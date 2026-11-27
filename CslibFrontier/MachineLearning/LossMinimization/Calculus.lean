/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiation and Mini-Batch Decomposition of Empirical Risk

For a loss function `ℓ : W → Z → ℝ` and a finite sample `S : Fin m → Z`, the empirical risk
`Cslib.MachineLearning.empiricalRisk ℓ S w = 𝔼 i, ℓ w (S i)` inherits Fréchet differentiability,
scalar differentiability, and Hilbert-space gradients from the per-example losses `w ↦ ℓ w (S i)` by
linearity of finite sample expectations. Moreover, when a dataset of size `b * m` is partitioned
into `b` equal-size mini-batches of size `m` (`b > 0`, `m > 0`), both the empirical risk and its
Fréchet derivative / gradient equal the uniform expectation over all mini-batches.

## Main definitions

* `CslibFrontier.MachineLearning.miniBatch`: the `j`-th mini-batch of size `m` cut from a sample
  `S : Fin (b * m) → Z` along `finProdFinEquiv`.

## Main results

* `CslibFrontier.MachineLearning.hasFDerivAt_empiricalRisk`,
  `CslibFrontier.MachineLearning.differentiableAt_empiricalRisk`,
  `CslibFrontier.MachineLearning.fderiv_empiricalRisk`: Fréchet derivative of empirical risk equals
  the sample expectation of the per-example Fréchet derivatives.
* `CslibFrontier.MachineLearning.hasDerivAt_empiricalRisk`,
  `CslibFrontier.MachineLearning.deriv_empiricalRisk`: scalar derivative of empirical risk equals
  the sample expectation of the per-example derivatives.
* `CslibFrontier.MachineLearning.hasGradientAt_empiricalRisk`,
  `CslibFrontier.MachineLearning.gradient_empiricalRisk`: Hilbert-space gradient of empirical risk
  equals the sample expectation of the per-example gradients.
* `CslibFrontier.MachineLearning.expect_empiricalRisk_miniBatch`,
  `CslibFrontier.MachineLearning.expect_fderiv_empiricalRisk_miniBatch`,
  `CslibFrontier.MachineLearning.expect_gradient_empiricalRisk_miniBatch`: exact decomposition of
  empirical risk, its Fréchet derivative, and its gradient as the uniform average across equal-size
  mini-batches.
-/

public section

open Cslib.MachineLearning Finset
open scoped BigOperators

namespace CslibFrontier.MachineLearning

section FDeriv

variable {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- If each per-example loss `w ↦ ℓ w (S i)` has Fréchet derivative `d i` at `w`, then
`empiricalRisk ℓ S` has Fréchet derivative `𝔼 i, d i` at `w`. -/
theorem hasFDerivAt_empiricalRisk {ℓ : W → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : W}
    {d : Fin m → W →L[ℝ] ℝ} (hℓ : ∀ i : Fin m, HasFDerivAt (fun w' ↦ ℓ w' (S i)) (d i) w) :
    HasFDerivAt (empiricalRisk ℓ S) ((m : ℝ)⁻¹ • ∑ i : Fin m, d i) w := by
  have hfn : empiricalRisk ℓ S = fun w' ↦ (m : ℝ)⁻¹ * ∑ i : Fin m, ℓ w' (S i) := by
    funext w'
    rw [empiricalRisk_eq_sum_div, div_eq_inv_mul]
  rw [hfn]
  exact (HasFDerivAt.fun_sum fun i _ ↦ hℓ i).const_mul (m : ℝ)⁻¹

/-- If every per-example loss `w ↦ ℓ w (S i)` is differentiable at `w`, so is `empiricalRisk ℓ S`.
-/
theorem differentiableAt_empiricalRisk {ℓ : W → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : W}
    (hℓ : ∀ i : Fin m, DifferentiableAt ℝ (fun w' ↦ ℓ w' (S i)) w) :
    DifferentiableAt ℝ (empiricalRisk ℓ S) w :=
  (hasFDerivAt_empiricalRisk fun i ↦ (hℓ i).hasFDerivAt).differentiableAt

/-- The Fréchet derivative of `empiricalRisk ℓ S` at `w` is the sample average of the per-example
Fréchet derivatives. -/
theorem fderiv_empiricalRisk {ℓ : W → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : W}
    (hℓ : ∀ i : Fin m, DifferentiableAt ℝ (fun w' ↦ ℓ w' (S i)) w) :
    fderiv ℝ (empiricalRisk ℓ S) w = (m : ℝ)⁻¹ • ∑ i : Fin m, fderiv ℝ (fun w' ↦ ℓ w' (S i)) w :=
  (hasFDerivAt_empiricalRisk fun i ↦ (hℓ i).hasFDerivAt).fderiv

end FDeriv

section Deriv

variable {Z : Type*}

/-- Scalar derivative rule for `empiricalRisk ℓ S` on a one-dimensional real parameter `w : ℝ`. -/
theorem hasDerivAt_empiricalRisk {ℓ : ℝ → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : ℝ}
    {d : Fin m → ℝ} (hℓ : ∀ i : Fin m, HasDerivAt (fun w' ↦ ℓ w' (S i)) (d i) w) :
    HasDerivAt (empiricalRisk ℓ S) (𝔼 i : Fin m, d i) w := by
  have hfn : empiricalRisk ℓ S = fun w' ↦ (∑ i : Fin m, ℓ w' (S i)) / m :=
    funext (empiricalRisk_eq_sum_div ℓ S)
  rw [hfn, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  exact (HasDerivAt.fun_sum fun i _ ↦ hℓ i).div_const (m : ℝ)

/-- Closed-form `deriv` of `empiricalRisk ℓ S` as the sample expectation of per-example derivatives.
-/
theorem deriv_empiricalRisk {ℓ : ℝ → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : ℝ}
    (hℓ : ∀ i : Fin m, DifferentiableAt ℝ (fun w' ↦ ℓ w' (S i)) w) :
    deriv (empiricalRisk ℓ S) w = 𝔼 i : Fin m, deriv (fun w' ↦ ℓ w' (S i)) w :=
  (hasDerivAt_empiricalRisk fun i ↦ (hℓ i).hasDerivAt).deriv

end Deriv

section Gradient

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- If each per-example loss `w ↦ ℓ w (S i)` has Hilbert-space gradient `g i` at `w`, then
`empiricalRisk ℓ S` has gradient `𝔼 i, g i` at `w`. -/
theorem hasGradientAt_empiricalRisk {ℓ : E → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : E}
    {g : Fin m → E} (hℓ : ∀ i : Fin m, HasGradientAt (fun w' ↦ ℓ w' (S i)) (g i) w) :
    HasGradientAt (empiricalRisk ℓ S) ((m : ℝ)⁻¹ • ∑ i : Fin m, g i) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hf := hasFDerivAt_empiricalRisk fun i ↦ hasGradientAt_iff_hasFDerivAt.mp (hℓ i)
  convert hf using 1
  rw [map_smul, map_sum]

/-- The Hilbert-space gradient of `empiricalRisk ℓ S` equals the sample average of per-example
gradients. -/
theorem gradient_empiricalRisk {ℓ : E → Z → ℝ} {m : ℕ} {S : Fin m → Z} {w : E}
    (hℓ : ∀ i : Fin m, DifferentiableAt ℝ (fun w' ↦ ℓ w' (S i)) w) :
    gradient (empiricalRisk ℓ S) w =
      (m : ℝ)⁻¹ • ∑ i : Fin m, gradient (fun w' ↦ ℓ w' (S i)) w :=
  (hasGradientAt_empiricalRisk fun i ↦ (hℓ i).hasGradientAt).gradient

end Gradient

section MiniBatch

variable {Z : Type*}

/-- The `j`-th contiguous mini-batch of size `m` cut from a dataset `S : Fin (b * m) → Z`. -/
def miniBatch {b m : ℕ} (S : Fin (b * m) → Z) (j : Fin b) : Fin m → Z :=
  fun i ↦ S (finProdFinEquiv (j, i))

private theorem smul_sum_miniBatch {M : Type*} [AddCommMonoid M] [Module ℝ M] {b m : ℕ}
    (S : Fin (b * m) → Z) (f : Z → M) :
    (b : ℝ)⁻¹ • (∑ j : Fin b, (m : ℝ)⁻¹ • ∑ i : Fin m, f (miniBatch S j i)) =
      ((b * m : ℕ) : ℝ)⁻¹ • ∑ k : Fin (b * m), f (S k) := by
  rw [← smul_sum, smul_smul, Nat.cast_mul, mul_inv_rev, mul_comm (m : ℝ)⁻¹ (b : ℝ)⁻¹]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv finProdFinEquiv _ (fun k ↦ f (S k)) fun _ ↦ rfl

/-- Partitioning a sample `S : Fin (b * m) → Z` into `b` equal mini-batches of size `m`, the average
of the mini-batch empirical risks equals the full-sample empirical risk. -/
theorem expect_empiricalRisk_miniBatch {W : Type*} (ℓ : W → Z → ℝ) {b m : ℕ}
    (S : Fin (b * m) → Z) (w : W) :
    (𝔼 j : Fin b, empiricalRisk ℓ (miniBatch S j) w) = empiricalRisk ℓ S w := by
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, empiricalRisk_eq_sum_div,
    div_eq_inv_mul, smul_eq_mul] using smul_sum_miniBatch S (ℓ w)

/-- The uniform average of the mini-batch empirical-risk Fréchet derivatives equals the exact
full-sample empirical-risk Fréchet derivative. -/
theorem expect_fderiv_empiricalRisk_miniBatch {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ℓ : W → Z → ℝ} {b m : ℕ} {S : Fin (b * m) → Z} {w : W}
    (hℓ : ∀ k : Fin (b * m), DifferentiableAt ℝ (fun w' ↦ ℓ w' (S k)) w) :
    (b : ℝ)⁻¹ • (∑ j : Fin b, fderiv ℝ (empiricalRisk ℓ (miniBatch S j)) w) =
      fderiv ℝ (empiricalRisk ℓ S) w := by
  rw [fderiv_empiricalRisk hℓ]
  have hmb : ∀ j : Fin b, fderiv ℝ (empiricalRisk ℓ (miniBatch S j)) w =
      (m : ℝ)⁻¹ • ∑ i : Fin m, fderiv ℝ (fun w' ↦ ℓ w' (miniBatch S j i)) w :=
    fun j ↦ fderiv_empiricalRisk fun i ↦ hℓ (finProdFinEquiv (j, i))
  simp only [hmb]
  exact smul_sum_miniBatch S fun z ↦ fderiv ℝ (fun w' ↦ ℓ w' z) w

/-- The uniform average of the mini-batch empirical-risk gradients equals the exact full-sample
empirical-risk gradient. -/
theorem expect_gradient_empiricalRisk_miniBatch {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ℓ : E → Z → ℝ} {b m : ℕ}
    {S : Fin (b * m) → Z} {w : E}
    (hℓ : ∀ k : Fin (b * m), DifferentiableAt ℝ (fun w' ↦ ℓ w' (S k)) w) :
    (b : ℝ)⁻¹ • (∑ j : Fin b, gradient (empiricalRisk ℓ (miniBatch S j)) w) =
      gradient (empiricalRisk ℓ S) w := by
  rw [gradient_empiricalRisk hℓ]
  have hmb : ∀ j : Fin b, gradient (empiricalRisk ℓ (miniBatch S j)) w =
      (m : ℝ)⁻¹ • ∑ i : Fin m, gradient (fun w' ↦ ℓ w' (miniBatch S j i)) w :=
    fun j ↦ gradient_empiricalRisk fun i ↦ hℓ (finProdFinEquiv (j, i))
  simp only [hmb]
  exact smul_sum_miniBatch S fun z ↦ gradient (fun w' ↦ ℓ w' z) w

end MiniBatch

end CslibFrontier.MachineLearning
