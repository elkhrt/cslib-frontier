/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Quantum.DensityMatrix.TraceDistanceDataProcessing

/-!
# Weighted-Prior Holevo–Helstrom Quantum State Discrimination

Generalizes equal-prior quantum state discrimination (`Cslib.Quantum.helstrom_success_le` and
`Cslib.Quantum.helstromPOVM_success`) to arbitrary prior probabilities `p` and `1 - p`
(`p ∈ [0, 1]`), together with subnormalized state discrimination bounds for unnormalized positive
operators.

## Main results

* `CslibFrontier.Quantum.helstrom_subnormalized_le`: for any two-outcome `M : POVM Bool κ` and
  matrices `A, B`,
  `M.densityProb A false + M.densityProb B true ≤ (Re Tr A + Re Tr B + ‖A - B‖_tr) / 2`.
* `CslibFrontier.Quantum.helstromPOVM_subnormalized_eq`: when `A - B` is Hermitian, `helstromPOVM`
  attains `(Re Tr A + Re Tr B + ‖A - B‖_tr) / 2`.
* `CslibFrontier.Quantum.helstrom_weighted_le`: for density matrices `ρ₀, ρ₁` with prior
  `p ∈ [0, 1]`, every two-outcome POVM `M` has success probability at most
  `1 / 2 + (1 / 2) * ‖p • ρ₀ - (1 - p) • ρ₁‖_tr`.
* `CslibFrontier.Quantum.helstrom_weighted_eq`: `helstromPOVM` attains the optimal weighted-prior
  success probability `1 / 2 + (1 / 2) * ‖p • ρ₀ - (1 - p) • ρ₁‖_tr`.
-/

public section

namespace CslibFrontier.Quantum

open Cslib.Quantum Matrix
open scoped MatrixOrder ComplexOrder

private theorem densityProb_real_smul {κ Z : Type*} [Fintype κ] [DecidableEq κ] [Fintype Z]
    (M : POVM Z κ) (c : ℝ) (ρ : Matrix κ κ ℂ) (z : Z) :
    M.densityProb ((c : ℂ) • ρ) z = c * M.densityProb ρ z := by
  unfold POVM.densityProb
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul]
  simp [Complex.mul_re]

/-- Subnormalized two-outcome Holevo–Helstrom upper bound: for any two-outcome POVM `M` and any
matrices `A, B`,
`M.densityProb A false + M.densityProb B true ≤ (Re Tr A + Re Tr B + ‖A - B‖_tr) / 2`. -/
theorem helstrom_subnormalized_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : POVM Bool κ) (A B : Matrix κ κ ℂ) :
    M.densityProb A false + M.densityProb B true ≤
      (A.trace.re + B.trace.re + (A - B).traceNorm) / 2 := by
  have hA := M.sum_densityProb A
  have hB := M.sum_densityProb B
  have htvd := M.half_sum_abs_densityProb_sub_le_traceDistance A B
  rw [Fintype.sum_bool] at hA hB htvd
  unfold traceDistance at htvd
  have h1 : M.densityProb A false - M.densityProb B false ≤
      |M.densityProb A false - M.densityProb B false| := le_abs_self _
  have h2 : M.densityProb B true - M.densityProb A true ≤
      |M.densityProb A true - M.densityProb B true| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

/-- Subnormalized two-outcome Holevo–Helstrom attainment: whenever `A - B` is Hermitian,
`helstromPOVM` attains `(Re Tr A + Re Tr B + ‖A - B‖_tr) / 2`. -/
theorem helstromPOVM_subnormalized_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A B : Matrix κ κ ℂ} (hΔ : (A - B).IsHermitian) :
    (helstromPOVM hΔ).densityProb A false + (helstromPOVM hΔ).densityProb B true =
      (A.trace.re + B.trace.re + (A - B).traceNorm) / 2 := by
  simp only [POVM.densityProb, helstromPOVM_effect, Bool.cond_false, Bool.cond_true]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.one_mul, trace_smul, trace_smul, trace_add, trace_sub, smul_eq_mul, smul_eq_mul]
  have hre :
      ((2⁻¹ : ℂ) * (A.trace + (helstromObservable hΔ * A).trace)).re +
        ((2⁻¹ : ℂ) * (B.trace - (helstromObservable hΔ * B).trace)).re =
      (A.trace.re + B.trace.re + (helstromObservable hΔ * (A - B)).trace.re) / 2 := by
    rw [Matrix.mul_sub, trace_sub]
    simp [Complex.mul_re]
    ring
  rw [hre, re_trace_helstromObservable_mul_sub hΔ]

/-- General-prior Holevo–Helstrom upper bound: for any two density matrices `ρ₀, ρ₁` with prior
probabilities `p` and `1 - p` (`p ∈ [0, 1]`) and any two-outcome POVM `M`, the success probability
is at most `1 / 2 + (1 / 2) * ‖p • ρ₀ - (1 - p) • ρ₁‖_tr`. -/
theorem helstrom_weighted_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : POVM Bool κ) {ρ₀ ρ₁ : Matrix κ κ ℂ}
    (h₀ : IsDensityMatrix ρ₀) (h₁ : IsDensityMatrix ρ₁)
    {p : ℝ} (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) :
    p * M.densityProb ρ₀ false + (1 - p) * M.densityProb ρ₁ true ≤
      1 / 2 + (1 / 2) * ((p : ℂ) • ρ₀ - ((1 - p : ℝ) : ℂ) • ρ₁).traceNorm := by
  have h := helstrom_subnormalized_le M ((p : ℂ) • ρ₀) (((1 - p : ℝ) : ℂ) • ρ₁)
  rw [densityProb_real_smul, densityProb_real_smul, trace_smul, trace_smul,
    h₀.trace_eq_one, h₁.trace_eq_one, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    Complex.ofReal_re, Complex.ofReal_re] at h
  linarith

/-- General-prior Holevo–Helstrom attainment: there exists a two-outcome POVM attaining
`1 / 2 + (1 / 2) * ‖p • ρ₀ - (1 - p) • ρ₁‖_tr`. -/
theorem helstrom_weighted_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ρ₀ ρ₁ : Matrix κ κ ℂ} (h₀ : IsDensityMatrix ρ₀) (h₁ : IsDensityMatrix ρ₁)
    {p : ℝ} (_hp₀ : 0 ≤ p) (_hp₁ : p ≤ 1) :
    ∃ M : POVM Bool κ,
      p * M.densityProb ρ₀ false + (1 - p) * M.densityProb ρ₁ true =
        1 / 2 + (1 / 2) * ((p : ℂ) • ρ₀ - ((1 - p : ℝ) : ℂ) • ρ₁).traceNorm := by
  have hA_herm : (((p : ℂ) • ρ₀)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      h₀.posSemidef.isHermitian.eq]
  have hB_herm : ((((1 - p : ℝ) : ℂ) • ρ₁)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      h₁.posSemidef.isHermitian.eq]
  have hΔ : (((p : ℂ) • ρ₀) - (((1 - p : ℝ) : ℂ) • ρ₁)).IsHermitian := hA_herm.sub hB_herm
  refine ⟨helstromPOVM hΔ, ?_⟩
  have h := helstromPOVM_subnormalized_eq hΔ
  rw [densityProb_real_smul, densityProb_real_smul, trace_smul, trace_smul,
    h₀.trace_eq_one, h₁.trace_eq_one, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    Complex.ofReal_re, Complex.ofReal_re] at h
  linarith

end CslibFrontier.Quantum
