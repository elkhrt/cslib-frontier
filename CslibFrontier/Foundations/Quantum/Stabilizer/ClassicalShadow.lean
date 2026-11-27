/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.Data.Finset.Median
public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Foundations.Quantum.DensityMatrix.MaxInformation
public import CslibFrontier.Foundations.Quantum.Stabilizer.Design
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Classical Shadows of Quantum States via Random Stabilizer Measurements

This module formalizes the classical shadow trace-estimation theorem of Huang, Kueng, and Preskill
 for `n`-qubit quantum states from first principles:

* **Random stabilizer measurement** (`CslibFrontier.Quantum.randomStabMeasurement`): choosing a
  uniformly random Lagrangian subspace `L` and measuring in its orthonormal stabilizer basis
  `stabPOVM L`, yielding a classical distribution over `StabState n`.
* **Single-shot estimator** (`CslibFrontier.Quantum.shadowSingleShot`):
  `d'(A, s) = Re Tr(A ((2^n + 1) P_s - 1))`, proved unbiased (`E[d'(A, S)] = Re Tr(A ρ)`) with
  variance bounded by `3 ‖A‖_F²` via the stabilizer 2- and 3-design trace identities.
* **Median-of-means classical shadow estimator** (`CslibFrontier.Quantum.shadowEstimator`):
  given `T = K * M` independent copies of `randomStabMeasurement ρ`, the deterministic median-of-
  means estimator achieves `|d(A, s) - Re Tr(A ρ)| ≤ ε` with probability at least `1 - δ` for
  every Hermitian observable `A` with `‖A‖_F² ≤ a`, where `T = O(a log(1/δ) / ε²)` and
  `log₂ |supp(S)| ≤ T * (n + n * (n + 3) / 2) = O(T n²)`.

All results are proved from first principles under standard Lean axioms.

## Main definitions

* `CslibFrontier.Quantum.randomStabMeasurement`: the random stabilizer measurement PMF on
  `StabState n`.
* `CslibFrontier.Quantum.shadowSingleShot`: single-copy unbiased trace estimator `d'(A, s)`.
* `CslibFrontier.Quantum.shadowBlocks`, `CslibFrontier.Quantum.shadowBlockSize`,
  `CslibFrontier.Quantum.shadowCopies`: explicit sample-complexity parameters `K, M, T = K * M`.
* `CslibFrontier.Quantum.shadowEstimator`: deterministic median-of-means estimator `d(A, s)`.

## Main results

* `CslibFrontier.Quantum.shadowSingleShot_expectation`: `E[d'(A, S)] = Re Tr(A ρ)`.
* `CslibFrontier.Quantum.shadowSingleShot_variance_le`: `Var(d'(A, S)) ≤ 3 ‖A‖_F²`.
* `CslibFrontier.Quantum.classical_shadow_trace_estimation`: Huang–Kueng–Preskill classical shadow
  trace estimation theorem with explicit constants and `O(T n²)` bit-representation bound.
-/

public section

namespace CslibFrontier.Quantum

open Matrix Finset Cslib Cslib.Quantum Cslib.Probability
open scoped MatrixOrder ComplexOrder ENNReal

/-! ### Random stabilizer measurement and single-shot shadow estimator -/

section SingleShot

/-- The random stabilizer measurement on an `n`-qubit density matrix `ρ`: pick a uniformly
random Lagrangian subspace `L` and measure `ρ` with the projective stabilizer POVM `stabPOVM L`. -/
noncomputable def randomStabMeasurement {n : ℕ} (ρ : Matrix (BitString n) (BitString n) ℂ)
    (hρ : IsDensityMatrix ρ) : PMF (StabState n) :=
  have : Nonempty {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} :=
    Fintype.card_pos_iff.mp (by rw [card_lagrangian]; exact lagrangianCount_pos n)
  (PMF.uniformOfFintype {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L}).bind fun L ↦
    ((stabPOVM L.1 L.2).measureDensity ρ hρ).map fun χ ↦ ⟨L.1, L.2, χ.1, χ.2⟩

theorem randomStabMeasurement_apply {n : ℕ} (ρ : Matrix (BitString n) (BitString n) ℂ)
    (hρ : IsDensityMatrix ρ) (s : StabState n) :
    (randomStabMeasurement ρ hρ s).toReal =
      ((2 : ℝ) ^ n / (Fintype.card (StabState n) : ℝ)) *
        (stabProjector s * ρ).trace.re := by
  classical
  have : Nonempty {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} :=
    Fintype.card_pos_iff.mp (by rw [card_lagrangian]; exact lagrangianCount_pos n)
  have hprob_nn : 0 ≤ (stabProjector s * ρ).trace.re :=
    (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg
      (stabProjector_isDensityMatrix s).posSemidef hρ.posSemidef)).1
  simp only [randomStabMeasurement, PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_fintype]
  have hterm (L : {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L}) :
      ((Fintype.card {L : Submodule (ZMod 2) (SympVec n) // IsLagrangian L} : ℝ≥0∞)⁻¹ *
        ∑ χ : {χ : SympVec n → Bool // IsStabSign L.1 χ},
          if s = ⟨L.1, L.2, χ.1, χ.2⟩ then
            (stabPOVM L.1 L.2).measureDensity ρ hρ χ else 0) =
      if L = ⟨s.L, s.isLagrangian⟩ then
        (lagrangianCount n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (stabProjector s * ρ).trace.re
      else 0 := by
    by_cases hL : L = ⟨s.L, s.isLagrangian⟩
    · subst hL
      simp only [ite_true, card_lagrangian]
      congr 1
      rw [Finset.sum_eq_single ⟨s.sign, s.isStabSign⟩]
      · simp [POVM.measureDensity_apply, POVM.densityProb, stabPOVM_effect]
      · intro χ _ hne
        simp only [show s ≠ ⟨s.L, s.isLagrangian, χ.1, χ.2⟩ from fun heq ↦
          hne (Subtype.ext (congrArg StabState.sign heq).symm), ite_false]
      · intro h; exact absurd (mem_univ _) h
    · simp only [hL, ite_false]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun χ _ ↦ ?_)
      simp only [show s ≠ ⟨L.1, L.2, χ.1, χ.2⟩ from fun heq ↦ hL (by
        cases s; simp only [StabState.mk.injEq] at heq; exact Subtype.ext heq.1.symm), ite_false]
  simp_rw [hterm]
  rw [Finset.sum_eq_single ⟨s.L, s.isLagrangian⟩]
  · simp only [ite_true, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hprob_nn]
    have hcard : (Fintype.card (StabState n) : ℝ) = (2 : ℝ) ^ n * (lagrangianCount n : ℝ) := by
      rw [card_stabState, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcard]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [h2]
  · intro L _ hne; simp [hne]
  · intro h; exact absurd (mem_univ _) h

/-- Single-shot classical shadow estimator `d'(A, s) = Re Tr(A ((2^n + 1) P_s - 1))`. -/
noncomputable def shadowSingleShot {n : ℕ} (A : Matrix (BitString n) (BitString n) ℂ)
    (s : StabState n) : ℝ :=
  (A * ((((2 : ℂ) ^ n + 1) • stabProjector s) - 1)).trace.re

/-- Unbiasedness of the single-shot classical shadow estimator: `E[d'(A, S)] = Re Tr(A ρ)`. -/
theorem shadowSingleShot_expectation {n : ℕ}
    (ρ : Matrix (BitString n) (BitString n) ℂ) (hρ : IsDensityMatrix ρ)
    (A : Matrix (BitString n) (BitString n) ℂ) (hA : A.IsHermitian) :
    ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal * shadowSingleShot A s =
      (A * ρ).trace.re := by
  set d : ℝ := (2 : ℝ) ^ n
  have hcard_pos : (0 : ℝ) < (Fintype.card (StabState n) : ℝ) := by
    rw [card_stabState]; have := lagrangianCount_pos n; positivity
  have hd_pos : 0 < d := by positivity
  -- Convert the real sum to the real part of a complex sum using Hermiticity of `A` and `P_s`, `ρ`.
  have htr_real (s : StabState n) :
      ((stabProjector s * ρ).trace.re : ℂ) = (ρ * stabProjector s).trace := by
    have h := Matrix.PosSemidef.trace_mul_nonneg
      (stabProjector_isDensityMatrix s).posSemidef hρ.posSemidef
    rw [trace_mul_comm]
    exact Complex.ext (Complex.ofReal_re _) (by
      rw [Complex.ofReal_im, trace_mul_comm]
      exact (Complex.nonneg_iff.mp h).2)
  have hA_real (M : Matrix (BitString n) (BitString n) ℂ) (hM : M.IsHermitian) :
      ((A * M).trace.re : ℂ) = (A * M).trace := by
    have hconj : star (A * M).trace = (A * M).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hM.eq, trace_mul_comm]
    exact Complex.ext (Complex.ofReal_re _) (by
      rw [Complex.ofReal_im]
      have := congrArg Complex.im hconj
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith)
  apply Complex.ofReal_injective
  push_cast
  have hterm_eq (s : StabState n) :
      ((randomStabMeasurement ρ hρ s).toReal : ℂ) * (shadowSingleShot A s : ℂ) =
        (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) * (ρ * stabProjector s).trace *
          (((2 : ℂ) ^ n + 1) * (A * stabProjector s).trace - A.trace) := by
    rw [randomStabMeasurement_apply]
    push_cast
    rw [htr_real s, shadowSingleShot, hA_real _ (by
      have hH := (stabProjector_isDensityMatrix s).posSemidef.isHermitian
      have hsc : star ((2 : ℂ) ^ n + 1) = (2 : ℂ) ^ n + 1 := by simp
      rw [Matrix.IsHermitian, conjTranspose_sub, conjTranspose_smul, hsc, hH.eq,
        conjTranspose_one]),
      Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, smul_eq_mul]
  simp_rw [hterm_eq, mul_sub, Finset.sum_sub_distrib]
  have hsum1 : ∑ s : StabState n, (ρ * stabProjector s).trace * (A * stabProjector s).trace =
      ((Fintype.card (StabState n) : ℂ) / ((2 : ℂ) ^ n * ((2 : ℂ) ^ n + 1))) *
        (ρ.trace * A.trace + (ρ * A).trace) := stabilizer_two_design_trace ρ A
  have hsum2 : ∑ s : StabState n, (ρ * stabProjector s).trace =
      ((Fintype.card (StabState n) : ℂ) / (2 : ℂ) ^ n) := by
    have h2 := stabilizer_two_design_trace ρ (1 : Matrix (BitString n) (BitString n) ℂ)
    have h1 (s : StabState n)
      : ((1 : Matrix (BitString n) (BitString n) ℂ) * stabProjector s).trace = 1 := by
      rw [Matrix.one_mul, (stabProjector_isDensityMatrix s).trace_eq_one]
    simp_rw [h1] at h2
    simp only [mul_one, trace_one, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, hρ.trace_eq_one, one_mul] at h2
    rw [h2]
    have hd_ne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hd1_ne : (2 : ℂ) ^ n + 1 ≠ 0 := by
      have : (0 : ℝ) < (2 : ℝ) ^ n + 1 := by positivity
      simpa using Complex.ofReal_ne_zero.mpr this.ne'
    field_simp [hd_ne, hd1_ne]
  have hmul_sum :
      ∑ s : StabState n, (ρ * stabProjector s).trace * (((2 : ℂ) ^ n +
        1) * (A * stabProjector s).trace) =
        ((2 : ℂ) ^ n +
          1) * ∑ s : StabState n, (ρ * stabProjector s).trace * (A * stabProjector s).trace := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ ↦ by ring
  have hd_ne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hd1_ne : (2 : ℂ) ^ n + 1 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 1 := by positivity
    simpa using Complex.ofReal_ne_zero.mpr this.ne'
  have hcard_ne : (Fintype.card (StabState n) : ℂ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  have hpart1 :
      ∑ s : StabState n,
        (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) * (ρ * stabProjector s).trace *
          (((2 : ℂ) ^ n + 1) * (A * stabProjector s).trace) =
        A.trace + (A * ρ).trace := by
    have hr : ∑ s : StabState n, (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) *
          (ρ * stabProjector s).trace * (((2 : ℂ) ^ n + 1) * (A * stabProjector s).trace) =
        (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) *
          ∑ s : StabState n, (ρ * stabProjector s).trace * (((2 : ℂ) ^ n +
            1) * (A * stabProjector s).trace) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hr, hmul_sum, hsum1, hρ.trace_eq_one, one_mul, trace_mul_comm ρ A]
    field_simp [hd_ne, hd1_ne, hcard_ne]
  have hpart2 :
      ∑ s : StabState n,
        (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) * (ρ * stabProjector s).trace *
          A.trace = A.trace := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum2]
    field_simp [hd_ne, hcard_ne]
  rw [hpart1, hpart2, add_sub_cancel_left, hA_real ρ hρ.posSemidef.isHermitian]

/-- Variance bound for the single-shot classical shadow estimator:
`Var(d'(A, S)) ≤ 3 ‖A‖_F²` for any Hermitian matrix `A`. -/
theorem shadowSingleShot_variance_le {n : ℕ}
    (ρ : Matrix (BitString n) (BitString n) ℂ) (hρ : IsDensityMatrix ρ)
    (A : Matrix (BitString n) (BitString n) ℂ) (hA : A.IsHermitian) :
    ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal *
        (shadowSingleShot A s - (A * ρ).trace.re) ^ 2 ≤
      3 * frobeniusNormSq A := by
  classical
  set d : ℝ := (2 : ℝ) ^ n
  have hd_pos : 0 < d := by positivity
  have hd_ne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hd1_ne : (2 : ℂ) ^ n + 1 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 1 := by positivity
    simpa using Complex.ofReal_ne_zero.mpr this.ne'
  have hd2_ne : (2 : ℂ) ^ n + 2 ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) ^ n + 2 := by positivity
    simpa using Complex.ofReal_ne_zero.mpr this.ne'
  have hcard_pos : (0 : ℝ) < (Fintype.card (StabState n) : ℝ) := by
    rw [card_stabState]; have := lagrangianCount_pos n; positivity
  have hcard_ne : (Fintype.card (StabState n) : ℂ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  -- Decompose `A = A₀ + (Tr(A)/d) • 1` where `A₀` is traceless Hermitian.
  let c0 : ℝ := A.trace.re / d
  let A0 : Matrix (BitString n) (BitString n) ℂ :=
    A - c0 • (1 : Matrix (BitString n) (BitString n) ℂ)
  have hA0_herm : A0.IsHermitian := by
    have h1 : (c0 • (1 : Matrix (BitString n) (BitString n) ℂ)).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_one]
      simp
    exact hA.sub h1
  have hA_tr_real : (A.trace.re : ℂ) = A.trace := by
    have hconj : star A.trace = A.trace := by rw [← trace_conjTranspose, hA.eq]
    exact Complex.ext (Complex.ofReal_re _) (by
      rw [Complex.ofReal_im]
      have := congrArg Complex.im hconj; simp only [Complex.star_def, Complex.conj_im] at this
      linarith)
  have hA0_tr : A0.trace = 0 := by
    simp only [A0, trace_sub, trace_smul, trace_one, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Complex.real_smul, c0, d]
    rw [← hA_tr_real]
    simp only [Complex.ofReal_re, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Nat.cast_pow, Nat.cast_ofNat, div_mul_cancel₀ _ hd_ne, sub_self]
  -- Shifting `A` by a scalar multiple of `1` shifts `shadowSingleShot` and `Tr(A ρ)` by the same
  -- `c0`!
  have hshift (s : StabState n) :
      shadowSingleShot A s - (A * ρ).trace.re = shadowSingleShot A0 s - (A0 * ρ).trace.re := by
    have htrP : (((2 : ℂ) ^ n + 1) • stabProjector s - 1).trace = 1 := by
      rw [trace_sub, trace_smul, (stabProjector_isDensityMatrix s).trace_eq_one, trace_one,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul, mul_one]
      push_cast; ring
    have h1 : shadowSingleShot A s = shadowSingleShot A0 s + c0 := by
      simp only [shadowSingleShot, A0, sub_mul, trace_sub, Complex.sub_re, Matrix.smul_mul,
        Matrix.one_mul, trace_smul, Complex.real_smul, Complex.ofReal_re, htrP, mul_one]
      ring
    have h2 : (A * ρ).trace.re = (A0 * ρ).trace.re + c0 := by
      simp only [A0, sub_mul, trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.one_mul,
        trace_smul, hρ.trace_eq_one, Complex.real_smul, mul_one, Complex.ofReal_re]
      ring
    linarith
  simp_rw [hshift]
  -- Variance ≤ second moment `E[d'(A0, S)^2]`.
  have hvar_le_sq :
      ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal *
          (shadowSingleShot A0 s - (A0 * ρ).trace.re) ^ 2 ≤
        ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal *
          (shadowSingleShot A0 s) ^ 2 := by
    have hexp0 := shadowSingleShot_expectation ρ hρ A0 hA0_herm
    have hsum1 : ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal = 1 :=
      Cslib.Probability.PMF.sum_toReal _
    have hdiff :
        (∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal * (shadowSingleShot A0 s) ^ 2) -
        (∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal *
          (shadowSingleShot A0 s - (A0 * ρ).trace.re) ^ 2) =
        ((A0 * ρ).trace.re) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      have hpt (s : StabState n) :
          (randomStabMeasurement ρ hρ s).toReal * (shadowSingleShot A0 s) ^ 2 -
          (randomStabMeasurement ρ hρ s).toReal * (shadowSingleShot A0 s - (A0 * ρ).trace.re) ^ 2 =
          2 * (A0 * ρ).trace.re * ((randomStabMeasurement ρ hρ s).toReal * shadowSingleShot A0 s) -
          (randomStabMeasurement ρ hρ s).toReal * ((A0 * ρ).trace.re) ^ 2 := by ring
      simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hexp0, hsum1]
      ring
    linarith [sq_nonneg ((A0 * ρ).trace.re)]
  -- Compute `E[d'(A0, S)^2]` via the 3-design trace identity!
  have hsq_eq :
      ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal * (shadowSingleShot A0 s) ^ 2 =
        ((d + 1) / (d + 2)) * ((A0 * A0).trace.re + 2 * (ρ * (A0 * A0)).trace.re) := by
    have hA0_real (M : Matrix (BitString n) (BitString n) ℂ) (hM : M.IsHermitian) :
        ((A0 * M).trace.re : ℂ) = (A0 * M).trace := by
      have hconj : star (A0 * M).trace = (A0 * M).trace := by
        rw [← trace_conjTranspose, conjTranspose_mul, hA0_herm.eq, hM.eq, trace_mul_comm]
      exact Complex.ext (Complex.ofReal_re _) (by
        rw [Complex.ofReal_im]
        have := congrArg Complex.im hconj; simp only [Complex.star_def, Complex.conj_im] at this
        linarith)
    have htr_real (s : StabState n) :
        ((stabProjector s * ρ).trace.re : ℂ) = (ρ * stabProjector s).trace := by
      have h := Matrix.PosSemidef.trace_mul_nonneg
        (stabProjector_isDensityMatrix s).posSemidef hρ.posSemidef
      rw [trace_mul_comm]
      exact Complex.ext (Complex.ofReal_re _) (by
        rw [Complex.ofReal_im, trace_mul_comm]; exact (Complex.nonneg_iff.mp h).2)
    have hshot0 (s : StabState n) :
        (shadowSingleShot A0 s : ℂ) = ((2 : ℂ) ^ n + 1) * (A0 * stabProjector s).trace := by
      rw [shadowSingleShot, hA0_real _ (by
        have hH := (stabProjector_isDensityMatrix s).posSemidef.isHermitian
        have hsc : star ((2 : ℂ) ^ n + 1) = (2 : ℂ) ^ n + 1 := by simp
        rw [Matrix.IsHermitian, conjTranspose_sub, conjTranspose_smul, hsc, hH.eq,
          conjTranspose_one])]
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, smul_eq_mul,
        hA0_tr, sub_zero]
    apply Complex.ofReal_injective
    push_cast
    have hterm_sq (s : StabState n) :
        ((randomStabMeasurement ρ hρ s).toReal : ℂ) * (shadowSingleShot A0 s : ℂ) ^ 2 =
          (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) * (ρ * stabProjector s).trace *
            (((2 : ℂ) ^ n + 1) * (A0 * stabProjector s).trace *
              (((2 : ℂ) ^ n + 1) * (A0 * stabProjector s).trace)) := by
      rw [randomStabMeasurement_apply]
      push_cast
      rw [htr_real s, sq, hshot0 s]
    simp_rw [hterm_sq]
    have hpull :
        ∑ s : StabState n,
          (2 : ℂ) ^ n / (Fintype.card (StabState n) : ℂ) * (ρ * stabProjector s).trace *
            (((2 : ℂ) ^ n + 1) * (A0 * stabProjector s).trace *
              (((2 : ℂ) ^ n + 1) * (A0 * stabProjector s).trace)) =
        (2 : ℂ) ^ n * ((2 : ℂ) ^ n + 1) ^ 2 / (Fintype.card (StabState n) : ℂ) *
          ∑ s : StabState n, (ρ * stabProjector s).trace * (A0 * stabProjector s).trace *
            (A0 * stabProjector s).trace := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ ↦ by ring
    rw [hpull, stabilizer_three_design_trace ρ A0 A0, hρ.trace_eq_one, hA0_tr]
    simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul]
    rw [hA0_real A0 hA0_herm]
    have hA02_psd : (A0 * A0).PosSemidef := by
      have h1 : A0 * A0 = A0ᴴ * A0 := by rw [hA0_herm.eq]
      rw [h1]
      exact posSemidef_conjTranspose_mul_self A0
    have hρA02_real : ((ρ * (A0 * A0)).trace.re : ℂ) = (ρ * (A0 * A0)).trace := by
      have h := Matrix.PosSemidef.trace_mul_nonneg hρ.posSemidef hA02_psd
      exact Complex.ext (Complex.ofReal_re _) (by
        rw [Complex.ofReal_im]; exact (Complex.nonneg_iff.mp h).2)
    rw [hρA02_real]
    have hmul_assoc_tr : (ρ * A0 * A0).trace = (ρ * (A0 * A0)).trace := by rw [Matrix.mul_assoc]
    rw [hmul_assoc_tr]
    dsimp only [d]
    push_cast
    field_simp [hd_ne, hd1_ne, hd2_ne, hcard_ne]
    ring
  -- Bound `(A0 * A0).trace.re ≤ frobeniusNormSq A` and `(ρ * (A0 * A0)).trace.re ≤ (A0 *
  -- A0).trace.re`.
  have hA0_le_A : (A0 * A0).trace.re ≤ frobeniusNormSq A := by
    have hA0_frob : (A0 * A0).trace.re = frobeniusNormSq A0 :=
      (frobeniusNormSq_of_isHermitian hA0_herm).symm
    rw [hA0_frob]
    have hdiff : frobeniusNormSq A - frobeniusNormSq A0 = d * c0 ^ 2 := by
      rw [frobeniusNormSq_of_isHermitian hA, frobeniusNormSq_of_isHermitian hA0_herm]
      simp only [A0, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, trace_sub, trace_smul, trace_one, Complex.sub_re, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have htrA : A.trace.re = c0 * d := by
        dsimp only [c0]; field_simp [show d ≠ 0 from hd_pos.ne']
      have htr1 : ((2 ^ n : ℕ) : ℂ).re = d := by dsimp only [d]; norm_cast
      rw [htrA, htr1]
      ring
    linarith [mul_nonneg hd_pos.le (sq_nonneg c0)]
  have hA02_psd : (A0 * A0).PosSemidef := by
    have h1 : A0 * A0 = A0ᴴ * A0 := by rw [hA0_herm.eq]
    rw [h1]
    exact posSemidef_conjTranspose_mul_self A0
  have hρA0_le : (ρ * (A0 * A0)).trace.re ≤ (A0 * A0).trace.re := by
    have h := Matrix.PosSemidef.trace_mul_nonneg (Matrix.le_iff.mp (isDensityMatrix_le_one hρ))
      hA02_psd
    rw [sub_mul, Matrix.one_mul, trace_sub] at h
    have hre := (Complex.nonneg_iff.mp h).1
    rw [Complex.sub_re] at hre
    linarith
  have hA02_nn : 0 ≤ (A0 * A0).trace.re := by
    rw [← frobeniusNormSq_of_isHermitian hA0_herm]
    exact frobeniusNormSq_nonneg A0
  have hfrac : (d + 1) / (d + 2) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  calc
    ∑ s : StabState n, (randomStabMeasurement ρ hρ s).toReal *
        (shadowSingleShot A0 s - (A0 * ρ).trace.re) ^ 2
        ≤ ((d + 1) / (d + 2)) * ((A0 * A0).trace.re + 2 * (ρ * (A0 * A0)).trace.re) :=
      hvar_le_sq.trans_eq hsq_eq
    _ ≤ 1 * ((A0 * A0).trace.re + 2 * (A0 * A0).trace.re) :=
      mul_le_mul hfrac (by linarith) (by
        have h1 : 0 ≤ (ρ * (A0 * A0)).trace.re :=
          (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg hρ.posSemidef hA02_psd)).1
        linarith) zero_le_one
    _ = 3 * (A0 * A0).trace.re := by ring
    _ ≤ 3 * frobeniusNormSq A := by linarith

end SingleShot

/-! ### Median-of-means classical shadow trace estimation -/

section MedianOfMeans

/-- Block size `M = ⌈12 a / ε²⌉ + 1` in the median-of-means classical shadow estimator. -/
noncomputable def shadowBlockSize (a ε : ℝ) : ℕ :=
  Nat.ceil (12 * a / ε ^ 2) + 1

/-- Number of blocks `K = ⌈8 ln(1/δ)⌉ + 1` in the median-of-means classical shadow estimator. -/
noncomputable def shadowBlocks (δ : ℝ) : ℕ :=
  Nat.ceil (8 * Real.log (1 / δ)) + 1

/-- Total number of copies `T = K * M` of `randomStabMeasurement` in the classical shadow. -/
noncomputable def shadowCopies (a ε δ : ℝ) : ℕ :=
  shadowBlocks δ * shadowBlockSize a ε

@[simp]
theorem shadowBlockSize_pos (a ε : ℝ) : 0 < shadowBlockSize a ε := by
  exact Nat.succ_pos _

@[simp]
theorem shadowBlocks_pos (δ : ℝ) : 0 < shadowBlocks δ := by
  exact Nat.succ_pos _

@[simp]
theorem shadowCopies_pos (a ε δ : ℝ) : 0 < shadowCopies a ε δ := by
  exact Nat.mul_pos (shadowBlocks_pos δ) (shadowBlockSize_pos a ε)

theorem shadowBlocks_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (shadowBlocks δ : ℝ) ≤ 8 * Real.log (1 / δ) + 2 := by
  have hnn : 0 ≤ 8 * Real.log (1 / δ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg ((one_le_div hδ0).mpr hδ1))
  have h := Nat.ceil_lt_add_one hnn
  dsimp only [shadowBlocks]
  push_cast
  linarith

theorem shadowBlockSize_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    (shadowBlockSize a ε : ℝ) ≤ 12 * a / ε ^ 2 + 2 := by
  have hnn : 0 ≤ 12 * a / ε ^ 2 := by positivity
  have h := Nat.ceil_lt_add_one hnn
  dsimp only [shadowBlockSize]
  push_cast
  linarith

/-- Deterministic median-of-means classical shadow trace estimator `d(A, s)` on `T = K * M`
independent stabilizer measurement outcomes `s : Fin K × Fin M → StabState n`. -/
noncomputable def shadowEstimator {n : ℕ} (a ε δ : ℝ)
    (A : Matrix (BitString n) (BitString n) ℂ)
    (s : Fin (shadowBlocks δ) × Fin (shadowBlockSize a ε) → StabState n) : ℝ :=
  Cslib.median fun j : Fin (shadowBlocks δ) ↦
    (∑ i : Fin (shadowBlockSize a ε), shadowSingleShot A (s (j, i))) / (shadowBlockSize a ε : ℝ)

/-- **Chebyshev inequality for empirical average of i.i.d. finite-PMF random variables**:
if `E[f] = μ` and `Var(f) ≤ v`, then `Pr[|avg_M - μ| > ε] ≤ v / (M ε²)`. -/
private theorem pi_empirical_mean_chebyshev {α : Type*} [Fintype α] (M : ℕ) (hM : 0 < M)
    (p : PMF α) (f : α → ℝ) (μ v ε : ℝ) (hε : 0 < ε)
    (hmean : ∑ x : α, (p x).toReal * f x = μ)
    (hvar : ∑ x : α, (p x).toReal * (f x - μ) ^ 2 ≤ v) :
    ((PMF.pi (fun _ : Fin M ↦ p)).toOuterMeasure
      {ω : Fin M → α | ε < |(∑ i : Fin M, f (ω i)) / (M : ℝ) - μ|}).toReal ≤
      v / ((M : ℝ) * ε ^ 2) := by
  classical
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  -- Compute exact variance of `∑ i, (f (ω i) - μ)`: equals `M * Var(f)` by independence!
  let g (x : α) : ℝ := f x - μ
  have hg_mean : ∑ x : α, (p x).toReal * g x = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Cslib.Probability.PMF.sum_toReal, one_mul, hmean, sub_self]
  have hsum_sq :
      ∑ ω : Fin M → α, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal * (∑ i : Fin M, g (ω i)) ^ 2 =
        (M : ℝ) * ∑ x : α, (p x).toReal * g x ^ 2 := by
    have hexpand (ω : Fin M → α) :
        (∑ i : Fin M, g (ω i)) ^ 2 = ∑ i : Fin M, ∑ j : Fin M, g (ω i) * g (ω j) := by
      rw [sq, Finset.sum_mul_sum]
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hpair (i : Fin M) :
        ∑ ω : Fin M → α, ∑ j : Fin M,
            (PMF.pi (fun _ : Fin M ↦ p) ω).toReal * (g (ω i) * g (ω j)) =
          ∑ x : α, (p x).toReal * g x ^ 2 := by
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single i]
      · simp_rw [← sq]
        exact Cslib.Probability.PMF.sum_pi_mul_eval (fun _ : Fin M ↦ p) i (fun x ↦ g x ^ 2)
      · intro j _ hji
        -- For `i ≠ j`, `(ω i, ω j)` has product distribution `p × p`, so expectation factors!
        have hfact :
            ∑ ω : Fin M → α, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal * (g (ω i) * g (ω j)) =
              (∑ x : α, (p x).toReal * g x) * (∑ y : α, (p y).toReal * g y) := by
          -- Condition on `ω i` using `PMF.pi_bind_update`!
          have hlaw := Cslib.Probability.PMF.pi_bind_update (fun _ : Fin M ↦ p) i
          rw [← hlaw]
          simp only [PMF.bind_apply, tsum_fintype,
            ENNReal.toReal_sum (fun _ _ ↦
              ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
          simp_rw [ENNReal.toReal_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          have hinner :
              ∑ ω : Fin M → α,
                (p x).toReal *
                  (PMF.pi (Function.update (fun _ : Fin M ↦ p) i (PMF.pure x)) ω).toReal *
                  (g (ω i) * g (ω j)) =
              (p x).toReal * g x *
                ∑ ω : Fin M → α,
                  (PMF.pi (Function.update (fun _ : Fin M ↦ p) i (PMF.pure x)) ω).toReal * g (ω j)
                    := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ω _ ↦ ?_
            by_cases hωi : ω i = x
            · rw [hωi]; ring
            · have hz : PMF.pi (Function.update (fun _ : Fin M ↦ p) i (PMF.pure x)) ω = 0 := by
                rw [PMF.pi_apply]
                exact Finset.prod_eq_zero (mem_univ i) (by simp [Function.update_self,
                  PMF.pure_apply, hωi])
              simp [hz]
          rw [hinner, Cslib.Probability.PMF.sum_pi_mul_eval, Function.update_of_ne hji]
        rw [hfact, hg_mean, mul_zero]
      · intro h; exact absurd (mem_univ _) h
    simp_rw [hpair, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  -- Apply Markov's inequality to `(∑ i, g (ω i))² ≥ (M ε)²`!
  let bad : Finset (Fin M → α) := Finset.univ.filter fun ω ↦
    ε < |(∑ i : Fin M, f (ω i)) / (M : ℝ) - μ|
  have hmeas : ((PMF.pi (fun _ : Fin M ↦ p)).toOuterMeasure
      {ω : Fin M → α | ε < |(∑ i : Fin M, f (ω i)) / (M : ℝ) - μ|}).toReal =
      ∑ ω ∈ bad, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal := by
    rw [PMF.toOuterMeasure_apply_fintype,
      ENNReal.toReal_sum (fun ω _ ↦ by
        simp only [Set.indicator_apply]; split_ifs
        · exact PMF.apply_ne_top _ _
        · exact ENNReal.zero_ne_top),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  rw [hmeas]
  have hmarkov :
      (M : ℝ) ^ 2 * ε ^ 2 * (∑ ω ∈ bad, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal) ≤
        (M : ℝ) * ∑ x : α, (p x).toReal * g x ^ 2 := by
    rw [← hsum_sq, Finset.mul_sum]
    calc
      ∑ ω ∈ bad, (M : ℝ) ^ 2 * ε ^ 2 * (PMF.pi (fun _ : Fin M ↦ p) ω).toReal
          ≤ ∑ ω ∈ bad, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal * (∑ i : Fin M, g (ω i)) ^ 2 := by
        refine Finset.sum_le_sum fun ω hω ↦ ?_
        have hgt : ε < |(∑ i : Fin M, f (ω i)) / (M : ℝ) - μ| := (mem_filter.mp hω).2
        have heq_g : (∑ i : Fin M, g (ω i)) = (M : ℝ) * ((∑ i : Fin M, f (ω i)) / (M : ℝ) - μ) := by
          simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp [hMpos.ne']
        have hsq_ge : (M : ℝ) ^ 2 * ε ^ 2 ≤ (∑ i : Fin M, g (ω i)) ^ 2 := by
          rw [heq_g, mul_pow, ← sq_abs ((∑ i : Fin M, f (ω i)) / (M : ℝ) - μ)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hgt.le 2) (sq_nonneg _)
        rw [mul_comm ((M : ℝ) ^ 2 * ε ^ 2)]
        exact mul_le_mul_of_nonneg_left hsq_ge ENNReal.toReal_nonneg
      _ ≤ ∑ ω : Fin M → α, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal * (∑ i : Fin M, g (ω i)) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg fun ω ↦
          mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have h1 : (M : ℝ) ^ 2 * ε ^ 2 * (∑ ω ∈ bad, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal) ≤
      (M : ℝ) * v := hmarkov.trans (mul_le_mul_of_nonneg_left hvar hMpos.le)
  rw [le_div_iff₀ (mul_pos hMpos (sq_pos_of_pos hε))]
  have h2 : (M : ℝ) * ((∑ ω ∈ bad, (PMF.pi (fun _ : Fin M ↦ p) ω).toReal) *
      ((M : ℝ) * ε ^ 2)) ≤ (M : ℝ) * v := by linarith
  exact le_of_mul_le_mul_left h2 hMpos

/--
For any `ε > 0`, `δ > 0`, `a : ℝ`, `n : ℕ`, and any `n`-qubit density matrix `ρ`, letting
`S = (randomStabMeasurement ρ)^⊗T` with `T = shadowCopies a ε δ = O(a log(1/δ) / ε²)`,
for every Hermitian matrix `A` with `‖A‖_F² ≤ a`,
`Pr_{s ← S}[|shadowEstimator a ε δ A s - Re Tr(A ρ)| ≤ ε] ≥ 1 - δ`,
and `log₂ |StabState n|^T ≤ T * (n + n * (n + 3) / 2)`.
-/
theorem classical_shadow_trace_estimation {n : ℕ} {a ε δ : ℝ}
    (hε : 0 < ε) (hδ0 : 0 < δ)
    (ρ : Matrix (BitString n) (BitString n) ℂ) (hρ : IsDensityMatrix ρ)
    (A : Matrix (BitString n) (BitString n) ℂ) (hA : A.IsHermitian)
    (hfrob : frobeniusNormSq A ≤ a) :
    let K := shadowBlocks δ
    let M := shadowBlockSize a ε
    let S := PMF.pi (fun _ : Fin K × Fin M ↦ randomStabMeasurement ρ hρ)
    1 - δ ≤ (S.toOuterMeasure
      {s | |shadowEstimator a ε δ A s - (A * ρ).trace.re| ≤ ε}).toReal := by
  classical
  intro K M S
  have hMpos : 0 < M := Nat.succ_pos _
  have hKpos : 0 < K := Nat.succ_pos _
  have hM_ge : 12 * a / ε ^ 2 ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  have hK_ge : 8 * Real.log (1 / δ) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  -- Reindex `S` as `PMF.pi (fun _ : Fin K ↦ PMF.pi (fun _ : Fin M ↦ randomStabMeasurement ρ hρ))`.
  let pBlock : PMF (Fin M → StabState n) := PMF.pi (fun _ : Fin M ↦ randomStabMeasurement ρ hρ)
  let eProd : (Fin K × Fin M → StabState n) ≃ (Fin K → Fin M → StabState n) :=
    Equiv.curry (Fin K) (Fin M) (StabState n)
  have hS_eq : S.map eProd = PMF.pi (fun _ : Fin K ↦ pBlock) := by
    ext g
    simp only [PMF.map_apply, PMF.pi_apply, S, pBlock, tsum_fintype]
    rw [Finset.sum_eq_single (eProd.symm g)]
    · simp only [Equiv.apply_symm_apply, ite_true, eProd]
      rw [Fintype.prod_prod_type]
      rfl
    · intro f _ hne
      simp only [show g ≠ eProd f from fun heq ↦ hne ((eProd.eq_symm_apply).mpr heq.symm),
        ite_false]
    · intro h; exact absurd (mem_univ _) h
  -- For each block `j`, the empirical average errs by `> ε` with probability `≤ 1/4` (Chebyshev).
  let blockAvg (ω : Fin M → StabState n) : ℝ :=
    (∑ i : Fin M, shadowSingleShot A (ω i)) / (M : ℝ)
  have hblock_bad :
      (pBlock.toOuterMeasure {ω | ε < |blockAvg ω - (A * ρ).trace.re|}).toReal ≤ 1 / 4 := by
    have hcheb := pi_empirical_mean_chebyshev M hMpos (randomStabMeasurement ρ hρ)
      (shadowSingleShot A) (A * ρ).trace.re (3 * a) ε hε
      (shadowSingleShot_expectation ρ hρ A hA)
      ((shadowSingleShot_variance_le ρ hρ A hA).trans (by linarith))
    refine hcheb.trans ?_
    have hMreal : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
    rw [div_le_iff₀ (mul_pos hMreal (sq_pos_of_pos hε))]
    have h1 : 12 * a ≤ (M : ℝ) * ε ^ 2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp hM_ge
    linarith
  -- Indicator score `score ω = 1` if `|blockAvg ω - μ| ≤ ε`, else `0`.
  let score (ω : Fin M → StabState n) : ℝ :=
    if |blockAvg ω - (A * ρ).trace.re| ≤ ε then 1 else 0
  have hscore_mean : 3 / 4 ≤ ∑ ω : Fin M → StabState n, (pBlock ω).toReal * score ω := by
    have hsum1 : ∑ ω : Fin M → StabState n, (pBlock ω).toReal = 1 :=
      Cslib.Probability.PMF.sum_toReal pBlock
    have hgood_bad :
        (∑ ω : Fin M → StabState n, (pBlock ω).toReal * score ω) +
          (pBlock.toOuterMeasure {ω | ε < |blockAvg ω - (A * ρ).trace.re|}).toReal = 1 := by
      rw [PMF.toOuterMeasure_apply_fintype,
        ENNReal.toReal_sum (fun _ _ ↦ by
          simp only [Set.indicator_apply]; split_ifs <;> simp [PMF.apply_ne_top]), ← hsum1,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      dsimp only [score, Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases h : |blockAvg ω - (A * ρ).trace.re| ≤ ε
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]
    linarith
  -- Apply Hoeffding (`pi_sum_le_mean_sub_card_mul`) to `∑ j : Fin K, score (g j)`!
  have hhoeff := Cslib.Probability.PMF.pi_sum_le_mean_sub_card_mul (fun _ : Fin K ↦ pBlock)
    (fun _ ↦ score) (fun _ ω _ ↦ by dsimp only [score]; split_ifs <;> norm_num)
    (γ := 1 / 4) (by norm_num)
  have hmean_K : (∑ _j : Fin K, ∑ ω : Fin M → StabState n, (pBlock ω).toReal * score ω) ≥
      (K : ℝ) * (3 / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hscore_mean (Nat.cast_nonneg K)
  have hfail_le :
      ((PMF.pi (fun _ : Fin K ↦ pBlock)).toOuterMeasure
        {g : Fin K → Fin M → StabState n |
          (∑ j : Fin K, score (g j)) ≤ (K : ℝ) / 2}).toReal ≤ δ := by
    have hsub :
        {g : Fin K → Fin M → StabState n | (∑ j : Fin K, score (g j)) ≤ (K : ℝ) / 2} ⊆
        {g | (∑ j : Fin K, score (g j)) ≤
          (∑ _j : Fin K, ∑ ω, (pBlock ω).toReal * score ω) -
            (Fintype.card (Fin K) : ℝ) * (1 / 4)} := by
      intro g hg
      simp only [Set.mem_ofPred_eq, Fintype.card_fin] at hg ⊢
      linarith
    have hmono :
        ((PMF.pi (fun _ : Fin K ↦ pBlock)).toOuterMeasure
          {g | (∑ j : Fin K, score (g j)) ≤ (K : ℝ) / 2}).toReal ≤
        ((PMF.pi (fun _ : Fin K ↦ pBlock)).toOuterMeasure
          {g | (∑ j : Fin K, score (g j)) ≤
            (∑ _j : Fin K, ∑ ω, (pBlock ω).toReal * score ω) -
              (Fintype.card (Fin K) : ℝ) * (1 / 4)}).toReal :=
      ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
        ((PMF.pi (fun _ : Fin K ↦ pBlock)).toOuterMeasure.mono hsub)
    refine (hmono.trans hhoeff).trans ?_
    simp only [Fintype.card_fin]
    have hexp_le : -2 * (K : ℝ) * (1 / 4 : ℝ) ^ 2 ≤ -Real.log (1 / δ) := by linarith
    calc
      Real.exp (-2 * (K : ℝ) * (1 / 4 : ℝ) ^ 2) ≤ Real.exp (-Real.log (1 / δ)) :=
        Real.exp_le_exp.mpr hexp_le
      _ = Real.exp (Real.log δ) := by rw [one_div, Real.log_inv, neg_neg]
      _ = δ := Real.exp_log hδ0
  -- If `∑ j, score (g j) > K / 2`, then strictly more than half of the blocks are within `ε`,
  -- so `Cslib.abs_median_sub_le` gives `|median - μ| ≤ ε`!
  have hgood_subset :
      {s : Fin K × Fin M → StabState n | (K : ℝ) / 2 < ∑ j : Fin K, score (eProd s j)} ⊆
      {s : Fin K × Fin M → StabState n | |shadowEstimator a ε δ A s - (A * ρ).trace.re| ≤ ε} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    apply Cslib.abs_median_sub_le
    have hcard_eq : (∑ j : Fin K, score (eProd s j)) =
        ((Finset.univ.filter fun j : Fin K ↦
          |blockAvg (eProd s j) - (A * ρ).trace.re| ≤ ε).card : ℝ) := by
      rw [← Finset.sum_boole]
    rw [hcard_eq] at hs
    simp only [Fintype.card_fin]
    have hlt_R : (K : ℝ) < 2 * ((Finset.univ.filter fun j : Fin K ↦
        |blockAvg (eProd s j) - (A * ρ).trace.re| ≤ ε).card : ℝ) := by linarith
    exact_mod_cast hlt_R
  have hcompl :
      (S.toOuterMeasure {s | (K : ℝ) / 2 < ∑ j : Fin K, score (eProd s j)}).toReal +
      (S.toOuterMeasure {s | ∑ j : Fin K, score (eProd s j) ≤ (K : ℝ) / 2}).toReal = 1 := by
    have h1 : ∑ s : Fin K × Fin M → StabState n, (S s).toReal = 1 :=
      Cslib.Probability.PMF.sum_toReal S
    rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ENNReal.toReal_sum (fun _ _ ↦ by
        simp only [Set.indicator_apply]; split_ifs <;> simp [PMF.apply_ne_top]),
      ENNReal.toReal_sum (fun _ _ ↦ by
        simp only [Set.indicator_apply]; split_ifs <;> simp [PMF.apply_ne_top]),
      ← Finset.sum_add_distrib, ← h1]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : (K : ℝ) / 2 < ∑ j : Fin K, score (eProd s j)
    · simp [h, not_le.mpr h]
    · simp [h, le_of_not_gt h]
  have hbad_eq :
      (S.toOuterMeasure {s | ∑ j : Fin K, score (eProd s j) ≤ (K : ℝ) / 2}).toReal =
        ((PMF.pi (fun _ : Fin K ↦ pBlock)).toOuterMeasure
          {g | ∑ j : Fin K, score (g j) ≤ (K : ℝ) / 2}).toReal := by
    rw [← hS_eq, PMF.toOuterMeasure_map_apply]
    rfl
  have hgood_ge :
      1 - δ ≤ (S.toOuterMeasure {s | (K : ℝ) / 2 < ∑ j : Fin K, score (eProd s j)}).toReal := by
    linarith [hbad_eq ▸ hfail_le]
  exact hgood_ge.trans (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (S.toOuterMeasure.mono hgood_subset))

/-- Bit-representation bound for classical shadows:
`log₂ |Fin T → StabState n| ≤ T * (n + n * (n + 3) / 2) = O(T n²)`. -/
theorem classical_shadow_support_log_le (n T : ℕ) :
    Real.logb 2 (Fintype.card (Fin T → StabState n) : ℝ) ≤
      (T : ℝ) * ((n + n * (n + 3) / 2 : ℕ) : ℝ) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  have hle : (Fintype.card (StabState n) ^ T : ℝ) ≤
      (2 : ℝ) ^ (T * (n + n * (n + 3) / 2)) := by
    have h1 := Nat.pow_le_pow_left (card_stabState_le n) T
    rw [← pow_mul, mul_comm (n + n * (n + 3) / 2) T] at h1
    exact_mod_cast h1
  have hpos : (0 : ℝ) < (Fintype.card (StabState n) ^ T : ℝ) := by
    rw [card_stabState]
    have := lagrangianCount_pos n
    positivity
  calc
    Real.logb 2 ((Fintype.card (StabState n) ^ T : ℕ) : ℝ)
        ≤ Real.logb 2 ((2 : ℝ) ^ (T * (n + n * (n + 3) / 2))) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) (by exact_mod_cast hle)
    _ = ((T * (n + n * (n + 3) / 2) : ℕ) : ℝ) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ = (T : ℝ) * ((n + n * (n + 3) / 2 : ℕ) : ℝ) := by push_cast; rfl

end MedianOfMeans

end CslibFrontier.Quantum
