/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefKernel
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Probability.PMF
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pretty Good Measurement and Renes Optimality

This module defines the guessing probability, optimal guessing probability, and Pretty Good
Measurement (PGM, also called the square-root measurement) for finite classical–quantum ensembles,
and proves the sharpened PGM optimality bound of Renes:

$$p_g^{\mathrm{pgm}}(X \mid Q)_\rho \ge g\bigl(p_g^{\mathrm{opt}}(X \mid Q)_\rho\bigr),
\qquad g(x) = x^2 + \frac{(1 - x)^2}{d - 1},$$

together with the convexity and monotonicity of `g` on `[1/d, 1]` and the PGM splitting identity
for composite functions of the classical register.

All results are proved from first principles under standard Lean axioms.

## Main definitions

* `CslibFrontier.Quantum.guessingProb`: guessing probability `∑ x, p(x) Re Tr(E_x ρ_x)` of a POVM.
* `CslibFrontier.Quantum.optGuessingProb`: optimal guessing probability `sup_M guessingProb p ρ M`.
* `CslibFrontier.Quantum.pgmPOVM`: the Pretty Good Measurement POVM
  `E_x = A^{-1/2} A_x A^{-1/2} + p(x)(1 - P_A)`.
* `CslibFrontier.Quantum.pgmGuessingProb`: guessing probability achieved by the PGM.
* `CslibFrontier.Quantum.renesPgmBound`: `g(x) = x^2 + (1 - x)^2 / (d - 1)`.

## Main results

* `CslibFrontier.Quantum.pgm_guessingProb_ge_renesPgmBound`: for every POVM `M` and `d = |X| ≥ 2`,
  `pgmGuessingProb p ρ ≥ renesPgmBound d (guessingProb p ρ M)`.
* `CslibFrontier.Quantum.pgm_optimality`: Renes optimality bound
  `pgmGuessingProb p ρ ≥ renesPgmBound d (optGuessingProb p ρ)`.
* `CslibFrontier.Quantum.renesPgmBound_convexOn`: convexity of `g` on `ℝ`.
* `CslibFrontier.Quantum.renesPgmBound_mono`: monotonicity of `g` on `[1/d, 1]`.
* `CslibFrontier.Quantum.pgmPOVM_effect_sum_fiber`: PGM splitting identity
  `∑_{x ∈ f⁻¹(z)} E^{pgm}_x = E^{pgm, f}_z`.
-/

public section

namespace CslibFrontier.Quantum

open Matrix Finset Cslib.Quantum
open scoped MatrixOrder ComplexOrder

variable {X ι : Type*}

/-! ### Guessing probability and the Pretty Good Measurement -/

section Definitions

/-- Guessing probability `∑ x, p(x) Re Tr(E_x ρ_x)` of a POVM `M` on the cq-ensemble `(p, ρ)`. -/
noncomputable def guessingProb [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) (M : POVM X ι) : ℝ :=
  ∑ x : X, (p x).toReal * M.densityProb (ρ x) x

theorem guessingProb_eq_sum_trace_re [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) (M : POVM X ι) :
    guessingProb p ρ M = ∑ x : X, (M.effect x * ((p x).toReal • ρ x)).trace.re := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [POVM.densityProb, Matrix.mul_smul, trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Optimal guessing probability `p_g^{opt}(X | Q)_ρ = sup_M guessingProb p ρ M`. -/
noncomputable def optGuessingProb [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) : ℝ :=
  sSup (Set.range fun M : POVM X ι ↦ guessingProb p ρ M)

/-- Average quantum state `A = ∑ x, p(x) ρ_x` of a classical–quantum ensemble. -/
noncomputable def ensembleAvg [Fintype X] (p : PMF X) (ρ : X → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ x : X, (p x).toReal • ρ x

/-- Support projector `P_A = A^{1/2} A^{-1/2}` of a Hermitian matrix `A`. -/
noncomputable def supportProj [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun t : ℝ ↦ if t = 0 then 0 else 1) A

private theorem isHermitian_cfc_real [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    (cfc f A).IsHermitian :=
  cfc_predicate (p := IsSelfAdjoint) f A

private theorem real_spectrum_nonneg_of_posSemidef [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : t ∈ spectrum ℝ A) : 0 ≤ t := by
  have hmem : t ∈ Set.range hA.isHermitian.eigenvalues := by
    rwa [← hA.isHermitian.spectrum_real_eq_range_eigenvalues]
  obtain ⟨i, rfl⟩ := hmem
  exact hA.eigenvalues_nonneg i

/-- Pretty Good Measurement (PGM) POVM for `(p, ρ)`, completed on `ker(A)` by
`p(x) (1 - P_A)` so that the effects sum to `1` and satisfy exact fiber splitting. -/
noncomputable def pgmPOVM [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) (hρ : ∀ x, IsDensityMatrix (ρ x)) : POVM X ι :=
  let A := ensembleAvg p ρ
  let R := cfc (fun t : ℝ ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹) A
  let P := supportProj A
  { effect := fun x ↦ R * ((p x).toReal • ρ x) * R + (p x).toReal • (1 - P)
    posSemidef := fun x ↦ by
      classical
      have hA_psd : A.PosSemidef :=
        posSemidef_sum _ fun y _ ↦ (hρ y).posSemidef.smul ENNReal.toReal_nonneg
      have hRh : R.IsHermitian := isHermitian_cfc_real A _
      have hterm1 : (R * ((p x).toReal • ρ x) * R).PosSemidef := by
        simpa only [hRh.eq] using
          ((hρ x).posSemidef.smul ENNReal.toReal_nonneg).mul_mul_conjTranspose_same R
      have h1P : (1 - P).PosSemidef := by
        have h1 : (1 : Matrix ι ι ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) A := by
          simpa using (cfc_const (p := IsSelfAdjoint) (1 : ℝ) A hA_psd.isHermitian).symm
        change (1 - cfc (fun t : ℝ ↦ if t = 0 then 0 else 1) A).PosSemidef
        rw [h1, ← cfc_sub (fun _ ↦ 1) (fun t ↦ if t = 0 then 0 else 1) A
          ((A.finite_real_spectrum).continuousOn _) ((A.finite_real_spectrum).continuousOn _)]
        refine Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun t _ ↦ ?_)
        split_ifs <;> norm_num
      exact hterm1.add (h1P.smul ENNReal.toReal_nonneg)
    sum_effect := by
      classical
      have hA_psd : A.PosSemidef :=
        posSemidef_sum _ fun y _ ↦ (hρ y).posSemidef.smul ENNReal.toReal_nonneg
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_smul,
        Cslib.Probability.PMF.sum_toReal p, one_smul]
      change R * A * R + (1 - P) = 1
      have hRAR : R * A * R = P := by
        have h1 : R * A = cfc (fun t : ℝ ↦ (if t = 0 then 0 else (Real.sqrt t)⁻¹) * t) A := by
          have hid : A = cfc id A := (cfc_id ℝ A hA_psd.isHermitian.isSelfAdjoint).symm
          conv_lhs => rw [hid]
          exact (cfc_mul _ _ A ((A.finite_real_spectrum).continuousOn _)
            ((A.finite_real_spectrum).continuousOn _)).symm
        rw [h1, ← cfc_mul _ _ A ((A.finite_real_spectrum).continuousOn _)
          ((A.finite_real_spectrum).continuousOn _)]
        exact cfc_congr fun t ht ↦ by
          have htnn : 0 ≤ t := real_spectrum_nonneg_of_posSemidef hA_psd ht
          by_cases h0 : t = 0
          · simp [h0]
          · have hsq : Real.sqrt t ≠ 0 :=
              (Real.sqrt_pos.mpr (lt_of_le_of_ne htnn (Ne.symm h0))).ne'
            simp only [h0, ite_false]
            have hmul : (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹ =
                t / (Real.sqrt t * Real.sqrt t) := by ring
            rw [hmul, Real.mul_self_sqrt htnn, div_self h0]
      rw [hRAR, add_sub_cancel] }

/-- Guessing probability of the Pretty Good Measurement. -/
noncomputable def pgmGuessingProb [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) (hρ : ∀ x, IsDensityMatrix (ρ x)) : ℝ :=
  guessingProb p ρ (pgmPOVM p ρ hρ)

theorem pgmGuessingProb_eq_sum_trace_re [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    pgmGuessingProb p ρ hρ =
      ∑ x : X, ((pgmPOVM p ρ hρ).effect x * ((p x).toReal • ρ x)).trace.re :=
  guessingProb_eq_sum_trace_re p ρ (pgmPOVM p ρ hρ)

/-- Renes' quadratic PGM lower-bound function `g(x) = x^2 + (1 - x)^2 / (d - 1)`. -/
noncomputable def renesPgmBound (d : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 + (1 - x) ^ 2 / ((d : ℝ) - 1)

@[simp]
theorem renesPgmBound_one (x : ℝ) : renesPgmBound 1 x = x ^ 2 := by
  simp [renesPgmBound]

end Definitions

/-! ### Properties of `renesPgmBound` -/

section BoundProps

theorem renesPgmBound_eq_centered {d : ℕ} (hd : 2 ≤ d) (x : ℝ) :
    renesPgmBound d x =
      1 / (d : ℝ) + (d : ℝ) / ((d : ℝ) - 1) * (x - 1 / (d : ℝ)) ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd1 : (d : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show d ≠ 1 by omega))
  unfold renesPgmBound
  field_simp
  ring

theorem renesPgmBound_one_sub {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) :
    renesPgmBound d (1 - ε) = 1 - (2 * ε - (d : ℝ) * ε ^ 2 / ((d : ℝ) - 1)) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show d ≠ 1 by omega))
  unfold renesPgmBound
  field_simp
  ring

theorem renesPgmBound_convexOn {d : ℕ} (hd : 2 ≤ d) :
    ConvexOn ℝ Set.univ (renesPgmBound d) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [renesPgmBound_eq_centered hd, renesPgmBound_eq_centered hd, renesPgmBound_eq_centered hd]
  simp only [smul_eq_mul]
  have hcomb : a * x + b * y - 1 / (d : ℝ) =
      a * (x - 1 / (d : ℝ)) + b * (y - 1 / (d : ℝ)) := by
    have h1 : (1 : ℝ) / (d : ℝ) = (a + b) * (1 / (d : ℝ)) := by rw [hab, one_mul]
    linarith
  rw [hcomb]
  have hsq : (a * (x - 1 / (d : ℝ)) + b * (y - 1 / (d : ℝ))) ^ 2 ≤
      a * (x - 1 / (d : ℝ)) ^ 2 + b * (y - 1 / (d : ℝ)) ^ 2 := by
    have hdiff : a * (x - 1 / (d : ℝ)) ^ 2 + b * (y - 1 / (d : ℝ)) ^ 2 -
        (a * (x - 1 / (d : ℝ)) + b * (y - 1 / (d : ℝ))) ^ 2 =
        a * b * ((x - 1 / (d : ℝ)) - (y - 1 / (d : ℝ))) ^ 2 := by
      have ha2 : a ^ 2 = a - a * b := by nlinarith
      have hb2 : b ^ 2 = b - a * b := by nlinarith
      nlinarith
    have hnn : 0 ≤ a * b * ((x - 1 / (d : ℝ)) - (y - 1 / (d : ℝ))) ^ 2 :=
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    linarith
  have hcoeff : 0 ≤ (d : ℝ) / ((d : ℝ) - 1) := div_nonneg hd0.le hd1.le
  have hmul := mul_le_mul_of_nonneg_left hsq hcoeff
  have hlin : a * (1 / (d : ℝ)) + b * (1 / (d : ℝ)) = 1 / (d : ℝ) := by
    rw [← add_mul, hab, one_mul]
  nlinarith

theorem renesPgmBound_mono {d : ℕ} (hd : 2 ≤ d) {x y : ℝ}
    (hx : 1 / (d : ℝ) ≤ x) (hxy : x ≤ y) :
    renesPgmBound d x ≤ renesPgmBound d y := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [renesPgmBound_eq_centered hd, renesPgmBound_eq_centered hd]
  have hsq : (x - 1 / (d : ℝ)) ^ 2 ≤ (y - 1 / (d : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hx) (sub_le_sub_right hxy _) 2
  have hmul := mul_le_mul_of_nonneg_left hsq (div_nonneg hd0.le hd1.le)
  linarith

end BoundProps

/-! ### Renes PGM optimality theorem -/

section Optimality

theorem guessingProb_nonneg [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (M : POVM X ι) :
    0 ≤ guessingProb p ρ M :=
  Finset.sum_nonneg fun x _ ↦
    mul_nonneg ENNReal.toReal_nonneg (M.densityProb_nonneg (hρ x).posSemidef x)

theorem guessingProb_le_one [Fintype X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (M : POVM X ι) :
    guessingProb p ρ M ≤ 1 := by
  calc
    guessingProb p ρ M ≤ ∑ x : X, (p x).toReal * 1 := by
      refine Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      calc
        M.densityProb (ρ x) x ≤ ∑ y : X, M.densityProb (ρ x) y :=
          Finset.single_le_sum (fun y _ ↦ M.densityProb_nonneg (hρ x).posSemidef y) (mem_univ x)
        _ = 1 := by rw [M.sum_densityProb, (hρ x).trace_eq_one, Complex.one_re]
    _ = 1 := by simp [Cslib.Probability.PMF.sum_toReal]

/-- The guessing probability of any POVM on a nonempty ensemble is at least `1 / |X|` when
evaluated via the uniform constant POVM, hence `optGuessingProb ≥ 1 / |X|`. -/
theorem one_div_card_le_optGuessingProb [Fintype X] [Nonempty X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    1 / (Fintype.card X : ℝ) ≤ optGuessingProb p ρ := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card X : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let U : POVM X ι :=
    { effect := fun _ ↦ ((Fintype.card X : ℝ)⁻¹) • (1 : Matrix ι ι ℂ)
      posSemidef := fun _ ↦ PosSemidef.one.smul (inv_nonneg.mpr hpos.le)
      sum_effect := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          mul_inv_cancel₀ hpos.ne', one_smul] }
  have hU : guessingProb p ρ U = 1 / (Fintype.card X : ℝ) := by
    simp only [guessingProb, POVM.densityProb, U, Matrix.smul_mul, trace_smul,
      (hρ _).trace_eq_one, Complex.real_smul, mul_one, Complex.ofReal_re, ← Finset.sum_mul,
      Cslib.Probability.PMF.sum_toReal, one_mul, one_div]
  have hbdd : BddAbove (Set.range fun M : POVM X ι ↦ guessingProb p ρ M) :=
    ⟨1, by rintro _ ⟨M, rfl⟩; exact guessingProb_le_one p hρ M⟩
  rw [← hU]
  exact le_csSup hbdd ⟨U, rfl⟩

/-- Centered Cauchy–Schwarz proof of Renes: for every POVM `M` and `d = |X| ≥ 2`,
`pgmGuessingProb p ρ ≥ g(guessingProb p ρ M)`.
-/
theorem pgm_guessingProb_ge_renesPgmBound [Fintype X] [Fintype ι] [DecidableEq ι]
    (hd : 2 ≤ Fintype.card X) (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) (M : POVM X ι) :
    renesPgmBound (Fintype.card X) (guessingProb p ρ M) ≤ pgmGuessingProb p ρ hρ := by
  classical
  set d := Fintype.card X
  set A := ensembleAvg p ρ
  have hA_psd : A.PosSemidef :=
    posSemidef_sum _ fun x _ ↦ (hρ x).posSemidef.smul ENNReal.toReal_nonneg
  have hA_tr : A.trace = 1 := by
    simp only [A, ensembleAvg, trace_sum, trace_smul, (hρ _).trace_eq_one, Complex.real_smul,
      mul_one]
    exact_mod_cast Cslib.Probability.PMF.sum_toReal p
  -- Functional calculus powers `A^{1/4}`, `A^{1/2}`, `A^{-1/4}`, `A^{-1/2}`, and `P_A`.
  let fQuarter : ℝ → ℝ := fun t ↦ Real.sqrt (Real.sqrt t)
  let fInvQuarter : ℝ → ℝ := fun t ↦ if t = 0 then 0 else (Real.sqrt (Real.sqrt t))⁻¹
  let fInvSqrt : ℝ → ℝ := fun t ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹
  let fProj : ℝ → ℝ := fun t ↦ if t = 0 then 0 else 1
  let Q := cfc fQuarter A
  let IQ := cfc fInvQuarter A
  let IS := cfc fInvSqrt A
  let S := cfc Real.sqrt A
  let P := supportProj A
  have hQ_herm : Q.IsHermitian := isHermitian_cfc_real A fQuarter
  have hIQ_herm : IQ.IsHermitian := isHermitian_cfc_real A fInvQuarter
  have hIS_herm : IS.IsHermitian := isHermitian_cfc_real A fInvSqrt
  have hS_herm : S.IsHermitian := isHermitian_cfc_real A Real.sqrt
  have hP_herm : P.IsHermitian := isHermitian_cfc_real A fProj
  have hcfc_mul (f g : ℝ → ℝ) : cfc f A * cfc g A = cfc (fun t ↦ f t * g t) A :=
    (cfc_mul f g A ((A.finite_real_spectrum).continuousOn _)
      ((A.finite_real_spectrum).continuousOn _)).symm
  have hQQ : Q * Q = S := by
    rw [hcfc_mul]
    exact cfc_congr fun t _ ↦ Real.mul_self_sqrt (Real.sqrt_nonneg t)
  have hSS : S * S = A := by
    rw [hcfc_mul]
    exact (cfc_congr fun t ht ↦
      Real.mul_self_sqrt (real_spectrum_nonneg_of_posSemidef hA_psd ht)).trans
      (cfc_id ℝ A hA_psd.isHermitian.isSelfAdjoint)
  have hIQ_IQ : IQ * IQ = IS := by
    rw [hcfc_mul]
    exact cfc_congr fun t _ ↦ by
      by_cases h0 : t = 0
      · simp [fInvQuarter, fInvSqrt, h0]
      · simp [fInvQuarter, fInvSqrt, h0, ← mul_inv, Real.mul_self_sqrt (Real.sqrt_nonneg t)]
  have hIQ_Q : IQ * Q = P := by
    rw [hcfc_mul]
    exact cfc_congr fun t ht ↦ by
      have htnn : 0 ≤ t := real_spectrum_nonneg_of_posSemidef hA_psd ht
      by_cases h0 : t = 0
      · simp [fInvQuarter, fQuarter, h0]
      · have hq : Real.sqrt (Real.sqrt t) ≠ 0 :=
          (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (lt_of_le_of_ne htnn (Ne.symm h0)))).ne'
        simp [fInvQuarter, fQuarter, h0, inv_mul_cancel₀ hq]
  have hQ_IQ : Q * IQ = P := by
    rw [hcfc_mul, show (fun t ↦ fQuarter t * fInvQuarter t) = (fun t ↦ fInvQuarter t * fQuarter t)
      from funext fun t ↦ mul_comm _ _, ← hcfc_mul, hIQ_Q]
  have hIQ_A_IQ : IQ * A * IQ = S := by
    calc
      IQ * A * IQ = IQ * (S * S) * IQ := by rw [hSS]
      _ = IQ * (Q * Q * (Q * Q)) * IQ := by rw [hQQ]
      _ = (IQ * Q) * Q * (Q * (Q * IQ)) := by simp only [Matrix.mul_assoc]
      _ = P * Q * (Q * P) := by rw [hIQ_Q, hQ_IQ]
      _ = (P * Q) * Q * P := by simp only [Matrix.mul_assoc]
      _ = Q * Q * P := by
        have hPQ : P * Q = Q := by
          rw [show P = cfc fProj A from rfl, hcfc_mul]
          exact cfc_congr fun t _ ↦ by
            by_cases h0 : t = 0 <;> simp [fProj, fQuarter, h0]
        rw [hPQ]
      _ = S * P := by rw [hQQ]
      _ = S := by
        rw [show P = cfc fProj A from rfl, hcfc_mul]
        exact cfc_congr fun t _ ↦ by
          by_cases h0 : t = 0 <;> simp [fProj, h0]
  -- Support property: `P * A_x = A_x` and `A_x * P = A_x`, and `(1 - P) * A_x = 0`.
  have hPAx (x : X) : P * ((p x).toReal • ρ x) = (p x).toReal • ρ x := by
    have h1P_psd : (1 - P).PosSemidef := by
      have h1 : (1 : Matrix ι ι ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) A := by
        simpa using (cfc_const (p := IsSelfAdjoint) (1 : ℝ) A hA_psd.isHermitian).symm
      change (1 - cfc fProj A).PosSemidef
      rw [h1, ← cfc_sub (fun _ ↦ 1) fProj A
        ((A.finite_real_spectrum).continuousOn _) ((A.finite_real_spectrum).continuousOn _)]
      refine Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun t _ ↦ ?_)
      simp only [fProj]; split_ifs <;> norm_num
    have h1P_A : (1 - P) * A = 0 := by
      rw [sub_mul, Matrix.one_mul]
      have hPA : P * A = A := by
        have hid : A = cfc id A := (cfc_id ℝ A hA_psd.isHermitian.isSelfAdjoint).symm
        calc
          P * A = cfc fProj A * cfc id A := by
            conv_lhs => arg 1; change cfc fProj A
            conv_lhs => arg 2; rw [hid]
          _ = cfc (fun t ↦ fProj t * id t) A := hcfc_mul fProj id
          _ = cfc id A := cfc_congr fun t _ ↦ by by_cases h0 : t = 0 <;> simp [fProj, h0]
          _ = A := cfc_id ℝ A hA_psd.isHermitian.isSelfAdjoint
      rw [hPA, sub_self]
    have hAx_psd : ((p x).toReal • ρ x).PosSemidef := (hρ x).posSemidef.smul ENNReal.toReal_nonneg
    have htr0 : ((1 - P) * ((p x).toReal • ρ x)).trace = 0 := by
      have hnonneg (y : X) : (0 : ℂ) ≤ ((1 - P) * ((p y).toReal • ρ y)).trace :=
        h1P_psd.trace_mul_nonneg ((hρ y).posSemidef.smul ENNReal.toReal_nonneg)
      have hsum0 : ∑ y : X, ((1 - P) * ((p y).toReal • ρ y)).trace = 0 := by
        rw [← trace_sum, ← Finset.mul_sum]
        change ((1 - P) * A).trace = 0
        rw [h1P_A, trace_zero]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ ↦ hnonneg y)).mp hsum0 x (mem_univ x)
    have hzero := (h1P_psd.trace_mul_eq_zero_iff hAx_psd).mp htr0
    rw [sub_mul, Matrix.one_mul, sub_eq_zero] at hzero
    exact hzero.symm
  have hAxP (x : X) : ((p x).toReal • ρ x) * P = (p x).toReal • ρ x := by
    have h := congrArg Matrix.conjTranspose (hPAx x)
    rw [conjTranspose_mul, hP_herm.eq,
      ((hρ x).posSemidef.smul ENNReal.toReal_nonneg).isHermitian.eq] at h
    exact h
  -- Define centered Hermitian matrices `Xc x = IQ * A_x * IQ - (1/d) S` and
  -- `Yc x = Q * E_x * Q - (1/d) S`.
  let Xmat (x : X) : Matrix ι ι ℂ := IQ * ((p x).toReal • ρ x) * IQ
  let Ymat (x : X) : Matrix ι ι ℂ := Q * M.effect x * Q
  let Hbar : Matrix ι ι ℂ := ((d : ℝ)⁻¹) • S
  have hX_herm (x : X) : (Xmat x).IsHermitian := by
    have h : (IQ * ((p x).toReal • ρ x) * IQᴴ).PosSemidef :=
      ((hρ x).posSemidef.smul ENNReal.toReal_nonneg).mul_mul_conjTranspose_same IQ
    simpa only [Xmat, hIQ_herm.eq] using h.isHermitian
  have hY_herm (x : X) : (Ymat x).IsHermitian := by
    have h := (M.posSemidef x).mul_mul_conjTranspose_same Q
    simpa only [Ymat, hQ_herm.eq] using h.isHermitian
  have hsumX : ∑ x : X, Xmat x = S := by
    simp only [Xmat, ← Finset.sum_mul, ← Finset.mul_sum]
    exact hIQ_A_IQ
  have hsumY : ∑ x : X, Ymat x = S := by
    simp only [Ymat, ← Finset.sum_mul, ← Finset.mul_sum, M.sum_effect, Matrix.mul_one, hQQ]
  have hS_normSq : (S * S).trace.re = 1 := by
    rw [hSS, hA_tr, Complex.one_re]
  -- Evaluate the three Frobenius sums:
  -- 1. `∑ x, Re Tr(Xmat x * Xmat x) = pgmGuessingProb p ρ hρ`.
  have hXX : ∑ x : X, (Xmat x * Xmat x).trace.re = pgmGuessingProb p ρ hρ := by
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    change (IQ * ((p x).toReal • ρ x) * IQ * (IQ * ((p x).toReal • ρ x) * IQ)).trace.re =
      (p x).toReal * ((IS * ((p x).toReal • ρ x) * IS + (p x).toReal • (1 - P)) * ρ x).trace.re
    have h1 : (IQ * ((p x).toReal • ρ x) * IQ * (IQ * ((p x).toReal • ρ x) * IQ)).trace =
        (IS * ((p x).toReal • ρ x) * IS * ((p x).toReal • ρ x)).trace := by
      calc
        (IQ * ((p x).toReal • ρ x) * IQ * (IQ * ((p x).toReal • ρ x) * IQ)).trace
            = (IQ * (IQ * ((p x).toReal • ρ x) * (IQ * IQ) * ((p x).toReal • ρ x))).trace := by
          rw [show IQ * ((p x).toReal • ρ x) * IQ * (IQ * ((p x).toReal • ρ x) * IQ) =
            (IQ * ((p x).toReal • ρ x) * (IQ * IQ) * ((p x).toReal • ρ x)) * IQ by
            simp only [Matrix.mul_assoc], trace_mul_comm]
        _ = (IS * ((p x).toReal • ρ x) * IS * ((p x).toReal • ρ x)).trace := by
          simp only [← Matrix.mul_assoc, hIQ_IQ]
    have h1P_zero : ((p x).toReal • (1 - P)) * ((p x).toReal • ρ x) = 0 := by
      rw [Matrix.smul_mul, sub_mul, Matrix.one_mul, hPAx x, sub_self, smul_zero]
    rw [h1]
    have h3 : (p x).toReal *
        ((IS * ((p x).toReal • ρ x) * IS + (p x).toReal • (1 - P)) * ρ x).trace.re =
        ((IS * ((p x).toReal • ρ x) * IS + (p x).toReal • (1 - P)) *
          ((p x).toReal • ρ x)).trace.re := by
      conv_rhs =>
        rw [Matrix.mul_smul, trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
    rw [h3, add_mul, h1P_zero, add_zero]
  -- 2. `∑ x, Re Tr(Xmat x * Ymat x) = guessingProb p ρ M`.
  have hXY : ∑ x : X, (Xmat x * Ymat x).trace.re = guessingProb p ρ M := by
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have h1 : (Xmat x * Ymat x).trace = (M.effect x * ((p x).toReal • ρ x)).trace := by
      calc
        (IQ * ((p x).toReal • ρ x) * IQ * (Q * M.effect x * Q)).trace
            = (Q * (IQ * ((p x).toReal • ρ x) * (IQ * Q) * M.effect x)).trace := by
          rw [show IQ * ((p x).toReal • ρ x) * IQ * (Q * M.effect x * Q) =
            (IQ * ((p x).toReal • ρ x) * (IQ * Q) * M.effect x) * Q by
            simp only [Matrix.mul_assoc], trace_mul_comm]
        _ = ((Q * IQ) * ((p x).toReal • ρ x) * (IQ * Q) * M.effect x).trace := by
          simp only [Matrix.mul_assoc]
        _ = (P * ((p x).toReal • ρ x) * P * M.effect x).trace := by rw [hQ_IQ, hIQ_Q]
        _ = (((p x).toReal • ρ x) * M.effect x).trace := by rw [hPAx x, hAxP x]
        _ = (M.effect x * ((p x).toReal • ρ x)).trace := trace_mul_comm _ _
    rw [h1, Matrix.mul_smul, trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  -- 3. `∑ x, Re Tr(Ymat x * Ymat x) ≤ 1`.
  have hYY : ∑ x : X, (Ymat x * Ymat x).trace.re ≤ 1 := by
    calc
      ∑ x : X, (Ymat x * Ymat x).trace.re ≤ ∑ x : X, (S * M.effect x * S).trace.re := by
        refine Finset.sum_le_sum fun x _ ↦ ?_
        have hY_eq : (Ymat x * Ymat x).trace = ((S * M.effect x * S) * M.effect x).trace := by
          calc
            (Q * M.effect x * Q * (Q * M.effect x * Q)).trace
                = (Q * (Q * M.effect x * (Q * Q) * M.effect x)).trace := by
              rw [show Q * M.effect x * Q * (Q * M.effect x * Q) =
                (Q * M.effect x * (Q * Q) * M.effect x) * Q by
                simp only [Matrix.mul_assoc], trace_mul_comm]
            _ = ((Q * Q) * M.effect x * (Q * Q) * M.effect x).trace := by
              simp only [Matrix.mul_assoc]
            _ = (S * M.effect x * S * M.effect x).trace := by rw [hQQ]
        have hEx_le : M.effect x ≤ 1 := by
          rw [← M.sum_effect, Matrix.le_iff]
          have hdiff : (∑ y : X, M.effect y) - M.effect x =
              ∑ y ∈ Finset.univ.erase x, M.effect y := by
            rw [← Finset.add_sum_erase _ _ (mem_univ x), add_sub_cancel_left]
          rw [hdiff]
          exact posSemidef_sum _ fun y _ ↦ M.posSemidef y
        have hSMS : (S * M.effect x * S).PosSemidef := by
          simpa only [hS_herm.eq] using (M.posSemidef x).mul_mul_conjTranspose_same S
        have htr := (hSMS.trace_mul_nonneg (Matrix.le_iff.mp hEx_le))
        rw [Matrix.mul_sub, Matrix.mul_one, trace_sub] at htr
        have hre := (Complex.nonneg_iff.mp htr).1
        rw [Complex.sub_re, ← hY_eq] at hre
        linarith
      _ = 1 := by
        rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, M.sum_effect,
          Matrix.mul_one, hS_normSq]
  -- Apply Cauchy–Schwarz to centered Hermitian matrices `Xc x = Xmat x - Hbar`, `Yc x = Ymat x -
  -- Hbar`.
  have hnorm_ge (A_m : Matrix ι ι ℂ) (hAm : A_m.IsHermitian) : 0 ≤ (A_m * A_m).trace.re := by
    have h := (posSemidef_conjTranspose_mul_self A_m).trace_nonneg
    rw [hAm.eq] at h
    exact (Complex.nonneg_iff.mp h).1
  have hcentered_X :
      ∑ x : X, ((Xmat x - Hbar) * (Xmat x - Hbar)).trace.re =
        pgmGuessingProb p ρ hρ - 1 / (d : ℝ) := by
    have hterm (x : X) :
        ((Xmat x - Hbar) * (Xmat x - Hbar)).trace.re =
          (Xmat x * Xmat x).trace.re - 2 * (d : ℝ)⁻¹ * (Xmat x * S).trace.re +
            (d : ℝ)⁻¹ ^ 2 * (S * S).trace.re := by
      have hcomm : (Hbar * Xmat x).trace = (Xmat x * Hbar).trace := trace_mul_comm _ _
      simp only [sub_mul, mul_sub, trace_sub, Complex.sub_re, hcomm]
      simp only [Hbar, Matrix.smul_mul, Matrix.mul_smul, trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hXX, ← Complex.re_sum, ← trace_sum,
      ← Finset.sum_mul, hsumX, hS_normSq]
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have hcentered_Y :
      ∑ x : X, ((Ymat x - Hbar) * (Ymat x - Hbar)).trace.re =
        (∑ x : X, (Ymat x * Ymat x).trace.re) - 1 / (d : ℝ) := by
    have hterm (x : X) :
        ((Ymat x - Hbar) * (Ymat x - Hbar)).trace.re =
          (Ymat x * Ymat x).trace.re - 2 * (d : ℝ)⁻¹ * (Ymat x * S).trace.re +
            (d : ℝ)⁻¹ ^ 2 * (S * S).trace.re := by
      have hcomm : (Hbar * Ymat x).trace = (Ymat x * Hbar).trace := trace_mul_comm _ _
      simp only [sub_mul, mul_sub, trace_sub, Complex.sub_re, hcomm]
      simp only [Hbar, Matrix.smul_mul, Matrix.mul_smul, trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Complex.re_sum, ← trace_sum,
      ← Finset.sum_mul, hsumY, hS_normSq]
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have hcentered_XY :
      ∑ x : X, ((Xmat x - Hbar) * (Ymat x - Hbar)).trace.re =
        guessingProb p ρ M - 1 / (d : ℝ) := by
    have hterm (x : X) :
        ((Xmat x - Hbar) * (Ymat x - Hbar)).trace.re =
          (Xmat x * Ymat x).trace.re - (d : ℝ)⁻¹ * (Xmat x * S).trace.re -
            (d : ℝ)⁻¹ * (Ymat x * S).trace.re + (d : ℝ)⁻¹ ^ 2 * (S * S).trace.re := by
      have hcomm : (Hbar * Ymat x).trace = (Ymat x * Hbar).trace := trace_mul_comm _ _
      simp only [sub_mul, mul_sub, trace_sub, Complex.sub_re, hcomm]
      simp only [Hbar, Matrix.smul_mul, Matrix.mul_smul, trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hXY, ← Complex.re_sum, ← trace_sum,
      ← Finset.sum_mul, hsumX, hsumY, hS_normSq]
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  have hsmul_herm (r : ℝ) {B : Matrix ι ι ℂ} (hB : B.IsHermitian) : (r • B).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hB.eq, star_trivial]
  -- Discriminant Cauchy–Schwarz for `t ↦ ∑ x, Re Tr((Xc x - t Yc x)²)` ≥ 0.
  have hCS : (guessingProb p ρ M - 1 / (d : ℝ)) ^ 2 ≤
      (pgmGuessingProb p ρ hρ - 1 / (d : ℝ)) *
        ((∑ x : X, (Ymat x * Ymat x).trace.re) - 1 / (d : ℝ)) := by
    set a := pgmGuessingProb p ρ hρ - 1 / (d : ℝ)
    set b := guessingProb p ρ M - 1 / (d : ℝ)
    set c := (∑ x : X, (Ymat x * Ymat x).trace.re) - 1 / (d : ℝ)
    have hquad (t : ℝ) : 0 ≤ a - 2 * t * b + t ^ 2 * c := by
      have hsum_nn : 0 ≤ ∑ x : X,
          (((Xmat x - Hbar) - t • (Ymat x - Hbar)) *
            ((Xmat x - Hbar) - t • (Ymat x - Hbar))).trace.re :=
        Finset.sum_nonneg fun x _ ↦ hnorm_ge _
          (((hX_herm x).sub (hsmul_herm _ hS_herm)).sub
            (hsmul_herm _ ((hY_herm x).sub (hsmul_herm _ hS_herm))))
      have hexp : ∑ x : X,
          (((Xmat x - Hbar) - t • (Ymat x - Hbar)) *
            ((Xmat x - Hbar) - t • (Ymat x - Hbar))).trace.re = a - 2 * t * b + t ^ 2 * c := by
        have hterm (x : X) :
            (((Xmat x - Hbar) - t • (Ymat x - Hbar)) *
              ((Xmat x - Hbar) - t • (Ymat x - Hbar))).trace.re =
              ((Xmat x - Hbar) * (Xmat x - Hbar)).trace.re -
                2 * t * ((Xmat x - Hbar) * (Ymat x - Hbar)).trace.re +
                t ^ 2 * ((Ymat x - Hbar) * (Ymat x - Hbar)).trace.re := by
          generalize Xmat x - Hbar = Xc
          generalize Ymat x - Hbar = Yc
          have hcomm : (Yc * Xc).trace = (Xc * Yc).trace := trace_mul_comm _ _
          simp only [sub_mul, mul_sub, trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.mul_smul,
            trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero, hcomm]
          ring
        simp_rw [hterm]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hcentered_X, hcentered_XY, hcentered_Y, a, b, c]
      linarith
    have ha_nn : 0 ≤ a := by simpa using hquad 0
    have hc_nn : 0 ≤ c := by
      have hsum_nn : 0 ≤ ∑ x : X, ((Ymat x - Hbar) * (Ymat x - Hbar)).trace.re :=
        Finset.sum_nonneg fun x _ ↦ hnorm_ge _ ((hY_herm x).sub (hsmul_herm _ hS_herm))
      linarith [hcentered_Y]
    by_cases hc0 : c = 0
    · have hb0 : b = 0 := by
        by_contra hbne
        have h1 := hquad ((a + 1) / (2 * b))
        have h2 : a - 2 * ((a + 1) / (2 * b)) * b + ((a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
          field_simp; ring
        rw [hc0] at h1; linarith
      simp [hc0, hb0]
    · have hcp : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc0)
      have hmin := hquad (b / c)
      have hsimp : a - 2 * (b / c) * b + (b / c) ^ 2 * c = a - b ^ 2 / c := by
        field_simp; ring
      rw [hsimp] at hmin
      exact (div_le_iff₀ hcp).mp (by linarith)
  have ha_nn : 0 ≤ pgmGuessingProb p ρ hρ - 1 / (d : ℝ) := by
    have hsum_nn : 0 ≤ ∑ x : X, ((Xmat x - Hbar) * (Xmat x - Hbar)).trace.re :=
      Finset.sum_nonneg fun x _ ↦ hnorm_ge _ ((hX_herm x).sub (hsmul_herm _ hS_herm))
    linarith [hcentered_X]
  have hc_le : (∑ x : X, (Ymat x * Ymat x).trace.re) - 1 / (d : ℝ) ≤ ((d : ℝ) - 1) / (d : ℝ) := by
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [sub_div, div_self hd0]
    linarith
  have hCS2 : (guessingProb p ρ M - 1 / (d : ℝ)) ^ 2 ≤
      (pgmGuessingProb p ρ hρ - 1 / (d : ℝ)) * (((d : ℝ) - 1) / (d : ℝ)) :=
    hCS.trans (mul_le_mul_of_nonneg_left hc_le ha_nn)
  rw [renesPgmBound_eq_centered hd]
  have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdiv := (div_le_iff₀ (div_pos hd1 hd0)).mpr hCS2
  have hrew : (guessingProb p ρ M - 1 / (d : ℝ)) ^ 2 / (((d : ℝ) - 1) / (d : ℝ)) =
      (d : ℝ) / ((d : ℝ) - 1) * (guessingProb p ρ M - 1 / (d : ℝ)) ^ 2 := by
    field_simp
  linarith

/-- : Optimality of the Pretty Good Measurement,
`p_g^{pgm}(X | Q)_ρ ≥ g(p_g^{opt}(X | Q)_ρ)`.
-/
theorem pgm_optimality [Fintype X] [Fintype ι] [DecidableEq ι]
    (hd : 2 ≤ Fintype.card X) (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    renesPgmBound (Fintype.card X) (optGuessingProb p ρ) ≤ pgmGuessingProb p ρ hρ := by
  classical
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hne : (Set.range fun M : POVM X ι ↦ guessingProb p ρ M).Nonempty :=
    ⟨guessingProb p ρ (POVM.const (Classical.arbitrary X)), ⟨_, rfl⟩⟩
  have hge : 1 / (Fintype.card X : ℝ) ≤ optGuessingProb p ρ :=
    one_div_card_le_optGuessingProb p hρ
  -- By continuity/monotonicity of `renesPgmBound` on `[1/d, 1]`, check every `ε > 0` or directly:
  -- Actually `renesPgmBound d` is continuous and monotone on `[1/d, ∞)`, and `optGuessingProb`
  -- is `sSup` of a bounded nonempty set!
  by_contra hlt
  push Not at hlt
  set gOpt := renesPgmBound (Fintype.card X) (optGuessingProb p ρ)
  set pPgm := pgmGuessingProb p ρ hρ
  have hcont : Continuous (renesPgmBound (Fintype.card X)) := by
    unfold renesPgmBound
    fun_prop
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuous_iff.mp hcont (optGuessingProb p ρ)
    (gOpt - pPgm) (sub_pos.mpr hlt)
  obtain ⟨y, ⟨M, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hne (sub_lt_self (optGuessingProb p ρ) hδpos)
  have hle_opt : guessingProb p ρ M ≤ optGuessingProb p ρ :=
    le_csSup ⟨1, by rintro _ ⟨M', rfl⟩; exact guessingProb_le_one p hρ M'⟩ ⟨M, rfl⟩
  have hdist : dist (guessingProb p ρ M) (optGuessingProb p ρ) < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle_opt)]
    linarith
  have hgdist := hδ (guessingProb p ρ M) hdist
  rw [Real.dist_eq] at hgdist
  have hpgmM := pgm_guessingProb_ge_renesPgmBound hd p hρ M
  have hlt2 : gOpt - renesPgmBound (Fintype.card X) (guessingProb p ρ M) < gOpt - pPgm :=
    (le_abs_self _).trans_lt (by simpa only [abs_sub_comm] using hgdist)
  linarith

end Optimality

/-! ### PGM splitting identity for composite classical functions -/

section Splitting

/-- Fiber-splitting identity for the PGM: summing `pgmPOVM p ρ` over the preimage `{x | f x = z}`
gives the exact PGM POVM for the pushed-forward classical–quantum ensemble `(p.map f, ρ_f)`. -/
theorem pgmPOVM_effect_sum_fiber {Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z]
    [Fintype ι] [DecidableEq ι]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x))
    (f : X → Z) (ρf : Z → Matrix ι ι ℂ) (hρf : ∀ z, IsDensityMatrix (ρf z))
    (hf : ∀ z, ((p.map f) z).toReal • ρf z =
      ∑ x ∈ Finset.univ.filter (fun x ↦ f x = z), (p x).toReal • ρ x)
    (z : Z) :
    ∑ x ∈ Finset.univ.filter (fun x ↦ f x = z), (pgmPOVM p ρ hρ).effect x =
      (pgmPOVM (p.map f) ρf hρf).effect z := by
  have havg : ensembleAvg (p.map f) ρf = ensembleAvg p ρ := by
    simp only [ensembleAvg, hf]
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _
  have hpmap : ((p.map f) z).toReal =
      ∑ x ∈ Finset.univ.filter (fun x ↦ f x = z), (p x).toReal := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun x _ ↦ by
      split_ifs <;> simp [PMF.apply_ne_top])]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : z = f x
    · simp [h]
    · simp [h, Ne.symm h]
  change ∑ x ∈ Finset.univ.filter (fun x ↦ f x = z),
      (cfc (fun t : ℝ ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹) (ensembleAvg p ρ) *
        ((p x).toReal • ρ x) *
        cfc (fun t : ℝ ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹) (ensembleAvg p ρ) +
        (p x).toReal • (1 - supportProj (ensembleAvg p ρ))) =
    cfc (fun t : ℝ ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹) (ensembleAvg (p.map f) ρf) *
      (((p.map f) z).toReal • ρf z) *
      cfc (fun t : ℝ ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹) (ensembleAvg (p.map f) ρf) +
      ((p.map f) z).toReal • (1 - supportProj (ensembleAvg (p.map f) ρf))
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_smul,
    ← hpmap, ← hf z, havg]

end Splitting

end CslibFrontier.Quantum
