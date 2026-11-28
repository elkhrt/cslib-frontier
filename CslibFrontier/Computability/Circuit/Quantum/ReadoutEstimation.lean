/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Born-Rule Readout Estimation and Variational Bounds for Quantum Circuits

General measurement-readout concentration and Rayleigh–Ritz energy bounds for `n`-qubit quantum
circuits (`Cslib.Quantum.Circuit`), supporting quantum ground-state energy and phase-estimation
algorithms:

1. **PMF-to-`measureProb` readout bridge** (`sum_measure_ite_eq_ofReal_measureProb`): relates the
   `ENNReal` outcome-event mass `∑ y, if P y then C.measure x y else 0` of a circuit `C` started in
   `|x⟩` to `ENNReal.ofReal (Cslib.Quantum.measureProb (C.run x) (Finset.univ.filter P))`.
2. **Born-rule readout tolerance monotonicity and Chebyshev concentration**
   (`measureProb_readout_mono`, `one_sub_mse_div_sq_le_measureProb_readout`,
   `ofReal_le_sum_measure_readout_of_mse_le`): proves that if a classical readout
   `readout : (Fin n → Bool) → ℝ` of `C.run x` has mean-squared error at most `δ * ε ^ 2` around a
   target quantity `E : ℝ` (`ε > 0`, `0 ≤ δ ≤ 1`), then `C.measure x` outputs an `ε`-accurate
   estimate of `E` with probability at least `1 - δ`.
3. **Locality and gate-budget composition** (`arity_le_append_iff`): composing state-preparation and
   readout circuits preserves `k`-locality (`∀ g ∈ C, g.arity ≤ k`).
4. **Variational Rayleigh–Ritz ground-energy bound** (`qubitGroundEnergy`, `energyExpectation`,
   `qubitGroundEnergy_mul_norm_sq_le_energyExpectation`,
   `qubitGroundEnergy_le_circuit_energyExpectation`): for any Hermitian `n`-qubit Hamiltonian
   `H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ`, every quantum circuit output state `C.run x` has
   energy expectation at least the minimum eigenvalue of `H`.
-/

public section

namespace CslibFrontier.Quantum

open Cslib.Quantum Finset Matrix
open scoped ComplexInnerProductSpace ComplexOrder

variable {n : ℕ}

/-! ### 1. Born-Rule Readout Success Probability and Chebyshev Concentration -/

/-- Exact bridge between the `ENNReal` `PMF` event sum of `Cslib.Quantum.Circuit.measure` and
`ENNReal.ofReal` of `Cslib.Quantum.measureProb`. -/
theorem sum_measure_ite_eq_ofReal_measureProb (C : Circuit n) (x : Fin n → Bool)
    (P : (Fin n → Bool) → Prop) [DecidablePred P] :
    (∑ y : Fin n → Bool, if P y then C.measure x y else 0) =
      ENNReal.ofReal (measureProb (C.run x) (univ.filter P)) := by
  rw [← sum_filter, measureProb, ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  exact sum_congr rfl fun y _ ↦ Circuit.measure_apply C x y

/-- Monotonicity of Born-rule readout estimation probability in the error tolerance `ε₁ ≤ ε₂`. -/
theorem measureProb_readout_mono (ψ : Qubits n) (readout : (Fin n → Bool) → ℝ) (E : ℝ)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    measureProb ψ (univ.filter fun y ↦ |readout y - E| ≤ ε₁) ≤
      measureProb ψ (univ.filter fun y ↦ |readout y - E| ≤ ε₂) :=
  measureProb_mono ψ fun _ hy ↦
    mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.trans hε⟩

/-- Mean-squared Born-rule readout error `∑_y (readout y - E)^2 * ‖ψ_y‖^2` of a state `ψ` around
target value `E : ℝ`. -/
noncomputable def readoutMeanSqError (ψ : Qubits n) (readout : (Fin n → Bool) → ℝ) (E : ℝ) : ℝ :=
  ∑ y : Fin n → Bool, (readout y - E) ^ 2 * ‖ψ.ofLp y‖ ^ 2

theorem readoutMeanSqError_nonneg (ψ : Qubits n) (readout : (Fin n → Bool) → ℝ) (E : ℝ) :
    0 ≤ readoutMeanSqError ψ readout E :=
  sum_nonneg fun _ _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Chebyshev / Markov concentration for Born-rule circuit readouts**: for any unit state
`ψ : Qubits n` (`‖ψ‖ = 1`), classical readout `readout : (Fin n → Bool) → ℝ`, target `E : ℝ`, and
`ε > 0`, the probability of measuring an outcome within `ε` of `E` is at least
`1 - readoutMeanSqError ψ readout E / ε ^ 2`. -/
theorem one_sub_mse_div_sq_le_measureProb_readout {ψ : Qubits n} (hψ : ‖ψ‖ = 1)
    (readout : (Fin n → Bool) → ℝ) (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    1 - readoutMeanSqError ψ readout E / ε ^ 2 ≤
      measureProb ψ (univ.filter fun y ↦ |readout y - E| ≤ ε) := by
  let S := univ.filter fun y : Fin n → Bool ↦ |readout y - E| ≤ ε
  have hcompl := measureProb_compl ψ S
  rw [hψ, one_pow] at hcompl
  have htail : ε ^ 2 * measureProb ψ Sᶜ ≤ readoutMeanSqError ψ readout E := by
    calc ε ^ 2 * measureProb ψ Sᶜ
        = ∑ y ∈ Sᶜ, ε ^ 2 * ‖ψ.ofLp y‖ ^ 2 := by rw [measureProb, mul_sum]
      _ ≤ ∑ y ∈ Sᶜ, (readout y - E) ^ 2 * ‖ψ.ofLp y‖ ^ 2 :=
          sum_le_sum fun y hy ↦ by
            have hgt : ε < |readout y - E| := by
              have hnot : y ∉ S := mem_compl.mp hy
              simp only [S, mem_filter, mem_univ, true_and, not_le] at hnot
              exact hnot
            have hsq : ε ^ 2 ≤ (readout y - E) ^ 2 := by
              rw [← sq_abs (readout y - E)]
              exact pow_le_pow_left₀ hε.le hgt.le 2
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ ≤ ∑ y ∈ univ, (readout y - E) ^ 2 * ‖ψ.ofLp y‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
      _ = readoutMeanSqError ψ readout E := rfl
  have hdiv : measureProb ψ Sᶜ ≤ readoutMeanSqError ψ readout E / ε ^ 2 :=
    (le_div_iff₀' (sq_pos_of_pos hε)).mpr htail
  linarith

/-- Circuit-level `ENNReal` readout accuracy guarantee: if `readoutMeanSqError (C.run x) readout E
≤ δ * ε ^ 2` (`ε > 0`), then `C.measure x` achieves additive error `≤ ε` with probability at least
`ENNReal.ofReal (1 - δ)`. -/
theorem ofReal_le_sum_measure_readout_of_mse_le (C : Circuit n) (x : Fin n → Bool)
    (readout : (Fin n → Bool) → ℝ) (E : ℝ) {ε δ : ℝ} (hε : 0 < ε)
    (hmse : readoutMeanSqError (C.run x) readout E ≤ δ * ε ^ 2) :
    ENNReal.ofReal (1 - δ) ≤
      ∑ y : Fin n → Bool, if |readout y - E| ≤ ε then C.measure x y else 0 := by
  rw [sum_measure_ite_eq_ofReal_measureProb]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcheb := one_sub_mse_div_sq_le_measureProb_readout (Circuit.norm_run C x) readout E hε
  have hdiv : readoutMeanSqError (C.run x) readout E / ε ^ 2 ≤ δ :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mpr hmse
  linarith

/-- Sequential circuit composition preserves `k`-locality of placed gates. -/
theorem arity_le_append_iff (C₁ C₂ : Circuit n) (k : ℕ) :
    (∀ g ∈ C₁ ++ C₂, g.arity ≤ k) ↔ (∀ g ∈ C₁, g.arity ≤ k) ∧ (∀ g ∈ C₂, g.arity ≤ k) := by
  simp [List.mem_append, or_imp, forall_and]

/-! ### 2. Variational Rayleigh–Ritz Ground-State Energy Lower Bound -/

/-- Ground-state energy (minimum eigenvalue) of a Hermitian `n`-qubit Hamiltonian
`H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ`. -/
noncomputable def qubitGroundEnergy {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian) : ℝ :=
  (univ.image hH.eigenvalues).min' (univ_nonempty.image _)

/-- Real energy expectation `Re ⟨ψ, H ψ⟩` of an `n`-qubit state `ψ : Qubits n`. -/
noncomputable def energyExpectation (H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (ψ : Qubits n) : ℝ :=
  RCLike.re ⟪ψ, (Matrix.toEuclideanCLM (n := Fin n → Bool) (𝕜 := ℂ) H) ψ⟫

/-- **Rayleigh–Ritz variational lower bound**: for any Hermitian `n`-qubit Hamiltonian `H` and any
state `ψ : Qubits n`, `qubitGroundEnergy hH * ‖ψ‖ ^ 2 ≤ energyExpectation H ψ`. -/
theorem qubitGroundEnergy_mul_norm_sq_le_energyExpectation
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ} (hH : H.IsHermitian) (ψ : Qubits n) :
    qubitGroundEnergy hH * ‖ψ‖ ^ 2 ≤ energyExpectation H ψ := by
  let E₀ := qubitGroundEnergy hH
  have hpsd : (H - (E₀ : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).PosSemidef := by
    let U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := hH.eigenvectorUnitary.1
    rw [hH.spectral_theorem]
    change (U * diagonal (Complex.ofReal ∘ hH.eigenvalues) * star U -
      (E₀ : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).PosSemidef
    have h1 : U * (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * star U = 1 := by
      rw [Matrix.mul_one]
      exact Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
    have hdiff :
        U * diagonal (Complex.ofReal ∘ hH.eigenvalues) * star U -
          (E₀ : ℂ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        U * diagonal (fun k ↦ ((hH.eigenvalues k - E₀ : ℝ) : ℂ)) * Uᴴ := by
      conv_lhs => rw [← h1]
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← sub_mul, ← mul_sub, star_eq_conjTranspose]
      congr 2; ext a b
      simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
        Function.comp_apply, smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    rw [hdiff]
    refine (posSemidef_diagonal_iff.mpr fun k ↦ ?_).mul_mul_conjTranspose_same _
    have hle : E₀ ≤ hH.eigenvalues k :=
      min'_le _ _ (mem_image.mpr ⟨k, mem_univ k, rfl⟩)
    exact_mod_cast sub_nonneg.mpr hle
  have hnonneg : 0 ≤ RCLike.re (star ψ.ofLp ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ ψ.ofLp)) :=
    (RCLike.nonneg_iff.mp (hpsd.dotProduct_mulVec_nonneg ψ.ofLp)).1
  have hinner_eq (M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
      RCLike.re ⟪ψ, (Matrix.toEuclideanCLM (n := Fin n → Bool) (𝕜 := ℂ) M) ψ⟫ =
        RCLike.re (star ψ.ofLp ⬝ᵥ (M *ᵥ ψ.ofLp)) := by
    simp only [PiLp.inner_apply, Matrix.ofLp_toEuclideanCLM, RCLike.inner_apply, dotProduct,
      Pi.star_apply, starRingEnd_apply, map_sum, mul_comm]
  have hexpand : star ψ.ofLp ⬝ᵥ ((H - (E₀ : ℂ) • 1) *ᵥ ψ.ofLp) =
      star ψ.ofLp ⬝ᵥ (H *ᵥ ψ.ofLp) - (E₀ : ℂ) * (star ψ.ofLp ⬝ᵥ ψ.ofLp) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hnorm : (star ψ.ofLp ⬝ᵥ ψ.ofLp).re = ‖ψ‖ ^ 2 := by
    change RCLike.re (star ψ.ofLp ⬝ᵥ ψ.ofLp) = ‖ψ‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq]
    simp only [dotProduct, Pi.star_apply, map_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [← starRingEnd_apply, mul_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [hexpand, map_sub, RCLike.mul_re] at hnonneg
  change 0 ≤ (star ψ.ofLp ⬝ᵥ (H *ᵥ ψ.ofLp)).re -
      ((E₀ : ℂ).re * (star ψ.ofLp ⬝ᵥ ψ.ofLp).re - (E₀ : ℂ).im * (star ψ.ofLp ⬝ᵥ ψ.ofLp).im)
      at hnonneg
  rw [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hnorm] at hnonneg
  rw [energyExpectation, hinner_eq]
  change E₀ * ‖ψ‖ ^ 2 ≤ (star ψ.ofLp ⬝ᵥ (H *ᵥ ψ.ofLp)).re
  linarith

/-- For every quantum circuit `C : Circuit n` and initial basis state `x`, the output state
`C.run x` has energy expectation at least `qubitGroundEnergy hH`. -/
theorem qubitGroundEnergy_le_circuit_energyExpectation
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ} (hH : H.IsHermitian)
    (C : Circuit n) (x : Fin n → Bool) :
    qubitGroundEnergy hH ≤ energyExpectation H (C.run x) := by
  have h := qubitGroundEnergy_mul_norm_sq_le_energyExpectation hH (C.run x)
  rwa [Circuit.norm_run, one_pow, mul_one] at h

end CslibFrontier.Quantum
end
