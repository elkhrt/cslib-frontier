/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Basic
public import CslibFrontier.Foundations.Quantum.DensityMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Real.Sqrt

/-!
# Quantum Effect Distinguishability and Uniform Orthonormal Basis Ensembles

This module develops two general quantum-information tools on finite-dimensional complex Hilbert
spaces `EuclideanSpace ℂ ι`:

1. **Effect expectation bounds from pure-state overlap**: for any
   quantum effect matrix `0 ≤ E ≤ 1` (`Cslib.Quantum.IsQuantumEffect`) and unit vectors `ψ₁, ψ₂`,
   the real expectation values `⟨ψᵢ, E ψᵢ⟩` satisfy the quadratic tradeoff
   `‖⟪ψ₁, ψ₂⟫_ℂ‖ ^ 2 + (matrixExpect E ψ₁ - matrixExpect E ψ₂) ^ 2 ≤ 1`, and hence whenever
   `1 - d ≤ ‖⟪ψ₁, ψ₂⟫_ℂ‖ ^ 2`, we have `|matrixExpect E ψ₁ - matrixExpect E ψ₂| ≤ √d`.
2. **Indistinguishability of uniform orthonormal basis ensembles**: the uniform mixture of pure
   computational-basis states `|i⟩⟨i|` and the uniform mixture of any unitarily rotated basis
   `U |i⟩⟨i| Uᴴ` both equal the maximally mixed matrix `(|ι|)⁻¹ • 1`.

## Main definitions

* `Cslib.Quantum.matrixExpect`: the real expectation value `Re ⟪ψ, E ψ⟫_ℂ` of a matrix `E` in a
  state vector `ψ : EuclideanSpace ℂ ι`.
* `Cslib.Quantum.IsQuantumEffect`: predicate `0 ≤ E ≤ 1` (`E.PosSemidef` and
  `(1 - E).PosSemidef`) characterizing two-outcome POVM effect operators.
* `Cslib.Quantum.uniformBasisDensity`: the uniform ensemble average
  `(card ι)⁻¹ • ∑ i, |v i⟩⟨v i|` of pure-state density matrices over a finite index type `ι`.

## Main results

* `Cslib.Quantum.matrixExpect_nonneg`, `Cslib.Quantum.matrixExpect_le_norm_sq`,
  `Cslib.Quantum.matrixExpect_le_one`: range bounds `[0, 1]` for quantum effect expectations.
* `Cslib.Quantum.norm_inner_sq_add_sq_matrixExpect_sub_le_one`: quadratic overlap-versus-bias
  inequality for arbitrary quantum effects `0 ≤ E ≤ 1`.
* `Cslib.Quantum.abs_matrixExpect_sub_le_sqrt`: Fuchs–van de Graaf pure-state distinguishability
  bound `|matrixExpect E ψ₁ - matrixExpect E ψ₂| ≤ √d` from `1 - d ≤ ‖⟪ψ₁, ψ₂⟫_ℂ‖ ^ 2`.
* `Cslib.Quantum.uniformBasisDensity_ket`, `Cslib.Quantum.uniformBasisDensity_unitary_ket`:
  equality of the uniform computational-basis density matrix and any unitarily rotated uniform basis
  ensemble with `(|ι|)⁻¹ • 1`.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped MatrixOrder ComplexOrder

section EffectExpectation

variable {ι : Type*} [Fintype ι]

/-- The real expectation value `Re ⟪ψ, E ψ⟫_ℂ` of a complex matrix `E` in a vector
`ψ : EuclideanSpace ℂ ι`. -/
noncomputable def matrixExpect (E : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  RCLike.re (inner ℂ ψ (WithLp.toLp 2 (E *ᵥ ψ.ofLp)))

/-- A matrix `E` on `ℂ^ι` is a **quantum effect** (`0 ≤ E ≤ 1`) if both `E` and `1 - E` are
positive semidefinite. -/
structure IsQuantumEffect [DecidableEq ι] (E : Matrix ι ι ℂ) : Prop where
  /-- The effect operator `E` is positive semidefinite (`0 ≤ E`). -/
  posSemidef : E.PosSemidef
  /-- The complementary effect `1 - E` is positive semidefinite (`E ≤ 1`). -/
  sub_posSemidef : (1 - E).PosSemidef

/-- The expectation value of the zero matrix vanishes on every state vector. -/
@[simp]
theorem matrixExpect_zero (ψ : EuclideanSpace ℂ ι) :
    matrixExpect (0 : Matrix ι ι ℂ) ψ = 0 := by
  simp [matrixExpect]

/-- The expectation value of any matrix vanishes at the zero vector. -/
@[simp]
theorem matrixExpect_zero_right (E : Matrix ι ι ℂ) :
    matrixExpect E (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [matrixExpect]

/-- The expectation value of the identity matrix equals the squared Euclidean norm `‖ψ‖ ^ 2`. -/
@[simp]
theorem matrixExpect_one [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    matrixExpect (1 : Matrix ι ι ℂ) ψ = ‖ψ‖ ^ 2 := by
  have hid : (WithLp.toLp 2 ((1 : Matrix ι ι ℂ) *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι) = ψ := by
    ext i
    simp
  rw [matrixExpect, hid, inner_self_eq_norm_sq]

/-- The expectation value of a rank-one pure-state operator `|μ⟩⟨μ|` in `ψ` equals
`‖⟪μ, ψ⟫_ℂ‖ ^ 2`. -/
@[simp]
theorem matrixExpect_pureState (μ ψ : EuclideanSpace ℂ ι) :
    matrixExpect (pureState μ) ψ = ‖inner ℂ μ ψ‖ ^ 2 := by
  have hin : inner ℂ μ ψ = ∑ j : ι, star (μ.ofLp j) * ψ.ofLp j := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hconj : star (inner ℂ μ ψ) = ∑ i : ι, μ.ofLp i * star (ψ.ofLp i) := by
    rw [hin, star_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hprod : inner ℂ ψ (WithLp.toLp 2 (pureState μ *ᵥ ψ.ofLp)) =
      star (inner ℂ μ ψ) * inner ℂ μ ψ := by
    rw [hconj, hin]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, pureState_apply,
      Pi.star_apply, sum_mul, mul_sum]
    exact (sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring).trans sum_comm
  rw [matrixExpect, hprod, Complex.star_def, RCLike.conj_mul]
  norm_cast

/-- For any unit vector `μ`, the rank-one projector `|μ⟩⟨μ|` is a quantum effect
(`0 ≤ |μ⟩⟨μ| ≤ 1`). -/
theorem isQuantumEffect_pureState [DecidableEq ι] {μ : EuclideanSpace ℂ ι} (hμ : ‖μ‖ = 1) :
    IsQuantumEffect (pureState μ) where
  posSemidef := posSemidef_pureState μ
  sub_posSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨Matrix.isHermitian_one.sub (posSemidef_pureState μ).isHermitian, fun v => ?_⟩
    let x : EuclideanSpace ℂ ι := WithLp.toLp 2 v
    have hdot : star v ⬝ᵥ ((1 - pureState μ) *ᵥ v) =
        ((‖x‖ ^ 2 - ‖inner ℂ μ x‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : star v ⬝ᵥ v = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
        rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
        push_cast
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
      have h2 : star v ⬝ᵥ (pureState μ *ᵥ v) = ((‖inner ℂ μ x‖ ^ 2 : ℝ) : ℂ) := by
        have hin : inner ℂ μ x = ∑ j : ι, star (μ.ofLp j) * v j := by
          simp [x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
        have hconj : star (inner ℂ μ x) = ∑ i : ι, μ.ofLp i * star (v i) := by
          rw [hin, star_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [star_mul', star_star, mul_comm]
        have hmul : star v ⬝ᵥ (pureState μ *ᵥ v) = star (inner ℂ μ x) * inner ℂ μ x := by
          rw [hconj, hin, sum_mul]
          simp only [dotProduct, Matrix.mulVec, pureState_apply, Pi.star_apply, mul_sum]
          exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
        rw [hmul, Complex.star_def, RCLike.conj_mul]
        norm_cast
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h1, h2]
      push_cast
      ring
    rw [hdot, ← Complex.ofReal_zero, Complex.real_le_real]
    have hcs : ‖inner ℂ μ x‖ ≤ ‖x‖ := by
      simpa [hμ] using norm_inner_le_norm μ x
    exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hcs 2)

/-- Classical positive semidefinite matrix square root `CFC.sqrt E`. -/
private noncomputable def cfcSqrtMat (E : Matrix ι ι ℂ) : Matrix ι ι ℂ := by
  classical
  exact CFC.sqrt E

/-- For a positive semidefinite matrix `E`, the square-root action `cfcSqrtMat E *ᵥ ψ` has inner
product `⟪cfcSqrtMat E ψ, cfcSqrtMat E φ⟫ = ⟪ψ, E φ⟫`. -/
private theorem inner_cfcSqrtMat_mulVec {E : Matrix ι ι ℂ} (hE : E.PosSemidef)
    (ψ φ : EuclideanSpace ℂ ι) :
    inner ℂ (WithLp.toLp 2 (cfcSqrtMat E *ᵥ ψ.ofLp)) (WithLp.toLp 2 (cfcSqrtMat E *ᵥ φ.ofLp)) =
      inner ℂ ψ (WithLp.toLp 2 (E *ᵥ φ.ofLp)) := by
  classical
  let P := cfcSqrtMat E
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E)
  have hPherm : Pᴴ = P := hP.isHermitian.eq
  have hPsq : P * P = E := CFC.sqrt_mul_sqrt_self E hE.nonneg
  change inner ℂ (WithLp.toLp 2 (P *ᵥ ψ.ofLp)) (WithLp.toLp 2 (P *ᵥ φ.ofLp)) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change dotProduct (P *ᵥ φ.ofLp) (star (P *ᵥ ψ.ofLp)) = dotProduct (E *ᵥ φ.ofLp) (star ψ.ofLp)
  rw [dotProduct_comm, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPherm,
    hPsq, ← Matrix.dotProduct_mulVec, dotProduct_comm]

/-- For a positive semidefinite matrix `E`, `matrixExpect E ψ` equals the squared Euclidean norm of
`cfcSqrtMat E *ᵥ ψ`. -/
private theorem matrixExpect_eq_norm_cfcSqrtMat_sq {E : Matrix ι ι ℂ}
    (hE : E.PosSemidef) (ψ : EuclideanSpace ℂ ι) :
    matrixExpect E ψ = ‖(WithLp.toLp 2 (cfcSqrtMat E *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [matrixExpect, ← inner_cfcSqrtMat_mulVec hE ψ ψ, inner_self_eq_norm_sq]

/-- The expectation value of a positive semidefinite matrix is nonnegative. -/
theorem matrixExpect_nonneg {E : Matrix ι ι ℂ} (hE : E.PosSemidef) (ψ : EuclideanSpace ℂ ι) :
    0 ≤ matrixExpect E ψ := by
  rw [matrixExpect_eq_norm_cfcSqrtMat_sq hE ψ]
  positivity

/-- The expectations of `E` and `1 - E` sum to `‖ψ‖ ^ 2`. -/
theorem matrixExpect_add_sub [DecidableEq ι] (E : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    matrixExpect E ψ + matrixExpect (1 - E) ψ = ‖ψ‖ ^ 2 := by
  have hsum : WithLp.toLp 2 (E *ᵥ ψ.ofLp) + WithLp.toLp 2 ((1 - E) *ᵥ ψ.ofLp) = ψ := by
    ext i
    simp [Matrix.sub_mulVec]
  rw [matrixExpect, matrixExpect, ← map_add RCLike.re, ← inner_add_right, hsum,
    inner_self_eq_norm_sq]

/-- The expectation value of a quantum effect `0 ≤ E ≤ 1` is at most `‖ψ‖ ^ 2`. -/
theorem matrixExpect_le_norm_sq [DecidableEq ι] {E : Matrix ι ι ℂ} (hE : IsQuantumEffect E)
    (ψ : EuclideanSpace ℂ ι) : matrixExpect E ψ ≤ ‖ψ‖ ^ 2 := by
  linarith [matrixExpect_add_sub E ψ, matrixExpect_nonneg hE.sub_posSemidef ψ]

/-- On a unit vector `ψ`, the expectation value of a quantum effect `0 ≤ E ≤ 1` lies in `[0, 1]`. -/
theorem matrixExpect_le_one [DecidableEq ι] {E : Matrix ι ι ℂ} (hE : IsQuantumEffect E)
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) : matrixExpect E ψ ≤ 1 := by
  simpa [hψ] using matrixExpect_le_norm_sq hE ψ

/-- **Quadratic overlap-distinguishability inequality for quantum effects**: for any `0 ≤ E ≤ 1`
and unit vectors `ψ₁, ψ₂`, `‖⟪ψ₁, ψ₂⟫_ℂ‖ ^ 2 + (matrixExpect E ψ₁ - matrixExpect E ψ₂) ^ 2 ≤ 1`. -/
theorem norm_inner_sq_add_sq_matrixExpect_sub_le_one [DecidableEq ι] {E : Matrix ι ι ℂ}
    (hE : IsQuantumEffect E) {ψ₁ ψ₂ : EuclideanSpace ℂ ι} (hψ₁ : ‖ψ₁‖ = 1) (hψ₂ : ‖ψ₂‖ = 1) :
    ‖inner ℂ ψ₁ ψ₂‖ ^ 2 + (matrixExpect E ψ₁ - matrixExpect E ψ₂) ^ 2 ≤ 1 := by
  let u₁ : EuclideanSpace ℂ ι := WithLp.toLp 2 (cfcSqrtMat E *ᵥ ψ₁.ofLp)
  let u₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 (cfcSqrtMat E *ᵥ ψ₂.ofLp)
  let v₁ : EuclideanSpace ℂ ι := WithLp.toLp 2 (cfcSqrtMat (1 - E) *ᵥ ψ₁.ofLp)
  let v₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 (cfcSqrtMat (1 - E) *ᵥ ψ₂.ofLp)
  have hdecomp : inner ℂ ψ₁ ψ₂ = inner ℂ u₁ u₂ + inner ℂ v₁ v₂ := by
    rw [inner_cfcSqrtMat_mulVec hE.posSemidef, inner_cfcSqrtMat_mulVec hE.sub_posSemidef,
      ← inner_add_right]
    congr 1
    ext i
    simp [Matrix.sub_mulVec]
  have hcs : ‖inner ℂ ψ₁ ψ₂‖ ≤ ‖u₁‖ * ‖u₂‖ + ‖v₁‖ * ‖v₂‖ := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm u₁ u₂) (norm_inner_le_norm v₁ v₂))
  have hu₁ : ‖u₁‖ ^ 2 = matrixExpect E ψ₁ :=
    (matrixExpect_eq_norm_cfcSqrtMat_sq hE.posSemidef ψ₁).symm
  have hu₂ : ‖u₂‖ ^ 2 = matrixExpect E ψ₂ :=
    (matrixExpect_eq_norm_cfcSqrtMat_sq hE.posSemidef ψ₂).symm
  have hv₁ : ‖v₁‖ ^ 2 = 1 - matrixExpect E ψ₁ := by
    have h1 := matrixExpect_add_sub E ψ₁
    rw [hψ₁, one_pow] at h1
    linarith [matrixExpect_eq_norm_cfcSqrtMat_sq hE.sub_posSemidef ψ₁]
  have hv₂ : ‖v₂‖ ^ 2 = 1 - matrixExpect E ψ₂ := by
    have h2 := matrixExpect_add_sub E ψ₂
    rw [hψ₂, one_pow] at h2
    linarith [matrixExpect_eq_norm_cfcSqrtMat_sq hE.sub_posSemidef ψ₂]
  have hn₁ : ‖u₁‖ ^ 2 + ‖v₁‖ ^ 2 = 1 := by linarith
  have hn₂ : ‖u₂‖ ^ 2 + ‖v₂‖ ^ 2 = 1 := by linarith
  have hlagrange : (‖u₁‖ * ‖u₂‖ + ‖v₁‖ * ‖v₂‖) ^ 2 + (‖u₁‖ * ‖v₂‖ - ‖v₁‖ * ‖u₂‖) ^ 2 = 1 := by
    calc (‖u₁‖ * ‖u₂‖ + ‖v₁‖ * ‖v₂‖) ^ 2 + (‖u₁‖ * ‖v₂‖ - ‖v₁‖ * ‖u₂‖) ^ 2
        = (‖u₁‖ ^ 2 + ‖v₁‖ ^ 2) * (‖u₂‖ ^ 2 + ‖v₂‖ ^ 2) := by ring
      _ = 1 := by rw [hn₁, hn₂, one_mul]
  have hcross : (‖u₁‖ * ‖v₂‖ + ‖v₁‖ * ‖u₂‖) ^ 2 ≤ 1 := by
    calc (‖u₁‖ * ‖v₂‖ + ‖v₁‖ * ‖u₂‖) ^ 2
        ≤ (‖u₁‖ * ‖u₂‖ - ‖v₁‖ * ‖v₂‖) ^ 2 + (‖u₁‖ * ‖v₂‖ + ‖v₁‖ * ‖u₂‖) ^ 2 :=
          le_add_of_nonneg_left (sq_nonneg _)
      _ = (‖u₁‖ ^ 2 + ‖v₁‖ ^ 2) * (‖u₂‖ ^ 2 + ‖v₂‖ ^ 2) := by ring
      _ = 1 := by rw [hn₁, hn₂, one_mul]
  have hdiff : matrixExpect E ψ₁ - matrixExpect E ψ₂ =
      (‖u₁‖ * ‖v₂‖ - ‖v₁‖ * ‖u₂‖) * (‖u₁‖ * ‖v₂‖ + ‖v₁‖ * ‖u₂‖) := by
    calc matrixExpect E ψ₁ - matrixExpect E ψ₂
        = ‖u₁‖ ^ 2 * ‖v₂‖ ^ 2 - ‖v₁‖ ^ 2 * ‖u₂‖ ^ 2 := by
            rw [hu₁, hu₂, hv₁, hv₂]; ring
      _ = (‖u₁‖ * ‖v₂‖ - ‖v₁‖ * ‖u₂‖) * (‖u₁‖ * ‖v₂‖ + ‖v₁‖ * ‖u₂‖) := by ring
  have hsq₁ : ‖inner ℂ ψ₁ ψ₂‖ ^ 2 ≤ (‖u₁‖ * ‖u₂‖ + ‖v₁‖ * ‖v₂‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcs 2
  have hsq₂ : (matrixExpect E ψ₁ - matrixExpect E ψ₂) ^ 2 ≤ (‖u₁‖ * ‖v₂‖ - ‖v₁‖ * ‖u₂‖) ^ 2 := by
    rw [hdiff, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hcross
  exact (add_le_add hsq₁ hsq₂).trans_eq hlagrange

/-- **Fuchs–van de Graaf effect distinguishability bound**: if `0 ≤ E ≤ 1` is a quantum effect and
`ψ₁, ψ₂` are unit states satisfying `1 - d ≤ ‖⟪ψ₁, ψ₂⟫_ℂ‖ ^ 2`, then
`|matrixExpect E ψ₁ - matrixExpect E ψ₂| ≤ √d`. -/
theorem abs_matrixExpect_sub_le_sqrt [DecidableEq ι] {E : Matrix ι ι ℂ} (hE : IsQuantumEffect E)
    {ψ₁ ψ₂ : EuclideanSpace ℂ ι} (hψ₁ : ‖ψ₁‖ = 1) (hψ₂ : ‖ψ₂‖ = 1) {d : ℝ}
    (hd : 1 - d ≤ ‖inner ℂ ψ₁ ψ₂‖ ^ 2) :
    |matrixExpect E ψ₁ - matrixExpect E ψ₂| ≤ √d := by
  have hquad := norm_inner_sq_add_sq_matrixExpect_sub_le_one hE hψ₁ hψ₂
  have hsq : (matrixExpect E ψ₁ - matrixExpect E ψ₂) ^ 2 ≤ d := by linarith
  exact Real.abs_le_sqrt hsq

end EffectExpectation

section UniformBasisEnsemble

variable {ι : Type*} [Fintype ι]

/-- The uniform ensemble density matrix `(card ι)⁻¹ • ∑ i, pureState (v i)` of a family of state
vectors `v : ι → EuclideanSpace ℂ ι`. -/
noncomputable def uniformBasisDensity (v : ι → EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  ((Fintype.card ι : ℂ)⁻¹) • ∑ i : ι, pureState (v i)

/-- On a finite basis `ι`, the uniform mixture of computational-basis states `|i⟩⟨i|` equals the
maximally mixed state `(card ι)⁻¹ • 1`. -/
theorem uniformBasisDensity_ket [DecidableEq ι] :
    uniformBasisDensity (ket (ι := ι)) = ((Fintype.card ι : ℂ)⁻¹) • (1 : Matrix ι ι ℂ) := by
  unfold uniformBasisDensity
  congr 1
  ext j k
  simp only [Matrix.sum_apply, pureState_apply, ket_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp)]
    simp
  · rw [ite_eq_right hjk]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hij : j = i
    · subst hij
      simp [Ne.symm hjk]
    · simp [hij]

/-- For any unitary matrix `U ∈ unitaryGroup ι ℂ`, the uniform mixture of the rotated basis states
`unitaryEquiv U (ket i)` has the exact same density matrix as the uniform mixture of computational
basis states `ket i`. -/
theorem uniformBasisDensity_unitary_ket [DecidableEq ι] (U : unitaryGroup ι ℂ) :
    uniformBasisDensity (fun i : ι => unitaryEquiv U (ket i)) =
      uniformBasisDensity (ket (ι := ι)) := by
  rw [uniformBasisDensity_ket]
  unfold uniformBasisDensity
  congr 1
  have hUU : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp U.2
  ext j k
  simp only [Matrix.sum_apply, pureState_apply, unitaryEquiv_apply, Matrix.mulVec, dotProduct,
    ket_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hrow : ∑ i : ι, (U : Matrix ι ι ℂ) j i * star ((U : Matrix ι ι ℂ) k i) =
      ((U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ) j k := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hrow, hUU]

end UniformBasisEnsemble

end Cslib.Quantum
