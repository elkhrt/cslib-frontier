module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid

/-!
# Quantum imaginary time evolution for finite-dimensional Hermitian Hamiltonians

This module formalizes continuous-time imaginary time evolution (ITE)
`ψ(t) = ‖exp(-t H) ψ₀‖⁻¹ exp(-t H) ψ₀` for a finite-dimensional Hermitian matrix `H` on
`EuclideanSpace ℂ ι`.

## Main definitions

* `iteUnnorm`: unnormalized imaginary time evolution `exp (-t H) ψ₀`.
* `iteState`: normalized imaginary time evolution `‖exp (-t H) ψ₀‖⁻¹ exp (-t H) ψ₀`.
* `sortedEigenvalues`, `sortedEigenbasis`: eigenvalues of `H` ordered increasingly (`λ₀ ≤ λ₁ ≤... ≤
  λ_N`) and the corresponding orthonormal eigenbasis.
* `groundEnergy`, `groundMultiplicity`, `spectralGap`, `groundProjection`: ground-state energy `λ₀`,
  multiplicity `μ`, energy gap `Δ = λ_μ - λ₀`, and orthogonal projection onto the ground eigenspace.
* `iteCoeff`, `iteEnergy`, `iteFidelity`: eigenbasis amplitudes `α_j(t)`, expectation energy `E(t) =
  Re ⟨ψ(t), H ψ(t)⟩`, and ground-state fidelity `f(t) = ∑_{j < μ} |α_j(t)|²`.
* `sphereTangentProj`: orthogonal projection onto the tangent space of the unit sphere at `ψ`.

## Main results

* `iteCoeff_eq`, `iteCoeff_ne_zero_iff`: closed-form eigenbasis expansion and preservation of
  nonzero amplitudes.
* `tendsto_iteCoeff_ground`, `tendsto_iteCoeff_excited`, `tendsto_iteState_ground`,
  `tendsto_iteState_active`: exact convergence of ITE to the normalized orthogonal projection onto
  the lowest-energy active eigenspace.
* `hasDerivAt_iteState`, `hasDerivAt_iteEnergy`, `iteEnergy_antitone`,
  `deriv_iteEnergy_eq_zero_iff`: spherical gradient-flow ODE `ψ'(t) = -pr_{T_{ψ(t)} S}(H ψ(t))`,
  energy dissipation `E'(t) = -2 ‖pr_{T_{ψ(t)} S}(H ψ(t))‖² ≤ 0`, and eigenstate characterization of
  critical points.
* `hasDerivAt_norm_sq_iteCoeff`: exact amplitude ODE `d/dt |α_j(t)|² = 2 (E(t) - λ_j) |α_j(t)|²`.
* `iteCoeff_norm_sq_le_of_excited`, `iteFidelity_ge`, `iteFidelity_ge_of_time_ge`,
  `iteState_dist_sq_le_sharp`, `iteState_dist_sq_le_cube`: exponential suppression, fidelity lower
  bound, linear-in-`1/Δ` threshold time, and state-distance convergence rate.
* `toSphere_orth_groundSpace_eq_zero`: unit states orthogonal to the ground eigenspace form a null
  set for spherical surface measure.
-/

public section

namespace CslibFrontier.Foundations.Quantum

open Matrix Finset Filter Topology Complex
open scoped Matrix.Norms.L2Operator InnerProductSpace RealInnerProductSpace Pointwise

private lemma real_inner_eq_re_complex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] (x y : E) :
    @inner ℝ _ _ x y = RCLike.re (@inner ℂ _ _ x y) := by
  have h1 := norm_add_sq_real x y
  have h2 := norm_add_sq (𝕜 := ℂ) x y
  linarith

section SpectralSetup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eigenvalues of a Hermitian matrix `H` ordered increasingly (`λ₀ ≤ λ₁ ≤ ... ≤ λ_N`). -/
noncomputable def sortedEigenvalues {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (j : Fin (Fintype.card ι)) : ℝ :=
  hH.eigenvalues₀ j.rev

/-- Increasing monotonicity of `sortedEigenvalues`. -/
@[gcongr]
theorem sortedEigenvalues_monotone {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    Monotone (sortedEigenvalues hH) := by
  intro i j hij
  exact hH.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

/-- Orthonormal eigenbasis of a Hermitian matrix `H` ordered by increasing eigenvalues. -/
noncomputable def sortedEigenbasis {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
    finrank_euclideanSpace).reindex Fin.revPerm

/-- Action of `H` on each vector of `sortedEigenbasis`. -/
theorem mulVec_sortedEigenbasis {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (j : Fin (Fintype.card ι)) :
    H *ᵥ (sortedEigenbasis hH j).ofLp =
      (sortedEigenvalues hH j : ℂ) • (sortedEigenbasis hH j).ofLp := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have h := hsym.apply_eigenvectorBasis finrank_euclideanSpace j.rev
  have hval : (Matrix.toEuclideanLin H) (sortedEigenbasis hH j) =
      (sortedEigenvalues hH j : ℂ) • sortedEigenbasis hH j := by
    rw [sortedEigenbasis, sortedEigenvalues, OrthonormalBasis.reindex_apply,
      Fin.revPerm_symm, Fin.revPerm_apply]
    exact h
  exact congrArg WithLp.ofLp hval

/-- Action of the matrix exponential `exp (c • H)` on each vector of `sortedEigenbasis`. -/
theorem exp_smul_mulVec_sortedEigenbasis {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (c : ℂ)
    (j : Fin (Fintype.card ι)) :
    NormedSpace.exp (c • H) *ᵥ (sortedEigenbasis hH j).ofLp =
      Complex.exp (c * (sortedEigenvalues hH j : ℂ)) • (sortedEigenbasis hH j).ofLp := by
  let v := sortedEigenbasis hH j
  have hv : H *ᵥ v.ofLp = (sortedEigenvalues hH j : ℂ) • v.ofLp :=
    mulVec_sortedEigenbasis hH j
  have hpow : ∀ k : ℕ, ((c • H) ^ k) *ᵥ v.ofLp =
      (c * (sortedEigenvalues hH j : ℂ)) ^ k • v.ofLp := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, Matrix.smul_mulVec, hv,
        smul_smul, smul_smul, pow_succ']
      ring_nf
  ext i
  have hentry : ∀ a b : ι,
      HasSum (fun k : ℕ ↦ (k.factorial⁻¹ : ℂ) * ((c • H) ^ k) a b)
        (NormedSpace.exp (c • H) a b) := by
    intro a b
    have he := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • H)
    have hcont : Continuous (fun M : Matrix ι ι ℂ ↦ M a b) := continuous_apply_apply a b
    have hmap := he.map (Matrix.entryLinearMap ℂ ℂ a b).toAddMonoidHom hcont
    exact hmap.congr_fun fun _ ↦ rfl
  have hsum1 :
      HasSum (fun k : ℕ ↦ (k.factorial⁻¹ : ℂ) * (((c • H) ^ k) *ᵥ v.ofLp) i)
        ((NormedSpace.exp (c • H) *ᵥ v.ofLp) i) := by
    have hmul : ∀ b : ι,
        HasSum (fun k : ℕ ↦ (k.factorial⁻¹ : ℂ) * ((c • H) ^ k) i b * v.ofLp b)
          (NormedSpace.exp (c • H) i b * v.ofLp b) :=
      fun b ↦ (hentry i b).mul_right (v.ofLp b)
    have hfin := hasSum_sum (s := Finset.univ) fun b _ ↦ hmul b
    exact hfin.congr_fun fun k ↦ by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hsum2 :
      HasSum (fun k : ℕ ↦ (k.factorial⁻¹ : ℂ) * (((c • H) ^ k) *ᵥ v.ofLp) i)
        ((Complex.exp (c * (sortedEigenvalues hH j : ℂ)) • v.ofLp) i) := by
    have he := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
      (c * (sortedEigenvalues hH j : ℂ))).mul_right (v.ofLp i)
    rw [← Complex.exp_eq_exp_ℂ] at he
    exact he.congr_fun fun k ↦ by
      simp only [hpow k, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact hsum1.unique hsum2

/-- Action of `exp (c • H)` on any state vector in the `sortedEigenbasis` expansion. -/
theorem exp_smul_mulVec_repr {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (c : ℂ)
    (ψ : EuclideanSpace ℂ ι) (j : Fin (Fintype.card ι)) :
    @inner ℂ _ _ (sortedEigenbasis hH j)
      (WithLp.toLp 2 (NormedSpace.exp (c • H) *ᵥ ψ.ofLp)) =
      Complex.exp (c * (sortedEigenvalues hH j : ℂ)) *
        @inner ℂ _ _ (sortedEigenbasis hH j) ψ := by
  have hrep : ψ = ∑ k, (@inner ℂ _ _ (sortedEigenbasis hH k) ψ) • sortedEigenbasis hH k :=
    ((sortedEigenbasis hH).sum_repr' ψ).symm
  conv_lhs => rw [hrep]
  have hlin : (WithLp.toLp 2 (NormedSpace.exp (c • H) *ᵥ
      (∑ k, (@inner ℂ _ _ (sortedEigenbasis hH k) ψ) • sortedEigenbasis hH k).ofLp)) =
      ∑ k, (@inner ℂ _ _ (sortedEigenbasis hH k) ψ) •
        (Complex.exp (c * (sortedEigenvalues hH k : ℂ)) • sortedEigenbasis hH k) := by
    ext i
    simp [Matrix.mulVec_sum, Matrix.mulVec_smul, exp_smul_mulVec_sortedEigenbasis]
  rw [hlin, inner_sum, Finset.sum_eq_single j]
  · simp [inner_smul_right, (sortedEigenbasis hH).orthonormal.1 j]
    ring
  · intro k _ hkj
    simp [inner_smul_right, (sortedEigenbasis hH).orthonormal.2 hkj.symm]
  · simp

/-- The **ground-state energy** `λ₀` of a Hermitian matrix `H` on a nonempty index type `ι`. -/
noncomputable def groundEnergy [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : ℝ :=
  sortedEigenvalues hH ⟨0, Fintype.card_pos⟩

/-- Every sorted eigenvalue is at least the ground energy. -/
theorem groundEnergy_le [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (j : Fin (Fintype.card ι)) :
    groundEnergy hH ≤ sortedEigenvalues hH j :=
  sortedEigenvalues_monotone hH (Fin.zero_le j)

/-- The **ground-state multiplicity** `μ = #{j | λ_j = λ₀}`. -/
noncomputable def groundMultiplicity [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : ℕ :=
  (Finset.univ.filter fun j : Fin (Fintype.card ι) ↦
    sortedEigenvalues hH j = groundEnergy hH).card

/-- Ground-state multiplicity is always at least `1`. -/
theorem groundMultiplicity_pos [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    0 < groundMultiplicity hH := by
  rw [groundMultiplicity]
  exact Finset.card_pos.mpr ⟨⟨0, Fintype.card_pos⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- Ground-state multiplicity is at most the Hilbert-space dimension. -/
theorem groundMultiplicity_le_card [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    groundMultiplicity hH ≤ Fintype.card ι := by
  rw [groundMultiplicity]
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (Fintype.card ι)))
    (fun j ↦ sortedEigenvalues hH j = groundEnergy hH)

/-- Characterization of ground-eigenspace indices: `λ_j = λ₀` iff `j.val < μ`. -/
theorem sortedEigenvalues_eq_groundEnergy_iff [Nonempty ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (j : Fin (Fintype.card ι)) :
    sortedEigenvalues hH j = groundEnergy hH ↔ j.val < groundMultiplicity hH := by
  let S : Finset (Fin (Fintype.card ι)) :=
    Finset.univ.filter fun k ↦ sortedEigenvalues hH k = groundEnergy hH
  have hS : ∀ a b : Fin (Fintype.card ι), a ∈ S → b ≤ a → b ∈ S := by
    intro a b ha hba
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      le_antisymm ((sortedEigenvalues_monotone hH hba).trans (Finset.mem_filter.mp ha).2.le)
        (groundEnergy_le hH b)⟩
  have hcard_range : ∀ m ≤ Fintype.card ι,
      (Finset.univ.filter fun k : Fin (Fintype.card ι) ↦ k.val < m).card = m := fun m hm ↦ by
    have hbij : (Finset.univ.filter fun k : Fin (Fintype.card ι) ↦ k.val < m).card =
        (Finset.range m).card :=
      Finset.card_bij (fun k _ ↦ k.val)
        (fun k hk ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
        (fun _ _ _ _ h ↦ Fin.ext h)
        (fun r hr ↦ ⟨⟨r, lt_of_lt_of_le (Finset.mem_range.mp hr) hm⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hr⟩, rfl⟩)
    simpa using hbij
  have hEq : S = Finset.univ.filter fun k : Fin (Fintype.card ι) ↦ k.val < S.card := by
    by_contra hne
    have hcard_le : S.card ≤ Fintype.card ι := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (Fintype.card ι)))
        (fun k ↦ sortedEigenvalues hH k = groundEnergy hH)
    obtain ⟨a, haS, hanot⟩ := Finset.not_subset.mp fun hsub ↦
      hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hcard_range S.card hcard_le)))
    have hge : S.card ≤ a.val := Nat.not_lt.mp (by simpa using hanot)
    have hle := Finset.card_le_card (show
        (Finset.univ.filter fun k : Fin (Fintype.card ι) ↦ k.val < a.val + 1) ⊆ S from
      fun b hb ↦ hS a b haS (Fin.le_def.mpr (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hb).2)))
    rw [hcard_range (a.val + 1) a.isLt] at hle
    omega
  rw [groundMultiplicity]
  have hmem : j ∈ S ↔ j.val < S.card := by
    conv_lhs => rw [hEq]
    simp
  simpa [S] using hmem

/-- The **spectral (energy) gap** `Δ = λ_μ - λ₀` when `μ < card ι` (and `0` if `H` is a scalar
multiple of the identity). -/
@[expose] noncomputable def spectralGap [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : ℝ :=
  if h : groundMultiplicity hH < Fintype.card ι then
    sortedEigenvalues hH ⟨groundMultiplicity hH, h⟩ - groundEnergy hH
  else 0

/-- Explicit formula `Δ = λ_μ - λ₀` when `μ < card ι`. -/
theorem spectralGap_eq_sub [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hμ : groundMultiplicity hH < Fintype.card ι) :
    spectralGap hH = sortedEigenvalues hH ⟨groundMultiplicity hH, hμ⟩ - groundEnergy hH := by
  rw [spectralGap, dite_eq_left hμ]

/-- The spectral gap is strictly positive whenever `μ < card ι`. -/
theorem spectralGap_pos [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hμ : groundMultiplicity hH < Fintype.card ι) :
    0 < spectralGap hH := by
  rw [spectralGap_eq_sub hH hμ]
  have hne : sortedEigenvalues hH ⟨groundMultiplicity hH, hμ⟩ ≠ groundEnergy hH := fun heq ↦
    lt_irrefl _ ((sortedEigenvalues_eq_groundEnergy_iff hH _).mp heq)
  exact sub_pos.mpr (lt_of_le_of_ne (groundEnergy_le hH _) hne.symm)

/-- Every excited eigenvalue `j ≥ μ` exceeds the ground energy by at least `spectralGap hH`. -/
theorem spectralGap_le_sub_of_ge [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {j : Fin (Fintype.card ι)} (hj : groundMultiplicity hH ≤ j.val) :
    spectralGap hH ≤ sortedEigenvalues hH j - groundEnergy hH := by
  have hμ : groundMultiplicity hH < Fintype.card ι := lt_of_le_of_lt hj j.isLt
  rw [spectralGap_eq_sub hH hμ]
  linarith [sortedEigenvalues_monotone hH (show (⟨groundMultiplicity hH, hμ⟩ :
    Fin (Fintype.card ι)) ≤ j from Fin.le_def.mpr hj)]

/-- Orthogonal projection onto the ground eigenspace of `H`. -/
@[expose] noncomputable def groundProjection [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
    (@inner ℂ _ _ (sortedEigenbasis hH j) ψ) • sortedEigenbasis hH j

/-- `groundProjection` is additive. -/
theorem groundProjection_add [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (x y : EuclideanSpace ℂ ι) :
    groundProjection hH (x + y) = groundProjection hH x + groundProjection hH y := by
  simp only [groundProjection, inner_add_right, add_smul, Finset.sum_add_distrib]

/-- `groundProjection` commutes with complex scalar multiplication. -/
theorem groundProjection_smul [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (c : ℂ) (x : EuclideanSpace ℂ ι) :
    groundProjection hH (c • x) = c • groundProjection hH x := by
  simp only [groundProjection, inner_smul_right, Finset.smul_sum, smul_smul]

/-- Eigenbasis coordinates of `groundProjection hH ψ`. -/
theorem inner_sortedEigenbasis_groundProjection [Nonempty ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (ψ : EuclideanSpace ℂ ι) (j : Fin (Fintype.card ι)) :
    @inner ℂ _ _ (sortedEigenbasis hH j) (groundProjection hH ψ) =
      if j.val < groundMultiplicity hH then @inner ℂ _ _ (sortedEigenbasis hH j) ψ else 0 := by
  rw [groundProjection, inner_sum]
  by_cases hj : j.val < groundMultiplicity hH
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · simp [inner_smul_right, (sortedEigenbasis hH).orthonormal.1 j]
    · intro k _ hk; simp [inner_smul_right, (sortedEigenbasis hH).orthonormal.2 hk.symm]
    · intro hnot; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hnot
  · rw [ite_eq_right hj]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hkj : j ≠ k := fun h ↦ hj (h ▸ (Finset.mem_filter.mp hk).2)
    simp [inner_smul_right, (sortedEigenbasis hH).orthonormal.2 hkj]

/-- Squared norm of the ground-eigenspace projection equals the sum of ground amplitudes squared. -/
theorem norm_sq_groundProjection [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℂ ι) :
    ‖groundProjection hH ψ‖ ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
        ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ‖ ^ 2 := by
  rw [groundProjection, ← @inner_self_eq_norm_sq ℂ,
    Orthonormal.inner_sum (sortedEigenbasis hH).orthonormal, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [RCLike.conj_mul]
  norm_cast

end SpectralSetup

section ImaginaryTimeEvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unnormalized imaginary time evolution `exp (-t H) ψ₀`. -/
@[expose] noncomputable def iteUnnorm (H : Matrix ι ι ℂ) (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (NormedSpace.exp ((-(t : ℂ)) • H) *ᵥ ψ₀.ofLp)

/-- Componentwise evaluation of unnormalized ITE. -/
theorem iteUnnorm_apply (H : Matrix ι ι ℂ) (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) (x : ι) :
    (iteUnnorm H t ψ₀).ofLp x = (NormedSpace.exp ((-(t : ℂ)) • H) *ᵥ ψ₀.ofLp) x :=
  rfl

/-- At `t = 0`, unnormalized ITE is the identity. -/
@[simp]
theorem iteUnnorm_zero (H : Matrix ι ι ℂ) (ψ₀ : EuclideanSpace ℂ ι) :
    iteUnnorm H 0 ψ₀ = ψ₀ := by
  ext i; simp [iteUnnorm]

/-- **Normalized quantum imaginary time evolution**
`ψ(t) = ‖exp (-t H) ψ₀‖⁻¹ exp (-t H) ψ₀`. -/
@[expose] noncomputable def iteState (H : Matrix ι ι ℂ) (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  ‖iteUnnorm H t ψ₀‖⁻¹ • iteUnnorm H t ψ₀

/-- Componentwise evaluation of normalized ITE. -/
theorem iteState_apply (H : Matrix ι ι ℂ) (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) (x : ι) :
    (iteState H t ψ₀).ofLp x =
      (‖iteUnnorm H t ψ₀‖⁻¹ : ℂ) * (iteUnnorm H t ψ₀).ofLp x := by
  simp [iteState, RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- At `t = 0`, normalized ITE of a unit state `ψ₀` equals `ψ₀`. -/
@[simp]
theorem iteState_zero (H : Matrix ι ι ℂ) {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) :
    iteState H 0 ψ₀ = ψ₀ := by
  simp [iteState, hψ₀]

/-- Unnormalized ITE is nonzero whenever `ψ₀ ≠ 0`. -/
theorem iteUnnorm_ne_zero (H : Matrix ι ι ℂ) (t : ℝ) {ψ₀ : EuclideanSpace ℂ ι}
    (hψ₀ : ψ₀ ≠ 0) :
    iteUnnorm H t ψ₀ ≠ 0 := by
  intro h
  have hmul : NormedSpace.exp ((-(t : ℂ)) • H) *ᵥ ψ₀.ofLp = 0 := congrArg WithLp.ofLp h
  have hback : ψ₀.ofLp = 0 := by
    have hinv := congrArg (fun v ↦ NormedSpace.exp ((t : ℂ) • H) *ᵥ v) hmul
    have hcomm : Commute ((t : ℂ) • H) ((-(t : ℂ)) • H) :=
      ((Commute.refl H).smul_left _).smul_right _
    rw [Matrix.mulVec_mulVec, ← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul,
      add_neg_cancel, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hinv
    exact hinv
  exact hψ₀ (WithLp.ofLp_injective 2 hback)

/-- Normalized ITE always has unit `ℓ²`-norm when `ψ₀ ≠ 0`. -/
@[simp]
theorem norm_iteState (H : Matrix ι ι ℂ) (t : ℝ) {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    ‖iteState H t ψ₀‖ = 1 := by
  rw [iteState, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (iteUnnorm_ne_zero H t hψ₀))

/-- Normalized ITE is invariant under positive real rescaling of the initial state. -/
theorem iteState_smul_pos (H : Matrix ι ι ℂ) (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι)
    {r : ℝ} (hr : 0 < r) :
    iteState H t (r • ψ₀) = iteState H t ψ₀ := by
  have hlin : iteUnnorm H t (r • ψ₀) = r • iteUnnorm H t ψ₀ := by
    ext x
    simp only [iteUnnorm, WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), Matrix.mulVec_smul]
  rw [iteState, iteState, hlin, norm_smul, Real.norm_of_nonneg hr.le, mul_inv, smul_smul,
    mul_right_comm, inv_mul_cancel₀ hr.ne', one_mul]

/-- Composing normalized ITE drops the intermediate normalization factor. -/
theorem iteState_iteState (H₁ H₂ : Matrix ι ι ℂ) (t₁ t₂ : ℝ) {ψ₀ : EuclideanSpace ℂ ι}
    (hψ₀ : ψ₀ ≠ 0) :
    iteState H₂ t₂ (iteState H₁ t₁ ψ₀) = iteState H₂ t₂ (iteUnnorm H₁ t₁ ψ₀) :=
  iteState_smul_pos H₂ t₂ (iteUnnorm H₁ t₁ ψ₀)
    (inv_pos.mpr (norm_pos_iff.mpr (iteUnnorm_ne_zero H₁ t₁ hψ₀)))

/-- Eigenbasis amplitude `α_j(t) = ⟨ψ_j, ψ(t)⟩` of the imaginary time evolution. -/
noncomputable def iteCoeff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    (ψ₀ : EuclideanSpace ℂ ι) (j : Fin (Fintype.card ι)) : ℂ :=
  @inner ℂ _ _ (sortedEigenbasis hH j) (iteState H t ψ₀)

/-- Initial eigenbasis amplitude `α_j(0) = ⟨ψ_j, ψ₀⟩` for a unit vector `ψ₀`. -/
@[simp]
theorem iteCoeff_zero {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {ψ₀ : EuclideanSpace ℂ ι}
    (hψ₀ : ‖ψ₀‖ = 1) (j : Fin (Fintype.card ι)) :
    iteCoeff hH 0 ψ₀ j = @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀ := by
  simp [iteCoeff, hψ₀]

/-- Parseval identity for eigenbasis amplitudes: `∑_k |α_k(t)|² = 1` whenever `ψ₀ ≠ 0`. -/
theorem sum_norm_sq_iteCoeff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    ∑ k : Fin (Fintype.card ι), ‖iteCoeff hH t ψ₀ k‖ ^ 2 = 1 := by
  rw [show (∑ k, ‖iteCoeff hH t ψ₀ k‖ ^ 2) = ‖iteState H t ψ₀‖ ^ 2 from
    (sortedEigenbasis hH).sum_sq_norm_inner_right (iteState H t ψ₀), norm_iteState H t hψ₀, one_pow]

/-- Squared norm of unnormalized ITE in the eigenbasis. -/
theorem norm_sq_iteUnnorm {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    (ψ₀ : EuclideanSpace ℂ ι) :
    ‖iteUnnorm H t ψ₀‖ ^ 2 =
      ∑ k : Fin (Fintype.card ι),
        ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
          Real.exp (-2 * t * sortedEigenvalues hH k) := by
  rw [← (sortedEigenbasis hH).sum_sq_norm_inner_right (iteUnnorm H t ψ₀)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [iteUnnorm, exp_smul_mulVec_repr hH (-(t : ℂ)) ψ₀ k, norm_mul, mul_pow, mul_comm]
  congr 1
  have hre : (-(t : ℂ) * (sortedEigenvalues hH k : ℂ)).re = -(t * sortedEigenvalues hH k) := by
    simp
  rw [Complex.norm_exp, hre, ← Real.exp_nat_mul]
  congr 1; ring

private lemma norm_sq_iteUnnorm_factor {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    (ψ₀ : EuclideanSpace ℂ ι) (lamRef : ℝ) :
    ‖iteUnnorm H t ψ₀‖ ^ 2 =
      Real.exp (-2 * t * lamRef) *
        ∑ k : Fin (Fintype.card ι),
          ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
            Real.exp (-2 * t * (sortedEigenvalues hH k - lamRef)) := by
  rw [norm_sq_iteUnnorm hH t ψ₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_left_comm, ← Real.exp_add]
  congr 2; ring

private noncomputable def excitedWeight [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card ι) ↦ ¬ k.val < groundMultiplicity hH),
    ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
      Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH))

private lemma excitedWeight_nonneg [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    (ψ₀ : EuclideanSpace ℂ ι) : 0 ≤ excitedWeight hH t ψ₀ :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

private lemma norm_sq_iteUnnorm_ground_split [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) :
    Real.exp (2 * t * groundEnergy hH) * ‖iteUnnorm H t ψ₀‖ ^ 2 =
      ‖groundProjection hH ψ₀‖ ^ 2 + excitedWeight hH t ψ₀ := by
  rw [norm_sq_iteUnnorm hH t ψ₀, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin (Fintype.card ι) ↦ k.val < groundMultiplicity hH),
    norm_sq_groundProjection, excitedWeight]
  congr 1
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have heig := (sortedEigenvalues_eq_groundEnergy_iff hH k).mpr (Finset.mem_filter.mp hk).2
    rw [heig, mul_left_comm, ← Real.exp_add]
    rw [show 2 * t * groundEnergy hH + -2 * t * groundEnergy hH = 0 by ring, Real.exp_zero,
      mul_one]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private lemma excited_weight_le_mul_exp [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) :
    excitedWeight hH t ψ₀ ≤
      (1 - ‖groundProjection hH ψ₀‖ ^ 2) * Real.exp (-2 * t * spectralGap hH) := by
  have h1a : 1 - ‖groundProjection hH ψ₀‖ ^ 2 = ∑ k ∈ Finset.univ.filter
      (fun k : Fin (Fintype.card ι) ↦ ¬ k.val < groundMultiplicity hH),
      ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 := by
    have hsum := (sortedEigenbasis hH).sum_sq_norm_inner_right ψ₀
    rw [hψ₀, one_pow, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin (Fintype.card ι) ↦ k.val < groundMultiplicity hH),
      ← norm_sq_groundProjection] at hsum
    linarith
  rw [excitedWeight, h1a, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (sq_nonneg _)
  have := spectralGap_le_sub_of_ge hH (Nat.not_lt.mp (Finset.mem_filter.mp hk).2)
  nlinarith

private lemma norm_sq_iteCoeff_eq [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) (j : Fin (Fintype.card ι)) :
    ‖iteCoeff hH t ψ₀ j‖ ^ 2 =
      ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 *
        Real.exp (-2 * t * (sortedEigenvalues hH j - groundEnergy hH)) /
        (Real.exp (2 * t * groundEnergy hH) * ‖iteUnnorm H t ψ₀‖ ^ 2) := by
  rw [iteCoeff, iteState, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, norm_mul,
    mul_pow, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_pow,
    iteUnnorm, exp_smul_mulVec_repr hH (-(t : ℂ)) ψ₀ j, norm_mul, mul_pow]
  have hre : (-(t : ℂ) * (sortedEigenvalues hH j : ℂ)).re = -(t * sortedEigenvalues hH j) := by
    simp
  rw [Complex.norm_exp, hre, ← Real.exp_nat_mul]
  have hexp_ne : Real.exp (2 * t * groundEnergy hH) ≠ 0 := (Real.exp_pos _).ne'
  have hnorm_ne : ‖iteUnnorm H t ψ₀‖ ^ 2 ≠ 0 :=
    (sq_pos_of_pos (norm_pos_iff.mpr (iteUnnorm_ne_zero H t hψ₀))).ne'
  change (‖iteUnnorm H t ψ₀‖ ^ 2)⁻¹ * _ =
    _ / (Real.exp (2 * t * groundEnergy hH) * ‖iteUnnorm H t ψ₀‖ ^ 2)
  field_simp [hexp_ne, hnorm_ne]
  congr 1
  rw [mul_comm (Real.exp _) (‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2), mul_assoc,
    ← Real.exp_add]
  congr 2; push_cast; ring

/-- **Closed-form eigenbasis amplitude formula**:
`α_j(t) = α_j(0) * (∑_k |α_k(0)|² exp (-2 t (λ_k - λ_j)))^{-1/2}`. -/
theorem iteCoeff_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) (j : Fin (Fintype.card ι)) :
    iteCoeff hH t ψ₀ j =
      (Real.sqrt (∑ k : Fin (Fintype.card ι),
          ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
            Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j))))⁻¹ •
        @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀ := by
  have hpos : 0 < ‖iteUnnorm H t ψ₀‖ := norm_pos_iff.mpr (iteUnnorm_ne_zero H t hψ₀)
  have hsqrt :
      ‖iteUnnorm H t ψ₀‖ =
        Real.exp (-t * sortedEigenvalues hH j) *
          Real.sqrt (∑ k : Fin (Fintype.card ι),
            ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
              Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j))) := by
    rw [← Real.sqrt_sq hpos.le, norm_sq_iteUnnorm_factor hH t ψ₀ (sortedEigenvalues hH j),
      Real.sqrt_mul (Real.exp_pos _).le]
    congr 1
    rw [show -2 * t * sortedEigenvalues hH j = (-t * sortedEigenvalues hH j) +
        (-t * sortedEigenvalues hH j) by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [iteCoeff, iteState, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, hsqrt,
    iteUnnorm, exp_smul_mulVec_repr hH (-(t : ℂ)) ψ₀ j]
  have hre : (-(t : ℂ) * (sortedEigenvalues hH j : ℂ)) =
      ((-t * sortedEigenvalues hH j : ℝ) : ℂ) := by push_cast; ring
  rw [hre, ← Complex.ofReal_exp, mul_inv]
  simp only [Complex.coe_algebraMap, Complex.ofReal_mul, Complex.ofReal_inv, Complex.real_smul]
  have hexp_ne : (Real.exp (-t * sortedEigenvalues hH j) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  field_simp [hexp_ne]

/-- **Support preservation**: `α_j(t) ≠ 0 ↔ α_j(0) ≠ 0` for every real time `t`. -/
theorem iteCoeff_ne_zero_iff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) (j : Fin (Fintype.card ι)) :
    iteCoeff hH t ψ₀ j ≠ 0 ↔ @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀ ≠ 0 := by
  rw [iteCoeff_eq hH t hψ₀ j, smul_ne_zero_iff]
  refine and_iff_right ?_
  have hnorm_pos : 0 < ‖iteUnnorm H t ψ₀‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (iteUnnorm_ne_zero H t hψ₀))
  have hfactor := norm_sq_iteUnnorm_factor hH t ψ₀ (sortedEigenvalues hH j)
  have hexp_pos : 0 < Real.exp (-2 * t * sortedEigenvalues hH j) := Real.exp_pos _
  have hsum_pos : 0 < ∑ k : Fin (Fintype.card ι),
      ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
        Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j)) := by nlinarith
  exact inv_ne_zero (Real.sqrt_pos.mpr hsum_pos).ne'

/-- Ground-state fidelity `f(t) = ∑_{j < μ} |α_j(t)|²` along ITE. -/
noncomputable def iteFidelity [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    (ψ₀ : EuclideanSpace ℂ ι) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
    ‖iteCoeff hH t ψ₀ j‖ ^ 2

/-- Ground-state fidelity at `t = 0` for a unit initial state. -/
@[simp]
theorem iteFidelity_zero [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) :
    iteFidelity hH 0 ψ₀ = ‖groundProjection hH ψ₀‖ ^ 2 := by
  rw [iteFidelity, norm_sq_groundProjection]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [iteCoeff_zero hH hψ₀ j]

/-- Exact formula for `iteFidelity` in terms of `a = ‖P₀ ψ₀‖²` and the excited weight `x(t)`. -/
theorem iteFidelity_eq_div [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    iteFidelity hH t ψ₀ =
      ‖groundProjection hH ψ₀‖ ^ 2 /
        (‖groundProjection hH ψ₀‖ ^ 2 +
          ∑ k ∈ Finset.univ.filter
              (fun k : Fin (Fintype.card ι) ↦ ¬ k.val < groundMultiplicity hH),
            ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
              Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH))) := by
  rw [← excitedWeight, ← norm_sq_iteUnnorm_ground_split hH t ψ₀, iteFidelity,
    norm_sq_groundProjection, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have heig := (sortedEigenvalues_eq_groundEnergy_iff hH j).mpr (Finset.mem_filter.mp hj).2
  rw [norm_sq_iteCoeff_eq hH t hψ₀ j, heig, sub_self, mul_zero, Real.exp_zero, mul_one]

/-- **Monotonicity of ground-state fidelity**: `t ↦ f(t)` is monotone increasing on `ℝ`. -/
theorem iteFidelity_monotone [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    Monotone (fun t ↦ iteFidelity hH t ψ₀) := by
  intro t₁ t₂ ht
  dsimp only
  rw [iteFidelity_eq_div hH t₁ hψ₀, iteFidelity_eq_div hH t₂ hψ₀, ← excitedWeight,
    ← excitedWeight]
  have hx₂_le : excitedWeight hH t₂ ψ₀ ≤ excitedWeight hH t₁ ψ₀ := by
    refine Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (sq_nonneg _)
    have := sub_nonneg.mpr (groundEnergy_le hH k)
    nlinarith
  have ha_nn : 0 ≤ ‖groundProjection hH ψ₀‖ ^ 2 := sq_nonneg _
  have hx₂_nn : 0 ≤ excitedWeight hH t₂ ψ₀ := excitedWeight_nonneg hH t₂ ψ₀
  by_cases ha0 : ‖groundProjection hH ψ₀‖ ^ 2 = 0
  · simp [ha0]
  · exact div_le_div_of_nonneg_left ha_nn
      (by linarith [lt_of_le_of_ne ha_nn (Ne.symm ha0)]) (by linarith)

/-- **Monotone convergence of ground-eigenspace amplitudes**: for every `j < μ`, `t ↦ |α_j(t)|`
is monotonically increasing on `ℝ`. -/
theorem norm_iteCoeff_monotone_of_ground [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) {j : Fin (Fintype.card ι)}
    (hj : j.val < groundMultiplicity hH) :
    Monotone (fun t ↦ ‖iteCoeff hH t ψ₀ j‖) := by
  intro t₁ t₂ ht
  dsimp only
  have heig := (sortedEigenvalues_eq_groundEnergy_iff hH j).mpr hj
  rw [iteCoeff_eq hH t₁ hψ₀ j, iteCoeff_eq hH t₂ hψ₀ j, norm_smul, norm_smul, heig]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hpos : ∀ t : ℝ, 0 < ∑ k : Fin (Fintype.card ι),
      ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
        Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH)) := by
    intro t
    have hfactor := norm_sq_iteUnnorm_factor hH t ψ₀ (groundEnergy hH)
    have hnorm_pos : 0 < ‖iteUnnorm H t ψ₀‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (iteUnnorm_ne_zero H t hψ₀))
    have hexp_pos : 0 < Real.exp (-2 * t * groundEnergy hH) := Real.exp_pos _
    nlinarith
  refine inv_anti₀ (Real.sqrt_pos.mpr (hpos t₂)) (Real.sqrt_le_sqrt ?_)
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hdiff := sub_nonneg.mpr (groundEnergy_le hH k)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (sq_nonneg _)

private lemma tendsto_exp_neg_two_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ ↦ Real.exp (-2 * t * c)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ ↦ (-2 * c) * t) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
  exact (Real.tendsto_exp_atBot.comp hlin).congr fun t ↦ by
    dsimp only [Function.comp_apply]; congr 1; ring

private lemma tendsto_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ ↦ Real.exp (-t * c)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ ↦ (-c) * t) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
  exact (Real.tendsto_exp_atBot.comp hlin).congr fun t ↦ by
    dsimp only [Function.comp_apply]; congr 1; ring

private lemma tendsto_finset_sum' {α E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] (s : Finset α) {f : α → ℝ → E} {a : α → E}
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (a i))) :
    Tendsto (fun t ↦ ∑ i ∈ s, f i t) atTop (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))

/-- **Convergence of ground-eigenspace amplitudes** (Eq. (1), `j < μ`):
`α_j(t) → α_j(0) / ‖P₀ ψ₀‖` as `t → ∞`. -/
theorem tendsto_iteCoeff_ground [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hP : groundProjection hH ψ₀ ≠ 0) {j : Fin (Fintype.card ι)}
    (hj : j.val < groundMultiplicity hH) :
    Tendsto (fun t ↦ iteCoeff hH t ψ₀ j) atTop
      (𝓝 ((‖groundProjection hH ψ₀‖⁻¹ : ℝ) • @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀)) := by
  have hψ₀ : ψ₀ ≠ 0 := by intro h; apply hP; simp [groundProjection, h]
  have heig := (sortedEigenvalues_eq_groundEnergy_iff hH j).mpr hj
  have hsum_tendsto :
      Tendsto (fun t : ℝ ↦ ∑ k : Fin (Fintype.card ι),
          ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
            Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH)))
        atTop (𝓝 (‖groundProjection hH ψ₀‖ ^ 2)) := by
    rw [norm_sq_groundProjection]
    have hsplit : ∀ t : ℝ, (∑ k : Fin (Fintype.card ι),
            ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
              Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH))) =
          (∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card ι) ↦ k.val < groundMultiplicity hH),
            ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2) +
          ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card ι) ↦ ¬ k.val < groundMultiplicity hH),
            ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
              Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH)) := fun t ↦ by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k : Fin (Fintype.card ι) ↦ k.val < groundMultiplicity hH)]
      exact congrArg (· + _) (Finset.sum_congr rfl fun k hk ↦ by
        simp [(sortedEigenvalues_eq_groundEnergy_iff hH k).mpr (Finset.mem_filter.mp hk).2])
    simp_rw [hsplit]
    have htail : Tendsto (fun t : ℝ ↦ ∑ k ∈ Finset.univ.filter
        (fun k : Fin (Fintype.card ι) ↦ ¬ k.val < groundMultiplicity hH),
        ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
          Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH))) atTop (𝓝 0) := by
      have h0 := tendsto_finset_sum'
        (Finset.univ.filter (fun k : Fin (Fintype.card ι) ↦ ¬ k.val < groundMultiplicity hH))
        (a := fun _ ↦ (0 : ℝ)) fun k hk ↦ by
          have hkgt : 0 < sortedEigenvalues hH k - groundEnergy hH :=
            sub_pos.mpr (lt_of_le_of_ne (groundEnergy_le hH k) fun heq ↦
              (Finset.mem_filter.mp hk).2
                ((sortedEigenvalues_eq_groundEnergy_iff hH k).mp heq.symm))
          simpa only [mul_zero] using (tendsto_const_nhds
            (x := ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2)).mul (tendsto_exp_neg_two_mul hkgt)
      simpa only [Finset.sum_const_zero] using h0
    simpa only [add_zero] using (tendsto_const_nhds (x := ∑ k ∈ Finset.univ.filter
      (fun k : Fin (Fintype.card ι) ↦ k.val < groundMultiplicity hH),
      ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2)).add htail
  have hPpos : 0 < ‖groundProjection hH ψ₀‖ := norm_pos_iff.mpr hP
  have hsqrt := (Real.continuous_sqrt.tendsto _).comp hsum_tendsto
  rw [Real.sqrt_sq hPpos.le] at hsqrt
  exact ((hsqrt.inv₀ hPpos.ne').smul_const (@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀)).congr
    fun t ↦ by dsimp only [Function.comp_apply]; rw [iteCoeff_eq hH t hψ₀ j, heig]

/-- **Convergence of excited-state amplitudes** (Eq. (1), `j ≥ μ`): `α_j(t) → 0` as `t → ∞`. -/
theorem tendsto_iteCoeff_excited [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hP : groundProjection hH ψ₀ ≠ 0) {j : Fin (Fintype.card ι)}
    (hj : groundMultiplicity hH ≤ j.val) :
    Tendsto (fun t ↦ iteCoeff hH t ψ₀ j) atTop (𝓝 0) := by
  have hgap_pos : 0 < spectralGap hH := spectralGap_pos hH (lt_of_le_of_lt hj j.isLt)
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖iteCoeff hH t ψ₀ j‖ ≤
        ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ *
          (‖groundProjection hH ψ₀‖⁻¹ * Real.exp (-t * spectralGap hH)) := by
    intro t ht
    have hsplit := norm_sq_iteUnnorm_ground_split hH t ψ₀
    have hfactor : Real.exp (-2 * t * groundEnergy hH) * ‖groundProjection hH ψ₀‖ ^ 2 ≤
        ‖iteUnnorm H t ψ₀‖ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left (show ‖groundProjection hH ψ₀‖ ^ 2 ≤
          Real.exp (2 * t * groundEnergy hH) * ‖iteUnnorm H t ψ₀‖ ^ 2 by
        linarith [excitedWeight_nonneg hH t ψ₀]) (Real.exp_pos (-2 * t * groundEnergy hH)).le
      rwa [← mul_assoc, ← Real.exp_add,
        show -2 * t * groundEnergy hH + 2 * t * groundEnergy hH = 0 by ring,
        Real.exp_zero, one_mul] at hmul
    have hnorm_ge : Real.exp (-t * groundEnergy hH) * ‖groundProjection hH ψ₀‖ ≤
        ‖iteUnnorm H t ψ₀‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (iteUnnorm H t ψ₀)),
        ← Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)), mul_pow,
        ← Real.exp_nat_mul]
      exact Real.sqrt_le_sqrt (by convert hfactor using 3; push_cast; ring)
    rw [iteCoeff, iteState, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, norm_mul,
      RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), iteUnnorm,
      exp_smul_mulVec_repr hH (-(t : ℂ)) ψ₀ j, norm_mul, Complex.norm_exp,
      show (-(t : ℂ) * (sortedEigenvalues hH j : ℂ)).re = -(t * sortedEigenvalues hH j) by simp]
    change ‖iteUnnorm H t ψ₀‖⁻¹ * _ ≤ _
    have hinv_le := inv_anti₀ (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hP)) hnorm_ge
    have hexp_le :
        Real.exp (-(t * sortedEigenvalues hH j)) * (Real.exp (-t * groundEnergy hH))⁻¹ ≤
          Real.exp (-t * spectralGap hH) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by have := spectralGap_le_sub_of_ge hH hj; nlinarith)
    calc
      ‖iteUnnorm H t ψ₀‖⁻¹ *
          (Real.exp (-(t * sortedEigenvalues hH j)) * ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖)
          ≤ (Real.exp (-t * groundEnergy hH) * ‖groundProjection hH ψ₀‖)⁻¹ *
            (Real.exp (-(t * sortedEigenvalues hH j)) *
              ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖) := by gcongr
      _ = ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ * (‖groundProjection hH ψ₀‖⁻¹ *
            (Real.exp (-(t * sortedEigenvalues hH j)) * (Real.exp (-t * groundEnergy hH))⁻¹)) := by
        rw [mul_inv]; ring
      _ ≤ ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ *
            (‖groundProjection hH ψ₀‖⁻¹ * Real.exp (-t * spectralGap hH)) := by gcongr
  exact squeeze_zero_norm' (eventually_atTop.mpr ⟨0, hbound⟩)
    (by simpa using tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_exp_neg_mul hgap_pos)))

/-- **Convergence of ITE to the normalized ground-eigenspace projection**: whenever `P₀ ψ₀ ≠ 0`,
`iteState H t ψ₀ → ‖P₀ ψ₀‖⁻¹ • P₀ ψ₀` as `t → ∞`. -/
theorem tendsto_iteState_ground [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hP : groundProjection hH ψ₀ ≠ 0) :
    Tendsto (fun t ↦ iteState H t ψ₀) atTop
      (𝓝 (‖groundProjection hH ψ₀‖⁻¹ • groundProjection hH ψ₀)) := by
  have hrep : ∀ t : ℝ, iteState H t ψ₀ =
      ∑ j : Fin (Fintype.card ι), iteCoeff hH t ψ₀ j • sortedEigenbasis hH j := fun t ↦
    ((sortedEigenbasis hH).sum_repr' (iteState H t ψ₀)).symm
  have hlim :
      ‖groundProjection hH ψ₀‖⁻¹ • groundProjection hH ψ₀ =
        ∑ j : Fin (Fintype.card ι),
          (if j.val < groundMultiplicity hH then
            (‖groundProjection hH ψ₀‖⁻¹ : ℝ) • @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀
          else 0) • sortedEigenbasis hH j := by
    rw [groundProjection, Finset.smul_sum]
    simp_rw [ite_smul, zero_smul, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.real_smul, smul_smul]; rfl
  rw [hlim]; simp_rw [hrep]
  refine tendsto_finset_sum' _ fun j _ ↦ ?_
  by_cases hj : j.val < groundMultiplicity hH
  · simp only [hj, ↓reduceIte]; exact (tendsto_iteCoeff_ground hH hP hj).smul_const _
  · simp only [hj, ↓reduceIte, zero_smul]
    simpa using (tendsto_iteCoeff_excited hH hP (Nat.not_lt.mp hj)).smul_const
      (sortedEigenbasis hH j)

/-- **General active-eigenspace convergence**: for any nonzero initial state `ψ₀ ≠ 0`, let `λ_*`
be the smallest eigenvalue of `H` having nonzero overlap with `ψ₀`, and `P_* ψ₀` the orthogonal
projection of `ψ₀` onto `ker (H - λ_* I)`. Then `iteState H t ψ₀ → ‖P_* ψ₀‖⁻¹ • P_* ψ₀`. -/
theorem tendsto_iteState_active {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    let active := Finset.univ.filter fun j : Fin (Fintype.card ι) ↦
      @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀ ≠ 0
    have hact : active.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hψ₀
      rw [← (sortedEigenbasis hH).sum_repr' ψ₀]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have h0 : @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀ = 0 := by
        by_contra hne
        have : j ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        simp [hempty] at this
      simp [h0]
    let lamStar := (active.image (sortedEigenvalues hH)).min' (hact.image _)
    let proj := ∑ j ∈ Finset.univ.filter
        (fun j : Fin (Fintype.card ι) ↦ sortedEigenvalues hH j = lamStar),
      (@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀) • sortedEigenbasis hH j
    Tendsto (fun t ↦ iteState H t ψ₀) atTop (𝓝 (‖proj‖⁻¹ • proj)) := by
  intro active hact lamStar proj
  have hproj_ne : proj ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hact.image (sortedEigenvalues hH)))
    have hact_j₀ : @inner ℂ _ _ (sortedEigenbasis hH j₀) ψ₀ ≠ 0 := (Finset.mem_filter.mp hj₀.1).2
    intro h0
    have hinner0 : @inner ℂ _ _ (sortedEigenbasis hH j₀) proj = 0 := by rw [h0, inner_zero_right]
    rw [inner_sum, Finset.sum_eq_single j₀] at hinner0
    · exact hact_j₀ (by simpa [inner_smul_right, (sortedEigenbasis hH).orthonormal.1 j₀] using
        hinner0)
    · intro k _ hkj
      simp [inner_smul_right, (sortedEigenbasis hH).orthonormal.2 hkj.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀.2⟩))
  have hle_lam : ∀ k : Fin (Fintype.card ι),
      @inner ℂ _ _ (sortedEigenbasis hH k) ψ₀ ≠ 0 → lamStar ≤ sortedEigenvalues hH k :=
    fun k hk ↦ Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩)
  have hnorm_sq_proj : ‖proj‖ ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) ↦ sortedEigenvalues hH j = lamStar),
        ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, Orthonormal.inner_sum (sortedEigenbasis hH).orthonormal,
      map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [RCLike.conj_mul]; norm_cast
  have hrep : ∀ t : ℝ, iteState H t ψ₀ =
      ∑ j : Fin (Fintype.card ι), iteCoeff hH t ψ₀ j • sortedEigenbasis hH j := fun t ↦
    ((sortedEigenbasis hH).sum_repr' (iteState H t ψ₀)).symm
  have hlim :
      ‖proj‖⁻¹ • proj =
        ∑ j : Fin (Fintype.card ι),
          (if sortedEigenvalues hH j = lamStar then
            (‖proj‖⁻¹ : ℝ) • @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀
          else 0) • sortedEigenbasis hH j := by
    change ‖proj‖⁻¹ • (∑ j ∈ Finset.univ.filter
        (fun j : Fin (Fintype.card ι) ↦ sortedEigenvalues hH j = lamStar),
      (@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀) • sortedEigenbasis hH j) = _
    rw [Finset.smul_sum]
    simp_rw [ite_smul, zero_smul, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.real_smul, smul_smul]; rfl
  rw [hlim]
  simp_rw [hrep]
  refine tendsto_finset_sum' _ fun j _ ↦ ?_
  by_cases hj : sortedEigenvalues hH j = lamStar
  · simp only [hj, ↓reduceIte]
    have hsum_tendsto :
        Tendsto (fun t : ℝ ↦ ∑ k : Fin (Fintype.card ι),
            ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
              Real.exp (-2 * t * (sortedEigenvalues hH k - lamStar)))
          atTop (𝓝 (‖proj‖ ^ 2)) := by
      rw [hnorm_sq_proj]
      have hsplit : ∀ t : ℝ, (∑ k : Fin (Fintype.card ι),
              ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                Real.exp (-2 * t * (sortedEigenvalues hH k - lamStar))) =
            (∑ k ∈ Finset.univ.filter (fun k ↦ sortedEigenvalues hH k = lamStar),
                ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2) +
              (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ sortedEigenvalues hH k = lamStar),
                ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                  Real.exp (-2 * t * (sortedEigenvalues hH k - lamStar))) := fun t ↦ by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun k : Fin (Fintype.card ι) ↦ sortedEigenvalues hH k = lamStar)]
        exact congrArg (· + _) (Finset.sum_congr rfl fun k hk ↦ by
          simp [(Finset.mem_filter.mp hk).2])
      simp_rw [hsplit]
      have htail : Tendsto (fun t : ℝ ↦ ∑ k ∈ Finset.univ.filter
          (fun k : Fin (Fintype.card ι) ↦ ¬ sortedEigenvalues hH k = lamStar),
          ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
            Real.exp (-2 * t * (sortedEigenvalues hH k - lamStar))) atTop (𝓝 0) := by
        simpa using tendsto_finset_sum'
          (Finset.univ.filter (fun k : Fin (Fintype.card ι) ↦ ¬ sortedEigenvalues hH k = lamStar))
          (f := fun k t ↦ ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
            Real.exp (-2 * t * (sortedEigenvalues hH k - lamStar)))
          (a := fun _ ↦ (0 : ℝ)) fun k hk ↦ by
            by_cases hinner0 : @inner ℂ _ _ (sortedEigenbasis hH k) ψ₀ = 0
            · simp [hinner0]
            · have hkgt : 0 < sortedEigenvalues hH k - lamStar :=
                sub_pos.mpr (lt_of_le_of_ne (hle_lam k hinner0)
                  (Ne.symm (Finset.mem_filter.mp hk).2))
              simpa only [mul_zero] using (tendsto_const_nhds
                (x := ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2)).mul
                (tendsto_exp_neg_two_mul hkgt)
      simpa only [add_zero] using (tendsto_const_nhds (x := ∑ k ∈ Finset.univ.filter
        (fun k : Fin (Fintype.card ι) ↦ sortedEigenvalues hH k = lamStar),
        ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2)).add htail
    have hPpos : 0 < ‖proj‖ := norm_pos_iff.mpr hproj_ne
    have hsqrt := (Real.continuous_sqrt.tendsto _).comp hsum_tendsto
    rw [Real.sqrt_sq hPpos.le] at hsqrt
    exact (((hsqrt.inv₀ hPpos.ne').smul_const (@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀)).congr
      fun t ↦ by dsimp only [Function.comp_apply]; rw [iteCoeff_eq hH t hψ₀ j, hj]).smul_const _
  · simp only [hj, ↓reduceIte, zero_smul]
    by_cases hinner0 : @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀ = 0
    · have h0 : ∀ t : ℝ, iteCoeff hH t ψ₀ j = 0 := fun t ↦ by
        rw [iteCoeff_eq hH t hψ₀ j, hinner0, smul_zero]
      simp [h0]
    · have hjgt : 0 < sortedEigenvalues hH j - lamStar :=
        sub_pos.mpr (lt_of_le_of_ne (hle_lam j hinner0) (Ne.symm hj))
      have hPpos : 0 < ‖proj‖ := norm_pos_iff.mpr hproj_ne
      have hbound : ∀ t : ℝ, 0 ≤ t →
          ‖iteCoeff hH t ψ₀ j‖ ≤ (‖proj‖⁻¹ * Real.exp (-t * (sortedEigenvalues hH j - lamStar))) *
            ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ := fun t _ ↦ by
        rw [iteCoeff_eq hH t hψ₀ j, norm_smul, Real.norm_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hsum_ge : ‖proj‖ ^ 2 * Real.exp (2 * t * (sortedEigenvalues hH j - lamStar)) ≤
            ∑ k : Fin (Fintype.card ι), ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
              Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j)) := by
          rw [hnorm_sq_proj, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun k : Fin (Fintype.card ι) ↦ sortedEigenvalues hH k = lamStar)]
          have hnn : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ sortedEigenvalues hH k = lamStar),
              ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j)) :=
            Finset.sum_nonneg fun _ _ ↦ by positivity
          have heq : (∑ k ∈ Finset.univ.filter (fun k ↦ sortedEigenvalues hH k = lamStar),
                ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                  Real.exp (2 * t * (sortedEigenvalues hH j - lamStar))) =
              ∑ k ∈ Finset.univ.filter (fun k ↦ sortedEigenvalues hH k = lamStar),
                ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                  Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j)) :=
            Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2]; congr 2; ring
          linarith
        calc
          (Real.sqrt (∑ k : Fin (Fintype.card ι), ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                Real.exp (-2 * t * (sortedEigenvalues hH k - sortedEigenvalues hH j))))⁻¹
              ≤ (‖proj‖ * Real.exp (t * (sortedEigenvalues hH j - lamStar)))⁻¹ := by
            refine inv_anti₀ (mul_pos hPpos (Real.exp_pos _)) ?_
            rw [← Real.sqrt_sq (mul_nonneg hPpos.le (Real.exp_pos _).le), mul_pow,
              ← Real.exp_nat_mul]
            exact Real.sqrt_le_sqrt (by convert hsum_ge using 3; push_cast; ring)
          _ = ‖proj‖⁻¹ * Real.exp (-t * (sortedEigenvalues hH j - lamStar)) := by
            rw [mul_inv, ← Real.exp_neg]; congr 2; ring
      have htend : Tendsto (fun t : ℝ ↦
          (‖proj‖⁻¹ * Real.exp (-t * (sortedEigenvalues hH j - lamStar))) *
            ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul (tendsto_exp_neg_mul hjgt)).mul tendsto_const_nhds
      simpa using (squeeze_zero_norm' (eventually_atTop.mpr ⟨0, hbound⟩) htend).smul_const
        (sortedEigenbasis hH j)

end ImaginaryTimeEvolution

section DifferentialEquations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Orthogonal projection onto the tangent space of the unit sphere** at `ψ`:
`pr_{T_ψ S}(w) = w - Re ⟨ψ, w⟩ • ψ`. -/
noncomputable def sphereTangentProj (ψ w : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  w - (RCLike.re (@inner ℂ _ _ ψ w) : ℂ) • ψ

omit [DecidableEq ι] in
/-- The tangent-space projection of a vector parallel to `ψ` vanishes on the unit sphere. -/
@[simp]
theorem sphereTangentProj_self {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    sphereTangentProj ψ ψ = 0 := by
  simp [sphereTangentProj, inner_self_eq_norm_sq_to_K, hψ]

omit [DecidableEq ι] in
/-- For a unit vector `ψ`, `pr_{T_ψ S}(w)` is real-orthogonal to `ψ`. -/
theorem real_inner_sphereTangentProj {ψ w : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    @inner ℝ _ _ ψ (sphereTangentProj ψ w) = 0 := by
  rw [sphereTangentProj, real_inner_eq_re_complex, inner_sub_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
  simp

/-- Real-valued expectation energy `E(t) = Re ⟨ψ(t), H ψ(t)⟩` along ITE. -/
@[expose] noncomputable def iteEnergy (H : Matrix ι ι ℂ) (t : ℝ) (ψ₀ : EuclideanSpace ℂ ι) : ℝ :=
  RCLike.re (@inner ℂ _ _ (iteState H t ψ₀) (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp)))

/-- Expectation energy at `t = 0` for a unit initial state. -/
@[simp]
theorem iteEnergy_zero (H : Matrix ι ι ℂ) {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) :
    iteEnergy H 0 ψ₀ = RCLike.re (@inner ℂ _ _ ψ₀ (WithLp.toLp 2 (H *ᵥ ψ₀.ofLp))) := by
  rw [iteEnergy, iteState_zero H hψ₀]

/-- Spectral expansion of expectation energy: `E(t) = ∑_k λ_k |α_k(t)|²`. -/
theorem iteEnergy_eq_sum_eigenvalues {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    (ψ₀ : EuclideanSpace ℂ ι) :
    iteEnergy H t ψ₀ =
      ∑ k : Fin (Fintype.card ι), sortedEigenvalues hH k * ‖iteCoeff hH t ψ₀ k‖ ^ 2 := by
  set ψ := iteState H t ψ₀
  have hHw : WithLp.toLp 2 (H *ᵥ ψ.ofLp) =
      ∑ k, ((sortedEigenvalues hH k : ℂ) * iteCoeff hH t ψ₀ k) • sortedEigenbasis hH k := by
    conv_lhs => rw [((sortedEigenbasis hH).sum_repr' ψ).symm]
    ext x
    simp only [iteCoeff, ψ, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec_sum, Matrix.mulVec_smul, mulVec_sortedEigenbasis]
    refine Finset.sum_congr rfl fun k _ ↦ by ring
  rw [iteEnergy, hHw, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [inner_smul_right, iteCoeff, ← inner_conj_symm (sortedEigenbasis hH k) (iteState H t ψ₀),
    mul_assoc, RCLike.conj_mul, Complex.norm_conj]
  simp [sq]

omit [DecidableEq ι] in
/-- For a Hermitian matrix `H`, `⟨ψ, H ψ⟩` is purely real. -/
theorem inner_mulVec_self_eq_re {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ψ : EuclideanSpace ℂ ι) :
    @inner ℂ _ _ ψ (WithLp.toLp 2 (H *ᵥ ψ.ofLp)) =
      (RCLike.re (@inner ℂ _ _ ψ (WithLp.toLp 2 (H *ᵥ ψ.ofLp))) : ℂ) := by
  classical
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hconj : starRingEnd ℂ (@inner ℂ _ _ ψ (WithLp.toLp 2 (H *ᵥ ψ.ofLp))) =
      @inner ℂ _ _ ψ (WithLp.toLp 2 (H *ᵥ ψ.ofLp)) := by
    rw [inner_conj_symm]
    exact hsym ψ ψ
  exact (Complex.conj_eq_iff_re.mp hconj).symm

/-- **Spherical gradient-flow ODE for ITE** (Eq. (2)):
`d/dt |ψ(t)⟩ = Re ⟨ψ(t)|H|ψ(t)⟩ |ψ(t)⟩ - H|ψ(t)⟩ = -pr_{T_{ψ(t)} S}(H|ψ(t)⟩)`. -/
theorem hasDerivAt_iteState (H : Matrix ι ι ℂ) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    HasDerivAt (fun s ↦ iteState H s ψ₀)
      (-sphereTangentProj (iteState H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp))) t := by
  have hu : HasDerivAt (fun s ↦ iteUnnorm H s ψ₀)
      (-(WithLp.toLp 2 (H *ᵥ (iteUnnorm H t ψ₀).ofLp))) t := by
    have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-H) t
    have heq : (fun s : ℝ ↦ NormedSpace.exp (s • (-H))) =
        fun s : ℝ ↦ NormedSpace.exp ((-(s : ℂ)) • H) := by
      funext s; congr 1; ext i j; simp
    rw [heq] at hexp
    let L : Matrix ι ι ℂ →L[ℝ] EuclideanSpace ℂ ι :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M ↦ WithLp.toLp 2 (M *ᵥ ψ₀.ofLp)
          map_add' := fun M₁ M₂ ↦ by ext i; simp [Matrix.add_mulVec]
          map_smul' := fun r M ↦ by ext i; simp [Matrix.smul_mulVec] }
    have hcomp := L.hasFDerivAt.comp_hasDerivAt t hexp
    have hmul : NormedSpace.exp ((-(t : ℂ)) • H) * (-H) =
        (-H) * NormedSpace.exp ((-(t : ℂ)) • H) := by
      have hcomm : Commute ((-(t : ℂ)) • H) H := (Commute.refl H).smul_left _
      exact (Commute.exp_left hcomm).neg_right
    have hderiv_eq : L (NormedSpace.exp (t • (-H)) * (-H)) =
        -(WithLp.toLp 2 (H *ᵥ (iteUnnorm H t ψ₀).ofLp)) := by
      rw [show t • (-H) = (-(t : ℂ)) • H by ext i j; simp]
      ext i
      change ((NormedSpace.exp ((-(t : ℂ)) • H) * (-H)) *ᵥ ψ₀.ofLp) i =
        (-(H *ᵥ (iteUnnorm H t ψ₀).ofLp)) i
      rw [hmul, ← Matrix.mulVec_mulVec, Matrix.neg_mulVec]; rfl
    rw [hderiv_eq] at hcomp; exact hcomp
  have hne : iteUnnorm H t ψ₀ ≠ 0 := iteUnnorm_ne_zero H t hψ₀
  have hnorm_sq : HasDerivAt (fun s ↦ ‖iteUnnorm H s ψ₀‖ ^ 2)
      (-2 * RCLike.re (@inner ℂ _ _ (iteUnnorm H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteUnnorm H t ψ₀).ofLp)))) t := by
    have h1 := HasDerivAt.inner ℝ hu hu
    rw [show (fun s ↦ @inner ℝ _ _ (iteUnnorm H s ψ₀) (iteUnnorm H s ψ₀)) =
        fun s ↦ ‖iteUnnorm H s ψ₀‖ ^ 2 from funext fun s ↦ real_inner_self_eq_norm_sq _] at h1
    convert h1 using 1
    rw [real_inner_comm (iteUnnorm H t ψ₀) _, inner_neg_right, real_inner_eq_re_complex]; ring
  have hnorm_pos : 0 < ‖iteUnnorm H t ψ₀‖ := norm_pos_iff.mpr hne
  have hinv_norm : HasDerivAt (fun s ↦ ‖iteUnnorm H s ψ₀‖⁻¹)
      (‖iteUnnorm H t ψ₀‖⁻¹ ^ 3 * RCLike.re (@inner ℂ _ _ (iteUnnorm H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteUnnorm H t ψ₀).ofLp)))) t := by
    have hcomp := (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ))
      (Or.inl (sq_pos_of_pos hnorm_pos).ne')).comp t hnorm_sq
    rw [show ((fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) ∘ (fun s ↦ ‖iteUnnorm H s ψ₀‖ ^ 2)) =
        fun s ↦ ‖iteUnnorm H s ψ₀‖⁻¹ from funext fun s ↦ by
      simp only [Function.comp_apply, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (norm_nonneg _)]] at hcomp
    convert hcomp using 1
    have hpow3 : (‖iteUnnorm H t ψ₀‖ ^ 2) ^ (-(1 / 2 : ℝ) - 1) = ‖iteUnnorm H t ψ₀‖⁻¹ ^ 3 := by
      rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by ring, Real.rpow_neg (sq_nonneg _),
        ← Real.rpow_natCast ‖iteUnnorm H t ψ₀‖ 2, ← Real.rpow_mul (norm_nonneg _),
        show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    rw [hpow3]; ring
  have hsmul := hinv_norm.smul hu
  change HasDerivAt (fun s ↦ iteState H s ψ₀) _ t at hsmul
  convert hsmul using 1
  rw [sphereTangentProj, neg_sub, iteState]
  have hmv : WithLp.toLp 2 (H *ᵥ (‖iteUnnorm H t ψ₀‖⁻¹ • iteUnnorm H t ψ₀).ofLp) =
      (‖iteUnnorm H t ψ₀‖⁻¹ : ℂ) • WithLp.toLp 2 (H *ᵥ (iteUnnorm H t ψ₀).ofLp) := by
    ext i; simp [Matrix.mulVec_smul]
  have hinner_scale :
      RCLike.re (@inner ℂ _ _ (‖iteUnnorm H t ψ₀‖⁻¹ • iteUnnorm H t ψ₀)
          (WithLp.toLp 2 (H *ᵥ (‖iteUnnorm H t ψ₀‖⁻¹ • iteUnnorm H t ψ₀).ofLp))) =
        ‖iteUnnorm H t ψ₀‖⁻¹ ^ 2 * RCLike.re (@inner ℂ _ _ (iteUnnorm H t ψ₀)
          (WithLp.toLp 2 (H *ᵥ (iteUnnorm H t ψ₀).ofLp))) := by
    rw [hmv, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right]
    simp [Complex.conj_ofReal]; ring
  rw [hinner_scale, hmv]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.coe_algebraMap, smul_smul, smul_neg,
    sub_eq_add_neg, add_comm, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  congr 1; congr 1; ring

/-- **Energy dissipation formula**:
`E'(t) = -2 ‖pr_{T_{ψ(t)} S}(H|ψ(t)⟩)‖² ≤ 0`. -/
theorem hasDerivAt_iteEnergy {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    HasDerivAt (fun s ↦ iteEnergy H s ψ₀)
      (-2 * ‖sphereTangentProj (iteState H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp))‖ ^ 2) t := by
  have hψ := hasDerivAt_iteState H t hψ₀
  let L : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ WithLp.toLp 2 (H *ᵥ v.ofLp)
        map_add' := fun v₁ v₂ ↦ by ext i; simp [Matrix.mulVec_add]
        map_smul' := fun r v ↦ by ext i; simp [Matrix.mulVec_smul] }
  have hHψ := L.hasFDerivAt.comp_hasDerivAt t hψ
  have hinner := HasDerivAt.inner ℝ hψ hHψ
  simp only [Function.comp_apply] at hinner
  have hfun : (fun s ↦ @inner ℝ _ _ (iteState H s ψ₀) (L (iteState H s ψ₀))) =
      fun s ↦ iteEnergy H s ψ₀ := funext fun s ↦ real_inner_eq_re_complex _ _
  rw [hfun] at hinner
  convert hinner using 1
  set ψ := iteState H t ψ₀
  set w := WithLp.toLp 2 (H *ᵥ ψ.ofLp)
  set v := sphereTangentProj ψ w
  have hsym_real : @inner ℝ _ _ ψ (L (-v)) = @inner ℝ _ _ (-v) w := by
    rw [real_inner_eq_re_complex, real_inner_eq_re_complex]
    have h := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) ψ (-v)
    change @inner ℂ _ _ w (-v) = @inner ℂ _ _ ψ (L (-v)) at h
    rw [← h, ← inner_conj_symm]; exact Complex.conj_re _
  rw [hsym_real, inner_neg_left, inner_neg_left]
  have hw : w = v + (RCLike.re (@inner ℂ _ _ ψ w) : ℂ) • ψ := by simp [v, sphereTangentProj]
  have hv_orth : @inner ℝ _ _ v ψ = 0 := by
    rw [real_inner_comm]; exact real_inner_sphereTangentProj (norm_iteState H t hψ₀)
  have hv_inner : @inner ℝ _ _ v w = ‖v‖ ^ 2 := by
    rw [hw, inner_add_right, real_inner_self_eq_norm_sq,
      show (RCLike.re (@inner ℂ _ _ ψ w) : ℂ) • ψ = (RCLike.re (@inner ℂ _ _ ψ w)) • ψ from
        (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm,
      inner_smul_right, hv_orth, mul_zero, add_zero]
  change -2 * ‖v‖ ^ 2 = -@inner ℝ _ _ v w + -@inner ℝ _ _ v w
  rw [hv_inner]; ring

/-- **Energy monotonicity**: `t ↦ E(t)` is antitone (monotonically decreasing) on `ℝ`. -/
theorem iteEnergy_antitone {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    Antitone (fun t ↦ iteEnergy H t ψ₀) := by
  refine antitone_of_deriv_nonpos (fun t ↦ (hasDerivAt_iteEnergy hH t hψ₀).differentiableAt)
    fun t ↦ ?_
  rw [(hasDerivAt_iteEnergy hH t hψ₀).deriv]
  nlinarith [sq_nonneg ‖sphereTangentProj (iteState H t ψ₀)
    (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp))‖]

/-- **Eigenstate characterization of zero energy gradient**: `E'(t) = 0` iff `ψ(t)` is an
eigenstate of `H` (with eigenvalue `E(t)`). -/
theorem deriv_iteEnergy_eq_zero_iff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) :
    deriv (fun s ↦ iteEnergy H s ψ₀) t = 0 ↔
      H *ᵥ (iteState H t ψ₀).ofLp = (iteEnergy H t ψ₀ : ℂ) • (iteState H t ψ₀).ofLp := by
  rw [(hasDerivAt_iteEnergy hH t hψ₀).deriv]
  constructor
  · intro h0
    have hnorm0 : ‖sphereTangentProj (iteState H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp))‖ = 0 := by
      nlinarith [sq_nonneg ‖sphereTangentProj (iteState H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp))‖]
    have hv0 := norm_eq_zero.mp hnorm0
    simpa [iteEnergy] using congrArg WithLp.ofLp (sub_eq_zero.mp hv0)
  · intro heig
    have hv0 : sphereTangentProj (iteState H t ψ₀)
        (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp)) = 0 := by
      rw [sphereTangentProj, sub_eq_zero]
      exact WithLp.ofLp_injective 2 heig
    simp [hv0]

/-- **Exact amplitude-squared ODE**:
`d/dt |α_j(t)|² = 2 (E(t) - λ_j) |α_j(t)|²` for every eigenbasis index `j`. -/
theorem hasDerivAt_norm_sq_iteCoeff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) (j : Fin (Fintype.card ι)) :
    HasDerivAt (fun s ↦ ‖iteCoeff hH s ψ₀ j‖ ^ 2)
      (2 * (iteEnergy H t ψ₀ - sortedEigenvalues hH j) * ‖iteCoeff hH t ψ₀ j‖ ^ 2) t := by
  have hψ := hasDerivAt_iteState H t hψ₀
  let L : EuclideanSpace ℂ ι →L[ℝ] ℂ :=
    (innerSL ℂ (sortedEigenbasis hH j)).restrictScalars ℝ
  have hα : HasDerivAt (fun s ↦ iteCoeff hH s ψ₀ j)
      (@inner ℂ _ _ (sortedEigenbasis hH j)
        (-sphereTangentProj (iteState H t ψ₀)
          (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp)))) t :=
    L.hasFDerivAt.comp_hasDerivAt t hψ
  have hnorm_sq := HasDerivAt.inner ℝ hα hα
  have hfun : (fun s ↦ @inner ℝ _ _ (iteCoeff hH s ψ₀ j) (iteCoeff hH s ψ₀ j)) =
      fun s ↦ ‖iteCoeff hH s ψ₀ j‖ ^ 2 := by
    funext s; exact real_inner_self_eq_norm_sq _
  rw [hfun] at hnorm_sq
  convert hnorm_sq using 1
  have hproj_inner :
      @inner ℂ _ _ (sortedEigenbasis hH j)
          (-sphereTangentProj (iteState H t ψ₀)
            (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp))) =
        ((iteEnergy H t ψ₀ - sortedEigenvalues hH j : ℝ) : ℂ) * iteCoeff hH t ψ₀ j := by
    rw [sphereTangentProj, neg_sub, inner_sub_right, inner_smul_right]
    have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    have hHw : @inner ℂ _ _ (sortedEigenbasis hH j)
        (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp)) =
        (sortedEigenvalues hH j : ℂ) * iteCoeff hH t ψ₀ j := by
      have h := hsym (sortedEigenbasis hH j) (iteState H t ψ₀)
      change @inner ℂ _ _ (WithLp.toLp 2 (H *ᵥ (sortedEigenbasis hH j).ofLp)) (iteState H t ψ₀) =
        @inner ℂ _ _ (sortedEigenbasis hH j) (WithLp.toLp 2 (H *ᵥ (iteState H t ψ₀).ofLp)) at h
      rw [← h, mulVec_sortedEigenbasis hH j, WithLp.toLp_smul, inner_smul_left]
      simp [iteCoeff]
    rw [hHw, iteEnergy, iteCoeff]
    push_cast; ring
  rw [hproj_inner, real_inner_comm (iteCoeff hH t ψ₀ j) _, real_inner_eq_re_complex,
    RCLike.inner_apply]
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero, Complex.conj_re, Complex.conj_im]
  have hsq : (iteCoeff hH t ψ₀ j).re * (iteCoeff hH t ψ₀ j).re +
      (iteCoeff hH t ψ₀ j).im * (iteCoeff hH t ψ₀ j).im = ‖iteCoeff hH t ψ₀ j‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [← hsq]; ring

end DifferentialEquations

section ConvergenceRates

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Exponential suppression of excited amplitudes**: for `j ≥ μ` and `t ≥ 0`,
`|α_j(t)|² ≤ |α_j(0)|² * f(0)⁻¹ * exp (-2 t Δ)`. -/
theorem iteCoeff_norm_sq_le_of_excited {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {t : ℝ}
    (ht : 0 ≤ t) {ψ₀ : EuclideanSpace ℂ ι} (hP : groundProjection hH ψ₀ ≠ 0)
    {j : Fin (Fintype.card ι)} (hj : groundMultiplicity hH ≤ j.val) :
    ‖iteCoeff hH t ψ₀ j‖ ^ 2 ≤
      ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 *
        (‖groundProjection hH ψ₀‖ ^ 2)⁻¹ * Real.exp (-2 * t * spectralGap hH) := by
  have hψ₀ : ψ₀ ≠ 0 := by intro h; apply hP; simp [groundProjection, h]
  have hPpos : 0 < ‖groundProjection hH ψ₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hP)
  have hden : ‖groundProjection hH ψ₀‖ ^ 2 ≤
      Real.exp (2 * t * groundEnergy hH) * ‖iteUnnorm H t ψ₀‖ ^ 2 := by
    rw [norm_sq_iteUnnorm_ground_split hH t ψ₀]
    linarith [excitedWeight_nonneg hH t ψ₀]
  rw [norm_sq_iteCoeff_eq hH t hψ₀ j]
  have hexp_le :
      Real.exp (-2 * t * (sortedEigenvalues hH j - groundEnergy hH)) ≤
        Real.exp (-2 * t * spectralGap hH) :=
    Real.exp_le_exp.mpr (by have := spectralGap_le_sub_of_ge hH hj; nlinarith)
  have h1 := div_le_div_of_nonneg_left (show 0 ≤ ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 *
      Real.exp (-2 * t * (sortedEigenvalues hH j - groundEnergy hH)) by positivity) hPpos hden
  have h2 : ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 *
      Real.exp (-2 * t * (sortedEigenvalues hH j - groundEnergy hH)) /
      ‖groundProjection hH ψ₀‖ ^ 2 =
      ‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 * (‖groundProjection hH ψ₀‖ ^ 2)⁻¹ *
        Real.exp (-2 * t * (sortedEigenvalues hH j - groundEnergy hH)) := by
    rw [div_eq_mul_inv]; ring
  exact h1.trans (h2.le.trans (by gcongr))

/-- **Ground-state fidelity lower bound**: for a unit initial state `ψ₀` with `f(0) > 0` and
`t ≥ 0`, `f(t) ≥ 1 / (1 + f(0)⁻¹ exp (-2 t Δ))`. -/
theorem iteFidelity_ge {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) (hP : groundProjection hH ψ₀ ≠ 0) :
    1 / (1 + (iteFidelity hH 0 ψ₀)⁻¹ * Real.exp (-2 * t * spectralGap hH)) ≤
      iteFidelity hH t ψ₀ := by
  have hψ₀_ne : ψ₀ ≠ 0 := by intro h; simp [h] at hψ₀
  rw [iteFidelity_eq_div hH t hψ₀_ne, ← excitedWeight, iteFidelity_zero hH hψ₀]
  set a := ‖groundProjection hH ψ₀‖ ^ 2
  have ha_pos : 0 < a := sq_pos_of_pos (norm_pos_iff.mpr hP)
  have hx_le2 : excitedWeight hH t ψ₀ ≤ Real.exp (-2 * t * spectralGap hH) :=
    (excited_weight_le_mul_exp hH ht hψ₀).trans (by
      have := mul_le_mul_of_nonneg_right (show 1 - a ≤ 1 by linarith)
        (Real.exp_pos (-2 * t * spectralGap hH)).le
      rwa [one_mul] at this)
  have hden_pos : 0 < 1 + a⁻¹ * Real.exp (-2 * t * spectralGap hH) := by positivity
  have hax_pos : 0 < a + excitedWeight hH t ψ₀ := by
    linarith [excitedWeight_nonneg hH t ψ₀]
  rw [div_le_div_iff₀ hden_pos hax_pos, one_mul]
  calc
    a + excitedWeight hH t ψ₀ ≤ a + Real.exp (-2 * t * spectralGap hH) := by linarith
    _ = a * (1 + a⁻¹ * Real.exp (-2 * t * spectralGap hH)) := by field_simp [ha_pos.ne']

/-- **Linear-in-`1/Δ` fidelity threshold time**: for any target fidelity `f ∈ (0, 1)`, whenever
`t ≥ 0` and `t ≥ (log f - log (1 - f) - log f(0)) / (2 Δ)` with `Δ > 0`, we have `f(t) ≥ f`. -/
theorem iteFidelity_ge_of_time_ge {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) (hP : groundProjection hH ψ₀ ≠ 0)
    (hgap : 0 < spectralGap hH) {f t : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (ht0 : 0 ≤ t)
    (ht : (Real.log f - Real.log (1 - f) - Real.log (iteFidelity hH 0 ψ₀)) /
        (2 * spectralGap hH) ≤ t) :
    f ≤ iteFidelity hH t ψ₀ := by
  refine le_trans ?_ (iteFidelity_ge hH ht0 hψ₀ hP)
  have hf0_pos : 0 < iteFidelity hH 0 ψ₀ := by
    rw [iteFidelity_zero hH hψ₀]
    exact sq_pos_of_pos (norm_pos_iff.mpr hP)
  have h1mf : 0 < 1 - f := sub_pos.mpr hf1
  have hmul : Real.log f - Real.log (1 - f) - Real.log (iteFidelity hH 0 ψ₀) ≤
      2 * t * spectralGap hH := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * spectralGap hH)).mp ht; linarith
  have hexp : Real.exp (-2 * t * spectralGap hH) ≤ iteFidelity hH 0 ψ₀ * (1 - f) / f := by
    have hle : -2 * t * spectralGap hH ≤ Real.log (iteFidelity hH 0 ψ₀ * (1 - f) / f) := by
      rw [Real.log_div (mul_pos hf0_pos h1mf).ne' hf0.ne', Real.log_mul hf0_pos.ne' h1mf.ne']
      linarith
    exact (Real.exp_le_exp.mpr hle).trans (le_of_eq (Real.exp_log (by positivity)))
  have hden : 1 + (iteFidelity hH 0 ψ₀)⁻¹ * Real.exp (-2 * t * spectralGap hH) ≤ f⁻¹ := by
    calc
      1 + (iteFidelity hH 0 ψ₀)⁻¹ * Real.exp (-2 * t * spectralGap hH)
          ≤ 1 + (iteFidelity hH 0 ψ₀)⁻¹ * (iteFidelity hH 0 ψ₀ * (1 - f) / f) := by gcongr
      _ = 1 + (1 - f) / f := by congr 1; field_simp [hf0_pos.ne', hf0.ne']
      _ = f⁻¹ := by field_simp [hf0.ne']; ring
  rw [one_div]
  have hinv := inv_anti₀ (by positivity) hden
  rwa [inv_inv] at hinv

/-- **Exact squared distance to the ground-state limit**:
`‖ψ(t) - ψ_∞‖² = 2 (1 - √f(t))`. -/
theorem iteState_dist_sq_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hP : groundProjection hH ψ₀ ≠ 0) :
    ‖iteState H t ψ₀ - ‖groundProjection hH ψ₀‖⁻¹ • groundProjection hH ψ₀‖ ^ 2 =
      2 * (1 - Real.sqrt (iteFidelity hH t ψ₀)) := by
  have hψ₀ : ψ₀ ≠ 0 := by intro h; apply hP; simp [groundProjection, h]
  set ψ := iteState H t ψ₀
  set ψinf := ‖groundProjection hH ψ₀‖⁻¹ • groundProjection hH ψ₀
  have hψ_norm : ‖ψ‖ = 1 := norm_iteState H t hψ₀
  have hψinf_norm : ‖ψinf‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hP)]
  have hinner : @inner ℂ _ _ ψ ψinf = (Real.sqrt (iteFidelity hH t ψ₀) : ℂ) := by
    have hinner_eval : @inner ℂ _ _ ψ ψinf = ∑ j ∈ Finset.univ.filter
        (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
        starRingEnd ℂ (iteCoeff hH t ψ₀ j) *
          ((‖groundProjection hH ψ₀‖⁻¹ : ℝ) • @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀) := by
      simp only [ψinf, groundProjection, Finset.smul_sum, inner_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.real_smul, smul_smul, inner_smul_right,
        mul_comm, ← inner_conj_symm ψ (sortedEigenbasis hH j)]; rfl
    rw [hinner_eval]
    have hfactor : ∀ j ∈ Finset.univ.filter
        (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
        starRingEnd ℂ (iteCoeff hH t ψ₀ j) *
            ((‖groundProjection hH ψ₀‖⁻¹ : ℝ) • @inner ℂ _ _ (sortedEigenbasis hH j) ψ₀) =
          (((Real.sqrt (∑ k : Fin (Fintype.card ι), ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
                Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH))))⁻¹ *
            ‖groundProjection hH ψ₀‖⁻¹ : ℝ) : ℂ) *
            (‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ ^ 2 : ℂ) := fun j hj ↦ by
      have heig := (sortedEigenvalues_eq_groundEnergy_iff hH j).mpr (Finset.mem_filter.mp hj).2
      rw [iteCoeff_eq hH t hψ₀ j, heig, Complex.real_smul, Complex.real_smul, map_mul,
        Complex.conj_ofReal,
        show ∀ a b c d : ℂ, a * b * (c * d) = (a * c) * (b * d) by intros; ring,
        RCLike.conj_mul, Complex.ofReal_mul]; rfl
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
    have hsum_eq : (∑ j ∈ Finset.univ.filter
        (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
        ((‖@inner ℂ _ _ (sortedEigenbasis hH j) ψ₀‖ : ℂ) ^ 2)) =
        ((‖groundProjection hH ψ₀‖ : ℂ) ^ 2) := by
      simp_rw [← Complex.ofReal_pow]
      rw [← Complex.ofReal_sum, ← norm_sq_groundProjection, Complex.ofReal_pow]
    rw [hsum_eq, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    have hPpos : 0 < ‖groundProjection hH ψ₀‖ := norm_pos_iff.mpr hP
    have hden_eq : (∑ k : Fin (Fintype.card ι), ‖@inner ℂ _ _ (sortedEigenbasis hH k) ψ₀‖ ^ 2 *
          Real.exp (-2 * t * (sortedEigenvalues hH k - groundEnergy hH))) =
        ‖groundProjection hH ψ₀‖ ^ 2 + excitedWeight hH t ψ₀ := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k : Fin (Fintype.card ι) ↦ k.val < groundMultiplicity hH), norm_sq_groundProjection,
        excitedWeight]
      exact congrArg (· + _) (Finset.sum_congr rfl fun k hk ↦ by
        simp [(sortedEigenvalues_eq_groundEnergy_iff hH k).mpr (Finset.mem_filter.mp hk).2])
    rw [iteFidelity_eq_div hH t hψ₀, ← excitedWeight, ← hden_eq, Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq hPpos.le]
    field_simp [hPpos.ne']
  rw [norm_sub_sq_real, hψ_norm, hψinf_norm, real_inner_eq_re_complex, hinner]
  simp; ring

private lemma iteFidelity_le_one {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (t : ℝ)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ψ₀ ≠ 0) : iteFidelity hH t ψ₀ ≤ 1 := by
  rw [iteFidelity]
  calc
    ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) ↦ j.val < groundMultiplicity hH),
        ‖iteCoeff hH t ψ₀ j‖ ^ 2
        ≤ ∑ j : Fin (Fintype.card ι), ‖iteCoeff hH t ψ₀ j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ sq_nonneg _
    _ = ‖iteState H t ψ₀‖ ^ 2 := (sortedEigenbasis hH).sum_sq_norm_inner_right _
    _ = 1 := by rw [norm_iteState H t hψ₀, one_pow]

/-- **Sharp state-distance convergence bound**: for unit `ψ₀` with `f(0) > 0` and `t ≥ 0`,
`‖ψ(t) - ψ_∞‖² ≤ (1 - f(0)) / f(0) * exp (-2 t Δ) ≤ f(0)⁻¹ exp (-2 t Δ)`. -/
theorem iteState_dist_sq_le_sharp {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) (hP : groundProjection hH ψ₀ ≠ 0) :
    ‖iteState H t ψ₀ - ‖groundProjection hH ψ₀‖⁻¹ • groundProjection hH ψ₀‖ ^ 2 ≤
      (1 - iteFidelity hH 0 ψ₀) / iteFidelity hH 0 ψ₀ * Real.exp (-2 * t * spectralGap hH) := by
  rw [iteState_dist_sq_eq hH t hP]
  have hψ₀_ne : ψ₀ ≠ 0 := by intro h; simp [h] at hψ₀
  have hfid_nn : 0 ≤ iteFidelity hH t ψ₀ := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hkey : 2 * (1 - Real.sqrt (iteFidelity hH t ψ₀)) ≤
      (1 - iteFidelity hH t ψ₀) / iteFidelity hH t ψ₀ := by
    have hft_pos : 0 < iteFidelity hH t ψ₀ := by
      refine lt_of_lt_of_le ?_ (iteFidelity_monotone hH hψ₀_ne ht)
      dsimp only
      rw [iteFidelity_zero hH hψ₀]
      exact sq_pos_of_pos (norm_pos_iff.mpr hP)
    rw [le_div_iff₀ hft_pos]
    set s := Real.sqrt (iteFidelity hH t ψ₀)
    have hs_sq : s ^ 2 = iteFidelity hH t ψ₀ := Real.sq_sqrt hfid_nn
    rw [← hs_sq]
    linarith [mul_nonneg (sq_nonneg (1 - s))
      (by linarith [Real.sqrt_nonneg (iteFidelity hH t ψ₀)] : 0 ≤ 2 * s + 1)]
  have hmono_x : (1 - iteFidelity hH t ψ₀) / iteFidelity hH t ψ₀ ≤
      (1 - iteFidelity hH 0 ψ₀) / iteFidelity hH 0 ψ₀ * Real.exp (-2 * t * spectralGap hH) := by
    rw [iteFidelity_eq_div hH t hψ₀_ne, ← excitedWeight, iteFidelity_zero hH hψ₀]
    set a := ‖groundProjection hH ψ₀‖ ^ 2
    have ha_pos : 0 < a := sq_pos_of_pos (norm_pos_iff.mpr hP)
    have hax_pos : 0 < a + excitedWeight hH t ψ₀ := by linarith [excitedWeight_nonneg hH t ψ₀]
    have hsimp : (1 - a / (a + excitedWeight hH t ψ₀)) / (a / (a + excitedWeight hH t ψ₀)) =
        excitedWeight hH t ψ₀ / a := by
      field_simp [ha_pos.ne', hax_pos.ne']; ring
    rw [hsimp]
    calc
      excitedWeight hH t ψ₀ / a ≤ ((1 - a) * Real.exp (-2 * t * spectralGap hH)) / a :=
        div_le_div_of_nonneg_right (excited_weight_le_mul_exp hH ht hψ₀) ha_pos.le
      _ = (1 - a) / a * Real.exp (-2 * t * spectralGap hH) := by ring
  exact hkey.trans hmono_x

/-- **Cubic-inverse-overlap state-distance bound**:
`‖ψ(t) - ψ_∞‖² ≤ f(0)⁻³ exp (-2 t Δ)` for unit `ψ₀` with `f(0) > 0` and `t ≥ 0`. -/
theorem iteState_dist_sq_le_cube {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    {ψ₀ : EuclideanSpace ℂ ι} (hψ₀ : ‖ψ₀‖ = 1) (hP : groundProjection hH ψ₀ ≠ 0) :
    ‖iteState H t ψ₀ - ‖groundProjection hH ψ₀‖⁻¹ • groundProjection hH ψ₀‖ ^ 2 ≤
      Real.exp (-2 * t * spectralGap hH) / (iteFidelity hH 0 ψ₀) ^ 3 := by
  have hψ₀_ne : ψ₀ ≠ 0 := by intro h; simp [h] at hψ₀
  have ha_pos : 0 < iteFidelity hH 0 ψ₀ := by
    rw [iteFidelity_zero hH hψ₀]; exact sq_pos_of_pos (norm_pos_iff.mpr hP)
  have ha_le_one : iteFidelity hH 0 ψ₀ ≤ 1 := iteFidelity_le_one hH 0 hψ₀_ne
  have h1 : (1 - iteFidelity hH 0 ψ₀) / iteFidelity hH 0 ψ₀ ≤ 1 / (iteFidelity hH 0 ψ₀) ^ 3 := by
    rw [div_le_div_iff₀ ha_pos (pow_pos ha_pos 3)]
    have : (iteFidelity hH 0 ψ₀) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  calc
    _ ≤ (1 - iteFidelity hH 0 ψ₀) / iteFidelity hH 0 ψ₀ * Real.exp (-2 * t * spectralGap hH) :=
      iteState_dist_sq_le_sharp hH ht hψ₀ hP
    _ ≤ (1 / (iteFidelity hH 0 ψ₀) ^ 3) * Real.exp (-2 * t * spectralGap hH) := by gcongr
    _ = Real.exp (-2 * t * spectralGap hH) / (iteFidelity hH 0 ψ₀) ^ 3 := by ring

end ConvergenceRates

section SphericalMeasure

open MeasureTheory Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Null-set property of states orthogonal to the ground eigenspace**: the set of unit vectors
`ψ ∈ sphere 0 1` with `P₀ ψ = 0` has spherical surface measure zero. -/
theorem toSphere_orth_groundSpace_eq_zero {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    (volume : Measure (EuclideanSpace ℂ ι)).toSphere
      {ψ : sphere (0 : EuclideanSpace ℂ ι) 1 | groundProjection hH (ψ : EuclideanSpace ℂ ι) = 0} =
      0 := by
  let P0 : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι :=
    { toFun := groundProjection hH
      map_add' := groundProjection_add hH
      map_smul' := fun r x ↦ by
        simp only [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
          groundProjection_smul] }
  let W : Submodule ℝ (EuclideanSpace ℂ ι) := LinearMap.ker P0
  have hW_ne_top : W ≠ ⊤ := fun htop ↦ by
    have hzero : groundProjection hH (sortedEigenbasis hH ⟨0, Fintype.card_pos⟩) = 0 :=
      show sortedEigenbasis hH ⟨0, Fintype.card_pos⟩ ∈ W from htop ▸ Submodule.mem_top
    have hinner := congrArg (fun v ↦ @inner ℂ _ _ (sortedEigenbasis hH ⟨0, Fintype.card_pos⟩) v)
      hzero
    rw [inner_sortedEigenbasis_groundProjection, ite_eq_left (groundMultiplicity_pos hH),
      inner_zero_right, inner_self_eq_norm_sq_to_K, (sortedEigenbasis hH).orthonormal.1] at hinner
    norm_num at hinner
  let s : Set (sphere (0 : EuclideanSpace ℂ ι) 1) :=
    {ψ | groundProjection hH (ψ : EuclideanSpace ℂ ι) = 0}
  have hs : MeasurableSet s :=
    ((Submodule.isClosed_of_finiteDimensional W).preimage continuous_subtype_val).measurableSet
  rw [Measure.toSphere_apply' volume hs]
  have hcone : Set.Ioo (0 : ℝ) 1 • (((↑) : sphere (0 : EuclideanSpace ℂ ι) 1 → _) '' s) ⊆
      (W : Set (EuclideanSpace ℂ ι)) := by
    rintro x ⟨r, _, y, ⟨z, hz, rfl⟩, rfl⟩; exact W.smul_mem r hz
  simp [measure_mono_null hcone (Measure.addHaar_submodule volume W hW_ne_top)]

end SphericalMeasure

end CslibFrontier.Foundations.Quantum
