/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumEntropy
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Rank
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefKernel
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantum Max-Relative Entropy, Max-Information, Naimark Dilation, and Projector Rank

This module develops foundational finite-dimensional quantum information theory over `ℂ`:

* **Max-relative entropy and max-information**: `CslibFrontier.Quantum.maxRelativeEntropy` and
  `CslibFrontier.Quantum.maxInformation`, together with
  their operational characterizations on classical–quantum states (`CslibFrontier.Quantum.cqState`).
* **Dimension and monotonicity bounds**: the cq-state domination inequalities
  `ρ_XA ≤ 1 ⊗ ρ_A` and `ρ_XA ≤ ρ_X ⊗ 1`, monotonicity of `I_max` under Kraus/CPTP channels,
  the Berta–Christandl–Renner dimension bound `I_max(A : B)_ρ ≤ 2 log₂ min(|A|, |B|)`, and the
  product-marginal bound `I_max(X : B D)_ρ ≤ 2 log₂ |D|` when `ρ_XB = ρ_X ⊗ ρ_B`.
* **Naimark dilation**: both the general `t`-outcome unitary dilation and the explicit two-outcome
  block-unitary dilation into projective measurements.
* **Frobenius norm of projectors**: `‖Π‖_F² = rank(Π)` for any orthogonal projector `Π`.

All results are proved from first principles under standard Lean axioms.

## Main definitions

* `CslibFrontier.Quantum.cqState`: classical–quantum state `∑ x, p(x) |x⟩⟨x| ⊗ ρ(x)`.
* `CslibFrontier.Quantum.maxRelativeEntropy`: `D_max(ρ ‖ σ) = inf {λ ∈ ℝ | ρ ≤ 2^λ σ}`.
* `CslibFrontier.Quantum.maxInformation`: `I_max(A : B)_ρ = inf_{σ_B} D_max(ρ_AB ‖ ρ_A ⊗ σ_B)`.
* `CslibFrontier.Quantum.frobeniusNormSq`: squared Frobenius (Hilbert–Schmidt) norm `Re Tr(Aᴴ A)`.
* `CslibFrontier.Quantum.IsKrausChannel`: finite Kraus family `{K_j}` satisfying `∑_j K_jᴴ K_j = 1`.
* `CslibFrontier.Quantum.krausApply`: CPTP action `ρ ↦ ∑_j K_j ρ K_jᴴ`.

## Main results

* `CslibFrontier.Quantum.isDensityMatrix_le_one`: every density matrix satisfies `ρ ≤ 1`.
* `CslibFrontier.Quantum.cqState_le_one_kronecker`,
  `CslibFrontier.Quantum.cqState_le_kronecker_one`:
  domination bounds for classical–quantum states.
* `CslibFrontier.Quantum.maxInformation_kraus_le`: data-processing monotonicity of `I_max`.
* `CslibFrontier.Quantum.maxInformation_cqState_le_logb_card`: `I_max(X : A)_ρ ≤ log₂ |A|`.
* `CslibFrontier.Quantum.maxInformation_le_two_mul_logb_min`:
  `I_max(A : B)_ρ ≤ 2 log₂ min(|A|, |B|)`.
* `CslibFrontier.Quantum.maxInformation_le_two_mul_logb_of_product_marginal`:
  `I_max(X : B D)_ρ ≤ 2 log₂ |D|` when `ρ_XB = ρ_X ⊗ ρ_B`.
* `CslibFrontier.Quantum.naimark_dilation`, `CslibFrontier.Quantum.naimark_two_outcome_projective`:
  Naimark's dilation theorem (general and two-outcome explicit form).
* `CslibFrontier.Quantum.frobeniusNormSq_eq_rank_of_isProjection`: `‖Π‖_F² = rank(Π)`.
-/

public section

namespace CslibFrontier.Quantum

open Matrix Finset Cslib.Quantum
open scoped MatrixOrder ComplexOrder Kronecker

/-! ### Classical–quantum states and Kraus channels -/

section Basic

variable {X ι κ : Type*}

/-- Classical–quantum state `∑ x, p(x) |x⟩⟨x| ⊗ ρ(x)` with classical register first and quantum
register second. -/
noncomputable def cqState [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    Matrix (X × ι) (X × ι) ℂ :=
  fun a b ↦ if a.1 = b.1 then ((p a.1).toReal : ℂ) * ρ a.1 a.2 b.2 else 0

theorem cqState_apply [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ)
    (a b : X × ι) :
    cqState p ρ a b = if a.1 = b.1 then ((p a.1).toReal : ℂ) * ρ a.1 a.2 b.2 else 0 := by
  unfold cqState
  rfl

theorem cqState_eq_sum [Fintype X] [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    cqState p ρ = ∑ x : X, (p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ ρ x) := by
  ext ⟨x₁, i₁⟩ ⟨x₂, i₂⟩
  simp only [cqState_apply, Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply,
    Matrix.single, Matrix.of_apply, Complex.real_smul]
  by_cases h : x₁ = x₂
  · subst h
    rw [Finset.sum_eq_single x₁]
    · simp
    · intro x _ hx
      simp [hx]
    · intro hx; exact absurd (mem_univ _) hx
  · simp only [h, ite_false]
    refine (Finset.sum_eq_zero fun x _ ↦ ?_).symm
    by_cases hx1 : x = x₁
    · subst hx1; simp [h]
    · simp [hx1]

private lemma posSemidef_single_one [Finite X] [DecidableEq X] (x : X) :
    (Matrix.single x x (1 : ℂ)).PosSemidef := by
  have : Fintype X := Fintype.ofFinite X
  have h1 : Matrix.single x x (1 : ℂ) =
      (Matrix.single x x (1 : ℂ))ᴴ * Matrix.single x x (1 : ℂ) := by
    rw [conjTranspose_single, star_one, single_mul_single_same, one_mul]
  rw [h1]
  exact posSemidef_conjTranspose_mul_self _

private lemma isDensityMatrix_uniform [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsDensityMatrix (((Fintype.card ι : ℝ)⁻¹) • (1 : Matrix ι ι ℂ)) := by
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨PosSemidef.one.smul (inv_nonneg.mpr hpos.le), ?_⟩
  rw [trace_smul, trace_one, Complex.real_smul]
  exact_mod_cast inv_mul_cancel₀ hpos.ne'

theorem cqState_posSemidef [Finite X] [DecidableEq X] (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, (ρ x).PosSemidef) :
    (cqState p ρ).PosSemidef := by
  have : Fintype X := Fintype.ofFinite X
  rw [cqState_eq_sum]
  exact posSemidef_sum _ fun x _ ↦
    ((posSemidef_single_one x).kronecker (hρ x)).smul ENNReal.toReal_nonneg

theorem isDensityMatrix_cqState [Fintype X] [DecidableEq X] [Fintype ι] (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    IsDensityMatrix (cqState p ρ) := by
  refine ⟨cqState_posSemidef p fun x ↦ (hρ x).posSemidef, ?_⟩
  rw [cqState_eq_sum, trace_sum]
  have hterm (x : X) :
      ((p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ ρ x)).trace = ((p x).toReal : ℂ) := by
    rw [trace_smul, trace_kronecker, trace_single_eq_same, (hρ x).trace_eq_one, mul_one,
      Complex.real_smul, mul_one]
  simp_rw [hterm]
  exact_mod_cast Cslib.Probability.PMF.sum_toReal p

/-- The left marginal `Tr_A(ρ_XA)` of a classical–quantum state is `∑ x, p(x) ρ(x)`. -/
theorem partialTraceLeft_cqState [Fintype X] [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    partialTraceLeft (cqState p ρ) = ∑ x : X, (p x).toReal • ρ x := by
  ext i j
  simp only [partialTraceLeft_apply, cqState_apply, ite_true, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul]

/-- The right marginal `Tr_Q(ρ_XQ)` of a classical–quantum state is `diag(p)`. -/
theorem partialTraceRight_cqState [DecidableEq X] [Fintype ι] (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    partialTraceRight (cqState p ρ) = diagonal (fun x ↦ ((p x).toReal : ℂ)) := by
  ext x y
  by_cases h : x = y
  · subst h
    simp only [partialTraceRight_apply, cqState_apply, ite_true, diagonal_apply_eq,
      ← Finset.mul_sum]
    rw [show ∑ i : ι, ρ x i i = 1 from (hρ x).trace_eq_one, mul_one]
  · simp [partialTraceRight_apply, cqState_apply, h]

/-- A finite Kraus family representing a completely positive trace-preserving (CPTP) map. -/
structure IsKrausChannel [Fintype ι] [Fintype κ] [DecidableEq ι]
    {α : Type*} (s : Finset α) (K : α → Matrix κ ι ℂ) : Prop where
  /-- Completeness relation `∑ j ∈ s, K_jᴴ K_j = 1`. -/
  sum_conjTranspose_mul : ∑ j ∈ s, (K j)ᴴ * K j = 1

/-- Action of a Kraus family `ρ ↦ ∑ j ∈ s, K_j ρ K_jᴴ`. -/
def krausApply [Fintype ι] {α : Type*} (s : Finset α) (K : α → Matrix κ ι ℂ)
    (ρ : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  ∑ j ∈ s, K j * ρ * (K j)ᴴ

theorem krausApply_posSemidef [Fintype ι] {α : Type*} (s : Finset α) (K : α → Matrix κ ι ℂ)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : (krausApply s K ρ).PosSemidef :=
  posSemidef_sum _ fun j _ ↦ hρ.mul_mul_conjTranspose_same (K j)

theorem krausApply_mono [Fintype ι] {α : Type*} (s : Finset α) (K : α → Matrix κ ι ℂ)
    {ρ σ : Matrix ι ι ℂ} (h : ρ ≤ σ) : krausApply s K ρ ≤ krausApply s K σ := by
  rw [Matrix.le_iff] at h ⊢
  rw [show krausApply s K σ - krausApply s K ρ = krausApply s K (σ - ρ) by
    simp only [krausApply, ← Finset.sum_sub_distrib, Matrix.mul_sub, Matrix.sub_mul]]
  exact krausApply_posSemidef s K h

theorem krausApply_smul [Fintype ι] {α : Type*} (s : Finset α) (K : α → Matrix κ ι ℂ)
    (c : ℝ) (ρ : Matrix ι ι ℂ) : krausApply s K (c • ρ) = c • krausApply s K ρ := by
  simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem krausApply_trace [Fintype ι] [Fintype κ] [DecidableEq ι] {α : Type*} (s : Finset α)
    (K : α → Matrix κ ι ℂ) (hK : IsKrausChannel s K) (ρ : Matrix ι ι ℂ) :
    (krausApply s K ρ).trace = ρ.trace := by
  simp only [krausApply, trace_sum]
  have hcyc (j : α) : (K j * ρ * (K j)ᴴ).trace = ((K j)ᴴ * K j * ρ).trace := by
    rw [trace_mul_cycle, Matrix.mul_assoc]
  simp_rw [hcyc, ← trace_sum, ← Finset.sum_mul, hK.sum_conjTranspose_mul, Matrix.one_mul]

theorem isDensityMatrix_krausApply [Fintype ι] [Fintype κ] [DecidableEq ι] {α : Type*}
    {s : Finset α} {K : α → Matrix κ ι ℂ} (hK : IsKrausChannel s K)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (CslibFrontier.Quantum.krausApply s K ρ) :=
  ⟨krausApply_posSemidef s K hρ.posSemidef, by rw [krausApply_trace s K hK, hρ.trace_eq_one]⟩

/-- Action of `id_X ⊗ E` on a classical–quantum state applies `E` to each conditional block. -/
theorem id_kronecker_krausApply_cqState [Fintype X] [DecidableEq X] [Fintype ι]
    {α : Type*} (s : Finset α) (K : α → Matrix κ ι ℂ) (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    krausApply s (fun j ↦ (1 : Matrix X X ℂ) ⊗ₖ K j) (cqState p ρ) =
      cqState p (fun x ↦ krausApply s K (ρ x)) := by
  rw [cqState_eq_sum, cqState_eq_sum]
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.smul_sum]; congr 1
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, kroneckerMap_apply]

private theorem isHermitian_cfc_real [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    (cfc f A).IsHermitian :=
  cfc_predicate (p := IsSelfAdjoint) f A

private theorem real_spectrum_nonneg_of_posSemidef [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : t ∈ spectrum ℝ A) : 0 ≤ t :=
  spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hA) ht

/-- Every positive semidefinite matrix is bounded in Loewner order by `Tr(A) • 1`. -/
theorem posSemidef_le_trace_smul_one [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) : A ≤ A.trace.re • (1 : Matrix ι ι ℂ) := by
  classical
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hsm : (A.trace.re • (1 : Matrix ι ι ℂ)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, isHermitian_one.eq, star_trivial]
    exact hsm.sub hA.isHermitian
  · intro v
    rw [sub_mulVec, dotProduct_sub, sub_nonneg, smul_mulVec, one_mulVec, dotProduct_smul]
    let hH := hA.isHermitian
    let U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
    let w : ι → ℂ := Uᴴ *ᵥ v
    have hUU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have hUUt : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    have hv : v = U *ᵥ w := by
      dsimp only [w]
      rw [mulVec_mulVec, hUUt, one_mulVec]
    have hdiag : star v ⬝ᵥ (A *ᵥ v) = ∑ i : ι, (hH.eigenvalues i : ℂ) * (star w i * w i) := by
      have hspec : A = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ := by
        simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, U] using
          hH.spectral_theorem
      conv_lhs => rw [hspec, hv]
      have hAv : (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ) *ᵥ (U *ᵥ w) =
          U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ w) := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one, ← mulVec_mulVec]
      rw [hAv, star_mulVec, dotProduct_mulVec, vecMul_vecMul, hUU, vecMul_one]
      simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Complex.coe_algebraMap]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hnorm : star v ⬝ᵥ v = ∑ i : ι, star w i * w i := by
      conv_lhs => rw [hv]
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hUU, vecMul_one]
      rfl
    have htr : (A.trace.re : ℂ) = ∑ i : ι, (hH.eigenvalues i : ℂ) := by
      have ht := hH.trace_eq_sum_eigenvalues
      have hre : A.trace.re = ∑ i : ι, hH.eigenvalues i := by
        simpa [Complex.re_sum] using congrArg Complex.re ht
      rw [hre, Complex.ofReal_sum]
    have heig : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
    have htr_ge (i : ι) : (hH.eigenvalues i : ℂ) ≤ (A.trace.re : ℂ) := by
      rw [htr, ← Complex.ofReal_sum]
      exact Complex.real_le_real.mpr (Finset.single_le_sum (fun j _ ↦ heig j) (mem_univ i))
    rw [hdiag, hnorm, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hww : (0 : ℂ) ≤ star w i * w i := by
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)
    exact mul_le_mul_of_nonneg_right (htr_ge i) hww

/-- Every density matrix satisfies `ρ ≤ 1`. -/
theorem isDensityMatrix_le_one [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) : ρ ≤ 1 := by
  simpa [hρ.trace_eq_one] using posSemidef_le_trace_smul_one hρ.posSemidef

/-- (part 1): for any cq-state `ρ_XA`, `ρ_XA ≤ 1_X ⊗ ρ_A`. -/
theorem cqState_le_one_kronecker [Fintype X] [DecidableEq X] [Fintype ι] (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    cqState p ρ ≤ (1 : Matrix X X ℂ) ⊗ₖ partialTraceLeft (cqState p ρ) := by
  rw [partialTraceLeft_cqState, cqState_eq_sum]
  have h1 : (1 : Matrix X X ℂ) = ∑ x : X, Matrix.single x x (1 : ℂ) := sum_single_one.symm
  rw [h1]
  have hkr : (∑ x : X, Matrix.single x x (1 : ℂ)) ⊗ₖ (∑ y : X, (p y).toReal • ρ y) =
      ∑ x : X, Matrix.single x x (1 : ℂ) ⊗ₖ (∑ y : X, (p y).toReal • ρ y) := by
    ext ⟨x₁, i₁⟩ ⟨x₂, i₂⟩
    simp [Matrix.sum_apply, Finset.sum_mul]
  rw [hkr]
  rw [Matrix.le_iff, ← Finset.sum_sub_distrib]
  refine posSemidef_sum _ fun x _ ↦ ?_
  have hdiff : (∑ y : X, (p y).toReal • ρ y) - (p x).toReal • ρ x =
      ∑ y ∈ Finset.univ.erase x, (p y).toReal • ρ y := by
    rw [← Finset.add_sum_erase _ _ (mem_univ x), add_sub_cancel_left]
  have hsub : Matrix.single x x (1 : ℂ) ⊗ₖ (∑ y : X, (p y).toReal • ρ y) -
      (p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ ρ x) =
      Matrix.single x x (1 : ℂ) ⊗ₖ ((∑ y : X, (p y).toReal • ρ y) - (p x).toReal • ρ x) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [kroneckerMap_apply, Complex.real_smul, mul_sub]; ring
  rw [hsub, hdiff]
  exact (posSemidef_single_one x).kronecker
    (posSemidef_sum _ fun y _ ↦ (hρ y).posSemidef.smul ENNReal.toReal_nonneg)

/-- (part 2): for any cq-state `ρ_XA`, `ρ_XA ≤ ρ_X ⊗ 1_A`. -/
theorem cqState_le_kronecker_one [Finite X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    cqState p ρ ≤ partialTraceRight (cqState p ρ) ⊗ₖ (1 : Matrix ι ι ℂ) := by
  have : Fintype X := Fintype.ofFinite X
  rw [partialTraceRight_cqState p hρ, cqState_eq_sum]
  have hdiag : diagonal (fun x : X ↦ ((p x).toReal : ℂ)) =
      ∑ x : X, (p x).toReal • Matrix.single x x (1 : ℂ) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [diagonal_apply_eq, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
      rw [Finset.sum_eq_single a (fun x _ hx ↦ by simp [hx]) (fun ha ↦ absurd (mem_univ _) ha)]
      simp
    · simp only [diagonal_apply_ne _ h, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
      refine (Finset.sum_eq_zero fun x _ ↦ ?_).symm
      by_cases hx : x = a
      · subst hx; simp [h]
      · simp [hx]
  rw [hdiag]
  have hkr : (∑ x : X, (p x).toReal • Matrix.single x x (1 : ℂ)) ⊗ₖ (1 : Matrix ι ι ℂ) =
      ∑ x : X, (p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ (1 : Matrix ι ι ℂ)) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply, Complex.real_smul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hkr, Matrix.le_iff, ← Finset.sum_sub_distrib]
  refine posSemidef_sum _ fun x _ ↦ ?_
  have hsub : (p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ (1 : Matrix ι ι ℂ)) -
      (p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ ρ x) =
      (p x).toReal • (Matrix.single x x (1 : ℂ) ⊗ₖ ((1 : Matrix ι ι ℂ) - ρ x)) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp [kroneckerMap_apply, Complex.real_smul]; ring
  rw [hsub]
  exact ((posSemidef_single_one x).kronecker
    (Matrix.le_iff.mp (isDensityMatrix_le_one (hρ x)))).smul ENNReal.toReal_nonneg

end Basic

/-! ### Max-relative entropy and max-information -/

section MaxInfo

variable {ι κ : Type*}

/-- Max-relative entropy `D_max(ρ ‖ σ) = inf {λ ∈ ℝ | ρ ≤ 2^λ σ}` (with value `⊤` when no finite
`λ` exists). -/
noncomputable def maxRelativeEntropy (ρ σ : Matrix ι ι ℂ) : WithTop ℝ :=
  @ite _ (∃ c : ℝ, ρ ≤ (2 : ℝ) ^ c • σ) (Classical.propDecidable _)
    ((sInf {c : ℝ | ρ ≤ (2 : ℝ) ^ c • σ} : ℝ) : WithTop ℝ) ⊤

/-- Quantum max-information `I_max(A : B)_ρ = inf_{σ_B ∈ D(H_B)} D_max(ρ_AB ‖ ρ_A ⊗ σ_B)`. -/
noncomputable def maxInformation [Fintype κ] (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    WithTop ℝ :=
  @ite _ (∃ (c : ℝ) (σ : Matrix κ κ ℂ), IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)) (Classical.propDecidable _)
    ((sInf {c : ℝ | ∃ σ : Matrix κ κ ℂ, IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)} : ℝ) : WithTop ℝ) ⊤

private theorem trace_le_of_le [Fintype ι] {A B : Matrix ι ι ℂ} (h : A ≤ B) :
    A.trace.re ≤ B.trace.re := by
  have htr := (Matrix.le_iff.mp h).trace_nonneg
  rw [trace_sub] at htr
  have hre := (Complex.nonneg_iff.mp htr).1
  rw [Complex.sub_re] at hre
  linarith

theorem maxRelativeEntropy_bddBelow [Fintype ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    BddBelow {c : ℝ | ρ ≤ (2 : ℝ) ^ c • σ} := by
  refine ⟨0, fun c hc ↦ ?_⟩
  have htr := trace_le_of_le hc
  rw [trace_smul, hρ.trace_eq_one, hσ.trace_eq_one, Complex.real_smul, mul_one,
    Complex.one_re, Complex.ofReal_re] at htr
  by_contra hlt
  push Not at hlt
  have hpow : (2 : ℝ) ^ c < 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  linarith

theorem maxRelativeEntropy_le_of_le [Fintype ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) {c : ℝ} (h : ρ ≤ (2 : ℝ) ^ c • σ) :
    maxRelativeEntropy ρ σ ≤ (c : WithTop ℝ) := by
  classical
  have hex : ∃ d : ℝ, ρ ≤ (2 : ℝ) ^ d • σ := ⟨c, h⟩
  simp only [maxRelativeEntropy, hex, ite_true, WithTop.coe_le_coe]
  exact csInf_le (maxRelativeEntropy_bddBelow hρ hσ) h

private lemma zero_mem_lowerBounds_maxInfo [Fintype ι] [Fintype κ]
    {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : IsDensityMatrix ρ) :
    (0 : ℝ) ∈ lowerBounds {c : ℝ | ∃ σ : Matrix κ κ ℂ, IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)} := by
  rintro c ⟨σ, hσ, hc⟩
  have htr := trace_le_of_le hc
  have hprod : (partialTraceRight ρ ⊗ₖ σ).trace = 1 := by
    rw [trace_kronecker, trace_partialTraceRight, hρ.trace_eq_one, hσ.trace_eq_one, mul_one]
  rw [trace_smul, hρ.trace_eq_one, hprod, Complex.real_smul, mul_one,
    Complex.one_re, Complex.ofReal_re] at htr
  by_contra hlt; push Not at hlt
  have hpow : (2 : ℝ) ^ c < 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  linarith

theorem maxInformation_bddBelow [Fintype ι] [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) :
    BddBelow {c : ℝ | ∃ σ : Matrix κ κ ℂ, IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)} :=
  ⟨0, zero_mem_lowerBounds_maxInfo hρ⟩

theorem maxInformation_le_of_le [Fintype ι] [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) {σ : Matrix κ κ ℂ} (hσ : IsDensityMatrix σ) {c : ℝ}
    (h : ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)) :
    maxInformation ρ ≤ (c : WithTop ℝ) := by
  classical
  have hex : ∃ (d : ℝ) (τ : Matrix κ κ ℂ), IsDensityMatrix τ ∧
      ρ ≤ (2 : ℝ) ^ d • (partialTraceRight ρ ⊗ₖ τ) := ⟨c, σ, hσ, h⟩
  simp only [maxInformation, hex, ite_true, WithTop.coe_le_coe]
  exact csInf_le (maxInformation_bddBelow hρ) ⟨σ, hσ, h⟩

theorem maxInformation_nonneg [Fintype ι] [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) :
    (0 : WithTop ℝ) ≤ maxInformation ρ := by
  classical
  unfold maxInformation
  split_ifs with hex
  · obtain ⟨c₀, σ₀, hσ₀, hc₀⟩ := hex
    exact WithTop.coe_le_coe.mpr (le_csInf ⟨c₀, σ₀, hσ₀, hc₀⟩ (zero_mem_lowerBounds_maxInfo hρ))
  · exact le_top

/-- If `I_max(A : B)_ρ ≤ c` for a positive semidefinite `ρ`, then for every `ε > 0` there is a
density matrix `σ` with `ρ ≤ 2^(c + ε) (ρ_A ⊗ σ)`. -/
theorem exists_le_of_maxInformation_le [Fintype κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) {c : ℝ} (h : maxInformation ρ ≤ (c : WithTop ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : Matrix κ κ ℂ, IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ (c + ε) • (partialTraceRight ρ ⊗ₖ σ) := by
  classical
  have hex : ∃ (d : ℝ) (σ : Matrix κ κ ℂ), IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ d • (partialTraceRight ρ ⊗ₖ σ) := by
    by_contra hne
    simp only [maxInformation, hne, ite_false] at h
    exact not_le_of_gt (WithTop.coe_lt_top c) h
  simp only [maxInformation, hex, ite_true, WithTop.coe_le_coe] at h
  have hlt : sInf {d : ℝ | ∃ σ : Matrix κ κ ℂ, IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ d • (partialTraceRight ρ ⊗ₖ σ)} < c + ε := by linarith
  obtain ⟨d, ⟨σ, hσ, hd⟩, hdlt⟩ := exists_lt_of_csInf_lt (by
    obtain ⟨d₀, σ₀, hσ₀, hd₀⟩ := hex; exact ⟨d₀, σ₀, hσ₀, hd₀⟩) hlt
  refine ⟨σ, hσ, hd.trans ?_⟩
  rw [Matrix.le_iff, ← sub_smul]
  have hpos : 0 ≤ (2 : ℝ) ^ (c + ε) - (2 : ℝ) ^ d :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) hdlt.le)
  exact ((posSemidef_partialTraceRight hρ).kronecker hσ.posSemidef).smul hpos

/-- (part 1): Monotonicity of `I_max` under Kraus/CPTP channels on the second register. -/
theorem maxInformation_kraus_le [Fintype ι] [Fintype κ] {κ' : Type*} [Fintype κ']
    [DecidableEq ι] [DecidableEq κ] {α : Type*} (s : Finset α) (K : α → Matrix κ' κ ℂ)
    (hK : IsKrausChannel s K) {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : IsDensityMatrix ρ) :
    maxInformation (krausApply s (fun j ↦ (1 : Matrix ι ι ℂ) ⊗ₖ K j) ρ) ≤
      maxInformation ρ := by
  classical
  set ρ' := krausApply s (fun j ↦ (1 : Matrix ι ι ℂ) ⊗ₖ K j) ρ
  have hρ' : IsDensityMatrix ρ' := by
    have hK' : IsKrausChannel s (fun j ↦ (1 : Matrix ι ι ℂ) ⊗ₖ K j) := by
      refine ⟨?_⟩
      have hsum : ∑ j ∈ s, ((1 : Matrix ι ι ℂ) ⊗ₖ K j)ᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ K j) =
          (1 : Matrix ι ι ℂ) ⊗ₖ ∑ j ∈ s, (K j)ᴴ * K j := by
        simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
        ext ⟨a, i⟩ ⟨b, j⟩
        simp [Matrix.sum_apply, Finset.mul_sum]
      rw [hsum, hK.sum_conjTranspose_mul, one_kronecker_one]
    exact isDensityMatrix_krausApply hK' hρ
  have hmarg : partialTraceRight ρ' = partialTraceRight ρ := by
    ext i i'
    simp only [ρ', krausApply, partialTraceRight_apply, Matrix.sum_apply]
    rw [Finset.sum_comm]
    have hterm (j : α) :
        ∑ k' : κ', (((1 : Matrix ι ι ℂ) ⊗ₖ K j) * ρ * ((1 : Matrix ι ι ℂ) ⊗ₖ K j)ᴴ)
          (i, k') (i', k') =
        ∑ k₁ : κ, ∑ k₂ : κ, ρ (i, k₁) (i', k₂) * ((K j)ᴴ * K j) k₂ k₁ := by
      simp only [Matrix.mul_apply, conjTranspose_kronecker, conjTranspose_one,
        kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, conjTranspose_apply]
      have hred (k' : κ') :
          ∑ x : ι, ∑ k₂ : κ,
            (∑ y : ι, ∑ k₁ : κ, (if i = y then 1 else 0) * K j k' k₁ * ρ (y, k₁) (x, k₂)) *
              ((if x = i' then 1 else 0) * star (K j k' k₂)) =
          ∑ k₂ : κ, ∑ k₁ : κ, K j k' k₁ * ρ (i, k₁) (i', k₂) * star (K j k' k₂) := by
        rw [Finset.sum_eq_single i']
        · refine Finset.sum_congr rfl fun k₂ _ ↦ ?_
          simp only [ite_true, one_mul]
          rw [Finset.sum_eq_single i]
          · simp [Finset.sum_mul]
          · intro y _ hy; simp [Ne.symm hy]
          · intro h; exact absurd (mem_univ _) h
        · intro x _ hx; refine Finset.sum_eq_zero fun k₂ _ ↦ by simp [hx]
        · intro h; exact absurd (mem_univ _) h
      simp_rw [hred]
      calc
        ∑ k' : κ', ∑ k₂ : κ, ∑ k₁ : κ, K j k' k₁ * ρ (i, k₁) (i', k₂) * star (K j k' k₂)
            = ∑ k₂ : κ, ∑ k' : κ', ∑ k₁ : κ, K j k' k₁ * ρ (i, k₁) (i', k₂) * star (K j k' k₂) :=
          Finset.sum_comm
        _ = ∑ k₂ : κ, ∑ k₁ : κ, ∑ k' : κ', K j k' k₁ * ρ (i, k₁) (i', k₂) * star (K j k' k₂) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
        _ = ∑ k₁ : κ, ∑ k₂ : κ, ∑ k' : κ', K j k' k₁ * ρ (i, k₁) (i', k₂) * star (K j k' k₂) :=
          Finset.sum_comm
        _ = ∑ k₁ : κ, ∑ k₂ : κ, ρ (i, k₁) (i', k₂) * ∑ k' : κ', star (K j k' k₂) * K j k' k₁ := by
          refine Finset.sum_congr rfl fun k₁ _ ↦ Finset.sum_congr rfl fun k₂ _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k' _ ↦ by ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have hKij (k₂ k₁ : κ) : ∑ j ∈ s, ((K j)ᴴ * K j) k₂ k₁ = (1 : Matrix κ κ ℂ) k₂ k₁ := by
      rw [← Matrix.sum_apply, hK.sum_conjTranspose_mul]
    calc
      ∑ k₁ : κ, ∑ j ∈ s, ∑ k₂ : κ, ρ (i, k₁) (i', k₂) * ((K j)ᴴ * K j) k₂ k₁
          = ∑ k₁ : κ, ∑ k₂ : κ, ρ (i, k₁) (i', k₂) * ∑ j ∈ s, ((K j)ᴴ * K j) k₂ k₁ := by
        refine Finset.sum_congr rfl fun k₁ _ ↦ ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k₂ _ ↦ (Finset.mul_sum ..).symm
      _ = ∑ k₁ : κ, ρ (i, k₁) (i', k₁) := by
        refine Finset.sum_congr rfl fun k₁ _ ↦ ?_
        simp_rw [hKij, Matrix.one_apply, mul_ite, mul_one, mul_zero]
        simp
  by_cases hex : ∃ (c : ℝ) (σ : Matrix κ κ ℂ), IsDensityMatrix σ ∧
      ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)
  · have hle_all : ∀ c ∈ {c : ℝ | ∃ σ : Matrix κ κ ℂ, IsDensityMatrix σ ∧
        ρ ≤ (2 : ℝ) ^ c • (partialTraceRight ρ ⊗ₖ σ)},
        maxInformation ρ' ≤ (c : WithTop ℝ) := by
      rintro c ⟨σ, hσ, hc⟩
      have hkr_map : krausApply s (fun j ↦ (1 : Matrix ι ι ℂ) ⊗ₖ K j)
          (partialTraceRight ρ ⊗ₖ σ) = partialTraceRight ρ ⊗ₖ krausApply s K σ := by
        simp only [krausApply]
        ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
        simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
          Matrix.one_mul, Matrix.mul_one, kroneckerMap_apply]
      have hstep : ρ' ≤ (2 : ℝ) ^ c • (partialTraceRight ρ' ⊗ₖ krausApply s K σ) := by
        rw [hmarg, ← hkr_map, ← krausApply_smul]
        exact krausApply_mono s _ hc
      exact maxInformation_le_of_le hρ' (isDensityMatrix_krausApply hK hσ) hstep
    have hex' : ∃ (c : ℝ) (σ : Matrix κ' κ' ℂ), IsDensityMatrix σ ∧
        ρ' ≤ (2 : ℝ) ^ c • (partialTraceRight ρ' ⊗ₖ σ) := by
      obtain ⟨c₀, σ₀, hσ₀, hc₀⟩ := hex
      have h1 := hle_all c₀ ⟨σ₀, hσ₀, hc₀⟩
      by_contra hne
      simp only [maxInformation, hne, ite_false] at h1
      exact not_le_of_gt (WithTop.coe_lt_top c₀) h1
    simp only [maxInformation, hex, hex', ite_true, WithTop.coe_le_coe]
    obtain ⟨c₀, σ₀, hσ₀, hc₀⟩ := hex
    refine le_csInf ⟨c₀, σ₀, hσ₀, hc₀⟩ fun c hc ↦ ?_
    have h2 := hle_all c hc
    simpa only [maxInformation, hex', ite_true, WithTop.coe_le_coe] using h2
  · simp [maxInformation, hex]

/-- (part 2): for any cq-state `ρ_XA` on a nonempty register `A`,
`I_max(X : A)_ρ ≤ log₂ |A|`.
-/
theorem maxInformation_cqState_le_logb_card {X : Type*} [Finite X] [DecidableEq X] [Fintype ι]
    [Nonempty ι] (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    maxInformation (cqState p ρ) ≤ ((Real.logb 2 (Fintype.card ι : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let u : Matrix ι ι ℂ := ((Fintype.card ι : ℝ)⁻¹) • (1 : Matrix ι ι ℂ)
  have hle : cqState p ρ ≤ (2 : ℝ) ^ (Real.logb 2 (Fintype.card ι : ℝ)) •
      (partialTraceRight (cqState p ρ) ⊗ₖ u) := by
    rw [Real.rpow_logb (by norm_num) (by norm_num) hpos,
      show (Fintype.card ι : ℝ) • (partialTraceRight (cqState p ρ) ⊗ₖ u) =
        partialTraceRight (cqState p ρ) ⊗ₖ (1 : Matrix ι ι ℂ) by
          simp only [u, kronecker_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]]
    exact cqState_le_kronecker_one p hρ
  exact maxInformation_le_of_le (isDensityMatrix_cqState p hρ) isDensityMatrix_uniform hle

/-! ### Berta–Christandl–Renner dimension bound -/

/-- Block Cauchy–Schwarz bound: every positive semidefinite bipartite matrix `ρ_AB` satisfies
`ρ_AB ≤ |B| • (ρ_A ⊗ 1_B)`. -/
theorem posSemidef_le_card_right_smul_partialTraceRight_kronecker_one
    [Finite ι] [Fintype κ] [DecidableEq κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) :
    ρ ≤ (Fintype.card κ : ℝ) • (partialTraceRight ρ ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have htr : (partialTraceRight ρ).PosSemidef := posSemidef_partialTraceRight hρ
    exact ((htr.kronecker PosSemidef.one).smul (Nat.cast_nonneg _)).isHermitian.sub
      hρ.isHermitian
  · intro v
    rw [sub_mulVec, dotProduct_sub, sub_nonneg]
    -- Write `v` in terms of slices `v_k : ι → ℂ`, `v_k i = v (i, k)`.
    let vk (k : κ) : ι → ℂ := fun i ↦ v (i, k)
    let block (k₁ k₂ : κ) : Matrix ι ι ℂ := fun i₁ i₂ ↦ ρ (i₁, k₁) (i₂, k₂)
    have hdiag_nonneg (k : κ) : 0 ≤ (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re := by
      let w : ι × κ → ℂ := fun p ↦ if p.2 = k then v p else 0
      have hw : star w ⬝ᵥ (ρ *ᵥ w) = star (vk k) ⬝ᵥ (block k k *ᵥ vk k) := by
        simp only [dotProduct, mulVec, Fintype.sum_prod_type, w, vk, block, Pi.star_apply]
        rw [Finset.sum_comm]
        rw [Finset.sum_eq_single k]
        · refine Finset.sum_congr rfl fun i₁ _ ↦ ?_
          simp only [ite_true]
          congr 1
          rw [Finset.sum_comm]
          rw [Finset.sum_eq_single k]
          · simp
          · intro k₂ _ hk₂; simp [hk₂]
          · intro hk; exact absurd (mem_univ _) hk
        · intro k₁ _ hk₁; simp [hk₁]
        · intro hk; exact absurd (mem_univ _) hk
      have h0 := (Complex.nonneg_iff.mp (hρ.dotProduct_mulVec_nonneg w)).1
      rwa [hw] at h0
    -- For any `k₁, k₂`, `(star (vk k₁) ⬝ᵥ block k₁ k₂ *ᵥ vk k₂).re ≤ √(q k₁) * √(q k₂)`.
    have hcs (k₁ k₂ : κ) :
        (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re ≤
          Real.sqrt (star (vk k₁) ⬝ᵥ (block k₁ k₁ *ᵥ vk k₁)).re *
            Real.sqrt (star (vk k₂) ⬝ᵥ (block k₂ k₂ *ᵥ vk k₂)).re := by
      -- For all `t : ℝ`, `q(v_{k₁} - t v_{k₂}) ≥ 0` on a `2×2` restriction when `k₁ ≠ k₂`.
      by_cases h12 : k₁ = k₂
      · subst h12
        rw [Real.mul_self_sqrt (hdiag_nonneg k₁)]
      · -- Evaluate quadratic form on `w(t) = t • e_{k₁} - e_{k₂}` (using `t` real).
        have hquad (t : ℝ) :
            0 ≤ t ^ 2 * (star (vk k₁) ⬝ᵥ (block k₁ k₁ *ᵥ vk k₁)).re -
              2 * t * (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re +
              (star (vk k₂) ⬝ᵥ (block k₂ k₂ *ᵥ vk k₂)).re := by
          let w : ι × κ → ℂ := fun p ↦
            if p.2 = k₁ then (t : ℂ) * v p else if p.2 = k₂ then -v p else 0
          have h0 := (Complex.nonneg_iff.mp (hρ.dotProduct_mulVec_nonneg w)).1
          have hsym : (star (vk k₂) ⬝ᵥ (block k₂ k₁ *ᵥ vk k₁)).re =
              (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re := by
            have hH := hρ.isHermitian
            have hconj : star (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)) =
                star (vk k₂) ⬝ᵥ (block k₂ k₁ *ᵥ vk k₁) := by
              simp only [dotProduct, mulVec, star_sum, star_mul, star_star, Pi.star_apply,
                Finset.mul_sum, block, vk]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i₂ _ ↦ Finset.sum_congr rfl fun i₁ _ ↦ ?_
              have hij : star (ρ (i₁, k₁) (i₂, k₂)) = ρ (i₂, k₂) (i₁, k₁) := by
                simpa [conjTranspose_apply] using congrFun (congrFun hH.eq (i₂, k₂)) (i₁, k₁)
              rw [hij]
              ring
            rw [← hconj, Complex.star_def, Complex.conj_re]
          have hexpand : star w ⬝ᵥ (ρ *ᵥ w) =
              ((t ^ 2 : ℝ) : ℂ) * (star (vk k₁) ⬝ᵥ (block k₁ k₁ *ᵥ vk k₁)) -
              (t : ℂ) * (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)) -
              (t : ℂ) * (star (vk k₂) ⬝ᵥ (block k₂ k₁ *ᵥ vk k₁)) +
              (star (vk k₂) ⬝ᵥ (block k₂ k₂ *ᵥ vk k₂)) := by
            simp only [dotProduct, mulVec, Fintype.sum_prod_type, w, vk, block, Pi.star_apply]
            have hsplit (c₁ c₂ : ℂ) :
                ∑ k : κ, (if k = k₁ then c₁ else if k = k₂ then c₂ else 0) = c₁ + c₂ := by
              rw [← Finset.add_sum_erase _ _ (mem_univ k₁)]
              simp only [ite_true]
              congr 1
              rw [Finset.sum_eq_single k₂]
              · simp [Ne.symm h12]
              · intro k hk hk2; simp [(Finset.mem_erase.mp hk).1, hk2]
              · intro hk2; exact absurd (Finset.mem_erase.mpr ⟨Ne.symm h12, mem_univ _⟩) hk2
            have hinner (i₁ : ι) (k : κ) :
                ∑ i₂ : ι, ∑ k' : κ, ρ (i₁, k) (i₂, k') *
                  (if k' = k₁ then (t : ℂ) * v (i₂, k')
                    else if k' = k₂ then -v (i₂, k') else 0) =
                (t : ℂ) * (∑ i₂ : ι, ρ (i₁, k) (i₂, k₁) * v (i₂, k₁)) -
                  (∑ i₂ : ι, ρ (i₁, k) (i₂, k₂) * v (i₂, k₂)) := by
              rw [Finset.sum_comm]
              have h1 : ∀ k', (∑ i₂ : ι, ρ (i₁, k) (i₂, k') *
                  (if k' = k₁ then (t : ℂ) * v (i₂, k')
                    else if k' = k₂ then -v (i₂, k') else 0)) =
                  if k' = k₁ then (t : ℂ) * (∑ i₂ : ι, ρ (i₁, k) (i₂, k₁) * v (i₂, k₁))
                  else if k' = k₂ then -(∑ i₂ : ι, ρ (i₁, k) (i₂, k₂) * v (i₂, k₂)) else 0 := by
                intro k'
                by_cases hk1 : k' = k₁
                · subst hk1; simp only [ite_true, Finset.mul_sum]
                  exact Finset.sum_congr rfl fun _ _ ↦ by ring
                · by_cases hk2 : k' = k₂
                  · subst hk2; simp [hk1, Finset.sum_neg_distrib]
                  · simp [hk1, hk2]
              simp_rw [h1]
              rw [hsplit, sub_eq_add_neg]
            rw [Finset.sum_comm]
            have houter : ∀ k : κ,
                (∑ i₁ : ι, star (if k = k₁ then (t : ℂ) * v (i₁, k)
                  else if k = k₂ then -v (i₁, k) else 0) *
                  ∑ i₂ : ι, ∑ k' : κ, ρ (i₁, k) (i₂, k') *
                    (if k' = k₁ then (t : ℂ) * v (i₂, k')
                      else if k' = k₂ then -v (i₂, k') else 0)) =
                if k = k₁ then
                  ((t ^ 2 : ℝ) : ℂ) * (∑ i₁, star (v (i₁, k₁)) * ∑ i₂, ρ (i₁, k₁) (i₂, k₁) * v (i₂,
                    k₁)) -
                  (t : ℂ) * (∑ i₁, star (v (i₁, k₁)) * ∑ i₂, ρ (i₁, k₁) (i₂, k₂) * v (i₂, k₂))
                else if k = k₂ then
                  -(t : ℂ) * (∑ i₁, star (v (i₁, k₂)) * ∑ i₂, ρ (i₁, k₂) (i₂, k₁) * v (i₂, k₁)) +
                  (∑ i₁, star (v (i₁, k₂)) * ∑ i₂, ρ (i₁, k₂) (i₂, k₂) * v (i₂, k₂))
                else 0 := by
              intro k
              simp_rw [hinner]
              by_cases hk1 : k = k₁
              · subst hk1
                simp only [ite_true, star_mul, Complex.star_def, Complex.conj_ofReal, mul_sub,
                  Finset.sum_sub_distrib, Complex.ofReal_pow]
                have h2 : ∑ x : ι, (starRingEnd ℂ) (v (x, k)) * (t : ℂ) *
                    ((t : ℂ) * ∑ i₂ : ι, ρ (x, k) (i₂, k) * v (i₂, k)) =
                    (t : ℂ) ^ 2 * ∑ x : ι, (starRingEnd ℂ) (v (x, k)) *
                      ∑ i₂ : ι, ρ (x, k) (i₂, k) * v (i₂, k) := by
                  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by ring
                have h3 : ∑ x : ι, (starRingEnd ℂ) (v (x, k)) * (t : ℂ) *
                    ∑ i₂ : ι, ρ (x, k) (i₂, k₂) * v (i₂, k₂) =
                    (t : ℂ) * ∑ x : ι, (starRingEnd ℂ) (v (x, k)) *
                      ∑ i₂ : ι, ρ (x, k) (i₂, k₂) * v (i₂, k₂) := by
                  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by ring
                rw [h2, h3]
              · by_cases hk2 : k = k₂
                · subst hk2
                  simp only [hk1, ite_false, ite_true, star_neg, neg_mul, mul_sub,
                    Finset.sum_add_distrib, sub_neg_eq_add, Finset.sum_neg_distrib]
                  have h4 : ∑ x : ι, (star (v (x, k)) * ((t : ℂ) *
                      ∑ i₂ : ι, ρ (x, k) (i₂, k₁) * v (i₂, k₁))) =
                      (t : ℂ) * ∑ x : ι, star (v (x, k)) *
                        ∑ i₂ : ι, ρ (x, k) (i₂, k₁) * v (i₂, k₁) := by
                    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by ring
                  rw [h4]
                · simp only [hk1, hk2, ite_false, star_zero, zero_mul, Finset.sum_const_zero]
            simp_rw [houter]
            rw [hsplit]
            ring
          rw [hexpand] at h0
          simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero] at h0
          rw [hsym] at h0
          linarith
        -- Apply discriminant inequality `b² ≤ a * c` to `a t² - 2 b t + c ≥ 0`.
        set a := (star (vk k₁) ⬝ᵥ (block k₁ k₁ *ᵥ vk k₁)).re
        set b := (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re
        set c := (star (vk k₂) ⬝ᵥ (block k₂ k₂ *ᵥ vk k₂)).re
        have ha : 0 ≤ a := hdiag_nonneg k₁
        have hc : 0 ≤ c := hdiag_nonneg k₂
        have hb_sq : b ^ 2 ≤ a * c := by
          by_cases ha0 : a = 0
          · have hlin : ∀ t : ℝ, 0 ≤ -2 * t * b + c := by
              intro t; have := hquad t; rw [ha0] at this; linarith
            have hb0 : b = 0 := by
              by_contra hbne
              have h1 := hlin ((c + 1) / (2 * b))
              have h2 : -2 * ((c + 1) / (2 * b)) * b + c = -1 := by field_simp; ring
              linarith
            simp [ha0, hb0]
          · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hmin := hquad (b / a)
            have hsimp : (b / a) ^ 2 * a - 2 * (b / a) * b + c = c - b ^ 2 / a := by
              field_simp; ring
            rw [hsimp] at hmin
            have hle : b ^ 2 / a ≤ c := by linarith
            exact (div_le_iff₀ hap).mp hle |>.trans_eq (mul_comm c a)
        calc
          b ≤ |b| := le_abs_self b
          _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
          _ ≤ Real.sqrt (a * c) := Real.sqrt_le_sqrt hb_sq
          _ = Real.sqrt a * Real.sqrt c := Real.sqrt_mul ha c
    -- Now compare real parts of the quadratic forms.
    have hLHS : (star v ⬝ᵥ (ρ *ᵥ v)).re =
        ∑ k₁ : κ, ∑ k₂ : κ, (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re := by
      simp only [dotProduct, mulVec, Fintype.sum_prod_type, Complex.re_sum, vk, block,
        Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k₁ _ ↦ ?_
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k₂ _ ↦ ?_
      rw [Finset.sum_comm]
      simp
    have hRHS_expand :
        (star v ⬝ᵥ (((Fintype.card κ : ℝ) • (partialTraceRight ρ ⊗ₖ (1 : Matrix κ κ ℂ))) *ᵥ v)).re =
          (Fintype.card κ : ℝ) * ∑ k : κ, ∑ k' : κ,
            (star (vk k) ⬝ᵥ (block k' k' *ᵥ vk k)).re := by
      simp only [smul_mulVec, dotProduct_smul, Complex.real_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      congr 1
      simp only [dotProduct, mulVec, Fintype.sum_prod_type, kroneckerMap_apply,
        partialTraceRight_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
        ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true, Complex.re_sum,
        vk, block, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
      calc
        ∑ i₁ : ι, ∑ k : κ, ∑ i₂ : ι, ∑ k' : κ,
            (star (v (i₁, k)) * (ρ (i₁, k') (i₂, k') * v (i₂, k))).re
            = ∑ k : κ, ∑ i₁ : ι, ∑ i₂ : ι, ∑ k' : κ,
              (star (v (i₁, k)) * (ρ (i₁, k') (i₂, k') * v (i₂, k))).re := Finset.sum_comm
        _ = ∑ k : κ, ∑ k' : κ, ∑ i₁ : ι, ∑ i₂ : ι,
              (star (v (i₁, k)) * (ρ (i₁, k') (i₂, k') * v (i₂, k))).re := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          calc
            ∑ i₁ : ι, ∑ i₂ : ι, ∑ k' : κ, (star (v (i₁, k)) * (ρ (i₁, k') (i₂, k') * v (i₂, k))).re
                = ∑ i₁ : ι, ∑ k' : κ, ∑ i₂ : ι,
                  (star (v (i₁, k)) * (ρ (i₁, k') (i₂, k') * v (i₂, k))).re :=
              Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
            _ = ∑ k' : κ, ∑ i₁ : ι, ∑ i₂ : ι,
                  (star (v (i₁, k)) * (ρ (i₁, k') (i₂, k') * v (i₂, k))).re := Finset.sum_comm
    have hstep1 :
        ∑ k₁ : κ, ∑ k₂ : κ, (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re ≤
          (Fintype.card κ : ℝ) * ∑ k : κ, (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re := by
      calc
        ∑ k₁ : κ, ∑ k₂ : κ, (star (vk k₁) ⬝ᵥ (block k₁ k₂ *ᵥ vk k₂)).re
            ≤ ∑ k₁ : κ, ∑ k₂ : κ,
              Real.sqrt (star (vk k₁) ⬝ᵥ (block k₁ k₁ *ᵥ vk k₁)).re *
                Real.sqrt (star (vk k₂) ⬝ᵥ (block k₂ k₂ *ᵥ vk k₂)).re :=
          Finset.sum_le_sum fun k₁ _ ↦ Finset.sum_le_sum fun k₂ _ ↦ hcs k₁ k₂
        _ = (∑ k : κ, Real.sqrt (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
        _ ≤ (Fintype.card κ : ℝ) *
              ∑ k : κ, (Real.sqrt (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re) ^ 2 := by
          have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun k : κ ↦ Real.sqrt (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re)
          simpa only [Finset.card_univ] using hsq
        _ = (Fintype.card κ : ℝ) * ∑ k : κ, (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re := by
          congr 1
          refine Finset.sum_congr rfl fun k _ ↦ Real.sq_sqrt (hdiag_nonneg k)
    have hstep2 :
        ∑ k : κ, (star (vk k) ⬝ᵥ (block k k *ᵥ vk k)).re ≤
          ∑ k : κ, ∑ k' : κ, (star (vk k) ⬝ᵥ (block k' k' *ᵥ vk k)).re := by
      refine Finset.sum_le_sum fun k _ ↦ ?_
      refine Finset.single_le_sum (f := fun k' : κ ↦ (star (vk k) ⬝ᵥ (block k' k' *ᵥ vk k)).re)
        (fun k' _ ↦ ?_) (mem_univ k)
      let w : ι × κ → ℂ := fun p ↦ if p.2 = k' then vk k p.1 else 0
      have hw : star w ⬝ᵥ (ρ *ᵥ w) = star (vk k) ⬝ᵥ (block k' k' *ᵥ vk k) := by
        simp only [dotProduct, mulVec, Fintype.sum_prod_type, w, vk, block, Pi.star_apply]
        rw [Finset.sum_comm, Finset.sum_eq_single k']
        · refine Finset.sum_congr rfl fun i₁ _ ↦ ?_
          simp only [ite_true]; congr 1
          rw [Finset.sum_comm, Finset.sum_eq_single k']
          · simp
          · intro k₂ _ hk₂; simp [hk₂]
          · intro hk; exact absurd (mem_univ _) hk
        · intro k₁ _ hk₁; simp [hk₁]
        · intro hk; exact absurd (mem_univ _) hk
      have h0 := (Complex.nonneg_iff.mp (hρ.dotProduct_mulVec_nonneg w)).1
      rwa [hw] at h0
    have hreal : (star v ⬝ᵥ (ρ *ᵥ v)).re ≤
        (star v ⬝ᵥ (((Fintype.card κ : ℝ) •
          (partialTraceRight ρ ⊗ₖ (1 : Matrix κ κ ℂ))) *ᵥ v)).re := by
      rw [hLHS, hRHS_expand]
      exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (Nat.cast_nonneg _))
    have hL0 := hρ.dotProduct_mulVec_nonneg v
    have hR0 := (((posSemidef_partialTraceRight hρ).kronecker PosSemidef.one).smul
      (Nat.cast_nonneg (α := ℝ) (Fintype.card κ))).dotProduct_mulVec_nonneg v
    rw [Complex.le_def]
    exact ⟨hreal, by rw [← (Complex.nonneg_iff.mp hL0).2, ← (Complex.nonneg_iff.mp hR0).2]⟩

/-- Symmetric block Cauchy–Schwarz bound: `ρ_AB ≤ |A| • (1_A ⊗ ρ_B)`. -/
theorem posSemidef_le_card_left_smul_one_kronecker_partialTraceLeft
    [Fintype ι] [DecidableEq ι] [Finite κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) :
    ρ ≤ (Fintype.card ι : ℝ) • ((1 : Matrix ι ι ℂ) ⊗ₖ partialTraceLeft ρ) := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  let e : ι × κ ≃ κ × ι := Equiv.prodComm ι κ
  let ρ' : Matrix (κ × ι) (κ × ι) ℂ := reindex e e ρ
  have hρ' : ρ'.PosSemidef := hρ.submatrix e.symm
  have hbound := posSemidef_le_card_right_smul_partialTraceRight_kronecker_one hρ'
  have hsub := Matrix.le_iff.mp hbound
  have hback : (reindex e.symm e.symm
      ((Fintype.card ι : ℝ) • (partialTraceRight ρ' ⊗ₖ (1 : Matrix ι ι ℂ)) - ρ')).PosSemidef :=
    hsub.submatrix e
  rw [Matrix.le_iff]
  convert hback using 1
  ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
  simp [ρ', e, reindex_apply, submatrix_apply, partialTraceRight_apply, partialTraceLeft_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_comm]

/-- First half of Berta–Christandl–Renner : `I_max(A : B)_ρ ≤ 2 log₂ |B|`. -/
theorem maxInformation_le_two_mul_logb_card_right [Fintype ι] [Fintype κ]
    [Nonempty κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : IsDensityMatrix ρ) :
    maxInformation ρ ≤ ((2 * Real.logb 2 (Fintype.card κ : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card κ : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let u : Matrix κ κ ℂ := ((Fintype.card κ : ℝ)⁻¹) • (1 : Matrix κ κ ℂ)
  have hpow : (2 : ℝ) ^ (2 * Real.logb 2 (Fintype.card κ : ℝ)) = (Fintype.card κ : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hpos,
      Real.rpow_two]
  have hle : ρ ≤ (2 : ℝ) ^ (2 * Real.logb 2 (Fintype.card κ : ℝ)) •
      (partialTraceRight ρ ⊗ₖ u) := by
    rw [hpow, sq]
    have hsm : ((Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)) • (partialTraceRight ρ ⊗ₖ u) =
        (Fintype.card κ : ℝ) • (partialTraceRight ρ ⊗ₖ (1 : Matrix κ κ ℂ)) := by
      simp only [u, kronecker_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
    rw [hsm]
    exact posSemidef_le_card_right_smul_partialTraceRight_kronecker_one hρ.posSemidef
  exact maxInformation_le_of_le hρ isDensityMatrix_uniform hle

/-- Second half of Berta–Christandl–Renner : `I_max(A : B)_ρ ≤ 2 log₂ |A|`. -/
theorem maxInformation_le_two_mul_logb_card_left [Fintype ι] [Fintype κ]
    [Nonempty ι] {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : IsDensityMatrix ρ) :
    maxInformation ρ ≤ ((2 * Real.logb 2 (Fintype.card ι : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  set ρA := partialTraceRight ρ
  have hρA : IsDensityMatrix ρA := hρ.partialTraceRight
  have hposA : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  -- Pseudoinverse square root `A^{-1/2}` and `A^{1/2}` via continuous functional calculus.
  let fInvSqrt : ℝ → ℝ := fun t ↦ if t = 0 then 0 else (Real.sqrt t)⁻¹
  let R : Matrix ι ι ℂ := cfc fInvSqrt ρA
  let S : Matrix ι ι ℂ := cfc Real.sqrt ρA
  have hR_herm : R.IsHermitian := isHermitian_cfc_real ρA fInvSqrt
  have hS_herm : S.IsHermitian := isHermitian_cfc_real ρA Real.sqrt
  -- Support projector `P = S * R = R * S` satisfies `P * ρA * P = ρA` and `R * ρA * R = P`.
  have hRS : R * S = cfc (fun t : ℝ ↦ if t = 0 then 0 else 1) ρA := by
    have hmul := (cfc_mul fInvSqrt Real.sqrt ρA
      ((ρA.finite_real_spectrum).continuousOn _)
      ((ρA.finite_real_spectrum).continuousOn _)).symm
    refine hmul.trans (cfc_congr fun t ht ↦ ?_)
    have htnn : 0 ≤ t := real_spectrum_nonneg_of_posSemidef hρA.posSemidef ht
    by_cases h0 : t = 0
    · simp [fInvSqrt, h0]
    · have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne htnn (Ne.symm h0))).ne'
      simp [fInvSqrt, h0, inv_mul_cancel₀ hsq]
  have hSR : S * R = R * S := by
    have hmul := (cfc_mul Real.sqrt fInvSqrt ρA
      ((ρA.finite_real_spectrum).continuousOn _)
      ((ρA.finite_real_spectrum).continuousOn _)).symm
    rw [hRS]
    refine hmul.trans (cfc_congr fun t ht ↦ ?_)
    have htnn : 0 ≤ t := real_spectrum_nonneg_of_posSemidef hρA.posSemidef ht
    by_cases h0 : t = 0
    · simp [fInvSqrt, h0]
    · have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne htnn (Ne.symm h0))).ne'
      simp [fInvSqrt, h0, mul_inv_cancel₀ hsq]
  have hSS : S * S = ρA := by
    have hmul := (cfc_mul Real.sqrt Real.sqrt ρA
      ((ρA.finite_real_spectrum).continuousOn _)
      ((ρA.finite_real_spectrum).continuousOn _)).symm
    refine hmul.trans ?_
    calc
      cfc (fun t ↦ Real.sqrt t * Real.sqrt t) ρA = cfc id ρA :=
        cfc_congr fun t ht ↦
          Real.mul_self_sqrt (real_spectrum_nonneg_of_posSemidef hρA.posSemidef ht)
      _ = ρA := cfc_id ℝ ρA hρA.posSemidef.isHermitian.isSelfAdjoint
  have hP_le_one : R * S ≤ 1 := by
    rw [hRS, Matrix.le_iff]
    have h1 : (1 : Matrix ι ι ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) ρA := by
      simpa using (cfc_const (p := IsSelfAdjoint) (1 : ℝ) ρA hρA.posSemidef.isHermitian).symm
    rw [h1, ← cfc_sub (fun _ ↦ 1) (fun t ↦ if t = 0 then 0 else 1) ρA
      ((ρA.finite_real_spectrum).continuousOn _) ((ρA.finite_real_spectrum).continuousOn _)]
    refine Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun t _ ↦ ?_)
    split_ifs <;> norm_num
  have hP_psd : (R * S).PosSemidef := by
    rw [hRS]
    refine Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun t _ ↦ ?_)
    split_ifs <;> norm_num
  have hR_rho_R : R * ρA * R = R * S := by
    calc
      R * ρA * R = R * (S * S) * R := by rw [hSS]
      _ = (R * S) * (S * R) := by simp only [Matrix.mul_assoc]
      _ = (R * S) * (R * S) := by rw [hSR]
      _ = R * S := by
        rw [hRS, ← cfc_mul _ _ ρA
          ((ρA.finite_real_spectrum).continuousOn _) ((ρA.finite_real_spectrum).continuousOn _)]
        exact cfc_congr fun t _ ↦ by split_ifs <;> norm_num
  -- `M = (R ⊗ 1) ρ (R ⊗ 1)` satisfies `Tr_B(M) = R ρA R = P ≤ 1`, so `Tr(M) ≤ |A|`.
  let M : Matrix (ι × κ) (ι × κ) ℂ := (R ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (R ⊗ₖ (1 : Matrix κ κ ℂ))
  have hM_psd : M.PosSemidef := by
    have hRh : (R ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ = R ⊗ₖ (1 : Matrix κ κ ℂ) := by
      rw [conjTranspose_kronecker, conjTranspose_one, hR_herm.eq]
    simpa only [M, hRh] using hρ.posSemidef.mul_mul_conjTranspose_same (R ⊗ₖ (1 : Matrix κ κ ℂ))
  have hM_right : partialTraceRight M = R * S := by
    have hstep : partialTraceRight M = R * ρA * R := by
      ext i i'
      simp only [M, partialTraceRight_apply, Matrix.mul_apply, kroneckerMap_apply,
        Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
        ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, ite_true, ρA]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j₁ _ ↦ ?_
      rw [Finset.sum_comm]
    rw [hstep, hR_rho_R]
  have hM_bound := posSemidef_le_card_left_smul_one_kronecker_partialTraceLeft hM_psd
  have htrM : M.trace = (R * S).trace := by
    rw [← trace_partialTraceRight M, hM_right]
  have htr_pos : 0 < (R * S).trace.re := by
    have hle_tr : (1 : ℝ) ≤ (R * S).trace.re := by
      have h1 : (R * S).trace = ∑ i : ι, ((if hρA.posSemidef.isHermitian.eigenvalues i = 0
          then (0 : ℝ) else 1) : ℂ) := by
        rw [hRS, hρA.posSemidef.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, trace_conjStarAlgAut,
          trace_diagonal]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [Function.comp_apply, Complex.coe_algebraMap]
        split_ifs <;> simp
      have hre : (R * S).trace.re = ∑ i : ι, if hρA.posSemidef.isHermitian.eigenvalues i = 0
          then (0 : ℝ) else 1 := by
        rw [congrArg Complex.re h1, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs <;> simp
      rw [hre]
      have hex_pos : ∃ i : ι, hρA.posSemidef.isHermitian.eigenvalues i ≠ 0 := by
        by_contra hall
        push Not at hall
        have ht := hρA.posSemidef.isHermitian.trace_eq_sum_eigenvalues
        simp only [hall, RCLike.ofReal_zero, Finset.sum_const_zero] at ht
        rw [hρA.trace_eq_one] at ht
        exact one_ne_zero ht
      obtain ⟨i₀, hi₀⟩ := hex_pos
      have hge := Finset.single_le_sum (f := fun i : ι ↦
        if hρA.posSemidef.isHermitian.eigenvalues i = 0 then (0 : ℝ) else 1)
        (fun i _ ↦ by split_ifs <;> norm_num) (mem_univ i₀)
      simpa only [hi₀, ite_false] using hge
    linarith
  have htr_le : (R * S).trace.re ≤ (Fintype.card ι : ℝ) := by
    have h1 := trace_le_of_le hP_le_one
    simpa only [trace_one, Complex.natCast_re] using h1
  let τ : Matrix κ κ ℂ := partialTraceLeft M
  have hτ_psd : τ.PosSemidef := posSemidef_partialTraceLeft hM_psd
  have hτ_tr : τ.trace.re = (R * S).trace.re := by
    rw [trace_partialTraceLeft, htrM]
  let σ : Matrix κ κ ℂ := (τ.trace.re)⁻¹ • τ
  have hσ : IsDensityMatrix σ := by
    refine ⟨hτ_psd.smul (inv_nonneg.mpr (hτ_tr.symm ▸ htr_pos.le)), ?_⟩
    rw [trace_smul, Complex.real_smul]
    have htr_real : τ.trace = (τ.trace.re : ℂ) :=
      Complex.ext rfl (Complex.nonneg_iff.mp hτ_psd.trace_nonneg).2.symm
    have hne : τ.trace.re ≠ 0 := hτ_tr.symm ▸ htr_pos.ne'
    calc
      (((τ.trace.re)⁻¹ : ℝ) : ℂ) * τ.trace
          = (((τ.trace.re)⁻¹ : ℝ) : ℂ) * (τ.trace.re : ℂ) :=
        congrArg ((((τ.trace.re)⁻¹ : ℝ) : ℂ) * ·) htr_real
      _ = (((τ.trace.re)⁻¹ * τ.trace.re : ℝ) : ℂ) := (Complex.ofReal_mul _ _).symm
      _ = 1 := by rw [inv_mul_cancel₀ hne, Complex.ofReal_one]
  -- Conjugate `M ≤ |A| • (1 ⊗ τ) = (|A| * Tr(τ)) • (1 ⊗ σ) ≤ |A|^2 • (1 ⊗ σ)` by `S ⊗ 1`.
  have hM_le_sq : M ≤ ((Fintype.card ι : ℝ) ^ 2) • ((1 : Matrix ι ι ℂ) ⊗ₖ σ) := by
    refine hM_bound.trans ?_
    have heq : (Fintype.card ι : ℝ) • ((1 : Matrix ι ι ℂ) ⊗ₖ τ) =
        ((Fintype.card ι : ℝ) * τ.trace.re) • ((1 : Matrix ι ι ℂ) ⊗ₖ σ) := by
      simp only [σ, kronecker_smul, smul_smul, mul_assoc,
        mul_inv_cancel₀ (hτ_tr.symm ▸ htr_pos.ne'), mul_one]
    rw [heq, Matrix.le_iff, ← sub_smul]
    have hcoef : 0 ≤ (Fintype.card ι : ℝ) ^ 2 - (Fintype.card ι : ℝ) * τ.trace.re := by
      rw [sq, ← mul_sub]
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hτ_tr.symm ▸ htr_le))
    exact (PosSemidef.one.kronecker hσ.posSemidef).smul hcoef
  -- Now conjugate by `S ⊗ 1`: `(S ⊗ 1) M (S ⊗ 1) = ρ` (using `S * R = P` and `SupportLE ρ (ρA ⊗
  -- 1)`!).
  have hS_conj : (S ⊗ₖ (1 : Matrix κ κ ℂ)) * M * (S ⊗ₖ (1 : Matrix κ κ ℂ)) = ρ := by
    have hP_kr : ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ = ρ := by
      -- Prove `(1 - P) ⊗ 1` annihilates `ρ` because `Tr_B(ρ) = ρA` and `(1 - P) ρA = 0`.
      have hQ_psd : ((1 : Matrix ι ι ℂ) - R * S).PosSemidef := Matrix.le_iff.mp hP_le_one
      have hQ_rhoA : ((1 : Matrix ι ι ℂ) - R * S) * ρA = 0 := by
        rw [sub_mul, Matrix.one_mul, ← hSS]
        have hPR : R * S * S = S := by
          rw [hRS, ← cfc_mul _ _ ρA
            ((ρA.finite_real_spectrum).continuousOn _) ((ρA.finite_real_spectrum).continuousOn _)]
          exact cfc_congr fun t _ ↦ by
            by_cases h0 : t = 0
            · simp [h0]
            · simp [h0]
        rw [← Matrix.mul_assoc, hPR, sub_self]
      have htr0 : ((((1 : Matrix ι ι ℂ) - R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ).trace = 0 := by
        rw [← trace_partialTraceRight]
        have hpt : partialTraceRight ((((1 : Matrix ι ι ℂ) - R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ) =
            ((1 : Matrix ι ι ℂ) - R * S) * ρA := by
          ext i i'
          simp only [partialTraceRight_apply, Matrix.mul_apply, kroneckerMap_apply,
            Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
            ρA, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
        rw [hpt, hQ_rhoA, trace_zero]
      have hzero : (((1 : Matrix ι ι ℂ) - R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ = 0 :=
        ((hQ_psd.kronecker PosSemidef.one).trace_mul_eq_zero_iff hρ.posSemidef).mp htr0
      have hsub_kr : (((1 : Matrix ι ι ℂ) - R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ =
          ρ - ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ := by
        have hsub1 : ((1 : Matrix ι ι ℂ) - R * S) ⊗ₖ (1 : Matrix κ κ ℂ) =
            (1 : Matrix (ι × κ) (ι × κ) ℂ) - (R * S) ⊗ₖ (1 : Matrix κ κ ℂ) := by
          ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
          simp only [Matrix.sub_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
          split_ifs <;> simp_all
        rw [hsub1, sub_mul, Matrix.one_mul]
      rw [hsub_kr, sub_eq_zero] at hzero
      exact hzero.symm
    have hP_kr_right : ρ * ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) = ρ := by
      have h1 := congrArg Matrix.conjTranspose hP_kr
      rw [conjTranspose_mul, hρ.posSemidef.isHermitian.eq, conjTranspose_kronecker,
        conjTranspose_one, hP_psd.isHermitian.eq] at h1
      exact h1
    calc
      (S ⊗ₖ (1 : Matrix κ κ ℂ)) * M * (S ⊗ₖ (1 : Matrix κ κ ℂ))
          = ((S * R) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) := by
        dsimp only [M]
        calc
          (S ⊗ₖ (1 : Matrix κ κ ℂ)) *
              ((R ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (R ⊗ₖ (1 : Matrix κ κ ℂ))) *
              (S ⊗ₖ (1 : Matrix κ κ ℂ))
              = ((S ⊗ₖ (1 : Matrix κ κ ℂ)) * (R ⊗ₖ (1 : Matrix κ κ ℂ))) * ρ *
                ((R ⊗ₖ (1 : Matrix κ κ ℂ)) * (S ⊗ₖ (1 : Matrix κ κ ℂ))) := by
            simp only [Matrix.mul_assoc]
          _ = ((S * R) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) := by
            rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul]
      _ = ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * ((R * S) ⊗ₖ (1 : Matrix κ κ ℂ)) := by rw [hSR]
      _ = ρ := by rw [hP_kr, hP_kr_right]
  have hfinal : ρ ≤ ((Fintype.card ι : ℝ) ^ 2) • (ρA ⊗ₖ σ) := by
    have hSh : (S ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ = S ⊗ₖ (1 : Matrix κ κ ℂ) := by
      rw [conjTranspose_kronecker, conjTranspose_one, hS_herm.eq]
    have hconj_le : (S ⊗ₖ (1 : Matrix κ κ ℂ)) * M * (S ⊗ₖ (1 : Matrix κ κ ℂ)) ≤
        (S ⊗ₖ (1 : Matrix κ κ ℂ)) *
          (((Fintype.card ι : ℝ) ^ 2) • ((1 : Matrix ι ι ℂ) ⊗ₖ σ)) *
          (S ⊗ₖ (1 : Matrix κ κ ℂ)) := by
      rw [Matrix.le_iff] at hM_le_sq ⊢
      have hmul : (S ⊗ₖ (1 : Matrix κ κ ℂ)) *
            (((Fintype.card ι : ℝ) ^ 2) • ((1 : Matrix ι ι ℂ) ⊗ₖ σ) - M) *
            (S ⊗ₖ (1 : Matrix κ κ ℂ)) =
          (S ⊗ₖ (1 : Matrix κ κ ℂ)) *
            (((Fintype.card ι : ℝ) ^ 2) • ((1 : Matrix ι ι ℂ) ⊗ₖ σ)) *
            (S ⊗ₖ (1 : Matrix κ κ ℂ)) -
          (S ⊗ₖ (1 : Matrix κ κ ℂ)) * M * (S ⊗ₖ (1 : Matrix κ κ ℂ)) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [← hmul]
      simpa only [hSh] using hM_le_sq.mul_mul_conjTranspose_same (S ⊗ₖ (1 : Matrix κ κ ℂ))
    rw [hS_conj] at hconj_le
    have hrhs : (S ⊗ₖ (1 : Matrix κ κ ℂ)) *
          (((Fintype.card ι : ℝ) ^ 2) • ((1 : Matrix ι ι ℂ) ⊗ₖ σ)) *
          (S ⊗ₖ (1 : Matrix κ κ ℂ)) =
        ((Fintype.card ι : ℝ) ^ 2) • (ρA ⊗ₖ σ) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, ← mul_kronecker_mul, Matrix.mul_one,
        Matrix.one_mul, hSS]
    rwa [hrhs] at hconj_le
  have hpow : (2 : ℝ) ^ (2 * Real.logb 2 (Fintype.card ι : ℝ)) = (Fintype.card ι : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hposA,
      Real.rpow_two]
  rw [← hpow] at hfinal
  exact maxInformation_le_of_le hρ hσ hfinal

/-- : for any bipartite density matrix `ρ_AB`,
`I_max(A : B)_ρ ≤ 2 log₂ min(|A|, |B|)`.
-/
theorem maxInformation_le_two_mul_logb_min [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : IsDensityMatrix ρ) :
    maxInformation ρ ≤
      ((2 * Real.logb 2 (min (Fintype.card ι) (Fintype.card κ) : ℝ) : ℝ) : WithTop ℝ) := by
  rcases le_total (Fintype.card ι) (Fintype.card κ) with h | h
  · rw [min_eq_left (Nat.cast_le.mpr h)]
    exact maxInformation_le_two_mul_logb_card_left hρ
  · rw [min_eq_right (Nat.cast_le.mpr h)]
    exact maxInformation_le_two_mul_logb_card_right hρ

/-- : if `ρ_XBD` is a density matrix on `X × (B × D)` whose `X × B` marginal is a product
state `ρ_X ⊗ ρ_B`, then `I_max(X : B D)_ρ ≤ 2 log₂ |D|`.
-/
theorem maxInformation_le_two_mul_logb_of_product_marginal {X B D : Type*}
    [Fintype X] [Fintype B] [Fintype D] [Nonempty D]
    {ρ : Matrix (X × B × D) (X × B × D) ℂ} (hρ : IsDensityMatrix ρ)
    (hprod : partialTraceRight (reindex (Equiv.prodAssoc X B D).symm
        (Equiv.prodAssoc X B D).symm ρ) =
      partialTraceRight ρ ⊗ₖ partialTraceLeft
        (partialTraceRight (reindex (Equiv.prodAssoc X B D).symm
          (Equiv.prodAssoc X B D).symm ρ))) :
    maxInformation ρ ≤ ((2 * Real.logb 2 (Fintype.card D : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  let e := (Equiv.prodAssoc X B D).symm
  let ρ' : Matrix ((X × B) × D) ((X × B) × D) ℂ := reindex e e ρ
  have hρ' : IsDensityMatrix ρ' := by
    refine ⟨hρ.posSemidef.submatrix e.symm, ?_⟩
    simpa only [ρ', trace, diag_apply, reindex_apply, submatrix_apply] using
      (e.symm.sum_comp (fun p : X × B × D ↦ ρ p p)).trans hρ.trace_eq_one
  have hposD : (0 : ℝ) < (Fintype.card D : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let uD : Matrix D D ℂ := ((Fintype.card D : ℝ)⁻¹) • (1 : Matrix D D ℂ)
  have hρB : IsDensityMatrix (partialTraceLeft (partialTraceRight ρ')) :=
    hρ'.partialTraceRight.partialTraceLeft
  let σBD : Matrix (B × D) (B × D) ℂ := partialTraceLeft (partialTraceRight ρ') ⊗ₖ uD
  have hσBD : IsDensityMatrix σBD := by
    refine ⟨hρB.posSemidef.kronecker isDensityMatrix_uniform.posSemidef, ?_⟩
    rw [trace_kronecker, hρB.trace_eq_one, isDensityMatrix_uniform.trace_eq_one, mul_one]
  have hle' : ρ' ≤ ((Fintype.card D : ℝ) ^ 2) • (partialTraceRight ρ' ⊗ₖ uD) := by
    rw [sq]
    have hsm : ((Fintype.card D : ℝ) * (Fintype.card D : ℝ)) • (partialTraceRight ρ' ⊗ₖ uD) =
        (Fintype.card D : ℝ) • (partialTraceRight ρ' ⊗ₖ (1 : Matrix D D ℂ)) := by
      simp only [uD, kronecker_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hposD.ne', mul_one]
    rw [hsm]
    exact posSemidef_le_card_right_smul_partialTraceRight_kronecker_one hρ'.posSemidef
  have hle_re : ρ ≤ ((Fintype.card D : ℝ) ^ 2) • (partialTraceRight ρ ⊗ₖ σBD) := by
    have hsub := (Matrix.le_iff.mp hle').submatrix e
    rw [Matrix.le_iff]
    convert hsub using 1
    ext ⟨x₁, b₁, d₁⟩ ⟨x₂, b₂, d₂⟩
    have h1 := congrFun (congrFun hprod (x₁, b₁)) (x₂, b₂)
    simp only [ρ', σBD, e, reindex_apply, submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      kroneckerMap_apply, Equiv.prodAssoc_symm_apply] at h1 ⊢
    rw [h1]
    simp only [Equiv.symm_symm, Equiv.prodAssoc_apply, Complex.real_smul]
    ring
  have hpow : (2 : ℝ) ^ (2 * Real.logb 2 (Fintype.card D : ℝ)) = (Fintype.card D : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hposD,
      Real.rpow_two]
  rw [← hpow] at hle_re
  exact maxInformation_le_of_le hρ hσBD hle_re

end MaxInfo

/-! ### Naimark's dilation theorem -/

section Naimark

variable {ι Z : Type*}

/-- Explicit two-outcome Naimark dilation: any two-outcome POVM `{E_false, E_true}` on `ℂ^ι`
is realized by a projective two-outcome POVM on `ℂ^(ι × Bool)` via an explicit `2 × 2` block
unitary `[[√E_false, -√E_true], [√E_true, √E_false]]`. -/
theorem naimark_two_outcome_projective [Fintype ι] [DecidableEq ι] (M : POVM Bool ι) :
    ∃ (U : Matrix (ι × Bool) (ι × Bool) ℂ), U ∈ unitaryGroup (ι × Bool) ℂ ∧
      ∀ (ρ : Matrix ι ι ℂ) (b : Bool),
        ((1 : Matrix ι ι ℂ) ⊗ₖ Matrix.single b b (1 : ℂ) *
          (U * (ρ ⊗ₖ Matrix.single false false (1 : ℂ)) * Uᴴ)).trace =
        (M.effect b * ρ).trace := by
  classical
  let E0 := M.effect false
  let E1 := M.effect true
  have hE01 : E0 + E1 = 1 := by
    have h := M.sum_effect
    rwa [Fintype.sum_bool, add_comm] at h
  have hE1_eq : E1 = 1 - E0 := eq_sub_of_add_eq' hE01
  let S0 : Matrix ι ι ℂ := cfc Real.sqrt E0
  let S1 : Matrix ι ι ℂ := cfc (fun t : ℝ ↦ Real.sqrt (1 - t)) E0
  have hE0_spec : ∀ t ∈ spectrum ℝ E0, 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    refine ⟨real_spectrum_nonneg_of_posSemidef (M.posSemidef false) ht, ?_⟩
    have hE1p : (1 - E0).PosSemidef := hE1_eq ▸ M.posSemidef true
    have hsub_nn : 0 ≤ 1 - t := by
      have hev := (M.posSemidef false).isHermitian.spectrum_real_eq_range_eigenvalues
      rw [hev] at ht
      obtain ⟨i, rfl⟩ := ht
      have hvec := (M.posSemidef false).isHermitian.mulVec_eigenvectorBasis i
      have hsubv : (1 - E0) *ᵥ ⇑((M.posSemidef false).isHermitian.eigenvectorBasis i) =
          ((1 - (M.posSemidef false).isHermitian.eigenvalues i : ℝ) : ℂ) •
            ⇑((M.posSemidef false).isHermitian.eigenvectorBasis i) := by
        rw [sub_mulVec, one_mulVec, hvec, Complex.ofReal_sub, Complex.ofReal_one, sub_smul,
          one_smul]
        rfl
      have hdot := hE1p.dotProduct_mulVec_nonneg
        ⇑((M.posSemidef false).isHermitian.eigenvectorBasis i)
      have hnorm1 : star ⇑((M.posSemidef false).isHermitian.eigenvectorBasis i) ⬝ᵥ
          ⇑((M.posSemidef false).isHermitian.eigenvectorBasis i) = 1 := by
        have h := (orthonormal_iff_ite.mp
          (M.posSemidef false).isHermitian.eigenvectorBasis.orthonormal) i i
        simp only [ite_true, EuclideanSpace.inner_eq_star_dotProduct] at h
        simpa [dotProduct, mul_comm] using h
      rw [hsubv, dotProduct_smul, hnorm1, smul_eq_mul, mul_one] at hdot
      exact (Complex.nonneg_iff.mp hdot).1
    linarith
  have hS0h : S0.IsHermitian := isHermitian_cfc_real E0 Real.sqrt
  have hS1h : S1.IsHermitian := isHermitian_cfc_real E0 (fun t ↦ Real.sqrt (1 - t))
  have hS00 : S0 * S0 = E0 := by
    rw [← cfc_mul _ _ E0 ((E0.finite_real_spectrum).continuousOn _)
      ((E0.finite_real_spectrum).continuousOn _)]
    exact (cfc_congr fun t ht ↦ Real.mul_self_sqrt (hE0_spec t ht).1).trans
      (cfc_id ℝ E0 (M.posSemidef false).isHermitian.isSelfAdjoint)
  have hS11 : S1 * S1 = E1 := by
    rw [← cfc_mul _ _ E0 ((E0.finite_real_spectrum).continuousOn _)
      ((E0.finite_real_spectrum).continuousOn _), hE1_eq]
    refine (cfc_congr fun t ht ↦ Real.mul_self_sqrt (sub_nonneg.mpr (hE0_spec t ht).2)).trans ?_
    change cfc (fun t : ℝ ↦ (fun _ ↦ (1 : ℝ)) t - id t) E0 = 1 - E0
    rw [cfc_sub (fun _ ↦ (1 : ℝ)) id E0 ((E0.finite_real_spectrum).continuousOn _)
      ((E0.finite_real_spectrum).continuousOn _),
      cfc_const (p := IsSelfAdjoint) (1 : ℝ) E0 (M.posSemidef false).isHermitian,
      cfc_id ℝ E0 (M.posSemidef false).isHermitian.isSelfAdjoint, map_one]
  have hcomm : S0 * S1 = S1 * S0 := by
    rw [← cfc_mul _ _ E0 ((E0.finite_real_spectrum).continuousOn _)
        ((E0.finite_real_spectrum).continuousOn _),
      ← cfc_mul _ _ E0 ((E0.finite_real_spectrum).continuousOn _)
        ((E0.finite_real_spectrum).continuousOn _)]
    exact cfc_congr fun t _ ↦ mul_comm _ _
  let U : Matrix (ι × Bool) (ι × Bool) ℂ := fun p q ↦
    match p.2, q.2 with
    | false, false => S0 p.1 q.1
    | false, true  => -S1 p.1 q.1
    | true,  false => S1 p.1 q.1
    | true,  true  => S0 p.1 q.1
  have hS0_star (x y : ι) : star (S0 x y) = S0 y x := by
    simpa [conjTranspose_apply] using congrFun (congrFun hS0h.eq y) x
  have hS1_star (x y : ι) : star (S1 x y) = S1 y x := by
    simpa [conjTranspose_apply] using congrFun (congrFun hS1h.eq y) x
  have hU_mul : Uᴴ * U = 1 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Matrix.one_apply, Prod.mk.injEq]
    cases a <;> cases b
    · have h := congrFun (congrFun (show S0 * S0 + S1 * S1 = 1 by rw [hS00, hS11, hE01]) i) j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply] at h
      simpa only [U, hS0_star, hS1_star, Finset.sum_add_distrib, add_comm, and_true] using h
    · have h := congrFun (congrFun (show -(S0 * S1) + S1 * S0 = 0 by rw [hcomm]; abel) i) j
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.zero_apply] at h
      simp only [U, hS0_star, hS1_star, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        Bool.false_eq_true, and_false, ite_false]
      exact (add_comm _ _).trans h
    · have h := congrFun (congrFun (show -(S1 * S0) + S0 * S1 = 0 by rw [hcomm]; abel) i) j
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.zero_apply] at h
      simp only [U, hS0_star, hS1_star, neg_mul, star_neg, Finset.sum_add_distrib,
        Finset.sum_neg_distrib, Bool.true_eq_false, and_false, ite_false]
      exact (add_comm _ _).trans h
    · have h := congrFun (congrFun (show S1 * S1 + S0 * S0 =
      1 by rw [hS00, hS11, add_comm, hE01]) i) j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply] at h
      simpa only [U, hS0_star, hS1_star, star_neg, neg_mul, mul_neg, neg_neg,
        Finset.sum_add_distrib, add_comm, and_true] using h
  have hU_mem : U ∈ unitaryGroup (ι × Bool) ℂ :=
    (mem_unitaryGroup_iff').mpr hU_mul
  refine ⟨U, hU_mem, fun ρ b ↦ ?_⟩
  -- Compute trace of `(I ⊗ |b⟩⟨b|) U (ρ ⊗ |false⟩⟨false|) Uᴴ`.
  have hslice (i j : ι) :
      (U * (ρ ⊗ₖ Matrix.single false false (1 : ℂ)) * Uᴴ) (i, b) (j, b) =
        ((match b with | false => S0 | true => S1) * ρ *
          (match b with | false => S0 | true => S1)) i j := by
    simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, Matrix.single,
      Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    cases b
    · simp only [U, hS0_star, ite_true, Bool.false_eq_true, ite_false,
        and_self, and_false, false_and, mul_zero, zero_mul, add_zero, zero_add, mul_one,
        Finset.sum_const_zero]
    · simp only [U, hS1_star, ite_true, Bool.false_eq_true, ite_false,
        and_self, and_false, false_and, mul_zero, zero_mul, add_zero, zero_add, mul_one,
        Finset.sum_const_zero]
  have htr : ((1 : Matrix ι ι ℂ) ⊗ₖ Matrix.single b b (1 : ℂ) *
      (U * (ρ ⊗ₖ Matrix.single false false (1 : ℂ)) * Uᴴ)).trace =
      ∑ i : ι, (U * (ρ ⊗ₖ Matrix.single false false (1 : ℂ)) * Uᴴ) (i, b) (i, b) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, kroneckerMap_apply,
      Matrix.one_apply, Matrix.single, Matrix.of_apply, Fintype.sum_prod_type,
      ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; simp [hb'.symm]
    · intro hb; exact absurd (mem_univ _) hb
  rw [htr]
  simp_rw [hslice]
  have hS_sq : ((match b with | false => S0 | true => S1) *
      (match b with | false => S0 | true => S1)) = M.effect b := by
    cases b <;> assumption
  change ((match b with | false => S0 | true => S1) * ρ *
    (match b with | false => S0 | true => S1)).trace = _
  rw [trace_mul_cycle, hS_sq]

/-- (Naimark's theorem): for any Kraus measurement `{M_z}_{z ∈ Z}` with `∑ z, M_zᴴ M_z = 1`
and any base outcome `z₀ : Z`, there exists a unitary `U` on `ℂ^(ι × Z)` such that measuring the
ancilla `Z` in the computational basis after applying `U` to `ρ ⊗ |z₀⟩⟨z₀|` yields outcome `z`
with probability `Tr(M_z ρ M_zᴴ)`.
-/
theorem naimark_dilation [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]
    (M : Z → Matrix ι ι ℂ) (hM : ∑ z : Z, (M z)ᴴ * M z = 1) (z₀ : Z) :
    ∃ (U : Matrix (ι × Z) (ι × Z) ℂ), U ∈ unitaryGroup (ι × Z) ℂ ∧
      ∀ (ρ : Matrix ι ι ℂ) (z : Z),
        ((1 : Matrix ι ι ℂ) ⊗ₖ Matrix.single z z (1 : ℂ) *
          (U * (ρ ⊗ₖ Matrix.single z₀ z₀ (1 : ℂ)) * Uᴴ)).trace =
        (M z * ρ * (M z)ᴴ).trace := by
  classical
  -- Column vectors `v p : EuclideanSpace ℂ (ι × Z)` on slice `s = {p | p.2 = z₀}`.
  let v : ι × Z → EuclideanSpace ℂ (ι × Z) :=
    fun p ↦ WithLp.toLp 2 (fun q : ι × Z ↦ M q.2 q.1 p.1)
  let s : Set (ι × Z) := {p | p.2 = z₀}
  have hv_ortho : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨⟨j₁, z₁⟩, hz₁⟩ ⟨⟨j₂, z₂⟩, hz₂⟩
    simp only [Set.domRestrict_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Pi.star_apply, Subtype.mk.injEq, Prod.mk.injEq]
    have hz12 : z₁ = z₂ := hz₁.trans hz₂.symm
    simp only [hz12, and_true]
    change (∑ p : ι × Z, M p.2 p.1 j₂ * star (M p.2 p.1 j₁)) = if j₁ = j₂ then 1 else 0
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hsum : ∑ z : Z, ∑ i : ι, M z i j₂ * star (M z i j₁) =
        (∑ z : Z, (M z)ᴴ * M z) j₁ j₂ := by
      simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
      refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    rw [hsum, hM, Matrix.one_apply]
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (ι × Z)) = Fintype.card (ι × Z) := by
    rw [finrank_euclideanSpace]
  obtain ⟨b, hb⟩ := hv_ortho.exists_orthonormalBasis_extension_of_card_eq hcard
  let U : Matrix (ι × Z) (ι × Z) ℂ := fun p q ↦ (b q).ofLp p
  have hU_mul : Uᴴ * U = 1 := by
    ext q₁ q₂
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    have hi := (orthonormal_iff_ite.mp b.orthonormal) q₁ q₂
    simpa [U, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hi
  have hU_mem : U ∈ unitaryGroup (ι × Z) ℂ := (mem_unitaryGroup_iff').mpr hU_mul
  refine ⟨U, hU_mem, fun ρ z ↦ ?_⟩
  have hU_col (i j : ι) (z' : Z) : U (i, z') (j, z₀) = M z' i j := by
    have h := hb (j, z₀) rfl
    change (b (j, z₀)).ofLp (i, z') = M z' i j
    rw [h]
  have hslice (i j : ι) :
      (U * (ρ ⊗ₖ Matrix.single z₀ z₀ (1 : ℂ)) * Uᴴ) (i, z) (j, z) = (M z * ρ * (M z)ᴴ) i j := by
    simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, Matrix.single,
      Matrix.of_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm, Finset.sum_eq_single z₀]
    · refine Finset.sum_congr rfl fun k₂ _ ↦ ?_
      rw [Finset.sum_comm, Finset.sum_eq_single z₀]
      · simp only [hU_col]
        congr 1
      · intro z' _ hz'; simp [hz'.symm]
      · intro h; exact absurd (mem_univ _) h
    · intro z' _ hz'; simp [hz'.symm]
    · intro h; exact absurd (mem_univ _) h
  have htr : ((1 : Matrix ι ι ℂ) ⊗ₖ Matrix.single z z (1 : ℂ) *
      (U * (ρ ⊗ₖ Matrix.single z₀ z₀ (1 : ℂ)) * Uᴴ)).trace =
      ∑ i : ι, (U * (ρ ⊗ₖ Matrix.single z₀ z₀ (1 : ℂ)) * Uᴴ) (i, z) (i, z) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, kroneckerMap_apply,
      Matrix.one_apply, Matrix.single, Matrix.of_apply, Fintype.sum_prod_type,
      ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm, Finset.sum_eq_single z]
    · simp
    · intro z' _ hz'; simp [hz'.symm]
    · intro h; exact absurd (mem_univ _) h
  rw [htr]
  simp_rw [hslice]
  rfl

end Naimark

/-! ### Frobenius norm squared and projector rank -/

section Frobenius

variable {ι κ : Type*}

/-- Squared Frobenius (Hilbert–Schmidt) norm `‖A‖_F² = Re Tr(Aᴴ A)`. -/
noncomputable def frobeniusNormSq [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  (Aᴴ * A).trace.re

@[simp]
theorem frobeniusNormSq_zero [Fintype ι] [Fintype κ] : frobeniusNormSq (0 : Matrix ι κ ℂ) = 0 := by
  simp [frobeniusNormSq]

theorem frobeniusNormSq_of_isHermitian [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    frobeniusNormSq A = (A * A).trace.re := by rw [frobeniusNormSq, hA.eq]

theorem frobeniusNormSq_eq_sum_norm_sq [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    frobeniusNormSq A = ∑ i : ι, ∑ j : κ, ‖A i j‖ ^ 2 := by
  simp only [frobeniusNormSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

theorem frobeniusNormSq_nonneg [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    0 ≤ frobeniusNormSq A := by
  rw [frobeniusNormSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- : for any orthogonal projector `Π` (`Πᴴ = Π` and `Π² = Π`), `‖Π‖_F² = rank(Π)`. -/
theorem frobeniusNormSq_eq_rank_of_isProjection [Fintype ι] {P : Matrix ι ι ℂ}
    (hH : P.IsHermitian) (hP : P * P = P) :
    frobeniusNormSq P = (P.rank : ℝ) := by
  classical
  rw [frobeniusNormSq_of_isHermitian hH, hP]
  have htr : P.trace.re = ∑ i : ι, hH.eigenvalues i := by
    simpa [Complex.re_sum] using congrArg Complex.re hH.trace_eq_sum_eigenvalues
  have heig (i : ι) : hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
    have hD : diagonal (fun j : ι ↦ (hH.eigenvalues j : ℂ)) *
        diagonal (fun j : ι ↦ (hH.eigenvalues j : ℂ)) =
        diagonal (fun j : ι ↦ (hH.eigenvalues j : ℂ)) := by
      have := congrArg (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star hH.eigenvectorUnitary)) hP
      rwa [map_mul, hH.conjStarAlgAut_star_eigenvectorUnitary] at this
    have hi := congrFun (congrFun hD i) i
    simp only [diagonal_mul_diagonal, diagonal_apply_eq] at hi
    have hreal : hH.eigenvalues i * hH.eigenvalues i = hH.eigenvalues i :=
      Complex.ofReal_injective (by simpa only [Complex.ofReal_mul] using hi)
    rcases mul_eq_zero.mp (show hH.eigenvalues i * (hH.eigenvalues i - 1) = 0 by linarith)
      with h0 | h1'
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1')
  have hrank : P.rank = (Finset.univ.filter fun i : ι ↦ hH.eigenvalues i ≠ 0).card := by
    let U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
    let D : Matrix ι ι ℂ := diagonal fun i ↦ (hH.eigenvalues i : ℂ)
    have hP_eq : P = U * D * Uᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, U, D,
        Function.comp_def, Complex.coe_algebraMap] using hH.spectral_theorem
    have hU_det : IsUnit U.det := isUnit_iff_ne_zero.mpr fun hdet ↦ by
      have h1' : (Uᴴ * U).det = 1 := by
        rw [show Uᴴ * U = 1 from Unitary.coe_star_mul_self hH.eigenvectorUnitary, det_one]
      rw [det_mul, hdet, mul_zero] at h1'; exact zero_ne_one h1'
    have hPrank : P.rank = D.rank := by
      rw [hP_eq, Matrix.rank_mul_eq_left_of_isUnit_det _ _
          (by rw [det_conjTranspose]; exact hU_det.map (starRingEnd ℂ)),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU_det]
    rw [hPrank, Matrix.rank_diagonal, Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ Complex.ofReal_ne_zero)
  rw [htr, hrank, ← Finset.sum_boole]
  exact Finset.sum_congr rfl fun i _ ↦ by rcases heig i with h | h <;> simp [h]

end Frobenius

end CslibFrontier.Quantum
