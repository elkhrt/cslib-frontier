module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Trace-Moment Spectral Bounds and PSD Voting Recovery

This module provides reusable, `Mathlib`-only foundations for spectral trace-moment methods and
spectral eigenvector recovery:

1. **Matrix spectral norm & even trace-moment inequalities** (`matrixSpectralNorm`,
   `matrixSpectralNorm_pow_two_mul_le_trace_pow`,
   `trace_pow_two_mul_le_card_mul_matrixSpectralNorm_pow`, `abs_rayleigh_le_matrixSpectralNorm`,
   `rayleigh_div_le_matrixSpectralNorm`, `measureReal_spectralNorm_ge_le_of_trace_bound`).
2. **PSD voting-matrix rank-1 eigenvector recovery** (`psd_voting_topEigenvector_corr`), proving
   that any top unit eigenvector `u₁` of a PSD real symmetric matrix `W` with trace `t > 0`
   satisfying `uᵀ W u ≥ t (1 - α)` obeys `(u ⬝ᵥ u₁)² ≥ 1 - 2 α`.
-/

public section

open MeasureTheory
open scoped symmDiff Matrix

namespace CslibFrontier.Foundations.LinearAlgebra.Matrix

/-- Operator `ℓ² → ℓ²` spectral norm `‖A‖_{sp}` of a real `ι × ι` matrix. -/
noncomputable def matrixSpectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : _root_.Matrix ι ι ℝ) : ℝ :=
  ‖_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- Nonnegativity of the spectral norm. -/
theorem matrixSpectralNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : _root_.Matrix ι ι ℝ) : 0 ≤ matrixSpectralNorm A :=
  norm_nonneg _

/-- For any real Hermitian matrix `A` and natural `k`,
`Tr(A ^ k) = ∑ i, (eigenvalues i) ^ k`. -/
theorem trace_pow_eq_sum_eigenvalues_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i : ι, (hA.eigenvalues i) ^ k := by
  have hspec := hA.spectral_theorem
  let U : _root_.Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hU_inv : U * star U = 1 := by
    simp [U]
  have hstar_U : star U * U = 1 := by
    simp [U]
  have hA_eq : A = U * _root_.Matrix.diagonal (hA.eigenvalues) * star U := by
    simpa [U, Unitary.conjStarAlgAut_apply, _root_.Matrix.mul_assoc] using hspec
  have hpow : A ^ k = U * _root_.Matrix.diagonal (fun i ↦ (hA.eigenvalues i) ^ k) * star U := by
    induction k with
    | zero =>
      simp only [pow_zero, _root_.Matrix.diagonal_one, _root_.Matrix.mul_one, hU_inv]
    | succ k ih =>
      rw [pow_succ, ih]
      conv_lhs => arg 2; rw [hA_eq]
      calc U * _root_.Matrix.diagonal (fun i ↦ (hA.eigenvalues i) ^ k) * star U *
            (U * _root_.Matrix.diagonal hA.eigenvalues * star U)
          = U * _root_.Matrix.diagonal (fun i ↦ (hA.eigenvalues i) ^ k) * (star U * U) *
              _root_.Matrix.diagonal hA.eigenvalues * star U := by
            simp only [_root_.Matrix.mul_assoc]
        _ = U * (_root_.Matrix.diagonal (fun i ↦ (hA.eigenvalues i) ^ k) *
              _root_.Matrix.diagonal hA.eigenvalues) * star U := by
            rw [hstar_U, _root_.Matrix.mul_one]
            simp only [_root_.Matrix.mul_assoc]
        _ = U * _root_.Matrix.diagonal (fun i ↦ (hA.eigenvalues i) ^ (k + 1)) * star U := by
            rw [_root_.Matrix.diagonal_mul_diagonal]
            congr 2
  rw [hpow, _root_.Matrix.trace_mul_cycle, hstar_U, _root_.Matrix.one_mul,
    _root_.Matrix.trace_diagonal]

/-- Every eigenvalue of a real Hermitian matrix `A` is bounded in absolute value by `‖A‖_{sp}`. -/
theorem abs_eigenvalue_le_matrixSpectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    |hA.eigenvalues i| ≤ matrixSpectralNorm A := by
  let b := hA.eigenvectorBasis
  have hbi_norm : ‖b i‖ = 1 := b.orthonormal.1 i
  have hmul : _root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A (b i) = hA.eigenvalues i • b i := by
    change A.toEuclideanLin (b i) = hA.eigenvalues i • b i
    exact PiLp.ext fun k ↦ congrFun (hA.mulVec_eigenvectorBasis i) k
  have hle := ContinuousLinearMap.le_opNorm (_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A) (b i)
  rw [hmul, norm_smul, Real.norm_eq_abs, hbi_norm, mul_one, mul_one] at hle
  exact hle

/-- If every eigenvalue of real Hermitian `A` has `|λ_i| ≤ c` (with `0 ≤ c`),
then `‖A‖_{sp} ≤ c`. -/
theorem matrixSpectralNorm_le_of_forall_abs_eigenvalue_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : ι, |hA.eigenvalues i| ≤ c) :
    matrixSpectralNorm A ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x ↦ ?_
  let b := hA.eigenvectorBasis
  have hx : ‖x‖ ^ 2 = ∑ i : ι, (b.repr x i) ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hAx : ‖_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ ^ 2 =
      ∑ i : ι, (hA.eigenvalues i * b.repr x i) ^ 2 := by
    have hrep : _root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x =
        ∑ i : ι, (hA.eigenvalues i * b.repr x i) • b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, show _root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A (b i) =
        hA.eigenvalues i • b i from
          PiLp.ext fun k ↦ congrFun (hA.mulVec_eigenvectorBasis i) k, smul_smul, mul_comm]
    rw [hrep, ← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [map_sum, map_smul, OrthonormalBasis.repr_self, Pi.single_apply, Real.norm_eq_abs,
      ← abs_mul]
  have hsq : ‖_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [hAx, mul_pow, hx, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [mul_pow]
    have hi : (hA.eigenvalues i) ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  nlinarith [norm_nonneg (_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x), mul_nonneg hc (norm_nonneg x)]

/-- For every real Hermitian matrix `A` and every `q ≥ 1`,
`‖A‖_{sp} ^ (2 * q) ≤ Tr(A ^ (2 * q))`. -/
theorem matrixSpectralNorm_pow_two_mul_le_trace_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) {q : ℕ} (hq : 1 ≤ q) :
    matrixSpectralNorm A ^ (2 * q) ≤ (A ^ (2 * q)).trace := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ
      (fun i : ι ↦ |hA.eigenvalues i|) Finset.univ_nonempty
    have hsp : matrixSpectralNorm A ≤ |hA.eigenvalues i₀| :=
      matrixSpectralNorm_le_of_forall_abs_eigenvalue_le hA (abs_nonneg _) fun i ↦
        hi₀ i (Finset.mem_univ i)
    rw [trace_pow_eq_sum_eigenvalues_pow hA]
    have hpow_le : matrixSpectralNorm A ^ (2 * q) ≤ (hA.eigenvalues i₀) ^ (2 * q) := by
      calc matrixSpectralNorm A ^ (2 * q)
          ≤ |hA.eigenvalues i₀| ^ (2 * q) :=
            pow_le_pow_left₀ (matrixSpectralNorm_nonneg _) hsp (2 * q)
        _ = (hA.eigenvalues i₀) ^ (2 * q) := by rw [pow_mul, sq_abs, ← pow_mul]
    have hterm : (hA.eigenvalues i₀) ^ (2 * q) ≤ ∑ i : ι, (hA.eigenvalues i) ^ (2 * q) :=
      Finset.single_le_sum (f := fun i : ι ↦ (hA.eigenvalues i) ^ (2 * q))
        (fun i _ ↦ by rw [pow_mul]; positivity) (Finset.mem_univ i₀)
    exact hpow_le.trans hterm
  · have hA0 : A = 0 := _root_.Matrix.ext fun i ↦ (hι ⟨i⟩).elim
    have hclm0 : _root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A = 0 := by
      ext x i; exact (hι ⟨i⟩).elim
    have hnorm0 : matrixSpectralNorm A = 0 := by simp [matrixSpectralNorm, hclm0]
    have htr0 : (A ^ (2 * q)).trace = 0 := by
      rw [hA0, zero_pow (by omega), _root_.Matrix.trace_zero]
    rw [hnorm0, zero_pow (by omega), htr0]

/-- For every real Hermitian matrix `A` and every `q : ℕ`,
`Tr(A ^ (2 * q)) ≤ |ι| · ‖A‖_{sp} ^ (2 * q)`. -/
theorem trace_pow_two_mul_le_card_mul_matrixSpectralNorm_pow {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) (q : ℕ) :
    (A ^ (2 * q)).trace ≤ (Fintype.card ι : ℝ) * matrixSpectralNorm A ^ (2 * q) := by
  rw [trace_pow_eq_sum_eigenvalues_pow hA]
  calc ∑ i : ι, (hA.eigenvalues i) ^ (2 * q)
      ≤ ∑ _i : ι, matrixSpectralNorm A ^ (2 * q) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have h1 := abs_eigenvalue_le_matrixSpectralNorm hA i
        calc (hA.eigenvalues i) ^ (2 * q)
            = |hA.eigenvalues i| ^ (2 * q) := by rw [pow_mul, ← sq_abs, ← pow_mul]
          _ ≤ matrixSpectralNorm A ^ (2 * q) := pow_le_pow_left₀ (abs_nonneg _) h1 (2 * q)
    _ = (Fintype.card ι : ℝ) * matrixSpectralNorm A ^ (2 * q) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Absolute Rayleigh quotient bound: `|v ⬝ᵥ (A *ᵥ v)| ≤ ‖A‖_{sp} · (v ⬝ᵥ v)`. -/
theorem abs_rayleigh_le_matrixSpectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : _root_.Matrix ι ι ℝ) (v : ι → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ matrixSpectralNorm A * (v ⬝ᵥ v) := by
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  have hinner : v ⬝ᵥ (A *ᵥ v) = inner ℝ x (_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    rfl
  have hx_sq : v ⬝ᵥ v = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [x, dotProduct, Real.norm_eq_abs, sq]
  rw [hinner, hx_sq]
  calc |inner ℝ x (_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x)|
      ≤ ‖x‖ * ‖_root_.Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (matrixSpectralNorm A * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ x) (norm_nonneg x)
    _ = matrixSpectralNorm A * ‖x‖ ^ 2 := by ring

/-- Rayleigh quotient lower bound on spectral norm for nonzero `v`. -/
theorem rayleigh_div_le_matrixSpectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : _root_.Matrix ι ι ℝ) {v : ι → ℝ} (hv : 0 < v ⬝ᵥ v) :
    (v ⬝ᵥ (A *ᵥ v)) / (v ⬝ᵥ v) ≤ matrixSpectralNorm A :=
  (div_le_iff₀ hv).mpr ((le_abs_self _).trans (abs_rayleigh_le_matrixSpectralNorm A v))

/-- Markov tail bound from an even trace moment:
for any probability measure `μ` and real Hermitian matrix-valued map `M`,
`μ.real {G | B ≤ ‖M G‖_{sp}} ≤ (∫ G, Tr(M(G) ^ (2 * q)) ∂μ) / B ^ (2 * q)`. -/
theorem measureReal_spectralNorm_ge_le_of_trace_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : Ω → _root_.Matrix ι ι ℝ} (hHerm : ∀ G, (M G).IsHermitian)
    {q : ℕ} (hq : 1 ≤ q)
    (hint : Integrable (fun G ↦ (M G ^ (2 * q)).trace) μ)
    {B : ℝ} (hB : 0 < B) :
    μ.real {G | B ≤ matrixSpectralNorm (M G)} ≤
      (∫ G, (M G ^ (2 * q)).trace ∂μ) / B ^ (2 * q) := by
  have htr_nonneg : ∀ G, 0 ≤ (M G ^ (2 * q)).trace := fun G ↦
    le_trans (pow_nonneg (matrixSpectralNorm_nonneg _) _)
      (matrixSpectralNorm_pow_two_mul_le_trace_pow (hHerm G) hq)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall htr_nonneg) hint (B ^ (2 * q))
  have hsub : {G : Ω | B ≤ matrixSpectralNorm (M G)} ⊆
      {G : Ω | B ^ (2 * q) ≤ (M G ^ (2 * q)).trace} := fun G hG ↦
    (pow_le_pow_left₀ hB.le hG (2 * q)).trans
      (matrixSpectralNorm_pow_two_mul_le_trace_pow (hHerm G) hq)
  have hmono : μ.real {G | B ≤ matrixSpectralNorm (M G)} ≤
      μ.real {G | B ^ (2 * q) ≤ (M G ^ (2 * q)).trace} := measureReal_mono hsub
  have hdiv : μ.real {G | B ^ (2 * q) ≤ (M G ^ (2 * q)).trace} ≤
      (∫ G, (M G ^ (2 * q)).trace ∂μ) / B ^ (2 * q) :=
    (le_div_iff₀ (pow_pos hB (2 * q))).mpr (by rw [mul_comm]; exact hmarkov)
  exact hmono.trans hdiv

/-- **PSD Voting-Matrix Rank-1 Eigenvector Recovery Lemma**: if `W` is a positive semidefinite
real symmetric matrix with `Tr(W) = t > 0` and a unit vector `u` satisfies
`u ⬝ᵥ (W *ᵥ u) ≥ t * (1 - α)` (with `α < 1`), then any top unit eigenvector `u₁` of `W`
satisfies `(u ⬝ᵥ u₁)² ≥ 1 - 2 * α`. -/
theorem psd_voting_topEigenvector_corr {n : ℕ} [NeZero n] {W : _root_.Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) {t α : ℝ} (ht : 0 < t) (hTr : W.trace = t)
    (hα1 : α < 1)
    {u u₁ : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (hu₁ : ‖u₁‖ = 1)
    (hquad : t * (1 - α) ≤ u.ofLp ⬝ᵥ (W *ᵥ u.ofLp))
    (htop : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
      w.ofLp ⬝ᵥ (W *ᵥ w.ofLp) ≤ u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) :
    1 - 2 * α ≤ (u.ofLp ⬝ᵥ u₁.ofLp) ^ 2 := by
  have hHerm := hW.isHermitian
  let b := hHerm.eigenvectorBasis
  let lam := hHerm.eigenvalues
  have hlam_nn : ∀ i, 0 ≤ lam i := hW.eigenvalues_nonneg
  have hsum_lam : ∑ i, lam i = t := by
    have := hHerm.trace_eq_sum_eigenvalues; simpa [lam, hTr] using this.symm
  let c : ℝ := u.ofLp ⬝ᵥ u₁.ofLp
  let w : EuclideanSpace ℝ (Fin n) := u - c • u₁
  have hinner_uu₁ : inner ℝ u u₁ = c := by
    simp [c, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hu₁_norm_sq : u₁.ofLp ⬝ᵥ u₁.ofLp = 1 := by
    have := EuclideanSpace.norm_sq_eq u₁
    rw [hu₁] at this; simpa [dotProduct, Real.norm_eq_abs, sq_abs, sq] using this.symm
  have hu_norm_sq : u.ofLp ⬝ᵥ u.ofLp = 1 := by
    have := EuclideanSpace.norm_sq_eq u
    rw [hu] at this; simpa [dotProduct, Real.norm_eq_abs, sq_abs, sq] using this.symm
  have hw_orth : w.ofLp ⬝ᵥ u₁.ofLp = 0 := by
    simp only [w, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul,
      hu₁_norm_sq, mul_one, c, sub_self]
  have hw_norm_sq : w.ofLp ⬝ᵥ w.ofLp = 1 - c ^ 2 := by
    simp only [w, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hu_norm_sq, hu₁_norm_sq, c]
    have hcomm : u₁.ofLp ⬝ᵥ u.ofLp = u.ofLp ⬝ᵥ u₁.ofLp := dotProduct_comm _ _
    rw [hcomm]; ring
  have hlam1_ge : t * (1 - α) ≤ u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp) := hquad.trans (htop u hu)
  have hq_exp : ∀ x : EuclideanSpace ℝ (Fin n),
      x.ofLp ⬝ᵥ (W *ᵥ x.ofLp) = ∑ j, lam j * (inner ℝ (b j) x) ^ 2 := by
    intro x
    have h1 : x.ofLp ⬝ᵥ (W *ᵥ x.ofLp) = inner ℝ x (W.toEuclideanLin x) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
      rfl
    rw [h1]
    conv_lhs => rw [← b.sum_repr x]
    have h2 : inner ℝ (∑ j, b.repr x j • b j) (W.toEuclideanLin (∑ j, b.repr x j • b j)) =
        ∑ j, lam j * (b.repr x j) ^ 2 := by
      rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [sum_inner, map_smul]
      have hbj : W.toEuclideanLin (b j) = lam j • b j :=
        PiLp.ext fun i ↦ congrFun (hHerm.mulVec_eigenvectorBasis j) i
      rw [hbj, Finset.sum_eq_single j]
      · rw [inner_smul_left, inner_smul_right, inner_smul_right,
          real_inner_self_eq_norm_sq, b.orthonormal.1 j]
        simp; ring
      · intro k _ hkj
        rw [inner_smul_left, inner_smul_right, inner_smul_right, b.orthonormal.2 hkj]
        simp
      · intro hj; exact (hj (Finset.mem_univ j)).elim
    simpa [b.repr_apply_apply] using h2
  have hlam1_le : u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp) ≤ t := by
    rw [hq_exp u₁, ← hsum_lam]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hle1 : (inner ℝ (b j) u₁) ^ 2 ≤ 1 := by
      have h1 := abs_real_inner_le_norm (b j) u₁
      rw [b.orthonormal.1 j, hu₁, one_mul] at h1
      rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans (by norm_num)
    nlinarith [hlam_nn j]
  have hW_orth_le : w.ofLp ⬝ᵥ (W *ᵥ w.ofLp) ≤
      (t - u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) * (w.ofLp ⬝ᵥ w.ofLp) := by
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      let w0 : EuclideanSpace ℝ (Fin n) := ‖w‖⁻¹ • w
      have hw0_norm : ‖w0‖ = 1 := by
        simp [w0, norm_smul, hwnorm.ne']
      have hw0_orth : inner ℝ u₁ w0 = 0 := by
        rw [inner_smul_right]
        have : inner ℝ u₁ w = 0 := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]; exact hw_orth
        simp [this]
      have hparseval : u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp) + w0.ofLp ⬝ᵥ (W *ᵥ w0.ofLp) ≤ t := by
        rw [hq_exp u₁, hq_exp w0, ← Finset.sum_add_distrib, ← hsum_lam]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [← mul_add]
        have hle1 : (inner ℝ (b j) u₁) ^ 2 + (inner ℝ (b j) w0) ^ 2 ≤ 1 := by
          let r := b j - inner ℝ u₁ (b j) • u₁ - inner ℝ w0 (b j) • w0
          have hr_nn : 0 ≤ inner ℝ r r := real_inner_self_nonneg
          have hbj1 : inner ℝ (b j) (b j) = 1 := by
            rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j, one_pow]
          have hu11 : inner ℝ u₁ u₁ = 1 := by rw [real_inner_self_eq_norm_sq, hu₁, one_pow]
          have hw01 : inner ℝ w0 w0 = 1 := by rw [real_inner_self_eq_norm_sq, hw0_norm, one_pow]
          have hcomm1 : inner ℝ (b j) u₁ = inner ℝ u₁ (b j) := real_inner_comm _ _
          have hcomm2 : inner ℝ (b j) w0 = inner ℝ w0 (b j) := real_inner_comm _ _
          have hw0u1 : inner ℝ w0 u₁ = 0 := by rw [real_inner_comm, hw0_orth]
          simp only [r, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
            conj_trivial, hbj1, hu11, hw01, hw0_orth, hw0u1, ← hcomm1, ← hcomm2] at hr_nn
          nlinarith
        nlinarith [hlam_nn j]
      have hwn : w.ofLp ⬝ᵥ w.ofLp = ‖w‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]; simp [dotProduct, Real.norm_eq_abs, sq]
      have hw0_quad : w0.ofLp ⬝ᵥ (W *ᵥ w0.ofLp) =
          (w.ofLp ⬝ᵥ (W *ᵥ w.ofLp)) / (w.ofLp ⬝ᵥ w.ofLp) := by
        rw [hwn]; simp only [w0, WithLp.ofLp_smul, _root_.Matrix.mulVec_smul, smul_dotProduct,
          dotProduct_smul, smul_eq_mul]; field_simp [hwnorm.ne']
      have hw_pos : 0 < w.ofLp ⬝ᵥ w.ofLp := by rw [hwn]; positivity
      rw [hw0_quad] at hparseval
      exact (div_le_iff₀ hw_pos).mp (by linarith)
  have hW_cross : w.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp) = 0 := by
    have hε : ∀ ε : ℝ, (u₁.ofLp + ε • w.ofLp) ⬝ᵥ (W *ᵥ (u₁.ofLp + ε • w.ofLp)) ≤
        (u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) * (1 + ε ^ 2 * (w.ofLp ⬝ᵥ w.ofLp)) := by
      intro ε
      let y : EuclideanSpace ℝ (Fin n) := u₁ + ε • w
      have hy_sq : y.ofLp ⬝ᵥ y.ofLp = 1 + ε ^ 2 * (w.ofLp ⬝ᵥ w.ofLp) := by
        simp only [y, WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
          smul_dotProduct, dotProduct_smul, smul_eq_mul, hu₁_norm_sq, hw_orth,
          dotProduct_comm u₁.ofLp w.ofLp]; ring
      have hy_pos : 0 < y.ofLp ⬝ᵥ y.ofLp := by
        rw [hy_sq]
        have : 0 ≤ w.ofLp ⬝ᵥ w.ofLp := by
          rw [hw_norm_sq]
          have hc_le : |c| ≤ 1 := by
            have := abs_real_inner_le_norm u u₁; rwa [hinner_uu₁, hu, hu₁, mul_one] at this
          nlinarith [sq_abs c, abs_nonneg c]
        nlinarith [sq_nonneg ε]
      have hy_n2 : ‖y‖ ^ 2 = y.ofLp ⬝ᵥ y.ofLp := by
        rw [EuclideanSpace.norm_sq_eq]; simp [dotProduct, Real.norm_eq_abs, sq]
      have hy_ne : ‖y‖ ≠ 0 := by intro h0; rw [h0, zero_pow (by norm_num)] at hy_n2; linarith
      let y0 : EuclideanSpace ℝ (Fin n) := ‖y‖⁻¹ • y
      have hy0_norm : ‖y0‖ = 1 := by
        simp [y0, norm_smul, hy_ne]
      have htop_y := htop y0 hy0_norm
      have hy0_quad : y0.ofLp ⬝ᵥ (W *ᵥ y0.ofLp) =
          (y.ofLp ⬝ᵥ (W *ᵥ y.ofLp)) / (y.ofLp ⬝ᵥ y.ofLp) := by
        simp only [y0, WithLp.ofLp_smul, _root_.Matrix.mulVec_smul, smul_dotProduct,
          dotProduct_smul, smul_eq_mul]; rw [← hy_n2]; field_simp [hy_ne]
      rw [hy0_quad, div_le_iff₀ hy_pos, hy_sq] at htop_y
      simpa [y] using htop_y
    have hsymm : u₁.ofLp ⬝ᵥ (W *ᵥ w.ofLp) = w.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp) := by
      rw [_root_.Matrix.dotProduct_mulVec, ← _root_.Matrix.mulVec_transpose]
      have hWT : Wᵀ = W := by simpa using hHerm.eq
      rw [hWT, dotProduct_comm]
    set A := w.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)
    set B := (u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) * (w.ofLp ⬝ᵥ w.ofLp) - w.ofLp ⬝ᵥ (W *ᵥ w.ofLp)
    have hquad_eps : ∀ ε : ℝ, 2 * ε * A ≤ ε ^ 2 * B := fun ε ↦ by
      have h := hε ε
      simp only [add_dotProduct, dotProduct_add, _root_.Matrix.mulVec_add,
        _root_.Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hsymm] at h
      linarith
    by_contra hAne
    let ε := A / (|B| + 1)
    have h1 := hquad_eps ε
    have h2 : ε ^ 2 * B ≤ ε ^ 2 * (|B| + 1) :=
      mul_le_mul_of_nonneg_left ((le_abs_self B).trans (by linarith)) (sq_nonneg ε)
    have h3 : 2 * ε * A ≤ ε ^ 2 * (|B| + 1) := h1.trans h2
    have h4 : ε ^ 2 * (|B| + 1) = A ^ 2 / (|B| + 1) := by
      dsimp only [ε]; field_simp [show (|B| + 1 : ℝ) ≠ 0 by positivity]
    have h5 : 2 * ε * A = 2 * (A ^ 2 / (|B| + 1)) := by dsimp only [ε]; ring
    rw [h4, h5] at h3
    have hA2 : 0 < A ^ 2 / (|B| + 1) := div_pos (sq_pos_of_ne_zero hAne) (by positivity)
    linarith
  have hu_eq : u.ofLp = c • u₁.ofLp + w.ofLp := by ext i; simp [w]
  have hu_quad : u.ofLp ⬝ᵥ (W *ᵥ u.ofLp) =
      c ^ 2 * (u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) + w.ofLp ⬝ᵥ (W *ᵥ w.ofLp) := by
    rw [hu_eq]
    have hsymm : u₁.ofLp ⬝ᵥ (W *ᵥ w.ofLp) = w.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp) := by
      rw [_root_.Matrix.dotProduct_mulVec, ← _root_.Matrix.mulVec_transpose]
      have hWT : Wᵀ = W := by simpa using hHerm.eq
      rw [hWT, dotProduct_comm]
    simp only [add_dotProduct, dotProduct_add, _root_.Matrix.mulVec_add,
      _root_.Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hsymm, hW_cross]
    ring
  rw [hu_quad] at hquad
  have hcomb : t * (1 - α) ≤ c ^ 2 * t + (t * α) * (1 - c ^ 2) := by
    have h1 : c ^ 2 * (u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) ≤ c ^ 2 * t :=
      mul_le_mul_of_nonneg_left hlam1_le (sq_nonneg c)
    have h2 : (t - u₁.ofLp ⬝ᵥ (W *ᵥ u₁.ofLp)) * (w.ofLp ⬝ᵥ w.ofLp) ≤ (t * α) * (1 - c ^ 2) := by
      rw [hw_norm_sq]; refine mul_le_mul_of_nonneg_right (by linarith) ?_
      have hc_le : |c| ≤ 1 := by
        have := abs_real_inner_le_norm u u₁; rwa [hinner_uu₁, hu, hu₁, mul_one] at this
      nlinarith [sq_abs c, abs_nonneg c]
    linarith
  by_cases h12 : 0 ≤ 1 - 2 * α
  · have hα0 : 0 ≤ α := by nlinarith
    have hpos : 0 < t * (1 - α) := mul_pos ht (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hα0 (show 0 ≤ t * (1 - 2 * α) by nlinarith)]
  · linarith [sq_nonneg c]

end CslibFrontier.Foundations.LinearAlgebra.Matrix
