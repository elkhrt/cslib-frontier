/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Kronecker

import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Hilbert Matrix Operator Norm Bounds and Nonnegative Symmetric Spectral Helpers

This module establishes elementary Euclidean `ℓ²` operator-norm (`Matrix.toEuclideanCLM (𝕜 := ℝ)`)
results for finite real nonnegative symmetric matrices, the finite Hilbert matrix, and the
inverse-distance Toeplitz matrix arising in ordered search lower bounds, all proved under standard
Lean axioms:

1. **Weighted Schur test, monotonicity, and Perron–Frobenius eigenvector attainment**:
   - `CslibFrontier.Matrix.opNorm_toEuclideanCLM_le_of_pos_weights` and
     `CslibFrontier.Matrix.opNorm_toEuclideanCLM_le_of_symm_pos_weights`: positive-weight Schur test
     bounding `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖`.
   - `CslibFrontier.Matrix.opNorm_toEuclideanCLM_mono_of_nonneg`: entrywise comparison
     `0 ≤ A x y ≤ B x y` implies `‖A‖ ≤ ‖B‖`.
   - `CslibFrontier.Matrix.exists_unit_nonneg_inner_eq_opNorm`: every finite real symmetric
     nonnegative matrix on a nonempty index type admits a nonnegative unit eigenvector achieving its
     Euclidean operator norm.
   - `CslibFrontier.Matrix.opNorm_offDiagOne` and
     `CslibFrontier.Matrix.opNorm_kronecker_of_symm_nonneg`: exact operator norm of the off-diagonal
     all-ones matrix `J - I` and multiplicativity of the Euclidean operator norm under Kronecker
     products of symmetric nonnegative matrices.
2. **Choi's Hilbert matrix bound (`‖H_m‖ ≤ π`)**:
   - `CslibFrontier.Matrix.hilbertMatrix`: the `m × m` Hilbert matrix `H_m[j, k] = 1 / (j + k + 1)`.
   - `CslibFrontier.Matrix.opNorm_hilbertMatrix_le_pi` and
     `CslibFrontier.Matrix.opNorm_hilbertMatrix_lt_pi`: elementary proof of `‖H_m‖ ≤ π` (and `< π`
     for `1 ≤ m`) via the weighted Schur test with weights `(j + 1 / 2)⁻¹/²` and telescoping
     arctangent differences.
3. **Inverse-distance Toeplitz and interval-masked bounds**:
   - `CslibFrontier.Matrix.invDistMatrix` and `CslibFrontier.Matrix.intervalMask`: the Toeplitz
     matrix `A_m[i, j] = 1 / (|i - j| + 1)` and coordinate-straddling mask `D_r[x, y]`.
   - `CslibFrontier.Matrix.log_div_two_le_opNorm_invDistMatrix_sub_one`,
     `CslibFrontier.Matrix.log_div_two_le_opNorm_invDistMatrix`, and
     `CslibFrontier.Matrix.opNorm_invDistMatrix_hadamard_intervalMask_le`: harmonic lower bounds
     `log m / 2 ≤ ‖A_m - I‖ ≤ ‖A_m‖` for all `m : ℕ` and interval-masked upper bound
     `‖A_m ⊙ D_r‖ ≤ 2π`.

## Main definitions

* `CslibFrontier.Matrix.offDiagOne`: off-diagonal all-ones matrix `J - I` on a finite type.
* `CslibFrontier.Matrix.hilbertMatrix`: finite `m × m` Hilbert matrix `1 / (j + k + 1)`.
* `CslibFrontier.Matrix.invDistMatrix`: `m × m` inverse-distance matrix `1 / (|i - j| + 1)`.
* `CslibFrontier.Matrix.intervalMask`: indicator matrix of pairs `(x, y)` straddling `r : Fin m`.

## Main results

* `CslibFrontier.Matrix.opNorm_toEuclideanCLM_le_of_pos_weights`,
  `CslibFrontier.Matrix.opNorm_toEuclideanCLM_le_of_symm_pos_weights`,
  `CslibFrontier.Matrix.opNorm_toEuclideanCLM_mono_of_nonneg`.
* `CslibFrontier.Matrix.exists_unit_nonneg_inner_eq_opNorm`,
  `CslibFrontier.Matrix.opNorm_offDiagOne`,
  `CslibFrontier.Matrix.opNorm_kronecker_of_symm_nonneg`.
* `CslibFrontier.Matrix.opNorm_hilbertMatrix_le_pi`,
  `CslibFrontier.Matrix.opNorm_hilbertMatrix_lt_pi`.
* `CslibFrontier.Matrix.log_div_two_le_opNorm_invDistMatrix_sub_one`,
  `CslibFrontier.Matrix.log_div_two_le_opNorm_invDistMatrix`,
  `CslibFrontier.Matrix.opNorm_invDistMatrix_hadamard_intervalMask_le`.

## Tags

Hilbert matrix, Schur test, Euclidean operator norm, Perron-Frobenius, Kronecker product
-/

public section

open Finset Matrix
open scoped Matrix Kronecker RealInnerProductSpace

namespace CslibFrontier.Matrix

/-! ### 1. Weighted Schur Test, Entrywise Monotonicity, and Nonnegative Eigenvectors -/

section WeightedSchur

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
private theorem sum_weighted_sq_le (A : Matrix κ κ ℝ) {p : κ → ℝ} (hp : ∀ x, 0 < p x) {R : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, |A x y| * p y ≤ R * p x) {u : EuclideanSpace ℝ κ}
    (hu : ‖u‖ ≤ 1) :
    ∑ q : κ × κ, (√(|A q.1 q.2| * p q.2 / p q.1) * |u.ofLp q.1|) ^ 2 ≤ R := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ x, ∑ y, (√(|A x y| * p y / p x) * |u.ofLp x|) ^ 2
        = ∑ x, u.ofLp x ^ 2 * ((∑ y, |A x y| * p y) / p x) := by
          refine sum_congr rfl fun x _ ↦ ?_
          rw [sum_div, mul_sum]
          refine sum_congr rfl fun y _ ↦ ?_
          have hnn : 0 ≤ |A x y| * p y / p x :=
            div_nonneg (mul_nonneg (abs_nonneg _) (hp y).le) (hp x).le
          rw [mul_pow, Real.sq_sqrt hnn, sq_abs, mul_comm]
    _ ≤ ∑ x, u.ofLp x ^ 2 * R := by
          refine sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact (div_le_iff₀ (hp x)).2 (hrow x)
    _ = (∑ x, u.ofLp x ^ 2) * R := (sum_mul _ _ _).symm
    _ ≤ 1 * R :=
          mul_le_mul_of_nonneg_right ((EuclideanSpace.norm_le_one_iff_sum_sq_le_one u).1 hu) hR
    _ = R := one_mul R

/-- **Weighted Schur test** for Euclidean operator norms: if `p : κ → ℝ` has strictly positive
entries and `∑ y, |A x y| * p y ≤ R * p x`, `∑ x, |A x y| * p x ≤ C * p y` for all `x, y`, then
`‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ √(R * C)`. -/
theorem opNorm_toEuclideanCLM_le_of_pos_weights (A : Matrix κ κ ℝ) {p : κ → ℝ}
    (hp : ∀ x, 0 < p x) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ x, ∑ y, |A x y| * p y ≤ R * p x)
    (hcol : ∀ y, ∑ x, |A x y| * p x ≤ C * p y) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ √(R * C) := by
  refine opNorm_toEuclideanCLM_le_of_inner A (Real.sqrt_nonneg _) fun u v hu hv ↦ ?_
  rw [inner_toEuclideanCLM]
  simp only [dotProduct, mulVec, mul_sum]
  have h1 : ∑ x, ∑ y, u.ofLp x * (A x y * v.ofLp y) ≤
      ∑ q : κ × κ, (√(|A q.1 q.2| * p q.2 / p q.1) * |u.ofLp q.1|) *
        (√(|A q.1 q.2| * p q.1 / p q.2) * |v.ofLp q.2|) := by
    rw [Fintype.sum_prod_type]
    refine sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_
    have hpx : p x ≠ 0 := (hp x).ne'
    have hpy : p y ≠ 0 := (hp y).ne'
    have hprod : √(|A x y| * p y / p x) * √(|A x y| * p x / p y) = |A x y| := by
      rw [← Real.sqrt_mul (div_nonneg (mul_nonneg (abs_nonneg _) (hp y).le) (hp x).le)]
      have hsimpl : (|A x y| * p y / p x) * (|A x y| * p x / p y) = |A x y| ^ 2 := by
        field_simp [hpx, hpy]
      rw [hsimpl, Real.sqrt_sq (abs_nonneg _)]
    calc
      u.ofLp x * (A x y * v.ofLp y)
          ≤ |u.ofLp x * (A x y * v.ofLp y)| := le_abs_self _
      _ = |A x y| * (|u.ofLp x| * |v.ofLp y|) := by rw [abs_mul, abs_mul]; ring
      _ = (√(|A x y| * p y / p x) * √(|A x y| * p x / p y)) * (|u.ofLp x| * |v.ofLp y|) := by
            rw [hprod]
      _ = (√(|A x y| * p y / p x) * |u.ofLp x|) *
            (√(|A x y| * p x / p y) * |v.ofLp y|) := by ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (κ × κ))
    (fun q ↦ √(|A q.1 q.2| * p q.2 / p q.1) * |u.ofLp q.1|)
    (fun q ↦ √(|A q.1 q.2| * p q.1 / p q.2) * |v.ofLp q.2|)
  have hlhs := sum_weighted_sq_le A hp hR hrow hu
  have hrhs : ∑ q : κ × κ, (√(|A q.1 q.2| * p q.1 / p q.2) * |v.ofLp q.2|) ^ 2 ≤ C := by
    have ht := sum_weighted_sq_le Aᵀ hp hC
      (fun y ↦ by simpa [transpose_apply] using hcol y) hv
    rw [Fintype.sum_prod_type, sum_comm]
    rw [Fintype.sum_prod_type] at ht
    simpa [transpose_apply] using ht
  calc
    ∑ x, ∑ y, u.ofLp x * (A x y * v.ofLp y)
        ≤ √(∑ q : κ × κ, (√(|A q.1 q.2| * p q.2 / p q.1) * |u.ofLp q.1|) ^ 2) *
            √(∑ q : κ × κ, (√(|A q.1 q.2| * p q.1 / p q.2) * |v.ofLp q.2|) ^ 2) :=
          h1.trans hcs
    _ ≤ √R * √C := mul_le_mul (Real.sqrt_le_sqrt hlhs) (Real.sqrt_le_sqrt hrhs)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = √(R * C) := (Real.sqrt_mul hR C).symm

/-- Symmetric specialization of the weighted Schur test: if `A` is symmetric and
`∑ y, |A x y| * p y ≤ K * p x` for positive weights `p`, then
`‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ K`. -/
theorem opNorm_toEuclideanCLM_le_of_symm_pos_weights {A : Matrix κ κ ℝ} (hSymm : A.IsSymm)
    {p : κ → ℝ} (hp : ∀ x, 0 < p x) {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ x, ∑ y, |A x y| * p y ≤ K * p x) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ K := by
  have hcol : ∀ y, ∑ x, |A x y| * p x ≤ K * p y := fun y ↦ by
    simpa only [hSymm.apply _ y] using hrow y
  exact (opNorm_toEuclideanCLM_le_of_pos_weights A hp hK hK hrow hcol).trans_eq
    (Real.sqrt_mul_self hK)

/-- Entrywise comparison for nonnegative real matrices: if `0 ≤ A x y ≤ B x y` for all `x, y`,
then `‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖toEuclideanCLM (𝕜 := ℝ) B‖`. -/
theorem opNorm_toEuclideanCLM_mono_of_nonneg {A B : Matrix κ κ ℝ}
    (hA : ∀ x y, 0 ≤ A x y) (hAB : ∀ x y, A x y ≤ B x y) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
  refine opNorm_toEuclideanCLM_le_of_inner A (norm_nonneg _) fun u v hu hv ↦ ?_
  have habs := inner_toEuclideanCLM_le_absVec hA u v
  have hle : inner ℝ (absVec u) (toEuclideanCLM (𝕜 := ℝ) A (absVec v)) ≤
      inner ℝ (absVec u) (toEuclideanCLM (𝕜 := ℝ) B (absVec v)) := by
    simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, absVec_apply]
    refine sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hAB x y) (abs_nonneg _)) (abs_nonneg _)
  exact habs.trans (hle.trans ((le_abs_self _).trans
    (abs_inner_toEuclideanCLM_le_opNorm B (norm_absVec_le hu) (norm_absVec_le hv))))

private theorem inner_toEuclideanCLM_symm {M : Matrix κ κ ℝ} (hSymm : M.IsSymm)
    (u v : EuclideanSpace ℝ κ) :
    inner ℝ u (toEuclideanCLM (𝕜 := ℝ) M v) = inner ℝ v (toEuclideanCLM (𝕜 := ℝ) M u) := by
  simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ ↦ sum_congr rfl fun x _ ↦ ?_
  rw [hSymm.apply x y]
  ring

private theorem inner_toEuclideanCLM_nonneg_of_nonneg {M : Matrix κ κ ℝ}
    (hNonneg : ∀ x y, 0 ≤ M x y) {u v : EuclideanSpace ℝ κ}
    (hu : ∀ x, 0 ≤ u.ofLp x) (hv : ∀ y, 0 ≤ v.ofLp y) :
    0 ≤ inner ℝ u (toEuclideanCLM (𝕜 := ℝ) M v) := by
  simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum]
  exact sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦
    mul_nonneg (hu x) (mul_nonneg (hNonneg x y) (hv y))

/-- Every finite real symmetric nonnegative matrix on a nonempty index type admits a nonnegative
unit eigenvector achieving its Euclidean operator norm. -/
theorem exists_unit_nonneg_inner_eq_opNorm [Nonempty κ] {M : Matrix κ κ ℝ}
    (hSymm : M.IsSymm) (hNonneg : ∀ x y, 0 ≤ M x y) :
    ∃ δ : EuclideanSpace ℝ κ, ‖δ‖ = 1 ∧ (∀ x, 0 ≤ δ.ofLp x) ∧
      toEuclideanCLM (𝕜 := ℝ) M δ = ‖toEuclideanCLM (𝕜 := ℝ) M‖ • δ ∧
      inner ℝ δ (toEuclideanCLM (𝕜 := ℝ) M δ) = ‖toEuclideanCLM (𝕜 := ℝ) M‖ := by
  set T := toEuclideanCLM (𝕜 := ℝ) M
  rcases (norm_nonneg T).eq_or_lt with hT0 | hTpos
  · have hTzero : T = 0 := norm_eq_zero.mp hT0.symm
    let x₀ : κ := Classical.arbitrary κ
    let δ : EuclideanSpace ℝ κ := WithLp.toLp 2 fun x ↦ if x = x₀ then 1 else 0
    have hδ_norm : ‖δ‖ = 1 := by
      have hsq : ‖δ‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        rw [sum_eq_single x₀ (fun x _ hx ↦ by simp [δ, hx]) (fun h ↦ (h (mem_univ x₀)).elim)]
        simp [δ]
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)
    refine ⟨δ, hδ_norm, fun x ↦ ?_, ?_, ?_⟩
    · dsimp only [δ]
      split_ifs <;> positivity
    · rw [hTzero]; simp
    · rw [hTzero]; simp
  · let B : Set (EuclideanSpace ℝ κ) := {v | ‖v‖ ≤ 1}
    have hB_eq : B = Metric.closedBall 0 1 := by
      ext v; simp [B, Metric.mem_closedBall, dist_zero_right]
    have hB_comp : IsCompact B := hB_eq ▸ isCompact_closedBall (0 : EuclideanSpace ℝ κ) 1
    have hB_ne : B.Nonempty := ⟨0, by change ‖(0 : EuclideanSpace ℝ κ)‖ ≤ 1; simp⟩
    let φ : EuclideanSpace ℝ κ × EuclideanSpace ℝ κ → ℝ := fun p ↦ inner ℝ p.1 (T p.2)
    have hφ_cont : Continuous φ := continuous_fst.inner (T.continuous.comp continuous_snd)
    obtain ⟨⟨u₀, v₀⟩, huv₀, hmax⟩ :=
      (hB_comp.prod hB_comp).exists_isMaxOn (hB_ne.prod hB_ne) hφ_cont.continuousOn
    have hmax' := isMaxOn_iff.mp hmax
    have hu₀ : ‖u₀‖ ≤ 1 := huv₀.1
    have hv₀ : ‖v₀‖ ≤ 1 := huv₀.2
    have hφ0 : 0 ≤ φ (u₀, v₀) := by
      have h00 : ((0 : EuclideanSpace ℝ κ), (0 : EuclideanSpace ℝ κ)) ∈ B ×ˢ B :=
        ⟨by change ‖(0 : EuclideanSpace ℝ κ)‖ ≤ 1; simp,
          by change ‖(0 : EuclideanSpace ℝ κ)‖ ≤ 1; simp⟩
      have hm := hmax' (0, 0) h00
      simpa [φ] using hm
    have hle_φ : ‖T‖ ≤ φ (u₀, v₀) :=
      opNorm_toEuclideanCLM_le_of_inner M hφ0 fun u v hu hv ↦ hmax' (u, v) ⟨hu, hv⟩
    let u₁ := absVec u₀
    let v₁ := absVec v₀
    have hu₁ : ‖u₁‖ ≤ 1 := norm_absVec_le hu₀
    have hv₁ : ‖v₁‖ ≤ 1 := norm_absVec_le hv₀
    have hu₁_nn : ∀ x, 0 ≤ u₁.ofLp x := fun _ ↦ abs_nonneg _
    have hv₁_nn : ∀ y, 0 ≤ v₁.ofLp y := fun _ ↦ abs_nonneg _
    have h_eq : inner ℝ u₁ (T v₁) = ‖T‖ := by
      refine le_antisymm ?_ (hle_φ.trans (inner_toEuclideanCLM_le_absVec hNonneg u₀ v₀))
      exact (le_abs_self _).trans (abs_inner_toEuclideanCLM_le_opNorm M hu₁ hv₁)
    have h_eig_pair : ∀ (a b : EuclideanSpace ℝ κ), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        inner ℝ a (T b) = ‖T‖ → T b = ‖T‖ • a := by
      intro a b ha hb hab
      have hTb : ‖T b‖ ≤ ‖T‖ := (T.le_opNorm b).trans (mul_le_of_le_one_right hTpos.le hb)
      have hTb_sq : ‖T b‖ ^ 2 ≤ ‖T‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) hTpos.le).2 hTb
      have ha_sq : ‖‖T‖ • a‖ ^ 2 ≤ ‖T‖ ^ 2 := by
        rw [norm_smul, Real.norm_of_nonneg hTpos.le, mul_pow]
        exact mul_le_of_le_one_right (sq_nonneg _) ((sq_le_one_iff₀ (norm_nonneg _)).2 ha)
      have hsub : ‖T b - ‖T‖ • a‖ ^ 2 ≤ 0 := by
        rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, hab]
        linarith
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
        (le_antisymm hsub (sq_nonneg _))))
    have hTv₁ : T v₁ = ‖T‖ • u₁ := h_eig_pair u₁ v₁ hu₁ hv₁ h_eq
    have hTu₁ : T u₁ = ‖T‖ • v₁ :=
      h_eig_pair v₁ u₁ hv₁ hu₁ ((inner_toEuclideanCLM_symm hSymm v₁ u₁).trans h_eq)
    let w := u₁ + v₁
    have hTw : T w = ‖T‖ • w := by
      dsimp only [w]
      rw [map_add, hTu₁, hTv₁, smul_add, add_comm]
    have hw_inner_pos : 0 < inner ℝ w (T w) := by
      have h11 := inner_toEuclideanCLM_nonneg_of_nonneg hNonneg hu₁_nn hu₁_nn
      have h22 := inner_toEuclideanCLM_nonneg_of_nonneg hNonneg hv₁_nn hv₁_nn
      have h21 : inner ℝ v₁ (T u₁) = ‖T‖ := (inner_toEuclideanCLM_symm hSymm v₁ u₁).trans h_eq
      dsimp only [w]
      rw [map_add, inner_add_left, inner_add_right, inner_add_right]
      linarith
    have hw_ne : w ≠ 0 := fun hw0 ↦ by simp [hw0] at hw_inner_pos
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    let δ : EuclideanSpace ℝ κ := (‖w‖)⁻¹ • w
    have hδ_norm : ‖δ‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hw_pos.le), inv_mul_cancel₀ hw_pos.ne']
    have hTδ : T δ = ‖T‖ • δ := by
      dsimp only [δ]
      rw [map_smul, hTw, smul_comm]
    refine ⟨δ, hδ_norm, fun x ↦ ?_, hTδ, ?_⟩
    · exact mul_nonneg (inv_nonneg.mpr hw_pos.le) (add_nonneg (hu₁_nn x) (hv₁_nn x))
    · rw [hTδ, real_inner_smul_right, real_inner_self_eq_norm_sq, hδ_norm, one_pow, mul_one]

end WeightedSchur

/-! ### 2. Off-Diagonal All-Ones Matrix and Kronecker Product Operator Norm -/

section KroneckerAndOffDiag

/-- The off-diagonal all-ones matrix `J - I` on `κ`, with entry `1` for `x ≠ y` and `0` on the
diagonal. -/
@[expose] def offDiagOne (κ : Type*) [DecidableEq κ] : Matrix κ κ ℝ :=
  of fun x y ↦ if x ≠ y then 1 else 0

/-- Coordinate evaluation of `offDiagOne`. -/
theorem offDiagOne_apply {κ : Type*} [DecidableEq κ] (x y : κ) :
    offDiagOne κ x y = if x ≠ y then 1 else 0 :=
  rfl

/-- Diagonal entries of `offDiagOne` vanish. -/
@[simp]
theorem offDiagOne_self {κ : Type*} [DecidableEq κ] (x : κ) :
    offDiagOne κ x x = 0 := by
  simp [offDiagOne]

/-- `offDiagOne κ` is symmetric. -/
theorem isSymm_offDiagOne (κ : Type*) [DecidableEq κ] : (offDiagOne κ).IsSymm := by
  ext x y
  dsimp only [transpose_apply, offDiagOne, of_apply]
  by_cases h : x = y
  · subst h; simp
  · have h' : y ≠ x := Ne.symm h
    simp [h, h']

/-- `offDiagOne κ` has nonnegative entries. -/
theorem offDiagOne_nonneg {κ : Type*} [DecidableEq κ] (x y : κ) : 0 ≤ offDiagOne κ x y := by
  simp only [offDiagOne_apply]
  split_ifs <;> positivity

/-- On a nonempty finite type `κ`, the Euclidean operator norm of `offDiagOne κ` equals
`(Fintype.card κ : ℝ) - 1`. -/
theorem opNorm_offDiagOne (κ : Type*) [Nonempty κ] [Fintype κ] [DecidableEq κ] :
    ‖toEuclideanCLM (𝕜 := ℝ) (offDiagOne κ)‖ = (Fintype.card κ : ℝ) - 1 := by
  have hcard1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos (α := κ)
  have hrow_eq : ∀ x : κ, ∑ y : κ, offDiagOne κ x y = (Fintype.card κ : ℝ) - 1 := fun x ↦ by
    have hsplit : ∑ y : κ, offDiagOne κ x y = ∑ _y ∈ univ.erase x, (1 : ℝ) := by
      rw [← add_sum_erase _ _ (mem_univ x)]
      simp only [offDiagOne_self, zero_add]
      refine sum_congr rfl fun y hy ↦ ?_
      have hne : x ≠ y := (ne_of_mem_erase hy).symm
      simp [offDiagOne, hne]
    rw [hsplit, sum_const, card_erase_of_mem (mem_univ x), card_univ, nsmul_eq_mul, mul_one]
    have hpos : 1 ≤ Fintype.card κ := Fintype.card_pos
    rw [Nat.cast_sub hpos, Nat.cast_one]
  refine le_antisymm ?_ ?_
  · refine opNorm_toEuclideanCLM_le_of_symm_pos_weights (isSymm_offDiagOne κ)
      (p := fun _ ↦ 1) (fun _ ↦ zero_lt_one) (by linarith) fun x ↦ ?_
    simp only [mul_one, abs_of_nonneg (offDiagOne_nonneg x _), hrow_eq x, le_refl]
  · have hpos : (0 : ℝ) < Fintype.card κ := by positivity
    let u : EuclideanSpace ℝ κ := WithLp.toLp 2 fun _ ↦ 1 / √(Fintype.card κ : ℝ)
    have hu : ‖u‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one]
      simp only [u, sum_const, card_univ, nsmul_eq_mul, one_div, inv_pow, Real.sq_sqrt hpos.le,
        mul_inv_cancel₀ hpos.ne', le_refl]
    have hval : inner ℝ u (toEuclideanCLM (𝕜 := ℝ) (offDiagOne κ) u) =
        (Fintype.card κ : ℝ) - 1 := by
      rw [inner_toEuclideanCLM]
      simp only [u, dotProduct, mulVec]
      calc
        ∑ x : κ, 1 / √(Fintype.card κ : ℝ) *
            ∑ y : κ, offDiagOne κ x y * (1 / √(Fintype.card κ : ℝ))
            = ∑ x : κ, (1 / √(Fintype.card κ : ℝ)) ^ 2 * ∑ y : κ, offDiagOne κ x y := by
              refine sum_congr rfl fun x _ ↦ ?_
              rw [← sum_mul]
              ring
        _ = (Fintype.card κ : ℝ) * ((1 / √(Fintype.card κ : ℝ)) ^ 2 *
              ((Fintype.card κ : ℝ) - 1)) := by
              simp only [hrow_eq, sum_const, card_univ, nsmul_eq_mul]
        _ = (Fintype.card κ : ℝ) - 1 := by
              rw [one_div, inv_pow, Real.sq_sqrt hpos.le]
              field_simp [hpos.ne']
    exact hval ▸ (le_abs_self _).trans (abs_inner_toEuclideanCLM_le_opNorm (offDiagOne κ) hu hu)

/-- Multiplicativity of the Euclidean operator norm under the Kronecker product of finite real
symmetric nonnegative matrices. -/
theorem opNorm_kronecker_of_symm_nonneg {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℝ} {B : Matrix β β ℝ}
    (hAs : A.IsSymm) (hAn : ∀ i j, 0 ≤ A i j)
    (hBs : B.IsSymm) (hBn : ∀ k l, 0 ≤ B k l) :
    ‖toEuclideanCLM (𝕜 := ℝ) (A ⊗ₖ B)‖ =
      ‖toEuclideanCLM (𝕜 := ℝ) A‖ * ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
  by_cases hα : Nonempty α
  · by_cases hβ : Nonempty β
    · refine le_antisymm ?_ ?_
      · refine opNorm_toEuclideanCLM_le_of_inner (A ⊗ₖ B)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun u v hu hv ↦ ?_
        let uSlice (a : α) : EuclideanSpace ℝ β := WithLp.toLp 2 fun b ↦ u.ofLp (a, b)
        let vSlice (a : α) : EuclideanSpace ℝ β := WithLp.toLp 2 fun b ↦ v.ofLp (a, b)
        let uNorm : EuclideanSpace ℝ α := WithLp.toLp 2 fun a ↦ ‖uSlice a‖
        let vNorm : EuclideanSpace ℝ α := WithLp.toLp 2 fun a ↦ ‖vSlice a‖
        have huNorm : ‖uNorm‖ ≤ 1 := by
          rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hu ⊢
          simpa only [uNorm, uSlice, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type] using hu
        have hvNorm : ‖vNorm‖ ≤ 1 := by
          rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hv ⊢
          simpa only [vNorm, vSlice, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type] using hv
        have hexpand : inner ℝ u (toEuclideanCLM (𝕜 := ℝ) (A ⊗ₖ B) v) =
            ∑ a₁ : α, ∑ a₂ : α, A a₁ a₂ *
              inner ℝ (uSlice a₁) (toEuclideanCLM (𝕜 := ℝ) B (vSlice a₂)) := by
          simp only [inner_toEuclideanCLM, dotProduct, mulVec, kroneckerMap_apply,
            Fintype.sum_prod_type, mul_sum, uSlice, vSlice]
          refine sum_congr rfl fun a₁ _ ↦ ?_
          rw [sum_comm]
          refine sum_congr rfl fun a₂ _ ↦ ?_
          exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
        rw [hexpand]
        calc
          ∑ a₁ : α, ∑ a₂ : α, A a₁ a₂ *
              inner ℝ (uSlice a₁) (toEuclideanCLM (𝕜 := ℝ) B (vSlice a₂))
              ≤ ∑ a₁ : α, ∑ a₂ : α, A a₁ a₂ *
                  (‖toEuclideanCLM (𝕜 := ℝ) B‖ * (‖uSlice a₁‖ * ‖vSlice a₂‖)) := by
                refine sum_le_sum fun a₁ _ ↦ sum_le_sum fun a₂ _ ↦
                  mul_le_mul_of_nonneg_left ?_ (hAn a₁ a₂)
                have hcs := (le_abs_self _).trans (abs_real_inner_le_norm (uSlice a₁)
                  (toEuclideanCLM (𝕜 := ℝ) B (vSlice a₂)))
                have hop := (toEuclideanCLM (𝕜 := ℝ) B).le_opNorm (vSlice a₂)
                exact hcs.trans ((mul_le_mul_of_nonneg_left hop (norm_nonneg _)).trans_eq (by ring))
          _ = ‖toEuclideanCLM (𝕜 := ℝ) B‖ *
                inner ℝ uNorm (toEuclideanCLM (𝕜 := ℝ) A vNorm) := by
                rw [inner_toEuclideanCLM]
                simp only [dotProduct, mulVec, mul_sum, uNorm, vNorm]
                exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
          _ ≤ ‖toEuclideanCLM (𝕜 := ℝ) A‖ * ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_right
                  ((le_abs_self _).trans
                    (abs_inner_toEuclideanCLM_le_opNorm A huNorm hvNorm))
                  (norm_nonneg _)
      · obtain ⟨δA, hδA_norm, _, _, hδA_eq⟩ := exists_unit_nonneg_inner_eq_opNorm hAs hAn
        obtain ⟨δB, hδB_norm, _, _, hδB_eq⟩ := exists_unit_nonneg_inner_eq_opNorm hBs hBn
        let δ : EuclideanSpace ℝ (α × β) := WithLp.toLp 2 fun p ↦ δA.ofLp p.1 * δB.ofLp p.2
        have hδ_norm : ‖δ‖ ≤ 1 := by
          rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one]
          have hA1 : ∑ a : α, δA.ofLp a ^ 2 = 1 := by
            rw [← EuclideanSpace.real_norm_sq_eq, hδA_norm, one_pow]
          have hB1 : ∑ b : β, δB.ofLp b ^ 2 = 1 := by
            rw [← EuclideanSpace.real_norm_sq_eq, hδB_norm, one_pow]
          simp only [δ, Fintype.sum_prod_type, mul_pow, ← mul_sum, hB1, mul_one, hA1, le_refl]
        have hδ_val : inner ℝ δ (toEuclideanCLM (𝕜 := ℝ) (A ⊗ₖ B) δ) =
            ‖toEuclideanCLM (𝕜 := ℝ) A‖ * ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
          rw [← hδA_eq, ← hδB_eq]
          simp only [inner_toEuclideanCLM, dotProduct, mulVec, kroneckerMap_apply,
            Fintype.sum_prod_type, δ]
          rw [sum_mul]
          refine sum_congr rfl fun a₁ _ ↦ ?_
          rw [mul_sum]
          refine sum_congr rfl fun b₁ _ ↦ ?_
          simp only [mul_sum, sum_mul]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
        exact hδ_val ▸ (le_abs_self _).trans
          (abs_inner_toEuclideanCLM_le_opNorm (A ⊗ₖ B) hδ_norm hδ_norm)
    · have : IsEmpty β := not_nonempty_iff.mp hβ
      have hB0 : ‖toEuclideanCLM (𝕜 := ℝ) B‖ = 0 := by
        refine le_antisymm ?_ (norm_nonneg _)
        refine opNorm_toEuclideanCLM_le_of_inner B le_rfl fun _ _ _ _ ↦ ?_
        simp [inner_toEuclideanCLM, dotProduct]
      have hAB0 : ‖toEuclideanCLM (𝕜 := ℝ) (A ⊗ₖ B)‖ = 0 := by
        refine le_antisymm ?_ (norm_nonneg _)
        refine opNorm_toEuclideanCLM_le_of_inner (A ⊗ₖ B) le_rfl fun _ _ _ _ ↦ ?_
        simp [inner_toEuclideanCLM, dotProduct]
      rw [hB0, hAB0, mul_zero]
  · have : IsEmpty α := not_nonempty_iff.mp hα
    have hA0 : ‖toEuclideanCLM (𝕜 := ℝ) A‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine opNorm_toEuclideanCLM_le_of_inner A le_rfl fun _ _ _ _ ↦ ?_
      simp [inner_toEuclideanCLM, dotProduct]
    have hAB0 : ‖toEuclideanCLM (𝕜 := ℝ) (A ⊗ₖ B)‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine opNorm_toEuclideanCLM_le_of_inner (A ⊗ₖ B) le_rfl fun _ _ _ _ ↦ ?_
      simp [inner_toEuclideanCLM, dotProduct]
    rw [hA0, hAB0, zero_mul]

end KroneckerAndOffDiag

/-! ### 3. Choi's Hilbert Matrix Operator Norm Bound (`‖H_m‖ ≤ π`) -/

section HilbertMatrix

/-- The `m × m` **Hilbert matrix** `H_m`, with entries `H_m[j, k] = 1 / ((j : ℝ) + (k : ℝ) + 1)`
for `j, k : Fin m`. -/
@[expose] noncomputable def hilbertMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  of fun j k ↦ 1 / ((j : ℝ) + (k : ℝ) + 1)

/-- Entry evaluation of `hilbertMatrix m`. -/
theorem hilbertMatrix_apply (m : ℕ) (j k : Fin m) :
    hilbertMatrix m j k = 1 / ((j : ℝ) + (k : ℝ) + 1) :=
  rfl

/-- The Hilbert matrix `hilbertMatrix m` is symmetric. -/
theorem isSymm_hilbertMatrix (m : ℕ) : (hilbertMatrix m).IsSymm := by
  ext j k
  simp only [transpose_apply, hilbertMatrix_apply]
  ring

/-- Every entry of `hilbertMatrix m` is strictly positive. -/
theorem hilbertMatrix_pos (m : ℕ) (j k : Fin m) : 0 < hilbertMatrix m j k := by
  rw [hilbertMatrix_apply]
  positivity

private theorem choi_arctan_step {a : ℝ} (ha : 0 < a) (k : ℕ) :
    1 / ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2)) ≤
      (2 / √a) * (Real.arctan √(((k : ℝ) + 1) / a) - Real.arctan √((k : ℝ) / a)) := by
  set u : ℝ := √(((k : ℝ) + 1) / a)
  set v : ℝ := √((k : ℝ) / a)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  have hu_sq : u ^ 2 = ((k : ℝ) + 1) / a := Real.sq_sqrt (by positivity)
  have hv_sq : v ^ 2 = (k : ℝ) / a := Real.sq_sqrt (by positivity)
  have hv_le_u : v ≤ u := Real.sqrt_le_sqrt (by gcongr; linarith)
  have hθ_nn : 0 ≤ Real.arctan u - Real.arctan v :=
    sub_nonneg.mpr (Real.arctan_mono hv_le_u)
  have hsin_le : Real.sin (Real.arctan u - Real.arctan v) ≤ Real.arctan u - Real.arctan v :=
    Real.sin_le hθ_nn
  have hsin_eq : Real.sin (Real.arctan u - Real.arctan v) =
      (u - v) / (√(1 + u ^ 2) * √(1 + v ^ 2)) := by
    rw [Real.sin_sub, Real.sin_arctan, Real.cos_arctan, Real.cos_arctan, Real.sin_arctan]
    ring
  have h1u : 1 + u ^ 2 = (a + (k : ℝ) + 1) / a := by rw [hu_sq]; field_simp [ha.ne']; ring
  have h1v : 1 + v ^ 2 = (a + (k : ℝ)) / a := by rw [hv_sq]; field_simp [ha.ne']
  have h_num : u - v = 1 / (√a * (√((k : ℝ) + 1) + √(k : ℝ))) := by
    have hsum_pos : 0 < √((k : ℝ) + 1) + √(k : ℝ) := by positivity
    rw [show u = √((k : ℝ) + 1) / √a from Real.sqrt_div (by positivity) a,
      show v = √(k : ℝ) / √a from Real.sqrt_div hk0 a]
    have hdiff : (√((k : ℝ) + 1) - √(k : ℝ)) * (√((k : ℝ) + 1) + √(k : ℝ)) = 1 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity), Real.sq_sqrt hk0]
    field_simp [hsa.ne', hsum_pos.ne']
    linarith
  have h_den_eq : √(1 + u ^ 2) * √(1 + v ^ 2) = √((a + (k : ℝ) + 1) * (a + (k : ℝ))) / a := by
    rw [h1u, h1v, Real.sqrt_div (by positivity) a, Real.sqrt_div (by positivity) a,
      div_mul_div_comm, ← Real.sqrt_mul (by positivity), Real.mul_self_sqrt ha.le]
  have h_lhs_le : √((k : ℝ) + 1) + √(k : ℝ) ≤ 2 * √((k : ℝ) + 1 / 2) := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    have hcs : 2 * (√((k : ℝ) + 1) * √(k : ℝ)) ≤ 2 * (k : ℝ) + 1 := by
      have h2 : (2 * (√((k : ℝ) + 1) * √(k : ℝ))) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hk0]
        linarith
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp h2
    rw [add_sq, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hk0,
      Real.sq_sqrt (by positivity)]
    linarith
  have h_ak_le : √((a + (k : ℝ) + 1) * (a + (k : ℝ))) ≤ a + ((k : ℝ) + 1 / 2) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith
  have h_prod_le : (√((k : ℝ) + 1) + √(k : ℝ)) * √((a + (k : ℝ) + 1) * (a + (k : ℝ))) ≤
      2 * ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2)) := by
    calc
      (√((k : ℝ) + 1) + √(k : ℝ)) * √((a + (k : ℝ) + 1) * (a + (k : ℝ)))
          ≤ (2 * √((k : ℝ) + 1 / 2)) * (a + ((k : ℝ) + 1 / 2)) :=
            mul_le_mul h_lhs_le h_ak_le (by positivity) (by positivity)
      _ = 2 * ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2)) := by ring
  have h_alg : (2 / √a) * ((u - v) / (√(1 + u ^ 2) * √(1 + v ^ 2))) =
      2 / ((√((k : ℝ) + 1) + √(k : ℝ)) * √((a + (k : ℝ) + 1) * (a + (k : ℝ)))) := by
    rw [h_num, h_den_eq]
    have hsum_pos : √((k : ℝ) + 1) + √(k : ℝ) ≠ 0 := by positivity
    have hrad_pos : √((a + (k : ℝ) + 1) * (a + (k : ℝ))) ≠ 0 := by positivity
    have hsqa : √a * √a = a := Real.mul_self_sqrt ha.le
    field_simp [hsa.ne', ha.ne', hsum_pos, hrad_pos]
    linarith
  calc
    1 / ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2))
        = 2 / (2 * ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2))) := by
          have hd1 : a + ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
          have hd2 : √((k : ℝ) + 1 / 2) ≠ 0 := by positivity
          field_simp [hd1, hd2]
    _ ≤ 2 / ((√((k : ℝ) + 1) + √(k : ℝ)) * √((a + (k : ℝ) + 1) * (a + (k : ℝ)))) :=
          div_le_div_of_nonneg_left zero_le_two (by positivity) h_prod_le
    _ = (2 / √a) * Real.sin (Real.arctan u - Real.arctan v) := by rw [hsin_eq, h_alg]
    _ ≤ (2 / √a) * (Real.arctan u - Real.arctan v) :=
          mul_le_mul_of_nonneg_left hsin_le (by positivity)

/-- **Choi's Hilbert matrix operator-norm bound**: for every `1 ≤ m`, the Euclidean `ℓ²` operator
norm of the `m × m` Hilbert matrix is strictly less than `π`. -/
theorem opNorm_hilbertMatrix_lt_pi {m : ℕ} (hm : 1 ≤ m) :
    ‖toEuclideanCLM (𝕜 := ℝ) (hilbertMatrix m)‖ < Real.pi := by
  have _ := hm
  let p : Fin m → ℝ := fun j ↦ 1 / √((j : ℝ) + 1 / 2)
  have hp : ∀ j : Fin m, 0 < p j := fun _ ↦ by dsimp only [p]; positivity
  let K : ℝ := 2 * Real.arctan √((m : ℝ) * 2)
  have hK_nn : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg zero_le_two (Real.arctan_nonneg.mpr (Real.sqrt_nonneg _))
  have hK_lt : K < Real.pi := by
    have hlt := Real.arctan_lt_pi_div_two √((m : ℝ) * 2)
    dsimp only [K]
    linarith
  refine (opNorm_toEuclideanCLM_le_of_symm_pos_weights (isSymm_hilbertMatrix m) hp hK_nn
    fun j ↦ ?_).trans_lt hK_lt
  set a : ℝ := (j : ℝ) + 1 / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsum_eq : ∑ k : Fin m, |hilbertMatrix m j k| * p k =
      ∑ k ∈ range m, 1 / ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2)) := by
    refine sum_bij (fun (k : Fin m) _ ↦ k.val)
      (fun k _ ↦ mem_range.mpr k.isLt)
      (fun _ _ _ _ h ↦ Fin.ext h)
      (fun k hk ↦ ⟨⟨k, mem_range.mp hk⟩, mem_univ _, rfl⟩)
      fun k _ ↦ ?_
    have hpos_d : 0 < (j : ℝ) + (k : ℝ) + 1 := by positivity
    simp only [hilbertMatrix, of_apply, p, abs_of_pos (one_div_pos.mpr hpos_d)]
    have hden : (j : ℝ) + (k : ℝ) + 1 = a + ((k : ℝ) + 1 / 2) := by dsimp only [a]; ring
    rw [hden, one_div_mul_one_div]
  rw [hsum_eq]
  let G : ℕ → ℝ := fun k ↦ (2 / √a) * Real.arctan √((k : ℝ) / a)
  have htel : ∑ k ∈ range m, (G (k + 1) - G k) = G m - G 0 := sum_range_sub G m
  have hG0 : G 0 = 0 := by simp [G]
  have hGm : G m ≤ K * p j := by
    have ha_ge : 1 / 2 ≤ a := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      dsimp only [a]; linarith
    have hma : (m : ℝ) / a ≤ (m : ℝ) * 2 := by
      rw [div_le_iff₀ ha]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have harc : Real.arctan √((m : ℝ) / a) ≤ Real.arctan √((m : ℝ) * 2) :=
      Real.arctan_mono (Real.sqrt_le_sqrt hma)
    dsimp only [G, K, p]
    calc
      (2 / √a) * Real.arctan √((m : ℝ) / a)
          ≤ (2 / √a) * Real.arctan √((m : ℝ) * 2) :=
            mul_le_mul_of_nonneg_left harc (by positivity)
      _ = 2 * Real.arctan √((m : ℝ) * 2) * (1 / √a) := by ring
  calc
    ∑ k ∈ range m, 1 / ((a + ((k : ℝ) + 1 / 2)) * √((k : ℝ) + 1 / 2))
        ≤ ∑ k ∈ range m, (G (k + 1) - G k) := by
          refine sum_le_sum fun k _ ↦ ?_
          simpa only [G, Nat.cast_add, Nat.cast_one, ← mul_sub] using choi_arctan_step ha k
    _ = G m := by rw [htel, hG0, sub_zero]
    _ ≤ K * p j := hGm

/-- **Choi's Hilbert matrix operator-norm bound** for all `m : ℕ`:
`‖toEuclideanCLM (𝕜 := ℝ) (hilbertMatrix m)‖ ≤ π`. -/
theorem opNorm_hilbertMatrix_le_pi (m : ℕ) :
    ‖toEuclideanCLM (𝕜 := ℝ) (hilbertMatrix m)‖ ≤ Real.pi := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine opNorm_toEuclideanCLM_le_of_inner (hilbertMatrix 0) Real.pi_pos.le fun _ _ _ _ ↦ ?_
    simp [inner_toEuclideanCLM, dotProduct, Real.pi_pos.le]
  · exact (opNorm_hilbertMatrix_lt_pi hm).le

end HilbertMatrix

/-! ### 4. Inverse-Distance Toeplitz Matrix and Interval-Masked Bounds -/

section InvDistMatrix

/-- The `m × m` inverse-distance Toeplitz matrix `A_m[i, j] = 1 / (|(i : ℝ) - (j : ℝ)| + 1)`. -/
@[expose] noncomputable def invDistMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  of fun i j ↦ 1 / (|(i : ℝ) - (j : ℝ)| + 1)

/-- Entry evaluation of `invDistMatrix m`. -/
theorem invDistMatrix_apply (m : ℕ) (i j : Fin m) :
    invDistMatrix m i j = 1 / (|(i : ℝ) - (j : ℝ)| + 1) :=
  rfl

/-- `invDistMatrix m` is symmetric. -/
theorem isSymm_invDistMatrix (m : ℕ) : (invDistMatrix m).IsSymm := by
  ext i j
  simp only [transpose_apply, invDistMatrix_apply, abs_sub_comm]

/-- Every entry of `invDistMatrix m` is strictly positive. -/
theorem invDistMatrix_pos (m : ℕ) (i j : Fin m) : 0 < invDistMatrix m i j := by
  rw [invDistMatrix_apply]
  have h : 0 < |(i : ℝ) - (j : ℝ)| + 1 := by positivity
  exact one_div_pos.mpr h

/-- Indicator matrix `intervalMask m r` on `Fin m` with entry `1` when `(x ≤ r ∧ r ≤ y)` or
`(y ≤ r ∧ r ≤ x)`, and `0` otherwise. -/
@[expose] def intervalMask (m : ℕ) (r : Fin m) : Matrix (Fin m) (Fin m) ℝ :=
  of fun x y ↦ if (x ≤ r ∧ r ≤ y) ∨ (y ≤ r ∧ r ≤ x) then 1 else 0

/-- Entry evaluation of `intervalMask m r`. -/
theorem intervalMask_apply (m : ℕ) (r x y : Fin m) :
    intervalMask m r x y = if (x ≤ r ∧ r ≤ y) ∨ (y ≤ r ∧ r ≤ x) then 1 else 0 :=
  rfl

/-- The diagonal entry of `intervalMask m r` at `r` equals `1`. -/
@[simp]
theorem intervalMask_self (m : ℕ) (r : Fin m) :
    intervalMask m r r r = 1 := by
  simp [intervalMask]

private theorem log_add_two_div_two_le_sum_range (L : ℕ) :
    Real.log (((L : ℝ) + 2) / 2) ≤ ∑ k ∈ range L, (1 / ((k : ℝ) + 2)) := by
  let F : ℕ → ℝ := fun k ↦ Real.log ((k : ℝ) + 2)
  have htel : ∑ k ∈ range L, (F (k + 1) - F k) = F L - F 0 := sum_range_sub F L
  have hF : F L - F 0 = Real.log (((L : ℝ) + 2) / 2) := by
    dsimp only [F]
    rw [Nat.cast_zero, zero_add, ← Real.log_div (by positivity) two_ne_zero]
  rw [← hF, ← htel]
  refine sum_le_sum fun k _ ↦ ?_
  dsimp only [F]
  have hkpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  rw [Nat.cast_add, Nat.cast_one, ← Real.log_div (by positivity) hkpos.ne']
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  have hsub : ((k : ℝ) + 1 + 2) / ((k : ℝ) + 2) - 1 = 1 / ((k : ℝ) + 2) := by
    field_simp [hkpos.ne']
    ring
  exact hsub.le

/-- **Harmonic lower bound for the off-diagonal inverse-distance matrix**: for every `m : ℕ`,
`Real.log m / 2 ≤ ‖toEuclideanCLM (𝕜 := ℝ) (invDistMatrix m - 1)‖`. -/
theorem log_div_two_le_opNorm_invDistMatrix_sub_one (m : ℕ) :
    Real.log (m : ℝ) / 2 ≤
      ‖toEuclideanCLM (𝕜 := ℝ) (invDistMatrix m - (1 : Matrix (Fin m) (Fin m) ℝ))‖ := by
  rcases m with _ | _ | n
  · rw [Nat.cast_zero, Real.log_zero, zero_div]
    exact norm_nonneg (toEuclideanCLM (𝕜 := ℝ) (invDistMatrix 0 - (1 : Matrix (Fin 0) (Fin 0) ℝ)))
  · rw [Nat.cast_one, Real.log_one, zero_div]
    exact norm_nonneg (toEuclideanCLM (𝕜 := ℝ) (invDistMatrix 1 - (1 : Matrix (Fin 1) (Fin 1) ℝ)))
  · set m := n + 2
    have hm_pos : (0 : ℝ) < m := by positivity
    let u : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun _ ↦ 1 / √(m : ℝ)
    have hu : ‖u‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one]
      simp only [u, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_div, inv_pow,
        Real.sq_sqrt hm_pos.le, mul_inv_cancel₀ hm_pos.ne', le_refl]
    have hrow : ∀ i : Fin m, Real.log (m : ℝ) / 2 ≤
        ∑ j : Fin m, (invDistMatrix m - 1) i j := fun i ↦ by
      have hdiag : (invDistMatrix m - 1) i i = 0 := by simp [invDistMatrix]
      have hoff : ∀ j : Fin m, j ≠ i → (invDistMatrix m - 1) i j =
          1 / (|(i : ℝ) - (j : ℝ)| + 1) := fun j hj ↦ by
        simp [invDistMatrix, hj.symm]
      have hleft_sum : ∑ k ∈ range i.val, (1 / ((k : ℝ) + 2)) ≤
          ∑ j : Fin m with j.val < i.val, (invDistMatrix m - 1) i j := by
        refine le_of_eq ?_
        refine sum_bij (fun (k : ℕ) (hk : k ∈ range i.val) ↦
            (⟨i.val - 1 - k, by have := mem_range.mp hk; omega⟩ : Fin m))
          (fun _ hk ↦ by simp only [mem_filter, mem_univ, true_and]; have := mem_range.mp hk; omega)
          (fun _ hk₁ _ hk₂ h ↦ by
            have h1 := mem_range.mp hk₁
            have h2 := mem_range.mp hk₂
            have hv := congrArg Fin.val h
            dsimp only at hv
            omega)
          (fun j hj ↦ by
            have hjlt : j.val < i.val := (mem_filter.mp hj).2
            refine ⟨i.val - 1 - j.val, mem_range.mpr (by omega), ?_⟩
            ext; dsimp only; omega)
          (fun k hk ↦ by
            have hklt : k < i.val := mem_range.mp hk
            have hne : (⟨i.val - 1 - k, by omega⟩ : Fin m) ≠ i := by
              intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
            rw [hoff _ hne]
            have hsub : (i : ℝ) - ((i.val - 1 - k : ℕ) : ℝ) = (k : ℝ) + 1 := by
              have hnat : (i.val - 1 - k) + (k + 1) = i.val := by omega
              have hcast : ((i.val - 1 - k : ℕ) : ℝ) + ((k : ℝ) + 1) = (i : ℝ) := by
                exact_mod_cast hnat
              linarith
            rw [show ((⟨i.val - 1 - k, by omega⟩ : Fin m) : ℝ) =
              ((i.val - 1 - k : ℕ) : ℝ) from rfl, hsub, abs_of_nonneg (by positivity)]
            ring)
      have hright_sum : ∑ k ∈ range (m - 1 - i.val), (1 / ((k : ℝ) + 2)) ≤
          ∑ j : Fin m with i.val < j.val, (invDistMatrix m - 1) i j := by
        refine le_of_eq ?_
        refine sum_bij (fun (k : ℕ) (hk : k ∈ range (m - 1 - i.val)) ↦
            (⟨i.val + 1 + k, by have := mem_range.mp hk; omega⟩ : Fin m))
          (fun _ _ ↦ by simp only [mem_filter, mem_univ, true_and]; omega)
          (fun _ _ _ _ h ↦ by
            have hv := congrArg Fin.val h
            dsimp only at hv
            omega)
          (fun j hj ↦ by
            have hjgt : i.val < j.val := (mem_filter.mp hj).2
            refine ⟨j.val - 1 - i.val, mem_range.mpr (by omega), ?_⟩
            ext; dsimp only; omega)
          (fun k hk ↦ by
            have hklt : k < m - 1 - i.val := mem_range.mp hk
            have hne : (⟨i.val + 1 + k, by omega⟩ : Fin m) ≠ i := by
              intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
            rw [hoff _ hne]
            have hsub : (i : ℝ) - ((i.val + 1 + k : ℕ) : ℝ) = -((k : ℝ) + 1) := by
              push_cast; ring
            rw [show ((⟨i.val + 1 + k, by omega⟩ : Fin m) : ℝ) =
              ((i.val + 1 + k : ℕ) : ℝ) from rfl, hsub, abs_neg, abs_of_nonneg (by positivity)]
            ring)
      have hsplit : ∑ j : Fin m, (invDistMatrix m - 1) i j =
          (∑ j : Fin m with j.val < i.val, (invDistMatrix m - 1) i j) +
            (∑ j : Fin m with i.val < j.val, (invDistMatrix m - 1) i j) := by
        rw [← sum_union (disjoint_filter.mpr fun _ _ h1 h2 ↦ by omega)]
        symm
        refine sum_subset (subset_univ _) fun j _ hj ↦ ?_
        simp only [mem_union, mem_filter, mem_univ, true_and, not_or, not_lt] at hj
        have hji : j = i := Fin.ext (by omega)
        rw [hji, hdiag]
      have hlog_prod : Real.log (m : ℝ) / 2 ≤
          Real.log (((i.val : ℝ) + 2) / 2) +
            Real.log ((((m - 1 - i.val : ℕ) : ℝ) + 2) / 2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        have hcast_r : ((m - 1 - i.val : ℕ) : ℝ) = (m : ℝ) - 1 - (i.val : ℝ) := by
          have hnat : (m - 1 - i.val) + 1 + i.val = m := by omega
          have hc : ((m - 1 - i.val : ℕ) : ℝ) + 1 + (i.val : ℝ) = (m : ℝ) := by
            exact_mod_cast hnat
          linarith
        have h_amgm : √(m : ℝ) ≤ (((i.val : ℝ) + 2) / 2) *
            ((((m - 1 - i.val : ℕ) : ℝ) + 2) / 2) := by
          rw [hcast_r]
          have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
          have hi1 : (i.val : ℝ) ≤ (m : ℝ) - 1 := by
            have : i.val + 1 ≤ m := i.isLt
            have hle : (i.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast this
            linarith
          have hprod : 2 * ((m : ℝ) + 1) ≤
              ((i.val : ℝ) + 2) * ((m : ℝ) + 1 - (i.val : ℝ)) := by
            nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hi1)]
          have hquarter : ((m : ℝ) + 1) / 2 ≤
              (((i.val : ℝ) + 2) / 2) * (((m : ℝ) - 1 - (i.val : ℝ) + 2) / 2) := by
            linarith
          refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
          have hsq : (m : ℝ) ≤ (((m : ℝ) + 1) / 2) ^ 2 := by nlinarith
          exact hsq.trans ((sq_le_sq₀ (by positivity) (by positivity)).mpr hquarter)
        calc
          Real.log (m : ℝ) / 2 = Real.log √(m : ℝ) := (Real.log_sqrt hm_pos.le).symm
          _ ≤ Real.log ((((i.val : ℝ) + 2) / 2) *
                ((((m - 1 - i.val : ℕ) : ℝ) + 2) / 2)) :=
                Real.log_le_log (Real.sqrt_pos.mpr hm_pos) h_amgm
      rw [hsplit]
      linarith [log_add_two_div_two_le_sum_range i.val,
        log_add_two_div_two_le_sum_range (m - 1 - i.val)]
    have hinner : Real.log (m : ℝ) / 2 ≤
        inner ℝ u (toEuclideanCLM (𝕜 := ℝ) (invDistMatrix m - 1) u) := by
      rw [inner_toEuclideanCLM]
      simp only [u, dotProduct, mulVec]
      have hfactor : ∑ i : Fin m, 1 / √(m : ℝ) *
          ∑ j : Fin m, (invDistMatrix m - 1) i j * (1 / √(m : ℝ)) =
          (1 / (m : ℝ)) * ∑ i : Fin m, ∑ j : Fin m, (invDistMatrix m - 1) i j := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [← sum_mul]
        have hsq : (1 / √(m : ℝ)) * (1 / √(m : ℝ)) = 1 / (m : ℝ) := by
          rw [one_div_mul_one_div, Real.mul_self_sqrt hm_pos.le]
        calc
          1 / √(m : ℝ) * ((∑ j : Fin m, (invDistMatrix m - 1) i j) * (1 / √(m : ℝ)))
              = ((1 / √(m : ℝ)) * (1 / √(m : ℝ))) *
                  ∑ j : Fin m, (invDistMatrix m - 1) i j := by ring
          _ = (1 / (m : ℝ)) * ∑ j : Fin m, (invDistMatrix m - 1) i j := by rw [hsq]
      rw [hfactor]
      calc
        Real.log (m : ℝ) / 2
            = (1 / (m : ℝ)) * ∑ _i : Fin m, (Real.log (m : ℝ) / 2) := by
              simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp [hm_pos.ne']
        _ ≤ (1 / (m : ℝ)) * ∑ i : Fin m, ∑ j : Fin m, (invDistMatrix m - 1) i j :=
              mul_le_mul_of_nonneg_left (sum_le_sum fun i _ ↦ hrow i) (by positivity)
    exact hinner.trans ((le_abs_self _).trans
      (abs_inner_toEuclideanCLM_le_opNorm (invDistMatrix m - 1) hu hu))

/-- **Harmonic lower bound for the inverse-distance matrix**: for every `m : ℕ`,
`Real.log m / 2 ≤ ‖toEuclideanCLM (𝕜 := ℝ) (invDistMatrix m)‖`. -/
theorem log_div_two_le_opNorm_invDistMatrix (m : ℕ) :
    Real.log (m : ℝ) / 2 ≤ ‖toEuclideanCLM (𝕜 := ℝ) (invDistMatrix m)‖ := by
  refine (log_div_two_le_opNorm_invDistMatrix_sub_one m).trans
    (opNorm_toEuclideanCLM_mono_of_nonneg ?_ ?_)
  · intro i j
    by_cases hij : i = j
    · subst hij; simp [invDistMatrix]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]
      exact (invDistMatrix_pos m i j).le
  · intro i j
    by_cases hij : i = j
    · subst hij; simp [invDistMatrix]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]

private theorem upper_quadrant_hilbert_bound {m : ℕ} (r : Fin m)
    {u v : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ∑ x : Fin m, ∑ y : Fin m,
        (if x ≤ r ∧ r ≤ y then invDistMatrix m x y else 0) * u.ofLp x * v.ofLp y ≤ Real.pi := by
  let uTil : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 fun j ↦ if hj : j.val ≤ r.val then u.ofLp ⟨r.val - j.val, by omega⟩ else 0
  let vTil : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 fun k ↦ if hk : r.val + k.val < m then v.ofLp ⟨r.val + k.val, hk⟩ else 0
  have huTil : ‖uTil‖ ≤ 1 := by
    rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hu ⊢
    refine (?_ : ∑ j : Fin m, uTil.ofLp j ^ 2 ≤ ∑ x : Fin m, u.ofLp x ^ 2).trans hu
    have hrewrite : ∑ j : Fin m, uTil.ofLp j ^ 2 =
        ∑ j : Fin m with j.val ≤ r.val, u.ofLp ⟨r.val - j.val, by omega⟩ ^ 2 := by
      rw [sum_filter]
      refine sum_congr rfl fun j _ ↦ ?_
      dsimp only [uTil]
      split_ifs <;> simp
    rw [hrewrite]
    have hbij : ∑ j : Fin m with j.val ≤ r.val, u.ofLp ⟨r.val - j.val, by omega⟩ ^ 2 =
        ∑ x : Fin m with x.val ≤ r.val, u.ofLp x ^ 2 := by
      refine sum_bij (fun j hj ↦ ⟨r.val - j.val, by have := (mem_filter.mp hj).2; omega⟩)
        (fun j hj ↦ by simp only [mem_filter, mem_univ, true_and]; omega)
        (fun _ hj₁ _ hj₂ h ↦ by
          have h1 := (mem_filter.mp hj₁).2
          have h2 := (mem_filter.mp hj₂).2
          have hv' := congrArg Fin.val h
          dsimp only at hv'; ext; omega)
        (fun x hx ↦ by
          have hxle := (mem_filter.mp hx).2
          refine ⟨⟨r.val - x.val, by omega⟩,
            mem_filter.mpr ⟨mem_univ _, by dsimp only; omega⟩, ?_⟩
          ext; dsimp only; omega)
        (fun _ _ ↦ rfl)
    rw [hbij]
    exact sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have hvTil : ‖vTil‖ ≤ 1 := by
    rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hv ⊢
    refine (?_ : ∑ k : Fin m, vTil.ofLp k ^ 2 ≤ ∑ y : Fin m, v.ofLp y ^ 2).trans hv
    have hrewrite : ∑ k : Fin m, vTil.ofLp k ^ 2 =
        ∑ k : Fin m with r.val + k.val < m,
          (if hk : r.val + k.val < m then v.ofLp ⟨r.val + k.val, hk⟩ else 0) ^ 2 := by
      rw [sum_filter]
      refine sum_congr rfl fun k _ ↦ ?_
      dsimp only [vTil]
      split_ifs <;> simp
    rw [hrewrite]
    have hbij : ∑ k : Fin m with r.val + k.val < m,
          (if hk : r.val + k.val < m then v.ofLp ⟨r.val + k.val, hk⟩ else 0) ^ 2 =
        ∑ y : Fin m with r.val ≤ y.val, v.ofLp y ^ 2 := by
      refine sum_bij (fun k hk ↦ ⟨r.val + k.val, (mem_filter.mp hk).2⟩)
        (fun _ _ ↦ by simp only [mem_filter, mem_univ, true_and]; omega)
        (fun _ _ _ _ h ↦ by
          have hv' := congrArg Fin.val h
          dsimp only at hv'; ext; omega)
        (fun y hy ↦ by
          have hyle := (mem_filter.mp hy).2
          refine ⟨⟨y.val - r.val, by omega⟩,
            mem_filter.mpr ⟨mem_univ _, by dsimp only; omega⟩, ?_⟩
          ext; dsimp only; omega)
        (fun k hk ↦ by
          have hklt := (mem_filter.mp hk).2
          simp [hklt])
    rw [hbij]
    exact sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have hsum_eq : ∑ x : Fin m, ∑ y : Fin m,
        (if x ≤ r ∧ r ≤ y then invDistMatrix m x y else 0) * u.ofLp x * v.ofLp y =
      inner ℝ uTil (toEuclideanCLM (𝕜 := ℝ) (hilbertMatrix m) vTil) := by
    rw [inner_toEuclideanCLM]
    simp only [dotProduct, mulVec, mul_sum]
    have hlhs_bij : ∑ x : Fin m, ∑ y : Fin m,
          (if x ≤ r ∧ r ≤ y then invDistMatrix m x y else 0) * u.ofLp x * v.ofLp y =
        ∑ j : Fin m, ∑ k : Fin m,
          (if hj : j.val ≤ r.val then if hk : r.val + k.val < m then
            hilbertMatrix m j k * u.ofLp ⟨r.val - j.val, by omega⟩ *
              v.ofLp ⟨r.val + k.val, hk⟩ else 0 else 0) := by
      trans ∑ x : Fin m with x.val ≤ r.val, ∑ y : Fin m with r.val ≤ y.val,
        invDistMatrix m x y * u.ofLp x * v.ofLp y
      · rw [sum_filter]
        refine sum_congr rfl fun x _ ↦ ?_
        by_cases hx : x.val ≤ r.val
        · simp only [hx, ↓reduceIte, sum_filter]
          refine sum_congr rfl fun y _ ↦ ?_
          simp only [Fin.le_iff_val_le_val, hx, true_and]
          split_ifs <;> ring
        · simp only [hx, ↓reduceIte]
          refine sum_eq_zero fun y _ ↦ ?_
          simp only [Fin.le_iff_val_le_val, hx, false_and, ↓reduceIte, zero_mul]
      · symm
        trans ∑ j : Fin m with j.val ≤ r.val, ∑ k : Fin m with r.val + k.val < m,
          (if hj : j.val ≤ r.val then if hk : r.val + k.val < m then
            hilbertMatrix m j k * u.ofLp ⟨r.val - j.val, by omega⟩ *
              v.ofLp ⟨r.val + k.val, hk⟩ else 0 else 0)
        · rw [sum_filter]
          refine sum_congr rfl fun j _ ↦ ?_
          by_cases hj : j.val ≤ r.val
          · simp only [hj, ↓reduceIte, ↓reduceDIte, sum_filter]
            refine sum_congr rfl fun k _ ↦ ?_
            by_cases hk : r.val + k.val < m <;> simp [hk]
          · simp only [hj, ↓reduceIte, ↓reduceDIte]
            exact sum_const_zero
        · refine sum_bij (fun j hj ↦ ⟨r.val - j.val, by have := (mem_filter.mp hj).2; omega⟩)
            (fun _ _ ↦ by simp only [mem_filter, mem_univ, true_and]; omega)
            (fun _ hj₁ _ hj₂ h ↦ by
              have h1 := (mem_filter.mp hj₁).2
              have h2 := (mem_filter.mp hj₂).2
              have hv' := congrArg Fin.val h
              dsimp only at hv'; ext; omega)
            (fun x hx ↦ by
              have hxle := (mem_filter.mp hx).2
              refine ⟨⟨r.val - x.val, by omega⟩,
                mem_filter.mpr ⟨mem_univ _, by dsimp only; omega⟩, ?_⟩
              ext; dsimp only; omega)
            (fun j hj ↦ by
              have hjle := (mem_filter.mp hj).2
              refine sum_bij (fun k hk ↦ ⟨r.val + k.val, (mem_filter.mp hk).2⟩)
                (fun _ _ ↦ by simp only [mem_filter, mem_univ, true_and]; omega)
                (fun _ _ _ _ h ↦ by
                  have hv' := congrArg Fin.val h
                  dsimp only at hv'; ext; omega)
                (fun y hy ↦ by
                  have hyle := (mem_filter.mp hy).2
                  refine ⟨⟨y.val - r.val, by omega⟩,
                    mem_filter.mpr ⟨mem_univ _, by dsimp only; omega⟩, ?_⟩
                  ext; dsimp only; omega)
                (fun k hk ↦ by
                  have hklt := (mem_filter.mp hk).2
                  simp only [hjle, ↓reduceDIte, hklt, hilbertMatrix_apply, invDistMatrix_apply]
                  congr 2
                  have hdiff : ((r.val - j.val : ℕ) : ℝ) - ((r.val + k.val : ℕ) : ℝ) =
                      -((j : ℝ) + (k : ℝ)) := by
                    have hadd : ((r.val - j.val : ℕ) : ℝ) + ((j : ℝ) + (k : ℝ)) =
                        ((r.val + k.val : ℕ) : ℝ) := by
                      have hn : (r.val - j.val) + (j.val + k.val) = r.val + k.val := by omega
                      exact_mod_cast hn
                    linarith
                  rw [show ((⟨r.val - j.val, by omega⟩ : Fin m) : ℝ) = ((r.val - j.val : ℕ) : ℝ)
                    from rfl,
                    show ((⟨r.val + k.val, hklt⟩ : Fin m) : ℝ) = ((r.val + k.val : ℕ) : ℝ)
                    from rfl, hdiff, abs_neg, abs_of_nonneg (by positivity)]))
    rw [hlhs_bij]
    refine sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
    dsimp only [uTil, vTil]
    split_ifs <;> ring
  rw [hsum_eq]
  exact ((le_abs_self _).trans
    (abs_inner_toEuclideanCLM_le_opNorm (hilbertMatrix m) huTil hvTil)).trans
    (opNorm_hilbertMatrix_le_pi m)

/-- **Interval-masked inverse-distance operator-norm bound**: for every `m : ℕ` and `r : Fin m`,
`‖toEuclideanCLM (𝕜 := ℝ) ((invDistMatrix m).hadamard (intervalMask m r))‖ ≤ 2 * π`. -/
theorem opNorm_invDistMatrix_hadamard_intervalMask_le (m : ℕ) (r : Fin m) :
    ‖toEuclideanCLM (𝕜 := ℝ) ((invDistMatrix m).hadamard (intervalMask m r))‖ ≤ 2 * Real.pi := by
  let M := (invDistMatrix m).hadamard (intervalMask m r)
  have hM_nn : ∀ x y, 0 ≤ M x y := fun x y ↦ by
    simp only [M, hadamard_apply, intervalMask_apply]
    split_ifs
    · exact mul_nonneg (invDistMatrix_pos m x y).le zero_le_one
    · simp
  refine opNorm_toEuclideanCLM_le_of_inner M (by positivity) fun u v hu hv ↦ ?_
  let u' := absVec u
  let v' := absVec v
  have hu' : ‖u'‖ ≤ 1 := norm_absVec_le hu
  have hv' : ‖v'‖ ≤ 1 := norm_absVec_le hv
  have hu'_nn : ∀ x, 0 ≤ u'.ofLp x := fun _ ↦ abs_nonneg _
  have hv'_nn : ∀ y, 0 ≤ v'.ofLp y := fun _ ↦ abs_nonneg _
  have habs := inner_toEuclideanCLM_le_absVec hM_nn u v
  have hsplit : inner ℝ u' (toEuclideanCLM (𝕜 := ℝ) M v') ≤
      (∑ x : Fin m, ∑ y : Fin m,
        (if x ≤ r ∧ r ≤ y then invDistMatrix m x y else 0) * u'.ofLp x * v'.ofLp y) +
      (∑ y : Fin m, ∑ x : Fin m,
        (if y ≤ r ∧ r ≤ x then invDistMatrix m y x else 0) * v'.ofLp y * u'.ofLp x) := by
    rw [inner_toEuclideanCLM]
    simp only [dotProduct, mulVec, mul_sum]
    rw [sum_comm (s := univ) (t := univ) (f := fun y x ↦
      (if y ≤ r ∧ r ≤ x then invDistMatrix m y x else 0) * v'.ofLp y * u'.ofLp x),
      ← sum_add_distrib]
    refine sum_le_sum fun x _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun y _ ↦ ?_
    have hsym := (isSymm_invDistMatrix m).apply x y
    dsimp only [M]
    rw [hadamard_apply, intervalMask_apply]
    have hpos := (invDistMatrix_pos m x y).le
    have hux := hu'_nn x
    have hvy := hv'_nn y
    by_cases h1 : x ≤ r ∧ r ≤ y <;> by_cases h2 : y ≤ r ∧ r ≤ x
    · simp only [h1, h2, and_self, or_self, ↓reduceIte]
      rw [hsym]
      nlinarith [mul_nonneg (mul_nonneg hpos hux) hvy]
    · simp only [h1, h2, and_self, or_false, ↓reduceIte]
      linarith
    · simp only [h1, h2, and_self, false_or, ↓reduceIte]
      rw [hsym]
      linarith
    · simp only [h1, h2, or_self, ↓reduceIte]
      linarith
  have hq1 := upper_quadrant_hilbert_bound r hu' hv'
  have hq2 := upper_quadrant_hilbert_bound r hv' hu'
  linarith

end InvDistMatrix

-- Private non-vacuity and sharpness sanity checks
private example : hilbertMatrix 2 0 1 = 1 / 2 := by
  norm_num [hilbertMatrix]

private example : ‖toEuclideanCLM (𝕜 := ℝ) (offDiagOne (Fin 3))‖ = 2 := by
  rw [opNorm_offDiagOne (Fin 3)]
  norm_num

end CslibFrontier.Matrix
