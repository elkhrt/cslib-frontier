/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Complexity
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# General Adversary Semidefinite Duality and Reichardt's Reflection Theorem

This module proves strong semidefinite programming duality for the Høyer–Lee–Špalek negative-weight
quantum adversary bound $\mathrm{ADV}^{\pm}(f)$ (`Cslib.Quantum.generalAdversary`) and constructs
the Reichardt / Lee–Mittal–Reichardt–Špalek–Szegedy alternating-reflection quantum query algorithm
showing $Q_2(f) = \Theta(\mathrm{ADV}^{\pm}(f))$ for every total Boolean function
$f : \{0, 1\}^N \to \{0, 1\}$.

Given a dual adversary solution $\{v_{x, i}\}_{x, i} \subset \mathbb{R}^D$ of weight $W \ge 1$ with
$\sum_i \|v_{x, i}\|^2 \le W$ and $\sum_{i : x_i \ne y_i} \langle v_{x, i}, v_{y, i}\rangle = 1$
whenever $f(x) \ne f(y)$, we form on $\mathcal{H} = \mathbb{C} \oplus
(\mathbb{C}^N \otimes \mathbb{C}^2 \otimes \mathbb{C}^D)$ the negative-input witness states
$|\varphi_y\rangle = |0\rangle + \alpha \sum_i |i, y_i, v_{y, i}\rangle$ (for $f(y) = 0$) and the
one-query unitary $V_x = R_x R_K$, where $R_K$ reflects through
$K = \mathrm{span}\{|\varphi_y\rangle : f(y) = 0\}$ and $R_x$ reflects through the basis coordinates
consistent with $x$:

* When $f(x) = 0$, $V_x |\varphi_x\rangle = |\varphi_x\rangle$, so every Cesàro average
  $A_T |0\rangle = \frac{1}{T} \sum_{t < T} V_x^t |0\rangle$ satisfies
  $\langle \varphi_x, A_T |0\rangle\rangle = 1$ and $\|A_T |0\rangle\|^2 \ge \|\varphi_x\|^{-2}
  \ge 1 - \varepsilon$.
* When $f(x) = 1$, the positive witness $|w_x\rangle = |0\rangle - \alpha^{-1} \sum_i
  |i, \neg x_i, v_{x, i}\rangle$ lies in $K^\perp$ and satisfies
  $(I - V_x)|w_x\rangle = 2|0\rangle$, so telescoping gives $\|A_T |0\rangle\| \le \|w_x\| / T$.

A coherent uniform clock register over $t \in \{0, \dots, T - 1\}$ executes $A_T |0\rangle$ with
$T - 1 = O(W / \varepsilon)$ phase queries, yielding $Q_2(f) \le 3\,\mathrm{ADV}^{\pm}(f)$.

## Main definitions

* `Cslib.Quantum.DualAdversary`: feasible dual solution of the general adversary
  semidefinite program for a (partial or total) Boolean function $(P, f)$.
* `Cslib.Quantum.psdFactor`: real Gram-factorization vectors of a positive semidefinite
  real matrix via the spectral theorem.

## Main results

* `Cslib.Quantum.DualAdversary.generalAdversary_le`: weak SDP duality
  $\mathrm{ADV}^{\pm}(P, f) \le W$.
* `Cslib.Quantum.exists_dualAdversary_eq_generalAdversary`: strong SDP duality attaining
  $W = \mathrm{ADV}^{\pm}(P, f)$ for every Boolean function on a promise domain.
* `Cslib.Quantum.isQuantumComputable_of_dualAdversary`: alternating-reflection algorithm
  computing $f$ within error $\varepsilon \in (0, 1/2)$ using $O(W / \varepsilon)$ queries.
* `Cslib.Quantum.queryComplexity_le_mul_generalAdversary`:
  $Q_\varepsilon(f) \le (\sqrt{2} / \varepsilon)\,\mathrm{ADV}^{\pm}(f)$ for $0 < \varepsilon <
  1/2$.
* `Cslib.Quantum.boundedQueryComplexity_le_three_mul_generalAdversary`:
  $Q_2(f) \le 3\,\mathrm{ADV}^{\pm}(f)$.
* `Cslib.Quantum.boundedQueryComplexity_generalAdversary_bounds`:
  $\frac{1}{36}\,\mathrm{ADV}^{\pm}(f) \le Q_2(f) \le 3\,\mathrm{ADV}^{\pm}(f)$.

## Tags

quantum query complexity, negative-weight adversary, semidefinite duality, span program, reflections
-/

public section

namespace Cslib.Quantum

open Finset Matrix Cslib Cslib.BitString Cslib.Quantum
open scoped RealInnerProductSpace

/-! ### Real Gram factorization of positive semidefinite matrices -/

section PSDFactor

/-- Real Gram-factorization vectors of a positive semidefinite matrix `A : Matrix ι ι ℝ`, defined
from its spectral decomposition `A = U · diag(λ) · Uᵀ` by `g k i = √(λ_k) · U_{i, k}`. -/
noncomputable def psdFactor {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (k i : ι) : ℝ :=
  √(hA.isHermitian.eigenvalues k) * (hA.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) i k

/-- The Gram inner products of `psdFactor hA` recover every entry of `A`. -/
theorem sum_psdFactor_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (i j : ι) :
    ∑ k : ι, psdFactor hA k i * psdFactor hA k j = A i j := by
  have hspec := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hA.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite,
    mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, RCLike.ofReal_real_eq_id, Function.comp_apply,
    id_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] at hspec
  rw [hspec]
  refine sum_congr rfl fun k _ ↦ ?_
  dsimp only [psdFactor]
  conv_rhs => rw [← Real.mul_self_sqrt (hA.eigenvalues_nonneg k)]
  ring

end PSDFactor

/-! ### Dual adversary structure and weak/strong SDP duality -/

section DualSDP

/-- A feasible solution to the dual semidefinite program of the general adversary bound
`ADV±(P, f)`: real vectors `vec x i ∈ ℝ^D` of total squared norm at most `weight` on each valid
input `x`, whose inner products across disagreeing coordinates sum to `1` whenever `f x ≠ f y`. -/
@[ext]
structure DualAdversary {N : ℕ} (P : BitString N → Prop) (f : BitString N → Bool)
    (D : Type*) [Fintype D] where
  /-- Dual vector family assigning `vec x i ∈ ℝ^D` to input `x` and coordinate `i`. -/
  vec : BitString N → Fin N → D → ℝ
  /-- Objective upper bound on `max_{x ∈ P} ∑_i ‖vec x i‖²`. -/
  weight : ℝ
  /-- The objective weight is nonnegative. -/
  weight_nonneg : 0 ≤ weight
  /-- Every valid input has total squared vector norm at most `weight`. -/
  sum_sq_le : ∀ x, P x → ∑ i : Fin N, ∑ d : D, vec x i d ^ 2 ≤ weight
  /-- Every valid pair `(x, y)` with `f x = true` and `f y = false` has disagreeing-coordinate
  inner-product sum equal to `1`. -/
  sum_inner_eq_one : ∀ x y, P x → P y → f x = true → f y = false →
    ∑ i with x i ≠ y i, ∑ d : D, vec x i d * vec y i d = 1

/-- By symmetry of the real inner product, `sum_inner_eq_one` holds whenever `f x ≠ f y`. -/
theorem DualAdversary.sum_inner_of_ne {N : ℕ} {P : BitString N → Prop} {f : BitString N → Bool}
    {D : Type*} [Fintype D] (w : DualAdversary P f D) {x y : BitString N}
    (hx : P x) (hy : P y) (hxy : f x ≠ f y) :
    ∑ i with x i ≠ y i, ∑ d : D, w.vec x i d * w.vec y i d = 1 := by
  cases hfx : f x <;> cases hfy : f y
  · exact (hxy (hfx.trans hfy.symm)).elim
  · rw [← w.sum_inner_eq_one y x hy hx hfy hfx]
    have hfilt : (univ.filter fun i : Fin N ↦ x i ≠ y i) =
        univ.filter fun i : Fin N ↦ y i ≠ x i := by
      ext i; simp [ne_comm]
    rw [hfilt]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun d _ ↦ mul_comm _ _
  · exact w.sum_inner_eq_one x y hx hy hfx hfy
  · exact (hxy (hfx.trans hfy.symm)).elim

/-- Any dual adversary for a function taking two distinct values on `P` has `1 ≤ w.weight`. -/
theorem DualAdversary.one_le_weight {N : ℕ} {P : BitString N → Prop} {f : BitString N → Bool}
    {D : Type*} [Fintype D] (w : DualAdversary P f D) {x y : BitString N}
    (hx : P x) (hy : P y) (hxy : f x ≠ f y) : 1 ≤ w.weight := by
  have h1 := w.sum_inner_of_ne hx hy hxy
  calc (1 : ℝ) = ∑ i with x i ≠ y i, ∑ d : D, w.vec x i d * w.vec y i d := h1.symm
    _ ≤ ∑ i with x i ≠ y i, ∑ d : D, |w.vec x i d| * |w.vec y i d| :=
        sum_le_sum fun i _ ↦ sum_le_sum fun d _ ↦ by rw [← abs_mul]; exact le_abs_self _
    _ ≤ ∑ i : Fin N, ∑ d : D, |w.vec x i d| * |w.vec y i d| :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦
          sum_nonneg fun _ _ ↦ by positivity
    _ = ∑ p : Fin N × D, |w.vec x p.1 p.2| * |w.vec y p.1 p.2| :=
        (Fintype.sum_prod_type fun p : Fin N × D ↦ |w.vec x p.1 p.2| * |w.vec y p.1 p.2|).symm
    _ ≤ √(∑ p : Fin N × D, |w.vec x p.1 p.2| ^ 2) *
          √(∑ p : Fin N × D, |w.vec y p.1 p.2| ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √w.weight * √w.weight := by
        simp only [sq_abs, Fintype.sum_prod_type]
        exact mul_le_mul (Real.sqrt_le_sqrt (w.sum_sq_le x hx))
          (Real.sqrt_le_sqrt (w.sum_sq_le y hy)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = w.weight := Real.mul_self_sqrt w.weight_nonneg

/-- Core bilinear factorization bound: if `Γ` is supported on pairs with `P x`, `P y`, and
`f x ≠ f y`, then a dual adversary `w` gives `‖Γ‖ ≤ w.weight · max_i ‖Γ ∘ D_i‖`. -/
theorem DualAdversary.opNorm_le_weight_mul {N : ℕ} {P : BitString N → Prop}
    {f : BitString N → Bool} {D : Type*} [Fintype D] (w : DualAdversary P f D)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → BitString N)
    (Γ : Matrix κ κ ℝ) (hsupp : ∀ a b, Γ a b ≠ 0 → P (π a) ∧ P (π b) ∧ f (π a) ≠ f (π b))
    {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ i : Fin N,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (Matrix.of fun a b ↦ if π a i ≠ π b i then Γ a b else 0)‖ ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ w.weight * K := by
  classical
  refine Matrix.opNorm_toEuclideanCLM_le_of_inner Γ (mul_nonneg w.weight_nonneg hK)
    fun u v hu hv ↦ ?_
  let uSlice (p : Fin N × D) : EuclideanSpace ℝ κ :=
    WithLp.toLp 2 fun a ↦ if P (π a) then u.ofLp a * w.vec (π a) p.1 p.2 else 0
  let vSlice (p : Fin N × D) : EuclideanSpace ℝ κ :=
    WithLp.toLp 2 fun b ↦ if P (π b) then v.ofLp b * w.vec (π b) p.1 p.2 else 0
  let M (i : Fin N) : Matrix κ κ ℝ := Matrix.of fun a b ↦ if π a i ≠ π b i then Γ a b else 0
  have hdecomp : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) =
      ∑ p : Fin N × D, inner ℝ (uSlice p) (Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1) (vSlice p)) := by
    rw [Matrix.inner_toEuclideanCLM, Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec, mul_sum, Matrix.inner_toEuclideanCLM]
    trans ∑ a : κ, ∑ b : κ, ∑ i : Fin N, ∑ d : D,
        (uSlice (i, d)).ofLp a * (M i a b * (vSlice (i, d)).ofLp b)
    · refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
      by_cases h0 : Γ a b = 0
      · simp [M, h0]
      · obtain ⟨haP, hbP, hne⟩ := hsupp a b h0
        have hsum : ∑ i : Fin N, ∑ d : D,
            (uSlice (i, d)).ofLp a * (M i a b * (vSlice (i, d)).ofLp b) =
            u.ofLp a * (Γ a b * v.ofLp b) *
              ∑ i with π a i ≠ π b i, ∑ d : D, w.vec (π a) i d * w.vec (π b) i d := by
          rw [mul_sum, sum_filter]
          refine sum_congr rfl fun i _ ↦ ?_
          by_cases hi : π a i ≠ π b i
          · simp only [uSlice, vSlice, M, haP, hbP, hi, ne_eq, not_false_eq_true, ↓reduceIte,
              Matrix.of_apply, mul_sum]
            exact sum_congr rfl fun d _ ↦ by ring
          · simp [M, hi]
        rw [hsum, w.sum_inner_of_ne haP hbP hne, mul_one]
    · conv_lhs => enter [2, a]; rw [sum_comm]
      rw [sum_comm]
      refine sum_congr rfl fun i _ ↦ ?_
      conv_lhs => enter [2, a]; rw [sum_comm]
      rw [sum_comm]
  have hnorm_sum (z : EuclideanSpace ℝ κ) (hz : ‖z‖ ≤ 1)
      (zSlice : Fin N × D → EuclideanSpace ℝ κ)
      (hzs : ∀ p a, (zSlice p).ofLp a = if P (π a) then z.ofLp a * w.vec (π a) p.1 p.2 else 0) :
      ∑ p : Fin N × D, ‖zSlice p‖ ^ 2 ≤ w.weight := by
    simp only [EuclideanSpace.real_norm_sq_eq, hzs]
    rw [sum_comm]
    calc ∑ a : κ, ∑ p : Fin N × D, (if P (π a) then z.ofLp a * w.vec (π a) p.1 p.2 else 0) ^ 2
        ≤ ∑ a : κ, z.ofLp a ^ 2 * w.weight := sum_le_sum fun a _ ↦ by
          by_cases haP : P (π a)
          · simp only [haP, ↓reduceIte, mul_pow, ← mul_sum, Fintype.sum_prod_type]
            exact mul_le_mul_of_nonneg_left (w.sum_sq_le (π a) haP) (sq_nonneg _)
          · simp only [haP, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
              sum_const_zero]
            exact mul_nonneg (sq_nonneg (z.ofLp a)) w.weight_nonneg
      _ = (∑ a : κ, z.ofLp a ^ 2) * w.weight := (sum_mul _ _ _).symm
      _ ≤ 1 * w.weight := mul_le_mul_of_nonneg_right
          ((EuclideanSpace.norm_le_one_iff_sum_sq_le_one z).1 hz) w.weight_nonneg
      _ = w.weight := one_mul _
  rw [hdecomp]
  calc ∑ p : Fin N × D, inner ℝ (uSlice p) (Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1) (vSlice p))
      ≤ ∑ p : Fin N × D, K * (‖uSlice p‖ * ‖vSlice p‖) := sum_le_sum fun p _ ↦ by
        calc inner ℝ (uSlice p) (Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1) (vSlice p))
            ≤ ‖uSlice p‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1) (vSlice p)‖ :=
              real_inner_le_norm _ _
          _ ≤ ‖uSlice p‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1)‖ * ‖vSlice p‖) :=
              mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1)).le_opNorm _)
                (norm_nonneg _)
          _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.1)‖ * (‖uSlice p‖ * ‖vSlice p‖) := by ring
          _ ≤ K * (‖uSlice p‖ * ‖vSlice p‖) :=
              mul_le_mul_of_nonneg_right (hdiff p.1) (by positivity)
    _ = K * ∑ p : Fin N × D, ‖uSlice p‖ * ‖vSlice p‖ := (mul_sum _ _ _).symm
    _ ≤ K * (√(∑ p : Fin N × D, ‖uSlice p‖ ^ 2) * √(∑ p : Fin N × D, ‖vSlice p‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hK
    _ ≤ K * (√w.weight * √w.weight) := mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt (hnorm_sum u hu uSlice fun _ _ ↦ rfl))
          (Real.sqrt_le_sqrt (hnorm_sum v hv vSlice fun _ _ ↦ rfl))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hK
    _ = w.weight * K := by rw [Real.mul_self_sqrt w.weight_nonneg, mul_comm]

/-- **Weak SDP duality**: every feasible dual adversary `w` upper-bounds `ADV±(P, f)`. -/
theorem DualAdversary.generalAdversary_le {N : ℕ} {P : BitString N → Prop}
    {f : BitString N → Bool} {D : Type*} [Fintype D] (w : DualAdversary P f D) :
    generalAdversary P f ≤ w.weight := by
  refine (generalAdversary_le_iff w.weight_nonneg).2 fun Γ _ hΓ ↦
    w.opNorm_le_weight_mul (fun x ↦ x) Γ hΓ (maxDiffNorm_nonneg Γ) fun i ↦ ?_
  have heq : (Matrix.of fun a b : BitString N ↦ if a i ≠ b i then Γ a b else 0) =
      Γ.hadamard (diffMatrix i) := by
    ext a b; simp [Matrix.hadamard_apply, diffMatrix_apply]
  rw [heq]
  exact norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ i

private theorem one_le_generalAdversary_of_pair {N : ℕ} {P : BitString N → Prop}
    {f : BitString N → Bool} {x₁ x₀ : BitString N}
    (h₁ : P x₁) (hf₁ : f x₁ = true) (h₀ : P x₀) (hf₀ : f x₀ = false) :
    1 ≤ generalAdversary P f := by
  have hne : x₁ ≠ x₀ := fun h ↦ by simp [h, hf₀] at hf₁
  let Γ : Matrix (BitString N) (BitString N) ℝ :=
    Matrix.of fun x y ↦ if (x = x₁ ∧ y = x₀) ∨ (x = x₀ ∧ y = x₁) then 1 else 0
  have hsym : Γ.IsSymm := Matrix.ext fun x y ↦ by
    simp only [Γ, transpose_apply, of_apply]
    have hiff : ((y = x₁ ∧ x = x₀) ∨ (y = x₀ ∧ x = x₁)) ↔
        ((x = x₁ ∧ y = x₀) ∨ (x = x₀ ∧ y = x₁)) := by tauto
    simp only [hiff]
  have hadv : IsAdversaryMatrix P f Γ := fun x y hxy ↦ by
    simp only [Γ, of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      Classical.not_not] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h₁, h₀, by simp [hf₁, hf₀]⟩
    · exact ⟨h₀, h₁, by simp [hf₁, hf₀]⟩
  have hrow (x : BitString N) : ∑ y, |Γ x y| ≤ 1 := by
    by_cases hx1 : x = x₁
    · rw [hx1]
      have hsub : ∑ y, |Γ x₁ y| = |Γ x₁ x₀| :=
        sum_eq_single x₀ (fun y _ hy ↦ by simp [Γ, hy, hne]) (by simp)
      rw [hsub]; simp [Γ]
    · by_cases hx0 : x = x₀
      · rw [hx0]
        have hne' : x₀ ≠ x₁ := hne.symm
        have hsub : ∑ y, |Γ x₀ y| = |Γ x₀ x₁| :=
          sum_eq_single x₁ (fun y _ hy ↦ by simp [Γ, hy, hne']) (by simp)
        rw [hsub]; simp [Γ]
      · simp [Γ, hx1, hx0]
  have hmd : maxDiffNorm Γ ≤ 1 := (maxDiffNorm_le_iff zero_le_one).2 fun i ↦ by
    have hbound (x : BitString N) : ∑ y, |(Γ.hadamard (diffMatrix i)) x y| ≤ 1 :=
      (sum_le_sum fun y _ ↦ by
        simp only [hadamard_apply, diffMatrix_apply]
        split_ifs <;> simp [abs_nonneg]).trans (hrow x)
    have hcol (y : BitString N) : ∑ x, |(Γ.hadamard (diffMatrix i)) x y| ≤ 1 :=
      (sum_le_sum fun x _ ↦ by
        simp only [hadamard_apply, diffMatrix_apply, hsym.apply y x]
        split_ifs <;> simp [abs_nonneg]).trans (hrow y)
    exact (Matrix.opNorm_toEuclideanCLM_le_sqrt _ zero_le_one zero_le_one hbound hcol).trans_eq
      (by simp)
  have hnorm : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
    simpa [Γ] using Matrix.abs_entry_le_norm_toEuclideanCLM Γ x₁ x₀
  have hpos : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) fun h0 ↦ by
    have hzero := eq_zero_of_maxDiffNorm_eq_zero hadv h0.symm
    have : Γ x₁ x₀ = 0 := by simp [hzero]
    simp [Γ] at this
  exact ((one_le_div hpos).2 (hmd.trans hnorm)).trans (le_generalAdversary hsym hadv)

private theorem posSemidef_smul {ι : Type*} [Finite ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) : (c • A).PosSemidef := by
  cases nonempty_fintype ι
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · ext i j
    have h := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hA.isHermitian
    simpa [conjTranspose_apply] using congrArg (c * ·) h
  · have heq : star x ⬝ᵥ ((c • A) *ᵥ x) = c * (star x ⬝ᵥ (A *ᵥ x)) := by
      simp only [dotProduct, mulVec, Matrix.smul_apply, smul_eq_mul, star_trivial, mul_sum]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    rw [heq]
    exact mul_nonneg hc (hA.dotProduct_mulVec_nonneg x)

private theorem posSemidef_abs_entry_le {ι : Type*} [Finite ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {C : ℝ} (hdiag : ∀ z, A z z ≤ C) (z₁ z₂ : ι) :
    |A z₁ z₂| ≤ C := by
  classical
  cases nonempty_fintype ι
  have hsym : A z₂ z₁ = A z₁ z₂ := by
    simpa [conjTranspose_apply] using congrArg (fun M : Matrix ι ι ℝ ↦ M z₁ z₂) hA.isHermitian
  by_cases heq : z₁ = z₂
  · subst heq
    have hnn : 0 ≤ A z₁ z₁ := by
      simpa [Pi.single_apply, dotProduct, mulVec] using
        hA.dotProduct_mulVec_nonneg (Pi.single z₁ 1)
    rw [abs_of_nonneg hnn]; exact hdiag z₁
  · have hquad (s : ℝ) : 0 ≤ A z₁ z₁ + 2 * s * A z₁ z₂ + s ^ 2 * A z₂ z₂ := by
      let v : ι → ℝ := fun z ↦ if z = z₁ then 1 else if z = z₂ then s else 0
      have hv := hA.dotProduct_mulVec_nonneg v
      have heval : star v ⬝ᵥ (A *ᵥ v) = A z₁ z₁ + 2 * s * A z₁ z₂ + s ^ 2 * A z₂ z₂ := by
        have hpair : ∀ f : ι → ℝ, (∀ z, z ≠ z₁ → z ≠ z₂ → f z = 0) →
            ∑ z, f z = f z₁ + f z₂ := fun f hf ↦ by
          rw [← sum_subset (subset_univ ({z₁, z₂} : Finset ι)) fun z _ hz ↦ by
            simp only [mem_insert, mem_singleton, not_or] at hz; exact hf z hz.1 hz.2,
            sum_pair heq]
        simp only [dotProduct, mulVec, star_trivial]
        rw [hpair _ fun z hz1 hz2 ↦ by simp [v, hz1, hz2]]
        rw [hpair (fun z ↦ A z₁ z * v z) fun z hz1 hz2 ↦ by simp [v, hz1, hz2],
          hpair (fun z ↦ A z₂ z * v z) fun z hz1 hz2 ↦ by simp [v, hz1, hz2]]
        have heq' : z₂ ≠ z₁ := Ne.symm heq
        simp only [v, ↓reduceIte, heq', hsym]
        ring
      rwa [heval] at hv
    have hp := hquad 1; have hm := hquad (-1); have h1 := hdiag z₁; have h2 := hdiag z₂
    exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem posSemidef_vecMulVec {ι : Type*} [Finite ι] (w : ι → ℝ) :
    (Matrix.vecMulVec w w).PosSemidef := by
  cases nonempty_fintype ι
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · ext i j; simp [vecMulVec_apply, mul_comm]
  · have heq : star x ⬝ᵥ (Matrix.vecMulVec w w *ᵥ x) = (∑ i, x i * w i) ^ 2 := by
      simp only [dotProduct, mulVec, vecMulVec_apply, star_trivial, sq, sum_mul, mul_sum]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    rw [heq]; exact sq_nonneg _

/-- **Strong SDP duality for the general adversary bound**:
for every Boolean function `f : BitString N → Bool` and promise domain `P`, there exists a finite
dimension `k` and a feasible dual adversary `w : DualAdversary P f (Fin k)` attaining
`w.weight = generalAdversary P f`.
-/
theorem exists_dualAdversary_eq_generalAdversary {N : ℕ} (P : BitString N → Prop)
    (f : BitString N → Bool) :
    ∃ (k : ℕ) (w : DualAdversary P f (Fin k)), w.weight = generalAdversary P f := by
  classical
  by_cases hpair : ∃ x₁ x₀ : BitString N, P x₁ ∧ f x₁ = true ∧ P x₀ ∧ f x₀ = false
  · obtain ⟨x₁₀, x₀₀, hx₁P, hfx₁, hx₀P, hfx₀⟩ := hpair
    set W := generalAdversary P f
    have hW1 : 1 ≤ W := one_le_generalAdversary_of_pair hx₁P hfx₁ hx₀P hfx₀
    have hW0 : 0 ≤ W := zero_le_one.trans hW1
    let P₁ (s : BitString N) : Prop := P s ∧ f s = true
    let P₀ (s : BitString N) : Prop := P s ∧ f s = false
    have hP_disj {s : BitString N} (h1 : P₁ s) (h0 : P₀ s) : False := by
      have := h1.2; simp [h0.2] at this
    let X₁ := {x : BitString N // P₁ x}
    let X₀ := {y : BitString N // P₀ y}
    let Z := X₁ ⊕ X₀
    have hZpos : 0 < Fintype.card Z :=
      Fintype.card_pos_iff.2 ⟨Sum.inl ⟨x₁₀, hx₁P, hfx₁⟩⟩
    -- Step 1: Define the closed convex dual feasibility cone in `(X₁ → X₀ → ℝ) × (Z → ℝ)`.
    let cone : Set ((X₁ → X₀ → ℝ) × (Z → ℝ)) :=
      {p | ∃ R : Fin N → Matrix Z Z ℝ,
        (∀ i, (R i).PosSemidef) ∧
        (∀ z, ∑ i : Fin N, R i z z ≤ p.2 z) ∧
        (∀ (x : X₁) (y : X₀),
          p.1 x y = ∑ i with x.1 i ≠ y.1 i, R i (Sum.inl x) (Sum.inr y))}
    have hconv : Convex ℝ cone := by
      rintro ⟨M₁, c₁⟩ ⟨R₁, hR₁, hd₁, hm₁⟩ ⟨M₂, c₂⟩ ⟨R₂, hR₂, hd₂, hm₂⟩ a b ha hb -
      refine ⟨fun i ↦ a • R₁ i + b • R₂ i,
        fun i ↦ (posSemidef_smul (hR₁ i) ha).add (posSemidef_smul (hR₂ i) hb),
        fun z ↦ ?_, fun x y ↦ ?_⟩
      · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
          Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply]
        exact add_le_add (mul_le_mul_of_nonneg_left (hd₁ z) ha)
          (mul_le_mul_of_nonneg_left (hd₂ z) hb)
      · dsimp only at hm₁ hm₂
        change a * M₁ x y + b * M₂ x y = _
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
          hm₁, hm₂]
    have hsmul : ∀ {t : ℝ}, 0 ≤ t → ∀ {p}, p ∈ cone → t • p ∈ cone := by
      rintro t ht ⟨M, c⟩ ⟨R, hR, hd, hm⟩
      refine ⟨fun i ↦ t • R i, fun i ↦ posSemidef_smul (hR i) ht, fun z ↦ ?_, fun x y ↦ ?_⟩
      · simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, Prod.smul_snd, Pi.smul_apply]
        exact mul_le_mul_of_nonneg_left (hd z) ht
      · dsimp only at hm
        change t * M x y = _
        simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, hm]
    have hclosed : IsClosed cone := by
      refine IsSeqClosed.isClosed fun seq p hmem htend ↦ ?_
      choose R hRpsd hRdiag hRmat using hmem
      have hc_tend : Filter.Tendsto (fun n ↦ (seq n).2) Filter.atTop (nhds p.2) :=
        continuous_snd.continuousAt.tendsto.comp htend
      obtain ⟨C₀, hC₀⟩ := (Metric.isBounded_range_of_tendsto _ hc_tend).subset_closedBall 0
      let C := max C₀ 0
      have hbox_mem (n : ℕ) (i : Fin N) (z₁ z₂ : Z) : R n i z₁ z₂ ∈ Set.Icc (-C) C := by
        refine abs_le.1 (posSemidef_abs_entry_le (hRpsd n i) (fun z ↦ ?_) z₁ z₂)
        have hcz : ‖(seq n).2 z‖ ≤ C₀ :=
          (norm_le_pi_norm ((seq n).2) z).trans (by simpa using hC₀ (Set.mem_range_self n))
        have hdiag_nn (j : Fin N) : 0 ≤ R n j z z := by
          simpa [Pi.single_apply, dotProduct, mulVec] using
            (hRpsd n j).dotProduct_mulVec_nonneg (Pi.single z 1)
        exact (single_le_sum (fun j _ ↦ hdiag_nn j) (mem_univ i)).trans
          ((hRdiag n z).trans ((le_abs_self _).trans (hcz.trans (le_max_left _ _))))
      have hcomp : IsCompact (Set.pi Set.univ fun _ : Fin N ↦
          Set.pi Set.univ fun _ : Z ↦ Set.pi Set.univ fun _ : Z ↦ Set.Icc (-C) C) :=
        isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
      obtain ⟨Rlim', -, φ, hφmono, hφtend⟩ := hcomp.tendsto_subseq fun n i _ z₁ _ z₂ _ ↦
        hbox_mem n i z₁ z₂
      let Rlim : Fin N → Matrix Z Z ℝ := fun i ↦ Matrix.of (Rlim' i)
      have hentry (i : Fin N) (z₁ z₂ : Z) :
          Filter.Tendsto (fun k ↦ R (φ k) i z₁ z₂) Filter.atTop (nhds (Rlim i z₁ z₂)) :=
        (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hφtend i) z₁)) z₂
      have tendsto_sum {α : Type} (s : Finset α) {g : α → ℕ → ℝ} {l : α → ℝ}
          (hg : ∀ a ∈ s, Filter.Tendsto (g a) Filter.atTop (nhds (l a))) :
          Filter.Tendsto (fun k ↦ ∑ a ∈ s, g a k) Filter.atTop (nhds (∑ a ∈ s, l a)) := by
        induction s using Finset.cons_induction with
        | empty => simp
        | cons a s ha ih =>
          simp only [sum_cons]
          exact (hg a (mem_cons_self a s)).add (ih fun b hb ↦ hg b (mem_cons_of_mem hb))
      refine ⟨Rlim, fun i ↦ Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v ↦ ?_⟩,
        fun z ↦ ?_, fun x y ↦ ?_⟩
      · ext z₁ z₂
        simp only [conjTranspose_apply, star_trivial]
        refine tendsto_nhds_unique (hentry i z₂ z₁) ?_
        have hsym_k (k : ℕ) : R (φ k) i z₂ z₁ = R (φ k) i z₁ z₂ := by
          simpa [conjTranspose_apply] using
            congrArg (fun M : Matrix Z Z ℝ ↦ M z₁ z₂) (hRpsd (φ k) i).isHermitian
        simpa only [hsym_k] using hentry i z₁ z₂
      · simp only [dotProduct, mulVec, star_trivial]
        refine ge_of_tendsto
          (tendsto_sum _ fun z₁ _ ↦ tendsto_const_nhds.mul
            (tendsto_sum _ fun z₂ _ ↦ (hentry i z₁ z₂).mul tendsto_const_nhds))
          (Filter.Eventually.of_forall fun k ↦ ?_)
        simpa [dotProduct, mulVec, star_trivial] using (hRpsd (φ k) i).dotProduct_mulVec_nonneg v
      · refine le_of_tendsto_of_tendsto (tendsto_sum _ fun i _ ↦ hentry i z z)
          ((tendsto_pi_nhds.1 hc_tend z).comp hφmono.tendsto_atTop)
          (Filter.Eventually.of_forall fun k ↦ hRdiag (φ k) z)
      · have hm_tend : Filter.Tendsto (fun k ↦ (seq (φ k)).1 x y) Filter.atTop (nhds (p.1 x y)) :=
          ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1
            (continuous_fst.continuousAt.tendsto.comp htend) x)) y).comp hφmono.tendsto_atTop
        refine tendsto_nhds_unique hm_tend ?_
        have hsum_t := tendsto_sum (univ.filter fun i : Fin N ↦ x.1 i ≠ y.1 i)
          fun i _ ↦ hentry i (Sum.inl x) (Sum.inr y)
        simpa only [fun k ↦ hRmat (φ k) x y] using hsum_t
    -- Step 2: Show `(1, fun _ ↦ W) ∈ cone` by Hahn–Banach separation.
    let target : (X₁ → X₀ → ℝ) × (Z → ℝ) := (fun _ _ ↦ 1, fun _ ↦ W)
    have hmem_target : target ∈ cone := by
      by_contra hnot
      obtain ⟨L, u, hLcone, hLtgt⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
      let basisM (x : X₁) (y : X₀) : X₁ → X₀ → ℝ := fun x' y' ↦ if x' = x ∧ y' = y then 1 else 0
      let B : X₁ → X₀ → ℝ := fun x y ↦ L (basisM x y, 0)
      let d : Z → ℝ := fun z ↦ -L (0, Pi.single z 1)
      have hLeval (M : X₁ → X₀ → ℝ) (c : Z → ℝ) :
          L (M, c) = (∑ x, ∑ y, B x y * M x y) - ∑ z, d z * c z := by
        have hMeq : M = ∑ x : X₁, ∑ y : X₀, M x y • basisM x y := by
          ext x' y'
          simp only [basisM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
            mul_zero]
          rw [sum_eq_single x' (fun x _ hx ↦ sum_eq_zero fun y _ ↦ by
              split_ifs with h; exacts [(hx h.1.symm).elim, rfl]) (by simp),
            sum_eq_single y' (fun y _ hy ↦ by
              split_ifs with h; exacts [(hy h.2.symm).elim, rfl]) (by simp)]
          simp
        have hceq : c = ∑ z : Z, c z • Pi.single z (1 : ℝ) := by
          ext z'; simp [Finset.sum_apply, Pi.single_apply]
        have hsplit : (M, c) = (M, 0) + (0, c) := by ext <;> simp
        rw [hsplit, map_add]
        have h1 : L (M, 0) = ∑ x, ∑ y, B x y * M x y := by
          conv_lhs => rw [hMeq]
          have hpair : (∑ x : X₁, ∑ y : X₀, M x y • basisM x y, (0 : Z → ℝ)) =
              ∑ x : X₁, ∑ y : X₀, M x y • (basisM x y, (0 : Z → ℝ)) :=
            Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])
          rw [hpair, map_sum]
          exact sum_congr rfl fun x _ ↦ by
            rw [map_sum]; exact sum_congr rfl fun y _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
        have h2 : L (0, c) = -∑ z, d z * c z := by
          conv_lhs => rw [hceq]
          have hpair : ((0 : X₁ → X₀ → ℝ), ∑ z : Z, c z • Pi.single z (1 : ℝ)) =
              ∑ z : Z, c z • ((0 : X₁ → X₀ → ℝ), Pi.single z (1 : ℝ)) :=
            Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])
          rw [hpair, map_sum, ← sum_neg_distrib]
          exact sum_congr rfl fun z _ ↦ by rw [map_smul, smul_eq_mul]; simp [d, mul_comm]
        rw [h1, h2, sub_eq_add_neg]
      have hzero_mem : ((0 : X₁ → X₀ → ℝ), (0 : Z → ℝ)) ∈ cone :=
        ⟨0, fun _ ↦ Matrix.PosSemidef.zero, fun _ ↦ by simp, fun _ _ ↦ by simp⟩
      have hu_pos : 0 < u := by
        have h := hLcone 0 hzero_mem
        rwa [map_zero] at h
      have hLnonpos : ∀ q ∈ cone, L q ≤ 0 := fun q hq ↦ by
        by_contra hpos
        push Not at hpos
        let t := u / L q + 1
        have hlt := hLcone (t • q)
          (hsmul (add_nonneg (div_nonneg hu_pos.le hpos.le) zero_le_one) hq)
        rw [map_smul, smul_eq_mul, show t * L q = u + L q by dsimp [t]; field_simp] at hlt
        linarith
      have hgap : W * ∑ z, d z < ∑ x, ∑ y, B x y := by
        have h := hu_pos.trans hLtgt
        rw [hLeval] at h
        simp only [mul_one, ← sum_mul] at h
        linarith
      have hd_nn (z : Z) : 0 ≤ d z := by
        have hmem : ((0 : X₁ → X₀ → ℝ), Pi.single z (1 : ℝ)) ∈ cone :=
          ⟨0, fun _ ↦ Matrix.PosSemidef.zero, fun z' ↦ by
            simp only [Pi.zero_apply, Matrix.zero_apply, sum_const_zero, Pi.single_apply]
            split_ifs <;> norm_num, fun _ _ ↦ by simp⟩
        have h := hLnonpos _ hmem
        rw [hLeval] at h
        simp only [Pi.zero_apply, mul_zero, sum_const_zero, zero_sub, Pi.single_apply, mul_ite,
          mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
        linarith
      have hrank1 (i₀ : Fin N) (w : Z → ℝ) :
          ∑ x : X₁, ∑ y : X₀, (if x.1 i₀ ≠ y.1 i₀ then B x y else 0) *
            w (Sum.inl x) * w (Sum.inr y) ≤ ∑ z : Z, d z * w z ^ 2 := by
        let M : X₁ → X₀ → ℝ := fun x y ↦
          if x.1 i₀ ≠ y.1 i₀ then w (Sum.inl x) * w (Sum.inr y) else 0
        let c : Z → ℝ := fun z ↦ w z ^ 2
        have hmem : (M, c) ∈ cone := by
          refine ⟨fun i ↦ if i = i₀ then Matrix.vecMulVec w w else 0,
            fun i ↦ by dsimp only; split_ifs; exacts [posSemidef_vecMulVec w, .zero],
            fun z ↦ by
              simp [c, apply_ite (fun A : Matrix Z Z ℝ ↦ A z z), vecMulVec_apply, sq],
            fun x y ↦ ?_⟩
          simp only [M, apply_ite (fun A : Matrix Z Z ℝ ↦ A (Sum.inl x) (Sum.inr y)),
            vecMulVec_apply, Matrix.zero_apply, sum_ite_eq', mem_filter, mem_univ, true_and]
        have h := hLnonpos _ hmem
        rw [hLeval] at h
        have hrewrite : ∑ x, ∑ y, B x y * M x y =
            ∑ x, ∑ y, (if x.1 i₀ ≠ y.1 i₀ then B x y else 0) *
              w (Sum.inl x) * w (Sum.inr y) :=
          sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by
            simp only [M]; split_ifs <;> ring
        linarith
      -- Perturb `d` to strictly positive weights `d'` and build a primal adversary matrix `Γ̂`.
      let δ := ((∑ x, ∑ y, B x y) - W * ∑ z, d z) / (2 * W * Fintype.card Z)
      have hδ_pos : 0 < δ := div_pos (by linarith) (by positivity)
      let d' : Z → ℝ := fun z ↦ d z + δ
      have hd'_pos (z : Z) : 0 < d' z := add_pos_of_nonneg_of_pos (hd_nn z) hδ_pos
      have hgap' : W * ∑ z, d' z < ∑ x, ∑ y, B x y := by
        have hsum : ∑ z, d' z = (∑ z, d z) + Fintype.card Z * δ := by
          simp [d', sum_add_distrib]
        have hmul : W * (Fintype.card Z * δ) = ((∑ x, ∑ y, B x y) - W * ∑ z, d z) / 2 := by
          have hWne : W ≠ 0 := by linarith
          have hZne : (Fintype.card Z : ℝ) ≠ 0 := by positivity
          dsimp [δ]; field_simp
        rw [hsum, mul_add, hmul]; linarith
      let entryVal (x : X₁) (y : X₀) : ℝ :=
        B x y / (2 * √(d' (Sum.inl x)) * √(d' (Sum.inr y)))
      let entry (s t : BitString N) : ℝ :=
        if hs : P₁ s then
          if ht : P₀ t then entryVal ⟨s, hs⟩ ⟨t, ht⟩ else 0
        else if hs0 : P₀ s then
          if ht1 : P₁ t then entryVal ⟨t, ht1⟩ ⟨s, hs0⟩ else 0
        else 0
      let Γ : Matrix (BitString N) (BitString N) ℝ := Matrix.of entry
      have hsym : Γ.IsSymm := Matrix.ext fun s t ↦ by
        simp only [Γ, transpose_apply, of_apply, entry]
        by_cases hs1 : P₁ s
        · have hs0 : ¬P₀ s := hP_disj hs1
          by_cases ht0 : P₀ t
          · have ht1 : ¬P₁ t := fun h ↦ hP_disj h ht0
            simp [hs1, ht0, ht1]
          · by_cases ht1 : P₁ t <;> simp [hs1, hs0, ht0, ht1]
        · by_cases hs0 : P₀ s
          · by_cases ht1 : P₁ t
            · simp [hs1, hs0, ht1]
            · simp [hs1, hs0, ht1]
          · by_cases ht1 : P₁ t <;> by_cases ht0 : P₀ t <;> simp [hs1, hs0, ht1, ht0]
      have hadv : IsAdversaryMatrix P f Γ := fun s t hne ↦ by
        simp only [Γ, of_apply, entry] at hne
        by_cases hs1 : P₁ s
        · simp only [hs1, ↓reduceDIte] at hne
          by_cases ht0 : P₀ t
          · exact ⟨hs1.1, ht0.1, by rw [hs1.2, ht0.2]; decide⟩
          · simp [ht0] at hne
        · simp only [hs1, ↓reduceDIte] at hne
          by_cases hs0 : P₀ s
          · simp only [hs0, ↓reduceDIte] at hne
            by_cases ht1 : P₁ t
            · exact ⟨hs0.1, ht1.1, by rw [hs0.2, ht1.2]; decide⟩
            · simp [ht1] at hne
          · simp [hs0] at hne
      have hsub_sum (q : BitString N → Prop) [DecidablePred q] (h : BitString N → ℝ) :
          ∑ x : {s : BitString N // q s}, h x.1 = ∑ s with q s, h s := by
        rw [← sum_attach (univ.filter q)]
        exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun s ↦ by simp) _ _ fun _ ↦ rfl
      have hsum_pair (g : BitString N → BitString N → ℝ)
          (hg : ∀ s t, ¬(P₁ s ∧ P₀ t) → ¬(P₀ s ∧ P₁ t) → g s t = 0) :
          ∑ s, ∑ t, g s t =
            (∑ x : X₁, ∑ y : X₀, g x.1 y.1) + ∑ x : X₁, ∑ y : X₀, g y.1 x.1 := by
        have h1 : ∑ x : X₁, ∑ y : X₀, g x.1 y.1 =
            ∑ s, ∑ t, if P₁ s then if P₀ t then g s t else 0 else 0 := by
          rw [hsub_sum P₁ (fun s ↦ ∑ y : X₀, g s y.1), sum_filter]
          refine sum_congr rfl fun s _ ↦ ?_
          rw [hsub_sum P₀ (fun t ↦ g s t), sum_filter]
          split_ifs <;> simp
        have h2 : ∑ x : X₁, ∑ y : X₀, g y.1 x.1 =
            ∑ s, ∑ t, if P₀ s then if P₁ t then g s t else 0 else 0 := by
          rw [hsub_sum P₁ (fun t ↦ ∑ y : X₀, g y.1 t), sum_filter]
          refine (sum_congr rfl fun t _ ↦ ?_).trans sum_comm
          rw [hsub_sum P₀ (fun s ↦ g s t), sum_filter]
          by_cases ht : P₁ t <;> simp [ht]
        rw [h1, h2, ← sum_add_distrib]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun t _ ↦ ?_
        by_cases hs1 : P₁ s
        · have hs0 : ¬P₀ s := hP_disj hs1
          by_cases ht0 : P₀ t <;> simp [hs1, hs0, ht0, hg s t]
        · by_cases hs0 : P₀ s
          · by_cases ht1 : P₁ t <;> simp [hs1, hs0, ht1, hg s t]
          · simp [hs1, hs0, hg s t]
      have hΓ_zero (s t : BitString N) (h1 : ¬(P₁ s ∧ P₀ t)) (h2 : ¬(P₀ s ∧ P₁ t)) :
          Γ s t = 0 := Classical.byContradiction fun hne ↦ by
        obtain ⟨hsP, htP, hfne⟩ := hadv s t hne
        cases hfs : f s <;> cases hft : f t
        exacts [hfne (hfs.trans hft.symm), h2 ⟨⟨hsP, hfs⟩, ⟨htP, hft⟩⟩,
          h1 ⟨⟨hsP, hfs⟩, ⟨htP, hft⟩⟩, hfne (hfs.trans hft.symm)]
      have hmd : maxDiffNorm Γ ≤ 1 := (maxDiffNorm_le_iff zero_le_one).2 fun i₀ ↦ by
        refine Matrix.opNorm_toEuclideanCLM_le_of_inner _ zero_le_one fun α β hα hβ ↦ ?_
        have boundOne (p q : EuclideanSpace ℝ (BitString N)) :
            ∑ x : X₁, ∑ y : X₀,
              p.ofLp x.1 * ((Γ.hadamard (diffMatrix i₀)) x.1 y.1 * q.ofLp y.1) ≤
              (1 / 2) * ((∑ x : X₁, p.ofLp x.1 ^ 2) + ∑ y : X₀, q.ofLp y.1 ^ 2) := by
          let w : Z → ℝ := Sum.elim
            (fun x ↦ p.ofLp x.1 / √(d' (Sum.inl x)))
            (fun y ↦ q.ofLp y.1 / √(d' (Sum.inr y)))
          have hlhs : ∑ x : X₁, ∑ y : X₀,
              p.ofLp x.1 * ((Γ.hadamard (diffMatrix i₀)) x.1 y.1 * q.ofLp y.1) =
              (1 / 2) * ∑ x : X₁, ∑ y : X₀,
                (if x.1 i₀ ≠ y.1 i₀ then B x y else 0) * w (Sum.inl x) * w (Sum.inr y) := by
            rw [mul_sum]
            refine sum_congr rfl fun x _ ↦ ?_
            rw [mul_sum]
            refine sum_congr rfl fun y _ ↦ ?_
            have hΓxy : Γ x.1 y.1 = entryVal x y := by simp [Γ, entry, x.2, y.2]
            simp only [hadamard_apply, diffMatrix_apply, hΓxy, entryVal, w, Sum.elim_inl,
              Sum.elim_inr]
            split_ifs <;> ring
          have hrhs : ∑ z : Z, d z * w z ^ 2 ≤
              (∑ x : X₁, p.ofLp x.1 ^ 2) + ∑ y : X₀, q.ofLp y.1 ^ 2 := by
            rw [Fintype.sum_sum_type]
            refine add_le_add (sum_le_sum fun x _ ↦ ?_) (sum_le_sum fun y _ ↦ ?_)
            · have hpos := hd'_pos (Sum.inl x)
              simp only [w, Sum.elim_inl, div_pow, Real.sq_sqrt hpos.le]
              rw [mul_div_left_comm]
              exact mul_le_of_le_one_right (sq_nonneg _)
                ((div_le_one hpos).2 (by dsimp [d']; linarith))
            · have hpos := hd'_pos (Sum.inr y)
              simp only [w, Sum.elim_inr, div_pow, Real.sq_sqrt hpos.le]
              rw [mul_div_left_comm]
              exact mul_le_of_le_one_right (sq_nonneg _)
                ((div_le_one hpos).2 (by dsimp [d']; linarith))
          rw [hlhs]
          exact mul_le_mul_of_nonneg_left ((hrank1 i₀ w).trans hrhs) (by norm_num)
        have hnorm_split (r : EuclideanSpace ℝ (BitString N)) (hr1 : ‖r‖ ≤ 1) :
            (∑ x : X₁, r.ofLp x.1 ^ 2) + ∑ y : X₀, r.ofLp y.1 ^ 2 ≤ 1 := by
          have hdisj : Disjoint (univ.filter P₁) (univ.filter P₀) :=
            disjoint_filter.2 fun _ _ ↦ hP_disj
          rw [hsub_sum P₁ fun a ↦ r.ofLp a ^ 2, hsub_sum P₀ fun a ↦ r.ofLp a ^ 2,
            ← sum_union hdisj]
          exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _).trans
            ((EuclideanSpace.norm_le_one_iff_sum_sq_le_one r).1 hr1)
        rw [Matrix.inner_toEuclideanCLM]
        simp only [dotProduct, mulVec, mul_sum]
        rw [hsum_pair _ fun s t h1 h2 ↦ by simp [hadamard_apply, hΓ_zero s t h1 h2]]
        have hswap : ∑ x : X₁, ∑ y : X₀,
            α.ofLp y.1 * ((Γ.hadamard (diffMatrix i₀)) y.1 x.1 * β.ofLp x.1) =
            ∑ x : X₁, ∑ y : X₀,
              β.ofLp x.1 * ((Γ.hadamard (diffMatrix i₀)) x.1 y.1 * α.ofLp y.1) :=
          sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by
            have h2 : diffMatrix i₀ y.1 x.1 = diffMatrix i₀ x.1 y.1 := by
              simp [diffMatrix_apply, ne_comm]
            simp only [hadamard_apply, hsym.apply x.1 y.1, h2]; ring
        rw [hswap]
        linarith [boundOne α β, boundOne β α, hnorm_split α hα, hnorm_split β hβ]
      -- Test `Γ` on `v_s = √(d' s)` to deduce `W < ‖Γ‖ ≤ W`.
      let v : EuclideanSpace ℝ (BitString N) := WithLp.toLp 2 fun s ↦
        if hs1 : P₁ s then √(d' (Sum.inl ⟨s, hs1⟩))
        else if hs0 : P₀ s then √(d' (Sum.inr ⟨s, hs0⟩))
        else 0
      have hv_sq : ‖v‖ ^ 2 = ∑ z : Z, d' z := by
        rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
        have h1 : ∑ x : X₁, d' (Sum.inl x) = ∑ a with P₁ a, v.ofLp a ^ 2 := by
          trans ∑ x : X₁, v.ofLp x.1 ^ 2
          · refine sum_congr rfl fun x _ ↦ ?_
            simp [v, x.2, Real.sq_sqrt (hd'_pos (Sum.inl x)).le]
          · exact hsub_sum P₁ fun a ↦ v.ofLp a ^ 2
        have h2 : ∑ y : X₀, d' (Sum.inr y) = ∑ a with P₀ a, v.ofLp a ^ 2 := by
          trans ∑ y : X₀, v.ofLp y.1 ^ 2
          · refine sum_congr rfl fun y _ ↦ ?_
            have hnot1 : ¬P₁ y.1 := fun h ↦ hP_disj h y.2
            simp [v, hnot1, y.2, Real.sq_sqrt (hd'_pos (Sum.inr y)).le]
          · exact hsub_sum P₀ fun a ↦ v.ofLp a ^ 2
        have hdisj : Disjoint (univ.filter P₁) (univ.filter P₀) :=
          disjoint_filter.2 fun _ _ ↦ hP_disj
        rw [h1, h2, ← sum_union hdisj]
        refine (sum_subset (subset_univ _) fun a _ ha ↦ ?_).symm
        simp only [mem_union, mem_filter, mem_univ, true_and, not_or] at ha
        simp [v, ha.1, ha.2]
      have : 0 < ∑ z : Z, d' z :=
        sum_pos (fun z _ ↦ hd'_pos z) (univ_nonempty_iff.2 ⟨Sum.inl ⟨x₁₀, hx₁P, hfx₁⟩⟩)
      have hquad : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) = ∑ x, ∑ y, B x y := by
        rw [Matrix.inner_toEuclideanCLM]
        simp only [dotProduct, mulVec, mul_sum]
        rw [hsum_pair _ fun s t h1 h2 ↦ by simp [hΓ_zero s t h1 h2]]
        have heval (x : X₁) (y : X₀) :
            v.ofLp x.1 * (Γ x.1 y.1 * v.ofLp y.1) = (1 / 2) * B x y ∧
            v.ofLp y.1 * (Γ y.1 x.1 * v.ofLp x.1) = (1 / 2) * B x y := by
          have hy_not1 : ¬P₁ y.1 := fun h ↦ hP_disj h y.2
          have hsx : √(d' (Sum.inl x)) ≠ 0 := (Real.sqrt_pos.2 (hd'_pos _)).ne'
          have hsy : √(d' (Sum.inr y)) ≠ 0 := (Real.sqrt_pos.2 (hd'_pos _)).ne'
          have hΓ1 : Γ x.1 y.1 = entryVal x y := by simp [Γ, entry, x.2, y.2]
          have hΓ2 : Γ y.1 x.1 = entryVal x y := by simp [Γ, entry, hy_not1, x.2, y.2]
          have hvx : v.ofLp x.1 = √(d' (Sum.inl x)) := by simp [v, x.2]
          have hvy : v.ofLp y.1 = √(d' (Sum.inr y)) := by simp [v, hy_not1, y.2]
          rw [hvx, hvy, hΓ1, hΓ2]
          dsimp only [entryVal]
          constructor <;> field_simp
        simp only [fun x y ↦ (heval x y).1, fun x y ↦ (heval x y).2, ← mul_sum]
        ring
      have hinner_le : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (∑ z : Z, d' z) :=
        (real_inner_le_norm _ _).trans <|
          (mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) Γ).le_opNorm v)
            (norm_nonneg _)).trans_eq (by rw [← hv_sq]; ring)
      have hΓle : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ W :=
        (((generalAdversary_le_iff hW0).1 le_rfl) Γ hsym hadv).trans
          ((mul_le_mul_of_nonneg_left hmd hW0).trans_eq (mul_one W))
      nlinarith
    -- Step 3: Extract real vectors from the PSD witness matrices `R i`.
    obtain ⟨R, hRpsd, hRdiag, hRmat⟩ := hmem_target
    let eZ : Fin (Fintype.card Z) ≃ Z := (Fintype.equivFin Z).symm
    let vec (s : BitString N) (i : Fin N) (d : Fin (Fintype.card Z)) : ℝ :=
      if hs1 : P₁ s then psdFactor (hRpsd i) (eZ d) (Sum.inl ⟨s, hs1⟩)
      else if hs0 : P₀ s then psdFactor (hRpsd i) (eZ d) (Sum.inr ⟨s, hs0⟩)
      else 0
    have hgram (i : Fin N) (z₁ z₂ : Z) :
        ∑ d : Fin (Fintype.card Z),
          psdFactor (hRpsd i) (eZ d) z₁ * psdFactor (hRpsd i) (eZ d) z₂ = R i z₁ z₂ :=
      (Fintype.sum_equiv eZ _ (fun k ↦ psdFactor (hRpsd i) k z₁ * psdFactor (hRpsd i) k z₂)
        fun _ ↦ rfl).trans (sum_psdFactor_mul (hRpsd i) z₁ z₂)
    refine ⟨Fintype.card Z, DualAdversary.mk vec W hW0 (fun s hsP ↦ ?_)
      (fun x y hxP hyP hfx hfy ↦ ?_), rfl⟩
    · cases hfs : f s
      · have hs0 : P₀ s := ⟨hsP, hfs⟩
        have hnot1 : ¬P₁ s := fun h ↦ hP_disj h hs0
        simp only [vec, hnot1, hs0, ↓reduceDIte, sq, hgram]
        exact hRdiag (Sum.inr ⟨s, hs0⟩)
      · have hs1 : P₁ s := ⟨hsP, hfs⟩
        simp only [vec, hs1, ↓reduceDIte, sq, hgram]
        exact hRdiag (Sum.inl ⟨s, hs1⟩)
    · have hx1 : P₁ x := ⟨hxP, hfx⟩
      have hy0 : P₀ y := ⟨hyP, hfy⟩
      have hynot1 : ¬P₁ y := fun h ↦ hP_disj h hy0
      simp only [vec, hx1, hynot1, hy0, ↓reduceDIte, hgram]
      exact (hRmat ⟨x, hx1⟩ ⟨y, hy0⟩).symm
  · have hconst : ∀ x y, P x → P y → f x = f y := fun x y hx hy ↦ by
      cases hfx : f x <;> cases hfy : f y
      exacts [rfl, (hpair ⟨y, x, hy, hfy, hx, hfx⟩).elim,
        (hpair ⟨x, y, hx, hfx, hy, hfy⟩).elim, rfl]
    refine ⟨0, DualAdversary.mk (fun _ _ d ↦ d.elim0) 0 le_rfl (fun _ _ ↦ by simp)
      (fun x y hx hy hfx hfy ↦ (hpair ⟨x, y, hx, hfx, hy, hfy⟩).elim),
      (generalAdversary_eq_zero_of_subsingleton hconst).symm⟩

end DualSDP

/-! ### Reichardt / LMRSS alternating-reflection quantum query algorithm -/

section ReflectionAlgorithm

private noncomputable def clockVec (T : ℕ) : EuclideanSpace ℂ (Fin T) :=
  WithLp.toLp 2 fun _ ↦ (((√(T : ℝ))⁻¹ : ℝ) : ℂ)

private noncomputable def householderStep {T : ℕ} (v φ : EuclideanSpace ℂ (Fin T)) :
    EuclideanSpace ℂ (Fin T) :=
  φ - ((2 : ℂ) * (inner ℂ v φ / ((‖v‖ : ℂ) ^ 2))) • v

private theorem householderStep_invol {T : ℕ} (v φ : EuclideanSpace ℂ (Fin T)) :
    householderStep v (householderStep v φ) = φ := by
  by_cases hv : v = 0
  · simp [householderStep, hv]
  · have hv2 : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv)
    have hvv : inner ℂ v v = (‖v‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v
    simp only [householderStep, inner_sub_right, inner_smul_right, hvv, sub_sub, ← add_smul]
    rw [show (2 : ℂ) * (inner ℂ v φ / (‖v‖ : ℂ) ^ 2) + 2 * ((inner ℂ v φ -
      2 * (inner ℂ v φ / (‖v‖ : ℂ) ^ 2) * (‖v‖ : ℂ) ^ 2) / (‖v‖ : ℂ) ^ 2) = 0 by
        field_simp; ring, zero_smul, sub_zero]

/-- Householder involution `φ ↦ φ - (2 ⟨v, φ⟩ / ‖v‖²) v` as a linear isometric equivalence. -/
private noncomputable def householderIso {T : ℕ} (v : EuclideanSpace ℂ (Fin T)) :
    EuclideanSpace ℂ (Fin T) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T) where
  toFun := householderStep v
  invFun := householderStep v
  map_add' x y := by simp only [householderStep, inner_add_right, add_div, mul_add, add_smul]; abel
  map_smul' c x := by
    simp only [householderStep, inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]
    rw [show (2 : ℂ) * (c * inner ℂ v x / (‖v‖ : ℂ) ^ 2) =
      c * (2 * (inner ℂ v x / (‖v‖ : ℂ) ^ 2)) by ring]
  left_inv := householderStep_invol v
  right_inv := householderStep_invol v
  norm_map' φ := by
    by_cases hv : v = 0
    · simp [householderStep, hv]
    · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      have hv2 : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv)
      have hzv : inner ℂ φ v = starRingEnd ℂ (inner ℂ v φ) := (inner_conj_symm φ v).symm
      have hvv : inner ℂ v v = (‖v‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v
      have h0 : inner ℂ (householderStep v φ) (householderStep v φ) = inner ℂ φ φ := by
        simp only [householderStep, inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, map_mul, map_div₀, map_ofNat, map_pow, Complex.conj_ofReal, hzv, hvv]
        field_simp; ring
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h0
      exact_mod_cast h0

private theorem householderIso_swap {T : ℕ} {u e : EuclideanSpace ℂ (Fin T)} {r : ℝ}
    (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (hr : inner ℂ u e = (r : ℂ)) :
    householderIso (u - e) u = e := by
  change householderStep (u - e) u = e
  dsimp only [householderStep]
  by_cases heq : u = e
  · simp [heq]
  · have hre : inner ℂ e u = (r : ℂ) :=
      (inner_conj_symm e u).symm.trans (by rw [hr, Complex.conj_ofReal])
    have huu : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
    have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
    have hv_sq : (‖u - e‖ : ℂ) ^ 2 = 2 - 2 * (r : ℂ) := by
      have h : inner ℂ (u - e) (u - e) = 2 - 2 * (r : ℂ) := by
        simp only [inner_sub_left, inner_sub_right, huu, hee, hr, hre]; ring
      rwa [inner_self_eq_norm_sq_to_K] at h
    have hvu : inner ℂ (u - e) u = 1 - (r : ℂ) := by rw [inner_sub_left, huu, hre]
    have hv2_ne : (‖u - e‖ : ℂ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (sub_ne_zero.2 heq)))
    rw [show (2 : ℂ) * (inner ℂ (u - e) u / (‖u - e‖ : ℂ) ^ 2) = 1 by
      rw [mul_div_assoc', div_eq_iff hv2_ne, hv_sq, hvu]; ring, one_smul, sub_sub_cancel]

private noncomputable def zeroVec {T : ℕ} (hT : 0 < T) : EuclideanSpace ℂ (Fin T) :=
  WithLp.toLp 2 fun t ↦ if t = ⟨0, hT⟩ then 1 else 0

private theorem norm_clockVec {T : ℕ} (hT : 0 < T) : ‖clockVec T‖ = 1 := by
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.2 hT
  refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 ?_
  rw [EuclideanSpace.norm_sq_eq]
  have hterm (t : Fin T) : ‖(clockVec T).ofLp t‖ ^ 2 = (T : ℝ)⁻¹ := by
    simp only [clockVec, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hTpos.le]
  simp only [hterm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel₀ hTpos.ne', one_pow]

private theorem norm_zeroVec {T : ℕ} (hT : 0 < T) : ‖zeroVec hT‖ = 1 :=
  (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 <| by
    rw [EuclideanSpace.norm_sq_eq,
      sum_eq_single ⟨0, hT⟩ (fun t _ ht ↦ by simp [zeroVec, ht]) (by simp)]
    simp [zeroVec]

private theorem inner_zeroVec_left {T : ℕ} (hT : 0 < T) (ψ : EuclideanSpace ℂ (Fin T)) :
    inner ℂ (zeroVec hT) ψ = ψ.ofLp ⟨0, hT⟩ := by
  rw [PiLp.inner_apply, sum_eq_single ⟨0, hT⟩ (fun t _ ht ↦ by simp [zeroVec, ht]) (by simp)]
  simp [zeroVec]

private theorem exists_clockUnitary {T : ℕ} (hT : 0 < T) :
    ∃ L : EuclideanSpace ℂ (Fin T) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T),
      ∀ φ, (L φ).ofLp ⟨0, hT⟩ = ∑ t : Fin T, (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * φ.ofLp t := by
  have hr : inner ℂ (clockVec T) (zeroVec hT) = (((√(T : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [← inner_conj_symm, inner_zeroVec_left]; simp [clockVec]
  let L := householderIso (clockVec T - zeroVec hT)
  have hswap : L (clockVec T) = zeroVec hT :=
    householderIso_swap (norm_clockVec hT) (norm_zeroVec hT) hr
  refine ⟨L, fun φ ↦ ?_⟩
  rw [← inner_zeroVec_left hT (L φ), ← hswap, L.inner_map_map, PiLp.inner_apply]
  exact sum_congr rfl fun t _ ↦ by simp [clockVec, mul_comm]

/-- Apply a linear isometric equivalence on `Fin T` fiberwise on `Fin T × B`. -/
private noncomputable def liftClock {T : ℕ} {B : Type*} [Fintype B]
    (L : EuclideanSpace ℂ (Fin T) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T)) :
    EuclideanSpace ℂ (Fin T × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T × B) where
  toFun Ψ := WithLp.toLp 2 fun (t, b) ↦ (L (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, b))).ofLp t
  invFun Ψ := WithLp.toLp 2 fun (t, b) ↦ (L.symm (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, b))).ofLp t
  map_add' Ψ₁ Ψ₂ := by
    ext ⟨t, b⟩
    have h : (WithLp.toLp 2 fun s ↦ (Ψ₁ + Ψ₂).ofLp (s, b)) =
        (WithLp.toLp 2 fun s ↦ Ψ₁.ofLp (s, b)) + (WithLp.toLp 2 fun s ↦ Ψ₂.ofLp (s, b)) := by
      ext s; rfl
    change (L (WithLp.toLp 2 fun s ↦ (Ψ₁ + Ψ₂).ofLp (s, b))).ofLp t =
      (L (WithLp.toLp 2 fun s ↦ Ψ₁.ofLp (s, b))).ofLp t +
        (L (WithLp.toLp 2 fun s ↦ Ψ₂.ofLp (s, b))).ofLp t
    rw [h, map_add, PiLp.add_apply]
  map_smul' c Ψ := by
    ext ⟨t, b⟩
    have h : (WithLp.toLp 2 fun s ↦ (c • Ψ).ofLp (s, b)) =
        c • (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, b)) := by ext s; rfl
    change (L (WithLp.toLp 2 fun s ↦ (c • Ψ).ofLp (s, b))).ofLp t =
      c * (L (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, b))).ofLp t
    rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]
  left_inv Ψ := by
    ext ⟨t, b⟩; exact congrArg (fun φ ↦ φ.ofLp t) (L.symm_apply_apply _)
  right_inv Ψ := by
    ext ⟨t, b⟩; exact congrArg (fun φ ↦ φ.ofLp t) (L.apply_symm_apply _)
  norm_map' Ψ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 <| by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change ∑ p : Fin T × B, ‖(L (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, p.2))).ofLp p.1‖ ^ 2 =
      ∑ p : Fin T × B, ‖Ψ.ofLp p‖ ^ 2
    rw [Fintype.sum_prod_type' (fun t b ↦ ‖(L (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, b))).ofLp t‖ ^ 2),
      Fintype.sum_prod_type' (fun t b ↦ ‖Ψ.ofLp (t, b)‖ ^ 2), sum_comm,
      sum_comm (s := univ) (f := fun t b ↦ ‖Ψ.ofLp (t, b)‖ ^ 2)]
    refine sum_congr rfl fun b _ ↦ ?_
    have hn := congrArg (· ^ 2) (L.norm_map (WithLp.toLp 2 fun s ↦ Ψ.ofLp (s, b)))
    rwa [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hn

/-- Apply a linear isometric equivalence on `B` conditionally on `act t = true`. -/
private noncomputable def condFiber {T : ℕ} {B : Type*} [Fintype B] (act : Fin T → Bool)
    (L : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (Fin T × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T × B) where
  toFun Ψ := WithLp.toLp 2 fun (t, b) ↦
    if act t then (L (WithLp.toLp 2 fun b' ↦ Ψ.ofLp (t, b'))).ofLp b else Ψ.ofLp (t, b)
  invFun Ψ := WithLp.toLp 2 fun (t, b) ↦
    if act t then (L.symm (WithLp.toLp 2 fun b' ↦ Ψ.ofLp (t, b'))).ofLp b else Ψ.ofLp (t, b)
  map_add' Ψ₁ Ψ₂ := by
    ext ⟨t, b⟩
    have h : (WithLp.toLp 2 fun b' ↦ (Ψ₁ + Ψ₂).ofLp (t, b')) =
        (WithLp.toLp 2 fun b' ↦ Ψ₁.ofLp (t, b')) +
        (WithLp.toLp 2 fun b' ↦ Ψ₂.ofLp (t, b')) := by ext b'; rfl
    change (if act t then (L (WithLp.toLp 2 fun b' ↦ (Ψ₁ + Ψ₂).ofLp (t, b'))).ofLp b
        else (Ψ₁ + Ψ₂).ofLp (t, b)) =
      (if act t then (L (WithLp.toLp 2 fun b' ↦ Ψ₁.ofLp (t, b'))).ofLp b else Ψ₁.ofLp (t, b)) +
      (if act t then (L (WithLp.toLp 2 fun b' ↦ Ψ₂.ofLp (t, b'))).ofLp b else Ψ₂.ofLp (t, b))
    cases act t
    · rfl
    · simp only [↓reduceIte]; rw [h, map_add, PiLp.add_apply]
  map_smul' c Ψ := by
    ext ⟨t, b⟩
    have h : (WithLp.toLp 2 fun b' ↦ (c • Ψ).ofLp (t, b')) =
        c • (WithLp.toLp 2 fun b' ↦ Ψ.ofLp (t, b')) := by ext b'; rfl
    change (if act t then (L (WithLp.toLp 2 fun b' ↦ (c • Ψ).ofLp (t, b'))).ofLp b
        else (c • Ψ).ofLp (t, b)) =
      c * (if act t then (L (WithLp.toLp 2 fun b' ↦ Ψ.ofLp (t, b'))).ofLp b else Ψ.ofLp (t, b))
    cases act t
    · rfl
    · simp only [↓reduceIte]; rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]
  left_inv Ψ := by
    ext ⟨t, b⟩
    change (if act t then (L.symm (WithLp.toLp 2 fun b' ↦
        if act t then (L (WithLp.toLp 2 fun b'' ↦ Ψ.ofLp (t, b''))).ofLp b'
        else Ψ.ofLp (t, b'))).ofLp b else if act t then _ else Ψ.ofLp (t, b)) = Ψ.ofLp (t, b)
    cases act t
    · rfl
    · simp only [↓reduceIte]; exact congrArg (fun φ ↦ φ.ofLp b) (L.symm_apply_apply _)
  right_inv Ψ := by
    ext ⟨t, b⟩
    change (if act t then (L (WithLp.toLp 2 fun b' ↦
        if act t then (L.symm (WithLp.toLp 2 fun b'' ↦ Ψ.ofLp (t, b''))).ofLp b'
        else Ψ.ofLp (t, b'))).ofLp b else if act t then _ else Ψ.ofLp (t, b)) = Ψ.ofLp (t, b)
    cases act t
    · rfl
    · simp only [↓reduceIte]; exact congrArg (fun φ ↦ φ.ofLp b) (L.apply_symm_apply _)
  norm_map' Ψ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change ∑ p : Fin T × B, ‖(if act p.1 then
        (L (WithLp.toLp 2 fun b' ↦ Ψ.ofLp (p.1, b'))).ofLp p.2 else Ψ.ofLp p)‖ ^ 2 =
      ∑ p : Fin T × B, ‖Ψ.ofLp p‖ ^ 2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun t _ ↦ ?_
    cases h : act t
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      have hn := congrArg (· ^ 2) (L.norm_map (WithLp.toLp 2 fun b' ↦ Ψ.ofLp (t, b')))
      rwa [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hn

private def reflEmb {N T : ℕ} {D : Type*} (i₀ : Fin N) (act : Fin T → Bool) :
    (Fin T × Option (Fin N × Bool × D)) ↪ Fin N × Bool × (Fin T × (Unit ⊕ (Bool × D))) where
  toFun
    | (t, none) => (i₀, false, (t, Sum.inl ()))
    | (t, some (i, b, d)) => (i, act t, (t, Sum.inr (b, d)))
  inj' q₁ q₂ h := by
    rcases q₁ with ⟨t₁, _ | ⟨i₁, b₁, d₁⟩⟩ <;> rcases q₂ with ⟨t₂, _ | ⟨i₂, b₂, d₂⟩⟩
    · simp only [Prod.mk.injEq, true_and, and_true] at h; exact Prod.ext h rfl
    · simp at h
    · simp at h
    · simp only [Prod.mk.injEq, Sum.inr.injEq] at h; obtain ⟨rfl, -, rfl, rfl, rfl⟩ := h; rfl

private noncomputable def diagIso {ι : Type*} [Fintype ι] (sgn : ι → Bool) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun ψ := WithLp.toLp 2 fun p ↦ (if sgn p then -1 else 1) * ψ.ofLp p
  invFun ψ := WithLp.toLp 2 fun p ↦ (if sgn p then -1 else 1) * ψ.ofLp p
  map_add' ψ φ := by ext p; simp [mul_add]
  map_smul' c ψ := by ext p; simp [mul_left_comm]
  left_inv ψ := by
    ext p; change (if sgn p then -1 else 1) * ((if sgn p then -1 else 1) * ψ.ofLp p) = ψ.ofLp p
    split_ifs <;> ring
  right_inv ψ := by
    ext p; change (if sgn p then -1 else 1) * ((if sgn p then -1 else 1) * ψ.ofLp p) = ψ.ofLp p
    split_ifs <;> ring
  norm_map' ψ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 <| by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine sum_congr rfl fun p _ ↦ ?_
    change ‖(if sgn p then (-1 : ℂ) else 1) * ψ.ofLp p‖ ^ 2 = ‖ψ.ofLp p‖ ^ 2
    rw [norm_mul]; split_ifs <;> simp

/-- **Alternating-reflection quantum query algorithm from a dual adversary**
: given a dual adversary `w` for a
non-constant total Boolean function `f : BooleanFunction N` and an error bound `0 < ε < 1/2`,
`f` is quantum-computable within error `ε` using `T - 1` queries, where
`T = ⌈√((1 + ((1 - ε) / ε) · w.weight²) / ε)⌉₊`.
-/
theorem isQuantumComputable_of_dualAdversary {N : ℕ} {f : BooleanFunction N} {D : Type*}
    [Fintype D] (w : DualAdversary (fun _ ↦ True) f D) {x₁ x₀ : BitString N}
    (hfx₁ : f x₁ = true) (hfx₀ : f x₀ = false) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    IsQuantumComputable ε f
      (⌈√((1 + (1 - ε) / ε * w.weight ^ 2) / ε)⌉₊ - 1) := by
  classical
  have hne_in : x₁ ≠ x₀ := fun h ↦ by simp [h, hfx₀] at hfx₁
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hne_in
  set W := w.weight
  have hW1 : 1 ≤ W := w.one_le_weight (x := x₁) (y := x₀) trivial trivial
    (by rw [hfx₁, hfx₀]; decide)
  have : 0 < W := zero_lt_one.trans_le hW1
  have h1ε : 0 < 1 - ε := by linarith
  let α : ℝ := √(ε / ((1 - ε) * W))
  have hα_pos : 0 < α := Real.sqrt_pos.2 (by positivity)
  have hα_sq : α ^ 2 = ε / ((1 - ε) * W) := Real.sq_sqrt (by positivity)
  set R_val : ℝ := (1 + (1 - ε) / ε * W ^ 2) / ε
  have hR_gt : 4 < R_val := by
    have hrat : 1 < (1 - ε) / ε := (one_lt_div hε0).2 (by linarith)
    have hnum : 2 < 1 + (1 - ε) / ε * W ^ 2 := by nlinarith [sq_nonneg (W - 1)]
    have hinv : 2 < 1 / ε := (lt_div_iff₀ hε0).2 (by linarith)
    dsimp only [R_val]
    rw [div_eq_mul_one_div]
    nlinarith
  set T : ℕ := ⌈√R_val⌉₊
  have hT_ge2 : 2 ≤ T := by
    have h2 : (2 : ℝ) < √R_val :=
      (Real.lt_sqrt (by norm_num)).2 (by linarith)
    exact_mod_cast (h2.trans_le (Nat.le_ceil _)).le
  have hTpos : 0 < T := by omega
  set Q : ℕ := T - 1
  have : 0 < Q := by omega
  have hTQ : Q + 1 = T := by omega
  have hT_sq : R_val ≤ (T : ℝ) ^ 2 := by
    have hc : √R_val ≤ (T : ℝ) := Nat.le_ceil _
    calc R_val = (√R_val) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ (T : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
  -- Step 1: Set up the reflection space `H = EuclideanSpace ℂ B` and witness vectors.
  let B := Option (Fin N × Bool × D)
  let ψ₀ : EuclideanSpace ℂ B := ket none
  have hψ₀_norm : ‖ψ₀‖ = 1 := norm_ket none
  let φNeg (y : BitString N) : EuclideanSpace ℂ B := WithLp.toLp 2 fun
    | none => 1
    | some (i, b, d) => if b = y i then ((α * w.vec y i d : ℝ) : ℂ) else 0
  let μPos (x : BitString N) : EuclideanSpace ℂ B := WithLp.toLp 2 fun
    | none => 0
    | some (i, b, d) => if b = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ) else 0
  let wPos (x : BitString N) : EuclideanSpace ℂ B := ψ₀ - μPos x
  have hφ_norm (y : BitString N) : ‖φNeg y‖ ^ 2 ≤ (1 - ε)⁻¹ := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    simp only [φNeg, norm_one, one_pow, Fintype.sum_prod_type, Fintype.sum_bool]
    have hsum : ∑ i : Fin N, (∑ d : D, ‖(if true = y i then ((α * w.vec y i d : ℝ) : ℂ)
          else 0)‖ ^ 2 + ∑ d : D, ‖(if false = y i then ((α * w.vec y i d : ℝ) : ℂ)
          else 0)‖ ^ 2) = α ^ 2 * ∑ i : Fin N, ∑ d : D, w.vec y i d ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by cases y i <;> simp [mul_pow, ← mul_sum]
    rw [hsum]
    calc 1 + α ^ 2 * ∑ i : Fin N, ∑ d : D, w.vec y i d ^ 2
        ≤ 1 + α ^ 2 * W := add_le_add_right
          (mul_le_mul_of_nonneg_left (w.sum_sq_le y trivial) (sq_nonneg α)) 1
      _ = (1 - ε)⁻¹ := by rw [hα_sq]; field_simp; ring
  have hw_norm (x : BitString N) : ‖wPos x‖ ^ 2 ≤ 1 + (1 - ε) / ε * W ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    have hnone : (wPos x).ofLp none = 1 := by simp [wPos, ψ₀, μPos]
    have hsome (i : Fin N) (b : Bool) (d : D) :
        (wPos x).ofLp (some (i, b, d)) = -(μPos x).ofLp (some (i, b, d)) := by simp [wPos, ψ₀]
    simp only [hnone, norm_one, one_pow, Fintype.sum_prod_type, hsome, norm_neg, Fintype.sum_bool,
      μPos]
    have hsum : ∑ i : Fin N, (∑ d : D, ‖(if true = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ)
          else 0)‖ ^ 2 + ∑ d : D, ‖(if false = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ)
          else 0)‖ ^ 2) = (α ^ 2)⁻¹ * ∑ i : Fin N, ∑ d : D, w.vec x i d ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by cases x i <;> simp [mul_pow, ← mul_sum, inv_pow]
    rw [hsum]
    calc 1 + (α ^ 2)⁻¹ * ∑ i : Fin N, ∑ d : D, w.vec x i d ^ 2
        ≤ 1 + (α ^ 2)⁻¹ * W := add_le_add_right
          (mul_le_mul_of_nonneg_left (w.sum_sq_le x trivial) (by positivity)) 1
      _ = 1 + (1 - ε) / ε * W ^ 2 := by rw [hα_sq, inv_div]; ring
  have horth {x y : BitString N} (hfx : f x = true) (hfy : f y = false) :
      inner ℂ (φNeg y) (wPos x) = 0 := by
    rw [PiLp.inner_apply, Fintype.sum_option]
    have h0 : inner ℂ ((φNeg y).ofLp none) ((wPos x).ofLp none) = 1 := by
      simp [φNeg, wPos, ψ₀, μPos]
    have hrest : ∑ p : Fin N × Bool × D,
        inner ℂ ((φNeg y).ofLp (some p)) ((wPos x).ofLp (some p)) = -1 := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, wPos, PiLp.sub_apply, ψ₀, ket_apply,
        reduceCtorEq, ↓reduceIte, zero_sub, inner_neg_right, φNeg, μPos]
      have hterm (i : Fin N) :
          (∑ d : D, -inner ℂ (if true = y i then ((α * w.vec y i d : ℝ) : ℂ) else 0)
              (if true = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ) else 0)) +
          (∑ d : D, -inner ℂ (if false = y i then ((α * w.vec y i d : ℝ) : ℂ) else 0)
              (if false = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ) else 0)) =
          if x i ≠ y i then -(((∑ d : D, w.vec x i d * w.vec y i d : ℝ)) : ℂ) else 0 := by
        have hαne : α ≠ 0 := hα_pos.ne'
        have hcancel (a b : ℝ) : α⁻¹ * a * (α * b) = a * b := by field_simp
        cases x i <;> cases y i <;> simp [← Complex.ofReal_mul, hcancel, sum_neg_distrib]
      have hrewrite : ∀ i : Fin N,
          (-∑ d : D, inner ℂ (if true = y i then ((α * w.vec y i d : ℝ) : ℂ) else 0)
              (if true = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ) else 0)) +
          (-∑ d : D, inner ℂ (if false = y i then ((α * w.vec y i d : ℝ) : ℂ) else 0)
              (if false = !x i then ((α⁻¹ * w.vec x i d : ℝ) : ℂ) else 0)) =
          if x i ≠ y i then -(((∑ d : D, w.vec x i d * w.vec y i d : ℝ)) : ℂ) else 0 := fun i ↦ by
        simpa only [sum_neg_distrib] using hterm i
      simp only [sum_neg_distrib, hrewrite, ← sum_filter, ← Complex.ofReal_sum,
        w.sum_inner_eq_one x y trivial trivial hfx hfy, Complex.ofReal_one]
    rw [h0, hrest, add_neg_cancel]
  -- Step 2: Define the input-independent reflection `K.reflection` and 1-query reflection `Rx x`.
  let K : Submodule ℂ (EuclideanSpace ℂ B) :=
    Submodule.span ℂ {φ | ∃ y : BitString N, f y = false ∧ φ = φNeg y}
  let Rx (x : BitString N) : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B :=
    diagIso fun
      | none => false
      | some (i, b, _) => decide (b ≠ x i)
  let Vx (x : BitString N) : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B :=
    K.reflection.trans (Rx x)
  have hVx_neg {y : BitString N} (hfy : f y = false) : Vx y (φNeg y) = φNeg y := by
    have hmem : φNeg y ∈ K := Submodule.subset_span ⟨y, hfy, rfl⟩
    have hrefl : K.reflection (φNeg y) = φNeg y := by
      rw [Submodule.reflection_apply, Submodule.starProjection_eq_self_iff.2 hmem, two_smul,
        add_sub_cancel_right]
    simp only [Vx, LinearIsometryEquiv.trans_apply, hrefl]
    ext p
    rcases p with _ | ⟨i, b, d⟩
    · change (if false then -1 else 1) * (φNeg y).ofLp none = (φNeg y).ofLp none; simp
    · change (if decide (b ≠ y i) then -1 else 1) * (φNeg y).ofLp (some (i, b, d)) =
        (φNeg y).ofLp (some (i, b, d))
      by_cases hb : b = y i <;> simp [φNeg, hb]
  have hVx_pos {x : BitString N} (hfx : f x = true) :
      Vx x (wPos x) = wPos x - (2 : ℂ) • ψ₀ := by
    have hmem_orth' : wPos x ∈ Kᗮ :=
      (Submodule.mem_orthogonal K (wPos x)).2 fun u hu ↦
        Submodule.span_induction (fun _ ⟨y, hfy, hφ⟩ ↦ hφ ▸ horth hfx hfy) (by simp)
          (fun _ _ _ _ h1 h2 ↦ by rw [inner_add_left, h1, h2, add_zero])
          (fun c _ _ h1 ↦ by rw [inner_smul_left, h1, mul_zero]) hu
    have hrefl : K.reflection (wPos x) = -wPos x := by
      rw [Submodule.reflection_apply, K.starProjection_apply_eq_zero_iff.2 hmem_orth',
        smul_zero, zero_sub]
    simp only [Vx, LinearIsometryEquiv.trans_apply, hrefl]
    ext p
    rcases p with _ | ⟨i, b, d⟩
    · change (if false then -1 else 1) * (-wPos x).ofLp none = (wPos x - (2 : ℂ) • ψ₀).ofLp none
      simp [wPos, ψ₀, μPos]; ring
    · change (if decide (b ≠ x i) then -1 else 1) * (-wPos x).ofLp (some (i, b, d)) =
        (wPos x - (2 : ℂ) • ψ₀).ofLp (some (i, b, d))
      cases b <;> cases hx : x i <;> simp [wPos, ψ₀, μPos, hx]
  -- Step 3: Bound the Cesàro average `cesaro x = T⁻¹ • ∑_{t < T} Vx x^[t] ψ₀` on both cases.
  let cesaro (x : BitString N) : EuclideanSpace ℂ B :=
    ((T : ℂ)⁻¹) • ∑ t ∈ range T, ((Vx x)^[t]) ψ₀
  have hcesaro_false {y : BitString N} (hfy : f y = false) :
      1 - ε ≤ ‖cesaro y‖ ^ 2 := by
    have hiter (t : ℕ) : inner ℂ (φNeg y) (((Vx y)^[t]) ψ₀) = 1 := by
      induction t with
      | zero => simp [φNeg, ψ₀, ket, EuclideanSpace.inner_single_right]
      | succ t ih =>
        rw [Function.iterate_succ_apply', ← hVx_neg hfy, (Vx y).inner_map_map, ih]
    have hinner : inner ℂ (φNeg y) (cesaro y) = 1 := by
      simp only [cesaro, inner_smul_right, inner_sum, hiter, sum_const, card_range, nsmul_eq_mul,
        mul_one]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hTpos.ne')
    have hcs : (1 : ℝ) ≤ ‖φNeg y‖ * ‖cesaro y‖ := by
      simpa [hinner] using norm_inner_le_norm (𝕜 := ℂ) (φNeg y) (cesaro y)
    have hsq : (1 : ℝ) ≤ ‖φNeg y‖ ^ 2 * ‖cesaro y‖ ^ 2 := by
      simpa [mul_pow] using pow_le_pow_left₀ zero_le_one hcs 2
    have hle : (1 : ℝ) ≤ (1 - ε)⁻¹ * ‖cesaro y‖ ^ 2 :=
      hsq.trans (mul_le_mul_of_nonneg_right (hφ_norm y) (sq_nonneg _))
    rwa [inv_mul_eq_div, one_le_div h1ε] at hle
  have hcesaro_true {x : BitString N} (hfx : f x = true) :
      ‖cesaro x‖ ^ 2 ≤ ε := by
    have hstep (t : ℕ) :
        (2 : ℂ) • ((Vx x)^[t]) ψ₀ = ((Vx x)^[t]) (wPos x) - ((Vx x)^[t + 1]) (wPos x) := by
      have hlin (t : ℕ) (u v : EuclideanSpace ℂ B) :
          ((Vx x)^[t]) (u - v) = ((Vx x)^[t]) u - ((Vx x)^[t]) v := by
        induction t with | zero => rfl | succ t ih => simp only [Function.iterate_succ_apply', ih,
          map_sub]
      have hsm (t : ℕ) (c : ℂ) (u : EuclideanSpace ℂ B) :
          ((Vx x)^[t]) (c • u) = c • ((Vx x)^[t]) u := by
        induction t with | zero => rfl | succ t ih => simp only [Function.iterate_succ_apply', ih,
          map_smul]
      rw [Function.iterate_succ_apply, hVx_pos hfx, hlin t (wPos x), hsm]
      abel
    have htel : (2 : ℂ) • ∑ t ∈ range T, ((Vx x)^[t]) ψ₀ = wPos x - ((Vx x)^[T]) (wPos x) := by
      rw [smul_sum]; simp only [hstep]; exact sum_range_sub' (fun t ↦ ((Vx x)^[t]) (wPos x)) T
    have hnorm_iter (t : ℕ) (u : EuclideanSpace ℂ B) : ‖((Vx x)^[t]) u‖ = ‖u‖ := by
      induction t with | zero => rfl | succ t ih => rw [Function.iterate_succ_apply',
        (Vx x).norm_map, ih]
    have hsum_norm : ‖∑ t ∈ range T, ((Vx x)^[t]) ψ₀‖ ≤ ‖wPos x‖ := by
      have h := congrArg (‖·‖) htel; rw [norm_smul, RCLike.norm_ofNat] at h
      linarith [(norm_sub_le (wPos x) (((Vx x)^[T]) (wPos x))).trans_eq (by rw [hnorm_iter])]
    have hces_le : ‖cesaro x‖ ≤ ‖wPos x‖ / T := by
      simp only [cesaro, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hsum_norm (by positivity)
    calc ‖cesaro x‖ ^ 2 ≤ (‖wPos x‖ / T) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hces_le 2
      _ = ‖wPos x‖ ^ 2 / (T : ℝ) ^ 2 := div_pow _ _ _
      _ ≤ (1 + (1 - ε) / ε * W ^ 2) / R_val :=
          div_le_div₀ (by positivity) (hw_norm x) (by positivity) hT_sq
      _ = ε := by dsimp [R_val]; field_simp
  -- Step 4: Implement `cesaro x` in `Q = T - 1` phase queries on `State N W_alg`.
  let act (s : ℕ) : Fin T → Bool := fun t ↦ decide (s < t.1)
  let idle : Fin T → Bool := fun _ ↦ false
  let zFix (a : Fin T → Bool) :
      EuclideanSpace ℂ (Fin T × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T × B) :=
    diagIso fun
      | (_, none) => false
      | (t, some (_, b, _)) => a t && b
  let oAct (x : BitString N) (a : Fin T → Bool) :
      EuclideanSpace ℂ (Fin T × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin T × B) :=
    diagIso fun
      | (_, none) => false
      | (t, some (i, _, _)) => a t && x i
  have horacle (x : BitString N) (a : Fin T → Bool)
      (Ψ : EuclideanSpace ℂ (Fin T × B)) :
      phaseOracle x (embedBasis (reflEmb (D := D) i₀ a) Ψ) =
        embedBasis (reflEmb i₀ a) (oAct x a Ψ) := by
    ext p
    by_cases hp : ∃ q, reflEmb (D := D) i₀ a q = p
    · obtain ⟨⟨t, _ | ⟨i, b, d⟩⟩, rfl⟩ := hp
      · rw [phaseOracle_apply, embedBasis_apply_image, embedBasis_apply_image]
        change (if false && x i₀ then -1 else 1) * Ψ.ofLp (t, none) =
          (if false then -1 else 1) * Ψ.ofLp (t, none)
        simp
      · rw [phaseOracle_apply, embedBasis_apply_image, embedBasis_apply_image]
        rfl
    · rw [phaseOracle_apply, embedBasis_apply_of_not_mem _ _ (not_exists.1 hp),
        embedBasis_apply_of_not_mem _ _ (not_exists.1 hp), mul_zero]
  have hzFix_oAct (x : BitString N) (a : Fin T → Bool)
      (Ψ : EuclideanSpace ℂ (Fin T × B)) :
      zFix a (oAct x a Ψ) = condFiber a (Rx x) Ψ := by
    ext ⟨t, p⟩
    rcases p with _ | ⟨i, b, d⟩
    · by_cases ha : a t = true <;>
        change (if false then -1 else 1) * ((if false then -1 else 1) * Ψ.ofLp (t, none)) =
          if a t then (if false then -1 else 1) * Ψ.ofLp (t, none) else Ψ.ofLp (t, none) <;>
        simp [ha]
    · change (if a t && b then -1 else 1) *
          ((if a t && x i then -1 else 1) * Ψ.ofLp (t, some (i, b, d))) =
        if a t then (if decide (b ≠ x i) then -1 else 1) * Ψ.ofLp (t, some (i, b, d))
        else Ψ.ofLp (t, some (i, b, d))
      rw [← mul_assoc]
      cases a t <;> cases b <;> cases x i <;> simp
  let stage (x : BitString N) (s : ℕ) : EuclideanSpace ℂ (Fin T × B) :=
    WithLp.toLp 2 fun (t, b) ↦ (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (((Vx x)^[min s t.1]) ψ₀).ofLp b
  have hstage_step (x : BitString N) (s : ℕ) :
      condFiber (act s) (Rx x) (condFiber (act s) K.reflection (stage x s)) =
        stage x (s + 1) := by
    ext ⟨t, b⟩
    by_cases hlt : s < t.1
    · have ha : act s t = true := decide_eq_true hlt
      have hmin1 : min s t.1 = s := Nat.min_eq_left hlt.le
      have hmin2 : min (s + 1) t.1 = s + 1 := Nat.min_eq_left (by omega)
      have hslice : (WithLp.toLp 2 fun b' ↦
          (condFiber (act s) K.reflection (stage x s)).ofLp (t, b')) =
          (((√(T : ℝ))⁻¹ : ℝ) : ℂ) • K.reflection (((Vx x)^[s]) ψ₀) := by
        ext b'
        change (if act s t then (K.reflection (WithLp.toLp 2 fun b'' ↦
            (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (((Vx x)^[min s t.1]) ψ₀).ofLp b'')).ofLp b'
          else _) = _
        have hsm : (WithLp.toLp 2 fun b'' ↦
            (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (((Vx x)^[s]) ψ₀).ofLp b'') =
            (((√(T : ℝ))⁻¹ : ℝ) : ℂ) • (((Vx x)^[s]) ψ₀) := rfl
        simp only [ha, ↓reduceIte, hmin1, hsm, map_smul, PiLp.smul_apply]
      change (if act s t then (Rx x _).ofLp b else _) =
        (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (((Vx x)^[min (s + 1) t.1]) ψ₀).ofLp b
      simp only [ha, ↓reduceIte]
      rw [hslice, map_smul, PiLp.smul_apply, smul_eq_mul, hmin2, Function.iterate_succ_apply']
      rfl
    · have ha : act s t = false := decide_eq_false hlt
      have hmin1 : min s t.1 = t.1 := Nat.min_eq_right (by omega)
      have hmin2 : min (s + 1) t.1 = t.1 := Nat.min_eq_right (by omega)
      change (if act s t then _ else if act s t then _ else (stage x s).ofLp (t, b)) =
        (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (((Vx x)^[min (s + 1) t.1]) ψ₀).ofLp b
      simp [ha, stage, hmin1, hmin2]
  obtain ⟨clkU, hclkU⟩ := exists_clockUnitary hTpos
  let W_alg := Fin T × (Unit ⊕ (Bool × D))
  let U : ℕ → State N W_alg →ₗᵢ[ℂ] State N W_alg := fun s ↦
    if s = 0 then
      transportBasis (reflEmb i₀ idle) (reflEmb i₀ (act 0)) (condFiber (act 0) K.reflection)
    else if s < Q then
      transportBasis (reflEmb i₀ (act (s - 1))) (reflEmb i₀ (act s))
        ((zFix (act (s - 1))).trans (condFiber (act s) K.reflection))
    else if s = Q then
      transportBasis (reflEmb i₀ (act (Q - 1))) (reflEmb i₀ idle)
        ((zFix (act (Q - 1))).trans (liftClock clkU))
    else LinearIsometry.id
  let initAlg : State N W_alg := embedBasis (reflEmb i₀ idle) (stage x₀ 0)
  have hstage0_indep (x : BitString N) : stage x 0 = stage x₀ 0 := by
    ext ⟨t, b⟩; simp [stage]
  have hinit_norm : ‖initAlg‖ = 1 := by
    rw [LinearIsometry.norm_map]
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 ?_
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have hrow (t : Fin T) : ∑ b : B, ‖(stage x₀ 0).ofLp (t, b)‖ ^ 2 = (T : ℝ)⁻¹ := by
      simp only [stage, Nat.zero_min, Function.iterate_zero_apply, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg T),
        ← mul_sum, ← EuclideanSpace.norm_sq_eq, hψ₀_norm, one_pow, mul_one]
    simp [hrow, (Nat.cast_pos.2 hTpos : (0 : ℝ) < T).ne']
  have hrun_lt (x : BitString N) : ∀ s < Q,
      run U initAlg x s =
        embedBasis (reflEmb i₀ (act s)) (condFiber (act s) K.reflection (stage x s)) := by
    intro s hs
    induction s with
    | zero =>
      simp only [run, U, ↓reduceIte, initAlg, ← hstage0_indep x, transportBasis_embedBasis]
    | succ s ih =>
      simp only [run, ih (by omega), horacle, U, Nat.succ_ne_zero, hs, ↓reduceIte,
        Nat.add_sub_cancel, transportBasis_embedBasis, LinearIsometryEquiv.trans_apply,
        hzFix_oAct, hstage_step]
  have hrun_Q (x : BitString N) :
      run U initAlg x Q =
        embedBasis (reflEmb i₀ idle) (liftClock clkU (stage x Q)) := by
    cases hQ_eq : Q with
    | zero => omega
    | succ r =>
      have hr : r < r + 1 := Nat.lt_succ_self r
      have hprev := hrun_lt x r (hQ_eq ▸ hr)
      rw [run, hprev, horacle]
      have hU : U (r + 1) = transportBasis (reflEmb i₀ (act r)) (reflEmb i₀ idle)
          ((zFix (act r)).trans (liftClock clkU)) := by
        simp [U, hQ_eq]
      rw [hU, transportBasis_embedBasis, LinearIsometryEquiv.trans_apply, hzFix_oAct, hstage_step]
  -- Step 5: Compute the acceptance probability on `S_acc = {p | p.2.2.1 ≠ 0}`.
  let S_zero : Finset (Fin N × Bool × W_alg) := univ.filter fun p ↦ p.2.2.1 = ⟨0, hTpos⟩
  have hprob_zero (x : BitString N) :
      measureProb (run U initAlg x Q) S_zero = ‖cesaro x‖ ^ 2 := by
    rw [hrun_Q, measureProb_embedBasis]
    trans measureProb (liftClock clkU (stage x Q))
      (univ.map ⟨fun b : B ↦ (⟨0, hTpos⟩, b), fun _ _ h ↦ (Prod.mk.inj h).2⟩)
    · congr 1; ext ⟨t, p⟩
      simp only [mem_filter, mem_univ, true_and, S_zero, mem_map]
      refine ⟨fun ht ↦ ⟨p, Prod.ext ?_ rfl⟩, fun ⟨b, hb⟩ ↦ ?_⟩
      · rcases p with _ | ⟨i, b, d⟩ <;> exact ht.symm
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb; rcases b with _ | ⟨i, b', d⟩ <;> rfl
    rw [measureProb, sum_map, EuclideanSpace.norm_sq_eq]
    refine sum_congr rfl fun b _ ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) ?_
    change (clkU (WithLp.toLp 2 fun t ↦ (stage x Q).ofLp (t, b))).ofLp ⟨0, hTpos⟩ =
      (cesaro x).ofLp b
    rw [hclkU]
    have hsq_inv : (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (((√(T : ℝ))⁻¹ : ℝ) : ℂ) = (T : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg T),
        Complex.ofReal_inv, Complex.ofReal_natCast]
    have hlhs : ∑ t : Fin T, (((√(T : ℝ))⁻¹ : ℝ) : ℂ) * (stage x Q).ofLp (t, b) =
        (T : ℂ)⁻¹ * ∑ t : Fin T, (((Vx x)^[t.1]) ψ₀).ofLp b := by
      rw [mul_sum]
      refine sum_congr rfl fun t _ ↦ ?_
      have hmin : min Q t.1 = t.1 := Nat.min_eq_right (by omega)
      simp only [stage, hmin, ← mul_assoc, hsq_inv]
    rw [hlhs, Fin.sum_univ_eq_sum_range (fun t ↦ (((Vx x)^[t]) ψ₀).ofLp b) T]
    simp [cesaro, Finset.sum_apply]
  refine ComputesWithin.isQuantumComputable (U := U) (ψ₀ := initAlg) (S := S_zeroᶜ)
    ⟨hinit_norm, fun x ↦ ?_⟩
  rw [measureProb_compl, norm_run, hinit_norm, one_pow, hprob_zero]
  have hnn : 0 ≤ ‖cesaro x‖ ^ 2 := sq_nonneg _
  have hle1 : ‖cesaro x‖ ^ 2 ≤ 1 := by
    rw [← hprob_zero]
    exact (measureProb_le_measureProb_univ _ _).trans_eq (by rw [measureProb_univ, norm_run,
      hinit_norm, one_pow])
  cases hfx : f x
  · simp only [bitVal_false, sub_zero]; exact abs_le.2 ⟨by linarith,
    by linarith [hcesaro_false hfx]⟩
  · simp only [bitVal_true]; exact abs_le.2 ⟨by linarith [hcesaro_true hfx], by linarith⟩

/-- **Reichardt's reflection upper bound for general bounded error `ε ∈ (0, 1/2)`**:
`Q_ε(f) ≤ (√2 / ε) · ADV±(f)`. -/
theorem queryComplexity_le_mul_generalAdversary {N : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (f : BooleanFunction N) :
    (queryComplexity ε f : ℝ) ≤ √2 / ε * generalAdversary (fun _ ↦ True) f := by
  by_cases hpair : ∃ x₁ x₀ : BitString N, f x₁ = true ∧ f x₀ = false
  · obtain ⟨x₁, x₀, hfx₁, hfx₀⟩ := hpair
    obtain ⟨k, w, hw⟩ := exists_dualAdversary_eq_generalAdversary (fun _ ↦ True) f
    have hcomp := isQuantumComputable_of_dualAdversary w hfx₁ hfx₀ hε0 hε
    have hq_le : queryComplexity ε f ≤ ⌈√((1 + (1 - ε) / ε * w.weight ^ 2) / ε)⌉₊ - 1 :=
      hcomp.queryComplexity_le
    set r := √((1 + (1 - ε) / ε * w.weight ^ 2) / ε)
    have hW1 : 1 ≤ w.weight :=
      w.one_le_weight (x := x₁) (y := x₀) trivial trivial (by rw [hfx₁, hfx₀]; decide)
    have h1ε : 0 < 1 - ε := by linarith
    have hr_pos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have h1_le : 1 ≤ (1 - ε) / ε * w.weight ^ 2 := by
      have hrat : 1 ≤ (1 - ε) / ε := (one_le_div hε0).2 (by linarith)
      nlinarith [sq_nonneg (w.weight - 1)]
    have hr_le : r ≤ √2 / ε * w.weight :=
      Real.sqrt_le_iff.2 ⟨by positivity, by
        rw [mul_pow, div_pow, Real.sq_sqrt zero_le_two]
        have hmul : (1 - ε) / ε * w.weight ^ 2 ≤ 1 / ε * w.weight ^ 2 :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hε0.le)
            (sq_nonneg _)
        have hnum : 1 + (1 - ε) / ε * w.weight ^ 2 ≤ 2 / ε * w.weight ^ 2 :=
          calc 1 + (1 - ε) / ε * w.weight ^ 2
              ≤ 1 / ε * w.weight ^ 2 + 1 / ε * w.weight ^ 2 := add_le_add (h1_le.trans hmul) hmul
            _ = 2 / ε * w.weight ^ 2 := by ring
        exact (div_le_div_of_nonneg_right hnum hε0.le).trans_eq (by ring)⟩
    have hceil_pos : 1 ≤ ⌈r⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hr_pos).ne'
    calc (queryComplexity ε f : ℝ) ≤ ((⌈r⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hq_le
      _ ≤ r := by rw [Nat.cast_sub hceil_pos,
        Nat.cast_one]; linarith [Nat.ceil_lt_add_one hr_pos.le]
      _ ≤ √2 / ε * generalAdversary (fun _ ↦ True) f := hw ▸ hr_le
  · have hconst : ∃ b, ∀ x, f x = b :=
      if hex : ∃ x, f x = true then
        ⟨true, fun x ↦ Classical.byContradiction fun h ↦
          hpair ⟨hex.choose, x, hex.choose_spec, Bool.eq_false_iff.2 h⟩⟩
      else ⟨false, fun x ↦ Bool.eq_false_iff.2 fun h ↦ hex ⟨x, h⟩⟩
    obtain ⟨b, hb⟩ := hconst
    rw [queryComplexity_eq_zero_of_forall_eq ε b hb, Nat.cast_zero]
    exact mul_nonneg (by positivity) (generalAdversary_nonneg _ _)

/-- **Reichardt's reflection upper bound for `Q_2(f)`**:
`Q_2(f) ≤ 3 · ADV±(f)` for every total Boolean function `f : BooleanFunction N`.
-/
theorem boundedQueryComplexity_le_three_mul_generalAdversary {N : ℕ} (f : BooleanFunction N) :
    (boundedQueryComplexity f : ℝ) ≤ 3 * generalAdversary (fun _ ↦ True) f := by
  by_cases hpair : ∃ x₁ x₀ : BitString N, f x₁ = true ∧ f x₀ = false
  · obtain ⟨x₁, x₀, hfx₁, hfx₀⟩ := hpair
    obtain ⟨k, w, hw⟩ := exists_dualAdversary_eq_generalAdversary (fun _ ↦ True) f
    have hcomp := isQuantumComputable_of_dualAdversary w hfx₁ hfx₀
      (ε := 1 / 3) (by norm_num) (by norm_num)
    have hq_le : boundedQueryComplexity f ≤
        ⌈√((1 + (1 - (1 / 3 : ℝ)) / (1 / 3) * w.weight ^ 2) / (1 / 3))⌉₊ - 1 :=
      hcomp.queryComplexity_le
    set r := √((1 + (1 - (1 / 3 : ℝ)) / (1 / 3) * w.weight ^ 2) / (1 / 3))
    have hW1 : 1 ≤ w.weight :=
      w.one_le_weight (x := x₁) (y := x₀) trivial trivial (by rw [hfx₁, hfx₀]; decide)
    have hr_pos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr_le : r ≤ 3 * w.weight :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_nonneg (w.weight - 1)]⟩
    have hceil_pos : 1 ≤ ⌈r⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hr_pos).ne'
    calc (boundedQueryComplexity f : ℝ) ≤ ((⌈r⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hq_le
      _ ≤ r := by rw [Nat.cast_sub hceil_pos,
        Nat.cast_one]; linarith [Nat.ceil_lt_add_one hr_pos.le]
      _ ≤ 3 * generalAdversary (fun _ ↦ True) f := hw ▸ hr_le
  · have hconst : ∃ b, ∀ x, f x = b :=
      if hex : ∃ x, f x = true then
        ⟨true, fun x ↦ Classical.byContradiction fun h ↦
          hpair ⟨hex.choose, x, hex.choose_spec, Bool.eq_false_iff.2 h⟩⟩
      else ⟨false, fun x ↦ Bool.eq_false_iff.2 fun h ↦ hex ⟨x, h⟩⟩
    obtain ⟨b, hb⟩ := hconst
    rw [boundedQueryComplexity, queryComplexity_eq_zero_of_forall_eq _ b hb, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (generalAdversary_nonneg _ _)

/-- **Tightness of the general adversary bound `Q_2(f) = Θ(ADV±(f))`**
: `(1 / 36) · ADV±(f) ≤ Q_2(f) ≤ 3 · ADV±(f)`.
-/
theorem boundedQueryComplexity_generalAdversary_bounds {N : ℕ} (f : BooleanFunction N) :
    (1 / 36 : ℝ) * generalAdversary (fun _ ↦ True) f ≤ (boundedQueryComplexity f : ℝ) ∧
      (boundedQueryComplexity f : ℝ) ≤ 3 * generalAdversary (fun _ ↦ True) f :=
  ⟨by linarith [generalAdversary_le_thirty_six_mul_boundedQueryComplexity f],
    boundedQueryComplexity_le_three_mul_generalAdversary f⟩

end ReflectionAlgorithm
end Cslib.Quantum
