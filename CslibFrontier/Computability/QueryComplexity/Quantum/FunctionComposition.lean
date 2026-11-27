/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.AdversaryDuality
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm

/-!
# Exact Adversary Composition and Reichardt's Quantum Query Composition Theorem

For total Boolean functions $f : \{0, 1\}^n \to \{0, 1\}$ and $g : \{0, 1\}^m \to \{0, 1\}$, their
block composition $f \bullet g : \{0, 1\}^{nm} \to \{0, 1\}$ evaluates $f$ on the $n$-bit tuple of
outputs of $g$ applied to $n$ disjoint $m$-bit blocks:
$$(f \bullet g)(x) = f\bigl(g(x_1, \dots, x_m), \dots, g(x_{(n-1)m+1}, \dots, x_{nm})\bigr).$$

This module proves two fundamental composition theorems in quantum query complexity under standard
Lean axioms:

* **Exact composition of the negative-weight adversary bound**
:
  $$\mathrm{ADV}^{\pm}(f \bullet g) = \mathrm{ADV}^{\pm}(f) \cdot \mathrm{ADV}^{\pm}(g).$$
* **Tight composition of bounded-error quantum query complexity**:
  $$Q_2(f \bullet g) = \Theta\bigl(Q_2(f) \cdot Q_2(g)\bigr),$$
  with explicit absolute constants
  $\frac{1}{324}\,Q_2(f)\,Q_2(g) \le Q_2(f \bullet g) \le 3888\,Q_2(f)\,Q_2(g)$.

## Main definitions

* `Cslib.Quantum.blockSlice`: the $i$-th contiguous $m$-bit block of $x \in \{0, 1\}^{nm}$,
  indexed via `finProdFinEquiv (i, j)`.
* `Cslib.Quantum.blockSummary`: the $n$-bit summary vector $i \mapsto g(x^{(i)})$.
* `Cslib.Quantum.composeBool`: the block-composed Boolean function $f \bullet g$.

## Main results

* `Cslib.Quantum.generalAdversary_composeBool_le`:
  $\mathrm{ADV}^{\pm}(f \bullet g) \le \mathrm{ADV}^{\pm}(f)\,\mathrm{ADV}^{\pm}(g)$.
* `Cslib.Quantum.mul_generalAdversary_le_composeBool`:
  $\mathrm{ADV}^{\pm}(f)\,\mathrm{ADV}^{\pm}(g) \le \mathrm{ADV}^{\pm}(f \bullet g)$.
* `Cslib.Quantum.generalAdversary_composeBool`:
  $\mathrm{ADV}^{\pm}(f \bullet g) = \mathrm{ADV}^{\pm}(f)\,\mathrm{ADV}^{\pm}(g)$.
* `Cslib.Quantum.boundedQueryComplexity_mul_le_composeBool`:
  $Q_2(f)\,Q_2(g) \le 324\,Q_2(f \bullet g)$.
* `Cslib.Quantum.boundedQueryComplexity_composeBool_le_mul`:
  $Q_2(f \bullet g) \le 3888\,Q_2(f)\,Q_2(g)$.
* `Cslib.Quantum.boundedQueryComplexity_composeBool_bounds`:
  $\frac{1}{324}\,Q_2(f)\,Q_2(g) \le Q_2(f \bullet g) \le 3888\,Q_2(f)\,Q_2(g)$.

## Tags

quantum query complexity, Boolean function composition, adversary bound, Reichardt theorem
-/

public section

namespace Cslib.Quantum

open Finset Matrix Cslib
open scoped RealInnerProductSpace

/-! ### Block composition of Boolean functions -/

section ComposeDefs

/-- Extract the `i`-th contiguous `m`-bit block `(j ↦ x (m * i + j))` of `x : BitString (n * m)`
via `finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)`. -/
def blockSlice {n m : ℕ} (x : BitString (n * m)) (i : Fin n) : BitString m :=
  fun j ↦ x (finProdFinEquiv (i, j))

@[simp]
theorem blockSlice_apply {n m : ℕ} (x : BitString (n * m)) (i : Fin n) (j : Fin m) :
    blockSlice x i j = x (finProdFinEquiv (i, j)) := by
  rfl

/-- Canonical bijection identifying `BitString (n * m)` with `n`-tuples of `m`-bit blocks. -/
def blockEquiv (n m : ℕ) : BitString (n * m) ≃ (Fin n → BitString m) where
  toFun := blockSlice
  invFun B k := B (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv x := by ext k; exact congrArg x (finProdFinEquiv.apply_symm_apply k)
  right_inv B := by ext i j; simp [blockSlice]

@[simp]
theorem blockEquiv_apply {n m : ℕ} (x : BitString (n * m)) :
    blockEquiv n m x = blockSlice x := by
  rfl

@[simp]
theorem blockSlice_blockEquiv_symm {n m : ℕ} (B : Fin n → BitString m) :
    blockSlice ((blockEquiv n m).symm B) = B :=
  (blockEquiv n m).apply_symm_apply B

/-- The `n`-bit summary string obtained by applying `g : BooleanFunction m` to each of the `n`
blocks of `x : BitString (n * m)`. -/
def blockSummary {n m : ℕ} (g : BooleanFunction m) (x : BitString (n * m)) : BitString n :=
  fun i ↦ g (blockSlice x i)

@[simp]
theorem blockSummary_apply {n m : ℕ} (g : BooleanFunction m) (x : BitString (n * m)) (i : Fin n) :
    blockSummary g x i = g (blockSlice x i) := by
  rfl

/-- Block composition `(f • g) : BooleanFunction (n * m)` of `f : BooleanFunction n` with `n`
independent copies of `g : BooleanFunction m`:
`(f • g)(x) = f(g(x_1, …, x_m), …, g(x_{(n-1)m+1}, …, x_{nm}))`. -/
def composeBool {n m : ℕ} (f : BooleanFunction n) (g : BooleanFunction m) :
    BooleanFunction (n * m) :=
  fun x ↦ f (blockSummary g x)

@[simp]
theorem composeBool_apply {n m : ℕ} (f : BooleanFunction n) (g : BooleanFunction m)
    (x : BitString (n * m)) :
    composeBool f g x = f (fun i ↦ g (fun j ↦ x (finProdFinEquiv (i, j)))) := by
  rfl

end ComposeDefs

/-! ### Exact multiplicativity of the general adversary bound -/

section AdversaryComposition

/-- Zeroing out the two diagonal blocks `{q a = q b}` of a real matrix does not increase its
Euclidean operator norm, since `A_off = (1/2) (A - Z A Z)` for the diagonal reflection `Z`. -/
private theorem opNorm_boolOffDiag_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (q : κ → Bool) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of fun a b ↦ if q a ≠ q b then A a b else 0)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  refine Matrix.opNorm_toEuclideanCLM_le_of_inner _ (norm_nonneg _) fun u v hu hv ↦ ?_
  let sgn (b : Bool) : ℝ := if b then 1 else -1
  let flip (w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ :=
    WithLp.toLp 2 fun a ↦ sgn (q a) * w.ofLp a
  have hflip (w : EuclideanSpace ℝ κ) (hw : ‖w‖ ≤ 1) : ‖flip w‖ ≤ 1 := by
    rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hw ⊢
    refine (le_of_eq ?_).trans hw
    refine sum_congr rfl fun a _ ↦ ?_
    cases q a <;> simp [flip, sgn]
  have hid : inner ℝ u
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of fun a b ↦ if q a ≠ q b then A a b else 0) v) =
      (1 / 2) * (inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) -
        inner ℝ (flip u) (Matrix.toEuclideanCLM (𝕜 := ℝ) A (flip v))) := by
    simp only [Matrix.inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, of_apply, flip,
      ← sum_sub_distrib]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    cases q a <;> cases q b <;> simp [sgn] <;> ring
  have h1 := (le_abs_self _).trans (Matrix.abs_inner_toEuclideanCLM_le_opNorm A hu hv)
  have h2 := (neg_le_abs _).trans
    (Matrix.abs_inner_toEuclideanCLM_le_opNorm A (hflip u hu) (hflip v hv))
  linarith

/-- **Submultiplicativity of `ADV±` under block composition**
: `ADV±(f • g) ≤ ADV±(f) · ADV±(g)`.
-/
theorem generalAdversary_composeBool_le {n m : ℕ} (f : BooleanFunction n) (g : BooleanFunction m) :
    generalAdversary (fun _ ↦ True) (composeBool f g) ≤
      generalAdversary (fun _ ↦ True) f * generalAdversary (fun _ ↦ True) g := by
  obtain ⟨kf, wf, hwf⟩ := exists_dualAdversary_eq_generalAdversary (fun _ ↦ True) f
  obtain ⟨kg, wg, hwg⟩ := exists_dualAdversary_eq_generalAdversary (fun _ ↦ True) g
  rw [← hwf, ← hwg]
  refine (generalAdversary_le_iff (mul_nonneg wf.weight_nonneg wg.weight_nonneg)).2
    fun Γ _ hΓ ↦ ?_
  rw [mul_assoc]
  refine wf.opNorm_le_weight_mul (blockSummary g) Γ
    (fun x y hxy ↦ ⟨trivial, trivial, (hΓ x y hxy).2.2⟩)
    (mul_nonneg wg.weight_nonneg (maxDiffNorm_nonneg Γ)) fun i ↦ ?_
  let Γi : Matrix (BitString (n * m)) (BitString (n * m)) ℝ :=
    Matrix.of fun x y ↦ if g (blockSlice x i) ≠ g (blockSlice y i) then Γ x y else 0
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γi‖ ≤ wg.weight * maxDiffNorm Γ
  refine wg.opNorm_le_weight_mul (fun x ↦ blockSlice x i) Γi
    (fun x y hxy ↦ ⟨trivial, trivial, fun heq ↦ hxy (by simp [Γi, heq])⟩)
    (maxDiffNorm_nonneg Γ) fun j ↦ ?_
  let k := finProdFinEquiv (i, j)
  have heq : (Matrix.of fun x y : BitString (n * m) ↦
      if blockSlice x i j ≠ blockSlice y i j then Γi x y else 0) =
      Matrix.of fun x y ↦ if g (blockSlice x i) ≠ g (blockSlice y i)
        then (Γ.hadamard (diffMatrix k)) x y else 0 := by
    ext x y
    simp only [Γi, of_apply, blockSlice_apply, hadamard_apply, diffMatrix_apply, k]
    by_cases hg : g (blockSlice x i) ≠ g (blockSlice y i) <;>
      by_cases hx : x (finProdFinEquiv (i, j)) ≠ y (finProdFinEquiv (i, j)) <;>
      simp [hg, hx]
  rw [heq]
  exact (opNorm_boolOffDiag_le (Γ.hadamard (diffMatrix k)) (fun x ↦ g (blockSlice x i))).trans
    (norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γ k)

/-- Attainment of the operator norm of a real continuous linear map on a proper Hilbert space. -/
private theorem exists_unit_inner_eq_opNorm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [ProperSpace E] (T : E →L[ℝ] E) :
    ∃ u v : E, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧ inner ℝ u (T v) = ‖T‖ := by
  let B : Set E := Metric.closedBall 0 1
  have hmem {w : E} : w ∈ B ↔ ‖w‖ ≤ 1 := by rw [Metric.mem_closedBall, dist_zero_right]
  have h0B : (0 : E) ∈ B := hmem.2 (norm_zero.trans_le zero_le_one)
  have hcomp : IsCompact (B ×ˢ B) := (isCompact_closedBall 0 1).prod (isCompact_closedBall 0 1)
  have hcont : Continuous (fun p : E × E ↦ inner ℝ p.1 (T p.2)) :=
    continuous_fst.inner (T.continuous.comp continuous_snd)
  obtain ⟨⟨u, v⟩, huv, hmax⟩ := hcomp.exists_isMaxOn ⟨(0, 0), h0B, h0B⟩ hcont.continuousOn
  have hu : ‖u‖ ≤ 1 := hmem.1 huv.1
  have hv : ‖v‖ ≤ 1 := hmem.1 huv.2
  have h0 : 0 ≤ inner ℝ u (T v) := by
    have h : inner ℝ 0 (T 0) ≤ inner ℝ u (T v) := hmax (a := (0, 0)) ⟨h0B, h0B⟩
    rwa [inner_zero_left] at h
  have hle : inner ℝ u (T v) ≤ ‖T‖ :=
    (real_inner_le_norm u (T v)).trans <|
      (mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg u)).trans <|
        (mul_le_of_le_one_left (mul_nonneg (norm_nonneg T) (norm_nonneg v)) hu).trans <|
          mul_le_of_le_one_right (norm_nonneg T) hv
  have hge : ‖T‖ ≤ inner ℝ u (T v) := T.opNorm_le_bound h0 fun x ↦ by
    by_cases hx : ‖x‖ = 0
    · simp [norm_eq_zero.1 hx]
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    by_cases hTx : ‖T x‖ = 0
    · rw [hTx]; positivity
    have hTpos : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hTx)
    have ha : ‖(‖T x‖⁻¹) • T x‖ ≤ 1 := by simp [norm_smul, hTpos.ne']
    have hb : ‖(‖x‖⁻¹) • x‖ ≤ 1 := by simp [norm_smul, hxpos.ne']
    have hm : inner ℝ ((‖T x‖⁻¹) • T x) (T ((‖x‖⁻¹) • x)) ≤ inner ℝ u (T v) :=
      hmax (a := ((‖T x‖⁻¹) • T x, (‖x‖⁻¹) • x)) ⟨hmem.2 ha, hmem.2 hb⟩
    rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq,
      show ‖T x‖⁻¹ * (‖x‖⁻¹ * ‖T x‖ ^ 2) = ‖T x‖ / ‖x‖ by field_simp,
      div_le_iff₀ hxpos] at hm
    exact hm
  exact ⟨u, v, hu, hv, le_antisymm hle hge⟩

/-- For a nonzero real symmetric adversary matrix `Γ_g` of a total Boolean function `g`, there
exist unit vectors `μ false` and `μ true` supported on `g⁻¹(false)` and `g⁻¹(true)` achieving
`⟨μ false, Γ_g (μ true)⟩ = ⟨μ true, Γ_g (μ false)⟩ = ‖Γ_g‖`. -/
private theorem exists_fiber_unit_vectors {m : ℕ} {g : BooleanFunction m}
    {Γ : Matrix (BitString m) (BitString m) ℝ} (hsym : Γ.IsSymm)
    (hΓ : IsAdversaryMatrix (fun _ ↦ True) g Γ)
    (hpos : 0 < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖) :
    ∃ μ : Bool → EuclideanSpace ℝ (BitString m),
      (∀ b, ‖μ b‖ = 1) ∧
      (∀ b w, (μ b).ofLp w ≠ 0 → g w = b) ∧
      (∀ b₁ b₂, b₁ ≠ b₂ →
        inner ℝ (μ b₁) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (μ b₂)) =
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖) := by
  set lam := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖
  obtain ⟨u, v, hu, hv, huv⟩ := exists_unit_inner_eq_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ)
  let part (w : EuclideanSpace ℝ (BitString m)) (b : Bool) : EuclideanSpace ℝ (BitString m) :=
    WithLp.toLp 2 fun x ↦ if g x = b then w.ofLp x else 0
  have hpart_sq (w : EuclideanSpace ℝ (BitString m)) :
      ‖part w false‖ ^ 2 + ‖part w true‖ ^ 2 = ‖w‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, part, ← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by cases g x <;> simp
  have hsplit : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) =
      inner ℝ (part u false) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (part v true)) +
      inner ℝ (part u true) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (part v false)) := by
    simp only [Matrix.inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, part, ← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    by_cases h0 : Γ x y = 0
    · simp [h0]
    · have hne := (hΓ x y h0).2.2
      cases hgx : g x <;> cases hgy : g y <;> simp_all
  set a0 := ‖part u false‖
  set a1 := ‖part u true‖
  set b0 := ‖part v false‖
  set b1 := ‖part v true‖
  set I01 := inner ℝ (part u false) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (part v true))
  set I10 := inner ℝ (part u true) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (part v false))
  have hI01 : I01 ≤ lam * (a0 * b1) := by
    calc I01 ≤ a0 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (part v true)‖ := real_inner_le_norm _ _
      _ ≤ a0 * (lam * b1) := mul_le_mul_of_nonneg_left
          ((Matrix.toEuclideanCLM (𝕜 := ℝ) Γ).le_opNorm _) (norm_nonneg _)
      _ = lam * (a0 * b1) := by ring
  have hI10 : I10 ≤ lam * (a1 * b0) := by
    calc I10 ≤ a1 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (part v false)‖ := real_inner_le_norm _ _
      _ ≤ a1 * (lam * b0) := mul_le_mul_of_nonneg_left
          ((Matrix.toEuclideanCLM (𝕜 := ℝ) Γ).le_opNorm _) (norm_nonneg _)
      _ = lam * (a1 * b0) := by ring
  have ha_sq : a0 ^ 2 + a1 ^ 2 ≤ 1 := (hpart_sq u).trans_le (sq_le_one_iff₀ (norm_nonneg u) |>.2 hu)
  have hb_sq : b0 ^ 2 + b1 ^ 2 ≤ 1 := (hpart_sq v).trans_le (sq_le_one_iff₀ (norm_nonneg v) |>.2 hv)
  have hprod_le : a0 * b1 + a1 * b0 ≤ 1 := by
    nlinarith [sq_nonneg (a0 - b1), sq_nonneg (a1 - b0)]
  have heq01 : I01 = lam * (a0 * b1) := by nlinarith [huv, hsplit]
  have heq10 : I10 = lam * (a1 * b0) := by nlinarith [huv, hsplit]
  have hsym_inner (p q : EuclideanSpace ℝ (BitString m)) :
      inner ℝ q (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ p) =
        inner ℝ p (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ q) := by
    simp only [Matrix.inner_toEuclideanCLM, dotProduct, mulVec, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by rw [hsym.apply x y]; ring
  have hbuild (p q : EuclideanSpace ℝ (BitString m)) (hp : 0 < ‖p‖) (hq : 0 < ‖q‖)
      (hp_supp : ∀ w, p.ofLp w ≠ 0 → g w = false)
      (hq_supp : ∀ w, q.ofLp w ≠ 0 → g w = true)
      (hpq : inner ℝ p (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ q) = lam * (‖p‖ * ‖q‖)) :
      ∃ μ : Bool → EuclideanSpace ℝ (BitString m),
        (∀ b, ‖μ b‖ = 1) ∧ (∀ b w, (μ b).ofLp w ≠ 0 → g w = b) ∧
        (∀ b₁ b₂, b₁ ≠ b₂ →
          inner ℝ (μ b₁) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (μ b₂)) = lam) := by
    let μ : Bool → EuclideanSpace ℝ (BitString m) := fun b ↦
      if b then (‖q‖⁻¹) • q else (‖p‖⁻¹) • p
    have hft : inner ℝ (μ false) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (μ true)) = lam := by
      simp only [μ, Bool.false_eq_true, ↓reduceIte, map_smul, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real, hpq]
      have hpne := hp.ne'; have hqne := hq.ne'
      field_simp
    refine ⟨μ, fun b ↦ ?_, fun b w hw ↦ ?_, fun b₁ b₂ hne ↦ ?_⟩
    · cases b <;> simp [μ, norm_smul, hp.ne', hq.ne']
    · cases b
      · simp only [μ, Bool.false_eq_true, ↓reduceIte, PiLp.smul_apply, smul_eq_mul] at hw
        exact hp_supp w (right_ne_zero_of_mul hw)
      · simp only [μ, ↓reduceIte, PiLp.smul_apply, smul_eq_mul] at hw
        exact hq_supp w (right_ne_zero_of_mul hw)
    · cases b₁ <;> cases b₂
      · exact (hne rfl).elim
      · exact hft
      · rw [hsym_inner]; exact hft
      · exact (hne rfl).elim
  by_cases h01 : 0 < a0 * b1
  · have ha0 : 0 < a0 := pos_of_mul_pos_left h01 (norm_nonneg _)
    have hb1 : 0 < b1 := pos_of_mul_pos_right h01 (norm_nonneg _)
    exact hbuild (part u false) (part v true) ha0 hb1
      (fun w hw ↦ Classical.byContradiction fun h ↦ hw (by simp [part, h]))
      (fun w hw ↦ Classical.byContradiction fun h ↦ hw (by simp [part, h])) heq01
  · have h10 : 0 < a1 * b0 := by
      have h01_eq : a0 * b1 = 0 := le_antisymm (le_of_not_gt h01) (by positivity)
      have h01_z : I01 = 0 := by rw [heq01, h01_eq, mul_zero]
      have : lam * (a1 * b0) = lam := by linarith [huv, hsplit, h01_z, heq10]
      nlinarith
    have ha1 : 0 < a1 := pos_of_mul_pos_left h10 (norm_nonneg _)
    have hb0 : 0 < b0 := pos_of_mul_pos_right h10 (norm_nonneg _)
    exact hbuild (part v false) (part u true) hb0 ha1
      (fun w hw ↦ Classical.byContradiction fun h ↦ hw (by simp [part, h]))
      (fun w hw ↦ Classical.byContradiction fun h ↦ hw (by simp [part, h]))
      (by rw [hsym_inner, mul_comm ‖part v false‖]; exact heq10)

/-- Bilinear bound for the Kronecker product of two real matrices:
`|∑ p, ∑ q, u p · (A p.1 q.1 · B p.2 q.2) · v q| ≤ ‖A‖ · ‖B‖ · ‖u‖ · ‖v‖`. -/
private theorem kronecker_bilinear_le {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁]
    [Fintype κ₂] [DecidableEq κ₂] (A : Matrix κ₁ κ₁ ℝ) (B : Matrix κ₂ κ₂ ℝ)
    (u v : EuclideanSpace ℝ (κ₁ × κ₂)) :
    ∑ p : κ₁ × κ₂, ∑ q : κ₁ × κ₂, u.ofLp p * (A p.1 q.1 * B p.2 q.2) * v.ofLp q ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * ‖u‖ * ‖v‖ := by
  let w (i' : κ₁) (j : κ₂) : ℝ := ∑ j' : κ₂, B j j' * v.ofLp (i', j')
  have hw_row (i' : κ₁) :
      ∑ j : κ₂, w i' j ^ 2 ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ ^ 2 * ∑ j' : κ₂, v.ofLp (i', j') ^ 2 := by
    let vi : EuclideanSpace ℝ κ₂ := WithLp.toLp 2 fun j' ↦ v.ofLp (i', j')
    have hle := (Matrix.toEuclideanCLM (𝕜 := ℝ) B).le_opNorm vi
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
    exact hsq
  have hw_tot : √(∑ j : κ₂, ∑ i' : κ₁, w i' j ^ 2) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * ‖v‖ := by
    rw [sum_comm]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∑ i' : κ₁, ∑ j : κ₂, w i' j ^ 2
        ≤ ∑ i' : κ₁, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ ^ 2 * ∑ j' : κ₂, v.ofLp (i', j') ^ 2 :=
          sum_le_sum fun i' _ ↦ hw_row i'
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ ^ 2 * ‖v‖ ^ 2 := by
          rw [← mul_sum, ← Fintype.sum_prod_type (fun p : κ₁ × κ₂ ↦ v.ofLp p ^ 2),
            ← EuclideanSpace.real_norm_sq_eq]
      _ = (‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * ‖v‖) ^ 2 := (mul_pow _ _ _).symm
  have hcol (j : κ₂) :
      ∑ i : κ₁, ∑ i' : κ₁, u.ofLp (i, j) * (A i i' * w i' j) ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
          (√(∑ i : κ₁, u.ofLp (i, j) ^ 2) * √(∑ i' : κ₁, w i' j ^ 2)) := by
    let uj : EuclideanSpace ℝ κ₁ := WithLp.toLp 2 fun i ↦ u.ofLp (i, j)
    let wj : EuclideanSpace ℝ κ₁ := WithLp.toLp 2 fun i' ↦ w i' j
    have hinner : ∑ i : κ₁, ∑ i' : κ₁, u.ofLp (i, j) * (A i i' * w i' j) =
        inner ℝ uj (Matrix.toEuclideanCLM (𝕜 := ℝ) A wj) := by
      simp only [Matrix.inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, uj, wj]
    have hu_eq : ‖uj‖ = √(∑ i : κ₁, u.ofLp (i, j) ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg uj), EuclideanSpace.real_norm_sq_eq]
    have hw_eq : ‖wj‖ = √(∑ i' : κ₁, w i' j ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg wj), EuclideanSpace.real_norm_sq_eq]
    rw [hinner, ← hu_eq, ← hw_eq]
    calc inner ℝ uj (Matrix.toEuclideanCLM (𝕜 := ℝ) A wj)
        ≤ ‖uj‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A wj‖ := real_inner_le_norm _ _
      _ ≤ ‖uj‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖wj‖) :=
          mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm wj)
            (norm_nonneg _)
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * (‖uj‖ * ‖wj‖) := by ring
  have hrewrite :
      ∑ p : κ₁ × κ₂, ∑ q : κ₁ × κ₂, u.ofLp p * (A p.1 q.1 * B p.2 q.2) * v.ofLp q =
        ∑ j : κ₂, ∑ i : κ₁, ∑ i' : κ₁, u.ofLp (i, j) * (A i i' * w i' j) := by
    simp only [Fintype.sum_prod_type, w, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun i' _ ↦
      sum_congr rfl fun j' _ ↦ by ring
  have hu_tot : √(∑ j : κ₂, ∑ i : κ₁, u.ofLp (i, j) ^ 2) = ‖u‖ := by
    rw [sum_comm, ← Fintype.sum_prod_type (fun p : κ₁ × κ₂ ↦ u.ofLp p ^ 2),
      ← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg u)]
  rw [hrewrite]
  calc ∑ j : κ₂, ∑ i : κ₁, ∑ i' : κ₁, u.ofLp (i, j) * (A i i' * w i' j)
      ≤ ∑ j : κ₂, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
          (√(∑ i : κ₁, u.ofLp (i, j) ^ 2) * √(∑ i' : κ₁, w i' j ^ 2)) :=
        sum_le_sum fun j _ ↦ hcol j
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
          ∑ j : κ₂, √(∑ i : κ₁, u.ofLp (i, j) ^ 2) * √(∑ i' : κ₁, w i' j ^ 2) :=
        (mul_sum _ _ _).symm
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
          (√(∑ j : κ₂, ∑ i : κ₁, u.ofLp (i, j) ^ 2) *
            √(∑ j : κ₂, ∑ i' : κ₁, w i' j ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (Real.sum_sqrt_mul_sqrt_le _ (fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)
            (fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)) (norm_nonneg _)
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
          (‖u‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * ‖v‖)) := by
        rw [hu_tot]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hw_tot (norm_nonneg u)) (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ *
          ‖u‖ * ‖v‖ := by ring

/-- Single-matrix composition inequality for the general adversary bound. -/
private theorem ratio_mul_ratio_le_generalAdversary_composeBool {n m : ℕ}
    (f : BooleanFunction n) (g : BooleanFunction m)
    {Γf : Matrix (BitString n) (BitString n) ℝ} (hsymf : Γf.IsSymm)
    (hΓf : IsAdversaryMatrix (fun _ ↦ True) f Γf)
    {Γg : Matrix (BitString m) (BitString m) ℝ} (hsymg : Γg.IsSymm)
    (hΓg : IsAdversaryMatrix (fun _ ↦ True) g Γg) :
    (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γf‖ / maxDiffNorm Γf) *
        (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γg‖ / maxDiffNorm Γg) ≤
      generalAdversary (fun _ ↦ True) (composeBool f g) := by
  classical
  by_cases hfz : Γf = 0
  · simp [hfz, generalAdversary_nonneg]
  by_cases hgz : Γg = 0
  · simp [hgz, generalAdversary_nonneg]
  have hn_pos : 0 < n := by
    by_contra hn0
    have : n = 0 := by omega
    subst this
    exact hfz (Matrix.ext fun x y ↦ Classical.byContradiction fun h ↦
      (hΓf x y h).2.2 (congrArg f (Subsingleton.elim x y)))
  set lamf := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γf‖
  set lamg := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γg‖
  have hlamf_pos : 0 < lamf := norm_pos_iff.2 fun h ↦ hfz <| Matrix.ext fun x y ↦ by
    simpa [h] using Matrix.abs_entry_le_norm_toEuclideanCLM Γf x y
  have hlamg_pos : 0 < lamg := norm_pos_iff.2 fun h ↦ hgz <| Matrix.ext fun x y ↦ by
    simpa [h] using Matrix.abs_entry_le_norm_toEuclideanCLM Γg x y
  have hmdf_pos : 0 < maxDiffNorm Γf := lt_of_le_of_ne (maxDiffNorm_nonneg Γf) fun h ↦
    hfz (eq_zero_of_maxDiffNorm_eq_zero hΓf h.symm)
  have hmdg_pos : 0 < maxDiffNorm Γg := lt_of_le_of_ne (maxDiffNorm_nonneg Γg) fun h ↦
    hgz (eq_zero_of_maxDiffNorm_eq_zero hΓg h.symm)
  -- Step 1: Build `Mg = lamg • 1 + Γg ≽ 0` and fiber unit vectors `μ false`, `μ true`.
  obtain ⟨μ, hμ_norm, hμ_supp, hμ_inner⟩ := exists_fiber_unit_vectors hsymg hΓg hlamg_pos
  let Mg : Matrix (BitString m) (BitString m) ℝ := lamg • (1 : Matrix _ _ ℝ) + Γg
  have hMg_sym : Mg.IsSymm :=
    Matrix.ext fun w₁ w₂ ↦ by simp [Mg, Matrix.one_apply, eq_comm, hsymg.apply w₁ w₂]
  have hMg_psd : Mg.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨by simpa using hMg_sym, fun x ↦ ?_⟩
    let xe : EuclideanSpace ℝ (BitString m) := WithLp.toLp 2 x
    have hxe : ∑ w, x w ^ 2 = ‖xe‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq xe).symm
    have hinner : star x ⬝ᵥ (Mg *ᵥ x) =
        lamg * ‖xe‖ ^ 2 + inner ℝ xe (Matrix.toEuclideanCLM (𝕜 := ℝ) Γg xe) := by
      simp only [Mg, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
        smul_eq_mul, star_trivial, Matrix.inner_toEuclideanCLM]
      rw [← hxe, dotProduct, mul_sum]
      exact congrArg (· + _) (mul_sum univ (fun w ↦ x w ^ 2) lamg ▸
        sum_congr rfl fun w _ ↦ by rw [sq])
    have hbd : -inner ℝ xe (Matrix.toEuclideanCLM (𝕜 := ℝ) Γg xe) ≤ lamg * ‖xe‖ ^ 2 := by
      calc -inner ℝ xe (Matrix.toEuclideanCLM (𝕜 := ℝ) Γg xe)
          ≤ |inner ℝ xe (Matrix.toEuclideanCLM (𝕜 := ℝ) Γg xe)| := neg_le_abs _
        _ ≤ ‖xe‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γg xe‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖xe‖ * (lamg * ‖xe‖) := mul_le_mul_of_nonneg_left
            ((Matrix.toEuclideanCLM (𝕜 := ℝ) Γg).le_opNorm xe) (norm_nonneg _)
        _ = lamg * ‖xe‖ ^ 2 := by ring
    linarith
  have hMg_same {w₁ w₂ : BitString m} (h : g w₁ = g w₂) :
      Mg w₁ w₂ = if w₁ = w₂ then lamg else 0 := by
    have h0 : Γg w₁ w₂ = 0 := Classical.byContradiction fun hne ↦ (hΓg w₁ w₂ hne).2.2 h
    simp [Mg, h0, Matrix.one_apply]
  have hMg_μ (b₁ b₂ : Bool) :
      ∑ w₁, ∑ w₂, (μ b₁).ofLp w₁ * Mg w₁ w₂ * (μ b₂).ofLp w₂ = lamg := by
    by_cases hb : b₁ = b₂
    · subst hb
      have hterm (w₁ w₂ : BitString m) :
          (μ b₁).ofLp w₁ * Mg w₁ w₂ * (μ b₁).ofLp w₂ =
            if w₁ = w₂ then lamg * (μ b₁).ofLp w₁ ^ 2 else 0 := by
        by_cases h1 : (μ b₁).ofLp w₁ = 0
        · split_ifs <;> simp [h1]
        by_cases h2 : (μ b₁).ofLp w₂ = 0
        · split_ifs with heq
          · subst heq; exact (h1 h2).elim
          · simp [h2]
        rw [hMg_same ((hμ_supp b₁ w₁ h1).trans (hμ_supp b₁ w₂ h2).symm)]
        split_ifs with heq
        · subst heq; ring
        · ring
      simp only [hterm, sum_ite_eq, mem_univ, ↓reduceIte, ← mul_sum,
        ← EuclideanSpace.real_norm_sq_eq, hμ_norm b₁, one_pow, mul_one]
    · have hterm (w₁ w₂ : BitString m) :
          (μ b₁).ofLp w₁ * Mg w₁ w₂ * (μ b₂).ofLp w₂ =
            (μ b₁).ofLp w₁ * (Γg w₁ w₂ * (μ b₂).ofLp w₂) := by
        by_cases h1 : (μ b₁).ofLp w₁ = 0
        · simp [h1]
        by_cases h2 : (μ b₂).ofLp w₂ = 0
        · simp [h2]
        have hwne : w₁ ≠ w₂ := fun heq ↦ hb ((hμ_supp b₁ w₁ h1).symm.trans
          (heq ▸ hμ_supp b₂ w₂ h2))
        simp [Mg, hwne]; ring
      have h1 := hμ_inner b₁ b₂ hb
      rw [Matrix.inner_toEuclideanCLM] at h1
      simpa only [dotProduct, mulVec, mul_sum, hterm] using h1
  -- Step 2: Construct composed adversary matrix `Γ x y = Γf (z(x)) (z(y)) * ∏_i Mg (x_i) (y_i)`.
  let Γ : Matrix (BitString (n * m)) (BitString (n * m)) ℝ :=
    Matrix.of fun x y ↦
      Γf (blockSummary g x) (blockSummary g y) * ∏ i : Fin n, Mg (blockSlice x i) (blockSlice y i)
  have hΓ_sym : Γ.IsSymm := Matrix.ext fun x y ↦ by
    simp only [Γ, transpose_apply, of_apply, hsymf.apply (blockSummary g x) (blockSummary g y),
      fun i ↦ hMg_sym.apply (blockSlice x i) (blockSlice y i)]
  have hΓ_adv : IsAdversaryMatrix (fun _ ↦ True) (composeBool f g) Γ := fun x y hxy ↦
    ⟨trivial, trivial, (hΓf _ _ (left_ne_zero_of_mul hxy)).2.2⟩
  -- Step 3: Prove `lamf * lamg ^ n ≤ ‖Γ‖` via lifted unit vectors.
  have hΓ_norm : lamf * lamg ^ n ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
    obtain ⟨α, β, hα, hβ, hαβ⟩ := exists_unit_inner_eq_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) Γf)
    let liftVec (γ : EuclideanSpace ℝ (BitString n)) : EuclideanSpace ℝ (BitString (n * m)) :=
      WithLp.toLp 2 fun x ↦
        γ.ofLp (blockSummary g x) * ∏ i : Fin n, (μ (blockSummary g x i)).ofLp (blockSlice x i)
    have hprod_supp (z : BitString n) (B : Fin n → BitString m)
        (hne : (fun i ↦ g (B i)) ≠ z) : ∏ i : Fin n, (μ (z i)).ofLp (B i) = 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
      exact prod_eq_zero (mem_univ i)
        (Classical.byContradiction fun h ↦ hi (hμ_supp (z i) (B i) h))
    have hlift_le (γ : EuclideanSpace ℝ (BitString n)) (hγ : ‖γ‖ ≤ 1) : ‖liftVec γ‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hγ ⊢
      refine (le_of_eq ((Fintype.sum_equiv (blockEquiv n m) (fun x ↦ (liftVec γ).ofLp x ^ 2)
        (fun B ↦ (γ.ofLp (fun i ↦ g (B i)) * ∏ i : Fin n, (μ (g (B i))).ofLp (B i)) ^ 2)
        fun x ↦ rfl).trans ?_)).trans hγ
      trans ∑ z : BitString n, γ.ofLp z ^ 2 * ∑ B : Fin n → BitString m,
          ∏ i : Fin n, (μ (z i)).ofLp (B i) ^ 2
      · simp only [mul_sum]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun B _ ↦ ?_
        rw [sum_eq_single (fun i ↦ g (B i))
          (fun z _ hz ↦ by rw [prod_pow, hprod_supp z B hz.symm]; simp) (by simp),
          mul_pow, ← prod_pow]
      · refine sum_congr rfl fun z _ ↦ ?_
        have hpi : ∑ B : Fin n → BitString m, ∏ i : Fin n, (μ (z i)).ofLp (B i) ^ 2 =
            ∏ i : Fin n, ∑ w : BitString m, (μ (z i)).ofLp w ^ 2 :=
          (Fintype.prod_sum fun i w ↦ (μ (z i)).ofLp w ^ 2).symm
        simp only [hpi, ← EuclideanSpace.real_norm_sq_eq, hμ_norm, one_pow, prod_const_one, mul_one]
    have hlift_inner :
        inner ℝ (liftVec α) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (liftVec β)) =
          lamf * lamg ^ n := by
      rw [Matrix.inner_toEuclideanCLM]
      simp only [dotProduct, mulVec, mul_sum, Γ, of_apply, liftVec]
      have hreidx :
          ∑ x : BitString (n * m), ∑ y : BitString (n * m),
            (α.ofLp (blockSummary g x) *
              ∏ i, (μ (blockSummary g x i)).ofLp (blockSlice x i)) *
            (Γf (blockSummary g x) (blockSummary g y) *
              (∏ i, Mg (blockSlice x i) (blockSlice y i)) *
              (β.ofLp (blockSummary g y) *
                ∏ i, (μ (blockSummary g y i)).ofLp (blockSlice y i))) =
          ∑ z₁ : BitString n, ∑ z₂ : BitString n,
            α.ofLp z₁ * (Γf z₁ z₂ * β.ofLp z₂) *
            ∑ B₁ : Fin n → BitString m, ∑ B₂ : Fin n → BitString m,
              ∏ i : Fin n,
                (μ (z₁ i)).ofLp (B₁ i) * Mg (B₁ i) (B₂ i) * (μ (z₂ i)).ofLp (B₂ i) := by
        refine (Fintype.sum_equiv (blockEquiv n m) _
          (fun B₁ ↦ ∑ B₂ : Fin n → BitString m,
            (α.ofLp (fun i ↦ g (B₁ i)) * ∏ i, (μ (g (B₁ i))).ofLp (B₁ i)) *
            (Γf (fun i ↦ g (B₁ i)) (fun i ↦ g (B₂ i)) * (∏ i, Mg (B₁ i) (B₂ i)) *
              (β.ofLp (fun i ↦ g (B₂ i)) * ∏ i, (μ (g (B₂ i))).ofLp (B₂ i))))
          fun x ↦ Fintype.sum_equiv (blockEquiv n m) _ _ fun y ↦ rfl).trans ?_
        simp only [mul_sum]
        conv_rhs => enter [2, z₁]; rw [sum_comm]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun B₁ _ ↦ ?_
        conv_rhs => enter [2, z₁]; rw [sum_comm]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun B₂ _ ↦ ?_
        simp only [prod_mul_distrib]
        rw [sum_eq_single (fun i ↦ g (B₁ i))
          (fun z₁ _ hz₁ ↦ sum_eq_zero fun z₂ _ ↦ by simp [hprod_supp z₁ B₁ hz₁.symm]) (by simp),
          sum_eq_single (fun i ↦ g (B₂ i))
          (fun z₂ _ hz₂ ↦ by simp [hprod_supp z₂ B₂ hz₂.symm]) (by simp)]
        ring
      have hfactor (z₁ z₂ : BitString n) :
          ∑ B₁ : Fin n → BitString m, ∑ B₂ : Fin n → BitString m,
            ∏ i : Fin n, (μ (z₁ i)).ofLp (B₁ i) * Mg (B₁ i) (B₂ i) * (μ (z₂ i)).ofLp (B₂ i) =
          lamg ^ n := by
        calc ∑ B₁ : Fin n → BitString m, ∑ B₂ : Fin n → BitString m,
              ∏ i : Fin n, (μ (z₁ i)).ofLp (B₁ i) * Mg (B₁ i) (B₂ i) * (μ (z₂ i)).ofLp (B₂ i)
            = ∑ p : Fin n → BitString m × BitString m,
                ∏ i : Fin n,
                  (μ (z₁ i)).ofLp (p i).1 * Mg (p i).1 (p i).2 * (μ (z₂ i)).ofLp (p i).2 := by
              rw [← Fintype.sum_prod_type fun q : (Fin n → BitString m) × (Fin n → BitString m) ↦
                ∏ i : Fin n,
                  (μ (z₁ i)).ofLp (q.1 i) * Mg (q.1 i) (q.2 i) * (μ (z₂ i)).ofLp (q.2 i)]
              exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun _ ↦ rfl
          _ = ∏ i : Fin n, ∑ q : BitString m × BitString m,
                (μ (z₁ i)).ofLp q.1 * Mg q.1 q.2 * (μ (z₂ i)).ofLp q.2 :=
              (Fintype.prod_sum fun (i : Fin n) (q : BitString m × BitString m) ↦
                (μ (z₁ i)).ofLp q.1 * Mg q.1 q.2 * (μ (z₂ i)).ofLp q.2).symm
          _ = ∏ _i : Fin n, lamg :=
              prod_congr rfl fun i _ ↦ by rw [Fintype.sum_prod_type, hMg_μ]
          _ = lamg ^ n := by simp
      rw [hreidx]
      simp only [hfactor, ← sum_mul]
      have hαβ' : ∑ z₁ : BitString n, ∑ z₂ : BitString n, α.ofLp z₁ * (Γf z₁ z₂ * β.ofLp z₂) =
          lamf := by
        simpa [Matrix.inner_toEuclideanCLM, dotProduct, mulVec, mul_sum] using hαβ
      rw [hαβ']
    rw [← hlift_inner]
    exact (le_abs_self _).trans
      (Matrix.abs_inner_toEuclideanCLM_le_opNorm Γ (hlift_le α hα) (hlift_le β hβ))
  -- Step 4: Prove `maxDiffNorm Γ ≤ maxDiffNorm Γf * maxDiffNorm Γg * lamg ^ (n - 1)`.
  let Q := psdFactor hMg_psd
  have hΓ_md : maxDiffNorm Γ ≤ maxDiffNorm Γf * maxDiffNorm Γg * lamg ^ (n - 1) := by
    refine (maxDiffNorm_le_iff (by positivity)).2 fun idx ↦ ?_
    set i₀ := (finProdFinEquiv.symm idx).1
    set j₀ := (finProdFinEquiv.symm idx).2
    have hidx : finProdFinEquiv (i₀, j₀) = idx := finProdFinEquiv.apply_symm_apply idx
    let S : Finset (Fin n) := univ.erase i₀
    have hcardS : #S = n - 1 := by simp [S, card_erase_of_mem]
    have hentry (x y : BitString (n * m)) :
        (Γ.hadamard (diffMatrix idx)) x y =
          (Γf.hadamard (diffMatrix i₀)) (blockSummary g x) (blockSummary g y) *
          (Γg.hadamard (diffMatrix j₀)) (blockSlice x i₀) (blockSlice y i₀) *
          ∏ i ∈ S, Mg (blockSlice x i) (blockSlice y i) := by
      simp only [hadamard_apply, diffMatrix_apply, Γ, of_apply, ← hidx]
      rw [← mul_prod_erase univ (fun i ↦ Mg (blockSlice x i) (blockSlice y i)) (mem_univ i₀)]
      by_cases hdiff : x (finProdFinEquiv (i₀, j₀)) ≠ y (finProdFinEquiv (i₀, j₀))
      · have hslice_ne : blockSlice x i₀ ≠ blockSlice y i₀ := fun h ↦ hdiff (congrFun h j₀)
        have hMg0 : Mg (blockSlice x i₀) (blockSlice y i₀) =
            Γg (blockSlice x i₀) (blockSlice y i₀) := by simp [Mg, hslice_ne]
        simp only [hdiff, ne_eq, not_false_eq_true, ↓reduceIte, mul_one, hMg0, blockSlice_apply,
          S]
        by_cases hgi : g (blockSlice x i₀) ≠ g (blockSlice y i₀)
        · simp only [blockSummary_apply, hgi, not_false_eq_true, ↓reduceIte, mul_one]; ring
        · push Not at hgi
          have hΓg0 : Γg (blockSlice x i₀) (blockSlice y i₀) = 0 :=
            Classical.byContradiction fun hne ↦ (hΓg _ _ hne).2.2 hgi
          simp [hΓg0]
      · simp [hdiff, blockSlice_apply]
    refine Matrix.opNorm_toEuclideanCLM_le_of_inner _ (by positivity) fun a b ha hb ↦ ?_
    let K := {i : Fin n // i ∈ S} → BitString m
    let projVec (u : EuclideanSpace ℝ (BitString (n * m))) (k : K) :
        EuclideanSpace ℝ (BitString n × BitString m) :=
      WithLp.toLp 2 fun (z, w) ↦
        ∑ x with blockSummary g x = z ∧ blockSlice x i₀ = w,
          u.ofLp x * ∏ i : {i : Fin n // i ∈ S}, Q (k i) (blockSlice x i.1)
    have hproj_gram (x y : BitString (n * m)) :
        ∑ k : K, (∏ i : {i : Fin n // i ∈ S}, Q (k i) (blockSlice x i.1)) *
            (∏ i : {i : Fin n // i ∈ S}, Q (k i) (blockSlice y i.1)) =
          ∏ i ∈ S, Mg (blockSlice x i) (blockSlice y i) := by
      simp only [← prod_mul_distrib]
      rw [(Fintype.prod_sum fun (i : {i : Fin n // i ∈ S}) d ↦
        Q d (blockSlice x i.1) * Q d (blockSlice y i.1)).symm]
      simp only [Q, sum_psdFactor_mul]
      exact prod_coe_sort S fun i ↦ Mg (blockSlice x i) (blockSlice y i)
    have hproj_norm (u : EuclideanSpace ℝ (BitString (n * m))) (hu : ‖u‖ ≤ 1) :
        ∑ k : K, ‖projVec u k‖ ^ 2 ≤ lamg ^ (n - 1) := by
      simp only [EuclideanSpace.real_norm_sq_eq, projVec]
      rw [sum_comm]
      have hcell (p : BitString n × BitString m) :
          ∑ k : K, (∑ x with blockSummary g x = p.1 ∧ blockSlice x i₀ = p.2,
            u.ofLp x * ∏ i : {i : Fin n // i ∈ S}, Q (k i) (blockSlice x i.1)) ^ 2 =
          lamg ^ (n - 1) *
            ∑ x with blockSummary g x = p.1 ∧ blockSlice x i₀ = p.2, u.ofLp x ^ 2 := by
        set F := univ.filter fun x : BitString (n * m) ↦
          blockSummary g x = p.1 ∧ blockSlice x i₀ = p.2
        have hexp : ∑ k : K, (∑ x ∈ F,
              u.ofLp x * ∏ i : {i : Fin n // i ∈ S}, Q (k i) (blockSlice x i.1)) ^ 2 =
            ∑ x ∈ F, ∑ y ∈ F,
              u.ofLp x * u.ofLp y * ∏ i ∈ S, Mg (blockSlice x i) (blockSlice y i) := by
          simp only [sq, sum_mul, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun x _ ↦ ?_
          rw [sum_comm]
          refine sum_congr rfl fun y _ ↦ ?_
          rw [← hproj_gram, mul_sum]
          exact sum_congr rfl fun k _ ↦ by ring
        rw [hexp, mul_sum]
        refine sum_congr rfl fun x hx ↦ ?_
        obtain ⟨hxz, hxw⟩ := (mem_filter.1 hx).2
        rw [sum_eq_single x _ (fun h ↦ (h hx).elim)]
        · have hdiag : ∏ i ∈ S, Mg (blockSlice x i) (blockSlice x i) = lamg ^ (n - 1) := by
            trans ∏ _i ∈ S, lamg
            · exact prod_congr rfl fun i _ ↦ by simp [hMg_same rfl]
            · rw [prod_const, hcardS]
          rw [hdiag]; ring
        · intro y hy hyx
          obtain ⟨hyz, hyw⟩ := (mem_filter.1 hy).2
          have hblk_ne : ∃ i ∈ S, blockSlice x i ≠ blockSlice y i := by
            by_contra hall
            push Not at hall
            refine hyx ((blockEquiv n m).injective (funext fun i ↦ ?_))
            by_cases hi : i = i₀
            · subst hi; exact hyw.trans hxw.symm
            · exact (hall i (mem_erase.2 ⟨hi, mem_univ i⟩)).symm
          obtain ⟨i, hiS, hne_i⟩ := hblk_ne
          have hgi : g (blockSlice x i) = g (blockSlice y i) := by
            simpa using congrFun (hxz.trans hyz.symm) i
          have hzero : Mg (blockSlice x i) (blockSlice y i) = 0 := by simp [hMg_same hgi, hne_i]
          rw [prod_eq_zero hiS hzero, mul_zero]
      have hpart : ∑ p : BitString n × BitString m,
          ∑ x with blockSummary g x = p.1 ∧ blockSlice x i₀ = p.2, u.ofLp x ^ 2 =
          ∑ x : BitString (n * m), u.ofLp x ^ 2 := by
        simp only [sum_filter]
        rw [sum_comm]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_eq_single (blockSummary g x, blockSlice x i₀) (fun ⟨z, w⟩ _ h ↦ by
          split_ifs with hc; exacts [(h (Prod.ext hc.1.symm hc.2.symm)).elim, rfl]) (by simp)]
        simp
      simp only [hcell, ← mul_sum, hpart]
      exact (mul_le_mul_of_nonneg_left
        ((EuclideanSpace.norm_le_one_iff_sum_sq_le_one u).1 hu) (by positivity)).trans_eq
        (mul_one _)
    have hdecomp :
        inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (diffMatrix idx)) b) =
          ∑ k : K, ∑ p : BitString n × BitString m, ∑ q : BitString n × BitString m,
            (projVec a k).ofLp p *
              ((Γf.hadamard (diffMatrix i₀)) p.1 q.1 *
                (Γg.hadamard (diffMatrix j₀)) p.2 q.2) *
              (projVec b k).ofLp q := by
      rw [Matrix.inner_toEuclideanCLM]
      simp only [dotProduct, mulVec, mul_sum, hentry, ← hproj_gram]
      simp only [projVec, sum_filter]
      trans ∑ k : K, ∑ x : BitString (n * m), ∑ y : BitString (n * m),
          (a.ofLp x * ∏ i : {i // i ∈ S}, Q (k i) (blockSlice x i.1)) *
          ((Γf.hadamard (diffMatrix i₀)) (blockSummary g x) (blockSummary g y) *
            (Γg.hadamard (diffMatrix j₀)) (blockSlice x i₀) (blockSlice y i₀)) *
          (b.ofLp y * ∏ i : {i // i ∈ S}, Q (k i) (blockSlice y i.1))
      · conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ ↦ ?_
        simp only [sum_mul, mul_sum]
        exact sum_congr rfl fun k _ ↦ by ring
      · refine (sum_congr rfl fun k _ ↦ ?_).symm
        let fa (x : BitString (n * m)) :=
          a.ofLp x * ∏ i : {i // i ∈ S}, Q (k i) (blockSlice x i.1)
        let fb (y : BitString (n * m)) :=
          b.ofLp y * ∏ i : {i // i ∈ S}, Q (k i) (blockSlice y i.1)
        let π (x : BitString (n * m)) : BitString n × BitString m :=
          (blockSummary g x, blockSlice x i₀)
        let Mpq (p q : BitString n × BitString m) : ℝ :=
          (Γf.hadamard (diffMatrix i₀)) p.1 q.1 * (Γg.hadamard (diffMatrix j₀)) p.2 q.2
        have hstep1 : ∑ p, ∑ q,
            (∑ x, if π x = p then fa x else 0) * Mpq p q * (∑ y, if π y = q then fb y else 0) =
            ∑ p, ∑ x, if π x = p then ∑ y, fa x * Mpq p (π y) * fb y else 0 :=
          sum_congr rfl fun p _ ↦ by
            simp only [mul_sum, mul_ite, mul_zero]
            rw [sum_comm]
            trans ∑ y, (∑ x, if π x = p then fa x else 0) * Mpq p (π y) * fb y
            · refine sum_congr rfl fun y _ ↦ ?_
              rw [sum_eq_single (π y) (fun q _ hq ↦ by
                split_ifs with h; exacts [(hq h.symm).elim, rfl]) (by simp)]
              simp
            · simp only [sum_mul, ite_mul, zero_mul]
              rw [sum_comm]
              exact sum_congr rfl fun x _ ↦ by split_ifs <;> simp
        have hstep2 : ∑ p, ∑ x, (if π x = p then ∑ y, fa x * Mpq p (π y) * fb y else 0) =
            ∑ x, ∑ y, fa x * Mpq (π x) (π y) * fb y := by
          rw [sum_comm]
          refine sum_congr rfl fun x _ ↦ ?_
          rw [sum_eq_single (π x) (fun p _ hp ↦ by
            split_ifs with h; exacts [(hp h.symm).elim, rfl]) (by simp)]
          simp
        refine (sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ ?_).trans (hstep1.trans hstep2)
        have hiff (x : BitString (n * m)) (r : BitString n × BitString m) :
            (blockSummary g x = r.1 ∧ blockSlice x i₀ = r.2) ↔ π x = r :=
          (Prod.ext_iff (x := π x) (y := r)).symm
        simp only [hiff, fa, fb, Mpq]
    set M := maxDiffNorm Γf * maxDiffNorm Γg
    rw [hdecomp]
    calc ∑ k : K, ∑ p, ∑ q,
          (projVec a k).ofLp p *
            ((Γf.hadamard (diffMatrix i₀)) p.1 q.1 *
              (Γg.hadamard (diffMatrix j₀)) p.2 q.2) *
            (projVec b k).ofLp q
        ≤ ∑ k : K, M * (‖projVec a k‖ * ‖projVec b k‖) := sum_le_sum fun k _ ↦
          (kronecker_bilinear_le _ _ (projVec a k) (projVec b k)).trans (by
            have hf := norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γf i₀
            have hg := norm_toEuclideanCLM_hadamard_le_maxDiffNorm Γg j₀
            have hprod : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γf.hadamard (diffMatrix i₀))‖ *
                ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γg.hadamard (diffMatrix j₀))‖ ≤ M :=
              mul_le_mul hf hg (norm_nonneg _) (maxDiffNorm_nonneg Γf)
            rw [mul_assoc (‖_‖ * ‖_‖)]
            exact mul_le_mul_of_nonneg_right hprod (by positivity))
      _ = M * ∑ k : K, ‖projVec a k‖ * ‖projVec b k‖ := (mul_sum _ _ _).symm
      _ ≤ M * (√(∑ k : K, ‖projVec a k‖ ^ 2) * √(∑ k : K, ‖projVec b k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
      _ ≤ M * (√(lamg ^ (n - 1)) * √(lamg ^ (n - 1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.sqrt_le_sqrt (hproj_norm a ha))
              (Real.sqrt_le_sqrt (hproj_norm b hb))
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
      _ = M * lamg ^ (n - 1) := by rw [Real.mul_self_sqrt (by positivity)]
  -- Step 5: Combine `‖Γ‖ ≥ lamf * lamg^n` and `maxDiffNorm Γ ≤ mdf * mdg * lamg^(n-1)`.
  have hΓ_md_pos : 0 < maxDiffNorm Γ := lt_of_le_of_ne (maxDiffNorm_nonneg Γ) fun h ↦ by
    have h0 := eq_zero_of_maxDiffNorm_eq_zero hΓ_adv h.symm
    have hpos : 0 < lamf * lamg ^ n := by positivity
    simp [h0] at hΓ_norm
    linarith
  have hpow : lamg ^ n = lamg * lamg ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ r => simp [pow_succ']
  refine (le_trans ?_ (le_generalAdversary hΓ_sym hΓ_adv))
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hmdf_pos hmdg_pos) hΓ_md_pos]
  calc (lamf * lamg) * maxDiffNorm Γ
      ≤ (lamf * lamg) * (maxDiffNorm Γf * maxDiffNorm Γg * lamg ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hΓ_md (by positivity)
    _ = (lamf * lamg ^ n) * (maxDiffNorm Γf * maxDiffNorm Γg) := by rw [hpow]; ring
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ * (maxDiffNorm Γf * maxDiffNorm Γg) :=
        mul_le_mul_of_nonneg_right hΓ_norm (by positivity)

/-- **Supermultiplicativity of `ADV±` under block composition**
: `ADV±(f) · ADV±(g) ≤ ADV±(f • g)`.
-/
theorem mul_generalAdversary_le_composeBool {n m : ℕ} (f : BooleanFunction n)
    (g : BooleanFunction m) :
    generalAdversary (fun _ ↦ True) f * generalAdversary (fun _ ↦ True) g ≤
      generalAdversary (fun _ ↦ True) (composeBool f g) := by
  set C := generalAdversary (fun _ ↦ True) (composeBool f g)
  have hC : 0 ≤ C := generalAdversary_nonneg _ _
  by_cases hg0 : generalAdversary (fun _ ↦ True) g = 0
  · rw [hg0, mul_zero]; exact hC
  have hg_pos : 0 < generalAdversary (fun _ ↦ True) g :=
    lt_of_le_of_ne (generalAdversary_nonneg _ _) (Ne.symm hg0)
  rw [← le_div_iff₀ hg_pos]
  refine (generalAdversary_le_iff (div_nonneg hC hg_pos.le)).2 fun Γf hsymf hΓf ↦ ?_
  by_cases hmf : maxDiffNorm Γf = 0
  · have hz := eq_zero_of_maxDiffNorm_eq_zero hΓf hmf
    rw [hz] at hmf ⊢; rw [hmf, map_zero, norm_zero, mul_zero]
  have hmf_pos : 0 < maxDiffNorm Γf := lt_of_le_of_ne (maxDiffNorm_nonneg Γf) (Ne.symm hmf)
  rw [← div_le_iff₀ hmf_pos]
  set rf := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γf‖ / maxDiffNorm Γf
  by_cases hrf0 : rf = 0
  · rw [hrf0]; exact div_nonneg hC hg_pos.le
  have hrf_pos : 0 < rf := lt_of_le_of_ne (by positivity) (Ne.symm hrf0)
  rw [le_div_iff₀ hg_pos, mul_comm, ← le_div_iff₀ hrf_pos]
  refine (generalAdversary_le_iff (div_nonneg hC hrf_pos.le)).2 fun Γg hsymg hΓg ↦ ?_
  by_cases hmg : maxDiffNorm Γg = 0
  · have hz := eq_zero_of_maxDiffNorm_eq_zero hΓg hmg
    rw [hz] at hmg ⊢; rw [hmg, map_zero, norm_zero, mul_zero]
  have hmg_pos : 0 < maxDiffNorm Γg := lt_of_le_of_ne (maxDiffNorm_nonneg Γg) (Ne.symm hmg)
  rw [← div_le_iff₀ hmg_pos, le_div_iff₀ hrf_pos, mul_comm]
  exact ratio_mul_ratio_le_generalAdversary_composeBool f g hsymf hΓf hsymg hΓg

/-- **Exact composition theorem for the general adversary bound**
: for all total Boolean functions `f : BooleanFunction n` and
`g : BooleanFunction m`, `ADV±(f • g) = ADV±(f) · ADV±(g)`.
-/
theorem generalAdversary_composeBool {n m : ℕ} (f : BooleanFunction n) (g : BooleanFunction m) :
    generalAdversary (fun _ ↦ True) (composeBool f g) =
      generalAdversary (fun _ ↦ True) f * generalAdversary (fun _ ↦ True) g :=
  le_antisymm (generalAdversary_composeBool_le f g) (mul_generalAdversary_le_composeBool f g)

end AdversaryComposition

/-! ### Reichardt's quantum query composition theorem -/

section QueryComposition

/-- **Reichardt's quantum query composition lower bound**:
`Q_2(f) · Q_2(g) ≤ 324 · Q_2(f • g)` for all total Boolean functions `f` and `g`.
-/
theorem boundedQueryComplexity_mul_le_composeBool {n m : ℕ} (f : BooleanFunction n)
    (g : BooleanFunction m) :
    boundedQueryComplexity f * boundedQueryComplexity g ≤
      324 * boundedQueryComplexity (composeBool f g) := by
  have hf := boundedQueryComplexity_le_three_mul_generalAdversary f
  have hg := boundedQueryComplexity_le_three_mul_generalAdversary g
  have hfg := generalAdversary_le_thirty_six_mul_boundedQueryComplexity (composeBool f g)
  rw [generalAdversary_composeBool] at hfg
  have hreal : (boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ) ≤
      324 * (boundedQueryComplexity (composeBool f g) : ℝ) := by
    have hmul : (boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ) ≤
        (3 * generalAdversary (fun _ ↦ True) f) * (3 * generalAdversary (fun _ ↦ True) g) :=
      mul_le_mul hf hg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (generalAdversary_nonneg _ _))
    linarith
  exact_mod_cast hreal

/-- **Reichardt's quantum query composition upper bound**:
`Q_2(f • g) ≤ 3888 · (Q_2(f) · Q_2(g))` for all total Boolean functions `f` and `g`.
-/
theorem boundedQueryComplexity_composeBool_le_mul {n m : ℕ} (f : BooleanFunction n)
    (g : BooleanFunction m) :
    boundedQueryComplexity (composeBool f g) ≤
      3888 * (boundedQueryComplexity f * boundedQueryComplexity g) := by
  have hf := generalAdversary_le_thirty_six_mul_boundedQueryComplexity f
  have hg := generalAdversary_le_thirty_six_mul_boundedQueryComplexity g
  have hfg := boundedQueryComplexity_le_three_mul_generalAdversary (composeBool f g)
  rw [generalAdversary_composeBool] at hfg
  have hreal : (boundedQueryComplexity (composeBool f g) : ℝ) ≤
      3888 * ((boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ)) := by
    have hmul : generalAdversary (fun _ ↦ True) f * generalAdversary (fun _ ↦ True) g ≤
        (36 * (boundedQueryComplexity f : ℝ)) * (36 * (boundedQueryComplexity g : ℝ)) :=
      mul_le_mul hf hg (generalAdversary_nonneg _ _) (by positivity)
    linarith
  exact_mod_cast hreal

/-- **Reichardt's quantum query composition theorem `Q_2(f • g) = Θ(Q_2(f) · Q_2(g))`**
: for all `n m : ℕ` and all total Boolean functions
`f : BooleanFunction n` and `g : BooleanFunction m`,
`(1 / 324) · Q_2(f) · Q_2(g) ≤ Q_2(f • g) ≤ 3888 · Q_2(f) · Q_2(g)`.
-/
theorem boundedQueryComplexity_composeBool_bounds {n m : ℕ} (f : BooleanFunction n)
    (g : BooleanFunction m) :
    (1 / 324 : ℝ) * (boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ) ≤
        (boundedQueryComplexity (composeBool f g) : ℝ) ∧
      (boundedQueryComplexity (composeBool f g) : ℝ) ≤
        3888 * (boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ) := by
  have h1 : (boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ) ≤
      324 * (boundedQueryComplexity (composeBool f g) : ℝ) := by
    exact_mod_cast boundedQueryComplexity_mul_le_composeBool f g
  have h2 : (boundedQueryComplexity (composeBool f g) : ℝ) ≤
      3888 * ((boundedQueryComplexity f : ℝ) * (boundedQueryComplexity g : ℝ)) := by
    exact_mod_cast boundedQueryComplexity_composeBool_le_mul f g
  exact ⟨by linarith, by linarith⟩

end QueryComposition

end Cslib.Quantum
