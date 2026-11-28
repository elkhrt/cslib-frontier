/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.JohnsonLindenstrauss
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.BitString.Rademacher
import CslibFrontier.Probability.KWiseIndependent
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Oblivious Subspace Embeddings and Sketched Least-Squares Regression

This module extends `CslibFrontier.Probability.JohnsonLindenstrauss`
(`Cslib.Probability.signProjection`) with the deterministic and probabilistic core of sketched
least-squares regression:

1. **Subspace embeddings** (`IsSubspaceEmbedding`): `(1 ± ε)` squared-norm preservation on a linear
   subspace `W : Submodule ℝ E`, implying injectivity on `W` whenever `ε < 1`.
2. **Structural sketched least-squares error bound** (`sketched_leastSquares_error_le`): when `S` is
   a `(1/2)`-subspace embedding on `W` with orthonormal basis `bW`, any vector `w_hat ∈ W` whose
   sketched residual is at most that of the true orthogonal projection `w_opt ∈ W` (`b_vec - w_opt`
   orthogonal to `W`) satisfies
   `‖w_hat - b_vec‖ ^ 2 ≤ ‖b_vec - w_opt‖ ^ 2 + 16 * ∑ j, ⟪S (bW j), S (b_vec - w_opt)⟫ ^ 2`.
3. **Second-moment cross-correlation bound for random `±1` sign projections**
   (`expect_sq_inner_signProjection_of_inner_eq_zero`): for orthogonal vectors `u, r`
   (`⟪u, r⟫ = 0`), a `t × ι` uniform random sign projection satisfies
   `𝔼 b, ⟪signProjection b u, signProjection b r⟫ ^ 2 ≤ (3 / t) * ‖u‖ ^ 2 * ‖r‖ ^ 2`.

## Main definitions

* `CslibFrontier.Probability.IsSubspaceEmbedding`: `(1 ± ε)` subspace embedding predicate.

## Main results

* `CslibFrontier.Probability.IsSubspaceEmbedding.injective_domRestrict`: injectivity for `ε < 1`.
* `CslibFrontier.Probability.sketched_leastSquares_error_le`: deterministic structural bound for
  sketched least-squares regression.
* `CslibFrontier.Probability.expect_inner_signProjection`: unbiasedness of inner products under
  random sign projections.
* `CslibFrontier.Probability.expect_sq_inner_signProjection_of_inner_eq_zero`: `O(1 / t)` second
  moment of sketched inner products of orthogonal vectors.
-/

public section

open Finset Real Cslib.BitString Cslib.Probability
open scoped BigOperators RealInnerProductSpace

namespace CslibFrontier.Probability

section SubspaceEmbedding

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear map `S : E →ₗ[ℝ] F` is an `ε`-subspace embedding for `W : Submodule ℝ E` if it
preserves squared Euclidean norms of all vectors in `W` within `1 ± ε`. -/
def IsSubspaceEmbedding (S : E →ₗ[ℝ] F) (W : Submodule ℝ E) (ε : ℝ) : Prop :=
  ∀ u ∈ W, ‖S u‖ ^ 2 ∈ Set.Icc ((1 - ε) * ‖u‖ ^ 2) ((1 + ε) * ‖u‖ ^ 2)

/-- Lower norm bound `(1 - ε) * ‖u‖ ^ 2 ≤ ‖S u‖ ^ 2` for `u ∈ W`. -/
theorem IsSubspaceEmbedding.norm_sq_ge {S : E →ₗ[ℝ] F} {W : Submodule ℝ E} {ε : ℝ}
    (hS : IsSubspaceEmbedding S W ε) {u : E} (hu : u ∈ W) :
    (1 - ε) * ‖u‖ ^ 2 ≤ ‖S u‖ ^ 2 :=
  (hS u hu).1

/-- Upper norm bound `‖S u‖ ^ 2 ≤ (1 + ε) * ‖u‖ ^ 2` for `u ∈ W`. -/
theorem IsSubspaceEmbedding.norm_sq_le {S : E →ₗ[ℝ] F} {W : Submodule ℝ E} {ε : ℝ}
    (hS : IsSubspaceEmbedding S W ε) {u : E} (hu : u ∈ W) :
    ‖S u‖ ^ 2 ≤ (1 + ε) * ‖u‖ ^ 2 :=
  (hS u hu).2

/-- Any `ε`-subspace embedding with `ε < 1` is injective on `W`. -/
theorem IsSubspaceEmbedding.injective_domRestrict {S : E →ₗ[ℝ] F} {W : Submodule ℝ E} {ε : ℝ}
    (hS : IsSubspaceEmbedding S W ε) (hε : ε < 1) :
    Function.Injective (S.domRestrict W) := by
  intro u v huv
  have hdiff : S ((u - v : W) : E) = 0 := by
    simpa only [LinearMap.domRestrict_apply, Submodule.coe_sub, map_sub, sub_eq_zero] using huv
  have hle := hS.norm_sq_ge (u - v : W).2
  rw [hdiff, norm_zero, sq (0 : ℝ), mul_zero] at hle
  have hnorm0 : ‖((u - v : W) : E)‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖((u - v : W) : E)‖]
  have hnorm_eq : ‖((u - v : W) : E)‖ = 0 := by
    nlinarith [sq_nonneg ‖((u - v : W) : E)‖, norm_nonneg ((u - v : W) : E)]
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq))

/-- **Deterministic structural bound for sketched least-squares regression.**
If `S` is a `(1 / 2)`-subspace embedding on `W`, `bW` is an orthonormal basis of `W`,
`b_vec - w_opt` is orthogonal to `W` (`w_opt ∈ W`), and `w_hat ∈ W` has sketched residual
`‖S w_hat - S b_vec‖ ^ 2 ≤ ‖S w_opt - S b_vec‖ ^ 2`, then
`‖w_hat - b_vec‖ ^ 2 ≤ ‖b_vec - w_opt‖ ^ 2 + 16 * ∑ j, ⟪S (bW j), S (b_vec - w_opt)⟫ ^ 2`. -/
theorem sketched_leastSquares_error_le {ι_W : Type*} [Fintype ι_W]
    {S : E →ₗ[ℝ] F} {W : Submodule ℝ E} (hSE : IsSubspaceEmbedding S W (1 / 2))
    (bW : OrthonormalBasis ι_W ℝ W) {b_vec w_opt w_hat : E}
    (hw_opt : w_opt ∈ W) (hw_hat : w_hat ∈ W)
    (horth : ∀ u ∈ W, ⟪u, b_vec - w_opt⟫ = 0)
    (hsketch : ‖S w_hat - S b_vec‖ ^ 2 ≤ ‖S w_opt - S b_vec‖ ^ 2) :
    ‖w_hat - b_vec‖ ^ 2 ≤
      ‖b_vec - w_opt‖ ^ 2 + 16 * ∑ j : ι_W, ⟪S (bW j : E), S (b_vec - w_opt)⟫ ^ 2 := by
  set Δ : E := w_hat - w_opt
  set r : E := b_vec - w_opt
  have hΔW : Δ ∈ W := W.sub_mem hw_hat hw_opt
  have hpyth : ‖w_hat - b_vec‖ ^ 2 = ‖Δ‖ ^ 2 + ‖r‖ ^ 2 := by
    have hrew : w_hat - b_vec = Δ - r := by simp only [Δ, r, sub_sub_sub_cancel_right]
    rw [hrew, norm_sub_sq_real, horth Δ hΔW, mul_zero, sub_zero]
  have hS_ineq : ‖S Δ‖ ^ 2 ≤ 2 * ⟪S Δ, S r⟫ := by
    have h1 : S w_hat - S b_vec = S Δ - S r := by
      simp only [Δ, r, map_sub, sub_sub_sub_cancel_right]
    have h2 : S w_opt - S b_vec = -S r := by
      simp only [r, map_sub, neg_sub]
    rw [h1, h2, norm_neg, norm_sub_sq_real] at hsketch
    linarith
  have hSE_Δ : (1 / 2 : ℝ) * ‖Δ‖ ^ 2 ≤ ‖S Δ‖ ^ 2 := by
    have h := hSE.norm_sq_ge hΔW
    linarith
  have hΔ_le_inner : ‖Δ‖ ^ 2 ≤ 4 * ⟪S Δ, S r⟫ := by linarith
  let ΔW : W := ⟨Δ, hΔW⟩
  have hΔ_decomp : ∑ j : ι_W, ⟪bW j, ΔW⟫ • (bW j : E) = Δ := by
    have h := congrArg W.subtype (bW.sum_repr' ΔW)
    simpa only [map_sum, map_smul, Submodule.coe_subtype] using h
  have hparseval : ∑ j : ι_W, ⟪bW j, ΔW⟫ ^ 2 = ‖Δ‖ ^ 2 :=
    (bW.sum_sq_inner_right ΔW).trans (by rw [← Submodule.norm_coe])
  have hinner_exp : ⟪S Δ, S r⟫ = ∑ j : ι_W, ⟪bW j, ΔW⟫ * ⟪S (bW j : E), S r⟫ := by
    conv_lhs => rw [← hΔ_decomp, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, real_inner_smul_left]
  have hcs : ⟪S Δ, S r⟫ ^ 2 ≤ ‖Δ‖ ^ 2 * ∑ j : ι_W, ⟪S (bW j : E), S r⟫ ^ 2 := by
    rw [hinner_exp, ← hparseval]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j ↦ ⟪bW j, ΔW⟫) (fun j ↦ ⟪S (bW j : E), S r⟫)
  have hsq4 : (‖Δ‖ ^ 2) ^ 2 ≤ 16 * (‖Δ‖ ^ 2 * ∑ j : ι_W, ⟪S (bW j : E), S r⟫ ^ 2) := by
    have h1 : (‖Δ‖ ^ 2) ^ 2 ≤ (4 * ⟪S Δ, S r⟫) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg ‖Δ‖) hΔ_le_inner 2
    nlinarith
  have hΔ_bound : ‖Δ‖ ^ 2 ≤ 16 * ∑ j : ι_W, ⟪S (bW j : E), S r⟫ ^ 2 := by
    by_cases h0 : ‖Δ‖ ^ 2 = 0
    · rw [h0]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    · have hpos : 0 < ‖Δ‖ ^ 2 := lt_of_le_of_ne (sq_nonneg ‖Δ‖) (Ne.symm h0)
      nlinarith
  linarith

end SubspaceEmbedding

section SignProjectionMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma expect_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    (𝔼 x : α, c * f x) = c * (𝔼 x : α, f x) := by
  simp only [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum, mul_div_assoc]

/-- Single-row Rademacher inner-product unbiasedness:
`𝔼 x : ι → Bool, (∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j)) = ∑ i, u i * v i`. -/
private theorem expect_row_mul_signVal (u v : ι → ℝ) :
    𝔼 x : ι → Bool, (∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j)) =
      ∑ i, u i * v i := by
  have hpair (i j : ι) :
      𝔼 x : ι → Bool, signVal (x i) * signVal (x j) = if i = j then 1 else 0 := by
    split_ifs with hij
    · subst hij
      simp only [signVal_mul_self, Fintype.expect_const]
    · rw [Fintype.expect_apply_pair (fun a b : Bool ↦ signVal a * signVal b) hij]
      simp only [expect_const_mul, expect_bool_signVal, mul_zero, Fintype.expect_const]
  have hexp (x : ι → Bool) :
      (∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j)) =
        ∑ i, ∑ j, (u i * v j) * (signVal (x i) * signVal (x j)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [hexp]
  rw [expect_sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [expect_sum_comm]
  simp only [expect_const_mul, hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- Single-row Rademacher cross-product second moment:
`𝔼 x : ι → Bool, ((∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))) ^ 2 ≤
  3 * (∑ i, u i ^ 2) * (∑ j, v j ^ 2)`. -/
private theorem expect_sq_row_mul_signVal_le (u v : ι → ℝ) :
    𝔼 x : ι → Bool, ((∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))) ^ 2 ≤
      3 * (∑ i, u i ^ 2) * (∑ j, v j ^ 2) := by
  set Su : ℝ := ∑ i, u i ^ 2
  set Sv : ℝ := ∑ j, v j ^ 2
  have hSu0 : 0 ≤ Su := Finset.sum_nonneg fun i _ ↦ sq_nonneg (u i)
  have hSv0 : 0 ≤ Sv := Finset.sum_nonneg fun j _ ↦ sq_nonneg (v j)
  rcases hSu0.eq_or_lt with hSu | hSu
  · have hu0 (i : ι) : u i = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 <|
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ sq_nonneg (u k)).1 hSu.symm i (mem_univ i)
    simp only [← hSu, hu0, zero_mul, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Fintype.expect_const, mul_zero, le_refl]
  rcases hSv0.eq_or_lt with hSv | hSv
  · have hv0 (j : ι) : v j = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 <|
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ sq_nonneg (v k)).1 hSv.symm j (mem_univ j)
    simp only [← hSv, hv0, zero_mul, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Fintype.expect_const, mul_zero, le_refl]
  have hpt (x : ι → Bool) :
      2 * Su * Sv * ((∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))) ^ 2 ≤
        Sv ^ 2 * (∑ i, u i * signVal (x i)) ^ 4 + Su ^ 2 * (∑ j, v j * signVal (x j)) ^ 4 := by
    nlinarith [sq_nonneg (Sv * (∑ i, u i * signVal (x i)) ^ 2 -
      Su * (∑ j, v j * signVal (x j)) ^ 2)]
  have hexp_le :
      2 * Su * Sv *
          𝔼 x : ι → Bool, ((∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))) ^ 2 ≤
        6 * Su ^ 2 * Sv ^ 2 := by
    calc 2 * Su * Sv *
          𝔼 x : ι → Bool, ((∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))) ^ 2
        = 𝔼 x : ι → Bool,
            2 * Su * Sv * ((∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))) ^ 2 := by
          rw [← expect_const_mul]
      _ ≤ 𝔼 x : ι → Bool,
            (Sv ^ 2 * (∑ i, u i * signVal (x i)) ^ 4 +
              Su ^ 2 * (∑ j, v j * signVal (x j)) ^ 4) :=
          expect_le_expect fun x _ ↦ hpt x
      _ = Sv ^ 2 * (𝔼 x : ι → Bool, (∑ i, u i * signVal (x i)) ^ 4) +
            Su ^ 2 * (𝔼 x : ι → Bool, (∑ j, v j * signVal (x j)) ^ 4) := by
          rw [expect_add_distrib, expect_const_mul, expect_const_mul]
      _ ≤ Sv ^ 2 * (3 * Su ^ 2) + Su ^ 2 * (3 * Sv ^ 2) := by
          nlinarith [expect_sum_mul_signVal_pow_four_le u, expect_sum_mul_signVal_pow_four_le v,
            sq_nonneg Sv, sq_nonneg Su]
      _ = 6 * Su ^ 2 * Sv ^ 2 := by ring
  have hprod_pos : 0 < Su * Sv := mul_pos hSu hSv
  nlinarith

/-- For `t > 0`, a uniform random sign projection preserves inner products in expectation. -/
theorem expect_inner_signProjection {t : ℕ} (ht : 0 < t) (u v : EuclideanSpace ℝ ι) :
    𝔼 b : Fin t → ι → Bool, ⟪signProjection b u, signProjection b v⟫ = ⟪u, v⟫ := by
  have ht_pos : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  let g : (ι → Bool) → ℝ := fun x ↦ (∑ i, u i * signVal (x i)) * (∑ j, v j * signVal (x j))
  have hinner (b : Fin t → ι → Bool) :
      ⟪signProjection b u, signProjection b v⟫ = (t : ℝ)⁻¹ * ∑ s : Fin t, g (b s) := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [signProjection_apply, RCLike.inner_apply, conj_trivial, g]
    have hsq : (√(t : ℝ))⁻¹ * (√(t : ℝ))⁻¹ = (t : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt ht_pos.le]
    calc ((√(t : ℝ))⁻¹ * ∑ i, v i * signVal (b s i)) *
          ((√(t : ℝ))⁻¹ * ∑ i, u i * signVal (b s i))
        = ((√(t : ℝ))⁻¹ * (√(t : ℝ))⁻¹) *
            ((∑ i, u i * signVal (b s i)) * (∑ j, v j * signVal (b s j))) := by ring
      _ = (t : ℝ)⁻¹ * g (b s) := by rw [hsq]
  have hrow_eq (s : Fin t) : 𝔼 b : Fin t → ι → Bool, g (b s) = 𝔼 x : ι → Bool, g x := by
    have h1 := (isKWiseIndependentHash_id (X := Fin t) (Y := ι → Bool) 1).expect_prod
      (T := {s}) (by simp) (fun _ x ↦ g x)
    simpa only [Finset.prod_singleton, id_eq] using h1
  simp only [hinner, expect_const_mul, expect_sum_comm, hrow_eq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ ht_pos.ne', one_mul]
  simp only [g, expect_row_mul_signVal, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm (u i) (v i)

/-- **Second-moment cross-correlation bound for random sign projections.**
For orthogonal vectors `u, r : EuclideanSpace ℝ ι` (`⟪u, r⟫ = 0`) and any `t : ℕ`,
`𝔼 b : Fin t → ι → Bool, ⟪signProjection b u, signProjection b r⟫ ^ 2 ≤
  (3 / t) * ‖u‖ ^ 2 * ‖r‖ ^ 2`. -/
theorem expect_sq_inner_signProjection_of_inner_eq_zero (t : ℕ)
    {u r : EuclideanSpace ℝ ι} (horth : ⟪u, r⟫ = 0) :
    𝔼 b : Fin t → ι → Bool, ⟪signProjection b u, signProjection b r⟫ ^ 2 ≤
      (3 / (t : ℝ)) * ‖u‖ ^ 2 * ‖r‖ ^ 2 := by
  rcases eq_or_ne t 0 with rfl | ht0
  · have hzero (b : Fin 0 → ι → Bool) : ⟪signProjection b u, signProjection b r⟫ = 0 := by
      simp only [PiLp.inner_apply, Finset.univ_eq_empty, Finset.sum_empty]
    simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Fintype.expect_const, Nat.cast_zero, div_zero, zero_mul, le_refl]
  have ht_pos : (0 : ℝ) < t := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht0)
  let g : (ι → Bool) → ℝ := fun x ↦ (∑ i, u i * signVal (x i)) * (∑ j, r j * signVal (x j))
  have hg_mean : 𝔼 x : ι → Bool, g x = 0 := by
    rw [expect_row_mul_signVal]
    have h0 : ∑ i, r i * u i = 0 := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using horth
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (u i) (r i)
  have hinner_sq (b : Fin t → ι → Bool) :
      ⟪signProjection b u, signProjection b r⟫ ^ 2 =
        ((t : ℝ)⁻¹) ^ 2 * ∑ s₁ : Fin t, ∑ s₂ : Fin t, g (b s₁) * g (b s₂) := by
    have hinner : ⟪signProjection b u, signProjection b r⟫ = (t : ℝ)⁻¹ * ∑ s : Fin t, g (b s) := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      simp only [signProjection_apply, RCLike.inner_apply, conj_trivial, g]
      have hsq : (√(t : ℝ))⁻¹ * (√(t : ℝ))⁻¹ = (t : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt ht_pos.le]
      calc ((√(t : ℝ))⁻¹ * ∑ i, r i * signVal (b s i)) *
            ((√(t : ℝ))⁻¹ * ∑ i, u i * signVal (b s i))
          = ((√(t : ℝ))⁻¹ * (√(t : ℝ))⁻¹) * g (b s) := by ring
        _ = (t : ℝ)⁻¹ * g (b s) := by rw [hsq]
    rw [hinner, mul_pow, sq (∑ s : Fin t, g (b s)), Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun s₁ _ ↦ Finset.mul_sum _ _ _
  have hpair_row (s₁ s₂ : Fin t) :
      𝔼 b : Fin t → ι → Bool, g (b s₁) * g (b s₂) =
        if s₁ = s₂ then 𝔼 x : ι → Bool, (g x) ^ 2 else 0 := by
    split_ifs with hs
    · subst hs
      have h1 := (isKWiseIndependentHash_id (X := Fin t) (Y := ι → Bool) 1).expect_prod
        (T := {s₁}) (by simp) (fun _ x ↦ (g x) ^ 2)
      simpa only [Finset.prod_singleton, id_eq, sq] using h1
    · rw [Fintype.expect_apply_pair (fun x y : ι → Bool ↦ g x * g y) hs]
      simp only [expect_const_mul, hg_mean, mul_zero, Fintype.expect_const]
  simp only [hinner_sq, expect_const_mul, expect_sum_comm, hpair_row, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hrow_ub : 𝔼 x : ι → Bool, (g x) ^ 2 ≤ 3 * ‖u‖ ^ 2 * ‖r‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq u, EuclideanSpace.real_norm_sq_eq r]
    exact expect_sq_row_mul_signVal_le (fun i ↦ u i) (fun j ↦ r j)
  calc ((t : ℝ)⁻¹) ^ 2 * ((t : ℝ) * 𝔼 x : ι → Bool, (g x) ^ 2)
      ≤ ((t : ℝ)⁻¹) ^ 2 * ((t : ℝ) * (3 * ‖u‖ ^ 2 * ‖r‖ ^ 2)) := by
        gcongr
    _ = (3 / (t : ℝ)) * ‖u‖ ^ 2 * ‖r‖ ^ 2 := by
        field_simp

end SignProjectionMoments

end CslibFrontier.Probability
