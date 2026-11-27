/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.QMA

import CslibFrontier.Computability.QueryComplexity.Quantum.Composition
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Marriott–Watrous In-Place QMA Query Amplification

This module proves Marriott–Watrous witness-preserving error reduction for `QMAQueryProtocol`:
given a `q`-query protocol `P` with witness length `w`, completeness `≥ a`, soundness `≤ b`
(`0 ≤ b < a ≤ 1`), and target error parameter `r ≥ 1`, there exists a `QMAQueryProtocol N w` with
the same witness length `w`, completeness and soundness error at most `2^{-r}`, and query
complexity at most `2 * q * (⌈32 * r / (a - b)^2⌉₊ + 1)`.

The proof uses the spectral theorem on `H_x = E^* P_1 E` to decompose the verifier space into
orthogonal 2D alternating-projection blocks `span{e_j^0, w_j^1}`, simulates the alternating
measurements coherently via deferred-measurement CNOTs, and bounds the binomial acceptance tail
via an elementary Hoeffding inequality.

## Main results

* `CslibFrontier.QueryComplexity.marriott_watrous_query_amplification`: witness-preserving QMA query
  error reduction to `2^{-r}` with `2 * P.queries * (⌈32 * r / (a - b)^2⌉₊ + 1)` queries.
-/

public section

open scoped BigOperators
open Finset Matrix Cslib Cslib.BitString Cslib.Quantum

namespace CslibFrontier.QueryComplexity

private noncomputable def mwRunUGo {N w : ℕ} (P : QMAQueryProtocol N w)
    (phaseEquiv : State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work)) :
    ℕ → State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work)
  | 0 => P.unitary 0
  | t + 1 => ((mwRunUGo P phaseEquiv t).trans phaseEquiv).trans (P.unitary (t + 1))

private lemma mwRunUGo_zero {N w : ℕ} (P : QMAQueryProtocol N w)
    (e : State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work)) :
    mwRunUGo P e 0 = P.unitary 0 := rfl

private lemma mwRunUGo_succ {N w : ℕ} (P : QMAQueryProtocol N w)
    (e : State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work)) (t : ℕ) :
    mwRunUGo P e (t + 1) = ((mwRunUGo P e t).trans e).trans (P.unitary (t + 1)) := rfl

private noncomputable def mwApplyRounds {N : ℕ} {W : Type*} [Fintype W] (M : ℕ)
    (roundOp : Fin M → State N W ≃ₗᵢ[ℂ] State N W) : ℕ → State N W → State N W
  | 0, χ => χ
  | k + 1, χ =>
    if hk : k < M then roundOp ⟨k, hk⟩ (mwApplyRounds M roundOp k χ)
    else mwApplyRounds M roundOp k χ

private lemma mwApplyRounds_zero {N : ℕ} {W : Type*} [Fintype W] (M : ℕ)
    (roundOp : Fin M → State N W ≃ₗᵢ[ℂ] State N W) (χ : State N W) :
    mwApplyRounds M roundOp 0 χ = χ := rfl

private lemma mwApplyRounds_succ {N : ℕ} {W : Type*} [Fintype W] (M : ℕ)
    (roundOp : Fin M → State N W ≃ₗᵢ[ℂ] State N W) (k : ℕ) (χ : State N W) :
    mwApplyRounds M roundOp (k + 1) χ =
      if hk : k < M then roundOp ⟨k, hk⟩ (mwApplyRounds M roundOp k χ)
      else mwApplyRounds M roundOp k χ := rfl

private lemma mwApplyRounds_add {N : ℕ} {W : Type*} [Fintype W] (M : ℕ)
    (roundOp : Fin M → State N W ≃ₗᵢ[ℂ] State N W) (m : ℕ) (ξ₁ ξ₂ : State N W) :
    mwApplyRounds M roundOp m (ξ₁ + ξ₂) =
      mwApplyRounds M roundOp m ξ₁ + mwApplyRounds M roundOp m ξ₂ := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [mwApplyRounds_succ]; split_ifs <;> simp [ih]

private lemma mwApplyRounds_smul {N : ℕ} {W : Type*} [Fintype W] (M : ℕ)
    (roundOp : Fin M → State N W ≃ₗᵢ[ℂ] State N W) (m : ℕ) (c : ℂ) (ξ : State N W) :
    mwApplyRounds M roundOp m (c • ξ) = c • mwApplyRounds M roundOp m ξ := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [mwApplyRounds_succ]; split_ifs <;> simp [ih]

/-! ### Elementary Bernoulli Hoeffding bound -/

private lemma bernoulli_tail_upper {M : ℕ} {lam τ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hτ1 : τ ≤ 1) (hgap : lam < τ) :
    ∑ y : BitString M with τ * (M : ℝ) ≤ (weight y : ℝ),
      lam ^ weight y * (1 - lam) ^ (M - weight y) ≤
      Real.exp (-(M : ℝ) * (τ - lam) ^ 2 / 8) := by
  set u : ℝ := (τ - lam) / 4
  have hu0 : 0 < u := by simp only [u]; linarith
  have hu1 : u ≤ 1 / 4 := by simp only [u]; linarith
  have hexp_u : Real.exp u ≤ 1 + u + 2 * u ^ 2 := by
    have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have h2 : (1 - u) * Real.exp u ≤ 1 := by
      calc (1 - u) * Real.exp u ≤ Real.exp (-u) * Real.exp u :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg u)
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith
  have hmgf : 1 - lam + lam * Real.exp u ≤ Real.exp (lam * u + 2 * u ^ 2) := by
    have h1 : 1 - lam + lam * Real.exp u ≤ 1 + (lam * u + 2 * u ^ 2) := by nlinarith
    exact h1.trans (by linarith [Real.add_one_le_exp (lam * u + 2 * u ^ 2)])
  have hstep : Real.exp (-u * τ) * (1 - lam + lam * Real.exp u) ≤
      Real.exp (-(τ - lam) ^ 2 / 8) := by
    calc Real.exp (-u * τ) * (1 - lam + lam * Real.exp u)
        ≤ Real.exp (-u * τ) * Real.exp (lam * u + 2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = Real.exp (-(τ - lam) ^ 2 / 8) := by rw [← Real.exp_add]; congr 1; simp only [u]; ring
  have hmarkov : ∑ y : BitString M with τ * (M : ℝ) ≤ (weight y : ℝ),
      lam ^ weight y * (1 - lam) ^ (M - weight y) ≤
      Real.exp (-u * τ * (M : ℝ)) *
        ∑ y : BitString M,
          Real.exp (u * (weight y : ℝ)) * (lam ^ weight y * (1 - lam) ^ (M - weight y)) := by
    rw [Finset.mul_sum]
    calc ∑ y : BitString M with τ * (M : ℝ) ≤ (weight y : ℝ),
          lam ^ weight y * (1 - lam) ^ (M - weight y)
        ≤ ∑ y : BitString M with τ * (M : ℝ) ≤ (weight y : ℝ),
            Real.exp (-u * τ * (M : ℝ)) *
              (Real.exp (u * (weight y : ℝ)) * (lam ^ weight y * (1 - lam) ^ (M - weight y))) := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hwy : τ * (M : ℝ) ≤ (weight y : ℝ) := (Finset.mem_filter.mp hy).2
          have hexp1 : (1 : ℝ) ≤ Real.exp (-u * τ * (M : ℝ)) * Real.exp (u * (weight y : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
          nlinarith [mul_nonneg (pow_nonneg hlam0 (weight y))
            (pow_nonneg (show 0 ≤ 1 - lam by linarith) (M - weight y))]
      _ ≤ ∑ y : BitString M,
            Real.exp (-u * τ * (M : ℝ)) *
              (Real.exp (u * (weight y : ℝ)) * (lam ^ weight y * (1 - lam) ^ (M - weight y))) := by
          refine Finset.sum_le_univ_sum_of_nonneg fun y => ?_
          exact mul_nonneg (Real.exp_nonneg _)
            (mul_nonneg (Real.exp_nonneg _)
              (mul_nonneg (pow_nonneg hlam0 _) (pow_nonneg (by linarith) _)))
  have hprod : ∑ y : BitString M,
      Real.exp (u * (weight y : ℝ)) * (lam ^ weight y * (1 - lam) ^ (M - weight y)) =
      (1 - lam + lam * Real.exp u) ^ M := by
    have hfactor : ∀ y : BitString M,
        Real.exp (u * (weight y : ℝ)) * (lam ^ weight y * (1 - lam) ^ (M - weight y)) =
        ∏ i : Fin M, (if y i = true then lam * Real.exp u else 1 - lam) := by
      intro y
      have hcard : #{i : Fin M | y i = false} = M - weight y := by
        simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight y
      have hsplit : ∏ i : Fin M, (if y i = true then lam * Real.exp u else 1 - lam) =
          (∏ i ∈ Finset.univ.filter (fun i : Fin M => y i = true), (lam * Real.exp u)) *
          (∏ i ∈ Finset.univ.filter (fun i : Fin M => ¬ y i = true), (1 - lam)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin M => y i = true)]
        congr 1
        · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      have hnot : Finset.univ.filter (fun i : Fin M => ¬ y i = true) =
          Finset.univ.filter (fun i : Fin M => y i = false) := by ext i; simp
      rw [hsplit, hnot, Finset.prod_const, Finset.prod_const, hcard]
      change _ = (lam * Real.exp u) ^ weight y * (1 - lam) ^ (M - weight y)
      rw [mul_pow, ← Real.exp_nat_mul, mul_comm (weight y : ℝ) u]
      ring
    simp_rw [hfactor]
    rw [← Fintype.prod_sum (fun (_ : Fin M) (b : Bool) =>
      if b = true then lam * Real.exp u else 1 - lam)]
    have h2 : ∀ _i : Fin M, ∑ b : Bool, (if b = true then lam * Real.exp u else 1 - lam) =
        1 - lam + lam * Real.exp u := fun _ => by
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]; ring
    rw [Finset.prod_congr rfl fun i _ => h2 i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc ∑ y : BitString M with τ * (M : ℝ) ≤ (weight y : ℝ),
        lam ^ weight y * (1 - lam) ^ (M - weight y)
      ≤ Real.exp (-u * τ * (M : ℝ)) * (1 - lam + lam * Real.exp u) ^ M := by
        rw [← hprod]; exact hmarkov
    _ = (Real.exp (-u * τ) * (1 - lam + lam * Real.exp u)) ^ M := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
    _ ≤ (Real.exp (-(τ - lam) ^ 2 / 8)) ^ M :=
        pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) (by
          have : 0 ≤ lam * Real.exp u := mul_nonneg hlam0 (Real.exp_nonneg _)
          linarith)) hstep M
    _ = Real.exp (-(M : ℝ) * (τ - lam) ^ 2 / 8) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

private lemma bernoulli_tail_lower {M : ℕ} {lam τ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hτ0 : 0 ≤ τ) (hgap : τ < lam) :
    ∑ y : BitString M with (weight y : ℝ) < τ * (M : ℝ),
      lam ^ weight y * (1 - lam) ^ (M - weight y) ≤
      Real.exp (-(M : ℝ) * (lam - τ) ^ 2 / 8) := by
  have hbij : ∑ y : BitString M with (weight y : ℝ) < τ * (M : ℝ),
      lam ^ weight y * (1 - lam) ^ (M - weight y) ≤
      ∑ z : BitString M with (1 - τ) * (M : ℝ) ≤ (weight z : ℝ),
        (1 - lam) ^ weight z * (1 - (1 - lam)) ^ (M - weight z) := by
    let flip : BitString M ≃ BitString M :=
      { toFun := fun y i => !y i
        invFun := fun y i => !y i
        left_inv := fun y => by funext i; simp
        right_inv := fun y => by funext i; simp }
    have hflip : ∀ y : BitString M, weight (flip y) = M - weight y := by
      intro y; simpa [flip, Fintype.card_fin] using weight_not y
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp hy).2⟩)
      (fun y _ _ => mul_nonneg (pow_nonneg hlam0 _) (pow_nonneg (by linarith) _))) (le_of_eq ?_)
    refine Finset.sum_bij (fun y _ => flip y) ?_ ?_ ?_ ?_
    · intro y hy
      have hwy : (weight y : ℝ) ≤ τ * (M : ℝ) := (Finset.mem_filter.mp hy).2
      have hwle : weight y ≤ M := by simpa [Fintype.card_fin] using weight_le y
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hflip, Nat.cast_sub hwle]
      linarith
    · intro a _ b _ h; exact flip.injective h
    · intro z hz
      refine ⟨flip z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have hwz : (1 - τ) * (M : ℝ) ≤ (weight z : ℝ) := (Finset.mem_filter.mp hz).2
        have hwle : weight z ≤ M := by simpa [Fintype.card_fin] using weight_le z
        rw [hflip, Nat.cast_sub hwle]; linarith
      · funext i; simp [flip]
    · intro y _
      have hwle : weight y ≤ M := by simpa [Fintype.card_fin] using weight_le y
      rw [hflip, Nat.sub_sub_self hwle, sub_sub_cancel, mul_comm]
  have hup := bernoulli_tail_upper (M := M) (lam := 1 - lam) (τ := 1 - τ)
    (by linarith) (by linarith) (by linarith) (by linarith)
  exact hbij.trans (hup.trans_eq (by congr 1; ring))

/-! ### Marriott–Watrous in-place amplification -/

private lemma mw_bernoulli_conclude {N w K r : ℕ} {a b τ : ℝ}
    (P P' : QMAQueryProtocol N w) {f : BooleanFunction N}
    (hb0 : 0 ≤ b) (hba : b < a) (ha1 : a ≤ 1) (hτ : τ = (a + b) / 2)
    (hK_ge : 32 * (r : ℝ) / (a - b) ^ 2 ≤ (K : ℝ))
    (hcomp : ∀ x, f x = true →
      ∃ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 ∧ a ≤ P.acceptProb x ψ)
    (hsound : ∀ x, f x = false →
      ∀ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 → P.acceptProb x ψ ≤ b)
    (hprob_formula : ∀ x : BitString N,
      ∃ (v : OrthonormalBasis (BitString w) ℂ (EuclideanSpace ℂ (BitString w)))
        (lam : BitString w → ℝ),
        (∀ j, lam j = P.acceptProb x (v j)) ∧
        (∀ ψ : EuclideanSpace ℂ (BitString w),
          P.acceptProb x ψ = ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 * lam j) ∧
        (∀ ψ : EuclideanSpace ℂ (BitString w),
          P'.acceptProb x ψ =
            ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 *
              ∑ y : BitString K with τ * (K : ℝ) ≤ (weight y : ℝ),
                (lam j) ^ weight y * (1 - lam j) ^ (K - weight y))) :
    P'.Computes f ((2 : ℝ) ^ (-(r : ℤ))) ((2 : ℝ) ^ (-(r : ℤ))) := by
  have hexp_le : Real.exp (-(K : ℝ) * ((a - b) / 2) ^ 2 / 8) ≤ (2 : ℝ) ^ (-(r : ℤ)) := by
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hexp_arg : (r : ℝ) * Real.log 2 ≤ (K : ℝ) * ((a - b) / 2) ^ 2 / 8 := by
      have h1 : (r : ℝ) ≤ (K : ℝ) * ((a - b) / 2) ^ 2 / 8 := by
        have hpos : 0 < (a - b) ^ 2 := sq_pos_of_pos (by linarith)
        have hmul := mul_le_mul_of_nonneg_right hK_ge hpos.le
        rw [div_mul_cancel₀ _ hpos.ne'] at hmul
        linarith
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    rw [_root_.zpow_neg, zpow_natCast, ← Real.rpow_natCast 2 r,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  constructor
  · intro x hfx
    obtain ⟨ψ₀, hψ₀, hacc₀⟩ := hcomp x hfx
    obtain ⟨v, lam, hlam, hspec, hform⟩ := hprob_formula x
    have hex_j : ∃ j₀ : BitString w, a ≤ lam j₀ := by
      by_contra hall
      push Not at hall
      have hsum_norm : ∑ j : BitString w, ‖inner ℂ (v j) ψ₀‖ ^ 2 = 1 := by
        have := v.sum_sq_norm_inner_right ψ₀
        rwa [hψ₀, one_pow] at this
      have hlt_a : ∑ j : BitString w, ‖inner ℂ (v j) ψ₀‖ ^ 2 * lam j < a := by
        have hstrict : ∃ j : BitString w, ‖inner ℂ (v j) ψ₀‖ ^ 2 > 0 := by
          by_contra h0; push Not at h0
          have : ∑ j : BitString w, ‖inner ℂ (v j) ψ₀‖ ^ 2 = 0 :=
            Finset.sum_eq_zero fun j _ => le_antisymm (h0 j) (sq_nonneg _)
          linarith
        obtain ⟨j₁, hj₁⟩ := hstrict
        calc ∑ j : BitString w, ‖inner ℂ (v j) ψ₀‖ ^ 2 * lam j
            < ∑ j : BitString w, ‖inner ℂ (v j) ψ₀‖ ^ 2 * a := by
              refine Finset.sum_lt_sum
                (fun j _ => mul_le_mul_of_nonneg_left (le_of_lt (hall j)) (sq_nonneg _))
                ⟨j₁, Finset.mem_univ _, mul_lt_mul_of_pos_left (hall j₁) hj₁⟩
          _ = a := by rw [← Finset.sum_mul, hsum_norm, one_mul]
      rw [← hspec ψ₀] at hlt_a
      linarith
    obtain ⟨j₀, hj₀⟩ := hex_j
    refine ⟨v j₀, v.orthonormal.1 j₀, ?_⟩
    rw [hform (v j₀)]
    have hdiag : ∑ j : BitString w, ‖inner ℂ (v j) (v j₀)‖ ^ 2 *
        (∑ y : BitString K with τ * (K : ℝ) ≤ (weight y : ℝ),
          (lam j) ^ weight y * (1 - lam j) ^ (K - weight y)) =
        ∑ y : BitString K with τ * (K : ℝ) ≤ (weight y : ℝ),
          (lam j₀) ^ weight y * (1 - lam j₀) ^ (K - weight y) := by
      rw [Finset.sum_eq_single j₀]
      · simp [v.orthonormal.1 j₀]
      · intro j _ hjj₀; simp [v.orthonormal.2 hjj₀]
      · simp
    rw [hdiag]
    have htot1 : ∑ y : BitString K, (lam j₀) ^ weight y * (1 - lam j₀) ^ (K - weight y) = 1 := by
      have hfac : ∀ y : BitString K, (lam j₀) ^ weight y * (1 - lam j₀) ^ (K - weight y) =
          ∏ i : Fin K, (if y i then lam j₀ else 1 - lam j₀) := by
        intro y
        have hcard : #{i : Fin K | y i = false} = K - weight y := by
          simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight y
        have hsplit := (Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun i : Fin K => y i = true) (fun i => if y i then lam j₀ else 1 - lam j₀)).symm
        have hnot : Finset.univ.filter (fun i : Fin K => ¬ y i = true) =
            Finset.univ.filter (fun i : Fin K => y i = false) := by ext i; simp
        rw [hsplit]
        have hp1 : ∏ i ∈ Finset.univ.filter (fun i : Fin K => y i = true),
            (if y i then lam j₀ else 1 - lam j₀) = (lam j₀) ^ weight y := by
          calc ∏ i ∈ Finset.univ.filter (fun i : Fin K => y i = true),
                (if y i then lam j₀ else 1 - lam j₀)
              = ∏ _i ∈ Finset.univ.filter (fun i : Fin K => y i = true), lam j₀ :=
                Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
            _ = (lam j₀) ^ weight y := by rw [Finset.prod_const]; rfl
        have hp2 : ∏ i ∈ Finset.univ.filter (fun i : Fin K => ¬ y i = true),
            (if y i then lam j₀ else 1 - lam j₀) = (1 - lam j₀) ^ (K - weight y) := by
          calc ∏ i ∈ Finset.univ.filter (fun i : Fin K => ¬ y i = true),
                (if y i then lam j₀ else 1 - lam j₀)
              = ∏ _i ∈ Finset.univ.filter (fun i : Fin K => y i = false), (1 - lam j₀) := by
                rw [hnot]
                exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
            _ = (1 - lam j₀) ^ (K - weight y) := by rw [Finset.prod_const, hcard]
        rw [hp1, hp2]
      simp_rw [hfac]
      rw [← Fintype.prod_sum (fun (_ : Fin K) (b : Bool) => if b then lam j₀ else 1 - lam j₀)]
      simp
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun y : BitString K => τ * (K : ℝ) ≤ (weight y : ℝ))
      (fun y => (lam j₀) ^ weight y * (1 - lam j₀) ^ (K - weight y))
    rw [htot1] at hpart
    have hlow := bernoulli_tail_lower (M := K) (lam := lam j₀) (τ := τ) (by linarith)
      (by rw [hlam]; exact P.acceptProb_le_one x (v.orthonormal.1 j₀))
      (by rw [hτ]; linarith) (by rw [hτ]; linarith)
    have hnot_eq : (Finset.univ.filter fun y : BitString K => ¬ τ * (K : ℝ) ≤ (weight y : ℝ)) =
        (Finset.univ.filter fun y : BitString K => (weight y : ℝ) < τ * (K : ℝ)) := by ext y; simp
    rw [hnot_eq] at hpart
    have hgap_le : Real.exp (-(K : ℝ) * (lam j₀ - τ) ^ 2 / 8) ≤
        Real.exp (-(K : ℝ) * ((a - b) / 2) ^ 2 / 8) := by
      refine Real.exp_le_exp.mpr ?_
      have hsq : ((a - b) / 2) ^ 2 ≤ (lam j₀ - τ) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by rw [hτ]; linarith) 2
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    linarith
  · intro x hfx ψ hψ
    obtain ⟨v, lam, hlam, _, hform⟩ := hprob_formula x
    rw [hform ψ]
    have hsum_norm : ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 = 1 := by
      have := v.sum_sq_norm_inner_right ψ
      rwa [hψ, one_pow] at this
    calc ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 *
          (∑ y : BitString K with τ * (K : ℝ) ≤ (weight y : ℝ),
            (lam j) ^ weight y * (1 - lam j) ^ (K - weight y))
        ≤ ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 * ((2 : ℝ) ^ (-(r : ℤ))) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hlj : lam j ≤ b := by rw [hlam]; exact hsound x hfx (v j) (v.orthonormal.1 j)
          have hup := bernoulli_tail_upper (M := K) (lam := lam j) (τ := τ)
            (by rw [hlam]; exact P.acceptProb_nonneg x (v j))
            (by linarith) (by rw [hτ]; linarith) (by rw [hτ]; linarith)
          have hgap_le : Real.exp (-(K : ℝ) * (τ - lam j) ^ 2 / 8) ≤
              Real.exp (-(K : ℝ) * ((a - b) / 2) ^ 2 / 8) := by
            refine Real.exp_le_exp.mpr ?_
            have hsq : ((a - b) / 2) ^ 2 ≤ (τ - lam j) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (by rw [hτ]; linarith) 2
            nlinarith [Nat.cast_nonneg (α := ℝ) K]
          exact (hup.trans hgap_le).trans hexp_le
      _ = (2 : ℝ) ^ (-(r : ℤ)) := by rw [← Finset.sum_mul, hsum_norm, one_mul]

private def mwEqBits (K : ℕ) (z : BitString K) : BitString K := fun idx =>
  if h : idx.1 = 0 then z idx == true else z idx == z ⟨idx.1 - 1, by omega⟩

private lemma mwEqBits_bijective (K : ℕ) : Function.Bijective (mwEqBits K) := by
  refine Finite.injective_iff_bijective.mp fun z₁ z₂ h => funext fun i => ?_
  have hval : ∀ (n : ℕ) (hn : n < K), z₁ ⟨n, hn⟩ = z₂ ⟨n, hn⟩ := fun n => by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      have hi := congr_fun h ⟨n, hn⟩
      simp only [mwEqBits] at hi
      by_cases h0 : n = 0
      · subst h0; simp only [↓reduceDIte] at hi
        cases h1 : z₁ ⟨0, hn⟩ <;> cases h2 : z₂ ⟨0, hn⟩ <;>
          simp only [h1, h2] at hi <;> first | rfl | exact absurd hi (by decide)
      · simp only [h0, ↓reduceDIte] at hi
        rw [ih (n - 1) (by omega) (by omega)] at hi
        cases h1 : z₁ ⟨n, hn⟩ <;> cases h2 : z₂ ⟨n, hn⟩ <;> cases h3 : z₂ ⟨n - 1, by omega⟩ <;>
          simp only [h1, h2, h3] at hi <;> first | rfl | exact absurd hi (by decide)
  exact hval i.1 i.2

private lemma mw_two_dim_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P0 P1 : E →ₗ[ℂ] E) (e0 w1 : E) (lam : ℝ) (a : ℂ) (bp b0 b1 : Bool) (prevProd : ℝ)
    (hP0_e0 : P0 e0 = e0) (hP0_w1 : P0 w1 = 0) (hP0_P1 : P0 (P1 e0) = (lam : ℂ) • e0)
    (hw1_def : w1 = P1 e0 - (lam : ℂ) • e0)
    (hP1_w1' : P1 w1 = ((lam * (1 - lam) : ℝ) : ℂ) • e0 + (1 - (lam : ℂ)) • w1)
    (hnorm_e0 : ‖e0‖ ^ 2 = 1) (hnorm_w1 : ‖w1‖ ^ 2 = lam * (1 - lam))
    (ha_sq : ‖a‖ ^ 2 * (if bp then 1 else lam * (1 - lam)) = prevProd) :
    ∃ a' : ℂ,
      (if b1 then P0 else LinearMap.id - P0)
        ((if b0 then P1 else LinearMap.id - P1) (a • (if bp then e0 else w1))) =
        a' • (if b1 then e0 else w1) ∧
      ‖(if b1 then P0 else LinearMap.id - P0)
        ((if b0 then P1 else LinearMap.id - P1) (a • (if bp then e0 else w1)))‖ ^ 2 =
        prevProd * (if (b0 == bp) then lam else 1 - lam) *
          (if (b1 == b0) then lam else 1 - lam) := by
  have hcase' : ∀ (c : ℂ),
      (if b1 then P0 else LinearMap.id - P0)
        ((if b0 then P1 else LinearMap.id - P1) (a • (if bp then e0 else w1))) =
        c • (if b1 then e0 else w1) →
      ‖c‖ ^ 2 * ‖if b1 then e0 else w1‖ ^ 2 =
        prevProd * (if (b0 == bp) then lam else 1 - lam) * (if (b1 == b0) then lam else 1 - lam) →
      ∃ a' : ℂ,
        (if b1 then P0 else LinearMap.id - P0)
          ((if b0 then P1 else LinearMap.id - P1) (a • (if bp then e0 else w1))) =
          a' • (if b1 then e0 else w1) ∧
        ‖(if b1 then P0 else LinearMap.id - P0)
          ((if b0 then P1 else LinearMap.id - P1) (a • (if bp then e0 else w1)))‖ ^ 2 =
          prevProd * (if (b0 == bp) then lam else 1 - lam) *
            (if (b1 == b0) then lam else 1 - lam) :=
    fun c hvec hnorm => ⟨c, hvec, by rw [hvec, norm_smul, mul_pow, hnorm]⟩
  have h1m : ‖(1 : ℂ) - (lam : ℂ)‖ ^ 2 = (1 - lam) ^ 2 := by
    rw [show (1 : ℂ) - (lam : ℂ) = ((1 - lam : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnsq (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have htf : (true == false) = false := rfl
  have hft : (false == true) = false := rfl
  cases bp <;> cases b0 <;> cases b1
  · refine hcase' (a * (lam : ℂ)) ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, hP1_w1', smul_sub, smul_add, map_sub, map_add, hP0_e0, hP0_w1]; module
    · simp only [Bool.false_eq_true, ↓reduceIte, hnorm_w1, norm_mul, mul_pow, hnsq,
        beq_self_eq_true]
      simp only [Bool.false_eq_true, ↓reduceIte] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' (-(a * ((lam * (1 - lam) : ℝ) : ℂ))) ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, hP1_w1', map_sub, map_add, hP0_e0, hP0_w1]; module
    · simp only [Bool.false_eq_true, ↓reduceIte, hnorm_e0, mul_one, norm_neg, norm_mul, mul_pow,
        hnsq, beq_self_eq_true, htf]
      simp only [Bool.false_eq_true, ↓reduceIte] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' (a * (1 - (lam : ℂ))) ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, hP1_w1', map_add, hP0_e0, hP0_w1]; module
    · simp only [Bool.false_eq_true, ↓reduceIte, hnorm_w1, norm_mul, mul_pow, h1m, htf, hft]
      simp only [Bool.false_eq_true, ↓reduceIte] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' (a * ((lam * (1 - lam) : ℝ) : ℂ)) ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, map_smul, hP1_w1', map_add, hP0_e0, hP0_w1]; module
    · simp only [Bool.false_eq_true, ↓reduceIte, hnorm_e0, mul_one, norm_mul, mul_pow, hnsq,
        beq_self_eq_true, htf]
      simp only [Bool.false_eq_true, ↓reduceIte] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' (-a) ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, map_sub, hP0_e0, hP0_P1]; rw [hw1_def]; module
    · simp only [Bool.false_eq_true, ↓reduceIte, norm_neg, hnorm_w1, beq_self_eq_true, hft]
      simp only [↓reduceIte, mul_one] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' (a * (1 - (lam : ℂ))) ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, map_sub, hP0_e0, hP0_P1]; module
    · simp only [Bool.false_eq_true, ↓reduceIte, hnorm_e0, mul_one, norm_mul, mul_pow, h1m,
        hft, htf]
      simp only [↓reduceIte, mul_one] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' a ?_ ?_
    · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.sub_apply, LinearMap.id_apply,
        map_smul, hP0_P1, hw1_def]
    · simp only [Bool.false_eq_true, ↓reduceIte, hnorm_w1, beq_self_eq_true, hft]
      simp only [↓reduceIte, mul_one] at ha_sq; rw [← ha_sq]; ring
  · refine hcase' (a * (lam : ℂ)) ?_ ?_
    · simp only [↓reduceIte, map_smul, hP0_P1]; module
    · simp only [↓reduceIte, hnorm_e0, mul_one, norm_mul, mul_pow, hnsq, beq_self_eq_true]
      simp only [↓reduceIte, mul_one] at ha_sq; rw [← ha_sq]; ring

/-- **Marriott–Watrous in-place QMA query amplification**:
given a `q`-query protocol `P` with witness length `w`, completeness `≥ a`, soundness `≤ b`
(`0 ≤ b < a ≤ 1`), and any target error parameter `r : ℕ`, there exists a `QMAQueryProtocol N w`
with the **same** witness length `w`, completeness and soundness error at most `2^{-r}`, and
query complexity at most `2 * P.queries * (⌈32 * r / (a - b)^2⌉₊ + 1)`. -/
theorem marriott_watrous_query_amplification {N w : ℕ} (P : QMAQueryProtocol N w)
    {f : BooleanFunction N} {a b : ℝ} (hb0 : 0 ≤ b) (hba : b < a) (ha1 : a ≤ 1)
    (hcomp : ∀ x, f x = true →
      ∃ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 ∧ a ≤ P.acceptProb x ψ)
    (hsound : ∀ x, f x = false →
      ∀ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 → P.acceptProb x ψ ≤ b)
    (r : ℕ) :
    ∃ P' : QMAQueryProtocol N w,
      P'.Computes f ((2 : ℝ) ^ (-(r : ℤ))) ((2 : ℝ) ^ (-(r : ℤ))) ∧
      P'.queries ≤ 2 * P.queries * (⌈32 * (r : ℝ) / (a - b) ^ 2⌉₊ + 1) := by
  classical
  set M : ℕ := ⌈32 * (r : ℝ) / (a - b) ^ 2⌉₊ + 1
  have hM_pos : 1 ≤ M := by omega
  set K : ℕ := 2 * M
  have hK_ge : (32 * (r : ℝ) / (a - b) ^ 2) ≤ (K : ℝ) := by
    have hc : 32 * (r : ℝ) / (a - b) ^ 2 ≤ (⌈32 * (r : ℝ) / (a - b) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have hM1 : (⌈32 * (r : ℝ) / (a - b) ^ 2⌉₊ : ℝ) ≤ (M : ℝ) := by
      simp only [M]; push_cast; linarith
    have hMK : (M : ℝ) ≤ (K : ℝ) := by simp only [K]; push_cast; linarith
    linarith
  set τ : ℝ := (a + b) / 2
  let cnotAccEquiv (idx : Fin K) :
      Equiv.Perm (Fin N × Bool × (BitString w × (P.Work × BitString K))) :=
    { toFun := fun p =>
        if (p.1, p.2.1, (p.2.2.1, p.2.2.2.1)) ∈ P.accept then
          (p.1, p.2.1, (p.2.2.1, (p.2.2.2.1, Function.update p.2.2.2.2 idx (!p.2.2.2.2 idx))))
        else p
      invFun := fun p =>
        if (p.1, p.2.1, (p.2.2.1, p.2.2.2.1)) ∈ P.accept then
          (p.1, p.2.1, (p.2.2.1, (p.2.2.2.1, Function.update p.2.2.2.2 idx (!p.2.2.2.2 idx))))
        else p
      left_inv := fun p => by
        dsimp only
        split_ifs with h
        · simp [Function.update_idem]
        · rfl
      right_inv := fun p => by
        dsimp only
        split_ifs with h
        · simp [Function.update_idem]
        · rfl }
  let cnotAcc (idx : Fin K) :
      State N (BitString w × (P.Work × BitString K)) ≃ₗᵢ[ℂ]
      State N (BitString w × (P.Work × BitString K)) :=
    permute (cnotAccEquiv idx)
  let cnotInitEquiv (idx : Fin K) :
      Equiv.Perm (Fin N × Bool × (BitString w × (P.Work × BitString K))) :=
    { toFun := fun p =>
        if (p.1, p.2.1, p.2.2.2.1) = P.initWork then
          (p.1, p.2.1, (p.2.2.1, (p.2.2.2.1, Function.update p.2.2.2.2 idx (!p.2.2.2.2 idx))))
        else p
      invFun := fun p =>
        if (p.1, p.2.1, p.2.2.2.1) = P.initWork then
          (p.1, p.2.1, (p.2.2.1, (p.2.2.2.1, Function.update p.2.2.2.2 idx (!p.2.2.2.2 idx))))
        else p
      left_inv := fun p => by
        dsimp only
        split_ifs with h
        · simp [Function.update_idem]
        · rfl
      right_inv := fun p => by
        dsimp only
        split_ifs with h
        · simp [Function.update_idem]
        · rfl }
  let cnotInit (idx : Fin K) :
      State N (BitString w × (P.Work × BitString K)) ≃ₗᵢ[ℂ]
      State N (BitString w × (P.Work × BitString K)) :=
    permute (cnotInitEquiv idx)
  let liftK (V : State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work)) :
      State N (BitString w × (P.Work × BitString K)) ≃ₗᵢ[ℂ]
      State N (BitString w × (P.Work × BitString K)) :=
    let e : (Fin N × Bool × (BitString w × (P.Work × BitString K))) ≃
        BitString K × (Fin N × Bool × (BitString w × P.Work)) :=
      { toFun := fun p => (p.2.2.2.2, (p.1, p.2.1, (p.2.2.1, p.2.2.2.1)))
        invFun := fun q => (q.2.1, q.2.2.1, (q.2.2.2.1, (q.2.2.2.2, q.1)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let toF : State N (BitString w × (P.Work × BitString K)) →
        State N (BitString w × (P.Work × BitString K)) := fun ψ =>
      WithLp.toLp 2 fun p =>
        (V (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q)))).ofLp
          (p.1, p.2.1, (p.2.2.1, p.2.2.2.1))
    let invF : State N (BitString w × (P.Work × BitString K)) →
        State N (BitString w × (P.Work × BitString K)) := fun ψ =>
      WithLp.toLp 2 fun p =>
        (V.symm (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q)))).ofLp
          (p.1, p.2.1, (p.2.2.1, p.2.2.2.1))
    { toFun := toF
      invFun := invF
      map_add' := fun ψ φ => by
        ext p
        have h : (WithLp.toLp 2 fun q => (ψ + φ).ofLp (e.symm (p.2.2.2.2, q))) =
            (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q))) +
            (WithLp.toLp 2 fun q => φ.ofLp (e.symm (p.2.2.2.2, q))) := rfl
        dsimp only [toF]; rw [h, map_add]; rfl
      map_smul' := fun c ψ => by
        ext p
        have h : (WithLp.toLp 2 fun q => (c • ψ).ofLp (e.symm (p.2.2.2.2, q))) =
            c • (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q))) := rfl
        dsimp only [toF]; rw [h, map_smul]; rfl
      left_inv := fun ψ => by
        ext p
        have h : (WithLp.toLp 2 fun q => (toF ψ).ofLp (e.symm (p.2.2.2.2, q))) =
            V (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q))) := by ext q; rfl
        simp only [invF, h, LinearIsometryEquiv.symm_apply_apply]; rfl
      right_inv := fun ψ => by
        ext p
        have h : (WithLp.toLp 2 fun q => (invF ψ).ofLp (e.symm (p.2.2.2.2, q))) =
            V.symm (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q))) := by ext q; rfl
        simp only [toF, h, LinearIsometryEquiv.apply_symm_apply]; rfl
      norm_map' := fun ψ => by
        have hsq : ‖toF ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
          dsimp only [toF]
          rw [Fintype.sum_equiv e
            (fun p => ‖(V (WithLp.toLp 2 fun q => ψ.ofLp (e.symm (p.2.2.2.2, q)))).ofLp
              (p.1, p.2.1, (p.2.2.1, p.2.2.2.1))‖ ^ 2)
            (fun q => ‖(V (WithLp.toLp 2 fun s => ψ.ofLp (e.symm (q.1, s)))).ofLp q.2‖ ^ 2)
            (fun _ => rfl)]
          rw [Fintype.sum_equiv e (fun p => ‖ψ.ofLp p‖ ^ 2) (fun q => ‖ψ.ofLp (e.symm q)‖ ^ 2)
            (fun p => by simp)]
          conv_lhs => rw [Fintype.sum_prod_type]
          conv_rhs => rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun z _ => ?_
          dsimp only
          rw [← EuclideanSpace.norm_sq_eq, V.norm_map, EuclideanSpace.norm_sq_eq]
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }
  let eqBits := mwEqBits K
  let roundZero : State N (BitString w × (P.Work × BitString K)) ≃ₗᵢ[ℂ]
      State N (BitString w × (P.Work × BitString K)) :=
    (List.ofFn fun k : Fin M =>
      (((liftK (P.unitary 0)).trans (cnotAcc ⟨2 * k.1, by omega⟩)).trans
        (liftK (P.unitary 0).symm)).trans (cnotInit ⟨2 * k.1 + 1, by omega⟩)).foldl
      (fun acc step => acc.trans step) (LinearIsometryEquiv.refl ℂ _)
  let q := P.queries
  let stepU (t : ℕ) : State N (BitString w × (P.Work × BitString K)) ≃ₗᵢ[ℂ]
      State N (BitString w × (P.Work × BitString K)) :=
    if q = 0 then
      if t = 0 then roundZero else LinearIsometryEquiv.refl ℂ _
    else if t = 0 then
      liftK (P.unitary 0)
    else if t < 2 * M * q then
      let rem := t % (2 * q)
      let k := t / (2 * q)
      if hrem : rem < q then
        if rem = 0 then
          if hk : 1 ≤ k ∧ k < M then
            ((liftK (P.unitary 0).symm).trans (cnotInit ⟨2 * (k - 1) + 1, by omega⟩)).trans
              (liftK (P.unitary 0))
          else LinearIsometryEquiv.refl ℂ _
        else
          liftK (P.unitary rem)
      else if rem = q then
        if hk : k < M then
          ((liftK (P.unitary q)).trans (cnotAcc ⟨2 * k, by omega⟩)).trans
            (liftK (P.unitary q).symm)
        else LinearIsometryEquiv.refl ℂ _
      else
        liftK (P.unitary (2 * q - rem)).symm
    else if t = 2 * M * q then
      (liftK (P.unitary 0).symm).trans (cnotInit ⟨2 * M - 1, by omega⟩)
    else
      LinearIsometryEquiv.refl ℂ _
  let P' : QMAQueryProtocol N w :=
    { Work := P.Work × BitString K
      queries := 2 * M * q
      unitary := stepU
      initWork := (P.initWork.1, P.initWork.2.1, (P.initWork.2.2, fun _ => false))
      accept := Finset.univ.filter fun p => τ * (K : ℝ) ≤ (weight (eqBits p.2.2.2.2) : ℝ) }
  refine ⟨P', ?_, by simp [P', M, q]; ring_nf; rfl⟩
  let phaseEquiv (x : BitString N) :
      State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work) :=
    { toFun := phaseOracle x
      invFun := phaseOracle x
      map_add' := map_add (phaseOracle x)
      map_smul' := map_smul (phaseOracle x)
      left_inv := fun χ => by
        ext p; simp only [phaseOracle_apply, ← mul_assoc]; split_ifs <;> simp
      right_inv := fun χ => by
        ext p; simp only [phaseOracle_apply, ← mul_assoc]; split_ifs <;> simp
      norm_map' := norm_phaseOracle x }
  let runUGo (x : BitString N) := mwRunUGo P (phaseEquiv x)
  let runU (x : BitString N) :
      State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work) :=
    runUGo x q
  have hrunU_eq : ∀ (x : BitString N) (χ : State N (BitString w × P.Work)),
      runU x χ = Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry) χ x q := by
    intro x χ
    have hgo : ∀ (t : ℕ),
        runUGo x t χ = Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry) χ x t := by
      intro t; induction t with
      | zero => rw [show runUGo x 0 = P.unitary 0 from mwRunUGo_zero P (phaseEquiv x)]; rfl
      | succ t ih =>
        rw [show runUGo x (t + 1) = ((runUGo x t).trans (phaseEquiv x)).trans (P.unitary (t + 1))
          from mwRunUGo_succ P (phaseEquiv x) t]
        simp only [LinearIsometryEquiv.trans_apply, Cslib.Quantum.run,
          LinearIsometryEquiv.coe_toLinearIsometry]
        rw [ih]; rfl
    exact hgo q
  let roundOp (x : BitString N) (k : Fin M) :
      State N (BitString w × (P.Work × BitString K)) ≃ₗᵢ[ℂ]
      State N (BitString w × (P.Work × BitString K)) :=
    (((liftK (runU x)).trans (cnotAcc ⟨2 * k.1, by omega⟩)).trans
      (liftK (runU x).symm)).trans (cnotInit ⟨2 * k.1 + 1, by omega⟩)
  let applyRounds (x : BitString N) := mwApplyRounds M (roundOp x)
  have hcircuit : ∀ (x : BitString N) (ψ : EuclideanSpace ℂ (BitString w)),
      P'.runState x ψ = applyRounds x M (P'.embedWitness ψ) := by
    intro x ψ
    have hlift_oracle : ∀ (ξ : State N (BitString w × (P.Work × BitString K))),
        phaseOracle x ξ = liftK (phaseEquiv x) ξ := fun _ => by ext p; rfl
    have hlift_trans : ∀ (V W : State N (BitString w × P.Work) ≃ₗᵢ[ℂ]
          State N (BitString w × P.Work))
        (ξ : State N (BitString w × (P.Work × BitString K))),
        liftK (V.trans W) ξ = liftK W (liftK V ξ) := by
      intro V W ξ; ext p
      have h : (WithLp.toLp 2 fun q =>
            (liftK V ξ).ofLp (q.1, q.2.1, (q.2.2.1, (q.2.2.2, p.2.2.2.2)))) =
          V (WithLp.toLp 2 fun q =>
            ξ.ofLp (q.1, q.2.1, (q.2.2.1, (q.2.2.2, p.2.2.2.2)))) := by
        ext q; rfl
      exact (congrArg (fun v => (W v).ofLp (p.1, p.2.1, (p.2.2.1, p.2.2.2.1))) h).symm
    have hlift_runU : ∀ (ξ : State N (BitString w × (P.Work × BitString K))),
        liftK (runU x) ξ =
          Cslib.Quantum.run (fun s => (liftK (P.unitary s)).toLinearIsometry) ξ x q := by
      intro ξ
      have hgo : ∀ (t : ℕ),
          liftK (runUGo x t) ξ =
            Cslib.Quantum.run (fun s => (liftK (P.unitary s)).toLinearIsometry) ξ x t := by
        intro t; induction t with
        | zero => rw [show runUGo x 0 = P.unitary 0 from mwRunUGo_zero P (phaseEquiv x)]; rfl
        | succ t ih =>
          rw [show runUGo x (t + 1) = ((runUGo x t).trans (phaseEquiv x)).trans (P.unitary (t + 1))
            from mwRunUGo_succ P (phaseEquiv x) t]
          rw [hlift_trans, hlift_trans, ih, ← hlift_oracle]; rfl
      exact hgo q
    have hlift_runU_symm : ∀ (ξ : State N (BitString w × (P.Work × BitString K))),
        liftK (runU x).symm ξ =
          Cslib.Quantum.run (fun s => (liftK (P.unitary (q - s)).symm).toLinearIsometry) ξ x q := by
      intro ξ
      have hrev : ∀ (t : ℕ) (ζ : State N (BitString w × (P.Work × BitString K))),
          liftK ((runUGo x t).symm) ζ =
          Cslib.Quantum.run (fun s => (liftK (P.unitary (t - s)).symm).toLinearIsometry) ζ x t := by
        intro t; induction t with
        | zero =>
          intro ζ
          rw [show runUGo x 0 = P.unitary 0 from mwRunUGo_zero P (phaseEquiv x)]
          rfl
        | succ t ih =>
          intro ζ
          have hsymm : (runUGo x (t + 1)).symm =
              ((P.unitary (t + 1)).symm.trans (phaseEquiv x)).trans (runUGo x t).symm := by
            rw [show runUGo x (t + 1) =
              ((runUGo x t).trans (phaseEquiv x)).trans (P.unitary (t + 1))
              from mwRunUGo_succ P (phaseEquiv x) t]
            ext u; rfl
          rw [hsymm, hlift_trans, hlift_trans, ih]
          have hshift : ∀ (m : ℕ) (η : State N (BitString w × (P.Work × BitString K))),
              Cslib.Quantum.run
                (fun s => (liftK (P.unitary (t + 1 - s)).symm).toLinearIsometry) η x (m + 1) =
              Cslib.Quantum.run (fun s => (liftK (P.unitary (t - s)).symm).toLinearIsometry)
                (phaseOracle x ((liftK (P.unitary (t + 1)).symm) η)) x m := by
            intro m; induction m with
            | zero =>
              intro η
              simp only [Cslib.Quantum.run, Nat.sub_zero, show t + 1 - 1 = t by omega,
                LinearIsometryEquiv.coe_toLinearIsometry]
            | succ m ihm =>
              intro η
              change (liftK (P.unitary (t + 1 - (m + 2))).symm) (phaseOracle x
                (Cslib.Quantum.run (fun s => (liftK (P.unitary (t + 1 - s)).symm).toLinearIsometry)
                  η x (m + 1))) = _
              rw [ihm, show t + 1 - (m + 2) = t - (m + 1) by omega]; rfl
          rw [hshift t ζ, hlift_oracle]
      exact hrev q ξ
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · have hfold : ∀ (m : ℕ) (hm : m ≤ M) (ξ : State N (BitString w × (P.Work × BitString K))),
          ((List.ofFn fun k : Fin m => roundOp x ⟨k.1, by omega⟩).foldl
            (fun acc step => acc.trans step) (LinearIsometryEquiv.refl ℂ _)) ξ =
          applyRounds x m ξ := by
        intro m; induction m with
        | zero => intro _ ξ; simp [applyRounds, mwApplyRounds_zero]
        | succ m ihm =>
          intro hm ξ
          rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
          simp only [Fin.val_last, Fin.val_castSucc, List.foldl_cons, List.foldl_nil,
            LinearIsometryEquiv.trans_apply]
          rw [ihm (by omega)]
          simp only [applyRounds, mwApplyRounds_succ, show m < M by omega, ↓reduceDIte]
      have hrz : ∀ ξ, roundZero ξ = applyRounds x M ξ := by
        intro ξ
        have h := hfold M le_rfl ξ
        have hlist : (List.ofFn fun k : Fin M => roundOp x ⟨k.1, k.2⟩) =
            List.ofFn fun k : Fin M =>
              (((liftK (P.unitary 0)).trans (cnotAcc ⟨2 * k.1, by omega⟩)).trans
                (liftK (P.unitary 0).symm)).trans (cnotInit ⟨2 * k.1 + 1, by omega⟩) := by
          refine congrArg List.ofFn (funext fun k => ?_)
          have h0 : runU x = P.unitary 0 := by
            simp only [runU, hq0, runUGo, mwRunUGo_zero]
          simp [roundOp, h0]
        dsimp only [roundZero]
        rw [← hlist]; exact h
      simp only [QMAQueryProtocol.runState_eq_run, P', hq0, mul_zero, Cslib.Quantum.run, stepU,
        ↓reduceIte, LinearIsometryEquiv.coe_toLinearIsometry]
      exact hrz _
    · -- Shared single-round helper for any `k < M`.
      have hrun_q_step : ∀ (U : ℕ → State N (BitString w × (P.Work × BitString K)) →ₗᵢ[ℂ]
            State N (BitString w × (P.Work × BitString K)))
          (ξ : State N (BitString w × (P.Work × BitString K))),
          Cslib.Quantum.run U ξ x q = U q (phaseOracle x (Cslib.Quantum.run U ξ x (q - 1))) := by
        intro U ξ
        have hq1 : q = (q - 1) + 1 := by omega
        conv_lhs => rw [hq1]
        simp only [Cslib.Quantum.run, show q - 1 + 1 = q by omega]
      have hround_back : ∀ (k : ℕ) (hk : k < M),
          Cslib.Quantum.run (fun s => (stepU s).toLinearIsometry)
            (P'.embedWitness ψ) x (2 * k * q) =
            liftK (P.unitary 0) (applyRounds x k (P'.embedWitness ψ)) →
          ∀ (j : ℕ) (hj : j < q),
            Cslib.Quantum.run (fun s => (stepU s).toLinearIsometry)
              (P'.embedWitness ψ) x (2 * k * q + q + j) =
            Cslib.Quantum.run (fun s => (liftK (P.unitary (q - s)).symm).toLinearIsometry)
              (cnotAcc ⟨2 * k, by omega⟩
                (liftK (runU x) (applyRounds x k (P'.embedWitness ψ)))) x j := by
        intro k hk hprev
        have hfwd : ∀ (j : ℕ) (hj : j < q),
            Cslib.Quantum.run (fun s => (stepU s).toLinearIsometry)
              (P'.embedWitness ψ) x (2 * k * q + j) =
            Cslib.Quantum.run (fun s => (liftK (P.unitary s)).toLinearIsometry)
              (applyRounds x k (P'.embedWitness ψ)) x j := by
          intro j; induction j with
          | zero => intro _; simpa [Cslib.Quantum.run] using hprev
          | succ j ihj =>
            intro hj
            rw [show 2 * k * q + (j + 1) = (2 * k * q + j) + 1 by omega]
            simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
            rw [ihj (by omega), show 2 * k * q + j + 1 = 2 * k * q + (j + 1) by omega]
            have hlt : 2 * k * q + (j + 1) < 2 * M * q := by nlinarith
            have hrem : (2 * k * q + (j + 1)) % (2 * q) = j + 1 := by
              rw [show 2 * k * q + (j + 1) = (j + 1) + (2 * q) * k by ring,
                Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
            simp only [stepU, hqpos.ne', show 2 * k * q + (j + 1) ≠ 0 by omega, hlt,
              ↓reduceIte, hrem, show j + 1 < q from hj, ↓reduceDIte, show j + 1 ≠ 0 by omega]
        have hmid : Cslib.Quantum.run (fun s => (stepU s).toLinearIsometry)
            (P'.embedWitness ψ) x (2 * k * q + q) =
            liftK (P.unitary q).symm (cnotAcc ⟨2 * k, by omega⟩
              (liftK (runU x) (applyRounds x k (P'.embedWitness ψ)))) := by
          rw [show 2 * k * q + q = (2 * k * q + (q - 1)) + 1 by omega]
          simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
          rw [hfwd (q - 1) (by omega), show 2 * k * q + (q - 1) + 1 = 2 * k * q + q by omega]
          have hlt : 2 * k * q + q < 2 * M * q := by nlinarith
          have hrem : (2 * k * q + q) % (2 * q) = q := by
            rw [show 2 * k * q + q = q + (2 * q) * k by ring,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          have hdiv : (2 * k * q + q) / (2 * q) = k := by
            rw [show 2 * k * q + q = q + (2 * q) * k by ring,
              Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
          simp only [stepU, hqpos.ne', show 2 * k * q + q ≠ 0 by omega, hlt, ↓reduceIte,
            hrem, show ¬ (q < q) by omega, ↓reduceDIte, hdiv, hk, eq_self,
            LinearIsometryEquiv.trans_apply]
          rw [hlift_runU, hrun_q_step]
          rfl
        intro j; induction j with
        | zero => intro _; simpa [Cslib.Quantum.run] using hmid
        | succ j ihj =>
          intro hj
          rw [show 2 * k * q + q + (j + 1) = (2 * k * q + q + j) + 1 by omega]
          simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
          rw [ihj (by omega), show 2 * k * q + q + j + 1 = 2 * k * q + q + (j + 1) by omega]
          have hlt : 2 * k * q + q + (j + 1) < 2 * M * q := by nlinarith
          have hrem : (2 * k * q + q + (j + 1)) % (2 * q) = q + (j + 1) := by
            rw [show 2 * k * q + q + (j + 1) = (q + (j + 1)) + (2 * q) * k by ring,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          simp only [stepU, hqpos.ne', show 2 * k * q + q + (j + 1) ≠ 0 by omega, hlt,
            ↓reduceIte, hrem, show ¬ (q + (j + 1) < q) by omega, ↓reduceDIte,
            show q + (j + 1) ≠ q by omega, show 2 * q - (q + (j + 1)) = q - (j + 1) by omega]
      have hstep_run : ∀ (k : ℕ) (hk : k < M),
          Cslib.Quantum.run (fun s => (stepU s).toLinearIsometry)
            (P'.embedWitness ψ) x (2 * k * q) =
          liftK (P.unitary 0) (applyRounds x k (P'.embedWitness ψ)) := by
        intro k; induction k with
        | zero =>
          intro _
          simp only [mul_zero, zero_mul, Cslib.Quantum.run, applyRounds, mwApplyRounds_zero,
            stepU, hqpos.ne', ↓reduceIte, LinearIsometryEquiv.coe_toLinearIsometry]
        | succ k ihk =>
          intro hk
          have hk0 : k < M := by omega
          have hback := hround_back k hk0 (ihk hk0)
          have h2eq : 2 * (k + 1) * q = (2 * k * q + q + (q - 1)) + 1 := by
            calc 2 * (k + 1) * q = 2 * k * q + 2 * q := by ring
              _ = (2 * k * q + q + (q - 1)) + 1 := by omega
          rw [h2eq]
          simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
          rw [hback (q - 1) (by omega)]
          have hlt : 2 * (k + 1) * q < 2 * M * q := by nlinarith
          have hrem : (2 * (k + 1) * q) % (2 * q) = 0 := by
            rw [show 2 * (k + 1) * q = (2 * q) * (k + 1) by ring, Nat.mul_mod_right]
          have hdiv : (2 * (k + 1) * q) / (2 * q) = k + 1 := by
            rw [show 2 * (k + 1) * q = (2 * q) * (k + 1) by ring,
              Nat.mul_div_cancel_left _ (by omega)]
          have hk1 : 1 ≤ k + 1 ∧ k + 1 < M := ⟨by omega, hk⟩
          have hstep_at : stepU (2 * (k + 1) * q) =
              ((liftK (P.unitary 0).symm).trans (cnotInit ⟨2 * k + 1, by omega⟩)).trans
                (liftK (P.unitary 0)) := by
            simp only [stepU, hqpos.ne', show 2 * (k + 1) * q ≠ 0 by omega,
              show 2 * (k + 1) * q < 2 * M * q from hlt, ↓reduceIte, hrem, hqpos, ↓reduceDIte,
              hdiv, hk1, show k + 1 - 1 = k by omega, eq_self, and_self]
          rw [← h2eq, hstep_at]
          simp only [LinearIsometryEquiv.trans_apply, applyRounds, mwApplyRounds_succ, hk0,
            ↓reduceDIte, roundOp]
          rw [hlift_runU_symm, hrun_q_step]
          simp only [Nat.sub_self, LinearIsometryEquiv.coe_toLinearIsometry]
      have hM1 : M - 1 < M := by omega
      have hback := hround_back (M - 1) hM1 (hstep_run (M - 1) hM1)
      have hfinal_eq : 2 * M * q = (2 * (M - 1) * q + q + (q - 1)) + 1 := by
        have hM_eq : M = (M - 1) + 1 := by omega
        calc 2 * M * q = 2 * ((M - 1) + 1) * q := by rw [← hM_eq]
          _ = 2 * (M - 1) * q + 2 * q := by ring
          _ = (2 * (M - 1) * q + q + (q - 1)) + 1 := by omega
      rw [QMAQueryProtocol.runState_eq_run]
      change Cslib.Quantum.run (fun s => (stepU s).toLinearIsometry) (P'.embedWitness ψ) x
        (2 * M * q) = _
      rw [hfinal_eq]
      simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
      rw [hback (q - 1) (by omega), ← hfinal_eq]
      have hstep_end : stepU (2 * M * q) =
          (liftK (P.unitary 0).symm).trans (cnotInit ⟨2 * M - 1, by omega⟩) := by
        simp only [stepU, hqpos.ne', show 2 * M * q ≠ 0 by omega,
          show ¬ (2 * M * q < 2 * M * q) by omega, ↓reduceIte, eq_self]
      rw [hstep_end]
      have hM_eq : M = (M - 1) + 1 := by omega
      conv_rhs => rw [hM_eq]
      simp only [applyRounds, mwApplyRounds_succ, hM1, ↓reduceDIte, roundOp,
        LinearIsometryEquiv.trans_apply, show 2 * (M - 1) + 1 = 2 * M - 1 by omega]
      rw [hlift_runU_symm, hrun_q_step]
      simp only [Nat.sub_self, LinearIsometryEquiv.coe_toLinearIsometry]
  -- Spectral analysis of `H_x` and exact binomial acceptance probability for any `x` and `ψ`.
  have hprob_formula : ∀ (x : BitString N),
      ∃ (v : OrthonormalBasis (BitString w) ℂ (EuclideanSpace ℂ (BitString w)))
        (lam : BitString w → ℝ),
        (∀ j, lam j = P.acceptProb x (v j)) ∧
        (∀ ψ : EuclideanSpace ℂ (BitString w),
          P.acceptProb x ψ = ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 * lam j) ∧
        (∀ ψ : EuclideanSpace ℂ (BitString w),
          P'.acceptProb x ψ =
            ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 *
              ∑ y : BitString K with τ * (K : ℝ) ≤ (weight y : ℝ),
                (lam j) ^ weight y * (1 - lam j) ^ (K - weight y)) := by
    intro x
    let Pacc : State N (BitString w × P.Work) →ₗ[ℂ] State N (BitString w × P.Work) :=
      { toFun := fun χ => WithLp.toLp 2 fun p => if p ∈ P.accept then χ.ofLp p else 0
        map_add' := fun χ₁ χ₂ => by
          ext p; simp only [PiLp.add_apply]; split_ifs <;> simp
        map_smul' := fun c χ => by
          ext p; simp only [PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    let P0 : State N (BitString w × P.Work) →ₗ[ℂ] State N (BitString w × P.Work) :=
      { toFun := fun χ =>
          WithLp.toLp 2 fun p => if (p.1, p.2.1, p.2.2.2) = P.initWork then χ.ofLp p else 0
        map_add' := fun χ₁ χ₂ => by
          ext p; simp only [PiLp.add_apply]; split_ifs <;> simp
        map_smul' := fun c χ => by
          ext p; simp only [PiLp.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    let P1 : State N (BitString w × P.Work) →ₗ[ℂ] State N (BitString w × P.Work) :=
      ((runU x).symm.toLinearMap.comp Pacc).comp (runU x).toLinearMap
    let Hx : Matrix (BitString w) (BitString w) ℂ :=
      Matrix.of fun u v => inner ℂ (P.runState x (ket u)) (Pacc (P.runState x (ket v)))
    have hHx_herm : Hx.IsHermitian := by
      ext u v
      simp only [Matrix.conjTranspose_apply, Hx, Matrix.of_apply, Complex.star_def]
      have hsymm : ∀ a b : State N (BitString w × P.Work),
          inner ℂ a (Pacc b) = inner ℂ (Pacc a) b := by
        intro a b
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pacc,
          LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Pi.star_apply]
        split_ifs <;> simp
      rw [hsymm, ← inner_conj_symm]
      simp [hsymm]
    let v := hHx_herm.eigenvectorBasis
    let lam := hHx_herm.eigenvalues
    have hexp_run : ∀ ψ : EuclideanSpace ℂ (BitString w),
        P.runState x ψ = ∑ u : BitString w, ψ.ofLp u • P.runState x (ket u) := by
      intro ψ
      have hsum : ψ = ∑ u : BitString w, ψ.ofLp u • ket u := (sum_smul_ket ψ).symm
      conv_lhs => rw [hsum]
      have hlin : ∀ S : Finset (BitString w),
          P.runState x (∑ u ∈ S, ψ.ofLp u • ket u) =
            ∑ u ∈ S, ψ.ofLp u • P.runState x (ket u) := by
        intro S; induction S using Finset.induction_on with
        | empty => have := P.runState_smul x 0 0; simpa using this
        | insert a S ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, P.runState_add, P.runState_smul, ih]
      exact hlin Finset.univ
    have hinner_quad : ∀ ψ : EuclideanSpace ℂ (BitString w),
        dotProduct (star ⇑ψ) (Hx *ᵥ ⇑ψ) = (P.acceptProb x ψ : ℂ) := by
      intro ψ
      have hinner : inner ℂ (P.runState x ψ) (Pacc (P.runState x ψ)) =
          dotProduct (star ⇑ψ) (Hx *ᵥ ⇑ψ) := by
        rw [hexp_run ψ, sum_inner]
        simp only [dotProduct, Matrix.mulVec, Hx, Matrix.of_apply, Pi.star_apply, Complex.star_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [inner_smul_left, map_sum, inner_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_smul, inner_smul_right]; ring
      rw [← hinner]
      have hfilt : (Finset.univ.filter fun p => p ∈ P.accept) = P.accept := by ext p; simp
      simp only [QMAQueryProtocol.acceptProb_eq_measureProb, measureProb,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pacc, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.star_apply]
      rw [Complex.ofReal_sum]
      conv_rhs => rw [← hfilt]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p ∈ P.accept
      · simp only [hp, ↓reduceIte, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp only [hp, ↓reduceIte, zero_mul]
    have hlam_eq : ∀ j, lam j = P.acceptProb x (v j) := by
      intro j
      dsimp only [lam, v]
      rw [hHx_herm.eigenvalues_eq j, hinner_quad (hHx_herm.eigenvectorBasis j),
        RCLike.re_eq_complex_re, Complex.ofReal_re]
    have haccept_spectral : ∀ ψ : EuclideanSpace ℂ (BitString w),
        P.acceptProb x ψ = ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 * lam j := by
      intro ψ
      have hrepr : ψ = ∑ j : BitString w, inner ℂ (v j) ψ • v j := (v.sum_repr' ψ).symm
      have hHx_ψ : Hx *ᵥ ⇑ψ = ∑ j : BitString w, (inner ℂ (v j) ψ * (lam j : ℂ)) • ⇑(v j) := by
        have hlin : ∀ S : Finset (BitString w),
            Hx *ᵥ ⇑(∑ j ∈ S, inner ℂ (v j) ψ • v j) =
              ∑ j ∈ S, (inner ℂ (v j) ψ * (lam j : ℂ)) • ⇑(v j) := by
          intro S; induction S using Finset.induction_on with
          | empty => simp
          | insert a S ha ih =>
            have hadd : (⇑(inner ℂ (v a) ψ • v a + ∑ j ∈ S, inner ℂ (v j) ψ • v j) :
                BitString w → ℂ) = ⇑(inner ℂ (v a) ψ • v a) +
                ⇑(∑ j ∈ S, inner ℂ (v j) ψ • v j) := by funext i; rfl
            have hsm : (⇑(inner ℂ (v a) ψ • v a) : BitString w → ℂ) =
                inner ℂ (v a) ψ • ⇑(v a) := by funext i; rfl
            rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, Matrix.mulVec_add,
              hsm, Matrix.mulVec_smul, hHx_herm.mulVec_eigenvectorBasis a, ih]
            simp only [mul_smul]; rfl
        conv_lhs => rw [hrepr]
        exact hlin Finset.univ
      have hdot : dotProduct (star ⇑ψ) (Hx *ᵥ ⇑ψ) =
          ∑ j : BitString w, ((‖inner ℂ (v j) ψ‖ ^ 2 * lam j : ℝ) : ℂ) := by
        rw [hHx_ψ, dotProduct_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        have hinner_v : dotProduct (star ⇑ψ) ⇑(v j) = inner ℂ ψ (v j) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        rw [hinner_v, ← inner_conj_symm ψ (v j)]
        calc inner ℂ (v j) ψ * (lam j : ℂ) * (starRingEnd ℂ) (inner ℂ (v j) ψ)
            = inner ℂ (v j) ψ * (starRingEnd ℂ) (inner ℂ (v j) ψ) * (lam j : ℂ) := by ring
          _ = ((‖inner ℂ (v j) ψ‖ ^ 2 * lam j : ℝ) : ℂ) := by
              rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
      have hre := congrArg Complex.re ((hinner_quad ψ).symm.trans hdot)
      rw [Complex.ofReal_re, Complex.re_sum] at hre
      simpa only [Complex.ofReal_re] using hre
    let e0 (j : BitString w) : State N (BitString w × P.Work) := P.embedWitness (v j)
    let w1 (j : BitString w) : State N (BitString w × P.Work) := P1 (e0 j) - (lam j : ℂ) • e0 j
    have hP0_e0 : ∀ j, P0 (e0 j) = e0 j := by
      intro j; ext p
      simp only [P0, e0, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
        QMAQueryProtocol.embedWitness_apply]
      split_ifs <;> rfl
    have hP0_P1 : ∀ j, P0 (P1 (e0 j)) = (lam j : ℂ) • e0 j := by
      intro j
      ext p
      simp only [P0, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, PiLp.smul_apply,
        smul_eq_mul]
      by_cases hp : (p.1, p.2.1, p.2.2.2) = P.initWork
      · simp only [hp, ↓reduceIte]
        have hket_eq : (P1 (e0 j)).ofLp p = inner ℂ (P.embedWitness (ket p.2.2.1)) (P1 (e0 j)) := by
          simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
            QMAQueryProtocol.embedWitness_apply, ket_apply]
          rw [Finset.sum_eq_single p]
          · simp [hp]
          · intro q _ hqp
            by_cases hq : (q.1, q.2.1, q.2.2.2) = P.initWork
            · have hqu : q.2.2.1 ≠ p.2.2.1 := fun hu => hqp (by
                rcases p with ⟨p1, p2, p3, p4⟩; rcases q with ⟨q1, q2, q3, q4⟩
                simp only at hp hq hu
                have hpq := hq.trans hp.symm
                rcases Prod.mk.inj hpq with ⟨rfl, hpq2⟩
                rcases Prod.mk.inj hpq2 with ⟨rfl, rfl⟩
                subst hu; rfl)
              simp [hq, hqu]
            · simp [hq]
          · simp
        rw [hket_eq]
        have hP1_inner : inner ℂ (P.embedWitness (ket p.2.2.1)) (P1 (e0 j)) =
            (Hx *ᵥ ⇑(v j)) p.2.2.1 := by
          simp only [P1, LinearMap.comp_apply, LinearEquiv.coe_coe,
            LinearIsometryEquiv.coe_toLinearEquiv, e0, Matrix.mulVec, dotProduct, Hx,
            Matrix.of_apply]
          rw [← LinearIsometryEquiv.inner_map_map (runU x), LinearIsometryEquiv.apply_symm_apply,
            hrunU_eq, hrunU_eq, ← QMAQueryProtocol.runState_eq_run,
            ← QMAQueryProtocol.runState_eq_run, hexp_run (v j), map_sum, inner_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_smul, inner_smul_right]; ring
        rw [hP1_inner, hHx_herm.mulVec_eigenvectorBasis j]
        simp only [Pi.smul_apply, Complex.real_smul, e0,
          QMAQueryProtocol.embedWitness_apply, hp, ↓reduceIte]; rfl
      · simp [hp, e0, QMAQueryProtocol.embedWitness_apply]
    have hP0_w1 : ∀ j, P0 (w1 j) = 0 := by
      intro j; simp [w1, map_sub, hP0_P1, hP0_e0]
    have hP1_idem : ∀ χ, P1 (P1 χ) = P1 χ := by
      intro χ
      simp only [P1, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
      congr 1; ext p; simp only [Pacc, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
      split_ifs <;> rfl
    have hP1_w1 : ∀ j, P1 (w1 j) = (1 - (lam j : ℂ)) • (P1 (e0 j)) := by
      intro j; simp only [w1, map_sub, map_smul, hP1_idem]; rw [sub_smul, one_smul]
    have hP1_w1' : ∀ j, P1 (w1 j) =
        ((lam j * (1 - lam j) : ℝ) : ℂ) • e0 j + (1 - (lam j : ℂ)) • w1 j := by
      intro j
      rw [hP1_w1]
      have hscal : (1 - (lam j : ℂ)) • P1 (e0 j) =
          ((lam j : ℂ) * (1 - (lam j : ℂ))) • e0 j +
            (1 - (lam j : ℂ)) • (P1 (e0 j) - (lam j : ℂ) • e0 j) := by
        rw [smul_sub, smul_smul]; module
      simpa [w1] using hscal
    have hinner_e0 : ∀ j k, inner ℂ (e0 j) (e0 k) = if j = k then 1 else 0 := by
      intro j k
      rw [show e0 j = P.embedWitnessLI (v j) from (P.embedWitnessLI_apply (v j)).symm,
        show e0 k = P.embedWitnessLI (v k) from (P.embedWitnessLI_apply (v k)).symm,
        LinearIsometry.inner_map_map]
      by_cases hjk : j = k
      · subst hjk; simp [v.orthonormal.1 j]
      · simp [hjk, v.orthonormal.2 hjk]
    have hinner_e0_w1 : ∀ j k, inner ℂ (e0 j) (w1 k) = 0 := by
      intro j k
      have hsymm : ∀ a b, inner ℂ a (P0 b) = inner ℂ (P0 a) b := by
        intro a b; simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
          P0, LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_congr rfl fun p _ => ?_; split_ifs <;> simp
      rw [← hP0_e0 j, ← hsymm, hP0_w1 k, inner_zero_right]
    have hinner_w1 : ∀ j k,
        inner ℂ (w1 j) (w1 k) = if j = k then ((lam j * (1 - lam j) : ℝ) : ℂ) else 0 := by
      intro j k
      have hsymm1 : ∀ a b, inner ℂ a (P1 b) = inner ℂ (P1 a) b := by
        intro a b
        have hacc : ∀ u v, inner ℂ u (Pacc v) = inner ℂ (Pacc u) v := by
          intro u v; simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
            Pacc, LinearMap.coe_mk, AddHom.coe_mk]
          refine Finset.sum_congr rfl fun p _ => ?_; split_ifs <;> simp
        simp only [P1, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toLinearEquiv]
        calc inner ℂ a ((runU x).symm (Pacc (runU x b)))
            = inner ℂ (runU x a) (runU x ((runU x).symm (Pacc (runU x b)))) :=
              ((runU x).inner_map_map _ _).symm
          _ = inner ℂ (runU x a) (Pacc (runU x b)) := by rw [LinearIsometryEquiv.apply_symm_apply]
          _ = inner ℂ (Pacc (runU x a)) (runU x b) := hacc _ _
          _ = inner ℂ (runU x ((runU x).symm (Pacc (runU x a)))) (runU x b) := by
              rw [LinearIsometryEquiv.apply_symm_apply]
          _ = inner ℂ ((runU x).symm (Pacc (runU x a))) b := (runU x).inner_map_map _ _
      have h1 : inner ℂ (w1 j) (w1 k) = inner ℂ (w1 j) (P1 (e0 k)) := by
        rw [show w1 k = P1 (e0 k) - (lam k : ℂ) • e0 k from rfl, inner_sub_right, inner_smul_right,
          ← inner_conj_symm (w1 j) (e0 k), hinner_e0_w1, map_zero, mul_zero, sub_zero]
      have h2 : inner ℂ (P1 (e0 j)) (e0 k) = (lam j : ℂ) * inner ℂ (e0 j) (e0 k) := by
        have h0symm : ∀ a b, inner ℂ a (P0 b) = inner ℂ (P0 a) b := by
          intro a b; simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
            P0, LinearMap.coe_mk, AddHom.coe_mk]
          refine Finset.sum_congr rfl fun p _ => ?_; split_ifs <;> simp
        conv_lhs => rw [← hP0_e0 k]
        rw [h0symm, hP0_P1, inner_smul_left, Complex.conj_ofReal]
      rw [h1, hsymm1, hP1_w1, inner_smul_left, h2, hinner_e0]
      split_ifs with hjk
      · subst hjk; simp; ring
      · simp
    let sliceK (z : BitString K) (χ : State N (BitString w × (P.Work × BitString K))) :
        State N (BitString w × P.Work) :=
      WithLp.toLp 2 fun p => χ.ofLp (p.1, p.2.1, (p.2.2.1, (p.2.2.2, z)))
    let prevBit (k : ℕ) (z : BitString K) : Bool :=
      if h : 1 ≤ k ∧ 2 * k - 1 < K then z ⟨2 * k - 1, h.2⟩ else true
    have hslice_rounds : ∀ (k : ℕ) (hk : k ≤ M) (j : BitString w) (z : BitString K),
        (∃ a : ℂ,
          (sliceK z (applyRounds x k (P'.embedWitness (v j))) =
            if ∀ i : Fin K, 2 * k ≤ i.1 → z i = false then
              a • (if prevBit k z then e0 j else w1 j)
            else 0) ∧
          ‖sliceK z (applyRounds x k (P'.embedWitness (v j)))‖ ^ 2 =
            if ∀ i : Fin K, 2 * k ≤ i.1 → z i = false then
              ∏ i : Fin K with i.1 < 2 * k, (if eqBits z i then lam j else 1 - lam j)
            else 0) := by
      intro k; induction k with
      | zero =>
        intro _ j z
        refine ⟨1, ?_, ?_⟩
        · by_cases hz : ∀ i : Fin K, 0 ≤ i.1 → z i = false
          · have hz0 : z = fun _ => false := funext fun i => hz i (Nat.zero_le _)
            subst hz0
            simp only [prevBit, one_smul, applyRounds, mwApplyRounds_zero]
            ext p; simp [sliceK, QMAQueryProtocol.embedWitness_apply, P', e0, Prod.ext_iff]
          · simp only [hz, ↓reduceIte, applyRounds, mwApplyRounds_zero]
            have hne : z ≠ fun _ => false := fun h => hz (fun i _ => congr_fun h i)
            ext p; simp [sliceK, QMAQueryProtocol.embedWitness_apply, P', hne]
        · by_cases hz : ∀ i : Fin K, 0 ≤ i.1 → z i = false
          · have hz0 : z = fun _ => false := funext fun i => hz i (Nat.zero_le _)
            subst hz0
            have hslice :
                sliceK (fun _ => false) (applyRounds x 0 (P'.embedWitness (v j))) = e0 j := by
              ext p
              simp [sliceK, applyRounds, mwApplyRounds_zero, QMAQueryProtocol.embedWitness_apply,
                P', e0, Prod.ext_iff]
            simp only [hslice, show ‖e0 j‖ = 1 by
              rw [show e0 j = P.embedWitnessLI (v j) from (P.embedWitnessLI_apply (v j)).symm,
                LinearIsometry.norm_map, v.orthonormal.1 j]]
            simp
          · have hne : z ≠ fun _ => false := fun h => hz (fun i _ => congr_fun h i)
            have hslice : sliceK z (applyRounds x 0 (P'.embedWitness (v j))) = 0 := by
              ext p
              simp [sliceK, applyRounds, mwApplyRounds_zero, QMAQueryProtocol.embedWitness_apply,
                P', hne]
            simp only [hz, ↓reduceIte, hslice, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      | succ k ihk =>
        intro hk j z
        have hklt : k < M := by omega
        have hcnotInit : ∀ (idx : Fin K) (ξ : State N (BitString w × (P.Work × BitString K)))
            (z' : BitString K),
            sliceK z' (cnotInit idx ξ) =
              P0 (sliceK (Function.update z' idx (!z' idx)) ξ) +
              (sliceK z' ξ - P0 (sliceK z' ξ)) := by
          intro idx ξ z'; ext p
          simp only [sliceK, cnotInit, permute_apply, cnotInitEquiv, Equiv.coe_fn_symm_mk, P0,
            PiLp.add_apply, PiLp.sub_apply, LinearMap.coe_mk, AddHom.coe_mk]
          by_cases hp : (p.1, p.2.1, p.2.2.2) = P.initWork <;> simp [hp]
        have hcnotAcc : ∀ (idx : Fin K) (ξ : State N (BitString w × (P.Work × BitString K)))
            (z' : BitString K),
            sliceK z' (cnotAcc idx ξ) =
              Pacc (sliceK (Function.update z' idx (!z' idx)) ξ) +
              (sliceK z' ξ - Pacc (sliceK z' ξ)) := by
          intro idx ξ z'; ext p
          simp only [sliceK, cnotAcc, permute_apply, cnotAccEquiv, Equiv.coe_fn_symm_mk, Pacc,
            PiLp.add_apply, PiLp.sub_apply, LinearMap.coe_mk, AddHom.coe_mk]
          by_cases hp : p ∈ P.accept <;> simp [hp]
        have hliftK_slice : ∀ (V : State N (BitString w × P.Work) ≃ₗᵢ[ℂ]
              State N (BitString w × P.Work))
            (ξ : State N (BitString w × (P.Work × BitString K))) (z' : BitString K),
            sliceK z' (liftK V ξ) = V (sliceK z' ξ) := fun _ _ _ => rfl
        let i0 : Fin K := ⟨2 * k, by omega⟩
        let i1 : Fin K := ⟨2 * k + 1, by omega⟩
        have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
        let zBase : BitString K := Function.update (Function.update z i1 false) i0 false
        have hstep_exact : ∀ ξ : State N (BitString w × (P.Work × BitString K)),
            (∀ z' : BitString K, (z' i0 = true ∨ z' i1 = true) → sliceK z' ξ = 0) →
            sliceK z (roundOp x ⟨k, hklt⟩ ξ) =
              (if z i1 then P0 else LinearMap.id - P0)
                ((if z i0 then P1 else LinearMap.id - P1) (sliceK zBase ξ)) := by
          intro ξ hξ0
          simp only [roundOp, LinearIsometryEquiv.trans_apply, hcnotInit]
          have hmid_zero : ∀ z' : BitString K, z' i1 = true →
              sliceK z' (liftK (runU x).symm (cnotAcc i0 (liftK (runU x) ξ))) = 0 := by
            intro z' hz'1
            rw [hliftK_slice, hcnotAcc, hliftK_slice, hliftK_slice]
            have h1 : sliceK (Function.update z' i0 (!z' i0)) ξ = 0 :=
              hξ0 _ (Or.inr (by rw [Function.update_of_ne hi01.symm]; exact hz'1))
            have h2 : sliceK z' ξ = 0 := hξ0 _ (Or.inr hz'1)
            simp [h1, h2]
          have hacc_simp : ∀ z' : BitString K, z' i1 = false →
              sliceK z' (liftK (runU x).symm (cnotAcc i0 (liftK (runU x) ξ))) =
                (if z' i0 then P1 else LinearMap.id - P1)
                  (sliceK (Function.update z' i0 false) ξ) := by
            intro z' hz'1
            rw [hliftK_slice, hcnotAcc, hliftK_slice, hliftK_slice]
            cases hz0 : z' i0
            · have h1 : sliceK (Function.update z' i0 (!false)) ξ = 0 :=
                hξ0 _ (Or.inl (by simp))
              have h2 : Function.update z' i0 false = z' :=
                Function.update_eq_self_iff.mpr hz0.symm
              simp only [h1, map_zero, zero_add, h2, Bool.false_eq_true, ↓reduceIte,
                LinearMap.sub_apply, LinearMap.id_apply, P1, LinearMap.comp_apply,
                LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, map_sub,
                LinearIsometryEquiv.symm_apply_apply]
            · have h2 : sliceK z' ξ = 0 := hξ0 _ (Or.inl hz0)
              simp only [h2, map_zero, sub_self, add_zero, ↓reduceIte, P1,
                LinearMap.comp_apply, LinearEquiv.coe_coe,
                LinearIsometryEquiv.coe_toLinearEquiv, Bool.not_true]
          cases hz1 : z i1
          · have h1 : sliceK (Function.update z i1 (!false))
                (liftK (runU x).symm (cnotAcc i0 (liftK (runU x) ξ))) = 0 :=
              hmid_zero _ (by simp)
            rw [h1, map_zero, zero_add, hacc_simp z hz1]
            have hzB : Function.update z i0 false = zBase := by
              ext i
              by_cases h0 : i = i0
              · simp [zBase, h0]
              · simp only [zBase, Function.update_of_ne h0]
                by_cases h1 : i = i1
                · subst h1; simp [hz1]
                · simp [Function.update_of_ne h1]
            rw [hzB]; simp
          · have h2 : sliceK z (liftK (runU x).symm (cnotAcc i0 (liftK (runU x) ξ))) = 0 :=
              hmid_zero z hz1
            rw [h2, map_zero, sub_self, add_zero, Bool.not_true, hacc_simp _ (by simp [i1]),
              Function.update_of_ne hi01]
            simp only [↓reduceIte]; rfl
        have hξ0 : ∀ z' : BitString K, (z' i0 = true ∨ z' i1 = true) →
            sliceK z' (applyRounds x k (P'.embedWitness (v j))) = 0 := by
          intro z' hz'
          obtain ⟨_, hEq, _⟩ := ihk (by omega) j z'
          rw [hEq]
          have hnot : ¬ ∀ i : Fin K, 2 * k ≤ i.1 → z' i = false := by
            intro hall
            rcases hz' with h0 | h1
            · rw [hall i0 (by simp [i0])] at h0; exact Bool.false_ne_true h0
            · rw [hall i1 (by simp [i1])] at h1; exact Bool.false_ne_true h1
          simp [hnot]
        simp only [applyRounds, mwApplyRounds_succ, hklt, ↓reduceDIte]
        rw [hstep_exact _ hξ0]
        obtain ⟨a, hEq, hNorm⟩ := ihk (by omega) j zBase
        by_cases hz : ∀ i : Fin K, 2 * (k + 1) ≤ i.1 → z i = false
        · have hzBase : ∀ i : Fin K, 2 * k ≤ i.1 → zBase i = false := by
            intro i hi
            by_cases hi0 : i = i0
            · subst hi0; simp [zBase]
            · by_cases hi1 : i = i1
              · subst hi1; simp [zBase, hi01.symm]
              · simp only [zBase, Function.update_of_ne hi0, Function.update_of_ne hi1]
                exact hz i (by simp only [i0, i1, Fin.ext_iff] at hi0 hi1; omega)
          have hnorm_prev : ‖sliceK zBase (applyRounds x k (P'.embedWitness (v j)))‖ ^ 2 =
              ∏ i : Fin K with i.1 < 2 * k, (if eqBits z i then lam j else 1 - lam j) := by
            rw [hNorm]
            simp only [eq_true hzBase, ↓reduceIte]
            refine Finset.prod_congr rfl fun i hi => ?_
            have hilt : i.1 < 2 * k := (Finset.mem_filter.mp hi).2
            have heq_i : eqBits zBase i = eqBits z i := by
              have hne0 : i ≠ i0 := by simp [i0, Fin.ext_iff]; omega
              have hne1 : i ≠ i1 := by simp [i1, Fin.ext_iff]; omega
              simp only [eqBits, mwEqBits]
              split_ifs with h0
              · simp [zBase, hne0, hne1]
              · have hp0 : (⟨i.1 - 1, by omega⟩ : Fin K) ≠ i0 := by
                  simp [i0, Fin.ext_iff]; omega
                have hp1 : (⟨i.1 - 1, by omega⟩ : Fin K) ≠ i1 := by
                  simp [i1, Fin.ext_iff]; omega
                simp [zBase, hne0, hne1, hp0, hp1]
            rw [heq_i]
          rw [hEq] at hnorm_prev ⊢
          simp only [eq_true hzBase, ↓reduceIte] at hnorm_prev ⊢
          have hlam0 : 0 ≤ lam j := by rw [hlam_eq]; exact P.acceptProb_nonneg x (v j)
          have hlam1 : lam j ≤ 1 := by rw [hlam_eq]; exact P.acceptProb_le_one x (v.orthonormal.1 j)
          have hnorm_e0 : ‖e0 j‖ ^ 2 = 1 := by
            rw [show e0 j = P.embedWitnessLI (v j) from (P.embedWitnessLI_apply (v j)).symm,
              LinearIsometry.norm_map, v.orthonormal.1 j, one_pow]
          have hnorm_w1 : ‖w1 j‖ ^ 2 = lam j * (1 - lam j) := by
            have h := hinner_w1 j j
            simp only [↓reduceIte, inner_self_eq_norm_sq_to_K,
              RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at h
            exact Complex.ofReal_injective h
          have hprod_step : (∏ i : Fin K with i.1 < 2 * (k + 1),
                (if eqBits z i then lam j else 1 - lam j)) =
              (∏ i : Fin K with i.1 < 2 * k, (if eqBits z i then lam j else 1 - lam j)) *
              (if eqBits z i0 then lam j else 1 - lam j) *
              (if eqBits z i1 then lam j else 1 - lam j) := by
            have hset : (Finset.univ.filter fun i : Fin K => i.1 < 2 * (k + 1)) =
                insert i1 (insert i0 (Finset.univ.filter fun i : Fin K => i.1 < 2 * k)) := by
              ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Fin.ext_iff, i0, i1]; omega
            rw [hset, Finset.prod_insert (by simp [i0, i1, Fin.ext_iff]),
              Finset.prod_insert (by simp [i0])]
            ring
          have hprev_eq : prevBit k zBase = prevBit k z := by
            simp only [prevBit]
            split_ifs with hk0
            · have hne0 : (⟨2 * k - 1, hk0.2⟩ : Fin K) ≠ i0 := by simp [i0, Fin.ext_iff]; omega
              have hne1 : (⟨2 * k - 1, hk0.2⟩ : Fin K) ≠ i1 := by simp [i1, Fin.ext_iff]
              simp [zBase, hne0, hne1]
            · rfl
          have heq0 : eqBits z i0 = (z i0 == prevBit k z) := by
            by_cases hk0 : k = 0
            · subst hk0; simp [eqBits, mwEqBits, prevBit, i0]
            · have h1 : 1 ≤ k ∧ 2 * k - 1 < K := ⟨by omega, by omega⟩
              simp [eqBits, mwEqBits, prevBit, i0, show 2 * k ≠ 0 by omega, h1]
          have heq1 : eqBits z i1 = (z i1 == z i0) := by
            simp only [eqBits, mwEqBits, i0, i1, show 2 * k + 1 ≠ 0 by omega, ↓reduceDIte,
              show 2 * k + 1 - 1 = 2 * k by omega]
          have hprev_next : prevBit (k + 1) z = z i1 := by
            simp [prevBit, i1, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
              show 2 * k + 1 < K by omega]
          rw [hprev_eq, hprev_next, hprod_step, heq0, heq1]
          simp only [eq_true hz, ↓reduceIte]
          have ha_sq : ‖a‖ ^ 2 * (if prevBit k z then 1 else lam j * (1 - lam j)) =
              ∏ i : Fin K with i.1 < 2 * k, (if eqBits z i then lam j else 1 - lam j) := by
            rw [← hnorm_prev, hprev_eq, norm_smul, mul_pow]
            congr 1; cases prevBit k z
            · exact hnorm_w1.symm
            · exact hnorm_e0.symm
          exact mw_two_dim_step P0 P1 (e0 j) (w1 j) (lam j) a (prevBit k z) (z i0) (z i1) _
            (hP0_e0 j) (hP0_w1 j) (hP0_P1 j) rfl (hP1_w1' j) hnorm_e0 hnorm_w1 ha_sq
        · have hnotBase : ¬ ∀ i : Fin K, 2 * k ≤ i.1 → zBase i = false := by
            intro hall; apply hz; intro i hi
            have hne0 : i ≠ i0 := by simp [i0, Fin.ext_iff]; omega
            have hne1 : i ≠ i1 := by simp [i1, Fin.ext_iff]; omega
            simpa [zBase, hne0, hne1] using hall i (by omega)
          rw [hEq]
          simp only [hnotBase, ↓reduceIte, map_zero]
          exact ⟨0, by simp [hz], by simp [hz]⟩
    refine ⟨v, lam, hlam_eq, haccept_spectral, fun ψ => ?_⟩
    have hψ_exp : ψ = ∑ j : BitString w, inner ℂ (v j) ψ • v j := (v.sum_repr' ψ).symm
    have hrun_lin : P'.runState x ψ =
        ∑ j : BitString w, inner ℂ (v j) ψ • applyRounds x M (P'.embedWitness (v j)) := by
      rw [hcircuit x ψ]
      have hlin : ∀ (m : ℕ) (S : Finset (BitString w)),
          applyRounds x m (P'.embedWitness (∑ j ∈ S, inner ℂ (v j) ψ • v j)) =
            ∑ j ∈ S, inner ℂ (v j) ψ • applyRounds x m (P'.embedWitness (v j)) := by
        intro m S; induction S using Finset.induction_on with
        | empty =>
          have h0 : P'.embedWitness (0 : EuclideanSpace ℂ (BitString w)) = 0 := by
            simpa using P'.embedWitness_smul 0 0
          simp only [Finset.sum_empty, h0]
          simpa using mwApplyRounds_smul M (roundOp x) m 0 0
        | insert a S ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, P'.embedWitness_add, P'.embedWitness_smul]
          dsimp only [applyRounds]
          rw [mwApplyRounds_add, mwApplyRounds_smul]
          exact congrArg (inner ℂ (v a) ψ • applyRounds x m (P'.embedWitness (v a)) + ·) ih
      conv_lhs => rw [hψ_exp]
      exact hlin M Finset.univ
    have hprob_slice : P'.acceptProb x ψ =
        ∑ z : BitString K with τ * (K : ℝ) ≤ (weight (eqBits z) : ℝ),
          ‖sliceK z (P'.runState x ψ)‖ ^ 2 := by
      simp only [QMAQueryProtocol.acceptProb_eq_measureProb, measureProb, P', Finset.sum_filter]
      let e : (Fin N × Bool × (BitString w × (P.Work × BitString K))) ≃
          BitString K × (Fin N × Bool × (BitString w × P.Work)) :=
        { toFun := fun p => (p.2.2.2.2, (p.1, p.2.1, (p.2.2.1, p.2.2.2.1)))
          invFun := fun q => (q.2.1, q.2.2.1, (q.2.2.2.1, (q.2.2.2.2, q.1)))
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      rw [Fintype.sum_equiv e
        (fun p => if τ * (K : ℝ) ≤ (weight (eqBits p.2.2.2.2) : ℝ) then
          ‖(P'.runState x ψ).ofLp p‖ ^ 2 else 0)
        (fun q => if τ * (K : ℝ) ≤ (weight (eqBits q.1) : ℝ) then
          ‖(P'.runState x ψ).ofLp (e.symm q)‖ ^ 2 else 0)
        (fun _ => rfl), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs
      · rw [EuclideanSpace.norm_sq_eq]; rfl
      · simp
    rw [hprob_slice, hrun_lin]
    have hpyth : ∀ z : BitString K,
        ‖sliceK z (∑ j : BitString w,
          inner ℂ (v j) ψ • applyRounds x M (P'.embedWitness (v j)))‖ ^ 2 =
          ∑ j : BitString w, ‖inner ℂ (v j) ψ‖ ^ 2 *
            ‖sliceK z (applyRounds x M (P'.embedWitness (v j)))‖ ^ 2 := by
      intro z
      have hslice_sum : sliceK z (∑ j : BitString w,
            inner ℂ (v j) ψ • applyRounds x M (P'.embedWitness (v j))) =
          ∑ j : BitString w,
            inner ℂ (v j) ψ • sliceK z (applyRounds x M (P'.embedWitness (v j))) := by
        ext p; simp [sliceK, Finset.sum_apply]
      rw [hslice_sum, ← @inner_self_eq_norm_sq ℂ, sum_inner]
      have horth : ∀ j k : BitString w, j ≠ k →
          inner ℂ (sliceK z (applyRounds x M (P'.embedWitness (v j))))
            (sliceK z (applyRounds x M (P'.embedWitness (v k)))) = 0 := by
        intro j k hjk
        obtain ⟨aj, hEqj, _⟩ := hslice_rounds M le_rfl j z
        obtain ⟨ak, hEqk, _⟩ := hslice_rounds M le_rfl k z
        rw [hEqj, hEqk]
        by_cases hcond : ∀ i : Fin K, 2 * M ≤ i.1 → z i = false
        · simp only [eq_true hcond, ↓reduceIte, inner_smul_left, inner_smul_right]
          have h00 : inner ℂ (if prevBit M z then e0 j else w1 j)
              (if prevBit M z then e0 k else w1 k) = 0 := by
            cases prevBit M z <;> simp [hinner_e0, hinner_w1, hjk]
          rw [h00, mul_zero, mul_zero]
        · simp [hcond]
      have hdiag : ∑ j : BitString w,
            inner ℂ (inner ℂ (v j) ψ • sliceK z (applyRounds x M (P'.embedWitness (v j))))
              (∑ k : BitString w,
                inner ℂ (v k) ψ • sliceK z (applyRounds x M (P'.embedWitness (v k)))) =
          ∑ j : BitString w, ((‖inner ℂ (v j) ψ‖ ^ 2 *
            ‖sliceK z (applyRounds x M (P'.embedWitness (v j)))‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inner_sum, Finset.sum_eq_single j]
        · rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ← mul_assoc,
            RCLike.conj_mul]
          simp only [Complex.ofReal_mul, Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal]
        · intro k _ hkj
          rw [inner_smul_left, inner_smul_right, horth j k hkj.symm, mul_zero, mul_zero]
        · simp
      rw [hdiag, ← Complex.ofReal_sum]
      exact Complex.ofReal_re _
    simp_rw [hpyth]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have heq_bij : Function.Bijective eqBits := mwEqBits_bijective K
    refine Finset.sum_bij (fun z _ => eqBits z)
      (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩)
      (fun _ _ _ _ h => heq_bij.1 h)
      (fun y hy => by
        obtain ⟨z, rfl⟩ := heq_bij.2 y
        exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩, rfl⟩)
      (fun z _ => ?_)
    obtain ⟨_, _, hNorm⟩ := hslice_rounds M le_rfl j z
    have hvac : ∀ i : Fin K, 2 * M ≤ i.1 → z i = false := fun i hi => by omega
    rw [hNorm]
    simp only [eq_true hvac, ↓reduceIte]
    have hcard : #{i : Fin K | eqBits z i = false} = K - weight (eqBits z) := by
      simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight (eqBits z)
    have hsplit : ∏ i : Fin K with i.1 < 2 * M, (if eqBits z i then lam j else 1 - lam j) =
        (∏ i ∈ Finset.univ.filter (fun i : Fin K => eqBits z i = true), lam j) *
        (∏ i ∈ Finset.univ.filter (fun i : Fin K => ¬ eqBits z i = true), (1 - lam j)) := by
      have hall : (Finset.univ.filter fun i : Fin K => i.1 < 2 * M) = Finset.univ := by
        ext i; simp [show i.1 < 2 * M from i.2]
      rw [hall, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : Fin K => eqBits z i = true)]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
    have hnot : Finset.univ.filter (fun i : Fin K => ¬ eqBits z i = true) =
        Finset.univ.filter (fun i : Fin K => eqBits z i = false) := by ext i; simp
    rw [hsplit, hnot, Finset.prod_const, Finset.prod_const, hcard]; rfl
  -- Conclude completeness and soundness from `hprob_formula` and `bernoulli_tail_lower/upper`.
  exact mw_bernoulli_conclude P P' hb0 hba ha1 rfl hK_ge hcomp hsound hprob_formula

end CslibFrontier.QueryComplexity
