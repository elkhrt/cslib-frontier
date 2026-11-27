/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.ComputableAnalysis.ComputableReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.NumberTheory.Real.Irrational

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Computability of `π`, Trigonometric, Exponential, and Logarithmic Functions

Uniform computability for Archimedes' constant `π`, the trigonometric functions `sin`, `cos`, and
`tan`, and the real natural logarithm `Real.log` on positive computable reals and sequences,
proved under standard Lean axioms.

## Main definitions

This module introduces no new public types; it extends the computable real and sequence predicates
from `CslibFrontier.Computability.ComputableAnalysis.ComputableReal` to transcendental elementary
functions.

## Main results

* `CslibFrontier.ComputableAnalysis.isComputableReal_arctan_rat`,
  `CslibFrontier.ComputableAnalysis.isComputableReal_pi`,
  `CslibFrontier.ComputableAnalysis.isComputableReal_two_pi`,
  `CslibFrontier.ComputableAnalysis.isComputableReal_pi_and_irrational`: computability of rational
  arctangents on `[-1/2, 1/2]`, Machin-formula computability of `π` and `2π`, and irrationality of
  `π`.
* `CslibFrontier.ComputableAnalysis.IsComputableRealSeq.sin`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealSeq.cos`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealSeq.tan`,
  `CslibFrontier.ComputableAnalysis.IsComputableReal.sin`,
  `CslibFrontier.ComputableAnalysis.IsComputableReal.cos`,
  `CslibFrontier.ComputableAnalysis.IsComputableReal.tan`: uniform and pointwise computability of
  real
  sine, cosine, and tangent via Maclaurin truncation and global `1`-Lipschitz bounds.
* `CslibFrontier.ComputableAnalysis.isComputableReal_log_two`,
  `CslibFrontier.ComputableAnalysis.IsComputableRealSeq.log`,
  `CslibFrontier.ComputableAnalysis.IsComputableReal.log`: computability of `log 2` and uniform
  computability of `Real.log` on positive computable sequences via dyadic range reduction and the
  hyperbolic arctangent series `log ((1 + u) / (1 - u))`.
-/

public section

namespace CslibFrontier.ComputableAnalysis

private lemma abs_sub_sum_range_le_of_hasSum {f : ℕ → ℝ} {s C : ℝ} (hf : HasSum f s) (N : ℕ)
    (htail : ∀ k : ℕ, |f (k + N)| ≤ C * (1 / 2 : ℝ) ^ k) :
    |s - ∑ n ∈ Finset.range N, f n| ≤ 2 * C := by
  have hshift : HasSum (fun k : ℕ ↦ f (k + N)) (s - ∑ n ∈ Finset.range N, f n) :=
    (hasSum_nat_add_iff N).mpr (by simpa only [sub_add_cancel] using hf)
  have hgeo : HasSum (fun k : ℕ ↦ C * (1 / 2 : ℝ) ^ k) (2 * C) := by
    have h := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by positivity)
      (by norm_num)).mul_left C
    rwa [show C * (1 - (1 / 2 : ℝ))⁻¹ = 2 * C by ring] at h
  have hsum_norm : Summable fun k : ℕ ↦ ‖f (k + N)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun k ↦ by simpa only [Real.norm_eq_abs] using htail k) hgeo.summable
  rw [← hshift.tsum_eq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hsum_norm).trans
    ((hsum_norm.tsum_le_tsum (fun k ↦ by simpa only [Real.norm_eq_abs] using htail k)
      hgeo.summable).trans_eq hgeo.tsum_eq)

/-! ### Computability and irrationality of `π` -/

section PiComputability

private def arctanPoly (q : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (-1) ^ n * q ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℚ)

private lemma computable_arctanPoly (q : ℚ) : IsComputableRatSeq (arctanPoly q) := by
  have h2n1 : Computable fun p : ℕ × ℕ ↦ 2 * p.2 + 1 :=
    Primrec.nat_double_succ.to_comp.comp .snd
  have hnum : IsComputableRatMap fun p : ℕ × ℕ ↦ (-1 : ℚ) ^ p.2 * q ^ (2 * p.2 + 1) :=
    ((IsComputableRatMap.const (-1)).pow .snd).mul ((IsComputableRatMap.const q).pow h2n1)
  exact IsComputableRatMap.sum_range .id (hnum.div (IsComputableRatMap.ofNat h2n1)).to₂

private lemma arctan_poly_err {q : ℚ} (hq : |(q : ℝ)| ≤ 1 / 2) (N : ℕ) :
    |Real.arctan (q : ℝ) - (arctanPoly q N : ℝ)| ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  have hnorm : ‖(q : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; linarith
  have hcast : (arctanPoly q N : ℝ) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * (q : ℝ) ^ (2 * n + 1) / (2 * n + 1 : ℕ) := by
    push_cast [arctanPoly]; rfl
  rw [hcast]
  have hbd := abs_sub_sum_range_le_of_hasSum (Real.hasSum_arctan hnorm) N
    (C := (1 / 2 : ℝ) ^ (2 * N + 1)) fun k ↦ by
      set n := k + N
      have hpos : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (2 * n)
      rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_pow, Nat.abs_cast]
      calc |(q : ℝ)| ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)
          ≤ |(q : ℝ)| ^ (2 * n + 1) := div_le_self (by positivity) hpos
        _ ≤ (1 / 2 : ℝ) ^ (2 * n + 1) := pow_le_pow_left₀ (abs_nonneg _) hq _
        _ ≤ (1 / 2 : ℝ) ^ ((2 * N + 1) + k) :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = (1 / 2 : ℝ) ^ (2 * N + 1) * (1 / 2 : ℝ) ^ k := pow_add _ _ _
  refine hbd.trans ?_
  calc 2 * (1 / 2 : ℝ) ^ (2 * N + 1)
      = (1 / 2 : ℝ) ^ (2 * N) := by rw [pow_succ]; ring
    _ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
    _ = (2 : ℝ) ^ (-(N : ℤ)) := by rw [one_div, inv_pow, zpow_neg, zpow_natCast]

/-- For every rational `q ∈ ℚ` with `|q| ≤ 1 / 2`, `Real.arctan q` is a computable real number. -/
theorem isComputableReal_arctan_rat {q : ℚ} (hq : |(q : ℝ)| ≤ 1 / 2) :
    IsComputableReal (Real.arctan (q : ℝ)) :=
  isComputableReal_of_rat_le (computable_arctanPoly q) (arctan_poly_err hq)

/-- Archimedes' constant `Real.pi` is a computable real number. -/
theorem isComputableReal_pi : IsComputableReal Real.pi := by
  have h5 : IsComputableReal (Real.arctan (5 : ℝ)⁻¹) := by
    simpa using isComputableReal_arctan_rat (q := 5⁻¹) (by norm_num)
  have h239 : IsComputableReal (Real.arctan (239 : ℝ)⁻¹) := by
    simpa using isComputableReal_arctan_rat (q := 239⁻¹) (by norm_num)
  have hpi : Real.pi = 16 * Real.arctan (5 : ℝ)⁻¹ - 4 * Real.arctan (239 : ℝ)⁻¹ := by
    linarith [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  rw [hpi]
  exact ((isComputableReal_nat 16).mul h5).sub ((isComputableReal_nat 4).mul h239)

/-- The period `2 * Real.pi` is a computable real number. -/
theorem isComputableReal_two_pi : IsComputableReal (2 * Real.pi) :=
  (isComputableReal_nat 2).mul isComputableReal_pi

/-- Archimedes' constant `Real.pi` is an irrational computable real number. -/
theorem isComputableReal_pi_and_irrational : IsComputableReal Real.pi ∧ Irrational Real.pi :=
  ⟨isComputableReal_pi, irrational_pi⟩

end PiComputability

/-! ### Uniform and pointwise computability of `sin`, `cos`, and `tan` -/

section SinCosComputability

private def altFactorialPoly (e : ℕ) (q : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (-1) ^ n * q ^ (2 * n + e) / (((2 * n + e).factorial : ℕ) : ℚ)

private lemma computable_altFactorialPoly {α : Type*} [Primcodable α] (e : ℕ)
    {q : α → ℚ} {N : α → ℕ} (hq : IsComputableRatMap q) (hN : Computable N) :
    IsComputableRatMap fun a ↦ altFactorialPoly e (q a) (N a) := by
  have hdeg : Computable fun p : α × ℕ ↦ 2 * p.2 + e :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_double.to_comp.comp .snd) (.const e)
  have hnum : IsComputableRatMap fun p : α × ℕ ↦ (-1 : ℚ) ^ p.2 * q p.1 ^ (2 * p.2 + e) :=
    ((IsComputableRatMap.const (-1)).pow .snd).mul ((hq.comp .fst).pow hdeg)
  exact IsComputableRatMap.sum_range hN
    (hnum.div (IsComputableRatMap.ofNat (primrec_nat_factorial.to_comp.comp hdeg))).to₂

private lemma abs_pow_div_factorial_le {r : ℝ} {B d : ℕ} (hr : |r| ≤ (B : ℝ)) :
    |r| ^ d / (d.factorial : ℝ) ≤ (2 : ℝ) ^ (4 * B) * (1 / 2 : ℝ) ^ d := by
  have h1 : |r| ^ d / (d.factorial : ℝ) ≤ (B : ℝ) ^ d / (d.factorial : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg r) hr d) (by positivity)
  have h2 : (B : ℝ) ^ d / (d.factorial : ℝ) =
      ((2 * (B : ℝ)) ^ d / (d.factorial : ℝ)) * (1 / 2 : ℝ) ^ d := by
    rw [show (B : ℝ) ^ d = (2 * (B : ℝ)) ^ d * (1 / 2 : ℝ) ^ d by rw [← mul_pow]; ring]; ring
  have hexp : (2 * (B : ℝ)) ^ d / (d.factorial : ℝ) ≤ (2 : ℝ) ^ (4 * B) := by
    calc (2 * (B : ℝ)) ^ d / (d.factorial : ℝ)
        ≤ Real.exp (2 * (B : ℝ)) := Real.pow_div_factorial_le_exp (2 * (B : ℝ)) (by positivity) d
      _ = (Real.exp 1) ^ (2 * B) := by
          rw [show (2 * (B : ℝ)) = ((2 * B : ℕ) : ℝ) * 1 by push_cast; ring, Real.exp_nat_mul]
      _ ≤ (4 : ℝ) ^ (2 * B) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (Real.exp_one_lt_d9.le.trans (by norm_num)) _
      _ = (2 : ℝ) ^ (4 * B) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]; congr 1; ring
  exact h1.trans (h2 ▸ mul_le_mul_of_nonneg_right hexp (by positivity))

private lemma alt_factorial_poly_err {r s : ℝ} {B m e : ℕ} (hr : |r| ≤ (B : ℝ))
    (hs : HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ n * r ^ (2 * n + e) / ((2 * n + e).factorial : ℝ)) s) :
    |s - ∑ n ∈ Finset.range (2 * B + m + 2),
      (-1 : ℝ) ^ n * r ^ (2 * n + e) / ((2 * n + e).factorial : ℝ)| ≤
      (2 : ℝ) ^ (-((m : ℤ) + 1)) := by
  set N := 2 * B + m + 2
  refine (abs_sub_sum_range_le_of_hasSum hs N
    (C := (2 : ℝ) ^ (4 * B) * (1 / 2 : ℝ) ^ (2 * N)) fun k ↦ ?_).trans ?_
  · rw [abs_div, abs_mul, abs_neg_one_pow, one_mul, abs_pow, Nat.abs_cast]
    refine (abs_pow_div_factorial_le hr).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
  · rw [one_div, inv_pow, ← zpow_natCast (2 : ℝ) (4 * B), ← zpow_natCast (2 : ℝ) (2 * N),
      ← zpow_neg, show (2 : ℝ) * ((2 : ℝ) ^ ((4 * B : ℕ) : ℤ) * (2 : ℝ) ^ (-((2 * N : ℕ) : ℤ))) =
        (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ ((4 * B : ℕ) : ℤ) * (2 : ℝ) ^ (-((2 * N : ℕ) : ℤ)) by
        rw [zpow_one, mul_assoc],
      ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    exact zpow_le_zpow_right₀ one_le_two (by dsimp [N]; omega)

private lemma isComputableRealSeq_of_lipschitz_poly {f : ℝ → ℝ} {poly : ℚ → ℕ → ℚ}
    (hpoly : ∀ {q : ℕ × ℕ → ℚ} {N : ℕ × ℕ → ℕ}, IsComputableRatMap q → Computable N →
      IsComputableRatMap fun p ↦ poly (q p) (N p))
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ |x - y|)
    (hrem : ∀ (q : ℚ) (B m : ℕ), |(q : ℝ)| ≤ (B : ℝ) →
      |f (q : ℝ) - (poly q (2 * B + m + 2) : ℝ)| ≤ (2 : ℝ) ^ (-((m : ℤ) + 1)))
    {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun n ↦ f (x n) := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  let B : ℕ → ℕ := fun n ↦ (q n 0).num.natAbs + 2
  let deg : ℕ → ℕ → ℕ := fun n M ↦ 2 * B n + M + 2
  have hB : Computable B :=
    Primrec.nat_add.to_comp.comp
      (primrec_int_natAbs.to_comp.comp (hq.comp .id (.const 0)).num) (.const 2)
  have hdeg : Computable fun p : ℕ × ℕ ↦ deg p.1 p.2 :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Primrec.nat_double.to_comp.comp (hB.comp .fst)) .snd)
      (.const 2)
  have hm1 : Computable fun p : ℕ × ℕ ↦ p.2 + 1 := Computable.succ.comp .snd
  refine isComputableRealSeq_of_rat_le (hpoly (hq.comp .fst hm1) hdeg).to₂ fun n M ↦ ?_
  have hqB : |(q n (M + 1) : ℝ)| ≤ (B n : ℝ) := by
    have h0 : |x n - (q n 0 : ℝ)| < 1 := by simpa using hc n 0
    have h1 : |x n - (q n (M + 1) : ℝ)| < 1 :=
      (hc n (M + 1)).trans_le (zpow_le_one_of_nonpos₀ one_le_two
        (neg_nonpos.mpr (Nat.cast_nonneg _)))
    have ht1 : |(q n (M + 1) : ℝ)| ≤ |(q n (M + 1) : ℝ) - x n| + |x n| := by
      simpa using abs_add_le ((q n (M + 1) : ℝ) - x n) (x n)
    have ht2 : |x n| ≤ |x n - (q n 0 : ℝ)| + |(q n 0 : ℝ)| := by
      simpa using abs_add_le (x n - (q n 0 : ℝ)) (q n 0 : ℝ)
    rw [abs_sub_comm] at ht1
    have hBc : (B n : ℝ) = ((q n 0).num.natAbs : ℝ) + 2 := by dsimp [B]; push_cast; ring
    linarith [abs_rat_le_natAbs_num (q n 0)]
  have h1 : |f (x n) - f (q n (M + 1) : ℝ)| ≤ (2 : ℝ) ^ (-((M : ℤ) + 1)) :=
    (hlip (x n) (q n (M + 1) : ℝ)).trans (by simpa [Nat.cast_add] using (hc n (M + 1)).le)
  have h2 : |f (q n (M + 1) : ℝ) - (poly (q n (M + 1)) (deg n M) : ℝ)| ≤
      (2 : ℝ) ^ (-((M : ℤ) + 1)) := hrem (q n (M + 1)) (B n) M hqB
  have hdouble : (2 : ℝ) ^ (-((M : ℤ) + 1)) + (2 : ℝ) ^ (-((M : ℤ) + 1)) =
      (2 : ℝ) ^ (-(M : ℤ)) := by
    rw [← two_mul, show (2 : ℝ) * (2 : ℝ) ^ (-((M : ℤ) + 1)) =
      (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-((M : ℤ) + 1)) by rw [zpow_one],
      ← zpow_add₀ two_ne_zero]; congr 1; omega
  exact (abs_sub_le _ _ _).trans ((add_le_add h1 h2).trans_eq hdouble)

/-- Termwise sine of a computable real sequence is computable. -/
theorem IsComputableRealSeq.sin {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun n ↦ Real.sin (x n) :=
  isComputableRealSeq_of_lipschitz_poly (computable_altFactorialPoly 1) Real.abs_sin_sub_sin_le
    (fun q _ _ hq ↦ by
      dsimp [altFactorialPoly]; push_cast
      exact alt_factorial_poly_err (e := 1) hq (Real.hasSum_sin q)) hx

/-- Termwise cosine of a computable real sequence is computable. -/
theorem IsComputableRealSeq.cos {x : ℕ → ℝ} (hx : IsComputableRealSeq x) :
    IsComputableRealSeq fun n ↦ Real.cos (x n) :=
  isComputableRealSeq_of_lipschitz_poly (computable_altFactorialPoly 0) Real.abs_cos_sub_cos_le
    (fun q _ _ hq ↦ by
      dsimp [altFactorialPoly]; push_cast
      simpa only [Nat.add_zero] using
        alt_factorial_poly_err (e := 0) hq (by simpa only [Nat.add_zero] using Real.hasSum_cos q))
    hx

/-- Termwise tangent of a computable real sequence is computable away from zeros of `cos`. -/
theorem IsComputableRealSeq.tan {x : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hcos : ∀ n, Real.cos (x n) ≠ 0) : IsComputableRealSeq fun n ↦ Real.tan (x n) := by
  simpa only [Real.tan_eq_sin_div_cos] using hx.sin.div hx.cos hcos

/-- Double-sequence termwise sine is computable. -/
theorem IsComputableRealDoubleSeq.sin {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x) :
    IsComputableRealDoubleSeq fun n k ↦ Real.sin (x n k) :=
  IsComputableRealSeq.sin hx

/-- Double-sequence termwise cosine is computable. -/
theorem IsComputableRealDoubleSeq.cos {x : ℕ → ℕ → ℝ} (hx : IsComputableRealDoubleSeq x) :
    IsComputableRealDoubleSeq fun n k ↦ Real.cos (x n k) :=
  IsComputableRealSeq.cos hx

/-- `Real.sin` preserves computable real numbers. -/
theorem IsComputableReal.sin {x : ℝ} (hx : IsComputableReal x) : IsComputableReal (Real.sin x) :=
  hx.constSeq.sin.apply 0

/-- `Real.cos` preserves computable real numbers. -/
theorem IsComputableReal.cos {x : ℝ} (hx : IsComputableReal x) : IsComputableReal (Real.cos x) :=
  hx.constSeq.cos.apply 0

/-- `Real.tan` preserves computable real numbers away from zeros of `Real.cos`. -/
theorem IsComputableReal.tan {x : ℝ} (hx : IsComputableReal x) (hcos : Real.cos x ≠ 0) :
    IsComputableReal (Real.tan x) :=
  (hx.constSeq.tan fun _ ↦ hcos).apply 0

end SinCosComputability

/-! ### Uniform and pointwise computability of `Real.log` on `(0, ∞)` -/

section LogComputability

private def atanhLogPoly (u : ℚ) (N : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range N, u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)

private lemma computable_atanhLogPoly {α : Type*} [Primcodable α]
    {u : α → ℚ} {N : α → ℕ} (hu : IsComputableRatMap u) (hN : Computable N) :
    IsComputableRatMap fun a ↦ atanhLogPoly (u a) (N a) := by
  have h2k1 : Computable fun p : α × ℕ ↦ 2 * p.2 + 1 :=
    Primrec.nat_double_succ.to_comp.comp .snd
  have hterm : IsComputableRatMap₂ fun (a : α) (k : ℕ) ↦
      u a ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ) :=
    (((hu.comp .fst).pow h2k1).div (IsComputableRatMap.ofNat h2k1)).to₂
  exact (IsComputableRatMap.const 2).mul (IsComputableRatMap.sum_range hN hterm)

private lemma hasSum_log_one_add_div_one_sub {u : ℝ} (hu : |u| < 1) :
    HasSum (fun k : ℕ ↦ 2 * (u ^ (2 * k + 1) / (2 * k + 1 : ℕ)))
      (Real.log ((1 + u) / (1 - u))) := by
  have hpos1 : 0 < 1 + u := by linarith [(abs_lt.mp hu).1]
  have hpos2 : 0 < 1 - u := by linarith [(abs_lt.mp hu).2]
  rw [Real.log_div hpos1.ne' hpos2.ne']
  refine (Real.hasSum_log_sub_log_of_abs_lt_one hu).congr_fun fun k ↦ ?_
  push_cast; ring

private lemma atanhLogPoly_err {u : ℚ} (hu : |(u : ℝ)| ≤ 1 / 2) (N : ℕ) :
    |Real.log ((1 + (u : ℝ)) / (1 - (u : ℝ))) - (atanhLogPoly u (N + 1) : ℝ)| ≤
      (2 : ℝ) ^ (-(N : ℤ)) := by
  have hlt : |(u : ℝ)| < 1 := by linarith
  have hcast : (atanhLogPoly u (N + 1) : ℝ) =
      ∑ k ∈ Finset.range (N + 1), 2 * ((u : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ)) := by
    dsimp [atanhLogPoly]; push_cast; rw [Finset.mul_sum]
  rw [hcast]
  refine (abs_sub_sum_range_le_of_hasSum (hasSum_log_one_add_div_one_sub hlt) (N + 1)
    (C := 2 * (1 / 2 : ℝ) ^ (2 * (N + 1) + 1)) fun j ↦ ?_).trans ?_
  · set k := j + (N + 1)
    have hpos : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (2 * k)
    rw [abs_mul, abs_of_pos two_pos, abs_div, abs_pow, Nat.abs_cast, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ two_pos.le
    calc |(u : ℝ)| ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
        ≤ |(u : ℝ)| ^ (2 * k + 1) := div_le_self (by positivity) hpos
      _ ≤ (1 / 2 : ℝ) ^ (2 * k + 1) := pow_le_pow_left₀ (abs_nonneg _) hu _
      _ ≤ (1 / 2 : ℝ) ^ ((2 * (N + 1) + 1) + j) :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
      _ = (1 / 2 : ℝ) ^ (2 * (N + 1) + 1) * (1 / 2 : ℝ) ^ j := pow_add _ _ _
  · calc 2 * (2 * (1 / 2 : ℝ) ^ (2 * (N + 1) + 1))
        = (1 / 2 : ℝ) ^ (2 * N + 1) := by rw [pow_succ, pow_succ]; ring
      _ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
      _ = (2 : ℝ) ^ (-(N : ℤ)) := by rw [one_div, inv_pow, zpow_neg, zpow_natCast]

/-- The natural logarithm `Real.log 2` is a computable real number. -/
theorem isComputableReal_log_two : IsComputableReal (Real.log 2) := by
  have heq : (2 : ℝ) = (1 + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) := by norm_num
  rw [heq]
  exact isComputableReal_of_rat_le
    (computable_atanhLogPoly (.const (1 / 3 : ℚ)) Computable.succ)
    (atanhLogPoly_err (u := 1 / 3) (by norm_num))

private lemma abs_log_one_add_div_one_sub_lip {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    |Real.log ((1 + a) / (1 - a)) - Real.log ((1 + b) / (1 - b))| ≤ 4 * |a - b| := by
  let g : ℝ → ℝ := fun t ↦ Real.log (1 + t) - Real.log (1 - t)
  have hg_eq : ∀ t : ℝ, |t| ≤ 1 / 2 → Real.log ((1 + t) / (1 - t)) = g t := fun t ht ↦
    Real.log_div (by linarith [(abs_le.mp ht).1]) (by linarith [(abs_le.mp ht).2])
  rw [hg_eq a ha, hg_eq b hb]
  have hderiv : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      HasDerivAt g ((1 + t)⁻¹ + (1 - t)⁻¹) t := fun t ht ↦ by
    have h1 : HasDerivAt (fun s ↦ Real.log (1 + s)) (1 + t)⁻¹ t := by
      have hp : (1 + t) ≠ 0 := by linarith [ht.1]
      simpa [one_div] using ((hasDerivAt_id t).const_add 1).log hp
    have h2 : HasDerivAt (fun s ↦ Real.log (1 - s)) (-(1 - t)⁻¹) t := by
      have hp : (1 - t) ≠ 0 := by linarith [ht.2]
      simpa [neg_div, one_div] using ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log hp
    exact (h1.sub h2).congr_deriv (by rw [sub_neg_eq_add])
  have hbound : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), ‖(1 + t)⁻¹ + (1 - t)⁻¹‖ ≤ 4 := fun t ht ↦ by
    have hp1 : 1 / 2 ≤ 1 + t := by linarith [ht.1]
    have hp2 : 1 / 2 ≤ 1 - t := by linarith [ht.2]
    have hi1 : (1 + t)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hi2 : (1 - t)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc (-1 / 2 : ℝ) (1 / 2))
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) hbound (convex_Icc _ _)
    ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩
    ⟨by linarith [(abs_le.mp ha).1], (abs_le.mp ha).2⟩
  simpa only [Real.norm_eq_abs] using hmv

private lemma isComputableRealSeq_log_reduced {u : ℕ → ℝ} (hu : IsComputableRealSeq u)
    (hub : ∀ n, |u n| ≤ 1 / 2) :
    IsComputableRealSeq fun n ↦ Real.log ((1 + u n) / (1 - u n)) := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hu
  let r : ℕ → ℕ → ℚ := fun n M ↦ Max.max (-1 / 2 : ℚ) (Min.min (1 / 2 : ℚ) (q n (M + 3)))
  have hm3 : Computable fun p : ℕ × ℕ ↦ p.2 + 3 :=
    Primrec.nat_add.to_comp.comp .snd (.const 3)
  have hr : IsComputableRatMap fun p : ℕ × ℕ ↦ r p.1 p.2 :=
    (IsComputableRatMap.const (-1 / 2)).max
      ((IsComputableRatMap.const (1 / 2)).min (hq.comp .fst hm3))
  have hm2 : Computable fun p : ℕ × ℕ ↦ p.2 + 2 :=
    Primrec.nat_add.to_comp.comp .snd (.const 2)
  refine isComputableRealSeq_of_rat_le (computable_atanhLogPoly hr hm2).to₂ fun n M ↦ ?_
  have hr_abs : |(r n M : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    have hlo : (-1 / 2 : ℚ) ≤ r n M := le_max_left _ _
    have hhi : r n M ≤ (1 / 2 : ℚ) := max_le (by norm_num) (min_le_left _ _)
    exact ⟨by have h := (Rat.cast_le (K := ℝ)).mpr hlo; norm_num at h; linarith,
      by have h := (Rat.cast_le (K := ℝ)).mpr hhi; norm_num at h; linarith⟩
  have hur : |u n - (r n M : ℝ)| ≤ (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) := by
    have hqerr := (hc n (M + 3)).le
    have hu_le := abs_le.mp (hub n)
    have hrc : (r n M : ℝ) = max (-1 / 2 : ℝ) (min (1 / 2 : ℝ) (q n (M + 3) : ℝ)) := by
      dsimp [r]; push_cast; norm_num
    rw [hrc, abs_le]
    have hqe := abs_le.mp hqerr
    constructor
    · have : min (1 / 2 : ℝ) (q n (M + 3) : ℝ) ≤ u n + (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) :=
        (min_le_right _ _).trans (by linarith [hqe.1])
      have hp2 : (0 : ℝ) < (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have : max (-1 / 2 : ℝ) (min (1 / 2 : ℝ) (q n (M + 3) : ℝ)) ≤
          u n + (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) :=
        max_le (by linarith [hu_le.1, hp2]) this
      linarith
    · have hp2 : (0 : ℝ) < (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have : u n - (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) ≤ min (1 / 2 : ℝ) (q n (M + 3) : ℝ) :=
        le_min (by linarith [hu_le.2, hp2]) (by linarith [hqe.2])
      have : u n - (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) ≤
          max (-1 / 2 : ℝ) (min (1 / 2 : ℝ) (q n (M + 3) : ℝ)) :=
        this.trans (le_max_right _ _)
      linarith
  have h1 : |Real.log ((1 + u n) / (1 - u n)) -
      Real.log ((1 + (r n M : ℝ)) / (1 - (r n M : ℝ)))| ≤ (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := by
    refine (abs_log_one_add_div_one_sub_lip (hub n) hr_abs).trans ?_
    calc 4 * |u n - (r n M : ℝ)|
        ≤ (2 : ℝ) ^ (2 : ℤ) * (2 : ℝ) ^ (-((M + 3 : ℕ) : ℤ)) := by
          have h4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
          rw [h4]; linarith
      _ = (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) := by
          rw [← zpow_add₀ two_ne_zero]; congr 1
  have h2 : |Real.log ((1 + (r n M : ℝ)) / (1 - (r n M : ℝ))) -
      (atanhLogPoly (r n M) (M + 2) : ℝ)| ≤ (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) :=
    atanhLogPoly_err hr_abs (M + 1)
  have hsum : (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(M : ℤ)) := by
    rw [← two_mul, show (2 : ℝ) * (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-((M + 1 : ℕ) : ℤ)) by rw [zpow_one],
      ← zpow_add₀ two_ne_zero]; congr 1; omega
  exact (abs_sub_le _ _ _).trans ((add_le_add h1 h2).trans_eq hsum)

/-- Termwise natural logarithm of a strictly positive computable real sequence is computable. -/
theorem IsComputableRealSeq.log {x : ℕ → ℝ} (hx : IsComputableRealSeq x)
    (hpos : ∀ n, 0 < x n) : IsComputableRealSeq fun n ↦ Real.log (x n) := by
  obtain ⟨q, hq, hc⟩ := isComputableRealSeq_iff_exists_rat_approx.mp hx
  let prec : ℤ → ℕ := fun z ↦ z.natAbs + 4
  let good : ℕ → ℕ → Bool := fun n k ↦
    let z := Denumerable.ofNat ℤ k
    let app := q n (prec z) * (2 : ℚ) ^ (-z)
    decide ((3 / 4 : ℚ) < app ∧ app < (7 / 4 : ℚ))
  have hz : Computable fun p : ℕ × ℕ ↦ Denumerable.ofNat ℤ p.2 :=
    (Computable.ofNat ℤ).comp .snd
  have hprec : Computable fun p : ℕ × ℕ ↦ prec (Denumerable.ofNat ℤ p.2) :=
    Primrec.nat_add.to_comp.comp (primrec_int_natAbs.to_comp.comp hz) (.const 4)
  have happ : IsComputableRatMap fun p : ℕ × ℕ ↦
      q p.1 (prec (Denumerable.ofNat ℤ p.2)) * (2 : ℚ) ^ (-Denumerable.ofNat ℤ p.2) :=
    (hq.comp .fst hprec).mul
      ((IsComputableRatMap.const 2).zpow (primrec_int_neg.to_comp.comp hz))
  have hgood : Computable₂ good :=
    (Primrec.and.to_comp.comp
      ((IsComputableRatMap.const (3 / 4)).decide_lt happ)
      (happ.decide_lt (.const (7 / 4)))).to₂
  have hex : ∀ n : ℕ, ∃ k : ℕ, good n k = true := fun n ↦ by
    -- Choose `z = ⌊log₂ (x n)⌋` so `1 ≤ x n * 2 ^ (-z) < 2`, or shift by `1`.
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    set t0 : ℝ := Real.log (x n) / Real.log 2
    have h2t0 : (2 : ℝ) ^ t0 = x n := by
      rw [Real.rpow_def_of_pos two_pos, mul_div_cancel₀ _ hlog2_pos.ne', Real.exp_log (hpos n)]
    set z0 : ℤ := Int.floor t0
    have hlo0 : (2 : ℝ) ^ z0 ≤ x n := by
      rw [← Real.rpow_intCast 2 z0, ← h2t0]
      exact (Real.rpow_le_rpow_left_iff one_lt_two).mpr (Int.floor_le t0)
    have hhi0 : x n < (2 : ℝ) ^ (z0 + 1) := by
      rw [← Real.rpow_intCast 2 (z0 + 1), ← h2t0]
      exact (Real.rpow_lt_rpow_left_iff one_lt_two).mpr (by push_cast; exact Int.lt_floor_add_one _)
    have hy0_lo : (1 : ℝ) ≤ x n * (2 : ℝ) ^ (-z0) := by
      rw [zpow_neg, ← div_eq_mul_inv, one_le_div (zpow_pos two_pos z0)]; exact hlo0
    have hy0_hi : x n * (2 : ℝ) ^ (-z0) < 2 := by
      rw [zpow_neg, ← div_eq_mul_inv, div_lt_iff₀ (zpow_pos two_pos z0)]
      rwa [zpow_add₀ two_ne_zero, zpow_one, mul_comm] at hhi0
    obtain ⟨z, hz_lo, hz_hi⟩ : ∃ z : ℤ,
        (13 / 16 : ℝ) ≤ x n * (2 : ℝ) ^ (-z) ∧ x n * (2 : ℝ) ^ (-z) ≤ (13 / 8 : ℝ) := by
      by_cases h : x n * (2 : ℝ) ^ (-z0) ≤ 13 / 8
      · exact ⟨z0, by linarith, h⟩
      · have hhalf : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
        have hgt : 13 / 8 < x n * (2 : ℝ) ^ (-z0) := lt_of_not_ge h
        refine ⟨z0 + 1, ?_, ?_⟩
        · rw [show -(z0 + 1) = -z0 + (-1 : ℤ) by omega, zpow_add₀ two_ne_zero, ← mul_assoc, hhalf]
          linarith
        · rw [show -(z0 + 1) = -z0 + (-1 : ℤ) by omega, zpow_add₀ two_ne_zero, ← mul_assoc, hhalf]
          linarith
    refine ⟨Encodable.encode z, ?_⟩
    dsimp only [good]
    rw [Denumerable.ofNat_encode, decide_eq_true_eq]
    have herr : |x n * (2 : ℝ) ^ (-z) - ((q n (prec z) * (2 : ℚ) ^ (-z) : ℚ) : ℝ)| < 1 / 16 := by
      have hpz : |(2 : ℝ) ^ (-z)| = (2 : ℝ) ^ (-z) :=
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) (-z))
      rw [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, ← sub_mul, abs_mul, hpz]
      calc |x n - (q n (prec z) : ℝ)| * (2 : ℝ) ^ (-z)
          < (2 : ℝ) ^ (-(prec z : ℤ)) * (2 : ℝ) ^ (-z) :=
            mul_lt_mul_of_pos_right (hc n (prec z)) (zpow_pos two_pos (-z))
        _ = (2 : ℝ) ^ (-(prec z : ℤ) + -z) := (zpow_add₀ two_ne_zero _ _).symm
        _ ≤ (2 : ℝ) ^ (-4 : ℤ) := by
            refine zpow_le_zpow_right₀ one_le_two ?_
            have : -z ≤ (z.natAbs : ℤ) := (neg_le_abs z).trans_eq (Int.natCast_natAbs z).symm
            dsimp [prec]; omega
        _ = 1 / 16 := by norm_num
    have he := abs_lt.mp herr
    refine ⟨(Rat.cast_lt (K := ℝ)).mp ?_, (Rat.cast_lt (K := ℝ)).mp ?_⟩
    · have hc34 : (((3 / 4 : ℚ) : ℝ)) = 3 / 4 := by norm_num
      linarith
    · have hc74 : (((7 / 4 : ℚ) : ℝ)) = 7 / 4 := by norm_num
      linarith
  let zSeq : ℕ → ℤ := fun n ↦ Denumerable.ofNat ℤ (Nat.find (hex n))
  have hzSeq : Computable zSeq :=
    (Computable.ofNat ℤ).comp <| Partrec.of_eq_tot (Partrec.rfind hgood.partrec₂) fun n ↦
      nat_find_mem_rfind (hex n)
  let scaleSeq : ℕ → ℝ := fun n ↦ (((2 : ℚ) ^ (-zSeq n) : ℚ) : ℝ)
  have hscale : IsComputableRealSeq scaleSeq := by
    simpa [scaleSeq] using isComputableRealSeq_rat <|
      (IsComputableRatMap.const 2).zpow (primrec_int_neg.to_comp.comp hzSeq)
  let y : ℕ → ℝ := fun n ↦ x n * scaleSeq n
  have hy_comp : IsComputableRealSeq y := hx.mul hscale
  have hy_bounds : ∀ n : ℕ, (11 / 16 : ℝ) < y n ∧ y n < (29 / 16 : ℝ) := fun n ↦ by
    have hsp : (3 / 4 : ℚ) < q n (prec (zSeq n)) * (2 : ℚ) ^ (-zSeq n) ∧
        q n (prec (zSeq n)) * (2 : ℚ) ^ (-zSeq n) < (7 / 4 : ℚ) := by
      simpa [good, zSeq] using Nat.find_spec (hex n)
    have hspr : (3 / 4 : ℝ) < ((q n (prec (zSeq n)) * (2 : ℚ) ^ (-zSeq n) : ℚ) : ℝ) ∧
        ((q n (prec (zSeq n)) * (2 : ℚ) ^ (-zSeq n) : ℚ) : ℝ) < (7 / 4 : ℝ) :=
      ⟨by simpa using (Rat.cast_lt (K := ℝ)).mpr hsp.1,
        by simpa using (Rat.cast_lt (K := ℝ)).mpr hsp.2⟩
    have herr : |y n - ((q n (prec (zSeq n)) * (2 : ℚ) ^ (-zSeq n) : ℚ) : ℝ)| < 1 / 16 := by
      have hpz : |(2 : ℝ) ^ (-zSeq n)| = (2 : ℝ) ^ (-zSeq n) :=
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) (-zSeq n))
      dsimp only [y, scaleSeq]
      rw [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, ← sub_mul, abs_mul, hpz]
      calc |x n - (q n (prec (zSeq n)) : ℝ)| * (2 : ℝ) ^ (-zSeq n)
          < (2 : ℝ) ^ (-(prec (zSeq n) : ℤ)) * (2 : ℝ) ^ (-zSeq n) :=
            mul_lt_mul_of_pos_right (hc n (prec (zSeq n))) (zpow_pos two_pos _)
        _ = (2 : ℝ) ^ (-(prec (zSeq n) : ℤ) + -zSeq n) := (zpow_add₀ two_ne_zero _ _).symm
        _ ≤ (2 : ℝ) ^ (-4 : ℤ) := by
            refine zpow_le_zpow_right₀ one_le_two ?_
            have : -zSeq n ≤ ((zSeq n).natAbs : ℤ) :=
              (neg_le_abs _).trans_eq (Int.natCast_natAbs _).symm
            dsimp [prec]; omega
        _ = 1 / 16 := by norm_num
    have he := abs_lt.mp herr
    exact ⟨by linarith [hspr.1, he.1], by linarith [hspr.2, he.2]⟩
  let u : ℕ → ℝ := fun n ↦ (y n - 1) / (y n + 1)
  have hu_comp : IsComputableRealSeq u :=
    (hy_comp.sub isComputableReal_one.constSeq).div
      (hy_comp.add isComputableReal_one.constSeq) fun n ↦ by linarith [(hy_bounds n).1]
  have hu_abs : ∀ n : ℕ, |u n| ≤ 1 / 2 := fun n ↦ by
    have hb := hy_bounds n
    dsimp [u]; rw [abs_le]
    constructor <;> [rw [le_div_iff₀ (by linarith)]; rw [div_le_iff₀ (by linarith)]] <;> linarith
  have hz_real : IsComputableRealSeq fun n ↦ (zSeq n : ℝ) := isComputableRealSeq_int hzSeq
  refine ((hz_real.mul isComputableReal_log_two.constSeq).add
    (isComputableRealSeq_log_reduced hu_comp hu_abs)).of_eq fun n ↦ ?_
  have hy_pos : 0 < y n := by linarith [(hy_bounds n).1]
  have hu_eq : (1 + u n) / (1 - u n) = y n := by
    dsimp [u]
    have h1 : y n + 1 ≠ 0 := by linarith
    have h2 : 1 - (y n - 1) / (y n + 1) ≠ 0 := by
      rw [one_sub_div h1]; ring_nf; positivity
    field_simp; ring
  have hx_eq : x n = y n * (2 : ℝ) ^ (zSeq n) := by
    dsimp [y, scaleSeq]; push_cast
    rw [mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, mul_one]
  rw [hu_eq, hx_eq, Real.log_mul hy_pos.ne' (zpow_pos two_pos _).ne', Real.log_zpow]
  ring

/-- `Real.log` preserves strictly positive computable real numbers. -/
theorem IsComputableReal.log {x : ℝ} (hx : IsComputableReal x) (hpos : 0 < x) :
    IsComputableReal (Real.log x) :=
  (hx.constSeq.log fun _ ↦ hpos).apply 0

/-- The sequence `n ↦ Real.log (n + 2)` is a computable sequence of positive real numbers. -/
theorem isComputableRealSeq_log_nat_add_two :
    IsComputableRealSeq fun n ↦ Real.log ((n + 2 : ℕ) : ℝ) :=
  (isComputableRealSeq_nat (Primrec.nat_add.to_comp.comp .id (.const 2))).log fun n ↦ by positivity

end LogComputability

end CslibFrontier.ComputableAnalysis
