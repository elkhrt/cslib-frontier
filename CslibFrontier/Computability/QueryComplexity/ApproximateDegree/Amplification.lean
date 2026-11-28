/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Polynomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Error Amplification for Approximate Polynomial Degree of Boolean Functions

This module formalizes uniform polynomial error reduction (amplification) for approximate polynomial
degree of Boolean functions on `{0, 1}^n` via univariate Bernstein majority polynomials.

Given a real polynomial `p` of degree at most `D` satisfying `|p(x) - f(x)| ≤ δ` for all
`x ∈ {0, 1}^n` with `0 ≤ δ < 1 / 2`, the affine normalization `u(x) = (p(x) + δ) / (1 + 2δ)` maps
values into `[0, 1]`, sending `f(x) = 0` into `[0, p₀]` and `f(x) = 1` into `[1 - p₀, 1]` where
`p₀ = 2δ / (1 + 2δ) < 1 / 2`. Composing `u` with the odd-degree Bernstein majority polynomial
`M_r(X) = ∑_{i=0}^r C(2r + 1, r + 1 + i) X^{r + 1 + i} (1 - X)^{r - i}` of degree at most `2r + 1`
amplifies the pointwise error exponentially in `r`, yielding `adeg_ε(f) ≤ 220 * adeg_{1/3}(f) *
log(1 / ε)` for `0 < ε < 1 / 2`.

## Main definitions

* `CslibFrontier.QueryComplexity.bernsteinMajorityPoly`: univariate Bernstein majority polynomial of
  parameter `r` and degree at most `2r + 1`.

## Main results

* `CslibFrontier.QueryComplexity.natDegree_bernsteinMajorityPoly_le`:
  `bernsteinMajorityPoly r` has degree at most `2r + 1`.
* `CslibFrontier.QueryComplexity.eval_bernsteinMajorityPoly_one_sub`: reflection symmetry
  `M_r(1 - u) = 1 - M_r(u)`.
* `CslibFrontier.QueryComplexity.eval_bernsteinMajorityPoly_le_exp`: Chernoff tail bound
  `M_r(u) ≤ exp(-r (1 - 2p₀)² / 3)` for `0 ≤ u ≤ p₀ < 1 / 2`.
* `CslibFrontier.QueryComplexity.approxDegree_le_of_approx_lt_half`: general `δ → ε` amplification
  for `0 ≤ δ < 1 / 2`.
* `CslibFrontier.QueryComplexity.approxDegree_one_third_le_mul_eleven_twentyfifths`: constant-error
  amplification `adeg_{1/3}(f) ≤ 2949 * adeg_{11/25}(f)`.
* `CslibFrontier.QueryComplexity.approxDegree_le_mul_log_inv`: general `1/3 → ε` error reduction
  `adeg_ε(f) ≤ 220 * adeg_{1/3}(f) * log(1 / ε)` for `0 < ε < 1 / 2`.
-/

public section

open Finset Polynomial
open scoped NNReal

namespace CslibFrontier.QueryComplexity

/-- Univariate Bernstein majority polynomial of parameter `r`:
`M_r(X) = ∑_{i=0}^r C(2r + 1, r + 1 + i) X^{r + 1 + i} (1 - X)^{r - i}`. -/
noncomputable def bernsteinMajorityPoly (r : ℕ) : Polynomial ℝ :=
  ∑ i ∈ range (r + 1),
    C (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * X ^ (r + 1 + i) * (1 - X) ^ (r - i)

/-- `bernsteinMajorityPoly r` has degree at most `2 * r + 1`. -/
theorem natDegree_bernsteinMajorityPoly_le (r : ℕ) :
    (bernsteinMajorityPoly r).natDegree ≤ 2 * r + 1 := by
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi ↦ ?_⟩
  have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have h1X : (1 - X : Polynomial ℝ).natDegree ≤ 1 := by
    refine (natDegree_sub_le 1 X).trans ?_
    simp [natDegree_one]
  have hpow2 : ((1 - X : Polynomial ℝ) ^ (r - i)).natDegree ≤ r - i :=
    (natDegree_pow_le (p := 1 - X) (n := r - i)).trans
      ((Nat.mul_le_mul_left (r - i) h1X).trans_eq (Nat.mul_one _))
  have hmul1 :
      (C (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * X ^ (r + 1 + i)).natDegree ≤ r + 1 + i := by
    refine (natDegree_mul_le (p := C _) (q := X ^ (r + 1 + i))).trans ?_
    have hX := natDegree_X_pow_le (R := ℝ) (r + 1 + i)
    simp only [natDegree_C, zero_add]
    exact hX
  refine (natDegree_mul_le (p := C _ * X ^ (r + 1 + i)) (q := (1 - X) ^ (r - i))).trans ?_
  omega

/-- Pointwise evaluation formula for `bernsteinMajorityPoly r`. -/
theorem eval_bernsteinMajorityPoly (r : ℕ) (u : ℝ) :
    (bernsteinMajorityPoly r).eval u =
      ∑ i ∈ range (r + 1),
        (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) * (1 - u) ^ (r - i) := by
  change (evalRingHom u) (bernsteinMajorityPoly r) = _
  simp [bernsteinMajorityPoly]

/-- Nonnegativity of `bernsteinMajorityPoly r` on `[0, 1]`. -/
theorem eval_bernsteinMajorityPoly_nonneg (r : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (bernsteinMajorityPoly r).eval u := by
  rw [eval_bernsteinMajorityPoly]
  refine sum_nonneg fun i _ ↦ ?_
  have h1u : 0 ≤ 1 - u := by linarith
  positivity

/-- Reflection symmetry `M_r(1 - u) = 1 - M_r(u)` from expanding `(u + (1 - u)) ^ (2r + 1)`. -/
theorem eval_bernsteinMajorityPoly_one_sub (r : ℕ) (u : ℝ) :
    (bernsteinMajorityPoly r).eval (1 - u) = 1 - (bernsteinMajorityPoly r).eval u := by
  have hbin :
      ∑ j ∈ range (2 * r + 2),
        (((2 * r + 1).choose j : ℕ) : ℝ) * u ^ j * (1 - u) ^ (2 * r + 1 - j) = 1 := by
    have h := add_pow u (1 - u) (2 * r + 1)
    rw [add_sub_cancel, one_pow, show 2 * r + 1 + 1 = 2 * r + 2 by omega] at h
    refine (sum_congr rfl fun j _ ↦ ?_).trans h.symm
    ring
  have hsplit : (r + 1) + (r + 1) = 2 * r + 2 := by omega
  rw [← hsplit, sum_range_add _ (r + 1) (r + 1)] at hbin
  have hleft :
      (bernsteinMajorityPoly r).eval (1 - u) =
        ∑ j ∈ range (r + 1),
          (((2 * r + 1).choose j : ℕ) : ℝ) * u ^ j * (1 - u) ^ (2 * r + 1 - j) := by
    rw [eval_bernsteinMajorityPoly]
    simp only [sub_sub_cancel]
    have hrefl :=
      (sum_range_reflect
        (fun i ↦
          (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * (1 - u) ^ (r + 1 + i) * u ^ (r - i))
        (r + 1)).symm
    simp only [Nat.add_sub_cancel_right] at hrefl
    rw [hrefl]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hsub1 : r + 1 + (r - j) = 2 * r + 1 - j := by omega
    have hsub2 : r - (r - j) = j := by omega
    have hch : (2 * r + 1).choose (2 * r + 1 - j) = (2 * r + 1).choose j :=
      Nat.choose_symm (by omega)
    rw [hsub1, hsub2, hch]
    ring
  have hright :
      (bernsteinMajorityPoly r).eval u =
        ∑ i ∈ range (r + 1),
          (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) *
            (1 - u) ^ (2 * r + 1 - (r + 1 + i)) := by
    rw [eval_bernsteinMajorityPoly]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hsub : 2 * r + 1 - (r + 1 + i) = r - i := by omega
    rw [hsub]
  linarith

/-- `bernsteinMajorityPoly r` is bounded above by `1` on `[0, 1]`. -/
theorem eval_bernsteinMajorityPoly_le_one (r : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (bernsteinMajorityPoly r).eval u ≤ 1 := by
  have h := eval_bernsteinMajorityPoly_nonneg r (u := 1 - u) (by linarith) (by linarith)
  rw [eval_bernsteinMajorityPoly_one_sub] at h
  linarith

/-- Exponential Chernoff tail bound for `bernsteinMajorityPoly r` on `[0, p₀]` when `p₀ < 1 / 2`. -/
theorem eval_bernsteinMajorityPoly_le_exp (r : ℕ) {u p₀ : ℝ}
    (hu0 : 0 ≤ u) (hup : u ≤ p₀) (hp₀ : p₀ < 1 / 2) :
    (bernsteinMajorityPoly r).eval u ≤ Real.exp (-(r : ℝ) * (1 - 2 * p₀) ^ 2 / 3) := by
  have hu1 : u ≤ 1 := by linarith
  have h1u : 0 ≤ 1 - u := by linarith
  set lam : ℝ := 3 - 4 * p₀
  have hlam1 : 1 < lam := by dsimp [lam]; linarith
  have hlam_pos : 0 < lam := by linarith
  have hdom :
      lam ^ (r + 1) * (bernsteinMajorityPoly r).eval u ≤
        (1 + (lam - 1) * p₀) ^ (2 * r + 1) := by
    rw [eval_bernsteinMajorityPoly, mul_sum]
    have hsplit : (r + 1) + (r + 1) = 2 * r + 2 := by omega
    have hbin :
        ∑ j ∈ range (2 * r + 2),
          (((2 * r + 1).choose j : ℕ) : ℝ) * (lam * u) ^ j * (1 - u) ^ (2 * r + 1 - j) =
            (1 + (lam - 1) * u) ^ (2 * r + 1) := by
      have h := add_pow (lam * u) (1 - u) (2 * r + 1)
      have heq : lam * u + (1 - u) = 1 + (lam - 1) * u := by ring
      rw [heq, show 2 * r + 1 + 1 = 2 * r + 2 by omega] at h
      rw [h]
      refine sum_congr rfl fun j _ ↦ ?_
      ring
    have hnonneg_left :
        0 ≤ ∑ j ∈ range (r + 1),
          (((2 * r + 1).choose j : ℕ) : ℝ) * (lam * u) ^ j * (1 - u) ^ (2 * r + 1 - j) :=
      sum_nonneg fun j _ ↦ by positivity
    have hterm_le :
        ∑ i ∈ range (r + 1),
          lam ^ (r + 1) *
            ((((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) * (1 - u) ^ (r - i)) ≤
        ∑ i ∈ range (r + 1),
          (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * (lam * u) ^ (r + 1 + i) *
            (1 - u) ^ (2 * r + 1 - (r + 1 + i)) := by
      refine sum_le_sum fun i hi ↦ ?_
      have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hsub : 2 * r + 1 - (r + 1 + i) = r - i := by omega
      rw [hsub, mul_pow]
      have hpow : lam ^ (r + 1) ≤ lam ^ (r + 1 + i) :=
        pow_le_pow_right₀ hlam1.le (by omega)
      have hrest :
          0 ≤ (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) * (1 - u) ^ (r - i) := by
        positivity
      calc lam ^ (r + 1) *
            ((((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) * (1 - u) ^ (r - i))
          ≤ lam ^ (r + 1 + i) *
              ((((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) * (1 - u) ^ (r - i)) :=
            mul_le_mul_of_nonneg_right hpow hrest
        _ = (((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) *
              (lam ^ (r + 1 + i) * u ^ (r + 1 + i)) * (1 - u) ^ (r - i) := by ring
    have hsum_le :
        ∑ i ∈ range (r + 1),
          lam ^ (r + 1) *
            ((((2 * r + 1).choose (r + 1 + i) : ℕ) : ℝ) * u ^ (r + 1 + i) * (1 - u) ^ (r - i)) ≤
        (1 + (lam - 1) * u) ^ (2 * r + 1) := by
      rw [← hbin, ← hsplit, sum_range_add _ (r + 1) (r + 1)]
      linarith
    refine hsum_le.trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have hlam_sub : 0 ≤ lam - 1 := by linarith
    nlinarith
  have hp₀_nonneg : 0 ≤ p₀ := le_trans hu0 hup
  have hfac1 : 1 + (lam - 1) * p₀ ≤ lam := by
    have hdiff : lam - (1 + (lam - 1) * p₀) = 2 * (1 - p₀) * (1 - 2 * p₀) := by
      dsimp [lam]; ring
    nlinarith
  have hfac2 : (1 + (lam - 1) * p₀) ^ 2 ≤ lam * (1 - (1 - 2 * p₀) ^ 2 / 3) := by
    have hlam_le3 : lam ≤ 3 := by dsimp [lam]; linarith
    have hid :
        lam - (1 + (lam - 1) * p₀) ^ 2 = 2 * (1 - 2 * p₀) ^ 2 * (1 - 2 * p₀ ^ 2) := by
      dsimp [lam]; ring
    have hp2 : 2 * p₀ ^ 2 ≤ 1 / 2 := by nlinarith
    have h1 : (1 - 2 * p₀) ^ 2 ≤ lam - (1 + (lam - 1) * p₀) ^ 2 := by nlinarith
    have h2 : lam * ((1 - 2 * p₀) ^ 2 / 3) ≤ (1 - 2 * p₀) ^ 2 := by
      have hsq : 0 ≤ (1 - 2 * p₀) ^ 2 := sq_nonneg _
      nlinarith
    linarith
  have hpow_comb :
      (1 + (lam - 1) * p₀) ^ (2 * r + 1) ≤
        lam ^ (r + 1) * (1 - (1 - 2 * p₀) ^ 2 / 3) ^ r := by
    calc (1 + (lam - 1) * p₀) ^ (2 * r + 1)
        = (1 + (lam - 1) * p₀) * ((1 + (lam - 1) * p₀) ^ 2) ^ r := by
          rw [← pow_mul, pow_succ']
      _ ≤ lam * (lam * (1 - (1 - 2 * p₀) ^ 2 / 3)) ^ r := by
          refine mul_le_mul hfac1 (pow_le_pow_left₀ (sq_nonneg _) hfac2 r)
            (pow_nonneg (sq_nonneg _) r) hlam_pos.le
      _ = lam ^ (r + 1) * (1 - (1 - 2 * p₀) ^ 2 / 3) ^ r := by
          rw [mul_pow, pow_succ']; ring
  have hdiv :
      (bernsteinMajorityPoly r).eval u ≤ (1 - (1 - 2 * p₀) ^ 2 / 3) ^ r := by
    have hcomb := hdom.trans hpow_comb
    exact le_of_mul_le_mul_left hcomb (pow_pos hlam_pos (r + 1))
  have hexp1 : 1 - (1 - 2 * p₀) ^ 2 / 3 ≤ Real.exp (-(1 - 2 * p₀) ^ 2 / 3) := by
    have h := Real.add_one_le_exp (-(1 - 2 * p₀) ^ 2 / 3)
    linarith
  have h1_nonneg : 0 ≤ 1 - (1 - 2 * p₀) ^ 2 / 3 := by
    have : (1 - 2 * p₀) ^ 2 ≤ 1 := by nlinarith
    linarith
  refine hdiv.trans ?_
  calc (1 - (1 - 2 * p₀) ^ 2 / 3) ^ r
      ≤ (Real.exp (-(1 - 2 * p₀) ^ 2 / 3)) ^ r := pow_le_pow_left₀ h1_nonneg hexp1 r
    _ = Real.exp (-(r : ℝ) * (1 - 2 * p₀) ^ 2 / 3) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- General polynomial error amplification: if `p` has degree at most `D` and approximates a
Boolean function `f` within `δ < 1 / 2`, and `r` satisfies
`exp(-r ((1 - 2δ) / (1 + 2δ))² / 3) ≤ ε`, then `adeg_ε(f) ≤ (2r + 1) * D`. -/
theorem approxDegree_le_of_mem_lowDegree_lt_half {n D : ℕ} {f : Cslib.BooleanFunction n}
    {p : Cslib.BitString n → ℝ} (hp : p ∈ Cslib.BitString.lowDegree ℝ (Fin n) D)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hpf : ∀ x, |p x - Cslib.BitString.bitVal ℝ (f x)| ≤ δ)
    {ε : ℝ≥0} (r : ℕ)
    (hr : Real.exp (-(r : ℝ) * ((1 - 2 * δ) / (1 + 2 * δ)) ^ 2 / 3) ≤ (ε : ℝ)) :
    Cslib.QueryComplexity.approxDegree ε f ≤ (2 * r + 1) * D := by
  have hden : 0 < 1 + 2 * δ := by linarith
  set u : Cslib.BitString n → ℝ := fun x ↦ (p x + δ) / (1 + 2 * δ)
  have hu_mem : u ∈ Cslib.BitString.lowDegree ℝ (Fin n) D := by
    have h1 : (fun x ↦ p x + δ) ∈ Cslib.BitString.lowDegree ℝ (Fin n) D :=
      Submodule.add_mem _ hp (Cslib.BitString.const_mem_lowDegree D δ)
    have heq : u = (1 / (1 + 2 * δ)) • fun x ↦ p x + δ := by
      funext x; simp [u, div_eq_inv_mul]
    rw [heq]
    exact Submodule.smul_mem _ _ h1
  set q : Cslib.BitString n → ℝ := fun x ↦ (bernsteinMajorityPoly r).eval (u x)
  have hq_mem : q ∈ Cslib.BitString.lowDegree ℝ (Fin n) ((2 * r + 1) * D) :=
    Cslib.BitString.polynomial_eval_mem_lowDegree hu_mem (natDegree_bernsteinMajorityPoly_le r)
  refine Cslib.QueryComplexity.approxDegree_le_of_mem_lowDegree hq_mem fun x ↦ ?_
  set p₀ : ℝ := 2 * δ / (1 + 2 * δ)
  have hp₀ : p₀ < 1 / 2 := by
    dsimp [p₀]
    rw [div_lt_iff₀ hden]
    linarith
  have hgap : 1 - 2 * p₀ = (1 - 2 * δ) / (1 + 2 * δ) := by
    dsimp [p₀]
    field_simp
    ring
  have habs := abs_le.mp (hpf x)
  cases hfx : f x with
  | false =>
    simp only [hfx, Cslib.BitString.bitVal_false, sub_zero] at habs ⊢
    have hu0 : 0 ≤ u x := by
      dsimp [u]; exact div_nonneg (by linarith) hden.le
    have hup : u x ≤ p₀ := by
      dsimp [u, p₀]; exact div_le_div_of_nonneg_right (by linarith) hden.le
    have hq0 : 0 ≤ q x := eval_bernsteinMajorityPoly_nonneg r hu0 (by linarith)
    have hq_le : q x ≤ (ε : ℝ) := by
      have hb := eval_bernsteinMajorityPoly_le_exp r hu0 hup hp₀
      rw [hgap] at hb
      exact hb.trans hr
    exact abs_le.mpr ⟨by linarith [ε.coe_nonneg], hq_le⟩
  | true =>
    simp only [hfx, Cslib.BitString.bitVal_true] at habs ⊢
    have h1u0 : 0 ≤ 1 - u x := by
      have : 1 - u x = (1 + δ - p x) / (1 + 2 * δ) := by dsimp [u]; field_simp; ring
      rw [this]; exact div_nonneg (by linarith) hden.le
    have h1up : 1 - u x ≤ p₀ := by
      have : 1 - u x = (1 + δ - p x) / (1 + 2 * δ) := by dsimp [u]; field_simp; ring
      rw [this]; dsimp [p₀]; exact div_le_div_of_nonneg_right (by linarith) hden.le
    have hu0 : 0 ≤ u x := by
      dsimp [u]; exact div_nonneg (by linarith) hden.le
    have hu1 : u x ≤ 1 := by linarith
    have hq1 : q x ≤ 1 := eval_bernsteinMajorityPoly_le_one r hu0 hu1
    have h1q_le : 1 - q x = (bernsteinMajorityPoly r).eval (1 - u x) := by
      dsimp [q]; rw [eval_bernsteinMajorityPoly_one_sub]
    have h1q_bound : 1 - q x ≤ (ε : ℝ) := by
      rw [h1q_le]
      have hb := eval_bernsteinMajorityPoly_le_exp r h1u0 h1up hp₀
      rw [hgap] at hb
      exact hb.trans hr
    exact abs_le.mpr ⟨by linarith, by linarith [ε.coe_nonneg]⟩

/-- General `δ → ε` approximate-degree amplification for `0 ≤ δ < 1 / 2`. -/
theorem approxDegree_le_of_approx_lt_half {n : ℕ} (f : Cslib.BooleanFunction n)
    {δ ε : ℝ≥0} (hδ : (δ : ℝ) < 1 / 2) (r : ℕ)
    (hr : Real.exp (-(r : ℝ) * ((1 - 2 * (δ : ℝ)) / (1 + 2 * (δ : ℝ))) ^ 2 / 3) ≤ (ε : ℝ)) :
    Cslib.QueryComplexity.approxDegree ε f ≤
      (2 * r + 1) * Cslib.QueryComplexity.approxDegree δ f := by
  obtain ⟨p, hp, hpf⟩ := Cslib.QueryComplexity.exists_mem_lowDegree_approxDegree (ε := δ) (f := f)
  exact approxDegree_le_of_mem_lowDegree_lt_half hp δ.coe_nonneg hδ hpf r hr

/-- Constant-factor amplification from `11 / 25` error to `1 / 3` error:
`adeg_{1/3}(f) ≤ 2949 * adeg_{11/25}(f)`. -/
theorem approxDegree_one_third_le_mul_eleven_twentyfifths {n : ℕ} (f : Cslib.BooleanFunction n) :
    Cslib.QueryComplexity.approxDegree (1 / 3) f ≤
      2949 * Cslib.QueryComplexity.approxDegree (11 / 25) f := by
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp 1]
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [this]
      nlinarith
    linarith
  have hexp :
      Real.exp (-(1474 : ℝ) * ((1 - 2 * ((11 / 25 : ℝ≥0) : ℝ)) /
        (1 + 2 * ((11 / 25 : ℝ≥0) : ℝ))) ^ 2 / 3) ≤ ((1 / 3 : ℝ≥0) : ℝ) := by
    have hexp_le :
        -(1474 : ℝ) * ((1 - 2 * ((11 / 25 : ℝ≥0) : ℝ)) /
          (1 + 2 * ((11 / 25 : ℝ≥0) : ℝ))) ^ 2 / 3 ≤ -2 := by
      push_cast; norm_num
    have hmon := Real.exp_le_exp.mpr hexp_le
    rw [Real.exp_neg] at hmon
    have hp2 : 0 < Real.exp 2 := Real.exp_pos 2
    have hinv2 : Real.exp 2 * (Real.exp 2)⁻¹ = 1 := mul_inv_cancel₀ hp2.ne'
    have hinv_pos : 0 ≤ (Real.exp 2)⁻¹ := inv_nonneg.mpr hp2.le
    have hinv : (Real.exp 2)⁻¹ ≤ (1 / 3 : ℝ) := by nlinarith
    have h13 : ((1 / 3 : ℝ≥0) : ℝ) = 1 / 3 := by push_cast; norm_num
    rw [h13]
    exact hmon.trans hinv
  have h := approxDegree_le_of_approx_lt_half f (δ := 11 / 25) (ε := 1 / 3)
    (by push_cast; norm_num) 1474 hexp
  simpa using h

/-- Error reduction for approximate polynomial degree: for every `0 < ε < 1 / 2` and every Boolean
function `f`, `adeg_ε(f) ≤ 220 * adeg_{1/3}(f) * log(1 / ε)`. -/
theorem approxDegree_le_mul_log_inv {n : ℕ} (f : Cslib.BooleanFunction n)
    {ε : ℝ≥0} (hε0 : 0 < (ε : ℝ)) (hε : (ε : ℝ) < 1 / 2) :
    (Cslib.QueryComplexity.approxDegree ε f : ℝ) ≤
      220 * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) * Real.log (1 / (ε : ℝ)) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h1 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2))⁻¹ := by
      have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
      rw [Real.exp_neg] at h
      linarith
    have hp : 0 < Real.exp (1 / 2) := Real.exp_pos (1 / 2)
    have hinv : Real.exp (1 / 2) * (Real.exp (1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    have h2 : Real.exp (1 / 2) ≤ 2 := by nlinarith
    have hexp1 : Real.exp (1 / 2) ≤ Real.exp (Real.log 2) := by
      rwa [Real.exp_log (by norm_num)]
    exact Real.exp_le_exp.mp hexp1
  have hinv_gt2 : 2 < 1 / (ε : ℝ) := by
    rw [lt_div_iff₀ hε0]
    linarith
  have hlog_ge : 1 / 2 ≤ Real.log (1 / (ε : ℝ)) :=
    hlog2.trans (Real.log_le_log (by norm_num) hinv_gt2.le)
  set r : ℕ := Nat.ceil (75 * Real.log (1 / (ε : ℝ)))
  have hr_ge : 75 * Real.log (1 / (ε : ℝ)) ≤ (r : ℝ) := Nat.le_ceil _
  have hr_le : (r : ℝ) ≤ 75 * Real.log (1 / (ε : ℝ)) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hexp :
      Real.exp (-(r : ℝ) * ((1 - 2 * ((1 / 3 : ℝ≥0) : ℝ)) /
        (1 + 2 * ((1 / 3 : ℝ≥0) : ℝ))) ^ 2 / 3) ≤ (ε : ℝ) := by
    have hsim :
        ((1 - 2 * ((1 / 3 : ℝ≥0) : ℝ)) / (1 + 2 * ((1 / 3 : ℝ≥0) : ℝ))) ^ 2 =
          1 / 25 := by
      push_cast; norm_num
    rw [hsim]
    have h1 : -(r : ℝ) * (1 / 25) / 3 ≤ -Real.log (1 / (ε : ℝ)) := by linarith
    have h2 := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-Real.log (1 / (ε : ℝ))) = (ε : ℝ) := by
      rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε0]
    rwa [h3] at h2
  have hdeg := approxDegree_le_of_approx_lt_half f (δ := 1 / 3) (ε := ε)
    (by push_cast; norm_num) r hexp
  have hdegR :
      (Cslib.QueryComplexity.approxDegree ε f : ℝ) ≤
        (2 * (r : ℝ) + 1) * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) := by
    exact_mod_cast hdeg
  have hcoef : 2 * (r : ℝ) + 1 ≤ 220 * Real.log (1 / (ε : ℝ)) := by
    linarith
  have hadeg_nonneg : (0 : ℝ) ≤ Cslib.QueryComplexity.approxDegree (1 / 3) f :=
    Nat.cast_nonneg _
  nlinarith

end CslibFrontier.QueryComplexity
