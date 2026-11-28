module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Interval.Set.Defs
import CslibFrontier.Foundations.Analysis.MarkovBrothersInequality
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# Complex-Ellipse Bounds and the Coppersmith–Rivlin Growth Bound

Proves an elementary complex-polynomial Maximum Modulus Principle via roots-of-unity coefficient
extraction and tensor powering, Bernstein's complex ellipse and disk inequalities, a Cauchy
Hasse-derivative estimate, and the Coppersmith–Rivlin growth bound
`|q(x)| ≤ 4 B exp(5000 d² / n)` on `[0, n]` for real polynomials bounded by `B` on `{0, …, n}`.

## Main results

* `CslibFrontier.Foundations.Analysis.norm_coeff_le_of_forall_norm_one`: roots-of-unity
  coefficient bound for complex polynomials bounded on the unit circle.
* `CslibFrontier.Foundations.Analysis.norm_eval_le_of_forall_norm_one`: elementary Maximum
  Modulus Principle for complex polynomials on the closed unit disk.
* `CslibFrontier.Foundations.Analysis.complex_ellipse_bound`,
  `CslibFrontier.Foundations.Analysis.complex_disk_bound`: Bernstein's complex ellipse and disk
  growth bounds.
* `CslibFrontier.Foundations.Analysis.abs_eval_hasseDeriv_le`: Cauchy Hasse-derivative estimate.
* `CslibFrontier.Foundations.Analysis.prod_abs_sub_node_eq`: exact factorial formula
  `∏_{j ≠ i} |i - j| = i! * (m - i)!` on consecutive integer nodes.
* `CslibFrontier.Foundations.Analysis.coppersmith_rivlin_bound`: Coppersmith–Rivlin bound
  `|q(x)| ≤ 4 B exp(5000 d² / n)` for `q.natDegree ≤ d ≤ n`.
-/

public section

namespace CslibFrontier.Foundations.Analysis

open Finset Polynomial Real
open Set (Icc)
open scoped BigOperators

/-! ### Elementary Complex-Ellipse Bound and Coppersmith–Rivlin Growth Bound -/

section CoppersmithRivlin

/-- Evaluating a real polynomial mapped to `ℂ` at a real scalar agrees with real evaluation. -/
private theorem eval_map_ofReal (p : ℝ[X]) (r : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (r : ℂ) = ((p.eval r : ℝ) : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => simp [hp₁, hp₂]
  | monomial k a => simp

/-- Coefficient formula for composing a polynomial with `C c * X`. -/
private theorem coeff_comp_C_mul_X {R : Type*} [CommRing R] (P : R[X]) (c : R) (r : ℕ) :
    (P.comp (C c * X)).coeff r = P.coeff r * c ^ r := by
  induction P using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => simp [add_comp, hp₁, hp₂, add_mul]
  | monomial k a =>
    rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow,
      coeff_monomial]
    by_cases h : r = k
    · subst h; simp
    · simp [h]

/-- **Roots-of-unity coefficient bound**: if `R : ℂ[X]` has degree at most `K` and satisfies
`‖R.eval ζ‖ ≤ B` (`0 ≤ B`) on the unit circle `‖ζ‖ = 1`, then `‖R.coeff k‖ ≤ B` for every `k`. -/
theorem norm_coeff_le_of_forall_norm_one {K : ℕ} {R : ℂ[X]} (hR : R.natDegree ≤ K)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖R.eval ζ‖ ≤ B) (k : ℕ) :
    ‖R.coeff k‖ ≤ B := by
  by_cases hk : K < k
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hR hk), norm_zero]; exact hB
  push Not at hk
  set N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hω_norm (m : ℕ) : ‖ω ^ m‖ = 1 := by
    rw [norm_pow]
    have harg : 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) =
      ((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [show ω = Complex.exp _ from rfl, harg, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hω_pow_N : ω ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have harg : (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I := by
      field_simp [hNne]
    rw [harg, Complex.exp_two_pi_mul_I]
  -- Orthogonality: `∑_{j < N} ω ^ (j * m) = if N ∣ m then N else 0`.
  have horth (m : ℕ) (hm1 : 0 < m) (hm2 : m < 2 * N) (hmN : m ≠ N) :
      ∑ j ∈ range N, (ω ^ m) ^ j = 0 := by
    have hne : ω ^ m ≠ 1 := by
      intro heq
      rw [← Complex.exp_nat_mul] at heq
      rw [Complex.exp_eq_one_iff] at heq
      obtain ⟨z, hz⟩ := heq
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hzm : (m : ℂ) = (z : ℂ) * (N : ℂ) := by
        have h1 : ((m : ℂ) / (N : ℂ)) * (2 * Real.pi * Complex.I) =
            (z : ℂ) * (2 * Real.pi * Complex.I) := by
          convert hz using 1; ring
        have h2 := mul_right_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hI) h1
        exact (div_eq_iff hNne).mp h2
      have hzm_int : (m : ℤ) = z * (N : ℤ) := by exact_mod_cast hzm
      have hdiv : (N : ℤ) ∣ (m : ℤ) := ⟨z, by linarith⟩
      have hdiv_nat : N ∣ m := Int.ofNat_dvd.mp hdiv
      obtain ⟨q, hq⟩ := hdiv_nat
      rcases q with _ | _ | q
      · have hm0 : m = 0 := by simpa using hq
        omega
      · exact hmN (by simpa using hq)
      · nlinarith
    rw [geom_sum_eq hne, ← pow_mul, mul_comm m N, pow_mul, hω_pow_N, one_pow, sub_self, zero_div]
  -- Extract `R.coeff k` by averaging `R.eval (ω ^ j) * ω ^ (j * (N - k))`.
  have hextract : ∑ j ∈ range N, R.eval (ω ^ j) * ω ^ (j * (N - k)) = (N : ℂ) * R.coeff k := by
    have heval (j : ℕ) : R.eval (ω ^ j) = ∑ t ∈ range N, R.coeff t * (ω ^ j) ^ t :=
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hR) (ω ^ j)
    simp_rw [heval, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single k]
    · calc ∑ j ∈ range N, R.coeff k * (ω ^ j) ^ k * ω ^ (j * (N - k))
          = ∑ j ∈ range N, R.coeff k * ((ω ^ N) ^ j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← pow_mul, mul_assoc, ← pow_add, ← mul_add, Nat.add_sub_of_le (by omega : k ≤ N),
                mul_comm j N, pow_mul]
        _ = (N : ℂ) * R.coeff k := by simp [hω_pow_N, mul_comm]
    · intro t ht htk
      have htlt : t < N := mem_range.mp ht
      calc ∑ j ∈ range N, R.coeff t * (ω ^ j) ^ t * ω ^ (j * (N - k))
          = R.coeff t * ∑ j ∈ range N, (ω ^ (t + (N - k))) ^ j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [mul_assoc, ← pow_mul, ← pow_add, ← mul_add, mul_comm j, pow_mul]
        _ = 0 := by
              rw [horth (t + (N - k)) (by omega) (by omega) (by omega), mul_zero]
    · intro hnot; exact absurd (mem_range.mpr (by omega)) hnot
  have hnorm_eq : (N : ℝ) * ‖R.coeff k‖ = ‖∑ j ∈ range N, R.eval (ω ^ j) * ω ^ (j * (N - k))‖ := by
    rw [hextract, norm_mul, Complex.norm_natCast]
  have hnorm_le : ‖∑ j ∈ range N, R.eval (ω ^ j) * ω ^ (j * (N - k))‖ ≤ (N : ℝ) * B := by
    calc ‖∑ j ∈ range N, R.eval (ω ^ j) * ω ^ (j * (N - k))‖
        ≤ ∑ j ∈ range N, ‖R.eval (ω ^ j) * ω ^ (j * (N - k))‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range N, B := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, hω_norm (j * (N - k)), mul_one]
          exact hbound (ω ^ j) (hω_norm j)
      _ = (N : ℝ) * B := by simp
  nlinarith

/-- **Elementary Maximum Modulus Principle for complex polynomials** on the unit disk, proved via
roots-of-unity coefficient extraction and tensor powering. -/
theorem norm_eval_le_of_forall_norm_one (Q : ℂ[X]) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖Q.eval ζ‖ ≤ M) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖Q.eval u‖ ≤ M := by
  by_contra hlt
  push Not at hlt
  have hpow_bound (m : ℕ) (hm : 1 ≤ m) :
      ‖Q.eval u‖ ^ m ≤ ((m * Q.natDegree + 1 : ℕ) : ℝ) * M ^ m := by
    have hdeg : (Q ^ m).natDegree ≤ m * Q.natDegree := natDegree_pow_le
    have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖(Q ^ m).eval ζ‖ ≤ M ^ m := fun ζ hζ => by
      rw [eval_pow, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound ζ hζ) m
    rw [← norm_pow, ← eval_pow, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
    calc ‖∑ k ∈ range (m * Q.natDegree + 1), (Q ^ m).coeff k * u ^ k‖
        ≤ ∑ k ∈ range (m * Q.natDegree + 1), ‖(Q ^ m).coeff k * u ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (m * Q.natDegree + 1), M ^ m := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_right (by positivity)
            (pow_le_one₀ (norm_nonneg u) hu) |>.trans'
            (mul_le_mul_of_nonneg_right
              (norm_coeff_le_of_forall_norm_one hdeg (by positivity) hcirc k)
              (by positivity))
      _ = ((m * Q.natDegree + 1 : ℕ) : ℝ) * M ^ m := by simp
  rcases eq_or_lt_of_le hM with rfl | hMpos
  · have h1 : ‖Q.eval u‖ ≤ 0 := by
      have h := hpow_bound 1 le_rfl
      simpa using h
    linarith
  · set ε : ℝ := ‖Q.eval u‖ / M - 1
    have hε : 0 < ε := by
      have : 1 < ‖Q.eval u‖ / M := (one_lt_div hMpos).mpr hlt
      linarith
    set m : ℕ := Nat.ceil (2 * ((Q.natDegree + 1 : ℕ) : ℝ) / ε ^ 2) + 2
    have hm1 : 1 ≤ m := by omega
    have hm_bound := hpow_bound m hm1
    have hQu : ‖Q.eval u‖ = M * (1 + ε) := by simp only [ε]; field_simp; ring
    rw [hQu, mul_pow] at hm_bound
    have h1 : (1 + ε) ^ m ≤ ((m * Q.natDegree + 1 : ℕ) : ℝ) := by
      have hMpow : 0 < M ^ m := pow_pos hMpos m
      nlinarith
    have h2 : ((m.choose 2 : ℕ) : ℝ) * ε ^ 2 + 1 ≤ (1 + ε) ^ m := by
      rw [add_comm 1 ε, add_pow]
      have h02 : (0 : ℕ) ≠ 2 := by decide
      have h0mem : 0 ∈ range (m + 1) := mem_range.mpr (by omega)
      have h2mem : 2 ∈ range (m + 1) := mem_range.mpr (by omega)
      have hpair : ({0, 2} : Finset ℕ) ⊆ range (m + 1) := by
        intro t ht; simp only [mem_insert,
          mem_singleton] at ht; rcases ht with rfl | rfl <;> assumption
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hpair (f :=
        fun k => ε ^ k * 1 ^ (m - k) * (m.choose k : ℝ))
        (fun _ _ _ => by positivity)
      rw [Finset.sum_pair h02] at hsum
      simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one] at hsum ⊢
      linarith
    have hch2 : ((m.choose 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
      have hnat : 2 * m.choose 2 = m * (m - 1) := by
        rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd]
      have hcast : (2 : ℝ) * (m.choose 2 : ℝ) = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sub hm1, Nat.cast_one] at hcast
      linarith
    have hm_large : 2 * ((Q.natDegree + 1 : ℕ) : ℝ) / ε ^ 2 < (m : ℝ) - 1 := by
      have hceil : 2 * ((Q.natDegree + 1 : ℕ) : ℝ) / ε ^ 2 ≤
          (Nat.ceil (2 * ((Q.natDegree + 1 : ℕ) : ℝ) / ε ^ 2) : ℝ) := Nat.le_ceil _
      have hm_eq : (m : ℝ) = (Nat.ceil (2 * ((Q.natDegree + 1 : ℕ) : ℝ) / ε ^ 2) : ℝ) + 2 := by
        simp [m]
      linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hprod : ((m : ℝ) * ((Q.natDegree : ℝ) + 1)) < ((m.choose 2 : ℕ) : ℝ) * ε ^ 2 := by
      rw [hch2]
      have hmul := mul_lt_mul_of_pos_right hm_large (pow_pos hε 2)
      rw [div_mul_cancel₀ _ (pow_pos hε 2).ne'] at hmul
      push_cast at hmul
      nlinarith
    push_cast at h1
    linarith

/-- **Bernstein's Lemma on complex ellipses**: if `p : ℝ[X]` has degree at most `d` and
`|p.eval x| ≤ M` on `[-1, 1]`, then `‖(p.map ℝ→ℂ).eval ((w + w⁻¹) / 2)‖ ≤ M * ‖w‖ ^ d` for
every `w : ℂ` with `1 ≤ ‖w‖`. -/
theorem complex_ellipse_bound {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖(p.map (algebraMap ℝ ℂ)).eval ((w + w⁻¹) / 2)‖ ≤ M * ‖w‖ ^ d := by
  let Q : ℂ[X] := ∑ j ∈ range (d + 1),
    C ((p.coeff j : ℝ) : ℂ) * X ^ (d - j) * ((X ^ 2 + 1) * C (2⁻¹ : ℂ)) ^ j
  have hQ_eval (u : ℂ) (hu : u ≠ 0) :
      Q.eval u = u ^ d * (p.map (algebraMap ℝ ℂ)).eval ((u + u⁻¹) / 2) := by
    have hdeg_map : (p.map (algebraMap ℝ ℂ)).natDegree ≤ d := natDegree_map_le.trans hp
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_map), Finset.mul_sum]
    simp only [Q, eval_finsetSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X, coeff_map,
      Complex.coe_algebraMap]
    have hpow : u ^ (d - j) * ((u ^ 2 + 1) * 2⁻¹) ^ j = u ^ d * ((u + u⁻¹) / 2) ^ j := by
      have h1 : (u ^ 2 + 1) * 2⁻¹ = u * ((u + u⁻¹) / 2) := by field_simp
      rw [h1, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj_le]
    rw [mul_assoc, hpow]
    ring
  have hQ_circ : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖Q.eval ζ‖ ≤ M := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζ
    rw [hQ_eval ζ hζ0, norm_mul, norm_pow, hζ, one_pow, one_mul]
    have hinv : ζ⁻¹ = starRingEnd ℂ ζ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ, one_pow, inv_one, Complex.ofReal_one,
        mul_one]
    have hreal : (ζ + ζ⁻¹) / 2 = (ζ.re : ℂ) := by
      rw [hinv, Complex.add_conj]
      push_cast; ring
    rw [hreal, eval_map_ofReal, Complex.norm_real, Real.norm_eq_abs]
    have hre : ζ.re ∈ Icc (-1 : ℝ) 1 := by
      have habs : |ζ.re| ≤ 1 := (Complex.abs_re_le_norm ζ).trans_eq hζ
      exact abs_le.mp habs
    exact hbound ζ.re hre
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw; linarith
  have hwinv : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hw
  have hQ_winv := norm_eval_le_of_forall_norm_one Q hM hQ_circ hwinv
  rw [hQ_eval w⁻¹ (inv_ne_zero hw0), inv_inv, add_comm w⁻¹ w, norm_mul, norm_pow,
    norm_inv] at hQ_winv
  have hpow_pos : (0 : ℝ) < ‖w‖ ^ d := pow_pos (by linarith) d
  rw [inv_pow] at hQ_winv
  have hmul := mul_le_mul_of_nonneg_left hQ_winv hpow_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hpow_pos.ne', one_mul, mul_comm (‖w‖ ^ d) M] at hmul
  exact hmul

/-- **Bernstein disk bound**: if `p : ℝ[X]` has degree at most `d`, `|p| ≤ M` on `[-1, 1]`,
`ξ ∈ [-1, 1]`, and `‖z - ξ‖ ≤ ρ` with `0 ≤ ρ ≤ 1 / 2`, then
`‖(p.map ℝ→ℂ).eval z‖ ≤ M * exp (3 * d * √ρ)`. -/
theorem complex_disk_bound {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) {z : ℂ} (hz : ‖z - (ξ : ℂ)‖ ≤ ρ) :
    ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ≤ M * Real.exp (3 * (d : ℝ) * √ρ) := by
  -- Find `s : ℂ` with `s ^ 2 = z ^ 2 - 1` explicitly in Cartesian coordinates.
  let u : ℂ := z ^ 2 - 1
  have hu_re : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
  have hplus_nn : 0 ≤ (‖u‖ + u.re) / 2 := by linarith [(abs_le.mp hu_re).1]
  have hminus_nn : 0 ≤ (‖u‖ - u.re) / 2 := by linarith [(abs_le.mp hu_re).2]
  let a : ℝ := √((‖u‖ + u.re) / 2)
  let b : ℝ := (if 0 ≤ u.im then (1 : ℝ) else -1) * √((‖u‖ - u.re) / 2)
  let s : ℂ := ⟨a, b⟩
  have hs2 : s ^ 2 = z ^ 2 - 1 := by
    have ha2 : a ^ 2 = (‖u‖ + u.re) / 2 := Real.sq_sqrt hplus_nn
    have hb2 : b ^ 2 = (‖u‖ - u.re) / 2 := by
      simp only [b, mul_pow]
      have hsgn : (if 0 ≤ u.im then (1 : ℝ) else -1) ^ 2 = 1 := by split_ifs <;> norm_num
      rw [hsgn, one_mul, Real.sq_sqrt hminus_nn]
    have hab_sq : (2 * a * b) ^ 2 = u.im ^ 2 := by
      have hnorm : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      calc (2 * a * b) ^ 2 = 4 * a ^ 2 * b ^ 2 := by ring
        _ = 4 * ((‖u‖ + u.re) / 2) * ((‖u‖ - u.re) / 2) := by rw [ha2, hb2]
        _ = ‖u‖ ^ 2 - u.re ^ 2 := by ring
        _ = u.im ^ 2 := by linarith
    have hab : 2 * a * b = u.im := by
      rcases le_or_gt 0 u.im with him | him
      · have hnn : 0 ≤ 2 * a * b := by
          simp only [b, him, ↓reduceIte, one_mul]
          exact mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        nlinarith
      · have hnp : 2 * a * b ≤ 0 := by
          have hnot : ¬ 0 ≤ u.im := not_le.mpr him
          simp only [b, hnot, ↓reduceIte, neg_one_mul]
          have : 0 ≤ 2 * a * √((‖u‖ - u.re) / 2) :=
            mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
          linarith
        nlinarith
    change s ^ 2 = u
    apply Complex.ext
    · simp only [s, sq, Complex.mul_re]
      nlinarith
    · simp only [s, sq, Complex.mul_im]
      linarith
  let w₁ : ℂ := z + s
  let w₂ : ℂ := z - s
  have hw12 : w₁ * w₂ = 1 := by
    have : w₁ * w₂ = z ^ 2 - s ^ 2 := by simp only [w₁, w₂]; ring
    rw [this, hs2]; ring
  have hw1_ne : w₁ ≠ 0 := left_ne_zero_of_mul_eq_one hw12
  have hw2_ne : w₂ ≠ 0 := right_ne_zero_of_mul_eq_one hw12
  have hw_ex : ∃ w : ℂ, 1 ≤ ‖w‖ ∧ (w + w⁻¹) / 2 = z := by
    rcases le_or_gt 1 ‖w₁‖ with h1 | h1
    · refine ⟨w₁, h1, ?_⟩
      have hinv : w₁⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hw12
      rw [hinv]; simp only [w₁, w₂]; ring
    · refine ⟨w₂, ?_, ?_⟩
      · have hprod : ‖w₁‖ * ‖w₂‖ = 1 := by rw [← norm_mul, hw12, norm_one]
        have hw1pos : 0 < ‖w₁‖ := norm_pos_iff.mpr hw1_ne
        nlinarith
      · have hinv : w₂⁻¹ = w₁ := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hw12)
        rw [hinv]; simp only [w₁, w₂]; ring
  obtain ⟨w, hw1, hwz⟩ := hw_ex
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw1; linarith
  have hw_pos : 0 < ‖w‖ := by linarith
  -- Ellipse identity: `‖w‖ + ‖w‖⁻¹ = ‖z - 1‖ + ‖z + 1‖`.
  have hellipse : ‖w‖ + ‖w‖⁻¹ = ‖z - 1‖ + ‖z + 1‖ := by
    have h1 : (w - 1) ^ 2 = 2 * w * (z - 1) := by rw [← hwz]; field_simp; ring
    have h2 : (w + 1) ^ 2 = 2 * w * (z + 1) := by rw [← hwz]; field_simp; ring
    have hn1 : ‖w - 1‖ ^ 2 = 2 * ‖w‖ * ‖z - 1‖ := by
      rw [← norm_pow, h1, norm_mul, norm_mul, Complex.norm_ofNat]
    have hn2 : ‖w + 1‖ ^ 2 = 2 * ‖w‖ * ‖z + 1‖ := by
      rw [← norm_pow, h2, norm_mul, norm_mul, Complex.norm_ofNat]
    have hpar : ‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2 = 2 * ‖w‖ ^ 2 + 2 := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      ring
    have hmul : 2 * ‖w‖ * (‖z - 1‖ + ‖z + 1‖) = 2 * ‖w‖ ^ 2 + 2 := by linarith
    have hmul' : 2 * ‖w‖ * (‖w‖ + ‖w‖⁻¹) = 2 * ‖w‖ ^ 2 + 2 := by field_simp
    nlinarith
  -- Triangle inequality: `‖z - 1‖ + ‖z + 1‖ ≤ 2 + 2 * ρ`.
  have htri : ‖z - 1‖ + ‖z + 1‖ ≤ 2 + 2 * ρ := by
    have h1 : ‖z - 1‖ ≤ ‖z - (ξ : ℂ)‖ + |ξ - 1| := by
      have : z - 1 = (z - (ξ : ℂ)) + ((ξ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact (norm_add_le _ _).trans_eq (by rw [Complex.norm_real, Real.norm_eq_abs])
    have h2 : ‖z + 1‖ ≤ ‖z - (ξ : ℂ)‖ + |ξ + 1| := by
      have : z + 1 = (z - (ξ : ℂ)) + ((ξ + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact (norm_add_le _ _).trans_eq (by rw [Complex.norm_real, Real.norm_eq_abs])
    have hξ1 : |ξ - 1| = 1 - ξ := by rw [abs_of_nonpos (by linarith [hξ.2])]; ring
    have hξ2 : |ξ + 1| = ξ + 1 := abs_of_nonneg (by linarith [hξ.1])
    linarith
  have hw_le3 : ‖w‖ ≤ 3 := by
    have : 0 ≤ ‖w‖⁻¹ := inv_nonneg.mpr hw_pos.le
    linarith
  have hw_sub_sq : (‖w‖ - 1) ^ 2 ≤ 6 * ρ := by
    have h1 : (‖w‖ - 1) ^ 2 / ‖w‖ = ‖w‖ + ‖w‖⁻¹ - 2 := by field_simp; ring
    have h2 : (‖w‖ - 1) ^ 2 / ‖w‖ ≤ 2 * ρ := by linarith
    have h3 : (‖w‖ - 1) ^ 2 ≤ 2 * ρ * ‖w‖ := (div_le_iff₀ hw_pos).mp h2
    nlinarith
  have hw_le_exp : ‖w‖ ≤ Real.exp (3 * √ρ) := by
    have hsub : ‖w‖ - 1 ≤ 3 * √ρ := by
      have hsq : (‖w‖ - 1) ^ 2 ≤ (3 * √ρ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hρ0]; linarith
      nlinarith [Real.sqrt_nonneg ρ]
    linarith [Real.add_one_le_exp (3 * √ρ)]
  have hpow_le : ‖w‖ ^ d ≤ Real.exp (3 * (d : ℝ) * √ρ) := by
    calc ‖w‖ ^ d ≤ (Real.exp (3 * √ρ)) ^ d := pow_le_pow_left₀ hw_pos.le hw_le_exp d
      _ = Real.exp ((d : ℝ) * (3 * √ρ)) := (Real.exp_nat_mul _ d).symm
      _ = Real.exp (3 * (d : ℝ) * √ρ) := by ring_nf
  rw [← hwz]
  exact (complex_ellipse_bound hp hM hbound hw1).trans
    (mul_le_mul_of_nonneg_left hpow_le hM)

/-- **Cauchy derivative bound via roots of unity**: if `p : ℝ[X]` has degree at most `d`,
`|p| ≤ M` on `[-1, 1]`, `ξ ∈ [-1, 1]`, and `0 < ρ ≤ 1 / 2`, then
`|(hasseDeriv r p).eval ξ| ≤ M * exp (3 * d * √ρ) / ρ ^ r`. -/
theorem abs_eval_hasseDeriv_le {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) (r : ℕ) :
    |(hasseDeriv r p).eval ξ| ≤ M * Real.exp (3 * (d : ℝ) * √ρ) / ρ ^ r := by
  let R : ℂ[X] := (p.map (algebraMap ℝ ℂ)).comp (C (ρ : ℂ) * X + C (ξ : ℂ))
  have hR_deg : R.natDegree ≤ d := by
    refine natDegree_comp_le.trans ?_
    have h1 : (p.map (algebraMap ℝ ℂ)).natDegree ≤ d := natDegree_map_le.trans hp
    have h2 : (C (ρ : ℂ) * X + C (ξ : ℂ)).natDegree ≤ 1 := natDegree_linear_le
    nlinarith
  have hR_circ : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖R.eval ζ‖ ≤ M * Real.exp (3 * (d : ℝ) * √ρ) := by
    intro ζ hζ
    have hev : R.eval ζ = (p.map (algebraMap ℝ ℂ)).eval ((ρ : ℂ) * ζ + (ξ : ℂ)) := by
      simp [R]
    rw [hev]
    refine complex_disk_bound hp hM hbound hξ hρ0.le hρhalf ?_
    have hsub : (ρ : ℂ) * ζ + (ξ : ℂ) - (ξ : ℂ) = (ρ : ℂ) * ζ := by ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hζ, mul_one]
  have hR_coeff : R.coeff r = (((hasseDeriv r p).eval ξ : ℝ) : ℂ) * (ρ : ℂ) ^ r := by
    have hcomp : R = (taylor (ξ : ℂ) (p.map (algebraMap ℝ ℂ))).comp (C (ρ : ℂ) * X) := by
      simp [R, taylor_apply, comp_assoc]
    rw [hcomp, coeff_comp_C_mul_X, taylor_coeff, hasseDeriv_map, eval_map_ofReal]
  have hc := norm_coeff_le_of_forall_norm_one hR_deg (by positivity) hR_circ r
  rw [hR_coeff, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ0] at hc
  exact (le_div_iff₀ (pow_pos hρ0 r)).mpr hc

/-- Auxiliary factorial inequality: `a! * b! ≤ (a + b - 1)!` for `a ≥ 1, b ≥ 1`. -/
private theorem factorial_mul_factorial_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a.factorial * b.factorial ≤ (a + b - 1).factorial := by
  induction a, ha using Nat.le_induction with
  | base =>
    simp only [Nat.factorial_one, one_mul, Nat.add_sub_cancel_left]
    exact le_rfl
  | succ a ha ih =>
    have heq : a + 1 + b - 1 = (a + b - 1) + 1 := by omega
    rw [heq, Nat.factorial_succ (a + b - 1), Nat.factorial_succ a, mul_assoc]
    have hle : a + 1 ≤ (a + b - 1) + 1 := by omega
    exact Nat.mul_le_mul hle ih

/-- Bounding `∏_{j ∈ (range (m + 1)).erase i} |x - (a + j)| ≤ m!` for `x ∈ [a, a + m]` and
`i ≤ m`. -/
private theorem prod_abs_sub_le_factorial {m : ℕ} {a x : ℝ} (hx : x ∈ Icc a (a + m))
    {i : ℕ} (hi : i ≤ m) :
    ∏ j ∈ (range (m + 1)).erase i, |x - (a + (j : ℝ))| ≤ (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hi0 : i = 0 := by omega
    subst hi0
    simp
  -- Let `t := min ⌊x - a⌋₊ (m - 1)` so `a + t ≤ x ≤ a + t + 1` and `t + 1 ≤ m`.
  set t : ℕ := min ⌊x - a⌋₊ (m - 1)
  have ht_lt : t < m := by omega
  have ht_le : a + (t : ℝ) ≤ x := by
    have h1 : (t : ℝ) ≤ (⌊x - a⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
    have h2 : (⌊x - a⌋₊ : ℝ) ≤ x - a := Nat.floor_le (by linarith [hx.1])
    linarith
  have hx_le : x ≤ a + (t : ℝ) + 1 := by
    rcases le_or_gt ⌊x - a⌋₊ (m - 1) with hmin | hmin
    · have ht_eq : t = ⌊x - a⌋₊ := min_eq_left hmin
      rw [ht_eq]
      have := Nat.lt_floor_add_one (x - a)
      linarith
    · have ht_eq : t = m - 1 := min_eq_right hmin.le
      rw [ht_eq, Nat.cast_sub hm, Nat.cast_one]
      linarith [hx.2]
  -- Split `range (m + 1)` into `j ≤ t` (`Icc 0 t`) and `j ≥ t + 1` (`Icc (t + 1) m`).
  have hfactor (j : ℕ) (hj : j ≤ m) :
      |x - (a + (j : ℝ))| ≤ if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ) := by
    split_ifs with hjt
    · have hjR : (j : ℝ) ≤ (t : ℝ) := by exact_mod_cast hjt
      rw [abs_of_nonneg (by linarith), Nat.cast_sub (by omega : j ≤ t + 1)]
      push_cast; linarith
    · have hjR : (t : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : t + 1 ≤ j)
      rw [abs_of_nonpos (by linarith), neg_sub, Nat.cast_sub (by omega : t ≤ j)]
      linarith
  have hpos_rhs (j : ℕ) :
      0 ≤ (if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ)) := by
    split_ifs <;> positivity
  have hge1_rhs (j : ℕ) (hj : j ≤ m) :
      1 ≤ (if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ)) := by
    split_ifs with hjt
    · exact_mod_cast (by omega : 1 ≤ t + 1 - j)
    · exact_mod_cast (by omega : 1 ≤ j - t)
  calc ∏ j ∈ (range (m + 1)).erase i, |x - (a + (j : ℝ))|
      ≤ ∏ j ∈ (range (m + 1)).erase i,
          (if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ)) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
            fun j hj => hfactor j (Nat.lt_succ_iff.mp (mem_range.mp (mem_of_mem_erase hj)))
    _ ≤ ∏ j ∈ range (m + 1),
          (if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ)) := by
          rw [← Finset.mul_prod_erase (range (m + 1)) _ (mem_range.mpr (Nat.lt_succ_of_le hi))]
          exact le_mul_of_one_le_left (Finset.prod_nonneg fun j _ => hpos_rhs j) (hge1_rhs i hi)
    _ = ((t + 1).factorial : ℝ) * ((m - t).factorial : ℝ) := by
          have hpart : range (m + 1) = range (t + 1) ∪ Icc (t + 1) m := by
            ext j; simp only [mem_range, mem_union, mem_Icc]; omega
          have hdisj : Disjoint (range (t + 1)) (Icc (t + 1) m) := by
            rw [Finset.disjoint_left]
            intro j hj1 hj2
            have := mem_range.mp hj1; have := (mem_Icc.mp hj2).1; omega
          rw [hpart, Finset.prod_union hdisj]
          congr 1
          · have h1 : ∏ j ∈ range (t + 1),
                (if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ)) =
                ∏ j ∈ range (t + 1), ((t + 1 - j : ℕ) : ℝ) :=
              Finset.prod_congr rfl fun j hj => by
                have hle : j ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hj)
                simp [hle]
            rw [h1]
            have hbij : ∏ j ∈ range (t + 1), (t + 1 - j) = (t + 1).factorial := by
              rw [← Finset.prod_Ico_id_eq_factorial]
              refine Finset.prod_bij (fun j _ => t + 1 - j)
                (fun j hj => mem_Ico.mpr (by have := mem_range.mp hj; omega))
                (fun j₁ hj₁ j₂ hj₂ h => by
                  have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega)
                (fun u hu => ⟨t + 1 - u, mem_range.mpr (by have := mem_Ico.mp hu; omega),
                  by have := mem_Ico.mp hu; omega⟩)
                (fun _ _ => rfl)
            exact_mod_cast hbij
          · have h2 : ∏ j ∈ Icc (t + 1) m,
                (if j ≤ t then ((t + 1 - j : ℕ) : ℝ) else ((j - t : ℕ) : ℝ)) =
                ∏ j ∈ Icc (t + 1) m, ((j - t : ℕ) : ℝ) :=
              Finset.prod_congr rfl fun j hj => by
                have hgt : ¬ j ≤ t := by have := (mem_Icc.mp hj).1; omega
                simp [hgt]
            rw [h2]
            have hbij : ∏ j ∈ Icc (t + 1) m, (j - t) = (m - t).factorial := by
              rw [← Finset.prod_Ico_id_eq_factorial]
              refine Finset.prod_bij (fun j _ => j - t)
                (fun j hj => mem_Ico.mpr (by have := mem_Icc.mp hj; omega))
                (fun j₁ hj₁ j₂ hj₂ h => by
                  have := mem_Icc.mp hj₁; have := mem_Icc.mp hj₂; omega)
                (fun u hu => ⟨u + t, mem_Icc.mpr (by have := mem_Ico.mp hu; omega),
                  Nat.add_sub_cancel u t⟩)
                (fun _ _ => rfl)
            exact_mod_cast hbij
    _ ≤ (m.factorial : ℝ) := by
          have hnat := factorial_mul_factorial_le (a := t + 1) (b := m - t) (by omega) (by omega)
          have heq : t + 1 + (m - t) - 1 = m := by omega
          rw [heq] at hnat
          exact_mod_cast hnat

/-- Denominator identity on consecutive integer nodes:
`∏_{j ∈ (range (m + 1)).erase i} |i - j| = i! * (m - i)!`. -/
theorem prod_abs_sub_node_eq (m : ℕ) {i : ℕ} (hi : i ≤ m) :
    ∏ j ∈ (range (m + 1)).erase i, |((i : ℝ) - (j : ℝ))| =
      (i.factorial : ℝ) * ((m - i).factorial : ℝ) := by
  have hpart : (range (m + 1)).erase i = range i ∪ Icc (i + 1) m := by
    ext j; simp only [mem_erase, mem_range, mem_union, mem_Icc]; omega
  have hdisj : Disjoint (range i) (Icc (i + 1) m) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have := mem_range.mp hj1; have := (mem_Icc.mp hj2).1; omega
  rw [hpart, Finset.prod_union hdisj]
  congr 1
  · have h1 : ∏ j ∈ range i, |((i : ℝ) - (j : ℝ))| = ∏ j ∈ range i, ((i - j : ℕ) : ℝ) :=
      Finset.prod_congr rfl fun j hj => by
        have hlt : j < i := mem_range.mp hj
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)), Nat.cast_sub hlt.le]
    rw [h1]
    have hbij : ∏ j ∈ range i, (i - j) = i.factorial := by
      rw [← Finset.prod_Ico_id_eq_factorial]
      refine Finset.prod_bij (fun j _ => i - j)
        (fun j hj => mem_Ico.mpr (by have := mem_range.mp hj; omega))
        (fun j₁ hj₁ j₂ hj₂ h => by have := mem_range.mp hj₁; have := mem_range.mp hj₂; omega)
        (fun u hu => ⟨i - u, mem_range.mpr (by have := mem_Ico.mp hu; omega),
          by have := mem_Ico.mp hu; omega⟩)
        (fun _ _ => rfl)
    exact_mod_cast hbij
  · have h2 : ∏ j ∈ Icc (i + 1) m, |((i : ℝ) - (j : ℝ))| =
        ∏ j ∈ Icc (i + 1) m, ((j - i : ℕ) : ℝ) :=
      Finset.prod_congr rfl fun j hj => by
        have hge : i ≤ j := by have := (mem_Icc.mp hj).1; omega
        rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hge)), neg_sub, Nat.cast_sub hge]
    rw [h2]
    have hbij : ∏ j ∈ Icc (i + 1) m, (j - i) = (m - i).factorial := by
      rw [← Finset.prod_Ico_id_eq_factorial]
      refine Finset.prod_bij (fun j _ => j - i)
        (fun j hj => mem_Ico.mpr (by have := mem_Icc.mp hj; omega))
        (fun j₁ hj₁ j₂ hj₂ h => by have := mem_Icc.mp hj₁; have := mem_Icc.mp hj₂; omega)
        (fun u hu => ⟨u + i, mem_Icc.mpr (by have := mem_Ico.mp hu; omega),
          Nat.add_sub_cancel u i⟩)
        (fun _ _ => rfl)
    exact_mod_cast hbij

/-- Lagrange interpolant bound on `m + 1` consecutive nodes `a, a + 1, …, a + m`: if
`|f(a + j)| ≤ B`
for `0 ≤ j ≤ m` and `x ∈ [a, a + m]`, then `|(Lagrange.interpolate ...).eval x| ≤ B * 2 ^ m`. -/
private theorem abs_eval_lagrange_consecutive_le (m : ℕ) (a : ℝ) (f : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ j ≤ m, |f j| ≤ B) {x : ℝ} (hx : x ∈ Icc a (a + m)) :
    |(Lagrange.interpolate (range (m + 1)) (fun j : ℕ => a + (j : ℝ)) f).eval x| ≤
      B * (2 : ℝ) ^ m := by
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm (i : ℕ) (hi : i ∈ range (m + 1)) :
      |(C (f i) * Lagrange.basis (range (m + 1)) (fun j : ℕ => a + (j : ℝ)) i).eval x| ≤
        B * (m.choose i : ℝ) := by
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [eval_mul, eval_C, abs_mul, Lagrange.eval_basis, Finset.abs_prod]
    have hbasis : ∏ j ∈ (range (m + 1)).erase i, |(x - (a + (j : ℝ))) / ((a + (i : ℝ)) - (a +
      (j : ℝ)))| ≤
        (m.choose i : ℝ) := by
      simp_rw [abs_div]
      rw [Finset.prod_div_distrib]
      have hden : ∏ j ∈ (range (m + 1)).erase i, |(a + (i : ℝ)) - (a + (j : ℝ))| =
          (i.factorial : ℝ) * ((m - i).factorial : ℝ) := by
        rw [← prod_abs_sub_node_eq m hi_le]
        exact Finset.prod_congr rfl fun j _ => by congr 1; ring
      rw [hden]
      have hden_pos : (0 : ℝ) < (i.factorial : ℝ) * ((m - i).factorial : ℝ) := by positivity
      rw [div_le_iff₀ hden_pos]
      have hch : (m.choose i : ℝ) * ((i.factorial : ℝ) * ((m - i).factorial : ℝ)) =
        (m.factorial : ℝ) := by
        have hnat := Nat.choose_mul_factorial_mul_factorial hi_le
        rw [mul_assoc] at hnat
        exact_mod_cast hnat
      rw [hch]
      exact prod_abs_sub_le_factorial hx hi_le
    exact mul_le_mul (hf i hi_le) hbasis (Finset.prod_nonneg fun _ _ => abs_nonneg _) hB
  calc ∑ i ∈ range (m + 1),
          |(C (f i) * Lagrange.basis (range (m + 1)) (fun j : ℕ => a + (j : ℝ)) i).eval x|
      ≤ ∑ i ∈ range (m + 1), B * (m.choose i : ℝ) := Finset.sum_le_sum hterm
    _ = B * ∑ i ∈ range (m + 1), (m.choose i : ℝ) := (Finset.mul_sum _ _ _).symm
    _ = B * (2 : ℝ) ^ m := by
          congr 1
          exact_mod_cast Nat.sum_range_choose m

/-- `r`-fold Rolle's theorem for polynomials: if a real polynomial `g` vanishes at `r + 1`
strictly increasing points `v 0 < v 1 < … < v r`, then there exists `ξ ∈ (v 0, v r)` such that
`(derivative^[r] g).eval ξ = 0`. -/
private theorem exists_iterate_derivative_eval_eq_zero :
    ∀ (r : ℕ) (g : ℝ[X]) (v : Fin (r + 1) → ℝ),
      StrictMono v → (∀ j, g.eval (v j) = 0) →
      ∃ ξ, v 0 ≤ ξ ∧ ξ ≤ v (Fin.last r) ∧ (derivative^[r] g).eval ξ = 0
  | 0, g, v, _, hzero => ⟨v 0, le_rfl, le_rfl, by simpa using hzero 0⟩
  | r + 1, g, v, hmono, hzero => by
    -- By Rolle's theorem on each adjacent interval `[v j, v (j + 1)]`, find `w j ∈ (v j, v (j +
    -- 1))`
    -- where `(derivative g).eval (w j) = 0`.
    have hstep (j : Fin (r + 1)) :
        ∃ c ∈ Set.Ioo (v j.castSucc) (v j.succ), (derivative g).eval c = 0 := by
      have hlt : v j.castSucc < v j.succ := hmono Fin.castSucc_lt_succ
      obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_zero hlt
        g.continuous.continuousOn
        (by rw [hzero j.castSucc, hzero j.succ])
        (fun x _ => g.hasDerivAt x)
      exact ⟨c, hc, hderiv⟩
    choose w hw_mem hw_zero using hstep
    have hw_mono : StrictMono w := by
      intro i j hij
      have h1 : w i < v i.succ := (hw_mem i).2
      have h2 : v i.succ ≤ v j.castSucc := hmono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
      have h3 : v j.castSucc < w j := (hw_mem j).1
      linarith
    obtain ⟨ξ, hξ1, hξ2, hξz⟩ :=
      exists_iterate_derivative_eval_eq_zero r (derivative g) w hw_mono hw_zero
    refine ⟨ξ, ?_, ?_, ?_⟩
    · exact ((hw_mem 0).1.le).trans hξ1
    · exact hξ2.trans (hw_mem (Fin.last r)).2.le
    · rwa [Function.iterate_succ_apply]

/-- Iterated derivative of a monic polynomial of degree `r` is the constant `C (r! : ℝ)`. -/
private theorem iterate_derivative_nodal (s : Finset ℕ) (v : ℕ → ℝ) :
    derivative^[#s] (Lagrange.nodal s v) = C ((#s).factorial : ℝ) := by
  have hmonic : (Lagrange.nodal s v).Monic := Lagrange.nodal_monic
  have hdeg : (Lagrange.nodal s v).natDegree = #s := Lagrange.natDegree_nodal
  have hfac := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) #s) (Lagrange.nodal s v)
  dsimp at hfac
  rw [← hfac, ← hdeg, Polynomial.hasseDeriv_natDegree_eq_C, hmonic.leadingCoeff, smul_C,
    nsmul_eq_mul,
    mul_one, hdeg]

/-- Lagrange interpolation remainder on `r` consecutive integer nodes `a, …, a + r - 1`:
for any non-node `x₀ ∈ [a, a + r - 1]`, there exists `ξ ∈ [a, a + r - 1]` with
`|q.eval x₀ - L.eval x₀| ≤ |(hasseDeriv r q).eval ξ| * r!`. -/
private theorem exists_lagrange_remainder_consecutive {r a : ℕ} (hr : 2 ≤ r) (q : ℝ[X])
    {x₀ : ℝ} (hx₀_ge : (a : ℝ) ≤ x₀) (hx₀_le : x₀ ≤ (a : ℝ) + ((r - 1 : ℕ) : ℝ))
    (hnode : ∀ j ∈ range r, x₀ ≠ (a : ℝ) + (j : ℝ)) :
    ∃ ξ ∈ Icc (a : ℝ) ((a : ℝ) + ((r - 1 : ℕ) : ℝ)),
      |q.eval x₀ -
          (Lagrange.interpolate (range r) (fun j => (a : ℝ) + (j : ℝ))
            (fun j => q.eval ((a : ℝ) + (j : ℝ)))).eval x₀| ≤
        |(hasseDeriv r q).eval ξ| * (r.factorial : ℝ) := by
  let v : ℕ → ℝ := fun j => (a : ℝ) + (j : ℝ)
  let L : ℝ[X] := Lagrange.interpolate (range r) v (fun j => q.eval (v j))
  have hnodal_ne : (Lagrange.nodal (range r) v).eval x₀ ≠ 0 := by
    rw [Lagrange.eval_nodal, Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.mpr (hnode j hj)
  set c : ℝ := (q.eval x₀ - L.eval x₀) / (Lagrange.nodal (range r) v).eval x₀
  let g : ℝ[X] := q - L - C c * Lagrange.nodal (range r) v
  have hg_zero_node (j : ℕ) (hj : j ∈ range r) : g.eval (v j) = 0 := by
    have hinj : Set.InjOn v (range r) := fun i _ j _ h => by
      simp only [v] at h; exact Nat.cast_injective (add_left_cancel h)
    have hLj : L.eval (v j) = q.eval (v j) := Lagrange.eval_interpolate_at_node _ hinj hj
    have hnj : (Lagrange.nodal (range r) v).eval (v j) = 0 := Lagrange.eval_nodal_at_node hj
    simp [g, hLj, hnj]
  have hg_zero_x₀ : g.eval x₀ = 0 := by
    simp only [g, eval_sub, eval_mul, eval_C, c]
    rw [div_mul_cancel₀ _ hnodal_ne, sub_self]
  have hpos_idx : ∃ k₀ : ℕ, k₀ < r - 1 ∧ v k₀ < x₀ ∧ x₀ < v (k₀ + 1) := by
    set k₀ := ⌊x₀ - (a : ℝ)⌋₊
    have hk₀_le : v k₀ ≤ x₀ := by
      simp only [v, k₀]; linarith [Nat.floor_le (sub_nonneg.mpr hx₀_ge)]
    have hk₀_lt_r1 : k₀ < r - 1 := by
      by_contra hge
      have hge' : r - 1 ≤ k₀ := not_lt.mp hge
      have hle' : (r - 1 : ℕ) ≤ x₀ - (a : ℝ) :=
        (by exact_mod_cast hge' : ((r - 1 : ℕ) : ℝ) ≤ (k₀ : ℝ)).trans
          (Nat.floor_le (sub_nonneg.mpr hx₀_ge))
      have heq : x₀ = v (r - 1) := by simp only [v]; linarith
      exact hnode (r - 1) (mem_range.mpr (by omega)) heq
    have hne0 : x₀ ≠ v k₀ := hnode k₀ (mem_range.mpr (by omega))
    refine ⟨k₀, hk₀_lt_r1, lt_of_le_of_ne hk₀_le hne0.symm, ?_⟩
    simp only [v, k₀]
    have := Nat.lt_floor_add_one (x₀ - (a : ℝ))
    push_cast; linarith
  obtain ⟨k₀, hk₀, hk₀_lt, hk₀_gt⟩ := hpos_idx
  let nodes : Fin (r + 1) → ℝ := fun idx =>
    if idx.1 ≤ k₀ then v idx.1
    else if idx.1 = k₀ + 1 then x₀
    else v (idx.1 - 1)
  have hv_mono : StrictMono v := fun m₁ m₂ hm => by
    simp only [v]
    linarith [Nat.cast_lt (α := ℝ).mpr hm]
  have hnodes_mono : StrictMono nodes := by
    intro i j hij
    have hij' : i.1 < j.1 := hij
    simp only [nodes]
    by_cases hi1 : i.1 ≤ k₀
    · simp only [hi1, ↓reduceIte]
      by_cases hj1 : j.1 ≤ k₀
      · simp only [hj1, ↓reduceIte]; exact hv_mono hij'
      · simp only [hj1, ↓reduceIte]
        by_cases hj2 : j.1 = k₀ + 1
        · simp only [hj2, ↓reduceIte]; exact (hv_mono.monotone hi1).trans_lt hk₀_lt
        · simp only [hj2, ↓reduceIte]; exact hv_mono (by omega)
    · simp only [hi1, ↓reduceIte]
      have hj1 : ¬ j.1 ≤ k₀ := by omega
      simp only [hj1, ↓reduceIte]
      by_cases hi2 : i.1 = k₀ + 1
      · have hj2 : j.1 ≠ k₀ + 1 := by omega
        simp only [hi2, hj2, ↓reduceIte]
        exact hk₀_gt.trans_le (hv_mono.monotone (by omega))
      · have hj2 : j.1 ≠ k₀ + 1 := by omega
        simp only [hi2, hj2, ↓reduceIte]
        exact hv_mono (by omega)
  have hnodes_zero : ∀ idx : Fin (r + 1), g.eval (nodes idx) = 0 := by
    intro idx
    simp only [nodes]
    split_ifs with h1 h2
    · exact hg_zero_node idx.1 (mem_range.mpr (by omega))
    · exact hg_zero_x₀
    · exact hg_zero_node (idx.1 - 1) (mem_range.mpr (by omega))
  obtain ⟨ξ, hξ_ge, hξ_le, hξ_zero⟩ :=
    exists_iterate_derivative_eval_eq_zero r g nodes hnodes_mono hnodes_zero
  have hξ_mem : ξ ∈ Icc (a : ℝ) ((a : ℝ) + ((r - 1 : ℕ) : ℝ)) := by
    have h0 : nodes 0 = (a : ℝ) := by simp [nodes, v]
    have hlast : nodes (Fin.last r) = (a : ℝ) + ((r - 1 : ℕ) : ℝ) := by
      simp only [nodes, Fin.val_last, v]
      have h1 : ¬ r ≤ k₀ := by omega
      have h2 : r ≠ k₀ + 1 := by omega
      simp [h1, h2]
    rw [h0] at hξ_ge; rw [hlast] at hξ_le
    exact ⟨hξ_ge, hξ_le⟩
  have hL_deriv_zero : derivative^[r] L = 0 := by
    have hL_deg : L.natDegree < r := by
      have hinj : Set.InjOn v (range r) := fun i _ j _ h => by
        simp only [v] at h; exact Nat.cast_injective (add_left_cancel h)
      have hdeg := Lagrange.degree_interpolate_lt (fun j => q.eval (v j)) hinj
      rw [card_range] at hdeg
      by_cases hL0 : L = 0
      · rw [hL0, natDegree_zero]; omega
      · rw [Polynomial.degree_eq_natDegree hL0] at hdeg
        exact_mod_cast hdeg
    have hfac := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) r) L
    dsimp at hfac
    rw [← hfac, hasseDeriv_eq_zero_of_lt_natDegree L r hL_deg, smul_zero]
  have hiter_sub (f₁ f₂ : ℝ[X]) : derivative^[r] (f₁ - f₂) =
      derivative^[r] f₁ - derivative^[r] f₂ := by
    clear * -
    induction r with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', ih, derivative_sub]
  have hiter_C_mul (α : ℝ) (f₁ : ℝ[X]) : derivative^[r] (C α * f₁) = C α * derivative^[r] f₁ := by
    clear * -
    induction r with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', ih, derivative_C_mul]
  have hc_eq : c = (hasseDeriv r q).eval ξ := by
    have hg_d : derivative^[r] g = derivative^[r] q - C (c * (r.factorial : ℝ)) := by
      simp only [g, hiter_sub, hL_deriv_zero, sub_zero, hiter_C_mul]
      have hnod := iterate_derivative_nodal (range r) v
      rw [card_range] at hnod
      rw [hnod, ← map_mul]
    rw [hg_d, eval_sub, eval_C] at hξ_zero
    have hfac := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) r) q
    dsimp at hfac
    have hq_d : (derivative^[r] q).eval ξ = (r.factorial : ℝ) * (hasseDeriv r q).eval ξ := by
      rw [← hfac, eval_smul, nsmul_eq_mul]
    rw [hq_d] at hξ_zero
    have hrfac : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    apply mul_right_cancel₀ hrfac
    linarith
  have hnodal_le : |(Lagrange.nodal (range r) v).eval x₀| ≤ (r.factorial : ℝ) := by
    rw [Lagrange.eval_nodal, Finset.abs_prod]
    have hlt_factor : ∀ j ∈ range r, |x₀ - v j| ≤ (r : ℝ) := fun j hj => by
      have hj_le : (j : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by have := mem_range.mp hj; omega : j ≤ r - 1)
      have h1 : |x₀ - v j| ≤ ((r - 1 : ℕ) : ℝ) := by
        simp only [v]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      linarith [show ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) by exact_mod_cast Nat.sub_le r 1]
    have hr_succ : r = (r - 1) + 1 := by omega
    have h0mem : (0 : ℕ) ∈ range r := mem_range.mpr (by omega)
    rw [← Finset.mul_prod_erase (range r) _ h0mem]
    have hprod_rest : ∏ j ∈ (range r).erase 0, |x₀ - v j| ≤ ((r - 1).factorial : ℝ) := by
      rw [show range r = range ((r - 1) + 1) by rw [← hr_succ]]
      exact prod_abs_sub_le_factorial ⟨hx₀_ge, hx₀_le⟩ (Nat.zero_le (r - 1))
    have h0le : |x₀ - v 0| ≤ (r : ℝ) := hlt_factor 0 h0mem
    calc |x₀ - v 0| * ∏ j ∈ (range r).erase 0, |x₀ - v j|
        ≤ (r : ℝ) * ((r - 1).factorial : ℝ) :=
            mul_le_mul h0le hprod_rest (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ = (r.factorial : ℝ) := by
            have hfac_nat : r * (r - 1).factorial = r.factorial := by
              conv_rhs => rw [hr_succ, Nat.factorial_succ, ← hr_succ]
            exact_mod_cast hfac_nat
  refine ⟨ξ, hξ_mem, ?_⟩
  have hfactor_eq : |q.eval x₀ - L.eval x₀| =
      |(hasseDeriv r q).eval ξ| * |(Lagrange.nodal (range r) v).eval x₀| := by
    rw [← hc_eq, ← abs_mul]
    simp only [c, div_mul_cancel₀ _ hnodal_ne]
  rw [hfactor_eq]
  exact mul_le_mul_of_nonneg_left hnodal_le (abs_nonneg _)

/-- Rescaled Cauchy Hasse-derivative bound on `[0, n]`. -/
private theorem abs_eval_hasseDeriv_Icc_zero_n_le {n d r : ℕ} (hn : 1 ≤ n) {q : ℝ[X]}
    (hq : q.natDegree ≤ d) {M : ℝ} (hM_nn : 0 ≤ M)
    (hM_bound : ∀ y ∈ Icc (0 : ℝ) n, |q.eval y| ≤ M) {ξ : ℝ} (hξ_mem : ξ ∈ Icc (0 : ℝ) n)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_half : ρ ≤ 1 / 2) :
    |(hasseDeriv r q).eval ξ| ≤
      M * Real.exp (3 * (d : ℝ) * √ρ) / (((n : ℝ) / 2) ^ r * ρ ^ r) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let scale : ℝ[X] := C ((n : ℝ) / 2) * X + C ((n : ℝ) / 2)
  let p : ℝ[X] := q.comp scale
  have hp_deg : p.natDegree ≤ d := by
    refine natDegree_comp_le.trans ?_
    have h1 : scale.natDegree ≤ 1 := natDegree_linear_le
    nlinarith
  have hp_bound : ∀ y ∈ Icc (-1 : ℝ) 1, |p.eval y| ≤ M := by
    intro y hy
    simp only [p, scale, eval_comp, eval_add, eval_mul, eval_C, eval_X]
    exact hM_bound _ ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
  have hhasse_scale : (hasseDeriv r p).eval (2 * ξ / (n : ℝ) - 1) =
      ((n : ℝ) / 2) ^ r * (hasseDeriv r q).eval ξ := by
    have hq_comp : p.comp (C (2 / (n : ℝ)) * X + C (2 * ξ / (n : ℝ) - 1)) =
        q.comp (X + C ξ) := by
      simp only [p, scale, comp_assoc]
      congr 1
      simp only [add_comp, mul_comp, C_comp, X_comp]
      rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul, add_assoc, ← C_add]
      have h1 : ((n : ℝ) / 2) * (2 / (n : ℝ)) = 1 := by field_simp
      have h2 : ((n : ℝ) / 2) * (2 * ξ / (n : ℝ) - 1) + (n : ℝ) / 2 = ξ := by field_simp; ring
      rw [h1, h2, C_1, one_mul]
    have h1 : (p.comp (C (2 / (n : ℝ)) * X + C (2 * ξ / (n : ℝ) - 1))).coeff r =
        (2 / (n : ℝ)) ^ r * (hasseDeriv r p).eval (2 * ξ / (n : ℝ) - 1) := by
      have hrew : p.comp (C (2 / (n : ℝ)) * X + C (2 * ξ / (n : ℝ) - 1)) =
          (taylor (2 * ξ / (n : ℝ) - 1) p).comp (C (2 / (n : ℝ)) * X) := by
        simp [taylor_apply, comp_assoc]
      rw [hrew, coeff_comp_C_mul_X, taylor_coeff, mul_comm]
    have h2 : (q.comp (X + C ξ)).coeff r = (hasseDeriv r q).eval ξ := by
      rw [← taylor_apply, taylor_coeff]
    rw [hq_comp, h2] at h1
    have h2n : (2 / (n : ℝ)) ^ r * ((n : ℝ) / 2) ^ r = 1 := by
      rw [← mul_pow]
      have h1' : (2 / (n : ℝ)) * ((n : ℝ) / 2) = 1 := by field_simp
      rw [h1', one_pow]
    calc (hasseDeriv r p).eval (2 * ξ / (n : ℝ) - 1)
        = ((n : ℝ) / 2) ^ r * ((2 / (n : ℝ)) ^ r * (hasseDeriv r p).eval (2 * ξ / (n : ℝ) -
          1)) := by
            rw [← mul_assoc, mul_comm (((n : ℝ) / 2) ^ r), h2n, one_mul]
      _ = ((n : ℝ) / 2) ^ r * (hasseDeriv r q).eval ξ := by rw [h1]
  have hξy : 2 * ξ / (n : ℝ) - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have : 0 ≤ 2 * ξ / (n : ℝ) := div_nonneg (by linarith [hξ_mem.1]) hnR.le
      linarith
    · have : 2 * ξ / (n : ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr (by linarith [hξ_mem.2])
      linarith
  have hcauchy := abs_eval_hasseDeriv_le hp_deg hM_nn hp_bound hξy hρ_pos hρ_half r
  rw [hhasse_scale, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) / 2) ^ r)] at hcauchy
  rw [le_div_iff₀ (by positivity)]
  have h1 := (le_div_iff₀ (pow_pos hρ_pos r)).mp hcauchy
  linarith

/-- Case 3 of Coppersmith–Rivlin (`n < 2 d²` and `80 d ≤ n`), proved via `r`-node Lagrange
interpolation, `r`-fold Rolle remainder, and the complex-ellipse Cauchy derivative bound. -/
private theorem coppersmith_rivlin_bound_case3 {n d : ℕ} (hn : 1 ≤ n)
    (hcase1 : n < 2 * d ^ 2) (hcase2 : 80 * d ≤ n) {q : ℝ[X]} (hq : q.natDegree ≤ d)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j : ℕ, j ≤ n → |q.eval (j : ℝ)| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) n) :
    |q.eval x| ≤ 4 * B * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hexp_ge1 : 1 ≤ Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) :=
    Real.one_le_exp (by positivity)
  have hd_ge : 41 ≤ d := by nlinarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  set r : ℕ := Nat.ceil (240 * (d : ℝ) ^ 2 / (n : ℝ))
  have hr_ge_real : 240 * (d : ℝ) ^ 2 / (n : ℝ) ≤ (r : ℝ) := Nat.le_ceil _
  have hr_gt120 : (120 : ℝ) < 240 * (d : ℝ) ^ 2 / (n : ℝ) := by
    rw [lt_div_iff₀ hnR]
    have : (n : ℝ) < 2 * (d : ℝ) ^ 2 := by exact_mod_cast hcase1
    linarith
  have hr_ge121 : 121 ≤ r := by
    have : (120 : ℝ) < (r : ℝ) := lt_of_lt_of_le hr_gt120 hr_ge_real
    have : (120 : ℕ) < r := by exact_mod_cast this
    omega
  have hr_lt_add : (r : ℝ) < 240 * (d : ℝ) ^ 2 / (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hr_le_4d : (r : ℝ) ≤ 4 * (d : ℝ) := by
    have h80 : 80 * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcase2
    have hdiv : 240 * (d : ℝ) ^ 2 / (n : ℝ) ≤ 3 * (d : ℝ) := by
      rw [div_le_iff₀ hnR]; nlinarith
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  have hr_lt_n : r < n := by
    have : (r : ℝ) < (n : ℝ) := by
      have h80 : 80 * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcase2
      linarith
    exact_mod_cast this
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hnR.le)
    (continuous_abs.comp q.continuous).continuousOn
  set M : ℝ := |q.eval x₀|
  have hM_nn : 0 ≤ M := abs_nonneg _
  have hM_bound (y : ℝ) (hy : y ∈ Icc (0 : ℝ) n) : |q.eval y| ≤ M := hmax hy
  suffices hM_le : M ≤ 4 * B * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) from
    (hM_bound x hx).trans hM_le
  set a : ℕ := min ⌊x₀⌋₊ (n - (r - 1))
  have ha_add_le : a + (r - 1) ≤ n := by omega
  have hx₀_ge_a : (a : ℝ) ≤ x₀ := by
    have h1 : (a : ℝ) ≤ (⌊x₀⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
    exact h1.trans (Nat.floor_le hx₀.1)
  have hx₀_le_ar : x₀ ≤ (a : ℝ) + ((r - 1 : ℕ) : ℝ) := by
    rcases le_or_gt ⌊x₀⌋₊ (n - (r - 1)) with hmin | hmin
    · have ha_eq : a = ⌊x₀⌋₊ := min_eq_left hmin
      rw [ha_eq]
      have hlt := Nat.lt_floor_add_one x₀
      have hr2 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
      linarith
    · have ha_eq : a = n - (r - 1) := min_eq_right hmin.le
      rw [ha_eq, ← Nat.cast_add, Nat.sub_add_cancel (by omega : r - 1 ≤ n)]
      exact hx₀.2
  by_cases hnode : ∃ j ∈ range r, x₀ = (a : ℝ) + (j : ℝ)
  · obtain ⟨j, hj, hxj⟩ := hnode
    have hjn : a + j ≤ n := by have := mem_range.mp hj; omega
    have hMB : M ≤ B := by
      simp only [M, hxj, ← Nat.cast_add]
      exact hb (a + j) hjn
    nlinarith only [hMB, hB, hexp_ge1]
  push Not at hnode
  let v : ℕ → ℝ := fun j => (a : ℝ) + (j : ℝ)
  let L : ℝ[X] := Lagrange.interpolate (range r) v (fun j => q.eval (v j))
  have hL_bound : |L.eval x₀| ≤ B * (2 : ℝ) ^ (r - 1) := by
    have hr_succ : r = (r - 1) + 1 := by omega
    rw [show L = Lagrange.interpolate (range ((r - 1) + 1)) v (fun j => q.eval (v j)) by
      simp only [L, ← hr_succ]]
    exact abs_eval_lagrange_consecutive_le (r - 1) (a : ℝ) (fun j => q.eval (v j)) hB
      (fun j hj => by
        simp only [v, ← Nat.cast_add]
        exact hb (a + j) (by omega))
      ⟨hx₀_ge_a, hx₀_le_ar⟩
  obtain ⟨ξ, hξ_ar, hrem_fac⟩ :=
    exists_lagrange_remainder_consecutive (by omega : 2 ≤ r) q hx₀_ge_a hx₀_le_ar hnode
  have hξ_mem : ξ ∈ Icc (0 : ℝ) n :=
    ⟨le_trans (Nat.cast_nonneg a) hξ_ar.1,
      le_trans hξ_ar.2 (by exact_mod_cast ha_add_le)⟩
  set ρ : ℝ := ((r : ℝ) / (6 * (d : ℝ))) ^ 2
  have hρ_pos : 0 < ρ := by positivity
  have hρ_half : ρ ≤ 1 / 2 := by
    have hfrac : (r : ℝ) / (6 * (d : ℝ)) ≤ 2 / 3 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [hr_le_4d]
    have hsq : ((r : ℝ) / (6 * (d : ℝ))) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hfrac 2
    linarith only [hsq]
  have hhasse_q :=
    abs_eval_hasseDeriv_Icc_zero_n_le hn hq hM_nn hM_bound hξ_mem hρ_pos hρ_half (r := r)
  have hrem_le : |q.eval x₀ - L.eval x₀| ≤ (1 / 2 : ℝ) * M := by
    have hrfac_le : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    have hsqrt_ρ : √ρ = (r : ℝ) / (6 * (d : ℝ)) := Real.sqrt_sq (by positivity)
    have hexp_eq : Real.exp (3 * (d : ℝ) * √ρ) = (Real.exp (1 / 2)) ^ r := by
      rw [← Real.exp_nat_mul, hsqrt_ρ]
      congr 1; field_simp; ring
    have hbase_le : (2 * (r : ℝ) / ((n : ℝ) * ρ)) * Real.exp (1 / 2) ≤ 1 / 2 := by
      have hsimp : 2 * (r : ℝ) / ((n : ℝ) * ρ) = 72 * (d : ℝ) ^ 2 / ((n : ℝ) * (r : ℝ)) := by
        simp only [ρ]; field_simp; ring
      rw [hsimp]
      have hexp_half : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
        have hsq : Real.exp (1 / 2 : ℝ) ^ 2 < (5 / 3 : ℝ) ^ 2 := by
          rw [← Real.exp_nat_mul]
          norm_num
          exact lt_trans Real.exp_one_lt_d9 (by norm_num)
        nlinarith only [hsq, Real.exp_pos (1 / 2 : ℝ)]
      have hdiv_le : 72 * (d : ℝ) ^ 2 / ((n : ℝ) * (r : ℝ)) ≤ 3 / 10 := by
        rw [div_le_iff₀ (by positivity)]
        have h240 : 240 * (d : ℝ) ^ 2 ≤ (r : ℝ) * (n : ℝ) := (div_le_iff₀ hnR).mp hr_ge_real
        rw [mul_comm (n : ℝ) (r : ℝ)]
        linarith only [h240]
      calc 72 * (d : ℝ) ^ 2 / ((n : ℝ) * (r : ℝ)) * Real.exp (1 / 2)
          ≤ (3 / 10 : ℝ) * (5 / 3 : ℝ) :=
              mul_le_mul hdiv_le hexp_half.le (Real.exp_pos _).le (by norm_num)
        _ = 1 / 2 := by norm_num
    calc |q.eval x₀ - L.eval x₀|
        ≤ |(hasseDeriv r q).eval ξ| * (r.factorial : ℝ) := hrem_fac
      _ ≤ (M * Real.exp (3 * (d : ℝ) * √ρ) / (((n : ℝ) / 2) ^ r * ρ ^ r)) * (r : ℝ) ^ r :=
            mul_le_mul hhasse_q hrfac_le (Nat.cast_nonneg _) (by positivity)
      _ = M * ((2 * (r : ℝ) / ((n : ℝ) * ρ)) * Real.exp (1 / 2)) ^ r := by
            simp only [hexp_eq, mul_pow, div_pow]
            field_simp
      _ ≤ M * (1 / 2 : ℝ) ^ r :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase_le r) hM_nn
      _ ≤ M * (1 / 2 : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ hM_nn
            calc (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ 1 :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              _ = 1 / 2 := pow_one _
      _ = (1 / 2 : ℝ) * M := mul_comm _ _
  have hM_tri : M ≤ |L.eval x₀| + |q.eval x₀ - L.eval x₀| := by
    have h := abs_add_le (L.eval x₀) (q.eval x₀ - L.eval x₀)
    rw [add_sub_cancel] at h
    exact h
  have hM_2r : M ≤ B * (2 : ℝ) ^ r := by
    have hpow : (2 : ℝ) * (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r := by
      conv_rhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
    have hBpow : 2 * (B * (2 : ℝ) ^ (r - 1)) = B * (2 : ℝ) ^ r := by
      rw [← hpow]; ring
    linarith only [hM_tri, hL_bound, hrem_le, hBpow]
  have h2r_le : (2 : ℝ) ^ r ≤ 4 * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := by
    have hpow : (2 : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log 2) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    rw [hpow]
    have hlog2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp_le : Real.exp ((r : ℝ) * Real.log 2) ≤
        Real.exp ((240 * (d : ℝ) ^ 2 / (n : ℝ) + 1) * 0.7) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hsplit : Real.exp ((240 * (d : ℝ) ^ 2 / (n : ℝ) + 1) * 0.7) =
        Real.exp 0.7 * Real.exp (168 * (d : ℝ) ^ 2 / (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp07 : Real.exp 0.7 ≤ 4 := by
      have : Real.exp 0.7 ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_one_lt_three]
    have hexp_mono : Real.exp (168 * (d : ℝ) ^ 2 / (n : ℝ)) ≤
        Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by nlinarith) hnR.le)
    calc Real.exp ((r : ℝ) * Real.log 2)
        ≤ Real.exp 0.7 * Real.exp (168 * (d : ℝ) ^ 2 / (n : ℝ)) := by
            rw [← hsplit]; exact hexp_le
      _ ≤ 4 * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) :=
            mul_le_mul hexp07 hexp_mono (Real.exp_pos _).le (by norm_num)
  calc M ≤ B * (2 : ℝ) ^ r := hM_2r
    _ ≤ B * (4 * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left h2r_le hB
    _ = 4 * B * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := by ring

/-- **Coppersmith–Rivlin growth bound**: if `q : ℝ[X]` has degree `d ≤ n` (`n ≥ 1`) and
`|q.eval j| ≤ B` (`0 ≤ B`) at every integer `j ∈ {0, …, n}`, then for all `x ∈ [0, n]`,
`|q.eval x| ≤ 4 * B * exp (5000 * d² / n)`. -/
theorem coppersmith_rivlin_bound {n d : ℕ} (hn : 1 ≤ n) (hdn : d ≤ n) {q : ℝ[X]}
    (hq : q.natDegree ≤ d) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j : ℕ, j ≤ n → |q.eval (j : ℝ)| ≤ B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) n) :
    |q.eval x| ≤ 4 * B * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hexp_ge1 : 1 ≤ Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) :=
    Real.one_le_exp (by positivity)
  -- Case 1: `2 * d ^ 2 ≤ n` (Ehlich–Zeller).
  by_cases hcase1 : 2 * d ^ 2 ≤ n
  · have hez := Polynomial.sub_mul_abs_eval_le_of_forall_nat hq hn hb hx
    have hdiff : (n : ℝ) / 2 ≤ (n : ℝ) - (d : ℝ) ^ 2 := by
      have : (2 : ℝ) * (d : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hcase1
      linarith
    have hle2B : |q.eval x| ≤ 2 * B := by
      nlinarith [abs_nonneg (q.eval x)]
    nlinarith
  -- Case 2: `n < 80 * d` (full Lagrange interpolation on `0, …, n`).
  by_cases hcase2 : n < 80 * d
  · have hinj : Set.InjOn (fun j : ℕ => (0 : ℝ) + (j : ℝ)) (range (n + 1)) := by
      intro i _ j _ h; simp only [zero_add] at h; exact Nat.cast_injective h
    have hdeg_lt : q.degree < #(range (n + 1)) := by
      rw [card_range]
      exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (hq.trans hdn))
    have heq : q = Lagrange.interpolate (range (n + 1)) (fun j : ℕ => (0 : ℝ) + (j : ℝ))
        (fun j => q.eval (j : ℝ)) := by
      simpa using Lagrange.eq_interpolate hinj hdeg_lt
    have hlag : |q.eval x| ≤ B * (2 : ℝ) ^ n := by
      conv_lhs => rw [heq]
      exact abs_eval_lagrange_consecutive_le n 0 (fun j => q.eval (j : ℝ)) hB hb
        (by simpa using hx)
    have h2n : (2 : ℝ) ^ n ≤ Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := by
      have hpow : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      rw [hpow]
      refine Real.exp_le_exp.mpr ?_
      have hlog2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have hn80 : (n : ℝ) < 80 * (d : ℝ) := by exact_mod_cast hcase2
      have hsq : (n : ℝ) ^ 2 < 6400 * (d : ℝ) ^ 2 := by nlinarith
      rw [le_div_iff₀ hnR]
      nlinarith
    calc |q.eval x| ≤ B * (2 : ℝ) ^ n := hlag
      _ ≤ B * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := mul_le_mul_of_nonneg_left h2n hB
      _ ≤ 4 * B * Real.exp (5000 * (d : ℝ) ^ 2 / (n : ℝ)) := by nlinarith
  -- Case 3: `n < 2 * d ^ 2` and `80 * d ≤ n`.
  push Not at hcase1 hcase2
  exact coppersmith_rivlin_bound_case3 hn hcase1 hcase2 hq hB hb hx

end CoppersmithRivlin

end CslibFrontier.Foundations.Analysis
