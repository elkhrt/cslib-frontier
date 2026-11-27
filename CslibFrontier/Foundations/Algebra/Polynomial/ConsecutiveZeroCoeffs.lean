module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Consecutive Zero Coefficients in Powers and Exponentials of Polynomials

This module establishes algebraic bounds on the length of runs of consecutive zero coefficients
(between nonzero coefficients) in polynomial powers `f(X)^t`, formal power-series rational powers
`f(X)^{r/s}`, and formal power-series exponentials `exp(f(X))` via formal differentiation and
logarithmic derivatives.

## Main results

- `CslibFrontier.Foundations.Algebra.Polynomial.eq_smul_of_logDeriv_eq_charP`:
  logarithmic derivative lemma in positive characteristic `p`: if `t * f.natDegree < p`,
  `B.natDegree < p`, `f ≠ 0`, `B ≠ 0`, and `(t : F) • (derivative f * B) = f * derivative B`,
  then `f ^ t = C c * B` for some `c ≠ 0`.
- `CslibFrontier.Foundations.Algebra.Polynomial.consecutiveZeroCoeffs_pow_charP`:
  if `f ^ t = A * X ^ ℓ + B` over a field of characteristic `p` with `f.natDegree ≤ d`,
  `B.natDegree ≤ b`, `t * d < p`, `b < p`, `A ≠ 0`, and `B ≠ 0`, then `ℓ ≤ d + b`.
- `CslibFrontier.Foundations.Algebra.Polynomial.consecutiveZeroCoeffs_pow_charZero`:
  characteristic-zero analogue of `consecutiveZeroCoeffs_pow_charP` (without degree upper bounds).
- `CslibFrontier.Foundations.Algebra.Polynomial.eq_C_mul_of_mul_derivative_eq_powerSeries`:
  in characteristic zero, `B * d⁄dX g = d⁄dX B * g` with `B ≠ 0` implies `g = C c * B` in `F⟦X⟧`.
- `CslibFrontier.Foundations.Algebra.Polynomial.consecutiveZeroCoeffs_powerSeries_of_logDeriv_eq`:
  formal power-series bound for solutions `g ∈ F⟦X⟧` of `f * d⁄dX g = t • f' * g` in
  characteristic zero.
- `CslibFrontier.Foundations.Algebra.Polynomial.consecutiveZeroCoeffs_powerSeries_ratPow`:
  consecutive zero-coefficient bound for formal power-series rational powers `g ^ s = f ^ r`
  (and negative rational powers `g ^ s * f ^ r = 1`) in characteristic zero.
- `CslibFrontier.Foundations.Algebra.Polynomial.consecutiveZeroCoeffs_powerSeries_exp`:
  consecutive zero-coefficient bound for `exp(f(X))` in `F⟦X⟧` over a field of characteristic zero.
-/

public section

namespace CslibFrontier.Foundations.Algebra.Polynomial

open _root_.Polynomial
open scoped PowerSeries

/-- Helper: if `c • derivative f * B - g * derivative B ≠ 0` with `f.natDegree ≤ d`,
`B.natDegree ≤ b`, and `d + b < ℓ`, then `2 ≤ ℓ`. -/
private lemma two_le_of_derivative_sub_ne_zero {F : Type*} [Field F]
    {f g B : F[X]} {c : F} {d b ℓ : ℕ}
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b) (hlt : d + b < ℓ)
    (hne : c • Polynomial.derivative f * B - g * Polynomial.derivative B ≠ 0) :
    2 ≤ ℓ := by
  by_contra hℓ1
  have hdb0 : d + b = 0 := by omega
  have hf0 : f.natDegree = 0 := by omega
  have hB0 : B.natDegree = 0 := by omega
  have hdf : Polynomial.derivative f = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hf0, Polynomial.derivative_C]
  have hdB : Polynomial.derivative B = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hB0, Polynomial.derivative_C]
  exact hne (by simp [hdf, hdB])

/-- Helper: for polynomials `f, B` with `f.natDegree ≤ d`, `B.natDegree ≤ b`, `d + b < ℓ`, and
`2 ≤ ℓ`, the polynomial `c • (derivative f) * B` has degree strictly less than `ℓ - 1`. -/
private lemma natDegree_smul_derivative_mul_lt {F : Type*} [Field F]
    {f B : F[X]} {c : F} {d b ℓ : ℕ}
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b) (hlt : d + b < ℓ) (hℓ : 2 ≤ ℓ) :
    (c • Polynomial.derivative f * B).natDegree < ℓ - 1 := by
  by_cases h0 : c • Polynomial.derivative f * B = 0
  · rw [h0, natDegree_zero]; omega
  · have h1 : (c • Polynomial.derivative f).natDegree ≤ (Polynomial.derivative f).natDegree :=
      Polynomial.natDegree_smul_le _ _
    have h2 : (c • Polynomial.derivative f * B).natDegree ≤
        (c • Polynomial.derivative f).natDegree + B.natDegree := Polynomial.natDegree_mul_le
    have h3 : (Polynomial.derivative f).natDegree ≤ d - 1 :=
      (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hfd 1)
    by_cases hd0 : d = 0
    · have hf0 : f.natDegree = 0 := by omega
      have : Polynomial.derivative f = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hf0, Polynomial.derivative_C]
      exact absurd (by simp [this]) h0
    · omega

/-- Helper: for polynomials `f, B` with `f.natDegree ≤ d`, `B.natDegree ≤ b`, `d + b < ℓ`, and
`2 ≤ ℓ`, the polynomial `f * derivative B` has degree strictly less than `ℓ - 1`. -/
private lemma natDegree_mul_derivative_lt {F : Type*} [Field F]
    {f B : F[X]} {d b ℓ : ℕ}
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b) (hlt : d + b < ℓ) (hℓ : 2 ≤ ℓ) :
    (f * Polynomial.derivative B).natDegree < ℓ - 1 := by
  by_cases h0 : f * Polynomial.derivative B = 0
  · rw [h0, natDegree_zero]; omega
  · have h1 : (f * Polynomial.derivative B).natDegree ≤
        f.natDegree + (Polynomial.derivative B).natDegree := Polynomial.natDegree_mul_le
    have h2 : (Polynomial.derivative B).natDegree ≤ b - 1 :=
      (Polynomial.natDegree_derivative_le B).trans (Nat.sub_le_sub_right hBb 1)
    by_cases hb0 : b = 0
    · have hB0 : B.natDegree = 0 := by omega
      have : Polynomial.derivative B = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hB0, Polynomial.derivative_C]
      exact absurd (by simp [this]) h0
    · omega

section PositiveChar

variable {F : Type*} [Field F] {p : ℕ} [CharP F p]

omit [CharP F p] in
/-- Auxiliary lemma: if `B * H(X^p) = G * K(X^p)` in `F[X]` with `deg(B), deg(G) < p` and
`B, G, K ≠ 0`, then `G = C c * B` for some nonzero `c : F`. -/
private lemma eq_C_mul_of_mul_expand_eq {B G H K : F[X]} (hp : 0 < p)
    (hB : B ≠ 0) (hG : G ≠ 0) (hK : K ≠ 0)
    (hBdeg : B.natDegree < p) (hGdeg : G.natDegree < p)
    (heq : B * expand F p H = G * expand F p K) :
    ∃ c : F, c ≠ 0 ∧ G = C c * B := by
  classical
  set g0 := EuclideanDomain.gcd H K
  have hg0_ne : g0 ≠ 0 := by
    intro h0
    exact hK ((EuclideanDomain.gcd_eq_zero_iff.mp h0).2)
  obtain ⟨H1, hH1⟩ := EuclideanDomain.gcd_dvd_left H K
  obtain ⟨K1, hK1⟩ := EuclideanDomain.gcd_dvd_right H K
  have hK1_ne : K1 ≠ 0 := right_ne_zero_of_mul (hK1 ▸ hK)
  have hcop : IsCoprime H1 K1 := by
    set u := EuclideanDomain.gcdA H K
    set v := EuclideanDomain.gcdB H K
    have huv : g0 = H * u + K * v := EuclideanDomain.gcd_eq_gcd_ab H K
    refine ⟨u, v, ?_⟩
    have hmul : g0 * (u * H1 + v * K1) = g0 * 1 := by
      calc g0 * (u * H1 + v * K1)
          = u * (g0 * H1) + v * (g0 * K1) := by ring
        _ = u * H + v * K := by rw [← hH1, ← hK1]
        _ = H * u + K * v := by ring
        _ = g0 * 1 := by rw [← huv, mul_one]
    exact mul_left_cancel₀ hg0_ne hmul
  have hcop_exp : IsCoprime (expand F p H1) (expand F p K1) :=
    (isCoprime_expand hp.ne').mpr hcop
  have hg0_exp_ne : expand F p g0 ≠ 0 := (expand_ne_zero hp).mpr hg0_ne
  have heq1 : B * expand F p H1 = G * expand F p K1 := by
    apply mul_left_cancel₀ hg0_exp_ne
    calc expand F p g0 * (B * expand F p H1)
        = B * expand F p (g0 * H1) := by rw [map_mul]; ring
      _ = B * expand F p H := by rw [← hH1]
      _ = G * expand F p K := heq
      _ = G * expand F p (g0 * K1) := by rw [← hK1]
      _ = expand F p g0 * (G * expand F p K1) := by rw [map_mul]; ring
  have hK1_dvd : expand F p K1 ∣ B := by
    have hdvd : expand F p K1 ∣ B * expand F p H1 := ⟨G, by rw [heq1, mul_comm]⟩
    exact hcop_exp.symm.dvd_of_dvd_mul_right hdvd
  have hH1_dvd : expand F p H1 ∣ G := by
    have hdvd : expand F p H1 ∣ G * expand F p K1 := ⟨B, by rw [← heq1, mul_comm]⟩
    exact hcop_exp.dvd_of_dvd_mul_right hdvd
  have hK1_deg : K1.natDegree = 0 := by
    have hle : (expand F p K1).natDegree ≤ B.natDegree :=
      Polynomial.natDegree_le_of_dvd hK1_dvd hB
    rw [natDegree_expand] at hle
    by_contra hne
    have hpos : 1 ≤ K1.natDegree := Nat.one_le_iff_ne_zero.mpr hne
    have : p ≤ K1.natDegree * p := by simpa using Nat.mul_le_mul_right p hpos
    omega
  have hH1_ne : H1 ≠ 0 := by
    intro h0
    have : G * expand F p K1 = 0 := by rw [← heq1, h0, map_zero, mul_zero]
    exact mul_ne_zero hG ((expand_ne_zero hp).mpr hK1_ne) this
  have hH1_deg : H1.natDegree = 0 := by
    have hle : (expand F p H1).natDegree ≤ G.natDegree :=
      Polynomial.natDegree_le_of_dvd hH1_dvd hG
    rw [natDegree_expand] at hle
    by_contra hne
    have hpos : 1 ≤ H1.natDegree := Nat.one_le_iff_ne_zero.mpr hne
    have : p ≤ H1.natDegree * p := by simpa using Nat.mul_le_mul_right p hpos
    omega
  set a := H1.coeff 0
  set b := K1.coeff 0
  have ha : H1 = C a := Polynomial.eq_C_of_natDegree_eq_zero hH1_deg
  have hb : K1 = C b := Polynomial.eq_C_of_natDegree_eq_zero hK1_deg
  have ha_ne : a ≠ 0 := by
    intro h0; exact hH1_ne (by rw [ha, h0, map_zero])
  have hb_ne : b ≠ 0 := by
    intro h0; exact hK1_ne (by rw [hb, h0, map_zero])
  refine ⟨a / b, div_ne_zero ha_ne hb_ne, ?_⟩
  rw [ha, hb, expand_C, expand_C] at heq1
  have hC : C (a / b) * C b = C a := by rw [← map_mul, div_mul_cancel₀ _ hb_ne]
  have hmul : C b * G = C b * (C (a / b) * B) := by
    calc C b * G = G * C b := mul_comm _ _
      _ = B * C a := heq1.symm
      _ = C b * (C (a / b) * B) := by rw [← hC]; ring
  exact mul_left_cancel₀ (C_ne_zero.mpr hb_ne) hmul

/-- Logarithmic derivative lemma over a field of characteristic `p`: if `t * deg(f) < p`,
`deg(B) < p`, `f ≠ 0`, `B ≠ 0`, and `t • (f' * B) = f * B'`, then `f ^ t = C c * B` for some
nonzero `c : F`. -/
theorem eq_smul_of_logDeriv_eq_charP {f B : F[X]} {t : ℕ}
    (hf : f ≠ 0) (hB : B ≠ 0)
    (hft : t * f.natDegree < p) (hBdeg : B.natDegree < p)
    (hlog : (t : F) • (Polynomial.derivative f * B) = f * Polynomial.derivative B) :
    ∃ c : F, c ≠ 0 ∧ f ^ t = C c * B := by
  have hp : 0 < p := Nat.pos_of_ne_zero (by omega)
  have hderiv_pow : Polynomial.derivative (B ^ p) = 0 := by
    rw [Polynomial.derivative_pow, CharP.cast_eq_zero, map_zero, zero_mul, zero_mul]
  have hBp_exp : expand F p (contract p (B ^ p)) = B ^ p :=
    expand_contract p hderiv_pow hp.ne'
  have hderiv_prod : Polynomial.derivative (f ^ t * B ^ (p - 1)) = 0 := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_pow,
      C_eq_natCast, C_eq_natCast]
    have hmul_eq : (t : F) • (Polynomial.derivative f * B) = f * Polynomial.derivative B := hlog
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp
    have hcast : ((p - 1 : ℕ) : F) = -1 := by
      have : ((p - 1 : ℕ) : F) + 1 = 0 := by
        rw [← Nat.cast_add_one, hp1, CharP.cast_eq_zero]
      exact eq_neg_of_add_eq_zero_left this
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [pow_zero, Nat.cast_zero, zero_mul, one_mul] at hlog ⊢
      have hB' : Polynomial.derivative B = 0 := by
        have : f * Polynomial.derivative B = 0 := by simpa using hlog.symm
        exact (mul_eq_zero.mp this).resolve_left hf
      simp [hB']
    · rcases p with _ | p'
      · omega
      rcases p' with _ | p''
      · have hprime := CharP.char_is_prime_or_zero F 1
        simp [Nat.not_prime_one] at hprime
      · have hp2 : p'' + 2 - 1 - 1 = p'' := by omega
        have hp_sub : p'' + 2 - 1 = p'' + 1 := by omega
        have hstep :
            (t : F[X]) * f ^ (t - 1) * Polynomial.derivative f * B ^ (p'' + 1) +
            f ^ t * ((p'' + 1 : ℕ) : F[X]) * B ^ p'' * Polynomial.derivative B =
            f ^ (t - 1) * B ^ p'' *
              ((t : F[X]) * (Polynomial.derivative f * B) - f * Polynomial.derivative B) := by
          have hf_split : f ^ t = f ^ (t - 1) * f := by
            conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
          have hB_split : B ^ (p'' + 1) = B ^ p'' * B := by rw [pow_succ]
          have hcast' : ((p'' + 1 : ℕ) : F[X]) = -1 := by
            rw [← map_natCast C, show ((p'' + 1 : ℕ) : F) = -1 by simpa [hp_sub] using hcast,
              map_neg, map_one]
          rw [hf_split, hB_split, hcast']
          ring
        have hzero :
            (t : F[X]) * (Polynomial.derivative f * B) - f * Polynomial.derivative B = 0 := by
          rw [← Polynomial.C_eq_natCast, ← Polynomial.smul_eq_C_mul, hmul_eq, sub_self]
        simpa [hp2, hp_sub, hzero, mul_assoc] using hstep
  have hprod_exp : expand F p (contract p (f ^ t * B ^ (p - 1))) = f ^ t * B ^ (p - 1) :=
    expand_contract p hderiv_prod hp.ne'
  have heq : B * expand F p (contract p (f ^ t * B ^ (p - 1))) =
      f ^ t * expand F p (contract p (B ^ p)) := by
    rw [hprod_exp, hBp_exp]
    have hp1 : 1 + (p - 1) = p := by omega
    calc B * (f ^ t * B ^ (p - 1)) = f ^ t * (B ^ 1 * B ^ (p - 1)) := by ring
      _ = f ^ t * B ^ p := by rw [← pow_add, hp1]
  have hft_deg : (f ^ t).natDegree < p := by
    calc (f ^ t).natDegree ≤ t * f.natDegree := Polynomial.natDegree_pow_le
      _ < p := hft
  have hBp_ne : expand F p (contract p (B ^ p)) ≠ 0 := by
    rw [hBp_exp]; exact pow_ne_zero p hB
  exact eq_C_mul_of_mul_expand_eq hp hB (pow_ne_zero t hf)
    ((expand_ne_zero hp).mp hBp_ne) hBdeg hft_deg heq

/-- **Consecutive zero coefficients in polynomial powers (characteristic `p`)**:
if `f ^ t = A * X ^ ℓ + B` over a field `F` of characteristic `p`, with `f.natDegree ≤ d`,
`B.natDegree ≤ b`, `t * d < p`, `b < p`, `A ≠ 0`, and `B ≠ 0`, then `ℓ ≤ d + b`.
-/
theorem consecutiveZeroCoeffs_pow_charP {f A B : F[X]} {t d b ℓ : ℕ}
    (heq : f ^ t = A * X ^ ℓ + B)
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b)
    (hdp : t * d < p) (hbp : b < p)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ℓ ≤ d + b := by
  by_contra hlt
  push Not at hlt
  have hℓ_pos : 1 ≤ ℓ := by omega
  have hB_lt : B.natDegree < ℓ := by omega
  have hAX_deg : (A * X ^ ℓ).natDegree = A.natDegree + ℓ := by
    rw [Polynomial.natDegree_mul hA (pow_ne_zero ℓ X_ne_zero), Polynomial.natDegree_X_pow]
  have hft_ne : f ^ t ≠ 0 := by
    intro h0
    have hBeq : B = -(A * X ^ ℓ) := by
      have := h0.symm.trans heq
      exact eq_neg_of_add_eq_zero_right this.symm
    have hdeg_eq : B.natDegree = A.natDegree + ℓ := by
      rw [hBeq, Polynomial.natDegree_neg, hAX_deg]
    omega
  have hf_ne : f ≠ 0 := by
    intro h0
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · have : (1 : F[X]) = A * X ^ ℓ + B := by simpa using heq
      have h1 : (A * X ^ ℓ + B).natDegree = A.natDegree + ℓ := by
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega), hAX_deg]
      rw [← this, Polynomial.natDegree_one] at h1
      omega
    · exact hft_ne (by rw [h0, zero_pow ht.ne'])
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h1 : (1 : F[X]) = A * X ^ ℓ + B := by simpa using heq
    have hdeg : (A * X ^ ℓ + B).natDegree = A.natDegree + ℓ := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega), hAX_deg]
    rw [← h1, Polynomial.natDegree_one] at hdeg
    omega
  have hderiv : Polynomial.derivative (f ^ t) =
      (Polynomial.derivative A * X + (ℓ : F) • A) * X ^ (ℓ - 1) + Polynomial.derivative B := by
    rw [heq, map_add, Polynomial.derivative_mul, Polynomial.derivative_X_pow]
    have hX : (X : F[X]) ^ ℓ = X * X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    conv_lhs => rw [hX]
    rw [Polynomial.smul_eq_C_mul]
    ring
  rw [Polynomial.derivative_pow, C_eq_natCast] at hderiv
  set Cpoly : F[X] := Polynomial.derivative A * X + (ℓ : F) • A
  have hmul :
      (t : F[X]) * Polynomial.derivative f * A * X ^ ℓ +
      (t : F[X]) * Polynomial.derivative f * B =
      f * Cpoly * X ^ (ℓ - 1) + f * Polynomial.derivative B := by
    have h1 : (t : F[X]) * Polynomial.derivative f * f ^ t =
        (t : F[X]) * Polynomial.derivative f * A * X ^ ℓ +
        (t : F[X]) * Polynomial.derivative f * B := by
      rw [heq]; ring
    have h2 : (t : F[X]) * Polynomial.derivative f * f ^ t =
        f * ((t : F[X]) * f ^ (t - 1) * Polynomial.derivative f) := by
      have ht_eq : f ^ t = f ^ (t - 1) * f := by
        conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
      rw [ht_eq]; ring
    rw [← h1, h2, hderiv]
    ring
  have hsub :
      (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B =
      (f * Cpoly - (t : F[X]) * Polynomial.derivative f * A * X) * X ^ (ℓ - 1) := by
    have hX : (X : F[X]) ^ ℓ = X * X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    calc (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B
        = f * Cpoly * X ^ (ℓ - 1) - (t : F[X]) * Polynomial.derivative f * A * X ^ ℓ := by
          linear_combination hmul
      _ = (f * Cpoly - (t : F[X]) * Polynomial.derivative f * A * X) * X ^ (ℓ - 1) := by
          rw [hX]; ring
  have hlog_zero : (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B = 0 := by
    by_contra hne
    have hℓ2 : 2 ≤ ℓ :=
      two_le_of_derivative_sub_ne_zero (c := (t : F)) (g := f) hfd hBb hlt
        (by simpa [Algebra.smul_def, C_eq_natCast] using hne)
    have hdeg_left1 : ((t : F[X]) * Polynomial.derivative f * B).natDegree < ℓ - 1 := by
      simpa [Algebra.smul_def, C_eq_natCast] using
        natDegree_smul_derivative_mul_lt (c := (t : F)) hfd hBb hlt hℓ2
    have hdeg_left2 : (f * Polynomial.derivative B).natDegree < ℓ - 1 :=
      natDegree_mul_derivative_lt hfd hBb hlt hℓ2
    have hdvd : X ^ (ℓ - 1) ∣
        (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B :=
      ⟨f * Cpoly - (t : F[X]) * Polynomial.derivative f * A * X, by rw [hsub, mul_comm]⟩
    have hle : (X ^ (ℓ - 1) : F[X]).natDegree ≤
        ((t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hne
    rw [Polynomial.natDegree_X_pow] at hle
    have hlt_sub : ((t : F[X]) * Polynomial.derivative f * B -
        f * Polynomial.derivative B).natDegree < ℓ - 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdeg_left1 hdeg_left2)
    omega
  have hlog : (t : F) • (Polynomial.derivative f * B) = f * Polynomial.derivative B := by
    rw [Algebra.smul_def, eq_comm, ← sub_eq_zero]
    simpa [mul_assoc, C_eq_natCast] using (neg_eq_zero.mpr hlog_zero)
  have hft_lt : t * f.natDegree < p := lt_of_le_of_lt (Nat.mul_le_mul_left t hfd) hdp
  have hB_lt_p : B.natDegree < p := lt_of_le_of_lt hBb hbp
  obtain ⟨c, _, hc⟩ := eq_smul_of_logDeriv_eq_charP hf_ne hB hft_lt hB_lt_p hlog
  have hAX_eq : A * X ^ ℓ = C (c - 1) * B := by
    have : A * X ^ ℓ + B = C c * B := heq.symm.trans hc
    rw [map_sub, map_one]
    linear_combination this
  have hc1 : c - 1 ≠ 0 := by
    intro h0
    have : A * X ^ ℓ = 0 := by rw [hAX_eq, h0, map_zero, zero_mul]
    exact mul_ne_zero hA (pow_ne_zero ℓ X_ne_zero) this
  have hdeg_eq : A.natDegree + ℓ = B.natDegree := by
    rw [← hAX_deg, hAX_eq, Polynomial.natDegree_C_mul hc1]
  omega

end PositiveChar

section CharZeroPowerSeries

variable {F : Type*} [Field F] [CharZero F]

/-- In characteristic zero, if two formal power series `B ≠ 0` and `g` satisfy
`B * d⁄dX g = d⁄dX B * g`, then `g = C c * B` for some scalar `c : F`. -/
theorem eq_C_mul_of_mul_derivative_eq_powerSeries {B g : F⟦X⟧}
    (hB : B ≠ 0) (heq : B * d⁄dX g = d⁄dX B * g) :
    ∃ c : F, g = PowerSeries.C c * B := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg]⟩
  set k := B.order.toNat
  set m := g.order.toNat
  set U := B.divXPowOrder
  set V := g.divXPowOrder
  have hB_fac : (PowerSeries.X : F⟦X⟧) ^ k * U = B := PowerSeries.X_pow_order_mul_divXPowOrder
  have hg_fac : (PowerSeries.X : F⟦X⟧) ^ m * V = g := PowerSeries.X_pow_order_mul_divXPowOrder
  have hU_coeff : PowerSeries.constantCoeff U ≠ 0 := by
    have := PowerSeries.coeff_order hB
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa [U, k] using this
  have hU_unit : IsUnit U :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hU_coeff)
  have hkm : m = k := by
    by_contra hne
    have hcoeff_B : PowerSeries.coeff k B ≠ 0 := PowerSeries.coeff_order hB
    have hcoeff_g : PowerSeries.coeff m g ≠ 0 := PowerSeries.coeff_order hg
    have h_lt_B : ∀ i < k, PowerSeries.coeff i B = 0 := fun i hi ↦
      PowerSeries.coeff_of_lt_order_toNat i hi
    have h_lt_g : ∀ i < m, PowerSeries.coeff i g = 0 := fun i hi ↦
      PowerSeries.coeff_of_lt_order_toNat i hi
    have h0 := congrArg (PowerSeries.coeff (k + m - 1)) heq
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul] at h0
    have hsum1 :
        ∑ p ∈ Finset.antidiagonal (k + m - 1), PowerSeries.coeff p.1 B *
          PowerSeries.coeff p.2 (d⁄dX g) =
        PowerSeries.coeff k B * (PowerSeries.coeff m g * (m : F)) := by
      by_cases hm0 : m = 0
      · rw [hm0]
        simp only [Nat.cast_zero, mul_zero, add_zero]
        apply Finset.sum_eq_zero
        intro p hp
        have hp_eq := Finset.mem_antidiagonal.mp hp
        have : p.1 < k := by omega
        rw [h_lt_B p.1 this, zero_mul]
      · rw [Finset.sum_eq_single (k, m - 1)]
        · rw [PowerSeries.coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
        · rintro ⟨p1, p2⟩ hp hpne
          have hp_eq := Finset.mem_antidiagonal.mp hp
          by_cases h1 : p1 < k
          · rw [h_lt_B p1 h1, zero_mul]
          · have h2 : p2 + 1 < m := by
              by_cases hpk : p1 = k
              · have : p2 ≠ m - 1 := fun h2 ↦ hpne (Prod.ext hpk h2)
                omega
              · omega
            rw [PowerSeries.coeff_derivative, h_lt_g (p2 + 1) h2, zero_mul, mul_zero]
        · intro hmem
          exfalso; apply hmem
          rw [Finset.mem_antidiagonal]; omega
    have hsum2 :
        ∑ p ∈ Finset.antidiagonal (k + m - 1), PowerSeries.coeff p.1 (d⁄dX B) *
          PowerSeries.coeff p.2 g =
        PowerSeries.coeff k B * (k : F) * PowerSeries.coeff m g := by
      by_cases hk0 : k = 0
      · rw [hk0]
        simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
        apply Finset.sum_eq_zero
        intro p hp
        have hp_eq := Finset.mem_antidiagonal.mp hp
        have : p.2 < m := by omega
        rw [h_lt_g p.2 this, mul_zero]
      · rw [Finset.sum_eq_single (k - 1, m)]
        · rw [PowerSeries.coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
        · rintro ⟨p1, p2⟩ hp hpne
          have hp_eq := Finset.mem_antidiagonal.mp hp
          by_cases h2 : p2 < m
          · rw [h_lt_g p2 h2, mul_zero]
          · have h1 : p1 + 1 < k := by
              by_cases hp1 : p1 = k - 1
              · have : p2 ≠ m := fun h2 ↦ hpne (Prod.ext hp1 h2)
                omega
              · omega
            rw [PowerSeries.coeff_derivative, h_lt_B (p1 + 1) h1, zero_mul, zero_mul]
        · intro hmem
          exfalso; apply hmem
          rw [Finset.mem_antidiagonal]; omega
    rw [hsum1, hsum2] at h0
    have hdiff : PowerSeries.coeff k B * PowerSeries.coeff m g * ((m : F) - (k : F)) = 0 := by
      linear_combination h0
    have hmk_eq : (m : F) = (k : F) := by
      have hne_prod : PowerSeries.coeff k B * PowerSeries.coeff m g ≠ 0 :=
        mul_ne_zero hcoeff_B hcoeff_g
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hne_prod)
    exact hne (Nat.cast_injective hmk_eq)
  have hUV : U * d⁄dX V = d⁄dX U * V := by
    have h1 : (PowerSeries.X : F⟦X⟧) ^ (2 * k) * (U * d⁄dX V - d⁄dX U * V) = 0 := by
      have hB' : d⁄dX B = PowerSeries.C (k : F) * PowerSeries.X ^ (k - 1) * U +
          PowerSeries.X ^ k * d⁄dX U := by
        rw [← hB_fac, Derivation.leibniz, PowerSeries.derivative_X_pow]
        simp only [smul_eq_mul]
        ring
      have hg' : d⁄dX g = PowerSeries.C (k : F) * PowerSeries.X ^ (k - 1) * V +
          PowerSeries.X ^ k * d⁄dX V := by
        rw [← hg_fac, hkm, Derivation.leibniz, PowerSeries.derivative_X_pow]
        simp only [smul_eq_mul]
        ring
      have hsub : B * d⁄dX g - d⁄dX B * g = 0 := sub_eq_zero.mpr heq
      rw [hB', hg'] at hsub
      rw [← hB_fac, ← hg_fac, hkm] at hsub
      have hpow : (PowerSeries.X : F⟦X⟧) ^ (2 * k) =
          (PowerSeries.X : F⟦X⟧) ^ k * (PowerSeries.X : F⟦X⟧) ^ k := by
        rw [two_mul, pow_add]
      rw [hpow]
      linear_combination hsub
    have hX_ne : (PowerSeries.X : F⟦X⟧) ^ (2 * k) ≠ 0 :=
      pow_ne_zero _ PowerSeries.X_ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hX_ne)
  obtain ⟨u, hu⟩ := hU_unit
  rw [← hu] at hUV hB_fac
  have hd : d⁄dX (V * (↑u⁻¹ : F⟦X⟧)) = 0 := by
    rw [Derivation.leibniz, PowerSeries.derivative_inv]
    simp only [smul_eq_mul]
    have hmul_inv : (u : F⟦X⟧) * (↑u⁻¹ : F⟦X⟧) = 1 := by simp
    calc V * (-(↑u⁻¹ : F⟦X⟧) ^ 2 * d⁄dX (u : F⟦X⟧)) + (↑u⁻¹ : F⟦X⟧) * d⁄dX V
        = (↑u⁻¹ : F⟦X⟧) ^ 2 * ((u : F⟦X⟧) * d⁄dX V - d⁄dX (u : F⟦X⟧) * V) := by
          calc V * (-(↑u⁻¹ : F⟦X⟧) ^ 2 * d⁄dX (u : F⟦X⟧)) + (↑u⁻¹ : F⟦X⟧) * d⁄dX V
              = -(↑u⁻¹ : F⟦X⟧) ^ 2 * (d⁄dX (u : F⟦X⟧) * V) +
                ((u : F⟦X⟧) * (↑u⁻¹ : F⟦X⟧)) * (↑u⁻¹ : F⟦X⟧) * d⁄dX V := by
                rw [hmul_inv, one_mul]; ring
            _ = (↑u⁻¹ : F⟦X⟧) ^ 2 * ((u : F⟦X⟧) * d⁄dX V - d⁄dX (u : F⟦X⟧) * V) := by ring
      _ = 0 := by rw [hUV, sub_self, mul_zero]
  set c : F := PowerSeries.constantCoeff (V * (↑u⁻¹ : F⟦X⟧))
  have hVu : V * (↑u⁻¹ : F⟦X⟧) = PowerSeries.C c := by
    apply PowerSeries.derivative.ext
    · rw [hd, PowerSeries.derivative_C]
    · simp [c]
  refine ⟨c, ?_⟩
  rw [← hg_fac, ← hB_fac, hkm]
  have hV_eq : V = PowerSeries.C c * (u : F⟦X⟧) := by
    calc V = V * ((↑u⁻¹ : F⟦X⟧) * (u : F⟦X⟧)) := by simp
      _ = (V * (↑u⁻¹ : F⟦X⟧)) * (u : F⟦X⟧) := by ring
      _ = PowerSeries.C c * (u : F⟦X⟧) := by rw [hVu]
  rw [hV_eq]
  ring

/-- **Consecutive zero coefficients in polynomial powers (characteristic zero)**:
if `f ^ t = A * X ^ ℓ + B` over a field `F` of characteristic zero with `0 < t`, `f.natDegree ≤ d`,
`B.natDegree ≤ b`, `A ≠ 0`, and `B ≠ 0`, then `ℓ ≤ d + b`. -/
theorem consecutiveZeroCoeffs_pow_charZero {f A B : F[X]} {t d b ℓ : ℕ}
    (ht : 0 < t) (heq : f ^ t = A * X ^ ℓ + B)
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ℓ ≤ d + b := by
  by_contra hlt
  push Not at hlt
  have hℓ_pos : 1 ≤ ℓ := by omega
  have hB_lt : B.natDegree < ℓ := by omega
  have hAX_deg : (A * X ^ ℓ).natDegree = A.natDegree + ℓ := by
    rw [Polynomial.natDegree_mul hA (pow_ne_zero ℓ X_ne_zero), Polynomial.natDegree_X_pow]
  have hderiv : Polynomial.derivative (f ^ t) =
      (Polynomial.derivative A * X + (ℓ : F) • A) * X ^ (ℓ - 1) + Polynomial.derivative B := by
    rw [heq, map_add, Polynomial.derivative_mul, Polynomial.derivative_X_pow]
    have hX : (X : F[X]) ^ ℓ = X * X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    conv_lhs => rw [hX]
    rw [Polynomial.smul_eq_C_mul]
    ring
  rw [Polynomial.derivative_pow, C_eq_natCast] at hderiv
  set Cpoly : F[X] := Polynomial.derivative A * X + (ℓ : F) • A
  have hsub :
      (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B =
      (f * Cpoly - (t : F[X]) * Polynomial.derivative f * A * X) * X ^ (ℓ - 1) := by
    have h1 : (t : F[X]) * Polynomial.derivative f * f ^ t =
        (t : F[X]) * Polynomial.derivative f * A * X ^ ℓ +
        (t : F[X]) * Polynomial.derivative f * B := by
      rw [heq]; ring
    have h2 : (t : F[X]) * Polynomial.derivative f * f ^ t =
        f * ((t : F[X]) * f ^ (t - 1) * Polynomial.derivative f) := by
      have ht_eq : f ^ t = f ^ (t - 1) * f := by
        conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
      rw [ht_eq]; ring
    have hX : (X : F[X]) ^ ℓ = X * X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    have h3 : (t : F[X]) * Polynomial.derivative f * A * X ^ ℓ +
        (t : F[X]) * Polynomial.derivative f * B =
        f * Cpoly * X ^ (ℓ - 1) + f * Polynomial.derivative B := by
      rw [← h1, h2, hderiv]; ring
    calc (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B
        = f * Cpoly * X ^ (ℓ - 1) - (t : F[X]) * Polynomial.derivative f * A * X ^ ℓ := by
          linear_combination h3
      _ = (f * Cpoly - (t : F[X]) * Polynomial.derivative f * A * X) * X ^ (ℓ - 1) := by
          rw [hX]; ring
  have hlog_zero : (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B = 0 := by
    by_contra hne
    have hℓ2 : 2 ≤ ℓ :=
      two_le_of_derivative_sub_ne_zero (c := (t : F)) (g := f) hfd hBb hlt
        (by simpa [Algebra.smul_def, C_eq_natCast] using hne)
    have hdeg_left1 : ((t : F[X]) * Polynomial.derivative f * B).natDegree < ℓ - 1 := by
      simpa [Algebra.smul_def, C_eq_natCast] using
        natDegree_smul_derivative_mul_lt (c := (t : F)) hfd hBb hlt hℓ2
    have hdeg_left2 : (f * Polynomial.derivative B).natDegree < ℓ - 1 :=
      natDegree_mul_derivative_lt hfd hBb hlt hℓ2
    have hdvd : X ^ (ℓ - 1) ∣
        (t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B :=
      ⟨f * Cpoly - (t : F[X]) * Polynomial.derivative f * A * X, by rw [hsub, mul_comm]⟩
    have hle : (X ^ (ℓ - 1) : F[X]).natDegree ≤
        ((t : F[X]) * Polynomial.derivative f * B - f * Polynomial.derivative B).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hne
    rw [Polynomial.natDegree_X_pow] at hle
    have hlt_sub : ((t : F[X]) * Polynomial.derivative f * B -
        f * Polynomial.derivative B).natDegree < ℓ - 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdeg_left1 hdeg_left2)
    omega
  have hps : (B : F⟦X⟧) * d⁄dX ((f ^ t : F[X]) : F⟦X⟧) =
      d⁄dX (B : F⟦X⟧) * ((f ^ t : F[X]) : F⟦X⟧) := by
    rw [PowerSeries.derivative_coe, PowerSeries.derivative_coe, ← Polynomial.coe_mul,
      ← Polynomial.coe_mul]
    congr 1
    rw [Polynomial.derivative_pow, C_eq_natCast]
    have hft_split : f ^ t = f ^ (t - 1) * f := by
      conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
    rw [hft_split]
    linear_combination f ^ (t - 1) * hlog_zero
  obtain ⟨c, hc⟩ := eq_C_mul_of_mul_derivative_eq_powerSeries
    (Polynomial.coe_eq_zero_iff.not.mpr hB) hps
  have hc_poly : f ^ t = C c * B := by
    apply Polynomial.coe_injective F
    simpa [Polynomial.coe_C] using hc
  have hAX_eq : A * X ^ ℓ = C (c - 1) * B := by
    have : A * X ^ ℓ + B = C c * B := heq.symm.trans hc_poly
    rw [map_sub, map_one]
    linear_combination this
  have hc1 : c - 1 ≠ 0 := by
    intro h0
    have : A * X ^ ℓ = 0 := by rw [hAX_eq, h0, map_zero, zero_mul]
    exact mul_ne_zero hA (pow_ne_zero ℓ X_ne_zero) this
  have hdeg_eq : A.natDegree + ℓ = B.natDegree := by
    rw [← hAX_deg, hAX_eq, Polynomial.natDegree_C_mul hc1]
  omega

/-- **Consecutive zero coefficients for solutions of `f * g' = t • f' * g` in `F⟦X⟧`**
: over a field `F` of characteristic zero, if `g = A * X ^ ℓ + B`
satisfies `(f : F⟦X⟧) * d⁄dX g = (t : F) • (derivative f : F⟦X⟧) * g` with `f ≠ 0`,
`f.natDegree ≤ d`, `B.natDegree ≤ b`, `A ≠ 0`, and `B ≠ 0`, then `ℓ ≤ d + b`.
-/
theorem consecutiveZeroCoeffs_powerSeries_of_logDeriv_eq {f B : F[X]} {A g : F⟦X⟧}
    {t : ℚ} {d b ℓ : ℕ}
    (hf : f ≠ 0) (heq : g = A * PowerSeries.X ^ ℓ + (B : F⟦X⟧))
    (hode : (f : F⟦X⟧) * d⁄dX g = (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g)
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ℓ ≤ d + b := by
  by_contra hlt
  push Not at hlt
  have hℓ_pos : 1 ≤ ℓ := by omega
  have hderiv : d⁄dX g = (d⁄dX A * PowerSeries.X + PowerSeries.C (ℓ : F) * A) *
      PowerSeries.X ^ (ℓ - 1) + ((Polynomial.derivative B : F[X]) : F⟦X⟧) := by
    rw [heq, map_add, Derivation.leibniz, PowerSeries.derivative_X_pow, PowerSeries.derivative_coe]
    simp only [smul_eq_mul]
    have hX : (PowerSeries.X : F⟦X⟧) ^ ℓ = PowerSeries.X * PowerSeries.X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    conv_lhs => rw [hX]
    ring
  set Cps : F⟦X⟧ := d⁄dX A * PowerSeries.X + PowerSeries.C (ℓ : F) * A
  have hdiff_ps :
      (((t : F) • Polynomial.derivative f * B - f * Polynomial.derivative B : F[X]) : F⟦X⟧) =
      ((f : F⟦X⟧) * Cps - (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A *
        PowerSeries.X) * PowerSeries.X ^ (ℓ - 1) := by
    have h1 : (f : F⟦X⟧) * d⁄dX g =
        (f : F⟦X⟧) * Cps * PowerSeries.X ^ (ℓ - 1) +
        ((f * Polynomial.derivative B : F[X]) : F⟦X⟧) := by
      rw [hderiv, Polynomial.coe_mul]; ring
    have h2 : (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g =
        (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A * PowerSeries.X ^ ℓ +
        (((t : F) • Polynomial.derivative f * B : F[X]) : F⟦X⟧) := by
      rw [heq, Polynomial.coe_mul, Polynomial.coe_smul]; ring
    have hX : (PowerSeries.X : F⟦X⟧) ^ ℓ = PowerSeries.X * PowerSeries.X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    rw [Polynomial.coe_sub]
    calc (((t : F) • Polynomial.derivative f * B : F[X]) : F⟦X⟧) -
          ((f * Polynomial.derivative B : F[X]) : F⟦X⟧)
        = (f : F⟦X⟧) * Cps * PowerSeries.X ^ (ℓ - 1) -
          (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A * PowerSeries.X ^ ℓ := by
          linear_combination (hode.symm.trans h1) - h2
      _ = ((f : F⟦X⟧) * Cps - (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A *
            PowerSeries.X) * PowerSeries.X ^ (ℓ - 1) := by
          rw [hX]; ring
  set P : F[X] := (t : F) • Polynomial.derivative f * B - f * Polynomial.derivative B
  have hP_zero : P = 0 := by
    by_contra hPne
    have hℓ2 : 2 ≤ ℓ := two_le_of_derivative_sub_ne_zero hfd hBb hlt hPne
    have hdeg_left1 : ((t : F) • Polynomial.derivative f * B).natDegree < ℓ - 1 :=
      natDegree_smul_derivative_mul_lt hfd hBb hlt hℓ2
    have hdeg_left2 : (f * Polynomial.derivative B).natDegree < ℓ - 1 :=
      natDegree_mul_derivative_lt hfd hBb hlt hℓ2
    have hP_deg : P.natDegree < ℓ - 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdeg_left1 hdeg_left2)
    have hcoeff : PowerSeries.coeff P.natDegree (P : F⟦X⟧) = P.leadingCoeff := by
      rw [Polynomial.coeff_coe]; rfl
    have hcoeff_zero : PowerSeries.coeff P.natDegree (P : F⟦X⟧) = 0 := by
      rw [hdiff_ps]
      apply PowerSeries.coeff_of_lt_order
      calc (P.natDegree : ℕ∞) < (ℓ - 1 : ℕ) := by exact_mod_cast hP_deg
        _ = (PowerSeries.X ^ (ℓ - 1) : F⟦X⟧).order := (PowerSeries.order_X_pow _).symm
        _ ≤ _ := by
          rw [mul_comm]
          exact le_trans (by simp) (PowerSeries.le_order_mul _ _)
    rw [hcoeff] at hcoeff_zero
    exact hPne (Polynomial.leadingCoeff_eq_zero.mp hcoeff_zero)
  have hB_ode : (f : F⟦X⟧) * d⁄dX (B : F⟦X⟧) =
      (t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * (B : F⟦X⟧) := by
    rw [PowerSeries.derivative_coe, ← Polynomial.coe_mul, ← Polynomial.coe_smul,
      ← Polynomial.coe_mul]
    congr 1
    exact (sub_eq_zero.mp hP_zero).symm
  have hBg : (f : F⟦X⟧) * ((B : F⟦X⟧) * d⁄dX g - d⁄dX (B : F⟦X⟧) * g) = 0 := by
    calc (f : F⟦X⟧) * ((B : F⟦X⟧) * d⁄dX g - d⁄dX (B : F⟦X⟧) * g)
        = (B : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) - g * ((f : F⟦X⟧) * d⁄dX (B : F⟦X⟧)) := by ring
      _ = (B : F⟦X⟧) * ((t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) -
          g * ((t : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * (B : F⟦X⟧)) := by
          rw [hode, hB_ode]
      _ = 0 := by ring
  have hBg' : (B : F⟦X⟧) * d⁄dX g = d⁄dX (B : F⟦X⟧) * g :=
    sub_eq_zero.mp ((mul_eq_zero.mp hBg).resolve_left (Polynomial.coe_eq_zero_iff.not.mpr hf))
  obtain ⟨c, hc⟩ := eq_C_mul_of_mul_derivative_eq_powerSeries
    (Polynomial.coe_eq_zero_iff.not.mpr hB) hBg'
  have hAX_eq : A * PowerSeries.X ^ ℓ = PowerSeries.C (c - 1) * (B : F⟦X⟧) := by
    have : A * PowerSeries.X ^ ℓ + (B : F⟦X⟧) = PowerSeries.C c * (B : F⟦X⟧) := heq.symm.trans hc
    rw [map_sub, map_one]
    linear_combination this
  obtain ⟨n, hn⟩ := PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mpr hA
  have hcoeff_AX : PowerSeries.coeff (n + ℓ) (A * PowerSeries.X ^ ℓ) = PowerSeries.coeff n A :=
    PowerSeries.coeff_mul_X_pow A ℓ n
  have hcoeff_rhs : PowerSeries.coeff (n + ℓ) (PowerSeries.C (c - 1) * (B : F⟦X⟧)) = 0 := by
    rw [PowerSeries.coeff_C_mul, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  rw [hAX_eq, hcoeff_rhs] at hcoeff_AX
  exact hn hcoeff_AX.symm

/-- **Consecutive zero coefficients in rational powers of polynomials**
: over a field `F` of characteristic zero, if `g ∈ F⟦X⟧` satisfies
`g ^ s = (f : F⟦X⟧) ^ r` with `0 < s`, `f ≠ 0`, `f.natDegree ≤ d`, `B.natDegree ≤ b`, `A ≠ 0`,
`B ≠ 0`, and `g = A * X ^ ℓ + B`, then `ℓ ≤ d + b`.
-/
theorem consecutiveZeroCoeffs_powerSeries_ratPow {f B : F[X]} {A g : F⟦X⟧}
    {r s d b ℓ : ℕ} (hs : 0 < s) (hf : f ≠ 0)
    (hpow : g ^ s = (f : F⟦X⟧) ^ r)
    (heq : g = A * PowerSeries.X ^ ℓ + (B : F⟦X⟧))
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ℓ ≤ d + b := by
  have hode : (f : F⟦X⟧) * d⁄dX g =
      (((r : ℚ) / (s : ℚ) : ℚ) : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by
    have hdiff := congrArg d⁄dX hpow
    rw [PowerSeries.derivative_pow, PowerSeries.derivative_pow, PowerSeries.derivative_coe] at hdiff
    have hmul : (f : F⟦X⟧) ^ r * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) -
        (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) = 0 := by
      have hg_split : g ^ s = g ^ (s - 1) * g := by
        conv_lhs => rw [← Nat.sub_add_cancel hs, pow_succ]
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [pow_zero, Nat.cast_zero, zero_mul, one_mul, sub_zero] at hdiff ⊢
        have : (s : F⟦X⟧) * g ^ (s - 1) * d⁄dX g * g = 0 := by rw [hdiff, zero_mul]
        calc (s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g)
            = (f : F⟦X⟧) * ((s : F⟦X⟧) * d⁄dX g) := by ring
          _ = (f : F⟦X⟧) * ((s : F⟦X⟧) * d⁄dX g * (g ^ (s - 1) * g)) := by
            rw [← hg_split, hpow, pow_zero, mul_one]
          _ = (f : F⟦X⟧) * ((s : F⟦X⟧) * g ^ (s - 1) * d⁄dX g * g) := by ring
          _ = 0 := by rw [this, mul_zero]
      · have hf_split : (f : F⟦X⟧) ^ r = (f : F⟦X⟧) ^ (r - 1) * (f : F⟦X⟧) := by
          conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ]
        calc (f : F⟦X⟧) ^ r * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) -
              (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g)
            = (f : F⟦X⟧) * g * ((s : F⟦X⟧) * g ^ (s - 1) * d⁄dX g -
              (r : F⟦X⟧) * (f : F⟦X⟧) ^ (r - 1) * ((Polynomial.derivative f : F[X]) : F⟦X⟧)) := by
              calc (f : F⟦X⟧) ^ r * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) -
                    (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g)
                  = g ^ s * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g)) -
                    (f : F⟦X⟧) ^ r *
                      ((r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) := by
                    rw [hpow]; ring
                _ = (g ^ (s - 1) * g) * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g)) -
                    ((f : F⟦X⟧) ^ (r - 1) * (f : F⟦X⟧)) *
                      ((r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) := by
                    rw [← hg_split, ← hf_split]
                _ = (f : F⟦X⟧) * g * ((s : F⟦X⟧) * g ^ (s - 1) * d⁄dX g -
                    (r : F⟦X⟧) * (f : F⟦X⟧) ^ (r -
                      1) * ((Polynomial.derivative f : F[X]) : F⟦X⟧)) := by
                    ring
          _ = 0 := by rw [hdiff, sub_self, mul_zero]
    have hfr_ne : (f : F⟦X⟧) ^ r ≠ 0 := pow_ne_zero r (Polynomial.coe_eq_zero_iff.not.mpr hf)
    have hsr : (s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) =
        (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g :=
      sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hfr_ne)
    have hs_ne : (s : F) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
    have hcast_div : (((r : ℚ) / (s : ℚ) : ℚ) : F) = (r : F) / (s : F) := by push_cast; rfl
    rw [hcast_div, Algebra.smul_def, ← PowerSeries.C_eq_algebraMap]
    have hmul_s : (PowerSeries.C (s : F)) * ((f : F⟦X⟧) * d⁄dX g) =
        (PowerSeries.C (s : F)) * ((PowerSeries.C ((r : F) / (s : F))) *
          ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) := by
      have hCs : PowerSeries.C (s : F) * PowerSeries.C ((r : F) / (s : F)) =
          PowerSeries.C (r : F) := by
        rw [← map_mul, mul_div_cancel₀ _ hs_ne]
      calc PowerSeries.C (s : F) * ((f : F⟦X⟧) * d⁄dX g)
          = (s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) := by rw [map_natCast]
        _ = (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := hsr
        _ = PowerSeries.C (r : F) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by
            rw [map_natCast]
        _ = (PowerSeries.C (s : F) * PowerSeries.C ((r : F) / (s : F))) *
            ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by rw [hCs]
        _ = PowerSeries.C (s : F) * (PowerSeries.C ((r : F) / (s : F)) *
            ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) := by ring
    have hCs_ne : (PowerSeries.C (s : F) : F⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg PowerSeries.constantCoeff h0
      exact hs_ne (by simpa using this)
    simpa [PowerSeries.C_eq_algebraMap] using mul_left_cancel₀ hCs_ne hmul_s
  exact consecutiveZeroCoeffs_powerSeries_of_logDeriv_eq hf heq hode hfd hBb hA hB

/-- **Consecutive zero coefficients in negative rational powers of polynomials**
: over a field `F` of characteristic zero, if
`g ^ s * (f : F⟦X⟧) ^ r = 1` with `0 < s`, `f ≠ 0`, `f.natDegree ≤ d`, `B.natDegree ≤ b`,
`A ≠ 0`, `B ≠ 0`, and `g = A * X ^ ℓ + B`, then `ℓ ≤ d + b`.
-/
theorem consecutiveZeroCoeffs_powerSeries_negRatPow {f B : F[X]} {A g : F⟦X⟧}
    {r s d b ℓ : ℕ} (hs : 0 < s) (hf : f ≠ 0)
    (hpow : g ^ s * (f : F⟦X⟧) ^ r = 1)
    (heq : g = A * PowerSeries.X ^ ℓ + (B : F⟦X⟧))
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ℓ ≤ d + b := by
  have hode : (f : F⟦X⟧) * d⁄dX g =
      (((-(r : ℚ)) / (s : ℚ) : ℚ) : F) • ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by
    have hdiff := congrArg d⁄dX hpow
    rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_pow,
      PowerSeries.derivative_coe, PowerSeries.derivative_one] at hdiff
    simp only [smul_eq_mul] at hdiff
    have hg_split : g ^ s = g ^ (s - 1) * g := by
      conv_lhs => rw [← Nat.sub_add_cancel hs, pow_succ]
    have hsr : (s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) =
        -(r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by
      have hmul : (g ^ s * (f : F⟦X⟧) ^ r) * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) +
          (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) = 0 := by
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · simp only [pow_zero, mul_one, one_mul, Nat.cast_zero, zero_mul, mul_zero, zero_add,
            add_zero] at hdiff ⊢
          calc g ^ s * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g))
              = (f : F⟦X⟧) * g * ((s : F⟦X⟧) * g ^ (s - 1) * d⁄dX g) := by
                rw [hg_split]; ring
            _ = 0 := by rw [hdiff, mul_zero]
        · have hf_split : (f : F⟦X⟧) ^ r = (f : F⟦X⟧) ^ (r - 1) * (f : F⟦X⟧) := by
            conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ]
          calc (g ^ s * (f : F⟦X⟧) ^ r) * ((s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) +
                (r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g)
              = (f : F⟦X⟧) * g * (g ^ s * ((r : F⟦X⟧) * (f : F⟦X⟧) ^ (r - 1) *
                  ((Polynomial.derivative f : F[X]) : F⟦X⟧)) +
                  (f : F⟦X⟧) ^ r * ((s : F⟦X⟧) * g ^ (s - 1) * d⁄dX g)) := by
                rw [hg_split, hf_split]
                ring
            _ = 0 := by rw [hdiff, mul_zero]
      rw [hpow, one_mul] at hmul
      linear_combination hmul
    have hs_ne : (s : F) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
    have hcast_div : (((-(r : ℚ)) / (s : ℚ) : ℚ) : F) = -(r : F) / (s : F) := by push_cast; rfl
    rw [hcast_div, Algebra.smul_def, ← PowerSeries.C_eq_algebraMap]
    have hmul_s : (PowerSeries.C (s : F)) * ((f : F⟦X⟧) * d⁄dX g) =
        (PowerSeries.C (s : F)) * (PowerSeries.C (-(r : F) / (s : F)) *
          ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) := by
      have hCs : PowerSeries.C (s : F) * PowerSeries.C (-(r : F) / (s : F)) =
          PowerSeries.C (-(r : F)) := by
        rw [← map_mul, mul_div_cancel₀ _ hs_ne]
      calc PowerSeries.C (s : F) * ((f : F⟦X⟧) * d⁄dX g)
          = (s : F⟦X⟧) * ((f : F⟦X⟧) * d⁄dX g) := by rw [map_natCast]
        _ = -(r : F⟦X⟧) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := hsr
        _ = PowerSeries.C (-(r : F)) * ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by
            rw [map_neg, map_natCast]
        _ = (PowerSeries.C (s : F) * PowerSeries.C (-(r : F) / (s : F))) *
            ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by rw [hCs]
        _ = PowerSeries.C (s : F) * (PowerSeries.C (-(r : F) / (s : F)) *
            ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g) := by ring
    have hCs_ne : (PowerSeries.C (s : F) : F⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg PowerSeries.constantCoeff h0
      exact hs_ne (by simpa using this)
    simpa [PowerSeries.C_eq_algebraMap] using mul_left_cancel₀ hCs_ne hmul_s
  exact consecutiveZeroCoeffs_powerSeries_of_logDeriv_eq hf heq hode hfd hBb hA hB

/-- **Consecutive zero coefficients in exponentials of polynomials**:
over a field `F` of characteristic zero, if `f ∈ F[X]` has degree at most `d` and constant term `0`,
and `(PowerSeries.exp F).subst (f : F⟦X⟧) = A * X ^ ℓ + B` with `B.natDegree ≤ b`, `A ≠ 0`, and
`B ≠ 0`, then `ℓ ≤ d + b`.
-/
theorem consecutiveZeroCoeffs_powerSeries_exp {f B : F[X]} {A : F⟦X⟧} {d b ℓ : ℕ}
    (hf0 : f.coeff 0 = 0)
    (heq : (PowerSeries.exp F).subst (f : F⟦X⟧) = A * PowerSeries.X ^ ℓ + (B : F⟦X⟧))
    (hfd : f.natDegree ≤ d) (hBb : B.natDegree ≤ b)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ℓ ≤ d + b := by
  by_contra hlt
  push Not at hlt
  have hℓ_pos : 1 ≤ ℓ := by omega
  set g : F⟦X⟧ := (PowerSeries.exp F).subst (f : F⟦X⟧)
  have hsubst : PowerSeries.HasSubst (f : F⟦X⟧) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hf0]
  have hode : d⁄dX g = ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g := by
    change d⁄dX ((PowerSeries.exp F).subst (f : F⟦X⟧)) = _
    rw [PowerSeries.derivative_subst hsubst, PowerSeries.derivative_exp F,
      PowerSeries.derivative_coe, mul_comm]
  have hderiv : d⁄dX g = (d⁄dX A * PowerSeries.X + PowerSeries.C (ℓ : F) * A) *
      PowerSeries.X ^ (ℓ - 1) + ((Polynomial.derivative B : F[X]) : F⟦X⟧) := by
    rw [heq, map_add, Derivation.leibniz, PowerSeries.derivative_X_pow, PowerSeries.derivative_coe]
    simp only [smul_eq_mul]
    have hX : (PowerSeries.X : F⟦X⟧) ^ ℓ = PowerSeries.X * PowerSeries.X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    conv_lhs => rw [hX]
    ring
  set Cps : F⟦X⟧ := d⁄dX A * PowerSeries.X + PowerSeries.C (ℓ : F) * A
  have hdiff_ps :
      ((Polynomial.derivative f * B - Polynomial.derivative B : F[X]) : F⟦X⟧) =
      (Cps - ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A * PowerSeries.X) *
        PowerSeries.X ^ (ℓ - 1) := by
    have hX : (PowerSeries.X : F⟦X⟧) ^ ℓ = PowerSeries.X * PowerSeries.X ^ (ℓ - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hℓ_pos, pow_succ']
    have h1 : ((Polynomial.derivative f : F[X]) : F⟦X⟧) * g =
        ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A * PowerSeries.X ^ ℓ +
        ((Polynomial.derivative f * B : F[X]) : F⟦X⟧) := by
      rw [heq, Polynomial.coe_mul]; ring
    rw [Polynomial.coe_sub]
    calc ((Polynomial.derivative f * B : F[X]) : F⟦X⟧) - ((Polynomial.derivative B : F[X]) : F⟦X⟧)
        = Cps * PowerSeries.X ^ (ℓ - 1) -
          ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A * PowerSeries.X ^ ℓ := by
          linear_combination (hode.symm.trans hderiv) - h1
      _ = (Cps - ((Polynomial.derivative f : F[X]) : F⟦X⟧) * A * PowerSeries.X) *
            PowerSeries.X ^ (ℓ - 1) := by
          rw [hX]; ring
  set P : F[X] := Polynomial.derivative f * B - Polynomial.derivative B
  have hP_zero : P = 0 := by
    by_contra hPne
    have hℓ2 : 2 ≤ ℓ :=
      two_le_of_derivative_sub_ne_zero (c := (1 : F)) (g := (1 : F[X])) hfd hBb hlt
        (by simpa [P] using hPne)
    have hdeg_left1 : (Polynomial.derivative f * B).natDegree < ℓ - 1 := by
      simpa using natDegree_smul_derivative_mul_lt (c := (1 : F)) hfd hBb hlt hℓ2
    have hdeg_left2 : (Polynomial.derivative B).natDegree < ℓ - 1 := by
      simpa using natDegree_mul_derivative_lt (f := (1 : F[X])) (d := d)
        (by rw [natDegree_one]; omega) hBb hlt hℓ2
    have hP_deg : P.natDegree < ℓ - 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdeg_left1 hdeg_left2)
    have hcoeff : PowerSeries.coeff P.natDegree (P : F⟦X⟧) = P.leadingCoeff := by
      rw [Polynomial.coeff_coe]; rfl
    have hcoeff_zero : PowerSeries.coeff P.natDegree (P : F⟦X⟧) = 0 := by
      rw [hdiff_ps]
      apply PowerSeries.coeff_of_lt_order
      calc (P.natDegree : ℕ∞) < (ℓ - 1 : ℕ) := by exact_mod_cast hP_deg
        _ = (PowerSeries.X ^ (ℓ - 1) : F⟦X⟧).order := (PowerSeries.order_X_pow _).symm
        _ ≤ _ := by
          rw [mul_comm]
          exact le_trans (by simp) (PowerSeries.le_order_mul _ _)
    rw [hcoeff] at hcoeff_zero
    exact hPne (Polynomial.leadingCoeff_eq_zero.mp hcoeff_zero)
  have hB_ode : d⁄dX (B : F⟦X⟧) = ((Polynomial.derivative f : F[X]) : F⟦X⟧) * (B : F⟦X⟧) := by
    rw [PowerSeries.derivative_coe, ← Polynomial.coe_mul]
    congr 1
    exact (sub_eq_zero.mp hP_zero).symm
  have hBg : (B : F⟦X⟧) * d⁄dX g = d⁄dX (B : F⟦X⟧) * g := by
    rw [hode, hB_ode]; ring
  obtain ⟨c, hc⟩ := eq_C_mul_of_mul_derivative_eq_powerSeries
    (Polynomial.coe_eq_zero_iff.not.mpr hB) hBg
  have hAX_eq : A * PowerSeries.X ^ ℓ = PowerSeries.C (c - 1) * (B : F⟦X⟧) := by
    have : A * PowerSeries.X ^ ℓ + (B : F⟦X⟧) = PowerSeries.C c * (B : F⟦X⟧) := heq.symm.trans hc
    rw [map_sub, map_one]
    linear_combination this
  obtain ⟨n, hn⟩ := PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mpr hA
  have hcoeff_AX : PowerSeries.coeff (n + ℓ) (A * PowerSeries.X ^ ℓ) = PowerSeries.coeff n A :=
    PowerSeries.coeff_mul_X_pow A ℓ n
  have hcoeff_rhs : PowerSeries.coeff (n + ℓ) (PowerSeries.C (c - 1) * (B : F⟦X⟧)) = 0 := by
    rw [PowerSeries.coeff_C_mul, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  rw [hAX_eq, hcoeff_rhs] at hcoeff_AX
  exact hn hcoeff_AX.symm

/-- Tightness example for `consecutiveZeroCoeffs_pow_charZero`: `(X^d + 1)^2 = (X^d + 2) * X^d + 1`
achieves equality `ℓ = d + b` with `d = 2`, `b = 0`, `ℓ = 2`. -/
example :
    ((Polynomial.X ^ 2 + 1 : ℚ[X]) ^ 2) =
      (Polynomial.X ^ 2 + 2) * Polynomial.X ^ 2 + (1 : ℚ[X]) := by
  ring

end CharZeroPowerSeries

end CslibFrontier.Foundations.Algebra.Polynomial
