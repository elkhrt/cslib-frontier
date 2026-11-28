module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Order.Interval.Set.Defs
import CslibFrontier.Foundations.Analysis.MarkovBrothersInequality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fejér–Jackson Trigonometric Kernels and Rescaled Bernstein Inequality

Constructs the normalized real Fejér kernel `fejerReal`, the symmetrized Jackson-type Chebyshev
localization polynomial `jacksonPoly` peaking at a chosen angle, the cosine-coordinate square-root
distance lower bound `abs_sqrt_sub_sqrt_div_le_sin`, and Bernstein's polynomial derivative
inequality rescaled to `[0, n]`.

## Main definitions

* `CslibFrontier.Foundations.Analysis.fejerReal`: normalized Fejér kernel
  `(1 / r²) ‖∑_{j < r} exp(i j φ)‖²`.
* `CslibFrontier.Foundations.Analysis.jacksonPoly`: symmetrized Chebyshev localization polynomial
  of degree at most `s * (r - 1)` peaking at `cos θ₀`.

## Main results

* `CslibFrontier.Foundations.Analysis.fejerReal_nonneg`,
  `CslibFrontier.Foundations.Analysis.fejerReal_le_one`,
  `CslibFrontier.Foundations.Analysis.fejerReal_zero`,
  `CslibFrontier.Foundations.Analysis.fejerReal_le_inv_sin_sq`: basic range and decay properties
  of the Fejér kernel.
* `CslibFrontier.Foundations.Analysis.natDegree_jacksonPoly_le`,
  `CslibFrontier.Foundations.Analysis.eval_jacksonPoly_cos`,
  `CslibFrontier.Foundations.Analysis.eval_jacksonPoly_cos_self`,
  `CslibFrontier.Foundations.Analysis.eval_jacksonPoly_bounds`,
  `CslibFrontier.Foundations.Analysis.eval_jacksonPoly_cos_le`: degree, peak, `[0, 2]` bounds,
  and off-peak decay of `jacksonPoly`.
* `CslibFrontier.Foundations.Analysis.sin_arccos_half_eq_sqrt`,
  `CslibFrontier.Foundations.Analysis.abs_sqrt_sub_sqrt_div_le_sin`: cosine-coordinate distance
  bounds on `[0, n]`.
* `CslibFrontier.Foundations.Analysis.sqrt_mul_abs_eval_derivative_le_on_Icc`: Bernstein's
  derivative inequality rescaled to `[0, n]`.
-/

public section

namespace CslibFrontier.Foundations.Analysis

open Finset Polynomial Real
open Set (Icc)
open scoped BigOperators

section FejerJackson

/-- Absolute difference of two natural numbers. -/
private def natDist (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

/-- The normalized real Fejér kernel `K_r(φ) = (1 / r²) ‖∑_{j < r} exp(i j φ)‖²`. -/
noncomputable def fejerReal (r : ℕ) (φ : ℝ) : ℝ :=
  (1 / (r : ℝ) ^ 2) * ‖∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)‖ ^ 2

/-- `fejerReal r φ ≥ 0`. -/
theorem fejerReal_nonneg (r : ℕ) (φ : ℝ) : 0 ≤ fejerReal r φ := by
  unfold fejerReal
  positivity

/-- `fejerReal r φ ≤ 1` for `r ≥ 1`. -/
theorem fejerReal_le_one {r : ℕ} (hr : 1 ≤ r) (φ : ℝ) : fejerReal r φ ≤ 1 := by
  unfold fejerReal
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hnorm : ‖∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)‖ ≤ (r : ℝ) := by
    calc ‖∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)‖
        ≤ ∑ j ∈ range r, ‖Complex.exp (Complex.I * (j : ℝ) * φ)‖ := norm_sum_le _ _
      _ = ∑ _j ∈ range r, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have harg : Complex.I * ((j : ℝ) : ℂ) * (φ : ℂ) =
              (((j : ℝ) * φ : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [harg, Complex.norm_exp_ofReal_mul_I]
      _ = (r : ℝ) := by simp
  have hsq : ‖∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)‖ ^ 2 ≤ (r : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc (1 / (r : ℝ) ^ 2) * ‖∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)‖ ^ 2
      ≤ (1 / (r : ℝ) ^ 2) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 := by field_simp

/-- `fejerReal r 0 = 1` for `r ≥ 1`. -/
theorem fejerReal_zero {r : ℕ} (hr : 1 ≤ r) : fejerReal r 0 = 1 := by
  unfold fejerReal
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Complex.norm_natCast]
  field_simp

/-- `fejerReal r φ ≤ 1 / (r * sin (φ / 2)) ^ 2` whenever `r ≥ 1` and `sin (φ / 2) ≠ 0`. -/
theorem fejerReal_le_inv_sin_sq {r : ℕ} (hr : 1 ≤ r) {φ : ℝ} (hsin : Real.sin (φ / 2) ≠ 0) :
    fejerReal r φ ≤ 1 / ((r : ℝ) * Real.sin (φ / 2)) ^ 2 := by
  unfold fejerReal
  set ζ : ℂ := Complex.exp (Complex.I * (φ : ℂ))
  have hterm (j : ℕ) : Complex.exp (Complex.I * ((j : ℝ) : ℂ) * (φ : ℂ)) = ζ ^ j := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  have hζ_norm : ‖ζ‖ = 1 := by
    have harg : Complex.I * (φ : ℂ) = (φ : ℂ) * Complex.I := mul_comm _ _
    simp [ζ, harg, Complex.norm_exp_ofReal_mul_I]
  have hdiff_eq : ζ - 1 = Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ)) *
      (2 * Complex.I * (Real.sin (φ / 2) : ℂ)) := by
    have hsinC : (Real.sin (φ / 2) : ℂ) = Complex.sin ((φ / 2 : ℝ) : ℂ) := by
      simp [Complex.ofReal_sin]
    rw [hsinC, Complex.sin]
    have h1 : Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ)) = ζ := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h2 : Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((φ / 2 : ℝ) : ℂ))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hmul : ((φ / 2 : ℝ) : ℂ) * Complex.I = Complex.I * ((φ / 2 : ℝ) : ℂ) := mul_comm _ _
    have hneg : -((φ / 2 : ℝ) : ℂ) * Complex.I = -(Complex.I * ((φ / 2 : ℝ) : ℂ)) := by
      rw [neg_mul, hmul]
    rw [hneg, hmul]
    have h3 : (2 : ℂ) * Complex.I *
        ((Complex.exp (-(Complex.I * ((φ / 2 : ℝ) : ℂ))) -
            Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ))) * Complex.I / 2) =
        Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ)) -
          Complex.exp (-(Complex.I * ((φ / 2 : ℝ) : ℂ))) := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h3, mul_sub, h1, h2]
  have hdiff_norm : ‖ζ - 1‖ = 2 * |Real.sin (φ / 2)| := by
    rw [hdiff_eq, norm_mul, norm_mul, norm_mul]
    have hexp : ‖Complex.exp (Complex.I * ((φ / 2 : ℝ) : ℂ))‖ = 1 := by
      have harg : Complex.I * ((φ / 2 : ℝ) : ℂ) = ((φ / 2 : ℝ) : ℂ) * Complex.I := mul_comm _ _
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [hexp, one_mul, Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hζ_ne : ζ ≠ 1 := by
    intro h
    have : ‖ζ - 1‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [hdiff_norm] at this
    exact hsin (abs_eq_zero.mp (by linarith))
  rw [geom_sum_eq hζ_ne, norm_div]
  have hnum : ‖ζ ^ r - 1‖ ≤ 2 := by
    calc ‖ζ ^ r - 1‖ ≤ ‖ζ ^ r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖ζ‖ ^ r + 1 := by rw [norm_pow, norm_one]
      _ = 2 := by rw [hζ_norm, one_pow]; norm_num
  have hsin_pos : 0 < |Real.sin (φ / 2)| := abs_pos.mpr hsin
  have hsum_le : ‖ζ ^ r - 1‖ / ‖ζ - 1‖ ≤ 1 / |Real.sin (φ / 2)| := by
    rw [hdiff_norm]
    calc ‖ζ ^ r - 1‖ / (2 * |Real.sin (φ / 2)|)
        ≤ 2 / (2 * |Real.sin (φ / 2)|) := div_le_div_of_nonneg_right hnum (by positivity)
      _ = 1 / |Real.sin (φ / 2)| := by field_simp
  have hsq : (‖ζ ^ r - 1‖ / ‖ζ - 1‖) ^ 2 ≤ (1 / |Real.sin (φ / 2)|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum_le 2
  calc (1 / (r : ℝ) ^ 2) * (‖ζ ^ r - 1‖ / ‖ζ - 1‖) ^ 2
      ≤ (1 / (r : ℝ) ^ 2) * (1 / |Real.sin (φ / 2)|) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / ((r : ℝ) * Real.sin (φ / 2)) ^ 2 := by
          rw [div_pow, one_pow, sq_abs, mul_pow]
          ring

/-- Cosine expansion of `fejerReal r φ` with maximum frequency at most `r - 1`. -/
private theorem exists_cos_expansion_fejerReal {r : ℕ} (_hr : 1 ≤ r) :
    ∃ c : ℕ → ℝ, ∀ φ : ℝ, fejerReal r φ = ∑ t ∈ range r, c t * Real.cos ((t : ℝ) * φ) := by
  classical
  refine ⟨fun t => (1 / (r : ℝ) ^ 2) *
      (#((range r ×ˢ range r).filter fun p => natDist p.1 p.2 = t) : ℝ), fun φ => ?_⟩
  unfold fejerReal
  have hnorm_sq : ‖∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)‖ ^ 2 =
      ∑ p ∈ range r ×ˢ range r, Real.cos ((natDist p.1 p.2 : ℝ) * φ) := by
    set S : ℂ := ∑ j ∈ range r, Complex.exp (Complex.I * (j : ℝ) * φ)
    have h1 : ‖S‖ ^ 2 = (S * starRingEnd ℂ S).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [h1]
    have hconj : starRingEnd ℂ S = ∑ m ∈ range r, Complex.exp (-(Complex.I * (m : ℝ) * φ)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj, Finset.sum_mul_sum, ← Finset.sum_product', Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Complex.exp_add]
    have harg : Complex.I * ((p.1 : ℝ) : ℂ) * (φ : ℂ) + -(Complex.I * ((p.2 : ℝ) : ℂ) * (φ : ℂ)) =
        ((((p.1 : ℝ) - (p.2 : ℝ)) * φ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
    rcases le_or_gt p.1 p.2 with hle | hgt
    · have hdist : (natDist p.1 p.2 : ℝ) = (p.2 : ℝ) - (p.1 : ℝ) := by
        simp only [natDist, hle, ↓reduceIte, Nat.cast_sub hle]
      rw [hdist, ← Real.cos_neg]
      congr 1; ring
    · have hdist : (natDist p.1 p.2 : ℝ) = (p.1 : ℝ) - (p.2 : ℝ) := by
        have hnot : ¬ p.1 ≤ p.2 := not_le.mpr hgt
        simp only [natDist, hnot, ↓reduceIte, Nat.cast_sub hgt.le]
      rw [hdist]
  rw [hnorm_sq]
  have hgroup : ∑ p ∈ range r ×ˢ range r, Real.cos ((natDist p.1 p.2 : ℝ) * φ) =
      ∑ t ∈ range r, (#((range r ×ˢ range r).filter fun p => natDist p.1 p.2 = t) : ℝ) *
        Real.cos ((t : ℝ) * φ) := by
    have hmaps : ∀ p ∈ range r ×ˢ range r, natDist p.1 p.2 ∈ range r := by
      intro p hp
      rw [mem_product, mem_range, mem_range] at hp
      rw [mem_range]
      unfold natDist
      split_ifs <;> omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun t _ => ?_
    calc ∑ p ∈ (range r ×ˢ range r).filter (fun p => natDist p.1 p.2 = t),
            Real.cos ((natDist p.1 p.2 : ℝ) * φ)
        = ∑ _p ∈ (range r ×ˢ range r).filter (fun p => natDist p.1 p.2 = t),
            Real.cos ((t : ℝ) * φ) :=
            Finset.sum_congr rfl fun p hp => by rw [(mem_filter.mp hp).2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hgroup, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

/-- Product of two finite cosine sums is a finite cosine sum of degree at most their sum. -/
private theorem exists_cos_expansion_mul {d₁ d₂ : ℕ} {c₁ c₂ : ℕ → ℝ} :
    ∃ c : ℕ → ℝ, ∀ φ : ℝ,
      (∑ a ∈ range (d₁ + 1), c₁ a * Real.cos ((a : ℝ) * φ)) *
        (∑ b ∈ range (d₂ + 1), c₂ b * Real.cos ((b : ℝ) * φ)) =
        ∑ t ∈ range (d₁ + d₂ + 1), c t * Real.cos ((t : ℝ) * φ) := by
  classical
  refine ⟨fun t =>
      ∑ a ∈ range (d₁ + 1), ∑ b ∈ range (d₂ + 1),
        (c₁ a * c₂ b / 2) * ((if a + b = t then (1 : ℝ) else 0) +
          (if natDist a b = t then (1 : ℝ) else 0)),
    fun φ => ?_⟩
  have hcos_mul (a b : ℕ) :
      Real.cos ((a : ℝ) * φ) * Real.cos ((b : ℝ) * φ) =
        (Real.cos (((a + b : ℕ) : ℝ) * φ) + Real.cos ((natDist a b : ℝ) * φ)) / 2 := by
    have h1 := Real.cos_add ((a : ℝ) * φ) ((b : ℝ) * φ)
    have h2 := Real.cos_sub ((a : ℝ) * φ) ((b : ℝ) * φ)
    have hdist_cos : Real.cos ((a : ℝ) * φ - (b : ℝ) * φ) = Real.cos ((natDist a b : ℝ) * φ) := by
      rcases le_or_gt a b with hle | hgt
      · have hd : (natDist a b : ℝ) = (b : ℝ) - (a : ℝ) := by
          simp only [natDist, hle, ↓reduceIte, Nat.cast_sub hle]
        rw [hd, ← Real.cos_neg]; congr 1; ring
      · have hd : (natDist a b : ℝ) = (a : ℝ) - (b : ℝ) := by
          have hnot : ¬ a ≤ b := not_le.mpr hgt
          simp only [natDist, hnot, ↓reduceIte, Nat.cast_sub hgt.le]
        rw [hd]; congr 1; ring
    have hadd_cos : Real.cos ((a : ℝ) * φ + (b : ℝ) * φ) = Real.cos (((a + b : ℕ) : ℝ) * φ) := by
      push_cast; congr 1; ring
    linarith
  have h1 (a : ℕ) (ha : a ∈ range (d₁ + 1)) (b : ℕ) (hb : b ∈ range (d₂ + 1)) :
      ∑ t ∈ range (d₁ + d₂ + 1),
          ((c₁ a * c₂ b / 2) * ((if a + b = t then (1 : ℝ) else 0) +
            (if natDist a b = t then (1 : ℝ) else 0))) * Real.cos ((t : ℝ) * φ) =
        c₁ a * Real.cos ((a : ℝ) * φ) * (c₂ b * Real.cos ((b : ℝ) * φ)) := by
    have ha' : a ≤ d₁ := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hb' : b ≤ d₂ := Nat.lt_succ_iff.mp (mem_range.mp hb)
    have hsum_mem : a + b ∈ range (d₁ + d₂ + 1) := mem_range.mpr (by omega)
    have hdist_mem : natDist a b ∈ range (d₁ + d₂ + 1) :=
      mem_range.mpr (by unfold natDist; split_ifs <;> omega)
    have hsplit : ∀ t,
        ((c₁ a * c₂ b / 2) * ((if a + b = t then (1 : ℝ) else 0) +
            (if natDist a b = t then (1 : ℝ) else 0))) * Real.cos ((t : ℝ) * φ) =
          (if a + b = t then (c₁ a * c₂ b / 2) * Real.cos ((t : ℝ) * φ) else 0) +
            (if natDist a b = t then (c₁ a * c₂ b / 2) * Real.cos ((t : ℝ) * φ) else 0) := by
      intro t; split_ifs <;> ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, hsum_mem, hdist_mem, ↓reduceIte]
    rw [show c₁ a * Real.cos ((a : ℝ) * φ) * (c₂ b * Real.cos ((b : ℝ) * φ)) =
        c₁ a * c₂ b * (Real.cos ((a : ℝ) * φ) * Real.cos ((b : ℝ) * φ)) by ring, hcos_mul]
    ring
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  symm
  calc ∑ t ∈ range (d₁ + d₂ + 1),
          (∑ a ∈ range (d₁ + 1), ∑ b ∈ range (d₂ + 1),
            (c₁ a * c₂ b / 2) * ((if a + b = t then (1 : ℝ) else 0) +
              (if natDist a b = t then (1 : ℝ) else 0))) * Real.cos ((t : ℝ) * φ)
      = ∑ t ∈ range (d₁ + d₂ + 1), ∑ a ∈ range (d₁ + 1), ∑ b ∈ range (d₂ + 1),
          ((c₁ a * c₂ b / 2) * ((if a + b = t then (1 : ℝ) else 0) +
            (if natDist a b = t then (1 : ℝ) else 0))) * Real.cos ((t : ℝ) * φ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
    _ = ∑ a ∈ range (d₁ + 1), ∑ b ∈ range (d₂ + 1), ∑ t ∈ range (d₁ + d₂ + 1),
          ((c₁ a * c₂ b / 2) * ((if a + b = t then (1 : ℝ) else 0) +
            (if natDist a b = t then (1 : ℝ) else 0))) * Real.cos ((t : ℝ) * φ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => h1 a ha b hb

/-- Cosine expansion of `(fejerReal r φ) ^ s` with maximum frequency at most `s * (r - 1)`. -/
private theorem exists_cos_expansion_fejerReal_pow {r : ℕ} (hr : 1 ≤ r) (s : ℕ) :
    ∃ c : ℕ → ℝ, ∀ φ : ℝ,
      (fejerReal r φ) ^ s = ∑ t ∈ range (s * (r - 1) + 1), c t * Real.cos ((t : ℝ) * φ) := by
  induction s with
  | zero =>
    refine ⟨fun _ => 1, fun φ => by simp⟩
  | succ s ih =>
    obtain ⟨c₁, hc₁⟩ := ih
    obtain ⟨c₂, hc₂⟩ := exists_cos_expansion_fejerReal hr
    have hr1 : r = (r - 1) + 1 := by omega
    have hc₂' : ∀ φ : ℝ,
        fejerReal r φ = ∑ t ∈ range ((r - 1) + 1), c₂ t * Real.cos ((t : ℝ) * φ) :=
      fun φ => by simpa [hr1.symm] using hc₂ φ
    obtain ⟨c, hc⟩ := exists_cos_expansion_mul (d₁ := s * (r - 1)) (d₂ := r - 1)
      (c₁ := c₁) (c₂ := c₂)
    refine ⟨c, fun φ => ?_⟩
    rw [pow_succ, hc₁ φ, hc₂' φ, hc φ]
    have hdeg : (s + 1) * (r - 1) + 1 = s * (r - 1) + (r - 1) + 1 := by ring
    rw [hdeg]

/-- Symmetrized Jackson-type polynomial of degree at most `s * (r - 1)` satisfying
`jacksonPoly r s θ₀ (cos θ) = (K_r(θ - θ₀)^s + K_r(θ + θ₀)^s) / (1 + K_r(2 θ₀)^s)`. -/
noncomputable def jacksonPoly (r s : ℕ) (θ₀ : ℝ) : ℝ[X] :=
  if hr : 1 ≤ r then
    let c := (exists_cos_expansion_fejerReal_pow hr s).choose
    let Z : ℝ := (1 + (fejerReal r (2 * θ₀)) ^ s) / 2
    C Z⁻¹ * ∑ t ∈ range (s * (r - 1) + 1),
      C (c t * Real.cos ((t : ℝ) * θ₀)) * Chebyshev.T ℝ t
  else 1

/-- Degree bound for `jacksonPoly r s θ₀`. -/
theorem natDegree_jacksonPoly_le (r s : ℕ) (θ₀ : ℝ) :
    (jacksonPoly r s θ₀).natDegree ≤ s * (r - 1) := by
  unfold jacksonPoly
  split_ifs with hr
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
    exact Nat.lt_succ_iff.mp (mem_range.mp ht)
  · simp

/-- Exact cosine evaluation formula for `jacksonPoly r s θ₀`. -/
theorem eval_jacksonPoly_cos {r : ℕ} (hr : 1 ≤ r) (s : ℕ) (θ₀ θ : ℝ) :
    (jacksonPoly r s θ₀).eval (Real.cos θ) =
      ((fejerReal r (θ - θ₀)) ^ s + (fejerReal r (θ + θ₀)) ^ s) /
        (1 + (fejerReal r (2 * θ₀)) ^ s) := by
  unfold jacksonPoly
  simp only [hr, ↓reduceDIte]
  set c := (exists_cos_expansion_fejerReal_pow hr s).choose
  have hc : ∀ φ, (fejerReal r φ) ^ s =
      ∑ t ∈ range (s * (r - 1) + 1), c t * Real.cos ((t : ℝ) * φ) :=
    (exists_cos_expansion_fejerReal_pow hr s).choose_spec
  set Z : ℝ := (1 + (fejerReal r (2 * θ₀)) ^ s) / 2
  rw [eval_mul, eval_C, eval_finsetSum]
  have hsum : ∑ t ∈ range (s * (r - 1) + 1),
      (C (c t * Real.cos ((t : ℝ) * θ₀)) * Chebyshev.T ℝ t).eval (Real.cos θ) =
      ((fejerReal r (θ - θ₀)) ^ s + (fejerReal r (θ + θ₀)) ^ s) / 2 := by
    rw [hc (θ - θ₀), hc (θ + θ₀), ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [eval_mul, eval_C, Chebyshev.T_real_cos, Int.cast_natCast]
    have h1 := Real.cos_sub ((t : ℝ) * θ) ((t : ℝ) * θ₀)
    have h2 := Real.cos_add ((t : ℝ) * θ) ((t : ℝ) * θ₀)
    have hsub : (t : ℝ) * (θ - θ₀) = (t : ℝ) * θ - (t : ℝ) * θ₀ := by ring
    have hadd : (t : ℝ) * (θ + θ₀) = (t : ℝ) * θ + (t : ℝ) * θ₀ := by ring
    rw [hsub, hadd, h1, h2]
    ring
  rw [hsum]
  have hZpos : 0 < 1 + (fejerReal r (2 * θ₀)) ^ s := by
    have : 0 ≤ (fejerReal r (2 * θ₀)) ^ s := pow_nonneg (fejerReal_nonneg r _) s
    linarith
  simp only [Z]
  field_simp

/-- `jacksonPoly r s θ₀` evaluates to `1` at `cos θ₀`. -/
theorem eval_jacksonPoly_cos_self {r : ℕ} (hr : 1 ≤ r) (s : ℕ) (θ₀ : ℝ) :
    (jacksonPoly r s θ₀).eval (Real.cos θ₀) = 1 := by
  rw [eval_jacksonPoly_cos hr s θ₀ θ₀, sub_self, fejerReal_zero hr, one_pow, two_mul]
  have hpos : 0 < 1 + (fejerReal r (θ₀ + θ₀)) ^ s := by
    have : 0 ≤ (fejerReal r (θ₀ + θ₀)) ^ s := pow_nonneg (fejerReal_nonneg r _) s
    linarith
  exact div_self hpos.ne'

/-- On `[-1, 1]`, `jacksonPoly r s θ₀` takes values in `[0, 2]`. -/
theorem eval_jacksonPoly_bounds {r : ℕ} (hr : 1 ≤ r) (s : ℕ) (θ₀ : ℝ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ (jacksonPoly r s θ₀).eval x ∧ (jacksonPoly r s θ₀).eval x ≤ 2 := by
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  rw [← hcos, eval_jacksonPoly_cos hr s θ₀ (Real.arccos x)]
  have h1 : 0 ≤ (fejerReal r (Real.arccos x - θ₀)) ^ s := pow_nonneg (fejerReal_nonneg r _) s
  have h2 : 0 ≤ (fejerReal r (Real.arccos x + θ₀)) ^ s := pow_nonneg (fejerReal_nonneg r _) s
  have h3 : 0 ≤ (fejerReal r (2 * θ₀)) ^ s := pow_nonneg (fejerReal_nonneg r _) s
  have h1le : (fejerReal r (Real.arccos x - θ₀)) ^ s ≤ 1 :=
    pow_le_one₀ (fejerReal_nonneg r _) (fejerReal_le_one hr _)
  have h2le : (fejerReal r (Real.arccos x + θ₀)) ^ s ≤ 1 :=
    pow_le_one₀ (fejerReal_nonneg r _) (fejerReal_le_one hr _)
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]
    linarith

/-- Off-peak decay of `jacksonPoly r s θ₀`: for `θ, θ₀ ∈ [0, π]` with `θ ≠ θ₀`,
`jacksonPoly r s θ₀ (cos θ) ≤ 2 / (r * sin (|θ - θ₀| / 2)) ^ (2 * s)`. -/
theorem eval_jacksonPoly_cos_le {r : ℕ} (hr : 1 ≤ r) (s : ℕ) {θ₀ θ : ℝ}
    (hθ₀ : θ₀ ∈ Icc (0 : ℝ) π) (hθ : θ ∈ Icc (0 : ℝ) π) (hne : θ ≠ θ₀) :
    (jacksonPoly r s θ₀).eval (Real.cos θ) ≤
      2 / ((r : ℝ) * Real.sin (|θ - θ₀| / 2)) ^ (2 * s) := by
  rw [eval_jacksonPoly_cos hr s θ₀ θ]
  let a : ℝ := |θ - θ₀| / 2
  let b : ℝ := (θ + θ₀) / 2
  have ha_pos : 0 < a := by
    have : 0 < |θ - θ₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    dsimp only [a]; linarith
  have ha_le : a ≤ π / 2 := by
    have : |θ - θ₀| ≤ π := abs_le.mpr ⟨by linarith [hθ.1, hθ₀.2], by linarith [hθ.2, hθ₀.1]⟩
    dsimp only [a]; linarith
  have ha_le_b : a ≤ b := by
    have h1 : θ - θ₀ ≤ θ + θ₀ := by linarith [hθ₀.1]
    have h2 : -(θ - θ₀) ≤ θ + θ₀ := by linarith [hθ.1]
    have : |θ - θ₀| ≤ θ + θ₀ := abs_le.mpr ⟨by linarith, h1⟩
    dsimp only [a, b]; linarith
  have hb_le : b ≤ π - a := by
    have h1 : θ - θ₀ ≤ 2 * π - (θ + θ₀) := by linarith [hθ.2]
    have h2 : -(θ - θ₀) ≤ 2 * π - (θ + θ₀) := by linarith [hθ₀.2]
    have : |θ - θ₀| ≤ 2 * π - (θ + θ₀) := abs_le.mpr ⟨by linarith, h1⟩
    dsimp only [a, b]; linarith
  have hsin_a_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha_pos (by linarith [pi_pos])
  have hsin_a_le_b : Real.sin a ≤ Real.sin b := by
    rcases le_or_gt b (π / 2) with hb | hb
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hb ha_le_b
    · rw [← Real.sin_pi_sub b]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hsin_diff_eq : |Real.sin ((θ - θ₀) / 2)| = Real.sin a := by
    rcases le_or_gt θ₀ θ with hle | hgt
    · have ha_eq : a = (θ - θ₀) / 2 := by simp [a, abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [← ha_eq, abs_of_pos hsin_a_pos]
    · have ha_eq : a = -((θ - θ₀) / 2) := by
        simp only [a, abs_of_neg (sub_neg.mpr hgt)]; ring
      rw [← abs_neg, ← Real.sin_neg, ← ha_eq, abs_of_pos hsin_a_pos]
  have hsin_diff_ne : Real.sin ((θ - θ₀) / 2) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hsin_diff_eq
    linarith
  have hsin_sum_ne : Real.sin b ≠ 0 := by linarith
  have hfejer_diff : fejerReal r (θ - θ₀) ≤ 1 / ((r : ℝ) * Real.sin a) ^ 2 := by
    refine (fejerReal_le_inv_sin_sq hr hsin_diff_ne).trans_eq ?_
    rw [mul_pow, ← sq_abs (Real.sin ((θ - θ₀) / 2)), hsin_diff_eq, ← mul_pow]
  have hfejer_sum : fejerReal r (θ + θ₀) ≤ 1 / ((r : ℝ) * Real.sin a) ^ 2 := by
    refine (fejerReal_le_inv_sin_sq hr hsin_sum_ne).trans ?_
    refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    exact mul_le_mul_of_nonneg_left hsin_a_le_b (Nat.cast_nonneg r)
  have hpow_diff : (fejerReal r (θ - θ₀)) ^ s ≤ 1 / ((r : ℝ) * Real.sin a) ^ (2 * s) := by
    calc (fejerReal r (θ - θ₀)) ^ s
        ≤ (1 / ((r : ℝ) * Real.sin a) ^ 2) ^ s :=
            pow_le_pow_left₀ (fejerReal_nonneg r _) hfejer_diff s
      _ = 1 / ((r : ℝ) * Real.sin a) ^ (2 * s) := by rw [div_pow, one_pow, ← pow_mul]
  have hpow_sum : (fejerReal r (θ + θ₀)) ^ s ≤ 1 / ((r : ℝ) * Real.sin a) ^ (2 * s) := by
    calc (fejerReal r (θ + θ₀)) ^ s
        ≤ (1 / ((r : ℝ) * Real.sin a) ^ 2) ^ s :=
            pow_le_pow_left₀ (fejerReal_nonneg r _) hfejer_sum s
      _ = 1 / ((r : ℝ) * Real.sin a) ^ (2 * s) := by rw [div_pow, one_pow, ← pow_mul]
  have hden : 1 ≤ 1 + (fejerReal r (2 * θ₀)) ^ s := by
    have : 0 ≤ (fejerReal r (2 * θ₀)) ^ s := pow_nonneg (fejerReal_nonneg r _) s
    linarith
  have hnum_nn : 0 ≤ (fejerReal r (θ - θ₀)) ^ s + (fejerReal r (θ + θ₀)) ^ s :=
    add_nonneg (pow_nonneg (fejerReal_nonneg _ _) _) (pow_nonneg (fejerReal_nonneg _ _) _)
  calc ((fejerReal r (θ - θ₀)) ^ s + (fejerReal r (θ + θ₀)) ^ s) /
          (1 + (fejerReal r (2 * θ₀)) ^ s)
      ≤ ((fejerReal r (θ - θ₀)) ^ s + (fejerReal r (θ + θ₀)) ^ s) / 1 :=
          div_le_div_of_nonneg_left hnum_nn zero_lt_one hden
    _ = (fejerReal r (θ - θ₀)) ^ s + (fejerReal r (θ + θ₀)) ^ s := div_one _
    _ ≤ 1 / ((r : ℝ) * Real.sin a) ^ (2 * s) + 1 / ((r : ℝ) * Real.sin a) ^ (2 * s) :=
          add_le_add hpow_diff hpow_sum
    _ = 2 / ((r : ℝ) * Real.sin a) ^ (2 * s) := by ring

end FejerJackson

section CosineAndBernstein

/-- For `n ≥ 1` and `x ∈ [0, n]`, `sin (arccos (1 - 2 x / n) / 2) = √(x / n)`. -/
theorem sin_arccos_half_eq_sqrt {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) n) :
    Real.sin (Real.arccos (1 - 2 * x / n) / 2) = √(x / n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have harg : 1 - 2 * x / n ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have h2 : 2 * x / n ≤ 2 := (div_le_iff₀ hnR).mpr (by linarith [hx.2])
      linarith
    · rw [sub_le_self_iff]; exact div_nonneg (by linarith [hx.1]) hnR.le
  set θ := Real.arccos (1 - 2 * x / n)
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ π := Real.arccos_le_pi _
  have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsq : Real.sin (θ / 2) ^ 2 = x / n := by
    have hcos := Real.cos_two_mul' (θ / 2)
    have h2 : 2 * (θ / 2) = θ := by ring
    rw [h2, Real.cos_arccos harg.1 harg.2, mul_div_assoc] at hcos
    have hpyth := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  rw [← Real.sqrt_sq hsin_nn, hsq]

/-- Exact angle-to-square-root lower bound: for `n ≥ 1` and `x, y ∈ [0, n]`,
`|√x - √y| / √n ≤ sin (|arccos (1 - 2 x / n) - arccos (1 - 2 y / n)| / 2)`. -/
theorem abs_sqrt_sub_sqrt_div_le_sin {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) n) (hy : y ∈ Icc (0 : ℝ) n) :
    |√x - √y| / √n ≤
      Real.sin (|Real.arccos (1 - 2 * x / n) - Real.arccos (1 - 2 * y / n)| / 2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set θx := Real.arccos (1 - 2 * x / n)
  set θy := Real.arccos (1 - 2 * y / n)
  have hdiff : |√x - √y| / √n = |Real.sin (θx / 2) - Real.sin (θy / 2)| := by
    rw [sin_arccos_half_eq_sqrt hn hx, sin_arccos_half_eq_sqrt hn hy,
      Real.sqrt_div hx.1, Real.sqrt_div hy.1, ← sub_div, abs_div,
      abs_of_pos (Real.sqrt_pos.mpr hnR)]
  rw [hdiff]
  have haux (u v : ℝ) (hu0 : 0 ≤ u) (huv : u ≤ v) (hvπ : v ≤ π / 2) :
      Real.sin v - Real.sin u ≤ Real.sin (v - u) := by
    rw [Real.sin_sub_sin]
    have h2 : Real.sin (v - u) = 2 * Real.sin ((v - u) / 2) * Real.cos ((v - u) / 2) := by
      simpa [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] using Real.sin_two_mul ((v - u) / 2)
    rw [h2]
    have hsin_nn : 0 ≤ Real.sin ((v - u) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcos_le : Real.cos ((v + u) / 2) ≤ Real.cos ((v - u) / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    nlinarith
  have hx0 : 0 ≤ θx / 2 := by linarith [Real.arccos_nonneg (1 - 2 * x / n)]
  have hxπ : θx / 2 ≤ π / 2 := by linarith [Real.arccos_le_pi (1 - 2 * x / n)]
  have hy0 : 0 ≤ θy / 2 := by linarith [Real.arccos_nonneg (1 - 2 * y / n)]
  have hyπ : θy / 2 ≤ π / 2 := by linarith [Real.arccos_le_pi (1 - 2 * y / n)]
  rcases le_or_gt θx θy with hle | hgt
  · have hsin_le : Real.sin (θx / 2) ≤ Real.sin (θy / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hyπ (by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hsin_le), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, sub_div]
    exact haux (θx / 2) (θy / 2) hx0 (by linarith) hyπ
  · have hsin_le : Real.sin (θy / 2) ≤ Real.sin (θx / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hxπ (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hsin_le), abs_of_pos (sub_pos.mpr hgt), sub_div]
    exact haux (θy / 2) (θx / 2) hy0 (by linarith) hxπ

/-- Bernstein's inequality rescaled to `[0, n]`: if `P : ℝ[X]` has degree at most `D` and
`|P.eval y| ≤ M` on `[0, n]` (`n ≥ 1`), then `√(x * (n - x)) * |(derivative P).eval x| ≤ D * M`
for all `x ∈ [0, n]`. -/
theorem sqrt_mul_abs_eval_derivative_le_on_Icc {n D : ℕ} (hn : 1 ≤ n) {P : ℝ[X]}
    (hP : P.natDegree ≤ D) {M : ℝ} (hM : ∀ y ∈ Set.Icc (0 : ℝ) n, |P.eval y| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) n) :
    √(x * ((n : ℝ) - x)) * |(derivative P).eval x| ≤ (D : ℝ) * M := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let L : ℝ[X] := C ((n : ℝ) / 2) - C ((n : ℝ) / 2) * X
  have hL_eval (t : ℝ) : L.eval t = (n : ℝ) / 2 * (1 - t) := by
    simp only [L, eval_sub, eval_C, eval_mul, eval_X]; ring
  have hL_deg : L.natDegree ≤ 1 :=
    natDegree_sub_le_of_le ((natDegree_C _).le.trans zero_le_one)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le)
  have hdeg : (P.comp L).natDegree ≤ D := by
    refine natDegree_comp_le.trans ?_
    nlinarith
  have hbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(P.comp L).eval t| ≤ M := by
    intro t ht
    rw [eval_comp, hL_eval]
    exact hM _ ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  set t : ℝ := 1 - 2 * x / n
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have h2x : 2 * x / (n : ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr (by linarith [hx.2])
      linarith
    · rw [sub_le_self_iff]; exact div_nonneg (by linarith [hx.1]) hnR.le
  have hLt : L.eval t = x := by rw [hL_eval]; simp only [t]; field_simp; ring
  have hL' : (derivative L).eval t = -((n : ℝ) / 2) := by simp [L]
  have hbern := Polynomial.sqrt_mul_abs_eval_derivative_le hdeg hbound ht
  rw [derivative_comp, eval_mul, eval_comp, hLt, hL', abs_mul, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / 2)] at hbern
  have h1mt : 1 - t ^ 2 = 4 * (x * ((n : ℝ) - x)) / (n : ℝ) ^ 2 := by
    simp only [t]; field_simp; ring
  have hsqrt : √(1 - t ^ 2) = 2 * √(x * ((n : ℝ) - x)) / (n : ℝ) := by
    rw [h1mt, Real.sqrt_div (by nlinarith [hx.1, hx.2]), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq hnR.le]
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
  rw [hsqrt] at hbern
  have heq : 2 * √(x * ((n : ℝ) - x)) / (n : ℝ) * (((n : ℝ) / 2) * |(derivative P).eval x|) =
      √(x * ((n : ℝ) - x)) * |(derivative P).eval x| := by
    field_simp
  linarith

end CosineAndBernstein

end CslibFrontier.Foundations.Analysis
