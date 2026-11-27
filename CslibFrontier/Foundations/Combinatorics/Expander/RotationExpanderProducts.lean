/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Hom
public import CslibFrontier.Foundations.Combinatorics.Expander.Zigzag
public import Mathlib.Analysis.Real.Sqrt

import CslibFrontier.Foundations.Combinatorics.Expander.Loops
import CslibFrontier.Foundations.Combinatorics.Expander.Tensor
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp Zig-Zag Spectral Bound and Derandomized Graph Squaring

This module develops two foundational spectral graph product theorems on regular multigraphs
represented by rotation maps (`Cslib.RotationMap`), proved under standard Lean axioms:

1. **Reingold–Vadhan–Wigderson Sharp Zig-Zag Spectral Bound**: for a `D`-regular multigraph `G`
   on `V` and an `E`-regular multigraph `H` on `D`, the spectral expansion of `G.zigzag H` is at
   most `((1 - α²) λ + √((1 - α²)² λ² + 4 α²)) / 2`, where `λ = G.spectralExpansion` and
   `α = H.spectralExpansion`, yielding the spectral-gap lower bound
   `(1 - α²) (1 - λ) / 2 ≤ 1 - (G.zigzag H).spectralExpansion`.
2. **Rozenman–Vadhan Derandomized Graph Squaring**: the derandomized square
   `derandomizedSquare G H` is a `(D × E)`-regular multigraph on `V` whose edges select a first
   step in `G` and then a neighbor in `H` of the return label for the second step in `G`, with
   spectral expansion at most `1 - (1 - λ²) (1 - α) ≤ λ² + α`.

## Main definitions

* `CslibFrontier.RotationMap.zigzagBound`: the Reingold–Vadhan–Wigderson sharp zig-zag eigenvalue
  function `((1 - α²) λ + √((1 - α²)² λ² + 4 α²)) / 2`.
* `CslibFrontier.RotationMap.derandomizedSquareRot`: functional rotation step for derandomized graph
  squaring.
* `CslibFrontier.RotationMap.derandomizedSquare`: the Rozenman–Vadhan derandomized square of a
  `D`-regular rotation map `G` on `V` by an `E`-regular rotation map `H` on `D`.
* `CslibFrontier.RotationMap.Hom.derandomizedSquare`: functoriality of derandomized squaring along
  rotation-map homomorphisms.
* `CslibFrontier.RotationMap.derandomizedSquareBound`: the Rozenman–Vadhan spectral bound
  `1 - (1 - λ²) (1 - α)`.

## Main results

* `CslibFrontier.RotationMap.spectralExpansion_zigzag_le_zigzagBound`: sharp
  Reingold–Vadhan–Wigderson bound
  `(G.zigzag H).spectralExpansion ≤ zigzagBound G.spectralExpansion H.spectralExpansion`.
* `CslibFrontier.RotationMap.zigzagBound_le_one_sub`: algebraic bound
  `zigzagBound lam alpha ≤ 1 - (1 - alpha ^ 2) * (1 - lam) / 2` for `|lam| ≤ 1`.
* `CslibFrontier.RotationMap.le_one_sub_spectralExpansion_zigzag`: spectral-gap corollary
  `(1 - H.spectralExpansion ^ 2) * (1 - G.spectralExpansion) / 2 ≤
    1 - (G.zigzag H).spectralExpansion`.
* `CslibFrontier.RotationMap.walk_derandomizedSquare`: operator identity for the walk on
  `derandomizedSquare G H`.
* `CslibFrontier.RotationMap.spectralExpansion_derandomizedSquare_le`: Rozenman–Vadhan spectral
  theorem `(derandomizedSquare G H).spectralExpansion ≤
    derandomizedSquareBound G.spectralExpansion H.spectralExpansion`.
* `CslibFrontier.RotationMap.spectralExpansion_derandomizedSquare_le_add`: simplified bound
  `(derandomizedSquare G H).spectralExpansion ≤ G.spectralExpansion ^ 2 + H.spectralExpansion`.
-/

public section

namespace CslibFrontier.RotationMap

open Finset
open Fintype (expect_comp_fst expect_add_sq_of_expect_fiber_eq_zero
  exists_eq_add_expect_fiber_eq_zero)
open scoped BigOperators

/-! ### 1. Sharp Reingold–Vadhan–Wigderson Zig-Zag Bound -/

/-- The sharp Reingold–Vadhan–Wigderson zig-zag eigenvalue bound
`((1 - α²) λ + √((1 - α²)² λ² + 4 α²)) / 2`. -/
@[expose]
noncomputable def zigzagBound (lam alpha : ℝ) : ℝ :=
  ((1 - alpha ^ 2) * lam + √((1 - alpha ^ 2) ^ 2 * lam ^ 2 + 4 * alpha ^ 2)) / 2

/-- `zigzagBound lam alpha` is always nonnegative. -/
theorem zigzagBound_nonneg (lam alpha : ℝ) : 0 ≤ zigzagBound lam alpha := by
  unfold zigzagBound
  have hsq : ((1 - alpha ^ 2) * lam) ^ 2 ≤ (1 - alpha ^ 2) ^ 2 * lam ^ 2 + 4 * alpha ^ 2 := by
    nlinarith [sq_nonneg alpha]
  have habs : |(1 - alpha ^ 2) * lam| ≤ √((1 - alpha ^ 2) ^ 2 * lam ^ 2 + 4 * alpha ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  linarith [neg_abs_le ((1 - alpha ^ 2) * lam)]

/-- `zigzagBound lam alpha` satisfies the defining quadratic identity
`μ² = (1 - α²) λ μ + α²`. -/
theorem zigzagBound_sq_eq (lam alpha : ℝ) :
    zigzagBound lam alpha ^ 2 = (1 - alpha ^ 2) * lam * zigzagBound lam alpha + alpha ^ 2 := by
  unfold zigzagBound
  set u := (1 - alpha ^ 2) * lam
  set d := (1 - alpha ^ 2) ^ 2 * lam ^ 2 + 4 * alpha ^ 2
  have hd : 0 ≤ d := by positivity
  have hsq : √d ^ 2 = d := Real.sq_sqrt hd
  have hu : (1 - alpha ^ 2) ^ 2 * lam ^ 2 = u ^ 2 := by ring
  nlinarith [hsq, hu]

/-- For `0 ≤ lam` and `0 ≤ alpha ≤ 1`, `alpha ≤ zigzagBound lam alpha`. -/
theorem le_zigzagBound_of_nonneg {lam alpha : ℝ} (hlam : 0 ≤ lam) (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1) : alpha ≤ zigzagBound lam alpha := by
  unfold zigzagBound
  have hu : 0 ≤ (1 - alpha ^ 2) * lam := mul_nonneg (by nlinarith) hlam
  have hrad : 2 * alpha ≤ √((1 - alpha ^ 2) ^ 2 * lam ^ 2 + 4 * alpha ^ 2) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * alpha)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- For `0 ≤ lam` and `0 ≤ alpha ≤ 1`, `alpha ^ 2 ≤ zigzagBound lam alpha`. -/
theorem sq_le_zigzagBound {lam alpha : ℝ} (hlam : 0 ≤ lam) (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1) : alpha ^ 2 ≤ zigzagBound lam alpha :=
  (by nlinarith : alpha ^ 2 ≤ alpha).trans (le_zigzagBound_of_nonneg hlam halpha0 halpha1)

/-- For `0 ≤ lam ≤ 1`, `lam ≤ zigzagBound lam alpha`. -/
theorem left_le_zigzagBound {lam alpha : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam ≤ zigzagBound lam alpha := by
  set mu := zigzagBound lam alpha
  have hmu0 : 0 ≤ mu := zigzagBound_nonneg lam alpha
  have hmu_sq : mu ^ 2 = (1 - alpha ^ 2) * lam * mu + alpha ^ 2 := zigzagBound_sq_eq lam alpha
  have hquad : (mu - lam) * (mu + alpha ^ 2 * lam) = alpha ^ 2 * (1 - lam ^ 2) := by
    linear_combination hmu_sq
  have hrhs : 0 ≤ alpha ^ 2 * (1 - lam ^ 2) := mul_nonneg (sq_nonneg alpha) (by nlinarith)
  rcases (by positivity : 0 ≤ mu + alpha ^ 2 * lam).eq_or_lt with h0 | hpos
  · have hmu_zero : mu = 0 := by nlinarith [sq_nonneg alpha]
    have halpha_zero : alpha = 0 := by
      rw [hmu_zero] at hmu_sq
      nlinarith [sq_nonneg alpha]
    have hzig : mu = lam := by
      dsimp only [mu]
      rw [halpha_zero]
      simp [zigzagBound, Real.sqrt_sq hlam0]
    linarith
  · exact sub_nonneg.mp (nonneg_of_mul_nonneg_left (hrhs.trans_eq hquad.symm) hpos)

/-- For `|lam| ≤ 1`, `zigzagBound lam alpha ≤ 1 - (1 - alpha ^ 2) * (1 - lam) / 2`. -/
theorem zigzagBound_le_one_sub {lam alpha : ℝ} (hlam : |lam| ≤ 1) :
    zigzagBound lam alpha ≤ 1 - (1 - alpha ^ 2) * (1 - lam) / 2 := by
  unfold zigzagBound
  have hlam2 : lam ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg lam]
  have hrad : √((1 - alpha ^ 2) ^ 2 * lam ^ 2 + 4 * alpha ^ 2) ≤ 1 + alpha ^ 2 := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 + alpha ^ 2)]
    refine Real.sqrt_le_sqrt ?_
    have h1 : (1 - alpha ^ 2) ^ 2 * lam ^ 2 ≤ (1 - alpha ^ 2) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hlam2 (sq_nonneg _)
    linarith
  linarith

/-- For `|lam| ≤ 1` and `|alpha| ≤ 1`, `zigzagBound lam alpha ≤ 1`. -/
theorem zigzagBound_le_one {lam alpha : ℝ} (hlam : |lam| ≤ 1) (halpha : |alpha| ≤ 1) :
    zigzagBound lam alpha ≤ 1 := by
  have h1 := zigzagBound_le_one_sub (alpha := alpha) hlam
  have halpha2 : alpha ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg alpha]
  have hlam1 : lam ≤ 1 := (le_abs_self lam).trans hlam
  linarith [mul_nonneg (by linarith : 0 ≤ 1 - alpha ^ 2) (by linarith : 0 ≤ 1 - lam)]

/-- `zigzagBound` is monotone in its first argument when `|alpha| ≤ 1`. -/
theorem zigzagBound_mono_left {lam₁ lam₂ alpha : ℝ} (hlam0 : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₂)
    (halpha : |alpha| ≤ 1) : zigzagBound lam₁ alpha ≤ zigzagBound lam₂ alpha := by
  unfold zigzagBound
  have ha2 : 0 ≤ 1 - alpha ^ 2 := by
    have : alpha ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg alpha]
    linarith
  have hmul : (1 - alpha ^ 2) * lam₁ ≤ (1 - alpha ^ 2) * lam₂ :=
    mul_le_mul_of_nonneg_left hlam ha2
  have hrad :
      √((1 - alpha ^ 2) ^ 2 * lam₁ ^ 2 + 4 * alpha ^ 2) ≤
        √((1 - alpha ^ 2) ^ 2 * lam₂ ^ 2 + 4 * alpha ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    have hsq : lam₁ ^ 2 ≤ lam₂ ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
    nlinarith [sq_nonneg (1 - alpha ^ 2)]
  linarith

/-- `zigzagBound` is strictly increasing in its first argument when `|alpha| < 1`. -/
theorem zigzagBound_strictMono_left {lam₁ lam₂ alpha : ℝ} (hlam0 : 0 ≤ lam₁) (hlam : lam₁ < lam₂)
    (halpha : |alpha| < 1) : zigzagBound lam₁ alpha < zigzagBound lam₂ alpha := by
  unfold zigzagBound
  have ha2 : 0 < 1 - alpha ^ 2 := by
    have : alpha ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg alpha]
    linarith
  have hmul : (1 - alpha ^ 2) * lam₁ < (1 - alpha ^ 2) * lam₂ :=
    mul_lt_mul_of_pos_left hlam ha2
  have hrad :
      √((1 - alpha ^ 2) ^ 2 * lam₁ ^ 2 + 4 * alpha ^ 2) ≤
        √((1 - alpha ^ 2) ^ 2 * lam₂ ^ 2 + 4 * alpha ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    have hsq : lam₁ ^ 2 ≤ lam₂ ^ 2 := pow_le_pow_left₀ hlam0 hlam.le 2
    nlinarith [sq_nonneg (1 - alpha ^ 2)]
  linarith

/-- `zigzagBound` is monotone in its second argument on `[0, 1]` when `0 ≤ lam ≤ 1`. -/
theorem zigzagBound_mono_right {lam alpha₁ alpha₂ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (ha0 : 0 ≤ alpha₁) (ha : alpha₁ ≤ alpha₂) (ha1 : alpha₂ ≤ 1) :
    zigzagBound lam alpha₁ ≤ zigzagBound lam alpha₂ := by
  set mu₁ := zigzagBound lam alpha₁
  set mu₂ := zigzagBound lam alpha₂
  have hq₁ : mu₁ ^ 2 = (1 - alpha₁ ^ 2) * lam * mu₁ + alpha₁ ^ 2 := zigzagBound_sq_eq lam alpha₁
  have hq₂ : mu₂ ^ 2 = (1 - alpha₂ ^ 2) * lam * mu₂ + alpha₂ ^ 2 := zigzagBound_sq_eq lam alpha₂
  have hmu₁ : lam ≤ mu₁ := left_le_zigzagBound hlam0 hlam1
  have hmu₂0 : 0 ≤ mu₂ := zigzagBound_nonneg lam alpha₂
  have hdiff :
      (mu₂ - mu₁) * (mu₂ + mu₁ - (1 - alpha₂ ^ 2) * lam) =
        (alpha₂ ^ 2 - alpha₁ ^ 2) * (1 - lam * mu₁) := by
    linear_combination hq₂ - hq₁
  have hmu₁_le : mu₁ ≤ 1 :=
    zigzagBound_le_one (by rw [abs_of_nonneg hlam0]; exact hlam1)
      (by rw [abs_of_nonneg ha0]; exact ha.trans ha1)
  have hrhs : 0 ≤ (alpha₂ ^ 2 - alpha₁ ^ 2) * (1 - lam * mu₁) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  have hpos_factor : 0 ≤ mu₂ + mu₁ - (1 - alpha₂ ^ 2) * lam := by
    have : (1 - alpha₂ ^ 2) * lam ≤ lam := by nlinarith [sq_nonneg alpha₂]
    linarith
  rcases hpos_factor.eq_or_lt with h0 | hpos
  · have hmu₂_zero : mu₂ = 0 := by
      have : (1 - alpha₂ ^ 2) * lam ≤ lam := by nlinarith [sq_nonneg alpha₂]
      linarith
    have ha₂_zero : alpha₂ = 0 := by
      rw [hmu₂_zero] at hq₂
      nlinarith [sq_nonneg alpha₂]
    have ha₁_zero : alpha₁ = 0 := by linarith
    dsimp only [mu₁, mu₂]
    rw [ha₁_zero, ha₂_zero]
  · exact sub_nonneg.mp (nonneg_of_mul_nonneg_left (hrhs.trans_eq hdiff.symm) hpos)

private theorem reflection_quadratic_bound {lam alpha p q A₂ B₂ C₂ : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hp : |p| ≤ lam) (hA₂ : 0 ≤ A₂) (hB₂ : 0 ≤ B₂) (hC₂ : C₂ ≤ alpha ^ 2 * B₂)
    (hq : q ^ 2 * (1 - p ^ 2) * A₂ ≤ C₂) :
    p * A₂ + 2 * q * (1 - p ^ 2) * A₂ - (1 + p) * q ^ 2 * (1 - p ^ 2) * A₂ + C₂ ≤
      zigzagBound lam alpha * (A₂ + B₂) := by
  set mu := zigzagBound lam alpha
  have hmu0 : 0 ≤ mu := zigzagBound_nonneg lam alpha
  have hmu_sq := zigzagBound_sq_eq lam alpha
  have hmu_ge_lam : lam ≤ mu := left_le_zigzagBound hlam0 hlam1
  have hmu_ge_a2 : alpha ^ 2 ≤ mu := sq_le_zigzagBound hlam0 halpha0 halpha1
  have hp_le : p ≤ lam := (le_abs_self p).trans hp
  have hp_ge : -lam ≤ p := neg_le_of_abs_le hp
  have hp2 : 0 ≤ 1 - p ^ 2 := by
    have : p ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg p]
    linarith
  rcases halpha0.eq_or_lt with rfl | halpha_pos
  · have hC0 : C₂ ≤ 0 := by simpa using hC₂
    have hy0 : q ^ 2 * (1 - p ^ 2) * A₂ ≤ 0 := hq.trans hC0
    have hy_eq : q ^ 2 * (1 - p ^ 2) * A₂ = 0 := le_antisymm hy0 (by positivity)
    have hterm0 : q * (1 - p ^ 2) * A₂ = 0 := by
      have : (q * (1 - p ^ 2) * A₂) ^ 2 = (q ^ 2 * (1 - p ^ 2) * A₂) * ((1 - p ^ 2) * A₂) := by
        ring
      rw [hy_eq, zero_mul] at this
      exact sq_eq_zero_iff.mp this
    have hmuB : 0 ≤ mu * B₂ := mul_nonneg hmu0 hB₂
    have hpA : p * A₂ ≤ mu * A₂ := mul_le_mul_of_nonneg_right (hp_le.trans hmu_ge_lam) hA₂
    nlinarith
  · -- Multiply the difference by `alpha ^ 2 > 0`.
    have ha2_pos : 0 < alpha ^ 2 := sq_pos_of_pos halpha_pos
    suffices hmul :
        0 ≤ alpha ^ 2 * (mu * (A₂ + B₂) -
          (p * A₂ + 2 * q * (1 - p ^ 2) * A₂ - (1 + p) * q ^ 2 * (1 - p ^ 2) * A₂ + C₂)) by
      nlinarith
    have hB_lower :
        (mu - alpha ^ 2) * (q ^ 2 * (1 - p ^ 2) * A₂) ≤ (mu - alpha ^ 2) * (alpha ^ 2 * B₂) :=
      mul_le_mul_of_nonneg_left (hq.trans hC₂) (by linarith)
    have hC_upper : alpha ^ 2 * C₂ ≤ alpha ^ 2 * (alpha ^ 2 * B₂) :=
      mul_le_mul_of_nonneg_left hC₂ ha2_pos.le
    set s := 1 - p ^ 2
    set Q := (mu + p * alpha ^ 2) * s * q ^ 2 - 2 * alpha ^ 2 * s * q + alpha ^ 2 * (mu - p)
    have hstep :
        A₂ * Q ≤ alpha ^ 2 * (mu * (A₂ + B₂) -
          (p * A₂ + 2 * q * s * A₂ - (1 + p) * q ^ 2 * s * A₂ + C₂)) := by
      nlinarith
    refine le_trans (mul_nonneg hA₂ ?_) hstep
    rcases hp2.eq_or_lt with hs0 | hs_pos
    · have hs_eq : s = 0 := hs0.symm
      simp only [Q, hs_eq, mul_zero, zero_mul, sub_zero, zero_add]
      exact mul_nonneg ha2_pos.le (by linarith)
    · have hmpa_pos : 0 < mu + p * alpha ^ 2 := by
        have hp1_ne : 1 + p ≠ 0 := fun h ↦ hs_pos.ne' (by dsimp only [s]; nlinarith)
        have hp1_pos : 0 < 1 + p := lt_of_le_of_ne (by linarith) hp1_ne.symm
        have h2 : 0 < (1 + p) * alpha ^ 2 := mul_pos hp1_pos ha2_pos
        linarith
      have hfac : 0 < (mu + p * alpha ^ 2) * s := mul_pos hmpa_pos hs_pos
      suffices hQ : 0 ≤ (mu + p * alpha ^ 2) * s * Q by
        exact nonneg_of_mul_nonneg_right hQ hfac
      have hdisc : 0 ≤ (mu - p) * (mu + p * alpha ^ 2) - alpha ^ 2 * s := by
        have hid :
            (mu - p) * (mu + p * alpha ^ 2) - alpha ^ 2 * s =
              (lam - p) * (1 - alpha ^ 2) * mu := by
          simp only [s]
          linear_combination hmu_sq
        rw [hid]
        exact mul_nonneg (mul_nonneg (by linarith) (by nlinarith)) hmu0
      have hpol :
          (mu + p * alpha ^ 2) * s * Q =
            ((mu + p * alpha ^ 2) * s * q - alpha ^ 2 * s) ^ 2 +
              alpha ^ 2 * s * ((mu - p) * (mu + p * alpha ^ 2) - alpha ^ 2 * s) := by
        simp only [Q]
        ring
      rw [hpol]
      positivity

/-- Signed reflection bound on `V × D`: for an involutive rotation `rot`, signed factor `ε = ±1`,
fiber-constant `f₁ : V → ℝ` with `|𝔼 p, f₁ p.1 * (ε * f₁ (rot p).1)| ≤ lam * 𝔼 v, f₁ v ^ 2`,
and fiber-mean-zero `g₂ : V × D → ℝ` with `𝔼 p, g₂ p ^ 2 ≤ alpha ^ 2 * B₂`, we have
`𝔼 p, (f₁ p.1 + g₂ p) * (ε * (f₁ (rot p).1 + g₂ (rot p))) ≤
  zigzagBound lam alpha * (𝔼 v, f₁ v ^ 2 + B₂)`. -/
private theorem expect_signed_rot_le_zigzagBound {V D : Type*} [Fintype V] [Fintype D]
    [Nonempty D] (G : Cslib.RotationMap V D) {ε lam alpha B₂ : ℝ} (hε : ε ^ 2 = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hB₂ : 0 ≤ B₂) (f₁ : V → ℝ) (g₂ : V × D → ℝ) (hg₂ : ∀ v, 𝔼 d, g₂ (v, d) = 0)
    (hf₁ : |𝔼 q : V × D, f₁ q.1 * (ε * f₁ (G.rot q).1)| ≤ lam * 𝔼 v, f₁ v ^ 2)
    (hC₂ : 𝔼 q, g₂ q ^ 2 ≤ alpha ^ 2 * B₂) :
    𝔼 q : V × D, (f₁ q.1 + g₂ q) * (ε * (f₁ (G.rot q).1 + g₂ (G.rot q))) ≤
      zigzagBound lam alpha * (𝔼 v, f₁ v ^ 2 + B₂) := by
  let S : (V × D → ℝ) → (V × D → ℝ) := fun u q ↦ ε * u (G.rot q)
  have hS_invol (u : V × D → ℝ) (q : V × D) : S (S u) q = u q := by
    dsimp only [S]
    rw [G.rot_rot, ← mul_assoc, ← sq, hε, one_mul]
  have hS_symm (u v : V × D → ℝ) : 𝔼 q, u q * S v q = 𝔼 q, S u q * v q := by
    dsimp only [S]
    calc 𝔼 q, u q * (ε * v (G.rot q))
        = 𝔼 q, u (G.rot (G.rot q)) * (ε * v (G.rot q)) := by simp only [G.rot_rot]
      _ = 𝔼 q, u (G.rot q) * (ε * v q) :=
          G.expect_comp_rot fun q ↦ u (G.rot q) * (ε * v q)
      _ = 𝔼 q, (ε * u (G.rot q)) * v q := expect_congr rfl fun _ _ ↦ by ring
  have hS_norm (u : V × D → ℝ) : 𝔼 q, S u q ^ 2 = 𝔼 q, u q ^ 2 := by
    calc 𝔼 q, S u q ^ 2 = 𝔼 q, S u q * S u q := expect_congr rfl fun _ _ ↦ sq _
      _ = 𝔼 q, S (S u) q * u q := hS_symm (S u) u
      _ = 𝔼 q, u q ^ 2 := expect_congr rfl fun q _ ↦ by rw [hS_invol, sq]
  have hS_le (u : V × D → ℝ) : 𝔼 q, u q * S u q ≤ 𝔼 q, u q ^ 2 := by
    have h0 : 0 ≤ 𝔼 q, (u q - S u q) ^ 2 := expect_nonneg fun q _ ↦ sq_nonneg _
    have hexp : 𝔼 q, (u q - S u q) ^ 2 = 2 * 𝔼 q, u q ^ 2 - 2 * 𝔼 q, u q * S u q := by
      have h1 : ∀ q, (u q - S u q) ^ 2 = u q ^ 2 - 2 * (u q * S u q) + S u q ^ 2 :=
        fun _ ↦ by ring
      simp only [h1, expect_add_distrib, expect_sub_distrib, ← mul_expect, hS_norm]
      ring
    linarith
  let F : V × D → ℝ := fun q ↦ f₁ q.1
  have hFA : 𝔼 q, F q ^ 2 = 𝔼 v, f₁ v ^ 2 := expect_comp_fst fun v ↦ f₁ v ^ 2
  have horth_Fg : 𝔼 q, F q * g₂ q = 0 := by
    dsimp only [F]
    simp only [Fintype.expect_prod_type, ← mul_expect, hg₂, mul_zero, expect_const_zero]
  set A₂ := 𝔼 v, f₁ v ^ 2
  set C₂ := 𝔼 q, g₂ q ^ 2
  have hA₂ : 0 ≤ A₂ := expect_nonneg fun v _ ↦ sq_nonneg _
  have hC₂0 : 0 ≤ C₂ := expect_nonneg fun q _ ↦ sq_nonneg _
  rcases hA₂.eq_or_lt with hA0 | hA_pos
  · -- When `A₂ = 0`, `F` has zero norm, so `𝔼 (F + g₂) S(F + g₂) = 𝔼 g₂ (S g₂) ≤ C₂`.
    have hF_zero : 𝔼 q, F q ^ 2 = 0 := hFA.trans hA0.symm
    have hSF_zero : 𝔼 q, S F q ^ 2 = 0 := (hS_norm F).trans hF_zero
    have hCS₁ : 𝔼 q, F q * S F q = 0 := by
      have := expect_mul_sq_le_sq_mul_sq univ F (S F)
      rw [hF_zero, zero_mul] at this
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
    have hCS₂ : 𝔼 q, g₂ q * S F q = 0 := by
      have := expect_mul_sq_le_sq_mul_sq univ g₂ (S F)
      rw [hSF_zero, mul_zero] at this
      exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
    have hCS₃ : 𝔼 q, F q * S g₂ q = 0 := by
      rw [hS_symm]
      exact (expect_congr rfl fun _ _ ↦ mul_comm _ _).trans hCS₂
    have hexp :
        𝔼 q, (F q + g₂ q) * S (fun r ↦ F r + g₂ r) q = 𝔼 q, g₂ q * S g₂ q := by
      have hpt (q : V × D) :
          (F q + g₂ q) * S (fun r ↦ F r + g₂ r) q =
            F q * S F q + g₂ q * S F q + F q * S g₂ q + g₂ q * S g₂ q := by
        dsimp only [S]; ring
      simp only [hpt, expect_add_distrib, hCS₁, hCS₂, hCS₃, zero_add]
    change 𝔼 q, (F q + g₂ q) * S (fun r ↦ F r + g₂ r) q ≤ _
    rw [hexp, ← hA0, zero_add]
    have hmu_a2 : alpha ^ 2 ≤ zigzagBound lam alpha := sq_le_zigzagBound hlam0 halpha0 halpha1
    exact (hS_le g₂).trans (hC₂.trans (mul_le_mul_of_nonneg_right hmu_a2 hB₂))
  · -- When `A₂ > 0`, decompose along `F` and `w = S F - p F`.
    let p : ℝ := (𝔼 q, F q * S F q) / A₂
    have hp_mul : p * A₂ = 𝔼 q, F q * S F q := div_mul_cancel₀ _ hA_pos.ne'
    have hp_abs : |p| ≤ lam := by
      rw [abs_div, abs_of_pos hA_pos, div_le_iff₀ hA_pos]
      exact hf₁
    have hp_le_one : p ^ 2 ≤ 1 := by
      rw [← sq_abs]
      have : |p| ≤ 1 := hp_abs.trans hlam1
      nlinarith [abs_nonneg p]
    let w : V × D → ℝ := fun q ↦ S F q - p * F q
    have hFw : 𝔼 q, F q * w q = 0 := by
      have hpt (q : V × D) : F q * w q = F q * S F q - p * F q ^ 2 := by dsimp only [w]; ring
      simp only [hpt, expect_sub_distrib, ← mul_expect, hFA]
      linarith [hp_mul]
    have hw_sq : 𝔼 q, w q ^ 2 = (1 - p ^ 2) * A₂ := by
      have hpt (q : V × D) : w q ^ 2 = S F q ^ 2 - 2 * p * (F q * S F q) + p ^ 2 * F q ^ 2 := by
        dsimp only [w]; ring
      simp only [hpt, expect_add_distrib, expect_sub_distrib, ← mul_expect, hS_norm, hFA, ← hp_mul]
      ring
    have hSw (q : V × D) : S w q = (1 - p ^ 2) * F q - p * w q := by
      have h1 : S w q = S (S F) q - p * S F q := by dsimp only [S, w]; ring
      rw [h1, hS_invol]
      dsimp only [w]
      ring
    have hgw_eq : 𝔼 q, g₂ q * S F q = 𝔼 q, g₂ q * w q := by
      have hpt (q : V × D) : g₂ q * S F q = g₂ q * w q + p * (F q * g₂ q) := by
        dsimp only [w]; ring
      simp only [hpt, expect_add_distrib, ← mul_expect, horth_Fg, mul_zero, add_zero]
    have hexpand_base :
        𝔼 q, (F q + g₂ q) * S (fun r ↦ F r + g₂ r) q =
          p * A₂ + 2 * 𝔼 q, g₂ q * w q + 𝔼 q, g₂ q * S g₂ q := by
      have h1 : 𝔼 q, F q * S g₂ q = 𝔼 q, g₂ q * S F q := by
        rw [hS_symm]
        exact expect_congr rfl fun _ _ ↦ mul_comm _ _
      have hpt (q : V × D) :
          (F q + g₂ q) * S (fun r ↦ F r + g₂ r) q =
            F q * S F q + (g₂ q * S F q + F q * S g₂ q) + g₂ q * S g₂ q := by
        dsimp only [S]; ring
      simp only [hpt, expect_add_distrib, h1, ← hp_mul, hgw_eq]
      ring
    rcases (by linarith : 0 ≤ 1 - p ^ 2).eq_or_lt with hp1 | hp1_pos
    · have hw0 : 𝔼 q, w q ^ 2 = 0 := by rw [hw_sq, ← hp1, zero_mul]
      have hgw0 : 𝔼 q, g₂ q * w q = 0 := by
        have := expect_mul_sq_le_sq_mul_sq univ g₂ w
        rw [hw0, mul_zero] at this
        exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))
      change 𝔼 q, (F q + g₂ q) * S (fun r ↦ F r + g₂ r) q ≤ _
      rw [hexpand_base, hgw0]
      have := reflection_quadratic_bound hlam0 hlam1 halpha0 halpha1 hp_abs hA₂ hB₂ hC₂
        (q := 0) (by simpa using hC₂0)
      linarith [hS_le g₂]
    · have hw_pos : 0 < 𝔼 q, w q ^ 2 := by rw [hw_sq]; exact mul_pos hp1_pos hA_pos
      let q : ℝ := (𝔼 r, g₂ r * w r) / (𝔼 r, w r ^ 2)
      have hq_mul : q * ((1 - p ^ 2) * A₂) = 𝔼 r, g₂ r * w r := by
        rw [← hw_sq]; exact div_mul_cancel₀ _ hw_pos.ne'
      let z : V × D → ℝ := fun r ↦ g₂ r - q * w r
      have hwz : 𝔼 r, w r * z r = 0 := by
        have hpt (r : V × D) : w r * z r = g₂ r * w r - q * w r ^ 2 := by dsimp only [z]; ring
        simp only [hpt, expect_sub_distrib, ← mul_expect, hw_sq]
        linarith [hq_mul]
      have hFz : 𝔼 r, F r * z r = 0 := by
        have hpt (r : V × D) : F r * z r = F r * g₂ r - q * (F r * w r) := by
          dsimp only [z]; ring
        simp only [hpt, expect_sub_distrib, ← mul_expect, horth_Fg, hFw, mul_zero, sub_zero]
      have hSwz : 𝔼 r, S w r * z r = 0 := by
        have hpt (r : V × D) : S w r * z r = (1 - p ^ 2) * (F r * z r) - p * (w r * z r) := by
          rw [hSw]; ring
        simp only [hpt, expect_sub_distrib, ← mul_expect, hFz, hwz, mul_zero, sub_zero]
      have hzSw : 𝔼 r, z r * S w r = 0 := by
        calc 𝔼 r, z r * S w r = 𝔼 r, S w r * z r := expect_congr rfl fun _ _ ↦ mul_comm _ _
          _ = 0 := hSwz
      have hC_decomp : C₂ = q ^ 2 * (1 - p ^ 2) * A₂ + 𝔼 r, z r ^ 2 := by
        have hpt (r : V × D) : g₂ r ^ 2 = (q * w r + z r) ^ 2 := by dsimp only [z]; ring
        have hpt2 (r : V × D) : (q * w r + z r) ^ 2 = q ^ 2 * w r ^ 2 + 2 * q * (w r * z r) +
            z r ^ 2 := by ring
        calc C₂ = 𝔼 r, g₂ r ^ 2 := rfl
          _ = 𝔼 r, (q ^ 2 * w r ^ 2 + 2 * q * (w r * z r) + z r ^ 2) :=
              expect_congr rfl fun r _ ↦ (hpt r).trans (hpt2 r)
          _ = q ^ 2 * (1 - p ^ 2) * A₂ + 𝔼 r, z r ^ 2 := by
              simp only [expect_add_distrib, ← mul_expect, hw_sq, hwz]
              ring
      have hq_bound : q ^ 2 * (1 - p ^ 2) * A₂ ≤ C₂ := by
        rw [hC_decomp]
        linarith [expect_nonneg fun r (_ : r ∈ univ) ↦ sq_nonneg (z r)]
      have hgSg :
          𝔼 r, g₂ r * S g₂ r = -p * q ^ 2 * (1 - p ^ 2) * A₂ + 𝔼 r, z r * S z r := by
        have hSw_self : 𝔼 r, w r * S w r = -p * ((1 - p ^ 2) * A₂) := by
          have hpt (r : V × D) : w r * S w r = (1 - p ^ 2) * (F r * w r) - p * w r ^ 2 := by
            rw [hSw]; ring
          simp only [hpt, expect_sub_distrib, ← mul_expect, hFw, hw_sq, mul_zero, zero_sub]
          ring
        have hwSz : 𝔼 r, w r * S z r = 0 := by rw [hS_symm]; exact hSwz
        have hpt (r : V × D) :
            g₂ r * S g₂ r =
              q ^ 2 * (w r * S w r) + q * (w r * S z r) + q * (z r * S w r) + z r * S z r := by
          have hg_eq : ∀ t, g₂ t = q * w t + z t := fun t ↦ by dsimp only [z]; ring
          have hSg_eq : S g₂ r = q * S w r + S z r := by
            dsimp only [S]; rw [hg_eq (G.rot r)]; ring
          rw [hg_eq r, hSg_eq]; ring
        simp only [hpt, expect_add_distrib, ← mul_expect, hSw_self, hwSz, hzSw]
        ring
      change 𝔼 r, (F r + g₂ r) * S (fun t ↦ F t + g₂ t) r ≤ _
      rw [hexpand_base, ← hq_mul, hgSg]
      have hz_le : 𝔼 r, z r * S z r ≤ C₂ - q ^ 2 * (1 - p ^ 2) * A₂ :=
        (hS_le z).trans (by linarith [hC_decomp])
      have hquad := reflection_quadratic_bound hlam0 hlam1 halpha0 halpha1 hp_abs hA₂ hB₂ hC₂
        hq_bound
      linarith

/-- **Reingold–Vadhan–Wigderson Sharp Zig-Zag Theorem**: for any finite `D`-regular multigraph
`G` on `V` and finite `E`-regular multigraph `H` on `D`,
`(G.zigzag H).spectralExpansion ≤ zigzagBound G.spectralExpansion H.spectralExpansion`. -/
theorem spectralExpansion_zigzag_le_zigzagBound {V D E : Type*} [Fintype V] [Fintype D]
    [Fintype E] (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E) :
    (G.zigzag H).spectralExpansion ≤ zigzagBound G.spectralExpansion H.spectralExpansion := by
  set lam := G.spectralExpansion
  set alpha := H.spectralExpansion
  have hlam0 : 0 ≤ lam := G.spectralExpansion_nonneg
  have hlam1 : lam ≤ 1 := G.spectralExpansion_le_one
  have halpha0 : 0 ≤ alpha := H.spectralExpansion_nonneg
  have halpha1 : alpha ≤ 1 := H.spectralExpansion_le_one
  refine (G.zigzag H).spectralExpansion_le_of_abs_expect_mul_walk_le
    (zigzagBound_nonneg lam alpha) fun f hf ↦ ?_
  rcases isEmpty_or_nonempty E with hE | hE
  · have hzero : (G.zigzag H).walk f = 0 := funext fun p ↦ by simp [Cslib.RotationMap.walk_apply]
    rw [hzero]
    simp only [Pi.zero_apply, mul_zero, expect_const_zero, abs_zero]
    exact mul_nonneg (zigzagBound_nonneg lam alpha) (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  let Btilde := ((Cslib.RotationMap.loops V Unit).tensor H).walk
  let g₂ : V × D → ℝ := Btilde f₂
  have hg₂_fiber : ∀ v, 𝔼 d, g₂ (v, d) = 0 := H.expect_walk_loops_tensor_eq_zero hf₂
  have hg₂_sq : 𝔼 q, g₂ q ^ 2 ≤ alpha ^ 2 * 𝔼 q, f₂ q ^ 2 := H.expect_walk_loops_tensor_sq_le hf₂
  have hwalk_eq :
      𝔼 q, (f₁ q.1 + f₂ q) * (G.zigzag H).walk (fun r ↦ f₁ r.1 + f₂ r) q =
        𝔼 q, (f₁ q.1 + g₂ q) * (f₁ (G.rot q).1 + g₂ (G.rot q)) := by
    rw [G.walk_zigzag H, LinearMap.comp_apply, LinearMap.comp_apply,
      ((Cslib.RotationMap.loops V Unit).tensor H).expect_mul_walk_comm,
      H.walk_loops_tensor_add f₁ f₂]
    rfl
  have hf₁_walk : 𝔼 q : V × D, f₁ q.1 * f₁ (G.rot q).1 = 𝔼 v, f₁ v * G.walk f₁ v := by
    simp only [Fintype.expect_prod_type, Cslib.RotationMap.walk_apply, mul_expect]
    rfl
  have hf₁_abs : |𝔼 v, f₁ v * G.walk f₁ v| ≤ lam * 𝔼 v, f₁ v ^ 2 := G.abs_expect_mul_walk_le hf₁
  have hB₂ : 0 ≤ 𝔼 q, f₂ q ^ 2 := expect_nonneg fun q _ ↦ sq_nonneg _
  rw [hwalk_eq, hff, abs_le]
  constructor
  · have hneg := expect_signed_rot_le_zigzagBound G (ε := -1) (by norm_num)
      hlam0 hlam1 halpha0 halpha1 hB₂ f₁ g₂ hg₂_fiber
      (by
        have : 𝔼 q : V × D, f₁ q.1 * (-1 * f₁ (G.rot q).1) = -(𝔼 v, f₁ v * G.walk f₁ v) := by
          rw [← hf₁_walk, ← expect_neg_distrib]
          exact expect_congr rfl fun _ _ ↦ by ring
        rw [this, abs_neg]
        exact hf₁_abs) hg₂_sq
    have heq :
        𝔼 q : V × D, (f₁ q.1 + g₂ q) * (-1 * (f₁ (G.rot q).1 + g₂ (G.rot q))) =
          -(𝔼 q : V × D, (f₁ q.1 + g₂ q) * (f₁ (G.rot q).1 + g₂ (G.rot q))) := by
      rw [← expect_neg_distrib]
      exact expect_congr rfl fun _ _ ↦ by ring
    linarith
  · have hpos := expect_signed_rot_le_zigzagBound G (ε := 1) (by norm_num)
      hlam0 hlam1 halpha0 halpha1 hB₂ f₁ g₂ hg₂_fiber
      (by simpa [one_mul, hf₁_walk] using hf₁_abs) hg₂_sq
    simpa only [one_mul] using hpos

/-- **Zig-Zag Spectral-Gap Corollary**: for any `D`-regular multigraph `G` on `V` and `E`-regular
multigraph `H` on `D`,
`(1 - H.spectralExpansion ^ 2) * (1 - G.spectralExpansion) / 2 ≤
  1 - (G.zigzag H).spectralExpansion`. -/
theorem le_one_sub_spectralExpansion_zigzag {V D E : Type*} [Fintype V] [Fintype D] [Fintype E]
    (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E) :
    (1 - H.spectralExpansion ^ 2) * (1 - G.spectralExpansion) / 2 ≤
      1 - (G.zigzag H).spectralExpansion := by
  have h1 := spectralExpansion_zigzag_le_zigzagBound G H
  have h2 := zigzagBound_le_one_sub (alpha := H.spectralExpansion)
    (by rw [abs_of_nonneg G.spectralExpansion_nonneg]; exact G.spectralExpansion_le_one)
  linarith

/-! ### 2. Rozenman–Vadhan Derandomized Graph Squaring -/

section DerandomizedSquare

variable {V D E : Type*}

/-- Functional rotation step for the Rozenman–Vadhan derandomized square: from `(v, (x, a))`,
set `(u, y) = rotG (v, x)`, `(z, b) = rotH (y, a)`, and `(w, h) = rotG (u, z)`, returning
`(w, (h, b))`. -/
@[expose]
def derandomizedSquareRot (rotG : V × D → V × D) (rotH : D × E → D × E)
    (p : V × (D × E)) : V × (D × E) :=
  let step₁ := rotG (p.1, p.2.1)
  let stepH := rotH (step₁.2, p.2.2)
  let step₂ := rotG (step₁.1, stepH.1)
  (step₂.1, (step₂.2, stepH.2))

/-- `derandomizedSquareRot` is involutive whenever `rotG` and `rotH` are involutive. -/
theorem derandomizedSquareRot_involutive {rotG : V × D → V × D} {rotH : D × E → D × E}
    (hG : Function.Involutive rotG) (hH : Function.Involutive rotH) :
    Function.Involutive (derandomizedSquareRot rotG rotH) := fun p ↦ by
  dsimp only [derandomizedSquareRot]
  rw [hG ( (rotG (p.1, p.2.1)).1, (rotH ((rotG (p.1, p.2.1)).2, p.2.2)).1 ),
    hH ((rotG (p.1, p.2.1)).2, p.2.2), hG (p.1, p.2.1)]

/-- The **Rozenman–Vadhan derandomized square** of a `D`-regular multigraph `G` on `V` by an
`E`-regular multigraph `H` on `D`, yielding a `(D × E)`-regular multigraph on `V`. -/
@[expose]
def derandomizedSquare (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E) :
    Cslib.RotationMap V (D × E) where
  rot := derandomizedSquareRot G.rot H.rot
  rot_involutive := derandomizedSquareRot_involutive G.rot_involutive H.rot_involutive

/-- Rotation map equation for `derandomizedSquare G H`. -/
@[simp]
theorem rot_derandomizedSquare (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E)
    (v : V) (x : D) (a : E) :
    (derandomizedSquare G H).rot (v, (x, a)) =
      let u := G.rot (v, x)
      let z := H.rot (u.2, a)
      let w := G.rot (u.1, z.1)
      (w.1, (w.2, z.2)) :=
  rfl

/-- Neighbor equation for `derandomizedSquare G H`. -/
@[simp]
theorem neighbor_derandomizedSquare (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E)
    (v : V) (p : D × E) :
    (derandomizedSquare G H).neighbor v p =
      G.neighbor (G.neighbor v p.1) (H.neighbor (G.rot (v, p.1)).2 p.2) :=
  rfl

/-- Derandomized squaring is functorial with respect to rotation-map homomorphisms. -/
@[expose]
def Hom.derandomizedSquare {W : Type*} {G : Cslib.RotationMap V D} {G' : Cslib.RotationMap W D}
    (φ : Cslib.RotationMap.Hom G G') (H : Cslib.RotationMap D E) :
    Cslib.RotationMap.Hom (CslibFrontier.RotationMap.derandomizedSquare G H)
      (CslibFrontier.RotationMap.derandomizedSquare G' H) where
  toFun := φ
  rot_map' v p := by
    obtain ⟨x, a⟩ := p
    change (CslibFrontier.RotationMap.derandomizedSquare G' H).rot (φ v, (x, a)) = _
    rw [rot_derandomizedSquare, rot_derandomizedSquare]
    dsimp only
    rw [φ.rot_map, Prod.map_fst, Prod.map_snd, id_eq, φ.rot_map]
    rfl

/-- Applying `Hom.derandomizedSquare φ H` evaluates `φ` on vertices. -/
@[simp]
theorem Hom.derandomizedSquare_apply {W : Type*} {G : Cslib.RotationMap V D}
    {G' : Cslib.RotationMap W D} (φ : Cslib.RotationMap.Hom G G') (H : Cslib.RotationMap D E)
    (v : V) : Hom.derandomizedSquare φ H v = φ v :=
  rfl

/-- Every edge of `derandomizedSquare G H` joins vertices reachable in two steps of `G`. -/
theorem reachable_neighbor_derandomizedSquare (G : Cslib.RotationMap V D)
    (H : Cslib.RotationMap D E) (v : V) (p : D × E) :
    G.toSimpleGraph.Reachable v ((derandomizedSquare G H).neighbor v p) := by
  rw [neighbor_derandomizedSquare]
  exact (G.reachable_neighbor v p.1).trans (G.reachable_neighbor _ _)

/-- The walk operator of `derandomizedSquare G H` averages `f` over a step in `G` followed by an
`H`-perturbed step in `G`. -/
theorem walk_derandomizedSquare [Fintype D] [Fintype E] (G : Cslib.RotationMap V D)
    (H : Cslib.RotationMap D E) (f : V → ℝ) (v : V) :
    (derandomizedSquare G H).walk f v =
      𝔼 x : D, 𝔼 a : E, f (G.neighbor (G.neighbor v x) (H.neighbor (G.rot (v, x)).2 a)) := by
  rw [Cslib.RotationMap.walk_apply, Fintype.expect_prod_type]
  rfl

/-- The Rozenman–Vadhan spectral bound `1 - (1 - λ²) (1 - α)` for derandomized squaring. -/
@[expose]
def derandomizedSquareBound (lam alpha : ℝ) : ℝ :=
  1 - (1 - lam ^ 2) * (1 - alpha)

/-- For `0 ≤ alpha`, `derandomizedSquareBound lam alpha ≤ lam ^ 2 + alpha`. -/
theorem derandomizedSquareBound_le_add {lam alpha : ℝ} (halpha : 0 ≤ alpha) :
    derandomizedSquareBound lam alpha ≤ lam ^ 2 + alpha := by
  unfold derandomizedSquareBound
  nlinarith [sq_nonneg lam]

/-- For `|lam| ≤ 1` and `0 ≤ alpha ≤ 1`, `0 ≤ derandomizedSquareBound lam alpha`. -/
theorem derandomizedSquareBound_nonneg {lam alpha : ℝ} (hlam : |lam| ≤ 1) (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1) : 0 ≤ derandomizedSquareBound lam alpha := by
  unfold derandomizedSquareBound
  have hlam2 : lam ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg lam]
  have hprod : (1 - lam ^ 2) * (1 - alpha) ≤ 1 := by
    nlinarith [sq_nonneg lam]
  linarith

/-- Monotonicity of `derandomizedSquareBound` on `[0, 1] × [0, 1]`. -/
theorem derandomizedSquareBound_mono {lam₁ lam₂ alpha₁ alpha₂ : ℝ} (hl0 : 0 ≤ lam₁)
    (hl : lam₁ ≤ lam₂) (hl1 : lam₂ ≤ 1) (ha : alpha₁ ≤ alpha₂) (ha1 : alpha₂ ≤ 1) :
    derandomizedSquareBound lam₁ alpha₁ ≤ derandomizedSquareBound lam₂ alpha₂ := by
  unfold derandomizedSquareBound
  have hsq : lam₁ ^ 2 ≤ lam₂ ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have hl2_le : lam₂ ^ 2 ≤ 1 := by nlinarith
  have h1 : (1 - lam₂ ^ 2) * (1 - alpha₂) ≤ (1 - lam₁ ^ 2) * (1 - alpha₂) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (1 - lam₁ ^ 2) * (1 - alpha₂) ≤ (1 - lam₁ ^ 2) * (1 - alpha₁) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- Strict monotonicity of `derandomizedSquareBound` when `0 ≤ lam₁ < lam₂ ≤ 1` and
`0 ≤ alpha₁ < alpha₂ ≤ 1`. -/
theorem derandomizedSquareBound_strictMono {lam₁ lam₂ alpha₁ alpha₂ : ℝ} (hl0 : 0 ≤ lam₁)
    (hl : lam₁ < lam₂) (hl1 : lam₂ ≤ 1) (ha : alpha₁ < alpha₂) (ha1 : alpha₂ ≤ 1) :
    derandomizedSquareBound lam₁ alpha₁ < derandomizedSquareBound lam₂ alpha₂ := by
  unfold derandomizedSquareBound
  have hsq : lam₁ ^ 2 < lam₂ ^ 2 := pow_lt_pow_left₀ hl hl0 two_ne_zero
  have hl1_lt : lam₁ ^ 2 < 1 := hsq.trans_le (by nlinarith)
  have h1 : (1 - lam₂ ^ 2) * (1 - alpha₂) ≤ (1 - lam₁ ^ 2) * (1 - alpha₂) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : (1 - lam₁ ^ 2) * (1 - alpha₂) < (1 - lam₁ ^ 2) * (1 - alpha₁) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  linarith

/-- **Rozenman–Vadhan Derandomized Squaring Theorem**: for any finite `D`-regular multigraph `G`
on `V` and finite `E`-regular multigraph `H` on `D`,
`(derandomizedSquare G H).spectralExpansion ≤
  derandomizedSquareBound G.spectralExpansion H.spectralExpansion`. -/
theorem spectralExpansion_derandomizedSquare_le [Fintype V] [Fintype D] [Fintype E]
    (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E) :
    (derandomizedSquare G H).spectralExpansion ≤
      derandomizedSquareBound G.spectralExpansion H.spectralExpansion := by
  set lam := G.spectralExpansion
  set alpha := H.spectralExpansion
  have hlam0 : 0 ≤ lam := G.spectralExpansion_nonneg
  have hlam1 : lam ≤ 1 := G.spectralExpansion_le_one
  have halpha0 : 0 ≤ alpha := H.spectralExpansion_nonneg
  have halpha1 : alpha ≤ 1 := H.spectralExpansion_le_one
  have hbound0 : 0 ≤ derandomizedSquareBound lam alpha :=
    derandomizedSquareBound_nonneg (by rw [abs_of_nonneg hlam0]; exact hlam1) halpha0 halpha1
  refine (derandomizedSquare G H).spectralExpansion_le_of_abs_expect_mul_walk_le hbound0
    fun f hf ↦ ?_
  rcases isEmpty_or_nonempty E with hE | hE
  · have hzero : (derandomizedSquare G H).walk f = 0 :=
      funext fun v ↦ by simp [walk_derandomizedSquare]
    rw [hzero]
    simp only [Pi.zero_apply, mul_zero, expect_const_zero, abs_zero]
    exact mul_nonneg hbound0 (expect_nonneg fun v _ ↦ sq_nonneg (f v))
  rcases isEmpty_or_nonempty D with hD | hD
  · have hzero : (derandomizedSquare G H).walk f = 0 :=
      funext fun v ↦ by simp [walk_derandomizedSquare]
    rw [hzero]
    simp only [Pi.zero_apply, mul_zero, expect_const_zero, abs_zero]
    exact mul_nonneg hbound0 (expect_nonneg fun v _ ↦ sq_nonneg (f v))
  let g : V × D → ℝ := fun q ↦ f (G.rot q).1
  have hg_norm : 𝔼 q, g q ^ 2 = 𝔼 v, f v ^ 2 := by
    calc 𝔼 q, g q ^ 2 = 𝔼 q : V × D, f (G.rot q).1 ^ 2 := rfl
      _ = 𝔼 q : V × D, f q.1 ^ 2 := G.expect_comp_rot fun q ↦ f q.1 ^ 2
      _ = 𝔼 v, f v ^ 2 := expect_comp_fst fun v ↦ f v ^ 2
  have hg_avg (u : V) : 𝔼 y : D, g (u, y) = G.walk f u := by
    rw [Cslib.RotationMap.walk_apply]
    rfl
  let g₂ : V × D → ℝ := fun q ↦ g q - G.walk f q.1
  have hg₂_fiber (u : V) : 𝔼 y : D, g₂ (u, y) = 0 := by
    have : (fun y ↦ g₂ (u, y)) = fun y ↦ g (u, y) - 𝔼 y', g (u, y') :=
      funext fun y ↦ by dsimp only [g₂]; rw [hg_avg]
    rw [this]
    exact Fintype.expect_sub_expect_fiber g u
  have hg_eq : g = fun q ↦ G.walk f q.1 + g₂ q := funext fun q ↦ by dsimp only [g₂]; ring
  have hpyth : 𝔼 v, f v ^ 2 = 𝔼 u, G.walk f u ^ 2 + 𝔼 q, g₂ q ^ 2 := by
    rw [← hg_norm, hg_eq, expect_add_sq_of_expect_fiber_eq_zero (G.walk f) hg₂_fiber,
      expect_comp_fst fun u ↦ G.walk f u ^ 2]
  have hquad :
      𝔼 v, f v * (derandomizedSquare G H).walk f v =
        𝔼 u, G.walk f u ^ 2 + 𝔼 u, 𝔼 y, g₂ (u, y) * H.walk (fun z ↦ g₂ (u, z)) y := by
    have hstep1 :
        𝔼 v, f v * (derandomizedSquare G H).walk f v =
          𝔼 q : V × D, g q * H.walk (fun z ↦ g (q.1, z)) q.2 := by
      have h1 :
          𝔼 v, f v * (derandomizedSquare G H).walk f v =
            𝔼 v : V, 𝔼 x : D, f v *
              𝔼 a : E, f (G.neighbor (G.neighbor v x) (H.neighbor (G.rot (v, x)).2 a)) :=
        expect_congr rfl fun v _ ↦ by
          rw [walk_derandomizedSquare, mul_expect]
      rw [h1, ← Fintype.expect_prod_type (fun q : V × D ↦
        f q.1 * 𝔼 a : E, f (G.neighbor (G.neighbor q.1 q.2) (H.neighbor (G.rot q).2 a)))]
      have hrot_inv :
          𝔼 q : V × D, f q.1 * 𝔼 a : E, f (G.neighbor (G.neighbor q.1 q.2)
            (H.neighbor (G.rot q).2 a)) =
          𝔼 q : V × D, f (G.rot q).1 * 𝔼 a : E, f (G.neighbor q.1 (H.neighbor q.2 a)) := by
        calc 𝔼 q : V × D, f q.1 * 𝔼 a : E, f (G.neighbor (G.neighbor q.1 q.2)
              (H.neighbor (G.rot q).2 a))
            = 𝔼 q : V × D, f (G.rot (G.rot q)).1 *
                𝔼 a : E, f (G.neighbor (G.rot q).1 (H.neighbor (G.rot q).2 a)) :=
              expect_congr rfl fun q _ ↦ by rw [G.rot_rot]; rfl
          _ = 𝔼 q : V × D, f (G.rot q).1 * 𝔼 a : E, f (G.neighbor q.1 (H.neighbor q.2 a)) :=
              G.expect_comp_rot fun r ↦
                f (G.rot r).1 * 𝔼 a : E, f (G.neighbor r.1 (H.neighbor r.2 a))
      rw [hrot_inv]
      exact expect_congr rfl fun q _ ↦ by rw [Cslib.RotationMap.walk_apply]; rfl
    rw [hstep1]
    have htensor :
        𝔼 q : V × D, g q * H.walk (fun z ↦ g (q.1, z)) q.2 =
          𝔼 q : V × D, g q * (((Cslib.RotationMap.loops V Unit).tensor H).walk g q) :=
      expect_congr rfl fun q _ ↦ by rw [H.walk_loops_tensor_apply]
    rw [htensor, hg_eq, H.walk_loops_tensor_add (G.walk f) g₂]
    have horth1 : 𝔼 q : V × D, G.walk f q.1 *
        (((Cslib.RotationMap.loops V Unit).tensor H).walk g₂ q) = 0 := by
      have hfib := H.expect_walk_loops_tensor_eq_zero hg₂_fiber
      simp only [Fintype.expect_prod_type, ← mul_expect, hfib, mul_zero, expect_const_zero]
    have horth2 : 𝔼 q : V × D, g₂ q * G.walk f q.1 = 0 := by
      simp only [Fintype.expect_prod_type, mul_comm (g₂ _), ← mul_expect, hg₂_fiber, mul_zero,
        expect_const_zero]
    have hpt (q : V × D) :
        (G.walk f q.1 + g₂ q) *
            (G.walk f q.1 + ((Cslib.RotationMap.loops V Unit).tensor H).walk g₂ q) =
          G.walk f q.1 ^ 2 + G.walk f q.1 *
            (((Cslib.RotationMap.loops V Unit).tensor H).walk g₂ q) +
            g₂ q * G.walk f q.1 +
            g₂ q * (((Cslib.RotationMap.loops V Unit).tensor H).walk g₂ q) := by
      ring
    simp only [hpt, expect_add_distrib, horth1, horth2, add_zero]
    rw [expect_comp_fst fun u ↦ G.walk f u ^ 2, Fintype.expect_prod_type]
    congr 1
    exact expect_congr rfl fun u _ ↦ expect_congr rfl fun y _ ↦ by
      rw [H.walk_loops_tensor_apply]
  have hH_abs :
      |𝔼 u, 𝔼 y, g₂ (u, y) * H.walk (fun z ↦ g₂ (u, z)) y| ≤ alpha * 𝔼 q, g₂ q ^ 2 := by
    calc |𝔼 u, 𝔼 y, g₂ (u, y) * H.walk (fun z ↦ g₂ (u, z)) y|
        ≤ 𝔼 u, |𝔼 y, g₂ (u, y) * H.walk (fun z ↦ g₂ (u, z)) y| := abs_expect_le _ _
      _ ≤ 𝔼 u, (alpha * 𝔼 y, g₂ (u, y) ^ 2) :=
          expect_le_expect fun u _ ↦ H.abs_expect_mul_walk_le (hg₂_fiber u)
      _ = alpha * 𝔼 q, g₂ q ^ 2 := by
          rw [← mul_expect, ← Fintype.expect_prod_type (fun q : V × D ↦ g₂ q ^ 2)]
  have hwalk_sq : 𝔼 u, G.walk f u ^ 2 ≤ lam ^ 2 * 𝔼 v, f v ^ 2 :=
    G.expect_walk_sq_le_spectralExpansion_sq_mul hf
  have hwalk_nn : 0 ≤ 𝔼 u, G.walk f u ^ 2 := expect_nonneg fun u _ ↦ sq_nonneg _
  have hf_nn : 0 ≤ 𝔼 v, f v ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg _
  rw [hquad, abs_le]
  have hH_le := abs_le.mp hH_abs
  constructor
  · have hlow : -alpha * 𝔼 v, f v ^ 2 ≤
        𝔼 u, G.walk f u ^ 2 + 𝔼 u, 𝔼 y, g₂ (u, y) * H.walk (fun z ↦ g₂ (u, z)) y := by
      nlinarith [hH_le.1, hpyth]
    have hgap : 0 ≤ (derandomizedSquareBound lam alpha - alpha) * 𝔼 v, f v ^ 2 := by
      unfold derandomizedSquareBound
      have : 1 - (1 - lam ^ 2) * (1 - alpha) - alpha = lam ^ 2 * (1 - alpha) := by ring
      rw [this]
      exact mul_nonneg (mul_nonneg (sq_nonneg lam) (by linarith)) hf_nn
    linarith
  · have hhigh :
        𝔼 u, G.walk f u ^ 2 + 𝔼 u, 𝔼 y, g₂ (u, y) * H.walk (fun z ↦ g₂ (u, z)) y ≤
          (1 - alpha) * 𝔼 u, G.walk f u ^ 2 + alpha * 𝔼 v, f v ^ 2 := by
      nlinarith [hH_le.2, hpyth]
    have hstep :
        (1 - alpha) * 𝔼 u, G.walk f u ^ 2 + alpha * 𝔼 v, f v ^ 2 ≤
          derandomizedSquareBound lam alpha * 𝔼 v, f v ^ 2 := by
      unfold derandomizedSquareBound
      have : (1 - alpha) * 𝔼 u, G.walk f u ^ 2 ≤ (1 - alpha) * (lam ^ 2 * 𝔼 v, f v ^ 2) :=
        mul_le_mul_of_nonneg_left hwalk_sq (by linarith)
      nlinarith
    exact hhigh.trans hstep

/-- Simplified Rozenman–Vadhan bound:
`(derandomizedSquare G H).spectralExpansion ≤ G.spectralExpansion ^ 2 + H.spectralExpansion`. -/
theorem spectralExpansion_derandomizedSquare_le_add [Fintype V] [Fintype D] [Fintype E]
    (G : Cslib.RotationMap V D) (H : Cslib.RotationMap D E) :
    (derandomizedSquare G H).spectralExpansion ≤
      G.spectralExpansion ^ 2 + H.spectralExpansion :=
  (spectralExpansion_derandomizedSquare_le G H).trans
    (derandomizedSquareBound_le_add H.spectralExpansion_nonneg)

end DerandomizedSquare

/-! ### 3. Non-Degenerate Sanity Examples -/

private example :
    let G := Cslib.RotationMap.loops (Fin 3) (Fin 2)
    let H := Cslib.RotationMap.loops (Fin 2) (Fin 2)
    (G.zigzag H).spectralExpansion ≤ zigzagBound G.spectralExpansion H.spectralExpansion ∧
      (derandomizedSquare G H).spectralExpansion ≤
        derandomizedSquareBound G.spectralExpansion H.spectralExpansion :=
  ⟨spectralExpansion_zigzag_le_zigzagBound _ _, spectralExpansion_derandomizedSquare_le _ _⟩

end CslibFrontier.RotationMap
