/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Or
public import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximate Polynomial Degree, Threshold Degree, and Dual Polynomials

This module defines the `α`-approximate polynomial degree (`alphaApproxDeg`) and threshold degree
(`inftyApproxDeg`) of Boolean functions on `BitString n`, bridges `alphaApproxDeg` to
`Cslib.QueryComplexity.approxDegree`, derives Nisan–Szegedy lower bounds for disjunction `OR_n`,
establishes strong linear-programming duality for the minimum approximation error at degree `d`,
and proves the existence of high-pure-high-degree dual polynomials for both finite `α` and `α = ∞`.

## Main definitions

* `IsAlphaApprox`, `IsInftyApprox`, `alphaApproxDeg`, `inftyApproxDeg`, `minAlphaForDeg`:
  `α`-approximate and threshold polynomial degrees and minimum approximation factor at degree `d`.

## Main results

* `approxDegree_eq_alphaApproxDeg`: correspondence between `Cslib.QueryComplexity.approxDegree`
  and `alphaApproxDeg ((1 + 2ε) / (1 - 2ε))`.
* `nisan_szegedy_alphaApproxDeg_five_or`, `nisan_szegedy_alphaApproxDeg_three_or`: quadratic
  `Ω(√n)` approximate-degree lower bounds for `threshold n 1` (`OR_n`).
* `minAlphaForDeg_dual`: strong LP duality characterizing `minAlphaForDeg d f`.
* `exists_dual_polynomial_finite`, `exists_dual_polynomial_infty`: existence of `ℓ₁`-normalized
  dual polynomials orthogonal to all parities of degree `< deg_α(f)` (resp. `< deg_∞(f)`).
-/

public section

open scoped BigOperators NNReal
open Cslib Cslib.BitString Cslib.QueryComplexity

namespace CslibFrontier.Computability.QueryComplexity

section ApproximateDegree

variable {n : ℕ}

/-- **`α`-approximating polynomial**:
`1 ≤ g(x) f(x) ≤ α` for all `x ∈ {0, 1}^n` (with `f` represented in `{-1, +1}` via `signVal`). -/
def IsAlphaApprox (α : ℝ) (f : BitString n → Bool) (g : BitString n → ℝ) : Prop :=
  ∀ x : BitString n, 1 ≤ g x * signVal (f x) ∧ g x * signVal (f x) ≤ α

/-- **`∞`-approximating (sign-representing) polynomial**: `1 ≤ g(x) f(x)` for all `x`. -/
def IsInftyApprox (f : BitString n → Bool) (g : BitString n → ℝ) : Prop :=
  ∀ x : BitString n, 1 ≤ g x * signVal (f x)

/-- **the definition — `α`-approximate degree `deg_α(f)`**. -/
noncomputable def alphaApproxDeg (α : ℝ) (f : BitString n → Bool) : ℕ :=
  sInf {d : ℕ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox α f g}

/-- **the definition — `∞`-approximate (threshold) degree `deg_∞(f)`**. -/
noncomputable def inftyApproxDeg (f : BitString n → Bool) : ℕ :=
  sInf {d : ℕ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsInftyApprox f g}

/-- Minimum approximation factor `α_d(f)` achievable by a degree-`≤ d` polynomial. -/
noncomputable def minAlphaForDeg (d : ℕ) (f : BitString n → Bool) : ℝ :=
  sInf {α : ℝ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox α f g}

/-- For `1 ≤ α`, `signVal ∘ f` itself is an `α`-approximation of degree at most `n`. -/
theorem signVal_isAlphaApprox {α : ℝ} (hα : 1 ≤ α) (f : BitString n → Bool) :
    IsAlphaApprox α f (fun x ↦ signVal (f x)) := fun x ↦ by
  rw [signVal_mul_self (f x)]
  exact ⟨le_rfl, hα⟩

/-- `signVal ∘ f` is always an `∞`-approximation of degree at most `n`. -/
theorem signVal_isInftyApprox (f : BitString n → Bool) :
    IsInftyApprox f (fun x ↦ signVal (f x)) := fun x ↦ by
  rw [signVal_mul_self (f x)]

/-- `deg_α(f) ≤ n` whenever `1 ≤ α`. -/
theorem alphaApproxDeg_le_card {α : ℝ} (hα : 1 ≤ α) (f : BitString n → Bool) :
    alphaApproxDeg α f ≤ n :=
  Nat.sInf_le ⟨fun x ↦ signVal (f x),
    (by simpa using mem_lowDegree_self (R := ℝ) (fun x : BitString n ↦ signVal (f x))),
    signVal_isAlphaApprox hα f⟩

/-- `deg_∞(f) ≤ n`. -/
theorem inftyApproxDeg_le_card (f : BitString n → Bool) : inftyApproxDeg f ≤ n :=
  Nat.sInf_le ⟨fun x ↦ signVal (f x),
    (by simpa using mem_lowDegree_self (R := ℝ) (fun x : BitString n ↦ signVal (f x))),
    signVal_isInftyApprox f⟩

/-- For `1 ≤ α`, `deg_α(f)` is attained by a polynomial of degree at most `deg_α(f)`. -/
theorem exists_mem_lowDegree_alphaApproxDeg {α : ℝ} (hα : 1 ≤ α) (f : BitString n → Bool) :
    ∃ g ∈ lowDegree ℝ (Fin n) (alphaApproxDeg α f), IsAlphaApprox α f g :=
  Nat.sInf_mem (s := {d : ℕ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox α f g})
    ⟨n, fun x ↦ signVal (f x),
      (by simpa using mem_lowDegree_self (R := ℝ) (fun x : BitString n ↦ signVal (f x))),
      signVal_isAlphaApprox hα f⟩

/-- `deg_∞(f)` is attained by a polynomial of degree at most `deg_∞(f)`. -/
theorem exists_mem_lowDegree_inftyApproxDeg (f : BitString n → Bool) :
    ∃ g ∈ lowDegree ℝ (Fin n) (inftyApproxDeg f), IsInftyApprox f g :=
  Nat.sInf_mem (s := {d : ℕ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsInftyApprox f g})
    ⟨n, fun x ↦ signVal (f x),
      (by simpa using mem_lowDegree_self (R := ℝ) (fun x : BitString n ↦ signVal (f x))),
      signVal_isInftyApprox f⟩

/-- `deg_α(f) ≤ d` iff there exists an `α`-approximating polynomial of degree at most `d`. -/
theorem alphaApproxDeg_le_iff {α : ℝ} (hα : 1 ≤ α) {f : BitString n → Bool} {d : ℕ} :
    alphaApproxDeg α f ≤ d ↔ ∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox α f g := by
  constructor
  · intro h
    obtain ⟨g, hg, happrox⟩ := exists_mem_lowDegree_alphaApproxDeg hα f
    exact ⟨g, lowDegree_mono h hg, happrox⟩
  · intro h
    exact Nat.sInf_le h

/-- `deg_∞(f) ≤ d` iff there exists an `∞`-approximating polynomial of degree at most `d`. -/
theorem inftyApproxDeg_le_iff {f : BitString n → Bool} {d : ℕ} :
    inftyApproxDeg f ≤ d ↔ ∃ g ∈ lowDegree ℝ (Fin n) d, IsInftyApprox f g := by
  constructor
  · intro h
    obtain ⟨g, hg, happrox⟩ := exists_mem_lowDegree_inftyApproxDeg f
    exact ⟨g, lowDegree_mono h hg, happrox⟩
  · intro h
    exact Nat.sInf_le h

/-- `deg_α(f)` is antitone in `α` for `1 ≤ α ≤ β`. -/
theorem alphaApproxDeg_antitone {α β : ℝ} (hα : 1 ≤ α) (hαβ : α ≤ β) (f : BitString n → Bool) :
    alphaApproxDeg β f ≤ alphaApproxDeg α f := by
  obtain ⟨g, hg, happrox⟩ := exists_mem_lowDegree_alphaApproxDeg hα f
  exact Nat.sInf_le ⟨g, hg, fun x ↦ ⟨(happrox x).1, (happrox x).2.trans hαβ⟩⟩

/-- `deg_∞(f) ≤ deg_α(f)` whenever `1 ≤ α`. -/
theorem inftyApproxDeg_le_alphaApproxDeg {α : ℝ} (hα : 1 ≤ α) (f : BitString n → Bool) :
    inftyApproxDeg f ≤ alphaApproxDeg α f := by
  obtain ⟨g, hg, happrox⟩ := exists_mem_lowDegree_alphaApproxDeg hα f
  exact Nat.sInf_le ⟨g, hg, fun x ↦ (happrox x).1⟩

/-- **Norm Equivalence**:
For `0 ≤ ε < 1/2`, the standard `0/1` approximate degree `approxDegree ε f` equals
`alphaApproxDeg ((1 + 2ε) / (1 - 2ε)) f`. -/
theorem approxDegree_eq_alphaApproxDeg {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 2)
    (f : BooleanFunction n) :
    approxDegree ε f = alphaApproxDeg ((1 + 2 * (ε : ℝ)) / (1 - 2 * (ε : ℝ))) f := by
  have hpos : 0 < 1 - 2 * (ε : ℝ) := by linarith
  have hε0 : (0 : ℝ) ≤ (ε : ℝ) := ε.2
  have hα : 1 ≤ (1 + 2 * (ε : ℝ)) / (1 - 2 * (ε : ℝ)) := by
    rw [le_div_iff₀ hpos]; linarith
  refine congrArg sInf (Set.ext fun D ↦ ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hpe⟩
    let g : BitString n → ℝ := ((1 - 2 * (ε : ℝ))⁻¹ : ℝ) • (1 - (2 : ℝ) • p)
    have hg : g ∈ lowDegree ℝ (Fin n) D :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (one_mem_lowDegree D) (Submodule.smul_mem _ _ hp))
    refine ⟨g, hg, fun x ↦ ?_⟩
    have h1 : 1 - 2 * p x - signVal (f x) = -2 * (p x - bitVal ℝ (f x)) := by
      rw [signVal_eq_one_sub_two_mul_bitVal]; ring
    have habs : |(1 - 2 * p x) * signVal (f x) - 1| ≤ 2 * (ε : ℝ) := by
      have heq : (1 - 2 * p x) * signVal (f x) - 1 =
          (1 - 2 * p x - signVal (f x)) * signVal (f x) := by
        symm
        rw [sub_mul, signVal_mul_self]
      rw [heq, abs_mul, abs_signVal, mul_one, h1, abs_mul, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hpe x]
    have hlo : 1 - 2 * (ε : ℝ) ≤ (1 - 2 * p x) * signVal (f x) := by linarith [(abs_le.mp habs).1]
    have hhi : (1 - 2 * p x) * signVal (f x) ≤ 1 + 2 * (ε : ℝ) := by linarith [(abs_le.mp habs).2]
    have hgx : g x * signVal (f x) = ((1 - 2 * p x) * signVal (f x)) / (1 - 2 * (ε : ℝ)) := by
      simp only [g, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, div_eq_inv_mul]
      ring
    rw [hgx, le_div_iff₀ hpos, div_le_div_iff_of_pos_right hpos]
    exact ⟨by linarith, hhi⟩
  · rintro ⟨g, hg, hga⟩
    let p : BitString n → ℝ := ((2 : ℝ)⁻¹) • (1 - (1 - 2 * (ε : ℝ)) • g)
    have hp : p ∈ lowDegree ℝ (Fin n) D :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (one_mem_lowDegree D) (Submodule.smul_mem _ _ hg))
    refine ⟨p, hp, fun x ↦ ?_⟩
    have hpx : p x - bitVal ℝ (f x) =
        ((signVal (f x) - (1 - 2 * (ε : ℝ)) * g x) / 2) := by
      have hbv : bitVal ℝ (f x) = (1 - signVal (f x)) / 2 := by
        rw [signVal_eq_one_sub_two_mul_bitVal]; ring
      simp only [p, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, hbv]
      ring
    have hprod : (signVal (f x) - (1 - 2 * (ε : ℝ)) * g x) * signVal (f x) =
        1 - (1 - 2 * (ε : ℝ)) * (g x * signVal (f x)) := by
      rw [sub_mul, signVal_mul_self]; ring
    have hlo : 1 - 2 * (ε : ℝ) ≤ (1 - 2 * (ε : ℝ)) * (g x * signVal (f x)) := by
      nlinarith [(hga x).1]
    have hhi : (1 - 2 * (ε : ℝ)) * (g x * signVal (f x)) ≤ 1 + 2 * (ε : ℝ) := by
      have h2 := (hga x).2
      rw [le_div_iff₀ hpos] at h2
      linarith
    have habs : |signVal (f x) - (1 - 2 * (ε : ℝ)) * g x| ≤ 2 * (ε : ℝ) := by
      calc |signVal (f x) - (1 - 2 * (ε : ℝ)) * g x|
          = |signVal (f x) - (1 - 2 * (ε : ℝ)) * g x| * |signVal (f x)| := by
            rw [abs_signVal, mul_one]
        _ = |(signVal (f x) - (1 - 2 * (ε : ℝ)) * g x) * signVal (f x)| := (abs_mul _ _).symm
        _ = |1 - (1 - 2 * (ε : ℝ)) * (g x * signVal (f x))| := by rw [hprod]
        _ ≤ 2 * (ε : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hpx, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-- **Nisan–Szegedy Approximate Degree Lower Bound for `OR_n`**:
`n ≤ 6 · deg_5(OR_n)²` (and hence `n ≤ 6 · deg_3(OR_n)²`), proved directly from
`Cslib.QueryComplexity.card_le_six_mul_approxDegree_threshold_one_right_sq` and the remark. -/
theorem nisan_szegedy_alphaApproxDeg_five_or (n : ℕ) :
    n ≤ 6 * alphaApproxDeg 5 (threshold n 1) ^ 2 := by
  have hrem := approxDegree_eq_alphaApproxDeg (ε := (1 / 3 : ℝ≥0)) (by norm_num)
    (threshold n 1)
  have hfive : (1 + 2 * ((1 / 3 : ℝ≥0) : ℝ)) / (1 - 2 * ((1 / 3 : ℝ≥0) : ℝ)) = (5 : ℝ) := by
    norm_num
  rw [hfive] at hrem
  rw [← hrem]
  exact card_le_six_mul_approxDegree_threshold_one_right_sq

/-- `n ≤ 6 · deg_3(OR_n)²`. -/
theorem nisan_szegedy_alphaApproxDeg_three_or (n : ℕ) :
    n ≤ 6 * alphaApproxDeg 3 (threshold n 1) ^ 2 := by
  have h5 := nisan_szegedy_alphaApproxDeg_five_or n
  have hle : alphaApproxDeg 5 (threshold n 1) ≤ alphaApproxDeg 3 (threshold n 1) :=
    alphaApproxDeg_antitone (by norm_num) (by norm_num) (threshold n 1)
  have hsq : alphaApproxDeg 5 (threshold n 1) ^ 2 ≤ alphaApproxDeg 3 (threshold n 1) ^ 2 :=
    Nat.pow_le_pow_left hle 2
  omega

end ApproximateDegree

section DualPolynomials

variable {n : ℕ}

/-- Pointwise inner product `⟨v, f⟩ = ∑_x v(x) f(x)` on `BitString n`. -/
@[expose] def boolInner (v : BitString n → ℝ) (f : BitString n → Bool) : ℝ :=
  ∑ x : BitString n, v x * signVal (f x)

/-- Sum expansion of the Boolean-domain inner product. -/
theorem boolInner_eq_sum (v : BitString n → ℝ) (f : BitString n → Bool) :
    boolInner v f = ∑ x : BitString n, v x * signVal (f x) := rfl

/-- `ℓ₁` norm `‖v‖₁ = ∑_x |v(x)|` on `BitString n`. -/
@[expose] def boolL1 (v : BitString n → ℝ) : ℝ :=
  ∑ x : BitString n, |v x|

/-- Sum expansion of the Boolean-domain `ℓ₁` norm. -/
theorem boolL1_eq_sum (v : BitString n → ℝ) :
    boolL1 v = ∑ x : BitString n, |v x| := rfl

/-- Vanishing of `fourierCoeff v T` is equivalent to `∑_x v(x) χ_T(x) = 0`. -/
theorem fourierCoeff_eq_zero_iff_sum_eq_zero (v : BitString n → ℝ) (T : Finset (Fin n)) :
    BitString.fourierCoeff v T = 0 ↔ ∑ x : BitString n, v x * chi ℝ T x = 0 := by
  rw [BitString.fourierCoeff_eq_sum]
  simp

/-- Every `g ∈ lowDegree ℝ (Fin n) d` is orthogonal to any `v` whose Fourier coefficients of degree
`≤ d` vanish. -/
theorem sum_mul_eq_zero_of_mem_lowDegree {d : ℕ} {g v : BitString n → ℝ}
    (hg : g ∈ lowDegree ℝ (Fin n) d)
    (hv : ∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0) :
    ∑ x : BitString n, g x * v x = 0 := by
  have hre : ∀ x, g x = ∑ T : Finset (Fin n), BitString.fourierCoeff g T * chi ℝ T x :=
    fun x ↦ (sum_fourierCoeff_mul_chi g x).symm
  calc ∑ x : BitString n, g x * v x
      = ∑ x : BitString n, (∑ T : Finset (Fin n), BitString.fourierCoeff g T * chi ℝ T x) * v x :=
        Finset.sum_congr rfl fun x _ ↦ by rw [hre x]
    _ = ∑ T : Finset (Fin n), BitString.fourierCoeff g T * ∑ x : BitString n, v x * chi ℝ T x := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun T _ ↦ ?_
        by_cases hT : T.card ≤ d
        · rw [(fourierCoeff_eq_zero_iff_sum_eq_zero v T).mp (hv T hT), mul_zero]
        · rw [fourierCoeff_eq_zero_of_mem_lowDegree hg (Nat.lt_of_not_ge hT), zero_mul]

/-- Weak duality inequality for `minAlphaForDeg`: any dual polynomial `v` orthogonal to degree `≤ d`
with `‖v‖₁ = 1` satisfies `⟨v, f⟩ ≤ (α - 1) / (α + 1)` whenever `g ∈ lowDegree d` gives an
`α`-approximation to `f`. -/
theorem boolInner_le_of_isAlphaApprox {d : ℕ} {α : ℝ} {f : BitString n → Bool}
    {g v : BitString n → ℝ} (hα : 1 ≤ α)
    (hg : g ∈ lowDegree ℝ (Fin n) d) (happrox : IsAlphaApprox α f g)
    (hv_orth : ∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0)
    (hv_l1 : boolL1 v = 1) :
    boolInner v f ≤ (α - 1) / (α + 1) := by
  have hpoint : ∀ x : BitString n,
      ((1 + α) * (v x * signVal (f x)) + (1 - α) * |v x|) / 2 ≤ g x * v x := by
    intro x
    have ha : signVal (f x) * signVal (f x) = 1 := signVal_mul_self (f x)
    have hgv : g x * v x = (g x * signVal (f x)) * (v x * signVal (f x)) := by
      calc g x * v x = g x * v x * (signVal (f x) * signVal (f x)) := by rw [ha, mul_one]
        _ = (g x * signVal (f x)) * (v x * signVal (f x)) := by ring
    have habs : |v x * signVal (f x)| = |v x| := by rw [abs_mul, abs_signVal, mul_one]
    rw [hgv, ← habs]
    have hlo := (happrox x).1
    have hhi := (happrox x).2
    by_cases hnn : 0 ≤ v x * signVal (f x)
    · rw [abs_of_nonneg hnn]; nlinarith
    · rw [abs_of_neg (lt_of_not_ge hnn)]; nlinarith
  have hsum : ((1 + α) * boolInner v f + (1 - α) * boolL1 v) / 2 ≤
      ∑ x : BitString n, g x * v x := by
    unfold boolInner boolL1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
    simp_rw [← div_eq_mul_inv]
    exact Finset.sum_le_sum fun x _ ↦ hpoint x
  rw [sum_mul_eq_zero_of_mem_lowDegree hg hv_orth, hv_l1, mul_one] at hsum
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < α + 1)]
  linarith

/-- Farkas infeasibility witness for `∞`-approximation: if no polynomial of degree `≤ d` gives an
`∞`-approximation to `f`, then there exists `v` orthogonal to degree `≤ d` with `‖v‖₁ = 1` and
`v(x) f(x) ≥ 0` everywhere. -/
theorem exists_dual_infty_of_lt_inftyApproxDeg {d : ℕ} {f : BitString n → Bool}
    (hd : d < inftyApproxDeg f) :
    ∃ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0) ∧
      boolL1 v = 1 ∧
      (∀ x : BitString n, 0 ≤ v x * signVal (f x)) := by
  let I := BitString n
  let J := {T : Finset (Fin n) // T.card ≤ d}
  let M : Matrix I J ℝ := Matrix.of fun x T ↦ -(chi ℝ T.1 x * signVal (f x))
  let b : I → ℝ := fun _ ↦ -1
  have hinfeas : ¬∃ c : J → ℝ, M.mulVec c ≤ b := by
    rintro ⟨c, hc⟩
    let g : BitString n → ℝ := fun x ↦ ∑ T : J, c T * chi ℝ T.1 x
    have hg_deg : g ∈ lowDegree ℝ (Fin n) d := by
      have heq : g = ∑ T : J, c T • chi ℝ T.1 := funext fun x ↦ by simp [g, Finset.sum_apply]
      rw [heq]
      exact Submodule.sum_mem _ fun T _ ↦
        Submodule.smul_mem _ _ (lowDegree_mono T.2 (chi_mem_lowDegree T.1))
    have hg_approx : IsInftyApprox f g := fun x ↦ by
      have hx := hc x
      simp only [M, b, Matrix.mulVec, dotProduct, Matrix.of_apply] at hx
      have heq : -(g x * signVal (f x)) = ∑ T : J, -(chi ℝ T.1 x * signVal (f x)) * c T := by
        dsimp only [g]
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun T _ ↦ by ring
      linarith
    have hle : inftyApproxDeg f ≤ d := inftyApproxDeg_le_iff.mpr ⟨g, hg_deg, hg_approx⟩
    omega
  obtain ⟨u, hu0, huM, hub⟩ := (Matrix.not_exists_mulVec_le_iff M b).mp hinfeas
  have hsum_pos : 0 < ∑ x : I, u x := by
    simp only [dotProduct, b, mul_neg, mul_one, Finset.sum_neg_distrib] at hub
    linarith
  let v : BitString n → ℝ := fun x ↦ (u x / ∑ y : I, u y) * signVal (f x)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro T hT
    rw [fourierCoeff_eq_zero_iff_sum_eq_zero]
    have hcol := congrFun huM ⟨T, hT⟩
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, M, Matrix.of_apply] at hcol
    have hsum0 : ∑ x : I, u x * (signVal (f x) * chi ℝ T x) = 0 := by
      have hneg : ∑ x : I, u x * -(chi ℝ T x * signVal (f x)) =
          -(∑ x : I, u x * (signVal (f x) * chi ℝ T x)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun x _ ↦ by ring
      rw [hneg] at hcol
      linarith
    calc ∑ x : I, v x * chi ℝ T x
        = (∑ y : I, u y)⁻¹ * ∑ x : I, u x * (signVal (f x) * chi ℝ T x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ by dsimp only [v]; ring
      _ = 0 := by rw [hsum0, mul_zero]
  · unfold boolL1
    calc ∑ x : I, |v x|
        = ∑ x : I, u x * (∑ y : I, u y)⁻¹ := Finset.sum_congr rfl fun x _ ↦ by
          dsimp only [v]
          rw [abs_mul, abs_signVal, mul_one, abs_of_nonneg (div_nonneg (hu0 x) hsum_pos.le),
            div_eq_mul_inv]
      _ = (∑ x : I, u x) * (∑ y : I, u y)⁻¹ := (Finset.sum_mul _ _ _).symm
      _ = 1 := mul_inv_cancel₀ hsum_pos.ne'
  · intro x
    dsimp only [v]
    rw [mul_assoc, signVal_mul_self, mul_one]
    exact div_nonneg (hu0 x) hsum_pos.le

/-- Farkas infeasibility witness for finite `α`-approximation: if `1 ≤ t` and no degree-`≤ d`
polynomial gives a `t`-approximation to `f`, then there exists `v` orthogonal to degree `≤ d`
with `‖v‖₁ = 1` and `(t - 1) / (t + 1) < ⟨v, f⟩`. -/
private theorem exists_dual_gt_of_no_alphaApprox {d : ℕ} {t : ℝ} {f : BitString n → Bool}
    (ht1 : 1 ≤ t) (hno : ¬∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox t f g) :
    ∃ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0) ∧
      boolL1 v = 1 ∧
      (t - 1) / (t + 1) < boolInner v f := by
  let I := BitString n
  let J := {T : Finset (Fin n) // T.card ≤ d}
  let M : Matrix (I ⊕ I) J ℝ := Matrix.of fun r T ↦
    match r with
    | .inl x => -(chi ℝ T.1 x * signVal (f x))
    | .inr x => chi ℝ T.1 x * signVal (f x)
  let b : I ⊕ I → ℝ := fun r ↦
    match r with
    | .inl _ => -1
    | .inr _ => t
  have hinfeas : ¬∃ c : J → ℝ, M.mulVec c ≤ b := by
    rintro ⟨c, hc⟩
    let g : BitString n → ℝ := fun x ↦ ∑ T : J, c T * chi ℝ T.1 x
    have hg_deg : g ∈ lowDegree ℝ (Fin n) d := by
      have heq : g = ∑ T : J, c T • chi ℝ T.1 := funext fun x ↦ by simp [g, Finset.sum_apply]
      rw [heq]
      exact Submodule.sum_mem _ fun T _ ↦
        Submodule.smul_mem _ _ (lowDegree_mono T.2 (chi_mem_lowDegree T.1))
    refine hno ⟨g, hg_deg, fun x ↦ ⟨?_, ?_⟩⟩
    · have hx := hc (.inl x)
      simp only [M, b, Matrix.mulVec, dotProduct, Matrix.of_apply] at hx
      have heq : -(g x * signVal (f x)) = ∑ T : J, -(chi ℝ T.1 x * signVal (f x)) * c T := by
        dsimp only [g]
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun T _ ↦ by ring
      linarith
    · have hx := hc (.inr x)
      simp only [M, b, Matrix.mulVec, dotProduct, Matrix.of_apply] at hx
      have heq : g x * signVal (f x) = ∑ T : J, (chi ℝ T.1 x * signVal (f x)) * c T := by
        dsimp only [g]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun T _ ↦ by ring
      linarith
  obtain ⟨y, hy0, hyM, hyb⟩ := (Matrix.not_exists_mulVec_le_iff M b).mp hinfeas
  let u : I → ℝ := fun x ↦ y (.inl x)
  let w : I → ℝ := fun x ↦ y (.inr x)
  have hu : ∀ x, 0 ≤ u x := fun x ↦ hy0 (.inl x)
  have hw : ∀ x, 0 ≤ w x := fun x ↦ hy0 (.inr x)
  have hdot : t * ∑ x : I, w x < ∑ x : I, u x := by
    simp only [dotProduct, Fintype.sum_sum_type, b, mul_neg, mul_one, Finset.sum_neg_distrib] at hyb
    have hsw : ∑ x : I, w x * t = t * ∑ x : I, w x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    change -(∑ x : I, u x) + ∑ x : I, w x * t < 0 at hyb
    linarith
  let v₀ : BitString n → ℝ := fun x ↦ (u x - w x) * signVal (f x)
  have hv₀_orth : ∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v₀ T = 0 := by
    intro T hT
    rw [fourierCoeff_eq_zero_iff_sum_eq_zero]
    have hcol := congrFun hyM ⟨T, hT⟩
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Pi.zero_apply, M,
      Matrix.of_apply] at hcol
    have heq : ∑ x : I, v₀ x * chi ℝ T x =
        -(∑ x : I, u x * -(chi ℝ T x * signVal (f x)) +
          ∑ x : I, w x * (chi ℝ T x * signVal (f x))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by dsimp only [v₀]; ring
    rw [heq]
    change -(∑ x : I, u x * -(chi ℝ T x * signVal (f x)) +
      ∑ x : I, w x * (chi ℝ T x * signVal (f x))) = 0
    rw [hcol, neg_zero]
  have hinner₀ : boolInner v₀ f = ∑ x : I, u x - ∑ x : I, w x := by
    unfold boolInner
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    dsimp only [v₀]
    rw [mul_assoc, signVal_mul_self, mul_one]
  have hl1₀_le : boolL1 v₀ ≤ ∑ x : I, u x + ∑ x : I, w x := by
    unfold boolL1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    dsimp only [v₀]
    rw [abs_mul, abs_signVal, mul_one]
    calc |u x - w x| = |u x + -w x| := by rw [sub_eq_add_neg]
      _ ≤ |u x| + |-w x| := abs_add_le _ _
      _ = u x + w x := by rw [abs_neg, abs_of_nonneg (hu x), abs_of_nonneg (hw x)]
  have hstrict₀ : (t - 1) * boolL1 v₀ < (t + 1) * boolInner v₀ f := by
    have hmul : (t - 1) * boolL1 v₀ ≤ (t - 1) * (∑ x : I, u x + ∑ x : I, w x) :=
      mul_le_mul_of_nonneg_left hl1₀_le (by linarith)
    rw [hinner₀]
    nlinarith
  have hl1₀_pos : 0 < boolL1 v₀ := by
    have hnn : 0 ≤ boolL1 v₀ := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    by_contra hle
    have h0 : boolL1 v₀ = 0 := le_antisymm (not_lt.mp hle) hnn
    have hv0 : v₀ = 0 := funext fun x ↦ by
      have hx : |v₀ x| ≤ boolL1 v₀ :=
        Finset.single_le_sum (f := fun y : I ↦ |v₀ y|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ x)
      rw [h0] at hx
      exact abs_nonpos_iff.mp hx
    have : boolInner v₀ f = 0 := by simp [boolInner, hv0]
    rw [h0, this] at hstrict₀
    linarith
  let v : BitString n → ℝ := fun x ↦ (boolL1 v₀)⁻¹ * v₀ x
  refine ⟨v, ?_, ?_, ?_⟩
  · intro T hT
    rw [fourierCoeff_eq_zero_iff_sum_eq_zero]
    have h0 := (fourierCoeff_eq_zero_iff_sum_eq_zero v₀ T).mp (hv₀_orth T hT)
    calc ∑ x : I, v x * chi ℝ T x
        = (boolL1 v₀)⁻¹ * ∑ x : I, v₀ x * chi ℝ T x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by dsimp only [v]; ring
      _ = 0 := by rw [h0, mul_zero]
  · calc boolL1 v
        = ∑ x : I, (boolL1 v₀)⁻¹ * |v₀ x| :=
          Finset.sum_congr rfl fun x _ ↦ by
            dsimp only [v]; rw [abs_mul, abs_inv, abs_of_pos hl1₀_pos]
      _ = (boolL1 v₀)⁻¹ * boolL1 v₀ := (Finset.mul_sum _ _ _).symm
      _ = 1 := inv_mul_cancel₀ hl1₀_pos.ne'
  · have hscale : boolInner v f = (boolL1 v₀)⁻¹ * boolInner v₀ f := by
      unfold boolInner
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by dsimp only [v]; ring
    rw [hscale, div_lt_iff₀ (by linarith : (0 : ℝ) < t + 1)]
    have := mul_lt_mul_of_pos_left hstrict₀ (inv_pos.mpr hl1₀_pos)
    have hL : (boolL1 v₀)⁻¹ * ((t - 1) * boolL1 v₀) = t - 1 := by field_simp [hl1₀_pos.ne']
    have hR : (boolL1 v₀)⁻¹ * ((t + 1) * boolInner v₀ f) =
        (boolL1 v₀)⁻¹ * boolInner v₀ f * (t + 1) := by ring
    linarith

private theorem continuous_sum_finset' {α β : Type*} [TopologicalSpace α]
    (s : Finset β) {f : β → α → ℝ} (hf : ∀ b ∈ s, Continuous (f b)) :
    Continuous (fun a ↦ ∑ b ∈ s, f b a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert b t hbt ih =>
    simp_rw [Finset.sum_insert hbt]
    exact (hf b (Finset.mem_insert_self b t)).add
      (ih fun c hc ↦ hf c (Finset.mem_insert_of_mem hc))

/-- **the contraction lemma (Strong LP Duality for `α_d(f)`)**:
Whenever `deg_∞(f) ≤ d < n`, `α_d(f) = max_v {(1 + ⟨v, f⟩) / (1 - ⟨v, f⟩): ‖v‖₁ = 1, v ⊥ deg ≤ d}`,
with the maximum attained. -/
theorem minAlphaForDeg_dual {d : ℕ} {f : BitString n → Bool}
    (hinf : inftyApproxDeg f ≤ d) (hdn : d < n) :
    (∀ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0) →
      boolL1 v = 1 →
      boolInner v f < 1 ∧ (1 + boolInner v f) / (1 - boolInner v f) ≤ minAlphaForDeg d f) ∧
    (∃ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0) ∧
      boolL1 v = 1 ∧
      boolInner v f < 1 ∧
      (1 + boolInner v f) / (1 - boolInner v f) = minAlphaForDeg d f) := by
  have hne_primal : {α : ℝ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox α f g}.Nonempty := by
    obtain ⟨g, hg, happrox⟩ := inftyApproxDeg_le_iff.mp hinf
    let M : ℝ := max 1 (∑ x : BitString n, |g x|)
    refine ⟨M, g, hg, fun x ↦ ⟨happrox x, ?_⟩⟩
    have hx : g x * signVal (f x) ≤ |g x| := by
      calc g x * signVal (f x) ≤ |g x * signVal (f x)| := le_abs_self _
        _ = |g x| := by rw [abs_mul, abs_signVal, mul_one]
    have hsum : |g x| ≤ ∑ y : BitString n, |g y| :=
      Finset.single_le_sum (f := fun y : BitString n ↦ |g y|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ x)
    exact hx.trans (hsum.trans (le_max_right _ _))
  have hge1 : 1 ≤ minAlphaForDeg d f := by
    refine le_csInf hne_primal ?_
    rintro α ⟨g, _, happrox⟩
    have hx := happrox (fun _ ↦ false)
    linarith [hx.1, hx.2]
  have hweak : ∀ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0) →
      boolL1 v = 1 →
      boolInner v f < 1 ∧ (1 + boolInner v f) / (1 - boolInner v f) ≤ minAlphaForDeg d f := by
    intro v hv_orth hv_l1
    have hle_α : ∀ α ∈ {α : ℝ | ∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox α f g},
        boolInner v f ≤ (α - 1) / (α + 1) := by
      rintro α ⟨g, hg, happrox⟩
      have hα1 : 1 ≤ α := by have hx := happrox (fun _ ↦ false); linarith [hx.1, hx.2]
      exact boolInner_le_of_isAlphaApprox hα1 hg happrox hv_orth hv_l1
    have ⟨α₀, hα₀⟩ := hne_primal
    have hα₀1 : 1 ≤ α₀ := by
      rcases hα₀ with ⟨_, _, ha⟩; have hx := ha (fun _ ↦ false); linarith [hx.1, hx.2]
    have hlt1 : boolInner v f < 1 := by
      have h1 := hle_α α₀ hα₀
      have h2 : (α₀ - 1) / (α₀ + 1) < 1 := by
        rw [div_lt_one (by linarith : (0 : ℝ) < α₀ + 1)]; linarith
      linarith
    refine ⟨hlt1, le_csInf hne_primal fun α hα ↦ ?_⟩
    have hα1 : 1 ≤ α := by
      rcases hα with ⟨_, _, ha⟩; have hx := ha (fun _ ↦ false); linarith [hx.1, hx.2]
    have h1 := hle_α α hα
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < α + 1)] at h1
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - boolInner v f)]
    linarith
  refine ⟨hweak, ?_⟩
 -- Compactness of the feasible dual set `V_d`:
  let V : Set (BitString n → ℝ) :=
    {v | boolL1 v = 1 ∧ ∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0}
  have hV_closed : IsClosed V := by
    have h1 : IsClosed {v : BitString n → ℝ | boolL1 v = 1} :=
      isClosed_eq (continuous_sum_finset' _ fun x _ ↦ continuous_abs.comp (continuous_apply x))
        continuous_const
    have h2 : IsClosed {v : BitString n → ℝ |
        ∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0} := by
      have heq : {v : BitString n → ℝ |
          ∀ T : Finset (Fin n), T.card ≤ d → BitString.fourierCoeff v T = 0} =
          ⋂ T : {T : Finset (Fin n) // T.card ≤ d},
            {v : BitString n → ℝ | ∑ x : BitString n, v x * chi ℝ T.1 x = 0} := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, fourierCoeff_eq_zero_iff_sum_eq_zero]
        exact ⟨fun h ⟨T, hT⟩ ↦ h T hT, fun h T hT ↦ h ⟨T, hT⟩⟩
      rw [heq]
      exact isClosed_iInter fun T ↦ isClosed_eq
        (continuous_sum_finset' _ fun x _ ↦ (continuous_apply x).mul continuous_const)
        continuous_const
    exact h1.inter h2
  have hV_bdd : Bornology.IsBounded V := by
    refine Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨1, fun v hv ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    have hx : |v x| ≤ boolL1 v :=
      Finset.single_le_sum (f := fun y : BitString n ↦ |v y|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ x)
    simpa [hv.1] using hx
  have hV_compact : IsCompact V := Metric.isCompact_of_isClosed_isBounded hV_closed hV_bdd
 -- Nonemptiness of `V_d`: since `d < n`, `2^{-n} χ_{univ} ∈ V_d`.
  let v_top : BitString n → ℝ := fun x ↦ ((2 : ℝ) ^ n)⁻¹ * chi ℝ Finset.univ x
  have hv_top_mem : v_top ∈ V := by
    refine ⟨?_, ?_⟩
    · unfold boolL1
      have hterms : ∀ x : BitString n, |v_top x| = ((2 : ℝ) ^ n)⁻¹ := fun x ↦ by
        dsimp only [v_top]
        rw [abs_mul, abs_chi, mul_one, abs_of_pos (by positivity)]
      simp_rw [hterms, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      exact mul_inv_cancel₀ (by positivity)
    · intro T hT
      rw [fourierCoeff_eq_zero_iff_sum_eq_zero]
      have hne : T ≠ Finset.univ := fun heq ↦ by
        have := congrArg Finset.card heq
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      have hexp : ∑ x : BitString n, v_top x * chi ℝ T x =
          BitString.fourierCoeff (chi ℝ Finset.univ) T := by
        rw [BitString.fourierCoeff_eq_sum]
        simp only [Fintype.card_fin, div_eq_inv_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by dsimp only [v_top]; ring
      rw [hexp, fourierCoeff_chi, ite_eq_right hne.symm]
  have hcont : Continuous (fun v : BitString n → ℝ ↦ boolInner v f) :=
    continuous_sum_finset' _ fun x _ ↦ (continuous_apply x).mul continuous_const
  obtain ⟨v₀, hv₀_mem, hv₀_max⟩ := hV_compact.exists_isMaxOn ⟨v_top, hv_top_mem⟩ hcont.continuousOn
  have hweak₀ := hweak v₀ hv₀_mem.2 hv₀_mem.1
  refine ⟨v₀, hv₀_mem.2, hv₀_mem.1, hweak₀.1, le_antisymm hweak₀.2 ?_⟩
  by_cases hα1 : minAlphaForDeg d f = 1
  · have hneg_mem : (fun x ↦ -v₀ x) ∈ V := by
      refine ⟨?_, ?_⟩
      · unfold boolL1; simp_rw [abs_neg]; exact hv₀_mem.1
      · intro T hT
        rw [fourierCoeff_eq_zero_iff_sum_eq_zero]
        have h0 := (fourierCoeff_eq_zero_iff_sum_eq_zero v₀ T).mp (hv₀_mem.2 T hT)
        simp_rw [neg_mul, Finset.sum_neg_distrib, h0, neg_zero]
    have hneg_inner : boolInner (fun x ↦ -v₀ x) f = -boolInner v₀ f := by
      unfold boolInner; simp_rw [neg_mul, Finset.sum_neg_distrib]
    have hge0 : 0 ≤ boolInner v₀ f := by
      have hmax : boolInner (fun x ↦ -v₀ x) f ≤ boolInner v₀ f := hv₀_max hneg_mem
      linarith
    rw [hα1, le_div_iff₀ (by linarith [hweak₀.1])]
    linarith
  · have hα_gt1 : 1 < minAlphaForDeg d f := lt_of_le_of_ne hge1 (Ne.symm hα1)
    have hge_inner : (minAlphaForDeg d f - 1) / (minAlphaForDeg d f + 1) ≤ boolInner v₀ f := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      let δ := min ((minAlphaForDeg d f - 1) / 2) ε
      have hδ_pos : 0 < δ := lt_min (by linarith) hε
      let t := minAlphaForDeg d f - δ
      have ht1 : 1 ≤ t := by
        have : δ ≤ (minAlphaForDeg d f - 1) / 2 := min_le_left _ _
        linarith
      have ht_lt : t < minAlphaForDeg d f := by linarith
      have hno : ¬∃ g ∈ lowDegree ℝ (Fin n) d, IsAlphaApprox t f g := by
        rintro ⟨g, hg, happrox⟩
        have hle : minAlphaForDeg d f ≤ t :=
          csInf_le ⟨1, fun α ⟨_, _, ha⟩ ↦ by
            have hx := ha (fun _ ↦ false); linarith [hx.1, hx.2]⟩ ⟨g, hg, happrox⟩
        linarith
      obtain ⟨v₁, hv₁_orth, hv₁_l1, hv₁_gt⟩ := exists_dual_gt_of_no_alphaApprox ht1 hno
      have hv₁_le : boolInner v₁ f ≤ boolInner v₀ f := hv₀_max ⟨hv₁_l1, hv₁_orth⟩
      have hdiff : (minAlphaForDeg d f - 1) / (minAlphaForDeg d f + 1) - (t - 1) / (t + 1) ≤ ε := by
        have hpos1 : 0 < minAlphaForDeg d f + 1 := by linarith
        have hpos2 : 0 < t + 1 := by linarith
        have hident : (minAlphaForDeg d f - 1) / (minAlphaForDeg d f + 1) - (t - 1) / (t + 1) =
            2 * δ / ((minAlphaForDeg d f + 1) * (t + 1)) := by
          field_simp [hpos1.ne', hpos2.ne']
          dsimp only [t]
          ring
        rw [hident, div_le_iff₀ (mul_pos hpos1 hpos2)]
        have hδ_le : δ ≤ ε := min_le_right _ _
        have hprod_ge : (2 : ℝ) ≤ (minAlphaForDeg d f + 1) * (t + 1) := by nlinarith
        nlinarith
      linarith
    rw [le_div_iff₀ (by linarith [hweak₀.1])]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < minAlphaForDeg d f + 1)] at hge_inner
    linarith

/-- **repaired finite-`α` form**:
For `f: BitString n → Bool`, `1 ≤ α`, and `d = alphaApproxDeg α f`, there exists `v` such that:
1. `fourierCoeff v T = 0` for all `|T| < d`,
2. `‖v‖₁ = 1`,
3. `⟨v, f⟩ ≥ (α - 1) / (α + 1)`. -/
theorem exists_dual_polynomial_finite {α : ℝ} (hα : 1 ≤ α) (f : BitString n → Bool) :
    ∃ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card < alphaApproxDeg α f → BitString.fourierCoeff v T = 0) ∧
      boolL1 v = 1 ∧
      (α - 1) / (α + 1) ≤ boolInner v f := by
  rcases Nat.eq_zero_or_pos (alphaApproxDeg α f) with hd0 | hdpos
  · -- When `d = 0`, a point mass at `fun _ ↦ false` gives `⟨v, f⟩ = 1 ≥ (α - 1) / (α + 1)`.
    let x₀ : BitString n := fun _ ↦ false
    refine ⟨fun x ↦ if x = x₀ then signVal (f x₀) else 0,
      fun _ hT ↦ by omega, ?_, ?_⟩
    · unfold boolL1
      rw [Finset.sum_eq_single x₀]
      · simp
      · intro x _ hne; simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · have hinner : boolInner (fun x ↦ if x = x₀ then signVal (f x₀) else 0) f = 1 := by
        unfold boolInner
        rw [Finset.sum_eq_single x₀]
        · simp [signVal_mul_self]
        · intro x _ hne; simp [hne]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [hinner, div_le_one (by linarith : (0 : ℝ) < α + 1)]
      linarith
  · let d' := alphaApproxDeg α f - 1
    have hd'_lt_n : d' < n := by
      have hle := alphaApproxDeg_le_card hα f
      omega
    by_cases hinf : d' < inftyApproxDeg f
    · obtain ⟨v, hv_orth, hv_l1, hv_sgn⟩ := exists_dual_infty_of_lt_inftyApproxDeg hinf
      refine ⟨v, fun T hT ↦ hv_orth T (by omega), hv_l1, ?_⟩
      have hinner : boolInner v f = 1 := by
        calc boolInner v f = boolL1 v := by
              unfold boolInner boolL1
              refine Finset.sum_congr rfl fun x _ ↦ ?_
              have habs : |v x * signVal (f x)| = |v x| := by rw [abs_mul, abs_signVal, mul_one]
              rw [← habs, abs_of_nonneg (hv_sgn x)]
          _ = 1 := hv_l1
      rw [hinner, div_le_one (by linarith : (0 : ℝ) < α + 1)]
      linarith
    · have hinf_le : inftyApproxDeg f ≤ d' := Nat.le_of_not_lt hinf
      obtain ⟨v, hv_orth, hv_l1, hv_lt1, hv_eq⟩ := (minAlphaForDeg_dual hinf_le hd'_lt_n).2
      have hα_le : α ≤ minAlphaForDeg d' f := by
        refine le_csInf ?_ ?_
        · obtain ⟨g, hg, happrox⟩ := inftyApproxDeg_le_iff.mp hinf_le
          refine ⟨max 1 (∑ x : BitString n, |g x|), g, hg, fun x ↦ ⟨happrox x, ?_⟩⟩
          have hx : g x * signVal (f x) ≤ |g x| := by
            calc g x * signVal (f x) ≤ |g x * signVal (f x)| := le_abs_self _
              _ = |g x| := by rw [abs_mul, abs_signVal, mul_one]
          exact hx.trans ((Finset.single_le_sum (f := fun y : BitString n ↦ |g y|)
            (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ x)).trans (le_max_right _ _))
        · rintro β ⟨g, hg, happrox⟩
          by_contra hlt
          push Not at hlt
          have hle_deg : alphaApproxDeg α f ≤ d' :=
            alphaApproxDeg_le_iff hα |>.mpr
              ⟨g, hg, fun x ↦ ⟨(happrox x).1, (happrox x).2.trans hlt.le⟩⟩
          omega
      refine ⟨v, fun T hT ↦ hv_orth T (by omega), hv_l1, ?_⟩
      rw [← hv_eq, le_div_iff₀ (by linarith)] at hα_le
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < α + 1)]
      linarith

/-- **repaired `α = ∞` form**:
For `f: BitString n → Bool` and `d = inftyApproxDeg f`, there exists `v` such that:
1. `fourierCoeff v T = 0` for all `|T| < d`,
2. `‖v‖₁ = 1`,
3. `v(x) f(x) ≥ 0` for all `x`. -/
theorem exists_dual_polynomial_infty (f : BitString n → Bool) :
    ∃ v : BitString n → ℝ,
      (∀ T : Finset (Fin n), T.card < inftyApproxDeg f → BitString.fourierCoeff v T = 0) ∧
      boolL1 v = 1 ∧
      (∀ x : BitString n, 0 ≤ v x * signVal (f x)) := by
  rcases Nat.eq_zero_or_pos (inftyApproxDeg f) with hd0 | hdpos
  · let x₀ : BitString n := fun _ ↦ false
    refine ⟨fun x ↦ if x = x₀ then signVal (f x₀) else 0,
      fun _ hT ↦ by omega, ?_, fun x ↦ ?_⟩
    · unfold boolL1
      rw [Finset.sum_eq_single x₀]
      · simp
      · intro x _ hne; simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · dsimp only
      split_ifs with hx
      · subst hx; rw [signVal_mul_self]; norm_num
      · simp
  · obtain ⟨v, hv_orth, hv_l1, hv_sgn⟩ :=
      exists_dual_infty_of_lt_inftyApproxDeg (d := inftyApproxDeg f - 1) (f := f) (by omega)
    exact ⟨v, fun T hT ↦ hv_orth T (by omega), hv_l1, hv_sgn⟩

end DualPolynomials

end CslibFrontier.Computability.QueryComplexity
