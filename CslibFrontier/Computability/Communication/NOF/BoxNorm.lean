/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Communication.NOF.Cube
public import CslibFrontier.Computability.Communication.NOF.Leaf
public import CslibFrontier.Computability.Communication.NOF.Protocol
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gowers Box Norm and Viola–Wigderson NOF Protocol Correlation Bound

Defines the real-valued Gowers box norm `‖f‖_□` (`boxNormPow`, `boxNorm`) over finite product
domains `∀ i : ι, X i`, derives the Cauchy–Schwarz cube correlation bound from
`Cslib.Communication.NOF.pow_expect_mul_prod_le`, and proves the Viola–Wigderson
correlation inequality for any `k`-party deterministic NOF protocol `P : Protocol X Bool` of depth
at most `c`:

`|E_x [w(P.run x) · d(x)]| ≤ 2^c · ‖d‖_□`

for every bounded weight `|w(b)| ≤ 1` (in particular `w ∈ {±1}` and `w ∈ {0, 1}`).

## Main definitions

* `Cslib.Communication.NOF.boxNormPow`: the `2 ^ |ι|`-th power of the Gowers box norm.
* `Cslib.Communication.NOF.boxNorm`: the Gowers box norm `‖f‖_□`.

## Main results

* `Cslib.Communication.NOF.abs_avg_mul_prod_le_boxNorm`: cube Cauchy–Schwarz bound for products of
  single-coordinate-independent bounded functions.
* `Cslib.Communication.NOF.abs_avg_mul_protocol_le_boxNorm`: Viola–Wigderson NOF protocol
  correlation bound (`w : Bool → ℝ`, `|w b| ≤ 1`).
* `Cslib.Communication.NOF.abs_avg_indicator_protocol_le_boxNorm`: indicator specialization
  (`P.run x = true`).
-/

public section

namespace Cslib.Communication.NOF

open scoped BigOperators

/-- The `2 ^ |ι|`-th power of the Gowers box norm of `f : (∀ i, X i) → ℝ`. -/
noncomputable def boxNormPow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) : ℝ :=
  ((Fintype.card (∀ i, X i) : ℝ) ^ 2)⁻¹ *
    ∑ x₀ : ∀ i, X i, ∑ x₁ : ∀ i, X i,
      ∏ ω : ι → Bool, f (fun i ↦ if ω i then x₁ i else x₀ i)

/-- Explicit average-of-products formula for `boxNormPow`. -/
theorem boxNormPow_eq_avg_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) :
    boxNormPow f =
      ((Fintype.card (∀ i, X i) : ℝ) ^ 2)⁻¹ *
        ∑ x₀ : ∀ i, X i, ∑ x₁ : ∀ i, X i,
          ∏ ω : ι → Bool, f (fun i ↦ if ω i then x₁ i else x₀ i) := by
  unfold boxNormPow; rfl

private lemma boxNormPow_eq_expect_cube {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) :
    boxNormPow f =
      𝔼 x₀ : ∀ i, X i, 𝔼 x₁ : ∀ i, X i,
        ∏ S ∈ (Finset.univ : Finset ι).powerset, f (S.piecewise x₁ x₀) := by
  rw [boxNormPow_eq_avg_prod]
  simp only [Fintype.expect_eq_sum_div_card, Finset.powerset_univ]
  have hprod : ∀ x₀ x₁ : ∀ i, X i,
      (∏ ω : ι → Bool, f (fun i ↦ if ω i then x₁ i else x₀ i)) =
        ∏ S : Finset ι, f (S.piecewise x₁ x₀) := fun x₀ x₁ ↦ by
    let e : (ι → Bool) ≃ Finset ι :=
      { toFun := fun ω ↦ Finset.univ.filter fun i ↦ ω i = true
        invFun := fun S i ↦ decide (i ∈ S)
        left_inv := fun ω ↦ funext fun i ↦ by cases h : ω i <;> simp [h]
        right_inv := fun S ↦ by ext i; simp }
    refine Fintype.prod_equiv e _ _ fun ω ↦ congrArg f (funext fun i ↦ ?_)
    by_cases h : ω i = true <;> simp [e, Finset.piecewise, h]
  simp_rw [hprod, ← Finset.sum_div, div_div, ← sq, div_eq_inv_mul]

/-- The Gowers box norm `‖f‖_□` of `f : (∀ i, X i) → ℝ`. -/
noncomputable def boxNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) : ℝ :=
  boxNormPow f ^ ((2 ^ Fintype.card ι : ℕ) : ℝ)⁻¹

/-- Gowers–Cauchy–Schwarz correlation inequality: if `g i` does not depend on coordinate `i` and
satisfies `|g i x| ≤ 1`, then `|E_x [f x * ∏ i, g i x]| ≤ ‖f‖_□` and `0 ≤ boxNormPow f`. -/
theorem abs_avg_mul_prod_le_boxNorm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ)
    (g : ι → (∀ j, X j) → ℝ)
    (hg : ∀ i x e, g i (Function.update x i e) = g i x)
    (hg1 : ∀ i x, |g i x| ≤ 1) :
    |(Fintype.card (∀ i, X i) : ℝ)⁻¹ * ∑ x, f x * ∏ i, g i x| ≤ boxNorm f ∧
      0 ≤ boxNormPow f := by
  have hcube := pow_expect_mul_prod_le (Finset.univ : Finset ι) f g
    (fun i _ ↦ hg i) (fun i _ ↦ hg1 i)
  rw [Finset.card_univ, ← boxNormPow_eq_expect_cube] at hcube
  have heven : Even (2 ^ Fintype.card ι) :=
    (Nat.even_pow' Fintype.card_ne_zero).mpr even_two
  have hpow_nn : 0 ≤ (𝔼 x, f x * ∏ i : ι, g i x) ^ (2 ^ Fintype.card ι) :=
    heven.pow_nonneg _
  have hrb_nn : 0 ≤ boxNormPow f := hpow_nn.trans hcube
  refine ⟨?_, hrb_nn⟩
  have havg : (Fintype.card (∀ i, X i) : ℝ)⁻¹ * ∑ x : ∀ i, X i, f x * ∏ i : ι, g i x =
      𝔼 x, f x * ∏ i : ι, g i x := by
    rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul]
  rw [havg]
  have habs_pow : |𝔼 x, f x * ∏ i : ι, g i x| ^ (2 ^ Fintype.card ι) ≤
      boxNorm f ^ (2 ^ Fintype.card ι) := by
    rw [heven.pow_abs, boxNorm,
      Real.rpow_inv_natCast_pow hrb_nn (pow_ne_zero _ two_ne_zero)]
    exact hcube
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ two_ne_zero)
    (Real.rpow_nonneg hrb_nn _) habs_pow

/-- Nonnegativity of `boxNormPow f` on any nonempty index type. -/
theorem boxNormPow_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) :
    0 ≤ boxNormPow f :=
  (abs_avg_mul_prod_le_boxNorm f (fun _ _ ↦ 1) (fun _ _ _ ↦ rfl)
    (fun _ _ ↦ by norm_num)).2

/-- Nonnegativity of `boxNorm f`. -/
theorem boxNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) :
    0 ≤ boxNorm f :=
  Real.rpow_nonneg (boxNormPow_nonneg f) _

/-- `boxNorm f ^ (2 ^ |ι|) = boxNormPow f`. -/
theorem boxNorm_pow_two_pow {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (f : (∀ i, X i) → ℝ) :
    boxNorm f ^ (2 ^ Fintype.card ι) = boxNormPow f := by
  unfold boxNorm
  exact Real.rpow_inv_natCast_pow (boxNormPow_nonneg f) (pow_ne_zero _ two_ne_zero)

/-- **Viola–Wigderson**: for any `k`-party (`1 ≤ k`) deterministic NOF protocol `P`
of depth at most `c`, any bounded output weight `w : Bool → ℝ` (`|w b| ≤ 1`), and any
`d : (∀ i, X i) → ℝ`, `|E_x [w(P.run x) * d(x)]| ≤ 2^c * ‖d‖_□`.
-/
theorem abs_avg_mul_protocol_le_boxNorm {k c : ℕ} (hk : 1 ≤ k) {X : Fin k → Type*}
    [∀ i, Fintype (X i)] (P : Protocol X Bool) (hP : P.depth ≤ c) (w : Bool → ℝ)
    (hw : ∀ b, |w b| ≤ 1) (d : (∀ i, X i) → ℝ) :
    |(Fintype.card (∀ i, X i) : ℝ)⁻¹ * ∑ x, w (P.run x) * d x| ≤ (2 : ℝ) ^ c * boxNorm d := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let leafOut : Fin P.leafCount → Bool := fun l ↦
    if h : ∃ x : ∀ i, X i, P.leaf x = l then P.run h.choose else false
  have hrun_leaf : ∀ (x : ∀ i, X i) (l : Fin P.leafCount), P.leaf x = l →
      P.run x = leafOut l := fun x l hx ↦ by
    have hex : ∃ y : ∀ i, X i, P.leaf y = l := ⟨x, hx⟩
    simp only [leafOut, hex, ↓reduceDIte]
    exact P.run_eq_of_leaf_eq (hx.trans hex.choose_spec.symm)
  have hpart : ∀ x : ∀ i, X i, w (P.run x) =
      ∑ l : Fin P.leafCount, if P.leaf x = l then w (leafOut l) else 0 := fun x ↦ by
    rw [Finset.sum_eq_single (P.leaf x)]
    · simp [hrun_leaf x (P.leaf x) rfl]
    · intro l _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  have hsum_eq : (Fintype.card (∀ i, X i) : ℝ)⁻¹ * ∑ x, w (P.run x) * d x =
      ∑ l : Fin P.leafCount, w (leafOut l) *
        ((Fintype.card (∀ i, X i) : ℝ)⁻¹ *
          ∑ x, d x * (if P.leaf x = l then (1 : ℝ) else 0)) := by
    simp_rw [hpart, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> ring
  have hfiber : ∀ l : Fin P.leafCount,
      |(Fintype.card (∀ i, X i) : ℝ)⁻¹ *
          ∑ x, d x * (if P.leaf x = l then (1 : ℝ) else 0)| ≤ boxNorm d := fun l ↦ by
    obtain ⟨φ, hφ⟩ := isCylinderIntersection_iff.mp (P.isCylinderIntersection_leaf l)
    let g : Fin k → (∀ j, X j) → ℝ := fun i x ↦
      if φ i (view i x) = true then 1 else 0
    have hg : ∀ i x e, g i (Function.update x i e) = g i x := fun i x e ↦ by
      simp [g, view_update_self]
    have hg1 : ∀ i x, |g i x| ≤ 1 := fun i x ↦ by dsimp only [g]; split_ifs <;> norm_num
    have hprod : ∀ x : ∀ i, X i,
        (∏ i : Fin k, g i x) = if P.leaf x = l then (1 : ℝ) else 0 := fun x ↦ by
      have hmem : P.leaf x = l ↔ ∀ i, φ i (view i x) = true := by
        have h := Set.ext_iff.mp hφ x
        simpa [mem_cylinderIntersection] using h
      by_cases hx : P.leaf x = l
      · simp only [hx, ↓reduceIte]
        exact Finset.prod_eq_one fun i _ ↦ by simp [g, hmem.mp hx i]
      · simp only [hx, ↓reduceIte]
        have hnot := mt hmem.mpr hx
        rw [not_forall] at hnot
        obtain ⟨i, hi⟩ := hnot
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hi])
    simp_rw [← hprod]
    exact (abs_avg_mul_prod_le_boxNorm d g hg hg1).1
  rw [hsum_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l : Fin P.leafCount,
          |w (leafOut l) * ((Fintype.card (∀ i, X i) : ℝ)⁻¹ *
            ∑ x, d x * (if P.leaf x = l then (1 : ℝ) else 0))|
      ≤ ∑ _l : Fin P.leafCount, 1 * boxNorm d := by
        refine Finset.sum_le_sum fun l _ ↦ ?_
        rw [abs_mul]
        exact mul_le_mul (hw _) (hfiber l) (abs_nonneg _) zero_le_one
    _ = (P.leafCount : ℝ) * boxNorm d := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ c * boxNorm d := by
        refine mul_le_mul_of_nonneg_right ?_ (boxNorm_nonneg d)
        have hlc : P.leafCount ≤ 2 ^ c :=
          P.leafCount_le_two_pow_depth.trans (Nat.pow_le_pow_right (by decide) hP)
        exact_mod_cast hlc

/-- Indicator form of Viola–Wigderson for deterministic NOF protocols. -/
theorem abs_avg_indicator_protocol_le_boxNorm {k c : ℕ} (hk : 1 ≤ k) {X : Fin k → Type*}
    [∀ i, Fintype (X i)] (P : Protocol X Bool) (hP : P.depth ≤ c) (d : (∀ i, X i) → ℝ) :
    |(Fintype.card (∀ i, X i) : ℝ)⁻¹ * ∑ x, (if P.run x = true then (1 : ℝ) else 0) * d x| ≤
      (2 : ℝ) ^ c * boxNorm d :=
  abs_avg_mul_protocol_le_boxNorm hk P hP (fun b ↦ if b = true then 1 else 0)
    (fun b ↦ by cases b <;> norm_num) d

end Cslib.Communication.NOF
