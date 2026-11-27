/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.BooleanAnalysis.ParitySpace
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Nat.Log

import CslibFrontier.Foundations.BooleanAnalysis.FourierBitVal
import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct
import CslibFrontier.Foundations.BooleanAnalysis.UncertaintyPrinciple
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fourier-Analytic Measures, Granularity, and Algebraic Degree of Boolean Functions

This module develops reusable Fourier-analytic invariants of Boolean functions
`f : (ι → Bool) → Bool` over arbitrary finite index types `ι`, proved under standard Lean axioms on
top of `Cslib.BitString.fourierCoeff` and `CslibFrontier.Foundations.BooleanAnalysis.ParitySpace`:

* Fourier support, Fourier sparsity, spectral (`ℓ₁`) norm, Boolean weight `δ(f) = Pr[f(x) = true]`,
  Fourier rank `r(f)`, threshold spectra `largeSpectrum`, `𝔽₂`-polynomial degree `f2Degree`, and
  bent Boolean functions `IsBent` (including `innerProductBent`);
* invariance of Boolean weight, Fourier sparsity, and `𝔽₂`-degree under invertible Fourier basis
  changes `fourierBasisChange`;
* the granularity theorem of Gopalan, O'Donnell, Servedio, Shpilka, and Wimmer: every
  Fourier coefficient of a Boolean function with Fourier sparsity `k ≥ 2` is an integer multiple of
  `2 ^ (1 - ⌊log₂ k⌋)`;
* the Bernasconi–Codenotti bound `2 ^ deg_{𝔽₂}(f) ≤ k(f)` (hence `deg_{𝔽₂}(f) ≤ log₂ k(f)`)
  for Boolean functions with `k(f) > 1`;
* the weighted spectral-norm bound `‖f̂‖₁ ≤ 3 √(k(f) δ(f))` for Boolean functions with `0 < δ(f)`.

## Main definitions

* `CslibFrontier.BooleanFunction.fourierSupport`, `CslibFrontier.BooleanFunction.fourierSparsity`,
  `CslibFrontier.BooleanFunction.spectralNorm`: Fourier support, sparsity, and spectral norm of
  `f : (ι → Bool) → ℝ`.
* `CslibFrontier.BooleanFunction.boolFourierCoeff`, `CslibFrontier.BooleanFunction.boolWeight`,
  `CslibFrontier.BooleanFunction.boolSupport`, `CslibFrontier.BooleanFunction.boolSparsity`,
  `CslibFrontier.BooleanFunction.boolNonemptySparsity`,
  `CslibFrontier.BooleanFunction.boolSpectralNorm`,
  `CslibFrontier.BooleanFunction.fourierRank`, `CslibFrontier.BooleanFunction.largeSpectrum`,
  `CslibFrontier.BooleanFunction.f2Degree`: Fourier-analytic measures of `f : (ι → Bool) → Bool`.
* `CslibFrontier.BooleanFunction.fourierBasisChange`: invertible basis change on the Fourier domain.
* `CslibFrontier.BooleanFunction.IsBent`, `CslibFrontier.BooleanFunction.innerProductBent`: bent
  Boolean
  functions and the canonical inner-product bent function on `2 * s` bits.

## Main results

* `CslibFrontier.BooleanFunction.f2Degree_fourierBasisChange`: `deg_{𝔽₂}(f_B) = deg_{𝔽₂}(f)` for
  every
  invertible `B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)`.
* `CslibFrontier.BooleanFunction.exists_int_mul_boolFourierCoeff`: Fourier granularity
  `2 ^ (1 - ⌊log₂ k⌋)` for `k(f) ≥ 2`.
* `CslibFrontier.BooleanFunction.two_div_boolSparsity_le_abs_boolFourierCoeff`: `2 / k(f) ≤ |f̂(S)|`
  for
  every `S ∈ supp(f)` when `k(f) ≥ 2`.
* `CslibFrontier.BooleanFunction.two_pow_f2Degree_le_boolSparsity`,
  `CslibFrontier.BooleanFunction.f2Degree_le_logb_boolSparsity`: `2 ^ deg_{𝔽₂}(f) ≤ k(f)` and
  `deg_{𝔽₂}(f) ≤ log₂ k(f)` when `k(f) > 1`.
* `CslibFrontier.BooleanFunction.boolSpectralNorm_le_three_mul_sqrt`: `‖f̂‖₁ ≤ 3 √(k(f) δ(f))` when
  `0 < δ(f)`.
-/

public section

namespace CslibFrontier.BooleanFunction

open Cslib Cslib.BitString Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fourier support `{S ⊆ ι : f̂(S) ≠ 0}` of `f : (ι → Bool) → ℝ`. -/
@[expose]
noncomputable def fourierSupport (f : (ι → Bool) → ℝ) : Finset (Finset ι) :=
  univ.filter fun S ↦ fourierCoeff f S ≠ 0

/-- Fourier sparsity `|supp(f)|` of `f : (ι → Bool) → ℝ`. -/
@[expose]
noncomputable def fourierSparsity (f : (ι → Bool) → ℝ) : ℕ :=
  #(fourierSupport f)

/-- Fourier spectral (`ℓ₁`) norm `∑ S, |f̂(S)|` of `f : (ι → Bool) → ℝ`. -/
@[expose]
noncomputable def spectralNorm (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S : Finset ι, |fourierCoeff f S|

/-- Membership in `fourierSupport`. -/
@[simp]
theorem mem_fourierSupport {f : (ι → Bool) → ℝ} {S : Finset ι} :
    S ∈ fourierSupport f ↔ fourierCoeff f S ≠ 0 := by
  simp [fourierSupport]

/-- The spectral norm is nonnegative. -/
theorem spectralNorm_nonneg (f : (ι → Bool) → ℝ) : 0 ≤ spectralNorm f :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Walsh–Fourier expansion restricted to `fourierSupport f`. -/
theorem fourierExpansion_on_support (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    f x = ∑ S ∈ fourierSupport f, fourierCoeff f S * chi ℝ S x := by
  rw [← sum_fourierCoeff_mul_chi f x]
  symm
  refine sum_subset (subset_univ _) fun S _ hS ↦ ?_
  simp only [mem_fourierSupport, not_not] at hS
  simp [hS]

/-- Every nonzero real-valued function on the Boolean cube has positive Fourier sparsity. -/
theorem fourierSparsity_pos_of_ne_zero {f : (ι → Bool) → ℝ} (hf : f ≠ 0) :
    0 < fourierSparsity f := by
  rw [fourierSparsity, card_pos]
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  apply hf
  ext x
  rw [fourierExpansion_on_support f x, h, sum_empty]
  rfl

/-- **Uncertainty principle** on the Boolean cube: any nonzero `f : (ι → Bool) → ℝ` is nonzero on
at least a `1 / k(f)` fraction of inputs. -/
theorem uncertainty_principle {f : (ι → Bool) → ℝ} (hf : f ≠ 0) :
    (1 : ℝ) / fourierSparsity f ≤ (dens {x : ι → Bool | f x ≠ 0} : ℝ) := by
  have hpos : (0 : ℝ) < fourierSparsity f := Nat.cast_pos.2 (fourierSparsity_pos_of_ne_zero hf)
  rw [div_le_iff₀ hpos]
  exact one_le_dens_mul_card_fourierCoeff_ne_zero hf

/-- Walsh–Fourier coefficient `f̂(S) = 𝔼 x, signVal (f x) * χ_S(x)` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def boolFourierCoeff (f : (ι → Bool) → Bool) (S : Finset ι) : ℝ :=
  fourierCoeff (fun x ↦ signVal (f x)) S

/-- Boolean weight `δ(f) = Pr_x[f(x) = true] = Pr_x[signVal (f x) = -1]`. -/
@[expose]
noncomputable def boolWeight (f : (ι → Bool) → Bool) : ℝ :=
  (dens {x : ι → Bool | f x = true} : ℝ)

/-- Fourier support `{S ⊆ ι : f̂(S) ≠ 0}` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def boolSupport (f : (ι → Bool) → Bool) : Finset (Finset ι) :=
  fourierSupport fun x ↦ signVal (f x)

/-- Fourier sparsity `k(f) = |supp(f)|` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def boolSparsity (f : (ι → Bool) → Bool) : ℕ :=
  fourierSparsity fun x ↦ signVal (f x)

/-- Non-empty Fourier sparsity `|{S ≠ ∅ : f̂(S) ≠ 0}|` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def boolNonemptySparsity (f : (ι → Bool) → Bool) : ℕ :=
  #((boolSupport f).erase ∅)

/-- Fourier spectral (`ℓ₁`) norm `‖f̂‖₁ = ∑ S, |f̂(S)|` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def boolSpectralNorm (f : (ι → Bool) → Bool) : ℝ :=
  spectralNorm fun x ↦ signVal (f x)

/-- Fourier rank `r(f) = dim_{𝔽₂}(span(supp(f)))` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def fourierRank (f : (ι → Bool) → Bool) : ℕ :=
  parityDim (boolSupport f)

/-- Threshold spectrum `𝒮_t(f) = {S ⊆ ι : |f̂(S)| ≥ 1 / t}` of `f : (ι → Bool) → Bool`. -/
@[expose]
noncomputable def largeSpectrum (f : (ι → Bool) → Bool) (t : ℝ) : Finset (Finset ι) :=
  univ.filter fun S ↦ 1 / t ≤ |boolFourierCoeff f S|

/-- Algebraic degree `deg_{𝔽₂}(f)` of the unique multilinear `𝔽₂`-polynomial representing `f`. -/
@[expose]
noncomputable def f2Degree (f : (ι → Bool) → Bool) : ℕ :=
  totalDegree fun x ↦ bitVal (ZMod 2) (f x)

/-- A Boolean function is **bent** if all of its Fourier coefficients have equal magnitude. -/
@[expose]
def IsBent (f : (ι → Bool) → Bool) : Prop :=
  ∀ S T : Finset ι, |boolFourierCoeff f S| = |boolFourierCoeff f T|

/-- Membership in `boolSupport f`. -/
@[simp]
theorem mem_boolSupport {f : (ι → Bool) → Bool} {S : Finset ι} :
    S ∈ boolSupport f ↔ boolFourierCoeff f S ≠ 0 := by
  simp [boolSupport, boolFourierCoeff]

/-- Cardinality of `boolSupport f` equals `boolSparsity f`. -/
theorem card_boolSupport (f : (ι → Bool) → Bool) : #(boolSupport f) = boolSparsity f := by
  rfl

/-- `boolNonemptySparsity f` equals `#((boolSupport f).erase ∅)`. -/
theorem card_erase_empty_boolSupport (f : (ι → Bool) → Bool) :
    #((boolSupport f).erase ∅) = boolNonemptySparsity f := by
  rfl

/-- `parityDim (boolSupport f)` equals `fourierRank f`. -/
theorem parityDim_boolSupport (f : (ι → Bool) → Bool) :
    parityDim (boolSupport f) = fourierRank f :=
  rfl

/-- Sum of Fourier coefficient magnitudes equals `boolSpectralNorm f`. -/
theorem sum_abs_boolFourierCoeff (f : (ι → Bool) → Bool) :
    ∑ S : Finset ι, |boolFourierCoeff f S| = boolSpectralNorm f :=
  rfl

/-- Expectation formula for `boolFourierCoeff f S`. -/
theorem boolFourierCoeff_eq_expect (f : (ι → Bool) → Bool) (S : Finset ι) :
    boolFourierCoeff f S = 𝔼 x : ι → Bool, signVal (f x) * chi ℝ S x :=
  rfl

/-- Normalized sum formula for `boolFourierCoeff f S`. -/
theorem boolFourierCoeff_eq_sum (f : (ι → Bool) → Bool) (S : Finset ι) :
    boolFourierCoeff f S =
      (∑ x : ι → Bool, signVal (f x) * chi ℝ S x) / (2 : ℝ) ^ Fintype.card ι :=
  fourierCoeff_eq_sum (fun x ↦ signVal (f x)) S

/-- Fourier coefficients of a constant Boolean function. -/
theorem boolFourierCoeff_const (v : Bool) (S : Finset ι) :
    boolFourierCoeff (fun _ : ι → Bool ↦ v) S = if S = ∅ then signVal v else 0 := by
  have hcs : (fun _ : ι → Bool ↦ signVal v) = fun x ↦ signVal v * chi ℝ ∅ x := by ext x; simp
  rw [boolFourierCoeff, hcs, fourierCoeff_const_mul, fourierCoeff_chi]
  by_cases h : S = ∅
  · subst h; simp
  · simp [Ne.symm h, h]

/-- Fourier coefficients of a parity function `x ↦ v ^^ parityOn T x`. -/
theorem boolFourierCoeff_const_xor_parityOn (v : Bool) (T S : Finset ι) :
    boolFourierCoeff (fun x : ι → Bool ↦ v ^^ parityOn T x) S =
      if T = S then signVal v else 0 := by
  have hcs : (fun x : ι → Bool ↦ signVal (v ^^ parityOn T x)) =
      fun x ↦ signVal v * chi ℝ T x := by ext x; rw [signVal_xor, chi_eq_signVal_parityOn]
  rw [boolFourierCoeff, hcs, fourierCoeff_const_mul, fourierCoeff_chi]
  by_cases h : T = S <;> simp [h]

/-- Fourier coefficients of the indicator `x ↦ decide (x = a)`. -/
theorem boolFourierCoeff_decide_eq (a : ι → Bool) (S : Finset ι) :
    boolFourierCoeff (fun x : ι → Bool ↦ decide (x = a)) S =
      (if S = ∅ then (1 : ℝ) else 0) - 2 * (chi ℝ S a / (2 : ℝ) ^ Fintype.card ι) :=
  fourierCoeff_signVal_decide_eq a S

/-- Translation rule `boolFourierCoeff (f (· + a)) S = χ_S(a) * boolFourierCoeff f S`. -/
theorem boolFourierCoeff_comp_add (f : (ι → Bool) → Bool) (a : ι → Bool) (S : Finset ι) :
    boolFourierCoeff (fun x ↦ f (x + a)) S = chi ℝ S a * boolFourierCoeff f S :=
  fourierCoeff_comp_add (fun x ↦ signVal (f x)) a S

/-- Pullback of `boolFourierCoeff` along an `𝔽₂`-linear map `A`. -/
theorem boolFourierCoeff_comp_applyF2Linear {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (f : (ι → Bool) → Bool) (U : Finset κ) :
    boolFourierCoeff (fun y ↦ f (applyF2Linear A y)) U =
      ∑ S : Finset ι with dualParitySet A S = U, boolFourierCoeff f S :=
  fourierCoeff_comp_applyF2Linear A (fun x ↦ signVal (f x)) U

/-- `boolNonemptySparsity f ≤ boolSparsity f`. -/
theorem boolNonemptySparsity_le_boolSparsity (f : (ι → Bool) → Bool) :
    boolNonemptySparsity f ≤ boolSparsity f :=
  card_erase_le

/-- Membership in `largeSpectrum f t`. -/
@[simp]
theorem mem_largeSpectrum {f : (ι → Bool) → Bool} {t : ℝ} {S : Finset ι} :
    S ∈ largeSpectrum f t ↔ 1 / t ≤ |boolFourierCoeff f S| := by
  simp [largeSpectrum]

/-- For `t > 0`, `largeSpectrum f t ⊆ boolSupport f`. -/
theorem largeSpectrum_subset_boolSupport {f : (ι → Bool) → Bool} {t : ℝ} (ht : 0 < t) :
    largeSpectrum f t ⊆ boolSupport f := by
  intro S hS
  rw [mem_largeSpectrum] at hS
  rw [mem_boolSupport]
  exact abs_pos.1 (lt_of_lt_of_le (by positivity) hS)

/-- Monotonicity of `largeSpectrum f t` in the threshold `t > 0`. -/
@[gcongr]
theorem largeSpectrum_mono {f : (ι → Bool) → Bool} {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h : t₁ ≤ t₂) :
    largeSpectrum f t₁ ⊆ largeSpectrum f t₂ := by
  intro S hS
  rw [mem_largeSpectrum] at hS ⊢
  exact (one_div_le_one_div_of_le ht₁ h).trans hS

/-- Counting formula for `boolWeight f`. -/
theorem boolWeight_eq_card_div (f : (ι → Bool) → Bool) :
    boolWeight f = (#{x : ι → Bool | f x = true} : ℝ) / 2 ^ Fintype.card ι := by
  simp [boolWeight, nnratCast_dens, Fintype.card_bool]

/-- Expectation formula `boolWeight f = 𝔼 x, bitVal ℝ (f x)`. -/
theorem boolWeight_eq_expect_bitVal (f : (ι → Bool) → Bool) :
    boolWeight f = 𝔼 x : ι → Bool, bitVal ℝ (f x) := by
  rw [boolWeight_eq_card_div, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  have hsum : (∑ x : ι → Bool, bitVal ℝ (f x)) = ∑ x : ι →
    Bool, if f x = true then (1 : ℝ) else 0 :=
    sum_congr rfl fun x _ ↦ by cases f x <;> simp [bitVal]
  rw [hsum, sum_boole]

/-- `0 ≤ δ(f)`. -/
theorem boolWeight_nonneg (f : (ι → Bool) → Bool) : 0 ≤ boolWeight f := by
  rw [boolWeight_eq_card_div]
  positivity

/-- `δ(f) ≤ 1`. -/
theorem boolWeight_le_one (f : (ι → Bool) → Bool) : boolWeight f ≤ 1 := by
  rw [boolWeight_eq_card_div, div_le_one (by positivity)]
  have h : #{x : ι → Bool | f x = true} ≤ Fintype.card (ι → Bool) := card_filter_le _ _
  simp only [Fintype.card_fun, Fintype.card_bool] at h
  exact_mod_cast h

/-- `δ(f) = 0` iff `f` is identically `false` (`+1`). -/
theorem boolWeight_eq_zero_iff {f : (ι → Bool) → Bool} :
    boolWeight f = 0 ↔ ∀ x, f x = false := by
  rw [boolWeight_eq_card_div, div_eq_zero_iff]
  simp only [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_univ, forall_true_left,
    Bool.not_eq_true, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, or_false]

/-- `δ(f) = 1` iff `f` is identically `true` (`-1`). -/
theorem boolWeight_eq_one_iff {f : (ι → Bool) → Bool} :
    boolWeight f = 1 ↔ ∀ x, f x = true := by
  rw [boolWeight_eq_card_div, div_eq_one_iff_eq (by positivity)]
  have hcard : (2 : ℝ) ^ Fintype.card ι = ((Fintype.card (ι → Bool) : ℕ) : ℝ) := by
    simp [Fintype.card_bool]
  rw [hcard, Nat.cast_inj, ← card_univ, card_filter_eq_iff]
  simp

/-- Negating a Boolean function sends `δ(f)` to `1 - δ(f)`. -/
theorem boolWeight_not (f : (ι → Bool) → Bool) :
    boolWeight (fun x ↦ !f x) = 1 - boolWeight f := by
  rw [boolWeight_eq_expect_bitVal, boolWeight_eq_expect_bitVal]
  have h : ∀ x : ι → Bool, bitVal ℝ (!f x) = 1 - bitVal ℝ (f x) := fun x ↦ by
    cases f x <;> simp [bitVal]
  simp_rw [h]
  rw [expect_sub_distrib, expect_const univ_nonempty]

/-- The empty Fourier coefficient satisfies `f̂(∅) = 1 - 2 δ(f)`. -/
theorem boolFourierCoeff_empty (f : (ι → Bool) → Bool) :
    boolFourierCoeff f ∅ = 1 - 2 * boolWeight f := by
  rw [boolFourierCoeff, fourierCoeff_empty, boolWeight_eq_expect_bitVal]
  simp_rw [signVal_eq_one_sub_two_mul_bitVal]
  rw [expect_sub_distrib, expect_const univ_nonempty, ← mul_expect]

/-- Negating a Boolean function negates every Fourier coefficient. -/
theorem boolFourierCoeff_not (f : (ι → Bool) → Bool) (S : Finset ι) :
    boolFourierCoeff (fun x ↦ !f x) S = -boolFourierCoeff f S := by
  simp only [boolFourierCoeff, signVal_not]
  simpa using fourierCoeff_const_mul (-1) (fun x ↦ signVal (f x)) S

/-- XORing with a parity `parityOn T` translates the Fourier spectrum by `symmDiff T`. -/
theorem boolFourierCoeff_xor_parityOn (f : (ι → Bool) → Bool) (T S : Finset ι) :
    boolFourierCoeff (fun x ↦ parityOn T x ^^ f x) S = boolFourierCoeff f (symmDiff T S) := by
  simp only [boolFourierCoeff, signVal_xor, ← chi_eq_signVal_parityOn]
  exact fourierCoeff_chi_mul T (fun x ↦ signVal (f x)) S

/-- XORing with a parity preserves Fourier sparsity. -/
theorem boolSparsity_xor_parityOn (f : (ι → Bool) → Bool) (T : Finset ι) :
    boolSparsity (fun x ↦ parityOn T x ^^ f x) = boolSparsity f := by
  rw [← card_boolSupport, ← card_boolSupport]
  refine card_bij (fun S _ ↦ symmDiff T S) ?_ ?_ ?_
  · intro S hS
    rw [mem_boolSupport] at hS ⊢
    rwa [← boolFourierCoeff_xor_parityOn]
  · intro S₁ _ S₂ _ h
    have := congr_arg (symmDiff T) h
    simpa [symmDiff_symmDiff_cancel_left] using this
  · intro S hS
    refine ⟨symmDiff T S, ?_, symmDiff_symmDiff_cancel_left T S⟩
    rw [mem_boolSupport] at hS ⊢
    rw [boolFourierCoeff_xor_parityOn, symmDiff_symmDiff_cancel_left]
    exact hS

/-- Full Walsh–Fourier expansion of `signVal (f x)`. -/
theorem boolFourierExpansion (f : (ι → Bool) → Bool) (x : ι → Bool) :
    signVal (f x) = ∑ S : Finset ι, boolFourierCoeff f S * chi ℝ S x :=
  (sum_fourierCoeff_mul_chi (fun y ↦ signVal (f y)) x).symm

/-- Walsh–Fourier expansion of `signVal (f x)` restricted to `boolSupport f`. -/
theorem boolFourierExpansion_on_support (f : (ι → Bool) → Bool) (x : ι → Bool) :
    signVal (f x) = ∑ S ∈ boolSupport f, boolFourierCoeff f S * chi ℝ S x :=
  fourierExpansion_on_support (fun y ↦ signVal (f y)) x

/-- **Parseval's identity** for Boolean functions: `∑ S, f̂(S)^2 = 1`. -/
theorem sum_boolFourierCoeff_sq (f : (ι → Bool) → Bool) :
    ∑ S : Finset ι, boolFourierCoeff f S ^ 2 = 1 := by
  simp only [boolFourierCoeff, ← expect_sq_eq_sum_fourierCoeff_sq]
  have h : ∀ x : ι → Bool, signVal (f x) ^ 2 = 1 := fun x ↦ by rw [sq, signVal_mul_self]
  simp_rw [h]
  exact expect_const univ_nonempty 1

/-- Non-empty Parseval identity: `∑_{S ≠ ∅} f̂(S)^2 = 4 δ(f) (1 - δ(f))`. -/
theorem sum_nonempty_boolFourierCoeff_sq (f : (ι → Bool) → Bool) :
    ∑ S : Finset ι with S ≠ ∅, boolFourierCoeff f S ^ 2 =
      4 * boolWeight f * (1 - boolWeight f) := by
  have hsplit : ∑ S : Finset ι, boolFourierCoeff f S ^ 2 =
      boolFourierCoeff f ∅ ^ 2 + ∑ S : Finset ι with S ≠ ∅, boolFourierCoeff f S ^ 2 := by
    rw [← add_sum_erase _ _ (mem_univ (∅ : Finset ι))]
    congr 1
    refine sum_congr ?_ fun _ _ ↦ rfl
    ext S
    simp
  rw [sum_boolFourierCoeff_sq, boolFourierCoeff_empty] at hsplit
  linarith

/-- Self-convolution orthogonality for Boolean functions: `∑ S, f̂(S) f̂(S ∆ T) = 0` for `T ≠ ∅`. -/
theorem sum_boolFourierCoeff_mul_symmDiff (f : (ι → Bool) → Bool) {T : Finset ι} (hT : T ≠ ∅) :
    ∑ S : Finset ι, boolFourierCoeff f S * boolFourierCoeff f (symmDiff S T) = 0 := by
  have h1 := expect_mul_eq_sum_fourierCoeff_mul (fun x ↦ signVal (f x))
    (fun x ↦ chi ℝ T x * signVal (f x))
  have hrew : ∀ S : Finset ι,
      fourierCoeff (fun x ↦ signVal (f x)) S *
        fourierCoeff (fun x ↦ chi ℝ T x * signVal (f x)) S =
      boolFourierCoeff f S * boolFourierCoeff f (symmDiff S T) := fun S ↦ by
    rw [fourierCoeff_chi_mul, symmDiff_comm T]
    rfl
  simp_rw [hrew] at h1
  rw [← h1]
  have hmul : ∀ x : ι → Bool, signVal (f x) * (chi ℝ T x * signVal (f x)) = chi ℝ T x := fun x ↦ by
    calc signVal (f x) * (chi ℝ T x * signVal (f x))
        = chi ℝ T x * (signVal (f x) * signVal (f x)) := by ring
      _ = chi ℝ T x := by rw [signVal_mul_self, mul_one]
  simp_rw [hmul]
  simp [expect_chi, hT]

/-- Every Fourier coefficient of a Boolean function satisfies `|f̂(S)| ≤ 1`. -/
theorem abs_boolFourierCoeff_le_one (f : (ι → Bool) → Bool) (S : Finset ι) :
    |boolFourierCoeff f S| ≤ 1 := by
  have hsq : |boolFourierCoeff f S| ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [sq_abs, one_pow, ← sum_boolFourierCoeff_sq f]
    exact single_le_sum (fun _ _ ↦ sq_nonneg _) (mem_univ S)
  exact le_of_sq_le_sq hsq zero_le_one

/-- Every Boolean function has positive Fourier sparsity. -/
theorem boolSparsity_pos (f : (ι → Bool) → Bool) : 0 < boolSparsity f := by
  apply fourierSparsity_pos_of_ne_zero
  intro h
  have habs := abs_signVal (f fun _ ↦ false)
  have h0 : signVal (f fun _ ↦ false) = 0 := congr_fun h (fun _ ↦ false)
  simp [h0] at habs

/-- Every Boolean function has spectral norm at least `1`. -/
theorem one_le_boolSpectralNorm (f : (ι → Bool) → Bool) : 1 ≤ boolSpectralNorm f :=
  one_le_sum_abs_fourierCoeff_signVal f

/-- Fourier support of a constant Boolean function is `{∅}`. -/
theorem boolSupport_const (b : Bool) : boolSupport (fun _ : ι → Bool ↦ b) = {∅} := by
  ext S
  simp only [mem_boolSupport, boolFourierCoeff, fourierCoeff_const, mem_singleton]
  by_cases hS : S = ∅
  · simp [hS, show signVal b ≠ 0 by cases b <;> simp [signVal]]
  · simp [hS]

/-- Fourier sparsity of a constant Boolean function is `1`. -/
theorem boolSparsity_const (b : Bool) : boolSparsity (fun _ : ι → Bool ↦ b) = 1 := by
  rw [← card_boolSupport, boolSupport_const, card_singleton]

/-- Fourier rank of a constant Boolean function is `0`. -/
theorem fourierRank_const (b : Bool) : fourierRank (fun _ : ι → Bool ↦ b) = 0 := by
  simp [fourierRank, boolSupport_const]

/-- A Boolean function is constant if and only if its non-empty Fourier sparsity is zero. -/
theorem boolNonemptySparsity_eq_zero_iff {f : (ι → Bool) → Bool} :
    boolNonemptySparsity f = 0 ↔ ∃ b : Bool, ∀ x, f x = b := by
  rw [boolNonemptySparsity, card_eq_zero, erase_eq_empty_iff]
  constructor
  · rintro (hempty | hsing)
    · exfalso
      have hp := boolSparsity_pos f
      rw [← card_boolSupport, hempty, card_empty] at hp
      omega
    · let x₀ : ι → Bool := fun _ ↦ false
      refine ⟨f x₀, fun x ↦ ?_⟩
      have hval : ∀ y : ι → Bool, signVal (f y) = boolFourierCoeff f ∅ := fun y ↦ by
        rw [boolFourierExpansion_on_support f y, hsing, sum_singleton, chi_empty, mul_one]
      have hsign : signVal (f x) = signVal (f x₀) := (hval x).trans (hval x₀).symm
      cases hfx : f x <;> cases hf0 : f x₀ <;> simp only [hfx, hf0, signVal] at hsign ⊢ <;>
        norm_num at hsign
  · rintro ⟨b, hb⟩
    right
    have : f = fun _ ↦ b := funext hb
    rw [this, boolSupport_const]

/-- A Boolean function has Fourier rank `0` iff it is constant. -/
theorem fourierRank_eq_zero_iff {f : (ι → Bool) → Bool} :
    fourierRank f = 0 ↔ ∃ b : Bool, ∀ x, f x = b := by
  rw [fourierRank, parityDim_eq_zero_iff, ← boolNonemptySparsity_eq_zero_iff,
    boolNonemptySparsity, card_eq_zero]
  simp [subset_singleton_iff, erase_eq_empty_iff]

/-- A Boolean function has Fourier sparsity `1` iff it is a signed parity character. -/
theorem boolSparsity_eq_one_iff {f : (ι → Bool) → Bool} :
    boolSparsity f = 1 ↔ ∃ (S : Finset ι) (b : Bool), ∀ x, f x = (b ^^ parityOn S x) := by
  rw [← card_boolSupport]
  constructor
  · intro hk
    obtain ⟨S, hS⟩ := card_eq_one.1 hk
    have hsq : boolFourierCoeff f S ^ 2 = 1 := by
      rw [← sum_boolFourierCoeff_sq f]
      symm
      refine sum_eq_single S (fun T _ hTS ↦ ?_) (by simp)
      have hnot : T ∉ boolSupport f := by rw [hS]; simp [hTS]
      rw [mem_boolSupport, not_not] at hnot
      simp [hnot]
    have hval : ∀ x, signVal (f x) = boolFourierCoeff f S * chi ℝ S x := fun x ↦ by
      rw [boolFourierExpansion_on_support f x, hS, sum_singleton]
    rcases sq_eq_one_iff.1 hsq with h1 | hm1
    · refine ⟨S, false, fun x ↦ ?_⟩
      have hx := hval x
      rw [h1, one_mul, chi_eq_signVal_parityOn] at hx
      cases hfx : f x <;> cases hp : parityOn S x <;>
        simp only [hfx, hp, signVal, Bool.false_xor] at hx ⊢ <;> norm_num at hx
    · refine ⟨S, true, fun x ↦ ?_⟩
      have hx := hval x
      rw [hm1, neg_one_mul, chi_eq_signVal_parityOn] at hx
      cases hfx : f x <;> cases hp : parityOn S x <;>
        simp only [hfx, hp, signVal, Bool.true_xor, Bool.not_true, Bool.not_false] at hx ⊢ <;>
        norm_num at hx
  · rintro ⟨S, b, hb⟩
    have hfeq : f = fun x ↦ b ^^ parityOn S x := funext hb
    rw [hfeq]
    have hsupp : boolSupport (fun x ↦ b ^^ parityOn S x) = {S} := by
      ext T
      rw [mem_boolSupport, mem_singleton]
      have hfc : boolFourierCoeff (fun x ↦ b ^^ parityOn S x) T =
          signVal b * if T = S then 1 else 0 := by
        rw [boolFourierCoeff]
        have hfn : (fun x : ι → Bool ↦ signVal (b ^^ parityOn S x)) =
            fun x ↦ signVal b * signVal (parityOn S x) := by ext x; exact signVal_xor _ _
        rw [hfn, fourierCoeff_const_mul, fourierCoeff_signVal_parityOn]
      rw [hfc]
      have hbnz : signVal b ≠ 0 := by cases b <;> simp [signVal]
      by_cases hTS : T = S <;> simp [hTS, hbnz]
    rw [hsupp, card_singleton]

/-- Every Boolean function of sparsity `1` has spectral norm `1`. -/
theorem boolSpectralNorm_eq_one_of_boolSparsity_eq_one {f : (ι → Bool) → Bool}
    (hk : boolSparsity f = 1) : boolSpectralNorm f = 1 := by
  rw [← card_boolSupport] at hk
  obtain ⟨S, hS⟩ := card_eq_one.1 hk
  have hsq : boolFourierCoeff f S ^ 2 = 1 := by
    rw [← sum_boolFourierCoeff_sq f]
    symm
    refine sum_eq_single S (fun T _ hTS ↦ ?_) (by simp)
    have hnot : T ∉ boolSupport f := by rw [hS]; simp [hTS]
    rw [mem_boolSupport, not_not] at hnot
    simp [hnot]
  have habs : |boolFourierCoeff f S| = 1 := by
    rcases sq_eq_one_iff.1 hsq with h | h <;> simp [h]
  unfold boolSpectralNorm spectralNorm
  refine (sum_eq_single S (fun T _ hTS ↦ ?_) (by simp)).trans habs
  have hnot : T ∉ boolSupport f := by rw [hS]; simp [hTS]
  rw [mem_boolSupport, not_not] at hnot
  exact abs_eq_zero.2 hnot

/-- If `k(f) > 1`, then `0 < δ(f)`. -/
theorem boolWeight_pos_of_one_lt_boolSparsity {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : 0 < boolWeight f := by
  rcases (boolWeight_nonneg f).eq_or_lt with h0 | hpos
  · exfalso
    have hfeq : f = fun _ ↦ false := funext (boolWeight_eq_zero_iff.1 h0.symm)
    rw [hfeq, boolSparsity_const] at hk
    omega
  · exact hpos

/-- If `k(f) > 1`, then `δ(f) < 1`. -/
theorem boolWeight_lt_one_of_one_lt_boolSparsity {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : boolWeight f < 1 := by
  rcases (boolWeight_le_one f).eq_or_lt with h1 | hlt
  · exfalso
    have hfeq : f = fun _ ↦ true := funext (boolWeight_eq_one_iff.1 h1)
    rw [hfeq, boolSparsity_const] at hk
    omega
  · exact hlt

/-- Every Boolean function with `k(f) > 1` satisfies `k(f) ≥ 4`. -/
theorem four_le_boolSparsity_of_one_lt {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : 4 ≤ boolSparsity f := by
  have htwo : 1 < #(boolSupport f) := hk
  obtain ⟨S₁, hS₁, S₂, hS₂, hne⟩ := one_lt_card.1 htwo
  set T := symmDiff S₁ S₂
  have hT : T ≠ ∅ := fun h0 ↦ hne (symmDiff_eq_bot.1 h0)
  have hprod_ne : boolFourierCoeff f S₁ * boolFourierCoeff f (symmDiff S₁ T) ≠ 0 := by
    rw [symmDiff_symmDiff_cancel_left]
    exact mul_ne_zero (mem_boolSupport.1 hS₁) (mem_boolSupport.1 hS₂)
  have horth := sum_boolFourierCoeff_mul_symmDiff f hT
  have hex : ∃ S₃ : Finset ι, S₃ ≠ S₁ ∧ S₃ ≠ S₂ ∧
      boolFourierCoeff f S₃ * boolFourierCoeff f (symmDiff S₃ T) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsum : ∑ S : Finset ι, boolFourierCoeff f S * boolFourierCoeff f (symmDiff S T) =
        2 * (boolFourierCoeff f S₁ * boolFourierCoeff f S₂) := by
      rw [← sum_subset (subset_univ ({S₁, S₂} : Finset (Finset ι)))]
      · rw [sum_pair hne]
        have h1 : symmDiff S₁ T = S₂ := symmDiff_symmDiff_cancel_left S₁ S₂
        have h2 : symmDiff S₂ T = S₁ := by
          dsimp [T]; rw [symmDiff_comm S₁ S₂, symmDiff_symmDiff_cancel_left]
        rw [h1, h2]; ring
      · intro S _ hnot
        simp only [mem_insert, mem_singleton, not_or] at hnot
        exact hall S hnot.1 hnot.2
    rw [hsum] at horth
    rw [symmDiff_symmDiff_cancel_left] at hprod_ne
    exact hprod_ne (by linarith)
  obtain ⟨S₃, h31, h32, h3prod⟩ := hex
  set S₄ := symmDiff S₃ T
  have hS₃ : S₃ ∈ boolSupport f := mem_boolSupport.2 (left_ne_zero_of_mul h3prod)
  have hS₄ : S₄ ∈ boolSupport f := mem_boolSupport.2 (right_ne_zero_of_mul h3prod)
  have h43 : S₄ ≠ S₃ := fun h ↦ hT (by
    have := congr_arg (symmDiff S₃) h
    simpa [S₄, symmDiff_symmDiff_cancel_left] using this)
  have h41 : S₄ ≠ S₁ := fun h ↦ h32 (by
    have := congr_arg (symmDiff · T) h
    simpa [S₄, T, symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_left] using this)
  have h42 : S₄ ≠ S₂ := fun h ↦ h31 (by
    have := congr_arg (symmDiff · T) h
    have h2 : symmDiff S₂ T = S₁ := by
      dsimp [T]; rw [symmDiff_comm S₁ S₂, symmDiff_symmDiff_cancel_left]
    simpa [S₄, symmDiff_symmDiff_cancel_right, h2] using this)
  have hsub : ({S₁, S₂, S₃, S₄} : Finset (Finset ι)) ⊆ boolSupport f := by
    intro S hS
    simp only [mem_insert, mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : #({S₁, S₂, S₃, S₄} : Finset (Finset ι)) = 4 := by
    rw [card_insert_of_notMem (by simp [hne, h31.symm, h41.symm]),
      card_insert_of_notMem (by simp [h32.symm, h42.symm]),
      card_insert_of_notMem (by simp [h43.symm]), card_singleton]
  rw [← card_boolSupport, ← hcard4]
  exact card_le_card hsub

/-- Every Boolean function with `k(f) > 1` satisfies `r(f) ≥ 2`. -/
theorem two_le_fourierRank_of_one_lt_boolSparsity {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : 2 ≤ fourierRank f := by
  have h4 := four_le_boolSparsity_of_one_lt hk
  have hpow : boolSparsity f ≤ 2 ^ fourierRank f := card_le_two_pow_parityDim (boolSupport f)
  by_contra hlt
  have hr : fourierRank f = 0 ∨ fourierRank f = 1 := by omega
  rcases hr with hr0 | hr1
  · rw [hr0] at hpow; omega
  · rw [hr1] at hpow; omega

/-- Every Boolean function satisfies `log₂ k(f) ≤ r(f)`. -/
theorem logb_boolSparsity_le_fourierRank (f : (ι → Bool) → Bool) :
    Real.logb 2 (boolSparsity f) ≤ fourierRank f := by
  have hpow : (boolSparsity f : ℝ) ≤ (2 : ℝ) ^ fourierRank f := by
    exact_mod_cast card_le_two_pow_parityDim (boolSupport f)
  have hpos : (0 : ℝ) < boolSparsity f := Nat.cast_pos.2 (boolSparsity_pos f)
  calc Real.logb 2 (boolSparsity f) ≤ Real.logb 2 ((2 : ℝ) ^ fourierRank f) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hpow
    _ = fourierRank f := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- For every Boolean function with `k(f) > 1`, `1 ≤ k(f) * δ(f)` by the uncertainty principle. -/
theorem one_le_boolSparsity_mul_boolWeight {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : 1 ≤ (boolSparsity f : ℝ) * boolWeight f := by
  have hδ := boolWeight_pos_of_one_lt_boolSparsity hk
  by_cases h0 : boolFourierCoeff f ∅ = 0
  · rw [boolFourierCoeff_empty] at h0
    have hδ_half : boolWeight f = 1 / 2 := by linarith
    have hk2 : (2 : ℝ) ≤ boolSparsity f := by exact_mod_cast hk
    rw [hδ_half]; linarith
  · let g : (ι → Bool) → ℝ := fun x ↦ bitVal ℝ (f x)
    have hg_ne : g ≠ 0 := fun hg0 ↦ hδ.ne' <| by
      rw [boolWeight_eq_expect_bitVal]
      change 𝔼 x, g x = 0
      simp [hg0]
    have hg_sub : fourierSupport g ⊆ boolSupport f := by
      intro S hS
      rw [mem_fourierSupport] at hS
      rw [mem_boolSupport]
      by_cases hSe : S = ∅
      · rwa [hSe]
      · have hbv := fourierCoeff_bitVal_of_nonempty f (nonempty_iff_ne_empty.2 hSe)
        intro hc
        apply hS
        rw [hbv]
        rw [boolFourierCoeff] at hc
        simp [hc]
    have hkg : (fourierSparsity g : ℝ) ≤ boolSparsity f := by
      exact_mod_cast card_le_card hg_sub
    have hd : (dens {x : ι → Bool | g x ≠ 0} : ℝ) = boolWeight f := by
      unfold boolWeight
      congr 2; ext x; cases f x <;> simp [g, bitVal]
    have hup := one_le_dens_mul_card_fourierCoeff_ne_zero hg_ne
    rw [hd] at hup
    calc (1 : ℝ) ≤ boolWeight f * fourierSparsity g := hup
      _ ≤ boolWeight f * boolSparsity f := mul_le_mul_of_nonneg_left hkg hδ.le
      _ = boolSparsity f * boolWeight f := mul_comm _ _

/-- **Spectral norm upper bound**: for any Boolean function `f` with `0 < δ(f)`,
`‖f̂‖₁ ≤ 3 √(k(f) δ(f))`. -/
theorem boolSpectralNorm_le_three_mul_sqrt {f : (ι → Bool) → Bool}
    (hδ : 0 < boolWeight f) :
    boolSpectralNorm f ≤ 3 * Real.sqrt ((boolSparsity f : ℝ) * boolWeight f) := by
  by_cases hk1 : boolSparsity f = 1
  · rw [boolSpectralNorm_eq_one_of_boolSparsity_eq_one hk1]
    obtain ⟨S, b, hb⟩ := boolSparsity_eq_one_iff.1 hk1
    have hfeq : f = fun x ↦ b ^^ parityOn S x := funext hb
    have hhalf : (1 / 2 : ℝ) ≤ boolWeight f := by
      by_cases hS : S = ∅
      · subst hS
        have hconst : f = fun _ ↦ b := by ext x; simp [hfeq]
        cases b
        · rw [hconst, boolWeight_eq_zero_iff.2 fun _ ↦ rfl] at hδ; linarith
        · rw [hconst, boolWeight_eq_one_iff.2 fun _ ↦ rfl]; norm_num
      · have h0 : boolFourierCoeff f ∅ = 0 := by
          rw [hfeq, boolFourierCoeff]
          have hfn : (fun x : ι → Bool ↦ signVal (b ^^ parityOn S x)) =
              fun x ↦ signVal b * signVal (parityOn S x) := by ext x; exact signVal_xor _ _
          rw [hfn, fourierCoeff_const_mul, fourierCoeff_signVal_parityOn]
          simp [Ne.symm hS]
        rw [boolFourierCoeff_empty] at h0
        linarith
    have hprod : (1 / 2 : ℝ) ≤ (boolSparsity f : ℝ) * boolWeight f := by
      rw [hk1, Nat.cast_one, one_mul]; exact hhalf
    have hsq : (1 : ℝ) ≤ 9 * ((boolSparsity f : ℝ) * boolWeight f) := by linarith
    have hsqrt9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (9 * ((boolSparsity f : ℝ) * boolWeight f)) := Real.sqrt_le_sqrt hsq
      _ = 3 * Real.sqrt ((boolSparsity f : ℝ) * boolWeight f) := by
          rw [Real.sqrt_mul (by norm_num), hsqrt9]
  · have hk : 1 < boolSparsity f := by have hp := boolSparsity_pos f; omega
    let N : Finset (Finset ι) := (boolSupport f).erase ∅
    have hsplit : boolSpectralNorm f =
        |1 - 2 * boolWeight f| + ∑ S ∈ N, |boolFourierCoeff f S| := by
      unfold boolSpectralNorm spectralNorm
      rw [← add_sum_erase _ _ (mem_univ (∅ : Finset ι)), ← boolFourierCoeff,
        boolFourierCoeff_empty]
      congr 1; symm
      refine sum_subset (erase_subset_erase ∅ (subset_univ _)) fun S hS hnot ↦ ?_
      have hne : S ≠ ∅ := ne_of_mem_erase hS
      have hnotsupp : S ∉ boolSupport f := fun hs ↦ hnot (mem_erase.2 ⟨hne, hs⟩)
      rw [mem_boolSupport, not_not] at hnotsupp
      exact abs_eq_zero.2 hnotsupp
    have hcs : (∑ S ∈ N, |boolFourierCoeff f S|) ^ 2 ≤
        (boolSparsity f : ℝ) * (4 * boolWeight f) := by
      calc (∑ S ∈ N, |boolFourierCoeff f S|) ^ 2
          = (∑ S ∈ N, |boolFourierCoeff f S| * 1) ^ 2 := by simp
        _ ≤ (∑ S ∈ N, |boolFourierCoeff f S| ^ 2) * (∑ _ ∈ N, (1 : ℝ) ^ 2) :=
            sum_mul_sq_le_sq_mul_sq N _ _
        _ = (#N : ℝ) * ∑ S ∈ N, boolFourierCoeff f S ^ 2 := by simp [sq_abs, mul_comm]
        _ ≤ (boolSparsity f : ℝ) * ∑ S : Finset ι with S ≠ ∅, boolFourierCoeff f S ^ 2 := by
            refine mul_le_mul (by exact_mod_cast card_erase_le) ?_
              (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)
            refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ sq_nonneg _
            intro S hS; simp [(mem_erase.1 hS).1]
        _ = (boolSparsity f : ℝ) * (4 * boolWeight f * (1 - boolWeight f)) := by
            rw [sum_nonempty_boolFourierCoeff_sq]
        _ ≤ (boolSparsity f : ℝ) * (4 * boolWeight f) :=
            mul_le_mul_of_nonneg_left (by nlinarith [boolWeight_nonneg f]) (Nat.cast_nonneg _)
    have htail : ∑ S ∈ N, |boolFourierCoeff f S| ≤
        2 * Real.sqrt ((boolSparsity f : ℝ) * boolWeight f) := by
      refine le_of_sq_le_sq ?_ (by positivity)
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      linarith
    have h1 : |1 - 2 * boolWeight f| ≤ 1 :=
      abs_le.2 ⟨by linarith [boolWeight_le_one f], by linarith [boolWeight_nonneg f]⟩
    have hsqrt1 : 1 ≤ Real.sqrt ((boolSparsity f : ℝ) * boolWeight f) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (one_le_boolSparsity_mul_boolWeight hk)
    rw [hsplit]; linarith

/-- Change of basis on the Fourier domain: given an invertible `𝔽₂`-linear operator `B`,
`fourierBasisChange B f` is the Boolean function `x ↦ f ((B⁻¹)ᵀ x)` whose Fourier coefficient at
`S` equals `f̂(B S)`. -/
@[expose]
def fourierBasisChange (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))
    (f : (ι → Bool) → Bool) : (ι → Bool) → Bool :=
  fun x ↦ f (applyF2Linear (transposeF2Equiv B.symm).toLinearMap x)

/-- Fourier coefficients of `fourierBasisChange B f` satisfy `f̂_B(S) = f̂(B S)`. -/
theorem boolFourierCoeff_fourierBasisChange
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (f : (ι → Bool) → Bool) (S : Finset ι) :
    boolFourierCoeff (fourierBasisChange B f) S =
      boolFourierCoeff f (parityVecEquiv.symm (B (parityVec S))) := by
  unfold boolFourierCoeff fourierBasisChange
  have hpull := fourierCoeff_comp_applyF2Linear (transposeF2Equiv B.symm).toLinearMap
    (fun y ↦ signVal (f y)) S
  rw [hpull]
  have hdual : ∀ T : Finset ι,
      dualParitySet (transposeF2Equiv B.symm).toLinearMap T = S ↔
        T = parityVecEquiv.symm (B (parityVec S)) := by
    intro T
    rw [← parityVec_injective.eq_iff, parityVec_dualParitySet, transposeF2Equiv_toLinearMap,
      transposeF2Linear_transposeF2Linear, LinearEquiv.coe_coe]
    constructor
    · intro h
      apply parityVec_injective
      rw [← h, LinearEquiv.apply_symm_apply, ← parityVecEquiv_apply (parityVecEquiv.symm _),
        Equiv.apply_symm_apply]
    · rintro rfl
      rw [← parityVecEquiv_apply, Equiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  simp_rw [hdual, filter_eq']
  simp

/-- Boolean weight is preserved under invertible Fourier basis changes. -/
theorem boolWeight_fourierBasisChange
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (f : (ι → Bool) → Bool) :
    boolWeight (fourierBasisChange B f) = boolWeight f := by
  have h := boolFourierCoeff_fourierBasisChange B f ∅
  simp only [parityVec_empty, map_zero, parityVecEquiv_symm_zero, boolFourierCoeff_empty] at h
  linarith

/-- Fourier sparsity is preserved under invertible Fourier basis changes. -/
theorem boolSparsity_fourierBasisChange
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (f : (ι → Bool) → Bool) :
    boolSparsity (fourierBasisChange B f) = boolSparsity f := by
  rw [← card_boolSupport, ← card_boolSupport]
  let eS : Finset ι ≃ Finset ι :=
    parityVecEquiv.trans (B.toEquiv.trans parityVecEquiv.symm)
  have heS : ∀ S : Finset ι, eS S = parityVecEquiv.symm (B (parityVec S)) :=
    fun S ↦ by simp [eS]
  refine card_bij (fun S _ ↦ eS S) ?_ (fun _ _ _ _ h ↦ eS.injective h) ?_
  · intro S hS
    rw [mem_boolSupport] at hS ⊢
    rw [boolFourierCoeff_fourierBasisChange, ← heS S] at hS
    exact hS
  · intro T hT
    refine ⟨eS.symm T, ?_, eS.apply_symm_apply T⟩
    rw [mem_boolSupport] at hT ⊢
    rwa [boolFourierCoeff_fourierBasisChange, ← heS (eS.symm T), Equiv.apply_symm_apply]

/-- `𝔽₂`-degree is invariant under invertible Fourier basis changes. -/
theorem f2Degree_fourierBasisChange
    (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (f : (ι → Bool) → Bool) :
    f2Degree (fourierBasisChange B f) = f2Degree f := by
  let E := transposeF2Equiv B.symm
  apply le_antisymm
  · rw [f2Degree, totalDegree_le_iff_mem_lowDegree]
    exact mem_lowDegree_comp_applyF2Linear E.toLinearMap (mem_lowDegree_totalDegree _)
  · rw [f2Degree, totalDegree_le_iff_mem_lowDegree]
    have hcomp : (fun x : ι → Bool ↦ bitVal (ZMod 2) (f x)) =
        fun x ↦ bitVal (ZMod 2) (fourierBasisChange B f (applyF2Linear E.symm.toLinearMap x)) := by
      ext x
      have hin : applyF2Linear E.toLinearMap (applyF2Linear E.symm.toLinearMap x) = x := by
        rw [applyF2Linear_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, applyF2Linear_id]
      change _ = bitVal (ZMod 2) (f (applyF2Linear E.toLinearMap
        (applyF2Linear E.symm.toLinearMap x)))
      rw [hin]
    rw [hcomp]
    exact mem_lowDegree_comp_applyF2Linear E.symm.toLinearMap (mem_lowDegree_totalDegree _)

/-- Uniqueness helper: if a Boolean function on `c ≥ 2` bits has an odd number of `true` inputs,
then every Walsh–Fourier coefficient is nonzero. -/
private theorem boolSupport_eq_univ_of_odd_card_true {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hκ : 1 < Fintype.card κ) (g : (κ → Bool) → Bool)
    (hodd : Odd #{y : κ → Bool | g y = true}) :
    boolSupport g = univ := by
  ext S
  simp only [mem_boolSupport, mem_univ, iff_true]
  let c : ℕ := Fintype.card κ
  have hc : 1 ≤ c - 1 := by omega
  let sumSign : ℤ := ∑ y : κ → Bool with g y = true, if parityOn S y then (-1 : ℤ) else 1
  let M : ℤ := (if S = ∅ then (2 : ℤ) ^ (c - 1) else 0) - sumSign
  have hcoeff : (2 : ℝ) ^ (c - 1) * boolFourierCoeff g S = (M : ℝ) := by
    rw [boolFourierCoeff, fourierCoeff_eq_sum]
    have hpow : (2 : ℝ) ^ Fintype.card κ = (2 : ℝ) ^ (c - 1) * 2 := by
      have hc_eq : Fintype.card κ = (c - 1) + 1 := by omega
      rw [hc_eq, pow_succ]
    have hterm : ∀ y : κ → Bool, signVal (g y) * chi ℝ S y =
        chi ℝ S y - 2 * if g y = true then chi ℝ S y else 0 := by
      intro y; cases g y
      · simp [signVal]
      · simp [signVal]; ring
    simp_rw [hterm, sum_sub_distrib, ← mul_sum, sum_chi]
    have hfilt : (∑ y : κ → Bool, if g y = true then chi ℝ S y else 0) = (sumSign : ℝ) := by
      dsimp [sumSign]
      push_cast
      rw [← sum_filter]
      refine sum_congr rfl fun y _ ↦ ?_
      rw [chi_eq_signVal_parityOn]
      cases parityOn S y <;> simp [signVal]
    rw [hfilt, hpow]
    have h2ne : (2 : ℝ) ^ (c - 1) ≠ 0 := by positivity
    dsimp [M]
    by_cases hS : S = ∅
    · simp only [hS, ↓reduceIte, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
      field_simp
    · simp only [hS, ↓reduceIte, Int.cast_sub, Int.cast_zero]
      field_simp; ring
  have hModd : Odd M := by
    have heven1 : Even (if S = ∅ then (2 : ℤ) ^ (c - 1) else 0) := by
      by_cases hS : S = ∅
      · simp only [hS, ↓reduceIte]; exact Even.pow_of_ne_zero even_two (by omega)
      · simp only [hS, ↓reduceIte]; exact Even.zero
    have hsum_odd : Odd sumSign := by
      rw [Int.odd_iff]
      obtain ⟨r, hr⟩ := hodd
      have hcast : (sumSign : ZMod 2) = 1 := by
        dsimp [sumSign]
        rw [Int.cast_sum]
        have hone : ∀ y ∈ univ.filter (fun y : κ → Bool ↦ g y = true),
            ((if parityOn S y then (-1 : ℤ) else 1 : ℤ) : ZMod 2) = 1 := fun y _ ↦ by
          cases parityOn S y <;> decide
        rw [sum_congr rfl hone, sum_const, nsmul_eq_mul, mul_one, hr]
        push_cast
        have h2 : (2 : ZMod 2) = 0 := by decide
        simp [h2]
      have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub (1 : ℤ) sumSign 2).1 hcast.symm
      omega
    exact heven1.sub_odd hsum_odd
  have hMne : M ≠ 0 := fun h0 ↦ by simp [h0] at hModd
  intro hc0
  rw [hc0, mul_zero] at hcoeff
  exact hMne (by exact_mod_cast hcoeff.symm)

/-- **Granularity of Fourier-sparse Boolean functions**
: for every Boolean function `f : (ι → Bool) → Bool` with Fourier sparsity
`k(f) ≥ 2` and every `S : Finset ι`, `f̂(S)` is an integer multiple of
`2 ^ (1 - ⌊log₂ k(f)⌋)`.
-/
theorem exists_int_mul_boolFourierCoeff {f : (ι → Bool) → Bool}
    (hk : 2 ≤ boolSparsity f) (S : Finset ι) :
    ∃ z : ℤ,
      boolFourierCoeff f S = (z : ℝ) * (2 : ℝ) ^ (1 - (Nat.log 2 (boolSparsity f) : ℤ)) := by
  by_cases hS : boolFourierCoeff f S = 0
  · exact ⟨0, by simp [hS]⟩
  set m : ℕ := Nat.log 2 (boolSparsity f)
  have hm1 : 1 ≤ m := Nat.le_log_of_pow_le (by norm_num) (by simpa using hk)
  have hk_lt : boolSparsity f < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  let fS : (ι → Bool) → Bool := fun x ↦ parityOn S x ^^ f x
  have hfS_sp : boolSparsity fS = boolSparsity f := boolSparsity_xor_parityOn f S
  have hfS_empty : boolFourierCoeff fS ∅ = boolFourierCoeff f S := by
    rw [boolFourierCoeff_xor_parityOn]; congr 1; exact symmDiff_bot S
  let badSet : Finset (Finset ι) := (boolSupport fS).erase ∅
  have hbad_card : #badSet < 2 ^ (m + 1) := by
    calc #badSet ≤ #(boolSupport fS) := card_erase_le
      _ = boolSparsity f := by rw [card_boolSupport, hfS_sp]
      _ < 2 ^ (m + 1) := hk_lt
  let κ := Fin (m + 1)
  let total : ℕ := Fintype.card (κ → ι → ZMod 2)
  have htotal : total = (2 ^ Fintype.card ι) ^ (m + 1) := by
    simp [total, κ, ZMod.card]
  have hperp_card : ∀ γ ∈ badSet,
      #{M : κ → ι → ZMod 2 | ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0} * 2 ^ (m + 1) =
        total := by
    intro γ hγ
    have hγne : γ ≠ ∅ := ne_of_mem_erase hγ
    obtain ⟨i₀, hi₀⟩ := nonempty_iff_ne_empty.2 hγne
    let H : Finset (ι → ZMod 2) := {v : ι → ZMod 2 | ∑ i : ι, parityVec γ i * v i = 0}
    have hH : #H * 2 = 2 ^ Fintype.card ι := by
      let rest := {i : ι // i ≠ i₀}
      let φ : (rest → ZMod 2) → H := fun r ↦
        ⟨fun i ↦ if h : i = i₀ then -∑ j : rest, parityVec γ j.1 * r j else r ⟨i, h⟩, by
          simp only [H, mem_filter, mem_univ, true_and]
          rw [← add_sum_erase _ _ (mem_univ i₀)]
          simp only [↓reduceDIte, parityVec_of_mem hi₀, one_mul]
          have herase : ∑ x ∈ univ.erase i₀,
              parityVec γ x *
                (if h : x = i₀ then -∑ j : rest, parityVec γ j.1 * r j else r ⟨x, h⟩) =
              ∑ j : rest, parityVec γ j.1 * r j :=
            sum_bij (fun x hx ↦ ⟨x, ne_of_mem_erase hx⟩) (fun _ _ ↦ mem_univ _)
              (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
              (fun j _ ↦ ⟨j.1, mem_erase.2 ⟨j.2, mem_univ _⟩, rfl⟩) fun x hx ↦ by
                simp [ne_of_mem_erase hx]
          rw [herase, neg_add_cancel]⟩
      have hbij : Function.Bijective φ := by
        refine ⟨fun r₁ r₂ h ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
        · ext ⟨i, hi⟩
          have := congr_fun (congr_arg Subtype.val h) i
          simpa [φ, hi] using this
        · refine ⟨fun j ↦ v j.1, Subtype.ext ?_⟩
          ext i
          simp only [φ]
          by_cases hi : i = i₀
          · subst hi
            simp only [↓reduceDIte]
            simp only [H, mem_filter, mem_univ, true_and] at hv
            rw [← add_sum_erase _ _ (mem_univ i), parityVec_of_mem hi₀, one_mul] at hv
            have herase : ∑ x ∈ univ.erase i, parityVec γ x * v x =
                ∑ j : rest, parityVec γ j.1 * v j.1 :=
              sum_bij (fun x hx ↦ ⟨x, ne_of_mem_erase hx⟩) (fun _ _ ↦ mem_univ _)
                (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
                (fun j _ ↦ ⟨j.1, mem_erase.2 ⟨j.2, mem_univ _⟩, rfl⟩) (fun _ _ ↦ rfl)
            rw [herase] at hv
            exact (eq_neg_of_add_eq_zero_left hv).symm
          · simp [hi]
      have hcardH : #H = Fintype.card (rest → ZMod 2) := by
        rw [← Fintype.card_coe, Fintype.card_of_bijective hbij]
      have hrest : Fintype.card rest + 1 = Fintype.card ι := by
        have h1 : Fintype.card rest = #(univ.erase i₀) := by
          rw [← Fintype.card_coe]
          exact Fintype.card_congr
            { toFun := fun j ↦ ⟨j.1, mem_erase.2 ⟨j.2, mem_univ _⟩⟩
              invFun := fun j ↦ ⟨j.1, ne_of_mem_erase j.2⟩
              left_inv := fun ⟨_, _⟩ ↦ rfl
              right_inv := fun ⟨_, _⟩ ↦ rfl }
        rw [h1, card_erase_add_one (mem_univ i₀), card_univ]
      rw [hcardH, Fintype.card_fun, ZMod.card, ← pow_succ, hrest]
    have hprod_card : #{M : κ → ι → ZMod 2 | ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0} =
        #H ^ (m + 1) := by
      have heq : (univ.filter fun M : κ → ι → ZMod 2 ↦
          ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0) = Fintype.piFinset fun _ : κ ↦ H := by
        ext M; simp [H]
      rw [heq, Fintype.card_piFinset_const]
    rw [hprod_card, ← mul_pow, hH, htotal]
  have hexM : ∃ M : κ → ι → ZMod 2,
      ∀ γ ∈ badSet, ∃ j : κ, ∑ i : ι, parityVec γ i * M j i ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcov : (univ : Finset (κ → ι → ZMod 2)) ⊆
        badSet.biUnion fun γ ↦
          {M : κ → ι → ZMod 2 | ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0} := by
      intro M _
      obtain ⟨γ, hγ, hM⟩ := hall M
      exact mem_biUnion.2 ⟨γ, hγ, by simpa using hM⟩
    have hle : total ≤ ∑ γ ∈ badSet,
        #{M : κ → ι → ZMod 2 | ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0} :=
      (card_le_card hcov).trans card_biUnion_le
    have hmul : total * 2 ^ (m + 1) ≤ total * #badSet := by
      calc total * 2 ^ (m + 1)
          ≤ (∑ γ ∈ badSet,
              #{M : κ → ι → ZMod 2 | ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0}) *
              2 ^ (m + 1) := Nat.mul_le_mul_right _ hle
        _ = ∑ γ ∈ badSet,
              #{M : κ → ι → ZMod 2 | ∀ j : κ, ∑ i : ι, parityVec γ i * M j i = 0} *
              2 ^ (m + 1) := sum_mul ..
        _ = ∑ _ ∈ badSet, total := sum_congr rfl hperp_card
        _ = total * #badSet := by simp [mul_comm]
    have htot_pos : 0 < total := by rw [htotal]; positivity
    have hge : 2 ^ (m + 1) ≤ #badSet := Nat.le_of_mul_le_mul_left hmul htot_pos
    omega
  obtain ⟨M, hM⟩ := hexM
  let A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    { toFun := fun v i ↦ ∑ j : κ, v j * M j i
      map_add' := fun u v ↦ by ext i; simp [add_mul, sum_add_distrib]
      map_smul' := fun c v ↦ by ext i; simp [mul_assoc, mul_sum] }
  have hA_single : ∀ j : κ, A (Pi.single j 1) = M j := by
    intro j; ext i; simp [A, Pi.single_apply]
  have hdual_ne : ∀ γ ∈ badSet, dualParitySet A γ ≠ ∅ := by
    intro γ hγ h0
    obtain ⟨j, hj⟩ := hM γ hγ
    apply hj
    have hv := congr_fun (congr_arg parityVec h0) j
    rw [parityVec_dualParitySet, parityVec_empty, Pi.zero_apply, transposeF2Linear_apply,
      hA_single] at hv
    exact hv
  let g : (κ → Bool) → Bool := fun y ↦ fS (applyF2Linear A y)
  have hg_coeff : ∀ U : Finset κ,
      boolFourierCoeff g U = ∑ γ ∈ boolSupport fS with dualParitySet A γ = U,
        boolFourierCoeff fS γ := by
    intro U
    unfold boolFourierCoeff g
    rw [fourierCoeff_comp_applyF2Linear A (fun x ↦ signVal (fS x)) U]
    symm
    refine sum_subset (filter_subset_filter _ (subset_univ _)) fun γ hγ hnot ↦ ?_
    have heq : dualParitySet A γ = U := (mem_filter.1 hγ).2
    have hnotsupp : γ ∉ boolSupport fS := fun hs ↦ hnot (mem_filter.2 ⟨hs, heq⟩)
    exact not_not.1 (mt mem_boolSupport.2 hnotsupp)
  have hg_empty : boolFourierCoeff g ∅ = boolFourierCoeff f S := by
    rw [hg_coeff ∅, ← hfS_empty]
    have hflt : {γ ∈ boolSupport fS | dualParitySet A γ = ∅} = {∅} := by
      ext γ
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hγs, hγ0⟩
        by_contra hne
        exact hdual_ne γ (mem_erase.2 ⟨hne, hγs⟩) hγ0
      · rintro rfl
        exact ⟨mem_boolSupport.2 (by rwa [hfS_empty]), dualParitySet_empty A⟩
    rw [hflt, sum_singleton]
  have hg_supp_sub : boolSupport g ⊆ (boolSupport fS).image (dualParitySet A) := by
    intro U hU
    rw [mem_boolSupport, hg_coeff] at hU
    obtain ⟨γ, hγ, _⟩ := exists_ne_zero_of_sum_ne_zero hU
    exact mem_image.2 ⟨γ, (mem_filter.1 hγ).1, (mem_filter.1 hγ).2⟩
  have hg_lt : boolSparsity g < 2 ^ (m + 1) := by
    calc boolSparsity g = #(boolSupport g) := (card_boolSupport g).symm
      _ ≤ #((boolSupport fS).image (dualParitySet A)) := card_le_card hg_supp_sub
      _ ≤ #(boolSupport fS) := card_image_le
      _ = boolSparsity f := by rw [card_boolSupport, hfS_sp]
      _ < 2 ^ (m + 1) := hk_lt
  have hnot_odd : ¬Odd #{y : κ → Bool | g y = true} := by
    intro hodd
    have huniv := boolSupport_eq_univ_of_odd_card_true (by simp [κ]; omega) g hodd
    have hcard : boolSparsity g = 2 ^ (m + 1) := by
      rw [← card_boolSupport, huniv]; simp [κ]
    omega
  obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.1 hnot_odd
  refine ⟨(2 : ℤ) ^ (m - 1) - (c : ℤ), ?_⟩
  rw [← hg_empty, boolFourierCoeff_empty, boolWeight_eq_card_div]
  simp only [κ, Fintype.card_fin, hc, ← two_mul]
  have hpow1 : (2 : ℝ) ^ (m + 1) = 4 * (2 : ℝ) ^ (m - 1) := by
    rw [show m + 1 = 2 + (m - 1) by omega, pow_add]; norm_num
  have hzpow : (2 : ℝ) ^ (1 - (m : ℤ)) = ((2 : ℝ) ^ (m - 1))⁻¹ := by
    rw [show (1 - (m : ℤ)) = -(((m - 1 : ℕ) : ℤ)) by omega, zpow_neg, zpow_natCast]
  rw [hpow1, hzpow]
  have h2ne : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Absolute-value form of Fourier granularity: `|f̂(S)| = z * 2 ^ (1 - ⌊log₂ k(f)⌋)` for some
nonnegative integer `z : ℕ` whenever `k(f) ≥ 2`. -/
theorem exists_nat_mul_abs_boolFourierCoeff {f : (ι → Bool) → Bool}
    (hk : 2 ≤ boolSparsity f) (S : Finset ι) :
    ∃ z : ℕ,
      |boolFourierCoeff f S| = (z : ℝ) * (2 : ℝ) ^ (1 - (Nat.log 2 (boolSparsity f) : ℤ)) := by
  obtain ⟨z, hz⟩ := exists_int_mul_boolFourierCoeff hk S
  refine ⟨z.natAbs, ?_⟩
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (1 - (Nat.log 2 (boolSparsity f) : ℤ)) :=
    zpow_pos (by norm_num) _
  rw [hz, abs_mul, abs_of_pos h2pos]
  congr 1
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

/-- Every nonzero Fourier coefficient of a Boolean function with `k(f) ≥ 2` has magnitude at least
`2 ^ (1 - ⌊log₂ k(f)⌋) ≥ 2 / k(f)`. -/
theorem two_div_boolSparsity_le_abs_boolFourierCoeff {f : (ι → Bool) → Bool}
    (hk : 2 ≤ boolSparsity f) {S : Finset ι} (hS : S ∈ boolSupport f) :
    (2 : ℝ) / boolSparsity f ≤ |boolFourierCoeff f S| := by
  obtain ⟨z, hz⟩ := exists_nat_mul_abs_boolFourierCoeff hk S
  have hzne : z ≠ 0 := fun h0 ↦ mem_boolSupport.1 hS (abs_eq_zero.1 (by simp [hz, h0]))
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hzne
  set m := Nat.log 2 (boolSparsity f)
  have hpow_le : (2 : ℝ) ^ m ≤ boolSparsity f := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : boolSparsity f ≠ 0)
  have hzpow : (2 : ℝ) ^ (1 - (m : ℤ)) = 2 / (2 : ℝ) ^ m := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast, div_eq_mul_inv]
  calc (2 : ℝ) / boolSparsity f ≤ 2 / (2 : ℝ) ^ m :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow_le
    _ = 1 * (2 : ℝ) ^ (1 - (m : ℤ)) := by rw [one_mul, hzpow]
    _ ≤ (z : ℝ) * (2 : ℝ) ^ (1 - (m : ℤ)) := mul_le_mul_of_nonneg_right hz1 (by positivity)
    _ = |boolFourierCoeff f S| := hz.symm

/-- **Bernasconi–Codenotti inequality**: every Boolean function with `k(f) > 1` satisfies
`2 ^ deg_{𝔽₂}(f) ≤ k(f)`. -/
theorem two_pow_f2Degree_le_boolSparsity {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : 2 ^ f2Degree f ≤ boolSparsity f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d := f2Degree f
  by_cases hd0 : d = 0
  · rw [hd0, pow_zero]; omega
  by_cases hd1 : d = 1
  · rw [hd1, pow_one]; omega
  have hd2 : 2 ≤ d := by omega
  let p : (ι → Bool) → ZMod 2 := fun x ↦ bitVal (ZMod 2) (f x)
  have hp_mem : p ∈ lowDegree (ZMod 2) ι d := mem_lowDegree_totalDegree p
  have hp_not : p ∉ lowDegree (ZMod 2) ι (d - 1) := fun hmem ↦ by
    have hle : d ≤ d - 1 := totalDegree_le_of_mem_lowDegree hmem
    exact (Nat.sub_lt (by omega : 0 < d) zero_lt_one).not_ge hle
  have hexp : ∃ c : Finset ι → ZMod 2,
      (∀ T, d < #T → c T = 0) ∧ p = ∑ T : Finset ι, c T • monomial (ZMod 2) T := by
    refine Submodule.span_induction ?_ ⟨0, fun _ _ ↦ rfl, by simp⟩ ?_ ?_ hp_mem
    · rintro _ ⟨S, hS, rfl⟩
      refine ⟨fun T ↦ if T = S then 1 else 0, fun T hT ↦ ?_, by simp⟩
      have hne : T ≠ S := fun he ↦ by subst he; exact hT.not_ge hS
      simp [hne]
    · rintro _ _ _ _ ⟨c₁, hc₁, rfl⟩ ⟨c₂, hc₂, rfl⟩
      exact ⟨c₁ + c₂, fun T hT ↦ by simp [hc₁ T hT, hc₂ T hT], by simp [add_smul, sum_add_distrib]⟩
    · rintro a _ _ ⟨c₁, hc₁, rfl⟩
      exact ⟨fun T ↦ a * c₁ T, fun T hT ↦ by simp [hc₁ T hT], by simp [mul_smul, smul_sum]⟩
  obtain ⟨c, hc_hi, hpeq⟩ := hexp
  have hexD : ∃ D : Finset ι, #D = d ∧ c D ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp_not
    rw [hpeq]
    refine Submodule.sum_mem _ fun T _ ↦ ?_
    by_cases hTd : #T ≤ d - 1
    · exact Submodule.smul_mem _ _ (monomial_mem_lowDegree hTd)
    · have hc0 : c T = 0 := by
        by_cases hgt : d < #T
        · exact hc_hi T hgt
        · exact hall T (by omega)
      simp [hc0]
  obtain ⟨D, hD_card, hcD⟩ := hexD
  let ext : (D → Bool) → (ι → Bool) := fun y i ↦ if h : i ∈ D then y ⟨i, h⟩ else false
  let g : (D → Bool) → Bool := fun y ↦ f (ext y)
  have hodd : Odd #{y : D → Bool | g y = true} := by
    have hsum_zmod : (∑ y : D → Bool, p (ext y)) = c D := by
      simp_rw [hpeq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_comm]
      calc ∑ T : Finset ι, ∑ y : D → Bool, c T * monomial (ZMod 2) T (ext y)
          = ∑ T : Finset ι, c T * ∑ y : D → Bool, monomial (ZMod 2) T (ext y) :=
            sum_congr rfl fun T _ ↦ (mul_sum ..).symm
        _ = c D * ∑ y : D → Bool, monomial (ZMod 2) D (ext y) := by
            refine sum_eq_single D (fun T _ hTD ↦ ?_) fun h ↦ (h (mem_univ D)).elim
            by_cases hsub : T ⊆ D
            · have hlt : #T < #D := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hTD⟩)
              have hcnt : #{y : D → Bool | ∀ i ∈ T, ext y i = true} = 2 ^ (#D - #T) := by
                let TD : Finset D := univ.filter fun j ↦ j.1 ∈ T
                have hTD_card : #TD = #T :=
                  card_bij (fun j _ ↦ j.1) (fun j hj ↦ (mem_filter.1 hj).2)
                    (fun _ _ _ _ h ↦ Subtype.ext h) fun i hi ↦
                    ⟨⟨i, hsub hi⟩, mem_filter.2 ⟨mem_univ _, hi⟩, rfl⟩
                let compl := {j : D // j ∉ TD}
                let ψ : (compl → Bool) ≃ {y : D → Bool // ∀ i ∈ T, ext y i = true} :=
                  { toFun := fun r ↦ ⟨fun j ↦ if h : j ∈ TD then true else r ⟨j, h⟩, fun i hi ↦ by
                      have hiD : i ∈ D := hsub hi
                      have hjTD : (⟨i, hiD⟩ : D) ∈ TD := mem_filter.2 ⟨mem_univ _, hi⟩
                      simp [ext, hiD, hjTD]⟩
                    invFun := fun y j ↦ y.1 j.1
                    left_inv := fun r ↦ by
                      ext ⟨j, hj⟩; exact dite_eq_right_of_eq_false (eq_false hj)
                    right_inv := fun ⟨y, hy⟩ ↦ by
                      apply Subtype.ext; ext j
                      by_cases hj : j ∈ TD
                      · have h1 := hy j.1 (mem_filter.1 hj).2
                        simp only [ext, j.2, ↓reduceDIte] at h1
                        simp [hj, h1]
                      · simp [hj] }
                have hc1 : #{y : D → Bool | ∀ i ∈ T, ext y i = true} =
                    Fintype.card (compl → Bool) := by
                  simpa [Fintype.card_subtype] using (Fintype.card_congr ψ).symm
                have hc2 : Fintype.card compl = #D - #T := by
                  have := Fintype.card_subtype_compl (fun j : D ↦ j ∈ TD)
                  simp [compl, Fintype.card_coe, hTD_card]
                rw [hc1, Fintype.card_fun, Fintype.card_bool, hc2]
              have hsum0 : (∑ y : D → Bool, monomial (ZMod 2) T (ext y)) = 0 := by
                have hsf : (∑ y : D → Bool, monomial (ZMod 2) T (ext y)) =
                    ∑ y : D → Bool with ∀ i ∈ T, ext y i = true, (1 : ZMod 2) := by
                  rw [sum_filter]; refine sum_congr rfl fun y _ ↦ ?_; rw [monomial_apply]; congr
                rw [hsf, sum_const, nsmul_eq_mul, mul_one, hcnt, Nat.cast_pow]
                have h2 : ((2 : ℕ) : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
                rw [h2, zero_pow (by omega)]
              rw [hsum0, mul_zero]
            · obtain ⟨i, hiT, hiD⟩ := not_subset.1 hsub
              have hzero : ∀ y : D → Bool, monomial (ZMod 2) T (ext y) = 0 := fun y ↦ by
                rw [monomial_apply]
                have hnot : ¬ ∀ k ∈ T, ext y k = true := fun hall ↦ by
                  have := hall i hiT; simp [ext, hiD] at this
                simp [hnot]
              simp [hzero]
        _ = c D := by
            have hsum1 : (∑ y : D → Bool, monomial (ZMod 2) D (ext y)) = 1 := by
              have hunique : ∀ y : D → Bool, (∀ i ∈ D, ext y i = true) ↔ y = fun _ ↦ true := by
                intro y
                constructor
                · intro h; ext ⟨i, hi⟩; simpa [ext, hi] using h i hi
                · rintro rfl i hi; simp [ext, hi]
              simp_rw [monomial_apply, hunique]
              rw [sum_eq_single (fun _ ↦ true)
                (fun y _ hne ↦ ite_eq_right_of_eq_false _ _ (eq_false hne))
                (fun h ↦ (h (mem_univ _)).elim),
                ite_eq_left_of_eq_true _ _ (eq_true rfl)]
            rw [hsum1, mul_one]
    have hsum_card : (∑ y : D → Bool, p (ext y)) = (#{y : D → Bool | g y = true} : ZMod 2) := by
      have hterm : (∑ y : D → Bool, p (ext y)) =
          ∑ y : D → Bool, if g y = true then (1 : ZMod 2) else 0 :=
        sum_congr rfl fun y _ ↦ by cases hgy : g y <;> simp [p, g, hgy, bitVal]
      rw [hterm, sum_boole]
    rw [hsum_card] at hsum_zmod
    have hcD1 : c D = 1 := (ZMod2_eq_zero_or_one (c D)).resolve_left hcD
    rw [hcD1] at hsum_zmod
    rw [Nat.odd_iff]
    by_contra hnot
    have hev : Even #{y : D → Bool | g y = true} := Nat.even_iff.2 (by omega)
    obtain ⟨r, hr⟩ := hev
    rw [hr] at hsum_zmod
    push_cast at hsum_zmod
    have hself : (r : ZMod 2) + (r : ZMod 2) = 0 := CharTwo.add_self_eq_zero _
    rw [hself] at hsum_zmod
    exact zero_ne_one hsum_zmod
  have hgsupp : boolSupport g = univ :=
    boolSupport_eq_univ_of_odd_card_true (by rw [Fintype.card_coe, hD_card]; omega) g hodd
  have hg_sp : boolSparsity g = 2 ^ d := by
    rw [← card_boolSupport, hgsupp, card_univ, Fintype.card_finset, Fintype.card_coe, hD_card]
  let A : (D → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    { toFun := fun v i ↦ if h : i ∈ D then v ⟨i, h⟩ else 0
      map_add' := fun u v ↦ by ext i; by_cases h : i ∈ D <;> simp [h]
      map_smul' := fun a v ↦ by ext i; by_cases h : i ∈ D <;> simp [h] }
  have hext_eq : ext = applyF2Linear A := by
    ext y i
    rw [applyF2Linear_apply]
    simp only [ext, A, LinearMap.coe_mk, AddHom.coe_mk, bitStringZModEquiv_apply]
    by_cases h : i ∈ D <;> simp [h]
  have hg_sub : boolSupport g ⊆ (boolSupport f).image (dualParitySet A) := by
    intro U hU
    rw [mem_boolSupport] at hU
    unfold boolFourierCoeff g at hU
    have hfn : (fun y : D → Bool ↦ signVal (f (ext y))) =
        fun y ↦ signVal (f (applyF2Linear A y)) := by simp_rw [hext_eq]
    rw [hfn, fourierCoeff_comp_applyF2Linear A (fun x ↦ signVal (f x)) U] at hU
    obtain ⟨S, hS, hSne⟩ := exists_ne_zero_of_sum_ne_zero hU
    exact mem_image.2 ⟨S, mem_boolSupport.2 hSne, (mem_filter.1 hS).2⟩
  calc 2 ^ d = boolSparsity g := hg_sp.symm
    _ ≤ #((boolSupport f).image (dualParitySet A)) := card_le_card hg_sub
    _ ≤ boolSparsity f := card_image_le

/-- Logarithmic form of the Bernasconi–Codenotti bound: `deg_{𝔽₂}(f) ≤ log₂ k(f)` for every Boolean
function with `k(f) > 1`. -/
theorem f2Degree_le_logb_boolSparsity {f : (ι → Bool) → Bool}
    (hk : 1 < boolSparsity f) : (f2Degree f : ℝ) ≤ Real.logb 2 (boolSparsity f) := by
  have hpow : ((2 : ℝ) ^ f2Degree f) ≤ boolSparsity f := by
    exact_mod_cast two_pow_f2Degree_le_boolSparsity hk
  calc (f2Degree f : ℝ) = Real.logb 2 ((2 : ℝ) ^ f2Degree f) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 (boolSparsity f) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hpow

/-- Every Fourier coefficient of a bent Boolean function on `ι` has absolute value
`1 / √(2 ^ |ι|)`. -/
theorem IsBent.abs_boolFourierCoeff {f : (ι → Bool) → Bool} (hf : IsBent f) (S : Finset ι) :
    |boolFourierCoeff f S| = 1 / Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by
  have hsq_eq : ∀ T : Finset ι, boolFourierCoeff f T ^ 2 = boolFourierCoeff f S ^ 2 := fun T ↦ by
    rw [← sq_abs (boolFourierCoeff f T), ← sq_abs (boolFourierCoeff f S), hf T S]
  have hsum := sum_boolFourierCoeff_sq f
  simp_rw [hsq_eq] at hsum
  simp only [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat] at hsum
  have hsq : |boolFourierCoeff f S| ^ 2 = ((2 : ℝ) ^ Fintype.card ι)⁻¹ := by
    rw [sq_abs]
    exact eq_inv_of_mul_eq_one_right hsum
  calc |boolFourierCoeff f S| = Real.sqrt (|boolFourierCoeff f S| ^ 2) :=
        (Real.sqrt_sq (abs_nonneg _)).symm
    _ = Real.sqrt (((2 : ℝ) ^ Fintype.card ι)⁻¹) := by rw [hsq]
    _ = 1 / Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by rw [Real.sqrt_inv, one_div]

/-- Every bent function has full Fourier support. -/
theorem IsBent.boolSupport_eq_univ {f : (ι → Bool) → Bool} (hf : IsBent f) :
    boolSupport f = univ := by
  ext S
  simp only [mem_boolSupport, mem_univ, iff_true]
  intro h0
  have := hf.abs_boolFourierCoeff S
  rw [h0, abs_zero] at this
  have hpos : (0 : ℝ) < 1 / Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by positivity
  linarith

/-- Every bent function on `ι` has Fourier sparsity `2 ^ |ι|`. -/
theorem IsBent.boolSparsity_eq {f : (ι → Bool) → Bool} (hf : IsBent f) :
    boolSparsity f = 2 ^ Fintype.card ι := by
  rw [← card_boolSupport, hf.boolSupport_eq_univ, card_univ, Fintype.card_finset]

/-- Every bent function on `ι` has Fourier rank `|ι|`. -/
theorem IsBent.fourierRank_eq {f : (ι → Bool) → Bool} (hf : IsBent f) :
    fourierRank f = Fintype.card ι := by
  rw [fourierRank, hf.boolSupport_eq_univ, parityDim_univ]

/-- Every bent function on `ι` has weight `1/2 ± 1 / (2 √(2 ^ |ι|))`. -/
theorem IsBent.boolWeight_eq {f : (ι → Bool) → Bool} (hf : IsBent f) :
    boolWeight f = 1 / 2 - 1 / (2 * Real.sqrt ((2 : ℝ) ^ Fintype.card ι)) ∨
      boolWeight f = 1 / 2 + 1 / (2 * Real.sqrt ((2 : ℝ) ^ Fintype.card ι)) := by
  have habs := hf.abs_boolFourierCoeff ∅
  rw [boolFourierCoeff_empty] at habs
  have hs : 0 < Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by positivity
  rcases eq_or_eq_neg_of_abs_eq habs with h | h
  · left; field_simp at h ⊢; linarith
  · right; field_simp at h ⊢; linarith

/-- The canonical inner-product Boolean function on `Fin (2 * s)` bits. -/
def innerProductBent (s : ℕ) : (Fin (2 * s) → Bool) → Bool :=
  fun x ↦
    let e : Fin (s + s) ≃ Fin (2 * s) := finCongr (by omega)
    fstBits (x ∘ e) ⬝ᵥ sndBits (x ∘ e)

/-- `innerProductBent s` is bent for every `s : ℕ`. -/
theorem isBent_innerProductBent (s : ℕ) : IsBent (innerProductBent s) := by
  let e : Fin (s + s) ≃ Fin (2 * s) := finCongr (by omega)
  have habs : ∀ S : Finset (Fin (2 * s)), |boolFourierCoeff (innerProductBent s) S| =
      1 / (2 : ℝ) ^ s := by
    intro S
    unfold boolFourierCoeff innerProductBent
    have hcomp := fourierCoeff_comp_arrowCongr e.symm
      (fun z : BitString (s + s) ↦ signVal (fstBits z ⬝ᵥ sndBits z)) S
    simp only [Equiv.symm_symm] at hcomp
    have hfun : (fun x : Fin (2 * s) → Bool ↦ signVal (fstBits (x ∘ e) ⬝ᵥ sndBits (x ∘ e))) =
        fun y : Fin (2 * s) → Bool ↦
          signVal (fstBits (fun j ↦ y (e j)) ⬝ᵥ sndBits (fun j ↦ y (e j))) := rfl
    rw [hfun, hcomp, abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits, one_div]
  intro S T
  rw [habs S, habs T]

end CslibFrontier.BooleanFunction
