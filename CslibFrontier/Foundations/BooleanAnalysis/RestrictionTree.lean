/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegreePart
public import CslibFrontier.Foundations.BooleanAnalysis.Mobius
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multilinear Sparsity, Semi-Adaptive Restriction Trees, and Fourier Tail Decay

This module develops multilinear (De Morgan) monomial sparsity and semi-adaptive max-degree
restriction trees for real-valued functions on the Boolean hypercube `{0, 1}^ι`, together with
exponential decay of expected high-degree Fourier `ℓ₁`-mass under uniform fixed-size star
restrictions and masked-variable averaging.

## Main definitions

* `CslibFrontier.BooleanAnalysis.monomialCoeff`, `CslibFrontier.BooleanAnalysis.monomialSupport`,
  `CslibFrontier.BooleanAnalysis.sparsity`, `CslibFrontier.BooleanAnalysis.boolSparsity`:
  multilinear monomial coefficients, support family, and sparsity on `{0, 1}^ι`.
* `CslibFrontier.BooleanAnalysis.fourierSparsity`, `CslibFrontier.BooleanAnalysis.fourierL1Norm`,
  `CslibFrontier.BooleanAnalysis.fourierTailL1`: Fourier sparsity, spectral `ℓ₁`-norm, and
  high-degree Fourier `ℓ₁`-mass above level `k`.
* `CslibFrontier.BooleanAnalysis.RestrictionVal`, `CslibFrontier.BooleanAnalysis.Restriction`,
  `CslibFrontier.BooleanAnalysis.freeVars`, `CslibFrontier.BooleanAnalysis.restrictFun`,
  `CslibFrontier.BooleanAnalysis.IsMaxDegreeRestriction`: partial assignments in `{0, 1, *}` and
  max-degree restrictions.
* `CslibFrontier.BooleanAnalysis.SemiAdaptiveRestrictionTree`,
  `CslibFrontier.BooleanAnalysis.SemiAdaptiveRestrictionTree.IsMaxDegreeTree`: semi-adaptive
  restriction trees with fixed core variable set `V` and adaptive outside fixings.

## Main results

* `CslibFrontier.BooleanAnalysis.existsUnique_multilinear_rep`: existence and uniqueness of the
  multilinear polynomial representation in `MvPolynomial.restrictDegree ι ℝ 1`.
* `CslibFrontier.BooleanAnalysis.exists_semiAdaptiveMaxDegreeTree_of_sparsity` and
  `CslibFrontier.BooleanAnalysis.exists_semiAdaptiveMaxDegreeTree_depth_ge_log`: construction of a
  semi-adaptive max-degree restriction tree of depth `d` from shattered monomial supports satisfying
  `sparsity f ≤ (|ι| + 1) ^ d`.
* `CslibFrontier.BooleanAnalysis.expect_fourierTailL1_piecewise_le` and
  `CslibFrontier.BooleanAnalysis.expect_fourierTailL1_piecewise_le_two_zpow`: exponential decay of
  expected high-degree Fourier `ℓ₁`-mass under uniform `m`-star subsets and masked averaging.
-/

public section

open Finset MvPolynomial
open scoped BigOperators

namespace CslibFrontier.BooleanAnalysis

/-! ### 1. Multilinear Representation, De Morgan Sparsity, and Fourier `ℓ₁`-Measures -/

/-- Coefficient `a_S` of the multilinear monomial `∏_{i ∈ S} x_i` in the unique multilinear
polynomial representation of `f : (ι → Bool) → ℝ`. -/
@[expose]
def monomialCoeff {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  Cslib.BitString.subsetMobius (fun T ↦ f fun i ↦ decide (i ∈ T)) S

/-- Family of monomial supports `{S ⊆ ι | a_S ≠ 0}` of `f`. -/
@[expose]
noncomputable def monomialSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : Finset (Finset ι) :=
  univ.filter fun S ↦ monomialCoeff f S ≠ 0

/-- Multilinear (De Morgan) sparsity of `f : (ι → Bool) → ℝ`, i.e., the number of nonzero
coefficients in its unique multilinear expansion `∑_S a_S ∏_{i ∈ S} x_i`. -/
@[expose]
noncomputable def sparsity {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) : ℕ :=
  #(monomialSupport f)

/-- Multilinear (De Morgan) sparsity of a Boolean function `f : BooleanFunction n` viewed as
`{0, 1}`-valued over `ℝ`. -/
@[expose]
noncomputable def boolSparsity {n : ℕ} (f : Cslib.BooleanFunction n) : ℕ :=
  sparsity fun x ↦ Cslib.BitString.bitVal ℝ (f x)

/-- Membership in `monomialSupport f` holds iff `monomialCoeff f S ≠ 0`. -/
theorem mem_monomialSupport_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} {S : Finset ι} :
    S ∈ monomialSupport f ↔ monomialCoeff f S ≠ 0 := by
  simp [monomialSupport]

/-- Multilinear expansion `f(x) = ∑_S monomialCoeff f S * monomial ℝ S x`. -/
theorem eq_sum_monomialCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    f x = ∑ S : Finset ι, monomialCoeff f S * Cslib.BitString.monomial ℝ S x := by
  have h := congrFun (Cslib.BitString.eq_sum_subsetMobius_smul_monomial (R := ℝ) f) x
  simpa [monomialCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

/-- `f = 0` iff `sparsity f = 0`. -/
theorem sparsity_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → Bool) → ℝ} :
    sparsity f = 0 ↔ f = 0 := by
  rw [sparsity, monomialSupport, card_eq_zero, filter_eq_empty_iff]
  simp only [mem_univ, forall_true_left, Decidable.not_not, monomialCoeff]
  refine ⟨Cslib.BitString.eq_zero_of_subsetMobius_eq_zero, ?_⟩
  rintro rfl S
  have h := Cslib.BitString.subsetMobius_const_mul (ι := ι) (0 : ℝ) (fun _ ↦ (1 : ℝ)) S
  simpa using h

/-- `1 ≤ sparsity f` iff `f ≠ 0`. -/
theorem one_le_sparsity_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → Bool) → ℝ} :
    1 ≤ sparsity f ↔ f ≠ 0 := by
  rw [Nat.one_le_iff_ne_zero, not_iff_not, sparsity_eq_zero_iff]

/-- Characterization of `totalDegree f ≤ D` via vanishing of `monomialCoeff` above `D`. -/
theorem totalDegree_le_iff_monomialCoeff_eq_zero {ι : Type*} [Finite ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} {D : ℕ} :
    Cslib.BitString.totalDegree f ≤ D ↔ ∀ S : Finset ι, D < #S → monomialCoeff f S = 0 := by
  rw [Cslib.BitString.totalDegree_le_iff_mem_lowDegree,
    Cslib.BitString.mem_lowDegree_iff_subsetMobius_eq_zero]
  rfl

/-- A nonzero multilinear coefficient on `S` forces `#S ≤ totalDegree f`. -/
theorem card_le_totalDegree_of_monomialCoeff_ne_zero {ι : Type*} [Finite ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} {S : Finset ι} (h : monomialCoeff f S ≠ 0) :
    #S ≤ Cslib.BitString.totalDegree f := by
  by_contra hlt
  exact h ((totalDegree_le_iff_monomialCoeff_eq_zero.mp le_rfl) S (Nat.lt_of_not_ge hlt))

/-- Indicator exponent vector `ι →₀ ℕ` taking value `1` on `S` and `0` outside `S`. -/
noncomputable def multilinearExponent {ι : Type*} (S : Finset ι) : ι →₀ ℕ := by
  classical
  exact Finsupp.onFinset S (fun i ↦ if i ∈ S then 1 else 0)
    (fun i hi ↦ by by_contra h; simp [h] at hi)

private lemma multilinearExponent_apply {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) :
    multilinearExponent S i = if i ∈ S then 1 else 0 := by
  simp only [multilinearExponent, Finsupp.onFinset_apply]
  split_ifs <;> rfl

private lemma support_multilinearExponent {ι : Type*} (S : Finset ι) :
    (multilinearExponent S).support = S := by
  classical
  ext i
  simp [Finsupp.mem_support_iff, multilinearExponent_apply]

private lemma eq_multilinearExponent_support {ι : Type*} {d : ι →₀ ℕ}
    (hd : ∀ i, d i ≤ 1) :
    d = multilinearExponent d.support := by
  classical
  ext i
  rw [multilinearExponent_apply]
  by_cases hi : i ∈ d.support
  · simp only [hi, ↓reduceIte]
    have hpos : 0 < d i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hle := hd i
    omega
  · simp only [hi, ↓reduceIte]
    exact Decidable.not_not.mp (Finsupp.mem_support_iff.not.mp hi)

/-- For any `Q ∈ restrictDegree ι ℝ 1`, its coefficient on `multilinearExponent S` equals
`monomialCoeff (fun x ↦ eval (bitPoint x) Q) S`. -/
theorem coeff_multilinearExponent_eq_monomialCoeff {ι : Type*} [DecidableEq ι]
    {Q : MvPolynomial ι ℝ} (hQ : Q ∈ restrictDegree ι ℝ 1) (S : Finset ι) :
    Q.coeff (multilinearExponent S) =
      monomialCoeff (fun x ↦ eval (Cslib.BitString.bitPoint x) Q) S := by
  have hQdeg : ∀ s ∈ Q.support, ∀ i, s i ≤ 1 := by
    rwa [mem_restrictDegree] at hQ
  have heval_eq :
      (fun T : Finset ι ↦ eval (Cslib.BitString.bitPoint fun i ↦ decide (i ∈ T)) Q) =
        fun T ↦ ∑ d ∈ Q.support,
          Q.coeff d * Cslib.BitString.monomial ℝ d.support (fun i ↦ decide (i ∈ T)) := by
    funext T
    rw [eval_eq]
    refine sum_congr rfl fun d hd ↦ ?_
    congr 1
    rw [Cslib.BitString.monomial]
    refine prod_congr rfl fun i hi ↦ ?_
    have hd1 : d i = 1 := by
      have hpos : 0 < d i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      have hle : d i ≤ 1 := hQdeg d hd i
      omega
    rw [hd1, pow_one]
  rw [monomialCoeff, heval_eq, Cslib.BitString.subsetMobius_sum]
  simp_rw [Cslib.BitString.subsetMobius_const_mul, Cslib.BitString.subsetMobius_monomial]
  by_cases hmem : multilinearExponent S ∈ Q.support
  · rw [Finset.sum_eq_single (multilinearExponent S)]
    · simp [support_multilinearExponent]
    · intro d hd hne
      have hd_eq := eq_multilinearExponent_support (hQdeg d hd)
      have hsupp_ne : d.support ≠ S := fun hs ↦ hne (hd_eq.trans (hs ▸ rfl))
      simp [hsupp_ne]
    · intro h; exact absurd hmem h
  · rw [Finset.sum_eq_zero fun d hd ↦ ?_]
    · exact notMem_support_iff.mp hmem
    · have hd_eq := eq_multilinearExponent_support (hQdeg d hd)
      have hsupp_ne : d.support ≠ S := fun hs ↦ hmem (hs ▸ hd_eq ▸ hd)
      simp [hsupp_ne]

/-- Every function `f : (ι → Bool) → ℝ` on a finite coordinate set admits a unique multilinear
polynomial representation `Q ∈ restrictDegree ι ℝ 1` agreeing with `f` on `{0, 1}^ι`, namely
`multilinearExtension f`. -/
theorem existsUnique_multilinear_rep {ι : Type*} [Finite ι] (f : (ι → Bool) → ℝ) :
    ∃! Q : MvPolynomial ι ℝ,
      Q ∈ restrictDegree ι ℝ 1 ∧
        ∀ x : ι → Bool, eval (Cslib.BitString.bitPoint x) Q = f x := by
  classical
  cases nonempty_fintype ι
  refine ⟨Cslib.BitString.multilinearExtension f,
    ⟨Cslib.BitString.multilinearExtension_mem_restrictDegree f,
      Cslib.BitString.eval_multilinearExtension f⟩, ?_⟩
  rintro Q ⟨hQ1, hQeval⟩
  have hQdeg : ∀ s ∈ Q.support, ∀ i, s i ≤ 1 := by
    rwa [mem_restrictDegree] at hQ1
  have hMdeg : ∀ s ∈ (Cslib.BitString.multilinearExtension f).support, ∀ i, s i ≤ 1 := by
    have hm := Cslib.BitString.multilinearExtension_mem_restrictDegree f
    rwa [mem_restrictDegree] at hm
  ext d
  by_cases hd : ∀ i, d i ≤ 1
  · rw [eq_multilinearExponent_support hd,
      coeff_multilinearExponent_eq_monomialCoeff hQ1,
      coeff_multilinearExponent_eq_monomialCoeff
        (Cslib.BitString.multilinearExtension_mem_restrictDegree f)]
    congr 1
    funext x
    rw [hQeval x, Cslib.BitString.eval_multilinearExtension]
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    have h1 : d ∉ Q.support := fun hmem ↦
      not_le.mpr hi (hQdeg d hmem i)
    have h2 : d ∉ (Cslib.BitString.multilinearExtension f).support := fun hmem ↦
      not_le.mpr hi (hMdeg d hmem i)
    rw [notMem_support_iff.mp h1, notMem_support_iff.mp h2]

/-- The support size `#(multilinearExtension f).support` equals `sparsity f`. -/
theorem card_support_multilinearExtension_eq_sparsity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) :
    #(Cslib.BitString.multilinearExtension f).support = sparsity f := by
  have hdeg := Cslib.BitString.multilinearExtension_mem_restrictDegree f
  have hMdeg : ∀ s ∈ (Cslib.BitString.multilinearExtension f).support, ∀ i, s i ≤ 1 := by
    rwa [mem_restrictDegree] at hdeg
  rw [sparsity]
  refine Finset.card_bij (fun d _ ↦ d.support) ?_ ?_ ?_
  · intro d hd
    rw [mem_monomialSupport_iff]
    have hd_eq := eq_multilinearExponent_support (hMdeg d hd)
    have hcoeff := coeff_multilinearExponent_eq_monomialCoeff hdeg d.support
    rw [← hd_eq, funext (Cslib.BitString.eval_multilinearExtension f)] at hcoeff
    exact hcoeff ▸ mem_support_iff.mp hd
  · intro d₁ hd₁ d₂ hd₂ hsupp
    rw [eq_multilinearExponent_support (hMdeg d₁ hd₁),
      eq_multilinearExponent_support (hMdeg d₂ hd₂), hsupp]
  · intro S hS
    rw [mem_monomialSupport_iff] at hS
    refine ⟨multilinearExponent S, ?_, support_multilinearExponent S⟩
    rw [mem_support_iff,
      coeff_multilinearExponent_eq_monomialCoeff hdeg,
      funext (Cslib.BitString.eval_multilinearExtension f)]
    exact hS

/-- Fourier sparsity `‖f̂‖₀`: number of nonzero Fourier coefficients `f̂(S)`. -/
@[expose]
noncomputable def fourierSparsity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : ℕ :=
  #{S : Finset ι | Cslib.BitString.fourierCoeff f S ≠ 0}

/-- Fourier spectral `ℓ₁`-norm `‖f̂‖₁ = ∑_S |f̂(S)|`. -/
@[expose]
noncomputable def fourierL1Norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S : Finset ι, |Cslib.BitString.fourierCoeff f S|

/-- Fourier `ℓ₁`-mass at or above degree `k`: `‖f̂‖₁^{≥ k} = ∑_{|S| ≥ k} |f̂(S)|`. -/
@[expose]
noncomputable def fourierTailL1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S : Finset ι with k ≤ #S, |Cslib.BitString.fourierCoeff f S|

/-- Nonnegativity of `fourierTailL1`. -/
theorem fourierTailL1_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (f : (ι → Bool) → ℝ) :
    0 ≤ fourierTailL1 k f :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Sublinearity of `fourierTailL1` on finite linear combinations. -/
theorem fourierTailL1_sum_mul_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (k : ℕ)
    (c : α → ℝ) (g : α → (ι → Bool) → ℝ) :
    fourierTailL1 k (fun x ↦ ∑ i, c i * g i x) ≤
      ∑ i, |c i| * fourierTailL1 k (g i) := by
  simp only [fourierTailL1, Cslib.BitString.fourierCoeff_sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_le_sum fun S _ ↦ ?_
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact le_of_eq (sum_congr rfl fun i _ ↦ abs_mul (c i) _)

/-- Pointwise approximation error of `lowDegreePart k f` is bounded by `fourierTailL1 (k + 1) f`. -/
theorem abs_sub_lowDegreePart_le_fourierTailL1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    |f x - Cslib.BitString.lowDegreePart k f x| ≤ fourierTailL1 (k + 1) f := by
  have hf := (Cslib.BitString.sum_fourierCoeff_mul_chi f x).symm
  have hlow := (Cslib.BitString.sum_fourierCoeff_mul_chi
    (Cslib.BitString.lowDegreePart k f) x).symm
  have hdiff :
      f x - Cslib.BitString.lowDegreePart k f x =
        ∑ S : Finset ι with k + 1 ≤ #S,
          Cslib.BitString.fourierCoeff f S * Cslib.BitString.chi ℝ S x := by
    conv_lhs => rw [hf, hlow]
    rw [← sum_sub_distrib, sum_filter]
    refine sum_congr rfl fun S _ ↦ ?_
    rw [Cslib.BitString.fourierCoeff_lowDegreePart]
    by_cases hle : #S ≤ k
    · have hnot : ¬(k + 1 ≤ #S) := by omega
      simp [hle, hnot]
    · have hge : k + 1 ≤ #S := by omega
      simp [hle, hge]
  rw [hdiff, fourierTailL1]
  exact Cslib.BitString.abs_sum_mul_chi_le _ _ x

/-! ### 2. Restrictions and Semi-Adaptive Max-Degree Restriction Trees -/

/-- Value assigned to a coordinate by a Boolean restriction: fixed to `0`, fixed to `1`, or left
free (`*`). -/
inductive RestrictionVal : Type
  | zero : RestrictionVal
  | one : RestrictionVal
  | star : RestrictionVal
  deriving DecidableEq, Repr, Inhabited

instance : Fintype RestrictionVal where
  elems := {.zero, .one, .star}
  complete x := by cases x <;> simp

/-- A restriction on coordinate set `ι` is a map `ι → {0, 1, *}`. -/
abbrev Restriction (ι : Type*) : Type _ := ι → RestrictionVal

/-- Set `ρ⁻¹(*)` of free coordinates under `ρ`. -/
@[expose]
def freeVars {ι : Type*} [Fintype ι] (ρ : Restriction ι) : Finset ι :=
  univ.filter fun i ↦ ρ i = .star

@[simp]
theorem mem_freeVars_iff {ι : Type*} [Fintype ι] {ρ : Restriction ι} {i : ι} :
    i ∈ freeVars ρ ↔ ρ i = .star := by
  simp [freeVars]

/-- Evaluates a restricted input vector on `x : ι → Bool`, replacing fixed coordinates by `false`
or `true` and keeping `.star` coordinates as `x i`. -/
@[expose]
def applyRestriction {ι : Type*} (ρ : Restriction ι) (x : ι → Bool) (i : ι) : Bool :=
  match ρ i with
  | .zero => false
  | .one => true
  | .star => x i

/-- Restriction `f|_ρ` of a function `f : (ι → Bool) → α` under `ρ`. -/
@[expose]
def restrictFun {ι α : Type*} (f : (ι → Bool) → α) (ρ : Restriction ι) (x : ι → Bool) : α :=
  f (applyRestriction ρ x)

/-- Restriction `Q|_ρ` of a multivariate polynomial `Q ∈ MvPolynomial ι ℝ` obtained by substituting
`0` or `1` for fixed variables and `X i` for free variables. -/
noncomputable def restrictMvPoly {ι : Type*} (Q : MvPolynomial ι ℝ)
    (ρ : Restriction ι) : MvPolynomial ι ℝ :=
  aeval (fun i ↦ match ρ i with
    | .zero => 0
    | .one => 1
    | .star => X i) Q

/-- `restrictMvPoly` commutes with evaluation at Boolean points. -/
theorem eval_restrictMvPoly {ι : Type*} (Q : MvPolynomial ι ℝ) (ρ : Restriction ι)
    (x : ι → Bool) :
    eval (Cslib.BitString.bitPoint x) (restrictMvPoly Q ρ) =
      restrictFun (fun y ↦ eval (Cslib.BitString.bitPoint y) Q) ρ x := by
  let φ : MvPolynomial ι ℝ →ₐ[ℝ] ℝ :=
    (aeval (Cslib.BitString.bitPoint x)).comp
      (aeval fun i : ι ↦ match ρ i with
        | .zero => (0 : MvPolynomial ι ℝ)
        | .one => 1
        | .star => X i)
  let ψ : MvPolynomial ι ℝ →ₐ[ℝ] ℝ :=
    aeval (Cslib.BitString.bitPoint (applyRestriction ρ x))
  have hφψ : φ = ψ := by
    ext i
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X]
    cases h : ρ i <;> simp [applyRestriction, h, Cslib.BitString.bitPoint]
  have hcongr := DFunLike.congr_fun hφψ Q
  simpa [φ, ψ, restrictMvPoly, restrictFun, aeval_def] using hcongr

/-- A restriction `ρ` is a *max-degree restriction* of `f` if `totalDegree (f|_ρ) = |ρ⁻¹(*)|`. -/
@[expose]
def IsMaxDegreeRestriction {ι : Type*} [Fintype ι]
    (f : (ι → Bool) → ℝ) (ρ : Restriction ι) : Prop :=
  Cslib.BitString.totalDegree (restrictFun f ρ) = #(freeVars ρ)

/-- The degree of any restricted function `f|_ρ` is at most `#(freeVars ρ)`. -/
theorem totalDegree_restrictFun_le_card_freeVars {ι : Type*} [Fintype ι]
    (f : (ι → Bool) → ℝ) (ρ : Restriction ι) :
    Cslib.BitString.totalDegree (restrictFun f ρ) ≤ #(freeVars ρ) := by
  classical
  rw [Cslib.BitString.totalDegree_le_iff_mem_lowDegree]
  have hf :
      restrictFun f ρ =
        ∑ M : Finset ι,
          (monomialCoeff f M *
            ∏ i ∈ M \ freeVars ρ,
              Cslib.BitString.bitVal ℝ (applyRestriction ρ (fun _ ↦ false) i)) •
            Cslib.BitString.monomial ℝ (M ∩ freeVars ρ) := by
    funext x
    rw [restrictFun, eq_sum_monomialCoeff f (applyRestriction ρ x), Finset.sum_apply]
    refine sum_congr rfl fun M _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, Cslib.BitString.monomial]
    rw [mul_assoc]
    congr 1
    rw [← prod_inter_mul_prod_sdiff M (freeVars ρ), mul_comm]
    congr 1
    · refine prod_congr rfl fun i hi ↦ ?_
      have hnot : ρ i ≠ .star := by
        have := (mem_sdiff.mp hi).2
        rwa [mem_freeVars_iff] at this
      cases hρ : ρ i with
      | zero => simp [applyRestriction, hρ]
      | one => simp [applyRestriction, hρ]
      | star => exact absurd hρ hnot
    · refine prod_congr rfl fun i hi ↦ ?_
      have hs : ρ i = .star := mem_freeVars_iff.mp (mem_inter.mp hi).2
      simp [applyRestriction, hs]
  rw [hf]
  refine Submodule.sum_mem _ fun M _ ↦ Submodule.smul_mem _ _ ?_
  exact Cslib.BitString.monomial_mem_lowDegree (card_le_card inter_subset_right)

/-- A *semi-adaptive restriction tree* of depth `d` on variable set `ι` consists of a core variable
set `coreVars` of size `d` and a family of `2 ^ d` restrictions fixing all non-core variables to
`{0, 1}` with a unique restriction extending every `{0, *}`-assignment on `coreVars`. -/
@[ext]
structure SemiAdaptiveRestrictionTree (ι : Type*) [Fintype ι] (d : ℕ) where
  /-- Fixed set `V` of core variables. -/
  coreVars : Finset ι
  /-- `|V| = d`. -/
  card_coreVars : #coreVars = d
  /-- Collection `𝒟` of restrictions in the tree. -/
  restrictions : Finset (Restriction ι)
  /-- `|𝒟| = 2 ^ d`. -/
  card_restrictions : #restrictions = 2 ^ d
  /-- Every variable outside `coreVars` is fixed to `0` or `1` in every restriction of `𝒟`. -/
  fixed_outside : ∀ ρ ∈ restrictions, ∀ i ∉ coreVars, ρ i = .zero ∨ ρ i = .one
  /-- Every `{0, *}`-assignment `α : coreVars → Bool` (`false` = `0`, `true` = `*`) extends
  uniquely to a restriction in `𝒟`. -/
  existsUnique_of_coreAssign :
    ∀ α : coreVars → Bool,
      ∃! ρ, ρ ∈ restrictions ∧ ∀ i : coreVars, ρ i.1 = if α i then .star else .zero

instance {ι : Type*} [Fintype ι] : Nonempty (SemiAdaptiveRestrictionTree ι 0) :=
  ⟨{ coreVars := ∅
     card_coreVars := card_empty
     restrictions := {fun _ ↦ .zero}
     card_restrictions := card_singleton _
     fixed_outside := fun ρ hρ _ _ ↦ Or.inl (by rw [mem_singleton.mp hρ])
     existsUnique_of_coreAssign := fun α ↦
       ⟨fun _ ↦ .zero,
         ⟨mem_singleton_self _, fun ⟨i, hi⟩ ↦ absurd hi (notMem_empty i)⟩,
         fun _ ⟨hρ, _⟩ ↦ mem_singleton.mp hρ⟩ }⟩

/-- Helper constructor building a `SemiAdaptiveRestrictionTree` from a core set `V` (`#V = d`) and
an outside-fixing rule `fixOut : (V → Bool) → ι → Bool`. -/
noncomputable def SemiAdaptiveRestrictionTree.ofFixing {ι : Type*} [Fintype ι] {d : ℕ}
    (V : Finset ι) (hVd : #V = d)
    (fixOut : (V → Bool) → ι → Bool) : SemiAdaptiveRestrictionTree ι d := by
  classical
  let mkRho (α : V → Bool) : Restriction ι :=
    fun i ↦ if hi : i ∈ V then (if α ⟨i, hi⟩ then .star else .zero)
      else (if fixOut α i then .one else .zero)
  have hinj : Function.Injective mkRho := by
    intro α₁ α₂ hfg
    funext ⟨i, hi⟩
    have := congrFun hfg i
    simp only [mkRho, hi, ↓reduceDIte] at this
    cases h1 : α₁ ⟨i, hi⟩ <;> cases h2 : α₂ ⟨i, hi⟩ <;> simp_all
  exact
    { coreVars := V
      card_coreVars := hVd
      restrictions := univ.image mkRho
      card_restrictions := by
        rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_coe, hVd]
      fixed_outside := by
        intro ρ hρ i hi
        obtain ⟨α, -, rfl⟩ := mem_image.mp hρ
        simp only [mkRho, hi, ↓reduceDIte]
        cases fixOut α i <;> simp
      existsUnique_of_coreAssign := by
        intro α
        refine ⟨mkRho α, ⟨mem_image_of_mem _ (mem_univ α), fun ⟨i, hi⟩ ↦ by simp [mkRho, hi]⟩, ?_⟩
        rintro ρ ⟨hρ, hcore⟩
        obtain ⟨β, -, rfl⟩ := mem_image.mp hρ
        have hαβ : β = α := by
          funext ⟨i, hi⟩
          have := hcore ⟨i, hi⟩
          simp only [mkRho, hi, ↓reduceDIte] at this
          cases h1 : β ⟨i, hi⟩ <;> cases h2 : α ⟨i, hi⟩ <;> simp_all
        rw [hαβ] }

private lemma mem_ofFixing {ι : Type*} [Fintype ι] {d : ℕ}
    {V : Finset ι} {hVd : #V = d} {fixOut : (V → Bool) → ι → Bool}
    {ρ : Restriction ι} (hρ : ρ ∈ (SemiAdaptiveRestrictionTree.ofFixing V hVd fixOut).restrictions)
      :
    ∃ α : V → Bool,
      (∀ (i : ι) (hi : i ∈ V), ρ i = if α ⟨i, hi⟩ then .star else .zero) ∧
      (∀ i ∉ V, ρ i = if fixOut α i then .one else .zero) := by
  classical
  simp only [SemiAdaptiveRestrictionTree.ofFixing, mem_image, mem_univ, true_and] at hρ
  obtain ⟨α, rfl⟩ := hρ
  exact ⟨α, fun i hi ↦ by simp [hi], fun i hi ↦ by simp [hi]⟩

/-- `SemiAdaptiveRestrictionTree ι d` is nonempty whenever `d ≤ Fintype.card ι`. -/
theorem nonempty_semiAdaptiveRestrictionTree {ι : Type*} [Fintype ι] {d : ℕ}
    (h : d ≤ Fintype.card ι) :
    Nonempty (SemiAdaptiveRestrictionTree ι d) := by
  have huniv : d ≤ #(univ : Finset ι) := by rwa [card_univ]
  obtain ⟨V, -, hVd⟩ := exists_subset_card_eq huniv
  exact ⟨SemiAdaptiveRestrictionTree.ofFixing V hVd (fun _ _ ↦ false)⟩

/-- `T` is a *semi-adaptive max-degree restriction tree* for `f` if every `ρ ∈ T.restrictions` is a
max-degree restriction of `f`. -/
@[expose]
def SemiAdaptiveRestrictionTree.IsMaxDegreeTree {ι : Type*} [Fintype ι] {d : ℕ}
    (T : SemiAdaptiveRestrictionTree ι d) (f : (ι → Bool) → ℝ) : Prop :=
  ∀ ρ ∈ T.restrictions, IsMaxDegreeRestriction f ρ

/-- Subset-indexed bijection between `{S ⊆ T.coreVars}` and `T.restrictions`: for every
`S ⊆ T.coreVars`, there is a unique `ρ ∈ T.restrictions` whose free-variable set `freeVars ρ`
equals `S`. -/
theorem SemiAdaptiveRestrictionTree.existsUnique_freeVars_eq {ι : Type*} [Fintype ι] {d : ℕ}
    (T : SemiAdaptiveRestrictionTree ι d) {S : Finset ι} (hS : S ⊆ T.coreVars) :
    ∃! ρ, ρ ∈ T.restrictions ∧ freeVars ρ = S := by
  classical
  let α : T.coreVars → Bool := fun i ↦ decide (i.1 ∈ S)
  obtain ⟨ρ₀, ⟨hρ₀_mem, hρ₀_core⟩, hρ₀_uniq⟩ := T.existsUnique_of_coreAssign α
  have hfree₀ : freeVars ρ₀ = S := by
    ext i
    rw [mem_freeVars_iff]
    by_cases hi : i ∈ T.coreVars
    · have h := hρ₀_core ⟨i, hi⟩
      simp only [α] at h
      by_cases hiS : i ∈ S <;> simp [h, hiS]
    · have hout := T.fixed_outside ρ₀ hρ₀_mem i hi
      have hiS : i ∉ S := fun h ↦ hi (hS h)
      rcases hout with h0 | h1
      · simp [h0, hiS]
      · simp [h1, hiS]
  refine ⟨ρ₀, ⟨hρ₀_mem, hfree₀⟩, ?_⟩
  rintro ρ ⟨hρ_mem, hfree⟩
  refine hρ₀_uniq ρ ⟨hρ_mem, fun i ↦ ?_⟩
  by_cases hiS : i.1 ∈ S
  · have hstar : ρ i.1 = .star := mem_freeVars_iff.mp (hfree ▸ hiS)
    simp [α, hiS, hstar]
  · have hnotstar : ρ i.1 ≠ .star := fun hs ↦ hiS (hfree ▸ mem_freeVars_iff.mpr hs)
    let chooseFn : (T.coreVars → Bool) → Restriction ι :=
      fun β ↦ (T.existsUnique_of_coreAssign β).choose
    have hinj : Function.Injective chooseFn := by
      intro β₁ β₂ heq
      funext j
      have h1 := (T.existsUnique_of_coreAssign β₁).choose_spec.1.2 j
      have h2 := (T.existsUnique_of_coreAssign β₂).choose_spec.1.2 j
      change chooseFn β₁ j.1 = _ at h1
      change chooseFn β₂ j.1 = _ at h2
      rw [heq] at h1
      cases b1 : β₁ j <;> cases b2 : β₂ j <;> simp_all
    let img := univ.image chooseFn
    have himg_sub : img ⊆ T.restrictions := by
      intro r hr
      obtain ⟨β, -, rfl⟩ := mem_image.mp hr
      exact (T.existsUnique_of_coreAssign β).choose_spec.1.1
    have himg_card : #img = #T.restrictions := by
      rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_coe, T.card_coreVars, T.card_restrictions]
    have himg_eq : img = T.restrictions := eq_of_subset_of_card_le himg_sub himg_card.ge
    have hρ_img : ρ ∈ img := himg_eq.symm ▸ hρ_mem
    obtain ⟨β, -, hβeq⟩ := mem_image.mp hρ_img
    have hβj := (T.existsUnique_of_coreAssign β).choose_spec.1.2 i
    change chooseFn β i.1 = _ at hβj
    rw [hβeq] at hβj
    cases hb : β i with
    | false =>
      rw [hb] at hβj
      simp [α, hiS, hβj]
    | true =>
      rw [hb] at hβj
      exact absurd (by simpa using hβj) hnotstar

/-- **Sauer–Shelah–Perles Max-Degree Restriction Tree Theorem**: every nonzero function
`f : (ι → Bool) → ℝ` admits a semi-adaptive max-degree restriction tree of depth `d` with
`sparsity f ≤ (|ι| + 1) ^ d` (specifically `d = (monomialSupport f).vcDim`). -/
theorem exists_semiAdaptiveMaxDegreeTree_of_sparsity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : f ≠ 0) :
    ∃ (d : ℕ) (T : SemiAdaptiveRestrictionTree ι d),
      T.IsMaxDegreeTree f ∧ sparsity f ≤ (Fintype.card ι + 1) ^ d := by
  have hne : (monomialSupport f).Nonempty :=
    card_pos.mp (Nat.pos_of_ne_zero (mt sparsity_eq_zero_iff.mp hf))
  have hshat_ne : (monomialSupport f).shatterer.Nonempty :=
    ⟨∅, mem_shatterer.mpr (shatters_empty.mpr hne)⟩
  obtain ⟨V, hV_mem, hV_sup⟩ := exists_mem_eq_sup (monomialSupport f).shatterer hshat_ne card
  have hV_shat : (monomialSupport f).Shatters V := mem_shatterer.mp hV_mem
  have hV_vc : #V = (monomialSupport f).vcDim := hV_sup.symm
  -- Bound `sparsity f ≤ (|ι| + 1) ^ #V` by Sauer–Shelah–Perles.
  have hssp : sparsity f ≤ (Fintype.card ι + 1) ^ #V := by
    have h1 : #(monomialSupport f) ≤ #(monomialSupport f).shatterer :=
      card_le_card_shatterer _
    have h2 : #(monomialSupport f).shatterer ≤
        ∑ k ∈ Iic (monomialSupport f).vcDim, (Fintype.card ι).choose k :=
      card_shatterer_le_sum_vcDim
    have h3 : Iic (monomialSupport f).vcDim = range (#V + 1) := by
      rw [hV_vc, Nat.range_succ_eq_Iic]
    rw [sparsity]
    exact h1.trans (h2.trans (h3 ▸ Cslib.sum_range_choose_le_add_one_pow (Fintype.card ι) #V))
  -- For each `α : V → Bool`, choose a minimum-cardinality `M₀ ∈ monomialSupport f` with `V ∩ M₀ =
  -- S_α`.
  let coreSet (α : V → Bool) : Finset ι :=
    univ.filter fun i ↦ ∃ hi : i ∈ V, α ⟨i, hi⟩ = true
  have hcore_sub (α : V → Bool) : coreSet α ⊆ V := by
    intro i hi
    obtain ⟨hV, -⟩ := (mem_filter.mp hi).2
    exact hV
  have hfib_ne (α : V → Bool) :
      ((monomialSupport f).filter fun M ↦ V ∩ M = coreSet α).Nonempty := by
    obtain ⟨M, hM, hVM⟩ := hV_shat.subset_iff.mp (hcore_sub α)
    exact ⟨M, mem_filter.mpr ⟨hM, hVM⟩⟩
  let witnessM (α : V → Bool) : Finset ι :=
    (exists_min_image ((monomialSupport f).filter fun M ↦ V ∩ M = coreSet α) card
      (hfib_ne α)).choose
  have hwitness_spec (α : V → Bool) :
      witnessM α ∈ monomialSupport f ∧
        V ∩ witnessM α = coreSet α ∧
        ∀ M ∈ monomialSupport f, V ∩ M = coreSet α → #(witnessM α) ≤ #M := by
    have h := (exists_min_image ((monomialSupport f).filter fun M ↦ V ∩ M = coreSet α) card
      (hfib_ne α)).choose_spec
    obtain ⟨hmem, hmin⟩ := h
    obtain ⟨hsupp, hinter⟩ := mem_filter.mp hmem
    exact ⟨hsupp, hinter, fun M hMs hMi ↦ hmin M (mem_filter.mpr ⟨hMs, hMi⟩)⟩
  let T := SemiAdaptiveRestrictionTree.ofFixing V rfl (fun α i ↦ decide (i ∈ witnessM α))
  refine ⟨#V, T, ?_, hssp⟩
  intro ρ₀ hρ
  obtain ⟨α₀, hρ₀_inside, hρ₀_out_bool⟩ := mem_ofFixing hρ
  set S : Finset ι := coreSet α₀
  set M₀ : Finset ι := witnessM α₀
  obtain ⟨hM₀_mem, hVM₀, hM₀_min⟩ := hwitness_spec α₀
  have hρ₀_outside : ∀ i ∉ V, ρ₀ i = if i ∈ M₀ then .one else .zero := by
    intro i hi
    rw [hρ₀_out_bool i hi]
    by_cases hiM : i ∈ M₀ <;> simp [M₀, hiM]
  have hfree_eq : freeVars ρ₀ = S := by
    ext i
    rw [mem_freeVars_iff]
    by_cases hi : i ∈ V
    · rw [hρ₀_inside i hi]
      simp only [S, coreSet, mem_filter, mem_univ, true_and]
      cases hα : α₀ ⟨i, hi⟩ <;> simp [hi, hα]
    · rw [hρ₀_outside i hi]
      simp only [S, coreSet, mem_filter, mem_univ, true_and]
      by_cases hiM : i ∈ M₀ <;> simp [hi, hiM]
  rw [IsMaxDegreeRestriction, hfree_eq]
  refine le_antisymm ?_ ?_
  · have hle := totalDegree_restrictFun_le_card_freeVars f ρ₀
    rwa [hfree_eq] at hle
  · refine card_le_totalDegree_of_monomialCoeff_ne_zero ?_
    have hval :
        (fun U : Finset ι ↦ restrictFun f ρ₀ (fun i ↦ decide (i ∈ U))) =
          fun U ↦ ∑ M : Finset ι,
            (if V ∩ M ⊆ S ∧ M \ V ⊆ M₀ then monomialCoeff f M else 0) *
              Cslib.BitString.monomial ℝ (V ∩ M) (fun i ↦ decide (i ∈ U)) := by
      funext U
      rw [restrictFun, eq_sum_monomialCoeff f]
      refine sum_congr rfl fun M _ ↦ ?_
      by_cases hcond : V ∩ M ⊆ S ∧ M \ V ⊆ M₀
      · simp only [hcond, and_self, ↓reduceIte]
        congr 1
        rw [Cslib.BitString.monomial, Cslib.BitString.monomial]
        rw [← prod_inter_mul_prod_sdiff M V, inter_comm M V]
        have hdiff_one :
            ∏ i ∈ M \ V, Cslib.BitString.bitVal ℝ
              (applyRestriction ρ₀ (fun j ↦ decide (j ∈ U)) i) = 1 := by
          refine prod_eq_one fun i hi ↦ ?_
          have hiV : i ∉ V := (mem_sdiff.mp hi).2
          have hiM₀ : i ∈ M₀ := hcond.2 hi
          have hρi := hρ₀_outside i hiV
          simp [applyRestriction, hρi, hiM₀]
        rw [hdiff_one, mul_one]
        refine prod_congr rfl fun i hi ↦ ?_
        have hiS : i ∈ S := hcond.1 hi
        have hiV : i ∈ V := (mem_inter.mp hi).1
        obtain ⟨_, hαi⟩ := (mem_filter.mp hiS).2
        have hρi := hρ₀_inside i hiV
        simp [applyRestriction, hρi, hαi]
      · simp only [hcond, ↓reduceIte, zero_mul]
        rw [not_and_or] at hcond
        rcases hcond with hnotS | hnotM₀
        · obtain ⟨i, hiVM, hiS⟩ := not_subset.mp hnotS
          have hiV : i ∈ V := (mem_inter.mp hiVM).1
          have hiM : i ∈ M := (mem_inter.mp hiVM).2
          have hαf : α₀ ⟨i, hiV⟩ = false := by
            cases hα : α₀ ⟨i, hiV⟩
            · rfl
            · exact absurd (mem_filter.mpr ⟨mem_univ i, ⟨hiV, hα⟩⟩) hiS
          have hzero : Cslib.BitString.bitVal ℝ
              (applyRestriction ρ₀ (fun j ↦ decide (j ∈ U)) i) = 0 := by
            have hρi := hρ₀_inside i hiV
            simp [applyRestriction, hρi, hαf]
          rw [Cslib.BitString.monomial, prod_eq_zero hiM hzero, mul_zero]
        · obtain ⟨i, hiMV, hiM₀⟩ := not_subset.mp hnotM₀
          have hiM : i ∈ M := (mem_sdiff.mp hiMV).1
          have hiV : i ∉ V := (mem_sdiff.mp hiMV).2
          have hzero : Cslib.BitString.bitVal ℝ
              (applyRestriction ρ₀ (fun j ↦ decide (j ∈ U)) i) = 0 := by
            have hρi := hρ₀_outside i hiV
            simp [applyRestriction, hρi, hiM₀]
          rw [Cslib.BitString.monomial, prod_eq_zero hiM hzero, mul_zero]
    have hmob : monomialCoeff (restrictFun f ρ₀) S = monomialCoeff f M₀ := by
      rw [monomialCoeff, hval, Cslib.BitString.subsetMobius_sum]
      simp_rw [Cslib.BitString.subsetMobius_const_mul, Cslib.BitString.subsetMobius_monomial]
      rw [Finset.sum_eq_single M₀]
      · have hVM₀' : V ∩ M₀ = S := hVM₀
        have hsub2 : M₀ \ V ⊆ M₀ := sdiff_subset
        simp [hsub2, hVM₀']
      · intro M _ hMM₀
        by_cases hVMS : V ∩ M = S
        · by_cases hcond : V ∩ M ⊆ S ∧ M \ V ⊆ M₀
          · have hsubM₀ : M ⊆ M₀ := by
              intro j hj
              by_cases hjV : j ∈ V
              · have hjS : j ∈ S := hVMS ▸ mem_inter.mpr ⟨hjV, hj⟩
                have hVM₀' : V ∩ M₀ = S := hVM₀
                exact (mem_inter.mp (hVM₀'.symm ▸ hjS)).2
              · exact hcond.2 (mem_sdiff.mpr ⟨hj, hjV⟩)
            have hlt : #M < #M₀ :=
              card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubM₀, hMM₀⟩)
            have hnot_supp : M ∉ monomialSupport f := fun hMs ↦
              not_le.mpr hlt (hM₀_min M hMs hVMS)
            have hcoeff0 : monomialCoeff f M = 0 :=
              Decidable.not_not.mp (mem_monomialSupport_iff.not.mp hnot_supp)
            simp [hcoeff0]
          · rw [ite_eq_right hcond]
            simp
        · simp [hVMS]
      · intro h; exact absurd (mem_univ M₀) h
    rw [hmob]
    exact mem_monomialSupport_iff.mp hM₀_mem

/-- Logarithmic depth corollary of `exists_semiAdaptiveMaxDegreeTree_of_sparsity` for `|ι| ≥ 2`:
`d ≥ (1 / 2) * log(sparsity f) / log |ι|`. -/
theorem exists_semiAdaptiveMaxDegreeTree_depth_ge_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : f ≠ 0) (hn : 2 ≤ Fintype.card ι) :
    ∃ (d : ℕ) (T : SemiAdaptiveRestrictionTree ι d),
      T.IsMaxDegreeTree f ∧
        (1 / 2 : ℝ) * (Real.log (sparsity f) / Real.log (Fintype.card ι)) ≤ d := by
  obtain ⟨d, T, hT, hssp⟩ := exists_semiAdaptiveMaxDegreeTree_of_sparsity hf
  refine ⟨d, T, hT, ?_⟩
  have hs_pos : 1 ≤ sparsity f := one_le_sparsity_iff.mpr hf
  set n := Fintype.card ι
  have hn1_le_sq : n + 1 ≤ n ^ 2 := by nlinarith
  have hpow : sparsity f ≤ (n ^ 2) ^ d :=
    hssp.trans (Nat.pow_le_pow_left hn1_le_sq d)
  rw [← pow_mul] at hpow
  have hpowR : (sparsity f : ℝ) ≤ (n : ℝ) ^ (2 * d) := by exact_mod_cast hpow
  have hsR_pos : (0 : ℝ) < sparsity f := by exact_mod_cast hs_pos
  have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  have hlog := Real.log_le_log hsR_pos hpowR
  rw [Real.log_pow] at hlog
  rw [mul_div_assoc', div_le_iff₀ hlogn_pos]
  push_cast at hlog
  linarith

/-! ### 3. Expected High-Degree Fourier `ℓ₁`-Tail Decay Under Uniform `m`-Star Restrictions -/

private lemma choose_sub_le_pow_mul_choose :
    ∀ t {m d : ℕ}, t ≤ m → m ≤ d →
      (((d - t).choose (m - t) : ℕ) : ℝ) ≤
        ((m : ℝ) / (d : ℝ)) ^ t * ((d.choose m : ℕ) : ℝ)
  | 0, m, d, _, _ => by simp
  | t + 1, m, d, htm, hmd => by
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hdt_pos : (0 : ℝ) < (d - t : ℕ) := by exact_mod_cast (by omega : 0 < d - t)
    have hih := choose_sub_le_pow_mul_choose t (by omega : t ≤ m) hmd
    have hstep_nat :
        (d - t) * (d - (t + 1)).choose (m - (t + 1)) =
          (d - t).choose (m - t) * (m - t) := by
      have h1 : d - t = (d - (t + 1)) + 1 := by omega
      have h2 : m - t = (m - (t + 1)) + 1 := by omega
      conv_lhs => rw [h1]
      conv_rhs => rw [h1, h2]
      exact Nat.add_one_mul_choose_eq (d - (t + 1)) (m - (t + 1))
    have hstepR :
        ((d - t : ℕ) : ℝ) * (((d - (t + 1)).choose (m - (t + 1)) : ℕ) : ℝ) =
          (((d - t).choose (m - t) : ℕ) : ℝ) * ((m - t : ℕ) : ℝ) := by
      exact_mod_cast hstep_nat
    have hfrac : ((m - t : ℕ) : ℝ) / ((d - t : ℕ) : ℝ) ≤ (m : ℝ) / (d : ℝ) := by
      rw [div_le_div_iff₀ hdt_pos hd_pos]
      have hm_sub : ((m - t : ℕ) : ℝ) = (m : ℝ) - (t : ℝ) := Nat.cast_sub (by omega)
      have hd_sub : ((d - t : ℕ) : ℝ) = (d : ℝ) - (t : ℝ) := Nat.cast_sub (by omega)
      rw [hm_sub, hd_sub]
      have hmdR : (m : ℝ) ≤ d := by exact_mod_cast hmd
      have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith
    have h1 :
        (((d - (t + 1)).choose (m - (t + 1)) : ℕ) : ℝ) =
          (((d - t).choose (m - t) : ℕ) : ℝ) * (((m - t : ℕ) : ℝ) / ((d - t : ℕ) : ℝ)) := by
      rw [mul_div_assoc', eq_div_iff hdt_pos.ne', mul_comm]
      exact hstepR
    rw [h1, pow_succ]
    calc (((d - t).choose (m - t) : ℕ) : ℝ) * (((m - t : ℕ) : ℝ) / ((d - t : ℕ) : ℝ))
        ≤ (((d - t).choose (m - t) : ℕ) : ℝ) * ((m : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      _ ≤ (((m : ℝ) / (d : ℝ)) ^ t * ((d.choose m : ℕ) : ℝ)) * ((m : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_right hih (by positivity)
      _ = ((m : ℝ) / (d : ℝ)) ^ t * ((m : ℝ) / (d : ℝ)) * ((d.choose m : ℕ) : ℝ) := by ring

private lemma pow_self_le_factorial_mul_exp :
    ∀ t : ℕ, (t : ℝ) ^ t ≤ (t.factorial : ℝ) * Real.exp t
  | 0 => by simp
  | t + 1 => by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [zero_add, Nat.cast_one, one_pow, Nat.factorial_one, one_mul]
      linarith [Real.add_one_le_exp 1]
    · have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
      have hih := pow_self_le_factorial_mul_exp t
      have h1 : (1 + 1 / (t : ℝ)) ^ t ≤ Real.exp 1 := by
        calc (1 + 1 / (t : ℝ)) ^ t
            ≤ (Real.exp (1 / (t : ℝ))) ^ t := by
              refine pow_le_pow_left₀ (by positivity) ?_ t
              linarith [Real.add_one_le_exp (1 / (t : ℝ))]
          _ = Real.exp 1 := by
              rw [← Real.exp_nat_mul, mul_one_div_cancel ht_pos.ne']
      have h2 : ((t : ℝ) + 1) ^ t = (t : ℝ) ^ t * (1 + 1 / (t : ℝ)) ^ t := by
        rw [← mul_pow]
        congr 1
        field_simp
      calc ((t + 1 : ℕ) : ℝ) ^ (t + 1)
          = ((t : ℝ) + 1) * ((t : ℝ) + 1) ^ t := by push_cast; rw [pow_succ']
        _ = ((t : ℝ) + 1) * ((t : ℝ) ^ t * (1 + 1 / (t : ℝ)) ^ t) := by rw [h2]
        _ ≤ ((t : ℝ) + 1) * (((t.factorial : ℝ) * Real.exp t) * Real.exp 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul hih h1 (by positivity) (by positivity)
        _ = ((t + 1).factorial : ℝ) * Real.exp ((t + 1 : ℕ) : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            rw [Real.exp_add]
            ring

private lemma choose_mul_factorial_le_pow :
    ∀ (t d : ℕ), d.choose t * t.factorial ≤ d ^ t
  | 0, _ => by simp
  | _ + 1, 0 => by simp
  | t + 1, d + 1 => by
    have hih := choose_mul_factorial_le_pow t d
    have h1 : (d + 1).choose (t + 1) * (t + 1) = (d + 1) * d.choose t := by
      have := Nat.add_one_mul_choose_eq d t
      linarith
    calc (d + 1).choose (t + 1) * (t + 1).factorial
        = ((d + 1).choose (t + 1) * (t + 1)) * t.factorial := by
          rw [Nat.factorial_succ]; ring
      _ = (d + 1) * (d.choose t * t.factorial) := by rw [h1]; ring
      _ ≤ (d + 1) * d ^ t := Nat.mul_le_mul_left (d + 1) hih
      _ ≤ (d + 1) * (d + 1) ^ t :=
          Nat.mul_le_mul_left (d + 1) (Nat.pow_le_pow_left (Nat.le_succ d) t)
      _ = (d + 1) ^ (t + 1) := by rw [pow_succ']

private lemma choose_le_exp_mul_div_pow (d : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    ((d.choose t : ℕ) : ℝ) ≤ (Real.exp 1 * (d : ℝ) / (t : ℝ)) ^ t := by
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hfac_pos : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  have h1 : ((d.choose t : ℕ) : ℝ) * (t.factorial : ℝ) ≤ (d : ℝ) ^ t := by
    exact_mod_cast choose_mul_factorial_le_pow t d
  have h2 : (t : ℝ) ^ t ≤ (t.factorial : ℝ) * (Real.exp 1) ^ t := by
    have := pow_self_le_factorial_mul_exp t
    rwa [← Real.exp_nat_mul, mul_one]
  rw [div_pow, le_div_iff₀ (pow_pos ht_pos t), mul_pow]
  have hcomb :
      (((d.choose t : ℕ) : ℝ) * (t : ℝ) ^ t) * (t.factorial : ℝ) ≤
        ((Real.exp 1) ^ t * (d : ℝ) ^ t) * (t.factorial : ℝ) := by
    calc (((d.choose t : ℕ) : ℝ) * (t : ℝ) ^ t) * (t.factorial : ℝ)
        ≤ ((d.choose t : ℕ) : ℝ) * ((t.factorial : ℝ) * (Real.exp 1) ^ t) * (t.factorial : ℝ) := by
          gcongr
      _ = (((d.choose t : ℕ) : ℝ) * (t.factorial : ℝ)) * (Real.exp 1) ^ t * (t.factorial : ℝ) := by
          ring
      _ ≤ (d : ℝ) ^ t * (Real.exp 1) ^ t * (t.factorial : ℝ) := by gcongr
      _ = ((Real.exp 1) ^ t * (d : ℝ) ^ t) * (t.factorial : ℝ) := by ring
  exact le_of_mul_le_mul_right hcomb hfac_pos

private lemma sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) : ∀ t : ℕ, Real.sqrt (x ^ t) = (Real.sqrt x) ^ t
  | 0 => by simp
  | t + 1 => by rw [pow_succ, Real.sqrt_mul (pow_nonneg hx t), sqrt_pow_eq x hx t, pow_succ]

private lemma sqrt_choose_mul_pow_le (d : ℕ) (p : ℝ) (hp : 0 ≤ p) (t : ℕ) :
    Real.sqrt ((d.choose t : ℕ) : ℝ) * p ^ t ≤
      (p * Real.sqrt (Real.exp 1 * (d : ℝ) / (t : ℝ))) ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [mul_pow, mul_comm (p ^ t)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp t)
    have hch := choose_le_exp_mul_div_pow d ht
    have hsq := Real.sqrt_le_sqrt hch
    rwa [sqrt_pow_eq _ (by positivity)] at hsq

private lemma card_powersetCard_superset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} {S : Finset ι} (hS : #S ≤ m) :
    #{J ∈ (univ : Finset ι).powersetCard m | S ⊆ J} =
      (Fintype.card ι - #S).choose (m - #S) := by
  have hbij :
      #{J ∈ (univ : Finset ι).powersetCard m | S ⊆ J} =
        #((univ \ S).powersetCard (m - #S)) := by
    refine Finset.card_bij (fun J _ ↦ J \ S) ?_ ?_ ?_
    · intro J hJ
      obtain ⟨hJm, hSJ⟩ := mem_filter.mp hJ
      rw [mem_powersetCard] at hJm ⊢
      exact ⟨sdiff_subset_sdiff (subset_univ J) le_rfl, card_sdiff_of_subset hSJ ▸ hJm.2 ▸ rfl⟩
    · intro J₁ hJ₁ J₂ hJ₂ heq
      have h1 := (mem_filter.mp hJ₁).2
      have h2 := (mem_filter.mp hJ₂).2
      rw [← sdiff_union_of_subset h1, ← sdiff_union_of_subset h2, heq]
    · intro K hK
      rw [mem_powersetCard] at hK
      have hdisj : Disjoint K S := disjoint_of_subset_left hK.1 sdiff_disjoint
      refine ⟨K ∪ S, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, subset_union_right⟩,
        union_sdiff_cancel_right hdisj⟩
      rw [card_union_of_disjoint hdisj, hK.2]
      omega
  rw [hbij, card_powersetCard, card_sdiff_of_subset (subset_univ S), card_univ]

/-- **Expected Fourier `ℓ₁`-Tail Bound Under Uniform `m`-Star Restrictions**: for any bounded
function `h : (ι → Bool) → ℝ` (`|h x| ≤ 1`), `m ≤ d = |ι|`, `p = m / d`, and `k : ℕ`, the average
over `J ∈ powersetCard m univ` of `fourierTailL1 k (fun x ↦ 𝔼 z, h (J.piecewise x z))` is at most
`∑ t ∈ Icc k m, (p * √(e * d / t)) ^ t`. -/
theorem expect_fourierTailL1_piecewise_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : (ι → Bool) → ℝ} (hh : ∀ x, |h x| ≤ 1)
    {m : ℕ} (hm : m ≤ Fintype.card ι) (k : ℕ) :
    let d := Fintype.card ι
    let p : ℝ := (m : ℝ) / (d : ℝ)
    (∑ J ∈ (univ : Finset ι).powersetCard m,
      fourierTailL1 k (fun x ↦ 𝔼 z, h (J.piecewise x z))) /
        (((d.choose m : ℕ) : ℝ)) ≤
      ∑ t ∈ Icc k m, (p * Real.sqrt (Real.exp 1 * (d : ℝ) / (t : ℝ))) ^ t := by
  intro d p
  have hchoose_pos : (0 : ℝ) < d.choose m := by
    exact_mod_cast Nat.choose_pos hm
  have hp_nonneg : 0 ≤ p := by positivity
  -- Step 1: Exchange summation over `J` and `S` via `fourierCoeff_expect_piecewise`.
  have hswap :
      (∑ J ∈ (univ : Finset ι).powersetCard m,
        fourierTailL1 k (fun x ↦ 𝔼 z, h (J.piecewise x z))) =
      ∑ S : Finset ι with k ≤ #S ∧ #S ≤ m,
        |Cslib.BitString.fourierCoeff h S| *
          (#{J ∈ (univ : Finset ι).powersetCard m | S ⊆ J} : ℝ) := by
    simp only [fourierTailL1, Cslib.BitString.fourierCoeff_expect_piecewise]
    rw [sum_comm]
    have hsplit :
        (∑ x : Finset ι with k ≤ #x,
          ∑ y ∈ (univ : Finset ι).powersetCard m,
            |if x ⊆ y then Cslib.BitString.fourierCoeff h x else 0|) =
        ∑ S : Finset ι with k ≤ #S ∧ #S ≤ m,
          ∑ y ∈ (univ : Finset ι).powersetCard m,
            |if S ⊆ y then Cslib.BitString.fourierCoeff h S else 0| := by
      symm
      refine sum_subset (fun S hS ↦ mem_filter.mpr ⟨mem_univ S, (mem_filter.mp hS).2.1⟩) ?_
      intro S hS hnot
      have hgt : m < #S := by
        have hkS := (mem_filter.mp hS).2
        have hnot' : ¬(k ≤ #S ∧ #S ≤ m) := fun hc ↦ hnot (mem_filter.mpr ⟨mem_univ S, hc⟩)
        omega
      refine sum_eq_zero fun J hJ ↦ ?_
      have hnot_sub : ¬(S ⊆ J) := fun hSJ ↦
        not_le.mpr hgt ((card_le_card hSJ).trans (mem_powersetCard.mp hJ).2.le)
      simp [hnot_sub]
    rw [hsplit]
    refine sum_congr rfl fun S _ ↦ ?_
    have hinner :
        (∑ y ∈ (univ : Finset ι).powersetCard m,
          |if S ⊆ y then Cslib.BitString.fourierCoeff h S else 0|) =
        ∑ y ∈ (univ : Finset ι).powersetCard m,
          (if S ⊆ y then (1 : ℝ) else 0) * |Cslib.BitString.fourierCoeff h S| := by
      refine sum_congr rfl fun y _ ↦ ?_
      split_ifs <;> simp
    rw [hinner, ← sum_mul, sum_boole, mul_comm]
  rw [hswap, sum_div]
  -- Step 2: Bound the survival probability by `p ^ #S` and group by `t = #S ∈ Icc k m`.
  have hprob_le :
      (∑ S : Finset ι with k ≤ #S ∧ #S ≤ m,
        |Cslib.BitString.fourierCoeff h S| *
          (#{J ∈ (univ : Finset ι).powersetCard m | S ⊆ J} : ℝ) / ((d.choose m : ℕ) : ℝ)) ≤
      ∑ t ∈ Icc k m, (∑ S : Finset ι with #S = t, |Cslib.BitString.fourierCoeff h S|) * p ^ t := by
    have h1 :
        (∑ S : Finset ι with k ≤ #S ∧ #S ≤ m,
          |Cslib.BitString.fourierCoeff h S| *
            (#{J ∈ (univ : Finset ι).powersetCard m | S ⊆ J} : ℝ) / ((d.choose m : ℕ) : ℝ)) ≤
        ∑ S : Finset ι with k ≤ #S ∧ #S ≤ m,
          |Cslib.BitString.fourierCoeff h S| * p ^ #S := by
      refine sum_le_sum fun S hS ↦ ?_
      have hSm : #S ≤ m := (mem_filter.mp hS).2.2
      rw [card_powersetCard_superset hSm, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [div_le_iff₀ hchoose_pos]
      exact choose_sub_le_pow_mul_choose #S hSm hm
    refine h1.trans ?_
    rw [← sum_fiberwise_of_maps_to (g := card) (t := Icc k m)
      (fun S hS ↦ mem_Icc.mpr (mem_filter.mp hS).2)]
    refine le_of_eq (sum_congr rfl fun t ht ↦ ?_)
    rw [sum_mul]
    refine sum_congr (by ext S; simp only [mem_filter, mem_univ, true_and]; exact
      ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ mem_Icc.mp ht, h⟩⟩) fun S hS ↦ ?_
    rw [(mem_filter.mp hS).2]
  refine hprob_le.trans (sum_le_sum fun t _ ↦ ?_)
  -- Step 3: Apply Cauchy–Schwarz and Parseval `∑_{|S|=t} f̂(S)² ≤ 1`.
  have hcs :
      (∑ S : Finset ι with #S = t, |Cslib.BitString.fourierCoeff h S|) ≤
        Real.sqrt ((d.choose t : ℕ) : ℝ) := by
    have hsq_le :
        (∑ S : Finset ι with #S = t, |Cslib.BitString.fourierCoeff h S|) ^ 2 ≤
          ((d.choose t : ℕ) : ℝ) := by
      have hcheb := sq_sum_le_card_mul_sum_sq (s := univ.filter fun S : Finset ι ↦ #S = t)
        (f := fun S ↦ |Cslib.BitString.fourierCoeff h S|)
      have hcard_t : #(univ.filter fun S : Finset ι ↦ #S = t) = d.choose t := by
        have heq : (univ.filter fun S : Finset ι ↦ #S = t) = (univ : Finset ι).powersetCard t := by
          ext S; simp [mem_powersetCard]
        rw [heq, card_powersetCard, card_univ]
      have hparseval :
          ∑ S ∈ univ.filter (fun S : Finset ι ↦ #S = t),
            |Cslib.BitString.fourierCoeff h S| ^ 2 ≤ 1 := by
        simpa [sq_abs] using Cslib.BitString.sum_fourierCoeff_sq_le_one_of_abs_le_one hh
          (univ.filter fun S : Finset ι ↦ #S = t)
      rw [hcard_t] at hcheb
      exact hcheb.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (d.choose t)])
    exact (Real.le_sqrt (sum_nonneg fun _ _ ↦ abs_nonneg _) (Nat.cast_nonneg _)).mpr hsq_le
  exact (mul_le_mul_of_nonneg_right hcs (pow_nonneg hp_nonneg t)).trans
    (sqrt_choose_mul_pow_le d p hp_nonneg t)

/-- **Exponential Fourier `ℓ₁`-Tail Decay Above `4 e p² d`**: when `4 * e * p ^ 2 * d ≤ k`, the
expected high-degree Fourier `ℓ₁`-mass above `k` is at most `2 ^ (-k + 1)`. -/
theorem expect_fourierTailL1_piecewise_le_two_zpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : (ι → Bool) → ℝ} (hh : ∀ x, |h x| ≤ 1)
    {m : ℕ} (hm : m ≤ Fintype.card ι) {k : ℕ}
    (hk : 4 * Real.exp 1 * ((m : ℝ) / (Fintype.card ι : ℝ)) ^ 2 * (Fintype.card ι : ℝ) ≤ k) :
    (∑ J ∈ (univ : Finset ι).powersetCard m,
      fourierTailL1 k (fun x ↦ 𝔼 z, h (J.piecewise x z))) /
        (((Fintype.card ι).choose m : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (-(k : ℤ) + 1) := by
  refine (expect_fourierTailL1_piecewise_le hh hm k).trans ?_
  set d := Fintype.card ι
  set p : ℝ := (m : ℝ) / (d : ℝ)
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- When `k = 0`, `4 e p² d ≤ 0` forces `m = 0`, so `Icc 0 0 = {0}` has sum `1 ≤ 2 = 2 ^ 1`.
    have hm0 : m = 0 := by
      rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
      · omega
      · have hdR : (0 : ℝ) < d := by exact_mod_cast hd_pos
        have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
        have hp0 : p ^ 2 ≤ 0 := by
          by_contra hp_gt
          push Not at hp_gt
          have : 0 < 4 * Real.exp 1 * p ^ 2 * (d : ℝ) := by positivity
          simp only [Nat.cast_zero] at hk
          linarith
        have hp_eq0 : p = 0 := sq_eq_zero_iff.mp (le_antisymm hp0 (sq_nonneg p))
        have hmR : (m : ℝ) = 0 := by
          dsimp [p] at hp_eq0
          exact (div_eq_zero_iff.mp hp_eq0).resolve_right hdR.ne'
        exact_mod_cast hmR
    subst hm0
    norm_num
  · -- When `1 ≤ k`, every `t ∈ Icc k m` satisfies `p * √(e d / t) ≤ 1 / 2`.
    have hterm_half : ∀ t ∈ Icc k m,
        (p * Real.sqrt (Real.exp 1 * (d : ℝ) / (t : ℝ))) ^ t ≤ (1 / 2 : ℝ) ^ t := by
      intro t ht
      have hkt : k ≤ t := (mem_Icc.mp ht).1
      have ht_pos : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le hk_pos hkt)
      have hk_posR : (0 : ℝ) < k := by exact_mod_cast hk_pos
      have hp_nonneg : 0 ≤ p := by positivity
      have hnonneg : 0 ≤ p * Real.sqrt (Real.exp 1 * (d : ℝ) / (t : ℝ)) := by positivity
      refine pow_le_pow_left₀ hnonneg ?_ t
      have hsq : (p * Real.sqrt (Real.exp 1 * (d : ℝ) / (t : ℝ))) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hdt : Real.exp 1 * (d : ℝ) / (t : ℝ) ≤ Real.exp 1 * (d : ℝ) / (k : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hk_posR (by exact_mod_cast hkt)
        have hmul :
            p ^ 2 * (Real.exp 1 * (d : ℝ) / (t : ℝ)) ≤
              p ^ 2 * (Real.exp 1 * (d : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hdt (sq_nonneg p)
        have hquarter : p ^ 2 * (Real.exp 1 * (d : ℝ) / (k : ℝ)) ≤ 1 / 4 := by
          rw [mul_div_assoc', div_le_iff₀ hk_posR]
          linarith
        linarith [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
      nlinarith
    refine (sum_le_sum hterm_half).trans ?_
    by_cases hkm : k ≤ m
    · -- Finite geometric series `∑_{t=k}^m (1/2)^t ≤ 2 * (1/2)^k = 2^(-k+1)`.
      have hgeom :
          ∑ t ∈ Icc k m, (1 / 2 : ℝ) ^ t ≤ 2 * (1 / 2 : ℝ) ^ k := by
        have hIcc : Icc k m = (range (m - k + 1)).image (fun j ↦ k + j) := by
          ext t
          simp only [mem_Icc, mem_image, mem_range]
          exact ⟨fun ⟨h1, h2⟩ ↦ ⟨t - k, by omega, by omega⟩,
            fun ⟨j, hj, heq⟩ ↦ ⟨by omega, by omega⟩⟩
        have hinj : ∀ a ∈ range (m - k + 1), ∀ b ∈ range (m - k + 1), k + a = k + b → a = b :=
          fun _ _ _ _ h ↦ by omega
        rw [hIcc, sum_image hinj]
        simp only [pow_add, ← mul_sum]
        rw [mul_comm 2 ((1 / 2 : ℝ) ^ k)]
        have hk_pow : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hk_pow
        have hgs := geom_sum_eq (x := (1 / 2 : ℝ)) (by norm_num) (m - k + 1)
        have hgs' : ∑ i ∈ range (m - k + 1), (1 / 2 : ℝ) ^ i =
            2 - 2 * (1 / 2) ^ (m - k + 1) := by
          rw [hgs]; ring
        have hpow_nonneg : (0 : ℝ) ≤ (1 / 2) ^ (m - k + 1) := by positivity
        linarith
      refine hgeom.trans_eq ?_
      rw [zpow_add₀ (by norm_num), zpow_one, zpow_neg, zpow_natCast, one_div, inv_pow]
      ring
    · rw [Icc_eq_empty hkm, sum_empty]
      positivity

private example : boolSparsity (fun x : Cslib.BitString 2 ↦ x 0 || x 1) = 3 := by
  have hf :
      (fun x : Cslib.BitString 2 ↦ Cslib.BitString.bitVal ℝ (x 0 || x 1)) =
        (1 : ℝ) • Cslib.BitString.monomial ℝ {0} +
          (1 : ℝ) • Cslib.BitString.monomial ℝ {1} +
          (-1 : ℝ) • Cslib.BitString.monomial ℝ {0, 1} := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Cslib.BitString.monomial_apply]
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1]
  have hmc (S : Finset (Fin 2)) :
      monomialCoeff (fun x : Cslib.BitString 2 ↦ Cslib.BitString.bitVal ℝ (x 0 || x 1)) S =
        (if ({0} : Finset (Fin 2)) = S then 1 else 0) +
          (if ({1} : Finset (Fin 2)) = S then 1 else 0) -
          (if ({0, 1} : Finset (Fin 2)) = S then 1 else 0) := by
    rw [hf, monomialCoeff]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Cslib.BitString.subsetMobius_add, Cslib.BitString.subsetMobius_add,
      Cslib.BitString.subsetMobius_const_mul,
      Cslib.BitString.subsetMobius_const_mul,
      Cslib.BitString.subsetMobius_const_mul,
      Cslib.BitString.subsetMobius_monomial,
      Cslib.BitString.subsetMobius_monomial,
      Cslib.BitString.subsetMobius_monomial]
    ring
  have hsupp :
      monomialSupport (fun x : Cslib.BitString 2 ↦ Cslib.BitString.bitVal ℝ (x 0 || x 1)) =
        {{0}, {1}, {0, 1}} := by
    ext S
    rw [mem_monomialSupport_iff, hmc]
    have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · right; right; right; ext i; fin_cases i <;> simp [h0, h1]
      · right; left; ext i; fin_cases i <;> simp [h0, h1]
      · right; right; left; ext i; fin_cases i <;> simp [h0, h1]
      · left; ext i; fin_cases i <;> simp [h0, h1]
    rcases hcases with rfl | rfl | rfl | rfl
    · simp only [show ({0} : Finset (Fin 2)) ≠ ∅ by decide,
        show ({1} : Finset (Fin 2)) ≠ ∅ by decide,
        show ({0, 1} : Finset (Fin 2)) ≠ ∅ by decide, ↓reduceIte]
      constructor
      · norm_num
      · intro h; exfalso; revert h; decide
    · simp only [↓reduceIte,
        show ({1} : Finset (Fin 2)) ≠ {0} by decide,
        show ({0, 1} : Finset (Fin 2)) ≠ {0} by decide]
      constructor
      · intro _; decide
      · intro _; norm_num
    · simp only [↓reduceIte,
        show ({0} : Finset (Fin 2)) ≠ {1} by decide,
        show ({0, 1} : Finset (Fin 2)) ≠ {1} by decide]
      constructor
      · intro _; decide
      · intro _; norm_num
    · simp only [↓reduceIte,
        show ({0} : Finset (Fin 2)) ≠ {0, 1} by decide,
        show ({1} : Finset (Fin 2)) ≠ {0, 1} by decide]
      constructor
      · intro _; decide
      · intro _; norm_num
  rw [boolSparsity, sparsity, hsupp]
  decide

end CslibFrontier.BooleanAnalysis
