module

public import Cslib.Probability.PMF
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Matrix.Mul
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-Field Fourier Transform, Empirical Distributions, and the Vazirani XOR-Lemma

This module develops finite-field additive Fourier analysis on vector spaces `ι → F` over a
finite field `F`, empirical row/vector distributions via `PMF`, the Fourier characterization of
normalized Hamming weight and vector bias, and the generalized and binary Vazirani XOR-lemmas.
All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Foundations.Data.Code.canonicalAddChar`: the canonical additive character
  `x ↦ exp(2πi · tr(x) / p)` on a finite field `F` of characteristic `p`.
* `CslibFrontier.Foundations.Data.Code.fourierTransform`: the additive Fourier transform
  `f̂(y) = ∑ x, f x * conj (χ(⟨x, y⟩))` for `f : (ι → F) → ℂ`.
* `CslibFrontier.Foundations.Data.Code.empiricalPMF`: the empirical distribution of a tuple
  `a : κ → α` as `(PMF.uniformOfFintype κ).map a`.
* `CslibFrontier.Foundations.Data.Code.normalizedHammingWeight`: normalized Hamming weight
  `hammingNorm u / |κ|`.
* `CslibFrontier.Foundations.Data.Code.IsVectorBiased`: `η`-bias of a vector `u : κ → F`.

## Main results

* `CslibFrontier.Foundations.Data.Code.fourier_inversion`: Fourier inversion on `ι → F`.
* `CslibFrontier.Foundations.Data.Code.parseval_inner` and
  `CslibFrontier.Foundations.Data.Code.parseval_norm_sq`: Parseval's identity.
* `CslibFrontier.Foundations.Data.Code.fourierTransform_empiricalPMF_mulVec`: Fourier transform of
  the empirical row distribution of a matrix evaluated at `a • y`.
* `CslibFrontier.Foundations.Data.Code.normalizedHammingWeight_eq_fourier`: expression of normalized
  Hamming weight via Fourier coefficients of the empirical distribution.
* `CslibFrontier.Foundations.Data.Code.normalizedHammingWeight_bounds_of_isVectorBiased`:
  two-sided Hamming weight bounds from vector bias.
* `CslibFrontier.Foundations.Data.Code.expect_le_sum_norm_fourier_mul_uniform`: generalized
  `ℓ¹`-Fourier Vazirani XOR-lemma over `ι → F`.
* `CslibFrontier.Foundations.Data.Code.tvDist_uniform_le_of_dotProduct_bias`: binary Vazirani
  XOR-lemma in total-variation distance.

## Tags

finite field, Fourier transform, Parseval, Hamming weight, small bias, Vazirani XOR lemma
-/

public section

namespace CslibFrontier.Foundations.Data.Code

open scoped ComplexConjugate Matrix
open Cslib.Probability

private lemma ringChar_prime_of_fintype (F : Type*) [Field F] [Finite F] :
    (ringChar F).Prime := by
  have hchar : ringChar F ≠ 0 := by
    intro h0
    have hcz : CharP F 0 := h0 ▸ ringChar.charP F
    have : CharZero F := CharP.charP_to_charZero F
    exact not_finite F
  exact (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hchar

private lemma neZero_ringChar_of_fintype (F : Type*) [Field F] [Finite F] :
    NeZero (ringChar F) :=
  ⟨(ringChar_prime_of_fintype F).ne_zero⟩

/-- The canonical additive character on a finite field `F` of characteristic `p`:
`x ↦ exp (2 * π * I * (tr_{F/𝔽_p}(x)).val / p)`. -/
noncomputable def canonicalAddChar (F : Type*) [Field F] [Fintype F] : AddChar F ℂ :=
  let : NeZero (ringChar F) := neZero_ringChar_of_fintype F
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

theorem canonicalAddChar_zero (F : Type*) [Field F] [Fintype F] :
    canonicalAddChar F 0 = 1 :=
  (canonicalAddChar F).map_zero_eq_one

theorem canonicalAddChar_add (F : Type*) [Field F] [Fintype F] (x y : F) :
    canonicalAddChar F (x + y) = canonicalAddChar F x * canonicalAddChar F y :=
  (canonicalAddChar F).map_add_eq_mul x y

theorem canonicalAddChar_neg (F : Type*) [Field F] [Fintype F] (x : F) :
    canonicalAddChar F (-x) = (canonicalAddChar F x)⁻¹ :=
  (canonicalAddChar F).map_neg_eq_inv x

theorem canonicalAddChar_sub (F : Type*) [Field F] [Fintype F] (x y : F) :
    canonicalAddChar F (x - y) = canonicalAddChar F x * (canonicalAddChar F y)⁻¹ := by
  rw [sub_eq_add_neg, canonicalAddChar_add, canonicalAddChar_neg]

/-- Compatibility of `canonicalAddChar` with any `Algebra (ZMod (ringChar F)) F` instance. -/
theorem canonicalAddChar_eq_stdAddChar_trace (F : Type*) [Field F] [Fintype F]
    [hNZ : NeZero (ringChar F)] [hAlg : Algebra (ZMod (ringChar F)) F] (x : F) :
    canonicalAddChar F x = ZMod.stdAddChar (Algebra.trace (ZMod (ringChar F)) F x) := by
  have hsub : ZMod.algebra F (ringChar F) = hAlg := Subsingleton.elim _ _
  unfold canonicalAddChar
  rw [hsub]
  rfl

/-- Explicit exponential formula for `canonicalAddChar` in terms of `Algebra.trace`. -/
theorem canonicalAddChar_eq_exp (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod (ringChar F)) F] (x : F) :
    canonicalAddChar F x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((Algebra.trace (ZMod (ringChar F)) F x).val : ℂ) / (ringChar F : ℂ)) := by
  have : NeZero (ringChar F) := neZero_ringChar_of_fintype F
  rw [canonicalAddChar_eq_stdAddChar_trace, ZMod.stdAddChar_apply, ZMod.toCircle_apply]

theorem norm_canonicalAddChar (F : Type*) [Field F] [Fintype F] (x : F) :
    ‖canonicalAddChar F x‖ = 1 := by
  have : NeZero (ringChar F) := neZero_ringChar_of_fintype F
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  rw [canonicalAddChar_eq_stdAddChar_trace, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem star_canonicalAddChar (F : Type*) [Field F] [Fintype F] (x : F) :
    conj (canonicalAddChar F x) = canonicalAddChar F (-x) := by
  have : NeZero (ringChar F) := neZero_ringChar_of_fintype F
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  rw [canonicalAddChar_neg, canonicalAddChar_eq_stdAddChar_trace, ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj _).symm

theorem canonicalAddChar_mul_conj_self (F : Type*) [Field F] [Fintype F] (x : F) :
    canonicalAddChar F x * conj (canonicalAddChar F x) = 1 := by
  rw [star_canonicalAddChar, ← canonicalAddChar_add, add_neg_cancel, canonicalAddChar_zero]

theorem exists_canonicalAddChar_ne_one (F : Type*) [Field F] [Fintype F]
    {a : F} (ha : a ≠ 0) :
    ∃ b : F, canonicalAddChar F (a * b) ≠ 1 := by
  have : NeZero (ringChar F) := neZero_ringChar_of_fintype F
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F ha
  refine ⟨b, ?_⟩
  rw [canonicalAddChar_eq_stdAddChar_trace]
  intro h
  have h0 : ZMod.stdAddChar (Algebra.trace (ZMod (ringChar F)) F (a * b)) =
      ZMod.stdAddChar (0 : ZMod (ringChar F)) := by
    rw [h, AddChar.map_zero_eq_one]
  exact hb (ZMod.injective_stdAddChar h0)

/-- Character orthogonality on a finite field `F`. -/
theorem sum_canonicalAddChar_mul (F : Type*) [Field F] [Fintype F] [DecidableEq F] (a : F) :
    ∑ x : F, canonicalAddChar F (a * x) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha]
  · obtain ⟨b, hb⟩ := exists_canonicalAddChar_ne_one F ha
    have hshift :
        canonicalAddChar F (a * b) * ∑ x : F, canonicalAddChar F (a * x) =
          ∑ x : F, canonicalAddChar F (a * x) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addLeft b) _ _ fun x ↦ ?_
      simp [mul_add, canonicalAddChar_add]
    have hzero : (canonicalAddChar F (a * b) - 1) * ∑ x : F, canonicalAddChar F (a * x) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hb)

theorem sum_canonicalAddChar_mul_conj (F : Type*) [Field F] [Fintype F] [DecidableEq F] (a : F) :
    ∑ x : F, conj (canonicalAddChar F (a * x)) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  have h := sum_canonicalAddChar_mul F (-a)
  have hneg : (-a = 0) ↔ (a = 0) := neg_eq_zero
  simp only [hneg] at h
  convert h using 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [star_canonicalAddChar, neg_mul]

private lemma canonicalAddChar_sum {F ι : Type*} [Field F] [Fintype F]
    (s : Finset ι) (g : ι → F) :
    canonicalAddChar F (∑ i ∈ s, g i) = ∏ i ∈ s, canonicalAddChar F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, canonicalAddChar_add, ih]

/-- Character orthogonality on a finite vector space `ι → F`. -/
theorem sum_canonicalAddChar_dotProduct {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (y : ι → F) :
    ∑ x : ι → F, canonicalAddChar F (dotProduct x y) =
      if y = 0 then (Fintype.card F : ℂ) ^ Fintype.card ι else 0 := by
  have hprod :
      ∑ x : ι → F, canonicalAddChar F (dotProduct x y) =
        ∏ i : ι, ∑ a : F, canonicalAddChar F (y i * a) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [dotProduct, canonicalAddChar_sum]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [mul_comm]
  rw [hprod]
  split_ifs with hy
  · simp [hy]
  · obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (funext h)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sum_canonicalAddChar_mul, ite_eq_right hi]

theorem sum_canonicalAddChar_conj_dotProduct {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (y : ι → F) :
    ∑ x : ι → F, conj (canonicalAddChar F (dotProduct x y)) =
      if y = 0 then (Fintype.card F : ℂ) ^ Fintype.card ι else 0 := by
  have h := sum_canonicalAddChar_dotProduct (F := F) (-y)
  have hneg : (-y = 0) ↔ (y = 0) := neg_eq_zero
  simp only [hneg] at h
  convert h using 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [star_canonicalAddChar, dotProduct_neg]

/-- Additive Fourier transform on `ι → F` with counting norm on `f`:
`f̂(y) = ∑ x, f x * conj (χ(⟨x, y⟩))`. -/
noncomputable def fourierTransform {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → ℂ) (y : ι → F) : ℂ :=
  ∑ x : ι → F, f x * conj (canonicalAddChar F (dotProduct x y))

/-- Scalar additive Fourier transform on `F`: `f̂(a) = ∑ x, f x * conj (χ(x * a))`. -/
noncomputable def fourierTransformScalar {F : Type*} [Field F] [Fintype F]
    (f : F → ℂ) (a : F) : ℂ :=
  ∑ x : F, f x * conj (canonicalAddChar F (x * a))

theorem fourierTransform_apply {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → ℂ) (y : ι → F) :
    fourierTransform f y = ∑ x : ι → F, f x * conj (canonicalAddChar F (dotProduct x y)) := by
  rfl

theorem fourierTransformScalar_apply {F : Type*} [Field F] [Fintype F] (f : F → ℂ) (a : F) :
    fourierTransformScalar f a = ∑ x : F, f x * conj (canonicalAddChar F (x * a)) := by
  rfl

@[simp]
theorem fourierTransform_zero {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → ℂ) :
    fourierTransform f 0 = ∑ x : ι → F, f x := by
  simp [fourierTransform, dotProduct_zero]

@[simp]
theorem fourierTransformScalar_zero {F : Type*} [Field F] [Fintype F] (f : F → ℂ) :
    fourierTransformScalar f 0 = ∑ x : F, f x := by
  simp [fourierTransformScalar]

theorem norm_fourierTransform_le {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → ℂ) (y : ι → F) :
    ‖fourierTransform f y‖ ≤ ∑ x : ι → F, ‖f x‖ := by
  unfold fourierTransform
  calc
    ‖∑ x : ι → F, f x * conj (canonicalAddChar F (dotProduct x y))‖
        ≤ ∑ x : ι → F, ‖f x * conj (canonicalAddChar F (dotProduct x y))‖ :=
      norm_sum_le _ _
    _ = ∑ x : ι → F, ‖f x‖ := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [norm_mul, RCLike.norm_conj, norm_canonicalAddChar, mul_one]

/-- Fourier inversion formula on `ι → F`:
`f(x) = q^{-b} ∑ y, f̂(y) * χ(⟨x, y⟩)`. -/
theorem fourier_inversion {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → ℂ) (x : ι → F) :
    f x = ((Fintype.card F : ℂ) ^ Fintype.card ι)⁻¹ *
      ∑ y : ι → F, fourierTransform f y * canonicalAddChar F (dotProduct x y) := by
  classical
  have hq : ((Fintype.card F : ℂ) ^ Fintype.card ι) ≠ 0 := by
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hsum :
      ∑ y : ι → F, fourierTransform f y * canonicalAddChar F (dotProduct x y) =
        ((Fintype.card F : ℂ) ^ Fintype.card ι) * f x := by
    simp only [fourierTransform, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ z : ι → F,
        ∑ y : ι → F, f z * conj (canonicalAddChar F (dotProduct z y)) *
            canonicalAddChar F (dotProduct x y) =
          f z * if x - z = 0 then (Fintype.card F : ℂ) ^ Fintype.card ι else 0 := by
      intro z
      calc
        ∑ y : ι → F, f z * conj (canonicalAddChar F (dotProduct z y)) *
            canonicalAddChar F (dotProduct x y)
            = f z * ∑ y : ι → F, canonicalAddChar F (dotProduct (x - z) y) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ ↦ ?_
              rw [sub_dotProduct, canonicalAddChar_sub, star_canonicalAddChar,
                canonicalAddChar_neg, mul_assoc, mul_comm (canonicalAddChar F (dotProduct z y))⁻¹]
        _ = f z * ∑ y : ι → F, canonicalAddChar F (dotProduct y (x - z)) := by
              congr 1
              refine Finset.sum_congr rfl fun y _ ↦ by rw [dotProduct_comm]
        _ = f z * if x - z = 0 then (Fintype.card F : ℂ) ^ Fintype.card ι else 0 := by
              rw [sum_canonicalAddChar_dotProduct]
    simp_rw [hinner]
    have hfilter :
        ∑ z : ι → F, (f z * if x - z = 0 then (Fintype.card F : ℂ) ^ Fintype.card ι else 0) =
          f x * (Fintype.card F : ℂ) ^ Fintype.card ι := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro z _ hzx
        have hne : x - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzx)
        simp [hne]
      · intro hx; exact (hx (Finset.mem_univ x)).elim
    rw [hfilter, mul_comm]
  rw [hsum, inv_mul_cancel_left₀ hq]

/-- Scalar Fourier inversion on `F`: `f(x) = q⁻¹ ∑ a, f̂(a) * χ(x * a)`. -/
theorem fourier_inversion_scalar {F : Type*} [Field F] [Fintype F] (f : F → ℂ) (x : F) :
    f x = (Fintype.card F : ℂ)⁻¹ *
      ∑ a : F, fourierTransformScalar f a * canonicalAddChar F (x * a) := by
  let e : (Unit → F) ≃ F := Equiv.funUnique Unit F
  have h := fourier_inversion (F := F) (ι := Unit) (f ∘ e) (e.symm x)
  simp only [Function.comp_apply, Equiv.apply_symm_apply, Fintype.card_unit, pow_one] at h
  rw [h]
  congr 1
  refine Fintype.sum_equiv e (fun y : Unit → F ↦
      fourierTransform (f ∘ e) y * canonicalAddChar F (dotProduct (e.symm x) y))
    (fun a : F ↦ fourierTransformScalar f a * canonicalAddChar F (x * a)) fun y ↦ ?_
  have hft : fourierTransform (f ∘ e) y = fourierTransformScalar f (e y) := by
    unfold fourierTransform fourierTransformScalar
    refine Fintype.sum_equiv e (fun z : Unit → F ↦
        (f ∘ e) z * conj (canonicalAddChar F (dotProduct z y)))
      (fun a : F ↦ f a * conj (canonicalAddChar F (a * e y))) fun z ↦ ?_
    simp [dotProduct, e]
  rw [hft]
  simp [dotProduct, e]

/-- Parseval's identity (inner-product form) on `ι → F`. -/
theorem parseval_inner {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f g : (ι → F) → ℂ) :
    ∑ x : ι → F, f x * conj (g x) =
      ((Fintype.card F : ℂ) ^ Fintype.card ι)⁻¹ *
        ∑ y : ι → F, fourierTransform f y * conj (fourierTransform g y) := by
  have hrhs :
      ∑ y : ι → F, fourierTransform f y * conj (fourierTransform g y) =
        ∑ x : ι → F, f x *
          ∑ y : ι → F, conj (fourierTransform g y) *
            conj (canonicalAddChar F (dotProduct x y)) := by
    simp only [fourierTransform, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ by ring
  rw [hrhs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hinv := congrArg conj (fourier_inversion g x)
  rw [map_mul, map_inv₀, map_pow, Complex.conj_natCast, map_sum] at hinv
  simp_rw [map_mul] at hinv
  calc
    f x * conj (g x)
        = f x * (((Fintype.card F : ℂ) ^ Fintype.card ι)⁻¹ *
            ∑ y : ι → F, conj (fourierTransform g y) *
              conj (canonicalAddChar F (dotProduct x y))) := by rw [hinv]
    _ = ((Fintype.card F : ℂ) ^ Fintype.card ι)⁻¹ *
          (f x * ∑ y : ι → F, conj (fourierTransform g y) *
            conj (canonicalAddChar F (dotProduct x y))) := by ring

/-- Parseval's identity (`ℓ²`-norm form) on `ι → F`. -/
theorem parseval_norm_sq {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    (f : (ι → F) → ℂ) :
    ∑ x : ι → F, ‖f x‖ ^ 2 =
      ((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ *
        ∑ y : ι → F, ‖fourierTransform f y‖ ^ 2 := by
  have h := parseval_inner f f
  have hre := congrArg Complex.re h
  have hmul_conj : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z ↦ by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hmul_conj] at hre
  have hcoeL :
      (∑ x : ι → F, ((‖f x‖ ^ 2 : ℝ) : ℂ)).re = ∑ x : ι → F, ‖f x‖ ^ 2 := by
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  have hcoeR :
      (((Fintype.card F : ℂ) ^ Fintype.card ι)⁻¹ *
          ∑ y : ι → F, ((‖fourierTransform f y‖ ^ 2 : ℝ) : ℂ)).re =
        ((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ * ∑ y : ι → F, ‖fourierTransform f y‖ ^ 2 := by
    have h1 : ((Fintype.card F : ℂ) ^ Fintype.card ι)⁻¹ =
        ((((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [h1, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hcoeL, hcoeR] at hre
  exact hre

/-- Empirical distribution of a finite family `a : κ → α` as a `PMF α`. -/
noncomputable def empiricalPMF {α κ : Type*} [Fintype κ] [Nonempty κ] (a : κ → α) : PMF α :=
  (PMF.uniformOfFintype κ).map a

theorem empiricalPMF_apply_toReal {α κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq α]
    (a : κ → α) (x : α) :
    (empiricalPMF a x).toReal =
      ((Finset.univ.filter fun i : κ ↦ a i = x).card : ℝ) / (Fintype.card κ : ℝ) := by
  unfold empiricalPMF
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun i _ ↦ by
    split_ifs <;> simp)]
  simp only [PMF.uniformOfFintype_apply]
  have hsum :
      ∑ i : κ, (if x = a i then (Fintype.card κ : ENNReal)⁻¹ else 0).toReal =
        ∑ i : κ, if a i = x then (Fintype.card κ : ℝ)⁻¹ else 0 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : a i = x
    · simp [hi]
    · have hi' : x ≠ a i := Ne.symm hi
      simp [hi, hi']
  rw [hsum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]

theorem sum_empiricalPMF_mul {α κ : Type*} [Fintype α] [Fintype κ] [Nonempty κ]
    (a : κ → α) (g : α → ℂ) :
    ∑ x : α, ((empiricalPMF a x).toReal : ℂ) * g x =
      ((Fintype.card κ : ℂ)⁻¹) * ∑ i : κ, g (a i) := by
  classical
  simp_rw [empiricalPMF_apply_toReal, Complex.ofReal_div, Complex.ofReal_natCast]
  have h1 :
      ∑ x : α, (((Finset.univ.filter fun i : κ ↦ a i = x).card : ℂ) /
          (Fintype.card κ : ℂ)) * g x =
        (Fintype.card κ : ℂ)⁻¹ *
          ∑ x : α, ∑ i ∈ Finset.univ.filter (fun i : κ ↦ a i = x), g (a i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hcongr : ∑ i ∈ Finset.univ.filter (fun i : κ ↦ a i = x), g (a i) =
        ((Finset.univ.filter fun i : κ ↦ a i = x).card : ℂ) * g x := by
      calc
        ∑ i ∈ Finset.univ.filter (fun i : κ ↦ a i = x), g (a i)
            = ∑ _i ∈ Finset.univ.filter (fun i : κ ↦ a i = x), g x :=
          Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2]
        _ = ((Finset.univ.filter fun i : κ ↦ a i = x).card : ℂ) * g x := by
          rw [Finset.sum_const, nsmul_eq_mul]
    rw [hcongr]
    ring
  rw [h1]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to (fun i _ ↦ Finset.mem_univ (a i)) _

theorem sum_empiricalPMF_mul_real {α κ : Type*} [Fintype α] [Fintype κ] [Nonempty κ]
    (a : κ → α) (g : α → ℝ) :
    ∑ x : α, (empiricalPMF a x).toReal * g x =
      (Fintype.card κ : ℝ)⁻¹ * ∑ i : κ, g (a i) := by
  have h := congrArg Complex.re (sum_empiricalPMF_mul a (fun x ↦ (g x : ℂ)))
  have hL :
      (∑ x : α, ((empiricalPMF a x).toReal : ℂ) * (g x : ℂ)).re =
        ∑ x : α, (empiricalPMF a x).toReal * g x := by
    simp_rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  have hR :
      ((Fintype.card κ : ℂ)⁻¹ * ∑ i : κ, (g (a i) : ℂ)).re =
        (Fintype.card κ : ℝ)⁻¹ * ∑ i : κ, g (a i) := by
    have h1 : (Fintype.card κ : ℂ)⁻¹ = (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; rfl
    rw [h1, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hL, hR] at h
  exact h

theorem support_empiricalPMF {α κ : Type*} [Fintype κ] [Nonempty κ] (a : κ → α) :
    (empiricalPMF a).support = Set.range a := by
  classical
  ext x
  simp only [PMF.mem_support_iff, empiricalPMF, PMF.map_apply, Set.mem_range]
  constructor
  · intro h
    by_contra hne
    apply h
    have hneq : ∀ i : κ, x ≠ a i := fun i hi ↦ hne ⟨i, hi.symm⟩
    simp [hneq]
  · rintro ⟨i, rfl⟩ h
    rw [tsum_fintype] at h
    have h0 : (PMF.uniformOfFintype κ) i = 0 := by
      have hle : (PMF.uniformOfFintype κ) i ≤
          ∑ j : κ, if a i = a j then (PMF.uniformOfFintype κ) j else 0 := by
        have := Finset.single_le_sum
          (f := fun j : κ ↦ if a i = a j then (PMF.uniformOfFintype κ) j else 0)
          (fun _ _ ↦ bot_le) (Finset.mem_univ i)
        simpa using this
      rw [h] at hle
      exact le_antisymm hle bot_le
    simp [PMF.uniformOfFintype_apply] at h0

theorem empiricalPMF_map {α β κ : Type*} [Fintype κ] [Nonempty κ] (a : κ → α) (f : α → β) :
    (empiricalPMF a).map f = empiricalPMF (f ∘ a) := by
  unfold empiricalPMF
  rw [PMF.map_comp]

theorem fourierTransform_empiricalPMF_eq {F ι κ : Type*} [Field F] [Fintype F] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [Nonempty κ] (A : Matrix κ ι F) (y : ι → F) :
    fourierTransform (fun x ↦ ((empiricalPMF A x).toReal : ℂ)) y =
      (Fintype.card κ : ℂ)⁻¹ * ∑ i : κ, conj (canonicalAddChar F (dotProduct (A i) y)) := by
  unfold fourierTransform
  exact sum_empiricalPMF_mul A (fun x ↦ conj (canonicalAddChar F (dotProduct x y)))

theorem fourierTransformScalar_empiricalPMF_eq {F κ : Type*} [Field F] [Fintype F]
    [Fintype κ] [Nonempty κ] (u : κ → F) (a : F) :
    fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a =
      (Fintype.card κ : ℂ)⁻¹ * ∑ i : κ, conj (canonicalAddChar F (u i * a)) := by
  unfold fourierTransformScalar
  exact sum_empiricalPMF_mul u (fun x ↦ conj (canonicalAddChar F (x * a)))

/-- Fourier transform of the empirical row distribution of `A` evaluated at `a • y` equals the
scalar Fourier transform of `A *ᵥ y` evaluated at `a`. -/
theorem fourierTransform_empiricalPMF_mulVec {F ι κ : Type*} [Field F] [Fintype F] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [Nonempty κ] (A : Matrix κ ι F) (a : F) (y : ι → F) :
    fourierTransform (fun x ↦ ((empiricalPMF A x).toReal : ℂ)) (a • y) =
      fourierTransformScalar (fun z ↦ ((empiricalPMF (A *ᵥ y) z).toReal : ℂ)) a := by
  rw [fourierTransform_empiricalPMF_eq, fourierTransformScalar_empiricalPMF_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  rw [dotProduct_smul, smul_eq_mul, mul_comm, Matrix.mulVec]

/-- Normalized Hamming weight `wt(u) = |{i | u i ≠ 0}| / |κ|`. -/
noncomputable def normalizedHammingWeight {α κ : Type*} [Fintype κ] [Zero α] [DecidableEq α]
    (u : κ → α) : ℝ :=
  (hammingNorm u : ℝ) / (Fintype.card κ : ℝ)

theorem normalizedHammingWeight_eq_div {α κ : Type*} [Fintype κ] [Zero α] [DecidableEq α]
    (u : κ → α) :
    normalizedHammingWeight u = (hammingNorm u : ℝ) / (Fintype.card κ : ℝ) := by
  rfl

theorem normalizedHammingWeight_nonneg {α κ : Type*} [Fintype κ] [Zero α] [DecidableEq α]
    (u : κ → α) :
    0 ≤ normalizedHammingWeight u := by
  unfold normalizedHammingWeight
  positivity

theorem normalizedHammingWeight_le_one {α κ : Type*} [Fintype κ] [Zero α] [DecidableEq α]
    (u : κ → α) :
    normalizedHammingWeight u ≤ 1 := by
  unfold normalizedHammingWeight
  rcases Nat.eq_zero_or_pos (Fintype.card κ) with h0 | hpos
  · simp [h0]
  · rw [div_le_one (Nat.cast_pos.mpr hpos)]
    exact_mod_cast hammingNorm_le_card_fintype

@[simp]
theorem normalizedHammingWeight_zero {α κ : Type*} [Fintype κ] [Zero α] [DecidableEq α] :
    normalizedHammingWeight (0 : κ → α) = 0 := by
  simp [normalizedHammingWeight]

theorem one_sub_normalizedHammingWeight {α κ : Type*} [Fintype κ] [Nonempty κ] [Zero α]
    [DecidableEq α] (u : κ → α) :
    1 - normalizedHammingWeight u = (empiricalPMF u 0).toReal := by
  rw [empiricalPMF_apply_toReal, normalizedHammingWeight]
  have hcard : (Finset.univ.filter fun i : κ ↦ u i = 0).card + hammingNorm u =
      Fintype.card κ := by
    rw [hammingNorm]
    have hcompl := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : κ ↦ u i = 0)
    simpa only [Finset.card_univ] using hcompl
  have hcast : ((Finset.univ.filter fun i : κ ↦ u i = 0).card : ℝ) + (hammingNorm u : ℝ) =
      (Fintype.card κ : ℝ) := by exact_mod_cast hcard
  have hk : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hk]
  linarith

/-- Normalized Hamming weight expressed via the scalar Fourier transform of `empiricalPMF u`. -/
theorem normalizedHammingWeight_eq_fourier {F κ : Type*} [Field F] [Fintype F]
    [Fintype κ] [Nonempty κ] [DecidableEq F] (u : κ → F) :
    (normalizedHammingWeight u : ℂ) =
      ((Fintype.card F : ℂ) - 1) / (Fintype.card F : ℂ) -
        (Fintype.card F : ℂ)⁻¹ *
          ∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
            fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a := by
  have hinv := fourier_inversion_scalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) 0
  have hzero : ∀ a : F, canonicalAddChar F (0 * a) = 1 := fun a ↦ by
    rw [zero_mul, canonicalAddChar_zero]
  simp_rw [hzero, mul_one] at hinv
  have hsplit :
      ∑ a : F, fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a =
        fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) 0 +
          ∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
            fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : F ↦ a = 0)]
    have h0 :
        ∑ a ∈ Finset.univ.filter (fun a : F ↦ a = 0),
            fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a =
          fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) 0 := by
      simp [Finset.filter_eq']
    rw [h0]
  have hf0 : fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) 0 = 1 := by
    rw [fourierTransformScalar_zero, ← Complex.ofReal_sum]
    have hsum1 : ∑ x : F, (empiricalPMF u x).toReal = 1 := by
      have htot : ∑ x : F, empiricalPMF u x = 1 :=
        (tsum_fintype (fun x : F ↦ empiricalPMF u x)).symm.trans (PMF.tsum_coe _)
      rw [← ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _), htot, ENNReal.toReal_one]
    rw [hsum1, Complex.ofReal_one]
  rw [hsplit, hf0] at hinv
  have hwt : (normalizedHammingWeight u : ℂ) = 1 - ((empiricalPMF u 0).toReal : ℂ) := by
    have h := one_sub_normalizedHammingWeight u
    have h' : normalizedHammingWeight u = 1 - (empiricalPMF u 0).toReal := by linarith
    rw [h']
    push_cast
    rfl
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hwt, hinv]
  field_simp [hq]
  ring

/-- A vector `u : κ → F` is `η`-biased if `‖∑ i, χ(a · u_i)‖ ≤ |κ| · η` for all `a ≠ 0`. -/
def IsVectorBiased {F κ : Type*} [Field F] [Fintype F] [Fintype κ] (η : ℝ) (u : κ → F) : Prop :=
  ∀ a : F, a ≠ 0 → ‖∑ i : κ, canonicalAddChar F (a * u i)‖ ≤ (Fintype.card κ : ℝ) * η

theorem isVectorBiased_iff {F κ : Type*} [Field F] [Fintype F] [Fintype κ] {η : ℝ}
    {u : κ → F} :
    IsVectorBiased η u ↔
      ∀ a : F, a ≠ 0 → ‖∑ i : κ, canonicalAddChar F (a * u i)‖ ≤ (Fintype.card κ : ℝ) * η := by
  rfl

theorem isVectorBiased_iff_fourier {F κ : Type*} [Field F] [Fintype F] [Fintype κ] [Nonempty κ]
    {η : ℝ} {u : κ → F} :
    IsVectorBiased η u ↔
      ∀ a : F, a ≠ 0 →
        ‖fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖ ≤ η := by
  have hk : (0 : ℝ) < (Fintype.card κ : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  constructor <;> intro h a ha
  · have hnorm :
        ‖fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖ =
          (Fintype.card κ : ℝ)⁻¹ * ‖∑ i : κ, canonicalAddChar F (a * u i)‖ := by
      rw [fourierTransformScalar_empiricalPMF_eq, norm_mul, norm_inv, Complex.norm_natCast]
      congr 1
      have hconj :
          ∑ i : κ, conj (canonicalAddChar F (u i * a)) =
            conj (∑ i : κ, canonicalAddChar F (a * u i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]
      rw [hconj, RCLike.norm_conj]
    rw [hnorm, inv_mul_le_iff₀ hk]
    exact h a ha
  · have hnorm :
        ‖∑ i : κ, canonicalAddChar F (a * u i)‖ =
          (Fintype.card κ : ℝ) *
            ‖fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖ := by
      rw [fourierTransformScalar_empiricalPMF_eq, norm_mul, norm_inv, Complex.norm_natCast,
        mul_inv_cancel_left₀ hk.ne']
      have hconj :
          ∑ i : κ, conj (canonicalAddChar F (u i * a)) =
            conj (∑ i : κ, canonicalAddChar F (a * u i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]
      rw [hconj, RCLike.norm_conj]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (h a ha) hk.le

/-- Two-sided Hamming weight bound for an `η`-biased vector. -/
theorem normalizedHammingWeight_bounds_of_isVectorBiased {F κ : Type*} [Field F] [Fintype F]
    [Fintype κ] [Nonempty κ] [DecidableEq F] {η : ℝ} {u : κ → F} (hu : IsVectorBiased η u) :
    ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) * (1 - η) ≤ normalizedHammingWeight u ∧
      normalizedHammingWeight u ≤
        ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) * (1 + η) := by
  have hfourier := normalizedHammingWeight_eq_fourier u
  have hdiff :
      ((normalizedHammingWeight u -
          ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) : ℝ) : ℂ) =
        -((Fintype.card F : ℂ)⁻¹ *
          ∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
            fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a) := by
    push_cast
    rw [hfourier]
    ring
  have habs :
      |normalizedHammingWeight u - ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ)| ≤
        ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) * η := by
    have hnorm :
        |normalizedHammingWeight u - ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ)| =
          ‖((normalizedHammingWeight u -
            ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) : ℝ) : ℂ)‖ :=
      (Complex.norm_real _).symm
    rw [hnorm, hdiff, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
    have hsum :
        ‖∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
            fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖ ≤
          ((Fintype.card F : ℝ) - 1) * η := by
      calc
        ‖∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
            fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖
            ≤ ∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
                ‖fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0), η :=
          Finset.sum_le_sum fun a ha ↦
            isVectorBiased_iff_fourier.mp hu a (Finset.mem_filter.mp ha).2
        _ = ((Finset.univ.filter (fun a : F ↦ a ≠ 0)).card : ℝ) * η := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((Fintype.card F : ℝ) - 1) * η := by
          congr 1
          have hcard : (Finset.univ.filter (fun a : F ↦ a ≠ 0)).card + 1 = Fintype.card F := by
            have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
              (p := fun a : F ↦ a ≠ 0)
            simpa only [not_not, Finset.filter_eq', Finset.mem_univ, ite_true,
              Finset.card_singleton, Finset.card_univ] using this
          have hcast : ((Finset.univ.filter (fun a : F ↦ a ≠ 0)).card : ℝ) + 1 =
              (Fintype.card F : ℝ) := by exact_mod_cast hcard
          linarith
    have hq_nonneg : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
    calc
      (Fintype.card F : ℝ)⁻¹ *
          ‖∑ a ∈ Finset.univ.filter (fun a : F ↦ a ≠ 0),
              fourierTransformScalar (fun x ↦ ((empiricalPMF u x).toReal : ℂ)) a‖
          ≤ (Fintype.card F : ℝ)⁻¹ * (((Fintype.card F : ℝ) - 1) * η) :=
        mul_le_mul_of_nonneg_left hsum hq_nonneg
      _ = ((Fintype.card F : ℝ) - 1) / (Fintype.card F : ℝ) * η := by ring
  have hpair := abs_le.mp habs
  constructor <;> linarith

/-- Generalized `ℓ¹`-Fourier Vazirani XOR-lemma: for any distribution `σ` over `ι → F` and any
nonnegative `f : (ι → F) → ℝ`,
`𝔼_{x ~ σ}[f x] ≤ (∑ y, ‖σ̂(y)‖) · 𝔼_{x ~ U(ι → F)}[f x]`. -/
theorem expect_le_sum_norm_fourier_mul_uniform {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    [DecidableEq ι] (σ : PMF (ι → F)) (f : (ι → F) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x : ι → F, (σ x).toReal * f x ≤
      (∑ y : ι → F, ‖fourierTransform (fun x ↦ ((σ x).toReal : ℂ)) y‖) *
        (((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x : ι → F, f x) := by
  have hpointwise : ∀ x : ι → F,
      (σ x).toReal ≤
        ((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ *
          ∑ y : ι → F, ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y‖ := by
    intro x
    have hinv := fourier_inversion (fun z ↦ ((σ z).toReal : ℂ)) x
    have hle :
        (σ x).toReal = ‖(((σ x).toReal : ℂ))‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [hle, hinv, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      ‖∑ y : ι → F, fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
          canonicalAddChar F (dotProduct x y)‖
          ≤ ∑ y : ι → F, ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
              canonicalAddChar F (dotProduct x y)‖ := norm_sum_le _ _
      _ = ∑ y : ι → F, ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y‖ := by
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [norm_mul, norm_canonicalAddChar, mul_one]
  calc
    ∑ x : ι → F, (σ x).toReal * f x
        ≤ ∑ x : ι → F,
            (((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ *
              ∑ y : ι → F, ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y‖) * f x :=
      Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (hpointwise x) (hf x)
    _ = (∑ y : ι → F, ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y‖) *
          (((Fintype.card F : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x : ι → F, f x) := by
      rw [← Finset.mul_sum]
      ring

/-- Over `ZMod 2`, the canonical additive character evaluates to `(-1) ^ x.val`. -/
theorem canonicalAddChar_zmod_two (x : ZMod 2) :
    canonicalAddChar (ZMod 2) x = if x = 0 then 1 else -1 := by
  have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have h1 : canonicalAddChar (ZMod 2) 1 = -1 := by
    have hsq : canonicalAddChar (ZMod 2) 1 * canonicalAddChar (ZMod 2) 1 = 1 := by
      rw [← canonicalAddChar_add, show (1 : ZMod 2) + 1 = 0 by decide, canonicalAddChar_zero]
    have hne : canonicalAddChar (ZMod 2) 1 ≠ 1 := by
      obtain ⟨b, hb⟩ := exists_canonicalAddChar_ne_one (ZMod 2) (one_ne_zero : (1 : ZMod 2) ≠ 0)
      rcases hz2 b with rfl | rfl
      · simp at hb
      · simpa only [one_mul] using hb
    have hfac : (canonicalAddChar (ZMod 2) 1 - 1) * (canonicalAddChar (ZMod 2) 1 + 1) = 0 := by
      linear_combination hsq
    have hadd := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    linear_combination hadd
  rcases hz2 x with rfl | rfl
  · simp
  · simp [h1]

/-- Pointwise closeness to uniform from binary parity bias (Vazirani XOR-lemma). -/
theorem abs_sub_uniform_le_of_dotProduct_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : PMF (ι → ZMod 2)) {η : ℝ} (hη : 0 ≤ η)
    (hbias : ∀ y : ι → ZMod 2, y ≠ 0 →
      (1 - η) / 2 ≤ ∑ x : ι → ZMod 2, (if dotProduct x y = 1 then (σ x).toReal else 0) ∧
      ∑ x : ι → ZMod 2, (if dotProduct x y = 1 then (σ x).toReal else 0) ≤ (1 + η) / 2)
    (x : ι → ZMod 2) :
    |(σ x).toReal - (PMF.uniformOfFintype (ι → ZMod 2) x).toReal| ≤ η := by
  have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hsum1 : ∑ z : ι → ZMod 2, (σ z).toReal = 1 := by
    have htot : ∑ z : ι → ZMod 2, σ z = 1 :=
      (tsum_fintype (fun z : ι → ZMod 2 ↦ σ z)).symm.trans (PMF.tsum_coe _)
    rw [← ENNReal.toReal_sum (fun _ _ ↦ PMF.apply_ne_top _ _), htot, ENNReal.toReal_one]
  have hinv := fourier_inversion (fun z ↦ ((σ z).toReal : ℂ)) x
  have h0 : fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) 0 = 1 := by
    rw [fourierTransform_zero, ← Complex.ofReal_sum, hsum1, Complex.ofReal_one]
  have hunif : (PMF.uniformOfFintype (ι → ZMod 2) x).toReal =
      ((2 : ℝ) ^ Fintype.card ι)⁻¹ := by
    simp [PMF.uniformOfFintype_apply]
  have hfourier_bound : ∀ y : ι → ZMod 2, y ≠ 0 →
      ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y‖ ≤ η := by
    intro y hy
    have hft : fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y =
        ((1 - 2 * ∑ z : ι → ZMod 2, (if dotProduct z y = 1 then (σ z).toReal else 0) : ℝ) :
          ℂ) := by
      unfold fourierTransform
      have hterm : ∀ z : ι → ZMod 2,
          ((σ z).toReal : ℂ) * conj (canonicalAddChar (ZMod 2) (dotProduct z y)) =
            (((if dotProduct z y = 1 then -(σ z).toReal else (σ z).toReal) : ℝ) : ℂ) := by
        intro z
        rw [canonicalAddChar_zmod_two]
        rcases hz2 (dotProduct z y) with h0' | h1'
        · simp [h0']
        · simp [h1']
      simp_rw [hterm]
      rw [← Complex.ofReal_sum]
      congr 1
      have hsplit :
          ∑ z : ι → ZMod 2, (if dotProduct z y = 1 then -(σ z).toReal else (σ z).toReal) =
            (∑ z : ι → ZMod 2, (σ z).toReal) -
              2 * ∑ z : ι → ZMod 2, (if dotProduct z y = 1 then (σ z).toReal else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        split_ifs <;> ring
      rw [hsplit, hsum1]
    rw [hft, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨hlo, hhi⟩ := hbias y hy
    rw [abs_le]
    constructor <;> linarith
  have hdiff :
      (((σ x).toReal - (PMF.uniformOfFintype (ι → ZMod 2) x).toReal : ℝ) : ℂ) =
        (((2 : ℂ) ^ Fintype.card ι)⁻¹) *
          ∑ y ∈ Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0),
            fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
              canonicalAddChar (ZMod 2) (dotProduct x y) := by
    have hsplit :
        ∑ y : ι → ZMod 2,
            fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
              canonicalAddChar (ZMod 2) (dotProduct x y) =
          1 + ∑ y ∈ Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0),
            fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
              canonicalAddChar (ZMod 2) (dotProduct x y) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : ι → ZMod 2 ↦ y = 0)]
      have hzero :
          ∑ y ∈ Finset.univ.filter (fun y : ι → ZMod 2 ↦ y = 0),
              fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
                canonicalAddChar (ZMod 2) (dotProduct x y) = 1 := by
        simp [Finset.filter_eq', h0]
      rw [hzero]
    rw [hunif]
    push_cast
    rw [hinv, hsplit]
    simp only [ZMod.card, Nat.cast_ofNat]
    ring
  have hnorm :
      |(σ x).toReal - (PMF.uniformOfFintype (ι → ZMod 2) x).toReal| =
        ‖(((σ x).toReal - (PMF.uniformOfFintype (ι → ZMod 2) x).toReal : ℝ) : ℂ)‖ :=
    (Real.norm_eq_abs _).symm.trans (Complex.norm_real _).symm
  rw [hnorm, hdiff, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc
    ((2 : ℝ) ^ Fintype.card ι)⁻¹ *
        ‖∑ y ∈ Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0),
            fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
              canonicalAddChar (ZMod 2) (dotProduct x y)‖
        ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ *
            ∑ y ∈ Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0),
              ‖fourierTransform (fun z ↦ ((σ z).toReal : ℂ)) y *
                canonicalAddChar (ZMod 2) (dotProduct x y)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ *
          ∑ _y ∈ Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0), η := by
      gcongr with y hy
      rw [norm_mul, norm_canonicalAddChar, mul_one]
      exact hfourier_bound y (Finset.mem_filter.mp hy).2
    _ = ((2 : ℝ) ^ Fintype.card ι)⁻¹ *
          (((Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0)).card : ℝ) * η) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ((2 : ℝ) ^ Fintype.card ι * η) := by
      have hcard_le : ((Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0)).card : ℝ) ≤
          (2 : ℝ) ^ Fintype.card ι := by
        have h1 : (Finset.univ.filter (fun y : ι → ZMod 2 ↦ y ≠ 0)).card ≤
            Fintype.card (ι → ZMod 2) := Finset.card_filter_le _ _
        have h2 : (Fintype.card (ι → ZMod 2) : ℝ) = (2 : ℝ) ^ Fintype.card ι := by
          simp [Fintype.card_pi, ZMod.card]
        rw [← h2]
        exact_mod_cast h1
      gcongr
    _ = η := by
      have hpow : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
      field_simp [hpow]

/-- Binary Vazirani XOR-lemma: if every nonzero parity of `σ : PMF (ι → ZMod 2)` has
`Pr[⟨x, y⟩ = 1] ∈ [(1 - η)/2, (1 + η)/2]` with `0 ≤ η`, then `σ` is `(2 ^ |ι| * η)`-close in
total-variation distance to the uniform distribution on `ι → ZMod 2`. -/
theorem tvDist_uniform_le_of_dotProduct_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : PMF (ι → ZMod 2)) {η : ℝ} (hη : 0 ≤ η)
    (hbias : ∀ y : ι → ZMod 2, y ≠ 0 →
      (1 - η) / 2 ≤ ∑ x : ι → ZMod 2, (if dotProduct x y = 1 then (σ x).toReal else 0) ∧
      ∑ x : ι → ZMod 2, (if dotProduct x y = 1 then (σ x).toReal else 0) ≤ (1 + η) / 2) :
    (1 / 2 : ℝ) * ∑ x : ι → ZMod 2,
        |(σ x).toReal - (PMF.uniformOfFintype (ι → ZMod 2) x).toReal| ≤
      (2 : ℝ) ^ Fintype.card ι * η := by
  calc
    (1 / 2 : ℝ) * ∑ x : ι → ZMod 2,
        |(σ x).toReal - (PMF.uniformOfFintype (ι → ZMod 2) x).toReal|
        ≤ (1 / 2 : ℝ) * ∑ _x : ι → ZMod 2, η := by
      gcongr with x _
      exact abs_sub_uniform_le_of_dotProduct_bias σ hη hbias x
    _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ Fintype.card ι * η) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [Fintype.card_pi, ZMod.card]
    _ ≤ (2 : ℝ) ^ Fintype.card ι * η := by
      have hpos : 0 ≤ (2 : ℝ) ^ Fintype.card ι * η := by positivity
      linarith

end CslibFrontier.Foundations.Data.Code
