/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrete Fourier Analysis over Finite Weighted Product Spaces

This module develops foundational product-space analysis, juntas, subset resampling operators, and
orthonormal Fourier bases on finite weighted product probability spaces `(ι → A, ν^⊗ι)` under
standard Lean axioms. Efron–Stein decompositions, noise operators, and coordinate influences are
developed in `CslibFrontier.Analysis.Fourier.EfronStein`.

## Main definitions

* `CslibFrontier.Analysis.Fourier.piWeight`, `piExpect`, `piExpectReal`, `piInner`, `l2NormSq`,
  `l2Norm`, `lpNorm`: product probability weight, expectation, `L²` inner product, and `L^p` norms.
* `CslibFrontier.Analysis.Fourier.IsJunta`, `IsDegJunta`, `degSubspace`, `pureDegSubspace`:
  juntas, degree-`d` subspace `V_{≤ d}`, and pure degree-`d` subspace `V_{= d}`.
* `CslibFrontier.Analysis.Fourier.coordCondExpect`, `subsetResampleOp`:
  coordinate conditional expectation and subset resampling operator `T_I`.
* `CslibFrontier.Analysis.Fourier.OrthonormalFourierBasis`:
  real orthonormal basis `{v_0 ≡ 1, v_1, …, v_{m-1}}` of `L²(A, ν)` and its tensor basis.

## Main results

* `CslibFrontier.Analysis.Fourier.subsetResampleOp_comp`: semigroup law `T_I ∘ T_J = T_{I ∪ J}`.
* `CslibFrontier.Analysis.Fourier.piInner_subsetResampleOp_left`: self-adjointness of `T_I`.
* `CslibFrontier.Analysis.Fourier.exists_orthonormalFourierBasis`: existence of a real orthonormal
  Fourier basis with `v_0 ≡ 1` on any full-support finite probability space.
* `CslibFrontier.Analysis.Fourier.OrthonormalFourierBasis.fourier_expansion`: full-support tensor
  Fourier expansion identity `f(x) = ∑_α f̂(α) v_α(x)`.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Analysis.Fourier

section ProductSpace

variable {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]

/-- The product probability weight `ν^⊗ι(x) = ∏ i, (ν (x i)).toReal`. -/
@[expose] noncomputable def piWeight (ν : PMF A) (x : ι → A) : ℝ :=
  ∏ i : ι, (ν (x i)).toReal

/-- Expectation of a complex-valued function on `(ι → A, ν^⊗ι)`. -/
@[expose] noncomputable def piExpect (ν : PMF A) (f : (ι → A) → ℂ) : ℂ :=
  ∑ x : ι → A, (piWeight ν x : ℂ) * f x

/-- Real expectation of a real-valued function on `(ι → A, ν^⊗ι)`. -/
@[expose] noncomputable def piExpectReal (ν : PMF A) (f : (ι → A) → ℝ) : ℝ :=
  ∑ x : ι → A, piWeight ν x * f x

/-- Standard `L²` inner product `⟨f, g⟩ = E_{x ~ ν^⊗ι}[f(x) * conj(g(x))]`. -/
@[expose] noncomputable def piInner (ν : PMF A) (f g : (ι → A) → ℂ) : ℂ :=
  piExpect ν (fun x ↦ f x * starRingEnd ℂ (g x))

/-- Squared `L²` norm `‖f‖₂² = E_{x ~ ν^⊗ι}[‖f(x)‖²]`. -/
@[expose] noncomputable def l2NormSq (ν : PMF A) (f : (ι → A) → ℂ) : ℝ :=
  piExpectReal ν (fun x ↦ ‖f x‖ ^ 2)

/-- `L²` norm `‖f‖₂ = √(E_{x ~ ν^⊗ι}[‖f(x)‖²])`. -/
@[expose] noncomputable def l2Norm (ν : PMF A) (f : (ι → A) → ℂ) : ℝ :=
  Real.sqrt (l2NormSq ν f)

/-- `L^q` norm `‖f‖_q = (E_{x ~ ν^⊗ι}[‖f(x)‖^q])^{1/q}` for real `q`. -/
@[expose] noncomputable def lpNorm (ν : PMF A) (q : ℝ) (f : (ι → A) → ℂ) : ℝ :=
  (piExpectReal ν (fun x ↦ ‖f x‖ ^ q)) ^ (1 / q)

/-- Pointwise `B`-boundedness of a complex-valued function. -/
@[expose] def IsBoundedBy {α : Type*} (B : ℝ) (f : α → ℂ) : Prop :=
  ∀ x, ‖f x‖ ≤ B

omit [Fintype A] [DecidableEq ι] in
lemma piWeight_eq_prod (ν : PMF A) (x : ι → A) :
    piWeight ν x = ∏ i : ι, (ν (x i)).toReal :=
  rfl

omit [Fintype ι] [Fintype A] [DecidableEq ι] in
lemma piWeight_fin_cons {n : ℕ} (ν : PMF A) (a : A) (y : Fin n → A) :
    piWeight ν (Fin.cons a y) = (ν a).toReal * piWeight ν y := by
  unfold piWeight; rw [Fin.prod_univ_succ]; simp

omit [Fintype ι] [Fintype A] [DecidableEq ι] in
@[simp]
lemma piWeight_fin_zero (ν : PMF A) (x : Fin 0 → A) : piWeight ν x = 1 := by
  simp [piWeight]

lemma piExpect_eq_sum (ν : PMF A) (f : (ι → A) → ℂ) :
    piExpect ν f = ∑ x : ι → A, (piWeight ν x : ℂ) * f x :=
  rfl

@[simp]
lemma piExpect_zero (ν : PMF A) : piExpect ν (0 : (ι → A) → ℂ) = 0 := by
  unfold piExpect; simp

lemma piExpectReal_eq_sum (ν : PMF A) (f : (ι → A) → ℝ) :
    piExpectReal ν f = ∑ x : ι → A, piWeight ν x * f x :=
  rfl

@[simp]
lemma piExpectReal_zero (ν : PMF A) : piExpectReal ν (0 : (ι → A) → ℝ) = 0 := by
  unfold piExpectReal; simp

lemma piInner_eq_piExpect (ν : PMF A) (f g : (ι → A) → ℂ) :
    piInner ν f g = piExpect ν (fun x ↦ f x * starRingEnd ℂ (g x)) :=
  rfl

lemma piInner_eq_sum (ν : PMF A) (f g : (ι → A) → ℂ) :
    piInner ν f g = ∑ x : ι → A, (piWeight ν x : ℂ) * (f x * starRingEnd ℂ (g x)) :=
  rfl

lemma l2NormSq_eq_piExpectReal (ν : PMF A) (f : (ι → A) → ℂ) :
    l2NormSq ν f = piExpectReal ν (fun x ↦ ‖f x‖ ^ 2) :=
  rfl

lemma l2NormSq_eq_sum (ν : PMF A) (f : (ι → A) → ℂ) :
    l2NormSq ν f = ∑ x : ι → A, piWeight ν x * ‖f x‖ ^ 2 :=
  rfl

lemma l2Norm_eq_sqrt (ν : PMF A) (f : (ι → A) → ℂ) :
    l2Norm ν f = Real.sqrt (l2NormSq ν f) :=
  rfl

lemma lpNorm_eq_rpow (ν : PMF A) (q : ℝ) (f : (ι → A) → ℂ) :
    lpNorm ν q f = (piExpectReal ν (fun x ↦ ‖f x‖ ^ q)) ^ (1 / q) :=
  rfl

omit [Fintype A] [DecidableEq ι] in
lemma piWeight_nonneg (ν : PMF A) (x : ι → A) : 0 ≤ piWeight ν x :=
  Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg

omit [Fintype A] [DecidableEq ι] in
lemma piWeight_pos (ν : PMF A) (hν : ∀ a, 0 < ν a) (x : ι → A) : 0 < piWeight ν x :=
  Finset.prod_pos fun i _ ↦ ENNReal.toReal_pos (ne_of_gt (hν (x i))) (ν.apply_ne_top (x i))

omit [Fintype ι] [DecidableEq ι] in
lemma sum_pmf_toReal (ν : PMF A) : ∑ a : A, (ν a).toReal = 1 := by
  have h := ν.tsum_coe
  rw [tsum_fintype] at h
  have hne : ∀ a ∈ (Finset.univ : Finset A), ν a ≠ ⊤ := fun a _ ↦ ν.apply_ne_top a
  have h1 := ENNReal.toReal_sum hne
  rw [h] at h1
  simpa using h1.symm

lemma sum_piWeight (ν : PMF A) : ∑ x : ι → A, piWeight ν x = 1 := by
  unfold piWeight
  rw [← Fintype.prod_sum (fun _ a ↦ (ν a).toReal)]
  simp [sum_pmf_toReal]

lemma piExpectReal_const (ν : PMF A) (c : ℝ) :
    piExpectReal ν (fun _ : ι → A ↦ c) = c := by
  unfold piExpectReal
  rw [← Finset.sum_mul, sum_piWeight, one_mul]

lemma piExpect_const (ν : PMF A) (c : ℂ) :
    piExpect ν (fun _ : ι → A ↦ c) = c := by
  unfold piExpect
  rw [← Finset.sum_mul]
  have h : (∑ x : ι → A, (piWeight ν x : ℂ)) = 1 := by
    exact_mod_cast sum_piWeight (ι := ι) ν
  rw [h, one_mul]

lemma piExpect_add (ν : PMF A) (f g : (ι → A) → ℂ) :
    piExpect ν (f + g) = piExpect ν f + piExpect ν g := by
  unfold piExpect
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma piExpect_sub (ν : PMF A) (f g : (ι → A) → ℂ) :
    piExpect ν (f - g) = piExpect ν f - piExpect ν g := by
  unfold piExpect
  simp [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma piExpect_smul (ν : PMF A) (c : ℂ) (f : (ι → A) → ℂ) :
    piExpect ν (fun x ↦ c * f x) = c * piExpect ν f := by
  unfold piExpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

lemma piExpect_sum {κ : Type*} (ν : PMF A) (s : Finset κ) (f : κ → (ι → A) → ℂ) :
    piExpect ν (fun x ↦ ∑ k ∈ s, f k x) = ∑ k ∈ s, piExpect ν (f k) := by
  unfold piExpect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma piExpectReal_add (ν : PMF A) (f g : (ι → A) → ℝ) :
    piExpectReal ν (f + g) = piExpectReal ν f + piExpectReal ν g := by
  unfold piExpectReal
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma piExpectReal_smul (ν : PMF A) (c : ℝ) (f : (ι → A) → ℝ) :
    piExpectReal ν (fun x ↦ c * f x) = c * piExpectReal ν f := by
  unfold piExpectReal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

lemma piExpectReal_sum {κ : Type*} (ν : PMF A) (s : Finset κ) (f : κ → (ι → A) → ℝ) :
    piExpectReal ν (fun x ↦ ∑ k ∈ s, f k x) = ∑ k ∈ s, piExpectReal ν (f k) := by
  unfold piExpectReal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma piExpectReal_nonneg (ν : PMF A) {f : (ι → A) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ piExpectReal ν f :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg (piWeight_nonneg ν x) (hf x)

lemma piExpectReal_mono (ν : PMF A) {f g : (ι → A) → ℝ} (hfg : ∀ x, f x ≤ g x) :
    piExpectReal ν f ≤ piExpectReal ν g :=
  Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hfg x) (piWeight_nonneg ν x)

lemma norm_piExpect_le (ν : PMF A) (f : (ι → A) → ℂ) :
    ‖piExpect ν f‖ ≤ piExpectReal ν (fun x ↦ ‖f x‖) := by
  unfold piExpect piExpectReal
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun x _ ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (piWeight_nonneg ν x)]

lemma piInner_self (ν : PMF A) (f : (ι → A) → ℂ) :
    piInner ν f f = (l2NormSq ν f : ℂ) := by
  unfold piInner piExpect l2NormSq piExpectReal
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  dsimp only
  rw [Complex.ofReal_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma l2NormSq_nonneg (ν : PMF A) (f : (ι → A) → ℂ) : 0 ≤ l2NormSq ν f :=
  piExpectReal_nonneg ν fun _ ↦ sq_nonneg _

lemma l2Norm_nonneg (ν : PMF A) (f : (ι → A) → ℂ) : 0 ≤ l2Norm ν f :=
  Real.sqrt_nonneg _

lemma l2Norm_sq (ν : PMF A) (f : (ι → A) → ℂ) : (l2Norm ν f) ^ 2 = l2NormSq ν f :=
  Real.sq_sqrt (l2NormSq_nonneg ν f)

lemma l2NormSq_zero (ν : PMF A) : l2NormSq ν (0 : (ι → A) → ℂ) = 0 := by
  unfold l2NormSq piExpectReal; simp

lemma l2Norm_zero (ν : PMF A) : l2Norm ν (0 : (ι → A) → ℂ) = 0 := by
  unfold l2Norm; simp [l2NormSq_zero]

lemma piInner_conj_symm (ν : PMF A) (f g : (ι → A) → ℂ) :
    starRingEnd ℂ (piInner ν f g) = piInner ν g f := by
  unfold piInner piExpect
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [Complex.conj_ofReal, mul_comm]

lemma piInner_add_left (ν : PMF A) (f₁ f₂ g : (ι → A) → ℂ) :
    piInner ν (f₁ + f₂) g = piInner ν f₁ g + piInner ν f₂ g := by
  unfold piInner
  have : (fun x ↦ (f₁ + f₂) x * starRingEnd ℂ (g x)) =
      (fun x ↦ f₁ x * starRingEnd ℂ (g x)) + (fun x ↦ f₂ x * starRingEnd ℂ (g x)) := by
    ext x; simp [add_mul]
  rw [this, piExpect_add]

lemma piInner_sub_left (ν : PMF A) (f₁ f₂ g : (ι → A) → ℂ) :
    piInner ν (f₁ - f₂) g = piInner ν f₁ g - piInner ν f₂ g := by
  unfold piInner
  have : (fun x ↦ (f₁ - f₂) x * starRingEnd ℂ (g x)) =
      (fun x ↦ f₁ x * starRingEnd ℂ (g x)) - (fun x ↦ f₂ x * starRingEnd ℂ (g x)) := by
    ext x; simp [sub_mul]
  rw [this, piExpect_sub]

lemma piInner_add_right (ν : PMF A) (f g₁ g₂ : (ι → A) → ℂ) :
    piInner ν f (g₁ + g₂) = piInner ν f g₁ + piInner ν f g₂ := by
  unfold piInner
  have : (fun x ↦ f x * starRingEnd ℂ ((g₁ + g₂) x)) =
      (fun x ↦ f x * starRingEnd ℂ (g₁ x)) + (fun x ↦ f x * starRingEnd ℂ (g₂ x)) := by
    ext x; simp [mul_add]
  rw [this, piExpect_add]

lemma piInner_sub_right (ν : PMF A) (f g₁ g₂ : (ι → A) → ℂ) :
    piInner ν f (g₁ - g₂) = piInner ν f g₁ - piInner ν f g₂ := by
  unfold piInner
  have : (fun x ↦ f x * starRingEnd ℂ ((g₁ - g₂) x)) =
      (fun x ↦ f x * starRingEnd ℂ (g₁ x)) - (fun x ↦ f x * starRingEnd ℂ (g₂ x)) := by
    ext x; simp [mul_sub]
  rw [this, piExpect_sub]

lemma piInner_smul_left (ν : PMF A) (c : ℂ) (f g : (ι → A) → ℂ) :
    piInner ν (fun x ↦ c * f x) g = c * piInner ν f g := by
  unfold piInner
  have : (fun x ↦ c * f x * starRingEnd ℂ (g x)) =
      (fun x ↦ c * (f x * starRingEnd ℂ (g x))) := by ext x; ring
  rw [this, piExpect_smul]

lemma piInner_smul_right (ν : PMF A) (c : ℂ) (f g : (ι → A) → ℂ) :
    piInner ν f (fun x ↦ c * g x) = starRingEnd ℂ c * piInner ν f g := by
  unfold piInner
  have : (fun x ↦ f x * starRingEnd ℂ (c * g x)) =
      (fun x ↦ starRingEnd ℂ c * (f x * starRingEnd ℂ (g x))) := by
    ext x; simp; ring
  rw [this, piExpect_smul]

lemma piInner_zero_left (ν : PMF A) (g : (ι → A) → ℂ) : piInner ν 0 g = 0 := by
  unfold piInner piExpect; simp

lemma piInner_zero_right (ν : PMF A) (f : (ι → A) → ℂ) : piInner ν f 0 = 0 := by
  unfold piInner piExpect; simp

lemma piInner_sum_left {κ : Type*} (ν : PMF A) (s : Finset κ) (f : κ → (ι → A) → ℂ)
    (g : (ι → A) → ℂ) :
    piInner ν (fun x ↦ ∑ k ∈ s, f k x) g = ∑ k ∈ s, piInner ν (f k) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [piInner, piExpect]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h : (fun x ↦ f a x + ∑ k ∈ s, f k x) = f a + (fun x ↦ ∑ k ∈ s, f k x) := rfl
    rw [h, piInner_add_left, ih]

lemma piInner_sum_right {κ : Type*} (ν : PMF A) (f : (ι → A) → ℂ) (s : Finset κ)
    (g : κ → (ι → A) → ℂ) :
    piInner ν f (fun x ↦ ∑ k ∈ s, g k x) = ∑ k ∈ s, piInner ν f (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [piInner, piExpect]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h : (fun x ↦ g a x + ∑ k ∈ s, g k x) = g a + (fun x ↦ ∑ k ∈ s, g k x) := rfl
    rw [h, piInner_add_right, ih]

/-- Cauchy–Schwarz inequality on `L²(ι → A, ν^⊗ι)`. -/
lemma norm_piInner_le (ν : PMF A) (f g : (ι → A) → ℂ) :
    ‖piInner ν f g‖ ≤ l2Norm ν f * l2Norm ν g := by
  have h1 : ‖piInner ν f g‖ ≤ ∑ x : ι → A, (√(piWeight ν x) * ‖f x‖) *
      (√(piWeight ν x) * ‖g x‖) := by
    refine (norm_piExpect_le ν _).trans ?_
    unfold piExpectReal
    refine Finset.sum_le_sum fun x _ ↦ ?_
    dsimp only
    rw [norm_mul, Complex.norm_conj]
    have hw : √(piWeight ν x) * √(piWeight ν x) = piWeight ν x :=
      Real.mul_self_sqrt (piWeight_nonneg ν x)
    exact le_of_eq (by
      calc piWeight ν x * (‖f x‖ * ‖g x‖)
          = (√(piWeight ν x) * √(piWeight ν x)) * (‖f x‖ * ‖g x‖) := by rw [hw]
        _ = (√(piWeight ν x) * ‖f x‖) * (√(piWeight ν x) * ‖g x‖) := by ring)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι → A))
    (fun x ↦ √(piWeight ν x) * ‖f x‖) (fun x ↦ √(piWeight ν x) * ‖g x‖)
  refine h1.trans (hcs.trans_eq ?_)
  congr 1
  · unfold l2Norm l2NormSq piExpectReal
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt (piWeight_nonneg ν x)]
  · unfold l2Norm l2NormSq piExpectReal
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt (piWeight_nonneg ν x)]

/-- Minkowski / triangle inequality for `l2Norm`. -/
lemma l2Norm_add_le (ν : PMF A) (f g : (ι → A) → ℂ) :
    l2Norm ν (f + g) ≤ l2Norm ν f + l2Norm ν g := by
  have hsq : l2NormSq ν (f + g) ≤ (l2Norm ν f + l2Norm ν g) ^ 2 := by
    have hexp : (l2NormSq ν (f + g) : ℂ) =
        (l2NormSq ν f : ℂ) + piInner ν f g + piInner ν g f + (l2NormSq ν g : ℂ) := by
      rw [← piInner_self, ← piInner_self, ← piInner_self,
        piInner_add_left, piInner_add_right, piInner_add_right]
      ring
    have hre : l2NormSq ν (f + g) =
        l2NormSq ν f + 2 * (piInner ν f g).re + l2NormSq ν g := by
      have hconj : piInner ν g f = starRingEnd ℂ (piInner ν f g) := (piInner_conj_symm ν f g).symm
      rw [hconj] at hexp
      have hre' := congr_arg Complex.re hexp
      simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at hre'
      linarith
    have hcs : (piInner ν f g).re ≤ l2Norm ν f * l2Norm ν g :=
      (Complex.re_le_norm _).trans (norm_piInner_le ν f g)
    rw [hre, add_sq, l2Norm_sq, l2Norm_sq]
    linarith
  have hnonneg : 0 ≤ l2Norm ν f + l2Norm ν g := add_nonneg (l2Norm_nonneg ν f) (l2Norm_nonneg ν g)
  rw [l2Norm]
  exact Real.sqrt_le_iff.mpr ⟨hnonneg, hsq⟩

/-- Triangle inequality for `l2Norm` over a finite sum. -/
lemma l2Norm_sum_le {κ : Type*} (ν : PMF A) (s : Finset κ) (f : κ → (ι → A) → ℂ) :
    l2Norm ν (fun x ↦ ∑ k ∈ s, f k x) ≤ ∑ k ∈ s, l2Norm ν (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (l2Norm_zero ν).le
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h : (fun x ↦ f a x + ∑ k ∈ s, f k x) = f a + (fun x ↦ ∑ k ∈ s, f k x) := rfl
    rw [h]
    exact (l2Norm_add_le ν _ _).trans (add_le_add le_rfl ih)

/-- Pythagorean theorem for pairwise orthogonal functions in `L²(ι → A, ν^⊗ι)`. -/
lemma l2NormSq_sum_of_pairwise_orth {κ : Type*} (ν : PMF A) (s : Finset κ)
    (f : κ → (ι → A) → ℂ) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → piInner ν (f i) (f j) = 0) :
    l2NormSq ν (fun x ↦ ∑ k ∈ s, f k x) = ∑ k ∈ s, l2NormSq ν (f k) := by
  have hc : (l2NormSq ν (fun x ↦ ∑ k ∈ s, f k x) : ℂ) = ∑ k ∈ s, (l2NormSq ν (f k) : ℂ) := by
    rw [← piInner_self, piInner_sum_left]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [piInner_sum_right, Finset.sum_eq_single i]
    · exact piInner_self ν (f i)
    · intro j hj hji; exact horth i hi j hj (Ne.symm hji)
    · intro hi'; exact absurd hi hi'
  exact_mod_cast hc

lemma l2NormSq_smul (ν : PMF A) (c : ℂ) (f : (ι → A) → ℂ) :
    l2NormSq ν (fun x ↦ c * f x) = ‖c‖ ^ 2 * l2NormSq ν f := by
  unfold l2NormSq
  have : (fun x ↦ ‖c * f x‖ ^ 2) = fun x ↦ ‖c‖ ^ 2 * ‖f x‖ ^ 2 := by
    ext x; rw [norm_mul, mul_pow]
  rw [this, piExpectReal_smul]

lemma l2Norm_smul (ν : PMF A) (c : ℂ) (f : (ι → A) → ℂ) :
    l2Norm ν (fun x ↦ c * f x) = ‖c‖ * l2Norm ν f := by
  unfold l2Norm
  rw [l2NormSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

lemma l2NormSq_sub_eq (ν : PMF A) (f g : (ι → A) → ℂ) :
    l2NormSq ν (f - g) = l2NormSq ν f - 2 * (piInner ν f g).re + l2NormSq ν g := by
  have hexp : (l2NormSq ν (f - g) : ℂ) =
      (l2NormSq ν f : ℂ) - piInner ν f g - piInner ν g f + (l2NormSq ν g : ℂ) := by
    rw [← piInner_self, ← piInner_self, ← piInner_self,
      piInner_sub_left, piInner_sub_right, piInner_sub_right]
    ring
  have hconj : piInner ν g f = starRingEnd ℂ (piInner ν f g) := (piInner_conj_symm ν f g).symm
  rw [hconj] at hexp
  have hre := congr_arg Complex.re hexp
  simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.conj_re] at hre
  linarith

lemma l2Norm_le_of_isBoundedBy (ν : PMF A) {B : ℝ} (hB : 0 ≤ B) {f : (ι → A) → ℂ}
    (hf : IsBoundedBy B f) : l2Norm ν f ≤ B := by
  unfold l2Norm
  refine Real.sqrt_le_iff.mpr ⟨hB, ?_⟩
  calc l2NormSq ν f
      ≤ piExpectReal ν (fun _ ↦ B ^ 2) :=
        piExpectReal_mono ν fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
    _ = B ^ 2 := piExpectReal_const ν _

lemma l2NormSq_eq_zero_iff (ν : PMF A) (hν : ∀ a, 0 < ν a) (f : (ι → A) → ℂ) :
    l2NormSq ν f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext x
    unfold l2NormSq piExpectReal at h
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦
      mul_nonneg (piWeight_nonneg ν y) (sq_nonneg _)).mp h x (Finset.mem_univ x)
    have hpos : 0 < piWeight ν x := piWeight_pos ν hν x
    have hsq : ‖f x‖ ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_left (ne_of_gt hpos)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · rintro rfl
    exact l2NormSq_zero ν

/-- Jensen's inequality for `‖E[f]‖² ≤ E[‖f‖²]`. -/
lemma norm_piExpect_sq_le (ν : PMF A) (f : (ι → A) → ℂ) :
    ‖piExpect ν f‖ ^ 2 ≤ l2NormSq ν f := by
  have h : piExpect ν f = piInner ν f (fun _ ↦ 1) := by
    unfold piInner; simp
  rw [h]
  have hcs := norm_piInner_le ν f (fun _ ↦ 1)
  have h1 : l2Norm ν (fun _ : ι → A ↦ (1 : ℂ)) = 1 := by
    unfold l2Norm l2NormSq
    simp [piExpectReal_const]
  rw [h1, mul_one] at hcs
  calc ‖piInner ν f (fun _ ↦ 1)‖ ^ 2 ≤ (l2Norm ν f) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ = l2NormSq ν f := l2Norm_sq ν f

end ProductSpace

section ResamplingAndJuntas

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Pointwise coordinatewise update on a subset `I : Finset ι`, keeping `Iᶜ` fixed to `x` and
replacing `I` by `y`. -/
@[expose] def splice (I : Finset ι) (x y : ι → A) : ι → A :=
  fun i ↦ if i ∈ I then y i else x i

omit [Fintype ι] [Fintype A] in
lemma splice_eq_ite (I : Finset ι) (x y : ι → A) (i : ι) :
    splice I x y i = if i ∈ I then y i else x i :=
  rfl

omit [Fintype ι] [Fintype A] in
lemma splice_of_mem {I : Finset ι} {i : ι} (hi : i ∈ I) (x y : ι → A) :
    splice I x y i = y i := by
  simp [splice, hi]

omit [Fintype ι] [Fintype A] in
lemma splice_of_notMem {I : Finset ι} {i : ι} (hi : i ∉ I) (x y : ι → A) :
    splice I x y i = x i := by
  simp [splice, hi]

omit [Fintype ι] [Fintype A] in
@[simp]
lemma splice_empty (x y : ι → A) : splice ∅ x y = x := by
  ext i; simp [splice]

omit [Fintype A] in
@[simp]
lemma splice_univ (x y : ι → A) : splice Finset.univ x y = y := by
  ext i; simp [splice]

omit [Fintype ι] [Fintype A] in
lemma splice_eq_self {I : Finset ι} {x y : ι → A} (h : ∀ i ∈ I, y i = x i) :
    splice I x y = x := by
  ext i; by_cases hi : i ∈ I <;> simp [splice, hi, h]

omit [Fintype ι] [Fintype A] in
lemma splice_splice_same (I : Finset ι) (x y z : ι → A) :
    splice I (splice I x y) z = splice I x z := by
  ext i; by_cases hi : i ∈ I <;> simp [splice, hi]

omit [Fintype ι] [Fintype A] in
lemma splice_comm {I J : Finset ι} (hIJ : Disjoint I J) (x y z : ι → A) :
    splice I (splice J x y) z = splice J (splice I x z) y := by
  ext i
  by_cases hi : i ∈ I
  · have hj : i ∉ J := Finset.disjoint_left.mp hIJ hi
    simp [splice, hi, hj]
  · simp [splice, hi]

/-- A function `f : (ι → A) → ℂ` is an `I`-junta if it depends only on the coordinates in `I`. -/
@[expose] def IsJunta (I : Finset ι) (f : (ι → A) → ℂ) : Prop :=
  ∀ x y : ι → A, (∀ i ∈ I, x i = y i) → f x = f y

/-- A function is a `d`-junta if it is an `I`-junta for some `I` with `|I| ≤ d`. -/
@[expose] def IsDegJunta (d : ℕ) (f : (ι → A) → ℂ) : Prop :=
  ∃ I : Finset ι, I.card ≤ d ∧ IsJunta I f

/-- The subspace `V_{≤ d}` of degree-`d` functions (span of all `d`-juntas). -/
@[expose] noncomputable def degSubspace (d : ℕ) : Submodule ℂ ((ι → A) → ℂ) :=
  Submodule.span ℂ {f | IsDegJunta d f}

/-- The pure degree-`d` subspace `V_{= d} = V_{≤ d} ∩ (V_{≤ d-1})^⊥` (with `V_{= 0} = V_{≤ 0}`). -/
@[expose] noncomputable def pureDegSubspace (ν : PMF A) : ℕ → Submodule ℂ ((ι → A) → ℂ)
  | 0 => degSubspace 0
  | d + 1 =>
    { carrier := {f | f ∈ degSubspace (d + 1) ∧ ∀ g ∈ degSubspace d, piInner ν f g = 0}
      add_mem' := fun {f₁ f₂} ⟨hf₁, ho₁⟩ ⟨hf₂, ho₂⟩ ↦
        ⟨Submodule.add_mem _ hf₁ hf₂, fun g hg ↦ by
          rw [piInner_add_left, ho₁ g hg, ho₂ g hg, add_zero]⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun g _ ↦ piInner_zero_left ν g⟩
      smul_mem' := fun c {f} ⟨hf, ho⟩ ↦
        ⟨Submodule.smul_mem _ c hf, fun g hg ↦ by
          change piInner ν (fun x ↦ c * f x) g = 0
          rw [piInner_smul_left, ho g hg, mul_zero]⟩ }

/-- Subset resampling operator `T_I f(x) = E_{y ~ ν^⊗ι}[f(splice I x y)]`:
fixes coordinates outside `I` and resamples coordinates in `I` independently from `ν`. -/
@[expose] noncomputable def subsetResampleOp (ν : PMF A) (I : Finset ι)
    (f : (ι → A) → ℂ) (x : ι → A) : ℂ :=
  piExpect ν (fun y ↦ f (splice I x y))

/-- Coordinate conditional expectation `E_i f = T_{i} f` (resampling coordinate `i`). -/
@[expose] noncomputable def coordCondExpect (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) : (ι → A) → ℂ :=
  subsetResampleOp ν {i} f

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma degSubspace_eq_span (d : ℕ) :
    (degSubspace d : Submodule ℂ ((ι → A) → ℂ)) = Submodule.span ℂ {f | IsDegJunta d f} :=
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma mem_degSubspace_of_isDegJunta {d : ℕ} {f : (ι → A) → ℂ} (hf : IsDegJunta d f) :
    f ∈ degSubspace d :=
  Submodule.subset_span hf

lemma subsetResampleOp_eq_piExpect (ν : PMF A) (I : Finset ι)
    (f : (ι → A) → ℂ) (x : ι → A) :
    subsetResampleOp ν I f x = piExpect ν (fun y ↦ f (splice I x y)) :=
  rfl

lemma subsetResampleOp_eq_sum (ν : PMF A) (I : Finset ι)
    (f : (ι → A) → ℂ) (x : ι → A) :
    subsetResampleOp ν I f x = ∑ y : ι → A, (piWeight ν y : ℂ) * f (splice I x y) :=
  rfl

@[simp]
lemma subsetResampleOp_zero (ν : PMF A) (I : Finset ι) :
    subsetResampleOp ν I (0 : (ι → A) → ℂ) = 0 := by
  ext x; unfold subsetResampleOp piExpect; simp

lemma coordCondExpect_eq_subsetResampleOp (ν : PMF A) (i : ι) (f : (ι → A) → ℂ) :
    coordCondExpect ν i f = subsetResampleOp ν {i} f :=
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma isJunta_mono {I J : Finset ι} (hIJ : I ⊆ J) {f : (ι → A) → ℂ} (hf : IsJunta I f) :
    IsJunta J f :=
  fun x y hxy ↦ hf x y fun i hi ↦ hxy i (hIJ hi)

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma isJunta_add {I : Finset ι} {f g : (ι → A) → ℂ} (hf : IsJunta I f) (hg : IsJunta I g) :
    IsJunta I (f + g) :=
  fun x y hxy ↦ by simp [hf x y hxy, hg x y hxy]

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma isJunta_smul {I : Finset ι} (c : ℂ) {f : (ι → A) → ℂ} (hf : IsJunta I f) :
    IsJunta I (fun x ↦ c * f x) :=
  fun x y hxy ↦ by dsimp only; rw [hf x y hxy]

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma isJunta_mul {I : Finset ι} {f g : (ι → A) → ℂ} (hf : IsJunta I f) (hg : IsJunta I g) :
    IsJunta I (fun x ↦ f x * g x) :=
  fun x y hxy ↦ by dsimp only; rw [hf x y hxy, hg x y hxy]

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma isJunta_const {I : Finset ι} (c : ℂ) : IsJunta I (fun _ : ι → A ↦ c) :=
  fun _ _ _ ↦ rfl

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
lemma isJunta_sum {κ : Type*} {I : Finset ι} (s : Finset κ) {f : κ → (ι → A) → ℂ}
    (hf : ∀ k ∈ s, IsJunta I (f k)) : IsJunta I (fun x ↦ ∑ k ∈ s, f k x) :=
  fun x y hxy ↦ Finset.sum_congr rfl fun k hk ↦ hf k hk x y hxy

omit [Fintype A] in
/-- Product weight factors cleanly across `splice I x y`. -/
lemma piWeight_splice_mul (ν : PMF A) (I : Finset ι) (x y : ι → A) :
    piWeight ν x * piWeight ν y =
      piWeight ν (splice I x y) * piWeight ν (splice I y x) := by
  unfold piWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ I <;> simp [splice, hi, mul_comm]

/-- `T_I` always outputs an `Iᶜ`-junta. -/
lemma subsetResampleOp_isJunta (ν : PMF A) (I : Finset ι) (f : (ι → A) → ℂ) :
    IsJunta Iᶜ (subsetResampleOp ν I f) := by
  intro x x' hxx'
  unfold subsetResampleOp
  congr 1; ext y
  have hs : splice I x y = splice I x' y := by
    ext i; by_cases hi : i ∈ I
    · simp [splice, hi]
    · simp [splice, hi, hxx' i (Finset.mem_compl.mpr hi)]
  rw [hs]

/-- On an `Iᶜ`-junta, `T_I` is the identity. -/
lemma subsetResampleOp_of_isJunta (ν : PMF A) {I : Finset ι} {f : (ι → A) → ℂ}
    (hf : IsJunta Iᶜ f) : subsetResampleOp ν I f = f := by
  ext x
  unfold subsetResampleOp
  have h : (fun y ↦ f (splice I x y)) = fun _ ↦ f x := by
    ext y; exact hf _ _ fun i hi ↦ by simp [splice, Finset.mem_compl.mp hi]
  rw [h, piExpect_const]

/-- `T_I` preserves `J`-juntas for any `J`. -/
lemma subsetResampleOp_preserves_isJunta (ν : PMF A) (I J : Finset ι) {f : (ι → A) → ℂ}
    (hf : IsJunta J f) : IsJunta J (subsetResampleOp ν I f) := by
  intro x x' hxx'
  unfold subsetResampleOp
  congr 1; ext y
  refine hf _ _ fun i hi ↦ ?_
  by_cases hI : i ∈ I <;> simp [splice, hI, hxx' i hi]

@[simp]
lemma subsetResampleOp_empty (ν : PMF A) (f : (ι → A) → ℂ) :
    subsetResampleOp ν ∅ f = f := by
  ext x; simp [subsetResampleOp, piExpect_const]

@[simp]
lemma subsetResampleOp_univ (ν : PMF A) (f : (ι → A) → ℂ) (x : ι → A) :
    subsetResampleOp ν Finset.univ f x = piExpect ν f := by
  simp [subsetResampleOp]

lemma subsetResampleOp_add (ν : PMF A) (I : Finset ι) (f g : (ι → A) → ℂ) :
    subsetResampleOp ν I (f + g) = subsetResampleOp ν I f + subsetResampleOp ν I g := by
  ext x; exact piExpect_add ν _ _

lemma subsetResampleOp_sub (ν : PMF A) (I : Finset ι) (f g : (ι → A) → ℂ) :
    subsetResampleOp ν I (f - g) = subsetResampleOp ν I f - subsetResampleOp ν I g := by
  ext x; exact piExpect_sub ν _ _

lemma subsetResampleOp_smul (ν : PMF A) (I : Finset ι) (c : ℂ) (f : (ι → A) → ℂ) :
    subsetResampleOp ν I (fun x ↦ c * f x) = fun x ↦ c * subsetResampleOp ν I f x := by
  ext x; exact piExpect_smul ν c _

lemma subsetResampleOp_sum {κ : Type*} (ν : PMF A) (I : Finset ι) (s : Finset κ)
    (f : κ → (ι → A) → ℂ) :
    subsetResampleOp ν I (fun x ↦ ∑ k ∈ s, f k x) =
      fun x ↦ ∑ k ∈ s, subsetResampleOp ν I (f k) x := by
  ext x; exact piExpect_sum ν s (fun k y ↦ f k (splice I x y))

lemma subsetResampleOp_const (ν : PMF A) (I : Finset ι) (c : ℂ) :
    subsetResampleOp ν I (fun _ ↦ c) = fun _ ↦ c := by
  ext x; exact piExpect_const ν c

/-- Semigroup / composition law: `T_I (T_J f) = T_{I ∪ J} f`. -/
lemma subsetResampleOp_comp (ν : PMF A) (I J : Finset ι) (f : (ι → A) → ℂ) :
    subsetResampleOp ν I (subsetResampleOp ν J f) = subsetResampleOp ν (I ∪ J) f := by
  ext x
  unfold subsetResampleOp piExpect
  simp_rw [Finset.mul_sum]
  let φ : (ι → A) × (ι → A) → (ι → A) × (ι → A) := fun p ↦ (splice J p.2 p.1, splice J p.1 p.2)
  have hφ : ∀ p, φ (φ p) = p := fun ⟨y, z⟩ ↦ by
    ext i <;> by_cases hj : i ∈ J <;> simp [φ, splice, hj]
  have h1 : (∑ y : ι → A, ∑ z : ι → A,
      (piWeight ν y : ℂ) * ((piWeight ν z : ℂ) * f (splice J (splice I x y) z))) =
      ∑ p : (ι → A) × (ι → A),
      (piWeight ν p.1 : ℂ) * ((piWeight ν p.2 : ℂ) *
        f (splice (I ∪ J) x (splice J p.1 p.2))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    have heq : splice J (splice I x y) z = splice (I ∪ J) x (splice J y z) := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp [splice, hi, hj]
    rw [heq]
  have h2 : (∑ p : (ι → A) × (ι → A),
      (piWeight ν p.1 : ℂ) * ((piWeight ν p.2 : ℂ) * f (splice (I ∪ J) x (splice J p.1 p.2)))) =
      ∑ p : (ι → A) × (ι → A),
      (piWeight ν p.1 : ℂ) * ((piWeight ν p.2 : ℂ) * f (splice (I ∪ J) x p.2)) := by
    refine Fintype.sum_equiv (⟨φ, φ, hφ, hφ⟩ : (ι → A) × (ι → A) ≃ (ι → A) × (ι → A)) _ _
      fun p ↦ ?_
    simp only [Equiv.coe_fn_mk, φ]
    have hw : piWeight ν p.1 * piWeight ν p.2 =
        piWeight ν (splice J p.2 p.1) * piWeight ν (splice J p.1 p.2) := by
      simpa [mul_comm] using piWeight_splice_mul ν J p.2 p.1
    have hwc : (piWeight ν p.1 : ℂ) * (piWeight ν p.2 : ℂ) =
        (piWeight ν (splice J p.2 p.1) : ℂ) * (piWeight ν (splice J p.1 p.2) : ℂ) := by
      exact_mod_cast hw
    calc (piWeight ν p.1 : ℂ) * ((piWeight ν p.2 : ℂ) * f (splice (I ∪ J) x (splice J p.1 p.2)))
        = ((piWeight ν p.1 : ℂ) * (piWeight ν p.2 : ℂ)) *
            f (splice (I ∪ J) x (splice J p.1 p.2)) := by ring
      _ = ((piWeight ν (splice J p.2 p.1) : ℂ) * (piWeight ν (splice J p.1 p.2) : ℂ)) *
            f (splice (I ∪ J) x (splice J p.1 p.2)) := by rw [hwc]
      _ = (piWeight ν (splice J p.2 p.1) : ℂ) *
            ((piWeight ν (splice J p.1 p.2) : ℂ) * f (splice (I ∪ J) x (splice J p.1 p.2))) := by
          ring
  rw [h1, h2, Fintype.sum_prod_type]
  have hsum : (∑ y : ι → A, (piWeight ν y : ℂ)) = 1 := by exact_mod_cast sum_piWeight ν
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]

/-- Self-adjointness of `T_I` with respect to `piInner`. -/
lemma piInner_subsetResampleOp_left (ν : PMF A) (I : Finset ι) (f g : (ι → A) → ℂ) :
    piInner ν (subsetResampleOp ν I f) g = piInner ν f (subsetResampleOp ν I g) := by
  unfold piInner subsetResampleOp piExpect
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [Finset.mul_sum]
  let φ : (ι → A) × (ι → A) → (ι → A) × (ι → A) := fun p ↦ (splice I p.1 p.2, splice I p.2 p.1)
  have hφ : ∀ p, φ (φ p) = p := fun ⟨x, y⟩ ↦ by
    ext i <;> by_cases hi : i ∈ I <;> simp [φ, splice, hi]
  have hL := (Fintype.sum_prod_type (fun p : (ι → A) × (ι → A) ↦
    (piWeight ν p.1 : ℂ) * ((piWeight ν p.2 : ℂ) * f (splice I p.1 p.2) *
      (starRingEnd ℂ) (g p.1)))).symm
  have hR := (Fintype.sum_prod_type (fun p : (ι → A) × (ι → A) ↦
    (piWeight ν p.1 : ℂ) * (f p.1 * ((piWeight ν p.2 : ℂ) *
      (starRingEnd ℂ) (g (splice I p.1 p.2)))))).symm
  dsimp only at hL hR
  rw [hL, hR]
  refine Fintype.sum_equiv (⟨φ, φ, hφ, hφ⟩ : (ι → A) × (ι → A) ≃ (ι → A) × (ι → A)) _ _ fun p ↦ ?_
  simp only [Equiv.coe_fn_mk, φ]
  have hw : (piWeight ν p.1 : ℂ) * (piWeight ν p.2 : ℂ) =
      (piWeight ν (splice I p.1 p.2) : ℂ) * (piWeight ν (splice I p.2 p.1) : ℂ) := by
    exact_mod_cast piWeight_splice_mul ν I p.1 p.2
  have hsp : splice I (splice I p.1 p.2) (splice I p.2 p.1) = p.1 := by
    ext i; by_cases hi : i ∈ I <;> simp [splice, hi]
  rw [hsp]
  calc (piWeight ν p.1 : ℂ) * ((piWeight ν p.2 : ℂ) * f (splice I p.1 p.2) *
        (starRingEnd ℂ) (g p.1))
      = ((piWeight ν p.1 : ℂ) * (piWeight ν p.2 : ℂ)) *
          (f (splice I p.1 p.2) * (starRingEnd ℂ) (g p.1)) := by ring
    _ = ((piWeight ν (splice I p.1 p.2) : ℂ) * (piWeight ν (splice I p.2 p.1) : ℂ)) *
          (f (splice I p.1 p.2) * (starRingEnd ℂ) (g p.1)) := by rw [hw]
    _ = (piWeight ν (splice I p.1 p.2) : ℂ) * (f (splice I p.1 p.2) *
          ((piWeight ν (splice I p.2 p.1) : ℂ) * (starRingEnd ℂ) (g p.1))) := by ring

/-- `T_I` preserves expectation: `E[T_I f] = E[f]`. -/
lemma piExpect_subsetResampleOp (ν : PMF A) (I : Finset ι) (f : (ι → A) → ℂ) :
    piExpect ν (subsetResampleOp ν I f) = piExpect ν f := by
  have h := piInner_subsetResampleOp_left ν I f (fun _ ↦ 1)
  simpa [piInner, subsetResampleOp_const] using h

/-- `T_I` is an `L²` contraction: `‖T_I f‖₂² ≤ ‖f‖₂²`. -/
lemma l2NormSq_subsetResampleOp_le (ν : PMF A) (I : Finset ι) (f : (ι → A) → ℂ) :
    l2NormSq ν (subsetResampleOp ν I f) ≤ l2NormSq ν f := by
  have h1 : l2NormSq ν (subsetResampleOp ν I f) =
      piExpectReal ν (fun x ↦ ‖piExpect ν (fun y ↦ f (splice I x y))‖ ^ 2) := rfl
  have h2 : ∀ x, ‖piExpect ν (fun y ↦ f (splice I x y))‖ ^ 2 ≤
      piExpectReal ν (fun y ↦ ‖f (splice I x y)‖ ^ 2) :=
    fun x ↦ norm_piExpect_sq_le ν (fun y ↦ f (splice I x y))
  calc l2NormSq ν (subsetResampleOp ν I f)
      ≤ piExpectReal ν (fun x ↦ piExpectReal ν (fun y ↦ ‖f (splice I x y)‖ ^ 2)) :=
        piExpectReal_mono ν h2
    _ = l2NormSq ν f := by
        have hc : (piExpectReal ν (fun x ↦ piExpectReal ν (fun y ↦ ‖f (splice I x y)‖ ^ 2)) : ℂ) =
            (l2NormSq ν f : ℂ) := by
          have h := piExpect_subsetResampleOp ν I (fun x ↦ (‖f x‖ ^ 2 : ℂ))
          simpa [subsetResampleOp, piExpect, l2NormSq, piExpectReal] using h
        exact_mod_cast hc

/-- `T_I` preserves `B`-boundedness. -/
lemma subsetResampleOp_isBoundedBy (ν : PMF A) (I : Finset ι) {B : ℝ} {f : (ι → A) → ℂ}
    (hf : IsBoundedBy B f) : IsBoundedBy B (subsetResampleOp ν I f) := by
  intro x
  refine (norm_piExpect_le ν _).trans ?_
  calc piExpectReal ν (fun y ↦ ‖f (splice I x y)‖)
      ≤ piExpectReal ν (fun _ ↦ B) := piExpectReal_mono ν fun y ↦ hf _
    _ = B := piExpectReal_const ν B

/-- `T_I` pulls out `Iᶜ`-juntas: `T_I (g * f) = g * T_I f` when `g` is an `Iᶜ`-junta. -/
lemma subsetResampleOp_mul_of_isJunta (ν : PMF A) {I : Finset ι} {g f : (ι → A) → ℂ}
    (hg : IsJunta Iᶜ g) :
    subsetResampleOp ν I (fun x ↦ g x * f x) = fun x ↦ g x * subsetResampleOp ν I f x := by
  ext x
  unfold subsetResampleOp
  have heq : (fun y ↦ g (splice I x y) * f (splice I x y)) =
      fun y ↦ g x * f (splice I x y) := by
    ext y
    have : g (splice I x y) = g x := hg _ _ fun i hi ↦ by simp [splice, Finset.mem_compl.mp hi]
    rw [this]
  rw [heq, piExpect_smul]

end ResamplingAndJuntas

section FourierBasis

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A real orthonormal basis `{v_0 ≡ 1, v_1, …, v_{m-1}}` of `L²(A, ν)`. -/
structure OrthonormalFourierBasis (ν : PMF A) (m : ℕ) where
  /-- The basis functions `v_j : A → ℝ` indexed by `Fin m`. -/
  vec : Fin m → A → ℝ
  /-- `m = |A|` (for a full-support probability space). -/
  card_eq : m = Fintype.card A
  /-- `v_0 ≡ 1` when `m > 0`. -/
  vec_zero : ∀ h : 0 < m, ∀ a : A, vec ⟨0, h⟩ a = 1
  /-- Orthonormality: `∑_a ν(a) v_j(a) v_k(a) = δ_{j,k}`. -/
  orthonormal : ∀ j k : Fin m,
    ∑ a : A, (ν a).toReal * vec j a * vec k a = if j = k then 1 else 0

/-- Tensor product Fourier basis function `v_α(x) = ∏_i v_{α i}(x i)`. -/
@[expose] def OrthonormalFourierBasis.tensorVec {ι : Type*} [Fintype ι] {ν : PMF A} {m : ℕ}
    (B : OrthonormalFourierBasis ν m) (α : ι → Fin m) (x : ι → A) : ℝ :=
  ∏ i : ι, B.vec (α i) (x i)

omit [DecidableEq A] in
lemma OrthonormalFourierBasis.tensorVec_eq_prod {ι : Type*} [Fintype ι] {ν : PMF A} {m : ℕ}
    (B : OrthonormalFourierBasis ν m) (α : ι → Fin m) (x : ι → A) :
    B.tensorVec α x = ∏ i : ι, B.vec (α i) (x i) :=
  rfl

omit [DecidableEq A] in
/-- The tensor product Fourier basis is orthonormal in `L²(ι → A, ν^⊗ι)`. -/
theorem OrthonormalFourierBasis.tensorVec_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : PMF A} {m : ℕ} (B : OrthonormalFourierBasis ν m) (α β : ι → Fin m) :
    piExpectReal ν (fun x ↦ B.tensorVec α x * B.tensorVec β x) = if α = β then 1 else 0 := by
  unfold piExpectReal piWeight OrthonormalFourierBasis.tensorVec
  have hprod : ∑ x : ι → A, (∏ i : ι, (ν (x i)).toReal) *
      ((∏ i : ι, B.vec (α i) (x i)) * (∏ i : ι, B.vec (β i) (x i))) =
      ∏ i : ι, ∑ a : A, (ν a).toReal * B.vec (α i) a * B.vec (β i) a := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_; ring
  rw [hprod]
  simp_rw [B.orthonormal]
  by_cases h : α = β
  · subst h; simp
  · simp only [h, ↓reduceIte]
    have hex : ∃ i, α i ≠ β i := by
      by_contra hall; push Not at hall; exact h (funext hall)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

omit [DecidableEq A] in
/-- Every full-support finite probability space `(A, ν)` admits a real orthonormal Fourier basis
with `v_0 ≡ 1`. -/
theorem exists_orthonormalFourierBasis (ν : PMF A) (hν : ∀ a : A, 0 < ν a) :
    Nonempty (OrthonormalFourierBasis ν (Fintype.card A)) := by
  classical
  have hne : Nonempty A := by
    by_contra hempty
    let : IsEmpty A := not_nonempty_iff.mp hempty
    have h0 := sum_pmf_toReal ν
    simp at h0
  let m := Fintype.card A
  have hm : 0 < m := Fintype.card_pos
  -- Work in `EuclideanSpace ℝ A` via the weighting `w(a) = √(ν a).toReal > 0`.
  let w : A → ℝ := fun a ↦ Real.sqrt (ν a).toReal
  have hw_pos : ∀ a, 0 < w a := fun a ↦
    Real.sqrt_pos.mpr (ENNReal.toReal_pos (ne_of_gt (hν a)) (ν.apply_ne_top a))
  let u0 : EuclideanSpace ℝ A := WithLp.toLp 2 w
  have hu0_norm : ‖u0‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ a : A, ‖u0 a‖ ^ 2 = 1 := by
      have : ∀ a, ‖u0 a‖ ^ 2 = (ν a).toReal := fun a ↦ by
        simp only [u0, Real.norm_eq_abs, sq_abs]
        exact Real.sq_sqrt ENNReal.toReal_nonneg
      simp_rw [this]
      exact sum_pmf_toReal ν
    rw [hsum, Real.sqrt_one]
  -- Pick an orthonormal basis of `(ℝ ∙ u0)ᗮ`, whose finrank is `m - 1`.
  let K : Submodule ℝ (EuclideanSpace ℝ A) := Submodule.span ℝ {u0}
  have hfinK : Module.finrank ℝ K = 1 :=
    finrank_span_singleton (by intro h0; rw [h0, norm_zero] at hu0_norm; norm_num at hu0_norm)
  have hfin_orth : Module.finrank ℝ (Kᗮ : Submodule ℝ (EuclideanSpace ℝ A)) = m - 1 := by
    have htot := Submodule.finrank_add_finrank_orthogonal K
    rw [hfinK, finrank_euclideanSpace] at htot
    omega
  let bOrth : OrthonormalBasis (Fin (m - 1)) ℝ (Kᗮ : Submodule ℝ (EuclideanSpace ℝ A)) :=
    (stdOrthonormalBasis ℝ (Kᗮ : Submodule ℝ (EuclideanSpace ℝ A))).reindex
      (Fintype.equivFinOfCardEq (by simp [hfin_orth]))
  -- Assemble the `Fin m` orthonormal vectors `u j` in `EuclideanSpace ℝ A`: `u 0 = u0`,
  -- `u (k + 1) = (bOrth k : EuclideanSpace ℝ A)`.
  let u : Fin m → EuclideanSpace ℝ A := fun j ↦
    if h0 : j.val = 0 then u0
    else (bOrth ⟨j.val - 1, by omega⟩ : EuclideanSpace ℝ A)
  have hu_ortho : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro j k
    by_cases hj : j.val = 0 <;> by_cases hk : k.val = 0
    · have hjk : j = k := Fin.ext (hj.trans hk.symm)
      subst hjk
      simp only [u, hj, ↓reduceDIte, real_inner_self_eq_norm_sq, hu0_norm, one_pow, ↓reduceIte]
    · have hjk : j ≠ k := fun h ↦ hk (h ▸ hj)
      simp only [u, hj, hk, ↓reduceDIte, hjk, ↓reduceIte]
      have hmem : (bOrth ⟨k.val - 1, by omega⟩ : EuclideanSpace ℝ A) ∈ Kᗮ := (bOrth _).2
      exact (Submodule.mem_orthogonal K _).mp hmem u0 (Submodule.mem_span_singleton_self u0)
    · have hjk : j ≠ k := fun h ↦ hj (h.symm ▸ hk)
      simp only [u, hj, hk, ↓reduceDIte, hjk, ↓reduceIte]
      have hmem : (bOrth ⟨j.val - 1, by omega⟩ : EuclideanSpace ℝ A) ∈ Kᗮ := (bOrth _).2
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal K _).mp hmem u0 (Submodule.mem_span_singleton_self u0)
    · simp only [u, hj, hk, ↓reduceDIte]
      have hsub := bOrth.orthonormal
      rw [orthonormal_iff_ite] at hsub
      have hidx : (⟨j.val - 1, by omega⟩ : Fin (m - 1)) = ⟨k.val - 1, by omega⟩ ↔ j = k := by
        constructor
        · intro heq
          have hv := congr_arg Fin.val heq
          dsimp at hv
          exact Fin.ext (by omega)
        · intro heq; subst heq; rfl
      have hinner := hsub ⟨j.val - 1, by omega⟩ ⟨k.val - 1, by omega⟩
      simpa [Submodule.coe_inner, hidx] using hinner
  refine ⟨⟨fun j a ↦ (u j a) / w a, rfl, ?_, ?_⟩⟩
  · intro h a
    simp only [u, ↓reduceDIte, u0, WithLp.ofLp_toLp]
    exact div_self (ne_of_gt (hw_pos a))
  · intro j k
    have hinner := (orthonormal_iff_ite.mp hu_ortho) j k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simp only [star_trivial, dotProduct] at hinner
    rw [← hinner]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hwa : w a ≠ 0 := ne_of_gt (hw_pos a)
    have hsq : w a * w a = (ν a).toReal := Real.mul_self_sqrt ENNReal.toReal_nonneg
    calc (ν a).toReal * (u j a / w a) * (u k a / w a)
        = (w a * w a) * (u j a / w a) * (u k a / w a) := by rw [hsq]
      _ = u k a * u j a := by field_simp [hwa]
      _ = u k a * u j a := rfl

/-- Fourier expansion of any function `f : (ι → A) → ℂ` in a tensor orthonormal basis. -/
@[expose] noncomputable def OrthonormalFourierBasis.fourierCoeff {ι : Type*} [Fintype ι]
    [DecidableEq ι] {ν : PMF A} {m : ℕ} (B : OrthonormalFourierBasis ν m) (f : (ι → A) → ℂ)
    (α : ι → Fin m) : ℂ :=
  piInner ν f (fun x ↦ (B.tensorVec α x : ℂ))

omit [DecidableEq A] in
lemma OrthonormalFourierBasis.fourierCoeff_eq_piInner {ι : Type*} [Fintype ι]
    [DecidableEq ι] {ν : PMF A} {m : ℕ} (B : OrthonormalFourierBasis ν m) (f : (ι → A) → ℂ)
    (α : ι → Fin m) :
    B.fourierCoeff f α = piInner ν f (fun x ↦ (B.tensorVec α x : ℂ)) :=
  rfl

omit [DecidableEq A] in
/-- Full-support Fourier basis expansion identity `f(x) = ∑_α f̂(α) v_α(x)`. -/
theorem OrthonormalFourierBasis.fourier_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : PMF A} (hν : ∀ a : A, 0 < ν a) {m : ℕ} (B : OrthonormalFourierBasis ν m)
    (f : (ι → A) → ℂ) (x : ι → A) :
    ∑ α : ι → Fin m, B.fourierCoeff f α * (B.tensorVec α x : ℂ) = f x := by
  classical
  -- Orthogonality of `g = f - ∑_α f̂(α) v_α` to every `v_β`, and `{v_α}` spans `L²` by dimension!
  let g : (ι → A) → ℂ := fun y ↦ f y - ∑ α : ι → Fin m, B.fourierCoeff f α * (B.tensorVec α y : ℂ)
  have hinner_zero : ∀ β : ι → Fin m, piInner ν g (fun y ↦ (B.tensorVec β y : ℂ)) = 0 := by
    intro β
    change piInner ν (f - fun y ↦ ∑ α : ι → Fin m, B.fourierCoeff f α * (B.tensorVec α y : ℂ))
      (fun y ↦ (B.tensorVec β y : ℂ)) = 0
    rw [piInner_sub_left, piInner_sum_left, Finset.sum_eq_single β]
    · rw [piInner_smul_left]
      have h1 : piInner ν (fun y ↦ (B.tensorVec β y : ℂ)) (fun y ↦ (B.tensorVec β y : ℂ)) = 1 := by
        have horth := B.tensorVec_orthonormal β β
        simp only [↓reduceIte] at horth
        unfold piInner piExpect
        have : (∑ y : ι → A, (piWeight ν y : ℂ) * ((B.tensorVec β y : ℂ) *
            (starRingEnd ℂ) (B.tensorVec β y : ℂ))) =
            ((piExpectReal ν fun y ↦ B.tensorVec β y * B.tensorVec β y : ℝ) : ℂ) := by
          unfold piExpectReal; rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_; simp [Complex.conj_ofReal]
        rw [this, horth, Complex.ofReal_one]
      rw [h1, mul_one]; exact sub_self _
    · intro α _ hαβ
      rw [piInner_smul_left]
      have h0 : piInner ν (fun y ↦ (B.tensorVec α y : ℂ)) (fun y ↦ (B.tensorVec β y : ℂ)) = 0 := by
        have horth := B.tensorVec_orthonormal α β
        simp only [hαβ, ↓reduceIte] at horth
        unfold piInner piExpect
        have : (∑ y : ι → A, (piWeight ν y : ℂ) * ((B.tensorVec α y : ℂ) *
            (starRingEnd ℂ) (B.tensorVec β y : ℂ))) =
            ((piExpectReal ν fun y ↦ B.tensorVec α y * B.tensorVec β y : ℝ) : ℂ) := by
          unfold piExpectReal; rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_; simp [Complex.conj_ofReal]
        rw [this, horth, Complex.ofReal_zero]
      rw [h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ β) h
  -- The `m^|ι|` functions `v_α` are linearly independent in the `|A|^|ι|`-dimensional space
  -- `(ι → A) → ℂ`, hence they span it.
  have hli : LinearIndependent ℂ (fun α : ι → Fin m ↦ (fun y : ι → A ↦ (B.tensorVec α y : ℂ))) := by
    rw [linearIndependent_iff']
    intro s c hc α hα
    have h0 := congr_arg (fun h ↦ piInner ν h (fun y ↦ (B.tensorVec α y : ℂ))) hc
    rw [piInner_zero_left] at h0
    have hsum : (∑ β ∈ s, c β • (fun y : ι → A ↦ (B.tensorVec β y : ℂ))) =
        fun y ↦ ∑ β ∈ s, c β * (B.tensorVec β y : ℂ) := by
      ext y; simp [Finset.sum_apply]
    rw [hsum, piInner_sum_left, Finset.sum_eq_single α] at h0
    · rw [piInner_smul_left] at h0
      have h1 : piInner ν (fun y ↦ (B.tensorVec α y : ℂ)) (fun y ↦ (B.tensorVec α y : ℂ)) = 1 := by
        have horth := B.tensorVec_orthonormal α α
        simp only [↓reduceIte] at horth
        unfold piInner piExpect
        have : (∑ y : ι → A, (piWeight ν y : ℂ) * ((B.tensorVec α y : ℂ) *
            (starRingEnd ℂ) (B.tensorVec α y : ℂ))) =
            ((piExpectReal ν fun y ↦ B.tensorVec α y * B.tensorVec α y : ℝ) : ℂ) := by
          unfold piExpectReal; rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_; simp [Complex.conj_ofReal]
        rw [this, horth, Complex.ofReal_one]
      simpa [h1] using h0
    · intro β _ hβα
      rw [piInner_smul_left]
      have h0' : piInner ν (fun y ↦ (B.tensorVec β y : ℂ)) (fun y ↦ (B.tensorVec α y : ℂ)) = 0 := by
        have horth := B.tensorVec_orthonormal β α
        simp only [hβα, ↓reduceIte] at horth
        unfold piInner piExpect
        have : (∑ y : ι → A, (piWeight ν y : ℂ) * ((B.tensorVec β y : ℂ) *
            (starRingEnd ℂ) (B.tensorVec α y : ℂ))) =
            ((piExpectReal ν fun y ↦ B.tensorVec β y * B.tensorVec α y : ℝ) : ℂ) := by
          unfold piExpectReal; rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_; simp [Complex.conj_ofReal]
        rw [this, horth, Complex.ofReal_zero]
      rw [h0', mul_zero]
    · intro h; exact absurd hα h
  have hspan : Submodule.span ℂ (Set.range fun α : ι → Fin m ↦
      (fun y : ι → A ↦ (B.tensorVec α y : ℂ))) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, Module.finrank_pi, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin, B.card_eq]
  have hgmem : g ∈ Submodule.span ℂ (Set.range fun α : ι → Fin m ↦
      (fun y : ι → A ↦ (B.tensorVec α y : ℂ))) := by
    rw [hspan]; trivial
  have hg_orth : piInner ν g g = 0 := by
    refine Submodule.span_induction (p := fun u _ ↦ piInner ν g u = 0) ?_ ?_ ?_ ?_ hgmem
    · rintro _ ⟨β, rfl⟩; exact hinner_zero β
    · exact piInner_zero_right ν g
    · intro u v _ _ ihu ihv; rw [piInner_add_right, ihu, ihv, add_zero]
    · intro c u _ ihu
      change piInner ν g (fun y ↦ c * u y) = 0
      rw [piInner_smul_right, ihu, mul_zero]
  rw [piInner_self] at hg_orth
  have hsq0 : l2NormSq ν g = 0 := by exact_mod_cast hg_orth
  have hg0 : g = 0 := (l2NormSq_eq_zero_iff ν hν g).mp hsq0
  have hgx := congr_fun hg0 x
  exact (sub_eq_zero.mp hgx).symm

end FourierBasis

end CslibFrontier.Analysis.Fourier

