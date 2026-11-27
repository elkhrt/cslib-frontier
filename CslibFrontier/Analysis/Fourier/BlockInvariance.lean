/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import CslibFrontier.Analysis.Fourier.EfronStein
public import CslibFrontier.Analysis.Fourier.FiniteProduct
public import CslibFrontier.Analysis.Fourier.Hypercontractivity

import CslibFrontier.Foundations.Analysis.Calculus.Taylor
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multivariate Block-Multilinear Invariance Principle

This module proves the Mossel–O'Donnell–Oleszkiewicz / Mossel invariance principle for correlated
finite-alphabet block ensembles and their covariance-matched Gaussian ensembles under standard Lean
axioms, together with truncation/Lipschitz estimates used in CSP dictatorship tests and mixed
invariance principles.

## Main definitions

* `CslibFrontier.Analysis.Fourier.BlockPoly`: vector-valued block-multilinear polynomials
  $M : (\mathrm{Fin}\,n \to \mathrm{Fin}\,q \to \mathbb{R}) \to (\mathrm{Fin}\,k \to \mathbb{R})$
  with degree `BlockPoly.HasDeg`, coordinate influence `BlockPoly.coordInfAt`, and coefficient
  $\ell^2$-norm `BlockPoly.coeffL2Sq`.
* `CslibFrontier.Analysis.Fourier.BlockEnsemble`: a centered finite-alphabet random vector
  $X : \Omega \to (\mathrm{Fin}\,q \to \mathbb{R})$ under $\mu$ with atom lower bound $\alpha > 0$,
  together with its covariance-matched centered Gaussian block `gaussBlock`.

## Main results

* `CslibFrontier.Analysis.Fourier.gaussBlock_cov`: covariance matching of the Gaussian block
  ensemble.
* `CslibFrontier.Analysis.Fourier.hybrid_poly_l2_eq`: exact $L^2$ invariance across hybrid
  discrete and
  Gaussian block ensembles.
* `CslibFrontier.Analysis.Fourier.hybrid_hypercontractivity_2_4`: $(2,4)$-hypercontractivity for
  degree-$\leq d$ block-multilinear polynomials over independent hybrid (discrete and Gaussian)
  blocks.
* `CslibFrontier.Analysis.Fourier.taylor_third_order_multivariate`: multivariate third-order Taylor
  remainder bound for $C^3$ test functions.
-/

public section

open Finset BigOperators MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Convolution

namespace CslibFrontier.Analysis.Fourier

section BlockPolynomials

/-- A vector-valued block-multilinear polynomial `M : (Fin n → Fin q → ℝ) → (Fin k → ℝ)`
represented by its real coefficients `M s α` indexed by `α : Fin n → Option (Fin q)`. -/
abbrev BlockPoly (n q k : ℕ) : Type := Fin k → (Fin n → Option (Fin q)) → ℝ

/-- Support of a block multi-index `α : Fin n → Option (Fin q)`. -/
@[expose] def blockSupp {n q : ℕ} (α : Fin n → Option (Fin q)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (α i).isSome

lemma blockSupp_eq_filter {n q : ℕ} (α : Fin n → Option (Fin q)) :
    blockSupp α = Finset.univ.filter (fun i ↦ (α i).isSome) := rfl

/-- Evaluation of a block-multilinear polynomial `M` at `x : Fin n → Fin q → ℝ`. -/
@[expose] def BlockPoly.eval {n q k : ℕ} (M : BlockPoly n q k) (x : Fin n → Fin q → ℝ)
    (s : Fin k) : ℝ :=
  ∑ α, M s α * ∏ i : Fin n, match α i with | none => 1 | some j => x i j

lemma BlockPoly.eval_eq_sum {n q k : ℕ} (M : BlockPoly n q k) (x : Fin n → Fin q → ℝ)
    (s : Fin k) :
    M.eval x s = ∑ α, M s α * ∏ i : Fin n, match α i with | none => 1 | some j => x i j := rfl

/-- `M` has degree at most `d` if every nonzero coefficient has support of size at most `d`. -/
@[expose] def BlockPoly.HasDeg {n q k : ℕ} (M : BlockPoly n q k) (d : ℕ) : Prop :=
  ∀ s α, d < (blockSupp α).card → M s α = 0

/-- Influence of variable `(i, j)` on the `s`-th coordinate of `M`:
`I_{i,j}[M_s] = ∑_{α : α i = some j} (M s α)²`. -/
@[expose] def BlockPoly.coordInfAt {n q k : ℕ} (M : BlockPoly n q k) (s : Fin k)
    (i : Fin n) (j : Fin q) : ℝ :=
  ∑ α ∈ Finset.univ.filter (fun α : Fin n → Option (Fin q) ↦ α i = some j), (M s α) ^ 2

lemma BlockPoly.coordInfAt_eq_sum {n q k : ℕ} (M : BlockPoly n q k) (s : Fin k)
    (i : Fin n) (j : Fin q) : M.coordInfAt s i j =
      ∑ α ∈ Finset.univ.filter (fun α : Fin n → Option (Fin q) ↦ α i = some j), (M s α) ^ 2 := rfl

/-- Sum of squared coefficients of the `s`-th coordinate of `M`. -/
@[expose] def BlockPoly.coeffL2Sq {n q k : ℕ} (M : BlockPoly n q k) (s : Fin k) : ℝ :=
  ∑ α : Fin n → Option (Fin q), (M s α) ^ 2

lemma BlockPoly.coeffL2Sq_eq_sum {n q k : ℕ} (M : BlockPoly n q k) (s : Fin k) :
    M.coeffL2Sq s = ∑ α : Fin n → Option (Fin q), (M s α) ^ 2 := rfl

lemma BlockPoly.coordInfAt_nonneg {n q k : ℕ} (M : BlockPoly n q k) (s : Fin k)
    (i : Fin n) (j : Fin q) : 0 ≤ M.coordInfAt s i j := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma BlockPoly.sum_coordInfAt_le {n q k d : ℕ} (M : BlockPoly n q k) (hdeg : M.HasDeg d)
    (s : Fin k) :
    ∑ i : Fin n, ∑ j : Fin q, M.coordInfAt s i j ≤ (d : ℝ) * M.coeffL2Sq s := by
  simp only [BlockPoly.coordInfAt, BlockPoly.coeffL2Sq]
  have h1 : ∀ α : Fin n → Option (Fin q),
      ∑ i : Fin n, ∑ j : Fin q, (if α i = some j then (M s α) ^ 2 else 0) =
        ((blockSupp α).card : ℝ) * (M s α) ^ 2 := fun α ↦ by
    trans ∑ i : Fin n, if (α i).isSome then (M s α) ^ 2 else 0
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      cases α i with
      | none => simp
      | some j₀ =>
        simp only [Option.isSome_some, ite_true]; rw [Finset.sum_eq_single j₀]
        · simp
        · intro j _ hj; simp [hj.symm]
        · intro h; exact (h (Finset.mem_univ j₀)).elim
    · simp [blockSupp, Finset.sum_ite]
  simp_rw [Finset.sum_filter]
  calc ∑ i : Fin n, ∑ j : Fin q, ∑ α : Fin n → Option (Fin q),
          (if α i = some j then (M s α) ^ 2 else 0)
      = ∑ i : Fin n, ∑ α, ∑ j : Fin q, (if α i = some j then (M s α) ^ 2 else 0) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ α, ∑ i : Fin n, ∑ j : Fin q, (if α i = some j then (M s α) ^ 2 else 0) := Finset.sum_comm
    _ = ∑ α, ((blockSupp α).card : ℝ) * (M s α) ^ 2 := Finset.sum_congr rfl fun α _ ↦ h1 α
    _ ≤ ∑ α, (d : ℝ) * (M s α) ^ 2 := Finset.sum_le_sum fun α _ ↦ by
        by_cases h : d < (blockSupp α).card
        · simp [hdeg s α h]
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast not_lt.mp h) (sq_nonneg _)
    _ = (d : ℝ) * ∑ α, (M s α) ^ 2 := by rw [← Finset.mul_sum]

/-- A centered finite-alphabet block ensemble `(Ω, μ, X)` of dimension `q` with atom lower bound
`α > 0` and coordinate variances at most `1`. -/
structure BlockEnsemble (Ω : Type*) [Fintype Ω] (q : ℕ) where
  /-- Underlying probability mass function on the finite block space `Ω`. -/
  μ : PMF Ω
  /-- Centered random vector `X : Ω → Fin q → ℝ`. -/
  X : Ω → Fin q → ℝ
  /-- Each coordinate has mean zero. -/
  centered : ∀ j : Fin q, ∑ ω : Ω, (μ ω).toReal * X ω j = 0
  /-- Each coordinate has variance at most `1`. -/
  var_le_one : ∀ j : Fin q, ∑ ω : Ω, (μ ω).toReal * (X ω j) ^ 2 ≤ 1
  /-- Atom probability lower bound `α > 0`. -/
  α : ℝ
  /-- Positivity of `α`. -/
  α_pos : 0 < α
  /-- Every atom in `μ.support` has mass at least `α`. -/
  atom_lb : ∀ ω ∈ μ.support, α ≤ (μ ω).toReal

/-- Product standard Gaussian measure on `Ω → ℝ`. -/
@[expose] noncomputable def stdGaussPi (Ω : Type*) [Fintype Ω] : Measure (Ω → ℝ) :=
  Measure.pi fun _ : Ω ↦ gaussianReal 0 1

lemma stdGaussPi_eq_pi (Ω : Type*) [Fintype Ω] :
    stdGaussPi Ω = Measure.pi (fun _ : Ω ↦ gaussianReal 0 1) := rfl

instance stdGaussPi_isProbabilityMeasure (Ω : Type*) [Fintype Ω] :
    IsProbabilityMeasure (stdGaussPi Ω) := by unfold stdGaussPi; infer_instance

/-- Covariance-matched centered Gaussian block `G_j(g) = ∑ ω, √(μ ω) * X ω j * g ω` for
`g ∼ stdGaussPi Ω`. -/
@[expose] noncomputable def gaussBlock {Ω : Type*} [Fintype Ω] {q : ℕ} (E : BlockEnsemble Ω q)
    (g : Ω → ℝ) (j : Fin q) : ℝ :=
  ∑ ω : Ω, Real.sqrt (E.μ ω).toReal * E.X ω j * g ω

lemma gaussBlock_eq_sum {Ω : Type*} [Fintype Ω] {q : ℕ} (E : BlockEnsemble Ω q)
    (g : Ω → ℝ) (j : Fin q) :
    gaussBlock E g j = ∑ ω : Ω, Real.sqrt (E.μ ω).toReal * E.X ω j * g ω := rfl

lemma gaussBlock_eq_dotProduct {Ω : Type*} [Fintype Ω] {q : ℕ} (E : BlockEnsemble Ω q)
    (g : Ω → ℝ) (j : Fin q) :
    gaussBlock E g j = (fun ω ↦ Real.sqrt (E.μ ω).toReal * E.X ω j) ⬝ᵥ g := rfl

lemma gaussBlock_memLp {Ω : Type*} [Fintype Ω] {q : ℕ} (E : BlockEnsemble Ω q)
    (j : Fin q) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun g ↦ gaussBlock E g j) p (stdGaussPi Ω) :=
  memLp_dotProduct_pi_gaussianReal (fun ω ↦ Real.sqrt (E.μ ω).toReal * E.X ω j) hp

lemma gaussBlock_mean_zero {Ω : Type*} [Fintype Ω] {q : ℕ} (E : BlockEnsemble Ω q)
    (j : Fin q) : ∫ g, gaussBlock E g j ∂stdGaussPi Ω = 0 := by
  let a : Ω → ℝ := fun ω ↦ Real.sqrt (E.μ ω).toReal * E.X ω j
  have hmap := pi_gaussianReal_map_dotProduct a
  have hid : ∫ x : ℝ, x ∂((stdGaussPi Ω).map (a ⬝ᵥ ·)) =
      ∫ g, a ⬝ᵥ g ∂stdGaussPi Ω :=
    integral_map (by fun_prop) aestronglyMeasurable_id
  change ∫ g, a ⬝ᵥ g ∂stdGaussPi Ω = 0
  unfold stdGaussPi at hid ⊢
  rw [← hid, hmap, integral_id_gaussianReal]

lemma gaussBlock_cov {Ω : Type*} [Fintype Ω] {q : ℕ} (E : BlockEnsemble Ω q) (j l : Fin q) :
    ∫ g, gaussBlock E g j * gaussBlock E g l ∂stdGaussPi Ω =
      ∑ ω : Ω, (E.μ ω).toReal * E.X ω j * E.X ω l := by
  let aj : Ω → ℝ := fun ω ↦ Real.sqrt (E.μ ω).toReal * E.X ω j
  let al : Ω → ℝ := fun ω ↦ Real.sqrt (E.μ ω).toReal * E.X ω l
  have hsq : ∀ b : Ω → ℝ, ∫ g, (b ⬝ᵥ g) ^ 2 ∂stdGaussPi Ω = b ⬝ᵥ b := by
    intro b
    have hmap := pi_gaussianReal_map_dotProduct b
    have hid : ∫ x : ℝ, x ^ 2 ∂((stdGaussPi Ω).map (b ⬝ᵥ ·)) =
        ∫ g, (b ⬝ᵥ g) ^ 2 ∂stdGaussPi Ω :=
      integral_map (by fun_prop) (by fun_prop)
    unfold stdGaussPi at hid ⊢
    rw [← hid, hmap]
    have hv := variance_id_gaussianReal (μ := 0) (v := ‖WithLp.toLp 2 b‖₊ ^ 2)
    rw [variance_eq_integral (by fun_prop)] at hv
    simp only [id, integral_id_gaussianReal, sub_zero] at hv
    have hnorm : ((‖WithLp.toLp 2 b‖₊ ^ 2 : ℝ≥0) : ℝ) = b ⬝ᵥ b := by
      have hnn : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun ω _ ↦ mul_self_nonneg (b ω)
      rw [NNReal.coe_pow, coe_nnNorm, ← sqrt_dotProduct_self_eq_norm, Real.sq_sqrt hnn]
    rw [← hnorm, ← hv]
  have hpol : ∀ g : Ω → ℝ, (aj ⬝ᵥ g) * (al ⬝ᵥ g) =
      (1 / 4 : ℝ) * (((aj + al) ⬝ᵥ g) ^ 2 - ((aj - al) ⬝ᵥ g) ^ 2) := by
    intro g
    simp only [add_dotProduct, sub_dotProduct]; ring
  have hint1 : Integrable (fun g ↦ ((aj + al) ⬝ᵥ g) ^ 2) (stdGaussPi Ω) :=
    (memLp_dotProduct_pi_gaussianReal (aj + al) (by simp)).integrable_sq
  have hint2 : Integrable (fun g ↦ ((aj - al) ⬝ᵥ g) ^ 2) (stdGaussPi Ω) :=
    (memLp_dotProduct_pi_gaussianReal (aj - al) (by simp)).integrable_sq
  calc ∫ g, gaussBlock E g j * gaussBlock E g l ∂stdGaussPi Ω
      = (1 / 4 : ℝ) * (∫ g, ((aj + al) ⬝ᵥ g) ^ 2 ∂stdGaussPi Ω -
          ∫ g, ((aj - al) ⬝ᵥ g) ^ 2 ∂stdGaussPi Ω) := by
        rw [← integral_sub hint1 hint2, ← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ hpol)
    _ = aj ⬝ᵥ al := by
        rw [hsq (aj + al), hsq (aj - al)]
        simp only [dotProduct, Pi.add_apply, Pi.sub_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = ∑ ω : Ω, (E.μ ω).toReal * E.X ω j * E.X ω l := by
        simp only [dotProduct, aj, al]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        calc Real.sqrt (E.μ ω).toReal * E.X ω j * (Real.sqrt (E.μ ω).toReal * E.X ω l)
            = (Real.sqrt (E.μ ω).toReal * Real.sqrt (E.μ ω).toReal) * E.X ω j * E.X ω l := by ring
          _ = (E.μ ω).toReal * E.X ω j * E.X ω l := by
              rw [Real.mul_self_sqrt ENNReal.toReal_nonneg]

/-- Single-block Gaussian `(2, 4, ρ)`-hypercontractivity for `ρ² ≤ 1 / 3`. -/
lemma gaussBlock_hypercontractivity_2_4 {Ω : Type*} [Fintype Ω] {q : ℕ}
    (E : BlockEnsemble Ω q) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1 / 3) (a0 : ℝ) (a : Fin q → ℝ) :
    ∫ g, (a0 + ρ * ∑ j : Fin q, a j * gaussBlock E g j) ^ 4 ∂stdGaussPi Ω ≤
      (∫ g, (a0 + ∑ j : Fin q, a j * gaussBlock E g j) ^ 2 ∂stdGaussPi Ω) ^ 2 := by
  let b : Ω → ℝ := fun ω ↦ ∑ j : Fin q, a j * (Real.sqrt (E.μ ω).toReal * E.X ω j)
  have hlin : ∀ g, ∑ j : Fin q, a j * gaussBlock E g j = b ⬝ᵥ g := by
    intro g
    simp only [gaussBlock, b, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  simp_rw [hlin]
  let σsq : ℝ := b ⬝ᵥ b
  have hσ_nonneg : 0 ≤ σsq := Finset.sum_nonneg fun ω _ ↦ mul_self_nonneg (b ω)
  have hmap := pi_gaussianReal_map_dotProduct b
  have hnorm : (‖WithLp.toLp 2 b‖₊ ^ 2 : ℝ) = σsq := by
    push_cast
    rw [← sqrt_dotProduct_self_eq_norm, Real.sq_sqrt hσ_nonneg]
  -- Pull back moments of `b ⬝ᵥ g` to 1D `gaussianReal 0 σsq`, then to `gaussianReal 0 1`.
  have hmom : ∀ m : ℕ, ∫ g, (b ⬝ᵥ g) ^ m ∂stdGaussPi Ω =
      (Real.sqrt σsq) ^ m * ∫ x : ℝ, x ^ m ∂gaussianReal 0 1 := by
    intro m
    have hmap' := pi_gaussianReal_map_dotProduct_eq_map_const_mul b
    have h1 : ∫ x : ℝ, x ^ m ∂((stdGaussPi Ω).map (b ⬝ᵥ ·)) =
        ∫ g, (b ⬝ᵥ g) ^ m ∂stdGaussPi Ω :=
      integral_map (by fun_prop) (by fun_prop)
    have h2 : ∫ x : ℝ, x ^ m ∂((gaussianReal 0 1).map (Real.sqrt σsq * ·)) =
        ∫ x : ℝ, (Real.sqrt σsq * x) ^ m ∂gaussianReal 0 1 :=
      integral_map (by fun_prop) (by fun_prop)
    unfold stdGaussPi at h1 ⊢
    rw [← h1, hmap', h2]
    simp_rw [mul_pow]
    rw [integral_const_mul]
  have hm1 : ∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1 = 0 := by
    simp_rw [pow_one]; exact integral_id_gaussianReal (μ := 0) (v := 1)
  have hm2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at hv
    simpa [integral_id_gaussianReal] using hv
  have hm3 : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0 := by
    have h1 : ∫ x : ℝ, x ^ 3 ∂((gaussianReal 0 1).map (fun x : ℝ ↦ -x)) =
        ∫ x : ℝ, (-x) ^ 3 ∂gaussianReal 0 1 := integral_map (by fun_prop) (by fun_prop)
    rw [(by simpa using gaussianReal_map_const_mul (μ := 0) (v := 1) (-1) :
      (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1)] at h1
    have h2 : ∫ x : ℝ, (-x) ^ 3 ∂gaussianReal 0 1 = -∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 := by
      simp_rw [show ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) from fun _ ↦ by ring]; exact integral_neg _
    linarith
  have hm4 : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
    have hmgf : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 =
        iteratedDeriv 4 (mgf (fun x ↦ x) (gaussianReal 0 1)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    rw [hmgf, mgf_fun_id_gaussianReal]
    have hd1 : deriv (fun t : ℝ ↦ Real.exp (0 * t + (1 : ℝ≥0) * t ^ 2 / 2)) =
        fun t ↦ t * Real.exp (t ^ 2 / 2) := by
      ext t; rw [show (fun t : ℝ ↦ Real.exp (0 * t + (1 : ℝ≥0) * t ^ 2 / 2)) =
        fun t ↦ Real.exp (t ^ 2 / 2) by ext s; simp, _root_.deriv_exp (by fun_prop),
        deriv_div_const, deriv_fun_pow (by fun_prop)]; simp; ring
    have hd2 : deriv (fun t : ℝ ↦ t * Real.exp (t ^ 2 / 2)) =
        fun t ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
      ext t; rw [deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop),
        deriv_div_const, deriv_fun_pow (by fun_prop)]; simp; ring
    have hd3 : deriv (fun t : ℝ ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
        fun t ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
      ext t
      rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
        _root_.deriv_exp (by fun_prop), deriv_div_const, deriv_fun_pow (by fun_prop)]; simp; ring
    have hd4 : deriv (fun t : ℝ ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
        fun t ↦ (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
      ext t
      rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
        deriv_const_mul _ (by fun_prop), _root_.deriv_exp (by fun_prop), deriv_div_const,
        deriv_fun_pow (by fun_prop), deriv_fun_pow (by fun_prop)]; simp; ring
    rw [iteratedDeriv_succ (n := 3), iteratedDeriv_succ (n := 2), iteratedDeriv_succ (n := 1),
      iteratedDeriv_one, hd1, hd2, hd3, hd4]; norm_num
  have hint_m : ∀ m : ℕ, Integrable (fun g ↦ (b ⬝ᵥ g) ^ m) (stdGaussPi Ω) := fun m ↦ by
    have h := memLp_dotProduct_pi_gaussianReal b (p := (m : ℝ≥0∞)) (by simp)
    rcases m with _ | m
    · simp
    · exact (h.integrable_norm_pow (Nat.succ_ne_zero m)).mono' (by fun_prop)
        (ae_of_all _ fun g ↦ by simp)
  have hLHS : ∫ g, (a0 + ρ * (b ⬝ᵥ g)) ^ 4 ∂stdGaussPi Ω =
      a0 ^ 4 + 6 * a0 ^ 2 * ρ ^ 2 * σsq + 3 * ρ ^ 4 * σsq ^ 2 := by
    simp_rw [show ∀ g, (a0 + ρ * (b ⬝ᵥ g)) ^ 4 =
        a0 ^ 4 + (4 * a0 ^ 3 * ρ) * (b ⬝ᵥ g) ^ 1 + (6 * a0 ^ 2 * ρ ^ 2) * (b ⬝ᵥ g) ^ 2 +
        (4 * a0 * ρ ^ 3) * (b ⬝ᵥ g) ^ 3 + ρ ^ 4 * (b ⬝ᵥ g) ^ 4 from fun _ ↦ by ring]
    rw [integral_add, integral_add, integral_add, integral_add]
    · simp only [integral_const, probReal_univ, one_smul, integral_const_mul, hmom,
        hm1, hm2, hm3, hm4, Real.sq_sqrt hσ_nonneg,
        show Real.sqrt σsq ^ 4 = σsq ^ 2 from by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hσ_nonneg]]; ring
    all_goals first
      | exact (((integrable_const _).add ((hint_m 1).const_mul _)).add
          ((hint_m 2).const_mul _)).add ((hint_m 3).const_mul _)
      | exact ((integrable_const _).add ((hint_m 1).const_mul _)).add ((hint_m 2).const_mul _)
      | exact (integrable_const _).add ((hint_m 1).const_mul _)
      | exact integrable_const _ | exact (hint_m _).const_mul _
  have hRHS : ∫ g, (a0 + b ⬝ᵥ g) ^ 2 ∂stdGaussPi Ω = a0 ^ 2 + σsq := by
    simp_rw [show ∀ g, (a0 + b ⬝ᵥ g) ^ 2 = a0 ^ 2 + (2 * a0) * (b ⬝ᵥ g) ^ 1 + (b ⬝ᵥ g) ^ 2
      from fun _ ↦ by ring]
    rw [integral_add, integral_add]
    · simp only [integral_const, probReal_univ, one_smul, integral_const_mul, hmom, hm1, hm2,
        Real.sq_sqrt hσ_nonneg]; ring
    all_goals first
      | exact (integrable_const _).add ((hint_m 1).const_mul _)
      | exact integrable_const _ | exact (hint_m _).const_mul _ | exact hint_m _
  rw [hLHS, hRHS]
  have hρ4 : 3 * ρ ^ 4 ≤ 1 := by nlinarith [sq_nonneg ρ]
  have h1 : 6 * a0 ^ 2 * ρ ^ 2 * σsq ≤ 2 * a0 ^ 2 * σsq := by
    have := mul_le_mul_of_nonneg_left hρ (show 0 ≤ 6 * a0 ^ 2 * σsq by positivity); linarith
  have h2 : 3 * ρ ^ 4 * σsq ^ 2 ≤ σsq ^ 2 := by
    have := mul_le_mul_of_nonneg_right hρ4 (sq_nonneg σsq); linarith
  have hsq_exp : (a0 ^ 2 + σsq) ^ 2 = a0 ^ 4 + 2 * a0 ^ 2 * σsq + σsq ^ 2 := by ring
  linarith

/-- Single-block discrete `(2, 4, ρ)`-hypercontractivity from `Hypercontractivity.lean`. -/
lemma discreteBlock_hypercontractivity_2_4 {Ω : Type*} [Fintype Ω] {q : ℕ}
    (E : BlockEnsemble Ω q) (a0 : ℝ) (a : Fin q → ℝ) :
    ∑ ω : Ω, (E.μ ω).toReal *
        (a0 + hypercontractivityRho 4 E.α * ∑ j : Fin q, a j * E.X ω j) ^ 4 ≤
      (∑ ω : Ω, (E.μ ω).toReal * (a0 + ∑ j : Fin q, a j * E.X ω j) ^ 2) ^ 2 := by
  let c_scale : ℝ := hypercontractivityRho 4 E.α / hypercontractivityRho 2 E.α
  have hc_nonneg : 0 ≤ c_scale :=
    div_nonneg (hypercontractivityRho_pos 4 E.α_pos).le (hypercontractivityRho_pos 2 E.α_pos).le
  have hc_le_one : c_scale ≤ 1 := by
    dsimp only [c_scale]; rw [hypercontractivityRho_eq_div, hypercontractivityRho_eq_div]
    rw [div_le_one (div_pos (Real.sqrt_pos.mpr E.α_pos) (by positivity))]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (by norm_num)
  let g : Ω → ℂ := fun ω ↦ ((∑ j : Fin q, a j * E.X ω j : ℝ) : ℂ)
  let g' : Ω → ℂ := fun ω ↦ (c_scale : ℂ) * g ω
  have hg0_real : ∑ ω : Ω, (E.μ ω).toReal * (∑ j : Fin q, a j * E.X ω j) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    calc ∑ ω : Ω, (E.μ ω).toReal * (a j * E.X ω j)
        = a j * ∑ ω : Ω, (E.μ ω).toReal * E.X ω j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ω _ ↦ by ring
      _ = 0 := by rw [E.centered j, mul_zero]
  have hg'0 : ∑ ω : Ω, ((E.μ ω).toReal : ℂ) * g' ω = 0 := by
    have : ∑ ω : Ω, ((E.μ ω).toReal : ℂ) * g' ω =
        (c_scale : ℂ) * ((∑ ω : Ω, (E.μ ω).toReal * (∑ j : Fin q, a j * E.X ω j) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      simp only [g', g, Complex.ofReal_mul]; ring
    rw [this, hg0_real, Complex.ofReal_zero, mul_zero]
  have hsingle := singleSite_hypercontractivity_even E.μ E.α_pos E.atom_lb (k := 2) (by omega)
    (a0 : ℂ) g' hg'0
  have hLHS : ∀ ω, ‖(a0 : ℂ) + (hypercontractivityRho 2 E.α : ℂ) * g' ω‖ ^ (2 * 2) =
      (a0 + hypercontractivityRho 4 E.α * ∑ j : Fin q, a j * E.X ω j) ^ 4 := by
    intro ω
    have hρ2_ne : hypercontractivityRho 2 E.α ≠ 0 := (hypercontractivityRho_pos 2 E.α_pos).ne'
    have heq : (a0 : ℂ) + (hypercontractivityRho 2 E.α : ℂ) * g' ω =
        ((a0 + hypercontractivityRho 4 E.α * ∑ j : Fin q, a j * E.X ω j : ℝ) : ℂ) := by
      have hmul : hypercontractivityRho 2 E.α * c_scale = hypercontractivityRho 4 E.α :=
        mul_div_cancel₀ _ hρ2_ne
      simp only [g', g]; push_cast
      rw [← mul_assoc]; norm_cast; rw [hmul]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      show (2 * 2 : ℕ) = 4 by rfl,
      show ∀ t : ℝ, |t| ^ 4 = t ^ 4 from fun t ↦ by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]]
  have hRHS_le : ‖(a0 : ℂ)‖ ^ 2 + ∑ ω : Ω, (E.μ ω).toReal * ‖g' ω‖ ^ 2 ≤
      ∑ ω : Ω, (E.μ ω).toReal * (a0 + ∑ j : Fin q, a j * E.X ω j) ^ 2 := by
    have hexp : ∑ ω : Ω, (E.μ ω).toReal * (a0 + ∑ j : Fin q, a j * E.X ω j) ^ 2 =
        a0 ^ 2 + ∑ ω : Ω, (E.μ ω).toReal * (∑ j : Fin q, a j * E.X ω j) ^ 2 := by
      have h1 : ∀ ω, (E.μ ω).toReal * (a0 + ∑ j : Fin q, a j * E.X ω j) ^ 2 =
          (E.μ ω).toReal * a0 ^ 2 + (2 * a0) * ((E.μ ω).toReal * (∑ j : Fin q, a j * E.X ω j)) +
          (E.μ ω).toReal * (∑ j : Fin q, a j * E.X ω j) ^ 2 := fun ω ↦ by ring
      simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        sum_pmf_toReal, hg0_real]
      ring
    rw [hexp, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsum_le : ∑ ω : Ω, (E.μ ω).toReal * ‖g' ω‖ ^ 2 ≤
        ∑ ω : Ω, (E.μ ω).toReal * (∑ j : Fin q, a j * E.X ω j) ^ 2 :=
      Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (by
        have hsq : ‖g' ω‖ ^ 2 = c_scale ^ 2 * (∑ j : Fin q, a j * E.X ω j) ^ 2 := by
          simp only [g', g, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
        rw [hsq]
        nlinarith [sq_nonneg (∑ j : Fin q, a j * E.X ω j),
          mul_nonneg hc_nonneg (sub_nonneg.mpr hc_le_one)]) ENNReal.toReal_nonneg
    linarith
  have hbase_nn : 0 ≤ ‖(a0 : ℂ)‖ ^ 2 + ∑ ω : Ω, (E.μ ω).toReal * ‖g' ω‖ ^ 2 := by positivity
  calc ∑ ω : Ω, (E.μ ω).toReal *
          (a0 + hypercontractivityRho 4 E.α * ∑ j : Fin q, a j * E.X ω j) ^ 4
      = ∑ ω : Ω, (E.μ ω).toReal * ‖(a0 : ℂ) + (hypercontractivityRho 2 E.α : ℂ) * g' ω‖ ^ (2 * 2) :=
        Finset.sum_congr rfl fun ω _ ↦ by rw [hLHS ω]
    _ ≤ (‖(a0 : ℂ)‖ ^ 2 + ∑ ω : Ω, (E.μ ω).toReal * ‖g' ω‖ ^ 2) ^ 2 := hsingle
    _ ≤ (∑ ω : Ω, (E.μ ω).toReal * (a0 + ∑ j : Fin q, a j * E.X ω j) ^ 2) ^ 2 :=
        pow_le_pow_left₀ hbase_nn hRHS_le 2

/-- **Four-line Fubini + Cauchy-Schwarz `L²`-Minkowski lemma**: for any nonnegative measurable
`F : α × β → ℝ` integrable in `L²(μ × ν)`, `𝔼_ν[(𝔼_μ[F(·, y)²])²] ≤
  (𝔼_μ[(𝔼_ν[F(x, ·)⁴])^{1/2}])²`. -/
lemma fubini_l2_minkowski {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : α → β → ℝ} (hF : Measurable (Function.uncurry F))
    (hF4 : Integrable (fun p : α × β ↦ (F p.1 p.2) ^ 4) (μ.prod ν)) :
    ∫ y, (∫ x, (F x y) ^ 2 ∂μ) ^ 2 ∂ν ≤
      (∫ x, Real.sqrt (∫ y, (F x y) ^ 4 ∂ν) ∂μ) ^ 2 := by
  -- Use `∫_y (∫_x F(x,y)²)² = ∫_{x₁} ∫_{x₂} ∫_y F(x₁,y)² F(x₂,y)² ≤ ∫_{x₁} ∫_{x₂} √(∫ F⁴) √(∫ F⁴)`.
  have hcs : ∀ x₁ x₂ : α,
      Integrable (fun y ↦ (F x₁ y) ^ 4) ν → Integrable (fun y ↦ (F x₂ y) ^ 4) ν →
      ∫ y, (F x₁ y) ^ 2 * (F x₂ y) ^ 2 ∂ν ≤
        Real.sqrt (∫ y, (F x₁ y) ^ 4 ∂ν) * Real.sqrt (∫ y, (F x₂ y) ^ 4 ∂ν) := by
    intro x₁ x₂ h1 h2
    have h1_nn : 0 ≤ ∫ y, (F x₁ y) ^ 4 ∂ν := integral_nonneg fun _ ↦ by positivity
    have h2_nn : 0 ≤ ∫ y, (F x₂ y) ^ 4 ∂ν := integral_nonneg fun _ ↦ by positivity
    have hzero_case : ∀ u v : α, Integrable (fun y ↦ (F u y) ^ 4) ν →
        ∫ y, (F u y) ^ 4 ∂ν = 0 → ∀ᵐ y ∂ν, (F u y) ^ 2 * (F v y) ^ 2 = 0 := fun u _ hu hz ↦
      ((integral_eq_zero_iff_of_nonneg (fun _ ↦ by positivity) hu).mp hz).mono fun y hy ↦ by
        have : F u y = 0 := by by_contra hne; exact absurd hy (pow_ne_zero 4 hne)
        simp [this]
    by_cases hz1 : ∫ y, (F x₁ y) ^ 4 ∂ν = 0
    · rw [integral_eq_zero_of_ae (hzero_case x₁ x₂ h1 hz1), hz1, Real.sqrt_zero, zero_mul]
    · by_cases hz2 : ∫ y, (F x₂ y) ^ 4 ∂ν = 0
      · have hprod := (hzero_case x₂ x₁ h2 hz2).mono fun y hy ↦ by rw [mul_comm] at hy; exact hy
        rw [integral_eq_zero_of_ae hprod, hz2, Real.sqrt_zero, mul_zero]
      · let s1 := Real.sqrt (∫ y, (F x₁ y) ^ 4 ∂ν)
        let s2 := Real.sqrt (∫ y, (F x₂ y) ^ 4 ∂ν)
        have hs1 : 0 < s1 := Real.sqrt_pos.mpr (lt_of_le_of_ne h1_nn (Ne.symm hz1))
        have hs2 : 0 < s2 := Real.sqrt_pos.mpr (lt_of_le_of_ne h2_nn (Ne.symm hz2))
        have hamgm : ∀ y, (F x₁ y) ^ 2 * (F x₂ y) ^ 2 / (s1 * s2) ≤
            (1 / 2 : ℝ) * ((F x₁ y) ^ 4 / s1 ^ 2 + (F x₂ y) ^ 4 / s2 ^ 2) := fun y ↦ by
          have hsq : 0 ≤ ((F x₁ y) ^ 2 / s1 - (F x₂ y) ^ 2 / s2) ^ 2 := sq_nonneg _
          have hexp : ((F x₁ y) ^ 2 / s1 - (F x₂ y) ^ 2 / s2) ^ 2 =
              (F x₁ y) ^ 4 / s1 ^ 2 - 2 * ((F x₁ y) ^ 2 * (F x₂ y) ^ 2 / (s1 * s2)) +
              (F x₂ y) ^ 4 / s2 ^ 2 := by field_simp [hs1.ne', hs2.ne']; ring
          linarith
        have hint_lhs : Integrable (fun y ↦ (F x₁ y) ^ 2 * (F x₂ y) ^ 2 / (s1 * s2)) ν :=
          (((h1.div_const (s1 ^ 2)).add (h2.div_const (s2 ^ 2))).const_mul (1 / 2)).mono'
            (by fun_prop) (ae_of_all _ fun y ↦ by
              rw [Real.norm_of_nonneg (by positivity)]; exact hamgm y)
        have hle := integral_mono hint_lhs
          (((h1.div_const (s1 ^ 2)).add (h2.div_const (s2 ^ 2))).const_mul (1 / 2)) hamgm
        rw [integral_div, integral_const_mul] at hle
        change _ ≤ (1 / 2 : ℝ) * ∫ y, ((F x₁ y) ^ 4 / s1 ^ 2 + (F x₂ y) ^ 4 / s2 ^ 2) ∂ν at hle
        rw [integral_add (h1.div_const _) (h2.div_const _), integral_div, integral_div,
          Real.sq_sqrt h1_nn, Real.sq_sqrt h2_nn,
          div_self (ne_of_gt (lt_of_le_of_ne h1_nn (Ne.symm hz1))),
          div_self (ne_of_gt (lt_of_le_of_ne h2_nn (Ne.symm hz2)))] at hle
        exact (div_le_one (mul_pos hs1 hs2)).mp (by linarith)
  have hF2 : Integrable (fun p : α × β ↦ (F p.1 p.2) ^ 2) (μ.prod ν) := by
    refine ((integrable_const (1 : ℝ)).add hF4).mono' (by fun_prop) (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    have h4 : (F p.1 p.2) ^ 4 = ((F p.1 p.2) ^ 2) ^ 2 := by ring
    rw [h4]; nlinarith [sq_nonneg ((F p.1 p.2) ^ 2 - 1)]
  have hF4_ae : ∀ᵐ x ∂μ, Integrable (fun y ↦ (F x y) ^ 4) ν := hF4.prod_right_ae
  have hexpand : ∀ y, (∫ x, (F x y) ^ 2 ∂μ) ^ 2 =
      ∫ p : α × α, (F p.1 y) ^ 2 * (F p.2 y) ^ 2 ∂(μ.prod μ) := fun y ↦ by
    rw [sq, integral_prod_mul (f := fun x ↦ (F x y) ^ 2) (g := fun x ↦ (F x y) ^ 2)]
  have hmp_fst : MeasurePreserving (Prod.fst : α × α → α) (μ.prod μ) μ :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod]; simp⟩
  have hmp_snd : MeasurePreserving (Prod.snd : α × α → α) (μ.prod μ) μ :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
  have hswap_int : Integrable (fun q : (α × α) × β ↦ (F q.1.1 q.2) ^ 2 * (F q.1.2 q.2) ^ 2)
      ((μ.prod μ).prod ν) := by
    have h1 : Integrable (fun q : (α × α) × β ↦ (F q.1.1 q.2) ^ 4) ((μ.prod μ).prod ν) :=
      (memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hF4).comp_measurePreserving
        (hmp_fst.prod (MeasurePreserving.id ν)))).congr (ae_of_all _ fun _ ↦ rfl)
    have h2 : Integrable (fun q : (α × α) × β ↦ (F q.1.2 q.2) ^ 4) ((μ.prod μ).prod ν) :=
      (memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hF4).comp_measurePreserving
        (hmp_snd.prod (MeasurePreserving.id ν)))).congr (ae_of_all _ fun _ ↦ rfl)
    refine ((h1.add h2).const_mul (1 / 2)).mono' (by fun_prop) (ae_of_all _ fun q ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]; simp only [Pi.add_apply]
    rw [show (F q.1.1 q.2) ^ 4 = ((F q.1.1 q.2) ^ 2) ^ 2 by ring,
      show (F q.1.2 q.2) ^ 4 = ((F q.1.2 q.2) ^ 2) ^ 2 by ring]
    nlinarith [sq_nonneg ((F q.1.1 q.2) ^ 2 - (F q.1.2 q.2) ^ 2)]
  simp_rw [hexpand]
  rw [← integral_integral_swap (μ := μ.prod μ) (ν := ν)
    (f := fun p y ↦ (F p.1 y) ^ 2 * (F p.2 y) ^ 2) hswap_int]
  have hbound_int : Integrable (fun p : α × α ↦
      Real.sqrt (∫ y, (F p.1 y) ^ 4 ∂ν) * Real.sqrt (∫ y, (F p.2 y) ^ 4 ∂ν)) (μ.prod μ) := by
    have h1 : Integrable (fun x ↦ Real.sqrt (∫ y, (F x y) ^ 4 ∂ν)) μ := by
      refine ((integrable_const (1 : ℝ)).add hF4.integral_prod_left).mono'
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          hF4.aestronglyMeasurable.integral_prod_right') (ae_of_all _ fun x ↦ ?_)
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      let s := Real.sqrt (∫ y, (F x y) ^ 4 ∂ν)
      have hs : s ^ 2 = ∫ y, (F x y) ^ 4 ∂ν := Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)
      dsimp only; change s ≤ 1 + ∫ y, (F x y) ^ 4 ∂ν; nlinarith [sq_nonneg (s - 1)]
    exact h1.mul_prod h1
  have hle_prod : ∫ p : α × α, ∫ y, (F p.1 y) ^ 2 * (F p.2 y) ^ 2 ∂ν ∂(μ.prod μ) ≤
      ∫ p : α × α, Real.sqrt (∫ y, (F p.1 y) ^ 4 ∂ν) *
        Real.sqrt (∫ y, (F p.2 y) ^ 4 ∂ν) ∂(μ.prod μ) :=
    integral_mono_ae hswap_int.integral_prod_left hbound_int
      (((hmp_fst.quasiMeasurePreserving.ae hF4_ae).and
        (hmp_snd.quasiMeasurePreserving.ae hF4_ae)).mono fun p ⟨hp1, hp2⟩ ↦ hcs p.1 p.2 hp1 hp2)
  rw [integral_prod_mul (f := fun x ↦ Real.sqrt (∫ y, (F x y) ^ 4 ∂ν))
    (g := fun x ↦ Real.sqrt (∫ y, (F x y) ^ 4 ∂ν))] at hle_prod
  simpa [sq] using hle_prod

end BlockPolynomials

section HybridInvariance

/-- Measure of a single block: discrete `μ` (on `Ω`, lifted to `Measure Ω`) when `b = false`,
or Gaussian `stdGaussPi Ω` (on `Ω → ℝ`) when `b = true`. We represent hybrid blocks cleanly on
the unified space `Ω × (Ω → ℝ)` equipped with `μ.toMeasure.prod (stdGaussPi Ω)`! -/
@[expose] noncomputable def blockSpaceMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    {q : ℕ} (E : BlockEnsemble Ω q) : Measure (Ω × (Ω → ℝ)) :=
  E.μ.toMeasure.prod (stdGaussPi Ω)

lemma blockSpaceMeasure_eq_prod {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    {q : ℕ} (E : BlockEnsemble Ω q) :
    blockSpaceMeasure E = E.μ.toMeasure.prod (stdGaussPi Ω) := rfl

instance blockSpaceMeasure_isProbabilityMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    {q : ℕ} (E : BlockEnsemble Ω q) : IsProbabilityMeasure (blockSpaceMeasure E) := by
  unfold blockSpaceMeasure; infer_instance

/-- Hybrid block value at coordinate `i` given choice `isGauss : Fin n → Bool`:
either the discrete vector `E.X (z i).1` or the Gaussian vector `gaussBlock E (z i).2`. -/
@[expose] noncomputable def hybridVec {Ω : Type*} [Fintype Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    (isGauss : Fin n → Bool) (z : Fin n → Ω × (Ω → ℝ)) (i : Fin n) : Fin q → ℝ :=
  if isGauss i then gaussBlock E (z i).2 else E.X (z i).1

lemma hybridVec_eq_ite {Ω : Type*} [Fintype Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    (isGauss : Fin n → Bool) (z : Fin n → Ω × (Ω → ℝ)) (i : Fin n) :
    hybridVec E isGauss z i = if isGauss i then gaussBlock E (z i).2 else E.X (z i).1 := rfl

@[simp]
lemma hybridVec_of_true {Ω : Type*} [Fintype Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    {isGauss : Fin n → Bool} (z : Fin n → Ω × (Ω → ℝ)) {i : Fin n} (h : isGauss i = true) :
    hybridVec E isGauss z i = gaussBlock E (z i).2 := by simp [hybridVec, h]

@[simp]
lemma hybridVec_of_false {Ω : Type*} [Fintype Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    {isGauss : Fin n → Bool} (z : Fin n → Ω × (Ω → ℝ)) {i : Fin n} (h : isGauss i = false) :
    hybridVec E isGauss z i = E.X (z i).1 := by simp [hybridVec, h]

/-- Product measure on `n` independent hybrid blocks `Fin n → Ω × (Ω → ℝ)`. -/
@[expose] noncomputable def hybridProductMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    {n q : ℕ} (E : BlockEnsemble Ω q) :
    Measure (Fin n → Ω × (Ω → ℝ)) :=
  Measure.pi fun _ : Fin n ↦ blockSpaceMeasure E

instance hybridProductMeasure_isProbabilityMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    {n q : ℕ} (E : BlockEnsemble Ω q) :
    IsProbabilityMeasure (hybridProductMeasure (n := n) E) := by
  unfold hybridProductMeasure; infer_instance

private lemma integral_pmf_toMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (μ : PMF Ω) (G : Ω → ℝ) :
    ∫ ω, G ω ∂μ.toMeasure = ∑ ω : Ω, (μ ω).toReal * G ω := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ω), smul_eq_mul]

/-- Integrability of any power of a block-multilinear polynomial under `hybridProductMeasure`. -/
lemma integrable_hybrid_poly_pow {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    (isGauss : Fin n → Bool) (f : (Fin n → Option (Fin q)) → ℝ) (ρ' : ℝ) (p : ℕ) :
    Integrable (fun z : Fin n → Ω × (Ω → ℝ) ↦
      (∑ α : Fin n → Option (Fin q), f α * ∏ i : Fin n,
        match α i with | none => 1 | some j => ρ' * hybridVec E isGauss z i j) ^ p)
      (hybridProductMeasure E) := by
  have hX_meas : Measurable E.X := measurable_of_finite E.X
  have hsingle : ∀ (i : Fin n) (a : Option (Fin q)) (m : ℕ),
      Integrable (fun z0 : Ω × (Ω → ℝ) ↦
        |(match a with
          | none => (1 : ℝ)
          | some j => ρ' * (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j)| ^ m)
        (blockSpaceMeasure E) := by
    intro i a m
    cases a with
    | none => simp only [abs_one, one_pow]; exact integrable_const _
    | some j =>
      cases hig : isGauss i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hm_j : Measurable (fun z0 : Ω × (Ω → ℝ) ↦ |ρ' * E.X z0.1 j| ^ m) :=
          (continuous_abs.measurable.comp (measurable_const.mul
            ((measurable_pi_apply j).comp (hX_meas.comp measurable_fst)))).pow_const m
        exact Integrable.of_bound hm_j.aestronglyMeasurable
          ((|ρ'| * ∑ ω : Ω, |E.X ω j|) ^ m) (ae_of_all _ fun z0 ↦ by
            rw [Real.norm_of_nonneg (by positivity), abs_mul]
            refine pow_le_pow_left₀ (by positivity) ?_ m
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (f := fun ω ↦ |E.X ω j|) (fun _ _ ↦ abs_nonneg _)
                (Finset.mem_univ z0.1)) (abs_nonneg _))
      · simp only [↓reduceIte, blockSpaceMeasure]
        have hmp_snd : MeasurePreserving (Prod.snd : Ω × (Ω → ℝ) → Ω → ℝ)
            (E.μ.toMeasure.prod (stdGaussPi Ω)) (stdGaussPi Ω) :=
          ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
        have hmem : MemLp (fun z0 : Ω × (Ω → ℝ) ↦ ρ' * gaussBlock E z0.2 j)
            (m : ℝ≥0∞) (E.μ.toMeasure.prod (stdGaussPi Ω)) :=
          ((gaussBlock_memLp E j (by simp)).comp_measurePreserving hmp_snd).const_mul ρ'
        rcases m with _ | m
        · simp
        · simpa [Real.norm_eq_abs] using hmem.integrable_norm_pow (Nat.succ_ne_zero m)
  have hexp : ∀ z : Fin n → Ω × (Ω → ℝ),
      (∑ α : Fin n → Option (Fin q), f α * ∏ i : Fin n,
        match α i with | none => 1 | some j => ρ' * hybridVec E isGauss z i j) ^ p =
      ∑ g : Fin p → (Fin n → Option (Fin q)), (∏ r : Fin p, f (g r)) *
        ∏ i : Fin n, ∏ r : Fin p, match (g r) i with
          | none => (1 : ℝ) | some j => ρ' * hybridVec E isGauss z i j := by
    intro z
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [hexp]
  refine integrable_finsetSum _ fun g _ ↦ (Integrable.const_mul ?_ _)
  have hcoord : ∀ i : Fin n, Integrable (fun z0 : Ω × (Ω → ℝ) ↦
      ∏ r : Fin p, match (g r) i with
        | none => (1 : ℝ) | some j =>
          ρ' * (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j)
      (blockSpaceMeasure E) := by
    intro i
    let u (r : Fin p) (z0 : Ω × (Ω → ℝ)) : ℝ := match (g r) i with
      | none => 1 | some j => ρ' * (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j
    have hbound : ∀ z0, ‖∏ r : Fin p, u r z0‖ ≤
        (p : ℝ) ^ p * ∑ r : Fin p, |u r z0| ^ p + 1 := by
      intro z0
      rw [Real.norm_eq_abs, Finset.abs_prod]
      rcases p.eq_zero_or_pos with rfl | hp
      · simp
      · obtain ⟨r₀, _, hr₀⟩ := Finset.exists_max_image Finset.univ (fun r : Fin p ↦ |u r z0|)
          ⟨⟨0, hp⟩, Finset.mem_univ _⟩
        have hprod_le : ∏ r : Fin p, |u r z0| ≤ |u r₀ z0| ^ p := by
          have hsub : ∀ s : Finset (Fin p), ∏ r ∈ s, |u r z0| ≤ |u r₀ z0| ^ s.card := fun s ↦ by
            induction s using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
              exact mul_le_mul (hr₀ a (Finset.mem_univ a)) ih
                (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) (abs_nonneg _)
          simpa using hsub Finset.univ
        have h1 : |u r₀ z0| ^ p ≤ (p : ℝ) ^ p * ∑ r : Fin p, |u r z0| ^ p := by
          have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ p := one_le_pow₀ (by exact_mod_cast hp)
          calc |u r₀ z0| ^ p ≤ 1 * ∑ r : Fin p, |u r z0| ^ p := by
                rw [one_mul]
                exact Finset.single_le_sum (f := fun r ↦ |u r z0| ^ p) (fun _ _ ↦ by positivity)
                  (Finset.mem_univ r₀)
            _ ≤ (p : ℝ) ^ p * ∑ r : Fin p, |u r z0| ^ p :=
                mul_le_mul_of_nonneg_right hp1 (Finset.sum_nonneg fun _ _ ↦ by positivity)
        linarith
    have hdom : Integrable (fun z0 ↦ (p : ℝ) ^ p * ∑ r : Fin p, |u r z0| ^ p + 1)
        (blockSpaceMeasure E) :=
      ((integrable_finsetSum _ fun r _ ↦ hsingle i (g r i) p).const_mul _).add (integrable_const _)
    exact hdom.mono' (by
      have hu_m : ∀ r, Measurable (u r) := fun r ↦ by
        unfold u; cases (g r) i with
        | none => fun_prop
        | some j =>
          cases isGauss i
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact measurable_const.mul ((measurable_pi_apply j).comp (hX_meas.comp measurable_fst))
          · simp only [↓reduceIte]; unfold gaussBlock; fun_prop
      exact (Finset.measurable_prod _ fun r _ ↦ hu_m r).aestronglyMeasurable) (ae_of_all _ hbound)
  unfold hybridProductMeasure
  exact Integrable.fintype_prod (μ := fun _ : Fin n ↦ blockSpaceMeasure E) hcoord

/-- Exact `L²` formula for a block-multilinear polynomial under any hybrid distribution:
independent of `isGauss`, orthogonal across distinct supports, and bounded by `q^d · ∑ (f α)²`. -/
lemma hybrid_poly_l2_eq {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    (isGauss : Fin n → Bool) (f : (Fin n → Option (Fin q)) → ℝ) :
    let P (j l : Fin q) : ℝ := ∑ ω : Ω, (E.μ ω).toReal * E.X ω j * E.X ω l
    ∫ z, (∑ α, f α * ∏ i : Fin n,
        match α i with | none => 1 | some j => hybridVec E isGauss z i j) ^ 2
        ∂hybridProductMeasure E =
      ∑ α : Fin n → Option (Fin q), ∑ β ∈ Finset.univ.filter (fun β ↦ blockSupp β = blockSupp α),
        f α * f β * ∏ i : Fin n, match α i, β i with
          | some j, some l => P j l
          | _, _ => 1 := by
  intro P
  have hX_meas : Measurable E.X := measurable_of_finite E.X
  have hmp_snd : MeasurePreserving (Prod.snd : Ω × (Ω → ℝ) → Ω → ℝ)
      (E.μ.toMeasure.prod (stdGaussPi Ω)) (stdGaussPi Ω) :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
  have hsingle_mean : ∀ (i : Fin n) (j : Fin q),
      ∫ z0 : Ω × (Ω → ℝ), (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j
        ∂blockSpaceMeasure E = 0 := by
    intro i j
    cases isGauss i
    · simp only [Bool.false_eq_true, ↓reduceIte, blockSpaceMeasure]
      rw [integral_fun_fst (f := fun ω : Ω ↦ E.X ω j), probReal_univ, one_smul,
        integral_pmf_toMeasure]
      exact E.centered j
    · simp only [↓reduceIte, blockSpaceMeasure]
      rw [integral_fun_snd (f := fun g : Ω → ℝ ↦ gaussBlock E g j)]
      simp [gaussBlock_mean_zero]
  have hsingle_cov : ∀ (i : Fin n) (j l : Fin q),
      ∫ z0 : Ω × (Ω → ℝ), (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j *
          (if isGauss i then gaussBlock E z0.2 else E.X z0.1) l
        ∂blockSpaceMeasure E = P j l := by
    intro i j l
    cases isGauss i
    · simp only [Bool.false_eq_true, ↓reduceIte, blockSpaceMeasure]
      rw [integral_fun_fst (f := fun ω : Ω ↦ E.X ω j * E.X ω l), probReal_univ, one_smul,
        integral_pmf_toMeasure]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    · simp only [↓reduceIte, blockSpaceMeasure]
      rw [integral_fun_snd (f := fun g : Ω → ℝ ↦ gaussBlock E g j * gaussBlock E g l)]
      simpa [P] using gaussBlock_cov E j l
  have hexp : ∀ z : Fin n → Ω × (Ω → ℝ),
      (∑ α, f α * ∏ i : Fin n,
        match α i with | none => 1 | some j => hybridVec E isGauss z i j) ^ 2 =
      ∑ α, ∑ β, (f α * f β) * ∏ i : Fin n,
        (match α i with | none => (1 : ℝ) | some j => hybridVec E isGauss z i j) *
        (match β i with | none => (1 : ℝ) | some l => hybridVec E isGauss z i l) := by
    intro z
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [Finset.prod_mul_distrib]; ring
  simp_rw [hexp]
  let fPair (α β : Fin n → Option (Fin q)) (i : Fin n) (z0 : Ω × (Ω → ℝ)) : ℝ :=
    (match α i with | none => 1 | some j => (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j) *
    (match β i with | none => 1 | some l => (if isGauss i then gaussBlock E z0.2 else E.X z0.1) l)
  have hint_pair : ∀ α β : Fin n → Option (Fin q),
      Integrable (fun z : Fin n → Ω × (Ω → ℝ) ↦ (f α * f β) * ∏ i : Fin n,
        (match α i with | none => (1 : ℝ) | some j => hybridVec E isGauss z i j) *
        (match β i with | none => (1 : ℝ) | some l => hybridVec E isGauss z i l))
      (hybridProductMeasure E) := by
    intro α β
    refine Integrable.const_mul ?_ _
    unfold hybridProductMeasure
    refine Integrable.fintype_prod (μ := fun _ : Fin n ↦ blockSpaceMeasure E)
      (f := fPair α β) fun i ↦ ?_
    have hsingle_int : ∀ (i : Fin n) (j : Fin q),
        Integrable (fun z0 : Ω × (Ω → ℝ) ↦ (if isGauss i then gaussBlock E z0.2 else E.X z0.1) j)
          (blockSpaceMeasure E) := fun i j ↦ by
      cases isGauss i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact Integrable.of_bound
          (((measurable_pi_apply j).comp (hX_meas.comp measurable_fst)).aestronglyMeasurable)
          (∑ ω : Ω, |E.X ω j|) (ae_of_all _ fun z0 ↦
            Finset.single_le_sum (f := fun ω ↦ |E.X ω j|) (fun _ _ ↦ abs_nonneg _)
              (Finset.mem_univ z0.1))
      · simp only [↓reduceIte, blockSpaceMeasure]
        exact ((gaussBlock_memLp E j (by simp)).comp_measurePreserving hmp_snd).integrable le_rfl
    dsimp only [fPair]
    cases hα : α i with
    | none =>
      cases hβ : β i with
      | none => simp
      | some l => simpa [one_mul] using hsingle_int i l
    | some j =>
      cases hβ : β i with
      | none => simpa [mul_one] using hsingle_int i j
      | some l =>
        cases isGauss i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact Integrable.of_bound
            ((((measurable_pi_apply j).comp (hX_meas.comp measurable_fst)).mul
              ((measurable_pi_apply l).comp (hX_meas.comp measurable_fst))).aestronglyMeasurable)
            ((∑ ω : Ω, |E.X ω j|) * (∑ ω : Ω, |E.X ω l|)) (ae_of_all _ fun z0 ↦ by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul
                (Finset.single_le_sum (f := fun ω ↦ |E.X ω j|) (fun _ _ ↦ abs_nonneg _)
                  (Finset.mem_univ z0.1))
                (Finset.single_le_sum (f := fun ω ↦ |E.X ω l|) (fun _ _ ↦ abs_nonneg _)
                  (Finset.mem_univ z0.1))
                (abs_nonneg _) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
        · simp only [↓reduceIte, blockSpaceMeasure]
          have hj := (gaussBlock_memLp E j (p := 2) (by simp)).comp_measurePreserving hmp_snd
          exact hj.integrable_mul
            ((gaussBlock_memLp E l (p := 2) (by simp)).comp_measurePreserving hmp_snd)
  rw [integral_finsetSum _ fun α _ ↦ integrable_finsetSum _ fun β _ ↦ hint_pair α β]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [integral_finsetSum _ fun β _ ↦ hint_pair α β,
    ← Finset.sum_filter_add_sum_filter_not _ (fun β ↦ blockSupp β = blockSupp α)]
  have hzero : ∑ β ∈ Finset.univ.filter (fun β ↦ ¬ blockSupp β = blockSupp α),
      ∫ z, (f α * f β) * ∏ i : Fin n,
        (match α i with | none => (1 : ℝ) | some j => hybridVec E isGauss z i j) *
        (match β i with | none => (1 : ℝ) | some l => hybridVec E isGauss z i l)
      ∂hybridProductMeasure E = 0 := by
    refine Finset.sum_eq_zero fun β hβ ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
    unfold hybridProductMeasure; dsimp only [hybridVec]
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (μ := fun _ : Fin n ↦ blockSpaceMeasure E) (f := fPair α β)]
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin n, (α i).isSome ≠ (β i).isSome := by
      by_contra hall; push Not at hall; apply hβ; ext i; simp [blockSupp, hall i]
    have hfac0 : ∫ z0 : Ω × (Ω → ℝ), fPair α β i₀ z0 ∂blockSpaceMeasure E = 0 := by
      dsimp only [fPair]; cases hα0 : α i₀ <;> cases hβ0 : β i₀
      · simp [hα0, hβ0] at hi₀
      · simpa only [one_mul] using hsingle_mean i₀ _
      · simpa only [mul_one] using hsingle_mean i₀ _
      · simp [hα0, hβ0] at hi₀
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hfac0, mul_zero]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun β hβ ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
  unfold hybridProductMeasure; dsimp only [hybridVec]
  rw [integral_const_mul,
    integral_fintype_prod_eq_prod (μ := fun _ : Fin n ↦ blockSpaceMeasure E) (f := fPair α β)]
  congr 1; refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hs : (α i).isSome = (β i).isSome := by simpa [blockSupp] using (Finset.ext_iff.mp hβ i).symm
  dsimp only [fPair]; cases hαi : α i <;> cases hβi : β i
  · simp
  · simp [hαi, hβi] at hs
  · simp [hαi, hβi] at hs
  · exact hsingle_cov i _ _

/-- `L²` norm squared of a degree-`≤ d` block-multilinear polynomial is at most `q^d · ∑ (f α)²`. -/
lemma hybrid_poly_l2_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] {n q d : ℕ} (E : BlockEnsemble Ω q) (hq : q ≠ 0)
    (isGauss : Fin n → Bool) (f : (Fin n → Option (Fin q)) → ℝ)
    (hdeg : ∀ α, d < (blockSupp α).card → f α = 0) :
    ∫ z, (∑ α, f α * ∏ i : Fin n,
        match α i with | none => 1 | some j => hybridVec E isGauss z i j) ^ 2
        ∂hybridProductMeasure E ≤ (q : ℝ) ^ d * ∑ α, (f α) ^ 2 := by
  rw [hybrid_poly_l2_eq]
  let P (j l : Fin q) : ℝ := ∑ ω : Ω, (E.μ ω).toReal * E.X ω j * E.X ω l
  have hP_le : ∀ j l : Fin q, |P j l| ≤ 1 := by
    intro j l
    have hcs : |P j l| ≤ (1 / 2 : ℝ) * ((∑ ω, (E.μ ω).toReal * (E.X ω j) ^ 2) +
        (∑ ω, (E.μ ω).toReal * (E.X ω l) ^ 2)) := by
      calc |P j l| ≤ ∑ ω, |(E.μ ω).toReal * E.X ω j * E.X ω l| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ ω, (E.μ ω).toReal * ((1 / 2 : ℝ) * ((E.X ω j) ^ 2 + (E.X ω l) ^ 2)) := by
            refine Finset.sum_le_sum fun ω _ ↦ ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
            have hnn : 0 ≤ (E.μ ω).toReal := ENNReal.toReal_nonneg
            nlinarith [sq_nonneg (|E.X ω j| - |E.X ω l|), sq_abs (E.X ω j), sq_abs (E.X ω l)]
        _ = (1 / 2 : ℝ) * ((∑ ω, (E.μ ω).toReal * (E.X ω j) ^ 2) +
            (∑ ω, (E.μ ω).toReal * (E.X ω l) ^ 2)) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun ω _ ↦ by ring
    linarith [E.var_le_one j, E.var_le_one l]
  have hcard_supp : ∀ S : Finset (Fin n),
      (Finset.univ.filter (fun β : Fin n → Option (Fin q) ↦ blockSupp β = S)).card ≤ q ^ S.card :=
    fun S ↦ by
    rcases eq_or_ne q 0 with rfl | hq
    · rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
      · simpa using Finset.card_le_one.mpr fun a _ b _ ↦ funext fun i ↦ by
          cases a i <;> cases b i <;> first | rfl | exact ‹Fin 0›.elim0
      · rw [Finset.filter_eq_empty_iff.mpr fun β _ hβ ↦ by
          have := (Finset.mem_filter.mp (hβ ▸ hi₀)).2
          cases h : β i₀ with | none => simp [h] at this | some j => exact j.elim0]; simp
    · have hne : Nonempty (Fin q) := ⟨⟨0, Nat.pos_of_ne_zero hq⟩⟩
      let e : (Fin n → Option (Fin q)) → (S → Fin q) := fun β i ↦ (β i.1).getD hne.some
      have hinj : Set.InjOn e
          ((Finset.univ.filter (fun β : Fin n → Option (Fin q) ↦ blockSupp β = S) : Finset _) :
            Set _) := fun a ha b hb hab ↦ by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        ext i; by_cases hi : i ∈ S
        · have ha_s : (a i).isSome = true := by
            simpa [blockSupp] using (show i ∈ blockSupp a by rwa [ha])
          have hb_s : (b i).isSome = true := by
            simpa [blockSupp] using (show i ∈ blockSupp b by rwa [hb])
          have heq := congr_fun hab ⟨i, hi⟩
          cases h1 : a i <;> cases h2 : b i <;> simp_all [e]
        · have ha_n : a i = none := by
            simpa [blockSupp, Option.not_isSome_iff_eq_none] using (show i ∉ blockSupp a by
              rwa [ha])
          have hb_n : b i = none := by
            simpa [blockSupp, Option.not_isSome_iff_eq_none] using (show i ∉ blockSupp b by
              rwa [hb])
          rw [ha_n, hb_n]
      exact (Finset.card_le_card_of_injOn e (fun _ _ ↦ Finset.mem_univ _) hinj).trans_eq (by simp)
  have hstep : ∀ α β : Fin n → Option (Fin q), blockSupp β = blockSupp α →
      f α * f β * (∏ i : Fin n, match α i, β i with | some j, some l => P j l | _, _ => 1) ≤
      (1 / 2 : ℝ) * ((f α) ^ 2 + (f β) ^ 2) := fun α β _ ↦ by
    have hprod : |∏ i : Fin n, (match α i, β i with | some j, some l => P j l | _, _ => 1)| ≤
      1 := by
      rw [Finset.abs_prod]
      have hsub : ∀ s : Finset (Fin n),
          ∏ i ∈ s, |(match α i, β i with | some j, some l => P j l | _, _ => 1)| ≤ 1 := fun s ↦ by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.prod_insert ha]
          have ha1 : |(match α a, β a with | some j, some l => P j l | _, _ => 1)| ≤ 1 := by
            cases α a <;> cases β a <;> simp [hP_le]
          exact (mul_le_mul ha1 ih (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) zero_le_one).trans_eq
            (one_mul 1)
      exact hsub Finset.univ
    have h1 : f α * f β * (∏ i, match α i, β i with | some j, some l => P j l | _, _ => 1) ≤
        |f α| * |f β| := by
      calc _ ≤ |f α * f β * (∏ i, match α i, β i with | some j, some l => P j l | _, _ => 1)| :=
              le_abs_self _
        _ = |f α| * |f β| *
              |∏ i, (match α i, β i with | some j, some l => P j l | _, _ => 1)| := by
              rw [abs_mul, abs_mul]
        _ ≤ |f α| * |f β| * 1 := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = |f α| * |f β| := mul_one _
    nlinarith [sq_nonneg (|f α| - |f β|), sq_abs (f α), sq_abs (f β)]
  have hlhs_le : ∑ α : Fin n → Option (Fin q),
        ∑ β ∈ Finset.univ.filter (fun β : Fin n → Option (Fin q) ↦ blockSupp β = blockSupp α),
          f α * f β * (∏ i : Fin n, match α i, β i with | some j, some l => P j l | _, _ => 1) ≤
      ∑ α : Fin n → Option (Fin q),
        ((Finset.univ.filter (fun β : Fin n →
          Option (Fin q) ↦ blockSupp β = blockSupp α)).card : ℝ) *
          (f α) ^ 2 := by
    calc _ ≤ ∑ α, ∑ β ∈ Finset.univ.filter
            (fun β : Fin n → Option (Fin q) ↦ blockSupp β = blockSupp α),
            (1 / 2 : ℝ) * ((f α) ^ 2 + (f β) ^ 2) :=
          Finset.sum_le_sum fun α _ ↦ Finset.sum_le_sum fun β hβ ↦
            hstep α β (Finset.mem_filter.mp hβ).2
      _ = _ := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul]
          have hsym : ∑ α : Fin n → Option (Fin q),
              (1 / 2 : ℝ) * ∑ β ∈ Finset.univ.filter
                (fun β : Fin n → Option (Fin q) ↦ blockSupp β = blockSupp α), (f β) ^ 2 =
              ∑ α : Fin n → Option (Fin q), (1 / 2 : ℝ) *
                (((Finset.univ.filter
                  (fun β : Fin n → Option (Fin q) ↦ blockSupp β = blockSupp α)).card : ℝ) *
                  (f α) ^ 2) := by
            simp_rw [Finset.sum_filter, Finset.mul_sum]; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun β _ ↦ ?_
            simp_rw [← Finset.mul_sum, ← Finset.sum_filter]
            have heq_f : (Finset.univ.filter (fun α : Fin n →
              Option (Fin q) ↦ blockSupp β = blockSupp α)) =
                (Finset.univ.filter (fun α : Fin n →
                  Option (Fin q) ↦ blockSupp α = blockSupp β)) := by ext α; simp [eq_comm]
            rw [heq_f, Finset.sum_const, nsmul_eq_mul]
          simp_rw [Finset.mul_sum] at hsym ⊢
          rw [hsym, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
  refine hlhs_le.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ ↦ ?_
  by_cases hd : d < (blockSupp α).card
  · simp [hdeg α hd]
  · have hle_d : (blockSupp α).card ≤ d := not_lt.mp hd
    have h1 : ((Finset.univ.filter
          (fun β : Fin n → Option (Fin q) ↦ blockSupp β = blockSupp α)).card : ℝ) ≤
        (q : ℝ) ^ (blockSupp α).card := by exact_mod_cast hcard_supp (blockSupp α)
    have h2 : (q : ℝ) ^ (blockSupp α).card ≤ (q : ℝ) ^ d :=
      pow_le_pow_right₀ (by exact_mod_cast Nat.pos_of_ne_zero hq) hle_d
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)

/-- Hybrid `(2, 4)`-hypercontractivity for block-multilinear polynomials of degree at most `d`:
`𝔼[(f(H))⁴] ≤ ((d + 1)³ / ρ^{4d}) · (𝔼[(f(H))²])²`, where `ρ = hypercontractivityRho 4 E.α`. -/
theorem hybrid_hypercontractivity_2_4 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] {n q : ℕ} (E : BlockEnsemble Ω q)
    (isGauss : Fin n → Bool) {d : ℕ} (M : BlockPoly n q 1) (hdeg : M.HasDeg d) :
    ∫ z, (M.eval (hybridVec E isGauss z) 0) ^ 4 ∂hybridProductMeasure E ≤
      ((d + 1 : ℝ) ^ 3 / (hypercontractivityRho 4 E.α) ^ (4 * d)) *
        (∫ z, (M.eval (hybridVec E isGauss z) 0) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
  let ρ := hypercontractivityRho 4 E.α
  have hρ_pos : 0 < ρ := hypercontractivityRho_pos 4 E.α_pos
  have hρ_sq : ρ ^ 2 ≤ 1 / 3 := by
    dsimp only [ρ]; rw [hypercontractivityRho_eq_div]
    have h1 : E.α ≤ 1 := by
      obtain ⟨ω₀, hω₀⟩ := E.μ.support_nonempty
      calc E.α ≤ (E.μ ω₀).toReal := E.atom_lb ω₀ hω₀
        _ ≤ ∑ ω : Ω, (E.μ ω).toReal :=
            Finset.single_le_sum (fun _ _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ ω₀)
        _ = 1 := sum_pmf_toReal E.μ
    rw [div_pow, Real.sq_sqrt E.α_pos.le]
    rw [div_le_iff₀ (by positivity)]
    linarith [show (1 : ℝ) ≤ (1 / 3 : ℝ) * (16 * (4 : ℝ) ^ 4) ^ 2 by norm_num]
  have hρ_le_one : ρ ≤ 1 := by nlinarith
  have hTrho : ∀ (m : ℕ) (ig : Fin m → Bool) (f : (Fin m → Option (Fin q)) → ℝ),
      ∫ z, (∑ α, f α * ∏ i : Fin m, match α i with
          | none => 1 | some j => ρ * hybridVec E ig z i j) ^ 4 ∂hybridProductMeasure E ≤
      (∫ z, (∑ α, f α * ∏ i : Fin m, match α i with
          | none => 1 | some j => hybridVec E ig z i j) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
    intro m; induction m with
    | zero =>
      intro ig f
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, integral_const,
        probReal_univ, one_smul]; ring_nf; exact le_rfl
    | succ m ih =>
      intro ig f
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ Ω × (Ω → ℝ)) 0
      have hmp : MeasurePreserving e (hybridProductMeasure (n := m + 1) E)
          ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ blockSpaceMeasure E) 0
      let f0 : (Fin m → Option (Fin q)) → ℝ := fun β ↦
        f (Fin.cons (α := fun _ ↦ Option (Fin q)) none β)
      let fj : Fin q → (Fin m → Option (Fin q)) → ℝ := fun j β ↦
        f (Fin.cons (α := fun _ ↦ Option (Fin q)) (some j) β)
      let ig' : Fin m → Bool := fun i ↦ ig i.succ
      let A (ρ' : ℝ) (z' : Fin m → Ω × (Ω → ℝ)) : ℝ :=
        ∑ β, f0 β * ∏ i : Fin m, match β i with | none => 1 | some j => ρ' * hybridVec E ig' z' i j
      let B (ρ' : ℝ) (z' : Fin m → Ω × (Ω → ℝ)) (j : Fin q) : ℝ :=
        ∑ β, fj j β * ∏ i : Fin m,
          match β i with | none => 1 | some l => ρ' * hybridVec E ig' z' i l
      have hsplit : ∀ (ρ' : ℝ) (z : Fin (m + 1) → Ω × (Ω → ℝ)),
          (∑ α : Fin (m + 1) → Option (Fin q), f α * ∏ i : Fin (m + 1),
            match α i with | none => 1 | some j => ρ' * hybridVec E ig z i j) =
          A ρ' (Fin.tail z) + ρ' * ∑ j : Fin q, B ρ' (Fin.tail z) j * hybridVec E ig z 0 j := by
        intro ρ' z
        let eα : (Fin (m + 1) → Option (Fin q)) ≃ Option (Fin q) × (Fin m → Option (Fin q)) :=
          { toFun := fun α ↦ (α 0, Fin.tail α)
            invFun := fun p ↦ Fin.cons p.1 p.2
            left_inv := fun α ↦ Fin.cons_self_tail α
            right_inv := fun p ↦ by cases p; simp }
        rw [← Equiv.sum_comp eα.symm]
        simp only [Fintype.sum_prod_type, Fintype.sum_option, eα, Equiv.coe_fn_symm_mk]
        have hnone : ∀ β : Fin m → Option (Fin q),
            (f (Fin.cons (α := fun _ ↦ Option (Fin q)) none β) * ∏ i : Fin (m + 1),
              match (Fin.cons (α := fun _ ↦ Option (Fin q)) none β) i with
              | none => 1 | some j => ρ' * hybridVec E ig z i j) =
            f0 β * ∏ i : Fin m, match β i with
              | none => 1 | some j => ρ' * hybridVec E ig' (Fin.tail z) i j := fun β ↦ by
          rw [Fin.prod_univ_succ]; simp [f0, ig', hybridVec, Fin.tail]
        have hsome : ∀ (j : Fin q) (β : Fin m → Option (Fin q)),
            (f (Fin.cons (α := fun _ ↦ Option (Fin q)) (some j) β) * ∏ i : Fin (m + 1),
              match (Fin.cons (α := fun _ ↦ Option (Fin q)) (some j) β) i with
              | none => 1 | some l => ρ' * hybridVec E ig z i l) =
            ρ' * ((fj j β * ∏ i : Fin m, match β i with
              | none => 1 | some l => ρ' * hybridVec E ig' (Fin.tail z) i l) *
              hybridVec E ig z 0 j) := fun j β ↦ by
          rw [Fin.prod_univ_succ]; simp [fj, ig', hybridVec, Fin.tail]; ring
        simp only [hnone, hsome]; rw [Finset.mul_sum]; congr 1
        exact Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.mul_sum, Finset.sum_mul]
      let F (z0 : Ω × (Ω → ℝ)) (z' : Fin m → Ω × (Ω → ℝ)) : ℝ :=
        A ρ z' + ∑ j, B ρ z' j * (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j
      have hX_meas : Measurable E.X := measurable_of_finite E.X
      have hpoly_meas : ∀ (ρ' : ℝ) (g : (Fin m → Option (Fin q)) → ℝ),
          Measurable (fun z' : Fin m → Ω × (Ω → ℝ) ↦
            ∑ β, g β * ∏ i : Fin m, match β i with
              | none => 1 | some l => ρ' * hybridVec E ig' z' i l) := fun ρ' g ↦
        Finset.measurable_sum _ fun β _ ↦ measurable_const.mul
          (Finset.measurable_prod _ fun i _ ↦ by
            cases β i with
            | none => fun_prop
            | some l =>
              unfold hybridVec; cases ig' i
              · simp only [Bool.false_eq_true, ↓reduceIte]
                have h1 : Measurable (fun z' : Fin m → Ω × (Ω → ℝ) ↦ (z' i).1) :=
                  measurable_fst.comp (measurable_pi_apply i)
                exact measurable_const.mul ((measurable_pi_apply l).comp (hX_meas.comp h1))
              · simp only [↓reduceIte]; unfold gaussBlock; fun_prop)
      have hF_meas : Measurable (Function.uncurry F) := by
        change Measurable (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦ F p.1 p.2)
        refine ((hpoly_meas ρ f0).comp measurable_snd).add (Finset.measurable_sum _ fun j _ ↦
          ((hpoly_meas ρ (fj j)).comp measurable_snd).mul ?_)
        cases ig 0
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact (measurable_pi_apply j).comp (hX_meas.comp (measurable_fst.comp measurable_fst))
        · simp only [↓reduceIte]; unfold gaussBlock; fun_prop
      have hsingle : ∀ z' : Fin m → Ω × (Ω → ℝ),
          ∫ z0, (A ρ z' + ρ * ∑ j, B ρ z' j *
            (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j) ^ 4 ∂blockSpaceMeasure E ≤
          (∫ z0, (F z0 z') ^ 2 ∂blockSpaceMeasure E) ^ 2 := by
        intro z'
        cases hig0 : ig 0
        · simp only [F, hig0, Bool.false_eq_true, ↓reduceIte, blockSpaceMeasure]
          have h1 : ∀ (G : Ω → ℝ),
              ∫ z0 : Ω × (Ω → ℝ), G z0.1 ∂(E.μ.toMeasure.prod (stdGaussPi Ω)) =
              ∑ ω : Ω, (E.μ ω).toReal * G ω := fun G ↦ by
            rw [integral_fun_fst (f := G), probReal_univ, one_smul, integral_pmf_toMeasure]
          rw [h1 (fun ω ↦ (A ρ z' + ρ * ∑ j, B ρ z' j * E.X ω j) ^ 4),
              h1 (fun ω ↦ (A ρ z' + ∑ j, B ρ z' j * E.X ω j) ^ 2)]
          exact discreteBlock_hypercontractivity_2_4 E (A ρ z') (B ρ z')
        · simp only [F, hig0, ↓reduceIte, blockSpaceMeasure]
          have h1 : ∀ (G : (Ω → ℝ) → ℝ),
              ∫ z0 : Ω × (Ω → ℝ), G z0.2 ∂(E.μ.toMeasure.prod (stdGaussPi Ω)) =
              ∫ g, G g ∂stdGaussPi Ω := fun G ↦ by rw [integral_fun_snd]; simp
          rw [h1 (fun g ↦ (A ρ z' + ρ * ∑ j, B ρ z' j * gaussBlock E g j) ^ 4),
              h1 (fun g ↦ (A ρ z' + ∑ j, B ρ z' j * gaussBlock E g j) ^ 2)]
          exact gaussBlock_hypercontractivity_2_4 E hρ_sq (A ρ z') (B ρ z')
      let lhsFn (p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ))) : ℝ :=
        (A ρ p.2 + ρ * ∑ j, B ρ p.2 j * (if ig 0 then gaussBlock E p.1.2 else E.X p.1.1) j) ^ 4
      have hlhs_eq : ∫ z, (∑ α, f α * ∏ i : Fin (m + 1), match α i with
            | none => 1 | some j => ρ * hybridVec E ig z i j) ^ 4 ∂hybridProductMeasure E =
          ∫ p, lhsFn p ∂((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) := by
        rw [← hmp.integral_comp e.measurableEmbedding lhsFn]
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        simp only [lhsFn, e, MeasurableEquiv.piFinSuccAbove_apply, hybridVec]
        exact congr_arg (· ^ 4) (hsplit ρ z)
      have hlhs_int : Integrable lhsFn
          ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) := by
        have h1 := integrable_hybrid_poly_pow E ig f ρ 4
        have h2 : lhsFn ∘ e = fun z ↦ (∑ α, f α * ∏ i : Fin (m + 1), match α i with
            | none => 1 | some j => ρ * hybridVec E ig z i j) ^ 4 := by
          funext z
          simp only [Function.comp_apply, lhsFn, e, MeasurableEquiv.piFinSuccAbove_apply, hybridVec]
          exact congr_arg (· ^ 4) (hsplit ρ z).symm
        exact (hmp.integrable_comp_emb e.measurableEmbedding).mp (h2.symm ▸ h1)
      have hF4_int : Integrable (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦ (F p.1 p.2) ^ 4)
          ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) := by
        have hmp_snd' : MeasurePreserving
            (Prod.snd : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) → Fin m → Ω × (Ω → ℝ))
            ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E))
            (hybridProductMeasure (n := m) E) :=
          ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
        have hmp_snd0 : MeasurePreserving (Prod.snd : Ω × (Ω → ℝ) → Ω → ℝ)
            (E.μ.toMeasure.prod (stdGaussPi Ω)) (stdGaussPi Ω) :=
          ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
        have hA4 : Integrable (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦ (A ρ p.2) ^ 4)
            ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) := by
          have h0 := memLp_one_iff_integrable.mpr (integrable_hybrid_poly_pow E ig' f0 ρ 4)
          exact memLp_one_iff_integrable.mp (h0.comp_measurePreserving hmp_snd')
        have hBj : ∀ j : Fin q,
            Integrable (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦
              (B ρ p.2 j) ^ 4 * ((if ig 0 then gaussBlock E p.1.2 else E.X p.1.1) j) ^ 4)
            ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) := fun j ↦ by
          have h1 := integrable_hybrid_poly_pow E ig' (fj j) ρ 4
          have h2 : Integrable (fun z0 : Ω × (Ω → ℝ) ↦
              ((if ig 0 then gaussBlock E z0.2 else E.X z0.1) j) ^ 4) (blockSpaceMeasure E) := by
            cases hig0 : ig 0
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hm0 : Measurable (fun z0 : Ω × (Ω → ℝ) ↦ E.X z0.1 j ^ 4) :=
                ((measurable_pi_apply j).comp (hX_meas.comp measurable_fst)).pow_const 4
              exact Integrable.of_bound hm0.aestronglyMeasurable
                ((∑ ω : Ω, |E.X ω j|) ^ 4) (ae_of_all _ fun z0 ↦ by
                  rw [Real.norm_of_nonneg (by positivity)]
                  have hle := Finset.single_le_sum (f := fun ω ↦ |E.X ω j|)
                    (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ z0.1)
                  have hsq : |E.X z0.1 j| ^ 4 = (E.X z0.1 j) ^ 4 := by
                    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
                  rw [← hsq]; exact pow_le_pow_left₀ (abs_nonneg _) hle 4)
            · simp only [↓reduceIte, blockSpaceMeasure]
              have hm := (gaussBlock_memLp E j (p := 4) (by simp)).comp_measurePreserving hmp_snd0
              exact (hm.integrable_norm_pow (by decide)).mono' (by unfold gaussBlock; fun_prop)
                (ae_of_all _ fun z0 ↦ by simp)
          exact (h2.mul_prod h1).congr (ae_of_all _ fun p ↦ mul_comm _ _)
        have hdom : Integrable (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦
            ((q + 1 : ℝ) ^ 3) * ((A ρ p.2) ^ 4 +
              ∑ j, (B ρ p.2 j) ^ 4 * ((if ig 0 then gaussBlock E p.1.2 else E.X p.1.1) j) ^ 4))
            ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) :=
          (hA4.add (integrable_finsetSum _ fun j _ ↦ hBj j)).const_mul _
        refine hdom.mono' ((hF_meas.pow_const 4).aestronglyMeasurable) (ae_of_all _ fun p ↦ ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        let a := A ρ p.2
        let b : Fin q → ℝ := fun j ↦ B ρ p.2 j * (if ig 0 then gaussBlock E p.1.2 else E.X p.1.1) j
        have hcs1 : (a + ∑ j, b j) ^ 2 ≤ (q + 1 : ℝ) * (a ^ 2 + ∑ j, (b j) ^ 2) := by
          rcases q.eq_zero_or_pos with rfl | hq
          · simp
          · have hsum_sq : (∑ j : Fin q, b j) ^ 2 ≤ (q : ℝ) * ∑ j : Fin q, (b j) ^ 2 := by
              simpa [Finset.card_fin] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
            have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
            have hmul : 0 ≤
              (q : ℝ) * ((q + 1 : ℝ) * (a ^ 2 + ∑ j, (b j) ^ 2) - (a + ∑ j, b j) ^ 2) := by
              nlinarith [sq_nonneg ((q : ℝ) * a - ∑ j, b j), hsum_sq]
            nlinarith
        have hcs2 : (a ^ 2 + ∑ j, (b j) ^ 2) ^ 2 ≤ (q + 1 : ℝ) * (a ^ 4 + ∑ j, (b j) ^ 4) := by
          rcases q.eq_zero_or_pos with rfl | hq
          · simp; ring_nf; exact le_rfl
          · have hsum_sq : (∑ j : Fin q, (b j) ^ 2) ^ 2 ≤ (q : ℝ) * ∑ j : Fin q, (b j) ^ 4 := by
              have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j ↦ (b j) ^ 2)
              simp only [Finset.card_univ, Fintype.card_fin, ← pow_mul] at h0; exact h0
            have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
            have hmul : 0 ≤ (q : ℝ) * ((q + 1 : ℝ) * (a ^ 4 + ∑ j, (b j) ^ 4) -
                (a ^ 2 + ∑ j, (b j) ^ 2) ^ 2) := by
              nlinarith [sq_nonneg ((q : ℝ) * a ^ 2 - ∑ j, (b j) ^ 2), hsum_sq]
            nlinarith
        have h4 : (a + ∑ j, b j) ^ 4 ≤ (q + 1 : ℝ) ^ 3 * (a ^ 4 + ∑ j, (b j) ^ 4) := by
          have := pow_le_pow_left₀ (sq_nonneg _) hcs1 2
          have := mul_le_mul_of_nonneg_left hcs2 (show 0 ≤ (q + 1 : ℝ) ^ 2 by positivity)
          nlinarith
        simpa [F, a, b, mul_pow] using h4
      have hmid_int : Integrable (fun z' ↦ (∫ z0, (F z0 z') ^ 2 ∂blockSpaceMeasure E) ^ 2)
          (hybridProductMeasure (n := m) E) := by
        have hF2 : Integrable (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦ (F p.1 p.2) ^ 2)
            ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) := by
          refine ((integrable_const (1 : ℝ)).add hF4_int).mono'
            ((hF_meas.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun p ↦ ?_)
          rw [Real.norm_of_nonneg (sq_nonneg _)]; simp only [Pi.add_apply]
          have h4 : (F p.1 p.2) ^ 4 = ((F p.1 p.2) ^ 2) ^ 2 := by ring
          rw [h4]; nlinarith [sq_nonneg ((F p.1 p.2) ^ 2 - 1)]
        have hle_z' : ∀ᵐ z' ∂hybridProductMeasure (n := m) E,
            (∫ z0, (F z0 z') ^ 2 ∂blockSpaceMeasure E) ^ 2 ≤
            ∫ z0, (F z0 z') ^ 4 ∂blockSpaceMeasure E := by
          filter_upwards [hF4_int.prod_left_ae] with z' hz'
          have h1 : Integrable (fun z0 ↦ (F z0 z') ^ 2) (blockSpaceMeasure E) := by
            have hm1 := (hF_meas.comp (measurable_id.prodMk (measurable_const (a := z')))).pow_const
              2
            refine ((integrable_const (1 : ℝ)).add hz').mono' hm1.aestronglyMeasurable
              (ae_of_all _ fun z0 ↦ ?_)
            rw [Real.norm_of_nonneg (sq_nonneg _), Pi.add_apply,
              show (F z0 z') ^ 4 = ((F z0 z') ^ 2) ^ 2 by ring]
            nlinarith [sq_nonneg ((F z0 z') ^ 2 - 1)]
          have hvar : 0 ≤ ∫ z0, ((F z0 z') ^ 2 - ∫ w, (F w z') ^ 2 ∂blockSpaceMeasure E) ^ 2
              ∂blockSpaceMeasure E := integral_nonneg fun _ ↦ sq_nonneg _
          simp_rw [show ∀ z0, ((F z0 z') ^ 2 - ∫ w, (F w z') ^ 2 ∂blockSpaceMeasure E) ^ 2 =
              ((F z0 z') ^ 4 - 2 * (∫ w, (F w z') ^ 2 ∂blockSpaceMeasure E) * (F z0 z') ^ 2) +
              (∫ w, (F w z') ^ 2 ∂blockSpaceMeasure E) ^ 2 from fun _ ↦ by ring] at hvar
          have hsub : Integrable (fun z0 ↦ (F z0 z') ^ 4 -
              2 * (∫ w, (F w z') ^ 2 ∂blockSpaceMeasure E) * (F z0 z') ^ 2) (blockSpaceMeasure E) :=
            hz'.sub (h1.const_mul _)
          rw [integral_add hsub (integrable_const _), integral_sub hz' (h1.const_mul _),
            integral_const_mul, integral_const, probReal_univ, one_smul] at hvar
          linarith
        refine hF4_int.integral_prod_right.mono'
          ((hF2.aestronglyMeasurable.prod_swap).integral_prod_right'.pow 2)
          (hle_z'.mono fun z' hz' ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hz')
      have hstep1 : ∫ p, lhsFn p ∂((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) ≤
          ∫ z', (∫ z0, (F z0 z') ^ 2 ∂blockSpaceMeasure E) ^ 2
            ∂hybridProductMeasure (n := m) E := by
        rw [integral_prod _ hlhs_int, integral_integral_swap hlhs_int]
        exact integral_mono (hlhs_int.integral_prod_right) hmid_int hsingle
      have hstep2 := fubini_l2_minkowski hF_meas hF4_int
      have hstep3 : ∫ z0, Real.sqrt (∫ z', (F z0 z') ^ 4 ∂hybridProductMeasure (n := m) E)
          ∂blockSpaceMeasure E ≤
          ∫ z0, ∫ z', (A 1 z' + ∑ j, B 1 z' j *
            (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j) ^ 2 ∂hybridProductMeasure (n := m) E
          ∂blockSpaceMeasure E := by
        refine integral_mono ?_ ?_ fun z0 ↦ ?_
        · refine ((integrable_const (1 : ℝ)).add hF4_int.integral_prod_left).mono'
            (Real.continuous_sqrt.comp_aestronglyMeasurable
              hF4_int.aestronglyMeasurable.integral_prod_right') (ae_of_all _ fun z0 ↦ ?_)
          rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
          let s := Real.sqrt (∫ z', (F z0 z') ^ 4 ∂hybridProductMeasure (n := m) E)
          have hs : s ^ 2 = ∫ z', (F z0 z') ^ 4 ∂hybridProductMeasure (n := m) E :=
            Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)
          dsimp only; change s ≤ 1 + ∫ z', (F z0 z') ^ 4 ∂hybridProductMeasure (n := m) E
          nlinarith [sq_nonneg (s - 1)]
        · have h2 := integrable_hybrid_poly_pow E ig f 1 2
          have heq2 : (fun p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ)) ↦
              (A 1 p.2 + ∑ j,
                B 1 p.2 j * (if ig 0 then gaussBlock E p.1.2 else E.X p.1.1) j) ^ 2) ∘ e =
              fun z ↦ (∑ α, f α * ∏ i : Fin (m + 1), match α i with
                | none => 1 | some j => 1 * hybridVec E ig z i j) ^ 2 := by
            funext z; have hsp := hsplit 1 z; simp only [one_mul] at hsp
            simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_apply,
              Fin.insertNthEquiv_symm_apply, Fin.removeNth_zero, one_mul]
            exact congr_arg (· ^ 2) (by rw [hsp]; rfl)
          exact ((hmp.integrable_comp_emb e.measurableEmbedding).mp
            (heq2.symm ▸ h2)).integral_prod_left
        · let u0 (j : Fin q) : ℝ := (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j
          let f_z0 : (Fin m → Option (Fin q)) → ℝ := fun β ↦ f0 β + ∑ j, fj j β * u0 j
          have hlin_eq : ∀ (ρ' : ℝ) (z' : Fin m → Ω × (Ω → ℝ)),
              A ρ' z' + ∑ j, B ρ' z' j * u0 j =
              ∑ β, f_z0 β * ∏ i : Fin m, match β i with
                | none => 1 | some l => ρ' * hybridVec E ig' z' i l := fun ρ' z' ↦ by
            simp only [A, B, f_z0, u0, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
            congr 1; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun β _ ↦ by ring
          have hF_eq : ∀ z', F z0 z' = ∑ β, f_z0 β * ∏ i : Fin m, match β i with
              | none => 1 | some l => ρ * hybridVec E ig' z' i l := hlin_eq ρ
          have h1_eq : ∀ z', A 1 z' + ∑ j, B 1 z' j *
              (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j =
              ∑ β, f_z0 β * ∏ i : Fin m, match β i with
                | none => 1 | some l => hybridVec E ig' z' i l := fun z' ↦ by
            simpa only [one_mul] using hlin_eq 1 z'
          simp_rw [hF_eq, h1_eq]
          exact Real.sqrt_le_iff.mpr ⟨integral_nonneg fun _ ↦ sq_nonneg _, ih ig' f_z0⟩
      have hrhs_eq : ∫ z0, ∫ z', (A 1 z' + ∑ j, B 1 z' j *
            (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j) ^ 2 ∂hybridProductMeasure (n := m) E
          ∂blockSpaceMeasure E =
          ∫ z, (∑ α, f α * ∏ i : Fin (m + 1), match α i with
            | none => 1 | some j => hybridVec E ig z i j) ^ 2 ∂hybridProductMeasure E := by
        have h2 := integrable_hybrid_poly_pow E ig f 1 2
        let rhsFn (p : (Ω × (Ω → ℝ)) × (Fin m → Ω × (Ω → ℝ))) : ℝ :=
          (A 1 p.2 + ∑ j, B 1 p.2 j * (if ig 0 then gaussBlock E p.1.2 else E.X p.1.1) j) ^ 2
        have heq2 : rhsFn ∘ e = fun z ↦ (∑ α, f α * ∏ i : Fin (m + 1), match α i with
            | none => 1 | some j => 1 * hybridVec E ig z i j) ^ 2 := by
          funext z
          have hsp := hsplit 1 z; simp only [one_mul] at hsp
          simp only [Function.comp_apply, rhsFn, e, MeasurableEquiv.piFinSuccAbove_apply,
            Fin.insertNthEquiv_symm_apply, Fin.removeNth_zero, one_mul]
          exact congr_arg (· ^ 2) (by rw [hsp]; rfl)
        have hrhs_int : Integrable rhsFn
            ((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E)) :=
          (hmp.integrable_comp_emb e.measurableEmbedding).mp (heq2.symm ▸ h2)
        rw [← integral_prod rhsFn hrhs_int, ← hmp.integral_comp e.measurableEmbedding rhsFn]
        simpa [one_mul] using congr_arg (fun g ↦ ∫ z, g z ∂hybridProductMeasure E) heq2
      rw [hlhs_eq]
      calc ∫ p, lhsFn p ∂((blockSpaceMeasure E).prod (hybridProductMeasure (n := m) E))
          ≤ ∫ z', (∫ z0, (F z0 z') ^ 2 ∂blockSpaceMeasure E) ^ 2
              ∂hybridProductMeasure (n := m) E := hstep1
        _ ≤ (∫ z0, Real.sqrt (∫ z', (F z0 z') ^ 4 ∂hybridProductMeasure (n := m) E)
              ∂blockSpaceMeasure E) ^ 2 := hstep2
        _ ≤ (∫ z0, ∫ z', (A 1 z' + ∑ j, B 1 z' j *
              (if ig 0 then gaussBlock E z0.2 else E.X z0.1) j) ^ 2
              ∂hybridProductMeasure (n := m) E ∂blockSpaceMeasure E) ^ 2 :=
            pow_le_pow_left₀ (integral_nonneg fun _ ↦ Real.sqrt_nonneg _) hstep3 2
        _ = (∫ z, (∑ α, f α * ∏ i : Fin (m + 1), match α i with
              | none => 1 | some j => hybridVec E ig z i j) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
            rw [hrhs_eq]
  -- Step 2: Decompose `M` by homogeneous degree `r = 0, ..., d` and combine via `hTrho`.
  let fr (r : ℕ) : (Fin n → Option (Fin q)) → ℝ := fun α ↦
    if (blockSupp α).card = r then M 0 α else 0
  let evalR (r : ℕ) (z : Fin n → Ω × (Ω → ℝ)) : ℝ :=
    ∑ α, fr r α * ∏ i : Fin n, match α i with | none => 1 | some j => hybridVec E isGauss z i j
  have hsum_deg : ∀ z, M.eval (hybridVec E isGauss z) 0 =
      ∑ r ∈ Finset.range (d + 1), evalR r z := fun z ↦ by
    simp only [BlockPoly.eval, evalR, fr]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    by_cases hd : d < (blockSupp α).card
    · simp only [hdeg 0 α hd, zero_mul, ite_self, Finset.sum_const_zero]
    · rw [Finset.sum_eq_single (blockSupp α).card]
      · simp
      · intro r _ hr; simp [Ne.symm hr]
      · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim
  have hevalR_Trho : ∀ r ∈ Finset.range (d + 1), ∀ z,
      evalR r z = ρ ^ (-(r : ℤ)) * (∑ α, fr r α * ∏ i : Fin n, match α i with
        | none => 1 | some j => ρ * hybridVec E isGauss z i j) := fun r _ z ↦ by
    simp only [evalR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    by_cases hr : (blockSupp α).card = r
    · have hprod : (∏ i : Fin n, match α i with
          | none => 1 | some j => ρ * hybridVec E isGauss z i j) =
          ρ ^ (blockSupp α).card * ∏ i : Fin n, match α i with
            | none => 1 | some j => hybridVec E isGauss z i j := by
        have h1 : ∀ i : Fin n,
            (match α i with | none => (1 : ℝ) | some j => ρ * hybridVec E isGauss z i j) =
            (if (α i).isSome then ρ else 1) *
              (match α i with | none => (1 : ℝ) | some j => hybridVec E isGauss z i j) := fun i ↦ by
          cases α i <;> simp
        simp_rw [h1]; rw [Finset.prod_mul_distrib]; congr 1; simp [blockSupp, Finset.prod_ite]
      rw [hprod, hr, zpow_neg, zpow_natCast]; field_simp [pow_ne_zero r hρ_pos.ne']
    · simp [fr, hr]
  have hl2_decomp : ∫ z, (M.eval (hybridVec E isGauss z) 0) ^ 2 ∂hybridProductMeasure E =
      ∑ r ∈ Finset.range (d + 1), ∫ z, (evalR r z) ^ 2 ∂hybridProductMeasure E := by
    dsimp only [BlockPoly.eval]
    rw [hybrid_poly_l2_eq]
    have hsplit_r : ∀ r ∈ Finset.range (d + 1),
        ∫ z, (evalR r z) ^ 2 ∂hybridProductMeasure E =
        ∑ α ∈ Finset.univ.filter (fun α : Fin n → Option (Fin q) ↦ (blockSupp α).card = r),
          ∑ β ∈ Finset.univ.filter (fun β ↦ blockSupp β = blockSupp α),
            M 0 α * M 0 β * ∏ i : Fin n, match α i, β i with
              | some j, some l => ∑ ω, (E.μ ω).toReal * E.X ω j * E.X ω l | _, _ => 1 := by
      intro r _; dsimp only [evalR]; rw [hybrid_poly_l2_eq]
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun α ↦ (blockSupp α).card = r),
        Finset.sum_eq_zero (s := Finset.univ.filter (fun α ↦ ¬ (blockSupp α).card = r))
          (fun α hα ↦ Finset.sum_eq_zero fun β _ ↦ by simp [fr, (Finset.mem_filter.mp hα).2]),
        add_zero]
      refine Finset.sum_congr rfl fun α hα ↦ Finset.sum_congr rfl fun β hβ ↦ ?_
      have hαr : (blockSupp α).card = r := (Finset.mem_filter.mp hα).2
      have hβr : (blockSupp β).card = r := by rw [(Finset.mem_filter.mp hβ).2, hαr]
      simp only [fr, hαr, hβr, ↓reduceIte]; rfl
    rw [Finset.sum_congr rfl hsplit_r]
    let g_term (α : Fin n → Option (Fin q)) : ℝ :=
      ∑ β ∈ Finset.univ.filter (fun β ↦ blockSupp β = blockSupp α), M 0 α * M 0 β *
        ∏ i : Fin n, match α i, β i with
          | some j, some l => ∑ ω, (E.μ ω).toReal * E.X ω j * E.X ω l | _, _ => 1
    change ∑ α, g_term α =
      ∑ r ∈ Finset.range (d + 1), ∑ α ∈ Finset.univ.filter (fun α ↦ (blockSupp α).card = r),
        g_term α
    simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    by_cases hd : d < (blockSupp α).card
    · rw [show g_term α = 0 from Finset.sum_eq_zero fun β _ ↦ by simp [hdeg 0 α hd]]
      exact (Finset.sum_eq_zero fun r hr ↦ by
        simp [show (blockSupp α).card ≠ r by have := Finset.mem_range.mp hr; omega]).symm
    · rw [Finset.sum_eq_single (blockSupp α).card]
      · simp
      · intro r _ hr; simp [Ne.symm hr]
      · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim
  have h4_sum : ∫ z, (M.eval (hybridVec E isGauss z) 0) ^ 4 ∂hybridProductMeasure E ≤
      ((d + 1 : ℝ) ^ 3) * ∑ r ∈ Finset.range (d + 1),
        ∫ z, (evalR r z) ^ 4 ∂hybridProductMeasure E := by
    have hpt : ∀ z, (M.eval (hybridVec E isGauss z) 0) ^ 4 ≤
        ((d + 1 : ℝ) ^ 3) * ∑ r ∈ Finset.range (d + 1), (evalR r z) ^ 4 := fun z ↦ by
      rw [hsum_deg z]
      have hcs1 : (∑ r ∈ Finset.range (d + 1), evalR r z) ^ 2 ≤
          (d + 1 : ℝ) * ∑ r ∈ Finset.range (d + 1), (evalR r z) ^ 2 := by
        simpa [Finset.card_range, Nat.cast_add, Nat.cast_one] using
          sq_sum_le_card_mul_sum_sq (s := Finset.range (d + 1)) (f := fun r ↦ evalR r z)
      have hcs2 : (∑ r ∈ Finset.range (d + 1), (evalR r z) ^ 2) ^ 2 ≤
          (d + 1 : ℝ) * ∑ r ∈ Finset.range (d + 1), (evalR r z) ^ 4 := by
        have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.range (d + 1)) (f :=
          fun r ↦ (evalR r z) ^ 2)
        simp only [Finset.card_range, Nat.cast_add, Nat.cast_one, ← pow_mul] at h0; exact h0
      have := pow_le_pow_left₀ (sq_nonneg _) hcs1 2
      have := mul_le_mul_of_nonneg_left hcs2 (show 0 ≤ (d + 1 : ℝ) ^ 2 by positivity)
      nlinarith
    have hevalR_int (r : ℕ) : Integrable (fun z ↦ (evalR r z) ^ 4) (hybridProductMeasure E) := by
      simpa [evalR] using integrable_hybrid_poly_pow E isGauss (fr r) 1 4
    have hM_int : Integrable (fun z ↦ (M.eval (hybridVec E isGauss z) 0) ^ 4)
        (hybridProductMeasure E) := by
      simpa [BlockPoly.eval] using integrable_hybrid_poly_pow E isGauss (M 0) 1 4
    rw [← integral_finsetSum _ fun r _ ↦ hevalR_int r, ← integral_const_mul]
    exact integral_mono hM_int ((integrable_finsetSum _ fun r _ ↦ hevalR_int r).const_mul _) hpt
  calc ∫ z, (M.eval (hybridVec E isGauss z) 0) ^ 4 ∂hybridProductMeasure E
      ≤ ((d + 1 : ℝ) ^ 3) * ∑ r ∈ Finset.range (d + 1),
          ∫ z, (evalR r z) ^ 4 ∂hybridProductMeasure E := h4_sum
    _ ≤ ((d + 1 : ℝ) ^ 3) * ∑ r ∈ Finset.range (d + 1),
          (1 / ρ ^ (4 * d)) * (∫ z, (evalR r z) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r hr ↦ ?_) (by positivity)
        have hrd : r ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        have hstep_r : ∫ z, (evalR r z) ^ 4 ∂hybridProductMeasure E =
            (ρ ^ (-(r : ℤ))) ^ 4 * ∫ z, (∑ α, fr r α * ∏ i : Fin n, match α i with
              | none => 1 | some j => ρ * hybridVec E isGauss z i j) ^ 4
              ∂hybridProductMeasure E := by
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun z ↦ by dsimp only; rw [hevalR_Trho r hr z,
            mul_pow])
        rw [hstep_r]
        have hpow_le : (ρ ^ (-(r : ℤ))) ^ 4 ≤ 1 / ρ ^ (4 * d) := by
          rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul, one_div]
          exact inv_anti₀ (pow_pos hρ_pos _)
            (pow_le_pow_of_le_one hρ_pos.le hρ_le_one (by omega : r * 4 ≤ 4 * d))
        exact mul_le_mul hpow_le (hTrho n isGauss (fr r))
          (integral_nonneg fun _ ↦ by positivity) (by positivity)
    _ = ((d + 1 : ℝ) ^ 3 / ρ ^ (4 * d)) *
          ∑ r ∈ Finset.range (d + 1), (∫ z, (evalR r z) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
        rw [← Finset.mul_sum (a := 1 / ρ ^ (4 * d))]; ring
    _ ≤ ((d + 1 : ℝ) ^ 3 / ρ ^ (4 * d)) *
          (∑ r ∈ Finset.range (d + 1), ∫ z, (evalR r z) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦
          integral_nonneg fun _ ↦ sq_nonneg _) (by positivity)
    _ = ((d + 1 : ℝ) ^ 3 / ρ ^ (4 * d)) *
          (∫ z, (M.eval (hybridVec E isGauss z) 0) ^ 2 ∂hybridProductMeasure E) ^ 2 := by
        rw [hl2_decomp]

/-- Second-order multivariate Taylor remainder bound along a line `s ↦ Ψ (Z + s • Δ)` for `C³`
test functions `Ψ : (Fin k → ℝ) → ℝ` with `‖iteratedFDeriv ℝ 3 Ψ u‖ ≤ C`. -/
theorem taylor_third_order_multivariate {k : ℕ} {Ψ : (Fin k → ℝ) → ℝ} (hΨ : ContDiff ℝ 3 Ψ)
    {C : ℝ} (hC : ∀ u, ‖iteratedFDeriv ℝ 3 Ψ u‖ ≤ C) (Z Δ : Fin k → ℝ) :
    |Ψ (Z + Δ) - (Ψ Z + fderiv ℝ Ψ Z Δ +
      (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 Ψ Z ![Δ, Δ])| ≤
    C * ‖Δ‖ ^ 3 / 6 := by
  let L : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) Δ
  let g : ℝ → ℝ := fun s ↦ Ψ (Z + s • Δ)
  have hg_eq : g = Ψ ∘ (fun s ↦ Z + L s) := by funext s; simp [g, L]
  have hg_cd : ContDiff ℝ 3 g := hΨ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hiter : ∀ (j : ℕ) (s : ℝ), j ≤ 3 →
      iteratedDeriv j g s = iteratedFDeriv ℝ j Ψ (Z + s • Δ) (fun _ : Fin j ↦ Δ) := fun j s hj ↦ by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have hcomp : iteratedFDeriv ℝ j (fun t ↦ Ψ (Z + L t)) s =
        (iteratedFDeriv ℝ j Ψ (Z + L s)).compContinuousLinearMap (fun _ ↦ L) := by
      change iteratedFDeriv ℝ j ((Ψ ∘ fun x ↦ Z + id x) ∘ L) s = _
      rw [L.iteratedFDeriv_comp_right (hΨ.comp (contDiff_const.add contDiff_id)) s
        (by exact_mod_cast hj)]
      congr 1; exact iteratedFDeriv_comp_add_left (f := Ψ) j Z (L s)
    rw [hg_eq]
    change iteratedFDeriv ℝ j (fun t ↦ Ψ (Z + L t)) s (fun _ ↦ 1) = _
    rw [hcomp]; simp [L]
  have hg3 : ∀ s, |iteratedDeriv 3 g s| ≤ C * ‖Δ‖ ^ 3 := fun s ↦ by
    rw [hiter 3 s le_rfl, ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 3 Ψ (Z + s • Δ) (fun _ : Fin 3 ↦ Δ)‖
        ≤ ‖iteratedFDeriv ℝ 3 Ψ (Z + s • Δ)‖ * ∏ _i : Fin 3, ‖Δ‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C * ‖Δ‖ ^ 3 := by
          simpa using mul_le_mul_of_nonneg_right (hC (Z + s • Δ)) (pow_nonneg (norm_nonneg Δ) 3)
  have htay := abs_sub_sum_iteratedDeriv_le (n := 2) hg_cd hg3 0 1
  simp only [zero_add, one_pow, mul_one, abs_one, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
    div_one] at htay
  have h0 : iteratedDeriv 0 g 0 = Ψ Z := by simp [g]
  have h1 : iteratedDeriv 1 g 0 = fderiv ℝ Ψ Z Δ := by
    rw [hiter 1 0 (by omega), zero_smul, add_zero, iteratedFDeriv_one_apply]
  have h2 : iteratedDeriv 2 g 0 = iteratedFDeriv ℝ 2 Ψ Z ![Δ, Δ] := by
    rw [hiter 2 0 (by omega), zero_smul, add_zero]; congr 1; funext i; fin_cases i <;> rfl
  rw [h0, h1, h2, show ((3 : ℕ).factorial : ℝ) = 6 by norm_num] at htay
  simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htay

end HybridInvariance

end CslibFrontier.Analysis.Fourier
