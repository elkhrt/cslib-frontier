module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import CslibFrontier.Foundations.Probability.Gaussian.Correlated
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Central

/-!
# Grothendieck's Inequality and Krivine Rounding

This module develops the finite-matrix theory of the real Grothendieck constant $K_G$ under
standard Lean axioms. For a finite real matrix $A \in \mathbb{R}^{\mu \times \nu}$, we define the
$\ell_\infty \to \ell_1$ bilinear sign norm `optNorm A` and its semidefinite vector relaxation
`sdpNorm A`, establish dimension-independent Hilbert-space and tensor-power bounds for `sdpNorm A`,
prove the power-series expansion of `Real.arcsin` on `[-1, 1]`, and deduce Krivine's upper bound
$K_G \le \frac{\pi}{2 \log(1 + \sqrt{2})}$ and finiteness of $K_G$.

## Main definitions

* `CslibFrontier.Grothendieck.optNorm`: the $\ell_\infty \to \ell_1$ maximum
  $\max_{x_i, y_j \in \{-1, 1\}} \sum_{i, j} A_{i j} x_i y_j$.
* `CslibFrontier.Grothendieck.sdpNorm`: the semidefinite relaxation
  $\sup_{\|u_i\| = \|w_j\| = 1} \sum_{i, j} A_{i j} \langle u_i, w_j \rangle$.
* `CslibFrontier.Grothendieck.vecTensorPow`: finite-dimensional $k$-fold tensor power of a Euclidean
  vector.
* `CslibFrontier.Grothendieck.arcsinSeriesCoeff`: Taylor coefficients
  $\frac{\binom{2k}{k}}{4^k (2k + 1)}$ of $\arcsin$ at the origin.
* `CslibFrontier.Grothendieck.krivineConstant`: Krivine's constant
  $\frac{\pi}{2 \log(1 + \sqrt{2})}$.
* `CslibFrontier.Grothendieck.grothendieckConstant`: the real Grothendieck constant $K_G$.

## Main results

* `CslibFrontier.Grothendieck.sum_inner_le_sdpNorm`: `sdpNorm A` dominates unit-vector inner-product
  bilinear forms in arbitrary real inner product spaces.
* `CslibFrontier.Grothendieck.abs_sum_pow_inner_le_sdpNorm`: tensor-power bound
  $|\sum_{i, j} A_{i j} \langle u_i, w_j \rangle^k| \le \mathrm{sdpNorm}(A)$ for $k \ge 1$.
* `CslibFrontier.Grothendieck.hasSum_arcsin`: power series expansion
  $\sum_{k=0}^\infty \frac{\binom{2k}{k}}{4^k (2k + 1)} t^{2k + 1} = \arcsin t$ for $|t| \le 1$.
* `CslibFrontier.Grothendieck.integral_stdGaussian_sign_mul_sign`: Sheppard's formula for $\pm 1$
  hyperplane signs under `stdGaussian`.
* `CslibFrontier.Grothendieck.sdpNorm_le_krivineConstant_mul_optNorm` and
  `CslibFrontier.Grothendieck.grothendieckConstant_le_krivineConstant`: Krivine's upper bound
  $K_G \le \frac{\pi}{2 \log(1 + \sqrt{2})}$ and finiteness of $K_G$ (Grothendieck's inequality).
* `CslibFrontier.Grothendieck.sdpNorm_le_grothendieckConstant_mul_optNorm`: universal Grothendieck
  inequality $\mathrm{sdpNorm}(A) \le K_G \cdot \mathrm{optNorm}(A)$.
-/

public section

open scoped BigOperators InnerProductSpace Real Topology
open MeasureTheory ProbabilityTheory

namespace CslibFrontier.Grothendieck

/-! ### The $\ell_\infty \to \ell_1$ Sign Norm `optNorm` -/

private def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

private theorem boolSign_mem (b : Bool) : boolSign b ∈ ({-1, 1} : Set ℝ) := by
  cases b <;> simp [boolSign]

private theorem mem_neg_one_one_iff {r : ℝ} :
    r ∈ ({-1, 1} : Set ℝ) ↔ ∃ b : Bool, boolSign b = r := by
  constructor
  · rintro (rfl | h)
    · exact ⟨false, by simp [boolSign]⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨true, by simp [boolSign]⟩
  · rintro ⟨b, rfl⟩
    exact boolSign_mem b

private theorem neg_mem_neg_one_one {r : ℝ} (hr : r ∈ ({-1, 1} : Set ℝ)) :
    (-r) ∈ ({-1, 1} : Set ℝ) := by
  rcases hr with rfl | h
  · simp
  · rw [Set.mem_singleton_iff.mp h]
    simp

private theorem abs_eq_one_of_mem_neg_one_one {r : ℝ} (hr : r ∈ ({-1, 1} : Set ℝ)) :
    |r| = 1 := by
  rcases hr with rfl | h
  · norm_num
  · rw [Set.mem_singleton_iff.mp h]
    norm_num

private def optValSet {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) : Set ℝ :=
  {v : ℝ | ∃ (x : μ → ℝ) (y : ν → ℝ),
    (∀ i, x i ∈ ({-1, 1} : Set ℝ)) ∧ (∀ j, y j ∈ ({-1, 1} : Set ℝ)) ∧
    v = ∑ i, ∑ j, A i j * x i * y j}

private theorem optValSet_eq_image {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    optValSet A =
      (fun p : (μ → Bool) × (ν → Bool) ↦
        ∑ i, ∑ j, A i j * boolSign (p.1 i) * boolSign (p.2 j)) '' Set.univ := by
  ext v
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    choose bx hbx using fun i ↦ (mem_neg_one_one_iff.mp (hx i))
    choose by_ hby using fun j ↦ (mem_neg_one_one_iff.mp (hy j))
    refine ⟨(bx, by_), Set.mem_univ _, ?_⟩
    simp only [hbx, hby]
  · rintro ⟨⟨bx, by_⟩, -, rfl⟩
    exact ⟨fun i ↦ boolSign (bx i), fun j ↦ boolSign (by_ j),
      fun i ↦ boolSign_mem (bx i), fun j ↦ boolSign_mem (by_ j), rfl⟩

private theorem optValSet_finite {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    (optValSet A).Finite := by
  rw [optValSet_eq_image]
  exact Set.toFinite _

private theorem optValSet_nonempty {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    (optValSet A).Nonempty :=
  ⟨∑ i, ∑ j, A i j * 1 * 1, fun _ ↦ 1, fun _ ↦ 1,
    fun _ ↦ by simp, fun _ ↦ by simp, rfl⟩

/-- The $\ell_\infty \to \ell_1$ bilinear sign norm of a finite matrix `A`,
$\mathrm{OPT}(A) = \max_{x_i, y_j \in \{-1, 1\}} \sum_{i, j} A_{i j} x_i y_j$. -/
noncomputable def optNorm {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) : ℝ :=
  sSup (optValSet A)

/-- Any $\pm 1$ sign assignment bounds `optNorm A` from below. -/
theorem le_optNorm_of_signs {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ)
    {x : μ → ℝ} {y : ν → ℝ}
    (hx : ∀ i, x i ∈ ({-1, 1} : Set ℝ)) (hy : ∀ j, y j ∈ ({-1, 1} : Set ℝ)) :
    ∑ i, ∑ j, A i j * x i * y j ≤ optNorm A :=
  le_csSup (optValSet_finite A).bddAbove ⟨x, y, hx, hy, rfl⟩

/-- The absolute value of any $\pm 1$ bilinear sum is at most `optNorm A`. -/
theorem abs_sum_le_optNorm_of_signs {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ)
    {x : μ → ℝ} {y : ν → ℝ}
    (hx : ∀ i, x i ∈ ({-1, 1} : Set ℝ)) (hy : ∀ j, y j ∈ ({-1, 1} : Set ℝ)) :
    |∑ i, ∑ j, A i j * x i * y j| ≤ optNorm A := by
  refine abs_le.mpr ⟨?_, le_optNorm_of_signs A hx hy⟩
  have hneg := le_optNorm_of_signs A (fun i ↦ neg_mem_neg_one_one (hx i)) hy
  have hsum : (∑ i, ∑ j, A i j * (-x i) * y j) = -(∑ i, ∑ j, A i j * x i * y j) := by
    simp only [mul_neg, neg_mul, Finset.sum_neg_distrib]
  linarith

/-- Any bounded vectors in `[-1, 1]` have bilinear sum at most `optNorm A` by multilinear
sign rounding. -/
theorem sum_le_optNorm_of_abs_le_one {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ)
    {x : μ → ℝ} {y : ν → ℝ} (hx : ∀ i, |x i| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    ∑ i, ∑ j, A i j * x i * y j ≤ optNorm A := by
  classical
  let yStar : ν → ℝ := fun j ↦ if 0 ≤ ∑ i, A i j * x i then 1 else -1
  have hyStar : ∀ j, yStar j ∈ ({-1, 1} : Set ℝ) := by
    intro j
    dsimp only [yStar]
    split_ifs <;> simp
  have hstep1 : ∑ i, ∑ j, A i j * x i * y j ≤ ∑ i, ∑ j, A i j * x i * yStar j := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun i j ↦ A i j * x i * yStar j)]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hys : -1 ≤ y j ∧ y j ≤ 1 := abs_le.mp (hy j)
    dsimp only [yStar]
    split_ifs <;> nlinarith
  let xStar : μ → ℝ := fun i ↦ if 0 ≤ ∑ j, A i j * yStar j then 1 else -1
  have hxStar : ∀ i, xStar i ∈ ({-1, 1} : Set ℝ) := by
    intro i
    dsimp only [xStar]
    split_ifs <;> simp
  have hstep2 : ∑ i, ∑ j, A i j * x i * yStar j ≤ ∑ i, ∑ j, A i j * xStar i * yStar j := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hrew : ∀ z : ℝ, (∑ j, A i j * z * yStar j) = z * ∑ j, A i j * yStar j := fun z ↦ by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hrew (x i), hrew (xStar i)]
    have hxs : -1 ≤ x i ∧ x i ≤ 1 := abs_le.mp (hx i)
    dsimp only [xStar]
    split_ifs <;> nlinarith
  exact (hstep1.trans hstep2).trans (le_optNorm_of_signs A hxStar hyStar)

/-- Characterization of upper bounds on `optNorm A`. -/
theorem optNorm_le_iff {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) (C : ℝ) :
    optNorm A ≤ C ↔
      ∀ (x : μ → ℝ) (y : ν → ℝ),
        (∀ i, x i ∈ ({-1, 1} : Set ℝ)) → (∀ j, y j ∈ ({-1, 1} : Set ℝ)) →
        ∑ i, ∑ j, A i j * x i * y j ≤ C := by
  constructor
  · intro h x y hx hy
    exact (le_optNorm_of_signs A hx hy).trans h
  · intro h
    refine csSup_le (optValSet_nonempty A) ?_
    rintro v ⟨x, y, hx, hy, rfl⟩
    exact h x y hx hy

/-- There exist $\pm 1$ optimizer vectors attaining `optNorm A`. -/
theorem exists_signs_optNorm {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    ∃ (x : μ → ℝ) (y : ν → ℝ),
      (∀ i, x i ∈ ({-1, 1} : Set ℝ)) ∧ (∀ j, y j ∈ ({-1, 1} : Set ℝ)) ∧
      ∑ i, ∑ j, A i j * x i * y j = optNorm A := by
  have hmem : optNorm A ∈ optValSet A :=
    (optValSet_finite A).isClosed.csSup_mem (optValSet_nonempty A) (optValSet_finite A).bddAbove
  rcases hmem with ⟨x, y, hx, hy, hEq⟩
  exact ⟨x, y, hx, hy, hEq.symm⟩

/-- `optNorm A` is always nonnegative. -/
theorem optNorm_nonneg {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    0 ≤ optNorm A := by
  have h := abs_sum_le_optNorm_of_signs A (x := fun _ ↦ 1) (y := fun _ ↦ 1)
    (fun _ ↦ by simp) (fun _ ↦ by simp)
  exact (abs_nonneg _).trans h

/-- The sign norm of the zero matrix is zero. -/
@[simp]
theorem optNorm_zero {μ ν : Type*} [Fintype μ] [Fintype ν] :
    optNorm (0 : Matrix μ ν ℝ) = 0 := by
  apply le_antisymm
  · rw [optNorm_le_iff]
    intro _ _ _ _
    simp
  · exact optNorm_nonneg 0

/-- Each matrix entry is bounded in absolute value by `optNorm A`. -/
theorem abs_entry_le_optNorm {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ)
    (i₀ : μ) (j₀ : ν) : |A i₀ j₀| ≤ optNorm A := by
  classical
  have h := sum_le_optNorm_of_abs_le_one A
    (x := fun i ↦ if i = i₀ then (if 0 ≤ A i₀ j₀ then 1 else -1) else 0)
    (y := fun j ↦ if j = j₀ then 1 else 0)
    (fun i ↦ by split_ifs <;> norm_num)
    (fun j ↦ by split_ifs <;> norm_num)
  have hsum :
      (∑ i, ∑ j, A i j *
        (if i = i₀ then (if 0 ≤ A i₀ j₀ then (1 : ℝ) else -1) else 0) *
        (if j = j₀ then (1 : ℝ) else 0)) = |A i₀ j₀| := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    split_ifs with hA
    · exact (abs_of_nonneg hA).symm
    · push Not at hA
      linarith [abs_of_neg hA]
  linarith

/-- `optNorm A = 0` if and only if `A = 0`. -/
theorem optNorm_eq_zero_iff {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    optNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hij := (abs_entry_le_optNorm A i j).trans_eq h
    exact abs_nonpos_iff.mp hij
  · rintro rfl
    exact optNorm_zero

/-- `0 < optNorm A` if and only if `A ≠ 0`. -/
theorem optNorm_pos_iff {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    0 < optNorm A ↔ A ≠ 0 := by
  rw [← not_iff_not]
  push Not
  exact ⟨fun h ↦ (optNorm_eq_zero_iff A).mp (le_antisymm h (optNorm_nonneg A)),
    fun h ↦ by simp [h]⟩

/-- Scalar multiplication law for `optNorm`. -/
theorem optNorm_smul {μ ν : Type*} [Fintype μ] [Fintype ν] (c : ℝ) (A : Matrix μ ν ℝ) :
    optNorm (c • A) = |c| * optNorm A := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  apply le_antisymm
  · rw [optNorm_le_iff]
    intro x y hx hy
    have hsum : (∑ i, ∑ j, (c • A) i j * x i * y j) = c * ∑ i, ∑ j, A i j * x i * y j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsum]
    calc
      c * ∑ i, ∑ j, A i j * x i * y j ≤ |c * ∑ i, ∑ j, A i j * x i * y j| := le_abs_self _
      _ = |c| * |∑ i, ∑ j, A i j * x i * y j| := abs_mul c _
      _ ≤ |c| * optNorm A := by
        gcongr
        exact abs_sum_le_optNorm_of_signs A hx hy
  · obtain ⟨x, y, hx, hy, hxy⟩ := exists_signs_optNorm A
    by_cases hpos : 0 ≤ c
    · have h1 := le_optNorm_of_signs (c • A) hx hy
      have hsum : (∑ i, ∑ j, (c • A) i j * x i * y j) = c * optNorm A := by
        rw [← hxy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        ring
      rw [abs_of_nonneg hpos, ← hsum]
      exact h1
    · push Not at hpos
      have h1 := le_optNorm_of_signs (c • A) (fun i ↦ neg_mem_neg_one_one (hx i)) hy
      have hsum : (∑ i, ∑ j, (c • A) i j * (-x i) * y j) = (-c) * optNorm A := by
        rw [← hxy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        ring
      rw [abs_of_neg hpos, ← hsum]
      exact h1

/-- Reindexing rows and columns by equivalences preserves `optNorm`. -/
theorem optNorm_reindex {μ ν μ' ν' : Type*} [Fintype μ] [Fintype ν] [Fintype μ'] [Fintype ν']
    (e₁ : μ ≃ μ') (e₂ : ν ≃ ν') (A : Matrix μ ν ℝ) :
    optNorm (Matrix.reindex e₁ e₂ A) = optNorm A := by
  apply le_antisymm
  · rw [optNorm_le_iff]
    intro x y hx hy
    have h1 := le_optNorm_of_signs A (x := x ∘ e₁) (y := y ∘ e₂)
      (fun i ↦ hx (e₁ i)) (fun j ↦ hy (e₂ j))
    convert h1 using 1
    rw [← e₁.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← e₂.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Matrix.reindex_apply]
  · rw [optNorm_le_iff]
    intro x y hx hy
    have h1 := le_optNorm_of_signs (Matrix.reindex e₁ e₂ A)
      (x := x ∘ e₁.symm) (y := y ∘ e₂.symm)
      (fun i ↦ hx (e₁.symm i)) (fun j ↦ hy (e₂.symm j))
    convert h1 using 1
    rw [← e₁.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← e₂.symm.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Matrix.reindex_apply]

/-! ### The Semidefinite Relaxation `sdpNorm` -/

private def sdpValSet {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) : Set ℝ :=
  {v : ℝ | ∃ (u : μ → EuclideanSpace ℝ (μ ⊕ ν)) (w : ν → EuclideanSpace ℝ (μ ⊕ ν)),
    (∀ i, ‖u i‖ = 1) ∧ (∀ j, ‖w j‖ = 1) ∧
    v = ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ}

private theorem sdpValSet_nonempty {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    (sdpValSet A).Nonempty := by
  classical
  by_cases hne : Nonempty (μ ⊕ ν)
  · obtain ⟨k₀⟩ := hne
    let e₀ : EuclideanSpace ℝ (μ ⊕ ν) := EuclideanSpace.single k₀ 1
    have he₀ : ‖e₀‖ = 1 := by simp [e₀]
    exact ⟨_, fun _ ↦ e₀, fun _ ↦ e₀, fun _ ↦ he₀, fun _ ↦ he₀, rfl⟩
  · rw [not_nonempty_iff] at hne
    have hμ : IsEmpty μ := ⟨fun i ↦ hne.false (Sum.inl i)⟩
    have hν : IsEmpty ν := ⟨fun j ↦ hne.false (Sum.inr j)⟩
    exact ⟨0, isEmptyElim, isEmptyElim, fun i ↦ isEmptyElim i, fun j ↦ isEmptyElim j, by simp⟩

private theorem sdpValSet_bddAbove {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    BddAbove (sdpValSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro v ⟨u, w, hu, hw, rfl⟩
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  calc
    A i j * ⟪u i, w j⟫_ℝ ≤ |A i j * ⟪u i, w j⟫_ℝ| := le_abs_self _
    _ = |A i j| * |⟪u i, w j⟫_ℝ| := abs_mul _ _
    _ ≤ |A i j| * (‖u i‖ * ‖w j‖) := by
      gcongr
      exact abs_real_inner_le_norm (u i) (w j)
    _ = |A i j| := by rw [hu i, hw j, mul_one, mul_one]

/-- The semidefinite vector relaxation of `optNorm A`,
$\mathrm{SDP}(A) = \sup_{\|u_i\| = \|w_j\| = 1} \sum_{i, j} A_{i j} \langle u_i, w_j \rangle$
for unit vectors $u_i, w_j \in \mathbb{R}^{\mu \oplus \nu}$. -/
noncomputable def sdpNorm {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) : ℝ :=
  sSup (sdpValSet A)

/-- Unit vectors in `EuclideanSpace ℝ (μ ⊕ ν)` bound `sdpNorm A` from below. -/
theorem le_sdpNorm_of_unit_vectors {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ)
    {u : μ → EuclideanSpace ℝ (μ ⊕ ν)} {w : ν → EuclideanSpace ℝ (μ ⊕ ν)}
    (hu : ∀ i, ‖u i‖ = 1) (hw : ∀ j, ‖w j‖ = 1) :
    ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ≤ sdpNorm A :=
  le_csSup (sdpValSet_bddAbove A) ⟨u, w, hu, hw, rfl⟩

/-- Characterization of upper bounds on `sdpNorm A`. -/
theorem sdpNorm_le_iff {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) (C : ℝ) :
    sdpNorm A ≤ C ↔
      ∀ (u : μ → EuclideanSpace ℝ (μ ⊕ ν)) (w : ν → EuclideanSpace ℝ (μ ⊕ ν)),
        (∀ i, ‖u i‖ = 1) → (∀ j, ‖w j‖ = 1) →
        ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ≤ C := by
  constructor
  · intro h u w hu hw
    exact (le_sdpNorm_of_unit_vectors A hu hw).trans h
  · intro h
    refine csSup_le (sdpValSet_nonempty A) ?_
    rintro v ⟨u, w, hu, hw, rfl⟩
    exact h u w hu hw

/-- Isometric projection of a finite pair of vector families `(u, w)` in an arbitrary real inner
product space `E` into `EuclideanSpace ℝ (μ ⊕ ν)`. -/
private theorem exists_euclidean_isometry_pair {μ ν E : Type*} [Fintype μ] [Fintype ν]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : μ → E) (w : ν → E) :
    ∃ (u' : μ → EuclideanSpace ℝ (μ ⊕ ν)) (w' : ν → EuclideanSpace ℝ (μ ⊕ ν)),
      (∀ i, ‖u' i‖ = ‖u i‖) ∧ (∀ j, ‖w' j‖ = ‖w j‖) ∧
      (∀ i j, ⟪u' i, w' j⟫_ℝ = ⟪u i, w j⟫_ℝ) := by
  classical
  let f : μ ⊕ ν → E := Sum.elim u w
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range f)
  have hfin : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  have hcard : Module.finrank ℝ S ≤ Fintype.card (μ ⊕ ν) := by
    calc
      Module.finrank ℝ S ≤ (Set.range f).toFinset.card := finrank_span_le_card (Set.range f)
      _ = (Finset.univ.image f).card := by rw [Set.toFinset_range]
      _ ≤ (Finset.univ : Finset (μ ⊕ ν)).card := Finset.card_image_le
      _ = Fintype.card (μ ⊕ ν) := Finset.card_univ
  let b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S
  let embIdx : Fin (Module.finrank ℝ S) ↪ μ ⊕ ν :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin (μ ⊕ ν)).symm.toEmbedding
  let toEuc : EuclideanSpace ℝ (Fin (Module.finrank ℝ S)) → EuclideanSpace ℝ (μ ⊕ ν) :=
    fun v ↦ WithLp.toLp 2 fun k ↦
      ∑ r : Fin (Module.finrank ℝ S), if embIdx r = k then v r else 0
  have htoEuc_norm : ∀ v, ‖toEuc v‖ = ‖v‖ := by
    intro v
    have hsq : ‖toEuc v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [toEuc, Real.norm_eq_abs, sq_abs]
      have hterm : ∀ k : μ ⊕ ν,
          (∑ r : Fin (Module.finrank ℝ S), if embIdx r = k then v r else 0) ^ 2 =
            ∑ r : Fin (Module.finrank ℝ S), if embIdx r = k then (v r) ^ 2 else 0 := by
        intro k
        by_cases hk : ∃ r, embIdx r = k
        · obtain ⟨r₀, rfl⟩ := hk
          rw [Finset.sum_eq_single r₀, Finset.sum_eq_single r₀]
          · simp
          · intro r _ hr
            simp [embIdx.injective.ne hr]
          · simp
          · intro r _ hr
            simp [embIdx.injective.ne hr]
          · simp
        · push Not at hk
          simp [hk]
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      simp
    nlinarith [norm_nonneg (toEuc v), norm_nonneg v]
  let T : S →ₗᵢ[ℝ] EuclideanSpace ℝ (μ ⊕ ν) :=
    { toLinearMap :=
        { toFun := fun x ↦ toEuc (b.repr x)
          map_add' := fun x y ↦ by
            ext k
            dsimp [toEuc]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun r _ ↦ ?_
            split_ifs <;> simp
          map_smul' := fun c x ↦ by
            ext k
            dsimp [toEuc]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ ↦ ?_
            split_ifs <;> simp }
      norm_map' := fun x ↦ (htoEuc_norm (b.repr x)).trans (b.repr.norm_map x) }
  refine ⟨fun i ↦ T ⟨u i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩,
    fun j ↦ T ⟨w j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩,
    fun i ↦ T.norm_map _, fun j ↦ T.norm_map _, fun i j ↦ T.inner_map_map _ _⟩

/-- Universal Hilbert-space bound: unit vectors in *any* real inner product space `E` have
inner-product bilinear sum at most `sdpNorm A`. -/
theorem sum_inner_le_sdpNorm {μ ν E : Type*} [Fintype μ] [Fintype ν]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix μ ν ℝ) {u : μ → E} {w : ν → E}
    (hu : ∀ i, ‖u i‖ = 1) (hw : ∀ j, ‖w j‖ = 1) :
    ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ≤ sdpNorm A := by
  obtain ⟨u', w', hu', hw', hinner⟩ := exists_euclidean_isometry_pair u w
  simpa [hinner] using le_sdpNorm_of_unit_vectors A
    (fun i ↦ (hu' i).trans (hu i)) (fun j ↦ (hw' j).trans (hw j))

/-- Absolute value version of `sum_inner_le_sdpNorm`. -/
theorem abs_sum_inner_le_sdpNorm {μ ν E : Type*} [Fintype μ] [Fintype ν]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix μ ν ℝ) {u : μ → E} {w : ν → E}
    (hu : ∀ i, ‖u i‖ = 1) (hw : ∀ j, ‖w j‖ = 1) :
    |∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ| ≤ sdpNorm A := by
  refine abs_le.mpr ⟨?_, sum_inner_le_sdpNorm A hu hw⟩
  have hu' : ∀ i, ‖-u i‖ = 1 := fun i ↦ by rw [norm_neg, hu i]
  have hneg := sum_inner_le_sdpNorm A hu' hw
  have hsum : (∑ i, ∑ j, A i j * ⟪-u i, w j⟫_ℝ) = -(∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ) := by
    simp only [inner_neg_left, mul_neg, Finset.sum_neg_distrib]
  linarith

/-- The semidefinite relaxation bounds `optNorm A` from above. -/
theorem optNorm_le_sdpNorm {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    optNorm A ≤ sdpNorm A := by
  rw [optNorm_le_iff]
  intro x y hx hy
  let e₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hx_norm : ∀ i, ‖x i • e₀‖ = 1 := fun i ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_eq_one_of_mem_neg_one_one (hx i), he₀, mul_one]
  have hy_norm : ∀ j, ‖y j • e₀‖ = 1 := fun j ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_eq_one_of_mem_neg_one_one (hy j), he₀, mul_one]
  have h := sum_inner_le_sdpNorm A hx_norm hy_norm
  refine le_trans ?_ h
  refine le_of_eq ?_
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have he₀_inner : ⟪e₀, e₀⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, he₀, one_pow]
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial, he₀_inner, mul_one]
  ring

/-- `sdpNorm A` is always nonnegative. -/
theorem sdpNorm_nonneg {μ ν : Type*} [Fintype μ] [Fintype ν] (A : Matrix μ ν ℝ) :
    0 ≤ sdpNorm A :=
  (optNorm_nonneg A).trans (optNorm_le_sdpNorm A)

/-- The semidefinite norm of the zero matrix is zero. -/
@[simp]
theorem sdpNorm_zero {μ ν : Type*} [Fintype μ] [Fintype ν] :
    sdpNorm (0 : Matrix μ ν ℝ) = 0 := by
  apply le_antisymm
  · rw [sdpNorm_le_iff]
    intro _ _ _ _
    simp
  · exact sdpNorm_nonneg 0

/-- Scalar multiplication law for `sdpNorm`. -/
theorem sdpNorm_smul {μ ν : Type*} [Fintype μ] [Fintype ν] (c : ℝ) (A : Matrix μ ν ℝ) :
    sdpNorm (c • A) = |c| * sdpNorm A := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  apply le_antisymm
  · rw [sdpNorm_le_iff]
    intro u w hu hw
    have hsum : (∑ i, ∑ j, (c • A) i j * ⟪u i, w j⟫_ℝ) = c * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsum]
    calc
      c * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ≤ |c * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ| := le_abs_self _
      _ = |c| * |∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ| := abs_mul c _
      _ ≤ |c| * sdpNorm A := by
        gcongr
        exact abs_sum_inner_le_sdpNorm A hu hw
  · have hpos_abs : 0 < |c| := abs_pos.mpr hc
    rw [← le_div_iff₀' hpos_abs, sdpNorm_le_iff]
    intro u w hu hw
    rw [le_div_iff₀' hpos_abs]
    by_cases hpos : 0 ≤ c
    · rw [abs_of_nonneg hpos]
      have h1 := le_sdpNorm_of_unit_vectors (c • A) hu hw
      convert h1 using 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    · push Not at hpos
      rw [abs_of_neg hpos]
      have hu' : ∀ i, ‖-u i‖ = 1 := fun i ↦ by rw [norm_neg, hu i]
      have h1 := le_sdpNorm_of_unit_vectors (c • A) hu' hw
      convert h1 using 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Matrix.smul_apply, smul_eq_mul, inner_neg_left]
      ring

/-- Reindexing rows and columns by equivalences preserves `sdpNorm`. -/
theorem sdpNorm_reindex {μ ν μ' ν' : Type*} [Fintype μ] [Fintype ν] [Fintype μ'] [Fintype ν']
    (e₁ : μ ≃ μ') (e₂ : ν ≃ ν') (A : Matrix μ ν ℝ) :
    sdpNorm (Matrix.reindex e₁ e₂ A) = sdpNorm A := by
  apply le_antisymm
  · rw [sdpNorm_le_iff]
    intro u w hu hw
    have h1 := sum_inner_le_sdpNorm A (u := u ∘ e₁) (w := w ∘ e₂)
      (fun i ↦ hu (e₁ i)) (fun j ↦ hw (e₂ j))
    convert h1 using 1
    rw [← e₁.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← e₂.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Matrix.reindex_apply]
  · rw [sdpNorm_le_iff]
    intro u w hu hw
    have h1 := sum_inner_le_sdpNorm (Matrix.reindex e₁ e₂ A)
      (u := u ∘ e₁.symm) (w := w ∘ e₂.symm)
      (fun i ↦ hu (e₁.symm i)) (fun j ↦ hw (e₂.symm j))
    convert h1 using 1
    rw [← e₁.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← e₂.symm.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Matrix.reindex_apply]

/-- Finite-dimensional $k$-fold tensor power vector in `EuclideanSpace ℝ (Fin k → ι)`. -/
noncomputable def vecTensorPow {ι : Type*} (k : ℕ)
    (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (Fin k → ι) :=
  WithLp.toLp 2 fun α ↦ ∏ r : Fin k, v (α r)

/-- Inner product of $k$-fold tensor powers equals the $k$-th power of the inner product. -/
theorem inner_vecTensorPow {ι : Type*} [Fintype ι] (k : ℕ)
    (u v : EuclideanSpace ℝ ι) :
    ⟪vecTensorPow k u, vecTensorPow k v⟫_ℝ = ⟪u, v⟫_ℝ ^ k := by
  simp only [vecTensorPow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have hprod : ∀ α : Fin k → ι,
      (∏ r : Fin k, v (α r)) * (∏ r : Fin k, u (α r)) = ∏ r : Fin k, (u (α r) * v (α r)) := by
    intro α
    rw [mul_comm, ← Finset.prod_mul_distrib]
  simp_rw [hprod]
  symm
  calc
    ⟪u, v⟫_ℝ ^ k = (∑ s : ι, u s * v s) ^ k := by
      congr 1
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
    _ = ∏ _r : Fin k, ∑ s : ι, u s * v s := by simp
    _ = ∑ α : Fin k → ι, ∏ r : Fin k, u (α r) * v (α r) := by
      simpa using (Fintype.prod_sum (fun (_ : Fin k) (s : ι) ↦ u s * v s))

/-- The $k$-fold tensor power of a unit vector has unit norm. -/
theorem norm_vecTensorPow {ι : Type*} [Fintype ι] (k : ℕ)
    {u : EuclideanSpace ℝ ι} (hu : ‖u‖ = 1) :
    ‖vecTensorPow k u‖ = 1 := by
  have hsq : ‖vecTensorPow k u‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_vecTensorPow, real_inner_self_eq_norm_sq, hu,
      one_pow, one_pow]
  nlinarith [norm_nonneg (vecTensorPow k u)]

/-- Tensor-power bound: for unit vectors `u i`, `w j` in any real inner product space `E` and any
exponent `1 ≤ k`,
$\left|\sum_{i, j} A_{i j} \langle u_i, w_j \rangle^k\right| \le \mathrm{sdpNorm}(A)$. -/
theorem abs_sum_pow_inner_le_sdpNorm {μ ν E : Type*} [Fintype μ] [Fintype ν]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix μ ν ℝ) {u : μ → E} {w : ν → E}
    (hu : ∀ i, ‖u i‖ = 1) (hw : ∀ j, ‖w j‖ = 1) {k : ℕ} (_hk : 1 ≤ k) :
    |∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ^ k| ≤ sdpNorm A := by
  obtain ⟨u', w', hu', hw', hinner⟩ := exists_euclidean_isometry_pair u w
  have hu'' : ∀ i, ‖vecTensorPow k (u' i)‖ = 1 := fun i ↦
    norm_vecTensorPow k ((hu' i).trans (hu i))
  have hw'' : ∀ j, ‖vecTensorPow k (w' j)‖ = 1 := fun j ↦
    norm_vecTensorPow k ((hw' j).trans (hw j))
  have hinner' : ∀ i j, ⟪vecTensorPow k (u' i), vecTensorPow k (w' j)⟫_ℝ = ⟪u i, w j⟫_ℝ ^ k := by
    intro i j
    rw [inner_vecTensorPow, hinner]
  simpa [hinner'] using abs_sum_inner_le_sdpNorm A hu'' hw''

/-! ### Power Series Expansion of `Real.arcsin` on `[-1, 1]` -/

/-- The Taylor coefficient $\frac{\binom{2k}{k}}{4^k (2k + 1)}$ of $\arcsin t$ at $t^{2k + 1}$. -/
@[expose] noncomputable def arcsinSeriesCoeff (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) / ((4 : ℝ) ^ k * (2 * (k : ℝ) + 1))

/-- Leading Taylor coefficient of $\arcsin t$ equals $1$. -/
@[simp]
theorem arcsinSeriesCoeff_zero : arcsinSeriesCoeff 0 = 1 := by
  unfold arcsinSeriesCoeff
  norm_num

/-- Every Taylor coefficient of $\arcsin$ is strictly positive. -/
theorem arcsinSeriesCoeff_pos (k : ℕ) : 0 < arcsinSeriesCoeff k := by
  unfold arcsinSeriesCoeff
  have h1 : (0 : ℝ) < (Nat.choose (2 * k) k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_mul_of_pos_left k two_pos))
  positivity

private noncomputable def invSqrtBinomCoeff (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) / (4 : ℝ) ^ k

private theorem invSqrtBinomCoeff_le_one (k : ℕ) : invSqrtBinomCoeff k ≤ 1 := by
  unfold invSqrtBinomCoeff
  rw [div_le_iff₀ (by positivity), one_mul]
  exact_mod_cast Nat.centralBinom_le_four_pow k

private theorem invSqrtBinomCoeff_nonneg (k : ℕ) : 0 ≤ invSqrtBinomCoeff k := by
  unfold invSqrtBinomCoeff
  positivity

private theorem invSqrtBinomCoeff_succ (k : ℕ) :
    (2 * (k : ℝ) + 2) * invSqrtBinomCoeff (k + 1) =
      (2 * (k : ℝ) + 1) * invSqrtBinomCoeff k := by
  unfold invSqrtBinomCoeff
  have hnat := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hnat
  have hcast : ((k : ℝ) + 1) * (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.choose (2 * k) k : ℝ) := by
    exact_mod_cast hnat
  rw [pow_succ]
  field_simp
  linarith

private theorem summable_arcsinSeries_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    Summable fun k ↦ arcsinSeriesCoeff k * t ^ (2 * k + 1) := by
  refine Summable.of_norm_bounded (g := fun k ↦ |t| * (|t| ^ 2) ^ k) ?_ fun k ↦ ?_
  · exact (summable_geometric_of_lt_one (by positivity)
      (by nlinarith [abs_nonneg t])).mul_left |t|
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (arcsinSeriesCoeff_pos k), abs_pow]
    have hcoeff : arcsinSeriesCoeff k ≤ 1 := by
      calc
        arcsinSeriesCoeff k ≤ invSqrtBinomCoeff k := by
          unfold arcsinSeriesCoeff invSqrtBinomCoeff
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
            (le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) k]))
        _ ≤ 1 := invSqrtBinomCoeff_le_one k
    calc
      arcsinSeriesCoeff k * |t| ^ (2 * k + 1) ≤ 1 * |t| ^ (2 * k + 1) := by gcongr
      _ = |t| * (|t| ^ 2) ^ k := by ring

private theorem summable_invSqrtSeries_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    Summable fun k ↦ invSqrtBinomCoeff k * t ^ (2 * k) := by
  refine Summable.of_norm_bounded (g := fun k ↦ (|t| ^ 2) ^ k)
    (summable_geometric_of_lt_one (by positivity) (by nlinarith [abs_nonneg t])) fun k ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (invSqrtBinomCoeff_nonneg k), abs_pow]
  calc
    invSqrtBinomCoeff k * |t| ^ (2 * k) ≤ 1 * |t| ^ (2 * k) := by
      gcongr
      exact invSqrtBinomCoeff_le_one k
    _ = (|t| ^ 2) ^ k := by ring

private theorem summable_nat_mul_geometric_real {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℕ ↦ (k : ℝ) * q ^ k := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm

private theorem hasSum_invSqrtSeries_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    HasSum (fun k ↦ invSqrtBinomCoeff k * t ^ (2 * k)) ((Real.sqrt (1 - t ^ 2))⁻¹) := by
  let f : ℝ → ℝ := fun s ↦ ∑' k, invSqrtBinomCoeff k * s ^ (2 * k)
  have hf_deriv : ∀ s : ℝ, |s| < 1 →
      HasDerivAt f (∑' k, invSqrtBinomCoeff (k + 1) * (2 * (k : ℝ) + 2) * s ^ (2 * k + 1)) s := by
    intro s hs
    obtain ⟨r, hsr, hr1⟩ := exists_between hs
    have hr_pos : 0 ≤ r := (abs_nonneg s).trans hsr.le
    have hbound : Summable fun k : ℕ ↦ invSqrtBinomCoeff k * ((2 * (k : ℝ)) * r ^ (2 * k - 1)) := by
      have hgeom : Summable fun k : ℕ ↦ (2 * (k : ℝ)) * (r ^ 2) ^ k := by
        have h1 := summable_nat_mul_geometric_real (sq_nonneg r) (by nlinarith)
        simpa [mul_assoc] using h1.mul_left (2 : ℝ)
      by_cases hr0 : r = 0
      · subst hr0
        refine summable_of_ne_finset_zero (s := {0}) fun k hk ↦ ?_
        have hkpos : 1 ≤ k := Nat.pos_of_ne_zero (by simpa using hk)
        have hpow : (0 : ℝ) ^ (2 * k - 1) = 0 := zero_pow (by omega)
        simp [hpow]
      · have hr_strict : 0 < r := lt_of_le_of_ne hr_pos (Ne.symm hr0)
        refine Summable.of_norm_bounded (g := fun k ↦ r⁻¹ * ((2 * (k : ℝ)) * (r ^ 2) ^ k))
          (hgeom.mul_left r⁻¹) fun k ↦ ?_
        rcases eq_or_ne k 0 with rfl | hk
        · simp
        · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (invSqrtBinomCoeff_nonneg k),
            abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ)),
            abs_pow, abs_of_pos hr_strict]
          have hpow : r ^ (2 * k - 1) = r⁻¹ * (r ^ 2) ^ k := by
            have : (r ^ 2) ^ k = r * r ^ (2 * k - 1) := by
              rw [← pow_mul, ← pow_succ']
              congr 1
              omega
            rw [this, inv_mul_cancel_left₀ hr0]
          rw [hpow]
          calc
            invSqrtBinomCoeff k * (2 * (k : ℝ) * (r⁻¹ * (r ^ 2) ^ k))
                ≤ 1 * (2 * (k : ℝ) * (r⁻¹ * (r ^ 2) ^ k)) :=
                  mul_le_mul_of_nonneg_right (invSqrtBinomCoeff_le_one k) (by positivity)
            _ = r⁻¹ * (2 * (k : ℝ) * (r ^ 2) ^ k) := by ring
    have hterm_deriv : ∀ k : ℕ, ∀ x ∈ Metric.ball (0 : ℝ) r,
        HasDerivAt (fun y ↦ invSqrtBinomCoeff k * y ^ (2 * k))
          (invSqrtBinomCoeff k * ((2 * (k : ℝ)) * x ^ (2 * k - 1))) x := by
      intro k x _
      rcases eq_or_ne k 0 with rfl | hk
      · simpa using hasDerivAt_const x (invSqrtBinomCoeff 0)
      · simpa [Nat.cast_mul, Nat.cast_ofNat] using (hasDerivAt_pow (2 * k) x).const_mul
          (invSqrtBinomCoeff k)
    have hterm_bound : ∀ k : ℕ, ∀ x ∈ Metric.ball (0 : ℝ) r,
        ‖invSqrtBinomCoeff k * ((2 * (k : ℝ)) * x ^ (2 * k - 1))‖ ≤
          invSqrtBinomCoeff k * ((2 * (k : ℝ)) * r ^ (2 * k - 1)) := by
      intro k x hx
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (invSqrtBinomCoeff_nonneg k),
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ)), abs_pow]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hx.le _) (by positivity))
        (invSqrtBinomCoeff_nonneg k)
    have hsum0 : Summable fun k ↦ invSqrtBinomCoeff k * (0 : ℝ) ^ (2 * k) :=
      summable_invSqrtSeries_of_abs_lt_one (by norm_num)
    have hd := hasDerivAt_tsum_of_isPreconnected hbound Metric.isOpen_ball
      (convex_ball (0 : ℝ) r).isPreconnected hterm_deriv hterm_bound
      (by simp [lt_of_le_of_lt (abs_nonneg s) hsr]) hsum0
      (by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hsr)
    have hshift : (∑' k : ℕ, invSqrtBinomCoeff k * ((2 * (k : ℝ)) * s ^ (2 * k - 1))) =
        ∑' m : ℕ, invSqrtBinomCoeff (m + 1) * (2 * (m : ℝ) + 2) * s ^ (2 * m + 1) := by
      have hsumm : Summable fun k : ℕ ↦
          invSqrtBinomCoeff k * ((2 * (k : ℝ)) * s ^ (2 * k - 1)) :=
        Summable.of_norm_bounded hbound fun k ↦ hterm_bound k s
          (by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hsr)
      rw [hsumm.tsum_eq_zero_add]
      simp only [CharP.cast_eq_zero, mul_zero, zero_mul, zero_add]
      refine tsum_congr fun m ↦ ?_
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      push_cast; ring
    rwa [hshift] at hd
  have hode : ∀ s : ℝ, |s| < 1 →
      (1 - s ^ 2) * (∑' k, invSqrtBinomCoeff (k + 1) * (2 * (k : ℝ) + 2) * s ^ (2 * k + 1)) =
        s * f s := by
    intro s hs
    let dterm : ℕ → ℝ := fun k ↦ invSqrtBinomCoeff (k + 1) * (2 * (k : ℝ) + 2) * s ^ (2 * k + 1)
    have hdsumm : Summable dterm := by
      have heq : dterm = fun k : ℕ ↦ (2 * (k : ℝ) + 1) * invSqrtBinomCoeff k * s ^ (2 * k + 1) := by
        ext k; dsimp [dterm]
        linarith [congrArg (· * s ^ (2 * k + 1)) (invSqrtBinomCoeff_succ k)]
      rw [heq]
      have hgeom : Summable fun k : ℕ ↦ (2 * (k : ℝ) + 1) * (|s| ^ 2) ^ k := by
        have h1 := summable_nat_mul_geometric_real (sq_nonneg |s|) (by nlinarith [abs_nonneg s])
        have h2 := summable_geometric_of_lt_one (sq_nonneg |s|) (by nlinarith [abs_nonneg s])
        convert (h1.mul_left 2).add h2 using 1; ext k; ring
      refine Summable.of_norm_bounded (hgeom.mul_left |s|) fun k ↦ ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ) + 1),
        abs_of_nonneg (invSqrtBinomCoeff_nonneg k), abs_pow]
      calc
        (2 * (k : ℝ) + 1) * invSqrtBinomCoeff k * |s| ^ (2 * k + 1)
            ≤ (2 * (k : ℝ) + 1) * 1 * |s| ^ (2 * k + 1) := by
              gcongr; exact invSqrtBinomCoeff_le_one k
        _ = |s| * ((2 * (k : ℝ) + 1) * (|s| ^ 2) ^ k) := by ring
    rw [sub_mul, one_mul, tsum_mul_left.symm]
    have hsplit_eq : ∀ k : ℕ, dterm k =
        s * (invSqrtBinomCoeff k * s ^ (2 * k)) +
          (2 * (k : ℝ)) * invSqrtBinomCoeff k * s ^ (2 * k + 1) := by
      intro k; dsimp [dterm]
      linarith [congrArg (· * s ^ (2 * k + 1)) (invSqrtBinomCoeff_succ k),
        show s * (invSqrtBinomCoeff k * s ^ (2 * k)) =
          invSqrtBinomCoeff k * s ^ (2 * k + 1) by ring]
    have h2summ : Summable fun k : ℕ ↦ (2 * (k : ℝ)) * invSqrtBinomCoeff k * s ^ (2 * k + 1) := by
      have : (fun k : ℕ ↦ (2 * (k : ℝ)) * invSqrtBinomCoeff k * s ^ (2 * k + 1)) =
          fun k : ℕ ↦ dterm k - s * (invSqrtBinomCoeff k * s ^ (2 * k)) := by
        ext k; linarith [hsplit_eq k]
      rw [this]
      exact hdsumm.sub ((summable_invSqrtSeries_of_abs_lt_one hs).mul_left s)
    rw [show (∑' k, dterm k) =
        (∑' k, s * (invSqrtBinomCoeff k * s ^ (2 * k))) +
          ∑' k : ℕ, (2 * (k : ℝ)) * invSqrtBinomCoeff k * s ^ (2 * k + 1) by
      rw [← ((summable_invSqrtSeries_of_abs_lt_one hs).mul_left s).tsum_add h2summ]
      exact tsum_congr hsplit_eq]
    rw [h2summ.tsum_eq_zero_add]
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul, zero_add]
    have htail : (∑' k : ℕ, (2 * ((k + 1 : ℕ) : ℝ)) * invSqrtBinomCoeff (k + 1) *
        s ^ (2 * (k + 1) + 1)) = ∑' k : ℕ, s ^ 2 * dterm k := by
      refine tsum_congr fun k ↦ ?_
      dsimp [dterm]
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega, pow_add]; push_cast; ring
    rw [htail, tsum_mul_left]; dsimp [f]; ring
  let G : ℝ → ℝ := (fun s ↦ 1 - s ^ 2) * (f * f)
  have hG_diff : ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      DifferentiableWithinAt ℝ G (Set.Ioo (-1 : ℝ) 1) s ∧ deriv G s = 0 := by
    intro s hs
    have hs_abs : |s| < 1 := abs_lt.mpr hs
    have hdf := hf_deriv s hs_abs
    have hd1 : HasDerivAt (fun x ↦ 1 - x ^ 2) (-2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).const_sub 1
    have hdG := hd1.mul (hdf.mul hdf)
    have hzero : (-2 * s) * (f * f) s + (1 - s ^ 2) *
        ((∑' k, invSqrtBinomCoeff (k + 1) * (2 * (k : ℝ) + 2) * s ^ (2 * k + 1)) * f s +
          f s * (∑' k, invSqrtBinomCoeff (k + 1) * (2 * (k : ℝ) + 2) * s ^ (2 * k + 1))) = 0 := by
      dsimp
      linarith [congrArg (fun z ↦ 2 * f s * z) (hode s hs_abs)]
    rw [hzero] at hdG
    exact ⟨hdG.differentiableAt.differentiableWithinAt, hdG.deriv⟩
  have hG0 : G 0 = 1 := by
    dsimp [G, f]
    rw [(summable_invSqrtSeries_of_abs_lt_one (by norm_num)).tsum_eq_zero_add]
    simp [invSqrtBinomCoeff]
  have hGt : G t = 1 := by
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1) 1).isPreconnected
      (fun x hx ↦ (hG_diff x hx).1) (fun x hx ↦ (hG_diff x hx).2)
      (abs_lt.mp ht) (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)
    exact hconst.trans hG0
  have hf_nonneg : 0 ≤ f t := tsum_nonneg fun k ↦ by
    rw [show t ^ (2 * k) = (t ^ 2) ^ k by rw [← pow_mul]]
    exact mul_nonneg (invSqrtBinomCoeff_nonneg k) (pow_nonneg (sq_nonneg t) k)
  have h1t : 0 < 1 - t ^ 2 := by nlinarith [abs_lt.mp ht]
  have hfeq : f t = (Real.sqrt (1 - t ^ 2))⁻¹ := by
    have hGt' : (1 - t ^ 2) * (f t * f t) = 1 := hGt
    have hsq : (f t) ^ 2 = ((Real.sqrt (1 - t ^ 2))⁻¹) ^ 2 := by
      rw [inv_pow, Real.sq_sqrt h1t.le]
      field_simp [h1t.ne']
      linarith [hGt']
    nlinarith [hf_nonneg, Real.sqrt_pos.mpr h1t, inv_pos.mpr (Real.sqrt_pos.mpr h1t)]
  rw [← hfeq]
  exact (summable_invSqrtSeries_of_abs_lt_one ht).hasSum

private theorem hasSum_arcsin_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    HasSum (fun k ↦ arcsinSeriesCoeff k * t ^ (2 * k + 1)) (Real.arcsin t) := by
  let A : ℝ → ℝ := fun s ↦ ∑' k, arcsinSeriesCoeff k * s ^ (2 * k + 1)
  have hA_deriv : ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt A ((Real.sqrt (1 - s ^ 2))⁻¹) s := by
    intro s hs
    have hs_abs : |s| < 1 := abs_lt.mpr hs
    obtain ⟨r, hsr, hr1⟩ := exists_between hs_abs
    have hr_pos : 0 ≤ r := (abs_nonneg s).trans hsr.le
    have hbound : Summable fun k : ℕ ↦ invSqrtBinomCoeff k * r ^ (2 * k) :=
      summable_invSqrtSeries_of_abs_lt_one (by rwa [abs_of_nonneg hr_pos])
    have hterm_deriv : ∀ k : ℕ, ∀ x ∈ Metric.ball (0 : ℝ) r,
        HasDerivAt (fun y ↦ arcsinSeriesCoeff k * y ^ (2 * k + 1))
          (invSqrtBinomCoeff k * x ^ (2 * k)) x := by
      intro k x _
      have hd := (hasDerivAt_pow (2 * k + 1) x).const_mul (arcsinSeriesCoeff k)
      convert hd using 1
      unfold arcsinSeriesCoeff invSqrtBinomCoeff
      have h2k1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      have hexp : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hexp]
      push_cast
      field_simp
    have hterm_bound : ∀ k : ℕ, ∀ x ∈ Metric.ball (0 : ℝ) r,
        ‖invSqrtBinomCoeff k * x ^ (2 * k)‖ ≤ invSqrtBinomCoeff k * r ^ (2 * k) := by
      intro k x hx
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (invSqrtBinomCoeff_nonneg k), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hx.le _)
        (invSqrtBinomCoeff_nonneg k)
    have hsum0 : Summable fun k ↦ arcsinSeriesCoeff k * (0 : ℝ) ^ (2 * k + 1) :=
      summable_arcsinSeries_of_abs_lt_one (by norm_num)
    have hd := hasDerivAt_tsum_of_isPreconnected hbound Metric.isOpen_ball
      (convex_ball (0 : ℝ) r).isPreconnected hterm_deriv hterm_bound
      (by simp [lt_of_le_of_lt (abs_nonneg s) hsr]) hsum0
      (by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hsr)
    rwa [(hasSum_invSqrtSeries_of_abs_lt_one hs_abs).tsum_eq] at hd
  have hdiff : ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      DifferentiableWithinAt ℝ (A - Real.arcsin) (Set.Ioo (-1 : ℝ) 1) s ∧
        deriv (A - Real.arcsin) s = 0 := by
    intro s hs
    have hd1 := hA_deriv s hs
    have hd2 := Real.hasDerivAt_arcsin (ne_of_gt hs.1) (ne_of_lt hs.2)
    rw [one_div] at hd2
    have hsub := hd1.sub hd2
    rw [sub_self] at hsub
    exact ⟨hsub.differentiableAt.differentiableWithinAt, hsub.deriv⟩
  have h0 : (A - Real.arcsin) 0 = 0 := by simp [A]
  have hAt : (A - Real.arcsin) t = 0 := by
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1) 1).isPreconnected
      (fun x hx ↦ (hdiff x hx).1) (fun x hx ↦ (hdiff x hx).2)
      (abs_lt.mp ht) (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)
    exact hconst.trans h0
  have hEq : A t = Real.arcsin t := sub_eq_zero.mp hAt
  rw [← hEq]
  exact (summable_arcsinSeries_of_abs_lt_one ht).hasSum

/-- Power series expansion of `Real.arcsin` on the entire closed interval `[-1, 1]`:
$\sum_{k=0}^\infty \frac{\binom{2k}{k}}{4^k (2k + 1)} t^{2k + 1} = \arcsin t$. -/
theorem hasSum_arcsin {t : ℝ} (ht : |t| ≤ 1) :
    HasSum (fun k ↦ arcsinSeriesCoeff k * t ^ (2 * k + 1)) (Real.arcsin t) := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact hasSum_arcsin_of_abs_lt_one hlt
  · have htend_seq : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) - ((n : ℝ) + 2)⁻¹)
        Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))))
    have h1 : HasSum arcsinSeriesCoeff (Real.pi / 2) := by
      have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, arcsinSeriesCoeff k ≤ Real.pi / 2 := by
        intro N
        have hle_s : ∀ s ∈ Set.Ico (0 : ℝ) 1,
            ∑ k ∈ Finset.range N, arcsinSeriesCoeff k * s ^ (2 * k + 1) ≤ Real.pi / 2 := by
          intro s hs
          have hs_abs : |s| < 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
          calc
            ∑ k ∈ Finset.range N, arcsinSeriesCoeff k * s ^ (2 * k + 1)
                ≤ ∑' k, arcsinSeriesCoeff k * s ^ (2 * k + 1) :=
                  (summable_arcsinSeries_of_abs_lt_one hs_abs).sum_le_tsum (Finset.range N)
                    fun k _ ↦ mul_nonneg (arcsinSeriesCoeff_pos k).le (pow_nonneg hs.1 _)
            _ = Real.arcsin s := (hasSum_arcsin_of_abs_lt_one hs_abs).tsum_eq
            _ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
        have hcont : Continuous fun s : ℝ ↦
            ∑ k ∈ Finset.range N, arcsinSeriesCoeff k * s ^ (2 * k + 1) := by fun_prop
        have htend : Filter.Tendsto
            (fun n : ℕ ↦ ∑ k ∈ Finset.range N,
              arcsinSeriesCoeff k * ((1 : ℝ) - ((n : ℝ) + 2)⁻¹) ^ (2 * k + 1))
            Filter.atTop
            (𝓝 (∑ k ∈ Finset.range N, arcsinSeriesCoeff k * (1 : ℝ) ^ (2 * k + 1))) :=
          hcont.continuousAt.tendsto.comp htend_seq
        simp only [one_pow, mul_one] at htend
        refine le_of_tendsto htend (Filter.Eventually.of_forall fun n ↦ hle_s _ ⟨?_, ?_⟩)
        · have : ((n : ℝ) + 2)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
          linarith
        · linarith [show 0 < ((n : ℝ) + 2)⁻¹ by positivity]
      have hsumm : Summable arcsinSeriesCoeff :=
        summable_of_sum_range_le (fun k ↦ (arcsinSeriesCoeff_pos k).le) hpart
      have htsum_le : ∑' k, arcsinSeriesCoeff k ≤ Real.pi / 2 :=
        hsumm.tsum_le_of_sum_range_le hpart
      have hge_s : ∀ n : ℕ, Real.arcsin ((1 : ℝ) - ((n : ℝ) + 2)⁻¹) ≤
        ∑' k, arcsinSeriesCoeff k := by
        intro n
        set s := (1 : ℝ) - ((n : ℝ) + 2)⁻¹
        have hs0 : 0 ≤ s := by
          have : ((n : ℝ) + 2)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
          linarith
        have hs1 : s < 1 := by linarith [show 0 < ((n : ℝ) + 2)⁻¹ by positivity]
        have hs_abs : |s| < 1 := by rwa [abs_of_nonneg hs0]
        rw [← (hasSum_arcsin_of_abs_lt_one hs_abs).tsum_eq]
        refine (summable_arcsinSeries_of_abs_lt_one hs_abs).tsum_le_tsum (fun k ↦ ?_) hsumm
        calc
          arcsinSeriesCoeff k * s ^ (2 * k + 1) ≤ arcsinSeriesCoeff k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hs0 hs1.le) (arcsinSeriesCoeff_pos k).le
          _ = arcsinSeriesCoeff k := mul_one _
      have htend_arcsin : Filter.Tendsto (fun n : ℕ ↦ Real.arcsin ((1 : ℝ) - ((n : ℝ) + 2)⁻¹))
          Filter.atTop (𝓝 (Real.arcsin 1)) :=
        Real.continuous_arcsin.continuousAt.tendsto.comp htend_seq
      rw [Real.arcsin_one] at htend_arcsin
      have hge : Real.pi / 2 ≤ ∑' k, arcsinSeriesCoeff k :=
        le_of_tendsto htend_arcsin (Filter.Eventually.of_forall hge_s)
      rw [← le_antisymm htsum_le hge]
      exact hsumm.hasSum
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp heq with rfl | rfl
    · simpa [Real.arcsin_one] using h1
    · have hodd : (fun k ↦ arcsinSeriesCoeff k * (-1 : ℝ) ^ (2 * k + 1)) =
          fun k ↦ -(arcsinSeriesCoeff k) := by
        ext k
        rw [pow_add, pow_mul]
        norm_num
      rw [hodd, Real.arcsin_neg, Real.arcsin_one]
      exact h1.neg

/-! ### Sheppard's Sign Expectation & Krivine's Upper Bound -/

/-- Sheppard's formula for $\pm 1$ hyperplane signs under `stdGaussian E`:
$\mathbb{E}_{x \sim \gamma_E}[\mathrm{sgn}\langle u, x\rangle \mathrm{sgn}\langle w, x\rangle]
= \frac{2}{\pi} \arcsin\langle u, w\rangle$. -/
theorem integral_stdGaussian_sign_mul_sign {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ∫ x : E, (if 0 < ⟪u, x⟫_ℝ then (1 : ℝ) else -1) * (if 0 < ⟪w, x⟫_ℝ then 1 else -1)
      ∂stdGaussian E = (2 / Real.pi) * Real.arcsin ⟪u, w⟫_ℝ := by
  have hρ : |⟪u, w⟫_ℝ| ≤ 1 := by
    simpa [hu, hw] using abs_real_inner_le_norm u w
  have hmap := stdGaussian_map_inner_prod_eq_correlatedGaussian hu hw
  let φ : ℝ × ℝ → ℝ := fun p ↦ (if 0 < p.1 then (1 : ℝ) else -1) * (if 0 < p.2 then 1 else -1)
  have hφ_meas : Measurable φ :=
    (Measurable.ite (measurableSet_Ioi.preimage measurable_fst) measurable_const
      measurable_const).mul
    (Measurable.ite (measurableSet_Ioi.preimage measurable_snd) measurable_const
      measurable_const)
  have hrew : (∫ x : E, φ (⟪u, x⟫_ℝ, ⟪w, x⟫_ℝ) ∂stdGaussian E) =
      ∫ p, φ p ∂correlatedGaussian ⟪u, w⟫_ℝ := by
    rw [← hmap, integral_map (by fun_prop) hφ_meas.aestronglyMeasurable]
  dsimp [φ] at hrew
  rw [hrew, integral_correlatedGaussian_ite_pos_mul_ite_pos hρ,
    Real.arccos_eq_pi_div_two_sub_arcsin]
  field_simp [Real.pi_ne_zero]
  ring

/-- Krivine's constant $\frac{\pi}{2 \log(1 + \sqrt{2})} \approx 1.782214$. -/
noncomputable def krivineConstant : ℝ :=
  Real.pi / (2 * Real.log (1 + Real.sqrt 2))

private theorem log_one_add_sqrt_two_pos : 0 < Real.log (1 + Real.sqrt 2) :=
  Real.log_pos (by have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos; linarith)

private theorem log_one_add_sqrt_two_lt_pi_div_two :
    Real.log (1 + Real.sqrt 2) < Real.pi / 2 := by
  have hsqrt : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hexp : 1 + Real.sqrt 2 < Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      pow_zero, pow_one, zero_add, div_one] at hsum
    linarith
  have hlog1 : Real.log (1 + Real.sqrt 2) < 1 :=
    (Real.log_lt_log (by positivity) hexp).trans_eq (Real.log_exp 1)
  linarith [Real.pi_gt_three]

private theorem sinh_log_one_add_sqrt_two :
    Real.sinh (Real.log (1 + Real.sqrt 2)) = 1 := by
  have hpos : 0 < 1 + Real.sqrt 2 := by positivity
  rw [Real.sinh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hinv]; ring

private theorem tendsto_sum_finset {ι α : Type*} (s : Finset ι) {f : ι → α → ℝ} {l : Filter α}
    {g : ι → ℝ} (hf : ∀ i ∈ s, Filter.Tendsto (f i) l (𝓝 (g i))) :
    Filter.Tendsto (fun a ↦ ∑ i ∈ s, f i a) l (𝓝 (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact tendsto_const_nhds
  | @insert i₀ s hi₀ ih =>
    simp only [Finset.sum_insert hi₀]
    exact (hf i₀ (Finset.mem_insert_self i₀ s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Krivine's theorem for finite matrices: for every finite real matrix `A`,
$\mathrm{SDP}(A) \le \frac{\pi}{2 \log(1 + \sqrt{2})} \mathrm{OPT}(A)$. -/
theorem sdpNorm_le_krivineConstant_mul_optNorm {μ ν : Type*} [Fintype μ] [Fintype ν]
    (A : Matrix μ ν ℝ) :
    sdpNorm A ≤ krivineConstant * optNorm A := by
  classical
  set a : ℝ := Real.log (1 + Real.sqrt 2)
  have ha_pos : 0 < a := log_one_add_sqrt_two_pos
  have ha_lt : a < Real.pi / 2 := log_one_add_sqrt_two_lt_pi_div_two
  have hsinh : HasSum (fun k : ℕ ↦ a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) 1 := by
    simpa [a, sinh_log_one_add_sqrt_two] using Real.hasSum_sinh a
  rw [sdpNorm_le_iff]
  intro u w hu hw
  have hK : ∀ K : ℕ,
      ∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin
        (∑ k ∈ Finset.range (K + 1),
          (-1 : ℝ) ^ k * a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) *
            ⟪u i, w j⟫_ℝ ^ (2 * k + 1))) ≤ optNorm A := by
    intro K
    let SK : ℝ := ∑ k ∈ Finset.range (K + 1), a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
    have hSK_le : SK ≤ 1 :=
      hsinh.summable.sum_le_tsum (Finset.range (K + 1))
        (fun k _ ↦ by positivity) |>.trans_eq hsinh.tsum_eq
    let J := (Σ k : Fin (K + 1), (Fin (2 * k.1 + 1) → (μ ⊕ ν))) ⊕ Fin 2
    let EK := EuclideanSpace ℝ J
    let uK : μ → EK := fun i ↦ WithLp.toLp 2 fun idx ↦
      match idx with
      | Sum.inl ⟨k, α⟩ =>
          Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
            vecTensorPow (2 * k.1 + 1) (u i) α
      | Sum.inr 0 => Real.sqrt (1 - SK)
      | Sum.inr 1 => 0
    let wK : ν → EK := fun j ↦ WithLp.toLp 2 fun idx ↦
      match idx with
      | Sum.inl ⟨k, α⟩ =>
          (-1 : ℝ) ^ k.1 * Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
            vecTensorPow (2 * k.1 + 1) (w j) α
      | Sum.inr 0 => 0
      | Sum.inr 1 => Real.sqrt (1 - SK)
    have hSK_fin : (∑ k : Fin (K + 1), a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) = SK :=
      Fin.sum_univ_eq_sum_range (fun k ↦ a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) (K + 1)
    have huK : ∀ i, ‖uK i‖ = 1 := by
      intro i
      have hsq : ‖uK i‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Real.norm_eq_abs, sq_abs, J, Fintype.sum_sum_type, Fintype.sum_sigma,
          Fin.sum_univ_two, Fin.isValue]
        dsimp [uK]
        have hpart : ∀ k : Fin (K + 1),
            (∑ α : Fin (2 * k.1 + 1) → (μ ⊕ ν),
              (Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
                vecTensorPow (2 * k.1 + 1) (u i) α) ^ 2) =
              a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by
          intro k
          have hc_nn : 0 ≤ a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by positivity
          have hnorm_t : ‖vecTensorPow (2 * k.1 + 1) (u i)‖ ^ 2 = 1 := by
            rw [norm_vecTensorPow _ (hu i), one_pow]
          rw [EuclideanSpace.norm_sq_eq] at hnorm_t
          simp only [Real.norm_eq_abs, sq_abs] at hnorm_t
          calc
            (∑ α, (Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
                vecTensorPow (2 * k.1 + 1) (u i) α) ^ 2)
                = (Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ))) ^ 2 *
                    ∑ α, (vecTensorPow (2 * k.1 + 1) (u i) α) ^ 2 := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ ↦ by ring
            _ = a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by
                  rw [Real.sq_sqrt hc_nn, hnorm_t, mul_one]
        simp_rw [hpart]
        rw [hSK_fin, Real.sq_sqrt (by linarith)]; ring
      nlinarith [norm_nonneg (uK i)]
    have hwK : ∀ j, ‖wK j‖ = 1 := by
      intro j
      have hsq : ‖wK j‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Real.norm_eq_abs, sq_abs, J, Fintype.sum_sum_type, Fintype.sum_sigma,
          Fin.sum_univ_two, Fin.isValue]
        dsimp [wK]
        have hpart : ∀ k : Fin (K + 1),
            (∑ α : Fin (2 * k.1 + 1) → (μ ⊕ ν),
              ((-1 : ℝ) ^ k.1 * Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
                vecTensorPow (2 * k.1 + 1) (w j) α) ^ 2) =
              a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by
          intro k
          have hc_nn : 0 ≤ a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by positivity
          have hnorm_t : ‖vecTensorPow (2 * k.1 + 1) (w j)‖ ^ 2 = 1 := by
            rw [norm_vecTensorPow _ (hw j), one_pow]
          rw [EuclideanSpace.norm_sq_eq] at hnorm_t
          simp only [Real.norm_eq_abs, sq_abs] at hnorm_t
          have hsign_sq : ((-1 : ℝ) ^ k.1) ^ 2 = 1 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          calc
            (∑ α, ((-1 : ℝ) ^ k.1 *
                Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
                vecTensorPow (2 * k.1 + 1) (w j) α) ^ 2)
                = ((-1 : ℝ) ^ k.1) ^ 2 *
                    (Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ))) ^ 2 *
                    ∑ α, (vecTensorPow (2 * k.1 + 1) (w j) α) ^ 2 := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ ↦ by ring
            _ = a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by
                  rw [hsign_sq, one_mul, Real.sq_sqrt hc_nn, hnorm_t, mul_one]
        simp_rw [hpart]
        rw [hSK_fin, Real.sq_sqrt (by linarith)]; ring
      nlinarith [norm_nonneg (wK j)]
    have hinnerK : ∀ i j, ⟪uK i, wK j⟫_ℝ =
        ∑ k ∈ Finset.range (K + 1),
          (-1 : ℝ) ^ k * a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) *
            ⟪u i, w j⟫_ℝ ^ (2 * k + 1) := by
      intro i j
      rw [PiLp.inner_apply]
      dsimp [uK, wK, J]
      simp only [conj_trivial, Fintype.sum_sum_type, Fintype.sum_sigma, Fin.sum_univ_two,
        mul_zero, zero_mul, add_zero]
      rw [← Fin.sum_univ_eq_sum_range _ (K + 1)]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hc_nn : 0 ≤ a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) := by positivity
      have hinner_t : (∑ α, vecTensorPow (2 * k.1 + 1) (w j) α *
          vecTensorPow (2 * k.1 + 1) (u i) α) = ⟪u i, w j⟫_ℝ ^ (2 * k.1 + 1) := by
        simpa [PiLp.inner_apply, conj_trivial] using inner_vecTensorPow (2 * k.1 + 1) (u i) (w j)
      calc
        (∑ α, ((-1 : ℝ) ^ k.1 *
            Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
            vecTensorPow (2 * k.1 + 1) (w j) α) *
          (Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ)) *
            vecTensorPow (2 * k.1 + 1) (u i) α))
            = (-1 : ℝ) ^ k.1 *
                (Real.sqrt (a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ))) ^ 2 *
                ∑ α, vecTensorPow (2 * k.1 + 1) (w j) α *
                  vecTensorPow (2 * k.1 + 1) (u i) α := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun α _ ↦ by ring
        _ = (-1 : ℝ) ^ k.1 * a ^ (2 * k.1 + 1) / ((2 * k.1 + 1).factorial : ℝ) *
              ⟪u i, w j⟫_ℝ ^ (2 * k.1 + 1) := by
              rw [Real.sq_sqrt hc_nn, hinner_t]
              ring
    let sgnU : EK → μ → ℝ := fun g i ↦ if 0 < ⟪uK i, g⟫_ℝ then 1 else -1
    let sgnW : EK → ν → ℝ := fun g j ↦ if 0 < ⟪wK j, g⟫_ℝ then 1 else -1
    have hint_pair : ∀ i j, Integrable (fun g : EK ↦ A i j * sgnU g i * sgnW g j)
        (stdGaussian EK) := by
      intro i j
      have hmeas : Measurable fun g : EK ↦ A i j * sgnU g i * sgnW g j := by
        refine (measurable_const.mul ?_).mul ?_
        · exact Measurable.ite
            (isOpen_lt continuous_const (continuous_const.inner continuous_id')).measurableSet
            measurable_const measurable_const
        · exact Measurable.ite
            (isOpen_lt continuous_const (continuous_const.inner continuous_id')).measurableSet
            measurable_const measurable_const
      refine Integrable.of_bound hmeas.aestronglyMeasurable |A i j|
        (Filter.Eventually.of_forall fun g ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |sgnU g i| = 1 := by dsimp [sgnU]; split_ifs <;> norm_num
      have h2 : |sgnW g j| = 1 := by dsimp [sgnW]; split_ifs <;> norm_num
      rw [h1, h2, mul_one, mul_one]
    have hexp_eq : (∫ g : EK, (∑ i, ∑ j, A i j * sgnU g i * sgnW g j) ∂stdGaussian EK) =
        ∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin ⟪uK i, wK j⟫_ℝ) := by
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint_pair i j]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum _ fun j _ ↦ hint_pair i j]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hmul : (fun g : EK ↦ A i j * sgnU g i * sgnW g j) =
          fun g : EK ↦ A i j * (sgnU g i * sgnW g j) := funext fun _ ↦ mul_assoc _ _ _
      rw [hmul, integral_const_mul, integral_stdGaussian_sign_mul_sign (huK i) (hwK j)]
    have hpt_le : ∀ g : EK, ∑ i, ∑ j, A i j * sgnU g i * sgnW g j ≤ optNorm A := by
      intro g
      refine le_optNorm_of_signs A (fun i ↦ ?_) (fun j ↦ ?_)
      · dsimp [sgnU]; split_ifs <;> simp
      · dsimp [sgnW]; split_ifs <;> simp
    have hint_le : (∫ g : EK, (∑ i, ∑ j, A i j * sgnU g i * sgnW g j) ∂stdGaussian EK) ≤
        ∫ _ : EK, optNorm A ∂stdGaussian EK :=
      integral_mono_ae
        (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint_pair i j)
        (integrable_const _) (Filter.Eventually.of_forall hpt_le)
    simp only [integral_const, probReal_univ, one_smul] at hint_le
    simpa [hexp_eq, hinnerK] using hint_le
  have htend : Filter.Tendsto
      (fun K : ℕ ↦ ∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin
        (∑ k ∈ Finset.range (K + 1),
          (-1 : ℝ) ^ k * a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) *
            ⟪u i, w j⟫_ℝ ^ (2 * k + 1))))
      Filter.atTop (𝓝 (∑ i, ∑ j, A i j * ((2 / Real.pi) * (a * ⟪u i, w j⟫_ℝ)))) := by
    refine tendsto_sum_finset _ fun i _ ↦ tendsto_sum_finset _ fun j _ ↦ ?_
    refine tendsto_const_nhds.mul (tendsto_const_nhds.mul ?_)
    have hsin_ij := Real.hasSum_sin (a * ⟪u i, w j⟫_ℝ)
    have hrew_term : (fun k : ℕ ↦
        (-1 : ℝ) ^ k * a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) *
          ⟪u i, w j⟫_ℝ ^ (2 * k + 1)) =
        fun k : ℕ ↦ (-1 : ℝ) ^ k * (a * ⟪u i, w j⟫_ℝ) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ) := by
      ext k
      rw [mul_pow]
      ring
    simp_rw [hrew_term]
    have htend_sin : Filter.Tendsto
        (fun K : ℕ ↦ ∑ k ∈ Finset.range (K + 1),
          (-1 : ℝ) ^ k * (a * ⟪u i, w j⟫_ℝ) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
        Filter.atTop (𝓝 (Real.sin (a * ⟪u i, w j⟫_ℝ))) :=
      hsin_ij.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have habs_ij : |a * ⟪u i, w j⟫_ℝ| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos ha_pos]
      have h1 : |⟪u i, w j⟫_ℝ| ≤ 1 := by simpa [hu i, hw j] using abs_real_inner_le_norm (u i) (w j)
      calc
        a * |⟪u i, w j⟫_ℝ| ≤ a * 1 := by gcongr
        _ = a := mul_one a
        _ ≤ Real.pi / 2 := ha_lt.le
    have harcsin_sin : Real.arcsin (Real.sin (a * ⟪u i, w j⟫_ℝ)) = a * ⟪u i, w j⟫_ℝ :=
      Real.arcsin_sin (abs_le.mp habs_ij).1 (abs_le.mp habs_ij).2
    have hcomp := Real.continuous_arcsin.continuousAt.tendsto.comp htend_sin
    rwa [harcsin_sin] at hcomp
  have hlim_le : ∑ i, ∑ j, A i j * ((2 / Real.pi) * (a * ⟪u i, w j⟫_ℝ)) ≤ optNorm A :=
    le_of_tendsto htend (Filter.Eventually.of_forall hK)
  have hfactor : (∑ i, ∑ j, A i j * ((2 / Real.pi) * (a * ⟪u i, w j⟫_ℝ))) =
      (2 * a / Real.pi) * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hfactor] at hlim_le
  unfold krivineConstant
  change ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ≤ (Real.pi / (2 * a)) * optNorm A
  have hinv : (Real.pi / (2 * a)) * (2 * a / Real.pi) = 1 := by
    field_simp [Real.pi_ne_zero, ha_pos.ne']
  calc
    ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ
        = (Real.pi / (2 * a)) * ((2 * a / Real.pi) * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ) := by
          rw [← mul_assoc, hinv, one_mul]
    _ ≤ (Real.pi / (2 * a)) * optNorm A :=
          mul_le_mul_of_nonneg_left hlim_le (by positivity)

/-! ### The Real Grothendieck Constant $K_G$ -/

private def oneMatrix : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ ↦ 1

private theorem oneMatrix_ne_zero : oneMatrix ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [oneMatrix] at this

private theorem optNorm_oneMatrix : optNorm oneMatrix = 1 := by
  apply le_antisymm
  · rw [optNorm_le_iff]
    intro x y hx hy
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
    calc
      oneMatrix 0 0 * x 0 * y 0 ≤ |oneMatrix 0 0 * x 0 * y 0| := le_abs_self _
      _ = 1 := by
        simp [oneMatrix, abs_mul, abs_eq_one_of_mem_neg_one_one (hx 0),
          abs_eq_one_of_mem_neg_one_one (hy 0)]
  · simpa [oneMatrix] using le_optNorm_of_signs oneMatrix (x := fun _ ↦ 1) (y := fun _ ↦ 1)
      (fun _ ↦ by simp) (fun _ ↦ by simp)

private theorem sdpNorm_oneMatrix : sdpNorm oneMatrix = 1 := by
  apply le_antisymm
  · rw [sdpNorm_le_iff]
    intro u w hu hw
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
      oneMatrix, Matrix.of_apply, one_mul]
    calc
      ⟪u 0, w 0⟫_ℝ ≤ ‖u 0‖ * ‖w 0‖ := (le_abs_self _).trans (abs_real_inner_le_norm _ _)
      _ = 1 := by rw [hu 0, hw 0, mul_one]
  · exact optNorm_oneMatrix ▸ optNorm_le_sdpNorm oneMatrix

private def grothendieckRatioSet : Set ℝ :=
  {r : ℝ | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), r = sdpNorm A / optNorm A}

private theorem grothendieckRatioSet_nonempty : grothendieckRatioSet.Nonempty :=
  ⟨1, 1, 1, oneMatrix, by simp [optNorm_oneMatrix, sdpNorm_oneMatrix]⟩

private theorem grothendieckRatioSet_bddAbove : BddAbove grothendieckRatioSet := by
  refine ⟨krivineConstant, ?_⟩
  rintro r ⟨m, n, A, rfl⟩
  by_cases hA : A = 0
  · subst hA
    simp only [sdpNorm_zero, optNorm_zero, zero_div]
    unfold krivineConstant
    have := log_one_add_sqrt_two_pos
    positivity
  · rw [div_le_iff₀ ((optNorm_pos_iff A).mpr hA)]
    exact sdpNorm_le_krivineConstant_mul_optNorm A

/-- The real Grothendieck constant
$K_G = \sup_{m, n \in \mathbb{N}} \sup_{A \in \mathbb{R}^{m \times n}}
\frac{\mathrm{SDP}(A)}{\mathrm{OPT}(A)}$. -/
noncomputable def grothendieckConstant : ℝ :=
  sSup grothendieckRatioSet

/-- Restricting the supremum defining `grothendieckConstant` to nonzero matrices `A ≠ 0` gives
the exact same value (eliminating any `0 / 0 = 0` division artifacts). -/
theorem grothendieckConstant_eq_sSup_ne_zero :
    grothendieckConstant =
      sSup {r : ℝ | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
        A ≠ 0 ∧ r = sdpNorm A / optNorm A} := by
  have h1_mem : (1 : ℝ) ∈ {r : ℝ | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
      A ≠ 0 ∧ r = sdpNorm A / optNorm A} :=
    ⟨1, 1, oneMatrix, oneMatrix_ne_zero, by simp [optNorm_oneMatrix, sdpNorm_oneMatrix]⟩
  have hsub : {r : ℝ | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
      A ≠ 0 ∧ r = sdpNorm A / optNorm A} ⊆ grothendieckRatioSet := by
    rintro r ⟨m, n, A, _, rfl⟩
    exact ⟨m, n, A, rfl⟩
  apply le_antisymm
  · refine csSup_le grothendieckRatioSet_nonempty ?_
    rintro r ⟨m, n, A, rfl⟩
    by_cases hA : A = 0
    · subst hA
      simp only [sdpNorm_zero, optNorm_zero, zero_div]
      exact le_trans zero_le_one (le_csSup (grothendieckRatioSet_bddAbove.mono hsub) h1_mem)
    · exact le_csSup (grothendieckRatioSet_bddAbove.mono hsub) ⟨m, n, A, hA, rfl⟩
  · exact csSup_le_csSup grothendieckRatioSet_bddAbove ⟨1, h1_mem⟩ hsub

/-- Krivine's upper bound on the real Grothendieck constant:
$K_G \le \frac{\pi}{2 \log(1 + \sqrt{2})}$. -/
theorem grothendieckConstant_le_krivineConstant :
    grothendieckConstant ≤ krivineConstant := by
  refine csSup_le grothendieckRatioSet_nonempty ?_
  rintro r ⟨m, n, A, rfl⟩
  by_cases hA : A = 0
  · subst hA
    simp only [sdpNorm_zero, optNorm_zero, zero_div]
    unfold krivineConstant
    have := log_one_add_sqrt_two_pos
    positivity
  · rw [div_le_iff₀ ((optNorm_pos_iff A).mpr hA)]
    exact sdpNorm_le_krivineConstant_mul_optNorm A

/-- $1 \le K_G$. -/
theorem one_le_grothendieckConstant : 1 ≤ grothendieckConstant :=
  le_csSup grothendieckRatioSet_bddAbove
    ⟨1, 1, oneMatrix, by simp [optNorm_oneMatrix, sdpNorm_oneMatrix]⟩

/-- `grothendieckConstant` is strictly positive. -/
theorem grothendieckConstant_pos : 0 < grothendieckConstant :=
  lt_of_lt_of_le zero_lt_one one_le_grothendieckConstant

/-- **Grothendieck's Inequality**: for every finite real matrix `A`,
$\mathrm{SDP}(A) \le K_G \cdot \mathrm{OPT}(A)$. -/
theorem sdpNorm_le_grothendieckConstant_mul_optNorm {μ ν : Type*} [Fintype μ] [Fintype ν]
    (A : Matrix μ ν ℝ) :
    sdpNorm A ≤ grothendieckConstant * optNorm A := by
  let e₁ := Fintype.equivFin μ
  let e₂ := Fintype.equivFin ν
  let B := Matrix.reindex e₁ e₂ A
  rw [← sdpNorm_reindex e₁ e₂ A, ← optNorm_reindex e₁ e₂ A]
  change sdpNorm B ≤ grothendieckConstant * optNorm B
  by_cases hB : B = 0
  · simp [hB]
  · have hpos : 0 < optNorm B := (optNorm_pos_iff B).mpr hB
    rw [← div_le_iff₀ hpos]
    exact le_csSup grothendieckRatioSet_bddAbove ⟨Fintype.card μ, Fintype.card ν, B, rfl⟩

/-- Lower-bound criterion for $K_G$: any finite matrix `A` gives
$\frac{\mathrm{SDP}(A)}{\mathrm{OPT}(A)} \le K_G$. -/
theorem div_le_grothendieckConstant {μ ν : Type*} [Fintype μ] [Fintype ν]
    (A : Matrix μ ν ℝ) :
    sdpNorm A / optNorm A ≤ grothendieckConstant := by
  by_cases hA : A = 0
  · subst hA
    simp [grothendieckConstant_pos.le]
  · rw [div_le_iff₀ ((optNorm_pos_iff A).mpr hA)]
    exact sdpNorm_le_grothendieckConstant_mul_optNorm A

/-- Upper-bound criterion for $K_G$ (equivalently lower-bound criterion for $K_G^{-1}$): if
`c * sdpNorm A ≤ optNorm A` holds for all finite matrices `A`, then
`c ≤ grothendieckConstant⁻¹`. -/
theorem inv_grothendieckConstant_ge_of_bound {c : ℝ}
    (h : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), c * sdpNorm A ≤ optNorm A) :
    c ≤ grothendieckConstant⁻¹ := by
  by_cases hc : c ≤ 0
  · exact hc.trans (inv_nonneg.mpr grothendieckConstant_pos.le)
  · push Not at hc
    rw [le_inv_comm₀ hc grothendieckConstant_pos]
    refine csSup_le grothendieckRatioSet_nonempty ?_
    rintro r ⟨m, n, A, rfl⟩
    by_cases hA : A = 0
    · subst hA
      simp only [sdpNorm_zero, optNorm_zero, zero_div]
      positivity
    · have hpos : 0 < optNorm A := (optNorm_pos_iff A).mpr hA
      rw [div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀' hc]
      exact h m n A

end CslibFrontier.Grothendieck
