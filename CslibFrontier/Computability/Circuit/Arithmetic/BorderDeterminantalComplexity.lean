/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Hausdorff

import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Symmetric and Border Determinantal Complexity and Quadratic Power-Sum Upper Bounds

This module extends `CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity` with
transpose-symmetric and border (coefficientwise limit) determinantal complexity models, degree
preservation under border approximation, and explicit quadratic determinantal representations for
diagonal power sums $F_{N,d} = \sum_{i=0}^{N-1} X_i^d$:

## Main definitions

* `Cslib.Circuits.Arithmetic.HasSymmetricDeterminantalRepresentation` and
  `Cslib.Circuits.Arithmetic.symmetricDeterminantalComplexity`: transpose-symmetric affine-linear
  determinantal representations and symmetric determinantal complexity `\sdc(f) : ℕ∞`.
* `Cslib.Circuits.Arithmetic.HasBorderDeterminantalRepresentation`,
  `Cslib.Circuits.Arithmetic.borderDeterminantalComplexity`,
  `Cslib.Circuits.Arithmetic.HasBorderSymmetricDeterminantalRepresentation`, and
  `Cslib.Circuits.Arithmetic.borderSymmDeterminantalComplexity`: coefficientwise limit models
  `\bdc(f)` and `\bsdc(f)` in `ℕ∞`.
* `Cslib.Circuits.Arithmetic.diagonalPowerSum`: $F_{N,d} = \sum_{i=0}^{N-1} X_i^d$.

## Main results

* `Cslib.Circuits.Arithmetic.borderDeterminantalComplexity_le_determinantalComplexity`,
  `Cslib.Circuits.Arithmetic.determinantalComplexity_le_symmetricDeterminantalComplexity`,
  `Cslib.Circuits.Arithmetic.borderSymmDeterminantalComplexity_le_symmetricDeterminantalComplexity`,
  `Cslib.Circuits.Arithmetic.borderDeterminantalComplexity_le_borderSymmDeterminantalComplexity`:
  comparison hierarchy among `\bdc`, `\dc`, `\bsdc`, and `\sdc`.
* `Cslib.Circuits.Arithmetic.totalDegree_le_of_hasBorderDeterminantalRepresentation`: over any
  Hausdorff topological commutative ring, border determinantal complexity is bounded below by total
  degree.
* `Cslib.Circuits.Arithmetic.hasDeterminantalRepresentation_diagonalPowerSum` and
  `Cslib.Circuits.Arithmetic.determinantalComplexity_diagonalPowerSum_le`: explicit ordinary
  determinantal representation of $F_{N,d}$ ($d \ge 1$) of size `1 + N * (d - 1)` over every
  commutative ring.
* `Cslib.Circuits.Arithmetic.hasSymmetricDeterminantalRepresentation_diagonalPowerSum` and
  `Cslib.Circuits.Arithmetic.symmetricDeterminantalComplexity_diagonalPowerSum_le`: explicit
  transpose-symmetric determinantal representation of $F_{N,d}$ ($d \ge 1$) of size
  `1 + 2 * N * (d - 1)` over any commutative ring in which `2` is a unit.
-/

public section

namespace Cslib.Circuits.Arithmetic

open Matrix MvPolynomial

/-! ### 1. Symmetric and border determinantal complexity models -/

section Models

variable {K : Type*} [CommRing K] {σ : Type*}

/-- `f` has a transpose-symmetric determinantal representation of size `m` if `f = A.det` for a
symmetric `m × m` matrix `A` whose entries have total degree at most `1`. -/
@[expose] def HasSymmetricDeterminantalRepresentation (f : MvPolynomial σ K) (m : ℕ) : Prop :=
  ∃ A : Matrix (Fin m) (Fin m) (MvPolynomial σ K),
    A.IsSymm ∧ (∀ i j, (A i j).totalDegree ≤ 1) ∧ A.det = f

theorem HasSymmetricDeterminantalRepresentation.hasDeterminantalRepresentation
    {f : MvPolynomial σ K} {m : ℕ} (h : HasSymmetricDeterminantalRepresentation f m) :
    HasDeterminantalRepresentation f m := by
  rcases h with ⟨A, -, hdeg, hdet⟩
  exact ⟨A, hdeg, hdet⟩

/-- The transpose-symmetric determinantal complexity `\sdc(f) : ℕ∞`. -/
noncomputable def symmetricDeterminantalComplexity (f : MvPolynomial σ K) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : HasSymmetricDeterminantalRepresentation f m), (m : ℕ∞)

theorem symmetricDeterminantalComplexity_le {f : MvPolynomial σ K} {m : ℕ}
    (h : HasSymmetricDeterminantalRepresentation f m) :
    symmetricDeterminantalComplexity f ≤ m := by
  unfold symmetricDeterminantalComplexity
  exact iInf₂_le m h

theorem le_symmetricDeterminantalComplexity_iff {f : MvPolynomial σ K} {k : ℕ∞} :
    k ≤ symmetricDeterminantalComplexity f ↔
      ∀ m, HasSymmetricDeterminantalRepresentation f m → k ≤ m := by
  unfold symmetricDeterminantalComplexity
  exact le_iInf₂_iff

theorem determinantalComplexity_le_symmetricDeterminantalComplexity (f : MvPolynomial σ K) :
    determinantalComplexity f ≤ symmetricDeterminantalComplexity f := by
  exact le_symmetricDeterminantalComplexity_iff.mpr fun _ hm ↦
    determinantalComplexity_le hm.hasDeterminantalRepresentation

theorem totalDegree_le_of_hasDeterminantalRepresentation {f : MvPolynomial σ K} {m : ℕ}
    (h : HasDeterminantalRepresentation f m) : f.totalDegree ≤ m := by
  rcases h with ⟨A, hdeg, rfl⟩
  rw [Matrix.det_apply']
  refine totalDegree_finsetSum_le fun π _ ↦ (totalDegree_mul _ _).trans ?_
  rw [← map_intCast (C : K →+* MvPolynomial σ K), totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    (∑ i : Fin m, (A (π i) i).totalDegree) ≤ ∑ _i : Fin m, 1 :=
      Finset.sum_le_sum fun i _ ↦ hdeg (π i) i
    _ = m := by simp

variable [TopologicalSpace K]

/-- `f` has a border determinantal representation of size `m` if a sequence of polynomials, each
having a size-`m` determinantal representation, converges coefficientwise to `f`. -/
@[expose] def HasBorderDeterminantalRepresentation (f : MvPolynomial σ K) (m : ℕ) : Prop :=
  ∃ seq : ℕ → MvPolynomial σ K,
    (∀ j : ℕ, HasDeterminantalRepresentation (seq j) m) ∧
      ∀ α : σ →₀ ℕ, Filter.Tendsto (fun j ↦ (seq j).coeff α) Filter.atTop (nhds (f.coeff α))

theorem HasDeterminantalRepresentation.hasBorderDeterminantalRepresentation
    {f : MvPolynomial σ K} {m : ℕ} (h : HasDeterminantalRepresentation f m) :
    HasBorderDeterminantalRepresentation f m :=
  ⟨fun _ ↦ f, fun _ ↦ h, fun _ ↦ tendsto_const_nhds⟩

/-- The border determinantal complexity `\bdc(f) : ℕ∞`. -/
noncomputable def borderDeterminantalComplexity (f : MvPolynomial σ K) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : HasBorderDeterminantalRepresentation f m), (m : ℕ∞)

theorem borderDeterminantalComplexity_le {f : MvPolynomial σ K} {m : ℕ}
    (h : HasBorderDeterminantalRepresentation f m) :
    borderDeterminantalComplexity f ≤ m := by
  unfold borderDeterminantalComplexity
  exact iInf₂_le m h

theorem le_borderDeterminantalComplexity_iff {f : MvPolynomial σ K} {k : ℕ∞} :
    k ≤ borderDeterminantalComplexity f ↔
      ∀ m, HasBorderDeterminantalRepresentation f m → k ≤ m := by
  unfold borderDeterminantalComplexity
  exact le_iInf₂_iff

theorem borderDeterminantalComplexity_le_determinantalComplexity (f : MvPolynomial σ K) :
    borderDeterminantalComplexity f ≤ determinantalComplexity f := by
  exact le_determinantalComplexity_iff.mpr fun _ hm ↦
    borderDeterminantalComplexity_le hm.hasBorderDeterminantalRepresentation

/-- `f` has a border symmetric determinantal representation of size `m` if a sequence of
polynomials, each having a size-`m` symmetric determinantal representation, converges
coefficientwise to `f`. -/
@[expose] def HasBorderSymmetricDeterminantalRepresentation (f : MvPolynomial σ K) (m : ℕ) :
    Prop :=
  ∃ seq : ℕ → MvPolynomial σ K,
    (∀ j : ℕ, HasSymmetricDeterminantalRepresentation (seq j) m) ∧
      ∀ α : σ →₀ ℕ, Filter.Tendsto (fun j ↦ (seq j).coeff α) Filter.atTop (nhds (f.coeff α))

theorem HasSymmetricDeterminantalRepresentation.hasBorderSymmetricDeterminantalRepresentation
    {f : MvPolynomial σ K} {m : ℕ} (h : HasSymmetricDeterminantalRepresentation f m) :
    HasBorderSymmetricDeterminantalRepresentation f m := by
  exact ⟨fun _ ↦ f, fun _ ↦ h, fun _ ↦ tendsto_const_nhds⟩

theorem HasBorderSymmetricDeterminantalRepresentation.hasBorderDeterminantalRepresentation
    {f : MvPolynomial σ K} {m : ℕ} (h : HasBorderSymmetricDeterminantalRepresentation f m) :
    HasBorderDeterminantalRepresentation f m := by
  rcases h with ⟨seq, hsymm, htend⟩
  exact ⟨seq, fun j ↦ (hsymm j).hasDeterminantalRepresentation, htend⟩

/-- The border symmetric determinantal complexity `\bsdc(f) : ℕ∞`. -/
noncomputable def borderSymmDeterminantalComplexity (f : MvPolynomial σ K) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : HasBorderSymmetricDeterminantalRepresentation f m), (m : ℕ∞)

theorem borderSymmDeterminantalComplexity_le {f : MvPolynomial σ K} {m : ℕ}
    (h : HasBorderSymmetricDeterminantalRepresentation f m) :
    borderSymmDeterminantalComplexity f ≤ m := by
  unfold borderSymmDeterminantalComplexity
  exact iInf₂_le m h

theorem le_borderSymmDeterminantalComplexity_iff {f : MvPolynomial σ K} {k : ℕ∞} :
    k ≤ borderSymmDeterminantalComplexity f ↔
      ∀ m, HasBorderSymmetricDeterminantalRepresentation f m → k ≤ m := by
  unfold borderSymmDeterminantalComplexity
  exact le_iInf₂_iff

theorem borderSymmDeterminantalComplexity_le_symmetricDeterminantalComplexity
    (f : MvPolynomial σ K) :
    borderSymmDeterminantalComplexity f ≤ symmetricDeterminantalComplexity f := by
  exact le_symmetricDeterminantalComplexity_iff.mpr fun _ hm ↦
    borderSymmDeterminantalComplexity_le hm.hasBorderSymmetricDeterminantalRepresentation

theorem borderDeterminantalComplexity_le_borderSymmDeterminantalComplexity
    (f : MvPolynomial σ K) :
    borderDeterminantalComplexity f ≤ borderSymmDeterminantalComplexity f := by
  exact le_borderSymmDeterminantalComplexity_iff.mpr fun _ hm ↦
    borderDeterminantalComplexity_le hm.hasBorderDeterminantalRepresentation

/-- Over a Hausdorff topological commutative ring `K`, total degree is preserved by border
determinantal representations (`f.totalDegree ≤ m`). -/
theorem totalDegree_le_of_hasBorderDeterminantalRepresentation [T2Space K]
    {f : MvPolynomial σ K} {m : ℕ} (h : HasBorderDeterminantalRepresentation f m) :
    f.totalDegree ≤ m := by
  rcases h with ⟨seq, hrep, htend⟩
  rw [totalDegree, Finset.sup_le_iff]
  intro α hα
  by_contra hgt
  have hzero : ∀ j : ℕ, (seq j).coeff α = 0 := fun j ↦ by
    by_contra hne
    have hmem : α ∈ (seq j).support := mem_support_iff.mpr hne
    have hle : α.sum (fun _ k ↦ k) ≤ m :=
      (Finset.le_sup (f := fun s : σ →₀ ℕ ↦ s.sum fun _ k ↦ k) hmem).trans
        (totalDegree_le_of_hasDeterminantalRepresentation (hrep j))
    omega
  have ht0 : Filter.Tendsto (fun j ↦ (seq j).coeff α) Filter.atTop (nhds 0) := by
    simpa only [hzero] using (tendsto_const_nhds (x := (0 : K)))
  exact (mem_support_iff.mp hα) (tendsto_nhds_unique (htend α) ht0)

theorem natCast_totalDegree_le_borderDeterminantalComplexity [T2Space K] (f : MvPolynomial σ K) :
    (f.totalDegree : ℕ∞) ≤ borderDeterminantalComplexity f :=
  le_borderDeterminantalComplexity_iff.mpr fun _ hm ↦
    Nat.cast_le.mpr (totalDegree_le_of_hasBorderDeterminantalRepresentation hm)

end Models

/-! ### 2. Quadratic ordinary and symmetric determinantal representations of diagonal power sums -/

section PowerSumUpperBounds

/-- The diagonal power sum polynomial $F_{N,d} = \sum_{i=0}^{N-1} X_i^d$. -/
noncomputable def diagonalPowerSum (K : Type*) [CommSemiring K] (N d : ℕ) :
    MvPolynomial (Fin N) K :=
  ∑ i : Fin N, (X i : MvPolynomial (Fin N) K) ^ d

private def superdiagShift (R : Type*) [Zero R] [One R] (r : ℕ) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun a b ↦ if a.1 + 1 = b.1 then 1 else 0

private lemma pow_superdiagShift_apply {R : Type*} [Semiring R] (r k : ℕ) (a b : Fin r) :
    (superdiagShift R r ^ k) a b = if a.1 + k = b.1 then 1 else 0 := by
  induction k generalizing a b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    simp only [add_zero, Fin.ext_iff]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, superdiagShift, Matrix.of_apply]
    by_cases h : a.1 + (k + 1) = b.1
    · simp only [h, ↓reduceIte]
      have hlt : a.1 + k < r := by omega
      have h' : a.1 + k + 1 = b.1 := by omega
      rw [Finset.sum_eq_single ⟨a.1 + k, hlt⟩]
      · simp [h']
      · intro c _ hc
        have hne : a.1 + k ≠ c.1 := fun heq ↦ hc (Fin.ext heq.symm)
        simp [hne]
      · intro hc
        exact (hc (Finset.mem_univ _)).elim
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun c _ ↦ ?_
      by_cases hac : a.1 + k = c.1
      · have hcb : c.1 + 1 ≠ b.1 := by omega
        simp [hcb]
      · simp [hac]

private lemma pow_superdiagShift_eq_zero {R : Type*} [Semiring R] {r k : ℕ} (hk : r ≤ k) :
    superdiagShift R r ^ k = 0 := by
  ext a b
  rw [pow_superdiagShift_apply, Matrix.zero_apply]
  have hne : a.1 + k ≠ b.1 := by omega
  simp [hne]

private def upperShiftUnit {R : Type*} [Ring R] (m : ℕ) (t : R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  1 - t • superdiagShift R (m + 1)

private def upperShiftInv {R : Type*} [Semiring R] (m : ℕ) (t : R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  ∑ k ∈ Finset.range (m + 1), t ^ k • superdiagShift R (m + 1) ^ k

private lemma upperShiftUnit_mul_upperShiftInv {R : Type*} [CommRing R] (m : ℕ) (t : R) :
    upperShiftUnit m t * upperShiftInv m t = 1 := by
  rw [upperShiftUnit, upperShiftInv, sub_mul, one_mul, Finset.mul_sum]
  have hstep :
      ∑ k ∈ Finset.range (m + 1),
          (t • superdiagShift R (m + 1)) * (t ^ k • superdiagShift R (m + 1) ^ k) =
        ∑ k ∈ Finset.range (m + 1),
          t ^ (k + 1) • superdiagShift R (m + 1) ^ (k + 1) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_mul_smul_comm, ← pow_succ', ← pow_succ']
  rw [hstep, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun k ↦ t ^ k • superdiagShift R (m + 1) ^ k) (m + 1),
    pow_zero, pow_zero, one_smul, pow_superdiagShift_eq_zero le_rfl, smul_zero, sub_zero]

private lemma upperShiftInv_mul_upperShiftUnit {R : Type*} [CommRing R] (m : ℕ) (t : R) :
    upperShiftInv m t * upperShiftUnit m t = 1 := by
  rw [upperShiftUnit, upperShiftInv, mul_sub, mul_one, Finset.sum_mul]
  have hstep :
      ∑ k ∈ Finset.range (m + 1),
          (t ^ k • superdiagShift R (m + 1) ^ k) * (t • superdiagShift R (m + 1)) =
        ∑ k ∈ Finset.range (m + 1),
          t ^ (k + 1) • superdiagShift R (m + 1) ^ (k + 1) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_mul_smul_comm, ← pow_succ, ← pow_succ]
  rw [hstep, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun k ↦ t ^ k • superdiagShift R (m + 1) ^ k) (m + 1),
    pow_zero, pow_zero, one_smul, pow_superdiagShift_eq_zero le_rfl, smul_zero, sub_zero]

private lemma det_upperShiftUnit {R : Type*} [CommRing R] (m : ℕ) (t : R) :
    (upperShiftUnit m t).det = 1 := by
  have htri : (upperShiftUnit m t).IsUpperTriangular := by
    intro a b hab
    have h1 : a ≠ b := ne_of_gt hab
    have h2 : a.1 + 1 ≠ b.1 := by
      have : b.1 < a.1 := hab
      omega
    simp [upperShiftUnit, superdiagShift, h1, h2]
  rw [det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun a _ ↦ ?_
  simp [upperShiftUnit, superdiagShift]

private lemma upperShiftInv_zero_last {R : Type*} [Semiring R] (m : ℕ) (t : R) :
    upperShiftInv m t 0 (Fin.last m) = t ^ m := by
  rw [upperShiftInv, Matrix.sum_apply, Finset.sum_eq_single m]
  · simp [Matrix.smul_apply, pow_superdiagShift_apply, Fin.last]
  · intro k _ hkm
    simp [Matrix.smul_apply, pow_superdiagShift_apply, Fin.last, hkm]
  · intro hm
    exact (hm (Finset.mem_range.mpr (Nat.lt_succ_self m))).elim

private lemma totalDegree_X_le_one {K σ : Type*} [CommSemiring K] (i : σ) :
    (X i : MvPolynomial σ K).totalDegree ≤ 1 := by
  rw [totalDegree, Finset.sup_le_iff]
  intro s hs
  rw [X] at hs
  have hs1 : s = Finsupp.single i 1 := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst hs1
  simp

private lemma totalDegree_neg_eq {K σ : Type*} [CommRing K] (p : MvPolynomial σ K) :
    (-p).totalDegree = p.totalDegree := by
  have h : (-p).support = p.support := by
    ext s
    simp
  simp [totalDegree, h]

private lemma totalDegree_upperShiftUnit_X_le {K : Type*} [CommRing K] {N : ℕ} (m : ℕ)
    (i : Fin N) (a b : Fin (m + 1)) :
    (upperShiftUnit m (X i : MvPolynomial (Fin N) K) a b).totalDegree ≤ 1 := by
  simp only [upperShiftUnit, superdiagShift, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp
  · simp only [hab, ↓reduceIte, zero_sub]
    split_ifs
    · rw [mul_one, totalDegree_neg_eq]
      exact totalDegree_X_le_one i
    · simp

/-- Over every commutative ring `K`, for all `N : ℕ` and `1 ≤ d`, the diagonal power sum $F_{N,d}$
admits an ordinary determinantal representation of size `1 + N * (d - 1)`. -/
theorem hasDeterminantalRepresentation_diagonalPowerSum (K : Type*) [CommRing K] (N : ℕ) {d : ℕ}
    (hd : 1 ≤ d) :
    HasDeterminantalRepresentation (diagonalPowerSum K N d) (1 + N * (d - 1)) := by
  by_cases hd1 : d = 1
  · subst hd1
    simp only [Nat.sub_self, mul_zero, add_zero]
    refine ⟨Matrix.of fun (_ _ : Fin 1) ↦ ∑ i : Fin N, (X i : MvPolynomial (Fin N) K),
      fun _ _ ↦ by
        simpa only [of_apply] using totalDegree_finsetSum_le fun i _ ↦ totalDegree_X_le_one i, ?_⟩
    simp [det_unique, diagonalPowerSum]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
    let M : Matrix (Unit ⊕ (Fin (m + 1) × Fin N)) (Unit ⊕ (Fin (m + 1) × Fin N))
        (MvPolynomial (Fin N) K) :=
      Matrix.fromBlocks 0
        (Matrix.of fun _ (p : Fin (m + 1) × Fin N) ↦ if p.1 = 0 then X p.2 else 0)
        (Matrix.of fun (p : Fin (m + 1) × Fin N) _ ↦ if p.1 = Fin.last m then -X p.2 else 0)
        (Matrix.blockDiagonal fun i : Fin N ↦ upperShiftUnit m (X i))
    have hdetM : M.det = diagonalPowerSum K N (m + 2) := by
      let D := Matrix.blockDiagonal fun i : Fin N ↦ upperShiftUnit m (X i : MvPolynomial (Fin N) K)
      let D_inv :=
        Matrix.blockDiagonal fun i : Fin N ↦ upperShiftInv m (X i : MvPolynomial (Fin N) K)
      have hDD : D * D_inv = 1 := by
        dsimp [D, D_inv]
        rw [← blockDiagonal_mul]
        simp only [upperShiftUnit_mul_upperShiftInv]
        exact blockDiagonal_one
      have hD_invD : D_inv * D = 1 := by
        dsimp [D, D_inv]
        rw [← blockDiagonal_mul]
        simp only [upperShiftInv_mul_upperShiftUnit]
        exact blockDiagonal_one
      let _ : Invertible D := ⟨D_inv, hD_invD, hDD⟩
      have hdetD : D.det = 1 := by
        dsimp [D]
        rw [det_blockDiagonal]
        simp [det_upperShiftUnit]
      dsimp [M]
      rw [det_fromBlocks₂₂, hdetD, one_mul]
      let B : Matrix Unit (Fin (m + 1) × Fin N) (MvPolynomial (Fin N) K) :=
        Matrix.of fun _ p ↦ if p.1 = 0 then X p.2 else 0
      let C_col : Matrix (Fin (m + 1) × Fin N) Unit (MvPolynomial (Fin N) K) :=
        Matrix.of fun p _ ↦ if p.1 = Fin.last m then -X p.2 else 0
      change (0 - B * D_inv * C_col).det = diagonalPowerSum K N (m + 2)
      rw [det_unique, Matrix.sub_apply, Matrix.zero_apply, zero_sub, Matrix.mul_assoc]
      have hentry : (B * (D_inv * C_col)) default default = -diagonalPowerSum K N (m + 2) := by
        simp only [B, C_col, D_inv, Matrix.mul_apply, of_apply, Fintype.sum_prod_type_right]
        rw [diagonalPowerSum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_eq_single (0 : Fin (m + 1))]
        · simp only [↓reduceIte]
          rw [Finset.sum_eq_single i]
          · rw [Finset.sum_eq_single (Fin.last m)]
            · simp only [blockDiagonal_apply, ↓reduceIte, upperShiftInv_zero_last]
              ring
            · intro b _ hbm
              simp [hbm]
            · intro h
              exact (h (Finset.mem_univ _)).elim
          · intro j _ hji
            refine Finset.sum_eq_zero fun b _ ↦ ?_
            rw [blockDiagonal_apply_ne _ _ _ (Ne.symm hji), zero_mul]
          · intro h
            exact (h (Finset.mem_univ i)).elim
        · intro a _ ha0
          simp [ha0]
        · intro h
          exact (h (Finset.mem_univ 0)).elim
      rw [hentry, neg_neg]
    have hcard : 1 + ((m + 1) * N) = 1 + N * (m + 2 - 1) := by
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub]
      ring
    let e : Unit ⊕ (Fin (m + 1) × Fin N) ≃ Fin (1 + N * (m + 2 - 1)) :=
      ((Equiv.sumCongr finOneEquiv.symm finProdFinEquiv).trans finSumFinEquiv).trans
        (finCongr hcard)
    refine ⟨Matrix.reindex e e M, fun r c ↦ ?_, ?_⟩
    · simp only [reindex_apply, submatrix_apply]
      rcases e.symm r with (⟨⟩ | ⟨a, i⟩) <;> rcases e.symm c with (⟨⟩ | ⟨b, j⟩)
      · simp [M]
      · simp only [M, fromBlocks_apply₁₂, of_apply]
        split_ifs
        · exact totalDegree_X_le_one _
        · simp
      · simp only [M, fromBlocks_apply₂₁, of_apply]
        split_ifs
        · rw [totalDegree_neg_eq]
          exact totalDegree_X_le_one _
        · simp
      · simp only [M, fromBlocks_apply₂₂, blockDiagonal_apply]
        split_ifs
        · exact totalDegree_upperShiftUnit_X_le m i a b
        · simp
    · rw [det_reindex_self, hdetM]

/-- `\dc(F_{N,d}) ≤ 1 + N * (d - 1)` for `1 ≤ d` over every commutative ring `K`. -/
theorem determinantalComplexity_diagonalPowerSum_le (K : Type*) [CommRing K] (N : ℕ) {d : ℕ}
    (hd : 1 ≤ d) :
    determinantalComplexity (diagonalPowerSum K N d) ≤ (1 + N * (d - 1) : ℕ) :=
  determinantalComplexity_le (hasDeterminantalRepresentation_diagonalPowerSum K N hd)

private def symmShiftPairBlock {R : Type*} [Ring R] (m : ℕ) (t : R) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) R :=
  Matrix.fromBlocks 0 (upperShiftUnit m t)ᵀ (upperShiftUnit m t) 0

private def symmShiftPairBlockInv {R : Type*} [Semiring R] (m : ℕ) (t : R) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) R :=
  Matrix.fromBlocks 0 (upperShiftInv m t) (upperShiftInv m t)ᵀ 0

private lemma det_symmShiftPairBlock_eq_zero_eval {R : Type*} [CommRing R] (m : ℕ) (t : R) :
    (symmShiftPairBlock m t).det = (symmShiftPairBlock m (0 : R)).det := by
  have hu0 : upperShiftUnit m (0 : R) = 1 := by simp [upperShiftUnit]
  have hfact :
      symmShiftPairBlock m t =
        symmShiftPairBlock m (0 : R) *
          fromBlocks (upperShiftUnit m t) 0 0 (upperShiftUnit m t)ᵀ := by
    rw [symmShiftPairBlock, symmShiftPairBlock, hu0, transpose_one, fromBlocks_multiply]
    simp
  rw [hfact, det_mul, det_fromBlocks_zero₁₂, det_transpose, det_upperShiftUnit, mul_one, mul_one]

/-- Over any commutative ring `K` in which `2` is a unit, for all `N : ℕ` and `1 ≤ d`, the diagonal
power sum $F_{N,d}$ admits a transpose-symmetric determinantal representation of size
`1 + 2 * N * (d - 1)`. -/
theorem hasSymmetricDeterminantalRepresentation_diagonalPowerSum {K : Type*} [CommRing K]
    (h2 : IsUnit (2 : K)) (N : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    HasSymmetricDeterminantalRepresentation (diagonalPowerSum K N d) (1 + 2 * N * (d - 1)) := by
  by_cases hd1 : d = 1
  · subst hd1
    simp only [Nat.sub_self, mul_zero, add_zero]
    have hsymm1 :
        (Matrix.of fun (_ _ : Fin 1) ↦ ∑ i : Fin N, (X i : MvPolynomial (Fin N) K)).IsSymm :=
      Matrix.ext fun i j ↦ by rw [Subsingleton.elim i j]; rfl
    refine ⟨Matrix.of fun (_ _ : Fin 1) ↦ ∑ i : Fin N, (X i : MvPolynomial (Fin N) K), hsymm1,
      fun _ _ ↦ by
        simpa only [of_apply] using totalDegree_finsetSum_le fun i _ ↦ totalDegree_X_le_one i, ?_⟩
    simp [det_unique, diagonalPowerSum]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
    let sig : K := ((symmShiftPairBlock m (0 : K)).det) ^ N
    have hsig_sq : sig ^ 2 = 1 := by
      have h0_sq : (symmShiftPairBlock m (0 : K)).det ^ 2 = 1 := by
        have hu0 : upperShiftUnit m (0 : K) = 1 := by simp [upperShiftUnit]
        rw [sq, ← det_mul]
        have hmul : symmShiftPairBlock m (0 : K) * symmShiftPairBlock m (0 : K) = 1 := by
          rw [symmShiftPairBlock, hu0, transpose_one, fromBlocks_multiply]
          simp
        rw [hmul, det_one]
      dsimp [sig]
      rw [← pow_mul, mul_comm N 2, pow_mul, h0_sq, one_pow]
    let tau : K := -sig * (↑h2.unit⁻¹ : K)
    have h2tau : 2 * tau = -sig := by
      dsimp [tau]
      calc
        (2 : K) * (-sig * (↑h2.unit⁻¹ : K)) = -sig * ((2 : K) * (↑h2.unit⁻¹ : K)) := by ring
        _ = -sig * 1 := by rw [IsUnit.mul_val_inv h2]
        _ = -sig := mul_one _
    let w : (Fin (m + 1) ⊕ Fin (m + 1)) × Fin N → MvPolynomial (Fin N) K := fun p ↦
      match p.1 with
      | Sum.inl a => if a = 0 then C tau * X p.2 else 0
      | Sum.inr a => if a = Fin.last m then X p.2 else 0
    let M : Matrix (Unit ⊕ ((Fin (m + 1) ⊕ Fin (m + 1)) × Fin N))
        (Unit ⊕ ((Fin (m + 1) ⊕ Fin (m + 1)) × Fin N)) (MvPolynomial (Fin N) K) :=
      Matrix.fromBlocks 0
        (Matrix.of fun _ p ↦ w p)
        (Matrix.of fun p _ ↦ w p)
        (Matrix.blockDiagonal fun i : Fin N ↦ symmShiftPairBlock m (X i))
    have hsymmM : M.IsSymm := by
      dsimp [M]
      rw [IsSymm, fromBlocks_transpose, transpose_zero, blockDiagonal_transpose]
      have hC :
          (fun i : Fin N ↦ (symmShiftPairBlock m (X i : MvPolynomial (Fin N) K))ᵀ) =
            fun i : Fin N ↦ symmShiftPairBlock m (X i) := by
        funext i
        rw [symmShiftPairBlock, fromBlocks_transpose, transpose_zero, transpose_transpose]
      rw [hC]
      rfl
    have hdetM : M.det = diagonalPowerSum K N (m + 2) := by
      let C_mat :=
        Matrix.blockDiagonal fun i : Fin N ↦ symmShiftPairBlock m (X i : MvPolynomial (Fin N) K)
      let C_inv :=
        Matrix.blockDiagonal fun i : Fin N ↦ symmShiftPairBlockInv m (X i : MvPolynomial (Fin N) K)
      have hCC : C_mat * C_inv = 1 := by
        dsimp [C_mat, C_inv]
        rw [← blockDiagonal_mul]
        have h1 : ∀ i : Fin N,
            symmShiftPairBlock m (X i : MvPolynomial (Fin N) K) *
              symmShiftPairBlockInv m (X i) = 1 := fun i ↦ by
          rw [symmShiftPairBlock, symmShiftPairBlockInv, fromBlocks_multiply]
          have ht : (upperShiftUnit m (X i : MvPolynomial (Fin N) K))ᵀ *
              (upperShiftInv m (X i))ᵀ = 1 := by
            rw [← transpose_mul, upperShiftInv_mul_upperShiftUnit, transpose_one]
          simp [ht, upperShiftUnit_mul_upperShiftInv]
        simp only [h1]
        exact blockDiagonal_one
      have hC_invC : C_inv * C_mat = 1 := by
        dsimp [C_mat, C_inv]
        rw [← blockDiagonal_mul]
        have h1 : ∀ i : Fin N,
            symmShiftPairBlockInv m (X i : MvPolynomial (Fin N) K) *
              symmShiftPairBlock m (X i) = 1 := fun i ↦ by
          rw [symmShiftPairBlock, symmShiftPairBlockInv, fromBlocks_multiply]
          have ht : (upperShiftInv m (X i : MvPolynomial (Fin N) K))ᵀ *
              (upperShiftUnit m (X i))ᵀ = 1 := by
            rw [← transpose_mul, upperShiftUnit_mul_upperShiftInv, transpose_one]
          simp [ht, upperShiftInv_mul_upperShiftUnit]
        simp only [h1]
        exact blockDiagonal_one
      let _ : Invertible C_mat := ⟨C_inv, hC_invC, hCC⟩
      have hmap0 :
          (C : K →+* MvPolynomial (Fin N) K) (symmShiftPairBlock m (0 : K)).det =
            (symmShiftPairBlock m (0 : MvPolynomial (Fin N) K)).det := by
        have hmat :
            (symmShiftPairBlock m (0 : K)).map (C : K →+* MvPolynomial (Fin N) K) =
              symmShiftPairBlock m (0 : MvPolynomial (Fin N) K) := by
          have hu1 : upperShiftUnit m (0 : K) = 1 := by simp [upperShiftUnit]
          have hu2 : upperShiftUnit m (0 : MvPolynomial (Fin N) K) = 1 := by simp [upperShiftUnit]
          rw [symmShiftPairBlock, symmShiftPairBlock, hu1, hu2, transpose_one, fromBlocks_map]
          refine Matrix.ext fun r c ↦ ?_
          rcases r with (i | i) <;> rcases c with (j | j) <;> simp [Matrix.one_apply]
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hmat]
      have hdetC : C_mat.det = C sig := by
        dsimp [C_mat, sig]
        rw [det_blockDiagonal, map_pow]
        simp_rw [det_symmShiftPairBlock_eq_zero_eval, ← hmap0]
        simp [Finset.prod_const]
      dsimp [M]
      let W_row : Matrix Unit ((Fin (m + 1) ⊕ Fin (m + 1)) × Fin N) (MvPolynomial (Fin N) K) :=
        Matrix.of fun _ p ↦ w p
      let W_col : Matrix ((Fin (m + 1) ⊕ Fin (m + 1)) × Fin N) Unit (MvPolynomial (Fin N) K) :=
        Matrix.of fun p _ ↦ w p
      change (Matrix.fromBlocks 0 W_row W_col C_mat).det = _
      rw [det_fromBlocks₂₂, hdetC]
      change C sig * (0 - W_row * C_inv * W_col).det = _
      rw [det_unique, Matrix.sub_apply, Matrix.zero_apply, zero_sub, Matrix.mul_assoc]
      have hquad : (W_row * (C_inv * W_col)) default default =
          C (2 * tau) * diagonalPowerSum K N (m + 2) := by
        simp only [W_row, W_col, C_inv, Matrix.mul_apply, of_apply, Fintype.sum_prod_type_right]
        rw [diagonalPowerSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hinner :
            ∀ p : Fin (m + 1) ⊕ Fin (m + 1),
              (∑ j : Fin N, ∑ q : Fin (m + 1) ⊕ Fin (m + 1),
                  (if i = j then symmShiftPairBlockInv m (X i) p q else 0) * w (q, j)) =
                ∑ q : Fin (m + 1) ⊕ Fin (m + 1),
                  symmShiftPairBlockInv m (X i) p q * w (q, i) := fun p ↦ by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [Ne.symm hji]
          · intro h
            exact (h (Finset.mem_univ i)).elim
        simp only [blockDiagonal_apply]
        simp_rw [hinner]
        rw [Fintype.sum_sum_type]
        have hleft :
            (∑ a : Fin (m + 1),
                w (Sum.inl a, i) *
                  ∑ q : Fin (m + 1) ⊕ Fin (m + 1),
                    symmShiftPairBlockInv m (X i) (Sum.inl a) q * w (q, i)) =
              C tau * (X i : MvPolynomial (Fin N) K) ^ (m + 2) := by
          rw [Finset.sum_eq_single (0 : Fin (m + 1))]
          · rw [Fintype.sum_sum_type]
            have hl0 :
                (∑ b : Fin (m + 1),
                    symmShiftPairBlockInv m (X i) (Sum.inl 0) (Sum.inl b) *
                      w (Sum.inl b, i)) = 0 := by
              simp [symmShiftPairBlockInv]
            rw [hl0, zero_add, Finset.sum_eq_single (Fin.last m)]
            · simp only [w, ↓reduceIte, symmShiftPairBlockInv, fromBlocks_apply₁₂,
                upperShiftInv_zero_last]
              ring
            · intro b _ hbm
              simp [w, hbm]
            · intro h
              exact (h (Finset.mem_univ _)).elim
          · intro a _ ha0
            simp [w, ha0]
          · intro h
            exact (h (Finset.mem_univ 0)).elim
        have hright :
            (∑ a : Fin (m + 1),
                w (Sum.inr a, i) *
                  ∑ q : Fin (m + 1) ⊕ Fin (m + 1),
                    symmShiftPairBlockInv m (X i) (Sum.inr a) q * w (q, i)) =
              C tau * (X i : MvPolynomial (Fin N) K) ^ (m + 2) := by
          rw [Finset.sum_eq_single (Fin.last m)]
          · rw [Fintype.sum_sum_type]
            have hr0 :
                (∑ b : Fin (m + 1),
                    symmShiftPairBlockInv m (X i) (Sum.inr (Fin.last m)) (Sum.inr b) *
                      w (Sum.inr b, i)) = 0 := by
              simp [symmShiftPairBlockInv]
            rw [hr0, add_zero, Finset.sum_eq_single (0 : Fin (m + 1))]
            · simp only [w, ↓reduceIte, symmShiftPairBlockInv, fromBlocks_apply₂₁, transpose_apply,
                upperShiftInv_zero_last]
              ring
            · intro b _ hb0
              simp [w, hb0]
            · intro h
              exact (h (Finset.mem_univ 0)).elim
          · intro a _ hal
            simp [w, hal]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        rw [hleft, hright]
        simp only [tau, map_mul, map_neg, map_ofNat]
        ring
      rw [hquad, h2tau]
      have hcoef : -sig * -sig = 1 := by
        calc
          -sig * -sig = sig ^ 2 := by ring
          _ = 1 := hsig_sq
      calc
        C sig * -(C (-sig) * diagonalPowerSum K N (m + 2))
            = C (-sig * -sig) * diagonalPowerSum K N (m + 2) := by
          simp only [map_mul, map_neg]
          ring
        _ = diagonalPowerSum K N (m + 2) := by rw [hcoef, map_one, one_mul]
    have hcard : 1 + ((m + 1 + (m + 1)) * N) = 1 + 2 * N * (m + 2 - 1) := by
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub]
      ring
    let e : Unit ⊕ ((Fin (m + 1) ⊕ Fin (m + 1)) × Fin N) ≃ Fin (1 + 2 * N * (m + 2 - 1)) :=
      ((Equiv.sumCongr finOneEquiv.symm
          ((Equiv.prodCongrLeft fun _ ↦ finSumFinEquiv).trans finProdFinEquiv)).trans
        finSumFinEquiv).trans (finCongr hcard)
    refine ⟨Matrix.reindex e e M,
      Matrix.ext fun r c ↦ by
        simpa only [transpose_apply, reindex_apply, submatrix_apply] using
          hsymmM.apply (e.symm r) (e.symm c),
      fun r c ↦ ?_, ?_⟩
    · simp only [reindex_apply, submatrix_apply]
      rcases e.symm r with (⟨⟩ | ⟨a | a, i⟩) <;> rcases e.symm c with (⟨⟩ | ⟨b | b, j⟩)
      · simp [M]
      · simp only [M, w, fromBlocks_apply₁₂, of_apply]
        split_ifs
        · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X_le_one])
        · simp
      · simp only [M, w, fromBlocks_apply₁₂, of_apply]
        split_ifs
        · exact totalDegree_X_le_one _
        · simp
      · simp only [M, w, fromBlocks_apply₂₁, of_apply]
        split_ifs
        · exact (totalDegree_mul _ _).trans (by simp [totalDegree_X_le_one])
        · simp
      · simp [M, fromBlocks_apply₂₂, blockDiagonal_apply, symmShiftPairBlock]
      · simp only [M, fromBlocks_apply₂₂, blockDiagonal_apply]
        split_ifs
        · simpa [symmShiftPairBlock] using totalDegree_upperShiftUnit_X_le m i b a
        · simp
      · simp only [M, w, fromBlocks_apply₂₁, of_apply]
        split_ifs
        · exact totalDegree_X_le_one _
        · simp
      · simp only [M, fromBlocks_apply₂₂, blockDiagonal_apply]
        split_ifs
        · simpa [symmShiftPairBlock] using totalDegree_upperShiftUnit_X_le m i a b
        · simp
      · simp [M, fromBlocks_apply₂₂, blockDiagonal_apply, symmShiftPairBlock]
    · rw [det_reindex_self, hdetM]

/-- `\sdc(F_{N,d}) ≤ 1 + 2 * N * (d - 1)` for `1 ≤ d` over any commutative ring `K` in which `2` is
a unit. -/
theorem symmetricDeterminantalComplexity_diagonalPowerSum_le {K : Type*} [CommRing K]
    (h2 : IsUnit (2 : K)) (N : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    symmetricDeterminantalComplexity (diagonalPowerSum K N d) ≤ (1 + 2 * N * (d - 1) : ℕ) :=
  symmetricDeterminantalComplexity_le
    (hasSymmetricDeterminantalRepresentation_diagonalPowerSum h2 N hd)

end PowerSumUpperBounds

end Cslib.Circuits.Arithmetic
