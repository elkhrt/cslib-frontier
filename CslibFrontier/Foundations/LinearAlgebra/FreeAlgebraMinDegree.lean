/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.FreeAlgebra
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-!
# Homogeneous Projections and Minimum Degree in Free Algebras

This module defines the homogeneous degree-`d` projection linear map
`CslibFrontier.FreeAlgebra.homogeneousComponent` and the minimum monomial degree
`CslibFrontier.FreeAlgebra.minDeg` on the free associative algebra `FreeAlgebra R X`, and proves
additivity of `minDeg` on products over a ring without zero divisors. All results are proved under
standard Lean axioms.

## Main definitions

* `CslibFrontier.FreeAlgebra.homogeneousComponent`: the `R`-linear projection onto the homogeneous
  degree-`d` subspace of `FreeAlgebra R X`.
* `CslibFrontier.FreeAlgebra.minDeg`: the minimum word length occurring with nonzero coefficient in
  a
  noncommutative polynomial (`0` for the zero polynomial).

## Main results

* `CslibFrontier.FreeAlgebra.coeff_homogeneousComponent`: coordinates of a homogeneous projection.
* `CslibFrontier.FreeAlgebra.isHomogeneous_homogeneousComponent`: the image of `homogeneousComponent
  d`
  is homogeneous of degree `d`.
* `CslibFrontier.FreeAlgebra.homogeneousComponent_eq_self_of_isHomogeneous`: `homogeneousComponent
  d`
  acts as the identity on homogeneous degree-`d` polynomials.
* `CslibFrontier.FreeAlgebra.mul_ne_zero_of_ne_zero`: `FreeAlgebra R X` has no zero divisors
  whenever
  `R` has no zero divisors.
* `CslibFrontier.FreeAlgebra.minDeg_mul`: `minDeg (f * g) = minDeg f + minDeg g` for nonzero `f, g`
  when `R` has no zero divisors.
* `CslibFrontier.FreeAlgebra.homogeneousComponent_eq_zero_of_lt_minDeg`: `homogeneousComponent d f =
  0`
  whenever `d < minDeg f`.
-/

public section

namespace CslibFrontier.FreeAlgebra

open _root_.FreeAlgebra

section HomogeneousComponent

variable {R : Type*} [CommSemiring R] {X : Type*}

/-- The `R`-linear projection onto the homogeneous degree-`d` component of `FreeAlgebra R X`. -/
noncomputable def homogeneousComponent (d : ℕ) : FreeAlgebra R X →ₗ[R] FreeAlgebra R X :=
  (basisFreeMonoid R X).constr R fun w ↦
    if w.toList.length = d then basisFreeMonoid R X w else 0

/-- The coefficient of a word `w` in `homogeneousComponent d f` is `coeff w f` if `|w| = d` and
`0` otherwise. -/
@[simp]
theorem coeff_homogeneousComponent (d : ℕ) (w : FreeMonoid X) (f : FreeAlgebra R X) :
    _root_.FreeAlgebra.coeff w (homogeneousComponent d f) =
      if w.toList.length = d then _root_.FreeAlgebra.coeff w f else 0 := by
  let lhs : FreeAlgebra R X →ₗ[R] R := (_root_.FreeAlgebra.coeff w).comp (homogeneousComponent d)
  let rhs : FreeAlgebra R X →ₗ[R] R :=
    if w.toList.length = d then _root_.FreeAlgebra.coeff w else 0
  have h : lhs = rhs := by
    apply (basisFreeMonoid R X).ext
    intro u
    change _root_.FreeAlgebra.coeff w (homogeneousComponent d (basisFreeMonoid R X u)) = rhs _
    rw [homogeneousComponent, Module.Basis.constr_basis]
    by_cases hu : u.toList.length = d <;> by_cases hw : w.toList.length = d
    · simp [rhs, hu, hw]
    · simp only [rhs, hu, hw, ↓reduceIte, LinearMap.zero_apply]
      rw [basisFreeMonoid_apply, coeff_lift_ι]
      exact Finsupp.single_eq_of_ne (fun h' ↦ hw (h' ▸ hu))
    · simp only [rhs, hu, hw, ↓reduceIte, map_zero]
      rw [basisFreeMonoid_apply, coeff_lift_ι]
      symm
      exact Finsupp.single_eq_of_ne (by rintro rfl; exact hu hw)
    · simp [rhs, hu, hw]
  have hf := DFunLike.congr_fun h f
  change _root_.FreeAlgebra.coeff w (homogeneousComponent d f) = rhs f at hf
  rw [hf]
  by_cases hw : w.toList.length = d <;> simp [rhs, hw]

/-- `homogeneousComponent d f` is homogeneous of degree `d`. -/
theorem isHomogeneous_homogeneousComponent (d : ℕ) (f : FreeAlgebra R X) :
    (homogeneousComponent d f).IsHomogeneous d := by
  intro w hw
  rw [coeff_homogeneousComponent] at hw
  by_contra hne
  simp [hne] at hw

/-- `homogeneousComponent d` fixes every homogeneous polynomial of degree `d`. -/
theorem homogeneousComponent_eq_self_of_isHomogeneous {d : ℕ} {f : FreeAlgebra R X}
    (hf : f.IsHomogeneous d) : homogeneousComponent d f = f := by
  apply ext_coeff
  intro w
  rw [coeff_homogeneousComponent]
  split_ifs with hw
  · rfl
  · exact (hf.coeff_eq_zero hw).symm

/-- `homogeneousComponent d` is idempotent. -/
@[simp]
theorem homogeneousComponent_idem (d : ℕ) (f : FreeAlgebra R X) :
    homogeneousComponent d (homogeneousComponent d f) = homogeneousComponent d f :=
  homogeneousComponent_eq_self_of_isHomogeneous (isHomogeneous_homogeneousComponent d f)

/-- `homogeneousComponent d f = 0` if every word of length `d` has zero coefficient in `f`. -/
theorem homogeneousComponent_eq_zero_of_forall_coeff_eq_zero {d : ℕ} {f : FreeAlgebra R X}
    (h : ∀ w : FreeMonoid X, w.toList.length = d → _root_.FreeAlgebra.coeff w f = 0) :
    homogeneousComponent d f = 0 := by
  apply ext_coeff
  intro w
  rw [coeff_homogeneousComponent, map_zero]
  split_ifs with hw
  · exact h w hw
  · rfl

end HomogeneousComponent

section MinDeg

variable {R : Type*} [CommSemiring R] {X : Type*}

/-- The minimum degree (word length) of a monomial appearing with nonzero coefficient in
`f : FreeAlgebra R X`, defined as `0` when `f = 0`. -/
noncomputable def minDeg (f : FreeAlgebra R X) : ℕ :=
  sInf { d : ℕ | ∃ w : FreeMonoid X, w.toList.length = d ∧ _root_.FreeAlgebra.coeff w f ≠ 0 }

/-- The minimum degree of `0` is `0`. -/
@[simp]
theorem minDeg_zero : minDeg (0 : FreeAlgebra R X) = 0 := by
  simp [minDeg]

/-- Every nonzero polynomial in `FreeAlgebra R X` has a monomial of length `minDeg f` with nonzero
coefficient. -/
theorem exists_coeff_ne_zero_minDeg {f : FreeAlgebra R X} (hf : f ≠ 0) :
    ∃ w : FreeMonoid X, w.toList.length = minDeg f ∧ _root_.FreeAlgebra.coeff w f ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_coeff_ne_zero hf
  exact Nat.sInf_mem (s := { d : ℕ | ∃ u : FreeMonoid X,
    u.toList.length = d ∧ _root_.FreeAlgebra.coeff u f ≠ 0 }) ⟨w.toList.length, w, rfl, hw⟩

/-- Every monomial occurring in `f` has length at least `minDeg f`. -/
theorem minDeg_le_length {f : FreeAlgebra R X} {w : FreeMonoid X}
    (hw : _root_.FreeAlgebra.coeff w f ≠ 0) : minDeg f ≤ w.toList.length := by
  exact Nat.sInf_le (s := { d : ℕ | ∃ u : FreeMonoid X,
    u.toList.length = d ∧ _root_.FreeAlgebra.coeff u f ≠ 0 }) ⟨w, rfl, hw⟩

/-- Every word of length strictly less than `minDeg f` has zero coefficient in `f`. -/
theorem coeff_eq_zero_of_lt_minDeg {f : FreeAlgebra R X} {w : FreeMonoid X}
    (hw : w.toList.length < minDeg f) : _root_.FreeAlgebra.coeff w f = 0 := by
  by_contra hne
  exact absurd (minDeg_le_length hne) (not_le.mpr hw)

/-- Characterization of lower bounds on `minDeg f` for nonzero `f`. -/
theorem le_minDeg_iff {f : FreeAlgebra R X} (hf : f ≠ 0) {d : ℕ} :
    d ≤ minDeg f ↔ ∀ w : FreeMonoid X, _root_.FreeAlgebra.coeff w f ≠ 0 → d ≤ w.toList.length := by
  constructor
  · intro hd w hw
    exact hd.trans (minDeg_le_length hw)
  · intro h
    obtain ⟨w, hlen, hw⟩ := exists_coeff_ne_zero_minDeg hf
    rw [← hlen]
    exact h w hw

/-- A nonzero homogeneous polynomial of degree `d` has minimum degree `d`. -/
theorem minDeg_eq_of_isHomogeneous {f : FreeAlgebra R X} {d : ℕ} (hf : f ≠ 0)
    (hd : f.IsHomogeneous d) : minDeg f = d := by
  obtain ⟨w, hlen, hw⟩ := exists_coeff_ne_zero_minDeg hf
  exact hlen.symm.trans (hd w hw)

/-- If `d < minDeg f`, then the homogeneous degree-`d` component of `f` vanishes. -/
theorem homogeneousComponent_eq_zero_of_lt_minDeg {f : FreeAlgebra R X} {d : ℕ}
    (hd : d < minDeg f) : homogeneousComponent d f = 0 :=
  homogeneousComponent_eq_zero_of_forall_coeff_eq_zero fun _ hw ↦
    coeff_eq_zero_of_lt_minDeg (hw.symm ▸ hd)

/-- In `FreeAlgebra R X` over a ring without zero divisors, the product of two nonzero elements is
nonzero and its minimum degree is the sum of their minimum degrees. -/
theorem mul_ne_zero_and_minDeg_mul [NoZeroDivisors R] {f g : FreeAlgebra R X}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 ∧ minDeg (f * g) = minDeg f + minDeg g := by
  obtain ⟨u, hu_len, hu_nz⟩ := exists_coeff_ne_zero_minDeg hf
  obtain ⟨v, hv_len, hv_nz⟩ := exists_coeff_ne_zero_minDeg hg
  have hcoeff_uv : _root_.FreeAlgebra.coeff (u * v) (f * g) =
      _root_.FreeAlgebra.coeff u f * _root_.FreeAlgebra.coeff v g := by
    rw [coeff_mul, Finset.sum_eq_single (minDeg f)]
    · have htake : FreeMonoid.ofList ((u * v).toList.take (minDeg f)) = u := by
        rw [FreeMonoid.toList_mul, ← hu_len, List.take_left, FreeMonoid.ofList_toList]
      have hdrop : FreeMonoid.ofList ((u * v).toList.drop (minDeg f)) = v := by
        rw [FreeMonoid.toList_mul, ← hu_len, List.drop_left, FreeMonoid.ofList_toList]
      rw [htake, hdrop]
    · intro i hi hne
      by_cases hlt : i < minDeg f
      · have hzero : _root_.FreeAlgebra.coeff (FreeMonoid.ofList ((u * v).toList.take i)) f = 0 :=
          coeff_eq_zero_of_lt_minDeg (by
            simp only [List.length_take]
            exact lt_of_le_of_lt (Nat.min_le_left _ _) hlt)
        rw [hzero, zero_mul]
      · have hgt : minDeg f < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
        have hlen_uv : (u * v).toList.length = minDeg f + minDeg g := by
          rw [FreeMonoid.toList_mul, List.length_append, hu_len, hv_len]
        have hzero : _root_.FreeAlgebra.coeff (FreeMonoid.ofList ((u * v).toList.drop i)) g = 0 :=
          coeff_eq_zero_of_lt_minDeg (by
            simp only [List.length_drop, hlen_uv]
            simp only [Finset.mem_range, hlen_uv] at hi
            omega)
        rw [hzero, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_range, FreeMonoid.toList_mul, List.length_append, hu_len, hv_len]
      omega
  have hprod_nz : _root_.FreeAlgebra.coeff (u * v) (f * g) ≠ 0 := by
    rw [hcoeff_uv]
    exact mul_ne_zero hu_nz hv_nz
  have hfg_ne : f * g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hprod_nz
    exact hprod_nz rfl
  refine ⟨hfg_ne, le_antisymm ?_ ?_⟩
  · have hle := minDeg_le_length hprod_nz
    rwa [FreeMonoid.toList_mul, List.length_append, hu_len, hv_len] at hle
  · rw [le_minDeg_iff hfg_ne]
    intro w hw
    rw [coeff_mul] at hw
    obtain ⟨i, hi, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have h1 := minDeg_le_length (left_ne_zero_of_mul hterm)
    have h2 := minDeg_le_length (right_ne_zero_of_mul hterm)
    simp only [List.length_take, List.length_drop] at h1 h2
    simp only [Finset.mem_range] at hi
    omega

/-- In `FreeAlgebra R X` over a ring without zero divisors, the product of nonzero elements is
nonzero. -/
theorem mul_ne_zero_of_ne_zero [NoZeroDivisors R] {f g : FreeAlgebra R X}
    (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 :=
  (mul_ne_zero_and_minDeg_mul hf hg).1

/-- Minimum degree is additive on products of nonzero elements in `FreeAlgebra R X` over a ring
without zero divisors. -/
theorem minDeg_mul [NoZeroDivisors R] {f g : FreeAlgebra R X} (hf : f ≠ 0) (hg : g ≠ 0) :
    minDeg (f * g) = minDeg f + minDeg g :=
  (mul_ne_zero_and_minDeg_mul hf hg).2

/-- A product of `r` nonzero factors in `FreeAlgebra R X` (over a nontrivial ring without zero
divisors), each of minimum degree at least `1`, is nonzero and has minimum degree at least `r`. -/
theorem listProd_ne_zero_and_length_le_minDeg [Nontrivial R] [NoZeroDivisors R]
    (l : List (FreeAlgebra R X)) (hl : ∀ p ∈ l, p ≠ 0 ∧ 1 ≤ minDeg p) :
    l.prod ≠ 0 ∧ l.length ≤ minDeg l.prod := by
  induction l with
  | nil =>
    refine ⟨?_, by simp⟩
    intro h0
    have h1 := congrArg (_root_.FreeAlgebra.coeff (1 : FreeMonoid X)) h0
    simp [coeff_one] at h1
  | cons p ps ih =>
    have hp := hl p (List.mem_cons_self ..)
    have hps := ih (fun q hq ↦ hl q (List.mem_cons_of_mem p hq))
    rw [List.prod_cons, List.length_cons]
    refine ⟨mul_ne_zero_of_ne_zero hp.1 hps.1, ?_⟩
    rw [minDeg_mul hp.1 hps.1]
    omega

end MinDeg

end CslibFrontier.FreeAlgebra
