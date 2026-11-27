/-
Copyright (c) 2026 The CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Degeneration
public import Mathlib.Order.Filter.Cofinite

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Lagrange

/-!
# Quantitative Border Rank, Degeneration Order, Error Degree, and First-Order Debordering

This module extends `CslibFrontier.Foundations.LinearAlgebra.Tensor.Degeneration` with the
quantitative algebraic invariants of a three-tensor `T : Cslib.Tensor K X Y Z`—its *border rank*
`borderRank T`, *degeneration order* `degenOrder T`, and *error degree* `errorDeg T`—together with
polynomial witness truncation, the bound `errorDeg T ≤ 2 * degenOrder T`, arbitrary-characteristic
Lagrange interpolation debordering `Rank ((errorDeg T + 1) * borderRank T) T`, the frontal-slice
simultaneous-diagonalization characterization of tensor rank, the first-order noncommutative
word-linearity identity `(M + N) ^ i = M ^ i + ∑_{k < i} M ^ k * N * M ^ (i - 1 - k)` when
`N * M ^ k * N = 0`, and the exact strict border-rank separation on the three-qubit `W`-state.

## Main definitions

* `CslibFrontier.Tensor.borderRank`: minimum `r : ℕ` such that `Cslib.Tensor.IsDegen h T (unit r)`
  for some `h : ℕ`.
* `CslibFrontier.Tensor.degenOrder`: minimum `h : ℕ` such that
  `Cslib.Tensor.IsDegen h T (unit (borderRank T))`.
* `CslibFrontier.Tensor.HasErrorDeg`, `CslibFrontier.Tensor.errorDeg`: polynomial approximation
  curves `P : Cslib.Tensor K[X] X Y Z` with `P(0) = T`, degree at most `d`, and cofinite
  evaluations of rank at most `r`, and the minimum such `d` at `r = borderRank T`.
* `CslibFrontier.Tensor.ofSlices`: three-tensor assembled from frontal matrix slices
  `S : Z → Matrix X Y K`.
* `CslibFrontier.Tensor.wState3`: the three-qubit `W`-state tensor on `Fin 2 × Fin 2 × Fin 2`.

## Main results

* `CslibFrontier.Tensor.rank_card_prod`, `CslibFrontier.Tensor.borderRank_le_iff`,
  `CslibFrontier.Tensor.isDegen_borderRank_degenOrder`: attainment and basic inequalities for
  `borderRank` and `degenOrder`.
* `CslibFrontier.Tensor.borderRank_le_of_isRestriction`,
  `CslibFrontier.Tensor.borderRank_le_of_isDegen`,
  `CslibFrontier.Tensor.borderRank_swap12`, `CslibFrontier.Tensor.borderRank_swap23`,
  `CslibFrontier.Tensor.borderRank_swap13`, `CslibFrontier.Tensor.borderRank_tprod_le`:
  monotonicity under restrictions and degenerations, leg-exchange symmetry, and submultiplicativity
  under tensor products.
* `CslibFrontier.Tensor.hasErrorDeg_two_mul_of_isDegen`,
  `CslibFrontier.Tensor.errorDeg_le_two_mul_degenOrder`: truncating degeneration encoders/decoder
  modulo `X ^ (h + 1)` yields an error-degree curve of degree at most `2 * h`.
* `CslibFrontier.Tensor.rank_of_hasErrorDeg`,
  `CslibFrontier.Tensor.rank_errorDeg_add_one_mul_borderRank`,
  `CslibFrontier.Tensor.rank_two_mul_degenOrder_add_one_mul_borderRank`: Lagrange interpolation
  debordering over any infinite field `K` (of arbitrary characteristic).
* `CslibFrontier.Tensor.rank_ofSlices_iff`: frontal-slice characterization
  `Rank r (ofSlices S) ↔ ∃ A B d, ∀ z, S z = A * diagonal (d z) * B`.
* `CslibFrontier.Tensor.add_pow_eq_add_sum_of_sandwich_eq_zero`: first-order expansion of
  `(M + N) ^ i` in any ring whenever `N * M ^ k * N = 0` for `k + 2 ≤ n`.
* `CslibFrontier.Tensor.borderRank_wState3`, `CslibFrontier.Tensor.degenOrder_wState3`,
  `CslibFrontier.Tensor.errorDeg_wState3`: exact values `borderRank = 2`, `degenOrder = 1`, and
  `errorDeg = 1` (with `¬ Rank 2` and `Rank 3`) for the three-qubit `W`-state over any infinite
  field.
-/

public section

namespace CslibFrontier.Tensor

open Cslib Cslib.Tensor Finset Matrix Polynomial

section BorderRank

variable {K X Y Z X' Y' Z' : Type*} [CommRing K]

/-- Evaluation of `restrict α β γ (unit r)` as an `r`-term sum of rank-one outer products. -/
theorem restrict_unit_apply {R : Type*} [CommSemiring R] {r : ℕ}
    (α : Matrix (Fin r) X R) (β : Matrix (Fin r) Y R) (γ : Matrix Z (Fin r) R)
    (x : X) (y : Y) (z : Z) :
    Cslib.Tensor.restrict α β γ (unit r) x y z = ∑ t : Fin r, α t x * β t y * γ z t := by
  simp only [Cslib.Tensor.restrict, unit_apply, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single t]
    · simp [mul_comm, mul_left_comm]
    · intro k _ hkt; simp [hkt.symm]
    · intro h; exact absurd (Finset.mem_univ t) h
  · intro j _ hjt
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    simp [hjt.symm]
  · intro h; exact absurd (Finset.mem_univ t) h

/-- Every finite three-tensor over a commutative semiring has rank at most
`card X * card Y * card Z`. -/
theorem rank_card_prod {R : Type*} [CommSemiring R] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor R X Y Z) :
    Rank (Fintype.card X * Fintype.card Y * Fintype.card Z) T := by
  classical
  have hcard : Fintype.card (X × Y × Z) = Fintype.card X * Fintype.card Y * Fintype.card Z := by
    simp [Fintype.card_prod, mul_assoc]
  let e : Fin (Fintype.card X * Fintype.card Y * Fintype.card Z) ≃ X × Y × Z :=
    (finCongr hcard.symm).trans (Fintype.equivFin (X × Y × Z)).symm
  refine ⟨Matrix.of fun t x ↦ if x = (e t).1 then T (e t).1 (e t).2.1 (e t).2.2 else 0,
    Matrix.of fun t y ↦ if y = (e t).2.1 then 1 else 0,
    Matrix.of fun z t ↦ if z = (e t).2.2 then 1 else 0, ?_⟩
  funext x y z
  rw [restrict_unit_apply]
  simp only [Matrix.of_apply]
  rw [Equiv.sum_comp e fun p : X × Y × Z ↦
    (if x = p.1 then T p.1 p.2.1 p.2.2 else 0) * (if y = p.2.1 then 1 else 0) *
      (if z = p.2.2 then 1 else 0)]
  rw [Finset.sum_eq_single (x, y, z)]
  · simp
  · rintro ⟨x', y', z'⟩ _ hne
    by_cases hx : x = x'
    · subst hx
      by_cases hy : y = y'
      · subst hy
        have hz : z ≠ z' := fun hz ↦ hne (by subst hz; rfl)
        simp [hz]
      · simp [hy]
    · simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Monotonicity of `Rank r T` in the rank bound `r`. -/
theorem rank_mono {R : Type*} [CommSemiring R] {r s : ℕ} {T : Cslib.Tensor R X Y Z}
    (hr : Rank r T) (hrs : r ≤ s) : Rank s T := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
  obtain ⟨α, β, γ, rfl⟩ := hr
  refine ⟨Matrix.of fun t x ↦ Fin.addCases (fun i ↦ α i x) (fun (_ : Fin k) ↦ 0) t,
    Matrix.of fun t y ↦ Fin.addCases (fun i ↦ β i y) (fun (_ : Fin k) ↦ 0) t,
    Matrix.of fun z t ↦ Fin.addCases (γ z) (fun (_ : Fin k) ↦ 0) t, ?_⟩
  funext x y z
  rw [restrict_unit_apply, restrict_unit_apply, Fin.sum_univ_add]
  simp

/-- Monotonicity of `IsDegen h T (unit r)` in the unit-tensor size `r`. -/
theorem isDegen_unit_mono {h r s : ℕ} {T : Cslib.Tensor K X Y Z}
    (hr : IsDegen h T (unit r)) (hrs : r ≤ s) : IsDegen h T (unit s) := by
  have hunit : IsRestriction (unit r : Cslib.Tensor K _ _ _) (unit s) :=
    rank_mono (IsRestriction.refl (unit r)) hrs
  simpa using hr.trans (IsDegen.of_isRestriction hunit)

/-- Every finite three-tensor admits a degeneration from some unit tensor. -/
theorem exists_isDegen_unit [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) :
    ∃ r h : ℕ, IsDegen h T (unit r) :=
  ⟨_, 0, IsDegen.of_isRestriction (rank_card_prod T)⟩

/-- Algebraic **border rank** of a finite three-tensor `T`: the least `r : ℕ` such that `T` is a
degeneration (of some order `h`) of the unit tensor `unit r`. -/
noncomputable def borderRank [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) : ℕ :=
  sInf {r : ℕ | ∃ h : ℕ, IsDegen h T (unit r)}

/-- Every finite three-tensor is a degeneration of `unit (borderRank T)`. -/
theorem exists_isDegen_borderRank [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) :
    ∃ h : ℕ, IsDegen h T (unit (borderRank T)) := by
  have hne : ({r : ℕ | ∃ h : ℕ, IsDegen h T (unit r)}).Nonempty := exists_isDegen_unit T
  exact Nat.sInf_mem hne

/-- A degeneration `IsDegen h T (unit r)` gives `borderRank T ≤ r`. -/
theorem borderRank_le_of_isDegen_unit [Fintype X] [Fintype Y] [Fintype Z] {h r : ℕ}
    {T : Cslib.Tensor K X Y Z} (hT : IsDegen h T (unit r)) :
    borderRank T ≤ r :=
  Nat.sInf_le ⟨h, hT⟩

/-- Characterization of bounded algebraic border rank. -/
theorem borderRank_le_iff [Fintype X] [Fintype Y] [Fintype Z] {T : Cslib.Tensor K X Y Z} {r : ℕ} :
    borderRank T ≤ r ↔ ∃ h : ℕ, IsDegen h T (unit r) :=
  ⟨fun hr ↦ let ⟨h, hh⟩ := exists_isDegen_borderRank T; ⟨h, isDegen_unit_mono hh hr⟩,
   fun ⟨_, hh⟩ ↦ borderRank_le_of_isDegen_unit hh⟩

/-- Exact rank bounds border rank from above. -/
theorem borderRank_le_of_rank [Fintype X] [Fintype Y] [Fintype Z] {r : ℕ}
    {T : Cslib.Tensor K X Y Z} (hT : Rank r T) :
    borderRank T ≤ r :=
  borderRank_le_of_isDegen_unit (IsDegen.of_isRestriction hT)

/-- The border rank of the zero tensor is `0`. -/
@[simp]
theorem borderRank_zero [Fintype X] [Fintype Y] [Fintype Z] :
    borderRank (0 : Cslib.Tensor K X Y Z) = 0 := by
  refine Nat.eq_zero_of_le_zero (borderRank_le_of_rank ⟨0, 0, 0, ?_⟩)
  funext x y z; simp [restrict_unit_apply]

/-- A tensor has border rank `0` if and only if it is zero. -/
theorem borderRank_eq_zero_iff [Fintype X] [Fintype Y] [Fintype Z] {T : Cslib.Tensor K X Y Z} :
    borderRank T = 0 ↔ T = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ borderRank_zero⟩
  obtain ⟨h, α, β, γ, E, hw⟩ := borderRank_le_iff.mp h0.le
  funext x y z
  have hxy := congrArg (fun p : K[X] ↦ p.coeff h) (congrFun (congrFun (congrFun hw x) y) z)
  have hlhs : Cslib.Tensor.restrict α β γ ((unit 0).map C) x y z = 0 := by
    simp [Cslib.Tensor.restrict]
  rw [hlhs] at hxy
  simpa [Polynomial.coeff_X_pow_mul'] using hxy.symm

/-- Border rank is monotone along degenerations. -/
theorem borderRank_le_of_isDegen [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ}
    {T : Cslib.Tensor K X Y Z} {S : Cslib.Tensor K X' Y' Z'} (hTS : IsDegen h T S) :
    borderRank T ≤ borderRank S := by
  obtain ⟨k, hS⟩ := exists_isDegen_borderRank S
  exact borderRank_le_of_isDegen_unit (hTS.trans hS)

/-- Border rank is monotone along restrictions. -/
theorem borderRank_le_of_isRestriction [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Cslib.Tensor K X Y Z} {S : Cslib.Tensor K X' Y' Z'} (hTS : IsRestriction T S) :
    borderRank T ≤ borderRank S :=
  borderRank_le_of_isDegen (IsDegen.of_isRestriction hTS)

private lemma borderRank_swap12_le [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) : borderRank (swap12 T) ≤ borderRank T := by
  obtain ⟨h, hh⟩ := exists_isDegen_borderRank T
  have hs : swap12 (unit (borderRank T) : Cslib.Tensor K _ _ _) = unit (borderRank T) := by
    funext i j k; simp only [swap12, unit_apply]; split_ifs <;> simp_all
  exact borderRank_le_of_isDegen_unit (hs ▸ hh.swap12)

/-- Border rank is invariant under exchanging the two input legs. -/
@[simp]
theorem borderRank_swap12 [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) :
    borderRank (swap12 T) = borderRank T :=
  le_antisymm (borderRank_swap12_le T) (borderRank_swap12_le (swap12 T))

private lemma borderRank_swap23_le [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) : borderRank (swap23 T) ≤ borderRank T := by
  obtain ⟨h, hh⟩ := exists_isDegen_borderRank T
  have hs : swap23 (unit (borderRank T) : Cslib.Tensor K _ _ _) = unit (borderRank T) := by
    funext i j k; simp only [swap23, unit_apply]; split_ifs <;> simp_all
  exact borderRank_le_of_isDegen_unit (hs ▸ hh.swap23)

/-- Border rank is invariant under exchanging the second and third legs. -/
@[simp]
theorem borderRank_swap23 [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) :
    borderRank (swap23 T) = borderRank T :=
  le_antisymm (borderRank_swap23_le T) (borderRank_swap23_le (swap23 T))

private lemma borderRank_swap13_le [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) : borderRank (swap13 T) ≤ borderRank T := by
  obtain ⟨h, hh⟩ := exists_isDegen_borderRank T
  have hs : swap13 (unit (borderRank T) : Cslib.Tensor K _ _ _) = unit (borderRank T) := by
    funext i j k; simp only [swap13, unit_apply]; split_ifs <;> simp_all
  exact borderRank_le_of_isDegen_unit (hs ▸ hh.swap13)

/-- Border rank is invariant under exchanging the first and third legs. -/
@[simp]
theorem borderRank_swap13 [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) :
    borderRank (swap13 T) = borderRank T :=
  le_antisymm (borderRank_swap13_le T) (borderRank_swap13_le (swap13 T))

/-- Border rank is submultiplicative under tensor products. -/
theorem borderRank_tprod_le [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Cslib.Tensor K X Y Z) (S : Cslib.Tensor K X' Y' Z') :
    borderRank (tprod T S) ≤ borderRank T * borderRank S := by
  obtain ⟨h₁, hT⟩ := exists_isDegen_borderRank T
  obtain ⟨h₂, hS⟩ := exists_isDegen_borderRank S
  have hprod := hT.tprod hS
  let e : Fin (borderRank T) × Fin (borderRank S) ≃ Fin (borderRank T * borderRank S) :=
    finProdFinEquiv
  have hunit : Cslib.Tensor.reindex e e e
      (tprod (unit (borderRank T) : Cslib.Tensor K _ _ _) (unit (borderRank S))) =
      unit (borderRank T * borderRank S) := by
    funext i j k
    simp only [Cslib.Tensor.reindex_apply, tprod_apply, unit_apply, mul_ite, ite_mul, one_mul,
      zero_mul, mul_zero]
    by_cases h : i = j ∧ j = k
    · rcases h with ⟨rfl, rfl⟩; simp
    · rw [ite_eq_right h]
      split_ifs with h1 h2
      · exfalso; apply h
        exact ⟨e.symm.injective (Prod.ext h2.1 h1.1), e.symm.injective (Prod.ext h2.2 h1.2)⟩
      · rfl
      · rfl
  exact borderRank_le_of_isDegen_unit (hunit ▸ hprod.reindex_source e e e)

/-- **Degeneration order** of a finite three-tensor `T`: the minimum order `h : ℕ` of a
degeneration from `unit (borderRank T)` to `T`. -/
noncomputable def degenOrder [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) : ℕ :=
  sInf {h : ℕ | IsDegen h T (unit (borderRank T))}

/-- Every finite three-tensor achieves `borderRank T` at degeneration order `degenOrder T`. -/
theorem isDegen_borderRank_degenOrder [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) :
    IsDegen (degenOrder T) T (unit (borderRank T)) := by
  have hne : ({h : ℕ | IsDegen h T (unit (borderRank T))}).Nonempty :=
    exists_isDegen_borderRank T
  exact Nat.sInf_mem hne

/-- Upper-bound criterion for `degenOrder T`. -/
theorem degenOrder_le_of_isDegen [Fintype X] [Fintype Y] [Fintype Z] {h : ℕ}
    {T : Cslib.Tensor K X Y Z} (hT : IsDegen h T (unit (borderRank T))) :
    degenOrder T ≤ h :=
  Nat.sInf_le hT

end BorderRank

section ErrorDegreeAndDebordering

variable {K X Y Z : Type*}

private noncomputable def truncPoly {R : Type*} [Semiring R] (h : ℕ) (p : R[X]) : R[X] :=
  ∑ i ∈ Finset.range (h + 1), C (p.coeff i) * Polynomial.X ^ i

private lemma natDegree_truncPoly_le {R : Type*} [Semiring R] (h : ℕ) (p : R[X]) :
    (truncPoly h p).natDegree ≤ h := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le (p.coeff i) i).trans
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

private lemma exists_sub_truncPoly_eq {R : Type*} [CommRing R] (h : ℕ) (p : R[X]) :
    ∃ q : R[X], p = truncPoly h p + Polynomial.X ^ (h + 1) * q := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1) \ Finset.range (h + 1),
      C (p.coeff i) * Polynomial.X ^ (i - (h + 1)), ?_⟩
  ext m
  simp only [truncPoly, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow_mul']
  by_cases hm : m ≤ h
  · have hm_lt : m < h + 1 := Nat.lt_succ_iff.mpr hm
    rw [ite_eq_right (by omega), add_zero, Finset.sum_eq_single m]
    · simp
    · intro i _ him; simp [him.symm]
    · intro hmem; exact absurd (Finset.mem_range.mpr hm_lt) hmem
  · have hge : h + 1 ≤ m := by omega
    rw [Finset.sum_eq_zero fun i hi ↦ ite_eq_right (by have := Finset.mem_range.mp hi; omega),
      zero_add, ite_eq_left hge]
    by_cases hdeg : m ≤ p.natDegree
    · have hmem : m ∈ Finset.range (p.natDegree + 1) \ Finset.range (h + 1) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),
          fun hc ↦ hm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))⟩
      rw [Finset.sum_eq_single m]
      · simp
      · intro i hi him
        have hi_ge : h + 1 ≤ i := by
          have := (Finset.mem_sdiff.mp hi).2
          rw [Finset.mem_range] at this; omega
        rw [ite_eq_right (by omega)]
      · intro hc; exact absurd hmem hc
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Finset.sum_eq_zero]
      intro i hi
      have hi_lt : i < p.natDegree + 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      have hi_ge : h + 1 ≤ i := by
        have := (Finset.mem_sdiff.mp hi).2
        rw [Finset.mem_range] at this; omega
      rw [ite_eq_right (by omega)]

private lemma unit_map_C {R : Type*} [CommSemiring R] (r : ℕ) :
    (unit r : Cslib.Tensor R _ _ _).map (C : R →+* R[X]) = (unit r : Cslib.Tensor R[X] _ _ _) := by
  funext i j k; simp only [Cslib.Tensor.map_apply, unit_apply]; split_ifs <;> simp

private lemma unit_map_eval {R : Type*} [CommSemiring R] (r : ℕ) (ε : R) :
    (unit r : Cslib.Tensor R[X] _ _ _).map (Polynomial.evalRingHom ε) =
      (unit r : Cslib.Tensor R _ _ _) := by
  funext i j k; simp only [Cslib.Tensor.map_apply, unit_apply]; split_ifs <;> simp

/-- A tensor `T` admits an **error-degree curve** of rank `r` and degree `d` if there exists a
polynomial tensor `P : Cslib.Tensor K[X] X Y Z` with `P(0) = T`, `natDegree (P x y z) ≤ d` for
every `(x, y, z)`, and `Rank r (P(ε))` for all cofinite `ε : K`. -/
def HasErrorDeg [CommSemiring K] (r d : ℕ) (T : Cslib.Tensor K X Y Z) : Prop :=
  ∃ P : Cslib.Tensor K[X] X Y Z,
    P.map (Polynomial.evalRingHom 0) = T ∧
    (∀ x y z, (P x y z).natDegree ≤ d) ∧
    ∀ᶠ ε : K in Filter.cofinite, Rank r (P.map (Polynomial.evalRingHom ε))

/-- Exact rank `r` yields error degree `0`. -/
theorem hasErrorDeg_zero_of_rank [CommSemiring K] {r : ℕ} {T : Cslib.Tensor K X Y Z}
    (hT : Rank r T) : HasErrorDeg r 0 T := by
  refine ⟨T.map C, by funext x y z; simp, fun x y z ↦ (Polynomial.natDegree_C _).le,
    Filter.Eventually.of_forall fun ε ↦ ?_⟩
  have hev : (T.map C).map (Polynomial.evalRingHom ε) = T := by funext x y z; simp
  rwa [hev]

/-- **Degeneration-to-error-degree bound**: over
any integral domain `K` (and in particular any field), every order-`h` degeneration of `unit r` to
`T` truncates modulo `X ^ (h + 1)` to produce an error-degree curve of rank `r` and degree at most
`2 * h`.
-/
theorem hasErrorDeg_two_mul_of_isDegen [Field K] {h r : ℕ} {T : Cslib.Tensor K X Y Z}
    (hT : IsDegen h T (unit r)) : HasErrorDeg r (2 * h) T := by
  obtain ⟨α, β, γ, E, hw⟩ := hT
  rw [unit_map_C] at hw
  let α' : Matrix (Fin r) X K[X] := Matrix.of fun t x ↦ truncPoly h (α t x)
  let β' : Matrix (Fin r) Y K[X] := Matrix.of fun t y ↦ truncPoly h (β t y)
  let γ' : Matrix Z (Fin r) K[X] := Matrix.of fun z t ↦ truncPoly h (γ z t)
  let W : Cslib.Tensor K[X] X Y Z := restrict α' β' γ' (unit r)
  have hW_deg (x : X) (y : Y) (z : Z) : (W x y z).natDegree ≤ 3 * h := by
    dsimp only [W]; rw [restrict_unit_apply]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t _ ↦ ?_
    refine (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_truncPoly_le h (α t x)) (natDegree_truncPoly_le h (β t y))))
      (natDegree_truncPoly_le h (γ z t)))).trans (by omega)
  have hW_mod (x : X) (y : Y) (z : Z) :
      ∃ q : K[X], W x y z = Polynomial.X ^ h * C (T x y z) + Polynomial.X ^ (h + 1) * q := by
    have hdiff : Polynomial.X ^ (h + 1) ∣ W x y z - restrict α β γ (unit r) x y z := by
      dsimp only [W]; rw [restrict_unit_apply, restrict_unit_apply, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun t _ ↦ ?_
      obtain ⟨qa, ha⟩ := exists_sub_truncPoly_eq h (α t x)
      obtain ⟨qb, hb⟩ := exists_sub_truncPoly_eq h (β t y)
      obtain ⟨qc, hc⟩ := exists_sub_truncPoly_eq h (γ z t)
      dsimp only [α', β', γ', Matrix.of_apply]
      set a := truncPoly h (α t x); set b := truncPoly h (β t y); set c := truncPoly h (γ z t)
      rw [ha, hb, hc]
      refine ⟨-(qa * b * c + a * qb * c + a * b * qc +
        Polynomial.X ^ (h + 1) * (qa * qb * c + qa * b * qc + a * qb * qc) +
        (Polynomial.X ^ (h + 1)) ^ 2 * (qa * qb * qc)), by ring⟩
    obtain ⟨qd, hqd⟩ := hdiff
    have hw_xyz := congrFun (congrFun (congrFun hw x) y) z
    refine ⟨E x y z + qd, ?_⟩
    calc
      W x y z = Polynomial.X ^ (h + 1) * qd + Cslib.Tensor.restrict α β γ (unit r) x y z :=
        eq_add_of_sub_eq hqd
      _ = Polynomial.X ^ h * C (T x y z) + Polynomial.X ^ (h + 1) * (E x y z + qd) := by
        rw [hw_xyz]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Cslib.Tensor.map_apply]
        ring
  let P : Cslib.Tensor K[X] X Y Z := fun x y z ↦
    C (T x y z) + Polynomial.X * (hW_mod x y z).choose
  have hW_eq (x : X) (y : Y) (z : Z) : W x y z = Polynomial.X ^ h * P x y z := by
    set q := (hW_mod x y z).choose
    have hq : W x y z = Polynomial.X ^ h * C (T x y z) + Polynomial.X ^ (h + 1) * q :=
      (hW_mod x y z).choose_spec
    change W x y z = Polynomial.X ^ h * (C (T x y z) + Polynomial.X * q)
    rw [hq, pow_succ]; ring
  refine ⟨P, ?_, ?_, ?_⟩
  · funext x y z; simp [P]
  · intro x y z
    by_cases hP0 : P x y z = 0
    · simp [hP0]
    · have hmul : (W x y z).natDegree = h + (P x y z).natDegree := by
        rw [hW_eq x y z, Polynomial.natDegree_mul (pow_ne_zero h Polynomial.X_ne_zero) hP0,
          Polynomial.natDegree_X_pow]
      have hle := hW_deg x y z
      omega
  · have hne0 : ∀ᶠ ε : K in Filter.cofinite, ε ≠ 0 :=
      Filter.eventually_cofinite.mpr (by simp)
    refine hne0.mono fun ε hε ↦ ?_
    let ev := Polynomial.evalRingHom ε
    refine ⟨α'.map ev, β'.map ev, (ε ^ h)⁻¹ • γ'.map ev, ?_⟩
    funext x y z
    have hsmul : restrict (α'.map ev) (β'.map ev) ((ε ^ h)⁻¹ • γ'.map ev) (unit r) x y z =
        (ε ^ h)⁻¹ * (W.map ev x y z) := by
      have hm : W.map ev = restrict (α'.map ev) (β'.map ev) (γ'.map ev) (unit r) := by
        dsimp only [W]; rw [map_restrict, unit_map_eval]
      rw [hm, restrict_unit_apply, restrict_unit_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      simp only [Matrix.smul_apply, smul_eq_mul]; ring
    rw [hsmul, Cslib.Tensor.map_apply, hW_eq x y z]
    simp only [ev, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Cslib.Tensor.map_apply]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero h hε), one_mul]

/-- **Error degree** of a finite three-tensor `T`: the minimum degree `d : ℕ` of a cofinite
rank-`borderRank T` polynomial approximation curve for `T`. -/
noncomputable def errorDeg [Field K] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) : ℕ :=
  sInf {d : ℕ | HasErrorDeg (borderRank T) d T}

/-- Every finite three-tensor over a field attains `errorDeg T` at rank `borderRank T`. -/
theorem hasErrorDeg_borderRank_errorDeg [Field K] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) :
    HasErrorDeg (borderRank T) (errorDeg T) T := by
  have hne : ({d : ℕ | HasErrorDeg (borderRank T) d T}).Nonempty :=
    ⟨2 * degenOrder T, hasErrorDeg_two_mul_of_isDegen (isDegen_borderRank_degenOrder T)⟩
  exact Nat.sInf_mem hne

/-- Upper-bound criterion for `errorDeg T`. -/
theorem errorDeg_le_of_hasErrorDeg [Field K] [Fintype X] [Fintype Y] [Fintype Z] {d : ℕ}
    {T : Cslib.Tensor K X Y Z} (hT : HasErrorDeg (borderRank T) d T) :
    errorDeg T ≤ d :=
  Nat.sInf_le hT

/-- **Quantitative error-degree bound for order-`3` tensors**: `errorDeg T ≤ 2 * degenOrder T`. -/
theorem errorDeg_le_two_mul_degenOrder [Field K] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Cslib.Tensor K X Y Z) :
    errorDeg T ≤ 2 * degenOrder T :=
  errorDeg_le_of_hasErrorDeg (hasErrorDeg_two_mul_of_isDegen (isDegen_borderRank_degenOrder T))

private lemma exists_inj_nodes {K : Type*} [Infinite K] {S : Set K} (hS : S.Finite) :
    ∀ m : ℕ, ∃ a : Fin m → K, Function.Injective a ∧ ∀ k, a k ∉ S
  | 0 => ⟨Fin.elim0, fun i ↦ i.elim0, fun k ↦ k.elim0⟩
  | m + 1 => by
    obtain ⟨a, ha_inj, ha_mem⟩ := exists_inj_nodes hS m
    have hfin : (S ∪ Set.range a).Finite := hS.union (Set.finite_range a)
    obtain ⟨x, hx⟩ := hfin.infinite_compl.nonempty
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hx
    refine ⟨Fin.cons x a, ?_, fun k ↦ Fin.cases hx.1 ha_mem k⟩
    intro i j
    refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
    · intro _; rfl
    · intro hij; exact absurd ⟨j', hij.symm⟩ hx.2
    · intro hij; exact absurd ⟨i', hij⟩ hx.2
    · intro hij; exact congrArg Fin.succ (ha_inj hij)

/-- **Arbitrary-characteristic Lagrange interpolation debordering**: over any infinite field `K`,
if `HasErrorDeg r d T`, then `Rank ((d + 1) * r) T`. -/
theorem rank_of_hasErrorDeg [Field K] [Infinite K] [Fintype X] [Fintype Y] [Fintype Z]
    {r d : ℕ} {T : Cslib.Tensor K X Y Z} (hT : HasErrorDeg r d T) :
    Rank ((d + 1) * r) T := by
  classical
  obtain ⟨P, hP0, hPdeg, hev⟩ := hT
  have hbad : {ε : K | ¬ Rank r (P.map (Polynomial.evalRingHom ε))}.Finite :=
    Filter.eventually_cofinite.mp hev
  obtain ⟨a, ha_inj, ha_good⟩ := exists_inj_nodes hbad (d + 1)
  have hrk (k : Fin (d + 1)) : Rank r (P.map (Polynomial.evalRingHom (a k))) :=
    not_not.mp (ha_good k)
  let c : Fin (d + 1) → K := fun k ↦ (Lagrange.basis Finset.univ a k).eval 0
  have hv : Set.InjOn a ↑(Finset.univ : Finset (Fin (d + 1))) := ha_inj.injOn
  have hsum : T = ∑ k : Fin (d + 1), c k • P.map (Polynomial.evalRingHom (a k)) := by
    funext x y z
    rw [← hP0]
    simp only [Cslib.Tensor.map_apply, Polynomial.coe_evalRingHom, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    have hdeg : (P x y z).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt
        (by exact_mod_cast Nat.lt_succ_iff.mpr (hPdeg x y z))
    conv_lhs => rw [Lagrange.eq_interpolate hv hdeg]
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, c]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hsum_res : IsRestriction (∑ k : Fin (d + 1), c k • P.map (Polynomial.evalRingHom (a k)))
      (dsum fun k : Fin (d + 1) ↦ P.map (Polynomial.evalRingHom (a k))) := by
    refine ⟨Matrix.of fun p x ↦ if p.2 = x then 1 else 0,
      Matrix.of fun p y ↦ if p.2 = y then 1 else 0,
      Matrix.of fun z p ↦ if z = p.2 then c p.1 else 0, ?_⟩
    funext x y z
    simp [Cslib.Tensor.restrict, Fintype.sum_prod_type, ite_and, mul_ite, ite_mul,
      Finset.sum_ite_irrel, Finset.sum_apply]
  rw [hsum]
  exact Rank.of_isRestriction (hsum_res.trans (IsRestriction.dsum hrk))
    (Rank.dsum (d + 1) (IsRestriction.refl _))

/-- Over any infinite field `K`, `Rank ((errorDeg T + 1) * borderRank T) T`. -/
theorem rank_errorDeg_add_one_mul_borderRank [Field K] [Infinite K]
    [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) :
    Rank ((errorDeg T + 1) * borderRank T) T :=
  rank_of_hasErrorDeg (hasErrorDeg_borderRank_errorDeg T)

/-- Over any infinite field `K`, `Rank ((2 * degenOrder T + 1) * borderRank T) T`. -/
theorem rank_two_mul_degenOrder_add_one_mul_borderRank [Field K] [Infinite K]
    [Fintype X] [Fintype Y] [Fintype Z] (T : Cslib.Tensor K X Y Z) :
    Rank ((2 * degenOrder T + 1) * borderRank T) T :=
  rank_mono (rank_errorDeg_add_one_mul_borderRank T)
    (Nat.mul_le_mul_right _ (Nat.succ_le_succ (errorDeg_le_two_mul_degenOrder T)))

end ErrorDegreeAndDebordering

section SlicesAndWordLinearity

/-- Assemble a family of frontal matrix slices `S : Z → Matrix X Y R` into a three-tensor. -/
def ofSlices {R X Y Z : Type*} (S : Z → Matrix X Y R) : Cslib.Tensor R X Y Z :=
  fun x y z ↦ S z x y

/-- **Simultaneous-diagonalization slice characterization of three-tensor rank**: a slice family
`S : Z → Matrix X Y R` has tensor rank at most `r` if and only if there exist matrices
`A : Matrix X (Fin r) R`, `B : Matrix (Fin r) Y R`, and diagonal tuples `d : Z → Fin r → R` such
that `S z = A * Matrix.diagonal (d z) * B` for every `z : Z`. -/
theorem rank_ofSlices_iff {R X Y Z : Type*} [CommSemiring R] {r : ℕ} (S : Z → Matrix X Y R) :
    Rank r (ofSlices S) ↔
      ∃ (A : Matrix X (Fin r) R) (B : Matrix (Fin r) Y R) (d : Z → Fin r → R),
        ∀ z : Z, S z = A * Matrix.diagonal (d z) * B := by
  constructor
  · rintro ⟨α, β, γ, h⟩
    refine ⟨αᵀ, β, fun z t ↦ γ z t, fun z ↦ ?_⟩
    ext x y
    have hxyz := (congrFun (congrFun (congrFun h x) y) z).symm
    rw [ofSlices, restrict_unit_apply] at hxyz
    rw [hxyz, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Matrix.mul_diagonal]
    simp [mul_comm, mul_left_comm]
  · rintro ⟨A, B, d, hS⟩
    refine ⟨Aᵀ, B, Matrix.of d, ?_⟩
    funext x y z
    rw [restrict_unit_apply, ofSlices, hS z, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Matrix.mul_diagonal]
    simp [mul_comm, mul_left_comm]

/-- **First-order noncommutative word-linearity identity**: in any ring `R`, if
`N * M ^ k * N = 0` for every `k` with `k + 2 ≤ n` (for instance, `M = J_n(0)` an `n × n` upper
Jordan block and `N = E_{n-1, 0}` the bottom-left rank-one perturbation), then every power
`(M + N) ^ i` with `i ≤ n` eliminates all terms of degree `≥ 2` in `N`:
`(M + N) ^ i = M ^ i + ∑ k : Fin i, M ^ k * N * M ^ (i - 1 - k)`. -/
theorem add_pow_eq_add_sum_of_sandwich_eq_zero {R : Type*} [Ring R] {n : ℕ} (M N : R)
    (h : ∀ k : ℕ, k + 2 ≤ n → N * M ^ k * N = 0) :
    ∀ {i : ℕ}, i ≤ n →
      (M + N) ^ i = M ^ i + ∑ k : Fin i, M ^ (k : ℕ) * N * M ^ (i - 1 - (k : ℕ))
  | 0, _ => by simp
  | i + 1, hi => by
    have ih := add_pow_eq_add_sum_of_sandwich_eq_zero M N h (Nat.le_of_succ_le hi)
    have hkill (k : Fin i) : (M ^ (k : ℕ) * N * M ^ (i - 1 - (k : ℕ))) * N = 0 := by
      have hk : i - 1 - (k : ℕ) + 2 ≤ n := by have := k.isLt; omega
      calc
        (M ^ (k : ℕ) * N * M ^ (i - 1 - (k : ℕ))) * N
            = M ^ (k : ℕ) * (N * M ^ (i - 1 - (k : ℕ)) * N) := by simp [mul_assoc]
        _ = 0 := by rw [h _ hk, mul_zero]
    rw [pow_succ, ih, add_mul, mul_add, mul_add, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_eq_zero fun k _ ↦ hkill k, add_zero, ← pow_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      mul_one]
    rw [show M ^ (i + 1) + M ^ i * N +
          (∑ x : Fin i, M ^ (x : ℕ) * N * M ^ (i - 1 - (x : ℕ)) * M) =
        M ^ (i + 1) + ((∑ x : Fin i, M ^ (x : ℕ) * N * M ^ (i - 1 - (x : ℕ)) * M) +
          M ^ i * N) by abel]
    congr 2
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hexp : i - 1 - (k : ℕ) + 1 = i - (k : ℕ) := by have := k.isLt; omega
    rw [mul_assoc, ← pow_succ, hexp]

end SlicesAndWordLinearity

section WState

/-- The **three-qubit `W`-state** tensor `|100⟩ + |010⟩ + |001⟩` on `Fin 2 × Fin 2 × Fin 2`. -/
def wState3 (R : Type*) [Zero R] [One R] : Cslib.Tensor R (Fin 2) (Fin 2) (Fin 2) :=
  fun x y z ↦ if x.val + y.val + z.val = 1 then 1 else 0

/-- Explicit order-`1` degeneration of `unit 2` to `wState3 K`:
`(e_0 + X e_1)^{\otimes 3} - e_0^{\otimes 3} = X • wState3 K + X ^ 2 • E`. -/
theorem isDegen_one_wState3_unit_two {K : Type*} [CommRing K] :
    IsDegen 1 (wState3 K) (unit 2) := by
  let v : Fin 2 → K[X] := ![1, Polynomial.X]
  let e₀ : Fin 2 → K[X] := ![1, 0]
  let α : Matrix (Fin 2) (Fin 2) K[X] := Matrix.of ![v, e₀]
  let γ : Matrix (Fin 2) (Fin 2) K[X] := Matrix.of fun z t ↦ if t = 0 then v z else -e₀ z
  let E : Cslib.Tensor K[X] (Fin 2) (Fin 2) (Fin 2) := fun x y z ↦
    if x.val + y.val + z.val = 2 then 1
    else if x.val + y.val + z.val = 3 then Polynomial.X
    else 0
  refine ⟨α, α, γ, E, ?_⟩
  rw [unit_map_C]
  funext x y z
  rw [restrict_unit_apply, Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [α, γ, v, e₀, E, wState3, pow_succ]

/-- The three-qubit `W`-state does not have rank `≤ 1` over any field. -/
theorem not_rank_one_wState3 {K : Type*} [Field K] : ¬ Rank 1 (wState3 K) := by
  rintro ⟨α, β, γ, h⟩
  have hval (x y z : Fin 2) : ∑ t : Fin 1, α t x * β t y * γ z t = wState3 K x y z := by
    rw [← restrict_unit_apply, h]
  have h100 : α 0 1 * β 0 0 * γ 0 0 = 1 := by simpa [wState3] using hval 1 0 0
  have h010 : α 0 0 * β 0 1 * γ 0 0 = 1 := by simpa [wState3] using hval 0 1 0
  have h110 : α 0 1 * β 0 1 * γ 0 0 = 0 := by simpa [wState3] using hval 1 1 0
  have ha1 : α 0 1 ≠ 0 := fun h0 ↦ by simp [h0] at h100
  have hbg : β 0 1 * γ 0 0 ≠ 0 := fun h0 ↦ by rw [mul_assoc, h0, mul_zero] at h010; simp at h010
  exact mul_ne_zero ha1 hbg (by simpa [mul_assoc] using h110)

/-- The three-qubit `W`-state does not have border rank `≤ 1` over any field. -/
theorem not_borderRank_le_one_wState3 {K : Type*} [Field K] :
    ¬ borderRank (wState3 K) ≤ 1 := by
  intro hle
  obtain ⟨h, α, β, γ, E, hw⟩ := borderRank_le_iff.mp hle
  rw [unit_map_C] at hw
  have hentry (x y z : Fin 2) :
      α 0 x * β 0 y * γ z 0 =
        Polynomial.X ^ h * C (wState3 K x y z) + Polynomial.X ^ (h + 1) * E x y z := by
    have := congrFun (congrFun (congrFun hw x) y) z
    simpa [restrict_unit_apply, Fin.sum_univ_one] using this
  have hprod : (α 0 1 * β 0 0 * γ 0 0) * (α 0 0 * β 0 1 * γ 0 0) =
      (α 0 0 * β 0 0 * γ 0 0) * (α 0 1 * β 0 1 * γ 0 0) := by ring
  rw [hentry 1 0 0, hentry 0 1 0, hentry 0 0 0, hentry 1 1 0] at hprod
  have hw100 : wState3 K 1 0 0 = 1 := rfl
  have hw010 : wState3 K 0 1 0 = 1 := rfl
  have hw000 : wState3 K 0 0 0 = 0 := rfl
  have hw110 : wState3 K 1 1 0 = 0 := rfl
  simp only [hw100, hw010, hw000, hw110, map_one, map_zero, mul_one, mul_zero, zero_add] at hprod
  have hcoeff := congrArg (fun p : K[X] ↦ p.coeff (2 * h)) hprod
  have hlhs : ((Polynomial.X ^ h + Polynomial.X ^ (h + 1) * E 1 0 0) *
      (Polynomial.X ^ h + Polynomial.X ^ (h + 1) * E 0 1 0)).coeff (2 * h) = 1 := by
    have hexp : (Polynomial.X ^ h + Polynomial.X ^ (h + 1) * E 1 0 0) *
        (Polynomial.X ^ h + Polynomial.X ^ (h + 1) * E 0 1 0) =
      Polynomial.X ^ (2 * h) + Polynomial.X ^ (2 * h + 1) *
        (E 1 0 0 + E 0 1 0 + Polynomial.X * E 1 0 0 * E 0 1 0) := by
      rw [two_mul, pow_add, pow_succ, pow_succ]; ring
    rw [hexp]; simp [Polynomial.coeff_X_pow_mul']
  have hrhs : ((Polynomial.X ^ (h + 1) * E 0 0 0) *
      (Polynomial.X ^ (h + 1) * E 1 1 0)).coeff (2 * h) = 0 := by
    have hexp : (Polynomial.X ^ (h + 1) * E 0 0 0) * (Polynomial.X ^ (h + 1) * E 1 1 0) =
        Polynomial.X ^ (2 * h + 2) * (E 0 0 0 * E 1 1 0) := by
      rw [show 2 * h + 2 = (h + 1) + (h + 1) by omega, pow_add]; ring
    rw [hexp, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)]
  rw [hlhs, hrhs] at hcoeff
  exact one_ne_zero hcoeff

/-- **Exact border rank of the three-qubit `W`-state**: `borderRank (wState3 K) = 2` over any
field `K`. -/
theorem borderRank_wState3 {K : Type*} [Field K] : borderRank (wState3 K) = 2 := by
  have hle : borderRank (wState3 K) ≤ 2 :=
    borderRank_le_of_isDegen_unit isDegen_one_wState3_unit_two
  have hgt : ¬ borderRank (wState3 K) ≤ 1 := not_borderRank_le_one_wState3
  omega

/-- **The three-qubit `W`-state does not have exact rank `2`** over any field `K` (strict gap
`borderRank (wState3 K) = 2 < 3 = rank`). -/
theorem not_rank_two_wState3 {K : Type*} [Field K] : ¬ Rank 2 (wState3 K) := by
  rintro ⟨α, β, γ, h⟩
  have hval (x y z : Fin 2) :
      α 0 x * β 0 y * γ z 0 + α 1 x * β 1 y * γ z 1 = wState3 K x y z := by
    have h2 := restrict_unit_apply α β γ x y z
    rw [h, Fin.sum_univ_two] at h2
    exact h2.symm
  have hg1 : γ 1 0 ≠ 0 ∨ γ 1 1 ≠ 0 := by
    by_contra hall; push Not at hall
    have h001 := hval 0 0 1
    simp [hall.1, hall.2, wState3] at h001
  have elim (t₀ t₁ : Fin 2) (hne : t₀ ≠ t₁) (hg : γ 1 t₀ ≠ 0) : False := by
    have hsum_t (x y z : Fin 2) :
        α t₀ x * β t₀ y * γ z t₀ + α t₁ x * β t₁ y * γ z t₁ = wState3 K x y z := by
      fin_cases t₀ <;> fin_cases t₁
      · exact absurd rfl hne
      · exact hval x y z
      · rw [add_comm]; exact hval x y z
      · exact absurd rfl hne
    let lam : K := γ 0 t₀ * (γ 1 t₀)⁻¹
    let c : K := γ 0 t₁ - lam * γ 1 t₁
    have hcomb (x y : Fin 2) :
        α t₁ x * β t₁ y * c = wState3 K x y 0 - lam * wState3 K x y 1 := by
      have h0 := hsum_t x y 0
      have h1 := hsum_t x y 1
      have hsub : (α t₀ x * β t₀ y * γ 0 t₀ + α t₁ x * β t₁ y * γ 0 t₁) -
          lam * (α t₀ x * β t₀ y * γ 1 t₀ + α t₁ x * β t₁ y * γ 1 t₁) =
        wState3 K x y 0 - lam * wState3 K x y 1 := by rw [h0, h1]
      have hcancel : γ 0 t₀ - lam * γ 1 t₀ = 0 := by
        simp [lam, mul_assoc, inv_mul_cancel₀ hg]
      have hlhs : (α t₀ x * β t₀ y * γ 0 t₀ + α t₁ x * β t₁ y * γ 0 t₁) -
          lam * (α t₀ x * β t₀ y * γ 1 t₀ + α t₁ x * β t₁ y * γ 1 t₁) =
        α t₀ x * β t₀ y * (γ 0 t₀ - lam * γ 1 t₀) + α t₁ x * β t₁ y * c := by
        dsimp only [c]; ring
      rw [hlhs, hcancel, mul_zero, zero_add] at hsub
      exact hsub
    have h10 : α t₁ 1 * β t₁ 0 * c = 1 := by simpa [wState3] using hcomb 1 0
    have h01 : α t₁ 0 * β t₁ 1 * c = 1 := by simpa [wState3] using hcomb 0 1
    have h11 : α t₁ 1 * β t₁ 1 * c = 0 := by simpa [wState3] using hcomb 1 1
    have ha1 : α t₁ 1 ≠ 0 := fun h0 ↦ by simp [h0] at h10
    have hbc : β t₁ 1 * c ≠ 0 := fun h0 ↦ by rw [mul_assoc, h0, mul_zero] at h01; simp at h01
    exact mul_ne_zero ha1 hbc (by simpa [mul_assoc] using h11)
  rcases hg1 with h0 | h1
  · exact elim 0 1 (by decide) h0
  · exact elim 1 0 (by decide) h1

/-- Exact rank `3` witness for the three-qubit `W`-state over any commutative semiring. -/
theorem rank_three_wState3 {R : Type*} [CommSemiring R] : Rank 3 (wState3 R) := by
  let e₀ : Fin 2 → R := ![1, 0]
  let e₁ : Fin 2 → R := ![0, 1]
  refine ⟨Matrix.of ![e₁, e₀, e₀], Matrix.of ![e₀, e₁, e₀],
    (Matrix.of ![e₀, e₀, e₁])ᵀ, ?_⟩
  funext x y z
  rw [restrict_unit_apply, Fin.sum_univ_three]
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [e₀, e₁, wState3]

/-- **Exact degeneration order of the three-qubit `W`-state**: `degenOrder (wState3 K) = 1` over
any field `K`. -/
theorem degenOrder_wState3 {K : Type*} [Field K] : degenOrder (wState3 K) = 1 := by
  have hle : degenOrder (wState3 K) ≤ 1 :=
    degenOrder_le_of_isDegen (borderRank_wState3 (K := K).symm ▸ isDegen_one_wState3_unit_two)
  have hne0 : degenOrder (wState3 K) ≠ 0 := by
    intro h0
    have hd : IsDegen 0 (wState3 K) (unit 2) := by
      have := isDegen_borderRank_degenOrder (wState3 K)
      rwa [h0, borderRank_wState3] at this
    obtain ⟨α, β, γ, E, hw⟩ := hd
    rw [unit_map_C] at hw
    let ev := Polynomial.evalRingHom (0 : K)
    refine not_rank_two_wState3 (K := K) ⟨α.map ev, β.map ev, γ.map ev, ?_⟩
    have hm := congrArg (Cslib.Tensor.map ev) hw
    rw [map_restrict, unit_map_eval] at hm
    funext x y z
    have hxyz := congrFun (congrFun (congrFun hm x) y) z
    simpa [ev] using hxyz
  omega

/-- **Exact error degree of the three-qubit `W`-state**: `errorDeg (wState3 K) = 1` over any
infinite field `K`. -/
theorem errorDeg_wState3 {K : Type*} [Field K] [Infinite K] : errorDeg (wState3 K) = 1 := by
  have h1 : HasErrorDeg 2 1 (wState3 K) := by
    let P : Cslib.Tensor K[X] (Fin 2) (Fin 2) (Fin 2) := fun x y z ↦
      if x.val + y.val + z.val = 1 then 1
      else if x = 1 ∧ y = 1 ∧ z = 0 then Polynomial.X
      else 0
    refine ⟨P, by funext x y z; fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [P, wState3],
      fun x y z ↦ by
        fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [P],
      (Filter.eventually_cofinite.mpr (by simp : {ε : K | ¬ ε ≠ 0}.Finite)).mono fun ε hε ↦ ?_⟩
    let a : Fin 2 → K := ![1, ε]
    let b : Fin 2 → K := ![1, 0]
    let c : Fin 2 → K := ![1, -ε]
    refine ⟨Matrix.of ![a, b], Matrix.of ![a, b],
      Matrix.of fun z t ↦ if t = 0 then (ε⁻¹ * ![1, 0] z : K) else -ε⁻¹ * c z, ?_⟩
    -- Use the 2-term symmetric formula ε⁻¹ ((e₀ + ε e₁)⊗(e₀ + ε e₁)⊗e₀ - e₀⊗e₀⊗(e₀ - ε e₁))
    funext x y z
    rw [restrict_unit_apply, Fin.sum_univ_two]
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [a, b, c, P] <;> field_simp [hε]
  have hle : errorDeg (wState3 K) ≤ 1 :=
    errorDeg_le_of_hasErrorDeg (borderRank_wState3 (K := K).symm ▸ h1)
  have hne0 : errorDeg (wState3 K) ≠ 0 := by
    intro h0
    have hrk := rank_errorDeg_add_one_mul_borderRank (wState3 K)
    rw [h0, borderRank_wState3, zero_add, one_mul] at hrk
    exact not_rank_two_wState3 hrk
  omega

end WState

end CslibFrontier.Tensor
