/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multivariate Lagrange Interpolation and Cleared-Denominator Integer Basis Polynomials

Provides multivariate Lagrange interpolation over an arbitrary field of characteristic zero on the
integer grid `{0, ..., d}^n`, together with cleared-denominator integer scaled Lagrange basis
polynomials on `{0, ..., 2^w - 1}^v` and a general coefficient identity for products of univariate
polynomials evaluated on distinct variables.

## Main definitions

* `CslibFrontier.MvPolynomial.lagrangeCommonDenom`: common integer denominator
  `∏_{i < 2^w} ∏_{j ≠ i} (i - j)`.
* `CslibFrontier.MvPolynomial.lagrangeComplement`: complementary integer factor
  `∏_{r ≠ i} ∏_{j ≠ r} (r - j)`.
* `CslibFrontier.MvPolynomial.lagrangeScaledUniPoly`: scaled univariate integer Lagrange basis
  polynomial `lagrangeComplement w i * ∏_{j ≠ i} (X - j)`.
* `CslibFrontier.MvPolynomial.lagrangeScaledMultiPoly`: scaled multivariate integer Lagrange basis
  polynomial obtained as the tensor product of univariate scaled basis polynomials.

## Main results

* `CslibFrontier.MvPolynomial.mvLagrangeInterpolation`: multivariate Lagrange interpolation over any
  characteristic-zero field for polynomials of individual degree at most `d`.
* `CslibFrontier.MvPolynomial.mvLagrangeInterpolation_totalDegree`: total-degree specialization.
* `CslibFrontier.MvPolynomial.coeff_prod_aeval_X`: coefficient formula for products of univariate
  polynomials evaluated on distinct variables of `MvPolynomial (Fin v) R`.
* `CslibFrontier.MvPolynomial.lagrange_interpolation_int`: cleared-denominator integer multivariate
  Lagrange interpolation identity on `{0, ..., 2^w - 1}^v`.
* `CslibFrontier.MvPolynomial.lagrange_interpolation_int_coeff`: coefficient extraction form of
  cleared-denominator integer multivariate Lagrange interpolation.
-/

public section

namespace CslibFrontier.MvPolynomial

open _root_.MvPolynomial

private theorem finSuccEquiv_symm_C {R : Type*} [CommSemiring R] (n : ℕ)
    (g : _root_.MvPolynomial (Fin n) R) :
    (_root_.MvPolynomial.finSuccEquiv R n).symm (Polynomial.C g) =
      _root_.MvPolynomial.rename Fin.succ g := by
  apply (_root_.MvPolynomial.finSuccEquiv R n).injective
  rw [AlgEquiv.apply_symm_apply]
  induction g using _root_.MvPolynomial.induction_on with
  | C a =>
    rw [_root_.MvPolynomial.rename_C]
    simp [_root_.MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p k hp =>
    rw [map_mul, map_mul, _root_.MvPolynomial.rename_X, map_mul,
      _root_.MvPolynomial.finSuccEquiv_X_succ, ← hp]

private theorem finSuccEquiv_symm_map_C {R : Type*} [CommSemiring R] (n : ℕ)
    (b : Polynomial R) :
    (_root_.MvPolynomial.finSuccEquiv R n).symm (Polynomial.map _root_.MvPolynomial.C b) =
      Polynomial.aeval (_root_.MvPolynomial.X (0 : Fin (n + 1))) b := by
  apply (_root_.MvPolynomial.finSuccEquiv R n).injective
  rw [AlgEquiv.apply_symm_apply]
  induction b using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
      _root_.MvPolynomial.finSuccEquiv_X_zero, ← Polynomial.C_mul_X_pow_eq_monomial]
    congr 1
    simp [_root_.MvPolynomial.finSuccEquiv_apply]

private theorem eval_C_finSuccEquiv {R : Type*} [CommSemiring R] {n : ℕ}
    (a : R) (p : _root_.MvPolynomial (Fin (n + 1)) R) :
    Polynomial.eval (_root_.MvPolynomial.C a) (_root_.MvPolynomial.finSuccEquiv R n p) =
      _root_.MvPolynomial.eval₂Hom _root_.MvPolynomial.C
        (Fin.cases (_root_.MvPolynomial.C a) _root_.MvPolynomial.X) p := by
  induction p using _root_.MvPolynomial.induction_on with
  | C c =>
    have hc : _root_.MvPolynomial.finSuccEquiv R n (_root_.MvPolynomial.C c) =
        Polynomial.C (_root_.MvPolynomial.C c) :=
      AlgEquiv.commutes (_root_.MvPolynomial.finSuccEquiv R n) c
    rw [hc, Polynomial.eval_C, _root_.MvPolynomial.eval₂Hom_C]
  | add p q hp hq => rw [map_add, Polynomial.eval_add, map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, Polynomial.eval_mul, map_mul, hp]
    congr 1
    cases k using Fin.cases with
    | zero => simp [_root_.MvPolynomial.finSuccEquiv_X_zero]
    | succ j => simp [_root_.MvPolynomial.finSuccEquiv_X_succ]

private theorem eval_eval_C_finSuccEquiv {R : Type*} [CommSemiring R] {n : ℕ}
    (a : R) (y : Fin n → R) (p : _root_.MvPolynomial (Fin (n + 1)) R) :
    _root_.MvPolynomial.eval y
        (Polynomial.eval (_root_.MvPolynomial.C a) (_root_.MvPolynomial.finSuccEquiv R n p)) =
      _root_.MvPolynomial.eval (Fin.cons a y) p := by
  rw [eval_C_finSuccEquiv]
  induction p using _root_.MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases k using Fin.cases with
    | zero => simp
    | succ j => simp

private theorem degreeOf_eval_C_finSuccEquiv_le' {R : Type*} [CommSemiring R] {n : ℕ}
    (a : R) (p : _root_.MvPolynomial (Fin (n + 1)) R) (k : Fin n) :
    (Polynomial.eval (_root_.MvPolynomial.C a)
        (_root_.MvPolynomial.finSuccEquiv R n p)).degreeOf k ≤
      p.degreeOf k.succ := by
  rw [_root_.MvPolynomial.degreeOf_le_iff]
  intro m hm
  rw [_root_.MvPolynomial.mem_support_iff] at hm
  set q := _root_.MvPolynomial.finSuccEquiv R n p
  have hsum : (Polynomial.eval (_root_.MvPolynomial.C a) q).coeff m =
      ∑ t ∈ Finset.range (q.natDegree + 1), ((q.coeff t).coeff m) * a ^ t := by
    rw [Polynomial.eval_eq_sum_range, _root_.MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← map_pow, mul_comm, _root_.MvPolynomial.coeff_C_mul, mul_comm]
  rw [hsum] at hm
  have hex : ∃ t ∈ Finset.range (q.natDegree + 1), ((q.coeff t).coeff m) * a ^ t ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hm (Finset.sum_eq_zero hall)
  obtain ⟨t, _, ht⟩ := hex
  have hcm : (q.coeff t).coeff m ≠ 0 := left_ne_zero_of_mul ht
  rw [_root_.MvPolynomial.finSuccEquiv_coeff_coeff] at hcm
  have hmem : m.cons t ∈ p.support := _root_.MvPolynomial.mem_support_iff.mpr hcm
  have hle := _root_.MvPolynomial.monomial_le_degreeOf k.succ hmem
  simpa using hle

private theorem finSuccEquiv_interp_step {K : Type*} [Field K] [CharZero K] {n d : ℕ}
    (q : Polynomial (_root_.MvPolynomial (Fin n) K)) (hq : ∀ r > d, q.coeff r = 0) :
    q = ∑ a : Fin (d + 1),
      Polynomial.C (q.eval (_root_.MvPolynomial.C (a.val : K))) *
        Polynomial.map _root_.MvPolynomial.C
          (Lagrange.basis (Finset.range (d + 1)) (Nat.cast : ℕ → K) a.val) := by
  have hq_nat : q.natDegree ≤ d := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hq
  ext r m
  let qm : Polynomial K := ∑ t ∈ Finset.range (d + 1), Polynomial.monomial t ((q.coeff t).coeff m)
  have hqm_coeff (t : ℕ) : qm.coeff t = (q.coeff t).coeff m := by
    dsimp only [qm]
    rw [Polynomial.finsetSum_coeff]
    by_cases ht : t < d + 1
    · rw [Finset.sum_eq_single t]
      · simp [Polynomial.coeff_monomial]
      · intro s _ hs; simp [Polynomial.coeff_monomial, hs]
      · intro hnot; exact absurd (Finset.mem_range.mpr ht) hnot
    · have hgt : t > d := by omega
      rw [hq t hgt]; simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      refine Finset.sum_eq_zero fun s hs => ?_
      have hslt : s < d + 1 := Finset.mem_range.mp hs
      have hne : s ≠ t := by omega
      simp [Polynomial.coeff_monomial, hne]
  have hqm_deg : qm.degree < (Finset.range (d + 1)).card := by
    rw [Finset.card_range]
    refine (Polynomial.degree_le_natDegree).trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun t ht => by
      rw [hqm_coeff, hq t ht]; simp)
  have hinj : Set.InjOn (Nat.cast : ℕ → K) (Finset.range (d + 1)) :=
    fun _ _ _ _ h => Nat.cast_injective h
  have hlag := Lagrange.eq_interpolate hinj hqm_deg
  have heval_eq (c : K) : (q.eval (_root_.MvPolynomial.C c)).coeff m = qm.eval c := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq_nat), _root_.MvPolynomial.coeff_sum]
    dsimp only [qm]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← map_pow, mul_comm, _root_.MvPolynomial.coeff_C_mul, Polynomial.eval_monomial, mul_comm]
  have hrhs_coeff : ((∑ a : Fin (d + 1),
      Polynomial.C (q.eval (_root_.MvPolynomial.C (a.val : K))) *
        Polynomial.map _root_.MvPolynomial.C
          (Lagrange.basis (Finset.range (d + 1)) (Nat.cast : ℕ → K) a.val)).coeff r).coeff m =
      (Lagrange.interpolate (Finset.range (d + 1)) (Nat.cast : ℕ → K)
        (fun a => qm.eval (a : K))).coeff r := by
    rw [Polynomial.finsetSum_coeff, _root_.MvPolynomial.coeff_sum, Lagrange.interpolate_apply,
      Polynomial.finsetSum_coeff]
    let g : ℕ → K := fun a =>
      ((Polynomial.C (q.eval (_root_.MvPolynomial.C (a : K))) *
        Polynomial.map _root_.MvPolynomial.C
          (Lagrange.basis (Finset.range (d + 1)) (Nat.cast : ℕ → K) a)).coeff r).coeff m
    change (∑ a : Fin (d + 1), g a.val) = _
    rw [Fin.sum_univ_eq_sum_range g]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [g]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map, mul_comm, _root_.MvPolynomial.coeff_C_mul,
      heval_eq, Polynomial.coeff_C_mul, mul_comm]
  rw [hrhs_coeff, ← hlag, hqm_coeff]

/-- Multivariate Lagrange interpolation over any characteristic-zero field `K` for polynomials of
individual degree at most `d` on the grid `{0, ..., d}^n`. -/
theorem mvLagrangeInterpolation {K : Type*} [Field K] [CharZero K] :
    ∀ {n d : ℕ} (p : _root_.MvPolynomial (Fin n) K), (∀ k : Fin n, p.degreeOf k ≤ d) →
      p = ∑ i : Fin n → Fin (d + 1),
        _root_.MvPolynomial.C (_root_.MvPolynomial.eval (fun k => ((i k).val : K)) p) *
          ∏ k : Fin n, ∏ j ∈ (Finset.range (d + 1)).erase (i k).val,
            _root_.MvPolynomial.C ((((i k).val : K) - (j : K))⁻¹) *
              (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : K))
  | 0, d, p, _ => by
    have huniq : (∑ i : Fin 0 → Fin (d + 1),
        _root_.MvPolynomial.C (_root_.MvPolynomial.eval (fun k => ((i k).val : K)) p) *
          ∏ k : Fin 0, ∏ j ∈ (Finset.range (d + 1)).erase (i k).val,
            _root_.MvPolynomial.C ((((i k).val : K) - (j : K))⁻¹) *
              (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : K))) =
        _root_.MvPolynomial.C (_root_.MvPolynomial.eval Fin.elim0 p) := by
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty,
        mul_one]
      exact congrArg (fun f => _root_.MvPolynomial.C (_root_.MvPolynomial.eval f p))
        (funext fun k => Fin.elim0 k)
    rw [huniq]
    have hp := _root_.MvPolynomial.eq_C_of_isEmpty p
    conv_rhs => rw [hp]
    rw [_root_.MvPolynomial.eval_C]
    exact hp
  | n + 1, d, p, hdeg => by
    set q := _root_.MvPolynomial.finSuccEquiv K n p
    have hq_deg : ∀ r > d, q.coeff r = 0 := fun r hr => by
      ext m
      rw [_root_.MvPolynomial.finSuccEquiv_coeff_coeff]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_contra hne
      have hle := _root_.MvPolynomial.monomial_le_degreeOf 0
        (_root_.MvPolynomial.mem_support_iff.mpr hne)
      have h0 := hdeg 0
      simp only [Finsupp.cons_zero] at hle
      omega
    have hstep := finSuccEquiv_interp_step q hq_deg
    have hp_eq := congrArg (_root_.MvPolynomial.finSuccEquiv K n).symm hstep
    rw [AlgEquiv.symm_apply_apply, map_sum] at hp_eq
    conv_lhs => rw [hp_eq]
    have hterm (a : Fin (d + 1)) :
        (_root_.MvPolynomial.finSuccEquiv K n).symm
          (Polynomial.C (q.eval (_root_.MvPolynomial.C (a.val : K))) *
            Polynomial.map _root_.MvPolynomial.C
              (Lagrange.basis (Finset.range (d + 1)) (Nat.cast : ℕ → K) a.val)) =
        ∑ i' : Fin n → Fin (d + 1),
          _root_.MvPolynomial.C (_root_.MvPolynomial.eval
            (fun k => (((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k).val : K)) p) *
            ∏ k : Fin (n + 1),
              ∏ j ∈ (Finset.range (d + 1)).erase
                ((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k).val,
                _root_.MvPolynomial.C
                  (((((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k).val : K) - (j : K))⁻¹) *
                  (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : K)) := by
      rw [map_mul, finSuccEquiv_symm_C, finSuccEquiv_symm_map_C]
      set pa : _root_.MvPolynomial (Fin n) K := q.eval (_root_.MvPolynomial.C (a.val : K))
      have hpa_deg : ∀ k : Fin n, pa.degreeOf k ≤ d := fun k =>
        (degreeOf_eval_C_finSuccEquiv_le' (a.val : K) p k).trans (hdeg k.succ)
      have ih := mvLagrangeInterpolation pa hpa_deg
      have hbasis : Polynomial.aeval (_root_.MvPolynomial.X (0 : Fin (n + 1)))
          (Lagrange.basis (Finset.range (d + 1)) (Nat.cast : ℕ → K) a.val) =
          ∏ j ∈ (Finset.range (d + 1)).erase a.val,
            _root_.MvPolynomial.C (((a.val : K) - (j : K))⁻¹) *
              (_root_.MvPolynomial.X (0 : Fin (n + 1)) - _root_.MvPolynomial.C (j : K)) := by
        rw [Lagrange.basis, map_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp [Lagrange.basisDivisor, _root_.MvPolynomial.algebraMap_eq]
      rw [ih, map_sum, Finset.sum_mul, hbasis]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, _root_.MvPolynomial.rename_C, map_prod, Fin.prod_univ_succ]
      have heval : _root_.MvPolynomial.eval (fun k => ((i' k).val : K)) pa =
          _root_.MvPolynomial.eval
            (fun k => (((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k).val : K)) p := by
        rw [eval_eval_C_finSuccEquiv]
        have hfn : Fin.cons (a.val : K) (fun k => ((i' k).val : K)) =
            fun k => (((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k).val : K) :=
          funext fun k => by cases k using Fin.cases <;> rfl
        rw [hfn]
      have hren : (∏ k : Fin n, _root_.MvPolynomial.rename Fin.succ
          (∏ j ∈ (Finset.range (d + 1)).erase (i' k).val,
            _root_.MvPolynomial.C ((((i' k).val : K) - (j : K))⁻¹) *
              (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : K)))) =
          ∏ k : Fin n,
            ∏ j ∈ (Finset.range (d + 1)).erase
              ((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k.succ).val,
              _root_.MvPolynomial.C
                (((((Fin.cons a i' : Fin (n + 1) → Fin (d + 1)) k.succ).val : K) - (j : K))⁻¹) *
                (_root_.MvPolynomial.X k.succ - _root_.MvPolynomial.C (j : K)) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [map_prod, Fin.cons_succ]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp [_root_.MvPolynomial.rename_X]
      rw [heval, hren, Fin.cons_zero]
      ring
    simp_rw [hterm]
    rw [← Fintype.sum_prod_type']
    refine Finset.sum_bij (fun p _ => Fin.cons p.1 p.2)
      (fun _ _ => Finset.mem_univ _)
      (fun p₁ _ p₂ _ h => Prod.ext
        (by simpa using congrFun h 0)
        (funext fun k => by simpa using congrFun h k.succ))
      (fun i _ => ⟨(i 0, fun k => i k.succ), Finset.mem_univ _,
        funext fun k => by cases k using Fin.cases <;> rfl⟩)
      (fun _ _ => rfl)

/-- Total-degree specialization of multivariate Lagrange interpolation over any characteristic-zero
field. -/
theorem mvLagrangeInterpolation_totalDegree {K : Type*} [Field K] [CharZero K] {n d : ℕ}
    (p : _root_.MvPolynomial (Fin n) K) (hdeg : p.totalDegree ≤ d) :
    p = ∑ i : Fin n → Fin (d + 1),
      _root_.MvPolynomial.C (_root_.MvPolynomial.eval (fun k => ((i k).val : K)) p) *
        ∏ k : Fin n, ∏ j ∈ (Finset.range (d + 1)).erase (i k).val,
          _root_.MvPolynomial.C ((((i k).val : K) - (j : K))⁻¹) *
            (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : K)) :=
  mvLagrangeInterpolation p fun k => (_root_.MvPolynomial.degreeOf_le_totalDegree p k).trans hdeg

/-- Common integer denominator `∏_{i < 2^w} ∏_{j ≠ i} (i - j)` for Lagrange interpolation on
`{0, ..., 2^w - 1}`. -/
def lagrangeCommonDenom (w : ℕ) : ℤ :=
  ∏ i ∈ Finset.range (2 ^ w), ∏ j ∈ (Finset.range (2 ^ w)).erase i, ((i : ℤ) - (j : ℤ))

/-- Complementary integer factor `∏_{r ≠ i} ∏_{j ≠ r} (r - j)` satisfying
`lagrangeComplement w i * ∏_{j ≠ i} (i - j) = lagrangeCommonDenom w`. -/
def lagrangeComplement (w i : ℕ) : ℤ :=
  ∏ r ∈ (Finset.range (2 ^ w)).erase i,
    ∏ j ∈ (Finset.range (2 ^ w)).erase r, ((r : ℤ) - (j : ℤ))

/-- Scaled univariate integer Lagrange basis polynomial
`lagrangeComplement w i * ∏_{j ≠ i} (X - j)`. -/
noncomputable def lagrangeScaledUniPoly (w i : ℕ) : Polynomial ℤ :=
  Polynomial.C (lagrangeComplement w i) *
    ∏ j ∈ (Finset.range (2 ^ w)).erase i, (Polynomial.X - Polynomial.C (j : ℤ))

/-- Scaled multivariate integer Lagrange basis polynomial on `{0, ..., 2^w - 1}^v`. -/
noncomputable def lagrangeScaledMultiPoly (v w : ℕ) (i : Fin v → Fin (2 ^ w)) :
    _root_.MvPolynomial (Fin v) ℤ :=
  ∏ k : Fin v, Polynomial.aeval (_root_.MvPolynomial.X k) (lagrangeScaledUniPoly w (i k).val)

/-- `lagrangeCommonDenom w` is nonzero for every `w`. -/
theorem lagrangeCommonDenom_ne_zero (w : ℕ) : lagrangeCommonDenom w ≠ 0 := by
  rw [lagrangeCommonDenom, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  omega

/-- Product factorization `lagrangeComplement w i * ∏_{j ≠ i} (i - j) = lagrangeCommonDenom w`. -/
theorem lagrangeComplement_mul_denom_eq (w i : ℕ) (hi : i < 2 ^ w) :
    lagrangeComplement w i * ∏ j ∈ (Finset.range (2 ^ w)).erase i, ((i : ℤ) - (j : ℤ)) =
      lagrangeCommonDenom w := by
  rw [lagrangeCommonDenom, lagrangeComplement, mul_comm]
  exact Finset.mul_prod_erase (Finset.range (2 ^ w))
    (fun r => ∏ j ∈ (Finset.range (2 ^ w)).erase r, ((r : ℤ) - (j : ℤ)))
    (Finset.mem_range.mpr hi)

/-- Product-of-univariate-polynomials coefficient formula: the `m`-th coefficient of
`∏ k, aeval (X k) (q k)` equals `∏ k, (q k).coeff (m k)`. -/
theorem coeff_prod_aeval_X {R : Type*} [CommRing R] :
    ∀ {v : ℕ} (q : Fin v → Polynomial R) (m : Fin v →₀ ℕ),
      (∏ k : Fin v, Polynomial.aeval (_root_.MvPolynomial.X k) (q k)).coeff m =
        ∏ k : Fin v, (q k).coeff (m k)
  | 0, q, m => by
    have hm : m = 0 := Subsingleton.elim _ _
    simp [hm]
  | v + 1, q, m => by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    set P : _root_.MvPolynomial (Fin v) R :=
      ∏ k : Fin v, Polynomial.aeval (_root_.MvPolynomial.X k) (q k.succ)
    have hren : (∏ k : Fin v, Polynomial.aeval (_root_.MvPolynomial.X k.succ) (q k.succ)) =
        _root_.MvPolynomial.rename Fin.succ P := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      induction q k.succ using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
      | monomial r c => simp [Polynomial.aeval_monomial, _root_.MvPolynomial.algebraMap_eq]
    rw [hren]
    have hfs : _root_.MvPolynomial.finSuccEquiv R v
        (Polynomial.aeval (_root_.MvPolynomial.X (0 : Fin (v + 1))) (q 0) *
          _root_.MvPolynomial.rename Fin.succ P) =
        Polynomial.map _root_.MvPolynomial.C (q 0) * Polynomial.C P := by
      rw [map_mul, ← finSuccEquiv_symm_map_C, ← finSuccEquiv_symm_C,
        AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have hmEq : m = (Finsupp.tail m).cons (m 0) := by
      ext k; cases k using Fin.cases <;> simp
    conv_lhs => rw [hmEq]
    rw [← _root_.MvPolynomial.finSuccEquiv_coeff_coeff, hfs, mul_comm, Polynomial.coeff_C_mul,
      Polynomial.coeff_map, mul_comm, _root_.MvPolynomial.coeff_C_mul]
    congr 1
    exact coeff_prod_aeval_X (fun k => q k.succ) (Finsupp.tail m)

/-- Coefficient formula for `lagrangeScaledMultiPoly`. -/
theorem coeff_lagrangeScaledMultiPoly {v w : ℕ} (i : Fin v → Fin (2 ^ w)) (m : Fin v →₀ ℕ) :
    (lagrangeScaledMultiPoly v w i).coeff m =
      ∏ k : Fin v, (lagrangeScaledUniPoly w (i k).val).coeff (m k) :=
  coeff_prod_aeval_X (fun k => lagrangeScaledUniPoly w (i k).val) m

/-- Cleared-denominator integer multivariate Lagrange interpolation on `{0, ..., 2^w - 1}^v`. -/
theorem lagrange_interpolation_int {v w : ℕ} (p : _root_.MvPolynomial (Fin v) ℤ)
    (hdeg : ∀ k : Fin v, p.degreeOf k < 2 ^ w) :
    _root_.MvPolynomial.C (lagrangeCommonDenom w ^ v) * p =
      ∑ i : Fin v → Fin (2 ^ w),
        _root_.MvPolynomial.C (_root_.MvPolynomial.eval (fun k => ((i k).val : ℤ)) p) *
          lagrangeScaledMultiPoly v w i := by
  have h2w_pos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  set d := 2 ^ w - 1
  have hd1 : d + 1 = 2 ^ w := Nat.sub_add_cancel h2w_pos
  apply _root_.MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hdegQ : ∀ k : Fin v, (_root_.MvPolynomial.map (Int.castRingHom ℚ) p).degreeOf k ≤ d :=
    fun k => by
      rw [_root_.MvPolynomial.degreeOf_le_iff]
      intro m hm
      have hle := _root_.MvPolynomial.monomial_le_degreeOf k
        (_root_.MvPolynomial.support_map_subset _ _ hm)
      have hk := hdeg k
      omega
  have hQ := mvLagrangeInterpolation (_root_.MvPolynomial.map (Int.castRingHom ℚ) p) hdegQ
  rw [map_mul, _root_.MvPolynomial.map_C, map_sum]
  conv_lhs => rw [hQ]
  rw [Finset.mul_sum]
  have hcast : ∀ (n₁ n₂ : ℕ), n₁ = n₂ →
      (∑ i : Fin v → Fin n₁,
        _root_.MvPolynomial.C ((Int.castRingHom ℚ) (lagrangeCommonDenom w ^ v)) *
          (_root_.MvPolynomial.C (_root_.MvPolynomial.eval (fun k => ((i k).val : ℚ))
            (_root_.MvPolynomial.map (Int.castRingHom ℚ) p)) *
            ∏ k : Fin v, ∏ j ∈ (Finset.range n₁).erase (i k).val,
              _root_.MvPolynomial.C ((((i k).val : ℚ) - (j : ℚ))⁻¹) *
                (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : ℚ)))) =
      (∑ i : Fin v → Fin n₂,
        _root_.MvPolynomial.C ((Int.castRingHom ℚ) (lagrangeCommonDenom w ^ v)) *
          (_root_.MvPolynomial.C (_root_.MvPolynomial.eval (fun k => ((i k).val : ℚ))
            (_root_.MvPolynomial.map (Int.castRingHom ℚ) p)) *
            ∏ k : Fin v, ∏ j ∈ (Finset.range n₂).erase (i k).val,
              _root_.MvPolynomial.C ((((i k).val : ℚ) - (j : ℚ))⁻¹) *
                (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : ℚ)))) :=
    fun _ _ h => h ▸ rfl
  rw [hcast (d + 1) (2 ^ w) hd1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, _root_.MvPolynomial.map_C]
  have hevalQ : _root_.MvPolynomial.eval (fun k => ((i k).val : ℚ))
      (_root_.MvPolynomial.map (Int.castRingHom ℚ) p) =
      ((_root_.MvPolynomial.eval (fun k => ((i k).val : ℤ)) p : ℤ) : ℚ) := by
    rw [_root_.MvPolynomial.eval_map]
    change _root_.MvPolynomial.eval₂ (Int.castRingHom ℚ)
        (fun k => ((Int.castRingHom ℚ) ((i k).val : ℤ))) p =
      (Int.castRingHom ℚ) (_root_.MvPolynomial.eval (fun k => ((i k).val : ℤ)) p)
    exact (_root_.MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom ℚ)
      (fun k => ((i k).val : ℤ))).symm
  rw [hevalQ]
  simp only [Int.coe_castRingHom, Int.cast_pow]
  rw [show _root_.MvPolynomial.C ((lagrangeCommonDenom w : ℚ) ^ v) *
        (_root_.MvPolynomial.C ((_root_.MvPolynomial.eval (fun k => ((i k).val : ℤ)) p : ℤ) : ℚ) *
          ∏ k : Fin v, ∏ j ∈ (Finset.range (2 ^ w)).erase (i k).val,
            _root_.MvPolynomial.C ((((i k).val : ℚ) - (j : ℚ))⁻¹) *
              (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : ℚ))) =
      _root_.MvPolynomial.C ((_root_.MvPolynomial.eval (fun k => ((i k).val : ℤ)) p : ℤ) : ℚ) *
        (_root_.MvPolynomial.C ((lagrangeCommonDenom w : ℚ) ^ v) *
          ∏ k : Fin v, ∏ j ∈ (Finset.range (2 ^ w)).erase (i k).val,
            _root_.MvPolynomial.C ((((i k).val : ℚ) - (j : ℚ))⁻¹) *
              (_root_.MvPolynomial.X k - _root_.MvPolynomial.C (j : ℚ))) by ring]
  congr 1
  have hpowC : (_root_.MvPolynomial.C ((lagrangeCommonDenom w : ℚ) ^ v) :
        _root_.MvPolynomial (Fin v) ℚ) =
      ∏ _k : Fin v, _root_.MvPolynomial.C (lagrangeCommonDenom w : ℚ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]
  rw [hpowC, ← Finset.prod_mul_distrib, lagrangeScaledMultiPoly, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
  have hden_ne : (∏ j ∈ (Finset.range (2 ^ w)).erase (i k).val,
      (((i k).val : ℚ) - (j : ℚ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have hne : j ≠ (i k).val := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (by exact_mod_cast hne.symm)
  have hB : (lagrangeCommonDenom w : ℚ) *
      (∏ j ∈ (Finset.range (2 ^ w)).erase (i k).val, (((i k).val : ℚ) - (j : ℚ))⁻¹) =
      (lagrangeComplement w (i k).val : ℚ) := by
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_eq_iff hden_ne]
    have hZ := lagrangeComplement_mul_denom_eq w (i k).val (i k).isLt
    have hQ' := congrArg (Int.cast : ℤ → ℚ) hZ
    simpa [Int.cast_mul, Int.cast_prod, Int.cast_sub, Int.cast_natCast] using hQ'.symm
  rw [hB, lagrangeScaledUniPoly, map_mul, Polynomial.aeval_C, _root_.MvPolynomial.algebraMap_eq,
    map_prod, map_mul, _root_.MvPolynomial.map_C, map_prod]
  simp only [Int.coe_castRingHom]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

/-- Coefficient form of cleared-denominator integer multivariate Lagrange interpolation. -/
theorem lagrange_interpolation_int_coeff {v w : ℕ} (p : _root_.MvPolynomial (Fin v) ℤ)
    (hdeg : ∀ k : Fin v, p.degreeOf k < 2 ^ w) (m : Fin v →₀ ℕ) :
    lagrangeCommonDenom w ^ v * p.coeff m =
      ∑ i : Fin v → Fin (2 ^ w),
        _root_.MvPolynomial.eval (fun k => ((i k).val : ℤ)) p *
          ∏ k : Fin v, (lagrangeScaledUniPoly w (i k).val).coeff (m k) := by
  have h := congrArg (fun q : _root_.MvPolynomial (Fin v) ℤ => q.coeff m)
    (lagrange_interpolation_int p hdeg)
  rw [_root_.MvPolynomial.coeff_C_mul, _root_.MvPolynomial.coeff_sum] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [_root_.MvPolynomial.coeff_C_mul, coeff_lagrangeScaledMultiPoly]

end CslibFrontier.MvPolynomial
