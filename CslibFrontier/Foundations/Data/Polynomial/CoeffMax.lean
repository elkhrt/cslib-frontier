module

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Coefficientwise Supremum and Infimum on Univariate Polynomials

This module defines the coefficientwise supremum `CslibFrontier.Polynomial.coeffMax` and
coefficientwise infimum `CslibFrontier.Polynomial.coeffMin` on univariate polynomials `R[X]` over a
semiring `R` equipped with a join-semilattice (`SemilatticeSup R`) or meet-semilattice
(`SemilatticeInf R`). Because `0 ⊔ 0 = 0` and `0 ⊓ 0 = 0` hold by idempotence in any semilattice,
both operations preserve finite support without assuming `0` is a bottom or top element.

We establish exact coefficient identities, semilattice laws, support and `Polynomial.natDegree`
bounds, universal coefficientwise join/meet characterizations, and pointwise evaluation dominance
and minorization bounds at nonnegative elements `0 ≤ x` of an ordered semiring.

## Main definitions

* `CslibFrontier.Polynomial.coeffMax`: polynomial with `n`-th coefficient `p.coeff n ⊔ q.coeff n`.
* `CslibFrontier.Polynomial.coeffMin`: polynomial with `n`-th coefficient `p.coeff n ⊓ q.coeff n`.

## Main results

* `CslibFrontier.Polynomial.coeff_coeffMax`, `CslibFrontier.Polynomial.coeff_coeffMin`: exact
  coefficient formulas at every degree `n : ℕ`.
* `CslibFrontier.Polynomial.natDegree_coeffMax_le`: degree bound
  `(coeffMax p q).natDegree ≤ max p.natDegree q.natDegree`.
* `CslibFrontier.Polynomial.coeffMax_le_iff`, `CslibFrontier.Polynomial.le_coeffMin_iff`:
  universal coefficientwise join and meet properties.
* `CslibFrontier.Polynomial.sup_eval_le_eval_coeffMax`,
  `CslibFrontier.Polynomial.eval_coeffMin_le_inf_eval`: evaluation bounds at nonnegative points.
-/

public section

namespace CslibFrontier.Polynomial

private theorem eval_mono_of_coeff_le {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q : _root_.Polynomial R} (hpq : ∀ n, p.coeff n ≤ q.coeff n) {x : R} (hx : 0 ≤ x) :
    p.eval x ≤ q.eval x := by
  let N : ℕ := max p.natDegree q.natDegree + 1
  have hpN : p.natDegree < N := Nat.lt_succ_of_le (le_max_left _ _)
  have hqN : q.natDegree < N := Nat.lt_succ_of_le (le_max_right _ _)
  rw [_root_.Polynomial.eval_eq_sum_range' hpN, _root_.Polynomial.eval_eq_sum_range' hqN]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hpq i) (pow_nonneg hx i)

section SemilatticeSup

variable {R : Type*} [Semiring R] [SemilatticeSup R]

/-- Coefficientwise supremum of two univariate polynomials `p, q : Polynomial R`, characterized by
`(coeffMax p q).coeff n = p.coeff n ⊔ q.coeff n` for all `n : ℕ`. -/
noncomputable def coeffMax (p q : _root_.Polynomial R) : _root_.Polynomial R := by
  classical
  exact ∑ i ∈ p.support ∪ q.support, _root_.Polynomial.monomial i (p.coeff i ⊔ q.coeff i)

/-- Every coefficient of `coeffMax p q` equals the supremum of the corresponding coefficients of
`p` and `q`. -/
@[simp]
theorem coeff_coeffMax (p q : _root_.Polynomial R) (n : ℕ) :
    (coeffMax p q).coeff n = p.coeff n ⊔ q.coeff n := by
  classical
  unfold coeffMax
  rw [_root_.Polynomial.finsetSum_coeff]
  simp only [_root_.Polynomial.coeff_monomial, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · simp only [Finset.mem_union, not_or, _root_.Polynomial.mem_support_iff, not_not] at hn
    rw [hn.1, hn.2, sup_idem]

/-- Commutativity of `coeffMax`. -/
theorem coeffMax_comm (p q : _root_.Polynomial R) : coeffMax p q = coeffMax q p := by
  ext n
  simp [sup_comm]

/-- Associativity of `coeffMax`. -/
theorem coeffMax_assoc (p q r : _root_.Polynomial R) :
    coeffMax (coeffMax p q) r = coeffMax p (coeffMax q r) := by
  ext n
  simp [sup_assoc]

/-- Idempotence of `coeffMax`. -/
@[simp]
theorem coeffMax_idem (p : _root_.Polynomial R) : coeffMax p p = p := by
  ext n
  simp

/-- Coefficientwise supremum of constant polynomials agrees with `Polynomial.C` of the supremum. -/
@[simp]
theorem coeffMax_C (a b : R) :
    coeffMax (_root_.Polynomial.C a) (_root_.Polynomial.C b) = _root_.Polynomial.C (a ⊔ b) := by
  ext n
  cases n with
  | zero => simp
  | succ k => simp

/-- The support of `coeffMax p q` is contained in `p.support ∪ q.support`. -/
theorem support_coeffMax_subset (p q : _root_.Polynomial R) :
    (coeffMax p q).support ⊆ p.support ∪ q.support := by
  classical
  intro n hn
  rw [_root_.Polynomial.mem_support_iff, coeff_coeffMax] at hn
  rw [Finset.mem_union, _root_.Polynomial.mem_support_iff, _root_.Polynomial.mem_support_iff]
  by_contra h
  simp only [not_or, not_not] at h
  rw [h.1, h.2, sup_idem] at hn
  exact hn rfl

/-- The natural degree of `coeffMax p q` is at most `max p.natDegree q.natDegree`. -/
theorem natDegree_coeffMax_le (p q : _root_.Polynomial R) :
    (coeffMax p q).natDegree ≤ max p.natDegree q.natDegree := by
  refine _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
  rw [coeff_coeffMax]
  have hp : p.coeff n = 0 :=
    _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_left _ _) hn)
  have hq : q.coeff n = 0 :=
    _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_right _ _) hn)
  rw [hp, hq, sup_idem]

/-- Every coefficient of `p` is bounded above by the corresponding coefficient of `coeffMax p q`. -/
theorem left_le_coeffMax (p q : _root_.Polynomial R) (n : ℕ) :
    p.coeff n ≤ (coeffMax p q).coeff n := by
  rw [coeff_coeffMax]
  exact le_sup_left

/-- Every coefficient of `q` is bounded above by the corresponding coefficient of `coeffMax p q`. -/
theorem right_le_coeffMax (p q : _root_.Polynomial R) (n : ℕ) :
    q.coeff n ≤ (coeffMax p q).coeff n := by
  rw [coeff_coeffMax]
  exact le_sup_right

/-- Universal least-upper-bound property of `coeffMax` with respect to coefficientwise order. -/
theorem coeffMax_le_iff {p q r : _root_.Polynomial R} :
    (∀ n, (coeffMax p q).coeff n ≤ r.coeff n) ↔
      (∀ n, p.coeff n ≤ r.coeff n) ∧ (∀ n, q.coeff n ≤ r.coeff n) := by
  constructor
  · intro h
    exact ⟨fun n => le_trans (left_le_coeffMax p q n) (h n),
      fun n => le_trans (right_le_coeffMax p q n) (h n)⟩
  · rintro ⟨hp, hq⟩ n
    rw [coeff_coeffMax]
    exact sup_le (hp n) (hq n)

/-- If every coefficient of `q` is nonnegative (`0 ≤ q.coeff n`), then `coeffMax 0 q = q`. -/
theorem coeffMax_zero_left {q : _root_.Polynomial R} (hq : ∀ n, 0 ≤ q.coeff n) :
    coeffMax 0 q = q := by
  ext n
  rw [coeff_coeffMax, _root_.Polynomial.coeff_zero]
  exact sup_eq_right.mpr (hq n)

/-- If every coefficient of `p` is nonnegative (`0 ≤ p.coeff n`), then `coeffMax p 0 = p`. -/
theorem coeffMax_zero_right {p : _root_.Polynomial R} (hp : ∀ n, 0 ≤ p.coeff n) :
    coeffMax p 0 = p := by
  ext n
  rw [coeff_coeffMax, _root_.Polynomial.coeff_zero]
  exact sup_eq_left.mpr (hp n)

/-- At any nonnegative point `0 ≤ x` in an ordered semiring, `p.eval x ≤ (coeffMax p q).eval x`. -/
theorem eval_le_eval_coeffMax_left [IsOrderedRing R] (p q : _root_.Polynomial R) {x : R}
    (hx : 0 ≤ x) : p.eval x ≤ (coeffMax p q).eval x :=
  eval_mono_of_coeff_le (left_le_coeffMax p q) hx

/-- At any nonnegative point `0 ≤ x` in an ordered semiring, `q.eval x ≤ (coeffMax p q).eval x`. -/
theorem eval_le_eval_coeffMax_right [IsOrderedRing R] (p q : _root_.Polynomial R) {x : R}
    (hx : 0 ≤ x) : q.eval x ≤ (coeffMax p q).eval x :=
  eval_mono_of_coeff_le (right_le_coeffMax p q) hx

/-- At any nonnegative point `0 ≤ x` in an ordered semiring, `(coeffMax p q).eval x` dominates
`p.eval x ⊔ q.eval x`. -/
theorem sup_eval_le_eval_coeffMax [IsOrderedRing R] (p q : _root_.Polynomial R) {x : R}
    (hx : 0 ≤ x) : p.eval x ⊔ q.eval x ≤ (coeffMax p q).eval x :=
  sup_le (eval_le_eval_coeffMax_left p q hx) (eval_le_eval_coeffMax_right p q hx)

end SemilatticeSup

section SemilatticeInf

variable {R : Type*} [Semiring R] [SemilatticeInf R]

/-- Coefficientwise infimum of two univariate polynomials `p, q : Polynomial R`, characterized by
`(coeffMin p q).coeff n = p.coeff n ⊓ q.coeff n` for all `n : ℕ`. -/
noncomputable def coeffMin (p q : _root_.Polynomial R) : _root_.Polynomial R := by
  classical
  exact ∑ i ∈ p.support ∪ q.support, _root_.Polynomial.monomial i (p.coeff i ⊓ q.coeff i)

/-- Every coefficient of `coeffMin p q` equals the infimum of the corresponding coefficients of
`p` and `q`. -/
@[simp]
theorem coeff_coeffMin (p q : _root_.Polynomial R) (n : ℕ) :
    (coeffMin p q).coeff n = p.coeff n ⊓ q.coeff n := by
  classical
  unfold coeffMin
  rw [_root_.Polynomial.finsetSum_coeff]
  simp only [_root_.Polynomial.coeff_monomial, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · simp only [Finset.mem_union, not_or, _root_.Polynomial.mem_support_iff, not_not] at hn
    rw [hn.1, hn.2, inf_idem]

/-- Commutativity of `coeffMin`. -/
theorem coeffMin_comm (p q : _root_.Polynomial R) : coeffMin p q = coeffMin q p := by
  ext n
  simp [inf_comm]

/-- Associativity of `coeffMin`. -/
theorem coeffMin_assoc (p q r : _root_.Polynomial R) :
    coeffMin (coeffMin p q) r = coeffMin p (coeffMin q r) := by
  ext n
  simp [inf_assoc]

/-- Idempotence of `coeffMin`. -/
@[simp]
theorem coeffMin_idem (p : _root_.Polynomial R) : coeffMin p p = p := by
  ext n
  simp

/-- Coefficientwise infimum of constant polynomials agrees with `Polynomial.C` of the infimum. -/
@[simp]
theorem coeffMin_C (a b : R) :
    coeffMin (_root_.Polynomial.C a) (_root_.Polynomial.C b) = _root_.Polynomial.C (a ⊓ b) := by
  ext n
  cases n with
  | zero => simp
  | succ k => simp

/-- Every coefficient of `coeffMin p q` is bounded above by `p.coeff n`. -/
theorem coeffMin_le_left (p q : _root_.Polynomial R) (n : ℕ) :
    (coeffMin p q).coeff n ≤ p.coeff n := by
  rw [coeff_coeffMin]
  exact inf_le_left

/-- Every coefficient of `coeffMin p q` is bounded above by `q.coeff n`. -/
theorem coeffMin_le_right (p q : _root_.Polynomial R) (n : ℕ) :
    (coeffMin p q).coeff n ≤ q.coeff n := by
  rw [coeff_coeffMin]
  exact inf_le_right

/-- Universal greatest-lower-bound property of `coeffMin` with respect to coefficientwise order. -/
theorem le_coeffMin_iff {p q r : _root_.Polynomial R} :
    (∀ n, r.coeff n ≤ (coeffMin p q).coeff n) ↔
      (∀ n, r.coeff n ≤ p.coeff n) ∧ (∀ n, r.coeff n ≤ q.coeff n) := by
  constructor
  · intro h
    exact ⟨fun n => le_trans (h n) (coeffMin_le_left p q n),
      fun n => le_trans (h n) (coeffMin_le_right p q n)⟩
  · rintro ⟨hp, hq⟩ n
    rw [coeff_coeffMin]
    exact le_inf (hp n) (hq n)

/-- At any nonnegative point `0 ≤ x` in an ordered semiring, `(coeffMin p q).eval x` is bounded
above by `p.eval x ⊓ q.eval x`. -/
theorem eval_coeffMin_le_inf_eval [IsOrderedRing R] (p q : _root_.Polynomial R) {x : R}
    (hx : 0 ≤ x) : (coeffMin p q).eval x ≤ p.eval x ⊓ q.eval x :=
  le_inf
    (eval_mono_of_coeff_le (coeffMin_le_left p q) hx)
    (eval_mono_of_coeff_le (coeffMin_le_right p q) hx)

end SemilatticeInf

end CslibFrontier.Polynomial
