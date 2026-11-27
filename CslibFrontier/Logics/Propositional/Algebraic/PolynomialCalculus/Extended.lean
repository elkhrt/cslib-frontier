/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.Boolean
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Proof
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Size

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

/-!
# Extended Polynomial Calculus, Monomial Calculus, and Rational Bit-Complexity

Explicit derivation traces, monomial-size and rational coefficient bit-complexity measures,
degree-bounded composition and linear-combination combinators, equivalence with
`Cslib.Logic.PL.PC.RefutableInDegree`, bounded-degree algebra-homomorphism simulation, and Boolean
soundness for the Monomial Calculus (`MCDeriv`), Polynomial Calculus (`PCDeriv`), and Extended
Polynomial Calculus (`EPCDeriv`) under standard Lean axioms.

## Main definitions

* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.polyMonomialCount`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.ratBitSize`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.polyBitComplexity`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.HasBoundedIntCoeffs`:
  monomial support count, binary fraction bit-size, and common-denominator coefficient bounds.
* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.MCDeriv`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.PCDeriv`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.EPCDeriv`:
  explicit finite derivation sequences for MC, PC, and EPC (with Boolean axioms restricted to base
  variables and fresh extension variables `x_f - f`).
* `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.EPCDerives`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.PCDerives`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.MCDerives`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.EPCRefutes`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.PCRefutes`,
  `CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.MCRefutes`:
  bounded-degree derivability and refutability predicates.

## Main results

* `HasBoundedIntCoeffs.finset_sum`, `EPCDeriv.exists_deriveIntScaledSum`,
  `EPCDeriv.exists_deriveLinearFormMul`: logarithmic coefficient bit-complexity and polynomial
  monomial-size bounds for multi-term rational linear combinations and linear-form multiplications.
* `EPCDeriv.rename`, `EPCDeriv.append`: injective variable-renaming and derivation-composition
  combinators preserving degree, size, bit-complexity, and extension-axiom invariants.
* `pcRefutes_iff_cslib_refutableInDegree`, `cslib_refutableInDegree_of_algHom`: equivalence between
  `PCRefutes Set.univ` and `Cslib.Logic.PL.PC.RefutableInDegree`, and bounded-degree simulation of
  PC refutations along algebra homomorphisms.
* `EPCDeriv.exists_boolExtension`, `EPCDeriv.eqOn_exts_of_eval_eq_zero`,
  `EPCDeriv.not_one_mem_of_boolSat`: existence and uniqueness of Boolean assignment extensions to
  extension variables and Boolean soundness of EPC, PC, and MC.
-/

public section

universe u v

namespace CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus

open MvPolynomial

section MonomialCount

variable {V : Type u} {R : Type v}

/-- The monomial count (number of nonzero terms) of a multivariate polynomial `p`. -/
def polyMonomialCount [CommSemiring R] (p : MvPolynomial V R) : ℕ :=
  p.support.card

/-- Monomial count equals the cardinality of the polynomial's support. -/
theorem polyMonomialCount_eq_card_support [CommSemiring R] (p : MvPolynomial V R) :
    polyMonomialCount p = p.support.card := by rfl

@[simp, grind =]
theorem polyMonomialCount_zero [CommSemiring R] :
    polyMonomialCount (0 : MvPolynomial V R) = 0 := by
  simp [polyMonomialCount]

@[simp, grind =]
theorem polyMonomialCount_eq_zero_iff [CommSemiring R] {p : MvPolynomial V R} :
    polyMonomialCount p = 0 ↔ p = 0 := by
  simp [polyMonomialCount]

@[simp, grind =]
theorem polyMonomialCount_one [CommSemiring R] [Nontrivial R] :
    polyMonomialCount (1 : MvPolynomial V R) = 1 := by
  simp [polyMonomialCount]

@[simp, grind =]
theorem polyMonomialCount_X [CommSemiring R] [Nontrivial R] (v : V) :
    polyMonomialCount (X v : MvPolynomial V R) = 1 := by
  simp [polyMonomialCount, support_X]

@[simp]
theorem polyMonomialCount_monomial [CommSemiring R] (s : V →₀ ℕ) {c : R} (hc : c ≠ 0) :
    polyMonomialCount (monomial s c : MvPolynomial V R) = 1 := by
  classical
  simp [polyMonomialCount, support_monomial, hc]

/-- Every single monomial term has monomial count at most `1`. -/
theorem polyMonomialCount_monomial_le [CommSemiring R] (s : V →₀ ℕ) (c : R) :
    polyMonomialCount (monomial s c : MvPolynomial V R) ≤ 1 := by
  simpa [polyMonomialCount] using
    Finset.card_le_card (support_monomial_subset (a := c) (s := s))

/-- A constant polynomial `C c` has monomial count at most `1`. -/
theorem polyMonomialCount_C_le [CommSemiring R] (c : R) :
    polyMonomialCount (C c : MvPolynomial V R) ≤ 1 := by
  rw [C_apply]
  exact polyMonomialCount_monomial_le 0 c

private theorem support_neg_eq [CommRing R] (p : MvPolynomial V R) :
    (-p).support = p.support := by
  ext m
  simp

@[simp, grind =]
theorem polyMonomialCount_neg [CommRing R] (p : MvPolynomial V R) :
    polyMonomialCount (-p) = polyMonomialCount p := by
  simp [polyMonomialCount]

/-- Subadditivity of `polyMonomialCount` under polynomial addition. -/
theorem polyMonomialCount_add_le [CommSemiring R] (p q : MvPolynomial V R) :
    polyMonomialCount (p + q) ≤ polyMonomialCount p + polyMonomialCount q := by
  classical
  exact (Finset.card_le_card MvPolynomial.support_add).trans (Finset.card_union_le _ _)

/-- Subadditivity of `polyMonomialCount` under polynomial subtraction. -/
theorem polyMonomialCount_sub_le [CommRing R] (p q : MvPolynomial V R) :
    polyMonomialCount (p - q) ≤ polyMonomialCount p + polyMonomialCount q := by
  simpa [sub_eq_add_neg, polyMonomialCount_neg] using polyMonomialCount_add_le p (-q)

/-- Scalar multiplication never increases `polyMonomialCount`. -/
theorem polyMonomialCount_smul_le {S : Type*} [CommSemiring R] [SMulZeroClass S R]
    (c : S) (p : MvPolynomial V R) :
    polyMonomialCount (c • p) ≤ polyMonomialCount p :=
  Finset.card_le_card MvPolynomial.support_smul

@[simp, grind =]
theorem polyMonomialCount_X_mul [CommSemiring R] (v : V) (p : MvPolynomial V R) :
    polyMonomialCount (X v * p) = polyMonomialCount p := by
  simp [polyMonomialCount, MvPolynomial.support_X_mul]

@[simp, grind =]
theorem polyMonomialCount_mul_X [CommSemiring R] (p : MvPolynomial V R) (v : V) :
    polyMonomialCount (p * X v) = polyMonomialCount p := by
  simp [polyMonomialCount, MvPolynomial.support_mul_X]

/-- Monomial count of a finite sum is at most the sum of monomial counts. -/
theorem polyMonomialCount_sum_le {ι : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → MvPolynomial V R) :
    polyMonomialCount (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyMonomialCount (f i) := by
  classical
  exact (Finset.card_le_card MvPolynomial.support_sum).trans Finset.card_biUnion_le

/-- Submultiplicativity of `polyMonomialCount` under polynomial multiplication. -/
theorem polyMonomialCount_mul_le [CommSemiring R] (p q : MvPolynomial V R) :
    polyMonomialCount (p * q) ≤ polyMonomialCount p * polyMonomialCount q := by
  classical
  exact (Finset.card_le_card (MvPolynomial.support_mul p q)).trans Finset.card_add_le

/-- Variable renaming never increases `polyMonomialCount`. -/
theorem polyMonomialCount_rename_le {W : Type*} [CommSemiring R] (f : V → W)
    (p : MvPolynomial V R) :
    polyMonomialCount (rename f p) ≤ polyMonomialCount p := by
  classical
  exact (Finset.card_le_card fun _ hd ↦ Finsupp.mapDomain_support hd).trans Finset.card_image_le

/-- Injective variable renaming preserves `polyMonomialCount` exactly. -/
theorem polyMonomialCount_rename_of_injective {W : Type*} [CommSemiring R]
    {f : V → W} (hf : Function.Injective f) (p : MvPolynomial V R) :
    polyMonomialCount (rename f p) = polyMonomialCount p := by
  classical
  rw [polyMonomialCount, MvPolynomial.support_rename_of_injective hf]
  exact Finset.card_image_of_injective _ (Finsupp.mapDomain_injective hf)

end MonomialCount

section BitComplexity

/-- Binary bit-size of a rational number `q : ℚ` stored as a reduced fraction of two binary
integers, `Nat.size q.num.natAbs + Nat.size q.den`. -/
def ratBitSize (q : ℚ) : ℕ :=
  Nat.size q.num.natAbs + Nat.size q.den

@[simp, grind =]
theorem ratBitSize_zero : ratBitSize 0 = 1 := by
  simp [ratBitSize]

@[simp, grind =]
theorem ratBitSize_one : ratBitSize 1 = 2 := by
  simp [ratBitSize]

@[simp, grind =]
theorem ratBitSize_neg (q : ℚ) : ratBitSize (-q) = ratBitSize q := by
  simp [ratBitSize]

@[simp, grind =]
theorem ratBitSize_natCast (n : ℕ) : ratBitSize (n : ℚ) = Nat.size n + 1 := by
  simp [ratBitSize]

@[simp, grind =]
theorem ratBitSize_intCast (z : ℤ) : ratBitSize (z : ℚ) = Nat.size z.natAbs + 1 := by
  simp [ratBitSize]

@[simp]
theorem ratBitSize_inv_natCast {n : ℕ} (hn : n ≠ 0) :
    ratBitSize ((n : ℚ)⁻¹) = 1 + Nat.size n := by
  have hpos : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hcop : Nat.Coprime (1 : ℤ).natAbs (n : ℤ).natAbs := by simp
  have hinv : ((n : ℚ)⁻¹) = ((1 : ℤ) : ℚ) / ((n : ℤ) : ℚ) := by simp [one_div]
  have hden : (((1 : ℤ) : ℚ) / ((n : ℤ) : ℚ)).den = n := by
    have := Rat.den_div_eq_of_coprime hpos hcop
    omega
  rw [ratBitSize, hinv, Rat.num_div_eq_of_coprime hpos hcop, hden]
  simp

private theorem size_mul_le (m n : ℕ) : Nat.size (m * n) ≤ Nat.size m + Nat.size n := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self m) (Nat.lt_size_self n)

private theorem size_add_le (m n : ℕ) : Nat.size (m + n) ≤ max (Nat.size m) (Nat.size n) + 1 := by
  rw [Nat.size_le, pow_succ', two_mul]
  exact Nat.add_lt_add
    ((Nat.lt_size_self m).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))
    ((Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))

/-- Bit-size bound for an integer quotient `(a : ℚ) / (b : ℚ)` with `b ≠ 0`. -/
theorem ratBitSize_div_intCast_le (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    ratBitSize ((a : ℚ) / (b : ℚ)) ≤ Nat.size a.natAbs + Nat.size b.natAbs := by
  by_cases ha : a = 0
  · subst ha
    have hsb : 1 ≤ Nat.size b.natAbs :=
      Nat.succ_le_of_lt (Nat.size_pos.mpr (Int.natAbs_pos.mpr hb))
    simpa using hsb
  · rw [Rat.intCast_div_eq_divInt, ratBitSize]
    exact Nat.add_le_add
      (Nat.size_le_size (Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hb))))
      (Nat.size_le_size (Nat.le_of_dvd (Int.natAbs_pos.mpr hb)
        (Int.natCast_dvd.mp (Rat.den_dvd a b))))

/-- Subadditivity of `ratBitSize` under multiplication. -/
theorem ratBitSize_mul_le (q r : ℚ) : ratBitSize (q * r) ≤ ratBitSize q + ratBitSize r := by
  have hmul : q * r = ((q.num * r.num : ℤ) : ℚ) / ((q.den * r.den : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den r]
    push_cast
    ring
  have hden_ne : (q.den * r.den : ℤ) ≠ 0 :=
    Int.mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) (Int.natCast_ne_zero.mpr r.den_ne_zero)
  refine hmul ▸ (ratBitSize_div_intCast_le _ hden_ne).trans ?_
  have h1 : Nat.size (q.num * r.num).natAbs ≤ Nat.size q.num.natAbs + Nat.size r.num.natAbs := by
    rw [Int.natAbs_mul]
    exact size_mul_le _ _
  have h2 : Nat.size (q.den * r.den : ℤ).natAbs ≤ Nat.size q.den + Nat.size r.den := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact size_mul_le _ _
  simp only [ratBitSize]
  omega

/-- Bit-size bound for the sum of two rationals. -/
theorem ratBitSize_add_le (q r : ℚ) :
    ratBitSize (q + r) ≤ 2 * (ratBitSize q + ratBitSize r) + 1 := by
  have hqd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hrd : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_ne_zero
  have hadd : q + r = ((q.num * r.den + r.num * q.den : ℤ) : ℚ) / ((q.den * r.den : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den r]
    rw [div_add_div _ _ hqd hrd]
    push_cast
    ring
  have hden_ne : (q.den * r.den : ℤ) ≠ 0 :=
    Int.mul_ne_zero (Int.natCast_ne_zero.mpr q.den_ne_zero) (Int.natCast_ne_zero.mpr r.den_ne_zero)
  have hnum_abs : (q.num * r.den + r.num * q.den).natAbs ≤
      q.num.natAbs * r.den + r.num.natAbs * q.den :=
    (Int.natAbs_add_le _ _).trans (by simp [Int.natAbs_mul])
  have h1 : Nat.size (q.num * r.den + r.num * q.den).natAbs ≤ ratBitSize q + ratBitSize r + 1 :=
    (Nat.size_le_size hnum_abs).trans ((size_add_le _ _).trans (Nat.add_le_add_right
      (max_le ((size_mul_le _ _).trans (by simp [ratBitSize]; omega))
        ((size_mul_le _ _).trans (by simp [ratBitSize]; omega))) 1))
  have h2 : Nat.size (q.den * r.den : ℤ).natAbs ≤ Nat.size q.den + Nat.size r.den := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact size_mul_le _ _
  have hle := hadd ▸ (ratBitSize_div_intCast_le _ hden_ne).trans (Nat.add_le_add h1 h2)
  simp only [ratBitSize] at hle ⊢
  omega

/-- Coefficient bit-complexity of `p : MvPolynomial V ℚ`: the maximum `ratBitSize` among nonzero
coefficients of `p` (`0` for the zero polynomial). -/
def polyBitComplexity {V : Type u} (p : MvPolynomial V ℚ) : ℕ :=
  p.support.sup fun m ↦ ratBitSize (p.coeff m)

@[simp, grind =]
theorem polyBitComplexity_zero {V : Type u} :
    polyBitComplexity (0 : MvPolynomial V ℚ) = 0 := by
  simp [polyBitComplexity]

@[simp, grind =]
theorem polyBitComplexity_one {V : Type u} :
    polyBitComplexity (1 : MvPolynomial V ℚ) = 2 := by
  simp [polyBitComplexity]

@[simp, grind =]
theorem polyBitComplexity_X {V : Type u} (v : V) :
    polyBitComplexity (X v : MvPolynomial V ℚ) = 2 := by
  simp [polyBitComplexity, support_X]

@[simp, grind =]
theorem polyBitComplexity_neg {V : Type u} (p : MvPolynomial V ℚ) :
    polyBitComplexity (-p) = polyBitComplexity p := by
  simp [polyBitComplexity]

/-- `polyBitComplexity p ≤ b` iff every nonzero coefficient of `p` has `ratBitSize ≤ b`. -/
theorem polyBitComplexity_le_iff {V : Type u} {p : MvPolynomial V ℚ} {b : ℕ} :
    polyBitComplexity p ≤ b ↔ ∀ m ∈ p.support, ratBitSize (p.coeff m) ≤ b := by
  simp [polyBitComplexity]

/-- Every supported coefficient of `p` has bit-size at most `polyBitComplexity p`. -/
theorem ratBitSize_coeff_le_polyBitComplexity {V : Type u} {p : MvPolynomial V ℚ}
    {m : V →₀ ℕ} (hm : m ∈ p.support) : ratBitSize (p.coeff m) ≤ polyBitComplexity p :=
  Finset.le_sup (f := fun s ↦ ratBitSize (p.coeff s)) hm

@[simp]
theorem polyBitComplexity_monomial {V : Type u} (s : V →₀ ℕ) {q : ℚ} (hq : q ≠ 0) :
    polyBitComplexity (monomial s q : MvPolynomial V ℚ) = ratBitSize q := by
  classical
  simp [polyBitComplexity, support_monomial, hq]

@[simp, grind =]
theorem polyBitComplexity_X_mul {V : Type u} (v : V) (p : MvPolynomial V ℚ) :
    polyBitComplexity (X v * p) = polyBitComplexity p := by
  simp only [polyBitComplexity, MvPolynomial.support_X_mul, Finset.sup_map]
  exact Finset.sup_congr rfl fun _ _ ↦ by simp

@[simp, grind =]
theorem polyBitComplexity_mul_X {V : Type u} (p : MvPolynomial V ℚ) (v : V) :
    polyBitComplexity (p * X v) = polyBitComplexity p := by
  simp only [polyBitComplexity, MvPolynomial.support_mul_X, Finset.sup_map]
  exact Finset.sup_congr rfl fun _ _ ↦ by simp

/-- Bit-complexity bound under rational scalar multiplication. -/
theorem polyBitComplexity_smul_le {V : Type u} (c : ℚ) (p : MvPolynomial V ℚ) :
    polyBitComplexity (c • p) ≤ ratBitSize c + polyBitComplexity p := by
  rw [polyBitComplexity_le_iff]
  intro m hm
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact (ratBitSize_mul_le c (p.coeff m)).trans
    (Nat.add_le_add_left (ratBitSize_coeff_le_polyBitComplexity (MvPolynomial.support_smul hm)) _)

/-- Sum of polynomials with disjoint supports has `polyBitComplexity` equal to the maximum. -/
theorem polyBitComplexity_add_of_disjoint {V : Type u} {p q : MvPolynomial V ℚ}
    (h : Disjoint p.support q.support) :
    polyBitComplexity (p + q) = max (polyBitComplexity p) (polyBitComplexity q) := by
  classical
  have hsub : ∀ {a b : MvPolynomial V ℚ}, Disjoint a.support b.support →
      a.support ⊆ (a + b).support := fun {a b} hab ↦ by
    simpa [Finset.sdiff_eq_self_iff_disjoint.mpr hab] using
      MvPolynomial.support_sdiff_support_subset_support_add a b
  have hle : ∀ {a b : MvPolynomial V ℚ}, Disjoint a.support b.support →
      polyBitComplexity a ≤ polyBitComplexity (a + b) := fun hab ↦
    polyBitComplexity_le_iff.mpr fun m hma ↦ by
      have hb0 := MvPolynomial.notMem_support_iff.mp (Finset.disjoint_left.mp hab hma)
      simpa [hb0] using ratBitSize_coeff_le_polyBitComplexity (hsub hab hma)
  refine le_antisymm (polyBitComplexity_le_iff.mpr fun m hm ↦ ?_)
    (max_le (hle h) (by rw [add_comm]; exact hle h.symm))
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hmp | hmq
  · have hq0 := MvPolynomial.notMem_support_iff.mp (Finset.disjoint_left.mp h hmp)
    simpa [hq0] using (ratBitSize_coeff_le_polyBitComplexity hmp).trans (le_max_left _ _)
  · have hp0 := MvPolynomial.notMem_support_iff.mp (Finset.disjoint_right.mp h hmq)
    simpa [hp0] using (ratBitSize_coeff_le_polyBitComplexity hmq).trans (le_max_right _ _)

/-- Bit-complexity bound for the sum of two rational multivariate polynomials. -/
theorem polyBitComplexity_add_le {V : Type u} (p q : MvPolynomial V ℚ) :
    polyBitComplexity (p + q) ≤ 2 * (polyBitComplexity p + polyBitComplexity q) + 1 := by
  classical
  rw [polyBitComplexity_le_iff]
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hmp | hmq
  · have hp := ratBitSize_coeff_le_polyBitComplexity hmp
    by_cases hmq : m ∈ q.support
    · have hq := ratBitSize_coeff_le_polyBitComplexity hmq
      have hadd : (p + q).coeff m = p.coeff m + q.coeff m := by simp
      exact hadd ▸ (ratBitSize_add_le _ _).trans (by omega)
    · have hadd : (p + q).coeff m = p.coeff m := by simp [MvPolynomial.notMem_support_iff.mp hmq]
      rw [hadd]; omega
  · have hq := ratBitSize_coeff_le_polyBitComplexity hmq
    by_cases hmp : m ∈ p.support
    · have hp := ratBitSize_coeff_le_polyBitComplexity hmp
      have hadd : (p + q).coeff m = p.coeff m + q.coeff m := by simp
      exact hadd ▸ (ratBitSize_add_le _ _).trans (by omega)
    · have hadd : (p + q).coeff m = q.coeff m := by simp [MvPolynomial.notMem_support_iff.mp hmp]
      rw [hadd]; omega

/-- Bit-complexity bound for the difference of two rational multivariate polynomials. -/
theorem polyBitComplexity_sub_le {V : Type u} (p q : MvPolynomial V ℚ) :
    polyBitComplexity (p - q) ≤ 2 * (polyBitComplexity p + polyBitComplexity q) + 1 := by
  simpa [sub_eq_add_neg] using polyBitComplexity_add_le p (-q)

/-- Injective variable renaming preserves `polyBitComplexity`. -/
theorem polyBitComplexity_rename_of_injective {V W : Type*} {f : V → W}
    (hf : Function.Injective f) (p : MvPolynomial V ℚ) :
    polyBitComplexity (rename f p) = polyBitComplexity p := by
  classical
  simp only [polyBitComplexity, MvPolynomial.support_rename_of_injective hf, Finset.sup_image]
  exact Finset.sup_congr rfl fun _ _ ↦ by
    simp [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain _ hf]

@[simp, grind =]
theorem polyBitComplexity_boolAx {V : Type u} (v : V) :
    polyBitComplexity ((X v : MvPolynomial V ℚ) ^ 2 - X v) = 2 := by
  have hdisj : Disjoint ((X v : MvPolynomial V ℚ) ^ 2).support
      (-(X v : MvPolynomial V ℚ)).support := by
    classical
    rw [support_neg_eq, support_X, support_X_pow, Finset.disjoint_singleton]
    intro heq
    have hval := congrArg (fun f : V →₀ ℕ ↦ f v) heq
    simp at hval
  rw [sub_eq_add_neg, polyBitComplexity_add_of_disjoint hdisj, polyBitComplexity_neg,
    polyBitComplexity_X, sq, polyBitComplexity_X_mul, polyBitComplexity_X]
  simp

/-- When `x ∉ f.vars`, `X x - f` has bit-complexity `max 2 (polyBitComplexity f)`. -/
theorem polyBitComplexity_sub_X_of_notMem_vars {V : Type u} {x : V} {f : MvPolynomial V ℚ}
    (hx : x ∉ f.vars) : polyBitComplexity (X x - f) = max 2 (polyBitComplexity f) := by
  have hdisj : Disjoint (X x : MvPolynomial V ℚ).support (-f).support := by
    classical
    rw [support_neg_eq, support_X, Finset.disjoint_singleton_left]
    exact fun hmem ↦ hx ((MvPolynomial.mem_vars_iff_mem_support x).mpr
      ⟨Finsupp.single x 1, hmem, by simp⟩)
  rw [sub_eq_add_neg, polyBitComplexity_add_of_disjoint hdisj, polyBitComplexity_X,
    polyBitComplexity_neg]

/-- Predicate asserting that every coefficient of `p` lies in `{0, 1, -1}` (scaled by `1 / d`). -/
@[expose] def HasBoundedIntCoeffs {V : Type u} (p : MvPolynomial V ℚ) (M d : ℕ) : Prop :=
  1 ≤ d ∧ ∀ m : V →₀ ℕ, ∃ z : ℤ, z.natAbs ≤ M ∧ p.coeff m = (z : ℚ) / (d : ℚ)

/-- Every polynomial with `HasBoundedIntCoeffs p M d` has bit-complexity at most
`Nat.size M + Nat.size d`. -/
theorem HasBoundedIntCoeffs.polyBitComplexity_le {V : Type u} {p : MvPolynomial V ℚ} {M d : ℕ}
    (hp : HasBoundedIntCoeffs p M d) :
    polyBitComplexity p ≤ Nat.size M + Nat.size d := by
  rw [polyBitComplexity_le_iff]
  intro m _
  rcases hp.2 m with ⟨z, hz, hcoeff⟩
  rw [hcoeff]
  have hd1 := hp.1
  have hd : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  exact (ratBitSize_div_intCast_le z hd).trans
    (by simpa using Nat.add_le_add_right (Nat.size_le_size hz) (Nat.size d))

/-- Every `{0, 1, -1}`-coefficient polynomial satisfies `HasBoundedIntCoeffs p 1 1`. -/
theorem HasBoundedIntCoeffs.of_unit {V : Type u} {p : MvPolynomial V ℚ}
    (hp : ∀ m : V →₀ ℕ, p.coeff m = 0 ∨ p.coeff m = 1 ∨ p.coeff m = -1) :
    HasBoundedIntCoeffs p 1 1 :=
  ⟨le_rfl, fun m ↦ by
    rcases hp m with h | h | h
    · exact ⟨0, by simp, by simp [h]⟩
    · exact ⟨1, by simp, by simp [h]⟩
    · exact ⟨-1, by simp, by simp [h]⟩⟩

/-- Multiplication by a variable preserves `HasBoundedIntCoeffs`. -/
theorem HasBoundedIntCoeffs.X_mul {V : Type u} (v : V) {p : MvPolynomial V ℚ} {M d : ℕ}
    (hp : HasBoundedIntCoeffs p M d) : HasBoundedIntCoeffs (X v * p) M d := by
  classical
  refine ⟨hp.1, fun m ↦ ?_⟩
  by_cases hmem : m ∈ (X v * p).support
  · rw [MvPolynomial.support_X_mul, Finset.mem_map] at hmem
    rcases hmem with ⟨m', _, rfl⟩
    change ∃ z : ℤ, z.natAbs ≤ M ∧ (X v * p).coeff (Finsupp.single v 1 + m') = (z : ℚ) / (d : ℚ)
    rw [MvPolynomial.coeff_X_mul]
    exact hp.2 m'
  · rw [MvPolynomial.notMem_support_iff.mp hmem]
    exact ⟨0, Nat.zero_le M, by simp⟩

/-- Negation preserves `HasBoundedIntCoeffs`. -/
theorem HasBoundedIntCoeffs.neg {V : Type u} {p : MvPolynomial V ℚ} {M d : ℕ}
    (hp : HasBoundedIntCoeffs p M d) : HasBoundedIntCoeffs (-p) M d :=
  ⟨hp.1, fun m ↦ by
    rcases hp.2 m with ⟨z, hz, hcoeff⟩
    exact ⟨-z, by simpa using hz, by simp [hcoeff, neg_div]⟩⟩

/-- Adding two polynomials with common denominator `d` adds their numerator bounds. -/
theorem HasBoundedIntCoeffs.add {V : Type u} {p q : MvPolynomial V ℚ} {M₁ M₂ d : ℕ}
    (hp : HasBoundedIntCoeffs p M₁ d) (hq : HasBoundedIntCoeffs q M₂ d) :
    HasBoundedIntCoeffs (p + q) (M₁ + M₂) d :=
  ⟨hp.1, fun m ↦ by
    rcases hp.2 m with ⟨z₁, hz₁, hc₁⟩
    rcases hq.2 m with ⟨z₂, hz₂, hc₂⟩
    refine ⟨z₁ + z₂, (Int.natAbs_add_le z₁ z₂).trans (Nat.add_le_add hz₁ hz₂), ?_⟩
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hc₁, hc₂, ← add_div]
    push_cast
    rfl⟩

/-- Scaling by `(a : ℚ) / (b : ℚ)` multiplies numerator and denominator bounds. -/
theorem HasBoundedIntCoeffs.div_smul {V : Type u} {p : MvPolynomial V ℚ} {M d : ℕ}
    (hp : HasBoundedIntCoeffs p M d) (a : ℤ) {b : ℕ} (hb : 1 ≤ b) :
    HasBoundedIntCoeffs (((a : ℚ) / (b : ℚ)) • p) (a.natAbs * M) (b * d) :=
  ⟨Nat.mul_pos hb hp.1, fun m ↦ by
    rcases hp.2 m with ⟨z, hz, hc⟩
    refine ⟨a * z, by rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ hz, ?_⟩
    rw [coeff_smul, smul_eq_mul, hc]
    push_cast
    ring⟩

/-- Finite sums with common denominator `d` sum their numerator bounds. -/
theorem HasBoundedIntCoeffs.finset_sum {V ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial V ℚ) {M d : ℕ} (hd : 1 ≤ d)
    (hg : ∀ i ∈ s, HasBoundedIntCoeffs (g i) M d) :
    HasBoundedIntCoeffs (∑ i ∈ s, g i) (s.card * M) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hd, fun _ ↦ ⟨0, by simp, by simp⟩⟩
  | insert i s₀ hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm _ M]
    exact (hg i (Finset.mem_insert_self i s₀)).add
      (ih fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))

/-- Single variable `X v` satisfies `HasBoundedIntCoeffs (X v) 1 1`. -/
theorem hasBoundedIntCoeffs_X {V : Type u} (v : V) :
    HasBoundedIntCoeffs (X v : MvPolynomial V ℚ) 1 1 :=
  .of_unit fun m ↦ by
    classical
    rw [coeff_X]
    split_ifs <;> simp

/-- Scaling denominator upward from `1` to any `d ≥ 1`. -/
theorem HasBoundedIntCoeffs.raise_den {V : Type u} {p : MvPolynomial V ℚ} {M d : ℕ}
    (hp : HasBoundedIntCoeffs p M d) {k : ℕ} (hk : 1 ≤ k) :
    HasBoundedIntCoeffs p (k * M) (k * d) :=
  ⟨Nat.mul_pos hk hp.1, fun m ↦ by
    rcases hp.2 m with ⟨z, hz, hc⟩
    have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨(k : ℤ) * z, by rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left k hz,
      ?_⟩
    rw [hc]
    push_cast
    rw [mul_div_mul_left _ _ hkq]⟩

end BitComplexity

section UnitMonomial

variable {V : Type u} {R : Type v}

/-- Monic syntactic monomial `∏ v, X v ^ s v` with coefficient `1`. -/
@[expose] def IsUnitMonomial [CommSemiring R] (p : MvPolynomial V R) : Prop :=
  ∃ s : V →₀ ℕ, p = MvPolynomial.monomial s 1

@[simp]
theorem isUnitMonomial_one [CommSemiring R] :
    IsUnitMonomial (1 : MvPolynomial V R) := ⟨0, by simp⟩

@[simp]
theorem isUnitMonomial_X [CommSemiring R] (v : V) :
    IsUnitMonomial (X v : MvPolynomial V R) := ⟨Finsupp.single v 1, rfl⟩

@[simp]
theorem isUnitMonomial_monomial_one [CommSemiring R] (s : V →₀ ℕ) :
    IsUnitMonomial (monomial s (1 : R)) := ⟨s, rfl⟩

/-- Product of two monic syntactic monomials is a monic syntactic monomial. -/
theorem IsUnitMonomial.mul [CommSemiring R] {p q : MvPolynomial V R}
    (hp : IsUnitMonomial p) (hq : IsUnitMonomial q) : IsUnitMonomial (p * q) := by
  rcases hp with ⟨s, rfl⟩
  rcases hq with ⟨t, rfl⟩
  exact ⟨s + t, by simp⟩

/-- Power of a monic syntactic monomial is a monic syntactic monomial. -/
theorem IsUnitMonomial.pow [CommSemiring R] {p : MvPolynomial V R}
    (hp : IsUnitMonomial p) (n : ℕ) : IsUnitMonomial (p ^ n) := by
  induction n with
  | zero => simp
  | succ _ ih => rw [pow_succ]; exact ih.mul hp

/-- Finite product of variables is a monic syntactic monomial. -/
theorem isUnitMonomial_finset_prod_X {ι : Type*} [CommSemiring R] (s : Finset ι) (f : ι → V) :
    IsUnitMonomial (∏ i ∈ s, X (f i) : MvPolynomial V R) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (isUnitMonomial_X _).mul ih

/-- Variable renaming preserves `IsUnitMonomial`. -/
theorem IsUnitMonomial.rename {W : Type*} [CommSemiring R] {p : MvPolynomial V R}
    (hp : IsUnitMonomial p) (f : V → W) : IsUnitMonomial (rename f p) := by
  rcases hp with ⟨s, rfl⟩
  exact ⟨s.mapDomain f, MvPolynomial.rename_monomial f s 1⟩

/-- Every monic monomial over a nontrivial semiring has monomial count `1`. -/
theorem IsUnitMonomial.polyMonomialCount_eq_one [CommSemiring R] [Nontrivial R]
    {p : MvPolynomial V R} (hp : IsUnitMonomial p) : polyMonomialCount p = 1 := by
  rcases hp with ⟨s, rfl⟩
  exact polyMonomialCount_monomial s one_ne_zero

/-- Every rational monic monomial has coefficient bit-complexity `2`. -/
theorem IsUnitMonomial.polyBitComplexity_eq_two {p : MvPolynomial V ℚ}
    (hp : IsUnitMonomial p) : polyBitComplexity p = 2 := by
  rcases hp with ⟨s, rfl⟩
  rw [polyBitComplexity_monomial s one_ne_zero, ratBitSize_one]

end UnitMonomial

/-! ### Line Measures and Inference Systems (`MC`, `PC`, `EPC`) -/

section LineMeasures

variable {V : Type u} {R : Type v}

/-- Every polynomial in `lines` has total degree at most `k`. -/
@[expose] def LinesMaxDegree [CommSemiring R] (lines : List (MvPolynomial V R)) (k : ℕ) : Prop :=
  ∀ p ∈ lines, p.totalDegree ≤ k

/-- `LinesMaxDegree` agrees with `Cslib.Logic.PL.PC.degree lines ≤ k`. -/
theorem linesMaxDegree_iff_cslib_degree_le [CommSemiring R]
    (lines : List (MvPolynomial V R)) (k : ℕ) :
    LinesMaxDegree lines k ↔ Cslib.Logic.PL.PC.degree lines ≤ k :=
  Cslib.Logic.PL.PC.degree_le_iff.symm

@[simp]
theorem linesMaxDegree_nil [CommSemiring R] (k : ℕ) :
    LinesMaxDegree ([] : List (MvPolynomial V R)) k :=
  fun _ h ↦ nomatch h

/-- Cons characterization for `LinesMaxDegree`. -/
theorem linesMaxDegree_cons [CommSemiring R] (p : MvPolynomial V R)
    (lines : List (MvPolynomial V R)) (k : ℕ) :
    LinesMaxDegree (p :: lines) k ↔ p.totalDegree ≤ k ∧ LinesMaxDegree lines k :=
  List.forall_mem_cons

/-- Append characterization for `LinesMaxDegree`. -/
theorem linesMaxDegree_append [CommSemiring R] (l₁ l₂ : List (MvPolynomial V R)) (k : ℕ) :
    LinesMaxDegree (l₁ ++ l₂) k ↔ LinesMaxDegree l₁ k ∧ LinesMaxDegree l₂ k :=
  List.forall_mem_append

/-- Monotonicity of `LinesMaxDegree` in the degree bound `k`. -/
theorem LinesMaxDegree.mono [CommSemiring R] {lines : List (MvPolynomial V R)} {k₁ k₂ : ℕ}
    (h : LinesMaxDegree lines k₁) (hle : k₁ ≤ k₂) : LinesMaxDegree lines k₂ :=
  fun p hp ↦ (h p hp).trans hle

/-- Variable renaming preserves `LinesMaxDegree`. -/
theorem LinesMaxDegree.map_rename {W : Type*} [CommSemiring R] {lines : List (MvPolynomial V R)}
    {k : ℕ} (h : LinesMaxDegree lines k) (f : V → W) :
    LinesMaxDegree (lines.map (rename f)) k := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact (totalDegree_rename_le f q).trans (h q hq)

/-- Total monomial size of a derivation trace (sum of monomial counts across lines), agreeing
definitionally with `Cslib.Logic.PL.PC.size`. -/
def derivLinesSize [CommSemiring R] (lines : List (MvPolynomial V R)) : ℕ :=
  (lines.map polyMonomialCount).sum

/-- `derivLinesSize` coincides with upstream `Cslib.Logic.PL.PC.size`. -/
theorem derivLinesSize_eq_cslib_size [CommSemiring R] (lines : List (MvPolynomial V R)) :
    derivLinesSize lines = Cslib.Logic.PL.PC.size lines := by rfl

@[simp, grind =]
theorem derivLinesSize_nil [CommSemiring R] :
    derivLinesSize ([] : List (MvPolynomial V R)) = 0 := by rfl

@[simp, grind =]
theorem derivLinesSize_cons [CommSemiring R]
    (p : MvPolynomial V R) (lines : List (MvPolynomial V R)) :
    derivLinesSize (p :: lines) = polyMonomialCount p + derivLinesSize lines := by rfl

@[simp, grind =]
theorem derivLinesSize_append [CommSemiring R] (l₁ l₂ : List (MvPolynomial V R)) :
    derivLinesSize (l₁ ++ l₂) = derivLinesSize l₁ + derivLinesSize l₂ := by
  simp [derivLinesSize]

/-- Injective variable renaming preserves total monomial size. -/
theorem derivLinesSize_map_rename_of_injective {W : Type*} [CommSemiring R]
    {f : V → W} (hf : Function.Injective f) (lines : List (MvPolynomial V R)) :
    derivLinesSize (lines.map (rename f)) = derivLinesSize lines := by
  induction lines with
  | nil => simp
  | cons _ _ ih => simp [polyMonomialCount_rename_of_injective hf, ih]

/-- Maximum coefficient bit-complexity across a rational derivation trace. -/
def derivLinesBitComplexity (lines : List (MvPolynomial V ℚ)) : ℕ :=
  (lines.map polyBitComplexity).foldr max 0

@[simp, grind =]
theorem derivLinesBitComplexity_nil :
    derivLinesBitComplexity ([] : List (MvPolynomial V ℚ)) = 0 := by rfl

@[simp, grind =]
theorem derivLinesBitComplexity_cons
    (p : MvPolynomial V ℚ) (lines : List (MvPolynomial V ℚ)) :
    derivLinesBitComplexity (p :: lines) =
      max (polyBitComplexity p) (derivLinesBitComplexity lines) := by rfl

@[simp, grind =]
theorem derivLinesBitComplexity_append (l₁ l₂ : List (MvPolynomial V ℚ)) :
    derivLinesBitComplexity (l₁ ++ l₂) =
      max (derivLinesBitComplexity l₁) (derivLinesBitComplexity l₂) := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => simp [ih, max_assoc]

/-- Upper bound characterization for `derivLinesBitComplexity`. -/
theorem derivLinesBitComplexity_le_iff {lines : List (MvPolynomial V ℚ)} {b : ℕ} :
    derivLinesBitComplexity lines ≤ b ↔ ∀ p ∈ lines, polyBitComplexity p ≤ b := by
  induction lines with
  | nil => simp
  | cons _ _ ih => simp [ih]

/-- Injective variable renaming preserves `derivLinesBitComplexity`. -/
theorem derivLinesBitComplexity_map_rename_of_injective {W : Type*}
    {f : V → W} (hf : Function.Injective f) (lines : List (MvPolynomial V ℚ)) :
    derivLinesBitComplexity (lines.map (rename f)) = derivLinesBitComplexity lines := by
  induction lines with
  | nil => simp
  | cons _ _ ih => simp [polyBitComplexity_rename_of_injective hf, ih]

end LineMeasures

section Derivations

variable {V : Type u} {R : Type v}

/-- Multiplicand side-condition for the monomial calculus ($\mathrm{MC}$): `f` is either a monic
monomial or the product of a monic monomial and an input or Boolean axiom. -/
@[expose] def IsMCMultiplicand [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R))
    (f : MvPolynomial V R) : Prop :=
  IsUnitMonomial f ∨
    ∃ m a, IsUnitMonomial m ∧ (a ∈ P ∨ ∃ v ∈ baseVars, a = X v ^ 2 - X v) ∧ f = m * a

/-- Every monic monomial is an allowed $\mathrm{MC}$ multiplicand. -/
theorem isMCMultiplicand_of_isUnitMonomial [CommRing R] (baseVars : Set V)
    (P : Set (MvPolynomial V R)) {f : MvPolynomial V R} (hf : IsUnitMonomial f) :
    IsMCMultiplicand baseVars P f :=
  Or.inl hf

/-- Every input axiom `p ∈ P` is an allowed $\mathrm{MC}$ multiplicand. -/
theorem isMCMultiplicand_of_mem [CommRing R] (baseVars : Set V)
    {P : Set (MvPolynomial V R)} {p : MvPolynomial V R} (hp : p ∈ P) :
    IsMCMultiplicand baseVars P p :=
  Or.inr ⟨1, p, isUnitMonomial_one, Or.inl hp, (one_mul p).symm⟩

/-- Every Boolean axiom `X v ^ 2 - X v` (`v ∈ baseVars`) is an allowed $\mathrm{MC}$
multiplicand. -/
theorem isMCMultiplicand_of_boolAx [CommRing R] {baseVars : Set V}
    (P : Set (MvPolynomial V R)) {v : V} (hv : v ∈ baseVars) :
    IsMCMultiplicand baseVars P (X v ^ 2 - X v) :=
  Or.inr ⟨1, X v ^ 2 - X v, isUnitMonomial_one, Or.inr ⟨v, hv, rfl⟩, by simp⟩

/-- Multiplying an allowed $\mathrm{MC}$ multiplicand by a monic monomial keeps it valid. -/
theorem IsMCMultiplicand.mul_isUnitMonomial [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {m f : MvPolynomial V R}
    (hm : IsUnitMonomial m) (hf : IsMCMultiplicand baseVars P f) :
    IsMCMultiplicand baseVars P (m * f) := by
  rcases hf with hunit | ⟨m₀, a, hm₀, ha, rfl⟩
  exacts [Or.inl (hm.mul hunit), Or.inr ⟨m * m₀, a, hm.mul hm₀, ha, (mul_assoc m m₀ a).symm⟩]

/-- Renaming variables preserves `IsMCMultiplicand`. -/
theorem IsMCMultiplicand.rename {W : Type*} [CommRing R]
    {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') {f : MvPolynomial V R}
    (hf : IsMCMultiplicand baseVars P f) :
    IsMCMultiplicand baseVars' P' (MvPolynomial.rename φ f) := by
  rcases hf with hunit | ⟨m, a, hm, ha, rfl⟩
  · exact Or.inl (hunit.rename φ)
  · refine Or.inr ⟨MvPolynomial.rename φ m, MvPolynomial.rename φ a, hm.rename φ, ?_, by simp⟩
    rcases ha with hp | ⟨v, hv, rfl⟩
    exacts [Or.inl (hP a hp), Or.inr ⟨φ v, hbase v hv, by simp⟩]

/-- Explicit finite derivation sequence in the monomial calculus ($\mathrm{MC}$), ordered newest
line at the head. -/
inductive MCDeriv [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R)) :
    List (MvPolynomial V R) → Type (max u v)
  /-- Empty derivation. -/
  | nil : MCDeriv baseVars P []
  /-- Introduction of an input axiom `p ∈ P`. -/
  | inputAx {lines p} (d : MCDeriv baseVars P lines) (hp : p ∈ P) : MCDeriv baseVars P (p :: lines)
  /-- Introduction of a Boolean axiom `X v ^ 2 - X v` for `v ∈ baseVars`. -/
  | boolAx {lines v} (d : MCDeriv baseVars P lines) (hv : v ∈ baseVars) :
      MCDeriv baseVars P ((X v ^ 2 - X v) :: lines)
  /-- Restricted multiplication `X v * f` where `f` is an $\mathrm{MC}$ multiplicand. -/
  | mulVar {lines v f} (d : MCDeriv baseVars P lines)
      (hv : v ∈ baseVars) (hf : f ∈ lines) (hmc : IsMCMultiplicand baseVars P f) :
      MCDeriv baseVars P ((X v * f) :: lines)
  /-- Scalar linear combination `a • g + b • f` of two previously derived lines. -/
  | linComb {lines} {a b : R} {g f} (d : MCDeriv baseVars P lines)
      (hg : g ∈ lines) (hf : f ∈ lines) : MCDeriv baseVars P ((a • g + b • f) :: lines)

/-- Explicit finite derivation sequence in the polynomial calculus ($\mathrm{PC}$), ordered newest
line at the head. -/
inductive PCDeriv [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R)) :
    List (MvPolynomial V R) → Type (max u v)
  /-- Empty derivation. -/
  | nil : PCDeriv baseVars P []
  /-- Introduction of an input axiom `p ∈ P`. -/
  | inputAx {lines p} (d : PCDeriv baseVars P lines) (hp : p ∈ P) : PCDeriv baseVars P (p :: lines)
  /-- Introduction of a Boolean axiom `X v ^ 2 - X v` for `v ∈ baseVars`. -/
  | boolAx {lines v} (d : PCDeriv baseVars P lines) (hv : v ∈ baseVars) :
      PCDeriv baseVars P ((X v ^ 2 - X v) :: lines)
  /-- Multiplication `X v * f` of a prior line `f` by a base variable `v ∈ baseVars`. -/
  | mulVar {lines v f} (d : PCDeriv baseVars P lines) (hv : v ∈ baseVars) (hf : f ∈ lines) :
      PCDeriv baseVars P ((X v * f) :: lines)
  /-- Scalar linear combination `a • g + b • f` of two previously derived lines. -/
  | linComb {lines} {a b : R} {g f} (d : PCDeriv baseVars P lines)
      (hg : g ∈ lines) (hf : f ∈ lines) : PCDeriv baseVars P ((a • g + b • f) :: lines)

/-- Explicit finite derivation sequence in the extended polynomial calculus ($\mathrm{EPC}$),
tracking introduced extension variables `exts` and derived polynomials `lines` (newest at head).
Boolean axioms apply solely to `baseVars`, while extension axioms introduce `X x - f` for a fresh
variable `x` outside `baseVars`, `exts`, and all input axioms in `P`. -/
inductive EPCDeriv [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R)) :
    List V → List (MvPolynomial V R) → Type (max u v)
  /-- Empty derivation with no extension variables and no lines. -/
  | nil : EPCDeriv baseVars P [] []
  /-- Introduction of an input axiom `p ∈ P`. -/
  | inputAx {exts lines p} (d : EPCDeriv baseVars P exts lines) (hp : p ∈ P) :
      EPCDeriv baseVars P exts (p :: lines)
  /-- Introduction of a Boolean axiom `X v ^ 2 - X v` strictly for `v ∈ baseVars`. -/
  | boolAx {exts lines v} (d : EPCDeriv baseVars P exts lines) (hv : v ∈ baseVars) :
      EPCDeriv baseVars P exts ((X v ^ 2 - X v) :: lines)
  /-- Multiplication `X v * f` by an active variable `v ∈ baseVars ∨ v ∈ exts`. -/
  | mulVar {exts lines v f} (d : EPCDeriv baseVars P exts lines)
      (hv : v ∈ baseVars ∨ v ∈ exts) (hf : f ∈ lines) :
      EPCDeriv baseVars P exts ((X v * f) :: lines)
  /-- Scalar linear combination `a • g + b • f` of two prior lines. -/
  | linComb {exts lines} {a b : R} {g f} (d : EPCDeriv baseVars P exts lines)
      (hg : g ∈ lines) (hf : f ∈ lines) : EPCDeriv baseVars P exts ((a • g + b • f) :: lines)
  /-- Extension axiom `X x - f` introducing a fresh extension variable `x` for a polynomial `f`
  over the currently active variables `baseVars ∪ exts` (so `x ∉ f.vars`). -/
  | extAx {exts lines x f} (d : EPCDeriv baseVars P exts lines)
      (hx_base : x ∉ baseVars) (hx_P : ∀ p ∈ P, x ∉ p.vars) (hx_fresh : x ∉ exts)
      (hf_vars : ∀ v ∈ f.vars, v ∈ baseVars ∨ v ∈ exts) :
      EPCDeriv baseVars P (x :: exts) ((X x - f) :: lines)

/-- Transport an `MCDeriv` along a line-list equality. -/
def MCDeriv.cast [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines lines' : List (MvPolynomial V R)} (hl : lines = lines')
    (d : MCDeriv baseVars P lines) : MCDeriv baseVars P lines' :=
  hl ▸ d

/-- Transport a `PCDeriv` along a line-list equality. -/
def PCDeriv.cast [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines lines' : List (MvPolynomial V R)} (hl : lines = lines')
    (d : PCDeriv baseVars P lines) : PCDeriv baseVars P lines' :=
  hl ▸ d

/-- Transport an `EPCDeriv` along extension-list and line-list equalities. -/
def EPCDeriv.cast [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {exts exts' : List V} {lines lines' : List (MvPolynomial V R)} (he : exts = exts')
    (hl : lines = lines') (d : EPCDeriv baseVars P exts lines) : EPCDeriv baseVars P exts' lines' :=
  he ▸ hl ▸ d

/-- Convenience `extAx` constructor when all input polynomials in `P` use only `baseVars`. -/
def EPCDeriv.extAxOfBaseVars [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    (hP_vars : ∀ p ∈ P, (p.vars : Set V) ⊆ baseVars) {exts lines}
    (d : EPCDeriv baseVars P exts lines) {x : V} {f : MvPolynomial V R}
    (hx_base : x ∉ baseVars) (hx_fresh : x ∉ exts)
    (hf_vars : ∀ v ∈ f.vars, v ∈ baseVars ∨ v ∈ exts) :
    EPCDeriv baseVars P (x :: exts) ((X x - f) :: lines) :=
  d.extAx hx_base (fun p hp hx_p ↦ hx_base (hP_vars p hp hx_p)) hx_fresh hf_vars

/-- Embed a monomial calculus derivation into `PCDeriv`. -/
def MCDeriv.toPCDeriv [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)} :
    ∀ {lines}, MCDeriv baseVars P lines → PCDeriv baseVars P lines
  | _, .nil => .nil
  | _, .inputAx d hp => d.toPCDeriv.inputAx hp
  | _, .boolAx d hv => d.toPCDeriv.boolAx hv
  | _, .mulVar d hv hf _ => d.toPCDeriv.mulVar hv hf
  | _, .linComb d hg hf => d.toPCDeriv.linComb hg hf

/-- Embed a polynomial calculus derivation into `EPCDeriv` with zero extension variables. -/
def PCDeriv.toEPCDeriv [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)} :
    ∀ {lines}, PCDeriv baseVars P lines → EPCDeriv baseVars P [] lines
  | _, .nil => .nil
  | _, .inputAx d hp => d.toEPCDeriv.inputAx hp
  | _, .boolAx d hv => d.toEPCDeriv.boolAx hv
  | _, .mulVar d hv hf => d.toEPCDeriv.mulVar (Or.inl hv) hf
  | _, .linComb d hg hf => d.toEPCDeriv.linComb hg hf

private def EPCDeriv.toPCDerivAux [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)} :
    ∀ {exts lines}, EPCDeriv baseVars P exts lines → exts = [] → PCDeriv baseVars P lines
  | _, _, .nil, _ => .nil
  | _, _, .inputAx d hp, h => (d.toPCDerivAux h).inputAx hp
  | _, _, .boolAx d hv, h => (d.toPCDerivAux h).boolAx hv
  | _, _, .mulVar d hv hf, h =>
      (d.toPCDerivAux h).mulVar (hv.elim id fun he ↦ nomatch h ▸ he) hf
  | _, _, .linComb d hg hf, h => (d.toPCDerivAux h).linComb hg hf
  | _, _, .extAx _ _ _ _ _, h => nomatch h

/-- Project an `EPCDeriv` with `exts = []` back to a `PCDeriv`. -/
def EPCDeriv.toPCDeriv [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines : List (MvPolynomial V R)} (d : EPCDeriv baseVars P [] lines) :
    PCDeriv baseVars P lines :=
  d.toPCDerivAux rfl

/-- Degree bound `≤ k` on all lines of an `MCDeriv`. -/
@[expose] def MCDeriv.HasMaxDegree [CommRing R] {baseVars : Set V}
  {P : Set (MvPolynomial V R)}
    {lines} (_ : MCDeriv baseVars P lines) (k : ℕ) : Prop :=
  LinesMaxDegree lines k

/-- Total monomial size of an `MCDeriv`. -/
@[expose] def MCDeriv.size [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines} (_ : MCDeriv baseVars P lines) : ℕ :=
  derivLinesSize lines

/-- Maximum rational coefficient bit-complexity of an `MCDeriv`. -/
@[expose] def MCDeriv.bitComplexity {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {lines} (_ : MCDeriv baseVars P lines) : ℕ :=
  derivLinesBitComplexity lines

/-- Degree bound `≤ k` on all lines of a `PCDeriv`. -/
@[expose] def PCDeriv.HasMaxDegree [CommRing R] {baseVars : Set V}
  {P : Set (MvPolynomial V R)}
    {lines} (_ : PCDeriv baseVars P lines) (k : ℕ) : Prop :=
  LinesMaxDegree lines k

/-- Total monomial size of a `PCDeriv`. -/
@[expose] def PCDeriv.size [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines} (_ : PCDeriv baseVars P lines) : ℕ :=
  derivLinesSize lines

/-- Maximum rational coefficient bit-complexity of a `PCDeriv`. -/
@[expose] def PCDeriv.bitComplexity {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {lines} (_ : PCDeriv baseVars P lines) : ℕ :=
  derivLinesBitComplexity lines

/-- Degree bound `≤ k` on all lines of an `EPCDeriv`. -/
@[expose] def EPCDeriv.HasMaxDegree [CommRing R] {baseVars : Set V}
  {P : Set (MvPolynomial V R)}
    {exts lines} (_ : EPCDeriv baseVars P exts lines) (k : ℕ) : Prop :=
  LinesMaxDegree lines k

/-- Total monomial size of an `EPCDeriv`. -/
@[expose] def EPCDeriv.size [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {exts lines} (_ : EPCDeriv baseVars P exts lines) : ℕ :=
  derivLinesSize lines

/-- Maximum rational coefficient bit-complexity of an `EPCDeriv`. -/
@[expose] def EPCDeriv.bitComplexity {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {exts lines} (_ : EPCDeriv baseVars P exts lines) : ℕ :=
  derivLinesBitComplexity lines

/-- Number of extension variables introduced by an `EPCDeriv`. -/
@[expose] def EPCDeriv.numExtVars [CommRing R] {baseVars : Set V}
  {P : Set (MvPolynomial V R)}
    {exts lines} (_ : EPCDeriv baseVars P exts lines) : ℕ :=
  exts.length

@[simp] theorem MCDeriv.size_nil [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)} :
    (MCDeriv.nil (baseVars := baseVars) (P := P)).size = 0 := derivLinesSize_nil

@[simp] theorem MCDeriv.size_inputAx [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines p} (d : MCDeriv baseVars P lines) (hp : p ∈ P) :
    (d.inputAx hp).size = polyMonomialCount p + d.size := derivLinesSize_cons _ _

@[simp] theorem MCDeriv.size_boolAx [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines v} (d : MCDeriv baseVars P lines) (hv : v ∈ baseVars) :
    (d.boolAx hv).size = polyMonomialCount (X v ^ 2 - X v : MvPolynomial V R) + d.size :=
  derivLinesSize_cons _ _

@[simp] theorem MCDeriv.size_mulVar [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines v f} (d : MCDeriv baseVars P lines) (hv : v ∈ baseVars) (hf : f ∈ lines)
    (hmc : IsMCMultiplicand baseVars P f) :
    (d.mulVar hv hf hmc).size = polyMonomialCount (X v * f) + d.size := derivLinesSize_cons _ _

@[simp] theorem MCDeriv.size_linComb [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {lines} {a b : R} {g f} (d : MCDeriv baseVars P lines) (hg : g ∈ lines) (hf : f ∈ lines) :
    (d.linComb (a := a) (b := b) hg hf).size = polyMonomialCount (a • g + b • f) + d.size :=
  derivLinesSize_cons _ _

@[simp] theorem MCDeriv.bitComplexity_nil {baseVars : Set V} {P : Set (MvPolynomial V ℚ)} :
    (MCDeriv.nil (baseVars := baseVars) (P := P)).bitComplexity = 0 := derivLinesBitComplexity_nil

@[simp] theorem MCDeriv.bitComplexity_inputAx {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {lines p} (d : MCDeriv baseVars P lines) (hp : p ∈ P) :
    (d.inputAx hp).bitComplexity = max (polyBitComplexity p) d.bitComplexity :=
  derivLinesBitComplexity_cons _ _

@[simp] theorem MCDeriv.bitComplexity_boolAx {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {lines v} (d : MCDeriv baseVars P lines) (hv : v ∈ baseVars) :
    (d.boolAx hv).bitComplexity =
      max (polyBitComplexity (X v ^ 2 - X v : MvPolynomial V ℚ)) d.bitComplexity :=
  derivLinesBitComplexity_cons _ _

@[simp] theorem MCDeriv.bitComplexity_mulVar {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {lines v f} (d : MCDeriv baseVars P lines) (hv : v ∈ baseVars) (hf : f ∈ lines)
    (hmc : IsMCMultiplicand baseVars P f) :
    (d.mulVar hv hf hmc).bitComplexity = max (polyBitComplexity (X v * f)) d.bitComplexity :=
  derivLinesBitComplexity_cons _ _

@[simp] theorem MCDeriv.bitComplexity_linComb {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {lines} {a b : ℚ} {g f} (d : MCDeriv baseVars P lines) (hg : g ∈ lines) (hf : f ∈ lines) :
    (d.linComb (a := a) (b := b) hg hf).bitComplexity =
      max (polyBitComplexity (a • g + b • f)) d.bitComplexity :=
  derivLinesBitComplexity_cons _ _

theorem MCDeriv.hasMaxDegree_mulVar_iff [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines v f} (d : MCDeriv baseVars P lines) (hv : v ∈ baseVars)
    (hf : f ∈ lines) (hmc : IsMCMultiplicand baseVars P f) (k : ℕ) :
    (d.mulVar hv hf hmc).HasMaxDegree k ↔ (X v * f).totalDegree ≤ k ∧ d.HasMaxDegree k :=
  linesMaxDegree_cons _ _ k

theorem MCDeriv.hasMaxDegree_linComb_iff [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines} {a b : R} {g f} (d : MCDeriv baseVars P lines)
    (hg : g ∈ lines) (hf : f ∈ lines) (k : ℕ) :
    (d.linComb (a := a) (b := b) hg hf).HasMaxDegree k ↔
      (a • g + b • f).totalDegree ≤ k ∧ d.HasMaxDegree k :=
  linesMaxDegree_cons _ _ k

@[simp]
theorem MCDeriv.hasMaxDegree_toPCDeriv [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines} (d : MCDeriv baseVars P lines) (k : ℕ) :
    d.toPCDeriv.HasMaxDegree k ↔ d.HasMaxDegree k := by rfl

@[simp]
theorem PCDeriv.hasMaxDegree_toEPCDeriv [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines} (d : PCDeriv baseVars P lines) (k : ℕ) :
    d.toEPCDeriv.HasMaxDegree k ↔ d.HasMaxDegree k := by rfl

@[simp]
theorem PCDeriv.numExtVars_toEPCDeriv [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines} (d : PCDeriv baseVars P lines) :
    d.toEPCDeriv.numExtVars = 0 := by rfl

/-- Invariant asserting that every extension axiom `X x - f` in an `EPCDeriv` satisfies `Φ` on the
active variable set `baseVars ∪ exts` at the point of introduction. -/
def EPCDeriv.ExtAxiomsSatisfy [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    (Φ : Set V → MvPolynomial V R → Prop) :
    ∀ {exts : List V} {lines : List (MvPolynomial V R)}, EPCDeriv baseVars P exts lines → Prop
  | _, _, .nil => True
  | _, _, .inputAx d _ => d.ExtAxiomsSatisfy Φ
  | _, _, .boolAx d _ => d.ExtAxiomsSatisfy Φ
  | _, _, .mulVar d _ _ => d.ExtAxiomsSatisfy Φ
  | _, _, .linComb d _ _ => d.ExtAxiomsSatisfy Φ
  | _, _, .extAx (exts := exts) (f := f) d _ _ _ _ =>
      Φ {v | v ∈ baseVars ∨ v ∈ exts} f ∧ d.ExtAxiomsSatisfy Φ

section ExtAxiomsSatisfyAPI

variable [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
  (Φ : Set V → MvPolynomial V R → Prop)

@[simp]
theorem EPCDeriv.extAxiomsSatisfy_cast {exts exts' : List V}
    {lines lines' : List (MvPolynomial V R)} (he : exts = exts') (hl : lines = lines')
    (d : EPCDeriv baseVars P exts lines) :
    (d.cast he hl).ExtAxiomsSatisfy Φ ↔ d.ExtAxiomsSatisfy Φ := by
  subst he hl
  rfl

@[simp]
theorem EPCDeriv.extAxiomsSatisfy_nil :
    (EPCDeriv.nil (baseVars := baseVars) (P := P)).ExtAxiomsSatisfy Φ := trivial

@[simp]
theorem EPCDeriv.extAxiomsSatisfy_inputAx {exts lines p}
    (d : EPCDeriv baseVars P exts lines) (hp : p ∈ P) :
    (d.inputAx hp).ExtAxiomsSatisfy Φ ↔ d.ExtAxiomsSatisfy Φ := by rfl

@[simp]
theorem EPCDeriv.extAxiomsSatisfy_boolAx {exts lines v}
    (d : EPCDeriv baseVars P exts lines) (hv : v ∈ baseVars) :
    (d.boolAx hv).ExtAxiomsSatisfy Φ ↔ d.ExtAxiomsSatisfy Φ := by rfl

@[simp]
theorem EPCDeriv.extAxiomsSatisfy_mulVar {exts lines v f}
    (d : EPCDeriv baseVars P exts lines) (hv : v ∈ baseVars ∨ v ∈ exts) (hf : f ∈ lines) :
    (d.mulVar hv hf).ExtAxiomsSatisfy Φ ↔ d.ExtAxiomsSatisfy Φ := by rfl

@[simp]
theorem EPCDeriv.extAxiomsSatisfy_linComb {exts lines} {a b : R} {g f}
    (d : EPCDeriv baseVars P exts lines) (hg : g ∈ lines) (hf : f ∈ lines) :
    (d.linComb (a := a) (b := b) hg hf).ExtAxiomsSatisfy Φ ↔ d.ExtAxiomsSatisfy Φ := by rfl

/-- Characterization of `ExtAxiomsSatisfy` on an extension-axiom step. -/
theorem EPCDeriv.extAxiomsSatisfy_extAx {exts lines x f}
    (d : EPCDeriv baseVars P exts lines) (hx_base : x ∉ baseVars) (hx_P : ∀ p ∈ P, x ∉ p.vars)
    (hx_fresh : x ∉ exts) (hf_vars : ∀ v ∈ f.vars, v ∈ baseVars ∨ v ∈ exts) :
    (d.extAx hx_base hx_P hx_fresh hf_vars).ExtAxiomsSatisfy Φ ↔
      Φ {v | v ∈ baseVars ∨ v ∈ exts} f ∧ d.ExtAxiomsSatisfy Φ := by rfl

/-- Characterization of `ExtAxiomsSatisfy` on `extAxOfBaseVars`. -/
theorem EPCDeriv.extAxiomsSatisfy_extAxOfBaseVars
    (hP_vars : ∀ p ∈ P, (p.vars : Set V) ⊆ baseVars) {exts lines}
    (d : EPCDeriv baseVars P exts lines) {x : V} {f : MvPolynomial V R}
    (hx_base : x ∉ baseVars) (hx_fresh : x ∉ exts)
    (hf_vars : ∀ v ∈ f.vars, v ∈ baseVars ∨ v ∈ exts) :
    (d.extAxOfBaseVars hP_vars hx_base hx_fresh hf_vars).ExtAxiomsSatisfy Φ ↔
      Φ {v | v ∈ baseVars ∨ v ∈ exts} f ∧ d.ExtAxiomsSatisfy Φ := by rfl

@[simp]
theorem PCDeriv.extAxiomsSatisfy_toEPCDeriv {lines} (d : PCDeriv baseVars P lines) :
    d.toEPCDeriv.ExtAxiomsSatisfy Φ := by
  induction d <;> simp [PCDeriv.toEPCDeriv, *]

end ExtAxiomsSatisfyAPI

end Derivations

/-! ### Structural Invariants, Renaming, Concatenation, and Combinators -/

section StructuralOps

variable {V : Type u} {R : Type v}

private theorem vars_X_subset [CommRing R] (v : V) : (X v : MvPolynomial V R).vars ⊆ {v} := by
  classical
  intro u hu
  rcases (MvPolynomial.mem_vars_iff_mem_support u).mp hu with ⟨d, hd, hud⟩
  have hd' := Finset.mem_singleton.mp
    (MvPolynomial.support_monomial_subset (a := (1 : R)) (s := Finsupp.single v 1) hd)
  subst hd'
  exact Finset.mem_singleton.mpr (by simpa [Finsupp.support_single] using hud)

private theorem vars_smul_subset [CommRing R] (c : R) (p : MvPolynomial V R) :
    (c • p).vars ⊆ p.vars := by
  classical
  rw [smul_eq_C_mul]
  simpa [MvPolynomial.vars_C] using MvPolynomial.vars_mul (C c) p

private theorem mem_vars_neg [CommRing R] {f : MvPolynomial V R} {v : V}
    (hv : v ∈ (-f).vars) : v ∈ f.vars := by
  classical
  rcases (MvPolynomial.mem_vars_iff_mem_support v).mp hv with ⟨m, hm, hmv⟩
  rw [mem_support_iff, coeff_neg, neg_ne_zero, ← mem_support_iff] at hm
  exact (MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨m, hm, hmv⟩

private theorem totalDegree_X_le [CommRing R] (v : V) :
    (X v : MvPolynomial V R).totalDegree ≤ 1 := by
  simpa [X, Finsupp.sum_single_index] using totalDegree_monomial_le (Finsupp.single v 1) (1 : R)

/-- Every variable occurring in `exts` is outside `baseVars` and does not occur in `P`. -/
theorem EPCDeriv.extVars_fresh [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)} :
    ∀ {exts lines}, EPCDeriv baseVars P exts lines →
      ∀ x ∈ exts, x ∉ baseVars ∧ ∀ p ∈ P, x ∉ p.vars
  | _, _, .nil, _, h => nomatch h
  | _, _, .inputAx d _, x, h => d.extVars_fresh x h
  | _, _, .boolAx d _, x, h => d.extVars_fresh x h
  | _, _, .mulVar d _ _, x, h => d.extVars_fresh x h
  | _, _, .linComb d _ _, x, h => d.extVars_fresh x h
  | _, _, .extAx d hxb hxP _ _, x, h => by
    rcases List.mem_cons.mp h with rfl | h'
    exacts [⟨hxb, hxP⟩, d.extVars_fresh x h']

/-- The extension variable list `exts` of any `EPCDeriv` is duplicate-free. -/
theorem EPCDeriv.nodup_exts [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)} :
    ∀ {exts lines}, EPCDeriv baseVars P exts lines → exts.Nodup
  | _, _, .nil => List.nodup_nil
  | _, _, .inputAx d _ => d.nodup_exts
  | _, _, .boolAx d _ => d.nodup_exts
  | _, _, .mulVar d _ _ => d.nodup_exts
  | _, _, .linComb d _ _ => d.nodup_exts
  | _, _, .extAx d _ _ hxf _ => List.nodup_cons.mpr ⟨hxf, d.nodup_exts⟩

/-- Every variable in any line of `d` lies in `baseVars`, `exts`, or `vars(P)`. -/
theorem EPCDeriv.vars_mem_lines [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {exts : List V} {lines : List (MvPolynomial V R)}
    (d : EPCDeriv baseVars P exts lines) :
    ∀ q ∈ lines, ∀ v ∈ q.vars, v ∈ baseVars ∨ v ∈ exts ∨ ∃ p ∈ P, v ∈ p.vars := by
  classical
  induction d with
  | nil => simp
  | inputAx _ hp ih =>
    rintro q hq v hv
    rcases List.mem_cons.mp hq with rfl | hq'
    exacts [Or.inr (Or.inr ⟨_, hp, hv⟩), ih q hq' v hv]
  | boolAx _ hv_base ih =>
    rintro q hq v hv
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [sub_eq_add_neg] at hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with h1 | h2
      · exact Or.inl (Finset.mem_singleton.mp
          (vars_X_subset _ (MvPolynomial.vars_pow _ 2 h1)) ▸ hv_base)
      · exact Or.inl (Finset.mem_singleton.mp (vars_X_subset _ (mem_vars_neg h2)) ▸ hv_base)
    · exact ih q hq' v hv
  | mulVar _ hv_act hf ih =>
    rintro q hq v hv
    rcases List.mem_cons.mp hq with rfl | hq'
    · rcases Finset.mem_union.mp (MvPolynomial.vars_mul (X _) _ hv) with hvX | hvf
      exacts [((Finset.mem_singleton.mp (vars_X_subset _ hvX)) ▸ hv_act).imp id Or.inl,
        ih _ hf v hvf]
    · exact ih q hq' v hv
  | linComb _ hg hf ih =>
    rintro q hq v hv
    rcases List.mem_cons.mp hq with rfl | hq'
    · rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with hvg | hvf
      exacts [ih _ hg v (vars_smul_subset _ _ hvg), ih _ hf v (vars_smul_subset _ _ hvf)]
    · exact ih q hq' v hv
  | extAx _ _ _ _ hf_vars ih =>
    rintro q hq v hv
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [sub_eq_add_neg] at hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with hvX | hvf
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp (vars_X_subset _ hvX) ▸ List.mem_cons_self))
      · rcases hf_vars v (mem_vars_neg hvf) with hb | he
        exacts [Or.inl hb, Or.inr (Or.inl (List.mem_cons_of_mem _ he))]
    · rcases ih q hq' v hv with hb | he | hp
      exacts [Or.inl hb, Or.inr (Or.inl (List.mem_cons_of_mem _ he)), Or.inr (Or.inr hp)]

/-- Any variable outside `baseVars`, `exts`, and `P` does not occur in any line of `d`. -/
theorem EPCDeriv.notMem_vars_lines_of_fresh [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {exts : List V} {lines : List (MvPolynomial V R)}
    (d : EPCDeriv baseVars P exts lines) {x : V}
    (hx_base : x ∉ baseVars) (hx_exts : x ∉ exts) (hx_P : ∀ p ∈ P, x ∉ p.vars) :
    ∀ q ∈ lines, x ∉ q.vars :=
  fun q hq hx ↦
    (d.vars_mem_lines q hq x hx).elim hx_base (·.elim hx_exts fun ⟨p, hp, hxp⟩ ↦ hx_P p hp hxp)

/-- Rename variables in an `MCDeriv`. -/
noncomputable def MCDeriv.rename {W : Type*} [CommRing R]
    {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') :
    ∀ {lines}, MCDeriv baseVars P lines → MCDeriv baseVars' P' (lines.map (MvPolynomial.rename φ))
  | _, .nil => .nil
  | _, .inputAx d hp => (d.rename φ hbase hP).inputAx (hP _ hp)
  | _, .boolAx d hv => ((d.rename φ hbase hP).boolAx (hbase _ hv)).cast (by simp)
  | _, .mulVar d hv hf hmc =>
    ((d.rename φ hbase hP).mulVar (hbase _ hv) (List.mem_map.mpr ⟨_, hf, rfl⟩)
      (hmc.rename φ hbase hP)).cast (by simp)
  | _, .linComb (a := a) (b := b) d hg hf =>
    ((d.rename φ hbase hP).linComb (a := a) (b := b)
      (List.mem_map.mpr ⟨_, hg, rfl⟩) (List.mem_map.mpr ⟨_, hf, rfl⟩)).cast (by simp)

/-- Degree preservation under `MCDeriv.rename`. -/
theorem MCDeriv.hasMaxDegree_rename {W : Type*} [CommRing R]
    {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') {lines} {d : MCDeriv baseVars P lines}
    {k : ℕ} (hd : d.HasMaxDegree k) : (d.rename φ hbase hP).HasMaxDegree k :=
  LinesMaxDegree.map_rename hd φ

/-- Rename variables in a `PCDeriv`. -/
noncomputable def PCDeriv.rename {W : Type*} [CommRing R]
    {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') :
    ∀ {lines}, PCDeriv baseVars P lines → PCDeriv baseVars' P' (lines.map (MvPolynomial.rename φ))
  | _, .nil => .nil
  | _, .inputAx d hp => (d.rename φ hbase hP).inputAx (hP _ hp)
  | _, .boolAx d hv => ((d.rename φ hbase hP).boolAx (hbase _ hv)).cast (by simp)
  | _, .mulVar d hv hf =>
    ((d.rename φ hbase hP).mulVar (hbase _ hv) (List.mem_map.mpr ⟨_, hf, rfl⟩)).cast (by simp)
  | _, .linComb (a := a) (b := b) d hg hf =>
    ((d.rename φ hbase hP).linComb (a := a) (b := b)
      (List.mem_map.mpr ⟨_, hg, rfl⟩) (List.mem_map.mpr ⟨_, hf, rfl⟩)).cast (by simp)

/-- Injective variable renaming of an `EPCDeriv`. -/
noncomputable def EPCDeriv.rename {W : Type*} [CommRing R]
    {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hφ : Function.Injective φ) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') :
    ∀ {exts lines}, EPCDeriv baseVars P exts lines →
      (∀ x ∈ exts, φ x ∉ baseVars') → (∀ x ∈ exts, ∀ p' ∈ P', φ x ∉ p'.vars) →
      EPCDeriv baseVars' P' (exts.map φ) (lines.map (MvPolynomial.rename φ))
  | _, _, .nil, _, _ => .nil
  | _, _, .inputAx d hp, hx_b, hx_P => (d.rename φ hφ hbase hP hx_b hx_P).inputAx (hP _ hp)
  | _, _, .boolAx d hv, hx_b, hx_P =>
    ((d.rename φ hφ hbase hP hx_b hx_P).boolAx (hbase _ hv)).cast rfl (by simp)
  | _, _, .mulVar d hv hf, hx_b, hx_P =>
    ((d.rename φ hφ hbase hP hx_b hx_P).mulVar
      (hv.imp (hbase _) (fun he ↦ List.mem_map.mpr ⟨_, he, rfl⟩))
      (List.mem_map.mpr ⟨_, hf, rfl⟩)).cast rfl (by simp)
  | _, _, .linComb (a := a) (b := b) d hg hf, hx_b, hx_P =>
    ((d.rename φ hφ hbase hP hx_b hx_P).linComb (a := a) (b := b)
      (List.mem_map.mpr ⟨_, hg, rfl⟩) (List.mem_map.mpr ⟨_, hf, rfl⟩)).cast rfl (by simp)
  | _, _, .extAx (x := x) (f := f) d _ _ hx_fresh hf_vars, hx_b, hx_P =>
    ((d.rename φ hφ hbase hP (fun y hy ↦ hx_b y (List.mem_cons_of_mem _ hy))
        (fun y hy ↦ hx_P y (List.mem_cons_of_mem _ hy))).extAx (x := φ x)
      (f := MvPolynomial.rename φ f) (hx_b x List.mem_cons_self) (hx_P x List.mem_cons_self)
      (fun hmem ↦ by
        rcases List.mem_map.mp hmem with ⟨y, hy, hy_eq⟩
        obtain rfl := hφ hy_eq
        exact hx_fresh hy)
      (fun w hw ↦ by
        rcases MvPolynomial.mem_vars_rename φ f hw with ⟨u, hu, rfl⟩
        exact (hf_vars u hu).imp (hbase u) (fun he ↦ List.mem_map.mpr ⟨u, he, rfl⟩))).cast
      rfl (by simp)

/-- Degree preservation under `EPCDeriv.rename`. -/
theorem EPCDeriv.hasMaxDegree_rename {W : Type*} [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hφ : Function.Injective φ) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') {exts lines} {d : EPCDeriv baseVars P exts lines}
    (hxb : ∀ x ∈ exts, φ x ∉ baseVars') (hxP : ∀ x ∈ exts, ∀ p' ∈ P', φ x ∉ p'.vars)
    {k : ℕ} (hd : d.HasMaxDegree k) : (d.rename φ hφ hbase hP hxb hxP).HasMaxDegree k :=
  LinesMaxDegree.map_rename hd φ

/-- Size preservation under injective `EPCDeriv.rename`. -/
theorem EPCDeriv.size_rename {W : Type*} [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hφ : Function.Injective φ) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') {exts lines} (d : EPCDeriv baseVars P exts lines)
    (hxb : ∀ x ∈ exts, φ x ∉ baseVars') (hxP : ∀ x ∈ exts, ∀ p' ∈ P', φ x ∉ p'.vars) :
    (d.rename φ hφ hbase hP hxb hxP).size = d.size :=
  derivLinesSize_map_rename_of_injective hφ lines

/-- Bit-complexity preservation under injective `EPCDeriv.rename`. -/
theorem EPCDeriv.bitComplexity_rename {W : Type*} {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W ℚ)} (φ : V → W) (hφ : Function.Injective φ)
    (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars') (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P')
    {exts lines} (d : EPCDeriv baseVars P exts lines) (hxb : ∀ x ∈ exts, φ x ∉ baseVars')
    (hxP : ∀ x ∈ exts, ∀ p' ∈ P', φ x ∉ p'.vars) :
    (d.rename φ hφ hbase hP hxb hxP).bitComplexity = d.bitComplexity :=
  derivLinesBitComplexity_map_rename_of_injective hφ lines

/-- Preservation of `numExtVars` under `EPCDeriv.rename`. -/
@[simp]
theorem EPCDeriv.numExtVars_rename {W : Type*} [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hφ : Function.Injective φ) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P') {exts lines} (d : EPCDeriv baseVars P exts lines)
    (hxb : ∀ x ∈ exts, φ x ∉ baseVars') (hxP : ∀ x ∈ exts, ∀ p' ∈ P', φ x ∉ p'.vars) :
    (d.rename φ hφ hbase hP hxb hxP).numExtVars = d.numExtVars :=
  List.length_map _

/-- Transfer of any renaming-invariant extension-axiom predicate across `EPCDeriv.rename`. -/
theorem EPCDeriv.extAxiomsSatisfy_rename {W : Type*} [CommRing R]
    {Φ : Set V → MvPolynomial V R → Prop} {Ψ : Set W → MvPolynomial W R → Prop}
    {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {baseVars' : Set W} {P' : Set (MvPolynomial W R)}
    (φ : V → W) (hφ : Function.Injective φ) (hbase : ∀ v ∈ baseVars, φ v ∈ baseVars')
    (hP : ∀ p ∈ P, MvPolynomial.rename φ p ∈ P')
    (hΦΨ : ∀ (A : Set V) (B : Set W), (∀ v ∈ A, φ v ∈ B) →
      ∀ f, Φ A f → Ψ B (MvPolynomial.rename φ f)) :
    ∀ {exts lines} (d : EPCDeriv baseVars P exts lines)
      (hxb : ∀ x ∈ exts, φ x ∉ baseVars') (hxP : ∀ x ∈ exts, ∀ p' ∈ P', φ x ∉ p'.vars),
      d.ExtAxiomsSatisfy Φ → (d.rename φ hφ hbase hP hxb hxP).ExtAxiomsSatisfy Ψ
  | _, _, .nil, _, _, _ => trivial
  | _, _, .inputAx d _, hxb, hxP, hd =>
    d.extAxiomsSatisfy_rename φ hφ hbase hP hΦΨ hxb hxP hd
  | _, _, .boolAx d _, hxb, hxP, hd => by
    simp only [EPCDeriv.rename, EPCDeriv.extAxiomsSatisfy_cast, EPCDeriv.extAxiomsSatisfy_boolAx]
    exact d.extAxiomsSatisfy_rename φ hφ hbase hP hΦΨ hxb hxP hd
  | _, _, .mulVar d _ _, hxb, hxP, hd => by
    simp only [EPCDeriv.rename, EPCDeriv.extAxiomsSatisfy_cast, EPCDeriv.extAxiomsSatisfy_mulVar]
    exact d.extAxiomsSatisfy_rename φ hφ hbase hP hΦΨ hxb hxP hd
  | _, _, .linComb d _ _, hxb, hxP, hd => by
    simp only [EPCDeriv.rename, EPCDeriv.extAxiomsSatisfy_cast, EPCDeriv.extAxiomsSatisfy_linComb]
    exact d.extAxiomsSatisfy_rename φ hφ hbase hP hΦΨ hxb hxP hd
  | _, _, .extAx d _ _ _ _, hxb, hxP, hd => by
    rw [EPCDeriv.extAxiomsSatisfy_extAx] at hd
    simp only [EPCDeriv.rename, EPCDeriv.extAxiomsSatisfy_cast, EPCDeriv.extAxiomsSatisfy_extAx]
    refine ⟨hΦΨ _ _ ?_ _ hd.1, d.extAxiomsSatisfy_rename φ hφ hbase hP hΦΨ
      (fun y hy ↦ hxb y (.tail _ hy)) (fun y hy ↦ hxP y (.tail _ hy)) hd.2⟩
    rintro v (hb | he)
    exacts [Or.inl (hbase v hb), Or.inr (List.mem_map.mpr ⟨v, he, rfl⟩)]

/-- Compose two `PCDeriv` derivations `d₁` (`P ⊢ Q`) and `d₂` (`Q ⊢ lines₂`). -/
noncomputable def PCDeriv.append [CommRing R] {baseVars : Set V} {P Q : Set (MvPolynomial V R)}
    {lines₁ : List (MvPolynomial V R)} (d₁ : PCDeriv baseVars P lines₁) (hQ : ∀ q ∈ Q, q ∈ lines₁) :
    ∀ {lines₂}, PCDeriv baseVars Q lines₂ → PCDeriv baseVars P (lines₂ ++ lines₁)
  | _, .nil => d₁
  | _, .inputAx (p := q) d₂ hq =>
    have hmem : q ∈ _ := List.mem_append.mpr (Or.inr (hQ q hq))
    ((d₁.append hQ d₂).linComb (a := (1 : R)) (b := 0) hmem hmem).cast (by simp)
  | _, .boolAx d₂ hv => (d₁.append hQ d₂).boolAx hv
  | _, .mulVar d₂ hv hf => (d₁.append hQ d₂).mulVar hv (List.mem_append.mpr (Or.inl hf))
  | _, .linComb (a := a) (b := b) d₂ hg hf =>
    (d₁.append hQ d₂).linComb (a := a) (b := b)
      (List.mem_append.mpr (Or.inl hg)) (List.mem_append.mpr (Or.inl hf))

/-- Compose two `EPCDeriv` derivations `d₁` (`P ⊢ Q`) and `d₂` (`Q ⊢ lines₂`) over an expanded
active base variable set `baseVars ∪ exts₁`, when `d₂`'s extension variables are fresh with
respect to `baseVars`, `exts₁`, and `P`, and `d₂` uses no Boolean axioms on `exts₁`. -/
noncomputable def EPCDeriv.append [CommRing R] {baseVars : Set V} {P Q : Set (MvPolynomial V R)}
    {exts₁ : List V} {lines₁ : List (MvPolynomial V R)} (d₁ : EPCDeriv baseVars P exts₁ lines₁)
    (hQ : ∀ q ∈ Q, q ∈ lines₁) : ∀ {exts₂ lines₂}, EPCDeriv baseVars Q exts₂ lines₂ →
      (∀ x ∈ exts₂, x ∉ exts₁) → (∀ x ∈ exts₂, ∀ p ∈ P, x ∉ p.vars) →
      EPCDeriv baseVars P (exts₂ ++ exts₁) (lines₂ ++ lines₁)
  | _, _, .nil, _, _ => d₁
  | _, _, .inputAx (p := q) d₂ hq, hexts, hP =>
    have hmem : q ∈ _ := List.mem_append.mpr (Or.inr (hQ q hq))
    ((d₁.append hQ d₂ hexts hP).linComb (a := (1 : R)) (b := 0) hmem hmem).cast rfl (by simp)
  | _, _, .boolAx d₂ hv, hexts, hP => (d₁.append hQ d₂ hexts hP).boolAx hv
  | _, _, .mulVar d₂ hv hf, hexts, hP =>
    (d₁.append hQ d₂ hexts hP).mulVar
      (hv.imp id fun he ↦ List.mem_append.mpr (Or.inl he)) (List.mem_append.mpr (Or.inl hf))
  | _, _, .linComb (a := a) (b := b) d₂ hg hf, hexts, hP =>
    (d₁.append hQ d₂ hexts hP).linComb (a := a) (b := b)
      (List.mem_append.mpr (Or.inl hg)) (List.mem_append.mpr (Or.inl hf))
  | _, _, .extAx d₂ hx_base _ hx_fresh hf_vars, hexts, hP =>
    (d₁.append hQ d₂ (fun y hy ↦ hexts y (.tail _ hy)) (fun y hy ↦ hP y (.tail _ hy))).extAx
      hx_base (hP _ List.mem_cons_self) (by simp [hx_fresh, hexts _ List.mem_cons_self])
      (fun v hv ↦ (hf_vars v hv).imp id fun he ↦ List.mem_append.mpr (Or.inl he))

/-- Degree bound for concatenated `EPCDeriv` derivations. -/
theorem EPCDeriv.hasMaxDegree_append [CommRing R] {baseVars : Set V} {P Q : Set (MvPolynomial V R)}
    {exts₁ lines₁ exts₂ lines₂} {d₁ : EPCDeriv baseVars P exts₁ lines₁} (hQ : ∀ q ∈ Q, q ∈ lines₁)
    {d₂ : EPCDeriv baseVars Q exts₂ lines₂} (hexts : ∀ x ∈ exts₂, x ∉ exts₁)
    (hP : ∀ x ∈ exts₂, ∀ p ∈ P, x ∉ p.vars) {k₁ k₂ : ℕ} (hk₁ : d₁.HasMaxDegree k₁)
    (hk₂ : d₂.HasMaxDegree k₂) : (d₁.append hQ d₂ hexts hP).HasMaxDegree (max k₁ k₂) := by
  rw [EPCDeriv.HasMaxDegree, linesMaxDegree_append]
  exact ⟨hk₂.mono (le_max_right _ _), hk₁.mono (le_max_left _ _)⟩

@[simp]
theorem EPCDeriv.size_append [CommRing R] {baseVars : Set V} {P Q : Set (MvPolynomial V R)}
    {exts₁ lines₁ exts₂ lines₂} (d₁ : EPCDeriv baseVars P exts₁ lines₁) (hQ : ∀ q ∈ Q, q ∈ lines₁)
    (d₂ : EPCDeriv baseVars Q exts₂ lines₂) (hexts : ∀ x ∈ exts₂, x ∉ exts₁)
    (hP : ∀ x ∈ exts₂, ∀ p ∈ P, x ∉ p.vars) :
    (d₁.append hQ d₂ hexts hP).size = d₂.size + d₁.size :=
  derivLinesSize_append lines₂ lines₁

@[simp]
theorem EPCDeriv.bitComplexity_append {baseVars : Set V} {P Q : Set (MvPolynomial V ℚ)}
    {exts₁ lines₁ exts₂ lines₂} (d₁ : EPCDeriv baseVars P exts₁ lines₁) (hQ : ∀ q ∈ Q, q ∈ lines₁)
    (d₂ : EPCDeriv baseVars Q exts₂ lines₂) (hexts : ∀ x ∈ exts₂, x ∉ exts₁)
    (hP : ∀ x ∈ exts₂, ∀ p ∈ P, x ∉ p.vars) :
    (d₁.append hQ d₂ hexts hP).bitComplexity = max d₂.bitComplexity d₁.bitComplexity :=
  derivLinesBitComplexity_append lines₂ lines₁

@[simp]
theorem EPCDeriv.numExtVars_append [CommRing R] {baseVars : Set V}
    {P Q : Set (MvPolynomial V R)} {exts₁ lines₁ exts₂ lines₂}
    (d₁ : EPCDeriv baseVars P exts₁ lines₁) (hQ : ∀ q ∈ Q, q ∈ lines₁)
    (d₂ : EPCDeriv baseVars Q exts₂ lines₂) (hexts : ∀ x ∈ exts₂, x ∉ exts₁)
    (hP : ∀ x ∈ exts₂, ∀ p ∈ P, x ∉ p.vars) :
    (d₁.append hQ d₂ hexts hP).numExtVars = d₂.numExtVars + d₁.numExtVars :=
  List.length_append

/-- Preservation of any monotone extension-axiom predicate across `EPCDeriv.append`. -/
theorem EPCDeriv.extAxiomsSatisfy_append [CommRing R]
    {Φ : Set V → MvPolynomial V R → Prop}
    (hmono : ∀ {A B : Set V}, A ⊆ B → ∀ {f}, Φ A f → Φ B f)
    {baseVars : Set V} {P Q : Set (MvPolynomial V R)}
    {exts₁ lines₁} (d₁ : EPCDeriv baseVars P exts₁ lines₁) (hQ : ∀ q ∈ Q, q ∈ lines₁) :
    ∀ {exts₂ lines₂} (d₂ : EPCDeriv baseVars Q exts₂ lines₂) (hexts : ∀ x ∈ exts₂, x ∉ exts₁)
      (hP : ∀ x ∈ exts₂, ∀ p ∈ P, x ∉ p.vars), d₁.ExtAxiomsSatisfy Φ →
      d₂.ExtAxiomsSatisfy Φ → (d₁.append hQ d₂ hexts hP).ExtAxiomsSatisfy Φ
  | _, _, .nil, _, _, h1, _ => h1
  | _, _, .inputAx d₂ _, hexts, hP, h1, h2 => by
    simp only [EPCDeriv.append, EPCDeriv.extAxiomsSatisfy_cast, EPCDeriv.extAxiomsSatisfy_linComb]
    exact d₁.extAxiomsSatisfy_append hmono hQ d₂ hexts hP h1 h2
  | _, _, .boolAx d₂ _, hexts, hP, h1, h2 =>
    d₁.extAxiomsSatisfy_append hmono hQ d₂ hexts hP h1 h2
  | _, _, .mulVar d₂ _ _, hexts, hP, h1, h2 =>
    d₁.extAxiomsSatisfy_append hmono hQ d₂ hexts hP h1 h2
  | _, _, .linComb d₂ _ _, hexts, hP, h1, h2 =>
    d₁.extAxiomsSatisfy_append hmono hQ d₂ hexts hP h1 h2
  | _, _, .extAx d₂ _ _ _ _, hexts, hP, h1, h2 => by
    rw [EPCDeriv.extAxiomsSatisfy_extAx] at h2
    rw [EPCDeriv.append, EPCDeriv.extAxiomsSatisfy_extAx]
    refine ⟨hmono ?_ h2.1, d₁.extAxiomsSatisfy_append hmono hQ d₂
      (fun y hy ↦ hexts y (.tail _ hy)) (fun y hy ↦ hP y (.tail _ hy)) h1 h2.2⟩
    rintro v (hb | he)
    exacts [Or.inl hb, Or.inr (List.mem_append.mpr (Or.inl he))]

/-- Derived addition step `g + f` in `EPCDeriv`. -/
noncomputable def EPCDeriv.add [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {exts lines} (d : EPCDeriv baseVars P exts lines) {g f : MvPolynomial V R}
    (hg : g ∈ lines) (hf : f ∈ lines) : EPCDeriv baseVars P exts ((g + f) :: lines) :=
  (d.linComb (a := (1 : R)) (b := 1) hg hf).cast rfl (by simp)

/-- Derived subtraction step `g - f` in `EPCDeriv`. -/
noncomputable def EPCDeriv.sub [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {exts lines} (d : EPCDeriv baseVars P exts lines) {g f : MvPolynomial V R}
    (hg : g ∈ lines) (hf : f ∈ lines) : EPCDeriv baseVars P exts ((g - f) :: lines) :=
  (d.linComb (a := (1 : R)) (b := (-1 : R)) hg hf).cast rfl (by simp [sub_eq_add_neg])

/-- Derived scalar-multiplication step `c • f` in `EPCDeriv`. -/
noncomputable def EPCDeriv.smul [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {exts lines} (d : EPCDeriv baseVars P exts lines) (c : R) {f : MvPolynomial V R}
    (hf : f ∈ lines) : EPCDeriv baseVars P exts ((c • f) :: lines) :=
  (d.linComb (a := c) (b := 0) hf hf).cast rfl (by simp)

/-- Derive a rational linear combination `∑ i ∈ u, ((a i : ℚ) / (b : ℚ)) • g i` from prior lines
with common denominator `d₀`, keeping intermediate coefficient bit-complexity logarithmic (no
compounding across summands). -/
theorem EPCDeriv.exists_deriveIntScaledSum {baseVars : Set V} {P : Set (MvPolynomial V ℚ)}
    {Φ : Set V → MvPolynomial V ℚ → Prop} {exts lines} (d : EPCDeriv baseVars P exts lines)
    (hΦ : d.ExtAxiomsSatisfy Φ) {k : ℕ} (hk : d.HasMaxDegree k)
    {ι : Type*} (u : Finset ι) {A M b d₀ : ℕ} (hb : 1 ≤ b) (hd₀ : 1 ≤ d₀)
    (a : ι → ℤ) (ha : ∀ i ∈ u, (a i).natAbs ≤ A)
    (g : ι → MvPolynomial V ℚ) (hmem : ∀ i ∈ u, g i ∈ lines)
    (hcoeff : ∀ i ∈ u, HasBoundedIntCoeffs (g i) M d₀)
    (hne : u.Nonempty ∨ lines ≠ []) :
    ∃ (lines' : List (MvPolynomial V ℚ)) (d' : EPCDeriv baseVars P exts lines'),
      (∑ i ∈ u, ((a i : ℚ) / (b : ℚ)) • g i) ∈ lines' ∧
      (∀ q ∈ lines, q ∈ lines') ∧
      d'.HasMaxDegree k ∧ d'.ExtAxiomsSatisfy Φ ∧
      d'.size ≤ d.size + u.card * ∑ i ∈ u, polyMonomialCount (g i) ∧
      d'.bitComplexity ≤
        max d.bitComplexity (Nat.size (u.card * (A * M)) + Nat.size (b * d₀)) := by
  classical
  have hterm : ∀ i ∈ u, HasBoundedIntCoeffs (((a i : ℚ) / (b : ℚ)) • g i) (A * M) (b * d₀) :=
    fun i hi ↦ by
      have h1 := (hcoeff i hi).div_smul (a i) hb
      exact ⟨h1.1, fun m ↦ let ⟨z, hz, hc⟩ := h1.2 m
        ⟨z, hz.trans (Nat.mul_le_mul_right M (ha i hi)), hc⟩⟩
  have hpart : ∀ {v : Finset ι}, v ⊆ u →
      polyBitComplexity (∑ i ∈ v, ((a i : ℚ) / (b : ℚ)) • g i) ≤
        Nat.size (u.card * (A * M)) + Nat.size (b * d₀) := fun {v} hv ↦ by
    have hsum := HasBoundedIntCoeffs.finset_sum v (fun i ↦ ((a i : ℚ) / (b : ℚ)) • g i)
      (Nat.mul_pos hb hd₀) (fun i hi ↦ hterm i (hv hi))
    exact hsum.polyBitComplexity_le.trans (Nat.add_le_add_right
      (Nat.size_le_size (Nat.mul_le_mul_right _ (Finset.card_le_card hv))) _)
  have hnonempty : ∀ {v : Finset ι}, v ⊆ u → v.Nonempty →
      ∃ (lines' : List (MvPolynomial V ℚ)) (d' : EPCDeriv baseVars P exts lines'),
        (∑ i ∈ v, ((a i : ℚ) / (b : ℚ)) • g i) ∈ lines' ∧
        (∀ q ∈ lines, q ∈ lines') ∧
        d'.HasMaxDegree k ∧ d'.ExtAxiomsSatisfy Φ ∧
        d'.size ≤ d.size + v.card * ∑ i ∈ v, polyMonomialCount (g i) ∧
        d'.bitComplexity ≤
          max d.bitComplexity (Nat.size (u.card * (A * M)) + Nat.size (b * d₀)) := by
    intro v
    induction v using Finset.induction_on with
    | empty => intro _ h; simp at h
    | @insert i v₀ hi ih =>
      intro hv _
      have hi_u : i ∈ u := hv (Finset.mem_insert_self i v₀)
      by_cases hv₀ : v₀.Nonempty
      · rcases ih ((Finset.subset_insert i v₀).trans hv) hv₀ with
          ⟨l₁, d₁, hsum₁, hsub₁, hk₁, hΦ₁, hsz₁, hbit₁⟩
        have hgi : g i ∈ l₁ := hsub₁ _ (hmem i hi_u)
        let d₂ := d₁.linComb (a := (a i : ℚ) / (b : ℚ)) (b := (1 : ℚ)) hgi hsum₁
        have heq : ((a i : ℚ) / (b : ℚ)) • g i + (1 : ℚ) •
            ∑ j ∈ v₀, ((a j : ℚ) / (b : ℚ)) • g j =
            ∑ j ∈ insert i v₀, ((a j : ℚ) / (b : ℚ)) • g j := by
          rw [one_smul, Finset.sum_insert hi]
        refine ⟨_, d₂, heq ▸ List.mem_cons_self, fun q hq ↦ .tail _ (hsub₁ q hq), ?_, hΦ₁, ?_, ?_⟩
        · rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
          exact ⟨(totalDegree_add _ _).trans (max_le
            ((totalDegree_smul_le _ _).trans (hk _ (hmem i hi_u)))
            ((totalDegree_smul_le _ _).trans (hk₁ _ hsum₁))), hk₁⟩
        · have hcnt : polyMonomialCount (∑ j ∈ insert i v₀, ((a j : ℚ) / (b : ℚ)) • g j) ≤
              ∑ j ∈ insert i v₀, polyMonomialCount (g j) :=
            (polyMonomialCount_sum_le _ _).trans
              (Finset.sum_le_sum fun j _ ↦ polyMonomialCount_smul_le _ _)
          have hsum_le : ∑ j ∈ v₀, polyMonomialCount (g j) ≤
              ∑ j ∈ insert i v₀, polyMonomialCount (g j) := by
            rw [Finset.sum_insert hi]; omega
          have hmul := Nat.mul_le_mul_left v₀.card hsum_le
          simp only [EPCDeriv.size, derivLinesSize_cons, heq] at hsz₁ ⊢
          rw [Finset.card_insert_of_notMem hi, Nat.succ_mul]
          omega
        · simp only [EPCDeriv.bitComplexity, derivLinesBitComplexity_cons, heq]
          exact max_le (le_max_of_le_right (hpart hv)) hbit₁
      · rw [Finset.not_nonempty_iff_eq_empty] at hv₀
        subst hv₀
        have hgi := hmem i hi_u
        let d₁ := d.smul ((a i : ℚ) / (b : ℚ)) hgi
        have heq : ((a i : ℚ) / (b : ℚ)) • g i =
            ∑ j ∈ ({i} : Finset ι), ((a j : ℚ) / (b : ℚ)) • g j := by simp
        refine ⟨_, d₁, heq ▸ List.mem_cons_self, fun q hq ↦ .tail _ hq, ?_, ?_, ?_, ?_⟩
        · rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
          exact ⟨(totalDegree_smul_le _ _).trans (hk _ hgi), hk⟩
        · simpa [d₁, EPCDeriv.smul] using hΦ
        · have hsml := polyMonomialCount_smul_le ((a i : ℚ) / (b : ℚ)) (g i)
          have hsz_d₁ : d₁.size = polyMonomialCount (((a i : ℚ) / (b : ℚ)) • g i) + d.size := by
            simp [EPCDeriv.size]
          have hcard1 : (insert i (∅ : Finset ι)).card = 1 := by simp
          have hsum1 : ∑ j ∈ insert i (∅ : Finset ι), polyMonomialCount (g j) =
              polyMonomialCount (g i) := by simp
          rw [hsz_d₁, hcard1, hsum1, one_mul]
          omega
        · simp only [EPCDeriv.bitComplexity, derivLinesBitComplexity_cons, heq]
          exact max_le (le_max_of_le_right (hpart hv)) (le_max_left _ _)
  by_cases hu : u.Nonempty
  · exact hnonempty Finset.Subset.rfl hu
  · rw [Finset.not_nonempty_iff_eq_empty] at hu
    subst hu
    rcases hne with hbad | hne_l
    · simp at hbad
    · obtain ⟨h₀, hh₀⟩ := List.exists_mem_of_ne_nil lines hne_l
      let d' : EPCDeriv baseVars P exts ((0 : MvPolynomial V ℚ) :: lines) :=
        (d.linComb (a := (0 : ℚ)) (b := 0) hh₀ hh₀).cast rfl (by simp)
      refine ⟨_, d', by simp, fun q hq ↦ .tail _ hq, ?_, ?_, ?_, ?_⟩
      · rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
        exact ⟨by simp, hk⟩
      · simpa [d'] using hΦ
      · simp [EPCDeriv.size]
      · simp [EPCDeriv.bitComplexity]

/-- Derive a general finite linear combination `∑ i ∈ s, c i • g i` from lines in `d`, preserving
`exts`, degree bound `k`, and extension-axiom predicate `Φ`. -/
theorem EPCDeriv.exists_deriveFinsetSum [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {Φ : Set V → MvPolynomial V R → Prop}
    {exts lines} (d : EPCDeriv baseVars P exts lines) (hΦ : d.ExtAxiomsSatisfy Φ)
    {k : ℕ} (hk : d.HasMaxDegree k) {ι : Type*} (s : Finset ι) (c : ι → R)
    (g : ι → MvPolynomial V R) (hg : ∀ i ∈ s, g i ∈ lines) (hne : s.Nonempty ∨ lines ≠ []) :
    ∃ (lines' : List (MvPolynomial V R)) (d' : EPCDeriv baseVars P exts lines'),
      (∑ i ∈ s, c i • g i) ∈ lines' ∧ (∀ q ∈ lines, q ∈ lines') ∧
      d'.HasMaxDegree k ∧ d'.ExtAxiomsSatisfy Φ ∧
      d'.size ≤ d.size + s.card * ∑ i ∈ s, polyMonomialCount (g i) := by
  classical
  have hne_case : ∀ (t : Finset ι), t.Nonempty → (∀ i ∈ t, g i ∈ lines) →
      ∃ (lines' : List (MvPolynomial V R)) (d' : EPCDeriv baseVars P exts lines'),
        (∑ i ∈ t, c i • g i) ∈ lines' ∧ (∀ q ∈ lines, q ∈ lines') ∧
        d'.HasMaxDegree k ∧ d'.ExtAxiomsSatisfy Φ ∧
        d'.size ≤ d.size + t.card * ∑ i ∈ t, polyMonomialCount (g i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro h; simp at h
    | @insert i s' hi ih =>
      intro _ hgt
      by_cases hs' : s'.Nonempty
      · rcases ih hs' (fun j hj ↦ hgt j (Finset.mem_insert_of_mem hj)) with
          ⟨l₁, d₁, hsum₁, hsub₁, hk₁, hΦ₁, hsz₁⟩
        have hgi := hsub₁ _ (hgt i (Finset.mem_insert_self i s'))
        let d₂ := d₁.linComb (a := c i) (b := (1 : R)) hgi hsum₁
        refine ⟨_, d₂, by simp [Finset.sum_insert hi], fun q hq ↦ .tail _ (hsub₁ q hq),
          ?_, hΦ₁, ?_⟩
        · rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
          exact ⟨(totalDegree_add _ _).trans (max_le
            ((totalDegree_smul_le _ _).trans (hk _ (hgt i (Finset.mem_insert_self i s'))))
            ((totalDegree_smul_le _ _).trans (hk₁ _ hsum₁))), hk₁⟩
        · have hcnt : polyMonomialCount (c i • g i + (1 : R) • ∑ j ∈ s', c j • g j) ≤
              ∑ j ∈ insert i s', polyMonomialCount (g j) := by
            rw [one_smul, Finset.sum_insert hi]
            exact (polyMonomialCount_add_le _ _).trans (Nat.add_le_add
              (polyMonomialCount_smul_le _ _) ((polyMonomialCount_sum_le s' _).trans
                (Finset.sum_le_sum fun j _ ↦ polyMonomialCount_smul_le _ _)))
          have hsum_le : ∑ j ∈ s', polyMonomialCount (g j) ≤
              ∑ j ∈ insert i s', polyMonomialCount (g j) := by
            rw [Finset.sum_insert hi]; omega
          have hmul := Nat.mul_le_mul_left s'.card hsum_le
          simp only [EPCDeriv.size, derivLinesSize_cons] at hsz₁ ⊢
          rw [Finset.card_insert_of_notMem hi, Nat.succ_mul]
          omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hs'
        subst hs'
        have hgi := hgt i (Finset.mem_insert_self i ∅)
        refine ⟨_, d.smul (c i) hgi, by simp, fun q hq ↦ .tail _ hq, ?_,
          by simpa [EPCDeriv.smul] using hΦ, ?_⟩
        · rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
          exact ⟨(totalDegree_smul_le _ _).trans (hk _ hgi), hk⟩
        · have hsml := polyMonomialCount_smul_le (c i) (g i)
          have hsz_s : (d.smul (c i) hgi).size = polyMonomialCount (c i • g i) + d.size := by
            simp [EPCDeriv.size]
          have hcard1 : (insert i (∅ : Finset ι)).card = 1 := by simp
          have hsum1 : ∑ j ∈ insert i (∅ : Finset ι), polyMonomialCount (g j) =
              polyMonomialCount (g i) := by simp
          rw [hsz_s, hcard1, hsum1, one_mul]
          omega
  by_cases hs : s.Nonempty
  · exact hne_case s hs hg
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    rcases hne with hbad | hne_l
    · simp at hbad
    · obtain ⟨h₀, hh₀⟩ := List.exists_mem_of_ne_nil lines hne_l
      let d' : EPCDeriv baseVars P exts ((0 : MvPolynomial V R) :: lines) :=
        (d.linComb (a := (0 : R)) (b := 0) hh₀ hh₀).cast rfl (by simp)
      refine ⟨_, d', List.mem_cons_self, fun q hq ↦ .tail _ hq, ?_, by simpa [d'] using hΦ,
        by simp [EPCDeriv.size]⟩
      rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
      exact ⟨by simp, hk⟩

/-- Derive `(∑ i ∈ s, ((a i : ℚ) / (b : ℚ)) • X (v i)) * f` from `f ∈ lines`, raising max degree
only to `max k (f.totalDegree + 1)`, with explicit polynomial size and logarithmic bit-complexity
bounds. -/
theorem EPCDeriv.exists_deriveLinearFormMul {baseVars : Set V}
    {P : Set (MvPolynomial V ℚ)} {Φ : Set V → MvPolynomial V ℚ → Prop}
    {exts lines} (d : EPCDeriv baseVars P exts lines) (hΦ : d.ExtAxiomsSatisfy Φ)
    {k : ℕ} (hk : d.HasMaxDegree k) {f : MvPolynomial V ℚ} (hf : f ∈ lines)
    {A M b d₀ : ℕ} (hb : 1 ≤ b) (hfc : HasBoundedIntCoeffs f M d₀)
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (ha : ∀ i ∈ s, (a i).natAbs ≤ A) (v : ι → V)
    (hv : ∀ i ∈ s, v i ∈ baseVars ∨ v i ∈ exts) :
    ∃ (lines' : List (MvPolynomial V ℚ)) (d' : EPCDeriv baseVars P exts lines'),
      (∑ i ∈ s, ((a i : ℚ) / (b : ℚ)) • X (v i)) * f ∈ lines' ∧
      (∀ q ∈ lines, q ∈ lines') ∧
      d'.HasMaxDegree (max k (f.totalDegree + 1)) ∧ d'.ExtAxiomsSatisfy Φ ∧
      d'.size ≤ d.size + (s.card + s.card ^ 2) * polyMonomialCount f ∧
      d'.bitComplexity ≤
        max d.bitComplexity (Nat.size (s.card * (A * M)) + Nat.size (b * d₀)) := by
  classical
  have hfb : polyBitComplexity f ≤ d.bitComplexity :=
    derivLinesBitComplexity_le_iff.mp le_rfl f hf
  have hmul : ∀ t : Finset ι, (∀ i ∈ t, v i ∈ baseVars ∨ v i ∈ exts) →
      ∃ (l₁ : List (MvPolynomial V ℚ)) (d₁ : EPCDeriv baseVars P exts l₁),
        (∀ i ∈ t, X (v i) * f ∈ l₁) ∧ (∀ q ∈ lines, q ∈ l₁) ∧
        d₁.HasMaxDegree (max k (f.totalDegree + 1)) ∧ d₁.ExtAxiomsSatisfy Φ ∧
        d₁.size ≤ d.size + t.card * polyMonomialCount f ∧
        d₁.bitComplexity ≤ d.bitComplexity := by
    intro t ht
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨lines, d, by simp, fun _ h ↦ h, hk.mono (le_max_left _ _), hΦ, by simp, le_rfl⟩
    | @insert i t' hi ih =>
      rcases ih (fun j hj ↦ ht j (Finset.mem_insert_of_mem hj)) with
        ⟨l₁, d₁, hmem₁, hsub₁, hk₁, hΦ₁, hsz₁, hbit₁⟩
      refine ⟨_, d₁.mulVar (ht i (Finset.mem_insert_self i t')) (hsub₁ f hf), ?_,
        fun q hq ↦ .tail _ (hsub₁ q hq), ?_, hΦ₁, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj'
        exacts [List.mem_cons_self, .tail _ (hmem₁ j hj')]
      · rw [EPCDeriv.HasMaxDegree, linesMaxDegree_cons]
        refine ⟨(totalDegree_mul _ _).trans ?_, hk₁⟩
        have hXv := totalDegree_X_le (R := ℚ) (v i)
        omega
      · simp only [EPCDeriv.size, derivLinesSize_cons, polyMonomialCount_X_mul,
          Finset.card_insert_of_notMem hi, Nat.succ_mul] at hsz₁ ⊢
        omega
      · simp only [EPCDeriv.bitComplexity, derivLinesBitComplexity_cons, polyBitComplexity_X_mul]
        exact max_le hfb hbit₁
  rcases hmul s hv with ⟨l₁, d₁, hmem₁, hsub₁, hk₁, hΦ₁, hsz₁, hbit₁⟩
  rcases d₁.exists_deriveIntScaledSum hΦ₁ hk₁ s hb hfc.1 a ha (fun i ↦ X (v i) * f) hmem₁
      (fun i _ ↦ hfc.X_mul (v i)) (Or.inr (List.ne_nil_of_mem (hsub₁ f hf))) with
    ⟨l₂, d₂, hsum₂, hsub₂, hk₂, hΦ₂, hsz₂, hbit₂⟩
  refine ⟨l₂, d₂, ?_, fun q hq ↦ hsub₂ q (hsub₁ q hq), hk₂, hΦ₂, ?_, ?_⟩
  · simpa [Finset.sum_mul, smul_mul_assoc] using hsum₂
  · simp only [polyMonomialCount_X_mul, Finset.sum_const, smul_eq_mul] at hsz₂
    rw [add_mul, sq, mul_assoc]
    omega
  · exact hbit₂.trans (max_le_max hbit₁ le_rfl)

end StructuralOps

/-! ### Derivability Predicates, Bridge to `Cslib.Logic.PL.PC`, and Boolean Soundness -/

section Soundness

variable {V : Type u} {R : Type v}

/-- Existence of a degree-`k` $\mathrm{EPC}$ derivation of `p` from `P` over `baseVars`. -/
@[expose] def EPCDerives [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R))
    (k : ℕ) (p : MvPolynomial V R) : Prop :=
  ∃ (exts : List V) (lines : List (MvPolynomial V R))
    (d : EPCDeriv baseVars P exts lines), p ∈ lines ∧ d.HasMaxDegree k

/-- Existence of a degree-`k` $\mathrm{PC}$ derivation of `p` from `P` over `baseVars`. -/
@[expose] def PCDerives [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R))
    (k : ℕ) (p : MvPolynomial V R) : Prop :=
  ∃ (lines : List (MvPolynomial V R)) (d : PCDeriv baseVars P lines), p ∈ lines ∧ d.HasMaxDegree k

/-- Existence of a degree-`k` $\mathrm{MC}$ derivation of `p` from `P` over `baseVars`. -/
@[expose] def MCDerives [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R))
    (k : ℕ) (p : MvPolynomial V R) : Prop :=
  ∃ (lines : List (MvPolynomial V R)) (d : MCDeriv baseVars P lines), p ∈ lines ∧ d.HasMaxDegree k

/-- Existence of a degree-`k` $\mathrm{EPC}$ refutation (derivation of `1`) of `P`. -/
@[expose] def EPCRefutes [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R)) (k : ℕ)
  : Prop :=
  EPCDerives baseVars P k 1

/-- Existence of a degree-`k` $\mathrm{PC}$ refutation (derivation of `1`) of `P`. -/
@[expose] def PCRefutes [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R)) (k : ℕ)
  : Prop :=
  PCDerives baseVars P k 1

/-- Existence of a degree-`k` $\mathrm{MC}$ refutation (derivation of `1`) of `P`. -/
@[expose] def MCRefutes [CommRing R] (baseVars : Set V) (P : Set (MvPolynomial V R)) (k : ℕ)
  : Prop :=
  MCDerives baseVars P k 1

/-- Every degree-`k` $\mathrm{MC}$ derivation yields a degree-`k` $\mathrm{PC}$ derivation. -/
theorem MCDerives.toPCDerives [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {k : ℕ} {p : MvPolynomial V R} (h : MCDerives baseVars P k p) :
    PCDerives baseVars P k p := by
  rcases h with ⟨lines, d, hmem, hdeg⟩
  exact ⟨lines, d.toPCDeriv, hmem, hdeg⟩

/-- Every degree-`k` $\mathrm{PC}$ derivation yields a degree-`k` $\mathrm{EPC}$ derivation. -/
theorem PCDerives.toEPCDerives [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {k : ℕ} {p : MvPolynomial V R} (h : PCDerives baseVars P k p) :
    EPCDerives baseVars P k p := by
  rcases h with ⟨lines, d, hmem, hdeg⟩
  exact ⟨[], lines, d.toEPCDeriv, hmem, hdeg⟩

/-- Monotonicity of `PCRefutes` in the degree bound. -/
theorem PCRefutes.mono [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {k₁ k₂ : ℕ} (h : PCRefutes baseVars P k₁) (hle : k₁ ≤ k₂) :
    PCRefutes baseVars P k₂ := by
  rcases h with ⟨lines, d, h1, hdeg⟩
  exact ⟨lines, d, h1, hdeg.mono hle⟩

/-- Monotonicity of `MCRefutes` in the degree bound. -/
theorem MCRefutes.mono [CommRing R] {baseVars : Set V} {P : Set (MvPolynomial V R)}
    {k₁ k₂ : ℕ} (h : MCRefutes baseVars P k₁) (hle : k₁ ≤ k₂) :
    MCRefutes baseVars P k₂ := by
  rcases h with ⟨lines, d, h1, hdeg⟩
  exact ⟨lines, d, h1, hdeg.mono hle⟩

/-- Convert a `PCDeriv` over finite variable set `V` into an upstream `Cslib.Logic.PL.PC.IsProof`
from `F ++ Cslib.Logic.PL.Algebraic.boolAxioms V R`. -/
theorem PCDeriv.toCslibIsProof [CommRing R] [Fintype V] {P : Set (MvPolynomial V R)}
    {F : List (MvPolynomial V R)} (hPF : ∀ p ∈ P, p ∈ F) {lines : List (MvPolynomial V R)}
    (d : PCDeriv Set.univ P lines) :
    Cslib.Logic.PL.PC.IsProof (F ++ Cslib.Logic.PL.Algebraic.boolAxioms V R) lines := by
  induction d with
  | nil => exact .nil
  | inputAx _ hp ih => exact ih.mem (List.mem_append_left _ (hPF _ hp))
  | @boolAx _ v _ _ ih =>
    exact ih.mem (List.mem_append_right _
      (Cslib.Logic.PL.Algebraic.mem_boolAxioms.mpr ⟨v, rfl⟩))
  | @mulVar _ v _ _ _ hf ih => exact ih.mulVar v hf
  | @linComb _ a b _ _ _ hg hf ih =>
    simpa only [smul_eq_C_mul] using ih.linear a b hg hf

/-- Convert an upstream `Cslib.Logic.PL.PC.IsProof` from `F ++ boolAxioms V R` back into a
`PCDeriv Set.univ P`. -/
theorem PCDeriv.exists_of_cslibIsProof [CommRing R] [Fintype V] {P : Set (MvPolynomial V R)}
    {F : List (MvPolynomial V R)} (hFP : ∀ p ∈ F, p ∈ P) {lines : List (MvPolynomial V R)}
    (h : Cslib.Logic.PL.PC.IsProof (F ++ Cslib.Logic.PL.Algebraic.boolAxioms V R) lines) :
    Nonempty (PCDeriv Set.univ P lines) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | mem _ hp ih =>
    rcases ih with ⟨d⟩
    rcases List.mem_append.mp hp with hpF | hpB
    · exact ⟨d.inputAx (hFP _ hpF)⟩
    · rcases Cslib.Logic.PL.Algebraic.mem_boolAxioms.mp hpB with ⟨v, rfl⟩
      exact ⟨d.boolAx trivial⟩
  | linear a b _ hp hq ih =>
    rcases ih with ⟨d⟩
    exact ⟨(d.linComb (a := a) (b := b) hp hq).cast (by simp [smul_eq_C_mul])⟩
  | mulVar v _ hp ih =>
    rcases ih with ⟨d⟩
    exact ⟨d.mulVar trivial hp⟩

/-- Exact equivalence between `PCRefutes Set.univ P k` on a finite variable type `V` and upstream
`Cslib.Logic.PL.PC.RefutableInDegree (F ++ boolAxioms V R) k` whenever `F` enumerates `P`. -/
theorem pcRefutes_iff_cslib_refutableInDegree [CommRing R] [Fintype V]
    {P : Set (MvPolynomial V R)} {F : List (MvPolynomial V R)}
    (hP : ∀ p, p ∈ P ↔ p ∈ F) (k : ℕ) :
    PCRefutes Set.univ P k ↔
      Cslib.Logic.PL.PC.RefutableInDegree
        (F ++ Cslib.Logic.PL.Algebraic.boolAxioms V R) k := by
  constructor
  · rintro ⟨lines, d, h1, hdeg⟩
    exact ⟨lines, d.toCslibIsProof (fun p hp ↦ (hP p).mp hp), h1,
      Cslib.Logic.PL.PC.degree_le_iff.mpr hdeg⟩
  · rintro ⟨lines, hls, h1, hdeg⟩
    obtain ⟨d⟩ := PCDeriv.exists_of_cslibIsProof (fun p hp ↦ (hP p).mpr hp) hls
    exact ⟨lines, d, h1, Cslib.Logic.PL.PC.degree_le_iff.mp hdeg⟩

/-- Any algebra homomorphism `Φ : MvPolynomial V R →ₐ[R] MvPolynomial W R` mapping `P` and Boolean
axioms into degree-`d'` `PC`-derivable polynomials over `W` and variables `X v` to degree-`≤ c`
polynomials maps any degree-`k` `PC` refutation of `P` to a degree-`max d' (c * k)` `PC` refutation
over `W`. -/
theorem cslib_refutableInDegree_of_algHom {W : Type*} [CommRing R] [Nontrivial R]
    {P : Set (MvPolynomial V R)} {G : List (MvPolynomial W R)}
    (Φ : MvPolynomial V R →ₐ[R] MvPolynomial W R) {c d' k : ℕ}
    (hX_deg : ∀ v : V, (Φ (X v)).totalDegree ≤ c)
    (hX_mul : ∀ (v : V) (q : MvPolynomial W R) (ls : List (MvPolynomial W R)),
      Cslib.Logic.PL.PC.IsProof G ls → q ∈ ls →
      ∃ ms, Cslib.Logic.PL.PC.IsProof G ms ∧ ls ⊆ ms ∧ Φ (X v) * q ∈ ms ∧
        Cslib.Logic.PL.PC.degree ms ≤ max (Cslib.Logic.PL.PC.degree ls) (q.totalDegree + c))
    (hP : ∀ p ∈ P, p.totalDegree ≤ k → ∃ ls, Cslib.Logic.PL.PC.IsProof G ls ∧ Φ p ∈ ls ∧
      Cslib.Logic.PL.PC.degree ls ≤ max d' (c * k))
    (hBool : ∀ v : V, 2 ≤ k → ∃ ls, Cslib.Logic.PL.PC.IsProof G ls ∧
      Φ (X v ^ 2 - X v) ∈ ls ∧ Cslib.Logic.PL.PC.degree ls ≤ max d' (c * k))
    (href : PCRefutes Set.univ P k) :
    Cslib.Logic.PL.PC.RefutableInDegree G (max d' (c * k)) := by
  rcases href with ⟨lines, d, h1, hdeg⟩
  have hdeg_map : ∀ p : MvPolynomial V R, (Φ p).totalDegree ≤ c * p.totalDegree := fun p ↦ by
    have heq : Φ p = aeval (fun v ↦ Φ (X v)) p := by
      induction p using MvPolynomial.induction_on with
      | C a => simp
      | add p₁ p₂ ih₁ ih₂ => simp [ih₁, ih₂]
      | mul_X p₁ v ih => simp [ih]
    conv_lhs => rw [heq, p.as_sum, map_sum]
    refine totalDegree_finsetSum_le fun m hm ↦ ?_
    rw [aeval_monomial, algebraMap_eq, ← smul_eq_C_mul]
    refine (totalDegree_smul_le _ _).trans ?_
    rw [Finsupp.prod]
    have hprod_deg : ∀ (s : Finset V) (g : V → MvPolynomial W R),
        (∏ v ∈ s, g v).totalDegree ≤ ∑ v ∈ s, (g v).totalDegree := fun s g ↦ by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)
    refine (hprod_deg m.support _).trans ?_
    calc
      ∑ v ∈ m.support, (Φ (X v) ^ m v).totalDegree
          ≤ ∑ v ∈ m.support, m v * c :=
            Finset.sum_le_sum fun v _ ↦
              (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hX_deg v))
      _ = c * ∑ v ∈ m.support, m v := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ ↦ Nat.mul_comm _ _
      _ ≤ c * p.totalDegree := Nat.mul_le_mul_left c (le_totalDegree hm)
  suffices ∀ {ls : List (MvPolynomial V R)}, PCDeriv Set.univ P ls → LinesMaxDegree ls k →
      ∃ ms : List (MvPolynomial W R), Cslib.Logic.PL.PC.IsProof G ms ∧
        (∀ q ∈ ls, Φ q ∈ ms) ∧ Cslib.Logic.PL.PC.degree ms ≤ max d' (c * k) by
    rcases this d hdeg with ⟨ms, hms, hmem, hmd⟩
    exact ⟨ms, hms, by simpa using hmem 1 h1, hmd⟩
  intro ls d₀ hls
  induction d₀ with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @inputAx ls₀ p _ hp ih =>
    have ⟨hp_deg, hls₀⟩ := (linesMaxDegree_cons p ls₀ k).mp hls
    rcases ih hls₀ with ⟨ms₀, hms₀, hmem₀, hmd₀⟩
    rcases hP p hp hp_deg with ⟨ms₁, hms₁, hp₁, hmd₁⟩
    refine ⟨ms₁ ++ ms₀, hms₁.append hms₀, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      exacts [List.mem_append_left _ hp₁, List.mem_append_right _ (hmem₀ q hq')]
    · rw [Cslib.Logic.PL.PC.degree_le_iff]
      exact List.forall_mem_append.mpr
        ⟨Cslib.Logic.PL.PC.degree_le_iff.mp hmd₁, Cslib.Logic.PL.PC.degree_le_iff.mp hmd₀⟩
  | @boolAx ls₀ v _ _ ih =>
    have ⟨hb_deg, hls₀⟩ := (linesMaxDegree_cons _ ls₀ k).mp hls
    rcases ih hls₀ with ⟨ms₀, hms₀, hmem₀, hmd₀⟩
    have hk2 : 2 ≤ k := by
      classical
      have hmem : Finsupp.single v 2 ∈ ((X v : MvPolynomial V R) ^ 2 - X v).support := by
        rw [mem_support_iff, coeff_sub, coeff_X_pow, ite_eq_left rfl, coeff_X,
          ite_eq_right (fun h ↦ by
            have := congrArg (fun f : V →₀ ℕ ↦ f v) h; simp at this), sub_zero]
        exact one_ne_zero
      have h2 : 2 ≤ ((X v : MvPolynomial V R) ^ 2 - X v).totalDegree := by
        simpa [Finsupp.sum_single_index] using le_totalDegree hmem
      exact h2.trans hb_deg
    rcases hBool v hk2 with ⟨ms₁, hms₁, hb₁, hmd₁⟩
    refine ⟨ms₁ ++ ms₀, hms₁.append hms₀, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      exacts [List.mem_append_left _ hb₁, List.mem_append_right _ (hmem₀ q hq')]
    · rw [Cslib.Logic.PL.PC.degree_le_iff]
      exact List.forall_mem_append.mpr
        ⟨Cslib.Logic.PL.PC.degree_le_iff.mp hmd₁, Cslib.Logic.PL.PC.degree_le_iff.mp hmd₀⟩
  | @mulVar ls₀ v f _ _ hf ih =>
    have ⟨hm_deg, hls₀⟩ := (linesMaxDegree_cons _ ls₀ k).mp hls
    rcases ih hls₀ with ⟨ms₀, hms₀, hmem₀, hmd₀⟩
    by_cases hf0 : f = 0
    · refine ⟨ms₀, hms₀, fun q hq ↦ ?_, hmd₀⟩
      rcases List.mem_cons.mp hq with rfl | hq'
      · simpa [hf0] using hmem₀ f hf
      · exact hmem₀ q hq'
    · rcases hX_mul v (Φ f) ms₀ hms₀ (hmem₀ f hf) with ⟨ms₁, hms₁, hsub₁, hprod₁, hmd₁⟩
      refine ⟨ms₁, hms₁, fun q hq ↦ ?_, hmd₁.trans (max_le hmd₀ ?_)⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rwa [map_mul]
        · exact hsub₁ (hmem₀ q hq')
      · have hfk : f.totalDegree + 1 ≤ k := by
          classical
          obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup f.support
            (support_nonempty.mpr hf0) (fun s : V →₀ ℕ ↦ s.sum fun _ e ↦ e)
          have hmem : m + Finsupp.single v 1 ∈ (X v * f).support := by
            rw [support_X_mul, Finset.mem_map]
            exact ⟨m, hm, add_comm _ _⟩
          have htd := (le_totalDegree hmem).trans hm_deg
          have hadd : (m + Finsupp.single v 1).sum (fun _ e ↦ e) = f.totalDegree + 1 := by
            rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), ← hmd,
              Finsupp.sum_single_index rfl]
            rfl
          omega
        have h1 := hdeg_map f
        have h2 : c * (f.totalDegree + 1) ≤ c * k := Nat.mul_le_mul_left c hfk
        rw [mul_add, mul_one] at h2
        exact le_max_of_le_right (by omega)
  | @linComb ls₀ a b g f _ hg hf ih =>
    have ⟨_, hls₀⟩ := (linesMaxDegree_cons _ ls₀ k).mp hls
    rcases ih hls₀ with ⟨ms₀, hms₀, hmem₀, hmd₀⟩
    have hlin := hms₀.linear a b (hmem₀ g hg) (hmem₀ f hf)
    refine ⟨(C a * Φ g + C b * Φ f) :: ms₀, hlin, fun q hq ↦ ?_, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq'
      · simp [smul_eq_C_mul]
      · exact .tail _ (hmem₀ q hq')
    · rw [Cslib.Logic.PL.PC.degree_cons, max_le_iff]
      refine ⟨(totalDegree_add _ _).trans (max_le ?_ ?_), hmd₀⟩
      · rw [← smul_eq_C_mul]
        exact (totalDegree_smul_le _ _).trans
          (Cslib.Logic.PL.PC.degree_le_iff.mp hmd₀ _ (hmem₀ g hg))
      · rw [← smul_eq_C_mul]
        exact (totalDegree_smul_le _ _).trans
          (Cslib.Logic.PL.PC.degree_le_iff.mp hmd₀ _ (hmem₀ f hf))

private theorem eval_congr_vars [CommRing R] {p : MvPolynomial V R} {σ₁ σ₂ : V → R}
    (h : ∀ v ∈ p.vars, σ₁ v = σ₂ v) : eval σ₁ p = eval σ₂ p := by
  classical
  exact MvPolynomial.eval₂_congr (f := RingHom.id R) σ₁ σ₂ fun {v c} hvc hcoeff ↦
    h v ((mem_vars_iff_mem_support v).mpr ⟨c, mem_support_iff.mpr hcoeff, hvc⟩)

/-- Boolean soundness (existence): any `{0, 1}`-assignment `σ : V → R` over `baseVars` vanishing on
`P` extends to `σ' : V → R` agreeing with `σ` outside `exts` and vanishing on all derived lines. -/
theorem EPCDeriv.exists_boolExtension [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {exts : List V} {lines : List (MvPolynomial V R)}
    (d : EPCDeriv baseVars P exts lines) (σ : V → R)
    (hbool : ∀ v ∈ baseVars, σ v = 0 ∨ σ v = 1) (hP : ∀ p ∈ P, eval σ p = 0) :
    ∃ σ' : V → R, (∀ v, v ∉ exts → σ' v = σ v) ∧ ∀ q ∈ lines, eval σ' q = 0 := by
  classical
  induction d with
  | nil => exact ⟨σ, fun _ _ ↦ rfl, by simp⟩
  | inputAx d hp ih =>
    rcases ih with ⟨σ', hσ', hlines⟩
    refine ⟨σ', hσ', fun q hq ↦ ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [eval_congr_vars fun v hv ↦ hσ' v fun he ↦ (d.extVars_fresh v he).2 q hp hv]
      exact hP q hp
    · exact hlines q hq'
  | boolAx d hv ih =>
    rcases ih with ⟨σ', hσ', hlines⟩
    refine ⟨σ', hσ', fun q hq ↦ ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    · have hσv : σ' _ = σ _ := hσ' _ fun hv_ext ↦ (d.extVars_fresh _ hv_ext).1 hv
      simp only [map_sub, map_pow, eval_X, hσv]
      rcases hbool _ hv with h | h <;> simp [h]
    · exact hlines q hq'
  | mulVar _ _ hf ih =>
    rcases ih with ⟨σ', hσ', hlines⟩
    refine ⟨σ', hσ', fun q hq ↦ ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    exacts [by simp [eval_mul, hlines _ hf], hlines q hq']
  | linComb _ hg hf ih =>
    rcases ih with ⟨σ', hσ', hlines⟩
    refine ⟨σ', hσ', fun q hq ↦ ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    exacts [by simp [eval_add, smul_eval, hlines _ hg, hlines _ hf], hlines q hq']
  | extAx d hxb hxP hxf hfv ih =>
    rename_i _ _ x f
    rcases ih with ⟨σ', hσ', hlines⟩
    let σ'' : V → R := fun u ↦ if u = x then eval σ' f else σ' u
    refine ⟨σ'', fun u hu ↦ ?_, fun q hq ↦ ?_⟩
    · have hne : u ≠ x := fun heq ↦ hu (heq ▸ List.mem_cons_self)
      simp [σ'', hne, hσ' u fun hm ↦ hu (.tail _ hm)]
    · have hx_f : x ∉ f.vars := fun hx ↦ (hfv x hx).elim hxb hxf
      rcases List.mem_cons.mp hq with rfl | hq'
      · have hf : eval σ'' f = eval σ' f :=
          eval_congr_vars fun v hv ↦ by simp [σ'', show v ≠ x from fun h ↦ hx_f (h ▸ hv)]
        simp [σ'', hf]
      · have hx_q := d.notMem_vars_lines_of_fresh hxb hxf hxP q hq'
        have hq : eval σ'' q = eval σ' q :=
          eval_congr_vars fun v hv ↦ by simp [σ'', show v ≠ x from fun h ↦ hx_q (h ▸ hv)]
        rw [hq]
        exact hlines q hq'

/-- Uniqueness of Boolean assignment extensions on all introduced extension variables `exts`. -/
theorem EPCDeriv.eqOn_exts_of_eval_eq_zero [CommRing R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} :
    ∀ {exts lines}, EPCDeriv baseVars P exts lines →
      ∀ {σ₁ σ₂ : V → R}, (∀ v ∈ baseVars, σ₁ v = σ₂ v) →
        (∀ q ∈ lines, eval σ₁ q = 0) → (∀ q ∈ lines, eval σ₂ q = 0) →
        ∀ x ∈ exts, σ₁ x = σ₂ x
  | _, _, .nil, _, _, _, _, _, _, h => nomatch h
  | _, _, .inputAx d _, _, _, hb, h1, h2, x, hx =>
    d.eqOn_exts_of_eval_eq_zero hb (fun _ hq ↦ h1 _ (.tail _ hq))
      (fun _ hq ↦ h2 _ (.tail _ hq)) x hx
  | _, _, .boolAx d _, _, _, hb, h1, h2, x, hx =>
    d.eqOn_exts_of_eval_eq_zero hb (fun _ hq ↦ h1 _ (.tail _ hq))
      (fun _ hq ↦ h2 _ (.tail _ hq)) x hx
  | _, _, .mulVar d _ _, _, _, hb, h1, h2, x, hx =>
    d.eqOn_exts_of_eval_eq_zero hb (fun _ hq ↦ h1 _ (.tail _ hq))
      (fun _ hq ↦ h2 _ (.tail _ hq)) x hx
  | _, _, .linComb d _ _, _, _, hb, h1, h2, x, hx =>
    d.eqOn_exts_of_eval_eq_zero hb (fun _ hq ↦ h1 _ (.tail _ hq))
      (fun _ hq ↦ h2 _ (.tail _ hq)) x hx
  | _, _, .extAx (f := f) d _ _ _ hf_vars, σ₁, σ₂, hb, h1, h2, x, hx => by
    have ih := d.eqOn_exts_of_eval_eq_zero hb
      (fun _ hq ↦ h1 _ (.tail _ hq)) (fun _ hq ↦ h2 _ (.tail _ hq))
    rcases List.mem_cons.mp hx with rfl | hx'
    · have heval_eq : eval σ₁ f = eval σ₂ f :=
        eval_congr_vars fun v hv ↦ (hf_vars v hv).elim (hb v) (ih v)
      have h1x := h1 (X x - f) List.mem_cons_self
      have h2x := h2 (X x - f) List.mem_cons_self
      simp only [map_sub, eval_X, sub_eq_zero] at h1x h2x
      exact h1x.trans (heval_eq.trans h2x.symm)
    · exact ih x hx'

/-- Boolean soundness of $\mathrm{EPC}$: a `{0, 1}`-satisfiable system cannot derive `1`. -/
theorem EPCDeriv.not_one_mem_of_boolSat [CommRing R] [Nontrivial R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {exts lines} (d : EPCDeriv baseVars P exts lines)
    (σ : V → R) (hbool : ∀ v ∈ baseVars, σ v = 0 ∨ σ v = 1) (hP : ∀ p ∈ P, eval σ p = 0) :
    (1 : MvPolynomial V R) ∉ lines := fun h1 ↦ by
  rcases d.exists_boolExtension σ hbool hP with ⟨σ', _, hlines⟩
  have hev := hlines 1 h1
  simp at hev

/-- Boolean soundness of $\mathrm{PC}$: a `{0, 1}`-satisfiable system cannot derive `1`. -/
theorem PCDeriv.not_one_mem_of_boolSat [CommRing R] [Nontrivial R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines} (d : PCDeriv baseVars P lines)
    (σ : V → R) (hbool : ∀ v ∈ baseVars, σ v = 0 ∨ σ v = 1) (hP : ∀ p ∈ P, eval σ p = 0) :
    (1 : MvPolynomial V R) ∉ lines :=
  d.toEPCDeriv.not_one_mem_of_boolSat σ hbool hP

/-- Boolean soundness of $\mathrm{MC}$: a `{0, 1}`-satisfiable system cannot derive `1`. -/
theorem MCDeriv.not_one_mem_of_boolSat [CommRing R] [Nontrivial R] {baseVars : Set V}
    {P : Set (MvPolynomial V R)} {lines} (d : MCDeriv baseVars P lines)
    (σ : V → R) (hbool : ∀ v ∈ baseVars, σ v = 0 ∨ σ v = 1) (hP : ∀ p ∈ P, eval σ p = 0) :
    (1 : MvPolynomial V R) ∉ lines :=
  d.toPCDeriv.not_one_mem_of_boolSat σ hbool hP

private theorem mcRefutes_twoMulXSubOne :
    MCRefutes ({0} : Set ℕ) {(2 : ℚ) • (X 0 : MvPolynomial ℕ ℚ) - 1} 2 := by
  let p : MvPolynomial ℕ ℚ := (2 : ℚ) • X 0 - 1
  let b : MvPolynomial ℕ ℚ := (X 0 : MvPolynomial ℕ ℚ) ^ 2 - X 0
  let d0 : MCDeriv ({0} : Set ℕ) {p} [b, p] := (MCDeriv.nil.inputAx rfl).boolAx rfl
  let d1 : MCDeriv ({0} : Set ℕ) {p} [X 0 * p, b, p] :=
    d0.mulVar rfl (List.mem_cons_of_mem _ List.mem_cons_self) (isMCMultiplicand_of_mem _ rfl)
  let l2 := (1 : ℚ) • (X 0 * p) + (-2 : ℚ) • b
  let d2 : MCDeriv ({0} : Set ℕ) {p} (l2 :: X 0 * p :: [b, p]) :=
    d1.linComb (a := (1 : ℚ)) (b := (-2 : ℚ)) List.mem_cons_self (.tail _ List.mem_cons_self)
  let l3 := (2 : ℚ) • l2 + (-1 : ℚ) • p
  let d3 := d2.linComb (a := (2 : ℚ)) (b := (-1 : ℚ)) List.mem_cons_self
    (.tail _ (.tail _ (.tail _ List.mem_cons_self)))
  have hl2 : l2 = X 0 := by
    simp only [l2, p, b, smul_eq_C_mul, map_neg, map_one, map_ofNat]
    ring
  have hl3 : l3 = 1 := by
    simp only [l3, hl2, p, smul_eq_C_mul, map_neg, map_one, map_ofNat]
    ring
  refine ⟨_, d3, hl3 ▸ List.mem_cons_self, ?_⟩
  have hC1 : (C (-1 : ℚ) : MvPolynomial ℕ ℚ).totalDegree ≤ 1 :=
    (totalDegree_C (-1 : ℚ)).le.trans (Nat.zero_le 1)
  have deg_p1 : p.totalDegree ≤ 1 := by
    rw [show p = (2 : ℚ) • X 0 + C (-1 : ℚ) by simp [p, sub_eq_add_neg]]
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_smul_le _ _).trans (by simp)) hC1)
  have deg_b : b.totalDegree ≤ 2 := by
    rw [show b = (X 0 : MvPolynomial ℕ ℚ) ^ 2 + (-1 : ℚ) • X 0 by simp [b, sub_eq_add_neg]]
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_pow _ _).trans (by simp))
      ((totalDegree_smul_le _ _).trans (by simp)))
  have deg_xp : (X 0 * p).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by have := totalDegree_X_le (R := ℚ) (0 : ℕ); omega)
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq1
  · rw [show (2 : ℚ) • l2 + (-1 : ℚ) • p = 1 from hl3]; simp
  rcases List.mem_cons.mp hq1 with rfl | hq2
  · rw [hl2]; exact (totalDegree_X_le (R := ℚ) 0).trans (by decide)
  rcases List.mem_cons.mp hq2 with rfl | hq3
  · exact deg_xp
  rcases List.mem_cons.mp hq3 with rfl | hq4
  · exact deg_b
  rcases List.mem_singleton.mp hq4 with rfl
  · exact deg_p1.trans (by decide)

private theorem not_epcRefutes_xSubOne (k : ℕ) :
    ¬ EPCRefutes ({0} : Set ℕ) {(X 0 : MvPolynomial ℕ ℚ) - 1} k := by
  rintro ⟨_, _, d, h1, _⟩
  exact d.not_one_mem_of_boolSat (fun _ ↦ (1 : ℚ)) (fun _ _ ↦ Or.inr rfl)
    (fun _ hp ↦ by rcases hp with rfl; simp) h1

end Soundness

end CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus
