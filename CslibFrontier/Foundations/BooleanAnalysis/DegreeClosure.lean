/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Nat.Prime.Defs

import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Choose
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Dimension
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-Degree Zariski Closure and Hamming-Ball Uniqueness on the Boolean Cube

Develops multilinear polynomial evaluation, Hamming-ball non-vanishing, Reed–Muller minimum
distance, and the Nie–Wang finite-degree Zariski closure bound on `{0, 1}^n` under standard Lean
axioms:

1. **Multilinear evaluation and canonical multilinearization**: evaluation of multivariate
   polynomials on `Cslib.BitString`, canonical multilinearization without increasing total degree,
   and exact correspondence with `Cslib.BitString.lowDegree`.
2. **Hamming-ball uniqueness and Reed–Muller minimum distance**: any nonzero function in
   `Cslib.BitString.lowDegree K ι d` is nonzero at some point of every Hamming ball of radius `d`,
   and on `Fin n` satisfies `2 ^ n ≤ #{x | f x ≠ 0} * 2 ^ d`.
3. **Finite-degree Zariski closure (Nie–Wang theorem)**: for any field `K`, degree bound `D`, and
   subset `E ⊆ {0, 1}^n`, the degree-`D` closure `degreeClosure K D E` satisfies
   `#(degreeClosure K D E) * ∑_{j ≤ D} n.choose j ≤ 2 ^ n * #E`, proved via graded-lexicographic
   initial monomials and the Harris–Kleitman correlation inequality.

## Main definitions

* `CslibFrontier.BooleanAnalysis.evalBitString`: evaluation of `P : MvPolynomial ι R` at `ι → Bool`.
* `CslibFrontier.BooleanAnalysis.cubeMonomialPoly`: canonical multilinear monomial `∏ i ∈ S, X i`.
* `CslibFrontier.BooleanAnalysis.multilinearize`: degree-nonincreasing multilinearization of `P`.
* `CslibFrontier.BooleanAnalysis.hammingDist`: Hamming distance on `ι → Bool`.
* `CslibFrontier.BooleanAnalysis.degreeClosure`: degree-`D` Zariski closure `cl_D(E)` on `{0, 1}^n`.

## Main results

* `CslibFrontier.BooleanAnalysis.totalDegree_le_iff_evalBitString_mem_lowDegree`: exact degree
  characterization of multilinear polynomials via `Cslib.BitString.lowDegree`.
* `CslibFrontier.BooleanAnalysis.not_vanish_on_hammingBall`: nonzero degree-`≤ d` functions do not
  vanish on any Hamming ball of radius `d`.
* `CslibFrontier.BooleanAnalysis.two_pow_le_card_ne_zero_mul`: Schwartz–Zippel / Reed–Muller
  minimum-distance bound `2 ^ n ≤ #{x | f x ≠ 0} * 2 ^ d`.
* `CslibFrontier.BooleanAnalysis.card_degreeClosure_mul_le`: Nie–Wang finite-degree closure bound.
* `CslibFrontier.BooleanAnalysis.card_degreeClosure_div_le`: density form of Nie–Wang's theorem.
-/

public section

open Finset MvPolynomial Cslib Cslib.BitString
open scoped BigOperators

namespace CslibFrontier.BooleanAnalysis

/-! ### Evaluation and multilinearization on the Boolean cube -/

section Multilinear

variable {ι R : Type*} [CommRing R]

/-- Evaluation of a multivariate polynomial `P : MvPolynomial ι R` at a Boolean vector
`x : ι → Bool`, mapping `false ↦ 0` and `true ↦ 1`. -/
@[expose]
noncomputable def evalBitString (P : MvPolynomial ι R) (x : ι → Bool) : R :=
  MvPolynomial.eval (bitPoint x) P

@[simp]
theorem evalBitString_C (c : R) (x : ι → Bool) :
    evalBitString (C c : MvPolynomial ι R) x = c := by
  simp [evalBitString]

@[simp]
theorem evalBitString_X (i : ι) (x : ι → Bool) :
    evalBitString (X i : MvPolynomial ι R) x = bitVal R (x i) := by
  simp [evalBitString, bitPoint]

@[simp]
theorem evalBitString_zero (x : ι → Bool) :
    evalBitString (0 : MvPolynomial ι R) x = 0 := by
  simp [evalBitString]

@[simp]
theorem evalBitString_one (x : ι → Bool) :
    evalBitString (1 : MvPolynomial ι R) x = 1 := by
  simp [evalBitString]

@[simp]
theorem evalBitString_add (P Q : MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (P + Q) x = evalBitString P x + evalBitString Q x := by
  simp [evalBitString]

@[simp]
theorem evalBitString_sub (P Q : MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (P - Q) x = evalBitString P x - evalBitString Q x := by
  simp [evalBitString]

@[simp]
theorem evalBitString_neg (P : MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (-P) x = -evalBitString P x := by
  simp [evalBitString]

@[simp]
theorem evalBitString_mul (P Q : MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (P * Q) x = evalBitString P x * evalBitString Q x := by
  simp [evalBitString]

@[simp]
theorem evalBitString_pow (P : MvPolynomial ι R) (k : ℕ) (x : ι → Bool) :
    evalBitString (P ^ k) x = evalBitString P x ^ k := by
  simp [evalBitString]

@[simp]
theorem evalBitString_sum {α : Type*} (s : Finset α) (f : α → MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (∑ a ∈ s, f a) x = ∑ a ∈ s, evalBitString (f a) x := by
  simp [evalBitString]

@[simp]
theorem evalBitString_prod {α : Type*} (s : Finset α) (f : α → MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (∏ a ∈ s, f a) x = ∏ a ∈ s, evalBitString (f a) x := by
  simp [evalBitString]

theorem evalBitString_rename {κ : Type*} (f : ι → κ) (P : MvPolynomial ι R) (x : κ → Bool) :
    evalBitString (MvPolynomial.rename f P) x = evalBitString P (x ∘ f) := by
  simp [evalBitString, MvPolynomial.eval_rename, bitPoint, Function.comp_def]

theorem evalBitString_map {S : Type*} [CommRing S] (φ : R →+* S) (P : MvPolynomial ι R)
    (x : ι → Bool) :
    evalBitString (MvPolynomial.map φ P) x = φ (evalBitString P x) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.map_X, evalBitString_mul,
        evalBitString_mul, map_mul, hp, evalBitString_X, evalBitString_X]
      cases x i <;> simp [bitVal]

theorem evalBitString_bind₁ {κ : Type*} (g : ι → MvPolynomial κ R) (P : MvPolynomial ι R)
    (x : κ → Bool) :
    evalBitString (MvPolynomial.bind₁ g P) x =
      MvPolynomial.eval (fun i ↦ evalBitString (g i) x) P := by
  change eval (bitPoint x) (bind₁ g P) = eval (fun i ↦ eval (bitPoint x) (g i)) P
  simp only [← coe_aeval_eq_eval]
  exact MvPolynomial.aeval_bind₁ (bitPoint x) g P

/-- Evaluating a polynomial of total degree at most `D` on `{0, 1}^ι` yields a function in
`Cslib.BitString.lowDegree R ι D`. -/
theorem evalBitString_mem_lowDegree (P : MvPolynomial ι R) {D : ℕ} (hP : P.totalDegree ≤ D) :
    evalBitString P ∈ lowDegree R ι D := by
  rw [lowDegree_eq_map_restrictTotalDegree]
  refine ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP, ?_⟩
  ext x
  change (aeval (fun i (y : ι → Bool) ↦ bitVal R (y i)) P) x = eval (bitPoint x) P
  clear hP
  induction P using MvPolynomial.induction_on with
  | C c => rw [aeval_C, eval_C, Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one]
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, hp, aeval_X, eval_X, bitPoint]

/-- Canonical multilinear monomial polynomial `∏ i ∈ S, X i`. -/
@[expose]
noncomputable def cubeMonomialPoly (S : Finset ι) : MvPolynomial ι R :=
  ∏ i ∈ S, X i

@[simp]
theorem evalBitString_cubeMonomialPoly (S : Finset ι) (x : ι → Bool) :
    evalBitString (cubeMonomialPoly S : MvPolynomial ι R) x =
      Cslib.BitString.monomial R S x := by
  classical
  rw [cubeMonomialPoly, evalBitString_prod, Cslib.BitString.monomial_apply]
  split_ifs with h
  · exact prod_eq_one fun i hi ↦ by simp [h i hi, bitVal]
  · push Not at h
    rcases h with ⟨i, hiS, hix⟩
    have hxf : x i = false := Bool.eq_false_iff.mpr hix
    exact prod_eq_zero hiS (by simp [hxf, bitVal])

theorem totalDegree_cubeMonomialPoly_le (S : Finset ι) :
    (cubeMonomialPoly S : MvPolynomial ι R).totalDegree ≤ #S := by
  refine (totalDegree_finsetProd S _).trans ?_
  calc ∑ i ∈ S, (X i : MvPolynomial ι R).totalDegree
      ≤ ∑ _i ∈ S, 1 := sum_le_sum fun i _ ↦ totalDegree_X_le i
    _ = #S := by simp

theorem totalDegree_cubeMonomialPoly [Nontrivial R] (S : Finset ι) :
    (cubeMonomialPoly S : MvPolynomial ι R).totalDegree = #S := by
  classical
  have hprod : (cubeMonomialPoly S : MvPolynomial ι R) =
      MvPolynomial.monomial (∑ i ∈ S, Finsupp.single i 1) 1 := by
    induction S using Finset.induction_on with
    | empty => simp [cubeMonomialPoly]
    | insert a s ha ih =>
        rw [cubeMonomialPoly, prod_insert ha, sum_insert ha]
        change X a * cubeMonomialPoly s = _
        rw [ih, X, MvPolynomial.monomial_mul_monomial, one_mul]
  rw [hprod, totalDegree_monomial _ one_ne_zero, Finsupp.sum]
  have hsupp : (∑ i ∈ S, Finsupp.single i (1 : ℕ)).support = S := by
    ext i
    simp [Finsupp.single_apply]
  rw [hsupp]
  have hval : ∀ i ∈ S, (∑ j ∈ S, Finsupp.single j (1 : ℕ)) i = 1 := by
    intro i hi
    simp [Finsupp.single_apply, hi]
  rw [sum_congr rfl hval]
  simp

theorem cubeMonomialPoly_mem_restrictDegree (S : Finset ι) :
    (cubeMonomialPoly S : MvPolynomial ι R) ∈ restrictDegree ι R 1 := by
  classical
  have hprod : (cubeMonomialPoly S : MvPolynomial ι R) =
      MvPolynomial.monomial (∑ j ∈ S, Finsupp.single j 1) 1 := by
    induction S using Finset.induction_on with
    | empty => simp [cubeMonomialPoly, MvPolynomial.monomial_zero']
    | insert a s ha ih =>
        rw [cubeMonomialPoly, prod_insert ha, sum_insert ha]
        change X a * cubeMonomialPoly s = _
        rw [ih, X, MvPolynomial.monomial_mul_monomial, one_mul]
  rw [mem_restrictDegree]
  intro d hd i
  by_cases h0 : (1 : R) = 0
  · exfalso
    have : Subsingleton R := subsingleton_of_zero_eq_one h0.symm
    exact (mem_support_iff.mp hd) (Subsingleton.elim _ _)
  · simp only [hprod, support_monomial, h0, ↓reduceIte, mem_singleton] at hd
    subst hd
    by_cases hi : i ∈ S <;> simp [Finsupp.single_apply, hi]

/-- Canonical multilinearization of a multivariate polynomial `P : MvPolynomial ι R`, replacing
each monomial `c · ∏ i, X_i^(d i)` with `c · ∏_{i ∈ d.support} X_i`. Preserves evaluation on
`{0, 1}^ι` and never increases total degree. -/
noncomputable def multilinearize (P : MvPolynomial ι R) : MvPolynomial ι R :=
  ∑ d ∈ P.support, C (P.coeff d) * cubeMonomialPoly d.support

theorem evalBitString_multilinearize (P : MvPolynomial ι R) (x : ι → Bool) :
    evalBitString (multilinearize P) x = evalBitString P x := by
  classical
  conv_rhs => rw [P.as_sum]
  rw [multilinearize, evalBitString_sum, evalBitString_sum]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [show MvPolynomial.monomial d (P.coeff d) = C (P.coeff d) * MvPolynomial.monomial d 1 by
    rw [C_mul_monomial, mul_one]]
  simp only [evalBitString_mul, evalBitString_C, evalBitString_cubeMonomialPoly,
    Cslib.BitString.monomial_apply]
  congr 1
  rw [evalBitString, eval_monomial, one_mul, Finsupp.prod]
  split_ifs with h
  · exact (prod_eq_one fun i hi ↦ by simp [bitPoint, h i hi, bitVal]).symm
  · push Not at h
    rcases h with ⟨i, hid, hix⟩
    have hxf : x i = false := Bool.eq_false_iff.mpr hix
    have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hid
    exact (prod_eq_zero hid (by simp [bitPoint, hxf, bitVal, zero_pow hdi])).symm

theorem totalDegree_multilinearize_le (P : MvPolynomial ι R) :
    (multilinearize P).totalDegree ≤ P.totalDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd ↦ ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_cubeMonomialPoly_le d.support).trans ?_
  calc #d.support = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := sum_le_sum fun i hi ↦
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    _ ≤ P.totalDegree := Finset.le_sup (f := fun s : ι →₀ ℕ ↦ s.sum fun _ e ↦ e) hd

theorem multilinearize_mem_restrictDegree (P : MvPolynomial ι R) :
    multilinearize P ∈ restrictDegree ι R 1 :=
  Submodule.sum_mem _ fun d _ ↦ by
    have hmem := cubeMonomialPoly_mem_restrictDegree (R := R) d.support
    simpa [Algebra.smul_def] using
      Submodule.smul_mem (restrictDegree ι R 1) (P.coeff d) hmem

/-- Every function in `lowDegree R ι D` is represented on `{0, 1}^ι` by a multilinear polynomial of
total degree at most `D`. -/
theorem exists_multilinear_poly_of_mem_lowDegree {D : ℕ} {f : (ι → Bool) → R}
    (hf : f ∈ lowDegree R ι D) :
    ∃ Q : MvPolynomial ι R, Q ∈ restrictDegree ι R 1 ∧ Q.totalDegree ≤ D ∧
      evalBitString Q = f := by
  rw [lowDegree_eq_map_restrictTotalDegree] at hf
  rcases hf with ⟨P, hPD, hPf⟩
  refine ⟨multilinearize P, multilinearize_mem_restrictDegree P,
    (totalDegree_multilinearize_le P).trans
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hPD), ?_⟩
  ext x
  rw [evalBitString_multilinearize, ← hPf]
  change eval (bitPoint x) P = (aeval (fun i (y : ι → Bool) ↦ bitVal R (y i)) P) x
  clear hPD hPf
  induction P using MvPolynomial.induction_on with
  | C c => rw [aeval_C, eval_C, Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one]
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, hp, aeval_X, eval_X, bitPoint]

/-- Expanding a multilinear polynomial as a linear combination of `cubeMonomialPoly S` allows
extracting its unique monomial coefficients from cube evaluation over any field. -/
theorem multilinear_eq_zero_of_evalBitString_eq_zero {K : Type*} [Field K]
    {Q : MvPolynomial ι K} (hQ : Q ∈ restrictDegree ι K 1)
    (heval : ∀ x : ι → Bool, evalBitString Q x = 0) : Q = 0 := by
  classical
  have hmon : ∀ S : Finset ι, (cubeMonomialPoly S : MvPolynomial ι K) =
      MvPolynomial.monomial (∑ i ∈ S, Finsupp.single i 1) 1 := fun S ↦ by
    induction S using Finset.induction_on with
    | empty => simp [cubeMonomialPoly, MvPolynomial.monomial_zero']
    | insert a s ha ih =>
        rw [cubeMonomialPoly, prod_insert ha, sum_insert ha]
        change X a * cubeMonomialPoly s = _
        rw [ih, X, MvPolynomial.monomial_mul_monomial, one_mul]
  have hd_eq : ∀ d ∈ Q.support, ∑ i ∈ d.support, Finsupp.single i (1 : ℕ) = d := fun d hd ↦ by
    have hd1 : ∀ i, d i ≤ 1 := by
      rw [mem_restrictDegree] at hQ
      exact hQ d hd
    ext i
    by_cases hi : i ∈ d.support
    · have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hle := hd1 i
      have h1 : (∑ j ∈ d.support, Finsupp.single j (1 : ℕ)) i = 1 := by
        simp [Finsupp.single_apply, hi]
      omega
    · have hdi : d i = 0 := Finsupp.notMem_support_iff.mp hi
      simp [Finsupp.single_apply, hi, hdi]
  let suppSets : Finset (Finset ι) := Q.support.image Finsupp.support
  have hexp : Q = ∑ S ∈ suppSets,
      C (Q.coeff (∑ i ∈ S, Finsupp.single i 1)) * cubeMonomialPoly S := by
    conv_lhs => rw [Q.as_sum]
    rw [show suppSets = Q.support.image Finsupp.support from rfl,
      sum_image (fun d₁ hd₁ d₂ hd₂ hsup ↦ by
        rw [← hd_eq d₁ hd₁, ← hd_eq d₂ hd₂, hsup])]
    refine sum_congr rfl fun d hd ↦ ?_
    rw [hmon d.support, hd_eq d hd, C_mul_monomial, mul_one]
  -- Prove linear independence on `suppSets` directly by upward-size evaluation (works for any `ι`)
  have hcoeff0 : ∀ m : ℕ, ∀ S ∈ suppSets, #S = m →
      Q.coeff (∑ i ∈ S, Finsupp.single i 1) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro S hS hSm
      let xS : ι → Bool := fun i ↦ decide (i ∈ S)
      have hx := heval xS
      rw [hexp, evalBitString_sum] at hx
      simp only [evalBitString_mul, evalBitString_C, evalBitString_cubeMonomialPoly,
        Cslib.BitString.monomial_apply, xS, decide_eq_true_eq] at hx
      rw [sum_eq_single S] at hx
      · simpa using hx
      · intro T hT hne
        by_cases hTS : T ⊆ S
        · have hlt : #T < m := hSm ▸ card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
          rw [ih #T hlt T hT rfl, zero_mul]
        · have hn : ¬(∀ i ∈ T, i ∈ S) := hTS; simp [hn]
      · intro hnot; exact (hnot hS).elim
  rw [hexp]
  exact sum_eq_zero fun S hS ↦ by simp [hcoeff0 #S S hS rfl]

/-- For a multilinear polynomial over a field, its total degree is bounded by `D` if and only if
its cube evaluation lies in `lowDegree K ι D`. -/
theorem totalDegree_le_iff_evalBitString_mem_lowDegree {K : Type*} [Field K]
    {Q : MvPolynomial ι K} (hQ : Q ∈ restrictDegree ι K 1) (D : ℕ) :
    Q.totalDegree ≤ D ↔ evalBitString Q ∈ lowDegree K ι D := by
  refine ⟨evalBitString_mem_lowDegree Q, fun hmem ↦ ?_⟩
  rcases exists_multilinear_poly_of_mem_lowDegree hmem with ⟨Q', hQ'1, hQ'D, hQ'eq⟩
  have hdiff : Q - Q' = 0 := by
    refine multilinear_eq_zero_of_evalBitString_eq_zero (Submodule.sub_mem _ hQ hQ'1) fun x ↦ ?_
    rw [evalBitString_sub, congr_fun hQ'eq x, sub_self]
  rw [sub_eq_zero.mp hdiff]
  exact hQ'D

end Multilinear

/-! ### Hamming balls and minimum distance of low-degree polynomials -/

section HammingBall

variable {ι K : Type*} [Field K] [Fintype ι]

/-- Hamming distance between two Boolean vectors `x, y : ι → Bool`. -/
def hammingDist (x y : ι → Bool) : ℕ :=
  #(univ.filter (fun i : ι ↦ x i ≠ y i))

@[simp]
theorem hammingDist_self (x : ι → Bool) : hammingDist x x = 0 := by
  simp [hammingDist]

theorem hammingDist_comm (x y : ι → Bool) : hammingDist x y = hammingDist y x := by
  simp only [hammingDist, ne_comm]

theorem hammingDist_false_eq_weight (x : ι → Bool) :
    hammingDist x (fun _ ↦ false) = weight x := by
  simp [hammingDist, weight]

omit [Fintype ι] in
/-- Coordinatewise XOR shift preserves membership in `lowDegree K ι d`. -/
theorem comp_xor_mem_lowDegree {d : ℕ} {f : (ι → Bool) → K}
    (hf : f ∈ lowDegree K ι d)
    (c : ι → Bool) : (fun x : ι → Bool ↦ f (fun i ↦ xor (x i) (c i))) ∈ lowDegree K ι d := by
  classical
  rcases exists_multilinear_poly_of_mem_lowDegree hf with ⟨Q, _, hQd, hQeq⟩
  let g : ι → MvPolynomial ι K := fun i ↦ if c i then 1 - X i else X i
  let Q' : MvPolynomial ι K := MvPolynomial.bind₁ g Q
  have hg_deg : ∀ i : ι, (g i).totalDegree ≤ 1 := by
    intro i
    simp only [g]
    split_ifs
    · rw [sub_eq_add_neg]
      refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
      rw [totalDegree_neg]; exact totalDegree_X_le i
    · exact totalDegree_X_le i
  have hQ'_eq : Q' = ∑ s ∈ Q.support, C (Q.coeff s) * ∏ i ∈ s.support, g i ^ s i := by
    change bind₁ g Q = _
    conv_lhs => rw [Q.as_sum, map_sum]
    exact sum_congr rfl fun s _ ↦ bind₁_monomial g s (Q.coeff s)
  have hQ'_deg' : Q'.totalDegree ≤ d := by
    rw [hQ'_eq]
    refine ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)).trans hQd
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ i ∈ s.support, (g i ^ s i).totalDegree
        ≤ ∑ i ∈ s.support, s i * (g i).totalDegree :=
          sum_le_sum fun i _ ↦ totalDegree_pow _ _
      _ ≤ ∑ i ∈ s.support, s i * 1 :=
          sum_le_sum fun i _ ↦ Nat.mul_le_mul_left _ (hg_deg i)
      _ = s.sum (fun _ e ↦ e) := by simp [Finsupp.sum]
      _ ≤ Q.totalDegree := Finset.le_sup (f := fun t : ι →₀ ℕ ↦ t.sum fun _ e ↦ e) hs
  have heval : evalBitString Q' = fun x ↦ f (fun i ↦ xor (x i) (c i)) := by
    ext x
    rw [← hQeq, evalBitString_bind₁, evalBitString]
    have hpt : (fun i ↦ evalBitString (g i) x) = bitPoint (fun i ↦ xor (x i) (c i)) := by
      ext i; dsimp [g, bitPoint]
      cases hc : c i <;> cases hx : x i <;> simp [hx, bitVal]
    rw [hpt]
  rw [← heval]
  exact evalBitString_mem_lowDegree Q' hQ'_deg'

/-- A function in `lowDegree K ι d` vanishing at all points of Hamming weight at most `d` is
identically zero. -/
theorem eq_zero_of_mem_lowDegree_of_vanish_weight_le {d : ℕ} {f : (ι → Bool) → K}
    (hf : f ∈ lowDegree K ι d) (hvan : ∀ x : ι → Bool, weight x ≤ d → f x = 0) :
    f = 0 := by
  classical
  have hspan : lowDegree K ι d =
      Submodule.span K ((Cslib.BitString.monomial K) ''
        (↑(univ.filter (fun S : Finset ι ↦ #S ≤ d)) : Set (Finset ι))) := by
    rw [lowDegree]; congr 1; ext g; simp
  rw [hspan, Submodule.mem_span_image_finset_iff_exists_fun] at hf
  rcases hf with ⟨c, rfl⟩
  have hc0 : ∀ m : ℕ, ∀ S : Finset ι, (hS : S ∈ univ.filter (fun T : Finset ι ↦ #T ≤ d)) →
      #S = m → c ⟨S, hS⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro S hS hSm
      have hSd : #S ≤ d := (mem_filter.mp hS).2
      let xS : ι → Bool := fun i ↦ decide (i ∈ S)
      have hwx : weight xS = #S := by simp [weight, xS]
      have hx0 : (∑ T : univ.filter (fun T : Finset ι ↦ #T ≤ d),
          c T • Cslib.BitString.monomial K (T : Finset ι)) xS = 0 :=
        hvan xS (hwx ▸ hSd)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Cslib.BitString.monomial_apply, xS, decide_eq_true_eq] at hx0
      rw [sum_eq_single ⟨S, hS⟩] at hx0
      · simpa using hx0
      · rintro ⟨T, hT⟩ _ hne
        by_cases hTS : T ⊆ S
        · have hss : T ⊂ S :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hTS, fun heq ↦ hne (Subtype.ext heq)⟩
          rw [ih #T (hSm ▸ card_lt_card hss) T hT rfl, zero_mul]
        · have hn : ¬(∀ i ∈ T, i ∈ S) := hTS
          simp [hn]
      · intro hmem; exact absurd (mem_univ _) hmem
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact sum_eq_zero fun T _ ↦ by rw [hc0 #T.1 T.1 T.2 rfl, zero_mul]

/-- **Non-vanishing on Hamming balls**: a nonzero function in
`lowDegree K ι d` cannot vanish at every point of a Hamming ball of radius `d` around any center
`c : ι → Bool`.
-/
theorem not_vanish_on_hammingBall {d : ℕ} {f : (ι → Bool) → K}
    (hf : f ∈ lowDegree K ι d) (hne : f ≠ 0) (c : ι → Bool) :
    ∃ x : ι → Bool, hammingDist x c ≤ d ∧ f x ≠ 0 := by
  by_contra hall
  push Not at hall
  let g : (ι → Bool) → K := fun y ↦ f (fun i ↦ xor (y i) (c i))
  have hg : g ∈ lowDegree K ι d := comp_xor_mem_lowDegree hf c
  have hg0 : g = 0 := by
    refine eq_zero_of_mem_lowDegree_of_vanish_weight_le hg fun y hy ↦ hall _ ?_
    have hdist : hammingDist (fun i ↦ xor (y i) (c i)) c = weight y := by
      simp only [hammingDist, weight]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and]
      cases y i <;> cases c i <;> decide
    exact hdist ▸ hy
  apply hne
  ext x
  have hx := congr_fun hg0 (fun i ↦ xor (x i) (c i))
  simpa [g, Bool.xor_assoc] using hx

/-- **Non-vanishing of multilinear polynomials on Hamming balls**: a nonzero multilinear polynomial
`R ∈ MvPolynomial ι K` of total degree at most `d` cannot vanish throughout any Hamming ball of
radius `d` in `{0, 1}^ι`. -/
theorem multilinear_not_vanish_on_hammingBall {d : ℕ} {P : MvPolynomial ι K}
    (hmlin : P ∈ restrictDegree ι K 1) (hd : P.totalDegree ≤ d) (hne : P ≠ 0)
    (c : ι → Bool) :
    ∃ x : ι → Bool, hammingDist x c ≤ d ∧ evalBitString P x ≠ 0 := by
  refine not_vanish_on_hammingBall (evalBitString_mem_lowDegree P hd) ?_ c
  intro heval
  exact hne (multilinear_eq_zero_of_evalBitString_eq_zero hmlin (congr_fun heval))

/-- **Reed–Muller minimum-distance bound on `{0, 1}^n`**: any nonzero function `f` in
`lowDegree K (Fin n) d` is nonzero at at least `2^(n - d)` points of `{0, 1}^n`, stated
division-freely as `2^n ≤ #{x | f x ≠ 0} * 2^d`. -/
theorem two_pow_le_card_ne_zero_mul :
    ∀ {n d : ℕ} {f : BitString n → K}, [DecidableEq K] →
      f ∈ lowDegree K (Fin n) d → f ≠ 0 →
      2 ^ n ≤ #(univ.filter (fun x : BitString n ↦ f x ≠ 0)) * 2 ^ d
  | 0, d, f, _, _, hne => by
      classical
      have h0 : f Fin.elim0 ≠ 0 := fun h0 ↦
        hne (funext fun x ↦ by rw [Subsingleton.elim x Fin.elim0]; exact h0)
      have hcard : 1 ≤ #(univ.filter (fun x : BitString 0 ↦ f x ≠ 0)) :=
        card_pos.mpr ⟨Fin.elim0, mem_filter.mpr ⟨mem_univ _, h0⟩⟩
      have hd1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      simpa using Nat.mul_le_mul hcard hd1
  | n + 1, 0, f, _, hf, hne => by
      have hspan : lowDegree K (Fin (n + 1)) 0 =
          Submodule.span K {Cslib.BitString.monomial K (∅ : Finset (Fin (n + 1)))} := by
        rw [lowDegree]; congr 1; ext g; simp
      rw [hspan, Submodule.mem_span_singleton] at hf
      rcases hf with ⟨c, rfl⟩
      have hc : c ≠ 0 := fun hc0 ↦ hne (by simp [hc0])
      have hall : univ.filter (fun x : BitString (n + 1) ↦
          (c • Cslib.BitString.monomial K (∅ : Finset (Fin (n + 1)))) x ≠ 0) = univ := by
        ext x
        simp [Cslib.BitString.monomial_empty, hc]
      rw [hall, card_univ, Fintype.card_pi, prod_const, Fintype.card_bool]
      simp [Fintype.card_fin]
  | n + 1, d + 1, f, _, hf, hne => by
      classical
      let f0 : BitString n → K := fun x ↦ f (Fin.cons false x)
      let f1 : BitString n → K := fun x ↦ f (Fin.cons true x) - f (Fin.cons false x)
      -- Restricting x_0 = false or taking the discrete derivative x_0 drops degree cleanly.
      have hdecomp : ∃ g0 ∈ lowDegree K (Fin n) (d + 1), ∃ g1 ∈ lowDegree K (Fin n) d,
          g0 = f0 ∧ g1 = f1 := by
        have hspan : lowDegree K (Fin (n + 1)) (d + 1) =
            Submodule.span K ((Cslib.BitString.monomial K) ''
              (↑(univ.filter (fun S : Finset (Fin (n + 1)) ↦ #S ≤ d + 1)) :
                Set (Finset (Fin (n + 1))))) := by
          rw [lowDegree]; congr 1; ext g; simp
        rw [hspan, Submodule.mem_span_image_finset_iff_exists_fun] at hf
        rcases hf with ⟨c, rfl⟩
        let tailSet : Finset (Fin (n + 1)) → Finset (Fin n) :=
          fun S ↦ univ.filter (fun j : Fin n ↦ j.succ ∈ S)
        have hmon_false : ∀ S : Finset (Fin (n + 1)), ∀ x : BitString n,
            Cslib.BitString.monomial K S (Fin.cons false x) =
              if (0 : Fin (n + 1)) ∈ S then 0 else Cslib.BitString.monomial K (tailSet S) x := by
          intro S x
          by_cases h0S : (0 : Fin (n + 1)) ∈ S
          · have hn : ¬(∀ i ∈ S, (Fin.cons false x : BitString (n + 1)) i = true) :=
              fun h ↦ Bool.false_ne_true (h 0 h0S)
            simp [h0S, Cslib.BitString.monomial_apply, hn]
          · simp only [h0S, ↓reduceIte, Cslib.BitString.monomial_apply]
            congr 1
            exact propext ⟨fun h j hj ↦ by
                have := h j.succ (by simpa [tailSet] using hj); simpa using this,
              fun h i hi ↦ Fin.cases (fun hi0 ↦ absurd hi0 h0S)
                (fun j hj ↦ by simpa using h j (by simp [tailSet, hj])) i hi⟩
        have hmon_true : ∀ S : Finset (Fin (n + 1)), ∀ x : BitString n,
            Cslib.BitString.monomial K S (Fin.cons true x) =
              Cslib.BitString.monomial K (tailSet S) x := by
          intro S x
          rw [Cslib.BitString.monomial_apply, Cslib.BitString.monomial_apply]
          congr 1
          exact propext ⟨fun h j hj ↦ by
              have := h j.succ (by simpa [tailSet] using hj); simpa using this,
            fun h i hi ↦ Fin.cases (fun _ ↦ by simp)
              (fun j hj ↦ by simpa using h j (by simp [tailSet, hj])) i hi⟩
        refine ⟨f0, ?_, f1, ?_, rfl, rfl⟩
        · have hf0_eq : f0 = ∑ T : univ.filter (fun S : Finset (Fin (n + 1)) ↦ #S ≤ d + 1),
              if (0 : Fin (n + 1)) ∈ (T : Finset (Fin (n + 1))) then 0
              else c T • Cslib.BitString.monomial K (tailSet T) := by
            ext x
            simp only [f0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hmon_false]
            refine sum_congr rfl fun T _ ↦ ?_
            split_ifs <;> simp
          rw [hf0_eq]
          refine Submodule.sum_mem _ fun ⟨S, hS⟩ _ ↦ ?_
          split_ifs
          · exact Submodule.zero_mem _
          · refine Submodule.smul_mem _ _ (monomial_mem_lowDegree ?_)
            have hcard : #(tailSet S) ≤ #S := by
              have himg : (tailSet S).map ⟨Fin.succ, Fin.succ_injective _⟩ ⊆ S := by
                intro i hi
                simp only [tailSet, mem_map, mem_filter, mem_univ, true_and] at hi
                rcases hi with ⟨j, hjS, rfl⟩
                exact hjS
              simpa using card_le_card himg
            exact hcard.trans (mem_filter.mp hS).2
        · have hf1_eq : f1 = ∑ T : univ.filter (fun S : Finset (Fin (n + 1)) ↦ #S ≤ d + 1),
              if (0 : Fin (n + 1)) ∈ (T : Finset (Fin (n + 1))) then
                c T • Cslib.BitString.monomial K (tailSet T)
              else 0 := by
            ext x
            simp only [f1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hmon_true, hmon_false,
              ← sum_sub_distrib]
            refine sum_congr rfl fun T _ ↦ ?_
            split_ifs <;> simp
          rw [hf1_eq]
          refine Submodule.sum_mem _ fun ⟨S, hS⟩ _ ↦ ?_
          split_ifs with h0S
          · refine Submodule.smul_mem _ _ (monomial_mem_lowDegree ?_)
            have himg : insert (0 : Fin (n + 1))
                ((tailSet S).map ⟨Fin.succ, Fin.succ_injective _⟩) ⊆ S := by
              intro i hi
              rcases mem_insert.mp hi with rfl | hi'
              · exact h0S
              · simp only [tailSet, mem_map, mem_filter, mem_univ, true_and] at hi'
                rcases hi' with ⟨j, hjS, rfl⟩
                exact hjS
            have h0not : (0 : Fin (n + 1)) ∉
                (tailSet S).map ⟨Fin.succ, Fin.succ_injective _⟩ := by
              simp
            have hle := card_le_card himg
            rw [card_insert_of_notMem h0not, card_map] at hle
            have hSd : #S ≤ d + 1 := (mem_filter.mp hS).2
            exact Nat.le_of_succ_le_succ (hle.trans hSd)
          · exact Submodule.zero_mem _
      rcases hdecomp with ⟨_, hf0_deg, _, hf1_deg, rfl, rfl⟩
      have hcount_split : #(univ.filter (fun x : BitString (n + 1) ↦ f x ≠ 0)) =
          #(univ.filter (fun y : BitString n ↦ f (Fin.cons false y) ≠ 0)) +
          #(univ.filter (fun y : BitString n ↦ f (Fin.cons true y) ≠ 0)) := by
        let e : Bool × BitString n ≃ BitString (n + 1) :=
          { toFun := fun p ↦ Fin.cons p.1 p.2
            invFun := fun x ↦ (x 0, Fin.tail x)
            left_inv := fun ⟨b, y⟩ ↦ by simp
            right_inv := fun x ↦ by simp }
        have hcard_eq : #(univ.filter (fun x : BitString (n + 1) ↦ f x ≠ 0)) =
            #(univ.filter (fun p : Bool × BitString n ↦ f (e p) ≠ 0)) := by
          refine card_bij (fun x _ ↦ e.symm x) (fun x hx ↦ by simpa using hx)
            (fun _ _ _ _ h ↦ e.symm.injective h)
            (fun p hp ↦ ⟨e p, by simpa using hp, e.symm_apply_apply p⟩)
        rw [hcard_eq]
        have hdisj : Disjoint
            (univ.filter (fun p : Bool × BitString n ↦ p.1 = false ∧ f (e p) ≠ 0))
            (univ.filter (fun p : Bool × BitString n ↦ p.1 = true ∧ f (e p) ≠ 0)) := by
          rw [disjoint_left]
          intro p hp1 hp2
          simp only [mem_filter] at hp1 hp2
          exact Bool.false_ne_true (hp1.2.1.symm.trans hp2.2.1)
        have hunion : univ.filter (fun p : Bool × BitString n ↦ f (e p) ≠ 0) =
            univ.filter (fun p : Bool × BitString n ↦ p.1 = false ∧ f (e p) ≠ 0) ∪
            univ.filter (fun p : Bool × BitString n ↦ p.1 = true ∧ f (e p) ≠ 0) := by
          ext ⟨b, y⟩
          cases b <;> simp
        rw [hunion, card_union_of_disjoint hdisj]
        congr 1
        · refine card_bij (fun p _ ↦ p.2) (fun ⟨b, y⟩ hp ↦ ?_) (fun ⟨b1, y1⟩ hp1 ⟨b2,
          y2⟩ hp2 h ↦ ?_)
            (fun y hy ↦ ⟨(false, y), by simpa [e] using hy, rfl⟩)
          · simp only [mem_filter, mem_univ, true_and] at hp ⊢
            rcases hp with ⟨rfl, hf'⟩
            exact hf'
          · simp only [mem_filter, mem_univ, true_and] at hp1 hp2
            rcases hp1 with ⟨rfl, _⟩; rcases hp2 with ⟨rfl, _⟩
            exact Prod.ext rfl h
        · refine card_bij (fun p _ ↦ p.2) (fun ⟨b, y⟩ hp ↦ ?_) (fun ⟨b1, y1⟩ hp1 ⟨b2,
          y2⟩ hp2 h ↦ ?_)
            (fun y hy ↦ ⟨(true, y), by simpa [e] using hy, rfl⟩)
          · simp only [mem_filter, mem_univ, true_and] at hp ⊢
            rcases hp with ⟨rfl, hf'⟩
            exact hf'
          · simp only [mem_filter, mem_univ, true_and] at hp1 hp2
            rcases hp1 with ⟨rfl, _⟩; rcases hp2 with ⟨rfl, _⟩
            exact Prod.ext rfl h
      by_cases hf1_zero : f1 = 0
      · have heq01 : ∀ y : BitString n, f (Fin.cons true y) = f (Fin.cons false y) := fun y ↦
          sub_eq_zero.mp (congr_fun hf1_zero y)
        have hf0_ne : f0 ≠ 0 := by
          intro hf0_z
          apply hne
          ext x
          rw [← Fin.cons_self_tail x]
          cases x 0
          · exact congr_fun hf0_z (Fin.tail x)
          · rw [heq01]; exact congr_fun hf0_z (Fin.tail x)
        have hih := two_pow_le_card_ne_zero_mul hf0_deg hf0_ne
        rw [hcount_split]
        have hsame : #(univ.filter (fun y : BitString n ↦ f (Fin.cons true y) ≠ 0)) =
            #(univ.filter (fun y : BitString n ↦ f (Fin.cons false y) ≠ 0)) := by
          simp_rw [heq01]
        rw [hsame]
        change 2 ^ (n + 1) ≤ (#(univ.filter fun y ↦ f0 y ≠ 0) +
          #(univ.filter fun y ↦ f0 y ≠ 0)) * 2 ^ (d + 1)
        linarith [show 2 ^ (n + 1) = 2 * 2 ^ n by ring]
      · have hih := two_pow_le_card_ne_zero_mul hf1_deg hf1_zero
        have hle_sum : #(univ.filter (fun y : BitString n ↦ f1 y ≠ 0)) ≤
            #(univ.filter (fun y : BitString n ↦ f (Fin.cons false y) ≠ 0)) +
            #(univ.filter (fun y : BitString n ↦ f (Fin.cons true y) ≠ 0)) := by
          refine (card_le_card (t :=
            univ.filter (fun y : BitString n ↦ f (Fin.cons false y) ≠ 0) ∪
            univ.filter (fun y : BitString n ↦ f (Fin.cons true y) ≠ 0)) ?_).trans
            (card_union_le _ _)
          intro y hy
          simp only [f1, mem_union, mem_filter, mem_univ, true_and] at hy ⊢
          by_contra hboth
          push Not at hboth
          exact hy (by rw [hboth.1, hboth.2, sub_self])
        rw [hcount_split, pow_succ 2 n, pow_succ 2 d]
        calc 2 ^ n * 2 ≤ #(univ.filter (fun y : BitString n ↦ f1 y ≠ 0)) * 2 ^ d * 2 :=
              Nat.mul_le_mul_right 2 hih
          _ ≤ (#(univ.filter (fun y : BitString n ↦ f (Fin.cons false y) ≠ 0)) +
               #(univ.filter (fun y : BitString n ↦ f (Fin.cons true y) ≠ 0))) *
              (2 ^ d * 2) := by
              rw [mul_assoc]
              exact Nat.mul_le_mul_right (2 ^ d * 2) hle_sum

end HammingBall

/-! ### Finite-degree Zariski closure and the Nie–Wang theorem -/

section DegreeClosure

variable (K : Type*) [Field K] {n : ℕ}

/-- The **degree-`D` polynomial closure** `cl_D(E)` of a set `E ⊆ {0, 1}^n` over a field `K`: the
set of Boolean points at which every function `Q ∈ lowDegree K (Fin n) D` vanishing throughout `E`
must also vanish. -/
noncomputable def degreeClosure (D : ℕ) (E : Finset (BitString n)) : Finset (BitString n) := by
  classical
  exact univ.filter (fun a : BitString n ↦
    ∀ Q ∈ lowDegree K (Fin n) D, (∀ x ∈ E, Q x = 0) → Q a = 0)

variable {K}

theorem mem_degreeClosure_iff {D : ℕ} {E : Finset (BitString n)} {a : BitString n} :
    a ∈ degreeClosure K D E ↔
      ∀ Q ∈ lowDegree K (Fin n) D, (∀ x ∈ E, Q x = 0) → Q a = 0 := by
  classical
  simp [degreeClosure]

/-- Membership in `degreeClosure K D E` characterized via multivariate polynomials of total degree
at most `D`. -/
theorem mem_degreeClosure_iff_mvPolynomial {D : ℕ} {E : Finset (BitString n)} {a : BitString n} :
    a ∈ degreeClosure K D E ↔
      ∀ Q : MvPolynomial (Fin n) K, Q.totalDegree ≤ D →
        (∀ x ∈ E, evalBitString Q x = 0) → evalBitString Q a = 0 := by
  rw [mem_degreeClosure_iff]
  refine ⟨fun h Q hQD hQE ↦ h (evalBitString Q) (evalBitString_mem_lowDegree Q hQD) hQE,
    fun h Q hQD hQE ↦ ?_⟩
  rcases exists_multilinear_poly_of_mem_lowDegree hQD with ⟨P, _, hPD, hPeq⟩
  rw [← hPeq]
  exact h P hPD fun x hx ↦ (congr_fun hPeq x).trans (hQE x hx)

theorem subset_degreeClosure (D : ℕ) (E : Finset (BitString n)) :
    E ⊆ degreeClosure K D E :=
  fun a ha ↦ mem_degreeClosure_iff.mpr fun _ _ hQE ↦ hQE a ha

@[gcongr]
theorem degreeClosure_mono (D : ℕ) {E F : Finset (BitString n)} (hEF : E ⊆ F) :
    degreeClosure K D E ⊆ degreeClosure K D F :=
  fun _ ha ↦ mem_degreeClosure_iff.mpr fun Q hQD hQF ↦
    (mem_degreeClosure_iff.mp ha) Q hQD fun x hx ↦ hQF x (hEF hx)

theorem degreeClosure_antitone_degree {D₁ D₂ : ℕ} (hD : D₁ ≤ D₂) (E : Finset (BitString n)) :
    degreeClosure K D₂ E ⊆ degreeClosure K D₁ E :=
  fun _ ha ↦ mem_degreeClosure_iff.mpr fun Q hQD hQE ↦
    (mem_degreeClosure_iff.mp ha) Q (lowDegree_mono hD hQD) hQE

theorem exists_poly_of_notMem_degreeClosure {D : ℕ} {E : Finset (BitString n)}
    {a : BitString n} (ha : a ∉ degreeClosure K D E) :
    ∃ Q : MvPolynomial (Fin n) K, Q ∈ restrictDegree (Fin n) K 1 ∧ Q.totalDegree ≤ D ∧
      (∀ x ∈ E, evalBitString Q x = 0) ∧ evalBitString Q a ≠ 0 := by
  rw [mem_degreeClosure_iff] at ha
  push Not at ha
  rcases ha with ⟨f, hfD, hfE, hfa⟩
  rcases exists_multilinear_poly_of_mem_lowDegree hfD with ⟨Q, hQ1, hQD, hQeq⟩
  exact ⟨Q, hQ1, hQD, fun x hx ↦ (congr_fun hQeq x).trans (hfE x hx),
    by rwa [congr_fun hQeq a]⟩

-- Graded-lexicographic encoding `S ↦ #S * 2^n + ∑ i ∈ S, 2^i` on `Finset (Fin n)`.
private def finsetBitMask {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  ∑ i ∈ S, 2 ^ (i : ℕ)

private lemma sum_two_pow_lt (k : ℕ) : ∑ j ∈ range k, 2 ^ j < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, pow_succ]
      omega

private lemma finsetBitMask_lt {n : ℕ} (S : Finset (Fin n)) : finsetBitMask S < 2 ^ n := by
  calc ∑ i ∈ S, 2 ^ (i : ℕ)
      ≤ ∑ i : Fin n, 2 ^ (i : ℕ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ ↦ Nat.zero_le _
    _ = ∑ j ∈ range n, 2 ^ j := Fin.sum_univ_eq_sum_range (fun j ↦ 2 ^ j) n
    _ < 2 ^ n := sum_two_pow_lt n

private lemma finsetBitMask_injective {n : ℕ} :
    Function.Injective (finsetBitMask (n := n)) := by
  intro S T hST
  by_contra hne
  have hsd_ne : (symmDiff S T).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hemp
    exact hne (symmDiff_eq_bot.mp hemp)
  let m : Fin n := (symmDiff S T).max' hsd_ne
  have hm_mem : m ∈ symmDiff S T := max'_mem _ hsd_ne
  have hagree : ∀ i : Fin n, m < i → (i ∈ S ↔ i ∈ T) := by
    intro i hmi
    by_contra hiff
    have hi_sd : i ∈ symmDiff S T := by
      rw [mem_symmDiff]
      tauto
    exact not_le.mpr hmi (le_max' _ i hi_sd)
  have hlt_of : ∀ A B : Finset (Fin n), m ∈ B → m ∉ A →
      (∀ i : Fin n, m < i → (i ∈ A ↔ i ∈ B)) → finsetBitMask A < finsetBitMask B := by
    intro A B hmB hmA hAB
    have hhi : A.filter (fun i ↦ m < i) = B.filter (fun i ↦ m < i) := by
      ext i; simp only [mem_filter, and_congr_left_iff]; exact hAB i
    have hsplit : ∀ U : Finset (Fin n),
        finsetBitMask U = (∑ i ∈ U.filter (fun i ↦ i ≤ m), 2 ^ (i : ℕ)) +
          (∑ i ∈ U.filter (fun i ↦ m < i), 2 ^ (i : ℕ)) := fun U ↦ by
      rw [finsetBitMask, ← sum_filter_add_sum_filter_not U (fun i ↦ i ≤ m)]
      congr 2
      ext i; simp
    rw [hsplit A, hsplit B, hhi]
    refine Nat.add_lt_add_right ?_ _
    have hAlo : ∑ i ∈ A.filter (fun i ↦ i ≤ m), 2 ^ (i : ℕ) < 2 ^ (m : ℕ) := by
      calc ∑ i ∈ A.filter (fun i ↦ i ≤ m), 2 ^ (i : ℕ)
          = ∑ i ∈ A.filter (fun i ↦ i < m), 2 ^ (i : ℕ) := by
            congr 1; ext i; simp only [mem_filter]
            refine ⟨fun ⟨hiA, him⟩ ↦ ⟨hiA, lt_of_le_of_ne him fun heq ↦ hmA (heq ▸ hiA)⟩,
              fun ⟨hiA, him⟩ ↦ ⟨hiA, him.le⟩⟩
        _ ≤ ∑ j ∈ range (m : ℕ), 2 ^ j := by
            rw [← sum_image (g := fun i : Fin n ↦ (i : ℕ))
              (fun _ _ _ _ h ↦ Fin.ext h)]
            exact sum_le_sum_of_subset_of_nonneg
              (fun j hj ↦ by
                simp only [mem_image, mem_filter, mem_range] at hj ⊢
                rcases hj with ⟨i, ⟨_, him⟩, rfl⟩
                exact him)
              (fun _ _ _ ↦ Nat.zero_le _)
        _ < 2 ^ (m : ℕ) := sum_two_pow_lt (m : ℕ)
    have hBlo : 2 ^ (m : ℕ) ≤ ∑ i ∈ B.filter (fun i ↦ i ≤ m), 2 ^ (i : ℕ) :=
      single_le_sum (f := fun i : Fin n ↦ 2 ^ (i : ℕ)) (fun _ _ ↦ Nat.zero_le _)
        (mem_filter.mpr ⟨hmB, le_rfl⟩)
    exact lt_of_lt_of_le hAlo hBlo
  rw [mem_symmDiff] at hm_mem
  rcases hm_mem with ⟨hmS, hmT⟩ | ⟨hmT, hmS⟩
  · exact (hlt_of T S hmS hmT fun i hi ↦ (hagree i hi).symm).ne hST.symm
  · exact (hlt_of S T hmT hmS hagree).ne hST

private def glexKey {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  #S * 2 ^ n + finsetBitMask S

private lemma glexKey_lt_iff {n : ℕ} {S T : Finset (Fin n)} :
    glexKey S < glexKey T ↔ #S < #T ∨ (#S = #T ∧ finsetBitMask S < finsetBitMask T) := by
  have hS := finsetBitMask_lt S
  have hT := finsetBitMask_lt T
  simp only [glexKey]
  constructor
  · intro h
    rcases lt_trichotomy #S #T with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, by rw [heq] at h; omega⟩
    · exfalso
      have : (#T + 1) * 2 ^ n ≤ #S * 2 ^ n := Nat.mul_le_mul_right _ hgt
      linarith
  · rintro (hlt | ⟨heq, hmask⟩)
    · have : (#S + 1) * 2 ^ n ≤ #T * 2 ^ n := Nat.mul_le_mul_right _ hlt
      linarith
    · rw [heq]; omega

private lemma glexKey_injective {n : ℕ} : Function.Injective (glexKey (n := n)) := by
  intro S T hST
  have hS := finsetBitMask_lt S
  have hT := finsetBitMask_lt T
  have hcard : #S = #T := by
    have hdS : glexKey S / 2 ^ n = #S := by
      rw [glexKey, add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
        Nat.div_eq_of_lt hS, zero_add]
    have hdT : glexKey T / 2 ^ n = #T := by
      rw [glexKey, add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
        Nat.div_eq_of_lt hT, zero_add]
    rw [← hdS, hST, hdT]
  apply finsetBitMask_injective
  simp only [glexKey, hcard] at hST
  omega

private lemma glexKey_insert_lt {n : ℕ} {S T : Finset (Fin n)} {j : Fin n}
    (hlt : glexKey S < glexKey T) (hjT : j ∉ T) :
    glexKey (insert j S) < glexKey (insert j T) := by
  rw [glexKey_lt_iff] at hlt ⊢
  rw [card_insert_of_notMem hjT]
  rcases hlt with hcard | ⟨hcard, hmask⟩
  · left
    by_cases hjS : j ∈ S
    · rw [insert_eq_of_mem hjS]; omega
    · rw [card_insert_of_notMem hjS]; omega
  · by_cases hjS : j ∈ S
    · left; rw [insert_eq_of_mem hjS]; omega
    · right
      rw [card_insert_of_notMem hjS, hcard]
      refine ⟨rfl, ?_⟩
      rw [finsetBitMask, finsetBitMask, sum_insert hjS, sum_insert hjT]
      exact Nat.add_lt_add_left hmask _

private lemma glexKey_union_lt {n : ℕ} {R S T : Finset (Fin n)}
    (hlt : glexKey S < glexKey T) (hdisj : Disjoint R T) :
    glexKey (R ∪ S) < glexKey (R ∪ T) := by
  induction R using Finset.induction_on with
  | empty => simpa using hlt
  | insert j r hjr ih =>
      rcases disjoint_insert_left.mp hdisj with ⟨hjT, hrT⟩
      simp only [insert_union]
      refine glexKey_insert_lt (ih hrT) ?_
      simp [hjT, hjr]

end DegreeClosure

section NieWang

/-- **Nie–Wang finite-degree closure inequality on `{0, 1}^n`**
: for any field `K`, any `D : ℕ`, and any subset
`E ⊆ {0, 1}^n`,
`#(degreeClosure K D E) * ∑_{j = 0}^D n.choose j ≤ 2^n * #E`.
-/
theorem card_degreeClosure_mul_le (K : Type*) [Field K] {n : ℕ} (D : ℕ)
    (E : Finset (BitString n)) :
    #(degreeClosure K D E) * (∑ j ∈ range (D + 1), n.choose j) ≤ 2 ^ n * #E := by
  classical
  -- Step 1: Establish the multilinear monomial basis and graded-lex leading monomials.
  have hli : LinearIndependent K (Cslib.BitString.monomial K (ι := Fin n)) :=
    linearIndependent_monomial
  have hcard_eq : Fintype.card (Finset (Fin n)) =
      Module.finrank K (BitString n → K) := by
    simp [BitString, Fintype.card_finset, Fintype.card_pi]
  let B : Module.Basis (Finset (Fin n)) K (BitString n → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard_eq
  have hB_apply : ∀ S : Finset (Fin n), B S = Cslib.BitString.monomial K S := fun S ↦ by
    simp [B]
  let supp : (BitString n → K) → Finset (Finset (Fin n)) := fun f ↦ (B.repr f).support
  have hsupp_nonempty : ∀ {f : BitString n → K}, f ≠ 0 → (supp f).Nonempty := fun {f} hf ↦
    Finsupp.support_nonempty_iff.mpr fun h0 ↦ hf (B.repr.injective (by simpa using h0))
  let lm : ∀ (f : BitString n → K), f ≠ 0 → Finset (Fin n) := fun f hf ↦
    (mem_image.mp (max'_mem _ ((hsupp_nonempty hf).image glexKey))).choose
  have hlm_mem : ∀ {f : BitString n → K} (hf : f ≠ 0), lm f hf ∈ supp f := fun hf ↦
    (mem_image.mp (max'_mem _ ((hsupp_nonempty hf).image glexKey))).choose_spec.1
  have hlm_key : ∀ {f : BitString n → K} (hf : f ≠ 0),
      glexKey (lm f hf) = ((supp f).image glexKey).max' ((hsupp_nonempty hf).image _) :=
    fun hf ↦ (mem_image.mp (max'_mem _ ((hsupp_nonempty hf).image glexKey))).choose_spec.2
  have hlm_max : ∀ {f : BitString n → K} (hf : f ≠ 0) {S : Finset (Fin n)},
      S ∈ supp f → glexKey S ≤ glexKey (lm f hf) := fun {_} hf {_} hS ↦ by
    rw [hlm_key hf]
    exact le_max' _ _ (mem_image_of_mem glexKey hS)
  have hlm_lt_of_ne : ∀ {f : BitString n → K} (hf : f ≠ 0) {S : Finset (Fin n)},
      S ∈ supp f → S ≠ lm f hf → glexKey S < glexKey (lm f hf) := fun {_} hf {_} hS hne ↦
    lt_of_le_of_ne (hlm_max hf hS) fun heq ↦ hne (glexKey_injective heq)
  -- Leading monomial determines lowDegree membership and shifts cleanly under monomial products.
  have hmem_lowDeg_of_lm : ∀ {f : BitString n → K} (hf : f ≠ 0),
      #(lm f hf) ≤ D → f ∈ lowDegree K (Fin n) D := by
    intro f hf hcard
    rw [← B.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun S hS ↦ ?_
    rw [hB_apply]
    refine Submodule.smul_mem _ _ (monomial_mem_lowDegree ?_)
    have hle := hlm_max hf hS
    by_contra hgt
    push Not at hgt
    exact not_lt.mpr hle (glexKey_lt_iff.mpr (Or.inl (lt_of_le_of_lt hcard hgt)))
  have hmul_lm : ∀ {f : BitString n → K} (hf : f ≠ 0) {R : Finset (Fin n)},
      Disjoint R (lm f hf) →
      ∃ hg : Cslib.BitString.monomial K R * f ≠ 0,
        lm (Cslib.BitString.monomial K R * f) hg = R ∪ lm f hf := by
    intro f hf R hdisj
    have hexp : Cslib.BitString.monomial K R * f =
        ∑ S ∈ supp f, (B.repr f S) • B (R ∪ S) := by
      conv_lhs => rw [← B.linearCombination_repr f]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, mul_sum]
      refine sum_congr rfl fun S _ ↦ ?_
      rw [mul_smul_comm, hB_apply, hB_apply, Cslib.BitString.monomial_mul]
    have hcoeff_top : B.repr (Cslib.BitString.monomial K R * f) (R ∪ lm f hf) =
        B.repr f (lm f hf) := by
      have h1 : B.repr (Cslib.BitString.monomial K R * f) =
          ∑ S ∈ supp f, (B.repr f S) • Finsupp.single (R ∪ S) (1 : K) := by
        rw [hexp, map_sum]
        exact sum_congr rfl fun S _ ↦ by rw [map_smul, Module.Basis.repr_self]
      have hsum_at : ∀ (t : Finset (Finset (Fin n))) (g : Finset (Fin n) → (Finset (Fin n) →₀ K))
          (U : Finset (Fin n)), (∑ S ∈ t, g S) U = ∑ S ∈ t, g S U := fun t g U ↦ by
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s ha _ => simp [sum_insert ha]
      rw [h1, hsum_at, sum_eq_single (lm f hf)]
      · simp
      · intro S hS hne
        have hneU : R ∪ S ≠ R ∪ lm f hf := fun hunion ↦
          (glexKey_union_lt (hlm_lt_of_ne hf hS hne) hdisj).ne (congrArg glexKey hunion)
        simp [hneU]
      · intro hnot; exact absurd (hlm_mem hf) hnot
    have htop_ne : B.repr (Cslib.BitString.monomial K R * f) (R ∪ lm f hf) ≠ 0 := by
      rw [hcoeff_top]
      exact Finsupp.mem_support_iff.mp (hlm_mem hf)
    have hg : Cslib.BitString.monomial K R * f ≠ 0 := fun h0 ↦
      htop_ne (by simp [h0])
    refine ⟨hg, ?_⟩
    apply glexKey_injective
    apply le_antisymm
    · have hmem_g : lm (Cslib.BitString.monomial K R * f) hg ∈
          supp (Cslib.BitString.monomial K R * f) := hlm_mem hg
      have hne_c : B.repr (Cslib.BitString.monomial K R * f)
          (lm (Cslib.BitString.monomial K R * f) hg) ≠ 0 :=
        Finsupp.mem_support_iff.mp hmem_g
      have h1 : B.repr (Cslib.BitString.monomial K R * f) =
          ∑ S ∈ supp f, (B.repr f S) • Finsupp.single (R ∪ S) (1 : K) := by
        rw [hexp, map_sum]
        exact sum_congr rfl fun S _ ↦ by rw [map_smul, Module.Basis.repr_self]
      have hsum_at : ∀ (t : Finset (Finset (Fin n))) (g : Finset (Fin n) → (Finset (Fin n) →₀ K))
          (U : Finset (Fin n)), (∑ S ∈ t, g S) U = ∑ S ∈ t, g S U := fun t g U ↦ by
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s ha _ => simp [sum_insert ha]
      rw [h1, hsum_at] at hne_c
      obtain ⟨S, hS, hSne⟩ := exists_ne_zero_of_sum_ne_zero hne_c
      have heqU : R ∪ S = lm (Cslib.BitString.monomial K R * f) hg := by
        by_contra hneU
        simp [hneU] at hSne
      rw [← heqU]
      by_cases hSlm : S = lm f hf
      · rw [hSlm]
      · exact (glexKey_union_lt (hlm_lt_of_ne hf hS hSlm) hdisj).le
    · exact hlm_max hg (Finsupp.mem_support_iff.mpr htop_ne)
  -- Step 2: Initial-monomial set LM(I(A)) has cardinality finrank I(A) = 2^n - #A.
  let vanSub : Finset (BitString n) → Submodule K (BitString n → K) := fun A ↦
    { carrier := {f | ∀ x ∈ A, f x = 0}
      add_mem' := fun ha hb x hx ↦ by simp [ha x hx, hb x hx]
      zero_mem' := fun _ _ ↦ rfl
      smul_mem' := fun c _ ha x hx ↦ by simp [ha x hx] }
  let lmSet : Submodule K (BitString n → K) → Finset (Finset (Fin n)) := fun M ↦
    univ.filter (fun S ↦ ∃ f ∈ M, ∃ hf : f ≠ 0, lm f hf = S)
  have hcard_lmSet : ∀ M : Submodule K (BitString n → K), #(lmSet M) = Module.finrank K M := by
    intro M
    let pick : lmSet M → M := fun S ↦
      have h := (mem_filter.mp S.2).2
      ⟨h.choose, h.choose_spec.1⟩
    have hpick_ne : ∀ S : lmSet M, (pick S : BitString n → K) ≠ 0 := fun S ↦
      (mem_filter.mp S.2).2.choose_spec.2.1
    have hpick_lm : ∀ S : lmSet M, lm (pick S) (hpick_ne S) = S.1 := fun S ↦
      (mem_filter.mp S.2).2.choose_spec.2.2
    have hpick_li : LinearIndependent K pick := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hnot
      push Not at hnot
      let active : Finset (lmSet M) := univ.filter (fun S ↦ c S ≠ 0)
      have hact_ne : active.Nonempty := by
        rcases hnot with ⟨S, hS⟩
        exact ⟨S, mem_filter.mpr ⟨mem_univ S, hS⟩⟩
      have himg_ne : (active.image (fun S : lmSet M ↦ glexKey S.1)).Nonempty := hact_ne.image _
      obtain ⟨Smax, hSmax_act, hSmax_key⟩ :=
        mem_image.mp (max'_mem _ himg_ne)
      have hval : (∑ S : lmSet M, c S • (pick S : BitString n → K)) = 0 := by
        have := congrArg Subtype.val hc
        simpa using this
      have hrepr0 : B.repr (∑ S ∈ active, c S • (pick S : BitString n → K)) Smax.1 = 0 := by
        have hsum_eq : ∑ S ∈ active, c S • (pick S : BitString n → K) =
            ∑ S : lmSet M, c S • (pick S : BitString n → K) := by
          refine sum_subset (subset_univ _) fun S _ hSnot ↦ ?_
          have hc0 : c S = 0 := by simpa [active] using hSnot
          simp [hc0]
        rw [hsum_eq, hval, map_zero, Finsupp.zero_apply]
      have hrepr_sum : B.repr (∑ S ∈ active, c S • (pick S : BitString n → K)) Smax.1 =
          ∑ S ∈ active, (B.repr (c S • (pick S : BitString n → K))) Smax.1 := by
        rw [map_sum]
        induction active using Finset.induction_on with
        | empty => simp
        | insert a s ha _ => simp [sum_insert ha]
      rw [hrepr_sum, sum_eq_single Smax] at hrepr0
      · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hrepr0
        rcases mul_eq_zero.mp hrepr0 with hc0 | hrep0
        · exact (mem_filter.mp hSmax_act).2 hc0
        · have hmem := hlm_mem (hpick_ne Smax)
          rw [hpick_lm Smax] at hmem
          exact (Finsupp.mem_support_iff.mp hmem) hrep0
      · intro S hS hne
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        suffices B.repr (pick S) Smax.1 = 0 by rw [this, mul_zero]
        by_contra hnz
        have hle1 : glexKey Smax.1 ≤ glexKey S.1 := by
          have := hlm_max (hpick_ne S) (Finsupp.mem_support_iff.mpr hnz)
          rwa [hpick_lm S] at this
        have hle2 : glexKey S.1 ≤ glexKey Smax.1 := by
          rw [hSmax_key]
          exact le_max' _ _ (mem_image_of_mem (fun T : lmSet M ↦ glexKey T.1) hS)
        exact hne (Subtype.ext (glexKey_injective (le_antisymm hle2 hle1)))
      · intro hnot; exact absurd hSmax_act hnot
    have hpick_span : ⊤ ≤ Submodule.span K (Set.range pick) := by
      rintro ⟨f, hfM⟩ _
      suffices ∀ k : ℕ, ∀ g : BitString n → K, (hgM : g ∈ M) →
          (∀ hg : g ≠ 0, glexKey (lm g hg) < k) →
          (⟨g, hgM⟩ : M) ∈ Submodule.span K (Set.range pick) by
        by_cases hf0 : f = 0
        · exact this 0 f hfM fun h ↦ absurd hf0 h
        · exact this (glexKey (lm f hf0) + 1) f hfM fun _ ↦ Nat.lt_succ_self _
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro g hgM hgk
        by_cases hg0 : g = 0
        · subst hg0; exact Submodule.zero_mem _
        · let S0 : Finset (Fin n) := lm g hg0
          have hS0_mem : S0 ∈ lmSet M :=
            mem_filter.mpr ⟨mem_univ _, g, hgM, hg0, rfl⟩
          let p0 : M := pick ⟨S0, hS0_mem⟩
          have hp0_ne : (p0 : BitString n → K) ≠ 0 := hpick_ne ⟨S0, hS0_mem⟩
          have hp0_lm : lm p0 hp0_ne = S0 := hpick_lm ⟨S0, hS0_mem⟩
          have hp0_coeff : B.repr (p0 : BitString n → K) S0 ≠ 0 := by
            have hm := hlm_mem hp0_ne
            rw [hp0_lm] at hm
            exact Finsupp.mem_support_iff.mp hm
          let α : K := B.repr g S0 / B.repr (p0 : BitString n → K) S0
          let g' : BitString n → K := g - α • (p0 : BitString n → K)
          have hg'M : g' ∈ M := M.sub_mem hgM (M.smul_mem α p0.2)
          have hg'_in : (⟨g', hg'M⟩ : M) ∈ Submodule.span K (Set.range pick) := by
            refine ih (glexKey S0) (hgk hg0) g' hg'M fun hg'0 ↦ ?_
            have hmem' : lm g' hg'0 ∈ supp g' := hlm_mem hg'0
            have hnz' : B.repr g' (lm g' hg'0) ≠ 0 := Finsupp.mem_support_iff.mp hmem'
            have hne_S0 : lm g' hg'0 ≠ S0 := by
              intro heq
              apply hnz'
              simp [g', heq, α, div_mul_cancel₀ _ hp0_coeff]
            have hsub_nz : B.repr g (lm g' hg'0) ≠ 0 ∨
                B.repr (p0 : BitString n → K) (lm g' hg'0) ≠ 0 := by
              by_contra hboth
              push Not at hboth
              apply hnz'
              simp [g', hboth.1, hboth.2]
            rcases hsub_nz with h1 | h2
            · exact hlm_lt_of_ne hg0 (Finsupp.mem_support_iff.mpr h1) hne_S0
            · have := hlm_lt_of_ne hp0_ne (Finsupp.mem_support_iff.mpr h2)
                (hp0_lm.symm ▸ hne_S0)
              rwa [hp0_lm] at this
          have hdecomp : (⟨g, hgM⟩ : M) = ⟨g', hg'M⟩ + α • p0 := by
            ext x; simp [g']
          rw [hdecomp]
          exact Submodule.add_mem _ hg'_in
            (Submodule.smul_mem _ α (Submodule.subset_span ⟨⟨S0, hS0_mem⟩, rfl⟩))
    let BM : Module.Basis (lmSet M) K M := Module.Basis.mk hpick_li hpick_span
    simpa using (Module.finrank_eq_card_basis BM).symm
  have hcard_van : ∀ A : Finset (BitString n), #(lmSet (vanSub A)) + #A = 2 ^ n := by
    intro A
    rw [hcard_lmSet (vanSub A)]
    let res : (BitString n → K) →ₗ[K] (A → K) :=
      { toFun := fun f x ↦ f x.1
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hker : LinearMap.ker res = vanSub A := by
      ext f
      simp only [LinearMap.mem_ker, funext_iff, Subtype.forall]
      exact Iff.rfl
    have hsurj : Function.Surjective res := by
      intro g
      refine ⟨fun x ↦ if hx : x ∈ A then g ⟨x, hx⟩ else 0, ?_⟩
      ext ⟨x, hx⟩
      simp [res, hx]
    have hrk := LinearMap.finrank_range_add_finrank_ker res
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrk
    have hfinA : Module.finrank K (A → K) = #A := by simp
    have hfinAll : Module.finrank K (BitString n → K) = 2 ^ n := by
      simp [BitString, Fintype.card_pi]
    omega
  -- Step 3: Build the lower set W complementary to the upset generated by degree-≤-D elements of
  -- LM(I(E)), and apply Harris–Kleitman to W and the Hamming ball B_D = {S | #S ≤ D}.
  let Cset : Finset (BitString n) := degreeClosure K D E
  let U0 : Finset (Finset (Fin n)) := (lmSet (vanSub E)).filter (fun S ↦ #S ≤ D)
  let V : Finset (Finset (Fin n)) := univ.filter (fun T ↦ ∃ S ∈ U0, S ⊆ T)
  let W : Finset (Finset (Fin n)) := univ \ V
  let BD : Finset (Finset (Fin n)) := univ.filter (fun T ↦ #T ≤ D)
  have hW_lower : IsLowerSet (W : Set (Finset (Fin n))) := by
    intro T₁ T₂ hT₂₁ hT₁
    have h1 : T₁ ∉ V := by simpa [W] using hT₁
    have h2 : T₂ ∉ V := by
      intro h2V
      apply h1
      simp only [V, mem_filter, mem_univ, true_and] at h2V ⊢
      rcases h2V with ⟨S, hSU, hST₂⟩
      exact ⟨S, hSU, hST₂.trans hT₂₁⟩
    simpa [W] using h2
  have hBD_lower : IsLowerSet (BD : Set (Finset (Fin n))) := by
    intro T₁ T₂ hT₂₁ hT₁
    have h1 : #T₁ ≤ D := by simpa [BD] using hT₁
    have h2 : #T₂ ≤ D := (card_le_card hT₂₁).trans h1
    simpa [BD] using h2
  have hV_sub_C : V ⊆ lmSet (vanSub Cset) := by
    intro T hT
    simp only [V, U0, lmSet, mem_filter, mem_univ, true_and] at hT ⊢
    rcases hT with ⟨S, ⟨⟨f, hfE, hf0, hflm⟩, hSD⟩, hST⟩
    have hfD : f ∈ lowDegree K (Fin n) D := hmem_lowDeg_of_lm hf0 (hflm.symm ▸ hSD)
    have hfC : ∀ x ∈ Cset, f x = 0 := fun x hx ↦
      (mem_degreeClosure_iff.mp hx) f hfD hfE
    have hdisj : Disjoint (T \ S) (lm f hf0) := by
      rw [hflm]; exact disjoint_sdiff_self_left
    rcases hmul_lm hf0 hdisj with ⟨hg0, hglm⟩
    refine ⟨Cslib.BitString.monomial K (T \ S) * f, fun x hx ↦ ?_, hg0, ?_⟩
    · simp [hfC x hx]
    · rw [hglm, hflm, sdiff_union_of_subset hST]
  have hC_le_W : #Cset ≤ #W := by
    have hVW : #V + #W = 2 ^ n := by
      have := card_sdiff_add_card_eq_card (subset_univ V)
      simp only [card_univ, Fintype.card_finset, Fintype.card_fin] at this
      change #W + #V = 2 ^ n at this
      omega
    have hVC : #V ≤ #(lmSet (vanSub Cset)) := card_le_card hV_sub_C
    have hCC := hcard_van Cset
    omega
  have hW_inter_le_E : #(W ∩ BD) ≤ #E := by
    have hsub : W ∩ BD ⊆ univ \ lmSet (vanSub E) := by
      intro T hT
      simp only [W, BD, V, U0, mem_inter, mem_sdiff, mem_filter, mem_univ, true_and] at hT ⊢
      intro hTE
      exact hT.1 ⟨T, ⟨hTE, hT.2⟩, Subset.rfl⟩
    have hcompl : #(univ \ lmSet (vanSub E)) = #E := by
      have hs := card_sdiff_add_card_eq_card (subset_univ (lmSet (vanSub E)))
      simp only [card_univ, Fintype.card_finset, Fintype.card_fin] at hs
      have hEE := hcard_van E
      omega
    exact hcompl ▸ card_le_card hsub
  have hBD_card : #BD = ∑ j ∈ range (D + 1), n.choose j := by
    have hpart : BD = (range (D + 1)).biUnion (fun j ↦ (univ : Finset (Fin n)).powersetCard j) := by
      ext S
      simp [BD, mem_powersetCard]
    rw [hpart, card_biUnion]
    · refine sum_congr rfl fun j _ ↦ ?_
      simp [card_powersetCard]
    · intro i _ j _ hij
      exact Finset.disjoint_left.mpr fun S hi hj ↦
        hij ((mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2)
  have hhk := hW_lower.le_card_inter_finset hBD_lower
  simp only [Fintype.card_fin] at hhk
  calc #Cset * (∑ j ∈ range (D + 1), n.choose j)
      ≤ #W * #BD := by rw [← hBD_card]; exact Nat.mul_le_mul_right _ hC_le_W
    _ ≤ 2 ^ n * #(W ∩ BD) := hhk
    _ ≤ 2 ^ n * #E := Nat.mul_le_mul_left _ hW_inter_le_E

/-- Real-ratio form of the **Nie–Wang theorem**: for any field `K`, subset `E ⊆ {0, 1}^n`, and
degree `D : ℕ`,
`#(degreeClosure K D E) / 2^n ≤ #E / ∑_{j = 0}^D n.choose j`. -/
theorem card_degreeClosure_div_le (K : Type*) [Field K] {n : ℕ} (D : ℕ)
    (E : Finset (BitString n)) :
    (#(degreeClosure K D E) : ℝ) / (2 : ℝ) ^ n ≤
      (#E : ℝ) / (∑ j ∈ range (D + 1), (n.choose j : ℝ)) := by
  have hN_pos_nat : 0 < ∑ j ∈ range (D + 1), n.choose j :=
    lt_of_lt_of_le (by simp : 0 < n.choose 0)
      (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr (Nat.succ_pos D)))
  have hN_pos : (0 : ℝ) < ∑ j ∈ range (D + 1), (n.choose j : ℝ) := by
    exact_mod_cast hN_pos_nat
  rw [div_le_div_iff₀ (by positivity) hN_pos, ← Nat.cast_sum, mul_comm (#E : ℝ)]
  exact_mod_cast card_degreeClosure_mul_le K D E

end NieWang

end CslibFrontier.BooleanAnalysis
