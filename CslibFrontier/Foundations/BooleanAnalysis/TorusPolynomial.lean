/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Torus Polynomial Approximation of Boolean Functions and Linear-Programming Duality

A real multivariate polynomial `P ∈ ℝ[X₁, …, Xₙ]` is a torus polynomial that `ε`-approximates a
Boolean function `f : {0, 1}ⁿ → {0, 1}` if there exists an integer function `Z : {0, 1}ⁿ → ℤ` such
that `|P(a) - f(a) / 2 - Z(a)| ≤ ε` for every Boolean input `a ∈ {0, 1}ⁿ`, meaning that `P(a)`
approximates `f(a) / 2` in the additive torus `ℝ / ℤ`. The minimum total degree of such a
polynomial is the torus approximation degree `torusDegree ε f`, and restricting `P` to symmetric
polynomials gives the symmetric torus approximation degree `symTorusDegree ε f`.

This module develops the algebraic and linear-programming foundations of asymmetric and symmetric
torus polynomial approximations:

1. Multilinear and low-degree characterizations on the Boolean cube, attainment, antitonicity in
   `ε`, the exact upper bound `≤ n`, binomial-basis representation of symmetric polynomials via
   Hamming-layer symmetrization, uniqueness of the integer-part witness `Z` for `ε < 1 / 2`, and
   inductive normalization of `Z` to vanish on inputs of Hamming weight at most `d`.
2. Linear-programming duality characterizations via Farkas' lemma for both asymmetric torus degree
   in terms of the subset-inclusion matrix `inclusionMatrix n d` and symmetric torus degree in
   terms of the binomial matrix `binomialMatrix n d`, together with the odd-parity short integer
   nullspace witness criterion.

## Main definitions

* `CslibFrontier.TorusPolynomial.setToBitString`, `CslibFrontier.TorusPolynomial.bitStringToSet`,
  `CslibFrontier.TorusPolynomial.finsetEquivBitString`: canonical equivalence between
  `Finset (Fin n)` and `Cslib.BitString n`.
* `CslibFrontier.TorusPolynomial.evalBool`: evaluation of `P : MvPolynomial (Fin n) ℝ` on a bit
  string.
* `CslibFrontier.TorusPolynomial.IsTorusApprox`,
  `CslibFrontier.TorusPolynomial.IsSymTorusApprox`: asymmetric and symmetric `ε`-torus polynomial
  approximation predicates.
* `CslibFrontier.TorusPolynomial.torusDegree`, `CslibFrontier.TorusPolynomial.symTorusDegree`:
  minimum total degree of an asymmetric or symmetric `ε`-torus polynomial approximating `f`.
* `CslibFrontier.TorusPolynomial.inclusionMatrix`: the `{S | #S ≤ d} × Finset (Fin n)`
  set-inclusion matrix with entries `1_{S ⊆ T}`.
* `CslibFrontier.TorusPolynomial.binomialMatrix`: the `Fin (d + 1) × Fin (n + 1)` binomial matrix
  with entries `Nat.choose i j`.

## Main results

* `CslibFrontier.TorusPolynomial.exists_isTorusApprox_zero_lowWeight`: normalization eliminating
  the integer part `Z(a)` on all inputs of Hamming weight at most `d`.
* `CslibFrontier.TorusPolynomial.lt_torusDegree_iff`: LP-duality characterization of
  `d < torusDegree`.
* `CslibFrontier.TorusPolynomial.lt_symTorusDegree_iff`: LP-duality characterization of
  `d < symTorusDegree` for symmetric Boolean functions.
* `CslibFrontier.TorusPolynomial.lt_torusDegree_of_odd_int_ker`,
  `CslibFrontier.TorusPolynomial.lt_symTorusDegree_of_odd_int_ker`: odd-parity short integer
  nullspace witness criteria for torus degree lower bounds.
-/

public section

namespace CslibFrontier.TorusPolynomial

open Finset Cslib Cslib.BitString

section Basic

variable {n : ℕ}

/-- Canonical conversion from a subset `S : Finset (Fin n)` to its indicator bit string in
`{0, 1}ⁿ`. -/
@[expose]
def setToBitString (S : Finset (Fin n)) : BitString n :=
  fun i ↦ decide (i ∈ S)

/-- Canonical conversion from a bit string `a : BitString n` to its support `Finset (Fin n)`. -/
@[expose]
def bitStringToSet (a : BitString n) : Finset (Fin n) :=
  univ.filter fun i ↦ a i = true

/-- Canonical bijection between `Finset (Fin n)` and `BitString n`. -/
def finsetEquivBitString (n : ℕ) : Finset (Fin n) ≃ BitString n where
  toFun := setToBitString
  invFun := bitStringToSet
  left_inv S := by ext i; simp [setToBitString, bitStringToSet]
  right_inv a := by funext i; simp [setToBitString, bitStringToSet]

/-- Applying `finsetEquivBitString n` computes `setToBitString`. -/
@[simp]
theorem finsetEquivBitString_apply (S : Finset (Fin n)) :
    finsetEquivBitString n S = setToBitString S := by
  rfl

/-- Applying `(finsetEquivBitString n).symm` computes `bitStringToSet`. -/
@[simp]
theorem finsetEquivBitString_symm_apply (a : BitString n) :
    (finsetEquivBitString n).symm a = bitStringToSet a := by
  rfl

/-- The support of `setToBitString S` recovers `S`. -/
@[simp]
theorem bitStringToSet_setToBitString (S : Finset (Fin n)) :
    bitStringToSet (setToBitString S) = S :=
  (finsetEquivBitString n).left_inv S

/-- The indicator bit string of `bitStringToSet a` recovers `a`. -/
@[simp]
theorem setToBitString_bitStringToSet (a : BitString n) :
    setToBitString (bitStringToSet a) = a :=
  (finsetEquivBitString n).right_inv a

/-- The Hamming weight of `setToBitString S` equals `#S`. -/
@[simp]
theorem weight_setToBitString (S : Finset (Fin n)) :
    weight (setToBitString S) = #S := by
  change #(bitStringToSet (setToBitString S)) = #S
  rw [bitStringToSet_setToBitString]

/-- The cardinality of `bitStringToSet a` equals the Hamming weight of `a`. -/
@[simp]
theorem card_bitStringToSet (a : BitString n) :
    #(bitStringToSet a) = weight a := by
  rfl

/-- Coordinate `i` of `setToBitString S` is `true` iff `i ∈ S`. -/
theorem setToBitString_eq_true_iff (S : Finset (Fin n)) (i : Fin n) :
    setToBitString S i = true ↔ i ∈ S := by
  simp [setToBitString]

/-- Evaluation of a real multivariate polynomial `P : MvPolynomial (Fin n) ℝ` at a Boolean point
`a : BitString n`, mapping `false ↦ 0` and `true ↦ 1`. -/
@[expose]
noncomputable def evalBool (P : MvPolynomial (Fin n) ℝ) (a : BitString n) : ℝ :=
  MvPolynomial.eval (fun i ↦ bitVal ℝ (a i)) P

/-- `evalBool` preserves addition. -/
@[simp]
theorem evalBool_add (P Q : MvPolynomial (Fin n) ℝ) (a : BitString n) :
    evalBool (P + Q) a = evalBool P a + evalBool Q a :=
  map_add _ P Q

/-- `evalBool` preserves multiplication. -/
@[simp]
theorem evalBool_mul (P Q : MvPolynomial (Fin n) ℝ) (a : BitString n) :
    evalBool (P * Q) a = evalBool P a * evalBool Q a :=
  map_mul _ P Q

/-- `evalBool` preserves finite sums. -/
theorem evalBool_sum {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n) ℝ)
    (a : BitString n) :
    evalBool (∑ i ∈ s, g i) a = ∑ i ∈ s, evalBool (g i) a :=
  map_sum (MvPolynomial.eval fun i ↦ bitVal ℝ (a i)) g s

/-- `evalBool` preserves subtraction. -/
@[simp]
theorem evalBool_sub (P Q : MvPolynomial (Fin n) ℝ) (a : BitString n) :
    evalBool (P - Q) a = evalBool P a - evalBool Q a :=
  map_sub _ P Q

/-- `evalBool` preserves negation. -/
@[simp]
theorem evalBool_neg (P : MvPolynomial (Fin n) ℝ) (a : BitString n) :
    evalBool (-P) a = -evalBool P a :=
  map_neg _ P

/-- `evalBool` evaluates a constant polynomial to its constant value. -/
@[simp]
theorem evalBool_C (c : ℝ) (a : BitString n) :
    evalBool (MvPolynomial.C c) a = c :=
  MvPolynomial.eval_C c

/-- `evalBool` evaluates variable `X i` to `bitVal ℝ (a i)`. -/
@[simp]
theorem evalBool_X (i : Fin n) (a : BitString n) :
    evalBool (MvPolynomial.X i) a = bitVal ℝ (a i) :=
  MvPolynomial.eval_X i

private lemma totalDegree_sum_le {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hg : ∀ i ∈ s, (g i).totalDegree ≤ d) :
    (∑ i ∈ s, g i).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [sum_insert hi]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (hg i (mem_insert_self i t)) (ih fun j hj ↦ hg j (mem_insert_of_mem hj)))

private lemma poly_eval_sum {ι : Type*} (s : Finset ι) (g : ι → Polynomial ℝ) (x : ℝ) :
    (∑ i ∈ s, g i).eval x = ∑ i ∈ s, (g i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [sum_insert hi, sum_insert hi, Polynomial.eval_add, ih]

private lemma poly_natDegree_sum_le {ι : Type*} (s : Finset ι) (g : ι → Polynomial ℝ) {d : ℕ}
    (hg : ∀ i ∈ s, (g i).natDegree ≤ d) :
    (∑ i ∈ s, g i).natDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [sum_insert hi]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (hg i (mem_insert_self i t)) (ih fun j hj ↦ hg j (mem_insert_of_mem hj)))

/-- Multilinear monomial `∏ i ∈ S, X i` corresponding to a subset `S : Finset (Fin n)`. -/
noncomputable def multilinearMonomial (S : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ S, MvPolynomial.X i

/-- The multilinear monomial of `S` has total degree at most `#S`. -/
theorem totalDegree_multilinearMonomial_le (S : Finset (Fin n)) :
    (multilinearMonomial S).totalDegree ≤ #S := by
  classical
  unfold multilinearMonomial
  induction S using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
      rw [prod_insert hi, card_insert_of_notMem hi]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X]
      omega

/-- Evaluating `multilinearMonomial S` at `setToBitString T` yields the subset indicator
`1_{S ⊆ T}`. -/
theorem evalBool_multilinearMonomial_set (S T : Finset (Fin n)) :
    evalBool (multilinearMonomial S) (setToBitString T) = if S ⊆ T then 1 else 0 := by
  simp only [evalBool, multilinearMonomial, map_prod, MvPolynomial.eval_X, setToBitString]
  split_ifs with h
  · exact Finset.prod_eq_one fun i hi ↦ by simp [h hi, bitVal]
  · obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hiS (by simp [hiT, bitVal])

/-- Evaluating `multilinearMonomial S` at a bit string `a` matches `Cslib.BitString.monomial`. -/
theorem evalBool_multilinearMonomial (S : Finset (Fin n)) (a : BitString n) :
    evalBool (multilinearMonomial S) a = BitString.monomial ℝ S a := by
  simp [evalBool, multilinearMonomial, BitString.monomial]

private lemma aeval_bitVal_eq_evalBool (P : MvPolynomial (Fin n) ℝ) (a : BitString n) :
    (MvPolynomial.aeval (fun (i : Fin n) (x : BitString n) ↦ bitVal ℝ (x i)) P) a =
      evalBool P a := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [evalBool]
  | add p q hp hq => simp [evalBool, hp, hq]
  | mul_X p i hp => simp [evalBool, hp]

/-- A function `p : BitString n → ℝ` lies in `lowDegree ℝ (Fin n) d` iff it equals `evalBool P` for
some polynomial `P : MvPolynomial (Fin n) ℝ` of total degree at most `d`. -/
theorem mem_lowDegree_iff_exists_mvPolynomial {d : ℕ} {p : BitString n → ℝ} :
    p ∈ lowDegree ℝ (Fin n) d ↔
      ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧ evalBool P = p := by
  rw [lowDegree_eq_map_restrictTotalDegree, Submodule.mem_map]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mp hP,
      funext fun a ↦ (aeval_bitVal_eq_evalBool P a).symm⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP,
      funext fun a ↦ aeval_bitVal_eq_evalBool P a⟩

/-- A function `p` lies in `lowDegree ℝ (Fin n) d` iff it is a linear combination of subset
indicators over subsets of cardinality at most `d`. -/
theorem mem_lowDegree_iff_exists_coeffs (d : ℕ) (p : BitString n → ℝ) :
    p ∈ lowDegree ℝ (Fin n) d ↔
      ∃ α : {S : Finset (Fin n) // #S ≤ d} → ℝ,
        ∀ T : Finset (Fin n),
          p (setToBitString T) = ∑ S : {S : Finset (Fin n) // #S ≤ d},
            α S * (if S.1 ⊆ T then 1 else 0) := by
  constructor
  · intro hp
    induction hp using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨S₀, hS₀, rfl⟩ := hg
        refine ⟨fun S ↦ if S.1 = S₀ then 1 else 0, fun T ↦ ?_⟩
        have hmem : (⟨S₀, hS₀⟩ : {S : Finset (Fin n) // #S ≤ d}) ∈ univ := mem_univ _
        rw [Finset.sum_eq_single ⟨S₀, hS₀⟩]
        · simp [← evalBool_multilinearMonomial, evalBool_multilinearMonomial_set]
        · rintro ⟨S, hS⟩ _ hne
          have hne' : S ≠ S₀ := fun h ↦ hne (Subtype.ext h)
          simp [hne']
        · exact fun h ↦ absurd hmem h
    | zero => exact ⟨0, fun _ ↦ by simp⟩
    | add f g _ _ hf hg =>
        obtain ⟨α, hα⟩ := hf
        obtain ⟨β, hβ⟩ := hg
        refine ⟨α + β, fun T ↦ ?_⟩
        simp only [Pi.add_apply, hα T, hβ T, ← Finset.sum_add_distrib, add_mul]
    | smul c f _ hf =>
        obtain ⟨α, hα⟩ := hf
        refine ⟨c • α, fun T ↦ ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, hα T, Finset.mul_sum, mul_assoc]
  · rintro ⟨α, hα⟩
    have heq : p = ∑ S : {S : Finset (Fin n) // #S ≤ d}, α S • BitString.monomial ℝ S.1 := by
      funext a
      rw [← setToBitString_bitStringToSet a]
      set T := bitStringToSet a
      rw [hα T]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        ← evalBool_multilinearMonomial, evalBool_multilinearMonomial_set]
    rw [heq]
    exact Submodule.sum_mem _ fun S _ ↦ Submodule.smul_mem _ _ (monomial_mem_lowDegree S.2)

/-- A polynomial `P ∈ ℝ[X₁, …, Xₙ]` is a torus polynomial that `ε`-approximates a Boolean function
`f : {0, 1}ⁿ → {0, 1}` if there exists an integer function `Z : {0, 1}ⁿ → ℤ` such that
`|P(a) - f(a) / 2 - Z(a)| ≤ ε` for every `a ∈ {0, 1}ⁿ`. -/
@[expose]
def IsTorusApprox (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) (f : BooleanFunction n) : Prop :=
  ∃ Z : BitString n → ℤ, ∀ a : BitString n,
    |evalBool P a - bitVal ℝ (f a) / 2 - (Z a : ℝ)| ≤ ε

/-- A polynomial `P ∈ ℝ[X₁, …, Xₙ]` is a symmetric torus polynomial that `ε`-approximates `f` if
`P` is invariant under variable permutations and `ε`-approximates `f` on the torus. -/
@[expose]
def IsSymTorusApprox (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) (f : BooleanFunction n) : Prop :=
  P.IsSymmetric ∧ IsTorusApprox P ε f

/-- The torus approximation degree `tdeg_ε(f)`: the minimum total degree of a real multivariate
polynomial that `ε`-approximates `f` on the torus. -/
noncomputable def torusDegree (ε : ℝ) (f : BooleanFunction n) : ℕ :=
  sInf {d : ℕ | ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧ IsTorusApprox P ε f}

/-- The symmetric torus approximation degree of `f`: the minimum total degree of a symmetric real
multivariate polynomial that `ε`-approximates `f` on the torus. -/
noncomputable def symTorusDegree (ε : ℝ) (f : BooleanFunction n) : ℕ :=
  sInf {d : ℕ | ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧ IsSymTorusApprox P ε f}

/-- Exact degree-`≤ n` torus approximation exists for every Boolean function when `0 ≤ ε`. -/
theorem exists_isTorusApprox_card {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ n ∧ IsTorusApprox P ε f := by
  have hmem : (fun a : BitString n ↦ bitVal ℝ (f a) / 2) ∈ lowDegree ℝ (Fin n) n := by
    simpa using mem_lowDegree_self (R := ℝ) (fun a : BitString n ↦ bitVal ℝ (f a) / 2)
  obtain ⟨P, hdeg, hev⟩ := mem_lowDegree_iff_exists_mvPolynomial.mp hmem
  refine ⟨P, hdeg, 0, fun a ↦ ?_⟩
  have ha := congrFun hev a
  simp [ha, hε]

/-- Any degree-`≤ d` torus `ε`-approximation of `f` bounds `torusDegree ε f` by `d`. -/
theorem torusDegree_le_of_isTorusApprox {P : MvPolynomial (Fin n) ℝ} {d : ℕ} {ε : ℝ}
    {f : BooleanFunction n} (hdeg : P.totalDegree ≤ d) (hP : IsTorusApprox P ε f) :
    torusDegree ε f ≤ d :=
  Nat.sInf_le ⟨P, hdeg, hP⟩

/-- A low-degree cube function approximating `f / 2` modulo `ℤ` within `ε` bounds
`torusDegree ε f`. -/
theorem torusDegree_le_of_mem_lowDegree {p : BitString n → ℝ} {d : ℕ} {ε : ℝ}
    {f : BooleanFunction n} (hp : p ∈ lowDegree ℝ (Fin n) d)
    (happrox : ∀ a : BitString n, ∃ z : ℤ, |p a - bitVal ℝ (f a) / 2 - (z : ℝ)| ≤ ε) :
    torusDegree ε f ≤ d := by
  obtain ⟨P, hdeg, rfl⟩ := mem_lowDegree_iff_exists_mvPolynomial.mp hp
  choose Z hZ using happrox
  exact torusDegree_le_of_isTorusApprox hdeg ⟨Z, hZ⟩

/-- For `0 ≤ ε`, the torus approximation degree is attained. -/
theorem exists_isTorusApprox_torusDegree {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ torusDegree ε f ∧ IsTorusApprox P ε f :=
  Nat.sInf_mem
    (s := {d : ℕ | ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧ IsTorusApprox P ε f})
    ⟨n, exists_isTorusApprox_card hε f⟩

/-- For `0 ≤ ε`, every `n`-variable Boolean function has `torusDegree ε f ≤ n`. -/
theorem torusDegree_le_card {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    torusDegree ε f ≤ n := by
  obtain ⟨P, hdeg, hP⟩ := exists_isTorusApprox_card hε f
  exact torusDegree_le_of_isTorusApprox hdeg hP

/-- Monotonicity of `IsTorusApprox` in the error parameter `ε`. -/
theorem IsTorusApprox.mono {P : MvPolynomial (Fin n) ℝ} {ε δ : ℝ} {f : BooleanFunction n}
    (hP : IsTorusApprox P ε f) (hεδ : ε ≤ δ) : IsTorusApprox P δ f := by
  obtain ⟨Z, hZ⟩ := hP
  exact ⟨Z, fun a ↦ (hZ a).trans hεδ⟩

/-- `torusDegree ε f` is antitone in `ε` on `[0, ∞)`. -/
theorem torusDegree_antitone {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ) (f : BooleanFunction n) :
    torusDegree δ f ≤ torusDegree ε f := by
  obtain ⟨P, hdeg, hP⟩ := exists_isTorusApprox_torusDegree hε f
  exact torusDegree_le_of_isTorusApprox hdeg (hP.mono hεδ)

/-- When `ε < 1 / 2`, the integer part `Z(a)` witnessing `|P(a) - f(a) / 2 - Z(a)| ≤ ε` is unique
at every Boolean input `a`. -/
theorem int_part_unique {P : MvPolynomial (Fin n) ℝ} {ε : ℝ} (hε : ε < 1 / 2)
    {f : BooleanFunction n} {Z₁ Z₂ : BitString n → ℤ}
    (h₁ : ∀ a, |evalBool P a - bitVal ℝ (f a) / 2 - (Z₁ a : ℝ)| ≤ ε)
    (h₂ : ∀ a, |evalBool P a - bitVal ℝ (f a) / 2 - (Z₂ a : ℝ)| ≤ ε) :
    Z₁ = Z₂ := by
  funext a
  have hdiff : |((Z₁ a - Z₂ a : ℤ) : ℝ)| < 1 := by
    push_cast
    have ha₁ := h₁ a
    have ha₂ := h₂ a
    calc |(Z₁ a : ℝ) - (Z₂ a : ℝ)|
        = |(evalBool P a - bitVal ℝ (f a) / 2 - (Z₂ a : ℝ)) -
            (evalBool P a - bitVal ℝ (f a) / 2 - (Z₁ a : ℝ))| := by ring_nf
      _ ≤ |evalBool P a - bitVal ℝ (f a) / 2 - (Z₂ a : ℝ)| +
            |evalBool P a - bitVal ℝ (f a) / 2 - (Z₁ a : ℝ)| := abs_sub _ _
      _ ≤ ε + ε := add_le_add ha₂ ha₁
      _ < 1 := by linarith
  have hz : |Z₁ a - Z₂ a| < 1 := by exact_mod_cast hdiff
  rw [abs_lt] at hz
  omega

/-- Converting a univariate polynomial `q : ℝ[X]` into the symmetric multivariate polynomial
`q(∑ i, X i)`. -/
noncomputable def symPolyOfUnivariate (n : ℕ) (q : Polynomial ℝ) : MvPolynomial (Fin n) ℝ :=
  Polynomial.aeval (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) q

/-- `symPolyOfUnivariate n q` is a symmetric multivariate polynomial. -/
theorem isSymmetric_symPolyOfUnivariate (n : ℕ) (q : Polynomial ℝ) :
    (symPolyOfUnivariate n q).IsSymmetric := by
  intro σ
  simp only [symPolyOfUnivariate]
  induction q using Polynomial.induction_on' with
  | add p r hp hr => simp [map_add, hp, hr]
  | monomial k c =>
      simp only [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq, map_mul,
        MvPolynomial.rename_C, map_pow, map_sum, MvPolynomial.rename_X]
      rw [Equiv.sum_comp σ (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))]

/-- `symPolyOfUnivariate n q` has total degree at most `q.natDegree`. -/
theorem totalDegree_symPolyOfUnivariate_le (n : ℕ) (q : Polynomial ℝ) :
    (symPolyOfUnivariate n q).totalDegree ≤ q.natDegree := by
  have hq_eq : q = ∑ i ∈ range (q.natDegree + 1), Polynomial.monomial i (q.coeff i) :=
    q.as_sum_range
  conv_lhs => rw [symPolyOfUnivariate, hq_eq]
  simp only [map_sum, Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine totalDegree_sum_le _ _ fun k hk ↦ ?_
  have hk_le : k ≤ q.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hk)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have hsum : (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 :=
    totalDegree_sum_le _ _ fun i _ ↦ by simp [MvPolynomial.totalDegree_X]
  exact (Nat.mul_le_mul_left k hsum).trans (by omega)

/-- Evaluating `symPolyOfUnivariate n q` at `a` gives `q(weight a)`. -/
@[simp]
theorem evalBool_symPolyOfUnivariate (q : Polynomial ℝ) (a : BitString n) :
    evalBool (symPolyOfUnivariate n q) a = q.eval (weight a : ℝ) := by
  have hsum : evalBool (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) a =
      (weight a : ℝ) := by
    simp only [evalBool, map_sum, MvPolynomial.eval_X, weight_eq_sum_toNat, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by cases a i <;> simp [bitVal]
  simp only [symPolyOfUnivariate]
  induction q using Polynomial.induction_on' with
  | add p r hp hr => simp [map_add, Polynomial.eval_add, hp, hr]
  | monomial k c =>
      simp only [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq, Polynomial.eval_monomial,
        evalBool, map_mul, MvPolynomial.eval_C, map_pow]
      congr 2

/-- Binomial-basis univariate polynomial `C(X, j) = descPochhammer ℝ j / j!`. -/
private noncomputable def choosePoly (j : ℕ) : Polynomial ℝ :=
  Polynomial.C ((j.factorial : ℝ)⁻¹) * descPochhammer ℝ j

private lemma natDegree_choosePoly_le (j : ℕ) : (choosePoly j).natDegree ≤ j :=
  (Polynomial.natDegree_C_mul_le _ _).trans (descPochhammer_natDegree ℝ j).le

private lemma eval_choosePoly_nat (j i : ℕ) :
    (choosePoly j).eval (i : ℝ) = (Nat.choose i j : ℝ) := by
  rw [choosePoly, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have hfac : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  push_cast
  field_simp

/-- Every univariate real polynomial of degree at most `d` is a linear combination of the binomial
polynomials `C(i, 0), …, C(i, d)` on `ℕ`. -/
private lemma exists_binomial_coeffs {d : ℕ} {q : Polynomial ℝ} (hq : q.natDegree ≤ d) :
    ∃ α : Fin (d + 1) → ℝ,
      ∀ i : ℕ, q.eval (i : ℝ) = ∑ j : Fin (d + 1), α j * (i.choose j : ℝ) := by
  induction d generalizing q with
  | zero =>
      rw [Nat.le_zero] at hq
      rw [Polynomial.eq_C_of_natDegree_eq_zero hq]
      exact ⟨fun _ ↦ q.coeff 0, fun _ ↦ by simp⟩
  | succ d ih =>
      set c : ℝ := q.coeff (d + 1) * ((d + 1).factorial : ℝ)
      set r : Polynomial ℝ := q - Polynomial.C c * choosePoly (d + 1)
      have hr_deg : r.natDegree ≤ d := by
        by_cases hlt : q.natDegree < d + 1
        · have hc0 : c = 0 := by
            simp [c, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
          simpa [r, hc0] using Nat.le_of_lt_succ hlt
        · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro k hk
          rcases lt_trichotomy k (d + 1) with h1 | rfl | h2
          · omega
          · simp only [r, c, choosePoly, Polynomial.coeff_sub, ← mul_assoc, ← Polynomial.C_mul,
              Polynomial.coeff_C_mul]
            have hfac : ((d + 1).factorial : ℝ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
            have hlead : (descPochhammer ℝ (d + 1)).coeff (d + 1) = 1 := by
              have hm := (monic_descPochhammer ℝ (d + 1)).leadingCoeff
              rwa [Polynomial.leadingCoeff, descPochhammer_natDegree] at hm
            rw [mul_inv_cancel_right₀ hfac, hlead, mul_one, sub_self]
          · have hq0 : q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            have hc0 : (Polynomial.C c * choosePoly (d + 1)).coeff k = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt
                (((Polynomial.natDegree_C_mul_le _ _).trans
                  (natDegree_choosePoly_le (d + 1))).trans_lt h2)
            simp [r, hq0, hc0]
      obtain ⟨α₀, hα₀⟩ := ih hr_deg
      refine ⟨Fin.snoc α₀ c, fun i ↦ ?_⟩
      have hqr : q.eval (i : ℝ) = r.eval (i : ℝ) + c * (choosePoly (d + 1)).eval (i : ℝ) := by
        simp [r]
      rw [hqr, hα₀ i, eval_choosePoly_nat]
      symm
      rw [Fin.sum_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- If two bit strings have equal Hamming weight, some permutation maps one to the other. -/
theorem exists_perm_of_weight_eq {a b : BitString n} (h : weight a = weight b) :
    ∃ σ : Equiv.Perm (Fin n), a = b ∘ σ := by
  let Sa := bitStringToSet a
  let Sb := bitStringToSet b
  have hcard : #Sa = #Sb := h
  have hcardc : #Saᶜ = #Sbᶜ := by
    rw [card_compl, card_compl, hcard]
  let e₁ : Sa ≃ Sb := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hcard])
  let e₂ : (Saᶜ : Finset (Fin n)) ≃ (Sbᶜ : Finset (Fin n)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hcardc])
  let σ : Equiv.Perm (Fin n) :=
    { toFun i := if hi : i ∈ Sa then (e₁ ⟨i, hi⟩).1 else (e₂ ⟨i, mem_compl.mpr hi⟩).1
      invFun j := if hj : j ∈ Sb then (e₁.symm ⟨j, hj⟩).1 else (e₂.symm ⟨j, mem_compl.mpr hj⟩).1
      left_inv i := by
        by_cases hi : i ∈ Sa
        · have h1 : (e₁ ⟨i, hi⟩).1 ∈ Sb := (e₁ ⟨i, hi⟩).2
          simp [hi, h1]
        · have h2 : (e₂ ⟨i, mem_compl.mpr hi⟩).1 ∉ Sb := mem_compl.mp (e₂ ⟨i, mem_compl.mpr hi⟩).2
          simp [hi, h2]
      right_inv j := by
        by_cases hj : j ∈ Sb
        · have h1 : (e₁.symm ⟨j, hj⟩).1 ∈ Sa := (e₁.symm ⟨j, hj⟩).2
          simp [hj, h1]
        · have h2 : (e₂.symm ⟨j, mem_compl.mpr hj⟩).1 ∉ Sa :=
            mem_compl.mp (e₂.symm ⟨j, mem_compl.mpr hj⟩).2
          simp [hj, h2] }
  refine ⟨σ, funext fun i ↦ ?_⟩
  by_cases hi : i ∈ Sa
  · have hbi : σ i ∈ Sb := by simp [σ, hi]
    have ha : a i = true := (mem_filter.mp hi).2
    have hb : b (σ i) = true := (mem_filter.mp hbi).2
    simp [ha, hb]
  · have hbi : σ i ∉ Sb := by
      simp only [σ, hi, ↓reduceDIte, Equiv.coe_fn_mk]
      exact mem_compl.mp (e₂ ⟨i, mem_compl.mpr hi⟩).2
    have ha : a i = false := Bool.eq_false_iff.mpr fun h' ↦ hi (mem_filter.mpr ⟨mem_univ i, h'⟩)
    have hb : b (σ i) = false :=
      Bool.eq_false_iff.mpr fun h' ↦ hbi (mem_filter.mpr ⟨mem_univ _, h'⟩)
    simp [ha, hb]

/-- Evaluating a symmetric polynomial on a bit string depends only on its Hamming weight. -/
theorem evalBool_eq_of_isSymmetric {P : MvPolynomial (Fin n) ℝ} (hP : P.IsSymmetric)
    {a b : BitString n} (hw : weight a = weight b) :
    evalBool P a = evalBool P b := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_weight_eq hw
  calc evalBool P (b ∘ σ)
      = MvPolynomial.eval (fun i ↦ bitVal ℝ (b i)) (MvPolynomial.rename σ P) := by
        simp [evalBool, MvPolynomial.eval_rename, Function.comp_def]
    _ = evalBool P b := by rw [hP σ]; rfl

/-- For every `i ≤ n`, there exists a bit string `a : BitString n` with `weight a = i`. -/
theorem exists_bitString_weight_eq {i : ℕ} (hi : i ≤ n) :
    ∃ a : BitString n, weight a = i := by
  refine ⟨setToBitString (univ.filter fun j : Fin n ↦ (j : ℕ) < i), ?_⟩
  rw [weight_setToBitString]
  have heq : (univ.filter fun j : Fin n ↦ (j : ℕ) < i) =
      (range i).attach.map ⟨fun k ↦ ⟨k.1, (mem_range.mp k.2).trans_le hi⟩,
        fun a b h ↦ Subtype.ext (Fin.mk.inj h)⟩ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_attach, Subtype.exists, mem_range]
    exact ⟨fun hj ↦ ⟨j.1, hj, rfl⟩, fun ⟨k, hk, hkj⟩ ↦ hkj ▸ hk⟩
  rw [heq, card_map, card_attach, card_range]

/-- Every symmetric multivariate polynomial of degree at most `d` evaluates on `{0, 1}ⁿ` as a
univariate polynomial of degree at most `d` in the Hamming weight, and hence as a linear
combination of `C(weight a, 0), …, C(weight a, d)`. -/
theorem exists_binomial_eval_of_isSymmetric {P : MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hsym : P.IsSymmetric) (hdeg : P.totalDegree ≤ d) :
    ∃ α : Fin (d + 1) → ℝ, ∀ a : BitString n,
      evalBool P a = ∑ j : Fin (d + 1), α j * ((weight a).choose j : ℝ) := by
  have hmem : evalBool P ∈ lowDegree ℝ (Fin n) d :=
    mem_lowDegree_iff_exists_mvPolynomial.mpr ⟨P, hdeg, rfl⟩
  obtain ⟨q, hq_deg, hq_ev⟩ := exists_natDegree_le_eval_eq_layerAverage hmem
  obtain ⟨α, hα⟩ := exists_binomial_coeffs hq_deg
  refine ⟨α, fun a ↦ ?_⟩
  have hwa : weight a ≤ Fintype.card (Fin n) := weight_le a
  have havg : layerAverage (evalBool P) (weight a) = evalBool P a := by
    rw [layerAverage, Finset.expect_eq_sum_div_card]
    have hsum : ∑ x ∈ univ.filter (fun x : BitString n ↦ weight x = weight a), evalBool P x =
        ∑ _x ∈ univ.filter (fun x : BitString n ↦ weight x = weight a), evalBool P a :=
      Finset.sum_congr rfl fun x hx ↦ evalBool_eq_of_isSymmetric hsym (mem_filter.mp hx).2
    have hne : (univ.filter fun x : BitString n ↦ weight x = weight a).Nonempty :=
      ⟨a, mem_filter.mpr ⟨mem_univ a, rfl⟩⟩
    have hcard_ne : ((#(univ.filter fun x : BitString n ↦ weight x = weight a) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hne.card_pos.ne'
    rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_ne]
  rw [← havg, ← hq_ev (weight a) hwa, hα (weight a)]

/-- Exact symmetric torus approximation of degree at most `n` exists for every symmetric Boolean
function when `0 ≤ ε`. -/
theorem exists_isSymTorusApprox_card {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction n}
    (hf : f.IsSymmetric) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ n ∧ IsSymTorusApprox P ε f := by
  obtain ⟨g, hg⟩ := hf.exists_eq_comp_weight
  have hinterp : ∀ m : ℕ, ∃ α : Fin (m + 1) → ℝ, ∀ i ≤ m,
      ∑ j : Fin (m + 1), α j * (i.choose j : ℝ) = bitVal ℝ (g i) / 2 := by
    intro m
    induction m with
    | zero =>
        refine ⟨fun _ ↦ bitVal ℝ (g 0) / 2, fun i hi ↦ ?_⟩
        obtain rfl : i = 0 := Nat.le_zero.mp hi
        simp
    | succ m ih =>
        obtain ⟨α₀, hα₀⟩ := ih
        let c : ℝ := bitVal ℝ (g (m + 1)) / 2 - ∑ j : Fin (m + 1), α₀ j * ((m + 1).choose j : ℝ)
        refine ⟨Fin.snoc α₀ c, fun i hi ↦ ?_⟩
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rcases eq_or_lt_of_le hi with rfl | hlt
        · simp [c]
        · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero, add_zero]
          exact hα₀ i (Nat.lt_succ_iff.mp hlt)
  obtain ⟨α, hα⟩ := hinterp n
  let q : Polynomial ℝ := ∑ j : Fin (n + 1), Polynomial.C (α j) * choosePoly j
  have hq_deg : q.natDegree ≤ n :=
    poly_natDegree_sum_le _ _ fun j _ ↦
      ((Polynomial.natDegree_C_mul_le _ _).trans (natDegree_choosePoly_le j)).trans
        (Nat.lt_succ_iff.mp j.2)
  refine ⟨symPolyOfUnivariate n q, (totalDegree_symPolyOfUnivariate_le n q).trans hq_deg,
    isSymmetric_symPolyOfUnivariate n q, 0, fun a ↦ ?_⟩
  have hwa : weight a ≤ n := weight_le_length a
  have hev : evalBool (symPolyOfUnivariate n q) a = bitVal ℝ (f a) / 2 := by
    rw [evalBool_symPolyOfUnivariate, ← hg a, ← hα (weight a) hwa]
    simp only [q, poly_eval_sum, Polynomial.eval_mul, Polynomial.eval_C, eval_choosePoly_nat]
  simp [hev, hε]

/-- Any degree-`≤ d` symmetric torus `ε`-approximation bounds `symTorusDegree ε f` by `d`. -/
theorem symTorusDegree_le_of_isSymTorusApprox {P : MvPolynomial (Fin n) ℝ} {d : ℕ} {ε : ℝ}
    {f : BooleanFunction n} (hdeg : P.totalDegree ≤ d) (hP : IsSymTorusApprox P ε f) :
    symTorusDegree ε f ≤ d :=
  Nat.sInf_le ⟨P, hdeg, hP⟩

/-- For `0 ≤ ε` and symmetric `f`, `symTorusDegree ε f` is attained. -/
theorem exists_isSymTorusApprox_symTorusDegree {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction n}
    (hf : f.IsSymmetric) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ symTorusDegree ε f ∧ IsSymTorusApprox P ε f :=
  Nat.sInf_mem
    (s := {d : ℕ | ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ d ∧ IsSymTorusApprox P ε f})
    ⟨n, exists_isSymTorusApprox_card hε hf⟩

/-- For `0 ≤ ε` and symmetric `f`, `symTorusDegree ε f ≤ n`. -/
theorem symTorusDegree_le_card {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction n}
    (hf : f.IsSymmetric) : symTorusDegree ε f ≤ n := by
  obtain ⟨P, hdeg, hP⟩ := exists_isSymTorusApprox_card hε hf
  exact symTorusDegree_le_of_isSymTorusApprox hdeg hP

/-- For `0 ≤ ε` and symmetric `f`, `torusDegree ε f ≤ symTorusDegree ε f`. -/
theorem torusDegree_le_symTorusDegree {ε : ℝ} (hε : 0 ≤ ε) {f : BooleanFunction n}
    (hf : f.IsSymmetric) : torusDegree ε f ≤ symTorusDegree ε f := by
  obtain ⟨P, hdeg, _, hP⟩ := exists_isSymTorusApprox_symTorusDegree hε hf
  exact torusDegree_le_of_isTorusApprox hdeg hP

/-- **Low-weight integer-part normalization.** Given any `P ∈ ℝ[X₁, …, Xₙ]` of total degree at
most `d` and any Boolean function `f`, there exists `P' ∈ ℝ[X₁, …, Xₙ]` of total degree at most `d`
such that `P(a) - P'(a) ∈ ℤ` for all `a ∈ {0, 1}ⁿ` (hence `P'` `ε`-approximates `f` whenever `P`
does), and whenever `P` `ε`-approximates `f` with `ε < 1 / 2`, we have `|P'(a) - f(a) / 2| ≤ ε`
for every `a` with `weight a ≤ d` (so the unique integer part `Z'` of `P'` satisfies `Z'(a) = 0`
on all inputs of Hamming weight at most `d`). -/
theorem exists_isTorusApprox_zero_lowWeight (P : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) (f : BooleanFunction n) :
    ∃ P' : MvPolynomial (Fin n) ℝ, P'.totalDegree ≤ d ∧
      (∀ a : BitString n, ∃ m : ℤ, evalBool P a - evalBool P' a = (m : ℝ)) ∧
      (∀ ε : ℝ, IsTorusApprox P ε f → IsTorusApprox P' ε f) ∧
      (∀ ε : ℝ, ε < 1 / 2 → IsTorusApprox P ε f →
        ∃ Z' : BitString n → ℤ,
          (∀ a, |evalBool P' a - bitVal ℝ (f a) / 2 - (Z' a : ℝ)| ≤ ε) ∧
          (∀ a, weight a ≤ d → Z' a = 0)) := by
  have hstep : ∀ k ≤ d + 1, ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ d ∧
      (∀ a : BitString n, ∃ m : ℤ, evalBool P a - evalBool Q a = (m : ℝ)) ∧
      (∀ ε : ℝ, ε < 1 / 2 → IsTorusApprox P ε f →
        ∀ a : BitString n, weight a < k → |evalBool Q a - bitVal ℝ (f a) / 2| ≤ ε) := by
    intro k hk
    induction k with
    | zero => exact ⟨P, hdeg, fun _ ↦ ⟨0, by simp⟩, fun _ _ _ _ h ↦ absurd h (Nat.not_lt_zero _)⟩
    | succ i ih =>
        obtain ⟨Q, hQdeg, hQint, hQlow⟩ := ih (by omega)
        have hi_le : i ≤ d := by omega
        let layer : Finset (Finset (Fin n)) := univ.filter fun S ↦ #S = i
        let mCoeff : Finset (Fin n) → ℤ :=
          fun S ↦ round (evalBool Q (setToBitString S) - bitVal ℝ (f (setToBitString S)) / 2)
        let Q' : MvPolynomial (Fin n) ℝ :=
          Q - ∑ S ∈ layer, MvPolynomial.C (mCoeff S : ℝ) * multilinearMonomial S
        have hQ'deg : Q'.totalDegree ≤ d := by
          have hqeq : Q' = Q + MvPolynomial.C (-1 : ℝ) *
              ∑ S ∈ layer, MvPolynomial.C (mCoeff S : ℝ) * multilinearMonomial S := by
            simp [Q', sub_eq_add_neg]
          rw [hqeq]
          refine (MvPolynomial.totalDegree_add Q _).trans (max_le hQdeg ?_)
          refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          rw [MvPolynomial.totalDegree_C, zero_add]
          refine totalDegree_sum_le layer _ fun S hS ↦ ?_
          have hcard : #S = i := (mem_filter.mp hS).2
          refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          rw [MvPolynomial.totalDegree_C, zero_add]
          exact (totalDegree_multilinearMonomial_le S).trans (hcard ▸ hi_le)
        have hev_diff : ∀ T : Finset (Fin n),
            evalBool Q (setToBitString T) - evalBool Q' (setToBitString T) =
              ((∑ S ∈ layer, if S ⊆ T then mCoeff S else 0 : ℤ) : ℝ) := by
          intro T
          have hsub : evalBool Q (setToBitString T) - evalBool Q' (setToBitString T) =
              evalBool (∑ S ∈ layer, MvPolynomial.C (mCoeff S : ℝ) * multilinearMonomial S)
                (setToBitString T) := by
            simp [Q']
          rw [hsub, Int.cast_sum]
          unfold evalBool
          rw [map_sum]
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [map_mul, MvPolynomial.eval_C]
          change (mCoeff S : ℝ) * evalBool (multilinearMonomial S) (setToBitString T) = _
          rw [evalBool_multilinearMonomial_set]
          split_ifs <;> simp
        refine ⟨Q', hQ'deg, fun a ↦ ?_, fun ε hε hP a ha ↦ ?_⟩
        · rw [← setToBitString_bitStringToSet a]
          set T := bitStringToSet a
          obtain ⟨m₀, hm₀⟩ := hQint (setToBitString T)
          refine ⟨m₀ + ∑ S ∈ layer, if S ⊆ T then mCoeff S else 0, ?_⟩
          rw [Int.cast_add]
          linarith [hm₀, hev_diff T]
        · rw [← setToBitString_bitStringToSet a] at ha ⊢
          set T := bitStringToSet a
          rw [weight_setToBitString] at ha
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ha) with hlt | heq
          · have hzero : evalBool Q' (setToBitString T) = evalBool Q (setToBitString T) := by
              have h0 : (∑ S ∈ layer, if S ⊆ T then mCoeff S else 0 : ℤ) = 0 := by
                refine Finset.sum_eq_zero fun S hS ↦ ?_
                split_ifs with hST
                · have := Finset.card_le_card hST
                  have hcard := (mem_filter.mp hS).2
                  omega
                · rfl
              have hd := hev_diff T
              rw [h0, Int.cast_zero] at hd
              linarith
            rw [hzero]
            exact hQlow ε hε hP _ (by simpa using hlt)
          · have hsingle : evalBool Q' (setToBitString T) =
                evalBool Q (setToBitString T) - (mCoeff T : ℝ) := by
              have hT : T ∈ layer := mem_filter.mpr ⟨mem_univ T, heq⟩
              have h1 : (∑ S ∈ layer, if S ⊆ T then mCoeff S else 0 : ℤ) = mCoeff T := by
                rw [Finset.sum_eq_single T]
                · simp
                · intro S hS hne
                  split_ifs with hST
                  · exact absurd
                      (Finset.eq_of_subset_of_card_le hST (by rw [(mem_filter.mp hS).2, heq])) hne
                  · rfl
                · exact fun h ↦ absurd hT h
              have hd := hev_diff T
              rw [h1] at hd
              linarith
            obtain ⟨Z, hZ⟩ := hP
            obtain ⟨m₀, hm₀⟩ := hQint (setToBitString T)
            set z : ℤ := Z (setToBitString T) - m₀
            set y : ℝ := evalBool Q (setToBitString T) - bitVal ℝ (f (setToBitString T)) / 2
            have hyz : |y - (z : ℝ)| ≤ ε := by
              have h := hZ (setToBitString T)
              convert h using 2
              simp only [y, z, Int.cast_sub]
              linarith
            have hround : round y = z := by
              have hlt1 : |(round y : ℝ) - (z : ℝ)| < 1 := by
                calc |(round y : ℝ) - (z : ℝ)|
                    = |(round y - y) + (y - (z : ℝ))| := by ring_nf
                  _ ≤ |(round y : ℝ) - y| + |y - (z : ℝ)| := abs_add_le _ _
                  _ ≤ 1 / 2 + ε := add_le_add (by rw [abs_sub_comm]; exact abs_sub_round y) hyz
                  _ < 1 := by linarith
              have hint : |round y - z| < 1 := by exact_mod_cast hlt1
              rw [abs_lt] at hint
              omega
            have hrew : evalBool Q (setToBitString T) - (mCoeff T : ℝ) -
                bitVal ℝ (f (setToBitString T)) / 2 = y - (round y : ℝ) := by
              dsimp only [y, mCoeff]
              ring
            rw [hsingle, hrew, hround]
            exact hyz
  obtain ⟨P', hP'deg, hP'int, hP'low⟩ := hstep (d + 1) le_rfl
  have hpres : ∀ ε : ℝ, IsTorusApprox P ε f → IsTorusApprox P' ε f := by
    rintro ε ⟨Z, hZ⟩
    choose m hm using hP'int
    refine ⟨fun a ↦ Z a - m a, fun a ↦ ?_⟩
    convert hZ a using 2
    push_cast
    linarith [hm a]
  refine ⟨P', hP'deg, hP'int, hpres, fun ε hε hP ↦ ?_⟩
  obtain ⟨Z', hZ'⟩ := hpres ε hP
  refine ⟨Z', hZ', fun a ha ↦ ?_⟩
  have hlow := hP'low ε hε hP a (Nat.lt_succ_of_le ha)
  have hza := hZ' a
  have hlt1 : |(Z' a : ℝ)| < 1 := by
    calc |(Z' a : ℝ)|
        = |(evalBool P' a - bitVal ℝ (f a) / 2) -
            (evalBool P' a - bitVal ℝ (f a) / 2 - (Z' a : ℝ))| := by ring_nf
      _ ≤ |evalBool P' a - bitVal ℝ (f a) / 2| +
            |evalBool P' a - bitVal ℝ (f a) / 2 - (Z' a : ℝ)| := abs_sub _ _
      _ ≤ ε + ε := add_le_add hlow hza
      _ < 1 := by linarith
  have hint : |Z' a| < 1 := by exact_mod_cast hlt1
  rw [abs_lt] at hint
  omega

end Basic

/-! ### Linear-programming duality for asymmetric and symmetric torus degrees -/

section Duality

open scoped Matrix

/-- The `ℓ¹` norm `∑ i, |γ i|` of a finitely indexed real vector `γ`. -/
@[expose]
def l1Norm {ι : Type*} [Fintype ι] (γ : ι → ℝ) : ℝ :=
  ∑ i, |γ i|

/-- The `ℓ¹` norm of the zero vector vanishes. -/
@[simp]
theorem l1Norm_zero {ι : Type*} [Fintype ι] : l1Norm (0 : ι → ℝ) = 0 := by
  simp [l1Norm]

/-- The `ℓ¹` norm is invariant under negation. -/
@[simp]
theorem l1Norm_neg {ι : Type*} [Fintype ι] (γ : ι → ℝ) : l1Norm (-γ) = l1Norm γ := by
  simp [l1Norm]

/-- The `ℓ¹` norm is nonnegative. -/
theorem l1Norm_nonneg {ι : Type*} [Fintype ι] (γ : ι → ℝ) : 0 ≤ l1Norm γ :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Every nonzero vector has strictly positive `ℓ¹` norm. -/
theorem l1Norm_pos_of_ne_zero {ι : Type*} [Fintype ι] {γ : ι → ℝ} (hγ : γ ≠ 0) :
    0 < l1Norm γ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hγ
  exact Finset.sum_pos' (fun j _ ↦ abs_nonneg _) ⟨i, mem_univ i, abs_pos.mpr hi⟩

/-- Scalar homogeneity of `l1Norm`. -/
theorem l1Norm_const_mul {ι : Type*} [Fintype ι] (c : ℝ) (γ : ι → ℝ) :
    l1Norm (fun i ↦ c * γ i) = |c| * l1Norm γ := by
  simp only [l1Norm, abs_mul, Finset.mul_sum]

/-- If `γ` vanishes outside a finset `s`, then `l1Norm γ = ∑ i ∈ s, |γ i|`. -/
theorem l1Norm_eq_sum_of_support_subset {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    {s : Finset ι} (hs : ∀ i, i ∉ s → γ i = 0) :
    l1Norm γ = ∑ i ∈ s, |γ i| := by
  rw [l1Norm]
  symm
  refine Finset.sum_subset (subset_univ s) fun i _ hi ↦ ?_
  rw [hs i hi, abs_zero]

/-- For an integer vector `φ : ι → ℤ`, the sum of `natAbs` casts to `l1Norm`. -/
theorem natCast_sum_natAbs_eq_l1Norm {ι : Type*} [Fintype ι] (φ : ι → ℤ) :
    ((∑ i : ι, (φ i).natAbs : ℕ) : ℝ) = l1Norm (fun i ↦ (φ i : ℝ)) := by
  simp only [l1Norm, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [← Int.cast_natCast (φ i).natAbs, Int.natCast_natAbs, Int.cast_abs]

/-- General `ℓ^∞`-approximation duality via Farkas' lemma: for any matrix `M : Matrix ρ κ ℝ`, target
`w : κ → ℝ`, and `ε ≥ 0`, there is no `α : ρ → ℝ` satisfying `|(Mᵀ *ᵥ α) j - w j| ≤ ε` for all `j`
if and only if there exists `γ : κ → ℝ` in the nullspace `M *ᵥ γ = 0` satisfying
`ε * l1Norm γ < |w ⬝ᵥ γ|`. -/
theorem not_exists_transpose_mulVec_approx_iff {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (M : Matrix ρ κ ℝ) (w : κ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (¬∃ α : ρ → ℝ, ∀ j : κ, |(Mᵀ *ᵥ α) j - w j| ≤ ε) ↔
      ∃ γ : κ → ℝ, M *ᵥ γ = 0 ∧ ε * l1Norm γ < |w ⬝ᵥ γ| := by
  let A : Matrix (κ ⊕ κ) ρ ℝ := _root_.Matrix.fromRows Mᵀ (-Mᵀ)
  let b : κ ⊕ κ → ℝ := Sum.elim (fun j ↦ ε + w j) (fun j ↦ ε - w j)
  have hsys : (∃ α : ρ → ℝ, ∀ j : κ, |(Mᵀ *ᵥ α) j - w j| ≤ ε) ↔ (∃ α : ρ → ℝ, A *ᵥ α ≤ b) := by
    refine exists_congr fun α ↦ ⟨fun h k ↦ ?_, fun h j ↦ abs_le.mpr ⟨?_, ?_⟩⟩
    · rcases k with j | j
      · have := (abs_le.mp (h j)).2
        change (Mᵀ *ᵥ α) j ≤ ε + w j
        linarith
      · have := (abs_le.mp (h j)).1
        change (-Mᵀ *ᵥ α) j ≤ ε - w j
        simp only [_root_.Matrix.neg_mulVec, Pi.neg_apply]
        linarith
    · have := h (Sum.inr j)
      change (-Mᵀ *ᵥ α) j ≤ ε - w j at this
      simp only [_root_.Matrix.neg_mulVec, Pi.neg_apply] at this
      linarith
    · have := h (Sum.inl j)
      change (Mᵀ *ᵥ α) j ≤ ε + w j at this
      linarith
  rw [hsys, _root_.Matrix.not_exists_mulVec_le_iff]
  constructor
  · rintro ⟨y, hy0, hyA, hyb⟩
    let yp : κ → ℝ := y ∘ Sum.inl
    let ym : κ → ℝ := y ∘ Sum.inr
    let γ : κ → ℝ := ym - yp
    refine ⟨γ, ?_, ?_⟩
    · have hvec : (yp - ym) ᵥ* Mᵀ = 0 := by
        ext i
        have hi := congrFun hyA i
        simp only [A, _root_.Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
          _root_.Matrix.fromRows_apply_inl, _root_.Matrix.fromRows_apply_inr,
          _root_.Matrix.neg_apply, Pi.zero_apply, mul_neg, Finset.sum_neg_distrib] at hi
        simp only [_root_.Matrix.vecMul, dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
          Pi.zero_apply, yp, ym, Function.comp_apply]
        linarith
      rw [← _root_.Matrix.mulVec_transpose, _root_.Matrix.transpose_transpose] at hvec
      have hneg : M *ᵥ γ = -(M *ᵥ (yp - ym)) := by
        rw [← _root_.Matrix.mulVec_neg]
        congr 1
        ext j; simp [γ]
      rw [hneg, hvec, neg_zero]
    · have hdot : y ⬝ᵥ b = ε * (∑ j, (yp j + ym j)) - w ⬝ᵥ γ := by
        simp only [b, γ, yp, ym, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Function.comp_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      have hl1 : l1Norm γ ≤ ∑ j, (yp j + ym j) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hp : 0 ≤ yp j := hy0 (Sum.inl j)
        have hm : 0 ≤ ym j := hy0 (Sum.inr j)
        simp only [γ, Pi.sub_apply, abs_le]
        constructor <;> linarith
      have hgt : ε * l1Norm γ < w ⬝ᵥ γ := by
        calc ε * l1Norm γ
            ≤ ε * ∑ j, (yp j + ym j) := mul_le_mul_of_nonneg_left hl1 hε
          _ < w ⬝ᵥ γ := by linarith
      exact hgt.trans_le (le_abs_self _)
  · rintro ⟨γ, hMγ, hgt⟩
    by_contra hno
    have hex : ∃ α : ρ → ℝ, A *ᵥ α ≤ b :=
      not_not.mp fun h' ↦ hno ((_root_.Matrix.not_exists_mulVec_le_iff A b).mp h')
    obtain ⟨α, hα⟩ := hsys.mpr hex
    have horth : (Mᵀ *ᵥ α) ⬝ᵥ γ = 0 := by
      rw [dotProduct_comm, _root_.Matrix.dotProduct_mulVec, _root_.Matrix.vecMul_transpose, hMγ,
        zero_dotProduct]
    have hle : |w ⬝ᵥ γ| ≤ ε * l1Norm γ := by
      have heq : w ⬝ᵥ γ = (w - Mᵀ *ᵥ α) ⬝ᵥ γ := by
        rw [sub_dotProduct, horth, sub_zero]
      rw [heq, dotProduct, l1Norm, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [abs_mul, Pi.sub_apply, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (hα j) (abs_nonneg _)
    linarith

/-- The set-inclusion matrix `M(n, d)` indexed by `{S : Finset (Fin n) // #S ≤ d}` (rows) and
`Finset (Fin n)` (columns), with entry `M(n, d)_{S, T} = 1` if `S ⊆ T` and `0` otherwise. -/
@[expose]
def inclusionMatrix (n d : ℕ) :
    Matrix {S : Finset (Fin n) // #S ≤ d} (Finset (Fin n)) ℝ :=
  fun S T ↦ if S.1 ⊆ T then 1 else 0

/-- Row `S` of `inclusionMatrix n d *ᵥ γ` sums `(if S ⊆ T then 1 else 0) * γ T` over `T`. -/
theorem inclusionMatrix_mulVec_apply (n d : ℕ) (γ : Finset (Fin n) → ℝ)
    (S : {S : Finset (Fin n) // #S ≤ d}) :
    (inclusionMatrix n d *ᵥ γ) S =
      ∑ T : Finset (Fin n), (if S.1 ⊆ T then (1 : ℝ) else 0) * γ T := by
  simp [inclusionMatrix, _root_.Matrix.mulVec, dotProduct]

/-- Entry `T` of `(inclusionMatrix n d)ᵀ *ᵥ α` evaluates the multilinear expansion at `T`. -/
theorem transpose_inclusionMatrix_mulVec_apply (n d : ℕ)
    (α : {S : Finset (Fin n) // #S ≤ d} → ℝ) (T : Finset (Fin n)) :
    ((inclusionMatrix n d)ᵀ *ᵥ α) T =
      ∑ S : {S : Finset (Fin n) // #S ≤ d}, α S * (if S.1 ⊆ T then 1 else 0) := by
  simp [inclusionMatrix, _root_.Matrix.mulVec, dotProduct, mul_comm]

/-- Entry `(S, j)` of `inclusionMatrix n d * A` sums `(if S ⊆ T then 1 else 0) * A T j`. -/
theorem inclusionMatrix_mul_apply {κ : Type*} (n d : ℕ)
    (A : Matrix (Finset (Fin n)) κ ℝ) (S : {S : Finset (Fin n) // #S ≤ d}) (j : κ) :
    (inclusionMatrix n d * A) S j =
      ∑ T : Finset (Fin n), (if S.1 ⊆ T then (1 : ℝ) else 0) * A T j := by
  simp [inclusionMatrix, _root_.Matrix.mul_apply]

/-- **Asymmetric torus degree LP duality.** For any `n, d : ℕ`, `0 ≤ ε`, and
`f : BooleanFunction n`, every torus polynomial `ε`-approximating `f` has total degree strictly
greater than `d` if and only if for every `Z : Finset (Fin n) → ℤ` there exists `γ` in the
nullspace of `inclusionMatrix n d` with
`ε * ‖γ‖₁ < |∑ T, (Z T + f(T) / 2) * γ T|`. -/
theorem not_exists_isTorusApprox_iff (n d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    (∀ P : MvPolynomial (Fin n) ℝ, IsTorusApprox P ε f → d < P.totalDegree) ↔
      ∀ Z : Finset (Fin n) → ℤ, ∃ γ : Finset (Fin n) → ℝ,
        inclusionMatrix n d *ᵥ γ = 0 ∧
        ε * l1Norm γ <
          |(fun T ↦ (Z T : ℝ) + bitVal ℝ (f (setToBitString T)) / 2) ⬝ᵥ γ| := by
  have hneg : (∀ P : MvPolynomial (Fin n) ℝ, IsTorusApprox P ε f → d < P.totalDegree) ↔
      ∀ Z : Finset (Fin n) → ℤ,
        ¬∃ α : {S : Finset (Fin n) // #S ≤ d} → ℝ, ∀ T : Finset (Fin n),
          |((inclusionMatrix n d)ᵀ *ᵥ α) T -
            ((Z T : ℝ) + bitVal ℝ (f (setToBitString T)) / 2)| ≤ ε := by
    constructor
    · intro h Z ⟨α, hα⟩
      let p : BitString n → ℝ := fun a ↦
        ∑ S : {S : Finset (Fin n) // #S ≤ d}, α S * (if S.1 ⊆ bitStringToSet a then 1 else 0)
      have hp : p ∈ lowDegree ℝ (Fin n) d :=
        (mem_lowDegree_iff_exists_coeffs d p).mpr ⟨α, fun T ↦ by
          simp only [p, bitStringToSet_setToBitString]⟩
      obtain ⟨P, hPdeg, hPev⟩ := mem_lowDegree_iff_exists_mvPolynomial.mp hp
      have happrox : IsTorusApprox P ε f := by
        refine ⟨fun a ↦ Z (bitStringToSet a), fun a ↦ ?_⟩
        rw [← setToBitString_bitStringToSet a]
        set T := bitStringToSet a
        rw [hPev]
        simp only [p, bitStringToSet_setToBitString]
        convert hα T using 2
        have hM : ((inclusionMatrix n d)ᵀ *ᵥ α) T =
            ∑ S : {S : Finset (Fin n) // #S ≤ d}, α S * (if S.1 ⊆ T then 1 else 0) := by
          simp [inclusionMatrix, _root_.Matrix.mulVec, dotProduct, mul_comm]
        rw [hM]
        ring
      exact not_lt_of_ge hPdeg (h P happrox)
    · rintro h P ⟨Z, hZ⟩
      by_contra hle
      push Not at hle
      have hp : evalBool P ∈ lowDegree ℝ (Fin n) d :=
        mem_lowDegree_iff_exists_mvPolynomial.mpr ⟨P, hle, rfl⟩
      obtain ⟨α, hα⟩ := (mem_lowDegree_iff_exists_coeffs d (evalBool P)).mp hp
      refine h (fun T ↦ Z (setToBitString T)) ⟨α, fun T ↦ ?_⟩
      convert hZ (setToBitString T) using 2
      have hM : ((inclusionMatrix n d)ᵀ *ᵥ α) T =
          ∑ S : {S : Finset (Fin n) // #S ≤ d}, α S * (if S.1 ⊆ T then 1 else 0) := by
        simp [inclusionMatrix, _root_.Matrix.mulVec, dotProduct, mul_comm]
      rw [hM, hα T]
      ring
  rw [hneg]
  exact forall_congr' fun Z ↦
    not_exists_transpose_mulVec_approx_iff (inclusionMatrix n d) _ hε

/-- Reformulation of `not_exists_isTorusApprox_iff` directly in terms of `d < torusDegree ε f`. -/
theorem lt_torusDegree_iff (n d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    d < torusDegree ε f ↔
      ∀ Z : Finset (Fin n) → ℤ, ∃ γ : Finset (Fin n) → ℝ,
        inclusionMatrix n d *ᵥ γ = 0 ∧
        ε * l1Norm γ <
          |(fun T ↦ (Z T : ℝ) + bitVal ℝ (f (setToBitString T)) / 2) ⬝ᵥ γ| := by
  rw [← not_exists_isTorusApprox_iff n d hε f]
  constructor
  · intro hlt P hP
    exact hlt.trans_le (torusDegree_le_of_isTorusApprox le_rfl hP)
  · intro h
    obtain ⟨P, hdeg, hP⟩ := exists_isTorusApprox_torusDegree hε f
    exact (h P hP).trans_le hdeg

/-- **Odd-parity integer witness lemma.** If `γ : ι → ℤ` has odd inner product
`∑ i, f(i) * γ i` with a Boolean vector `f : ι → Bool`, then for every `Z : ι → ℤ` and every
`ε < 1 / (2 * ‖γ‖₁)` we have `ε * ‖γ‖₁ < |⟨Z + f / 2, γ⟩|`. -/
theorem dual_witness_of_odd_int {ι : Type*} [Fintype ι] (f : ι → Bool) (γ : ι → ℤ)
    (hodd : Odd (∑ i : ι, ((f i).toNat : ℤ) * γ i)) (Z : ι → ℤ) {ε : ℝ}
    (hε : ε < 1 / (2 * l1Norm (fun i ↦ (γ i : ℝ)))) :
    ε * l1Norm (fun i ↦ (γ i : ℝ)) <
      |(fun i ↦ (Z i : ℝ) + bitVal ℝ (f i) / 2) ⬝ᵥ (fun i ↦ (γ i : ℝ))| := by
  have hγ_ne : (fun i ↦ (γ i : ℝ)) ≠ 0 := by
    intro h0
    have hsum0 : (∑ i : ι, ((f i).toNat : ℤ) * γ i) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have hi_real : (γ i : ℝ) = 0 := congrFun h0 i
      have hi : γ i = 0 := by exact_mod_cast hi_real
      simp [hi]
    rw [hsum0] at hodd
    exact Int.not_odd_zero hodd
  have hl1_pos : 0 < l1Norm (fun i ↦ (γ i : ℝ)) := l1Norm_pos_of_ne_zero hγ_ne
  obtain ⟨z, hz⟩ := hodd
  let z' : ℤ := ∑ i : ι, Z i * γ i
  have hdot : (fun i ↦ (Z i : ℝ) + bitVal ℝ (f i) / 2) ⬝ᵥ (fun i ↦ (γ i : ℝ)) =
      ((z' + z : ℤ) : ℝ) + 1 / 2 := by
    have hfsum : ∑ i : ι, bitVal ℝ (f i) * (γ i : ℝ) = ((2 * z + 1 : ℤ) : ℝ) := by
      rw [← hz, Int.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      cases f i <;> simp [bitVal]
    have hzsum : ∑ i : ι, (Z i : ℝ) * (γ i : ℝ) = (z' : ℝ) := by
      simp [z']
    calc (fun i ↦ (Z i : ℝ) + bitVal ℝ (f i) / 2) ⬝ᵥ (fun i ↦ (γ i : ℝ))
        = (∑ i, (Z i : ℝ) * (γ i : ℝ)) + (1 / 2) * ∑ i, bitVal ℝ (f i) * (γ i : ℝ) := by
          simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (z' : ℝ) + (1 / 2) * ((2 * z + 1 : ℤ) : ℝ) := by rw [hzsum, hfsum]
      _ = ((z' + z : ℤ) : ℝ) + 1 / 2 := by push_cast; ring
  have hhalf : (1 / 2 : ℝ) ≤ |((z' + z : ℤ) : ℝ) + 1 / 2| := by
    rcases le_or_gt 0 (z' + z) with hge | hlt
    · have : (0 : ℝ) ≤ ((z' + z : ℤ) : ℝ) := by exact_mod_cast hge
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hle : z' + z ≤ -1 := by omega
      have : ((z' + z : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hle
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hmul : ε * l1Norm (fun i ↦ (γ i : ℝ)) < 1 / 2 := by
    rw [← lt_div_iff₀ hl1_pos]
    refine hε.trans_eq ?_
    field_simp
  rw [hdot]
  exact hmul.trans_le hhalf

/-- Asymmetric torus degree lower bound from an odd-parity integer vector in `ker M(n, d)`. -/
theorem lt_torusDegree_of_odd_int_ker {n d : ℕ} {f : BooleanFunction n}
    {γ : Finset (Fin n) → ℤ}
    (hker : inclusionMatrix n d *ᵥ (fun T ↦ (γ T : ℝ)) = 0)
    (hodd : Odd (∑ T : Finset (Fin n), ((f (setToBitString T)).toNat : ℤ) * γ T))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / (2 * l1Norm (fun T ↦ (γ T : ℝ)))) :
    d < torusDegree ε f :=
  (lt_torusDegree_iff n d hε0 f).mpr fun Z ↦
    ⟨fun T ↦ (γ T : ℝ), hker,
      dual_witness_of_odd_int (fun T ↦ f (setToBitString T)) γ hodd Z hε⟩

/-- The symmetric binomial matrix `M̂(n, d)` of size `(d + 1) × (n + 1)` with entry
`M̂(n, d)_{j, i} = Nat.choose i j`. -/
@[expose]
def binomialMatrix (n d : ℕ) : Matrix (Fin (d + 1)) (Fin (n + 1)) ℝ :=
  fun j i ↦ ((i : ℕ).choose (j : ℕ) : ℝ)

/-- Row `j` of `binomialMatrix n d *ᵥ ψ` evaluates `∑ i, C(i, j) * ψ i`. -/
theorem binomialMatrix_mulVec_apply (n d : ℕ) (ψ : Fin (n + 1) → ℝ) (j : Fin (d + 1)) :
    (binomialMatrix n d *ᵥ ψ) j =
      ∑ i : Fin (n + 1), ((i : ℕ).choose (j : ℕ) : ℝ) * ψ i := by
  simp [binomialMatrix, _root_.Matrix.mulVec, dotProduct]

/-- Entry `(j, k)` of `binomialMatrix n d * A` evaluates `∑ i, C(i, j) * A i k`. -/
theorem binomialMatrix_mul_apply {κ : Type*} (n d : ℕ)
    (A : Matrix (Fin (n + 1)) κ ℝ) (j : Fin (d + 1)) (k : κ) :
    (binomialMatrix n d * A) j k =
      ∑ i : Fin (n + 1), ((i : ℕ).choose (j : ℕ) : ℝ) * A i k := by
  simp [binomialMatrix, _root_.Matrix.mul_apply]

/-- Lift a weight profile `g : Fin (n + 1) → Bool` to a symmetric Boolean function on `n` bits. -/
@[expose]
def ofWeightProfile {n : ℕ} (g : Fin (n + 1) → Bool) : BooleanFunction n :=
  fun a ↦ g ⟨weight a, Nat.lt_succ_of_le (weight_le_length a)⟩

/-- Evaluating `ofWeightProfile g` on a bit string of Hamming weight `w` yields `g w`. -/
theorem ofWeightProfile_of_weight_eq {n : ℕ} (g : Fin (n + 1) → Bool) {a : BitString n}
    (w : Fin (n + 1)) (hw : weight a = (w : ℕ)) :
    ofWeightProfile g a = g w := by
  simp only [ofWeightProfile]
  congr 1
  exact Fin.ext hw

/-- `ofWeightProfile g` is always symmetric. -/
theorem isSymmetric_ofWeightProfile {n : ℕ} (g : Fin (n + 1) → Bool) :
    (ofWeightProfile g).IsSymmetric := by
  intro x y h
  simp [ofWeightProfile, h]

/-- **Symmetric torus degree LP duality.** For any `n, d : ℕ`, `0 ≤ ε`, and weight profile
`g : Fin (n + 1) → Bool`, every symmetric torus polynomial `ε`-approximating `ofWeightProfile g`
has total degree strictly greater than `d` if and only if for every `Z : Fin (n + 1) → ℤ` there
exists `ψ` in the nullspace of `binomialMatrix n d` with
`ε * ‖ψ‖₁ < |∑ i, (Z i + g(i) / 2) * ψ i|`. -/
theorem not_exists_isSymTorusApprox_iff (n d : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (g : Fin (n + 1) → Bool) :
    (∀ P : MvPolynomial (Fin n) ℝ, IsSymTorusApprox P ε (ofWeightProfile g) →
        d < P.totalDegree) ↔
      ∀ Z : Fin (n + 1) → ℤ, ∃ ψ : Fin (n + 1) → ℝ,
        binomialMatrix n d *ᵥ ψ = 0 ∧
        ε * l1Norm ψ < |(fun i ↦ (Z i : ℝ) + bitVal ℝ (g i) / 2) ⬝ᵥ ψ| := by
  have hneg : (∀ P : MvPolynomial (Fin n) ℝ, IsSymTorusApprox P ε (ofWeightProfile g) →
        d < P.totalDegree) ↔
      ∀ Z : Fin (n + 1) → ℤ,
        ¬∃ α : Fin (d + 1) → ℝ, ∀ i : Fin (n + 1),
          |((binomialMatrix n d)ᵀ *ᵥ α) i - ((Z i : ℝ) + bitVal ℝ (g i) / 2)| ≤ ε := by
    constructor
    · intro h Z ⟨α, hα⟩
      let q : Polynomial ℝ := ∑ j : Fin (d + 1), Polynomial.C (α j) * choosePoly j
      have hq_deg : q.natDegree ≤ d :=
        poly_natDegree_sum_le _ _ fun j _ ↦
          ((Polynomial.natDegree_C_mul_le _ _).trans (natDegree_choosePoly_le j)).trans
            (Nat.lt_succ_iff.mp j.2)
      let P := symPolyOfUnivariate n q
      have hPdeg : P.totalDegree ≤ d := (totalDegree_symPolyOfUnivariate_le n q).trans hq_deg
      have hPsym : IsSymTorusApprox P ε (ofWeightProfile g) := by
        refine ⟨isSymmetric_symPolyOfUnivariate n q,
          fun a ↦ Z ⟨weight a, Nat.lt_succ_of_le (weight_le_length a)⟩, fun a ↦ ?_⟩
        set idx : Fin (n + 1) := ⟨weight a, Nat.lt_succ_of_le (weight_le_length a)⟩
        convert hα idx using 2
        have hwa : (weight a : ℝ) = ((idx : ℕ) : ℝ) := rfl
        have hPval : evalBool P a = ∑ j : Fin (d + 1), α j * ((idx : ℕ).choose j : ℝ) := by
          simp only [P, q, evalBool_symPolyOfUnivariate, hwa, poly_eval_sum, Polynomial.eval_mul,
            Polynomial.eval_C, eval_choosePoly_nat]
        have hMval : ((binomialMatrix n d)ᵀ *ᵥ α) idx =
            ∑ j : Fin (d + 1), α j * ((idx : ℕ).choose j : ℝ) := by
          simp [binomialMatrix, _root_.Matrix.mulVec, dotProduct, mul_comm]
        rw [hPval, hMval]
        change _ - bitVal ℝ (g idx) / 2 - (Z idx : ℝ) = _
        ring
      exact not_lt_of_ge hPdeg (h P hPsym)
    · rintro h P ⟨hsym, Z, hZ⟩
      by_contra hle
      push Not at hle
      obtain ⟨α, hα⟩ := exists_binomial_eval_of_isSymmetric hsym hle
      choose rep hrep using fun i : Fin (n + 1) ↦
        exists_bitString_weight_eq (Nat.lt_succ_iff.mp i.2)
      refine h (fun i ↦ Z (rep i)) ⟨α, fun i ↦ ?_⟩
      have hzi := hZ (rep i)
      convert hzi using 2
      have hMval : ((binomialMatrix n d)ᵀ *ᵥ α) i =
          ∑ j : Fin (d + 1), α j * ((i : ℕ).choose j : ℝ) := by
        simp [binomialMatrix, _root_.Matrix.mulVec, dotProduct, mul_comm]
      have hgval : ofWeightProfile g (rep i) = g i := by
        simp [ofWeightProfile, hrep i]
      rw [hMval, hα (rep i), hrep i, hgval]
      ring
  rw [hneg]
  exact forall_congr' fun Z ↦
    not_exists_transpose_mulVec_approx_iff (binomialMatrix n d) _ hε

/-- Reformulation of `not_exists_isSymTorusApprox_iff` in terms of `d < symTorusDegree`. -/
theorem lt_symTorusDegree_iff (n d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (g : Fin (n + 1) → Bool) :
    d < symTorusDegree ε (ofWeightProfile g) ↔
      ∀ Z : Fin (n + 1) → ℤ, ∃ ψ : Fin (n + 1) → ℝ,
        binomialMatrix n d *ᵥ ψ = 0 ∧
        ε * l1Norm ψ < |(fun i ↦ (Z i : ℝ) + bitVal ℝ (g i) / 2) ⬝ᵥ ψ| := by
  rw [← not_exists_isSymTorusApprox_iff n d hε g]
  constructor
  · intro hlt P hP
    exact hlt.trans_le (symTorusDegree_le_of_isSymTorusApprox le_rfl hP)
  · intro h
    obtain ⟨P, hdeg, hP⟩ :=
      exists_isSymTorusApprox_symTorusDegree hε (isSymmetric_ofWeightProfile g)
    exact (h P hP).trans_le hdeg

/-- Symmetric torus degree lower bound from an odd-parity integer vector in `ker M̂(n, d)`. -/
theorem lt_symTorusDegree_of_odd_int_ker {n d : ℕ} {g : Fin (n + 1) → Bool}
    {ψ : Fin (n + 1) → ℤ}
    (hker : binomialMatrix n d *ᵥ (fun i ↦ (ψ i : ℝ)) = 0)
    (hodd : Odd (∑ i : Fin (n + 1), ((g i).toNat : ℤ) * ψ i))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / (2 * l1Norm (fun i ↦ (ψ i : ℝ)))) :
    d < symTorusDegree ε (ofWeightProfile g) :=
  (lt_symTorusDegree_iff n d hε0 g).mpr fun Z ↦
    ⟨fun i ↦ (ψ i : ℝ), hker, dual_witness_of_odd_int g ψ hodd Z hε⟩

end Duality

end CslibFrontier.TorusPolynomial
