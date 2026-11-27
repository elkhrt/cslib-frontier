/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Dioph

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finsupp.Multiset
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Skolem Degree Reduction, Sum-of-Squares Aggregation, and Quartic Diophantine Equations

Develops the classical polynomial degree-reduction machinery for Diophantine equations under
standard Lean axioms:

1. **Sum-of-squares system aggregation**: merging a finite list of multivariate polynomials of
   total degree at most `d` into a single polynomial `sumSq ps` of total degree at most `2 * d`
   whose zeros over any linearly ordered commutative ring coincide with the common zeros of `ps`.
2. **Lagrange four-squares bounds and `ℕ`-to-`ℤ` translation**: quadratic encoding of strict
   inequalities `r < m` over `ℕ`, and substitution of sums of four squares reducing natural-number
   solvability of a polynomial (or quadratic system) to integer solvability at double (or equal
   quadratic-system) total degree.
3. **Balanced recursive monomial shielding (Skolem reduction)**: decomposing each monomial of
   degree `d > k` via balanced binary factorization into `d - 1` quadratic equations
   `y = u * v` of recursion depth `Nat.clog 2 d`, reducing any polynomial `p` over a commutative
   ring to an equisolvable system with quadratic auxiliary equations and reduced polynomial of
   total degree at most `max k 1`, preserving both ring solutions and natural-number solutions.
4. **Single-equation quartic reduction**: combining Skolem reduction at threshold `k = 1` with
   sum-of-squares aggregation (and four-squares variable constraints over `ℤ`) to transform any
   integer polynomial `p` into a single polynomial of total degree at most `4` over `ℕ`
   (`skolemQuarticNat`) and over `ℤ` (`skolemQuarticInt`) preserving natural-number solvability,
   together with the evaluation-preserving translation `polyToMvPoly` from `Poly`.

## Main definitions

* `CslibFrontier.Computability.Diophantine.sumSq`: sum of squares `(ps.map (· ^ 2)).sum` of a list
  of polynomials.
* `CslibFrontier.Computability.Diophantine.lagrangeSubst`: replaces each variable `X i` with a sum
  of four squares.
* `CslibFrontier.Computability.Diophantine.ShieldTree`: balanced binary factorization of a nonempty
  variable list into
  quadratic equations `X (Sum.inr w) - X u * X v`.
* `CslibFrontier.Computability.Diophantine.shieldVarList`: constructs the balanced `ShieldTree` for
  a variable list.
* `CslibFrontier.Computability.Diophantine.SkolemReduction`: equisolvable bounded-degree polynomial
  system produced by
  Skolem monomial shielding.
* `CslibFrontier.Computability.Diophantine.reduceToSystem`: reduces `p : MvPolynomial (Fin n) R` to
  a
  `SkolemReduction` with quadratic shield constraints and reduced polynomial of total degree at
  most `max k 1`.
* `CslibFrontier.Computability.Diophantine.skolemQuarticNat`: single quartic polynomial over `ℤ`
  preserving `ℕ`-roots.
* `CslibFrontier.Computability.Diophantine.skolemQuarticInt`: single quartic polynomial over `ℤ`
  whose `ℤ`-roots
  correspond to `ℕ`-roots of the input polynomial.
* `CslibFrontier.Computability.Diophantine.polyToMvPoly`: translates `Poly σ` to `MvPolynomial σ ℤ`.

## Main results

* `CslibFrontier.Computability.Diophantine.eval_sumSq_eq_zero_iff`: `sumSq ps` vanishes iff every `p
  ∈ ps` vanishes.
* `CslibFrontier.Computability.Diophantine.totalDegree_sumSq_le`: `(sumSq ps).totalDegree ≤ 2 * d`.
* `CslibFrontier.Computability.Diophantine.nat_lt_iff_exists_four_squares`: quadratic four-squares
  characterization of
  `r < m` in `ℕ`.
* `CslibFrontier.Computability.Diophantine.exists_int_eval_lagrangeSubst_eq_zero_iff`:
  `lagrangeSubst p` has a root in
  `ℤ` iff `p` has a root in `ℕ`.
* `CslibFrontier.Computability.Diophantine.shieldVarList_auxCount`: balanced shielding of a
  degree-`d` monomial
  (`d ≥ 1`) introduces exactly `d - 1` auxiliary variables and quadratic constraints.
* `CslibFrontier.Computability.Diophantine.shieldVarList_depth`: balanced shielding has recursion
  depth `Nat.clog 2 d`.
* `CslibFrontier.Computability.Diophantine.exists_eval_reduceToSystem_iff` and
  `CslibFrontier.Computability.Diophantine.exists_nat_eval_reduceToSystem_iff`: Skolem reduction
  preserves solvability
  over any commutative ring and over `ℕ`.
* `CslibFrontier.Computability.Diophantine.totalDegree_skolemQuarticNat_le`,
  `CslibFrontier.Computability.Diophantine.exists_nat_eval_skolemQuarticNat_iff`,
  `CslibFrontier.Computability.Diophantine.totalDegree_skolemQuarticInt_le`,
  `CslibFrontier.Computability.Diophantine.exists_int_eval_skolemQuarticInt_iff`: single-equation
  degree-`4` reduction
  over `ℕ` and over `ℤ`.

## Tags

Diophantine equations, Skolem reduction, degree reduction, four-square theorem, quartic equations
-/

public section

namespace CslibFrontier.Computability.Diophantine

open MvPolynomial

/-! ### Sum-of-squares system aggregation -/

section SumSq

/-- The sum of squares `∑ p ∈ ps, p ^ 2` of a list of multivariate polynomials. -/
public noncomputable def sumSq {σ R : Type*} [CommSemiring R]
    (ps : List (MvPolynomial σ R)) : MvPolynomial σ R :=
  (ps.map fun p ↦ p ^ 2).sum

@[simp]
public theorem sumSq_nil {σ R : Type*} [CommSemiring R] :
    sumSq ([] : List (MvPolynomial σ R)) = 0 := by
  simp [sumSq]

@[simp]
public theorem sumSq_cons {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (ps : List (MvPolynomial σ R)) :
    sumSq (p :: ps) = p ^ 2 + sumSq ps := by
  simp [sumSq]

/-- Evaluating `sumSq ps` at `x` yields the sum of squares of the evaluations of `ps` at `x`. -/
public theorem eval_sumSq {σ R : Type*} [CommSemiring R]
    (x : σ → R) (ps : List (MvPolynomial σ R)) :
    eval x (sumSq ps) = (ps.map fun p ↦ eval x p ^ 2).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- Over a linearly ordered commutative ring, `sumSq ps` evaluates nonnegatively everywhere. -/
public theorem eval_sumSq_nonneg {σ R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x : σ → R) (ps : List (MvPolynomial σ R)) :
    0 ≤ eval x (sumSq ps) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [sumSq_cons, map_add, map_pow]
    exact add_nonneg (sq_nonneg _) ih

/-- Over a linearly ordered commutative ring, `sumSq ps` vanishes at `x` if and only if every
polynomial in `ps` vanishes at `x`. -/
public theorem eval_sumSq_eq_zero_iff {σ R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : σ → R} {ps : List (MvPolynomial σ R)} :
    eval x (sumSq ps) = 0 ↔ ∀ p ∈ ps, eval x p = 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [sumSq_cons, map_add, map_pow, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have hp : 0 ≤ eval x p ^ 2 := sq_nonneg _
      have hps : 0 ≤ eval x (sumSq ps) := eval_sumSq_nonneg x ps
      have hp0 : eval x p ^ 2 = 0 := by linarith
      have hps0 : eval x (sumSq ps) = 0 := by linarith
      exact ⟨sq_eq_zero_iff.mp hp0, ih.mp hps0⟩
    · rintro ⟨hp, hps⟩
      rw [hp, ih.mpr hps]
      ring

private theorem totalDegree_list_sum_le {σ R : Type*} [CommSemiring R]
    {ps : List (MvPolynomial σ R)} {d : ℕ} (hd : ∀ p ∈ ps, p.totalDegree ≤ d) :
    ps.sum.totalDegree ≤ d := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.sum_cons]
    refine (totalDegree_add p ps.sum).trans (max_le ?_ ?_)
    · exact hd p List.mem_cons_self
    · exact ih fun q hq ↦ hd q (List.mem_cons_of_mem p hq)

/-- If every polynomial in `ps` has total degree at most `d`, then `sumSq ps` has total degree
at most `2 * d`. -/
public theorem totalDegree_sumSq_le {σ R : Type*} [CommSemiring R]
    {ps : List (MvPolynomial σ R)} {d : ℕ} (hd : ∀ p ∈ ps, p.totalDegree ≤ d) :
    (sumSq ps).totalDegree ≤ 2 * d := by
  apply totalDegree_list_sum_le
  intro q hq
  rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
  calc (p ^ 2).totalDegree
      = (p * p).totalDegree := by rw [sq]
    _ ≤ p.totalDegree + p.totalDegree := totalDegree_mul p p
    _ ≤ d + d := add_le_add (hd p hp) (hd p hp)
    _ = 2 * d := by ring

end SumSq

/-! ### Helper lemmas on total degrees of quadratic gadgets -/

private theorem totalDegree_X_le_one {σ R : Type*} [CommSemiring R] (i : σ) :
    (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  by_cases hR : Nontrivial R
  · exact (totalDegree_X i).le
  · rw [not_nontrivial_iff_subsingleton] at hR
    rw [Subsingleton.elim (X i : MvPolynomial σ R) 0, totalDegree_zero]
    exact Nat.zero_le 1

private theorem totalDegree_X_sq_le_two {σ R : Type*} [CommSemiring R] (i : σ) :
    ((X i : MvPolynomial σ R) ^ 2).totalDegree ≤ 2 := by
  rw [sq]
  exact (totalDegree_mul _ _).trans (add_le_add (totalDegree_X_le_one i) (totalDegree_X_le_one i))

private theorem totalDegree_X_mul_X_le_two {σ R : Type*} [CommSemiring R] (i j : σ) :
    ((X i * X j : MvPolynomial σ R)).totalDegree ≤ 2 :=
  (totalDegree_mul _ _).trans (add_le_add (totalDegree_X_le_one i) (totalDegree_X_le_one j))

private theorem totalDegree_shield_eq_le_two {σ R : Type*} [CommRing R] (w u v : σ) :
    ((X w - X u * X v : MvPolynomial σ R)).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_X_mul_X_le_two u v))
  exact (totalDegree_X_le_one w).trans (by decide)

private theorem totalDegree_fourSq_sum_le_two {σ R : Type*} [CommSemiring R]
    (f : Fin 4 → σ) :
    (∑ j : Fin 4, (X (f j) : MvPolynomial σ R) ^ 2).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun j _ ↦ totalDegree_X_sq_le_two (f j)

private theorem totalDegree_var_sub_fourSq_le_two {σ R : Type*} [CommRing R]
    (v : σ) (f : Fin 4 → σ) :
    ((X v - ∑ j : Fin 4, (X (f j) : MvPolynomial σ R) ^ 2)).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_fourSq_sum_le_two f))
  exact (totalDegree_X_le_one v).trans (by decide)

/-! ### Lagrange four-squares bounds and `ℕ`-to-`ℤ` substitution -/

/-- Lagrange four-squares characterization of strict inequality `r < m` on natural numbers via
two quadratic equations over `ℕ` (evaluated in `ℤ`). -/
public theorem nat_lt_iff_exists_four_squares {r m : ℕ} :
    r < m ↔ ∃ a b c e α β γ δ : ℕ,
      r = a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 ∧
      (m : ℤ) - 1 - (r : ℤ) = (α : ℤ) ^ 2 + (β : ℤ) ^ 2 + (γ : ℤ) ^ 2 + (δ : ℤ) ^ 2 := by
  constructor
  · intro hrm
    obtain ⟨a, b, c, e, hr⟩ := Nat.sum_four_squares r
    obtain ⟨α, β, γ, δ, hu⟩ := Nat.sum_four_squares (m - 1 - r)
    refine ⟨a, b, c, e, α, β, γ, δ, hr.symm, ?_⟩
    have hcast : ((m - 1 - r : ℕ) : ℤ) = (m : ℤ) - 1 - (r : ℤ) := by omega
    rw [← hcast, ← hu]
    push_cast
    ring
  · rintro ⟨_, _, _, _, α, β, γ, δ, _, hu⟩
    have hnn : (0 : ℤ) ≤ (α : ℤ) ^ 2 + (β : ℤ) ^ 2 + (γ : ℤ) ^ 2 + (δ : ℤ) ^ 2 := by positivity
    omega

/-- An integer is nonnegative if and only if it is a sum of four integer squares. -/
public theorem int_nonneg_iff_exists_four_int_sq {z : ℤ} :
    0 ≤ z ↔ ∃ f : Fin 4 → ℤ, z = ∑ j : Fin 4, f j ^ 2 := by
  constructor
  · intro hz
    obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares z.toNat
    refine ⟨![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)], ?_⟩
    have hz' : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    rw [Fin.sum_univ_four, ← hz', ← h]
    simp
  · rintro ⟨f, rfl⟩
    exact Finset.sum_nonneg fun j _ ↦ sq_nonneg (f j)

/-- Substitutes each variable `X i` of `p` with the sum of four squares
`∑ j : Fin 4, X (i, j) ^ 2`, converting natural-number roots to integer roots. -/
public noncomputable def lagrangeSubst {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) : MvPolynomial (σ × Fin 4) R :=
  eval₂ C (fun i ↦ ∑ j : Fin 4, (X (i, j) : MvPolynomial (σ × Fin 4) R) ^ 2) p

/-- Evaluating `lagrangeSubst p` at `y` equals evaluating `p` at `i ↦ ∑ j, y (i, j) ^ 2`. -/
public theorem eval_lagrangeSubst {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (y : σ × Fin 4 → R) :
    eval y (lagrangeSubst p) = eval (fun i ↦ ∑ j : Fin 4, y (i, j) ^ 2) p := by
  unfold lagrangeSubst
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p i hp => simp [eval₂_mul, eval₂_X, hp]

private theorem totalDegree_finsetProd_le {ι σ R : Type*} [CommSemiring R]
    (u : Finset ι) (g : ι → MvPolynomial σ R) :
    (∏ i ∈ u, g i).totalDegree ≤ ∑ i ∈ u, (g i).totalDegree := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

/-- Substituting sums of four squares at most doubles total degree. -/
public theorem totalDegree_lagrangeSubst_le {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    (lagrangeSubst p).totalDegree ≤ 2 * p.totalDegree := by
  classical
  rw [lagrangeSubst, eval₂_eq]
  refine totalDegree_finsetSum_le fun s hs ↦ ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd_le s.support _).trans ?_
  calc ∑ i ∈ s.support, ((∑ j : Fin 4, (X (i,
    j) : MvPolynomial (σ × Fin 4) R) ^ 2) ^ s i).totalDegree
      ≤ ∑ i ∈ s.support, s i * 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact (totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left _ (totalDegree_fourSq_sum_le_two fun j ↦ (i, j)))
    _ = 2 * s.sum (fun _ e ↦ e) := by
        rw [Finsupp.sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ Nat.mul_comm _ _
    _ ≤ 2 * p.totalDegree := Nat.mul_le_mul_left 2 (le_totalDegree hs)

/-- `lagrangeSubst p` has an integer solution if and only if `p` has a natural-number solution. -/
public theorem exists_int_eval_lagrangeSubst_eq_zero_iff {σ : Type*} (p : MvPolynomial σ ℤ) :
    (∃ y : σ × Fin 4 → ℤ, eval y (lagrangeSubst p) = 0) ↔
    (∃ x : σ → ℕ, eval (fun i ↦ (x i : ℤ)) p = 0) := by
  constructor
  · rintro ⟨y, hy⟩
    rw [eval_lagrangeSubst] at hy
    refine ⟨fun i ↦ (∑ j : Fin 4, y (i, j) ^ 2).toNat, ?_⟩
    have hfn : (fun i ↦ (((∑ j : Fin 4, y (i, j) ^ 2).toNat : ℕ) : ℤ)) =
        fun i ↦ ∑ j : Fin 4, y (i, j) ^ 2 :=
      funext fun _ ↦ Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    rwa [hfn]
  · rintro ⟨x, hx⟩
    have hf : ∀ i : σ, ∃ f : Fin 4 → ℤ, (x i : ℤ) = ∑ j : Fin 4, f j ^ 2 := fun i ↦
      int_nonneg_iff_exists_four_int_sq.mp (Nat.cast_nonneg (x i))
    choose f hf using hf
    refine ⟨fun q ↦ f q.1 q.2, ?_⟩
    rw [eval_lagrangeSubst]
    have hfn : (fun i ↦ ∑ j : Fin 4, f i j ^ 2) = fun i ↦ (x i : ℤ) :=
      funext fun i ↦ (hf i).symm
    rwa [hfn]

/-! ### Balanced recursive monomial shielding (Skolem reduction) -/

/-- A quadratic shielding step `X (Sum.inr target) = X left * X right` over variables
`σ ⊕ ℕ`, where `Sum.inl i` are original variables and `Sum.inr w` are fresh shield variables. -/
@[ext]
public structure ShieldEq (σ : Type*) where
  /-- Index of the fresh auxiliary variable introduced by this step. -/
  target : ℕ
  /-- Left factor variable (original or earlier auxiliary). -/
  left : σ ⊕ ℕ
  /-- Right factor variable (original or earlier auxiliary). -/
  right : σ ⊕ ℕ
  deriving DecidableEq

/-- Converts a `ShieldEq σ` into the quadratic polynomial `X (inr target) - X left * X right`. -/
public noncomputable def ShieldEq.toPoly {σ R : Type*} [CommRing R]
    (e : ShieldEq σ) : MvPolynomial (σ ⊕ ℕ) R :=
  X (Sum.inr e.target) - X e.left * X e.right

/-- Every shield polynomial has total degree at most `2`. -/
public theorem ShieldEq.totalDegree_toPoly_le {σ R : Type*} [CommRing R] (e : ShieldEq σ) :
    (e.toPoly (R := R)).totalDegree ≤ 2 :=
  totalDegree_shield_eq_le_two (Sum.inr e.target) e.left e.right

/-- Evaluating `e.toPoly` vanishes iff the target auxiliary variable equals the product of the
left and right factor variables. -/
public theorem ShieldEq.eval_toPoly_eq_zero_iff {σ R : Type*} [CommRing R]
    (e : ShieldEq σ) (x : σ → R) (y : ℕ → R) :
    eval (Sum.elim x y) e.toPoly = 0 ↔
      y e.target = Sum.elim x y e.left * Sum.elim x y e.right := by
  simp [ShieldEq.toPoly, sub_eq_zero]

/-- Output of balanced recursive monomial shielding on a nonempty list of variables: the list of
quadratic shield equations, the replacement variable representing the full product, the number of
auxiliary variables introduced, and the recursion depth. -/
@[ext]
public structure ShieldTree (σ : Type*) where
  /-- Quadratic equations `y_w - u * v = 0` introduced during shielding. -/
  eqs : List (ShieldEq σ)
  /-- Variable (`Sum.inl i` or `Sum.inr w`) representing the shielded monomial. -/
  outVar : σ ⊕ ℕ
  /-- Number of fresh auxiliary variables allocated starting at `offset`. -/
  auxCount : ℕ
  /-- Maximum recursion depth of the balanced factorization tree. -/
  depth : ℕ
  deriving DecidableEq

/-- Internal balanced recursive shielding of a variable list `vs` with proof `vs ≠ []`,
splitting `vs` into prefix of length `⌈d / 2⌉ = (d + 1) / 2` and suffix of length `⌊d / 2⌋ = d / 2`
and allocating fresh auxiliary indices in `[offset, offset + d - 1)`. -/
public def shieldVarListAux {σ : Type*} (offset : ℕ) :
    (vs : List σ) → vs ≠ [] → ShieldTree σ
  | [v], _ => ⟨[], Sum.inl v, 0, 0⟩
  | v₁ :: v₂ :: rest, _ =>
    let vs := v₁ :: v₂ :: rest
    let mid := (vs.length + 1) / 2
    let lhs := vs.take mid
    let rhs := vs.drop mid
    have hlhs_ne : lhs ≠ [] := by
      intro h
      have h0 : lhs.length = 0 := by rw [h]; rfl
      simp only [lhs, mid, vs, List.length_take, List.length_cons] at h0
      omega
    have hrhs_ne : rhs ≠ [] := by
      intro h
      have h0 : rhs.length = 0 := by rw [h]; rfl
      simp only [rhs, mid, vs, List.length_drop, List.length_cons] at h0
      omega
    let tL := shieldVarListAux offset lhs hlhs_ne
    let tR := shieldVarListAux (offset + tL.auxCount) rhs hrhs_ne
    let w := offset + tL.auxCount + tR.auxCount
    { eqs := tL.eqs ++ tR.eqs ++ [⟨w, tL.outVar, tR.outVar⟩]
      outVar := Sum.inr w
      auxCount := tL.auxCount + tR.auxCount + 1
      depth := max tL.depth tR.depth + 1 }
termination_by vs _ => vs.length
decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

/-- Balanced recursive monomial shielding of a nonempty variable list `vs` starting at `offset`. -/
public def shieldVarList {σ : Type*} (offset : ℕ) (vs : List σ) (hne : vs ≠ []) :
    ShieldTree σ :=
  shieldVarListAux offset vs hne

/-- Balanced shielding of a degree-`d` monomial (`d = vs.length ≥ 1`) introduces exactly `d - 1`
auxiliary variables. -/
public theorem shieldVarList_auxCount {σ : Type*} (offset : ℕ) (vs : List σ) (hne : vs ≠ []) :
    (shieldVarList offset vs hne).auxCount = vs.length - 1 := by
  unfold shieldVarList
  fun_induction shieldVarListAux offset vs hne with
  | case1 => rfl
  | case2 offset v₁ v₂ rest _ vs mid lhs rhs hlhs_ne hrhs_ne tL tR w _ ihL _ ihR =>
    change tL.auxCount + tR.auxCount + 1 = vs.length - 1
    rw [ihL, ihR]
    simp only [lhs, rhs, mid, vs, List.length_take, List.length_drop, List.length_cons]
    omega

/-- The number of quadratic shield equations produced equals `auxCount` (`= vs.length - 1`). -/
public theorem shieldVarList_eqs_length {σ : Type*} (offset : ℕ) (vs : List σ) (hne : vs ≠ []) :
    (shieldVarList offset vs hne).eqs.length = (shieldVarList offset vs hne).auxCount := by
  unfold shieldVarList
  fun_induction shieldVarListAux offset vs hne with
  | case1 => rfl
  | case2 offset v₁ v₂ rest _ vs mid lhs rhs hlhs_ne hrhs_ne tL tR w _ ihL _ ihR =>
    change (tL.eqs ++ tR.eqs ++ [ShieldEq.mk w tL.outVar tR.outVar]).length =
      tL.auxCount + tR.auxCount + 1
    simp only [List.length_append, List.length_singleton]
    rw [ihL, ihR]

private theorem clog_two_split (d : ℕ) (hd : 2 ≤ d) :
    max (Nat.clog 2 ((d + 1) / 2)) (Nat.clog 2 (d / 2)) + 1 = Nat.clog 2 d := by
  have hmono : Nat.clog 2 (d / 2) ≤ Nat.clog 2 ((d + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  rw [max_eq_left hmono]
  have hceil : (d + 1) / 2 = (d + 2 - 1) / 2 := by omega
  rw [hceil, ← Nat.clog_of_two_le (by decide : 1 < 2) hd]

/-- Balanced shielding of a degree-`d` monomial (`d = vs.length ≥ 1`) has exact recursion depth
`Nat.clog 2 d = ⌈log₂ d⌉`. -/
public theorem shieldVarList_depth {σ : Type*} (offset : ℕ) (vs : List σ) (hne : vs ≠ []) :
    (shieldVarList offset vs hne).depth = Nat.clog 2 vs.length := by
  unfold shieldVarList
  fun_induction shieldVarListAux offset vs hne with
  | case1 => simp
  | case2 offset v₁ v₂ rest _ vs mid lhs rhs hlhs_ne hrhs_ne tL tR w _ ihL _ ihR =>
    change max tL.depth tR.depth + 1 = Nat.clog 2 vs.length
    have hge2 : 2 ≤ vs.length := by simp [vs]
    have hlhs : lhs.length = (vs.length + 1) / 2 := by
      simp only [lhs, mid, List.length_take]
      omega
    have hrhs : rhs.length = vs.length / 2 := by
      simp only [rhs, mid, List.length_drop]
      omega
    rw [ihL, ihR, hlhs, hrhs]
    exact clog_two_split vs.length hge2

private def varInRange {σ : Type*} (bound : ℕ) : σ ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr w => w < bound

private theorem varInRange_mono {σ : Type*} {a b : ℕ} (hab : a ≤ b) {v : σ ⊕ ℕ}
    (hv : varInRange a v) : varInRange b v := by
  cases v with
  | inl _ => trivial
  | inr w => exact lt_of_lt_of_le hv hab

private theorem shieldVarListAux_bounds {σ : Type*} (offset : ℕ) (vs : List σ) (hne : vs ≠ []) :
    let t := shieldVarListAux offset vs hne
    varInRange (offset + t.auxCount) t.outVar ∧
    (∀ w, t.outVar = Sum.inr w → offset ≤ w) ∧
    ∀ e ∈ t.eqs, offset ≤ e.target ∧ e.target < offset + t.auxCount ∧
      varInRange e.target e.left ∧ varInRange e.target e.right := by
  fun_induction shieldVarListAux offset vs hne with
  | case1 =>
    refine ⟨trivial, ?_, ?_⟩
    · rintro w ⟨⟩
    · rintro e ⟨⟩
  | case2 offset v₁ v₂ rest _ vs mid lhs rhs hlhs_ne hrhs_ne tL tR w _ ihL _ ihR =>
    rcases ihL with ⟨houtL, _, heqsL⟩
    rcases ihR with ⟨houtR, _, heqsR⟩
    have hw : w = offset + tL.auxCount + tR.auxCount := rfl
    have htL : (shieldVarListAux offset lhs hlhs_ne).auxCount = tL.auxCount := rfl
    have htR : (shieldVarListAux (offset + tL.auxCount) rhs hrhs_ne).auxCount = tR.auxCount := rfl
    have htL : (shieldVarListAux offset lhs hlhs_ne).auxCount = tL.auxCount := rfl
    have htR : (shieldVarListAux (offset + tL.auxCount) rhs hrhs_ne).auxCount = tR.auxCount := rfl
    refine ⟨?_, ?_, ?_⟩
    · change w < offset + (tL.auxCount + tR.auxCount + 1)
      omega
    · intro u hu
      cases hu
      omega
    · intro e he
      dsimp only at he ⊢
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with (he | he) | rfl
      · obtain ⟨h1, h2, h3, h4⟩ := heqsL e he
        exact ⟨h1, by omega, h3, h4⟩
      · obtain ⟨h1, h2, h3, h4⟩ := heqsR e he
        exact ⟨by omega, by omega, h3, h4⟩
      · dsimp only
        exact ⟨by omega, by omega,
          varInRange_mono (by omega) houtL, varInRange_mono (by omega) houtR⟩

/-- All variables appearing in `shieldVarList offset vs hne` have auxiliary index strictly below
`offset + auxCount`. -/
public theorem shieldVarList_indices_lt {σ : Type*} (offset : ℕ) (vs : List σ) (hne : vs ≠ []) :
    let t := shieldVarList offset vs hne
    (∀ w, t.outVar = Sum.inr w → w < offset + t.auxCount) ∧
    ∀ e ∈ t.eqs, e.target < offset + t.auxCount ∧
      (∀ w, e.left = Sum.inr w → w < offset + t.auxCount) ∧
      (∀ w, e.right = Sum.inr w → w < offset + t.auxCount) := by
  obtain ⟨hout, _, heqs⟩ := shieldVarListAux_bounds offset vs hne
  refine ⟨?_, ?_⟩
  · intro w hw
    change (shieldVarListAux offset vs hne).outVar = Sum.inr w at hw
    change varInRange _ (shieldVarListAux offset vs hne).outVar at hout
    rw [hw] at hout
    exact hout
  · intro e he
    obtain ⟨_, ht, hl, hr⟩ := heqs e he
    refine ⟨ht, ?_, ?_⟩
    · intro w hw; rw [hw] at hl; exact lt_trans hl ht
    · intro w hw; rw [hw] at hr; exact lt_trans hr ht

/-- Soundness of balanced shielding: any assignment `(x, y)` satisfying all shield equations maps
`outVar` to the product `(vs.map x).prod`. -/
public theorem shieldVarList_sound {σ R : Type*} [CommRing R]
    (offset : ℕ) (vs : List σ) (hne : vs ≠ []) (x : σ → R) (y : ℕ → R)
    (h : ∀ e ∈ (shieldVarList offset vs hne).eqs, eval (Sum.elim x y) e.toPoly = 0) :
    Sum.elim x y (shieldVarList offset vs hne).outVar = (vs.map x).prod := by
  unfold shieldVarList at h ⊢
  fun_induction shieldVarListAux offset vs hne with
  | case1 offset v => simp
  | case2 offset v₁ v₂ rest _ vs mid lhs rhs hlhs_ne hrhs_ne tL tR w _ ihL _ ihR =>
    have hL : ∀ e ∈ tL.eqs, eval (Sum.elim x y) e.toPoly = 0 := fun e he ↦
      h e (List.mem_append_left _ (List.mem_append_left _ he))
    have hR : ∀ e ∈ tR.eqs, eval (Sum.elim x y) e.toPoly = 0 := fun e he ↦
      h e (List.mem_append_left _ (List.mem_append_right _ he))
    have hW : eval (Sum.elim x y) (ShieldEq.mk w tL.outVar tR.outVar).toPoly = 0 :=
      h ⟨w, tL.outVar, tR.outVar⟩ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [ShieldEq.eval_toPoly_eq_zero_iff] at hW
    change y w = (vs.map x).prod
    rw [hW, ihL hL, ihR hR, ← List.prod_append, ← List.map_append]
    simp only [lhs, rhs, List.take_append_drop]

private theorem sumElim_congr_varInRange {σ α : Type*} {bound : ℕ} (x : σ → α)
    {y₁ y₂ : ℕ → α} (hy : ∀ k < bound, y₁ k = y₂ k) {v : σ ⊕ ℕ} (hv : varInRange bound v) :
    Sum.elim x y₁ v = Sum.elim x y₂ v := by
  cases v with
  | inl _ => rfl
  | inr k => exact hy k hv

private theorem eval_shieldEq_congr {σ R : Type*} [CommRing R] {offset bound : ℕ}
    {e : ShieldEq σ} (ht : e.target < bound) (hl : varInRange e.target e.left)
    (hr : varInRange e.target e.right) (x : σ → R) {y₁ y₂ : ℕ → R}
    (hy : ∀ k, k < bound → offset ≤ k → y₁ k = y₂ k)
    (hy_low : ∀ k < offset, y₁ k = y₂ k) :
    eval (Sum.elim x y₁) e.toPoly = eval (Sum.elim x y₂) e.toPoly := by
  have hall : ∀ k < bound, y₁ k = y₂ k := fun k hk ↦
    if h : offset ≤ k then hy k hk h else hy_low k (by omega)
  simp only [ShieldEq.toPoly, map_sub, map_mul, eval_X, Sum.elim_inr]
  rw [hall e.target ht,
    sumElim_congr_varInRange x hall (varInRange_mono ht.le hl),
    sumElim_congr_varInRange x hall (varInRange_mono ht.le hr)]

/-- Completeness of balanced shielding over any semiring `S` mapped into `R` (setting `S = R` gives
ring witnesses and `S = ℕ`, `R = ℤ` gives natural-number witnesses directly): given `x : σ → S`
and any initial `y₀ : ℕ → S`, there exists `y : ℕ → S` agreeing with `y₀` outside
`[offset, offset + auxCount)` such that all shield equations vanish under `f`. -/
public theorem shieldVarList_complete {σ S R : Type*} [CommSemiring S] [CommRing R]
    (f : S →+* R) (offset : ℕ) (vs : List σ) (hne : vs ≠ []) (x : σ → S) (y₀ : ℕ → S) :
    ∃ y : ℕ → S,
      (∀ k, k < offset ∨ offset + (shieldVarList offset vs hne).auxCount ≤ k → y k = y₀ k) ∧
      (∀ e ∈ (shieldVarList offset vs hne).eqs,
        eval (Sum.elim (f ∘ x) (f ∘ y)) e.toPoly = 0) ∧
      Sum.elim x y (shieldVarList offset vs hne).outVar = (vs.map x).prod := by
  unfold shieldVarList
  fun_induction shieldVarListAux offset vs hne generalizing y₀ with
  | case1 offset v =>
    refine ⟨y₀, fun _ _ ↦ rfl, ?_, by simp⟩
    rintro e ⟨⟩
  | case2 offset v₁ v₂ rest _ vs mid lhs rhs hlhs_ne hrhs_ne tL tR w _ ihL _ ihR =>
    obtain ⟨y₁, hy₁_out, hy₁_eqs, hy₁_val⟩ := ihL y₀
    obtain ⟨y₂, hy₂_out, hy₂_eqs, hy₂_val⟩ := ihR y₁
    have hw : w = offset + tL.auxCount + tR.auxCount := rfl
    have htL : (shieldVarListAux offset lhs hlhs_ne).auxCount = tL.auxCount := rfl
    have htR : (shieldVarListAux (offset + tL.auxCount) rhs hrhs_ne).auxCount = tR.auxCount := rfl
    let valL := Sum.elim x y₂ tL.outVar
    let valR := Sum.elim x y₂ tR.outVar
    let y₃ : ℕ → S := fun k ↦ if k = w then valL * valR else y₂ k
    obtain ⟨houtL, _, heqsL⟩ := shieldVarListAux_bounds offset lhs hlhs_ne
    obtain ⟨houtR, _, heqsR⟩ := shieldVarListAux_bounds (offset + tL.auxCount) rhs hrhs_ne
    change varInRange (offset + tL.auxCount) tL.outVar at houtL
    change ∀ e ∈ tL.eqs, offset ≤ e.target ∧ e.target < offset + tL.auxCount ∧
      varInRange e.target e.left ∧ varInRange e.target e.right at heqsL
    change varInRange (offset + tL.auxCount + tR.auxCount) tR.outVar at houtR
    change ∀ e ∈ tR.eqs, offset + tL.auxCount ≤ e.target ∧
      e.target < offset + tL.auxCount + tR.auxCount ∧
      varInRange e.target e.left ∧ varInRange e.target e.right at heqsR
    have hy₂₁ : ∀ k < offset + tL.auxCount, y₂ k = y₁ k := fun k hk ↦ hy₂_out k (Or.inl hk)
    have hy₃₂ : ∀ k < w, y₃ k = y₂ k := fun k hk ↦ ite_eq_right (by omega)
    have hvalL : valL = (lhs.map x).prod := by
      rw [← hy₁_val]
      exact sumElim_congr_varInRange x hy₂₁ houtL
    have hvalR : valR = (rhs.map x).prod := hy₂_val
    refine ⟨y₃, ?_, ?_, ?_⟩
    · intro k hk
      change k < offset ∨ offset + (tL.auxCount + tR.auxCount + 1) ≤ k at hk
      have hkw : k ≠ w := by omega
      simp only [y₃, ite_eq_right hkw]
      rcases hk with hk | hk
      · rw [hy₂_out k (Or.inl (by omega)), hy₁_out k (Or.inl hk)]
      · rw [hy₂_out k (Or.inr (by omega)), hy₁_out k (Or.inr (by omega))]
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with (he | he) | rfl
      · obtain ⟨_, ht, hl, hr⟩ := heqsL e he
        have h31 : ∀ k < offset + tL.auxCount, (f ∘ y₃) k = (f ∘ y₁) k := fun k hk ↦ by
          simp only [Function.comp_apply, hy₃₂ k (by omega), hy₂₁ k hk]
        rw [eval_shieldEq_congr ht hl hr (f ∘ x) (fun k hk _ ↦ h31 k hk)
          (fun k hk ↦ h31 k (by omega))]
        exact hy₁_eqs e he
      · obtain ⟨_, ht, hl, hr⟩ := heqsR e he
        have h32 : ∀ k < w, (f ∘ y₃) k = (f ∘ y₂) k := fun k hk ↦ by
          simp only [Function.comp_apply, hy₃₂ k hk]
        rw [eval_shieldEq_congr ht hl hr (f ∘ x) (fun k hk _ ↦ h32 k hk)
          (fun k hk ↦ h32 k (by omega))]
        exact hy₂_eqs e he
      · rw [ShieldEq.eval_toPoly_eq_zero_iff]
        have hL' : Sum.elim (f ∘ x) (f ∘ y₃) tL.outVar = f valL := by
          rw [sumElim_congr_varInRange (f ∘ x) (y₁ := f ∘ y₃) (y₂ := f ∘ y₂)
            (fun k hk ↦ congrArg f (hy₃₂ k hk)) (varInRange_mono (by omega) houtL)]
          dsimp only [valL]; cases tL.outVar <;> rfl
        have hR' : Sum.elim (f ∘ x) (f ∘ y₃) tR.outVar = f valR := by
          rw [sumElim_congr_varInRange (f ∘ x) (y₁ := f ∘ y₃) (y₂ := f ∘ y₂)
            (fun k hk ↦ congrArg f (hy₃₂ k hk)) (varInRange_mono (by omega) houtR)]
          dsimp only [valR]; cases tR.outVar <;> rfl
        simp only [Function.comp_apply, y₃, ↓reduceIte, hL', hR', map_mul]
    · change y₃ w = (vs.map x).prod
      simp only [y₃, ↓reduceIte, hvalL, hvalR, ← List.prod_append, ← List.map_append,
        lhs, rhs, List.take_append_drop]

/-! ### Expanding monomials to sorted variable lists and polynomial Skolem reduction -/

/-- Expands a monomial exponent vector `s : Fin n →₀ ℕ` into an explicit list of variable indices
whose multiplicities match `s`, with length equal to `s.sum (fun _ e ↦ e)`. -/
public def monomialToVarList {n : ℕ} (s : Fin n →₀ ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun i ↦ List.replicate (s i) i

/-- The length of `monomialToVarList s` equals the total degree `s.sum (fun _ e ↦ e)` of `s`. -/
public theorem length_monomialToVarList {n : ℕ} (s : Fin n →₀ ℕ) :
    (monomialToVarList s).length = s.sum (fun _ e ↦ e) := by
  classical
  simp only [monomialToVarList, List.length_flatMap, List.length_replicate, Finsupp.sum]
  have h1 : ((List.finRange n).map fun i ↦ s i).sum = ∑ i : Fin n, s i :=
    (Fin.sum_univ_def fun i ↦ s i).symm
  rw [h1]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ Finsupp.notMem_support_iff.mp hi

/-- The product of `x` along `monomialToVarList s` equals `∏ i, x i ^ s i`. -/
public theorem prod_map_monomialToVarList {n : ℕ} {S : Type*} [CommMonoid S]
    (s : Fin n →₀ ℕ) (x : Fin n → S) :
    ((monomialToVarList s).map x).prod = s.prod (fun i e ↦ x i ^ e) := by
  classical
  have hflat : ((monomialToVarList s).map x).prod =
      ((List.finRange n).map fun i ↦ x i ^ s i).prod := by
    unfold monomialToVarList
    induction (List.finRange n) with
    | nil => simp
    | cons i is ih =>
      simp [List.flatMap_cons, List.map_append, List.prod_append, List.map_replicate,
        List.prod_replicate, ih]
  rw [hflat]
  have h1 : ((List.finRange n).map fun i ↦ x i ^ s i).prod = ∏ i : Fin n, x i ^ s i :=
    (Fin.prod_univ_def fun i ↦ x i ^ s i).symm
  rw [h1, Finsupp.prod]
  symm
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

private noncomputable def clampShieldEq {n m : ℕ} {R : Type*} [CommRing R]
    (hm : 0 < m) (e : ShieldEq (Fin n)) : MvPolynomial (Fin n ⊕ Fin m) R :=
  let f : Fin n ⊕ ℕ → Fin n ⊕ Fin m := fun
    | Sum.inl i => Sum.inl i
    | Sum.inr w => if hw : w < m then Sum.inr ⟨w, hw⟩ else Sum.inr ⟨0, hm⟩
  X (f (Sum.inr e.target)) - X (f e.left) * X (f e.right)

private theorem totalDegree_clampShieldEq_le {n m : ℕ} {R : Type*} [CommRing R]
    (hm : 0 < m) (e : ShieldEq (Fin n)) :
    (clampShieldEq (R := R) hm e).totalDegree ≤ 2 :=
  totalDegree_shield_eq_le_two _ _ _

private theorem eval_clampShieldEq {n m : ℕ} {R : Type*} [CommRing R]
    (hm : 0 < m) {e : ShieldEq (Fin n)}
    (ht : e.target < m) (hl : ∀ w, e.left = Sum.inr w → w < m)
    (hr : ∀ w, e.right = Sum.inr w → w < m)
    (x : Fin n → R) (y : Fin m → R) (yExt : ℕ → R)
    (hy : ∀ k (hk : k < m), yExt k = y ⟨k, hk⟩) :
    eval (Sum.elim x y) (clampShieldEq hm e) = eval (Sum.elim x yExt) e.toPoly := by
  simp only [clampShieldEq, ShieldEq.toPoly, map_sub, map_mul, eval_X,
    dite_eq_left ht, Sum.elim_inr, hy e.target ht]
  congr 2
  · cases h : e.left with
    | inl i => rfl
    | inr w => simp [dite_eq_left (hl w h), hy w (hl w h)]
  · cases h : e.right with
    | inl i => rfl
    | inr w => simp [dite_eq_left (hr w h), hy w (hr w h)]

/-- Accumulator folding Skolem monomial shielding across a list of `(monomial, coeff)` terms
for degree threshold `k`. Terms of degree `≤ max k 1` remain untouched; terms of degree
`> max k 1` (hence `≥ 2`) are shielded to a single linear term `C c * X outVar`. -/
private noncomputable def reduceTerms {n : ℕ} {R : Type*} [CommRing R] (k : ℕ) :
    List ((Fin n →₀ ℕ) × R) → ℕ →
      List (ShieldEq (Fin n)) × MvPolynomial (Fin n ⊕ ℕ) R × ℕ
  | [], offset => ([], 0, offset)
  | (s, c) :: rest, offset =>
    if hdeg : max k 1 < s.sum (fun _ e ↦ e) then
      let vs := monomialToVarList s
      have hvs_ne : vs ≠ [] := by
        intro h
        have h0 : (monomialToVarList s).length = 0 := by
          rw [show monomialToVarList s = vs from rfl, h]; rfl
        rw [length_monomialToVarList] at h0
        omega
      let t := shieldVarList offset vs hvs_ne
      let (eqsRest, polyRest, finalOff) := reduceTerms k rest (offset + t.auxCount)
      (t.eqs ++ eqsRest, C c * X t.outVar + polyRest, finalOff)
    else
      let term : MvPolynomial (Fin n ⊕ ℕ) R := rename Sum.inl (monomial s c)
      let (eqsRest, polyRest, finalOff) := reduceTerms k rest offset
      (eqsRest, term + polyRest, finalOff)

private theorem reduceTerms_spec {n : ℕ} {R : Type*} [CommRing R] (k : ℕ)
    (terms : List ((Fin n →₀ ℕ) × R)) (offset : ℕ) :
    let res := reduceTerms k terms offset
    offset ≤ res.2.2 ∧
    res.1.length = res.2.2 - offset ∧
    res.2.1.totalDegree ≤ max k 1 ∧
    (∀ v ∈ res.2.1.vars, ∀ w, v = Sum.inr w → w < res.2.2) ∧
    (∀ e ∈ res.1, e.target < res.2.2 ∧
      (∀ w, e.left = Sum.inr w → w < res.2.2) ∧
      (∀ w, e.right = Sum.inr w → w < res.2.2)) ∧
    (∀ (x : Fin n → R) (y : ℕ → R),
      (∀ e ∈ res.1, eval (Sum.elim x y) e.toPoly = 0) →
      eval (Sum.elim x y) res.2.1 =
        (terms.map fun sc ↦ eval x (monomial sc.1 sc.2)).sum) ∧
    (∀ {d : ℕ}, (∀ sc ∈ terms, sc.1.sum (fun _ e ↦ e) ≤ d) →
      res.2.2 - offset ≤ terms.length * (d - 1)) := by
  induction terms generalizing offset with
  | nil =>
    refine ⟨le_rfl, by simp [reduceTerms], by simp [reduceTerms], ?_, ?_, ?_, ?_⟩
    · intro v hv
      simp [reduceTerms] at hv
    · intro e he
      simp [reduceTerms] at he
    · intro x y _
      simp [reduceTerms]
    · intro d _
      simp [reduceTerms]
  | cons sc rest ih =>
    rcases sc with ⟨s, c⟩
    by_cases hdeg : max k 1 < s.sum (fun _ e ↦ e)
    · have hvs_ne : monomialToVarList s ≠ [] := by
        intro h
        have h0 : (monomialToVarList s).length = 0 := by rw [h]; rfl
        rw [length_monomialToVarList] at h0
        omega
      let t := shieldVarList offset (monomialToVarList s) hvs_ne
      obtain ⟨hoff, hlen, htd, hvars, heqs, hsound, hcnt⟩ := ih (offset + t.auxCount)
      obtain ⟨hout_lt, hteqs_lt⟩ := shieldVarList_indices_lt offset (monomialToVarList s) hvs_ne
      have hres : reduceTerms k ((s, c) :: rest) offset =
          (t.eqs ++ (reduceTerms k rest (offset + t.auxCount)).1,
           C c * X t.outVar + (reduceTerms k rest (offset + t.auxCount)).2.1,
           (reduceTerms k rest (offset + t.auxCount)).2.2) := by
        simp [reduceTerms, hdeg, t]
      rw [hres]
      refine ⟨Nat.le_trans (Nat.le_add_right offset t.auxCount) hoff, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, shieldVarList_eqs_length, hlen]
        change t.auxCount + ((reduceTerms k rest (offset + t.auxCount)).2.2 -
          (offset + t.auxCount)) = (reduceTerms k rest (offset + t.auxCount)).2.2 - offset
        omega
      · refine (totalDegree_add _ _).trans (max_le ?_ htd)
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        exact (totalDegree_X_le_one t.outVar).trans (le_max_right k 1)
      · intro v hv w hw
        classical
        have hv' := vars_add_subset _ _ hv
        rcases Finset.mem_union.mp hv' with hv1 | hv2
        · have hv1' := vars_mul _ _ hv1
          rcases Finset.mem_union.mp hv1' with hvc | hvx
          · simp [vars_C] at hvc
          · have hveq : v = t.outVar := by
              by_cases hR : Nontrivial R
              · rw [vars_X] at hvx
                exact Finset.mem_singleton.mp hvx
              · rw [not_nontrivial_iff_subsingleton] at hR
                rw [Subsingleton.elim (X t.outVar : MvPolynomial _ R) 0] at hvx
                simp at hvx
            exact lt_of_lt_of_le (hout_lt w (hveq.symm.trans hw)) hoff
        · exact hvars v hv2 w hw
      · intro e he
        rcases List.mem_append.mp he with he1 | he2
        · obtain ⟨ht1, hl1, hr1⟩ := hteqs_lt e he1
          exact ⟨lt_of_lt_of_le ht1 hoff, fun w hw ↦ lt_of_lt_of_le (hl1 w hw) hoff,
            fun w hw ↦ lt_of_lt_of_le (hr1 w hw) hoff⟩
        · exact heqs e he2
      · intro x y hall
        have h1 : ∀ e ∈ t.eqs, eval (Sum.elim x y) e.toPoly = 0 := fun e he ↦
          hall e (List.mem_append_left _ he)
        have h2 : ∀ e ∈ (reduceTerms k rest (offset + t.auxCount)).1,
            eval (Sum.elim x y) e.toPoly = 0 := fun e he ↦
          hall e (List.mem_append_right _ he)
        simp only [map_add, map_mul, eval_C, eval_X, List.map_cons, List.sum_cons]
        rw [hsound x y h2, shieldVarList_sound offset (monomialToVarList s) hvs_ne x y h1,
          prod_map_monomialToVarList, eval_monomial]
      · intro d hd
        have hsd : s.sum (fun _ e ↦ e) ≤ d := hd (s, c) List.mem_cons_self
        have htaux : t.auxCount ≤ d - 1 := by
          rw [shieldVarList_auxCount, length_monomialToVarList]
          omega
        have hrest : (reduceTerms k rest (offset + t.auxCount)).2.2 - (offset + t.auxCount) ≤
            rest.length * (d - 1) :=
          hcnt fun sc hsc ↦ hd sc (List.mem_cons_of_mem _ hsc)
        simp only [List.length_cons, Nat.succ_mul]
        omega
    · obtain ⟨hoff, hlen, htd, hvars, heqs, hsound, hcnt⟩ := ih offset
      have hres : reduceTerms k ((s, c) :: rest) offset =
          ((reduceTerms k rest offset).1,
           rename Sum.inl (monomial s c) + (reduceTerms k rest offset).2.1,
           (reduceTerms k rest offset).2.2) := by
        simp [reduceTerms, hdeg]
      rw [hres]
      refine ⟨hoff, hlen, ?_, ?_, heqs, ?_, ?_⟩
      · refine (totalDegree_add _ _).trans (max_le ?_ htd)
        refine (totalDegree_rename_le Sum.inl (monomial s c)).trans ?_
        exact (totalDegree_monomial_le s c).trans (le_of_not_gt hdeg)
      · intro v hv w hw
        classical
        rcases Finset.mem_union.mp (vars_add_subset _ _ hv) with hv1 | hv2
        · have hv1' := vars_rename Sum.inl (monomial s c) hv1
          rcases Finset.mem_image.mp hv1' with ⟨i, _, hi⟩
          rw [← hi] at hw
          cases hw
        · exact hvars v hv2 w hw
      · intro x y hall
        simp only [map_add, eval_rename, List.map_cons, List.sum_cons]
        rw [hsound x y hall]
        rfl
      · intro d hd
        have hrest := hcnt fun sc hsc ↦ hd sc (List.mem_cons_of_mem _ hsc)
        simp only [List.length_cons, Nat.succ_mul]
        omega

private theorem reduceTerms_complete {n : ℕ} {S R : Type*} [CommSemiring S] [CommRing R]
    (f : S →+* R) (k : ℕ) (terms : List ((Fin n →₀ ℕ) × R)) (offset : ℕ)
    (x : Fin n → S) (y₀ : ℕ → S) :
    ∃ y : ℕ → S,
      (∀ j < offset, y j = y₀ j) ∧
      ∀ e ∈ (reduceTerms k terms offset).1,
        eval (Sum.elim (f ∘ x) (f ∘ y)) e.toPoly = 0 := by
  induction terms generalizing offset y₀ with
  | nil => exact ⟨y₀, fun _ _ ↦ rfl, by simp [reduceTerms]⟩
  | cons sc rest ih =>
    rcases sc with ⟨s, c⟩
    by_cases hdeg : max k 1 < s.sum (fun _ e ↦ e)
    · have hvs_ne : monomialToVarList s ≠ [] := by
        intro h
        have h0 : (monomialToVarList s).length = 0 := by rw [h]; rfl
        rw [length_monomialToVarList] at h0
        omega
      set t := shieldVarList offset (monomialToVarList s) hvs_ne
      obtain ⟨y₁, hy₁_out, hy₁_eqs, _⟩ :=
        shieldVarList_complete f offset (monomialToVarList s) hvs_ne x y₀
      obtain ⟨y₂, hy₂_low, hy₂_eqs⟩ := ih (offset + t.auxCount) y₁
      obtain ⟨_, _, hteqs_b⟩ :=
        shieldVarListAux_bounds offset (monomialToVarList s) hvs_ne
      refine ⟨y₂, fun j hj ↦ (hy₂_low j (by omega)).trans (hy₁_out j (Or.inl hj)), ?_⟩
      intro e he
      have hres : (reduceTerms k ((s, c) :: rest) offset).1 =
          t.eqs ++ (reduceTerms k rest (offset + t.auxCount)).1 := by
        simp [reduceTerms, hdeg, t]
      rw [hres] at he
      rcases List.mem_append.mp he with he1 | he2
      · obtain ⟨_, ht, hl, hr⟩ := hteqs_b e he1
        have h21 : ∀ j < offset + t.auxCount, (f ∘ y₂) j = (f ∘ y₁) j := fun j hj ↦
          congrArg f (hy₂_low j hj)
        rw [eval_shieldEq_congr ht hl hr (f ∘ x) (fun j hj _ ↦ h21 j hj)
          (fun j hj ↦ h21 j (by omega))]
        exact hy₁_eqs e he1
      · exact hy₂_eqs e he2
    · have hres : (reduceTerms k ((s, c) :: rest) offset).1 =
          (reduceTerms k rest offset).1 := by
        simp [reduceTerms, hdeg]
      rw [hres]
      exact ih offset y₀

/-- An equisolvable bounded-degree polynomial system over `n` original variables and `auxVars`
auxiliary variables (`Fin n ⊕ Fin auxVars`), consisting of quadratic shield equations `constraints`
and a reduced polynomial `reduced`. -/
@[ext]
public structure SkolemReduction (n : ℕ) (R : Type*) [CommRing R] where
  /-- Number of fresh auxiliary variables introduced by monomial shielding. -/
  auxVars : ℕ
  /-- Quadratic shield constraints `y_w - u * v = 0`, each of total degree at most `2`. -/
  constraints : List (MvPolynomial (Fin n ⊕ Fin auxVars) R)
  /-- Reduced polynomial obtained by substituting auxiliary variables for high-degree monomials. -/
  reduced : MvPolynomial (Fin n ⊕ Fin auxVars) R

/-- All polynomials of a `SkolemReduction` collected into a single list `reduced :: constraints`. -/
public def SkolemReduction.allPolys {n : ℕ} {R : Type*} [CommRing R]
    (sys : SkolemReduction n R) : List (MvPolynomial (Fin n ⊕ Fin sys.auxVars) R) :=
  sys.reduced :: sys.constraints

private def clampAuxVar {n m : ℕ} (hm : 0 < m) : Fin n ⊕ ℕ → Fin n ⊕ Fin m
  | Sum.inl i => Sum.inl i
  | Sum.inr w => if hw : w < m then Sum.inr ⟨w, hw⟩ else Sum.inr ⟨0, hm⟩

private theorem eval_congr_vars {σ R : Type*} [CommSemiring R]
    (q : MvPolynomial σ R) {f g : σ → R}
    (h : ∀ v, (∃ s ∈ q.support, v ∈ s.support) → f v = g v) :
    eval f q = eval g q := by
  classical
  rw [q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  simp only [eval_monomial, Finsupp.prod]
  congr 1
  exact Finset.prod_congr rfl fun v hv ↦ by rw [h v ⟨s, hs, hv⟩]

/-- Reduces a multivariate polynomial `p : MvPolynomial (Fin n) R` to an equisolvable
`SkolemReduction n R` with quadratic shield constraints (total degree `≤ 2`) and reduced polynomial
of total degree `≤ max k 1`. Setting `k = 3` reduces to a cubic system (`totalDegree ≤ 3`);
setting `k = 1` reduces to a quadratic system (`totalDegree ≤ 2`, with `reduced` linear). -/
public noncomputable def reduceToSystem {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R) : SkolemReduction n R := by
  classical
  let terms := p.support.toList.map fun s ↦ (s, p.coeff s)
  let res := reduceTerms k terms 0
  let m := res.2.2
  exact
    { auxVars := m
      constraints := if hm : 0 < m then res.1.map (clampShieldEq hm) else []
      reduced := if hm : 0 < m then rename (clampAuxVar hm) res.2.1 else rename Sum.inl p }

/-- Every shield constraint in `reduceToSystem k p` has total degree at most `2`. -/
public theorem totalDegree_mem_constraints_reduceToSystem_le {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R)
    {c : MvPolynomial (Fin n ⊕ Fin (reduceToSystem k p).auxVars) R}
    (hc : c ∈ (reduceToSystem k p).constraints) :
    c.totalDegree ≤ 2 := by
  simp only [reduceToSystem] at hc
  split_ifs at hc with hm
  · rcases List.mem_map.mp hc with ⟨e, _, rfl⟩
    exact totalDegree_clampShieldEq_le hm e
  · cases hc

/-- The reduced polynomial of `reduceToSystem k p` has total degree at most `max k 1`. -/
public theorem totalDegree_reduced_reduceToSystem_le {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R) :
    (reduceToSystem k p).reduced.totalDegree ≤ max k 1 := by
  classical
  let terms := p.support.toList.map fun s ↦ (s, p.coeff s)
  obtain ⟨_, _, htd, _, _, _, _⟩ := reduceTerms_spec k terms 0
  change (if hm : 0 < (reduceTerms k terms 0).2.2 then
      rename (clampAuxVar hm) (reduceTerms k terms 0).2.1
    else rename Sum.inl p).totalDegree ≤ max k 1
  split_ifs with hm
  · exact (totalDegree_rename_le _ _).trans htd
  · refine (totalDegree_rename_le _ _).trans ?_
    rw [totalDegree]
    refine Finset.sup_le fun s hs ↦ ?_
    by_contra hgt
    push Not at hgt
    have hmem : (s, p.coeff s) ∈ terms :=
      List.mem_map.mpr ⟨s, Finset.mem_toList.mpr hs, rfl⟩
    have hm0 : (reduceTerms k terms 0).2.2 = 0 := by omega
    have hpos : ∀ (ts : List ((Fin n →₀ ℕ) × R)) (off : ℕ),
        (s, p.coeff s) ∈ ts → 0 < (reduceTerms k ts off).2.2 - off := by
      intro ts
      induction ts with
      | nil => intro _ h; cases h
      | cons sc rest ih =>
        intro off hsc
        rcases sc with ⟨s', c'⟩
        rcases List.mem_cons.mp hsc with heq | hrest
        · cases heq
          have hvs_ne : monomialToVarList s ≠ [] := by
            intro h
            have h0 : (monomialToVarList s).length = 0 := by rw [h]; rfl
            rw [length_monomialToVarList] at h0
            omega
          let t := shieldVarList off (monomialToVarList s) hvs_ne
          have htpos : 0 < t.auxCount := by
            rw [shieldVarList_auxCount, length_monomialToVarList]
            omega
          obtain ⟨hoff2, _, _, _, _, _, _⟩ := reduceTerms_spec k rest (off + t.auxCount)
          have hr : (reduceTerms k ((s, p.coeff s) :: rest) off).2.2 =
              (reduceTerms k rest (off + t.auxCount)).2.2 := by
            simp [reduceTerms, hgt, t]
          rw [hr]
          have : off + t.auxCount ≤ (reduceTerms k rest (off + t.auxCount)).2.2 := hoff2
          omega
        · by_cases hd' : max k 1 < s'.sum (fun _ e ↦ e)
          · have hvs_ne : monomialToVarList s' ≠ [] := by
              intro h
              have h0 : (monomialToVarList s').length = 0 := by rw [h]; rfl
              rw [length_monomialToVarList] at h0
              omega
            let t := shieldVarList off (monomialToVarList s') hvs_ne
            have hih := ih (off + t.auxCount) hrest
            have hr : (reduceTerms k ((s', c') :: rest) off).2.2 =
                (reduceTerms k rest (off + t.auxCount)).2.2 := by
              simp [reduceTerms, hd', t]
            rw [hr]
            omega
          · have hih := ih off hrest
            have hr : (reduceTerms k ((s', c') :: rest) off).2.2 =
                (reduceTerms k rest off).2.2 := by
              simp [reduceTerms, hd']
            rw [hr]
            exact hih
    have := hpos terms 0 hmem
    omega

/-- The number of shield constraints in `reduceToSystem k p` equals `auxVars`. -/
public theorem length_constraints_reduceToSystem {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R) :
    (reduceToSystem k p).constraints.length = (reduceToSystem k p).auxVars := by
  classical
  let terms := p.support.toList.map fun s ↦ (s, p.coeff s)
  obtain ⟨_, hlen, _, _, _, _, _⟩ := reduceTerms_spec k terms 0
  change (if hm : 0 < (reduceTerms k terms 0).2.2 then
      (reduceTerms k terms 0).1.map (clampShieldEq hm) else []).length =
    (reduceTerms k terms 0).2.2
  split_ifs with hm
  · rw [List.length_map, hlen, Nat.sub_zero]
  · simp only [List.length_nil]
    omega

/-- The number of auxiliary variables in `reduceToSystem k p` is at most
`p.support.card * (p.totalDegree - 1)`. -/
public theorem auxVars_reduceToSystem_le {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R) :
    (reduceToSystem k p).auxVars ≤ p.support.card * (p.totalDegree - 1) := by
  classical
  let terms := p.support.toList.map fun s ↦ (s, p.coeff s)
  obtain ⟨_, _, _, _, _, _, hcnt⟩ := reduceTerms_spec k terms 0
  have hbound : (reduceTerms k terms 0).2.2 - 0 ≤ terms.length * (p.totalDegree - 1) :=
    hcnt fun sc hsc ↦ by
      rcases List.mem_map.mp hsc with ⟨s, hs, rfl⟩
      exact le_totalDegree (Finset.mem_toList.mp hs)
  have htlen : terms.length = p.support.card := by
    simp [terms, Finset.length_toList]
  rw [htlen, Nat.sub_zero] at hbound
  exact hbound

private theorem sum_eval_monomial_toList {n : ℕ} {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin n) R) (x : Fin n → R) :
    ((p.support.toList.map fun s ↦ (s, p.coeff s)).map
      fun sc ↦ eval x (monomial sc.1 sc.2)).sum = eval x p := by
  classical
  rw [List.map_map]
  dsimp only [Function.comp_def]
  have hsum : (p.support.toList.map fun s ↦ eval x (monomial s (p.coeff s))).sum =
      ∑ s ∈ p.support, eval x (monomial s (p.coeff s)) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  rw [hsum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum]

/-- General semiring-parametrized solvability preservation for `reduceToSystem k p`: taking
`f = RingHom.id R` yields equivalence over any commutative ring `R`, and taking
`f = Nat.castRingHom ℤ` (`S = ℕ`, `R = ℤ`) yields equivalence for natural-number solutions. -/
public theorem exists_map_eval_reduceToSystem_iff {n : ℕ} {S R : Type*}
    [CommSemiring S] [CommRing R] (f : S →+* R) (k : ℕ) (p : MvPolynomial (Fin n) R)
    (x : Fin n → S) :
    (∃ y : Fin (reduceToSystem k p).auxVars → S,
      (∀ c ∈ (reduceToSystem k p).constraints,
        eval (Sum.elim (f ∘ x) (f ∘ y)) c = 0) ∧
      eval (Sum.elim (f ∘ x) (f ∘ y)) (reduceToSystem k p).reduced = 0) ↔
    eval (f ∘ x) p = 0 := by
  classical
  let terms := p.support.toList.map fun s ↦ (s, p.coeff s)
  obtain ⟨_, _, _, hvars, heqs, hsound, _⟩ := reduceTerms_spec k terms 0
  let res := reduceTerms k terms 0
  let m := res.2.2
  change (∃ y : Fin m → S,
      (∀ c ∈ (if hm : 0 < m then res.1.map (clampShieldEq hm) else []),
        eval (Sum.elim (f ∘ x) (f ∘ y)) c = 0) ∧
      eval (Sum.elim (f ∘ x) (f ∘ y))
        (if hm : 0 < m then rename (clampAuxVar hm) res.2.1 else rename Sum.inl p) = 0) ↔
    eval (f ∘ x) p = 0
  split_ifs with hm
  · constructor
    · rintro ⟨y, hc, hr⟩
      let yExt : ℕ → R := fun w ↦ if hw : w < m then f (y ⟨w, hw⟩) else 0
      have hyExt : ∀ w (hw : w < m), yExt w = (f ∘ y) ⟨w, hw⟩ := fun w hw ↦ dite_eq_left hw
      have hall : ∀ e ∈ res.1, eval (Sum.elim (f ∘ x) yExt) e.toPoly = 0 := by
        intro e he
        obtain ⟨ht, hl, hr'⟩ := heqs e he
        rw [← eval_clampShieldEq hm ht hl hr' (f ∘ x) (f ∘ y) yExt hyExt]
        exact hc _ (List.mem_map_of_mem he)
      have heval_red : eval (Sum.elim (f ∘ x) (f ∘ y)) (rename (clampAuxVar hm) res.2.1) =
          eval (Sum.elim (f ∘ x) yExt) res.2.1 := by
        classical
        rw [eval_rename]
        refine eval_congr_vars res.2.1 fun v ⟨s, hs, hvs⟩ ↦ ?_
        have hv : v ∈ res.2.1.vars := by
          rw [vars_def, Multiset.mem_toFinset, degrees_def]
          exact Multiset.mem_of_le (Finset.le_sup (f := Finsupp.toMultiset) hs)
            ((s.mem_toMultiset v).mpr hvs)
        cases v with
        | inl i => rfl
        | inr w =>
          have hw : w < m := hvars (Sum.inr w) hv w rfl
          simp [clampAuxVar, yExt, dite_eq_left hw]
      rw [heval_red, hsound (f ∘ x) yExt hall, sum_eval_monomial_toList] at hr
      exact hr
    · intro hpx
      obtain ⟨yExt, _, hall⟩ := reduceTerms_complete f k terms 0 x (fun _ ↦ 0)
      let y : Fin m → S := fun j ↦ yExt j.1
      have hyExt : ∀ w (hw : w < m), (f ∘ yExt) w = (f ∘ y) ⟨w, hw⟩ := fun _ _ ↦ rfl
      refine ⟨y, ?_, ?_⟩
      · intro c hc
        rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
        obtain ⟨ht, hl, hr'⟩ := heqs e he
        rw [eval_clampShieldEq hm ht hl hr' (f ∘ x) (f ∘ y) (f ∘ yExt) hyExt]
        exact hall e he
      · have heval_red : eval (Sum.elim (f ∘ x) (f ∘ y)) (rename (clampAuxVar hm) res.2.1) =
            eval (Sum.elim (f ∘ x) (f ∘ yExt)) res.2.1 := by
          classical
          rw [eval_rename]
          refine eval_congr_vars res.2.1 fun v ⟨s, hs, hvs⟩ ↦ ?_
          have hv : v ∈ res.2.1.vars := by
            rw [vars_def, Multiset.mem_toFinset, degrees_def]
            exact Multiset.mem_of_le (Finset.le_sup (f := Finsupp.toMultiset) hs)
              ((s.mem_toMultiset v).mpr hvs)
          cases v with
          | inl i => rfl
          | inr w =>
            have hw : w < m := hvars (Sum.inr w) hv w rfl
            simp [clampAuxVar, y, dite_eq_left hw]
        rw [heval_red, hsound (f ∘ x) (f ∘ yExt) hall, sum_eval_monomial_toList]
        exact hpx
  · have hm0 : m = 0 := by omega
    constructor
    · rintro ⟨y, _, hr⟩
      simpa [eval_rename] using hr
    · intro hpx
      refine ⟨fun j ↦ absurd j.2 (by omega), ?_, by simpa [eval_rename] using hpx⟩
      rintro c ⟨⟩

/-- Skolem reduction preserves solvability over any commutative ring `R`. -/
public theorem exists_eval_reduceToSystem_iff {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R) :
    (∃ z : Fin n ⊕ Fin (reduceToSystem k p).auxVars → R,
      (∀ c ∈ (reduceToSystem k p).constraints, eval z c = 0) ∧
      eval z (reduceToSystem k p).reduced = 0) ↔
    (∃ x : Fin n → R, eval x p = 0) := by
  constructor
  · rintro ⟨z, hc, hr⟩
    refine ⟨z ∘ Sum.inl, ?_⟩
    exact (exists_map_eval_reduceToSystem_iff (RingHom.id R) k p (z ∘ Sum.inl)).mp
      ⟨z ∘ Sum.inr, by simpa [Sum.elim_comp_inl_inr] using hc,
        by simpa [Sum.elim_comp_inl_inr] using hr⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hc, hr⟩ := (exists_map_eval_reduceToSystem_iff (RingHom.id R) k p x).mpr hx
    exact ⟨Sum.elim x y, hc, hr⟩

/-- Skolem reduction preserves natural-number solvability of integer polynomials. -/
public theorem exists_nat_eval_reduceToSystem_iff {n : ℕ}
    (k : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    (∃ z : Fin n ⊕ Fin (reduceToSystem k p).auxVars → ℕ,
      (∀ c ∈ (reduceToSystem k p).constraints, eval (fun v ↦ (z v : ℤ)) c = 0) ∧
      eval (fun v ↦ (z v : ℤ)) (reduceToSystem k p).reduced = 0) ↔
    (∃ x : Fin n → ℕ, eval (fun i ↦ (x i : ℤ)) p = 0) := by
  constructor
  · rintro ⟨z, hc, hr⟩
    refine ⟨z ∘ Sum.inl, ?_⟩
    have hcomp : (fun v ↦ (z v : ℤ)) =
        Sum.elim ((Nat.castRingHom ℤ) ∘ (z ∘ Sum.inl)) ((Nat.castRingHom ℤ) ∘ (z ∘ Sum.inr)) := by
      ext (i | j) <;> rfl
    rw [hcomp] at hc hr
    exact (exists_map_eval_reduceToSystem_iff (Nat.castRingHom ℤ) k p (z ∘ Sum.inl)).mp
      ⟨z ∘ Sum.inr, hc, hr⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hc, hr⟩ :=
      (exists_map_eval_reduceToSystem_iff (Nat.castRingHom ℤ) k p x).mpr hx
    have hfn : (fun v ↦ (Int.ofNat (Sum.elim x y v))) =
        Sum.elim ((Nat.castRingHom ℤ) ∘ x) ((Nat.castRingHom ℤ) ∘ y) := by
      ext (i | j) <;> rfl
    refine ⟨Sum.elim x y, ?_, ?_⟩
    · intro c hcm
      change eval (fun v ↦ Int.ofNat (Sum.elim x y v)) c = 0
      rw [hfn]
      exact hc c hcm
    · change eval (fun v ↦ Int.ofNat (Sum.elim x y v)) _ = 0
      rw [hfn]
      exact hr

/-- At every threshold `k`, all polynomials in `(reduceToSystem k p).allPolys` have total degree
at most `max k 2`. In particular, `k = 1` gives total degree `≤ 2` (quadratic system) and `k = 3`
gives total degree `≤ 3` (cubic system). -/
public theorem totalDegree_mem_allPolys_reduceToSystem_le {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial (Fin n) R)
    {q : MvPolynomial (Fin n ⊕ Fin (reduceToSystem k p).auxVars) R}
    (hq : q ∈ (reduceToSystem k p).allPolys) :
    q.totalDegree ≤ max k 2 := by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact (totalDegree_reduced_reduceToSystem_le k p).trans (by omega)
  · exact (totalDegree_mem_constraints_reduceToSystem_le k p hq).trans (le_max_right k 2)

/-! ### Single-equation quartic reduction over `ℕ` and over `ℤ` -/

/-- Variable type of `skolemQuarticNat p`: original variables `Fin n` plus Skolem auxiliary
variables `Fin (reduceToSystem 1 p).auxVars`. -/
public abbrev QuarticNatVar {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : Type :=
  Fin n ⊕ Fin (reduceToSystem 1 p).auxVars

/-- Skolem's single-equation quartic reduction over `ℕ`: reduces `p` to a quadratic system
(`reduceToSystem 1 p`, every equation of total degree `≤ 2`) and merges all equations by
sum-of-squares into a single polynomial of total degree at most `4`. -/
public noncomputable def skolemQuarticNat {n : ℕ}
    (p : MvPolynomial (Fin n) ℤ) : MvPolynomial (QuarticNatVar p) ℤ :=
  sumSq (reduceToSystem 1 p).allPolys

/-- `skolemQuarticNat p` has total degree at most `4`. -/
public theorem totalDegree_skolemQuarticNat_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (skolemQuarticNat p).totalDegree ≤ 4 := by
  have h : (skolemQuarticNat p).totalDegree ≤ 2 * 2 :=
    totalDegree_sumSq_le fun q hq ↦ totalDegree_mem_allPolys_reduceToSystem_le 1 p hq
  exact h

/-- `skolemQuarticNat p` vanishes at `z` iff every polynomial in `(reduceToSystem 1 p).allPolys`
vanishes at `z`. -/
public theorem eval_skolemQuarticNat_eq_zero_iff {n : ℕ}
    (p : MvPolynomial (Fin n) ℤ) (z : QuarticNatVar p → ℤ) :
    eval z (skolemQuarticNat p) = 0 ↔
      ∀ q ∈ (reduceToSystem 1 p).allPolys, eval z q = 0 :=
  eval_sumSq_eq_zero_iff

/-- For a fixed `x : Fin n → ℕ`, `skolemQuarticNat p` has a natural-number root extending `x`
if and only if `p` vanishes at `x`. -/
public theorem exists_aux_eval_skolemQuarticNat_iff {n : ℕ}
    (p : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ) :
    (∃ y : Fin (reduceToSystem 1 p).auxVars → ℕ,
      eval (fun v : QuarticNatVar p ↦ ((Sum.elim x y v : ℕ) : ℤ)) (skolemQuarticNat p) = 0) ↔
    eval (fun i ↦ (x i : ℤ)) p = 0 := by
  have hsum : ∀ y : Fin (reduceToSystem 1 p).auxVars → ℕ,
      eval (fun v : QuarticNatVar p ↦ ((Sum.elim x y v : ℕ) : ℤ)) (skolemQuarticNat p) = 0 ↔
        (∀ c ∈ (reduceToSystem 1 p).constraints,
          eval (Sum.elim ((Nat.castRingHom ℤ) ∘ x) ((Nat.castRingHom ℤ) ∘ y)) c = 0) ∧
        eval (Sum.elim ((Nat.castRingHom ℤ) ∘ x) ((Nat.castRingHom ℤ) ∘ y))
          (reduceToSystem 1 p).reduced = 0 := by
    intro y
    have hfn : (fun v : QuarticNatVar p ↦ ((Sum.elim x y v : ℕ) : ℤ)) =
        Sum.elim ((Nat.castRingHom ℤ) ∘ x) ((Nat.castRingHom ℤ) ∘ y) := by
      ext (i | j) <;> rfl
    rw [eval_skolemQuarticNat_eq_zero_iff, SkolemReduction.allPolys, hfn]
    simp [and_comm]
  simp_rw [hsum]
  exact exists_map_eval_reduceToSystem_iff (Nat.castRingHom ℤ) 1 p x

/-- `skolemQuarticNat p` has a natural-number solution if and only if `p` has one. -/
public theorem exists_nat_eval_skolemQuarticNat_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (∃ z : QuarticNatVar p → ℕ, eval (fun v ↦ (z v : ℤ)) (skolemQuarticNat p) = 0) ↔
    (∃ x : Fin n → ℕ, eval (fun i ↦ (x i : ℤ)) p = 0) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ∘ Sum.inl, (exists_aux_eval_skolemQuarticNat_iff p (z ∘ Sum.inl)).mp ⟨z ∘ Sum.inr,
      ?_⟩⟩
    simpa [Sum.elim_comp_inl_inr] using hz
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (exists_aux_eval_skolemQuarticNat_iff p x).mpr hx
    exact ⟨Sum.elim x y, hy⟩

/-- Variable type of `intifySystem`: original system variables `σ` together with four Lagrange
four-squares slack variables `σ × Fin 4` enforcing `x_v ≥ 0` at quadratic degree. -/
public abbrev IntifyVar (σ : Type*) : Type _ := σ ⊕ (σ × Fin 4)

/-- Converts a finite polynomial system `ps` over `ℕ` (with `σ` finite) into an equisolvable
system over `ℤ` by adjoining `X (inl v) - ∑ j : Fin 4, X (inr (v, j)) ^ 2` for each variable `v`,
preserving any total degree bound `d ≥ 2`. -/
public noncomputable def intifySystem {σ : Type*} [Fintype σ]
    (ps : List (MvPolynomial σ ℤ)) : List (MvPolynomial (IntifyVar σ) ℤ) :=
  ps.map (rename Sum.inl) ++
    (Finset.univ.toList.map fun v : σ ↦
      (X (Sum.inl v) : MvPolynomial (IntifyVar σ) ℤ) -
        ∑ j : Fin 4, (X (Sum.inr (v, j)) : MvPolynomial (IntifyVar σ) ℤ) ^ 2)

/-- Every polynomial in `intifySystem ps` has total degree at most `max d 2` whenever every
polynomial in `ps` has total degree at most `d`. -/
public theorem totalDegree_mem_intifySystem_le {σ : Type*} [Fintype σ]
    {ps : List (MvPolynomial σ ℤ)} {d : ℕ} (hd : ∀ p ∈ ps, p.totalDegree ≤ d)
    {q : MvPolynomial (IntifyVar σ) ℤ} (hq : q ∈ intifySystem ps) :
    q.totalDegree ≤ max d 2 := by
  rcases List.mem_append.mp hq with hq1 | hq2
  · rcases List.mem_map.mp hq1 with ⟨p, hp, rfl⟩
    exact (totalDegree_rename_le Sum.inl p).trans ((hd p hp).trans (le_max_left d 2))
  · rcases List.mem_map.mp hq2 with ⟨v, _, rfl⟩
    exact (totalDegree_var_sub_fourSq_le_two (Sum.inl v) fun j ↦ Sum.inr (v, j)).trans
      (le_max_right d 2)

/-- An integer assignment `z` satisfies every polynomial in `intifySystem ps` if and only if every
`p ∈ ps` vanishes on `z ∘ Sum.inl` and every `z (Sum.inl v)` is the sum of the squares of its four
slack variables `z (Sum.inr (v, j))`. -/
public theorem forall_eval_mem_intifySystem_iff {σ : Type*} [Fintype σ]
    (ps : List (MvPolynomial σ ℤ)) (z : IntifyVar σ → ℤ) :
    (∀ q ∈ intifySystem ps, eval z q = 0) ↔
      (∀ p ∈ ps, eval (z ∘ Sum.inl) p = 0) ∧
      (∀ v : σ, z (Sum.inl v) = ∑ j : Fin 4, z (Sum.inr (v, j)) ^ 2) := by
  simp only [intifySystem, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_univ,
    true_and]
  constructor
  · intro h
    refine ⟨fun p hp ↦ ?_, fun v ↦ ?_⟩
    · have hp0 := h (rename Sum.inl p) (Or.inl ⟨p, hp, rfl⟩)
      rwa [eval_rename] at hp0
    · simpa [sub_eq_zero] using h _ (Or.inr ⟨v, rfl⟩)
  · rintro ⟨hp, hv⟩ _ (⟨p, hpm, rfl⟩ | ⟨v, rfl⟩)
    · rw [eval_rename]; exact hp p hpm
    · simp [hv v]

/-- `intifySystem ps` has a common zero over `ℤ` if and only if `ps` has a common zero over `ℕ`. -/
public theorem exists_int_eval_intifySystem_iff {σ : Type*} [Fintype σ]
    (ps : List (MvPolynomial σ ℤ)) :
    (∃ z : IntifyVar σ → ℤ, ∀ q ∈ intifySystem ps, eval z q = 0) ↔
    (∃ x : σ → ℕ, ∀ p ∈ ps, eval (fun v ↦ (x v : ℤ)) p = 0) := by
  constructor
  · rintro ⟨z, hz⟩
    have hnonneg : ∀ v : σ, 0 ≤ z (Sum.inl v) := by
      intro v
      have hv : eval z ((X (Sum.inl v) : MvPolynomial (IntifyVar σ) ℤ) -
          ∑ j : Fin 4, X (Sum.inr (v, j)) ^ 2) = 0 :=
        hz _ (List.mem_append_right _ (List.mem_map_of_mem (Finset.mem_toList.mpr
          (Finset.mem_univ v))))
      simp only [map_sub, eval_X, map_sum, map_pow, sub_eq_zero] at hv
      rw [hv]
      exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    refine ⟨fun v ↦ (z (Sum.inl v)).toNat, fun p hp ↦ ?_⟩
    have hp0 := hz (rename Sum.inl p) (List.mem_append_left _ (List.mem_map_of_mem hp))
    rw [eval_rename] at hp0
    have hfn : (fun v : σ ↦ (((z (Sum.inl v)).toNat : ℕ) : ℤ)) = fun v ↦ z (Sum.inl v) :=
      funext fun v ↦ Int.toNat_of_nonneg (hnonneg v)
    rwa [hfn]
  · rintro ⟨x, hx⟩
    have hf : ∀ v : σ, ∃ f : Fin 4 → ℤ, (x v : ℤ) = ∑ j : Fin 4, f j ^ 2 := fun v ↦
      int_nonneg_iff_exists_four_int_sq.mp (Nat.cast_nonneg (x v))
    choose f hf using hf
    let z : IntifyVar σ → ℤ := Sum.elim (fun v ↦ (x v : ℤ)) (fun p ↦ f p.1 p.2)
    refine ⟨z, fun q hq ↦ ?_⟩
    rcases List.mem_append.mp hq with hq1 | hq2
    · rcases List.mem_map.mp hq1 with ⟨p, hp, rfl⟩
      rw [eval_rename]
      exact hx p hp
    · rcases List.mem_map.mp hq2 with ⟨v, _, rfl⟩
      simp [z, hf v]

/-- Variable type of `skolemQuarticInt p`: Skolem quadratic variables together with four Lagrange
slack variables per system variable. -/
public abbrev QuarticIntVar {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : Type :=
  IntifyVar (QuarticNatVar p)

/-- Single-equation quartic reduction from `ℕ`-solvability of `p` to `ℤ`-solvability: adjoins
Lagrange four-squares equations (degree `2`) to the quadratic Skolem system `reduceToSystem 1 p`
and aggregates all equations via `sumSq`, yielding a polynomial of total degree at most `4`. -/
public noncomputable def skolemQuarticInt {n : ℕ}
    (p : MvPolynomial (Fin n) ℤ) : MvPolynomial (QuarticIntVar p) ℤ :=
  sumSq (intifySystem (reduceToSystem 1 p).allPolys)

/-- `skolemQuarticInt p` has total degree at most `4`. -/
public theorem totalDegree_skolemQuarticInt_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (skolemQuarticInt p).totalDegree ≤ 4 := by
  have h : (skolemQuarticInt p).totalDegree ≤ 2 * 2 :=
    totalDegree_sumSq_le fun q hq ↦
      totalDegree_mem_intifySystem_le
        (fun r hr ↦ totalDegree_mem_allPolys_reduceToSystem_le 1 p hr) hq
  exact h

/-- `skolemQuarticInt p` vanishes at `z` iff every polynomial in
`intifySystem (reduceToSystem 1 p).allPolys` vanishes at `z`. -/
public theorem eval_skolemQuarticInt_eq_zero_iff {n : ℕ}
    (p : MvPolynomial (Fin n) ℤ) (z : QuarticIntVar p → ℤ) :
    eval z (skolemQuarticInt p) = 0 ↔
      ∀ q ∈ intifySystem (reduceToSystem 1 p).allPolys, eval z q = 0 :=
  eval_sumSq_eq_zero_iff

/-- `skolemQuarticInt p` has an integer root if and only if `p` has a natural-number root. -/
public theorem exists_int_eval_skolemQuarticInt_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (∃ z : QuarticIntVar p → ℤ, eval z (skolemQuarticInt p) = 0) ↔
    (∃ x : Fin n → ℕ, eval (fun i ↦ (x i : ℤ)) p = 0) := by
  simp_rw [eval_skolemQuarticInt_eq_zero_iff]
  rw [exists_int_eval_intifySystem_iff, ← exists_nat_eval_reduceToSystem_iff 1 p]
  simp [SkolemReduction.allPolys, and_comm]

/-! ### Translation from Mathlib's `Poly σ` to `MvPolynomial σ ℤ` -/

private theorem isPoly_exists_mvPoly {σ : Type*} {f : (σ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ p : MvPolynomial σ ℤ, ∀ x : σ → ℕ, eval (fun i ↦ (x i : ℤ)) p = f x := by
  induction hf with
  | proj i => exact ⟨X i, fun x ↦ by simp⟩
  | const c => exact ⟨C c, fun x ↦ by simp⟩
  | sub hg₁ hg₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨p₁, hp₁⟩
    rcases ih₂ with ⟨p₂, hp₂⟩
    exact ⟨p₁ - p₂, fun x ↦ by simp [hp₁ x, hp₂ x]⟩
  | mul hg₁ hg₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨p₁, hp₁⟩
    rcases ih₂ with ⟨p₂, hp₂⟩
    exact ⟨p₁ * p₂, fun x ↦ by simp [hp₁ x, hp₂ x]⟩

/-- Associates to each Diophantine polynomial function `f : Poly σ` a multivariate polynomial
`polyToMvPoly f : MvPolynomial σ ℤ` matching `f` on all natural-number assignments. -/
public noncomputable def polyToMvPoly {σ : Type*} (f : Poly σ) : MvPolynomial σ ℤ :=
  (isPoly_exists_mvPoly f.isPoly).choose

/-- `polyToMvPoly f` evaluates at `(x · : ℤ)` to `f x` for every `x : σ → ℕ`. -/
@[simp]
public theorem eval_polyToMvPoly {σ : Type*} (f : Poly σ) (x : σ → ℕ) :
    eval (fun i ↦ (x i : ℤ)) (polyToMvPoly f) = f x :=
  (isPoly_exists_mvPoly f.isPoly).choose_spec x

/-- Non-vacuity check: Skolem quartic reduction preserves solvability of a concrete degree-`6`
polynomial `x₀ ^ 6 - 64` over `ℕ` and over `ℤ`. -/
private example :
    let p : MvPolynomial (Fin 1) ℤ := X 0 ^ 6 - C 64
    (skolemQuarticNat p).totalDegree ≤ 4 ∧
    (∃ z : QuarticNatVar p → ℕ, eval (fun v ↦ (z v : ℤ)) (skolemQuarticNat p) = 0) ∧
    (∃ z : QuarticIntVar p → ℤ, eval z (skolemQuarticInt p) = 0) := by
  intro p
  refine ⟨totalDegree_skolemQuarticNat_le p, ?_, ?_⟩
  · rw [exists_nat_eval_skolemQuarticNat_iff]
    exact ⟨fun _ ↦ 2, by norm_num [p]⟩
  · rw [exists_int_eval_skolemQuarticInt_iff]
    exact ⟨fun _ ↦ 2, by norm_num [p]⟩

end CslibFrontier.Computability.Diophantine
