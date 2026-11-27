/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Rat.Floor
import CslibFrontier.Computability.Complexity.Classes.Ladner
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.Polynomial.FiniteDifference
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Tactic.PolyTime
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Lagrange

/-!
# Rational Counting Turing Reductions, Batch Composition, and Lagrange Interpolation

This module develops polynomial-time counting Turing reductions to rational-valued counting
problems, composable non-adaptive polynomial-time batch counting reductions, and polynomial-time
exact univariate Lagrange interpolation over `ℚ`, proved under standard Lean axioms.

In counting complexity and probabilistic network/database reliability, many canonical `#P`-hard
problems return exact rational probabilities `g : β → ℚ` rather than natural-number counts. We
expose a rational oracle `g` through its normalized sign, numerator, and denominator bits
(`CslibFrontier.Complexity.AnswersRatBits` and `CslibFrontier.Complexity.bitGraphRat`), define
`CslibFrontier.Complexity.RatCountingTuringReducible` and
`CslibFrontier.Complexity.RatCountingTuringHard` via `PolyTimeOracleProgram`, and prove that
polynomial-time computability of any `RatCountingTuringHard` function with a polynomial-time
decodable input encoding collapses `#P` to `FP` and implies `P = NP`.

To compose chains of interpolation and saturation-rounding reductions without repeated oracle-monad
plumbing, `CslibFrontier.Complexity.PolyTimeBatchReducible` packages non-adaptive polynomial-time
truth-table reductions between arbitrary encoded value types, proves transitivity across mixed
intermediate types, and bridges directly to both `Cslib.Complexity.CountingTuringReducible` and
`CslibFrontier.Complexity.RatCountingTuringReducible`.

Finally, `CslibFrontier.Complexity.lagrangeInterpCoeffs` computes the full monomial coefficient list
of a univariate polynomial `P : ℚ[X]` of degree `< n` from its values at `n` pairwise distinct
rational nodes in polynomial time, together with `CslibFrontier.Complexity.ratListSum`,
`CslibFrontier.Complexity.ratListProd`, and nearest-integer rounding
`CslibFrontier.Complexity.ratRoundNat`.

## Main definitions

* `CslibFrontier.Complexity.ratListProd`, `CslibFrontier.Complexity.ratListSum`,
  `CslibFrontier.Complexity.ratRoundNat`: polynomial-time rational list product, list sum, and
  nearest-natural rounding.
* `CslibFrontier.Complexity.intPolyMulLinear`, `CslibFrontier.Complexity.intPolyOfLinearFactors`,
  `CslibFrontier.Complexity.lagrangeBasisCoeffs`, `CslibFrontier.Complexity.lagrangeInterpCoeffs`,
  `CslibFrontier.Complexity.geomRatNodes`: polynomial-time exact univariate Lagrange interpolation
  over `ℚ`.
* `CslibFrontier.Complexity.ratTestBit`, `CslibFrontier.Complexity.ratBitSize`,
  `CslibFrontier.Complexity.ratOfBits`, `CslibFrontier.Complexity.AnswersRatBits`,
  `CslibFrontier.Complexity.bitGraphRat`: bit-graph oracle representation of rational functions.
* `CslibFrontier.Complexity.RatCountingTuringReducible`,
  `CslibFrontier.Complexity.RatCountingTuringHard`: `#P`-reducibility and `#P`-hardness for
  rational-valued problems.
* `CslibFrontier.Complexity.PolyTimeBatchReducible`: composable non-adaptive polynomial-time batch
  reductions.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_ratListProd`,
  `CslibFrontier.Complexity.computableInPolyTime_ratListSum`,
  `CslibFrontier.Complexity.computableInPolyTime_ratRoundNat`: polynomial-time certificates for
  rational aggregation and rounding.
* `CslibFrontier.Complexity.computableInPolyTime_lagrangeInterpCoeffs`,
  `CslibFrontier.Complexity.getD_lagrangeInterpCoeffs_eq_coeff`,
  `CslibFrontier.Complexity.getD_lagrangeInterpCoeffs_geomRatNodes`: polynomial-time soundness of
  exact rational Lagrange interpolation.
* `CslibFrontier.Complexity.PolyTimeBatchReducible.trans`,
  `CslibFrontier.Complexity.PolyTimeBatchReducible.toCountingTuringReducible`,
  `CslibFrontier.Complexity.PolyTimeBatchReducible.toRatCountingTuringReducible`: composition and
  counting-Turing realization of batch reductions.
* `CslibFrontier.Complexity.bitGraphRat_mem_P`,
  `CslibFrontier.Complexity.RatCountingTuringHard.computableInPolyTime_of_decoder`,
  `CslibFrontier.Complexity.RatCountingTuringHard.P_eq_NP_of_decoder`: collapse of `#P` and `NP`
  when
  a rational `#P`-hard function is polynomial-time computable.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Probability Polynomial Turing.MultiTapeTM

/-! ### Polynomial-time rational list product, list sum, and nearest-integer rounding -/

/-- Product of a list of rational numbers computed by multiplying all numerators and all
denominators separately before normalizing once. -/
def ratListProd (l : List ℚ) : ℚ :=
  Rat.divInt (l.map Rat.num).prod (((l.map Rat.den).prod : ℕ) : ℤ)

/-- `ratListProd` agrees with `List.prod` on every list of rationals. -/
@[simp]
theorem ratListProd_eq_prod (l : List ℚ) : ratListProd l = l.prod := by
  unfold ratListProd
  rw [Rat.divInt_eq_div]
  induction l with
  | nil => simp
  | cons q qs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul, mul_div_mul_comm, Rat.num_div_den, ← Int.cast_natCast, ih,
      List.prod_cons]

/-- Computing the product of a list of rationals is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_ratListProd :
    ComputableInPolyTime ratListProd (encList encRat) encRat := by
  unfold ratListProd
  have hnums : ComputableInPolyTime (fun l : List ℚ ↦ (l.map Rat.num).prod)
      (encList encRat) encIntBin :=
    ComputableInPolyTime.intBin_prod.comp
      (ComputableInPolyTime.mapWithInput ComputableInPolyTime.id'
        (ComputableInPolyTime.rat_num.comp (ComputableInPolyTime.snd _ _)))
  have hdens : ComputableInPolyTime (fun l : List ℚ ↦ (((l.map Rat.den).prod : ℕ) : ℤ))
      (encList encRat) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp <|
      ComputableInPolyTime.binary_prod.comp
        (ComputableInPolyTime.mapWithInput ComputableInPolyTime.id'
          (ComputableInPolyTime.rat_den.comp (ComputableInPolyTime.snd _ _)))
  exact ComputableInPolyTime.rat_divInt' hnums hdens

/-- Sum of a list of rational numbers computed via the product of all denominators so that
intermediate numerators remain polynomially bounded in encoded bit length. -/
def ratListSum (l : List ℚ) : ℚ :=
  let D : ℕ := (l.map Rat.den).prod
  Rat.divInt ((l.map fun q ↦ q.num * ((D / q.den : ℕ) : ℤ)).sum) (D : ℤ)

private lemma list_prod_pos_of_pos : ∀ {l : List ℕ}, (∀ x ∈ l, 0 < x) → 0 < l.prod
  | [], _ => by simp
  | x :: xs, h => Nat.mul_pos (h x List.mem_cons_self)
      (list_prod_pos_of_pos fun y hy ↦ h y (List.mem_cons_of_mem x hy))

private lemma dvd_list_prod_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ∣ l.prod
  | _ :: xs, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_list_prod_of_mem hmem) _

private lemma sum_scaled_div_eq {D : ℕ} (hD : 0 < D) :
    ∀ {l : List ℚ}, (∀ q ∈ l, q.den ∣ D) →
      (((l.map fun q ↦ q.num * ((D / q.den : ℕ) : ℤ)).sum : ℤ) : ℚ) / (D : ℚ) = l.sum
  | [], _ => by simp
  | q :: qs, hdvd => by
    have hq_dvd : q.den ∣ D := hdvd q List.mem_cons_self
    have hD_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    have hq_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_pos.ne'
    have hmul : (q.den : ℚ) * ((D / q.den : ℕ) : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.mul_div_cancel' hq_dvd
    have hterm : ((q.num : ℚ) * ((D / q.den : ℕ) : ℚ)) / (D : ℚ) = q := by
      rw [← hmul, mul_div_mul_right _ _ (by
        intro h0
        rw [h0, mul_zero] at hmul
        exact hD_ne hmul.symm), Rat.num_div_den]
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      add_div, hterm, sum_scaled_div_eq hD fun r hr ↦ hdvd r (List.mem_cons_of_mem q hr)]

/-- `ratListSum` agrees with `List.sum` on every list of rationals. -/
@[simp]
theorem ratListSum_eq_sum (l : List ℚ) : ratListSum l = l.sum := by
  unfold ratListSum
  dsimp only
  rw [Rat.divInt_eq_div, Int.cast_natCast]
  have hD : 0 < (l.map Rat.den).prod :=
    list_prod_pos_of_pos fun x hx ↦ by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      exact q.den_pos
  exact sum_scaled_div_eq hD fun q hq ↦ dvd_list_prod_of_mem (List.mem_map_of_mem hq)

/-- Computing the sum of a list of rationals is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_ratListSum :
    ComputableInPolyTime ratListSum (encList encRat) encRat := by
  unfold ratListSum
  have hD : ComputableInPolyTime (fun l : List ℚ ↦ (l.map Rat.den).prod)
      (encList encRat) encNat :=
    ComputableInPolyTime.binary_prod.comp
      (ComputableInPolyTime.mapWithInput ComputableInPolyTime.id'
        (ComputableInPolyTime.rat_den.comp (ComputableInPolyTime.snd _ _)))
  have hterm : ComputableInPolyTime
      (fun p : List ℚ × ℚ ↦ p.2.num * (((p.1.map Rat.den).prod / p.2.den : ℕ) : ℤ))
      (encPair (encList encRat) encRat) encIntBin := by
    have hDp := hD.comp (ComputableInPolyTime.fst (encList encRat) encRat)
    have hq := ComputableInPolyTime.snd (encList encRat) encRat
    have hdiv := ComputableInPolyTime.binary_div' hDp (ComputableInPolyTime.rat_den.comp hq)
    exact ComputableInPolyTime.intBin_mul' (ComputableInPolyTime.rat_num.comp hq)
      (ComputableInPolyTime.intBin_natCast.comp hdiv)
  have hsum : ComputableInPolyTime
      (fun l : List ℚ ↦ (l.map fun q ↦ q.num * (((l.map Rat.den).prod / q.den : ℕ) : ℤ)).sum)
      (encList encRat) encIntBin :=
    ComputableInPolyTime.intBin_sum.comp
      (ComputableInPolyTime.mapWithInput ComputableInPolyTime.id' hterm)
  exact ComputableInPolyTime.rat_divInt' hsum (ComputableInPolyTime.intBin_natCast.comp hD)

/-- Nearest natural number to a rational `q`, defined as `⌊q + 1/2⌋.toNat`. -/
def ratRoundNat (q : ℚ) : ℕ :=
  (q + 1 / 2).floor.toNat

/-- Rounding a rational `q` within strict distance `1 / 2` of a natural number `z` recovers `z`
exactly. -/
theorem ratRoundNat_eq_of_abs_sub_lt_half {q : ℚ} {z : ℕ} (h : |q - (z : ℚ)| < 1 / 2) :
    ratRoundNat q = z := by
  rw [abs_lt] at h
  have hfloor : (q + 1 / 2).floor = (z : ℤ) := by
    refine (Int.floor_eq_iff (R := ℚ)).mpr ?_
    rw [Int.cast_natCast]
    constructor <;> linarith
  simp only [ratRoundNat, hfloor, Int.toNat_natCast]

/-- Nearest-natural rounding `ratRoundNat` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ratRoundNat :
    ComputableInPolyTime ratRoundNat encRat encNat := by
  unfold ratRoundNat
  exact ComputableInPolyTime.intBin_toNat.comp <|
    ComputableInPolyTime.rat_floor' <|
      ComputableInPolyTime.rat_add' ComputableInPolyTime.id' (ComputableInPolyTime.const (1 / 2))

/-! ### Polynomial-time exact univariate Lagrange interpolation over `ℚ` -/

/-- Multiply a coefficient list `p` (representing `∑ i, p[i] X^i ∈ ℤ[X]`) by the linear polynomial
`ab.2 * X - ab.1`. -/
def intPolyMulLinear (p : List ℤ) (ab : ℤ × ℤ) : List ℤ :=
  (List.range (p.length + 1)).map fun i ↦
    (if i = 0 then 0 else ab.2 * p.getD (i - 1) 0) - ab.1 * p.getD i 0

/-- Expand a product `∏ (a, b) ∈ l, (b * X - a) ∈ ℤ[X]` into its dense coefficient list of length
`l.length + 1`. -/
def intPolyOfLinearFactors (l : List (ℤ × ℤ)) : List ℤ :=
  l.foldl intPolyMulLinear [1]

private lemma length_intPolyMulLinear (p : List ℤ) (ab : ℤ × ℤ) :
    (intPolyMulLinear p ab).length = p.length + 1 := by
  simp [intPolyMulLinear]

private lemma length_foldl_intPolyMulLinear (l : List (ℤ × ℤ)) (p : List ℤ) :
    (l.foldl intPolyMulLinear p).length = p.length + l.length := by
  induction l generalizing p with
  | nil => simp
  | cons ab rest ih =>
    rw [List.foldl_cons, ih, length_intPolyMulLinear, List.length_cons]
    omega

/-- `intPolyOfLinearFactors l` has length `l.length + 1`. -/
theorem length_intPolyOfLinearFactors (l : List (ℤ × ℤ)) :
    (intPolyOfLinearFactors l).length = l.length + 1 := by
  simpa [intPolyOfLinearFactors, Nat.add_comm] using length_foldl_intPolyMulLinear l [1]

private lemma coeff_finset_sum {ι R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (c : ℕ) :
    (∑ i ∈ s, f i).coeff c = ∑ i ∈ s, (f i).coeff c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

private noncomputable def listToIntPoly (p : List ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range p.length, C (p.getD i 0) * X ^ i

private lemma coeff_listToIntPoly (p : List ℤ) (c : ℕ) :
    (listToIntPoly p).coeff c = p.getD c 0 := by
  rw [listToIntPoly, coeff_finset_sum]
  by_cases hc : c < p.length
  · rw [Finset.sum_eq_single c
      (fun i _ hi ↦ by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        split_ifs with heq
        · exact absurd heq.symm hi
        · exact mul_zero _)
      (fun hnot ↦ absurd (Finset.mem_range.mpr hc) hnot),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  · rw [Finset.sum_eq_zero fun i hi ↦ by
      have hne : c ≠ i := by have := Finset.mem_range.mp hi; omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs with heq
      · exact absurd heq hne
      · exact mul_zero _]
    exact (List.getD_eq_default p 0 (Nat.le_of_not_lt hc)).symm

private lemma listToIntPoly_intPolyMulLinear (p : List ℤ) (ab : ℤ × ℤ) :
    listToIntPoly (intPolyMulLinear p ab) = listToIntPoly p * (C ab.2 * X - C ab.1) := by
  ext c
  rw [coeff_listToIntPoly, mul_sub, Polynomial.coeff_sub, mul_comm (C ab.2) X, ← mul_assoc,
    Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, coeff_listToIntPoly]
  have hmulX : (listToIntPoly p * X).coeff c = if c = 0 then 0 else p.getD (c - 1) 0 := by
    cases c with
    | zero => exact Polynomial.coeff_mul_X_zero _
    | succ k => simp [Polynomial.coeff_mul_X, coeff_listToIntPoly]
  rw [hmulX]
  by_cases hc : c < p.length + 1
  · have hlen : c < (intPolyMulLinear p ab).length := by simp [intPolyMulLinear, hc]
    have hgd := List.getD_eq_getElem (intPolyMulLinear p ab) 0 hlen
    rw [hgd]
    simp only [intPolyMulLinear, List.getElem_map, List.getElem_range]
    cases c <;> simp [mul_comm]
  · rw [List.getD_eq_default _ 0 (by simp [intPolyMulLinear]; omega)]
    cases c with
    | zero => omega
    | succ k =>
      have hk1 : p.length ≤ k := by omega
      have hk2 : p.length ≤ k + 1 := by omega
      simp [List.getElem?_eq_none hk1, List.getElem?_eq_none hk2]

private lemma listToIntPoly_ofLinearFactors (l : List (ℤ × ℤ)) :
    listToIntPoly (intPolyOfLinearFactors l) =
      (l.map fun ab ↦ C ab.2 * X - C ab.1).prod := by
  have hgen (l : List (ℤ × ℤ)) (p : List ℤ) :
      listToIntPoly (l.foldl intPolyMulLinear p) =
        listToIntPoly p * (l.map fun ab ↦ C ab.2 * X - C ab.1).prod := by
    induction l generalizing p with
    | nil => simp
    | cons ab rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih,
        listToIntPoly_intPolyMulLinear, mul_assoc]
  have h1 : listToIntPoly [1] = 1 := by
    simp [listToIntPoly]
  rw [intPolyOfLinearFactors, hgen, h1, one_mul]

/-- The `c`-th entry of `intPolyOfLinearFactors l` is the exact `X^c` coefficient of
`∏ (a, b) ∈ l, (b * X - a)`. -/
theorem getD_intPolyOfLinearFactors_eq_coeff (l : List (ℤ × ℤ)) (c : ℕ) :
    (intPolyOfLinearFactors l).getD c 0 =
      ((l.map fun ab ↦ (C ab.2 * X - C ab.1 : ℤ[X])).prod).coeff c := by
  rw [← listToIntPoly_ofLinearFactors, coeff_listToIntPoly]

private lemma size_getD_le_of_forall {p : List ℤ} {M : ℕ}
    (hp : ∀ z ∈ p, z.natAbs.size ≤ M) (i : ℕ) :
    (p.getD i 0).natAbs.size ≤ M := by
  by_cases hi : i < p.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hp _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ 0 (Nat.le_of_not_lt hi)]
    simp

private lemma size_mem_intPolyMulLinear {p : List ℤ} {M : ℕ} (ab : ℤ × ℤ)
    (hp : ∀ z ∈ p, z.natAbs.size ≤ M) {z : ℤ} (hz : z ∈ intPolyMulLinear p ab) :
    z.natAbs.size ≤ M + (encPair encIntBin encIntBin ab).length + 1 := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  have hpair : ab.1.natAbs.size + ab.2.natAbs.size ≤ (encPair encIntBin encIntBin ab).length := by
    simp only [length_encPair, length_encIntBin]
    omega
  have hr : (ab.1 * p.getD i 0).natAbs.size ≤ ab.1.natAbs.size + M :=
    (Int.size_natAbs_mul_le _ _).trans (Nat.add_le_add_left (size_getD_le_of_forall hp i) _)
  have hl : (if i = 0 then (0 : ℤ) else ab.2 * p.getD (i - 1) 0).natAbs.size ≤
      ab.2.natAbs.size + M := by
    split_ifs
    · simp
    · exact (Int.size_natAbs_mul_le _ _).trans
        (Nat.add_le_add_left (size_getD_le_of_forall hp (i - 1)) _)
  have hsub := Int.size_natAbs_sub_le
    (if i = 0 then (0 : ℤ) else ab.2 * p.getD (i - 1) 0) (ab.1 * p.getD i 0)
  omega

private lemma size_mem_foldl_intPolyMulLinear :
    ∀ (l : List (ℤ × ℤ)) (p : List ℤ) (M : ℕ),
      (∀ z ∈ p, z.natAbs.size ≤ M) →
      ∀ z ∈ l.foldl intPolyMulLinear p,
        z.natAbs.size ≤ M + (encList (encPair encIntBin encIntBin) l).length
  | [], p, M, hp, z, hz => by simpa using hp z hz
  | ab :: rest, p, M, hp, z, hz => by
    simp only [List.foldl_cons] at hz
    have hstep : ∀ w ∈ intPolyMulLinear p ab,
        w.natAbs.size ≤ M + (encPair encIntBin encIntBin ab).length + 1 :=
      fun w hw ↦ size_mem_intPolyMulLinear ab hp hw
    have hih := size_mem_foldl_intPolyMulLinear rest (intPolyMulLinear p ab) _ hstep z hz
    simp only [encList_cons, List.length_append, length_frame]
    omega

private lemma length_encList_le_of_forall {α : Type} (enc : α ↪ List Bool) :
    ∀ (l : List α) (B : ℕ), (∀ x ∈ l, (enc x).length ≤ B) →
      (encList enc l).length ≤ l.length * (2 * B + 2)
  | [], _, _ => by simp
  | x :: xs, B, h => by
    have hx := h x List.mem_cons_self
    have hxs := length_encList_le_of_forall enc xs B fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    have : 2 * (enc x).length + 1 + (encList enc xs).length ≤
        (2 * B + 2) + xs.length * (2 * B + 2) := by omega
    nlinarith

private lemma computableInPolyTime_intPolyMulLinear :
    ComputableInPolyTime (fun q : List ℤ × (ℤ × ℤ) ↦ intPolyMulLinear q.1 q.2)
      (encPair (encList encIntBin) (encPair encIntBin encIntBin)) (encList encIntBin) := by
  unfold intPolyMulLinear
  have hp := ComputableInPolyTime.fst (encList encIntBin) (encPair encIntBin encIntBin)
  have hab := ComputableInPolyTime.snd (encList encIntBin) (encPair encIntBin encIntBin)
  have hcnt : ComputableInPolyTime
      (fun q : List ℤ × (ℤ × ℤ) ↦ q.1.length + 1)
      (encPair (encList encIntBin) (encPair encIntBin encIntBin)) encUnary := by
    have hlen := (ComputableInPolyTime.length encIntBin).comp hp
    fun_prop
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hcnt) ?_
  have hq := ComputableInPolyTime.fst
    (encPair (encList encIntBin) (encPair encIntBin encIntBin)) encUnary
  have hi := ComputableInPolyTime.snd
    (encPair (encList encIntBin) (encPair encIntBin encIntBin)) encUnary
  have hp' := hp.comp hq
  have ha := (ComputableInPolyTime.fst encIntBin encIntBin).comp (hab.comp hq)
  have hb := (ComputableInPolyTime.snd encIntBin encIntBin).comp (hab.comp hq)
  have hget_i := ComputableInPolyTime.listGetDWithInput hp' hi (0 : ℤ)
  have hget_im1 := ComputableInPolyTime.listGetDWithInput hp'
    (ComputableInPolyTime.unary_sub' hi (ComputableInPolyTime.const 1)) (0 : ℤ)
  have hi0 := ComputableInPolyTime.unary_eq' hi (ComputableInPolyTime.const 0)
  have hleft := hi0.ite' (ComputableInPolyTime.const (0 : ℤ))
    (ComputableInPolyTime.intBin_mul' hb hget_im1)
  exact (ComputableInPolyTime.intBin_sub' hleft
    (ComputableInPolyTime.intBin_mul' ha hget_i)).of_enc_eq fun x ↦ by simp

/-- Expanding a list of linear integer factors is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_intPolyOfLinearFactors :
    ComputableInPolyTime intPolyOfLinearFactors
      (encList (encPair encIntBin encIntBin)) (encList encIntBin) := by
  unfold intPolyOfLinearFactors
  refine ComputableInPolyTime.foldl'
    (encA := encPair encIntBin encIntBin)
    (encL := encList (encPair encIntBin encIntBin))
    (encB := encList encIntBin)
    ComputableInPolyTime.id'
    (ComputableInPolyTime.const [1])
    computableInPolyTime_intPolyMulLinear
    (B := fun l ↦ ((encList (encPair encIntBin encIntBin) l).length + 1) *
      (2 * (encList (encPair encIntBin encIntBin) l).length + 6))
    (by
      refine PolyBounded.of_forall_le 8 2 fun l ↦ ?_
      set N := (encList (encPair encIntBin encIntBin) l).length
      nlinarith)
    fun l i hi ↦ ?_
  set N := (encList (encPair encIntBin encIntBin) l).length
  have htake_enc : (encList (encPair encIntBin encIntBin) (l.take i)).length ≤ N := by
    have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
    have : N = (encList (encPair encIntBin encIntBin) (l.take i)).length +
        (encList (encPair encIntBin encIntBin) (l.drop i)).length := by
      simpa only [N, encList_append, List.length_append] using
        congrArg (fun xs ↦ (encList (encPair encIntBin encIntBin) xs).length) hsplit
    omega
  have hllen : (l.take i).length ≤ N :=
    (List.length_take_le' i l).trans (length_le_length_encList _ l)
  have hacc_len : ((l.take i).foldl intPolyMulLinear [1]).length ≤ N + 1 := by
    rw [length_foldl_intPolyMulLinear, List.length_singleton]
    omega
  have hmem : ∀ z ∈ (l.take i).foldl intPolyMulLinear [1], (encIntBin z).length ≤ N + 2 := by
    intro z hz
    rw [length_encIntBin]
    have hsz := size_mem_foldl_intPolyMulLinear (l.take i) [1] 1
      (fun w hw ↦ by simp only [List.mem_singleton.mp hw]; decide) z hz
    omega
  calc (encList encIntBin ((l.take i).foldl intPolyMulLinear [1])).length
      ≤ ((l.take i).foldl intPolyMulLinear [1]).length * (2 * (N + 2) + 2) :=
        length_encList_le_of_forall encIntBin _ (N + 2) hmem
    _ ≤ (N + 1) * (2 * N + 6) := Nat.mul_le_mul hacc_len (by omega)

/-- Monomial coefficient list `[b_0, …, b_{n-1}]` of the `m`-th Lagrange basis polynomial for the
node list `xs` of length `n`. -/
def lagrangeBasisCoeffs (xs : List ℚ) (m : ℕ) : List ℚ :=
  let others : List ℚ := (xs.zipIdx.filter fun p ↦ decide (p.2 ≠ m)).map Prod.fst
  let xm : ℚ := xs.getD m 0
  let numCoeffs : List ℤ := intPolyOfLinearFactors (others.map fun x ↦ (x.num, (x.den : ℤ)))
  let denScale : ℕ := (others.map Rat.den).prod
  let lagDen : ℚ := ratListProd (others.map fun x ↦ xm - x)
  let denom : ℚ := (denScale : ℚ) * lagDen
  (List.range xs.length).map fun c ↦ ((numCoeffs.getD c 0 : ℤ) : ℚ) / denom

/-- Monomial coefficient list `[c_0, …, c_{n-1}]` of the unique polynomial `P : ℚ[X]` of degree
`< xs.length` satisfying `P(xs[m]) = ys[m]` for all `m < xs.length` (`xs` duplicate-free). -/
def lagrangeInterpCoeffs (xs ys : List ℚ) : List ℚ :=
  let bases : List (List ℚ) := (List.range xs.length).map (lagrangeBasisCoeffs xs)
  (List.range xs.length).map fun c ↦
    ratListSum ((List.range xs.length).map fun m ↦ ys.getD m 0 * (bases.getD m []).getD c 0)

/-- Computing `lagrangeBasisCoeffs` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeBasisCoeffs :
    ComputableInPolyTime (fun p : List ℚ × ℕ ↦ lagrangeBasisCoeffs p.1 p.2)
      (encPair (encList encRat) encUnary) (encList encRat) := by
  unfold lagrangeBasisCoeffs
  have hxs := ComputableInPolyTime.fst (encList encRat) encUnary
  have hm := ComputableInPolyTime.snd (encList encRat) encUnary
  have hzip : ComputableInPolyTime (fun p : List ℚ × ℕ ↦ p.1.zipIdx)
      (encPair (encList encRat) encUnary) (encList (encPair encRat encUnary)) :=
    (ComputableInPolyTime.zipIdx encRat).comp hxs
  have hfilt : ComputableInPolyTime
      (fun p : List ℚ × ℕ ↦ p.1.zipIdx.filter fun q ↦ decide (q.2 ≠ p.2))
      (encPair (encList encRat) encUnary) (encList (encPair encRat encUnary)) := by
    refine ComputableInPolyTime.filterWithInput hzip ?_
    have hi := (ComputableInPolyTime.snd encRat encUnary).comp
      (ComputableInPolyTime.snd (encPair (encList encRat) encUnary) (encPair encRat encUnary))
    have hm' := hm.comp
      (ComputableInPolyTime.fst (encPair (encList encRat) encUnary) (encPair encRat encUnary))
    have heq := ComputableInPolyTime.unary_eq' hi hm'
    exact (ComputableInPolyTime.bool_not.comp heq).of_enc_eq fun x ↦ by
      simp [decide_not]
  have hothers : ComputableInPolyTime
      (fun p : List ℚ × ℕ ↦ (p.1.zipIdx.filter fun q ↦ decide (q.2 ≠ p.2)).map Prod.fst)
      (encPair (encList encRat) encUnary) (encList encRat) :=
    ComputableInPolyTime.mapWithInput hfilt
      ((ComputableInPolyTime.fst encRat encUnary).comp (ComputableInPolyTime.snd _ _))
  have hxm : ComputableInPolyTime (fun p : List ℚ × ℕ ↦ p.1.getD p.2 0)
      (encPair (encList encRat) encUnary) encRat :=
    ComputableInPolyTime.listGetDWithInput hxs hm (0 : ℚ)
  have hpairs : ComputableInPolyTime
      (fun p : List ℚ × ℕ ↦
        ((p.1.zipIdx.filter fun q ↦ decide (q.2 ≠ p.2)).map Prod.fst).map
          fun x ↦ (x.num, (x.den : ℤ)))
      (encPair (encList encRat) encUnary) (encList (encPair encIntBin encIntBin)) := by
    refine ComputableInPolyTime.mapWithInput hothers ?_
    have hx := ComputableInPolyTime.snd (encPair (encList encRat) encUnary) encRat
    exact (ComputableInPolyTime.rat_num.comp hx).prod
      (ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.rat_den.comp hx))
  have hnumCoeffs := computableInPolyTime_intPolyOfLinearFactors.comp hpairs
  have hdenScale : ComputableInPolyTime
      (fun p : List ℚ × ℕ ↦
        (((p.1.zipIdx.filter fun q ↦ decide (q.2 ≠ p.2)).map Prod.fst).map Rat.den).prod)
      (encPair (encList encRat) encUnary) encNat :=
    ComputableInPolyTime.binary_prod.comp <|
      ComputableInPolyTime.mapWithInput hothers
        (ComputableInPolyTime.rat_den.comp (ComputableInPolyTime.snd _ _))
  have hlagDen : ComputableInPolyTime
      (fun p : List ℚ × ℕ ↦
        ratListProd (((p.1.zipIdx.filter fun q ↦ decide (q.2 ≠ p.2)).map Prod.fst).map
          fun x ↦ p.1.getD p.2 0 - x))
      (encPair (encList encRat) encUnary) encRat :=
    computableInPolyTime_ratListProd.comp <|
      ComputableInPolyTime.mapWithInput hothers <|
        ComputableInPolyTime.rat_sub' (hxm.comp (ComputableInPolyTime.fst _ _))
          (ComputableInPolyTime.snd _ _)
  have hdenom := ComputableInPolyTime.rat_mul'
    (ComputableInPolyTime.rat_natCast.comp hdenScale) hlagDen
  have hrange := ComputableInPolyTime.range.comp ((ComputableInPolyTime.length encRat).comp hxs)
  refine ComputableInPolyTime.mapWithInput hrange ?_
  have hp := ComputableInPolyTime.fst (encPair (encList encRat) encUnary) encUnary
  have hc := ComputableInPolyTime.snd (encPair (encList encRat) encUnary) encUnary
  have hcoeff := ComputableInPolyTime.rat_intCast.comp
    (ComputableInPolyTime.listGetDWithInput (hnumCoeffs.comp hp) hc (0 : ℤ))
  exact ComputableInPolyTime.rat_div' hcoeff (hdenom.comp hp)

/-- Computing `lagrangeInterpCoeffs` from `(xs, ys)` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeInterpCoeffs :
    ComputableInPolyTime (fun p : List ℚ × List ℚ ↦ lagrangeInterpCoeffs p.1 p.2)
      (encPair (encList encRat) (encList encRat)) (encList encRat) := by
  unfold lagrangeInterpCoeffs
  have hxs := ComputableInPolyTime.fst (encList encRat) (encList encRat)
  have hys := ComputableInPolyTime.snd (encList encRat) (encList encRat)
  have hrange : ComputableInPolyTime (fun p : List ℚ × List ℚ ↦ List.range p.1.length)
      (encPair (encList encRat) (encList encRat)) (encList encUnary) :=
    (ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.length encRat).comp hxs)).of_enc_eq fun _ ↦ rfl
  have hbases1 : ComputableInPolyTime
      (fun xs : List ℚ ↦ (List.range xs.length).map (lagrangeBasisCoeffs xs))
      (encList encRat) (encList (encList encRat)) :=
    ComputableInPolyTime.mapWithInput (f := lagrangeBasisCoeffs)
      (ComputableInPolyTime.range.comp (ComputableInPolyTime.length encRat))
      computableInPolyTime_lagrangeBasisCoeffs
  have hbases : ComputableInPolyTime
      (fun p : List ℚ × List ℚ ↦ (List.range p.1.length).map (lagrangeBasisCoeffs p.1))
      (encPair (encList encRat) (encList encRat)) (encList (encList encRat)) :=
    (hbases1.comp hxs).of_enc_eq fun _ ↦ rfl
  let stepInner (qc : (List ℚ × List ℚ) × ℕ) (m : ℕ) : ℚ :=
    qc.1.2.getD m 0 *
      (((List.range qc.1.1.length).map (lagrangeBasisCoeffs qc.1.1)).getD m []).getD qc.2 0
  have hinner : ComputableInPolyTime
      (fun r : ((List ℚ × List ℚ) × ℕ) × ℕ ↦ stepInner r.1 r.2)
      (encPair (encPair (encPair (encList encRat) (encList encRat)) encUnary) encUnary)
      encRat := by
    have hp := ComputableInPolyTime.fst (encPair (encList encRat) (encList encRat)) encUnary
    have hc := ComputableInPolyTime.snd (encPair (encList encRat) (encList encRat)) encUnary
    have hpc := ComputableInPolyTime.fst
      (encPair (encPair (encList encRat) (encList encRat)) encUnary) encUnary
    have hm := ComputableInPolyTime.snd
      (encPair (encPair (encList encRat) (encList encRat)) encUnary) encUnary
    have hy := ComputableInPolyTime.listGetDWithInput (hys.comp (hp.comp hpc)) hm (0 : ℚ)
    have hbase_m := ComputableInPolyTime.listGetDWithInput
      (hbases.comp (hp.comp hpc)) hm ([] : List ℚ)
    have hbc := ComputableInPolyTime.listGetDWithInput hbase_m (hc.comp hpc) (0 : ℚ)
    exact (ComputableInPolyTime.rat_mul' hy hbc).of_enc_eq fun _ ↦ rfl
  let stepOuter (p : List ℚ × List ℚ) (c : ℕ) : ℚ :=
    ratListSum ((List.range p.1.length).map (stepInner (p, c)))
  have houter : ComputableInPolyTime
      (fun q : (List ℚ × List ℚ) × ℕ ↦ stepOuter q.1 q.2)
      (encPair (encPair (encList encRat) (encList encRat)) encUnary) encRat := by
    have hrange' : ComputableInPolyTime
        (fun q : (List ℚ × List ℚ) × ℕ ↦ List.range q.1.1.length)
        (encPair (encPair (encList encRat) (encList encRat)) encUnary) (encList encUnary) :=
      (hrange.comp
        (ComputableInPolyTime.fst (encPair (encList encRat) (encList encRat))
          encUnary)).of_enc_eq fun _ ↦ rfl
    exact (computableInPolyTime_ratListSum.comp
      (ComputableInPolyTime.mapWithInput (f := stepInner) hrange' hinner)).of_enc_eq fun _ ↦ rfl
  exact ComputableInPolyTime.mapWithInput (f := stepOuter) hrange houter

private lemma zipIdx_eq_map_range {α : Type*} [Inhabited α] (xs : List α) :
    xs.zipIdx = (List.range xs.length).map fun i ↦ (xs.getD i default, i) := by
  refine List.ext_getElem (by simp) fun i hi _ ↦ ?_
  simp only [List.length_zipIdx] at hi
  rw [List.getElem_zipIdx, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi,
    zero_add]

private lemma list_prod_filter_range_erase {M : Type*} [CommMonoid M] (n m : ℕ) (f : ℕ → M) :
    (((List.range n).filter fun i ↦ decide (i ≠ m)).map f).prod =
      ∏ i ∈ (Finset.range n).erase m, f i := by
  have hnodup : ((List.range n).filter fun i ↦ decide (i ≠ m)).Nodup :=
    List.nodup_range.filter _
  have htoFinset : ((List.range n).filter fun i ↦ decide (i ≠ m)).toFinset =
      (Finset.range n).erase m := by
    ext i
    simp [and_comm]
  rw [← htoFinset, List.prod_toFinset _ hnodup]

private lemma getD_lagrangeBasisCoeffs_eq (xs : List ℚ) {m c : ℕ} (hc : c < xs.length) :
    (lagrangeBasisCoeffs xs m).getD c 0 =
      (Lagrange.basis (Finset.range xs.length) (fun i ↦ xs.getD i 0) m).coeff c := by
  have hlen : c < (lagrangeBasisCoeffs xs m).length := by simp [lagrangeBasisCoeffs, hc]
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [lagrangeBasisCoeffs, List.getElem_map, List.getElem_range, ratListProd_eq_prod]
  set others : List ℚ := (xs.zipIdx.filter fun p ↦ decide (p.2 ≠ m)).map Prod.fst
  have hothers : others =
      ((List.range xs.length).filter fun i ↦ decide (i ≠ m)).map fun i ↦ xs.getD i 0 := by
    have hz : xs.zipIdx = (List.range xs.length).map fun i ↦ (xs.getD i 0, i) :=
      zipIdx_eq_map_range (α := ℚ) xs
    change ((xs.zipIdx.filter fun p ↦ decide (p.2 ≠ m)).map Prod.fst) = _
    rw [hz, List.filter_map, List.map_map]
    rfl
  rw [getD_intPolyOfLinearFactors_eq_coeff]
  have hcast_poly :
      ((((others.map fun x ↦ (x.num, (x.den : ℤ))).map
        fun ab ↦ (C ab.2 * X - C ab.1 : ℤ[X])).prod).coeff c : ℚ) =
      ((others.map fun x ↦ (C (x.den : ℚ) * X - C (x.num : ℚ) : ℚ[X])).prod).coeff c := by
    have hmap : (((others.map fun x ↦ (x.num, (x.den : ℤ))).map
          fun ab ↦ (C ab.2 * X - C ab.1 : ℤ[X])).prod.map (Int.castRingHom ℚ)).coeff c =
        ((((others.map fun x ↦ (x.num, (x.den : ℤ))).map
          fun ab ↦ (C ab.2 * X - C ab.1 : ℤ[X])).prod).coeff c : ℚ) := by
      rw [Polynomial.coeff_map, eq_intCast]
    rw [← hmap, Polynomial.map_list_prod, List.map_map, List.map_map]
    refine congrArg (fun p : ℚ[X] ↦ p.coeff c) (congrArg List.prod (List.map_congr_left ?_))
    intro x _
    simp
  have hscale_poly :
      (others.map fun x ↦ (C (x.den : ℚ) * X - C (x.num : ℚ) : ℚ[X])).prod =
        C (((others.map Rat.den).prod : ℕ) : ℚ) *
          (others.map fun x ↦ (X - C x : ℚ[X])).prod := by
    clear hothers
    induction others with
    | nil => simp
    | cons x rest ih =>
      have hxden : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_pos.ne'
      have hfac : (C (x.den : ℚ) * X - C (x.num : ℚ) : ℚ[X]) =
          C (x.den : ℚ) * (X - C x) := by
        have hx : (x.den : ℚ) * x = (x.num : ℚ) := by
          conv_lhs => arg 2; rw [← Rat.num_div_den x]
          exact mul_div_cancel₀ _ hxden
        rw [mul_sub, ← C_mul, hx]
      simp only [List.map_cons, List.prod_cons, ih, hfac, Nat.cast_mul, C_mul]
      ring
  have hden_ne : (((others.map Rat.den).prod : ℕ) : ℚ) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr (list_prod_pos_of_pos fun d hd ↦ ?_).ne'
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
    exact x.den_pos
  rw [hcast_poly, hscale_poly, Polynomial.coeff_C_mul, mul_div_mul_left _ _ hden_ne]
  have hnum_prod : (others.map fun x ↦ (X - C x : ℚ[X])).prod =
      ∏ j ∈ (Finset.range xs.length).erase m, (X - C (xs.getD j 0)) := by
    rw [hothers, List.map_map]
    exact list_prod_filter_range_erase xs.length m fun j ↦ X - C (xs.getD j 0)
  have hden_prod : (others.map fun x ↦ xs.getD m 0 - x).prod =
      ∏ j ∈ (Finset.range xs.length).erase m, (xs.getD m 0 - xs.getD j 0) := by
    rw [hothers, List.map_map]
    exact list_prod_filter_range_erase xs.length m fun j ↦ xs.getD m 0 - xs.getD j 0
  rw [hnum_prod, hden_prod, Lagrange.basis]
  have hbasis_eq :
      ∏ j ∈ (Finset.range xs.length).erase m,
        Lagrange.basisDivisor (xs.getD m 0) (xs.getD j 0) =
      C (∏ j ∈ (Finset.range xs.length).erase m, (xs.getD m 0 - xs.getD j 0))⁻¹ *
        ∏ j ∈ (Finset.range xs.length).erase m, (X - C (xs.getD j 0)) := by
    rw [← Finset.prod_inv_distrib, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [Lagrange.basisDivisor]
  rw [hbasis_eq, Polynomial.coeff_C_mul, div_eq_inv_mul]

/-- **Exact soundness of `lagrangeInterpCoeffs`**: given a duplicate-free list `xs` of rational
evaluation nodes and any polynomial `P : ℚ[X]` with `P.degree < xs.length`, the `c`-th entry of
`lagrangeInterpCoeffs xs (xs.map P.eval)` equals `P.coeff c` for every `c < xs.length`. -/
theorem getD_lagrangeInterpCoeffs_eq_coeff (P : ℚ[X]) (xs : List ℚ)
    (hnodup : xs.Nodup) (hdeg : P.degree < xs.length) {c : ℕ} (hc : c < xs.length) :
    (lagrangeInterpCoeffs xs (xs.map P.eval)).getD c 0 = P.coeff c := by
  have hinj : Set.InjOn (fun i : ℕ ↦ xs.getD i 0) (Finset.range xs.length) := by
    intro i hi j hj hij
    dsimp only at hij
    have hi' : i < xs.length := Finset.mem_range.mp hi
    have hj' : j < xs.length := Finset.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
    exact (List.Nodup.getElem_inj_iff hnodup).mp hij
  have hdeg' : P.degree < (Finset.range xs.length).card := by
    simpa [Finset.card_range] using hdeg
  have hP : P = Lagrange.interpolate (Finset.range xs.length) (fun i ↦ xs.getD i 0)
      (fun i ↦ P.eval (xs.getD i 0)) :=
    Lagrange.eq_interpolate hinj hdeg'
  have hlen : c < (lagrangeInterpCoeffs xs (xs.map P.eval)).length := by
    simp [lagrangeInterpCoeffs, hc]
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [lagrangeInterpCoeffs, List.getElem_map, List.getElem_range, ratListSum_eq_sum]
  have hsum_range : ∀ (n : ℕ) (f : ℕ → ℚ),
      ((List.range n).map f).sum = ∑ m ∈ Finset.range n, f m := by
    intro n f
    induction n with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [hsum_range]
  conv_rhs => rw [hP, Lagrange.interpolate_apply, coeff_finset_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' : m < xs.length := Finset.mem_range.mp hm
  have hys : (xs.map P.eval).getD m 0 = P.eval (xs.getD m 0) := by
    rw [List.getD_eq_getElem _ _ (by simp [hm']), List.getElem_map, List.getD_eq_getElem _ _ hm']
  have hbm : ((List.range xs.length).map (lagrangeBasisCoeffs xs)).getD m [] =
      lagrangeBasisCoeffs xs m := by
    rw [List.getD_eq_getElem _ _ (by simp [hm']), List.getElem_map, List.getElem_range]
  rw [hys, hbm, getD_lagrangeBasisCoeffs_eq xs hc, Polynomial.coeff_C_mul]

/-- Convenience wrapper around `getD_lagrangeInterpCoeffs_eq_coeff` for
`P.natDegree < xs.length`. -/
theorem getD_lagrangeInterpCoeffs_eq_coeff_of_natDegree_lt (P : ℚ[X]) (xs : List ℚ)
    (hnodup : xs.Nodup) (hdeg : P.natDegree < xs.length) {c : ℕ} (hc : c < xs.length) :
    (lagrangeInterpCoeffs xs (xs.map P.eval)).getD c 0 = P.coeff c :=
  getD_lagrangeInterpCoeffs_eq_coeff P xs hnodup
    ((Polynomial.degree_le_natDegree).trans_lt (WithBot.coe_lt_coe.mpr hdeg)) hc

/-- Geometric progression nodes `[r ^ 1, r ^ 2, …, r ^ (d + 1)]` of length `d + 1`. -/
@[expose]
def geomRatNodes (r : ℚ) (d : ℕ) : List ℚ :=
  (List.range (d + 1)).map fun k ↦ r ^ (k + 1)

/-- `geomRatNodes r d` has length `d + 1`. -/
@[simp]
theorem length_geomRatNodes (r : ℚ) (d : ℕ) : (geomRatNodes r d).length = d + 1 := by
  simp [geomRatNodes]

/-- For `0 < r` and `r ≠ 1`, `geomRatNodes r d` is duplicate-free. -/
theorem nodup_geomRatNodes {r : ℚ} (hr0 : 0 < r) (hr1 : r ≠ 1) (d : ℕ) :
    (geomRatNodes r d).Nodup := by
  rw [geomRatNodes, List.nodup_map_iff_inj_on List.nodup_range]
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hr1 with hlt | hgt
  · have hanti : StrictAnti (fun n : ℕ ↦ r ^ n) := fun _ _ h ↦
      pow_lt_pow_right_of_lt_one₀ hr0 hlt h
    exact Nat.succ.inj (hanti.injective hij)
  · have hmono : StrictMono (fun n : ℕ ↦ r ^ n) := pow_right_strictMono₀ hgt
    exact Nat.succ.inj (hmono.injective hij)

/-- Generating `geomRatNodes r d` for a fixed rational `r` is computable in polynomial time from
unary `d`. -/
@[fun_prop]
theorem computableInPolyTime_geomRatNodes (r : ℚ) :
    ComputableInPolyTime (geomRatNodes r) encUnary (encList encRat) := by
  unfold geomRatNodes
  have hrange : ComputableInPolyTime (fun d : ℕ ↦ List.range (d + 1)) encUnary
      (encList encUnary) :=
    ComputableInPolyTime.range.comp (by fun_prop)
  refine ComputableInPolyTime.mapWithInput hrange ?_
  have hk := ComputableInPolyTime.snd encUnary encUnary
  exact ComputableInPolyTime.rat_pow' (ComputableInPolyTime.const r) (by fun_prop)

/-- Interpolating a polynomial `P : ℚ[X]` of `natDegree ≤ d` from its evaluations on
`geomRatNodes r d` (with `0 < r` and `r ≠ 1`) recovers `P.coeff c` for every `c ≤ d`. -/
theorem getD_lagrangeInterpCoeffs_geomRatNodes {r : ℚ} (hr0 : 0 < r) (hr1 : r ≠ 1)
    (P : ℚ[X]) {d c : ℕ} (hdeg : P.natDegree ≤ d) (hc : c ≤ d) :
    (lagrangeInterpCoeffs (geomRatNodes r d) ((geomRatNodes r d).map P.eval)).getD c 0 =
      P.coeff c :=
  getD_lagrangeInterpCoeffs_eq_coeff_of_natDegree_lt P (geomRatNodes r d)
    (nodup_geomRatNodes hr0 hr1 d) (by simp; omega) (by simp; omega)

/-! ### Bit-graph oracle representation and counting Turing hardness for rational functions -/

/-- Bit index `k` of a normalized rational `q : ℚ`: bit `0` encodes `q.num < 0`, odd indices
`2 * i + 1` encode `q.num.natAbs.testBit i`, and positive even indices `2 * i + 2` encode
`q.den.testBit i`. -/
def ratTestBit (q : ℚ) (k : ℕ) : Bool :=
  if k = 0 then decide (q.num < 0)
  else if k.testBit 0 then q.num.natAbs.testBit (k / 2)
  else q.den.testBit (k / 2 - 1)

/-- Maximum binary bit-size of `|q.num|` and `q.den` for a normalized rational `q : ℚ`. -/
@[expose]
def ratBitSize (q : ℚ) : ℕ :=
  max q.num.natAbs.size q.den.size

/-- Reconstruct a rational number from the `2 * K + 1` bit answers `[ratTestBit q 0, …,
ratTestBit q (2 * K)]`. -/
def ratOfBits (K : ℕ) (bits : List Bool) : ℚ :=
  let neg : Bool := bits.headD false
  let numAbs : ℕ := ofBits ((List.range K).map fun i ↦ bits.getD (2 * i + 1) false)
  let den : ℕ := ofBits ((List.range K).map fun i ↦ bits.getD (2 * i + 2) false)
  Rat.divInt (if neg then -(numAbs : ℤ) else (numAbs : ℤ)) (den : ℤ)

/-- `ratOfBits K` exactly reconstructs `q` from `(List.range (2 * K + 1)).map (ratTestBit q)`
whenever `ratBitSize q ≤ K`. -/
theorem ratOfBits_map_ratTestBit {q : ℚ} {K : ℕ} (hK : ratBitSize q ≤ K) :
    ratOfBits K ((List.range (2 * K + 1)).map (ratTestBit q)) = q := by
  have hnumK : q.num.natAbs.size ≤ K := (le_max_left _ _).trans hK
  have hdenK : q.den.size ≤ K := (le_max_right _ _).trans hK
  unfold ratOfBits
  have hhead : ((List.range (2 * K + 1)).map (ratTestBit q)).headD false = decide (q.num < 0) := by
    rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]
    simp [ratTestBit]
  have hodd : ((List.range K).map fun i ↦
      ((List.range (2 * K + 1)).map (ratTestBit q)).getD (2 * i + 1) false) =
      (List.range K).map q.num.natAbs.testBit := by
    refine List.map_congr_left fun i hi ↦ ?_
    have hi' : i < K := List.mem_range.mp hi
    have hlt : 2 * i + 1 < 2 * K + 1 := by omega
    rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map, List.getElem_range]
    have htb : (2 * i + 1).testBit 0 = true := by simp [Nat.testBit_zero]
    have hdiv : (2 * i + 1) / 2 = i := by omega
    simp [ratTestBit, htb, hdiv]
  have heven : ((List.range K).map fun i ↦
      ((List.range (2 * K + 1)).map (ratTestBit q)).getD (2 * i + 2) false) =
      (List.range K).map q.den.testBit := by
    refine List.map_congr_left fun i hi ↦ ?_
    have hi' : i < K := List.mem_range.mp hi
    have hlt : 2 * i + 2 < 2 * K + 1 := by omega
    rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map, List.getElem_range]
    have htb : (2 * i + 2).testBit 0 = false := by simp [Nat.testBit_zero]
    have hdiv : (2 * i + 2) / 2 - 1 = i := by omega
    have hnz : 2 * i + 2 ≠ 0 := by omega
    simp only [ratTestBit, hnz, ↓reduceIte, htb, Bool.false_eq_true, hdiv]
  dsimp only
  rw [hhead, hodd, heven,
    show ofBits ((List.range K).map q.num.natAbs.testBit) = q.num.natAbs from
      Nat.foldr_bit_testBit hnumK,
    show ofBits ((List.range K).map q.den.testBit) = q.den from
      Nat.foldr_bit_testBit hdenK]
  have hsign : (if decide (q.num < 0) then -(q.num.natAbs : ℤ) else (q.num.natAbs : ℤ)) =
      q.num := by
    cases hq : q.num with
    | ofNat n => simp
    | negSucc n => simp; omega
  rw [hsign, Rat.divInt_eq_div, Int.cast_natCast, Rat.num_div_den]

/-- Reconstructing a rational number via `ratOfBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ratOfBits :
    ComputableInPolyTime (fun p : ℕ × List Bool ↦ ratOfBits p.1 p.2)
      (encPair encUnary encBits) encRat := by
  unfold ratOfBits
  have hK := ComputableInPolyTime.fst encUnary encBits
  have hbits := ComputableInPolyTime.snd encUnary encBits
  have hneg := (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hbits
  have hnumBits : ComputableInPolyTime
      (fun p : ℕ × List Bool ↦ (List.range p.1).map fun i ↦ p.2.getD (2 * i + 1) false)
      (encPair encUnary encBits) encBits := by
    have hlist : ComputableInPolyTime
        (fun p : ℕ × List Bool ↦ (List.range p.1).map fun i ↦ p.2.getD (2 * i + 1) false)
        (encPair encUnary encBits) (encList encBool) :=
      ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hK) <|
        ComputableInPolyTime.bitsGetDWithInput (hbits.comp (ComputableInPolyTime.fst _ _))
          (by fun_prop) false
    exact (bits_encList_polyTime encBool).2.comp hlist
  have hdenBits : ComputableInPolyTime
      (fun p : ℕ × List Bool ↦ (List.range p.1).map fun i ↦ p.2.getD (2 * i + 2) false)
      (encPair encUnary encBits) encBits := by
    have hlist : ComputableInPolyTime
        (fun p : ℕ × List Bool ↦ (List.range p.1).map fun i ↦ p.2.getD (2 * i + 2) false)
        (encPair encUnary encBits) (encList encBool) :=
      ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hK) <|
        ComputableInPolyTime.bitsGetDWithInput (hbits.comp (ComputableInPolyTime.fst _ _))
          (by fun_prop) false
    exact (bits_encList_polyTime encBool).2.comp hlist
  have hnumInt := ComputableInPolyTime.intBin_signMagnitude' hneg
    (ComputableInPolyTime.bitsToNat.comp hnumBits)
  have hdenInt := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.bitsToNat.comp hdenBits)
  exact ComputableInPolyTime.rat_divInt' hnumInt hdenInt

/-- An oracle language `A` answers the normalized sign, numerator, and denominator bits of
`g : β → ℚ` under encoding `encB`. -/
def AnswersRatBits {β : Type} (encB : β ↪ List Bool) (g : β → ℚ) (A : Set (List Bool)) : Prop :=
  ∀ b k, encPair encB encNat (b, k) ∈ A ↔ ratTestBit (g b) k = true

/-- The canonical rational bit-graph language of `g : β → ℚ` under `encB`. -/
def bitGraphRat {β : Type} (encB : β ↪ List Bool) (g : β → ℚ) : Set (List Bool) :=
  encPair encB encNat '' {x | ratTestBit (g x.1) x.2 = true}

/-- `bitGraphRat encB g` satisfies `AnswersRatBits encB g`. -/
theorem answersRatBits_bitGraphRat {β : Type} (encB : β ↪ List Bool) (g : β → ℚ) :
    AnswersRatBits encB g (bitGraphRat encB g) :=
  fun _ _ ↦ (encPair encB encNat).injective.mem_set_image

/-- If `g : β → ℚ` is computable in polynomial time and `encB` has a total polynomial-time decoder,
then `bitGraphRat encB g ∈ P`. -/
theorem bitGraphRat_mem_P {β : Type} {encB : β ↪ List Bool} {g : β → ℚ}
    (D : Decoder encB) (hg : ComputableInPolyTime g encB encRat) :
    bitGraphRat encB g ∈ P encBits := by
  classical
  let D' := D.pair Decoder.nat
  have hdec : ComputableInPolyTime D'.decode encBits (encPair encB encNat) :=
    D'.computableInPolyTime
  have hq : ComputableInPolyTime (fun w ↦ g (D'.decode w).1) encBits encRat :=
    hg.comp ((ComputableInPolyTime.fst _ _).comp hdec)
  have hk : ComputableInPolyTime (fun w ↦ (D'.decode w).2) encBits encNat :=
    (ComputableInPolyTime.snd _ _).comp hdec
  have hnumAbs : ComputableInPolyTime (fun w ↦ (g (D'.decode w).1).num.natAbs) encBits encNat :=
    ComputableInPolyTime.intBin_natAbs.comp (ComputableInPolyTime.rat_num.comp hq)
  have hden : ComputableInPolyTime (fun w ↦ (g (D'.decode w).1).den) encBits encNat :=
    ComputableInPolyTime.rat_den.comp hq
  have hnumSz : ComputableInPolyTime (fun w ↦ (g (D'.decode w).1).num.natAbs.size)
      encBits encUnary := by
    simpa only [Function.comp_def, Nat.size_eq_bits_len] using
      ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.natBits.comp hnumAbs)
  have hdenSz : ComputableInPolyTime (fun w ↦ (g (D'.decode w).1).den.size)
      encBits encUnary := by
    simpa only [Function.comp_def, Nat.size_eq_bits_len] using
      ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.natBits.comp hden)
  have hkHalf : ComputableInPolyTime (fun w ↦ (D'.decode w).2 / 2) encBits encNat :=
    ComputableInPolyTime.binary_div' hk (ComputableInPolyTime.const 2)
  have hkHalfSub : ComputableInPolyTime (fun w ↦ (D'.decode w).2 / 2 - 1) encBits encNat :=
    ComputableInPolyTime.binary_sub' hkHalf (ComputableInPolyTime.const 1)
  have hnumBit := ComputableInPolyTime.binary_testBit hnumAbs
    (ComputableInPolyTime.binary_min_unary' hnumSz hkHalf)
  have hdenBit := ComputableInPolyTime.binary_testBit hden
    (ComputableInPolyTime.binary_min_unary' hdenSz hkHalfSub)
  have hk0 := ComputableInPolyTime.decide_eq' hk (ComputableInPolyTime.const 0)
  have hkOdd := ComputableInPolyTime.binary_testBit hk (ComputableInPolyTime.const 0)
  have hneg := ComputableInPolyTime.intBin_isNeg.comp (ComputableInPolyTime.rat_num.comp hq)
  have hrtb : ComputableInPolyTime (fun w ↦ ratTestBit (g (D'.decode w).1) (D'.decode w).2)
      encBits encBool := by
    have hcap (n i : ℕ) : n.testBit (min n.size i) = n.testBit i := by
      rcases le_total i n.size with h | h
      · rw [min_eq_right h]
      · rw [min_eq_left h, Nat.testBit_eq_false_of_lt (Nat.lt_size_self n),
          Nat.testBit_eq_false_of_lt ((Nat.lt_size_self n).trans_le
            (Nat.pow_le_pow_right two_pos h))]
    exact (hk0.ite' hneg (hkOdd.ite' hnumBit hdenBit)).of_enc_eq fun w ↦ by
      simp [ratTestBit, hcap]
  have hround : ComputableInPolyTime
      (fun w ↦ decide (encPair encB encNat (D'.decode w) = w)) encBits encBool := by
    have henc : ComputableInPolyTime (encPair encB encNat) (encPair encB encNat) encBits := .id'
    have _ := henc.comp hdec
    fun_prop
  refine ⟨fun w ↦ decide (encPair encB encNat (D'.decode w) = w) &&
      ratTestBit (g (D'.decode w).1) (D'.decode w).2,
    ComputableInPolyTime.bool_and' hround hrtb, fun w ↦ ?_⟩
  simp only [bitGraphRat, Set.mem_image, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨x, hx, he⟩ ↦ by subst he; rw [D'.decode_enc]; exact ⟨rfl, hx⟩,
    fun ⟨hw, hbit⟩ ↦ ⟨D'.decode w, hbit, hw⟩⟩

/-- Polynomial-time counting Turing reduction from a natural-number counting problem `f : α → ℕ` to
a rational-valued problem `g : β → ℚ`. -/
def RatCountingTuringReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (f : α → ℕ) (g : β → ℚ) : Prop :=
  PolyTimeOracleProgram encA encNat (AnswersRatBits encB g) (· = f)

/-- A rational-valued problem `g : β → ℚ` is `#P`-hard under polynomial-time counting Turing
reductions when every function in `SharpP` reduces to `g`. -/
def RatCountingTuringHard {β : Type} (encB : β ↪ List Bool) (g : β → ℚ) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (f : α → ℕ),
    f ∈ SharpP encA → RatCountingTuringReducible encA encB f g

/-- Precomposing a rational counting Turing reduction with a parsimonious reduction yields a
rational counting Turing reduction. -/
theorem RatCountingTuringReducible.comp_parsimonious {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → ℕ} {h : β → ℕ} {g : γ → ℚ}
    (hfh : ParsimoniousReducible encA encB f h)
    (hhg : RatCountingTuringReducible encB encC h g) :
    RatCountingTuringReducible encA encC f g := by
  obtain ⟨r, hr, hfr⟩ := hfh
  obtain ⟨prog, hprog, hspec⟩ := hhg
  exact ⟨fun a ↦ prog (r a), hprog.preprocess hr, fun A hA ↦
    funext fun a ↦ (congrFun (hspec A hA) (r a)).trans (hfr a).symm⟩

/-- Transferring parsimonious `#P`-hardness across a rational counting Turing reduction yields
`RatCountingTuringHard`. -/
theorem RatCountingTuringHard.of_sharpPHard {β γ : Type}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {h : β → ℕ} {g : γ → ℚ}
    (hh : SharpPHard encB h) (hhg : RatCountingTuringReducible encB encC h g) :
    RatCountingTuringHard encC g :=
  fun _ encA f hf ↦ hhg.comp_parsimonious (hh encA f hf)

/-- If `f` reduces to `g : β → ℚ` by a rational counting Turing reduction, `g` is computable in
polynomial time, and `encB` has a polynomial-time decoder, then `f` is computable in polynomial
time (`FP`). -/
theorem RatCountingTuringReducible.computableInPolyTime_of_decoder {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (D : Decoder encB)
    {f : α → ℕ} {g : β → ℚ}
    (hfg : RatCountingTuringReducible encA encB f g)
    (hg : ComputableInPolyTime g encB encRat) :
    ComputableInPolyTime f encA encNat := by
  obtain ⟨f', hf', rfl⟩ :=
    hfg.exists_computableInPolyTimeWithOracle (answersRatBits_bitGraphRat encB g)
  exact hf'.computableInPolyTime (bitGraphRat_mem_P D hg)

/-- If a `RatCountingTuringHard` problem `g : β → ℚ` (with a polynomial-time input decoder) is
computable in polynomial time, then every function in `#P` is computable in polynomial time. -/
theorem RatCountingTuringHard.computableInPolyTime_of_decoder {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (D : Decoder encB)
    {g : β → ℚ} (hhard : RatCountingTuringHard encB g)
    (hg : ComputableInPolyTime g encB encRat)
    {f : α → ℕ} (hf : f ∈ SharpP encA) :
    ComputableInPolyTime f encA encNat :=
  (hhard encA f hf).computableInPolyTime_of_decoder D hg

/-- If a `RatCountingTuringHard` problem `g : β → ℚ` (with a polynomial-time input decoder) is
computable in polynomial time, then `P = NP` under every encoding. -/
theorem RatCountingTuringHard.P_eq_NP_of_decoder {α β : Type}
    {encB : β ↪ List Bool} (D : Decoder encB)
    {g : β → ℚ} (hhard : RatCountingTuringHard encB g)
    (hg : ComputableInPolyTime g encB encRat) (encA : α ↪ List Bool) :
    P encA = NP encA := by
  have hSS : ComputableInPolyTime SharpSAT encCNF encNat :=
    hhard.computableInPolyTime_of_decoder D hg SharpSAT.mem_SharpP
  have hSAT : SAT ∈ P encCNF :=
    ⟨fun φ ↦ decide (0 < SharpSAT φ),
      ComputableInPolyTime.binary_lt' (ComputableInPolyTime.const 0) hSS,
      fun φ ↦ by rw [decide_eq_true_eq, SharpSAT, Cslib.Logic.PL.CNF.modelCount_pos_iff]; rfl⟩
  exact Ladner.P_eq_NP_of_SAT_mem_P hSAT encA

/-! ### Composable polynomial-time non-adaptive batch reductions -/

/-- Non-adaptive polynomial-time batch (truth-table) reduction from `f : α → Y` to `g : β → Z`,
with oracle answer sizes measured by `sizeZ : Z → ℕ` and bounded in unary polynomial time. -/
@[expose]
def PolyTimeBatchReducible {α β Y Z : Type}
    (encA : α ↪ List Bool) (encY : Y ↪ List Bool)
    (encB : β ↪ List Bool) (encZ : Z ↪ List Bool)
    (sizeZ : Z → ℕ) (f : α → Y) (g : β → Z) : Prop :=
  ∃ (queries : α → List β) (bound : α → ℕ) (combine : α × List Z → Y),
    ComputableInPolyTime queries encA (encList encB) ∧
    ComputableInPolyTime bound encA encUnary ∧
    ComputableInPolyTime combine (encPair encA (encList encZ)) encY ∧
    (∀ a, ∀ b ∈ queries a, sizeZ (g b) ≤ bound a) ∧
    (∀ a, combine (a, (queries a).map g) = f a)

/-- Single-query constructor for `PolyTimeBatchReducible`: covers parsimonious, metric, and
saturation-rounding reductions making one oracle call `query a`. -/
theorem PolyTimeBatchReducible.of_single {α β Y Z : Type}
    {encA : α ↪ List Bool} {encY : Y ↪ List Bool}
    {encB : β ↪ List Bool} {encZ : Z ↪ List Bool}
    {sizeZ : Z → ℕ} {f : α → Y} {g : β → Z} (defaultZ : Z)
    (query : α → β) (bound : α → ℕ) (recover : α × Z → Y)
    (hquery : ComputableInPolyTime query encA encB)
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hrecover : ComputableInPolyTime recover (encPair encA encZ) encY)
    (hsize : ∀ a, sizeZ (g (query a)) ≤ bound a)
    (hspec : ∀ a, recover (a, g (query a)) = f a) :
    PolyTimeBatchReducible encA encY encB encZ sizeZ f g := by
  refine ⟨fun a ↦ [query a], bound, fun p ↦ recover (p.1, p.2.headD defaultZ),
    (ComputableInPolyTime.cons encB).comp (hquery.prod (ComputableInPolyTime.const [])),
    hbound,
    hrecover.comp ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.headD defaultZ).comp (ComputableInPolyTime.snd _ _))),
    fun a b hb ↦ by rw [List.mem_singleton.mp hb]; exact hsize a,
    fun a ↦ by simpa using hspec a⟩

/-- Guarded single-query constructor: when `guard a = false` returns a polynomial-time fallback
`trivialVal a` without issuing any oracle queries; otherwise queries `query a`. -/
theorem PolyTimeBatchReducible.of_guardedSingle {α β Y Z : Type}
    {encA : α ↪ List Bool} {encY : Y ↪ List Bool}
    {encB : β ↪ List Bool} {encZ : Z ↪ List Bool}
    {sizeZ : Z → ℕ} {f : α → Y} {g : β → Z} (defaultZ : Z)
    (guard : α → Bool) (trivialVal : α → Y)
    (query : α → β) (bound : α → ℕ) (recover : α × Z → Y)
    (hguard : ComputableInPolyTime guard encA encBool)
    (htriv : ComputableInPolyTime trivialVal encA encY)
    (hquery : ComputableInPolyTime query encA encB)
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hrecover : ComputableInPolyTime recover (encPair encA encZ) encY)
    (hsize : ∀ a, guard a = true → sizeZ (g (query a)) ≤ bound a)
    (htrivSpec : ∀ a, guard a = false → trivialVal a = f a)
    (hspec : ∀ a, guard a = true → recover (a, g (query a)) = f a) :
    PolyTimeBatchReducible encA encY encB encZ sizeZ f g := by
  refine ⟨fun a ↦ if guard a then [query a] else [], bound,
    fun p ↦ if guard p.1 then recover (p.1, p.2.headD defaultZ) else trivialVal p.1,
    hguard.ite'
      ((ComputableInPolyTime.cons encB).comp (hquery.prod (ComputableInPolyTime.const [])))
      (ComputableInPolyTime.const []),
    hbound,
    (hguard.comp (ComputableInPolyTime.fst _ _)).ite'
      (hrecover.comp ((ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.headD defaultZ).comp (ComputableInPolyTime.snd _ _))))
      (htriv.comp (ComputableInPolyTime.fst _ _)),
    fun a b hb ↦ ?_,
    fun a ↦ ?_⟩
  · cases hga : guard a
    · simp [hga] at hb
    · simp only [hga, ↓reduceIte, List.mem_singleton] at hb
      rw [hb]
      exact hsize a hga
  · cases hga : guard a
    · simpa [hga] using htrivSpec a hga
    · simpa [hga] using hspec a hga

private def unflattenByLengths {Z : Type} (lens : List ℕ) (zs : List Z) : List (List Z) :=
  (List.range lens.length).map fun i ↦ (zs.drop (lens.take i).sum).take (lens.getD i 0)

private lemma drop_sum_take_flatten {Z : Type} (xss : List (List Z)) :
    ∀ (i : ℕ) (hi : i < xss.length),
      (xss.flatten.drop ((xss.map List.length).take i).sum).take
        ((xss.map List.length).getD i 0) = xss[i] := by
  induction xss with
  | nil => intro i hi; simp at hi
  | cons xs rest ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < rest.length := Nat.lt_of_succ_lt_succ (by simpa using hi)
      simp only [List.flatten_cons, List.map_cons, List.take_succ_cons, List.sum_cons,
        ← List.drop_drop, List.drop_left, List.getD_cons_succ, List.getElem_cons_succ]
      exact ih i hi'

private lemma unflattenByLengths_flatten {Z : Type} (xss : List (List Z)) :
    unflattenByLengths (xss.map List.length) xss.flatten = xss := by
  refine List.ext_getElem (by simp [unflattenByLengths]) fun i _ hi2 ↦ ?_
  simp only [unflattenByLengths, List.getElem_map, List.getElem_range]
  exact drop_sum_take_flatten xss i hi2

private lemma unaryListMax_polyTime :
    ComputableInPolyTime (fun l : List ℕ ↦ l.foldl max 0) (encList encUnary) encUnary := by
  have hmax : ComputableInPolyTime (fun p : ℕ × ℕ ↦ max p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    have hle := ComputableInPolyTime.unary_le' (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.snd _ _)
    exact (hle.ite' (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.fst _ _)).of_enc_eq
      fun p ↦ by simp [max_def]
  refine ComputableInPolyTime.foldl'
    (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    ComputableInPolyTime.id' (ComputableInPolyTime.const 0) hmax
    (B := fun l ↦ (encList encUnary l).length) .self fun l i _ ↦ ?_
  simp only [encUnary_apply, List.length_replicate]
  have hbound : ∀ (xs : List ℕ) (acc : ℕ),
      acc ≤ (encList encUnary l).length →
      (∀ x ∈ xs, x ≤ (encList encUnary l).length) →
      xs.foldl max acc ≤ (encList encUnary l).length := by
    intro xs
    induction xs with
    | nil => intro acc hacc _; exact hacc
    | cons x xs ih =>
      intro acc hacc hxs
      exact ih (max acc x) (max_le hacc (hxs x List.mem_cons_self))
        fun y hy ↦ hxs y (List.mem_cons_of_mem x hy)
  refine hbound (l.take i) 0 (Nat.zero_le _) fun x hx ↦ ?_
  have hmem : x ∈ l := List.mem_of_mem_take hx
  simpa [encUnary_apply] using length_le_encList_of_mem encUnary hmem

private lemma unaryListSum_polyTime :
    ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  refine (ComputableInPolyTime.foldl'
    (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
    (by fun_prop : ComputableInPolyTime (fun p : ℕ × ℕ ↦ p.1 + p.2)
      (encPair encUnary encUnary) encUnary)
    (B := fun l ↦ (encList encUnary l).length) .self fun l i _ ↦ ?_).of_enc_eq
    fun l ↦ by rw [List.sum_eq_foldl]
  simp only [encUnary_apply, List.length_replicate, ← List.sum_eq_foldl]
  have hsum_le : ∀ (xs : List ℕ), xs.sum ≤ (encList encUnary xs).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.sum_cons, encList_cons, List.length_append, length_frame, encUnary_apply,
        List.length_replicate]
      omega
  have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  have htake : (encList encUnary (l.take i)).length ≤ (encList encUnary l).length := by
    have := congrArg (fun xs ↦ (encList encUnary xs).length) hsplit
    simp only [encList_append, List.length_append] at this
    omega
  exact (hsum_le (l.take i)).trans htake

private lemma le_foldl_max_of_mem {l : List ℕ} {x : ℕ} (acc : ℕ) (hx : x ∈ l) :
    x ≤ l.foldl max acc := by
  induction l generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · have hmono : ∀ (zs : List ℕ) (a : ℕ), a ≤ zs.foldl max a := by
        intro zs
        induction zs with
        | nil => intro a; exact le_rfl
        | cons z zs ihz => intro a; exact (le_max_left a z).trans (ihz (max a z))
      exact (le_max_right acc x).trans (hmono ys (max acc x))
    · exact ih (max acc y) hmem

/-- **Transitivity of `PolyTimeBatchReducible`**: non-adaptive polynomial-time batch reductions
compose across arbitrary intermediate instance and value types. -/
theorem PolyTimeBatchReducible.trans {α β γ X Y Z : Type}
    {encA : α ↪ List Bool} {encX : X ↪ List Bool}
    {encB : β ↪ List Bool} {encY : Y ↪ List Bool}
    {encC : γ ↪ List Bool} {encZ : Z ↪ List Bool}
    {sizeY : Y → ℕ} {sizeZ : Z → ℕ}
    {f : α → X} {g : β → Y} {h : γ → Z}
    (hfg : PolyTimeBatchReducible encA encX encB encY sizeY f g)
    (hgh : PolyTimeBatchReducible encB encY encC encZ sizeZ g h) :
    PolyTimeBatchReducible encA encX encC encZ sizeZ f h := by
  obtain ⟨q₁, _, c₁, hq₁, _, hc₁, _, hspec₁⟩ := hfg
  obtain ⟨q₂, b₂, c₂, hq₂, hb₂, hc₂, hsize₂, hspec₂⟩ := hgh
  let queries (a : α) : List γ := (q₁ a).flatMap q₂
  let bound (a : α) : ℕ := ((q₁ a).map b₂).foldl max 0
  let combine (p : α × List Z) : X :=
    let bs := q₁ p.1
    let lens := bs.map fun b ↦ (q₂ b).length
    let chunks := unflattenByLengths lens p.2
    c₁ (p.1, (bs.zip chunks).map c₂)
  have hqueries : ComputableInPolyTime queries encA (encList encC) :=
    (ComputableInPolyTime.flatten encC).comp <|
      ComputableInPolyTime.mapWithInput hq₁ (hq₂.comp (ComputableInPolyTime.snd _ _))
  have hbound : ComputableInPolyTime bound encA encUnary :=
    unaryListMax_polyTime.comp <|
      ComputableInPolyTime.mapWithInput hq₁ (hb₂.comp (ComputableInPolyTime.snd _ _))
  have hunflat : ComputableInPolyTime
      (fun r : List ℕ × List Z ↦ unflattenByLengths r.1 r.2)
      (encPair (encList encUnary) (encList encZ)) (encList (encList encZ)) := by
    unfold unflattenByLengths
    have hlens := ComputableInPolyTime.fst (encList encUnary) (encList encZ)
    have hzs := ComputableInPolyTime.snd (encList encUnary) (encList encZ)
    refine ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length encUnary).comp hlens)) ?_
    have hr := ComputableInPolyTime.fst (encPair (encList encUnary) (encList encZ)) encUnary
    have hi := ComputableInPolyTime.snd (encPair (encList encUnary) (encList encZ)) encUnary
    have hsum := unaryListSum_polyTime.comp
      (ComputableInPolyTime.listTakeWithInput (hlens.comp hr) hi)
    have hli := ComputableInPolyTime.listGetDWithInput (hlens.comp hr) hi (0 : ℕ)
    exact ComputableInPolyTime.listTakeWithInput
      (ComputableInPolyTime.listDropWithInput (hzs.comp hr) hsum) hli
  have hcombine : ComputableInPolyTime combine (encPair encA (encList encZ)) encX := by
    have ha := ComputableInPolyTime.fst encA (encList encZ)
    have hzs := ComputableInPolyTime.snd encA (encList encZ)
    have hbs := hq₁.comp ha
    have hlens : ComputableInPolyTime (fun p : α × List Z ↦ (q₁ p.1).map fun b ↦ (q₂ b).length)
        (encPair encA (encList encZ)) (encList encUnary) :=
      ComputableInPolyTime.mapWithInput hbs
        (((ComputableInPolyTime.length encC).comp hq₂).comp (ComputableInPolyTime.snd _ _))
    have hchunks := hunflat.comp (hlens.prod hzs)
    have hzip := (ComputableInPolyTime.zip encB (encList encZ)).comp (hbs.prod hchunks)
    have hys : ComputableInPolyTime
        (fun p : α × List Z ↦ ((q₁ p.1).zip
          (unflattenByLengths ((q₁ p.1).map fun b ↦ (q₂ b).length) p.2)).map c₂)
        (encPair encA (encList encZ)) (encList encY) :=
      ComputableInPolyTime.mapWithInput hzip
        (hc₂.comp (ComputableInPolyTime.snd
          (encPair encA (encList encZ)) (encPair encB (encList encZ))))
    exact hc₁.comp (ha.prod hys)
  refine ⟨queries, bound, combine, hqueries, hbound, hcombine, fun a c hc ↦ ?_, fun a ↦ ?_⟩
  · obtain ⟨b, hb, hcb⟩ := List.mem_flatMap.mp hc
    exact (hsize₂ b c hcb).trans (le_foldl_max_of_mem 0 (List.mem_map_of_mem hb))
  · dsimp only [combine, queries]
    have hflat : ((q₁ a).flatMap q₂).map h = ((q₁ a).map fun b ↦ (q₂ b).map h).flatten := by
      rw [List.map_flatMap, List.flatMap_def]
    have hlens : ((q₁ a).map fun b ↦ (q₂ b).length) =
        ((q₁ a).map fun b ↦ (q₂ b).map h).map List.length := by
      rw [List.map_map]
      exact List.map_congr_left fun b _ ↦ (List.length_map _).symm
    rw [hflat, hlens, unflattenByLengths_flatten]
    have hzip : ((q₁ a).zip ((q₁ a).map fun b ↦ (q₂ b).map h)).map c₂ = (q₁ a).map g := by
      refine List.ext_getElem (by simp) fun i hi1 hi2 ↦ ?_
      have hi : i < (q₁ a).length := by simpa using hi2
      simp [hspec₂]
    rw [hzip, hspec₁]

/-- Every `ℕ → ℕ` batch reduction yields a `Cslib.Complexity.CountingTuringReducible` reduction. -/
theorem PolyTimeBatchReducible.toCountingTuringReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → ℕ} {g : β → ℕ}
    (h : PolyTimeBatchReducible encA encNat encB encNat Nat.size f g) :
    CountingTuringReducible encA encB f g := by
  obtain ⟨queries, bound, combine, hq, hb, hc, hsize, hspec⟩ := h
  exact PolyTimeOracleProgram.of_batchNatBits queries bound combine hq hb hc hsize hspec

private def ratBitWords {β : Type} (encB : β ↪ List Bool) (b : β) (K : ℕ) : List (List Bool) :=
  (List.range (2 * K + 1)).map fun k ↦ encPair encB encNat (b, k)

private def batchRatBitWords {β : Type} (encB : β ↪ List Bool) (qs : List β) (K : ℕ) :
    List (List Bool) :=
  qs.flatMap fun b ↦ ratBitWords encB b K

private def decodeRatBatch (count K : ℕ) (bits : List Bool) : List ℚ :=
  let W := 2 * K + 1
  (List.range count).map fun j ↦ ratOfBits K ((bits.drop (j * W)).take W)

private lemma drop_take_flatMap_fixed {γ δ : Type*} (l : List γ) (f : γ → List δ) (W : ℕ)
    (hlen : ∀ x ∈ l, (f x).length = W) {j : ℕ} (hj : j < l.length) :
    ((l.flatMap f).drop (j * W)).take W = f l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a rest ih =>
    cases j with
    | zero => simpa using List.take_left' (hlen a List.mem_cons_self)
    | succ j =>
      rw [List.flatMap_cons, show (j + 1) * W = W + j * W by ring, ← List.drop_drop,
        List.drop_left' (hlen a List.mem_cons_self), List.getElem_cons_succ]
      exact ih (fun x hx ↦ hlen x (List.mem_cons_of_mem a hx)) (Nat.lt_of_succ_lt_succ hj)

/-- Every `ℕ ← ℚ` batch reduction yields a `RatCountingTuringReducible` reduction. -/
theorem PolyTimeBatchReducible.toRatCountingTuringReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → ℕ} {g : β → ℚ}
    (h : PolyTimeBatchReducible encA encNat encB encRat ratBitSize f g) :
    RatCountingTuringReducible encA encB f g := by
  classical
  obtain ⟨queries, bound, combine, hq, hb, hc, hsize, hspec⟩ := h
  let prog (a : α) : WordQueryComp Unit ℕ :=
    (fun bits ↦ combine (a, decodeRatBatch (queries a).length (bound a) bits)) <$>
      queryWords (batchRatBitWords encB (queries a) (bound a))
  have hrbw : ComputableInPolyTime (fun p : ℕ × β ↦ ratBitWords encB p.2 p.1)
      (encPair encUnary encB) (encList encBits) := by
    unfold ratBitWords
    have hK := ComputableInPolyTime.fst encUnary encB
    have hrange : ComputableInPolyTime (fun p : ℕ × β ↦ List.range (2 * p.1 + 1))
        (encPair encUnary encB) (encList encUnary) :=
      ComputableInPolyTime.range.comp (by fun_prop)
    refine ComputableInPolyTime.mapWithInput hrange ?_
    exact ComputableInPolyTime.encoding_comp <|
      ((ComputableInPolyTime.snd encUnary encB).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  have hbatch : ComputableInPolyTime (fun a : α ↦ batchRatBitWords encB (queries a) (bound a))
      encA (encList encBits) :=
    (ComputableInPolyTime.flatMapWith hrbw (ComputableInPolyTime.snd _ _)
      (ComputableInPolyTime.fst _ _)).comp (hq.prod hb)
  have hdec : ComputableInPolyTime
      (fun p : α × List Bool ↦ decodeRatBatch (queries p.1).length (bound p.1) p.2)
      (encPair encA encBits) (encList encRat) := by
    unfold decodeRatBatch
    have ha := ComputableInPolyTime.fst encA encBits
    have hbits := ComputableInPolyTime.snd encA encBits
    have hrange : ComputableInPolyTime (fun p : α × List Bool ↦ List.range (queries p.1).length)
        (encPair encA encBits) (encList encUnary) :=
      (ComputableInPolyTime.range.comp
        (((ComputableInPolyTime.length encB).comp hq).comp ha)).of_enc_eq fun _ ↦ rfl
    have hstep : ComputableInPolyTime
        (fun x : (α × List Bool) × ℕ ↦
          ratOfBits (bound x.1.1)
            ((x.1.2.drop (x.2 * (2 * bound x.1.1 + 1))).take (2 * bound x.1.1 + 1)))
        (encPair (encPair encA encBits) encUnary) encRat := by
      have hp := ComputableInPolyTime.fst (encPair encA encBits) encUnary
      have hj := ComputableInPolyTime.snd (encPair encA encBits) encUnary
      have hKp : ComputableInPolyTime (fun x : (α × List Bool) × ℕ ↦ bound x.1.1)
          (encPair (encPair encA encBits) encUnary) encUnary :=
        (hb.comp (ha.comp hp)).of_enc_eq fun _ ↦ rfl
      have hWp : ComputableInPolyTime (fun x : (α × List Bool) × ℕ ↦ 2 * bound x.1.1 + 1)
          (encPair (encPair encA encBits) encUnary) encUnary :=
        ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hKp)
          (ComputableInPolyTime.const 1)
      have hbp : ComputableInPolyTime (fun x : (α × List Bool) × ℕ ↦ x.1.2)
          (encPair (encPair encA encBits) encUnary) encBits :=
        (hbits.comp hp).of_enc_eq fun _ ↦ rfl
      have hslice := ComputableInPolyTime.bitsTakeWithInput
        (ComputableInPolyTime.bitsDropWithInput hbp
          (ComputableInPolyTime.unary_mul' hj hWp)) hWp
      exact (computableInPolyTime_ratOfBits.comp (hKp.prod hslice)).of_enc_eq fun _ ↦ rfl
    exact ComputableInPolyTime.mapWithInput hrange hstep
  refine ⟨prog, ?_, fun A hA ↦ funext fun a ↦ ?_⟩
  · simp only [prog, Cslib.OracleComp.interpret_map]
    exact (isOraclePPTOn_queryWords.preprocess hbatch).map_with
      (hc.comp ((ComputableInPolyTime.fst _ _).prod hdec))
  · simp only [prog, Cslib.OracleComp.interpret_map, interpret_queryWords]
    change combine (a, decodeRatBatch (queries a).length (bound a) _) = f a
    have hword (b : β) :
        (ratBitWords encB b (bound a)).map (fun w ↦ decide (w ∈ A)) =
          (List.range (2 * bound a + 1)).map (ratTestBit (g b)) := by
      rw [ratBitWords, List.map_map]
      refine List.map_congr_left fun k _ ↦ ?_
      simp only [Function.comp_apply, hA b k]
      cases ratTestBit (g b) k <;> rfl
    have hmap : (batchRatBitWords encB (queries a) (bound a)).map (fun w ↦ decide (w ∈ A)) =
        (queries a).flatMap fun b ↦ (List.range (2 * bound a + 1)).map (ratTestBit (g b)) := by
      rw [batchRatBitWords, List.map_flatMap]
      exact congrArg List.flatten (List.map_congr_left fun b _ ↦ hword b)
    have hdecoded :
        decodeRatBatch (queries a).length (bound a)
          ((queries a).flatMap fun b ↦ (List.range (2 * bound a + 1)).map (ratTestBit (g b))) =
        (queries a).map g := by
      refine List.ext_getElem (by simp [decodeRatBatch]) fun j _ hj2 ↦ ?_
      have hj : j < (queries a).length := by simpa using hj2
      simp only [decodeRatBatch, List.getElem_map, List.getElem_range,
        drop_take_flatMap_fixed (queries a)
          (fun b ↦ (List.range (2 * bound a + 1)).map (ratTestBit (g b)))
          (2 * bound a + 1) (fun _ _ ↦ by simp) hj,
        ratOfBits_map_ratTestBit (hsize a (queries a)[j] (List.getElem_mem hj))]
    rw [hmap, hdecoded, hspec a]

@[local fun_prop]
private lemma computableInPolyTime_zVar' {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun a ↦ zVar (f a) (g a)) enc encNat := by
  unfold zVar
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

@[local fun_prop]
private lemma computableInPolyTime_uVar' {α : Type} {enc : α ↪ List Bool} {f g h : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary)
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun a ↦ uVar (f a) (g a) (h a)) enc encNat := by
  unfold uVar
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

/-- Batch counting reduction from `SharpSAT` to `SharpTwoSAT`, packaging the clause-weight
finite-difference reduction of `CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT`. -/
theorem batchReducible_sharpSAT_sharpTwoSAT :
    PolyTimeBatchReducible encCNF encNat encCNF encNat Nat.size SharpSAT SharpTwoSAT := by
  open Cslib.Logic.PL in
  let queries (φ : CNF ℕ) : List (CNF ℕ) :=
    (List.range (φ.length + 1)).map (clauseWeightTwoSAT φ)
  let bound (φ : Cslib.Logic.PL.CNF ℕ) : ℕ :=
    φ.vars.length + φ.length * (φ.length + 1) + 1
  have hcw : ComputableInPolyTime
      (fun p : Cslib.Logic.PL.CNF ℕ × ℕ ↦ clauseWeightTwoSAT p.1 p.2)
      (encPair encCNF encUnary) encCNF := by
    have hd : ComputableInPolyTime (Cslib.Logic.PL.CNF.distinctVars (V := ℕ))
        encCNF (encList encNat) := SAT.computableInPolyTime_distinctVars
    have hgadget : ComputableInPolyTime
        (fun p : ℕ × (Cslib.Logic.PL.Clause ℕ × ℕ) ↦ clauseWeightGadget p.1 p.2)
        (encPair encUnary (encPair (encList (encPair encNat encBool)) encUnary)) encCNF := by
      polytime [clauseWeightGadget]
    polytime [clauseWeightTwoSAT, clauseWeightVarTauts]
  have hqueries : ComputableInPolyTime queries encCNF (encList encCNF) := by
    polytime
  have hbound : ComputableInPolyTime bound encCNF encUnary := by
    have hv := SAT.computableInPolyTime_vars_length ComputableInPolyTime.id'
    have hm := SAT.computableInPolyTime_length ComputableInPolyTime.id'
    fun_prop
  refine ⟨queries, bound, clauseWeightCombine, hqueries, hbound,
    by polytime [clauseWeightCombine], fun φ ψ hψ ↦ ?_,
    fun φ ↦ by simpa only [queries, List.map_map, Function.comp_def] using
      clauseWeightCombine_spec φ⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hψ
  rw [List.mem_range] at hr
  exact size_SharpTwoSAT_clauseWeightTwoSAT_le (by omega)

/-- Any counting problem `g : β → ℕ` receiving a batch reduction from `SharpTwoSAT` is `#P`-hard
under `Cslib.Complexity.CountingTuringHard`. -/
theorem countingTuringHard_of_batch_sharpTwoSAT {β : Type} {encB : β ↪ List Bool} {g : β → ℕ}
    (h : PolyTimeBatchReducible encCNF encNat encB encNat Nat.size SharpTwoSAT g) :
    CountingTuringHard encB g :=
  CookLevin.SharpSAT_sharpPHard.trans_countingTuring
    (batchReducible_sharpSAT_sharpTwoSAT.trans h).toCountingTuringReducible

/-- Any rational-valued problem `g : β → ℚ` receiving a batch reduction from `SharpTwoSAT` is
`#P`-hard under `RatCountingTuringHard`. -/
theorem ratCountingTuringHard_of_batch_sharpTwoSAT {β : Type} {encB : β ↪ List Bool} {g : β → ℚ}
    (h : PolyTimeBatchReducible encCNF encNat encB encRat ratBitSize SharpTwoSAT g) :
    RatCountingTuringHard encB g :=
  RatCountingTuringHard.of_sharpPHard CookLevin.SharpSAT_sharpPHard
    (batchReducible_sharpSAT_sharpTwoSAT.trans h).toRatCountingTuringReducible

/-- Composing a batch reduction from `SharpTwoSAT` to `h : β → ℚ` with a batch reduction from `h`
to `g : γ → ℕ` proves `Cslib.Complexity.CountingTuringHard encC g`. -/
theorem countingTuringHard_of_rat_batch {β γ : Type}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {h : β → ℚ} {g : γ → ℕ}
    (h₁ : PolyTimeBatchReducible encCNF encNat encB encRat ratBitSize SharpTwoSAT h)
    (h₂ : PolyTimeBatchReducible encB encRat encC encNat Nat.size h g) :
    CountingTuringHard encC g :=
  countingTuringHard_of_batch_sharpTwoSAT (h₁.trans h₂)

end CslibFrontier.Complexity
