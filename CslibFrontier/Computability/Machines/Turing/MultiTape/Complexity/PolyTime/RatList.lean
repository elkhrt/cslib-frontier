/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate


public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Roots

import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.Reduction.Turing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Polynomial-Time Rational List Operations, Multinomials, and Lagrange Recovery

This module extends the multi-tape Turing machine polynomial-time library over `ℕ`, `ℤ`, and `ℚ`
with five general building blocks:

1. **Unary list sums, binary list products, and multinomial coefficients**:
   `CslibFrontier.PolyTime.RatList.unary_list_sum`,
   `CslibFrontier.PolyTime.RatList.binary_list_prod`, and
   `CslibFrontier.PolyTime.RatList.binary_multinomial` (`encList encUnary → encNat` for
   `List.multinomial`).
2. **Polynomial-time sums and products over `ℚ`**:
   `CslibFrontier.PolyTime.RatList.rat_list_prod` and `CslibFrontier.PolyTime.RatList.rat_list_sum`
   (`encList encRat → encRat`), together with finite-set and unary-range wrappers
   `rat_finset_prod`, `rat_finset_sum`, `rat_prod_range`, and `rat_sum_range`.
3. **Total rational decoding**:
   `CslibFrontier.PolyTime.RatList.decodeRat` and
   `CslibFrontier.PolyTime.RatList.ratDecoder : Decoder encRat`.
4. **Polynomial-time univariate Lagrange coefficient extraction over `ℚ`**:
   `CslibFrontier.PolyTime.RatList.lagrangeCoeffs`, certified in polynomial time via
   `CslibFrontier.PolyTime.RatList.computableInPolyTime_lagrangeCoeffs` and proved to recover every
   coefficient `P.coeff k` of any rational polynomial `P : ℚ[X]` of degree `< d` from its values
   `[P.eval 0, …, P.eval (d - 1)]`
   (`CslibFrontier.PolyTime.RatList.lagrangeCoeffs_getD_of_degree_lt`).
5. **Batch rational function-oracle Turing reductions**:
   `CslibFrontier.PolyTime.RatList.AnswersRatBits`, `CslibFrontier.PolyTime.RatList.ratBitGraph`,
   `CslibFrontier.PolyTime.RatList.ratBitGraph_mem_P`, and
   `CslibFrontier.PolyTime.RatList.polyTimeOracleProgram_of_batchRat`, collapsing to plain
   `ComputableInPolyTime` whenever the queried rational oracle itself lies in `FP`
   (`CslibFrontier.PolyTime.RatList.computableInPolyTime_of_batchRat`).

## Main definitions

* `CslibFrontier.PolyTime.RatList.decodeRat`, `CslibFrontier.PolyTime.RatList.ratDecoder`
* `CslibFrontier.PolyTime.RatList.toPoly`, `CslibFrontier.PolyTime.RatList.mulSubConstCoeffs`,
  `CslibFrontier.PolyTime.RatList.lagrangeBasisNumCoeffs`,
  `CslibFrontier.PolyTime.RatList.lagrangeCoeffs`
* `CslibFrontier.PolyTime.RatList.AnswersRatBits`, `CslibFrontier.PolyTime.RatList.ratBitGraph`

## Main results

* `CslibFrontier.PolyTime.RatList.unary_list_sum`,
  `CslibFrontier.PolyTime.RatList.binary_list_prod`,
  `CslibFrontier.PolyTime.RatList.binary_multinomial`
* `CslibFrontier.PolyTime.RatList.rat_list_prod`, `CslibFrontier.PolyTime.RatList.rat_list_sum`,
  `CslibFrontier.PolyTime.RatList.rat_prod_range`, `CslibFrontier.PolyTime.RatList.rat_sum_range`
* `CslibFrontier.PolyTime.RatList.toPoly_lagrangeCoeffs`,
  `CslibFrontier.PolyTime.RatList.lagrangeCoeffs_getD_of_degree_lt`,
  `CslibFrontier.PolyTime.RatList.computableInPolyTime_lagrangeCoeffs`
* `CslibFrontier.PolyTime.RatList.ratBitGraph_mem_P`,
  `CslibFrontier.PolyTime.RatList.polyTimeOracleProgram_of_batchRat`,
  `CslibFrontier.PolyTime.RatList.computableInPolyTimeWithOracle_of_batchRat`,
  `CslibFrontier.PolyTime.RatList.computableInPolyTime_of_batchRat`

## Tags

polynomial time, rational arithmetic, multinomial coefficients, Lagrange interpolation, oracle
reductions
-/

public section

namespace CslibFrontier.PolyTime.RatList

open Polynomial Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Cslib Cslib.Complexity

/-! ### Unary Sums, Binary Products, and Multinomial Coefficients -/

section Multinomial

/-- Sum of a list of unary natural numbers in unary. -/
@[fun_prop]
theorem unary_list_sum :
    ComputableInPolyTime (fun l : List ℕ ↦ l.sum) (encList encUnary) encUnary := by
  have hq := fst (encPair (encList encUnary) encUnary) encUnary
  have h := foldlWith_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (encB := encUnary) (par := fun l : List ℕ ↦ l) (list := fun l ↦ l)
    (init := fun _ ↦ 0) (step := fun _ s a ↦ s + a)
    id' id' (const 0) (unary_add.comp (hq.snd'.prod (snd _ _)))
    (growth := fun l ↦ (encList encUnary l).length) .self
    (fun l s a ha ↦ by
      have hmem := SizedListEncoding.length_elem_le (encA := encUnary)
        (encL := encList encUnary) l a ha
      simp only [encUnary_apply, List.length_replicate] at hmem ⊢
      omega)
  simpa only [← List.sum_eq_foldl] using h

/-- Sum of a computed list of unary naturals. -/
@[fun_prop]
theorem unary_list_sum' {α : Type} {encIn : α ↪ List Bool} {f : α → List ℕ}
    (hf : ComputableInPolyTime f encIn (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ (f x).sum) encIn encUnary :=
  unary_list_sum.comp hf

/-- Product of a list of binary natural numbers in binary. -/
@[fun_prop]
theorem binary_list_prod :
    ComputableInPolyTime (fun l : List ℕ ↦ l.prod) (encList encNat) encNat := by
  have hq := fst (encPair (encList encNat) encNat) encNat
  have h := foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (encB := encNat) (par := fun l : List ℕ ↦ l) (list := fun l ↦ l)
    (init := fun _ ↦ 1) (step := fun _ s a ↦ s * a)
    id' id' (const 1) (binary_mul' hq.snd' (snd _ _))
    (growth := fun l ↦ (encList encNat l).length) .self
    (fun l s a ha ↦ by
      have hmem := SizedListEncoding.length_elem_le (encA := encNat)
        (encL := encList encNat) l a ha
      have hmul := Nat.size_mul_le s a
      simp only [encNat_apply, Nat.size_eq_bits_len] at hmem hmul ⊢
      omega)
  simpa only [← List.prod_eq_foldl] using h

/-- Product of a computed list of binary naturals. -/
@[fun_prop]
theorem binary_list_prod' {α : Type} {encIn : α ↪ List Bool} {f : α → List ℕ}
    (hf : ComputableInPolyTime f encIn (encList encNat)) :
    ComputableInPolyTime (fun x ↦ (f x).prod) encIn encNat :=
  binary_list_prod.comp hf

private theorem prod_factorial_mul_multinomial (l : List ℕ) :
    (l.map Nat.factorial).prod * l.multinomial = l.sum.factorial := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.sum_cons, List.multinomial_cons]
    calc (x.factorial * (l.map Nat.factorial).prod) * ((x + l.sum).choose x * l.multinomial)
        = (x + l.sum).choose x * x.factorial * ((l.map Nat.factorial).prod * l.multinomial) := by
            ring
      _ = (x + l.sum).choose x * x.factorial * l.sum.factorial := by rw [ih]
      _ = (x + l.sum).factorial := by
            simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              Nat.add_choose_mul_factorial_mul_factorial l.sum x

private theorem prod_map_factorial_pos (l : List ℕ) : 0 < (l.map Nat.factorial).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [Nat.mul_pos (Nat.factorial_pos x) ih]

/-- Explicit factorial quotient formula for `List.multinomial`. -/
theorem list_multinomial_eq_div (l : List ℕ) :
    l.multinomial = l.sum.factorial / (l.map Nat.factorial).prod := by
  rw [← prod_factorial_mul_multinomial l,
    Nat.mul_div_right _ (prod_map_factorial_pos l)]

/-- Multinomial coefficient `l.multinomial` in binary, from a list of unary natural numbers. -/
@[fun_prop]
theorem binary_multinomial :
    ComputableInPolyTime List.multinomial (encList encUnary) encNat := by
  have hmap : ComputableInPolyTime (fun l : List ℕ ↦ l.map Nat.factorial)
      (encList encUnary) (encList encNat) := by
    simpa only [Function.comp_def] using
      mapWith (f := fun p : Bool × ℕ ↦ p.2.factorial)
        (binary_factorial.comp (snd encBool encUnary)) (const false) id'
  have hdiv : ComputableInPolyTime
      (fun l : List ℕ ↦ l.sum.factorial / (l.map Nat.factorial).prod)
      (encList encUnary) encNat := by
    have hnum : ComputableInPolyTime (fun l : List ℕ ↦ l.sum.factorial)
        (encList encUnary) encNat := binary_factorial.comp unary_list_sum
    have hden : ComputableInPolyTime (fun l : List ℕ ↦ (l.map Nat.factorial).prod)
        (encList encUnary) encNat := binary_list_prod.comp hmap
    fun_prop
  exact hdiv.of_enc_eq fun l ↦ congrArg encNat (list_multinomial_eq_div l)

/-- Multinomial coefficient of a computed list of unary naturals, returned in binary. -/
@[fun_prop]
theorem binary_multinomial' {α : Type} {encIn : α ↪ List Bool} {f : α → List ℕ}
    (hf : ComputableInPolyTime f encIn (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ (f x).multinomial) encIn encNat :=
  binary_multinomial.comp hf

end Multinomial

/-! ### Polynomial-Time Sums and Products over `ℚ` -/

section RatBigOperators

/-- Product of a list of rational numbers in polynomial time. -/
@[fun_prop]
theorem rat_list_prod :
    ComputableInPolyTime (fun l : List ℚ ↦ l.prod) (encList encRat) encRat := by
  have hq := fst (encPair (encList encRat) encRat) encRat
  have h := foldlWith_of_bounded_growth (encA := encRat) (encL := encList encRat)
    (encB := encRat) (par := fun l : List ℚ ↦ l) (list := fun l ↦ l)
    (init := fun _ ↦ (1 : ℚ)) (step := fun _ s a ↦ s * a)
    id' id' (const 1) (rat_mul' hq.snd' (snd _ _))
    (growth := fun l ↦ (encList encRat l).length) .self
    (fun l s a ha ↦
      (length_encRat_mul_le s a).trans <|
        Nat.add_le_add_left
          (SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) l a ha) _)
  simpa only [← List.prod_eq_foldl] using h

/-- Product of a computed list of rational numbers. -/
@[fun_prop]
theorem rat_list_prod' {α : Type} {encIn : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f encIn (encList encRat)) :
    ComputableInPolyTime (fun x ↦ (f x).prod) encIn encRat :=
  rat_list_prod.comp hf

private theorem size_le_of_le_two_pow {a m : ℕ} (ha : a ≤ 2 ^ m) : a.size ≤ m + 1 := by
  refine Nat.size_le.mpr ?_
  have := Nat.two_pow_pos m
  rw [Nat.pow_succ]
  omega

/-- Sum of a list of rational numbers in polynomial time. -/
@[fun_prop]
theorem rat_list_sum :
    ComputableInPolyTime (fun l : List ℚ ↦ l.sum) (encList encRat) encRat := by
  have hspec := foldl_spec (encIn := encList encRat) (encA := encRat) (encB := encRat)
    (encL := encList encRat) (list := fun l : List ℚ ↦ l) (init := fun _ ↦ (0 : ℚ))
    (step := (· + ·)) id' (const 0) rat_add
    (fun l consumed s ↦
      s.den ≤ 2 ^ (consumed.length * (encList encRat l).length) ∧
        s.num.natAbs ≤ consumed.length * 2 ^ (consumed.length * (encList encRat l).length))
    (fun _ ↦ by simp)
    (fun l consumed s q hpre ⟨hsden, hsnum⟩ ↦ by
      let L := (encList encRat l).length
      have hqmem : q ∈ l := hpre.subset (by simp)
      have hqL : (encRat q).length ≤ L :=
        SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) l q hqmem
      have hqden : q.den ≤ 2 ^ L :=
        (den_lt_two_pow_length_encRat q).le.trans (Nat.pow_le_pow_right (by omega) hqL)
      have hqnum : q.num.natAbs ≤ 2 ^ L :=
        (natAbs_num_lt_two_pow_length_encRat q).le.trans (Nat.pow_le_pow_right (by omega) hqL)
      have hpow : 2 ^ ((consumed ++ [q]).length * L) =
          2 ^ (consumed.length * L) * 2 ^ L := by
        simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul, pow_add]
      refine ⟨?_, ?_⟩
      · rw [hpow]
        exact (Rat.den_add_le s q).trans (Nat.mul_le_mul hsden hqden)
      · rw [hpow, List.length_append, List.length_singleton]
        calc (s + q).num.natAbs
            ≤ s.num.natAbs * q.den + q.num.natAbs * s.den := Rat.natAbs_num_add_le s q
          _ ≤ (consumed.length * 2 ^ (consumed.length * L)) * 2 ^ L +
                2 ^ L * 2 ^ (consumed.length * L) :=
              Nat.add_le_add (Nat.mul_le_mul hsnum hqden) (Nat.mul_le_mul hqnum hsden)
          _ = (consumed.length + 1) * (2 ^ (consumed.length * L) * 2 ^ L) := by ring)
    (size := fun l ↦
      3 * ((encList encRat l).length * (encList encRat l).length) +
        2 * (encList encRat l).length + 6)
    (PolyBounded.of_forall_le 6 2 fun l ↦ by nlinarith)
    (fun l consumed s hpre ⟨hsden, hsnum⟩ ↦ by
      let L := (encList encRat l).length
      have hkL : consumed.length ≤ L :=
        hpre.length_le.trans
          (SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) l)
      have hden_le : s.den ≤ 2 ^ (L * L) :=
        hsden.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right L hkL))
      have hnum_le : s.num.natAbs ≤ 2 ^ (L + L * L) := by
        rw [pow_add]
        exact hsnum.trans <| Nat.mul_le_mul
          (hkL.trans Nat.lt_two_pow_self.le)
          (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right L hkL))
      have hsd := size_le_of_le_two_pow hden_le
      have hsn := size_le_of_le_two_pow hnum_le
      rw [length_encRat]
      change 2 * s.num.natAbs.size + s.den.size + 3 ≤ 3 * (L * L) + 2 * L + 6
      omega)
  simpa only [← List.sum_eq_foldl] using hspec.1

/-- Sum of a computed list of rational numbers. -/
@[fun_prop]
theorem rat_list_sum' {α : Type} {encIn : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f encIn (encList encRat)) :
    ComputableInPolyTime (fun x ↦ (f x).sum) encIn encRat :=
  rat_list_sum.comp hf

/-- Multiply a fixed finite family of computed rational numbers. -/
theorem rat_finset_prod {α : Type} {ι : Type*} {enc : α ↪ List Bool} (s : Finset ι)
    {f : ι → α → ℚ} (hf : ∀ i ∈ s, ComputableInPolyTime (f i) enc encRat) :
    ComputableInPolyTime (fun a ↦ ∏ i ∈ s, f i a) enc encRat := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (const 1).of_enc_eq fun _ ↦ congrArg encRat (by simp)
  | insert i s hi ih =>
    exact ((hf i (Finset.mem_insert_self i s)).rat_mul'
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))).of_enc_eq
      fun _ ↦ congrArg encRat (Finset.prod_insert hi)

/-- Sum a fixed finite family of computed rational numbers. -/
theorem rat_finset_sum {α : Type} {ι : Type*} {enc : α ↪ List Bool} (s : Finset ι)
    {f : ι → α → ℚ} (hf : ∀ i ∈ s, ComputableInPolyTime (f i) enc encRat) :
    ComputableInPolyTime (fun a ↦ ∑ i ∈ s, f i a) enc encRat := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (const 0).of_enc_eq fun _ ↦ congrArg encRat (by simp)
  | insert i s hi ih =>
    exact ((hf i (Finset.mem_insert_self i s)).rat_add'
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))).of_enc_eq
      fun _ ↦ congrArg encRat (Finset.sum_insert hi)

private theorem prod_range_eq_list_prod (g : ℕ → ℚ) (m : ℕ) :
    ∏ i ∈ Finset.range m, g i = ((List.range m).map g).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, List.range_succ, List.map_append, List.map_singleton,
      List.prod_append, List.prod_singleton, ih]

private theorem sum_range_eq_list_sum (g : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ Finset.range m, g i = ((List.range m).map g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, ih]

/-- Product of a uniformly computed family of rationals over a computed unary range. -/
@[fun_prop]
theorem rat_prod_range {α : Type} {enc : α ↪ List Bool}
    {f : α × ℕ → ℚ} {r : α → ℕ}
    (hf : ComputableInPolyTime f (encPair enc encUnary) encRat)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun a ↦ ∏ i ∈ Finset.range (r a), f (a, i)) enc encRat :=
  (rat_list_prod.comp (mapWithInput (f := fun a i ↦ f (a, i)) (range.comp hr) hf)).of_enc_eq
    fun a ↦ congrArg encRat (prod_range_eq_list_prod (fun i ↦ f (a, i)) (r a)).symm

/-- Sum of a uniformly computed family of rationals over a computed unary range. -/
@[fun_prop]
theorem rat_sum_range {α : Type} {enc : α ↪ List Bool}
    {f : α × ℕ → ℚ} {r : α → ℕ}
    (hf : ComputableInPolyTime f (encPair enc encUnary) encRat)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun a ↦ ∑ i ∈ Finset.range (r a), f (a, i)) enc encRat :=
  (rat_list_sum.comp (mapWithInput (f := fun a i ↦ f (a, i)) (range.comp hr) hf)).of_enc_eq
    fun a ↦ congrArg encRat (sum_range_eq_list_sum (fun i ↦ f (a, i)) (r a)).symm

end RatBigOperators

/-! ### Total Rational Decoder -/

section RatDecoder

/-- Total bit-string decoder for `encRat`, normalizing arbitrary `(ℤ × ℕ)` pairs via
`Rat.divInt`. -/
def decodeRat (w : List Bool) : ℚ :=
  let p := (Decoder.intBin.pair Decoder.nat).decode w
  Rat.divInt p.1 p.2

/-- `decodeRat` left-inverts `encRat` on every rational number. -/
theorem decodeRat_encRat (q : ℚ) : decodeRat (encRat q) = q := by
  simp only [decodeRat, encRat_apply, (Decoder.intBin.pair Decoder.nat).decode_enc]
  rw [Rat.divInt_eq_div, Int.cast_natCast, Rat.num_div_den]

/-- `decodeRat` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_decodeRat :
    ComputableInPolyTime decodeRat encBits encRat := by
  have hdec := (Decoder.intBin.pair Decoder.nat).computableInPolyTime
  exact rat_divInt' (hdec.fst') (intBin_natCast.comp hdec.snd')

/-- Total polynomial-time `Decoder` for `encRat`. -/
def ratDecoder : Decoder encRat where
  decode := decodeRat
  decode_enc := decodeRat_encRat
  computable := computableInPolyTime_decodeRat.exists_degree

end RatDecoder

/-! ### Univariate Polynomial Coefficient Extraction via Lagrange Interpolation -/

section LagrangeRecovery

/-- Polynomial over `ℚ` represented by its low-to-high coefficient list `cs : List ℚ`. -/
noncomputable def toPoly (cs : List ℚ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length, C (cs.getD k 0) * X ^ k

/-- Every coefficient `k` of `toPoly cs` equals `cs.getD k 0`. -/
@[simp]
theorem coeff_toPoly (cs : List ℚ) (k : ℕ) : (toPoly cs).coeff k = cs.getD k 0 := by
  rw [toPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hk : k < cs.length
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      simp [hbk.symm]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hk) hmem
  · rw [Finset.sum_eq_zero]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hk),
        Option.getD_none]
    · intro b hb
      have hne : k ≠ b := fun hkb ↦ hk (hkb ▸ Finset.mem_range.mp hb)
      simp [hne]

/-- Coefficient list of `(X - C a) * toPoly p`. -/
def mulSubConstCoeffs (p : List ℚ) (a : ℚ) : List ℚ :=
  (List.range (p.length + 1)).map fun k ↦
    (if k = 0 then 0 else p.getD (k - 1) 0) - a * p.getD k 0

@[simp]
theorem length_mulSubConstCoeffs (p : List ℚ) (a : ℚ) :
    (mulSubConstCoeffs p a).length = p.length + 1 := by
  simp [mulSubConstCoeffs]

/-- `mulSubConstCoeffs p a` represents `(X - C a) * toPoly p`. -/
theorem toPoly_mulSubConstCoeffs (p : List ℚ) (a : ℚ) :
    toPoly (mulSubConstCoeffs p a) = (X - C a) * toPoly p := by
  ext k
  rw [coeff_toPoly, sub_mul, coeff_sub, coeff_C_mul, coeff_toPoly]
  have hget : (mulSubConstCoeffs p a).getD k 0 =
      (if k = 0 then 0 else p.getD (k - 1) 0) - a * p.getD k 0 := by
    by_cases hk : k < p.length + 1
    · simp [mulSubConstCoeffs, List.getD_eq_getElem?_getD, hk]
    · have hk0 : k ≠ 0 := by omega
      have hk1 : p.length ≤ k - 1 := by omega
      have hk2 : p.length ≤ k := by omega
      simp [mulSubConstCoeffs, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega : (List.range (p.length + 1)).length ≤ k),
        List.getElem?_eq_none hk1, List.getElem?_eq_none hk2, hk0]
  rw [hget]
  cases k with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_X_mul, coeff_toPoly]

@[fun_prop]
private theorem computableInPolyTime_mulSubConstCoeffs :
    ComputableInPolyTime (fun q : List ℚ × ℚ ↦ mulSubConstCoeffs q.1 q.2)
      (encPair (encList encRat) encRat) (encList encRat) := by
  have hlen1 : ComputableInPolyTime (fun q : List ℚ × ℚ ↦ q.1.length + 1)
      (encPair (encList encRat) encRat) encUnary := by fun_prop
  refine mapWithInput (range.comp hlen1) ?_
  have hp : ComputableInPolyTime (fun r : (List ℚ × ℚ) × ℕ ↦ r.1.1)
      (encPair (encPair (encList encRat) encRat) encUnary) (encList encRat) :=
    (fst _ _).comp (fst _ _)
  have ha : ComputableInPolyTime (fun r : (List ℚ × ℚ) × ℕ ↦ r.1.2)
      (encPair (encPair (encList encRat) encRat) encUnary) encRat :=
    (snd _ _).comp (fst _ _)
  have hk : ComputableInPolyTime (fun r : (List ℚ × ℚ) × ℕ ↦ r.2)
      (encPair (encPair (encList encRat) encRat) encUnary) encUnary :=
    snd _ _
  have hterm1 : ComputableInPolyTime
      (fun r : (List ℚ × ℚ) × ℕ ↦ if r.2 == 0 then (0 : ℚ) else r.1.1.getD (r.2 - 1) 0)
      (encPair (encPair (encList encRat) encRat) encUnary) encRat :=
    (unary_beq hk (const 0)).ite (const 0)
      (listGetDWithInput hp (unary_sub.comp (hk.prod (const 1))) 0)
  have hterm2 : ComputableInPolyTime
      (fun r : (List ℚ × ℚ) × ℕ ↦ r.1.2 * r.1.1.getD r.2 0)
      (encPair (encPair (encList encRat) encRat) encUnary) encRat :=
    rat_mul' ha (listGetDWithInput hp hk 0)
  exact (rat_sub' hterm1 hterm2).of_enc_eq fun r ↦ by
    simp only [beq_iff_eq]

/-- Coefficient list of the monic Lagrange numerator `∏_{j ∈ range d \ {i}} (X - C j)`. -/
def lagrangeBasisNumCoeffs (d i : ℕ) : List ℚ :=
  ((List.range d).filter (· != i)).foldl
    (fun (p : List ℚ) (j : ℕ) ↦ mulSubConstCoeffs p (j : ℚ)) [1]

private theorem lagrangeBasisNumCoeffs_spec :
    ComputableInPolyTime
      (fun par : ℕ × ℕ ↦ lagrangeBasisNumCoeffs par.1 par.2)
      (encPair encUnary encUnary) (encList encRat) ∧
    ∀ par : ℕ × ℕ,
      toPoly (lagrangeBasisNumCoeffs par.1 par.2) =
        (((List.range par.1).filter (· != par.2)).map fun (j : ℕ) ↦ X - C (j : ℚ)).prod := by
  have hnodes : ComputableInPolyTime
      (fun par : ℕ × ℕ ↦ (List.range par.1).filter (· != par.2))
      (encPair encUnary encUnary) (encList encUnary) := by
    refine filterWithInput (range.comp (fst encUnary encUnary)) ?_
    exact bne (snd _ _) ((snd encUnary encUnary).comp (fst _ _))
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List ℚ) × ℕ ↦ mulSubConstCoeffs q.1.2 (q.2 : ℚ))
      (encPair (encPair (encPair encUnary encUnary) (encList encRat)) encUnary)
      (encList encRat) :=
    computableInPolyTime_mulSubConstCoeffs.comp
      (((snd _ _).comp (fst _ _)).prod (rat_natCast.comp (unary_to_binary.comp (snd _ _))))
  have hf := foldlWith_spec (encIn := encPair encUnary encUnary) (encP := encPair encUnary encUnary)
    (encA := encUnary) (encL := encList encUnary) (encB := encList encRat)
    (par := id) (list := fun par : ℕ × ℕ ↦ (List.range par.1).filter (· != par.2))
    (init := fun _ ↦ [(1 : ℚ)])
    (step := fun _ (p : List ℚ) (j : ℕ) ↦ mulSubConstCoeffs p (j : ℚ))
    id' hnodes (const [1]) hstep
    (fun par consumed p ↦
      p.length = consumed.length + 1 ∧
      (∀ q ∈ p, q.den = 1 ∧ q.num.natAbs ≤ (par.1 + 1) ^ consumed.length) ∧
      toPoly p = (consumed.map fun (j : ℕ) ↦ X - C (j : ℚ)).prod)
    (fun par ↦ ⟨rfl, fun q hq ↦ by
      rcases List.mem_singleton.mp hq with rfl
      exact ⟨rfl, by simp⟩, by simp [toPoly]⟩)
    (fun par consumed p j hpre ⟨hlen, hmem, hpoly⟩ ↦ by
      have hjmem : j ∈ (List.range par.1).filter (· != par.2) := hpre.subset (by simp)
      have hjlt : j < par.1 := List.mem_range.mp (List.mem_filter.mp hjmem).1
      refine ⟨by simp [hlen], ?_, ?_⟩
      · intro q hq
        simp only [mulSubConstCoeffs, List.mem_map, List.mem_range] at hq
        rcases hq with ⟨k, _, rfl⟩
        have hget_bound : ∀ idx : ℕ,
            (p.getD idx 0).den = 1 ∧
              (p.getD idx 0).num.natAbs ≤ (par.1 + 1) ^ consumed.length := by
          intro idx
          by_cases hidx : idx < p.length
          · rw [List.getD_eq_getElem _ _ hidx]
            exact hmem _ (List.getElem_mem hidx)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hidx)]
            exact ⟨rfl, Nat.zero_le _⟩
        let a : ℚ := if k = 0 then 0 else p.getD (k - 1) 0
        have ha : a.den = 1 ∧ a.num.natAbs ≤ (par.1 + 1) ^ consumed.length := by
          by_cases hk0 : k = 0
          · simp [a, hk0]
          · simpa [a, hk0] using hget_bound (k - 1)
        have hb := hget_bound k
        have ha_eq : a = (a.num : ℚ) := ((Rat.den_eq_one_iff a).mp ha.1).symm
        have hb_eq : p.getD k 0 = ((p.getD k 0).num : ℚ) :=
          ((Rat.den_eq_one_iff _).mp hb.1).symm
        have hexpr : a - (j : ℚ) * p.getD k 0 =
            ((a.num - (j : ℤ) * (p.getD k 0).num : ℤ) : ℚ) := by
          push_cast
          rw [← ha_eq, ← hb_eq]
        change (a - (j : ℚ) * p.getD k 0).den = 1 ∧
          (a - (j : ℚ) * p.getD k 0).num.natAbs ≤ (par.1 + 1) ^ (consumed ++ [j]).length
        rw [hexpr, Rat.den_intCast, Rat.num_intCast, List.length_append, List.length_singleton,
          pow_succ]
        refine ⟨rfl, ?_⟩
        exact (calc (a.num - (j : ℤ) * (p.getD k 0).num).natAbs
            ≤ a.num.natAbs + ((j : ℤ) * (p.getD k 0).num).natAbs := Int.natAbs_sub_le _ _
          _ = a.num.natAbs + j * (p.getD k 0).num.natAbs := by simp [Int.natAbs_mul]
          _ ≤ (par.1 + 1) ^ consumed.length + par.1 * (par.1 + 1) ^ consumed.length :=
              Nat.add_le_add ha.2 (Nat.mul_le_mul (Nat.le_of_lt hjlt) hb.2)
          _ = (par.1 + 1) ^ consumed.length * (par.1 + 1) := by ring)
      · rw [toPoly_mulSubConstCoeffs, hpoly, List.map_append, List.map_singleton, List.prod_append,
          List.prod_singleton, mul_comm])
    (size := fun par ↦
      let L := (encPair encUnary encUnary par).length
      (L + 1) * (2 * (2 * ((L + 1) * L + 1) + 4) + 1))
    (PolyBounded.of_forall_le 40 3 fun par ↦ by dsimp only; ring_nf; nlinarith)
    (fun par consumed p hpre ⟨hlen, hmem, _⟩ ↦ by
      let L := (encPair encUnary encUnary par).length
      have hdL : par.1 ≤ L := by
        have h1 : (encUnary par.1).length ≤ L := length_le_encPair_left encUnary encUnary par
        have h2 : (encUnary par.1).length = par.1 := by simp [encUnary_apply]
        exact h2 ▸ h1
      have hclen : consumed.length ≤ par.1 :=
        hpre.length_le.trans ((List.length_filter_le _ _).trans (by simp))
      have hplen : p.length ≤ L + 1 := by omega
      have helem : ∀ q ∈ p, (encRat q).length ≤ 2 * ((L + 1) * L + 1) + 4 := by
        intro q hq
        obtain ⟨hqden, hqnum⟩ := hmem q hq
        have hpow_le : q.num.natAbs ≤ 2 ^ ((L + 1) * L) := by
          calc q.num.natAbs
              ≤ (par.1 + 1) ^ consumed.length := hqnum
            _ ≤ (L + 1) ^ L :=
                (Nat.pow_le_pow_left (Nat.add_le_add_right hdL 1) _).trans
                  (Nat.pow_le_pow_right (by omega) (hclen.trans hdL))
            _ ≤ (2 ^ (L + 1)) ^ L :=
                Nat.pow_le_pow_left Nat.lt_two_pow_self.le L
            _ = 2 ^ ((L + 1) * L) := (pow_mul 2 (L + 1) L).symm
        have hnsize := size_le_of_le_two_pow hpow_le
        rw [length_encRat, hqden]
        have hs1 : (1 : ℕ).size = 1 := by decide
        rw [hs1]
        omega
      exact (length_encList_le encRat p helem).trans
        (Nat.mul_le_mul_right _ hplen))
  exact ⟨hf.1, fun par ↦ (hf.2 par).2.2⟩

/-- `lagrangeBasisNumCoeffs` is computable in polynomial time from unary `(d, i)`. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeBasisNumCoeffs :
    ComputableInPolyTime
      (fun par : ℕ × ℕ ↦ lagrangeBasisNumCoeffs par.1 par.2)
      (encPair encUnary encUnary) (encList encRat) :=
  lagrangeBasisNumCoeffs_spec.1

/-- `toPoly (lagrangeBasisNumCoeffs d i)` equals `∏_{j ∈ (range d).erase i} (X - C j)`. -/
theorem toPoly_lagrangeBasisNumCoeffs (d i : ℕ) :
    toPoly (lagrangeBasisNumCoeffs d i) =
      ∏ j ∈ (Finset.range d).erase i, (X - C (j : ℚ)) := by
  rw [lagrangeBasisNumCoeffs_spec.2 (d, i)]
  have hfin : ((List.range d).filter (· != i)).toFinset = (Finset.range d).erase i := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq,
      Finset.mem_erase, Finset.mem_range, and_comm]
  rw [← hfin]
  exact (List.prod_toFinset (fun (j : ℕ) ↦ X - C (j : ℚ))
    (List.Nodup.filter _ List.nodup_range)).symm

/-- Extract the coefficient list `[c_0, …, c_{d - 1}]` of the unique degree-`< d` polynomial
taking values `vals = [y_0, …, y_{d - 1}]` at `0, 1, …, d - 1` via Lagrange interpolation. -/
def lagrangeCoeffs (vals : List ℚ) : List ℚ :=
  let d := vals.length
  (List.range d).map fun k ↦
    ((List.range d).map fun i ↦
      (vals.getD i 0 /
        (((List.range d).filter (· != i)).map fun (j : ℕ) ↦ (i : ℚ) - (j : ℚ)).prod) *
      (lagrangeBasisNumCoeffs d i).getD k 0).sum

@[simp]
theorem length_lagrangeCoeffs (vals : List ℚ) :
    (lagrangeCoeffs vals).length = vals.length := by
  simp [lagrangeCoeffs]

/-- `lagrangeCoeffs vals` computes the exact coefficients of the Lagrange interpolant on
`0, 1, …, vals.length - 1`. -/
theorem toPoly_lagrangeCoeffs (vals : List ℚ) :
    toPoly (lagrangeCoeffs vals) =
      ∑ i ∈ Finset.range vals.length,
        C (vals.getD i 0 /
            ∏ j ∈ (Finset.range vals.length).erase i, ((i : ℚ) - (j : ℚ))) *
          ∏ j ∈ (Finset.range vals.length).erase i, (X - C (j : ℚ)) := by
  let d := vals.length
  have hprod_denom : ∀ i : ℕ,
      (((List.range d).filter (· != i)).map fun (j : ℕ) ↦ (i : ℚ) - (j : ℚ)).prod =
        ∏ j ∈ (Finset.range d).erase i, ((i : ℚ) - (j : ℚ)) := by
    intro i
    have hfin : ((List.range d).filter (· != i)).toFinset = (Finset.range d).erase i := by
      ext j
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq,
        Finset.mem_erase, Finset.mem_range, and_comm]
    rw [← hfin]
    exact (List.prod_toFinset (fun (j : ℕ) ↦ (i : ℚ) - (j : ℚ))
      (List.Nodup.filter _ List.nodup_range)).symm
  ext k
  rw [coeff_toPoly, finsetSum_coeff]
  simp_rw [coeff_C_mul, ← toPoly_lagrangeBasisNumCoeffs, coeff_toPoly]
  by_cases hk : k < d
  · rw [sum_range_eq_list_sum]
    have hget : (lagrangeCoeffs vals).getD k 0 =
        ((List.range d).map fun i ↦
          (vals.getD i 0 /
            (((List.range d).filter (· != i)).map fun (j : ℕ) ↦ (i : ℚ) - (j : ℚ)).prod) *
          (lagrangeBasisNumCoeffs d i).getD k 0).sum := by
      simp [lagrangeCoeffs, d, List.getD_eq_getElem?_getD, hk]
    rw [hget]
    exact congrArg List.sum (List.map_congr_left fun i _ ↦ by rw [hprod_denom i])
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa [lagrangeCoeffs, d] using Nat.le_of_not_lt hk),
      Option.getD_none]
    symm
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi_mem : i ∈ List.range d := List.mem_range.mpr (Finset.mem_range.mp hi)
    have hfold_len : ∀ (l : List ℕ) (p : List ℚ),
        (l.foldl (fun (p : List ℚ) (j : ℕ) ↦ mulSubConstCoeffs p (j : ℚ)) p).length =
          p.length + l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        intro p
        rw [List.foldl_cons, ih, length_mulSubConstCoeffs, List.length_cons]
        omega
    have hlt_filt : ((List.range d).filter (· != i)).length < d := by
      have hcount := (List.length_filter_lt_length_iff_exists (p := (· != i))).mpr
        ⟨i, hi_mem, by simp⟩
      simpa using hcount
    have hlen_num : (lagrangeBasisNumCoeffs d i).length ≤ d := by
      rw [lagrangeBasisNumCoeffs, hfold_len, List.length_singleton]; omega
    have hzero : (lagrangeBasisNumCoeffs d i).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (hlen_num.trans (Nat.le_of_not_lt hk)),
        Option.getD_none]
    rw [hzero, mul_zero]

private theorem eval_prod_X_sub_C (s : Finset ℕ) (x : ℚ) :
    (∏ j ∈ s, (X - C (j : ℚ))).eval x = ∏ j ∈ s, (x - (j : ℚ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, eval_mul, eval_sub, eval_X, eval_C, ih]

private theorem eval_toPoly_lagrangeCoeffs (vals : List ℚ) {t : ℕ} (ht : t < vals.length) :
    (toPoly (lagrangeCoeffs vals)).eval (t : ℚ) = vals.getD t 0 := by
  have hev_sum : ∀ (s : Finset ℕ) (g : ℕ → ℚ[X]),
      (∑ i ∈ s, g i).eval (t : ℚ) = ∑ i ∈ s, (g i).eval (t : ℚ) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eval_add, ih]
  rw [toPoly_lagrangeCoeffs, hev_sum, Finset.sum_eq_single t]
  · simp only [eval_mul, eval_C, eval_prod_X_sub_C]
    have hnez : (∏ j ∈ (Finset.range vals.length).erase t, ((t : ℚ) - (j : ℚ))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
      exact sub_ne_zero.mpr (Nat.cast_injective.ne (Finset.mem_erase.mp hj).1.symm)
    exact div_mul_cancel₀ _ hnez
  · intro i _ hit
    simp only [eval_mul, eval_C, eval_prod_X_sub_C]
    have hmem : t ∈ (Finset.range vals.length).erase i :=
      Finset.mem_erase.mpr ⟨hit.symm, Finset.mem_range.mpr ht⟩
    have hp0 : (∏ j ∈ (Finset.range vals.length).erase i, ((t : ℚ) - (j : ℚ))) = 0 :=
      Finset.prod_eq_zero hmem (sub_self (t : ℚ))
    rw [hp0, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_range.mpr ht) hnot

/-- **Univariate Lagrange coefficient recovery**: for any rational polynomial `P : ℚ[X]` of
degree `< d`, `lagrangeCoeffs` applied to `[P.eval 0, …, P.eval (d - 1)]` recovers `P.coeff k`
for every `k : ℕ`. -/
theorem lagrangeCoeffs_getD_of_degree_lt {P : ℚ[X]} {d : ℕ} (hdeg : P.degree < d) (k : ℕ) :
    (lagrangeCoeffs ((List.range d).map fun i : ℕ ↦ P.eval (i : ℚ))).getD k 0 = P.coeff k := by
  let vals := (List.range d).map fun i : ℕ ↦ P.eval (i : ℚ)
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · have hp0 : P = 0 := by
      by_contra hp
      rw [degree_eq_natDegree hp, Nat.cast_zero] at hdeg
      exact Nat.not_lt_zero _ (Nat.cast_lt.mp hdeg)
    subst hp0
    simp [lagrangeCoeffs]
  · rw [← coeff_toPoly]
    have hlen : (lagrangeCoeffs vals).length = d := by simp [vals]
    have hnd_Q : (toPoly (lagrangeCoeffs vals)).natDegree < d := by
      have hle : (toPoly (lagrangeCoeffs vals)).natDegree ≤ d - 1 := by
        refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
        rw [coeff_toPoly, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), Option.getD_none]
      omega
    have hnd_P : P.natDegree < d := by
      by_cases hp : P = 0
      · subst hp; simpa using hd_pos
      · rw [degree_eq_natDegree hp] at hdeg
        exact Nat.cast_lt.mp hdeg
    have heq : toPoly (lagrangeCoeffs vals) = P := by
      refine eq_of_natDegree_lt_card_of_eval_eq _ _
        (f := fun i : Fin d ↦ (i.val : ℚ))
        (fun i j h ↦ Fin.ext (Nat.cast_injective h))
        (fun i ↦ ?_)
        (by rw [Fintype.card_fin]; exact max_lt hnd_Q hnd_P)
      have hvals_len : vals.length = d := by simp [vals]
      rw [eval_toPoly_lagrangeCoeffs vals (i.isLt.trans_eq hvals_len.symm)]
      simp [vals, List.getD_eq_getElem?_getD, i.isLt]
    rw [heq]

/-- `lagrangeCoeffs` is computable in polynomial time on framed rational lists. -/
@[fun_prop]
theorem computableInPolyTime_lagrangeCoeffs :
    ComputableInPolyTime lagrangeCoeffs (encList encRat) (encList encRat) := by
  have hd : ComputableInPolyTime (fun vals : List ℚ ↦ vals.length)
      (encList encRat) encUnary := length_list encRat
  refine mapWithInput (range.comp hd) ?_
  -- Input is `(vals, k) : List ℚ × ℕ`
  have hvals : ComputableInPolyTime (fun p : List ℚ × ℕ ↦ p.1)
      (encPair (encList encRat) encUnary) (encList encRat) := fst _ _
  have hk : ComputableInPolyTime (fun p : List ℚ × ℕ ↦ p.2)
      (encPair (encList encRat) encUnary) encUnary := snd _ _
  have hd' : ComputableInPolyTime (fun p : List ℚ × ℕ ↦ p.1.length)
      (encPair (encList encRat) encUnary) encUnary := hd.comp hvals
  refine rat_list_sum' (mapWithInput (range.comp hd') ?_)
  -- Input is `((vals, k), i) : (List ℚ × ℕ) × ℕ`
  have hvals2 : ComputableInPolyTime (fun q : (List ℚ × ℕ) × ℕ ↦ q.1.1)
      (encPair (encPair (encList encRat) encUnary) encUnary) (encList encRat) :=
    hvals.comp (fst _ _)
  have hk2 : ComputableInPolyTime (fun q : (List ℚ × ℕ) × ℕ ↦ q.1.2)
      (encPair (encPair (encList encRat) encUnary) encUnary) encUnary :=
    hk.comp (fst _ _)
  have hi2 : ComputableInPolyTime (fun q : (List ℚ × ℕ) × ℕ ↦ q.2)
      (encPair (encPair (encList encRat) encUnary) encUnary) encUnary :=
    snd _ _
  have hd2 : ComputableInPolyTime (fun q : (List ℚ × ℕ) × ℕ ↦ q.1.1.length)
      (encPair (encPair (encList encRat) encUnary) encUnary) encUnary :=
    hd.comp hvals2
  have hval_i : ComputableInPolyTime (fun q : (List ℚ × ℕ) × ℕ ↦ q.1.1.getD q.2 0)
      (encPair (encPair (encList encRat) encUnary) encUnary) encRat :=
    listGetDWithInput hvals2 hi2 0
  have hfilt : ComputableInPolyTime
      (fun q : (List ℚ × ℕ) × ℕ ↦ (List.range q.1.1.length).filter (· != q.2))
      (encPair (encPair (encList encRat) encUnary) encUnary) (encList encUnary) :=
    filterWithInput (range.comp hd2) (bne (snd _ _) (hi2.comp (fst _ _)))
  let encQ := encPair (encPair (encList encRat) encUnary) encUnary
  have hdiffs : ComputableInPolyTime
      (fun q : (List ℚ × ℕ) × ℕ ↦
        (((List.range q.1.1.length).filter (· != q.2)).map fun (j : ℕ) ↦ (q.2 : ℚ) - (j : ℚ)).prod)
      encQ encRat :=
    rat_list_prod' <|
      mapWithInput (f := fun (q : (List ℚ × ℕ) × ℕ) (j : ℕ) ↦ (q.2 : ℚ) - (j : ℚ)) hfilt <|
        rat_sub' (rat_natCast.comp (unary_to_binary.comp (hi2.comp (fst encQ encUnary))))
          (rat_natCast.comp (unary_to_binary.comp (snd encQ encUnary)))
  have hbasis_ik : ComputableInPolyTime
      (fun q : (List ℚ × ℕ) × ℕ ↦ (lagrangeBasisNumCoeffs q.1.1.length q.2).getD q.1.2 0)
      (encPair (encPair (encList encRat) encUnary) encUnary) encRat :=
    listGetDWithInput (computableInPolyTime_lagrangeBasisNumCoeffs.comp (hd2.prod hi2)) hk2 0
  exact rat_mul' (rat_div' hval_i hdiffs) hbasis_ik

end LagrangeRecovery

/-! ### Batch Rational Function-Oracle Turing Reductions -/

section RatOracle

variable {α β γ : Type}

/-- An oracle language `A` answers the framed binary bits of a rational-valued function
`g : β → ℚ` under encoding `encB`. -/
def AnswersRatBits (encB : β ↪ List Bool) (g : β → ℚ) (A : Set (List Bool)) : Prop :=
  ∀ b i, encPair encB encNat (b, i) ∈ A ↔ (frame (encRat (g b))).getD i false = true

/-- Canonical bit-graph oracle language of a rational-valued function `g : β → ℚ`. -/
def ratBitGraph (encB : β ↪ List Bool) (g : β → ℚ) : Set (List Bool) :=
  encPair encB encNat '' { x : β × ℕ | (frame (encRat (g x.1))).getD x.2 false = true }

/-- `ratBitGraph encB g` satisfies `AnswersRatBits encB g`. -/
theorem answersRatBits_ratBitGraph (encB : β ↪ List Bool) (g : β → ℚ) :
    AnswersRatBits encB g (ratBitGraph encB g) :=
  fun _ _ ↦ (encPair encB encNat).injective.mem_set_image

private theorem computableInPolyTime_frameRat :
    ComputableInPolyTime (fun q : ℚ ↦ frame (encRat q)) encRat encBits :=
  (of_eq (encIn := encPair encRat encBits) (encOut := encBits)
    (f := fun p : ℚ × List Bool ↦ frame (encRat p.1) ++ p.2) fun _ ↦ rfl).comp
    (id'.prod (const [])) |>.of_enc_eq fun q ↦ by simp

private theorem computableInPolyTime_unframe :
    ComputableInPolyTime unframe encBits encBits :=
  (fst encBits encBits).comp (Decoder.bits.pair Decoder.bits).computableInPolyTime

/-- If `g : β → ℚ` is computable in polynomial time and `encB` admits a total polynomial-time
decoder, then `ratBitGraph encB g` lies in `P`. -/
theorem ratBitGraph_mem_P {encB : β ↪ List Bool} {g : β → ℚ} (D : Decoder encB)
    (hg : ComputableInPolyTime g encB encRat) : ratBitGraph encB g ∈ P encBits := by
  classical
  let D' := D.pair Decoder.nat
  have hdec : ComputableInPolyTime D'.decode encBits (encPair encB encNat) :=
    D'.computableInPolyTime
  have hword : ComputableInPolyTime (fun w ↦ frame (encRat (g (D'.decode w).1))) encBits encBits :=
    computableInPolyTime_frameRat.comp (hg.comp ((fst _ _).comp hdec))
  have hlen : ComputableInPolyTime
      (fun w ↦ (frame (encRat (g (D'.decode w).1))).length) encBits encUnary :=
    length_bits_comp hword
  have hidx : ComputableInPolyTime
      (fun w ↦ min (frame (encRat (g (D'.decode w).1))).length (D'.decode w).2)
      encBits encUnary :=
    binary_min_unary' hlen ((snd _ _).comp hdec)
  have hbit : ComputableInPolyTime
      (fun w ↦ (frame (encRat (g (D'.decode w).1))).getD
        (min (frame (encRat (g (D'.decode w).1))).length (D'.decode w).2) false)
      encBits encBool :=
    bitsGetDWithInput hword hidx false
  have hcheck : ComputableInPolyTime
      (fun w ↦ decide (encPair encB encNat (D'.decode w) = w)) encBits encBool := by
    have henc : ComputableInPolyTime (fun w ↦ encPair encB encNat (D'.decode w))
        encBits encBits :=
      (of_eq (encIn := encPair encB encNat) (encOut := encBits) fun _ ↦ rfl).comp hdec
    exact henc.decide_eq' id'
  refine ⟨fun w ↦ decide (encPair encB encNat (D'.decode w) = w) &&
      (frame (encRat (g (D'.decode w).1))).getD
        (min (frame (encRat (g (D'.decode w).1))).length (D'.decode w).2) false,
    bool_and' hcheck hbit, fun w ↦ ?_⟩
  have hget_min : ∀ (u : List Bool) (i : ℕ), u.getD (min u.length i) false = u.getD i false := by
    intro u i
    rcases le_total i u.length with h | h
    · rw [min_eq_right h]
    · rw [min_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_eq_none le_rfl,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp only [hget_min, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [D'.decode_enc]
    exact ⟨rfl, hx⟩
  · rintro ⟨hw, hbit'⟩
    exact ⟨D'.decode w, hbit', hw⟩

private def ratBitWords (encB : β ↪ List Bool) (b : β) (K : ℕ) : List (List Bool) :=
  (List.range K).map fun i ↦ encPair encB encNat (b, i)

private def batchRatBitWords (encB : β ↪ List Bool) (qs : List β) (K : ℕ) : List (List Bool) :=
  qs.flatMap fun b ↦ ratBitWords encB b K

private def decodeRatBatch (count K : ℕ) (bits : List Bool) : List ℚ :=
  (List.range count).map fun j ↦ decodeRat (unframe ((bits.drop (j * K)).take K))

private theorem drop_take_flatMap_eq {δ ε : Type*} (l : List δ) (f : δ → List ε) (K : ℕ)
    (hlen : ∀ x ∈ l, (f x).length = K) {j : ℕ} (hj : j < l.length) :
    ((l.flatMap f).drop (j * K)).take K = f l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simpa using List.take_left' (hlen a (List.mem_cons_self ..))
    | succ j =>
      rw [List.flatMap_cons, show (j + 1) * K = K + j * K by ring, ← List.drop_drop,
        List.drop_left' (hlen a (List.mem_cons_self ..)), List.getElem_cons_succ]
      exact ih (fun x hx ↦ hlen x (List.mem_cons_of_mem _ hx)) (Nat.lt_of_succ_lt_succ hj)

private theorem map_range_getD_eq_append (u : List Bool) {K : ℕ} (hu : u.length ≤ K) :
    ((List.range K).map fun i ↦ u.getD i false) = u ++ List.replicate (K - u.length) false := by
  refine List.ext_getElem (by simp; omega) fun i hi1 hi2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hiu : i < u.length
  · rw [List.getD_eq_getElem _ _ hiu, List.getElem_append_left hiu]
  · have hle : u.length ≤ i := Nat.le_of_not_lt hiu
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none,
      List.getElem_append_right hle, List.getElem_replicate]

/-- **Batch rational oracle reduction**: any polynomial-time query batch `queries` with a
polynomial-time unary bit-length bound `bound` and polynomial-time combiner `combine` yields a
`PolyTimeOracleProgram` against every oracle satisfying `AnswersRatBits encB g`. -/
theorem polyTimeOracleProgram_of_batchRat
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → γ} {g : β → ℚ}
    (queries : α → List β) (bound : α → ℕ) (combine : α × List ℚ → γ)
    (hqueries : ComputableInPolyTime queries encA (encList encB))
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hcombine : ComputableInPolyTime combine (encPair encA (encList encRat)) encC)
    (hsize : ∀ a, ∀ b ∈ queries a, (frame (encRat (g b))).length ≤ bound a)
    (hspec : ∀ a, combine (a, (queries a).map g) = f a) :
    PolyTimeOracleProgram encA encC (AnswersRatBits encB g) (· = f) := by
  classical
  have hratWords : ComputableInPolyTime (fun p : ℕ × β ↦ ratBitWords encB p.2 p.1)
      (encPair encUnary encB) (encList encBits) :=
    mapWithInput (by fun_prop) <|
      encoding_comp <|
        ((snd encUnary encB).comp (fst _ _)).prod (unary_to_binary.comp (snd _ _))
  have hbatchWords : ComputableInPolyTime (fun p : List β × ℕ ↦ batchRatBitWords encB p.1 p.2)
      (encPair (encList encB) encUnary) (encList encBits) :=
    flatMapWith hratWords (snd (encList encB) encUnary) (fst (encList encB) encUnary)
  have hdecodeBatch : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List Bool ↦ decodeRatBatch p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBits) (encList encRat) := by
    have hk : ComputableInPolyTime
        (fun q : ((ℕ × ℕ) × List Bool) × ℕ ↦ q.1.1.2)
        (encPair (encPair (encPair encUnary encUnary) encBits) encUnary) encUnary :=
      (snd _ _).comp ((fst _ _).comp (fst _ _))
    exact mapWithInput (by fun_prop) <|
      computableInPolyTime_decodeRat.comp <|
        computableInPolyTime_unframe.comp <|
          bitsTakeWithInput
            (bitsDropWithInput ((snd _ _).comp (fst _ _))
              (unary_mul.comp ((snd _ _).prod hk))) hk
  refine ⟨fun a ↦
    (fun bits ↦ combine (a, decodeRatBatch (queries a).length (bound a) bits)) <$>
      queryWords (batchRatBitWords encB (queries a) (bound a)),
    ?_, fun A hA ↦ funext fun a ↦ ?_⟩
  · simp only [OracleComp.interpret_map]
    have hlen := (length encB).comp hqueries
    have hpost : ComputableInPolyTime
        (fun pair : α × List Bool ↦
          combine (pair.1, decodeRatBatch (queries pair.1).length (bound pair.1) pair.2))
        (encPair encA encBits) encC :=
      (hcombine.comp <| (fst encA encBits).prod <|
        hdecodeBatch.comp <|
          (((hlen.comp (fst encA encBits)).prod (hbound.comp (fst encA encBits)))).prod
            (snd encA encBits)).of_enc_eq fun _ ↦ rfl
    exact (isOraclePPTOn_queryWords.preprocess
      (hbatchWords.comp (hqueries.prod hbound))).map_with hpost
  · rw [OracleComp.interpret_map, interpret_queryWords]
    have hword_map : ∀ b : β,
        (ratBitWords encB b (bound a)).map (fun w ↦ decide (w ∈ A)) =
          (List.range (bound a)).map fun i ↦ (frame (encRat (g b))).getD i false := by
      intro b
      rw [ratBitWords, List.map_map]
      exact List.map_congr_left fun i _ ↦ by
        simp only [Function.comp_apply, hA b i]
        cases (frame (encRat (g b))).getD i false <;> rfl
    have hbatch_map :
        (batchRatBitWords encB (queries a) (bound a)).map (fun w ↦ decide (w ∈ A)) =
          (queries a).flatMap fun b ↦
            (List.range (bound a)).map fun i ↦ (frame (encRat (g b))).getD i false := by
      rw [batchRatBitWords, List.map_flatMap]
      exact congrArg List.flatten (List.map_congr_left fun b _ ↦ hword_map b)
    have hdec_eq : decodeRatBatch (queries a).length (bound a)
        ((queries a).flatMap fun b ↦
          (List.range (bound a)).map fun i ↦ (frame (encRat (g b))).getD i false) =
        (queries a).map g := by
      refine List.ext_getElem (by simp [decodeRatBatch]) fun j hj1 hj2 ↦ ?_
      have hj : j < (queries a).length := by simpa [decodeRatBatch] using hj1
      simp only [decodeRatBatch, List.getElem_map, List.getElem_range]
      rw [drop_take_flatMap_eq (queries a)
        (fun b ↦ (List.range (bound a)).map fun i ↦ (frame (encRat (g b))).getD i false)
        (bound a) (fun _ _ ↦ by simp) hj]
      rw [map_range_getD_eq_append _ (hsize a _ (List.getElem_mem hj)),
        unframe_frame_append, decodeRat_encRat]
    change combine (a, decodeRatBatch (queries a).length (bound a) _) = f a
    rw [hbatch_map, hdec_eq, hspec a]

/-- Batch rational oracle reduction specialized to the canonical oracle `ratBitGraph encB g`. -/
theorem computableInPolyTimeWithOracle_of_batchRat
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → γ} {g : β → ℚ}
    (queries : α → List β) (bound : α → ℕ) (combine : α × List ℚ → γ)
    (hqueries : ComputableInPolyTime queries encA (encList encB))
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hcombine : ComputableInPolyTime combine (encPair encA (encList encRat)) encC)
    (hsize : ∀ a, ∀ b ∈ queries a, (frame (encRat (g b))).length ≤ bound a)
    (hspec : ∀ a, combine (a, (queries a).map g) = f a) :
    ComputableInPolyTimeWithOracle (ratBitGraph encB g) f encA encC := by
  obtain ⟨_, hf, rfl⟩ :=
    (polyTimeOracleProgram_of_batchRat queries bound combine hqueries hbound hcombine
      hsize hspec).exists_computableInPolyTimeWithOracle (answersRatBits_ratBitGraph encB g)
  exact hf

/-- When the rational oracle `g : β → ℚ` is itself computable in polynomial time and `encB` admits
a total polynomial-time decoder, any batch rational oracle reduction collapses to plain
`ComputableInPolyTime`. -/
theorem computableInPolyTime_of_batchRat
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    (D : Decoder encB) {f : α → γ} {g : β → ℚ}
    (hg : ComputableInPolyTime g encB encRat)
    (queries : α → List β) (bound : α → ℕ) (combine : α × List ℚ → γ)
    (hqueries : ComputableInPolyTime queries encA (encList encB))
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hcombine : ComputableInPolyTime combine (encPair encA (encList encRat)) encC)
    (hsize : ∀ a, ∀ b ∈ queries a, (frame (encRat (g b))).length ≤ bound a)
    (hspec : ∀ a, combine (a, (queries a).map g) = f a) :
    ComputableInPolyTime f encA encC :=
  (computableInPolyTimeWithOracle_of_batchRat queries bound combine hqueries hbound hcombine
    hsize hspec).computableInPolyTime (ratBitGraph_mem_P D hg)

end RatOracle

end CslibFrontier.PolyTime.RatList
