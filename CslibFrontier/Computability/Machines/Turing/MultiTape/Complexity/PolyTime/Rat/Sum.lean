/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational decoders, unary rational encodings, and polynomial-time rational list aggregation

Total polynomial-time decoders for `encIntBin` and `encRat`, a Garey–Johnson unary numerical
encoding `encRatUnary` of `ℚ` (for strong `NP`-completeness reductions and pseudo-polynomial-time
algorithms on rational inputs), and certified multi-tape Turing-machine polynomial-time certificates
for exact binary rational list summation `List.sum : List ℚ → ℚ` and list extrema.

## Main definitions

* `Turing.MultiTapeTM.Decoder.intBin`: total polynomial-time decoder for `encIntBin`.
* `Turing.MultiTapeTM.Decoder.rat`: total polynomial-time decoder for `encRat`.
* `Turing.MultiTapeTM.encRatUnary`: unary sign-magnitude numerator and unary denominator encoding
  of `ℚ`.

## Main results

* `Turing.MultiTapeTM.length_encRatUnary`, `Turing.MultiTapeTM.den_le_length_encRatUnary`: exact
  encoded bit length and denominator bound for `encRatUnary`.
* `Turing.MultiTapeTM.ComputableInPolyTime.ratUnary_den`,
  `Turing.MultiTapeTM.ComputableInPolyTime.ratUnary_to_rat`,
  `Turing.MultiTapeTM.ComputableInPolyTime.ratUnary_divNat`,
  `Turing.MultiTapeTM.ComputableInPolyTime.ratUnary_divNat'`: polynomial-time denominator
  projection, unary-to-binary conversion, and reduced unary quotient formation.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_sum`,
  `Turing.MultiTapeTM.ComputableInPolyTime.rat_sum'`: exact binary rational list summation
  `List.sum : List ℚ → ℚ` is computable in polynomial time (bounding intermediate unreduced
  numerator and denominator bit-lengths quadratically in input bit-length).
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_listMaxD`,
  `Turing.MultiTapeTM.ComputableInPolyTime.rat_listMinD`: polynomial-time maximum and minimum of a
  rational list with a fallback value.
-/

public section

namespace Turing.MultiTapeTM

open Cslib Turing.MultiTapeTM.ComputableInPolyTime

/-- Total polynomial-time decoder for sign-magnitude binary integers `encIntBin`. -/
def Decoder.intBin : Decoder encIntBin where
  decode w := if w.headD false then -(ofBits w.tail : ℤ) else (ofBits w.tail : ℤ)
  decode_enc z := by
    have hbits : ofBits z.natAbs.bits = z.natAbs := Nat.foldr_bit_bits z.natAbs
    simp only [encIntBin_apply, List.headD_cons, List.tail_cons, hbits]
    by_cases h : z < 0
    · simp only [decide_eq_true h, ↓reduceIte]; omega
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]; omega
  computable :=
    (intBin_signMagnitude' (headD (encA := encBool) (encL := encBits) false)
      (bitsToNat.comp bitsTail)).exists_degree

/-- Total polynomial-time decoder for binary-encoded rationals `encRat`. -/
def Decoder.rat : Decoder encRat where
  decode w :=
    let p := (Decoder.intBin.pair Decoder.nat).decode w
    Rat.divInt p.1 (p.2 : ℤ)
  decode_enc q := by
    have hp : (Decoder.intBin.pair Decoder.nat).decode (encRat q) = (q.num, q.den) :=
      (Decoder.intBin.pair Decoder.nat).decode_enc (q.num, q.den)
    dsimp only
    rw [hp, Rat.divInt_eq_div, Int.cast_natCast, Rat.num_div_den]
  computable := by
    have hp := (Decoder.intBin.pair Decoder.nat).computableInPolyTime
    exact (rat_divInt' hp.fst' (intBin_natCast.comp hp.snd')).exists_degree

/-- Raw unary representation `((q < 0, |q.num|), q.den)` of a rational number `q : ℚ`. -/
abbrev encRatUnaryData : (Bool × ℕ) × ℕ ↪ List Bool :=
  encPair (encPair encBool encUnary) encUnary

/-- Garey–Johnson unary numerical encoding of `ℚ`: framed sign bit, unary `|q.num|`, and unary
`q.den`.
-/
def encRatUnary : ℚ ↪ List Bool where
  toFun q := encRatUnaryData ((decide (q.num < 0), q.num.natAbs), q.den)
  inj' q₁ q₂ h := by
    have hp := encRatUnaryData.injective h
    have h1 := congrArg Prod.fst hp
    have hden : q₁.den = q₂.den := congrArg Prod.snd hp
    have hlt : q₁.num < 0 ↔ q₂.num < 0 := decide_eq_decide.mp (congrArg Prod.fst h1)
    have habs : q₁.num.natAbs = q₂.num.natAbs := congrArg Prod.snd h1
    exact Rat.ext (by omega) hden

/-- Unfolding of `encRatUnary`. -/
theorem encRatUnary_apply (q : ℚ) :
    encRatUnary q = encRatUnaryData ((decide (q.num < 0), q.num.natAbs), q.den) := by
  rfl

/-- Exact bit length of `encRatUnary q`. -/
theorem length_encRatUnary (q : ℚ) :
    (encRatUnary q).length = 2 * q.num.natAbs + q.den + 7 := by
  have hb : ∀ b : Bool, (encBool b).length = 1 := fun b => by cases b <;> rfl
  simp only [encRatUnary_apply, length_encPair, hb, encUnary_apply, List.length_replicate]
  omega

/-- Every rational's denominator is bounded above by `(encRatUnary q).length`. -/
theorem den_le_length_encRatUnary (q : ℚ) : q.den ≤ (encRatUnary q).length := by
  rw [length_encRatUnary]; omega

/-- The binary encoding length of `q : ℚ` is linearly bounded by its unary encoding length. -/
theorem length_encRat_le_encRatUnary (q : ℚ) :
    (encRat q).length ≤ 2 * (encRatUnary q).length + 4 := by
  have hsz : ∀ k : ℕ, k.size ≤ k := by
    intro k
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := k))
  have h1 := hsz q.num.natAbs
  have h2 := hsz q.den
  rw [length_encRat, length_encRatUnary]
  omega

namespace ComputableInPolyTime

/-- Extracting the unary denominator `q.den` from `encRatUnary q` runs in polynomial time. -/
@[fun_prop]
theorem ratUnary_den : ComputableInPolyTime Rat.den encRatUnary encUnary :=
  (ComputableInPolyTime.of_eq
    (f := fun q : ℚ => ((decide (q.num < 0), q.num.natAbs), q.den))
    (encIn := encRatUnary) (encOut := encRatUnaryData) fun _ => rfl).snd'

/-- Converting `encRatUnary` to binary `encRat` runs in polynomial time. -/
@[fun_prop]
theorem ratUnary_to_rat : ComputableInPolyTime (fun q : ℚ => q) encRatUnary encRat := by
  have hraw : ComputableInPolyTime
      (fun q : ℚ => ((decide (q.num < 0), q.num.natAbs), q.den)) encRatUnary encRatUnaryData :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hnum := intBin_signMagnitude' hraw.fst'.fst' (unary_to_binary.comp hraw.fst'.snd')
  have hden := unary_to_binary.comp hraw.snd'
  refine (hnum.prod hden).of_enc_eq fun q => ?_
  rw [encRat_apply]
  refine congrArg encRatData (Prod.ext ?_ rfl)
  by_cases h : q.num < 0
  · simp only [Function.comp_apply, decide_eq_true h, ↓reduceIte]; omega
  · simp only [Function.comp_apply, decide_eq_false h, Bool.false_eq_true, ↓reduceIte]; omega

/-- Forming the reduced nonnegative rational quotient `(a : ℚ) / (b : ℚ)` from two unary natural
numbers `(a, b)` is computable in polynomial time with output in `encRatUnary`. -/
theorem ratUnary_divNat :
    ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))
      (encPair encUnary encUnary) encRatUnary := by
  have ha_u := fst encUnary encUnary
  have hb_u := snd encUnary encUnary
  have ha_b := unary_to_binary.comp ha_u
  have hb_b := unary_to_binary.comp hb_u
  have hg := binary_gcd' ha_b hb_b
  have hnum_u :=
    ite (unary_beq hb_u (const 0)) (const 0) (binary_min_unary' ha_u (binary_div' ha_b hg))
  have hden_u :=
    ite (unary_beq hb_u (const 0)) (const 1) (binary_min_unary' hb_u (binary_div' hb_b hg))
  have hraw : ComputableInPolyTime
      (fun p : ℕ × ℕ => ((false, if p.2 == 0 then 0 else min p.1 (p.1 / p.1.gcd p.2)),
        if p.2 == 0 then 1 else min p.2 (p.2 / p.1.gcd p.2)))
      (encPair encUnary encUnary) encRatUnaryData :=
    (((const (encOut := encBool) false).prod hnum_u).prod hden_u).of_enc_eq fun _ => rfl
  refine hraw.of_enc_eq (encD := encRatUnary) (g := fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))
    fun ⟨a, b⟩ => ?_
  rw [encRatUnary_apply]
  have hnn : ¬ (((a : ℚ) / (b : ℚ)).num < 0) :=
    not_lt.mpr (Rat.num_nonneg.mpr (by positivity))
  have hdiv : ((a : ℚ) / (b : ℚ)) = Rat.divInt (a : ℤ) (b : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
  by_cases hb0 : b = 0
  · subst hb0; simp
  · refine congrArg encRatUnaryData (Prod.ext (Prod.ext (decide_eq_false hnn) ?_) ?_)
    · have hb0' : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
      simp only [beq_iff_eq, hb0, ↓reduceIte, hdiv, Rat.natAbs_num_divInt, Int.natAbs_natCast,
        hb0', Nat.min_eq_right (Nat.div_le_self _ _)]
    · have hb0' : (b : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
      simp only [beq_iff_eq, hb0, ↓reduceIte, hdiv, Rat.den_divInt, Int.natAbs_natCast, hb0',
        Int.gcd, Nat.gcd_comm a b, Nat.min_eq_right (Nat.div_le_self _ _)]

/-- Compositional form of `ratUnary_divNat`. -/
theorem ratUnary_divNat' {α : Type} {enc : α ↪ List Bool} {a b : α → ℕ}
    (ha : ComputableInPolyTime a enc encUnary) (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => (a x : ℚ) / (b x : ℚ)) enc encRatUnary := by
  exact (ComputableInPolyTime.comp
    (f := fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)) (g := fun x => (a x, b x))
    ratUnary_divNat (ha.prod hb)).of_enc_eq fun _ => rfl

private lemma rat_foldl_add_bounds {M : ℕ} (hM : 1 ≤ M) :
    ∀ (ys : List ℚ) (acc : ℚ) (k : ℕ),
      acc.num.natAbs ≤ k * M ^ k → acc.den ≤ M ^ k →
      (∀ q ∈ ys, q.num.natAbs ≤ M ∧ q.den ≤ M) →
      let s := ys.foldl (· + ·) acc
      s.num.natAbs ≤ (k + ys.length) * M ^ (k + ys.length) ∧
        s.den ≤ M ^ (k + ys.length)
  | [], _, _, hn, hd, _ => by simpa using ⟨hn, hd⟩
  | q :: ys, acc, k, hn, hd, hys => by
    have ⟨hqn, hqd⟩ := hys q List.mem_cons_self
    have hacc_n : (acc + q).num.natAbs ≤ (k + 1) * M ^ (k + 1) := by
      calc (acc + q).num.natAbs
          ≤ acc.num.natAbs * q.den + q.num.natAbs * acc.den := Rat.natAbs_num_add_le acc q
        _ ≤ (k * M ^ k) * M + M * M ^ k :=
          Nat.add_le_add (Nat.mul_le_mul hn hqd) (Nat.mul_le_mul hqn hd)
        _ = (k + 1) * M ^ (k + 1) := by rw [pow_succ]; ring
    have hacc_d : (acc + q).den ≤ M ^ (k + 1) := by
      calc (acc + q).den ≤ acc.den * q.den := Rat.den_add_le acc q
        _ ≤ M ^ k * M := Nat.mul_le_mul hd hqd
        _ = M ^ (k + 1) := (pow_succ M k).symm
    have ih := rat_foldl_add_bounds hM ys (acc + q) (k + 1) hacc_n hacc_d
      (fun r hr => hys r (List.mem_cons_of_mem _ hr))
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm 1 ys.length] using ih

/-- Exact summation `List.sum : List ℚ → ℚ` of binary-encoded rationals is computable in
polynomial time on a multi-tape Turing machine. -/
@[fun_prop]
theorem rat_sum : ComputableInPolyTime (fun xs : List ℚ => xs.sum) (encList encRat) encRat := by
  have hfold : ComputableInPolyTime
      (fun xs : List ℚ => xs.foldl (· + ·) (0 : ℚ)) (encList encRat) encRat := by
    refine foldl' (encA := encRat) (encL := encList encRat) (encB := encRat)
      (list := id) (init := fun _ => (0 : ℚ)) (step := (· + ·)) id' (const 0) rat_add
      (B := fun xs =>
        let L := (encList encRat xs).length
        3 * L * L + 2 * L + 9)
      ((((((PolyBounded.const 3).mul .self).mul .self).add
        ((PolyBounded.const 2).mul .self)).add (.const 9)))
      fun xs i _ => ?_
    dsimp only
    set L := (encList encRat xs).length
    have helem : ∀ q ∈ xs.take i, q.num.natAbs ≤ 2 ^ L ∧ q.den ≤ 2 ^ L := fun q hq => by
      have hqL : (encRat q).length ≤ L :=
        SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat)
          xs q (List.mem_of_mem_take hq)
      have hpow : 2 ^ (encRat q).length ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hqL
      exact ⟨(natAbs_num_lt_two_pow_length_encRat q).le.trans hpow,
        (den_lt_two_pow_length_encRat q).le.trans hpow⟩
    have ⟨hsn, hsd⟩ := rat_foldl_add_bounds (M := 2 ^ L) Nat.one_le_two_pow
      (xs.take i) 0 0 (by simp) (by simp) helem
    simp only [zero_add] at hsn hsd
    have hlen_le : (xs.take i).length ≤ L :=
      (List.length_take_le' i xs).trans
        (SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) xs)
    have hnum_pow : ((xs.take i).foldl (· + ·) 0).num.natAbs < 2 ^ ((L + 1) * L) := by
      by_cases h0 : (xs.take i).length = 0
      · rw [List.eq_nil_of_length_eq_zero h0]; simp
      · have hk_lt : (xs.take i).length < 2 ^ L :=
          (Nat.lt_two_pow_self (n := (xs.take i).length)).trans_le
            (Nat.pow_le_pow_right (by decide) hlen_le)
        calc ((xs.take i).foldl (· + ·) 0).num.natAbs
            ≤ (xs.take i).length * (2 ^ L) ^ (xs.take i).length := hsn
          _ < 2 ^ L * (2 ^ L) ^ (xs.take i).length :=
            Nat.mul_lt_mul_of_pos_right hk_lt (by positivity)
          _ ≤ 2 ^ L * (2 ^ L) ^ L :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.one_le_two_pow hlen_le)
          _ = 2 ^ ((L + 1) * L) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    have hden_pow : ((xs.take i).foldl (· + ·) 0).den ≤ 2 ^ (L * L) :=
      hsd.trans ((Nat.pow_le_pow_right Nat.one_le_two_pow hlen_le).trans_eq (pow_mul 2 L L).symm)
    have hnum_sz := Nat.size_le.mpr hnum_pow
    have hden_sz :=
      Nat.size_le.mpr (hden_pow.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))
    dsimp only [id]
    rw [length_encRat]
    linarith
  exact hfold.of_enc_eq fun _ => congrArg encRat List.sum_eq_foldl

/-- Compositional rule for `rat_sum`. -/
@[fun_prop]
theorem rat_sum' {α : Type} {enc : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f enc (encList encRat)) :
    ComputableInPolyTime (fun x => (f x).sum) enc encRat :=
  rat_sum.comp hf

/-- Computing `xs.foldl max d` on a binary-encoded rational list runs in polynomial time. -/
theorem rat_listMaxD :
    ComputableInPolyTime (fun p : ℚ × List ℚ => p.2.foldl max p.1)
      (encPair encRat (encList encRat)) encRat := by
  have hstep : ComputableInPolyTime (fun p : ℚ × ℚ => max p.1 p.2)
      (encPair encRat encRat) encRat :=
    (ite (rat_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _)).of_enc_eq fun p => by
      simp only [decide_eq_true_eq]
      split_ifs with h
      · rw [max_eq_right h]
      · rw [max_eq_left (not_le.mp h).le]
  refine foldl' (snd encRat (encList encRat)) (fst encRat (encList encRat)) hstep
    (B := fun p => (encPair encRat (encList encRat) p).length) .self fun p i _ => ?_
  have haux : ∀ (l : List ℚ) (acc : ℚ), acc = p.1 ∨ acc ∈ p.2 →
      (∀ q ∈ l, q ∈ p.2) → l.foldl max acc = p.1 ∨ l.foldl max acc ∈ p.2 := by
    intro l; induction l with
    | nil => intro acc ha _; exact ha
    | cons x xs ih =>
      intro acc ha hl
      refine ih (max acc x) ?_ (fun u hu => hl u (List.mem_cons_of_mem _ hu))
      rcases max_choice acc x with h1 | h2
      · rwa [h1]
      · rw [h2]; exact Or.inr (hl x List.mem_cons_self)
  rcases haux (p.2.take i) p.1 (Or.inl rfl) (fun q hq => List.mem_of_mem_take hq) with heq | hmem
  · rw [heq]; simp [encPair_apply, length_frame]; omega
  · exact (SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat)
      p.2 _ hmem).trans (by simp only [encPair_apply, List.length_append]; omega)

/-- Computing `xs.foldl min d` on a binary-encoded rational list runs in polynomial time. -/
theorem rat_listMinD :
    ComputableInPolyTime (fun p : ℚ × List ℚ => p.2.foldl min p.1)
      (encPair encRat (encList encRat)) encRat := by
  have hstep : ComputableInPolyTime (fun p : ℚ × ℚ => min p.1 p.2)
      (encPair encRat encRat) encRat :=
    (ite (rat_le' (fst _ _) (snd _ _)) (fst _ _) (snd _ _)).of_enc_eq fun p => by
      simp only [decide_eq_true_eq]
      split_ifs with h
      · rw [min_eq_left h]
      · rw [min_eq_right (not_le.mp h).le]
  refine foldl' (snd encRat (encList encRat)) (fst encRat (encList encRat)) hstep
    (B := fun p => (encPair encRat (encList encRat) p).length) .self fun p i _ => ?_
  have haux : ∀ (l : List ℚ) (acc : ℚ), acc = p.1 ∨ acc ∈ p.2 →
      (∀ q ∈ l, q ∈ p.2) → l.foldl min acc = p.1 ∨ l.foldl min acc ∈ p.2 := by
    intro l; induction l with
    | nil => intro acc ha _; exact ha
    | cons x xs ih =>
      intro acc ha hl
      refine ih (min acc x) ?_ (fun u hu => hl u (List.mem_cons_of_mem _ hu))
      rcases min_choice acc x with h1 | h2
      · rwa [h1]
      · rw [h2]; exact Or.inr (hl x List.mem_cons_self)
  rcases haux (p.2.take i) p.1 (Or.inl rfl) (fun q hq => List.mem_of_mem_take hq) with heq | hmem
  · rw [heq]; simp [encPair_apply, length_frame]; omega
  · exact (SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat)
      p.2 _ hmem).trans (by simp only [encPair_apply, List.length_append]; omega)

end ComputableInPolyTime

end Turing.MultiTapeTM
