module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Cast.Order
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Binary Rational Arithmetic on Multi-Tape Turing Machines

Defines the canonical binary encoding `CslibFrontier.RatBinary.encRatBin` of exact rational numbers
`q : ℚ` as reduced signed-numerator / natural-denominator pairs `(q.num, q.den)`, and establishes
under standard Lean axioms that all field operations, order comparisons, floor and ceiling, finite
list sums, minima, and common-denominator clearing are computable in deterministic polynomial time
on multi-tape Turing machines (`Turing.MultiTapeTM.ComputableInPolyTime`).

## Main definitions

* `CslibFrontier.RatBinary.encRatBin`: canonical binary encoding `ℚ ↪ List Bool` via
  `encPair encIntBin encNat` on `(q.num, q.den)`.
* `CslibFrontier.RatBinary.clearDenom`: positive common denominator `(qs.map Rat.den).prod` of a
  list of rationals.
* `CslibFrontier.RatBinary.scaleToInt`: exact integer `q.num * (D / q.den : ℤ)` representing `D * q`
  whenever `q.den ∣ D`.
* `CslibFrontier.RatBinary.listMinD`: minimum of a list of rationals with a supplied fallback value.

## Main results

* `CslibFrontier.RatBinary.computableInPolyTime_mkRat`,
  `CslibFrontier.RatBinary.computableInPolyTime_divInt`: reduced fraction construction is computable
  in polynomial time.
* `CslibFrontier.RatBinary.computableInPolyTime_add`, `computableInPolyTime_sub`,
  `computableInPolyTime_mul`, `computableInPolyTime_inv`, `computableInPolyTime_div`,
  `computableInPolyTime_neg`, `computableInPolyTime_abs`: exact rational field arithmetic is
  computable in polynomial time.
* `CslibFrontier.RatBinary.computableInPolyTime_lt`, `computableInPolyTime_le`,
  `computableInPolyTime_min`, `computableInPolyTime_max`: rational order comparisons and binary
  extrema are computable in polynomial time.
* `CslibFrontier.RatBinary.computableInPolyTime_floor`, `computableInPolyTime_ceil`: integer floor
  and ceiling of binary rationals are computable in polynomial time.
* `CslibFrontier.RatBinary.computableInPolyTime_sum`, `computableInPolyTime_listMinD`,
  `computableInPolyTime_clearDenom`, `computableInPolyTime_scaleToInt`: finite list summation,
  minimum with default, and common-denominator scaling to binary integers run in polynomial time.
-/

public section

namespace CslibFrontier.RatBinary

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Pair projection sending a rational `q : ℚ` to its reduced `(q.num, q.den)` representation. -/
@[expose] def toPair (q : ℚ) : ℤ × ℕ :=
  (q.num, q.den)

/-- `toPair` is injective because every `q : ℚ` is uniquely determined by `(q.num, q.den)`. -/
theorem toPair_injective : Function.Injective toPair := by
  intro p q h
  exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Canonical binary encoding of `ℚ` as the framed pair `(q.num, q.den)` in signed/unsigned
binary. -/
@[expose] def encRatBin : ℚ ↪ List Bool where
  toFun q := encPair encIntBin encNat (q.num, q.den)
  inj' _ _ h := toPair_injective ((encPair encIntBin encNat).injective h)

@[simp]
theorem encRatBin_apply (q : ℚ) :
    encRatBin q = encPair encIntBin encNat (q.num, q.den) :=
  rfl

/-- Encoded bit length of a binary rational in terms of the encoded numerator and denominator. -/
theorem length_encRatBin (q : ℚ) :
    (encRatBin q).length = 2 * (encIntBin q.num).length + 1 + (encNat q.den).length := by
  simp only [encRatBin_apply, length_encPair]

private theorem computableInPolyTime_toPair :
    ComputableInPolyTime toPair encRatBin (encPair encIntBin encNat) :=
  of_eq fun _ => rfl

/-- Extracting the reduced signed numerator `Rat.num` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_num : ComputableInPolyTime Rat.num encRatBin encIntBin :=
  (fst encIntBin encNat).comp computableInPolyTime_toPair

/-- Extracting the reduced positive denominator `Rat.den` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_den : ComputableInPolyTime Rat.den encRatBin encNat :=
  (snd encIntBin encNat).comp computableInPolyTime_toPair

/-- Composition form of `computableInPolyTime_num`. -/
theorem computableInPolyTime_num' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun a => (f a).num) enc encIntBin :=
  computableInPolyTime_num.comp hf

/-- Composition form of `computableInPolyTime_den`. -/
theorem computableInPolyTime_den' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun a => (f a).den) enc encNat :=
  computableInPolyTime_den.comp hf

/-- Casting a signed binary integer to `ℚ` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_intCast :
    ComputableInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encRatBin := by
  have h : ComputableInPolyTime (fun z : ℤ => (z, (1 : ℕ)))
      encIntBin (encPair encIntBin encNat) :=
    (id' (encIn := encIntBin)).prod (const 1)
  exact h.of_enc_eq fun z => by
    simp only [encRatBin_apply, Rat.num_intCast, Rat.den_intCast]

/-- Composition form of `computableInPolyTime_intCast`. -/
theorem computableInPolyTime_intCast' {α : Type} {enc : α ↪ List Bool} {f : α → ℤ}
    (hf : ComputableInPolyTime f enc encIntBin) :
    ComputableInPolyTime (fun a => (f a : ℚ)) enc encRatBin :=
  computableInPolyTime_intCast.comp hf

/-- Casting an unsigned binary natural to `ℚ` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_natCast :
    ComputableInPolyTime (fun n : ℕ => (n : ℚ)) encNat encRatBin := by
  have h := computableInPolyTime_intCast.comp intBin_natCast
  exact h.of_enc_eq fun n => by simp

/-- Composition form of `computableInPolyTime_natCast`. -/
theorem computableInPolyTime_natCast' {α : Type} {enc : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f enc encNat) :
    ComputableInPolyTime (fun a => (f a : ℚ)) enc encRatBin :=
  computableInPolyTime_natCast.comp hf

/-- Casting a unary natural to `ℚ` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_natCast_unary :
    ComputableInPolyTime (fun n : ℕ => (n : ℚ)) encUnary encRatBin := by
  have h := computableInPolyTime_intCast.comp intBin_natCast_unary
  exact h.of_enc_eq fun n => by simp

private def mkRatPair (a : ℤ) (b : ℕ) : ℤ × ℕ :=
  if b = 0 then (0, 1)
  else
    let g := Nat.gcd a.natAbs b
    let mag := a.natAbs / g
    (if a < 0 then -(mag : ℤ) else (mag : ℤ), b / g)

private theorem toPair_mkRat_eq (a : ℤ) (b : ℕ) :
    toPair (mkRat a b) = mkRatPair a b := by
  unfold mkRatPair toPair
  by_cases hb : b = 0
  · subst hb; simp
  · rw [ite_eq_right hb]
    set g := Nat.gcd a.natAbs b
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right a.natAbs (Nat.pos_of_ne_zero hb)
    have hga : g ∣ a.natAbs := Nat.gcd_dvd_left a.natAbs b
    have hgb : g ∣ b := Nat.gcd_dvd_right a.natAbs b
    set d := b / g
    have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hgb) hg_pos
    have hd_ne : d ≠ 0 := Nat.ne_of_gt hd_pos
    set num' : ℤ := if a < 0 then -((a.natAbs / g : ℕ) : ℤ) else ((a.natAbs / g : ℕ) : ℤ)
    have hnum_abs : num'.natAbs = a.natAbs / g := by
      dsimp only [num']
      split_ifs
      · exact Int.natAbs_neg _ |>.trans (Int.natAbs_natCast _)
      · exact Int.natAbs_natCast _
    have hnum_mul : num' * (g : ℤ) = a := by
      dsimp only [num']
      have hdiv : (a.natAbs / g) * g = a.natAbs := Nat.div_mul_cancel hga
      have hdivZ : ((a.natAbs / g : ℕ) : ℤ) * (g : ℤ) = (a.natAbs : ℤ) := by
        exact_mod_cast hdiv
      split_ifs with hneg
      · have ha : (a.natAbs : ℤ) = -a := Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
        linarith
      · have ha : (a.natAbs : ℤ) = a := Int.ofNat_natAbs_of_nonneg (not_lt.mp hneg)
        linarith
    have hcop : num'.natAbs.Coprime d := by
      rw [hnum_abs]
      exact Nat.coprime_div_gcd_div_gcd hg_pos
    let q : ℚ := ⟨num', d, hd_ne, hcop⟩
    suffices hq : mkRat a b = q by rw [hq]
    have hnum_eq : a * (q.den : ℤ) = q.num * (b : ℤ) := by
      have hbd : (b : ℤ) = (d : ℤ) * (g : ℤ) := by
        exact_mod_cast (Nat.div_mul_cancel hgb).symm
      change a * (d : ℤ) = num' * (b : ℤ)
      rw [hbd, ← hnum_mul]
      ring
    have h1 : mkRat a b = (a : ℚ) / (b : ℚ) := Rat.mkRat_eq_div a b
    have h2 : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hdQ : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    rw [h1, h2, div_eq_div_iff hbQ hdQ]
    exact_mod_cast hnum_eq

/-- Constructing a reduced rational `mkRat a b` from `(a, b) : ℤ × ℕ` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_mkRat :
    ComputableInPolyTime (fun p : ℤ × ℕ => mkRat p.1 p.2)
      (encPair encIntBin encNat) encRatBin := by
  have ha := fst encIntBin encNat
  have hb := snd encIntBin encNat
  have hzero := decide_eq' hb (const 0)
  have hg := binary_gcd' (intBin_natAbs.comp ha) hb
  have hmag := binary_div' (intBin_natAbs.comp ha) hg
  have hnum := intBin_signMagnitude' (intBin_isNeg.comp ha) hmag
  have hden := binary_div' hb hg
  have hpair := hzero.ite' ((const (0 : ℤ)).prod (const (1 : ℕ))) (hnum.prod hden)
  refine hpair.of_enc_eq fun p => ?_
  have heq := toPair_mkRat_eq p.1 p.2
  simp only [encRatBin_apply]
  change encPair encIntBin encNat (toPair (mkRat p.1 p.2)) = _
  rw [heq]
  simp only [mkRatPair, Function.comp_apply, decide_eq_true_eq]

/-- Composition form of `computableInPolyTime_mkRat`. -/
theorem computableInPolyTime_mkRat' {α : Type} {enc : α ↪ List Bool} {a : α → ℤ} {b : α → ℕ}
    (ha : ComputableInPolyTime a enc encIntBin)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun x => mkRat (a x) (b x)) enc encRatBin :=
  (computableInPolyTime_mkRat.comp (ha.prod hb)).of_enc_eq fun _ => rfl

private theorem divInt_eq_mkRat (a b : ℤ) :
    Rat.divInt a b = if b < 0 then mkRat (-a) b.natAbs else mkRat a b.natAbs := by
  by_cases hb : b < 0
  · rw [ite_eq_left hb]
    have hbn : (b.natAbs : ℤ) = -b := Int.ofNat_natAbs_of_nonpos (le_of_lt hb)
    have hbn_ne : (b.natAbs : ℚ) ≠ 0 := by
      have : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_lt hb)
      exact Nat.cast_ne_zero.mpr this
    have hbQ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_lt hb)
    rw [Rat.divInt_eq_div, Rat.mkRat_eq_div, div_eq_div_iff hbQ hbn_ne]
    have hbnQ : ((b.natAbs : ℕ) : ℚ) = -(b : ℚ) := by
      have h1 : ((b.natAbs : ℤ) : ℚ) = ((-b : ℤ) : ℚ) := congrArg Int.cast hbn
      simpa only [Int.cast_natCast, Int.cast_neg] using h1
    push_cast
    rw [hbnQ]
    ring
  · rw [ite_eq_right hb]
    have hbn : (b.natAbs : ℤ) = b := Int.ofNat_natAbs_of_nonneg (not_lt.mp hb)
    rw [← hbn]
    exact Rat.divInt_ofNat a b.natAbs

/-- Constructing a reduced rational `Rat.divInt a b` from signed integers runs in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_divInt :
    ComputableInPolyTime (fun p : ℤ × ℤ => Rat.divInt p.1 p.2)
      (encPair encIntBin encIntBin) encRatBin := by
  have ha := fst encIntBin encIntBin
  have hb := snd encIntBin encIntBin
  have h := (intBin_isNeg.comp hb).ite'
    (computableInPolyTime_mkRat' (intBin_neg.comp ha) (intBin_natAbs.comp hb))
    (computableInPolyTime_mkRat' ha (intBin_natAbs.comp hb))
  refine h.of_enc_eq fun p => congrArg encRatBin ?_
  simpa only [Function.comp_apply, decide_eq_true_eq] using divInt_eq_mkRat p.1 p.2

/-- Composition form of `computableInPolyTime_divInt`. -/
theorem computableInPolyTime_divInt' {α : Type} {enc : α ↪ List Bool} {a b : α → ℤ}
    (ha : ComputableInPolyTime a enc encIntBin)
    (hb : ComputableInPolyTime b enc encIntBin) :
    ComputableInPolyTime (fun x => Rat.divInt (a x) (b x)) enc encRatBin :=
  (computableInPolyTime_divInt.comp (ha.prod hb)).of_enc_eq fun _ => rfl

/-- Rational negation runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_neg :
    ComputableInPolyTime (fun q : ℚ => -q) encRatBin encRatBin := by
  have h := (intBin_neg.comp computableInPolyTime_num).prod computableInPolyTime_den
  refine h.of_enc_eq fun q => ?_
  simp only [encRatBin_apply, Function.comp_apply, Rat.neg_num, Rat.neg_den]

/-- Composition form of `computableInPolyTime_neg`. -/
theorem computableInPolyTime_neg' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun x => -f x) enc encRatBin :=
  computableInPolyTime_neg.comp hf

/-- Rational addition runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_add :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 + p.2)
      (encPair encRatBin encRatBin) encRatBin := by
  have hp := fst encRatBin encRatBin
  have hq := snd encRatBin encRatBin
  have hpn := computableInPolyTime_num' hp
  have hpd := computableInPolyTime_den' hp
  have hqn := computableInPolyTime_num' hq
  have hqd := computableInPolyTime_den' hq
  have hnum := intBin_add'
    (intBin_mul' hpn (intBin_natCast.comp hqd))
    (intBin_mul' hqn (intBin_natCast.comp hpd))
  have hden := binary_mul.comp (hpd.prod hqd)
  refine (computableInPolyTime_mkRat' hnum hden).of_enc_eq fun r => congrArg encRatBin ?_
  simp only [Function.comp_apply]
  rw [Rat.add_def]
  exact Rat.normalize_eq_mkRat (Nat.mul_ne_zero r.1.den_nz r.2.den_nz)

/-- Composition form of `computableInPolyTime_add`. -/
theorem computableInPolyTime_add' {α : Type} {enc : α ↪ List Bool} {f g : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin)
    (hg : ComputableInPolyTime g enc encRatBin) :
    ComputableInPolyTime (fun x => f x + g x) enc encRatBin :=
  (computableInPolyTime_add.comp (hf.prod hg)).of_enc_eq fun _ => rfl

/-- Rational subtraction runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sub :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 - p.2)
      (encPair encRatBin encRatBin) encRatBin := by
  have h := computableInPolyTime_add' (fst encRatBin encRatBin)
    (computableInPolyTime_neg' (snd encRatBin encRatBin))
  exact h.of_enc_eq fun p => congrArg encRatBin (sub_eq_add_neg p.1 p.2)

/-- Composition form of `computableInPolyTime_sub`. -/
theorem computableInPolyTime_sub' {α : Type} {enc : α ↪ List Bool} {f g : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin)
    (hg : ComputableInPolyTime g enc encRatBin) :
    ComputableInPolyTime (fun x => f x - g x) enc encRatBin :=
  (computableInPolyTime_sub.comp (hf.prod hg)).of_enc_eq fun _ => rfl

/-- Rational multiplication runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_mul :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 * p.2)
      (encPair encRatBin encRatBin) encRatBin := by
  have hp := fst encRatBin encRatBin
  have hq := snd encRatBin encRatBin
  have hnum := intBin_mul' (computableInPolyTime_num' hp) (computableInPolyTime_num' hq)
  have hden := binary_mul.comp ((computableInPolyTime_den' hp).prod (computableInPolyTime_den' hq))
  refine (computableInPolyTime_mkRat' hnum hden).of_enc_eq fun r => congrArg encRatBin ?_
  simp only [Function.comp_apply]
  rw [Rat.mul_def]
  exact Rat.normalize_eq_mkRat (Nat.mul_ne_zero r.1.den_nz r.2.den_nz)

/-- Composition form of `computableInPolyTime_mul`. -/
theorem computableInPolyTime_mul' {α : Type} {enc : α ↪ List Bool} {f g : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin)
    (hg : ComputableInPolyTime g enc encRatBin) :
    ComputableInPolyTime (fun x => f x * g x) enc encRatBin :=
  (computableInPolyTime_mul.comp (hf.prod hg)).of_enc_eq fun _ => rfl

/-- Rational multiplicative inverse (with totalized `0⁻¹ = 0`) runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_inv :
    ComputableInPolyTime (fun q : ℚ => q⁻¹) encRatBin encRatBin := by
  have h := computableInPolyTime_divInt'
    (intBin_natCast.comp computableInPolyTime_den) computableInPolyTime_num
  refine h.of_enc_eq fun q => congrArg encRatBin ?_
  simpa only [Function.comp_apply] using Rat.inv_def q

/-- Composition form of `computableInPolyTime_inv`. -/
theorem computableInPolyTime_inv' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun x => (f x)⁻¹) enc encRatBin :=
  (computableInPolyTime_inv.comp hf).of_enc_eq fun _ => rfl

/-- Rational division (with totalized `q / 0 = 0`) runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_div :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 / p.2)
      (encPair encRatBin encRatBin) encRatBin := by
  have h := computableInPolyTime_mul' (fst encRatBin encRatBin)
    (computableInPolyTime_inv' (snd encRatBin encRatBin))
  exact h.of_enc_eq fun p => congrArg encRatBin (div_eq_mul_inv p.1 p.2)

/-- Composition form of `computableInPolyTime_div`. -/
theorem computableInPolyTime_div' {α : Type} {enc : α ↪ List Bool} {f g : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin)
    (hg : ComputableInPolyTime g enc encRatBin) :
    ComputableInPolyTime (fun x => f x / g x) enc encRatBin :=
  (computableInPolyTime_div.comp (hf.prod hg)).of_enc_eq fun _ => rfl

/-- Strict comparison `p < q` on binary rationals runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lt :
    ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 < p.2))
      (encPair encRatBin encRatBin) encBool := by
  have hp := fst encRatBin encRatBin
  have hq := snd encRatBin encRatBin
  have hl := intBin_mul' (computableInPolyTime_num' hp)
    (intBin_natCast.comp (computableInPolyTime_den' hq))
  have hr := intBin_mul' (computableInPolyTime_num' hq)
    (intBin_natCast.comp (computableInPolyTime_den' hp))
  refine (intBin_lt.comp (hl.prod hr)).of_enc_eq fun r => congrArg encBool ?_
  simp only [Function.comp_apply, Rat.lt_iff]

/-- Composition form of `computableInPolyTime_lt`. -/
theorem computableInPolyTime_lt' {α : Type} {enc : α ↪ List Bool} {f g : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin)
    (hg : ComputableInPolyTime g enc encRatBin) :
    ComputableInPolyTime (fun x => decide (f x < g x)) enc encBool :=
  (computableInPolyTime_lt.comp (hf.prod hg)).of_enc_eq fun _ => rfl

/-- Weak comparison `p ≤ q` on binary rationals runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_le :
    ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 ≤ p.2))
      (encPair encRatBin encRatBin) encBool := by
  have hp := fst encRatBin encRatBin
  have hq := snd encRatBin encRatBin
  have hl := intBin_mul' (computableInPolyTime_num' hp)
    (intBin_natCast.comp (computableInPolyTime_den' hq))
  have hr := intBin_mul' (computableInPolyTime_num' hq)
    (intBin_natCast.comp (computableInPolyTime_den' hp))
  refine (intBin_le.comp (hl.prod hr)).of_enc_eq fun r => congrArg encBool ?_
  simp only [Function.comp_apply, Rat.le_iff]

/-- Composition form of `computableInPolyTime_le`. -/
theorem computableInPolyTime_le' {α : Type} {enc : α ↪ List Bool} {f g : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin)
    (hg : ComputableInPolyTime g enc encRatBin) :
    ComputableInPolyTime (fun x => decide (f x ≤ g x)) enc encBool :=
  (computableInPolyTime_le.comp (hf.prod hg)).of_enc_eq fun _ => rfl

/-- Absolute value `|q|` on binary rationals runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_abs :
    ComputableInPolyTime (fun q : ℚ => |q|) encRatBin encRatBin := by
  have h := (computableInPolyTime_lt' id' (const 0)).ite' computableInPolyTime_neg id'
  refine h.of_enc_eq fun q => congrArg encRatBin ?_
  simp only [decide_eq_true_eq]
  split_ifs with hlt
  · exact abs_of_neg hlt
  · exact abs_of_nonneg (not_lt.mp hlt)

/-- Composition form of `computableInPolyTime_abs`. -/
theorem computableInPolyTime_abs' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun x => |f x|) enc encRatBin :=
  computableInPolyTime_abs.comp hf

/-- Binary minimum `min p q` on binary rationals runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_min :
    ComputableInPolyTime (fun p : ℚ × ℚ => min p.1 p.2)
      (encPair encRatBin encRatBin) encRatBin := by
  have hp := fst encRatBin encRatBin
  have hq := snd encRatBin encRatBin
  exact (computableInPolyTime_le.ite' hp hq).of_enc_eq fun r => congrArg encRatBin <| by
    simp only [min_def, decide_eq_true_eq]

/-- Binary maximum `max p q` on binary rationals runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_max :
    ComputableInPolyTime (fun p : ℚ × ℚ => max p.1 p.2)
      (encPair encRatBin encRatBin) encRatBin := by
  have hp := fst encRatBin encRatBin
  have hq := snd encRatBin encRatBin
  exact (computableInPolyTime_le.ite' hq hp).of_enc_eq fun r => congrArg encRatBin <| by
    simp only [max_def, decide_eq_true_eq]

private theorem floor_eq_sign_div (q : ℚ) :
    ⌊q⌋ = if q.num < 0 then -(((q.num.natAbs + q.den - 1) / q.den : ℕ) : ℤ)
      else ((q.num.natAbs / q.den : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff]
  have hd : 0 < q.den := q.den_pos
  have hdQ : (0 : ℚ) < (q.den : ℚ) := Nat.cast_pos.mpr hd
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  by_cases hneg : q.num < 0
  · rw [ite_eq_left hneg]
    set m := q.num.natAbs
    have hnum : q.num = -(m : ℤ) := by
      have := Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
      omega
    have hm_pos : 0 < m := by omega
    set k := (m + q.den - 1) / q.den
    have hk_low : k * q.den ≤ m + q.den - 1 := Nat.div_mul_le_self _ q.den
    have hk_high : m + q.den - 1 < (k + 1) * q.den := by
      have hlt := Nat.lt_mul_div_succ (m + q.den - 1) hd
      simpa only [k, mul_comm] using hlt
    have h1 : m ≤ k * q.den := by
      have : (k + 1) * q.den = k * q.den + q.den := by ring
      omega
    have h2 : k * q.den < m + q.den := by omega
    have h1Q : (m : ℚ) ≤ (k : ℚ) * (q.den : ℚ) := by exact_mod_cast h1
    have h2Q : (k : ℚ) * (q.den : ℚ) < (m : ℚ) + (q.den : ℚ) := by exact_mod_cast h2
    have hnumQ : (q.num : ℚ) = -(m : ℚ) := by exact_mod_cast hnum
    constructor
    · rw [hq, le_div_iff₀ hdQ, hnumQ]
      push_cast; linarith
    · rw [hq, div_lt_iff₀ hdQ, hnumQ]
      push_cast; linarith
  · rw [ite_eq_right hneg]
    set m := q.num.natAbs
    have hnum : q.num = (m : ℤ) := (Int.ofNat_natAbs_of_nonneg (not_lt.mp hneg)).symm
    set k := m / q.den
    have h1 : k * q.den ≤ m := Nat.div_mul_le_self m q.den
    have h2 : m < (k + 1) * q.den := by
      have hlt := Nat.lt_mul_div_succ m hd
      simpa only [k, mul_comm] using hlt
    have h1Q : (k : ℚ) * (q.den : ℚ) ≤ (m : ℚ) := by exact_mod_cast h1
    have h2Q : (m : ℚ) < ((k : ℚ) + 1) * (q.den : ℚ) := by exact_mod_cast h2
    have hnumQ : (q.num : ℚ) = (m : ℚ) := by exact_mod_cast hnum
    constructor
    · rw [hq, le_div_iff₀ hdQ, hnumQ]
      push_cast; linarith
    · rw [hq, div_lt_iff₀ hdQ, hnumQ]
      push_cast; linarith

/-- Integer floor `⌊q⌋` of a binary rational runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_floor :
    ComputableInPolyTime (fun q : ℚ => ⌊q⌋) encRatBin encIntBin := by
  have hn := computableInPolyTime_num
  have hd := computableInPolyTime_den
  have ha := intBin_natAbs.comp hn
  have hnegQ := intBin_neg.comp
    (intBin_natCast.comp (binary_div' (binary_sub' (binary_add' ha hd) (const 1)) hd))
  have hposQ := intBin_natCast.comp (binary_div' ha hd)
  refine ((intBin_isNeg.comp hn).ite' hnegQ hposQ).of_enc_eq fun q => congrArg encIntBin ?_
  simpa only [Function.comp_apply, decide_eq_true_eq] using floor_eq_sign_div q

/-- Composition form of `computableInPolyTime_floor`. -/
theorem computableInPolyTime_floor' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun x => ⌊f x⌋) enc encIntBin :=
  computableInPolyTime_floor.comp hf

/-- Integer ceiling `⌈q⌉` of a binary rational runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ceil :
    ComputableInPolyTime (fun q : ℚ => ⌈q⌉) encRatBin encIntBin := by
  have h := intBin_neg.comp (computableInPolyTime_floor.comp computableInPolyTime_neg)
  refine h.of_enc_eq fun q => congrArg encIntBin ?_
  have hceil : ⌈q⌉ = -⌊-q⌋ := by
    have := Int.floor_neg (a := q)
    omega
  simpa only [Function.comp_apply] using hceil

/-- Composition form of `computableInPolyTime_ceil`. -/
theorem computableInPolyTime_ceil' {α : Type} {enc : α ↪ List Bool} {f : α → ℚ}
    (hf : ComputableInPolyTime f enc encRatBin) :
    ComputableInPolyTime (fun x => ⌈f x⌉) enc encIntBin :=
  computableInPolyTime_ceil.comp hf

/-- Positive common denominator `(qs.map Rat.den).prod` of a finite list of rationals. -/
def clearDenom (qs : List ℚ) : ℕ :=
  (qs.map Rat.den).prod

/-- `clearDenom qs` is strictly positive for every list `qs`. -/
theorem clearDenom_pos (qs : List ℚ) : 0 < clearDenom qs := by
  unfold clearDenom
  induction qs with
  | nil => simp
  | cons q rest ih => exact Nat.mul_pos q.den_pos ih

/-- Every element's denominator divides `clearDenom qs`. -/
theorem den_dvd_clearDenom {qs : List ℚ} {q : ℚ} (hq : q ∈ qs) :
    q.den ∣ clearDenom qs :=
  List.dvd_prod (List.mem_map_of_mem hq)

/-- Exact integer `q.num * (D / q.den : ℤ)` obtained by multiplying `q` by a multiple `D` of its
denominator. -/
def scaleToInt (D : ℕ) (q : ℚ) : ℤ :=
  q.num * ((D / q.den : ℕ) : ℤ)

/-- Whenever `q.den ∣ D`, casting `scaleToInt D q` back to `ℚ` yields `(D : ℚ) * q`. -/
theorem cast_scaleToInt {D : ℕ} {q : ℚ} (hdvd : q.den ∣ D) :
    (scaleToInt D q : ℚ) = (D : ℚ) * q := by
  unfold scaleToInt
  have hmul : (D / q.den) * q.den = D := Nat.div_mul_cancel hdvd
  have hmulQ : ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) = (D : ℚ) := by exact_mod_cast hmul
  have hdz : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  push_cast
  conv_rhs => rw [← Rat.num_div_den q]
  rw [mul_div_assoc', eq_div_iff hdz]
  calc
    (q.num : ℚ) * ((D / q.den : ℕ) : ℚ) * (q.den : ℚ)
        = (q.num : ℚ) * (((D / q.den : ℕ) : ℚ) * (q.den : ℚ)) := by ring
    _ = (D : ℚ) * (q.num : ℚ) := by rw [hmulQ]; ring

/-- Computing the product of a list of unsigned binary naturals runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_natProd :
    ComputableInPolyTime List.prod (encList encNat) encNat := by
  have hcast : ComputableInPolyTime (List.map (fun n : ℕ => (n : ℤ)))
      (encList encNat) (encList encIntBin) :=
    mapWith (intBin_natCast.comp (snd encBool encNat)) (const false)
      (id' (encIn := encList encNat))
  refine (intBin_toNat.comp (intBin_prod.comp hcast)).of_enc_eq fun l => congrArg encNat ?_
  have hprod : (l.map (fun n : ℕ => (n : ℤ))).prod = ((l.prod : ℕ) : ℤ) := by
    induction l with
    | nil => rfl
    | cons a s ih =>
      rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
      exact (Nat.cast_mul a s.prod).symm
  change l.prod = ((l.map (fun n : ℕ => (n : ℤ))).prod).toNat
  rw [hprod, Int.toNat_natCast]

/-- Computing `clearDenom qs` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_clearDenom :
    ComputableInPolyTime clearDenom (encList encRatBin) encNat := by
  unfold clearDenom
  have hmap := mapWith (computableInPolyTime_den.comp (snd encBool encRatBin)) (const false)
    (id' (encIn := encList encRatBin))
  exact computableInPolyTime_natProd.comp hmap

/-- Computing `scaleToInt D q` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_scaleToInt :
    ComputableInPolyTime (fun p : ℕ × ℚ => scaleToInt p.1 p.2)
      (encPair encNat encRatBin) encIntBin := by
  unfold scaleToInt
  have hD := fst encNat encRatBin
  have hq := snd encNat encRatBin
  exact intBin_mul' (computableInPolyTime_num' hq)
    (intBin_natCast.comp (binary_div' hD (computableInPolyTime_den' hq)))

/-- Exact summation of a finite list of binary rationals via common-denominator scaling runs in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sum :
    ComputableInPolyTime List.sum (encList encRatBin) encRatBin := by
  have hD := computableInPolyTime_clearDenom
  have hscaled := mapWith
    (computableInPolyTime_scaleToInt.comp
      ((fst encNat encRatBin).prod (snd encNat encRatBin)))
    hD (id' (encIn := encList encRatBin))
  have hnum := intBin_sum.comp hscaled
  refine (computableInPolyTime_mkRat' hnum hD).of_enc_eq fun qs => congrArg encRatBin ?_
  have hDne : (clearDenom qs : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (clearDenom_pos qs))
  change qs.sum = mkRat ((qs.map (scaleToInt (clearDenom qs))).sum) (clearDenom qs)
  rw [Rat.mkRat_eq_div, eq_div_iff hDne]
  have hsum : ∀ sub : List ℚ, (∀ q ∈ sub, q.den ∣ clearDenom qs) →
      (((sub.map (scaleToInt (clearDenom qs))).sum : ℤ) : ℚ) =
        sub.sum * (clearDenom qs : ℚ) := by
    intro sub hsub
    induction sub with
    | nil => simp
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add]
      rw [cast_scaleToInt (hsub q List.mem_cons_self),
        ih (fun r hr => hsub r (List.mem_cons_of_mem q hr))]
      ring
  exact (hsum qs fun q hq => den_dvd_clearDenom hq).symm

/-- Minimum of a list of binary rationals with a supplied fallback value `d`. -/
def listMinD (d : ℚ) (qs : List ℚ) : ℚ :=
  qs.foldl min d

/-- `listMinD d qs` is at most the fallback value `d`. -/
theorem listMinD_le_default (d : ℚ) (qs : List ℚ) : listMinD d qs ≤ d := by
  unfold listMinD
  induction qs generalizing d with
  | nil => exact le_rfl
  | cons q rest ih => exact (ih (min d q)).trans (min_le_left d q)

/-- `listMinD d qs` is at most every member of `qs`. -/
theorem listMinD_le_of_mem (d : ℚ) {qs : List ℚ} {q : ℚ} (hq : q ∈ qs) :
    listMinD d qs ≤ q := by
  unfold listMinD
  induction qs generalizing d with
  | nil => cases hq
  | cons r rest ih =>
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact (listMinD_le_default (min d q) rest).trans (min_le_right d q)
    · exact ih (min d r) hmem

/-- `listMinD d qs` equals either `d` or some element of `qs`. -/
theorem listMinD_eq_default_or_mem (d : ℚ) (qs : List ℚ) :
    listMinD d qs = d ∨ listMinD d qs ∈ qs := by
  unfold listMinD
  induction qs generalizing d with
  | nil => exact Or.inl rfl
  | cons r rest ih =>
    simp only [List.foldl_cons]
    rcases ih (min d r) with heq | hmem
    · rw [heq]
      rcases min_choice d r with h1 | h2
      · exact Or.inl h1
      · rw [h2]; exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem r hmem)

/-- If `d` and every element of `qs` are strictly positive, then `listMinD d qs` is strictly
positive. -/
theorem listMinD_pos {d : ℚ} {qs : List ℚ} (hd : 0 < d) (hqs : ∀ q ∈ qs, 0 < q) :
    0 < listMinD d qs := by
  rcases listMinD_eq_default_or_mem d qs with heq | hmem
  · rw [heq]; exact hd
  · exact hqs _ hmem

/-- Computing `listMinD p.1 p.2` runs in polynomial time because the running minimum is always
equal to the fallback or an already-present input element, so its encoding never exceeds the input
length. -/
@[fun_prop]
theorem computableInPolyTime_listMinD :
    ComputableInPolyTime (fun p : ℚ × List ℚ => listMinD p.1 p.2)
      (encPair encRatBin (encList encRatBin)) encRatBin := by
  let step : ℚ × List ℚ → ℚ × List ℚ := fun s =>
    match s.2 with
    | [] => s
    | q :: rest => (min s.1 q, rest)
  have hstep_eq : ∀ s : ℚ × List ℚ,
      step s = if s.2.isEmpty then s else (min s.1 (s.2.headD 0), s.2.tail) := by
    rintro ⟨acc, _ | ⟨q, rest⟩⟩ <;> rfl
  have hstep : ComputableInPolyTime step
      (encPair encRatBin (encList encRatBin)) (encPair encRatBin (encList encRatBin)) := by
    have hacc := fst encRatBin (encList encRatBin)
    have hls := snd encRatBin (encList encRatBin)
    have hempty := (listIsEmpty' encRatBin).comp hls
    have hhd := (headD (encA := encRatBin) (encL := encList encRatBin) (0 : ℚ)).comp hls
    have htl := (listTail encRatBin).comp hls
    have hbranch := hempty.ite' id' ((computableInPolyTime_min.comp (hacc.prod hhd)).prod htl)
    exact hbranch.of_enc_eq fun s => congrArg _ (hstep_eq s)
  have hiter_eq : ∀ (i : ℕ) (d : ℚ) (l : List ℚ),
      step^[i] (d, l) = (listMinD d (l.take i), l.drop i) := by
    intro i
    induction i with
    | zero => intro d l; simp [listMinD]
    | succ k ih =>
      intro d l
      cases l with
      | nil =>
        change step^[k] (step (d, [])) = _
        simpa [step, listMinD] using ih d []
      | cons q rest =>
        change step^[k] (step (d, q :: rest)) = _
        simpa [step, listMinD, List.take_succ_cons, List.drop_succ_cons, List.foldl_cons] using
          ih (min d q) rest
  have hcount : ComputableInPolyTime (fun p : ℚ × List ℚ => p.2.length)
      (encPair encRatBin (encList encRatBin)) encUnary := by
    fun_prop
  have hbound_fn : ∀ (p : ℚ × List ℚ) (i : ℕ), i ≤ p.2.length →
      (encPair encRatBin (encList encRatBin) (step^[i] p)).length ≤
        4 * (encPair encRatBin (encList encRatBin) p).length := by
    rintro ⟨d, l⟩ i _
    rw [hiter_eq]
    have hacc_len : (encRatBin (listMinD d (l.take i))).length ≤
        (encPair encRatBin (encList encRatBin) (d, l)).length := by
      rcases listMinD_eq_default_or_mem d (l.take i) with heq | hmem
      · rw [heq]
        exact length_le_encPair_left encRatBin (encList encRatBin) (d, l)
      · have hmem_l : listMinD d (l.take i) ∈ l := List.mem_of_mem_take hmem
        have h1 : (encRatBin (listMinD d (l.take i))).length ≤ (encList encRatBin l).length := by
          have := List.le_sum_of_mem
            (List.mem_map_of_mem (f := fun a => (encRatBin a).length) hmem_l)
          exact this.trans (sum_length_le_length_encList (enc := encRatBin) l)
        exact h1.trans (length_le_encPair_right encRatBin (encList encRatBin) (d, l))
    have hdrop_len : (encList encRatBin (l.drop i)).length ≤ (encList encRatBin l).length := by
      rw [length_encList, length_encList]
      have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
      conv_rhs => rw [hsplit, List.map_append, List.sum_append]
      omega
    have hdrop_pair := hdrop_len.trans
      (length_le_encPair_right encRatBin (encList encRatBin) (d, l))
    have htot : (encPair encRatBin (encList encRatBin) (listMinD d (l.take i), l.drop i)).length =
        2 * (encRatBin (listMinD d (l.take i))).length + 1 +
          (encList encRatBin (l.drop i)).length :=
      length_encPair (listMinD d (l.take i), l.drop i)
    have hpos : 1 ≤ (encPair encRatBin (encList encRatBin) (d, l)).length := by
      rw [length_encPair]; omega
    omega
  have hrun := (iterate hcount id' hstep ((PolyBounded.const 4).mul .self) hbound_fn).fst'
  refine hrun.of_enc_eq fun p => congrArg encRatBin ?_
  rw [hiter_eq, List.take_length]

end CslibFrontier.RatBinary
