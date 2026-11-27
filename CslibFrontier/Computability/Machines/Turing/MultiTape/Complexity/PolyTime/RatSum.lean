/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.TrackedRun

/-!
# Polynomial-Time Summation of Rational Lists and Total Extension via Decoders

Two general polynomial-time combinators for `Turing.MultiTapeTM`:

* `Turing.MultiTapeTM.ComputableInPolyTime.rat_listSum`: summing a list `l : List ℚ` under
  `encList encRat` is computable in polynomial time (avoiding intermediate GCD blowup warnings by
  accumulating an unnormalized numerator–denominator pair `(a, b) : ℤ × ℕ` with linearly bounded
  bit length and normalizing once via `Rat.divInt`).
* `Turing.MultiTapeTM.ComputableInPolyTime.exists_extension_of_decoder`: every polynomial-time
  function `f : α → β` into an encoding `encOut` admitting a total polynomial-time `Decoder` extends
  to a polynomial-time map `g : List Bool → β` on all bit strings `encBits`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private def unnormRatAdd (acc : ℤ × ℕ) (q : ℚ) : ℤ × ℕ :=
  (acc.1 * (q.den : ℤ) + q.num * (acc.2 : ℤ), acc.2 * q.den)

private theorem unnormRatAdd_fold_eq (xs : List ℚ) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    let r := xs.foldl unnormRatAdd (a, b)
    0 < r.2 ∧ Rat.divInt r.1 (r.2 : ℤ) = Rat.divInt a (b : ℤ) + xs.sum := by
  induction xs generalizing a b with
  | nil => exact ⟨hb, by simp⟩
  | cons q tl ih =>
    simp only [List.foldl_cons, List.sum_cons]
    obtain ⟨hpos, heq⟩ := ih (a * (q.den : ℤ) + q.num * (b : ℤ)) (b * q.den)
      (Nat.mul_pos hb q.den_pos)
    refine ⟨hpos, heq.trans ?_⟩
    have hadd : Rat.divInt (a * (q.den : ℤ) + q.num * (b : ℤ)) ((b * q.den : ℕ) : ℤ) =
        Rat.divInt a (b : ℤ) + q := by
      conv_rhs => rw [← Rat.num_divInt_den q]
      rw [Rat.divInt_add_divInt _ _ (Nat.cast_ne_zero.mpr hb.ne')
        (Nat.cast_ne_zero.mpr q.den_pos.ne')]
      push_cast; rfl
    rw [hadd, add_assoc]

private theorem nat_size_mul_le (x y : ℕ) : (x * y).size ≤ x.size + y.size := by
  rcases eq_or_ne x 0 with rfl | _
  · simp
  · rcases eq_or_ne y 0 with rfl | _
    · simp
    · refine Nat.size_le.mpr ?_
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul'' (Nat.lt_size_self x) (Nat.lt_size_self y)

private theorem nat_size_add_le_max (x y : ℕ) : (x + y).size ≤ max x.size y.size + 1 := by
  refine Nat.size_le.mpr ?_
  have hx : x < 2 ^ max x.size y.size :=
    (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hy : y < 2 ^ max x.size y.size :=
    (Nat.lt_size_self y).trans_le (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  rw [Nat.pow_succ]; omega

/-- Summing a framed list of rational numbers `List.sum : List ℚ → ℚ` is computable in polynomial
time under `encList encRat` and `encRat`. -/
@[fun_prop]
theorem rat_listSum : ComputableInPolyTime (List.sum : List ℚ → ℚ) (encList encRat) encRat := by
  have hstep : ComputableInPolyTime
      (fun p : (ℤ × ℕ) × ℚ => unnormRatAdd p.1 p.2)
      (encPair (encPair encIntBin encNat) encRat) (encPair encIntBin encNat) := by
    unfold unnormRatAdd; fun_prop
  have hfold : ComputableInPolyTime
      (fun l : List ℚ => l.foldl unnormRatAdd (0, 1))
      (encList encRat) (encPair encIntBin encNat) := by
    have hsize_encNat : ∀ n : ℕ, n.size = (encNat n).length := fun n => by
      rw [encNat_apply, Nat.size_eq_bits_len]
    have hlen_intBin : ∀ z : ℤ, (encIntBin z).length = 1 + z.natAbs.size := fun z => by
      rw [encIntBin_apply, List.length_cons, Nat.size_eq_bits_len]; omega
    have hlen_ratd : ∀ (a : ℤ) (b : ℕ), (encPair encIntBin encNat (a, b)).length =
        3 + 2 * a.natAbs.size + b.size := fun a b => by
      rw [length_encPair]; dsimp only; rw [hlen_intBin, ← hsize_encNat]; omega
    have hsubl : ∀ {l₁ l₂ : List ℚ}, l₁.Sublist l₂ →
        (encList encRat l₁).length ≤ (encList encRat l₂).length := by
      intro l₁ l₂ h; induction h with
      | slnil => exact le_rfl
      | cons _ _ ih => simp only [encList_cons, List.length_append]; omega
      | cons_cons _ _ ih => simp only [encList_cons, List.length_append]; omega
    refine ComputableInPolyTime.foldl' id' (const ((0 : ℤ), (1 : ℕ))) hstep
      (B := fun l => 16 * ((encList encRat l).length + 1) ^ 1)
      (PolyBounded.of_forall_le 16 1 fun _ => le_rfl) fun l i _ => ?_
    have hsz : ∀ (xs : List ℚ) (a : ℤ) (b : ℕ),
        let r := xs.foldl unnormRatAdd (a, b)
        r.2.size ≤ b.size + (encList encRat xs).length ∧
        r.1.natAbs.size ≤ max a.natAbs.size b.size + (encList encRat xs).length := by
      intro xs; induction xs with
      | nil => intro a b; exact ⟨by simp, by simp⟩
      | cons q tl ih =>
        intro a b
        simp only [List.foldl_cons, encList_cons, List.length_append]
        have hqlen : q.num.natAbs.size + q.den.size + 1 ≤
            (MultiTapeTM.frame (encRat q)).length := by
          rw [length_frame, encRat_apply, show encRatData (q.num, q.den) =
            encPair encIntBin encNat (q.num, q.den) from rfl, hlen_ratd]; omega
        let a' : ℤ := a * (q.den : ℤ) + q.num * (b : ℤ)
        let b' : ℕ := b * q.den
        have hb' : b'.size ≤ b.size + q.den.size := nat_size_mul_le b q.den
        have ha' : a'.natAbs.size ≤
            max a.natAbs.size b.size + q.num.natAbs.size + q.den.size + 1 := by
          have htri : a'.natAbs ≤ a.natAbs * q.den + q.num.natAbs * b := by
            simpa [a', Int.natAbs_mul] using Int.natAbs_add_le (a * q.den) (q.num * b)
          have hs1 := (Nat.size_le_size htri).trans (nat_size_add_le_max _ _)
          have hs2 := nat_size_mul_le a.natAbs q.den
          have hs3 := nat_size_mul_le q.num.natAbs b
          exact hs1.trans (by
            have : max (a.natAbs * q.den).size (q.num.natAbs * b).size ≤
                max a.natAbs.size b.size + q.num.natAbs.size + q.den.size :=
              max_le (hs2.trans (by have := le_max_left a.natAbs.size b.size; omega))
                (hs3.trans (by have := le_max_right a.natAbs.size b.size; omega))
            omega)
        obtain ⟨h1, h2⟩ := ih a' b'
        refine ⟨h1.trans (by omega), h2.trans ?_⟩
        have hm : max a'.natAbs.size b'.size ≤
            max a.natAbs.size b.size + (MultiTapeTM.frame (encRat q)).length :=
          max_le (ha'.trans (by omega))
            (hb'.trans (by have := le_max_right a.natAbs.size b.size; omega))
        omega
    obtain ⟨hb_sz, ha_sz⟩ := hsz (l.take i) 0 1
    set r := (l.take i).foldl unnormRatAdd (0, 1)
    have htake := hsubl (List.take_sublist i l)
    have h1 : r.2.size ≤ 1 + (encList encRat (l.take i)).length := by
      simpa [show (1 : ℕ).size = 1 by decide] using hb_sz
    have h2 : r.1.natAbs.size ≤ 1 + (encList encRat (l.take i)).length := by
      simpa [show (0 : ℕ).size = 0 by decide, show (1 : ℕ).size = 1 by decide] using ha_sz
    rw [show r = (r.1, r.2) from rfl, hlen_ratd, pow_one]; omega
  have hdiv : ComputableInPolyTime (fun p : ℤ × ℕ => Rat.divInt p.1 (p.2 : ℤ))
      (encPair encIntBin encNat) encRat := by fun_prop
  refine (hdiv.comp hfold).of_enc_eq fun l => congrArg encRat ?_
  have h := (unnormRatAdd_fold_eq l 0 1 Nat.one_pos).2
  dsimp only [Function.comp_apply]
  rw [h, Rat.zero_divInt, zero_add]

/-- Every polynomial-time function `f : α → β` whose target encoding `encOut` admits a total
polynomial-time decoder `D : Decoder encOut` extends to a polynomial-time function
`g : List Bool → β` on all bit strings `encBits` satisfying `g (encIn a) = f a` for all `a : α`. -/
theorem exists_extension_of_decoder {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (D : Decoder encOut) {f : α → β} (hf : ComputableInPolyTime f encIn encOut) :
    ∃ g : List Bool → β, ComputableInPolyTime g encBits encOut ∧ ∀ a, g (encIn a) = f a := by
  obtain ⟨t, _, ht, -, k, State, hfin, tm, htm⟩ := hf
  obtain ⟨c, d, ht⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  have hp (w : List Bool) : t w.length ≤ p.eval w.length := by simpa [p] using ht w.length
  refine ⟨fun w => D.decode (trackedRun tm (w, p.eval w.length)).1.output, ?_, fun a => ?_⟩
  · have hsteps : ComputableInPolyTime (fun w : List Bool => p.eval w.length) encBits encUnary :=
      (unary_eval p).comp (encoding_length encBits)
    have hrun := (computableInPolyTime_trackedRun tm).comp (id'.prod hsteps)
    exact D.computableInPolyTime.comp (finiteCfg_output.comp (.fst' hrun))
  · dsimp only
    rw [(trackedAgrees_trackedRun tm (encIn a) (p.eval (encIn a).length)).output,
      ((htm a).runFrom_of_le (hp (encIn a))).2, D.decode_enc]

end Turing.MultiTapeTM.ComputableInPolyTime
