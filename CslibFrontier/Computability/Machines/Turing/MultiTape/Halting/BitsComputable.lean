module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Reduction
public import Mathlib.Computability.Partrec

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
import CslibFrontier.Computability.Machines.Turing.TM2.Computable
import CslibFrontier.Computability.Machines.Turing.TM2.PartrecToTM2
import Mathlib.Computability.Primrec.List

/-!
# Encoding-Level `Computable → IsComputable` Bridge

Shows that any function `f : α → β` whose action on arbitrary bitstring encodings `encA, encB`
is realized by a Mathlib-`Computable` function `g : List Bool → List Bool` is multi-tape
Turing-machine `IsComputable`.

## Main results

* `isComputable_of_computable_enc`: lifts `Computable g` on `List Bool → List Bool` with
  `g (encA a) = encB (f a)` to `IsComputable f encA encB`.
-/

public section

namespace CslibFrontier.Computability.Machines.Turing.MultiTape.Halting

open Turing.MultiTapeTM

private def bitsToNat (w : List Bool) : ℕ :=
  ofBits (w ++ [true])

private def natToBits (n : ℕ) : List Bool :=
  n.bits.dropLast

private lemma ofBits_append_true_ne_zero (w : List Bool) : ofBits (w ++ [true]) ≠ 0 := by
  induction w with
  | nil => decide
  | cons b w ih =>
    change Nat.bit b (ofBits (w ++ [true])) ≠ 0
    cases b <;> simp [Nat.bit, ih]

private lemma bits_bitsToNat (w : List Bool) : (bitsToNat w).bits = w ++ [true] := by
  unfold bitsToNat
  induction w with
  | nil => decide
  | cons b w ih =>
    change (Nat.bit b (ofBits (w ++ [true]))).bits = b :: (w ++ [true])
    rw [Nat.bits_append_bit _ _ (fun h ↦ absurd h (ofBits_append_true_ne_zero w)), ih]

private lemma natToBits_bitsToNat (w : List Bool) : natToBits (bitsToNat w) = w := by
  simp [natToBits, bits_bitsToNat]

private lemma dropLast_eq_rev_tail_rev {α : Type*} (l : List α) :
    l.dropLast = l.reverse.tail.reverse := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b l), ih]
      rw [List.reverse_cons (a := a) (as := b :: l),
        List.tail_append_of_ne_nil (by simp), List.reverse_append,
        List.reverse_singleton, List.singleton_append]

private lemma poly_of_enc_eq {α β δ : Type*} {encIn : α ↪ List Bool}
    {encMid : β ↪ List Bool} {encD : δ ↪ List Bool} {f : α → β} {g : α → δ}
    (hf : ComputableInPolyTime f encIn encMid) (h : ∀ a, encD (g a) = encMid (f a)) :
    ComputableInPolyTime g encIn encD := by
  rcases hf with ⟨t, s, ht, hs, k, State, hfin, tm, htm⟩
  exact ⟨t, s, ht, hs, k, State, hfin, tm, fun a ↦ by rw [h a]; exact htm a⟩

private lemma primrec_ofBits : Primrec ofBits := by
  have hbit : Primrec₂ fun (_ : List Bool) (p : Bool × ℕ) ↦ Nat.bit p.1 p.2 :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂.of_eq
      fun _ p ↦ by cases p.1 <;> simp [Nat.bit]
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hbit).of_eq fun _ ↦ rfl

private lemma primrec_bitsToNat : Primrec bitsToNat :=
  primrec_ofBits.comp (Primrec.list_append.comp Primrec.id (Primrec.const [true]))

private lemma primrec_natToBits : Primrec natToBits := by
  have hdrop : Primrec (fun l : List Bool ↦ l.reverse.tail.reverse) :=
    Primrec.list_reverse.comp (Primrec.list_tail.comp Primrec.list_reverse)
  refine (hdrop.comp Turing.PartrecToTM2.primrec_bits).of_eq fun n ↦ ?_
  dsimp [natToBits]
  exact (dropLast_eq_rev_tail_rev n.bits).symm

private lemma poly_bitsToNat : ComputableInPolyTime bitsToNat encBits encNat := by
  have h1 : ComputableInPolyTime (fun w : List Bool ↦ w ++ [true]) encBits encBits :=
    ComputableInPolyTime.bitsAppend ComputableInPolyTime.id'
      (ComputableInPolyTime.const [true])
  exact poly_of_enc_eq h1 fun w ↦ by simp [encNat_apply, bits_bitsToNat]

private lemma poly_natToBits : ComputableInPolyTime natToBits encNat encBits := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits :=
    ComputableInPolyTime.of_eq fun _ ↦ rfl
  have h1 : ComputableInPolyTime (fun l : List Bool ↦ l.reverse.tail.reverse) encBits encBits :=
    ComputableInPolyTime.listToBits.comp
      ((ComputableInPolyTime.listReverse encBool).comp
        ((ComputableInPolyTime.listTail encBool).comp
          ((ComputableInPolyTime.listReverse encBool).comp ComputableInPolyTime.bitsToList)))
  exact poly_of_enc_eq (h1.comp hbits) fun n ↦ by
    simp only [encBits_apply, Function.comp_apply, natToBits, dropLast_eq_rev_tail_rev]

/-- Any function `f : α → β` whose encoded bitstring action is implemented by a Mathlib-`Computable`
function `g : List Bool → List Bool` is multi-tape Turing-machine `IsComputable`. -/
theorem isComputable_of_computable_enc {α β : Type} {f : α → β}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (g : List Bool → List Bool) (hg : Computable g) (hfg : ∀ a, g (encA a) = encB (f a)) :
    IsComputable f encA encB := by
  let h : ℕ → ℕ := fun n ↦ bitsToNat (g (natToBits n))
  have hh : Computable h := (primrec_bitsToNat.to_comp.comp hg).comp primrec_natToBits.to_comp
  have hEncNat : ((Encodable.encode' ℕ).trans encNat) = encNat := by ext n; rfl
  have hh_tm : IsComputable h encNat encNat := by
    simpa [hEncNat] using hh.isComputable
  have hg_tm : IsComputable g encBits encBits := by
    have hcomp := poly_natToBits.isComputable.comp (hh_tm.comp poly_bitsToNat.isComputable)
    exact (isComputable_iff.mp hcomp).elim fun k hk ↦
      isComputable_iff.mpr ⟨k, hk.choose, hk.choose_spec.choose, hk.choose_spec.choose_spec.choose,
        fun w ↦ by
          simpa [Function.comp_def, h, natToBits_bitsToNat] using
            hk.choose_spec.choose_spec.choose_spec w⟩
  obtain ⟨k, State, hfin, tm, htm⟩ := isComputable_iff.mp hg_tm
  exact isComputable_iff.mpr ⟨k, State, hfin, tm, fun a ↦ by
    simpa [encBits_apply, hfg a] using htm (encA a)⟩

end CslibFrontier.Computability.Machines.Turing.MultiTape.Halting
