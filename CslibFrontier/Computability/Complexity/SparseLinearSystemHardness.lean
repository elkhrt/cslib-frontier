/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Problems.LinearProgramming
public import CslibFrontier.Computability.Complexity.Problems.ThreeExactCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat

import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded-Mask Closure of `NP` and NP-Completeness of Sparse Linear Systems

This module establishes bounded-mask existential closure of `NP` (`mem_NP_of_boundedBits_NP`),
polynomial-time denominator-clearing reduction of rational linear equality systems to
`Cslib.Complexity.LPFeasibility` (`ratEqSystemToLP`), and NP-completeness (under standard Lean
axioms) on multi-tape Turing machines for **Sparse Linear System (`SparseLinearSystem`)**: deciding
whether `A z = b` admits a rational solution `z ∈ ℚ^n` with `‖z‖₀ ≤ t`.

## Main definitions

- `CslibFrontier.Computability.Complexity.bitsCountTrue`,
  `CslibFrontier.Computability.Complexity.ratEqSystemToLP`: bitstring weight and rational-equality
  to integer-LP compiler.
- `CslibFrontier.Computability.Complexity.matEntry`,
  `CslibFrontier.Computability.Complexity.vecEntry`: rational matrix/vector accessors.
- `CslibFrontier.Computability.Complexity.SparseLinearSystemInstance`,
  `CslibFrontier.Computability.Complexity.SparseLinearSystem`: sparse linear system problem.

## Main results

- `CslibFrontier.Computability.Complexity.mem_NP_of_boundedBits_NP`,
  `CslibFrontier.Computability.Complexity.ratEqSystemToLP_mem_LPFeasibility_iff`.
- `CslibFrontier.Computability.Complexity.SparseLinearSystem.mem_NP`,
  `CslibFrontier.Computability.Complexity.SparseLinearSystem_npHard`,
  `CslibFrontier.Computability.Complexity.SparseLinearSystem_npComplete`.

## Tags

computational complexity, NP-completeness, sparse linear systems, linear programming feasibility
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Bounded-Mask Existential Closure of `NP` and Rational Equality Systems -/

private lemma poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial d c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h d)

/-- Count `true` bits of a raw bitstring in unary polynomial time. -/
@[expose]
def bitsCountTrue (w : List Bool) : ℕ :=
  (List.range w.length).countP fun i ↦ w.getD i false

theorem bitsCountTrue_eq (w : List Bool) :
    bitsCountTrue w = w.countP (· = true) := by
  unfold bitsCountTrue
  have hrec : ∀ l : List Bool, ((List.range l.length).countP fun i ↦ l.getD i false) =
      l.countP (· = true) := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
        List.countP_cons]
      simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
      rw [ih]
      cases b <;> simp [Nat.add_comm]
  exact hrec w

@[fun_prop]
theorem computableInPolyTime_bitsCountTrue :
    ComputableInPolyTime bitsCountTrue encBits encUnary := by
  unfold bitsCountTrue
  exact countPWithInput (ComputableInPolyTime.range.comp length_bits)
    (bitsGetDWithInput (fst _ _) (snd _ _) false)

/-- Existential quantification over a bitstring of unary-computable length preserves `NP`
membership. -/
theorem mem_NP_of_boundedBits_NP {α : Type} {encA : α ↪ List Bool}
    {maskLen : α → ℕ} (hm : ComputableInPolyTime maskLen encA encUnary)
    {S : Set (α × List Bool)} (hS : S ∈ NP (encPair encA encBits)) :
    {x : α | ∃ m : List Bool, m.length = maskLen x ∧ (x, m) ∈ S} ∈ NP encA := by
  obtain ⟨pS, W, hW, hWS⟩ := Cslib.Complexity.mem_NP.mp hS
  obtain ⟨q, hq⟩ := hm.polyBounded_length.exists_polynomial
  have hm_le : ∀ x : α, maskLen x ≤ q.eval (encA x).length := by
    intro x
    simpa [encUnary_apply] using hq x
  let certLenS (x : α) (m : List Bool) : ℕ := pS.eval (encPair encA encBits (x, m)).length
  have hcertLenS : ComputableInPolyTime (fun p : α × List Bool ↦ certLenS p.1 p.2)
      (encPair encA encBits) encUnary :=
    (unary_eval pS).comp (encoding_length (encPair encA encBits))
  let V (p : α × List Bool) : Bool :=
    let x := p.1
    let w := p.2
    let k1 := maskLen x
    let m := w.take k1
    let rest := w.drop k1
    let k2 := certLenS x m
    decide (k1 ≤ w.length) && decide (k2 ≤ rest.length) && W ((x, m), rest.take k2)
  have hV : ComputableInPolyTime V (encPair encA encBits) encBool := by
    let E := encPair encA encBits
    have hx : ComputableInPolyTime (fun p : α × List Bool ↦ p.1) E encA := fst _ _
    have hw : ComputableInPolyTime (fun p : α × List Bool ↦ p.2) E encBits := snd _ _
    have hk1 : ComputableInPolyTime (fun p : α × List Bool ↦ maskLen p.1) E encUnary :=
      hm.comp hx
    have hm_take : ComputableInPolyTime
        (fun p : α × List Bool ↦ p.2.take (maskLen p.1)) E encBits :=
      bitsTakeWithInput hw hk1
    have hrest : ComputableInPolyTime
        (fun p : α × List Bool ↦ p.2.drop (maskLen p.1)) E encBits :=
      bitsDropWithInput hw hk1
    have hk2 : ComputableInPolyTime
        (fun p : α × List Bool ↦ certLenS p.1 (p.2.take (maskLen p.1))) E encUnary :=
      hcertLenS.comp (hx.prod hm_take)
    have hu : ComputableInPolyTime
        (fun p : α × List Bool ↦
          (p.2.drop (maskLen p.1)).take (certLenS p.1 (p.2.take (maskLen p.1))))
        E encBits :=
      bitsTakeWithInput hrest hk2
    unfold V
    dsimp only
    exact bool_and'
      (bool_and'
        (binary_le' (unary_to_binary.comp hk1)
          (unary_to_binary.comp (length_bits_comp hw)))
        (binary_le' (unary_to_binary.comp hk2)
          (unary_to_binary.comp (length_bits_comp hrest))))
      (hW.comp ((hx.prod hm_take).prod hu))
  let P_tot : Polynomial ℕ := q + pS.comp (2 * Polynomial.X + q + 2)
  refine Cslib.Complexity.mem_NP.mpr ⟨P_tot, V, hV, ?_⟩
  refine IsVerifier.of_padding (fun x w _ hVw ↦ ?_) (fun x ⟨m, hmlen, hmS⟩ ↦ ?_)
  · unfold V at hVw
    dsimp only at hVw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hVw
    rcases hVw with ⟨⟨hk1_le, hk2_le⟩, hW_acc⟩
    set m := w.take (maskLen x)
    have hmlen : m.length = maskLen x := List.length_take_of_le hk1_le
    set u := (w.drop (maskLen x)).take (certLenS x m)
    have hulen : u.length = certLenS x m := List.length_take_of_le hk2_le
    exact ⟨m, hmlen, (hWS (x, m)).mpr ⟨u, hulen, hW_acc⟩⟩
  · obtain ⟨u, hulen, hW_acc⟩ := (hWS (x, m)).mp hmS
    have hulen' : u.length = certLenS x m := hulen
    refine ⟨m ++ u, ?_, fun pad ↦ ?_⟩
    · simp only [List.length_append, hmlen, hulen, P_tot, Polynomial.eval_add,
        Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      have hpair_le :
          (encPair encA encBits (x, m)).length ≤
            2 * (encA x).length + q.eval (encA x).length + 2 := by
        have h1 := hm_le x
        rw [length_encPair]
        dsimp only
        rw [encBits_apply, hmlen]
        omega
      exact Nat.add_le_add (hm_le x) (poly_eval_mono pS hpair_le)
    · unfold V
      dsimp only
      rw [List.append_assoc]
      have htake1 : (m ++ (u ++ List.replicate pad false)).take (maskLen x) = m := by
        rw [← hmlen, List.take_left]
      have hdrop1 : (m ++ (u ++ List.replicate pad false)).drop (maskLen x) =
          u ++ List.replicate pad false := by
        rw [← hmlen, List.drop_left]
      rw [htake1, hdrop1]
      have htake2 : (u ++ List.replicate pad false).take (certLenS x m) = u := by
        rw [← hulen', List.take_left]
      rw [htake2]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, ?_⟩, hW_acc⟩
      · rw [List.length_append, hmlen]; omega
      · rw [List.length_append, hulen']; omega

private def eqRowDenom (row : List ℚ) (rhs : ℚ) : ℕ :=
  ((rhs :: row).map Rat.den).prod

private lemma eqRowDenom_pos (row : List ℚ) (rhs : ℚ) : 0 < eqRowDenom row rhs :=
  List.prod_pos fun _ hd ↦ by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    exact q.pos

private def scaleRatEntry (D : ℕ) (q : ℚ) : ℤ :=
  q.num * ((D / q.den : ℕ) : ℤ)

private lemma cast_scaleRatEntry {D : ℕ} {q : ℚ} (hdvd : q.den ∣ D) :
    ((scaleRatEntry D q : ℤ) : ℚ) = (D : ℚ) * q :=
  (Rat.clearDenom_entry hdvd).symm

private def eqPairToLP (p : List ℚ × ℚ) : List LinearInequality :=
  let D := eqRowDenom p.1 p.2
  let coeffs := p.1.map (scaleRatEntry D)
  let b := scaleRatEntry D p.2
  [⟨coeffs, b⟩, ⟨coeffs.map (-·), -b⟩]

/-- Convert a list of rational linear equations `(row, rhs)` into an equivalent integer linear
inequality system for `LPFeasibility`. -/
def ratEqSystemToLP (eqs : List (List ℚ × ℚ)) : List LinearInequality :=
  (eqs.map eqPairToLP).flatten

private lemma encLinearInequality_mk_poly :
    ComputableInPolyTime (fun p : List ℤ × ℤ ↦ LinearInequality.mk p.1 p.2)
      (encPair (encList encIntBin) encIntBin) encLinearInequality :=
  (ComputableInPolyTime.id' (encIn := encPair (encList encIntBin) encIntBin)).of_enc_eq
    fun p ↦ (encLinearInequality_apply ⟨p.1, p.2⟩).symm

@[fun_prop]
theorem computableInPolyTime_ratEqSystemToLP :
    ComputableInPolyTime ratEqSystemToLP
      (encList (encPair (encList encRat) encRat)) LPFeasibility.encSystem := by
  have hpair : ComputableInPolyTime eqPairToLP
      (encPair (encList encRat) encRat) (encList encLinearInequality) := by
    let E := encPair (encList encRat) encRat
    have hrow : ComputableInPolyTime (fun p : List ℚ × ℚ ↦ p.1) E (encList encRat) := fst _ _
    have hD : ComputableInPolyTime (fun p : List ℚ × ℚ ↦ eqRowDenom p.1 p.2) E encNat := by
      unfold eqRowDenom
      fun_prop
    have hcoeffs : ComputableInPolyTime
        (fun p : List ℚ × ℚ ↦ p.1.map (scaleRatEntry (eqRowDenom p.1 p.2)))
        E (encList encIntBin) := by
      refine mapWithInput hrow ?_
      unfold scaleRatEntry
      fun_prop
    have hb : ComputableInPolyTime
        (fun p : List ℚ × ℚ ↦ scaleRatEntry (eqRowDenom p.1 p.2) p.2) E encIntBin := by
      unfold scaleRatEntry
      fun_prop
    have hnegCoeffs : ComputableInPolyTime
        (fun p : List ℚ × ℚ ↦ (p.1.map (scaleRatEntry (eqRowDenom p.1 p.2))).map (-·))
        E (encList encIntBin) :=
      mapWithInput hcoeffs (by fun_prop)
    have h1 : ComputableInPolyTime
        (fun p : List ℚ × ℚ ↦
          LinearInequality.mk (p.1.map (scaleRatEntry (eqRowDenom p.1 p.2)))
            (scaleRatEntry (eqRowDenom p.1 p.2) p.2))
        E encLinearInequality := encLinearInequality_mk_poly.comp (hcoeffs.prod hb)
    have h2 : ComputableInPolyTime
        (fun p : List ℚ × ℚ ↦
          LinearInequality.mk ((p.1.map (scaleRatEntry (eqRowDenom p.1 p.2))).map (-·))
            (-scaleRatEntry (eqRowDenom p.1 p.2) p.2))
        E encLinearInequality := encLinearInequality_mk_poly.comp (hnegCoeffs.prod (by fun_prop))
    unfold eqPairToLP
    dsimp only
    exact cons' h1 (cons' h2 (const []))
  unfold ratEqSystemToLP
  exact (ComputableInPolyTime.flatten encLinearInequality).comp
    (mapWithInput id' (hpair.comp (snd _ _)))

/-- `ratEqSystemToLP eqs` belongs to `LPFeasibility` iff all rational linear equations in `eqs`
share a common rational solution `z : ℕ → ℚ`. -/
theorem ratEqSystemToLP_mem_LPFeasibility_iff (eqs : List (List ℚ × ℚ)) :
    ratEqSystemToLP eqs ∈ LPFeasibility ↔
      ∃ z : ℕ → ℚ, ∀ p ∈ eqs,
        ∑ j ∈ Finset.range p.1.length, p.1.getD j 0 * z j = p.2 := by
  simp only [LPFeasibility, ratEqSystemToLP, Set.mem_ofPred_eq, List.mem_flatten, List.mem_map]
  refine exists_congr fun z ↦ ⟨fun h p hp ↦ ?_, fun h c hmem_c ↦ ?_⟩
  · let D := eqRowDenom p.1 p.2
    have hD_pos : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr (eqRowDenom_pos p.1 p.2)
    have hdvd_rhs : p.2.den ∣ D :=
      List.dvd_prod (List.mem_map.mpr ⟨p.2, List.mem_cons_self, rfl⟩)
    have hdvd_row : ∀ j < p.1.length, (p.1.getD j 0).den ∣ D := by
      intro j hj
      rw [List.getD_eq_getElem p.1 0 hj]
      exact List.dvd_prod
        (List.mem_map.mpr ⟨p.1[j], List.mem_cons_of_mem _ (List.getElem_mem hj), rfl⟩)
    let cPos : LinearInequality := ⟨p.1.map (scaleRatEntry D), scaleRatEntry D p.2⟩
    let cNeg : LinearInequality := ⟨(p.1.map (scaleRatEntry D)).map (-·), -scaleRatEntry D p.2⟩
    have hPos := h cPos ⟨eqPairToLP p, ⟨p, hp, rfl⟩, by simp [eqPairToLP, D, cPos]⟩
    have hNeg := h cNeg ⟨eqPairToLP p, ⟨p, hp, rfl⟩, by simp [eqPairToLP, D, cNeg]⟩
    have hsum_pos :
        ∑ j ∈ Finset.range cPos.coeffs.length, (cPos.coeffs.getD j 0 : ℚ) * z j =
          (D : ℚ) * ∑ j ∈ Finset.range p.1.length, p.1.getD j 0 * z j := by
      change ∑ j ∈ Finset.range (p.1.map (scaleRatEntry D)).length,
          ((p.1.map (scaleRatEntry D)).getD j 0 : ℚ) * z j = _
      rw [List.length_map, mul_sum]
      refine sum_congr rfl fun j hj ↦ ?_
      have hj' : j < p.1.length := Finset.mem_range.mp hj
      have hget : (p.1.map (scaleRatEntry D)).getD j 0 = scaleRatEntry D (p.1.getD j 0) := by
        simp [List.getD_eq_getElem?_getD, hj']
      rw [hget, cast_scaleRatEntry (hdvd_row j hj'), mul_assoc]
    have hsum_neg :
        ∑ j ∈ Finset.range cNeg.coeffs.length, (cNeg.coeffs.getD j 0 : ℚ) * z j =
          -((D : ℚ) * ∑ j ∈ Finset.range p.1.length, p.1.getD j 0 * z j) := by
      change ∑ j ∈ Finset.range ((p.1.map (scaleRatEntry D)).map (-·)).length,
          (((p.1.map (scaleRatEntry D)).map (-·)).getD j 0 : ℚ) * z j = _
      rw [List.length_map, List.length_map, ← hsum_pos]
      change _ = -(∑ j ∈ Finset.range (p.1.map (scaleRatEntry D)).length,
          ((p.1.map (scaleRatEntry D)).getD j 0 : ℚ) * z j)
      rw [List.length_map, ← sum_neg_distrib]
      refine sum_congr rfl fun j hj ↦ ?_
      have hj' : j < p.1.length := Finset.mem_range.mp hj
      have hget1 : ((p.1.map (scaleRatEntry D)).map (-·)).getD j 0 =
          -((p.1.map (scaleRatEntry D)).getD j 0) := by
        simp [List.getD_eq_getElem?_getD, hj']
      rw [hget1, Int.cast_neg, neg_mul]
    have hrhs_eq : (cPos.bound : ℚ) = (D : ℚ) * p.2 :=
      cast_scaleRatEntry hdvd_rhs
    have hrhs_neg : (cNeg.bound : ℚ) = -((D : ℚ) * p.2) := by
      change ((-scaleRatEntry D p.2 : ℤ) : ℚ) = -((D : ℚ) * p.2)
      rw [Int.cast_neg, cast_scaleRatEntry hdvd_rhs]
    rw [hsum_pos, hrhs_eq] at hPos
    rw [hsum_neg, hrhs_neg] at hNeg
    have hmul_eq : (D : ℚ) * ∑ j ∈ Finset.range p.1.length, p.1.getD j 0 * z j = (D : ℚ) * p.2 := by
      linarith
    exact mul_left_cancel₀ hD_pos.ne' hmul_eq
  · obtain ⟨l, ⟨p, hp, rfl⟩, hc⟩ := hmem_c
    let D := eqRowDenom p.1 p.2
    have hdvd_rhs : p.2.den ∣ D :=
      List.dvd_prod (List.mem_map.mpr ⟨p.2, List.mem_cons_self, rfl⟩)
    have hdvd_row : ∀ j < p.1.length, (p.1.getD j 0).den ∣ D := by
      intro j hj
      rw [List.getD_eq_getElem p.1 0 hj]
      exact List.dvd_prod
        (List.mem_map.mpr ⟨p.1[j], List.mem_cons_of_mem _ (List.getElem_mem hj), rfl⟩)
    have heq := h p hp
    simp only [eqPairToLP, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp only [List.length_map]
      have hsum :
          ∑ j ∈ Finset.range p.1.length,
            ((p.1.map (scaleRatEntry D)).getD j 0 : ℚ) * z j =
          (D : ℚ) * ∑ j ∈ Finset.range p.1.length, p.1.getD j 0 * z j := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj ↦ ?_
        have hj' : j < p.1.length := Finset.mem_range.mp hj
        have hget : (p.1.map (scaleRatEntry D)).getD j 0 = scaleRatEntry D (p.1.getD j 0) := by
          simp [List.getD_eq_getElem?_getD, hj']
        rw [hget, cast_scaleRatEntry (hdvd_row j hj'), mul_assoc]
      rw [hsum, heq, cast_scaleRatEntry hdvd_rhs]
    · simp only [List.length_map, Int.cast_neg]
      have hsum :
          ∑ j ∈ Finset.range p.1.length,
            (((p.1.map (scaleRatEntry D)).map (-·)).getD j 0 : ℚ) * z j =
          -((D : ℚ) * ∑ j ∈ Finset.range p.1.length, p.1.getD j 0 * z j) := by
        rw [mul_sum, ← sum_neg_distrib]
        refine sum_congr rfl fun j hj ↦ ?_
        have hj' : j < p.1.length := Finset.mem_range.mp hj
        have hget : ((p.1.map (scaleRatEntry D)).map (-·)).getD j 0 =
            -(scaleRatEntry D (p.1.getD j 0)) := by
          simp [List.getD_eq_getElem?_getD, hj']
        rw [hget, Int.cast_neg, neg_mul, cast_scaleRatEntry (hdvd_row j hj'), mul_assoc]
      rw [hsum, heq, cast_scaleRatEntry hdvd_rhs]

/-! ### 2. Matrix/Vector Accessors and `SparseLinearSystem` -/

/-- Entry `(i, j)` of a rational matrix `mat`, defaulting to `0` out of bounds. -/
@[expose]
def matEntry (mat : List (List ℚ)) (i j : ℕ) : ℚ :=
  (mat.getD i []).getD j 0

/-- Entry `i` of a rational vector `v`, defaulting to `0` out of bounds. -/
@[expose]
def vecEntry (v : List ℚ) (i : ℕ) : ℚ :=
  v.getD i 0

@[fun_prop]
theorem computableInPolyTime_matEntry_unary {α : Type} {enc : α ↪ List Bool}
    {mat : α → List (List ℚ)} {i j : α → ℕ}
    (hm : ComputableInPolyTime mat enc (encList (encList encRat)))
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a ↦ matEntry (mat a) (i a) (j a)) enc encRat :=
  listGetDWithInput (listGetDWithInput hm hi ([] : List ℚ)) hj (0 : ℚ)

@[fun_prop]
theorem computableInPolyTime_vecEntry_unary {α : Type} {enc : α ↪ List Bool}
    {v : α → List ℚ} {i : α → ℕ}
    (hv : ComputableInPolyTime v enc (encList encRat))
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun a ↦ vecEntry (v a) (i a)) enc encRat :=
  listGetDWithInput hv hi (0 : ℚ)

/-- An instance `(m, n, mat, rhs, budget)` of **Sparse Linear System**: an `m × n` rational matrix
`mat` (`m, n` in unary), length-`m` right-hand side `rhs`, and binary `ℓ₀` budget `budget`. -/
@[ext]
structure SparseLinearSystemInstance where
  /-- Number of equations (rows), encoded in unary. -/
  m : ℕ
  /-- Number of variables (columns), encoded in unary. -/
  n : ℕ
  /-- Explicit `m × n` rational coefficient matrix `A`. -/
  mat : List (List ℚ)
  /-- Rational right-hand side vector `b`. -/
  rhs : List ℚ
  /-- Sparsity budget `t` (`‖z‖₀ ≤ t`), encoded in binary. -/
  budget : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `SparseLinearSystemInstance`. -/
enc_structure encSparseLinearSystem : SparseLinearSystemInstance where
  m : encUnary,
  n : encUnary,
  mat : (encList (encList encRat)),
  rhs : (encList encRat),
  budget : encNat

attribute [fun_prop] encSparseLinearSystem_m_polyTime encSparseLinearSystem_n_polyTime
  encSparseLinearSystem_mat_polyTime encSparseLinearSystem_rhs_polyTime
  encSparseLinearSystem_budget_polyTime encSparseLinearSystem_mk_polyTime

/-- **Sparse Linear System**: instances admitting `z : Fin n → ℚ` with `A z = b` and `‖z‖₀ ≤ t`. -/
@[expose]
def SparseLinearSystem : Set SparseLinearSystemInstance :=
  {x | ∃ z : Fin x.n → ℚ,
    (∀ i : Fin x.m, ∑ j : Fin x.n, matEntry x.mat i.1 j.1 * z j = vecEntry x.rhs i.1) ∧
    (univ.filter fun j : Fin x.n ↦ z j ≠ 0).card ≤ x.budget}

namespace SparseLinearSystem

private def maskEqs (x : SparseLinearSystemInstance) (mask : List Bool) : List (List ℚ × ℚ) :=
  ((List.range x.m).map fun i ↦
    ((List.range x.n).map (fun j ↦ matEntry x.mat i j), vecEntry x.rhs i)) ++
  ((List.range x.n).map fun j ↦
    ((List.range x.n).map (fun l ↦
      if !mask.getD j false && decide (l = j) then (1 : ℚ) else 0), (0 : ℚ)))

private def maskGuard (p : SparseLinearSystemInstance × List Bool) : Bool :=
  decide (bitsCountTrue p.2 ≤ p.1.budget)

private theorem computableInPolyTime_maskEqs :
    ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ maskEqs p.1 p.2)
      (encPair encSparseLinearSystem encBits)
      (encList (encPair (encList encRat) encRat)) := by
  let E := encPair encSparseLinearSystem encBits
  have hx : ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ p.1)
      E encSparseLinearSystem := fst _ _
  have hmask : ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ p.2)
      E encBits := snd _ _
  have hm : ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ p.1.m)
      E encUnary := encSparseLinearSystem_m_polyTime hx
  have hn : ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ p.1.n)
      E encUnary := encSparseLinearSystem_n_polyTime hx
  have hmat : ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ p.1.mat)
      E (encList (encList encRat)) := encSparseLinearSystem_mat_polyTime hx
  have hrhs : ComputableInPolyTime (fun p : SparseLinearSystemInstance × List Bool ↦ p.1.rhs)
      E (encList encRat) := encSparseLinearSystem_rhs_polyTime hx
  have hpart1 : ComputableInPolyTime
      (fun p : SparseLinearSystemInstance × List Bool ↦
        (List.range p.1.m).map fun i ↦
          ((List.range p.1.n).map (fun j ↦ matEntry p.1.mat i j), vecEntry p.1.rhs i))
      E (encList (encPair (encList encRat) encRat)) := by
    refine mapWithInput (ComputableInPolyTime.range.comp hm) ?_
    refine (mapWithInput (ComputableInPolyTime.range.comp (hn.comp (fst _ _))) ?_).prod
      (computableInPolyTime_vecEntry_unary (hrhs.comp (fst _ _)) (snd _ _))
    exact computableInPolyTime_matEntry_unary
      (hmat.comp ((fst _ _).comp (fst _ _)))
      ((snd _ _).comp (fst _ _)) (snd _ _)
  have hpart2 : ComputableInPolyTime
      (fun p : SparseLinearSystemInstance × List Bool ↦
        (List.range p.1.n).map fun j ↦
          ((List.range p.1.n).map (fun l ↦
            if !p.2.getD j false && decide (l = j) then (1 : ℚ) else 0), (0 : ℚ)))
      E (encList (encPair (encList encRat) encRat)) := by
    refine mapWithInput (ComputableInPolyTime.range.comp hn) ?_
    refine (mapWithInput (ComputableInPolyTime.range.comp (hn.comp (fst _ _))) ?_).prod
      (const (0 : ℚ))
    have hbit : ComputableInPolyTime
        (fun q : ((SparseLinearSystemInstance × List Bool) × ℕ) × ℕ ↦
          !q.1.1.2.getD q.1.2 false)
        (encPair (encPair E encUnary) encUnary) encBool :=
      bool_not.comp (bitsGetDWithInput (hmask.comp ((fst _ _).comp (fst _ _)))
        ((snd _ _).comp (fst _ _)) false)
    exact ite' (bool_and' hbit (decide_eq' (snd _ _) ((snd _ _).comp (fst _ _))))
      (const (1 : ℚ)) (const (0 : ℚ))
  unfold maskEqs
  exact listAppend' hpart1 hpart2

/-- `SparseLinearSystem` belongs to `NP`. -/
theorem mem_NP : SparseLinearSystem ∈ NP encSparseLinearSystem := by
  let S : Set (SparseLinearSystemInstance × List Bool) :=
    {p | maskGuard p = true ∧ ratEqSystemToLP (maskEqs p.1 p.2) ∈ LPFeasibility}
  have hLP_pull :
      {p : SparseLinearSystemInstance × List Bool |
        ratEqSystemToLP (maskEqs p.1 p.2) ∈ LPFeasibility} ∈
      NP (encPair encSparseLinearSystem encBits) :=
    PolyTimeReducible.mem_NP
      ⟨fun p ↦ ratEqSystemToLP (maskEqs p.1 p.2),
        computableInPolyTime_ratEqSystemToLP.comp computableInPolyTime_maskEqs,
        fun _ ↦ Iff.rfl⟩
      LPFeasibility.mem_NP
  have hS_NP : S ∈ NP (encPair encSparseLinearSystem encBits) :=
    mem_NP_of_guard
      (binary_le'
        (unary_to_binary.comp (computableInPolyTime_bitsCountTrue.comp (snd _ _)))
        (encSparseLinearSystem_budget_polyTime (fst _ _)))
      hLP_pull fun _ ↦ Iff.rfl
  have hExt : SparseLinearSystem =
      {x | ∃ m : List Bool, m.length = x.n ∧ (x, m) ∈ S} := by
    ext x
    simp only [SparseLinearSystem, S, maskGuard, Set.mem_ofPred_eq, decide_eq_true_eq,
      ratEqSystemToLP_mem_LPFeasibility_iff]
    constructor
    · rintro ⟨z, hAz, hcard⟩
      let m : List Bool := List.ofFn fun j : Fin x.n ↦ decide (z j ≠ 0)
      refine ⟨m, List.length_ofFn, ?_, ?_⟩
      · rw [bitsCountTrue_eq]
        have hrec : ∀ (n : ℕ) (f : Fin n → Bool),
            ((List.ofFn f).countP (· = true)) = ∑ j : Fin n, if f j = true then 1 else 0 := by
          intro n f
          induction n with
          | zero => simp
          | succ n ih =>
            rw [List.ofFn_succ, List.countP_cons, ih, Fin.sum_univ_succ]
            cases f 0 <;> simp [Nat.add_comm]
        have hcnt : m.countP (· = true) = (univ.filter fun j : Fin x.n ↦ z j ≠ 0).card := by
          dsimp [m]
          rw [hrec]
          simp only [decide_eq_true_eq, sum_boole, Nat.cast_id]
        rw [hcnt]
        exact hcard
      · refine ⟨fun j ↦ if hj : j < x.n then z ⟨j, hj⟩ else 0, fun p hp ↦ ?_⟩
        simp only [maskEqs, List.mem_append, List.mem_map, List.mem_range] at hp
        rcases hp with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · simp only [List.length_map, List.length_range]
          rw [← Fin.sum_univ_eq_sum_range (fun l ↦
            ((List.range x.n).map (fun j' ↦ matEntry x.mat i j')).getD l 0 *
              if hl : l < x.n then z ⟨l, hl⟩ else 0)]
          have hcongr : ∀ l : Fin x.n,
              ((List.range x.n).map (fun j' ↦ matEntry x.mat i j')).getD l.1 0 *
                (if hl : l.1 < x.n then z ⟨l.1, hl⟩ else 0) =
              matEntry x.mat i l.1 * z l := by
            intro l
            simp [List.getD_eq_getElem?_getD, l.2]
          rw [sum_congr rfl fun l _ ↦ hcongr l]
          exact hAz ⟨i, hi⟩
        · simp only [List.length_map, List.length_range]
          refine sum_eq_zero fun l hl ↦ ?_
          have hl' : l < x.n := Finset.mem_range.mp hl
          have hget : ((List.range x.n).map (fun l' ↦
              if !m.getD j false && decide (l' = j) then (1 : ℚ) else 0)).getD l 0 =
              if !m.getD j false && decide (l = j) then (1 : ℚ) else 0 := by
            simp [List.getD_eq_getElem?_getD, hl']
          rw [hget]
          simp only [hl', ↓reduceDIte]
          by_cases hlj : l = j
          · subst hlj
            have hmget : m.getD l false = decide (z ⟨l, hl'⟩ ≠ 0) := by
              simp [m, List.getD_eq_getElem?_getD, hl']
            rw [hmget]
            by_cases hznz : z ⟨l, hl'⟩ = 0 <;> simp [hznz]
          · simp [hlj]
    · rintro ⟨m, hmlen, hbudget, z, hz⟩
      refine ⟨fun j ↦ z j.1, fun i ↦ ?_, ?_⟩
      · have hmem : ((List.range x.n).map (fun j ↦ matEntry x.mat i.1 j), vecEntry x.rhs i.1) ∈
            maskEqs x m := by
          simp only [maskEqs, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inl ⟨i.1, i.2, rfl⟩
        have hrow := hz _ hmem
        simp only [List.length_map, List.length_range] at hrow
        rw [← hrow, ← Fin.sum_univ_eq_sum_range (fun j ↦
          ((List.range x.n).map (fun j' ↦ matEntry x.mat i.1 j')).getD j 0 * z j)]
        refine sum_congr rfl fun j _ ↦ ?_
        simp [List.getD_eq_getElem?_getD, j.2]
      · have hzero_of_false : ∀ j : Fin x.n, m.getD j.1 false = false → z j.1 = 0 := by
          intro j hmf
          have hmem : ((List.range x.n).map (fun l ↦
              if !m.getD j.1 false && decide (l = j.1) then (1 : ℚ) else 0), (0 : ℚ)) ∈
              maskEqs x m := by
            simp only [maskEqs, List.mem_append, List.mem_map, List.mem_range]
            exact Or.inr ⟨j.1, j.2, rfl⟩
          have hrow := hz _ hmem
          simp only [List.length_map, List.length_range, hmf, Bool.not_false, Bool.true_and] at hrow
          rw [← Fin.sum_univ_eq_sum_range (fun l ↦
            ((List.range x.n).map (fun l' ↦ if decide (l' = j.1) then (1 : ℚ) else 0)).getD l 0 *
              z l)] at hrow
          have hterm : ∀ l : Fin x.n,
              ((List.range x.n).map (fun l' ↦ if decide (l' =
                j.1) then (1 : ℚ) else 0)).getD l.1 0 *
                z l.1 = if l = j then z j.1 else 0 := by
            intro l
            simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range l.2,
              Option.map_some, Option.getD_some, decide_eq_true_eq]
            by_cases hlj : l = j
            · subst hlj; simp
            · have hne : l.1 ≠ j.1 := fun h ↦ hlj (Fin.ext h)
              simp [hne, hlj]
          rw [sum_congr rfl fun l _ ↦ hterm l] at hrow
          simpa only [sum_ite_eq', mem_univ, ↓reduceIte] using hrow
        have hsub_cnt :
            (univ.filter fun j : Fin x.n ↦ z j.1 ≠ 0).card ≤ bitsCountTrue m := by
          unfold bitsCountTrue
          rw [hmlen]
          have hcnt_sum : ((List.range x.n).countP fun i ↦ m.getD i false) =
              (univ.filter fun j : Fin x.n ↦ m.getD j.1 false = true).card := by
            have hrec : ∀ (k : ℕ) (p : ℕ → Bool),
                (List.range k).countP p = (Finset.range k |>.filter fun i ↦ p i = true).card := by
              intro k p
              induction k with
              | zero => simp
              | succ k ih =>
                rw [List.range_succ, List.countP_append, ih, Finset.range_add_one,
                  Finset.filter_insert]
                cases hk : p k <;> simp [hk, Nat.add_comm]
            rw [hrec]
            refine Finset.card_bij (fun i hi ↦ ⟨i, Finset.mem_range.mp (mem_filter.mp hi).1⟩)
              (fun i hi ↦ mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩)
              (fun _ _ _ _ h ↦ congrArg Fin.val h)
              (fun j hj ↦ ⟨j.1, mem_filter.mpr ⟨Finset.mem_range.mpr j.2, (mem_filter.mp hj).2⟩,
                Fin.eta j j.2⟩)
          rw [hcnt_sum]
          refine card_le_card fun j hj ↦ ?_
          rw [mem_filter] at hj ⊢
          refine ⟨mem_univ _, ?_⟩
          cases hmb : m.getD j.1 false
          · exact (hj.2 (hzero_of_false j hmb)).elim
          · rfl
        exact hsub_cnt.trans hbudget
  rw [hExt]
  exact mem_NP_of_boundedBits_NP (encSparseLinearSystem_n_polyTime id') hS_NP

/-! #### Reduction from `ThreeExactCover` to `SparseLinearSystem` -/

private def slsDedupNat (S : List ℕ) : List ℕ :=
  selectDistinct S (List.replicate S.length true)

private lemma mem_slsDedupNat {S : List ℕ} {u : ℕ} : u ∈ slsDedupNat S ↔ u ∈ S :=
  mem_selectDistinct_replicate

private lemma nodup_slsDedupNat (S : List ℕ) : (slsDedupNat S).Nodup :=
  nodup_selectDistinct _ _

@[local fun_prop]
private theorem computableInPolyTime_slsDedupNat :
    ComputableInPolyTime slsDedupNat (encList encNat) (encList encNat) := by
  unfold slsDedupNat
  fun_prop

private def slsIsTriple (S : List ℕ) : Bool :=
  (S.length == 3) && (S.getD 0 0 != S.getD 1 0) && (S.getD 0 0 != S.getD 2 0) &&
    (S.getD 1 0 != S.getD 2 0)

private lemma slsIsTriple_iff (S : List ℕ) :
    slsIsTriple S = true ↔ S.length = 3 ∧ S.Nodup := by
  rcases S with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  all_goals simp [slsIsTriple, List.getD, List.nodup_cons, and_assoc, and_left_comm, and_comm]

/-- Fixed accepted `SparseLinearSystem` instance (`0 × 0`). -/
def yesInstance : SparseLinearSystemInstance := ⟨0, 0, [], [], 0⟩

/-- Fixed rejected `SparseLinearSystem` instance (`0 * z = 1`). -/
def noInstance : SparseLinearSystemInstance := ⟨1, 0, [[]], [1], 0⟩

private theorem yesInstance_mem : yesInstance ∈ SparseLinearSystem :=
  ⟨Fin.elim0, fun i ↦ Fin.elim0 i, le_trans (card_le_univ _) (by decide)⟩

private theorem noInstance_notMem : noInstance ∉ SparseLinearSystem := by
  rintro ⟨z, hz, _⟩
  have h0 := hz ⟨0, by decide⟩
  have hsum : (∑ j : Fin noInstance.n, matEntry noInstance.mat 0 j.1 * z j) = 0 :=
    sum_eq_zero fun j _ ↦ Fin.elim0 j
  rw [hsum] at h0
  simp [noInstance, vecEntry] at h0

/-- Polynomial-time reduction from `ThreeExactCover` to `SparseLinearSystem`. -/
def fromThreeExactCover (C : List (List ℕ)) : SparseLinearSystemInstance :=
  let U := slsDedupNat C.flatten
  if !(C.all slsIsTriple) then noInstance
  else if !(decide (U.length % 3 = 0)) then noInstance
  else
    let mat := (List.range U.length).map fun i ↦
      (List.range C.length).map fun j ↦
        if decide (U.getD i 0 ∈ C.getD j []) then (1 : ℚ) else 0
    let rhs := List.replicate U.length (1 : ℚ)
    ⟨U.length, C.length, mat, rhs, U.length / 3⟩

@[fun_prop]
theorem computableInPolyTime_fromThreeExactCover :
    ComputableInPolyTime fromThreeExactCover
      (encList (encList encNat)) encSparseLinearSystem := by
  let EC := encList (encList encNat)
  have hU : ComputableInPolyTime (fun C : List (List ℕ) ↦ slsDedupNat C.flatten)
      EC (encList encNat) :=
    computableInPolyTime_slsDedupNat.comp (ComputableInPolyTime.flatten encNat)
  have hu : ComputableInPolyTime (fun C : List (List ℕ) ↦ (slsDedupNat C.flatten).length)
      EC encUnary := (length_list encNat).comp hU
  have hu_bin : ComputableInPolyTime (fun C : List (List ℕ) ↦ (slsDedupNat C.flatten).length)
      EC encNat := unary_to_binary.comp hu
  have hc : ComputableInPolyTime (fun C : List (List ℕ) ↦ C.length) EC encUnary :=
    length_list (encList encNat)
  have hTriples : ComputableInPolyTime (fun C : List (List ℕ) ↦ !(C.all slsIsTriple))
      EC encBool := by
    unfold slsIsTriple
    fun_prop
  have hMod : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ !(decide ((slsDedupNat C.flatten).length % 3 = 0)))
      EC encBool :=
    bool_not.comp (decide_eq' (binary_mod' hu_bin (const 3)) (const 0))
  have hmat : ComputableInPolyTime
      (fun C : List (List ℕ) ↦
        (List.range (slsDedupNat C.flatten).length).map fun i ↦
          (List.range C.length).map fun j ↦
            if decide ((slsDedupNat C.flatten).getD i 0 ∈ C.getD j []) then (1 : ℚ) else 0)
      EC (encList (encList encRat)) := by
    refine mapWithInput (ComputableInPolyTime.range.comp hu) ?_
    refine mapWithInput (ComputableInPolyTime.range.comp (hc.comp (fst _ _))) ?_
    have hui : ComputableInPolyTime
        (fun q : (List (List ℕ) × ℕ) × ℕ ↦ (slsDedupNat q.1.1.flatten).getD q.1.2 0)
        (encPair (encPair EC encUnary) encUnary) encNat :=
      listGetDWithInput (hU.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _)) 0
    have hcj : ComputableInPolyTime
        (fun q : (List (List ℕ) × ℕ) × ℕ ↦ q.1.1.getD q.2 [])
        (encPair (encPair EC encUnary) encUnary) (encList encNat) :=
      listGetDWithInput ((fst _ _).comp (fst _ _)) (snd _ _) ([] : List ℕ)
    exact ite' (decide_mem hcj hui) (const (1 : ℚ)) (const (0 : ℚ))
  have hrhs : ComputableInPolyTime
      (fun C : List (List ℕ) ↦ List.replicate (slsDedupNat C.flatten).length (1 : ℚ))
      EC (encList encRat) :=
    ComputableInPolyTime.replicate hu (const (1 : ℚ))
  unfold fromThreeExactCover
  dsimp only
  exact ite' hTriples (const noInstance)
    (ite' hMod (const noInstance)
      (encSparseLinearSystem_mk_polyTime hu hc hmat hrhs (binary_div' hu_bin (const 3))))

private lemma pairwiseDisjoint_of_card_biUnion_eq_sum {α β : Type*} [DecidableEq β]
    {T : Finset α} {f : α → Finset β}
    (heq : (T.biUnion f).card = ∑ a ∈ T, (f a).card) :
    (T : Set α).PairwiseDisjoint f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha] at heq
    have hsub_le : (s.biUnion f).card ≤ ∑ b ∈ s, (f b).card := card_biUnion_le
    have hunion_le : (f a ∪ s.biUnion f).card ≤ (f a).card + (s.biUnion f).card := card_union_le _ _
    have hdisj_union : Disjoint (f a) (s.biUnion f) := by
      rw [← card_union_eq_card_add_card]
      omega
    have heq_s : (s.biUnion f).card = ∑ b ∈ s, (f b).card := by omega
    have hpw_s := ih heq_s
    intro x hx y hy hxy
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact Disjoint.mono_right (subset_biUnion_of_mem f hy) hdisj_union
    · exact (Disjoint.mono_right (subset_biUnion_of_mem f hx) hdisj_union).symm
    · exact hpw_s hx hy hxy

theorem fromThreeExactCover_mem_iff (C : List (List ℕ)) :
    fromThreeExactCover C ∈ SparseLinearSystem ↔ C ∈ ThreeExactCover := by
  let U := slsDedupNat C.flatten
  have hU_nd : U.Nodup := nodup_slsDedupNat _
  by_cases htr_b : C.all slsIsTriple = true
  · have htr : ∀ S ∈ C, S.length = 3 ∧ S.Nodup := by
      intro S hS
      exact (slsIsTriple_iff S).mp ((List.all_eq_true.mp htr_b) S hS)
    by_cases hmod : U.length % 3 = 0
    · let mat := (List.range U.length).map fun i ↦
        (List.range C.length).map fun j ↦
          if decide (U.getD i 0 ∈ C.getD j []) then (1 : ℚ) else 0
      let rhs := List.replicate U.length (1 : ℚ)
      have hfx : fromThreeExactCover C = ⟨U.length, C.length, mat, rhs, U.length / 3⟩ := by
        simp [fromThreeExactCover, U, mat, rhs, htr_b, hmod]
      rw [hfx]
      have hmat_entry : ∀ (i : Fin U.length) (j : Fin C.length),
          matEntry mat i.1 j.1 = if U[i.1]'i.2 ∈ C[j.1]'j.2 then 1 else 0 := by
        intro i j
        simp only [mat, matEntry, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range i.2, List.getElem?_range j.2, List.getElem?_eq_getElem i.2,
          List.getElem?_eq_getElem j.2, Option.map_some, Option.getD_some,
          decide_eq_true_eq]
      have hrhs_entry : ∀ i : Fin U.length, vecEntry rhs i.1 = 1 := by
        intro i
        simp [rhs, vecEntry, List.getD_eq_getElem?_getD, i.2]
      let q := U.length / 3
      have hu_eq : U.length = 3 * q := by omega
      let cover (j : Fin C.length) : Finset (Fin U.length) :=
        univ.filter fun i ↦ U[i.1]'i.2 ∈ C[j.1]'j.2
      have hcover_card : ∀ j : Fin C.length, (cover j).card = 3 := by
        intro j
        obtain ⟨hlen3, hndS⟩ := htr C[j.1] (List.getElem_mem j.2)
        have hS_sub_U : ∀ u ∈ C[j.1], u ∈ U := fun u hu ↦
          mem_slsDedupNat.mpr (List.mem_flatten.mpr ⟨C[j.1], List.getElem_mem j.2, hu⟩)
        have hbij : (cover j).card = (C[j.1]).toFinset.card := by
          refine Finset.card_bij (fun i _ ↦ U[i.1]'i.2)
            (fun i hi ↦ List.mem_toFinset.mpr (mem_filter.mp hi).2)
            (fun i₁ _ i₂ _ hEq ↦ by
              have h1 := hU_nd.idxOf_getElem i₁.1 i₁.2
              have h2 := hU_nd.idxOf_getElem i₂.1 i₂.2
              rw [hEq] at h1
              exact Fin.ext (h1.symm.trans h2))
            (fun u hu ↦ ?_)
          have huS : u ∈ C[j.1] := List.mem_toFinset.mp hu
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hS_sub_U u huS)
          exact ⟨⟨i, hi⟩, mem_filter.mpr ⟨mem_univ _, huS⟩, rfl⟩
        rw [hbij, List.toFinset_card_of_nodup hndS, hlen3]
      constructor
      · rintro ⟨z, hAz, hcard⟩
        dsimp only at z hAz hcard
        let T : Finset (Fin C.length) := univ.filter fun j ↦ z j ≠ 0
        have hT_le : T.card ≤ q := hcard
        have huniv_sub : (univ : Finset (Fin U.length)) ⊆ T.biUnion cover := by
          intro i _
          have hi_eq := hAz i
          rw [hrhs_entry i] at hi_eq
          by_contra hnot
          rw [mem_biUnion] at hnot
          push Not at hnot
          have h0 : ∑ j : Fin C.length, matEntry mat i.1 j.1 * z j = 0 := by
            refine sum_eq_zero fun j _ ↦ ?_
            rw [hmat_entry i j]
            by_cases hjT : j ∈ T
            · have hnotc : i ∉ cover j := hnot j hjT
              have hnot_mem : U[i.1] ∉ C[j.1] := fun h ↦ hnotc (mem_filter.mpr ⟨mem_univ _, h⟩)
              simp [hnot_mem]
            · have hz0 : z j = 0 := by simpa [T] using hjT
              rw [hz0, mul_zero]
          rw [h0] at hi_eq
          norm_num at hi_eq
        have hbi_eq : T.biUnion cover = univ := eq_univ_of_forall fun i ↦ huniv_sub (mem_univ i)
        have hbi_card : (T.biUnion cover).card = 3 * q := by
          rw [hbi_eq, card_univ, Fintype.card_fin, hu_eq]
        have hsum_T : ∑ j ∈ T, (cover j).card = 3 * T.card := by
          rw [sum_congr rfl fun j _ ↦ hcover_card j, sum_const, smul_eq_mul, mul_comm]
        have hbi_le := (card_biUnion_le (s := T) (t := cover))
        have hpw : (T : Set (Fin C.length)).PairwiseDisjoint cover :=
          pairwiseDisjoint_of_card_biUnion_eq_sum (by omega)
        let D : Finset (List ℕ) := T.image fun j : Fin C.length ↦ C[j.1]'j.2
        refine ⟨htr, D, fun S hS ↦ ?_, fun u hu ↦ ?_⟩
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hS
          exact List.getElem_mem j.2
        · obtain ⟨i_nat, hi_lt, rfl⟩ := List.getElem_of_mem (mem_slsDedupNat.mpr hu)
          let i : Fin U.length := ⟨i_nat, hi_lt⟩
          have hi_bi : i ∈ T.biUnion cover := hbi_eq ▸ mem_univ i
          obtain ⟨j₀, hj₀T, hi_j₀⟩ := mem_biUnion.mp hi_bi
          have hfilt_eq : D.filter (U[i.1] ∈ ·) = {C[j₀.1]'j₀.2} := by
            ext S
            simp only [D, mem_filter, mem_image, mem_singleton]
            constructor
            · rintro ⟨⟨j, hjT, rfl⟩, hui⟩
              have hij : i ∈ cover j := mem_filter.mpr ⟨mem_univ _, hui⟩
              have hjj₀ : j = j₀ := by
                by_contra hne
                exact Finset.disjoint_left.mp (hpw hjT hj₀T hne) hij hi_j₀
              subst hjj₀; rfl
            · rintro rfl
              exact ⟨⟨j₀, hj₀T, rfl⟩, (mem_filter.mp hi_j₀).2⟩
          rw [hfilt_eq, card_singleton]
      · rintro ⟨_, D, hDC, hexact⟩
        have h3D : 3 * D.card = U.length := by
          have hsum_U : ∑ u ∈ U.toFinset, (D.filter (u ∈ ·)).card = U.length := by
            have h1 : ∀ u ∈ U.toFinset, (D.filter (u ∈ ·)).card = 1 := fun u hu ↦
              hexact u (mem_slsDedupNat.mp (List.mem_toFinset.mp hu))
            rw [sum_congr rfl h1, sum_const, smul_eq_mul, mul_one,
              List.toFinset_card_of_nodup hU_nd]
          have hswap : ∑ u ∈ U.toFinset, (D.filter (u ∈ ·)).card =
              ∑ S ∈ D, (U.toFinset.filter (· ∈ S)).card := by
            simp only [card_filter]
            exact sum_comm
          have hsum_D : ∑ S ∈ D, (U.toFinset.filter (· ∈ S)).card = 3 * D.card := by
            have h3 : ∀ S ∈ D, (U.toFinset.filter (· ∈ S)).card = 3 := by
              intro S hSD
              obtain ⟨hlen3, hndS⟩ := htr S (hDC S hSD)
              have hfilt : U.toFinset.filter (· ∈ S) = S.toFinset := by
                ext u
                simp only [mem_filter, List.mem_toFinset]
                exact ⟨fun h ↦ h.2,
                  fun huS ↦ ⟨mem_slsDedupNat.mpr
                    (List.mem_flatten.mpr ⟨S, hDC S hSD, huS⟩), huS⟩⟩
              rw [hfilt, List.toFinset_card_of_nodup hndS, hlen3]
            rw [sum_congr rfl h3, sum_const, smul_eq_mul, mul_comm]
          omega
        have hD_eq_q : D.card = q := by omega
        let idxSet : Finset (Fin C.length) :=
          D.attach.image fun S ↦ ⟨C.idxOf S.1, List.idxOf_lt_length_iff.mpr (hDC S.1 S.2)⟩
        have hidx_card : idxSet.card ≤ D.card :=
          card_image_le.trans_eq card_attach
        refine ⟨fun j ↦ if j ∈ idxSet then 1 else 0, fun i ↦ ?_, ?_⟩
        · dsimp only at i ⊢
          rw [hrhs_entry i]
          have hu_mem : U[i.1] ∈ C.flatten := mem_slsDedupNat.mp (List.getElem_mem i.2)
          obtain ⟨S₀, hS₀_filt⟩ := card_eq_one.mp (hexact U[i.1] hu_mem)
          have hS₀_mem : S₀ ∈ D.filter (U[i.1] ∈ ·) := hS₀_filt.symm ▸ mem_singleton_self S₀
          have hS₀D : S₀ ∈ D := (mem_filter.mp hS₀_mem).1
          have huS₀ : U[i.1] ∈ S₀ := (mem_filter.mp hS₀_mem).2
          let j₀ : Fin C.length := ⟨C.idxOf S₀, List.idxOf_lt_length_iff.mpr (hDC S₀ hS₀D)⟩
          have hterm : ∀ j : Fin C.length,
              matEntry mat i.1 j.1 * (if j ∈ idxSet then (1 : ℚ) else 0) =
              if j = j₀ then 1 else 0 := by
            intro j
            rw [hmat_entry i j]
            by_cases hj : j ∈ idxSet
            · obtain ⟨⟨S, hSD⟩, _, hjEq⟩ := mem_image.mp hj
              have hCS : C[j.1] = S := by
                have hlt : C.idxOf S < C.length := List.idxOf_lt_length_iff.mpr (hDC S hSD)
                have hval : j.1 = C.idxOf S := (congrArg Fin.val hjEq).symm
                simp [hval, List.getElem_idxOf hlt]
              simp only [hj, ↓reduceIte, mul_one, hCS]
              by_cases huS : U[i.1] ∈ S
              · have hSS₀ : S = S₀ :=
                  mem_singleton.mp (hS₀_filt ▸ mem_filter.mpr ⟨hSD, huS⟩)
                subst hSS₀
                have hjj₀ : j = j₀ := hjEq.symm
                simp [huS, hjj₀]
              · have hne : j ≠ j₀ := by
                  intro hEq
                  apply huS
                  have : S = S₀ := by
                    rw [← hCS]
                    have hv : j.1 = C.idxOf S₀ := congrArg Fin.val hEq
                    simp [hv]
                  exact this ▸ huS₀
                simp [huS, hne]
            · have hne : j ≠ j₀ :=
                fun hEq ↦ hj (hEq ▸ mem_image.mpr ⟨⟨S₀, hS₀D⟩, mem_attach _ _, rfl⟩)
              simp [hj, hne]
          rw [sum_congr rfl fun j _ ↦ hterm j]
          simp
        · dsimp only
          have hsub :
              (univ.filter fun j : Fin C.length ↦ (if j ∈ idxSet then (1 : ℚ) else 0) ≠ 0) ⊆
                idxSet := by
            intro j hj
            rw [mem_filter] at hj
            by_contra hnot
            simp [hnot] at hj
          exact (card_le_card hsub).trans (hidx_card.trans_eq hD_eq_q)
    · have hnot3XC : C ∉ ThreeExactCover := by
        rintro ⟨_, D, hDC, hexact⟩
        have hsum_U : ∑ u ∈ U.toFinset, (D.filter (u ∈ ·)).card = U.length := by
          have h1 : ∀ u ∈ U.toFinset, (D.filter (u ∈ ·)).card = 1 := fun u hu ↦
            hexact u (mem_slsDedupNat.mp (List.mem_toFinset.mp hu))
          rw [sum_congr rfl h1, sum_const, smul_eq_mul, mul_one,
            List.toFinset_card_of_nodup hU_nd]
        have hswap : ∑ u ∈ U.toFinset, (D.filter (u ∈ ·)).card =
            ∑ S ∈ D, (U.toFinset.filter (· ∈ S)).card := by
          simp only [card_filter]; exact sum_comm
        have hsum_D : ∑ S ∈ D, (U.toFinset.filter (· ∈ S)).card = 3 * D.card := by
          have h3 : ∀ S ∈ D, (U.toFinset.filter (· ∈ S)).card = 3 := by
            intro S hSD
            obtain ⟨hlen3, hndS⟩ := htr S (hDC S hSD)
            have hfilt : U.toFinset.filter (· ∈ S) = S.toFinset := by
              ext u
              simp only [mem_filter, List.mem_toFinset]
              exact ⟨fun h ↦ h.2,
                fun huS ↦ ⟨mem_slsDedupNat.mpr
                  (List.mem_flatten.mpr ⟨S, hDC S hSD, huS⟩), huS⟩⟩
            rw [hfilt, List.toFinset_card_of_nodup hndS, hlen3]
          rw [sum_congr rfl h3, sum_const, smul_eq_mul, mul_comm]
        omega
      have hfx : fromThreeExactCover C = noInstance := by
        simp [fromThreeExactCover, U, htr_b, hmod]
      rw [hfx]
      exact ⟨fun h ↦ (noInstance_notMem h).elim, fun h ↦ (hnot3XC h).elim⟩
  · have hnot3XC : C ∉ ThreeExactCover := by
      rintro ⟨htr, _⟩
      apply htr_b
      rw [List.all_eq_true]
      intro S hS
      exact (slsIsTriple_iff S).mpr (htr S hS)
    have hfx : fromThreeExactCover C = noInstance := by
      simp [fromThreeExactCover, htr_b]
    rw [hfx]
    exact ⟨fun h ↦ (noInstance_notMem h).elim, fun h ↦ (hnot3XC h).elim⟩

end SparseLinearSystem

/-- `ThreeExactCover` reduces to `SparseLinearSystem` in polynomial time. -/
theorem polyTimeReducible_ThreeExactCover_SparseLinearSystem :
    PolyTimeReducible (encList (encList encNat)) encSparseLinearSystem
      ThreeExactCover SparseLinearSystem :=
  ⟨SparseLinearSystem.fromThreeExactCover,
    SparseLinearSystem.computableInPolyTime_fromThreeExactCover,
    fun C ↦ (SparseLinearSystem.fromThreeExactCover_mem_iff C).symm⟩

/-- **Sparse Linear System is `NP`-hard.** -/
theorem SparseLinearSystem_npHard : NPHard encSparseLinearSystem SparseLinearSystem :=
  ThreeExactCover_npComplete.2.trans polyTimeReducible_ThreeExactCover_SparseLinearSystem

/-- **Sparse Linear System is `NP`-complete.** -/
theorem SparseLinearSystem_npComplete : NPComplete encSparseLinearSystem SparseLinearSystem :=
  ⟨SparseLinearSystem.mem_NP, SparseLinearSystem_npHard⟩

end CslibFrontier.Computability.Complexity
