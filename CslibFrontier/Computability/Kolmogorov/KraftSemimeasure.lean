/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import CslibFrontier.Computability.Kolmogorov.LevinCoding
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Primrec.List

/-!
# Recursively Enumerable Discrete Semimeasures, Universal Kraft Weights, and $KC$-Strings

This upstream candidate module develops explicit primitive-recursively encoded rational codes
`RatCode`, Cantor-space prefixes and cylinders, recursively enumerable discrete semimeasures
`ν : List Bool → ℝ` defined via their rational lower graphs, equivalence with
`Cslib.Kolmogorov.IsLowerSemicomputable`, the universal prefix-free Kraft weight
`s ↦ 2⁻¹ ^ universalPrefixBits.complexity s`, Levin's coding upper bound over all recursively
enumerable discrete semimeasures, and Kolmogorov–Chaitin incompressible infinite binary sequences
($KC$-strings), proved unconditionally under standard Lean axioms using only `CslibFrontier` and
`Mathlib` imports.
-/

public section

open Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Filter

namespace CslibFrontier.Computability.Kolmogorov

/-- Explicit natural-number triple `(pos, neg, den)` representing the rational number
`((pos : ℚ) - (neg : ℚ)) / (den : ℚ)` with transparent `Primcodable` encoding. -/
@[ext]
structure RatCode where
  /-- Nonnegative numerator component. -/
  pos : ℕ
  /-- Negative numerator component. -/
  neg : ℕ
  /-- Natural-number denominator (evaluating to `0` when `den = 0`, matching division in `ℚ`). -/
  den : ℕ
deriving DecidableEq

/-- Explicit equivalence between `RatCode` and `ℕ × ℕ × ℕ`. -/
def RatCode.equivTuple : RatCode ≃ ℕ × ℕ × ℕ where
  toFun q := (q.pos, q.neg, q.den)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv := fun ⟨_, _, _⟩ ↦ rfl
  right_inv := fun ⟨_, _, _⟩ ↦ rfl

instance instPrimcodableRatCode : Primcodable RatCode :=
  Primcodable.ofEquiv (ℕ × ℕ × ℕ) RatCode.equivTuple

/-- Rational value `((q.pos : ℚ) - (q.neg : ℚ)) / (q.den : ℚ)` of a code `q : RatCode`. -/
@[expose]
def RatCode.toRat (q : RatCode) : ℚ :=
  ((q.pos : ℚ) - (q.neg : ℚ)) / (q.den : ℚ)

section RationalCodeHelpers

private theorem primrec_ratCode_pos : Primrec RatCode.pos :=
  Primrec.fst.comp (@Primrec.of_equiv (ℕ × ℕ × ℕ) _ RatCode RatCode.equivTuple)

private theorem primrec_ratCode_neg : Primrec RatCode.neg :=
  (Primrec.fst.comp Primrec.snd).comp
    (@Primrec.of_equiv (ℕ × ℕ × ℕ) _ RatCode RatCode.equivTuple)

private theorem primrec_ratCode_den : Primrec RatCode.den :=
  (Primrec.snd.comp Primrec.snd).comp
    (@Primrec.of_equiv (ℕ × ℕ × ℕ) _ RatCode RatCode.equivTuple)

private theorem primrec_ratCode_tuple : Primrec (fun t : ℕ × ℕ × ℕ ↦ RatCode.mk t.1 t.2.1 t.2.2) :=
  @Primrec.of_equiv_symm (ℕ × ℕ × ℕ) _ RatCode RatCode.equivTuple

private theorem primrec_ratCode_mk₃ {α : Type*} [Primcodable α]
    {f g h : α → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a : α ↦ RatCode.mk (f a) (g a) (h a)) :=
  primrec_ratCode_tuple.comp (hf.pair (hg.pair hh))

instance instZeroRatCode : Zero RatCode := ⟨⟨0, 0, 1⟩⟩

instance instOneRatCode : One RatCode := ⟨⟨1, 0, 1⟩⟩

instance instInhabitedRatCode : Inhabited RatCode := ⟨0⟩

instance (priority := low) instOfNatRatCode (n : ℕ) : OfNat RatCode n := ⟨⟨n, 0, 1⟩⟩

theorem RatCode.toRat_zero : (0 : RatCode).toRat = 0 := by
  change (RatCode.mk 0 0 1).toRat = 0; simp [RatCode.toRat]

theorem RatCode.toRat_one : (1 : RatCode).toRat = 1 := by
  change (RatCode.mk 1 0 1).toRat = 1; simp [RatCode.toRat]

@[simp]
theorem RatCode.toRat_ofNat (n : ℕ) :
    (no_index (OfNat.ofNat n) : RatCode).toRat = OfNat.ofNat n := by
  cases n with
  | zero => exact RatCode.toRat_zero
  | succ k =>
    cases k with
    | zero => exact RatCode.toRat_one
    | succ m =>
      change (RatCode.mk (m + 2) 0 1).toRat = ((m + 2 : ℕ) : ℚ); simp [RatCode.toRat]

instance instNegRatCode : Neg RatCode := ⟨fun q ↦ ⟨q.neg, q.pos, q.den⟩⟩

@[simp]
theorem RatCode.toRat_neg (q : RatCode) : (-q).toRat = -q.toRat := by
  change (RatCode.mk q.neg q.pos q.den).toRat = -q.toRat
  simp only [RatCode.toRat]; ring

private theorem primrec_ratCode_neg_op : Primrec ((- ·) : RatCode → RatCode) :=
  primrec_ratCode_mk₃ primrec_ratCode_neg primrec_ratCode_pos primrec_ratCode_den

instance instAddRatCode : Add RatCode where
  add q₁ q₂ :=
    if q₁.den = 0 then q₂
    else if q₂.den = 0 then q₁
    else ⟨q₁.pos * q₂.den + q₂.pos * q₁.den,
          q₁.neg * q₂.den + q₂.neg * q₁.den,
          q₁.den * q₂.den⟩

@[simp]
theorem RatCode.toRat_add (q₁ q₂ : RatCode) : (q₁ + q₂).toRat = q₁.toRat + q₂.toRat := by
  change (if q₁.den = 0 then q₂ else if q₂.den = 0 then q₁ else
    RatCode.mk (q₁.pos * q₂.den + q₂.pos * q₁.den)
      (q₁.neg * q₂.den + q₂.neg * q₁.den) (q₁.den * q₂.den)).toRat = q₁.toRat + q₂.toRat
  by_cases hd₁ : q₁.den = 0
  · simp [RatCode.toRat, hd₁]
  · by_cases hd₂ : q₂.den = 0
    · simp [RatCode.toRat, hd₁, hd₂]
    · simp only [hd₁, hd₂, ↓reduceIte, RatCode.toRat]
      rw [div_add_div _ _ (Nat.cast_ne_zero.mpr hd₁) (Nat.cast_ne_zero.mpr hd₂)]
      push_cast; ring

private theorem primrec₂_ratCode_add : Primrec₂ ((· + ·) : RatCode → RatCode → RatCode) := by
  have hp₁ : Primrec fun p : RatCode × RatCode ↦ p.1.pos := primrec_ratCode_pos.comp Primrec.fst
  have hm₁ : Primrec fun p : RatCode × RatCode ↦ p.1.neg := primrec_ratCode_neg.comp Primrec.fst
  have hd₁ : Primrec fun p : RatCode × RatCode ↦ p.1.den := primrec_ratCode_den.comp Primrec.fst
  have hp₂ : Primrec fun p : RatCode × RatCode ↦ p.2.pos := primrec_ratCode_pos.comp Primrec.snd
  have hm₂ : Primrec fun p : RatCode × RatCode ↦ p.2.neg := primrec_ratCode_neg.comp Primrec.snd
  have hd₂ : Primrec fun p : RatCode × RatCode ↦ p.2.den := primrec_ratCode_den.comp Primrec.snd
  have hmain := primrec_ratCode_mk₃
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hp₁ hd₂) (Primrec.nat_mul.comp hp₂ hd₁))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hm₁ hd₂) (Primrec.nat_mul.comp hm₂ hd₁))
    (Primrec.nat_mul.comp hd₁ hd₂)
  exact Primrec₂.mk <| Primrec.ite (PrimrecRel.comp Primrec.eq hd₁ (Primrec.const 0)) Primrec.snd
    (Primrec.ite (PrimrecRel.comp Primrec.eq hd₂ (Primrec.const 0)) Primrec.fst hmain)

instance instSubRatCode : Sub RatCode := ⟨fun q₁ q₂ ↦ q₁ + (-q₂)⟩

@[simp]
theorem RatCode.toRat_sub (q₁ q₂ : RatCode) : (q₁ - q₂).toRat = q₁.toRat - q₂.toRat := by
  change (q₁ + (-q₂)).toRat = q₁.toRat - q₂.toRat
  rw [RatCode.toRat_add, RatCode.toRat_neg, sub_eq_add_neg]

private theorem primrec₂_ratCode_sub : Primrec₂ ((· - ·) : RatCode → RatCode → RatCode) :=
  Primrec₂.mk <| primrec₂_ratCode_add.comp Primrec.fst (primrec_ratCode_neg_op.comp Primrec.snd)

instance instMulRatCode : Mul RatCode where
  mul q₁ q₂ :=
    ⟨q₁.pos * q₂.pos + q₁.neg * q₂.neg,
     q₁.pos * q₂.neg + q₁.neg * q₂.pos,
     q₁.den * q₂.den⟩

@[simp]
theorem RatCode.toRat_mul (q₁ q₂ : RatCode) : (q₁ * q₂).toRat = q₁.toRat * q₂.toRat := by
  change (RatCode.mk (q₁.pos * q₂.pos + q₁.neg * q₂.neg)
    (q₁.pos * q₂.neg + q₁.neg * q₂.pos) (q₁.den * q₂.den)).toRat = q₁.toRat * q₂.toRat
  simp only [RatCode.toRat]; rw [div_mul_div_comm]; push_cast; ring

private theorem primrec₂_ratCode_mul : Primrec₂ ((· * ·) : RatCode → RatCode → RatCode) := by
  have hp₁ : Primrec fun p : RatCode × RatCode ↦ p.1.pos := primrec_ratCode_pos.comp Primrec.fst
  have hm₁ : Primrec fun p : RatCode × RatCode ↦ p.1.neg := primrec_ratCode_neg.comp Primrec.fst
  have hd₁ : Primrec fun p : RatCode × RatCode ↦ p.1.den := primrec_ratCode_den.comp Primrec.fst
  have hp₂ : Primrec fun p : RatCode × RatCode ↦ p.2.pos := primrec_ratCode_pos.comp Primrec.snd
  have hm₂ : Primrec fun p : RatCode × RatCode ↦ p.2.neg := primrec_ratCode_neg.comp Primrec.snd
  have hd₂ : Primrec fun p : RatCode × RatCode ↦ p.2.den := primrec_ratCode_den.comp Primrec.snd
  exact Primrec₂.mk <| primrec_ratCode_mk₃
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hp₁ hp₂) (Primrec.nat_mul.comp hm₁ hm₂))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hp₁ hm₂) (Primrec.nat_mul.comp hm₁ hp₂))
    (Primrec.nat_mul.comp hd₁ hd₂)

instance instInvRatCode : Inv RatCode where
  inv q :=
    if q.neg ≤ q.pos then ⟨q.den, 0, q.pos - q.neg⟩
    else ⟨0, q.den, q.neg - q.pos⟩

@[simp]
theorem RatCode.toRat_inv (q : RatCode) : (q⁻¹).toRat = (q.toRat)⁻¹ := by
  change (if q.neg ≤ q.pos then RatCode.mk q.den 0 (q.pos - q.neg)
    else RatCode.mk 0 q.den (q.neg - q.pos)).toRat = (q.toRat)⁻¹
  by_cases hle : q.neg ≤ q.pos
  · simp only [hle, ↓reduceIte, RatCode.toRat, Nat.cast_zero, sub_zero, Nat.cast_sub hle, inv_div]
  · have hlt : q.pos ≤ q.neg := (lt_of_not_ge hle).le
    simp only [hle, ↓reduceIte, RatCode.toRat, Nat.cast_zero, zero_sub, Nat.cast_sub hlt]
    have hneg : ((q.neg : ℚ) - (q.pos : ℚ)) = -((q.pos : ℚ) - (q.neg : ℚ)) := by ring
    rw [hneg, neg_div_neg_eq, inv_div]

instance instPowRatCodeNat : Pow RatCode ℕ where
  pow q n := Nat.rec 1 (fun _ acc ↦ acc * q) n

@[simp]
theorem RatCode.toRat_pow (q : RatCode) (n : ℕ) : (q ^ n).toRat = q.toRat ^ n := by
  have hrec : ∀ m : ℕ,
      (Nat.rec (motive := fun _ ↦ RatCode) (1 : RatCode) (fun _ acc ↦ acc * q) m).toRat =
        q.toRat ^ m := fun m ↦ by
    induction m with
    | zero => simp
    | succ k ih =>
      change ((Nat.rec (motive := fun _ ↦ RatCode) (1 : RatCode)
        (fun _ acc ↦ acc * q) k) * q).toRat = q.toRat ^ (k + 1)
      rw [RatCode.toRat_mul, ih, pow_succ]
  exact hrec n

private theorem primrec₂_ratCode_pow : Primrec₂ ((· ^ ·) : RatCode → ℕ → RatCode) := by
  have hstep : Primrec₂ fun (qn : RatCode × ℕ) (ih : ℕ × RatCode) ↦ ih.2 * qn.1 :=
    Primrec₂.mk <| primrec₂_ratCode_mul.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact Primrec₂.mk <| Primrec.nat_rec' Primrec.snd (Primrec.const (1 : RatCode)) hstep

private theorem nonneg_toRat_iff (r : RatCode) :
    (0 : ℚ) ≤ r.toRat ↔ r.den = 0 ∨ r.neg ≤ r.pos := by
  by_cases hd : r.den = 0
  · simp [RatCode.toRat, hd]
  · simp only [hd, false_or, RatCode.toRat]
    have hd_pos : (0 : ℚ) < (r.den : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
    rw [div_nonneg_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ Or.inl ⟨sub_nonneg.mpr (Nat.cast_le.mpr h), hd_pos.le⟩⟩
    rcases h with ⟨hnum, _⟩ | ⟨_, hden_le⟩
    · exact Nat.cast_le.mp (sub_nonneg.mp hnum)
    · linarith

private theorem primrecRel_ratCode_le : PrimrecRel (fun q₁ q₂ : RatCode ↦ q₁.toRat ≤ q₂.toRat) := by
  have hdiff : Primrec fun p : RatCode × RatCode ↦ p.2 - p.1 :=
    primrec₂_ratCode_sub.comp Primrec.snd Primrec.fst
  refine (PrimrecPred.or
    (PrimrecRel.comp Primrec.eq (primrec_ratCode_den.comp hdiff) (Primrec.const 0))
    (PrimrecRel.comp Primrec.nat_le (primrec_ratCode_neg.comp hdiff)
      (primrec_ratCode_pos.comp hdiff))).of_eq fun ⟨q₁, q₂⟩ ↦ ?_
  rw [← nonneg_toRat_iff, RatCode.toRat_sub, sub_nonneg]

private theorem primrecRel_ratCode_lt : PrimrecRel (fun q₁ q₂ : RatCode ↦ q₁.toRat < q₂.toRat) :=
  (PrimrecPred.and primrecRel_ratCode_le
    (PrimrecPred.not (PrimrecPred.comp primrecRel_ratCode_le
      (Primrec.snd.pair Primrec.fst)))).of_eq fun ⟨_, _⟩ ↦ lt_iff_le_not_ge.symm

end RationalCodeHelpers

/-- Length-`n` prefix word of an infinite binary sequence `α : ℕ → Bool`. -/
def binaryPrefix (α : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn fun i : Fin n ↦ α i

@[simp]
private theorem length_binaryPrefix (α : ℕ → Bool) (n : ℕ) :
    (binaryPrefix α n).length = n := by
  simp [binaryPrefix]

/-- Cylinder subset `[s]` of Cantor space `ℕ → Bool` generated by `s : List Bool`. -/
def binaryCylinder (s : List Bool) : Set (ℕ → Bool) :=
  {α | binaryPrefix α s.length = s}

/-- A function `ν : List Bool → ℝ` is a **recursively enumerable discrete semimeasure** on
`{0, 1}^*` if `ν` is nonnegative, summable with `∑' a, ν a ≤ 1`, and its strict nonnegative
rational lower graph `{(a, q) : List Bool × RatCode | 0 ≤ q.toRat ∧ (q.toRat : ℝ) < ν a}` is
`REPred`. -/
def IsRESemimeasure (ν : List Bool → ℝ) : Prop :=
  (∀ a, 0 ≤ ν a) ∧ Summable ν ∧ (∑' a, ν a) ≤ 1 ∧
    REPred fun p : List Bool × RatCode ↦ 0 ≤ p.2.toRat ∧ (p.2.toRat : ℝ) < ν p.1

/-- Every recursively enumerable discrete semimeasure satisfies `IsLowerSemicomputable`. -/
theorem IsRESemimeasure.isLowerSemicomputable {ν : List Bool → ℝ} (hν : IsRESemimeasure ν) :
    IsLowerSemicomputable ν := by
  have hmap : Computable fun p : List Bool × ℕ × ℕ ↦
      (p.1, RatCode.mk p.2.1 0 (p.2.2 + 1)) := by
    have hq : Primrec fun p : List Bool × ℕ × ℕ ↦ RatCode.mk p.2.1 0 (p.2.2 + 1) :=
      primrec_ratCode_tuple.comp
        ((Primrec.fst.comp Primrec.snd).pair
          ((Primrec.const 0).pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))))
    exact Computable.fst.pair hq.to_comp
  refine (hν.2.2.2.comp hmap).of_eq fun ⟨x, a, b⟩ ↦ ?_
  have hq_nonneg : (0 : ℚ) ≤ (RatCode.mk a 0 (b + 1)).toRat := by
    simp only [RatCode.toRat, Nat.cast_zero, sub_zero]; positivity
  have hq_cast : ((RatCode.mk a 0 (b + 1)).toRat : ℝ) = (a : ℝ) / ((b + 1 : ℕ) : ℝ) := by
    simp [RatCode.toRat]
  dsimp only [IsLowerSemicomputable]
  rw [and_iff_right hq_nonneg, hq_cast]

private theorem rePred_bool_and {α : Type*} [Primcodable α] {b : α → Bool} {q : α → Prop}
    (hb : Computable b) (hq : REPred q) :
    REPred fun a ↦ b a = true ∧ q a := by
  refine (Partrec.cond hb hq Partrec.none).of_eq fun a ↦ Part.ext fun u ↦ ?_
  cases u; cases h : b a <;> simp [h]

/-- Conversely, every nonnegative summable `IsLowerSemicomputable` function with total mass at most
`1` satisfies `IsRESemimeasure`. -/
theorem isRESemimeasure_of_isLowerSemicomputable {ν : List Bool → ℝ}
    (hnonneg : ∀ a, 0 ≤ ν a) (hsummable : Summable ν) (hle : (∑' a, ν a) ≤ 1)
    (hμ : IsLowerSemicomputable ν) :
    IsRESemimeasure ν := by
  refine ⟨hnonneg, hsummable, hle, ?_⟩
  let numOf : RatCode → ℕ := fun q ↦ if q.den = 0 then 0 else q.pos - q.neg
  let denPred : RatCode → ℕ := fun q ↦ if q.den = 0 then 0 else q.den - 1
  let nonnegB : RatCode → Bool := fun q ↦ decide (q.den = 0) || decide (q.neg ≤ q.pos)
  have hnum_prim : Primrec numOf :=
    Primrec.ite (PrimrecRel.comp Primrec.eq primrec_ratCode_den (Primrec.const 0))
      (Primrec.const 0) (Primrec.nat_sub.comp primrec_ratCode_pos primrec_ratCode_neg)
  have hden_prim : Primrec denPred :=
    Primrec.ite (PrimrecRel.comp Primrec.eq primrec_ratCode_den (Primrec.const 0))
      (Primrec.const 0) (Primrec.pred.comp primrec_ratCode_den)
  have hnonneg_prim : Primrec nonnegB :=
    Primrec.or.comp
      (PrimrecRel.comp Primrec.eq primrec_ratCode_den (Primrec.const 0)).decide
      (PrimrecRel.comp Primrec.nat_le primrec_ratCode_neg primrec_ratCode_pos).decide
  have hmap : Computable fun p : List Bool × RatCode ↦ (p.1, numOf p.2, denPred p.2) :=
    Computable.fst.pair
      ((hnum_prim.comp Primrec.snd).to_comp.pair (hden_prim.comp Primrec.snd).to_comp)
  have hc0 : Computable fun p : List Bool × RatCode ↦ nonnegB p.2 :=
    (hnonneg_prim.comp Primrec.snd).to_comp
  have hnonnegB_iff : ∀ r : RatCode, nonnegB r = true ↔ (0 : ℚ) ≤ r.toRat := fun r ↦ by
    rw [nonneg_toRat_iff]
    dsimp only [nonnegB]
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  have hval : ∀ q : RatCode, (0 : ℚ) ≤ q.toRat →
      (numOf q : ℝ) / ((denPred q + 1 : ℕ) : ℝ) = (q.toRat : ℝ) := fun q hq0 ↦ by
    have hq_real : (q.toRat : ℝ) = ((q.pos : ℝ) - (q.neg : ℝ)) / (q.den : ℝ) := by
      rw [RatCode.toRat, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_natCast,
        Rat.cast_natCast]
    rw [hq_real]
    by_cases hd : q.den = 0
    · have hn0 : numOf q = 0 := by simp only [numOf, hd, ↓reduceIte]
      rw [hn0, hd, Nat.cast_zero, zero_div, div_zero]
    · have hle_pn : q.neg ≤ q.pos := by
        rcases (nonneg_toRat_iff q).mp hq0 with h0 | hle_pn
        · exact (hd h0).elim
        · exact hle_pn
      have hn_eq : numOf q = q.pos - q.neg := by simp only [numOf, hd, ↓reduceIte]
      have hd_eq : denPred q + 1 = q.den := by
        simp only [denPred, hd, ↓reduceIte, Nat.sub_add_cancel (Nat.pos_of_ne_zero hd)]
      rw [hn_eq, hd_eq, Nat.cast_sub hle_pn]
  have hre_sub : REPred fun p : List Bool × RatCode ↦
      (numOf p.2 : ℝ) / ((denPred p.2 + 1 : ℕ) : ℝ) < ν p.1 :=
    (Partrec.comp hμ hmap).of_eq fun ⟨_, _⟩ ↦ rfl
  refine (rePred_bool_and hc0 hre_sub).of_eq fun ⟨x, q⟩ ↦
    ⟨fun ⟨hb, hlt⟩ ↦ ?_, fun ⟨hq0, hlt⟩ ↦ ⟨(hnonnegB_iff q).mpr hq0, (hval q hq0).symm ▸ hlt⟩⟩
  have hq0 : (0 : ℚ) ≤ q.toRat := (hnonnegB_iff q).mp hb
  exact ⟨hq0, (hval q hq0) ▸ hlt⟩

/-- **The universal prefix-free Kraft weight `s ↦ 2⁻¹ ^ K(s)` is a recursively enumerable
semimeasure.** -/
theorem isRESemimeasure_two_inv_pow_complexity :
    IsRESemimeasure fun s : List Bool ↦ (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity s := by
  have hsum : Summable fun s : List Bool ↦ (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity s :=
    isPrefixFree_universalPrefixBits.summable_universalProb.of_nonneg_of_le
      (fun _ ↦ by positivity) two_inv_pow_complexity_universalPrefixBits_le
  have htsum : (∑' s : List Bool, (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity s) ≤ 1 :=
    (hsum.tsum_le_tsum two_inv_pow_complexity_universalPrefixBits_le
      isPrefixFree_universalPrefixBits.summable_universalProb).trans
      (isPrefixFree_universalPrefixBits.tsum_universalProb_eq_chaitinOmega.trans_le
        isPrefixFree_universalPrefixBits.chaitinOmega_le_one)
  refine ⟨fun _ ↦ by positivity, hsum, htsum, ?_⟩
  let Q : (List Bool × RatCode) → ℕ → Prop := fun p t ↦
    (0 : RatCode).toRat ≤ p.2.toRat ∧
      ∃ qx ∈ universalPrefixTable t,
        (Encodable.decode (α := List Bool) qx.2).getD [] = p.1 ∧
          p.2.toRat < ((2 : RatCode)⁻¹ ^ qx.1.length).toRat
  have hQ_nonneg : ComputablePred fun pt : (List Bool × RatCode) × ℕ ↦
      (0 : RatCode).toRat ≤ pt.1.2.toRat :=
    ((PrimrecRel.comp primrecRel_ratCode_le (Primrec.const (0 : RatCode))
      (Primrec.snd.comp Primrec.fst)).of_eq fun _ ↦ Iff.rfl).computablePred
  have hQ_mem : ComputablePred fun pt : (List Bool × RatCode) × ℕ ↦
      ∃ qx ∈ universalPrefixTable pt.2,
        (Encodable.decode (α := List Bool) qx.2).getD [] = pt.1.1 ∧
          pt.1.2.toRat < ((2 : RatCode)⁻¹ ^ qx.1.length).toRat := by
    let itemOk : ((List Bool × RatCode) × ℕ) → (List Bool × ℕ) → Bool := fun pt qx ↦
      decide ((Encodable.decode (α := List Bool) qx.2).getD [] = pt.1.1) &&
        decide (pt.1.2.toRat < ((2 : RatCode)⁻¹ ^ qx.1.length).toRat)
    have hitem_prim : Primrec₂ itemOk := by
      have hdec_eq : Primrec fun arg : ((List Bool × RatCode) × ℕ) × (List Bool × ℕ) ↦
          decide ((Encodable.decode (α := List Bool) arg.2.2).getD [] = arg.1.1.1) :=
        (PrimrecRel.comp Primrec.eq
          (Primrec.option_getD_default.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).decide
      have hpow : Primrec fun arg : ((List Bool × RatCode) × ℕ) × (List Bool × ℕ) ↦
          (2 : RatCode)⁻¹ ^ arg.2.1.length :=
        primrec₂_ratCode_pow.comp (Primrec.const (2 : RatCode)⁻¹)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      have hlt : Primrec fun arg : ((List Bool × RatCode) × ℕ) × (List Bool × ℕ) ↦
          decide (arg.1.1.2.toRat < ((2 : RatCode)⁻¹ ^ arg.2.1.length).toRat) :=
        primrecRel_ratCode_lt.decide.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) hpow
      exact Primrec₂.mk (Primrec.and.comp hdec_eq hlt)
    have hany : Computable fun pt : (List Bool × RatCode) × ℕ ↦
        (universalPrefixTable pt.2).foldr (fun qx acc ↦ itemOk pt qx || acc) false := by
      have hstep : Primrec₂ fun (pt : (List Bool × RatCode) × ℕ)
          (qxacc : (List Bool × ℕ) × Bool) ↦ itemOk pt qxacc.1 || qxacc.2 :=
        Primrec₂.mk <| Primrec.or.comp
          (hitem_prim.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)
      exact (Primrec.list_foldr
        (primrec_universalPrefixTable.comp Primrec.snd)
        (Primrec.const false) hstep).to_comp
    refine ComputablePred.computable_iff.mpr ⟨_, hany, funext fun pt ↦ propext ?_⟩
    have hfold : ∀ L : List (List Bool × ℕ),
        (∃ qx ∈ L, (Encodable.decode (α := List Bool) qx.2).getD [] = pt.1.1 ∧
          pt.1.2.toRat < ((2 : RatCode)⁻¹ ^ qx.1.length).toRat) ↔
        L.foldr (fun qx acc ↦ itemOk pt qx || acc) false = true := fun L ↦ by
      induction L with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.mem_cons, exists_eq_or_imp, List.foldr_cons, Bool.or_eq_true, ← ih]
        simp [itemOk]
    exact hfold (universalPrefixTable pt.2)
  have hQ_comp : ComputablePred (Function.uncurry Q) := hQ_nonneg.and hQ_mem
  refine (ComputablePred.rePred_exists hQ_comp).of_eq fun ⟨s, r⟩ ↦ ⟨?_, ?_⟩
  · rintro ⟨t, hr0, ⟨q, x⟩, hmem, hdec, hlt⟩
    rw [RatCode.toRat_zero] at hr0
    rw [RatCode.toRat_pow, RatCode.toRat_inv, RatCode.toRat_ofNat] at hlt
    refine ⟨hr0, ?_⟩
    have hprod_bits : universalPrefixBits.Produces q s :=
      map_produces_iff.mpr ⟨x, mem_universalPrefixTable_produces hmem, hdec⟩
    have hfin := ecomplexity_universalPrefixBits_ne_top s
    have hecomp := ecomplexity_le_length hprod_bits
    rw [← natCast_complexity hfin] at hecomp
    have hlen : universalPrefixBits.complexity s ≤ q.length := by exact_mod_cast hecomp
    have hcast : (r.toRat : ℝ) < (2 : ℝ)⁻¹ ^ q.length := by
      simpa using (Rat.cast_lt (K := ℝ)).mpr hlt
    exact hcast.trans_le (pow_le_pow_of_le_one (by positivity) (by norm_num) hlen)
  · rintro ⟨hr0, hlt⟩
    have hfin := ecomplexity_universalPrefixBits_ne_top s
    obtain ⟨q, hprod_bits, hlen_e⟩ := exists_length_eq_ecomplexity hfin
    have hlen : q.length = universalPrefixBits.complexity s :=
      ENat.natCast_inj.mp (hlen_e.trans (natCast_complexity hfin).symm)
    obtain ⟨x, hprod_nat, hdec⟩ := map_produces_iff.mp hprod_bits
    obtain ⟨t, hmem⟩ := produces_iff_exists_mem_universalPrefixTable.mp hprod_nat
    refine ⟨t, by simpa [RatCode.toRat_zero] using hr0, (q, x), hmem, hdec, ?_⟩
    rw [RatCode.toRat_pow, RatCode.toRat_inv, RatCode.toRat_ofNat]
    have hcast : (r.toRat : ℝ) < (((2 : ℚ)⁻¹ ^ q.length : ℚ) : ℝ) := by
      push_cast; rwa [hlen]
    exact (Rat.cast_lt (K := ℝ)).mp hcast

/-- **Levin–Chaitin coding bound for recursively enumerable semimeasures.** -/
theorem exists_le_two_pow_sub_complexity_of_isRESemimeasure
    {ν : List Bool → ℝ} (hν : IsRESemimeasure ν) :
    ∃ D : ℕ, ∀ a : List Bool,
      ν a ≤ (2 : ℝ) ^ ((D : ℝ) - (universalPrefixBits.complexity a : ℝ)) := by
  obtain ⟨c, hc⟩ := exists_le_two_pow_mul_universalPrefixBits_of_isLowerSemicomputable
    hν.1 hν.2.1 hν.2.2.1 hν.isLowerSemicomputable
  refine ⟨c, fun a ↦ ?_⟩
  have hrew : (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity a =
      (2 : ℝ) ^ ((c : ℝ) - (universalPrefixBits.complexity a : ℝ)) := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  rw [← hrew]
  exact hc a

/-- **Universality of the prefix-free Kolmogorov–Chaitin complexity semimeasure.** -/
theorem exists_kolmogorov_reSemimeasure_universal :
    ∃ K : List Bool → ℕ,
      IsRESemimeasure (fun s ↦ (2 : ℝ)⁻¹ ^ K s) ∧
      ∀ ν : List Bool → ℝ, IsRESemimeasure ν →
        ∃ D : ℝ, ∀ a : List Bool,
          ν a ≤ (2 : ℝ) ^ (D - (K a : ℝ)) ∧
          (0 < ν a → (K a : ℝ) ≤ -Real.logb 2 (ν a) + D) := by
  refine ⟨universalPrefixBits.complexity, isRESemimeasure_two_inv_pow_complexity, fun ν hν ↦ ?_⟩
  obtain ⟨D, hD⟩ := exists_le_two_pow_sub_complexity_of_isRESemimeasure hν
  refine ⟨(D : ℝ), fun a ↦ ⟨hD a, fun hνa ↦ ?_⟩⟩
  have hlog : Real.logb 2 (ν a) ≤
      Real.logb 2 ((2 : ℝ) ^ ((D : ℝ) - (universalPrefixBits.complexity a : ℝ))) :=
    Real.logb_le_logb_of_le (by norm_num) hνa (hD a)
  rw [Real.logb_rpow two_pos (by norm_num)] at hlog
  linarith

/-- `d`-incompressible infinite binary sequence with respect to `universalPrefixBits.complexity`. -/
def IsKCStringIncompressible (d : ℕ) (α : ℕ → Bool) : Prop :=
  ∀ n : ℕ, n - d ≤ universalPrefixBits.complexity (binaryPrefix α n)

/-- Kolmogorov–Chaitin complex infinite binary sequence ($KC$-string). -/
def IsKCString (α : ℕ → Bool) : Prop :=
  ∃ d : ℕ, IsKCStringIncompressible d α

/-- Existence of $KC$-strings (witnessed by `realBit (chaitinOmega universalPrefix)`). -/
theorem exists_isKCString : ∃ α : ℕ → Bool, IsKCString α := by
  obtain ⟨c, hc⟩ := exists_le_complexity_realPrefix_chaitinOmega
  refine ⟨realBit (chaitinOmega universalPrefix), c, fun n ↦ ?_⟩
  have hpre : binaryPrefix (realBit (chaitinOmega universalPrefix)) n =
      realPrefix (chaitinOmega universalPrefix) n := by
    refine List.ext_getElem (by simp) fun i _ hi₂ ↦ ?_
    simp only [binaryPrefix, List.getElem_ofFn, getElem_realPrefix hi₂]
  rw [hpre]
  have h := hc n
  omega

end CslibFrontier.Computability.Kolmogorov
