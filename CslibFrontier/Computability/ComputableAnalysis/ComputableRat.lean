/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Nat.Sqrt

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Computable Rational Maps and Effective Integer Arithmetic

Primitive recursive arithmetic on `ℕ` and `ℤ`, signed numerator/denominator computable rational
maps in the sense of Turing and Pour-El–Richards, canonical Gödel numbering of `ℚ`, and effective
algebraic, order, finite-sum, and finite-extremum closure under standard Lean axioms.

## Main definitions

* `CslibFrontier.ComputableAnalysis.IsComputableRatMap`,
  `CslibFrontier.ComputableAnalysis.IsComputableRatMap₂`,
  `CslibFrontier.ComputableAnalysis.IsComputableRatSeq`: rational maps and sequences representable
  as
  `(-1) ^ s(x) * a(x) / b(x)` with total computable `a, b, s` and `b(x) ≠ 0`.
* `CslibFrontier.ComputableAnalysis.ratEncode`, `CslibFrontier.ComputableAnalysis.ratOfNat`:
  explicit
  canonical Gödel code `(q.num, q.den - 1)` of `q : ℚ` and its computable left-inverse surjection
  `ℕ → ℚ`.

## Main results

* `CslibFrontier.ComputableAnalysis.primrec_int_ofNat`,
  `CslibFrontier.ComputableAnalysis.primrec_int_sub`,
  `CslibFrontier.ComputableAnalysis.primrecRel_int_le`,
  `CslibFrontier.ComputableAnalysis.primrecRel_int_lt`,
  `CslibFrontier.ComputableAnalysis.primrec_nat_gcd`,
  `CslibFrontier.ComputableAnalysis.primrec_nat_sqrt`,
  `CslibFrontier.ComputableAnalysis.primrec_nat_factorial`,
  `CslibFrontier.ComputableAnalysis.primrec_nat_pow`,
  `CslibFrontier.ComputableAnalysis.nat_find_mem_rfind`: primitive recursiveness of integer ring and
  order operations and natural-number `gcd`, floor square root, factorial, and exponentiation, plus
  the `Nat.find`/`Nat.rfind` bridge for total Boolean predicates.
* `CslibFrontier.ComputableAnalysis.isComputableRatMap_iff_num_den`,
  `CslibFrontier.ComputableAnalysis.isComputableRatMap_iff_ratEncode`: equivalence between
  `IsComputableRatMap`, computability of reduced numerator/denominator, and computability of
  `ratEncode`.
* `CslibFrontier.ComputableAnalysis.IsComputableRatMap.div`,
  `CslibFrontier.ComputableAnalysis.IsComputableRatMap.decide_le`,
  `CslibFrontier.ComputableAnalysis.IsComputableRatMap.sum_range`,
  `CslibFrontier.ComputableAnalysis.IsComputableRatMap.sup'_range`,
  `CslibFrontier.ComputableAnalysis.IsComputableRatMap.inf'_range`: effective field, lattice, power,
  order, finite-sum, and finite-extremum closure for computable rational maps.
-/

public section

namespace CslibFrontier.ComputableAnalysis

/-! ### Effective arithmetic on `ℕ` and `ℤ` -/

section EffectiveArithmetic

private lemma encode_int_ofNat (n : ℕ) : Encodable.encode (n : ℤ) = 2 * n := by
  change Nat.bit false n = 2 * n
  simp [Nat.bit_val]

private lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
  change Nat.bit true n = 2 * n + 1
  simp [Nat.bit_val]

/-- Coercion `Nat.cast : ℕ → ℤ` is primitive recursive. -/
theorem primrec_int_ofNat : Primrec (Nat.cast : ℕ → ℤ) :=
  Primrec.encode_iff.mp <| Primrec.nat_double.of_eq fun n ↦ (encode_int_ofNat n).symm

private lemma primrec_int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp <| Primrec.nat_double_succ.of_eq fun n ↦ (encode_int_negSucc n).symm

private lemma primrec_int_cases {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → ℤ} {g h : α → ℕ → σ} (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec fun a ↦ @Int.casesOn (fun _ ↦ σ) (f a) (g a) (h a) := by
  have henc : Primrec fun a ↦ Encodable.encode (f a) := Primrec.encode.comp hf
  refine (Primrec.cond (Primrec.nat_bodd.comp henc)
    (hh.comp .id (Primrec.nat_div2.comp henc))
    (hg.comp .id (Primrec.nat_div2.comp henc))).of_eq fun a ↦ ?_
  rcases f a with n | n
  · change (bif (Encodable.encode (n : ℤ)).bodd then h a (Encodable.encode (n : ℤ)).div2
      else g a (Encodable.encode (n : ℤ)).div2) = g a n
    rw [encode_int_ofNat, Nat.div2_val]
    have hb : (2 * n).bodd = false := by simp [Nat.bodd_mul]
    have hd : 2 * n / 2 = n := by omega
    rw [hb, hd]; rfl
  · change (bif (Encodable.encode (Int.negSucc n)).bodd then
      h a (Encodable.encode (Int.negSucc n)).div2
      else g a (Encodable.encode (Int.negSucc n)).div2) = h a n
    rw [encode_int_negSucc, Nat.div2_val]
    have hb : (2 * n + 1).bodd = true := by simp [Nat.bodd_mul]
    have hd : (2 * n + 1) / 2 = n := by omega
    rw [hb, hd]; rfl

/-- Integer `natAbs` is primitive recursive. -/
theorem primrec_int_natAbs : Primrec Int.natAbs :=
  (primrec_int_cases .id Primrec.snd.to₂ (Primrec.succ.comp .snd).to₂).of_eq fun z ↦ by
    rcases z with n | n <;> rfl

/-- Integer negation is primitive recursive. -/
theorem primrec_int_neg : Primrec (Neg.neg : ℤ → ℤ) :=
  (primrec_int_cases .id
    (Primrec.nat_casesOn .snd (.const (0 : ℤ)) (primrec_int_negSucc.comp .snd).to₂).to₂
    (primrec_int_ofNat.comp (Primrec.succ.comp .snd)).to₂).of_eq fun z ↦ by
    rcases z with (_ | n) | n <;> rfl

private lemma primrec_int_subNatNat : Primrec₂ Int.subNatNat := by
  refine Primrec.of_eq
    (Primrec.ite (Primrec.nat_le.comp .snd .fst)
      (primrec_int_ofNat.comp (Primrec.nat_sub.comp .fst .snd))
      (primrec_int_negSucc.comp (Primrec.pred.comp (Primrec.nat_sub.comp .snd .fst))))
    fun ⟨m, n⟩ ↦ ?_
  dsimp only
  by_cases h : n ≤ m
  · rw [Int.subNatNat_of_le h]; simp only [h, ↓reduceIte]
  · rw [Int.subNatNat_of_lt (lt_of_not_ge h)]; simp only [h, ↓reduceIte]

/-- Integer addition is primitive recursive. -/
theorem primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  refine Primrec.of_eq
    (primrec_int_cases .fst
      (primrec_int_cases (Primrec.snd.comp .fst)
        (primrec_int_ofNat.comp (Primrec.nat_add.comp (Primrec.snd.comp .fst) .snd)).to₂
        (primrec_int_subNatNat.comp (Primrec.snd.comp .fst) (Primrec.succ.comp .snd)).to₂).to₂
      (primrec_int_cases (Primrec.snd.comp .fst)
        (primrec_int_subNatNat.comp .snd (Primrec.succ.comp (Primrec.snd.comp .fst))).to₂
        (primrec_int_negSucc.comp
          (Primrec.succ.comp
            (Primrec.nat_add.comp (Primrec.snd.comp .fst) .snd))).to₂).to₂)
    fun ⟨a, b⟩ ↦ ?_
  rcases a with m | m <;> rcases b with n | n <;> rfl

/-- Integer subtraction is primitive recursive. -/
theorem primrec_int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) :=
  Primrec.of_eq (primrec_int_add.comp .fst (primrec_int_neg.comp .snd))
    fun ⟨a, b⟩ ↦ (sub_eq_add_neg a b).symm

/-- Integer multiplication is primitive recursive. -/
theorem primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  refine Primrec.of_eq
    (primrec_int_cases .fst
      (primrec_int_cases (Primrec.snd.comp .fst)
        (primrec_int_ofNat.comp (Primrec.nat_mul.comp (Primrec.snd.comp .fst) .snd)).to₂
        (primrec_int_neg.comp (primrec_int_ofNat.comp
          (Primrec.nat_mul.comp (Primrec.snd.comp .fst) (Primrec.succ.comp .snd)))).to₂).to₂
      (primrec_int_cases (Primrec.snd.comp .fst)
        (primrec_int_neg.comp (primrec_int_ofNat.comp
          (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp .fst)) .snd))).to₂
        (primrec_int_ofNat.comp (Primrec.nat_mul.comp
          (Primrec.succ.comp (Primrec.snd.comp .fst)) (Primrec.succ.comp .snd))).to₂).to₂)
    fun ⟨a, b⟩ ↦ ?_
  rcases a with m | m <;> rcases b with n | n
  · rfl
  · change -(((m * (n + 1) : ℕ) : ℤ)) = (m : ℤ) * Int.negSucc n
    rw [Int.negSucc_eq]; push_cast; ring
  · change -((((m + 1) * n : ℕ) : ℤ)) = Int.negSucc m * (n : ℤ)
    rw [Int.negSucc_eq]; push_cast; ring
  · change (((m + 1) * (n + 1) : ℕ) : ℤ) = Int.negSucc m * Int.negSucc n
    rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring

private lemma primrecPred_int_nonneg : PrimrecPred fun z : ℤ ↦ 0 ≤ z :=
  Primrec.primrecPred <|
    (primrec_int_cases .id (Primrec.const true).to₂ (Primrec.const false).to₂).of_eq
      fun z ↦ by
        rcases z with n | n
        · exact (decide_eq_true (Int.natCast_nonneg n)).symm
        · exact (decide_eq_false (not_le.mpr (Int.negSucc_lt_zero n))).symm

/-- Integer order `≤` is a primitive recursive relation. -/
theorem primrecRel_int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) :=
  PrimrecPred.of_eq (primrecPred_int_nonneg.comp (primrec_int_sub.comp .snd .fst))
    fun ⟨_, _⟩ ↦ sub_nonneg

/-- Integer strict order `<` is a primitive recursive relation. -/
theorem primrecRel_int_lt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) :=
  PrimrecPred.of_eq (primrecRel_int_le.comp .snd .fst).not fun ⟨_, _⟩ ↦ not_le

/-- Natural-number floor square root `Nat.sqrt` is primitive recursive. -/
theorem primrec_nat_sqrt : Primrec Nat.sqrt := by
  refine Primrec.of_graph ⟨id, .id, Nat.sqrt_le_self⟩ ?_
  have hrel : PrimrecRel fun n k : ℕ ↦ k * k ≤ n ∧ n < (k + 1) * (k + 1) :=
    PrimrecPred.and
      (Primrec.nat_le.comp (Primrec.nat_mul.comp .snd .snd) .fst)
      (Primrec.nat_lt.comp .fst
        (Primrec.nat_mul.comp (Primrec.succ.comp .snd) (Primrec.succ.comp .snd)))
  exact hrel.of_eq fun n k ↦
    ⟨fun h ↦ (Nat.eq_sqrt.mpr h).symm, fun h ↦ Nat.eq_sqrt.mp h.symm⟩

/-- Natural-number factorial `Nat.factorial` is primitive recursive. -/
theorem primrec_nat_factorial : Primrec Nat.factorial :=
  (Primrec.nat_rec' .id (.const 1)
    (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp .snd))
      (Primrec.snd.comp .snd)).to₂).of_eq
    fun n ↦ by
      induction n with
      | zero => rfl
      | succ k ih => dsimp only [id] at ih ⊢; rw [ih, Nat.factorial_succ]

/-- Natural-number exponentiation `(· ^ ·)` is primitive recursive. -/
theorem primrec_nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

private def maxCommonDivAux (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if a % (k + 1) = 0 ∧ b % (k + 1) = 0 then k + 1 else maxCommonDivAux a b k

private lemma maxCommonDivAux_spec (a b : ℕ) :
    ∀ k : ℕ, (maxCommonDivAux a b k = 0 ∨
      (maxCommonDivAux a b k ∣ a ∧ maxCommonDivAux a b k ∣ b)) ∧
      (∀ d : ℕ, d ≤ k → d ∣ a → d ∣ b → d ≤ maxCommonDivAux a b k)
  | 0 => ⟨Or.inl rfl, fun _ hd _ _ ↦ hd⟩
  | k + 1 => by
    obtain ⟨hdiv, hmax⟩ := maxCommonDivAux_spec a b k
    dsimp only [maxCommonDivAux]
    by_cases hc : a % (k + 1) = 0 ∧ b % (k + 1) = 0
    · simp only [hc, and_self, ↓reduceIte]
      refine ⟨Or.inr ⟨Nat.dvd_of_mod_eq_zero hc.1, Nat.dvd_of_mod_eq_zero hc.2⟩,
        fun d hd _ _ ↦ hd⟩
    · simp only [hc, ↓reduceIte]
      refine ⟨hdiv, fun d hd hda hdb ↦ ?_⟩
      rcases eq_or_lt_of_le hd with rfl | hlt
      · exact absurd ⟨Nat.mod_eq_zero_of_dvd hda, Nat.mod_eq_zero_of_dvd hdb⟩ hc
      · exact hmax d (Nat.lt_succ_iff.mp hlt) hda hdb

/-- Natural-number greatest common divisor `Nat.gcd` is primitive recursive. -/
theorem primrec_nat_gcd : Primrec₂ Nat.gcd := by
  have hdvd : PrimrecPred fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦
      p.1.1 % (p.2.1 + 1) = 0 ∧ p.1.2 % (p.2.1 + 1) = 0 := by
    have hk1 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2.1 + 1 :=
      Primrec.succ.comp (Primrec.fst.comp .snd)
    exact PrimrecPred.and
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp .fst) hk1) (.const 0))
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp .fst) hk1) (.const 0))
  have hstep : Primrec₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) ↦
      if p.1 % (q.1 + 1) = 0 ∧ p.2 % (q.1 + 1) = 0 then q.1 + 1 else q.2 :=
    Primrec.ite hdvd (Primrec.succ.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp .snd)
  have haux : Primrec fun p : ℕ × ℕ ↦ maxCommonDivAux p.1 p.2 p.1 :=
    (Primrec.nat_rec' .fst (.const 0) hstep).of_eq fun ⟨a, b⟩ ↦ by
      suffices ∀ k : ℕ,
          Nat.rec 0 (fun n IH ↦ if a % (n + 1) = 0 ∧ b % (n + 1) = 0 then n + 1 else IH) k =
            maxCommonDivAux a b k from this a
      intro k; induction k with
      | zero => rfl
      | succ m ih => dsimp only [maxCommonDivAux]; rw [ih]
  refine Primrec.of_eq
    (Primrec.ite (Primrec.eq.comp .fst (.const 0)) .snd haux)
    fun ⟨a, b⟩ ↦ ?_
  dsimp only
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    have hapos : 0 < a := Nat.pos_of_ne_zero ha
    obtain ⟨hdiv, hmax⟩ := maxCommonDivAux_spec a b a
    have h1le : 1 ≤ maxCommonDivAux a b a := hmax 1 hapos (one_dvd a) (one_dvd b)
    have hcd : maxCommonDivAux a b a ∣ a ∧ maxCommonDivAux a b a ∣ b :=
      hdiv.resolve_left (by omega)
    have hle1 : maxCommonDivAux a b a ≤ Nat.gcd a b :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b hapos) (Nat.dvd_gcd hcd.1 hcd.2)
    have hle2 : Nat.gcd a b ≤ maxCommonDivAux a b a :=
      hmax (Nat.gcd a b) (Nat.le_of_dvd hapos (Nat.gcd_dvd_left a b))
        (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    exact le_antisymm hle1 hle2

private lemma int_natAbs_cast_of_neg {z : ℤ} (h : z < 0) : ((z.natAbs : ℕ) : ℚ) = -(z : ℚ) := by
  simpa only [Int.cast_natCast, Int.cast_neg] using
    congrArg (Int.cast : ℤ → ℚ) (Int.ofNat_natAbs_of_nonpos h.le)

private lemma int_natAbs_cast_of_nonneg {z : ℤ} (h : 0 ≤ z) : ((z.natAbs : ℕ) : ℚ) = (z : ℚ) := by
  simpa only [Int.cast_natCast] using
    congrArg (Int.cast : ℤ → ℚ) (Int.natAbs_of_nonneg h)

private def reduceIntNat (a : ℤ) (b : ℕ) : ℤ × ℕ :=
  if b = 0 then (0, 1)
  else
    let g := a.natAbs.gcd b
    let m := a.natAbs / g
    (if a < 0 then -((m : ℕ) : ℤ) else (m : ℕ), b / g)

private lemma primrec_reduceIntNat : Primrec₂ reduceIntNat := by
  have hg : Primrec fun p : ℤ × ℕ ↦ p.1.natAbs.gcd p.2 :=
    primrec_nat_gcd.comp (primrec_int_natAbs.comp .fst) .snd
  have hm : Primrec fun p : ℤ × ℕ ↦ p.1.natAbs / p.1.natAbs.gcd p.2 :=
    Primrec.nat_div.comp (primrec_int_natAbs.comp .fst) hg
  have hnum : Primrec fun p : ℤ × ℕ ↦
      if p.1 < 0 then -(((p.1.natAbs / p.1.natAbs.gcd p.2 : ℕ) : ℤ))
      else ((p.1.natAbs / p.1.natAbs.gcd p.2 : ℕ) : ℤ) :=
    Primrec.ite (primrecRel_int_lt.comp .fst (.const 0))
      (primrec_int_neg.comp (primrec_int_ofNat.comp hm))
      (primrec_int_ofNat.comp hm)
  exact Primrec.ite (Primrec.eq.comp .snd (.const 0))
    (.const ((0 : ℤ), (1 : ℕ)))
    (Primrec.pair hnum (Primrec.nat_div.comp .snd hg))

private lemma reduceIntNat_eq_num_den (a : ℤ) (b : ℕ) :
    reduceIntNat a b = (((a : ℚ) / (b : ℚ)).num, ((a : ℚ) / (b : ℚ)).den) := by
  dsimp only [reduceIntNat]
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ↓reduceIte]
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    set g := a.natAbs.gcd b
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right a.natAbs hb_pos
    set m := a.natAbs / g
    set d := b / g
    set n : ℤ := if a < 0 then -((m : ℕ) : ℤ) else (m : ℕ)
    have hdg : d * g = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a.natAbs b)
    have hmg : m * g = a.natAbs := Nat.div_mul_cancel (Nat.gcd_dvd_left a.natAbs b)
    have hd_pos : 0 < d :=
      Nat.pos_of_ne_zero fun hd0 ↦ by rw [hd0, zero_mul] at hdg; exact hb hdg.symm
    have hna : n.natAbs = m := by
      dsimp only [n]
      by_cases hlt : a < 0 <;> simp [hlt]
    have hcop : n.natAbs.Coprime d := by
      rw [hna]; exact Nat.coprime_div_gcd_div_gcd hg_pos
    have hng : n * (g : ℤ) = a := by
      dsimp only [n]
      by_cases hlt : a < 0
      · simp only [hlt, ↓reduceIte, neg_mul]
        have : ((m * g : ℕ) : ℤ) = -a := by
          rw [hmg]; exact Int.ofNat_natAbs_of_nonpos hlt.le
        push_cast at this; omega
      · simp only [hlt, ↓reduceIte]
        have : ((m * g : ℕ) : ℤ) = a := by
          rw [hmg]; exact Int.natAbs_of_nonneg (not_lt.mp hlt)
        push_cast at this; exact this
    set q : ℚ := (a : ℚ) / (b : ℚ)
    have hq_eq : (q.num : ℚ) / (q.den : ℚ) = (n : ℚ) / (d : ℚ) := by
      rw [q.num_div_den]
      have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
      have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
      rw [div_eq_div_iff hbq hdq]
      have hz : a * (d : ℤ) = n * (b : ℤ) := by rw [← hdg, ← hng]; push_cast; ring
      exact_mod_cast hz
    have hcross_q : (q.num : ℚ) * (d : ℚ) = (n : ℚ) * (q.den : ℚ) :=
      (div_eq_div_iff (Nat.cast_ne_zero.mpr q.den_ne_zero)
        (Nat.cast_ne_zero.mpr hd_pos.ne')).mp hq_eq
    have hcross : q.num * (d : ℤ) = n * (q.den : ℤ) := by exact_mod_cast hcross_q
    have hcross_nat : q.num.natAbs * d = n.natAbs * q.den := by
      have := congrArg Int.natAbs hcross
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using this
    have hd_eq : d = q.den := by
      apply Nat.dvd_antisymm
      · exact hcop.symm.dvd_of_dvd_mul_left ⟨q.num.natAbs, by linarith⟩
      · exact q.reduced.symm.dvd_of_dvd_mul_left ⟨n.natAbs, by linarith⟩
    have hn_eq : n = q.num := by
      rw [hd_eq] at hcross
      exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero) hcross.symm
    exact Prod.ext hn_eq hd_eq

end EffectiveArithmetic

/-! ### Computable rational maps, Gödel numbering of `ℚ`, and closure operations -/

/-- A rational map `r : α → ℚ` on a `Primcodable` domain `α` is computable if there exist total
computable functions `a b s : α → ℕ` with `b x ≠ 0` and `r x = (-1) ^ s x * a x / b x` for every
`x : α`. -/
@[expose] def IsComputableRatMap {α : Type*} [Primcodable α] (r : α → ℚ) : Prop :=
  ∃ a b s : α → ℕ, Computable a ∧ Computable b ∧ Computable s ∧
    (∀ x, b x ≠ 0) ∧ ∀ x, r x = (-1 : ℚ) ^ s x * (a x : ℚ) / (b x : ℚ)

/-- A binary rational map `r : α → β → ℚ` on `Primcodable` domains is computable if its uncurried
map `fun p : α × β ↦ r p.1 p.2` satisfies `IsComputableRatMap`. -/
abbrev IsComputableRatMap₂ {α β : Type*} [Primcodable α] [Primcodable β] (r : α → β → ℚ) : Prop :=
  IsComputableRatMap fun p : α × β ↦ r p.1 p.2

/-- A sequence of rational numbers `r : ℕ → ℚ` is computable if `r n = (-1) ^ s n * a n / b n` for
total computable `a b s : ℕ → ℕ` with `b n ≠ 0` everywhere. -/
abbrev IsComputableRatSeq (r : ℕ → ℚ) : Prop := IsComputableRatMap r

/-- Explicit canonical Gödel code `Nat.pair (Encodable.encode q.num) (q.den - 1)` of a rational
number `q : ℚ`. -/
def ratEncode (q : ℚ) : ℕ :=
  Nat.pair (Encodable.encode q.num) (q.den - 1)

/-- Explicit computable surjection `ℕ → ℚ` left-inverse to `ratEncode`. -/
def ratOfNat (m : ℕ) : ℚ :=
  ((Denumerable.ofNat ℤ m.unpair.1 : ℤ) : ℚ) / ((m.unpair.2 + 1 : ℕ) : ℚ)

/-- `ratOfNat` is a left inverse of `ratEncode`. -/
@[simp] theorem ratOfNat_ratEncode (q : ℚ) : ratOfNat (ratEncode q) = q := by
  have hd : q.den - 1 + 1 = q.den := Nat.sub_add_cancel q.den_pos
  rw [ratOfNat, ratEncode, Nat.unpair_pair, Denumerable.ofNat_encode, hd, q.num_div_den]

/-- Forming `x ↦ (a x : ℚ) / (b x : ℚ)` from computable `a : α → ℤ` and `b : α → ℕ` yields a
computable rational map (including where `b x = 0`, using Lean's totalized `/ 0 = 0`). -/
theorem IsComputableRatMap.of_intDivNat {α : Type*} [Primcodable α] {a : α → ℤ} {b : α → ℕ}
    (ha : Computable a) (hb : Computable b) :
    IsComputableRatMap fun x ↦ (a x : ℚ) / (b x : ℚ) := by
  refine ⟨fun x ↦ if b x = 0 then 0 else (a x).natAbs,
    fun x ↦ if b x = 0 then 1 else b x,
    fun x ↦ if a x < 0 then 1 else 0,
    (Computable.cond (Primrec.beq.to_comp.comp hb (.const 0)) (.const 0)
      (primrec_int_natAbs.to_comp.comp ha)).of_eq (fun x ↦ by by_cases h : b x = 0 <;> simp [h]),
    (Computable.cond (Primrec.beq.to_comp.comp hb (.const 0)) (.const 1) hb).of_eq
      (fun x ↦ by by_cases h : b x = 0 <;> simp [h]),
    (Computable.cond ((primrecRel_int_lt.comp .id (.const 0)).decide.to_comp.comp ha)
      (.const 1) (.const 0)).of_eq (fun x ↦ by by_cases h : a x < 0 <;> simp [h]),
    fun x ↦ by by_cases h : b x = 0 <;> simp [h],
    fun x ↦ ?_⟩
  by_cases hb0 : b x = 0
  · simp [hb0]
  · simp only [hb0, ↓reduceIte]
    by_cases hlt : a x < 0
    · simp only [hlt, ↓reduceIte, pow_one, neg_one_mul, int_natAbs_cast_of_neg hlt, neg_neg]
    · simp only [hlt, ↓reduceIte, pow_zero, one_mul,
        int_natAbs_cast_of_nonneg (not_lt.mp hlt)]

/-- Pointwise equality preserves `IsComputableRatMap`. -/
theorem IsComputableRatMap.of_eq {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (h : ∀ x, f x = g x) : IsComputableRatMap g :=
  funext h ▸ hf

/-- Characterization of `IsComputableRatMap` by computability of reduced numerator and
denominator. -/
theorem isComputableRatMap_iff_num_den {α : Type*} [Primcodable α] {r : α → ℚ} :
    IsComputableRatMap r ↔
      Computable (fun x ↦ (r x).num) ∧ Computable (fun x ↦ (r x).den) := by
  constructor
  · rintro ⟨a, b, s, ha, hb, hs, _, hr⟩
    let n0 : α → ℤ := fun x ↦ if s x % 2 = 0 then (a x : ℤ) else -(a x : ℤ)
    have hn0 : Computable n0 :=
      (Computable.cond
        (Primrec.beq.to_comp.comp (Primrec.nat_mod.to_comp.comp hs (.const 2)) (.const 0))
        (primrec_int_ofNat.to_comp.comp ha)
        (primrec_int_neg.to_comp.comp (primrec_int_ofNat.to_comp.comp ha))).of_eq fun x ↦ by
        dsimp only [n0]; by_cases h : s x % 2 = 0 <;> simp [h]
    have hred := primrec_reduceIntNat.to_comp.comp hn0 hb
    have heq : ∀ x, reduceIntNat (n0 x) (b x) = ((r x).num, (r x).den) := fun x ↦ by
      rw [reduceIntNat_eq_num_den]
      suffices hq : (n0 x : ℚ) / (b x : ℚ) = r x by rw [hq]
      dsimp only [n0]; rw [hr x]
      rcases Nat.even_or_odd' (s x) with ⟨k, hk | hk⟩
      · have hm : s x % 2 = 0 := by omega
        simp only [hm, ↓reduceIte, Int.cast_natCast]
        rw [hk, pow_mul, neg_one_sq, one_pow, one_mul]
      · have hm : s x % 2 ≠ 0 := by omega
        simp only [hm, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
        rw [hk, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one, neg_one_mul]
    exact ⟨(Computable.fst.comp hred).of_eq fun x ↦ congrArg Prod.fst (heq x),
      (Computable.snd.comp hred).of_eq fun x ↦ congrArg Prod.snd (heq x)⟩
  · rintro ⟨hnum, hden⟩
    exact (IsComputableRatMap.of_intDivNat hnum hden).of_eq fun x ↦ (r x).num_div_den

/-- Reduced numerator of a computable rational map is computable. -/
theorem IsComputableRatMap.num {α : Type*} [Primcodable α] {r : α → ℚ}
    (hr : IsComputableRatMap r) : Computable fun x ↦ (r x).num :=
  (isComputableRatMap_iff_num_den.mp hr).1

/-- Reduced denominator of a computable rational map is computable. -/
theorem IsComputableRatMap.den {α : Type*} [Primcodable α] {r : α → ℚ}
    (hr : IsComputableRatMap r) : Computable fun x ↦ (r x).den :=
  (isComputableRatMap_iff_num_den.mp hr).2

/-- `ratOfNat : ℕ → ℚ` is a computable rational sequence. -/
theorem isComputableRatMap_ratOfNat : IsComputableRatMap ratOfNat :=
  IsComputableRatMap.of_intDivNat
    ((Computable.ofNat ℤ).comp (Computable.fst.comp .unpair))
    (Computable.succ.comp (Computable.snd.comp .unpair))

/-- The Gödel code `x ↦ ratEncode (r x)` of a computable rational map is computable. -/
theorem IsComputableRatMap.ratEncode {α : Type*} [Primcodable α] {r : α → ℚ}
    (hr : IsComputableRatMap r) : Computable fun x ↦ ratEncode (r x) :=
  Primrec₂.natPair.to_comp.comp (Computable.encode.comp hr.num) (Computable.pred.comp hr.den)

/-- Precomposition of a computable rational map with a computable map is computable. -/
theorem IsComputableRatMap.comp {α β : Type*} [Primcodable α] [Primcodable β]
    {r : β → ℚ} {g : α → β} (hr : IsComputableRatMap r) (hg : Computable g) :
    IsComputableRatMap fun x ↦ r (g x) :=
  isComputableRatMap_iff_num_den.mpr ⟨hr.num.comp hg, hr.den.comp hg⟩

/-- Equivalence between the signed numerator/denominator representation `IsComputableRatMap r` and
total recursive computability of `x ↦ ratEncode (r x)`. -/
theorem isComputableRatMap_iff_ratEncode {α : Type*} [Primcodable α] {r : α → ℚ} :
    IsComputableRatMap r ↔ Computable fun x ↦ ratEncode (r x) :=
  ⟨IsComputableRatMap.ratEncode,
    fun h ↦ (isComputableRatMap_ratOfNat.comp h).of_eq fun x ↦ ratOfNat_ratEncode (r x)⟩

/-- Converting `IsComputableRatMap` on a product domain into `IsComputableRatMap₂`. -/
theorem IsComputableRatMap.to₂ {α β : Type*} [Primcodable α] [Primcodable β] {r : α × β → ℚ}
    (hr : IsComputableRatMap r) : IsComputableRatMap₂ fun a b ↦ r (a, b) := hr

/-- Composing a binary computable rational map with two computable maps. -/
theorem IsComputableRatMap₂.comp {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {r : β → γ → ℚ} {f : α → β} {g : α → γ} (hr : IsComputableRatMap₂ r)
    (hf : Computable f) (hg : Computable g) :
    IsComputableRatMap fun x ↦ r (f x) (g x) :=
  IsComputableRatMap.comp hr (hf.pair hg)

/-- Constant rational maps are computable. -/
theorem IsComputableRatMap.const {α : Type*} [Primcodable α] (q : ℚ) :
    IsComputableRatMap fun _ : α ↦ q :=
  isComputableRatMap_iff_num_den.mpr ⟨.const q.num, .const q.den⟩

/-- Constant binary rational maps are computable. -/
theorem IsComputableRatMap₂.const {α β : Type*} [Primcodable α] [Primcodable β] (q : ℚ) :
    IsComputableRatMap₂ fun (_ : α) (_ : β) ↦ q :=
  IsComputableRatMap.const q

/-- Casting a computable `ℕ`-valued map to `ℚ` yields a computable rational map. -/
theorem IsComputableRatMap.ofNat {α : Type*} [Primcodable α] {f : α → ℕ} (hf : Computable f) :
    IsComputableRatMap fun x ↦ (f x : ℚ) :=
  (IsComputableRatMap.of_intDivNat (primrec_int_ofNat.to_comp.comp hf) (.const 1)).of_eq
    fun _ ↦ by simp

/-- Casting a computable `ℤ`-valued map to `ℚ` yields a computable rational map. -/
theorem IsComputableRatMap.ofInt {α : Type*} [Primcodable α] {f : α → ℤ} (hf : Computable f) :
    IsComputableRatMap fun x ↦ (f x : ℚ) :=
  (IsComputableRatMap.of_intDivNat hf (.const 1)).of_eq fun _ ↦ by simp

/-- Boolean conditional of computable rational maps is computable. -/
theorem IsComputableRatMap.ite {α : Type*} [Primcodable α] {c : α → Bool} {f g : α → ℚ}
    (hc : Computable c) (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ if c x = true then f x else g x :=
  isComputableRatMap_iff_num_den.mpr
    ⟨(Computable.cond hc hf.num hg.num).of_eq fun x ↦ by cases c x <;> rfl,
      (Computable.cond hc hf.den hg.den).of_eq fun x ↦ by cases c x <;> rfl⟩

/-- Negation of a computable rational map is computable. -/
theorem IsComputableRatMap.neg {α : Type*} [Primcodable α] {f : α → ℚ}
    (hf : IsComputableRatMap f) : IsComputableRatMap fun x ↦ -f x :=
  (IsComputableRatMap.of_intDivNat (primrec_int_neg.to_comp.comp hf.num) hf.den).of_eq fun x ↦ by
    push_cast; rw [neg_div, (f x).num_div_den]

/-- Sum of computable rational maps is computable. -/
theorem IsComputableRatMap.add {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ f x + g x :=
  (IsComputableRatMap.of_intDivNat
    (primrec_int_add.to_comp.comp
      (primrec_int_mul.to_comp.comp hf.num (primrec_int_ofNat.to_comp.comp hg.den))
      (primrec_int_mul.to_comp.comp hg.num (primrec_int_ofNat.to_comp.comp hf.den)))
    (Primrec.nat_mul.to_comp.comp hf.den hg.den)).of_eq fun x ↦ by
    have hfd : ((f x).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f x).den_ne_zero
    have hgd : ((g x).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (g x).den_ne_zero
    conv_rhs => rw [← (f x).num_div_den, ← (g x).num_div_den]
    push_cast; field_simp

/-- Difference of computable rational maps is computable. -/
theorem IsComputableRatMap.sub {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ f x - g x :=
  (hf.add hg.neg).of_eq fun x ↦ (sub_eq_add_neg (f x) (g x)).symm

/-- Product of computable rational maps is computable. -/
theorem IsComputableRatMap.mul {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ f x * g x :=
  (IsComputableRatMap.of_intDivNat
    (primrec_int_mul.to_comp.comp hf.num hg.num)
    (Primrec.nat_mul.to_comp.comp hf.den hg.den)).of_eq fun x ↦ by
    conv_rhs => rw [← (f x).num_div_den, ← (g x).num_div_den]
    push_cast; field_simp

/-- Multiplicative inverse of a computable rational map is computable. -/
theorem IsComputableRatMap.inv {α : Type*} [Primcodable α] {f : α → ℚ}
    (hf : IsComputableRatMap f) : IsComputableRatMap fun x ↦ (f x)⁻¹ :=
  (IsComputableRatMap.of_intDivNat
    (Computable.cond ((primrecRel_int_lt.comp .id (.const 0)).decide.to_comp.comp hf.num)
      (primrec_int_neg.to_comp.comp (primrec_int_ofNat.to_comp.comp hf.den))
      (primrec_int_ofNat.to_comp.comp hf.den))
    (primrec_int_natAbs.to_comp.comp hf.num)).of_eq fun x ↦ by
    by_cases hlt : (f x).num < 0
    · have hb : (bif decide (id (f x).num < 0) then -((f x).den : ℤ) else ((f x).den : ℤ)) =
          -((f x).den : ℤ) := by simp [hlt]
      rw [hb, Int.cast_neg, Int.cast_natCast, int_natAbs_cast_of_neg hlt, neg_div_neg_eq]
      conv_rhs => rw [← (f x).num_div_den, inv_div]
    · have hb : (bif decide (id (f x).num < 0) then -((f x).den : ℤ) else ((f x).den : ℤ)) =
          ((f x).den : ℤ) := by simp [hlt]
      rw [hb, Int.cast_natCast, int_natAbs_cast_of_nonneg (not_lt.mp hlt)]
      conv_rhs => rw [← (f x).num_div_den, inv_div]

/-- Quotient of computable rational maps is computable. -/
theorem IsComputableRatMap.div {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ f x / g x :=
  (hf.mul hg.inv).of_eq fun x ↦ (div_eq_mul_inv (f x) (g x)).symm

/-- Deciding `f x ≤ g x` between computable rational maps is computable. -/
theorem IsComputableRatMap.decide_le {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    Computable fun x ↦ decide (f x ≤ g x) :=
  (primrecRel_int_le.decide.to₂.to_comp.comp
    (primrec_int_mul.to_comp.comp hf.num (primrec_int_ofNat.to_comp.comp hg.den))
    (primrec_int_mul.to_comp.comp hg.num (primrec_int_ofNat.to_comp.comp hf.den))).of_eq fun x ↦ by
    have hfp : (0 : ℚ) < ((f x).den : ℚ) := Nat.cast_pos.mpr (f x).den_pos
    have hgp : (0 : ℚ) < ((g x).den : ℚ) := Nat.cast_pos.mpr (g x).den_pos
    have hiff : ((f x).num : ℚ) * ((g x).den : ℚ) ≤ ((g x).num : ℚ) * ((f x).den : ℚ) ↔
        f x ≤ g x := by
      conv_rhs => rw [← (f x).num_div_den, ← (g x).num_div_den, div_le_div_iff₀ hfp hgp]
    have hiff_z : (f x).num * ((g x).den : ℤ) ≤ (g x).num * ((f x).den : ℤ) ↔ f x ≤ g x := by
      exact_mod_cast hiff
    simp only [hiff_z]

/-- Deciding `f x < g x` between computable rational maps is computable. -/
theorem IsComputableRatMap.decide_lt {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    Computable fun x ↦ decide (f x < g x) :=
  (Primrec.not.to_comp.comp (hg.decide_le hf)).of_eq fun x ↦ by
    by_cases h : g x ≤ f x <;> simp [h, not_lt.mpr, lt_of_not_ge]

/-- Pointwise maximum of computable rational maps is computable. -/
theorem IsComputableRatMap.max {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ Max.max (f x) (g x) :=
  (IsComputableRatMap.ite (hf.decide_le hg) hg hf).of_eq fun x ↦ by
    by_cases h : f x ≤ g x <;> simp [h, le_of_not_ge]

/-- Pointwise minimum of computable rational maps is computable. -/
theorem IsComputableRatMap.min {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : IsComputableRatMap f) (hg : IsComputableRatMap g) :
    IsComputableRatMap fun x ↦ Min.min (f x) (g x) :=
  (IsComputableRatMap.ite (hf.decide_le hg) hf hg).of_eq fun x ↦ by
    by_cases h : f x ≤ g x <;> simp [h, le_of_not_ge]

/-- Pointwise absolute value of a computable rational map is computable. -/
theorem IsComputableRatMap.abs {α : Type*} [Primcodable α] {f : α → ℚ}
    (hf : IsComputableRatMap f) : IsComputableRatMap fun x ↦ |f x| :=
  hf.max hf.neg

/-- Natural-number recursion producing a computable rational map via `ratEncode`/`ratOfNat`. -/
private lemma isComputableRatMap_nat_rec {α : Type*} [Primcodable α]
    {b : α → ℕ} {z : α → ℚ} {step : α → ℕ → ℚ → ℚ}
    (hb : Computable b) (hz : IsComputableRatMap z)
    (hstep : ∀ {f : α × (ℕ × ℕ) → ℚ}, IsComputableRatMap f →
      IsComputableRatMap fun p : α × (ℕ × ℕ) ↦ step p.1 p.2.1 (f p)) :
    IsComputableRatMap fun a ↦ Nat.rec (z a) (fun k acc ↦ step a k acc) (b a) := by
  have hcode := Computable.nat_rec hb hz.ratEncode
    ((hstep (isComputableRatMap_ratOfNat.comp (Computable.snd.comp .snd))).ratEncode).to₂
  refine isComputableRatMap_iff_ratEncode.mpr (hcode.of_eq fun a ↦ ?_)
  induction b a with
  | zero => rfl
  | succ k ih => dsimp only at ih ⊢; rw [ih, ratOfNat_ratEncode]

/-- Natural-number power `x ↦ f x ^ d x` of a computable rational map is computable. -/
theorem IsComputableRatMap.pow {α : Type*} [Primcodable α] {f : α → ℚ} {d : α → ℕ}
    (hf : IsComputableRatMap f) (hd : Computable d) :
    IsComputableRatMap fun x ↦ f x ^ d x :=
  (isComputableRatMap_nat_rec hd (.const 1) (step := fun x _ acc ↦ acc * f x)
    fun hacc ↦ hacc.mul (hf.comp .fst)).of_eq fun x ↦ by
    induction d x with
    | zero => simp
    | succ k ih => dsimp only at ih ⊢; rw [ih, pow_succ]

/-- Integer power `x ↦ f x ^ z x` of a computable rational map is computable. -/
theorem IsComputableRatMap.zpow {α : Type*} [Primcodable α] {f : α → ℚ} {z : α → ℤ}
    (hf : IsComputableRatMap f) (hz : Computable z) :
    IsComputableRatMap fun x ↦ f x ^ z x := by
  have hpow := hf.pow (primrec_int_natAbs.to_comp.comp hz)
  refine (IsComputableRatMap.ite
    ((primrecRel_int_lt.comp .id (.const 0)).decide.to_comp.comp hz)
    hpow.inv hpow).of_eq fun x ↦ ?_
  rcases z x with n | n
  · simp
  · have hlt : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    simp [hlt, zpow_negSucc]

/-- Finite sums `a ↦ ∑ i ∈ Finset.range (b a), g a i` of a computable binary rational map are
computable. -/
theorem IsComputableRatMap.sum_range {α : Type*} [Primcodable α] {b : α → ℕ} {g : α → ℕ → ℚ}
    (hb : Computable b) (hg : IsComputableRatMap₂ g) :
    IsComputableRatMap fun a ↦ ∑ i ∈ Finset.range (b a), g a i :=
  (isComputableRatMap_nat_rec hb (.const 0) (step := fun a k acc ↦ acc + g a k)
    fun hacc ↦ hacc.add (hg.comp .fst (Computable.fst.comp .snd))).of_eq fun a ↦ by
    induction b a with
    | zero => simp
    | succ k ih => dsimp only at ih ⊢; rw [ih, Finset.sum_range_succ]

/-- Finite suprema `a ↦ (Finset.range (b a + 1)).sup' _ (g a)` of a computable binary rational map
are computable. -/
theorem IsComputableRatMap.sup'_range {α : Type*} [Primcodable α] {b : α → ℕ} {g : α → ℕ → ℚ}
    (hb : Computable b) (hg : IsComputableRatMap₂ g) :
    IsComputableRatMap fun a ↦
      (Finset.range (b a + 1)).sup' Finset.nonempty_range_add_one (g a) :=
  (isComputableRatMap_nat_rec hb (hg.comp .id (.const 0))
    (step := fun a k acc ↦ Max.max acc (g a (k + 1)))
    fun hacc ↦ hacc.max
      (hg.comp .fst (Computable.succ.comp (Computable.fst.comp .snd)))).of_eq fun a ↦ by
    induction b a with
    | zero => simp
    | succ k ih =>
      dsimp only at ih ⊢; rw [ih]
      apply le_antisymm
      · refine max_le
          (Finset.sup'_le _ _ fun i hi ↦ Finset.le_sup' (g a)
            (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
          (Finset.le_sup' (g a) (Finset.mem_range.mpr (Nat.lt_succ_self (k + 1))))
      · refine Finset.sup'_le _ _ fun i hi ↦ ?_
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) with rfl | hlt
        · exact le_max_right _ _
        · exact (Finset.le_sup' (g a) (Finset.mem_range.mpr hlt)).trans (le_max_left _ _)

/-- Finite infima `a ↦ (Finset.range (b a + 1)).inf' _ (g a)` of a computable binary rational map
are computable. -/
theorem IsComputableRatMap.inf'_range {α : Type*} [Primcodable α] {b : α → ℕ} {g : α → ℕ → ℚ}
    (hb : Computable b) (hg : IsComputableRatMap₂ g) :
    IsComputableRatMap fun a ↦
      (Finset.range (b a + 1)).inf' Finset.nonempty_range_add_one (g a) :=
  (isComputableRatMap_nat_rec hb (hg.comp .id (.const 0))
    (step := fun a k acc ↦ Min.min acc (g a (k + 1)))
    fun hacc ↦ hacc.min
      (hg.comp .fst (Computable.succ.comp (Computable.fst.comp .snd)))).of_eq fun a ↦ by
    induction b a with
    | zero => simp
    | succ k ih =>
      dsimp only at ih ⊢; rw [ih]
      apply le_antisymm
      · refine Finset.le_inf' _ _ fun i hi ↦ ?_
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) with rfl | hlt
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (Finset.inf'_le (g a) (Finset.mem_range.mpr hlt))
      · refine le_min
          (Finset.le_inf' _ _ fun i hi ↦ Finset.inf'_le (g a)
            (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
          (Finset.inf'_le (g a) (Finset.mem_range.mpr (Nat.lt_succ_self (k + 1))))

/-- Minimal witness `Nat.find hex` belongs to `Nat.rfind` of a total Boolean predicate. -/
theorem nat_find_mem_rfind {p : ℕ → Bool} (hex : ∃ k, p k = true) :
    Nat.find hex ∈ Nat.rfind fun k ↦ Part.some (p k) :=
  Nat.mem_rfind.mpr ⟨Part.mem_some_iff.mpr (Nat.find_spec hex).symm,
    fun hm ↦ Part.mem_some_iff.mpr (Bool.eq_false_iff.mpr (Nat.find_min hex hm)).symm⟩

end CslibFrontier.ComputableAnalysis
