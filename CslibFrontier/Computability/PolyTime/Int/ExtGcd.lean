/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Polynomial-time extended Euclidean algorithm

An unsigned-state deterministic polynomial-time extended Euclidean algorithm `extGcdNat` on
multi-tape Turing machines, computing `(Nat.gcd a b, α, β)` satisfying `α * a + β * b = Nat.gcd a b`
on binary-encoded inputs `(encPair encNat encNat)`.

## Main definitions

* `Cslib.PolyTime.ExtGcdResult`: result record `(gcd, coeffLeft, coeffRight)` of extended GCD.
* `Cslib.PolyTime.encExtGcdResult`: binary encoding of `ExtGcdResult`.
* `Cslib.PolyTime.extGcdNat`: deterministic extended Euclidean algorithm on `ℕ × ℕ`.

## Main results

* `Cslib.PolyTime.extGcdNat_spec`: Bézout identity and GCD specification for `extGcdNat`.
* `Cslib.PolyTime.extGcdNat_computableInPolyTime`: `extGcdNat` is computable in polynomial time.
-/

public section

namespace Cslib.PolyTime

open Turing Turing.MultiTapeTM ComputableInPolyTime

/-- Output record of the extended Euclidean algorithm on `(a, b) : ℕ × ℕ`. -/
structure ExtGcdResult where
  /-- Greatest common divisor `Nat.gcd a b`. -/
  gcd : ℕ
  /-- Left Bézout coefficient `α : ℤ`. -/
  coeffLeft : ℤ
  /-- Right Bézout coefficient `β : ℤ`. -/
  coeffRight : ℤ
  deriving DecidableEq

/-- Binary encoding of `ExtGcdResult` as framed `(encNat, (encIntBin, encIntBin))`. -/
abbrev encExtGcdResult : ExtGcdResult ↪ List Bool :=
  { toFun := fun r ↦ encPair encNat (encPair encIntBin encIntBin) (r.gcd, (r.coeffLeft,
    r.coeffRight))
    inj' := fun r₁ r₂ h ↦ by
      have hp := (encPair encNat (encPair encIntBin encIntBin)).inj' h
      cases r₁; cases r₂; simp_all }

private abbrev ExtGcdState : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × Bool)

private def encExtGcdState : ExtGcdState ↪ List Bool :=
  encPair (encPair (encPair encNat encNat) (encPair encNat encNat))
    (encPair (encPair encNat encNat) encBool)

private def extGcdInit (p : ℕ × ℕ) : ExtGcdState :=
  (((p.1, p.2), (1, 0)), ((0, 1), false))

private def extGcdStep (st : ExtGcdState) : ExtGcdState :=
  let r0 := st.1.1.1
  let r1 := st.1.1.2
  let u0 := st.1.2.1
  let u1 := st.1.2.2
  let v0 := st.2.1.1
  let v1 := st.2.1.2
  let flip := st.2.2
  if r1 = 0 then st
  else
    let q := r0 / r1
    let r2 := r0 % r1
    (((r1, r2), (u1, u0 + q * u1)), ((v1, v0 + q * v1), !flip))

private def extGcdExtract (st : ExtGcdState) : ExtGcdResult where
  gcd := st.1.1.1
  coeffLeft := if st.2.2 then -(st.1.2.1 : ℤ) else (st.1.2.1 : ℤ)
  coeffRight := if st.2.2 then (st.2.1.1 : ℤ) else -(st.2.1.1 : ℤ)

/-- Extended Euclidean algorithm on `(a, b) : ℕ × ℕ`, running `2 * b.bits.length + 2` steps. -/
def extGcdNat (a b : ℕ) : ExtGcdResult :=
  extGcdExtract (extGcdStep^[2 * b.bits.length + 2] (extGcdInit (a, b)))

private def ExtGcdInv (a b : ℕ) (st : ExtGcdState) : Prop :=
  let r0 := st.1.1.1
  let r1 := st.1.1.2
  let u0 := st.1.2.1
  let u1 := st.1.2.2
  let v0 := st.2.1.1
  let v1 := st.2.1.2
  let flip := st.2.2
  let s0 : ℤ := if flip then -(u0 : ℤ) else (u0 : ℤ)
  let t0 : ℤ := if flip then (v0 : ℤ) else -(v0 : ℤ)
  let s1 : ℤ := if flip then (u1 : ℤ) else -(u1 : ℤ)
  let t1 : ℤ := if flip then -(v1 : ℤ) else (v1 : ℤ)
  Nat.gcd r0 r1 = Nat.gcd a b ∧
    r0 * u1 + r1 * u0 = b ∧
    r0 * v1 + r1 * v0 = a ∧
    s0 * (a : ℤ) + t0 * (b : ℤ) = (r0 : ℤ) ∧
    s1 * (a : ℤ) + t1 * (b : ℤ) = (r1 : ℤ) ∧
    r0 ≤ a + b ∧ r1 ≤ b ∧
    u0 ≤ b + 1 ∧ u1 ≤ b + 1 ∧
    v0 ≤ a + 1 ∧ v1 ≤ a + 1

private theorem extGcdInv_init (a b : ℕ) : ExtGcdInv a b (extGcdInit (a, b)) := by
  dsimp only [ExtGcdInv, extGcdInit]
  refine ⟨rfl, ?_, ?_, ?_, ?_, by omega, le_rfl, by omega, by omega, by omega, by omega⟩ <;>
    simp only [mul_zero, mul_one, add_zero, zero_add, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_zero, Nat.cast_one, one_mul, zero_mul, neg_zero]

private theorem extGcdInv_step {a b : ℕ} {st : ExtGcdState} (h : ExtGcdInv a b st) :
    ExtGcdInv a b (extGcdStep st) := by
  rcases st with ⟨⟨⟨r0, r1⟩, ⟨u0, u1⟩⟩, ⟨⟨v0, v1⟩, flip⟩⟩
  dsimp only [extGcdStep]
  by_cases hr1_0 : r1 = 0
  · rw [ite_eq_left hr1_0]; exact h
  · rw [ite_eq_right hr1_0]
    dsimp only [ExtGcdInv] at h ⊢
    obtain ⟨hgcd, hu_eq, hv_eq, hs0, hs1, hr0, hr1, hu0, hu1, hv0, hv1⟩ := h
    set q := r0 / r1
    set r2 := r0 % r1
    have hdiv : r1 * q + r2 = r0 := Nat.div_add_mod r0 r1
    have hr1_pos : 0 < r1 := Nat.pos_of_ne_zero hr1_0
    have hr2_lt : r2 < r1 := Nat.mod_lt r0 hr1_pos
    have hgcd' : Nat.gcd r1 r2 = Nat.gcd a b := by
      rw [Nat.gcd_comm r1 r2, ← Nat.gcd_rec r1 r0, Nat.gcd_comm r1 r0, hgcd]
    have hu_eq' : r1 * (u0 + q * u1) + r2 * u1 = b := by
      calc r1 * (u0 + q * u1) + r2 * u1 = (r1 * q + r2) * u1 + r1 * u0 := by ring
        _ = r0 * u1 + r1 * u0 := by rw [hdiv]
        _ = b := hu_eq
    have hv_eq' : r1 * (v0 + q * v1) + r2 * v1 = a := by
      calc r1 * (v0 + q * v1) + r2 * v1 = (r1 * q + r2) * v1 + r1 * v0 := by ring
        _ = r0 * v1 + r1 * v0 := by rw [hdiv]
        _ = a := hv_eq
    have hu2_le : u0 + q * u1 ≤ b + 1 := by
      have : 1 * (u0 + q * u1) ≤ r1 * (u0 + q * u1) := Nat.mul_le_mul_right _ hr1_pos
      omega
    have hv2_le : v0 + q * v1 ≤ a + 1 := by
      have : 1 * (v0 + q * v1) ≤ r1 * (v0 + q * v1) := Nat.mul_le_mul_right _ hr1_pos
      omega
    have hdivZ : (r2 : ℤ) = (r0 : ℤ) - (q : ℤ) * (r1 : ℤ) := by
      have := congrArg (Nat.cast (R := ℤ)) hdiv
      push_cast at this; linarith
    refine ⟨hgcd', hu_eq', hv_eq', ?_, ?_, by omega, by omega, hu1, hu2_le, hv1, hv2_le⟩
    · cases flip <;>
        simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hs1
    · cases flip <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs0 hs1 ⊢ <;>
        push_cast
      · calc ((u0 : ℤ) + (q : ℤ) * (u1 : ℤ)) * (a : ℤ) +
            -((v0 : ℤ) + (q : ℤ) * (v1 : ℤ)) * (b : ℤ) =
            ((u0 : ℤ) * (a : ℤ) + -(v0 : ℤ) * (b : ℤ)) -
              (q : ℤ) * (-(u1 : ℤ) * (a : ℤ) + (v1 : ℤ) * (b : ℤ)) := by ring
          _ = (r0 : ℤ) - (q : ℤ) * (r1 : ℤ) := by rw [hs0, hs1]
          _ = (r2 : ℤ) := hdivZ.symm
      · calc -((u0 : ℤ) + (q : ℤ) * (u1 : ℤ)) * (a : ℤ) +
            ((v0 : ℤ) + (q : ℤ) * (v1 : ℤ)) * (b : ℤ) =
            (-(u0 : ℤ) * (a : ℤ) + (v0 : ℤ) * (b : ℤ)) -
              (q : ℤ) * ((u1 : ℤ) * (a : ℤ) + -(v1 : ℤ) * (b : ℤ)) := by ring
          _ = (r0 : ℤ) - (q : ℤ) * (r1 : ℤ) := by rw [hs0, hs1]
          _ = (r2 : ℤ) := hdivZ.symm

private theorem extGcdInv_iterate (a b k : ℕ) :
    ExtGcdInv a b (extGcdStep^[k] (extGcdInit (a, b))) := by
  induction k with
  | zero => exact extGcdInv_init a b
  | succ k ih => rw [Function.iterate_succ_apply']; exact extGcdInv_step ih

private theorem extGcdStep_two_halves (st : ExtGcdState) :
    let r1 := st.1.1.2
    let r3 := (extGcdStep (extGcdStep st)).1.1.2
    r1 = 0 ∨ r3 ≤ r1 / 2 := by
  intro r1 r3
  by_cases h1 : r1 = 0
  · exact .inl h1
  · right
    have hr1_pos : 0 < r1 := Nat.pos_of_ne_zero h1
    let r0 := st.1.1.1
    let r2 := r0 % r1
    have hst1_1 : (extGcdStep st).1.1.1 = r1 := by
      simp only [extGcdStep, h1, ↓reduceIte, r1]
    have hst1_2 : (extGcdStep st).1.1.2 = r2 := by
      simp only [extGcdStep, h1, ↓reduceIte, r0, r1, r2]
    by_cases h2 : r2 = 0
    · have : r3 = 0 := by
        dsimp only [r3]
        rw [extGcdStep, ite_eq_left (hst1_2.trans h2), hst1_2, h2]
      omega
    · have hr2_pos : 0 < r2 := Nat.pos_of_ne_zero h2
      have hr2_lt : r2 < r1 := Nat.mod_lt r0 hr1_pos
      have hr3_eq : r3 = r1 % r2 := by
        dsimp only [r3]
        conv_lhs => rw [extGcdStep]
        rw [ite_eq_right (by rw [hst1_2]; exact h2)]
        dsimp only
        rw [hst1_1, hst1_2]
      rw [hr3_eq]
      by_cases hhalf : r2 ≤ r1 / 2
      · exact (Nat.mod_lt r1 hr2_pos).le.trans hhalf
      · have hquot1 : r1 / r2 = 1 := by
          apply le_antisymm
          · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hr2_pos).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le hr2_pos).mpr (by omega)
        have hmod := Nat.div_add_mod r1 r2
        rw [hquot1, mul_one] at hmod
        omega

private theorem extGcd_reaches_zero (a b : ℕ) :
    (extGcdStep^[2 * b.size + 2] (extGcdInit (a, b))).1.1.2 = 0 := by
  suffices ∀ m (st : ExtGcdState), st.1.1.2.size ≤ m →
      (extGcdStep^[2 * m + 2] st).1.1.2 = 0 from
    this b.size (extGcdInit (a, b)) le_rfl
  intro m
  induction m with
  | zero =>
    intro st hsz
    have hr1 : st.1.1.2 = 0 := Nat.size_eq_zero.mp (Nat.le_zero.mp hsz)
    simp [Function.iterate_succ_apply', extGcdStep, hr1]
  | succ m ih =>
    intro st hsz
    rcases extGcdStep_two_halves st with hr1 | hr3
    · have hfix : ∀ k, extGcdStep^[k] st = st := by
        intro k; induction k with
        | zero => rfl
        | succ k ihk => rw [Function.iterate_succ_apply', ihk, extGcdStep, ite_eq_left hr1]
      rw [hfix, hr1]
    · rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega, Function.iterate_add_apply]
      apply ih (extGcdStep^[2] st)
      rcases eq_or_ne st.1.1.2 0 with h0 | hpos
      · have hfix : extGcdStep (extGcdStep st) = st := by simp [extGcdStep, h0]
        change (extGcdStep (extGcdStep st)).1.1.2.size ≤ m
        rw [hfix, h0]; simp
      · have hsize_div : (st.1.1.2 / 2).size ≤ m := by
          have := Nat.size_div_two_add_one hpos; omega
        exact (Nat.size_le_size hr3).trans hsize_div

/-- **Bézout specification of `extGcdNat`.** -/
theorem extGcdNat_spec (a b : ℕ) :
    (extGcdNat a b).gcd = Nat.gcd a b ∧
      (extGcdNat a b).coeffLeft * (a : ℤ) + (extGcdNat a b).coeffRight * (b : ℤ) =
        ((extGcdNat a b).gcd : ℤ) := by
  have hbits : b.bits.length = b.size := by simp only [Nat.size_eq_bits_len]
  have hinv := extGcdInv_iterate a b (2 * b.bits.length + 2)
  have hr1_0 : (extGcdStep^[2 * b.bits.length + 2] (extGcdInit (a, b))).1.1.2 = 0 := by
    rw [hbits]; exact extGcd_reaches_zero a b
  obtain ⟨hgcd, _, _, hs0, _⟩ := hinv
  rw [hr1_0, Nat.gcd_zero_right] at hgcd
  exact ⟨hgcd, hs0⟩

section Poly

attribute [local irreducible] encNat encIntBin encUnary

private theorem extGcdStep_poly :
    ComputableInPolyTime extGcdStep encExtGcdState encExtGcdState := by
  have hr0 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.1.1.1) encExtGcdState encNat :=
    (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hr1 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.1.1.2) encExtGcdState encNat :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hu0 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.1.2.1) encExtGcdState encNat :=
    (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hu1 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.1.2.2) encExtGcdState encNat :=
    (snd _ _).comp ((snd _ _).comp (fst _ _))
  have hv0 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.2.1.1) encExtGcdState encNat :=
    (fst _ _).comp ((fst _ _).comp (snd _ _))
  have hv1 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.2.1.2) encExtGcdState encNat :=
    (snd _ _).comp ((fst _ _).comp (snd _ _))
  have hfl : ComputableInPolyTime (fun st : ExtGcdState ↦ st.2.2) encExtGcdState encBool :=
    (snd _ _).comp (snd _ _)
  have hq := binary_div' hr0 hr1
  have hr2 := binary_mod' hr0 hr1
  have hu2 := binary_add' hu0 (binary_mul' hq hu1)
  have hv2 := binary_add' hv0 (binary_mul' hq hv1)
  have hstep_br : ComputableInPolyTime
      (fun st : ExtGcdState ↦
        ((((st.1.1.2, st.1.1.1 % st.1.1.2),
            (st.1.2.2, st.1.2.1 + (st.1.1.1 / st.1.1.2) * st.1.2.2)),
          ((st.2.1.2, st.2.1.1 + (st.1.1.1 / st.1.1.2) * st.2.1.2), !st.2.2)) : ExtGcdState))
      encExtGcdState encExtGcdState :=
    ((hr1.prod hr2).prod (hu1.prod hu2)).prod ((hv1.prod hv2).prod (bool_not.comp hfl))
  have his0 := decide_eq' hr1 (const 0)
  refine (his0.ite' id' hstep_br).of_enc_eq fun st ↦ (congrArg _ ?_).symm
  dsimp only [extGcdStep, Function.comp_apply, id_eq]
  by_cases h : st.1.1.2 = 0 <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- **`extGcdNat` is computable in deterministic polynomial time.** -/
theorem extGcdNat_computableInPolyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ extGcdNat p.1 p.2)
      (encPair encNat encNat) encExtGcdResult := by
  have ha : ComputableInPolyTime Prod.fst (encPair encNat encNat) encNat := fst _ _
  have hb : ComputableInPolyTime Prod.snd (encPair encNat encNat) encNat := snd _ _
  have hcnt : ComputableInPolyTime (fun p : ℕ × ℕ ↦ 2 * p.2.bits.length + 2)
      (encPair encNat encNat) encUnary := by
    have hblen : ComputableInPolyTime (fun p : ℕ × ℕ ↦ p.2.bits.length)
        (encPair encNat encNat) encUnary :=
      length_bits_comp (natBits.comp hb)
    exact unary_add' (unary_mul' (const 2) hblen) (const 2)
  have hinit : ComputableInPolyTime extGcdInit (encPair encNat encNat) encExtGcdState :=
    (((ha.prod hb).prod ((const 1).prod (const 0))).prod
      (((const 0).prod (const 1)).prod (const false)))
  have hiter : ComputableInPolyTime
      (fun p : ℕ × ℕ ↦ extGcdStep^[2 * p.2.bits.length + 2] (extGcdInit p))
      (encPair encNat encNat) encExtGcdState := by
    refine ComputableInPolyTime.iterate hcnt hinit extGcdStep_poly
      (bound := fun p ↦ 64 * ((encPair encNat encNat p).length + 4))
      (by growth_poly) (fun ⟨pa, pb⟩ i _ ↦ ?_)
    have hinv := extGcdInv_iterate pa pb i
    obtain ⟨_, _, _, _, _, hr0, hr1, hu0, hu1, hv0, hv1⟩ := hinv
    set L := (encPair encNat encNat (pa, pb)).length with hL_def
    have hsz : ∀ x ≤ pa + pb + 1, (encNat x).length ≤ L + 2 := by
      intro x hx
      have ha_sz : pa.size ≤ L := by
        have h1 : (encNat pa).length ≤ L :=
          length_le_encPair_left encNat encNat (pa, pb)
        simp only [encNat_apply, Nat.size_eq_bits_len] at h1 ⊢
        exact h1
      have hb_sz : pb.size ≤ L := by
        have h2 : (encNat pb).length ≤ L :=
          length_le_encPair_right encNat encNat (pa, pb)
        simp only [encNat_apply, Nat.size_eq_bits_len] at h2 ⊢
        exact h2
      simp only [encNat_apply, Nat.size_eq_bits_len]
      have hlt : x < 2 ^ (L + 2) := by
        have hlt_a : pa < 2 ^ L :=
          (Nat.lt_size_self pa).trans_le (Nat.pow_le_pow_right (by omega) ha_sz)
        have hlt_b : pb < 2 ^ L :=
          (Nat.lt_size_self pb).trans_le (Nat.pow_le_pow_right (by omega) hb_sz)
        rw [Nat.pow_add]
        change x < 2 ^ L * 4
        omega
      exact Nat.size_le.mpr hlt
    have s1 := hsz (extGcdStep^[i] (extGcdInit (pa, pb))).1.1.1 (by omega)
    have s2 := hsz (extGcdStep^[i] (extGcdInit (pa, pb))).1.1.2 (by omega)
    have s3 := hsz (extGcdStep^[i] (extGcdInit (pa, pb))).1.2.1 (by omega)
    have s4 := hsz (extGcdStep^[i] (extGcdInit (pa, pb))).1.2.2 (by omega)
    have s5 := hsz (extGcdStep^[i] (extGcdInit (pa, pb))).2.1.1 (by omega)
    have s6 := hsz (extGcdStep^[i] (extGcdInit (pa, pb))).2.1.2 (by omega)
    have hst_len : (encExtGcdState (extGcdStep^[i] (extGcdInit (pa, pb)))).length ≤
        24 * L + 61 := by
      dsimp only [encExtGcdState]
      rw [length_encPair, length_encPair, length_encPair, length_encPair, length_encPair,
        length_encPair]
      simp only [encBool_apply, List.length_singleton]
      omega
    omega
  have hextr_pair : ComputableInPolyTime
      (fun st : ExtGcdState ↦
        (st.1.1.1,
          (if st.2.2 then -(st.1.2.1 : ℤ) else (st.1.2.1 : ℤ),
           if st.2.2 then (st.2.1.1 : ℤ) else -(st.2.1.1 : ℤ))))
      encExtGcdState (encPair encNat (encPair encIntBin encIntBin)) := by
    have hr0 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.1.1.1) encExtGcdState encNat :=
      (fst _ _).comp ((fst _ _).comp (fst _ _))
    have hu0 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.1.2.1) encExtGcdState encNat :=
      (fst _ _).comp ((snd _ _).comp (fst _ _))
    have hv0 : ComputableInPolyTime (fun st : ExtGcdState ↦ st.2.1.1) encExtGcdState encNat :=
      (fst _ _).comp ((fst _ _).comp (snd _ _))
    have hfl : ComputableInPolyTime (fun st : ExtGcdState ↦ st.2.2) encExtGcdState encBool :=
      (snd _ _).comp (snd _ _)
    have hv_part : ComputableInPolyTime
        (fun st : ExtGcdState ↦ if st.2.2 then (st.2.1.1 : ℤ) else -(st.2.1.1 : ℤ))
        encExtGcdState encIntBin :=
      (intBin_signMagnitude' (bool_not.comp hfl) hv0).of_enc_eq fun st ↦
        congrArg ⇑encIntBin (by rcases Bool.dichotomy st.2.2 with h | h <;> simp [h])
    exact hr0.prod ((intBin_signMagnitude' hfl hu0).prod hv_part)
  exact (hextr_pair.comp hiter).of_enc_eq fun _ ↦ rfl

end Poly

end Cslib.PolyTime
