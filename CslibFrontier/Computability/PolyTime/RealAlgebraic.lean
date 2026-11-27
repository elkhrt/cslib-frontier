/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import Mathlib.RingTheory.Algebraic.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Algebra.Polynomial

/-!
# Exact polynomial-time order comparison and dyadic rounding for real algebraic numbers

For every fixed real algebraic number `α : ℝ` (`IsAlgebraic ℚ α`), exact order comparisons
`(q : ℝ) < α`, `α < (q : ℝ)`, `(q : ℝ) ≤ α`, `α ≤ (q : ℝ)`, and `(q : ℝ) = α` against an arbitrary
rational input `q : ℚ` (encoded in binary under `Turing.MultiTapeTM.encRat`) are computable in
deterministic polynomial time (`Turing.MultiTapeTM.ComputableInPolyTime`).

Combining exact algebraic comparison with invariant-carrying binary search
(`ComputableInPolyTime.iterateWith_spec`) computes the exact integer floor
`⌊2 ^ r * (q + k * α)⌋ : ℤ` and exact integrality flag on inputs `((q, k), r) : (ℚ × ℕ) × ℕ` with
`q` encoded by `encRat`, the iterate count `k` encoded in *binary* (`encNat`), and the precision `r`
encoded in *unary* (`encUnary`), running in time polynomial in `|q| + log k + r`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.rat_eval_poly`: evaluating any fixed polynomial
  `p : Polynomial ℚ` on `encRat` is computable in polynomial time.
* `Turing.MultiTapeTM.ComputableInPolyTime.rat_lt_algebraic`,
  `.algebraic_lt_rat`, `.rat_le_algebraic`, `.algebraic_le_rat`, `.rat_eq_algebraic`:
  exact polynomial-time order and equality tests between `q : ℚ` and any fixed real algebraic `α`.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_le_twoPow_mul_add_mul_algebraic`,
  `.eq_twoPow_mul_add_mul_algebraic`, `.floor_twoPow_mul_add_mul_algebraic`:
  exact comparison, integrality test, and floor `⌊2 ^ r * (q + k * α)⌋` in polynomial time in `|q|`,
  `log k` (binary), and `r` (unary).
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Polynomial Set

/-- Evaluating any fixed rational polynomial `p : Polynomial ℚ` at a rational input `q : ℚ` is
computable in polynomial time under `encRat`. -/
theorem rat_eval_poly (p : Polynomial ℚ) :
    ComputableInPolyTime (fun q : ℚ => p.eval q) encRat encRat := by
  have hpow : ∀ m : ℕ, ComputableInPolyTime (fun q : ℚ => q ^ m) encRat encRat := by
    intro m
    induction m with
    | zero => exact (const (encOut := encRat) 1).of_enc_eq fun _ => by simp
    | succ m ihm => simpa only [pow_succ] using rat_mul' ihm id'
  have hsum : ∀ n : ℕ,
      ComputableInPolyTime (fun q : ℚ => ∑ i ∈ Finset.range n, p.coeff i * q ^ i)
        encRat encRat := by
    intro n
    induction n with
    | zero => exact const 0
    | succ n ih =>
      simpa only [Finset.sum_range_succ] using
        rat_add' ih (rat_mul' (const (p.coeff n)) (hpow n))
  refine (hsum (p.natDegree + 1)).of_enc_eq fun q => congrArg encRat ?_
  rw [Polynomial.eval_eq_sum_range]

private theorem aeval_rat_eq_cast_eval (p : Polynomial ℚ) (q : ℚ) :
    Polynomial.aeval (q : ℝ) p = ((p.eval q : ℚ) : ℝ) := by
  simpa using Polynomial.aeval_algebraMap_apply ℝ q p

private theorem hasDerivAt_aeval_rat (p : Polynomial ℚ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Polynomial.aeval t p) (Polynomial.aeval x p.derivative) x := by
  let q : Polynomial ℝ := p.map (algebraMap ℚ ℝ)
  have hfn : (fun t : ℝ => Polynomial.aeval t p) = fun t : ℝ => q.eval t := by
    ext t; rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hd : Polynomial.aeval x p.derivative = q.derivative.eval x := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map]
  rw [hfn, hd]
  exact q.hasDerivAt x

private theorem continuous_aeval_rat (p : Polynomial ℚ) :
    Continuous (fun t : ℝ => Polynomial.aeval t p) := by
  let q : Polynomial ℝ := p.map (algebraMap ℚ ℝ)
  have hfn : (fun t : ℝ => Polynomial.aeval t p) = fun t : ℝ => q.eval t := by
    ext t; rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [hfn]
  exact q.continuous

/-- **Exact polynomial-time comparison with a real algebraic number**: for every real algebraic
number `α : ℝ` (`IsAlgebraic ℚ α`), deciding `(q : ℝ) < α` on input `q : ℚ` runs in deterministic
polynomial time under `encRat`. -/
theorem rat_lt_algebraic {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime (fun q : ℚ => decide ((q : ℝ) < α)) encRat encBool := by
  by_cases hrat : ∃ r : ℚ, (r : ℝ) = α
  · obtain ⟨r, rfl⟩ := hrat
    refine (rat_lt' id' (const r)).of_enc_eq fun q =>
      congrArg encBool (decide_eq_decide.mpr Rat.cast_lt)
  · set p : Polynomial ℚ := minpoly ℚ α
    have hsep : p.Separable := (minpoly.irreducible hα.isIntegral).separable
    have hroot : Polynomial.aeval α p = 0 := minpoly.aeval ℚ α
    have hderiv_ne : Polynomial.aeval α p.derivative ≠ 0 := by
      intro hzero
      obtain ⟨u, v, huv⟩ : IsCoprime p p.derivative := hsep
      have h1 := congrArg (Polynomial.aeval α) huv
      simp only [map_add, map_mul, map_one, hroot, hzero, mul_zero, add_zero] at h1
      exact zero_ne_one h1
    have hcont' : Continuous (fun t : ℝ => Polynomial.aeval t p.derivative) :=
      continuous_aeval_rat p.derivative
    rcases lt_or_gt_of_ne hderiv_ne with hneg | hpos
    · obtain ⟨δ, _, hball⟩ :=
        Metric.isOpen_iff.mp (isOpen_lt hcont' continuous_const) α hneg
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (by linarith : α - δ < α)
      obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (by linarith : α < α + δ)
      have hanti : StrictAntiOn (fun t : ℝ => Polynomial.aeval t p) (Icc (a : ℝ) (b : ℝ)) := by
        intro x hx y hy hxy
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => Polynomial.aeval t p)
          (fun t : ℝ => Polynomial.aeval t p.derivative) hxy
          (continuous_aeval_rat p).continuousOn (fun t _ => hasDerivAt_aeval_rat p t)
        have hcneg : Polynomial.aeval c p.derivative < 0 := hball (Metric.mem_ball.mpr
          (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hy.2, hc.1, hc.2]))
        have hmul : Polynomial.aeval y p - Polynomial.aeval x p < 0 := by
          rw [eq_div_iff (sub_pos.mpr hxy).ne'] at hslope
          nlinarith [sub_pos.mpr hxy]
        linarith
      let dec : ℚ → Bool := fun q =>
        if decide (q ≤ a) then true
        else if decide (b ≤ q) then false
        else decide (0 < p.eval q)
      have hpoly : ComputableInPolyTime dec encRat encBool :=
        (rat_le' id' (const a)).ite' (const true)
          ((rat_le' (const b) id').ite' (const false)
            (rat_lt' (const 0) (rat_eval_poly p)))
      refine hpoly.of_enc_eq fun q => congrArg encBool ?_
      dsimp only [dec]
      by_cases hqa : q ≤ a
      · have hlt : (q : ℝ) < α := lt_of_le_of_lt (by exact_mod_cast hqa) ha2
        simp [hqa, hlt]
      · by_cases hbq : b ≤ q
        · have hge : ¬((q : ℝ) < α) := not_lt.mpr (hb1.le.trans (by exact_mod_cast hbq))
          simp [hqa, hbq, hge]
        · simp only [hqa, hbq, decide_false, Bool.false_eq_true, ↓reduceIte]
          refine decide_eq_decide.mpr ?_
          have hqm : (q : ℝ) ∈ Icc (a : ℝ) (b : ℝ) :=
            ⟨by exact_mod_cast (lt_of_not_ge hqa).le, by exact_mod_cast (lt_of_not_ge hbq).le⟩
          have hiff := hanti.lt_iff_gt ⟨ha2.le, hb1.le⟩ hqm
          rw [hroot, aeval_rat_eq_cast_eval] at hiff
          exact hiff.symm.trans (Rat.cast_pos (K := ℝ))
    · obtain ⟨δ, _, hball⟩ :=
        Metric.isOpen_iff.mp (isOpen_lt continuous_const hcont') α hpos
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (by linarith : α - δ < α)
      obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (by linarith : α < α + δ)
      have hmono : StrictMonoOn (fun t : ℝ => Polynomial.aeval t p) (Icc (a : ℝ) (b : ℝ)) := by
        intro x hx y hy hxy
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => Polynomial.aeval t p)
          (fun t : ℝ => Polynomial.aeval t p.derivative) hxy
          (continuous_aeval_rat p).continuousOn (fun t _ => hasDerivAt_aeval_rat p t)
        have hcpos : 0 < Polynomial.aeval c p.derivative := hball (Metric.mem_ball.mpr
          (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hy.2, hc.1, hc.2]))
        rw [eq_div_iff (sub_pos.mpr hxy).ne'] at hslope
        have hmul : 0 < Polynomial.aeval y p - Polynomial.aeval x p := by
          nlinarith [sub_pos.mpr hxy]
        linarith
      let dec : ℚ → Bool := fun q =>
        if decide (q ≤ a) then true
        else if decide (b ≤ q) then false
        else decide (p.eval q < 0)
      have hpoly : ComputableInPolyTime dec encRat encBool :=
        (rat_le' id' (const a)).ite' (const true)
          ((rat_le' (const b) id').ite' (const false)
            (rat_lt' (rat_eval_poly p) (const 0)))
      refine hpoly.of_enc_eq fun q => congrArg encBool ?_
      dsimp only [dec]
      by_cases hqa : q ≤ a
      · have hlt : (q : ℝ) < α := lt_of_le_of_lt (by exact_mod_cast hqa) ha2
        simp [hqa, hlt]
      · by_cases hbq : b ≤ q
        · have hge : ¬((q : ℝ) < α) := not_lt.mpr (hb1.le.trans (by exact_mod_cast hbq))
          simp [hqa, hbq, hge]
        · simp only [hqa, hbq, decide_false, Bool.false_eq_true, ↓reduceIte]
          refine decide_eq_decide.mpr ?_
          have hqm : (q : ℝ) ∈ Icc (a : ℝ) (b : ℝ) :=
            ⟨by exact_mod_cast (lt_of_not_ge hqa).le, by exact_mod_cast (lt_of_not_ge hbq).le⟩
          have hiff := hmono.lt_iff_lt hqm ⟨ha2.le, hb1.le⟩
          rw [hroot, aeval_rat_eq_cast_eval] at hiff
          exact hiff.symm.trans (Rat.cast_lt_zero (K := ℝ))

/-- Exact polynomial-time test `decide (α < (q : ℝ))` for fixed real algebraic `α`. -/
theorem algebraic_lt_rat {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime (fun q : ℚ => decide (α < (q : ℝ))) encRat encBool :=
  ((rat_lt_algebraic hα.neg).comp rat_neg).of_enc_eq
    fun q => congrArg encBool (by simp [Rat.cast_neg, neg_lt_neg_iff])

/-- Exact polynomial-time test `decide ((q : ℝ) ≤ α)` for fixed real algebraic `α`. -/
theorem rat_le_algebraic {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime (fun q : ℚ => decide ((q : ℝ) ≤ α)) encRat encBool :=
  (bool_not.comp (algebraic_lt_rat hα)).of_enc_eq
    fun q => congrArg encBool (by simp [← decide_not, not_lt])

/-- Exact polynomial-time test `decide (α ≤ (q : ℝ))` for fixed real algebraic `α`. -/
theorem algebraic_le_rat {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime (fun q : ℚ => decide (α ≤ (q : ℝ))) encRat encBool :=
  (bool_not.comp (rat_lt_algebraic hα)).of_enc_eq
    fun q => congrArg encBool (by simp [← decide_not, not_lt])

/-- Exact polynomial-time test `decide ((q : ℝ) = α)` for fixed real algebraic `α`. -/
theorem rat_eq_algebraic {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime (fun q : ℚ => decide ((q : ℝ) = α)) encRat encBool := by
  refine (bool_and' (rat_le_algebraic hα) (algebraic_le_rat hα)).of_enc_eq
    fun q => congrArg encBool ?_
  rw [Bool.eq_iff_iff]
  simp [le_antisymm_iff]

/-- Mixed encoding for `((q, k), r) : (ℚ × ℕ) × ℕ` with `q : ℚ` in binary, `k : ℕ` in binary, and
`r : ℕ` in unary. -/
abbrev encRatBinUnary : (ℚ × ℕ) × ℕ ↪ List Bool :=
  encPair (encPair encRat encNat) encUnary

/-- Exact polynomial-time test `decide ((z : ℝ) ≤ 2 ^ r * (q + k * α))` for fixed algebraic `α`. -/
theorem int_le_twoPow_mul_add_mul_algebraic {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime
      (fun p : ((ℚ × ℕ) × ℕ) × ℤ =>
        decide ((p.2 : ℝ) ≤ (2 : ℝ) ^ p.1.2 * ((p.1.1.1 : ℝ) + (p.1.1.2 : ℝ) * α)))
      (encPair encRatBinUnary encIntBin) encBool := by
  let encIn := encPair encRatBinUnary encIntBin
  have hq : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => p.1.1.1) encIn encRat :=
    ((fst encRatBinUnary encIntBin).fst').fst'
  have hk : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => p.1.1.2) encIn encNat :=
    ((fst encRatBinUnary encIntBin).fst').snd'
  have hr' : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => p.1.2) encIn encUnary :=
    (snd (encPair encRat encNat) encUnary).comp (fst encRatBinUnary encIntBin)
  have hz : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => (p.2 : ℚ)) encIn encRat :=
    rat_intCast.comp (snd encRatBinUnary encIntBin)
  have h2r : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => (2 : ℚ) ^ p.1.2) encIn encRat :=
    rat_pow' (const 2) hr'
  have hkq : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => (p.1.1.2 : ℚ)) encIn encRat :=
    rat_natCast.comp hk
  have hk0 : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => decide (p.1.1.2 = 0))
      encIn encBool := (rat_isZero' hkq).of_enc_eq fun _ => by simp
  have hthresh : ComputableInPolyTime
      (fun p : ((ℚ × ℕ) × ℕ) × ℤ => ((p.2 : ℚ) / (2 : ℚ) ^ p.1.2 - p.1.1.1) / (p.1.1.2 : ℚ))
      encIn encRat :=
    rat_div' (rat_sub' (rat_div' hz h2r) hq) hkq
  refine (hk0.ite' (rat_le' hz (rat_mul' h2r hq))
    ((rat_le_algebraic hα).comp hthresh)).of_enc_eq
    fun ⟨⟨⟨q, k⟩, r⟩, z⟩ => congrArg encBool ?_
  by_cases hkz : k = 0
  · subst hkz
    simp only [decide_true, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero]
    exact decide_eq_decide.mpr (by exact_mod_cast Iff.rfl)
  · simp only [hkz, decide_false, Bool.false_eq_true, ↓reduceIte, Function.comp_apply]
    refine decide_eq_decide.mpr ?_
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    push_cast
    rw [div_le_iff₀ hkpos, sub_le_iff_le_add', div_le_iff₀ h2pos, mul_comm ((q : ℝ) + _),
      mul_comm α _]

/-- Exact polynomial-time integrality test `decide ((z : ℝ) = 2 ^ r * (q + k * α))` for a fixed
real algebraic number `α : ℝ`. -/
theorem eq_twoPow_mul_add_mul_algebraic {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime
      (fun p : ((ℚ × ℕ) × ℕ) × ℤ =>
        decide ((p.2 : ℝ) = (2 : ℝ) ^ p.1.2 * ((p.1.1.1 : ℝ) + (p.1.1.2 : ℝ) * α)))
      (encPair encRatBinUnary encIntBin) encBool := by
  let encIn := encPair encRatBinUnary encIntBin
  have hq : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => p.1.1.1) encIn encRat :=
    ((fst encRatBinUnary encIntBin).fst').fst'
  have hk : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => p.1.1.2) encIn encNat :=
    ((fst encRatBinUnary encIntBin).fst').snd'
  have hr' : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => p.1.2) encIn encUnary :=
    (snd (encPair encRat encNat) encUnary).comp (fst encRatBinUnary encIntBin)
  have hz : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => (p.2 : ℚ)) encIn encRat :=
    rat_intCast.comp (snd encRatBinUnary encIntBin)
  have h2r : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => (2 : ℚ) ^ p.1.2) encIn encRat :=
    rat_pow' (const 2) hr'
  have hkq : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => (p.1.1.2 : ℚ)) encIn encRat :=
    rat_natCast.comp hk
  have hk0 : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × ℤ => decide (p.1.1.2 = 0))
      encIn encBool := (rat_isZero' hkq).of_enc_eq fun _ => by simp
  have hthresh : ComputableInPolyTime
      (fun p : ((ℚ × ℕ) × ℕ) × ℤ => ((p.2 : ℚ) / (2 : ℚ) ^ p.1.2 - p.1.1.1) / (p.1.1.2 : ℚ))
      encIn encRat :=
    rat_div' (rat_sub' (rat_div' hz h2r) hq) hkq
  refine (hk0.ite' (rat_eq.comp (hz.prod (rat_mul' h2r hq)))
    ((rat_eq_algebraic hα).comp hthresh)).of_enc_eq
    fun ⟨⟨⟨q, k⟩, r⟩, z⟩ => congrArg encBool ?_
  by_cases hkz : k = 0
  · subst hkz
    simp only [decide_true, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero, Function.comp_apply]
    exact decide_eq_decide.mpr (by exact_mod_cast Iff.rfl)
  · simp only [hkz, decide_false, Bool.false_eq_true, ↓reduceIte, Function.comp_apply]
    refine decide_eq_decide.mpr ?_
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    push_cast
    rw [div_eq_iff hkpos.ne', sub_eq_iff_eq_add', div_eq_iff h2pos.ne', mul_comm ((q : ℝ) + _),
      mul_comm α _]

/-- Exact polynomial-time computation of `⌊2 ^ r * (q + k * α)⌋ : ℤ` on input `((q, k), r)` with
`q : ℚ` in binary, `k : ℕ` in binary (`log k` bits), and `r : ℕ` in unary. -/
theorem floor_twoPow_mul_add_mul_algebraic {α : ℝ} (hα : IsAlgebraic ℚ α) :
    ComputableInPolyTime
      (fun x : (ℚ × ℕ) × ℕ => Int.floor ((2 : ℝ) ^ x.2 * ((x.1.1 : ℝ) + (x.1.2 : ℝ) * α)))
      encRatBinUnary encIntBin := by
  let M : ℕ := Nat.ceil |α| + 1
  have hα_abs : |α| ≤ (M : ℝ) := by
    have := Nat.le_ceil |α|
    have hcast : ((Nat.ceil |α| : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith
  have hα_lo : -(M : ℝ) ≤ α := (abs_le.mp hα_abs).1
  have hα_hi : α ≤ (M : ℝ) := (abs_le.mp hα_abs).2
  let lo0 : (ℚ × ℕ) × ℕ → ℤ := fun x =>
    Rat.floor ((2 : ℚ) ^ x.2 * (x.1.1 - (x.1.2 : ℚ) * (M : ℚ))) - 1
  let hi0 : (ℚ × ℕ) × ℕ → ℤ := fun x =>
    Rat.floor ((2 : ℚ) ^ x.2 * (x.1.1 + (x.1.2 : ℚ) * (M : ℚ))) + 2
  have hq : ComputableInPolyTime (fun x : (ℚ × ℕ) × ℕ => x.1.1) encRatBinUnary encRat :=
    (fst _ _).fst'
  have hkq : ComputableInPolyTime (fun x : (ℚ × ℕ) × ℕ => (x.1.2 : ℚ)) encRatBinUnary encRat :=
    rat_natCast.comp (fst _ _).snd'
  have h2r : ComputableInPolyTime (fun x : (ℚ × ℕ) × ℕ => (2 : ℚ) ^ x.2) encRatBinUnary encRat :=
    rat_pow' (const 2) (snd _ _)
  have hlo0 : ComputableInPolyTime lo0 encRatBinUnary encIntBin :=
    intBin_sub' (rat_floor' (rat_mul' h2r (rat_sub' hq (rat_mul' hkq (const (M : ℚ)))))) (const 1)
  have hhi0 : ComputableInPolyTime hi0 encRatBinUnary encIntBin :=
    intBin_add' (rat_floor' (rat_mul' h2r (rat_add' hq (rat_mul' hkq (const (M : ℚ)))))) (const 2)
  let init : (ℚ × ℕ) × ℕ → ℤ × ℤ := fun x => (lo0 x, hi0 x)
  let count : (ℚ × ℕ) × ℕ → ℕ := fun x => (hi0 x - lo0 x).natAbs.size
  have hcount : ComputableInPolyTime count encRatBinUnary encUnary :=
    binary_size.comp (intBin_natAbs.comp (intBin_sub' hhi0 hlo0))
  let target : (ℚ × ℕ) × ℕ → ℝ := fun x => (2 : ℝ) ^ x.2 * ((x.1.1 : ℝ) + (x.1.2 : ℝ) * α)
  let midFn : ℤ × ℤ → ℤ := fun st => st.1 + (((st.2 - st.1).toNat / 2 : ℕ) : ℤ)
  have hmid : ComputableInPolyTime midFn (encPair encIntBin encIntBin) encIntBin :=
    intBin_add' (fst _ _) (intBin_natCast.comp
      (binary_div.comp ((intBin_toNat.comp (intBin_sub' (snd _ _) (fst _ _))).prod (const 2))))
  let step : (ℚ × ℕ) × ℕ → ℤ × ℤ → ℤ × ℤ := fun x st =>
    let m := midFn st
    if decide ((m : ℝ) ≤ target x) then (m, st.2) else (st.1, m)
  have hstep : ComputableInPolyTime (fun p : ((ℚ × ℕ) × ℕ) × (ℤ × ℤ) => step p.1 p.2)
      (encPair encRatBinUnary (encPair encIntBin encIntBin)) (encPair encIntBin encIntBin) := by
    have hst := snd encRatBinUnary (encPair encIntBin encIntBin)
    have hx := fst encRatBinUnary (encPair encIntBin encIntBin)
    have hm := hmid.comp hst
    have hcmp := (int_le_twoPow_mul_add_mul_algebraic hα).comp (hx.prod hm)
    exact hcmp.ite' (hm.prod hst.snd') (hst.fst'.prod hm)
  let inv : (ℚ × ℕ) × ℕ → ℕ → ℤ × ℤ → Prop := fun x i st =>
    lo0 x ≤ st.1 ∧ st.1 ≤ Int.floor (target x) ∧ Int.floor (target x) < st.2 ∧ st.2 ≤ hi0 x ∧
      (st.2 - st.1).toNat ≤ 2 ^ (count x - i)
  have hbase : ∀ x, inv x 0 (init x) := fun x => by
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ x.2 := by positivity
    have hk0 : (0 : ℝ) ≤ (x.1.2 : ℝ) := Nat.cast_nonneg _
    have hlo_le : (lo0 x : ℝ) ≤ target x := by
      let ql : ℚ := (2 : ℚ) ^ x.2 * (x.1.1 - (x.1.2 : ℚ) * (M : ℚ))
      have hfl : ((Rat.floor ql : ℤ) : ℝ) ≤ (ql : ℝ) := by exact_mod_cast Int.floor_le ql
      have hql : (ql : ℝ) ≤ target x := by
        dsimp only [ql, target]; push_cast
        exact mul_le_mul_of_nonneg_left (by nlinarith) h2pos
      have hcast : (lo0 x : ℝ) = ((Rat.floor ql : ℤ) : ℝ) - 1 := by
        dsimp only [lo0]; push_cast; ring
      linarith
    have hlt_hi : target x < (hi0 x : ℝ) := by
      let qh : ℚ := (2 : ℚ) ^ x.2 * (x.1.1 + (x.1.2 : ℚ) * (M : ℚ))
      have hfl : (qh : ℝ) < ((Rat.floor qh : ℤ) : ℝ) + 1 := by
        exact_mod_cast Int.lt_floor_add_one qh
      have hqh : target x ≤ (qh : ℝ) := by
        dsimp only [qh, target]; push_cast
        exact mul_le_mul_of_nonneg_left (by nlinarith) h2pos
      have hcast : (hi0 x : ℝ) = ((Rat.floor qh : ℤ) : ℝ) + 2 := by
        dsimp only [hi0]; push_cast; ring
      linarith
    have hfl_ge : lo0 x ≤ Int.floor (target x) := Int.le_floor.mpr hlo_le
    have hfl_lt : Int.floor (target x) < hi0 x := by
      by_contra hge
      have hle : (hi0 x : ℝ) ≤ (Int.floor (target x) : ℝ) := by exact_mod_cast not_lt.mp hge
      linarith [Int.floor_le (target x)]
    have hsz : (hi0 x - lo0 x).toNat ≤ 2 ^ count x := by
      have heq : (hi0 x - lo0 x).toNat = (hi0 x - lo0 x).natAbs := by omega
      rw [heq]; exact (Nat.lt_size_self _).le
    exact ⟨le_rfl, hfl_ge, hfl_lt, le_rfl, by simpa using hsz⟩
  have hpres : ∀ x i st, i < count x → inv x i st → inv x (i + 1) (step x st) := by
    intro x i st hi ⟨h1, h2, h3, h4, h5⟩
    have hpow : 2 ^ (count x - i) = 2 * 2 ^ (count x - (i + 1)) := by
      rw [show count x - i = (count x - (i + 1)) + 1 by omega, pow_succ']
    set m := midFn st
    have hmb : st.1 ≤ m ∧ m ≤ st.2 ∧ (st.2 - m).toNat ≤ 2 ^ (count x - (i + 1)) ∧
        (m - st.1).toNat ≤ 2 ^ (count x - (i + 1)) := by dsimp only [m, midFn]; omega
    have hstep_eq : step x st =
        if decide ((m : ℝ) ≤ target x) then (m, st.2) else (st.1, m) := rfl
    rw [hstep_eq]
    by_cases hcmp : (m : ℝ) ≤ target x
    · rw [decide_eq_true hcmp]; simp only [↓reduceIte]
      exact ⟨h1.trans hmb.1, Int.le_floor.mpr hcmp, h3, h4, hmb.2.2.1⟩
    · rw [decide_eq_false hcmp]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hlt_m : Int.floor (target x) < m := by
        by_contra hge
        exact hcmp (le_trans (by exact_mod_cast not_lt.mp hge) (Int.floor_le (target x)))
      exact ⟨h1, h2, hlt_m, hmb.2.1.trans h4, hmb.2.2.2⟩
  let boundFn : (ℚ × ℕ) × ℕ → ℕ := fun x =>
    3 * ((encIntBin (lo0 x)).length + (encIntBin (hi0 x)).length) + 5
  have hpolyB : PolyBounded (fun x => (encRatBinUnary x).length) boundFn :=
    ((PolyBounded.const 3).mul (hlo0.polyBounded_length.add hhi0.polyBounded_length)).add
      (.const 5)
  have hbound : ∀ x i st, i ≤ count x → inv x i st →
      (encPair encIntBin encIntBin st).length ≤ boundFn x := by
    intro x _ st _ ⟨h1, h2, h3, h4, _⟩
    have habs1 : st.1.natAbs ≤ max (lo0 x).natAbs (hi0 x).natAbs := by omega
    have habs2 : st.2.natAbs ≤ max (lo0 x).natAbs (hi0 x).natAbs := by omega
    have hsz_max : (max (lo0 x).natAbs (hi0 x).natAbs).size ≤
        (lo0 x).natAbs.size + (hi0 x).natAbs.size := by
      rcases le_total (lo0 x).natAbs (hi0 x).natAbs with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    have hs1 := (Nat.size_le_size habs1).trans hsz_max
    have hs2 := (Nat.size_le_size habs2).trans hsz_max
    simp only [boundFn, length_encPair, length_encIntBin]
    omega
  obtain ⟨hloop, hpost⟩ :=
    iterateWith_spec id' hcount (hlo0.prod hhi0) hstep inv hbase hpres hpolyB hbound
  refine hloop.fst'.of_enc_eq fun x => congrArg encIntBin ?_
  obtain ⟨_, hle, hlt, _, hgap⟩ := hpost x
  simp only [Nat.sub_self, pow_zero] at hgap
  dsimp only [target] at hle hlt
  omega

end Turing.MultiTapeTM.ComputableInPolyTime
