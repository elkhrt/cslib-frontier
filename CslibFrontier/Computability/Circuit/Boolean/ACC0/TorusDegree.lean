/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.TorusPolynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0
import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Collapse
import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Mobius
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Polynomial
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import CslibFrontier.Foundations.Data.Polynomial.ModulusAmplifier
import CslibFrontier.Foundations.Data.Polynomial.ParityAmplifier
import CslibFrontier.Probability.SmallBias.Powering
import Mathlib.Algebra.Order.Round

/-!
# Polylogarithmic Torus Polynomial Approximations for Conjunction and `ACC⁰`

This module proves polylogarithmic upper bounds on the torus approximation degree of conjunction
and constant-depth modular Boolean circuits (`ACC⁰`):

1. Converting seeded binary-field disjunction polynomials into torus polynomials via parity
   amplification yields `torusDegree ε (andBool n) ≤ 10 * (Real.logb 2 (n / ε)) ^ 2` for all
   `n ≥ 1` and `0 < ε < 1 / 4`.
2. Telescoping torus collapse of prime-modulus polynomial towers shows that every language
   `L ∈ ACC⁰` has polylogarithmic torus approximation degree at arbitrary inverse-polynomial error
   `ε ≥ 1 / n ^ k`, so any super-polylogarithmic torus degree lower bound for `MAJORITY` at
   inverse-polynomial error implies `MAJORITY ∉ ACC⁰` (`BarringtonConjecture`).

## Main definitions

* `CslibFrontier.TorusPolynomial.andBool`: the `n`-bit conjunction Boolean function
  `threshold n n`.
* `CslibFrontier.TorusPolynomial.BarringtonConjecture`: the conjecture `MAJORITY ∉ ACC⁰`.

## Main results

* `CslibFrontier.TorusPolynomial.torusDegree_andBool_le_of_pow`,
  `CslibFrontier.TorusPolynomial.torusDegree_andBool_le_logb_sq`: `O(log₂²(n / ε))` torus degree
  upper bound for `n`-bit conjunction.
* `CslibFrontier.TorusPolynomial.torusDegree_circuit_le`: explicit torus degree upper bound for a
  single `AC⁰[m]` circuit at error `2 ^ (-e)`.
* `CslibFrontier.TorusPolynomial.exists_polylog_torusDegree_of_mem_ACC0`: every language in `ACC⁰`
  has polylogarithmic torus degree for arbitrary inverse-polynomial error.
* `CslibFrontier.TorusPolynomial.barringtonConjecture_of_not_polylog`: super-polylogarithmic torus
  degree lower bounds for `MAJORITY` at inverse-polynomial error imply `MAJORITY ∉ ACC⁰`.
-/

public section

namespace CslibFrontier.TorusPolynomial

open Finset Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean

/-- Cast an integer low-degree function on the Boolean cube to a real low-degree function of the
same degree. -/
private lemma intCast_mem_lowDegree {T : Type*} {D : ℕ} {g : (T → Bool) → ℤ}
    (hg : g ∈ lowDegree ℤ T D) :
    (fun v ↦ (g v : ℝ)) ∈ lowDegree ℝ T D := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      have heq : (fun v : T → Bool ↦ (BitString.monomial ℤ S v : ℝ)) = BitString.monomial ℝ S := by
        funext v
        simp [BitString.monomial_apply]
      rw [heq]
      exact monomial_mem_lowDegree hS
  | zero =>
      convert (lowDegree ℝ T D).zero_mem using 1
      funext v
      simp
  | add f₁ f₂ _ _ h₁ h₂ =>
      convert Submodule.add_mem _ h₁ h₂ using 1
      funext v
      exact Int.cast_add _ _
  | smul c f _ hf =>
      convert Submodule.smul_mem _ (c : ℝ) hf using 1
      funext v
      simp [smul_eq_mul]

/-- The `n`-bit conjunction Boolean function `AND_n = threshold n n`. -/
@[expose]
def andBool (n : ℕ) : BooleanFunction n := threshold n n

/-- `andBool n x` is `true` iff every bit of `x` is `true`. -/
theorem andBool_eq_true_iff {n : ℕ} {x : BitString n} :
    andBool n x = true ↔ ∀ i : Fin n, x i = true := by
  rw [andBool, threshold_self, decide_eq_true_iff]

/-- `andBool n` is symmetric. -/
theorem isSymmetric_andBool (n : ℕ) : (andBool n).IsSymmetric :=
  isSymmetric_threshold n

/-- **Seeded `𝔽₂` probabilistic polynomial upper bound for the torus degree of `AND_n`**
via seeded binary-field parity amplification. For every `n, κ : ℕ` with
`1 ≤ κ` and `(n - 1 : ℝ) ≤ ε * 2 ^ (κ + 1)`, we have
`torusDegree ε (andBool n) ≤ (2 * κ + 1) * κ`. -/
theorem torusDegree_andBool_le_of_pow {n κ : ℕ} (hκ : 1 ≤ κ) {ε : ℝ}
    (hε : ((n - 1 : ℕ) : ℝ) ≤ ε * (2 : ℝ) ^ (κ + 1)) :
    torusDegree ε (andBool n) ≤ (2 * κ + 1) * κ := by
  let F := Cslib.BinaryField κ
  have hcard : Fintype.card F = 2 ^ κ := Cslib.BinaryField.card (by omega)
  let b : Module.Basis (Fin κ) (ZMod 2) F := Cslib.BinaryField.basis (by omega)
  let qr : F → BitString n → ℤ := fun r x ↦
    orTest b (fun i : Fin n ↦ r ^ (i : ℕ)) univ (fun i ↦ !x i)
  let hr : F → BitString n → ℤ := fun r x ↦
    1 - (Polynomial.parityAmplifier (κ + 1)).eval (qr r x)
  have hqr_deg : ∀ r : F, qr r ∈ lowDegree ℤ (Fin n) κ := fun r ↦ by
    simpa using orTest_mem_lowDegree b (fun i : Fin n ↦ r ^ (i : ℕ)) univ
      (g := fun i (x : BitString n) ↦ !x i)
      (fun i _ ↦ comp_not_mem_lowDegree (bitVal_mem_lowDegree i))
  have hamp_deg : (Polynomial.parityAmplifier (κ + 1)).natDegree ≤ 2 * κ + 1 := by
    have h := Polynomial.natDegree_parityAmplifier_le (κ + 1)
    omega
  have hhr_deg : ∀ r : F, hr r ∈ lowDegree ℤ (Fin n) ((2 * κ + 1) * κ) := fun r ↦
    one_sub_mem_lowDegree (polynomial_eval_mem_lowDegree (hqr_deg r) hamp_deg)
  let p : BitString n → ℝ := fun x ↦
    (1 / 2 : ℝ) - ((2 : ℝ) ^ (κ + 1))⁻¹ * ∑ r : F, (hr r x : ℝ)
  have hp_deg : p ∈ lowDegree ℝ (Fin n) ((2 * κ + 1) * κ) := by
    refine Submodule.sub_mem _ (const_mem_lowDegree _ (1 / 2)) ?_
    refine Submodule.smul_mem _ (((2 : ℝ) ^ (κ + 1))⁻¹) ?_
    have hsum_mem : (∑ r : F, fun x : BitString n ↦ (hr r x : ℝ)) ∈
        lowDegree ℝ (Fin n) ((2 * κ + 1) * κ) :=
      sum_mem_lowDegree univ fun r _ ↦ intCast_mem_lowDegree (hhr_deg r)
    convert hsum_mem using 1
    funext x
    simp [Finset.sum_apply]
  refine torusDegree_le_of_mem_lowDegree hp_deg fun x ↦ ?_
  classical
  let bit : F → ℤ := fun r ↦ if qr r x % 2 = 0 then 0 else 1
  have hmod : ∀ r : F, ∃ m : ℤ, hr r x = bit r + (2 : ℤ) ^ (κ + 1) * m := by
    intro r
    have hpa := Polynomial.parityAmplifier_eval_modEq_two_pow (show 1 ≤ κ + 1 by omega) (qr r x)
    have heven : Even (qr r x) ↔ qr r x % 2 = 0 := Int.even_iff
    have h1 : hr r x ≡ bit r [ZMOD (2 : ℤ) ^ (κ + 1)] := by
      have hsub := Int.ModEq.sub (Int.ModEq.refl (1 : ℤ)) hpa
      convert hsub using 1
      by_cases h0 : qr r x % 2 = 0
      · simp [bit, h0, heven.mpr h0]
      · have hne : ¬Even (qr r x) := fun he ↦ h0 (heven.mp he)
        have h1' : qr r x % 2 = 1 := by omega
        simp [bit, h1', hne]
    obtain ⟨m, hm⟩ := Int.modEq_iff_add_fac.mp h1.symm
    exact ⟨m, hm⟩
  choose m hm using hmod
  refine ⟨-(∑ r : F, m r), ?_⟩
  have hpow_ne : ((2 : ℝ) ^ (κ + 1)) ≠ 0 := by positivity
  have hsimp : p x - bitVal ℝ (andBool n x) / 2 - ((-(∑ r : F, m r) : ℤ) : ℝ) =
      (1 / 2 - bitVal ℝ (andBool n x) / 2) -
        ((2 : ℝ) ^ (κ + 1))⁻¹ * ∑ r : F, (bit r : ℝ) := by
    have hsum : ∑ r : F, (hr r x : ℝ) =
        (∑ r : F, (bit r : ℝ)) + (2 : ℝ) ^ (κ + 1) * ∑ r : F, (m r : ℝ) := by
      simp only [hm, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [p, hsum, mul_add, inv_mul_cancel_left₀ hpow_ne, Int.cast_neg, Int.cast_sum]
    ring
  rw [hsimp]
  have hbit_iff : ∀ r : F, qr r x % 2 ≠ 0 ↔ ∑ i ∈ univ.filter (fun i : Fin n ↦ x i = false),
      r ^ (i : ℕ) ≠ 0 := by
    intro r
    simpa [qr] using orTest_emod_two_ne_zero_iff b (fun i : Fin n ↦ r ^ (i : ℕ)) univ (fun i ↦ !x i)
  by_cases hand : andBool n x = true
  · have hall := andBool_eq_true_iff.mp hand
    have hfilt : (univ.filter fun i : Fin n ↦ x i = false) = ∅ := by
      rw [filter_eq_empty_iff]
      intro i _; simp [hall i]
    have hsum0 : ∑ r : F, (bit r : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun r _ ↦ ?_
      have h0 : qr r x % 2 = 0 := by
        by_contra hne
        have := (hbit_iff r).mp hne
        simp [hfilt] at this
      simp [bit, h0]
    have hε0 : 0 ≤ ε := by
      have : (0 : ℝ) ≤ ε * (2 : ℝ) ^ (κ + 1) := (Nat.cast_nonneg _).trans hε
      exact nonneg_of_mul_nonneg_left this (by positivity)
    simpa [hand, bitVal, hsum0] using hε0
  · have hfalse : andBool n x = false := Bool.eq_false_iff.mpr hand
    have hne : (univ.filter fun i : Fin n ↦ x i = false).Nonempty := by
      rw [filter_nonempty_iff]
      by_contra hno
      push Not at hno
      exact hand
        (andBool_eq_true_iff.mpr fun i ↦ Bool.eq_true_of_not_eq_false (hno i (mem_univ i)))
    let bad : Finset F := univ.filter fun r : F ↦
      ∑ i ∈ univ.filter (fun i : Fin n ↦ x i = false), r ^ (i : ℕ) = 0
    have hbad : #bad ≤ n - 1 := card_filter_sum_pow_eq_zero_le (F := F) hne
    have hgood_sum : ∑ r : F, (bit r : ℝ) = ((Fintype.card F - #bad : ℕ) : ℝ) := by
      have h1 : ∑ r : F, (bit r : ℝ) = (#(univ.filter fun r : F ↦ r ∉ bad) : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        by_cases hr : r ∈ bad
        · have h0 : qr r x % 2 = 0 := by
            by_contra hne'
            exact (hbit_iff r).mp hne' (mem_filter.mp hr).2
          simp [bit, hr, h0]
        · have hne' : qr r x % 2 ≠ 0 := by
            rw [hbit_iff]
            intro hs
            exact hr (mem_filter.mpr ⟨mem_univ r, hs⟩)
          have h1' : qr r x % 2 = 1 := by omega
          simp [bit, hr, h1']
      rw [h1]
      congr 2
      have hcompl : (univ.filter fun r : F ↦ r ∉ bad) = badᶜ := by ext r; simp
      rw [hcompl, card_compl]
    have hbad_le_card : #bad ≤ Fintype.card F := card_le_univ bad
    have hval : (1 / 2 : ℝ) - ((2 : ℝ) ^ (κ + 1))⁻¹ * ((Fintype.card F - #bad : ℕ) : ℝ) =
        (#bad : ℝ) / (2 : ℝ) ^ (κ + 1) := by
      rw [Nat.cast_sub hbad_le_card, hcard, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      ring
    rw [hfalse, bitVal, hgood_sum]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_div, sub_zero, hval]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    exact (Nat.cast_le.mpr hbad).trans hε

/-- **Asymmetric torus degree upper bound for `AND_n`**: for every `n ≥ 1` and every
`0 < ε < 1 / 4`, `torusDegree ε (andBool n) ≤ 10 * (Real.logb 2 (n / ε)) ^ 2`. -/
theorem torusDegree_andBool_le_logb_sq {n : ℕ} (hn : 1 ≤ n) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    (torusDegree ε (andBool n) : ℝ) ≤ 10 * (Real.logb 2 ((n : ℝ) / ε)) ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hratio_gt : (4 : ℝ) < (n : ℝ) / ε := by
    rw [lt_div_iff₀ hε0]
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog_gt : (2 : ℝ) < Real.logb 2 ((n : ℝ) / ε) := by
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    calc (2 : ℝ) = Real.logb 2 (4 : ℝ) := h4.symm
      _ < Real.logb 2 ((n : ℝ) / ε) := Real.logb_lt_logb (by norm_num) (by norm_num) hratio_gt
  let κ : ℕ := ⌊Real.logb 2 ((n : ℝ) / ε)⌋₊ + 1
  have hκ1 : 1 ≤ κ := Nat.succ_pos _
  have hpow : (n : ℝ) / ε ≤ (2 : ℝ) ^ κ := by
    have hlt : Real.logb 2 ((n : ℝ) / ε) < (κ : ℝ) := by
      simpa [κ] using Nat.lt_floor_add_one (Real.logb 2 ((n : ℝ) / ε))
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
        (by positivity : 0 < (n : ℝ) / ε),
      ← Real.rpow_natCast]
    exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt).le
  have hcond : ((n - 1 : ℕ) : ℝ) ≤ ε * (2 : ℝ) ^ (κ + 1) := by
    have h1 : (n : ℝ) ≤ (2 : ℝ) ^ κ * ε := (div_le_iff₀ hε0).mp hpow
    have h2 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have h3 : (2 : ℝ) ^ κ * ε ≤ ε * (2 : ℝ) ^ (κ + 1) := by
      have hpos : 0 < (2 : ℝ) ^ κ * ε := by positivity
      have heq : ε * (2 : ℝ) ^ (κ + 1) = 2 * ((2 : ℝ) ^ κ * ε) := by rw [pow_succ]; ring
      linarith
    exact h2.trans (h1.trans h3)
  have hdeg := torusDegree_andBool_le_of_pow hκ1 hcond
  have hκ_le : (κ : ℝ) ≤ (3 / 2 : ℝ) * Real.logb 2 ((n : ℝ) / ε) := by
    have hfl : (⌊Real.logb 2 ((n : ℝ) / ε)⌋₊ : ℝ) ≤ Real.logb 2 ((n : ℝ) / ε) :=
      Nat.floor_le (by linarith)
    simp only [κ, Nat.cast_add, Nat.cast_one]
    linarith
  calc (torusDegree ε (andBool n) : ℝ)
      ≤ (((2 * κ + 1) * κ : ℕ) : ℝ) := Nat.cast_le.mpr hdeg
    _ = (2 * (κ : ℝ) + 1) * (κ : ℝ) := by push_cast; ring
    _ ≤ 10 * (Real.logb 2 ((n : ℝ) / ε)) ^ 2 := by nlinarith

/-- One step of collapsing a prime-modulus polynomial layer into a scaled torus approximation of a
`SymAnd` gate count. -/
private lemma torus_collapse_step {T : Type*} [Fintype T]
    (C : SymAnd T) (L : ModPolyLayer T) {B F S : ℕ} (_hB : 2 ≤ B)
    (hp : L.p.Prime) (hpB : L.p ≤ B) (hq : ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B) (hF : C.fanIn ≤ F) (hS : C.size ≤ 2 ^ S)
    (α : ℝ) (e : ℕ) :
    ∃ (C' : SymAnd T) (α' : ℝ),
      C'.fanIn ≤ 2 * (S + e + 1) * B ^ 2 * F ∧
      C'.size ≤ 2 ^ (B * (S + e + 1 + 2 * (S + e + 1) * B ^ 2 * F)) ∧
      ∀ w : T → Bool, ∃ z : ℤ,
        |α' * (C'.count w : ℝ) - α * (C.count (L.step w) : ℝ) - (z : ℝ)| ≤
          ((2 : ℝ) ^ (e + 1))⁻¹ := by
  classical
  let k : ℕ := S + e + 1
  let M : ℕ := L.p ^ k
  have hp2 : 2 ≤ L.p := hp.two_le
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have h2k_le_M : 2 ^ k ≤ M := Nat.pow_le_pow_left hp2 k
  let D' : ℕ := C.fanIn * ((2 * k - 1) * ((L.p - 1) * B))
  have hD'_le : D' ≤ 2 * (S + e + 1) * B ^ 2 * F := by
    have hk1 : 2 * k - 1 ≤ 2 * k := Nat.sub_le _ _
    have hp1 : L.p - 1 ≤ B := (Nat.sub_le _ _).trans hpB
    calc D' ≤ F * ((2 * k) * (B * B)) :=
          Nat.mul_le_mul hF (Nat.mul_le_mul hk1 (Nat.mul_le_mul_right B hp1))
      _ = 2 * (S + e + 1) * B ^ 2 * F := by simp [k]; ring
  let A : (T → Bool) → ℤ := SymAnd.amplifiedCount C L k
  have hA_deg : A ∈ lowDegree ℤ T D' := SymAnd.amplifiedCount_mem_lowDegree C L hq k
  let C' : SymAnd T := SymAnd.ofLowDegree D' M A (fun _ ↦ false)
  let q_int : ℤ := round (α * (M : ℝ))
  let α' : ℝ := (q_int : ℝ) / (M : ℝ)
  have hM_real : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hC'_fan : C'.fanIn ≤ 2 * (S + e + 1) * B ^ 2 * F :=
    (SymAnd.fanIn_ofLowDegree_le D' M A _).trans hD'_le
  have hC'_size : C'.size ≤ 2 ^ (B * (S + e + 1 + 2 * (S + e + 1) * B ^ 2 * F)) := by
    have hMp : M ≤ 2 ^ (B * k) := by
      have hp_pow : L.p ≤ 2 ^ B := hpB.trans Nat.lt_two_pow_self.le
      calc M = L.p ^ k := rfl
        _ ≤ (2 ^ B) ^ k := Nat.pow_le_pow_left hp_pow k
        _ = 2 ^ (B * k) := (pow_mul 2 B k).symm
    calc C'.size
        ≤ M * (Fintype.card T + 1) ^ D' := SymAnd.size_ofLowDegree_le D' hM_pos A _
      _ ≤ 2 ^ (B * k) * (2 ^ B) ^ (2 * (S + e + 1) * B ^ 2 * F) :=
          Nat.mul_le_mul hMp ((Nat.pow_le_pow_left hT D').trans
            (Nat.pow_le_pow_right (by norm_num) hD'_le))
      _ = 2 ^ (B * (S + e + 1 + 2 * (S + e + 1) * B ^ 2 * F)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          simp [k]; ring
  refine ⟨C', α', hC'_fan, hC'_size, fun w ↦ ?_⟩
  have hmod1 : (C'.count w : ℤ) ≡ A w [ZMOD (M : ℤ)] :=
    SymAnd.natCast_count_ofLowDegree_modEq hA_deg hM_pos _ w
  have hmod2 : A w ≡ (C.count (L.step w) : ℤ) [ZMOD (M : ℤ)] :=
    SymAnd.amplifiedCount_modEq C L hp k w
  obtain ⟨u, hu⟩ := Int.modEq_iff_add_fac.mp (hmod1.trans hmod2).symm
  refine ⟨q_int * u, ?_⟩
  have hu_real : (C'.count w : ℝ) = (C.count (L.step w) : ℝ) + (M : ℝ) * (u : ℝ) := by
    exact_mod_cast hu
  have hdiff : α' * (C'.count w : ℝ) - α * (C.count (L.step w) : ℝ) - ((q_int * u : ℤ) : ℝ) =
      ((q_int : ℝ) - α * (M : ℝ)) / (M : ℝ) * (C.count (L.step w) : ℝ) := by
    simp only [α', hu_real, Int.cast_mul]
    field_simp
    ring
  have hcnt_nn : (0 : ℝ) ≤ (C.count (L.step w) : ℝ) := Nat.cast_nonneg _
  rw [hdiff, abs_mul, abs_div, abs_of_pos hM_real, abs_of_nonneg hcnt_nn]
  have hround : |(q_int : ℝ) - α * (M : ℝ)| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round _
  have hcnt : (C.count (L.step w) : ℝ) ≤ (2 : ℝ) ^ S := by
    have h1 : C.count (L.step w) ≤ C.size := by
      unfold SymAnd.count SymAnd.size
      exact @Multiset.countP_le_card _ _ (fun _ ↦ Finset.decidableDforallFinset) C.gates
    exact_mod_cast h1.trans hS
  have hM_ge : (2 : ℝ) ^ S * (2 : ℝ) ^ (e + 1) ≤ (M : ℝ) := by
    have hnat : 2 ^ S * 2 ^ (e + 1) ≤ M := by
      have heq : 2 ^ S * 2 ^ (e + 1) = 2 ^ k := by
        rw [← pow_add]
        rfl
      exact heq ▸ h2k_le_M
    exact_mod_cast hnat
  calc |(q_int : ℝ) - α * (M : ℝ)| / (M : ℝ) * (C.count (L.step w) : ℝ)
      ≤ (1 / 2) / (M : ℝ) * (2 : ℝ) ^ S := by gcongr
    _ ≤ (1 / 2) * ((2 : ℝ) ^ (e + 1))⁻¹ := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        gcongr
        rw [div_le_iff₀ hM_real, inv_mul_eq_div, le_div_iff₀ (by positivity)]
        exact hM_ge
    _ ≤ ((2 : ℝ) ^ (e + 1))⁻¹ := by
        have : (0 : ℝ) ≤ ((2 : ℝ) ^ (e + 1))⁻¹ := by positivity
        linarith

/-- Recursive polylogarithmic fan-in and log-size envelope `(4 * B) ^ (5 ^ t)` across a tower of
`t` prime-modulus polynomial layers. -/
private lemma torus_collapse_run {T : Type*} [Fintype T]
    (C : SymAnd T) (Ls : List (ModPolyLayer T)) (B : ℕ) (hB : 2 ≤ B)
    (hLs : ∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B)
    (hT : Fintype.card T + 1 ≤ 2 ^ B)
    (hF : C.fanIn ≤ B) (hS : C.size ≤ 2 ^ B)
    (α : ℝ) (e : ℕ) (he : e + Ls.length ≤ B) :
    ∃ p ∈ lowDegree ℝ T ((4 * B) ^ (5 ^ Ls.length)),
      ∀ v : T → Bool, ∃ z : ℤ,
        |p v - α * (C.count (ModPolyLayer.run Ls v) : ℝ) - (z : ℝ)| ≤
          ((2 : ℝ) ^ e)⁻¹ := by
  classical
  suffices hgen : ∀ (Ls : List (ModPolyLayer T)) (C : SymAnd T) (K : ℕ) (α : ℝ) (e : ℕ),
      B ≤ K →
      (∀ L ∈ Ls, L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ T B) →
      C.fanIn ≤ K → C.size ≤ 2 ^ K → e + Ls.length ≤ K →
      ∃ p ∈ lowDegree ℝ T ((4 * K) ^ (5 ^ Ls.length)),
        ∀ v : T → Bool, ∃ z : ℤ,
          |p v - α * (C.count (ModPolyLayer.run Ls v) : ℝ) - (z : ℝ)| ≤ ((2 : ℝ) ^ e)⁻¹ from
    hgen Ls C B α e le_rfl hLs hF hS he
  intro Ls'
  induction Ls' with
  | nil =>
      intro C₀ K α₀ e₀ hBK _ hF₀ _ _
      have hcnt_deg : (fun v : T → Bool ↦ (C₀.count v : ℝ)) ∈ lowDegree ℝ T C₀.fanIn := by
        have hZ : (fun v : T → Bool ↦ (C₀.count v : ℤ)) ∈ lowDegree ℤ T C₀.fanIn := by
          have heq : (fun v : T → Bool ↦ (C₀.count v : ℤ)) =
              fun v ↦ (C₀.gates.map fun S ↦ BitString.monomial ℤ S v).sum :=
            funext fun v ↦ SymAnd.natCast_count_eq_sum C₀ v
          rw [heq]
          suffices hmult : ∀ G : Multiset (Finset T), (∀ S ∈ G, #S ≤ C₀.fanIn) →
              (fun v : T → Bool ↦ (G.map fun S ↦ BitString.monomial ℤ S v).sum) ∈
                lowDegree ℤ T C₀.fanIn from
            hmult C₀.gates fun _ hS ↦ SymAnd.card_le_fanIn hS
          intro G
          induction G using Multiset.induction_on with
          | empty => intro _; exact (lowDegree ℤ T C₀.fanIn).zero_mem
          | cons S G' ihG =>
              intro hcard
              have hadd := Submodule.add_mem _
                (monomial_mem_lowDegree (R := ℤ) (hcard S (Multiset.mem_cons_self S G')))
                (ihG fun S' hS' ↦ hcard S' (Multiset.mem_cons_of_mem hS'))
              convert hadd using 1
              funext v
              simp
        exact intCast_mem_lowDegree hZ
      refine ⟨fun v ↦ α₀ * (C₀.count v : ℝ),
        lowDegree_mono (by simp; omega) (Submodule.smul_mem _ α₀ hcnt_deg),
        fun v ↦ ⟨0, by simp⟩⟩
  | cons L Ls'' ih =>
      intro C₀ K α₀ e₀ hBK hLs' hF₀ hS₀ he₀
      have hK2 : 2 ≤ K := hB.trans hBK
      obtain ⟨hp, hpB, hq⟩ := hLs' L List.mem_cons_self
      obtain ⟨C', α', hC'_fan, hC'_size, hstep⟩ :=
        torus_collapse_step C₀ L hB hp hpB hq hT hF₀ hS₀ α₀ e₀
      let K' : ℕ := 6 * K ^ 5
      have hke : K + e₀ + 1 ≤ 2 * K := by simp [List.length_cons] at he₀; omega
      have hfan_le : 2 * (K + e₀ + 1) * B ^ 2 * K ≤ 4 * K ^ 4 := by
        calc 2 * (K + e₀ + 1) * B ^ 2 * K
            ≤ 2 * (2 * K) * K ^ 2 * K :=
              Nat.mul_le_mul_right K
                (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hke) (Nat.pow_le_pow_left hBK 2))
          _ = 4 * K ^ 4 := by ring
      have hK4_le_K5 : K ^ 4 ≤ K ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hK2_le_K5 : K ^ 2 ≤ K ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hK1_le_K5 : K ≤ K ^ 5 := by
        simpa using Nat.pow_le_pow_right (show 1 ≤ K by omega) (show 1 ≤ 5 by norm_num)
      have hfan_K' : C'.fanIn ≤ K' := by
        refine hC'_fan.trans (hfan_le.trans ?_)
        change 4 * K ^ 4 ≤ 6 * K ^ 5
        omega
      have hsize_K' : C'.size ≤ 2 ^ K' := by
        refine hC'_size.trans (Nat.pow_le_pow_right (by norm_num) ?_)
        calc B * (K + e₀ + 1 + 2 * (K + e₀ + 1) * B ^ 2 * K)
            ≤ K * (2 * K + 4 * K ^ 4) :=
              Nat.mul_le_mul hBK (Nat.add_le_add hke hfan_le)
          _ = 2 * K ^ 2 + 4 * K ^ 5 := by ring
          _ ≤ 6 * K ^ 5 := by omega
      have hBK' : B ≤ K' := hBK.trans (hK1_le_K5.trans (by change K ^ 5 ≤ 6 * K ^ 5; omega))
      have heK' : (e₀ + 1) + Ls''.length ≤ K' := by
        have h1 : (e₀ + 1) + Ls''.length = e₀ + (L :: Ls'').length := by simp; omega
        rw [h1]
        exact he₀.trans (hK1_le_K5.trans (by change K ^ 5 ≤ 6 * K ^ 5; omega))
      obtain ⟨p, hp_deg, hp_approx⟩ := ih C' K' α' (e₀ + 1) hBK'
        (fun L' hL' ↦ hLs' L' (List.mem_cons_of_mem L hL')) hfan_K' hsize_K' heK'
      have hdeg_le : (4 * K') ^ (5 ^ Ls''.length) ≤ (4 * K) ^ (5 ^ (L :: Ls'').length) := by
        have h4K' : 4 * K' ≤ (4 * K) ^ 5 := by
          have : 24 * K ^ 5 ≤ 1024 * K ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
          calc 4 * K' = 24 * K ^ 5 := by simp [K']; ring
            _ ≤ 1024 * K ^ 5 := this
            _ = (4 * K) ^ 5 := by ring
        calc (4 * K') ^ (5 ^ Ls''.length)
            ≤ ((4 * K) ^ 5) ^ (5 ^ Ls''.length) := Nat.pow_le_pow_left h4K' _
          _ = (4 * K) ^ (5 * 5 ^ Ls''.length) := (pow_mul _ _ _).symm
          _ = (4 * K) ^ (5 ^ (L :: Ls'').length) := by
              congr 1; simp [List.length_cons, pow_succ, mul_comm]
      refine ⟨p, lowDegree_mono hdeg_le hp_deg, fun v ↦ ?_⟩
      obtain ⟨z₁, hz₁⟩ := hp_approx v
      obtain ⟨z₂, hz₂⟩ := hstep (ModPolyLayer.run Ls'' v)
      refine ⟨z₁ + z₂, ?_⟩
      simp only [ModPolyLayer.run_cons, Int.cast_add]
      calc |p v - α₀ * (C₀.count (L.step (ModPolyLayer.run Ls'' v)) : ℝ) - ((z₁ : ℝ) + (z₂ : ℝ))|
          = |(p v - α' * (C'.count (ModPolyLayer.run Ls'' v) : ℝ) - (z₁ : ℝ)) +
              (α' * (C'.count (ModPolyLayer.run Ls'' v) : ℝ) -
                α₀ * (C₀.count (L.step (ModPolyLayer.run Ls'' v)) : ℝ) - (z₂ : ℝ))| := by
            ring_nf
        _ ≤ |p v - α' * (C'.count (ModPolyLayer.run Ls'' v) : ℝ) - (z₁ : ℝ)| +
              |α' * (C'.count (ModPolyLayer.run Ls'' v) : ℝ) -
                α₀ * (C₀.count (L.step (ModPolyLayer.run Ls'' v)) : ℝ) - (z₂ : ℝ)| :=
            abs_add_le _ _
        _ ≤ ((2 : ℝ) ^ (e₀ + 1))⁻¹ + ((2 : ℝ) ^ (e₀ + 1))⁻¹ := add_le_add hz₁ hz₂
        _ = ((2 : ℝ) ^ e₀)⁻¹ := by rw [pow_succ]; field_simp; ring

/-- Explicit torus degree upper bound for a single `AC⁰[m]` circuit `C` (`m > 0`) at error
`2 ^ (-e)`: `torusDegree (2 ^ (-e)) f ≤ (4 * B) ^ (5 ^ (C.depth * (m + 2)))` where
`B = 4 * ((m + 1) ^ 2 + ⌊log₂ (n + C.size)⌋ + e + C.depth * (m + 2) + 2)`. -/
theorem torusDegree_circuit_le {n : ℕ} (C : Circuit Unbounded.extSignature n 1)
    {m : ℕ} (hm : 0 < m) (e : ℕ) :
    torusDegree (((2 : ℝ) ^ e)⁻¹)
      (fun x ↦ C.eval (Unbounded.extInterpretation (modGate m)) x 0) ≤
      (4 * (4 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2))) ^
        (5 ^ (C.depth * (m + 2))) := by
  classical
  open ACC0ToSymAnd in
  set ℓ : ℕ := Nat.log 2 (n + C.size) + e + 2
  have hN : n + C.size < 2 ^ (Nat.log 2 (n + C.size) + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two _
  have hNℓ : n + C.size < 2 ^ ℓ :=
    hN.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  set B : ℕ := 4 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2)
  have hB2 : 2 ≤ B := by omega
  have hBℓ : 3 * ℓ + 2 + (m + 1) ^ 2 ≤ B := by omega
  let Ls := (towerS C.program m ℓ C.depth).map SLayer.lift
  have hlen : Ls.length ≤ C.depth * (m + 2) := by
    simp only [Ls, List.length_map, length_towerS]
    exact Nat.mul_le_mul_left _ (by have := length_primes_le m; omega)
  have hLs : ∀ L ∈ Ls,
      L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ (Seed ℓ × Slot n C.size m) B := by
    intro L hL
    obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.mp hL
    obtain ⟨hp, hpM, hq⟩ := layer_ok C.program hm (mem_macroS_of_mem_towerS C.program hL₀)
    have hmB : m + 2 ≤ B := by
      have : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
      omega
    exact ⟨hp, hpM.trans hmB, SLayer.lift_mem_lowDegree L₀ fun r s ↦
      lowDegree_mono (by omega) (hq r s)⟩
  have hT : Fintype.card (Seed ℓ × Slot n C.size m) + 1 ≤ 2 ^ B :=
    (card_seed_slot_lt (m := m) hNℓ).trans_le (Nat.pow_le_pow_right (by norm_num) hBℓ)
  let Ctop := top ℓ (Sum.inl (C.outputs 0) : Slot n C.size m)
  have hF : Ctop.fanIn ≤ B := (fanIn_top_le _).trans (by omega)
  have hS : Ctop.size ≤ 2 ^ B := by
    rw [size_top, Cslib.BinaryField.card (by omega)]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have heB : (e + 1) + Ls.length ≤ B := by omega
  let α : ℝ := ((2 : ℝ) * (Fintype.card (Seed ℓ) : ℝ))⁻¹
  obtain ⟨p, hp_deg, hp_approx⟩ :=
    torus_collapse_run Ctop Ls B hB2 hLs hT hF hS α (e + 1) heB
  let φ : BitString n → (Seed ℓ × Slot n C.size m → Bool) :=
    fun x t ↦ (slotInput t).elim false x
  have hφ : ∀ t, (fun x : BitString n ↦ bitVal ℝ (φ x t)) ∈ lowDegree ℝ (Fin n) 1 := by
    intro t
    cases h : slotInput t with
    | none => simpa [φ, h, bitVal] using const_mem_lowDegree (R := ℝ) (ι := Fin n) 1 0
    | some i => simpa [φ, h] using bitVal_mem_lowDegree (R := ℝ) i
  have hpx_deg : (fun x ↦ p (φ x)) ∈ lowDegree ℝ (Fin n)
      ((4 * B) ^ (5 ^ (C.depth * (m + 2)))) := by
    have hcomp : (fun x ↦ p (φ x)) ∈ lowDegree ℝ (Fin n) ((4 * B) ^ (5 ^ Ls.length)) := by
      refine Submodule.span_induction ?_ (lowDegree ℝ (Fin n) _).zero_mem
        (fun _ _ _ _ h₁ h₂ ↦ Submodule.add_mem _ h₁ h₂)
        (fun c _ _ hg ↦ Submodule.smul_mem _ c hg) hp_deg
      rintro _ ⟨S, hS, rfl⟩
      have hmon : (fun x : BitString n ↦ BitString.monomial ℝ S (φ x)) =
          ∏ t ∈ S, fun x : BitString n ↦ bitVal ℝ (φ x t) := by
        funext x
        simp [BitString.monomial, Finset.prod_apply]
      rw [hmon]
      exact lowDegree_mono (by simpa using hS) (prod_mem_lowDegree S fun t _ ↦ hφ t)
    exact lowDegree_mono
      (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) hlen)) hcomp
  refine torusDegree_le_of_mem_lowDegree hpx_deg fun x ↦ ?_
  obtain ⟨z, hz⟩ := hp_approx (φ x)
  refine ⟨z, ?_⟩
  set fx : Bool := C.eval (Unbounded.extInterpretation (modGate m)) x 0
  have hgood_eq : ∀ r : Seed ℓ, Good C.program m x r →
      ModPolyLayer.run Ls (φ x) (r, Sum.inl (C.outputs 0)) = fx := by
    intro r hr
    have h1 : ModPolyLayer.run Ls (φ x) (r, Sum.inl (C.outputs 0)) =
        ModPolyLayer.run ((towerS C.program m ℓ C.depth).map fun L ↦ L.atSeed r)
          (init x) (Sum.inl (C.outputs 0)) := by
      have := SLayer.run_lift (towerS C.program m ℓ C.depth) (φ x) r (Sum.inl (C.outputs 0))
      simpa only [Ls, φ, slotInput_elim] using this
    rw [h1]
    exact wiresOK_run_towerS C.program hm x hr C.depth _ (C.outputDepths_le_depth 0)
  have hbad_card : #{r : Seed ℓ | ¬Good C.program m x r} * 2 ^ (e + 1) ≤
      Fintype.card (Seed ℓ) := by
    rw [Cslib.BinaryField.card (by omega)]
    have h1 := card_not_good_le (ℓ := ℓ) C.program m x
    have h2 : C.size * (2 * (n + C.size)) ≤ 2 * (n + C.size) ^ 2 := by nlinarith
    have h3 : (n + C.size) ^ 2 ≤ (2 ^ (Nat.log 2 (n + C.size) + 1)) ^ 2 :=
      Nat.pow_le_pow_left hN.le 2
    calc #{r : Seed ℓ | ¬Good C.program m x r} * 2 ^ (e + 1)
        ≤ (2 * (2 ^ (Nat.log 2 (n + C.size) + 1)) ^ 2) * 2 ^ (e + 1) :=
          Nat.mul_le_mul_right _ (h1.trans (h2.trans (Nat.mul_le_mul_left 2 h3)))
      _ = 2 ^ (2 * Nat.log 2 (n + C.size) + e + 4) := by
          rw [← pow_mul]
          calc 2 * 2 ^ ((Nat.log 2 (n + C.size) + 1) * 2) * 2 ^ (e + 1)
              = 2 ^ 1 * 2 ^ ((Nat.log 2 (n + C.size) + 1) * 2) * 2 ^ (e + 1) := by rw [pow_one]
            _ = 2 ^ (1 + (Nat.log 2 (n + C.size) + 1) * 2 + (e + 1)) := by
                rw [← pow_add, ← pow_add]
            _ = 2 ^ (2 * Nat.log 2 (n + C.size) + e + 4) := by congr 1; omega
      _ ≤ 2 ^ (2 * ℓ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hseed_err :
      |α * (Ctop.count (ModPolyLayer.run Ls (φ x)) : ℝ) - bitVal ℝ fx / 2| ≤
        ((2 : ℝ) ^ (e + 1))⁻¹ := by
    rw [count_top]
    set M_seed : ℕ := Fintype.card (Seed ℓ)
    have hM_pos : (0 : ℝ) < (M_seed : ℝ) := by
      rw [show M_seed = 2 ^ (2 * ℓ + 2) from Cslib.BinaryField.card (by omega)]
      positivity
    set cnt : ℕ := #{r : Seed ℓ | ModPolyLayer.run Ls (φ x) (r, Sum.inl (C.outputs 0)) = true}
    set bad : ℕ := #{r : Seed ℓ | ¬Good C.program m x r}
    have hsplit : #{r : Seed ℓ | Good C.program m x r} + bad = M_seed := by
      simpa [bad, M_seed] using
        card_filter_add_card_filter_not (s := (univ : Finset (Seed ℓ))) (Good C.program m x)
    have hcnt_diff : |(cnt : ℝ) - bitVal ℝ fx * (M_seed : ℝ)| ≤ (bad : ℝ) := by
      cases hfx : fx with
      | false =>
          have hle : cnt ≤ bad := card_le_card fun r hr ↦ by
            simp only [mem_filter, mem_univ, true_and] at hr ⊢
            intro hg
            have := hgood_eq r hg
            rw [hfx, hr] at this
            exact Bool.noConfusion this
          have hcnt_nn : (0 : ℝ) ≤ (cnt : ℝ) := Nat.cast_nonneg _
          simp only [bitVal, Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero]
          rw [abs_of_nonneg hcnt_nn]
          exact_mod_cast hle
      | true =>
          have hge : #{r : Seed ℓ | Good C.program m x r} ≤ cnt := card_le_card fun r hr ↦ by
            simp only [mem_filter, mem_univ, true_and] at hr ⊢
            rw [hgood_eq r hr, hfx]
          have hle : cnt ≤ M_seed := card_le_univ _
          have h1 : (M_seed : ℝ) - (bad : ℝ) ≤ (cnt : ℝ) := by
            exact_mod_cast (by omega : (M_seed : ℤ) - bad ≤ cnt)
          have h2 : (cnt : ℝ) ≤ (M_seed : ℝ) := by exact_mod_cast hle
          simp only [bitVal, ↓reduceIte, one_mul, abs_le]
          constructor <;> linarith
    have halg : α * (cnt : ℝ) - bitVal ℝ fx / 2 =
        ((cnt : ℝ) - bitVal ℝ fx * (M_seed : ℝ)) / (2 * (M_seed : ℝ)) := by
      simp only [α, M_seed]
      field_simp
    have h2M_pos : (0 : ℝ) < 2 * (M_seed : ℝ) := by linarith
    rw [halg, abs_div, abs_of_pos h2M_pos]
    have hbad_real : (bad : ℝ) * (2 : ℝ) ^ (e + 1) ≤ (M_seed : ℝ) := by
      exact_mod_cast hbad_card
    calc |(cnt : ℝ) - bitVal ℝ fx * (M_seed : ℝ)| / (2 * (M_seed : ℝ))
        ≤ (bad : ℝ) / (2 * (M_seed : ℝ)) := by gcongr
      _ ≤ (bad : ℝ) / (M_seed : ℝ) := by gcongr; linarith
      _ ≤ ((2 : ℝ) ^ (e + 1))⁻¹ := by
          rw [div_le_iff₀ hM_pos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
          exact hbad_real
  calc |p (φ x) - bitVal ℝ fx / 2 - (z : ℝ)|
      = |(p (φ x) - α * (Ctop.count (ModPolyLayer.run Ls (φ x)) : ℝ) - (z : ℝ)) +
          (α * (Ctop.count (ModPolyLayer.run Ls (φ x)) : ℝ) - bitVal ℝ fx / 2)| := by ring_nf
    _ ≤ |p (φ x) - α * (Ctop.count (ModPolyLayer.run Ls (φ x)) : ℝ) - (z : ℝ)| +
          |α * (Ctop.count (ModPolyLayer.run Ls (φ x)) : ℝ) - bitVal ℝ fx / 2| := abs_add_le _ _
    _ ≤ ((2 : ℝ) ^ (e + 1))⁻¹ + ((2 : ℝ) ^ (e + 1))⁻¹ := add_le_add hz hseed_err
    _ = ((2 : ℝ) ^ e)⁻¹ := by rw [pow_succ]; field_simp; ring

/-- **Polylogarithmic torus degree upper bound for `ACC⁰`.** Every language
`L ∈ ACC⁰` has polylogarithmic torus approximation degree at arbitrary inverse-polynomial error:
for every exponent `k : ℕ`, there exists a constant `c : ℕ` such that for all `n ≥ 1` and every
`ε ≥ 1 / n ^ k`, `torusDegree ε (L.slice n) ≤ (c * (Nat.log 2 n + 1)) ^ c`. -/
theorem exists_polylog_torusDegree_of_mem_ACC0 {L : Language Bool} (hL : L ∈ ACC0) (k : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, ((n : ℝ) ^ k)⁻¹ ≤ ε →
      torusDegree ε (L.slice n) ≤ (c * (Nat.log 2 n + 1)) ^ c := by
  obtain ⟨m, hm2, hLm⟩ := mem_ACC0_iff.mp hL
  have hm : 0 < m := by omega
  obtain ⟨d, s, hs, hC⟩ := ConstDepth.mem_iff.mp hLm
  obtain ⟨a, ha⟩ := (PolynomiallyBounded.id.add hs).exists_clog_le_mul_log
  let K : ℕ := max (16 * ((m + 1) ^ 2 + a + k + d * (m + 2) + 2)) (5 ^ (d * (m + 2)))
  refine ⟨K, fun n hn ε hε ↦ ?_⟩
  obtain ⟨C, hCc, hd, hsz⟩ := hC n
  have hslice : (fun x ↦ C.eval (Unbounded.extInterpretation (modGate m)) x 0) = L.slice n :=
    funext fun x ↦ congrFun (hCc x) 0
  let e : ℕ := k * (Nat.log 2 n + 1)
  have h2e_le : ((2 : ℝ) ^ e)⁻¹ ≤ ε := by
    refine le_trans ?_ hε
    have hn_lt : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self one_lt_two n).le
    have hnk : (n : ℝ) ^ k ≤ (2 : ℝ) ^ e := by
      have : n ^ k ≤ 2 ^ e := by
        calc n ^ k ≤ (2 ^ (Nat.log 2 n + 1)) ^ k := Nat.pow_le_pow_left hn_lt k
          _ = 2 ^ e := by simp [e, ← pow_mul, mul_comm]
      exact_mod_cast this
    exact inv_anti₀ (by positivity) hnk
  have hanti : torusDegree ε (L.slice n) ≤ torusDegree (((2 : ℝ) ^ e)⁻¹) (L.slice n) :=
    torusDegree_antitone (by positivity) h2e_le (L.slice n)
  refine hanti.trans ?_
  rw [← hslice]
  refine (torusDegree_circuit_le C hm e).trans ?_
  have hlog : Nat.log 2 (n + C.size) ≤ a * (Nat.log 2 n + 1) :=
    (Nat.log_mono_right (by omega)).trans ((Nat.log_le_clog 2 _).trans (ha n))
  have hd_le : C.depth * (m + 2) ≤ d * (m + 2) := Nat.mul_le_mul_right _ hd
  let L_log : ℕ := Nat.log 2 n + 1
  have hL_pos : 1 ≤ L_log := Nat.succ_pos _
  have hbase :
      4 * (4 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2)) ≤
        K * L_log := by
    have hcoef : 16 * ((m + 1) ^ 2 + a + k + d * (m + 2) + 2) ≤ K := le_max_left _ _
    have h1 : (m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2 ≤
        ((m + 1) ^ 2 + a + k + d * (m + 2) + 2) * L_log := by
      calc (m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2
          ≤ (m + 1) ^ 2 * L_log + a * L_log + k * L_log + d * (m + 2) * L_log + 2 * L_log := by
            have h_m : (m + 1) ^ 2 ≤ (m + 1) ^ 2 * L_log := Nat.le_mul_of_pos_right _ hL_pos
            have h_d : C.depth * (m + 2) ≤ d * (m + 2) * L_log :=
              hd_le.trans (Nat.le_mul_of_pos_right _ hL_pos)
            have h_2 : 2 ≤ 2 * L_log := Nat.le_mul_of_pos_right _ hL_pos
            have hlog' : Nat.log 2 (n + C.size) ≤ a * L_log := hlog
            have he' : e = k * L_log := rfl
            omega
        _ = ((m + 1) ^ 2 + a + k + d * (m + 2) + 2) * L_log := by ring
    calc 4 * (4 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2))
        = 16 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + e + C.depth * (m + 2) + 2) := by ring
      _ ≤ 16 * (((m + 1) ^ 2 + a + k + d * (m + 2) + 2) * L_log) := Nat.mul_le_mul_left 16 h1
      _ = (16 * ((m + 1) ^ 2 + a + k + d * (m + 2) + 2)) * L_log := by ring
      _ ≤ K * L_log := Nat.mul_le_mul_right L_log hcoef
  have hKL_pos : 1 ≤ K * L_log :=
    Nat.mul_pos (lt_of_lt_of_le (by omega) (le_max_left _ _)) hL_pos
  have hexp : 5 ^ (C.depth * (m + 2)) ≤ K :=
    (Nat.pow_le_pow_right (by norm_num) hd_le).trans (le_max_right _ _)
  exact (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right hKL_pos hexp)

/-- **Barrington's conjecture**: the `MAJORITY` language is not contained in `ACC⁰`. -/
@[expose]
def BarringtonConjecture : Prop :=
  Language.ofSlices Cslib.majority ∉ Cslib.Circuits.Boolean.ACC0

/-- Any super-polylogarithmic lower bound on `torusDegree (ε n) (majority n)` for infinitely many
input lengths `n` at eventually inverse-polynomial error `ε n ≥ 1 / n ^ k` implies
`BarringtonConjecture`. -/
theorem barringtonConjecture_of_not_polylog {k : ℕ} {ε : ℕ → ℝ}
    (hε : ∃ N₀ : ℕ, ∀ n ≥ N₀, ((n : ℝ) ^ k)⁻¹ ≤ ε n)
    (hlb : ∀ c N : ℕ, ∃ n ≥ N,
      (c * (Nat.log 2 n + 1)) ^ c < torusDegree (ε n) (Cslib.majority n)) :
    BarringtonConjecture := by
  intro hmem
  obtain ⟨c, hc⟩ := exists_polylog_torusDegree_of_mem_ACC0 hmem k
  obtain ⟨N₀, hN₀⟩ := hε
  obtain ⟨n, hn, hlt⟩ := hlb c (max N₀ 1)
  have hle := hc n (le_of_max_le_right hn) (ε n) (hN₀ n (le_of_max_le_left hn))
  rw [Language.slice_ofSlices] at hle
  exact not_lt_of_ge hle hlt

end CslibFrontier.TorusPolynomial
