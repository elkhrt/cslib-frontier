module

public import CslibFrontier.Foundations.Combinatorics.Quasipolynomial
public import Mathlib.Algebra.GCDMonoid.Finset

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Positive Rational Generating Forms and Frobenius Saturation Bounds

Develops positive rational generating forms `F(t) = h(t) / ∏ (1 - t^{a_j})` with `h ∈ ℕ[X]`,
`h(0) = 1`, and `a_j > 0`, establishing:

- Quasipolynomiality (`exists_quasipolynomial_of_positiveRationalForm`) with period `lcm_j a_j`
  whenever `deg h < ∑ a_j`;
- Strict saturation (`isStrictlySaturated_of_exists_eq_one`) when some denominator exponent equals
  `1`;
- Brauer's elementary Frobenius-number bound (`mem_addSubmonoid_closure_of_ge_brauer`) for coprime
  positive integers bounded by `A`;
- The modular-index saturation bound (`saturationIndex_le_modularIndex_mul_pred`): when the
  denominator exponents are coprime and bounded by `A`, the saturation index satisfies
  `s(f) ≤ A * (A - 1)`.
-/

public section

namespace CslibFrontier.Combinatorics

open scoped BigOperators Polynomial PowerSeries

/-- A positive rational form for a formal power series `F ∈ ℚ⟦X⟧`:
`F(t) * ∏_{j : Fin m} (1 - t^{a_j}) = h(t)` with `h ∈ ℕ[X]`, `h.coeff 0 = 1`, and `a_j > 0`. -/
structure PositiveRationalForm (F : ℚ⟦X⟧) where
  /-- Number of denominator factors `(1 - t^{a_j})`. -/
  numFactors : ℕ
  /-- Positive exponents `a_j` in the denominator `∏ (1 - t^{a_j})`. -/
  exponents : Fin numFactors → ℕ
  /-- Positivity of every denominator exponent. -/
  exponents_pos : ∀ j, 0 < exponents j
  /-- Nonnegative-integer numerator polynomial `h(t) ∈ ℕ[X]`. -/
  numerator : ℕ[X]
  /-- Normalization `h(0) = 1`. -/
  coeff_zero_eq_one : numerator.coeff 0 = 1
  /-- Rational-function identity `F(t) * ∏ (1 - t^{a_j}) = h(t)` in `ℚ⟦X⟧`. -/
  series_eq :
    F * (∏ j : Fin numFactors, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ exponents j)) =
      ((numerator.map (Nat.castRingHom ℚ) : ℚ[X]) : ℚ⟦X⟧)

namespace PositiveRationalForm

/-- The modular index `max_j a_j` of a positive rational form. -/
def modularIndex {F : ℚ⟦X⟧} (pf : PositiveRationalForm F) : ℕ :=
  Finset.univ.sup pf.exponents

/-- Sum of denominator exponents `∑_j a_j`. -/
def denomDegree {F : ℚ⟦X⟧} (pf : PositiveRationalForm F) : ℕ :=
  ∑ j : Fin pf.numFactors, pf.exponents j

/-- The formal power series `∑_{k ≥ 0} X^{k * a}` inverting `1 - X^a` when `0 < a`. -/
def invOneSubXPow (a : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if a ∣ n then 1 else 0

theorem one_sub_X_pow_mul_invOneSubXPow {a : ℕ} (ha : 0 < a) :
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ a) * invOneSubXPow a = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [invOneSubXPow, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hn0 : n = 0
  · subst hn0
    have hnot : ¬ a ≤ 0 := Nat.not_le_of_gt ha
    simp [hnot]
  · simp only [hn0, ↓reduceIte]
    by_cases han : a ≤ n
    · simp only [han, ↓reduceIte]
      have hdvd : a ∣ n ↔ a ∣ (n - a) :=
        ⟨fun h ↦ Nat.dvd_sub h (dvd_refl a),
          fun h ↦ by rw [← Nat.sub_add_cancel han]; exact dvd_add h (dvd_refl a)⟩
      by_cases h : a ∣ n
      · simp [h, hdvd.1 h]
      · simp [h, mt hdvd.2 h]
    · have hndvd : ¬ a ∣ n := fun h ↦ han (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h)
      simp [han, hndvd]

theorem coeff_invOneSubXPow_nonneg (a n : ℕ) : 0 ≤ PowerSeries.coeff n (invOneSubXPow a) := by
  simp only [invOneSubXPow, PowerSeries.coeff_mk]
  split_ifs <;> norm_num

private lemma coeff_invOneSubPow_succ (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℚ (d + 1) : ℚ⟦X⟧) = ((d + n).choose d : ℚ) := by
  simp [PowerSeries.invOneSubPow]

private lemma coeff_invOneSubXPow_pow {L : ℕ} (hL : 0 < L) (t n : ℕ) :
    PowerSeries.coeff n ((invOneSubXPow L) ^ t) =
      if L ∣ n then PowerSeries.coeff (n / L) (PowerSeries.invOneSubPow ℚ t : ℚ⟦X⟧) else 0 := by
  induction t generalizing n with
  | zero =>
    simp only [pow_zero, PowerSeries.coeff_one, PowerSeries.invOneSubPow_zero, Units.val_one]
    by_cases hn : n = 0
    · subst hn; simp
    · by_cases hd : L ∣ n
      · have hpos : 0 < n / L := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hL
        simp [hn, hd, Nat.ne_of_gt hpos]
      · simp [hn, hd]
  | succ t ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    have hstep : (PowerSeries.invOneSubPow ℚ (t + 1) : ℚ⟦X⟧) =
        (PowerSeries.invOneSubPow ℚ t : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ 1 : ℚ⟦X⟧) := by
      rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]
    by_cases hd : L ∣ n
    · rcases hd with ⟨u, rfl⟩
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left u hL]
      rw [hstep, PowerSeries.coeff_mul]
      rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ ↦ L ∣ p.1 ∧ L ∣ p.2)]
      · refine Finset.sum_bij (fun p _ ↦ (p.1 / L, p.2 / L)) ?_ ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_filter.1 hp with ⟨hanti, ⟨a, ha⟩, ⟨b, hb⟩⟩
          rw [Finset.mem_antidiagonal] at hanti ⊢
          rw [ha, hb, Nat.mul_div_cancel_left a hL, Nat.mul_div_cancel_left b hL]
          exact Nat.eq_of_mul_eq_mul_left hL (by linarith)
        · intro p₁ hp₁ p₂ hp₂ heq
          rcases Finset.mem_filter.1 hp₁ with ⟨_, h1a, h1b⟩
          rcases Finset.mem_filter.1 hp₂ with ⟨_, h2a, h2b⟩
          have he1 : p₁.1 / L = p₂.1 / L := congrArg Prod.fst heq
          have he2 : p₁.2 / L = p₂.2 / L := congrArg Prod.snd heq
          ext
          · rw [← Nat.mul_div_cancel' h1a, ← Nat.mul_div_cancel' h2a, he1]
          · rw [← Nat.mul_div_cancel' h1b, ← Nat.mul_div_cancel' h2b, he2]
        · intro q hq
          rw [Finset.mem_antidiagonal] at hq
          refine ⟨(L * q.1, L * q.2), ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_antidiagonal]
            exact ⟨by rw [← mul_add, hq], dvd_mul_right L q.1, dvd_mul_right L q.2⟩
          · simp [Nat.mul_div_cancel_left _ hL]
        · intro p hp
          rcases Finset.mem_filter.1 hp with ⟨_, h1, h2⟩
          rw [ih p.1, ite_eq_left_iff.2 (fun h ↦ absurd h1 h), coeff_invOneSubPow_succ 0]
          simp [invOneSubXPow, h2]
      · intro p _ hne
        by_contra hnot
        apply hne
        rw [ih p.1]
        simp only [invOneSubXPow, PowerSeries.coeff_mk]
        by_cases h1 : L ∣ p.1
        · have h2 : ¬ L ∣ p.2 := fun h2 ↦ hnot ⟨h1, h2⟩
          simp [h1, h2]
        · simp [h1]
    · simp only [hd, ↓reduceIte]
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [ih p.1]
      simp only [invOneSubXPow, PowerSeries.coeff_mk]
      by_cases h1 : L ∣ p.1
      · have h2 : ¬ L ∣ p.2 := fun h2 ↦ hd (hp ▸ dvd_add h1 h2)
        simp [h1, h2]
      · simp [h1]

/-- The product `∏_{j : Fin m} (1 - t^{a_j})^{-1}` as a formal power series. -/
noncomputable def denomInv {m : ℕ} (a : Fin m → ℕ) : ℚ⟦X⟧ :=
  ∏ j : Fin m, invOneSubXPow (a j)

theorem denom_mul_denomInv {m : ℕ} (a : Fin m → ℕ) (ha : ∀ j, 0 < a j) :
    (∏ j : Fin m, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ a j)) * denomInv a = 1 := by
  unfold denomInv
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ ↦ one_sub_X_pow_mul_invOneSubXPow (ha j)

/-- Explicit formula for `F` as `h(t) * ∏ (1 - t^{a_j})^{-1}`. -/
theorem eq_numerator_mul_denomInv {F : ℚ⟦X⟧} (pf : PositiveRationalForm F) :
    F = ((pf.numerator.map (Nat.castRingHom ℚ) : ℚ[X]) : ℚ⟦X⟧) * denomInv pf.exponents := by
  calc
    F = F * 1 := (mul_one F).symm
    _ = F * ((∏ j : Fin pf.numFactors, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ pf.exponents j)) *
          denomInv pf.exponents) := by
      rw [denom_mul_denomInv pf.exponents pf.exponents_pos]
    _ = (F * ∏ j : Fin pf.numFactors, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ pf.exponents j)) *
          denomInv pf.exponents := by rw [mul_assoc]
    _ = ((pf.numerator.map (Nat.castRingHom ℚ) : ℚ[X]) : ℚ⟦X⟧) * denomInv pf.exponents := by
      rw [pf.series_eq]

private lemma coeff_prod_invOneSubXPow_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℕ) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (∏ j ∈ s, invOneSubXPow (a j)) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, PowerSeries.coeff_mul]
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (coeff_invOneSubXPow_nonneg (a j) p.1) (ih p.2)

theorem coeff_denomInv_nonneg {m : ℕ} (a : Fin m → ℕ) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (denomInv a) :=
  coeff_prod_invOneSubXPow_nonneg Finset.univ a n

private lemma one_le_coeff_prod_invOneSubXPow_of_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {x : ι → ℕ} {n : ℕ} (hx : ∑ j ∈ s, x j * a j = n) :
    1 ≤ PowerSeries.coeff n (∏ j ∈ s, invOneSubXPow (a j)) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.sum_empty] at hx
    subst hx
    simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at hx
    rw [Finset.prod_insert hj, PowerSeries.coeff_mul]
    set m₁ := x j * a j
    set m₂ := ∑ i ∈ s, x i * a i
    set P : ℚ⟦X⟧ := invOneSubXPow (a j)
    set Q : ℚ⟦X⟧ := ∏ i ∈ s, invOneSubXPow (a i)
    have hmem : (m₁, m₂) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.2 hx
    have h1 : PowerSeries.coeff m₁ P = 1 := by
      simp only [P, invOneSubXPow, PowerSeries.coeff_mk]
      exact ite_eq_left_iff.2 fun h ↦ absurd (dvd_mul_left (a j) (x j)) h
    have hterm : 1 ≤ PowerSeries.coeff m₁ P * PowerSeries.coeff m₂ Q := by
      rw [h1, one_mul]
      exact ih rfl
    have hnonneg : ∀ p ∈ Finset.antidiagonal n,
        0 ≤ PowerSeries.coeff p.1 P * PowerSeries.coeff p.2 Q := fun p _ ↦
      mul_nonneg (coeff_invOneSubXPow_nonneg (a j) p.1)
        (coeff_prod_invOneSubXPow_nonneg s a p.2)
    have hle := Finset.single_le_sum hnonneg hmem
    exact le_trans hterm hle

theorem one_le_coeff_denomInv_of_mem_closure {m : ℕ} {a : Fin m → ℕ} {n : ℕ}
    (hn : n ∈ AddSubmonoid.closure (Set.range a)) :
    1 ≤ PowerSeries.coeff n (denomInv a) := by
  classical
  have hrep : ∃ x : Fin m → ℕ, ∑ j : Fin m, x j * a j = n := by
    refine AddSubmonoid.closure_induction
      (motive := fun k _ ↦ ∃ x : Fin m → ℕ, ∑ j, x j * a j = k) ?_ ?_ ?_ hn
    · rintro _ ⟨j₀, rfl⟩
      refine ⟨fun j ↦ if j = j₀ then 1 else 0, ?_⟩
      simp
    · exact ⟨0, by simp⟩
    · rintro u v _ _ ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      simp [add_mul, Finset.sum_add_distrib, hx, hy]
  rcases hrep with ⟨x, hx⟩
  exact one_le_coeff_prod_invOneSubXPow_of_sum Finset.univ a hx

/-- Lower bound `[t^n] F(t) ≥ [t^n] ∏ (1 - t^{a_j})^{-1}` using `h_0 = 1` and `h_i ≥ 0`. -/
theorem coeff_denomInv_le_coeff {F : ℚ⟦X⟧} (pf : PositiveRationalForm F) (n : ℕ) :
    PowerSeries.coeff n (denomInv pf.exponents) ≤ PowerSeries.coeff n F := by
  conv_rhs => rw [pf.eq_numerator_mul_denomInv]
  rw [PowerSeries.coeff_mul]
  have hmem : (0, n) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.2 (zero_add n)
  have hterm : PowerSeries.coeff 0 ((pf.numerator.map (Nat.castRingHom ℚ) : ℚ[X]) : ℚ⟦X⟧) *
      PowerSeries.coeff n (denomInv pf.exponents) =
      PowerSeries.coeff n (denomInv pf.exponents) := by
    simp [pf.coeff_zero_eq_one]
  rw [← hterm]
  refine Finset.single_le_sum
    (f := fun p : ℕ × ℕ ↦
      PowerSeries.coeff p.1 ((pf.numerator.map (Nat.castRingHom ℚ) : ℚ[X]) : ℚ⟦X⟧) *
        PowerSeries.coeff p.2 (denomInv pf.exponents))
    (fun p _ ↦ ?_) hmem
  refine mul_nonneg ?_ (coeff_denomInv_nonneg _ _)
  simp

/-- If `F(t)` has a positive rational form with some `a_j = 1`, then `[t^n] F(t) ≥ 1` for
all `n`. -/
theorem one_le_coeff_of_exists_eq_one {F : ℚ⟦X⟧} (pf : PositiveRationalForm F)
    (h1 : ∃ j, pf.exponents j = 1) (n : ℕ) : 1 ≤ PowerSeries.coeff n F := by
  rcases h1 with ⟨j₀, hj₀⟩
  refine le_trans ?_ (pf.coeff_denomInv_le_coeff n)
  refine one_le_coeff_denomInv_of_mem_closure ?_
  have hmem1 : (1 : ℕ) ∈ AddSubmonoid.closure (Set.range pf.exponents) :=
    AddSubmonoid.subset_closure ⟨j₀, hj₀⟩
  simpa using (AddSubmonoid.closure (Set.range pf.exponents)).nsmul_mem hmem1 n

/-- If `f` is a quasipolynomial whose generating series has a positive rational form with some
denominator exponent equal to `1`, then `f` is strictly saturated. -/
theorem isStrictlySaturated_of_exists_eq_one {f : Quasipolynomial}
    (pf : PositiveRationalForm f.genSeries) (h1 : ∃ j, pf.exponents j = 1) :
    f.IsStrictlySaturated := by
  rw [Quasipolynomial.isStrictlySaturated_iff]
  intro n _ _
  have hge := pf.one_le_coeff_of_exists_eq_one h1 n
  rw [Quasipolynomial.coeff_genSeries] at hge
  linarith

private lemma one_sub_X_pow_mul_geomSum {a L : ℕ} (ha : 0 < a) (hdiv : a ∣ L) :
    ((1 : ℚ[X]) - Polynomial.X ^ a) * (∑ r ∈ Finset.range (L / a), Polynomial.X ^ (r * a)) =
      (1 : ℚ[X]) - Polynomial.X ^ L := by
  rcases hdiv with ⟨q, rfl⟩
  rw [Nat.mul_div_cancel_left q ha]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hpow : (Polynomial.X : ℚ[X]) ^ (a * (q + 1)) =
        (Polynomial.X : ℚ[X]) ^ a * (Polynomial.X : ℚ[X]) ^ (q * a) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    ring

private lemma natDegree_geomSum_le {a L : ℕ} (ha : 0 < a) (hL : 0 < L) (hdiv : a ∣ L) :
    (∑ r ∈ Finset.range (L / a), (Polynomial.X : ℚ[X]) ^ (r * a)).natDegree ≤ L - a := by
  have hq : 0 < L / a := Nat.div_pos (Nat.le_of_dvd hL hdiv) ha
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr ↦ ?_
  rw [Polynomial.natDegree_X_pow]
  have hrle : r + 1 ≤ L / a := Finset.mem_range.1 hr
  have hmul : (r + 1) * a ≤ L :=
    le_trans (Nat.mul_le_mul_right a hrle) (le_of_eq (Nat.div_mul_cancel hdiv))
  rw [add_mul, one_mul] at hmul
  omega

private lemma coeff_mul_invOneSubPow_eq_hilbertPoly_all (Q : ℚ[X]) (d : ℕ)
    (hdeg : Q.natDegree ≤ d) (k : ℕ) :
    PowerSeries.coeff k ((Q : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ (d + 1) : ℚ⟦X⟧)) =
      (Polynomial.hilbertPoly Q (d + 1)).eval (k : ℚ) := by
  rw [Polynomial.hilbertPoly_succ]
  change _ = (Polynomial.evalRingHom (k : ℚ)) _
  rw [map_sum]
  have hQcoe : (Q : ℚ⟦X⟧) =
      ∑ i ∈ Q.support, ((Polynomial.C (Q.coeff i) * Polynomial.X ^ i : ℚ[X]) : ℚ⟦X⟧) := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow Q]
    exact map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) _ _
  rw [hQcoe, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi_le : i ≤ d := le_trans (Polynomial.le_natDegree_of_mem_supp i hi) hdeg
  change PowerSeries.coeff k _ = (Q.coeff i • Polynomial.preHilbertPoly ℚ d i).eval (k : ℚ)
  rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.preHilbertPoly_eq_choose_add_sub (F := ℚ) d (k := i) (n := k) (by omega)]
  have hterm : ((Polynomial.C (Q.coeff i) * Polynomial.X ^ i : ℚ[X]) : ℚ⟦X⟧) =
      PowerSeries.C (Q.coeff i) * PowerSeries.X ^ i := by
    simp
  rw [hterm, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hik : i ≤ k
  · simp only [hik, ↓reduceIte, coeff_invOneSubPow_succ]
    have heq : d + (k - i) = k + d - i := by omega
    rw [heq]
  · simp only [hik, ↓reduceIte]
    have hlt : k + d - i < d := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]

/-- Any power series with a positive rational form whose numerator degree is strictly smaller than
the denominator degree `∑ a_j` is the generating series of a quasipolynomial of period
`lcm_j a_j`. -/
theorem exists_quasipolynomial_of_positiveRationalForm {F : ℚ⟦X⟧}
    (pf : PositiveRationalForm F) (hdeg : pf.numerator.natDegree < pf.denomDegree) :
    ∃ f : Quasipolynomial, f.period = Finset.univ.lcm pf.exponents ∧ f.genSeries = F := by
  classical
  have hm : 0 < pf.numFactors := Nat.pos_of_ne_zero fun h0 ↦ by
    have hd0 : pf.denomDegree = 0 := by
      unfold denomDegree
      exact Finset.sum_eq_zero fun j _ ↦ absurd j.2 (by omega)
    omega
  set m := pf.numFactors
  set L := Finset.univ.lcm pf.exponents
  have hL : 0 < L := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [Finset.lcm_eq_zero_iff] at h0
    rcases h0 with ⟨j, _, hj⟩
    exact Nat.ne_of_gt (pf.exponents_pos j) hj
  set G : Fin m → ℚ[X] := fun j ↦ ∑ r ∈ Finset.range (L / pf.exponents j),
    Polynomial.X ^ (r * pf.exponents j)
  set Htilde : ℚ[X] := pf.numerator.map (Nat.castRingHom ℚ) * ∏ j : Fin m, G j
  have hdiv : ∀ j : Fin m, pf.exponents j ∣ L := fun j ↦ Finset.dvd_lcm (Finset.mem_univ j)
  have hprod_eq :
      (∏ j : Fin m, ((1 : ℚ[X]) - Polynomial.X ^ pf.exponents j)) * (∏ j : Fin m, G j) =
        ((1 : ℚ[X]) - Polynomial.X ^ L) ^ m := by
    rw [← Finset.prod_mul_distrib]
    calc
      ∏ j : Fin m, (((1 : ℚ[X]) - Polynomial.X ^ pf.exponents j) * G j)
          = ∏ _j : Fin m, ((1 : ℚ[X]) - Polynomial.X ^ L) :=
        Finset.prod_congr rfl fun j _ ↦ one_sub_X_pow_mul_geomSum (pf.exponents_pos j) (hdiv j)
      _ = ((1 : ℚ[X]) - Polynomial.X ^ L) ^ m := by simp
  have hseries_lift :
      F * (((1 : ℚ⟦X⟧) - PowerSeries.X ^ L) ^ m) = (Htilde : ℚ⟦X⟧) := by
    have hcoe : ((((1 : ℚ[X]) - Polynomial.X ^ L) ^ m : ℚ[X]) : ℚ⟦X⟧) =
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ L) ^ m := by
      rw [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow,
        Polynomial.coe_X]
    have hcoe_prod :
        ((∏ j : Fin m, ((1 : ℚ[X]) - Polynomial.X ^ pf.exponents j) : ℚ[X]) : ℚ⟦X⟧) =
          ∏ j : Fin m, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ pf.exponents j) := by
      rw [show ((∏ j : Fin m, ((1 : ℚ[X]) - Polynomial.X ^ pf.exponents j) : ℚ[X]) : ℚ⟦X⟧) =
          ∏ j : Fin m, (((1 : ℚ[X]) - Polynomial.X ^ pf.exponents j : ℚ[X]) : ℚ⟦X⟧) from
        map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) _ _]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]
    calc
      F * (((1 : ℚ⟦X⟧) - PowerSeries.X ^ L) ^ m)
          = F * ((((1 : ℚ[X]) - Polynomial.X ^ L) ^ m : ℚ[X]) : ℚ⟦X⟧) := by rw [hcoe]
      _ = F * (((∏ j : Fin m, ((1 : ℚ[X]) - Polynomial.X ^ pf.exponents j)) *
            (∏ j : Fin m, G j) : ℚ[X]) : ℚ⟦X⟧) := by rw [hprod_eq]
      _ = (F * (∏ j : Fin m, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ pf.exponents j))) *
            ((∏ j : Fin m, G j : ℚ[X]) : ℚ⟦X⟧) := by
        rw [Polynomial.coe_mul, hcoe_prod, mul_assoc]
      _ = (Htilde : ℚ⟦X⟧) := by
        rw [pf.series_eq, ← Polynomial.coe_mul]
  have hHtilde_deg : Htilde.natDegree < m * L := by
    have h1 : Htilde.natDegree ≤
        (pf.numerator.map (Nat.castRingHom ℚ)).natDegree + (∏ j : Fin m, G j).natDegree :=
      Polynomial.natDegree_mul_le
    have h2 : (pf.numerator.map (Nat.castRingHom ℚ)).natDegree ≤ pf.numerator.natDegree :=
      Polynomial.natDegree_map_le
    have h3 : (∏ j : Fin m, G j).natDegree ≤ ∑ j : Fin m, (G j).natDegree :=
      Polynomial.natDegree_prod_le _ _
    have h4 : ∑ j : Fin m, (G j).natDegree ≤ ∑ j : Fin m, (L - pf.exponents j) :=
      Finset.sum_le_sum fun j _ ↦ natDegree_geomSum_le (pf.exponents_pos j) hL (hdiv j)
    have h5 : ∑ j : Fin m, (L - pf.exponents j) + pf.denomDegree = m * L := by
      unfold denomDegree
      rw [← Finset.sum_add_distrib]
      calc
        ∑ j : Fin m, (L - pf.exponents j + pf.exponents j)
            = ∑ _j : Fin m, L := Finset.sum_congr rfl fun j _ ↦
              Nat.sub_add_cancel (Nat.le_of_dvd hL (hdiv j))
        _ = m * L := by simp
    omega
  set Q : Fin L → ℚ[X] := fun r ↦
    ∑ q ∈ Finset.range m, Polynomial.C (Htilde.coeff (q * L + r.1)) * Polynomial.X ^ q
  have hQ_deg : ∀ r : Fin L, (Q r).natDegree ≤ m - 1 := by
    intro r
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun q hq ↦ ?_
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    have := Finset.mem_range.1 hq
    omega
  have hinv_pow : F = (Htilde : ℚ⟦X⟧) * (invOneSubXPow L) ^ m := by
    calc
      F = F * 1 := (mul_one F).symm
      _ = F * ((((1 : ℚ⟦X⟧) - PowerSeries.X ^ L) * invOneSubXPow L) ^ m) := by
        rw [one_sub_X_pow_mul_invOneSubXPow hL, one_pow]
      _ = (F * ((1 : ℚ⟦X⟧) - PowerSeries.X ^ L) ^ m) * (invOneSubXPow L) ^ m := by
        rw [mul_pow, mul_assoc]
      _ = (Htilde : ℚ⟦X⟧) * (invOneSubXPow L) ^ m := by rw [hseries_lift]
  have hcoeff_split : ∀ (r : Fin L) (k : ℕ),
      PowerSeries.coeff (k * L + r.1) F =
        PowerSeries.coeff k ((Q r : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ m : ℚ⟦X⟧)) := by
    intro r k
    rw [hinv_pow, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ ↦ L ∣ p.2)]
    · refine Finset.sum_bij (fun p _ ↦ (k - p.2 / L, p.2 / L)) ?_ ?_ ?_ ?_
      · intro p hp
        rcases Finset.mem_filter.1 hp with ⟨hanti, ⟨b, hb⟩⟩
        rw [Finset.mem_antidiagonal] at hanti ⊢
        rw [hb, Nat.mul_div_cancel_left b hL]
        have hbk : b ≤ k := by
          have hrlt : r.1 < L := r.2
          nlinarith
        exact Nat.sub_add_cancel hbk
      · intro p₁ hp₁ p₂ hp₂ heq
        rcases Finset.mem_filter.1 hp₁ with ⟨hanti₁, h1⟩
        rcases Finset.mem_filter.1 hp₂ with ⟨hanti₂, h2⟩
        rw [Finset.mem_antidiagonal] at hanti₁ hanti₂
        have he2 : p₁.2 / L = p₂.2 / L := congrArg Prod.snd heq
        have hp2 : p₁.2 = p₂.2 := by
          rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, he2]
        ext <;> omega
      · intro q hq
        rw [Finset.mem_antidiagonal] at hq
        refine ⟨(q.1 * L + r.1, L * q.2), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_antidiagonal]
          exact ⟨by nlinarith, dvd_mul_right L q.2⟩
        · simp only [Nat.mul_div_cancel_left _ hL]
          ext <;> omega
      · intro p hp
        rcases Finset.mem_filter.1 hp with ⟨hanti, ⟨b, hb⟩⟩
        rw [Finset.mem_antidiagonal] at hanti
        rw [coeff_invOneSubXPow_pow hL m p.2,
          ite_eq_left_iff.2 (fun h ↦ absurd ⟨b, hb⟩ h), hb, Nat.mul_div_cancel_left b hL]
        have hbk : b ≤ k := by
          have hrlt : r.1 < L := r.2
          nlinarith
        have hp1 : p.1 = (k - b) * L + r.1 := by
          have hsub : (k - b) * L + b * L = k * L := by
            rw [← add_mul, Nat.sub_add_cancel hbk]
          linarith
        rw [hp1, Polynomial.coeff_coe, Polynomial.coeff_coe]
        congr 1
        simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        by_cases hkm : k - b < m
        · simp [Finset.mem_range.2 hkm]
        · have hbig : m * L ≤ (k - b) * L + r.1 := by
            have hge : m ≤ k - b := Nat.le_of_not_lt hkm
            have := Nat.mul_le_mul_right L hge
            omega
          have hzero : Htilde.coeff ((k - b) * L + r.1) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hHtilde_deg hbig)
          rw [hzero]
          symm
          refine Finset.sum_eq_zero fun q hq ↦ ?_
          have hne : k - b ≠ q := by
            have := Finset.mem_range.1 hq
            omega
          simp [hne]
    · intro p _ hne
      by_contra hndvd
      apply hne
      rw [coeff_invOneSubXPow_pow hL m p.2]
      simp [hndvd]
  refine ⟨⟨L, hL, fun r ↦
    (Polynomial.hilbertPoly (Q r) m).comp
      (Polynomial.C ((L : ℚ)⁻¹) * (Polynomial.X - Polynomial.C (r.1 : ℚ)))⟩, rfl, ?_⟩
  ext n
  rw [Quasipolynomial.coeff_genSeries, Quasipolynomial.eval_apply]
  set r : Fin L := ⟨n % L, Nat.mod_lt n hL⟩
  set k : ℕ := n / L
  have hn_eq : k * L + r.1 = n := by
    change (n / L) * L + n % L = n
    rw [mul_comm]
    exact Nat.div_add_mod n L
  have hQ_eval := coeff_mul_invOneSubPow_eq_hilbertPoly_all (Q r) (m - 1) (hQ_deg r) k
  rw [Nat.sub_add_cancel hm] at hQ_eval
  have hsplit := hcoeff_split r k
  rw [hn_eq] at hsplit
  rw [hsplit, hQ_eval]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  congr 1
  have hLne : (L : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hn_rat : (n : ℚ) = (k : ℚ) * (L : ℚ) + (r.1 : ℚ) := by exact_mod_cast hn_eq.symm
  rw [hn_rat]
  field_simp [hLne]
  ring

private lemma sum_sub_one_le_prod_sub_one {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : ∀ i ∈ s, 1 ≤ q i) :
    ∑ i ∈ s, (q i - 1) ≤ (∏ i ∈ s, q i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hqi : 1 ≤ q i := hq i (Finset.mem_insert_self i s)
    have hprod : 1 ≤ ∏ j ∈ s, q j :=
      Finset.one_le_prod fun j hj ↦ hq j (Finset.mem_insert_of_mem hj)
    have hih := ih fun j hj ↦ hq j (Finset.mem_insert_of_mem hj)
    rcases Nat.exists_eq_add_of_le' hqi with ⟨a, ha⟩
    rcases Nat.exists_eq_add_of_le' hprod with ⟨b, hb⟩
    rw [hb] at hih
    rw [ha, hb]
    have hmul : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    omega

private def prefixGcd {m : ℕ} (a : Fin m → ℕ) : ℕ → ℕ
  | 0 => if h : 0 < m then a ⟨0, h⟩ else 0
  | k + 1 => if h : k + 1 < m then Nat.gcd (prefixGcd a k) (a ⟨k + 1, h⟩) else prefixGcd a k

private lemma prefixGcd_pos {m : ℕ} (a : Fin m → ℕ) (ha : ∀ j, 0 < a j) (hm : 0 < m) (k : ℕ) :
    0 < prefixGcd a k := by
  induction k with
  | zero => simp [prefixGcd, hm, ha]
  | succ k ih =>
    simp only [prefixGcd]
    split_ifs with h
    · exact Nat.gcd_pos_of_pos_left _ ih
    · exact ih

private lemma prefixGcd_dvd_prev {m : ℕ} (a : Fin m → ℕ) (k : ℕ) :
    prefixGcd a (k + 1) ∣ prefixGcd a k := by
  simp only [prefixGcd]
  split_ifs
  · exact Nat.gcd_dvd_left _ _
  · exact dvd_refl _

private lemma prefixGcd_eq_finset_gcd {m : ℕ} (a : Fin m → ℕ) (hm : 0 < m) :
    prefixGcd a (m - 1) = Finset.univ.gcd a := by
  have haux : ∀ k (hk : k < m),
      prefixGcd a k = (Finset.univ.filter fun j : Fin m ↦ j.1 ≤ k).gcd a := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hfilt : (Finset.univ.filter fun j : Fin m ↦ j.1 ≤ 0) = {⟨0, hk⟩} := by
        ext j
        simp [Fin.ext_iff]
      rw [hfilt, Finset.gcd_singleton]
      simp [prefixGcd, hk]
    | succ k ih =>
      intro hk
      have hk' : k < m := Nat.lt_of_succ_lt hk
      have hfilt : (Finset.univ.filter fun j : Fin m ↦ j.1 ≤ k + 1) =
          insert ⟨k + 1, hk⟩ (Finset.univ.filter fun j : Fin m ↦ j.1 ≤ k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hfilt, Finset.gcd_insert, ← ih hk']
      simp only [prefixGcd, hk, ↓reduceDIte, Nat.gcd_comm]
      rfl
  rw [haux (m - 1) (Nat.sub_lt hm Nat.one_pos)]
  congr 1
  ext j
  simp [Nat.le_sub_one_of_lt j.2]

/-- Brauer's elementary Frobenius-number bound: for any nonempty tuple of positive integers
`a_0, ..., a_{m-1}` with `gcd = 1` and `∀ j, a_j ≤ A`, every integer `n ≥ A * (A - 1)` lies in the
additive submonoid generated by `a_0, ..., a_{m-1}`. -/
theorem mem_addSubmonoid_closure_of_ge_brauer {m : ℕ} (hm : 0 < m) (a : Fin m → ℕ)
    (ha_pos : ∀ j, 0 < a j) (hcop : Finset.univ.gcd a = 1) {A : ℕ}
    (ha_le : ∀ j, a j ≤ A) {n : ℕ} (hn : A * (A - 1) ≤ n) :
    n ∈ AddSubmonoid.closure (Set.range a) := by
  set B : ℕ → ℕ := fun k ↦
    ∑ i ∈ Finset.range k,
      (if h : i + 1 < m then a ⟨i + 1, h⟩ * (prefixGcd a i / prefixGcd a (i + 1) - 1) else 0)
  have hind : ∀ k, k < m → ∀ t : ℕ, prefixGcd a k ∣ t → B k ≤ t →
      t ∈ AddSubmonoid.closure (Set.range a) := by
    intro k
    induction k with
    | zero =>
      intro hk t hdvd _
      simp only [prefixGcd, hk, ↓reduceDIte] at hdvd
      rcases hdvd with ⟨c, rfl⟩
      rw [mul_comm]
      exact (AddSubmonoid.closure (Set.range a)).nsmul_mem
        (AddSubmonoid.subset_closure ⟨⟨0, hk⟩, rfl⟩) c
    | succ k ih =>
      intro hk t hdvd hBt
      have hk' : k < m := Nat.lt_of_succ_lt hk
      set d_prev := prefixGcd a k
      set d_cur := prefixGcd a (k + 1)
      set ak := a ⟨k + 1, hk⟩
      have hd_cur_pos : 0 < d_cur := prefixGcd_pos a ha_pos hm (k + 1)
      have hd_prev_pos : 0 < d_prev := prefixGcd_pos a ha_pos hm k
      have hdvd_prev : d_cur ∣ d_prev := prefixGcd_dvd_prev a k
      have hdvd_ak : d_cur ∣ ak := by
        simp only [d_cur, prefixGcd, hk, ↓reduceDIte]
        exact Nat.gcd_dvd_right _ _
      set q := d_prev / d_cur
      have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hd_prev_pos hdvd_prev) hd_cur_pos
      have hcop_step : Nat.Coprime (ak / d_cur) q := by
        have hgcd_eq : d_cur = Nat.gcd d_prev ak := by
          simp only [d_cur, prefixGcd, hk, ↓reduceDIte]
          rfl
        have hcop' : Nat.Coprime (d_prev / Nat.gcd d_prev ak) (ak / Nat.gcd d_prev ak) :=
          Nat.coprime_div_gcd_div_gcd (by rwa [← hgcd_eq])
        rw [← hgcd_eq] at hcop'
        exact hcop'.symm
      set u := t / d_cur
      set v := ak / d_cur
      have hexists_x : ∃ x < q, (q : ℤ) ∣ ((u : ℤ) - (x : ℤ) * (v : ℤ)) := by
        have hbez : (1 : ℤ) = (v : ℤ) * Nat.gcdA v q + (q : ℤ) * Nat.gcdB v q := by
          have h := Nat.gcd_eq_gcd_ab v q
          rw [hcop_step.gcd_eq_one, Nat.cast_one] at h
          exact h
        have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq_pos
        set rZ : ℤ := ((u : ℤ) * Nat.gcdA v q) % (q : ℤ)
        have hrZ_nonneg : 0 ≤ rZ := Int.emod_nonneg _ (ne_of_gt hqZ)
        have hrZ_lt : rZ < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
        refine ⟨rZ.toNat, ?_, ?_⟩
        · have : (rZ.toNat : ℤ) < (q : ℤ) := by
            rwa [Int.toNat_of_nonneg hrZ_nonneg]
          exact_mod_cast this
        · rw [Int.toNat_of_nonneg hrZ_nonneg]
          have hmod_dvd : (q : ℤ) ∣ ((u : ℤ) * Nat.gcdA v q - rZ) := by
            refine ⟨((u : ℤ) * Nat.gcdA v q) / (q : ℤ), ?_⟩
            have := Int.mul_ediv_add_emod ((u : ℤ) * Nat.gcdA v q) (q : ℤ)
            linarith
          rcases hmod_dvd with ⟨w, hw⟩
          refine ⟨(u : ℤ) * Nat.gcdB v q + (v : ℤ) * w, ?_⟩
          calc
            (u : ℤ) - rZ * (v : ℤ)
                = (u : ℤ) * ((v : ℤ) * Nat.gcdA v q + (q : ℤ) * Nat.gcdB v q) -
                    rZ * (v : ℤ) := by rw [← hbez, mul_one]
            _ = ((u : ℤ) * Nat.gcdA v q - rZ) * (v : ℤ) +
                  (q : ℤ) * ((u : ℤ) * Nat.gcdB v q) := by ring
            _ = ((q : ℤ) * w) * (v : ℤ) + (q : ℤ) * ((u : ℤ) * Nat.gcdB v q) := by rw [hw]
            _ = (q : ℤ) * ((u : ℤ) * Nat.gcdB v q + (v : ℤ) * w) := by ring
      rcases hexists_x with ⟨x, hxq, hq_dvd_int⟩
      have hBstep : B (k + 1) = B k + ak * (q - 1) := by
        simp only [B, Finset.sum_range_succ, hk, ↓reduceDIte]
        rfl
      have hxak_le : x * ak ≤ ak * (q - 1) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left ak (Nat.le_sub_one_of_lt hxq)
      have ht_ge : B k ≤ t - x * ak := by omega
      have hxak_le_t : x * ak ≤ t := by omega
      have hdvd_diff : d_prev ∣ (t - x * ak) := by
        have hsub_div : (t - x * ak) / d_cur = u - x * v := by
          have ht_eq : t = d_cur * u := (Nat.mul_div_cancel' hdvd).symm
          have hak_eq : ak = d_cur * v := (Nat.mul_div_cancel' hdvd_ak).symm
          have hmul : t - x * ak = d_cur * (u - x * v) := by
            rw [Nat.mul_sub_left_distrib, ← ht_eq, ← mul_assoc, mul_comm d_cur x, mul_assoc,
              ← hak_eq]
          rw [hmul, Nat.mul_div_cancel_left _ hd_cur_pos]
        have hxv_le : x * v ≤ u := by
          have : d_cur * (x * v) ≤ d_cur * u := by
            calc
              d_cur * (x * v) = x * (d_cur * v) := by ring
              _ = x * ak := by rw [Nat.mul_div_cancel' hdvd_ak]
              _ ≤ t := hxak_le_t
              _ = d_cur * u := (Nat.mul_div_cancel' hdvd).symm
          exact Nat.le_of_mul_le_mul_left this hd_cur_pos
        have hq_dvd : q ∣ (u - x * v) := by
          have hcast : ((u - x * v : ℕ) : ℤ) = (u : ℤ) - (x : ℤ) * (v : ℤ) := by
            rw [Nat.cast_sub hxv_le, Nat.cast_mul]
          rw [← Int.natCast_dvd_natCast, hcast]
          exact hq_dvd_int
        have hd_prev_eq : d_prev = d_cur * q := (Nat.mul_div_cancel' hdvd_prev).symm
        have hdvd_cur_diff : d_cur ∣ (t - x * ak) :=
          Nat.dvd_sub hdvd (dvd_mul_of_dvd_right hdvd_ak x)
        rw [hd_prev_eq, ← Nat.mul_div_cancel' hdvd_cur_diff, hsub_div]
        exact Nat.mul_dvd_mul_left d_cur hq_dvd
      have hmem_rem : t - x * ak ∈ AddSubmonoid.closure (Set.range a) :=
        ih hk' (t - x * ak) hdvd_diff ht_ge
      have hmem_xak : x * ak ∈ AddSubmonoid.closure (Set.range a) :=
        (AddSubmonoid.closure (Set.range a)).nsmul_mem
          (AddSubmonoid.subset_closure ⟨⟨k + 1, hk⟩, rfl⟩) x
      have hsum : (t - x * ak) + x * ak = t := Nat.sub_add_cancel hxak_le_t
      rw [← hsum]
      exact AddSubmonoid.add_mem _ hmem_rem hmem_xak
  have hB_le : B (m - 1) ≤ A * (A - 1) := by
    have hstep_le : B (m - 1) ≤
        A * ∑ i ∈ Finset.range (m - 1), (prefixGcd a i / prefixGcd a (i + 1) - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have him : i + 1 < m := by
        have := Finset.mem_range.1 hi
        omega
      simp only [him, ↓reduceDIte]
      exact Nat.mul_le_mul_right _ (ha_le ⟨i + 1, him⟩)
    have hq_ge1 : ∀ i ∈ Finset.range (m - 1),
        1 ≤ prefixGcd a i / prefixGcd a (i + 1) := fun i _ ↦
      Nat.div_pos (Nat.le_of_dvd (prefixGcd_pos a ha_pos hm i) (prefixGcd_dvd_prev a i))
        (prefixGcd_pos a ha_pos hm (i + 1))
    have hsum_le := sum_sub_one_le_prod_sub_one (Finset.range (m - 1))
      (fun i ↦ prefixGcd a i / prefixGcd a (i + 1)) hq_ge1
    have hprod_eq :
        (∏ i ∈ Finset.range (m - 1), (prefixGcd a i / prefixGcd a (i + 1))) *
          prefixGcd a (m - 1) = prefixGcd a 0 := by
      have hteles : ∀ r : ℕ,
          (∏ i ∈ Finset.range r, (prefixGcd a i / prefixGcd a (i + 1))) *
            prefixGcd a r = prefixGcd a 0 := by
        intro r
        induction r with
        | zero => simp
        | succ r ihr =>
          rw [Finset.prod_range_succ, mul_assoc,
            Nat.div_mul_cancel (prefixGcd_dvd_prev a r), ihr]
      exact hteles (m - 1)
    rw [prefixGcd_eq_finset_gcd a hm, hcop, mul_one] at hprod_eq
    have ha0_le : prefixGcd a 0 ≤ A := by
      simpa [prefixGcd, hm] using ha_le ⟨0, hm⟩
    have hsum_le_A : ∑ i ∈ Finset.range (m - 1), (prefixGcd a i / prefixGcd a (i + 1) - 1) ≤
        A - 1 := by
      rw [hprod_eq] at hsum_le
      omega
    exact le_trans hstep_le (Nat.mul_le_mul_left A hsum_le_A)
  have hdvd1 : prefixGcd a (m - 1) ∣ n := by
    rw [prefixGcd_eq_finset_gcd a hm, hcop]
    exact one_dvd n
  exact hind (m - 1) (Nat.sub_lt hm Nat.one_pos) n hdvd1 (le_trans hB_le hn)

/-- If a quasipolynomial `f` has a generating series with a positive rational form whose
coprime positive denominator exponents bounded by `A = pf.modularIndex`, then its saturation index
satisfies `f.saturationIndex ≤ A * (A - 1)`. -/
theorem saturationIndex_le_modularIndex_mul_pred {f : Quasipolynomial}
    (pf : PositiveRationalForm f.genSeries) (hm : 0 < pf.numFactors)
    (hcop : Finset.univ.gcd pf.exponents = 1) :
    f.HasSaturationIndex ∧ f.saturationIndex ≤ pf.modularIndex * (pf.modularIndex - 1) := by
  set A := pf.modularIndex
  have ha_le : ∀ j, pf.exponents j ≤ A := fun j ↦ Finset.le_sup (Finset.mem_univ j)
  have hshift : (f.shift (A * (A - 1))).IsStrictlySaturated := by
    rw [Quasipolynomial.isStrictlySaturated_iff]
    intro n hn _
    rw [Quasipolynomial.eval_shift]
    have hge : A * (A - 1) ≤ n + A * (A - 1) := Nat.le_add_left _ _
    have hmem : n + A * (A - 1) ∈ AddSubmonoid.closure (Set.range pf.exponents) :=
      mem_addSubmonoid_closure_of_ge_brauer hm pf.exponents pf.exponents_pos hcop ha_le hge
    have h1 : 1 ≤ PowerSeries.coeff (n + A * (A - 1)) f.genSeries :=
      le_trans (one_le_coeff_denomInv_of_mem_closure hmem)
        (pf.coeff_denomInv_le_coeff (n + A * (A - 1)))
    rw [Quasipolynomial.coeff_genSeries] at h1
    linarith
  exact ⟨(f.hasSaturationIndex_iff).2 ⟨A * (A - 1), hshift⟩, f.saturationIndex_le hshift⟩

end PositiveRationalForm

end CslibFrontier.Combinatorics
