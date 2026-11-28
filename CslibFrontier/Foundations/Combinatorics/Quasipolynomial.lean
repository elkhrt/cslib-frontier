module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quasipolynomials, Coefficient Positivity, Saturation, and Rational Generating Series

Defines quasipolynomials of positive period $\ell \ge 1$ over a semiring $R$, their evaluation
sequence, coefficient positivity, index, and saturation, and proves:

## Main definitions

- `Quasipolynomial`: a periodic family of polynomials $(f_0, \dots, f_{\ell-1})$ of period
  $\ell \ge 1$ over a semiring $R$, evaluated by $f(k) = f_{k \bmod \ell}(k)$.
- `Quasipolynomial.eval`, `Quasipolynomial.IsPositive`, `Quasipolynomial.index`,
  `Quasipolynomial.IsSaturated`: sequence evaluation, coefficient positivity, index, and
  saturation predicates.

## Main results

- `Quasipolynomial.IsPositive.isSaturated`: nonnegative polynomial coefficients imply
  saturation for any quasipolynomial over a linearly ordered semiring.
- `polynomial_positive_implies_saturated`: specialization to polynomials (period $1$).
- `period_two_positive_odd_iff`: a positive period-$2$ quasipolynomial vanishes on all odd
  arguments iff it vanishes at $1$.
- `quasipolynomial_iff_rational_generating_series`: two-way characterization of complex
  quasipolynomials of period $\ell$ as sequences whose ordinary generating function is a
  rational power series $P(t) / Q(t)$ with $\deg P < \deg Q$ whose denominator roots are
  $\ell$-th roots of unity.
-/

public section

namespace CslibFrontier

open Finset

/-! ### Quasipolynomials, Positivity, Index, and Saturation -/

/-- A quasipolynomial $f = (f_0, \dots, f_{\ell-1})$ of period $\ell \ge 1$ over a semiring $R$,
with $f(k) = f_{k \bmod \ell}(k)$. -/
@[ext]
structure Quasipolynomial (R : Type*) [Semiring R] where
  /-- Period $\ell \ge 1$ of the quasipolynomial. -/
  period : ℕ
  /-- Positivity of the period. -/
  period_pos : 0 < period
  /-- Component polynomials indexed by residue classes modulo `period`. -/
  poly : Fin period → Polynomial R

namespace Quasipolynomial

/-- Evaluation of a quasipolynomial at a natural number $k$. -/
def eval {R : Type*} [Semiring R] (q : Quasipolynomial R) (k : ℕ) : R :=
  (q.poly ⟨k % q.period, Nat.mod_lt k q.period_pos⟩).eval (k : R)

/-- A quasipolynomial is positive if every coefficient of every
component polynomial is nonnegative. -/
def IsPositive {R : Type*} [Semiring R] [PartialOrder R] (q : Quasipolynomial R) : Prop :=
  ∀ (i : Fin q.period) (d : ℕ), 0 ≤ (q.poly i).coeff d

/-- The index of a quasipolynomial: the least $i \in \{1, \dots, \ell\}$
such that $f_{i \bmod \ell}$ is not identically zero, or $0$ if every component polynomial
is zero. -/
noncomputable def index {R : Type*} [Semiring R] (q : Quasipolynomial R) : ℕ := by
  classical
  exact if h : ∃ i ∈ Icc 1 q.period,
      q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0 then
    Nat.find (p := fun i ↦ i ∈ Icc 1 q.period ∧
      q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0) ⟨h.choose, h.choose_spec⟩
  else 0

/-- A quasipolynomial is saturated if whenever it is not identically
zero (`q.index ≠ 0`), its value at `q.index` is nonzero. -/
def IsSaturated {R : Type*} [Semiring R] (q : Quasipolynomial R) : Prop :=
  q.index ≠ 0 → q.eval q.index ≠ 0

/-- A quasipolynomial has index zero if and only if all of its component polynomials are zero. -/
theorem index_eq_zero_iff {R : Type*} [Semiring R] (q : Quasipolynomial R) :
    q.index = 0 ↔ ∀ i : Fin q.period, q.poly i = 0 := by
  classical
  unfold index
  split_ifs with h
  · constructor
    · intro h0
      have hspec := Nat.find_spec (p := fun i ↦ i ∈ Icc 1 q.period ∧
        q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0) ⟨h.choose, h.choose_spec⟩
      rw [h0] at hspec
      exact absurd (mem_Icc.mp hspec.1).1 (by omega)
    · intro hall
      rcases h with ⟨i, _, hne⟩
      exact absurd (hall _) hne
  · simp only [true_iff]
    intro i
    by_contra hne
    apply h
    by_cases hi : i.1 = 0
    · refine ⟨q.period, mem_Icc.mpr ⟨q.period_pos, le_rfl⟩, ?_⟩
      convert hne using 2
      ext; simp [hi]
    · refine ⟨i.1, mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi, le_of_lt i.2⟩, ?_⟩
      convert hne using 2
      ext; exact Nat.mod_eq_of_lt i.2

/-- If a quasipolynomial is nonzero, its index lies in $\{1, \dots, \ell\}$ and the
corresponding component polynomial is nonzero. -/
theorem index_spec {R : Type*} [Semiring R] (q : Quasipolynomial R) (h : q.index ≠ 0) :
    1 ≤ q.index ∧ q.index ≤ q.period ∧
      q.poly ⟨q.index % q.period, Nat.mod_lt q.index q.period_pos⟩ ≠ 0 := by
  classical
  have hex : ∃ i ∈ Icc 1 q.period, q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0 := by
    by_contra hc
    apply h
    unfold index
    split_ifs with h'
    · exact absurd h' hc
    · rfl
  have hspec := Nat.find_spec (p := fun i ↦ i ∈ Icc 1 q.period ∧
    q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0) ⟨hex.choose, hex.choose_spec⟩
  have hidx : q.index = Nat.find (p := fun i ↦ i ∈ Icc 1 q.period ∧
      q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0) ⟨hex.choose, hex.choose_spec⟩ := by
    unfold index
    split_ifs with h'
    · rfl
    · exact absurd hex h'
  rw [hidx]
  exact ⟨(mem_Icc.mp hspec.1).1, (mem_Icc.mp hspec.1).2, hspec.2⟩

/-- Minimality of `Quasipolynomial.index`. -/
theorem index_le_of_poly_ne_zero {R : Type*} [Semiring R] (q : Quasipolynomial R)
    {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ q.period)
    (hne : q.poly ⟨i % q.period, Nat.mod_lt i q.period_pos⟩ ≠ 0) :
    q.index ≤ i := by
  classical
  have hex : ∃ j ∈ Icc 1 q.period, q.poly ⟨j % q.period, Nat.mod_lt j q.period_pos⟩ ≠ 0 :=
    ⟨i, mem_Icc.mpr ⟨hi1, hi2⟩, hne⟩
  unfold index
  split_ifs with h'
  · exact Nat.find_min' _ ⟨mem_Icc.mpr ⟨hi1, hi2⟩, hne⟩
  · exact absurd hex h'

/-- Helper: a nonzero polynomial with nonnegative coefficients evaluates strictly positively
at any positive natural number. -/
private lemma eval_pos_of_nonneg_coeff {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {p : Polynomial R} (hp0 : p ≠ 0) (hnn : ∀ d, 0 ≤ p.coeff d)
    {k : ℕ} (hk : 0 < k) : 0 < p.eval (k : R) := by
  have hlc : 0 < p.coeff p.natDegree :=
    lt_of_le_of_ne (hnn p.natDegree) (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hp0))
  have hk_pos : (0 : R) < (k : R) := Nat.cast_pos.mpr hk
  rw [Polynomial.eval_eq_sum_range]
  have hmem : p.natDegree ∈ range (p.natDegree + 1) := mem_range.mpr (Nat.lt_succ_self _)
  have hterm : 0 < p.coeff p.natDegree * (k : R) ^ p.natDegree :=
    mul_pos hlc (pow_pos hk_pos _)
  exact lt_of_lt_of_le hterm (single_le_sum (f := fun i ↦ p.coeff i * (k : R) ^ i)
    (fun i _ ↦ mul_nonneg (hnn i) (pow_nonneg (le_of_lt hk_pos) i)) hmem)

/-- Coefficient positivity implies saturation for any quasipolynomial over an ordered ring. -/
theorem IsPositive.isSaturated {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {q : Quasipolynomial R} (hpos : q.IsPositive) :
    q.IsSaturated := by
  intro hne
  obtain ⟨h1, _, hpne⟩ := q.index_spec hne
  exact ne_of_gt (eval_pos_of_nonneg_coeff hpne (hpos _) h1)

end Quasipolynomial

/-- Polynomial specialization of positivity implies saturation:
if $p(k) = \sum a_i k^i$ has nonnegative coefficients and $p(k) \neq 0$ for some $k \ge 1$,
then $p(1) \neq 0$. -/
theorem polynomial_positive_implies_saturated {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : Polynomial R) (hnn : ∀ d, 0 ≤ p.coeff d)
    {k : ℕ} (hk : p.eval (k : R) ≠ 0) :
    p.eval 1 ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro h0; simp [h0] at hk
  have hpos : 0 < p.eval ((1 : ℕ) : R) :=
    Quasipolynomial.eval_pos_of_nonneg_coeff hp0 hnn Nat.one_pos
  simpa using ne_of_gt hpos

/-! ### Period-2 Odd-Dilation Reduction -/

/-- If a period-2 quasipolynomial $q$ agreeing with a counting function
$d : \mathbb{N} \to \mathbb{N}$ on positive integers has nonnegative coefficients, then
$d(1) \ge 1$ iff there exists an odd integer $k$ with $d(k) \ge 1$. -/
theorem period_two_positive_odd_iff (d : ℕ → ℕ) (q : Quasipolynomial ℚ)
    (hper : q.period = 2) (hpos : q.IsPositive)
    (heval : ∀ k, 0 < k → q.eval k = (d k : ℚ)) :
    1 ≤ d 1 ↔ ∃ k : ℕ, Odd k ∧ 1 ≤ d k := by
  constructor
  · intro h1; exact ⟨1, odd_one, h1⟩
  · rintro ⟨k, hodd, hdk⟩
    have hk_pos : 0 < k := by
      rcases hodd with ⟨m, rfl⟩; omega
    have hmod : k % q.period = 1 := by
      rw [hper]; exact Nat.odd_iff.mp hodd
    have h1mod : 1 % q.period = 1 := by
      rw [hper]
    have hq1_ne : q.poly ⟨1, by omega⟩ ≠ 0 := by
      intro h0
      have hk_val := heval k hk_pos
      unfold Quasipolynomial.eval at hk_val
      have hidx : (⟨k % q.period, Nat.mod_lt k q.period_pos⟩ : Fin q.period) =
          ⟨1, by omega⟩ := Fin.ext hmod
      rw [hidx, h0, Polynomial.eval_zero] at hk_val
      have hdpos : (0 : ℚ) < (d k : ℚ) := by exact_mod_cast (show 0 < d k by omega)
      linarith
    have hval1_pos : (0 : ℚ) < q.eval 1 := by
      unfold Quasipolynomial.eval
      have hidx : (⟨1 % q.period, Nat.mod_lt 1 q.period_pos⟩ : Fin q.period) =
          ⟨1, by omega⟩ := Fin.ext h1mod
      rw [hidx]
      exact Quasipolynomial.eval_pos_of_nonneg_coeff hq1_ne (hpos _) Nat.one_pos
    rw [heval 1 Nat.one_pos] at hval1_pos
    have hd1 : 0 < d 1 := by exact_mod_cast hval1_pos
    omega

/-! ### Rational Generating Series Characterization -/

/-- The `D`-th forward finite difference of a sequence `g : ℕ → ℂ`. -/
private def fwdDiff : ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, g => g
  | D + 1, g => fun n ↦ fwdDiff D g (n + 1) - fwdDiff D g n

private lemma fwdDiff_succ (D : ℕ) (g : ℕ → ℂ) (n : ℕ) :
    fwdDiff (D + 1) g n = fwdDiff D (fun m ↦ g (m + 1) - g m) n := by
  induction D generalizing g n with
  | zero => rfl
  | succ D ih =>
    change fwdDiff (D + 1) g (n + 1) - fwdDiff (D + 1) g n =
      fwdDiff D (fun m ↦ g (m + 1) - g m) (n + 1) - fwdDiff D (fun m ↦ g (m + 1) - g m) n
    rw [ih g (n + 1), ih g n]

private lemma fwdDiff_eq_sum_choose (D : ℕ) (g : ℕ → ℂ) (n : ℕ) :
    fwdDiff D g n =
      ∑ j ∈ range (D + 1), (-1 : ℂ) ^ j * (D.choose j : ℂ) * g (n + D - j) := by
  induction D generalizing n with
  | zero => simp [fwdDiff]
  | succ D ih =>
    simp only [fwdDiff, ih]
    rw [sum_range_succ' _ (D + 1)]
    have hsplit1 :
        ∑ j ∈ range (D + 1), (-1 : ℂ) ^ j * (D.choose j : ℂ) * g (n + 1 + D - j) =
        g (n + (D + 1)) +
        ∑ j ∈ range D, (-1 : ℂ) ^ (j + 1) * (D.choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1)) := by
      rw [sum_range_succ']
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        show n + 1 + D = n + (D + 1) by omega]
      rw [add_comm]
    have hsplit2 :
        ∑ j ∈ range (D + 1), (-1 : ℂ) ^ j * (D.choose j : ℂ) * g (n + D - j) =
        ∑ j ∈ range D, (-1 : ℂ) ^ j * (D.choose j : ℂ) * g (n + (D + 1) - (j + 1)) +
        (-1 : ℂ) ^ D * g n := by
      rw [sum_range_succ]
      simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.add_sub_cancel]
      congr 1
      refine sum_congr rfl fun j _ ↦ ?_
      have hsub : n + D - j = n + (D + 1) - (j + 1) := by omega
      rw [hsub]
    have hlast : ∑ j ∈ range (D + 1), (-1 : ℂ) ^ (j + 1) * ((D + 1).choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1)) =
        (∑ j ∈ range D, (-1 : ℂ) ^ (j + 1) * ((D + 1).choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1))) + (-1 : ℂ) ^ (D + 1) * g n := by
      rw [sum_range_succ]
      simp [Nat.choose_self]
    have hmid :
        (∑ j ∈ range D, (-1 : ℂ) ^ (j + 1) * (D.choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1))) -
        (∑ j ∈ range D, (-1 : ℂ) ^ j * (D.choose j : ℂ) * g (n + (D + 1) - (j + 1))) =
        ∑ j ∈ range D, (-1 : ℂ) ^ (j + 1) * ((D + 1).choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
      ring
    rw [hsplit1, hsplit2, hlast]
    have hmid' :
        (∑ j ∈ range D, (-1 : ℂ) ^ (j + 1) * (D.choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1))) -
        (∑ j ∈ range D, (-1 : ℂ) ^ j * (D.choose j : ℂ) * g (n + (D + 1) - (j + 1))) =
        ∑ j ∈ range D, (-1 : ℂ) ^ (j + 1) * ((D + 1).choose (j + 1) : ℂ) *
          g (n + (D + 1) - (j + 1)) := hmid
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [pow_succ (-1 : ℂ) D]
    linear_combination hmid'

private lemma fwdDiff_eval_poly_eq_zero {D : ℕ} {p : Polynomial ℂ} (hp : p.degree < D) :
    ∀ n, fwdDiff D (fun m ↦ p.eval (m : ℂ)) n = 0 := by
  induction D generalizing p with
  | zero =>
    have h0 : p = 0 := by
      by_contra hne
      rw [Polynomial.degree_eq_natDegree hne] at hp
      exact absurd (WithBot.coe_lt_coe.mp hp) (Nat.not_lt_zero _)
    intro n; simp [fwdDiff, h0]
  | succ D ih =>
    intro n
    rw [fwdDiff_succ]
    let q : Polynomial ℂ := p.comp (Polynomial.X + 1) - p
    have hq_eval : ∀ m : ℕ,
        q.eval (m : ℂ) = p.eval ((m + 1 : ℕ) : ℂ) - p.eval (m : ℂ) := fun m ↦ by
      simp [q, Polynomial.eval_comp]
    have hq_deg : q.degree < D := by
      by_cases hp0 : p = 0
      · simp [q, hp0]
      · have hle : p.natDegree ≤ D := by
          rw [Polynomial.degree_eq_natDegree hp0] at hp
          exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp hp)
        by_cases hd0 : p.natDegree = 0
        · have hq0 : q = 0 := by
            dsimp only [q]
            rw [Polynomial.eq_C_of_natDegree_eq_zero hd0]
            simp
          rw [hq0]; simp
        · have hq_nat : q.degree < (p.natDegree : WithBot ℕ) := by
            rw [Polynomial.degree_lt_iff_coeff_zero]
            intro k hk
            by_cases hgt : p.natDegree < k
            · have hcomp_deg : (p.comp (Polynomial.X + 1)).natDegree = p.natDegree := by
                rw [Polynomial.natDegree_comp]
                have hX1 : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 :=
                  Polynomial.natDegree_X_add_C 1
                simp [hX1]
              have hc1 : (p.comp (Polynomial.X + 1)).coeff k = 0 :=
                Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
              have hc2 : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
              simp [q, hc1, hc2]
            · have heq : k = p.natDegree := by omega
              subst heq
              have hX1 : (Polynomial.X + 1 : Polynomial ℂ).leadingCoeff = 1 :=
                (Polynomial.monic_X_add_C (1 : ℂ)).leadingCoeff
              have hX1d : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 :=
                Polynomial.natDegree_X_add_C 1
              have hc1 : (p.comp (Polynomial.X + 1)).coeff p.natDegree = p.leadingCoeff := by
                have hdeg : (p.comp (Polynomial.X + 1)).natDegree = p.natDegree := by
                  rw [Polynomial.natDegree_comp, hX1d, mul_one]
                rw [← hdeg, ← Polynomial.leadingCoeff,
                  Polynomial.leadingCoeff_comp (by rw [hX1d]; omega), hX1, one_pow, mul_one]
              dsimp only [q]
              rw [Polynomial.coeff_sub, hc1, Polynomial.coeff_natDegree, sub_self]
          exact lt_of_lt_of_le hq_nat (WithBot.coe_le_coe.mpr hle)
    simpa only [hq_eval] using ih hq_deg n

/-- Discrete integration: for any polynomial $q$, there exists a polynomial $p$ with
$p(m + 1) - p(m) = q(m)$ for all $m \in \mathbb{N}$. -/
private lemma exists_poly_fwdDiff_eq (q : Polynomial ℂ) :
    ∃ p : Polynomial ℂ, ∀ m : ℕ,
      p.eval ((m + 1 : ℕ) : ℂ) - p.eval (m : ℂ) = q.eval (m : ℂ) := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ ih₁ ih₂ =>
    obtain ⟨p₁, hp₁⟩ := ih₁
    obtain ⟨p₂, hp₂⟩ := ih₂
    refine ⟨p₁ + p₂, fun m ↦ ?_⟩
    simp only [Polynomial.eval_add]
    linear_combination hp₁ m + hp₂ m
  | monomial k c =>
    suffices ∀ k : ℕ, ∃ p : Polynomial ℂ,
        ∀ m : ℕ, p.eval ((m + 1 : ℕ) : ℂ) - p.eval (m : ℂ) = (m : ℂ) ^ k by
      obtain ⟨p, hp⟩ := this k
      refine ⟨Polynomial.C c * p, fun m ↦ ?_⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_monomial]
      linear_combination c * hp m
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      have hbin : ∀ m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 1) - (m : ℂ) ^ (k + 1) =
          ((k + 1 : ℕ) : ℂ) * (m : ℂ) ^ k +
            ∑ j ∈ range k, ((k + 1).choose j : ℂ) * (m : ℂ) ^ j := by
        intro m
        rw [Nat.cast_add, Nat.cast_one, add_pow]
        simp only [one_pow, mul_one]
        rw [sum_range_succ, sum_range_succ]
        simp only [Nat.choose_self, Nat.cast_one, mul_one,
          Nat.choose_succ_self_right]
        simp_rw [mul_comm ((m : ℂ) ^ _)]
        ring
      have hlower : ∃ r : Polynomial ℂ, ∀ m : ℕ,
          r.eval ((m + 1 : ℕ) : ℂ) - r.eval (m : ℂ) =
            ∑ j ∈ range k, ((k + 1).choose j : ℂ) * (m : ℂ) ^ j := by
        have hterm : ∀ j ∈ range k, ∃ pj : Polynomial ℂ, ∀ m : ℕ,
            pj.eval ((m + 1 : ℕ) : ℂ) - pj.eval (m : ℂ) =
              ((k + 1).choose j : ℂ) * (m : ℂ) ^ j := by
          intro j hj
          obtain ⟨pj, hpj⟩ := ih j (mem_range.mp hj)
          refine ⟨Polynomial.C (((k + 1).choose j : ℂ)) * pj, fun m ↦ ?_⟩
          simp only [Polynomial.eval_mul, Polynomial.eval_C]
          linear_combination ((k + 1).choose j : ℂ) * hpj m
        choose pj hpj using hterm
        refine ⟨∑ j ∈ (range k).attach, pj j.1 j.2, fun m ↦ ?_⟩
        have heval_sum : ∀ (x : ℂ),
            (∑ j ∈ (range k).attach, pj j.1 j.2).eval x =
              ∑ j ∈ (range k).attach, (pj j.1 j.2).eval x := fun x ↦
          map_sum (Polynomial.evalRingHom x) _ _
        rw [heval_sum, heval_sum, ← sum_sub_distrib]
        calc ∑ j ∈ (range k).attach, ((pj j.1 j.2).eval ((m + 1 : ℕ) : ℂ) -
              (pj j.1 j.2).eval (m : ℂ))
            = ∑ j ∈ (range k).attach, ((k + 1).choose j.1 : ℂ) * (m : ℂ) ^ j.1 :=
                sum_congr rfl fun j _ ↦ hpj j.1 j.2 m
          _ = ∑ j ∈ range k, ((k + 1).choose j : ℂ) * (m : ℂ) ^ j :=
                sum_attach (range k) (fun j ↦ ((k + 1).choose j : ℂ) * (m : ℂ) ^ j)
      obtain ⟨r, hr⟩ := hlower
      let p : Polynomial ℂ :=
        Polynomial.C (((k + 1 : ℕ) : ℂ)⁻¹) * (Polynomial.X ^ (k + 1) - r)
      refine ⟨p, fun m ↦ ?_⟩
      have hk_ne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      simp only [p, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X]
      have h1 := hbin m
      have h2 := hr m
      field_simp
      linear_combination h1 - h2

private lemma exists_poly_of_fwdDiff_eq_zero {D : ℕ} {g : ℕ → ℂ}
    (hg : ∀ n, fwdDiff D g n = 0) :
    ∃ p : Polynomial ℂ, ∀ m : ℕ, p.eval (m : ℂ) = g m := by
  induction D generalizing g with
  | zero => exact ⟨0, fun m ↦ by simpa [fwdDiff] using (hg m).symm⟩
  | succ D ih =>
    have hg' : ∀ n, fwdDiff D (fun m ↦ g (m + 1) - g m) n = 0 := fun n ↦ by
      rw [← fwdDiff_succ]; exact hg n
    obtain ⟨q, hq⟩ := ih hg'
    obtain ⟨p, hp⟩ := exists_poly_fwdDiff_eq q
    refine ⟨p + Polynomial.C (g 0 - p.eval 0), fun m ↦ ?_⟩
    induction m with
    | zero => simp
    | succ m ihm =>
      simp only [Polynomial.eval_add, Polynomial.eval_C] at ihm ⊢
      have h1 := hp m
      have h2 := hq m
      linear_combination ihm + h1 + h2

private lemma poly_coe_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    ((∑ i ∈ s, f i : Polynomial ℂ) : PowerSeries ℂ) = ∑ i ∈ s, (f i : PowerSeries ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, Polynomial.coe_add, ih, sum_insert ha]

private lemma one_sub_X_pow_natDegree {ℓ : ℕ} :
    (1 - Polynomial.X ^ ℓ : Polynomial ℂ).natDegree = ℓ := by
  have h1 : (1 - Polynomial.X ^ ℓ : Polynomial ℂ) = -(Polynomial.X ^ ℓ - Polynomial.C 1) := by
    simp
  rw [h1, Polynomial.natDegree_neg]
  exact Polynomial.natDegree_X_pow_sub_C (a := (1 : ℂ))

private lemma one_sub_X_pow_leadingCoeff {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (1 - Polynomial.X ^ ℓ : Polynomial ℂ).leadingCoeff = -1 := by
  have h1 : (1 - Polynomial.X ^ ℓ : Polynomial ℂ) = -(Polynomial.X ^ ℓ - Polynomial.C 1) := by
    simp
  rw [h1, Polynomial.leadingCoeff_neg,
    (Polynomial.monic_X_pow_sub_C (1 : ℂ) (ne_of_gt hℓ)).leadingCoeff]

private lemma one_sub_X_pow_pow_ne_zero {ℓ D : ℕ} (hℓ : 0 < ℓ) :
    ((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) ≠ 0 := by
  have h1 : (1 - Polynomial.X ^ ℓ : Polynomial ℂ) ≠ 0 := by
    intro h0
    have h2 := congrArg (Polynomial.eval 0) h0
    simp [zero_pow (ne_of_gt hℓ)] at h2
  exact pow_ne_zero D h1

/-- Coefficient of $X^n$ in $(1 - X^\ell)^D \cdot \mathrm{mk}\, f$ for $n \ge \ell D$. -/
private lemma coeff_one_sub_X_pow_mul_mk {ℓ D : ℕ} (f : ℕ → ℂ) {n : ℕ} (hn : ℓ * D ≤ n) :
    PowerSeries.coeff n ((((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) : PowerSeries ℂ) *
      PowerSeries.mk f) =
    ∑ j ∈ range (D + 1), (-1 : ℂ) ^ j * (D.choose j : ℂ) * f (n - j * ℓ) := by
  have hpoly : ((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) =
      ∑ j ∈ range (D + 1), Polynomial.C ((-1 : ℂ) ^ j * (D.choose j : ℂ)) *
        Polynomial.X ^ (j * ℓ) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [one_pow, mul_one, neg_eq_neg_one_mul, mul_pow, ← pow_mul, mul_comm ℓ j,
      map_mul, map_pow, map_neg, map_one, Polynomial.C_eq_natCast]
    ring
  rw [hpoly, poly_coe_sum, sum_mul, map_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj_le : j ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hjl_le : j * ℓ ≤ n :=
    le_trans (by rw [mul_comm]; exact Nat.mul_le_mul_left ℓ hj_le) hn
  rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp [hjl_le]

/-- a function $f : \mathbb{N} \to \mathbb{C}$
is a quasipolynomial of period $\ell \ge 1$ if and only if its generating series
$F(t) = \sum_{k \ge 0} f(k) t^k$ is a rational function $A(t)/B(t)$ with $\deg A < \deg B$
and every root of $B(t)$ an $\ell$-th root of unity. -/
theorem quasipolynomial_iff_rational_generating_series {ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ → ℂ) :
    (∃ q : Quasipolynomial ℂ, q.period = ℓ ∧ ∀ k, q.eval k = f k) ↔
    (∃ A B : Polynomial ℂ, B ≠ 0 ∧ A.degree < B.degree ∧
      (∀ ζ : ℂ, B.IsRoot ζ → ζ ^ ℓ = 1) ∧
      (B : PowerSeries ℂ) * PowerSeries.mk f = (A : PowerSeries ℂ)) := by
  constructor
  · rintro ⟨q, hper, hfeq⟩
    let D : ℕ := univ.sup (fun i : Fin q.period ↦ (q.poly i).natDegree) + 1
    let B : Polynomial ℂ := (1 - Polynomial.X ^ ℓ) ^ D
    have hB_ne : B ≠ 0 := one_sub_X_pow_pow_ne_zero hℓ
    have hB_natDeg : B.natDegree = ℓ * D := by
      rw [Polynomial.natDegree_pow' (by rw [one_sub_X_pow_leadingCoeff hℓ]; simp),
        one_sub_X_pow_natDegree, mul_comm]
    have hB_deg : B.degree = (ℓ * D : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hB_ne, hB_natDeg]
    have hvanish : ∀ n, ℓ * D ≤ n →
        PowerSeries.coeff n ((B : PowerSeries ℂ) * PowerSeries.mk f) = 0 := by
      intro n hn
      rw [coeff_one_sub_X_pow_mul_mk f hn]
      let r : Fin q.period := ⟨n % q.period, Nat.mod_lt n q.period_pos⟩
      let n0 : ℕ := n - D * ℓ
      have hn0 : n0 + D * ℓ = n := Nat.sub_add_cancel (by rw [mul_comm]; exact hn)
      let p : Polynomial ℂ :=
        (q.poly r).comp (Polynomial.C (n0 : ℂ) + Polynomial.C (ℓ : ℂ) * Polynomial.X)
      have hp_deg : p.degree < D := by
        by_cases hqr : q.poly r = 0
        · simp [p, hqr]
        · have hle : (q.poly r).natDegree < D :=
            Nat.lt_succ_of_le (le_sup (f := fun i : Fin q.period ↦ (q.poly i).natDegree)
              (mem_univ r))
          have hlin_deg :
              (Polynomial.C (n0 : ℂ) + Polynomial.C (ℓ : ℂ) * Polynomial.X).natDegree ≤ 1 := by
            have h1 : (Polynomial.C (ℓ : ℂ) * Polynomial.X).natDegree ≤ 1 :=
              le_trans Polynomial.natDegree_mul_le (by simp)
            exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) h1)
          have hpn : p.natDegree ≤ (q.poly r).natDegree := by
            calc p.natDegree ≤ (q.poly r).natDegree *
                  (Polynomial.C (n0 : ℂ) + Polynomial.C (ℓ : ℂ) * Polynomial.X).natDegree :=
                  Polynomial.natDegree_comp_le
              _ ≤ (q.poly r).natDegree * 1 := Nat.mul_le_mul_left _ hlin_deg
              _ = (q.poly r).natDegree := mul_one _
          exact lt_of_le_of_lt Polynomial.degree_le_natDegree
            (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hpn hle))
      have hfd := fwdDiff_eval_poly_eq_zero hp_deg 0
      rw [fwdDiff_eq_sum_choose] at hfd
      convert hfd using 1
      refine sum_congr rfl fun j hj ↦ ?_
      have hj_le : j ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hj)
      congr 1
      rw [← hfeq (n - j * ℓ)]
      unfold Quasipolynomial.eval
      have hmod : (n - j * ℓ) % q.period = n % q.period := by
        rw [hper]
        have h1 : n - j * ℓ + j * ℓ = n := Nat.sub_add_cancel
          (le_trans (by rw [mul_comm]; exact Nat.mul_le_mul_left ℓ hj_le) hn)
        have h2 := congrArg (· % ℓ) h1
        simpa [Nat.add_mul_mod_self_right] using h2
      have hidx : (⟨(n - j * ℓ) % q.period, Nat.mod_lt _ q.period_pos⟩ : Fin q.period) = r :=
        Fin.ext hmod
      rw [hidx]
      simp only [p, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, zero_add]
      congr 1
      have hnat : n - j * ℓ = n0 + ℓ * (D - j) := by
        have h1 : j * ℓ ≤ D * ℓ := Nat.mul_le_mul_right ℓ hj_le
        have h2 : (D - j) * ℓ = D * ℓ - j * ℓ := Nat.sub_mul D j ℓ
        have h3 : ℓ * (D - j) = (D - j) * ℓ := mul_comm _ _
        omega
      rw [hnat]
      push_cast
      ring
    let F : PowerSeries ℂ := PowerSeries.mk f
    let A : Polynomial ℂ := ∑ k ∈ range (ℓ * D),
      Polynomial.monomial k (PowerSeries.coeff k ((B : PowerSeries ℂ) * F))
    have hA_deg : A.degree < B.degree := by
      rw [hB_deg]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro k hk
      exact lt_of_le_of_lt (Polynomial.degree_monomial_le k _)
        (WithBot.coe_lt_coe.mpr (mem_range.mp hk))
    refine ⟨A, B, hB_ne, hA_deg, fun ζ hζ ↦ ?_, ?_⟩
    · simp only [B, Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X] at hζ
      have h1 : 1 - ζ ^ ℓ = 0 := by
        by_contra hne
        exact pow_ne_zero D hne hζ
      exact (sub_eq_zero.mp h1).symm
    · ext n
      have hAcoeff : A.coeff n =
          if n < ℓ * D then PowerSeries.coeff n ((B : PowerSeries ℂ) * F) else 0 := by
        change (Polynomial.lcoeff ℂ n) A = _
        dsimp only [A]
        rw [map_sum]
        simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial, Finsupp.single_apply,
          sum_ite_eq', mem_range]
      rw [Polynomial.coeff_coe, hAcoeff]
      by_cases hn : n < ℓ * D
      · simp [F, hn]
      · simp only [hn, ↓reduceIte]
        exact hvanish n (Nat.le_of_not_lt hn)
  · rintro ⟨A, B, hB_ne, hAB_deg, hroots, hBF⟩
    let D : ℕ := B.natDegree
    have hB_dvd : B ∣ (1 - Polynomial.X ^ ℓ) ^ D := by
      have hsplit : B.Splits := IsAlgClosed.splits B
      rw [hsplit.eq_prod_roots]
      have hprod_dvd : (B.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod ∣
          (1 - Polynomial.X ^ ℓ) ^ D := by
        have hcard : B.roots.card = D := hsplit.natDegree_eq_card_roots.symm
        have hlen : (B.roots.map fun a ↦ Polynomial.X - Polynomial.C a).card = D := by
          rw [Multiset.card_map, hcard]
        rw [← hlen]
        have hstep : ∀ s : Multiset ℂ,
            (∀ a ∈ s, Polynomial.X - Polynomial.C a ∣ (1 - Polynomial.X ^ ℓ : Polynomial ℂ)) →
            (s.map fun a ↦ Polynomial.X - Polynomial.C a).prod ∣
              ((1 - Polynomial.X ^ ℓ : Polynomial ℂ)) ^ s.card := by
          intro s hs
          induction s using Multiset.induction_on with
          | empty => simp
          | cons a s ih =>
            rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
            exact mul_dvd_mul (hs a (Multiset.mem_cons_self a s))
              (ih fun b hb ↦ hs b (Multiset.mem_cons_of_mem hb))
        have hres := hstep B.roots fun a ha ↦ by
          have hr : B.IsRoot a := (Polynomial.mem_roots hB_ne).mp ha
          have ha_pow : a ^ ℓ = 1 := hroots a hr
          rw [Polynomial.dvd_iff_isRoot]
          simp [Polynomial.IsRoot.def, ha_pow]
        simpa [Multiset.card_map] using hres
      exact (Polynomial.isUnit_C.mpr
        (Polynomial.leadingCoeff_ne_zero.mpr hB_ne).isUnit).mul_left_dvd.mpr hprod_dvd
    obtain ⟨Q, hQ⟩ := hB_dvd
    have hpow_ne : ((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) ≠ 0 :=
      one_sub_X_pow_pow_ne_zero hℓ
    have hpow_deg : ((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ).degree = (ℓ * D : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hpow_ne,
        Polynomial.natDegree_pow' (by rw [one_sub_X_pow_leadingCoeff hℓ]; simp),
        one_sub_X_pow_natDegree, mul_comm]
    have hQ_ne : Q ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hQ; exact hpow_ne hQ
    have hQA_deg : (Q * A).degree < (ℓ * D : ℕ) := by
      rw [← hpow_deg, hQ, mul_comm B Q, Polynomial.degree_mul, Polynomial.degree_mul]
      have hQ_deg : Q.degree = (Q.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hQ_ne
      rw [hQ_deg]
      exact WithBot.add_lt_add_left (WithBot.coe_ne_bot) hAB_deg
    have hpow_mul : ((((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) : PowerSeries ℂ)) *
        PowerSeries.mk f = ((Q * A : Polynomial ℂ) : PowerSeries ℂ) := by
      calc ((((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) : PowerSeries ℂ)) * PowerSeries.mk f
          = ((Q : PowerSeries ℂ) * (B : PowerSeries ℂ)) * PowerSeries.mk f := by
              rw [hQ, mul_comm B Q, Polynomial.coe_mul]
        _ = (Q : PowerSeries ℂ) * ((B : PowerSeries ℂ) * PowerSeries.mk f) := mul_assoc _ _ _
        _ = ((Q * A : Polynomial ℂ) : PowerSeries ℂ) := by
              rw [hBF, Polynomial.coe_mul]
    have hpoly_res : ∀ r : Fin ℓ, ∃ p : Polynomial ℂ,
        ∀ m : ℕ, p.eval ((m * ℓ + r.1 : ℕ) : ℂ) = f (m * ℓ + r.1) := by
      intro r
      have hfd : ∀ m : ℕ, fwdDiff D (fun k ↦ f (k * ℓ + r.1)) m = 0 := by
        intro m
        rw [fwdDiff_eq_sum_choose]
        have hn_ge : ℓ * D ≤ (m + D) * ℓ + r.1 := by
          rw [add_mul, mul_comm ℓ D]; omega
        have hcoeff0 : PowerSeries.coeff ((m + D) * ℓ + r.1)
            (((((1 - Polynomial.X ^ ℓ) ^ D : Polynomial ℂ) : PowerSeries ℂ)) *
              PowerSeries.mk f) = 0 := by
          rw [hpow_mul, Polynomial.coeff_coe]
          exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hQA_deg
            (WithBot.coe_le_coe.mpr hn_ge))
        rw [coeff_one_sub_X_pow_mul_mk f hn_ge] at hcoeff0
        convert hcoeff0 using 1
        refine sum_congr rfl fun j hj ↦ ?_
        have hj_le : j ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hj)
        congr 2
        have h1 : (m + D - j) * ℓ = (m + D) * ℓ - j * ℓ := Nat.sub_mul (m + D) j ℓ
        have h2 : j * ℓ ≤ (m + D) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
        omega
      obtain ⟨q_r, hq_r⟩ := exists_poly_of_fwdDiff_eq_zero hfd
      let p_r : Polynomial ℂ :=
        q_r.comp (Polynomial.C ((ℓ : ℂ)⁻¹) * (Polynomial.X - Polynomial.C (r.1 : ℂ)))
      refine ⟨p_r, fun m ↦ ?_⟩
      have hℓ_ne : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hℓ)
      simp only [p_r, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X, Nat.cast_add, Nat.cast_mul]
      have hsimp : (ℓ : ℂ)⁻¹ * ((m : ℂ) * (ℓ : ℂ) + (r.1 : ℂ) - (r.1 : ℂ)) = (m : ℂ) := by
        field_simp; ring
      rw [hsimp]
      exact hq_r m
    choose pr hpr using hpoly_res
    refine ⟨⟨ℓ, hℓ, pr⟩, rfl, fun k ↦ ?_⟩
    unfold Quasipolynomial.eval
    have hk : k / ℓ * ℓ + k % ℓ = k := by
      have := Nat.div_add_mod k ℓ; linarith
    have h := hpr ⟨k % ℓ, Nat.mod_lt k hℓ⟩ (k / ℓ)
    simpa only [hk] using h

end CslibFrontier
