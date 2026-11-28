module

public import CslibFrontier.Probability.Product
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Kim–Vu Style Concentration for Almost-Independent Distributions

This module formalizes `(δ, m)`-almost independence for binary distributions over a finite index
set and proves a Kim–Vu style moment and tail concentration inequality for low-degree multilinear
polynomials with nonnegative integer coefficients via the moment method.

It also proves that the indicator matrix `F_{(x, y)} = 1[f(x) = y]` of a uniform random permutation
`f` on a finite type `α` is `(1, M)`-almost independent whenever `2 * (M - 1) ≤ Fintype.card α`.

## Main definitions

* `CslibFrontier.Probability.Concentration.IsAlmostIndependent`: `(δ, m)`-almost independence of a
  binary distribution over `ι → Bool`.
* `CslibFrontier.Probability.Concentration.marginalProd`: the product distribution with independent
  coordinates matching the marginals of `P`.
* `CslibFrontier.Probability.Concentration.evalPoly`, `derivPoly`, `muStar`, `maxDerivExp`:
  multilinear polynomial evaluation, formal partial derivative `∂_B P`, expectation under the
  product of marginals, and maximum nonempty derivative expectation.
* `CslibFrontier.Probability.Concentration.permIndicatorPMF`: distribution of the indicator matrix
  of a uniform random permutation.

## Main results

* `CslibFrontier.Probability.Concentration.kimVu_moment_le`: the `m`-th moment bound
  `E_{P}[P(x)^m] ≤ ((1 + δ)^r · (μ* + r^r m^r E*))^m`.
* `CslibFrontier.Probability.Concentration.kimVu_concentration_unnormalized`: upper-tail bound
  `Pr[P(x) ≥ t] ≤ ((1 + δ)^r · (μ* + r^r m^r E*) / t)^m`.
* `CslibFrontier.Probability.Concentration.kimVu_concentration`: normalized Kim–Vu style
  concentration inequality around `μ*`.
* `CslibFrontier.Probability.Concentration.permIndicator_isAlmostIndependent`: `(1, M)`-almost
  independence of random permutation indicators.
-/

public section

namespace CslibFrontier.Probability.Concentration

open Cslib.Probability

/-! ### Definition of `(δ, m)`-almost independence and product marginals -/

/-- The indicator event that every coordinate in `S` is `true`. -/
def allTrue {ι : Type*} (S : Finset ι) (x : ι → Bool) : Prop :=
  ∀ i ∈ S, x i = true

/-- Characterization of `allTrue`. -/
theorem allTrue_iff {ι : Type*} (S : Finset ι) (x : ι → Bool) :
    allTrue S x ↔ ∀ i ∈ S, x i = true := by rfl

instance {ι : Type*} (S : Finset ι) (x : ι → Bool) : Decidable (allTrue S x) :=
  inferInstanceAs (Decidable (∀ i ∈ S, x i = true))

/-- Probability that `allTrue S x` holds under a PMF `P` over `ι → Bool`. -/
noncomputable def probAllTrue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (S : Finset ι) : ℝ :=
  ∑ x : ι → Bool, if allTrue S x then (P x).toReal else 0

/-- Marginal probability that coordinate `i` equals `true`. -/
noncomputable def marginalTrue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (i : ι) : ℝ :=
  probAllTrue P {i}

/-- A distribution `P` over `ι → Bool` is `(δ, m)`-almost independent if for every set `M` with
`|M| < m` and every `j ∉ M`,
`Pr[x_j = 1 ∧ ∀ i ∈ M, x_i = 1] ≤ (1 + δ) · Pr[x_j = 1] · Pr[∀ i ∈ M, x_i = 1]`.
Written in multiplicative form to avoid division by zero when the conditioning event has
probability `0`. -/
def IsAlmostIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (δ : ℝ) (m : ℕ) : Prop :=
  ∀ M : Finset ι, M.card < m → ∀ j : ι, j ∉ M →
    probAllTrue P (insert j M) ≤ marginalTrue P j * (1 + δ) * probAllTrue P M

/-- Nonnegativity of `probAllTrue`. -/
theorem probAllTrue_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (S : Finset ι) :
    0 ≤ probAllTrue P S :=
  Finset.sum_nonneg fun x _ => by split_ifs <;> positivity

/-- `probAllTrue P ∅ = 1`. -/
@[simp] theorem probAllTrue_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) :
    probAllTrue P ∅ = 1 := by
  simp [probAllTrue, allTrue, PMF.sum_toReal]

/-- Equivalence with the conditional-probability phrasing whenever the conditioning event has
positive probability. -/
theorem IsAlmostIndependent.cond_prob_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : PMF (ι → Bool)} {δ : ℝ} {m : ℕ} (hP : IsAlmostIndependent P δ m)
    {M : Finset ι} (hM : M.card < m) {j : ι} (hj : j ∉ M)
    (hpos : 0 < probAllTrue P M) :
    probAllTrue P (insert j M) / probAllTrue P M ≤ marginalTrue P j * (1 + δ) :=
  (div_le_iff₀ hpos).mpr (hP M hM j hj)

/-- Under `(δ, m)`-almost independence with `0 ≤ δ`, any conjunction of `|S| ≤ m` coordinates has
probability at most `(1 + δ)^{|S|}` times the product of marginals. -/
theorem IsAlmostIndependent.probAllTrue_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : PMF (ι → Bool)} {δ : ℝ} {m : ℕ} (hδ : 0 ≤ δ) (hP : IsAlmostIndependent P δ m)
    {S : Finset ι} (hS : S.card ≤ m) :
    probAllTrue P S ≤ (1 + δ) ^ S.card * ∏ i ∈ S, marginalTrue P i := by
  induction S using Finset.induction with
  | empty =>
    simp
  | insert j M hj ih =>
    rw [Finset.card_insert_of_notMem hj] at hS ⊢
    rw [Finset.prod_insert hj]
    have hMlt : M.card < m := Nat.lt_of_succ_le hS
    have hstep := hP M hMlt j hj
    have hih := ih (Nat.le_of_lt hMlt)
    have hmarg : 0 ≤ marginalTrue P j := probAllTrue_nonneg P {j}
    have h1δ : 0 ≤ 1 + δ := by linarith
    calc probAllTrue P (insert j M)
        ≤ marginalTrue P j * (1 + δ) * probAllTrue P M := hstep
      _ ≤ marginalTrue P j * (1 + δ) * ((1 + δ) ^ M.card * ∏ i ∈ M, marginalTrue P i) :=
          mul_le_mul_of_nonneg_left hih (mul_nonneg hmarg h1δ)
      _ = (1 + δ) ^ (M.card + 1) * (marginalTrue P j * ∏ i ∈ M, marginalTrue P i) := by
          rw [pow_succ]; ring

/-- The product distribution with independent coordinates and the same marginals as `P`. -/
noncomputable def marginalProd {ι : Type*} [Fintype ι] (P : PMF (ι → Bool)) : PMF (ι → Bool) :=
  PMF.pi fun i => P.map fun x => x i

/-- Under the product marginal distribution, `probAllTrue` equals the product of marginals of
`P`. -/
theorem probAllTrue_marginalProd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (S : Finset ι) :
    probAllTrue (marginalProd P) S = ∏ i ∈ S, marginalTrue P i := by
  have hcoord : ∀ i : ι, ((P.map fun x => x i) true).toReal = marginalTrue P i := by
    intro i
    rw [PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum (fun x _ => by split_ifs <;> simp [PMF.apply_ne_top])]
    simp only [marginalTrue, probAllTrue, allTrue, Finset.mem_singleton, forall_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x i = true <;> simp [hx]
  have hpi : ∀ x : ι → Bool,
      ((marginalProd P) x).toReal = ∏ i : ι, ((P.map fun y => y i) (x i)).toReal := by
    intro x
    simp only [marginalProd, PMF.pi_apply]
    rw [ENNReal.toReal_prod]
  have hsum :
      probAllTrue (marginalProd P) S =
        ∏ i : ι, ∑ b : Bool,
          (if i ∈ S → b = true then ((P.map fun y => y i) b).toReal else 0) := by
    rw [Fintype.prod_sum]
    simp only [probAllTrue]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hpi x]
    by_cases hx : allTrue S x
    · simp only [hx, ↓reduceIte]
      refine Finset.prod_congr rfl fun i _ => ?_
      split_ifs with hcond
      · rfl
      · exact absurd (fun hi => hx i hi) hcond
    · simp only [hx, ↓reduceIte]
      rw [allTrue] at hx
      push Not at hx
      obtain ⟨i₀, hi₀, hne⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀, hne])
  rw [hsum]
  calc ∏ i : ι, ∑ b : Bool, (if i ∈ S → b = true then ((P.map fun y => y i) b).toReal else 0)
      = ∏ i : ι, if i ∈ S then marginalTrue P i else 1 := by
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S
        · simp only [hi, true_implies, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero,
            hcoord i]
        · simp only [hi, false_implies, ↓reduceIte, Fintype.sum_bool]
          have htot := PMF.sum_toReal (P.map fun y => y i)
          simpa [Fintype.sum_bool] using htot
    _ = ∏ i ∈ S, marginalTrue P i := by
        rw [Finset.prod_ite_mem, Finset.univ_inter]

/-! ### Multilinear polynomials, derivatives, and combinatorial bound -/

/-- Evaluation of a multilinear polynomial `P(x) = ∑_{e ∈ F} ∏_{i ∈ e} x_i` on `x : ι → Bool`.
Represented as a list of monomial supports to allow repeated monomials (nonnegative integer
coefficients). -/
def evalPoly {ι : Type*} (F : List (Finset ι)) (x : ι → Bool) : ℝ :=
  (F.map fun e => if allTrue e x then (1 : ℝ) else 0).sum

/-- Evaluation of `evalPoly` as a list sum of indicators. -/
theorem evalPoly_eq_sum {ι : Type*} (F : List (Finset ι)) (x : ι → Bool) :
    evalPoly F x = (F.map fun e => if allTrue e x then (1 : ℝ) else 0).sum := by rfl

/-- Nonnegativity of `evalPoly`. -/
theorem evalPoly_nonneg {ι : Type*} (F : List (Finset ι)) (x : ι → Bool) :
    0 ≤ evalPoly F x := by
  induction F with
  | nil => simp [evalPoly]
  | cons e F ih =>
    simp only [evalPoly, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs <;> linarith

/-- Formal partial derivative `∂_B P` of a multilinear polynomial `F`. -/
def derivPoly {ι : Type*} [DecidableEq ι] (F : List (Finset ι)) (B : Finset ι) :
    List (Finset ι) :=
  (F.filter fun e => decide (B ⊆ e)).map fun e => e \ B

/-- Formula for `derivPoly`. -/
theorem derivPoly_eq_map_filter {ι : Type*} [DecidableEq ι] (F : List (Finset ι)) (B : Finset ι) :
    derivPoly F B = (F.filter fun e => decide (B ⊆ e)).map fun e => e \ B := by rfl

/-- The empty derivative leaves a polynomial unchanged. -/
@[simp] theorem derivPoly_empty {ι : Type*} [DecidableEq ι] (F : List (Finset ι)) :
    derivPoly F ∅ = F := by
  simp [derivPoly]

/-- Expectation of `evalPoly F` under a distribution `P`. -/
noncomputable def expectPoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) : ℝ :=
  ∑ x : ι → Bool, (P x).toReal * evalPoly F x

/-- `expectPoly` equals the sum of `probAllTrue` over the monomials in `F`. -/
theorem expectPoly_eq_sum_probAllTrue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) :
    expectPoly P F = (F.map fun e => probAllTrue P e).sum := by
  induction F with
  | nil => simp [expectPoly, evalPoly]
  | cons e F ih =>
    simp only [expectPoly, evalPoly, List.map_cons, List.sum_cons] at ih ⊢
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ih]
    congr 1
    simp only [probAllTrue]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring

/-- Nonnegativity of `expectPoly`. -/
theorem expectPoly_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) :
    0 ≤ expectPoly P F :=
  Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (evalPoly_nonneg F x)

/-- Expectation `μ* = E_{x ← marginalProd P}[P(x)]`. -/
noncomputable def muStar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) : ℝ :=
  expectPoly (marginalProd P) F

/-- `muStar` equals `expectPoly (marginalProd P) F`. -/
theorem muStar_eq_expectPoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) :
    muStar P F = expectPoly (marginalProd P) F := by rfl

/-- Maximum nonempty derivative expectation
`E* = max_{∅ ⊂neq B ⊆ ι} E_{x ← marginalProd P}[(∂_B P)(x)]`, defaulting to `0` when `ι` is
empty. -/
noncomputable def maxDerivExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) : ℝ :=
  let nonemptySubs : Finset (Finset ι) := Finset.univ.filter Finset.Nonempty
  if h : nonemptySubs.Nonempty then
    nonemptySubs.sup' h fun B => expectPoly (marginalProd P) (derivPoly F B)
  else
    0

/-- Upper bound on `maxDerivExp` from a uniform upper bound on every nonempty derivative. -/
theorem maxDerivExp_le_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ B : Finset ι, B.Nonempty → expectPoly (marginalProd P) (derivPoly F B) ≤ c) :
    maxDerivExp P F ≤ c := by
  simp only [maxDerivExp]
  split_ifs with hne
  · rw [Finset.sup'_le_iff]
    intro B hmem
    exact hB B (Finset.mem_filter.mp hmem).2
  · exact hc

/-- `maxDerivExp` is nonnegative. -/
theorem maxDerivExp_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) :
    0 ≤ maxDerivExp P F := by
  simp only [maxDerivExp]
  split_ifs with h
  · obtain ⟨B, hB⟩ := h
    exact (expectPoly_nonneg (marginalProd P) (derivPoly F B)).trans
      (Finset.le_sup' (fun B => expectPoly (marginalProd P) (derivPoly F B)) hB)
  · exact le_rfl

/-- Every nonempty `B` has `E_{marginalProd P}[∂_B P] ≤ maxDerivExp P F`. -/
theorem expectPoly_derivPoly_le_maxDerivExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {B : Finset ι} (hB : B.Nonempty) :
    expectPoly (marginalProd P) (derivPoly F B) ≤ maxDerivExp P F := by
  simp only [maxDerivExp]
  have hmem : B ∈ (Finset.univ : Finset (Finset ι)).filter Finset.Nonempty := by
    simp [hB]
  have hne : ((Finset.univ : Finset (Finset ι)).filter Finset.Nonempty).Nonempty := ⟨B, hmem⟩
  simp only [hne, ↓reduceDIte]
  exact Finset.le_sup' (fun B => expectPoly (marginalProd P) (derivPoly F B)) hmem

/-- Helper inequality: for `r ≥ 2`, `∑_{b=1}^r 2^{b-r} / b! ≤ 1`. -/
private theorem sum_two_pow_div_factorial_le_one (r : ℕ) (hr : 2 ≤ r) :
    ∑ b ∈ Finset.Icc 1 r, (2 : ℝ) ^ ((b : ℤ) - (r : ℤ)) / (b.factorial : ℝ) ≤ 1 := by
  induction r, hr using Nat.le_induction with
  | base =>
    have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [hIcc]
    norm_num [Nat.factorial]
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hhalf :
        ∑ b ∈ Finset.Icc 1 k, (2 : ℝ) ^ ((b : ℤ) - ((k + 1 : ℕ) : ℤ)) / (b.factorial : ℝ) =
          (1 / 2 : ℝ) * ∑ b ∈ Finset.Icc 1 k,
            (2 : ℝ) ^ ((b : ℤ) - (k : ℤ)) / (b.factorial : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hexp : (b : ℤ) - ((k + 1 : ℕ) : ℤ) = ((b : ℤ) - (k : ℤ)) + (-1 : ℤ) := by omega
      rw [hexp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    rw [hhalf]
    have hfac : (6 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
      have : 6 ≤ (k + 1).factorial := by
        calc 6 = Nat.factorial 3 := rfl
          _ ≤ (k + 1).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hlast : (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)) /
        ((k + 1).factorial : ℝ) ≤ 1 / 6 := by
      rw [sub_self, zpow_zero]
      exact one_div_le_one_div_of_le (by norm_num) hfac
    linarith

/-- Combinatorial lemma: for any `N : ℕ` and `r ≥ 1`, `∑_{b=1}^r C(N, b) ≤ N^r`. -/
theorem sum_choose_Icc_le_pow (N r : ℕ) (hr : 1 ≤ r) :
    (∑ b ∈ Finset.Icc 1 r, N.choose b : ℕ) ≤ N ^ r := by
  by_cases hN0 : N = 0
  · subst hN0
    have hzero : ∀ b ∈ Finset.Icc 1 r, Nat.choose 0 b = 0 := by
      intro b hb
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      cases b with
      | zero => omega
      | succ b' => exact Nat.choose_zero_succ b'
    rw [Finset.sum_eq_zero hzero]
    exact Nat.zero_le _
  by_cases hN1 : N = 1
  · subst hN1
    rw [one_pow]
    have hsum : ∑ b ∈ Finset.Icc 1 r, Nat.choose 1 b = 1 := by
      rw [Finset.sum_eq_single 1]
      · rfl
      · intro b hb hne
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
        exact Nat.choose_eq_zero_of_lt (by omega)
      · intro hnot
        exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hr⟩) hnot
    omega
  have hN2 : 2 ≤ N := by omega
  by_cases hr1 : r = 1
  · subst hr1
    simp
  have hr2 : 2 ≤ r := by omega
  suffices h : (∑ b ∈ Finset.Icc 1 r, (N.choose b : ℝ)) ≤ (N : ℝ) ^ r by
    exact_mod_cast h
  have hterm : ∀ b ∈ Finset.Icc 1 r,
      (N.choose b : ℝ) ≤ (N : ℝ) ^ r * ((2 : ℝ) ^ ((b : ℤ) - (r : ℤ)) / (b.factorial : ℝ)) := by
    intro b hb
    have hbr : b ≤ r := (Finset.mem_Icc.mp hb).2
    have hch : (N.choose b : ℝ) * (b.factorial : ℝ) ≤ (N : ℝ) ^ b := by
      have hnat : N.choose b * b.factorial ≤ N ^ b := by
        rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow N b
      exact_mod_cast hnat
    have hfacpos : (0 : ℝ) < (b.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos b)
    have hch' : (N.choose b : ℝ) ≤ (N : ℝ) ^ b / (b.factorial : ℝ) :=
      (le_div_iff₀ hfacpos).mpr hch
    have hpow : (N : ℝ) ^ b ≤ (N : ℝ) ^ r * (2 : ℝ) ^ ((b : ℤ) - (r : ℤ)) := by
      have hdiff : (b : ℤ) - (r : ℤ) = -((r - b : ℕ) : ℤ) := by omega
      rw [hdiff, zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h2N : (2 : ℝ) ^ (r - b) ≤ (N : ℝ) ^ (r - b) :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hN2) (r - b)
      calc (N : ℝ) ^ b * (2 : ℝ) ^ (r - b)
          ≤ (N : ℝ) ^ b * (N : ℝ) ^ (r - b) :=
            mul_le_mul_of_nonneg_left h2N (by positivity)
        _ = (N : ℝ) ^ (b + (r - b)) := (pow_add (N : ℝ) b (r - b)).symm
        _ = (N : ℝ) ^ r := by rw [Nat.add_sub_of_le hbr]
    calc (N.choose b : ℝ)
        ≤ (N : ℝ) ^ b / (b.factorial : ℝ) := hch'
      _ ≤ ((N : ℝ) ^ r * (2 : ℝ) ^ ((b : ℤ) - (r : ℤ))) / (b.factorial : ℝ) :=
          div_le_div_of_nonneg_right hpow hfacpos.le
      _ = (N : ℝ) ^ r * ((2 : ℝ) ^ ((b : ℤ) - (r : ℤ)) / (b.factorial : ℝ)) := by ring
  calc ∑ b ∈ Finset.Icc 1 r, (N.choose b : ℝ)
      ≤ ∑ b ∈ Finset.Icc 1 r, (N : ℝ) ^ r * ((2 : ℝ) ^ ((b : ℤ) - (r : ℤ)) / (b.factorial : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) ^ r * ∑ b ∈ Finset.Icc 1 r, (2 : ℝ) ^ ((b : ℤ) - (r : ℤ)) / (b.factorial : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (N : ℝ) ^ r * 1 :=
        mul_le_mul_of_nonneg_left (sum_two_pow_div_factorial_le_one r hr2) (by positivity)
    _ = (N : ℝ) ^ r := mul_one _

/-- Number of nonempty subsets of `U` of size at most `r` is at most `|U|^r` (for `r ≥ 1`). -/
theorem card_nonempty_subsets_le {ι : Type*} (U : Finset ι) {r : ℕ} (hr : 1 ≤ r) :
    (U.powerset.filter fun B => B.Nonempty ∧ B.card ≤ r).card ≤ U.card ^ r := by
  classical
  have hpart :
      (U.powerset.filter fun B => B.Nonempty ∧ B.card ≤ r) =
        (Finset.Icc 1 r).biUnion fun b => U.powersetCard b := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_Icc,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hne, hle⟩
      exact ⟨B.card, ⟨Finset.card_pos.mpr hne, hle⟩, hsub, rfl⟩
    · rintro ⟨b, ⟨hb1, hbr⟩, hsub, hcard⟩
      exact ⟨hsub, Finset.card_pos.mp (by omega), by omega⟩
  rw [hpart]
  calc ((Finset.Icc 1 r).biUnion fun b => U.powersetCard b).card
      ≤ ∑ b ∈ Finset.Icc 1 r, (U.powersetCard b).card := Finset.card_biUnion_le
    _ = ∑ b ∈ Finset.Icc 1 r, U.card.choose b := by
        refine Finset.sum_congr rfl fun b _ => Finset.card_powersetCard b U
    _ ≤ U.card ^ r := sum_choose_Icc_le_pow U.card r hr

/-! ### Moment method and Kim–Vu style concentration -/

private theorem list_sum_flatMap {α : Type*} (L : List α) (f : α → List ℝ) :
    (L.flatMap f).sum = (L.map fun a => (f a).sum).sum := by
  induction L with
  | nil => simp
  | cons a L' ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- For any fixed `U : Finset ι` with `|U| ≤ M`, expanding one extra factor of `evalPoly F` under
`marginalProd P` contributes at most `μ* + M^r · E*` (when `r ≥ 1`). -/
private theorem sum_overlap_marginalProd_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {r M : ℕ} (hr : 1 ≤ r)
    (hdeg : ∀ e ∈ F, e.card ≤ r) (U : Finset ι) (hU : U.card ≤ M) :
    (F.map fun e => ∏ i ∈ e \ U, marginalTrue P i).sum ≤
      muStar P F + (M : ℝ) ^ r * maxDerivExp P F := by
  let S : Finset (Finset ι) := U.powerset.filter fun B => B.Nonempty ∧ B.card ≤ r
  have hsplit :
      (F.map fun e => ∏ i ∈ e \ U, marginalTrue P i).sum ≤
        (F.map fun e => ∏ i ∈ e, marginalTrue P i).sum +
        ∑ B ∈ S, ((derivPoly F B).map fun d => ∏ i ∈ d, marginalTrue P i).sum := by
    induction F with
    | nil =>
      simp [derivPoly]
    | cons e F' ih =>
      have hdeg' : ∀ e' ∈ F', e'.card ≤ r := fun e' he' => hdeg e' (List.mem_cons_of_mem e he')
      have ih' := ih hdeg'
      have hedeg : e.card ≤ r := hdeg e (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons]
      have hB_nonneg : ∀ B : Finset ι,
          0 ≤ ((derivPoly (e :: F') B).map fun d => ∏ i ∈ d, marginalTrue P i).sum -
              ((derivPoly F' B).map fun d => ∏ i ∈ d, marginalTrue P i).sum := by
        intro B
        simp only [derivPoly, List.filter_cons]
        split_ifs
        · simp only [List.map_cons, List.sum_cons, add_sub_cancel_right]
          exact Finset.prod_nonneg fun i _ => probAllTrue_nonneg P {i}
        · simp
      by_cases hdisj : Disjoint e U
      · have hsdiff : e \ U = e := Finset.sdiff_eq_self_of_disjoint hdisj
        rw [hsdiff]
        have hsum_le :
            ∑ B ∈ S, ((derivPoly F' B).map fun d => ∏ i ∈ d, marginalTrue P i).sum ≤
              ∑ B ∈ S, ((derivPoly (e :: F') B).map fun d => ∏ i ∈ d, marginalTrue P i).sum := by
          refine Finset.sum_le_sum fun B _ => ?_
          linarith [hB_nonneg B]
        linarith
      · set B₀ : Finset ι := e ∩ U
        have hB₀_ne : B₀.Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdisj
        have hB₀_mem : B₀ ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.inter_subset_right, hB₀_ne,
            (Finset.card_le_card Finset.inter_subset_left).trans hedeg⟩
        have hB₀_sub : B₀ ⊆ e := Finset.inter_subset_left
        have hsdiff : e \ B₀ = e \ U := by
          ext i
          simp [B₀]
        have hB₀_diff :
            ((derivPoly (e :: F') B₀).map fun d => ∏ i ∈ d, marginalTrue P i).sum -
              ((derivPoly F' B₀).map fun d => ∏ i ∈ d, marginalTrue P i).sum =
              ∏ i ∈ e \ U, marginalTrue P i := by
          simp only [derivPoly, List.filter_cons, decide_eq_true_eq, hB₀_sub, ↓reduceIte,
            List.map_cons, List.sum_cons, add_sub_cancel_right, hsdiff]
        have hsum_diff :
            ∏ i ∈ e \ U, marginalTrue P i ≤
              ∑ B ∈ S, (((derivPoly (e :: F') B).map fun d => ∏ i ∈ d, marginalTrue P i).sum -
                ((derivPoly F' B).map fun d => ∏ i ∈ d, marginalTrue P i).sum) := by
          rw [← hB₀_diff]
          exact Finset.single_le_sum (fun B _ => hB_nonneg B) hB₀_mem
        rw [Finset.sum_sub_distrib] at hsum_diff
        have hprod_nonneg : 0 ≤ ∏ i ∈ e, marginalTrue P i :=
          Finset.prod_nonneg fun i _ => probAllTrue_nonneg P {i}
        linarith
  have hmu : (F.map fun e => ∏ i ∈ e, marginalTrue P i).sum = muStar P F := by
    rw [muStar, expectPoly_eq_sum_probAllTrue]
    congr 1
    exact List.map_congr_left fun e _ => (probAllTrue_marginalProd P e).symm
  have hderiv : ∀ B ∈ S,
      ((derivPoly F B).map fun d => ∏ i ∈ d, marginalTrue P i).sum ≤ maxDerivExp P F := by
    intro B hB
    have hBne : B.Nonempty := (Finset.mem_filter.mp hB).2.1
    have heq : ((derivPoly F B).map fun d => ∏ i ∈ d, marginalTrue P i).sum =
        expectPoly (marginalProd P) (derivPoly F B) := by
      rw [expectPoly_eq_sum_probAllTrue]
      congr 1
      exact List.map_congr_left fun d _ => (probAllTrue_marginalProd P d).symm
    rw [heq]
    exact expectPoly_derivPoly_le_maxDerivExp P F hBne
  have hScard : (S.card : ℝ) ≤ (M : ℝ) ^ r := by
    have h1 : S.card ≤ U.card ^ r := card_nonempty_subsets_le U hr
    have h2 : U.card ^ r ≤ M ^ r := Nat.pow_le_pow_left hU r
    exact_mod_cast h1.trans h2
  calc (F.map fun e => ∏ i ∈ e \ U, marginalTrue P i).sum
      ≤ (F.map fun e => ∏ i ∈ e, marginalTrue P i).sum +
          ∑ B ∈ S, ((derivPoly F B).map fun d => ∏ i ∈ d, marginalTrue P i).sum := hsplit
    _ ≤ muStar P F + ∑ _B ∈ S, maxDerivExp P F := by
        rw [hmu]
        linarith [Finset.sum_le_sum hderiv]
    _ = muStar P F + (S.card : ℝ) * maxDerivExp P F := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ muStar P F + (M : ℝ) ^ r * maxDerivExp P F := by
        linarith [mul_le_mul_of_nonneg_right hScard (maxDerivExp_nonneg P F)]

/-- Inductive expansion of `(evalPoly F x)^k` as a list of monomial supports of size `≤ k * r`. -/
private def powMonomials {ι : Type*} [DecidableEq ι] (F : List (Finset ι)) :
    ℕ → List (Finset ι)
  | 0 => [∅]
  | k + 1 => (powMonomials F k).flatMap fun U => F.map fun e => U ∪ e

private theorem evalPoly_union_sum {ι : Type*} [DecidableEq ι]
    (F : List (Finset ι)) (U : Finset ι) (x : ι → Bool) :
    (F.map fun e => if allTrue (U ∪ e) x then (1 : ℝ) else 0).sum =
      (if allTrue U x then (1 : ℝ) else 0) *
        (F.map fun e => if allTrue e x then (1 : ℝ) else 0).sum := by
  induction F with
  | nil => simp
  | cons e F' ihF =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [ihF]
    congr 1
    by_cases hU : allTrue U x <;> by_cases he : allTrue e x
    · have hUe : allTrue (U ∪ e) x := fun i hi => by
        rcases Finset.mem_union.mp hi with hiU | hie
        · exact hU i hiU
        · exact he i hie
      simp only [hU, he, hUe, ↓reduceIte, mul_one]
    · have hUe : ¬ allTrue (U ∪ e) x := fun h =>
        he fun i hi => h i (Finset.mem_union_right U hi)
      simp only [he, hUe, ↓reduceIte, mul_zero]
    · have hUe : ¬ allTrue (U ∪ e) x := fun h =>
        hU fun i hi => h i (Finset.mem_union_left e hi)
      simp only [hU, hUe, ↓reduceIte, zero_mul]
    · have hUe : ¬ allTrue (U ∪ e) x := fun h =>
        hU fun i hi => h i (Finset.mem_union_left e hi)
      simp only [hU, hUe, ↓reduceIte, zero_mul]

private theorem evalPoly_powMonomials {ι : Type*} [DecidableEq ι] (F : List (Finset ι))
    (k : ℕ) (x : ι → Bool) :
    evalPoly (powMonomials F k) x = (evalPoly F x) ^ k := by
  induction k with
  | zero => simp [powMonomials, evalPoly, allTrue]
  | succ k ih =>
    rw [pow_succ, ← ih]
    simp only [powMonomials, evalPoly, List.map_flatMap, list_sum_flatMap, List.map_map,
      Function.comp_def]
    have hmap : ∀ L : List (Finset ι),
        (L.map fun U => (F.map fun e => if allTrue (U ∪ e) x then (1 : ℝ) else 0).sum).sum =
          (L.map fun U => if allTrue U x then (1 : ℝ) else 0).sum *
            (F.map fun e => if allTrue e x then (1 : ℝ) else 0).sum := by
      intro L
      induction L with
      | nil => simp
      | cons U L' ihL =>
        simp only [List.map_cons, List.sum_cons, add_mul, ihL, evalPoly_union_sum F U x]
    exact hmap (powMonomials F k)

private theorem card_mem_powMonomials {ι : Type*} [DecidableEq ι] (F : List (Finset ι))
    {r : ℕ} (hdeg : ∀ e ∈ F, e.card ≤ r) (k : ℕ) :
    ∀ U ∈ powMonomials F k, U.card ≤ k * r := by
  induction k with
  | zero =>
    intro U hU
    simp only [powMonomials, List.mem_singleton] at hU
    subst hU
    simp
  | succ k ih =>
    intro W hW
    simp only [powMonomials, List.mem_flatMap, List.mem_map] at hW
    obtain ⟨U, hU, e, he, rfl⟩ := hW
    calc (U ∪ e).card ≤ U.card + e.card := Finset.card_union_le U e
      _ ≤ k * r + r := Nat.add_le_add (ih U hU) (hdeg e he)
      _ = (k + 1) * r := by ring

private theorem prod_union_sum_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) (U : Finset ι) :
    (F.map fun e => ∏ i ∈ U ∪ e, marginalTrue P i).sum =
      (∏ i ∈ U, marginalTrue P i) * (F.map fun e => ∏ i ∈ e \ U, marginalTrue P i).sum := by
  induction F with
  | nil => simp
  | cons e F' ihF =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [ihF]
    congr 1
    have hdisj : Disjoint U (e \ U) := Finset.disjoint_sdiff
    have hunion : U ∪ (e \ U) = U ∪ e := Finset.union_sdiff_self_eq_union
    rw [← hunion, Finset.prod_union hdisj]

/-- The `k`-th moment of `P` under the product marginal distribution satisfies
`E_{marginalProd P}[P(x)^k] ≤ (μ* + (r · m)^r E*)^k` for all `k ≤ m` (when `r ≥ 1`). -/
private theorem moment_marginalProd_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {r m : ℕ} (hr : 1 ≤ r)
    (hdeg : ∀ e ∈ F, e.card ≤ r) :
    ∀ k ≤ m,
      ((powMonomials F k).map fun U => ∏ i ∈ U, marginalTrue P i).sum ≤
        (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [powMonomials]
  | succ k ih =>
    intro hkm
    have hk_le : k ≤ m := Nat.le_of_succ_le hkm
    have hBaseNonneg : 0 ≤ muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F := by
      have h1 : 0 ≤ muStar P F := expectPoly_nonneg (marginalProd P) F
      have h2 : 0 ≤ maxDerivExp P F := maxDerivExp_nonneg P F
      positivity
    simp only [powMonomials, List.map_flatMap, list_sum_flatMap, List.map_map, Function.comp_def]
    have hterm : ∀ U ∈ powMonomials F k,
        (F.map fun e => ∏ i ∈ U ∪ e, marginalTrue P i).sum ≤
          (∏ i ∈ U, marginalTrue P i) *
            (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) := by
      intro U hU
      rw [prod_union_sum_marginal P F U]
      have hUcard : U.card ≤ r * m := by
        calc U.card ≤ k * r := card_mem_powMonomials F hdeg k U hU
          _ ≤ m * r := Nat.mul_le_mul_right r hk_le
          _ = r * m := mul_comm m r
      have hstep := sum_overlap_marginalProd_le P F hr hdeg U hUcard
      have hmul : ((r * m : ℕ) : ℝ) ^ r = (r : ℝ) ^ r * (m : ℝ) ^ r := by
        push_cast
        exact mul_pow (r : ℝ) (m : ℝ) r
      rw [hmul] at hstep
      exact mul_le_mul_of_nonneg_left hstep
        (Finset.prod_nonneg fun i _ => probAllTrue_nonneg P {i})
    have hsum_le : ∀ (L : List (Finset ι)),
        (∀ U ∈ L, (F.map fun e => ∏ i ∈ U ∪ e, marginalTrue P i).sum ≤
          (∏ i ∈ U, marginalTrue P i) *
            (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F)) →
        (L.map fun U => (F.map fun e => ∏ i ∈ U ∪ e, marginalTrue P i).sum).sum ≤
          (L.map fun U => ∏ i ∈ U, marginalTrue P i).sum *
            (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) := by
      intro L hL
      induction L with
      | nil => simp
      | cons U L' ihL =>
        simp only [List.map_cons, List.sum_cons, add_mul]
        exact add_le_add (hL U (List.mem_cons_self ..))
          (ihL fun U' hU' => hL U' (List.mem_cons_of_mem U hU'))
    calc ((powMonomials F k).map fun U => (F.map fun e => ∏ i ∈ U ∪ e, marginalTrue P i).sum).sum
        ≤ ((powMonomials F k).map fun U => ∏ i ∈ U, marginalTrue P i).sum *
            (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) := hsum_le _ hterm
      _ ≤ (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) ^ k *
            (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) :=
          mul_le_mul_of_nonneg_right (ih hk_le) hBaseNonneg
      _ = (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) ^ (k + 1) :=
          (pow_succ _ k).symm

/-- Moment bound for `(δ, r·m)`-almost independent distributions:
`E_{x ← P}[P(x)^m] ≤ ((1 + δ)^r · (μ* + r^r m^r E*))^m`. -/
theorem kimVu_moment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {δ : ℝ} {r m : ℕ}
    (hδ : 0 ≤ δ) (hP : IsAlmostIndependent P δ (r * m))
    (hdeg : ∀ e ∈ F, e.card ≤ r) :
    ∑ x : ι → Bool, (P x).toReal * (evalPoly F x) ^ m ≤
      ((1 + δ) ^ r * (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F)) ^ m := by
  by_cases hr0 : r = 0
  · subst hr0
    have hconst : ∀ x : ι → Bool, evalPoly F x = (F.length : ℝ) := by
      intro x
      induction F with
      | nil => simp [evalPoly]
      | cons e F' ih =>
        have he : e = ∅ := Finset.card_eq_zero.mp
          (Nat.eq_zero_of_le_zero (hdeg e (List.mem_cons_self ..)))
        subst he
        have ih' := ih (fun e' he' => hdeg e' (List.mem_cons_of_mem _ he'))
        have hempty : allTrue ∅ x := fun i hi => absurd hi (Finset.notMem_empty i)
        simp only [evalPoly, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
          Nat.cast_one, hempty, ↓reduceIte] at ih' ⊢
        linarith
    have hmu : muStar P F = (F.length : ℝ) := by
      simp only [muStar, expectPoly, hconst, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
    simp only [hconst, ← Finset.sum_mul, PMF.sum_toReal, one_mul, pow_zero, hmu]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _)
      (le_add_of_nonneg_right (by have := maxDerivExp_nonneg P F; positivity)) m
  have hr : 1 ≤ r := Nat.pos_of_ne_zero hr0
  have h1δ : 1 ≤ 1 + δ := by linarith
  have hexpand :
      ∑ x : ι → Bool, (P x).toReal * (evalPoly F x) ^ m =
        ((powMonomials F m).map fun U => probAllTrue P U).sum := by
    have h1 : ∀ x, (evalPoly F x) ^ m = evalPoly (powMonomials F m) x :=
      fun x => (evalPoly_powMonomials F m x).symm
    simp_rw [h1]
    exact expectPoly_eq_sum_probAllTrue P (powMonomials F m)
  rw [hexpand]
  have hterm : ∀ U ∈ powMonomials F m,
      probAllTrue P U ≤ (1 + δ) ^ (r * m) * ∏ i ∈ U, marginalTrue P i := by
    intro U hU
    have hUcard : U.card ≤ r * m := by
      rw [mul_comm]
      exact card_mem_powMonomials F hdeg m U hU
    calc probAllTrue P U
        ≤ (1 + δ) ^ U.card * ∏ i ∈ U, marginalTrue P i := hP.probAllTrue_le hδ hUcard
      _ ≤ (1 + δ) ^ (r * m) * ∏ i ∈ U, marginalTrue P i :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1δ hUcard)
            (Finset.prod_nonneg fun i _ => probAllTrue_nonneg P {i})
  have hsum_le : ∀ L : List (Finset ι),
      (∀ U ∈ L, probAllTrue P U ≤ (1 + δ) ^ (r * m) * ∏ i ∈ U, marginalTrue P i) →
      (L.map fun U => probAllTrue P U).sum ≤
        (1 + δ) ^ (r * m) * (L.map fun U => ∏ i ∈ U, marginalTrue P i).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons U L' ihL =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      exact add_le_add (hL U (List.mem_cons_self ..))
        (ihL fun U' hU' => hL U' (List.mem_cons_of_mem U hU'))
  calc ((powMonomials F m).map fun U => probAllTrue P U).sum
      ≤ (1 + δ) ^ (r * m) * ((powMonomials F m).map fun U => ∏ i ∈ U, marginalTrue P i).sum :=
        hsum_le _ hterm
    _ ≤ (1 + δ) ^ (r * m) *
          (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) ^ m :=
        mul_le_mul_of_nonneg_left (moment_marginalProd_le P F hr hdeg m le_rfl) (by positivity)
    _ = ((1 + δ) ^ r * (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F)) ^ m := by
        rw [mul_pow, pow_mul]

/-- Unnormalized Kim–Vu style concentration tail bound (valid even when `μ* = 0`):
for any threshold `t > 0`,
`Pr_{x ← P}[P(x) ≥ t] ≤ ((1 + δ)^r · (μ* + r^r m^r E*) / t)^m`. -/
theorem kimVu_concentration_unnormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {δ t : ℝ} {r m : ℕ}
    (hδ : 0 ≤ δ) (ht : 0 < t) (hP : IsAlmostIndependent P δ (r * m))
    (hdeg : ∀ e ∈ F, e.card ≤ r) :
    (∑ x : ι → Bool, if t ≤ evalPoly F x then (P x).toReal else 0) ≤
      ((1 + δ) ^ r * (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) / t) ^ m := by
  have hmarkov :
      t ^ m * (∑ x : ι → Bool, if t ≤ evalPoly F x then (P x).toReal else 0) ≤
        ∑ x : ι → Bool, (P x).toReal * (evalPoly F x) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with hx
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hx m) ENNReal.toReal_nonneg
    · rw [mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (evalPoly_nonneg F x) m)
  rw [div_pow, le_div_iff₀ (pow_pos ht m), mul_comm]
  exact hmarkov.trans (kimVu_moment_le P F hδ hP hdeg)

/-- Kim–Vu style concentration inequality for low-degree multilinear polynomials under
`(δ, r·m)`-almost independent binary distributions. -/
theorem kimVu_concentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PMF (ι → Bool)) (F : List (Finset ι)) {δ ε : ℝ} {r m : ℕ}
    (hδ : 0 ≤ δ) (hμ : 0 < muStar P F) (hε : 0 < 1 + ε)
    (hP : IsAlmostIndependent P δ (r * m)) (hdeg : ∀ e ∈ F, e.card ≤ r) :
    (∑ x : ι → Bool, if muStar P F * (1 + ε) ≤ evalPoly F x then (P x).toReal else 0) ≤
      ((1 + δ) ^ r * (1 + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F / muStar P F) /
        (1 + ε)) ^ m := by
  have ht : 0 < muStar P F * (1 + ε) := mul_pos hμ hε
  have hbound := kimVu_concentration_unnormalized P F hδ ht hP hdeg
  have hrew :
      (1 + δ) ^ r * (muStar P F + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F) /
          (muStar P F * (1 + ε)) =
        (1 + δ) ^ r * (1 + (r : ℝ) ^ r * (m : ℝ) ^ r * maxDerivExp P F / muStar P F) /
          (1 + ε) := by
    field_simp [hμ.ne', hε.ne']
  rwa [hrew] at hbound

/-! ### Permutation indicator `(1, M)`-almost independence -/

/-- The indicator matrix `F_{(x, y)} = decide (f x = y)` of a permutation `f : Equiv.Perm α`. -/
def permIndicator {α : Type*} [DecidableEq α] (f : Equiv.Perm α) : α × α → Bool :=
  fun p => decide (f p.1 = p.2)

/-- Evaluation of `permIndicator`. -/
@[simp] theorem permIndicator_apply {α : Type*} [DecidableEq α] (f : Equiv.Perm α) (p : α × α) :
    permIndicator f p = decide (f p.1 = p.2) := by rfl

/-- The distribution on `(α × α) → Bool` induced by a uniform random permutation of `α`. -/
noncomputable def permIndicatorPMF (α : Type*) [Fintype α] [DecidableEq α] :
    PMF (α × α → Bool) :=
  (PMF.uniformOfFintype (Equiv.Perm α)).map permIndicator

/-- Probability of any event `E` under `permIndicatorPMF α` equals the fraction of permutations
whose indicator matrix satisfies `E`. -/
theorem sum_ite_permIndicatorPMF_toReal {α : Type*} [Fintype α] [DecidableEq α]
    (E : (α × α → Bool) → Prop) [DecidablePred E] :
    (∑ x : α × α → Bool, if E x then (permIndicatorPMF α x).toReal else 0) =
      ((Finset.univ.filter fun f : Equiv.Perm α => E (permIndicator f)).card : ℝ) /
        (Fintype.card (Equiv.Perm α) : ℝ) := by
  classical
  have hmap : ∀ (s : α × α → Bool),
      (permIndicatorPMF α s).toReal =
        ∑ f : Equiv.Perm α, if permIndicator f = s then
          ((PMF.uniformOfFintype (Equiv.Perm α)) f).toReal else 0 := by
    intro s
    simp only [permIndicatorPMF]
    rw [PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum (fun f _ => by split_ifs <;> simp)]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases h : s = permIndicator f
    · subst h; simp
    · have h' : permIndicator f ≠ s := Ne.symm h
      simp [h, h']
  simp_rw [hmap]
  calc ∑ x : α × α → Bool, (if E x then
          ∑ f : Equiv.Perm α, if permIndicator f = x then
            ((PMF.uniformOfFintype (Equiv.Perm α)) f).toReal else 0
          else 0)
      = ∑ x : α × α → Bool, ∑ f : Equiv.Perm α,
          if E x ∧ permIndicator f = x then
            ((PMF.uniformOfFintype (Equiv.Perm α)) f).toReal else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : E x
        · simp only [hx, ↓reduceIte, true_and]
        · simp only [hx, ↓reduceIte, false_and, Finset.sum_const_zero]
    _ = ∑ f : Equiv.Perm α, ∑ x : α × α → Bool,
          if E x ∧ permIndicator f = x then
            ((PMF.uniformOfFintype (Equiv.Perm α)) f).toReal else 0 := Finset.sum_comm
    _ = ∑ f : Equiv.Perm α,
          if E (permIndicator f) then ((PMF.uniformOfFintype (Equiv.Perm α)) f).toReal else 0 := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.sum_eq_single (permIndicator f)]
        · simp only [and_true]
        · intro x _ hne
          have : permIndicator f ≠ x := Ne.symm hne
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = ((Finset.univ.filter fun f : Equiv.Perm α => E (permIndicator f)).card : ℝ) /
          (Fintype.card (Equiv.Perm α) : ℝ) := by
        have hunif : ∀ f : Equiv.Perm α,
            ((PMF.uniformOfFintype (Equiv.Perm α)) f).toReal =
              1 / (Fintype.card (Equiv.Perm α) : ℝ) := by
          intro f
          rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
        simp_rw [hunif]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_one_div]

/-- Number of permutations of `α` matching a partial bijection `M : Finset (α × α)` equals
`(card α - M.card)!` when `M` is functional on both coordinates. -/
theorem card_perm_matching {α : Type*} [Fintype α] [DecidableEq α] (M : Finset (α × α))
    (hfun : ∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p.2 = q.2)
    (hinj : ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p.1 = q.1) :
    (Finset.univ.filter fun f : Equiv.Perm α => ∀ p ∈ M, f p.1 = p.2).card =
      (Fintype.card α - M.card).factorial := by
  classical
  let dom : Finset α := M.image Prod.fst
  let cod : Finset α := M.image Prod.snd
  have hdom_card : dom.card = M.card :=
    Finset.card_image_of_injOn fun p hp q hq heq => Prod.ext heq (hfun p hp q hq heq)
  have hcod_card : cod.card = M.card :=
    Finset.card_image_of_injOn fun p hp q hq heq => Prod.ext (hinj p hp q hq heq) heq
  have hcompl_card : Fintype.card {x : α // x ∉ dom} = Fintype.card α - M.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hdom_card]
  have hcompl_cod_card : Fintype.card {y : α // y ∉ cod} = Fintype.card α - M.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hcod_card]
  let eCompl : {x : α // x ∉ dom} ≃ {y : α // y ∉ cod} :=
    Fintype.equivOfCardEq (hcompl_card.trans hcompl_cod_card.symm)
  have hmatch_iff : ∀ f : Equiv.Perm α, (∀ p ∈ M, f p.1 = p.2) →
      ∀ x : α, x ∉ dom ↔ f x ∉ cod := by
    intro f hf x
    constructor
    · intro hx hfx
      obtain ⟨p, hp, hpf⟩ := Finset.mem_image.mp hfx
      have hxeq : x = p.1 := f.injective (by rw [hf p hp, hpf])
      exact hx (Finset.mem_image.mpr ⟨p, hp, hxeq.symm⟩)
    · intro hfx hx
      obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
      apply hfx
      exact Finset.mem_image.mpr ⟨p, hp, by rw [← hpx, hf p hp]⟩
  have hcard_eq :
      (Finset.univ.filter fun f : Equiv.Perm α => ∀ p ∈ M, f p.1 = p.2).card =
        Fintype.card (Equiv.Perm {x : α // x ∉ dom}) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij
      (fun f hf =>
        let hfm : ∀ p ∈ M, f p.1 = p.2 := (Finset.mem_filter.mp hf).2
        { toFun := fun x => eCompl.symm ⟨f x.1, (hmatch_iff f hfm x.1).mp x.2⟩
          invFun := fun x => ⟨f.symm (eCompl x).1, by
            rw [hmatch_iff f hfm, Equiv.apply_symm_apply]
            exact (eCompl x).2⟩
          left_inv := fun x => by ext; simp
          right_inv := fun x => by ext; simp })
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro f₁ hf₁ f₂ hf₂ heq
      have hm₁ := (Finset.mem_filter.mp hf₁).2
      have hm₂ := (Finset.mem_filter.mp hf₂).2
      ext x
      by_cases hx : x ∈ dom
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        rw [hm₁ p hp, hm₂ p hp]
      · have hval := congrArg
          (fun σ : Equiv.Perm {x : α // x ∉ dom} => (eCompl (σ ⟨x, hx⟩)).1) heq
        simpa using hval
    · intro σ _
      let toDom : {x : α // x ∈ dom} → α := fun x =>
        (Classical.choose (Finset.mem_image.mp x.2)).2
      let invCod : {y : α // y ∈ cod} → α := fun y =>
        (Classical.choose (Finset.mem_image.mp y.2)).1
      have htoDom_spec : ∀ (x : {x : α // x ∈ dom}), (x.1, toDom x) ∈ M := by
        intro x
        have hch := Classical.choose_spec (Finset.mem_image.mp x.2)
        have : (x.1, toDom x) = Classical.choose (Finset.mem_image.mp x.2) :=
          Prod.ext hch.2.symm rfl
        rw [this]
        exact hch.1
      have hinvCod_spec : ∀ (y : {y : α // y ∈ cod}), (invCod y, y.1) ∈ M := by
        intro y
        have hch := Classical.choose_spec (Finset.mem_image.mp y.2)
        have : (invCod y, y.1) = Classical.choose (Finset.mem_image.mp y.2) :=
          Prod.ext rfl hch.2.symm
        rw [this]
        exact hch.1
      let f : Equiv.Perm α :=
        { toFun := fun x => if hx : x ∈ dom then toDom ⟨x, hx⟩ else (eCompl (σ ⟨x, hx⟩)).1
          invFun := fun y =>
            if hy : y ∈ cod then invCod ⟨y, hy⟩ else (σ.symm (eCompl.symm ⟨y, hy⟩)).1
          left_inv := fun x => by
            by_cases hx : x ∈ dom
            · have hy : toDom ⟨x, hx⟩ ∈ cod :=
                Finset.mem_image.mpr ⟨(x, toDom ⟨x, hx⟩), htoDom_spec ⟨x, hx⟩, rfl⟩
              simp only [hx, ↓reduceDIte, hy]
              exact hinj _ (hinvCod_spec ⟨toDom ⟨x, hx⟩, hy⟩) _ (htoDom_spec ⟨x, hx⟩) rfl
            · have hy : (eCompl (σ ⟨x, hx⟩)).1 ∉ cod := (eCompl (σ ⟨x, hx⟩)).2
              simp [hx, hy]
          right_inv := fun y => by
            by_cases hy : y ∈ cod
            · have hx : invCod ⟨y, hy⟩ ∈ dom :=
                Finset.mem_image.mpr ⟨(invCod ⟨y, hy⟩, y), hinvCod_spec ⟨y, hy⟩, rfl⟩
              simp only [hy, ↓reduceDIte, hx]
              exact hfun _ (htoDom_spec ⟨invCod ⟨y, hy⟩, hx⟩) _ (hinvCod_spec ⟨y, hy⟩) rfl
            · have hx : (σ.symm (eCompl.symm ⟨y, hy⟩)).1 ∉ dom :=
                (σ.symm (eCompl.symm ⟨y, hy⟩)).2
              simp [hy, hx] }
      have hfm : ∀ p ∈ M, f p.1 = p.2 := by
        intro p hp
        have hx : p.1 ∈ dom := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        simp only [f, Equiv.coe_fn_mk, hx, ↓reduceDIte]
        exact hfun _ (htoDom_spec ⟨p.1, hx⟩) p hp rfl
      refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfm⟩, ?_⟩
      ext ⟨x, hx⟩
      simp [f, hx]
  rw [hcard_eq, Fintype.card_perm, hcompl_card]

/-- `probAllTrue (permIndicatorPMF α) M` equals the fraction of permutations matching `M`. -/
theorem probAllTrue_permIndicatorPMF {α : Type*} [Fintype α] [DecidableEq α]
    (M : Finset (α × α)) :
    probAllTrue (permIndicatorPMF α) M =
      ((Finset.univ.filter fun f : Equiv.Perm α => ∀ p ∈ M, f p.1 = p.2).card : ℝ) /
        ((Fintype.card α).factorial : ℝ) := by
  classical
  rw [probAllTrue, sum_ite_permIndicatorPMF_toReal (allTrue M)]
  have hcard : (Fintype.card (Equiv.Perm α) : ℝ) = ((Fintype.card α).factorial : ℝ) := by
    exact_mod_cast Fintype.card_perm
  rw [hcard]
  congr 1
  congr 1
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, allTrue, permIndicator,
    decide_eq_true_eq]

/-- Marginal probability of each indicator `F_{(x, y)}` under a uniform random permutation is
`1 / |α|`. -/
theorem marginalTrue_permIndicatorPMF {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α × α) :
    marginalTrue (permIndicatorPMF α) p = 1 / (Fintype.card α : ℝ) := by
  rw [marginalTrue, probAllTrue_permIndicatorPMF]
  rw [card_perm_matching {p} (by simp) (by simp)]
  simp only [Finset.card_singleton]
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  have hfac : (Fintype.card α).factorial = Fintype.card α * (Fintype.card α - 1).factorial := by
    cases h : Fintype.card α with
    | zero => omega
    | succ k => simp [Nat.factorial_succ]
  rw [hfac, Nat.cast_mul]
  have h1 : ((Fintype.card α - 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  field_simp [h1, h2]

/-- The indicator variables `F_{(x, y)} = 1[f(x) = y]` of a uniform random permutation `f` on `α`
are `(1, M)`-almost independent whenever `2 * (M - 1) ≤ Fintype.card α`. -/
theorem permIndicator_isAlmostIndependent {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {M : ℕ} (hM : 2 * (M - 1) ≤ Fintype.card α) :
    IsAlmostIndependent (permIndicatorPMF α) 1 M := by
  intro S hS q hq
  rw [marginalTrue_permIndicatorPMF, probAllTrue_permIndicatorPMF, probAllTrue_permIndicatorPMF]
  have hNpos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hfacpos : (0 : ℝ) < ((Fintype.card α).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  by_cases hvalid : (∀ p ∈ insert q S, ∀ p' ∈ insert q S, p.1 = p'.1 → p.2 = p'.2) ∧
      (∀ p ∈ insert q S, ∀ p' ∈ insert q S, p.2 = p'.2 → p.1 = p'.1)
  · obtain ⟨hfun, hinj⟩ := hvalid
    have hfunS : ∀ p ∈ S, ∀ p' ∈ S, p.1 = p'.1 → p.2 = p'.2 :=
      fun p hp p' hp' => hfun p (Finset.mem_insert_of_mem hp) p' (Finset.mem_insert_of_mem hp')
    have hinjS : ∀ p ∈ S, ∀ p' ∈ S, p.2 = p'.2 → p.1 = p'.1 :=
      fun p hp p' hp' => hinj p (Finset.mem_insert_of_mem hp) p' (Finset.mem_insert_of_mem hp')
    rw [card_perm_matching (insert q S) hfun hinj, card_perm_matching S hfunS hinjS,
      Finset.card_insert_of_notMem hq]
    have hSbound : 2 * S.card ≤ Fintype.card α := by omega
    have hSlt : S.card < Fintype.card α := by
      have := Fintype.card_pos (α := α)
      omega
    have hfac_step : (Fintype.card α - S.card).factorial =
        (Fintype.card α - S.card) * (Fintype.card α - (S.card + 1)).factorial := by
      have hsub : Fintype.card α - S.card = (Fintype.card α - (S.card + 1)) + 1 := by omega
      rw [hsub, Nat.factorial_succ]
    rw [hfac_step, Nat.cast_mul]
    have h2le : (Fintype.card α : ℝ) ≤ 2 * ((Fintype.card α - S.card : ℕ) : ℝ) := by
      have : Fintype.card α ≤ 2 * (Fintype.card α - S.card) := by omega
      exact_mod_cast this
    have hnum_nonneg : 0 ≤ ((Fintype.card α - (S.card + 1)).factorial : ℝ) := by positivity
    rw [show (1 + 1 : ℝ) = 2 by norm_num, div_le_iff₀ hfacpos]
    calc ((Fintype.card α - (S.card + 1)).factorial : ℝ)
        ≤ ((Fintype.card α - (S.card + 1)).factorial : ℝ) *
            (2 * ((Fintype.card α - S.card : ℕ) : ℝ) / (Fintype.card α : ℝ)) := by
          have hone : 1 ≤ 2 * ((Fintype.card α - S.card : ℕ) : ℝ) / (Fintype.card α : ℝ) :=
            (one_le_div hNpos).mpr h2le
          nlinarith
      _ = 1 / (Fintype.card α : ℝ) * 2 *
            (((Fintype.card α - S.card : ℕ) : ℝ) *
              ((Fintype.card α - (S.card + 1)).factorial : ℝ) /
                ((Fintype.card α).factorial : ℝ)) *
            ((Fintype.card α).factorial : ℝ) := by
          field_simp [hNpos.ne', hfacpos.ne']
  · have hempty :
        (Finset.univ.filter fun f : Equiv.Perm α => ∀ p ∈ insert q S, f p.1 = p.2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro f _ hf
      apply hvalid
      exact ⟨fun p hp p' hp' h1 => by rw [← hf p hp, ← hf p' hp', h1],
             fun p hp p' hp' h2 => f.injective (by rw [hf p hp, hf p' hp', h2])⟩
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

end CslibFrontier.Probability.Concentration

end
