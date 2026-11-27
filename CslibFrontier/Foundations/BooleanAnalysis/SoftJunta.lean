/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
public import CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta
public import CslibFrontier.Probability.Product
public import Mathlib.Logic.Function.DependsOn

import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Soft Junta Complexity and Anisotropic Boolean Noise

This module develops the anisotropic product-Bernoulli noise operator on the Boolean cube,
correlated error and correlated variance of a Boolean function, hard junta complexity, and soft
junta complexity.

For a coordinate correlation vector `α : ι → ℝ` with `α i ∈ [-1, 1]`, the anisotropic noise
operator `noiseOpVec α f x` averages `f (x + P)` over a mask `P` whose coordinates are
independently `true` with probability `(1 - α i) / 2`. Its Fourier coefficients are
`fourierCoeff (noiseOpVec α f) S = (∏ i ∈ S, α i) * fourierCoeff f S`.

The `α`-correlated error of a Boolean function `g` is the minimum error of a predictor `h(x)`
attempting to predict `g(y)` when `(x, y)` is `α`-correlated, and the `α`-correlated variance is
`1 - 𝔼_x (noiseOpVec α (signVal ∘ g) x) ^ 2`. These satisfy the pointwise sandwich
`2 * corrError g α ≤ corrVar g α ≤ 4 * corrError g α`, and `corrVar g α` depends only on the
coordinatewise squares `α i ^ 2`, giving the randomized rounding inequality between hard junta
complexity `J(g, δ)` and soft junta complexity `J̃(g, δ)`:
`(1 / 2) * J(g, 4 * δ) ≤ J̃(g, δ) ≤ J(g, δ)`.

## Main definitions

* `Cslib.BitString.bernoulliWeightVec`, `Cslib.BitString.bernoulliAverageVec`: anisotropic
  product-Bernoulli weights and expectations on `ι → Bool`.
* `Cslib.BitString.noiseOpVec`: the anisotropic Boolean noise operator `T_α`.
* `Cslib.BitString.corrPairError`, `Cslib.BitString.corrError`, `Cslib.BitString.corrVar`:
  `α`-correlated error and `α`-correlated variance.
* `Cslib.BitString.juntaComplexity`, `Cslib.BitString.softJuntaComplexity`: hard and soft
  `δ`-approximate junta complexity of a Boolean function.

## Main results

* `Cslib.BitString.fourierCoeff_noiseOpVec`, `Cslib.BitString.noiseOpVec_eq_sum`: Fourier
  expansion of the anisotropic noise operator.
* `Cslib.BitString.two_mul_corrError_le_corrVar`,
  `Cslib.BitString.corrVar_le_four_mul_corrError`: sandwich between correlated error and
  correlated variance.
* `Cslib.BitString.sum_pi_corrVar_eq`: product-distribution expectation invariance of correlated
  variance.
* `Cslib.BitString.bernoulliAverageVec_corrError_le_two_mul`: randomized junta rounding doubles
  the correlated error in expectation.
* `Cslib.BitString.half_juntaComplexity_four_mul_le_softJuntaComplexity`,
  `Cslib.BitString.softJuntaComplexity_le_juntaComplexity`: the two-sided comparison
  `(1 / 2) * J(g, 4 * δ) ≤ J̃(g, δ) ≤ J(g, δ)`.
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Anisotropic product-Bernoulli averages -/

omit [DecidableEq ι] in
/-- The probability weight of a Boolean mask `selected : ι → Bool` when coordinate `i` is selected
independently with probability `p i`. -/
@[expose] def bernoulliWeightVec (p : ι → ℝ) (selected : ι → Bool) : ℝ :=
  ∏ i, if selected i then p i else 1 - p i

omit [DecidableEq ι] in
/-- Product formula for `bernoulliWeightVec`. -/
theorem bernoulliWeightVec_eq_prod (p : ι → ℝ) (selected : ι → Bool) :
    bernoulliWeightVec p selected = ∏ i, if selected i then p i else 1 - p i := rfl

/-- Expectation of `f` over an anisotropic product-Bernoulli mask with coordinate rates `p`. -/
@[expose] def bernoulliAverageVec (p : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ selected, bernoulliWeightVec p selected * f selected

/-- Sum formula for `bernoulliAverageVec`. -/
theorem bernoulliAverageVec_eq_sum (p : ι → ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverageVec p f = ∑ selected, bernoulliWeightVec p selected * f selected := rfl

/-- Coordinatewise product factorization for anisotropic product-Bernoulli averages. -/
theorem bernoulliAverageVec_prod (p : ι → ℝ) (g : ι → Bool → ℝ) :
    bernoulliAverageVec p (fun x => ∏ i, g i (x i)) =
      ∏ i, ((1 - p i) * g i false + p i * g i true) := by
  unfold bernoulliAverageVec bernoulliWeightVec
  have hterm (x : ι → Bool) :
    (∏ i, if x i then p i else 1 - p i) * (∏ i, g i (x i)) =
      ∏ i, (if x i then p i else 1 - p i) * g i (x i) :=
    (Finset.prod_mul_distrib).symm
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i b => (if b then p i else 1 - p i) * g i b)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, add_comm]

/-- The anisotropic product-Bernoulli weights sum to `1`. -/
@[simp]
theorem sum_bernoulliWeightVec (p : ι → ℝ) :
    ∑ selected : ι → Bool, bernoulliWeightVec p selected = 1 := by
  have h := bernoulliAverageVec_prod p (fun _ _ => (1 : ℝ))
  simpa [bernoulliAverageVec] using h

/-- Anisotropic product-Bernoulli expectation of a constant equals that constant. -/
@[simp]
theorem bernoulliAverageVec_const (p : ι → ℝ) (c : ℝ) :
    bernoulliAverageVec p (fun _ => c) = c := by
  unfold bernoulliAverageVec
  rw [← Finset.sum_mul, sum_bernoulliWeightVec, one_mul]

/-- Anisotropic product-Bernoulli expectation is linear in additions. -/
theorem bernoulliAverageVec_add (p : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    bernoulliAverageVec p (fun x => f x + g x) =
      bernoulliAverageVec p f + bernoulliAverageVec p g := by
  simp only [bernoulliAverageVec, mul_add, Finset.sum_add_distrib]

/-- Anisotropic product-Bernoulli expectation commutes with scalar multiplication. -/
theorem bernoulliAverageVec_const_mul (p : ι → ℝ) (c : ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverageVec p (fun x => c * f x) = c * bernoulliAverageVec p f := by
  simp only [bernoulliAverageVec, mul_left_comm, ← Finset.mul_sum]

omit [DecidableEq ι] in
/-- Anisotropic product-Bernoulli weights are nonnegative when all rates lie in `[0, 1]`. -/
theorem bernoulliWeightVec_nonneg {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (selected : ι → Bool) :
    0 ≤ bernoulliWeightVec p selected := by
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact (hp i).1
  · linarith [(hp i).2]

/-- Anisotropic product-Bernoulli expectation preserves nonnegativity for rates in `[0, 1]`. -/
theorem bernoulliAverageVec_nonneg {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ bernoulliAverageVec p f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (bernoulliWeightVec_nonneg hp x) (hf x)

/-- Monotonicity of anisotropic product-Bernoulli expectation for rates in `[0, 1]`. -/
theorem bernoulliAverageVec_mono {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    {f g : (ι → Bool) → ℝ} (hfg : ∀ x, f x ≤ g x) :
    bernoulliAverageVec p f ≤ bernoulliAverageVec p g :=
  Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (hfg x) (bernoulliWeightVec_nonneg hp x)

/-- The expectation of a Fourier character `chi ℝ S` under an anisotropic mask with rates `p` is
`∏ i ∈ S, (1 - 2 * p i)`. -/
theorem bernoulliAverageVec_chi (p : ι → ℝ) (S : Finset ι) :
    bernoulliAverageVec p (chi ℝ S) = ∏ i ∈ S, (1 - 2 * p i) := by
  rw [funext (chi_eq_prod_univ S),
    bernoulliAverageVec_prod p fun i b => if i ∈ S then (-1) ^ b.toNat else 1,
    ← Fintype.prod_ite_mem S]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one]
    ring
  · ring

/-- Expected Hamming weight of an anisotropic product-Bernoulli mask equals `∑ i, p i`. -/
theorem bernoulliAverageVec_card_filter (p : ι → ℝ) :
    bernoulliAverageVec p (fun P => (#{i | P i = true} : ℝ)) = ∑ i, p i := by
  have hcard (P : ι → Bool) :
      (#{i | P i = true} : ℝ) = ∑ i, if P i = true then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  simp_rw [hcard, bernoulliAverageVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoord :
      (∑ P : ι → Bool, bernoulliWeightVec p P * (if P i = true then (1 : ℝ) else 0)) =
        bernoulliAverageVec p (fun P => ∏ j, if j = i then (if P j then 1 else 0) else 1) := by
    refine Finset.sum_congr rfl fun P _ => ?_
    dsimp only
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => if P j then (1 : ℝ) else 0)]
    simp
  rw [hcoord, bernoulliAverageVec_prod p (fun j b => if j = i then (if b then 1 else 0) else 1)]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ### Anisotropic noise operator -/

/-- The **anisotropic noise operator** `T_α`: averages `f (x + P)` over a mask `P` flipping each
coordinate `i` independently with probability `(1 - α i) / 2`. -/
@[expose] noncomputable def noiseOpVec (α : ι → ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  bernoulliAverageVec (fun i => (1 - α i) / 2) (fun P => f (x + P))

/-- Anisotropic noise scales each Fourier character `chi ℝ S` by `∏ i ∈ S, α i`. -/
@[simp]
theorem noiseOpVec_chi (α : ι → ℝ) (S : Finset ι) (x : ι → Bool) :
    noiseOpVec α (chi ℝ S) x = (∏ i ∈ S, α i) * chi ℝ S x := by
  unfold noiseOpVec
  simp_rw [chi_add]
  rw [bernoulliAverageVec_const_mul, bernoulliAverageVec_chi, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-- **Fourier expansion of the anisotropic noise operator**:
`T_α f x = ∑_S f̂(S) (∏_{i ∈ S} α_i) χ_S(x)`. -/
theorem noiseOpVec_eq_sum (α : ι → ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOpVec α f x = ∑ S : Finset ι, fourierCoeff f S * (∏ i ∈ S, α i) * chi ℝ S x := by
  conv_lhs =>
    unfold noiseOpVec
    arg 2
    ext P
    rw [← sum_fourierCoeff_mul_chi f (x + P)]
  simp only [bernoulliAverageVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS :
      (∑ P : ι → Bool, bernoulliWeightVec (fun i => (1 - α i) / 2) P *
        (fourierCoeff f S * chi ℝ S (x + P))) =
      fourierCoeff f S * noiseOpVec α (chi ℝ S) x := by
    unfold noiseOpVec bernoulliAverageVec
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => by ring
  rw [hS, noiseOpVec_chi]
  ring

/-- **Fourier coefficients of the anisotropic noise operator**:
`(T_α f)^(S) = (∏_{i ∈ S} α_i) f̂(S)`. -/
@[simp]
theorem fourierCoeff_noiseOpVec (α : ι → ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (noiseOpVec α f) S = (∏ i ∈ S, α i) * fourierCoeff f S := by
  have hfun : noiseOpVec α f = fun x => ∑ T : Finset ι, (fourierCoeff f T * ∏ i ∈ T, α i) *
      chi ℝ T x :=
    funext fun x => noiseOpVec_eq_sum α f x
  rw [hfun, fourierCoeff_sum_mul_chi]
  ring

/-- Second moment of the anisotropic noise operator:
`𝔼_x (T_α f x)² = ∑_S f̂(S)² ∏_{i ∈ S} α_i²`. -/
theorem expect_noiseOpVec_sq (α : ι → ℝ) (f : (ι → Bool) → ℝ) :
    (𝔼 x : ι → Bool, noiseOpVec α f x ^ 2) =
      ∑ S : Finset ι, fourierCoeff f S ^ 2 * ∏ i ∈ S, α i ^ 2 := by
  simp_rw [sq, expect_mul_eq_sum_fourierCoeff_mul, fourierCoeff_noiseOpVec]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- For `α ∈ [-1, 1]^ι` and a Boolean function `g`, `|T_α (signVal ∘ g) x| ≤ 1`. -/
theorem abs_noiseOpVec_signVal_le_one {α : ι → ℝ} (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1)
    (g : (ι → Bool) → Bool) (x : ι → Bool) :
    |noiseOpVec α (fun y => signVal (g y)) x| ≤ 1 := by
  have hp : ∀ i, (1 - α i) / 2 ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨by linarith [(hα i).2], by linarith [(hα i).1]⟩
  unfold noiseOpVec bernoulliAverageVec
  calc |∑ P : ι → Bool, bernoulliWeightVec (fun i => (1 - α i) / 2) P * signVal (g (x + P))|
      ≤ ∑ P : ι → Bool, |bernoulliWeightVec (fun i => (1 - α i) / 2) P * signVal (g (x + P))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ P : ι → Bool, bernoulliWeightVec (fun i => (1 - α i) / 2) P := by
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [abs_mul, abs_signVal, mul_one, abs_of_nonneg (bernoulliWeightVec_nonneg hp P)]
    _ = 1 := sum_bernoulliWeightVec _

/-- Anisotropic noise with indicator vector `1_J` is the conditional expectation fixing `J`. -/
theorem noiseOpVec_indicator_eq_expect_piecewise (f : (ι → Bool) → ℝ) (J : Finset ι)
    (x : ι → Bool) :
    noiseOpVec (fun i => if i ∈ J then (1 : ℝ) else 0) f x =
      𝔼 z : ι → Bool, f (J.piecewise x z) := by
  have heq : noiseOpVec (fun i => if i ∈ J then (1 : ℝ) else 0) f =
      fun x => 𝔼 z : ι → Bool, f (J.piecewise x z) := by
    apply fourierCoeff_injective
    ext S
    rw [fourierCoeff_noiseOpVec, fourierCoeff_expect_piecewise]
    have hprod : (∏ i ∈ S, if i ∈ J then (1 : ℝ) else 0) = if S ⊆ J then 1 else 0 := by
      by_cases hSJ : S ⊆ J
      · simp only [hSJ, ↓reduceIte]
        exact Finset.prod_eq_one fun i hi => by simp only [hSJ hi, ↓reduceIte]
      · simp only [hSJ, ↓reduceIte]
        obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hSJ
        exact Finset.prod_eq_zero hiS (by simp only [hiJ, ↓reduceIte])
    rw [hprod]
    split_ifs <;> ring
  exact congrFun heq x

/-! ### Correlated error and correlated variance -/

/-- The probability `Pr_{(x, y) ~ D(α)}[g(y) ≠ h(x)]` that a predictor `h` errs on `g` under the
`α`-correlated pair distribution. -/
@[expose] noncomputable def corrPairError (g h : (ι → Bool) → Bool) (α : ι → ℝ) : ℝ :=
  𝔼 x : ι → Bool,
    bernoulliAverageVec (fun i => (1 - α i) / 2) (fun P => if g (x + P) = h x then 0 else 1)

/-- Expectation formula for `corrPairError` in terms of `bernoulliAverageVec`. -/
theorem corrPairError_eq_expect_bernoulliAverageVec (g h : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrPairError g h α =
      𝔼 x : ι → Bool,
        bernoulliAverageVec (fun i => (1 - α i) / 2) (fun P => if g (x + P) = h x then 0 else 1) :=
  rfl

/-- The **`α`-correlated error** of a Boolean function `g`:
`𝔼_x [(1 - |T_α (signVal ∘ g) x|) / 2]`. -/
@[expose] noncomputable def corrError (g : (ι → Bool) → Bool) (α : ι → ℝ) : ℝ :=
  𝔼 x : ι → Bool, (1 - |noiseOpVec α (fun y => signVal (g y)) x|) / 2

/-- Expectation formula for `corrError`. -/
theorem corrError_eq_expect (g : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrError g α = 𝔼 x : ι → Bool, (1 - |noiseOpVec α (fun y => signVal (g y)) x|) / 2 := rfl

/-- The **`α`-correlated variance** of a Boolean function `g`:
`1 - 𝔼_x (T_α (signVal ∘ g) x)²`. -/
@[expose] noncomputable def corrVar (g : (ι → Bool) → Bool) (α : ι → ℝ) : ℝ :=
  1 - 𝔼 x : ι → Bool, noiseOpVec α (fun y => signVal (g y)) x ^ 2

/-- Expectation formula for `corrVar`. -/
theorem corrVar_eq_one_sub (g : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrVar g α = 1 - 𝔼 x : ι → Bool, noiseOpVec α (fun y => signVal (g y)) x ^ 2 := rfl

/-- Exact formula for `corrPairError` in terms of the anisotropic noise operator. -/
theorem corrPairError_eq_expect (g h : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrPairError g h α =
      𝔼 x : ι → Bool, (1 - signVal (h x) * noiseOpVec α (fun y => signVal (g y)) x) / 2 := by
  unfold corrPairError
  refine Finset.expect_congr rfl fun x _ => ?_
  have hpt (P : ι → Bool) :
      (if g (x + P) = h x then (0 : ℝ) else 1) =
        (1 - signVal (h x) * signVal (g (x + P))) / 2 := by
    cases g (x + P) <;> cases h x <;> norm_num [signVal]
  simp_rw [hpt, sub_div, bernoulliAverageVec]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_bernoulliWeightVec, one_mul]
  congr 1
  unfold noiseOpVec bernoulliAverageVec
  simp_rw [sub_div]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun P _ => ?_
  ring

/-- `corrError g α` is a lower bound on `corrPairError g h α` for every predictor `h`. -/
theorem corrError_le_corrPairError (g h : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrError g α ≤ corrPairError g h α := by
  rw [corrPairError_eq_expect]
  unfold corrError
  refine Finset.expect_le_expect fun x _ => ?_
  have hle : signVal (h x) * noiseOpVec α (fun y => signVal (g y)) x ≤
      |noiseOpVec α (fun y => signVal (g y)) x| :=
    signVal_mul_le_abs _ _
  linarith

/-- The Bayes-optimal predictor `h x = decide (T_α (signVal ∘ g) x < 0)` achieves `corrError`. -/
theorem corrPairError_bayes_eq_corrError (g : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrPairError g (fun x => decide (noiseOpVec α (fun y => signVal (g y)) x < 0)) α =
      corrError g α := by
  rw [corrPairError_eq_expect]
  unfold corrError
  refine Finset.expect_congr rfl fun x _ => ?_
  set t := noiseOpVec α (fun y => signVal (g y)) x
  by_cases ht : t < 0
  · simp [ht, signVal, abs_of_neg ht]
  · simp [ht, signVal, abs_of_nonneg (not_lt.mp ht)]

/-- `corrError g α` is nonnegative when `α ∈ [-1, 1]^ι`. -/
theorem corrError_nonneg {α : ι → ℝ} (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1)
    (g : (ι → Bool) → Bool) :
    0 ≤ corrError g α := by
  refine Finset.expect_nonneg fun x _ => ?_
  have h1 := abs_noiseOpVec_signVal_le_one hα g x
  linarith

/-- When `α = 1_J` and `h` depends only on `J`, `corrPairError g h α` equals the relative Hamming
distance `hammingDist g h / 2 ^ |ι|`. -/
theorem corrPairError_indicator_of_dependsOn (g h : (ι → Bool) → Bool)
    (J : Finset ι) (hh : DependsOn h (J : Set ι)) :
    corrPairError g h (fun i => if i ∈ J then (1 : ℝ) else 0) =
      (hammingDist g h : ℝ) / 2 ^ Fintype.card ι := by
  have hres :
      corrPairError g h (fun i => if i ∈ J then (1 : ℝ) else 0) =
        𝔼 x : ι → Bool, 𝔼 z : ι → Bool, if g (J.piecewise x z) = h x then (0 : ℝ) else 1 := by
    rw [corrPairError_eq_expect]
    refine Finset.expect_congr rfl fun x _ => ?_
    rw [noiseOpVec_indicator_eq_expect_piecewise]
    have hpt (z : ι → Bool) :
        (if g (J.piecewise x z) = h x then (0 : ℝ) else 1) =
          (1 - signVal (h x) * signVal (g (J.piecewise x z))) / 2 := by
      cases g (J.piecewise x z) <;> cases h x <;> norm_num [signVal]
    simp_rw [hpt, sub_div]
    rw [Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.expect_div, ← Finset.mul_expect]
  rw [hres]
  have hdep (x z : ι → Bool) : h x = h (J.piecewise x z) :=
    hh (fun i hi => (J.piecewise_eq_of_mem x z (Finset.mem_coe.mp hi)).symm)
  have hcongr :
      (𝔼 x : ι → Bool, 𝔼 z : ι → Bool, if g (J.piecewise x z) = h x then (0 : ℝ) else 1) =
        𝔼 x : ι → Bool, 𝔼 z : ι → Bool,
          if g (J.piecewise x z) = h (J.piecewise x z) then (0 : ℝ) else 1 := by
    refine Finset.expect_congr rfl fun x _ => Finset.expect_congr rfl fun z _ => ?_
    rw [hdep x z]
  rw [hcongr]
  have hinv :
      (𝔼 x : ι → Bool, 𝔼 z : ι → Bool,
        if g (J.piecewise x z) = h (J.piecewise x z) then (0 : ℝ) else 1) =
      𝔼 y : ι → Bool, if g y = h y then (0 : ℝ) else 1 := by
    let φ : (ι → Bool) → ℝ := fun y => if g y = h y then 0 else 1
    have hcoeff : fourierCoeff (fun x => 𝔼 z, φ (J.piecewise x z)) ∅ = fourierCoeff φ ∅ := by
      rw [fourierCoeff_expect_piecewise]
      simp only [Finset.empty_subset, ↓reduceIte]
    simpa [fourierCoeff_empty, φ] using hcoeff
  rw [hinv, Finset.expect_eq_sum_div_card]
  have hsum : (∑ y : ι → Bool, if g y = h y then (0 : ℝ) else 1) = (hammingDist g h : ℝ) := by
    rw [hammingDist, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : g y = h y <;> simp [hy]
  rw [hsum, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]

/-- **Lower sandwich**: `2 * corrError g α ≤ corrVar g α` for `α ∈ [-1, 1]^ι`. -/
theorem two_mul_corrError_le_corrVar {α : ι → ℝ} (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1)
    (g : (ι → Bool) → Bool) :
    2 * corrError g α ≤ corrVar g α := by
  unfold corrError corrVar
  have h1 : (1 : ℝ) = 𝔼 _x : ι → Bool, (1 : ℝ) := (Fintype.expect_const 1).symm
  conv_rhs => rw [h1, ← Finset.expect_sub_distrib]
  rw [Finset.mul_expect]
  refine Finset.expect_le_expect fun x _ => ?_
  have habs := abs_noiseOpVec_signVal_le_one hα g x
  have hnonneg : 0 ≤ |noiseOpVec α (fun y => signVal (g y)) x| := abs_nonneg _
  have hsq : |noiseOpVec α (fun y => signVal (g y)) x| ^ 2 =
      noiseOpVec α (fun y => signVal (g y)) x ^ 2 := sq_abs _
  nlinarith

/-- **Upper sandwich**: `corrVar g α ≤ 4 * corrError g α` for `α ∈ [-1, 1]^ι`. -/
theorem corrVar_le_four_mul_corrError {α : ι → ℝ} (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1)
    (g : (ι → Bool) → Bool) :
    corrVar g α ≤ 4 * corrError g α := by
  unfold corrError corrVar
  have h1 : (1 : ℝ) = 𝔼 _x : ι → Bool, (1 : ℝ) := (Fintype.expect_const 1).symm
  conv_lhs => rw [h1, ← Finset.expect_sub_distrib]
  rw [Finset.mul_expect]
  refine Finset.expect_le_expect fun x _ => ?_
  have habs := abs_noiseOpVec_signVal_le_one hα g x
  have hnonneg : 0 ≤ |noiseOpVec α (fun y => signVal (g y)) x| := abs_nonneg _
  have hsq : |noiseOpVec α (fun y => signVal (g y)) x| ^ 2 =
      noiseOpVec α (fun y => signVal (g y)) x ^ 2 := sq_abs _
  nlinarith

/-- Fourier formula for correlated variance:
`corrVar g α = 1 - ∑_S ĝ(S)² ∏_{i ∈ S} α_i²`. -/
theorem corrVar_eq_sum (g : (ι → Bool) → Bool) (α : ι → ℝ) :
    corrVar g α = 1 - ∑ S : Finset ι, fourierCoeff (fun y => signVal (g y)) S ^ 2 *
      ∏ i ∈ S, α i ^ 2 := by
  rw [corrVar, expect_noiseOpVec_sq]

/-- Correlated variance is nonnegative for `α ∈ [-1, 1]^ι`. -/
theorem corrVar_nonneg {α : ι → ℝ} (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1)
    (g : (ι → Bool) → Bool) :
    0 ≤ corrVar g α :=
  (mul_nonneg zero_le_two (corrError_nonneg hα g)).trans (two_mul_corrError_le_corrVar hα g)

/-- **Product-distribution invariance of correlated variance**: for any independent random vector
`z_i` with `𝔼[z_i²] = α_i²`, the expected `z`-correlated variance equals `corrVar g α`. -/
theorem sum_pi_corrVar_eq {β : ι → Type*} [∀ i, Fintype (β i)]
    (μ : ∀ i, PMF (β i)) (z : ∀ i, β i → ℝ) (α : ι → ℝ)
    (hz : ∀ i, ∑ b, (μ i b).toReal * z i b ^ 2 = α i ^ 2)
    (g : (ι → Bool) → Bool) :
    ∑ ω : ∀ i, β i, (Cslib.Probability.PMF.pi μ ω).toReal *
        corrVar g (fun i => z i (ω i)) =
      corrVar g α := by
  simp_rw [corrVar_eq_sum, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Cslib.Probability.PMF.sum_toReal, one_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hpull :
      (∑ ω : ∀ i, β i, (Cslib.Probability.PMF.pi μ ω).toReal *
        (fourierCoeff (fun y => signVal (g y)) S ^ 2 * ∏ i ∈ S, z i (ω i) ^ 2)) =
      fourierCoeff (fun y => signVal (g y)) S ^ 2 *
        ∑ ω : ∀ i, β i, (Cslib.Probability.PMF.pi μ ω).toReal *
          ∏ i ∈ S, z i (ω i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => by ring
  rw [hpull]
  congr 1
  have hprod :
      (∑ ω : ∀ i, β i, (Cslib.Probability.PMF.pi μ ω).toReal * ∏ i ∈ S, z i (ω i) ^ 2) =
        ∑ ω : ∀ i, β i, ∏ i : ι, (μ i (ω i)).toReal * (if i ∈ S then z i (ω i) ^ 2 else 1) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod, Finset.prod_mul_distrib,
      Fintype.prod_ite_mem S]
  rw [hprod, ← Fintype.prod_sum (fun i b => (μ i b).toReal * if i ∈ S then z i b ^ 2 else 1),
    ← Fintype.prod_ite_mem S]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact hz i
  · simp [Cslib.Probability.PMF.sum_toReal]

/-- Anisotropic Bernoulli specialization of correlated variance invariance: sampling each
coordinate `i` independently as `1` with probability `α i ^ 2` and `0` otherwise preserves
correlated variance in expectation. -/
theorem bernoulliAverageVec_corrVar_eq (α : ι → ℝ) (g : (ι → Bool) → Bool) :
    bernoulliAverageVec (fun i => α i ^ 2)
        (fun P => corrVar g (fun i => if P i then 1 else 0)) =
      corrVar g α := by
  unfold bernoulliAverageVec
  simp_rw [corrVar_eq_sum, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_bernoulliWeightVec, one_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hpull :
      (∑ P : ι → Bool, bernoulliWeightVec (fun i => α i ^ 2) P *
        (fourierCoeff (fun y => signVal (g y)) S ^ 2 *
          ∏ i ∈ S, (if P i then (1 : ℝ) else 0) ^ 2)) =
      fourierCoeff (fun y => signVal (g y)) S ^ 2 *
        bernoulliAverageVec (fun i => α i ^ 2)
          (fun P => ∏ i, if i ∈ S then (if P i then (1 : ℝ) else 0) ^ 2 else 1) := by
    unfold bernoulliAverageVec
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    dsimp only
    rw [Fintype.prod_ite_mem S]
    ring
  rw [hpull, bernoulliAverageVec_prod (fun i => α i ^ 2)
      (fun i b => if i ∈ S then (if b then (1 : ℝ) else 0) ^ 2 else 1), ← Fintype.prod_ite_mem S]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S <;> simp [hi]

/-- **Randomized junta rounding**: sampling each coordinate `i` independently with probability
`α_i²` yields an indicator vector whose expected correlated error is at most `2 * corrError g α`. -/
theorem bernoulliAverageVec_corrError_le_two_mul {α : ι → ℝ}
    (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) (g : (ι → Bool) → Bool) :
    bernoulliAverageVec (fun i => α i ^ 2)
        (fun P => corrError g (fun i => if P i then 1 else 0)) ≤
      2 * corrError g α := by
  have hp : ∀ i, α i ^ 2 ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨sq_nonneg _, by nlinarith [(hα i).1, (hα i).2]⟩
  have hstep :
      bernoulliAverageVec (fun i => α i ^ 2)
          (fun P => corrError g (fun i => if P i then 1 else 0)) ≤
        bernoulliAverageVec (fun i => α i ^ 2)
          (fun P => corrVar g (fun i => if P i then 1 else 0) / 2) := by
    refine bernoulliAverageVec_mono hp fun P => ?_
    have hP : ∀ i, (if P i then (1 : ℝ) else 0) ∈ Set.Icc (-1 : ℝ) 1 := fun i => by
      split_ifs <;> norm_num
    linarith [two_mul_corrError_le_corrVar hP g]
  have hhalf :
      bernoulliAverageVec (fun i => α i ^ 2)
          (fun P => corrVar g (fun i => if P i then 1 else 0) / 2) =
        corrVar g α / 2 := by
    simp_rw [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹]
    rw [bernoulliAverageVec_const_mul, bernoulliAverageVec_corrVar_eq α g]
  linarith [corrVar_le_four_mul_corrError hα g]

/-! ### Hard and soft junta complexity -/

/-- **Hard `δ`-approximate junta complexity** `J(g, δ)` under the uniform distribution: the
smallest `r : ℕ` such that `g` is within relative Hamming distance `δ` of a Boolean function
depending on at most `r` coordinates. -/
@[expose] noncomputable def juntaComplexity (g : (ι → Bool) → Bool) (δ : ℝ) : ℕ :=
  sInf {r : ℕ | ∃ (J : Finset ι) (h : (ι → Bool) → Bool),
    #J ≤ r ∧ DependsOn h (J : Set ι) ∧
      (hammingDist g h : ℝ) / 2 ^ Fintype.card ι ≤ δ}

/-- Infimum characterization of `juntaComplexity`. -/
theorem juntaComplexity_eq_sInf (g : (ι → Bool) → Bool) (δ : ℝ) :
    juntaComplexity g δ =
      sInf {r : ℕ | ∃ (J : Finset ι) (h : (ι → Bool) → Bool),
        #J ≤ r ∧ DependsOn h (J : Set ι) ∧
          (hammingDist g h : ℝ) / 2 ^ Fintype.card ι ≤ δ} := rfl

/-- **Soft `δ`-approximate junta complexity** `J̃(g, δ)`: the infimum of `∑ i, α i ^ 2` over all
correlation vectors `α ∈ [-1, 1]^ι` whose `α`-correlated error is at most `δ`. -/
@[expose] noncomputable def softJuntaComplexity (g : (ι → Bool) → Bool) (δ : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ α : ι → ℝ,
    (∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) ∧ corrError g α ≤ δ ∧ t = ∑ i, α i ^ 2}

/-- At `α = 1`, `noiseOpVec` is the identity operator. -/
@[simp]
theorem noiseOpVec_one (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    noiseOpVec (fun _ => 1) f x = f x := by
  have h := noiseOpVec_indicator_eq_expect_piecewise f Finset.univ x
  simp only [Finset.mem_univ, ↓reduceIte] at h
  rw [h]
  have hp : ∀ z : ι → Bool, Finset.univ.piecewise x z = x := fun z => by
    ext i
    simp
  simp [hp]

/-- At `α = 1`, the correlated error of any Boolean function is `0`. -/
@[simp]
theorem corrError_one (g : (ι → Bool) → Bool) :
    corrError g (fun _ => 1) = 0 := by
  unfold corrError
  simp [noiseOpVec_one, abs_signVal]

/-- The feasible set for `softJuntaComplexity g δ` is nonempty whenever `0 ≤ δ`. -/
theorem softJuntaComplexity_set_nonempty (g : (ι → Bool) → Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    {t : ℝ | ∃ α : ι → ℝ,
      (∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) ∧ corrError g α ≤ δ ∧ t = ∑ i, α i ^ 2}.Nonempty :=
  ⟨∑ _i : ι, (1 : ℝ) ^ 2, fun _ => 1, fun _ => ⟨by norm_num, le_rfl⟩,
    by rw [corrError_one]; exact hδ, rfl⟩

/-- `softJuntaComplexity g δ` is nonnegative. -/
theorem softJuntaComplexity_nonneg (g : (ι → Bool) → Bool) (δ : ℝ) :
    0 ≤ softJuntaComplexity g δ := by
  apply Real.sInf_nonneg
  rintro t ⟨α, -, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `softJuntaComplexity` is antitone in `δ`. -/
theorem softJuntaComplexity_antitone (g : (ι → Bool) → Bool) {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hδ : δ₁ ≤ δ₂) :
    softJuntaComplexity g δ₂ ≤ softJuntaComplexity g δ₁ := by
  apply csInf_le_csInf
  · exact ⟨0, by rintro t ⟨α, -, -, rfl⟩; exact Finset.sum_nonneg fun i _ => sq_nonneg _⟩
  · exact softJuntaComplexity_set_nonempty g hδ₁
  · rintro t ⟨α, hα, herr, rfl⟩
    exact ⟨α, hα, herr.trans hδ, rfl⟩

/-- `juntaComplexity` is bounded by `Fintype.card ι` whenever `0 ≤ δ`. -/
theorem juntaComplexity_le_card (g : (ι → Bool) → Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    juntaComplexity g δ ≤ Fintype.card ι := by
  apply Nat.sInf_le
  refine ⟨Finset.univ, g, by simp, fun x y hxy => ?_, ?_⟩
  · have : x = y := funext fun i => hxy i (Finset.mem_coe.mpr (Finset.mem_univ i))
    rw [this]
  · simpa [hammingDist_self] using hδ

/-- `juntaComplexity g δ` is achieved by some coordinate set `J` and `J`-junta `h` whenever
`0 ≤ δ`. -/
theorem exists_junta_of_juntaComplexity (g : (ι → Bool) → Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ (J : Finset ι) (h : (ι → Bool) → Bool),
      #J ≤ juntaComplexity g δ ∧ DependsOn h (J : Set ι) ∧
        (hammingDist g h : ℝ) / 2 ^ Fintype.card ι ≤ δ := by
  have hne : {r : ℕ | ∃ (J : Finset ι) (h : (ι → Bool) → Bool),
      #J ≤ r ∧ DependsOn h (J : Set ι) ∧
        (hammingDist g h : ℝ) / 2 ^ Fintype.card ι ≤ δ}.Nonempty := by
    refine ⟨Fintype.card ι, Finset.univ, g, by simp, fun x y hxy => ?_, ?_⟩
    · have : x = y := funext fun i => hxy i (Finset.mem_coe.mpr (Finset.mem_univ i))
      rw [this]
    · simpa [hammingDist_self] using hδ
  exact Nat.sInf_mem hne

/-- **Upper bound on soft junta complexity**: `J̃(g, δ) ≤ J(g, δ)` for all `δ ≥ 0`. -/
theorem softJuntaComplexity_le_juntaComplexity (g : (ι → Bool) → Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    softJuntaComplexity g δ ≤ (juntaComplexity g δ : ℝ) := by
  obtain ⟨J, h, hJ, hh, hdist⟩ := exists_junta_of_juntaComplexity g hδ
  let α : ι → ℝ := fun i => if i ∈ J then 1 else 0
  have hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1 := fun i => by
    dsimp [α]; split_ifs <;> norm_num
  have herr : corrError g α ≤ δ :=
    (corrError_le_corrPairError g h α).trans
      ((corrPairError_indicator_of_dependsOn g h J hh).le.trans hdist)
  have hsum : ∑ i, α i ^ 2 = (#J : ℝ) := by
    simp [α]
  have hmem : (#J : ℝ) ∈ {t : ℝ | ∃ α : ι → ℝ,
      (∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) ∧ corrError g α ≤ δ ∧ t = ∑ i, α i ^ 2} :=
    ⟨α, hα, herr, hsum.symm⟩
  have hbdd : BddBelow {t : ℝ | ∃ α : ι → ℝ,
      (∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) ∧ corrError g α ≤ δ ∧ t = ∑ i, α i ^ 2} :=
    ⟨0, by rintro t ⟨α', -, -, rfl⟩; exact Finset.sum_nonneg fun i _ => sq_nonneg _⟩
  exact (csInf_le hbdd hmem).trans (by exact_mod_cast hJ)

/-- **Hard-from-soft junta rounding**: for every `α ∈ [-1, 1]^ι` with `corrError g α ≤ δ`
(`δ ≥ 0`), there exists a coordinate set `J` of size at most `2 * ∑ i, α i ^ 2` and a `J`-junta
`h` at relative Hamming distance at most `4 * δ` from `g`. -/
theorem exists_junta_of_corrError_le (g : (ι → Bool) → Bool) {α : ι → ℝ}
    (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ) (herr : corrError g α ≤ δ) :
    ∃ (J : Finset ι) (h : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 2 * ∑ i, α i ^ 2 ∧ DependsOn h (J : Set ι) ∧
        (hammingDist g h : ℝ) / 2 ^ Fintype.card ι ≤ 4 * δ := by
  classical
  let p : ι → ℝ := fun i => α i ^ 2
  have hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    ⟨sq_nonneg _, by nlinarith [(hα i).1, (hα i).2]⟩
  let S : ℝ := ∑ i, p i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (hp i).1
  let ind (P : ι → Bool) : ι → ℝ := fun i => if P i then 1 else 0
  let sizeP (P : ι → Bool) : ℝ := (#{i | P i = true} : ℝ)
  have hExpSize : bernoulliAverageVec p sizeP = S := bernoulliAverageVec_card_filter p
  have hExpErr : bernoulliAverageVec p (fun P => corrError g (ind P)) ≤ 2 * δ :=
    (bernoulliAverageVec_corrError_le_two_mul hα g).trans (by linarith)
  unfold bernoulliAverageVec at hExpSize hExpErr
  -- Pick a mask `P` with both small size and small correlated error.
  have hexP : ∃ P : ι → Bool, sizeP P ≤ 2 * S ∧ corrError g (ind P) ≤ 4 * δ := by
    by_cases hS0 : S = 0
    · -- All `α i = 0`; the empty mask has weight `1`, size `0`, and error `corrError g 0 ≤ 2 δ`.
      have hα0 : ∀ i, α i = 0 := fun i => by
        have hle : p i ≤ S := Finset.single_le_sum (fun j _ => (hp j).1) (Finset.mem_univ i)
        have hpi0 : α i ^ 2 = 0 := le_antisymm (hS0 ▸ hle) (sq_nonneg _)
        exact sq_eq_zero_iff.mp hpi0
      refine ⟨fun _ => false, by simp [sizeP, hS0], ?_⟩
      have hind : ind (fun _ => false) = α := funext fun i => by simp [ind, hα0 i]
      rw [hind]
      linarith
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      by_cases hδ0 : δ = 0
      · -- At `δ = 0`, `corrError g α = 0`, so every mask in the support has `corrError = 0`.
        have herr0 : corrError g α = 0 := le_antisymm (hδ0 ▸ herr) (corrError_nonneg hα g)
        have hExp0 : ∑ P : ι → Bool, bernoulliWeightVec p P * corrError g (ind P) = 0 :=
          le_antisymm (by linarith)
            (Finset.sum_nonneg fun P _ =>
              mul_nonneg (bernoulliWeightVec_nonneg hp P)
                (corrError_nonneg (fun i => by dsimp [ind]; split_ifs <;> norm_num) g))
        -- Some `P` in the support has `sizeP P ≤ S ≤ 2 * S` (strictly positive total weight `1`).
        by_contra hno
        push Not at hno
        have hbad : ∀ P : ι → Bool,
            bernoulliWeightVec p P * (sizeP P) ≥
              bernoulliWeightVec p P * (2 * S) ∨
            bernoulliWeightVec p P * corrError g (ind P) > 0 := by
          intro P
          by_cases hw : bernoulliWeightVec p P = 0
          · left; simp [hw]
          · have hwpos : 0 < bernoulliWeightVec p P :=
              lt_of_le_of_ne (bernoulliWeightVec_nonneg hp P) (Ne.symm hw)
            by_cases hsz : sizeP P ≤ 2 * S
            · right
              have hce := hno P hsz
              rw [hδ0, mul_zero] at hce
              exact mul_pos hwpos hce
            · left
              exact mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hsz)) hwpos.le
        have hzero : ∀ P : ι → Bool,
            bernoulliWeightVec p P * corrError g (ind P) = 0 := by
          intro P
          exact Finset.sum_eq_zero_iff_of_nonneg (fun Q _ =>
            mul_nonneg (bernoulliWeightVec_nonneg hp Q)
              (corrError_nonneg (fun i => by dsimp [ind]; split_ifs <;> norm_num) g))
            |>.mp hExp0 P (Finset.mem_univ P)
        have hge : ∀ P : ι → Bool,
            bernoulliWeightVec p P * (2 * S) ≤ bernoulliWeightVec p P * sizeP P := by
          intro P
          rcases hbad P with h1 | h2
          · exact h1
          · linarith [hzero P]
        have hsum : (2 * S) ≤ S := by
          calc 2 * S = ∑ P : ι → Bool, bernoulliWeightVec p P * (2 * S) := by
                rw [← Finset.sum_mul, sum_bernoulliWeightVec, one_mul]
            _ ≤ ∑ P : ι → Bool, bernoulliWeightVec p P * sizeP P :=
                Finset.sum_le_sum fun P _ => hge P
            _ = S := hExpSize
        linarith
      · -- Generic case `S > 0`, `δ > 0`: strict Markov on size `< 1/2` + Markov on error `≤ 1/2`.
        have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
        by_contra hno
        push Not at hno
        -- Strict Markov: `∑_{sizeP P > 2 S} w(P) < 1 / 2`.
        let B₁ : Finset (ι → Bool) := Finset.univ.filter (fun P => 2 * S < sizeP P)
        let B₂ : Finset (ι → Bool) := Finset.univ.filter (fun P => 4 * δ < corrError g (ind P))
        have hB₁ : ∑ P ∈ B₁, bernoulliWeightVec p P < 1 / 2 := by
          by_cases hB₁0 : ∑ P ∈ B₁, bernoulliWeightVec p P = 0
          · linarith
          · have hpos : 0 < ∑ P ∈ B₁, bernoulliWeightVec p P :=
              lt_of_le_of_ne (Finset.sum_nonneg fun P _ => bernoulliWeightVec_nonneg hp P)
                (Ne.symm hB₁0)
            obtain ⟨P₀, hP₀mem, hP₀pos⟩ : ∃ P₀ ∈ B₁, 0 < bernoulliWeightVec p P₀ := by
              by_contra hall
              push Not at hall
              have : ∑ P ∈ B₁, bernoulliWeightVec p P = 0 :=
                Finset.sum_eq_zero fun P hP =>
                  le_antisymm (hall P hP) (bernoulliWeightVec_nonneg hp P)
              exact hB₁0 this
            have hstrict :
                (2 * S) * ∑ P ∈ B₁, bernoulliWeightVec p P <
                  ∑ P ∈ B₁, bernoulliWeightVec p P * sizeP P := by
              rw [Finset.mul_sum]
              refine Finset.sum_lt_sum (fun P hP => ?_) ⟨P₀, hP₀mem, ?_⟩
              · rw [mul_comm]
                exact mul_le_mul_of_nonneg_left (le_of_lt (Finset.mem_filter.mp hP).2)
                  (bernoulliWeightVec_nonneg hp P)
              · rw [mul_comm]
                exact mul_lt_mul_of_pos_left (Finset.mem_filter.mp hP₀mem).2 hP₀pos
            have hleS : ∑ P ∈ B₁, bernoulliWeightVec p P * sizeP P ≤ S := by
              calc ∑ P ∈ B₁, bernoulliWeightVec p P * sizeP P
                  ≤ ∑ P : ι → Bool, bernoulliWeightVec p P * sizeP P :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun P _ _ =>
                      mul_nonneg (bernoulliWeightVec_nonneg hp P) (Nat.cast_nonneg _)
                _ = S := hExpSize
            nlinarith
        -- Markov on error: `∑_{corrError > 4 δ} w(P) ≤ 1 / 2`.
        have hB₂ : ∑ P ∈ B₂, bernoulliWeightVec p P ≤ 1 / 2 := by
          have hmul : (4 * δ) * ∑ P ∈ B₂, bernoulliWeightVec p P ≤ 2 * δ := by
            calc (4 * δ) * ∑ P ∈ B₂, bernoulliWeightVec p P
                = ∑ P ∈ B₂, bernoulliWeightVec p P * (4 * δ) := by
                  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
              _ ≤ ∑ P ∈ B₂, bernoulliWeightVec p P * corrError g (ind P) :=
                  Finset.sum_le_sum fun P hP =>
                    mul_le_mul_of_nonneg_left (le_of_lt (Finset.mem_filter.mp hP).2)
                      (bernoulliWeightVec_nonneg hp P)
              _ ≤ ∑ P : ι → Bool, bernoulliWeightVec p P * corrError g (ind P) :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun P _ _ =>
                    mul_nonneg (bernoulliWeightVec_nonneg hp P)
                      (corrError_nonneg (fun i => by dsimp [ind]; split_ifs <;> norm_num) g)
              _ ≤ 2 * δ := hExpErr
          nlinarith
        -- Every `P` belongs to `B₁ ∪ B₂`, so the weights sum to `< 1`, contradiction.
        have hcov : Finset.univ ⊆ B₁ ∪ B₂ := by
          intro P _
          rw [Finset.mem_union]
          by_cases hsz : sizeP P ≤ 2 * S
          · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ P, hno P hsz⟩)
          · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ P, not_le.mp hsz⟩)
        have hsum1 : (1 : ℝ) ≤ ∑ P ∈ B₁ ∪ B₂, bernoulliWeightVec p P := by
          calc (1 : ℝ) = ∑ P : ι → Bool, bernoulliWeightVec p P := (sum_bernoulliWeightVec p).symm
            _ ≤ ∑ P ∈ B₁ ∪ B₂, bernoulliWeightVec p P :=
                Finset.sum_le_sum_of_subset_of_nonneg hcov fun P _ _ =>
                  bernoulliWeightVec_nonneg hp P
        have hunion :
            ∑ P ∈ B₁ ∪ B₂, bernoulliWeightVec p P ≤
              (∑ P ∈ B₁, bernoulliWeightVec p P) + ∑ P ∈ B₂, bernoulliWeightVec p P := by
          have h := Finset.sum_union_inter (s₁ := B₁) (s₂ := B₂) (f := bernoulliWeightVec p)
          have hni : 0 ≤ ∑ P ∈ B₁ ∩ B₂, bernoulliWeightVec p P :=
            Finset.sum_nonneg fun P _ => bernoulliWeightVec_nonneg hp P
          linarith
        linarith
  obtain ⟨P, hPsize, hPerr⟩ := hexP
  let J : Finset ι := Finset.univ.filter (fun i => P i = true)
  let h : (ι → Bool) → Bool :=
    fun x => decide (noiseOpVec (ind P) (fun y => signVal (g y)) x < 0)
  have hh : DependsOn h (J : Set ι) := by
    intro x y hxy
    have hnoise : noiseOpVec (ind P) (fun z => signVal (g z)) x =
        noiseOpVec (ind P) (fun z => signVal (g z)) y := by
      have hind : ind P = fun i => if i ∈ J then (1 : ℝ) else 0 := by
        ext i; simp [ind, J]
      rw [hind, noiseOpVec_indicator_eq_expect_piecewise,
        noiseOpVec_indicator_eq_expect_piecewise]
      refine Finset.expect_congr rfl fun z _ => ?_
      exact congrArg (fun u => signVal (g u))
        (J.piecewise_congr (fun i hi => hxy i (Finset.mem_coe.mpr hi)) (fun _ _ => rfl))
    simp only [h, hnoise]
  have hdist : (hammingDist g h : ℝ) / 2 ^ Fintype.card ι ≤ 4 * δ := by
    have hind : ind P = fun i => if i ∈ J then (1 : ℝ) else 0 := by
      ext i; simp [ind, J]
    rw [← corrPairError_indicator_of_dependsOn g h J hh, ← hind]
    have heq := corrPairError_bayes_eq_corrError g (ind P)
    dsimp only [h]
    rw [heq]
    exact hPerr
  exact ⟨J, h, hPsize, hh, hdist⟩

/-- **Lower bound on soft junta complexity**: `(1 / 2) * J(g, 4 * δ) ≤ J̃(g, δ)` for all `δ ≥ 0`. -/
theorem half_juntaComplexity_four_mul_le_softJuntaComplexity (g : (ι → Bool) → Bool)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (juntaComplexity g (4 * δ) : ℝ) / 2 ≤ softJuntaComplexity g δ := by
  apply le_csInf (softJuntaComplexity_set_nonempty g hδ)
  rintro t ⟨α, hα, herr, rfl⟩
  obtain ⟨J, h, hJ, hh, hdist⟩ := exists_junta_of_corrError_le g hα hδ herr
  have hle : juntaComplexity g (4 * δ) ≤ #J :=
    Nat.sInf_le ⟨J, h, le_rfl, hh, hdist⟩
  have hleR : (juntaComplexity g (4 * δ) : ℝ) ≤ (#J : ℝ) := by exact_mod_cast hle
  linarith

end Cslib.BitString
