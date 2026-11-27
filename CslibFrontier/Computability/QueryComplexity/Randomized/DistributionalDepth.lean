/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Computability.DecisionTree.Cost
public import CslibFrontier.Computability.DecisionTree.Leaves
public import CslibFrontier.Computability.QueryComplexity.Randomized
public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalCost
public import CslibFrontier.Computability.QueryComplexity.Randomized.ZeroError
public import CslibFrontier.Probability.Conditioning
public import CslibFrontier.Probability.Minimax
public import CslibFrontier.Probability.Product
public import Mathlib.Basic.Real.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Core definitions for distributional query complexity and direct sum theorems

This module defines the basic objects:

- Boolean functions in `{-1, +1}`-sign convention (`signBool`), $k$-fold direct products
 `directProduct` ($f^{\otimes k}$), $k$-fold XOR / direct sums `directSum` ($f^{\oplus k}$),
 and the parity function `parity` ($\mathsf{Par}$).
- Expected distributional depth (`detDistDepth`, `distDepth`), threshold distributional depth
 (`thresholdDistDepth`), and expected-depth randomized query complexity (`randExpectedDepth`)
 built directly on `Cslib.DecisionTree` and `Cslib.RandomizedDecisionTree`.
- Bernoulli-sum distributions (`berSumPMF`), binomial distributions (`binomialPMF`), hardcore
 measures (`IsHardcoreMeasure`), the canonical leaf distribution (`leafDist`), hardcore
 density (`hardcoreDensityAt`, `hardcoreDensity`), hardcore advantage (`hardcoreAdvantageAt`,
 `hardcoreAdvantage`), and the $k$-wise product tree (`productTree`).
- Basic structural results: deterministic-vs-randomized comparison (`claim_connect_det_rand`,
 `cor_rand_to_det_DP`), monotonicity of `berSumPMF` tail probabilities, and the leaf
 product-distribution property (`claim_leaf_product`).
-/

public section

namespace CslibFrontier.Computability.QueryComplexity.DirectSum

open Cslib Convexity Finset
open scoped BigOperators ENNReal NNReal

/-! ### Sign convention and Boolean function constructions -/

/-- Map `Bool` to `{-1, +1}` in `ℝ` (`true ↦ 1`, `false ↦ -1`). -/
@[expose] def signBool (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] theorem signBool_true : signBool true = 1 := rfl

@[simp] theorem signBool_false : signBool false = -1 := rfl

@[simp] theorem signBool_not (b : Bool) : signBool (!b) = -signBool b := by
  cases b <;> norm_num [signBool]

@[simp] theorem signBool_mul_self (b : Bool) : signBool b * signBool b = 1 := by
  cases b <;> norm_num [signBool]

@[simp] theorem abs_signBool (b : Bool) : |signBool b| = 1 := by
  cases b <;> norm_num [signBool]

theorem signBool_mul_eq_ite (b c : Bool) :
    signBool b * signBool c = if b = c then 1 else -1 := by
  cases b <;> cases c <;> norm_num [signBool]

theorem one_sub_signBool_mul_div_two (b c : Bool) :
    (1 - signBool b * signBool c) / 2 = if b = c then 0 else 1 := by
  cases b <;> cases c <;> norm_num [signBool]

theorem one_add_signBool_mul_div_two (b c : Bool) :
    (1 + signBool b * signBool c) / 2 = if b = c then 1 else 0 := by
  cases b <;> cases c <;> norm_num [signBool]

theorem signBool_le_one (b : Bool) : signBool b ≤ 1 := by
  cases b <;> norm_num [signBool]

theorem neg_one_le_signBool (b : Bool) : -1 ≤ signBool b := by
  cases b <;> norm_num [signBool]

/-- The $k$-fold direct product $f^{\otimes k} : (\{0,1\}^n)^k \to \{0,1\}^k$. -/
@[expose] def directProduct {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) :
    (Fin k → Fin n → Bool) → (Fin k → Bool) :=
  fun X i ↦ f (X i)

@[simp] theorem directProduct_apply {n k : ℕ} (f : (Fin n → Bool) → Bool)
    (X : Fin k → Fin n → Bool) (i : Fin k) :
    directProduct f k X i = f (X i) := rfl

/-- The uncurried $k$-fold direct product for `DecisionTree (Fin k × Fin n)`. -/
@[expose] def directProductUncurry {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) :
    (Fin k × Fin n → Bool) → (Fin k → Bool) :=
  fun x i ↦ f (fun j ↦ x (i, j))

/-- The $k$-fold XOR (direct sum in `{-1, +1}` multiplication) $f^{\oplus k}$. -/
@[expose] def directSum {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) :
    (Fin k → Fin n → Bool) → Bool :=
  fun X ↦ decide (Even (Finset.univ.filter fun i : Fin k ↦ f (X i) = false).card)

/-- The uncurried $k$-fold XOR for `DecisionTree (Fin k × Fin n)`. -/
@[expose] def directSumUncurry {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) :
    (Fin k × Fin n → Bool) → Bool :=
  fun x ↦ directSum f k (Function.curry x)

/-- Sign of `directSum f k X` equals the product of `signBool (f (X i))` over `i : Fin k`. -/
theorem signBool_directSum {n k : ℕ} (f : (Fin n → Bool) → Bool)
    (X : Fin k → Fin n → Bool) :
    signBool (directSum f k X) = ∏ i : Fin k, signBool (f (X i)) := by
  have hprod : (∏ i : Fin k, signBool (f (X i))) =
      (-1 : ℝ) ^ (Finset.univ.filter fun i : Fin k ↦ f (X i) = false).card := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin k ↦ f (X i) = false)]
    have h1 : (∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ f (X i) = false),
        signBool (f (X i))) =
        (-1 : ℝ) ^ (Finset.univ.filter fun i : Fin k ↦ f (X i) = false).card := by
      calc (∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ f (X i) = false),
            signBool (f (X i)))
          = ∏ _i ∈ Finset.univ.filter (fun i : Fin k ↦ f (X i) = false), (-1 : ℝ) :=
            Finset.prod_congr rfl fun i hi ↦ by simp [(Finset.mem_filter.mp hi).2]
        _ = (-1 : ℝ) ^ (Finset.univ.filter fun i : Fin k ↦ f (X i) = false).card := by
            rw [Finset.prod_const]
    have h2 : (∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ ¬(f (X i) = false)),
        signBool (f (X i))) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hne : f (X i) ≠ false := (Finset.mem_filter.mp hi).2
      cases h : f (X i)
      · exact absurd h hne
      · rfl
    rw [h1, h2, mul_one]
  rw [hprod, directSum]
  by_cases he : Even (Finset.univ.filter fun i : Fin k ↦ f (X i) = false).card
  · simp [he, he.neg_one_pow]
  · simp [he, (Nat.not_even_iff_odd.mp he).neg_one_pow]

/-- The $n$-variable parity function $\mathsf{Par} : \{0,1\}^n \to \{0,1\}$ (in `{-1,+1}`
multiplication). -/
@[expose] def parity (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x ↦ decide (Even (Finset.univ.filter fun i : Fin n ↦ x i = false).card)

/-- Sign of `parity n x` is `∏ i, signBool (x i)`. -/
theorem signBool_parity {n : ℕ} (x : Fin n → Bool) :
    signBool (parity n x) = ∏ i : Fin n, signBool (x i) := by
  simpa [parity, directSum] using
    signBool_directSum (n := 1) (k := n) (fun v ↦ v 0) (fun i _ ↦ x i)

@[simp] theorem parity_zero (x : Fin 0 → Bool) : parity 0 x = true := by
  simp [parity]

/-- Flipping a single coordinate flips `parity n x`. -/
theorem parity_update_not {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    parity n (Function.update x i (!x i)) = !(parity n x) := by
  have h1 := signBool_parity (Function.update x i (!x i))
  have h2 := signBool_parity x
  have hprod : (∏ j : Fin n, signBool (Function.update x i (!x i) j)) =
      -(∏ j : Fin n, signBool (x j)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, signBool_not, neg_mul]
    congr 1
    congr 1
    exact Finset.prod_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hprod, ← h2] at h1
  cases hp : parity n (Function.update x i (!x i)) <;> cases hq : parity n x
  · rw [hp, hq] at h1; norm_num [signBool] at h1
  · rfl
  · rfl
  · rw [hp, hq] at h1; norm_num [signBool] at h1

/-- Hamming distance $\lVert y - z \rVert_0$ between two `Fin k → Bool` vectors. -/
@[expose] def hammingDist {k : ℕ} (y z : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin k ↦ y i ≠ z i).card

@[simp] theorem hammingDist_eq_zero_iff {k : ℕ} {y z : Fin k → Bool} :
    hammingDist y z = 0 ↔ y = z := by
  simp [hammingDist, Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]

theorem hammingDist_le {k : ℕ} (y z : Fin k → Bool) : hammingDist y z ≤ k := by
  unfold hammingDist
  simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin k ↦ y i ≠ z i)

/-! ### Product, Bernoulli, and Bernoulli-sum distributions -/

/-- The $k$-fold product distribution $\mu^k$ on `Fin k → Fin n → Bool`. -/
noncomputable def prodPMF {n : ℕ} (μ : PMF (Fin n → Bool)) (k : ℕ) :
    PMF (Fin k → Fin n → Bool) :=
  Cslib.Probability.PMF.pi (fun _ : Fin k ↦ μ)

theorem prodPMF_eq_pi {n k : ℕ} (μ : PMF (Fin n → Bool)) :
    prodPMF μ k = Cslib.Probability.PMF.pi (fun _ : Fin k ↦ μ) := by rfl

theorem prodPMF_apply {n k : ℕ} (μ : PMF (Fin n → Bool)) (X : Fin k → Fin n → Bool) :
    prodPMF μ k X = ∏ i : Fin k, μ (X i) :=
  Cslib.Probability.PMF.pi_apply (fun _ : Fin k ↦ μ) X

/-- Bernoulli distribution $\mathrm{Ber}(p)$ on `Bool` for `p ∈ [0, 1]`
(clamped outside `[0, 1]`). -/
noncomputable def bernoulliPMF (p : ℝ) : PMF Bool :=
  let q := max 0 (min p 1)
  PMF.ofFintype (fun b ↦ if b then ENNReal.ofReal q else ENNReal.ofReal (1 - q)) (by
    have hq0 : 0 ≤ q := le_max_left 0 _
    have hq1 : q ≤ 1 := max_le zero_le_one (min_le_right p 1)
    rw [Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rw [← ENNReal.ofReal_add hq0 (sub_nonneg.mpr hq1), add_sub_cancel, ENNReal.ofReal_one])

theorem bernoulliPMF_apply_true {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliPMF p true).toReal = p := by
  simp [bernoulliPMF, min_eq_left hp1, max_eq_right hp0, ENNReal.toReal_ofReal hp0]

theorem bernoulliPMF_apply_false {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliPMF p false).toReal = 1 - p := by
  simp [bernoulliPMF, min_eq_left hp1, max_eq_right hp0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]

/-- Sum of independent Bernoulli random variables $\mathrm{BerSum}(p)$ on `Fin k → Bool`. -/
noncomputable def berSumPMF {k : ℕ} (p : Fin k → ℝ) : PMF (Fin k → Bool) :=
  Cslib.Probability.PMF.pi (fun i : Fin k ↦ bernoulliPMF (p i))

theorem berSumPMF_eq_pi {k : ℕ} (p : Fin k → ℝ) :
    berSumPMF p = Cslib.Probability.PMF.pi (fun i : Fin k ↦ bernoulliPMF (p i)) := by rfl

/-- Number of `true` entries in a Boolean vector. -/
@[expose] def trueCount {k : ℕ} (z : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin k ↦ z i = true).card

theorem trueCount_eq_card_filter {k : ℕ} (z : Fin k → Bool) :
    trueCount z = (Finset.univ.filter fun i : Fin k ↦ z i = true).card := rfl

theorem trueCount_cast_eq_sum {k : ℕ} (z : Fin k → Bool) :
    (trueCount z : ℝ) = ∑ i : Fin k, if z i = true then (1 : ℝ) else 0 := by
  simp [trueCount, Finset.sum_boole]

theorem hammingDist_eq_trueCount_decide {k : ℕ} (y z : Fin k → Bool) :
    hammingDist y z = trueCount (fun i ↦ decide (y i ≠ z i)) := by
  simp [hammingDist, trueCount]

/-- Tail probability $\Pr_{z \sim \mathrm{BerSum}(p)}[\sum_i z_i \le t]$. -/
noncomputable def berSumCdf {k : ℕ} (p : Fin k → ℝ) (t : ℝ) : ℝ :=
  ∑ z : Fin k → Bool,
    (berSumPMF p z).toReal * if (trueCount z : ℝ) ≤ t then 1 else 0

theorem berSumCdf_eq_sum {k : ℕ} (p : Fin k → ℝ) (t : ℝ) :
    berSumCdf p t = ∑ z : Fin k → Bool,
      (berSumPMF p z).toReal * if (trueCount z : ℝ) ≤ t then 1 else 0 := by rfl

/-- Binomial distribution $\mathrm{Bin}(k, \delta)$ as the `trueCount` pushforward of
`berSumPMF (fun _ ↦ δ)`. -/
noncomputable def binomialPMF (k : ℕ) (δ : ℝ) : PMF ℕ :=
  (berSumPMF (fun _ : Fin k ↦ δ)).map trueCount

theorem trueCount_fin_succ {k : ℕ} (z : Fin (k + 1) → Bool) :
    trueCount z = (if z 0 = true then 1 else 0) + trueCount (Fin.tail z) := by
  classical
  simp only [trueCount, Fin.card_filter_univ_succ]
  cases z 0 <;> simp [Fin.tail, add_comm] <;> rfl

theorem berSumCdf_fin_succ {k : ℕ} (p : Fin (k + 1) → ℝ) (hp : ∀ i, p i ∈ Set.Icc 0 1)
    (t : ℝ) :
    berSumCdf p t =
      p 0 * berSumCdf (Fin.tail p) (t - 1) + (1 - p 0) * berSumCdf (Fin.tail p) t := by
  classical
  simp only [berSumCdf, berSumPMF, Cslib.Probability.PMF.pi_fin_succ_dep]
  rw [Cslib.Probability.PMF.sum_bind_mul]
  rw [Fintype.sum_bool]
  have htrue : (bernoulliPMF (p 0) true).toReal = p 0 :=
    bernoulliPMF_apply_true (hp 0).1 (hp 0).2
  have hfalse : (bernoulliPMF (p 0) false).toReal = 1 - p 0 :=
    bernoulliPMF_apply_false (hp 0).1 (hp 0).2
  rw [htrue, hfalse]
  congr 1
  · congr 1
    rw [Cslib.Probability.PMF.sum_map_mul]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    congr 1
    have htc : trueCount (Fin.cons true z) = 1 + trueCount z := by
      simpa [Fin.tail_cons] using trueCount_fin_succ (Fin.cons true z)
    rw [htc]
    simp only [Nat.cast_add, Nat.cast_one]
    have hiff : (1 : ℝ) + (trueCount z : ℝ) ≤ t ↔ (trueCount z : ℝ) ≤ t - 1 := by
      constructor <;> intro h <;> linarith
    simp [hiff]
  · congr 1
    rw [Cslib.Probability.PMF.sum_map_mul]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    congr 1
    have htc : trueCount (Fin.cons false z) = trueCount z := by
      simpa [Fin.tail_cons] using trueCount_fin_succ (Fin.cons false z)
    rw [htc]

theorem berSumCdf_mono_threshold {k : ℕ} (p : Fin k → ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    berSumCdf p t₁ ≤ berSumCdf p t₂ := by
  refine Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans ht) h2
  · exact zero_le_one
  · exact le_rfl

/-- $\Pr_{z \sim \mathrm{BerSum}(q)}[z \le t]$ is monotonically decreasing in each coordinate
of `q`. -/
theorem berSumCdf_antitone {k : ℕ} {p q : Fin k → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hq : ∀ i, q i ∈ Set.Icc 0 1)
    (hpq : ∀ i, p i ≤ q i) (t : ℝ) :
    berSumCdf q t ≤ berSumCdf p t := by
  induction k generalizing t with
  | zero =>
    simp [berSumCdf, berSumPMF, Cslib.Probability.PMF.pi_apply]
  | succ k ih =>
    rw [berSumCdf_fin_succ q hq t, berSumCdf_fin_succ p hp t]
    have htail_p : ∀ i : Fin k, Fin.tail p i ∈ Set.Icc 0 1 := fun i ↦ hp i.succ
    have htail_q : ∀ i : Fin k, Fin.tail q i ∈ Set.Icc 0 1 := fun i ↦ hq i.succ
    have htail_pq : ∀ i : Fin k, Fin.tail p i ≤ Fin.tail q i := fun i ↦ hpq i.succ
    have h1 := ih htail_p htail_q htail_pq (t - 1)
    have h2 := ih htail_p htail_q htail_pq t
    have hmono := berSumCdf_mono_threshold (Fin.tail p) (show t - 1 ≤ t by linarith)
    have hstep1 : q 0 * berSumCdf (Fin.tail q) (t - 1) + (1 - q 0) * berSumCdf (Fin.tail q) t ≤
        q 0 * berSumCdf (Fin.tail p) (t - 1) + (1 - q 0) * berSumCdf (Fin.tail p) t := by
      have hq0 : 0 ≤ q 0 := (hq 0).1
      have h1q0 : 0 ≤ 1 - q 0 := sub_nonneg.mpr (hq 0).2
      nlinarith
    have hstep2 : q 0 * berSumCdf (Fin.tail p) (t - 1) + (1 - q 0) * berSumCdf (Fin.tail p) t ≤
        p 0 * berSumCdf (Fin.tail p) (t - 1) + (1 - p 0) * berSumCdf (Fin.tail p) t := by
      have hdiff := hpq 0
      nlinarith
    exact hstep1.trans hstep2

/-! ### Expected depth, distributional error, and distributional query complexity -/

/-- Expected depth $\overline{\mathrm{Depth}}^\mu(t)$ of a deterministic decision tree under `μ`. -/
noncomputable def detExpectedDepth {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (t : DecisionTree ι β) : ℝ :=
  ∑ x : ι → Bool, (μ x).toReal * (t.cost x : ℝ)

/-- Expected depth $\overline{\mathrm{Depth}}^\mu(\mathcal{T})$ of a randomized decision tree
under `μ`. -/
noncomputable def randExpectedDepthTree {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (T : RandomizedDecisionTree ι β) : ℝ :=
  T.weights.sum fun t w ↦ w * detExpectedDepth μ t

/-- Distributional error $\Pr_{x \sim \mu}[t(x) \ne f(x)]$ of a deterministic tree. -/
noncomputable def detDistError {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (t : DecisionTree ι β) : ℝ :=
  t.distributionalError (Cslib.Probability.PMF.toStdSimplex μ) f

/-- Distributional error $\Pr_{x \sim \mu, t \sim \mathcal{T}}[t(x) \ne f(x)]$ of a randomized
decision tree. -/
noncomputable def randDistError {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (T : RandomizedDecisionTree ι β) : ℝ :=
  T.weights.sum fun t w ↦ w * detDistError μ f t

theorem detExpectedDepth_eq_sum {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (t : DecisionTree ι β) :
    detExpectedDepth μ t = ∑ x : ι → Bool, (μ x).toReal * (t.cost x : ℝ) := by rfl

@[simp] theorem detExpectedDepth_leaf {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (b : β) :
    detExpectedDepth μ (.leaf b) = 0 := by
  simp [detExpectedDepth]

theorem randExpectedDepthTree_eq_sum {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (T : RandomizedDecisionTree ι β) :
    randExpectedDepthTree μ T = T.weights.sum fun t w ↦ w * detExpectedDepth μ t := by rfl

theorem randDistError_eq_sum {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (T : RandomizedDecisionTree ι β) :
    randDistError μ f T = T.weights.sum fun t w ↦ w * detDistError μ f t := by rfl

theorem detExpectedDepth_eq_distributionalCost {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (t : DecisionTree ι β) :
    detExpectedDepth μ t = t.distributionalCost (Cslib.Probability.PMF.toStdSimplex μ) := by
  rw [detExpectedDepth, DecisionTree.distributionalCost_eq_sum,
    Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
  simp

theorem detExpectedDepth_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (t : DecisionTree ι β) : 0 ≤ detExpectedDepth μ t :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

theorem randExpectedDepthTree_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (T : RandomizedDecisionTree ι β) :
    0 ≤ randExpectedDepthTree μ T :=
  Finset.sum_nonneg fun t _ ↦ mul_nonneg (T.weights_nonneg t) (detExpectedDepth_nonneg μ t)

@[simp] theorem randExpectedDepthTree_single {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (t : DecisionTree ι β) :
    randExpectedDepthTree μ (StdSimplex.single t) = detExpectedDepth μ t := by
  simp [randExpectedDepthTree]

theorem detDistError_eq_zero_of_computes {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) {f : (ι → Bool) → β} {t : DecisionTree ι β} (ht : t.Computes f) :
    detDistError μ f t = 0 := by
  rw [detDistError, ht.distributionalError_eq_zero]

theorem detDistError_eq_sum {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (t : DecisionTree ι β) :
    detDistError μ f t = ∑ x : ι → Bool, (μ x).toReal * if t.eval x = f x then 0 else 1 := by
  rw [detDistError, DecisionTree.distributionalError_eq_sum,
    Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
  simp

theorem detDistError_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (t : DecisionTree ι β) :
    0 ≤ detDistError μ f t :=
  DecisionTree.distributionalError_nonneg

theorem detDistError_le_one {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (t : DecisionTree ι β) :
    detDistError μ f t ≤ 1 := by
  classical
  rw [detDistError_eq_sum]
  exact Cslib.Probability.PMF.sum_mul_le μ _ 1 fun x ↦ by split_ifs <;> norm_num

theorem randDistError_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (T : RandomizedDecisionTree ι β) :
    0 ≤ randDistError μ f T :=
  Finset.sum_nonneg fun t _ ↦ mul_nonneg (T.weights_nonneg t) (detDistError_nonneg μ f t)

@[simp] theorem randDistError_single {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (t : DecisionTree ι β) :
    randDistError μ f (StdSimplex.single t) = detDistError μ f t := by
  simp [randDistError]

theorem randDistError_eq_sum_eval {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (T : RandomizedDecisionTree ι β) :
    randDistError μ f T = ∑ x : ι → Bool, (μ x).toReal * T.errorProb f x := by
  classical
  simp only [randDistError, detDistError_eq_sum, RandomizedDecisionTree.errorProb_eq_sum,
    Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

/-- Deterministic distributional expected query complexity
$\overline{\mathrm{Depth}}^\mu_{\mathrm{det}}(f, \varepsilon)$. -/
noncomputable def detDistDepth {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) : ℝ :=
  sInf {d : ℝ | ∃ t : DecisionTree ι β, detDistError μ f t ≤ ε ∧ detExpectedDepth μ t ≤ d}

/-- Randomized distributional expected query complexity
$\overline{\mathrm{Depth}}^\mu(f, \varepsilon)$. -/
noncomputable def distDepth {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) : ℝ :=
  sInf {d : ℝ | ∃ T : RandomizedDecisionTree ι β,
    randDistError μ f T ≤ ε ∧ randExpectedDepthTree μ T ≤ d}

/-- Expected-depth randomized query complexity $\overline{\mathrm{R}}(f, \varepsilon)$. -/
noncomputable def randExpectedDepth {ι β : Type*}
    (f : (ι → Bool) → β) (ε : ℝ) : ℝ :=
  sInf {d : ℝ | ∃ T : RandomizedDecisionTree ι β,
    T.Computes ε f ∧ ∀ x, T.expectedCost x ≤ d}

theorem randExpectedDepth_nonneg {ι β : Type*}
    (f : (ι → Bool) → β) (ε : ℝ) : 0 ≤ randExpectedDepth f ε :=
  Real.sInf_nonneg fun _ ⟨_, _, hd⟩ ↦
    RandomizedDecisionTree.expectedCost_nonneg.trans (hd fun _ ↦ false)

theorem randExpectedDepth_bddBelow {ι β : Type*}
    (f : (ι → Bool) → β) (ε : ℝ) :
    BddBelow {d : ℝ | ∃ T : RandomizedDecisionTree ι β,
      T.Computes ε f ∧ ∀ x, T.expectedCost x ≤ d} :=
  ⟨0, fun _ ⟨_, _, hd⟩ ↦ RandomizedDecisionTree.expectedCost_nonneg.trans (hd fun _ ↦ false)⟩

theorem randExpectedDepth_le {ι β : Type*}
    (f : (ι → Bool) → β) {ε d : ℝ} {T : RandomizedDecisionTree ι β}
    (hT : T.Computes ε f) (hd : ∀ x, T.expectedCost x ≤ d) :
    randExpectedDepth f ε ≤ d :=
  csInf_le (randExpectedDepth_bddBelow f ε) ⟨T, hT, hd⟩

theorem le_randExpectedDepth {ι β : Type*} [Finite ι]
    (f : (ι → Bool) → β) {ε c : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ T : RandomizedDecisionTree ι β, ∀ d : ℝ,
      T.Computes ε f → (∀ x, T.expectedCost x ≤ d) → c ≤ d) :
    c ≤ randExpectedDepth f ε := by
  cases nonempty_fintype ι
  have hne : {d : ℝ | ∃ T : RandomizedDecisionTree ι β,
      T.Computes ε f ∧ ∀ x, T.expectedCost x ≤ d}.Nonempty := by
    obtain ⟨t, ht, _⟩ := DecisionTree.exists_computes f
    refine ⟨t.depth, StdSimplex.single t, RandomizedDecisionTree.computes_single ht hε, fun x ↦ ?_⟩
    simpa using t.cost_le_depth x
  exact le_csInf hne fun d ⟨T, hT, hd⟩ ↦ hc T d hT hd

private theorem exists_det_zero_error {ι β : Type*} [Fintype ι] (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, t.Computes f ∧ t.depth ≤ Fintype.card ι :=
  DecisionTree.exists_computes f

theorem detDistDepth_nonempty {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε : ℝ} (hε : 0 ≤ ε) :
    {d : ℝ | ∃ t : DecisionTree ι β, detDistError μ f t ≤ ε ∧
      detExpectedDepth μ t ≤ d}.Nonempty := by
  obtain ⟨t, ht, _⟩ := exists_det_zero_error f
  refine ⟨detExpectedDepth μ t, t, ?_, le_rfl⟩
  rw [detDistError, ht.distributionalError_eq_zero]
  exact hε

theorem distDepth_nonempty {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε : ℝ} (hε : 0 ≤ ε) :
    {d : ℝ | ∃ T : RandomizedDecisionTree ι β,
      randDistError μ f T ≤ ε ∧ randExpectedDepthTree μ T ≤ d}.Nonempty := by
  obtain ⟨t, ht, _⟩ := exists_det_zero_error f
  refine ⟨detExpectedDepth μ t, StdSimplex.single t, ?_, by simp⟩
  rw [randDistError_single, detDistError, ht.distributionalError_eq_zero]
  exact hε

theorem distDepth_bddBelow {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) :
    BddBelow {d : ℝ | ∃ T : RandomizedDecisionTree ι β,
      randDistError μ f T ≤ ε ∧ randExpectedDepthTree μ T ≤ d} :=
  ⟨0, fun _ ⟨T, _, hd⟩ ↦ (randExpectedDepthTree_nonneg μ T).trans hd⟩

theorem detDistDepth_bddBelow {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) :
    BddBelow {d : ℝ | ∃ t : DecisionTree ι β,
      detDistError μ f t ≤ ε ∧ detExpectedDepth μ t ≤ d} :=
  ⟨0, fun _ ⟨t, _, hd⟩ ↦ (detExpectedDepth_nonneg μ t).trans hd⟩

theorem distDepth_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) : 0 ≤ distDepth μ f ε :=
  Real.sInf_nonneg fun _ ⟨T, _, hd⟩ ↦ (randExpectedDepthTree_nonneg μ T).trans hd

theorem detDistDepth_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) : 0 ≤ detDistDepth μ f ε :=
  Real.sInf_nonneg fun _ ⟨t, _, hd⟩ ↦ (detExpectedDepth_nonneg μ t).trans hd

theorem distDepth_le {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε : ℝ}
    {T : RandomizedDecisionTree ι β} (hT : randDistError μ f T ≤ ε) :
    distDepth μ f ε ≤ randExpectedDepthTree μ T :=
  csInf_le (distDepth_bddBelow μ f ε) ⟨T, hT, le_rfl⟩

theorem le_distDepth {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε c : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ T : RandomizedDecisionTree ι β,
      randDistError μ f T ≤ ε → c ≤ randExpectedDepthTree μ T) :
    c ≤ distDepth μ f ε :=
  le_csInf (distDepth_nonempty μ f hε) fun _ ⟨T, hT, hd⟩ ↦ (hc T hT).trans hd

theorem detDistDepth_le {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε : ℝ}
    {t : DecisionTree ι β} (ht : detDistError μ f t ≤ ε) :
    detDistDepth μ f ε ≤ detExpectedDepth μ t :=
  csInf_le (detDistDepth_bddBelow μ f ε) ⟨t, ht, le_rfl⟩

theorem le_detDistDepth {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε c : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ t : DecisionTree ι β,
      detDistError μ f t ≤ ε → c ≤ detExpectedDepth μ t) :
    c ≤ detDistDepth μ f ε :=
  le_csInf (detDistDepth_nonempty μ f hε) fun _ ⟨t, ht, hd⟩ ↦ (hc t ht).trans hd

theorem distDepth_antitone {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) :
    distDepth μ f ε₂ ≤ distDepth μ f ε₁ :=
  le_distDepth μ f hε₁ fun _ hT ↦ distDepth_le μ f (hT.trans h)

/-- Any Boolean-valued function has distributional depth `0` at error `ε ≥ 1/2`. -/
theorem distDepth_eq_zero_of_half_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → Bool) {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    distDepth μ f ε = 0 := by
  obtain ⟨T, hT, hd⟩ := QueryComplexity.exists_computes_depth_zero_of_le hε f
  refine le_antisymm ?_ (distDepth_nonneg μ f ε)
  have hcost : randExpectedDepthTree μ T = 0 := by
    refine le_antisymm ?_ (randExpectedDepthTree_nonneg μ T)
    refine Finset.sum_nonpos fun t ht ↦ ?_
    have hdt : t.depth = 0 :=
      Nat.le_zero.mp ((RandomizedDecisionTree.depth_le_depth ht).trans_eq hd)
    have hdet : detExpectedDepth μ t = 0 := by
      simp only [detExpectedDepth]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      have hc : t.cost x = 0 := Nat.le_zero.mp ((t.cost_le_depth x).trans_eq hdt)
      simp [hc]
    dsimp only
    rw [hdet, mul_zero]
  have herr : randDistError μ f T ≤ ε := by
    rw [randDistError_eq_sum_eval]
    exact Cslib.Probability.PMF.sum_mul_le μ _ ε hT
  exact (distDepth_le μ f herr).trans_eq hcost

/-- Any constant function has distributional depth `0` for every `ε ≥ 0`. -/
theorem distDepth_const {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (b : β) {ε : ℝ} (hε : 0 ≤ ε) :
    distDepth μ (fun _ ↦ b) ε = 0 := by
  refine le_antisymm ?_ (distDepth_nonneg μ _ ε)
  have hT : randDistError μ (fun _ ↦ b) (StdSimplex.single (.leaf b)) ≤ ε := by
    rw [randDistError_single, detDistError,
      (show (DecisionTree.leaf b : DecisionTree ι β).Computes (fun _ ↦ b) from
        fun _ ↦ rfl).distributionalError_eq_zero]
    exact hε
  have hd : randExpectedDepthTree μ (StdSimplex.single (.leaf b)) = 0 := by
    simp [detExpectedDepth]
  exact (distDepth_le μ _ hT).trans_eq hd

/-! ### -/

private theorem markov_gt_two_mul_lt_half {α : Type*}
    (p : StdSimplex ℝ α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) {c : ℝ} (hc : 0 ≤ c)
    (hmean : (p.weights.sum fun a w ↦ w * g a) ≤ c) :
    (p.weights.sum fun a w ↦ w * if 2 * c < g a then (1 : ℝ) else 0) < 1 / 2 := by
  classical
  set S := p.weights.support.filter fun a ↦ 2 * c < g a
  have hsum_eq : (p.weights.sum fun a w ↦ w * if 2 * c < g a then (1 : ℝ) else 0) =
      ∑ a ∈ S, p.weights a := by
    rw [Finsupp.sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> ring
  rw [hsum_eq]
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.sum_empty]
    norm_num
  · have hstrict : (∑ a ∈ S, p.weights a * (2 * c)) < ∑ a ∈ S, p.weights a * g a := by
      refine Finset.sum_lt_sum_of_nonempty hS fun a ha ↦ ?_
      have hmem := Finset.mem_filter.mp ha
      have hw : 0 < p.weights a :=
        (p.weights_nonneg a).lt_of_ne' (Finsupp.mem_support_iff.mp hmem.1)
      exact mul_lt_mul_of_pos_left hmem.2 hw
    have hle : (∑ a ∈ S, p.weights a * g a) ≤ p.weights.sum fun a w ↦ w * g a := by
      rw [Finsupp.sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ ↦
        mul_nonneg (p.weights_nonneg a) (hg a)
    have hlt : (∑ a ∈ S, p.weights a) * (2 * c) < c := by
      rw [Finset.sum_mul]
      exact hstrict.trans_le (hle.trans hmean)
    rcases hc.eq_or_lt with rfl | hcpos
    · simp at hlt
    · nlinarith

/-- For every function `f`, distribution `μ`, and `ε ≥ 0`,
$\overline{\mathrm{Depth}}^\mu(f, 2\varepsilon) \le
 \overline{\mathrm{Depth}}^\mu_{\mathrm{det}}(f, 2\varepsilon) \le
 2 \cdot \overline{\mathrm{Depth}}^\mu(f, \varepsilon)$. -/
theorem claim_connect_det_rand {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (f : (ι → Bool) → β) {ε : ℝ} (hε : 0 ≤ ε) :
    distDepth μ f (2 * ε) ≤ detDistDepth μ f (2 * ε) ∧
      detDistDepth μ f (2 * ε) ≤ 2 * distDepth μ f ε := by
  classical
  constructor
  · refine le_detDistDepth μ f (by linarith) fun t ht ↦ ?_
    exact (distDepth_le μ f (T := StdSimplex.single t) (by simpa using ht)).trans_eq (by simp)
  · have hgoal : detDistDepth μ f (2 * ε) / 2 ≤ distDepth μ f ε := by
      refine le_distDepth μ f hε fun T hT ↦ ?_
      set d := randExpectedDepthTree μ T
      have hd : 0 ≤ d := randExpectedDepthTree_nonneg μ T
      have hm1 := markov_gt_two_mul_lt_half T (detDistError μ f)
        (detDistError_nonneg μ f) hε hT
      have hm2 := markov_gt_two_mul_lt_half T (detExpectedDepth μ)
        (detExpectedDepth_nonneg μ) hd le_rfl
      have hbad : (T.weights.sum fun t w ↦
          w * if 2 * ε < detDistError μ f t ∨ 2 * d < detExpectedDepth μ t
              then (1 : ℝ) else 0) < 1 := by
        have hpt : ∀ t, (if 2 * ε < detDistError μ f t ∨ 2 * d < detExpectedDepth μ t
            then (1 : ℝ) else 0) ≤
            (if 2 * ε < detDistError μ f t then 1 else 0) +
            (if 2 * d < detExpectedDepth μ t then 1 else 0) := by
          intro t
          by_cases h1 : 2 * ε < detDistError μ f t <;>
            by_cases h2 : 2 * d < detExpectedDepth μ t <;> simp [h1, h2]
        have hsum : (T.weights.sum fun t w ↦
            w * if 2 * ε < detDistError μ f t ∨ 2 * d < detExpectedDepth μ t
                then (1 : ℝ) else 0) ≤
            (T.weights.sum fun t w ↦ w * if 2 * ε < detDistError μ f t then (1 : ℝ) else 0) +
            (T.weights.sum fun t w ↦ w * if 2 * d < detExpectedDepth μ t then (1 : ℝ) else 0) := by
          simp only [Finsupp.sum, ← Finset.sum_add_distrib, ← mul_add]
          exact Finset.sum_le_sum fun t _ ↦
            mul_le_mul_of_nonneg_left (hpt t) (T.weights_nonneg t)
        linarith
      have hex : ∃ t ∈ T.weights.support,
          detDistError μ f t ≤ 2 * ε ∧ detExpectedDepth μ t ≤ 2 * d := by
        by_contra! hall
        have h1 : (T.weights.sum fun t w ↦
            w * if 2 * ε < detDistError μ f t ∨ 2 * d < detExpectedDepth μ t
                then (1 : ℝ) else 0) = 1 := by
          calc (T.weights.sum fun t w ↦
                w * if 2 * ε < detDistError μ f t ∨ 2 * d < detExpectedDepth μ t
                    then (1 : ℝ) else 0)
              = ∑ t ∈ T.weights.support, T.weights t := by
                rw [Finsupp.sum]
                refine Finset.sum_congr rfl fun t ht ↦ ?_
                have hcase : 2 * ε < detDistError μ f t ∨ 2 * d < detExpectedDepth μ t := by
                  by_cases h1 : detDistError μ f t ≤ 2 * ε
                  · exact Or.inr (hall t ht h1)
                  · exact Or.inl (lt_of_not_ge h1)
                simp [hcase]
            _ = 1 := T.total
        linarith
      obtain ⟨t, -, hte, htd⟩ := hex
      have := detDistDepth_le μ f hte
      linarith
    linarith

/-- Any direct sum lower bound for randomized decision trees immediately implies one for
deterministic decision trees with a factor-of-2 loss in depth and error. -/
theorem cor_rand_to_det_DP {n k : ℕ} {f : (Fin n → Bool) → Bool}
    {μ : PMF (Fin n → Bool)} {ε δ M : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hDP : M * distDepth μ f δ ≤
      distDepth ((prodPMF μ k).map Function.uncurry) (directProductUncurry f k) ε) :
    M / 2 * detDistDepth μ f (2 * δ) ≤
      detDistDepth ((prodPMF μ k).map Function.uncurry) (directProductUncurry f k) ε := by
  have h2 := (claim_connect_det_rand μ f hδ).2
  have h3 : distDepth ((prodPMF μ k).map Function.uncurry) (directProductUncurry f k) ε ≤
      detDistDepth ((prodPMF μ k).map Function.uncurry) (directProductUncurry f k) ε := by
    refine le_detDistDepth _ _ hε fun t ht ↦ ?_
    exact (distDepth_le _ _ (T := StdSimplex.single t) (by simpa using ht)).trans_eq (by simp)
  nlinarith

/-! ### Block evaluation, threshold error, and threshold distributional depth -/

/-- Run a deterministic tree over `Fin k × Fin n` on a block input `X : Fin k → Fin n → Bool`. -/
@[expose] def evalBlock {n k : ℕ} {β : Type*}
    (t : DecisionTree (Fin k × Fin n) β) (X : Fin k → Fin n → Bool) : β :=
  t.eval (Function.uncurry X)

/-- Number of queries made by `t` on a block input `X : Fin k → Fin n → Bool`. -/
@[expose] def costBlock {n k : ℕ} {β : Type*}
    (t : DecisionTree (Fin k × Fin n) β) (X : Fin k → Fin n → Bool) : ℕ :=
  t.cost (Function.uncurry X)

/-- Root-to-leaf path taken by `t` on a block input `X : Fin k → Fin n → Bool`. -/
@[expose] def pathBlock {n k : ℕ} {β : Type*}
    (t : DecisionTree (Fin k × Fin n) β) (X : Fin k → Fin n → Bool) : List Bool :=
  t.path (Function.uncurry X)

/-- Probability that a deterministic tree makes strictly more than `thr` block mistakes on
$f^{\otimes k}$. -/
noncomputable def detThresholdError {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (thr : ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) : ℝ :=
  ∑ X : Fin k → Fin n → Bool,
    (prodPMF μ k X).toReal *
      if thr < (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) then 1 else 0

/-- Probability that a randomized tree makes strictly more than `thr` block mistakes on
$f^{\otimes k}$. -/
noncomputable def randThresholdError {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (thr : ℝ)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)) : ℝ :=
  T.weights.sum fun t w ↦ w * detThresholdError μ f thr t

/-- Expected depth of a deterministic tree on `prodPMF μ k`. -/
noncomputable def detProdExpectedDepth {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β) : ℝ :=
  ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal * (costBlock t X : ℝ)

/-- Expected depth of a randomized tree on `prodPMF μ k`. -/
noncomputable def randProdExpectedDepth {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (T : RandomizedDecisionTree (Fin k × Fin n) β) : ℝ :=
  T.weights.sum fun t w ↦ w * detProdExpectedDepth μ t

/-- Distributional error of a randomized tree on $f^{\otimes k}$ under $\mu^k$. -/
noncomputable def randProdDistError {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)) : ℝ :=
  randThresholdError μ f 0 T

/-- Distributional error of a randomized tree on $f^{\oplus k}$ under $\mu^k$. -/
noncomputable def randXorDistError {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool)
    (T : RandomizedDecisionTree (Fin k × Fin n) Bool) : ℝ :=
  T.weights.sum fun t w ↦ w *
    ∑ X : Fin k → Fin n → Bool,
      (prodPMF μ k X).toReal * if evalBlock t X = directSum f k X then 0 else 1

/-- Threshold distributional depth
$\overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, \varepsilon, t)$. -/
noncomputable def thresholdDistDepth {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) (thr : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool),
    randThresholdError μ f (thr : ℝ) T ≤ ε ∧ randProdExpectedDepth μ T ≤ d}

/-- Distributional depth $\overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, \varepsilon)$ on the
$k$-fold direct product. -/
noncomputable def prodDistDepth {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) : ℝ :=
  thresholdDistDepth μ f k ε 0

/-- Distributional depth $\overline{\mathrm{Depth}}^{\mu^k}(f^{\oplus k}, \varepsilon)$ on the
$k$-fold XOR. -/
noncomputable def xorDistDepth {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) : ℝ :=
  sInf {d : ℝ | ∃ T : RandomizedDecisionTree (Fin k × Fin n) Bool,
    randXorDistError μ f T ≤ ε ∧ randProdExpectedDepth μ T ≤ d}

@[simp] theorem evalBlock_leaf {n k : ℕ} {β : Type*}
    (b : β) (X : Fin k → Fin n → Bool) :
    evalBlock (.leaf b : DecisionTree (Fin k × Fin n) β) X = b := rfl

@[simp] theorem evalBlock_node {n k : ℕ} {β : Type*}
    (q : Fin k × Fin n) (t₀ t₁ : DecisionTree (Fin k × Fin n) β)
    (X : Fin k → Fin n → Bool) :
    evalBlock (.node q t₀ t₁) X = cond (X q.1 q.2) (evalBlock t₁ X) (evalBlock t₀ X) := rfl

theorem costBlock_eq_cost {n k : ℕ} {β : Type*}
    (t : DecisionTree (Fin k × Fin n) β) (X : Fin k → Fin n → Bool) :
    costBlock t X = t.cost (Function.uncurry X) := rfl

@[simp] theorem costBlock_leaf {n k : ℕ} {β : Type*}
    (b : β) (X : Fin k → Fin n → Bool) :
    costBlock (.leaf b : DecisionTree (Fin k × Fin n) β) X = 0 := rfl

@[simp] theorem pathBlock_leaf {n k : ℕ} {β : Type*}
    (b : β) (X : Fin k → Fin n → Bool) :
    pathBlock (.leaf b : DecisionTree (Fin k × Fin n) β) X = [] := rfl

@[simp] theorem pathBlock_node {n k : ℕ} {β : Type*}
    (q : Fin k × Fin n) (t₀ t₁ : DecisionTree (Fin k × Fin n) β)
    (X : Fin k → Fin n → Bool) :
    pathBlock (.node q t₀ t₁) X =
      X q.1 q.2 :: cond (X q.1 q.2) (pathBlock t₁ X) (pathBlock t₀ X) := rfl

theorem detThresholdError_eq_sum {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (thr : ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    detThresholdError μ f thr t = ∑ X : Fin k → Fin n → Bool,
      (prodPMF μ k X).toReal *
        if thr < (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) then 1 else 0 := by rfl

theorem randThresholdError_eq_sum {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (thr : ℝ)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    randThresholdError μ f thr T = T.weights.sum fun t w ↦ w * detThresholdError μ f thr t := by
  rfl

theorem detProdExpectedDepth_eq_sum {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β) :
    detProdExpectedDepth μ t =
      ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal * (costBlock t X : ℝ) := by rfl

@[simp] theorem detProdExpectedDepth_leaf {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (b : β) :
    detProdExpectedDepth μ (.leaf b : DecisionTree (Fin k × Fin n) β) = 0 := by
  simp [detProdExpectedDepth]

theorem randProdExpectedDepth_eq_sum {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    randProdExpectedDepth μ T = T.weights.sum fun t w ↦ w * detProdExpectedDepth μ t := by rfl

theorem randProdDistError_eq_randThresholdError {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    randProdDistError μ f T = randThresholdError μ f 0 T := by rfl

theorem randXorDistError_eq_sum {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool)
    (T : RandomizedDecisionTree (Fin k × Fin n) Bool) :
    randXorDistError μ f T = T.weights.sum fun t w ↦ w *
      ∑ X : Fin k → Fin n → Bool,
        (prodPMF μ k X).toReal * if evalBlock t X = directSum f k X then 0 else 1 := by rfl

theorem detThresholdError_nonneg {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (thr : ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    0 ≤ detThresholdError μ f thr t :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

theorem detProdExpectedDepth_nonneg {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β) :
    0 ≤ detProdExpectedDepth μ t :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

theorem randProdExpectedDepth_nonneg {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    0 ≤ randProdExpectedDepth μ T :=
  Finset.sum_nonneg fun t _ ↦ mul_nonneg (T.weights_nonneg t) (detProdExpectedDepth_nonneg μ t)

theorem thresholdDistDepth_nonempty {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (thr : ℕ) :
    {d : ℝ | ∃ T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool),
      randThresholdError μ f (thr : ℝ) T ≤ ε ∧ randProdExpectedDepth μ T ≤ d}.Nonempty := by
  obtain ⟨t, ht, _⟩ := exists_det_zero_error (directProductUncurry f k)
  refine ⟨detProdExpectedDepth μ t, StdSimplex.single t, ?_, by simp [randProdExpectedDepth]⟩
  have hzero : detThresholdError μ f (thr : ℝ) t = 0 := by
    refine Finset.sum_eq_zero fun X _ ↦ ?_
    have hev : evalBlock t X = directProduct f k X := ht (Function.uncurry X)
    have hhd : hammingDist (evalBlock t X) (directProduct f k X) = 0 :=
      hammingDist_eq_zero_iff.mpr hev
    simp [hhd]
  simpa [randThresholdError, hzero] using hε

theorem thresholdDistDepth_bddBelow {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) (thr : ℕ) :
    BddBelow {d : ℝ | ∃ T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool),
      randThresholdError μ f (thr : ℝ) T ≤ ε ∧ randProdExpectedDepth μ T ≤ d} :=
  ⟨0, fun _ ⟨T, _, hd⟩ ↦ (randProdExpectedDepth_nonneg μ T).trans hd⟩

theorem thresholdDistDepth_nonneg {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) (thr : ℕ) :
    0 ≤ thresholdDistDepth μ f k ε thr :=
  Real.sInf_nonneg fun _ ⟨T, _, hd⟩ ↦ (randProdExpectedDepth_nonneg μ T).trans hd

theorem le_thresholdDistDepth {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε c : ℝ} (hε : 0 ≤ ε) (thr : ℕ)
    (hc : ∀ T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool),
      randThresholdError μ f (thr : ℝ) T ≤ ε → c ≤ randProdExpectedDepth μ T) :
    c ≤ thresholdDistDepth μ f k ε thr :=
  le_csInf (thresholdDistDepth_nonempty μ f k hε thr) fun _ ⟨T, hT, hd⟩ ↦ (hc T hT).trans hd

theorem thresholdDistDepth_le {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ} (thr : ℕ)
    {T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)}
    (hT : randThresholdError μ f (thr : ℝ) T ≤ ε) :
    thresholdDistDepth μ f k ε thr ≤ randProdExpectedDepth μ T :=
  csInf_le (thresholdDistDepth_bddBelow μ f k ε thr) ⟨T, hT, le_rfl⟩

theorem thresholdDistDepth_antitone_error {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) (thr : ℕ) :
    thresholdDistDepth μ f k ε₂ thr ≤ thresholdDistDepth μ f k ε₁ thr :=
  le_thresholdDistDepth μ f k hε₁ thr fun _ hT ↦ thresholdDistDepth_le μ f k thr (hT.trans h)

theorem thresholdDistDepth_antitone_threshold {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    thresholdDistDepth μ f k ε t₂ ≤ thresholdDistDepth μ f k ε t₁ := by
  refine le_thresholdDistDepth μ f k hε t₁ fun T hT ↦ thresholdDistDepth_le μ f k t₂ ?_
  refine (Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)).trans hT
  refine Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt (Nat.cast_le.mpr ht) h1) h2
  · exact zero_le_one
  · exact le_rfl

theorem prodDistDepth_nonneg {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) : 0 ≤ prodDistDepth μ f k ε :=
  thresholdDistDepth_nonneg μ f k ε 0

theorem prodDistDepth_le {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ}
    {T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)}
    (hT : randProdDistError μ f T ≤ ε) :
    prodDistDepth μ f k ε ≤ randProdExpectedDepth μ T :=
  thresholdDistDepth_le μ f k 0 (by simpa [randProdDistError_eq_randThresholdError] using hT)

theorem prodDistDepth_antitone_error {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) :
    prodDistDepth μ f k ε₂ ≤ prodDistDepth μ f k ε₁ :=
  thresholdDistDepth_antitone_error μ f k hε₁ h 0

theorem thresholdDistDepth_le_prodDistDepth {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (thr : ℕ) :
    thresholdDistDepth μ f k ε thr ≤ prodDistDepth μ f k ε :=
  thresholdDistDepth_antitone_threshold μ f k hε (Nat.zero_le thr)

theorem xorDistDepth_nonempty {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    {d : ℝ | ∃ T : RandomizedDecisionTree (Fin k × Fin n) Bool,
      randXorDistError μ f T ≤ ε ∧ randProdExpectedDepth μ T ≤ d}.Nonempty := by
  obtain ⟨t, ht, _⟩ := exists_det_zero_error (directSumUncurry f k)
  refine ⟨detProdExpectedDepth μ t, StdSimplex.single t, ?_, by simp [randProdExpectedDepth]⟩
  have hzero : (∑ X : Fin k → Fin n → Bool,
      (prodPMF μ k X).toReal * if evalBlock t X = directSum f k X then 0 else 1) = 0 := by
    refine Finset.sum_eq_zero fun X _ ↦ ?_
    have hev : evalBlock t X = directSum f k X := by
      simpa [evalBlock, directSumUncurry] using ht (Function.uncurry X)
    simp [hev]
  rw [randXorDistError, StdSimplex.weights_single, Finsupp.sum_single_index (zero_mul _),
    one_mul, hzero]
  exact hε

theorem xorDistDepth_bddBelow {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) :
    BddBelow {d : ℝ | ∃ T : RandomizedDecisionTree (Fin k × Fin n) Bool,
      randXorDistError μ f T ≤ ε ∧ randProdExpectedDepth μ T ≤ d} :=
  ⟨0, fun _ ⟨T, _, hd⟩ ↦ (randProdExpectedDepth_nonneg μ T).trans hd⟩

theorem xorDistDepth_nonneg {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) (ε : ℝ) : 0 ≤ xorDistDepth μ f k ε :=
  Real.sInf_nonneg fun _ ⟨T, _, hd⟩ ↦ (randProdExpectedDepth_nonneg μ T).trans hd

theorem le_xorDistDepth {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε c : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ T : RandomizedDecisionTree (Fin k × Fin n) Bool,
      randXorDistError μ f T ≤ ε → c ≤ randProdExpectedDepth μ T) :
    c ≤ xorDistDepth μ f k ε :=
  le_csInf (xorDistDepth_nonempty μ f k hε) fun _ ⟨T, hT, hd⟩ ↦ (hc T hT).trans hd

theorem xorDistDepth_le {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (k : ℕ) {ε : ℝ}
    {T : RandomizedDecisionTree (Fin k × Fin n) Bool}
    (hT : randXorDistError μ f T ≤ ε) :
    xorDistDepth μ f k ε ≤ randProdExpectedDepth μ T :=
  csInf_le (xorDistDepth_bddBelow μ f k ε) ⟨T, hT, le_rfl⟩

/-! ### Hardcore measures, canonical leaf distributions, density, and advantage -/

/-- `H : (Fin n → Bool) → ℝ` is a `(γ, d)`-hardcore measure for `f` w.r.t. `μ` of density `δ` if
`H x ∈ [0, 1]`, `𝔼_{x ~ μ}[H x] = δ`, and every randomized decision tree `T` with expected depth
at most `d` satisfies `𝔼_{x ~ μ, t ~ T}[f(x) t(x) H(x)] ≤ γ * δ`. -/
structure IsHardcoreMeasure {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (γ d δ : ℝ) (H : (Fin n → Bool) → ℝ) : Prop where
  mem_Icc : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1
  density : (∑ x : Fin n → Bool, (μ x).toReal * H x) = δ
  correlation_le : ∀ T : RandomizedDecisionTree (Fin n) Bool,
    randExpectedDepthTree μ T ≤ d →
      (T.weights.sum fun t w ↦
        w * ∑ x : Fin n → Bool, (μ x).toReal * (signBool (f x) * signBool (t.eval x) * H x)) ≤
      γ * δ

/-- The canonical leaf distribution $\mu^k(T)$ over pairs `(t, ℓ)` of a deterministic tree drawn
from `T` and a root-to-leaf path `ℓ`. -/
noncomputable def leafDist {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    PMF (DecisionTree (Fin k × Fin n) β × List Bool) :=
  (Cslib.Probability.PMF.ofStdSimplex T).bind fun t ↦
    (prodPMF μ k).map fun X ↦ (t, pathBlock t X)

/-- Expectation of a leaf function `g t ℓ` under the canonical leaf distribution `μ^k(T)`. -/
noncomputable def leafExpect {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (T : RandomizedDecisionTree (Fin k × Fin n) β)
    (g : DecisionTree (Fin k × Fin n) β → List Bool → ℝ) : ℝ :=
  T.weights.sum fun t w ↦ w * ∑ X : Fin k → Fin n →
    Bool, (prodPMF μ k X).toReal * g t (pathBlock t X)

/-- Conditional distribution of `X ~ μ^k` given that `t` follows path `ℓ`. -/
noncomputable def leafCondPMF {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) :
    PMF (Fin k → Fin n → Bool) :=
  Cslib.Probability.PMF.conditionalSnd
    ((prodPMF μ k).map fun X ↦ (pathBlock t X, X)) ℓ

/-- Hardcore density $\mathrm{Dens}_H((t, \ell), i)$ in block `i`. -/
noncomputable def hardcoreDensityAt {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) (i : Fin k) : ℝ :=
  ∑ X : Fin k → Fin n → Bool, (leafCondPMF μ t ℓ X).toReal * H (X i)

/-- Total hardcore density $\mathrm{Dens}_H((t, \ell)) = \sum_i \mathrm{Dens}_H((t, \ell), i)$. -/
noncomputable def hardcoreDensity {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) : ℝ :=
  ∑ i : Fin k, hardcoreDensityAt μ H t ℓ i

/-- Hardcore advantage $\mathrm{Adv}_H((t, \ell), i)$ in block `i`. -/
noncomputable def hardcoreAdvantageAt {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) (i : Fin k) : ℝ :=
  |∑ X : Fin k → Fin n → Bool,
    (leafCondPMF μ t ℓ X).toReal *
      (signBool (f (X i)) * signBool (evalBlock t X i) * H (X i))|

/-- Total hardcore advantage $\mathrm{Adv}_H((t, \ell)) = \sum_i \mathrm{Adv}_H((t, \ell), i)$. -/
noncomputable def hardcoreAdvantage {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) : ℝ :=
  ∑ i : Fin k, hardcoreAdvantageAt μ f H t ℓ i

theorem leafCondPMF_eq {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) :
    leafCondPMF μ t ℓ = Cslib.Probability.PMF.conditionalSnd
      ((prodPMF μ k).map fun X ↦ (pathBlock t X, X)) ℓ := by rfl

theorem hardcoreAdvantageAt_eq_abs {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) (i : Fin k) :
    hardcoreAdvantageAt μ f H t ℓ i =
      |∑ X : Fin k → Fin n → Bool,
        (leafCondPMF μ t ℓ X).toReal *
          (signBool (f (X i)) * signBool (evalBlock t X i) * H (X i))| := by rfl

/-- Version of `Cslib.Probability.PMF.sum_conditionalSnd_map` requiring only `[Fintype α]`
(no `[Finite β]` needed, since the image of `f` is automatically finite). -/
theorem sum_conditionalSnd_map_fintype {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) (score : β → α → ℝ) :
    (∑ x, (p x).toReal * ∑ y,
      (Cslib.Probability.PMF.conditionalSnd (p.map fun a ↦ (f a, a)) (f x) y).toReal *
        score (f x) y) =
      ∑ x, (p x).toReal * score (f x) x := by
  classical
  let S : Finset β := Finset.univ.image f
  let g : α → S := fun a ↦ ⟨f a, Finset.mem_image_of_mem f (Finset.mem_univ a)⟩
  have hcond (x : α) (hx : p x ≠ 0) :
      Cslib.Probability.PMF.conditionalSnd (p.map fun a ↦ (f a, a)) (f x) =
      Cslib.Probability.PMF.conditionalSnd (p.map fun a ↦ (g a, a)) (g x) := by
    apply Cslib.Probability.PMF.conditionalSnd_eq_of_scaled_slices _ _ (f x) (g x) 1 1
    · rw [PMF.map_comp]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x, (PMF.mem_support_iff _ _).mpr hx, rfl⟩
    · exact one_ne_zero
    · exact ENNReal.one_ne_top
    · intro y
      simp only [one_mul, PMF.map_apply, tsum_fintype]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      have hiff : (f x, y) = (f a, a) ↔ (g x, y) = (g a, a) := by
        simp [g, Subtype.ext_iff]
      simp [hiff]
  have h := Cslib.Probability.PMF.sum_conditionalSnd_map p g (fun s y ↦ score s.1 y)
  refine (Finset.sum_congr rfl fun x _ ↦ ?_).trans h
  by_cases hx : p x = 0
  · simp [hx]
  · rw [hcond x hx]

theorem sum_leafCondPMF_eq {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β)
    (score : List Bool → (Fin k → Fin n → Bool) → ℝ) :
    (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
      ∑ Y : Fin k → Fin n → Bool,
        (leafCondPMF μ t (pathBlock t X) Y).toReal * score (pathBlock t X) Y) =
      ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal * score (pathBlock t X) X :=
  sum_conditionalSnd_map_fintype (prodPMF μ k) (pathBlock t) score

theorem leafExpect_eq_sum {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (T : RandomizedDecisionTree (Fin k × Fin n) β)
    (g : DecisionTree (Fin k × Fin n) β → List Bool → ℝ) :
    leafExpect μ T g = T.weights.sum fun t w ↦
      w * ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal * g t (pathBlock t X) := by rfl

@[simp] theorem leafExpect_single {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β)
    (g : DecisionTree (Fin k × Fin n) β → List Bool → ℝ) :
    leafExpect μ (StdSimplex.single t) g =
      ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal * g t (pathBlock t X) := by
  simp [leafExpect]

theorem hardcoreDensityAt_eq_sum {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) (i : Fin k) :
    hardcoreDensityAt μ H t ℓ i =
      ∑ X : Fin k → Fin n → Bool, (leafCondPMF μ t ℓ X).toReal * H (X i) := by rfl

theorem hardcoreDensity_eq_sum {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) :
    hardcoreDensity μ H t ℓ = ∑ i : Fin k, hardcoreDensityAt μ H t ℓ i := by rfl

theorem hardcoreAdvantage_eq_sum {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) :
    hardcoreAdvantage μ f H t ℓ = ∑ i : Fin k, hardcoreAdvantageAt μ f H t ℓ i := by rfl

@[simp] theorem hardcoreAdvantage_zero {n : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin 0 × Fin n) (Fin 0 → Bool)) (ℓ : List Bool) :
    hardcoreAdvantage μ f H t ℓ = 0 := by
  simp [hardcoreAdvantage]

theorem hardcoreDensityAt_mem_Icc {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) (i : Fin k) :
    hardcoreDensityAt μ H t ℓ i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Finset.sum_nonneg fun X _ ↦ mul_nonneg ENNReal.toReal_nonneg (hH (X i)).1, ?_⟩
  exact Cslib.Probability.PMF.sum_mul_le (leafCondPMF μ t ℓ) _ 1 fun X ↦ (hH (X i)).2

theorem hardcoreDensity_nonneg {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) :
    0 ≤ hardcoreDensity μ H t ℓ :=
  Finset.sum_nonneg fun i _ ↦ (hardcoreDensityAt_mem_Icc μ hH t ℓ i).1

theorem hardcoreAdvantageAt_nonneg {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) (i : Fin k) :
    0 ≤ hardcoreAdvantageAt μ f H t ℓ i :=
  abs_nonneg _

theorem hardcoreAdvantageAt_le_densityAt {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) (i : Fin k) :
    hardcoreAdvantageAt μ f H t ℓ i ≤ hardcoreDensityAt μ H t ℓ i := by
  unfold hardcoreAdvantageAt hardcoreDensityAt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun X _ ↦ ?_
  rw [abs_mul, abs_mul, abs_mul, abs_signBool, abs_signBool,
    abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (hH (X i)).1]
  simp

theorem hardcoreAdvantage_nonneg {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) :
    0 ≤ hardcoreAdvantage μ f H t ℓ :=
  Finset.sum_nonneg fun i _ ↦ hardcoreAdvantageAt_nonneg μ f H t ℓ i

theorem hardcoreAdvantage_le_density {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) (ℓ : List Bool) :
    hardcoreAdvantage μ f H t ℓ ≤ hardcoreDensity μ H t ℓ :=
  Finset.sum_le_sum fun i _ ↦ hardcoreAdvantageAt_le_densityAt μ f hH t ℓ i

/-! ### -/

private theorem exists_blockPred_pathBlock {n k : ℕ} {β : Type*}
    (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool) :
    ∃ S : Fin k → (Fin n → Bool) → Prop,
      (∀ X : Fin k → Fin n → Bool, pathBlock t X = ℓ ↔ ∀ i, S i (X i)) ∨
        (∀ X : Fin k → Fin n → Bool, pathBlock t X ≠ ℓ) := by
  classical
  induction t generalizing ℓ with
  | leaf b =>
    cases ℓ with
    | nil =>
      exact ⟨fun _ _ ↦ True, Or.inl fun _ ↦ by simp [pathBlock, DecisionTree.path]⟩
    | cons a l =>
      exact ⟨fun _ _ ↦ False, Or.inr fun _ ↦ by simp [pathBlock, DecisionTree.path]⟩
  | node q t₀ t₁ ih₀ ih₁ =>
    rcases q with ⟨i₀, j₀⟩
    cases ℓ with
    | nil =>
      exact ⟨fun _ _ ↦ False, Or.inr fun _ ↦ by simp [pathBlock, DecisionTree.path]⟩
    | cons a l =>
      cases a with
      | false =>
        obtain ⟨S, hS | hS⟩ := ih₀ l
        · refine ⟨fun i x ↦ if h : i = i₀ then x j₀ = false ∧ S i x else S i x, Or.inl fun X ↦ ?_⟩
          have hcons : pathBlock (.node (i₀, j₀) t₀ t₁) X = false :: l ↔
              X i₀ j₀ = false ∧ pathBlock t₀ X = l := by
            simp only [pathBlock, DecisionTree.path, Function.uncurry_apply_pair, List.cons.injEq]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨h1, by simpa [h1] using h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, by simpa [h1] using h2⟩
          rw [hcons, hS X]
          constructor
          · rintro ⟨hx, hall⟩ i
            split_ifs with h
            · subst h; exact ⟨hx, hall i⟩
            · exact hall i
          · intro hall
            refine ⟨?_, fun i ↦ ?_⟩
            · have hi := hall i₀; simp only [dite_true] at hi; exact hi.1
            · have hi := hall i
              by_cases h : i = i₀
              · subst h; simp only [dite_true] at hi; exact hi.2
              · simpa [h] using hi
        · refine ⟨fun _ _ ↦ False, Or.inr fun X hpath ↦ ?_⟩
          simp only [pathBlock, DecisionTree.path, Function.uncurry_apply_pair,
            List.cons.injEq] at hpath
          exact hS X (by simpa [pathBlock, hpath.1] using hpath.2)
      | true =>
        obtain ⟨S, hS | hS⟩ := ih₁ l
        · refine ⟨fun i x ↦ if h : i = i₀ then x j₀ = true ∧ S i x else S i x, Or.inl fun X ↦ ?_⟩
          have hcons : pathBlock (.node (i₀, j₀) t₀ t₁) X = true :: l ↔
              X i₀ j₀ = true ∧ pathBlock t₁ X = l := by
            simp only [pathBlock, DecisionTree.path, Function.uncurry_apply_pair, List.cons.injEq]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨h1, by simpa [h1] using h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, by simpa [h1] using h2⟩
          rw [hcons, hS X]
          constructor
          · rintro ⟨hx, hall⟩ i
            split_ifs with h
            · subst h; exact ⟨hx, hall i⟩
            · exact hall i
          · intro hall
            refine ⟨?_, fun i ↦ ?_⟩
            · have hi := hall i₀; simp only [dite_true] at hi; exact hi.1
            · have hi := hall i
              by_cases h : i = i₀
              · subst h; simp only [dite_true] at hi; exact hi.2
              · simpa [h] using hi
        · refine ⟨fun _ _ ↦ False, Or.inr fun X hpath ↦ ?_⟩
          simp only [pathBlock, DecisionTree.path, Function.uncurry_apply_pair,
            List.cons.injEq] at hpath
          exact hS X (by simpa [pathBlock, hpath.1] using hpath.2)

/-- For any deterministic tree `t : DecisionTree (Fin k × Fin n) β` and reachable leaf `ℓ`, the
distribution of `X ~ μ^k` conditioned on `X` reaching `ℓ` is a product distribution over the `k`
blocks. -/
theorem claim_leaf_product {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β) (ℓ : List Bool)
    (hℓ : ℓ ∈ ((prodPMF μ k).map (pathBlock t)).support) :
    ∃ ν : Fin k → PMF (Fin n → Bool),
      leafCondPMF μ t ℓ = Cslib.Probability.PMF.pi ν := by
  classical
  obtain ⟨S, hS | hS⟩ := exists_blockPred_pathBlock t ℓ
  · have hmarg_eq : ((prodPMF μ k).map (pathBlock t)) ℓ =
        ∏ i : Fin k, ∑ x : Fin n → Bool, if S i x then μ x else 0 := by
      rw [PMF.map_apply, tsum_fintype]
      have hfactor : ∀ X : Fin k → Fin n → Bool,
          (if ℓ = pathBlock t X then prodPMF μ k X else 0) =
            ∏ i : Fin k, if S i (X i) then μ (X i) else 0 := by
        intro X
        rw [prodPMF_apply]
        by_cases hX : ∀ i, S i (X i)
        · have hp : ℓ = pathBlock t X := ((hS X).mpr hX).symm
          simp only [hp, ite_true]
          exact Finset.prod_congr rfl fun i _ ↦ by simp [hX i]
        · have hp : ℓ ≠ pathBlock t X := fun heq ↦ hX ((hS X).mp heq.symm)
          rw [ite_eq_right hp]
          obtain ⟨i, hi⟩ := not_forall.mp hX
          exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm
      refine (Finset.sum_congr rfl fun X _ ↦ ?_).trans
        (Fintype.prod_sum fun i x ↦ if S i x then μ x else 0).symm
      rw [← hfactor X]
      congr 1
    have hmarg_ne : ((prodPMF μ k).map (pathBlock t)) ℓ ≠ 0 :=
      (PMF.mem_support_iff _ _).mp hℓ
    have hZ_ne : ∀ i : Fin k, (∑ x : Fin n → Bool, if S i x then μ x else 0) ≠ 0 := by
      intro i hi
      apply hmarg_ne
      rw [hmarg_eq]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hZ_top : ∀ i : Fin k, (∑ x : Fin n → Bool, if S i x then μ x else 0) ≠ ⊤ := by
      intro i
      refine ne_of_lt ((Finset.sum_le_sum (g := fun x ↦ μ x) fun x _ ↦ ?_).trans_lt ?_)
      · split_ifs
        · exact le_rfl
        · exact zero_le
      · have hsum1 : ∑ x : Fin n → Bool, μ x = 1 := by
          simpa [tsum_fintype] using μ.tsum_coe
        rw [hsum1]
        exact ENNReal.one_lt_top
    let ν : Fin k → PMF (Fin n → Bool) := fun i ↦
      PMF.ofFintype (fun x ↦ (if S i x then μ x else 0) /
          (∑ y : Fin n → Bool, if S i y then μ y else 0)) (by
        rw [← ENNReal.sum_div, ENNReal.div_self (hZ_ne i) (hZ_top i)])
    refine ⟨ν, ?_⟩
    ext X
    have hjoint : (((prodPMF μ k).map fun Y ↦ (pathBlock t Y, Y)) (ℓ, X)) =
        if pathBlock t X = ℓ then prodPMF μ k X else 0 := by
      rw [PMF.map_apply, tsum_eq_single X]
      · simp [eq_comm]
      · intro Y hY
        simp [hY.symm]
    have hmapfst : (((prodPMF μ k).map fun Y ↦ (pathBlock t Y, Y)).map Prod.fst) =
        (prodPMF μ k).map (pathBlock t) := by
      rw [PMF.map_comp]
      rfl
    have hsupp : ℓ ∈ (((prodPMF μ k).map fun Y ↦ (pathBlock t Y, Y)).map Prod.fst).support := by
      rwa [hmapfst]
    rw [leafCondPMF, Cslib.Probability.PMF.conditionalSnd_apply _ ℓ hsupp X, hmapfst, hjoint,
      hmarg_eq, Cslib.Probability.PMF.pi_apply]
    simp only [ν, PMF.ofFintype_apply, ENNReal.prod_div_distrib_of_ne_top (fun i _ ↦ hZ_top i)]
    congr 1
    rw [prodPMF_apply]
    by_cases hX : ∀ i, S i (X i)
    · have hp : pathBlock t X = ℓ := (hS X).mpr hX
      simp only [hp, ite_true]
      exact Finset.prod_congr rfl fun i _ ↦ by simp [hX i]
    · have hp : pathBlock t X ≠ ℓ := fun heq ↦ hX ((hS X).mp heq)
      simp only [hp, ite_false]
      obtain ⟨i, hi⟩ := not_forall.mp hX
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  · exfalso
    have hzero : ((prodPMF μ k).map (pathBlock t)) ℓ = 0 := by
      rw [PMF.map_apply, tsum_fintype]
      refine Finset.sum_eq_zero fun X _ ↦ ?_
      simp [(hS X).symm]
    exact (PMF.mem_support_iff _ _).mp hℓ hzero

/-- Given `t : DecisionTree (Fin k × Fin n) Bool`, the $k$-wise product tree $\tilde{t}$ keeps the
internal structure of `t` and labels each leaf `ℓ` with
$\ell_i = \mathrm{sign}(\mathbb{E}_{X \sim \mu^k}[f(X^{(i)}) \mid X\text{ reaches }\ell])$. -/
noncomputable def productTreeAux {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool)
    (tOrig : DecisionTree (Fin k × Fin n) Bool) :
    List Bool → DecisionTree (Fin k × Fin n) Bool →
      DecisionTree (Fin k × Fin n) (Fin k → Bool)
  | revPath, .leaf _ =>
    .leaf fun i ↦
      decide (0 ≤ ∑ X : Fin k → Fin n → Bool,
        (leafCondPMF μ tOrig revPath.reverse X).toReal * signBool (f (X i)))
  | revPath, .node q t₀ t₁ =>
    .node q (productTreeAux μ f tOrig (false :: revPath) t₀)
      (productTreeAux μ f tOrig (true :: revPath) t₁)

/-- The $k$-wise product tree $\tilde{t}$ associated to `t : DecisionTree (Fin k × Fin n) Bool`. -/
noncomputable def productTree {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool)
    (t : DecisionTree (Fin k × Fin n) Bool) :
    DecisionTree (Fin k × Fin n) (Fin k → Bool) :=
  productTreeAux μ f t [] t

theorem cost_productTreeAux {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (tOrig : DecisionTree (Fin k × Fin n) Bool)
    (revPath : List Bool) (t : DecisionTree (Fin k × Fin n) Bool)
    (x : Fin k × Fin n → Bool) :
    (productTreeAux μ f tOrig revPath t).cost x = t.cost x := by
  induction t generalizing revPath with
  | leaf _ => rfl
  | node q t₀ t₁ ih₀ ih₁ =>
    simp only [productTreeAux, DecisionTree.cost_node]
    cases x q <;> simp [ih₀, ih₁]

theorem cost_productTree {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (t : DecisionTree (Fin k × Fin n) Bool)
    (x : Fin k × Fin n → Bool) :
    (productTree μ f t).cost x = t.cost x :=
  cost_productTreeAux μ f t [] t x

theorem eval_productTreeAux {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (tOrig : DecisionTree (Fin k × Fin n) Bool)
    (revPath : List Bool) (t : DecisionTree (Fin k × Fin n) Bool)
    (X : Fin k → Fin n → Bool) (i : Fin k) :
    (evalBlock (productTreeAux μ f tOrig revPath t) X i = true) ↔
      (0 ≤ ∑ Y : Fin k → Fin n → Bool,
        (leafCondPMF μ tOrig (revPath.reverse ++ pathBlock t X) Y).toReal *
          signBool (f (Y i))) := by
  induction t generalizing revPath with
  | leaf _ =>
    simp [productTreeAux, evalBlock, pathBlock, DecisionTree.path]
  | node q t₀ t₁ ih₀ ih₁ =>
    simp only [productTreeAux, evalBlock, DecisionTree.eval_node, pathBlock, DecisionTree.path]
    cases h : Function.uncurry X q
    · simpa [evalBlock, pathBlock, List.reverse_cons, List.append_assoc] using
        ih₀ (false :: revPath)
    · simpa [evalBlock, pathBlock, List.reverse_cons, List.append_assoc] using
        ih₁ (true :: revPath)

theorem eval_productTree {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (t : DecisionTree (Fin k × Fin n) Bool)
    (X : Fin k → Fin n → Bool) (i : Fin k) :
    (evalBlock (productTree μ f t) X i = true) ↔
      (0 ≤ ∑ Y : Fin k → Fin n → Bool,
        (leafCondPMF μ t (pathBlock t X) Y).toReal * signBool (f (Y i))) := by
  unfold productTree
  simpa using eval_productTreeAux μ f t [] t X i

end CslibFrontier.Computability.QueryComplexity.DirectSum

end
