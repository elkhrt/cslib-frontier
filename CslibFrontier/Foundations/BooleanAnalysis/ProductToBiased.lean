module

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.Product
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi

import CslibFrontier.Probability.StatisticalDistance.Product
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Product-to-Biased Boolean Encoding for Monotone Coalitional Influence

This module develops $p$-biased resampling influence and coalitional forcing on the Boolean cube,
together with the max-selector reduction from monotone Boolean functions over finite ordered
alphabets `Fin r` under the uniform product distribution to monotone Boolean functions on the cube
under the independent $p$-biased product distribution (`p ∈ (0, 1 / 2)`).

Every nonconstant threshold of the monotone max-selector `maxSelector` reduces to an unstructured
disjunction of input bits, whose total $p$-biased influence is at most twice its acceptance
probability. Choosing coordinate multiplicities via powers of `1 - p` approximates the uniform
distribution on `Fin r` within `2 * p` in `ℓ_∞`, yielding a monotone cube encoding with controlled
expectation shift `p * r * n`, total $p$-biased influence bounded in terms of `0`-directed
influence, and non-increasing coalition size under coordinate block projection.

## Main definitions

* `CslibFrontier.BooleanAnalysis.bernoulliProb` and
  `CslibFrontier.BooleanAnalysis.bernoulliEventProb`: point mass and event probability under the
  independent $p$-biased product law on `ι → Bool`.
* `CslibFrontier.BooleanAnalysis.pBiasedCoordInfluence`,
  `CslibFrontier.BooleanAnalysis.pBiasedTotalInfluence`, and
  `CslibFrontier.BooleanAnalysis.pBiasedCoalitionProb`: resampling coordinate influence, total
  influence, and coalitional forcing probability on `(ι → Bool) → Bool`.
* `CslibFrontier.BooleanAnalysis.maxSelector`: monotone max-selector map `(Fin ℓ → Bool) → Fin r`
  sending `y` to `a (max {j | y j = true})` when `y ≠ 0` and `0` otherwise.

## Main results

* `CslibFrontier.BooleanAnalysis.pBiasedCoordInfluence_eq_two_mul_pivotal`: relates resampling
  $p$-biased influence to `2 * p * (1 - p)` times the pivotal probability.
* `CslibFrontier.BooleanAnalysis.pBiasedTotalInfluence_or_subset_le`: bounds the total $p$-biased
  influence of any subset disjunction by twice its acceptance probability.
* `CslibFrontier.BooleanAnalysis.pBiasedCoalitionProb_eq_of_monotone`: unanimous-vote formula for
  monotone $p$-biased coalitional forcing.
* `CslibFrontier.BooleanAnalysis.le_maxSelector_iff_exists`: every positive threshold of
  `maxSelector` is equivalent to a disjunction over a subset of coordinates.
* `CslibFrontier.BooleanAnalysis.exists_monotone_seq_approx_uniform`: constructs a monotone
  sequence `a : Fin ℓ → Fin r` whose `p`-biased pushforward approximates the uniform distribution
  within `2 * p` pointwise.
* `CslibFrontier.BooleanAnalysis.exists_monotone_pBiased_encoding`: complete monotone reduction
  from `(Fin n → Fin r) → Bool` under the uniform product measure to `(Fin m → Bool) → Bool` under
  the $p$-biased product measure.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Finset
open scoped Cslib.Probability.PMF ENNReal

section BiasedCube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Point mass `∏ i, p^{x_i} (1 - p)^{1 - x_i}` of `x : ι → Bool` under the independent $p$-biased
Bernoulli product law. -/
noncomputable def bernoulliProb (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then p else 1 - p

omit [DecidableEq ι] in
theorem bernoulliProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ bernoulliProb p x := by
  rw [bernoulliProb]
  refine prod_nonneg fun i _ ↦ ?_
  cases x i
  · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
  · simp only [↓reduceIte]; exact hp0

private noncomputable def bernoulliExpect (p : ℝ) (g : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, bernoulliProb p x * g x

private lemma bernoulliExpect_prod (p : ℝ) (g : ι → Bool → ℝ) :
    bernoulliExpect p (fun x ↦ ∏ i, g i (x i)) =
      ∏ i, ((1 - p) * g i false + p * g i true) := by
  simp only [bernoulliExpect, bernoulliProb, ← prod_mul_distrib]
  rw [← Fintype.prod_sum fun i (b : Bool) ↦ (if b then p else 1 - p) * g i b]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

@[simp]
theorem sum_bernoulliProb (p : ℝ) : (∑ x : ι → Bool, bernoulliProb p x) = 1 := by
  have h := bernoulliExpect_prod (ι := ι) p (fun _ _ ↦ 1)
  simp only [bernoulliExpect, prod_const_one, mul_one] at h
  rw [h]
  exact prod_eq_one fun _ _ ↦ by ring

private lemma bernoulliProb_split (p : ℝ) (A : Finset ι) (x : ι → Bool) :
    bernoulliProb p x =
      (∏ i ∈ A, if x i then p else 1 - p) * ∏ i ∈ univ \ A, if x i then p else 1 - p := by
  rw [bernoulliProb, ← prod_sdiff (subset_univ A), mul_comm]

omit [DecidableEq ι] in
private lemma bernoulliProb_prod_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α × β ≃ ι) (p : ℝ) (y : ι → Bool) :
    bernoulliProb p y = ∏ a : α, bernoulliProb p (fun b : β ↦ y (e (a, b))) := by
  simp only [bernoulliProb]
  rw [← Fintype.prod_equiv e
    (fun ab ↦ if y (e ab) then p else 1 - p)
    (fun i ↦ if y i then p else 1 - p) (fun _ ↦ rfl)]
  exact Fintype.prod_prod_type fun ab ↦ if y (e ab) then p else 1 - p

/-- Event probability under the independent $p$-biased product law on `ι → Bool`. -/
noncomputable def bernoulliEventProb (p : ℝ) (E : (ι → Bool) → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then bernoulliProb p x else 0

private lemma bernoulliEventProb_congr {p : ℝ} {E₁ E₂ : (ι → Bool) → Prop}
    (h : ∀ x, E₁ x ↔ E₂ x) :
    bernoulliEventProb p E₁ = bernoulliEventProb p E₂ := by
  classical
  simp only [bernoulliEventProb]
  exact sum_congr rfl fun x _ ↦ if_congr (h x) rfl rfl

private lemma bernoulliEventProb_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E₁ E₂ : (ι → Bool) → Prop} (h : ∀ x, E₁ x → E₂ x) :
    bernoulliEventProb p E₁ ≤ bernoulliEventProb p E₂ := by
  classical
  simp only [bernoulliEventProb]
  refine sum_le_sum fun x _ ↦ ?_
  by_cases h1 : E₁ x
  · simp [h1, h x h1]
  · simp only [h1, ↓reduceIte]
    split_ifs
    · exact bernoulliProb_nonneg hp0 hp1 x
    · exact le_rfl

private lemma bernoulliEventProb_not (p : ℝ) (E : (ι → Bool) → Prop) :
    bernoulliEventProb p (fun x ↦ ¬ E x) = 1 - bernoulliEventProb p E := by
  classical
  have hsum : bernoulliEventProb p E + bernoulliEventProb p (fun x ↦ ¬ E x) = 1 := by
    simp only [bernoulliEventProb, ← sum_add_distrib]
    refine (sum_congr rfl fun x _ ↦ ?_).trans (sum_bernoulliProb p)
    split_ifs <;> linarith
  linarith

private lemma bernoulliEventProb_all_false (p : ℝ) (A : Finset ι) :
    bernoulliEventProb p (fun x ↦ ∀ i ∈ A, x i = false) = (1 - p) ^ A.card := by
  classical
  have hprod := bernoulliExpect_prod p
    (fun i b ↦ if i ∈ A then (if b = false then (1 : ℝ) else 0) else 1)
  have hlhs : bernoulliExpect p
      (fun x ↦ ∏ i, if i ∈ A then (if x i = false then (1 : ℝ) else 0) else 1) =
      bernoulliEventProb p (fun x ↦ ∀ i ∈ A, x i = false) := by
    simp only [bernoulliExpect, bernoulliEventProb]
    refine sum_congr rfl fun x _ ↦ ?_
    by_cases hx : ∀ i ∈ A, x i = false
    · have hp1 : (∏ i : ι, if i ∈ A then (if x i = false then (1 : ℝ) else 0) else 1) = 1 := by
        refine prod_eq_one fun i _ ↦ ?_
        by_cases hi : i ∈ A
        · simp [hi, hx i hi]
        · simp [hi]
      rw [hp1, mul_one]
      split_ifs
      rfl
    · have hx_neg : ¬ ∀ i ∈ A, x i = false := hx
      push Not at hx
      obtain ⟨i₀, hi₀, hxi₀⟩ := hx
      have hp0 : (∏ i : ι, if i ∈ A then (if x i = false then (1 : ℝ) else 0) else 1) = 0 :=
        prod_eq_zero (mem_univ i₀) (by simp [hi₀, hxi₀])
      rw [hp0, mul_zero]
      split_ifs
      rfl
  rw [← hlhs, hprod]
  have hfactor : ∀ i : ι,
      (1 - p) * (if i ∈ A then (1 : ℝ) else 1) + p * (if i ∈ A then 0 else 1) =
        if i ∈ A then 1 - p else 1 := fun i ↦ by by_cases hi : i ∈ A <;> simp [hi]
  simp only [↓reduceIte, Bool.true_eq_false]
  simp_rw [hfactor]
  rw [prod_ite, filter_mem_eq_inter, univ_inter, prod_const, prod_const_one, mul_one]

private lemma bernoulliEventProb_any_true (p : ℝ) (A : Finset ι) :
    bernoulliEventProb p (fun x ↦ ∃ i ∈ A, x i = true) = 1 - (1 - p) ^ A.card := by
  have heq : bernoulliEventProb p (fun x ↦ ∃ i ∈ A, x i = true) =
      bernoulliEventProb p (fun x ↦ ¬ ∀ i ∈ A, x i = false) := by
    refine bernoulliEventProb_congr fun x ↦ ?_
    push Not; simp
  rw [heq, bernoulliEventProb_not, bernoulliEventProb_all_false]

private lemma bernoulliExpect_update_split (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    bernoulliExpect p g =
      bernoulliExpect p (fun x ↦
        (1 - p) * g (Function.update x i false) + p * g (Function.update x i true)) := by
  let e : (ι → Bool) ≃ Bool × ({j : ι // j ≠ i} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun j ↦ j = i) (fun _ ↦ Bool)).trans
      (Equiv.prodCongr (Equiv.funUnique {j : ι // j = i} Bool) (Equiv.refl _))
  have hprob (b : Bool) (z : {j : ι // j ≠ i} → Bool) :
      bernoulliProb p (e.symm (b, z)) =
        (if b then p else 1 - p) * ∏ j : {j : ι // j ≠ i}, if z j then p else 1 - p := by
    have hsplit := bernoulliProb_split p ({i} : Finset ι) (e.symm (b, z))
    rw [prod_singleton] at hsplit
    have hi : e.symm (b, z) i = b := by simp [e, Equiv.piEquivPiSubtypeProd]
    rw [hi] at hsplit
    rw [hsplit]
    congr 1
    let eSub : {j : ι // j ≠ i} ≃ {j : ι // j ∈ univ \ ({i} : Finset ι)} :=
      { toFun := fun ⟨j, hj⟩ ↦ ⟨j, by simp [hj]⟩
        invFun := fun ⟨j, hj⟩ ↦ ⟨j, by simpa using hj⟩
        left_inv := fun ⟨_, _⟩ ↦ rfl
        right_inv := fun ⟨_, _⟩ ↦ rfl }
    rw [← prod_coe_sort (univ \ ({i} : Finset ι)) (fun j ↦ if e.symm (b, z) j then p else 1 - p)]
    refine Fintype.prod_equiv eSub.symm
      (fun k ↦ if e.symm (b, z) k.1 then p else 1 - p)
      (fun j ↦ if z j then p else 1 - p) fun k ↦ ?_
    have hne : k.1 ≠ i := fun h ↦ (mem_sdiff.mp k.2).2 (mem_singleton.mpr h)
    have hk : e.symm (b, z) k.1 = z (eSub.symm k) := by
      simp [e, eSub, Equiv.piEquivPiSubtypeProd, hne]
    rw [hk]
  have hupd (b b' : Bool) (z : {j : ι // j ≠ i} → Bool) :
      Function.update (e.symm (b, z)) i b' = e.symm (b', z) := by
    funext j
    by_cases hji : j = i
    · subst hji; simp [e, Equiv.piEquivPiSubtypeProd]
    · simp [Function.update, hji, e, Equiv.piEquivPiSubtypeProd]
  simp only [bernoulliExpect]
  rw [← e.symm.sum_comp, ← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun z _ ↦ ?_
  simp only [hprob, hupd, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Resampling $p$-biased coordinate influence `Pr_{x, y ~ μ_p}[f(x) ≠ f(x_{-i}, y_i)]`. -/
noncomputable def pBiasedCoordInfluence (p : ℝ) (i : ι) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ x, ∑ y,
    if f x ≠ f (Function.update x i (y i)) then bernoulliProb p x * bernoulliProb p y else 0

/-- Total $p$-biased resampling influence `∑ i, pBiasedCoordInfluence p i f`. -/
noncomputable def pBiasedTotalInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i, pBiasedCoordInfluence p i f

/-- Resampling $p$-biased coordinate influence equals `2 * p * (1 - p)` times the $p$-biased
pivotal probability of coordinate `i`. -/
theorem pBiasedCoordInfluence_eq_two_mul_pivotal (p : ℝ) (i : ι) (f : (ι → Bool) → Bool) :
    pBiasedCoordInfluence p i f =
      2 * p * (1 - p) * bernoulliEventProb p (fun x ↦
        f (Function.update x i true) ≠ f (Function.update x i false)) := by
  classical
  have hy_prob (b : Bool) :
      bernoulliEventProb p (fun y : ι → Bool ↦ y i = b) = if b then p else 1 - p := by
    cases b
    · simpa using bernoulliEventProb_all_false p ({i} : Finset ι)
    · have h := bernoulliEventProb_any_true p ({i} : Finset ι)
      simp only [mem_singleton, exists_eq_left, card_singleton, pow_one] at h
      simp only [↓reduceIte]; linarith
  have hinner (x : ι → Bool) :
      (∑ y : ι → Bool,
          if f x ≠ f (Function.update x i (y i)) then bernoulliProb p x * bernoulliProb p y
          else 0) =
        bernoulliProb p x *
          (if f x ≠ f (Function.update x i (!x i)) then (if !x i then p else 1 - p) else 0) := by
    have hcond (y : ι → Bool) :
        (f x ≠ f (Function.update x i (y i))) ↔
          (f x ≠ f (Function.update x i (!x i)) ∧ y i = !x i) := by
      by_cases hyx : y i = x i
      · rw [hyx, Function.update_eq_self]; cases x i <;> simp
      · have hy_not : y i = !x i := by cases h1 : y i <;> cases h2 : x i <;> simp_all
        rw [hy_not]; simp
    have hrw : ∀ y : ι → Bool,
        (if f x ≠ f (Function.update x i (y i)) then bernoulliProb p x * bernoulliProb p y
          else 0) =
        (if f x ≠ f (Function.update x i (!x i)) ∧ y i = !x i then
          bernoulliProb p x * bernoulliProb p y else 0) :=
      fun y ↦ if_congr (hcond y) rfl rfl
    simp_rw [hrw]
    by_cases hpiv : f x ≠ f (Function.update x i (!x i))
    · have htrue : ∀ y : ι → Bool,
          (if f x ≠ f (Function.update x i (!x i)) ∧ y i = !x i then
            bernoulliProb p x * bernoulliProb p y else 0) =
          if y i = !x i then bernoulliProb p x * bernoulliProb p y else 0 :=
        fun y ↦ if_congr ⟨fun h ↦ h.2, fun h ↦ ⟨hpiv, h⟩⟩ rfl rfl
      simp_rw [htrue]
      have hmul : (∑ y : ι → Bool,
          if y i = !x i then bernoulliProb p x * bernoulliProb p y else 0) =
          bernoulliProb p x * bernoulliEventProb p (fun y : ι → Bool ↦ y i = !x i) := by
        rw [bernoulliEventProb, mul_sum]
        refine sum_congr rfl fun y _ ↦ ?_
        split_ifs <;> ring
      rw [hmul, hy_prob]
      split_ifs <;> rfl
    · have hfalse : ∀ y : ι → Bool,
          (if f x ≠ f (Function.update x i (!x i)) ∧ y i = !x i then
            bernoulliProb p x * bernoulliProb p y else 0) = 0 := by
        intro y; split_ifs with h
        · exact (hpiv h.1).elim
        · rfl
      simp_rw [hfalse]
      rw [sum_const_zero]
      split_ifs; ring
  rw [pBiasedCoordInfluence]
  simp_rw [hinner]
  let g : (ι → Bool) → ℝ := fun x ↦
    if f x ≠ f (Function.update x i (!x i)) then (if !x i then p else 1 - p) else 0
  have hexp : (∑ x : ι → Bool, bernoulliProb p x * g x) = bernoulliExpect p g := rfl
  rw [hexp, bernoulliExpect_update_split p i g]
  simp only [bernoulliExpect, bernoulliEventProb, mul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  have h0 : g (Function.update x i false) =
      if f (Function.update x i true) ≠ f (Function.update x i false) then p else 0 := by
    simp only [g, Function.update_self, Bool.not_false, ↓reduceIte, Function.update_idem, ne_comm]
  have h1 : g (Function.update x i true) =
      if f (Function.update x i true) ≠ f (Function.update x i false) then 1 - p else 0 := by
    simp only [g, Function.update_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Function.update_idem]
  rw [h0, h1]
  split_ifs <;> ring

private lemma mul_pow_pred_le_one_sub_pow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ k : ℕ, (k : ℝ) * p * (1 - p) ^ (k - 1) ≤ 1 - (1 - p) ^ k
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
    have ih := mul_pow_pred_le_one_sub_pow hp0 hp1 (k + 1)
    change ((k + 1 : ℕ) : ℝ) * p * (1 - p) ^ k ≤ 1 - (1 - p) ^ (k + 1) at ih
    change ((k + 2 : ℕ) : ℝ) * p * (1 - p) ^ (k + 1) ≤ 1 - (1 - p) ^ (k + 2)
    have hpow : (1 - p) ^ (k + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hstep :
        ((k + 2 : ℕ) : ℝ) * p * (1 - p) ^ (k + 1) =
          (1 - p) * (((k + 1 : ℕ) : ℝ) * p * (1 - p) ^ k) + p * (1 - p) ^ (k + 1) := by
      push_cast; ring
    rw [hstep]
    have hmul :
        (1 - p) * (((k + 1 : ℕ) : ℝ) * p * (1 - p) ^ k) ≤ (1 - p) * (1 - (1 - p) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have hp_term : p * (1 - p) ^ (k + 1) ≤ p * 1 := mul_le_mul_of_nonneg_left hpow hp0
    have hident : (1 - p) * (1 - (1 - p) ^ (k + 1)) + p = 1 - (1 - p) ^ (k + 2) := by ring
    linarith

/-- For `0 ≤ p ≤ 1`, the total $p$-biased influence of the disjunction over any coordinate subset
`A : Finset ι` is at most twice its acceptance probability. -/
theorem pBiasedTotalInfluence_or_subset_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset ι) :
    pBiasedTotalInfluence p (fun x ↦ decide (∃ j ∈ A, x j = true)) ≤
      2 * bernoulliEventProb p (fun x ↦ decide (∃ j ∈ A, x j = true) = true) := by
  let f : (ι → Bool) → Bool := fun x ↦ decide (∃ j ∈ A, x j = true)
  have hcoord (i : ι) :
      pBiasedCoordInfluence p i f =
        if i ∈ A then 2 * p * (1 - p) * (1 - p) ^ (A.card - 1) else 0 := by
    rw [pBiasedCoordInfluence_eq_two_mul_pivotal]
    by_cases hi : i ∈ A
    · simp only [hi, ↓reduceIte]
      congr 1
      have hpiv : ∀ x : ι → Bool,
          (f (Function.update x i true) ≠ f (Function.update x i false)) ↔
            ∀ j ∈ A.erase i, x j = false := by
        intro x
        have htrue : f (Function.update x i true) = true := by
          simp only [f, decide_eq_true_eq]; exact ⟨i, hi, by simp⟩
        rw [htrue, ne_comm]
        have hbf : ∀ b : Bool, (b ≠ true) ↔ (b = false) := by decide
        rw [hbf]
        simp only [f, decide_eq_false_iff_not, not_exists, not_and, Bool.not_eq_true]
        refine ⟨fun h j hj ↦ ?_, fun h j hj ↦ ?_⟩
        · have hjne : j ≠ i := ne_of_mem_erase hj
          simpa [Function.update, hjne] using h j (mem_of_mem_erase hj)
        · by_cases hji : j = i
          · subst hji; simp
          · simpa [Function.update, hji] using h j (mem_erase.mpr ⟨hji, hj⟩)
      rw [bernoulliEventProb_congr hpiv, bernoulliEventProb_all_false, card_erase_of_mem hi]
    · simp only [hi, ↓reduceIte]
      have hconst : ∀ x : ι → Bool,
          ¬ (f (Function.update x i true) ≠ f (Function.update x i false)) := by
        intro x; push Not; simp only [f]; congr 1
        exact propext ⟨fun ⟨j, hj, hxj⟩ ↦ ⟨j, hj, by
          have hjne : j ≠ i := fun h ↦ hi (h ▸ hj)
          simpa [Function.update, hjne] using hxj⟩,
          fun ⟨j, hj, hxj⟩ ↦ ⟨j, hj, by
          have hjne : j ≠ i := fun h ↦ hi (h ▸ hj)
          simpa [Function.update, hjne] using hxj⟩⟩
      have hev : bernoulliEventProb p
          (fun x ↦ f (Function.update x i true) ≠ f (Function.update x i false)) = 0 := by
        rw [bernoulliEventProb_congr (E₂ := fun _ ↦ False)
          (fun x ↦ ⟨fun h ↦ (hconst x h).elim, False.elim⟩)]
        classical
        simp [bernoulliEventProb]
      rw [hev, mul_zero]
  have htot : pBiasedTotalInfluence p f =
      (A.card : ℝ) * (2 * p * (1 - p) * (1 - p) ^ (A.card - 1)) := by
    refine (sum_congr rfl fun i _ ↦ hcoord i).trans ?_
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  change pBiasedTotalInfluence p f ≤ _
  rw [htot, bernoulliEventProb_congr (fun _ ↦ decide_eq_true_iff), bernoulliEventProb_any_true]
  have hbin := mul_pow_pred_le_one_sub_pow hp0 hp1 A.card
  have hnonneg : 0 ≤ (A.card : ℝ) * p * (1 - p) ^ (A.card - 1) := by
    have : 0 ≤ 1 - p := by linarith
    positivity
  calc (A.card : ℝ) * (2 * p * (1 - p) * (1 - p) ^ (A.card - 1))
      = 2 * (1 - p) * ((A.card : ℝ) * p * (1 - p) ^ (A.card - 1)) := by ring
    _ ≤ 2 * 1 * ((A.card : ℝ) * p * (1 - p) ^ (A.card - 1)) := by gcongr; linarith
    _ ≤ 2 * (1 - (1 - p) ^ A.card) := by linarith

/-- Probability under `x ~ μ_p` that a coalition `S : Finset ι` can choose its coordinates to
force `f` to output `b`. -/
noncomputable def pBiasedCoalitionProb (p : ℝ) (S : Finset ι) (b : Bool)
    (f : (ι → Bool) → Bool) : ℝ :=
  bernoulliEventProb p (fun x ↦ ∃ y : ι → Bool, f (S.piecewise y x) = b)

/-- Unanimous-vote formula for $p$-biased coalitional forcing of a monotone Boolean function. -/
theorem pBiasedCoalitionProb_eq_of_monotone {p : ℝ} {f : (ι → Bool) → Bool} (hf : Monotone f)
    (S : Finset ι) (b : Bool) :
    pBiasedCoalitionProb p S b f =
      bernoulliEventProb p (fun x ↦ f (S.piecewise (fun _ ↦ b) x) = b) := by
  refine bernoulliEventProb_congr fun x ↦ ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ⟨fun _ ↦ b, h⟩⟩
  cases b
  · have hle : S.piecewise (fun _ ↦ false) x ≤ S.piecewise y x := fun j ↦ by
      by_cases hj : j ∈ S <;> simp [Finset.piecewise, hj]
    exact Bool.eq_false_iff.mpr fun htrue ↦ by
      have := hf hle; rw [htrue, hy] at this; exact not_le_of_gt Bool.false_lt_true this
  · have hle : S.piecewise y x ≤ S.piecewise (fun _ ↦ true) x := fun j ↦ by
      by_cases hj : j ∈ S <;> simp [Finset.piecewise, hj]
    have := hf hle; rw [hy] at this; exact top_le_iff.mp this

end BiasedCube

section MaxSelectorEncoding

/-- Monotone max-selector `(Fin ℓ → Bool) → Fin r` returning `a (max {j | y j = true})` when `y`
has at least one `true` coordinate, and `0` otherwise. -/
def maxSelector {r : ℕ} (hr : 1 ≤ r) {ℓ : ℕ} (a : Fin ℓ → Fin r)
    (y : Fin ℓ → Bool) : Fin r :=
  if h : (univ.filter fun j : Fin ℓ ↦ y j = true).Nonempty then
    a ((univ.filter fun j : Fin ℓ ↦ y j = true).max' h)
  else
    ⟨0, hr⟩

/-- Monotonicity of `maxSelector` whenever the lookup sequence `a` is monotone. -/
theorem maxSelector_monotone {r : ℕ} (hr : 1 ≤ r) {ℓ : ℕ} {a : Fin ℓ → Fin r} (ha : Monotone a) :
    Monotone (maxSelector hr a) := by
  intro y₁ y₂ hy
  unfold maxSelector
  split_ifs with h1 h2 h2
  · refine ha (le_max' _ _ ?_)
    have hmem := max'_mem (univ.filter fun j : Fin ℓ ↦ y₁ j = true) h1
    rw [mem_filter] at hmem ⊢
    exact ⟨mem_univ _, top_le_iff.mp (hmem.2.symm.trans_le (hy _))⟩
  · exfalso
    obtain ⟨j, hj⟩ := h1
    rw [mem_filter] at hj
    exact h2 ⟨j, mem_filter.mpr ⟨mem_univ j, top_le_iff.mp (hj.2.symm.trans_le (hy j))⟩⟩
  · exact Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  · exact le_rfl

/-- Every positive threshold `t ≤ maxSelector hr a y` (`0 < t.val`) is equivalent to an OR over
the coordinate subset `{j | t ≤ a j}`. -/
theorem le_maxSelector_iff_exists {r : ℕ} (hr : 1 ≤ r) {ℓ : ℕ} {a : Fin ℓ → Fin r}
    (ha : Monotone a) {t : Fin r} (ht : 0 < t.val) (y : Fin ℓ → Bool) :
    t ≤ maxSelector hr a y ↔ ∃ j : Fin ℓ, t ≤ a j ∧ y j = true := by
  unfold maxSelector
  split_ifs with h
  · refine ⟨fun hle ↦ ?_, fun ⟨j, hta, hyj⟩ ↦ hta.trans (ha (le_max' _ j ?_))⟩
    · have hmem := max'_mem (univ.filter fun j : Fin ℓ ↦ y j = true) h
      exact ⟨_, hle, (mem_filter.mp hmem).2⟩
    · exact mem_filter.mpr ⟨mem_univ j, hyj⟩
  · refine ⟨fun hle ↦ ?_, fun ⟨j, _, hyj⟩ ↦ (h ⟨j, mem_filter.mpr ⟨mem_univ j, hyj⟩⟩).elim⟩
    simp only [Fin.le_iff_val_le_val] at hle
    omega

private lemma maxSelector_le_iff_forall {r : ℕ} (hr : 1 ≤ r) {ℓ : ℕ} {a : Fin ℓ → Fin r}
    (ha : Monotone a) (i : Fin r) (y : Fin ℓ → Bool) :
    maxSelector hr a y ≤ i ↔ ∀ j : Fin ℓ, i < a j → y j = false := by
  unfold maxSelector
  split_ifs with h
  · refine ⟨fun hle j hij ↦ ?_, fun hall ↦ ?_⟩
    · by_contra hyj
      rw [Bool.not_eq_false] at hyj
      have hjle :=
        le_max' (univ.filter fun k : Fin ℓ ↦ y k = true) j (mem_filter.mpr ⟨mem_univ j, hyj⟩)
      exact not_lt_of_ge ((ha hjle).trans hle) hij
    · have hmem := max'_mem (univ.filter fun k : Fin ℓ ↦ y k = true) h
      have hy_max : y ((univ.filter fun k : Fin ℓ ↦ y k = true).max' h) = true :=
        (mem_filter.mp hmem).2
      by_contra hnot
      rw [not_le] at hnot
      have := hall _ hnot
      rw [hy_max] at this
      exact Bool.noConfusion this
  · refine ⟨fun _ j _ ↦ ?_, fun _ ↦ Fin.le_iff_val_le_val.mpr (Nat.zero_le _)⟩
    by_contra hyj
    rw [Bool.not_eq_false] at hyj
    exact h ⟨j, mem_filter.mpr ⟨mem_univ j, hyj⟩⟩

private lemma exists_chi_pow {r : ℕ} (hr : 1 ≤ r) {p : ℝ} (hp0 : 0 < p) (hp12 : p < 1 / 2)
    (i : Fin r) :
    ∃ k : ℕ, (1 - p) ^ (k + 1) < ((i.val + 1 : ℕ) : ℝ) / (r : ℝ) := by
  have h1mp_pos : 0 < 1 - p := by linarith
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hi_pos : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by positivity
  let q : ℝ := p / (1 - p)
  have hq_pos : 0 < q := div_pos hp0 h1mp_pos
  let K : ℕ := ⌈((r : ℝ) / ((i.val + 1 : ℕ) : ℝ)) / q⌉₊
  refine ⟨K, ?_⟩
  have h1q : (1 + q) ^ (K + 1) > (r : ℝ) / ((i.val + 1 : ℕ) : ℝ) := by
    have hbern := one_add_mul_le_pow (a := q) (by linarith) (K + 1)
    have hK : ((r : ℝ) / ((i.val + 1 : ℕ) : ℝ)) / q ≤ (K : ℝ) := Nat.le_ceil _
    have hKq : (r : ℝ) / ((i.val + 1 : ℕ) : ℝ) ≤ (K : ℝ) * q := (div_le_iff₀ hq_pos).mp hK
    have hsucc : (K : ℝ) * q < ((K + 1 : ℕ) : ℝ) * q := by push_cast; linarith
    linarith
  have hinv_eq : 1 + q = (1 - p)⁻¹ := by simp only [q]; field_simp; ring
  rw [hinv_eq, inv_pow] at h1q
  have hpow_pos : 0 < (1 - p) ^ (K + 1) := pow_pos h1mp_pos (K + 1)
  have hfrac_pos : 0 < (r : ℝ) / ((i.val + 1 : ℕ) : ℝ) := div_pos hr_pos hi_pos
  have := (inv_lt_inv₀ (inv_pos.mpr hpow_pos) hfrac_pos).mpr h1q
  simpa [inv_div] using this

/-- For every `r ≥ 1` and `p ∈ (0, 1 / 2)`, there exist `ℓ : ℕ` and a monotone sequence
`a : Fin ℓ → Fin r` whose `maxSelector` pushforward under `μ_p^ℓ` approximates the uniform mass
`1 / r` within `2 * p` at every symbol `i : Fin r`. -/
theorem exists_monotone_seq_approx_uniform {r : ℕ} (hr : 1 ≤ r) {p : ℝ}
    (hp0 : 0 < p) (hp12 : p < 1 / 2) :
    ∃ (ℓ : ℕ) (a : Fin ℓ → Fin r),
      Monotone a ∧
        ∀ i : Fin r,
          |bernoulliEventProb p (fun y : Fin ℓ → Bool ↦ maxSelector hr a y = i) -
            1 / (r : ℝ)| ≤ 2 * p := by
  classical
  let χ (i : Fin r) : ℕ := Nat.find (exists_chi_pow hr hp0 hp12 i)
  have hchi_lt : ∀ i : Fin r, (1 - p) ^ (χ i + 1) < ((i.val + 1 : ℕ) : ℝ) / (r : ℝ) :=
    fun i ↦ Nat.find_spec (exists_chi_pow hr hp0 hp12 i)
  have hchi_le : ∀ i : Fin r, ((i.val + 1 : ℕ) : ℝ) / (r : ℝ) ≤ (1 - p) ^ χ i := by
    intro i
    cases h : χ i with
    | zero =>
      rw [pow_zero, div_le_one (by exact_mod_cast hr)]
      exact_mod_cast i.isLt
    | succ k =>
      exact not_lt.mp (Nat.find_min (exists_chi_pow hr hp0 hp12 i) (show k < χ i by omega))
  have hchi_upper : ∀ i : Fin r,
      (1 - p) ^ χ i ≤ (((i.val + 1 : ℕ) : ℝ) / (r : ℝ)) * (1 + 2 * p) := by
    intro i
    have hlt := hchi_lt i
    rw [pow_succ] at hlt
    have h1mp_pos : 0 < 1 - p := by linarith
    have hdiv : (1 - p) ^ χ i ≤ (((i.val + 1 : ℕ) : ℝ) / (r : ℝ)) * (1 / (1 - p)) := by
      rw [mul_one_div, le_div_iff₀ h1mp_pos]; exact hlt.le
    have hinv_le : 1 / (1 - p) ≤ 1 + 2 * p := by rw [div_le_iff₀ h1mp_pos]; nlinarith
    exact hdiv.trans (mul_le_mul_of_nonneg_left hinv_le (by positivity))
  have hchi_last : χ ⟨r - 1, by omega⟩ = 0 := by
    by_contra hne
    have hle := hchi_le ⟨r - 1, by omega⟩
    have h1 : (((⟨r - 1, by omega⟩ : Fin r).val + 1 : ℕ) : ℝ) / (r : ℝ) = 1 := by
      have hval : (⟨r - 1, by omega⟩ : Fin r).val + 1 = r := by simp; omega
      rw [hval, div_self (by exact_mod_cast (show r ≠ 0 by omega))]
    rw [h1] at hle
    have hpow := pow_le_pow_of_le_one (a :=
      1 - p) (by linarith) (by linarith) (show 1 ≤ χ ⟨r - 1, by omega⟩ by omega)
    linarith
  have hchi_anti : Antitone χ := by
    intro i₁ i₂ hi
    by_contra hlt
    have hsucc : χ i₁ + 1 ≤ χ i₂ := by omega
    have hpow := pow_le_pow_of_le_one (a := 1 - p) (by linarith) (by linarith) hsucc
    have h1 := hchi_lt i₁
    have h2 := hchi_le i₂
    have hfrac : ((i₁.val + 1 : ℕ) : ℝ) / (r : ℝ) ≤ ((i₂.val + 1 : ℕ) : ℝ) / (r : ℝ) := by
      gcongr; exact Fin.le_iff_val_le_val.mp hi
    linarith
  let L : ℕ := χ ⟨0, hr⟩ + 1
  have hnonempty : ∀ j : Fin L, (univ.filter fun i : Fin r ↦ j.val < L - χ i).Nonempty := by
    intro j
    refine ⟨⟨r - 1, by omega⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [hchi_last, Nat.sub_zero]; exact j.isLt
  let a : Fin L → Fin r := fun j ↦ (univ.filter fun i : Fin r ↦ j.val < L - χ i).min' (hnonempty j)
  have ha_le_iff : ∀ (j : Fin L) (i : Fin r), a j ≤ i ↔ j.val < L - χ i := by
    intro j i
    refine ⟨fun hle ↦ ?_, fun hlt ↦ min'_le _ i (mem_filter.mpr ⟨mem_univ i, hlt⟩)⟩
    have hjlt : j.val < L - χ (a j) := (mem_filter.mp (min'_mem _ (hnonempty j))).2
    have := hchi_anti hle
    omega
  have ha_mono : Monotone a := by
    intro j₁ j₂ hj
    rw [ha_le_iff]
    have h2 := (ha_le_iff j₂ (a j₂)).mp le_rfl
    have := Fin.le_iff_val_le_val.mp hj
    omega
  have hcdf : ∀ i : Fin r,
      bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y ≤ i) = (1 - p) ^ χ i := by
    intro i
    have hiff : ∀ y : Fin L → Bool,
        maxSelector hr a y ≤ i ↔ ∀ j ∈ univ.filter (fun j : Fin L ↦ i < a j), y j = false := by
      intro y; rw [maxSelector_le_iff_forall hr ha_mono]; simp
    rw [bernoulliEventProb_congr hiff, bernoulliEventProb_all_false]
    have hfilter_eq : (univ.filter fun j : Fin L ↦ i < a j) =
        univ.filter fun j : Fin L ↦ L - χ i ≤ j.val := by
      ext j; simp only [mem_filter, mem_univ, true_and]; rw [← not_le, ha_le_iff, not_lt]
    rw [hfilter_eq]
    have hbij : (univ.filter fun j : Fin L ↦ L - χ i ≤ j.val).card =
        (Ico (L - χ i) L).card :=
      Finset.card_bij (fun (j : Fin L) _ ↦ j.val)
        (fun j hj ↦ mem_Ico.mpr ⟨(mem_filter.mp hj).2, j.isLt⟩)
        (fun _ _ _ _ h ↦ Fin.ext h)
        (fun m hm ↦ ⟨⟨m, (mem_Ico.mp hm).2⟩, mem_filter.mpr ⟨mem_univ _, (mem_Ico.mp hm).1⟩, rfl⟩)
    have hchi_top : χ i ≤ L := by
      have := hchi_anti (show (⟨0, hr⟩ : Fin r) ≤ i from Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
      omega
    rw [hbij, Nat.card_Ico, Nat.sub_sub_self hchi_top]
  refine ⟨L, a, ha_mono, fun i ↦ ?_⟩
  rcases eq_or_ne i.val 0 with hi0 | hi_pos
  · have hi_eq : i = ⟨0, hr⟩ := Fin.ext hi0
    subst hi_eq
    have heq : bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y = ⟨0, hr⟩) =
        bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y ≤ ⟨0, hr⟩) :=
      bernoulliEventProb_congr fun y ↦ ⟨fun h ↦ h.le,
        fun h ↦ Fin.ext (by have := Fin.le_iff_val_le_val.mp h; omega)⟩
    rw [heq, hcdf ⟨0, hr⟩]
    have hlow := hchi_le ⟨0, hr⟩
    have hhigh := hchi_upper ⟨0, hr⟩
    simp only [zero_add, Nat.cast_one] at hlow hhigh
    have h1r_le1 : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one (by exact_mod_cast hr)]; exact_mod_cast hr
    rw [abs_le]; constructor <;> nlinarith
  · let ipred : Fin r := ⟨i.val - 1, by omega⟩
    have hdiff : bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y = i) =
        (1 - p) ^ χ i - (1 - p) ^ χ ipred := by
      have hsum : bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y ≤ i) =
          bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y ≤ ipred) +
            bernoulliEventProb p (fun y : Fin L → Bool ↦ maxSelector hr a y = i) := by
        simp only [bernoulliEventProb, ← sum_add_distrib]
        refine sum_congr rfl fun y _ ↦ ?_
        by_cases hyi : maxSelector hr a y = i
        · have hnot : ¬ (i ≤ ipred) := by
            simp [ipred, Fin.le_iff_val_le_val]; omega
          simp [hyi, hnot]
        · by_cases hle : maxSelector hr a y ≤ i
          · have hpred : maxSelector hr a y ≤ ipred := by
              have hlt := lt_of_le_of_ne (Fin.le_iff_val_le_val.mp hle) (fun h ↦ hyi (Fin.ext h))
              simp [ipred, Fin.le_iff_val_le_val]; omega
            simp [hle, hpred, hyi]
          · have hnot : ¬ (maxSelector hr a y ≤ ipred) := fun hp ↦ hle (hp.trans (by
              simp [ipred, Fin.le_iff_val_le_val]))
            simp [hle, hnot, hyi]
      rw [hcdf i, hcdf ipred] at hsum
      linarith
    rw [hdiff]
    have hlow_i := hchi_le i
    have hhigh_i := hchi_upper i
    have hlow_p := hchi_le ipred
    have hhigh_p := hchi_upper ipred
    have hipred_succ : ipred.val + 1 = i.val := by simp [ipred]; omega
    rw [hipred_succ] at hlow_p hhigh_p
    have hi_le_r : ((i.val + 1 : ℕ) : ℝ) / (r : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hr)]; exact_mod_cast i.isLt
    have hipred_le_r : (i.val : ℝ) / (r : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hr)]; exact_mod_cast i.isLt.le
    have hdiff_frac : ((i.val + 1 : ℕ) : ℝ) / (r : ℝ) - (i.val : ℝ) / (r : ℝ) = 1 / (r : ℝ) := by
      push_cast; ring
    rw [abs_le]
    constructor
    · calc - (2 * p) ≤ - (2 * p * ((i.val : ℝ) / (r : ℝ))) := by nlinarith
        _ = (((i.val + 1 : ℕ) : ℝ) / (r : ℝ) - ((i.val : ℝ) / (r : ℝ)) * (1 + 2 * p)) -
              1 / (r : ℝ) := by rw [← hdiff_frac]; ring
        _ ≤ ((1 - p) ^ χ i - (1 - p) ^ χ ipred) - 1 / (r : ℝ) := by linarith
    · calc ((1 - p) ^ χ i - (1 - p) ^ χ ipred) - 1 / (r : ℝ)
          ≤ ((((i.val + 1 : ℕ) : ℝ) / (r : ℝ)) * (1 + 2 * p) - (i.val : ℝ) / (r : ℝ)) -
              1 / (r : ℝ) := by linarith
        _ = 2 * p * (((i.val + 1 : ℕ) : ℝ) / (r : ℝ)) := by rw [← hdiff_frac]; ring
        _ ≤ 2 * p := by nlinarith

/-- Uniform acceptance probability of `f : (Fin n → Fin r) → Bool` over `Fin n → Fin r`. -/
noncomputable def uniformFinExpect (r n : ℕ)
    (f : (Fin n → Fin r) → Bool) : ℝ :=
  ((univ.filter fun x : Fin n → Fin r ↦ f x = true).card : ℝ) * (1 / (r : ℝ)) ^ n

/-- Total `0`-directed influence of a monotone function `f : (Fin n → Fin r) → Bool` under the
uniform product distribution on `Fin n → Fin r`. -/
noncomputable def uniformFinZeroDirInf {r : ℕ} (hr : 1 ≤ r) (n : ℕ)
    (f : (Fin n → Fin r) → Bool) : ℝ :=
  ∑ i : Fin n,
    (uniformFinExpect r n f -
      uniformFinExpect r n (fun x ↦ f (Function.update x i ⟨0, hr⟩)))

/-- Probability under the uniform product distribution on `Fin n → Fin r` that fixing coordinates in
`T` to the maximum symbol `r - 1` makes `f` evaluate to `true`. -/
noncomputable def uniformFinTopForcing {r : ℕ} (hr : 1 ≤ r) (n : ℕ)
    (T : Finset (Fin n)) (f : (Fin n → Fin r) → Bool) : ℝ :=
  uniformFinExpect r n (fun x ↦ f (T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) x))

/-- **Monotone Product-to-Biased Boolean Encoding**: for every `r ≥ 1`, `n : ℕ`, monotone
`f : (Fin n → Fin r) → Bool`, `ε : ℝ`, and `p ∈ (0, 1 / 2)`, there exist `m : ℕ` and a monotone
Boolean function `g : (Fin m → Bool) → Bool` such that:
1. `|Pr_{y ~ μ_p}[g(y) = true] - Pr_{x ~ U_r^n}[f(x) = true]| ≤ p * r * n`,
2. `pBiasedTotalInfluence p g ≤ 2 * J^0(f) + 4 * p * r * n ^ 2`, and
3. every coalition `S : Finset (Fin m)` forcing `g` to `true` with probability `≥ 1 - ε` under
   `μ_p` projects to a coalition `T : Finset (Fin n)` of size `|T| ≤ |S|` forcing `f` to `true`
   with uniform probability `≥ 1 - ε - p * r * n`. -/
theorem exists_monotone_pBiased_encoding {r n : ℕ} (hr : 1 ≤ r)
    {f : (Fin n → Fin r) → Bool} (hf : Monotone f) (ε : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp12 : p < 1 / 2) :
    ∃ (m : ℕ) (g : (Fin m → Bool) → Bool),
      Monotone g ∧
        |bernoulliEventProb p (fun y ↦ g y = true) - uniformFinExpect r n f| ≤
          p * (r : ℝ) * (n : ℝ) ∧
        pBiasedTotalInfluence p g ≤
          2 * uniformFinZeroDirInf hr n f + 4 * p * (r : ℝ) * (n : ℝ) ^ 2 ∧
        ∀ S : Finset (Fin m),
          1 - ε ≤ pBiasedCoalitionProb p S true g →
          ∃ T : Finset (Fin n),
            T.card ≤ S.card ∧
              1 - ε - p * (r : ℝ) * (n : ℝ) ≤ uniformFinTopForcing hr n T f := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hp1 : p ≤ 1 := by linarith
  obtain ⟨ℓ, a, ha_mono, hA_approx⟩ := exists_monotone_seq_approx_uniform hr hp0 hp12
  let cubePMF (k : ℕ) : PMF (Fin k → Bool) :=
    PMF.ofFintype (fun y ↦ ENNReal.ofReal (bernoulliProb p y)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ bernoulliProb_nonneg hp0.le hp1 y),
        sum_bernoulliProb, ENNReal.ofReal_one])
  let A : PMF (Fin r) := (cubePMF ℓ).map (maxSelector hr a)
  let U : PMF (Fin r) := PMF.ofFintype (fun _ ↦ ((r : ℝ≥0∞))⁻¹) (by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top _)])
  have hA_toReal : ∀ i : Fin r, (A i).toReal =
      bernoulliEventProb p (fun y : Fin ℓ → Bool ↦ maxSelector hr a y = i) := by
    classical
    intro i
    simp only [A, cubePMF, PMF.map_apply, PMF.ofFintype_apply, bernoulliEventProb]
    rw [tsum_fintype, ENNReal.toReal_sum (fun y _ ↦ by split_ifs <;> simp)]
    refine sum_congr rfl fun y _ ↦ ?_
    by_cases h : i = maxSelector hr a y
    · simp [h, ENNReal.toReal_ofReal (bernoulliProb_nonneg hp0.le hp1 y)]
    · have hne : maxSelector hr a y ≠ i := fun h' ↦ h h'.symm
      simp [h, hne]
  have hU_toReal : ∀ i : Fin r, (U i).toReal = 1 / (r : ℝ) := by
    intro i; simp [U, ENNReal.toReal_inv, one_div]
  have hdist_AU : dist A U ≤ p * (r : ℝ) := by
    rw [Cslib.Probability.PMF.dist_eq]
    have hsum : (∑ i : Fin r, |(A i).toReal - (U i).toReal|) ≤ (r : ℝ) * (2 * p) := by
      calc (∑ i : Fin r, |(A i).toReal - (U i).toReal|)
          ≤ ∑ _i : Fin r, (2 * p) := sum_le_sum fun i _ ↦ by
            rw [hA_toReal i, hU_toReal i]; exact hA_approx i
        _ = (r : ℝ) * (2 * p) := by simp [nsmul_eq_mul]
    linarith
  have hdist_pi : dist (Cslib.Probability.PMF.pi fun _ : Fin n ↦ A)
      (Cslib.Probability.PMF.pi fun _ : Fin n ↦ U) ≤ p * (r : ℝ) * (n : ℝ) := by
    have h := Cslib.Probability.PMF.dist_pi_le_sum (fun _ : Fin n ↦ A) (fun _ : Fin n ↦ U)
    calc dist (Cslib.Probability.PMF.pi fun _ : Fin n ↦ A)
          (Cslib.Probability.PMF.pi fun _ : Fin n ↦ U)
        ≤ ∑ _j : Fin n, dist A U := h
      _ ≤ ∑ _j : Fin n, (p * (r : ℝ)) := sum_le_sum fun _ _ ↦ hdist_AU
      _ = p * (r : ℝ) * (n : ℝ) := by simp [nsmul_eq_mul]; ring
  let slice (y : Fin (n * ℓ) → Bool) (j : Fin n) : Fin ℓ → Bool :=
    fun k ↦ y (finProdFinEquiv (j, k))
  let decode (y : Fin (n * ℓ) → Bool) : Fin n → Fin r :=
    fun j ↦ maxSelector hr a (slice y j)
  let g : (Fin (n * ℓ) → Bool) → Bool := fun y ↦ f (decode y)
  have hg_mono : Monotone g := fun y₁ y₂ hy ↦
    hf fun j ↦ maxSelector_monotone hr ha_mono fun k ↦ hy (finProdFinEquiv (j, k))
  -- Equivalence splitting `Fin (n * ℓ) → Bool` into `Fin n → Fin ℓ → Bool`.
  let blocksEquiv : (Fin (n * ℓ) → Bool) ≃ (Fin n → Fin ℓ → Bool) :=
    { toFun := slice
      invFun := fun B idx ↦ B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
      left_inv := fun y ↦ funext fun idx ↦ congrArg y (finProdFinEquiv.apply_symm_apply idx)
      right_inv := fun B ↦ funext fun j ↦ funext fun k ↦ by
        dsimp only [slice]; rw [finProdFinEquiv.symm_apply_apply] }
  have hmap_decode : (cubePMF (n * ℓ)).map decode =
      Cslib.Probability.PMF.pi (fun _ : Fin n ↦ A) := by
    have h1 : Cslib.Probability.PMF.pi (fun _ : Fin n ↦ A) =
        (Cslib.Probability.PMF.pi fun _ : Fin n ↦ cubePMF ℓ).map
          (fun B j ↦ maxSelector hr a (B j)) :=
      Cslib.Probability.PMF.pi_map (fun _ : Fin n ↦ cubePMF ℓ) (fun _ ↦ maxSelector hr a)
    rw [h1]
    have h2 : (cubePMF (n * ℓ)).map blocksEquiv =
        Cslib.Probability.PMF.pi (fun _ : Fin n ↦ cubePMF ℓ) := by
      ext B
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_eq_single (blocksEquiv.symm B)]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte, cubePMF, PMF.ofFintype_apply,
          Cslib.Probability.PMF.pi_apply]
        rw [bernoulliProb_prod_equiv finProdFinEquiv p (blocksEquiv.symm B),
          ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ bernoulliProb_nonneg hp0.le hp1 _)]
        refine prod_congr rfl fun j _ ↦ ?_
        have hj : slice (blocksEquiv.symm B) j = B j :=
          congrFun (blocksEquiv.apply_symm_apply B) j
        exact congrArg (fun u ↦ ENNReal.ofReal (bernoulliProb p u)) hj
      · intro y hy
        split_ifs with h
        · subst h; exact (hy (blocksEquiv.symm_apply_apply y).symm).elim
        · rfl
    have hcomp : decode = (fun B j ↦ maxSelector hr a (B j)) ∘ blocksEquiv := rfl
    rw [hcomp, ← PMF.map_comp, h2]
  -- Helper relating Boolean expectation difference under two PMFs to `dist`.
  have hbool_dpi : ∀ (P Q : PMF (Fin n → Fin r)) (h : (Fin n → Fin r) → Bool),
      |(∑ x, if h x = true then (P x).toReal else 0) -
        (∑ x, if h x = true then (Q x).toReal else 0)| ≤ dist P Q := by
    intro P Q h
    have hd := Cslib.Probability.PMF.dist_map_le P Q h
    rw [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool] at hd
    have hm_true : ∀ R : PMF (Fin n → Fin r),
        ((R.map h) true).toReal = ∑ x, if h x = true then (R x).toReal else 0 := by
      intro R
      rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun x _ ↦ by
        split_ifs
        · exact R.apply_ne_top x
        · simp)]
      refine sum_congr rfl fun x _ ↦ ?_
      by_cases hx : h x = true <;> simp [hx, eq_comm]
    have hm_sum : ∀ R : PMF Bool, (R true).toReal + (R false).toReal = 1 := by
      intro R
      have h1 : (∑' b : Bool, R b).toReal = 1 := by rw [R.tsum_coe, ENNReal.toReal_one]
      rwa [tsum_fintype, ENNReal.toReal_sum (fun b _ ↦ R.apply_ne_top b), Fintype.sum_bool] at h1
    have hP1 := hm_sum (P.map h)
    have hQ1 := hm_sum (Q.map h)
    have hfalse : ((P.map h) false).toReal - ((Q.map h) false).toReal =
        - (((P.map h) true).toReal - ((Q.map h) true).toReal) := by linarith
    rw [hfalse, abs_neg] at hd
    rw [← hm_true P, ← hm_true Q]
    linarith
  have hA_exp_eq : ∀ h : (Fin n → Fin r) → Bool,
      bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦ h (decode y) = true) =
        ∑ x : Fin n → Fin r,
          if h x = true then ((Cslib.Probability.PMF.pi fun _ : Fin n ↦ A) x).toReal else 0 := by
    intro h
    rw [← hmap_decode]
    have htoR : ∀ x : Fin n → Fin r,
        (((cubePMF (n * ℓ)).map decode) x).toReal =
          ∑ y, if x = decode y then bernoulliProb p y else 0 := by
      intro x
      rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun y _ ↦ by
        split_ifs
        · exact (cubePMF (n * ℓ)).apply_ne_top y
        · simp)]
      refine sum_congr rfl fun y _ ↦ ?_
      split_ifs <;> simp [cubePMF, ENNReal.toReal_ofReal (bernoulliProb_nonneg hp0.le hp1 y)]
    simp_rw [htoR]
    have hite_in : ∀ x : Fin n → Fin r,
        (if h x = true then ∑ y, (if x = decode y then bernoulliProb p y else 0) else 0) =
          ∑ y, if x = decode y ∧ h x = true then bernoulliProb p y else 0 := by
      intro x; by_cases hx : h x = true <;> simp [hx]
    simp_rw [hite_in]
    rw [sum_comm]
    have hbev : bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦ h (decode y) = true) =
        ∑ y, if h (decode y) = true then bernoulliProb p y else 0 := by
      classical
      rw [bernoulliEventProb]
      exact sum_congr rfl fun y _ ↦ by split_ifs <;> rfl
    rw [hbev]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [Fintype.sum_eq_single (decode y)]
    · simp
    · intro x hx; simp [hx]
  have hU_exp_eq : ∀ h : (Fin n → Fin r) → Bool,
      uniformFinExpect r n h =
        ∑ x : Fin n → Fin r,
          if h x = true then ((Cslib.Probability.PMF.pi fun _ : Fin n ↦ U) x).toReal else 0 := by
    intro h
    simp only [uniformFinExpect]
    have hmass : ∀ x : Fin n → Fin r,
        ((Cslib.Probability.PMF.pi fun _ : Fin n ↦ U) x).toReal = (1 / (r : ℝ)) ^ n := by
      intro x
      rw [Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod]
      simp [hU_toReal]
    simp_rw [hmass]
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  refine ⟨n * ℓ, g, hg_mono, ?_, ?_, ?_⟩
  · -- Property 1: Expectation approximation.
    change |bernoulliEventProb p (fun y ↦ f (decode y) = true) - uniformFinExpect r n f| ≤ _
    rw [hA_exp_eq f, hU_exp_eq f]
    exact (hbool_dpi _ _ f).trans hdist_pi
  · -- Property 2: Total `p`-biased influence bound.
    -- Single-block threshold bound `I^p(h ∘ φ_a) ≤ 2 * (E_A[h] - h(0))`.
    have h1d_inf : ∀ (h : Fin r → Bool), Monotone h →
        pBiasedTotalInfluence p (fun y : Fin ℓ → Bool ↦ h (maxSelector hr a y)) ≤
          2 * (bernoulliEventProb p (fun y : Fin ℓ → Bool ↦ h (maxSelector hr a y) = true) -
            if h ⟨0, hr⟩ then 1 else 0) := by
      intro h hh
      by_cases h0 : h ⟨0, hr⟩ = true
      · have hall : ∀ z : Fin r, h z = true := fun z ↦
          top_le_iff.mp (h0.symm.trans_le (hh (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))))
        have hconst : (fun y : Fin ℓ → Bool ↦ h (maxSelector hr a y)) = fun _ ↦ true :=
          funext fun _ ↦ hall _
        have hev : bernoulliEventProb p (fun y : Fin ℓ → Bool ↦ h (maxSelector hr a y) = true) =
            1 := by
          classical
          simp [bernoulliEventProb, hall]
        rw [hconst, hev, h0]
        simp [pBiasedTotalInfluence, pBiasedCoordInfluence]
      · rw [Bool.not_eq_true] at h0
        by_cases hex : ∃ z : Fin r, h z = true
        · let S_true := univ.filter fun z : Fin r ↦ h z = true
          have hS_ne : S_true.Nonempty := by
            obtain ⟨z, hz⟩ := hex; exact ⟨z, mem_filter.mpr ⟨mem_univ z, hz⟩⟩
          let tStar : Fin r := S_true.min' hS_ne
          have htStar_true : h tStar = true := (mem_filter.mp (min'_mem S_true hS_ne)).2
          have htStar_pos : 0 < tStar.val := by
            by_contra hzero
            have heq0 : tStar = ⟨0, hr⟩ := Fin.ext (by simp; omega)
            rw [heq0, h0] at htStar_true; exact Bool.noConfusion htStar_true
          have hh_iff : ∀ z : Fin r, h z = true ↔ tStar ≤ z := fun z ↦
            ⟨fun hz ↦ min'_le S_true z (mem_filter.mpr ⟨mem_univ z, hz⟩),
              fun hle ↦ top_le_iff.mp (htStar_true.symm.trans_le (hh hle))⟩
          let Aset : Finset (Fin ℓ) := univ.filter fun j : Fin ℓ ↦ tStar ≤ a j
          have hcomp_iff : ∀ y : Fin ℓ → Bool,
              h (maxSelector hr a y) = true ↔ ∃ j ∈ Aset, y j = true := by
            intro y; rw [hh_iff, le_maxSelector_iff_exists hr ha_mono htStar_pos]; simp [Aset]
          let dFn : (Fin ℓ → Bool) → Bool :=
            fun y ↦ @decide (∃ j ∈ Aset, y j = true) decidableExistsAndFinsetCoe
          have hcomp_eq : (fun y : Fin ℓ → Bool ↦ h (maxSelector hr a y)) = dFn := by
            funext y; apply Bool.eq_iff_iff.mpr
            rw [hcomp_iff y, @decide_eq_true_eq (∃ j ∈ Aset, y j = true)
              decidableExistsAndFinsetCoe]
          have hev_eq : bernoulliEventProb p (fun y : Fin ℓ →
            Bool ↦ h (maxSelector hr a y) = true) =
              bernoulliEventProb p (fun y : Fin ℓ → Bool ↦ dFn y = true) :=
            bernoulliEventProb_congr fun y ↦ by rw [congrFun hcomp_eq y]
          rw [hcomp_eq, hev_eq, h0]
          simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
          exact pBiasedTotalInfluence_or_subset_le hp0.le hp1 Aset
        · push Not at hex
          have hall : ∀ z : Fin r, h z = false := fun z ↦ Bool.not_eq_true (h z) ▸ hex z
          have hconst : (fun y : Fin ℓ → Bool ↦ h (maxSelector hr a y)) = fun _ ↦ false :=
            funext fun _ ↦ hall _
          have hev : bernoulliEventProb p (fun y : Fin ℓ → Bool ↦
              h (maxSelector hr a y) = true) = 0 := by
            classical
            simp [bernoulliEventProb, hall]
          rw [hconst, hev, h0]
          simp [pBiasedTotalInfluence, pBiasedCoordInfluence]
    -- Sum `h1d_inf` across all `j : Fin n` and compare `A^n` vs `U^n`.
    have hinf_A : pBiasedTotalInfluence p g ≤
        2 * ∑ j : Fin n,
          (bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦ f (decode y) = true) -
            bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦
              f (Function.update (decode y) j ⟨0, hr⟩) = true)) := by
      have hsum_eq : pBiasedTotalInfluence p g =
          ∑ j : Fin n, ∑ k : Fin ℓ, pBiasedCoordInfluence p (finProdFinEquiv (j, k)) g := by
        rw [pBiasedTotalInfluence, ← Fintype.sum_equiv finProdFinEquiv
          (fun jk ↦ pBiasedCoordInfluence p (finProdFinEquiv jk) g)
          (fun idx ↦ pBiasedCoordInfluence p idx g) (fun _ ↦ rfl)]
        exact Fintype.sum_prod_type _
      rw [hsum_eq, mul_sum]
      refine sum_le_sum fun j _ ↦ ?_
      let splitN : (Fin n → Fin ℓ → Bool) ≃
          (Fin ℓ → Bool) × ({j' : Fin n // j' ≠ j} → Fin ℓ → Bool) :=
        (Equiv.piEquivPiSubtypeProd (fun j' : Fin n ↦ j' = j) (fun _ ↦ Fin ℓ → Bool)).trans
          (Equiv.prodCongr (Equiv.funUnique {j' : Fin n // j' = j} (Fin ℓ → Bool)) (Equiv.refl _))
      have hprob_split : ∀ (bj : Fin ℓ → Bool) (rest : {j' : Fin n // j' ≠ j} → Fin ℓ → Bool),
          bernoulliProb p (blocksEquiv.symm (splitN.symm (bj, rest))) =
            bernoulliProb p bj * ∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j') := by
        intro bj rest
        rw [bernoulliProb_prod_equiv finProdFinEquiv p]
        have hblk_prod : (∏ j' : Fin n, bernoulliProb p
            (fun k : Fin ℓ ↦ blocksEquiv.symm (splitN.symm (bj, rest))
              (finProdFinEquiv (j', k)))) =
            ∏ j' : Fin n, bernoulliProb p (splitN.symm (bj, rest) j') := by
          refine prod_congr rfl fun j' _ ↦ congrArg (bernoulliProb p) ?_
          exact congrFun (blocksEquiv.apply_symm_apply _) j'
        rw [hblk_prod, ← prod_sdiff (subset_univ ({j} : Finset (Fin n))), prod_singleton, mul_comm]
        have hbj : splitN.symm (bj, rest) j = bj := by simp [splitN, Equiv.piEquivPiSubtypeProd]
        rw [hbj]
        congr 1
        let eSub : {j' : Fin n // j' ≠ j} ≃ {j' : Fin n // j' ∈ univ \ ({j} : Finset (Fin n))} :=
          { toFun := fun ⟨j', hj'⟩ ↦ ⟨j', by simp [hj']⟩
            invFun := fun ⟨j', hj'⟩ ↦ ⟨j', by simpa using hj'⟩
            left_inv := fun ⟨_, _⟩ ↦ rfl
            right_inv := fun ⟨_, _⟩ ↦ rfl }
        rw [← prod_coe_sort (univ \ ({j} : Finset (Fin n)))
          (fun j' ↦ bernoulliProb p (splitN.symm (bj, rest) j'))]
        refine Fintype.prod_equiv eSub.symm
          (fun k ↦ bernoulliProb p (splitN.symm (bj, rest) k.1))
          (fun j' ↦ bernoulliProb p (rest j')) fun k ↦ ?_
        have hne : k.1 ≠ j := fun h ↦ (mem_sdiff.mp k.2).2 (mem_singleton.mpr h)
        have hrest : splitN.symm (bj, rest) k.1 = rest (eSub.symm k) := by
          simp [splitN, eSub, Equiv.piEquivPiSubtypeProd, hne]
        rw [hrest]
      have hdecode_split : ∀ (bj : Fin ℓ → Bool) (rest : {j' : Fin n // j' ≠ j} → Fin ℓ → Bool),
          decode (blocksEquiv.symm (splitN.symm (bj, rest))) =
            Function.update
              (fun j' : Fin n ↦ if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩))
              j (maxSelector hr a bj) := by
        intro bj rest; funext j'
        have hblk : slice (blocksEquiv.symm (splitN.symm (bj, rest))) j' =
            splitN.symm (bj, rest) j' := congrFun (blocksEquiv.apply_symm_apply _) j'
        simp only [decode, hblk]
        by_cases hjj' : j' = j
        · subst hjj'; simp [splitN, Equiv.piEquivPiSubtypeProd]
        · simp [Function.update, hjj', splitN, Equiv.piEquivPiSubtypeProd]
      have hlhs : (∑ k : Fin ℓ, pBiasedCoordInfluence p (finProdFinEquiv (j, k)) g) =
          ∑ rest : {j' : Fin n // j' ≠ j} → Fin ℓ → Bool,
            (∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j')) *
              pBiasedTotalInfluence p (fun bj : Fin ℓ → Bool ↦
                f (Function.update
                  (fun j' : Fin n ↦
                    if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩))
                  j (maxSelector hr a bj))) := by
        classical
        simp only [pBiasedCoordInfluence_eq_two_mul_pivotal, bernoulliEventProb, mul_sum,
          pBiasedTotalInfluence]
        conv_lhs =>
          arg 2; ext k
          rw [← blocksEquiv.symm.sum_comp, ← splitN.symm.sum_comp, Fintype.sum_prod_type]
        rw [sum_comm]
        conv_lhs => arg 2; ext bj; rw [sum_comm]
        rw [sum_comm]
        refine sum_congr rfl fun rest _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun k _ ↦ ?_
        refine sum_congr rfl fun bj _ ↦ ?_
        have hupd_b : ∀ b : Bool,
            decode (Function.update (blocksEquiv.symm (splitN.symm (bj, rest)))
              (finProdFinEquiv (j, k)) b) =
            Function.update
              (fun j' : Fin n ↦ if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩))
              j (maxSelector hr a (Function.update bj k b)) := by
          intro b
          have heq_b : Function.update (blocksEquiv.symm (splitN.symm (bj, rest)))
              (finProdFinEquiv (j, k)) b =
              blocksEquiv.symm (splitN.symm (Function.update bj k b, rest)) := by
            apply blocksEquiv.injective
            rw [blocksEquiv.apply_symm_apply]
            funext j' k'
            by_cases hjj' : j' = j
            · subst hjj'
              by_cases hkk' : k' = k
              · subst hkk'; simp [blocksEquiv, slice, splitN, Equiv.piEquivPiSubtypeProd]
              · have hne : finProdFinEquiv (j', k') ≠ finProdFinEquiv (j', k) := fun h ↦
                  hkk' (Prod.mk.inj (finProdFinEquiv.injective h)).2
                change Function.update (blocksEquiv.symm (splitN.symm (bj, rest)))
                    (finProdFinEquiv (j', k)) b (finProdFinEquiv (j', k')) = _
                rw [Function.update_of_ne hne]
                have := congrFun (congrFun (blocksEquiv.apply_symm_apply
                  (splitN.symm (bj, rest))) j') k'
                simpa [blocksEquiv, slice, splitN, Equiv.piEquivPiSubtypeProd, hkk'] using this
            · have hne : finProdFinEquiv (j', k') ≠ finProdFinEquiv (j, k) := fun h ↦
                hjj' (Prod.mk.inj (finProdFinEquiv.injective h)).1
              change Function.update (blocksEquiv.symm (splitN.symm (bj, rest)))
                  (finProdFinEquiv (j, k)) b (finProdFinEquiv (j', k')) = _
              rw [Function.update_of_ne hne]
              have := congrFun (congrFun (blocksEquiv.apply_symm_apply
                (splitN.symm (bj, rest))) j') k'
              simpa [blocksEquiv, slice, splitN, Equiv.piEquivPiSubtypeProd, hjj'] using this
          rw [heq_b, hdecode_split]
        simp only [g, hupd_b true, hupd_b false, hprob_split bj rest]
        split_ifs <;> ring
      have hrhs : bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦ f (decode y) = true) -
          bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦
            f (Function.update (decode y) j ⟨0, hr⟩) = true) =
          ∑ rest : {j' : Fin n // j' ≠ j} → Fin ℓ → Bool,
            (∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j')) *
              (bernoulliEventProb p (fun bj : Fin ℓ → Bool ↦
                  f (Function.update
                    (fun j' : Fin n ↦
                      if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩))
                    j (maxSelector hr a bj)) = true) -
                if f (Function.update
                    (fun j' : Fin n ↦
                      if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩))
                    j ⟨0, hr⟩) = true then 1 else 0) := by
        have hbev_ite : ∀ {m : ℕ} (P : (Fin m → Bool) → Bool),
            bernoulliEventProb p (fun y ↦ P y = true) =
              ∑ y, if P y = true then bernoulliProb p y else 0 := by
          intro m P
          classical
          rw [bernoulliEventProb]
          exact sum_congr rfl fun y _ ↦ by split_ifs <;> rfl
        rw [hbev_ite, hbev_ite, ← sum_sub_distrib, ← blocksEquiv.symm.sum_comp,
          ← splitN.symm.sum_comp, Fintype.sum_prod_type, sum_comm]
        refine sum_congr rfl fun rest _ ↦ ?_
        let baseX : Fin n → Fin r := fun j' ↦
          if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩)
        rw [hbev_ite]
        have hsum_eq' :
            (∑ bj : Fin ℓ → Bool,
              ((if f (decode (blocksEquiv.symm (splitN.symm (bj, rest)))) = true then
                  bernoulliProb p (blocksEquiv.symm (splitN.symm (bj, rest))) else 0) -
                (if f (Function.update (decode (blocksEquiv.symm (splitN.symm (bj, rest))))
                    j ⟨0, hr⟩) = true then
                  bernoulliProb p (blocksEquiv.symm (splitN.symm (bj, rest))) else 0))) =
            ∑ bj : Fin ℓ → Bool,
              (∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j')) *
                ((if f (Function.update baseX j (maxSelector hr a bj)) = true then
                    bernoulliProb p bj else 0) -
                  bernoulliProb p bj *
                    (if f (Function.update baseX j ⟨0, hr⟩) = true then 1 else 0)) := by
          refine sum_congr rfl fun bj _ ↦ ?_
          rw [hdecode_split bj rest, hprob_split bj rest, Function.update_idem]
          split_ifs <;> ring
        rw [hsum_eq', ← mul_sum, sum_sub_distrib, ← sum_mul, sum_bernoulliProb, one_mul]
      rw [hlhs, hrhs, mul_sum]
      refine sum_le_sum fun rest _ ↦ ?_
      let baseX : Fin n → Fin r := fun j' ↦
        if h : j' = j then ⟨0, hr⟩ else maxSelector hr a (rest ⟨j', h⟩)
      have hhSlice : Monotone (fun z : Fin r ↦ f (Function.update baseX j z)) :=
        fun z₁ z₂ hz ↦ hf fun j' ↦ by
          by_cases hjj' : j' = j
          · subst hjj'; simpa using hz
          · simp [Function.update, hjj']
      have hw_nn : 0 ≤ ∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j') :=
        prod_nonneg fun j' _ ↦ bernoulliProb_nonneg hp0.le hp1 (rest j')
      have hb := h1d_inf (fun z ↦ f (Function.update baseX j z)) hhSlice
      calc (∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j')) *
            pBiasedTotalInfluence p (fun bj ↦ f (Function.update baseX j (maxSelector hr a bj)))
          ≤ (∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j')) *
              (2 * (bernoulliEventProb p (fun bj ↦
                  f (Function.update baseX j (maxSelector hr a bj)) = true) -
                if f (Function.update baseX j ⟨0, hr⟩) = true then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hb hw_nn
        _ = 2 * ((∏ j' : {j' : Fin n // j' ≠ j}, bernoulliProb p (rest j')) *
              (bernoulliEventProb p (fun bj ↦
                  f (Function.update baseX j (maxSelector hr a bj)) = true) -
                if f (Function.update baseX j ⟨0, hr⟩) = true then 1 else 0)) := by ring
    -- Bound each coordinate difference between `A^n` and `U^n` by `2 * p * r * n`.
    have hdiff_inf : (∑ j : Fin n,
          (bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦ f (decode y) = true) -
            bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦
              f (Function.update (decode y) j ⟨0, hr⟩) = true))) ≤
        uniformFinZeroDirInf hr n f + 2 * p * (r : ℝ) * (n : ℝ) ^ 2 := by
      unfold uniformFinZeroDirInf
      have hcoord_diff : ∀ j : Fin n,
          bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦ f (decode y) = true) -
            bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦
              f (Function.update (decode y) j ⟨0, hr⟩) = true) ≤
          (uniformFinExpect r n f -
            uniformFinExpect r n (fun x ↦ f (Function.update x j ⟨0, hr⟩))) +
            2 * p * (r : ℝ) * (n : ℝ) := by
        intro j
        have hd1 : |bernoulliEventProb p (fun y ↦ f (decode y) = true) -
            uniformFinExpect r n f| ≤ p * (r : ℝ) * (n : ℝ) := by
          rw [hA_exp_eq f, hU_exp_eq f]; exact (hbool_dpi _ _ f).trans hdist_pi
        have hd2 : |bernoulliEventProb p (fun y ↦
              f (Function.update (decode y) j ⟨0, hr⟩) = true) -
            uniformFinExpect r n (fun x ↦ f (Function.update x j ⟨0, hr⟩))| ≤
            p * (r : ℝ) * (n : ℝ) := by
          rw [hA_exp_eq (fun x ↦ f (Function.update x j ⟨0, hr⟩)),
            hU_exp_eq (fun x ↦ f (Function.update x j ⟨0, hr⟩))]
          exact (hbool_dpi _ _ _).trans hdist_pi
        linarith [(abs_le.mp hd1).2, (abs_le.mp hd2).1]
      calc (∑ j : Fin n,
            (bernoulliEventProb p (fun y ↦ f (decode y) = true) -
              bernoulliEventProb p (fun y ↦ f (Function.update (decode y) j ⟨0, hr⟩) = true)))
          ≤ ∑ j : Fin n,
              ((uniformFinExpect r n f -
                uniformFinExpect r n (fun x ↦ f (Function.update x j ⟨0, hr⟩))) +
                2 * p * (r : ℝ) * (n : ℝ)) := sum_le_sum fun j _ ↦ hcoord_diff j
        _ = (∑ j : Fin n,
              (uniformFinExpect r n f -
                uniformFinExpect r n (fun x ↦ f (Function.update x j ⟨0, hr⟩)))) +
              2 * p * (r : ℝ) * (n : ℝ) ^ 2 := by
            rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    linarith
  · -- Property 3: Coalition projection from `Fin (n * ℓ)` to `Fin n`.
    intro S hS
    let T : Finset (Fin n) := S.image (fun idx ↦ (finProdFinEquiv.symm idx).1)
    refine ⟨T, card_image_le, ?_⟩
    let S' : Finset (Fin (n * ℓ)) := univ.filter fun idx ↦ (finProdFinEquiv.symm idx).1 ∈ T
    have hSS' : S ⊆ S' := fun idx hidx ↦
      mem_filter.mpr ⟨mem_univ idx, mem_image_of_mem _ hidx⟩
    have hmono_S' : 1 - ε ≤ pBiasedCoalitionProb p S' true g := by
      refine hS.trans (bernoulliEventProb_mono hp0.le hp1 fun x ⟨y, hy⟩ ↦ ⟨S.piecewise y x, ?_⟩)
      convert hy using 2; funext idx
      by_cases hidx : idx ∈ S
      · simp [Finset.piecewise, hidx, hSS' hidx]
      · by_cases hS' : idx ∈ S' <;> simp [Finset.piecewise, hidx, hS']
    rw [pBiasedCoalitionProb_eq_of_monotone hg_mono] at hmono_S'
    have hA_T : 1 - ε ≤ bernoulliEventProb p (fun y : Fin (n * ℓ) → Bool ↦
        f (T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) (decode y)) = true) := by
      refine hmono_S'.trans (bernoulliEventProb_mono hp0.le hp1 fun y hy ↦ ?_)
      have hle : decode (S'.piecewise (fun _ ↦ true) y) ≤
          T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) (decode y) := by
        intro j
        by_cases hjT : j ∈ T
        · simp only [Finset.piecewise, hjT, ↓reduceIte, Fin.le_iff_val_le_val]; omega
        · simp only [Finset.piecewise, hjT, ↓reduceIte, decode]
          have hblk_eq : slice (S'.piecewise (fun _ ↦ true) y) j = slice y j := by
            funext k
            have hnotS' : finProdFinEquiv (j, k) ∉ S' := by
              rw [mem_filter]; rintro ⟨_, hmem⟩
              rw [Equiv.symm_apply_apply] at hmem; exact hjT hmem
            simp [slice, hnotS']
          rw [hblk_eq]
      exact top_le_iff.mp (hy.symm.trans_le (hf hle))
    unfold uniformFinTopForcing
    have hdiff : |bernoulliEventProb p (fun y ↦
          f (T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) (decode y)) = true) -
        uniformFinExpect r n (fun x ↦ f (T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) x))| ≤
        p * (r : ℝ) * (n : ℝ) := by
      rw [hA_exp_eq (fun x ↦ f (T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) x)),
        hU_exp_eq (fun x ↦ f (T.piecewise (fun _ ↦ ⟨r - 1, by omega⟩) x))]
      exact (hbool_dpi _ _ _).trans hdist_pi
    linarith [(abs_le.mp hdiff).2]

end MaxSelectorEncoding

end CslibFrontier.BooleanAnalysis
