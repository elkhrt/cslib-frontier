/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Distributional.Distinguishing
public import CslibFrontier.Probability.StatisticalDistance.TotalVariation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Prefix-Conditioned Binary-Tree Bitstring Samplers and Product Bit Channels

A prefix-conditioned binary-tree sampler on `Fin n → Bool` specifies, at every bit prefix
`u : Σ d : Fin n, (Fin d.val → Bool)`, the conditional probability `R u ∈ [0, 1]` of emitting
`false` (`0`) versus `1 - R u` of emitting `true` (`1`). Walking from the empty prefix to depth `n`
via `n` sequential Bernoulli choices defines a discrete probability distribution
`prefixTreePMF R hR : PMF (Fin n → Bool)` whose point mass at `x` factors as the path product
`∏ k : Fin n, if x k then 1 - R (bitPrefix x k) else R (bitPrefix x k)`.

We also formalize post-composition of any bitstring `PMF` with independent per-coordinate binary
channels `(k : Fin n) → Bool → PMF Bool` (`applyProductBitChannel`), proving the exact marginal
convolution formula, and establish zero distinguishing advantage in
`Cslib.Probability.DistinguishingProblem` whenever two samplers induce the same observation `PMF`.

## Main definitions

* `CslibFrontier.Probability.BitPrefix`: internal binary-tree prefixes
  `Σ d : Fin n, Fin d.val → Bool`.
* `CslibFrontier.Probability.bitPrefix`: length-`k` prefix of `x : Fin n → Bool`.
* `CslibFrontier.Probability.prefixTreeProb`: multiplicative path probability along
  `x : Fin n → Bool`.
* `CslibFrontier.Probability.prefixTreePMF`: sequential `n`-step `PMF (Fin n → Bool)` tree walk.
* `CslibFrontier.Probability.applyProductBitChannel`: independent per-bit noisy `PMF` channel.

## Main results

* `CslibFrontier.Probability.prefixTreePMF_apply`: exact equality between `prefixTreePMF` and
  `ENNReal.ofReal (prefixTreeProb R x)`.
* `CslibFrontier.Probability.sum_prefixTreeProb_eq_one`: path products sum to `1` over all
  `x : Fin n → Bool` for arbitrary real branch parameters.
* `CslibFrontier.Probability.applyProductBitChannel_apply`: exact product-channel transition law
  `∑ x, p x * ∏ k, C k (x k) (y k)`.
* `CslibFrontier.Probability.dist_experiment_eq_zero_of_nullDist_eq`: zero total-variation
  distinguishing distance for all randomized tests when `nullDist = alternativeDist`.
-/

public section

noncomputable section

open scoped BigOperators NNReal ENNReal Cslib.Probability.PMF

namespace CslibFrontier.Probability

/-- Internal prefix node of a depth-`n` binary decision tree, consisting of a depth `d < n` and a
prefix `Fin d.val → Bool`. -/
abbrev BitPrefix (n : ℕ) : Type := Σ d : Fin n, Fin d.val → Bool

/-- Prefix of `x : Fin n → Bool` of length `k < n`. -/
def bitPrefix {n : ℕ} (x : Fin n → Bool) (k : Fin n) : BitPrefix n :=
  ⟨k, fun j ↦ x ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩⟩

/-- Root prefix at depth `0` in a tree of depth `n + 1`. -/
def rootBitPrefix (n : ℕ) : BitPrefix (n + 1) :=
  ⟨0, Fin.elim0⟩

/-- Left (`false`) child embedding of a `BitPrefix n` into `BitPrefix (n + 1)`. -/
def leftBitPrefix {n : ℕ} (u : BitPrefix n) : BitPrefix (n + 1) :=
  ⟨u.1.succ, Fin.cons false u.2⟩

/-- Right (`true`) child embedding of a `BitPrefix n` into `BitPrefix (n + 1)`. -/
def rightBitPrefix {n : ℕ} (u : BitPrefix n) : BitPrefix (n + 1) :=
  ⟨u.1.succ, Fin.cons true u.2⟩

/-- Single-step branch factor at depth `k`, equal to `R (bitPrefix x k)` when `x k = false` and
`1 - R (bitPrefix x k)` when `x k = true`. -/
def prefixBranchFactor {n : ℕ} (R : BitPrefix n → ℝ) (x : Fin n → Bool) (k : Fin n) : ℝ :=
  if x k then 1 - R (bitPrefix x k) else R (bitPrefix x k)

/-- Multiplicative leaf probability `∏ k : Fin n, prefixBranchFactor R x k` along root-to-leaf
path `x`. -/
def prefixTreeProb {n : ℕ} (R : BitPrefix n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ k : Fin n, prefixBranchFactor R x k

/-- Left-branch recursion for `prefixTreeProb` on `Fin.cons false w`. -/
theorem prefixTreeProb_cons_false {n : ℕ} (R : BitPrefix (n + 1) → ℝ) (w : Fin n → Bool) :
    prefixTreeProb R (Fin.cons false w) =
      R (rootBitPrefix n) * prefixTreeProb (fun u ↦ R (leftBitPrefix u)) w := by
  unfold prefixTreeProb
  rw [Fin.prod_univ_succ]
  congr 1
  · have h0 : bitPrefix (Fin.cons false w) 0 = rootBitPrefix n := by
      ext
      · rfl
      · exact Fin.heq_fun_iff rfl |>.mpr fun j ↦ Fin.elim0 j
    simp [prefixBranchFactor, h0]
  · refine Finset.prod_congr rfl fun k _ ↦ ?_
    have hk : bitPrefix (Fin.cons false w) k.succ = leftBitPrefix (bitPrefix w k) := by
      ext
      · rfl
      · refine Fin.heq_fun_iff rfl |>.mpr fun j ↦ ?_
        refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl
    simp [prefixBranchFactor, hk]

/-- Right-branch recursion for `prefixTreeProb` on `Fin.cons true w`. -/
theorem prefixTreeProb_cons_true {n : ℕ} (R : BitPrefix (n + 1) → ℝ) (w : Fin n → Bool) :
    prefixTreeProb R (Fin.cons true w) =
      (1 - R (rootBitPrefix n)) * prefixTreeProb (fun u ↦ R (rightBitPrefix u)) w := by
  unfold prefixTreeProb
  rw [Fin.prod_univ_succ]
  congr 1
  · have h0 : bitPrefix (Fin.cons true w) 0 = rootBitPrefix n := by
      ext
      · rfl
      · exact Fin.heq_fun_iff rfl |>.mpr fun j ↦ Fin.elim0 j
    simp [prefixBranchFactor, h0]
  · refine Finset.prod_congr rfl fun k _ ↦ ?_
    have hk : bitPrefix (Fin.cons true w) k.succ = rightBitPrefix (bitPrefix w k) := by
      ext
      · rfl
      · refine Fin.heq_fun_iff rfl |>.mpr fun j ↦ ?_
        refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl
    simp [prefixBranchFactor, hk]

/-- Total path probability sums to `1` over `Fin n → Bool` for any real branch table `R`. -/
@[simp]
theorem sum_prefixTreeProb_eq_one {n : ℕ} (R : BitPrefix n → ℝ) :
    ∑ x : Fin n → Bool, prefixTreeProb R x = 1 := by
  induction n with
  | zero => simp [prefixTreeProb]
  | succ n ih =>
    let e : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) :=
      { toFun := fun bw ↦ Fin.cons bw.1 bw.2
        invFun := fun x ↦ (x 0, fun k ↦ x k.succ)
        left_inv := fun ⟨_, _⟩ ↦ by ext <;> rfl
        right_inv := fun x ↦ by funext k; refine Fin.cases ?_ (fun _ ↦ ?_) k <;> rfl }
    rw [← Equiv.sum_comp e]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, e, Equiv.coe_fn_mk,
      prefixTreeProb_cons_true, prefixTreeProb_cons_false, ← Finset.mul_sum, ih, mul_one]
    ring

/-- Path probabilities are nonnegative whenever every branch ratio lies in `[0, 1]`. -/
theorem prefixTreeProb_nonneg {n : ℕ} {R : BitPrefix n → ℝ}
    (hR : ∀ u, R u ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → Bool) :
    0 ≤ prefixTreeProb R x := by
  refine Finset.prod_nonneg fun k _ ↦ ?_
  have hk := hR (bitPrefix x k)
  cases h : x k <;> simp only [prefixBranchFactor, h, ↓reduceIte, Bool.false_eq_true]
  · exact hk.1
  · linarith [hk.2]

/-- Single-bit `PMF Bool` emitting `false` with probability `r` and `true` with probability
`1 - r`. -/
def leftBiasCoinPMF (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : PMF Bool :=
  ⟨fun b ↦ if b then ENNReal.ofReal (1 - r) else ENNReal.ofReal r, by
    convert hasSum_fintype (fun b : Bool ↦ if b then ENNReal.ofReal (1 - r) else ENNReal.ofReal r)
    simp [← ENNReal.ofReal_add (sub_nonneg.mpr hr.2) hr.1]⟩

@[simp]
theorem leftBiasCoinPMF_false (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    leftBiasCoinPMF r hr false = ENNReal.ofReal r := by
  change (if false then ENNReal.ofReal (1 - r) else ENNReal.ofReal r) = ENNReal.ofReal r
  simp

@[simp]
theorem leftBiasCoinPMF_true (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    leftBiasCoinPMF r hr true = ENNReal.ofReal (1 - r) := by
  change (if true then ENNReal.ofReal (1 - r) else ENNReal.ofReal r) = ENNReal.ofReal (1 - r)
  simp

/-- Sequential `n`-step prefix-tree bitstring sampler `PMF (Fin n → Bool)`. -/
def prefixTreePMF : {n : ℕ} → (R : BitPrefix n → ℝ) →
    (∀ u, R u ∈ Set.Icc (0 : ℝ) 1) → PMF (Fin n → Bool)
  | 0, _, _ => PMF.pure Fin.elim0
  | n + 1, R, hR =>
      (leftBiasCoinPMF (R (rootBitPrefix n)) (hR (rootBitPrefix n))).bind fun b ↦
        if b then
          (prefixTreePMF (fun u ↦ R (rightBitPrefix u))
            (fun u ↦ hR (rightBitPrefix u))).map (fun w ↦ Fin.cons true w)
        else
          (prefixTreePMF (fun u ↦ R (leftBitPrefix u))
            (fun u ↦ hR (leftBitPrefix u))).map (fun w ↦ Fin.cons false w)

/-- `prefixTreePMF` assigns exact probability `ENNReal.ofReal (prefixTreeProb R x)` to every
`x : Fin n → Bool`. -/
theorem prefixTreePMF_apply {n : ℕ} (R : BitPrefix n → ℝ)
    (hR : ∀ u, R u ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → Bool) :
    prefixTreePMF R hR x = ENNReal.ofReal (prefixTreeProb R x) := by
  induction n with
  | zero =>
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    subst hx
    simp [prefixTreePMF, prefixTreeProb]
  | succ n ih =>
    rw [prefixTreePMF, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have hx : x = Fin.cons (x 0) (fun k ↦ x k.succ) := by
      funext k; refine Fin.cases ?_ (fun _ ↦ ?_) k <;> rfl
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    have hcons_inj (b : Bool) {w₁ w₂ : Fin n → Bool}
        (h : (Fin.cons b w₁ : Fin (n + 1) → Bool) = Fin.cons b w₂) : w₁ = w₂ := by
      funext k
      simpa using congrFun h k.succ
    cases hb : x 0
    · have htrue_zero : ((prefixTreePMF (fun u ↦ R (rightBitPrefix u))
          (fun u ↦ hR (rightBitPrefix u))).map (fun w ↦ Fin.cons true w))
          (Fin.cons false (fun k ↦ x k.succ) : Fin (n + 1) → Bool) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        have hne : (Fin.cons false (fun k ↦ x k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons true w :=
          fun h ↦ by have h0 := congrFun h 0; simp at h0
        simp [hne]
      have hfalse_eq : ((prefixTreePMF (fun u ↦ R (leftBitPrefix u))
          (fun u ↦ hR (leftBitPrefix u))).map (fun w ↦ Fin.cons false w))
          (Fin.cons false (fun k ↦ x k.succ) : Fin (n + 1) → Bool) =
          ENNReal.ofReal (prefixTreeProb (fun u ↦ R (leftBitPrefix u)) (fun k ↦ x k.succ)) := by
        rw [PMF.map_apply, tsum_eq_single (fun k ↦ x k.succ)]
        · simp [ih]
        · intro w hw
          have hne : (Fin.cons false (fun k ↦ x k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons false w :=
            fun h ↦ hw (hcons_inj false h).symm
          simp [hne]
      simp only [↓reduceIte, Bool.false_eq_true, leftBiasCoinPMF_true, leftBiasCoinPMF_false,
        htrue_zero, mul_zero, zero_add, hfalse_eq, prefixTreeProb_cons_false]
      rw [ENNReal.ofReal_mul (hR (rootBitPrefix n)).1]
    · have hfalse_zero : ((prefixTreePMF (fun u ↦ R (leftBitPrefix u))
          (fun u ↦ hR (leftBitPrefix u))).map (fun w ↦ Fin.cons false w))
          (Fin.cons true (fun k ↦ x k.succ) : Fin (n + 1) → Bool) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        have hne : (Fin.cons true (fun k ↦ x k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons false w :=
          fun h ↦ by have h0 := congrFun h 0; simp at h0
        simp [hne]
      have htrue_eq : ((prefixTreePMF (fun u ↦ R (rightBitPrefix u))
          (fun u ↦ hR (rightBitPrefix u))).map (fun w ↦ Fin.cons true w))
          (Fin.cons true (fun k ↦ x k.succ) : Fin (n + 1) → Bool) =
          ENNReal.ofReal (prefixTreeProb (fun u ↦ R (rightBitPrefix u)) (fun k ↦ x k.succ)) := by
        rw [PMF.map_apply, tsum_eq_single (fun k ↦ x k.succ)]
        · simp [ih]
        · intro w hw
          have hne : (Fin.cons true (fun k ↦ x k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons true w :=
            fun h ↦ hw (hcons_inj true h).symm
          simp [hne]
      simp only [↓reduceIte, Bool.false_eq_true, leftBiasCoinPMF_true, leftBiasCoinPMF_false,
        hfalse_zero, mul_zero, add_zero, htrue_eq, prefixTreeProb_cons_true]
      rw [ENNReal.ofReal_mul (sub_nonneg.mpr (hR (rootBitPrefix n)).2)]

/-- Apply independent per-coordinate binary channels `C k : Bool → PMF Bool` to a bitstring `x`. -/
def productBitChannelKernel : {n : ℕ} → (Fin n → Bool → PMF Bool) →
    (Fin n → Bool) → PMF (Fin n → Bool)
  | 0, _, _ => PMF.pure Fin.elim0
  | _ + 1, C, x =>
      (C 0 (x 0)).bind fun b ↦
        (productBitChannelKernel (fun k ↦ C k.succ) (fun k ↦ x k.succ)).map (fun w ↦ Fin.cons b w)

/-- Transition probability of `productBitChannelKernel` factors as `∏ k, C k (x k) (y k)`. -/
theorem productBitChannelKernel_apply {n : ℕ} (C : Fin n → Bool → PMF Bool)
    (x y : Fin n → Bool) :
    productBitChannelKernel C x y = ∏ k : Fin n, C k (x k) (y k) := by
  induction n with
  | zero =>
    have hy : y = Fin.elim0 := Subsingleton.elim _ _
    subst hy
    simp [productBitChannelKernel]
  | succ n ih =>
    rw [productBitChannelKernel, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have hy : y = Fin.cons (y 0) (fun k ↦ y k.succ) := by
      funext k; refine Fin.cases ?_ (fun _ ↦ ?_) k <;> rfl
    conv_lhs => rw [hy]
    conv_rhs => rw [hy, Fin.prod_univ_succ]
    have hcons_inj (b : Bool) {w₁ w₂ : Fin n → Bool}
        (h : (Fin.cons b w₁ : Fin (n + 1) → Bool) = Fin.cons b w₂) : w₁ = w₂ := by
      funext k
      simpa using congrFun h k.succ
    cases hb : y 0
    · have htrue_zero : ((productBitChannelKernel (fun k ↦ C k.succ)
          (fun k ↦ x k.succ)).map (fun w ↦ Fin.cons true w))
          (Fin.cons false (fun k ↦ y k.succ) : Fin (n + 1) → Bool) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        have hne : (Fin.cons false (fun k ↦ y k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons true w :=
          fun h ↦ by have h0 := congrFun h 0; simp at h0
        simp [hne]
      have hfalse_eq : ((productBitChannelKernel (fun k ↦ C k.succ)
          (fun k ↦ x k.succ)).map (fun w ↦ Fin.cons false w))
          (Fin.cons false (fun k ↦ y k.succ) : Fin (n + 1) → Bool) =
          ∏ k : Fin n, C k.succ (x k.succ) (y k.succ) := by
        rw [PMF.map_apply, tsum_eq_single (fun k ↦ y k.succ)]
        · simp [ih]
        · intro w hw
          have hne : (Fin.cons false (fun k ↦ y k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons false w :=
            fun h ↦ hw (hcons_inj false h).symm
          simp [hne]
      simp [htrue_zero, hfalse_eq]
    · have hfalse_zero : ((productBitChannelKernel (fun k ↦ C k.succ)
          (fun k ↦ x k.succ)).map (fun w ↦ Fin.cons false w))
          (Fin.cons true (fun k ↦ y k.succ) : Fin (n + 1) → Bool) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        have hne : (Fin.cons true (fun k ↦ y k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons false w :=
          fun h ↦ by have h0 := congrFun h 0; simp at h0
        simp [hne]
      have htrue_eq : ((productBitChannelKernel (fun k ↦ C k.succ)
          (fun k ↦ x k.succ)).map (fun w ↦ Fin.cons true w))
          (Fin.cons true (fun k ↦ y k.succ) : Fin (n + 1) → Bool) =
          ∏ k : Fin n, C k.succ (x k.succ) (y k.succ) := by
        rw [PMF.map_apply, tsum_eq_single (fun k ↦ y k.succ)]
        · simp [ih]
        · intro w hw
          have hne : (Fin.cons true (fun k ↦ y k.succ) : Fin (n + 1) → Bool) ≠ Fin.cons true w :=
            fun h ↦ hw (hcons_inj true h).symm
          simp [hne]
      simp [hfalse_zero, htrue_eq]

/-- Post-compose a bitstring distribution `p : PMF (Fin n → Bool)` with independent per-coordinate
binary channels `C`. -/
def applyProductBitChannel {n : ℕ} (C : Fin n → Bool → PMF Bool)
    (p : PMF (Fin n → Bool)) : PMF (Fin n → Bool) :=
  p.bind (productBitChannelKernel C)

/-- Marginal output probability under `applyProductBitChannel` equals
`∑ x, p x * ∏ k, C k (x k) (y k)`. -/
theorem applyProductBitChannel_apply {n : ℕ} (C : Fin n → Bool → PMF Bool)
    (p : PMF (Fin n → Bool)) (y : Fin n → Bool) :
    applyProductBitChannel C p y = ∑ x : Fin n → Bool, p x * ∏ k : Fin n, C k (x k) (y k) := by
  rw [applyProductBitChannel, PMF.bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [productBitChannelKernel_apply]

/-- When `P.nullDist = P.alternativeDist`, every randomized test in
`Cslib.Probability.DistinguishingProblem` produces identical output distributions under both
hypotheses and has total-variation distance `0`. -/
theorem dist_experiment_eq_zero_of_nullDist_eq {Input : Type*}
    {P : Cslib.Probability.DistinguishingProblem Input}
    (h : P.nullDist = P.alternativeDist) (test : Input → PMF Bool) :
    P.experiment false test = P.experiment true test ∧
      dist (P.experiment false test) (P.experiment true test) = 0 := by
  have hexp : P.experiment false test = P.experiment true test := by
    simp [h]
  exact ⟨hexp, by rw [hexp, dist_self]⟩

end CslibFrontier.Probability
