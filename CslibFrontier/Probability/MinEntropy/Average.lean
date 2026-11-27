module

/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import CslibFrontier.Probability.Collision
public import CslibFrontier.Probability.Conditioning
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.MinEntropy
public import CslibFrontier.Probability.Product
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Average Min-Entropy, Rényi-2 Entropy, and KL Extraction

This module provides textbook finite-distribution information-theoretic tools built over
`Cslib.Probability.PMF`:

* **Rényi-2 entropy** `renyiTwoEntropy`, satisfying `H_∞ ≤ H_2 ≤ H`.
* **Average min-entropy** `avgMinEntropy`, defined as
  `H̃_∞(A | B) = -log₂(𝔼_{b ~ B}[2^(-H_∞(A | B = b))])`, together with conditioning monotonicity,
  the Dodis–Ostrovsky–Reyzin–Smith chain rule, event conditioning, and the expected
  collision-probability bound `𝔼_b[‖p(·|b)‖₂²] ≤ 2^(-H̃_∞(A | B))`.
* **KL-to-min-entropy extraction** `exists_event_minEntropy_of_klDivBits_le`: any distribution `p`
  with `D_2(p ‖ q) ≤ t` (`t > 1`) admits for every `α > 2` an event `E` of probability at least
  `1 - 1 / α` on which `H_∞(p|_E) ≥ H_∞(q) - 2 α t`.
* **Bernoulli KL Chernoff bound** `bernoulli_chernoff_kl_le` and the linear lower bound
  `bernoulliKL_two_mul_ge` on `D_e(Ber(2p) ‖ Ber(p))`.

## Main definitions

* `Cslib.Probability.PMF.renyiTwoEntropy`: Rényi entropy of order 2 in bits.
* `Cslib.Probability.PMF.avgMinEntropy`: average conditional min-entropy in bits.
* `Cslib.Probability.PMF.klDivBits`: finite Kullback–Leibler divergence in bits.
* `Cslib.Probability.PMF.bernoulliKL`: Bernoulli KL divergence in nats.
* `Cslib.Probability.PMF.bernoulliPMF`: Bernoulli distribution `Ber(p)` on `Bool`.

## Main results

* `Cslib.Probability.PMF.minEntropy_le_renyiTwoEntropy`,
  `Cslib.Probability.PMF.renyiTwoEntropy_le_entropy`: Rényi entropy ordering `H_∞ ≤ H_2 ≤ H`.
* `Cslib.Probability.PMF.avgMinEntropy_conditioning_le`: conditioning decreases average
  min-entropy.
* `Cslib.Probability.PMF.avgMinEntropy_dors_ge`,
  `Cslib.Probability.PMF.avgMinEntropy_fst_le_pair`: Dodis–Ostrovsky–Reyzin–Smith chain rule.
* `Cslib.Probability.PMF.avgMinEntropy_cond_true_ge`: event conditioning lower bound.
* `Cslib.Probability.PMF.expected_collisionProbability_le_rpow_neg_avgMinEntropy`:
  expected `ℓ₂²` bound from average min-entropy.
* `Cslib.Probability.PMF.exists_event_minEntropy_of_klDivBits_le`: KL-to-min-entropy
  extraction.
* `Cslib.Probability.PMF.bernoulli_chernoff_kl_le`,
  `Cslib.Probability.PMF.bernoulliKL_two_mul_ge`: Bernoulli KL Chernoff bound and estimate.
-/

public section

namespace Cslib.Probability.PMF
open scoped BigOperators ENNReal

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Helper for multiplying `Finset.sup'` by a nonnegative scalar -/

private theorem mul_sup'_of_nonneg {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {c : ℝ} (hc : 0 ≤ c) (f : ι → ℝ) :
    c * s.sup' hs f = s.sup' hs (fun i => c * f i) := by
  apply le_antisymm
  · rcases eq_or_lt_of_le hc with rfl | hcpos
    · simp only [zero_mul]
      obtain ⟨i, hi⟩ := hs
      exact Finset.le_sup' (fun _ => (0 : ℝ)) hi
    · rw [mul_comm, ← le_div_iff₀ hcpos]
      refine Finset.sup'_le hs _ fun i hi => (le_div_iff₀ hcpos).mpr ?_
      rw [mul_comm]
      exact Finset.le_sup' (fun j => c * f j) hi
  · refine Finset.sup'_le hs _ fun i hi =>
      mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc

/-! ### Rényi-2 entropy -/

/-- Rényi entropy of order 2 in bits: `H₂(p) = -log₂(∑_a p(a)²)`. -/
noncomputable def renyiTwoEntropy (p : PMF α) : ℝ :=
  -Real.logb 2 (collisionProbability p)

/-- Min-entropy is at most Rényi-2 entropy: `H_∞(p) ≤ H₂(p)`. -/
theorem minEntropy_le_renyiTwoEntropy (p : PMF α) :
    minEntropy p ≤ renyiTwoEntropy p := by
  rw [renyiTwoEntropy]
  have hcol : collisionProbability p ≤ 2 ^ (-minEntropy p) :=
    collisionProbability_le_rpow_neg_minEntropy p
  have hpos : 0 < collisionProbability p := collisionProbability_pos p
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hcol
  rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hlog
  linarith

/-- Rényi-2 entropy is nonnegative. -/
theorem renyiTwoEntropy_nonneg (p : PMF α) : 0 ≤ renyiTwoEntropy p :=
  (minEntropy_nonneg p).trans (minEntropy_le_renyiTwoEntropy p)

/-- Rényi-2 entropy is at most Shannon entropy: `H₂(p) ≤ H(p)`. -/
theorem renyiTwoEntropy_le_entropy [Finite α] (p : PMF α) :
    renyiTwoEntropy p ≤ entropy p := by
  let _ := Fintype.ofFinite α
  rw [renyiTwoEntropy, collisionProbability_eq_sum, entropy_eq_sum_surprisal]
  set C : ℝ := ∑ a : α, (p a).toReal ^ 2
  have hpos : 0 < C := by
    change 0 < ∑ a : α, (p a).toReal ^ 2
    rw [← collisionProbability_eq_sum]
    exact collisionProbability_pos p
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Elementary proof via `log(x) ≤ x - 1` applied to `x = p(a) / C`:
  -- `∑ p(a) (log p(a) - log C) ≤ ∑ p(a) (p(a)/C - 1) = C/C - 1 = 0`.
  have hpt : ∀ a : α, (p a).toReal * Real.log (p a).toReal - (p a).toReal * Real.log C ≤
      (p a).toReal ^ 2 / C - (p a).toReal := by
    intro a
    by_cases ha : a ∈ p.support
    · have hpa : 0 < (p a).toReal := ENNReal.toReal_pos ha (PMF.apply_ne_top _ _)
      have hle := Real.log_le_sub_one_of_pos (div_pos hpa hpos)
      rw [Real.log_div hpa.ne' hpos.ne'] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hpa.le
      rw [show (p a).toReal * ((p a).toReal / C - 1) = (p a).toReal ^ 2 / C - (p a).toReal by
        ring] at hmul
      linarith
    · rw [(p.apply_eq_zero_iff a).mpr ha, ENNReal.toReal_zero]
      simp
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpt a
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
    sum_toReal, one_mul, div_self hpos.ne', sub_self] at hsum
  have hjensen : ∑ a : α, (p a).toReal * Real.log (p a).toReal ≤ Real.log C := by linarith
  have hdiv := div_le_div_of_nonneg_right hjensen hlog_pos.le
  rw [Finset.sum_div] at hdiv
  have hlhs : ∑ a : α, (p a).toReal * surprisal p a =
      -(∑ a : α, (p a).toReal * Real.log (p a).toReal / Real.log 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [surprisal, Real.logb, mul_neg, mul_div_assoc]
  rw [hlhs, Real.logb]
  linarith

/-! ### Average min-entropy -/

/-- On a nonempty finite type, `2 ^ (-minEntropy p)` equals the maximum probability mass. -/
theorem rpow_neg_minEntropy_eq_sup' [Fintype α] [Nonempty α] (p : PMF α) :
    (2 : ℝ) ^ (-minEntropy p) =
      Finset.univ.sup' Finset.univ_nonempty (fun a => (p a).toReal) := by
  apply le_antisymm
  · obtain ⟨a, ha, hsurp⟩ := exists_surprisal_eq_minEntropy p
    have hpa : (2 : ℝ) ^ (-minEntropy p) = (p a).toReal := by
      rw [← hsurp, surprisal, neg_neg,
        Real.rpow_logb (by norm_num) (by norm_num) (ENNReal.toReal_pos ha (PMF.apply_ne_top _ _))]
    rw [hpa]
    exact Finset.le_sup' (fun x => (p x).toReal) (Finset.mem_univ a)
  · refine Finset.sup'_le _ _ fun a _ => toReal_apply_le_rpow_neg_minEntropy p a

/-- The maximum probability mass of a finite distribution is strictly positive. -/
theorem sup'_toReal_pos [Fintype α] [Nonempty α] (p : PMF α) :
    0 < Finset.univ.sup' Finset.univ_nonempty (fun a => (p a).toReal) := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  exact lt_of_lt_of_le (ENNReal.toReal_pos ha (PMF.apply_ne_top _ _))
    (Finset.le_sup' (fun x => (p x).toReal) (Finset.mem_univ a))

/-- Average conditional min-entropy of the second component given the first, in bits:
`H̃_∞(A | B) = -log₂(𝔼_{b ~ B}[2^(-H_∞(A | B = b))])`. -/
noncomputable def avgMinEntropy [Finite β] (joint : PMF (β × α)) : ℝ :=
  (let _ := Fintype.ofFinite β;
    -Real.logb 2 (∑ b : β, ((joint.map Prod.fst) b).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b))))

/-- Finite-sum formula for `avgMinEntropy` independent of the `Fintype` instance. -/
theorem avgMinEntropy_eq_sum [Fintype β] (joint : PMF (β × α)) :
    avgMinEntropy joint = -Real.logb 2
      (∑ b : β, ((joint.map Prod.fst) b).toReal *
        (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b))) := by
  rw [avgMinEntropy, Subsingleton.elim (Fintype.ofFinite β) ‹Fintype β›]

/-- The inner expectation `∑_b p(b) · 2^(-H_∞(A | B = b))` is strictly positive. -/
theorem avgMinEntropy_inner_pos [Fintype β] (joint : PMF (β × α)) :
    0 < ∑ b : β, ((joint.map Prod.fst) b).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b)) := by
  obtain ⟨b₀, hb₀⟩ := (joint.map Prod.fst).support_nonempty
  have hterm : 0 < ((joint.map Prod.fst) b₀).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b₀)) :=
    mul_pos (ENNReal.toReal_pos hb₀ (PMF.apply_ne_top _ _)) (by positivity)
  have hle : ((joint.map Prod.fst) b₀).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b₀)) ≤
      ∑ b : β, ((joint.map Prod.fst) b).toReal *
        (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b)) :=
    Finset.single_le_sum
      (f := fun b : β => ((joint.map Prod.fst) b).toReal *
        (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b)))
      (fun b _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)) (Finset.mem_univ b₀)
  exact lt_of_lt_of_le hterm hle

/-- The inner expectation `∑_b p(b) · 2^(-H_∞(A | B = b))` is at most `1`. -/
theorem avgMinEntropy_inner_le_one [Fintype β] (joint : PMF (β × α)) :
    ∑ b : β, ((joint.map Prod.fst) b).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b)) ≤ 1 := by
  calc ∑ b : β, ((joint.map Prod.fst) b).toReal *
        (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b))
      ≤ ∑ b : β, ((joint.map Prod.fst) b).toReal * 1 := by
        refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (neg_nonpos.mpr (minEntropy_nonneg _))
    _ = 1 := by simp only [mul_one, sum_toReal]

/-- Characterization of `2 ^ (-avgMinEntropy joint)` as the average of `2 ^ (-minEntropy)`. -/
theorem rpow_neg_avgMinEntropy [Fintype β] (joint : PMF (β × α)) :
    (2 : ℝ) ^ (-avgMinEntropy joint) =
      ∑ b : β, ((joint.map Prod.fst) b).toReal *
        (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b)) := by
  rw [avgMinEntropy_eq_sum, neg_neg,
    Real.rpow_logb (by norm_num) (by norm_num) (avgMinEntropy_inner_pos joint)]

/-- Formula expressing `avgMinEntropy` via `sup'` of conditional probability masses. -/
theorem avgMinEntropy_eq_neg_logb_sum_sup' [Fintype β] [Fintype α] [Nonempty α]
    (joint : PMF (β × α)) :
    avgMinEntropy joint = -Real.logb 2
      (∑ b : β, ((joint.map Prod.fst) b).toReal *
        Finset.univ.sup' Finset.univ_nonempty (fun a => (conditionalSnd joint b a).toReal)) := by
  rw [avgMinEntropy_eq_sum]
  congr 2
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rpow_neg_minEntropy_eq_sup']

/-- Formula expressing `2 ^ (-avgMinEntropy joint)` directly in terms of joint masses:
`∑_b max_a Pr[B = b, A = a]`. -/
theorem rpow_neg_avgMinEntropy_eq_sum_sup'_joint [Fintype β] [Fintype α] [Nonempty α]
    (joint : PMF (β × α)) :
    (2 : ℝ) ^ (-avgMinEntropy joint) =
      ∑ b : β, Finset.univ.sup' Finset.univ_nonempty (fun a => (joint (b, a)).toReal) := by
  rw [rpow_neg_avgMinEntropy]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rpow_neg_minEntropy_eq_sup', mul_sup'_of_nonneg Finset.univ_nonempty ENNReal.toReal_nonneg]
  refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
  rw [← ENNReal.toReal_mul, marginal_mul_conditionalSnd]

/-- Average min-entropy is nonnegative. -/
theorem avgMinEntropy_nonneg [Finite β] (joint : PMF (β × α)) :
    0 ≤ avgMinEntropy joint := by
  let _ := Fintype.ofFinite β
  rw [avgMinEntropy_eq_sum, neg_nonneg]
  exact Real.logb_nonpos (by norm_num) (avgMinEntropy_inner_pos joint).le
    (avgMinEntropy_inner_le_one joint)

/-- Conditioning on a constant leaves average min-entropy equal to ordinary min-entropy. -/
theorem avgMinEntropy_map_const [Finite β] (p : PMF α) (b₀ : β) :
    avgMinEntropy (p.map (b₀, ·)) = minEntropy p := by
  classical
  let _ := Fintype.ofFinite β
  have hmarg : (p.map (b₀, ·)).map Prod.fst = PMF.pure b₀ := by
    rw [PMF.map_comp]; exact PMF.map_const p b₀
  have hcond : conditionalSnd (p.map (b₀, ·)) b₀ = p := by
    have hsupp : b₀ ∈ ((p.map (b₀, ·)).map Prod.fst).support := by simp [hmarg]
    ext a
    rw [conditionalSnd_apply _ _ hsupp, hmarg, PMF.pure_apply_self, div_one,
      PMF.map_apply, tsum_eq_single a fun a' ha' => by simp [Ne.symm ha']]
    simp
  rw [avgMinEntropy_eq_sum, hmarg]
  have hsum : ∑ b : β, ((PMF.pure b₀) b).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd (p.map (b₀, ·)) b)) =
      (2 : ℝ) ^ (-minEntropy p) := by
    rw [Finset.sum_eq_single b₀]
    · simp [hcond]
    · intro b _ hb; simp [PMF.pure_apply, hb]
    · intro h; exact absurd (Finset.mem_univ b₀) h
  rw [hsum, Real.logb_rpow (by norm_num) (by norm_num), neg_neg]

/-- Pointwise lower bounds on conditional min-entropy transfer to average min-entropy. -/
theorem avgMinEntropy_le_of_le [Finite β] (joint : PMF (β × α)) {k : ℝ}
    (h : ∀ b ∈ (joint.map Prod.fst).support, k ≤ minEntropy (conditionalSnd joint b)) :
    k ≤ avgMinEntropy joint := by
  let _ := Fintype.ofFinite β
  rw [avgMinEntropy_eq_sum, le_neg]
  rw [Real.logb_le_iff_le_rpow (by norm_num) (avgMinEntropy_inner_pos joint)]
  calc ∑ b : β, ((joint.map Prod.fst) b).toReal *
        (2 : ℝ) ^ (-minEntropy (conditionalSnd joint b))
      ≤ ∑ b : β, ((joint.map Prod.fst) b).toReal * (2 : ℝ) ^ (-k) := by
        refine Finset.sum_le_sum fun b _ => ?_
        by_cases hb : b ∈ (joint.map Prod.fst).support
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (h b hb)))
            ENNReal.toReal_nonneg
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hb]
    _ = (2 : ℝ) ^ (-k) := by rw [← Finset.sum_mul, sum_toReal, one_mul]

/-- Average min-entropy of independent variables equals the marginal min-entropy. -/
theorem avgMinEntropy_prod [Finite β] (p : PMF β) (q : PMF α) :
    avgMinEntropy (p.bind fun b => q.map (b, ·)) = minEntropy q := by
  let _ := Fintype.ofFinite β
  rw [avgMinEntropy_eq_sum]
  have hsum : ∑ b : β, (((p.bind fun b => q.map (b, ·)).map Prod.fst) b).toReal *
      (2 : ℝ) ^ (-minEntropy (conditionalSnd (p.bind fun b => q.map (b, ·)) b)) =
      (2 : ℝ) ^ (-minEntropy q) := by
    calc _ = ∑ b : β, (p b).toReal * (2 : ℝ) ^ (-minEntropy q) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases hb : b ∈ p.support
          · rw [map_fst_bind_pair, conditionalSnd_bind_pair p _ b hb]
          · rw [map_fst_bind_pair, (p.apply_eq_zero_iff b).mpr hb, ENNReal.toReal_zero,
              zero_mul, zero_mul]
      _ = (2 : ℝ) ^ (-minEntropy q) := by rw [← Finset.sum_mul, sum_toReal, one_mul]
  rw [hsum, Real.logb_rpow (by norm_num) (by norm_num), neg_neg]

/-- Injective re-encoding of the conditioning variable preserves `avgMinEntropy`. -/
theorem avgMinEntropy_map_fst_of_injective [Finite β] [Finite γ] [Finite α]
    (joint : PMF (β × α)) {e : β → γ} (he : Function.Injective e) :
    avgMinEntropy (joint.map (Prod.map e id)) = avgMinEntropy joint := by
  classical
  let _ := Fintype.ofFinite β
  let _ := Fintype.ofFinite γ
  let _ := Fintype.ofFinite α
  by_cases hne : Nonempty α
  · rw [avgMinEntropy_eq_sum, avgMinEntropy_eq_sum]
    congr 2
    rw [← rpow_neg_avgMinEntropy, ← rpow_neg_avgMinEntropy,
      rpow_neg_avgMinEntropy_eq_sum_sup'_joint, rpow_neg_avgMinEntropy_eq_sum_sup'_joint]
    have hzero : ∀ c : γ, c ∉ Set.range e →
        Finset.univ.sup' Finset.univ_nonempty
          (fun a => ((joint.map (Prod.map e id)) (c, a)).toReal) = 0 := by
      intro c hc
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun a _ => ?_
        have : (joint.map (Prod.map e id)) (c, a) = 0 := by
          rw [PMF.map_apply]
          refine tsum_eq_zero_iff.mpr fun ⟨b, a'⟩ => ?_
          split_ifs with h
          · exact absurd ⟨b, (Prod.mk.inj h).1.symm⟩ hc
          · rfl
        simp [this]
      · exact (ENNReal.toReal_nonneg).trans
          (Finset.le_sup' (fun x => ((joint.map (Prod.map e id)) (c, x)).toReal)
            (Finset.mem_univ hne.some))
    have hval : ∀ b : β,
        Finset.univ.sup' Finset.univ_nonempty
          (fun a => ((joint.map (Prod.map e id)) (e b, a)).toReal) =
        Finset.univ.sup' Finset.univ_nonempty (fun a => (joint (b, a)).toReal) := by
      intro b
      refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
      rw [PMF.map_apply, tsum_eq_single (b, a)]
      · simp
      · intro ⟨b', a'⟩ hne'
        split_ifs with h
        · have hb' : b' = b := he (Prod.mk.inj h).1.symm
          have ha' : a' = a := (Prod.mk.inj h).2.symm
          exact absurd (Prod.ext hb' ha') hne'
        · rfl
    calc ∑ c : γ, Finset.univ.sup' Finset.univ_nonempty
            (fun a => ((joint.map (Prod.map e id)) (c, a)).toReal)
        = ∑ c ∈ Finset.univ.image e, Finset.univ.sup' Finset.univ_nonempty
            (fun a => ((joint.map (Prod.map e id)) (c, a)).toReal) := by
          symm
          refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
          refine hzero c fun ⟨b, hb⟩ => hc (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)
      _ = ∑ b : β, Finset.univ.sup' Finset.univ_nonempty
            (fun a => ((joint.map (Prod.map e id)) (e b, a)).toReal) :=
          Finset.sum_image fun _ _ _ _ h => he h
      _ = ∑ b : β, Finset.univ.sup' Finset.univ_nonempty (fun a => (joint (b, a)).toReal) :=
          Finset.sum_congr rfl fun b _ => hval b
  · obtain ⟨⟨_, a⟩, _⟩ := joint.support_nonempty
    exact absurd ⟨a⟩ hne

/-- **Conditioning decreases average min-entropy**:
`H̃_∞(A | B, C) ≤ H̃_∞(A | B)`.
-/
theorem avgMinEntropy_conditioning_le [Finite β] [Finite γ] [Finite α]
    (joint : PMF ((β × γ) × α)) :
    avgMinEntropy joint ≤ avgMinEntropy (joint.map (fun t => (t.1.1, t.2))) := by
  classical
  let _ := Fintype.ofFinite β
  let _ := Fintype.ofFinite γ
  let _ := Fintype.ofFinite α
  have hne : Nonempty α := ⟨joint.support_nonempty.choose.2⟩
  rw [avgMinEntropy_eq_sum, avgMinEntropy_eq_sum, neg_le_neg_iff]
  refine Real.logb_le_logb_of_le (by norm_num) (avgMinEntropy_inner_pos _) ?_
  rw [← rpow_neg_avgMinEntropy, ← rpow_neg_avgMinEntropy,
    rpow_neg_avgMinEntropy_eq_sum_sup'_joint, rpow_neg_avgMinEntropy_eq_sum_sup'_joint]
  have hrow (b : β) :
      Finset.univ.sup' Finset.univ_nonempty
        (fun a => ((joint.map fun t => (t.1.1, t.2)) (b, a)).toReal) ≤
      ∑ c : γ, Finset.univ.sup' Finset.univ_nonempty (fun a => (joint ((b, c), a)).toReal) := by
    refine Finset.sup'_le _ _ fun a _ => ?_
    have hsum_eq : ((joint.map fun t => (t.1.1, t.2)) (b, a)).toReal =
        ∑ c : γ, (joint ((b, c), a)).toReal := by
      rw [PMF.map_apply, tsum_fintype,
        ENNReal.toReal_sum (fun x _ => by split_ifs <;> simp [PMF.apply_ne_top])]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp [Prod.mk.injEq, and_comm, ite_and, apply_ite ENNReal.toReal]
    rw [hsum_eq]
    exact Finset.sum_le_sum fun c _ => Finset.le_sup' (fun x => (joint ((b, c), x)).toReal)
      (Finset.mem_univ a)
  calc ∑ b : β, Finset.univ.sup' Finset.univ_nonempty
          (fun a => ((joint.map fun t => (t.1.1, t.2)) (b, a)).toReal)
      ≤ ∑ b : β, ∑ c : γ, Finset.univ.sup' Finset.univ_nonempty
          (fun a => (joint ((b, c), a)).toReal) :=
        Finset.sum_le_sum fun b _ => hrow b
    _ = ∑ bc : β × γ, Finset.univ.sup' Finset.univ_nonempty
          (fun a => (joint (bc, a)).toReal) :=
        (Fintype.sum_prod_type (fun bc : β × γ =>
          Finset.univ.sup' Finset.univ_nonempty (fun a => (joint (bc, a)).toReal))).symm

/-- **Dodis–Ostrovsky–Reyzin–Smith chain rule, first inequality**:
if `B` ranges over a finite type `β`, then `H̃_∞(A | B, C) ≥ H̃_∞(A, B | C) - log₂ |β|`.
-/
theorem avgMinEntropy_dors_ge [Fintype β] [Finite γ] [Finite α]
    (joint : PMF ((β × γ) × α)) :
    avgMinEntropy (joint.map (fun t => (t.1.2, (t.1.1, t.2)))) -
      Real.logb 2 (Fintype.card β) ≤ avgMinEntropy joint := by
  classical
  let _ := Fintype.ofFinite γ
  let _ := Fintype.ofFinite α
  have hneα : Nonempty α := ⟨joint.support_nonempty.choose.2⟩
  have hneβ : Nonempty β := ⟨joint.support_nonempty.choose.1.1⟩
  have hcard_pos : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hbound : (2 : ℝ) ^ (-avgMinEntropy joint) ≤
      (Fintype.card β : ℝ) *
        (2 : ℝ) ^ (-avgMinEntropy (joint.map (fun t => (t.1.2, (t.1.1, t.2))))) := by
    rw [rpow_neg_avgMinEntropy_eq_sum_sup'_joint, rpow_neg_avgMinEntropy_eq_sum_sup'_joint,
      Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    have hle : ∀ b : β,
        Finset.univ.sup' Finset.univ_nonempty (fun a => (joint ((b, c), a)).toReal) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun ba : β × α => ((joint.map fun t => (t.1.2, (t.1.1, t.2))) (c, ba)).toReal) := by
      intro b
      refine Finset.sup'_le _ _ fun a _ => ?_
      have heq : ((joint.map fun t => (t.1.2, (t.1.1, t.2))) (c, (b, a))).toReal =
          (joint ((b, c), a)).toReal := by
        congr 1
        rw [PMF.map_apply, tsum_eq_single ((b, c), a)]
        · simp
        · intro ⟨⟨b', c'⟩, a'⟩ hne
          by_cases h : (c, (b, a)) = (c', (b', a'))
          · simp only [Prod.mk.injEq] at h
            exact absurd (Prod.ext (Prod.ext h.2.1.symm h.1.symm) h.2.2.symm) hne
          · simp [h]
      rw [← heq]
      exact Finset.le_sup' (fun ba : β × α =>
        ((joint.map fun t => (t.1.2, (t.1.1, t.2))) (c, ba)).toReal) (Finset.mem_univ (b, a))
    calc ∑ b : β, Finset.univ.sup' Finset.univ_nonempty (fun a => (joint ((b, c), a)).toReal)
        ≤ ∑ _b : β, Finset.univ.sup' Finset.univ_nonempty
            (fun ba : β × α => ((joint.map fun t => (t.1.2, (t.1.1, t.2))) (c, ba)).toReal) :=
          Finset.sum_le_sum fun b _ => hle b
      _ = (Fintype.card β : ℝ) * Finset.univ.sup' Finset.univ_nonempty
            (fun ba : β × α => ((joint.map fun t => (t.1.2, (t.1.1, t.2))) (c, ba)).toReal) := by
          simp
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by rw [rpow_neg_avgMinEntropy]; exact avgMinEntropy_inner_pos joint) hbound
  rw [Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_mul hcard_pos.ne' (by positivity),
    Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  linarith

/-- **Dodis–Ostrovsky–Reyzin–Smith chain rule, second inequality**:
`H̃_∞(A | C) ≤ H̃_∞(A, B | C)`. -/
theorem avgMinEntropy_fst_le_pair [Finite γ] [Finite β] [Finite α]
    (joint : PMF (γ × β × α)) :
    avgMinEntropy (joint.map (fun t => (t.1, t.2.2))) ≤
      avgMinEntropy (joint.map (fun t => (t.1, (t.2.1, t.2.2)))) := by
  classical
  let _ := Fintype.ofFinite γ
  let _ := Fintype.ofFinite β
  let _ := Fintype.ofFinite α
  have hneα : Nonempty α := ⟨joint.support_nonempty.choose.2.2⟩
  have hneβ : Nonempty β := ⟨joint.support_nonempty.choose.2.1⟩
  have hbound : (2 : ℝ) ^ (-avgMinEntropy (joint.map (fun t => (t.1, (t.2.1, t.2.2))))) ≤
      (2 : ℝ) ^ (-avgMinEntropy (joint.map (fun t => (t.1, t.2.2)))) := by
    rw [rpow_neg_avgMinEntropy_eq_sum_sup'_joint, rpow_neg_avgMinEntropy_eq_sum_sup'_joint]
    refine Finset.sum_le_sum fun c _ => ?_
    refine Finset.sup'_le _ _ fun ⟨b, a⟩ _ => ?_
    have hle : ((joint.map fun t => (t.1, (t.2.1, t.2.2))) (c, (b, a))).toReal ≤
        ((joint.map fun t => (t.1, t.2.2)) (c, a)).toReal := by
      refine ENNReal.toReal_mono (PMF.apply_ne_top _ _) ?_
      rw [PMF.map_apply, PMF.map_apply]
      refine tsum_le_tsum fun t => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        exact h2 (Prod.ext (Prod.mk.inj h1).1 (Prod.mk.inj (Prod.mk.inj h1).2).2)
      · exact bot_le
      · exact le_rfl
    exact hle.trans (Finset.le_sup' (fun x => ((joint.map fun t => (t.1, t.2.2)) (c, x)).toReal)
      (Finset.mem_univ a))
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by rw [rpow_neg_avgMinEntropy]; exact avgMinEntropy_inner_pos _) hbound
  rw [Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  linarith

/-- **Event conditioning for average min-entropy**: conditioning on a positive-probability event
`E = true` lowers `H̃_∞(A | B, E = true)` from `H̃_∞(A | B, E)` by at most `-log₂ Pr[E = true]`. -/
theorem avgMinEntropy_cond_true_ge [Finite β] [Finite α]
    (joint : PMF ((Bool × β) × α))
    (htrue : true ∈ ((joint.map (fun t => t.1.1))).support) :
    Real.logb 2 (((joint.map fun t => t.1.1) true).toReal) + avgMinEntropy joint ≤
      avgMinEntropy (conditionalSnd (joint.map (fun t => (t.1.1, (t.1.2, t.2)))) true) := by
  classical
  let _ := Fintype.ofFinite β
  let _ := Fintype.ofFinite α
  have hneα : Nonempty α := ⟨joint.support_nonempty.choose.2⟩
  set J := joint.map (fun t => (t.1.1, (t.1.2, t.2)))
  have hJfst : J.map Prod.fst = joint.map (fun t => t.1.1) := by
    rw [PMF.map_comp]; rfl
  have htrueJ : true ∈ (J.map Prod.fst).support := by rwa [hJfst]
  have hp_pos : 0 < ((joint.map fun t => t.1.1) true).toReal :=
    ENNReal.toReal_pos htrue (PMF.apply_ne_top _ _)
  have hbound : ((joint.map fun t => t.1.1) true).toReal *
      (2 : ℝ) ^ (-avgMinEntropy (conditionalSnd J true)) ≤
      (2 : ℝ) ^ (-avgMinEntropy joint) := by
    rw [rpow_neg_avgMinEntropy_eq_sum_sup'_joint, rpow_neg_avgMinEntropy_eq_sum_sup'_joint,
      Fintype.sum_prod_type, Fintype.sum_bool, Finset.mul_sum]
    refine le_add_of_le_of_nonneg ?_ (Finset.sum_nonneg fun b _ =>
      (ENNReal.toReal_nonneg).trans
        (Finset.le_sup' (fun x => (joint ((false, b), x)).toReal) (Finset.mem_univ hneα.some)))
    refine Finset.sum_le_sum fun b _ => ?_
    rw [mul_sup'_of_nonneg Finset.univ_nonempty ENNReal.toReal_nonneg]
    refine le_of_eq (Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_)
    have hcond_eq : (conditionalSnd J true (b, a)).toReal =
        (joint ((true, b), a)).toReal / ((joint.map fun t => t.1.1) true).toReal := by
      rw [conditionalSnd_apply J true htrueJ, hJfst, ENNReal.toReal_div]
      congr 2
      rw [PMF.map_apply, tsum_eq_single ((true, b), a)]
      · simp
      · intro ⟨⟨e', b'⟩, a'⟩ hne
        by_cases h : (true, (b, a)) = (e', (b', a'))
        · simp only [Prod.mk.injEq] at h
          exact absurd (Prod.ext (Prod.ext h.1.symm h.2.1.symm) h.2.2.symm) hne
        · simp [h]
    rw [hcond_eq, mul_div_cancel₀ _ hp_pos.ne']
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos hp_pos (by positivity)) hbound
  rw [Real.logb_mul hp_pos.ne' (by positivity),
    Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  linarith

/-- **Expected collision probability bound**:
`𝔼_{b ~ B}[∑_a Pr[A = a | B = b]²] ≤ 2^(-H̃_∞(A | B))`.
-/
theorem expected_collisionProbability_le_rpow_neg_avgMinEntropy [Fintype β]
    (joint : PMF (β × α)) :
    ∑ b : β, ((joint.map Prod.fst) b).toReal * collisionProbability (conditionalSnd joint b) ≤
      (2 : ℝ) ^ (-avgMinEntropy joint) := by
  rw [rpow_neg_avgMinEntropy]
  refine Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (collisionProbability_le_rpow_neg_minEntropy _)
      ENNReal.toReal_nonneg

/-! ### KL-to-min-entropy extraction -/

/-- Finite Kullback–Leibler divergence in bits: `D_2(p ‖ q) = ∑_a p(a) log₂(p(a) / q(a))`. -/
noncomputable def klDivBits [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a : α, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal)

/-- KL divergence in bits equals KL divergence in nats divided by `log 2`. -/
theorem klDivBits_eq_sum_div_log_two [Fintype α] (p q : PMF α) :
    klDivBits p q = (∑ a : α, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) /
      Real.log 2 := by
  simp only [klDivBits, Real.logb, Finset.sum_div, mul_div_assoc]

/-- KL divergence in bits is nonnegative when `p.support ⊆ q.support`. -/
theorem klDivBits_nonneg [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    0 ≤ klDivBits p q := by
  rw [klDivBits_eq_sum_div_log_two]
  exact div_nonneg (sum_mul_log_div_nonneg h) (Real.log_nonneg (by norm_num))

/-- Auxiliary log-sum lower bound for a sub-probability restriction: for any event `E` with
`p.support ⊆ q.support`, `∑_{a ∈ E} p(a) log₂(p(a) / q(a)) ≥ p(E) log₂(p(E))`. -/
private theorem sum_filter_mul_logb_div_ge [Finite α] (p q : PMF α) (E : Finset α)
    (hsupp : p.support ⊆ q.support) :
    (∑ a ∈ E, (p a).toReal) * Real.logb 2 (∑ a ∈ E, (p a).toReal) ≤
      ∑ a ∈ E, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal) := by
  classical
  let _ := Fintype.ofFinite α
  set s := ∑ a ∈ E, (p a).toReal
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  by_cases hs : s = 0
  · have hzero : ∀ a ∈ E, (p a).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)).mp hs
    have hrhs : ∑ a ∈ E, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [hzero a ha, zero_mul]
    rw [hrhs, hs, zero_mul]
  have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs)
  set t := ∑ a ∈ E, (q a).toReal
  have ht_le_one : t ≤ 1 := by
    calc t ≤ ∑ a : α, (q a).toReal :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => ENNReal.toReal_nonneg
      _ = 1 := sum_toReal q
  let pE : PMF α := PMF.ofFintype (fun a => if a ∈ E then ENNReal.ofReal ((p a).toReal / s) else 0)
    (by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← ENNReal.ofReal_sum_of_nonneg fun _ _ => div_nonneg ENNReal.toReal_nonneg hs_pos.le,
        ← Finset.sum_div, div_self hs, ENNReal.ofReal_one])
  have hpE_supp : ∀ a, a ∈ pE.support ↔ a ∈ E ∧ a ∈ p.support := by
    intro a
    simp only [pE, PMF.mem_support_iff, PMF.ofFintype_apply]
    by_cases ha : a ∈ E
    · simp only [ha, ↓reduceIte, ne_eq, ENNReal.ofReal_eq_zero, not_le, true_and]
      exact ⟨fun h hz => by simp [hz] at h,
        fun h => div_pos (ENNReal.toReal_pos h (PMF.apply_ne_top _ _)) hs_pos⟩
    · simp [ha]
  have ht_pos : 0 < t := by
    have : ∃ a ∈ E, a ∈ p.support := by
      by_contra hall
      push Not at hall
      have : s = 0 := Finset.sum_eq_zero fun a ha => by
        rw [(p.apply_eq_zero_iff a).mpr (hall a ha), ENNReal.toReal_zero]
      exact hs this
    obtain ⟨a, haE, hap⟩ := this
    exact lt_of_lt_of_le (ENNReal.toReal_pos (hsupp hap) (PMF.apply_ne_top _ _))
      (Finset.single_le_sum (fun _ _ => ENNReal.toReal_nonneg) haE)
  let qE : PMF α := PMF.ofFintype (fun a => if a ∈ E then ENNReal.ofReal ((q a).toReal / t) else 0)
    (by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← ENNReal.ofReal_sum_of_nonneg fun _ _ => div_nonneg ENNReal.toReal_nonneg ht_pos.le,
        ← Finset.sum_div, div_self ht_pos.ne', ENNReal.ofReal_one])
  have hsub : pE.support ⊆ qE.support := by
    intro a ha
    obtain ⟨haE, hap⟩ := (hpE_supp a).mp ha
    simp only [qE, PMF.mem_support_iff, PMF.ofFintype_apply, haE, ↓reduceIte, ne_eq,
      ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (ENNReal.toReal_pos (hsupp hap) (PMF.apply_ne_top _ _)) ht_pos
  have hgibbs : 0 ≤ klDivBits pE qE := klDivBits_nonneg hsub
  have hexpand : s * klDivBits pE qE =
      (∑ a ∈ E, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal)) -
      s * Real.logb 2 (s / t) := by
    rw [klDivBits, Finset.mul_sum]
    have hrewrite : ∑ a : α, s * ((pE a).toReal * Real.logb 2 ((pE a).toReal / (qE a).toReal)) =
        ∑ a ∈ E, (p a).toReal * (Real.logb 2 ((p a).toReal / (q a).toReal) -
          Real.logb 2 (s / t)) := by
      rw [← Finset.sum_subset (Finset.subset_univ E) (fun a _ ha => by simp [pE, ha])]
      refine Finset.sum_congr rfl fun a ha => ?_
      by_cases hap : a ∈ p.support
      · have hpa : 0 < (p a).toReal := ENNReal.toReal_pos hap (PMF.apply_ne_top _ _)
        have hqa : 0 < (q a).toReal := ENNReal.toReal_pos (hsupp hap) (PMF.apply_ne_top _ _)
        have hpEa : (pE a).toReal = (p a).toReal / s := by
          simp [pE, ha, ENNReal.toReal_ofReal (div_nonneg hpa.le hs_pos.le)]
        have hqEa : (qE a).toReal = (q a).toReal / t := by
          simp [qE, ha, ENNReal.toReal_ofReal (div_nonneg hqa.le ht_pos.le)]
        rw [hpEa, hqEa, show s * ((p a).toReal / s *
            Real.logb 2 ((p a).toReal / s / ((q a).toReal / t))) =
            (p a).toReal * Real.logb 2 (((p a).toReal / (q a).toReal) / (s / t)) by
            field_simp,
          Real.logb_div (div_pos hpa hqa).ne' (div_pos hs_pos ht_pos).ne']
      · have hp0 : (p a).toReal = 0 := by rw [(p.apply_eq_zero_iff a).mpr hap, ENNReal.toReal_zero]
        have hpE0 : (pE a).toReal = 0 := by simp [pE, ha, hp0]
        rw [hp0, hpE0, zero_mul, zero_mul, mul_zero]
    rw [hrewrite]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rfl
  have hst : Real.logb 2 s ≤ Real.logb 2 (s / t) := by
    refine Real.logb_le_logb_of_le (by norm_num) hs_pos ?_
    exact (le_div_iff₀ ht_pos).mpr (mul_le_of_le_one_right hs_pos.le ht_le_one)
  have h1 : 0 ≤ s * klDivBits pE qE := mul_nonneg hs_pos.le hgibbs
  nlinarith

/-- Elementary real inequality used in KL-to-min-entropy extraction: for `u ∈ (0, 1/2)`,
`1 - u + (1 - u) * log₂(1 - u) > 0`. -/
private theorem one_sub_add_mul_logb_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    0 < 1 - u + (1 - u) * Real.logb 2 (1 - u) := by
  have h1u_pos : 0 < 1 - u := by linarith
  have hhalf : (1 / 2 : ℝ) < 1 - u := by linarith
  have hlog : -1 < Real.logb 2 (1 - u) := by
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    rwa [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)] at h
  nlinarith

/-- **KL-to-min-entropy extraction**:
if `D_2(p ‖ q) ≤ t` with `t > 1` and `α' > 2`, then there exists an event `E` with
`p(E) ≥ 1 - 1 / α'` and `H_∞(p|_E) ≥ H_∞(q) - 2 α' t`.
-/
theorem exists_event_minEntropy_of_klDivBits_le [Fintype α] (p q : PMF α) {t α' : ℝ}
    (ht : 1 < t) (hα : 2 < α') (hsupp : p.support ⊆ q.support) (hkl : klDivBits p q ≤ t) :
    ∃ E : Set α, ∃ hE : ∃ a ∈ E, a ∈ p.support,
      1 - 1 / α' ≤ (p.toOuterMeasure E).toReal ∧
      minEntropy q - 2 * α' * t ≤ minEntropy (p.filter E hE) := by
  classical
  let Efin : Finset α := Finset.univ.filter fun a =>
    Real.logb 2 ((p a).toReal / (q a).toReal) < 2 * α' * t - 1
  set E : Set α := (Efin : Set α)
  have hα_pos : 0 < α' := by linarith
  have h1_sub : 1 - 1 / α' ≤ (p.toOuterMeasure E).toReal := by
    by_contra hlt
    push Not at hlt
    set r := 1 - (p.toOuterMeasure E).toReal
    have hr_gt : 1 / α' < r := by linarith
    have hr_le : r ≤ 1 := by
      have : 0 ≤ (p.toOuterMeasure E).toReal := ENNReal.toReal_nonneg
      linarith
    have hpE : (p.toOuterMeasure E).toReal = ∑ a ∈ Efin, (p a).toReal := by
      rw [toOuterMeasure_apply_toReal]
      simp [E]
    have hpEc : r = ∑ a ∈ Efinᶜ, (p a).toReal := by
      have htot := Finset.sum_add_sum_compl Efin (fun a => (p a).toReal)
      rw [sum_toReal] at htot
      linarith [hpE]
    have hE_bound : (1 - r) * Real.logb 2 (1 - r) ≤
        ∑ a ∈ Efin, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal) := by
      simpa only [show ∑ a ∈ Efin, (p a).toReal = 1 - r by linarith] using
        sum_filter_mul_logb_div_ge p q Efin hsupp
    have hEc_bound : r * (2 * α' * t - 1) ≤
        ∑ a ∈ Efinᶜ, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal) := by
      calc r * (2 * α' * t - 1)
          = ∑ a ∈ Efinᶜ, (p a).toReal * (2 * α' * t - 1) := by rw [← Finset.sum_mul, hpEc]
        _ ≤ ∑ a ∈ Efinᶜ, (p a).toReal * Real.logb 2 ((p a).toReal / (q a).toReal) := by
          refine Finset.sum_le_sum fun a ha => ?_
          simp only [Efin, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
            not_lt] at ha
          exact mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
    have hkl_ge : r * (2 * α' * t - 1) + (1 - r) * Real.logb 2 (1 - r) ≤ klDivBits p q := by
      rw [klDivBits, ← Finset.sum_add_sum_compl Efin]
      linarith
    have hgt : t < r * (2 * α' * t - 1) + (1 - r) * Real.logb 2 (1 - r) := by
      set u := 1 / α'
      have hu_pos : 0 < u := by positivity
      have hu_half : u < 1 / 2 := (div_lt_div_iff₀ hα_pos (by norm_num)).mpr (by linarith)
      have hgu : t < u * (2 * α' * t - 1) + (1 - u) * Real.logb 2 (1 - u) := by
        have hmul : u * (2 * α' * t - 1) = 2 * t - u := by
          simp only [u]; field_simp
        rw [hmul]
        linarith [one_sub_add_mul_logb_pos hu_pos hu_half]
      by_cases hr1 : r = 1
      · rw [hr1]; norm_num; nlinarith
      · have h1r_pos : 0 < 1 - r := by
          have : r < 1 := lt_of_le_of_ne hr_le hr1
          linarith
        have h1u_pos : 0 < 1 - u := by linarith
        have hconv : (1 - u) * Real.log (1 - u) + (Real.log (1 - u) + 1) * (u - r) ≤
            (1 - r) * Real.log (1 - r) := by
          have hlog_le := Real.log_le_sub_one_of_pos (div_pos h1u_pos h1r_pos)
          rw [Real.log_div h1u_pos.ne' h1r_pos.ne'] at hlog_le
          have hmul2 := mul_le_mul_of_nonneg_left hlog_le h1r_pos.le
          rw [show (1 - r) * ((1 - u) / (1 - r) - 1) = r - u by field_simp; ring] at hmul2
          linarith
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hconv2 : (1 - u) * Real.logb 2 (1 - u) +
            (Real.logb 2 (1 - u) + 1 / Real.log 2) * (u - r) ≤
            (1 - r) * Real.logb 2 (1 - r) := by
          simp only [Real.logb]
          have hd := div_le_div_of_nonneg_right hconv hlog2_pos.le
          convert hd using 1 <;> ring
        have hlog1u_neg : Real.logb 2 (1 - u) ≤ 0 :=
          Real.logb_nonpos (by norm_num) h1u_pos.le (by linarith)
        have hinv_log2 : 1 / Real.log 2 < 2 := by
          have hln2 : (1 / 2 : ℝ) < Real.log 2 := by
            have := Real.log_two_gt_d9
            linarith
          exact (div_lt_iff₀ hlog2_pos).mpr (by linarith)
        have hslope : Real.logb 2 (1 - u) + 1 / Real.log 2 < 2 * α' * t - 1 := by
          nlinarith
        have hstep : 0 < (r - u) * (2 * α' * t - 1 - (Real.logb 2 (1 - u) + 1 / Real.log 2)) :=
          mul_pos (by linarith) (by linarith)
        nlinarith
    linarith
  have hE : ∃ a ∈ E, a ∈ p.support :=
    (toOuterMeasure_toReal_pos_iff p E).mp (by
      have h12 : 1 / α' < 1 / 2 := (div_lt_div_iff₀ hα_pos (by norm_num)).mpr (by linarith)
      linarith)
  refine ⟨E, hE, h1_sub, ?_⟩
  rw [le_minEntropy_iff]
  intro a
  rw [filter_apply_toReal]
  split_ifs with ha
  · have hE_half : (1 / 2 : ℝ) < (p.toOuterMeasure E).toReal := by
      have : 1 / α' < 1 / 2 := (div_lt_div_iff₀ hα_pos (by norm_num)).mpr (by linarith)
      linarith
    by_cases hap : a ∈ p.support
    · have hpa_pos : 0 < (p a).toReal := ENNReal.toReal_pos hap (PMF.apply_ne_top _ _)
      have hqa_pos : 0 < (q a).toReal := ENNReal.toReal_pos (hsupp hap) (PMF.apply_ne_top _ _)
      have ha_lt : Real.logb 2 ((p a).toReal / (q a).toReal) < 2 * α' * t - 1 := by
        simpa [E, Efin] using ha
      have hratio : (p a).toReal / (q a).toReal ≤ 2 ^ (2 * α' * t - 1) :=
        ((Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos hpa_pos hqa_pos)).mp ha_lt).le
      have hpa_le : (p a).toReal ≤ 2 ^ (2 * α' * t - 1) * (q a).toReal :=
        (div_le_iff₀ hqa_pos).mp hratio
      have hqa_le : (q a).toReal ≤ 2 ^ (-minEntropy q) := toReal_apply_le_rpow_neg_minEntropy q a
      calc (p a).toReal / (p.toOuterMeasure E).toReal
          ≤ (p a).toReal / (1 / 2) :=
            div_le_div_of_nonneg_left hpa_pos.le (by norm_num) hE_half.le
        _ = 2 * (p a).toReal := by ring
        _ ≤ 2 * (2 ^ (2 * α' * t - 1) * 2 ^ (-minEntropy q)) := by
            gcongr
            exact hpa_le.trans (mul_le_mul_of_nonneg_left hqa_le (by positivity))
        _ = 2 ^ (-(minEntropy q - 2 * α' * t)) := by
            have h2 : (2 : ℝ) * (2 ^ (2 * α' * t - 1) * 2 ^ (-minEntropy q)) =
                (2 : ℝ) ^ (1 : ℝ) * 2 ^ (2 * α' * t - 1) * 2 ^ (-minEntropy q) := by
              rw [Real.rpow_one, ← mul_assoc]
            rw [h2, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
            congr 1; ring
    · rw [(p.apply_eq_zero_iff a).mpr hap, ENNReal.toReal_zero, zero_div]
      positivity
  · positivity

/-! ### Bernoulli KL Chernoff bound -/

/-- Kullback–Leibler divergence between `Ber(q)` and `Ber(p)` in nats. -/
@[expose] noncomputable def bernoulliKL (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

/-- Lower bound `D_e(Ber(2pc) ‖ Ber(p)) ≥ c (2 ln 2 - 1) p` for `p > 0`, `c ≥ 1`, `2pc < 1`. -/
theorem bernoulliKL_two_mul_mul_ge {p c : ℝ} (hp0 : 0 < p) (hc : 1 ≤ c) (hq1 : 2 * p * c < 1) :
    c * (2 * Real.log 2 - 1) * p ≤ bernoulliKL (2 * p * c) p := by
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have h1p : 0 < 1 - p := by nlinarith
  have h1q : 0 < 1 - 2 * p * c := by linarith
  have hlog_tail : p - 2 * p * c ≤ (1 - 2 * p * c) * Real.log ((1 - 2 * p * c) / (1 - p)) := by
    have hle := Real.log_le_sub_one_of_pos (div_pos h1p h1q)
    have hmul := mul_le_mul_of_nonneg_left hle h1q.le
    rw [Real.log_div h1p.ne' h1q.ne'] at hmul
    rw [Real.log_div h1q.ne' h1p.ne']
    have hrhs : (1 - 2 * p * c) * ((1 - p) / (1 - 2 * p * c) - 1) = 2 * p * c - p := by
      field_simp; ring
    linarith
  have hlog_c : c - 1 ≤ c * Real.log c := by
    have hle := Real.log_le_sub_one_of_pos (one_div_pos.mpr hc_pos)
    rw [one_div, Real.log_inv] at hle
    have hmul := mul_le_mul_of_nonneg_left hle hc_pos.le
    have hrhs : c * (c⁻¹ - 1) = 1 - c := by field_simp
    linarith
  have hlog_2c : Real.log (2 * p * c / p) = Real.log 2 + Real.log c := by
    rw [show 2 * p * c / p = 2 * c by field_simp, Real.log_mul (by norm_num) hc_pos.ne']
  rw [bernoulliKL, hlog_2c]
  have halg : 2 * p * c * (Real.log 2 + Real.log c) + (p - 2 * p * c) =
      c * (2 * Real.log 2 - 1) * p + p * (2 * (c * Real.log c - (c - 1)) + (c - 1)) := by ring
  have hrem : 0 ≤ p * (2 * (c * Real.log c - (c - 1)) + (c - 1)) :=
    mul_nonneg hp0.le (by linarith)
  linarith

/-- Lower bound `D_e(Ber(2p) ‖ Ber(p)) ≥ (2 ln 2 - 1) p` for all `p ∈ (0, 1/2)`. -/
theorem bernoulliKL_two_mul_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    (2 * Real.log 2 - 1) * p ≤ bernoulliKL (2 * p) p := by
  have h := bernoulliKL_two_mul_mul_ge hp0 le_rfl (by linarith)
  simpa only [mul_one, one_mul] using h

/-- The Bernoulli distribution `Ber(p)` on `Bool` (returning `true` with probability `p`). -/
noncomputable def bernoulliPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then p else 1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true, ← ENNReal.ofReal_add hp0 (by linarith : 0 ≤ 1 - p)]
      norm_num)

@[simp]
theorem bernoulliPMF_apply_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliPMF p hp0 hp1 true).toReal = p := by
  simp [bernoulliPMF, ENNReal.toReal_ofReal hp0]

@[simp]
theorem bernoulliPMF_apply_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliPMF p hp0 hp1 false).toReal = 1 - p := by
  simp [bernoulliPMF, ENNReal.toReal_ofReal (show 0 ≤ 1 - p by linarith)]

/-- **Chernoff–Hoeffding KL bound**: for `n` i.i.d. `Ber(p)` random variables and
`ε > 0` with `p + ε < 1`, the probability that at least `(p + ε) n` variables equal `true` is
at most `exp(-n · D_e(Ber(p + ε) ‖ Ber(p)))`.
-/
theorem bernoulli_chernoff_kl_le {n : ℕ} {p ε : ℝ}
    (hp0 : 0 < p) (hε0 : 0 < ε) (hpε : p + ε < 1) :
    ((pi fun _ : Fin n => bernoulliPMF p hp0.le (by linarith)).toOuterMeasure
      {x : Fin n → Bool | (p + ε) * n ≤ (Finset.univ.filter fun i => x i = true).card}).toReal ≤
      Real.exp (-(n : ℝ) * bernoulliKL (p + ε) p) := by
  classical
  set q := p + ε
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have hp1 : 0 < 1 - p := by linarith
  set lam : ℝ := Real.log (q * (1 - p) / (p * (1 - q)))
  have hlam_pos : 0 < lam := by
    refine Real.log_pos ?_
    rw [one_lt_div (mul_pos hp0 hq1)]
    nlinarith
  have hexp_lam : Real.exp lam = q * (1 - p) / (p * (1 - q)) :=
    Real.exp_log (div_pos (mul_pos hq0 hp1) (mul_pos hp0 hq1))
  set μ := pi fun _ : Fin n => bernoulliPMF p hp0.le (by linarith)
  set S : (Fin n → Bool) → ℝ := fun x =>
    ((Finset.univ.filter fun i => x i = true).card : ℝ)
  have hmarkov : Real.exp (lam * (q * n)) *
      (μ.toOuterMeasure {x | q * n ≤ S x}).toReal ≤
      ∑ x : Fin n → Bool, (μ x).toReal * Real.exp (lam * S x) := by
    rw [toOuterMeasure_apply_toReal, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with hx
    · rw [mul_comm (Real.exp (lam * (q * ↑n)))]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hlam_pos.le)) ENNReal.toReal_nonneg
    · rw [mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _)
  have hmgf : ∑ x : Fin n → Bool, (μ x).toReal * Real.exp (lam * S x) =
      (p * Real.exp lam + (1 - p)) ^ n := by
    have hfactor (x : Fin n → Bool) :
        (μ x).toReal * Real.exp (lam * S x) =
          ∏ i : Fin n, ((bernoulliPMF p hp0.le (by linarith) (x i)).toReal *
            (if x i = true then Real.exp lam else 1)) := by
      have hμ : (μ x).toReal = ∏ i : Fin n, (bernoulliPMF p hp0.le (by linarith) (x i)).toReal := by
        rw [pi_apply, ENNReal.toReal_prod]
      have hexpS : Real.exp (lam * S x) =
          ∏ i : Fin n, (if x i = true then Real.exp lam else 1) := by
        have hS : lam * S x = ∑ i : Fin n, (if x i = true then lam else 0) := by
          have hcard : (∑ i : Fin n, if x i = true then (1 : ℝ) else 0) = S x := by
            simp only [S, Finset.sum_boole]
          rw [← hcard, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> ring
        rw [hS, Real.exp_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [hμ, hexpS, Finset.prod_mul_distrib]
    simp_rw [hfactor]
    rw [← Fintype.prod_sum (fun (_i : Fin n) (b : Bool) =>
      (bernoulliPMF p hp0.le (by linarith) b).toReal * (if b = true then Real.exp lam else 1))]
    simp [add_comm]
  have hbase : p * Real.exp lam + (1 - p) = (1 - p) / (1 - q) := by
    rw [hexp_lam]
    field_simp
    ring
  have hstep : (μ.toOuterMeasure {x | q * n ≤ S x}).toReal ≤
      Real.exp (-lam * (q * n)) * ((1 - p) / (1 - q)) ^ n := by
    rw [hmgf, hbase] at hmarkov
    calc (μ.toOuterMeasure {x | q * n ≤ S x}).toReal
        = Real.exp (-lam * (q * n)) *
            (Real.exp (lam * (q * n)) * (μ.toOuterMeasure {x | q * n ≤ S x}).toReal) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
      _ ≤ Real.exp (-lam * (q * n)) * ((1 - p) / (1 - q)) ^ n :=
          mul_le_mul_of_nonneg_left hmarkov (Real.exp_nonneg _)
  refine hstep.trans_eq ?_
  have hpow : ((1 - p) / (1 - q)) ^ n = Real.exp ((n : ℝ) * Real.log ((1 - p) / (1 - q))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos hp1 hq1), mul_comm]
  rw [hpow, ← Real.exp_add]
  congr 1
  have hlam_eq : lam = Real.log (q / p) + Real.log ((1 - p) / (1 - q)) := by
    simp only [lam]
    rw [show q * (1 - p) / (p * (1 - q)) = (q / p) * ((1 - p) / (1 - q)) by
          field_simp,
      Real.log_mul (div_pos hq0 hp0).ne' (div_pos hp1 hq1).ne']
  have hinv_log : Real.log ((1 - q) / (1 - p)) = -Real.log ((1 - p) / (1 - q)) := by
    rw [← Real.log_inv, inv_div]
  rw [bernoulliKL, hlam_eq, hinv_log]
  ring

end Cslib.Probability.PMF
