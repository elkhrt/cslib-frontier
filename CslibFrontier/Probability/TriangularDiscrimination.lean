/-
Copyright (c) 2026 The CSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CSLib contributors
-/
module

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.ChiSquare
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.MutualInformation
public import CslibFrontier.Probability.StatisticalDistance.XOR
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue

/-!
# Triangular Discrimination and Jensen–Shannon Divergence on Finite Distributions

This module develops classical triangular discrimination (also known as the Vincze–Le Cam
divergence) and the classical Jensen–Shannon divergence (in bits and in nats) on probability
mass functions `PMF α` over finite types, together with their sharp comparison inequalities
with statistical distance, squared Hellinger distance, Pearson `χ²`-divergence, Kullback–Leibler
divergence, mutual information, and base-2 binary entropy. All theorems are proved
unconditionally under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

* `CslibFrontier.Probability.binEntropyBits`: base-2 binary Shannon entropy
  `H₂(p) = Real.binEntropy p / Real.log 2`.
* `CslibFrontier.Probability.pmfMidpoint`: equal-weight mixture `(p + q) / 2` of two PMFs.
* `CslibFrontier.Probability.pmfBinaryJoint`: joint distribution on `Bool × α` choosing a
  uniform bit `b` and sampling from `p` (`b = false`) or `q` (`b = true`).
* `CslibFrontier.Probability.pmfCollisionProb`: collision probability `∑ x, p(x) q(x)`.
* `CslibFrontier.Probability.triangularDisc`: classical triangular discrimination
  `TD(p, q) = (1 / 2) * ∑ x, (p(x) - q(x))² / (p(x) + q(x))`.
* `CslibFrontier.Probability.jensenShannonBits`: base-2 Jensen–Shannon divergence
  `JS₂(p, q) = H((p + q) / 2) - (H(p) + H(q)) / 2`.
* `CslibFrontier.Probability.jensenShannon`: natural-logarithm Jensen–Shannon divergence
  `JS(p, q) = Real.log 2 * JS₂(p, q)`.

## Main results

* `CslibFrontier.Probability.binEntropyBits_le_two_mul_sqrt`: `H₂(x) ≤ 2 √x` for `x ∈ [0, 1]`.
* `CslibFrontier.Probability.hasSum_one_sub_binEntropyBits_half_one_sub`: Topsøe power-series
  expansion `1 - H₂((1 - s) / 2) = ∑_{v=1}^∞ s^{2v} / (ln 2 · 2v(2v - 1))` on `[0, 1]`.
* `CslibFrontier.Probability.dist_sq_le_triangularDisc`,
  `CslibFrontier.Probability.triangularDisc_le_dist`: Topsøe bounds `SD² ≤ TD ≤ SD`.
* `CslibFrontier.Probability.hellingerSq_le_triangularDisc`,
  `CslibFrontier.Probability.triangularDisc_le_two_mul_hellingerSq`: Le Cam bounds
  `H² ≤ TD ≤ 2 H²`.
* `CslibFrontier.Probability.triangularDisc_xorMix`: exact multiplicativity of `TD` under the
  `k`-fold parity mixture `xorMix`.
* `CslibFrontier.Probability.half_triangularDisc_le_jensenShannon`,
  `CslibFrontier.Probability.jensenShannon_le_log_two_mul_triangularDisc`: Topsøe two-sided
  bounds `(1 / 2) TD ≤ JS ≤ ln 2 · TD`.
* `CslibFrontier.Probability.one_sub_binEntropyBits_le_jensenShannonBits`,
  `CslibFrontier.Probability.jensenShannonBits_le_dist`: Fuchs–van de Graaf and Topsøe bounds
  `1 - H₂((1 - SD) / 2) ≤ JS₂ ≤ SD`.
* `CslibFrontier.Probability.jensenShannonBits_eq_mutualInfo`: mutual-information and
  conditional-entropy identity `JS₂(p, q) = I(T; X) = 1 - H(T | X)`.

## Tags

triangular discrimination, Le Cam divergence, Jensen-Shannon divergence, Hellinger distance,
statistical distance, binary entropy
-/

public section

open Finset Filter MeasureTheory
open Cslib.Probability.PMF
open scoped BigOperators Cslib.Probability.PMF ENNReal NNReal Topology

namespace CslibFrontier.Probability

/-! ### 1. Base-2 binary entropy and the Topsøe power series -/

section BinaryEntropy

/-- Base-2 binary Shannon entropy `H₂(p) = -p log₂ p - (1 - p) log₂ (1 - p)`, defined as
`Real.binEntropy p / Real.log 2` (vanishing at `p = 0` and `p = 1`). -/
@[expose] noncomputable def binEntropyBits (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- Explicit formula for `binEntropyBits` in terms of `Real.logb 2`. -/
theorem binEntropyBits_eq_neg_mul_logb (p : ℝ) :
    binEntropyBits p = -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p) := by
  rw [binEntropyBits, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog,
    Real.negMulLog, Real.logb, Real.logb]
  ring

@[simp]
theorem binEntropyBits_zero : binEntropyBits 0 = 0 := by
  simp [binEntropyBits]

@[simp]
theorem binEntropyBits_one : binEntropyBits 1 = 0 := by
  simp [binEntropyBits]

theorem binEntropyBits_half : binEntropyBits (1 / 2 : ℝ) = 1 := by
  rw [binEntropyBits, one_div, Real.binEntropy_two_inv, div_self (Real.log_pos one_lt_two).ne']

/-- Symmetry `H₂(1 - p) = H₂(p)`. -/
theorem binEntropyBits_one_sub (p : ℝ) : binEntropyBits (1 - p) = binEntropyBits p := by
  rw [binEntropyBits, binEntropyBits, Real.binEntropy_one_sub]

/-- Nonnegativity `0 ≤ H₂(p)` on `[0, 1]`. -/
theorem binEntropyBits_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binEntropyBits p :=
  div_nonneg (Real.binEntropy_nonneg hp0 hp1) (Real.log_pos one_lt_two).le

/-- Upper bound `H₂(p) ≤ 1` for all `p : ℝ`. -/
theorem binEntropyBits_le_one (p : ℝ) : binEntropyBits p ≤ 1 :=
  (div_le_one (Real.log_pos one_lt_two)).mpr Real.binEntropy_le_log_two

/-- Continuity of `binEntropyBits`. -/
@[fun_prop]
theorem continuous_binEntropyBits : Continuous binEntropyBits :=
  Real.binEntropy_continuous.div_const _

/-- Strict monotonicity of `binEntropyBits` on `[0, 1 / 2]`. -/
theorem binEntropyBits_strictMonoOn : StrictMonoOn binEntropyBits (Set.Icc 0 (1 / 2)) := by
  intro x hx y hy hxy
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [binEntropyBits, binEntropyBits, div_lt_div_iff_of_pos_right hlog]
  rw [one_div] at hx hy
  exact Real.binEntropy_strictMonoOn hx hy hxy

/-- Intermediate-value theorem for `binEntropyBits`: every target entropy `y ∈ [0, 1]` is attained
at some `p ∈ [0, 1 / 2]`. -/
theorem exists_mem_Icc_binEntropyBits_eq {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ p ∈ Set.Icc (0 : ℝ) (1 / 2), binEntropyBits p = y := by
  have hmem : y ∈ Set.Icc (binEntropyBits 0) (binEntropyBits (1 / 2)) := by
    simpa only [binEntropyBits_zero, binEntropyBits_half] using Set.mem_Icc.mpr ⟨hy0, hy1⟩
  exact intermediate_value_Icc (by norm_num) continuous_binEntropyBits.continuousOn hmem

/-- Square-root upper bound `H₂(x) ≤ 2 √x` for all `x ∈ [0, 1]`. -/
theorem binEntropyBits_le_two_mul_sqrt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    binEntropyBits x ≤ 2 * Real.sqrt x := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · simp
  by_cases hquarter : (1 / 4 : ℝ) ≤ x
  · have hsq4 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc binEntropyBits x ≤ 1 := binEntropyBits_le_one x
      _ = 2 * Real.sqrt (1 / 4) := by rw [hsq4]; norm_num
      _ ≤ 2 * Real.sqrt x := by gcongr
  · push Not at hquarter
    have hsq4 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [binEntropyBits, div_le_iff₀ hlog2, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    set r := Real.sqrt x
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hxpos
    have hr_le : r ≤ 1 / 2 := (Real.sqrt_le_sqrt hquarter.le).trans_eq hsq4
    have hrx : r ^ 2 = x := Real.sq_sqrt hx0
    -- Bound `-r * log r ≤ 1 / exp 1` via `log (1 / (r * exp 1)) ≤ 1 / (r * exp 1) - 1`.
    have hterm1 : Real.negMulLog x ≤ (2 / Real.exp 1) * r := by
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      have hre : 0 < r * Real.exp 1 := mul_pos hr_pos he
      have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hre)
      rw [Real.log_inv, Real.log_mul hr_pos.ne' he.ne', Real.log_exp] at hlog
      have hmul : -r * Real.log r ≤ 1 / Real.exp 1 := by
        have h1 : -(Real.log r + 1) ≤ (r * Real.exp 1)⁻¹ - 1 := hlog
        have h2 : r * (-Real.log r) ≤ r * (r * Real.exp 1)⁻¹ := by nlinarith
        have h3 : r * (r * Real.exp 1)⁻¹ = 1 / Real.exp 1 := by
          field_simp [hr_pos.ne', he.ne']
        linarith
      have hneg : Real.negMulLog x = 2 * r * (-r * Real.log r) := by
        rw [Real.negMulLog, ← hrx, Real.log_pow]
        push_cast
        ring
      rw [hneg]
      calc 2 * r * (-r * Real.log r) ≤ 2 * r * (1 / Real.exp 1) := by gcongr
        _ = (2 / Real.exp 1) * r := by ring
    -- Bound `-(1 - x) * log (1 - x) ≤ x ≤ (1 / 2) * r` via `log (1 / (1 - x)) ≤ x / (1 - x)`.
    have hterm2 : Real.negMulLog (1 - x) ≤ (1 / 2 : ℝ) * r := by
      have h1x : 0 < 1 - x := by linarith
      have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
      rw [Real.log_inv] at hlog
      have hmul : -(1 - x) * Real.log (1 - x) ≤ x := by
        have h := mul_le_mul_of_nonneg_left hlog h1x.le
        have hsimp : (1 - x) * ((1 - x)⁻¹ - 1) = x := by field_simp [h1x.ne']; ring
        nlinarith
      calc Real.negMulLog (1 - x) = -(1 - x) * Real.log (1 - x) := by rw [Real.negMulLog]
        _ ≤ x := hmul
        _ = r * r := by rw [← hrx, sq]
        _ ≤ (1 / 2) * r := by nlinarith
    have hconst : 2 / Real.exp 1 + 1 / 2 ≤ 2 * Real.log 2 := by
      have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hdiv : 2 / Real.exp 1 < 2 / 2.7182818283 :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) he
      linarith
    calc Real.negMulLog x + Real.negMulLog (1 - x)
        ≤ (2 / Real.exp 1 + 1 / 2) * r := by linarith
      _ ≤ (2 * Real.log 2) * r := by gcongr
      _ = 2 * r * Real.log 2 := by ring

/-- Algebraic identity relating `ln 2 · (1 - H₂((1 - s) / 2))` to the symmetrized `x ln x` kernel
`((1 + s) ln (1 + s) + (1 - s) ln (1 - s)) / 2` for `s ∈ [0, 1]`. -/
theorem log_two_mul_one_sub_binEntropyBits {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.log 2 * (1 - binEntropyBits ((1 - s) / 2)) =
      ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [binEntropyBits, mul_sub, mul_one, mul_div_cancel₀ _ hlog2,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog,
    show 1 - (1 - s) / 2 = (1 + s) / 2 by ring]
  have h1s_pos : 0 < 1 + s := by linarith
  have hlog_plus : Real.log ((1 + s) / 2) = Real.log (1 + s) - Real.log 2 :=
    Real.log_div h1s_pos.ne' (by norm_num)
  rcases hs1.eq_or_lt with rfl | hslt
  · simp only [sub_self, zero_div, Real.log_zero, mul_zero, neg_zero, zero_add, add_zero]
    rw [show (1 + 1 : ℝ) / 2 = 1 by norm_num, Real.log_one, mul_zero]
    norm_num
  · have h1ms_pos : 0 < 1 - s := by linarith
    have hlog_minus : Real.log ((1 - s) / 2) = Real.log (1 - s) - Real.log 2 :=
      Real.log_div h1ms_pos.ne' (by norm_num)
    rw [hlog_plus, hlog_minus]
    ring

/-- The `k`-th term `s^{2(k+1)} / ((2k+2)(2k+1))` of the natural-logarithm Topsøe power series. -/
@[expose] noncomputable def topsoeSeriesTerm (s : ℝ) (k : ℕ) : ℝ :=
  s ^ (2 * (k + 1)) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1))

theorem topsoeSeriesTerm_nonneg (s : ℝ) (k : ℕ) : 0 ≤ topsoeSeriesTerm s k := by
  rw [topsoeSeriesTerm]
  refine div_nonneg ?_ ?_
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg s) _
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

theorem topsoeSeriesTerm_le_inv (s : ℝ) (hs : |s| ≤ 1) (k : ℕ) :
    topsoeSeriesTerm s k ≤ 1 / ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1)) := by
  rw [topsoeSeriesTerm]
  have hden : 0 < (2 * (k + 1) : ℝ) * (2 * (k + 1) - 1) := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hpow : s ^ (2 * (k + 1)) ≤ 1 := by
    rw [pow_mul]
    have hs2 : s ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg s]
    exact pow_le_one₀ (sq_nonneg s) hs2
  exact div_le_div_of_nonneg_right hpow hden.le

theorem summable_topsoeSeriesTerm_one : Summable (topsoeSeriesTerm 1) := by
  have hbound : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℝ) ^ 2)) := by
    have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    simpa using (summable_nat_add_iff 1).mpr hp
  refine Summable.of_nonneg_of_le (topsoeSeriesTerm_nonneg 1) (fun k => ?_) hbound
  rw [topsoeSeriesTerm, one_pow]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith

theorem summable_topsoeSeriesTerm {s : ℝ} (hs : |s| ≤ 1) :
    Summable (topsoeSeriesTerm s) := by
  refine Summable.of_nonneg_of_le (topsoeSeriesTerm_nonneg s) (fun k => ?_)
    summable_topsoeSeriesTerm_one
  simpa [topsoeSeriesTerm] using topsoeSeriesTerm_le_inv s hs k

/-- Natural-logarithm Topsøe power-series identity for `|s| < 1`:
`∑_{v=1}^∞ s^{2v} / (2v(2v - 1)) = ((1 + s) ln (1 + s) + (1 - s) ln (1 - s)) / 2`. -/
private theorem hasSum_topsoeSeriesTerm_of_abs_lt_one {s : ℝ} (hs : |s| < 1) :
    HasSum (topsoeSeriesTerm s)
      (((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2) := by
  -- Use `Real.hasSum_pow_div_log_of_abs_lt_one` for `s` and `-s`.
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one hs
  have h2 := Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_neg] : |-s| < 1)
  -- `h1 : HasSum (fun n => s^(n+1)/(n+1)) (-log(1 - s))`
  -- `h2 : HasSum (fun n => (-s)^(n+1)/(n+1)) (-log(1 + s))`
  have h1' : HasSum (fun n : ℕ => s ^ (n + 1) / (n + 1 : ℝ)) (-Real.log (1 - s)) := h1
  have h2' : HasSum (fun n : ℕ => (-s) ^ (n + 1) / (n + 1 : ℝ)) (-Real.log (1 + s)) := by
    simpa [sub_neg_eq_add] using h2
  -- Even parts: `(1/2) * (h1' + h2')` gives `∑_{k} s^{2k+2} / (2k+2) = -(log(1-s)+log(1+s))/2`.
  have heven : HasSum (fun k : ℕ => s ^ (2 * k + 2) / (2 * k + 2 : ℝ))
      (-(Real.log (1 - s) + Real.log (1 + s)) / 2) := by
    have hadd := (h1'.add h2').mul_left (1 / 2 : ℝ)
    have hpair : ∀ k : ℕ,
        (1 / 2 : ℝ) * (s ^ (2 * k + 1) / (2 * k + 1 : ℝ) +
          (-s) ^ (2 * k + 1) / (2 * k + 1 : ℝ)) +
        (1 / 2 : ℝ) * (s ^ (2 * k + 2) / (2 * k + 2 : ℝ) +
          (-s) ^ (2 * k + 2) / (2 * k + 2 : ℝ)) =
        s ^ (2 * k + 2) / (2 * k + 2 : ℝ) := by
      intro k
      have hodd_pow : (-s) ^ (2 * k + 1) = -s ^ (2 * k + 1) :=
        Odd.neg_pow ⟨k, rfl⟩ s
      have heven_pow : (-s) ^ (2 * k + 2) = s ^ (2 * k + 2) :=
        Even.neg_pow ⟨k + 1, by ring⟩ s
      rw [hodd_pow, heven_pow]
      ring
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have htend := hadd.tendsto_sum_nat.comp (tendsto_id.const_mul_atTop' two_pos)
      have hsum_eq : ∀ N : ℕ,
          (∑ n ∈ range (2 * N),
            (1 / 2 : ℝ) * (s ^ (n + 1) / (n + 1 : ℝ) + (-s) ^ (n + 1) / (n + 1 : ℝ))) =
          ∑ k ∈ range N, s ^ (2 * k + 2) / (2 * k + 2 : ℝ) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ,
            show 2 * N + 1 + 1 = 2 * N + 2 by omega]
          have hp := hpair N
          push_cast at hp ⊢
          rw [show (2 * (N : ℝ) + 1 + 1) = 2 * (N : ℝ) + 2 by ring]
          linarith
      simpa only [Function.comp_def, id_eq, hsum_eq,
        show (1 / 2 : ℝ) * (-Real.log (1 - s) + -Real.log (1 + s)) =
          -(Real.log (1 - s) + Real.log (1 + s)) / 2 by ring] using htend
    · intro k
      refine div_nonneg ?_ (by positivity)
      exact Even.pow_nonneg ⟨k + 1, by ring⟩ s
  -- Odd parts multiplied by `s`: `(s / 2) * (h1' - h2')` gives
  -- `∑_k s^{2k+2} / (2k+1) = s * (log(1+s) - log(1-s)) / 2`.
  have hodd : HasSum (fun k : ℕ => s ^ (2 * k + 2) / (2 * k + 1 : ℝ))
      (s * (Real.log (1 + s) - Real.log (1 - s)) / 2) := by
    have hsub := (h1'.sub h2').mul_left (s / 2)
    have hpair : ∀ k : ℕ,
        (s / 2) * (s ^ (2 * k + 1) / (2 * k + 1 : ℝ) -
          (-s) ^ (2 * k + 1) / (2 * k + 1 : ℝ)) +
        (s / 2) * (s ^ (2 * k + 2) / (2 * k + 2 : ℝ) -
          (-s) ^ (2 * k + 2) / (2 * k + 2 : ℝ)) =
        s ^ (2 * k + 2) / (2 * k + 1 : ℝ) := by
      intro k
      have hodd_pow : (-s) ^ (2 * k + 1) = -s ^ (2 * k + 1) :=
        Odd.neg_pow ⟨k, rfl⟩ s
      have heven_pow : (-s) ^ (2 * k + 2) = s ^ (2 * k + 2) :=
        Even.neg_pow ⟨k + 1, by ring⟩ s
      rw [hodd_pow, heven_pow, show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ]
      ring
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have htend := hsub.tendsto_sum_nat.comp (tendsto_id.const_mul_atTop' two_pos)
      have hsum_eq : ∀ N : ℕ,
          (∑ n ∈ range (2 * N),
            (s / 2) * (s ^ (n + 1) / (n + 1 : ℝ) - (-s) ^ (n + 1) / (n + 1 : ℝ))) =
          ∑ k ∈ range N, s ^ (2 * k + 2) / (2 * k + 1 : ℝ) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ,
            show 2 * N + 1 + 1 = 2 * N + 2 by omega]
          have hp := hpair N
          push_cast at hp ⊢
          rw [show (2 * (N : ℝ) + 1 + 1) = 2 * (N : ℝ) + 2 by ring]
          linarith
      simpa only [Function.comp_def, id_eq, hsum_eq,
        show (s / 2) * (-Real.log (1 - s) - -Real.log (1 + s)) =
          s * (Real.log (1 + s) - Real.log (1 - s)) / 2 by ring] using htend
    · intro k
      refine div_nonneg ?_ (by positivity)
      exact Even.pow_nonneg ⟨k + 1, by ring⟩ s
  -- Subtract `hodd - heven`: `1/(2k+1) - 1/(2k+2) = 1/((2k+2)(2k+1))`.
  have hdiff := hodd.sub heven
  have hterm : (fun k : ℕ =>
      s ^ (2 * k + 2) / (2 * k + 1 : ℝ) - s ^ (2 * k + 2) / (2 * k + 2 : ℝ)) =
      topsoeSeriesTerm s := by
    ext k
    rw [topsoeSeriesTerm, show 2 * (k + 1) = 2 * k + 2 by omega,
      show (2 * ((k : ℝ) + 1) - 1) = 2 * (k : ℝ) + 1 by ring,
      show (2 * ((k : ℝ) + 1)) = 2 * (k : ℝ) + 2 by ring]
    have h1pos : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2pos : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    field_simp [h1pos, h2pos]
    ring
  have hval : s * (Real.log (1 + s) - Real.log (1 - s)) / 2 -
      -(Real.log (1 - s) + Real.log (1 + s)) / 2 =
      ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2 := by ring
  rwa [hterm, hval] at hdiff

/-- At `s = 1`, `∑_{v=1}^∞ 1 / (2v(2v - 1)) = ln 2`. -/
theorem hasSum_topsoeSeriesTerm_one : HasSum (topsoeSeriesTerm 1) (Real.log 2) := by
  have hsum : HasSum (topsoeSeriesTerm 1) (∑' k, topsoeSeriesTerm 1 k) :=
    summable_topsoeSeriesTerm_one.hasSum
  suffices h : (∑' k, topsoeSeriesTerm 1 k) = Real.log 2 by rwa [← h]
  let f : ℝ → ℝ := fun s => ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2
  have hf_cont : ContinuousOn f (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun s : ℝ => -Real.negMulLog (1 + s)) (Set.Icc 0 1) :=
      (Real.continuous_negMulLog.comp (continuous_const.add continuous_id')).neg.continuousOn
    have h2 : ContinuousOn (fun s : ℝ => -Real.negMulLog (1 - s)) (Set.Icc 0 1) :=
      (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id')).neg.continuousOn
    have heq : f = fun s => (-Real.negMulLog (1 + s) + -Real.negMulLog (1 - s)) / 2 := by
      ext s
      simp only [f, Real.negMulLog]
      ring
    rw [heq]
    exact (h1.add h2).div_const 2
  have hf1 : f 1 = Real.log 2 := by
    simp only [f]
    norm_num
  have hseq_tend : Tendsto (fun m : ℕ => 1 - 1 / (m + 2 : ℝ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 2 : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine h.congr fun m => ?_
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
      ring
    simpa using tendsto_const_nhds.sub h0
  set seq : ℕ → ℝ := fun m => 1 - 1 / (m + 2 : ℝ)
  have hseq_mem : ∀ m, seq m ∈ Set.Icc (0 : ℝ) 1 := fun m => by
    have hm : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hdiv : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm
    have hpos : 0 < 1 / ((m : ℝ) + 2) := by positivity
    exact ⟨by dsimp [seq]; linarith, by dsimp [seq]; linarith⟩
  have hseq_lt : ∀ m, |seq m| < 1 := fun m => by
    have hm := hseq_mem m
    have hpos : 0 < 1 / ((m : ℝ) + 2) := by positivity
    rw [abs_of_nonneg hm.1]; dsimp only [seq]; linarith
  have hf_seq : Tendsto (f ∘ seq) atTop (𝓝 (Real.log 2)) := by
    rw [← hf1]
    exact (hf_cont.continuousWithinAt ⟨zero_le_one, le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within seq hseq_tend
        (Eventually.of_forall hseq_mem))
  apply le_antisymm
  · refine Real.tsum_le_of_sum_range_le (topsoeSeriesTerm_nonneg 1) fun N => ?_
    have hle : ∀ m, (∑ k ∈ range N, topsoeSeriesTerm (seq m) k) ≤ f (seq m) := fun m =>
      sum_le_hasSum (range N) (fun k _ => topsoeSeriesTerm_nonneg _ k)
        (hasSum_topsoeSeriesTerm_of_abs_lt_one (hseq_lt m))
    have hlhs : Tendsto (fun m => ∑ k ∈ range N, topsoeSeriesTerm (seq m) k) atTop
        (𝓝 (∑ k ∈ range N, topsoeSeriesTerm 1 k)) := by
      clear hle
      induction N with
      | zero => simp
      | succ n ih =>
        simp_rw [sum_range_succ]
        refine ih.add ?_
        dsimp only [topsoeSeriesTerm]
        simpa only [one_pow] using (hseq_tend.pow (2 * (n + 1))).div_const _
    exact le_of_tendsto_of_tendsto hlhs hf_seq (Eventually.of_forall hle)
  · have hle : ∀ m, f (seq m) ≤ ∑' k, topsoeSeriesTerm 1 k := fun m => by
      dsimp only [f]
      rw [← (hasSum_topsoeSeriesTerm_of_abs_lt_one (hseq_lt m)).tsum_eq]
      refine Summable.tsum_le_tsum (fun k => ?_)
        (summable_topsoeSeriesTerm (hseq_lt m).le) summable_topsoeSeriesTerm_one
      simpa [topsoeSeriesTerm] using topsoeSeriesTerm_le_inv (seq m) (hseq_lt m).le k
    exact le_of_tendsto_of_tendsto hf_seq tendsto_const_nhds (Eventually.of_forall hle)

/-- Natural-logarithm Topsøe power series on the entire closed unit interval `|s| ≤ 1`. -/
theorem hasSum_topsoeSeriesTerm {s : ℝ} (hs : |s| ≤ 1) :
    HasSum (topsoeSeriesTerm s)
      (((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2) := by
  rcases hs.eq_or_lt with h1 | hlt
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl
    · rw [show ((1 + (1 : ℝ)) * Real.log (1 + 1) + (1 - 1) * Real.log (1 - 1)) / 2 =
        Real.log 2 by norm_num]
      exact hasSum_topsoeSeriesTerm_one
    · have hterm : topsoeSeriesTerm (-1) = topsoeSeriesTerm 1 := by
        ext k; simp [topsoeSeriesTerm, pow_mul]
      rw [hterm, show ((1 + (-1 : ℝ)) * Real.log (1 + -1) + (1 - -1) * Real.log (1 - -1)) / 2 =
        Real.log 2 by norm_num]
      exact hasSum_topsoeSeriesTerm_one
  · exact hasSum_topsoeSeriesTerm_of_abs_lt_one hlt

/-- Topsøe power-series expansion of `1 - H₂((1 - s) / 2)` for all `s ∈ [0, 1]`:
`∑_{v=1}^∞ s^{2v} / (ln 2 · 2v(2v - 1)) = 1 - H₂((1 - s) / 2)`. -/
theorem hasSum_one_sub_binEntropyBits_half_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasSum (fun k : ℕ =>
        s ^ (2 * (k + 1)) / (Real.log 2 * ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1))))
      (1 - binEntropyBits ((1 - s) / 2)) := by
  have hs_abs : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
  have h := (hasSum_topsoeSeriesTerm hs_abs).div_const (Real.log 2)
  rw [← log_two_mul_one_sub_binEntropyBits hs0 hs1,
    mul_div_cancel_left₀ _ (Real.log_pos one_lt_two).ne'] at h
  convert h using 1
  ext k
  rw [topsoeSeriesTerm, div_div, mul_comm _ (Real.log 2)]

/-- `tsum` form of the Topsøe binary-entropy power series on `[0, 1]`. -/
theorem tsum_eq_one_sub_binEntropyBits_half_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑' k : ℕ, s ^ (2 * (k + 1)) / (Real.log 2 * ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1)))) =
      1 - binEntropyBits ((1 - s) / 2) :=
  (hasSum_one_sub_binEntropyBits_half_one_sub hs0 hs1).tsum_eq

/-- Two-sided quadratic bounds `s² / 2 ≤ ((1 + s) ln(1 + s) + (1 - s) ln(1 - s)) / 2 ≤ ln 2 · s²`
for all `|s| ≤ 1`, obtained immediately from the first term and full sum of the Topsøe series. -/
theorem half_sq_le_symmMulLog {s : ℝ} (hs : |s| ≤ 1) :
    s ^ 2 / 2 ≤ ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2 := by
  have hsum := hasSum_topsoeSeriesTerm hs
  have h1 := sum_le_hasSum ({0} : Finset ℕ) (fun k _ => topsoeSeriesTerm_nonneg s k) hsum
  simp only [sum_singleton, topsoeSeriesTerm, zero_add, Nat.mul_one] at h1
  norm_num at h1
  linarith

theorem symmMulLog_le_log_two_mul_sq {s : ℝ} (hs : |s| ≤ 1) :
    ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2 ≤ Real.log 2 * s ^ 2 := by
  rw [← (hasSum_topsoeSeriesTerm hs).tsum_eq, mul_comm (Real.log 2) (s ^ 2),
    ← (hasSum_topsoeSeriesTerm_one.mul_left (s ^ 2)).tsum_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_topsoeSeriesTerm hs)
    (summable_topsoeSeriesTerm_one.mul_left (s ^ 2))
  simp only [topsoeSeriesTerm, one_pow]
  have hden : 0 < (2 * (k + 1) : ℝ) * (2 * (k + 1) - 1) := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hpow : s ^ (2 * (k + 1)) ≤ s ^ 2 := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add, pow_mul]
    have hs2 : s ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg s]
    have h1 : (s ^ 2) ^ k ≤ 1 := pow_le_one₀ (sq_nonneg s) hs2
    nlinarith [sq_nonneg s]
  calc s ^ (2 * (k + 1)) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1))
      ≤ s ^ 2 / ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1)) :=
        div_le_div_of_nonneg_right hpow hden.le
    _ = s ^ 2 * (1 / ((2 * (k + 1) : ℝ) * (2 * (k + 1) - 1))) := by ring

/-- First-order Pinsker-type bound `s² / (2 ln 2) ≤ 1 - H₂((1 - s) / 2)` for `s ∈ [0, 1]`. -/
theorem sq_div_two_log_two_le_one_sub_binEntropyBits {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 2 / (2 * Real.log 2) ≤ 1 - binEntropyBits ((1 - s) / 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [div_le_iff₀ (by positivity)]
  have hs_abs : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
  have h := half_sq_le_symmMulLog hs_abs
  rw [← log_two_mul_one_sub_binEntropyBits hs0 hs1] at h
  linarith

/-- Monotonicity of `s ↦ 1 - H₂((1 - s) / 2)` on `[0, 1]`. -/
theorem monotoneOn_one_sub_binEntropyBits_half_one_sub :
    MonotoneOn (fun s : ℝ => 1 - binEntropyBits ((1 - s) / 2)) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  refine sub_le_sub_left (binEntropyBits_strictMonoOn ?_ ?_ (by linarith)).le 1
  · exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

end BinaryEntropy

/-! ### 2. Midpoint mixture, binary joint distribution, and collision probability -/

section Midpoint

variable {α β : Type*}

/-- The equal-weight mixture `(p + q) / 2` of two probability mass functions on `α`. -/
noncomputable def pmfMidpoint (p q : PMF α) : PMF α :=
  (uniformOfFintype Bool).bind fun b => if b then q else p

/-- Pointwise real probability mass of `pmfMidpoint p q`. -/
@[simp]
theorem toReal_pmfMidpoint (p q : PMF α) (a : α) :
    (pmfMidpoint p q a).toReal = ((p a).toReal + (q a).toReal) / 2 := by
  have hne : ∀ b : Bool,
      (uniformOfFintype Bool b) * ((if b then q else p) a) ≠ ⊤ := fun b =>
    ENNReal.mul_ne_top ((uniformOfFintype Bool).apply_ne_top b)
      ((if b then q else p).apply_ne_top a)
  rw [pmfMidpoint, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun b _ => hne b,
    Fintype.sum_bool]
  simp only [uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ↓reduceIte,
    Bool.false_eq_true, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  ring

/-- Symmetry of `pmfMidpoint`. -/
theorem pmfMidpoint_comm (p q : PMF α) : pmfMidpoint p q = pmfMidpoint q p := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff' ((pmfMidpoint p q).apply_ne_top a)
    ((pmfMidpoint q p).apply_ne_top a)).mp
  simp [add_comm]

/-- Idempotence of `pmfMidpoint`. -/
@[simp]
theorem pmfMidpoint_self (p : PMF α) : pmfMidpoint p p = p := by
  ext a
  apply (ENNReal.toReal_eq_toReal_iff' ((pmfMidpoint p p).apply_ne_top a) (p.apply_ne_top a)).mp
  simp

/-- The support of `p` lies in the support of `(p + q) / 2`. -/
theorem support_subset_pmfMidpoint_left (p q : PMF α) :
    p.support ⊆ (pmfMidpoint p q).support := by
  intro a ha
  rw [PMF.mem_support_iff] at ha ⊢
  intro h0
  have htr : (pmfMidpoint p q a).toReal = 0 := by simp [h0]
  rw [toReal_pmfMidpoint] at htr
  have hp : 0 < (p a).toReal := ENNReal.toReal_pos ha (p.apply_ne_top a)
  have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
  linarith

/-- The support of `q` lies in the support of `(p + q) / 2`. -/
theorem support_subset_pmfMidpoint_right (p q : PMF α) :
    q.support ⊆ (pmfMidpoint p q).support :=
  pmfMidpoint_comm q p ▸ support_subset_pmfMidpoint_left q p

/-- Pushforward commutes with `pmfMidpoint`. -/
theorem pmfMidpoint_map (p q : PMF α) (f : α → β) :
    (pmfMidpoint p q).map f = pmfMidpoint (p.map f) (q.map f) := by
  rw [pmfMidpoint, pmfMidpoint, PMF.map_bind]
  congr 1
  ext b
  cases b <;> rfl

/-- Joint distribution on `Bool × α` that draws a uniform bit `T ∈ Bool` and samples `X ∼ p` when
`T = false` and `X ∼ q` when `T = true`. -/
noncomputable def pmfBinaryJoint (p q : PMF α) : PMF (Bool × α) :=
  (uniformOfFintype Bool).bind fun b => (if b then q else p).map (b, ·)

@[simp]
theorem pmfBinaryJoint_map_fst (p q : PMF α) :
    (pmfBinaryJoint p q).map Prod.fst = uniformOfFintype Bool := by
  ext c
  rw [pmfBinaryJoint, PMF.map_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  have hconst : ∀ (r : PMF α) (b : Bool), (r.map (fun _ => b)) c = if c = b then 1 else 0 := by
    intro r b
    rw [PMF.map_apply]
    by_cases h : c = b <;> simp [h]
  simp only [PMF.map_comp, Function.comp_def, hconst]
  cases c <;> simp

@[simp]
theorem pmfBinaryJoint_map_snd (p q : PMF α) :
    (pmfBinaryJoint p q).map Prod.snd = pmfMidpoint p q := by
  rw [pmfBinaryJoint, pmfMidpoint, PMF.map_bind]
  congr 1; ext b; simp [PMF.map_comp, Function.comp_def]

/-- Collision probability `Col(p, q) = ∑ x, p(x) q(x)` of two finite PMFs. -/
@[expose] noncomputable def pmfCollisionProb [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a, (p a).toReal * (q a).toReal

theorem pmfCollisionProb_nonneg [Fintype α] (p q : PMF α) : 0 ≤ pmfCollisionProb p q :=
  sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- If `dist p q = 1`, the supports of `p` and `q` are disjoint and `Col(p, q) = 0`. -/
theorem pmfCollisionProb_eq_zero_of_dist_eq_one [Fintype α] {p q : PMF α} (h : dist p q = 1) :
    pmfCollisionProb p q = 0 := by
  have hmin := Cslib.Probability.PMF.sum_min_toReal p q
  rw [h, sub_self] at hmin
  have hall : ∀ a, min (p a).toReal (q a).toReal = 0 := fun a =>
    (sum_eq_zero_iff_of_nonneg fun b _ =>
      le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp hmin a (mem_univ a)
  refine sum_eq_zero fun a _ => ?_
  rcases min_cases (p a).toReal (q a).toReal with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
    simp [hm.symm.trans (hall a)]

/-- If `dist p q = 0` (so `p = q`), Cauchy–Schwarz on any finite superset `S` of `supp p` gives
`1 / |S| ≤ Col(p, q)`. -/
theorem inv_card_support_le_pmfCollisionProb_of_dist_eq_zero [Fintype α]
    {p q : PMF α} {S : Finset α} (h : dist p q = 0) (hS : ∀ a ∈ p.support, a ∈ S) :
    1 / (S.card : ℝ) ≤ pmfCollisionProb p q := by
  have hpq : p = q := dist_eq_zero.mp h
  subst hpq
  have hsum1 : ∑ a ∈ S, (p a).toReal = 1 := by
    have htot : ∑ a : α, (p a).toReal = 1 := by
      rw [← ENNReal.toReal_one, ← p.tsum_coe, tsum_fintype,
        ENNReal.toReal_sum fun a _ => p.apply_ne_top a]
    rw [← htot]
    refine sum_subset (subset_univ S) fun a _ ha => ?_
    have h0 : p a = 0 := not_not.mp fun hn => ha (hS a ((PMF.mem_support_iff p a).mpr hn))
    simp [h0]
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by
    have hne : S.Nonempty := nonempty_of_sum_ne_zero (by rw [hsum1]; exact one_ne_zero)
    exact_mod_cast hne.card_pos
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun a => (p a).toReal)
  rw [hsum1, one_pow] at hcs
  have hle : ∑ a ∈ S, (p a).toReal ^ 2 ≤ pmfCollisionProb p p := by
    rw [pmfCollisionProb]
    simp_rw [← sq]
    exact sum_le_univ_sum_of_nonneg fun a => sq_nonneg _
  rw [div_le_iff₀ hS_pos]
  nlinarith

end Midpoint

/-! ### 3. Classical triangular discrimination (Le Cam divergence) -/

section TriangularDiscrimination

variable {α β : Type*} [Fintype α]

/-- Classical triangular discrimination (Vincze–Le Cam divergence) between two probability mass
functions `p` and `q` on a finite type `α`:
`TD(p, q) = (1 / 2) * ∑ x, (p(x) - q(x))² / (p(x) + q(x))`.
Terms with `p(x) = q(x) = 0` evaluate to `0 / 0 = 0`, matching summation over `supp p ∪ supp q`. -/
@[expose] noncomputable def triangularDisc (p q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, ((p a).toReal - (q a).toReal) ^ 2 / ((p a).toReal + (q a).toReal)

/-- Symmetry `TD(p, q) = TD(q, p)`. -/
theorem triangularDisc_comm (p q : PMF α) : triangularDisc p q = triangularDisc q p := by
  simp only [triangularDisc]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  ring

/-- Reflexivity `TD(p, p) = 0`. -/
@[simp]
theorem triangularDisc_self (p : PMF α) : triangularDisc p p = 0 := by
  simp [triangularDisc]

/-- Nonnegativity `0 ≤ TD(p, q)`. -/
theorem triangularDisc_nonneg (p q : PMF α) : 0 ≤ triangularDisc p q :=
  mul_nonneg (by norm_num) <| sum_nonneg fun a _ =>
    div_nonneg (sq_nonneg _) (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Triangular discrimination equals the Pearson `χ²`-divergence `χ²(p ‖ (p + q) / 2)`. -/
theorem triangularDisc_eq_chiSquare_left (p q : PMF α) :
    triangularDisc p q = chiSquare p (pmfMidpoint p q) := by
  rw [chiSquare_eq_sum (support_subset_pmfMidpoint_left p q), triangularDisc, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [toReal_pmfMidpoint]
  by_cases hsum : (p a).toReal + (q a).toReal = 0
  · have hp0 : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
    have hp : (p a).toReal = 0 := by linarith
    have hq : (q a).toReal = 0 := by linarith
    simp [hp, hq]
  · field_simp [hsum]
    ring

/-- Triangular discrimination equals the Pearson `χ²`-divergence `χ²(q ‖ (p + q) / 2)`. -/
theorem triangularDisc_eq_chiSquare_right (p q : PMF α) :
    triangularDisc p q = chiSquare q (pmfMidpoint p q) := by
  rw [triangularDisc_comm, triangularDisc_eq_chiSquare_left, pmfMidpoint_comm]

/-- Definiteness `TD(p, q) = 0 ↔ p = q`. -/
theorem triangularDisc_eq_zero_iff (p q : PMF α) : triangularDisc p q = 0 ↔ p = q := by
  rw [triangularDisc_eq_chiSquare_left, chiSquare_eq_zero_iff (support_subset_pmfMidpoint_left p q)]
  refine ⟨fun h => ?_, fun h => by subst h; simp⟩
  ext a
  apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp
  have ha := congrArg (fun r : PMF α => (r a).toReal) h
  rw [toReal_pmfMidpoint] at ha
  linarith

/-- Data-processing inequality for triangular discrimination along Markov kernels. -/
theorem triangularDisc_bind_le [Fintype β] (p q : PMF α) (kernel : α → PMF β) :
    triangularDisc (p.bind kernel) (q.bind kernel) ≤ triangularDisc p q := by
  have hmid : pmfMidpoint (p.bind kernel) (q.bind kernel) = (pmfMidpoint p q).bind kernel := by
    rw [pmfMidpoint, pmfMidpoint, PMF.bind_bind]
    congr 1
    ext b
    cases b <;> rfl
  rw [triangularDisc_eq_chiSquare_left, triangularDisc_eq_chiSquare_left, hmid]
  exact chiSquare_bind_le (support_subset_pmfMidpoint_left p q) kernel

/-- Data-processing inequality for triangular discrimination along deterministic maps. -/
theorem triangularDisc_map_le [Fintype β] (p q : PMF α) (f : α → β) :
    triangularDisc (p.map f) (q.map f) ≤ triangularDisc p q := by
  rw [triangularDisc_eq_chiSquare_left, triangularDisc_eq_chiSquare_left, ← pmfMidpoint_map]
  exact chiSquare_map_le (support_subset_pmfMidpoint_left p q) f

/-- Topsøe lower bound `SD(p, q)² ≤ TD(p, q)`. -/
theorem dist_sq_le_triangularDisc (p q : PMF α) :
    dist p q ^ 2 ≤ triangularDisc p q := by
  have h := four_mul_dist_sq_le_chiSquare (support_subset_pmfMidpoint_left p q)
  rw [← triangularDisc_eq_chiSquare_left] at h
  have hd : dist p (pmfMidpoint p q) = dist p q / 2 := by
    rw [Cslib.Probability.PMF.dist_eq, Cslib.Probability.PMF.dist_eq]
    have hterm : ∀ a, |(p a).toReal - (pmfMidpoint p q a).toReal| =
        |(p a).toReal - (q a).toReal| / 2 := fun a => by
      rw [toReal_pmfMidpoint,
        show (p a).toReal - ((p a).toReal + (q a).toReal) / 2 =
          ((p a).toReal - (q a).toReal) / 2 by ring,
        abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    simp_rw [hterm, ← sum_div]
  rw [hd] at h
  linarith

/-- Topsøe upper bound `TD(p, q) ≤ SD(p, q)`. -/
theorem triangularDisc_le_dist (p q : PMF α) :
    triangularDisc p q ≤ dist p q := by
  rw [triangularDisc, Cslib.Probability.PMF.dist_eq,
    show (∑ a, |(p a).toReal - (q a).toReal|) / 2 =
      (1 / 2 : ℝ) * ∑ a, |(p a).toReal - (q a).toReal| by ring]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) (by norm_num)
  have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
  by_cases hsum : (p a).toReal + (q a).toReal = 0
  · have hp0 : (p a).toReal = 0 := by linarith
    have hq0 : (q a).toReal = 0 := by linarith
    simp [hp0, hq0]
  · have hpos : 0 < (p a).toReal + (q a).toReal := lt_of_le_of_ne (by linarith) (Ne.symm hsum)
    rw [div_le_iff₀ hpos, ← sq_abs]
    have habs : |(p a).toReal - (q a).toReal| ≤ (p a).toReal + (q a).toReal := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg ((p a).toReal - (q a).toReal)]

/-- Upper bound `TD(p, q) ≤ 1`. -/
theorem triangularDisc_le_one (p q : PMF α) : triangularDisc p q ≤ 1 :=
  (triangularDisc_le_dist p q).trans (Cslib.Probability.PMF.dist_le_one p q)

/-- Le Cam lower bound `H²(p, q) ≤ TD(p, q)`. -/
theorem hellingerSq_le_triangularDisc (p q : PMF α) :
    hellingerSq p q ≤ triangularDisc p q := by
  rw [hellingerSq_eq_sum, triangularDisc,
    show (∑ a, (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2) / 2 =
      (1 / 2 : ℝ) * ∑ a, (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2 by ring]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) (by norm_num)
  have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
  set u := Real.sqrt (p a).toReal
  set v := Real.sqrt (q a).toReal
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (p a).toReal := Real.sq_sqrt hp
  have hv2 : v ^ 2 = (q a).toReal := Real.sq_sqrt hq
  rw [← hu2, ← hv2]
  by_cases hsum : u ^ 2 + v ^ 2 = 0
  · have hu0 : u = 0 := by nlinarith
    have hv0 : v = 0 := by nlinarith
    simp [hu0, hv0]
  · have hpos : 0 < u ^ 2 + v ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hsum)
    rw [le_div_iff₀ hpos, show (u ^ 2 - v ^ 2) ^ 2 = (u - v) ^ 2 * (u + v) ^ 2 by ring]
    have hadd : u ^ 2 + v ^ 2 ≤ (u + v) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hadd (sq_nonneg _)

/-- Le Cam upper bound `TD(p, q) ≤ 2 H²(p, q)`. -/
theorem triangularDisc_le_two_mul_hellingerSq (p q : PMF α) :
    triangularDisc p q ≤ 2 * hellingerSq p q := by
  rw [hellingerSq_eq_sum, triangularDisc,
    show 2 * ((∑ a, (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2) / 2) =
      (1 / 2 : ℝ) * ∑ a, 2 * (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2 by
      rw [← mul_sum]; ring]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) (by norm_num)
  have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
  set u := Real.sqrt (p a).toReal
  set v := Real.sqrt (q a).toReal
  have hu2 : u ^ 2 = (p a).toReal := Real.sq_sqrt hp
  have hv2 : v ^ 2 = (q a).toReal := Real.sq_sqrt hq
  rw [← hu2, ← hv2]
  by_cases hsum : u ^ 2 + v ^ 2 = 0
  · have hu0 : u = 0 := by nlinarith
    have hv0 : v = 0 := by nlinarith
    simp [hu0, hv0]
  · have hpos : 0 < u ^ 2 + v ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hsum)
    rw [div_le_iff₀ hpos, show (u ^ 2 - v ^ 2) ^ 2 = (u - v) ^ 2 * (u + v) ^ 2 by ring]
    have hadd : (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by nlinarith [sq_nonneg (u - v)]
    nlinarith [sq_nonneg (u - v)]

/-- Exact multiplicativity of `TD` under the `k`-fold parity mixture `xorMix` (`k ≠ 0`). -/
theorem triangularDisc_xorMix (p₀ p₁ : PMF α) {k : ℕ} (hk : k ≠ 0) :
    triangularDisc (xorMix p₀ p₁ k false) (xorMix p₀ p₁ k true) =
      triangularDisc p₀ p₁ ^ k := by
  have hadd : ∀ x : Fin k → α,
      (xorMix p₀ p₁ k false x).toReal + (xorMix p₀ p₁ k true x).toReal =
        (∏ i, ((p₀ (x i)).toReal + (p₁ (x i)).toReal)) / 2 ^ (k - 1) := by
    intro x
    rw [toReal_xorMix p₀ p₁ hk false x, toReal_xorMix p₀ p₁ hk true x, ← add_div]
    congr 1
    rw [← sum_add_distrib]
    have hsum : ∀ b : Fin k → Bool,
        (if Cslib.parity k b = false then ∏ i, ((bif b i then p₁ else p₀) (x i)).toReal else 0) +
        (if Cslib.parity k b = true then ∏ i, ((bif b i then p₁ else p₀) (x i)).toReal else 0) =
        ∏ i, ((bif b i then p₁ else p₀) (x i)).toReal := fun b => by
      cases Cslib.parity k b <;> simp
    simp_rw [hsum]
    rw [← Fintype.prod_sum (f := fun (i : Fin k) (c : Bool) =>
      ((bif c then p₁ else p₀) (x i)).toReal)]
    refine prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp [add_comm]
  have hterm : ∀ x : Fin k → α,
      ((xorMix p₀ p₁ k false x).toReal - (xorMix p₀ p₁ k true x).toReal) ^ 2 /
        ((xorMix p₀ p₁ k false x).toReal + (xorMix p₀ p₁ k true x).toReal) =
      (1 / 2 ^ (k - 1) : ℝ) *
        ∏ i, (((p₀ (x i)).toReal - (p₁ (x i)).toReal) ^ 2 /
          ((p₀ (x i)).toReal + (p₁ (x i)).toReal)) := by
    intro x
    rw [toReal_xorMix_sub p₀ p₁ hk x, hadd x, div_pow, ← prod_pow, prod_div_distrib]
    have h2 : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
    field_simp [h2]
  rw [triangularDisc, triangularDisc]
  simp_rw [hterm]
  rw [← mul_sum, ← Fintype.prod_sum (f := fun (_ : Fin k) (a : α) =>
    ((p₀ a).toReal - (p₁ a).toReal) ^ 2 / ((p₀ a).toReal + (p₁ a).toReal)),
    prod_const, card_fin, mul_pow, ← mul_assoc]
  congr 1
  have hpow : (1 / 2 : ℝ) * (1 / 2 ^ (k - 1)) = (1 / 2 : ℝ) ^ k := by
    cases k with
    | zero => exact absurd rfl hk
    | succ m =>
      simp only [Nat.add_sub_cancel, one_div, pow_succ, inv_pow]
      ring
  exact hpow

end TriangularDiscrimination

/-! ### 4. Classical Jensen–Shannon divergence and comparison inequalities -/

section JensenShannon

variable {α β : Type*} [Fintype α]

/-- Classical Jensen–Shannon divergence in bits (base-2 logarithm):
`JS₂(p, q) = H((p + q) / 2) - (H(p) + H(q)) / 2`,
where `H` is the base-2 Shannon entropy `Cslib.Probability.PMF.entropy`. -/
@[expose] noncomputable def jensenShannonBits (p q : PMF α) : ℝ :=
  entropy (pmfMidpoint p q) - (entropy p + entropy q) / 2

/-- Classical Jensen–Shannon divergence in nats (natural logarithm):
`JS(p, q) = ln 2 · JS₂(p, q)`. -/
@[expose] noncomputable def jensenShannon (p q : PMF α) : ℝ :=
  Real.log 2 * jensenShannonBits p q

/-- Conversion `JS₂(p, q) = JS(p, q) / ln 2`. -/
theorem jensenShannonBits_eq_div_log_two (p q : PMF α) :
    jensenShannonBits p q = jensenShannon p q / Real.log 2 := by
  rw [jensenShannon, mul_div_cancel_left₀ _ (Real.log_pos one_lt_two).ne']

/-- Symmetry `JS₂(p, q) = JS₂(q, p)`. -/
theorem jensenShannonBits_comm (p q : PMF α) :
    jensenShannonBits p q = jensenShannonBits q p := by
  rw [jensenShannonBits, jensenShannonBits, pmfMidpoint_comm, add_comm (entropy p)]

/-- Symmetry `JS(p, q) = JS(q, p)`. -/
theorem jensenShannon_comm (p q : PMF α) :
    jensenShannon p q = jensenShannon q p := by
  rw [jensenShannon, jensenShannon, jensenShannonBits_comm]

/-- Reflexivity `JS₂(p, p) = 0`. -/
@[simp]
theorem jensenShannonBits_self (p : PMF α) : jensenShannonBits p p = 0 := by
  simp [jensenShannonBits]

/-- Reflexivity `JS(p, p) = 0`. -/
@[simp]
theorem jensenShannon_self (p : PMF α) : jensenShannon p p = 0 := by
  simp [jensenShannon]

/-- Pointwise formula for `jensenShannon` in nats. -/
theorem jensenShannon_eq_sum (p q : PMF α) :
    jensenShannon p q =
      ∑ a, (Real.negMulLog (((p a).toReal + (q a).toReal) / 2) -
        (Real.negMulLog (p a).toReal + Real.negMulLog (q a).toReal) / 2) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [jensenShannon, jensenShannonBits, entropy_eq_sum, entropy_eq_sum, entropy_eq_sum]
  simp_rw [toReal_pmfMidpoint]
  rw [← add_div, ← sum_add_distrib, div_right_comm _ (Real.log 2) 2, ← sub_div,
    mul_div_cancel₀ _ hlog2, sum_div, ← sum_sub_distrib]

/-- Pointwise symmetrized-log representation: for each `a`, writing `m = (p(a) + q(a)) / 2` and
`u = (p(a) - q(a)) / (p(a) + q(a)) ∈ [-1, 1]`, the `a`-th summand of `JS(p, q)` equals
`m · ((1 + u) ln (1 + u) + (1 - u) ln (1 - u)) / 2`. -/
private theorem jensenShannon_term_eq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog ((x + y) / 2) - (Real.negMulLog x + Real.negMulLog y) / 2 =
      ((x + y) / 2) *
        (((1 + (x - y) / (x + y)) * Real.log (1 + (x - y) / (x + y)) +
          (1 - (x - y) / (x + y)) * Real.log (1 - (x - y) / (x + y))) / 2) := by
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  have h1p : 1 + (x - y) / (x + y) = 2 * x / (x + y) := by field_simp [hpos.ne']; ring
  have h1m : 1 - (x - y) / (x + y) = 2 * y / (x + y) := by field_simp [hpos.ne']; ring
  rw [h1p, h1m, Real.negMulLog, Real.negMulLog, Real.negMulLog]
  have hm_pos : 0 < (x + y) / 2 := half_pos hpos
  have hx_term : x * Real.log (2 * x / (x + y)) =
      x * Real.log x - x * Real.log ((x + y) / 2) := by
    rcases hx.eq_or_lt with rfl | hxpos
    · simp
    rw [show 2 * x / (x + y) = x / ((x + y) / 2) by field_simp [hpos.ne'],
      Real.log_div hxpos.ne' hm_pos.ne']
    ring
  have hy_term : y * Real.log (2 * y / (x + y)) =
      y * Real.log y - y * Real.log ((x + y) / 2) := by
    rcases hy.eq_or_lt with rfl | hypos
    · simp
    rw [show 2 * y / (x + y) = y / ((x + y) / 2) by field_simp [hpos.ne'],
      Real.log_div hypos.ne' hm_pos.ne']
    ring
  calc -((x + y) / 2) * Real.log ((x + y) / 2) - (-x * Real.log x + -y * Real.log y) / 2
      = ((x * Real.log x - x * Real.log ((x + y) / 2)) +
          (y * Real.log y - y * Real.log ((x + y) / 2))) / 2 := by ring
    _ = (x * Real.log (2 * x / (x + y)) + y * Real.log (2 * y / (x + y))) / 2 := by
        rw [hx_term, hy_term]
    _ = (x + y) / 2 *
        ((2 * x / (x + y) * Real.log (2 * x / (x + y)) +
          2 * y / (x + y) * Real.log (2 * y / (x + y))) / 2) := by
        field_simp [hpos.ne']

/-- Symmetrized Kullback–Leibler divergence identity:
`JS(p, q) = (KL(p ‖ (p + q) / 2) + KL(q ‖ (p + q) / 2)) / 2`. -/
theorem jensenShannon_eq_half_klDiv_add [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) :
    jensenShannon p q =
      ((InformationTheory.klDiv p.toMeasure (pmfMidpoint p q).toMeasure).toReal +
        (InformationTheory.klDiv q.toMeasure (pmfMidpoint p q).toMeasure).toReal) / 2 := by
  rw [toReal_klDiv_toMeasure (support_subset_pmfMidpoint_left p q),
    toReal_klDiv_toMeasure (support_subset_pmfMidpoint_right p q), jensenShannon_eq_sum,
    ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [toReal_pmfMidpoint, Real.negMulLog, Real.negMulLog, Real.negMulLog]
  set x := (p a).toReal
  set y := (q a).toReal
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  have hm : (x + y) / 2 ≠ 0 := (half_pos hpos).ne'
  have h1 : x * Real.log (x / ((x + y) / 2)) = x * Real.log x - x * Real.log ((x + y) / 2) := by
    rcases hx.eq_or_lt with hx0 | hxp
    · simp [← hx0]
    rw [Real.log_div hxp.ne' hm]; ring
  have h2 : y * Real.log (y / ((x + y) / 2)) = y * Real.log y - y * Real.log ((x + y) / 2) := by
    rcases hy.eq_or_lt with hy0 | hyp
    · simp [← hy0]
    rw [Real.log_div hyp.ne' hm]; ring
  rw [h1, h2]
  ring

/-- Mutual-information representation of Jensen–Shannon divergence:
`JS₂(p, q) = I(T; X)` where `(T, X) ∼ pmfBinaryJoint p q`. -/
theorem jensenShannonBits_eq_mutualInfo (p q : PMF α) :
    jensenShannonBits p q = mutualInfo (pmfBinaryJoint p q) := by
  rw [mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, pmfBinaryJoint_map_snd,
    pmfBinaryJoint, conditionalEntropy_bind_pair, Fintype.sum_bool, jensenShannonBits]
  simp only [uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ↓reduceIte, Bool.false_eq_true]
  ring

/-- Conditional-entropy representation `JS₂(p, q) = 1 - H(T | X)` for `(T, X) ∼ pmfBinaryJoint p q`
(equivalently `1 - conditionalEntropy ((pmfBinaryJoint p q).map Prod.swap)`). -/
theorem jensenShannonBits_eq_one_sub_conditionalEntropy (p q : PMF α) :
    jensenShannonBits p q = 1 - conditionalEntropy ((pmfBinaryJoint p q).map Prod.swap) := by
  have hmut : mutualInfo ((pmfBinaryJoint p q).map Prod.swap) =
      mutualInfo (pmfBinaryJoint p q) := by
    have h1 := mutualInfo_map (pmfBinaryJoint p q) Prod.snd Prod.fst
    have h2 := mutualInfo_map (pmfBinaryJoint p q) Prod.fst Prod.snd
    have hswap : entropy ((pmfBinaryJoint p q).map Prod.swap) =
        entropy (pmfBinaryJoint p q) :=
      entropy_map_of_injective _ Prod.swap_injective
    have hid : ((pmfBinaryJoint p q).map fun ω => (ω.1, ω.2)) = pmfBinaryJoint p q :=
      PMF.map_id _
    have hsw : ((pmfBinaryJoint p q).map fun ω => (ω.2, ω.1)) =
        (pmfBinaryJoint p q).map Prod.swap := rfl
    rw [hid] at h2
    rw [hsw] at h1
    linarith
  rw [jensenShannonBits_eq_mutualInfo, ← hmut,
    mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy, PMF.map_comp]
  have hsnd : Prod.snd ∘ (Prod.swap : Bool × α → α × Bool) = Prod.fst := rfl
  rw [hsnd, pmfBinaryJoint_map_fst, entropy_uniform, Fintype.card_bool, Nat.cast_ofNat,
    Real.logb_self_eq_one one_lt_two]

/-- Topsøe lower bound `(1 / 2) TD(p, q) ≤ JS(p, q)`. -/
theorem half_triangularDisc_le_jensenShannon (p q : PMF α) :
    (1 / 2 : ℝ) * triangularDisc p q ≤ jensenShannon p q := by
  rw [jensenShannon_eq_sum, triangularDisc, mul_left_comm, mul_sum, mul_sum]
  refine sum_le_sum fun a _ => ?_
  set x := (p a).toReal
  set y := (q a).toReal
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  rw [jensenShannon_term_eq x y hx hy]
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  have hu : |(x - y) / (x + y)| ≤ 1 := by
    rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hlow := half_sq_le_symmMulLog hu
  calc (1 / 2 : ℝ) * ((1 / 2) * ((x - y) ^ 2 / (x + y)))
      = ((x + y) / 2) * (((x - y) / (x + y)) ^ 2 / 2) := by field_simp [hpos.ne']
    _ ≤ ((x + y) / 2) *
        (((1 + (x - y) / (x + y)) * Real.log (1 + (x - y) / (x + y)) +
          (1 - (x - y) / (x + y)) * Real.log (1 - (x - y) / (x + y))) / 2) :=
        mul_le_mul_of_nonneg_left hlow (half_pos hpos).le

/-- Topsøe upper bound `JS(p, q) ≤ ln 2 · TD(p, q)`. -/
theorem jensenShannon_le_log_two_mul_triangularDisc (p q : PMF α) :
    jensenShannon p q ≤ Real.log 2 * triangularDisc p q := by
  rw [jensenShannon_eq_sum, triangularDisc, ← mul_assoc, mul_sum]
  refine sum_le_sum fun a _ => ?_
  set x := (p a).toReal
  set y := (q a).toReal
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  rw [jensenShannon_term_eq x y hx hy]
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  have hu : |(x - y) / (x + y)| ≤ 1 := by
    rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hup := symmMulLog_le_log_two_mul_sq hu
  calc ((x + y) / 2) *
        (((1 + (x - y) / (x + y)) * Real.log (1 + (x - y) / (x + y)) +
          (1 - (x - y) / (x + y)) * Real.log (1 - (x - y) / (x + y))) / 2)
      ≤ ((x + y) / 2) * (Real.log 2 * ((x - y) / (x + y)) ^ 2) :=
        mul_le_mul_of_nonneg_left hup (half_pos hpos).le
    _ = Real.log 2 * (1 / 2) * ((x - y) ^ 2 / (x + y)) := by field_simp [hpos.ne']

/-- Base-2 Topsøe upper bound `JS₂(p, q) ≤ TD(p, q)`. -/
theorem jensenShannonBits_le_triangularDisc (p q : PMF α) :
    jensenShannonBits p q ≤ triangularDisc p q := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact le_of_mul_le_mul_left (jensenShannon_le_log_two_mul_triangularDisc p q) hlog2

/-- Upper bound `JS₂(p, q) ≤ SD(p, q)`. -/
theorem jensenShannonBits_le_dist (p q : PMF α) :
    jensenShannonBits p q ≤ dist p q :=
  (jensenShannonBits_le_triangularDisc p q).trans (triangularDisc_le_dist p q)

/-- Natural-logarithm upper bound `JS(p, q) ≤ ln 2 · SD(p, q)`. -/
theorem jensenShannon_le_log_two_mul_dist (p q : PMF α) :
    jensenShannon p q ≤ Real.log 2 * dist p q :=
  mul_le_mul_of_nonneg_left (jensenShannonBits_le_dist p q) (Real.log_pos one_lt_two).le

/-- Nonnegativity `0 ≤ JS(p, q)`. -/
theorem jensenShannon_nonneg (p q : PMF α) : 0 ≤ jensenShannon p q :=
  le_trans (mul_nonneg (by norm_num) (triangularDisc_nonneg p q))
    (half_triangularDisc_le_jensenShannon p q)

/-- Nonnegativity `0 ≤ JS₂(p, q)`. -/
theorem jensenShannonBits_nonneg (p q : PMF α) : 0 ≤ jensenShannonBits p q := by
  rw [jensenShannonBits_eq_div_log_two]
  exact div_nonneg (jensenShannon_nonneg p q) (Real.log_pos one_lt_two).le

/-- Upper bound `JS₂(p, q) ≤ 1`. -/
theorem jensenShannonBits_le_one (p q : PMF α) : jensenShannonBits p q ≤ 1 :=
  (jensenShannonBits_le_dist p q).trans (Cslib.Probability.PMF.dist_le_one p q)

/-- Upper bound `JS(p, q) ≤ ln 2`. -/
theorem jensenShannon_le_log_two (p q : PMF α) : jensenShannon p q ≤ Real.log 2 := by
  rw [jensenShannon]
  simpa using mul_le_mul_of_nonneg_left (jensenShannonBits_le_one p q)
    (Real.log_pos one_lt_two).le

/-- Data-processing inequality for `JS₂` under deterministic post-processing. -/
theorem jensenShannonBits_map_le [Fintype β] (p q : PMF α) (f : α → β) :
    jensenShannonBits (p.map f) (q.map f) ≤ jensenShannonBits p q := by
  let _ : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace β := ⊤
  have : MeasurableSingletonClass β := ⟨fun _ => trivial⟩
  suffices h : jensenShannon (p.map f) (q.map f) ≤ jensenShannon p q from
    le_of_mul_le_mul_left h (Real.log_pos one_lt_two)
  rw [jensenShannon_eq_half_klDiv_add, jensenShannon_eq_half_klDiv_add, ← pmfMidpoint_map]
  have h1 := klDiv_toMeasure_map_le p (pmfMidpoint p q) f
  have h2 := klDiv_toMeasure_map_le q (pmfMidpoint p q) f
  have ht1 : InformationTheory.klDiv p.toMeasure (pmfMidpoint p q).toMeasure ≠ ⊤ :=
    klDiv_toMeasure_ne_top_iff.mpr (support_subset_pmfMidpoint_left p q)
  have ht2 : InformationTheory.klDiv q.toMeasure (pmfMidpoint p q).toMeasure ≠ ⊤ :=
    klDiv_toMeasure_ne_top_iff.mpr (support_subset_pmfMidpoint_right p q)
  linarith [ENNReal.toReal_mono ht1 h1, ENNReal.toReal_mono ht2 h2]

/-- Binary-distribution calculus lemma: for `0 ≤ b ≤ a ≤ 1` with `s = a - b`, the binary
Jensen–Shannon divergence satisfies `ln 2 · (1 - H₂((1 - s) / 2)) ≤ binEntropy ((a + b) / 2) -
(binEntropy a + binEntropy b) / 2`. -/
private theorem log_two_mul_one_sub_binEntropyBits_le_binary {a b : ℝ}
    (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    Real.log 2 * (1 - binEntropyBits ((1 - (a - b)) / 2)) ≤
      Real.binEntropy ((a + b) / 2) - (Real.binEntropy a + Real.binEntropy b) / 2 := by
  set s := a - b
  have hs0 : 0 ≤ s := sub_nonneg.mpr hba
  have hs1 : s ≤ 1 := by linarith
  -- Parameterize by `m = (a + b) / 2 ∈ [s / 2, 1 - s / 2]`.
  let φ : ℝ → ℝ := fun m =>
    Real.binEntropy m - (Real.binEntropy (m + s / 2) + Real.binEntropy (m - s / 2)) / 2
  have hφ_half : φ (1 / 2) = Real.log 2 * (1 - binEntropyBits ((1 - s) / 2)) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [φ, binEntropyBits]
    rw [one_div, Real.binEntropy_two_inv, mul_sub, mul_one, mul_div_cancel₀ _ hlog2,
      show (2⁻¹ : ℝ) + s / 2 = 1 - (1 - s) / 2 by ring,
      show (2⁻¹ : ℝ) - s / 2 = (1 - s) / 2 by ring, Real.binEntropy_one_sub]
    ring
  have hφ_symm : ∀ m, φ (1 - m) = φ m := fun m => by
    simp only [φ]
    rw [Real.binEntropy_one_sub m,
      show 1 - m + s / 2 = 1 - (m - s / 2) by ring,
      show 1 - m - s / 2 = 1 - (m + s / 2) by ring,
      Real.binEntropy_one_sub (m - s / 2), Real.binEntropy_one_sub (m + s / 2)]
    ring
  have hφ_cont : Continuous φ := by
    dsimp only [φ]
    fun_prop
  -- Show `φ` is increasing on `[1 / 2, 1 - s / 2]` via nonnegative derivative on `(1/2, 1 - s/2)`.
  have hφ_mono : ∀ m ∈ Set.Icc (1 / 2 : ℝ) (1 - s / 2), φ (1 / 2) ≤ φ m := by
    intro m hm
    rcases eq_or_lt_of_le hm.1 with rfl | hmlt
    · exact le_rfl
    have hderiv_nonneg : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) (1 - s / 2),
        HasDerivAt φ
          ((Real.log (1 - x) - Real.log x) -
            ((Real.log (1 - (x + s / 2)) - Real.log (x + s / 2)) +
              (Real.log (1 - (x - s / 2)) - Real.log (x - s / 2))) / 2) x ∧
        0 ≤ (Real.log (1 - x) - Real.log x) -
          ((Real.log (1 - (x + s / 2)) - Real.log (x + s / 2)) +
            (Real.log (1 - (x - s / 2)) - Real.log (x - s / 2))) / 2 := by
      intro x ⟨hx1, hx2⟩
      have hx0 : 0 < x := by linarith
      have hx1' : 0 < 1 - x := by linarith
      have hxp0 : 0 < x + s / 2 := by linarith
      have hxp1 : 0 < 1 - (x + s / 2) := by linarith
      have hxm0 : 0 < x - s / 2 := by linarith
      have hxm1 : 0 < 1 - (x - s / 2) := by linarith
      have hd1 := Real.hasDerivAt_binEntropy hx0.ne' (by linarith)
      have hd2 : HasDerivAt (fun t => Real.binEntropy (t + s / 2))
          (Real.log (1 - (x + s / 2)) - Real.log (x + s / 2)) x := by
        have h := (Real.hasDerivAt_binEntropy hxp0.ne' (by linarith)).comp x
          ((hasDerivAt_id x).add_const (s / 2))
        rw [mul_one] at h
        exact h
      have hd3 : HasDerivAt (fun t => Real.binEntropy (t - s / 2))
          (Real.log (1 - (x - s / 2)) - Real.log (x - s / 2)) x := by
        have h := (Real.hasDerivAt_binEntropy hxm0.ne' (by linarith)).comp x
          ((hasDerivAt_id x).sub_const (s / 2))
        rw [mul_one] at h
        exact h
      refine ⟨hd1.sub ((hd2.add hd3).div_const 2), ?_⟩
      -- Combine logs: `2 * d = log(((1-x)^2 * (x^2 - s^2/4)) / (x^2 * ((1-x)^2 - s^2/4))) ≥ 0`.
      have hnum : 0 < x ^ 2 - (s / 2) ^ 2 := by nlinarith
      have hden : 0 < (1 - x) ^ 2 - (s / 2) ^ 2 := by nlinarith
      have hlog_eq :
          2 * ((Real.log (1 - x) - Real.log x) -
            ((Real.log (1 - (x + s / 2)) - Real.log (x + s / 2)) +
              (Real.log (1 - (x - s / 2)) - Real.log (x - s / 2))) / 2) =
          Real.log ((1 - x) ^ 2 * (x ^ 2 - (s / 2) ^ 2)) -
            Real.log (x ^ 2 * ((1 - x) ^ 2 - (s / 2) ^ 2)) := by
        have hfx : x ^ 2 - (s / 2) ^ 2 = (x + s / 2) * (x - s / 2) := by ring
        have hf1x : (1 - x) ^ 2 - (s / 2) ^ 2 = (1 - (x + s / 2)) * (1 - (x - s / 2)) := by ring
        rw [Real.log_mul (pow_pos hx1' 2).ne' hnum.ne',
          Real.log_mul (pow_pos hx0 2).ne' hden.ne',
          Real.log_pow, Real.log_pow, hfx, hf1x,
          Real.log_mul hxp0.ne' hxm0.ne', Real.log_mul hxp1.ne' hxm1.ne']
        push_cast
        ring
      have hineq : x ^ 2 * ((1 - x) ^ 2 - (s / 2) ^ 2) ≤
          (1 - x) ^ 2 * (x ^ 2 - (s / 2) ^ 2) := by
        have hdiff : (1 - x) ^ 2 * (x ^ 2 - (s / 2) ^ 2) -
            x ^ 2 * ((1 - x) ^ 2 - (s / 2) ^ 2) =
            (s / 2) ^ 2 * (2 * x - 1) := by ring
        nlinarith [sq_nonneg (s / 2)]
      have hlog_le := Real.log_le_log (mul_pos (pow_pos hx0 2) hden) hineq
      linarith
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (1 / 2 : ℝ) (1 - s / 2))
      hφ_cont.continuousOn
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (hderiv_nonneg x hx).1.differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        rw [(hderiv_nonneg x hx).1.deriv]
        exact (hderiv_nonneg x hx).2)
    exact hmono ⟨le_rfl, hm.1.trans hm.2⟩ hm hm.1
  set m := (a + b) / 2
  have htarget : Real.binEntropy m - (Real.binEntropy a + Real.binEntropy b) / 2 = φ m := by
    simp only [φ]
    rw [show m + s / 2 = a by dsimp [m, s]; ring, show m - s / 2 = b by dsimp [m, s]; ring]
  rw [← hφ_half, htarget]
  by_cases hm_half : (1 / 2 : ℝ) ≤ m
  · exact hφ_mono m ⟨hm_half, by dsimp [m, s]; linarith⟩
  · rw [← hφ_symm m]
    exact hφ_mono (1 - m) ⟨by linarith, by dsimp [m, s]; linarith⟩

/-- Fuchs–van de Graaf / Topsøe lower bound:
`1 - H₂((1 - SD(p, q)) / 2) ≤ JS₂(p, q)` for any two probability mass functions on a finite type. -/
theorem one_sub_binEntropyBits_le_jensenShannonBits (p q : PMF α) :
    1 - binEntropyBits ((1 - dist p q) / 2) ≤ jensenShannonBits p q := by
  -- Coarsen `α → Bool` via the Scheffé event `{a | (q a).toReal < (p a).toReal}`.
  let f : α → Bool := fun a => decide ((q a).toReal < (p a).toReal)
  have hdp : jensenShannonBits (p.map f) (q.map f) ≤ jensenShannonBits p q :=
    jensenShannonBits_map_le p q f
  set P := p.map f
  set Q := q.map f
  have hP_true : (P true).toReal =
      ∑ a ∈ univ.filter (fun a => (q a).toReal < (p a).toReal), (p a).toReal := by
    rw [PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum fun a _ => by split_ifs <;> simp [p.apply_ne_top a]]
    rw [sum_filter]
    refine sum_congr rfl fun a _ => ?_
    simp only [f]
    by_cases h : (q a).toReal < (p a).toReal <;> simp [h]
  have hQ_true : (Q true).toReal =
      ∑ a ∈ univ.filter (fun a => (q a).toReal < (p a).toReal), (q a).toReal := by
    rw [PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum fun a _ => by split_ifs <;> simp [q.apply_ne_top a]]
    rw [sum_filter]
    refine sum_congr rfl fun a _ => ?_
    simp only [f]
    by_cases h : (q a).toReal < (p a).toReal <;> simp [h]
  have hdiff : (P true).toReal - (Q true).toReal = dist p q := by
    rw [hP_true, hQ_true, ← sum_sub_distrib, Cslib.Probability.PMF.dist_eq_sum_filter_lt]
  have hent : ∀ R : PMF Bool, entropy R = Real.binEntropy (R true).toReal / Real.log 2 := by
    intro R
    have hsum : (R false).toReal + (R true).toReal = 1 := by
      have h1 : ∑ b : Bool, (R b).toReal = 1 := by
        rw [← ENNReal.toReal_one, ← R.tsum_coe, tsum_fintype,
          ENNReal.toReal_sum fun b _ => R.apply_ne_top b]
      rw [Fintype.sum_bool] at h1
      linarith
    rw [entropy_eq_sum, Fintype.sum_bool, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      show (R false).toReal = 1 - (R true).toReal by linarith]
  have hjs_bool : Real.log 2 * jensenShannonBits P Q =
      Real.binEntropy (((P true).toReal + (Q true).toReal) / 2) -
        (Real.binEntropy (P true).toReal + Real.binEntropy (Q true).toReal) / 2 := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    rw [jensenShannonBits, hent, hent, hent, toReal_pmfMidpoint]
    field_simp [hlog2]
  have hP_le1 : (P true).toReal ≤ 1 := by
    have h1 : ∑ b : Bool, (P b).toReal = 1 := by
      rw [← ENNReal.toReal_one, ← P.tsum_coe, tsum_fintype,
        ENNReal.toReal_sum fun b _ => P.apply_ne_top b]
    rw [Fintype.sum_bool] at h1
    linarith [@ENNReal.toReal_nonneg (P false)]
  have hQP : (Q true).toReal ≤ (P true).toReal := by linarith [dist_nonneg (x := p) (y := q)]
  have hbin := log_two_mul_one_sub_binEntropyBits_le_binary ENNReal.toReal_nonneg hQP hP_le1
  rw [hdiff, ← hjs_bool] at hbin
  exact (le_of_mul_le_mul_left hbin (Real.log_pos one_lt_two)).trans hdp

end JensenShannon

end CslibFrontier.Probability
