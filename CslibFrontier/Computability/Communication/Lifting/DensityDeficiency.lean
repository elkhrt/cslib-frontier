/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Lifting.Density
public import CslibFrontier.Probability.MinEntropy

import CslibFrontier.Computability.Communication.Lifting.Partition
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Min-entropy deficiency and logarithmic tail-sum bounds for density restoration

Min-entropy deficiency `|J| log₂ n - H_∞(p)`, binary partition logarithmic bound, and the
universal tail-entropy bound `∑_i p_i log₂ (1 / ∑_{j ≥ i} p_j) ≤ (Real.log 2)⁻¹` used in
density-increment lifting arguments [Göös, Pitassi and Watson ].
-/

public section

namespace CslibFrontier.Computability.Communication.Lifting

open Finset

/-- Min-entropy deficiency `|J| log₂ n - H_∞(p)` of a distribution `p` on `J → α`. -/
noncomputable def minEntropyDeficiency {ι α : Type*} (n : ℕ) (J : Finset ι)
    (p : PMF (J → α)) : ℝ :=
  (#J : ℝ) * Real.logb 2 n - Cslib.Probability.PMF.minEntropy p

/-- Binary partition logarithmic inequality: for nonnegative `a, b` with `0 < a + b`,
`(a / (a + b)) log₂ ((a + b) / a) + (b / (a + b)) log₂ ((a + b) / b) ≤ 1`. -/
theorem binary_partition_logb_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    a / (a + b) * Real.logb 2 ((a + b) / a) +
      b / (a + b) * Real.logb 2 ((a + b) / b) ≤ 1 := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb_ne : b ≠ 0 := by linarith
    simp [hb_ne]
  rcases hb.eq_or_lt with rfl | hb_pos
  · have ha_ne : a ≠ 0 := ha_pos.ne'
    simp [ha_ne]
  set s := a + b
  set p := a / s
  set q := b / s
  have hp : 0 < p := div_pos ha_pos hab
  have hq : 0 < q := div_pos hb_pos hab
  have hpq : p + q = 1 := by
    dsimp only [p, q]
    rw [← add_div, div_self hab.ne']
  have h1 : p * Real.log (1 / (2 * p)) ≤ 1 / 2 - p := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (2 * p) by positivity)
    have hm := mul_le_mul_of_nonneg_left h hp.le
    have hsimp : p * (1 / (2 * p) - 1) = 1 / 2 - p := by field_simp
    linarith
  have h2 : q * Real.log (1 / (2 * q)) ≤ 1 / 2 - q := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (2 * q) by positivity)
    have hm := mul_le_mul_of_nonneg_left h hq.le
    have hsimp : q * (1 / (2 * q) - 1) = 1 / 2 - q := by field_simp
    linarith
  have hlog_p : Real.log (1 / (2 * p)) = Real.log (s / a) - Real.log 2 := by
    have hpa : 1 / (2 * p) = (s / a) / 2 := by simp only [p]; field_simp
    rw [hpa, Real.log_div (div_pos hab ha_pos).ne' two_ne_zero]
  have hlog_q : Real.log (1 / (2 * q)) = Real.log (s / b) - Real.log 2 := by
    have hqb : 1 / (2 * q) = (s / b) / 2 := by simp only [q]; field_simp
    rw [hqb, Real.log_div (div_pos hab hb_pos).ne' two_ne_zero]
  have hsum : p * Real.log (s / a) + q * Real.log (s / b) ≤ Real.log 2 := by
    rw [hlog_p, mul_sub] at h1
    rw [hlog_q, mul_sub] at h2
    have hpq_log : p * Real.log 2 + q * Real.log 2 = Real.log 2 := by
      rw [← add_mul, hpq, one_mul]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  change p * (Real.log (s / a) / Real.log 2) + q * (Real.log (s / b) / Real.log 2) ≤ 1
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_le_one hlog2]
  exact hsum

private theorem mul_neg_log_le_ent_diff {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha : 0 < a) :
    (a - b) * (-Real.log a) ≤ (a - a * Real.log a) - (b - b * Real.log b) := by
  rcases hb0.eq_or_lt with rfl | hb
  · simp only [sub_zero, zero_mul, Real.log_zero]; linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at h
    have hm := mul_le_mul_of_nonneg_left h hb.le
    have hsimp : b * (a / b - 1) = a - b := by field_simp
    linarith

private theorem sum_mul_neg_log_tail_le_ent :
    ∀ {m : ℕ} (p : Fin m → ℝ), (∀ i, 0 ≤ p i) →
      (∑ i : Fin m, p i * (-Real.log (∑ j : Fin m with i ≤ j, p j))) ≤
        (∑ i : Fin m, p i) - (∑ i : Fin m, p i) * Real.log (∑ i : Fin m, p i)
  | 0, _, _ => by simp
  | m + 1, p, hp => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    set B := ∑ k : Fin m, p k.succ
    set A := p 0 + B
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ ↦ hp k.succ
    have hp0 : 0 ≤ p 0 := hp 0
    have hBA : B ≤ A := le_add_of_nonneg_left hp0
    have h0_filter : (Finset.univ.filter fun j : Fin (m + 1) ↦ (0 : Fin (m + 1)) ≤ j) =
        Finset.univ := by ext j; simp
    have h0_sum : (∑ j : Fin (m + 1) with (0 : Fin (m + 1)) ≤ j, p j) = A := by
      rw [h0_filter, Fin.sum_univ_succ]
    have hsucc_sum : ∀ k : Fin m,
        (∑ j : Fin (m + 1) with k.succ ≤ j, p j) = ∑ j : Fin m with k ≤ j, p j.succ := by
      intro k
      rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
      have h0 : ¬ k.succ ≤ (0 : Fin (m + 1)) := Nat.not_succ_le_zero k.1
      simp [h0, Fin.succ_le_succ_iff]
    simp only [h0_sum, hsucc_sum]
    have ih := sum_mul_neg_log_tail_le_ent (fun k : Fin m ↦ p k.succ) (fun k ↦ hp k.succ)
    change p 0 * (-Real.log A) +
        ∑ k : Fin m, p k.succ * (-Real.log (∑ j : Fin m with k ≤ j, p j.succ)) ≤
      A - A * Real.log A
    rcases hp0.eq_or_lt with hp0_zero | hp0_pos
    · have hAB : A = B := by simp [A, ← hp0_zero]
      rw [← hp0_zero, zero_mul, zero_add, hAB]; exact ih
    · have hA_pos : 0 < A := add_pos_of_pos_of_nonneg hp0_pos hB0
      have hhead : p 0 * (-Real.log A) ≤ (A - A * Real.log A) - (B - B * Real.log B) := by
        have hp0_eq : p 0 = A - B := by simp [A]
        rw [hp0_eq]; exact mul_neg_log_le_ent_diff hB0 hBA hA_pos
      linarith

/-- Universal tail-entropy inequality: for any probability vector `p : Fin m → ℝ`,
`∑ i, p i * log₂ (1 / ∑_{j ≥ i} p_j) ≤ (Real.log 2)⁻¹`. -/
theorem sum_mul_logb_inv_tail_le {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    (∑ i : Fin m, p i * Real.logb 2 (1 / ∑ j : Fin m with i ≤ j, p j)) ≤
      (Real.log 2)⁻¹ := by
  have hln := sum_mul_neg_log_tail_le_ent p hp
  rw [hsum, Real.log_one, mul_zero, sub_zero] at hln
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hterm : ∀ i : Fin m,
      p i * Real.logb 2 (1 / ∑ j : Fin m with i ≤ j, p j) =
        (p i * (-Real.log (∑ j : Fin m with i ≤ j, p j))) / Real.log 2 := by
    intro i; rw [Real.logb, one_div, Real.log_inv, mul_div_assoc]
  simp only [hterm, ← Finset.sum_div]
  rw [← one_div]
  exact div_le_div_of_nonneg_right hln hlog2.le

end CslibFrontier.Computability.Communication.Lifting
