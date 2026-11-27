/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Dual
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.ConjunctionLower

import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Small-Error Approximate Degree of Conjunction

This module proves the Chebyshev-product upper bound
$\widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m) \le 20 \sqrt{m \log_2(1/\gamma)}$ and combines it
with `CslibFrontier.QueryComplexity.and_oneSidedApproxDegree_lower` to obtain the tight small-error
characterization $\widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m) = \Theta(\sqrt{m \log_2(1/\gamma)})$
for $\gamma \in [2^{-m}, 1/3]$.

## Main results

* `CslibFrontier.QueryComplexity.and_oneSidedApproxDegree_upper`:
  $\widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m) \le 20 \sqrt{m \log_2(1/\gamma)}$.
* `CslibFrontier.QueryComplexity.and_oneSidedApproxDegree_bounds`:
  tight two-sided bound $\widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m) = \Theta(\sqrt{m
  \log_2(1/\gamma)})$.
-/

public section

open scoped NNReal BigOperators
open Finset Cslib Cslib.BitString Cslib.QueryComplexity Polynomial

namespace CslibFrontier.QueryComplexity

/-! #### Upper bound via Chebyshev product -/

private lemma chebyshev_T_eval_one_add {μ : ℝ} (hμ : 0 ≤ μ) (s : ℕ) :
    (1 + Real.sqrt (2 * μ)) ^ s / 2 ≤ (Chebyshev.T ℝ s).eval (1 + μ) := by
  set α : ℝ := 1 + μ + Real.sqrt (2 * μ + μ ^ 2)
  set β : ℝ := 1 + μ - Real.sqrt (2 * μ + μ ^ 2)
  have hαβ : α * β = 1 := by
    simp only [α, β]
    have hsq : Real.sqrt (2 * μ + μ ^ 2) ^ 2 = 2 * μ + μ ^ 2 :=
      Real.sq_sqrt (by positivity)
    nlinarith
  have hsum : α + β = 2 * (1 + μ) := by simp only [α, β]; ring
  have hform : ∀ k : ℕ, (Chebyshev.T ℝ k).eval (1 + μ) = (α ^ k + β ^ k) / 2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      match k with
      | 0 => simp
      | 1 => simp [hsum]
      | k + 2 =>
        have hk0 := ih k (by omega)
        have hk1 : (Chebyshev.T ℝ ((k : ℤ) + 1)).eval (1 + μ) =
            (α ^ (k + 1) + β ^ (k + 1)) / 2 := by
          simpa [Nat.cast_add, Nat.cast_one] using ih (k + 1) (by omega)
        simp only [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two, eval_sub, eval_mul,
          eval_ofNat, eval_X, hk0, hk1]
        have hstep : 2 * (1 + μ) * ((α ^ (k + 1) + β ^ (k + 1)) / 2) - (α ^ k + β ^ k) / 2 =
            (α ^ (k + 2) + β ^ (k + 2)) / 2 := by
          rw [← hsum]
          have h1 : α ^ (k + 2) = α * α ^ (k + 1) := by ring
          have h2 : β ^ (k + 2) = β * β ^ (k + 1) := by ring
          have h3 : α * β ^ (k + 1) = β ^ k := by
            calc α * β ^ (k + 1) = (α * β) * β ^ k := by ring
              _ = β ^ k := by rw [hαβ, one_mul]
          have h4 : β * α ^ (k + 1) = α ^ k := by
            calc β * α ^ (k + 1) = (α * β) * α ^ k := by ring
              _ = α ^ k := by rw [hαβ, one_mul]
          rw [h1, h2]
          linarith
        exact hstep
  rw [hform]
  have hα_pos : 0 < α := by
    have : 0 ≤ Real.sqrt (2 * μ + μ ^ 2) := Real.sqrt_nonneg _
    linarith
  have hβ_nonneg : 0 ≤ β := by
    have : β = α⁻¹ := eq_inv_of_mul_eq_one_right hαβ
    rw [this]; positivity
  have hα_ge : 1 + Real.sqrt (2 * μ) ≤ α := by
    simp only [α]
    have : Real.sqrt (2 * μ) ≤ Real.sqrt (2 * μ + μ ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hpow : (1 + Real.sqrt (2 * μ)) ^ s ≤ α ^ s :=
    pow_le_pow_left₀ (by positivity) hα_ge s
  have hβpow : 0 ≤ β ^ s := pow_nonneg hβ_nonneg s
  linarith

private lemma chebyshev_T_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) (s : ℕ) :
    0 < (Chebyshev.T ℝ s).eval x := by
  have h := chebyshev_T_eval_one_add (μ := x - 1) (by linarith) s
  rw [show 1 + (x - 1) = x by ring] at h
  have hpos : (0 : ℝ) < (1 + Real.sqrt (2 * (x - 1))) ^ s / 2 := by positivity
  linarith

private lemma chebyshev_T_mono_of_one_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (s : ℕ) :
    (Chebyshev.T ℝ s).eval x ≤ (Chebyshev.T ℝ s).eval y := by
  have hform : ∀ (u : ℝ), 1 ≤ u →
      (Chebyshev.T ℝ s).eval u =
        ((u + Real.sqrt (u ^ 2 - 1)) ^ s + (u + Real.sqrt (u ^ 2 - 1))⁻¹ ^ s) / 2 := by
    intro u hu
    set α : ℝ := u + Real.sqrt (u ^ 2 - 1)
    set β : ℝ := u - Real.sqrt (u ^ 2 - 1)
    have hsq : Real.sqrt (u ^ 2 - 1) ^ 2 = u ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have hαβ : α * β = 1 := by simp only [α, β]; nlinarith
    have hβ_eq : β = α⁻¹ := eq_inv_of_mul_eq_one_right hαβ
    have hsum : α + β = 2 * u := by simp only [α, β]; ring
    have hind : ∀ k : ℕ, (Chebyshev.T ℝ k).eval u = (α ^ k + β ^ k) / 2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        match k with
        | 0 => simp
        | 1 => simp [hsum]
        | k + 2 =>
          have hk0 := ih k (by omega)
          have hk1 : (Chebyshev.T ℝ ((k : ℤ) + 1)).eval u =
              (α ^ (k + 1) + β ^ (k + 1)) / 2 := by
            simpa [Nat.cast_add, Nat.cast_one] using ih (k + 1) (by omega)
          simp only [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two, eval_sub, eval_mul,
            eval_ofNat, eval_X, hk0, hk1]
          rw [← hsum]
          have h1 : α ^ (k + 2) = α * α ^ (k + 1) := by ring
          have h2 : β ^ (k + 2) = β * β ^ (k + 1) := by ring
          have h3 : α * β ^ (k + 1) = β ^ k := by
            calc α * β ^ (k + 1) = (α * β) * β ^ k := by ring
              _ = β ^ k := by rw [hαβ, one_mul]
          have h4 : β * α ^ (k + 1) = α ^ k := by
            calc β * α ^ (k + 1) = (α * β) * α ^ k := by ring
              _ = α ^ k := by rw [hαβ, one_mul]
          rw [h1, h2]; linarith
    rw [hind s, hβ_eq]
  rw [hform x hx, hform y (hx.trans hxy)]
  set a := x + Real.sqrt (x ^ 2 - 1)
  set b := y + Real.sqrt (y ^ 2 - 1)
  have ha1 : 1 ≤ a := by
    have : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _; linarith
  have hab : a ≤ b := by
    have : Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt (y ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hkey : a ^ s + a⁻¹ ^ s ≤ b ^ s + b⁻¹ ^ s := by
    have hdiff : (b ^ s + b⁻¹ ^ s) - (a ^ s + a⁻¹ ^ s) =
        (b ^ s - a ^ s) * (1 - (a * b)⁻¹ ^ s) := by
      have ha0 : a ≠ 0 := by linarith
      have hb0 : b ≠ 0 := by linarith
      simp only [inv_pow, mul_pow]
      field_simp [pow_ne_zero s ha0, pow_ne_zero s hb0]; ring
    have h1 : 0 ≤ b ^ s - a ^ s := sub_nonneg.mpr (pow_le_pow_left₀ (by linarith) hab s)
    have h2 : 0 ≤ 1 - (a * b)⁻¹ ^ s := by
      have hab1 : 1 ≤ a * b := by nlinarith
      have hinv : (a * b)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hab1
      have : (a * b)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by positivity) hinv
      linarith
    nlinarith
  linarith

private lemma one_sub_cos_le_half_sq (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]

private lemma sum_inv_sqrt_le (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (Real.sqrt (j : ℝ))⁻¹ ≤ 2 * Real.sqrt (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have hstep : (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
      have hs1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hs0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hsq1 : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 = (k : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hsq0 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
      have hdiff : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (k : ℝ) ^ 2 = 1 := by linarith
      rw [inv_le_iff_one_le_mul₀' hs1]
      nlinarith [Real.sqrt_le_sqrt (show (k : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ k)]
    linarith

/-- **Small-error approximate degree upper bound for $\mathrm{AND}_m$**
: for every `m ≥ 1` and `γ ∈ [2^{-m}, 1/3]`,
`oneSidedApproxDegree γ (threshold m m) ≤ 20 * √(m * log₂(1 / γ))`.
-/
theorem and_oneSidedApproxDegree_upper {m : ℕ} {γ : ℝ} (hm : 1 ≤ m)
    (hγlo : (2 : ℝ) ^ (-(m : ℤ)) ≤ γ) (hγhi : γ ≤ 1 / 3) :
    (oneSidedApproxDegree γ (threshold m m) : ℝ) ≤
      20 * Real.sqrt (m * Real.logb 2 (1 / γ)) := by
  have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγlo
  rw [oneSidedApproxDegree_and_eq_signApproxDegree hγpos.le, signApproxDegree_and_eq_or hγpos.le]
  set d := signApproxDegree γ (threshold m 1)
  have hlog_pos : 1 ≤ Real.logb 2 (1 / γ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
    rw [le_div_iff₀ hγpos]; linarith
  set k : ℕ := ⌈Real.logb 2 (2 / γ)⌉₊
  have hlog2_eq : Real.logb 2 (2 / γ) = 1 + Real.logb 2 (1 / γ) := by
    rw [show (2 : ℝ) / γ = 2 * (1 / γ) by ring,
      Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have hk_ge : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    have hle1 : Real.logb 2 (2 / γ) ≤ 1 := (Nat.le_ceil _).trans (by exact_mod_cast hk1)
    linarith
  have hk_le : (k : ℝ) ≤ 3 * Real.logb 2 (1 / γ) := by
    have h1 : (k : ℝ) < Real.logb 2 (2 / γ) + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have h2pow_k : 2 / γ ≤ (2 : ℝ) ^ k := by
    have hceil : Real.logb 2 (2 / γ) ≤ (k : ℝ) := Nat.le_ceil _
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast] at hceil
    exact hceil
  by_cases hkm : m ≤ k
  · -- Exact polynomial of degree `m` suffices.
    have hdm : (d : ℝ) ≤ m := by exact_mod_cast signApproxDegree_le_card hγpos.le (threshold m 1)
    have hm_le_sq : (m : ℝ) ^ 2 ≤ 3 * (m : ℝ) * Real.logb 2 (1 / γ) := by
      have hm_le_k : (m : ℝ) ≤ k := by exact_mod_cast hkm
      nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    have hsqrt : (m : ℝ) ≤ Real.sqrt (3 * (m : ℝ) * Real.logb 2 (1 / γ)) := by
      conv_lhs => rw [← Real.sqrt_sq (Nat.cast_nonneg m)]
      exact Real.sqrt_le_sqrt hm_le_sq
    have h3 : Real.sqrt (3 * ((m : ℝ) * Real.logb 2 (1 / γ))) =
        Real.sqrt 3 * Real.sqrt ((m : ℝ) * Real.logb 2 (1 / γ)) :=
      Real.sqrt_mul (by norm_num) _
    have hs3 : Real.sqrt 3 ≤ 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [show 3 * (m : ℝ) * Real.logb 2 (1 / γ) = 3 * ((m : ℝ) * Real.logb 2 (1 / γ)) by ring, h3]
      at hsqrt
    nlinarith [Real.sqrt_nonneg ((m : ℝ) * Real.logb 2 (1 / γ))]
  · -- Chebyshev product `Q_k * ∏_{j=1}^{k-1} Q_j` for `2 ≤ k < m`.
    push Not at hkm
    set sk : ℕ := ⌈2 * Real.sqrt ((m : ℝ) * (k : ℝ))⌉₊
    set Lk : ℝ[X] := C (((m : ℝ) + k) / ((m : ℝ) - k)) - C (2 / ((m : ℝ) - k)) * X
    have hmk_pos : (0 : ℝ) < (m : ℝ) - (k : ℝ) := by
      have : (k : ℝ) < m := by exact_mod_cast hkm
      linarith
    have hLk_eval : ∀ t : ℝ, Lk.eval t = ((m : ℝ) + k - 2 * t) / ((m : ℝ) - k) := by
      intro t; simp only [Lk, eval_sub, eval_C, eval_mul, eval_X]; ring
    have hLk0 : Lk.eval 0 = 1 + 2 * (k : ℝ) / ((m : ℝ) - k) := by
      rw [hLk_eval]; field_simp [hmk_pos.ne']; ring
    have hTk0_pos : 0 < (Chebyshev.T ℝ sk).eval (Lk.eval 0) :=
      chebyshev_T_pos_of_one_le
        (by rw [hLk0]; exact le_add_of_nonneg_right (by positivity)) sk
    have hTk0_ge : 2 / γ ≤ (Chebyshev.T ℝ sk).eval (Lk.eval 0) := by
      have hμ : 2 * (k : ℝ) / (m : ℝ) ≤ 2 * (k : ℝ) / ((m : ℝ) - k) :=
        div_le_div_of_nonneg_left (by positivity) hmk_pos (by linarith)
      have hcheb := chebyshev_T_eval_one_add (μ := 2 * (k : ℝ) / ((m : ℝ) - k)) (by positivity) sk
      have hsqrt_ge : 2 * Real.sqrt ((k : ℝ) / (m : ℝ)) ≤
          Real.sqrt (2 * (2 * (k : ℝ) / ((m : ℝ) - k))) := by
        have h4 : 4 * ((k : ℝ) / (m : ℝ)) ≤ 2 * (2 * (k : ℝ) / ((m : ℝ) - k)) := by
          calc 4 * ((k : ℝ) / (m : ℝ)) = 2 * (2 * (k : ℝ) / (m : ℝ)) := by ring
            _ ≤ 2 * (2 * (k : ℝ) / ((m : ℝ) - k)) := by linarith
        calc 2 * Real.sqrt ((k : ℝ) / (m : ℝ))
            = Real.sqrt (4 * ((k : ℝ) / (m : ℝ))) := by
              rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          _ ≤ Real.sqrt (2 * (2 * (k : ℝ) / ((m : ℝ) - k))) := Real.sqrt_le_sqrt h4
      -- Since `k < m`, `x := 2 * √(k/m) ≤ 2`, so `1 + x ≥ 2^(x/2)`.
      have hx_le2 : 2 * Real.sqrt ((k : ℝ) / (m : ℝ)) ≤ 2 := by
        have h1 : (k : ℝ) / (m : ℝ) ≤ 1 :=
          (div_le_one (by positivity)).mpr (by exact_mod_cast hkm.le)
        have h2 : Real.sqrt ((k : ℝ) / (m : ℝ)) ≤ 1 := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h1
        linarith
      have h2rpow : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → (2 : ℝ) ^ (x / 2) ≤ 1 + x := by
        intro x hx0 hx2
        have ht0 : 0 ≤ x / 2 := by linarith
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2)]
        have hce := (convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log 2))
          (show (0 : ℝ) ≤ 1 - x / 2 by linarith) ht0 (by ring : (1 - x / 2) + x / 2 = 1))
        simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hce
        linarith
      have hbase : (2 : ℝ) ^ Real.sqrt ((k : ℝ) / (m : ℝ)) ≤
          1 + Real.sqrt (2 * (2 * (k : ℝ) / ((m : ℝ) - k))) := by
        have h1 := h2rpow (2 * Real.sqrt ((k : ℝ) / (m : ℝ))) (by positivity) hx_le2
        rw [show 2 * Real.sqrt ((k : ℝ) / (m : ℝ)) / 2 =
          Real.sqrt ((k : ℝ) / (m : ℝ)) by ring] at h1
        linarith
      have hpow_ge : (2 : ℝ) ^ (2 * (k : ℝ)) ≤
          (1 + Real.sqrt (2 * (2 * (k : ℝ) / ((m : ℝ) - k)))) ^ sk := by
        have hsk_ge : 2 * Real.sqrt ((m : ℝ) * (k : ℝ)) ≤ (sk : ℝ) := Nat.le_ceil _
        have hexp_ge : 2 * (k : ℝ) ≤ Real.sqrt ((k : ℝ) / (m : ℝ)) * (sk : ℝ) := by
          have hmpos : (0 : ℝ) < m := by positivity
          have hmul_eq : Real.sqrt ((k : ℝ) / (m : ℝ)) * (2 * Real.sqrt ((m : ℝ) * (k : ℝ))) =
              2 * (k : ℝ) := by
            rw [Real.sqrt_div (Nat.cast_nonneg k), Real.sqrt_mul (Nat.cast_nonneg m)]
            have hms : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hmpos).ne'
            field_simp [hms]
            rw [Real.sq_sqrt (Nat.cast_nonneg k)]
          calc 2 * (k : ℝ)
              = Real.sqrt ((k : ℝ) / (m : ℝ)) * (2 * Real.sqrt ((m : ℝ) * (k : ℝ))) := hmul_eq.symm
            _ ≤ Real.sqrt ((k : ℝ) / (m : ℝ)) * (sk : ℝ) :=
                mul_le_mul_of_nonneg_left hsk_ge (Real.sqrt_nonneg _)
        calc (2 : ℝ) ^ (2 * (k : ℝ))
            ≤ (2 : ℝ) ^ (Real.sqrt ((k : ℝ) / (m : ℝ)) * (sk : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge
          _ = ((2 : ℝ) ^ Real.sqrt ((k : ℝ) / (m : ℝ))) ^ (sk : ℝ) :=
              Real.rpow_mul (by norm_num) _ _
          _ = ((2 : ℝ) ^ Real.sqrt ((k : ℝ) / (m : ℝ))) ^ sk := Real.rpow_natCast _ _
          _ ≤ (1 + Real.sqrt (2 * (2 * (k : ℝ) / ((m : ℝ) - k)))) ^ sk :=
              pow_le_pow_left₀ (by positivity) hbase sk
      have h2k_ge : (2 : ℝ) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * (k : ℝ)) := by
        have hk2_r : (2 : ℝ) ≤ k := by exact_mod_cast hk_ge
        have h1 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by linarith
        calc (2 : ℝ) * (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) + 1) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one, mul_comm]
          _ ≤ (2 : ℝ) ^ (2 * (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      rw [hLk0]
      linarith
    let Qk : ℝ[X] := C (((Chebyshev.T ℝ sk).eval (Lk.eval 0))⁻¹) * (Chebyshev.T ℝ sk).comp Lk
    let sJ : ℕ → ℕ := fun j => ⌈Real.sqrt ((m : ℝ) / (j : ℝ))⌉₊ + 1
    let LJ : ℕ → ℝ[X] := fun j =>
      1 - C ((1 - Real.cos (Real.pi / (2 * (sJ j : ℝ)))) / (j : ℝ)) * X
    let QJ : ℕ → ℝ[X] := fun j => (Chebyshev.T ℝ (sJ j)).comp (LJ j)
    let Q : ℝ[X] := Qk * ∏ j ∈ Finset.Icc 1 (k - 1), QJ j
    have hQ_eval0 : Q.eval 0 = 1 := by
      simp only [Q, eval_mul, eval_prod, Qk, eval_C, eval_comp,
        inv_mul_cancel₀ hTk0_pos.ne']
      rw [one_mul]
      refine Finset.prod_eq_one fun j _ => ?_
      simp [QJ, LJ]
    have hQ_eval_small : ∀ t : ℕ, 1 ≤ t → t < k → Q.eval (t : ℝ) = 0 := by
      intro t ht1 htk
      have hmem : t ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨ht1, by omega⟩
      simp only [Q, eval_mul, eval_prod]
      rw [Finset.prod_eq_zero hmem]
      · ring
      · simp only [QJ, LJ, eval_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
        have htne : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have harg : 1 - (1 - Real.cos (Real.pi / (2 * (sJ t : ℝ)))) / (t : ℝ) * (t : ℝ) =
            Real.cos (Real.pi / (2 * (sJ t : ℝ))) := by field_simp [htne]; ring
        rw [harg, Chebyshev.T_real_cos]
        have hsJ_ne : (sJ t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp [sJ])
        have harg2 : (sJ t : ℝ) * (Real.pi / (2 * (sJ t : ℝ))) = Real.pi / 2 := by
          field_simp [hsJ_ne]
        rw [Int.cast_natCast, harg2, Real.cos_pi_div_two]
    have hQJ_abs : ∀ j ∈ Finset.Icc 1 (k - 1), ∀ t : ℕ, t ≤ m →
        |(QJ j).eval (t : ℝ)| ≤ 1 := by
      intro j hj t htm
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      simp only [QJ, LJ, eval_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
      refine Chebyshev.abs_eval_T_real_le_one (sJ j) ?_
      have hcos_le1 : Real.cos (Real.pi / (2 * (sJ j : ℝ))) ≤ 1 := Real.cos_le_one _
      have h1sub : 1 - Real.cos (Real.pi / (2 * (sJ j : ℝ))) ≤ 2 / (sJ j : ℝ) ^ 2 := by
        have h1 := one_sub_cos_le_half_sq (Real.pi / (2 * (sJ j : ℝ)))
        have hpi : Real.pi < 4 := Real.pi_lt_four
        have hsJ_pos : (0 : ℝ) < sJ j := by exact_mod_cast (show 0 < sJ j by simp [sJ])
        have hsq : (Real.pi / (2 * (sJ j : ℝ))) ^ 2 / 2 ≤ 2 / (sJ j : ℝ) ^ 2 := by
          rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
          nlinarith [sq_pos_of_pos hsJ_pos]
        linarith
      have hsJ_sq : (m : ℝ) / (j : ℝ) ≤ (sJ j : ℝ) ^ 2 := by
        have h1 : Real.sqrt ((m : ℝ) / (j : ℝ)) ≤ (sJ j : ℝ) := by
          have := Nat.le_ceil (Real.sqrt ((m : ℝ) / (j : ℝ)))
          have hlt : (⌈Real.sqrt ((m : ℝ) / (j : ℝ))⌉₊ : ℝ) ≤ (sJ j : ℝ) := by
            simp only [sJ]; push_cast; linarith
          exact this.trans hlt
        have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
        rwa [Real.sq_sqrt (by positivity)] at hsq
      have hterm_le2 : (1 - Real.cos (Real.pi / (2 * (sJ j : ℝ)))) / (j : ℝ) * (t : ℝ) ≤ 2 := by
        have htm_r : (t : ℝ) ≤ m := by exact_mod_cast htm
        calc (1 - Real.cos (Real.pi / (2 * (sJ j : ℝ)))) / (j : ℝ) * (t : ℝ)
            ≤ (2 / (sJ j : ℝ) ^ 2) / (j : ℝ) * (m : ℝ) := by
              have hnonneg : 0 ≤ (1 - Real.cos (Real.pi / (2 * (sJ j : ℝ)))) / (j : ℝ) :=
                div_nonneg (by linarith) hjpos.le
              have hstep1 := mul_le_mul_of_nonneg_left htm_r hnonneg
              have hstep2 := mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_right h1sub hjpos.le) (Nat.cast_nonneg m)
              exact hstep1.trans hstep2
          _ = 2 * (((m : ℝ) / (j : ℝ)) / (sJ j : ℝ) ^ 2) := by ring
          _ ≤ 2 * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact (div_le_one (by positivity)).mpr hsJ_sq
          _ = 2 := mul_one 2
      have hterm_nn : 0 ≤ (1 - Real.cos (Real.pi / (2 * (sJ j : ℝ)))) / (j : ℝ) * (t : ℝ) :=
        mul_nonneg (div_nonneg (by linarith) hjpos.le) (Nat.cast_nonneg t)
      rw [abs_le]
      constructor <;> linarith
    have hQ_eval_large : ∀ t : ℕ, k ≤ t → t ≤ m → |Q.eval (t : ℝ)| ≤ γ / 2 := by
      intro t hkt htm
      simp only [Q, eval_mul, eval_prod, abs_mul, Finset.abs_prod]
      have hprod_le1 : ∏ j ∈ Finset.Icc 1 (k - 1), |(QJ j).eval (t : ℝ)| ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j hj => hQJ_abs j hj t htm)
      have hQk_le : |Qk.eval (t : ℝ)| ≤ γ / 2 := by
        simp only [Qk, eval_mul, eval_C, eval_comp, abs_mul, abs_inv, abs_of_pos hTk0_pos]
        have hL_abs : |Lk.eval (t : ℝ)| ≤ 1 := by
          rw [hLk_eval, abs_le, le_div_iff₀ hmk_pos, div_le_iff₀ hmk_pos]
          have hkt_r : (k : ℝ) ≤ t := by exact_mod_cast hkt
          have htm_r : (t : ℝ) ≤ m := by exact_mod_cast htm
          constructor <;> linarith
        have hT_le := Chebyshev.abs_eval_T_real_le_one sk hL_abs
        calc ((Chebyshev.T ℝ sk).eval (Lk.eval 0))⁻¹ * |(Chebyshev.T ℝ sk).eval (Lk.eval (t : ℝ))|
            ≤ ((Chebyshev.T ℝ sk).eval (Lk.eval 0))⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left hT_le (inv_nonneg.mpr hTk0_pos.le)
          _ = ((Chebyshev.T ℝ sk).eval (Lk.eval 0))⁻¹ := mul_one _
          _ ≤ (2 / γ)⁻¹ := inv_anti₀ (by positivity) hTk0_ge
          _ = γ / 2 := by rw [inv_div]
      calc |Qk.eval (t : ℝ)| * ∏ j ∈ Finset.Icc 1 (k - 1), |(QJ j).eval (t : ℝ)|
          ≤ (γ / 2) * 1 := mul_le_mul hQk_le hprod_le1 (Finset.prod_nonneg fun _ _ => abs_nonneg _)
            (by positivity)
        _ = γ / 2 := mul_one _
    -- Construct `P := 2 • Q - 1` approximating `signVal (OR_m x)` to within `γ`.
    let P : ℝ[X] := C (2 : ℝ) * Q - 1
    have hP_deg : P.natDegree ≤ sk + ∑ j ∈ Finset.Icc 1 (k - 1), sJ j := by
      have hLk_deg : Lk.natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le ((natDegree_C _).le.trans zero_le_one)
          ((natDegree_C_mul_le _ _).trans natDegree_X_le))
      have hQk_deg : Qk.natDegree ≤ sk := by
        refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
        rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
        exact (Nat.mul_le_mul_left sk hLk_deg).trans_eq (mul_one sk)
      have hQJ_deg : ∀ j, (QJ j).natDegree ≤ sJ j := by
        intro j
        have hLJ_deg : (LJ j).natDegree ≤ 1 :=
          (natDegree_sub_le _ _).trans (max_le (by simp)
            ((natDegree_C_mul_le _ _).trans natDegree_X_le))
        refine natDegree_comp_le.trans ?_
        rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
        exact (Nat.mul_le_mul_left (sJ j) hLJ_deg).trans_eq (mul_one _)
      have hQ_deg : Q.natDegree ≤ sk + ∑ j ∈ Finset.Icc 1 (k - 1), sJ j := by
        refine (natDegree_mul_le).trans ?_
        refine Nat.add_le_add hQk_deg ?_
        refine (natDegree_prod_le _ _).trans ?_
        exact Finset.sum_le_sum fun j _ => hQJ_deg j
      exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hQ_deg) (by simp))
    have hd_le_P : d ≤ sk + ∑ j ∈ Finset.Icc 1 (k - 1), sJ j := by
      refine signApproxDegree_le_of_mem_lowDegree
        (p := fun x => P.eval (weight x : ℝ))
        (lowDegree_mono hP_deg (eval_weight_mem_lowDegree P)) fun x => ?_
      rw [threshold_apply]
      have hw_le : weight x ≤ m := by simpa [Fintype.card_fin] using weight_le x
      simp only [P, eval_sub, eval_mul, eval_C, eval_one]
      rcases Nat.eq_zero_or_pos (weight x) with hw0 | hwpos
      · rw [hw0, Nat.cast_zero, hQ_eval0]
        simp only [mul_one, nonpos_iff_eq_zero, one_ne_zero, decide_false, signVal_false]
        norm_num; exact hγpos.le
      · rw [decide_eq_true (Nat.succ_le_of_lt hwpos), signVal_true]
        have hrew : 2 * Q.eval (weight x : ℝ) - 1 - (-1) = 2 * Q.eval (weight x : ℝ) := by ring
        rw [hrew, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        by_cases hwk : weight x < k
        · rw [hQ_eval_small (weight x) hwpos hwk, abs_zero, mul_zero]; exact hγpos.le
        · push Not at hwk
          linarith [hQ_eval_large (weight x) hwk hw_le]
    -- Bound `sk + ∑_{j=1}^{k-1} sJ j ≤ 20 * √(m * log₂(1 / γ))`.
    have hsk_le : (sk : ℝ) ≤ 2 * Real.sqrt ((m : ℝ) * (k : ℝ)) + 1 := by
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hsum_sJ : (∑ j ∈ Finset.Icc 1 (k - 1), sJ j : ℝ) ≤
        2 * Real.sqrt ((m : ℝ) * (k : ℝ)) + 2 * (k : ℝ) := by
      have hterm_sJ : ∀ j ∈ Finset.Icc 1 (k - 1),
          (sJ j : ℝ) ≤ Real.sqrt (m : ℝ) * (Real.sqrt (j : ℝ))⁻¹ + 2 := by
        intro j _
        simp only [sJ]
        push_cast
        have hc := (Nat.ceil_lt_add_one (Real.sqrt_nonneg ((m : ℝ) / (j : ℝ)))).le
        have hdiv : Real.sqrt ((m : ℝ) / (j : ℝ)) = Real.sqrt (m : ℝ) * (Real.sqrt (j : ℝ))⁻¹ := by
          rw [Real.sqrt_div (Nat.cast_nonneg m), div_eq_mul_inv]
        linarith
      calc (∑ j ∈ Finset.Icc 1 (k - 1), (sJ j : ℝ))
          ≤ ∑ j ∈ Finset.Icc 1 (k - 1), (Real.sqrt (m : ℝ) * (Real.sqrt (j : ℝ))⁻¹ + 2) :=
            Finset.sum_le_sum hterm_sJ
        _ = Real.sqrt (m : ℝ) * (∑ j ∈ Finset.Icc 1 (k - 1), (Real.sqrt (j : ℝ))⁻¹) +
              2 * ((Finset.Icc 1 (k - 1)).card : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
              mul_comm _ 2]
        _ ≤ Real.sqrt (m : ℝ) * (2 * Real.sqrt ((k - 1 : ℕ) : ℝ)) + 2 * (k : ℝ) := by
            have h1 := sum_inv_sqrt_le (k - 1)
            have hcard : ((Finset.Icc 1 (k - 1)).card : ℝ) ≤ (k : ℝ) := by
              rw [Nat.card_Icc]; exact_mod_cast (show k - 1 + 1 - 1 ≤ k by omega)
            nlinarith [Real.sqrt_nonneg (m : ℝ)]
        _ ≤ 2 * Real.sqrt ((m : ℝ) * (k : ℝ)) + 2 * (k : ℝ) := by
            have hle : Real.sqrt ((k - 1 : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) :=
              Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le k 1)
            have hmul : Real.sqrt (m : ℝ) * Real.sqrt (k : ℝ) = Real.sqrt ((m : ℝ) * (k : ℝ)) :=
              (Real.sqrt_mul (Nat.cast_nonneg m) _).symm
            nlinarith [Real.sqrt_nonneg (m : ℝ)]
    have htot_cast : (d : ℝ) ≤ (sk : ℝ) + ∑ j ∈ Finset.Icc 1 (k - 1), (sJ j : ℝ) := by
      exact_mod_cast hd_le_P
    have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        nlinarith)
    have hk_le_sqrt : (k : ℝ) ≤ Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      conv_lhs => rw [← Real.sqrt_sq (Nat.cast_nonneg k)]
      exact Real.sqrt_le_sqrt (by
        have : (k : ℝ) ≤ m := by exact_mod_cast hkm.le
        nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
    have hmk_le : Real.sqrt ((m : ℝ) * (k : ℝ)) ≤
        Real.sqrt 3 * Real.sqrt ((m : ℝ) * Real.logb 2 (1 / γ)) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m])
    have hs3 : Real.sqrt 3 ≤ 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg ((m : ℝ) * Real.logb 2 (1 / γ))]


/-- **Small-error approximate degree of $\mathrm{AND}_m$**
: there exist universal constants `0 < δ_AND` and `δ'_AND` such that for
every `m ≥ 1` and `γ ∈ [2^{-m}, 1/3]`,
`δ_AND * √(m * log₂(1 / γ)) < oneSidedApproxDegree γ (threshold m m) ≤
  δ'_AND * √(m * log₂(1 / γ))`.
-/
theorem and_oneSidedApproxDegree_bounds :
    ∃ (δ δ' : ℝ), 0 < δ ∧ 0 < δ' ∧
      ∀ (m : ℕ) (γ : ℝ), 1 ≤ m → (2 : ℝ) ^ (-(m : ℤ)) ≤ γ → γ ≤ 1 / 3 →
        δ * Real.sqrt (m * Real.logb 2 (1 / γ)) <
          (oneSidedApproxDegree γ (threshold m m) : ℝ) ∧
        (oneSidedApproxDegree γ (threshold m m) : ℝ) ≤
          δ' * Real.sqrt (m * Real.logb 2 (1 / γ)) :=
  ⟨1 / 25, 20, by norm_num, by norm_num, fun _ _ hm hγlo hγhi =>
    ⟨and_oneSidedApproxDegree_lower hm hγlo hγhi, and_oneSidedApproxDegree_upper hm hγlo hγhi⟩⟩

end CslibFrontier.QueryComplexity
