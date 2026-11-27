/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Asymptotics.CostBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compositional combinators and linearithmic bounds for `Cslib.CostIsBigO`

Extends `CslibFrontier.Foundations.Analysis.Asymptotics.CostBound` (`Cslib.CostIsBigO`) with
constant, additive, scalar-multiple, and multiplicative composition combinators together with
ceiling-logarithm bounds (`Nat.clog 2 n ≤ n`, `(Nat.clog 2 n : ℝ) ≤ (2 / Real.log 2) * Real.log n`)
and linearithmic / quadratic comparison lemmas (`n * Real.log n =O[atTop] n ^ 2`).

## Main results

* `CslibFrontier.CostIsBigO.const`: bounded constant operation counts satisfy `CostIsBigO`.
* `CslibFrontier.CostIsBigO.add`, `CslibFrontier.CostIsBigO.add_of_isBigO`: sequential sum of
  `CostIsBigO` bounds.
* `CslibFrontier.CostIsBigO.const_mul`, `CslibFrontier.CostIsBigO.mul`: constant-multiple and
  product composition of `CostIsBigO` bounds.
* `CslibFrontier.CostIsBigO.clog_two_le_self`,
  `CslibFrontier.CostIsBigO.cast_clog_two_le_mul_log`: binary ceiling-logarithm bounds.
* `CslibFrontier.CostIsBigO.of_le_linear_add_mul_clog`: operation counts bounded by
  `a + b * size x + c * (size x * Nat.clog 2 (size x))` are `O(n * Real.log n)`.
* `CslibFrontier.CostIsBigO.isBigO_mul_log_sq`: `n * Real.log n =O[atTop] n ^ 2`.
-/

public section

open Asymptotics Cslib Filter

namespace CslibFrontier.CostIsBigO

section Combinators

variable {α ι : Type*} [Preorder ι] {l : Filter ι} {size : α → ι}

/-- A cost uniformly bounded by a constant `c : ℕ` is `O(1)` along any filter `l`. -/
theorem const {cost : α → ℕ} (c : ℕ) (hc : ∀ x, cost x ≤ c) :
    CostIsBigO l (fun _ ↦ (1 : ℝ)) size cost := by
  refine CostIsBigO.of_le_nat (F := fun _ ↦ c) monotone_const ?_ hc
  refine IsBigO.of_bound (c : ℝ) (Eventually.of_forall fun _ ↦ ?_)
  simp

/-- Sequential sum of two costs sharing the same asymptotic bound `g`. -/
theorem add {g : ι → ℝ} {cost₁ cost₂ : α → ℕ}
    (h₁ : CostIsBigO l g size cost₁) (h₂ : CostIsBigO l g size cost₂) :
    CostIsBigO l g size (fun x ↦ cost₁ x + cost₂ x) := by
  obtain ⟨f₁, hf₁_mono, hf₁_nn, hf₁_O, hb₁⟩ := h₁
  obtain ⟨f₂, hf₂_mono, hf₂_nn, hf₂_O, hb₂⟩ := h₂
  refine ⟨fun i ↦ f₁ i + f₂ i, hf₁_mono.add hf₂_mono, add_nonneg hf₁_nn hf₂_nn, hf₁_O.add hf₂_O,
    fun x ↦ ?_⟩
  push_cast
  exact add_le_add (hb₁ x) (hb₂ x)

/-- Sequential sum of two costs whose respective bounds `g₁, g₂` are each `O(g)`. -/
theorem add_of_isBigO {g₁ g₂ g : ι → ℝ} {cost₁ cost₂ : α → ℕ}
    (h₁ : CostIsBigO l g₁ size cost₁) (h₂ : CostIsBigO l g₂ size cost₂)
    (hg₁ : g₁ =O[l] g) (hg₂ : g₂ =O[l] g) :
    CostIsBigO l g size (fun x ↦ cost₁ x + cost₂ x) :=
  add (h₁.trans_isBigO hg₁) (h₂.trans_isBigO hg₂)

/-- Scaling an operation count by a constant `c : ℕ` preserves `CostIsBigO`. -/
theorem const_mul {g : ι → ℝ} {cost : α → ℕ} (c : ℕ)
    (h : CostIsBigO l g size cost) :
    CostIsBigO l g size (fun x ↦ c * cost x) := by
  obtain ⟨f, hf_mono, hf_nn, hf_O, hb⟩ := h
  refine ⟨fun i ↦ (c : ℝ) * f i, hf_mono.const_mul (Nat.cast_nonneg c),
    fun i ↦ mul_nonneg (Nat.cast_nonneg c) (hf_nn i), hf_O.const_mul_left (c : ℝ), fun x ↦ ?_⟩
  push_cast
  exact mul_le_mul_of_nonneg_left (hb x) (Nat.cast_nonneg c)

/-- Product of two `CostIsBigO` bounds yields a `CostIsBigO` bound for `fun i ↦ g₁ i * g₂ i`. -/
theorem mul {g₁ g₂ : ι → ℝ} {cost₁ cost₂ : α → ℕ}
    (h₁ : CostIsBigO l g₁ size cost₁) (h₂ : CostIsBigO l g₂ size cost₂) :
    CostIsBigO l (fun i ↦ g₁ i * g₂ i) size (fun x ↦ cost₁ x * cost₂ x) := by
  obtain ⟨f₁, hf₁_mono, hf₁_nn, hf₁_O, hb₁⟩ := h₁
  obtain ⟨f₂, hf₂_mono, hf₂_nn, hf₂_O, hb₂⟩ := h₂
  refine ⟨fun i ↦ f₁ i * f₂ i, hf₁_mono.mul hf₂_mono hf₁_nn hf₂_nn,
    fun i ↦ mul_nonneg (hf₁_nn i) (hf₂_nn i), hf₁_O.mul hf₂_O, fun x ↦ ?_⟩
  push_cast
  exact mul_le_mul (hb₁ x) (hb₂ x) (Nat.cast_nonneg _) (hf₁_nn (size x))

end Combinators

section Logarithmic

/-- The binary ceiling logarithm satisfies `Nat.clog 2 n ≤ n` for every `n : ℕ`. -/
theorem clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  exact Nat.lt_two_pow_self.le

/-- For `n ≥ 2`, `(Nat.clog 2 n : ℝ) ≤ (2 / Real.log 2) * Real.log n`. -/
theorem cast_clog_two_le_mul_log {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ (2 / Real.log 2) * Real.log n := by
  set k := Nat.clog 2 n
  have hk_pos : 1 ≤ k := by
    have h2 : Nat.clog 2 2 = 1 := by decide
    rw [← h2]
    exact Nat.clog_mono_right 2 hn
  have hpow_lt : 2 ^ (k - 1) < n := by
    by_contra hge
    push Not at hge
    have hk_le : k ≤ k - 1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hge
    omega
  have hpow_real : ((2 : ℝ) ^ (k - 1)) ≤ (n : ℝ) := by
    exact_mod_cast hpow_lt.le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_pow : ((k - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow_real
  have hlog_two_le : Real.log 2 ≤ Real.log n :=
    Real.log_le_log zero_lt_two (by exact_mod_cast hn)
  have hk_cast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hk_pos
  have hmul : (k : ℝ) * Real.log 2 ≤ 2 * Real.log n := by
    calc
      (k : ℝ) * Real.log 2 = (((k - 1 : ℕ) : ℝ) + 1) * Real.log 2 := by rw [hk_cast]
      _ = ((k - 1 : ℕ) : ℝ) * Real.log 2 + Real.log 2 := by ring
      _ ≤ Real.log n + Real.log n := add_le_add hlog_pow hlog_two_le
      _ = 2 * Real.log n := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
  exact hmul

/-- Any operation count bounded by `a + b * size x + c * (size x * Nat.clog 2 (size x))` satisfies
`Cslib.CostIsBigO atTop (fun n : ℕ ↦ (n : ℝ) * Real.log n) size cost`. -/
theorem of_le_linear_add_mul_clog {α : Type*} {size : α → ℕ} {cost : α → ℕ}
    (a b c : ℕ)
    (h : ∀ x, cost x ≤ a + b * size x + c * (size x * Nat.clog 2 (size x))) :
    CostIsBigO atTop (fun n : ℕ ↦ (n : ℝ) * Real.log n) size cost := by
  refine CostIsBigO.of_le_nat
    (F := fun n ↦ a + b * n + c * (n * Nat.clog 2 n))
    (fun m n hmn ↦ Nat.add_le_add
      (Nat.add_le_add_left (Nat.mul_le_mul_left b hmn) a)
      (Nat.mul_le_mul_left c (Nat.mul_le_mul hmn (Nat.clog_mono_right 2 hmn)))) ?_ h
  refine IsBigO.of_bound (((a : ℝ) + b + 2 * c) / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog_ge : Real.log 2 ≤ Real.log n :=
    Real.log_le_log zero_lt_two (by exact_mod_cast hn)
  have hlogn_nn : 0 ≤ Real.log n := le_trans hlog2_pos.le hlog_ge
  have h1_le : (1 : ℝ) ≤ (1 / Real.log 2) * ((n : ℝ) * Real.log n) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hlog2_pos, one_mul]
    calc
      Real.log 2 ≤ 1 * Real.log n := by linarith
      _ ≤ (n : ℝ) * Real.log n := mul_le_mul_of_nonneg_right hn_ge1 hlogn_nn
  have hn_le : (n : ℝ) ≤ (1 / Real.log 2) * ((n : ℝ) * Real.log n) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hlog2_pos]
    exact mul_le_mul_of_nonneg_left hlog_ge (Nat.cast_nonneg n)
  have hclog_le : (n : ℝ) * (Nat.clog 2 n : ℝ) ≤ (2 / Real.log 2) * ((n : ℝ) * Real.log n) := by
    calc
      (n : ℝ) * (Nat.clog 2 n : ℝ) ≤ (n : ℝ) * ((2 / Real.log 2) * Real.log n) :=
        mul_le_mul_of_nonneg_left (cast_clog_two_le_mul_log hn) (Nat.cast_nonneg n)
      _ = (2 / Real.log 2) * ((n : ℝ) * Real.log n) := by ring
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  push_cast
  have ha := mul_le_mul_of_nonneg_left h1_le (Nat.cast_nonneg a)
  have hb := mul_le_mul_of_nonneg_left hn_le (Nat.cast_nonneg b)
  have hc := mul_le_mul_of_nonneg_left hclog_le (Nat.cast_nonneg c)
  linarith [show (a : ℝ) * (1 / Real.log 2 * ((n : ℝ) * Real.log n)) +
      (b : ℝ) * (1 / Real.log 2 * ((n : ℝ) * Real.log n)) +
      (c : ℝ) * (2 / Real.log 2 * ((n : ℝ) * Real.log n)) =
      ((a : ℝ) + b + 2 * c) / Real.log 2 * ((n : ℝ) * Real.log n) by ring]

/-- Linearithmic growth `n * Real.log n` is dominated by quadratic growth `n ^ 2` as `n → ∞`. -/
theorem isBigO_mul_log_sq :
    (fun n : ℕ ↦ (n : ℝ) * Real.log n) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlog_le : Real.log n ≤ (n : ℝ) := by
    have hsub := Real.log_le_sub_one_of_pos hn_pos
    linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul, sq]
  exact mul_le_mul_of_nonneg_left hlog_le hn_pos.le

end Logarithmic

end CslibFrontier.CostIsBigO
