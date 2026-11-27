/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Asymptotics.CostBound
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.Data.Nat.LogTwoRpow

/-!
# Logarithmic asymptotic cost bounds and halving recurrences

This module extends `CslibFrontier.Foundations.Analysis.Asymptotics.CostBound` with logarithmic
`Cslib.CostIsBigO` rules (`O(log₂ n)`), bit-length / binary-logarithm big-O equivalences, general
halving-recurrence call-count bounds, and the positive-integer-witness characterization of
`Asymptotics.IsBigO` on eventually nonnegative sequences `ℕ → ℝ`.

## Main results

* `Cslib.isBigO_iff_exists_pos_nat`: equivalence between `f =O[atTop] g` and positive-integer
  witnesses `∃ c n₀ : ℕ, 0 < c ∧ 0 < n₀ ∧ ∀ n, n₀ ≤ n → f n ≤ c * g n` for eventually
  nonnegative `f, g : ℕ → ℝ`.
* `Cslib.Nat.size_le_two_mul_logb`, `Cslib.Nat.size_isBigO_logb`, `Cslib.Nat.logb_isBigO_size`,
  `Cslib.Nat.log_isBigO_logb`: asymptotic equivalence between `Nat.size`, `Nat.log 2`, and
  `Real.logb 2`.
* `Cslib.Nat.le_size_of_halving`, `Cslib.Nat.succ_le_size_of_halving`: general halving
  recurrence bounds in terms of `Nat.size`.
* `Cslib.CostIsBigO.of_le_add_mul_size`, `Cslib.CostIsBigO.of_le_add_mul_log`,
  `Cslib.CostIsBigO.of_le_add_mul_clog`, `Cslib.CostIsBigO.of_halving`: logarithmic
  `Cslib.CostIsBigO` constructors matching `Cslib.CostIsBigO.of_le_add_mul`.
-/

public section

open Asymptotics Filter

namespace Cslib

/-- For eventually nonnegative sequences `f, g : ℕ → ℝ`, `f =O[atTop] g` holds iff there exist
positive natural numbers `c` and `n₀` such that `f n ≤ c * g n` for all `n ≥ n₀`. -/
theorem isBigO_iff_exists_pos_nat {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    f =O[atTop] g ↔
      ∃ c n₀ : ℕ, 0 < c ∧ 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → f n ≤ (c : ℝ) * g n := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    rw [eventually_atTop] at hg hC
    obtain ⟨n₁, hn₁⟩ := hg
    obtain ⟨n₂, hn₂⟩ := hC
    let c : ℕ := max ⌈C⌉₊ 1
    let n₀ : ℕ := max (max n₁ n₂) 1
    refine ⟨c, n₀, by omega, by omega, fun n hn ↦ ?_⟩
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hgn : 0 ≤ g n := hn₁ n hn1
    have hbound : ‖f n‖ ≤ C * ‖g n‖ := hn₂ n hn2
    rw [Real.norm_of_nonneg hgn] at hbound
    have hc : C ≤ (c : ℝ) :=
      (Nat.le_ceil C).trans (Nat.cast_le.mpr (le_max_left _ _))
    calc
      f n ≤ ‖f n‖ := le_abs_self (f n)
      _ ≤ C * g n := hbound
      _ ≤ (c : ℝ) * g n := mul_le_mul_of_nonneg_right hc hgn
  · rintro ⟨c, n₀, -, -, hle⟩
    refine IsBigO.of_bound (c : ℝ) ?_
    filter_upwards [hf, hg, eventually_ge_atTop n₀] with n hfn hgn hn
    rw [Real.norm_of_nonneg hfn, Real.norm_of_nonneg hgn]
    exact hle n hn

namespace Nat

private theorem size_eq_log_add_one {n : ℕ} (hn : 0 < n) : n.size = _root_.Nat.log 2 n + 1 := by
  have h1 : 2 ^ _root_.Nat.log 2 n ≤ n := _root_.Nat.pow_log_le_self 2 hn.ne'
  have h2 : n < 2 ^ (_root_.Nat.log 2 n + 1) := _root_.Nat.lt_pow_succ_log_self (by decide) n
  have hle : n.size ≤ _root_.Nat.log 2 n + 1 := _root_.Nat.size_le.mpr h2
  have hge : _root_.Nat.log 2 n + 1 ≤ n.size := _root_.Nat.lt_size.mpr h1
  omega

/-- For `n ≥ 2`, `n.size ≤ 2 * Real.logb 2 n`. -/
theorem size_le_two_mul_logb {n : ℕ} (hn : 2 ≤ n) :
    (n.size : ℝ) ≤ 2 * Real.logb 2 n := by
  have hpos : 0 < n := by omega
  rw [size_eq_log_add_one hpos]
  have hpow : (2 : ℝ) ^ _root_.Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast _root_.Nat.pow_log_le_self 2 hpos.ne'
  have hlog : (_root_.Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hpos)]
    simpa [Real.rpow_natCast] using hpow
  have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hpos)]
    norm_num
    exact_mod_cast hn
  push_cast
  linarith

/-- Binary bit-length `Nat.size` is `O(log₂ n)` along `Filter.atTop`. -/
theorem size_isBigO_logb :
    (fun n : ℕ ↦ (n.size : ℝ)) =O[atTop] fun n ↦ Real.logb 2 n := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_nonneg : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by linarith)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlog_nonneg]
  exact size_le_two_mul_logb hn

/-- Real binary logarithm `Real.logb 2` is `O(Nat.size)` along `Filter.atTop`. -/
theorem logb_isBigO_size :
    (fun n : ℕ ↦ Real.logb 2 n) =O[atTop] fun n ↦ (n.size : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : 0 < n := by omega
  have hlog_nonneg : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hlt : (n : ℝ) < (2 : ℝ) ^ n.size := by
    exact_mod_cast _root_.Nat.lt_size_self n
  have hbound : Real.logb 2 n ≤ (n.size : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
    simpa [Real.rpow_natCast] using hlt.le
  rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact hbound

/-- Integer floor binary logarithm `Nat.log 2` is `O(log₂ n)` along `Filter.atTop`. -/
theorem log_isBigO_logb :
    (fun n : ℕ ↦ (_root_.Nat.log 2 n : ℝ)) =O[atTop] fun n ↦ Real.logb 2 n := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : 0 < n := by omega
  have hlog_nonneg : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hpow : (2 : ℝ) ^ _root_.Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast _root_.Nat.pow_log_le_self 2 hpos.ne'
  have hbound : (_root_.Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hpos)]
    simpa [Real.rpow_natCast] using hpow
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlog_nonneg, one_mul]
  exact hbound

/-- General halving recurrence bound: if `f 0 = 0` and every positive `w` halves to some
`w' ≤ w / 2` with `f w ≤ 1 + f w'`, then `f w ≤ w.size`. -/
theorem le_size_of_halving {f : ℕ → ℕ}
    (hf₀ : f 0 = 0)
    (hf_step : ∀ w : ℕ, 0 < w → ∃ w' ≤ w / 2, f w ≤ 1 + f w') :
    ∀ w : ℕ, f w ≤ w.size := by
  intro w
  induction w using _root_.Nat.strong_induction_on with
  | ind w ih =>
    cases w with
    | zero => simp [hf₀]
    | succ k =>
      obtain ⟨w', hw', hstep⟩ := hf_step (k + 1) (_root_.Nat.succ_pos k)
      have hw'_lt : w' < k + 1 :=
        lt_of_le_of_lt hw' (_root_.Nat.div_lt_self (_root_.Nat.succ_pos k) (by decide))
      have ihw' : f w' ≤ w'.size := ih w' hw'_lt
      have hmono : w'.size ≤ ((k + 1) / 2).size := _root_.Nat.size_le_size hw'
      have hsize_step : ((k + 1) / 2).size + 1 ≤ (k + 1).size := by
        rcases lt_or_ge (k + 1) 2 with hlt | hge
        · have hk : k = 0 := by omega
          subst hk; simp
        · have hdiv_pos : 0 < (k + 1) / 2 := _root_.Nat.div_pos hge (by decide)
          rw [size_eq_log_add_one (_root_.Nat.succ_pos k), size_eq_log_add_one hdiv_pos,
            _root_.Nat.log_of_one_lt_of_le (by decide) hge]
      omega

/-- Early-stopping halving recurrence bound: if every positive `w` either stops (`f w = 0`) or
halves to a positive `w' ≤ w / 2` with `f w ≤ 1 + f w'`, then `f w + 1 ≤ w.size` for `0 < w`. -/
theorem succ_le_size_of_halving {f : ℕ → ℕ}
    (hf_step : ∀ w : ℕ, 0 < w → f w = 0 ∨ ∃ w' : ℕ, 0 < w' ∧ w' ≤ w / 2 ∧ f w ≤ 1 + f w') :
    ∀ w : ℕ, 0 < w → f w + 1 ≤ w.size := by
  intro w hw
  induction w using _root_.Nat.strong_induction_on with
  | ind w ih =>
    rcases hf_step w hw with hzero | ⟨w', hw'_pos, hw'_le, hstep⟩
    · rw [hzero, zero_add]
      exact _root_.Nat.size_pos.mpr hw
    · have hw'_lt : w' < w :=
        lt_of_le_of_lt hw'_le (_root_.Nat.div_lt_self hw (by decide))
      have ihw' : f w' + 1 ≤ w'.size := ih w' hw'_lt hw'_pos
      have hmono : w'.size ≤ (w / 2).size := _root_.Nat.size_le_size hw'_le
      have hge : 2 ≤ w := by omega
      have hdiv_pos : 0 < w / 2 := _root_.Nat.div_pos hge (by decide)
      have hsize_step : (w / 2).size + 1 ≤ w.size := by
        rw [size_eq_log_add_one hw, size_eq_log_add_one hdiv_pos,
          _root_.Nat.log_of_one_lt_of_le (by decide) hge]
      omega

end Nat

namespace CostIsBigO

variable {α : Type*} {size : α → ℕ} {cost : α → ℕ}

/-- A cost at most `a + b * (size x).size` is `O(log₂ (size x))` along `atTop`. -/
theorem of_le_add_mul_size (a b : ℕ) (h : ∀ x, cost x ≤ a + b * (size x).size) :
    CostIsBigO Filter.atTop (fun n : ℕ ↦ Real.logb 2 n) size cost := by
  refine of_le_nat (F := fun n ↦ a + b * n.size)
    (fun _ _ hmn ↦ _root_.Nat.add_le_add_left
      (_root_.Nat.mul_le_mul_left b (_root_.Nat.size_le_size hmn)) a) ?_ h
  have h1 : (fun n : ℕ ↦ ((a + b * n.size : ℕ) : ℝ)) =O[atTop] fun n ↦ (n.size : ℝ) := by
    refine IsBigO.of_bound ((a + b : ℕ) : ℝ) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsize : 1 ≤ n.size := _root_.Nat.size_pos.mpr (by omega)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hnat : a + b * n.size ≤ (a + b) * n.size := by
      rw [_root_.Nat.add_mul]
      exact _root_.Nat.add_le_add_right (_root_.Nat.le_mul_of_pos_right a hsize) _
    exact_mod_cast hnat
  exact h1.trans Nat.size_isBigO_logb

/-- A cost at most `a + b * Nat.log 2 (size x)` is `O(log₂ (size x))` along `atTop`. -/
theorem of_le_add_mul_log (a b : ℕ) (h : ∀ x, cost x ≤ a + b * _root_.Nat.log 2 (size x)) :
    CostIsBigO Filter.atTop (fun n : ℕ ↦ Real.logb 2 n) size cost :=
  of_le_add_mul_size a b fun x ↦ (h x).trans <|
    _root_.Nat.add_le_add_left (_root_.Nat.mul_le_mul_left b <| by
      rcases _root_.Nat.eq_zero_or_pos (size x) with h0 | hpos
      · simp [h0]
      · rw [Nat.size_eq_log_add_one hpos]; omega) a

/-- A cost at most `a + b * Nat.clog 2 (size x)` is `O(log₂ (size x))` along `atTop`. -/
theorem of_le_add_mul_clog (a b : ℕ) (h : ∀ x, cost x ≤ a + b * _root_.Nat.clog 2 (size x)) :
    CostIsBigO Filter.atTop (fun n : ℕ ↦ Real.logb 2 n) size cost := by
  refine of_le_nat (F := fun n ↦ a + b * _root_.Nat.clog 2 n)
    (fun _ _ hmn ↦ _root_.Nat.add_le_add_left
      (_root_.Nat.mul_le_mul_left b (_root_.Nat.clog_mono_right 2 hmn)) a) ?_ h
  refine IsBigO.of_bound ((a + 2 * b : ℕ) : ℝ) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < n))]
    norm_num
    exact_mod_cast hn
  have hclog : (_root_.Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n :=
    _root_.Nat.clog_le_two_mul_logb one_lt_two hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by linarith)]
  push_cast
  nlinarith

/-- Any cost bounded by an affine function of a halving recurrence `f` is `O(log₂ (size x))`. -/
theorem of_halving {f : ℕ → ℕ} (a b : ℕ)
    (hf₀ : f 0 = 0)
    (hf_step : ∀ w : ℕ, 0 < w → ∃ w' ≤ w / 2, f w ≤ 1 + f w')
    (h : ∀ x, cost x ≤ a + b * f (size x)) :
    CostIsBigO Filter.atTop (fun n : ℕ ↦ Real.logb 2 n) size cost :=
  of_le_add_mul_size a b fun x ↦ (h x).trans <|
    _root_.Nat.add_le_add_left (_root_.Nat.mul_le_mul_left b
      (Nat.le_size_of_halving hf₀ hf_step (size x))) a

end CostIsBigO

end Cslib
