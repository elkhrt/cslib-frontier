/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Log

import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Correctness
import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Cost
import CslibFrontier.Algorithms.Lean.Query.Arith.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# FFT-Based Toeplitz Matrix-Vector Multiplication in the Arithmetic Query Model

Reduces multiplication by an `n × n` complex Toeplitz matrix `T_{i,j} = τ(i - j)` to a single
cyclic convolution of length `N = 2 ^ (fftLog n + 1) ≤ 4 * n` executed via `Cslib.Query.fftMul`
in `Cslib.FreeM (ArithQuery ℂ)`.

## Main definitions

* `Cslib.Query.fftLog`: FFT exponent `Nat.log 2 (max 1 n) + 1` with `2 * n ≤ 2^(k+1) ≤ 4 * n`.
* `Cslib.Query.fftRoot`: primitive `2 ^ (k + 1)`-th root of unity `exp(2 π i / 2 ^ (k + 1))`.
* `Cslib.Query.padVec`, `Cslib.Query.padToeplitz`: zero-padded vector and wrap-around kernel.
* `Cslib.Query.toeplitzMulVec`: `FreeM (ArithQuery ℂ)` Toeplitz matrix-vector product.

## Main results

* `Cslib.Query.eval_toeplitzMulVec`: exactness of `toeplitzMulVec` under `ArithQuery.honest`.
* `Cslib.Query.countQueries_toeplitzMulVec_le`: query complexity bound
  `≤ 28 * n * (Nat.log 2 n + 2)` for every `n ≥ 1`.
-/

public section

namespace Cslib.Query

open Cslib Finset

/-- FFT exponent `k = Nat.log 2 (max 1 n) + 1`, so `N = 2 ^ (k + 1)` satisfies
`2 * n ≤ N ≤ 4 * n` for every `n ≥ 1`. -/
def fftLog (n : ℕ) : ℕ :=
  Nat.log 2 (max 1 n) + 1

/-- Lower bound `2 * n ≤ 2 ^ (fftLog n + 1)`. -/
theorem two_mul_le_two_pow_fftLog (n : ℕ) : 2 * n ≤ 2 ^ (fftLog n + 1) := by
  unfold fftLog
  have hlt : max 1 n < 2 ^ (Nat.log 2 (max 1 n) + 1) := Nat.lt_pow_succ_log_self one_lt_two _
  have h1 : n ≤ max 1 n := le_max_right 1 n
  have h2 : 2 ^ (Nat.log 2 (max 1 n) + 1 + 1) = 2 * 2 ^ (Nat.log 2 (max 1 n) + 1) := by
    rw [pow_succ']
  omega

/-- Upper bound `2 ^ (fftLog n + 1) ≤ 4 * n` for `n ≥ 1`. -/
theorem two_pow_fftLog_le_four_mul {n : ℕ} (hn : 1 ≤ n) : 2 ^ (fftLog n + 1) ≤ 4 * n := by
  unfold fftLog
  rw [max_eq_right hn]
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (Nat.log 2 n + 1 + 1) = 4 * 2 ^ Nat.log 2 n := by
    rw [pow_succ', pow_succ']; ring
  omega

/-- Primitive `2 ^ (k + 1)`-th root of unity `exp(2 π i / 2 ^ (k + 1))` in `ℂ`. -/
noncomputable def fftRoot (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / ((2 ^ (k + 1) : ℕ) : ℂ))

/-- `fftRoot k` satisfies `(fftRoot k) ^ (2 ^ k) = -1`. -/
theorem fftRoot_pow_eq_neg_one (k : ℕ) : fftRoot k ^ (2 ^ k) = -1 := by
  unfold fftRoot
  rw [← Complex.exp_nat_mul]
  have harg : ((2 ^ k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / ((2 ^ (k + 1) : ℕ) : ℂ)) =
      Real.pi * Complex.I := by
    have hpow : ((2 ^ (k + 1) : ℕ) : ℂ) = ((2 ^ k : ℕ) : ℂ) * 2 := by
      push_cast [pow_succ]; ring
    have hne : ((2 ^ k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
    rw [hpow]
    field_simp [hne]
  rw [harg, Complex.exp_pi_mul_I]

/-- Zero-padded vector `v` of length `2 ^ (fftLog n + 1)`. -/
def padVec (n : ℕ) (v : Fin n → ℂ) : Fin (2 ^ (fftLog n + 1)) → ℂ :=
  fun r => if h : (r : ℕ) < n then v ⟨r, h⟩ else 0

/-- Wrap-around Toeplitz kernel of length `N = 2 ^ (fftLog n + 1)` encoding `τ(i - j)` for
`i, j < n`. -/
def padToeplitz (n : ℕ) (τ : ℤ → ℂ) : Fin (2 ^ (fftLog n + 1)) → ℂ :=
  fun r =>
    if (r : ℕ) < n then τ (r : ℤ)
    else if 2 ^ (fftLog n + 1) - n < (r : ℕ) then τ ((r : ℤ) - (2 ^ (fftLog n + 1) : ℤ))
    else 0

/-- **FFT-based Toeplitz matrix-vector product** `toeplitzMulVec n τ v` in `FreeM (ArithQuery ℂ)`:
evaluates `i ↦ ∑ j : Fin n, τ(i - j) * v j` in `O(n log n)` arithmetic queries. -/
noncomputable def toeplitzMulVec (n : ℕ) (τ : ℤ → ℂ) (v : Fin n → ℂ) :
    FreeM (ArithQuery ℂ) (Fin n → ℂ) := do
  let c ← fftMul (fftLog n) (fftRoot (fftLog n))
    (((2 ^ (fftLog n + 1) : ℕ) : ℂ)⁻¹) (padVec n v) (padToeplitz n τ)
  return fun i => c ⟨i.1, lt_of_lt_of_le i.2 (by have := two_mul_le_two_pow_fftLog n; omega)⟩

/-- **Exact correctness of `toeplitzMulVec`**: under the honest arithmetic oracle,
`toeplitzMulVec n τ v` computes `∑ j, τ(i - j) * v j` exactly. -/
theorem eval_toeplitzMulVec (n : ℕ) (τ : ℤ → ℂ) (v : Fin n → ℂ) :
    (toeplitzMulVec n τ v).eval ArithQuery.honest =
      fun i : Fin n => ∑ j : Fin n, τ ((i : ℤ) - (j : ℤ)) * v j := by
  have hN : 2 * n ≤ 2 ^ (fftLog n + 1) := two_mul_le_two_pow_fftLog n
  have hnInv : (((2 ^ (fftLog n + 1) : ℕ) : ℂ)⁻¹) * (2 : ℂ) ^ (fftLog n + 1) = 1 := by
    have hne : (2 : ℂ) ^ (fftLog n + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ hne]
  simp only [toeplitzMulVec, FreeM.eval_bind, FreeM.eval_pure]
  rw [eval_fftMul (fftRoot_pow_eq_neg_one (fftLog n)) hnInv]
  funext i
  simp only [Cslib.cyclicConv]
  set N := 2 ^ (fftLog n + 1)
  have hsplit : (∑ r : Fin N, padVec n v r * padToeplitz n τ (⟨i.1, by omega⟩ - r)) =
      ∑ j : Fin n, v j * padToeplitz n τ (⟨i.1, by omega⟩ - ⟨j.1, by omega⟩) := by
    have hfilt : (∑ r : Fin N, padVec n v r * padToeplitz n τ (⟨i.1, by omega⟩ - r)) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin N => (r : ℕ) < n),
          padVec n v r * padToeplitz n τ (⟨i.1, by omega⟩ - r) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin N => (r : ℕ) < n)]
      have hzero : ∑ r ∈ Finset.univ.filter (fun r : Fin N => ¬((r : ℕ) < n)),
          padVec n v r * padToeplitz n τ (⟨i.1, by omega⟩ - r) = 0 := by
        refine Finset.sum_eq_zero fun r hr => ?_
        have hnr : ¬((r : ℕ) < n) := (Finset.mem_filter.mp hr).2
        simp [padVec, hnr]
      rw [hzero, add_zero]
    rw [hfilt]
    refine Finset.sum_bij (fun r hr => ⟨r.1, (Finset.mem_filter.mp hr).2⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun r₁ _ r₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun j _ => ⟨⟨j.1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩, rfl⟩)
      (fun r hr => by simp [padVec, (Finset.mem_filter.mp hr).2])
  rw [hsplit]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 1
  simp only [padToeplitz]
  have hsub_val : ((⟨i.1, by omega⟩ - ⟨j.1, by omega⟩ : Fin N) : ℕ) =
      if j.1 ≤ i.1 then i.1 - j.1 else N + i.1 - j.1 := by
    simp only [Fin.val_sub]
    split_ifs with hji
    · have heq : N - j.1 + i.1 = N + (i.1 - j.1) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hsub_val]
  have hN_eq : 2 ^ (fftLog n + 1) = N := rfl
  simp only [hN_eq]
  have hi : i.1 < n := i.2
  have hj : j.1 < n := j.2
  by_cases hji : j.1 ≤ i.1
  · simp only [hji, ↓reduceIte, show i.1 - j.1 < n by omega]
    congr 1; omega
  · simp only [hji, ↓reduceIte, show ¬(N + i.1 - j.1 < n) by omega,
      show N - n < N + i.1 - j.1 by omega]
    congr 1
    have hZ : (2 : ℤ) ^ (fftLog n + 1) = (N : ℤ) := by push_cast [N]; rfl
    rw [hZ]
    omega

/-- **Query complexity of `toeplitzMulVec`**: at most `28 * n * (Nat.log 2 n + 2)` queries
for every `n ≥ 1`. -/
theorem countQueries_toeplitzMulVec_le {n : ℕ} (hn : 1 ≤ n)
    (oracle : {ι : Type} → ArithQuery ℂ ι → ι) (τ : ℤ → ℂ) (v : Fin n → ℂ) :
    (toeplitzMulVec n τ v).countQueries oracle ≤ 28 * n * (Nat.log 2 n + 2) := by
  rw [ArithQuery.countQueries_eq_cost_weight_one]
  simp only [toeplitzMulVec, FreeM.cost_bind, FreeM.cost_pure, add_zero,
    ← ArithQuery.countQueries_eq_cost_weight_one]
  have hfft := countQueries_fftMul_le oracle (fftLog n) (fftRoot (fftLog n))
    (((2 ^ (fftLog n + 1) : ℕ) : ℂ)⁻¹) (padVec n v) (padToeplitz n τ)
  have hNle : 2 ^ (fftLog n + 1) ≤ 4 * n := two_pow_fftLog_le_four_mul hn
  have hlog : Nat.log 2 (2 ^ (fftLog n + 1)) = Nat.log 2 n + 2 := by
    rw [Nat.log_pow one_lt_two, fftLog, max_eq_right hn]
  rw [hlog] at hfft
  calc _ ≤ 7 * 2 ^ (fftLog n + 1) * (Nat.log 2 n + 2) := hfft
    _ ≤ 7 * (4 * n) * (Nat.log 2 n + 2) := by gcongr
    _ = 28 * n * (Nat.log 2 n + 2) := by ring

end Cslib.Query
