/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Correctness
public import CslibFrontier.Algorithms.Lean.Query.Arith.FFT.Cost
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear Integer and Boolean Vector Convolution via FFT in the Arithmetic Query Model

Fischer and Paterson reduce `n`-dimensional linear integer arithmetic convolution
`(p ⋆ q)_k = ∑_{l + m = k} p_l q_m` (`0 ≤ k < 2n - 1`) and Boolean vector convolution
`c_k = ⋁_{l + m = k} (a_l ∧ b_m)` to cyclic polynomial multiplication of length
`N = 2 ^ (k + 1) ≥ 2n - 1` (`N ≤ 4n`) over `ℂ` via `Cslib.Query.fftMul`.

## Main definitions

* `CslibFrontier.Query.intArithConv`: linear arithmetic convolution of `p, q : Fin n → ℤ`.
* `CslibFrontier.Query.boolConv`: linear Boolean vector convolution of `a, b : Fin n → Bool`.
* `CslibFrontier.Query.arithConvViaFFT`: `FreeM (ArithQuery ℂ)` algorithm computing `intArithConv`.
* `CslibFrontier.Query.boolConvViaFFT`: `FreeM (ArithQuery ℂ)` algorithm computing `boolConv`.

## Main results

* `CslibFrontier.Query.eval_arithConvViaFFT`, `CslibFrontier.Query.countQueries_arithConvViaFFT_le`:
  exactness and `28 * n * (Nat.log 2 n + 2)` query bound for integer arithmetic convolution.
* `CslibFrontier.Query.eval_boolConvViaFFT`, `CslibFrontier.Query.countQueries_boolConvViaFFT_le`:
  exactness and `28 * n * (Nat.log 2 n + 2)` query bound for Boolean vector convolution.
-/

public section

namespace CslibFrontier.Query

open Cslib Cslib.FreeM Cslib.Query

/-- Valid index set `{l : Fin n | l ≤ k ∧ k - l < n}` for coordinate `k` of `n`-dimensional
linear convolution. -/
def convIndexSet (n : ℕ) (k : Fin (2 * n - 1)) : Finset (Fin n) :=
  Finset.univ.filter fun l : Fin n => l.1 ≤ k.1 ∧ k.1 - l.1 < n

theorem mem_convIndexSet_iff {n : ℕ} {k : Fin (2 * n - 1)} {l : Fin n} :
    l ∈ convIndexSet n k ↔ l.1 ≤ k.1 ∧ k.1 - l.1 < n := by
  simp [convIndexSet]

/-- Mate index `k - l : Fin n` for `l ∈ convIndexSet n k`. -/
def convMate {n : ℕ} {k : Fin (2 * n - 1)} {l : Fin n} (hl : l ∈ convIndexSet n k) : Fin n :=
  ⟨k.1 - l.1, (mem_convIndexSet_iff.mp hl).2⟩

/-- Linear arithmetic convolution of two `n`-dimensional integer vectors. -/
def intArithConv {n : ℕ} (p q : Fin n → ℤ) (k : Fin (2 * n - 1)) : ℤ :=
  ∑ l : Fin n, if h : l.1 ≤ k.1 ∧ k.1 - l.1 < n then p l * q ⟨k.1 - l.1, h.2⟩ else 0

/-- Linear Boolean vector convolution of two `n`-dimensional Boolean vectors. -/
def boolConv {n : ℕ} (a b : Fin n → Bool) (k : Fin (2 * n - 1)) : Bool :=
  decide (∃ (l : Fin n) (hl : l ∈ convIndexSet n k), a l = true ∧ b (convMate hl) = true)

theorem boolConv_eq_true_iff {n : ℕ} (a b : Fin n → Bool) (k : Fin (2 * n - 1)) :
    boolConv a b k = true ↔
      ∃ (l : Fin n) (hl : l ∈ convIndexSet n k), a l = true ∧ b (convMate hl) = true := by
  simp [boolConv]

/-- Exponent `k` such that `2 * n - 1 ≤ 2 ^ (k + 1) ≤ 4 * n` for `0 < n`. -/
def fftConvExp (n : ℕ) : ℕ :=
  Nat.clog 2 (2 * n - 1) - 1

theorem two_pow_fftConvExp_ge {n : ℕ} (hn : 0 < n) : 2 * n - 1 ≤ 2 ^ (fftConvExp n + 1) := by
  dsimp only [fftConvExp]
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · simp
  · have hclog : 1 ≤ Nat.clog 2 (2 * n - 1) := Nat.clog_pos one_lt_two (by omega)
    rw [Nat.sub_add_cancel hclog]
    exact Nat.le_pow_clog one_lt_two _

theorem two_pow_fftConvExp_le {n : ℕ} (hn : 0 < n) : 2 ^ (fftConvExp n + 1) ≤ 4 * n := by
  dsimp only [fftConvExp]
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · simp
  · have hclog : 1 ≤ Nat.clog 2 (2 * n - 1) := Nat.clog_pos one_lt_two (by omega)
    rw [Nat.sub_add_cancel hclog]
    have hlt : 2 ^ (Nat.clog 2 (2 * n - 1) - 1) < 2 * n - 1 := by
      by_contra hge
      push Not at hge
      have hle := Nat.clog_le_of_le_pow hge
      omega
    have hmul : 2 ^ Nat.clog 2 (2 * n - 1) = 2 * 2 ^ (Nat.clog 2 (2 * n - 1) - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hclog, pow_succ']
    omega

/-- Principal complex root of unity `ω = exp(π i / 2 ^ k)` satisfying `ω ^ (2 ^ k) = -1`. -/
noncomputable def complexRootPowTwo (k : ℕ) : ℂ :=
  Complex.exp (Real.pi * Complex.I / (2 ^ k : ℂ))

theorem complexRootPowTwo_pow_eq_neg_one (k : ℕ) :
    (complexRootPowTwo k) ^ (2 ^ k) = -1 := by
  rw [complexRootPowTwo, ← Complex.exp_nat_mul]
  have hne : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  have hmul : ((2 ^ k : ℕ) : ℂ) * (Real.pi * Complex.I / (2 ^ k : ℂ)) = Real.pi * Complex.I := by
    push_cast
    exact mul_div_cancel₀ _ hne
  rw [hmul, Complex.exp_pi_mul_I]

/-- Zero-pad `p : Fin n → ℤ` to a complex vector of length `2 ^ (k + 1)`. -/
def padIntToComplex {n : ℕ} (k : ℕ) (p : Fin n → ℤ) : Fin (2 ^ (k + 1)) → ℂ :=
  fun i => if h : i.1 < n then (p ⟨i.1, h⟩ : ℂ) else 0

private theorem fin_sub_val {N : ℕ} [NeZero N] (a b : Fin N) :
    (a - b).1 = if b.1 ≤ a.1 then a.1 - b.1 else N + a.1 - b.1 := by
  have hadd : ((a - b).1 + b.1) % N = a.1 := by
    have h := congrArg Fin.val (sub_add_cancel a b)
    rw [Fin.val_add] at h
    exact h
  have ha : a.1 < N := a.2
  have hb : b.1 < N := b.2
  have hab : (a - b).1 < N := (a - b).2
  by_cases hsum : (a - b).1 + b.1 < N
  · rw [Nat.mod_eq_of_lt hsum] at hadd
    split_ifs <;> omega
  · have hlt2 : (a - b).1 + b.1 - N < N := by omega
    rw [Nat.mod_eq_sub_mod (not_lt.mp hsum), Nat.mod_eq_of_lt hlt2] at hadd
    split_ifs <;> omega

/-- Linear arithmetic convolution of `n`-dimensional integer vectors via `Cslib.Query.fftMul`. -/
noncomputable def arithConvViaFFT (n : ℕ) (p q : Fin n → ℤ) :
    FreeM (ArithQuery ℂ) (Fin (2 * n - 1) → ℂ) := do
  let k := fftConvExp n
  let res ← fftMul k (complexRootPowTwo k) ((2 ^ (k + 1) : ℂ)⁻¹)
    (padIntToComplex k p) (padIntToComplex k q)
  pure fun i => if h : i.1 < 2 ^ (k + 1) then res ⟨i.1, h⟩ else 0

/-- `arithConvViaFFT` computes `intArithConv` under `ArithQuery.honest`. -/
theorem eval_arithConvViaFFT {n : ℕ} (p q : Fin n → ℤ) (i : Fin (2 * n - 1)) :
    (arithConvViaFFT n p q).eval ArithQuery.honest i = (intArithConv p q i : ℂ) := by
  classical
  have hn : 0 < n := by have := i.2; omega
  have hi : i.1 < 2 ^ (fftConvExp n + 1) := lt_of_lt_of_le i.2 (two_pow_fftConvExp_ge hn)
  have hinv : ((2 ^ (fftConvExp n + 1) : ℂ)⁻¹) * (2 ^ (fftConvExp n + 1) : ℂ) = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  simp only [arithConvViaFFT, FreeM.eval_bind, FreeM.eval_pure,
    eval_fftMul (complexRootPowTwo_pow_eq_neg_one (fftConvExp n)) hinv, hi, ↓reduceDIte]
  set N := 2 ^ (fftConvExp n + 1)
  have hN : 2 * n - 1 ≤ N := two_pow_fftConvExp_ge hn
  simp only [cyclicConv]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun j : Fin N => j.1 < n)]
  have htail : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬j.1 < n),
      padIntToComplex (fftConvExp n) p j *
        padIntToComplex (fftConvExp n) q (⟨i.1, hi⟩ - j) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hnot := (Finset.mem_filter.mp hj).2
      simp [padIntToComplex, hnot]
  rw [htail, add_zero]
  have hre : ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.1 < n),
      padIntToComplex (fftConvExp n) p j *
        padIntToComplex (fftConvExp n) q (⟨i.1, hi⟩ - j) =
      ∑ l : Fin n,
        (if h : l.1 ≤ i.1 ∧ i.1 - l.1 < n then (p l : ℂ) * (q ⟨i.1 - l.1, h.2⟩ : ℂ) else 0) := by
    refine Finset.sum_bij (fun j hj => ⟨j.1, (Finset.mem_filter.mp hj).2⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun j₁ _ j₂ _ h => Fin.ext (Fin.mk.inj h))
      (fun l _ => ⟨⟨l.1, lt_of_lt_of_le l.2 (by omega)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.2⟩, rfl⟩)
      (fun j hj => ?_)
    have hlt : j.1 < n := (Finset.mem_filter.mp hj).2
    let l : Fin n := ⟨j.1, hlt⟩
    change padIntToComplex (fftConvExp n) p j *
        padIntToComplex (fftConvExp n) q (⟨i.1, hi⟩ - j) =
      if h : l.1 ≤ i.1 ∧ i.1 - l.1 < n then (p l : ℂ) * (q ⟨i.1 - l.1, h.2⟩ : ℂ) else 0
    by_cases hle : j.1 ≤ i.1
    · have hsub_val : ((⟨i.1, hi⟩ - j : Fin N) : ℕ) = i.1 - j.1 := by
        rw [fin_sub_val]; simp [hle]
      by_cases hlt2 : i.1 - j.1 < n
      · simp [padIntToComplex, hlt, l, hle, hsub_val, hlt2]
      · simp [padIntToComplex, hlt, l, hle, hsub_val, hlt2]
    · have hsub_val : ((⟨i.1, hi⟩ - j : Fin N) : ℕ) = N + i.1 - j.1 := by
        rw [fin_sub_val]; simp [hle]
      have hge : ¬(N + i.1 - j.1 < n) := by omega
      simp [padIntToComplex, hlt, l, hle, hsub_val, hge]
  rw [hre, intArithConv, Int.cast_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/-- `arithConvViaFFT` makes at most `28 * n * (Nat.log 2 n + 2)` arithmetic queries. -/
theorem countQueries_arithConvViaFFT_le (oracle : {ι : Type} → ArithQuery ℂ ι → ι)
    {n : ℕ} (hn : 0 < n) (p q : Fin n → ℤ) :
    (arithConvViaFFT n p q).countQueries oracle ≤ 28 * n * (Nat.log 2 n + 2) := by
  simp only [arithConvViaFFT, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
  have h1 := countQueries_fftMul_le oracle (fftConvExp n)
    (complexRootPowTwo (fftConvExp n)) ((2 ^ (fftConvExp n + 1) : ℂ)⁻¹)
    (padIntToComplex (fftConvExp n) p) (padIntToComplex (fftConvExp n) q)
  have hN : 2 ^ (fftConvExp n + 1) ≤ 4 * n := two_pow_fftConvExp_le hn
  have hlog : Nat.log 2 (2 ^ (fftConvExp n + 1)) ≤ Nat.log 2 n + 2 := by
    calc Nat.log 2 (2 ^ (fftConvExp n + 1)) ≤ Nat.log 2 (4 * n) := Nat.log_mono_right hN
      _ = Nat.log 2 (n * 2 * 2) := by ring_nf
      _ = Nat.log 2 n + 2 := by
        rw [Nat.log_mul_base one_lt_two (by omega), Nat.log_mul_base one_lt_two hn.ne']
  calc (fftMul (fftConvExp n) _ _ _ _).countQueries oracle
      ≤ 7 * 2 ^ (fftConvExp n + 1) * Nat.log 2 (2 ^ (fftConvExp n + 1)) := h1
    _ ≤ 7 * (4 * n) * (Nat.log 2 n + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 7 hN) hlog
    _ = 28 * n * (Nat.log 2 n + 2) := by ring

/-- Linear Boolean vector convolution reduced to `arithConvViaFFT` on `{0, 1}` vectors. -/
noncomputable def boolConvViaFFT (n : ℕ) (a b : Fin n → Bool) :
    FreeM (ArithQuery ℂ) (Fin (2 * n - 1) → Bool) := do
  let res ← arithConvViaFFT n (fun l => if a l then 1 else 0) (fun l => if b l then 1 else 0)
  pure fun i => decide (res i ≠ 0)

/-- `boolConvViaFFT` computes `boolConv` under `ArithQuery.honest`. -/
theorem eval_boolConvViaFFT {n : ℕ} (a b : Fin n → Bool) :
    (boolConvViaFFT n a b).eval ArithQuery.honest = boolConv a b := by
  classical
  funext i
  simp only [boolConvViaFFT, FreeM.eval_bind, FreeM.eval_pure]
  rw [eval_arithConvViaFFT]
  have hsum : intArithConv (fun l => if a l then (1 : ℤ) else 0)
      (fun l => if b l then (1 : ℤ) else 0) i =
      ((Finset.univ.filter fun l : Fin n =>
        ∃ hl : l ∈ convIndexSet n i, a l = true ∧ b (convMate hl) = true).card : ℤ) := by
    rw [intArithConv, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.1 ≤ i.1 ∧ i.1 - l.1 < n
    · have hmem : l ∈ convIndexSet n i := mem_convIndexSet_iff.mpr hl
      have hbeq : b ⟨i.1 - l.1, hl.2⟩ = b (convMate hmem) := rfl
      by_cases hal : a l = true
      · by_cases hbl : b (convMate hmem) = true
        · simp [hl, hbeq, hal, hbl, hmem]
        · have hbf : b (convMate hmem) = false := Bool.eq_false_iff.mpr hbl
          simp [hl, hbeq, hal, hbf]
      · have haf : a l = false := Bool.eq_false_iff.mpr hal
        simp [hl, haf]
    · have hnot : l ∉ convIndexSet n i := fun hm => hl (mem_convIndexSet_iff.mp hm)
      simp [hl, hnot]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, hsum, Int.cast_natCast, Nat.cast_ne_zero,
    Finset.card_ne_zero, Finset.filter_nonempty_iff, boolConv_eq_true_iff]
  simp only [Finset.mem_univ, true_and]

/-- `boolConvViaFFT` makes at most `28 * n * (Nat.log 2 n + 2)` arithmetic queries. -/
theorem countQueries_boolConvViaFFT_le (oracle : {ι : Type} → ArithQuery ℂ ι → ι)
    {n : ℕ} (hn : 0 < n) (a b : Fin n → Bool) :
    (boolConvViaFFT n a b).countQueries oracle ≤ 28 * n * (Nat.log 2 n + 2) := by
  simp only [boolConvViaFFT, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
  exact countQueries_arithConvViaFFT_le oracle hn _ _

end CslibFrontier.Query
