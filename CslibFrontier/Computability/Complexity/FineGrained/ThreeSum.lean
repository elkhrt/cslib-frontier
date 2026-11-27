/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.ConvThreeSum
import CslibFrontier.Computability.Complexity.FineGrained.ChanHeWorklist
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equivalence of the 3SUM and Convolution-3SUM Hypotheses

This module completes the deterministic multi-tape Turing machine reduction from positive-integer
three-set `3SUM` to `Convolution-3SUM` via Chan and He's bounded-worklist prime-modulus
residue-hashing traversal, establishing `ThreeSumHypothesis ↔ ConvThreeSumHypothesis`
under standard Lean axioms.

## Main results

* `CslibFrontier.Complexity.convThreeSumHypothesis_of_threeSumHypothesis`:
  if `ConvThreeSum` admits an `O(n ^ (2 - ε) * (log M) ^ e)` deterministic multi-tape Turing
  machine for some `ε > 0` and `e : ℕ`, then `ThreeSum` admits an
  `O(N ^ (2 - ε') * (log M) ^ E)` deterministic multi-tape Turing machine for some `ε' > 0` and
  `E : ℕ`; hence `ThreeSumHypothesis → ConvThreeSumHypothesis`.
* `CslibFrontier.Complexity.threeSumHypothesis_iff_convThreeSumHypothesis`:
  `ThreeSumHypothesis ↔ ConvThreeSumHypothesis`.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Complexity
open Cslib.Algorithms.ThreeSum.ChanHe

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

attribute [local irreducible] encNat encIntBin encUnary

private theorem chanHeValidRoundAndState_le (cConv Cidle e ds Dmax : ℕ) (ε₁ : ℝ)
    (hds_le : ds ≤ Dmax) {p : ThreeSumInput} (hvT : validThreeSumBool p = true)
    (hn1 : 1 ≤ p.1.length)
    (hm_le : mPar p.1.length (threeSumMaxVal p) + 1 ≤
      513 * Nat.sqrt p.1.length * (threeSumSize p).size.succ * threeSumBitScale p ^ 2)
    (hm2_le : (mPar p.1.length (threeSumMaxVal p) + 1) ^ 2 ≤
      513 ^ 2 * p.1.length * (threeSumSize p).size.succ ^ 2 * threeSumBitScale p ^ 4)
    (hsc_all : 32 * (p.1.length.size + (threeSumMaxVal p).size +
      (mPar p.1.length (threeSumMaxVal p) + 1).size + 16) ≤
      1024 * (threeSumSize p).size.succ * threeSumBitScale p) :
    (chanHeValidRoundBnd cConv ε₁ e ds p + Cidle) + (chanHeValidStateBnd p + 16) ≤
      chanHeConvCap cConv ε₁ e p.1.length (threeSumMaxVal p) + (Cidle + 16) +
        2 ^ 28 * 1024 ^ Dmax * (p.1.length * Nat.sqrt p.1.length) *
          (threeSumSize p).size.succ ^ (Dmax + 3) * threeSumBitScale p ^ (Dmax + 4) := by
  let n := p.1.length
  let U := threeSumMaxVal p
  let m := mPar n U
  let L := (threeSumSize p).size.succ
  let B := threeSumBitScale p
  have hLpos : 1 ≤ L := Nat.succ_pos _
  have hB1 : 1 ≤ B := threeSumBitScale_pos p
  let sc0 := 32 * (n.size + U.size + (m + 1).size + 16)
  have hsc_ds : sc0 ^ ds ≤ 1024 ^ Dmax * L ^ Dmax * B ^ Dmax :=
    (Nat.pow_le_pow_left hsc_all ds).trans (by
      simp only [Nat.mul_pow]
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hds_le)
        (Nat.pow_le_pow_right hLpos hds_le)) (Nat.pow_le_pow_right hB1 hds_le))
  let K1 : ℕ := (n * Nat.sqrt n) * L ^ 2 * B ^ 4
  have hsq1 : n ≤ n * Nat.sqrt n := Nat.le_mul_of_pos_right n (Nat.sqrt_pos.mpr hn1)
  have hK1_pos : 1 ≤ K1 := Nat.mul_pos
    (Nat.mul_pos (hn1.trans hsq1) (Nat.pow_pos hLpos)) (Nat.pow_pos hB1)
  have hn_le_K1 : n ≤ K1 :=
    (hsq1.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.pow_pos hLpos) (Nat.pow_pos hB1)))
      ).trans_eq (Nat.mul_assoc _ _ _).symm
  have hm2_K1 : (m + 1) ^ 2 ≤ 513 ^ 2 * K1 :=
    hm2_le.trans (calc 513 ^ 2 * n * L ^ 2 * B ^ 4 = n * (513 ^ 2 * L ^ 2 * B ^ 4) := by ring
      _ ≤ (n * Nat.sqrt n) * (513 ^ 2 * L ^ 2 * B ^ 4) := Nat.mul_le_mul_right _ hsq1
      _ = 513 ^ 2 * K1 := by dsimp only [K1]; ring)
  have hvs : chanHeValidStateBnd p ≤ 2 ^ 26 * (n * Nat.sqrt n) * L ^ 3 * B ^ 3 :=
    chanHeValidStateBnd_le hvT (by
      have hnsz : n.size ≤ (threeSumSize p).size := by
        obtain ⟨_, hN_eq⟩ := validThreeSumBool_lengths hvT
        exact Nat.size_le_size (by omega)
      have hf : fuel n + 1 ≤ 6 * L := by
        obtain ⟨_, hN_eq⟩ := validThreeSumBool_lengths hvT
        have ho : 1 ≤ (threeSumSize p).size := Nat.size_pos.mpr (by omega)
        have hfl := fuel_le_size n
        have hL_eq : L = (threeSumSize p).size + 1 := rfl
        omega
      have hnm : n + m + 1 ≤ 514 * (n * Nat.sqrt n) * L * B ^ 2 := by
        have h1 : n ≤ (n * Nat.sqrt n) * (L * B ^ 2) :=
          hsq1.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos hLpos (Nat.pow_pos hB1)))
        have h2 : m + 1 ≤ 513 * ((n * Nat.sqrt n) * (L * B ^ 2)) :=
          hm_le.trans ((show 513 * Nat.sqrt n * L * B ^ 2 =
            Nat.sqrt n * (513 * L * B ^ 2) by ring).trans_le
            ((Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hn1)).trans_eq (by ring)))
        exact ((Nat.add_assoc n m 1).trans_le (Nat.add_le_add h1 h2)).trans_eq (by ring)
      have hsc0 : n.size + U.size + (m + 1).size + 16 ≤ 32 * L * B :=
        Nat.le_of_mul_le_mul_left
          (hsc_all.trans_eq (show 1024 * L * B = 32 * (32 * L * B) by ring)) (by norm_num)
      calc _ ≤ 400 * (6 * L) * (514 * (n * Nat.sqrt n) * L * B ^ 2) * (32 * L * B) :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 400 hf) hnm) hsc0
        _ = (400 * 6 * 514 * 32) * ((n * Nat.sqrt n) * L ^ 3 * B ^ 3) := by ring
        _ ≤ 2 ^ 26 * ((n * Nat.sqrt n) * L ^ 3 * B ^ 3) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ 26 * (n * Nat.sqrt n) * L ^ 3 * B ^ 3 := by ring)
  have hmod_b : (m + 2) * (m + 3 * n + 2) ≤ 2 ^ 21 * K1 := by
    have h1 : (m + 2) * (m + 3 * n + 2) ≤ 4 * (m + 1) ^ 2 + 6 * (n * (m + 1)) :=
      calc (m + 2) * (m + 3 * n + 2)
          = (m + 1) ^ 2 + 2 * (m + 1) + 1 + 3 * (n * (m + 1)) + 3 * n := by ring
        _ ≤ (m + 1) ^ 2 + 2 * (m + 1) ^ 2 + (m + 1) ^ 2 +
              3 * (n * (m + 1)) + 3 * (n * (m + 1)) :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl
              (Nat.mul_le_mul_left 2 (Nat.le_self_pow (by norm_num) _)))
              (Nat.one_le_pow 2 _ (Nat.succ_pos m))) le_rfl)
              (Nat.mul_le_mul_left 3 (Nat.le_mul_of_pos_right n (Nat.succ_pos m)))
        _ = 4 * (m + 1) ^ 2 + 6 * (n * (m + 1)) := by ring
    have h2 : n * (m + 1) ≤ 513 * K1 :=
      calc n * (m + 1) ≤ n * (513 * Nat.sqrt n * L * B ^ 2) := Nat.mul_le_mul_left n hm_le
        _ = 513 * (n * Nat.sqrt n) * (L * B ^ 2) := by ring
        _ ≤ 513 * (n * Nat.sqrt n) * (L ^ 2 * B ^ 4) := Nat.mul_le_mul_left _
            (Nat.mul_le_mul (Nat.le_self_pow (by norm_num) L)
              (Nat.pow_le_pow_right hB1 (by norm_num)))
        _ = 513 * K1 := by dsimp only [K1]; ring
    exact (h1.trans (Nat.add_le_add (Nat.mul_le_mul_left 4 hm2_K1)
      (Nat.mul_le_mul_left 6 h2))).trans
      ((show 4 * (513 ^ 2 * K1) + 6 * (513 * K1) = (4 * 513 ^ 2 + 6 * 513) * K1 by ring).trans_le
        (Nat.mul_le_mul_right K1 (by norm_num)))
  have hpk_b : (2 * m ^ 2 + 3 * n + 1) + 4 * (n + 1) ≤ 2 ^ 21 * K1 := by
    have h1 : m ^ 2 ≤ 513 ^ 2 * K1 := (Nat.pow_le_pow_left (Nat.le_succ m) 2).trans hm2_K1
    have h2 : 3 * n + 1 + 4 * (n + 1) ≤ 12 * K1 :=
      ((show 3 * n + 1 + 4 * (n + 1) = 7 * n + 5 by ring).trans_le
        (Nat.add_le_add (Nat.mul_le_mul_left 7 hn_le_K1) (Nat.mul_le_mul_left 5 hK1_pos))).trans_eq
        (by ring)
    exact ((show (2 * m ^ 2 + 3 * n + 1) + 4 * (n + 1) =
        2 * m ^ 2 + (3 * n + 1 + 4 * (n + 1)) by ring).trans_le
      (Nat.add_le_add (Nat.mul_le_mul_left 2 h1) h2)).trans
      ((show 2 * (513 ^ 2 * K1) + 12 * K1 = (2 * 513 ^ 2 + 12) * K1 by ring).trans_le
        (Nat.mul_le_mul_right K1 (by norm_num)))
  let K2 : ℕ := 1024 ^ Dmax * (n * Nat.sqrt n) * L ^ (Dmax + 3) * B ^ (Dmax + 4)
  have hK12 : K1 * (1024 ^ Dmax * L ^ Dmax * B ^ Dmax) ≤ K2 :=
    ((show K1 * (1024 ^ Dmax * L ^ Dmax * B ^ Dmax) =
      (1024 ^ Dmax * (n * Nat.sqrt n) * B ^ (Dmax + 4)) * L ^ (Dmax + 2) by
        dsimp only [K1]; ring).trans_le
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hLpos (by omega : Dmax + 2 ≤ Dmax + 3)))
      ).trans_eq (by dsimp only [K2]; ring)
  have hm1 : (m + 2) * (m + 3 * n + 2) * sc0 ^ ds ≤ 2 ^ 21 * K2 :=
    (Nat.mul_le_mul hmod_b hsc_ds).trans
      ((Nat.mul_assoc (2 ^ 21) K1 _).trans_le (Nat.mul_le_mul_left _ hK12))
  have hm2 : (2 * m ^ 2 + 3 * n + 1) * sc0 ^ ds + 4 * (n + 1) * sc0 ^ ds ≤ 2 ^ 21 * K2 := by
    rw [← Nat.add_mul]
    exact (Nat.mul_le_mul hpk_b hsc_ds).trans
      ((Nat.mul_assoc (2 ^ 21) K1 _).trans_le (Nat.mul_le_mul_left _ hK12))
  have hvs' : chanHeValidStateBnd p ≤ 2 ^ 26 * K2 :=
    hvs.trans (by
      have hmul : 1 * L ^ 3 * B ^ 3 ≤ 1024 ^ Dmax * L ^ (Dmax + 3) * B ^ (Dmax + 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow Dmax 1024 (by norm_num))
          (Nat.pow_le_pow_right hLpos (by omega))) (Nat.pow_le_pow_right hB1 (by omega))
      exact ((show 2 ^ 26 * (n * Nat.sqrt n) * L ^ 3 * B ^ 3 =
        (2 ^ 26 * (n * Nat.sqrt n)) * (1 * L ^ 3 * B ^ 3) by ring).trans_le
        (Nat.mul_le_mul_left _ hmul)).trans_eq (by dsimp only [K2]; ring))
  rw [chanHeValidRoundBnd_of_valid cConv ε₁ e ds hvT]
  simp only []
  have hsum : (m + 2) * (m + 3 * n + 2) * sc0 ^ ds +
      ((2 * m ^ 2 + 3 * n + 1) * sc0 ^ ds + 4 * (n + 1) * sc0 ^ ds) +
      (chanHeValidStateBnd p + chanHeValidStateBnd p) ≤ 2 ^ 28 * K2 :=
    (Nat.add_le_add (Nat.add_le_add hm1 hm2) (Nat.add_le_add hvs' hvs')).trans
      ((show 2 ^ 21 * K2 + 2 ^ 21 * K2 + (2 ^ 26 * K2 + 2 ^ 26 * K2) =
        (2 ^ 21 + 2 ^ 21 + 2 * 2 ^ 26) * K2 by ring).trans_le
        (Nat.mul_le_mul_right K2 (by norm_num)))
  have hK2_eq : 2 ^ 28 * K2 = 2 ^ 28 * 1024 ^ Dmax * (p.1.length * Nat.sqrt p.1.length) *
      (threeSumSize p).size.succ ^ (Dmax + 3) * threeSumBitScale p ^ (Dmax + 4) := by
    dsimp only [K2, n, L, B]; ring
  rw [← hK2_eq]
  dsimp only [sc0, n, U, m] at hsum
  omega

private theorem chanHe_coef_combine (cConv Cidle Dmax e : ℕ) :
    3 * (2 ^ 12 : ℝ) ^ (Dmax + 1) + 2 * (2 ^ 20 : ℝ) ^ (Dmax + 1) +
      ((cConv + 1 : ℝ) * (2 ^ 26 : ℝ) ^ (e + 2) + (Cidle + 16 : ℝ) * 65 +
        65 * 2 ^ 28 * (1024 : ℝ) ^ Dmax) + 2 ^ 17 ≤
      (cConv + Cidle + 1 : ℝ) * (2 ^ 30 : ℝ) ^ (Dmax + e + 4) := by
  let M28 : ℝ := (2 ^ 28 : ℝ) ^ (Dmax + e + 3)
  have p1 : (2 ^ 26 : ℝ) ^ (e + 2) * 2 ^ 28 ≤ M28 :=
    ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by norm_num)
      ).trans_eq (pow_succ (2 ^ 28 : ℝ) (e + 2)).symm).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have p2 : (1024 : ℝ) ^ Dmax * (2 ^ 28) ^ 3 ≤ M28 :=
    ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by norm_num)
      ).trans_eq (pow_add (2 ^ 28 : ℝ) Dmax 3).symm).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have p3 : (1 : ℝ) ≤ (2 ^ 26 : ℝ) ^ (e + 2) := one_le_pow₀ (by norm_num)
  have p5 : (65 : ℝ) * 2 ^ 28 * 1024 ^ Dmax ≤ (1 / 2 : ℝ) * M28 :=
    calc (65 : ℝ) * 2 ^ 28 * 1024 ^ Dmax = (1024 : ℝ) ^ Dmax * (65 * 2 ^ 28) := by ring
      _ ≤ (1024 : ℝ) ^ Dmax * ((1 / 2 : ℝ) * (2 ^ 28) ^ 3) :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = (1 / 2 : ℝ) * ((1024 : ℝ) ^ Dmax * (2 ^ 28) ^ 3) := by ring
      _ ≤ (1 / 2 : ℝ) * M28 := mul_le_mul_of_nonneg_left p2 (by norm_num)
  have p6 : (2 ^ 26 : ℝ) ^ (e + 2) + 16 * 65 ≤ (1 / 2 : ℝ) * M28 :=
    calc (2 ^ 26 : ℝ) ^ (e + 2) + 16 * 65 ≤ (2 ^ 26 : ℝ) ^ (e + 2) * (1 + 16 * 65) := by linarith
      _ ≤ (2 ^ 26 : ℝ) ^ (e + 2) * ((1 / 2 : ℝ) * 2 ^ 28) :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = (1 / 2 : ℝ) * ((2 ^ 26 : ℝ) ^ (e + 2) * 2 ^ 28) := by ring
      _ ≤ (1 / 2 : ℝ) * M28 := mul_le_mul_of_nonneg_left p1 (by norm_num)
  have hc1 : (cConv : ℝ) * (2 ^ 26 : ℝ) ^ (e + 2) ≤ (cConv : ℝ) * M28 :=
    mul_le_mul_of_nonneg_left (le_trans (by linarith [p3]) p1) (Nat.cast_nonneg (α := ℝ) cConv)
  have hc2 : (Cidle : ℝ) * 65 ≤ (Cidle : ℝ) * M28 :=
    mul_le_mul_of_nonneg_left (le_trans (by linarith [p3]) p1) (Nat.cast_nonneg (α := ℝ) Cidle)
  have q1 : (2 ^ 12 : ℝ) ^ (Dmax + 1) ≤ M28 :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) _).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have q2 : (2 ^ 20 : ℝ) ^ (Dmax + 1) ≤ M28 :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) _).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have q3 : (2 ^ 17 : ℝ) ≤ M28 :=
    le_trans (by norm_num : (2 ^ 17 : ℝ) ≤ 2 ^ 28) (le_self_pow₀ (by norm_num) (by omega))
  have q4 : 7 * M28 ≤ (2 ^ 30 : ℝ) ^ (Dmax + e + 4) :=
    (mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
      (by positivity) (by norm_num)).trans_eq (pow_succ' (2 ^ 30 : ℝ) (Dmax + e + 3)).symm
  have q5 := mul_le_mul_of_nonneg_left q4 (by positivity : (0 : ℝ) ≤ cConv + Cidle + 1)
  have q6 : (0 : ℝ) ≤ (cConv + Cidle : ℝ) * M28 := by positivity
  linarith

private theorem chanHeConvCap_bound (cConv e n U L B : ℕ) {ε₁ : ℝ}
    (hε₁_pos : 0 < ε₁) (hε₁_le : ε₁ ≤ 1 / 4) (hLpos : 1 ≤ L) (hB1 : 1 ≤ B)
    (hUsz : U.size + 1 ≤ B)
    (hm2_le : (mPar n U + 1) ^ 2 ≤ 513 ^ 2 * n * L ^ 2 * B ^ 4)
    (hbud_le : chanHeIterBudget n + 1 ≤ 65 * L ^ 5) {Z : ℝ} (hZ_nn : 0 ≤ Z)
    (hz1 : (n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 9 * (B : ℝ) ^ (e + 8) ≤ Z)
    (hz2 : (1 : ℝ) * (L : ℝ) ^ 5 * (B : ℝ) ^ 0 ≤ Z) :
    ((chanHeIterBudget n + 1 : ℕ) : ℝ) * (chanHeConvCap cConv ε₁ e n U : ℝ) ≤
      (cConv + 1 : ℝ) * (2 ^ 26) ^ (e + 2) * Z := by
  let m := mPar n U
  have h8m : ((8 * m ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) ≤
      (2 ^ 22) ^ 2 * (n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 4 * (B : ℝ) ^ 8 := by
    have h1 : 8 * m ^ 2 ≤ 2 ^ 22 * n * L ^ 2 * B ^ 4 :=
      calc 8 * m ^ 2 ≤ 8 * (m + 1) ^ 2 :=
            Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.le_succ m) 2)
        _ ≤ 8 * (513 ^ 2 * n * L ^ 2 * B ^ 4) := Nat.mul_le_mul_left 8 hm2_le
        _ = (8 * 513 ^ 2) * (n * L ^ 2 * B ^ 4) := by ring
        _ ≤ 2 ^ 22 * (n * L ^ 2 * B ^ 4) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ 22 * n * L ^ 2 * B ^ 4 := by ring
    have he2 : 2 - ε₁ ≤ 2 := by linarith
    calc ((8 * m ^ 2 : ℕ) : ℝ) ^ (2 - ε₁)
        ≤ ((2 ^ 22 * n * L ^ 2 * B ^ 4 : ℕ) : ℝ) ^ (2 - ε₁) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1) (by linarith)
      _ = (2 ^ 22 : ℝ) ^ (2 - ε₁) * (n : ℝ) ^ (2 - ε₁) *
            ((L ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) * ((B ^ 4 : ℕ) : ℝ) ^ (2 - ε₁) := by
          rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
            Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
            Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
            Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 ^ 22 : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (2 - ε₁) *
            ((L ^ 2 : ℕ) : ℝ) ^ (2 : ℝ) * ((B ^ 4 : ℕ) : ℝ) ^ (2 : ℝ) := by
          have b1 := Real.rpow_le_rpow_of_exponent_le (x := (2 ^ 22 : ℝ)) (by norm_num) he2
          have b2 := Real.rpow_le_rpow_of_exponent_le (x := ((L ^ 2 : ℕ) : ℝ))
            (by exact_mod_cast Nat.one_le_pow 2 L hLpos) he2
          have b3 := Real.rpow_le_rpow_of_exponent_le (x := ((B ^ 4 : ℕ) : ℝ))
            (by exact_mod_cast Nat.one_le_pow 4 B hB1) he2
          gcongr
      _ = (2 ^ 22) ^ 2 * (n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 4 * (B : ℝ) ^ 8 := by
          simp only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          push_cast; ring
  have hU10 : ((U.size + 10 : ℕ) : ℝ) ^ e ≤ 10 ^ e * (B : ℝ) ^ e := by
    exact_mod_cast (Nat.pow_le_pow_left (by omega : U.size + 10 ≤ 10 * B) e).trans_eq
      (Nat.mul_pow 10 B e)
  have hcc : (chanHeConvCap cConv ε₁ e n U : ℝ) ≤
      (cConv : ℝ) * (2 ^ 44 * 10 ^ e) *
        ((n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 4 * (B : ℝ) ^ (e + 8)) + (cConv + 2 : ℝ) := by
    have hcl := chanHeConvCap_cast_le cConv (ε₁ := ε₁) e n U
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul h8m hU10 (by positivity) (by positivity)) (Nat.cast_nonneg (α := ℝ) cConv)
    have hrew : (cConv : ℝ) *
        (((2 ^ 22) ^ 2 * (n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 4 * (B : ℝ) ^ 8) *
          (10 ^ e * (B : ℝ) ^ e)) =
        (cConv : ℝ) * (2 ^ 44 * 10 ^ e) *
          ((n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 4 * (B : ℝ) ^ (e + 8)) := by
      rw [pow_add (B : ℝ) e 8]; ring
    dsimp only [m] at hmul; linarith
  have hbR : ((chanHeIterBudget n + 1 : ℕ) : ℝ) ≤ 65 * (L : ℝ) ^ 5 := by exact_mod_cast hbud_le
  calc ((chanHeIterBudget n + 1 : ℕ) : ℝ) * (chanHeConvCap cConv ε₁ e n U : ℝ)
      ≤ (65 * (L : ℝ) ^ 5) * ((cConv : ℝ) * (2 ^ 44 * 10 ^ e) *
          ((n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 4 * (B : ℝ) ^ (e + 8)) + (cConv + 2 : ℝ)) :=
        mul_le_mul hbR hcc (by positivity) (by positivity)
    _ = (cConv : ℝ) * (65 * 2 ^ 44 * 10 ^ e) *
          ((n : ℝ) ^ (2 - ε₁) * (L : ℝ) ^ 9 * (B : ℝ) ^ (e + 8)) +
        (65 * (cConv + 2 : ℝ)) * ((1 : ℝ) * (L : ℝ) ^ 5 * (B : ℝ) ^ 0) := by ring
    _ ≤ ((cConv : ℝ) * (65 * 2 ^ 44 * 10 ^ e) + 65 * (cConv + 2 : ℝ)) * Z := by
        have m1 := mul_le_mul_of_nonneg_left hz1
          (by positivity : (0 : ℝ) ≤ (cConv : ℝ) * (65 * 2 ^ 44 * 10 ^ e))
        have m2 := mul_le_mul_of_nonneg_left hz2
          (by positivity : (0 : ℝ) ≤ 65 * (cConv + 2 : ℝ))
        linarith
    _ ≤ (cConv + 1 : ℝ) * (2 ^ 26) ^ (e + 2) * Z := by
        refine mul_le_mul_of_nonneg_right ?_ hZ_nn
        rw [pow_add (2 ^ 26 : ℝ) e 2]
        have h10e : (10 : ℝ) ^ e ≤ (2 ^ 26 : ℝ) ^ e :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) e
        have h1e : (1 : ℝ) ≤ (2 ^ 26 : ℝ) ^ e := one_le_pow₀ (by norm_num)
        have k0 : (65 : ℝ) * 2 ^ 44 * 10 ^ e + 65 ≤ (2 ^ 26 : ℝ) ^ e * (2 ^ 26) ^ 2 := by
          have s1 := mul_le_mul_of_nonneg_left h10e (by norm_num : (0 : ℝ) ≤ 65 * 2 ^ 44)
          have s2 := mul_le_mul_of_nonneg_right
            (by norm_num : (65 : ℝ) * 2 ^ 44 + 65 ≤ (2 ^ 26) ^ 2)
            (by positivity : (0 : ℝ) ≤ (2 ^ 26 : ℝ) ^ e)
          linarith
        have k1 := mul_le_mul_of_nonneg_left k0 (Nat.cast_nonneg (α := ℝ) cConv)
        have k2 : (130 : ℝ) ≤ (2 ^ 26 : ℝ) ^ e * (2 ^ 26) ^ 2 :=
          (by norm_num : (130 : ℝ) ≤ 1 * (2 ^ 26) ^ 2).trans
            (mul_le_mul_of_nonneg_right h1e (by norm_num))
        linarith

/-- **3SUM reduces to Convolution-3SUM**: `ThreeSumHypothesis → ConvThreeSumHypothesis`. -/
theorem convThreeSumHypothesis_of_threeSumHypothesis (h : ThreeSumHypothesis) :
    ConvThreeSumHypothesis := by
  intro ε hε e hdec
  let ε₁ : ℝ := min ε (1 / 4)
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁_le : ε₁ ≤ 1 / 4 := min_le_right _ _
  have hdec₁ : DecidableInTimeO ConvThreeSum encConvThreeSum
      fun A => (A.length : ℝ) ^ (2 - ε₁) * (convThreeSumBitScale A : ℝ) ^ e := by
    refine hdec.mono 1 (fun A => ?_) (fun A => by positivity)
    simp only [Nat.cast_one, one_mul]
    rcases Nat.eq_zero_or_pos A.length with h0 | hpos
    · have hnil : A = [] := List.length_eq_zero_iff.mp h0
      subst hnil
      rw [convThreeSumBitScale_nil, List.length_nil, Nat.cast_zero, Nat.cast_one, one_pow,
        mul_one, mul_one]
      have hnn : (0 : ℝ) ≤ (0 : ℝ) ^ (2 - ε₁) := by positivity
      by_cases hz : 2 - ε = 0
      · rw [hz, Real.rpow_zero]; linarith
      · rw [Real.zero_rpow hz]; linarith
    · exact (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos)
          (by have : ε₁ ≤ ε := min_le_left _ _; linarith)) (by positivity)).trans
        (le_add_of_nonneg_right zero_le_one)
  obtain ⟨gConv, tConv, cConv, hgConv, hg_iff, htConv⟩ := hdec₁.exists_computableInO
  obtain ⟨dv, hval⟩ := computableInO_validThreeSumBool
  obtain ⟨di, hbud, hinit⟩ := computableInO_chanHeInitAndBudget
  obtain ⟨ds, hstep⟩ := computableInO_chanHeStep hgConv
  let idleSt : ChanHeState := ((false, []), ((0, (0, 0)), []))
  have hBudG := hval.ite hbud (ComputableInO.constZero 0)
  have hInitG := hval.ite hinit (ComputableInO.constZero idleSt)
  let stateBnd (p : ThreeSumInput) := chanHeValidStateBnd p + 16
  let Cidle := chanHeStepCost tConv ds idleSt
  let roundBnd (p : ThreeSumInput) := chanHeValidRoundBnd cConv ε₁ e ds p + Cidle
  have hIter := ((ComputableInO.iterate (B := stateBnd) (R := roundBnd) (Q := roundBnd)
    hBudG hInitG hstep
    (fun p j hj => by
      by_cases hv : validThreeSumBool p = true
      · simp only [hv, ↓reduceIte]
        exact (chanHeStepCost_valid_le hg_iff htConv hv j).trans (Nat.le_add_right _ _)
      · simp only [Bool.eq_false_iff.mpr hv, Bool.false_eq_true, ↓reduceIte] at hj ⊢
        have hj0 : j = 0 := by omega
        subst hj0; exact Nat.le_add_left _ _)
    (fun p j hj => by
      by_cases hv : validThreeSumBool p = true
      · simp only [hv, ↓reduceIte]
        exact (chanHeStepCost_valid_le hg_iff htConv hv j).trans (Nat.le_add_right _ _)
      · simp only [Bool.eq_false_iff.mpr hv, Bool.false_eq_true, ↓reduceIte] at hj ⊢
        have hj0 : j = 0 := by omega
        subst hj0; exact Nat.le_add_left _ _)
    (fun p j hj => by
      by_cases hv : validThreeSumBool p = true
      · simp only [hv, ↓reduceIte]
        exact (encChanHeState_valid_le hg_iff hv j).trans (Nat.le_add_right _ _)
      · simp only [Bool.eq_false_iff.mpr hv, Bool.false_eq_true, ↓reduceIte] at hj ⊢
        have hj0 : j = 0 := by omega
        subst hj0
        have : (encChanHeState idleSt).length ≤ 16 := by
          change (encPair (encPair encBool (encList encChanHeTask))
            (encPair (encPair encNat (encPair encNat encNat)) (encList encNat)) idleSt).length ≤ 16
          simp only [idleSt, length_encPair, length_encNat]; decide
        exact this.trans (Nat.le_add_left 16 _))).fst').fst'
  have hMach := (hval.ite hIter (ComputableInO.constZero false)).of_enc_eq
    (g := decideThreeSum gConv) (encC := encBool) fun p => congrArg encBool (by
      rw [decideThreeSum_eq_ite]
      by_cases hv : validThreeSumBool p = true
      · simp [hv]
      · simp [Bool.eq_false_iff.mpr hv])
  let Dmax := max dv (max di ds)
  let Klog := Dmax + 12
  let E := 4 * Dmax + e + 12
  let ε' := ε₁ / 2
  have hε' : 0 < ε' := by positivity
  obtain ⟨Clog, hClog1, hClog⟩ := exists_nat_size_pow_le_rpow Klog (δ := ε') hε'
  refine h ε' hε' E ?_
  let Cbig : ℕ := (cConv + Cidle + 1) * Clog * (2 ^ 30) ^ (Dmax + e + 4)
  refine (DecidableInTimeO.of_computableInO hMach (decideThreeSum_iff hg_iff)
    (fun _ => le_rfl)).mono Cbig (fun p => ?_) (fun p => by positivity)
  let N := threeSumSize p
  let B := threeSumBitScale p
  have hB1 : 1 ≤ B := threeSumBitScale_pos p
  by_cases hv : validThreeSumBool p = false
  · have hsc_v : B + N.size + 6 ≤ 8 * (N.size + 1) * B := by nlinarith
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · have hp0 : p = ([], ([], [])) := by
        have hsum := threeSumSize_add p
        rcases p with ⟨X, Y, Z⟩
        have : X.length = 0 ∧ Y.length = 0 ∧ Z.length = 0 := by dsimp only [N] at hN0 hsum; omega
        exact Prod.ext (List.length_eq_zero_iff.mp this.1)
          (Prod.ext (List.length_eq_zero_iff.mp this.2.1) (List.length_eq_zero_iff.mp this.2.2))
      subst hp0
      have hsz0 : (0 : ℕ).size = 0 := by decide
      have henc0 : (encThreeSum ([], ([], []))).length ≤ 3 := by
        change (encPair (encList encNat)
          (encPair (encList encNat) (encList encNat)) ([], ([], []))).length ≤ 3
        simp only [length_encPair, encList_nil, List.length_nil]
        norm_num
      simp only [hv, Bool.false_eq_true, ↓reduceIte, threeSumSize_empty, threeSumBitScale_empty,
        hsz0]
      have hnn : (0 : ℝ) ≤ (Cbig : ℝ) * ((0 : ℝ) ^ (2 - ε') * (1 : ℝ) ^ E) := by positivity
      have h7 : (1 : ℝ) ≤ (7 : ℝ) ^ dv := one_le_pow₀ (by norm_num)
      have henc0R : ((encThreeSum ([], ([], []))).length : ℝ) ≤ 3 := by exact_mod_cast henc0
      have hCb : 4 * (7 : ℝ) ^ dv ≤ (Cbig : ℝ) := by
        have h1 : 4 * 7 ^ dv ≤ (2 ^ 30) ^ (Dmax + e + 4) :=
          calc 4 * 7 ^ dv ≤ 7 * 7 ^ Dmax := Nat.mul_le_mul (by norm_num)
                (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
            _ = 7 ^ (Dmax + 1) := (pow_succ' 7 Dmax).symm
            _ ≤ (2 ^ 30) ^ (Dmax + e + 4) :=
                (Nat.pow_le_pow_left (by norm_num) _).trans
                  (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact_mod_cast h1.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hClog1))
      push_cast; linarith
    · have hval_le : (((N + 1) * (B + N.size + 6) ^ dv : ℕ) : ℝ) ≤
          2 * 8 ^ Dmax * (Clog : ℝ) * ((N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E) := by
        have hp : (B + N.size + 6) ^ dv ≤ 8 ^ Dmax * (N.size + 1) ^ Klog * B ^ E :=
          calc (B + N.size + 6) ^ dv ≤ (8 * (N.size + 1) * B) ^ dv := Nat.pow_le_pow_left hsc_v dv
            _ = 8 ^ dv * (N.size + 1) ^ dv * B ^ dv := by simp only [Nat.mul_pow]
            _ ≤ 8 ^ Dmax * (N.size + 1) ^ Klog * B ^ E :=
                Nat.mul_le_mul (Nat.mul_le_mul
                  (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
                  (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [Klog, Dmax]; omega)))
                  (Nat.pow_le_pow_right hB1 (by dsimp only [E, Dmax]; omega))
        have hpR : ((B + N.size + 6 : ℕ) : ℝ) ^ dv ≤
            8 ^ Dmax * ((Clog : ℝ) * (N : ℝ) ^ ε') * (B : ℝ) ^ E :=
          (show ((B + N.size + 6 : ℕ) : ℝ) ^ dv ≤
              8 ^ Dmax * ((N.size + 1 : ℕ) : ℝ) ^ Klog * (B : ℝ) ^ E by exact_mod_cast hp).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hClog N hN1) (by positivity)) (by positivity))
        have hN2 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
          exact_mod_cast (show N + 1 ≤ 2 * N by omega)
        have hNr : (N : ℝ) * (N : ℝ) ^ ε' ≤ (N : ℝ) ^ (2 - ε') := by
          rw [← Real.rpow_one_add' (by positivity) (by linarith)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
            (by dsimp only [ε']; linarith)
        calc (((N + 1) * (B + N.size + 6) ^ dv : ℕ) : ℝ)
            = ((N + 1 : ℕ) : ℝ) * ((B + N.size + 6 : ℕ) : ℝ) ^ dv := by push_cast; ring
          _ ≤ (2 * (N : ℝ)) * (8 ^ Dmax * ((Clog : ℝ) * (N : ℝ) ^ ε') * (B : ℝ) ^ E) :=
              mul_le_mul hN2 hpR (by positivity) (by positivity)
          _ = 2 * 8 ^ Dmax * (Clog : ℝ) * ((N : ℝ) * (N : ℝ) ^ ε') * (B : ℝ) ^ E := by ring
          _ ≤ 2 * 8 ^ Dmax * (Clog : ℝ) * ((N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E) := by
              nlinarith [mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hNr (by positivity : (0 : ℝ) ≤ 2 * 8 ^ Dmax * Clog))
                (by positivity : (0 : ℝ) ≤ (B : ℝ) ^ E)]
      have henc_le : ((encThreeSum p).length : ℝ) ≤
          24 * ((N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E) := by
        have h1 : (encThreeSum p).length ≤ 24 * (N * B) := by
          change (encPair (encList encNat) (encPair (encList encNat) (encList encNat)) p).length ≤ _
          simp only [length_encPair]
          obtain ⟨hmX, hmY, hmZ⟩ := listMax_size_lt_threeSumBitScale p
          have b (L : List ℕ) (hM : listMax Nat.size L < B) :
              (encList encNat L).length ≤ 5 * (L.length * B) :=
            ((length_encList_le_mul encNat L (b := listMax Nat.size L) fun x hx => by
              rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
              (Nat.mul_le_mul_left _ (by omega : _ ≤ 5 * B))).trans_eq (Nat.mul_left_comm _ _ _)
          have := b p.1 hmX; have := b p.2.1 hmY; have := b p.2.2 hmZ
          have := threeSumSize_add p; nlinarith
        have hNR : (N : ℝ) ≤ (N : ℝ) ^ (2 - ε') := by
          conv_lhs => rw [← Real.rpow_one (N : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
            (by dsimp only [ε']; linarith)
        have hBR : (B : ℝ) ≤ (B : ℝ) ^ E := by
          exact_mod_cast Nat.le_self_pow (by dsimp only [E]; omega) B
        exact (show ((encThreeSum p).length : ℝ) ≤ 24 * ((N : ℝ) * (B : ℝ)) by
          exact_mod_cast h1).trans
          (by nlinarith [mul_le_mul hNR hBR (by positivity) (by positivity)])
      have hcoef : 6 * (8 : ℝ) ^ Dmax * Clog + 24 ≤ Cbig := by
        have h1 : 6 * 8 ^ Dmax + 24 ≤ (2 ^ 30) ^ (Dmax + e + 4) :=
          calc 6 * 8 ^ Dmax + 24
              ≤ 256 * (2 ^ 30) ^ Dmax := by
                have h8 : 8 ^ Dmax ≤ (2 ^ 30) ^ Dmax := Nat.pow_le_pow_left (by norm_num) Dmax
                have h1p : 1 ≤ (2 ^ 30) ^ Dmax := Nat.one_le_pow Dmax (2 ^ 30) (by norm_num)
                omega
            _ ≤ (2 ^ 30) ^ (e + 4) * (2 ^ 30) ^ Dmax :=
                Nat.mul_le_mul_right _
                  (le_trans (by norm_num : 256 ≤ 2 ^ 30) (Nat.le_self_pow (by omega) _))
            _ = (2 ^ 30) ^ (Dmax + e + 4) := by rw [← Nat.pow_add]; congr 1; omega
        have h2 : Clog * (6 * 8 ^ Dmax + 24) ≤ Cbig :=
          calc Clog * (6 * 8 ^ Dmax + 24)
              ≤ Clog * (2 ^ 30) ^ (Dmax + e + 4) := Nat.mul_le_mul_left Clog h1
            _ ≤ (cConv + Cidle + 1) * (Clog * (2 ^ 30) ^ (Dmax + e + 4)) :=
                Nat.le_mul_of_pos_left _ (by omega)
            _ = Cbig := (Nat.mul_assoc _ _ _).symm
        have hc1 : (1 : ℝ) ≤ Clog := by exact_mod_cast hClog1
        have h2R : (Clog : ℝ) * ((6 * 8 ^ Dmax + 24 : ℕ) : ℝ) ≤ Cbig := by exact_mod_cast h2
        push_cast at h2R; nlinarith
      simp only [hv, Bool.false_eq_true, ↓reduceIte, Nat.cast_add]
      have hZ_nn : (0 : ℝ) ≤ (N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcoef hZ_nn]
  · have hvT : validThreeSumBool p = true := Bool.eq_true_of_not_eq_false hv
    obtain ⟨hn1, hN_eq⟩ := validThreeSumBool_lengths hvT
    let n := p.1.length
    have hN1 : 1 ≤ N := by dsimp only [N]; omega
    let U := threeSumMaxVal p
    let m := mPar n U
    have hUsz : U.size + 1 ≤ B := threeSumMaxVal_size_succ_le p
    let L := N.size + 1
    have hL2 : 2 ≤ L := Nat.succ_le_succ (Nat.size_pos.mpr (by omega))
    have hnsz : n.size + 1 ≤ L := Nat.succ_le_succ (Nat.size_le_size (by omega))
    have hm_le : m + 1 ≤ 513 * Nat.sqrt n * L * B ^ 2 := by
      have h0 := mPar_le_bound (U := U) hn1
      have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left (512 * Nat.sqrt n) hnsz)
        (Nat.pow_le_pow_left hUsz 2)
      have hpos : 1 ≤ Nat.sqrt n * L * B ^ 2 :=
        Nat.mul_pos (Nat.mul_pos (Nat.sqrt_pos.mpr hn1) (Nat.succ_pos _)) (Nat.pow_pos hB1)
      dsimp only [m]; nlinarith
    have hm2_le : (m + 1) ^ 2 ≤ 513 ^ 2 * n * L ^ 2 * B ^ 4 :=
      calc (m + 1) ^ 2 ≤ (513 * Nat.sqrt n * L * B ^ 2) ^ 2 := Nat.pow_le_pow_left hm_le 2
        _ = 513 ^ 2 * (Nat.sqrt n * Nat.sqrt n) * L ^ 2 * B ^ 4 := by ring
        _ ≤ 513 ^ 2 * n * L ^ 2 * B ^ 4 := by have := Nat.sqrt_le n; gcongr
    have hmsz : (m + 1).size ≤ 3 * L + 3 * B + 12 := by
      refine Nat.size_le.mpr ?_
      have h1 : 513 < 2 ^ 10 := by norm_num
      have h2 : Nat.sqrt n < 2 ^ L := (Nat.sqrt_le_self n).trans_lt
        ((Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h3 : L < 2 ^ L := Nat.lt_two_pow_self
      have h4 : B ^ 2 ≤ 2 ^ (2 * B) :=
        calc B ^ 2 = B * B := sq B
          _ ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le
          _ = 2 ^ (2 * B) := by rw [← Nat.pow_add, two_mul]
      have h5 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.le h2.le) h3.le) h4
      simp only [← Nat.pow_add] at h5
      exact lt_of_le_of_lt hm_le
        (lt_of_le_of_lt h5 (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have hsc_all : 32 * (n.size + U.size + (m + 1).size + 16) ≤ 1024 * L * B := by
      have hLB : 1 ≤ L * B := Nat.mul_pos (Nat.succ_pos _) hB1
      have hL_le : L ≤ L * B := Nat.le_mul_of_pos_right L hB1
      have hB_le : B ≤ L * B := Nat.le_mul_of_pos_left B (Nat.succ_pos _)
      have : 1024 * L * B = 1024 * (L * B) := Nat.mul_assoc _ _ _
      omega
    have hisc : chanHeInitScale p ≤ 1024 * L * B := chanHeInitScale_le (by
      have hLB : 1 ≤ L * B := Nat.mul_pos (Nat.succ_pos _) hB1
      have hL_le : L ≤ L * B := Nat.le_mul_of_pos_right L hB1
      have hB_le : B ≤ L * B := Nat.le_mul_of_pos_left B (Nat.succ_pos _)
      have : 1024 * L * B = 1024 * (L * B) := Nat.mul_assoc _ _ _
      have : N.size + 1 = L := rfl
      change B + N.size + U.size + (m + 1).size + 8 ≤ 1024 * L * B
      omega)
    have hbud_le : chanHeIterBudget n + 1 ≤ 65 * L ^ 5 := chanHeIterBudget_succ_le hnsz
    let Z : ℝ := (Clog : ℝ) * ((N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E)
    have hZ_pos : 1 ≤ Z := by
      dsimp only [Z]
      have c1 : (1 : ℝ) ≤ Clog := by exact_mod_cast hClog1
      have c2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 - ε') :=
        Real.one_le_rpow (by exact_mod_cast hN1) (by dsimp only [ε']; linarith)
      have c3 : (1 : ℝ) ≤ (B : ℝ) ^ E := one_le_pow₀ (by exact_mod_cast hB1)
      nlinarith [mul_le_mul c2 c3 zero_le_one (by positivity)]
    have hZ_ge (a b : ℕ) (ha : a ≤ Klog) (hb : b ≤ E) {x : ℝ}
        (hx : x ≤ (N : ℝ) ^ (2 - 2 * ε')) :
        x * (L : ℝ) ^ a * (B : ℝ) ^ b ≤ Z := by
      have hLa : (L : ℝ) ^ a ≤ (Clog : ℝ) * (N : ℝ) ^ ε' :=
        (pow_le_pow_right₀ (by dsimp only [L]; exact_mod_cast Nat.succ_pos N.size) ha).trans
          (hClog N hN1)
      have hBb : (B : ℝ) ^ b ≤ (B : ℝ) ^ E := pow_le_pow_right₀ (by exact_mod_cast hB1) hb
      have hNr : (N : ℝ) ^ (2 - 2 * ε') * (N : ℝ) ^ ε' = (N : ℝ) ^ (2 - ε') := by
        rw [← Real.rpow_add (by exact_mod_cast hN1)]; congr 1; ring
      by_cases hx0 : x ≤ 0
      · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx0 (by positivity))
          (by positivity)).trans (by positivity)
      · push Not at hx0
        calc x * (L : ℝ) ^ a * (B : ℝ) ^ b
            ≤ (N : ℝ) ^ (2 - 2 * ε') * ((Clog : ℝ) * (N : ℝ) ^ ε') * (B : ℝ) ^ E :=
              mul_le_mul (mul_le_mul hx hLa (by positivity) (by positivity)) hBb
                (by positivity) (by positivity)
          _ = (Clog : ℝ) * ((N : ℝ) ^ (2 - 2 * ε') * (N : ℝ) ^ ε') * (B : ℝ) ^ E := by ring
          _ = Z := by dsimp only [Z]; rw [hNr]; ring
    have hn_rpow : (n : ℝ) ≤ (N : ℝ) ^ (2 - 2 * ε') :=
      calc (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show n ≤ N by omega)
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (2 - 2 * ε') := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
            (by dsimp only [ε']; linarith)
    have hn32_rpow : ((n * Nat.sqrt n : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 - 2 * ε') := by
      have hsqR : (Nat.sqrt n : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.le_sqrt_of_sq_le (by
          have : Nat.sqrt n * Nat.sqrt n ≤ N := (Nat.sqrt_le n).trans (by omega)
          have h' : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
          linarith [sq (Nat.sqrt n : ℝ)])
      have hnR : (n : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]; exact_mod_cast (show n ≤ N by omega)
      calc ((n * Nat.sqrt n : ℕ) : ℝ) = (n : ℝ) * (Nat.sqrt n : ℝ) := by push_cast; ring
        _ ≤ (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
            mul_le_mul hnR hsqR (by positivity) (by positivity)
        _ = (N : ℝ) ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add (by exact_mod_cast hN1)]; norm_num
        _ ≤ (N : ℝ) ^ (2 - 2 * ε') := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
            (by dsimp only [ε']; linarith)
    have t_val : (((N + 1) * (B + N.size + 6) ^ dv : ℕ) : ℝ) ≤ (2 ^ 12) ^ (Dmax + 1) * Z := by
      have hb : (B + N.size + 6) ^ dv ≤ 8 ^ Dmax * L ^ Dmax * B ^ Dmax :=
        (Nat.pow_le_pow_left (by dsimp only [L]; nlinarith : _ ≤ 8 * L * B) dv).trans (by
          simp only [Nat.mul_pow]
          exact Nat.mul_le_mul (Nat.mul_le_mul
            (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
            (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)))
            (Nat.pow_le_pow_right hB1 (le_max_left _ _)))
      have h1 : (N + 1) * (B + N.size + 6) ^ dv ≤ 2 * 8 ^ Dmax * N * L ^ Dmax * B ^ Dmax :=
        (Nat.mul_le_mul (by omega : N + 1 ≤ 2 * N) hb).trans_eq (by ring)
      have hNR : (N : ℝ) ≤ 3 * (N : ℝ) ^ (2 - 2 * ε') := by
        change (threeSumSize p : ℝ) ≤ _; rw [hN_eq]; push_cast; linarith
      have hz := hZ_ge Dmax Dmax (by dsimp only [Klog]; omega) (by dsimp only [E]; omega)
        (x := (N : ℝ) / 3) (by linarith)
      have h1R : (((N + 1) * (B + N.size + 6) ^ dv : ℕ) : ℝ) ≤
          6 * 8 ^ Dmax * (((N : ℝ) / 3) * (L : ℝ) ^ Dmax * (B : ℝ) ^ Dmax) :=
        (show _ ≤ ((2 * 8 ^ Dmax * N * L ^ Dmax * B ^ Dmax : ℕ) : ℝ) by
          exact_mod_cast h1).trans_eq (by push_cast; ring)
      have hc : (6 : ℝ) * 8 ^ Dmax ≤ (2 ^ 12) ^ (Dmax + 1) :=
        calc (6 : ℝ) * 8 ^ Dmax
            ≤ (2 ^ 12 : ℝ) * (2 ^ 12 : ℝ) ^ Dmax :=
              mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
                (by positivity) (by norm_num)
          _ = (2 ^ 12) ^ (Dmax + 1) := (pow_succ' _ _).symm
      exact h1R.trans ((mul_le_mul_of_nonneg_left hz (by positivity)).trans
        (mul_le_mul_of_nonneg_right hc (by positivity)))
    have t_init : ((chanHeInitRawCost p * chanHeInitScale p ^ di : ℕ) : ℝ) ≤
        (2 ^ 20) ^ (Dmax + 1) * Z := by
      have hdi_le : di ≤ Dmax := (le_max_left di ds).trans (le_max_right dv _)
      have hrc : chanHeInitRawCost p ≤ 2 ^ 19 * n * L ^ 2 * B ^ 4 := chanHeInitRawCost_le (by
        have hLB : n ≤ n * L ^ 2 * B ^ 4 := by
          have : 1 ≤ L ^ 2 * B ^ 4 := Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) (Nat.pow_pos hB1)
          calc n = n * 1 := (Nat.mul_one n).symm
            _ ≤ n * (L ^ 2 * B ^ 4) := Nat.mul_le_mul_left n this
            _ = n * L ^ 2 * B ^ 4 := (Nat.mul_assoc _ _ _).symm
        have hc0 : 513 ^ 2 + 4 ≤ 2 ^ 19 := by norm_num
        have h1 : (m + 1) ^ 2 + 3 * n + 1 ≤ (513 ^ 2 + 4) * (n * L ^ 2 * B ^ 4) := by
          have : 513 ^ 2 * n * L ^ 2 * B ^ 4 = 513 ^ 2 * (n * L ^ 2 * B ^ 4) := by ring
          have : 1 ≤ n * L ^ 2 * B ^ 4 := hn1.trans hLB
          omega
        change threeSumSize p + (m + 1) ^ 2 + 1 ≤ 2 ^ 19 * n * L ^ 2 * B ^ 4
        rw [hN_eq, Nat.add_comm (3 * n) ((m + 1) ^ 2)]
        exact h1.trans ((Nat.mul_le_mul_right _ hc0).trans_eq (by ring)))
      have hsp : chanHeInitScale p ^ di ≤ 1024 ^ Dmax * L ^ Dmax * B ^ Dmax :=
        (Nat.pow_le_pow_left hisc di).trans (by
          simp only [Nat.mul_pow]
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hdi_le)
            (Nat.pow_le_pow_right (Nat.succ_pos _) hdi_le)) (Nat.pow_le_pow_right hB1 hdi_le))
      have hprod : ((chanHeInitRawCost p * chanHeInitScale p ^ di : ℕ) : ℝ) ≤
          2 ^ 19 * 1024 ^ Dmax * ((n : ℝ) * (L : ℝ) ^ (Dmax + 2) * (B : ℝ) ^ (Dmax + 4)) :=
        (show _ ≤ (((2 ^ 19 * n * L ^ 2 * B ^ 4) *
            (1024 ^ Dmax * L ^ Dmax * B ^ Dmax) : ℕ) : ℝ) by
          exact_mod_cast Nat.mul_le_mul hrc hsp).trans_eq (by push_cast; ring)
      have hz := hZ_ge (Dmax + 2) (Dmax + 4) (by dsimp only [Klog]; omega)
        (by dsimp only [E]; omega) hn_rpow
      have hc : (2 : ℝ) ^ 19 * 1024 ^ Dmax ≤ (2 ^ 20) ^ (Dmax + 1) :=
        calc (2 : ℝ) ^ 19 * 1024 ^ Dmax
            ≤ (2 ^ 20 : ℝ) * (2 ^ 20 : ℝ) ^ Dmax :=
              mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
                (by positivity) (by norm_num)
          _ = (2 ^ 20) ^ (Dmax + 1) := (pow_succ' _ _).symm
      exact hprod.trans ((mul_le_mul_of_nonneg_left hz (by positivity)).trans
        (mul_le_mul_of_nonneg_right hc (by positivity)))
    have hconv_R : ((chanHeIterBudget n + 1 : ℕ) : ℝ) * (chanHeConvCap cConv ε₁ e n U : ℝ) ≤
        (cConv + 1 : ℝ) * (2 ^ 26) ^ (e + 2) * Z :=
      chanHeConvCap_bound cConv e n U L B hε₁ hε₁_le (Nat.succ_pos _) hB1 hUsz hm2_le hbud_le
        (by positivity)
        (hZ_ge 9 (e + 8) (by dsimp only [Klog]; omega) (by dsimp only [E]; omega) (by
          rw [show 2 - ε₁ = 2 - 2 * ε' by dsimp only [ε']; ring]
          exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show n ≤ N by omega))
            (by dsimp only [ε']; linarith)))
        (hZ_ge 5 0 (by dsimp only [Klog]; omega) (by dsimp only [E]; omega)
          (Real.one_le_rpow (by exact_mod_cast hN1) (by dsimp only [ε']; linarith)))
    let coefAlg : ℝ := (cConv + 1 : ℝ) * (2 ^ 26) ^ (e + 2) + (Cidle + 16 : ℝ) * 65 +
        65 * 2 ^ 28 * 1024 ^ Dmax
    have halg_R : ((chanHeIterBudget n + 1 : ℕ) : ℝ) * ((roundBnd p + stateBnd p : ℕ) : ℝ) ≤
        coefAlg * Z := by
      have hds_le : ds ≤ Dmax := (le_max_right di ds).trans (le_max_right dv _)
      have halg_nat :=
        chanHeValidRoundAndState_le cConv Cidle e ds Dmax ε₁ hds_le hvT hn1 hm_le hm2_le hsc_all
      have hz_alg := hZ_ge (Dmax + 8) (Dmax + 4) (by dsimp only [Klog]; omega)
        (by dsimp only [E]; omega) hn32_rpow
      have hz_id := hZ_ge 5 0 (by dsimp only [Klog]; omega) (by dsimp only [E]; omega)
        (Real.one_le_rpow (by exact_mod_cast hN1) (by dsimp only [ε']; linarith))
      have hbR : ((chanHeIterBudget n + 1 : ℕ) : ℝ) ≤ 65 * (L : ℝ) ^ 5 := by
        exact_mod_cast hbud_le
      have hnatR : ((roundBnd p + stateBnd p : ℕ) : ℝ) ≤
          (chanHeConvCap cConv ε₁ e n U : ℝ) + ((Cidle + 16 : ℝ) +
            2 ^ 28 * 1024 ^ Dmax * ((n * Nat.sqrt n : ℕ) : ℝ) * (L : ℝ) ^ (Dmax + 3) *
              (B : ℝ) ^ (Dmax + 4)) := by
        have h0 : ((roundBnd p + stateBnd p : ℕ) : ℝ) ≤
            ((chanHeConvCap cConv ε₁ e n U + (Cidle + 16) + 2 ^ 28 * 1024 ^ Dmax *
              (n * Nat.sqrt n) * L ^ (Dmax + 3) * B ^ (Dmax + 4) : ℕ) : ℝ) := by
          exact_mod_cast halg_nat
        refine h0.trans_eq ?_
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      have hpart2 : ((chanHeIterBudget n + 1 : ℕ) : ℝ) * ((Cidle + 16 : ℝ) +
          2 ^ 28 * 1024 ^ Dmax * ((n * Nat.sqrt n : ℕ) : ℝ) * (L : ℝ) ^ (Dmax + 3) *
            (B : ℝ) ^ (Dmax + 4)) ≤
          ((Cidle + 16 : ℝ) * 65 + 65 * 2 ^ 28 * 1024 ^ Dmax) * Z :=
        calc _ ≤ (65 * (L : ℝ) ^ 5) * ((Cidle + 16 : ℝ) +
              2 ^ 28 * 1024 ^ Dmax * ((n * Nat.sqrt n : ℕ) : ℝ) * (L : ℝ) ^ (Dmax + 3) *
                (B : ℝ) ^ (Dmax + 4)) := mul_le_mul_of_nonneg_right hbR (by positivity)
          _ = ((Cidle + 16 : ℝ) * 65) * ((1 : ℝ) * (L : ℝ) ^ 5 * (B : ℝ) ^ 0) +
              (65 * 2 ^ 28 * 1024 ^ Dmax) *
                (((n * Nat.sqrt n : ℕ) : ℝ) * (L : ℝ) ^ (Dmax + 8) * (B : ℝ) ^ (Dmax + 4)) := by
              ring
          _ ≤ ((Cidle + 16 : ℝ) * 65) * Z + (65 * 2 ^ 28 * 1024 ^ Dmax) * Z :=
              add_le_add (mul_le_mul_of_nonneg_left hz_id (by positivity))
                (mul_le_mul_of_nonneg_left hz_alg (by positivity))
          _ = ((Cidle + 16 : ℝ) * 65 + 65 * 2 ^ 28 * 1024 ^ Dmax) * Z := (add_mul _ _ _).symm
      calc ((chanHeIterBudget n + 1 : ℕ) : ℝ) * ((roundBnd p + stateBnd p : ℕ) : ℝ)
          ≤ ((chanHeIterBudget n + 1 : ℕ) : ℝ) * (chanHeConvCap cConv ε₁ e n U : ℝ) +
              ((chanHeIterBudget n + 1 : ℕ) : ℝ) * ((Cidle + 16 : ℝ) +
                2 ^ 28 * 1024 ^ Dmax * ((n * Nat.sqrt n : ℕ) : ℝ) * (L : ℝ) ^ (Dmax + 3) *
                  (B : ℝ) ^ (Dmax + 4)) := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left hnatR (by positivity)
        _ ≤ (cConv + 1 : ℝ) * (2 ^ 26) ^ (e + 2) * Z +
              ((Cidle + 16 : ℝ) * 65 + 65 * 2 ^ 28 * 1024 ^ Dmax) * Z :=
            add_le_add hconv_R hpart2
        _ = coefAlg * Z := by dsimp only [coefAlg]; ring
    have hnb_sq : ((chanHeIterBudget n + 1 : ℕ) : ℝ) *
        (((encNat (chanHeIterBudget n)).length + 1 : ℕ) : ℝ) ^ 2 ≤ 2 ^ 17 * Z := by
      rw [length_encNat]
      have h1 : (chanHeIterBudget n).size + 1 ≤ 32 * L := by
        have hsz : (chanHeIterBudget n).size ≤ 6 * L + 8 := by
          refine Nat.size_le.mpr ?_
          have hL5 : L ^ 5 ≤ 2 ^ (5 * L) := by
            rw [mul_comm 5 L, Nat.pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 5
          calc chanHeIterBudget n < 65 * L ^ 5 := hbud_le
            _ ≤ 2 ^ 7 * 2 ^ (5 * L) := Nat.mul_le_mul (by norm_num) hL5
            _ = 2 ^ (5 * L + 7) := (Nat.pow_add 2 7 (5 * L)).symm.trans (by congr 1; omega)
            _ < 2 ^ (6 * L + 8) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have hsq : (((chanHeIterBudget n).size + 1 : ℕ) : ℝ) ^ 2 ≤ 1024 * (L : ℝ) ^ 2 := by
        exact_mod_cast (Nat.pow_le_pow_left h1 2).trans_eq (by ring)
      have hbR : ((chanHeIterBudget n + 1 : ℕ) : ℝ) ≤ 65 * (L : ℝ) ^ 5 := by
        exact_mod_cast hbud_le
      have hz := hZ_ge 7 0 (by dsimp only [Klog]; omega) (by dsimp only [E]; omega)
        (Real.one_le_rpow (by exact_mod_cast hN1) (by dsimp only [ε']; linarith))
      calc _ ≤ (65 * (L : ℝ) ^ 5) * (1024 * (L : ℝ) ^ 2) :=
            mul_le_mul hbR hsq (by positivity) (by positivity)
        _ = (65 * 1024) * ((1 : ℝ) * (L : ℝ) ^ 7 * (B : ℝ) ^ 0) := by ring
        _ ≤ (65 * 1024) * Z := mul_le_mul_of_nonneg_left hz (by norm_num)
        _ ≤ 2 ^ 17 * Z := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hfin : ((cConv + Cidle + 1 : ℝ) * (2 ^ 30 : ℝ) ^ (Dmax + e + 4)) * Z ≤
        (Cbig : ℝ) * ((N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E) + Cbig := by
      have : ((cConv + Cidle + 1 : ℝ) * (2 ^ 30 : ℝ) ^ (Dmax + e + 4)) * Z =
          (Cbig : ℝ) * ((N : ℝ) ^ (2 - ε') * (B : ℝ) ^ E) := by
        dsimp only [Cbig, Z]
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
        ring
      rw [this]; exact le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) Cbig)
    have hiter_R : (((chanHeIterBudget n + 1) * (roundBnd p + stateBnd p +
        ((encNat (chanHeIterBudget n)).length + 1) ^ 2) : ℕ) : ℝ) ≤
        (coefAlg + 2 ^ 17) * Z := by
      rw [Nat.mul_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, add_mul]
      exact add_le_add halg_R hnb_sq
    let Tv := (N + 1) * (B + N.size + 6) ^ dv
    let Ti := chanHeInitRawCost p * chanHeInitScale p ^ di
    let Titer := (chanHeIterBudget n + 1) * (roundBnd p + stateBnd p +
      ((encNat (chanHeIterBudget n)).length + 1) ^ 2)
    have hlhs : ((Tv + ((Tv + Ti) + (Tv + Ti) + Titer) : ℕ) : ℝ) ≤
        ((cConv + Cidle + 1 : ℝ) * (2 ^ 30 : ℝ) ^ (Dmax + e + 4)) * Z := by
      simp only [Nat.cast_add]
      calc (Tv : ℝ) + ((Tv : ℝ) + (Ti : ℝ) + ((Tv : ℝ) + (Ti : ℝ)) + (Titer : ℝ))
          = 3 * (Tv : ℝ) + 2 * (Ti : ℝ) + (Titer : ℝ) := by ring
        _ ≤ 3 * ((2 ^ 12 : ℝ) ^ (Dmax + 1) * Z) + 2 * ((2 ^ 20 : ℝ) ^ (Dmax + 1) * Z) +
              (coefAlg + 2 ^ 17) * Z :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left t_val (by norm_num))
              (mul_le_mul_of_nonneg_left t_init (by norm_num))) hiter_R
        _ = (3 * (2 ^ 12 : ℝ) ^ (Dmax + 1) + 2 * (2 ^ 20 : ℝ) ^ (Dmax + 1) +
              coefAlg + 2 ^ 17) * Z := by ring
        _ ≤ ((cConv + Cidle + 1 : ℝ) * (2 ^ 30 : ℝ) ^ (Dmax + e + 4)) * Z :=
            mul_le_mul_of_nonneg_right (chanHe_coef_combine cConv Cidle Dmax e) (by positivity)
    simp only [hvT, ↓reduceIte]
    exact hlhs.trans hfin

/-- **Equivalence of the 3SUM and Convolution-3SUM Hypotheses** on deterministic multi-tape Turing
machines. -/
theorem threeSumHypothesis_iff_convThreeSumHypothesis :
    ThreeSumHypothesis ↔ ConvThreeSumHypothesis :=
  ⟨convThreeSumHypothesis_of_threeSumHypothesis, threeSumHypothesis_of_convThreeSumHypothesis⟩

end CslibFrontier.Complexity
