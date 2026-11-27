module
/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

public import CslibFrontier.Foundations.Combinatorics.Expander.ParvareshVardyArithmetic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.PolyTime.BinaryField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit Guruswami–Umans–Vadhan Lossless Bipartite Expanders

This module instantiates the Parvaresh–Vardy construction over `Cslib.BinaryField t` modulo the
irreducible cyclotomic trinomials `X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1` to establish the explicit
unbalanced lossless bipartite vertex expander theorem of Guruswami, Umans, and Vadhan, under
standard Lean constraints:

* `guruswami_umans_vadhan_expander`: for all real `γ > 0`, all `M r : ℕ` with `r ≤ M`, and all real
  `0 < ε < 1`, constructs an `(r, d, (1 - ε) * d)`-expander on `Fin M` and `Fin N` with
  `d ≤ C_γ * (max 1 (log₂ M) * max 1 (log₂ r) / ε) ^ (1 + 1 / γ)`, `N ≤ d ^ 2 * r ^ (1 + γ)`, and
  a De Morgan neighbor-list circuit of size at most `C₀ * (d + Nat.clog 2 M + 2) ^ K₀` for universal
  constants `C₀ K₀ : ℕ`.
* `guruswami_umans_vadhan_explicit_family`: for all positive rationals `γ = p / q` and
  `ε = 1 / B ∈ (0, 1)` and any polynomial-time parameter `rFn : ℕ → ℕ`, constructs a uniform
  zero-advice `ExplicitBipartiteFamily` (`Turing.MultiTapeTM.ComputableInPolyTime`) realizing these
  bounds.

## Main results

* `CslibFrontier.ParvareshVardy.guruswami_umans_vadhan_expander`: general real-parameter
  Guruswami–Umans–Vadhan lossless bipartite expander with polynomial-size neighbor-list circuits.
* `CslibFrontier.ParvareshVardy.guruswami_umans_vadhan_explicit_family`: uniform polynomial-time
  `ExplicitBipartiteFamily` for rational `γ > 0` and `ε = 1 / B ∈ (0, 1)`.
-/

public section

namespace CslibFrontier.ParvareshVardy

open CslibFrontier.ProofComplexity
open Cslib Cslib.BinaryField Turing.MultiTapeTM ComputableInPolyTime

/-! ### Parameter Selection and Shared Numerical Verification -/

private def coprimeOffset (t₀ : ℕ) : ℕ :=
  if t₀ % 6 == 1 || t₀ % 6 == 5 then 0
  else if t₀ % 6 == 0 || t₀ % 6 == 4 then 1
  else if t₀ % 6 == 3 then 2
  else 3

private theorem coprimeOffset_le_three (t₀ : ℕ) : coprimeOffset t₀ ≤ 3 := by
  unfold coprimeOffset; split_ifs <;> omega

private theorem coprime_add_coprimeOffset (t₀ : ℕ) :
    Nat.Coprime (t₀ + coprimeOffset t₀) 6 := by
  set x := t₀ + coprimeOffset t₀
  have hmod : x % 6 = 1 ∨ x % 6 = 5 := by
    dsimp [x]; unfold coprimeOffset
    have := Nat.mod_lt t₀ (by decide : 0 < 6)
    rcases (show t₀ % 6 = 0 ∨ t₀ % 6 = 1 ∨ t₀ % 6 = 2 ∨ t₀ % 6 = 3 ∨
        t₀ % 6 = 4 ∨ t₀ % 6 = 5 by omega) with h | h | h | h | h | h <;>
      simp [h] <;> omega
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec 6]
  rcases hmod with h | h <;> rw [h] <;> decide

private theorem clog_two_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Nat.clog 2 n :=
  Nat.succ_le_iff.2 (Nat.clog_pos (by decide : 1 < 2) (by omega))

private theorem clog_two_le_two_mul_max_logb {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * max 1 (Real.logb 2 n) := by
  set L := Nat.clog 2 n
  have hL1 : 1 ≤ L := clog_two_pos hn
  have hpow : ((2 : ℝ) ^ (L - 1)) < (n : ℝ) := by
    exact_mod_cast (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (show L - 1 < L by omega)
  have hlog : ((L - 1 : ℕ) : ℝ) ≤ Real.logb 2 n := by
    simpa [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num)] using
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpow.le
  have hcast : (L : ℝ) = ((L - 1 : ℕ) : ℝ) + 1 := by rw [Nat.cast_sub hL1]; ring
  linarith [le_max_left (1 : ℝ) (Real.logb 2 n), le_max_right (1 : ℝ) (Real.logb 2 n)]

private theorem guv_params_verify {M r h m Q k : ℕ} {γ ε : ℝ}
    (hγ : 0 < γ) (hε0 : 0 < ε) (hε1 : ε < 1) (hr2 : 2 ≤ r) (hrM : r ≤ M)
    (hh2 : 2 ≤ h)
    (hA_le_h : 72 * (Nat.clog 2 M : ℝ) * (Nat.clog 2 r : ℝ) / ε ≤ (h : ℝ) ^ γ)
    (hh_up : (h : ℝ) ≤ 2 * (72 * (Nat.clog 2 M : ℝ) * (Nat.clog 2 r : ℝ) / ε) ^ (1 / γ))
    (hm1 : 1 ≤ m) (hr_hm : r ≤ h ^ m) (hhm_lt : h ^ (m - 1) < r)
    (hQ_lo : 3 * (m : ℝ) * (Nat.clog 2 M : ℝ) * (h : ℝ) / ε ≤ (Q : ℝ))
    (hQ_hi : (Q : ℝ) ≤ 4 * (Nat.clog 2 M : ℝ) * (Nat.clog 2 r : ℝ) * (h : ℝ) / ε)
    (hcap : Nat.clog 2 M ≤ 2 * 3 ^ k * (Nat.clog 2 Q + coprimeOffset (Nat.clog 2 Q)))
    (hdeg : 2 * 3 ^ k ≤ 3 * Nat.clog 2 M) :
    let t := Nat.clog 2 Q + coprimeOffset (Nat.clog 2 Q)
    let d := 2 ^ t
    let N := d ^ (m + 1)
    1 ≤ t ∧ h ≤ d ∧
    (∀ u < M, ∀ j < d, pvNeighborNat (Nat.clog 2 M) t k m h u j < N) ∧
    (∀ u < M, Set.InjOn (pvNeighborNat (Nat.clog 2 M) t k m h u) { j | j < d }) ∧
    IsBipartiteExpander
      (fun (u : Fin M) (v : Fin N) ↦
        ∃ j : Fin d, pvNeighborNat (Nat.clog 2 M) t k m h u.val j.val = v.val)
      r d ((1 - ε) * (d : ℝ)) ∧
    (N : ℝ) ≤ (d : ℝ) ^ 2 * (r : ℝ) ^ (1 + γ) ∧
    (d : ℝ) ≤ 2 * (288 : ℝ) ^ (1 + 1 / γ) *
      (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) := by
  have hM2 : 2 ≤ M := le_trans hr2 hrM
  set wU := Nat.clog 2 M
  set wR := Nat.clog 2 r
  have hwU1 : 1 ≤ wU := clog_two_pos hM2
  set A : ℝ := 72 * (wU : ℝ) * (wR : ℝ) / ε
  have hQ_ge : 6 ≤ Q := by
    have h6 : (6 : ℝ) ≤ 3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε := by
      rw [le_div_iff₀ hε0]
      have : (2 : ℝ) ≤ (m : ℝ) * (wU : ℝ) * (h : ℝ) := by
        exact_mod_cast (show 2 ≤ m * wU * h by have := Nat.mul_le_mul hm1 hwU1; nlinarith)
      nlinarith
    exact_mod_cast h6.trans hQ_lo
  set t₀ := Nat.clog 2 Q
  have ht₀1 : 1 ≤ t₀ := clog_two_pos (by omega)
  set t := t₀ + coprimeOffset t₀
  have ht1 : 1 ≤ t := by omega
  set d := 2 ^ t
  have hd_cast : ((2 : ℝ) ^ t) = (d : ℝ) := by simp [d]
  have hd_lo : 3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε ≤ (d : ℝ) :=
    hQ_lo.trans <| (show (Q : ℝ) ≤ ((2 ^ t₀ : ℕ) : ℝ) by
      exact_mod_cast Nat.le_pow_clog (by decide) Q).trans
      (by exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hd_Ah : (d : ℝ) ≤ A * (h : ℝ) := by
    have hd_16Q : d ≤ 16 * Q := by
      have h1 : d ≤ 8 * 2 ^ t₀ := by
        dsimp [d, t]; rw [pow_add, mul_comm]
        exact Nat.mul_le_mul_right _
          ((Nat.pow_le_pow_right (by decide) (coprimeOffset_le_three t₀)).trans (by norm_num))
      have hlt : 2 ^ (t₀ - 1) < Q :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (show t₀ - 1 < t₀ by omega)
      have h2 : 2 ^ t₀ = 2 * 2 ^ (t₀ - 1) := by
        conv_lhs => rw [show t₀ = (t₀ - 1) + 1 by omega, pow_succ']
      omega
    calc (d : ℝ) ≤ 16 * (Q : ℝ) := by exact_mod_cast hd_16Q
      _ ≤ 16 * (4 * (wU : ℝ) * (wR : ℝ) * (h : ℝ) / ε) := by linarith
      _ ≤ 72 * (wU : ℝ) * (wR : ℝ) * (h : ℝ) / ε := by
          rw [show 16 * (4 * (wU : ℝ) * (wR : ℝ) * (h : ℝ) / ε) =
            64 * (wU : ℝ) * (wR : ℝ) * (h : ℝ) / ε by ring]
          exact div_le_div_of_nonneg_right
            (by linarith [show (0 : ℝ) ≤ (wU : ℝ) * (wR : ℝ) * (h : ℝ) by positivity]) hε0.le
      _ = A * (h : ℝ) := by dsimp [A]; ring
  have hd_hpow : (d : ℝ) ≤ (h : ℝ) ^ (1 + γ) :=
    hd_Ah.trans <| (mul_le_mul_of_nonneg_right hA_le_h (by positivity)).trans_eq
      (by rw [Real.rpow_add (by positivity), Real.rpow_one, mul_comm])
  have hh_d : h ≤ d := by
    have hR : (h : ℝ) ≤ 3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε := by
      rw [le_div_iff₀ hε0]
      have h1 : (1 : ℝ) ≤ (m : ℝ) * (wU : ℝ) := by exact_mod_cast Nat.mul_le_mul hm1 hwU1
      have h2 : (h : ℝ) * ε ≤ (h : ℝ) := mul_le_of_le_one_right (by positivity) hε1.le
      nlinarith [show (0 : ℝ) ≤ (h : ℝ) by positivity]
    exact_mod_cast hR.trans hd_lo
  have hloss : ((m * (h - 1) * (2 * 3 ^ k - 1) : ℕ) : ℝ) ≤ ε * (d : ℝ) := by
    have hnat : m * (h - 1) * (2 * 3 ^ k - 1) ≤ 3 * m * wU * h :=
      calc m * (h - 1) * (2 * 3 ^ k - 1)
          ≤ m * h * (3 * wU) := Nat.mul_le_mul (Nat.mul_le_mul_left m (Nat.sub_le h 1))
              ((Nat.sub_le _ 1).trans hdeg)
        _ = 3 * m * wU * h := by ring
    exact (show _ ≤ 3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) by exact_mod_cast hnat).trans
      (by have := (div_le_iff₀ hε0).1 hd_lo; linarith)
  have hbound : m * (h - 1) * (2 * 3 ^ k - 1) < 2 ^ t := by
    have : ((m * (h - 1) * (2 * 3 ^ k - 1) : ℕ) : ℝ) < (d : ℝ) := by
      nlinarith [show (0 : ℝ) < (d : ℝ) by positivity]
    exact_mod_cast this
  have ha_ge : (1 - ε) * (2 ^ t : ℝ) ≤
      ((2 ^ t - m * (h - 1) * (2 * 3 ^ k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hbound.le, Nat.cast_pow, Nat.cast_ofNat, hd_cast]
    linarith
  obtain ⟨hltN, hinjN, hexpN⟩ :=
    isBipartiteExpander_pvNeighborNat ht1 (coprime_add_coprimeOffset t₀) hh2 hm1
      hcap hr_hm hbound ha_ge
  refine ⟨ht1, hh_d, hltN, hinjN, hexpN, ?_, ?_⟩
  · have hm_eq : m + 1 = 2 + (m - 1) := by omega
    have hN_cast : (((d ^ (m + 1) : ℕ) : ℝ)) = (d : ℝ) ^ 2 * (d : ℝ) ^ (m - 1) := by
      rw [Nat.cast_pow, hm_eq, pow_add]
    rw [hN_cast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (d : ℝ) ^ (m - 1)
        ≤ ((h : ℝ) ^ (1 + γ)) ^ (m - 1) := pow_le_pow_left₀ (by positivity) hd_hpow _
      _ = ((h : ℝ) ^ (m - 1)) ^ (1 + γ) := by
          rw [← Real.rpow_natCast ((h : ℝ) ^ (1 + γ)), ← Real.rpow_mul (by positivity),
            mul_comm (1 + γ), Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ (r : ℝ) ^ (1 + γ) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhm_lt.le) (by positivity)
  · have hA_pos : 0 < A := by
      have hwR1 : 1 ≤ wR := clog_two_pos hr2
      dsimp [A]; positivity
    have hA_bound : A ≤ 288 * (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) := by
      have hmul := mul_le_mul (clog_two_le_two_mul_max_logb hM2)
        (clog_two_le_two_mul_max_logb hr2) (by positivity) (by positivity)
      dsimp [A]
      calc 72 * (wU : ℝ) * (wR : ℝ) / ε
          ≤ 72 * (4 * (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r))) / ε :=
            div_le_div_of_nonneg_right (by linarith) hε0.le
        _ = 288 * (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) := by ring
    calc (d : ℝ) ≤ A * (h : ℝ) := hd_Ah
      _ ≤ A * (2 * A ^ (1 / γ)) := mul_le_mul_of_nonneg_left hh_up hA_pos.le
      _ = 2 * A ^ (1 + 1 / γ) := by rw [Real.rpow_add hA_pos, Real.rpow_one]; ring
      _ ≤ 2 * (288 * (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε)) ^ (1 + 1 / γ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA_pos.le hA_bound (by positivity))
            (by norm_num)
      _ = 2 * (288 : ℝ) ^ (1 + 1 / γ) *
            (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) := by
          have hb_nn : 0 ≤ max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε :=
            div_nonneg (mul_nonneg (by linarith [le_max_left (1 : ℝ) (Real.logb 2 M)])
              (by linarith [le_max_left (1 : ℝ) (Real.logb 2 r)])) hε0.le
          rw [Real.mul_rpow (by norm_num) hb_nn, ← mul_assoc]

private theorem one_le_guv_deg_bound {γ ε : ℝ} (hγ : 0 < γ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (M r : ℕ) :
    (1 : ℝ) ≤ 2 * (288 : ℝ) ^ (1 + 1 / γ) *
      (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) := by
  have h1 : (1 : ℝ) ≤ (288 : ℝ) ^ (1 + 1 / γ) := Real.one_le_rpow (by norm_num) (by positivity)
  have hb : (1 : ℝ) ≤ max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε := by
    rw [le_div_iff₀ hε0]
    have ha : (1 : ℝ) ≤ max 1 (Real.logb 2 M) := le_max_left _ _
    have hc : (1 : ℝ) ≤ max 1 (Real.logb 2 r) := le_max_left _ _
    have hp : (1 : ℝ) ≤ max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) := by nlinarith
    linarith
  have h2 : (1 : ℝ) ≤ (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) :=
    Real.one_le_rpow hb (by positivity)
  have h12 : (1 : ℝ) ≤ (288 : ℝ) ^ (1 + 1 / γ) *
      (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) := by nlinarith
  linarith

/-! ### General Real-Parameter Guruswami–Umans–Vadhan Expander Theorem -/

/-- **Guruswami–Umans–Vadhan lossless bipartite expander theorem**: there exist universal constants
`C₀ K₀ : ℕ` such that for every real `γ > 0`, there is a constant `C_γ > 0` such that for all
`M r : ℕ` with `r ≤ M` and all real `0 < ε < 1`, there exist `N d : ℕ`, a neighbor function
`neighbor : Fin M → Fin d → Fin N`, and a De Morgan circuit
`c : Circuit Boolean.signature (Nat.clog 2 M) (d * Nat.clog 2 N)` satisfying:
1. `fun u v ↦ ∃ j, neighbor u j = v` is an `(r, d, (1 - ε) * d)`-expander;
2. `(N : ℝ) ≤ (d : ℝ) ^ 2 * (r : ℝ) ^ (1 + γ)`, with `1 ≤ d` and `N = 2 ^ Nat.clog 2 N` whenever
   `1 ≤ r`;
3. `(d : ℝ) ≤ C_γ * (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ)`;
4. `c.size ≤ C₀ * (d + Nat.clog 2 M + 2) ^ K₀` and `c` computes all binary bits of all `d`
   neighbors of every left vertex `x`. -/
theorem guruswami_umans_vadhan_expander :
    ∃ C₀ K₀ : ℕ, ∀ {γ : ℝ}, 0 < γ →
      ∃ Cγ : ℝ, 0 < Cγ ∧
        ∀ (M r : ℕ), r ≤ M → ∀ {ε : ℝ}, 0 < ε → ε < 1 →
          ∃ (N d : ℕ) (neighbor : Fin M → Fin d → Fin N)
            (c : Circuits.Circuit Circuits.Boolean.signature (Nat.clog 2 M) (d * Nat.clog 2 N)),
            IsBipartiteExpander (fun u v ↦ ∃ j : Fin d, neighbor u j = v)
              r d ((1 - ε) * (d : ℝ)) ∧
            (N : ℝ) ≤ (d : ℝ) ^ 2 * (r : ℝ) ^ (1 + γ) ∧
            (1 ≤ r → 1 ≤ d ∧ N = 2 ^ Nat.clog 2 N) ∧
            (d : ℝ) ≤ Cγ *
              (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) ∧
            c.size ≤ C₀ * (d + Nat.clog 2 M + 2) ^ K₀ ∧
            ∀ (x : BitString (Nat.clog 2 M)) (hx : lsbValue (List.ofFn x) < M)
              (j : Fin d) (b : Fin (Nat.clog 2 N)) (idx : Fin (d * Nat.clog 2 N)),
              idx.val = j.val * Nat.clog 2 N + b.val →
              c.eval Circuits.Boolean.interpretation x idx =
                (neighbor ⟨lsbValue (List.ofFn x), hx⟩ j).val.testBit b.val := by
  classical
  obtain ⟨C₀, K₀, hcirc⟩ := exists_circuit_pvNeighborNat
  refine ⟨max 1 C₀, K₀, fun {γ} hγ ↦ ⟨2 * (288 : ℝ) ^ (1 + 1 / γ), by positivity,
    fun M r hrM {ε} hε0 hε1 ↦ ?_⟩⟩
  have emptySize (w : ℕ) : (Circuits.Circuit.pi fun i : Fin 0 ↦
      (i.elim0 : Circuits.Circuit Circuits.Boolean.signature w 1)).size = 0 := by simp
  have hbound_nn : 0 ≤ 2 * (288 : ℝ) ^ (1 + 1 / γ) *
      (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 r) / ε) ^ (1 + 1 / γ) :=
    le_trans zero_le_one (one_le_guv_deg_bound hγ hε0 hε1 M r)
  rcases eq_or_ne r 0 with rfl | hr0
  · refine ⟨0, 0, fun _ j ↦ j.elim0,
      show Circuits.Circuit _ _ (0 * Nat.clog 2 0) from Circuits.Circuit.pi fun i ↦ i.elim0,
      ⟨fun u ↦ by
        have he : bipartiteNeighbors (fun (_ : Fin M) (v : Fin 0) ↦
            ∃ j : Fin 0, (j.elim0 : Fin 0) = v) u = ∅ := by ext v; exact v.elim0
        rw [he, Finset.card_empty],
       fun W hW ↦ by simp [Nat.eq_zero_of_le_zero hW]⟩,
      by simp [Real.zero_rpow (show (1 : ℝ) + γ ≠ 0 by linarith)],
      fun h ↦ by omega, by simpa using hbound_nn, ?_, fun _ _ j ↦ j.elim0⟩
    change (Circuits.Circuit.pi fun i : Fin 0 ↦ i.elim0).size ≤ _
    rw [emptySize]; exact Nat.zero_le _
  rcases eq_or_ne r 1 with rfl | hr1
  · refine ⟨1, 1, fun _ _ ↦ 0,
      show Circuits.Circuit _ _ (1 * Nat.clog 2 1) from Circuits.Circuit.pi fun i ↦ i.elim0,
      ⟨fun u ↦ ?_, fun W hW ↦ ?_⟩,
      by simp, fun _ ↦ ⟨le_rfl, by simp⟩,
      by simpa using one_le_guv_deg_bound hγ hε0 hε1 M 1, ?_,
      fun _ _ _ b ↦ by have := b.isLt; simp at this⟩
    · have he : bipartiteNeighbors
          (fun (_ : Fin M) (v : Fin 1) ↦ ∃ _ : Fin 1, (0 : Fin 1) = v) u = Finset.univ := by
        ext v
        exact ⟨fun _ ↦ Finset.mem_univ v,
          fun _ ↦ mem_bipartiteNeighbors.2 ⟨0, (Fin.eq_zero v).symm⟩⟩
      rw [he, Finset.card_univ, Fintype.card_fin]
    · rcases Nat.eq_zero_or_pos W.card with hW0 | hWpos
      · simp [hW0]
      · obtain ⟨u, hu⟩ := Finset.card_pos.1 hWpos
        have hmem : (0 : Fin 1) ∈ bipartiteNeighborSet
            (fun (_ : Fin M) (v : Fin 1) ↦ ∃ _ : Fin 1, (0 : Fin 1) = v) W :=
          mem_bipartiteNeighborSet.2 ⟨u, hu, (0 : Fin 1), rfl⟩
        have hc : (1 : ℝ) ≤ ((bipartiteNeighborSet
            (fun (_ : Fin M) (v : Fin 1) ↦ ∃ _ : Fin 1, (0 : Fin 1) = v) W).card : ℝ) := by
          exact_mod_cast Finset.card_pos.2 ⟨0, hmem⟩
        rw [show W.card = 1 by omega]; simp only [Nat.cast_one, mul_one]; linarith
    · change (Circuits.Circuit.pi fun i : Fin 0 ↦ i.elim0).size ≤ _
      rw [emptySize]; exact Nat.zero_le _
  have hr2 : 2 ≤ r := by omega
  set wU := Nat.clog 2 M
  set wR := Nat.clog 2 r
  have hwU1 : 1 ≤ wU := clog_two_pos (le_trans hr2 hrM)
  have hwR1 : 1 ≤ wR := clog_two_pos hr2
  set A : ℝ := 72 * (wU : ℝ) * (wR : ℝ) / ε
  have hA1 : (1 : ℝ) ≤ A := by
    dsimp [A]; rw [le_div_iff₀ hε0]
    have : (1 : ℝ) ≤ (wU : ℝ) * (wR : ℝ) := by exact_mod_cast Nat.mul_le_mul hwU1 hwR1
    nlinarith
  set h : ℕ := max 2 ⌈A ^ (1 / γ)⌉₊
  have hh2 : 2 ≤ h := le_max_left _ _
  have hA_le_h : A ≤ (h : ℝ) ^ γ := by
    have hle : A ^ (1 / γ) ≤ (h : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 ⌈A ^ (1 / γ)⌉₊)
    have hpow := Real.rpow_le_rpow (by positivity) hle hγ.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hγ.ne', Real.rpow_one] at hpow
  have hh_up : (h : ℝ) ≤ 2 * A ^ (1 / γ) := by
    have hp1 : (1 : ℝ) ≤ A ^ (1 / γ) := Real.one_le_rpow hA1 (by positivity)
    have hc := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ A ^ (1 / γ) by positivity)).le
    have : (h : ℝ) = max (2 : ℝ) (⌈A ^ (1 / γ)⌉₊ : ℝ) := by simp [h]
    rw [this]; exact max_le (by linarith) (by linarith)
  have hexM : ∃ m, r ≤ h ^ m :=
    ⟨wR, (Nat.le_pow_clog (by decide) r).trans (Nat.pow_le_pow_left hh2 _)⟩
  set m := Nat.find hexM
  have hr_hm : r ≤ h ^ m := Nat.find_spec hexM
  have hm_le : m ≤ wR :=
    Nat.find_min' hexM ((Nat.le_pow_clog (by decide) r).trans (Nat.pow_le_pow_left hh2 _))
  have hm1 : 1 ≤ m := by
    rcases m with _ | _
    · simp at hr_hm; omega
    · omega
  have hhm_lt : h ^ (m - 1) < r := by
    by_contra hge
    exact Nat.find_min hexM (show m - 1 < m by omega) (not_lt.1 hge)
  set Q : ℕ := ⌈3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε⌉₊
  have hmwUh2 : (2 : ℝ) ≤ (m : ℝ) * (wU : ℝ) * (h : ℝ) := by
    exact_mod_cast (show 2 ≤ m * wU * h by have := Nat.mul_le_mul hm1 hwU1; nlinarith)
  have hQ_hi : (Q : ℝ) ≤ 4 * (wU : ℝ) * (wR : ℝ) * (h : ℝ) / ε := by
    have hc := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * m * wU * h / ε by positivity)).le
    have h1 : (1 : ℝ) ≤ (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε := by
      rw [le_div_iff₀ hε0]; linarith
    have hsum : (Q : ℝ) ≤ 4 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε := by
      have : 3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε +
          (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε =
          4 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε := by ring
      linarith
    have hmR : (m : ℝ) ≤ (wR : ℝ) := by exact_mod_cast hm_le
    refine hsum.trans (div_le_div_of_nonneg_right ?_ hε0.le)
    have hmul := mul_le_mul_of_nonneg_right hmR (show (0 : ℝ) ≤ 4 * wU * h by positivity)
    linarith
  set t := Nat.clog 2 Q + coprimeOffset (Nat.clog 2 Q)
  have ht1 : 1 ≤ t := by
    have hQ2 : 2 ≤ Q := by
      have : (2 : ℝ) ≤ (Q : ℝ) :=
        (show (2 : ℝ) ≤ 3 * m * wU * h / ε by rw [le_div_iff₀ hε0]; linarith).trans (Nat.le_ceil _)
      exact_mod_cast this
    have := clog_two_pos hQ2; omega
  have hexK : ∃ k, wU ≤ 2 * 3 ^ k * t :=
    ⟨wU, by have := le_of_lt (Nat.lt_pow_self (a := 3) (by decide) (n := wU)); nlinarith⟩
  set k := Nat.find hexK
  have hcap : wU ≤ 2 * 3 ^ k * t := Nat.find_spec hexK
  have hdeg : 2 * 3 ^ k ≤ 3 * wU := by
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [hk0]; simp; omega
    · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hlt : 2 * 3 ^ k' * t < wU := by
        by_contra hge
        exact Nat.find_min hexK (show k' < k by omega) (not_lt.1 hge)
      rw [hk', pow_succ]; nlinarith
  obtain ⟨_, hh_d, hltN, -, hexp, hN_le, hd_le⟩ :=
    guv_params_verify hγ hε0 hε1 hr2 hrM hh2 hA_le_h hh_up hm1 hr_hm hhm_lt
      (Nat.le_ceil _) hQ_hi hcap hdeg
  set d := 2 ^ t
  set N := d ^ (m + 1)
  have hN_pow : N = 2 ^ ((m + 1) * t) := by dsimp [N, d]; rw [← pow_mul, mul_comm t]
  have hclogN : Nat.clog 2 N = (m + 1) * t := by rw [hN_pow, Nat.clog_pow _ _ (by decide)]
  obtain ⟨c₀, hc₀_sz, hc₀_ev⟩ :=
    hcirc M t k m h ht1 hm1 hh_d hdeg (hm_le.trans (Nat.clog_mono_right 2 hrM))
  have hdout : d * Nat.clog 2 N = d * ((m + 1) * t) := by rw [hclogN]
  let cOut : Circuits.Circuit Circuits.Boolean.signature wU (d * Nat.clog 2 N) :=
    (Circuits.Circuit.wiring Circuits.Boolean.signature (Fin.cast hdout)).comp c₀
  refine ⟨N, d, fun u j ↦ ⟨pvNeighborNat wU t k m h u.val j.val, hltN u.val u.isLt j.val j.isLt⟩,
    cOut, by simpa only [Fin.ext_iff] using hexp, hN_le,
    fun _ ↦ ⟨Nat.one_le_pow _ _ (by decide), by rw [hclogN, hN_pow]⟩, hd_le, ?_, ?_⟩
  · have hsz : cOut.size = c₀.size := by simp [cOut]
    rw [hsz]
    exact hc₀_sz.trans (Nat.mul_le_mul_right _ (le_max_right 1 C₀))
  · intro x hx j b idx hidx
    have hev : cOut.eval Circuits.Boolean.interpretation x idx =
        c₀.eval Circuits.Boolean.interpretation x (idx.cast hdout) := by simp [cOut]
    rw [hev]
    exact hc₀_ev x j (b.cast hclogN) (idx.cast hdout) (by simpa [hclogN] using hidx)

/-! ### Uniform Polynomial-Time `ExplicitBipartiteFamily` for Rational `γ` and `ε` -/

section UniformFamily

attribute [local irreducible] ComputableInPolyTime

private def execClog2 (n : ℕ) : ℕ := (n - 1).size

private theorem execClog2_eq (n : ℕ) : execClog2 n = Nat.clog 2 n := by
  dsimp [execClog2]
  rcases n with _ | _ | m'
  · simp
  · simp
  · refine le_antisymm (Nat.size_le.2 ?_) ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 ?_)
    · have hle : m' + 2 ≤ 2 ^ Nat.clog 2 (m' + 2) := Nat.le_pow_clog (by decide : 1 < 2) (m' + 2)
      change m' + 1 < 2 ^ Nat.clog 2 (m' + 2); omega
    · have hlt : m' + 1 < 2 ^ (m' + 1).size := Nat.lt_size_self (m' + 1)
      change m' + 2 ≤ 2 ^ (m' + 1).size; omega

private def execFindH (p q A : ℕ) : ℕ :=
  ((List.range (A ^ q + 1)).find? fun h ↦ decide (2 ≤ h ∧ A ^ q ≤ h ^ p)).getD (max 2 (A ^ q))

private def execFindM (r h wR : ℕ) : ℕ :=
  ((List.range wR).foldl (fun (st : ℕ × ℕ) i ↦ if r ≤ st.1 then st else (st.1 * h, i + 2))
    (h, 1)).2

private def execFindS (wU t : ℕ) : ℕ :=
  (List.range wU).foldl (fun s _ ↦ if wU ≤ 2 * s * max 1 t then s else 3 * s) 1

private def execGuvParams (p q B M r : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let wU := execClog2 M
  let wR := execClog2 r
  let h := execFindH p q (72 * B * wU * wR)
  let m := execFindM r h wR
  let Q := 3 * B * m * wU * h
  let t₀ := Nat.clog 2 Q
  let off := coprimeOffset t₀
  let t := t₀ + off
  (wU, 2 ^ (off + 1) * 2 ^ t₀, t, execFindS wU t, m, h)

private def execGuvNeighbor (p q B : ℕ) (rFn : ℕ → ℕ) (M u j : ℕ) : ℕ :=
  if decide (rFn M ≤ 1 ∨ M < rFn M) then 0
  else
    let par := execGuvParams p q B M (rFn M)
    lsbValue (pvNeighborBits (BitString.lowBits par.1 u)
      par.2.1 par.2.2.1 par.2.2.2.1 par.2.2.2.2.1 par.2.2.2.2.2.bits
      (BitString.lowBits par.2.2.1 j))

private theorem execFindH_spec {p q A : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hA : 72 ≤ A) :
    let h := execFindH p q A
    2 ≤ h ∧ (A : ℝ) ≤ (h : ℝ) ^ ((p : ℝ) / (q : ℝ)) ∧
      (h : ℝ) ≤ 2 * (A : ℝ) ^ ((q : ℝ) / (p : ℝ)) := by
  let test (x : ℕ) : Bool := decide (2 ≤ x ∧ A ^ q ≤ x ^ p)
  have hAq : 2 ≤ A ^ q := le_trans (by omega) (Nat.le_self_pow (by omega) A)
  have hsat0 : test (A ^ q) = true := decide_eq_true ⟨hAq, Nat.le_self_pow (by omega) _⟩
  obtain ⟨h, hfind⟩ : ∃ h, (List.range (A ^ q + 1)).find? test = some h := by
    rcases hf : (List.range (A ^ q + 1)).find? test with _ | y
    · exact absurd hsat0
        (by simpa using List.find?_eq_none.1 hf (A ^ q) (List.mem_range.2 (by omega)))
    · exact ⟨y, rfl⟩
  have heq : execFindH p q A = h := by
    change ((List.range (A ^ q + 1)).find? test).getD (max 2 (A ^ q)) = h
    rw [hfind]; rfl
  change 2 ≤ execFindH p q A ∧ _ ∧ _
  rw [heq]
  have hsat : 2 ≤ h ∧ A ^ q ≤ h ^ p := by
    have ht_true := List.find?_some hfind
    change decide (2 ≤ h ∧ A ^ q ≤ h ^ p) = true at ht_true
    exact of_decide_eq_true ht_true
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  refine ⟨hsat.1, ?_, ?_⟩
  · have hR : (A : ℝ) ^ (q : ℝ) ≤ (h : ℝ) ^ (p : ℝ) := by
      simpa only [Real.rpow_natCast] using (show (A : ℝ) ^ q ≤ (h : ℝ) ^ p by exact_mod_cast hsat.2)
    have hpow := Real.rpow_le_rpow (by positivity) hR (show (0 : ℝ) ≤ 1 / (q : ℝ) by positivity)
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hq_pos.ne', Real.rpow_one,
      ← Real.rpow_mul (by positivity), mul_one_div] at hpow
  · have hA1 : (1 : ℝ) ≤ (A : ℝ) ^ ((q : ℝ) / (p : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ A by omega)) (by positivity)
    rcases eq_or_ne h 2 with rfl | _
    · push_cast; linarith
    · obtain ⟨_, l₁, _, hrange, hnot⟩ := List.find?_eq_some_iff_append.1 hfind
      have hlen_eq : l₁.length = h := by
        have hget : (List.range (A ^ q + 1))[l₁.length]'(by rw [hrange]; simp) = h := by
          simp [hrange]
        simpa using hget
      have hmem1 : h - 1 ∈ l₁ := by
        have hlt : h - 1 < l₁.length := by omega
        have hltR : h - 1 < A ^ q + 1 := by
          have := congrArg List.length hrange; simp at this; omega
        have hget : l₁[h - 1]'hlt = h - 1 := by
          have : (List.range (A ^ q + 1))[h - 1]'(by simpa using hltR) = l₁[h - 1] := by
            simp [hrange, List.getElem_append_left hlt]
          simpa using this.symm
        exact hget ▸ List.getElem_mem hlt
      have hfail : h ≤ 2 ∨ (h - 1) ^ p < A ^ q := by
        simpa [test] using hnot (h - 1) hmem1
      have hlt_pow : (h - 1) ^ p < A ^ q := by omega
      have hR : ((h - 1 : ℕ) : ℝ) ^ (p : ℝ) ≤ (A : ℝ) ^ (q : ℝ) := by
        simpa only [Real.rpow_natCast] using
          (show ((h - 1 : ℕ) : ℝ) ^ p ≤ (A : ℝ) ^ q by exact_mod_cast hlt_pow.le)
      have hpow := Real.rpow_le_rpow (by positivity) hR (show (0 : ℝ) ≤ 1 / (p : ℝ) by positivity)
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hp_pos.ne', Real.rpow_one,
        ← Real.rpow_mul (by positivity), mul_one_div] at hpow
      have hcast : (h : ℝ) = ((h - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (show 1 ≤ h by omega)]; ring
      linarith

private theorem execFindM_spec {r h wR : ℕ} (hh : 2 ≤ h) (hr2 : 2 ≤ r)
    (hwR1 : 1 ≤ wR) (hr_le : r ≤ 2 ^ wR) :
    let m := execFindM r h wR
    1 ≤ m ∧ m ≤ wR ∧ r ≤ h ^ m ∧ h ^ (m - 1) < r := by
  let step (st : ℕ × ℕ) (i : ℕ) : ℕ × ℕ := if r ≤ st.1 then st else (st.1 * h, i + 2)
  have hinv : ∀ j : ℕ,
      let st := (List.range j).foldl step (h, 1)
      1 ≤ st.2 ∧ st.2 ≤ j + 1 ∧ st.1 = h ^ st.2 ∧
        (r ≤ st.1 → h ^ (st.2 - 1) < r) ∧ (st.1 < r → st.2 = j + 1) := by
    intro j
    induction j with
    | zero =>
      refine ⟨le_rfl, le_rfl, (pow_one h).symm, fun _ ↦ ?_, fun _ ↦ rfl⟩
      change h ^ 0 < r; rw [pow_zero]; omega
    | succ j ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set st := (List.range j).foldl step (h, 1)
      dsimp only [step]
      split_ifs with hle
      · exact ⟨h1, by omega, h3, h4, fun hlt ↦ absurd hlt (not_lt.2 hle)⟩
      · have hlt := lt_of_not_ge hle
        have hs2 := h5 hlt
        refine ⟨by omega, le_rfl, by change st.1 * h = h ^ (j + 2); rw [h3, hs2]; ring,
          fun _ ↦ ?_, fun _ ↦ rfl⟩
        change h ^ (j + 2 - 1) < r
        have hsub' : j + 2 - 1 = st.2 := by omega
        rwa [hsub', ← h3]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv (wR - 1)
  have hsub : wR - 1 + 1 = wR := by omega
  set st1 := (List.range (wR - 1)).foldl step (h, 1)
  have hfin : r ≤ st1.1 := by
    by_contra hnot
    have hlt : st1.1 < r := lt_of_not_ge hnot
    have hs2 : st1.2 = wR := (h5 hlt).trans hsub
    have hr_hwR : r ≤ h ^ wR := hr_le.trans (Nat.pow_le_pow_left hh wR)
    rw [h3, hs2] at hlt; omega
  have heq : execFindM r h wR = st1.2 := by
    change ((List.range wR).foldl step (h, 1)).2 = st1.2
    rw [← hsub, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp [step, st1, hfin]
  change 1 ≤ execFindM r h wR ∧ _
  rw [heq]
  exact ⟨h1, h2.trans_eq hsub, h3 ▸ hfin, h4 hfin⟩

private theorem execFindS_spec {wU t : ℕ} (hwU : 1 ≤ wU) (ht : 1 ≤ t) :
    ∃ k : ℕ, execFindS wU t = 3 ^ k ∧ wU ≤ 2 * 3 ^ k * t ∧ 2 * 3 ^ k ≤ 3 * wU := by
  let step (s _ : ℕ) : ℕ := if wU ≤ 2 * s * t then s else 3 * s
  have hinv : ∀ j : ℕ,
      let s := (List.range j).foldl step 1
      (∃ k, s = 3 ^ k) ∧ 2 * s ≤ 3 * wU ∧ (2 * s * t < wU → s = 3 ^ j) := by
    intro j
    induction j with
    | zero => exact ⟨⟨0, rfl⟩, by dsimp; omega, fun _ ↦ rfl⟩
    | succ j ih =>
      obtain ⟨⟨k, hk⟩, hle, hpow⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set s := (List.range j).foldl step 1
      dsimp only [step]
      split_ifs with hcond
      · exact ⟨⟨k, hk⟩, hle, fun hlt ↦ absurd hlt (not_lt.2 hcond)⟩
      · have hlt := lt_of_not_ge hcond
        exact ⟨⟨k + 1, by rw [hk, pow_succ']⟩, by nlinarith,
          fun _ ↦ by rw [hpow hlt, pow_succ']⟩
  obtain ⟨⟨k, hk⟩, hle, hpow⟩ := hinv wU
  have heqS : execFindS wU t = (List.range wU).foldl step 1 := by
    simp [execFindS, step, max_eq_right ht]
  refine ⟨k, heqS.trans hk, ?_, hk ▸ hle⟩
  rw [← hk]
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have h3 : wU < 3 ^ wU := Nat.lt_pow_self (by decide)
  have heq := hpow hlt
  nlinarith

private theorem poly_execGuvNeighbor (p q B : ℕ) {rFn : ℕ → ℕ}
    (hrFn : ComputableInPolyTime rFn encNat encNat) :
    ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ execGuvNeighbor p q B rFn x.1 x.2.1 x.2.2)
      encNat3 encNat := by
  have hM : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ x.1) encNat3 encNat := fst _ _
  have hu : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ x.2.1) encNat3 encNat :=
    (fst _ _).comp (snd _ _)
  have hj : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ x.2.2) encNat3 encNat :=
    (snd _ _).comp (snd _ _)
  have hr := hrFn.comp hM
  have hclog : ComputableInPolyTime execClog2 encNat encUnary :=
    binary_size.comp (binary_sub' id' (const 1))
  have hwU := hclog.comp hM
  have hwR := hclog.comp hr
  have hA : ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ ↦ 72 * B * execClog2 x.1 * execClog2 (rFn x.1)) encNat3 encUnary := by
    fun_prop
  have hfindH : ComputableInPolyTime (execFindH p q) encUnary encUnary := by
    unfold execFindH
    have hp_fn := unary_pow p
    have hq_fn := unary_pow q
    have htest : ComputableInPolyTime (fun s : ℕ × ℕ ↦ decide (2 ≤ s.2 ∧ s.1 ^ q ≤ s.2 ^ p))
        (encPair encUnary encUnary) encBool := by
      have h1 : ComputableInPolyTime
          (fun s : ℕ × ℕ ↦ decide (2 ≤ s.2) && decide (s.1 ^ q ≤ s.2 ^ p))
          (encPair encUnary encUnary) encBool := by fun_prop
      convert h1 using 1
    have hlist : ComputableInPolyTime (fun A : ℕ ↦ List.range (A ^ q + 1))
        encUnary (encList encUnary) := by fun_prop
    have hopt := findWith htest id' hlist
    have hdef : ComputableInPolyTime (fun A : ℕ ↦ max 2 (A ^ q)) encUnary encUnary := by fun_prop
    fun_prop
  have hh := hfindH.comp hA
  have hfindM : ComputableInPolyTime (fun g : (ℕ × ℕ) × ℕ ↦ execFindM g.1.1 g.1.2 g.2)
      (encPair (encPair encNat encUnary) encUnary) encUnary := by
    unfold execFindM
    let encG := encPair (encPair encNat encUnary) encUnary
    let encPar := encPair encNat encUnary
    let encSt := encPair encNat encUnary
    let encStep := encPair (encPair encPar encSt) encUnary
    have sr : ComputableInPolyTime (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ s.1.1.1)
        encStep encNat := by fun_prop
    have sh : ComputableInPolyTime (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ s.1.1.2)
        encStep encUnary := by fun_prop
    have sa : ComputableInPolyTime (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ s.1.2.1)
        encStep encNat := by fun_prop
    have sst : ComputableInPolyTime (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ s.1.2)
        encStep encSt := by fun_prop
    have si : ComputableInPolyTime (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ s.2 + 2)
        encStep encUnary := by fun_prop
    have hcond : ComputableInPolyTime
        (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ decide (s.1.1.1 ≤ s.1.2.1)) encStep encBool := by
      have hlt := binary_lt' sa sr
      have hneg : ComputableInPolyTime
          (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦ !(decide (s.1.2.1 < s.1.1.1))) encStep encBool := by
        fun_prop
      convert hneg using 1
      funext s; exact Bool.eq_iff_iff.2 (by simp)
    have hstep : ComputableInPolyTime
        (fun s : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ ↦
          if s.1.1.1 ≤ s.1.2.1 then s.1.2 else (s.1.2.1 * s.1.1.2, s.2 + 2))
        encStep encSt := by
      have hmul := binary_mul.comp (sa.prod (unary_to_binary.comp sh))
      convert ComputableInPolyTime.ite' hcond sst (hmul.prod si) using 1
      funext s; by_cases hc : s.1.1.1 ≤ s.1.2.1 <;> simp [hc]
    have gr : ComputableInPolyTime (fun g : (ℕ × ℕ) × ℕ ↦ g.1.1) encG encNat := by fun_prop
    have gh : ComputableInPolyTime (fun g : (ℕ × ℕ) × ℕ ↦ g.1.2) encG encUnary := by fun_prop
    have gw : ComputableInPolyTime (fun g : (ℕ × ℕ) × ℕ ↦ g.2) encG encUnary := by fun_prop
    let bnd (g : (ℕ × ℕ) × ℕ) : ℕ := 2 * (g.1.1.size + g.1.2 + 1) + g.2 + 5
    have hbnd : PolyBounded (fun g ↦ (encG g).length) bnd := by
      have pr : PolyBounded (fun g ↦ (encG g).length) (fun g ↦ g.1.1.size) := by
        simpa using (binary_size.comp gr).polyBounded_length
      have ph : PolyBounded (fun g ↦ (encG g).length) (fun g ↦ g.1.2) := by
        simpa using gh.polyBounded_length
      have pw : PolyBounded (fun g ↦ (encG g).length) (fun g ↦ g.2) := by
        simpa using gw.polyBounded_length
      exact (((PolyBounded.of_forall_le 2 0 (by simp)).mul
        ((pr.add ph).add (.of_forall_le 1 0 (by simp)))).add pw).add
        (.of_forall_le 5 0 (by simp))
    exact (snd encNat encUnary).comp
      (foldlWith_spec (encA := encUnary) (encL := encList encUnary)
        (encP := encPar) (encB := encSt)
        (par := Prod.fst) (list := fun g ↦ List.range g.2) (init := fun g ↦ (g.1.2, 1))
        (step := fun par st i ↦ if par.1 ≤ st.1 then st else (st.1 * par.2, i + 2))
        (fst _ _) (unary_range' gw) ((unary_to_binary.comp gh).prod (const 1)) hstep
        (fun g _ st ↦ st.1 ≤ max g.1.2 (g.1.1 * g.1.2) ∧ st.2 ≤ g.2 + 2)
        (fun g ↦ ⟨le_max_left _ _, by omega⟩)
        (fun g _ st i hpref hinv ↦ by
          split_ifs with hle
          · exact hinv
          · have hi := List.mem_range.1
              (hpref.subset (List.mem_append_right _ (List.mem_singleton_self i)))
            exact ⟨(Nat.mul_le_mul_right _ (le_of_not_ge hle)).trans (le_max_right _ _), by omega⟩)
        hbnd
        (fun g _ st _ hinv ↦ by
          have hsz : (encNat st.1).length ≤ g.1.1.size + g.1.2 := by
            rw [encNat_apply, Nat.size_eq_bits_len]
            rcases eq_or_ne st.1 0 with h0 | _
            · simp [h0]
            · rw [Nat.size_le]
              have h1 : g.1.1 < 2 ^ g.1.1.size := Nat.lt_size_self g.1.1
              have h2 : g.1.2 < 2 ^ g.1.2 := Nat.lt_two_pow_self
              have h3 : g.1.1 * g.1.2 < 2 ^ (g.1.1.size + g.1.2) := by
                rw [pow_add]; exact Nat.mul_lt_mul'' h1 h2
              exact lt_of_le_of_lt hinv.1
                (max_lt (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))) h3)
          simp only [encSt, length_encPair, encUnary_apply, List.length_replicate, bnd]
          omega)).1
  have hm := hfindM.comp ((hr.prod hh).prod hwR)
  let qFn (x : ℕ × ℕ × ℕ) : ℕ :=
    3 * B * execFindM (rFn x.1)
      (execFindH p q (72 * B * execClog2 x.1 * execClog2 (rFn x.1))) (execClog2 (rFn x.1)) *
      execClog2 x.1 * execFindH p q (72 * B * execClog2 x.1 * execClog2 (rFn x.1))
  have hQ : ComputableInPolyTime qFn encNat3 encUnary :=
    unary_mul' (unary_mul' (unary_mul' (const (3 * B)) hm) hwU) hh
  have ht₀ := (unary_clog_const 2).comp hQ
  have hpowT₀ := unary_pow_clog_const hQ 2 2
  have hoff_fn : ComputableInPolyTime coprimeOffset encUnary encUnary := by
    unfold coprimeOffset; fun_prop
  have hoff := hoff_fn.comp ht₀
  have ht := unary_add' ht₀ hoff
  have hBnd : ComputableInPolyTime
      (fun x ↦ 2 ^ (coprimeOffset (Nat.clog 2 (qFn x)) + 1) * 2 ^ Nat.clog 2 (qFn x))
      encNat3 encUnary := by
    have hfac : ComputableInPolyTime _ encNat3 encUnary :=
      ComputableInPolyTime.ite' (unary_beq hoff (const 0)) (const 2)
        (ComputableInPolyTime.ite' (unary_beq hoff (const 1)) (const 4)
          (ComputableInPolyTime.ite' (unary_beq hoff (const 2)) (const 8) (const 16)))
    convert unary_mul' hfac hpowT₀ using 1
    funext x
    congr 1
    have := coprimeOffset_le_three (Nat.clog 2 (qFn x))
    set o := coprimeOffset (Nat.clog 2 (qFn x)) with ho
    rcases (show o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 by omega) with h | h | h | h <;>
      simp [Function.comp_apply, ← ho, h]
  have hfindS : ComputableInPolyTime (fun g : ℕ × ℕ ↦ execFindS g.1 g.2)
      (encPair encUnary encUnary) encUnary := by
    unfold execFindS
    let encG := encPair encUnary encUnary
    let encStep := encPair (encPair encG encUnary) encUnary
    have hstep : ComputableInPolyTime
        (fun s : ((ℕ × ℕ) × ℕ) × ℕ ↦
          if s.1.1.1 ≤ 2 * s.1.2 * max 1 s.1.1.2 then s.1.2 else 3 * s.1.2)
        encStep encUnary := by
      have hd : ComputableInPolyTime
          (fun s : ((ℕ × ℕ) × ℕ) × ℕ ↦
            if decide (s.1.1.1 ≤ 2 * s.1.2 * max 1 s.1.1.2) then s.1.2 else 3 * s.1.2)
          encStep encUnary := by fun_prop
      convert hd using 1
      funext s; by_cases hc : s.1.1.1 ≤ 2 * s.1.2 * max 1 s.1.1.2 <;> simp [hc]
    exact (foldlWith_spec (encA := encUnary) (encL := encList encUnary)
      (encP := encG) (encB := encUnary)
      (par := id) (list := fun g ↦ List.range g.1) (init := fun _ ↦ 1)
      (step := fun par s _ ↦ if par.1 ≤ 2 * s * max 1 par.2 then s else 3 * s)
      id' (unary_range' (fst _ _)) (const 1) hstep
      (fun g _ s ↦ s ≤ 3 * g.1 + 1) (fun _ ↦ by omega)
      (fun g _ s _ _ hinv ↦ by
        split_ifs with hle
        · exact hinv
        · have hlt : 2 * s * max 1 g.2 < g.1 := lt_of_not_ge hle
          have hm1 : 1 ≤ max 1 g.2 := le_max_left 1 g.2
          have hs_lt : 2 * s < g.1 := by nlinarith
          omega)
      (size := fun g ↦ 3 * g.1 + 1)
      (by
        have pg : PolyBounded (fun g ↦ (encG g).length) (fun g ↦ g.1) := by
          have hp0 := (fst encUnary encUnary).polyBounded_length
          simpa only [encUnary_apply, List.length_replicate] using hp0
        exact ((PolyBounded.of_forall_le 3 0 (by simp)).mul pg).add (.of_forall_le 1 0 (by simp)))
      (fun g _ s _ hinv ↦ by
        rw [encUnary_apply, List.length_replicate]
        exact hinv)).1
  have hs := hfindS.comp (hwU.prod ht)
  have hval := computableInPolyTime_lsbValue.comp (computableInPolyTime_pvNeighborBits.comp
    ((bitsLow hwU hu).prod (hBnd.prod (ht.prod (hs.prod (hm.prod
      ((computableInPolyTime_bits_unary.comp hh).prod (bitsLow ht hj))))))))
  have hguard : ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ ↦ decide (rFn x.1 ≤ 1 ∨ x.1 < rFn x.1)) encNat3 encBool := by
    have hor : ComputableInPolyTime
        (fun x : ℕ × ℕ × ℕ ↦ decide (rFn x.1 < 2) || decide (x.1 < rFn x.1)) encNat3 encBool := by
      have := binary_lt' hr (const 2); have := binary_lt' hM hr; fun_prop
    have heq : (fun x : ℕ × ℕ × ℕ ↦ decide (rFn x.1 ≤ 1 ∨ x.1 < rFn x.1)) =
        fun x ↦ decide (rFn x.1 < 2) || decide (x.1 < rFn x.1) := by
      funext x
      rw [← Bool.decide_or]
      exact decide_eq_decide.2 (by omega)
    rwa [heq]
  exact ComputableInPolyTime.ite' hguard (const 0) hval

/-- **Uniform Guruswami–Umans–Vadhan `ExplicitBipartiteFamily`**: for every positive rational
`γ = p / q` (`1 ≤ p`, `1 ≤ q`), rational `ε = 1 / B` (`2 ≤ B`), and polynomial-time function
`rFn : ℕ → ℕ`, there exists a uniform zero-advice `G : ExplicitBipartiteFamily` indexed by left
vertex count `M` (`G.leftSize M = M`) realizing the Guruswami–Umans–Vadhan lossless expansion,
right vertex count, and left degree bounds at every `M` with `rFn M ≤ M`. -/
theorem guruswami_umans_vadhan_explicit_family {p q B : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hB : 2 ≤ B)
    {rFn : ℕ → ℕ} (hrFn : ComputableInPolyTime rFn encNat encNat) :
    let γ : ℝ := (p : ℝ) / (q : ℝ)
    let ε : ℝ := 1 / (B : ℝ)
    ∃ (G : ExplicitBipartiteFamily) (Cγ : ℝ),
      0 < Cγ ∧ (∀ M, G.leftSize M = M) ∧
      ∀ M, rFn M ≤ M →
        IsBipartiteExpander (G.adj M) (rFn M) (G.leftDeg M) ((1 - ε) * (G.leftDeg M : ℝ)) ∧
        (G.rightSize M : ℝ) ≤ (G.leftDeg M : ℝ) ^ 2 * (rFn M : ℝ) ^ (1 + γ) ∧
        (G.leftDeg M : ℝ) ≤
          Cγ * (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 (rFn M)) / ε) ^ (1 + 1 / γ) := by
  set γ : ℝ := (p : ℝ) / (q : ℝ)
  set ε : ℝ := 1 / (B : ℝ)
  have hγ : 0 < γ := by positivity
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    dsimp [ε]; rw [div_lt_one (by positivity)]; exact_mod_cast (show 1 < B by omega)
  have hmain : ∀ M, 2 ≤ rFn M → rFn M ≤ M →
      let par := execGuvParams p q B M (rFn M)
      let d := 2 ^ par.2.2.1
      let N := d ^ (par.2.2.2.2.1 + 1)
      (∀ u < M, ∀ j < d, execGuvNeighbor p q B rFn M u j < N) ∧
      (∀ u < M, Set.InjOn (execGuvNeighbor p q B rFn M u) { j | j < d }) ∧
      IsBipartiteExpander
        (fun (u : Fin M) (v : Fin N) ↦
          ∃ j : Fin d, execGuvNeighbor p q B rFn M u.val j.val = v.val)
        (rFn M) d ((1 - ε) * (d : ℝ)) ∧
      (N : ℝ) ≤ (d : ℝ) ^ 2 * (rFn M : ℝ) ^ (1 + γ) ∧
      (d : ℝ) ≤ 2 * (288 : ℝ) ^ (1 + 1 / γ) *
        (max 1 (Real.logb 2 M) * max 1 (Real.logb 2 (rFn M)) / ε) ^ (1 + 1 / γ) := by
    intro M hr2 hrM
    set r := rFn M
    set wU := Nat.clog 2 M
    set wR := Nat.clog 2 r
    have hwU1 : 1 ≤ wU := clog_two_pos (le_trans hr2 hrM)
    have hwR1 : 1 ≤ wR := clog_two_pos hr2
    set A : ℕ := 72 * B * wU * wR
    have hA_ge : 72 ≤ A := by
      have : 1 ≤ B * wU * wR := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ B by omega) hwU1) hwR1
      dsimp [A]; nlinarith
    have hAR : (A : ℝ) = 72 * (wU : ℝ) * (wR : ℝ) / ε := by
      dsimp [A, ε]; push_cast; field_simp
    obtain ⟨hh2, hA_le_h, hh_up⟩ := execFindH_spec hp hq hA_ge
    set h := execFindH p q A
    obtain ⟨hm1, hm_le, hr_hm, hhm_lt⟩ :=
      execFindM_spec hh2 hr2 hwR1 (Nat.le_pow_clog (by decide) r)
    set m := execFindM r h wR
    set Q : ℕ := 3 * B * m * wU * h
    have hQR : (Q : ℝ) = 3 * (m : ℝ) * (wU : ℝ) * (h : ℝ) / ε := by
      dsimp [Q, ε]; push_cast; field_simp
    have hQ_hi : (Q : ℝ) ≤ 4 * (wU : ℝ) * (wR : ℝ) * (h : ℝ) / ε := by
      rw [hQR]
      apply div_le_div_of_nonneg_right _ hε0.le
      have hmR : (m : ℝ) ≤ (wR : ℝ) := by exact_mod_cast hm_le
      have hmul := mul_le_mul_of_nonneg_right hmR (show (0 : ℝ) ≤ 3 * wU * h by positivity)
      linarith [show (0 : ℝ) ≤ (wU : ℝ) * (wR : ℝ) * (h : ℝ) by positivity]
    set t := Nat.clog 2 Q + coprimeOffset (Nat.clog 2 Q)
    have ht1 : 1 ≤ t := by
      have hQ2 : 2 ≤ Q := by
        have h1 : 1 ≤ B * m * wU :=
          Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ B by omega) hm1) hwU1
        have h2 := Nat.mul_le_mul h1 hh2
        dsimp [Q]; linarith
      have := clog_two_pos hQ2; omega
    obtain ⟨k, hs_eq, hcap, hdeg⟩ := execFindS_spec hwU1 ht1
    have hinv_γ : 1 / γ = (q : ℝ) / (p : ℝ) := by dsimp [γ]; rw [one_div_div]
    obtain ⟨_, _, hltN, hinjN, hexpN, hN_le, hd_le⟩ :=
      guv_params_verify hγ hε0 hε1 hr2 hrM hh2 (hAR ▸ hA_le_h)
        (by rw [← hAR, hinv_γ]; exact hh_up) hm1 hr_hm hhm_lt hQR.symm.le hQ_hi hcap hdeg
    have hsb : 2 ^ (coprimeOffset (Nat.clog 2 Q) + 1) * 2 ^ Nat.clog 2 Q = 2 ^ (t + 1) := by
      dsimp [t]; rw [← pow_add]; congr 1; omega
    have hpar_eq : execGuvParams p q B M r = (wU, 2 ^ (t + 1), t, 3 ^ k, m, h) := by
      simp only [execGuvParams, execClog2_eq]
      change (wU, 2 ^ (coprimeOffset (Nat.clog 2 Q) + 1) * 2 ^ Nat.clog 2 Q, t,
        execFindS wU t, m, h) = _
      rw [hsb, hs_eq]
    have hnb_eq : execGuvNeighbor p q B rFn M = pvNeighborNat wU t k m h := by
      funext u j
      have hf : decide (r ≤ 1 ∨ M < r) = false := decide_eq_false (by omega)
      simp only [execGuvNeighbor, show rFn M = r from rfl, hf, Bool.false_eq_true, ↓reduceIte,
        hpar_eq]
      rfl
    dsimp only
    change (∀ u < M, ∀ j < 2 ^ (execGuvParams p q B M r).2.2.1, _) ∧ _
    rw [hpar_eq, hnb_eq]
    exact ⟨hltN, hinjN, hexpN, hN_le, hd_le⟩
  let leftDegFn (M : ℕ) : ℕ :=
    if rFn M = 0 ∨ M < rFn M then 0
    else if rFn M = 1 then 1
    else 2 ^ (execGuvParams p q B M (rFn M)).2.2.1
  let rightSizeFn (M : ℕ) : ℕ :=
    if rFn M = 0 ∨ M < rFn M then 0
    else if rFn M = 1 then 1
    else
      let par := execGuvParams p q B M (rFn M)
      (2 ^ par.2.2.1) ^ (par.2.2.2.2.1 + 1)
  let G : ExplicitBipartiteFamily :=
    { leftSize := id
      rightSize := rightSizeFn
      leftDeg := leftDegFn
      neighbor := execGuvNeighbor p q B rFn
      neighbor_lt := fun M u j hu hj ↦ by
        dsimp [leftDegFn, rightSizeFn] at hj ⊢
        split_ifs at hj ⊢ with h0 h1
        · omega
        · simp [execGuvNeighbor, h1]
        · exact (hmain M (by omega) (by omega)).1 u hu j hj
      neighbor_injOn := fun M u hu j₁ hj₁ j₂ hj₂ h12 ↦ by
        dsimp [leftDegFn] at hj₁ hj₂
        split_ifs at hj₁ hj₂ with h0 h1
        · simp at hj₁
        · simp at hj₁ hj₂; omega
        · exact (hmain M (by omega) (by omega)).2.1 u hu hj₁ hj₂ h12
      polyTime := poly_execGuvNeighbor p q B hrFn }
  refine ⟨G, 2 * (288 : ℝ) ^ (1 + 1 / γ), by positivity, fun _ ↦ rfl, fun M hrM ↦ ?_⟩
  have hbound_ge1 := one_le_guv_deg_bound hγ hε0 hε1 M (rFn M)
  rcases eq_or_ne (rFn M) 0 with hr0 | hr0
  · have hd0 : G.leftDeg M = 0 := by simp [G, leftDegFn, hr0]
    have hN0 : G.rightSize M = 0 := by simp [G, rightSizeFn, hr0]
    exact ⟨⟨fun u ↦ by rw [G.card_neighbors, hd0],
        fun W hW ↦ by rw [hr0] at hW; simp [Nat.eq_zero_of_le_zero hW]⟩,
      by simp [hN0, hd0, hr0, Real.zero_rpow (show (1 : ℝ) + γ ≠ 0 by linarith)],
      by rw [hd0, Nat.cast_zero]; linarith⟩
  rcases eq_or_ne (rFn M) 1 with hr1 | hr1
  · have hM_not_lt : ¬ M < 1 := by omega
    have hd1 : G.leftDeg M = 1 := by simp [G, leftDegFn, hr1, hM_not_lt]
    have hN1 : G.rightSize M = 1 := by simp [G, rightSizeFn, hr1, hM_not_lt]
    refine ⟨⟨fun u ↦ by rw [G.card_neighbors, hd1], fun W hW ↦ ?_⟩,
      by simp [hN1, hd1, hr1], by rw [hd1, Nat.cast_one]; exact hbound_ge1⟩
    rw [hr1] at hW
    rcases Nat.eq_zero_or_pos W.card with hW0 | hWpos
    · simp [hW0]
    · obtain ⟨u, hu⟩ := Finset.card_pos.1 hWpos
      let j0 : Fin (G.leftDeg M) := ⟨0, by omega⟩
      have hmem : G.neighborFin M u j0 ∈ bipartiteNeighborSet (G.adj M) W :=
        mem_bipartiteNeighborSet.2 ⟨u, hu, j0, rfl⟩
      have hc : (1 : ℝ) ≤ ((bipartiteNeighborSet (G.adj M) W).card : ℝ) := by
        exact_mod_cast Finset.card_pos.2 ⟨G.neighborFin M u j0, hmem⟩
      rw [show W.card = 1 by omega, hd1]; simp only [Nat.cast_one, mul_one]; linarith
  have hM_not_lt : ¬ M < rFn M := by omega
  obtain ⟨_, _, hexp, hN_le, hd_le⟩ := hmain M (by omega) hrM
  have hd_eq : G.leftDeg M = 2 ^ (execGuvParams p q B M (rFn M)).2.2.1 := by
    simp [G, leftDegFn, hr0, hr1, hM_not_lt]
  have hN_eq : G.rightSize M =
      (2 ^ (execGuvParams p q B M (rFn M)).2.2.1) ^
        ((execGuvParams p q B M (rFn M)).2.2.2.2.1 + 1) := by
    simp [G, rightSizeFn, hr0, hr1, hM_not_lt]
  refine ⟨?_, by rwa [hN_eq, hd_eq], by rwa [hd_eq]⟩
  have hpb := isBipartiteExpander_pullback (c' := (1 - ε) * (G.leftDeg M : ℝ)) hexp
    (fun u : Fin (G.leftSize M) ↦ (u : Fin M)) Function.injective_id
    (finCongr hN_eq.symm) le_rfl (le_of_eq (by rw [hd_eq]))
  have hadj : G.adj M = fun (u : Fin (G.leftSize M)) (v : Fin (G.rightSize M)) ↦
      ∃ j : Fin (2 ^ (execGuvParams p q B M (rFn M)).2.2.1),
        execGuvNeighbor p q B rFn M u.val j.val = ((finCongr hN_eq.symm).symm v).val := by
    funext u v
    apply propext
    rw [G.adj_iff]
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨j.cast hd_eq, hj⟩, fun ⟨j, hj⟩ ↦ ⟨j.cast hd_eq.symm, hj⟩⟩
  refine ⟨fun u ↦ G.card_neighbors M u, ?_⟩
  rw [hadj]
  exact hpb.2

end UniformFamily

end CslibFrontier.ParvareshVardy
