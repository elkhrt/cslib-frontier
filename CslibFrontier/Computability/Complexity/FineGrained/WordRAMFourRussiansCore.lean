/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.WordRAMTableCompilation
import CslibFrontier.Computability.WordRAM.Call
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Core Method-of-Four-Russians Compilation for Fine-Grained Reductions

This module establishes the core Method-of-Four-Russians compilation theorem
(`exponentiallyUpwards_core`) combining a threshold subroutine `nuCode`, `buildBitTableCode`, an
outer fine-grained self-reduction `c_B`, an inner fine-grained reduction `c_A`, and
`bitTableLookupCode` into a faster deterministic Word-RAM decider.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.Complexity.FineGrained

open Cslib.WordRAM CslibFrontier.WordRAM

/-! ### Elementary Real Analysis Helpers -/

private theorem rpow_clamp_le {x d : ℝ} (hx : x = 0 ∨ 1 ≤ x) (_hd : 0 < d) :
    x ^ (1 - d) ≤ x ^ (1 - min d (1 / 2)) + 1 := by
  rcases hx with rfl | hx1
  · by_cases h0 : (1 : ℝ) - d = 0
    · rw [h0, Real.rpow_zero]
      have hpos : 0 ≤ (0 : ℝ) ^ (1 - min d (1 / 2)) := Real.rpow_nonneg le_rfl _
      linarith
    · rw [Real.zero_rpow h0]
      have hpos : 0 ≤ (0 : ℝ) ^ (1 - min d (1 / 2)) := Real.rpow_nonneg le_rfl _
      linarith
  · have hle : 1 - d ≤ 1 - min d (1 / 2) := by
      have := min_le_left d (1 / 2); linarith
    exact (Real.rpow_le_rpow_of_exponent_le hx1 hle).trans (by linarith)

private theorem rpow_lt_one_le {x d : ℝ} (hx : x = 0 ∨ 1 ≤ x) (hd : 0 < d) :
    x ^ (1 - d) ≤ x + 1 := by
  rcases hx with rfl | hx1
  · by_cases h0 : (1 : ℝ) - d = 0
    · rw [h0, Real.rpow_zero]; linarith
    · rw [Real.zero_rpow h0]; linarith
  · calc x ^ (1 - d) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
      _ ≤ x + 1 := by linarith

private theorem linear_le_exp_base {γ : ℝ} (hγ : 1 < γ) (m : ℕ) :
    (18 * m + 30 : ℝ) ≤ (36 / Real.log γ + 30) * (γ ^ (m : ℝ)) ^ (1 / 2 : ℝ) := by
  have hlog : 0 < Real.log γ := Real.log_pos hγ
  have hγ0 : 0 ≤ γ := by linarith
  have hrpow : (γ ^ (m : ℝ)) ^ (1 / 2 : ℝ) = Real.exp ((m : ℝ) * (Real.log γ / 2)) := by
    rw [← Real.rpow_mul hγ0, Real.rpow_def_of_pos (by linarith)]
    congr 1; ring
  rw [hrpow]
  have hexp := Real.add_one_le_exp ((m : ℝ) * (Real.log γ / 2))
  have h1 : 1 ≤ Real.exp ((m : ℝ) * (Real.log γ / 2)) := by
    have : 0 ≤ (m : ℝ) * (Real.log γ / 2) := by positivity
    linarith
  have hm : (m : ℝ) * (Real.log γ / 2) ≤ Real.exp ((m : ℝ) * (Real.log γ / 2)) := by linarith
  have hm_le : (m : ℝ) ≤ (2 / Real.log γ) * Real.exp ((m : ℝ) * (Real.log γ / 2)) := by
    have hmul : (m : ℝ) * (Real.log γ / 2) * (2 / Real.log γ) ≤
        Real.exp ((m : ℝ) * (Real.log γ / 2)) * (2 / Real.log γ) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    have hlhs : (m : ℝ) * (Real.log γ / 2) * (2 / Real.log γ) = (m : ℝ) := by
      field_simp [hlog.ne']
    linarith
  have h18 : (18 : ℝ) * (m : ℝ) ≤
      (36 / Real.log γ) * Real.exp ((m : ℝ) * (Real.log γ / 2)) := by
    have := mul_le_mul_of_nonneg_left hm_le (by norm_num : (0 : ℝ) ≤ 18)
    linarith [show (18 : ℝ) * ((2 / Real.log γ) * Real.exp ((m : ℝ) * (Real.log γ / 2))) =
      (36 / Real.log γ) * Real.exp ((m : ℝ) * (Real.log γ / 2)) by ring]
  have h30 : (30 : ℝ) ≤ 30 * Real.exp ((m : ℝ) * (Real.log γ / 2)) := by linarith
  linarith [show (36 / Real.log γ + 30) * Real.exp ((m : ℝ) * (Real.log γ / 2)) =
    (36 / Real.log γ) * Real.exp ((m : ℝ) * (Real.log γ / 2)) +
      30 * Real.exp ((m : ℝ) * (Real.log γ / 2)) by ring]

theorem nat_log_le_sqrt (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  by_cases hn : n = 0
  · subst hn; simp
  · have hpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hn
    have hlog_le : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      have := Real.log_le_log (by positivity) hpow
      simpa [Real.log_pow] using this
    have hlog_sqrt : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hsq : Real.log ((n : ℝ) ^ (1 / 2 : ℝ)) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        have := Real.add_one_le_exp (Real.log ((n : ℝ) ^ (1 / 2 : ℝ)))
        rw [Real.exp_log (Real.rpow_pos_of_pos hpos _)] at this
        linarith
      rw [Real.log_rpow hpos] at hsq
      linarith
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h; linarith
    nlinarith

private theorem two_pow_le_four_beta_pow {β : ℝ} (hβ : 1 < β) (nu : ℕ) :
    ((2 ^ (nu + 1) : ℕ) : ℝ) * (11 * (nu : ℝ) + 7 * ((⌈β ^ nu⌉₊ : ℕ) : ℝ) + 1) ≤
      (52 : ℝ) * (4 * β) ^ nu := by
  have h1β : 1 ≤ β ^ nu := one_le_pow₀ (by linarith)
  have h4_pow : (4 : ℝ) ^ nu ≤ (4 * β) ^ nu :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith) nu
  have h2β_pow : (2 * β) ^ nu ≤ (4 * β) ^ nu :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) nu
  have hnu_pow : (nu : ℝ) ≤ (2 : ℝ) ^ nu := by
    exact_mod_cast le_of_lt (Nat.lt_two_pow_self (n := nu))
  have hceil : ((⌈β ^ nu⌉₊ : ℕ) : ℝ) ≤ 2 * β ^ nu := by
    have := Nat.ceil_lt_add_one (show 0 ≤ β ^ nu by positivity)
    linarith
  have h2_pow : ((2 ^ (nu + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ nu := by
    push_cast [pow_succ]; ring
  rw [h2_pow]
  have hmul1 : (2 : ℝ) ^ nu * (2 : ℝ) ^ nu = (4 : ℝ) ^ nu := by
    rw [← mul_pow]; norm_num
  have hmul2 : (2 : ℝ) ^ nu * β ^ nu = (2 * β) ^ nu := by rw [mul_pow]
  have h2_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ nu := one_le_pow₀ (by norm_num)
  have hA : (2 : ℝ) ^ nu * (nu : ℝ) ≤ (4 : ℝ) ^ nu := by
    calc (2 : ℝ) ^ nu * (nu : ℝ) ≤ (2 : ℝ) ^ nu * (2 : ℝ) ^ nu :=
          mul_le_mul_of_nonneg_left hnu_pow (by positivity)
      _ = (4 : ℝ) ^ nu := hmul1
  have hB : (2 : ℝ) ^ nu * ((⌈β ^ nu⌉₊ : ℕ) : ℝ) ≤ 2 * (2 * β) ^ nu := by
    calc (2 : ℝ) ^ nu * ((⌈β ^ nu⌉₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ nu * (2 * β ^ nu) :=
          mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = 2 * ((2 : ℝ) ^ nu * β ^ nu) := by ring
      _ = 2 * (2 * β) ^ nu := by rw [hmul2]
  have hC : (2 : ℝ) ^ nu ≤ (4 : ℝ) ^ nu := by
    calc (2 : ℝ) ^ nu = (2 : ℝ) ^ nu * 1 := by ring
      _ ≤ (2 : ℝ) ^ nu * (2 : ℝ) ^ nu := mul_le_mul_of_nonneg_left h2_ge1 (by positivity)
      _ = (4 : ℝ) ^ nu := hmul1
  have hsum : 2 * (2 : ℝ) ^ nu * (11 * (nu : ℝ) + 7 * ((⌈β ^ nu⌉₊ : ℕ) : ℝ) + 1) =
      22 * ((2 : ℝ) ^ nu * (nu : ℝ)) + 14 * ((2 : ℝ) ^ nu * ((⌈β ^ nu⌉₊ : ℕ) : ℝ)) +
        2 * (2 : ℝ) ^ nu := by ring
  linarith

/-! ### Core Method-of-Four-Russians Theorem -/

private theorem fourRussians_hA_on_q {P Q : Set (List Bool)} {p : ℕ → ℝ} {γ a_exp d_A : ℝ}
    {r_A C_A k_A K_γ K_step K_tot W w_log T_tot s t_B : ℕ}
    {c_A : OracleCode .standard r_A} {out_A : Fin r_A} {nu : ℕ → ℕ} {qs_B : List (List ℕ)}
    (hγ : 1 < γ) (hp_int : ∀ n, p n = 0 ∨ 1 ≤ p n) (hp0 : ∀ n, 0 ≤ p n)
    (ha_pos : 0 < a_exp) (ha_lt1 : a_exp < 1) (hd_A : 0 < d_A)
    (hK_γ_ge : (36 / Real.log γ + 30 : ℝ) ≤ (K_γ : ℝ))
    (hK_step : K_step = (7 + K_γ) * C_A + r_A + 50)
    (hk_A_le : 2 * k_A + 3 ≤ K_tot) (h4_le : 4 ≤ K_tot)
    (hW_ge_log : K_tot * (Nat.log 2 (T_tot + s) + 1) ≤ W) (hw_log : w_log = W - 3)
    (hp_sq_le : ⌈p s⌉₊ ≤ (T_tot + s) ^ 2) (ht_B_le_T : t_B ≤ T_tot)
    (hsum_len_B : (qs_B.map fun q => q.length + 1).sum ≤ t_B)
    (hvalid_B : ∀ qi ∈ qs_B, qi ∈ Set.range encBits)
    (hquery_B : ∀ qi ∈ qs_B, ∀ a', encBits a' = qi → p a'.length ≤ (p s) ^ a_exp)
    (hnu_cov : ∀ s', p s' ≤ (p s) ^ a_exp → ∀ m : ℕ,
      (γ ^ (m : ℝ)) ^ (1 / 2 : ℝ) ≤ (C_A : ℝ) * p s' + 2 * (C_A : ℝ) → m ≤ nu s)
    (hA : ∀ (a : List Bool) (w : ℕ),
      logWidth k_A (⌈p a.length⌉₊ + (encBits a).length) ≤ w → InputFits w (encBits a) →
      ∃ y t qs, OracleExec w (oracleOf Q encBits) c_A (.init (encBits a)) y t qs ∧
        y.regs out_A ≤ 1 ∧ (y.regs out_A = 1 ↔ a ∈ P) ∧ (∀ qi ∈ qs, qi ∈ Set.range encBits) ∧
        (t : ℝ) ≤ (C_A : ℝ) * (p a.length) ^ (1 - d_A) + (C_A : ℝ) ∧
        ((qs.map fun qi =>
          (γ ^ (querySize encBits List.length qi)) ^ (1 - (1 / 2 : ℝ))).sum : ℝ) ≤
          (C_A : ℝ) * (p a.length) ^ (1 - d_A) + (C_A : ℝ)) :
    ∀ q ∈ qs_B, ∃ (z' : List Bool) (y_A : Data r_A) (t_A : ℕ) (qs_A : List (List ℕ)),
      encBits z' = q ∧
      OracleExec w_log (oracleOf Q encBits) c_A (.init q) y_A t_A qs_A ∧
      y_A.regs out_A = (oracleOf P encBits q).toNat ∧
      (∀ qi ∈ qs_A, ∃ zq : List Bool, encBits zq = qi ∧ zq.length ≤ nu s) ∧
      11 * q.length + 7 * t_A + (qs_A.map fun qi => (18 * qi.length + 25) + 5).sum + r_A + 20 ≤
        11 * q.length + K_step * ⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ + 2 * K_step := by
  intro q hq
  obtain ⟨z', hz'⟩ := hvalid_B q hq
  have hq_len_le : z'.length ≤ t_B := by
    have h2 : q.length + 1 ≤ (qs_B.map fun q => q.length + 1).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hq)
    rw [← hz', encBits_length] at h2; omega
  have hpz'_le : p z'.length ≤ (p s) ^ a_exp := hquery_B q hq z' hz'
  have hw_log_A : logWidth k_A (⌈p z'.length⌉₊ + (encBits z').length) ≤ w_log := by
    rw [encBits_length]
    have hpz'_le_ps : ⌈p z'.length⌉₊ ≤ ⌈p s⌉₊ := by
      rcases hp_int s with hpz | hp1
      · have h0 : p z'.length = 0 := by
          have hle := hpz'_le
          rw [hpz, Real.zero_rpow ha_pos.ne'] at hle
          exact le_antisymm hle (hp0 _)
        simp [h0, hpz]
      · exact Nat.ceil_mono (hpz'_le.trans
          ((Real.rpow_le_rpow_of_exponent_le hp1 ha_lt1.le).trans (by rw [Real.rpow_one])))
    have hsum_le : ⌈p z'.length⌉₊ + z'.length ≤ ⌈p s⌉₊ + (T_tot + s) := by omega
    have hlog_z' : Nat.log 2 (⌈p z'.length⌉₊ + z'.length) + 1 ≤
        2 * (Nat.log 2 (T_tot + s) + 1) := by
      have hlt0 : T_tot + s < 2 ^ (Nat.log 2 (T_tot + s) + 1) :=
        Nat.lt_pow_succ_log_self Nat.one_lt_two _
      have hlt_sq : ⌈p s⌉₊ + (T_tot + s) < 2 ^ (2 * (Nat.log 2 (T_tot + s) + 1)) := by
        have hm : (T_tot + s) ^ 2 + (T_tot + s) < (2 ^ (Nat.log 2 (T_tot + s) + 1)) ^ 2 := by
          have hle1 : (T_tot + s) + 1 ≤ 2 ^ (Nat.log 2 (T_tot + s) + 1) := hlt0
          have hm1 := Nat.mul_le_mul hle1 hle1
          have he1 : ((T_tot + s) + 1) * ((T_tot + s) + 1) =
              (T_tot + s) ^ 2 + 2 * (T_tot + s) + 1 := by ring
          have he2 : 2 ^ (Nat.log 2 (T_tot + s) + 1) * 2 ^ (Nat.log 2 (T_tot + s) + 1) =
              (2 ^ (Nat.log 2 (T_tot + s) + 1)) ^ 2 := (sq _).symm
          omega
        rw [← pow_mul, mul_comm] at hm; omega
      rcases Nat.eq_zero_or_pos (⌈p z'.length⌉₊ + z'.length) with hz | hpos
      · simp [hz]; omega
      · exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow hpos.ne' (lt_of_le_of_lt hsum_le hlt_sq))
    have h1 : k_A * (Nat.log 2 (⌈p z'.length⌉₊ + z'.length) + 1) ≤
        2 * k_A * (Nat.log 2 (T_tot + s) + 1) := by
      calc k_A * (Nat.log 2 (⌈p z'.length⌉₊ + z'.length) + 1)
          ≤ k_A * (2 * (Nat.log 2 (T_tot + s) + 1)) := Nat.mul_le_mul_left _ hlog_z'
        _ = 2 * k_A * (Nat.log 2 (T_tot + s) + 1) := by ring
    have h2 : (2 * k_A + 3) * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
      (Nat.mul_le_mul_right _ hk_A_le).trans hW_ge_log
    have h3 : 2 * k_A * (Nat.log 2 (T_tot + s) + 1) + 3 ≤
        (2 * k_A + 3) * (Nat.log 2 (T_tot + s) + 1) := by
      rw [Nat.add_mul]
      have := Nat.le_mul_of_pos_right 3 (show 1 ≤ Nat.log 2 (T_tot + s) + 1 by omega)
      omega
    simp only [logWidth, hw_log] at h2 ⊢; omega
  have hfits_z' : InputFits w_log (encBits z') :=
    inputFits_encBits (by
      have hlt_T : z'.length ≤ T_tot := hq_len_le.trans ht_B_le_T
      have h1 : Nat.log 2 z'.length + 1 ≤ Nat.log 2 (T_tot + s) + 1 :=
        Nat.add_le_add_right (Nat.log_mono_right (le_trans hlt_T (Nat.le_add_right _ _))) 1
      have h2 : 4 * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
        (Nat.mul_le_mul_right _ h4_le).trans hW_ge_log
      simp only [logWidth, one_mul, hw_log]; omega)
  obtain ⟨y_A, t_A, qs_A, hex_A, hyA_le, hyA_iff, hvalid_A, ht_A, hsum_A⟩ :=
    hA z' w_log hw_log_A hfits_z'
  have hq_out : y_A.regs out_A = (oracleOf P encBits (encBits z')).toNat := by
    by_cases hzP : z' ∈ P
    · rw [hyA_iff.mpr hzP, (oracleOf_enc P encBits z').mpr hzP]; rfl
    · have hne : y_A.regs out_A ≠ 1 := fun h => hzP (hyA_iff.mp h)
      have h0 : y_A.regs out_A = 0 := by omega
      have hf : oracleOf P encBits (encBits z') = false := by
        cases h : oracleOf P encBits (encBits z')
        · rfl
        · exact absurd ((oracleOf_enc P encBits z').mp h) hzP
      rw [h0, hf]; rfl
  have hA_rpow : (p z'.length) ^ (1 - d_A) ≤ (p z'.length) ^ (1 - min d_A (1 / 2)) + 1 :=
    rpow_clamp_le (hp_int z'.length) hd_A
  have hA_lt1 : (p z'.length) ^ (1 - d_A) ≤ p z'.length + 1 :=
    rpow_lt_one_le (hp_int z'.length) hd_A
  have hA_cov : ∀ qi ∈ qs_A, ∃ zq : List Bool, encBits zq = qi ∧ zq.length ≤ nu s := by
    intro qi hqi
    obtain ⟨zq, rfl⟩ := hvalid_A qi hqi
    refine ⟨zq, rfl, hnu_cov z'.length hpz'_le zq.length ?_⟩
    have hterm : ((γ ^ zq.length) ^ (1 - (1 / 2 : ℝ))) ≤
        (qs_A.map fun r => (γ ^ (querySize encBits List.length r)) ^ (1 - (1 / 2 : ℝ))).sum := by
      have hmem : (γ ^ zq.length) ^ (1 - (1 / 2 : ℝ)) ∈
          qs_A.map (fun r => (γ ^ (querySize encBits List.length r)) ^ (1 - (1 / 2 : ℝ))) :=
        List.mem_map.mpr ⟨encBits zq, hqi, by rw [querySize_enc]⟩
      exact List.single_le_sum (fun x hx => by
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
        exact Real.rpow_nonneg (by positivity) _) _ hmem
    have hpow_eq : (γ ^ (zq.length : ℝ)) ^ (1 / 2 : ℝ) = (γ ^ zq.length) ^ (1 - (1 / 2 : ℝ)) := by
      rw [Real.rpow_natCast]; norm_num
    rw [hpow_eq]
    exact hterm.trans (hsum_A.trans (by
      linarith [mul_le_mul_of_nonneg_left hA_lt1 (by positivity : (0 : ℝ) ≤ C_A)]))
  have hsum_lin_real :
      (((qs_A.map fun qi => (18 * qi.length + 25) + 5).sum : ℕ) : ℝ) ≤
        (K_γ : ℝ) * ((C_A : ℝ) * (p z'.length) ^ (1 - min d_A (1 / 2)) + 2 * (C_A : ℝ)) := by
    have hlist : (((qs_A.map fun qi => (18 * qi.length + 25) + 5).sum : ℕ) : ℝ) ≤
        (K_γ : ℝ) *
          (qs_A.map fun r =>
            (γ ^ (querySize encBits List.length r)) ^ (1 - (1 / 2 : ℝ))).sum := by
      rw [Nat.cast_list_sum, List.map_map, ← List.sum_map_mul_left]
      refine List.sum_le_sum fun qi hqi => ?_
      obtain ⟨zq, rfl, _⟩ := hA_cov qi hqi
      simp only [Function.comp_def, encBits_length, querySize_enc]
      have hlin := linear_le_exp_base hγ zq.length
      have hpow_eq : (γ ^ (zq.length : ℝ)) ^ (1 / 2 : ℝ) =
          (γ ^ zq.length) ^ (1 - (1 / 2 : ℝ)) := by
        rw [Real.rpow_natCast]; norm_num
      have hnn : (0 : ℝ) ≤ (γ ^ zq.length) ^ (1 - (1 / 2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      push_cast; rw [← hpow_eq] at hnn ⊢
      linarith [mul_le_mul_of_nonneg_right hK_γ_ge hnn]
    have hsum_A' : (qs_A.map fun r => (γ ^ (querySize encBits List.length r)) ^
        (1 - (1 / 2 : ℝ))).sum ≤
        (C_A : ℝ) * (p z'.length) ^ (1 - min d_A (1 / 2)) + 2 * (C_A : ℝ) :=
      hsum_A.trans (by
        linarith [mul_le_mul_of_nonneg_left hA_rpow (by positivity : (0 : ℝ) ≤ C_A)])
    exact hlist.trans (mul_le_mul_of_nonneg_left hsum_A' (by positivity))
  have htime_real :
      ((7 * t_A + (qs_A.map fun qi => (18 * qi.length + 25) + 5).sum + r_A + 20 : ℕ) : ℝ) ≤
        ((K_step * ⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ + 2 * K_step : ℕ) : ℝ) := by
    have hceil_z' : (p z'.length) ^ (1 - min d_A (1 / 2)) ≤
        (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) := Nat.le_ceil _
    have hK_eq : (K_step : ℝ) = (7 + (K_γ : ℝ)) * (C_A : ℝ) + (r_A : ℝ) + 50 := by
      rw [hK_step]; push_cast; ring
    have htA' : (t_A : ℝ) ≤
        (C_A : ℝ) * (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) + 2 * (C_A : ℝ) :=
      ht_A.trans (by
        linarith [mul_le_mul_of_nonneg_left (hA_rpow.trans (add_le_add hceil_z' le_rfl))
          (by positivity : (0 : ℝ) ≤ C_A)])
    have hsum' : (((qs_A.map fun qi => (18 * qi.length + 25) + 5).sum : ℕ) : ℝ) ≤
        (K_γ : ℝ) *
          ((C_A : ℝ) * (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) + 2 * (C_A : ℝ)) :=
      hsum_lin_real.trans (mul_le_mul_of_nonneg_left
        (by linarith [mul_le_mul_of_nonneg_left hceil_z' (by positivity : (0 : ℝ) ≤ C_A)])
        (by positivity))
    have hKmul : ((r_A : ℝ) + 50) * (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) ≥ 0 := by
      positivity
    have halg : (K_step : ℝ) * (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) +
          2 * (K_step : ℝ) =
        (7 + (K_γ : ℝ)) *
          ((C_A : ℝ) * (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) + 2 * (C_A : ℝ)) +
          ((r_A : ℝ) + 50) * (⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ : ℝ) +
          2 * ((r_A : ℝ) + 50) := by
      rw [hK_eq]; ring
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [htA', hsum', hKmul, halg]
  have htime_nat :
      7 * t_A + (qs_A.map fun qi => (18 * qi.length + 25) + 5).sum + r_A + 20 ≤
        K_step * ⌈(p z'.length) ^ (1 - min d_A (1 / 2))⌉₊ + 2 * K_step := by
    exact_mod_cast htime_real
  refine ⟨z', y_A, t_A, qs_A, hz', hz' ▸ hex_A, hz' ▸ hq_out, hA_cov, by omega⟩

private theorem fourRussians_stage012_exec {r_nu r_Q r_B r_A W w_log H T_nu T_Q : ℕ}
    {Q : Set (List Bool)} {nu : ℕ → ℕ}
    {nuCode : Code .standard (r_nu + 2)} {c_Q : Code .standard r_Q} {out_Q : Fin r_Q}
    {c_B : OracleCode .standard r_B} {out_B : Fin r_B}
    {c_A : OracleCode .standard r_A} {out_A : Fin r_A}
    {z : List Bool} {tail : Code .standard
      (8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3)))}
    {t_tail out_val : ℕ}
    (hw_log : w_log = W - 3) (hW_ge : 8 ≤ W) (hH : H = 2 ^ w_log)
    (h6H : Fits W (6 * H)) (hpow_nu : 2 ^ (nu z.length + 1) ≤ H)
    (hs_lt : z.length + 1 < H) (hrf_Q : c_Q.IsRandFree)
    (hnu_exec : ∀ x : Data (r_nu + 2), x.regs 0 = z.length →
      ∃ y : Data (r_nu + 2), ExecWithin W nuCode x y T_nu ∧
        y.regs 1 = nu z.length ∧ y.mem = x.mem)
    (hQ_tab : ∀ zq : List Bool, zq.length ≤ nu z.length →
      c_Q.Answers out_Q w_log (encBits zq) (zq ∈ Q) T_Q)
    (htail : ∀ x18 : Data (8 + (r_nu + 2) + (r_Q + 26) +
        ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))),
      x18.regs ⟨0, by omega⟩ = H →
      x18.regs ⟨1, by omega⟩ = w_log →
      (∀ k, x18.regs (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) k) = 0) →
      x18.mem (6 * H) = nu z.length →
      (∀ a < H, x18.mem a = (Data.init (encBits z) (r :=
        8 + (r_nu + 2) + (r_Q + 26) +
          ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3)))).mem a) →
      (∀ a < H, x18.mem (2 * H + 2 * a) = 0) →
      (∀ zq : List Bool, zq.length ≤ nu z.length →
        x18.mem (H + bitStringCode zq) = (oracleOf Q encBits (encBits zq)).toNat) →
      ∃ y_final : Data (8 + (r_nu + 2) + (r_Q + 26) +
          ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))),
        ExecWithin W tail x18 y_final t_tail ∧ y_final.regs ⟨6, by omega⟩ = out_val)
    (hprog_eq : fourRussiansProg nuCode c_Q out_Q c_B out_B c_A out_A =
      .seq (.seq (.op (.alu .width ⟨1, by omega⟩ ![]))
        (.seq (.op (.const ⟨5, by omega⟩ 3))
          (.seq (.op (.bin .sub ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨5, by omega⟩))
            (.seq (.op (.const ⟨5, by omega⟩ 1))
              (.seq (.op (.bin .shiftLeft ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨1, by omega⟩))
                (.seq (.op (.const ⟨4, by omega⟩ 0))
                  (.op (.load ⟨2, by omega⟩ ⟨4, by omega⟩))))))))
        (.seq (.op (.copy (frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) 0)
            ⟨2, by omega⟩))
          (.seq (nuCode.rename (frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)))
            (.seq (.op (.copy ⟨3, by omega⟩
                (frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) 1)))
              (.seq (.seq (.op (.bin .add ⟨4, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩))
                  (.seq (.op (.bin .add ⟨5, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩))
                    (.seq (.op (.bin .add ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨5, by omega⟩))
                      (.op (.store ⟨4, by omega⟩ ⟨3, by omega⟩)))))
                (.seq (.op (.copy (frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
                    ⟨0, by omega⟩) ⟨0, by omega⟩))
                  (.seq (.op (.copy (frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B)
                      (r_A := r_A) ⟨1, by omega⟩) ⟨1, by omega⟩))
                    (.seq (.op (.copy (frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B)
                        (r_A := r_A) ⟨2, by omega⟩) ⟨3, by omega⟩))
                      (.seq ((buildBitTableCode c_Q out_Q).rename
                          (frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)))
                        tail))))))))) :
    ∃ y_final : Data (8 + (r_nu + 2) + (r_Q + 26) +
        ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))),
      ExecWithin W (fourRussiansProg nuCode c_Q out_Q c_B out_B c_A out_A)
        (.init (encBits z)) y_final
        (7 + (1 + T_nu + 1 + 4) +
          (1 + 1 + 1 +
            (2 ^ (nu z.length + 1) * (11 * nu z.length + 7 * T_Q + r_Q + 40) + 20)) +
          t_tail) ∧
      y_final.regs ⟨6, by omega⟩ = out_val := by
  let rTot := 8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))
  let x0 : Data rTot := .init (encBits z)
  let nuReg := frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  let buildReg := frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  let compReg := frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  have h3_fits : Fits W 3 := show 3 < 2 ^ W by
    have : 2 ^ 3 ≤ 2 ^ W := Nat.pow_le_pow_right Nat.two_pos (by omega); norm_num at this; omega
  have h1_fits : Fits W 1 := Fits.of_le h3_fits (by omega)
  have hw_fits : Fits W w_log := Fits.of_le (fits_self W) (by omega)
  have hH_fits : Fits W H := Fits.of_le h6H (by omega)
  have h2H_fits : Fits W (2 * H) := Fits.of_le h6H (by omega)
  have h4H_fits : Fits W (4 * H) := Fits.of_le h6H (by omega)
  let x1 := x0.set ⟨1, by omega⟩ W
  let x2 := x1.set ⟨5, by omega⟩ 3
  let x3 := x2.set ⟨1, by omega⟩ w_log
  let x4 := x3.set ⟨5, by omega⟩ 1
  let x5 := x4.set ⟨0, by omega⟩ H
  let x6 := x5.set ⟨4, by omega⟩ 0
  let x7 := x6.set ⟨2, by omega⟩ z.length
  have hne51 : (⟨5, by omega⟩ : Fin rTot) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne15 : (⟨1, by omega⟩ : Fin rTot) ≠ ⟨5, by omega⟩ := hne51.symm
  have hne40 : (⟨4, by omega⟩ : Fin rTot) ≠ ⟨0, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne45 : (⟨4, by omega⟩ : Fin rTot) ≠ ⟨5, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne54 : (⟨5, by omega⟩ : Fin rTot) ≠ ⟨4, by omega⟩ := hne45.symm
  have hne34 : (⟨3, by omega⟩ : Fin rTot) ≠ ⟨4, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne35 : (⟨3, by omega⟩ : Fin rTot) ≠ ⟨5, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne02 : (⟨0, by omega⟩ : Fin rTot) ≠ ⟨2, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne04 : (⟨0, by omega⟩ : Fin rTot) ≠ ⟨4, by omega⟩ := hne40.symm
  have hne12 : (⟨1, by omega⟩ : Fin rTot) ≠ ⟨2, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne14 : (⟨1, by omega⟩ : Fin rTot) ≠ ⟨4, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hne10 : (⟨1, by omega⟩ : Fin rTot) ≠ ⟨0, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have hs0 : ExecWithin (B := .standard) W
      (.seq (.op (.alu .width ⟨1, by omega⟩ ![]))
        (.seq (.op (.const ⟨5, by omega⟩ 3))
          (.seq (.op (.bin .sub ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨5, by omega⟩))
            (.seq (.op (.const ⟨5, by omega⟩ 1))
              (.seq (.op (.bin .shiftLeft ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨1, by omega⟩))
                (.seq (.op (.const ⟨4, by omega⟩ 0))
                  (.op (.load ⟨2, by omega⟩ ⟨4, by omega⟩)))))))) x0 x7 7 := by
    have e1 : ExecWithin (B := .standard) W (.op (.alu .width ⟨1, by omega⟩ _)) x0 x1 1 :=
      ExecWithin.width
    have e2 : ExecWithin (B := .standard) W (.op (.const ⟨5, by omega⟩ 3)) x1 x2 1 :=
      ExecWithin.const h3_fits
    have hx2_1 : x2.regs ⟨1, by omega⟩ = W := by
      simp only [x2, x1, Data.set_regs, Function.update_of_ne hne15, Function.update_self]
    have hx2_5 : x2.regs ⟨5, by omega⟩ = 3 := by
      simp only [x2, Data.set_regs, Function.update_self]
    have e3 : ExecWithin (B := .standard) W
        (.op (.bin .sub ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨5, by omega⟩)) x2 x3 1 := by
      have hsub : W - 3 = w_log := hw_log.symm
      have hb := ExecWithin.bin (w := W) (x := x2) (f := .sub)
        (d := ⟨1, by omega⟩) (i := ⟨1, by omega⟩) (j := ⟨5, by omega⟩)
        (by rw [hx2_1, hx2_5]; dsimp only [BinOp.eval]; rw [hsub]; exact hw_fits)
      simpa only [BinOp.eval, hx2_1, hx2_5, hsub] using hb
    have e4 : ExecWithin (B := .standard) W (.op (.const ⟨5, by omega⟩ 1)) x3 x4 1 :=
      ExecWithin.const h1_fits
    have hx4_5 : x4.regs ⟨5, by omega⟩ = 1 := by
      simp only [x4, Data.set_regs, Function.update_self]
    have hx4_1 : x4.regs ⟨1, by omega⟩ = w_log := by
      simp only [x4, x3, Data.set_regs, Function.update_of_ne hne15, Function.update_self]
    have e5 : ExecWithin (B := .standard) W
        (.op (.bin .shiftLeft ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨1, by omega⟩)) x4 x5 1 := by
      have hsh : 1 <<< w_log = H := by rw [Nat.shiftLeft_eq, one_mul, hH]
      have hb := ExecWithin.bin (w := W) (x := x4) (f := .shiftLeft)
        (d := ⟨0, by omega⟩) (i := ⟨5, by omega⟩) (j := ⟨1, by omega⟩)
        (by rw [hx4_5, hx4_1]; dsimp only [BinOp.eval]; rw [hsh]; exact hH_fits)
      simpa only [BinOp.eval, hx4_5, hx4_1, hsh] using hb
    have e6 : ExecWithin (B := .standard) W (.op (.const ⟨4, by omega⟩ 0)) x5 x6 1 :=
      ExecWithin.const (fits_zero W)
    have e7 : ExecWithin (B := .standard) W (.op (.load ⟨2, by omega⟩ ⟨4, by omega⟩)) x6 x7 1 := by
      have hx6_4 : x6.regs ⟨4, by omega⟩ = 0 := by
        simp only [x6, Data.set_regs, Function.update_self]
      have hm0 : x6.mem 0 = z.length := by
        simp only [x6, x5, x4, x3, x2, x1, x0, Data.set_mem, Data.init_mem_zero, encBits_length]
      have hl : ExecWithin (B := .standard) W (.op (.load ⟨2, by omega⟩ ⟨4, by omega⟩)) x6
          (x6.set ⟨2, by omega⟩ (x6.mem (x6.regs ⟨4, by omega⟩))) 1 := ExecWithin.load
      simpa only [hx6_4, hm0] using hl
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  let x8 := x7.set (nuReg 0) (x7.regs ⟨2, by omega⟩)
  have hx8_0 : (x8.comap nuReg).regs 0 = z.length := by
    simp only [Data.comap_regs, x8, x7, Data.set_regs, Function.update_self]
  obtain ⟨nu_out, hnu_out, hnu_1, hnu_mem⟩ := hnu_exec (x8.comap nuReg) hx8_0
  obtain ⟨x9, hx9, hx9_eq, hx9_fr⟩ :=
    ExecWithin.rename_post frNuReg_injective ⟨nu_out, hnu_out, rfl⟩
  have hx9_mem : x9.mem = x0.mem := (congrArg Data.mem hx9_eq.symm).trans hnu_mem
  have hx9_low : ∀ j : Fin rTot, j.val < 8 → x9.regs j = x7.regs j := fun j hj => by
    have hne : ∀ k : Fin (r_nu + 2), nuReg k ≠ j := fun k h => by
      have := congrArg Fin.val h; simp only [nuReg, frNuReg_val] at this; omega
    have h8j : x8.regs j = x7.regs j := by
      simp only [x8, Data.set_regs, Function.update_of_ne (hne 0).symm]
    exact (hx9_fr j hne).trans h8j
  have hx9_comp : ∀ k, x9.regs (compReg k) = 0 := fun k => by
    have hne : ∀ j : Fin (r_nu + 2), nuReg j ≠ compReg k := fun j h => by
      have := congrArg Fin.val h; simp only [nuReg, compReg, frNuReg_val, frCompReg_val] at this
      omega
    have hne_low : ∀ j : Fin rTot, j.val < 8 → compReg k ≠ j := fun j hj =>
      Fin.ne_of_val_ne (by simp only [compReg, frCompReg_val]; omega)
    rw [hx9_fr _ hne]
    simp only [x8, x7, x6, x5, x4, x3, x2, x1, x0, Data.set_regs,
      Function.update_of_ne (hne 0).symm,
      Function.update_of_ne (hne_low ⟨2, by omega⟩ (by simp)),
      Function.update_of_ne (hne_low ⟨4, by omega⟩ (by simp)),
      Function.update_of_ne (hne_low ⟨0, by omega⟩ (by simp)),
      Function.update_of_ne (hne_low ⟨5, by omega⟩ (by simp)),
      Function.update_of_ne (hne_low ⟨1, by omega⟩ (by simp)), Data.init_regs]
  let x10 := x9.set ⟨3, by omega⟩ (x9.regs (nuReg 1))
  have hx10_3 : x10.regs ⟨3, by omega⟩ = nu z.length := by
    have := congrFun (congrArg Data.regs hx9_eq.symm) 1
    simp only [x10, Data.set_regs, Function.update_self]
    exact (show x9.regs (nuReg 1) = nu_out.regs 1 from this).trans hnu_1
  let x11 := x10.set ⟨4, by omega⟩ (2 * H)
  let x12 := x11.set ⟨5, by omega⟩ (4 * H)
  let x13 := x12.set ⟨4, by omega⟩ (6 * H)
  let x14 := x13.write (6 * H) (nu z.length)
  have hx10_0 : x10.regs ⟨0, by omega⟩ = H := by
    have hne03 : (⟨0, by omega⟩ : Fin rTot) ≠ ⟨3, by omega⟩ := Fin.ne_of_val_ne (by simp)
    simp only [x10, Data.set_regs, Function.update_of_ne hne03, hx9_low ⟨0, by omega⟩ (by simp),
      x7, x6, x5, Function.update_of_ne hne02, Function.update_of_ne hne04, Function.update_self]
  have hstoreNu : ExecWithin (B := .standard) W
      (.seq (.op (.bin .add ⟨4, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩))
        (.seq (.op (.bin .add ⟨5, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩))
          (.seq (.op (.bin .add ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨5, by omega⟩))
            (.op (.store ⟨4, by omega⟩ ⟨3, by omega⟩))))) x10 x14 4 := by
    have e1 : ExecWithin (B := .standard) W
        (.op (.bin .add ⟨4, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)) x10 x11 1 := by
      have ha : H + H = 2 * H := by omega
      have hb := ExecWithin.bin (w := W) (x := x10) (f := .add)
        (d := ⟨4, by omega⟩) (i := ⟨0, by omega⟩) (j := ⟨0, by omega⟩)
        (by rw [hx10_0]; dsimp only [BinOp.eval]; rw [ha]; exact h2H_fits)
      simpa only [BinOp.eval, hx10_0, ha] using hb
    have hx11_4 : x11.regs ⟨4, by omega⟩ = 2 * H := by
      simp only [x11, Data.set_regs, Function.update_self]
    have e2 : ExecWithin (B := .standard) W
        (.op (.bin .add ⟨5, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩)) x11 x12 1 := by
      have ha : 2 * H + 2 * H = 4 * H := by omega
      have hb := ExecWithin.bin (w := W) (x := x11) (f := .add)
        (d := ⟨5, by omega⟩) (i := ⟨4, by omega⟩) (j := ⟨4, by omega⟩)
        (by rw [hx11_4]; dsimp only [BinOp.eval]; rw [ha]; exact h4H_fits)
      simpa only [BinOp.eval, hx11_4, ha] using hb
    have hx12_4 : x12.regs ⟨4, by omega⟩ = 2 * H := by
      simp only [x12, Data.set_regs, Function.update_of_ne hne45, hx11_4]
    have hx12_5 : x12.regs ⟨5, by omega⟩ = 4 * H := by
      simp only [x12, Data.set_regs, Function.update_self]
    have e3 : ExecWithin (B := .standard) W
        (.op (.bin .add ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨5, by omega⟩)) x12 x13 1 := by
      have ha : 2 * H + 4 * H = 6 * H := by omega
      have hb := ExecWithin.bin (w := W) (x := x12) (f := .add)
        (d := ⟨4, by omega⟩) (i := ⟨4, by omega⟩) (j := ⟨5, by omega⟩)
        (by rw [hx12_4, hx12_5]; dsimp only [BinOp.eval]; rw [ha]; exact h6H)
      simpa only [BinOp.eval, hx12_4, hx12_5, ha] using hb
    have hx13_4 : x13.regs ⟨4, by omega⟩ = 6 * H := by
      simp only [x13, Data.set_regs, Function.update_self]
    have hx13_3 : x13.regs ⟨3, by omega⟩ = nu z.length := by
      simp only [x13, x12, x11, Data.set_regs, Function.update_of_ne hne34,
        Function.update_of_ne hne35, hx10_3]
    have e4 : ExecWithin (B := .standard) W
        (.op (.store ⟨4, by omega⟩ ⟨3, by omega⟩)) x13 x14 1 := by
      have hs : ExecWithin (B := .standard) W (.op (.store ⟨4, by omega⟩ ⟨3, by omega⟩)) x13
          (x13.write (x13.regs ⟨4, by omega⟩) (x13.regs ⟨3, by omega⟩)) 1 := ExecWithin.store
      simpa only [hx13_4, hx13_3] using hs
    exact (e1.seq (e2.seq (e3.seq e4))).mono (by omega)
  let x15 := x14.set (buildReg ⟨0, by omega⟩) (x14.regs ⟨0, by omega⟩)
  let x16 := x15.set (buildReg ⟨1, by omega⟩) (x15.regs ⟨1, by omega⟩)
  let x17 := x16.set (buildReg ⟨2, by omega⟩) (x16.regs ⟨3, by omega⟩)
  have hx14_0 : x14.regs ⟨0, by omega⟩ = H := by
    have hne05 : (⟨0, by omega⟩ : Fin rTot) ≠ ⟨5, by omega⟩ := Fin.ne_of_val_ne (by simp)
    simp only [x14, x13, x12, x11, Data.write_regs, Data.set_regs, Function.update_of_ne hne04,
      Function.update_of_ne hne05, hx10_0]
  have hx14_1 : x14.regs ⟨1, by omega⟩ = w_log := by
    have hne13 : (⟨1, by omega⟩ : Fin rTot) ≠ ⟨3, by omega⟩ := Fin.ne_of_val_ne (by simp)
    simp only [x14, x13, x12, x11, x10, Data.write_regs, Data.set_regs,
      Function.update_of_ne hne14, Function.update_of_ne hne15, Function.update_of_ne hne13,
      hx9_low ⟨1, by omega⟩ (by simp), x7, x6, x5, x4, x3, Function.update_of_ne hne12,
      Function.update_of_ne hne10, Function.update_self]
  have hx14_3 : x14.regs ⟨3, by omega⟩ = nu z.length := by
    simp only [x14, x13, x12, x11, Data.write_regs, Data.set_regs, Function.update_of_ne hne34,
      Function.update_of_ne hne35, hx10_3]
  have hneB01 : buildReg ⟨0, by omega⟩ ≠ buildReg ⟨1, by omega⟩ :=
    frBuildReg_injective.ne (Fin.ne_of_val_ne (by simp))
  have hneB02 : buildReg ⟨0, by omega⟩ ≠ buildReg ⟨2, by omega⟩ :=
    frBuildReg_injective.ne (Fin.ne_of_val_ne (by simp))
  have hneB12 : buildReg ⟨1, by omega⟩ ≠ buildReg ⟨2, by omega⟩ :=
    frBuildReg_injective.ne (Fin.ne_of_val_ne (by simp))
  have hneB_low : ∀ (k : Fin (r_Q + 26)) (j : Fin rTot), j.val < 8 → buildReg k ≠ j :=
    fun k j hj => Fin.ne_of_val_ne (by simp only [buildReg, frBuildReg_val]; omega)
  have hx17_0 : (x17.comap buildReg).regs ⟨0, by omega⟩ = H := by
    simp only [Data.comap_regs, x17, x16, x15, Data.set_regs,
      Function.update_of_ne hneB02, Function.update_of_ne hneB01, Function.update_self, hx14_0]
  have hx17_1 : (x17.comap buildReg).regs ⟨1, by omega⟩ = w_log := by
    simp only [Data.comap_regs, x17, x16, x15, Data.set_regs,
      Function.update_of_ne hneB12, Function.update_self,
      Function.update_of_ne (hneB_low ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)).symm, hx14_1]
  have hx17_2 : (x17.comap buildReg).regs ⟨2, by omega⟩ = nu z.length := by
    simp only [Data.comap_regs, x17, x16, x15, Data.set_regs,
      Function.update_self,
      Function.update_of_ne (hneB_low ⟨1, by omega⟩ ⟨3, by omega⟩ (by simp)).symm,
      Function.update_of_ne (hneB_low ⟨0, by omega⟩ ⟨3, by omega⟩ (by simp)).symm, hx14_3]
  have hst4_0 : StampLe (4 * H) H 0 (x17.comap buildReg).mem := by
    intro a _
    have hne : 4 * H + 2 * a ≠ 6 * H := by omega
    have hm : (x17.comap buildReg).mem (4 * H + 2 * a) = x0.mem (4 * H + 2 * a) := by
      simp only [Data.comap_mem, x17, x16, x15, x14, x13, x12, x11, x10, Data.set_mem,
        Data.write_mem, Function.update_of_ne hne, hx9_mem]
    rw [hm]
    obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero (show 4 * H + 2 * a ≠ 0 by omega)
    rw [hm', Data.init_mem_succ]; simp [show ¬(m < z.length) by omega]
  obtain ⟨bt_out, hbt_out, hbt_tab, hbt_lo, hbt_mid, hbt_6H⟩ :=
    buildBitTableCode_exec (W := W) (w_log := w_log) (H := H) (nu := nu z.length)
      (T_max := T_Q) (x := x17.comap buildReg)
      hrf_Q hH (le_of_lt h6H) hpow_nu hx17_0 hx17_1 hx17_2 hQ_tab hst4_0
  obtain ⟨x18, hx18, hx18_eq, hx18_fr⟩ :=
    ExecWithin.rename_post frBuildReg_injective ⟨bt_out, hbt_out, rfl⟩
  have hx18_mem : x18.mem = bt_out.mem := congrArg Data.mem hx18_eq.symm
  have hx18_0 : x18.regs ⟨0, by omega⟩ = H := by
    have hne : ∀ j, buildReg j ≠ ⟨0, by omega⟩ := fun j => hneB_low j ⟨0, by omega⟩ (by simp)
    rw [hx18_fr _ hne]
    simp only [x17, x16, x15, Data.set_regs, Function.update_of_ne (hne _).symm, hx14_0]
  have hx18_1 : x18.regs ⟨1, by omega⟩ = w_log := by
    have hne : ∀ j, buildReg j ≠ ⟨1, by omega⟩ := fun j => hneB_low j ⟨1, by omega⟩ (by simp)
    rw [hx18_fr _ hne]
    simp only [x17, x16, x15, Data.set_regs, Function.update_of_ne (hne _).symm, hx14_1]
  have hx18_comp : ∀ k, x18.regs (compReg k) = 0 := fun k => by
    have hneB : ∀ j : Fin (r_Q + 26), buildReg j ≠ compReg k := fun j h => by
      have := congrArg Fin.val h
      simp only [buildReg, compReg, frBuildReg_val, frCompReg_val] at this
      omega
    have hne_low : ∀ j : Fin rTot, j.val < 8 → compReg k ≠ j := fun j hj =>
      Fin.ne_of_val_ne (by simp only [compReg, frCompReg_val]; omega)
    rw [hx18_fr _ hneB]
    simp only [x17, x16, x15, x14, x13, x12, x11, x10, Data.write_regs, Data.set_regs,
      Function.update_of_ne (hneB _).symm,
      Function.update_of_ne (hne_low ⟨4, by omega⟩ (by simp)),
      Function.update_of_ne (hne_low ⟨5, by omega⟩ (by simp)),
      Function.update_of_ne (hne_low ⟨3, by omega⟩ (by simp)), hx9_comp k]
  have hx18_6H : x18.mem (6 * H) = nu z.length := by
    rw [hx18_mem, hbt_6H]
    simp only [Data.comap_mem, x17, x16, x15, x14, Data.set_mem, Data.write_mem,
      Function.update_self]
  have hx18_lo : ∀ a < H, x18.mem a = x0.mem a := fun a ha => by
    rw [hx18_mem, hbt_lo a ha]
    have hne : a ≠ 6 * H := by omega
    simp only [Data.comap_mem, x17, x16, x15, x14, x13, x12, x11, x10, Data.set_mem,
      Data.write_mem, Function.update_of_ne hne, hx9_mem]
  have hx18_mid : ∀ a < H, x18.mem (2 * H + 2 * a) = 0 := fun a ha => by
    rw [hx18_mem, hbt_mid _ (by omega) (by omega)]
    have hne : 2 * H + 2 * a ≠ 6 * H := by omega
    have hm : (x17.comap buildReg).mem (2 * H + 2 * a) = x0.mem (2 * H + 2 * a) := by
      simp only [Data.comap_mem, x17, x16, x15, x14, x13, x12, x11, x10, Data.set_mem,
        Data.write_mem, Function.update_of_ne hne, hx9_mem]
    rw [hm]
    obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero (show 2 * H + 2 * a ≠ 0 by omega)
    rw [hm', Data.init_mem_succ]; simp [show ¬(m < z.length) by omega]
  have hx18_tab : ∀ zq : List Bool, zq.length ≤ nu z.length →
      x18.mem (H + bitStringCode zq) = (oracleOf Q encBits (encBits zq)).toNat := fun zq hzq => by
    rw [hx18_mem]; exact hbt_tab zq hzq
  obtain ⟨y_final, htail_ex, hy_out⟩ :=
    htail x18 hx18_0 hx18_1 hx18_comp hx18_6H hx18_lo hx18_mid hx18_tab
  rw [hprog_eq]
  exact ⟨y_final,
    (hs0.seq (ExecWithin.copy.seq (hx9.seq (ExecWithin.copy.seq (hstoreNu.seq
      (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
        (hx18.seq htail_ex))))))))).mono (by omega),
    hy_out⟩

private theorem fourRussians_stage3_exec {r_nu r_Q r_B r_A W w_log H T_tot K_tot t_B : ℕ}
    {P Q : Set (List Bool)} {nu : ℕ → ℕ}
    {c_B : OracleCode .standard r_B} {out_B : Fin r_B}
    {c_A : OracleCode .standard r_A} {out_A : Fin r_A}
    {z : List Bool} {y_B : Data r_B} {qs_B : List (List ℕ)}
    {T_wso : List ℕ → ℕ}
    {x18 : Data (8 + (r_nu + 2) + (r_Q + 26) +
      ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3)))}
    (hw_log : w_log = W - 3) (hW_ge : 8 ≤ W) (hH : H = 2 ^ w_log)
    (h6H : Fits W (6 * H)) (hpow_nu : 2 ^ (nu z.length + 1) ≤ H)
    (h4K : 4 ≤ K_tot) (hW_ge_log : K_tot * (Nat.log 2 (T_tot + z.length) + 1) ≤ W)
    (ht_B_le_T : t_B ≤ T_tot) (hfits_z : InputFits w_log (encBits z))
    (hex_B : OracleExec w_log (oracleOf P encBits) c_B (.init (encBits z)) y_B t_B qs_B)
    (hA_on_q : ∀ q ∈ qs_B, ∃ (z' : List Bool) (y_A : Data r_A) (t_A : ℕ) (qs_A : List (List ℕ)),
      encBits z' = q ∧
      OracleExec w_log (oracleOf Q encBits) c_A (.init q) y_A t_A qs_A ∧
      y_A.regs out_A = (oracleOf P encBits q).toNat ∧
      (∀ qi ∈ qs_A, ∃ zq : List Bool, encBits zq = qi ∧ zq.length ≤ nu z.length) ∧
      11 * q.length + 7 * t_A + (qs_A.map fun qi => (18 * qi.length + 25) + 5).sum + r_A + 20 ≤
        T_wso q)
    (hx18_0 : x18.regs ⟨0, by omega⟩ = H)
    (hx18_1 : x18.regs ⟨1, by omega⟩ = w_log)
    (hx18_comp : ∀ k,
      x18.regs (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) k) = 0)
    (hx18_6H : x18.mem (6 * H) = nu z.length)
    (hx18_lo : ∀ a < H, x18.mem a = (Data.init (encBits z) (r :=
      8 + (r_nu + 2) + (r_Q + 26) +
        ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3)))).mem a)
    (hx18_mid : ∀ a < H, x18.mem (2 * H + 2 * a) = 0)
    (hx18_tab : ∀ zq : List Bool, zq.length ≤ nu z.length →
      x18.mem (H + bitStringCode zq) = (oracleOf Q encBits (encBits zq)).toNat) :
    ∃ y_final : Data (8 + (r_nu + 2) + (r_Q + 26) +
        ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))),
      ExecWithin W
        (.seq (.op (.copy (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
            callerWidthReg) ⟨1, by omega⟩))
          (.seq (.op (.copy (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
              (subReg ⟨3, by omega⟩)) ⟨0, by omega⟩))
            (.seq (.op (.copy (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
                (subReg ⟨4, by omega⟩)) ⟨1, by omega⟩))
              (.seq ((compileOracle c_B (wrapStampedOracle c_A out_A bitTableLookupCode)).rename
                  (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)))
                (.op (.copy ⟨6, by omega⟩ (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B)
                  (r_A := r_A) (callerReg out_B))))))))
        x18 y_final (1 + 1 + 1 + (t_B + (qs_B.map fun q => T_wso q + 3).sum) + 1) ∧
      y_final.regs ⟨6, by omega⟩ = y_B.regs out_B := by
  let rTot := 8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))
  let compReg := frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  let subA := wrapStampedOracle c_A out_A bitTableLookupCode
  let x19 := x18.set (compReg callerWidthReg) (x18.regs ⟨1, by omega⟩)
  let x20 := x19.set (compReg (subReg ⟨3, by omega⟩)) (x19.regs ⟨0, by omega⟩)
  let x21 := x20.set (compReg (subReg ⟨4, by omega⟩)) (x20.regs ⟨1, by omega⟩)
  have hqsB_le_tB : qs_B.length ≤ t_B := hex_B.length_queries_le
  have hW_ne : ∀ j : Fin (((r_A + 6) + (16 + 5) + 18) + 3),
      (callerWidthReg (r_c := r_B) (r_s := ((r_A + 6) + (16 + 5) + 18) + 3)) ≠ subReg j :=
    fun j => callerWidthReg_ne_subReg j
  have hsub_ne : ∀ {a b : Fin (((r_A + 6) + (16 + 5) + 18) + 3)}, a.val ≠ b.val →
      (subReg a : Fin ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) ≠ subReg b :=
    fun hab h => hab (congrArg Fin.val (subReg_injective h))
  have hlow_ne : ∀ (a : Fin rTot) (k : Fin ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))),
      a.val < 8 → a ≠ frCompReg k :=
    fun a k ha => Fin.ne_of_val_ne (by simp only [frCompReg_val]; omega)
  let Inv (mem : ℕ → ℕ) (rs : Fin (((r_A + 6) + (16 + 5) + 18) + 3) → ℕ) (k : ℕ) : Prop :=
    rs ⟨3, by omega⟩ = H ∧ rs ⟨4, by omega⟩ = w_log ∧ rs ⟨5, by omega⟩ + k ≤ qs_B.length ∧
      StampLe (2 * H) H (rs ⟨5, by omega⟩) mem ∧
      mem (6 * H) = nu z.length ∧
      (∀ zq : List Bool, zq.length ≤ nu z.length →
        mem (H + bitStringCode zq) = (oracleOf Q encBits (encBits zq)).toNat)
  have hInv0 : Inv (x21.comap compReg).mem ((x21.comap compReg).regs ∘ subReg) qs_B.length := by
    have h5_0 : ((x21.comap compReg).regs ∘ subReg) ⟨5, by omega⟩ = 0 := by
      dsimp only [Function.comp_apply, Data.comap_regs, x21, x20, x19, compReg]
      simp only [Data.set_regs,
        Function.update_of_ne (frCompReg_injective.ne (hsub_ne (a := ⟨4, by omega⟩)
          (b := ⟨5, by omega⟩) (by simp)).symm),
        Function.update_of_ne (frCompReg_injective.ne (hsub_ne (a := ⟨3, by omega⟩)
          (b := ⟨5, by omega⟩) (by simp)).symm),
        Function.update_of_ne (frCompReg_injective.ne (hW_ne ⟨5, by omega⟩).symm),
        hx18_comp]
    refine ⟨?_, ?_, by rw [h5_0]; omega, ?_, ?_, ?_⟩
    · dsimp only [Function.comp_apply, Data.comap_regs, x21, x20, x19, compReg]
      simp only [Data.set_regs,
        Function.update_of_ne (frCompReg_injective.ne (hsub_ne (a := ⟨3, by omega⟩)
          (b := ⟨4, by omega⟩) (by simp))),
        Function.update_self,
        Function.update_of_ne (hlow_ne ⟨0, by omega⟩ callerWidthReg (by simp)), hx18_0]
    · dsimp only [Function.comp_apply, Data.comap_regs, x21, x20, x19, compReg]
      simp only [Data.set_regs, Function.update_self,
        Function.update_of_ne (hlow_ne ⟨1, by omega⟩ (subReg ⟨3, by omega⟩) (by simp)),
        Function.update_of_ne (hlow_ne ⟨1, by omega⟩ callerWidthReg (by simp)), hx18_1]
    · intro a ha
      rw [h5_0]
      simp only [Data.comap_mem, x21, x20, x19, Data.set_mem, hx18_mid a ha]
      exact Nat.zero_le _
    · simp only [Data.comap_mem, x21, x20, x19, Data.set_mem, hx18_6H]
    · intro zq hzq
      simp only [Data.comap_mem, x21, x20, x19, Data.set_mem]
      exact hx18_tab zq hzq
  have hcomp_W : (x21.comap compReg).regs callerWidthReg = w_log := by
    dsimp only [Data.comap_regs, x21, x20, x19, compReg]
    simp only [Data.set_regs,
      Function.update_of_ne (frCompReg_injective.ne (hW_ne ⟨4, by omega⟩)),
      Function.update_of_ne (frCompReg_injective.ne (hW_ne ⟨3, by omega⟩)),
      Function.update_self, hx18_1]
  have hcomp_regs : (x21.comap compReg).regs ∘ callerReg =
      (Data.init (encBits z) (r := r_B)).regs := by
    funext i
    dsimp only [Function.comp_apply, Data.comap_regs, x21, x20, x19, compReg, Data.set_regs]
    rw [Function.update_of_ne (frCompReg_injective.ne (callerReg_ne_subReg i ⟨4, by omega⟩)),
      Function.update_of_ne (frCompReg_injective.ne (callerReg_ne_subReg i ⟨3, by omega⟩)),
      Function.update_of_ne (frCompReg_injective.ne (callerReg_ne_callerWidthReg i)),
      hx18_comp]
    rfl
  have hcomp_mem : ∀ a < H, (x21.comap compReg).mem a =
      (Data.init (encBits z) (r := r_B)).mem a := by
    intro a ha
    simp only [Data.comap_mem, x21, x20, x19, Data.set_mem, hx18_lo a ha]
    cases a <;> simp [Data.init_mem_zero, Data.init_mem_succ]
  obtain ⟨comp_out, hcomp_out, _, hcomp_regs_out, _, _⟩ :=
    compileOracle_exec (W := W) (w := w_log) (c := c_B) (sub := subA) (T_sub := T_wso) (Inv := Inv)
      (by omega) (Data.Bounded.init hfits_z) hex_B
      (fun m₁ m₂ rs k hagree ⟨h3, h4, h5, hst, h6, htab⟩ =>
        ⟨h3, h4, h5, fun a ha => by rw [← hagree _ (by omega)]; exact hst a ha,
          by rw [← hagree _ (by omega)]; exact h6,
          fun zq hzq => by
            have := bitStringCode_pos zq
            rw [← hagree _ (by omega)]; exact htab zq hzq⟩)
      (fun m rs k u v ⟨h3, h4, h5, hst, h6, htab⟩ =>
        ⟨by simp [h3], by simp [h4], by simp [h5], by simpa using hst, h6, htab⟩)
      (fun q k xs hq hk hbl hq_eq h1 ⟨h3, h4, h5, hst, h6, htab⟩ => by
        obtain ⟨z', y_A, t_A, qs_A, hz', hex_A, hyA_out, hA_cov, ht_wso⟩ := hA_on_q q hq
        have hgen_fits : Fits W (xs.regs ⟨5, by omega⟩ + 1) :=
          show xs.regs ⟨5, by omega⟩ + 1 < 2 ^ W by
            have : T_tot < 2 ^ W := by
              have hlt : T_tot + z.length < 2 ^ (Nat.log 2 (T_tot + z.length) + 1) :=
                Nat.lt_pow_succ_log_self (by omega) _
              have hpow : 2 ^ (Nat.log 2 (T_tot + z.length) + 1) ≤ 2 ^ W :=
                Nat.pow_le_pow_right Nat.two_pos (by
                  have := Nat.le_mul_of_pos_left (Nat.log 2 (T_tot + z.length) + 1)
                    (show 0 < K_tot by omega)
                  omega)
              omega
            omega
        have hq_fits_log : InputFits w_log q := by
          rw [← hz']
          exact inputFits_encBits (by
            have h1' := hex_B.sum_query_length_le
            have h2' : q.length + 1 ≤ (qs_B.map fun q => q.length + 1).sum :=
              List.le_sum_of_mem (List.mem_map_of_mem hq)
            rw [← hz', encBits_length] at h2'
            have h3' : Nat.log 2 z'.length + 1 ≤ Nat.log 2 (T_tot + z.length) + 1 :=
              Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
            have h4' : 4 * (Nat.log 2 (T_tot + z.length) + 1) ≤ W :=
              (Nat.mul_le_mul_right _ h4K).trans hW_ge_log
            simp only [logWidth, one_mul, hw_log]; omega)
        obtain ⟨zo, hzo, hzo2, hzo3, hzo4, hzo5, hzo_st, hzo_fr⟩ :=
          wrapStampedOracle_exec (W := W) (w_log := w_log) (H := H) (gen₀ := xs.regs ⟨5, by omega⟩)
            (O := oracleOf Q encBits) (c_A := c_A) (out_A := out_A) (sub := bitTableLookupCode)
            (T_sub := fun qi => 18 * qi.length + 25)
            hH.ge (by have : 6 * H < 2 ^ W := h6H; omega) hgen_fits hq_fits_log hex_A
            (fun qi xs_i hqi hbl_i hql_i hqb_i hqg_i hqrep_i hfr_i => by
              obtain ⟨zq, hzq, hzq_len⟩ := hA_cov qi hqi
              have hmem_nu : xs_i.mem (6 * H) = nu z.length :=
                (hfr_i (6 * H) (by omega)).trans h6
              obtain ⟨z_b, hz_b, hz_b_mem, hz_b_le, _⟩ :=
                bitTableLookupCode_exec (W := W) (H := H) (nu := nu z.length) (base := 2 * H)
                  (gen := xs.regs ⟨5, by omega⟩ + 1) (x := xs_i)
                  rfl h6H (hH ▸ Nat.one_le_two_pow) hpow_nu hmem_nu
                  (by rw [← hH] at hbl_i
                      change xs_i.regs ⟨0, by omega⟩ + xs_i.regs ⟨1, by omega⟩ ≤ H
                      rw [hql_i]; exact le_of_lt hbl_i) hqb_i hqg_i
              have hqi_len : qi.length = zq.length := by rw [← hzq, encBits_length]
              have hbits_le : ∀ i < qi.length,
                  stampedRead (2 * H) (xs.regs ⟨5, by omega⟩ + 1) xs_i.mem
                    (xs_i.regs ⟨0, by omega⟩ + i) ≤ 1 := by
                intro i hi
                have hget := congrArg (fun l => l[i]?) hqrep_i
                simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at hget
                rw [← hzq, encBits_apply] at hget
                have hi' : i < zq.length := by omega
                simp only [List.getElem?_map, List.getElem?_eq_getElem hi', Option.map_some,
                  Option.some.injEq] at hget
                rw [← hget]; cases zq[i] <;> simp
              have hz_eq : ((List.range qi.length).map fun i =>
                  decide (stampedRead (2 * H) (xs.regs ⟨5, by omega⟩ + 1) xs_i.mem
                    (xs_i.regs ⟨0, by omega⟩ + i) = 1)) = zq := by
                refine List.ext_getElem (by simp [hqi_len]) fun i hi₁ hi₂ => ?_
                have hi : i < qi.length := by simpa using hi₁
                have hget := congrArg (fun l => l[i]?) hqrep_i
                simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at hget
                rw [← hzq, encBits_apply] at hget
                simp only [List.getElem?_map, List.getElem?_eq_getElem hi₂, Option.map_some,
                  Option.some.injEq] at hget
                simp only [List.getElem_map, List.getElem_range]
                rw [← hget]; cases zq[i] <;> rfl
              have h4_eq : z_b.regs 4 = (oracleOf Q encBits qi).toNat := by
                have hle_nu : xs_i.regs 1 ≤ nu z.length := by
                  change xs_i.regs ⟨1, by omega⟩ ≤ nu z.length; omega
                have hbits' : ∀ i < xs_i.regs 1,
                    stampedRead (2 * H) (xs.regs ⟨5, by omega⟩ + 1) xs_i.mem (xs_i.regs 0 + i) ≤
                      1 := by
                  simpa only [show xs_i.regs 1 = qi.length from hql_i,
                    show xs_i.regs 0 = xs_i.regs ⟨0, by omega⟩ from rfl] using hbits_le
                rw [(hz_b_le hle_nu).1 hbits']
                have hz_eq' : ((List.range (xs_i.regs 1)).map fun i =>
                    decide (stampedRead (2 * H) (xs.regs ⟨5, by omega⟩ + 1) xs_i.mem
                      (xs_i.regs 0 + i) = 1)) = zq := by
                  simpa only [show xs_i.regs 1 = qi.length from hql_i,
                    show xs_i.regs 0 = xs_i.regs ⟨0, by omega⟩ from rfl] using hz_eq
                rw [hz_eq']
                have hnot : ¬(2 * H ≤ H + bitStringCode zq ∧ H + bitStringCode zq < 4 * H) := by
                  have hlt := bitStringCode_lt zq
                  have h2p : 2 ^ (zq.length + 1) ≤ 2 ^ (nu z.length + 1) :=
                    Nat.pow_le_pow_right Nat.two_pos (by omega)
                  omega
                rw [hfr_i _ hnot, htab zq hzq_len, hzq]
              exact ⟨z_b, hz_b.mono (by
                change 18 * xs_i.regs ⟨1, by omega⟩ + 25 ≤ 18 * qi.length + 25; rw [hql_i]),
                h4_eq, hz_b_mem⟩)
            (hH ▸ hbl) h1 hq_eq h3 h4 rfl hst
        refine ⟨zo, hzo.mono ht_wso, hzo2.trans hyA_out, fun a ha => hzo_fr a (by omega),
          hzo3, hzo4, by omega, hzo5 ▸ hzo_st, (hzo_fr (6 * H) (by omega)).trans h6,
          fun zq hzq => by
            have hlt := bitStringCode_lt zq
            have hpos := bitStringCode_pos zq
            have h2p : 2 ^ (zq.length + 1) ≤ 2 ^ (nu z.length + 1) :=
              Nat.pow_le_pow_right Nat.two_pos (by omega)
            exact (hzo_fr _ (by omega)).trans (htab zq hzq)⟩)
      le_rfl hcomp_W hcomp_regs (hH ▸ hcomp_mem) hInv0
  obtain ⟨x22, hx22, hx22_eq, _⟩ :=
    ExecWithin.rename_post frCompReg_injective ⟨comp_out, hcomp_out, rfl⟩
  let y_final := x22.set ⟨6, by omega⟩ (x22.regs (compReg (callerReg out_B)))
  have hy_out : y_final.regs ⟨6, by omega⟩ = y_B.regs out_B := by
    have h1 := congrFun (congrArg Data.regs hx22_eq.symm) (callerReg out_B)
    have h2 := congrFun hcomp_regs_out out_B
    simp only [y_final, Data.set_regs, Function.update_self]
    exact (show x22.regs (compReg (callerReg out_B)) =
      comp_out.regs (callerReg out_B) from h1).trans h2
  exact ⟨y_final, (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
    (hx22.seq ExecWithin.copy)))).mono (by omega), hy_out⟩

/-- **Core Method-of-Four-Russians Theorem**: given a problem `P` efficiently self-reducible for
`p`, a problem `Q` solvable in `O(β^s)` (`β > 1`), a fine-grained reduction `(P, p) ≤ (Q, γ^s)`
(`γ > 1`), and an efficiently computable threshold `ν(s)` balancing preprocessing `(4*β)^{ν(s)}`
with query coverage for all queries of `c_A` on sub-instances produced by `c_B`, `P` is decidable
on the Word RAM in time `O(p(s)^{1 - ε})` for some `0 < ε < 1`. -/
theorem exponentiallyUpwards_core {P Q : Set (List Bool)} {p : ℕ → ℝ} {β γ : ℝ}
    (hp_int : ∀ n, p n = 0 ∨ 1 ≤ p n)
    (hβ : 1 < β) (hγ : 1 < γ)
    (hQ : WordRAMDecidableInO Q encBits (fun z => β ^ z.length))
    (hSelf : EfficientlySelfReducible P encBits List.length p)
    (hRed : FineGrainedReducible P encBits List.length p Q encBits List.length (fun s => γ ^ s))
    (hNu : ∀ C_A : ℕ, 0 < C_A →
      ∃ (a_exp η_nu : ℝ) (r_nu C_nu : ℕ) (nuCode : Code .standard (r_nu + 2)) (nu : ℕ → ℕ),
        0 < a_exp ∧ a_exp < 1 ∧ 0 < η_nu ∧ η_nu < 1 ∧ 0 < C_nu ∧ nuCode.IsRandFree ∧
        (∀ s W (x : Data (r_nu + 2)),
          Fits W (s + ⌈p s⌉₊ + C_nu) → x.regs 0 = s →
          ∃ y : Data (r_nu + 2),
            ExecWithin W nuCode x y (C_nu * ⌈(p s) ^ (1 - η_nu)⌉₊ + C_nu) ∧
            y.regs 1 = nu s ∧ y.mem = x.mem) ∧
        (∀ s, ((4 * β) ^ (nu s) : ℝ) ≤ (C_nu : ℝ) * (p s) ^ (1 / 4 : ℝ) + (C_nu : ℝ)) ∧
        (∀ s s', p s' ≤ (p s) ^ a_exp → ∀ m : ℕ,
          (γ ^ (m : ℝ)) ^ (1 / 2 : ℝ) ≤ (C_A : ℝ) * p s' + 2 * (C_A : ℝ) →
          m ≤ nu s)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      WordRAMDecidableInO P encBits (fun z => (p z.length) ^ (1 - ε)) := by
  obtain ⟨hp_mono, hp0, hself⟩ := hSelf
  obtain ⟨δ_A, _, _, _, _, hδA_pos, hredA⟩ := hRed
  obtain ⟨r_A, c_A, out_A, C_A, k_A, hC_A, hk_A, hA⟩ := hredA (1 / 2 : ℝ) (by norm_num)
  obtain ⟨C_Q, hC_Q, r_Q, c_Q, out_Q, k_Q, hrf_Q, hk_Q, hQ_dec⟩ := hQ
  set ε_B : ℝ := min (δ_A (1 / 2)) (1 / 2)
  have hε_B : 0 < ε_B := lt_min (hδA_pos (1 / 2) (by norm_num)) (by norm_num)
  obtain ⟨a_exp, η_nu, r_nu, C_nu, nuCode, nu, ha_pos, ha_lt1, hη_pos, hη_lt1, hC_nu, hrf_nu,
    hnu_exec, hnu_pre, hnu_cov⟩ := hNu C_A hC_A
  obtain ⟨δ_B, hδB_pos, hselfB⟩ := hself a_exp ha_pos ha_lt1
  obtain ⟨r_B, c_B, out_B, C_B, k_B, hC_B, hk_B, hB⟩ := hselfB ε_B hε_B
  set ε : ℝ := min (1 / 4 : ℝ) (min η_nu (δ_B ε_B))
  have hε_pos : 0 < ε := lt_min (by norm_num) (lt_min hη_pos (hδB_pos ε_B hε_B))
  have hε_le_quarter : ε ≤ 1 / 4 := min_le_left _ _
  have hε_le_η : ε ≤ η_nu := (min_le_right _ _).trans (min_le_left _ _)
  have hε_le_δB : ε ≤ δ_B ε_B := (min_le_right _ _).trans (min_le_right _ _)
  let K_γ : ℕ := ⌈36 / Real.log γ + 30⌉₊ + 1
  have hK_γ_ge : (36 / Real.log γ + 30 : ℝ) ≤ (K_γ : ℝ) := by
    have := Nat.le_ceil (36 / Real.log γ + 30)
    have h1 : ((⌈36 / Real.log γ + 30⌉₊ : ℕ) : ℝ) + 1 = (K_γ : ℝ) := by simp [K_γ]
    linarith
  let K_build : ℕ := 104 * (7 * C_Q + r_Q + 40) * C_nu + 40
  let K_step : ℕ := (7 + K_γ) * C_A + r_A + 50
  let C_tot : ℕ := 2 * C_nu + K_build + (2 * C_B + 2) * (6 * K_step + 40) + 100
  have hC_tot_pos : 0 < C_tot := by positivity
  let K_tot : ℕ := 4 * (k_B + k_A + k_Q + C_nu + C_Q + C_A + C_B + r_Q + r_A + 20)
  have hK_tot_pos : 0 < K_tot := by positivity
  let prog := fourRussiansProg nuCode c_Q out_Q c_B out_B c_A out_A
  let rTot := 8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))
  refine ⟨ε, hε_pos, by linarith, C_tot, hC_tot_pos, rTot, prog, ⟨6, by omega⟩, K_tot,
    isRandFree_fourRussiansProg out_Q c_B out_B c_A out_A hrf_nu hrf_Q,
    hK_tot_pos, fun z W hW _ => ?_⟩
  set s := z.length
  set P_val : ℝ := (p s) ^ (1 - ε)
  set T_tot : ℕ := C_tot * ⌈max 0 P_val⌉₊ + C_tot
  have hP_nonneg : 0 ≤ P_val := Real.rpow_nonneg (hp0 s) _
  have hmaxP : max 0 P_val = P_val := max_eq_right hP_nonneg
  have hP_ge_ceil : P_val ≤ (⌈max 0 P_val⌉₊ : ℝ) := by rw [hmaxP]; exact Nat.le_ceil P_val
  have hrpow_le : ∀ r : ℝ, ε ≤ r → (p s) ^ (1 - r) ≤ P_val + 1 := fun r hr => by
    rcases hp_int s with hpz | hp1
    · rw [hpz]
      by_cases h0 : (1 : ℝ) - r = 0
      · rw [h0, Real.rpow_zero]; linarith
      · rw [Real.zero_rpow h0]; linarith
    · dsimp only [P_val]
      exact (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)).trans
        (le_add_of_nonneg_right zero_le_one)
  have hp_sq_le : ⌈p s⌉₊ ≤ (T_tot + s) ^ 2 := by
    rcases hp_int s with hpz | hp1
    · simp [hpz]
    · have h1 : p s ≤ P_val ^ 2 := by
        calc p s = (p s) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (p s) ^ (2 * (1 - ε)) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
          _ = P_val ^ 2 := by
              rw [show (2 : ℝ) * (1 - ε) = (1 - ε) * 2 by ring, Real.rpow_mul (hp0 s),
                Real.rpow_two]
      have h2 : P_val ≤ (T_tot : ℝ) := by
        have hC1 : (1 : ℝ) ≤ (C_tot : ℝ) := by exact_mod_cast hC_tot_pos
        have : (T_tot : ℝ) = (C_tot : ℝ) * (⌈max 0 P_val⌉₊ : ℝ) + (C_tot : ℝ) := by
          push_cast [T_tot]; ring
        nlinarith
      have h3 : p s ≤ ((T_tot + s : ℕ) : ℝ) ^ 2 := by
        have : (T_tot : ℝ) ≤ ((T_tot + s : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
        nlinarith
      exact Nat.ceil_le.mpr (by exact_mod_cast h3)
  have hlog_p : Nat.log 2 (⌈p s⌉₊ + s) + 1 ≤ 2 * (Nat.log 2 (T_tot + s) + 1) := by
    have hlt : T_tot + s < 2 ^ (Nat.log 2 (T_tot + s) + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hsum_lt : ⌈p s⌉₊ + s < 2 ^ (2 * (Nat.log 2 (T_tot + s) + 1)) := by
      have hlt' : (T_tot + s) ^ 2 + (T_tot + s) < (2 ^ (Nat.log 2 (T_tot + s) + 1)) ^ 2 := by
        have hpos : 1 ≤ 2 ^ (Nat.log 2 (T_tot + s) + 1) := Nat.one_le_two_pow
        nlinarith
      rw [← pow_mul, mul_comm] at hlt'
      omega
    rcases Nat.eq_zero_or_pos (⌈p s⌉₊ + s) with hz | hpos
    · simp [hz]; omega
    · exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow hpos.ne' hsum_lt)
  set w_log := W - 3
  set H := 2 ^ w_log
  have hW_ge_log : K_tot * (Nat.log 2 (T_tot + s) + 1) ≤ W := by
    simpa [encBits_length, s, T_tot, logWidth] using hW
  have hW_ge20 : 20 ≤ W := by
    have : 1 ≤ Nat.log 2 (T_tot + s) + 1 := by omega
    have : K_tot ≤ W := le_trans (Nat.le_mul_of_pos_right _ this) hW_ge_log
    omega
  have hH_gt : T_tot + s < H := by
    have hlt : T_tot + s < 2 ^ (Nat.log 2 (T_tot + s) + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hle : Nat.log 2 (T_tot + s) + 1 ≤ w_log := by
      have : 4 * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
        (Nat.mul_le_mul_right _ (by omega : 4 ≤ K_tot)).trans hW_ge_log
      omega
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right Nat.two_pos hle)
  have h6H : 6 * H < 2 ^ W := by
    have h8 : 2 ^ W = 8 * H := by
      rw [show W = w_log + 3 by omega, pow_add]; simp [H]; ring
    have hH_pos : 1 ≤ H := Nat.one_le_two_pow
    omega
  have hFits_s : Fits W (s + ⌈p s⌉₊ + C_nu) := by
    have hlt0 : T_tot + s < 2 ^ (Nat.log 2 (T_tot + s) + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hsum_lt : ⌈p s⌉₊ + s < 2 ^ (2 * (Nat.log 2 (T_tot + s) + 1)) := by
      have hlt' : (T_tot + s) ^ 2 + (T_tot + s) < (2 ^ (Nat.log 2 (T_tot + s) + 1)) ^ 2 := by
        have : 1 ≤ 2 ^ (Nat.log 2 (T_tot + s) + 1) := Nat.one_le_two_pow
        nlinarith
      rw [← pow_mul, mul_comm] at hlt'; omega
    have hpow_le : 2 ^ (2 * (Nat.log 2 (T_tot + s) + 1)) ≤ H := by
      apply Nat.pow_le_pow_right Nat.two_pos
      have : 4 * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
        (Nat.mul_le_mul_right _ (by omega : 4 ≤ K_tot)).trans hW_ge_log
      omega
    have hC_lt : C_nu < H := by omega
    exact show s + ⌈p s⌉₊ + C_nu < 2 ^ W by omega
  -- Preprocessing time bound and table size 2^(nu s + 1) ≤ H
  have hbuild_real :
      (((2 ^ (nu s + 1) : ℕ) * (11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40) + 20 :
        ℕ) : ℝ) ≤ (K_build : ℝ) * P_val + (K_build : ℝ) := by
    have h24 := two_pow_le_four_beta_pow hβ (nu s)
    have hpre := hnu_pre s
    have hP_q : (p s) ^ (1 / 4 : ℝ) ≤ P_val + 1 := by
      have h := hrpow_le (3 / 4 : ℝ) (by linarith)
      rwa [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num] at h
    have hstep_le :
        (11 * (nu s : ℝ) + 7 * ((C_Q : ℝ) * ((⌈β ^ (nu s)⌉₊ : ℕ) : ℝ) + (C_Q : ℝ)) +
          (r_Q : ℝ) + 40) ≤
        ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) *
          (11 * (nu s : ℝ) + 7 * ((⌈β ^ (nu s)⌉₊ : ℕ) : ℝ) + 1) := by
      have hCQ1 : (1 : ℝ) ≤ (C_Q : ℝ) := by exact_mod_cast hC_Q
      have hA : (7 : ℝ) * ((C_Q : ℝ) * ((⌈β ^ (nu s)⌉₊ : ℕ) : ℝ)) ≤
          ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (7 * ((⌈β ^ (nu s)⌉₊ : ℕ) : ℝ)) := by
        have h7 : (C_Q : ℝ) ≤ ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : C_Q ≤ 7 * C_Q + r_Q + 40)
        have hnn : (0 : ℝ) ≤ 7 * ((⌈β ^ (nu s)⌉₊ : ℕ) : ℝ) := by positivity
        linarith [mul_le_mul_of_nonneg_right h7 hnn]
      have hB : 11 * (nu s : ℝ) ≤ ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (11 * (nu s : ℝ)) := by
        have h1 : (1 : ℝ) ≤ ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ 7 * C_Q + r_Q + 40)
        exact le_mul_of_one_le_left (by positivity) h1
      have hC : 7 * (C_Q : ℝ) + (r_Q : ℝ) + 40 = ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * 1 := by
        push_cast; ring
      linarith
    have h1 : (((2 ^ (nu s + 1) : ℕ) *
        (11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40) + 20 : ℕ) : ℝ) ≤
        ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (52 * (4 * β) ^ (nu s)) + 20 := by
      have h2pow_nn : (0 : ℝ) ≤ ((2 ^ (nu s + 1) : ℕ) : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hstep_le h2pow_nn
      have hmul2 := mul_le_mul_of_nonneg_left h24
        (by positivity : (0 : ℝ) ≤ ((7 * C_Q + r_Q + 40 : ℕ) : ℝ))
      have hlhs_eq : (((2 ^ (nu s + 1) : ℕ) *
          (11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40) + 20 : ℕ) : ℝ) =
          ((2 ^ (nu s + 1) : ℕ) : ℝ) *
            (11 * (nu s : ℝ) + 7 * ((C_Q : ℝ) * ((⌈β ^ (nu s)⌉₊ : ℕ) : ℝ) + (C_Q : ℝ)) +
              (r_Q : ℝ) + 40) + 20 := by push_cast; ring
      rw [hlhs_eq]; linarith
    have hK_eq : (K_build : ℝ) =
        104 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ) + 40 := by
      dsimp only [K_build]; push_cast; ring
    have hpre2 : 52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (4 * β) ^ (nu s) ≤
        52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * ((C_nu : ℝ) * (P_val + 1) + (C_nu : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by linarith [mul_le_mul_of_nonneg_left hP_q (by positivity : (0 : ℝ) ≤ C_nu)])
        (by positivity)
    have h_alg : ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (52 * (4 * β) ^ (nu s)) =
        52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (4 * β) ^ (nu s) := by ring
    have h_alg2 : 52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * ((C_nu : ℝ) * (P_val + 1) + (C_nu : ℝ)) =
        (52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ)) * P_val +
          104 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ) := by ring
    have hnn_MC : (0 : ℝ) ≤ 52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ) * P_val := by
      positivity
    have h40P : (0 : ℝ) ≤ 40 * P_val := by positivity
    have hKP : (K_build : ℝ) * P_val =
        (104 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ) + 40) * P_val := by rw [hK_eq]
    have hKP_split : (104 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ) + 40) * P_val =
        (52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ)) * P_val +
          52 * ((7 * C_Q + r_Q + 40 : ℕ) : ℝ) * (C_nu : ℝ) * P_val + 40 * P_val := by ring
    linarith
  have hbuild_nat :
      2 ^ (nu s + 1) * (11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40) + 20 ≤
        K_build * ⌈max 0 P_val⌉₊ + K_build := by
    have hceil_r : (K_build : ℝ) * P_val + (K_build : ℝ) ≤
        ((K_build * ⌈max 0 P_val⌉₊ + K_build : ℕ) : ℝ) := by
      push_cast; linarith [mul_le_mul_of_nonneg_left hP_ge_ceil (by positivity : (0 : ℝ) ≤ K_build)]
    exact_mod_cast (hbuild_real.trans hceil_r)
  have hpow_nu : 2 ^ (nu s + 1) ≤ H := by
    have h1 : 2 ^ (nu s + 1) ≤
        2 ^ (nu s + 1) * (11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40) + 20 := by
      have := Nat.le_mul_of_pos_right (2 ^ (nu s + 1))
        (show 0 < 11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40 by omega)
      omega
    have hKC : K_build ≤ C_tot := by dsimp only [C_tot]; omega
    have h2 : K_build * ⌈max 0 P_val⌉₊ + K_build ≤ T_tot :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hKC) hKC
    omega
  -- Check w_log suffices for c_B
  have hw_log_B : logWidth k_B (⌈p s⌉₊ + s) ≤ w_log := by
    have h1 : k_B * (Nat.log 2 (⌈p s⌉₊ + s) + 1) ≤ 2 * k_B * (Nat.log 2 (T_tot + s) + 1) := by
      calc k_B * (Nat.log 2 (⌈p s⌉₊ + s) + 1)
          ≤ k_B * (2 * (Nat.log 2 (T_tot + s) + 1)) := Nat.mul_le_mul_left _ hlog_p
        _ = 2 * k_B * (Nat.log 2 (T_tot + s) + 1) := by ring
    have h2 : (2 * k_B + 3) * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
      (Nat.mul_le_mul_right _ (by omega : 2 * k_B + 3 ≤ K_tot)).trans hW_ge_log
    have hpos : 1 ≤ Nat.log 2 (T_tot + s) + 1 := by omega
    have h3 : 2 * k_B * (Nat.log 2 (T_tot + s) + 1) + 3 ≤
        (2 * k_B + 3) * (Nat.log 2 (T_tot + s) + 1) := by
      rw [Nat.add_mul]; have := Nat.le_mul_of_pos_right 3 hpos; omega
    simp only [logWidth, w_log] at h2 ⊢; omega
  have hfits_z : InputFits w_log (encBits z) :=
    inputFits_encBits (by
      have h1 : Nat.log 2 z.length + 1 ≤ Nat.log 2 (T_tot + s) + 1 :=
        Nat.add_le_add_right (Nat.log_mono_right (Nat.le_add_left _ _)) 1
      have h2 : 4 * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
        (Nat.mul_le_mul_right _ (by omega : 4 ≤ K_tot)).trans hW_ge_log
      simp only [logWidth, one_mul, w_log]; omega)
  -- Run outer self-reduction B
  obtain ⟨y_B, t_B, qs_B, hex_B, hyB_le, hyB_iff, hvalid_B, ht_B, hsum_B, hquery_B⟩ :=
    hB z w_log (by rwa [encBits_length]) hfits_z
  have ht_B_nat : t_B ≤ C_B * ⌈max 0 P_val⌉₊ + 2 * C_B := by
    have hCB : (0 : ℝ) ≤ (C_B : ℝ) := by positivity
    have h1 : (t_B : ℝ) ≤ (C_B : ℝ) * (P_val + 1) + (C_B : ℝ) :=
      ht_B.trans (by linarith [mul_le_mul_of_nonneg_left (hrpow_le (δ_B ε_B) hε_le_δB) hCB])
    have h2 : (C_B : ℝ) * (P_val + 1) + (C_B : ℝ) ≤
        ((C_B * ⌈max 0 P_val⌉₊ + 2 * C_B : ℕ) : ℝ) := by
      push_cast; linarith [mul_le_mul_of_nonneg_left hP_ge_ceil hCB]
    exact_mod_cast (h1.trans h2)
  have ht_B_le_T : t_B ≤ T_tot := by
    have hCB2 : 2 * C_B ≤ C_tot := by
      have hmul : 2 * C_B ≤ (2 * C_B + 2) * (6 * K_step + 40) :=
        le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
      dsimp only [C_tot]; omega
    have h1 : C_B * ⌈max 0 P_val⌉₊ + 2 * C_B ≤ C_tot * ⌈max 0 P_val⌉₊ + C_tot :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) hCB2
    exact ht_B_nat.trans h1
  have hqsB_le_tB : qs_B.length ≤ t_B := hex_B.length_queries_le
  -- Set up Q table solver bound
  have hQ_tab : ∀ zq : List Bool, zq.length ≤ nu s →
      c_Q.Answers out_Q w_log (encBits zq) (zq ∈ Q) (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) := by
    intro zq hzq
    have hpow_zq : β ^ zq.length ≤ β ^ (nu s) := pow_le_pow_right₀ (by linarith) hzq
    have hT_le : C_Q * ⌈max 0 (β ^ zq.length)⌉₊ + C_Q ≤ C_Q * ⌈β ^ (nu s)⌉₊ + C_Q := by
      rw [max_eq_right (by positivity)]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.ceil_mono hpow_zq)) _
    have hTQ_le_T : C_Q * ⌈β ^ (nu s)⌉₊ + C_Q + zq.length ≤ T_tot := by
      have h3 : C_Q * ⌈β ^ (nu s)⌉₊ + C_Q + zq.length ≤
          11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40 := by omega
      have h4 := h3.trans (Nat.le_mul_of_pos_left _ (Nat.one_le_two_pow (n := nu s + 1)))
      have hKC : K_build ≤ C_tot := by dsimp only [C_tot]; omega
      have h5 : K_build * ⌈max 0 P_val⌉₊ + K_build ≤ T_tot :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hKC) hKC
      omega
    have hw_Q : logWidth k_Q (C_Q * ⌈max 0 (β ^ zq.length)⌉₊ + C_Q + (encBits zq).length) ≤
        w_log := by
      rw [encBits_length]
      have h1 : Nat.log 2 (C_Q * ⌈max 0 (β ^ zq.length)⌉₊ + C_Q + zq.length) + 1 ≤
          Nat.log 2 (T_tot + s) + 1 :=
        Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
      have h2 : (k_Q + 3) * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
        (Nat.mul_le_mul_right _ (by omega : k_Q + 3 ≤ K_tot)).trans hW_ge_log
      have h3 : k_Q * (Nat.log 2 (T_tot + s) + 1) + 3 ≤
          (k_Q + 3) * (Nat.log 2 (T_tot + s) + 1) := by
        rw [Nat.add_mul]
        have := Nat.le_mul_of_pos_right 3 (show 1 ≤ Nat.log 2 (T_tot + s) + 1 by omega)
        omega
      have h4 := Nat.mul_le_mul_left k_Q h1
      simp only [logWidth, w_log] at h2 ⊢; omega
    have hfits_zq : InputFits w_log (encBits zq) :=
      inputFits_encBits (by
        have h1 : zq.length < 2 ^ (nu s + 1) :=
          lt_of_le_of_lt hzq (lt_trans (Nat.lt_succ_self _) Nat.lt_two_pow_self)
        have h2 : Nat.log 2 zq.length + 1 ≤ Nat.log 2 (T_tot + s) + 1 :=
          Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
        have h3 : 4 * (Nat.log 2 (T_tot + s) + 1) ≤ W :=
          (Nat.mul_le_mul_right _ (by omega : 4 ≤ K_tot)).trans hW_ge_log
        simp only [logWidth, one_mul, w_log]; omega)
    obtain ⟨yq, hyq, hyq1, hyqiff⟩ := hQ_dec zq w_log hw_Q hfits_zq
    exact ⟨yq, hyq.mono hT_le, hyq1, hyqiff⟩
  -- For every query q ∈ qs_B, obtain c_A execution, query coverage ≤ nu s, and time bound
  have hA_on_q : ∀ q ∈ qs_B, ∃ (z' : List Bool) (y_A : Data r_A) (t_A : ℕ) (qs_A : List (List ℕ)),
      encBits z' = q ∧
      OracleExec w_log (oracleOf Q encBits) c_A (.init q) y_A t_A qs_A ∧
      y_A.regs out_A = (oracleOf P encBits q).toNat ∧
      (∀ qi ∈ qs_A, ∃ zq : List Bool, encBits zq = qi ∧ zq.length ≤ nu s) ∧
      11 * q.length + 7 * t_A + (qs_A.map fun qi => (18 * qi.length + 25) + 5).sum + r_A + 20 ≤
        11 * q.length + K_step * ⌈(p z'.length) ^ (1 - ε_B)⌉₊ + 2 * K_step :=
    fourRussians_hA_on_q hγ hp_int hp0 ha_pos ha_lt1 (hδA_pos (1 / 2) (by norm_num)) hK_γ_ge rfl
      (by omega) (by omega) hW_ge_log rfl hp_sq_le ht_B_le_T hex_B.sum_query_length_le
      hvalid_B hquery_B (hnu_cov s) hA
  -- Define per-query time bound for compileOracle
  let T_wso : List ℕ → ℕ := fun q =>
    11 * q.length + K_step * ⌈(p (querySize encBits List.length q)) ^ (1 - ε_B)⌉₊ + 2 * K_step
  have hsum_Twso : (qs_B.map fun q => T_wso q + 3).sum ≤
      11 * t_B + K_step * (2 * C_B * ⌈max 0 P_val⌉₊ + 4 * C_B) + (3 * K_step + 3) * t_B := by
    have h1 : (qs_B.map fun q => T_wso q + 3).sum =
        11 * (qs_B.map List.length).sum +
        K_step * (qs_B.map fun q => ⌈(p (querySize encBits List.length q)) ^ (1 - ε_B)⌉₊).sum +
        (2 * K_step + 3) * qs_B.length := by
      suffices ∀ l : List (List ℕ), (l.map fun q => T_wso q + 3).sum =
          11 * (l.map List.length).sum +
          K_step * (l.map fun q => ⌈(p (querySize encBits List.length q)) ^ (1 - ε_B)⌉₊).sum +
          (2 * K_step + 3) * l.length from this qs_B
      intro l
      induction l with
      | nil => simp
      | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, T_wso] at ih ⊢
        rw [ih]; ring
    have hsum_len : (qs_B.map List.length).sum ≤ t_B :=
      (List.sum_le_sum fun q _ => Nat.le_succ q.length).trans hex_B.sum_query_length_le
    have hsum_ceil_real :
        (((qs_B.map fun q => ⌈(p (querySize encBits List.length q)) ^ (1 - ε_B)⌉₊).sum : ℕ) : ℝ) ≤
          (qs_B.map fun q => (p (querySize encBits List.length q)) ^ (1 - ε_B)).sum +
            (qs_B.length : ℝ) := by
      rw [Nat.cast_list_sum, List.map_map]
      have hlen_eq : (qs_B.length : ℝ) = (qs_B.map fun _ => (1 : ℝ)).sum := by simp
      rw [hlen_eq, ← List.sum_map_add]
      refine List.sum_le_sum fun q _ => ?_
      have hnn : 0 ≤ (p (querySize encBits List.length q)) ^ (1 - ε_B) :=
        Real.rpow_nonneg (hp0 _) _
      exact le_of_lt (Nat.ceil_lt_add_one hnn)
    have hsum_ceil_nat :
        (qs_B.map fun q => ⌈(p (querySize encBits List.length q)) ^ (1 - ε_B)⌉₊).sum ≤
          C_B * ⌈max 0 P_val⌉₊ + 2 * C_B + t_B := by
      have hCB : (0 : ℝ) ≤ (C_B : ℝ) := by positivity
      have hB_r : (qs_B.map fun q => (p (querySize encBits List.length q)) ^ (1 - ε_B)).sum ≤
          (C_B : ℝ) * (P_val + 1) + (C_B : ℝ) :=
        hsum_B.trans (by linarith [mul_le_mul_of_nonneg_left (hrpow_le (δ_B ε_B) hε_le_δB) hCB])
      have htot_r :
          (((qs_B.map fun q => ⌈(p (querySize encBits List.length q)) ^ (1 - ε_B)⌉₊).sum : ℕ) :
            ℝ) ≤ ((C_B * ⌈max 0 P_val⌉₊ + 2 * C_B + t_B : ℕ) : ℝ) := by
        have hqt : (qs_B.length : ℝ) ≤ (t_B : ℝ) := by exact_mod_cast hqsB_le_tB
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        linarith [mul_le_mul_of_nonneg_left hP_ge_ceil hCB]
      exact_mod_cast htot_r
    rw [h1]
    have hmul := Nat.mul_le_mul_left K_step hsum_ceil_nat
    have h2 : K_step * (C_B * ⌈max 0 P_val⌉₊ + 2 * C_B + t_B) =
        K_step * (C_B * ⌈max 0 P_val⌉₊ + 2 * C_B) + K_step * t_B := by ring
    have h3 : K_step * (C_B * ⌈max 0 P_val⌉₊ + 2 * C_B) ≤
        K_step * (2 * C_B * ⌈max 0 P_val⌉₊ + 4 * C_B) := by
      have : 2 * C_B * ⌈max 0 P_val⌉₊ = 2 * (C_B * ⌈max 0 P_val⌉₊) := by ring
      exact Nat.mul_le_mul_left _ (by omega)
    have h4 : (2 * K_step + 3) * qs_B.length ≤ (2 * K_step + 3) * t_B :=
      Nat.mul_le_mul_left _ hqsB_le_tB
    have h5 : K_step * t_B + (2 * K_step + 3) * t_B = (3 * K_step + 3) * t_B := by ring
    omega
  -- Combine all four stages via fourRussians_stage012_exec and fourRussians_stage3_exec
  have hnu_time : C_nu * ⌈(p s) ^ (1 - η_nu)⌉₊ + C_nu ≤ C_nu * ⌈max 0 P_val⌉₊ + 2 * C_nu := by
    have hceil_r : (p s) ^ (1 - η_nu) ≤ (⌈max 0 P_val⌉₊ : ℝ) + 1 :=
      (hrpow_le η_nu hε_le_η).trans (add_le_add hP_ge_ceil le_rfl)
    have hceil_n : ⌈(p s) ^ (1 - η_nu)⌉₊ ≤ ⌈max 0 P_val⌉₊ + 1 :=
      Nat.ceil_le.mpr (by exact_mod_cast hceil_r)
    have hm := Nat.mul_le_mul_left C_nu hceil_n
    rw [Nat.mul_add, Nat.mul_one] at hm; omega
  have htotal_time :
      7 + (1 + (C_nu * ⌈(p s) ^ (1 - η_nu)⌉₊ + C_nu) + 1 + 4) +
      (1 + 1 + 1 + (2 ^ (nu s + 1) * (11 * nu s + 7 * (C_Q * ⌈β ^ (nu s)⌉₊ + C_Q) + r_Q + 40) +
        20)) +
      (1 + 1 + 1 + (t_B + (qs_B.map fun q => T_wso q + 3).sum) + 1) ≤ T_tot := by
    have h1 : (3 * K_step + 15) * t_B ≤ (3 * K_step + 15) * (C_B * ⌈max 0 P_val⌉₊ + 2 * C_B) :=
      Nat.mul_le_mul_left _ ht_B_nat
    have h2 : K_step * (2 * C_B * ⌈max 0 P_val⌉₊ + 4 * C_B) +
        (3 * K_step + 15) * (C_B * ⌈max 0 P_val⌉₊ + 2 * C_B) =
        (5 * K_step + 15) * C_B * ⌈max 0 P_val⌉₊ + (10 * K_step + 30) * C_B := by ring
    have h3 : (5 * K_step + 15) * C_B ≤ (2 * C_B + 2) * (6 * K_step + 40) := by
      have : (2 * C_B + 2) * (6 * K_step + 40) =
          12 * (C_B * K_step) + 80 * C_B + 12 * K_step + 80 := by ring
      have : (5 * K_step + 15) * C_B = 5 * (C_B * K_step) + 15 * C_B := by ring
      omega
    have h4 : (10 * K_step + 30) * C_B ≤ (2 * C_B + 2) * (6 * K_step + 40) := by
      have : (2 * C_B + 2) * (6 * K_step + 40) =
          12 * (C_B * K_step) + 80 * C_B + 12 * K_step + 80 := by ring
      have : (10 * K_step + 30) * C_B = 10 * (C_B * K_step) + 30 * C_B := by ring
      omega
    have h5 : C_nu * ⌈max 0 P_val⌉₊ + K_build * ⌈max 0 P_val⌉₊ +
        (5 * K_step + 15) * C_B * ⌈max 0 P_val⌉₊ ≤ C_tot * ⌈max 0 P_val⌉₊ := by
      have hle : C_nu + K_build + (5 * K_step + 15) * C_B ≤ C_tot := by dsimp only [C_tot]; omega
      have := Nat.mul_le_mul_right ⌈max 0 P_val⌉₊ hle
      simpa [Nat.add_mul] using this
    have h6 : 2 * C_nu + K_build + (10 * K_step + 30) * C_B + 100 ≤ C_tot := by
      dsimp only [C_tot]; omega
    have h7 : t_B + (qs_B.map fun q => T_wso q + 3).sum ≤
        K_step * (2 * C_B * ⌈max 0 P_val⌉₊ + 4 * C_B) + (3 * K_step + 15) * t_B := by
      have : (3 * K_step + 15) * t_B = t_B + 11 * t_B + (3 * K_step + 3) * t_B := by ring
      omega
    dsimp only [T_tot]; omega
  have hA_on_q' : ∀ q ∈ qs_B, ∃ (z' : List Bool) (y_A : Data r_A) (t_A : ℕ) (qs_A : List (List ℕ)),
      encBits z' = q ∧
      OracleExec w_log (oracleOf Q encBits) c_A (.init q) y_A t_A qs_A ∧
      y_A.regs out_A = (oracleOf P encBits q).toNat ∧
      (∀ qi ∈ qs_A, ∃ zq : List Bool, encBits zq = qi ∧ zq.length ≤ nu s) ∧
      11 * q.length + 7 * t_A + (qs_A.map fun qi => (18 * qi.length + 25) + 5).sum + r_A + 20 ≤
        T_wso q := fun q hq => by
    obtain ⟨z', y_A, t_A, qs_A, hz', hex_A, hyA_out, hA_cov, ht_wso⟩ := hA_on_q q hq
    refine ⟨z', y_A, t_A, qs_A, hz', hex_A, hyA_out, hA_cov, ?_⟩
    dsimp only [T_wso]
    rw [← hz', querySize_enc, hz']; exact ht_wso
  have hstage3_ex : ∀ x18 : Data rTot,
      x18.regs ⟨0, by omega⟩ = H →
      x18.regs ⟨1, by omega⟩ = w_log →
      (∀ k, x18.regs (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) k) = 0) →
      x18.mem (6 * H) = nu s →
      (∀ a < H, x18.mem a = (Data.init (encBits z) (r := rTot)).mem a) →
      (∀ a < H, x18.mem (2 * H + 2 * a) = 0) →
      (∀ zq : List Bool, zq.length ≤ nu s →
        x18.mem (H + bitStringCode zq) = (oracleOf Q encBits (encBits zq)).toNat) →
      ∃ y_final : Data rTot,
        ExecWithin W
          (.seq (.op (.copy (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
              callerWidthReg) ⟨1, by omega⟩))
            (.seq (.op (.copy (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
                (subReg ⟨3, by omega⟩)) ⟨0, by omega⟩))
              (.seq (.op (.copy (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
                  (subReg ⟨4, by omega⟩)) ⟨1, by omega⟩))
                (.seq ((compileOracle c_B (wrapStampedOracle c_A out_A bitTableLookupCode)).rename
                    (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)))
                  (.op (.copy ⟨6, by omega⟩ (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B)
                    (r_A := r_A) (callerReg out_B))))))))
          x18 y_final (1 + 1 + 1 + (t_B + (qs_B.map fun q => T_wso q + 3).sum) + 1) ∧
        y_final.regs ⟨6, by omega⟩ = y_B.regs out_B :=
    fun x18 h0 h1 hc h6H' hlo hmid htab =>
      fourRussians_stage3_exec rfl (by omega) rfl h6H hpow_nu (by omega) hW_ge_log ht_B_le_T
        hfits_z hex_B hA_on_q' h0 h1 hc h6H' hlo hmid htab
  obtain ⟨y_final, hy_exec, hy_out⟩ :=
    fourRussians_stage012_exec (nuCode := nuCode) (c_Q := c_Q) (out_Q := out_Q)
      (c_B := c_B) (out_B := out_B) (c_A := c_A) (out_A := out_A)
      rfl (by omega) rfl h6H hpow_nu
      (by have : 1 ≤ T_tot := le_trans hC_tot_pos (Nat.le_add_left _ _); change s + 1 < H; omega)
      hrf_Q
      (fun x hx0 => hnu_exec s W x hFits_s hx0) hQ_tab hstage3_ex rfl
  exact ⟨y_final, hy_exec.mono htotal_time, by rw [hy_out]; exact hyB_le,
    by rw [hy_out]; exact hyB_iff⟩

end CslibFrontier.Complexity.FineGrained
