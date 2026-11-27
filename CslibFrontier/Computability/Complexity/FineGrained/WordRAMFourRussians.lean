/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.WordRAMFourRussiansCore
import CslibFrontier.Computability.WordRAM.Call
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Impossibility of Fine-Grained Reductions to Truly Exponential Problems

This module proves the Method-of-Four-Russians impossibility theorem for fine-grained reductions
from efficiently self-reducible problems to truly exponential problems (`exponentiallyUpwards`),
its corollary that no efficiently self-reducible problem has a tight exponential upper bound
(`exponentiallyUpwards_corollary`), and an unconditional joint-hypothesis non-vacuity witness
(`exponentiallyUpwards_nonvacuous`).

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.Complexity.FineGrained

open Cslib.WordRAM CslibFrontier.WordRAM

/-! ### `exponentiallyUpwards` -/

private def thm2NuCode {r_p : ℕ} (c_p : Code .standard (r_p + 2)) (M b₀ : ℕ) :
    Code .standard ((r_p + 2) + 5 + 3) :=
  let rTot := (r_p + 2) + 5 + 3
  let r0 : Fin rTot := ⟨0, by omega⟩
  let r1 : Fin rTot := ⟨1, by omega⟩
  let rTmp : Fin rTot := ⟨2, by omega⟩
  let pReg : Fin (r_p + 2) → Fin rTot := fun j => ⟨3 + j.val, by omega⟩
  let logReg : Fin 5 → Fin rTot := fun j => ⟨3 + (r_p + 2) + j.val, by omega⟩
  .seq (.op (.copy (pReg 0) r0))
    (.seq (c_p.rename pReg)
      (.seq (.op (.copy (logReg 0) (pReg 1)))
        (.seq (natLog2Code.rename logReg)
          (.seq (.op (.const rTmp M))
            (.seq (.op (.bin .div r1 (logReg 1) rTmp))
              (.seq (.op (.const rTmp b₀))
                (.op (.bin .add r1 r1 rTmp))))))))

private theorem isRandFree_thm2NuCode {r_p : ℕ} {c_p : Code .standard (r_p + 2)}
    (hc : c_p.IsRandFree) (M b₀ : ℕ) : (thm2NuCode c_p M b₀).IsRandFree :=
  ⟨trivial, isRandFree_rename hc, trivial, isRandFree_rename isRandFree_natLog2Code,
    trivial, trivial, trivial, trivial⟩

/-- if `p : ℕ → ℕ` is monotone and efficiently computable, `P` is efficiently
self-reducible for `p`, `Q` is solvable in time `O(β^s)` (`β > 1`), and `(P, p) ≤ (Q, γ^s)`
(`γ > 1`), then `P` is solvable in time `O(p(s)^{1 - ε})` for some `ε > 0`. -/
theorem exponentiallyUpwards {P Q : Set (List Bool)} {p : ℕ → ℕ} {β γ : ℝ}
    (hp_comp : EfficientlyComputable p)
    (hβ : 1 < β) (hγ : 1 < γ)
    (hQ : WordRAMDecidableInO Q encBits (fun z => β ^ z.length))
    (hSelf : EfficientlySelfReducible P encBits List.length (fun s => (p s : ℝ)))
    (hRed : FineGrainedReducible P encBits List.length (fun s => (p s : ℝ))
      Q encBits List.length (fun s => γ ^ s)) :
    ∃ ε : ℝ, 0 < ε ∧
      WordRAMDecidableInO P encBits (fun z => ((p z.length : ℝ)) ^ (1 - ε)) := by
  have hp_int : ∀ n, (p n : ℝ) = 0 ∨ 1 ≤ (p n : ℝ) := fun n => by
    rcases Nat.eq_zero_or_pos (p n) with h0 | hpos
    · left; simp [h0]
    · right; exact_mod_cast hpos
  obtain ⟨r_p, c_p, C_p, η_p, hrf_p, hC_p, hη_p, hη_p_lt1, hc_p⟩ := hp_comp
  obtain ⟨ε, hε, -, hdec⟩ :=
    exponentiallyUpwards_core hp_int hβ hγ hQ hSelf hRed (fun C_A hC_A => by
    let M : ℕ := ⌈4 * Real.log (4 * β) / Real.log 2⌉₊ + 4
    let b₀ : ℕ := ⌈2 * Real.log (3 * (C_A : ℝ)) / Real.log γ⌉₊ + 3
    let a_exp : ℝ := min (1 / 2 : ℝ) (Real.log γ / (2 * (M : ℝ) * Real.log 2))
    let nu : ℕ → ℕ := fun s => Nat.log 2 (p s) / M + b₀
    let η_nu : ℝ := min η_p (1 / 2 : ℝ)
    let C_nu : ℕ := ⌈(4 * β) ^ b₀⌉₊ + 2 * C_p + M + b₀ + 40
    have hM_pos : 0 < M := by positivity
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogγ : 0 < Real.log γ := Real.log_pos hγ
    have hlog4β : 0 < Real.log (4 * β) := Real.log_pos (by linarith)
    have ha_pos : 0 < a_exp := lt_min (by norm_num) (by positivity)
    have ha_lt1 : a_exp < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hη_pos : 0 < η_nu := lt_min hη_p (by norm_num)
    have hη_lt1 : η_nu < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hC_nu_pos : 0 < C_nu := by positivity
    let nuCode := thm2NuCode c_p M b₀
    let pReg : Fin (r_p + 2) → Fin ((r_p + 2) + 5 + 3) := fun j => ⟨3 + j.val, by omega⟩
    let logReg : Fin 5 → Fin ((r_p + 2) + 5 + 3) := fun j => ⟨3 + (r_p + 2) + j.val, by omega⟩
    have hpReg_inj : Function.Injective pReg := fun a b h => by
      have hv := congrArg Fin.val h; simp only [pReg] at hv; exact Fin.ext (by omega)
    have hlogReg_inj : Function.Injective logReg := fun a b h => by
      have hv := congrArg Fin.val h; simp only [logReg] at hv; exact Fin.ext (by omega)
    refine ⟨a_exp, η_nu, (r_p + 2) + 5 + 1, C_nu, nuCode, nu, ha_pos, ha_lt1, hη_pos, hη_lt1,
      hC_nu_pos, isRandFree_thm2NuCode hrf_p M b₀, ?_, ?_, ?_⟩
    · intro s W x hfits hx0
      have hceil_ps : ⌈(p s : ℝ)⌉₊ = p s := Nat.ceil_natCast (p s)
      rw [hceil_ps] at hfits
      have hW_ge1 : 1 ≤ W := by
        have h1 : 1 < 2 ^ W := lt_of_le_of_lt (by omega : 1 ≤ s + p s + C_nu) hfits
        rcases Nat.eq_zero_or_pos W with rfl | hw
        · simp at h1
        · exact hw
      have hfits_p : Fits W (s + p s + 1) := Fits.of_le hfits (by omega)
      let x1 := x.set (pReg 0) (x.regs 0)
      obtain ⟨p_out, hp_out, hp_1, hp_mem⟩ := hc_p s W (x1.comap pReg) hfits_p (by
        simp [x1, pReg, hx0])
      obtain ⟨x2, hx2, hx2_eq, _⟩ := ExecWithin.rename_post hpReg_inj ⟨p_out, hp_out, rfl⟩
      have hx2_mem : x2.mem = x.mem := (congrArg Data.mem hx2_eq.symm).trans hp_mem
      have hx2_p1 : x2.regs (pReg 1) = p s :=
        (congrFun (congrArg Data.regs hx2_eq.symm) 1).trans hp_1
      let x3 := x2.set (logReg 0) (x2.regs (pReg 1))
      have hx3_0 : (x3.comap logReg).regs 0 = p s := by simp [x3, logReg, hx2_p1]
      have hps_fits : Fits W (p s) := Fits.of_le hfits (by omega)
      obtain ⟨l_out, hl_out, hl_1, _, hl_mem⟩ :=
        natLog2Code_exec hW_ge1 (x := x3.comap logReg) (by rw [hx3_0]; exact hps_fits)
      obtain ⟨x4, hx4, hx4_eq, _⟩ := ExecWithin.rename_post hlogReg_inj ⟨l_out, hl_out, rfl⟩
      have hx4_mem : x4.mem = x.mem := (congrArg Data.mem hx4_eq.symm).trans (hl_mem.trans hx2_mem)
      have hx4_l1 : x4.regs (logReg 1) = Nat.log 2 (p s) :=
        (congrFun (congrArg Data.regs hx4_eq.symm) 1).trans
          (hl_1.trans (congrArg (Nat.log 2) hx3_0))
      have hM_fits : Fits W M := Fits.of_le hfits (by omega)
      have hb0_fits : Fits W b₀ := Fits.of_le hfits (by omega)
      have hdiv_fits : Fits W (Nat.log 2 (p s) / M) :=
        Fits.of_le hps_fits ((Nat.div_le_self _ _).trans (Nat.log_le_self 2 (p s)))
      have hnu_fits : Fits W (nu s) := by
        have h1 : Nat.log 2 (p s) / M ≤ p s := (Nat.div_le_self _ _).trans (Nat.log_le_self 2 _)
        exact Fits.of_le hfits (by dsimp only [nu]; omega)
      let x5 := x4.set ⟨2, by omega⟩ M
      let x6 := x5.set ⟨1, by omega⟩ (Nat.log 2 (p s) / M)
      let x7 := x6.set ⟨2, by omega⟩ b₀
      let x8 := x7.set ⟨1, by omega⟩ (nu s)
      have htail : ExecWithin (B := .standard) W
          (.seq (.op (.const ⟨2, by omega⟩ M))
            (.seq (.op (.bin .div ⟨1, by omega⟩ (logReg 1) ⟨2, by omega⟩))
              (.seq (.op (.const ⟨2, by omega⟩ b₀))
                (.op (.bin .add ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩))))) x4 x8 4 := by
        have e1 : ExecWithin (B := .standard) W (.op (.const ⟨2, by omega⟩ M)) x4 x5 1 :=
          ExecWithin.const hM_fits
        have hne2 : logReg 1 ≠ ⟨2, by omega⟩ := Fin.ne_of_val_ne (by simp [logReg]; omega)
        have e2 : ExecWithin (B := .standard) W
            (.op (.bin .div ⟨1, by omega⟩ (logReg 1) ⟨2, by omega⟩)) x5 x6 1 := by
          simpa [x6, x5, hne2, hx4_l1] using ExecWithin.bin (w := W) (x := x5) (f := .div)
            (d := ⟨1, by omega⟩) (i := logReg 1) (j := ⟨2, by omega⟩)
            (by simpa [x5, hne2, hx4_l1] using hdiv_fits)
        have e3 : ExecWithin (B := .standard) W (.op (.const ⟨2, by omega⟩ b₀)) x6 x7 1 :=
          ExecWithin.const hb0_fits
        have e4 : ExecWithin (B := .standard) W
            (.op (.bin .add ⟨1, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩)) x7 x8 1 := by
          simpa [x8, x7, x6, nu] using ExecWithin.bin (w := W) (x := x7) (f := .add)
            (d := ⟨1, by omega⟩) (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
            (by simpa [x7, x6, nu] using hnu_fits)
        exact e1.seq (e2.seq (e3.seq e4))
      have htime : 1 + (C_p * ⌈((p s : ℝ)) ^ (1 - η_p)⌉₊ + C_p) + 1 +
          (4 * Nat.log 2 (p s) + 6) + 4 ≤ C_nu * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + C_nu := by
        have h1 : ⌈((p s : ℝ)) ^ (1 - η_p)⌉₊ ≤ ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + 1 := by
          refine Nat.ceil_le.mpr ?_
          have hle : ((p s : ℝ)) ^ (1 - η_p) ≤ ((p s : ℝ)) ^ (1 - η_nu) + 1 := by
            rcases hp_int s with hpz | hp1
            · rw [hpz]
              have h0 : (0 : ℝ) ^ (1 - η_p) = 0 := Real.zero_rpow (by linarith)
              have h0' : (0 : ℝ) ^ (1 - η_nu) = 0 := Real.zero_rpow (by linarith)
              rw [h0, h0']; norm_num
            · exact (Real.rpow_le_rpow_of_exponent_le hp1
                (by have := min_le_left η_p (1 / 2 : ℝ); linarith)).trans
                (le_add_of_nonneg_right zero_le_one)
          have := Nat.le_ceil (((p s : ℝ)) ^ (1 - η_nu))
          push_cast; linarith
        have h2 : 4 * Nat.log 2 (p s) ≤ 16 * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + 16 := by
          have hsq := nat_log_le_sqrt (p s)
          have hle : ((p s : ℝ)) ^ (1 / 2 : ℝ) ≤ ((p s : ℝ)) ^ (1 - η_nu) + 1 := by
            rcases hp_int s with hpz | hp1
            · rw [hpz, Real.zero_rpow (by norm_num), Real.zero_rpow (by linarith)]; norm_num
            · exact (Real.rpow_le_rpow_of_exponent_le hp1
                (by have := min_le_right η_p (1 / 2 : ℝ); linarith)).trans
                (le_add_of_nonneg_right zero_le_one)
          have hc := Nat.le_ceil (((p s : ℝ)) ^ (1 - η_nu))
          have hr : (4 * (Nat.log 2 (p s) : ℝ)) ≤
              ((16 * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + 16 : ℕ) : ℝ) := by
            push_cast; nlinarith
          exact_mod_cast hr
        have hC1 : C_p + 16 ≤ C_nu := by dsimp only [C_nu]; omega
        have hC2 : 2 * C_p + 28 ≤ C_nu := by dsimp only [C_nu]; omega
        have hm1 : C_p * ⌈((p s : ℝ)) ^ (1 - η_p)⌉₊ ≤ C_p * (⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + 1) :=
          Nat.mul_le_mul_left _ h1
        have hm2 : (C_p + 16) * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ ≤
            C_nu * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ := Nat.mul_le_mul_right _ hC1
        have hadd : (C_p + 16) * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ =
            C_p * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + 16 * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ := by ring
        have hmul : C_p * (⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + 1) =
            C_p * ⌈((p s : ℝ)) ^ (1 - η_nu)⌉₊ + C_p := by ring
        omega
      refine ⟨x8, (ExecWithin.copy.seq (hx2.seq (ExecWithin.copy.seq
        (hx4.seq htail)))).mono (by rw [hx3_0]; omega),
        by simp [x8], by simp [x8, x7, x6, x5, hx4_mem]⟩
    · intro s
      have h4β_pos : 0 < 4 * β := by linarith
      have hM_ge : 4 * Real.log (4 * β) / Real.log 2 ≤ (M : ℝ) := by
        have := Nat.le_ceil (4 * Real.log (4 * β) / Real.log 2)
        dsimp only [M]; push_cast; linarith
      have hdiv_le : ((Nat.log 2 (p s) / M : ℕ) : ℝ) ≤ (Nat.log 2 (p s) : ℝ) / (M : ℝ) :=
        Nat.cast_div_le
      have hpow_eq : ((4 * β) ^ (nu s) : ℝ) = (4 * β) ^ b₀ * (4 * β) ^ (Nat.log 2 (p s) / M) := by
        dsimp only [nu]; rw [pow_add, mul_comm]
      rw [hpow_eq]
      have hpart : (4 * β) ^ (Nat.log 2 (p s) / M) ≤ ((p s : ℝ)) ^ (1 / 4 : ℝ) + 1 := by
        rcases Nat.eq_zero_or_pos (p s) with hpz | hpos
        · simp [hpz]
        · have hlog_le : (Nat.log 2 (p s) / M : ℕ) * Real.log (4 * β) ≤
              Real.log (p s) / 4 := by
            have h1 : ((Nat.log 2 (p s) / M : ℕ) : ℝ) * Real.log (4 * β) ≤
                ((Nat.log 2 (p s) : ℝ) / (M : ℝ)) * Real.log (4 * β) :=
              mul_le_mul_of_nonneg_right hdiv_le hlog4β.le
            have h2 : Real.log (4 * β) / (M : ℝ) ≤ Real.log 2 / 4 := by
              rw [div_le_iff₀ (by positivity)]
              have hmul := (div_le_iff₀ hlog2).mp hM_ge
              linarith
            have h3 : (Nat.log 2 (p s) : ℝ) * Real.log 2 ≤ Real.log (p s) := by
              have hpow : (2 : ℝ) ^ (Nat.log 2 (p s)) ≤ (p s : ℝ) := by
                exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
              simpa [Real.log_pow] using Real.log_le_log (by positivity) hpow
            have h4 : ((Nat.log 2 (p s) : ℝ) / (M : ℝ)) * Real.log (4 * β) =
                (Nat.log 2 (p s) : ℝ) * (Real.log (4 * β) / (M : ℝ)) := by ring
            have hnn : (0 : ℝ) ≤ (Nat.log 2 (p s) : ℝ) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left h2 hnn]
          have hexp : (4 * β) ^ (Nat.log 2 (p s) / M) ≤ ((p s : ℝ)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos h4β_pos,
              Real.rpow_def_of_pos (by exact_mod_cast hpos)]
            exact Real.exp_le_exp.mpr (by linarith)
          linarith
      have hceil_b0 : (4 * β) ^ b₀ ≤ (C_nu : ℝ) := by
        have := Nat.le_ceil ((4 * β) ^ b₀)
        dsimp only [C_nu]; push_cast; linarith
      have h1 : (4 * β) ^ b₀ * (4 * β) ^ (Nat.log 2 (p s) / M) ≤
          (C_nu : ℝ) * (((p s : ℝ)) ^ (1 / 4 : ℝ) + 1) :=
        mul_le_mul hceil_b0 hpart (by positivity) (by positivity)
      linarith
    · intro s s' hps' m hm
      have h1 : (γ ^ (m : ℝ)) ^ (1 / 2 : ℝ) ≤
          3 * (C_A : ℝ) * max 1 (((p s : ℝ)) ^ a_exp) := by
        rcases hp_int s with hpz | hp1
        · have h0 : (p s' : ℝ) = 0 := by
            rw [hpz, Real.zero_rpow ha_pos.ne'] at hps'
            exact le_antisymm hps' (Nat.cast_nonneg _)
          rw [h0] at hm; simp only [mul_zero, zero_add] at hm
          have hmax : (1 : ℝ) ≤ max 1 (((p s : ℝ)) ^ a_exp) := le_max_left _ _
          nlinarith
        · have hge1 : (1 : ℝ) ≤ ((p s : ℝ)) ^ a_exp :=
            Real.one_le_rpow hp1 ha_pos.le
          rw [max_eq_right hge1]
          nlinarith
      have hlog_step : (m : ℝ) * (Real.log γ / 2) ≤
          Real.log (3 * (C_A : ℝ)) + a_exp * Real.log (max 1 (p s : ℝ)) := by
        have hpos_rhs : 0 < 3 * (C_A : ℝ) * max 1 (((p s : ℝ)) ^ a_exp) := by
          have : (1 : ℝ) ≤ max 1 (((p s : ℝ)) ^ a_exp) := le_max_left _ _
          positivity
        have hlhs : Real.log ((γ ^ (m : ℝ)) ^ (1 / 2 : ℝ)) = (m : ℝ) * (Real.log γ / 2) := by
          rw [Real.log_rpow (Real.rpow_pos_of_pos (by linarith) _),
            Real.log_rpow (by linarith)]; ring
        have hlog_le := Real.log_le_log (by positivity) h1
        rw [hlhs, Real.log_mul (by positivity) (by positivity)] at hlog_le
        rcases hp_int s with hpz | hp1
        · rw [hpz, Real.zero_rpow ha_pos.ne', max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
            Real.log_one] at hlog_le
          rw [hpz, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), Real.log_one]
          linarith
        · have hge1 : (1 : ℝ) ≤ ((p s : ℝ)) ^ a_exp := Real.one_le_rpow hp1 ha_pos.le
          rw [max_eq_right hge1, Real.log_rpow (by linarith)] at hlog_le
          rw [max_eq_right hp1]
          linarith
      have hm_real : (m : ℝ) ≤ ((nu s : ℕ) : ℝ) := by
        have hb0_ge : 2 * Real.log (3 * (C_A : ℝ)) / Real.log γ + 2 ≤ (b₀ : ℝ) := by
          have := Nat.le_ceil (2 * Real.log (3 * (C_A : ℝ)) / Real.log γ)
          dsimp only [b₀]; push_cast; linarith
        have ha_le : 2 * a_exp * Real.log 2 / Real.log γ ≤ 1 / (M : ℝ) := by
          have h1' : a_exp ≤ Real.log γ / (2 * (M : ℝ) * Real.log 2) := min_le_right _ _
          rw [div_le_iff₀ hlogγ]
          have h2' := (le_div_iff₀ (by positivity)).mp h1'
          calc 2 * a_exp * Real.log 2
              = a_exp * (2 * (M : ℝ) * Real.log 2) / (M : ℝ) := by field_simp
            _ ≤ Real.log γ / (M : ℝ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
            _ = 1 / (M : ℝ) * Real.log γ := by ring
        have hlog_max : Real.log (max 1 (p s : ℝ)) ≤
            ((Nat.log 2 (p s) : ℝ) + 1) * Real.log 2 := by
          rcases hp_int s with hpz | hp1
          · rw [hpz, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), Real.log_one]
            positivity
          · rw [max_eq_right hp1]
            have hlt : (p s : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (p s) + 1) := by
              exact_mod_cast le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two (p s))
            simpa [Real.log_pow] using Real.log_le_log (by linarith) hlt
        have hdiv_ge : (Nat.log 2 (p s) : ℝ) / (M : ℝ) - 1 ≤ ((Nat.log 2 (p s) / M : ℕ) : ℝ) := by
          have hlt : Nat.log 2 (p s) < (Nat.log 2 (p s) / M + 1) * M := by
            have := Nat.lt_div_mul_add hM_pos (a := Nat.log 2 (p s))
            have hmul : Nat.log 2 (p s) / M * M + M = (Nat.log 2 (p s) / M + 1) * M := by ring
            omega
          have hr : (Nat.log 2 (p s) : ℝ) < (((Nat.log 2 (p s) / M : ℕ) : ℝ) + 1) * (M : ℝ) := by
            exact_mod_cast hlt
          have := (div_lt_iff₀ (by positivity)).mpr hr
          linarith
        have hstep1 : (m : ℝ) ≤ 2 * Real.log (3 * (C_A : ℝ)) / Real.log γ +
            (2 * a_exp / Real.log γ) * Real.log (max 1 (p s : ℝ)) := by
          have hmul : (m : ℝ) * (Real.log γ / 2) * (2 / Real.log γ) ≤
              (Real.log (3 * (C_A : ℝ)) + a_exp * Real.log (max 1 (p s : ℝ))) * (2 / Real.log γ) :=
            mul_le_mul_of_nonneg_right hlog_step (by positivity)
          have hlhs : (m : ℝ) * (Real.log γ / 2) * (2 / Real.log γ) = (m : ℝ) := by
            field_simp [hlogγ.ne']
          rw [hlhs] at hmul
          linarith [show (Real.log (3 * (C_A : ℝ)) + a_exp * Real.log (max 1 (p s : ℝ))) *
              (2 / Real.log γ) = 2 * Real.log (3 * (C_A : ℝ)) / Real.log γ +
              (2 * a_exp / Real.log γ) * Real.log (max 1 (p s : ℝ)) by ring]
        have hstep2 : (2 * a_exp / Real.log γ) * Real.log (max 1 (p s : ℝ)) ≤
            ((Nat.log 2 (p s) : ℝ) + 1) / (M : ℝ) := by
          have h1' : (2 * a_exp / Real.log γ) * Real.log (max 1 (p s : ℝ)) ≤
              (2 * a_exp / Real.log γ) * (((Nat.log 2 (p s) : ℝ) + 1) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hlog_max (by positivity)
          have h2' : (2 * a_exp / Real.log γ) * (((Nat.log 2 (p s) : ℝ) + 1) * Real.log 2) =
              ((Nat.log 2 (p s) : ℝ) + 1) * (2 * a_exp * Real.log 2 / Real.log γ) := by ring
          have h3' : ((Nat.log 2 (p s) : ℝ) + 1) * (2 * a_exp * Real.log 2 / Real.log γ) ≤
              ((Nat.log 2 (p s) : ℝ) + 1) * (1 / (M : ℝ)) :=
            mul_le_mul_of_nonneg_left ha_le (by positivity)
          linarith [show ((Nat.log 2 (p s) : ℝ) + 1) * (1 / (M : ℝ)) =
            ((Nat.log 2 (p s) : ℝ) + 1) / (M : ℝ) by ring]
        have h1M : (1 : ℝ) / (M : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact_mod_cast hM_pos
        have hsplit : ((Nat.log 2 (p s) : ℝ) + 1) / (M : ℝ) =
            (Nat.log 2 (p s) : ℝ) / (M : ℝ) + 1 / (M : ℝ) := by ring
        dsimp only [nu]; push_cast; linarith
      exact_mod_cast hm_real)
  exact ⟨ε, hε, hdec⟩

/-! ### Immediate Corollary -/

private def corNuCode (b_rat b₀ : ℕ) : Code .standard 4 :=
  let r0 : Fin 4 := 0; let r1 : Fin 4 := 1; let r2 : Fin 4 := 2
  ram[ r2 ← #b_rat; r1 ← r0 / r2; r2 ← #b₀; r1 ← r1 + r2 ]

/-- Corollary: no efficiently self-reducible problem has truly
exponential complexity. If `P` is solvable in `O(α^s)` (`α > 1`) and efficiently self-reducible
for `β^s` (`β > 1`), then `P` is solvable in `O(γ^s)` for some `1 < γ < β`. -/
theorem exponentiallyUpwards_corollary {P : Set (List Bool)} {α β : ℝ}
    (hα : 1 < α) (hβ : 1 < β)
    (hP : WordRAMDecidableInO P encBits (fun z => α ^ z.length))
    (hSelf : EfficientlySelfReducible P encBits List.length (fun s => β ^ s)) :
    ∃ γ : ℝ, 1 < γ ∧ γ < β ∧ WordRAMDecidableInO P encBits (fun z => γ ^ z.length) := by
  have hp_int : ∀ n, β ^ n = 0 ∨ 1 ≤ β ^ n := fun n => Or.inr (one_le_pow₀ (by linarith))
  -- Self-reducibility at a_exp = 1/2 yields (P, β^s) ≤ (P, β^s)
  have hRed : FineGrainedReducible P encBits List.length (fun s => β ^ s)
      P encBits List.length (fun s => β ^ s) := by
    obtain ⟨hm, h0, hs⟩ := hSelf
    obtain ⟨δ, hδ, hrun⟩ := hs (1 / 2) (by norm_num) (by norm_num)
    refine ⟨δ, hm, hm, h0, h0, hδ, fun ε hε => ?_⟩
    obtain ⟨r, c, out, C, k, hC, hk, h⟩ := hrun ε hε
    refine ⟨r, c, out, C, k, hC, hk, fun a w hw hi => ?_⟩
    obtain ⟨y, t, qs, hex, hy1, hyi, hv, ht, hsum, -⟩ := h a w hw hi
    exact ⟨y, t, qs, hex, hy1, hyi, hv, ht, hsum⟩
  obtain ⟨ε, hε, hε_lt1, hdec⟩ :=
    exponentiallyUpwards_core hp_int hα hβ hP hSelf hRed (fun C_A hC_A => by
    let b_rat : ℕ := ⌈4 * Real.log (4 * α) / Real.log β⌉₊ + 1
    let b₀ : ℕ := ⌈2 * Real.log (3 * (C_A : ℝ)) / Real.log β⌉₊ + 3
    let a_exp : ℝ := min (1 / 2 : ℝ) (1 / (2 * (b_rat : ℝ)))
    let nu : ℕ → ℕ := fun s => s / b_rat + b₀
    let C_nu : ℕ := ⌈(4 * α) ^ b₀⌉₊ + b_rat + b₀ + 10
    have hb_pos : 0 < b_rat := by positivity
    have hlogβ : 0 < Real.log β := Real.log_pos hβ
    have hlog4α : 0 < Real.log (4 * α) := Real.log_pos (by linarith)
    have ha_pos : 0 < a_exp := lt_min (by norm_num) (by positivity)
    have ha_lt1 : a_exp < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨a_exp, 1 / 2, 2, C_nu, corNuCode b_rat b₀, nu, ha_pos, ha_lt1,
      by norm_num, by norm_num, by positivity, by simp [corNuCode, Code.IsRandFree], ?_, ?_, ?_⟩
    · intro s W x hfits hx0
      have hbr : Fits W b_rat := Fits.of_le hfits (by dsimp only [C_nu]; omega)
      have hb0f : Fits W b₀ := Fits.of_le hfits (by dsimp only [C_nu]; omega)
      have hdivf : Fits W (s / b_rat) := Fits.of_le hfits (by
        have := Nat.div_le_self s b_rat; omega)
      have hnuf : Fits W (nu s) := Fits.of_le hfits (by
        have := Nat.div_le_self s b_rat; dsimp only [nu, C_nu]; omega)
      let x1 := x.set 2 b_rat
      let x2 := x1.set 1 (s / b_rat)
      let x3 := x2.set 2 b₀
      let x4 := x3.set 1 (nu s)
      have hex : ExecWithin (B := .standard) W (corNuCode b_rat b₀) x x4 4 := by
        have e1 : ExecWithin (B := .standard) W (.op (.const 2 b_rat)) x x1 1 :=
          ExecWithin.const hbr
        have e2 : ExecWithin (B := .standard) W (.op (.bin .div 1 0 2)) x1 x2 1 := by
          simpa [x2, x1, hx0] using ExecWithin.bin (w := W) (x := x1) (f := .div)
            (d := 1) (i := 0) (j := 2) (by simpa [x1, hx0] using hdivf)
        have e3 : ExecWithin (B := .standard) W (.op (.const 2 b₀)) x2 x3 1 :=
          ExecWithin.const hb0f
        have e4 : ExecWithin (B := .standard) W (.op (.bin .add 1 1 2)) x3 x4 1 := by
          simpa [x4, x3, x2, nu] using ExecWithin.bin (w := W) (x := x3) (f := .add)
            (d := 1) (i := 1) (j := 2) (by simpa [x3, x2, nu] using hnuf)
        exact e1.seq (e2.seq (e3.seq e4))
      refine ⟨x4, hex.mono (by dsimp only [C_nu]; omega), by simp [x4], rfl⟩
    · intro s
      have hb_ge : 4 * Real.log (4 * α) / Real.log β ≤ (b_rat : ℝ) := by
        have := Nat.le_ceil (4 * Real.log (4 * α) / Real.log β)
        dsimp only [b_rat]; push_cast; linarith
      have hdiv_le : ((s / b_rat : ℕ) : ℝ) ≤ (s : ℝ) / (b_rat : ℝ) := Nat.cast_div_le
      have hpow_eq : ((4 * α) ^ (nu s) : ℝ) = (4 * α) ^ b₀ * (4 * α) ^ (s / b_rat) := by
        dsimp only [nu]; rw [pow_add, mul_comm]
      rw [hpow_eq]
      have hpart : (4 * α) ^ (s / b_rat) ≤ (β ^ s) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith),
          ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
        refine Real.exp_le_exp.mpr ?_
        rw [Real.log_rpow (by linarith)]
        have h1 : ((s / b_rat : ℕ) : ℝ) * Real.log (4 * α) ≤
            ((s : ℝ) / (b_rat : ℝ)) * Real.log (4 * α) :=
          mul_le_mul_of_nonneg_right hdiv_le hlog4α.le
        have h2 : Real.log (4 * α) / (b_rat : ℝ) ≤ Real.log β / 4 := by
          rw [div_le_iff₀ (by positivity)]
          have := (div_le_iff₀ hlogβ).mp hb_ge; linarith
        have h3 : ((s : ℝ) / (b_rat : ℝ)) * Real.log (4 * α) =
            (s : ℝ) * (Real.log (4 * α) / (b_rat : ℝ)) := by ring
        have hnn : (0 : ℝ) ≤ (s : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2 hnn]
      have hceil_b0 : (4 * α) ^ b₀ ≤ (C_nu : ℝ) := by
        have := Nat.le_ceil ((4 * α) ^ b₀)
        dsimp only [C_nu]; push_cast; linarith
      have h1 : (4 * α) ^ b₀ * (4 * α) ^ (s / b_rat) ≤ (C_nu : ℝ) * (β ^ s) ^ (1 / 4 : ℝ) :=
        mul_le_mul hceil_b0 hpart (by positivity) (by positivity)
      linarith
    · intro s s' hps' m hm
      have hge1 : (1 : ℝ) ≤ (β ^ s) ^ a_exp :=
        Real.one_le_rpow (one_le_pow₀ (by linarith)) ha_pos.le
      have h1 : (β ^ (m : ℝ)) ^ (1 / 2 : ℝ) ≤ 3 * (C_A : ℝ) * (β ^ s) ^ a_exp := by nlinarith
      have hlog_step : (m : ℝ) * (Real.log β / 2) ≤
          Real.log (3 * (C_A : ℝ)) + a_exp * ((s : ℝ) * Real.log β) := by
        have hlhs : Real.log ((β ^ (m : ℝ)) ^ (1 / 2 : ℝ)) = (m : ℝ) * (Real.log β / 2) := by
          rw [Real.log_rpow (Real.rpow_pos_of_pos (by linarith) _),
            Real.log_rpow (by linarith)]; ring
        have hlog_le := Real.log_le_log (by positivity) h1
        rw [hlhs, Real.log_mul (by positivity) (by positivity),
          Real.log_rpow (by positivity), Real.log_pow] at hlog_le
        exact hlog_le
      have hmul : (m : ℝ) * (Real.log β / 2) * (2 / Real.log β) ≤
          (Real.log (3 * (C_A : ℝ)) + a_exp * ((s : ℝ) * Real.log β)) * (2 / Real.log β) :=
        mul_le_mul_of_nonneg_right hlog_step (by positivity)
      have hlhs : (m : ℝ) * (Real.log β / 2) * (2 / Real.log β) = (m : ℝ) := by
        field_simp [hlogβ.ne']
      have hrhs : (Real.log (3 * (C_A : ℝ)) + a_exp * ((s : ℝ) * Real.log β)) * (2 / Real.log β) =
          2 * Real.log (3 * (C_A : ℝ)) / Real.log β + 2 * a_exp * (s : ℝ) := by
        field_simp [hlogβ.ne']
      rw [hlhs, hrhs] at hmul
      have ha_s : 2 * a_exp * (s : ℝ) ≤ (s : ℝ) / (b_rat : ℝ) := by
        have h1' : a_exp ≤ 1 / (2 * (b_rat : ℝ)) := min_le_right _ _
        have h2' : 2 * a_exp ≤ 1 / (b_rat : ℝ) := by
          have := mul_le_mul_of_nonneg_left h1' (by norm_num : (0 : ℝ) ≤ 2)
          linarith [show 2 * (1 / (2 * (b_rat : ℝ))) = 1 / (b_rat : ℝ) by ring]
        have := mul_le_mul_of_nonneg_right h2' (by positivity : (0 : ℝ) ≤ (s : ℝ))
        linarith [show 1 / (b_rat : ℝ) * (s : ℝ) = (s : ℝ) / (b_rat : ℝ) by ring]
      have hdiv_ge : (s : ℝ) / (b_rat : ℝ) - 1 ≤ ((s / b_rat : ℕ) : ℝ) := by
        have hlt : s < (s / b_rat + 1) * b_rat := by
          have := Nat.lt_div_mul_add hb_pos (a := s)
          have hmul : s / b_rat * b_rat + b_rat = (s / b_rat + 1) * b_rat := by ring
          omega
        have hr : (s : ℝ) < (((s / b_rat : ℕ) : ℝ) + 1) * (b_rat : ℝ) := by exact_mod_cast hlt
        have := (div_lt_iff₀ (by positivity)).mpr hr; linarith
      have hb0_ge : 2 * Real.log (3 * (C_A : ℝ)) / Real.log β + 2 ≤ (b₀ : ℝ) := by
        have := Nat.le_ceil (2 * Real.log (3 * (C_A : ℝ)) / Real.log β)
        dsimp only [b₀]; push_cast; linarith
      have hm_r : (m : ℝ) ≤ ((nu s : ℕ) : ℝ) := by dsimp only [nu]; push_cast; linarith
      exact_mod_cast hm_r)
  refine ⟨β ^ (1 - ε), Real.one_lt_rpow hβ (by linarith), ?_, ?_⟩
  · calc β ^ (1 - ε) < β ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hβ (by linarith)
      _ = β := Real.rpow_one β
  · convert hdec using 1
    funext z
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
      ← Real.rpow_mul (by linarith), mul_comm (z.length : ℝ) (1 - ε)]

/-! ### Joint-Hypothesis Non-Vacuity Witness for `exponentiallyUpwards` -/

private def headTrueProblem : Set (List Bool) := { z | z.getD 0 false = true }

private def headTrueCode : Code .standard 2 :=
  let r0 : Fin 2 := 0; let r1 : Fin 2 := 1
  ram[ r0 ← #1; r1 ← *r0 ]

private theorem headTrueCode_exec {w : ℕ} (hw : 1 ≤ w) (z : List Bool) :
    headTrueCode.Answers 1 w (encBits z) (z ∈ headTrueProblem) 2 := by
  have h1 : Fits w 1 := fits_one (by omega)
  let x0 : Data 2 := .init (encBits z)
  let x1 := x0.set 0 1
  let x2 := x1.set 1 (x1.mem 1)
  have hex : ExecWithin (B := .standard) w headTrueCode x0 x2 2 := by
    have e1 : ExecWithin (B := .standard) w (.op (.const 0 1)) x0 x1 1 := ExecWithin.const h1
    have e2 : ExecWithin (B := .standard) w (.op (.load 1 0)) x1 x2 1 := by
      simpa [x2, x1] using ExecWithin.load (w := w) (x := x1) (d := 1) (a := 0)
    exact e1.seq e2
  have hm1 : x1.mem 1 = (z.getD 0 false).toNat := by
    cases z with
    | nil => simp [x1, x0, Data.init_mem_succ, encBits_apply]
    | cons b zs => simp [x1, x0, Data.init_mem_succ, encBits_apply]
  refine ⟨x2, hex, ?_, ?_⟩
  · simp only [x2, Data.set_regs, Function.update_self, hm1]; cases z.getD 0 false <;> simp
  · simp only [x2, Data.set_regs, Function.update_self, hm1, headTrueProblem, Set.mem_ofPred_eq]
    cases z.getD 0 false <;> simp

/-- Unconditional non-degenerate joint-hypothesis witness for `exponentiallyUpwards`:
every hypothesis of `exponentiallyUpwards` holds for `P = Q = { z | z.getD 0 false = true }`,
`p(s) = s^2`, `β = γ = 2`, with `[true] ∈ P` and `[false] ∉ P`. -/
theorem exponentiallyUpwards_nonvacuous :
    ∃ (P Q : Set (List Bool)) (p : ℕ → ℕ) (β γ : ℝ),
      [true] ∈ P ∧ [false] ∉ P ∧ [true] ∈ Q ∧ [false] ∉ Q ∧
      Monotone p ∧ EfficientlyComputable p ∧ 1 < β ∧ 1 < γ ∧
      WordRAMDecidableInO Q encBits (fun z => β ^ z.length) ∧
      EfficientlySelfReducible P encBits List.length (fun s => (p s : ℝ)) ∧
      FineGrainedReducible P encBits List.length (fun s => (p s : ℝ))
        Q encBits List.length (fun s => γ ^ s) := by
  refine ⟨headTrueProblem, headTrueProblem, fun s => s ^ 2, 2, 2,
    by simp [headTrueProblem], by simp [headTrueProblem],
    by simp [headTrueProblem], by simp [headTrueProblem],
    fun _ _ h => Nat.pow_le_pow_left h 2, efficientlyComputable_sq,
    by norm_num, by norm_num, ?_, ?_, ?_⟩
  · refine ⟨2, by norm_num, 2, headTrueCode, 1, 1, by simp [headTrueCode, Code.IsRandFree],
      Nat.one_pos, fun z w hw _ => ?_⟩
    have hw1 : 1 ≤ w := le_trans (by simp [logWidth]) hw
    obtain ⟨y, hy, hy1, hyiff⟩ := headTrueCode_exec hw1 z
    exact ⟨y, hy.mono (by dsimp only; omega), hy1, hyiff⟩
  · refine ⟨fun _ _ h => by dsimp only; exact_mod_cast Nat.pow_le_pow_left h 2,
      fun _ => by positivity, fun _ _ _ => ⟨fun _ => 1 / 2, fun _ _ => by norm_num,
        fun _ _ => ⟨2, OracleCode.ofCode headTrueCode, 1, 2, 1, by norm_num, Nat.one_pos,
          fun z w hw _ => ?_⟩⟩⟩
    have hw1 : 1 ≤ w := le_trans (by simp [logWidth]) hw
    obtain ⟨y, ⟨t, ht, hex⟩, hy1, hyiff⟩ := headTrueCode_exec hw1 z
    refine ⟨y, t, [], oracleExec_of_exec hex (by simp [headTrueCode, Code.IsRandFree]), hy1, hyiff,
      (fun _ h => nomatch h), ?_, ?_, (fun _ h => nomatch h)⟩
    · have : 0 ≤ ((z.length ^ 2 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
      dsimp only; nlinarith
    · simp only [Nat.cast_pow, List.map_nil, List.sum_nil, Nat.cast_ofNat, one_div]; positivity
  · refine ⟨fun _ => 1 / 2, fun _ _ h => by dsimp only; exact_mod_cast Nat.pow_le_pow_left h 2,
      fun _ _ h => pow_le_pow_right₀ (by norm_num) h, fun _ => by positivity,
      fun _ => by positivity, fun _ _ => by norm_num, fun _ _ =>
        ⟨2, OracleCode.ofCode headTrueCode, 1, 2, 1, by norm_num, Nat.one_pos,
          fun z w hw _ => ?_⟩⟩
    have hw1 : 1 ≤ w := le_trans (by simp [logWidth]) hw
    obtain ⟨y, ⟨t, ht, hex⟩, hy1, hyiff⟩ := headTrueCode_exec hw1 z
    refine ⟨y, t, [], oracleExec_of_exec hex (by simp [headTrueCode, Code.IsRandFree]), hy1, hyiff,
      (fun _ h => nomatch h), ?_, ?_⟩
    · have : 0 ≤ ((z.length ^ 2 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
      dsimp only; nlinarith
    · simp only [List.map_nil, List.sum_nil, Nat.cast_ofNat, Nat.cast_pow, one_div]; positivity

end CslibFrontier.Complexity.FineGrained
