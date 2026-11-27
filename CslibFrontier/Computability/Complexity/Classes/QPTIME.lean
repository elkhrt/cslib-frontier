module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.Time

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Quasipolynomial Deterministic Time (`QPTIME`)

Defines the deterministic quasipolynomial time complexity class `QPTIME` over
`Cslib.Complexity.DTIME`, together with closure under complement, inclusion of `P`, and a
convenient constructor from `ComputableInO` decision procedures with time bounds of the form
`C * 2 ^ (D * (Nat.log 2 n + 1) ^ l) * (n + 1) ^ D`.

## Main definitions

- `Cslib.Complexity.QPTIME`: languages decidable in deterministic time
  $\mathcal{O}(2^{(\log n)^t})$ for some real exponent $t > 0$.

## Main results

- `Cslib.Complexity.mem_QPTIME_of_exp_natLog_pow`: lifts a `ComputableInO` decision procedure
  with quasipolynomial `Nat.log`-polynomial time bound into `QPTIME`.
- `Cslib.Complexity.QPTIME.compl`: closure of `QPTIME` under complement.
- `Cslib.Complexity.P_subset_QPTIME`: `P enc ⊆ QPTIME enc`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Deterministic quasipolynomial time `QPTIME`: languages decidable in deterministic time
`O(2 ^ ((log (max n 2)) ^ t))` for some `t > 0`. -/
def QPTIME {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (t : ℝ) (C : ℕ) (T : ℕ → ℕ), 0 < t ∧
    (∀ n : ℕ, (T n : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ ((Real.log (max (n : ℝ) 2)) ^ t)) ∧
    L ∈ DTIME enc T}

lemma mem_QPTIME_iff {α : Type} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ QPTIME enc ↔
      ∃ (t : ℝ) (C : ℕ) (T : ℕ → ℕ), 0 < t ∧
        (∀ n : ℕ, (T n : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ ((Real.log (max (n : ℝ) 2)) ^ t)) ∧
        L ∈ DTIME enc T := by rfl

private lemma real_log_max_pos (n : ℕ) : 0 < Real.log (max (n : ℝ) 2) :=
  lt_of_lt_of_le (Real.log_pos one_lt_two) (Real.log_le_log (by norm_num) (le_max_right _ _))

private lemma real_one_le_two_rpow_log (n : ℕ) (t : ℝ) :
    (1 : ℝ) ≤ (2 : ℝ) ^ ((Real.log (max (n : ℝ) 2)) ^ t) :=
  Real.one_le_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt (real_log_max_pos n)) t)

private lemma nat_log2_le_real_log_div (n : ℕ) :
    ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.log (max (n : ℝ) 2) / Real.log 2 := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.log_zero_right, Nat.cast_zero]
    have h0 := real_log_max_pos 0
    rw [Nat.cast_zero] at h0
    exact div_nonneg (le_of_lt h0) (le_of_lt (Real.log_pos one_lt_two))
  · have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
    have hpowR : (2 : ℝ) ^ (Nat.log 2 n) ≤ max (n : ℝ) 2 :=
      le_trans (by exact_mod_cast hpow) (le_max_left _ _)
    have hlog := Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).mpr hlog

private lemma exists_rpow_absorb_tail (c t : ℝ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (Real.log (max (n : ℝ) 2)) ^ t ≤ (Real.log (max (n : ℝ) 2)) ^ (t + 1) := by
  let M : ℝ := Real.exp (max c 1)
  refine ⟨Nat.ceil M + 2, fun n hn ↦ ?_⟩
  have hM_le_n : M ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil M) (by exact_mod_cast (by omega : Nat.ceil M ≤ n))
  have hlog_ge : max c 1 ≤ Real.log (max (n : ℝ) 2) := by
    calc max c 1 = Real.log M := (Real.log_exp _).symm
      _ ≤ Real.log (max (n : ℝ) 2) :=
        Real.log_le_log (Real.exp_pos _) (le_trans hM_le_n (le_max_left _ _))
  have hpos := real_log_max_pos n
  rw [Real.rpow_add hpos, Real.rpow_one, mul_comm _ (Real.log (max (n : ℝ) 2))]
  exact mul_le_mul_of_nonneg_right (le_trans (le_max_left c 1) hlog_ge)
    (Real.rpow_nonneg (le_of_lt hpos) t)

private lemma nat_rpow_le_two_rpow_log (d : ℕ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ d ≤
      (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2)) := by
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * max (n : ℝ) 2 := by
    have hle : (n : ℝ) ≤ max (n : ℝ) 2 := le_max_left _ _
    have h2 : (2 : ℝ) ≤ max (n : ℝ) 2 := le_max_right _ _
    push_cast; linarith
  have hpow : ((n + 1 : ℕ) : ℝ) ^ d ≤ (2 * max (n : ℝ) 2) ^ d :=
    pow_le_pow_left₀ (by positivity) hn1 d
  rw [mul_pow] at hpow
  have hmax : (max (n : ℝ) 2) ^ d =
      (2 : ℝ) ^ ((d : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2)) := by
    have hpos : 0 < max (n : ℝ) 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
    rw [show (2 : ℝ) ^ ((d : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2)) =
        Real.exp (Real.log 2 * ((d : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2))) from
      Real.rpow_def_of_pos (by norm_num) _]
    rw [show Real.log 2 * ((d : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2)) =
        Real.log (max (n : ℝ) 2) * (d : ℝ) by field_simp [hlog2]]
    rw [← Real.rpow_def_of_pos hpos, Real.rpow_natCast]
  rw [hmax] at hpow
  exact hpow

/-- Any decision procedure `f : α → Bool` computable within time
`C * 2 ^ (D * (Nat.log 2 n + 1) ^ l) * (n + 1) ^ D` decides `{a | f a = true}` in `QPTIME`. -/
theorem mem_QPTIME_of_exp_natLog_pow {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    {T S : α → ℕ} (hf : ComputableInO f enc encBool T S) (C D l : ℕ)
    (hT : ∀ a : α, T a ≤
      C * 2 ^ (D * (Nat.log 2 (enc a).length + 1) ^ l) * ((enc a).length + 1) ^ D) :
    {a | f a = true} ∈ QPTIME enc := by
  let tFun : ℕ → ℕ := fun n ↦ C * 2 ^ (D * (Nat.log 2 n + 1) ^ l) * (n + 1) ^ D
  have hmem : {a | f a = true} ∈ DTIME enc tFun := setOf_mem_DTIME_of_computableInO hf hT
  let t : ℝ := (l : ℝ) + 2
  have ht : 0 < t := by dsimp only [t]; positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let c0 : ℝ := ((D : ℝ) * (2 / Real.log 2) ^ l + (D : ℝ) / Real.log 2) + 1
  obtain ⟨N₁, hN₁⟩ := exists_rpow_absorb_tail c0 ((l : ℝ) + 1)
  have hlog_ge_one : ∀ n : ℕ, 3 ≤ n → (1 : ℝ) ≤ Real.log (max (n : ℝ) 2) := by
    intro n hn
    have hexp1 : Real.exp 1 ≤ 3 := by
      have hlt : (9 / 10 : ℝ) < Real.exp (-(1 / 10 : ℝ)) := by
        have h := Real.add_one_lt_exp (show (-(1 / 10 : ℝ)) ≠ 0 by norm_num)
        linarith
      have hinv : Real.exp (1 / 10 : ℝ) < 10 / 9 := by
        rw [Real.exp_neg] at hlt
        have hpos : 0 < Real.exp (1 / 10 : ℝ) := Real.exp_pos _
        rw [lt_inv_comm₀ (by norm_num) hpos] at hlt
        linarith
      have hpow : Real.exp 1 = (Real.exp (1 / 10 : ℝ)) ^ 10 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [hpow]
      have h10 : (Real.exp (1 / 10 : ℝ)) ^ 10 < (10 / 9 : ℝ) ^ 10 :=
        pow_lt_pow_left₀ hinv (le_of_lt (Real.exp_pos _)) (by decide)
      have hnum : (10 / 9 : ℝ) ^ 10 < 3 := by norm_num
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (max (n : ℝ) 2) :=
        Real.log_le_log (Real.exp_pos 1) (le_trans hexp1 (le_trans (by exact_mod_cast hn)
          (le_max_left _ _)))
  let N₀ : ℕ := max (max N₁ 3) 1
  let K_tail : ℕ := C * 2 ^ D
  let K_head : ℕ := (Finset.range N₀).sup tFun
  refine ⟨t, K_tail + K_head + 1, tFun, ht, fun n ↦ ?_, hmem⟩
  by_cases hn : n < N₀
  · have hle : tFun n ≤ K_head := Finset.le_sup (f := tFun) (Finset.mem_range.mpr hn)
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((Real.log (max (n : ℝ) 2)) ^ t) :=
      real_one_le_two_rpow_log n t
    have hK : (tFun n : ℝ) ≤ ((K_tail + K_head + 1 : ℕ) : ℝ) := by
      exact_mod_cast le_trans hle (by omega)
    nlinarith
  · have hn_ge : N₀ ≤ n := Nat.le_of_not_lt hn
    have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ 3) (le_max_left _ 1)) hn_ge
    have h3 : 3 ≤ n := le_trans (le_trans (le_max_right N₁ 3) (le_max_left _ 1)) hn_ge
    have hL1 : (1 : ℝ) ≤ Real.log (max (n : ℝ) 2) := hlog_ge_one n h3
    have hL_pos : 0 < Real.log (max (n : ℝ) 2) := real_log_max_pos n
    have hnat_log : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤
        (2 / Real.log 2) * Real.log (max (n : ℝ) 2) := by
      have h1 := nat_log2_le_real_log_div n
      have h2 : (1 : ℝ) ≤ Real.log (max (n : ℝ) 2) / Real.log 2 := by
        rw [one_le_div hlog2_pos]
        have hlt2 : Real.log 2 < 1 := by
          have : Real.log 2 < Real.log (Real.exp 1) := by
            apply Real.log_lt_log (by norm_num)
            have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
            linarith
          rwa [Real.log_exp] at this
        linarith
      push_cast
      have hmul : (2 / Real.log 2) * Real.log (max (n : ℝ) 2) =
          2 * (Real.log (max (n : ℝ) 2) / Real.log 2) := by ring
      rw [hmul]; linarith
    have hpow_l : (((Nat.log 2 n + 1 : ℕ) ^ l : ℕ) : ℝ) ≤
        (2 / Real.log 2) ^ l * (Real.log (max (n : ℝ) 2)) ^ l := by
      push_cast
      calc (((Nat.log 2 n : ℝ) + 1) ^ l)
          ≤ ((2 / Real.log 2) * Real.log (max (n : ℝ) 2)) ^ l :=
            pow_le_pow_left₀ (by positivity) (by push_cast at hnat_log; exact hnat_log) l
        _ = (2 / Real.log 2) ^ l * (Real.log (max (n : ℝ) 2)) ^ l := mul_pow _ _ _
    have hL_pow_le : (Real.log (max (n : ℝ) 2)) ^ l ≤
        (Real.log (max (n : ℝ) 2)) ^ ((l : ℝ) + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hL_le_pow : Real.log (max (n : ℝ) 2) ≤
        (Real.log (max (n : ℝ) 2)) ^ ((l : ℝ) + 1) := by
      conv_lhs => rw [← Real.rpow_one (Real.log (max (n : ℝ) 2))]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [Nat.cast_nonneg (α := ℝ) l])
    have hexp_le :
        ((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) +
          (D : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2) ≤
          (Real.log (max (n : ℝ) 2)) ^ t := by
      have hstep1 :
          ((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) +
            (D : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2) ≤
            c0 * (Real.log (max (n : ℝ) 2)) ^ ((l : ℝ) + 1) := by
        have hD1 : ((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) ≤
            (D : ℝ) * ((2 / Real.log 2) ^ l * (Real.log (max (n : ℝ) 2)) ^ ((l : ℝ) + 1)) := by
          push_cast
          exact mul_le_mul_of_nonneg_left (le_trans (by exact_mod_cast hpow_l)
            (mul_le_mul_of_nonneg_left hL_pow_le (by positivity))) (by positivity)
        have hD2 : (D : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2) ≤
            ((D : ℝ) / Real.log 2) * (Real.log (max (n : ℝ) 2)) ^ ((l : ℝ) + 1) := by
          rw [show (D : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2) =
              ((D : ℝ) / Real.log 2) * Real.log (max (n : ℝ) 2) by ring]
          exact mul_le_mul_of_nonneg_left hL_le_pow (by positivity)
        have hc0_pos : (0 : ℝ) ≤ (Real.log (max (n : ℝ) 2)) ^ ((l : ℝ) + 1) :=
          Real.rpow_nonneg (le_of_lt hL_pos) _
        dsimp only [c0]
        nlinarith
      have hstep2 := hN₁ n hN1
      have ht_eq : (l : ℝ) + 1 + 1 = t := by dsimp only [t]; ring
      rw [ht_eq] at hstep2
      exact le_trans hstep1 hstep2
    have hcast : (tFun n : ℝ) =
        (C : ℝ) * (2 : ℝ) ^ ((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) *
          ((n + 1 : ℕ) : ℝ) ^ D := by
      dsimp only [tFun]; rw [Real.rpow_natCast]; push_cast; rfl
    rw [hcast]
    have hpoly := nat_rpow_le_two_rpow_log D n
    calc (C : ℝ) * (2 : ℝ) ^ ((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ D
        ≤ (C : ℝ) * (2 : ℝ) ^ ((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) *
            ((2 : ℝ) ^ D * (2 : ℝ) ^ ((D : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2))) := by
          gcongr
      _ = ((C : ℝ) * (2 : ℝ) ^ D) *
            (2 : ℝ) ^ (((D * (Nat.log 2 n + 1) ^ l : ℕ) : ℝ) +
              (D : ℝ) * (Real.log (max (n : ℝ) 2) / Real.log 2)) := by
          rw [Real.rpow_add (by norm_num)]; ring
      _ ≤ (K_tail : ℝ) * (2 : ℝ) ^ ((Real.log (max (n : ℝ) 2)) ^ t) := by
          have hKtail : (C : ℝ) * (2 : ℝ) ^ D = (K_tail : ℝ) := by
            dsimp only [K_tail]; push_cast; rfl
          rw [hKtail]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le) (by positivity)
      _ ≤ ((K_tail + K_head + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((Real.log (max (n : ℝ) 2)) ^ t) := by
          gcongr
          exact_mod_cast (by omega : K_tail ≤ K_tail + K_head + 1)

/-- `QPTIME` is closed under complement. -/
theorem QPTIME.compl {α : Type} {enc : α ↪ List Bool} {L : Set α}
    (h : L ∈ QPTIME enc) : Lᶜ ∈ QPTIME enc := by
  rcases h with ⟨t, C, T, ht, hT, hDT⟩
  refine ⟨t, C, T, ht, hT, ?_⟩
  have hind := computableInO_indicator_of_mem_DTIME hDT
  obtain ⟨Tn, Sn, _, _, hnO⟩ :=
    (ComputableInPolyTime.bool_not :
      ComputableInPolyTime (fun b : Bool ↦ !b) encBool encBool).exists_computableInO
  let C₀ := max (Tn false) (Tn true)
  have hcomp := hnO.comp hind
  have hT_le : ∀ a : α, T (enc a).length + Tn (indicator L a) ≤ T (enc a).length + C₀ := by
    intro a; apply Nat.add_le_add_left
    cases indicator L a <;> [exact le_max_left _ _; exact le_max_right _ _]
  have hmem' : {a | !(indicator L a) = true} ∈ DTIME enc (fun n ↦ T n + C₀) :=
    setOf_mem_DTIME_of_computableInO hcomp hT_le
  have hset : {a | !(indicator L a) = true} = Lᶜ := by
    ext a
    change !(indicator L a) = true ↔ a ∉ L
    simp only [Bool.not_eq_true']
    by_cases ha : a ∈ L
    · simp [indicator, ha]
    · simp [indicator, ha]
  rw [hset] at hmem'
  exact DTIME_mono_of_le_mul_add (C := C₀ + 1) (fun n ↦ by
    have : T n + C₀ ≤ (C₀ + 1) * T n + (C₀ + 1) := by nlinarith
    exact this) hmem'

/-- Every language in `P` lies in `QPTIME`. -/
theorem P_subset_QPTIME {α : Type} (enc : α ↪ List Bool) : P enc ⊆ QPTIME enc := by
  intro L h
  obtain ⟨k, hDT⟩ := mem_P_iff_exists_mem_DTIME.mp h
  have h1 : L ∈ DTIME enc (fun n ↦ (n + 1) ^ k) :=
    DTIME_mono (fun n ↦ Nat.pow_le_pow_left (Nat.le_succ n) k) hDT
  have hind := computableInO_indicator_of_mem_DTIME h1
  have hset : L = {a | indicator L a = true} := by
    ext a; simp [indicator]
  rw [hset]
  exact mem_QPTIME_of_exp_natLog_pow hind 1 k 0 fun a ↦ by
    simpa only [pow_zero, mul_one, one_mul] using
      Nat.le_mul_of_pos_left (((enc a).length + 1) ^ k) (Nat.pos_of_ne_zero (by positivity))

end Cslib.Complexity
