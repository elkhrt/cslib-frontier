module

public import CslibFrontier.Computability.Communication.DirectProduct.BalancedSplit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Razborov's Fixed-Weight Lemma and the Intersection Sampling Lemma

Rectangle measure comparison theorems under the fixed-weight intersection distributions `μ_{k,n,m}`:

* `razborov_main_four_fifths` and `razborov_main_fixedWeight`: for every combinatorial rectangle
  `R = A × B`, the `1`-intersection mass `μ_{1,n,m}(R)` is bounded below by a constant multiple of
  `μ_{0,n,m}(R)` minus an exponentially small error `2 ^ (-δ n)`.
* `intersection_sampling_inductive`: inductive lower bound comparing `μ_{k,n,m}(R)` to
  `μ_{0,n,m}(R)` for every `k ≥ 1`.
* `intersection_sampling_three_fourths` and `intersection_sampling`: uniform `(3 / 4) ^ k` and
  `(1 / 2) ^ k` lower bounds on `μ_{k,n,m}(R)` for sufficiently small `k / n`.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Finset

/-! ### Razborov's Main Lemma for Fixed-Weight Distributions -/

/-- Explicit universal exponent constant `δ = 2 ^ (-42)` for the fixed-weight Razborov bound. -/
@[expose] noncomputable def deltaRaz : ℝ := (2 : ℝ) ^ (-42 : ℤ)

/-- Numeric value of `deltaRaz`. -/
theorem deltaRaz_eq_zpow : deltaRaz = (2 : ℝ) ^ (-42 : ℤ) := rfl

/-- `deltaRaz` is strictly positive. -/
theorem deltaRaz_pos : 0 < deltaRaz := by
  unfold deltaRaz; positivity

/-- Elementary fourth-root bound on the natural logarithm: `ln x ≤ 4 * x ^ (1/4)` via two square
roots, without needing calculus. -/
private theorem log_le_four_mul_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have hy0 : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)
  have hy4 : (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
    calc (Real.sqrt (Real.sqrt x)) ^ 4
        = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
      _ = x := Real.sq_sqrt hx.le
  have hlog : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    conv_lhs => rw [← hy4]
    rw [Real.log_pow]
    norm_num
  rw [hlog]
  linarith [Real.log_le_sub_one_of_pos hy0]

/-- Quantitative coefficient bound for the sub-Gaussian tail term in Razborov's main lemma when
`n > 2 ^ 40`, `m ∈ [n / 4 - δ n, n / 4]`, and `s ∈ [n / 2, n / 2 + 1]`. -/
private theorem razborov_coeff_le {n m s : ℕ} (hn_large : (2 : ℝ) ^ (40 : ℕ) < (n : ℝ))
    (hm_lo : (n : ℝ) / 4 - deltaRaz * (n : ℝ) ≤ (m : ℝ))
    (hm_hi : (m : ℝ) ≤ (n : ℝ) / 4)
    (hs_lo : (n : ℝ) / 2 ≤ (s : ℝ)) (hs_hi : (s : ℝ) ≤ (n : ℝ) / 2 + 1) :
    (1 / ((1 / 20 : ℝ) * ((m : ℝ) / (s : ℝ)) * (1 - (m : ℝ) / (s : ℝ))) *
      Real.sqrt (Real.log (((s : ℝ) + 1) / (2 : ℝ) ^ (-30 * deltaRaz * (n : ℝ))) / (s : ℝ))) ≤
      1 / 40 := by
  have hδ_val : deltaRaz = 1 / (2 : ℝ) ^ (42 : ℕ) := by unfold deltaRaz; norm_num
  set ε : ℝ := 1 / 20
  set τ : ℝ := (2 : ℝ) ^ (-30 * deltaRaz * (n : ℝ))
  have hτ0 : 0 < τ := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) hn_large
  have hs0 : (0 : ℝ) < s := by linarith
  set p : ℝ := (m : ℝ) / (s : ℝ)
  have hp_lo : 1 / 3 ≤ p := by
    rw [div_le_div_iff₀ (by norm_num) hs0]
    nlinarith [show deltaRaz * (n : ℝ) ≤ (n : ℝ) / 100 by rw [hδ_val]; nlinarith]
  have hp_hi : p ≤ 2 / 3 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have hprod : 2 / 9 ≤ p * (1 - p) := by nlinarith
  have hpref : 1 / (ε * p * (1 - p)) ≤ 90 := by
    have h1 : (1 : ℝ) / 90 ≤ ε * p * (1 - p) := by dsimp only [ε]; nlinarith
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) h1)]
    have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 90)
    exact (by norm_num : (1 : ℝ) = 90 * (1 / 90)).le.trans h2
  have hlog_bound : Real.log (((s : ℝ) + 1) / τ) / (s : ℝ) ≤ (1 / 3600 : ℝ) ^ 2 := by
    have hs1_le : (s : ℝ) + 1 ≤ (n : ℝ) := by linarith
    have hlog1 : Real.log ((s : ℝ) + 1) ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := by
      refine (Real.log_le_log (by positivity) hs1_le).trans ?_
      exact log_le_four_mul_sqrt_sqrt (by positivity)
    have hlog2 : Real.log (1 / τ) = 30 * deltaRaz * (n : ℝ) * Real.log 2 := by
      dsimp only [τ]
      rw [one_div, ← Real.rpow_neg zero_le_two, neg_mul, neg_mul, neg_neg, Real.log_rpow two_pos]
    have hlog_split : Real.log (((s : ℝ) + 1) / τ) =
        Real.log ((s : ℝ) + 1) + Real.log (1 / τ) := by
      rw [div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity)]
    have hsqrt4_bound : 4 * Real.sqrt (Real.sqrt (n : ℝ)) / ((n : ℝ) / 2) ≤
        8 / (2 : ℝ) ^ (30 : ℕ) := by
      have h1 : (2 : ℝ) ^ (30 : ℕ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
        have h10 : (2 : ℝ) ^ (10 : ℕ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
          have h20 : (2 : ℝ) ^ (20 : ℕ) ≤ Real.sqrt (n : ℝ) := by
            rw [Real.le_sqrt (by positivity) hn_pos.le]
            have : ((2 : ℝ) ^ (20 : ℕ)) ^ 2 = (2 : ℝ) ^ (40 : ℕ) := by norm_num
            linarith
          rw [Real.le_sqrt (by positivity) (Real.sqrt_nonneg _)]
          have : ((2 : ℝ) ^ (10 : ℕ)) ^ 2 = (2 : ℝ) ^ (20 : ℕ) := by norm_num
          linarith
        calc (2 : ℝ) ^ (30 : ℕ) = ((2 : ℝ) ^ (10 : ℕ)) ^ 3 := by norm_num
          _ ≤ (Real.sqrt (Real.sqrt (n : ℝ))) ^ 3 := pow_le_pow_left₀ (by positivity) h10 3
      have hn_eq : (n : ℝ) = (Real.sqrt (Real.sqrt (n : ℝ))) ^ 4 := by
        calc (n : ℝ) = (Real.sqrt (n : ℝ)) ^ 2 := (Real.sq_sqrt hn_pos.le).symm
          _ = ((Real.sqrt (Real.sqrt (n : ℝ))) ^ 2) ^ 2 := by
            rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
          _ = (Real.sqrt (Real.sqrt (n : ℝ))) ^ 4 := by ring
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc 4 * Real.sqrt (Real.sqrt (n : ℝ)) * (2 : ℝ) ^ (30 : ℕ)
          ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) * (Real.sqrt (Real.sqrt (n : ℝ))) ^ 3 := by gcongr
        _ = 4 * (n : ℝ) := by
          conv_rhs => rw [hn_eq]
          ring
        _ = 8 * ((n : ℝ) / 2) := by ring
    have hln2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos two_pos]
    calc
      Real.log (((s : ℝ) + 1) / τ) / (s : ℝ)
        ≤ Real.log (((s : ℝ) + 1) / τ) / ((n : ℝ) / 2) := by
          have hnum_nn : 0 ≤ Real.log (((s : ℝ) + 1) / τ) := by
            apply Real.log_nonneg
            rw [one_le_div hτ0]
            have hτ1 : τ ≤ 1 := by
              dsimp only [τ]
              exact Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by nlinarith [deltaRaz_pos])
            linarith
          gcongr
      _ = 4 * Real.sqrt (Real.sqrt (n : ℝ)) / ((n : ℝ) / 2) +
            (Real.log ((s : ℝ) + 1) - 4 * Real.sqrt (Real.sqrt (n : ℝ))) / ((n : ℝ) / 2) +
            60 * deltaRaz * Real.log 2 := by
          rw [hlog_split, hlog2]; field_simp; ring
      _ ≤ 8 / (2 : ℝ) ^ (30 : ℕ) + 0 + 60 * deltaRaz * 1 := by
          have hsub0 : (Real.log ((s : ℝ) + 1) - 4 * Real.sqrt (Real.sqrt (n : ℝ))) /
              ((n : ℝ) / 2) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
          have h60 : 60 * deltaRaz * Real.log 2 ≤ 60 * deltaRaz * 1 :=
            mul_le_mul_of_nonneg_left hln2 (by positivity)
          linarith
      _ ≤ (1 / 3600 : ℝ) ^ 2 := by rw [hδ_val]; norm_num
  have hsqrt : Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ)) ≤ 1 / 3600 := by
    rw [show (1 / 3600 : ℝ) = Real.sqrt ((1 / 3600 : ℝ) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hlog_bound
  calc
    1 / (ε * p * (1 - p)) * Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ))
      ≤ 90 * (1 / 3600) := mul_le_mul hpref hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ = 1 / 40 := by norm_num

/-- Strong Razborov main lemma with constant `4 / 5`:
for `δ = 2 ^ (-42)`, every `n ≥ 1`, every `m ∈ [n / 4 - δ n, n / 4]`, and every rectangle
`R = A × B` with `μ_{0,n,m}(R) ≥ 2 ^ (-δ n)`, we have `μ_{1,n,m}(R) ≥ (4 / 5) * μ_{0,n,m}(R)`. -/
theorem razborov_main_four_fifths {n m : ℕ} (hn : 1 ≤ n)
    (hm_lo : (n : ℝ) / 4 - deltaRaz * (n : ℝ) ≤ (m : ℝ))
    (hm_hi : (m : ℝ) ≤ (n : ℝ) / 4)
    (A B : Finset (BitString n))
    (hbig : (2 : ℝ) ^ (-deltaRaz * (n : ℝ)) ≤ muRect 0 n m A B) :
    (4 / 5 : ℝ) * muRect 0 n m A B ≤ muRect 1 n m A B := by
  have hδ_val : deltaRaz = 1 / (2 : ℝ) ^ (42 : ℕ) := by
    unfold deltaRaz; norm_num
  have hδ_pos : 0 < deltaRaz := deltaRaz_pos
  have hδ_lt : deltaRaz < 1 / 12 := by rw [hδ_val]; norm_num
  have hn4 : 4 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n
    · have : (0 : ℝ) < (m : ℝ) := by linarith
      have : (m : ℝ) < 1 := by linarith
      have hm1 : 1 ≤ m := by exact_mod_cast (show (0 : ℝ) < m from by linarith)
      have hm0 : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 from by linarith)
      omega
    · have : (0 : ℝ) < (m : ℝ) := by linarith
      have : (m : ℝ) < 1 := by linarith
      have hm1 : 1 ≤ m := by exact_mod_cast (show (0 : ℝ) < m from by linarith)
      have hm0 : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 from by linarith)
      omega
    · have : (0 : ℝ) < (m : ℝ) := by linarith
      have : (m : ℝ) < 1 := by linarith
      have hm1 : 1 ≤ m := by exact_mod_cast (show (0 : ℝ) < m from by linarith)
      have hm0 : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 from by linarith)
      omega
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < (m : ℝ) := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      nlinarith
    exact_mod_cast this
  have h4m : 4 * m ≤ n := by
    have : (4 * m : ℝ) ≤ n := by linarith
    exact_mod_cast this
  -- Case 1: small `n ≤ 2 ^ 40`, where `2 ^ (-δ n) ≥ 2 ^ (-1/4) > 5/6` and the marginal union bound
  -- suffices immediately.
  by_cases hsmall : n ≤ 2 ^ 40
  · have hexp : -((1 : ℝ) / 4) ≤ -deltaRaz * (n : ℝ) := by
      have hnR : (n : ℝ) ≤ (2 : ℝ) ^ (40 : ℕ) := by exact_mod_cast hsmall
      rw [hδ_val]
      nlinarith [show (1 / (2 : ℝ) ^ (42 : ℕ)) * (2 : ℝ) ^ (40 : ℕ) = 1 / 4 by norm_num]
    have h56 : (5 / 6 : ℝ) ≤ (2 : ℝ) ^ (-((1 : ℝ) / 4)) := by
      have hpow : ((5 / 6 : ℝ) ^ (4 : ℕ)) ≤ ((2 : ℝ) ^ (-((1 : ℝ) / 4))) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul zero_le_two]
        norm_num
      have hnonneg : 0 ≤ (2 : ℝ) ^ (-((1 : ℝ) / 4)) := by positivity
      by_contra hlt
      push Not at hlt
      have : ((2 : ℝ) ^ (-((1 : ℝ) / 4))) ^ (4 : ℕ) < (5 / 6 : ℝ) ^ (4 : ℕ) :=
        pow_lt_pow_left₀ hlt hnonneg (by norm_num)
      linarith
    have hmu56 : (5 / 6 : ℝ) ≤ muRect 0 n m A B :=
      h56.trans ((Real.rpow_le_rpow_of_exponent_le one_le_two hexp).trans hbig)
    have hunion := muRect_one_ge_two_mul_sub_one hm1 (by omega) A B
    linarith
  -- Case 2: large `n > 2 ^ 40`, using balanced splits and `bad_coord_mass_bound`.
  · push Not at hsmall
    have hn_large : (2 : ℝ) ^ (40 : ℕ) < (n : ℝ) := by exact_mod_cast hsmall
    set ε : ℝ := 1 / 20
    set τ : ℝ := (2 : ℝ) ^ (-30 * deltaRaz * (n : ℝ))
    have hε : 0 < ε := by positivity
    have hτ0 : 0 < τ := by positivity
    set k₁ := (n - 1) / 2
    set k₂ := n / 2
    have hmk1 : m ≤ k₁ := by omega
    have hmk2 : m ≤ k₂ := by omega
    -- Bound the square-root coefficient on both sides (`s = k₁ + 1` and `s = k₂ + 1`).
    have hcoeff_side : ∀ s : ℕ, (n : ℝ) / 2 ≤ (s : ℝ) → (s : ℝ) ≤ (n : ℝ) / 2 + 1 →
        (1 / (ε * ((m : ℝ) / (s : ℝ)) * (1 - (m : ℝ) / (s : ℝ))) *
          Real.sqrt (Real.log (((s : ℝ) + 1) / τ) / (s : ℝ))) ≤ 1 / 40 :=
      fun _ hs_lo hs_hi => razborov_coeff_le hn_large hm_lo hm_hi hs_lo hs_hi
    -- Bad splits for Alice (`qSide A T.left T.point m < (1 - ε) * pSide A T.left m`).
    have hbadA : (∑ T ∈ splits n with
        qSide A T.left T.point m < (1 - ε) * pSide A T.left m,
        pSide A T.left m * pSide B T.right m) / ((splits n).card : ℝ) ≤
        (1 / 40 : ℝ) * muRect 0 n m A B + τ := by
      have hsp_pos : (0 : ℝ) < (splits n).card := Nat.cast_pos.mpr (card_splits_pos hn)
      rw [muRect_zero_eq_avg_splits hn hmk1 A B, sum_filter, sum_splits_right hn,
        sum_splits_right hn]
      rw [mul_div_assoc', ← mul_div_cancel_right₀ τ hsp_pos.ne', ← add_div]
      gcongr
      have hcard_eq : ((splits n).card : ℝ) =
          ∑ _Ty ∈ (univ : Finset (Fin n)).powersetCard k₂, ((k₁ + 1 : ℕ) : ℝ) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul,
          card_splits hn]
        push_cast; ring
      rw [hcard_eq, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun Ty hTy => ?_
      have hTyc : Ty.card = k₂ := (mem_powersetCard.mp hTy).2
      have hSc : Tyᶜ.card = k₁ + 1 := by rw [card_compl, Fintype.card_fin, hTyc]; omega
      have hbadS := bad_coord_mass_bound A Tyᶜ hm1 (by omega) hε hτ0
      have hcoeffS := hcoeff_side Tyᶜ.card
        (by rw [hSc]; have : n ≤ 2 * (k₁ + 1) := by omega
            have : (n : ℝ) ≤ 2 * ((k₁ + 1 : ℕ) : ℝ) := by exact_mod_cast this
            linarith)
        (by rw [hSc]; have : 2 * k₁ ≤ n := by omega
            have : (2 * k₁ : ℝ) ≤ n := by exact_mod_cast this
            push_cast; linarith)
      have hbadS' : (∑ i ∈ Tyᶜ with
          qSide A (Tyᶜ.erase i) i m < (1 - ε) * pSide A (Tyᶜ.erase i) m,
          pSide A (Tyᶜ.erase i) m) / (Tyᶜ.card : ℝ) ≤ (1 / 40 : ℝ) * pSide A Tyᶜ m + τ := by
        have hnn : 0 ≤ pSide A Tyᶜ m := pSide_nonneg A Tyᶜ m
        have := mul_le_mul_of_nonneg_right hcoeffS hnn
        linarith
      have havgS := avg_pSide_erase A Tyᶜ (by omega : m < Tyᶜ.card)
      rw [← havgS] at hbadS'
      have hSc_pos : (0 : ℝ) < Tyᶜ.card := Nat.cast_pos.mpr (by omega)
      have hbadS_mul : (∑ i ∈ Tyᶜ with
          qSide A (Tyᶜ.erase i) i m < (1 - ε) * pSide A (Tyᶜ.erase i) m,
          pSide A (Tyᶜ.erase i) m) ≤
          (1 / 40 : ℝ) * (∑ i ∈ Tyᶜ, pSide A (Tyᶜ.erase i) m) + (Tyᶜ.card : ℝ) * τ := by
        have h := mul_le_mul_of_nonneg_right hbadS' hSc_pos.le
        rw [div_mul_cancel₀ _ hSc_pos.ne', add_mul, mul_div_assoc',
          div_mul_cancel₀ _ hSc_pos.ne', mul_comm τ] at h
        exact h
      have hpb0 : 0 ≤ pSide B Ty m := pSide_nonneg B Ty m
      have hpb1 : pSide B Ty m ≤ 1 := pSide_le_one B Ty m
      calc
        ∑ i ∈ Tyᶜ, (if qSide A (Tyᶜ.erase i) i m < (1 - ε) * pSide A (Tyᶜ.erase i) m then
            pSide A (Tyᶜ.erase i) m * pSide B Ty m else 0)
          = (∑ i ∈ Tyᶜ with qSide A (Tyᶜ.erase i) i m < (1 - ε) * pSide A (Tyᶜ.erase i) m,
              pSide A (Tyᶜ.erase i) m) * pSide B Ty m := by
            rw [sum_filter, sum_mul]
            refine sum_congr rfl fun i _ => by split_ifs <;> ring
        _ ≤ ((1 / 40 : ℝ) * (∑ i ∈ Tyᶜ, pSide A (Tyᶜ.erase i) m) +
              (Tyᶜ.card : ℝ) * τ) * pSide B Ty m :=
            mul_le_mul_of_nonneg_right hbadS_mul hpb0
        _ ≤ (1 / 40 : ℝ) * (∑ i ∈ Tyᶜ, pSide A (Tyᶜ.erase i) m * pSide B Ty m) +
              τ * ((k₁ + 1 : ℕ) : ℝ) := by
            rw [← sum_mul, hSc]
            nlinarith [show (0 : ℝ) ≤ ((k₁ + 1 : ℕ) : ℝ) * τ by positivity]
    -- Symmetrically, bad splits for Bob (`qSide B T.right T.point m < (1 - ε) * pSide B T.right
    -- m`).
    have hbadB : (∑ T ∈ splits n with
        qSide B T.right T.point m < (1 - ε) * pSide B T.right m,
        pSide A T.left m * pSide B T.right m) / ((splits n).card : ℝ) ≤
        (1 / 40 : ℝ) * muRect 0 n m A B + τ := by
      have hsp_pos : (0 : ℝ) < (splits n).card := Nat.cast_pos.mpr (card_splits_pos hn)
      rw [muRect_zero_eq_avg_splits hn hmk1 A B, sum_filter, sum_splits_left hn,
        sum_splits_left hn]
      rw [mul_div_assoc', ← mul_div_cancel_right₀ τ hsp_pos.ne', ← add_div]
      gcongr
      have hcard_eq : ((splits n).card : ℝ) =
          ∑ _Tx ∈ (univ : Finset (Fin n)).powersetCard k₁, ((k₂ + 1 : ℕ) : ℝ) := by
        have hnat : (splits n).card = n.choose k₁ * (k₂ + 1) := by
          rw [card_eq_sum_ones, sum_splits_left hn]
          simp only [sum_const, smul_eq_mul, mul_one]
          rw [sum_congr rfl fun Tx hTx => by
              rw [card_compl, Fintype.card_fin, (mem_powersetCard.mp hTx).2],
            sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
          congr 1; omega
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, hnat]
        push_cast; ring
      rw [hcard_eq, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun Tx hTx => ?_
      have hTxc : Tx.card = k₁ := (mem_powersetCard.mp hTx).2
      have hSc : Txᶜ.card = k₂ + 1 := by rw [card_compl, Fintype.card_fin, hTxc]; omega
      have hbadS := bad_coord_mass_bound B Txᶜ hm1 (by omega) hε hτ0
      have hcoeffS := hcoeff_side Txᶜ.card
        (by rw [hSc]; have : n ≤ 2 * (k₂ + 1) := by omega
            have : (n : ℝ) ≤ 2 * ((k₂ + 1 : ℕ) : ℝ) := by exact_mod_cast this
            linarith)
        (by rw [hSc]; have : 2 * k₂ ≤ n := by omega
            have : (2 * k₂ : ℝ) ≤ n := by exact_mod_cast this
            push_cast; linarith)
      have hbadS' : (∑ i ∈ Txᶜ with
          qSide B (Txᶜ.erase i) i m < (1 - ε) * pSide B (Txᶜ.erase i) m,
          pSide B (Txᶜ.erase i) m) / (Txᶜ.card : ℝ) ≤ (1 / 40 : ℝ) * pSide B Txᶜ m + τ := by
        have hnn : 0 ≤ pSide B Txᶜ m := pSide_nonneg B Txᶜ m
        have := mul_le_mul_of_nonneg_right hcoeffS hnn
        linarith
      have havgS := avg_pSide_erase B Txᶜ (by omega : m < Txᶜ.card)
      rw [← havgS] at hbadS'
      have hSc_pos : (0 : ℝ) < Txᶜ.card := Nat.cast_pos.mpr (by omega)
      have hbadS_mul : (∑ i ∈ Txᶜ with
          qSide B (Txᶜ.erase i) i m < (1 - ε) * pSide B (Txᶜ.erase i) m,
          pSide B (Txᶜ.erase i) m) ≤
          (1 / 40 : ℝ) * (∑ i ∈ Txᶜ, pSide B (Txᶜ.erase i) m) + (Txᶜ.card : ℝ) * τ := by
        have h := mul_le_mul_of_nonneg_right hbadS' hSc_pos.le
        rw [div_mul_cancel₀ _ hSc_pos.ne', add_mul, mul_div_assoc',
          div_mul_cancel₀ _ hSc_pos.ne', mul_comm τ] at h
        exact h
      have hpa0 : 0 ≤ pSide A Tx m := pSide_nonneg A Tx m
      have hpa1 : pSide A Tx m ≤ 1 := pSide_le_one A Tx m
      calc
        ∑ i ∈ Txᶜ, (if qSide B (Txᶜ.erase i) i m < (1 - ε) * pSide B (Txᶜ.erase i) m then
            pSide A Tx m * pSide B (Txᶜ.erase i) m else 0)
          = pSide A Tx m * (∑ i ∈ Txᶜ with
              qSide B (Txᶜ.erase i) i m < (1 - ε) * pSide B (Txᶜ.erase i) m,
              pSide B (Txᶜ.erase i) m) := by
            rw [sum_filter, mul_sum]
            refine sum_congr rfl fun i _ => by split_ifs <;> ring
        _ ≤ pSide A Tx m * ((1 / 40 : ℝ) * (∑ i ∈ Txᶜ, pSide B (Txᶜ.erase i) m) +
              (Txᶜ.card : ℝ) * τ) :=
            mul_le_mul_of_nonneg_left hbadS_mul hpa0
        _ ≤ (1 / 40 : ℝ) * (∑ i ∈ Txᶜ, pSide A Tx m * pSide B (Txᶜ.erase i) m) +
              τ * ((k₂ + 1 : ℕ) : ℝ) := by
            rw [← mul_sum, hSc]
            nlinarith [show (0 : ℝ) ≤ ((k₂ + 1 : ℕ) : ℝ) * τ by positivity]
    -- Combine good splits.
    have hpt_good : ∀ T ∈ splits n,
        (1 - ε) ^ 2 * (pSide A T.left m * pSide B T.right m) ≤
          qSide A T.left T.point m * qSide B T.right T.point m +
            (1 - ε) ^ 2 *
              ((if qSide A T.left T.point m < (1 - ε) * pSide A T.left m then
                  pSide A T.left m * pSide B T.right m else 0) +
               (if qSide B T.right T.point m < (1 - ε) * pSide B T.right m then
                  pSide A T.left m * pSide B T.right m else 0)) := by
      intro T _
      have ha0 := pSide_nonneg A T.left m
      have hb0 := pSide_nonneg B T.right m
      have hqa0 : 0 ≤ qSide A T.left T.point m := qSide_nonneg A T.left T.point m
      have hqb0 : 0 ≤ qSide B T.right T.point m := qSide_nonneg B T.right T.point m
      by_cases ha : qSide A T.left T.point m < (1 - ε) * pSide A T.left m <;>
        by_cases hb : qSide B T.right T.point m < (1 - ε) * pSide B T.right m <;>
        simp only [ha, hb, ↓reduceIte, add_zero, zero_add]
      · nlinarith only [mul_nonneg ha0 hb0, mul_nonneg hqa0 hqb0, sq_nonneg (1 - ε)]
      · linarith only [mul_nonneg hqa0 hqb0]
      · linarith only [mul_nonneg hqa0 hqb0]
      · push Not at ha hb
        have hmul := mul_le_mul ha hb (by positivity) (by positivity)
        have heq : (1 - ε) ^ 2 * (pSide A T.left m * pSide B T.right m) =
            (1 - ε) * pSide A T.left m * ((1 - ε) * pSide B T.right m) := by ring
        linarith only [hmul, heq]
    have hsp_pos : (0 : ℝ) < (splits n).card := Nat.cast_pos.mpr (card_splits_pos hn)
    have havg_good : (1 - ε) ^ 2 * muRect 0 n m A B ≤
        muRect 1 n m A B + (1 - ε) ^ 2 * (2 * ((1 / 40 : ℝ) * muRect 0 n m A B + τ)) := by
      have hsum := sum_le_sum hpt_good
      rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_add_distrib, ← sum_filter, ← sum_filter]
        at hsum
      have hdiv := div_le_div_of_nonneg_right hsum hsp_pos.le
      rw [mul_div_assoc, add_div, mul_div_assoc, add_div,
        ← muRect_zero_eq_avg_splits hn hmk1 A B,
        ← muRect_one_eq_avg_splits hn hm1 (by omega) A B] at hdiv
      nlinarith only [hdiv, hbadA, hbadB, sq_nonneg (1 - ε)]
    -- Since `n > 2 ^ 40` and `δ = 2 ^ (-42)`, `29 * δ * n > 7`, so `τ < 2 ^ (-7) * μ_0(R)`.
    have hτ_le : τ ≤ (1 / 128 : ℝ) * muRect 0 n m A B := by
      have h29 : (7 : ℝ) ≤ 29 * deltaRaz * (n : ℝ) := by
        rw [hδ_val]
        nlinarith [show (29 : ℝ) * (1 / (2 : ℝ) ^ (42 : ℕ)) * (2 : ℝ) ^ (40 : ℕ) = 29 / 4 by
          norm_num]
      calc
        τ = (2 : ℝ) ^ (-29 * deltaRaz * (n : ℝ)) * (2 : ℝ) ^ (-deltaRaz * (n : ℝ)) := by
            dsimp only [τ]
            rw [← Real.rpow_add two_pos]
            congr 1; ring
        _ ≤ (2 : ℝ) ^ (-7 : ℝ) * muRect 0 n m A B :=
            mul_le_mul (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) hbig
              (by positivity) (by positivity)
        _ = (1 / 128 : ℝ) * muRect 0 n m A B := by
            rw [show (-7 : ℝ) = ((-7 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    have h19 : (1 - (1 / 20 : ℝ)) ^ 2 = 361 / 400 := by norm_num
    dsimp only [ε] at havg_good
    rw [h19] at havg_good
    linarith only [havg_good, hτ_le, muRect_nonneg 0 n m A B]

/-- Razborov's main lemma for fixed-weight distributions `μ_{0,n,m}` and `μ_{1,n,m}`:
There is a constant `δ > 0` such that for all `n ≥ 1`, all `m ∈ [n / 4 - δ n, n / 4]`, and every
rectangle `R = A × B` with `μ_{0,n,m}(R) ≥ 2 ^ (-δ n)`, we have
`μ_{1,n,m}(R) ≥ μ_{0,n,m}(R) / (3 / 2)`. -/
theorem razborov_main_fixedWeight :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n m : ℕ), 1 ≤ n →
      (n : ℝ) / 4 - δ * (n : ℝ) ≤ (m : ℝ) → (m : ℝ) ≤ (n : ℝ) / 4 →
      ∀ (A B : Finset (BitString n)),
        (2 : ℝ) ^ (-δ * (n : ℝ)) ≤ muRect 0 n m A B →
        muRect 0 n m A B / (3 / 2 : ℝ) ≤ muRect 1 n m A B := by
  refine ⟨deltaRaz, deltaRaz_pos, fun n m hn hlo hhi A B hbig => ?_⟩
  have h := razborov_main_four_fifths hn hlo hhi A B hbig
  linarith [muRect_nonneg 0 n m A B]

/-! ### Inductive and Uniform Intersection Sampling Lemmas -/

/-- Double-counting identity for `μ_{k,n,m}(R)` over `k`-element subsets `I`:
every pair in `T_{k,n} ∩ R` lies in a unique slice `R_I`. -/
private theorem sum_muRect_slice {n k m : ℕ} (A B : Finset (BitString n)) :
    ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
      muRect k n m (sliceSide I A) (sliceSide I B) = muRect k n m A B := by
  classical
  simp_rw [muRect_eq_sum]
  calc
    ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
        ∑ x ∈ sliceSide I A, ∑ y ∈ sliceSide I B, muWeight k n m x y
      = ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
          ∑ x ∈ A, ∑ y ∈ B,
            if I ⊆ interSet x y then muWeight k n m x y else 0 := by
        refine sum_congr rfl fun I _ => ?_
        rw [sum_sliceSide]
        refine sum_congr rfl fun x _ => ?_
        split_ifs with hx
        · rw [sum_sliceSide]
          refine sum_congr rfl fun y _ => ?_
          simp only [interSet_eq_inter, subset_inter_iff, hx, true_and]
        · rw [eq_comm, sum_eq_zero]
          intro y _
          simp only [interSet_eq_inter, subset_inter_iff, hx, false_and, ↓reduceIte]
    _ = ∑ x ∈ A, ∑ y ∈ B,
          ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
            if I ⊆ interSet x y then muWeight k n m x y else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_comm
    _ = ∑ x ∈ A, ∑ y ∈ B, muWeight k n m x y := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        by_cases hmem : (x, y) ∈ weightPairs k n m
        · have hcard : (interSet x y).card = k := (mem_weightPairs.mp hmem).2.2
          have huniq : ∀ I ∈ (univ : Finset (Fin n)).powersetCard k,
              I ⊆ interSet x y ↔ I = interSet x y := fun I hI =>
            ⟨fun hsub => eq_of_subset_of_card_le hsub (by rw [(mem_powersetCard.mp hI).2, hcard]),
              fun heq => heq ▸ Subset.rfl⟩
          rw [sum_congr rfl fun I hI => by rw [if_congr (huniq I hI) rfl rfl]]
          rw [sum_ite_eq']
          simp [mem_powersetCard, hcard]
        · rw [muWeight_eq_zero_of_notMem hmem]
          simp

/-- Double-counting identity for `μ_{k+1,n,m}(R)` over `k`-element subsets `I`:
every pair in `T_{k+1,n} ∩ R` lies in exactly `k + 1` slices `R_I`. -/
private theorem sum_muRect_slice_succ {n k m : ℕ} (A B : Finset (BitString n)) :
    (∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
        muRect (k + 1) n m (sliceSide I A) (sliceSide I B)) / ((k + 1 : ℕ) : ℝ) =
      muRect (k + 1) n m A B := by
  classical
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  simp_rw [muRect_eq_sum]
  rw [eq_comm, eq_div_iff hk1, sum_mul]
  calc
    ∑ x ∈ A, (∑ y ∈ B, muWeight (k + 1) n m x y) * ((k + 1 : ℕ) : ℝ)
      = ∑ x ∈ A, ∑ y ∈ B,
          ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
            if I ⊆ interSet x y then muWeight (k + 1) n m x y else 0 := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun y _ => ?_
        by_cases hmem : (x, y) ∈ weightPairs (k + 1) n m
        · have hcard : (interSet x y).card = k + 1 := (mem_weightPairs.mp hmem).2.2
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
          congr 1
          have hfl : ((univ : Finset (Fin n)).powersetCard k).filter (fun I => I ⊆ interSet x y) =
              (interSet x y).powersetCard k := by
            ext I; simp only [mem_filter, mem_powersetCard, subset_univ, true_and]; tauto
          rw [hfl, card_powersetCard, hcard, Nat.choose_succ_self_right]
        · rw [muWeight_eq_zero_of_notMem hmem, zero_mul]
          simp
    _ = ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
          ∑ x ∈ A, ∑ y ∈ B,
            if I ⊆ interSet x y then muWeight (k + 1) n m x y else 0 := by
        trans ∑ x ∈ A, ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
            ∑ y ∈ B, if I ⊆ interSet x y then muWeight (k + 1) n m x y else 0
        · exact sum_congr rfl fun x _ => sum_comm
        · exact sum_comm
    _ = ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
          ∑ x ∈ sliceSide I A, ∑ y ∈ sliceSide I B, muWeight (k + 1) n m x y := by
        refine sum_congr rfl fun I _ => ?_
        rw [sum_sliceSide]
        refine sum_congr rfl fun x _ => ?_
        split_ifs with hx
        · rw [sum_sliceSide]
          refine sum_congr rfl fun y _ => ?_
          simp only [interSet_eq_inter, subset_inter_iff, hx, true_and]
        · rw [sum_eq_zero]
          intro y _
          simp only [interSet_eq_inter, subset_inter_iff, hx, false_and, ↓reduceIte]

/-- Explicit constant `γ = δ / 6` for the Intersection Sampling Lemma. -/
@[expose] noncomputable def gammaISL : ℝ := deltaRaz / 6

/-- Formula expressing `gammaISL` in terms of `deltaRaz`. -/
theorem gammaISL_eq_div : gammaISL = deltaRaz / 6 := rfl

/-- `gammaISL ≤ 1`. -/
theorem gammaISL_le_one : gammaISL ≤ 1 := by
  unfold gammaISL deltaRaz; norm_num

/-- `gammaISL / 2 ≤ 1 / 8`. -/
theorem gammaISL_div_two_le : gammaISL / 2 ≤ 1 / 8 := by
  unfold gammaISL deltaRaz; norm_num

/-- `gammaISL` is strictly positive. -/
theorem gammaISL_pos : 0 < gammaISL := by
  unfold gammaISL; linarith [deltaRaz_pos]

/-- Generic inductive step of the Intersection Sampling Lemma with ratio `ρ ∈ {1/2, 4/5}`:
from `razborov_main_four_fifths`, for any `ρ ≤ 4/5` (`0 < ρ ≤ 1`), `m = n / 4`, and
`k ≤ gammaISL * n / 2`, we obtain
`μ_{k, n, m}(R) ≥ ρ ^ k * μ_{0, n, m}(R) - k * 2 ^ (-deltaRaz * (n - k + 1))`. -/
private theorem intersection_sampling_inductive_aux {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 4 / 5)
    {n k : ℕ} (hk : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2)
    (A B : Finset (BitString n)) :
    ρ ^ k * muRect 0 n (n / 4) A B -
        (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ)) ≤
      muRect k n (n / 4) A B := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hδ_val : deltaRaz = 1 / (2 : ℝ) ^ (42 : ℕ) := by
      unfold deltaRaz; norm_num
    have hγ_val : gammaISL = deltaRaz / 6 := rfl
    have hγn : gammaISL * (n : ℝ) / 2 = deltaRaz * (n : ℝ) / 12 := by rw [hγ_val]; ring
    have hk_pos : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
    have hn_large : (12 : ℝ) * (2 : ℝ) ^ (42 : ℕ) ≤ (n : ℝ) := by
      have : (1 : ℝ) ≤ deltaRaz * (n : ℝ) / 12 := by linarith only [hk, hk_pos, hγn]
      rw [hδ_val] at this
      linarith
    have hn_ge : 100 ≤ n := by
      have : (100 : ℝ) ≤ n := by linarith [show (100 : ℝ) ≤ 12 * (2 : ℝ) ^ (42 : ℕ) by norm_num]
      exact_mod_cast this
    have hk_le_n : k + 1 ≤ n / 4 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) / 8 := by
        have : deltaRaz / 12 ≤ 1 / 8 := by rw [hδ_val]; norm_num
        nlinarith only [hk, hγn, this, Nat.cast_nonneg (α := ℝ) n]
      have h4 : 8 * (k + 1) ≤ n := by exact_mod_cast (show (8 * (k + 1 : ℕ) : ℝ) ≤ n by linarith)
      omega
    have hk_prev : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2 := by
      have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    have hIH := ih hk_prev
    set m := n / 4
    set bad := ((univ : Finset (Fin n)).powersetCard k).filter fun I =>
      ∃ hI : I.card = k,
        muRect 0 (n - k) (m - k) (restrictSide I hI A) (restrictSide I hI B) <
          (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ))
    -- Equation (15): bad slices contribute at most `2 ^ (-δ (n - k))`.
    have hbad_sum : ∑ I ∈ bad, muRect k n m (sliceSide I A) (sliceSide I B) ≤
        (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) := by
      have hch_pos : (0 : ℝ) < n.choose k := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      calc
        ∑ I ∈ bad, muRect k n m (sliceSide I A) (sliceSide I B)
          ≤ ∑ _I ∈ bad, ((n.choose k : ℝ))⁻¹ * (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) := by
            refine sum_le_sum fun I hI => ?_
            obtain ⟨hIpow, hIcard, hIlt⟩ := mem_filter.mp hI
            rw [muRect_slice_sub (by omega) (by omega) hIcard A B]
            gcongr
        _ = (bad.card : ℝ) * (((n.choose k : ℝ))⁻¹ *
              (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ))) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (n.choose k : ℝ) * (((n.choose k : ℝ))⁻¹ *
              (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ))) := by
            gcongr
            have hle : bad.card ≤ ((univ : Finset (Fin n)).powersetCard k).card :=
              card_le_card (filter_subset _ _)
            rw [card_powersetCard, card_univ, Fintype.card_fin] at hle
            exact_mod_cast hle
        _ = (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hch_pos.ne', one_mul]
    -- Good slices satisfy `razborov_main_four_fifths` on `(n - k, m - k)`.
    have hgood : ∀ I ∈ (univ : Finset (Fin n)).powersetCard k, I ∉ bad →
        ρ * muRect k n m (sliceSide I A) (sliceSide I B) ≤
          muRect (k + 1) n m (sliceSide I A) (sliceSide I B) / ((k + 1 : ℕ) : ℝ) := by
      intro I hIpow hnotbad
      have hIcard : I.card = k := (mem_powersetCard.mp hIpow).2
      have hbig' : (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) ≤
          muRect 0 (n - k) (m - k) (restrictSide I hIcard A) (restrictSide I hIcard B) := by
        by_contra hlt
        push Not at hlt
        exact hnotbad (mem_filter.mpr ⟨hIpow, hIcard, hlt⟩)
      have hm_hi' : ((m - k : ℕ) : ℝ) ≤ ((n - k : ℕ) : ℝ) / 4 := by
        have : 4 * (m - k) ≤ n - k := by omega
        have : (4 * (m - k : ℕ) : ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hm_lo' : ((n - k : ℕ) : ℝ) / 4 - deltaRaz * ((n - k : ℕ) : ℝ) ≤ ((m - k : ℕ) : ℝ) := by
        have h4m_ge : n ≤ 4 * m + 3 := by omega
        have h4mR : (n : ℝ) - 3 ≤ 4 * (m : ℝ) := by
          have : (n : ℝ) ≤ 4 * (m : ℝ) + 3 := by exact_mod_cast h4m_ge
          linarith
        have hmk : k ≤ m := by omega
        have hnk : k ≤ n := by omega
        rw [Nat.cast_sub hmk, Nat.cast_sub hnk]
        have hk_small : (k : ℝ) ≤ deltaRaz * (n : ℝ) / 12 := by linarith only [hk_prev, hγn]
        have h3_small : (3 : ℝ) ≤ deltaRaz * (n : ℝ) := by
          rw [hδ_val] at *
          linarith
        nlinarith [show deltaRaz ≤ 1 / 12 by rw [hδ_val]; norm_num]
      have hraz := razborov_main_four_fifths (n := n - k) (m := m - k) (by omega) hm_lo' hm_hi'
        (restrictSide I hIcard A) (restrictSide I hIcard B) hbig'
      rw [muRect_slice_sub (by omega) (by omega) hIcard A B,
        muRect_slice_succ_sub (by omega) (by omega) hIcard A B]
      have hbin_id : ((n - k : ℕ) : ℝ) * (n.choose k : ℝ) =
          ((k + 1 : ℕ) : ℝ) * (n.choose (k + 1) : ℝ) := by
        exact_mod_cast (by
          have h := Nat.choose_succ_right_eq n k
          linarith : (n - k) * n.choose k = (k + 1) * n.choose (k + 1))
      have hch0 : (0 : ℝ) < n.choose k := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      have hch1 : (0 : ℝ) < n.choose (k + 1) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      have hk10 : (0 : ℝ) < (k + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos k)
      have hratio : (((n - k : ℕ) : ℝ) / (n.choose (k + 1) : ℝ)) / ((k + 1 : ℕ) : ℝ) =
          ((n.choose k : ℝ))⁻¹ := by
        field_simp; linarith
      calc
        ρ * (((n.choose k : ℝ))⁻¹ *
            muRect 0 (n - k) (m - k) (restrictSide I hIcard A) (restrictSide I hIcard B))
          ≤ ((n.choose k : ℝ))⁻¹ *
              ((4 / 5 : ℝ) *
                muRect 0 (n - k) (m - k) (restrictSide I hIcard A) (restrictSide I hIcard B)) := by
            have hnn := muRect_nonneg 0 (n - k) (m - k) (restrictSide I hIcard A)
              (restrictSide I hIcard B)
            have h1 : ρ * muRect 0 (n - k) (m - k) (restrictSide I hIcard A)
                (restrictSide I hIcard B) ≤ (4 / 5 : ℝ) * muRect 0 (n - k) (m - k)
                (restrictSide I hIcard A) (restrictSide I hIcard B) :=
              mul_le_mul_of_nonneg_right hρ hnn
            nlinarith [inv_pos.mpr hch0]
        _ ≤ ((n.choose k : ℝ))⁻¹ *
              muRect 1 (n - k) (m - k) (restrictSide I hIcard A) (restrictSide I hIcard B) :=
            mul_le_mul_of_nonneg_left hraz (by positivity)
        _ = ((((n - k : ℕ) : ℝ) / (n.choose (k + 1) : ℝ)) *
              muRect 1 (n - k) (m - k) (restrictSide I hIcard A) (restrictSide I hIcard B)) /
              ((k + 1 : ℕ) : ℝ) := by
            rw [mul_div_right_comm, hratio]
    -- Combine Equations (16)–(23).
    have hsplit : ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
          muRect k n m (sliceSide I A) (sliceSide I B) =
        ∑ I ∈ (univ : Finset (Fin n)).powersetCard k with I ∉ bad,
          muRect k n m (sliceSide I A) (sliceSide I B) +
        ∑ I ∈ bad, muRect k n m (sliceSide I A) (sliceSide I B) := by
      have hsub : bad ⊆ (univ : Finset (Fin n)).powersetCard k := filter_subset _ _
      have hpart := (sum_sdiff hsub (f := fun I => muRect k n m (sliceSide I A) (sliceSide I B)))
      have hsdiff : (univ : Finset (Fin n)).powersetCard k \ bad =
          ((univ : Finset (Fin n)).powersetCard k).filter (fun I => I ∉ bad) := by
        ext I; simp only [mem_sdiff, mem_filter]
      rw [hsdiff] at hpart
      linarith
    have hstep : ρ * muRect k n m A B - (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) ≤
        muRect (k + 1) n m A B := by
      rw [← sum_muRect_slice_succ, sum_div]
      calc
        ρ * muRect k n m A B - (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ))
          ≤ ρ * (∑ I ∈ (univ : Finset (Fin n)).powersetCard k with I ∉ bad,
              muRect k n m (sliceSide I A) (sliceSide I B)) := by
            rw [← sum_muRect_slice, hsplit, mul_add]
            have h1 : ρ * ∑ I ∈ bad, muRect k n m (sliceSide I A) (sliceSide I B) ≤
                1 * (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) := by
              refine mul_le_mul (by linarith) hbad_sum
                (sum_nonneg fun _ _ => muRect_nonneg _ _ _ _ _) (by norm_num)
            linarith
        _ = ∑ I ∈ (univ : Finset (Fin n)).powersetCard k with I ∉ bad,
              ρ * muRect k n m (sliceSide I A) (sliceSide I B) := by rw [mul_sum]
        _ ≤ ∑ I ∈ (univ : Finset (Fin n)).powersetCard k with I ∉ bad,
              muRect (k + 1) n m (sliceSide I A) (sliceSide I B) / ((k + 1 : ℕ) : ℝ) :=
            sum_le_sum fun I hI => hgood I (mem_filter.mp hI).1 (mem_filter.mp hI).2
        _ ≤ ∑ I ∈ (univ : Finset (Fin n)).powersetCard k,
              muRect (k + 1) n m (sliceSide I A) (sliceSide I B) / ((k + 1 : ℕ) : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
              div_nonneg (muRect_nonneg _ _ _ _ _) (by positivity)
    have hpow_mono : (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      have : ((n - k : ℕ) : ℝ) ≤ ((n - k + 1 : ℕ) : ℝ) := by push_cast; linarith
      nlinarith [deltaRaz_pos]
    have hsub_eq : n - (k + 1) + 1 = n - k := by omega
    rw [hsub_eq, pow_succ']
    have hmul_ih := mul_le_mul_of_nonneg_left hIH hρ0.le
    have hρ_le1 : ρ ≤ 1 := by linarith
    have herr : ρ * ((k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ))) +
        (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) ≤
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ)) := by
      have h1 : ρ * ((k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ))) ≤
          1 * ((k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k : ℕ) : ℝ))) := by
        refine mul_le_mul hρ_le1 (mul_le_mul_of_nonneg_left hpow_mono (Nat.cast_nonneg k))
          (by positivity) (by norm_num)
      have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hk1]; linarith
    linarith

/-- Inductive Intersection Sampling Lemma:
There is a constant `γ > 0` (explicitly `gammaISL = deltaRaz / 6`) such that for `m = n / 4`,
every rectangle `R = A × B` with `μ_{0,n,m}(R) ≥ 2 ^ (-γ n)`, and all `k ≤ γ n / 2`,
`μ_{k,n,m}(R) ≥ μ_{0,n,m}(R) / 2 ^ k - k * 2 ^ (-δ (n - k + 1))`. -/
theorem intersection_sampling_inductive :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (n k : ℕ), (k : ℝ) ≤ γ * (n : ℝ) / 2 →
      ∀ (A B : Finset (BitString n)),
        (2 : ℝ) ^ (-γ * (n : ℝ)) ≤ muRect 0 n (n / 4) A B →
        muRect 0 n (n / 4) A B / (2 : ℝ) ^ k -
            (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ)) ≤
          muRect k n (n / 4) A B := by
  refine ⟨gammaISL, gammaISL_pos, fun n k hk A B _ => ?_⟩
  have h := intersection_sampling_inductive_aux (ρ := 1 / 2) (by norm_num) (by norm_num) hk A B
  simpa [one_div, inv_pow, div_eq_mul_inv, mul_comm] using h

/-- **Sharper Intersection Sampling Lemma** with base `3 / 4` (for all `k ≥ 0` with
`k ≤ gammaISL * n / 2`, matching `μ_{k,n,m}(R) ≥ (3 / 4) ^ k * μ_{0,n,m}(R)`): absorbs the
additive error term uniformly for every `k ≥ 1`, handling all small-`k` regimes. -/
theorem intersection_sampling_three_fourths {n k : ℕ}
    (hk : (k : ℝ) ≤ gammaISL * (n : ℝ) / 2) (A B : Finset (BitString n))
    (hbig : (2 : ℝ) ^ (-gammaISL * (n : ℝ)) ≤ muRect 0 n (n / 4) A B) :
    (3 / 4 : ℝ) ^ k * muRect 0 n (n / 4) A B ≤ muRect k n (n / 4) A B := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  have h := intersection_sampling_inductive_aux (ρ := 4 / 5) (by norm_num) le_rfl hk A B
  have hgap : (1 / 20 : ℝ) * (3 / 4 : ℝ) ^ (k - 1) ≤ (4 / 5 : ℝ) ^ k - (3 / 4 : ℝ) ^ k := by
    have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hkpos).symm
    have hpow : (3 / 4 : ℝ) ^ (k - 1) ≤ (4 / 5 : ℝ) ^ (k - 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    conv_rhs => rw [hk1]
    rw [pow_succ, pow_succ]
    nlinarith
  have hδ_val : deltaRaz = 1 / (2 : ℝ) ^ (42 : ℕ) := by
    unfold deltaRaz; norm_num
  have hγ_val : gammaISL = deltaRaz / 6 := rfl
  have hγn : gammaISL * (n : ℝ) / 2 = deltaRaz * (n : ℝ) / 12 := by rw [hγ_val]; ring
  have hk_le_n : k ≤ n := by
    have : (k : ℝ) ≤ (n : ℝ) := by
      have : gammaISL / 2 ≤ 1 := by rw [hγ_val, hδ_val]; norm_num
      nlinarith
    exact_mod_cast this
  have hn_large : (12 : ℝ) * (2 : ℝ) ^ (42 : ℕ) ≤ (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
    have : (1 : ℝ) ≤ deltaRaz * (n : ℝ) / 12 := by linarith only [hk, h1, hγn]
    rw [hδ_val] at this; linarith
  -- Show `k * 2 ^ (-δ (n - k + 1)) ≤ (1 / 20) * (3 / 4) ^ (k - 1) * 2 ^ (-γ n)`.
  have herr_le : (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ)) ≤
      (1 / 20 : ℝ) * (3 / 4 : ℝ) ^ (k - 1) * (2 : ℝ) ^ (-gammaISL * (n : ℝ)) := by
    have hk_pow : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have h34 : (2 : ℝ) ^ (-(k : ℝ)) ≤ (3 / 4 : ℝ) ^ (k - 1) := by
      calc (2 : ℝ) ^ (-(k : ℝ))
          = (1 / 2 : ℝ) ^ k := by
            rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, one_div, inv_pow]
        _ ≤ (1 / 2 : ℝ) ^ (k - 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ ≤ (3 / 4 : ℝ) ^ (k - 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h120 : (2 : ℝ) ^ (-5 : ℝ) ≤ 1 / 20 := by
      rw [show (-5 : ℝ) = ((-5 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    have hexp : (k : ℝ) + -deltaRaz * ((n - k + 1 : ℕ) : ℝ) ≤
        -5 + -(k : ℝ) + -gammaISL * (n : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hk_le_n, Nat.cast_one]
      have hδ1 : deltaRaz ≤ 1 := by rw [hδ_val]; norm_num
      have h5 : (5 : ℝ) ≤ (7 / 12 : ℝ) * deltaRaz * (n : ℝ) := by rw [hδ_val]; linarith
      have hk_d : (k : ℝ) ≤ deltaRaz * (n : ℝ) / 12 := by linarith only [hk, hγn]
      have hγn2 : gammaISL * (n : ℝ) = deltaRaz * (n : ℝ) / 6 := by rw [hγ_val]; ring
      nlinarith only [deltaRaz_pos, Nat.cast_nonneg (α := ℝ) k, hδ1, h5, hk_d, hγn2]
    calc
      (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ))
        ≤ (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast]; gcongr
      _ = (2 : ℝ) ^ ((k : ℝ) + -deltaRaz * ((n - k + 1 : ℕ) : ℝ)) :=
          (Real.rpow_add two_pos _ _).symm
      _ ≤ (2 : ℝ) ^ (-5 + -(k : ℝ) + -gammaISL * (n : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two hexp
      _ = (2 : ℝ) ^ (-5 : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-gammaISL * (n : ℝ)) := by
          rw [Real.rpow_add two_pos, Real.rpow_add two_pos]
      _ ≤ (1 / 20 : ℝ) * (3 / 4 : ℝ) ^ (k - 1) * (2 : ℝ) ^ (-gammaISL * (n : ℝ)) := by
          gcongr
  have hcomb : (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ)) ≤
      ((4 / 5 : ℝ) ^ k - (3 / 4 : ℝ) ^ k) * muRect 0 n (n / 4) A B := by
    calc
      (k : ℝ) * (2 : ℝ) ^ (-deltaRaz * ((n - k + 1 : ℕ) : ℝ))
        ≤ (1 / 20 : ℝ) * (3 / 4 : ℝ) ^ (k - 1) * (2 : ℝ) ^ (-gammaISL * (n : ℝ)) := herr_le
      _ ≤ (1 / 20 : ℝ) * (3 / 4 : ℝ) ^ (k - 1) * muRect 0 n (n / 4) A B := by gcongr
      _ ≤ ((4 / 5 : ℝ) ^ k - (3 / 4 : ℝ) ^ k) * muRect 0 n (n / 4) A B :=
          mul_le_mul_of_nonneg_right hgap (muRect_nonneg 0 n (n / 4) A B)
  linarith

/-- Intersection Sampling Lemma:
There is a constant `γ > 0` such that for `m = n / 4`, every rectangle `R = A × B` with
`μ_{0,n,m}(R) ≥ 2 ^ (-γ n)`, and all `k ≤ γ n / 2`, we have
`μ_{k,n,m}(R) ≥ μ_{0,n,m}(R) / 2 ^ (k + 1)`. -/
theorem intersection_sampling :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (n k : ℕ), (k : ℝ) ≤ γ * (n : ℝ) / 2 →
      ∀ (A B : Finset (BitString n)),
        (2 : ℝ) ^ (-γ * (n : ℝ)) ≤ muRect 0 n (n / 4) A B →
        muRect 0 n (n / 4) A B / (2 : ℝ) ^ (k + 1) ≤ muRect k n (n / 4) A B := by
  refine ⟨gammaISL, gammaISL_pos, fun n k hk A B hbig => ?_⟩
  have h := intersection_sampling_three_fourths hk A B hbig
  have hpow : (1 / 2 : ℝ) ^ (k + 1) ≤ (3 / 4 : ℝ) ^ k := by
    calc (1 / 2 : ℝ) ^ (k + 1)
        ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
      _ ≤ (3 / 4 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hnn := muRect_nonneg 0 n (n / 4) A B
  have hdiv : muRect 0 n (n / 4) A B / (2 : ℝ) ^ (k + 1) =
      (1 / 2 : ℝ) ^ (k + 1) * muRect 0 n (n / 4) A B := by
    rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]
  rw [hdiv]
  exact (mul_le_mul_of_nonneg_right hpow hnn).trans h

end CslibFrontier.Computability.Communication
