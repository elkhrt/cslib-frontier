/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Dual

import CslibFrontier.Computability.QueryComplexity.NisanSzegedy
import CslibFrontier.Computability.QueryComplexity.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Small-Error Approximate Degree Lower Bound for Conjunction

This module proves the Buhrman–Cleve–de Wolf–Zalka small-error approximate degree lower bound
$\widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m) > \frac{1}{25}\sqrt{m \log_2(1/\gamma)}$ for all
$m \ge 1$ and $\gamma \in [2^{-m}, 1/3]$, combining the Nisan–Szegedy bound in the moderate-error
regime with Lagrange interpolation on a mixed linear-quadratic integer grid in the small-error
regime.

## Main results

* `CslibFrontier.QueryComplexity.and_oneSidedApproxDegree_lower`:
  $\frac{1}{25}\sqrt{m \log_2(1/\gamma)} < \widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m)$ for
  $m \ge 1$ and $\gamma \in [2^{-m}, 1/3]$.
-/

public section

open scoped NNReal BigOperators
open Finset Cslib Cslib.BitString Cslib.QueryComplexity Polynomial

namespace CslibFrontier.QueryComplexity

/-! #### Lagrange interpolation lower bound for small-error `OR_m` -/

private lemma lagrange_coeff_sum_eq_zero {N : ℕ} (s : Fin (N + 1) → ℝ)
    (hs : Function.Injective s) (u : ℝ[X]) (hu : u.natDegree < N) :
    ∑ i : Fin (N + 1), u.eval (s i) * (∏ j ∈ Finset.univ.erase i, (s i - s j))⁻¹ = 0 := by
  let L : Fin (N + 1) → ℝ[X] := fun i =>
    C (∏ j ∈ Finset.univ.erase i, (s i - s j))⁻¹ * ∏ j ∈ Finset.univ.erase i, (X - C (s j))
  have hL_eval : ∀ i k, (L i).eval (s k) = if k = i then 1 else 0 := by
    intro i k
    simp only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    by_cases hki : k = i
    · subst hki
      simp only [↓reduceIte]
      rw [inv_mul_cancel₀]
      refine Finset.prod_ne_zero_iff.mpr fun j hj =>
        sub_ne_zero.mpr (hs.ne (Finset.ne_of_mem_erase hj).symm)
    · simp only [hki, ↓reduceIte]
      have hkmem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
      have hzero : ∏ j ∈ Finset.univ.erase i, (s k - s j) = 0 :=
        Finset.prod_eq_zero hkmem (sub_self (s k))
      rw [hzero, mul_zero]
  have hL_deg : ∀ i, (L i).natDegree ≤ N := by
    intro i
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    refine le_of_eq ?_
    calc ∑ j ∈ Finset.univ.erase i, (X - C (s j)).natDegree
        = ∑ _j ∈ Finset.univ.erase i, 1 := Finset.sum_congr rfl fun j _ => natDegree_X_sub_C (s j)
      _ = N := by simp [Finset.card_erase_of_mem]
  have hL_coeff : ∀ i, (L i).coeff N = (∏ j ∈ Finset.univ.erase i, (s i - s j))⁻¹ := by
    intro i
    have hprod_monic : (∏ j ∈ Finset.univ.erase i, (X - C (s j))).Monic :=
      monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (s j)
    have hprod_deg : (∏ j ∈ Finset.univ.erase i, (X - C (s j))).natDegree = N := by
      rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (s j))]
      simp [Finset.card_erase_of_mem]
    simp only [L, coeff_C_mul]
    have hcoeff : (∏ j ∈ Finset.univ.erase i, (X - C (s j))).coeff N = 1 := by
      have h := hprod_monic.coeff_natDegree
      rwa [hprod_deg] at h
    rw [hcoeff, mul_one]
  let R : ℝ[X] := u - ∑ i : Fin (N + 1), C (u.eval (s i)) * L i
  have hR_eval : ∀ k, R.eval (s k) = 0 := by
    intro k
    have hsum : (∑ i : Fin (N + 1), C (u.eval (s i)) * L i).eval (s k) =
        ∑ i : Fin (N + 1), (C (u.eval (s i)) * L i).eval (s k) := by
      simpa only [coe_evalRingHom] using
        map_sum (evalRingHom (s k)) (fun i => C (u.eval (s i)) * L i) Finset.univ
    simp only [R, eval_sub, hsum, eval_mul, eval_C, hL_eval, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sub_self]
  have hR_deg : R.natDegree ≤ N := by
    refine (natDegree_sub_le _ _).trans (max_le (le_of_lt hu) ?_)
    refine (natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le N, fun i _ => (natDegree_C_mul_le _ _).trans (hL_deg i)⟩
  have hR_zero : R = 0 := by
    by_contra hne
    have hle1 : (Finset.univ.image s).card ≤ R.natDegree := by
      have hcard : (Finset.univ.image s).card ≤ R.roots.toFinset.card := by
        refine Finset.card_le_card fun r hr => ?_
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hr
        rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
        exact hR_eval k
      exact hcard.trans ((Multiset.toFinset_card_le R.roots).trans (Polynomial.card_roots' R))
    rw [Finset.card_image_of_injective _ hs, Finset.card_univ, Fintype.card_fin] at hle1
    omega
  have hcoeff0 : R.coeff N = 0 := by rw [hR_zero, coeff_zero]
  have hsum_coeff : (∑ i : Fin (N + 1), C (u.eval (s i)) * L i).coeff N =
      ∑ i : Fin (N + 1), (C (u.eval (s i)) * L i).coeff N := by
    simpa only [lcoeff_apply] using
      map_sum (lcoeff ℝ N) (fun i => C (u.eval (s i)) * L i) Finset.univ
  simp only [R, coeff_sub, hsum_coeff, coeff_C_mul, hL_coeff] at hcoeff0
  have huN : u.coeff N = 0 := coeff_eq_zero_of_natDegree_lt hu
  linarith

private def gridT (K : ℕ) (i : ℕ) : ℕ :=
  if i ≤ 2 * K then i else K + i ^ 2 / (4 * K)

private lemma gridT_strictMono {K : ℕ} (hK : 1 ≤ K) : StrictMono (gridT K) := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  unfold gridT
  by_cases h1 : i + 1 ≤ 2 * K
  · have h0 : i ≤ 2 * K := by omega
    simp only [h0, h1, ↓reduceIte]; omega
  · by_cases h0 : i ≤ 2 * K
    · have hi : i = 2 * K := by omega
      subst hi
      simp only [le_refl, ↓reduceIte, h1]
      have hdiv : (2 * K + 1) ^ 2 / (4 * K) = K + 1 := by
        have hsq : (2 * K + 1) ^ 2 = (4 * K) * (K + 1) + 1 := by ring
        rw [hsq, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
      omega
    · simp only [h0, h1, ↓reduceIte]
      have hdiff : (i + 1) ^ 2 = i ^ 2 + (2 * i + 1) := by ring
      have hge : 4 * K ≤ 2 * i + 1 := by omega
      have : i ^ 2 / (4 * K) + 1 ≤ (i + 1) ^ 2 / (4 * K) := by
        rw [hdiff]
        have := Nat.add_div_right (i ^ 2 + (2 * i + 1 - 4 * K)) (show 0 < 4 * K by omega)
        have hrew : i ^ 2 + (2 * i + 1) = i ^ 2 + (2 * i + 1 - 4 * K) + 4 * K := by omega
        rw [hrew, this]
        have hmono := Nat.div_le_div_right (c :=
          4 * K) (show i ^ 2 ≤ i ^ 2 + (2 * i + 1 - 4 * K) by omega)
        omega
      omega

private lemma gridT_step_ge {K : ℕ} (hK : 1 ≤ K) {a b : ℕ} (hab : a ≤ b) :
    b - a ≤ gridT K b - gridT K a := by
  have hstep : ∀ d : ℕ, d ≤ gridT K (a + d) - gridT K a := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hlt := gridT_strictMono hK (show a + d < a + d + 1 by omega)
      have hle := (gridT_strictMono hK).monotone (show a ≤ a + d by omega)
      rw [show a + (d + 1) = a + d + 1 by omega]
      omega
  have := hstep (b - a)
  rwa [Nat.add_sub_cancel' hab] at this

private lemma gridT_zero (K : ℕ) : gridT K 0 = 0 := by simp [gridT]

private lemma gridT_quad_sub_le {K : ℕ} (hK : 1 ≤ K) (a b : ℕ) (hab : a < b) :
    ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / (4 * K) - 1 ≤ (gridT K b : ℝ) - (gridT K a : ℝ) := by
  have hKpos : (0 : ℝ) < 4 * K := by positivity
  have hupper : ∀ j : ℕ, (gridT K j : ℝ) ≤ K + (j : ℝ) ^ 2 / (4 * K) := by
    intro j
    unfold gridT
    split_ifs with hj
    · have hsq : 0 ≤ ((2 * (K : ℝ) - j) ^ 2) / (4 * K) := by positivity
      have : (K : ℝ) + (j : ℝ) ^ 2 / (4 * K) - j = (2 * (K : ℝ) - j) ^ 2 / (4 * K) := by
        field_simp [hKpos.ne']; ring
      linarith
    · have hdiv : ((j ^ 2 / (4 * K) : ℕ) : ℝ) ≤ (j : ℝ) ^ 2 / (4 * K) := by
        rw [le_div_iff₀ hKpos]
        exact_mod_cast Nat.div_mul_le_self (j ^ 2) (4 * K)
      push_cast; linarith
  have hlower : ∀ j : ℕ, 2 * K < j →
      (K : ℝ) + (j : ℝ) ^ 2 / (4 * K) - 1 ≤ (gridT K j : ℝ) := by
    intro j hj
    unfold gridT
    simp only [not_le.mpr hj, ↓reduceIte]
    have hdiv : (j : ℝ) ^ 2 / (4 * K) - 1 ≤ ((j ^ 2 / (4 * K) : ℕ) : ℝ) := by
      have hmod := Nat.div_add_mod (j ^ 2) (4 * K)
      have hlt : j ^ 2 % (4 * K) < 4 * K := Nat.mod_lt _ (by omega)
      have hcast : (4 * (K : ℝ)) * ((j ^ 2 / (4 * K) : ℕ) : ℝ) + ((j ^ 2 % (4 * K) : ℕ) : ℝ) =
          (j : ℝ) ^ 2 := by exact_mod_cast hmod
      have hlt_r : ((j ^ 2 % (4 * K) : ℕ) : ℝ) < 4 * K := by exact_mod_cast hlt
      rw [sub_le_iff_le_add, div_le_iff₀ hKpos]
      linarith
    push_cast; linarith
  by_cases hb : 2 * K < b
  · rw [sub_div]
    linarith [hlower b hb, hupper a]
  · push Not at hb
    have ha : a ≤ 2 * K := (le_of_lt hab).trans hb
    have hta : gridT K a = a := by simp [gridT, ha]
    have htb : gridT K b = b := by simp [gridT, hb]
    rw [hta, htb]
    have hab_r : (a : ℝ) + (b : ℝ) ≤ 4 * K := by exact_mod_cast (show a + b ≤ 4 * K by omega)
    have hba_pos : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) :=
      sub_nonneg.mpr (Nat.cast_le.mpr (le_of_lt hab))
    have h1 : ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / (4 * K) ≤ (b : ℝ) - (a : ℝ) := by
      rw [div_le_iff₀ hKpos]
      nlinarith
    linarith

private lemma gridT_lower {K : ℕ} (hK : 1 ≤ K) (j : ℕ) (hj : 1 ≤ j) :
    max (j : ℝ) ((j : ℝ) ^ 2 / (4 * K) - 1) ≤ (gridT K j : ℝ) := by
  refine max_le ?_ ?_
  · have h := gridT_step_ge hK (Nat.zero_le j)
    rw [gridT_zero, Nat.sub_zero, Nat.sub_zero] at h
    exact_mod_cast h
  · have h := gridT_quad_sub_le hK 0 j (by omega)
    rw [gridT_zero] at h
    simpa using h

private lemma gridT_diff_lower {K : ℕ} (hK : 1 ≤ K) {a b : ℕ} (hab : a < b) :
    max ((b - a : ℕ) : ℝ) (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) / (4 * K) - 1) ≤
      (gridT K b : ℝ) - (gridT K a : ℝ) := by
  refine max_le ?_ (gridT_quad_sub_le hK a b hab)
  have h := gridT_step_ge hK (le_of_lt hab)
  have hle : gridT K a ≤ gridT K b := (gridT_strictMono hK).monotone (le_of_lt hab)
  have hcast : ((gridT K b - gridT K a : ℕ) : ℝ) = (gridT K b : ℝ) - (gridT K a : ℝ) :=
    Nat.cast_sub hle
  rw [← hcast]
  exact_mod_cast h

private lemma sum_inv_gridT_diff_le {K : ℕ} (hK : 1 ≤ K) (M : ℕ) (i : ℕ) :
    ∑ j ∈ (Finset.range M).erase i, ((|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹) ≤
      16 * (K : ℝ) + 4 := by
  have hside : ∀ S : Finset ℕ, (∀ r ∈ S, 1 ≤ r) →
      ∑ r ∈ S, (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ ≤ 8 * (K : ℝ) + 2 := by
    intro S hS
    have hsplit : S = S.filter (fun r => r ≤ 8 * K) ∪ S.filter (fun r => ¬ r ≤ 8 * K) := by
      ext r; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [hsplit, Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
    have h1 : ∑ r ∈ S.filter (fun r => r ≤ 8 * K), (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ ≤
        8 * (K : ℝ) := by
      calc ∑ r ∈ S.filter (fun r => r ≤ 8 * K), (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹
          ≤ ∑ _r ∈ S.filter (fun r => r ≤ 8 * K), (1 : ℝ) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hS r (Finset.mem_filter.mp hr).1
            exact inv_le_one_of_one_le₀ (hr1.trans (le_max_left _ _))
        _ = ((S.filter (fun r => r ≤ 8 * K)).card : ℝ) := by simp
        _ ≤ ((Finset.Icc 1 (8 * K)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card fun r hr =>
              Finset.mem_Icc.mpr ⟨hS r (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
        _ = 8 * (K : ℝ) := by simp
    have h2 : ∑ r ∈ S.filter (fun r => ¬ r ≤ 8 * K),
        (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ ≤ 2 := by
      have hterm : ∀ r ∈ S.filter (fun r => ¬ r ≤ 8 * K),
          (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ ≤
            8 * (K : ℝ) * (((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹) := by
        intro r hr
        have hrgt : 8 * K < r := Nat.lt_of_not_ge (Finset.mem_filter.mp hr).2
        have hr_r : (8 * K : ℝ) < r := by exact_mod_cast hrgt
        have hr1 : (2 : ℝ) ≤ r := by linarith [show (1 : ℝ) ≤ K by exact_mod_cast hK]
        have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
        have hquad : (r : ℝ) ^ 2 / (8 * K) ≤ (r : ℝ) ^ 2 / (4 * K) - 1 := by
          have : (8 * K : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
          rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
          have hrew : ((r : ℝ) ^ 2 / (8 * K) + 1) * (4 * K) = (r : ℝ) ^ 2 / 2 + 4 * K := by
            field_simp [hKpos.ne']; ring
          rw [hrew]; linarith
        have hmax_ge : (r : ℝ) ^ 2 / (8 * K) ≤ max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1) :=
          hquad.trans (le_max_right _ _)
        have hinv1 : (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ ≤ 8 * (K : ℝ) / (r : ℝ) ^ 2 := by
          calc (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹
              ≤ ((r : ℝ) ^ 2 / (8 * K))⁻¹ := inv_anti₀ (by positivity) hmax_ge
            _ = 8 * (K : ℝ) / (r : ℝ) ^ 2 := by rw [inv_div]
        have hrm1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
        have hrm1_pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
        have htel : 1 / (r : ℝ) ^ 2 ≤ ((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹ := by
          rw [hrm1, inv_sub_inv hrm1_pos.ne' (by linarith : (r : ℝ) ≠ 0)]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        calc (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹
            ≤ 8 * (K : ℝ) / (r : ℝ) ^ 2 := hinv1
          _ = 8 * (K : ℝ) * (1 / (r : ℝ) ^ 2) := by ring
          _ ≤ 8 * (K : ℝ) * (((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left htel (by positivity)
      have hmaxR : ∃ B : ℕ, 8 * K ≤ B ∧ ∀ r ∈ S.filter (fun r => ¬ r ≤ 8 * K), r ≤ B := by
        obtain ⟨B, hB⟩ := Finset.exists_nat_subset_range (S.filter (fun r => ¬ r ≤ 8 * K))
        exact ⟨max (8 * K) B, le_max_left _ _, fun r hr =>
          (Nat.le_of_lt (Finset.mem_range.mp (hB hr))).trans (le_max_right _ _)⟩
      obtain ⟨B, hBge, hBle⟩ := hmaxR
      calc ∑ r ∈ S.filter (fun r => ¬ r ≤ 8 * K),
            (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹
          ≤ ∑ r ∈ S.filter (fun r => ¬ r ≤ 8 * K),
              8 * (K : ℝ) * (((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹) := Finset.sum_le_sum hterm
        _ ≤ ∑ r ∈ Finset.Icc (8 * K + 1) B,
              8 * (K : ℝ) * (((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r hr _ => ?_
            · intro r hr
              have h1 := Nat.lt_of_not_ge (Finset.mem_filter.mp hr).2
              exact Finset.mem_Icc.mpr ⟨by omega, hBle r hr⟩
            · have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
              have hle : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
              have hpos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
                have : 1 ≤ r - 1 := by have := (Finset.mem_Icc.mp hr).1; omega
                exact_mod_cast this
              exact mul_nonneg (by positivity) (sub_nonneg.mpr (inv_anti₀ hpos hle))
        _ = 8 * (K : ℝ) * ∑ r ∈ Finset.Icc (8 * K + 1) B,
              (((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
        _ ≤ 8 * (K : ℝ) * ((8 * K : ℝ)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have htel_sum : ∀ m : ℕ,
                ∑ r ∈ Finset.Icc (8 * K + 1) (8 * K + m),
                  (((r - 1 : ℕ) : ℝ)⁻¹ - (r : ℝ)⁻¹) =
                  ((8 * K : ℝ)⁻¹ - ((8 * K + m : ℕ) : ℝ)⁻¹) := by
              intro m
              induction m with
              | zero =>
                have : Finset.Icc (8 * K + 1) (8 * K + 0) = ∅ :=
                  Finset.Icc_eq_empty (by omega)
                rw [this]; simp
              | succ m ihm =>
                have hIcc : Finset.Icc (8 * K + 1) (8 * K + (m + 1)) =
                    insert (8 * K + m + 1) (Finset.Icc (8 * K + 1) (8 * K + m)) := by
                  ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc]), ihm]
                have hsub : 8 * K + m + 1 - 1 = 8 * K + m := by omega
                rw [hsub]
                push_cast
                ring
            have hsum_eq := htel_sum (B - 8 * K)
            rw [Nat.add_sub_cancel' hBge] at hsum_eq
            rw [hsum_eq]
            have hnonneg : (0 : ℝ) ≤ ((B : ℕ) : ℝ)⁻¹ := by positivity
            linarith
        _ = 1 := by
            have hKne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            field_simp [hKne]
        _ ≤ 2 := by norm_num
    linarith
  let L := ((Finset.range M).erase i).filter (fun j => j < i)
  let R := ((Finset.range M).erase i).filter (fun j => ¬ j < i)
  have hpart : (Finset.range M).erase i = L ∪ R := by
    ext j; simp only [L, R, Finset.mem_union, Finset.mem_filter]; tauto
  rw [hpart, Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  have hL : ∑ j ∈ L, (|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹ ≤ 8 * (K : ℝ) + 2 := by
    calc ∑ j ∈ L, (|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹
        ≤ ∑ j ∈ L, (max ((i - j : ℕ) : ℝ) (((i - j : ℕ) : ℝ) ^ 2 / (4 * K) - 1))⁻¹ := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hji : j < i := (Finset.mem_filter.mp hj).2
          have hdiff := gridT_diff_lower hK hji
          have hpos : (0 : ℝ) < max ((i - j : ℕ) : ℝ) (((i - j : ℕ) : ℝ) ^ 2 / (4 * K) - 1) := by
            have : (1 : ℝ) ≤ ((i - j : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ i - j by omega)
            exact lt_of_lt_of_le zero_lt_one (this.trans (le_max_left _ _))
          have hsq : ((i - j : ℕ) : ℝ) ^ 2 ≤ (i : ℝ) ^ 2 - (j : ℝ) ^ 2 := by
            have hsub : ((i - j : ℕ) : ℝ) = (i : ℝ) - (j : ℝ) := by
              exact_mod_cast Nat.cast_sub hji.le
            rw [hsub]
            nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j,
              show (j : ℝ) ≤ i from Nat.cast_le.mpr hji.le]
          have hge : max ((i - j : ℕ) : ℝ) (((i - j : ℕ) : ℝ) ^ 2 / (4 * K) - 1) ≤
              |(gridT K i : ℝ) - (gridT K j : ℝ)| := by
            have hgt : (gridT K j : ℝ) ≤ gridT K i := by
              exact_mod_cast (gridT_strictMono hK).monotone hji.le
            rw [abs_of_nonneg (by linarith)]
            refine (max_le_max_left _ ?_).trans hdiff
            linarith [div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 4 * K)]
          exact inv_anti₀ hpos hge
      _ = ∑ r ∈ L.image (fun j => i - j),
            (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have ha' : a < i := (Finset.mem_filter.mp ha).2
          have hb' : b < i := (Finset.mem_filter.mp hb).2
          dsimp only at hab; omega
      _ ≤ 8 * (K : ℝ) + 2 := by
          refine hside _ fun r hr => ?_
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
          have := (Finset.mem_filter.mp hj).2
          omega
  have hR : ∑ j ∈ R, (|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹ ≤ 8 * (K : ℝ) + 2 := by
    calc ∑ j ∈ R, (|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹
        ≤ ∑ j ∈ R, (max ((j - i : ℕ) : ℝ) (((j - i : ℕ) : ℝ) ^ 2 / (4 * K) - 1))⁻¹ := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hne : j ≠ i := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
          have hij : i < j := lt_of_le_of_ne (Nat.le_of_not_gt (Finset.mem_filter.mp hj).2) hne.symm
          have hdiff := gridT_diff_lower hK hij
          have hpos : (0 : ℝ) < max ((j - i : ℕ) : ℝ) (((j - i : ℕ) : ℝ) ^ 2 / (4 * K) - 1) := by
            have : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j - i by omega)
            exact lt_of_lt_of_le zero_lt_one (this.trans (le_max_left _ _))
          have hsq : ((j - i : ℕ) : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 - (i : ℝ) ^ 2 := by
            have hsub : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
              exact_mod_cast Nat.cast_sub hij.le
            rw [hsub]
            nlinarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i,
              show (i : ℝ) ≤ j from Nat.cast_le.mpr hij.le]
          have hge : max ((j - i : ℕ) : ℝ) (((j - i : ℕ) : ℝ) ^ 2 / (4 * K) - 1) ≤
              |(gridT K i : ℝ) - (gridT K j : ℝ)| := by
            have hgt : (gridT K i : ℝ) ≤ gridT K j := by
              exact_mod_cast (gridT_strictMono hK).monotone hij.le
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            refine (max_le_max_left _ ?_).trans hdiff
            linarith [div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 4 * K)]
          exact inv_anti₀ hpos hge
      _ = ∑ r ∈ R.image (fun j => j - i),
            (max (r : ℝ) ((r : ℝ) ^ 2 / (4 * K) - 1))⁻¹ := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have ha' : i ≤ a := Nat.le_of_not_gt (Finset.mem_filter.mp ha).2
          have hb' : i ≤ b := Nat.le_of_not_gt (Finset.mem_filter.mp hb).2
          dsimp only at hab; omega
      _ ≤ 8 * (K : ℝ) + 2 := by
          refine hside _ fun r hr => ?_
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
          have hne : j ≠ i := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
          have hij : i < j := lt_of_le_of_ne (Nat.le_of_not_gt (Finset.mem_filter.mp hj).2) hne.symm
          omega
  linarith

private lemma prod_gridT_over_quad_le {K : ℕ} (hK : 1 ≤ K) (M : ℕ) :
    ∏ j ∈ Finset.Icc 1 M, ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))) ≤ Real.exp (6 * K) := by
  have hsplit : Finset.Icc 1 M =
      (Finset.Icc 1 M).filter (fun j => j ≤ 2 * K) ∪
      (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K) := by
    ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  rw [hsplit, Finset.prod_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  have h1 : ∏ j ∈ (Finset.Icc 1 M).filter (fun j => j ≤ 2 * K),
      ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))) ≤ Real.exp (4 * K) := by
    have heq : ∏ j ∈ (Finset.Icc 1 M).filter (fun j => j ≤ 2 * K),
        ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))) =
        ∏ j ∈ (Finset.Icc 1 M).filter (fun j => j ≤ 2 * K), (4 * (K : ℝ) / (j : ℝ)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
      have hj2 : j ≤ 2 * K := (Finset.mem_filter.mp hj).2
      have hjn : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [gridT, hj2, ↓reduceIte]
      field_simp [hjn]
    rw [heq]
    set S := (Finset.Icc 1 M).filter (fun j => j ≤ 2 * K)
    have hSsub : S ⊆ Finset.Icc 1 (2 * K) := fun j hj =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1,
        (Finset.mem_filter.mp hj).2⟩
    have hle_full : ∏ j ∈ S, (4 * (K : ℝ) / (j : ℝ)) ≤
        ∏ j ∈ Finset.Icc 1 (2 * K), (4 * (K : ℝ) / (j : ℝ)) := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hSsub
        (fun j hj => by
          have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp (hSsub hj)).1
          positivity)
        fun j hj _ => ?_
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      have hj2 : (j : ℝ) ≤ 2 * K := by exact_mod_cast (Finset.mem_Icc.mp hj).2
      rw [one_le_div (by linarith)]
      linarith
    refine hle_full.trans ?_
    have hprod_eq : ∏ j ∈ Finset.Icc 1 (2 * K), (4 * (K : ℝ) / (j : ℝ)) =
        (4 * (K : ℝ)) ^ (2 * K) / ((2 * K).factorial : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Icc,
        show 2 * K + 1 - 1 = 2 * K by omega]
      congr 1
      have hfac : ∀ n : ℕ, ∏ j ∈ Finset.Icc 1 n, (j : ℝ) = (n.factorial : ℝ) := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc]), ihn, Nat.factorial_succ]
          push_cast; ring
      exact hfac (2 * K)
    rw [hprod_eq]
    exact Real.pow_div_factorial_le_exp (4 * (K : ℝ)) (by positivity) (2 * K)
  have h2 : ∏ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
      ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))) ≤ Real.exp (2 * K) := by
    have hterm : ∀ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
        (gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K)) ≤ Real.exp (4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2) := by
      intro j hj
      have hjgt : 2 * K < j := Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hle : (gridT K j : ℝ) ≤ K + (j : ℝ) ^ 2 / (4 * K) := by
        simp only [gridT, not_le.mpr hjgt, ↓reduceIte]
        have hdiv : ((j ^ 2 / (4 * K) : ℕ) : ℝ) ≤ (j : ℝ) ^ 2 / (4 * K) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
          exact_mod_cast Nat.div_mul_le_self (j ^ 2) (4 * K)
        push_cast; linarith
      have hdiv_le : (gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K)) ≤
          1 + 4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2 := by
        calc (gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))
            ≤ (K + (j : ℝ) ^ 2 / (4 * K)) / ((j : ℝ) ^ 2 / (4 * K)) :=
              div_le_div_of_nonneg_right hle (by positivity)
          _ = 1 + 4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2 := by
              field_simp [hKpos.ne', hjpos.ne']; ring
      exact hdiv_le.trans (by linarith [Real.add_one_le_exp (4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2)])
    calc ∏ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
          ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K)))
        ≤ ∏ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
            Real.exp (4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2) :=
          Finset.prod_le_prod₀ (fun j hj => by
            have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
            positivity) hterm
      _ = Real.exp (∑ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
            4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * K) := by
          refine Real.exp_le_exp.mpr ?_
          have hsum_le : ∑ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
              4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2 ≤ 2 * (K : ℝ) := by
            have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
            have htel : ∀ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
                4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2 ≤
                  4 * (K : ℝ) ^ 2 * (((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹) := by
              intro j hj
              have hjgt : 2 * K < j := Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2
              have hjm1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
                exact_mod_cast Nat.cast_sub (by omega)
              have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
              have hinv : 1 / (j : ℝ) ^ 2 ≤ ((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹ := by
                rw [hjm1, inv_sub_inv (by linarith) (by linarith)]
                rw [div_le_div_iff₀ (by positivity) (by nlinarith : (0 : ℝ) < ((j : ℝ) - 1) * j)]
                nlinarith
              calc 4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2
                  = 4 * (K : ℝ) ^ 2 * (1 / (j : ℝ) ^ 2) := by ring
                _ ≤ 4 * (K : ℝ) ^ 2 * (((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹) :=
                    mul_le_mul_of_nonneg_left hinv (by positivity)
            set B := max (2 * K) M
            calc ∑ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
                  4 * (K : ℝ) ^ 2 / (j : ℝ) ^ 2
                ≤ ∑ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
                    4 * (K : ℝ) ^ 2 * (((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹) :=
                  Finset.sum_le_sum htel
              _ ≤ ∑ j ∈ Finset.Icc (2 * K + 1) B,
                    4 * (K : ℝ) ^ 2 * (((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹) := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j hj _ => ?_
                  · intro j hj
                    have hgt := Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2
                    have hM := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
                    exact Finset.mem_Icc.mpr ⟨by omega, hM.trans (le_max_right _ _)⟩
                  · have hj1 : 1 ≤ j - 1 := by have := (Finset.mem_Icc.mp hj).1; omega
                    have hpos : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast hj1
                    have hle : ((j - 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j 1
                    exact mul_nonneg (by positivity) (sub_nonneg.mpr (inv_anti₀ hpos hle))
              _ = 4 * (K : ℝ) ^ 2 * ∑ j ∈ Finset.Icc (2 * K + 1) B,
                    (((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
              _ ≤ 4 * (K : ℝ) ^ 2 * (2 * (K : ℝ))⁻¹ := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  have htel_sum : ∀ m : ℕ,
                      ∑ j ∈ Finset.Icc (2 * K + 1) (2 * K + m),
                        (((j - 1 : ℕ) : ℝ)⁻¹ - (j : ℝ)⁻¹) =
                        ((2 * K : ℝ)⁻¹ - ((2 * K + m : ℕ) : ℝ)⁻¹) := by
                    intro m
                    induction m with
                    | zero =>
                      have : Finset.Icc (2 * K + 1) (2 * K + 0) = ∅ :=
                        Finset.Icc_eq_empty (by omega)
                      rw [this]; simp
                    | succ m ihm =>
                      have hIcc : Finset.Icc (2 * K + 1) (2 * K + (m + 1)) =
                          insert (2 * K + m + 1) (Finset.Icc (2 * K + 1) (2 * K + m)) := by
                        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                      rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc]), ihm]
                      have hsub : 2 * K + m + 1 - 1 = 2 * K + m := by omega
                      rw [hsub]; push_cast; ring
                  have hsum_eq := htel_sum (B - 2 * K)
                  rw [Nat.add_sub_cancel' (le_max_left (2 * K) M)] at hsum_eq
                  rw [hsum_eq]
                  have hnn : (0 : ℝ) ≤ ((B : ℕ) : ℝ)⁻¹ := by positivity
                  linarith
              _ = 2 * K := by field_simp [hKpos.ne']; ring
          exact hsum_le
  calc (∏ j ∈ (Finset.Icc 1 M).filter (fun j => j ≤ 2 * K),
        ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K)))) *
      (∏ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ j ≤ 2 * K),
        ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))))
      ≤ Real.exp (4 * K) * Real.exp (2 * K) :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun j hj => by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1; positivity)
          (Real.exp_nonneg _)
    _ = Real.exp (6 * K) := by rw [← Real.exp_add]; ring_nf

private lemma prod_quad_over_sq_le (M : ℕ) (i : ℕ) (hi : 1 ≤ i) (hiM : i ≤ M) :
    (∏ j ∈ Finset.Icc 1 M, (j : ℝ) ^ 2) /
      (∏ j ∈ (Finset.range (M + 1)).erase i, |(i : ℝ) ^ 2 - (j : ℝ) ^ 2|) ≤ 2 := by
  have hsplit_num : ∏ j ∈ Finset.Icc 1 M, (j : ℝ) ^ 2 = ((M.factorial : ℝ) ^ 2) := by
    rw [Finset.prod_pow]
    congr 1
    have hfac : ∀ n : ℕ, ∏ j ∈ Finset.Icc 1 n, (j : ℝ) = (n.factorial : ℝ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc]), ih, Nat.factorial_succ]
        push_cast; ring
    exact hfac M
  have hden_eq : ∏ j ∈ (Finset.range (M + 1)).erase i, |(i : ℝ) ^ 2 - (j : ℝ) ^ 2| =
      ((M - i).factorial : ℝ) * ((M + i).factorial : ℝ) / 2 := by
    have h0 : 0 ∈ (Finset.range (M + 1)).erase i :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    rw [← Finset.mul_prod_erase _ _ h0]
    have hleft : ((Finset.range (M + 1)).erase i).erase 0 =
        (Finset.Icc 1 (i - 1)) ∪ (Finset.Icc (i + 1) M) := by
      ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
    rw [hleft, Finset.prod_union (Finset.disjoint_iff_ne.mpr fun a ha b hb => by
      simp only [Finset.mem_Icc] at ha hb; omega)]
    have hfac_low : ∏ j ∈ Finset.Icc 1 (i - 1), |(i : ℝ) ^ 2 - (j : ℝ) ^ 2| =
        (((i - 1).factorial : ℝ)) * (((2 * i - 1).factorial : ℝ) / (i.factorial : ℝ)) := by
      have hrew : ∀ j ∈ Finset.Icc 1 (i - 1),
          |(i : ℝ) ^ 2 - (j : ℝ) ^ 2| = ((i - j : ℕ) : ℝ) * ((i + j : ℕ) : ℝ) := by
        intro j hj
        have hji : j < i := by have := (Finset.mem_Icc.mp hj).2; omega
        rw [abs_of_nonneg (by nlinarith [show (j : ℝ) ≤ i from Nat.cast_le.mpr hji.le])]
        rw [Nat.cast_sub hji.le, Nat.cast_add]; ring
      rw [Finset.prod_congr rfl hrew, Finset.prod_mul_distrib]
      congr 1
      · have hbij : ∏ j ∈ Finset.Icc 1 (i - 1), ((i - j : ℕ) : ℝ) =
            ∏ r ∈ Finset.Icc 1 (i - 1), (r : ℝ) := by
          refine Finset.prod_bij (fun j _ => i - j) (fun j hj => by
            simp only [Finset.mem_Icc] at hj ⊢; omega) (fun a ha b hb hab => by
            simp only [Finset.mem_Icc] at ha hb; omega) (fun r hr => ⟨i - r, by
            simp only [Finset.mem_Icc] at hr ⊢; omega, by
            simp only [Finset.mem_Icc] at hr; omega⟩) (fun _ _ => rfl)
        rw [hbij]
        have hfac : ∀ n : ℕ, ∏ r ∈ Finset.Icc 1 n, (r : ℝ) = (n.factorial : ℝ) := by
          intro n; induction n with
          | zero => simp
          | succ n ihn =>
            have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc]), ihn, Nat.factorial_succ]
            push_cast; ring
        exact hfac (i - 1)
      · have hbij : ∏ j ∈ Finset.Icc 1 (i - 1), ((i + j : ℕ) : ℝ) =
            ∏ r ∈ Finset.Icc (i + 1) (2 * i - 1), (r : ℝ) := by
          refine Finset.prod_bij (fun j _ => i + j) (fun j hj => by
            simp only [Finset.mem_Icc] at hj ⊢; omega) (fun a _ b _ hab => by omega)
            (fun r hr => ⟨r - i, by simp only [Finset.mem_Icc] at hr ⊢; omega, by
              simp only [Finset.mem_Icc] at hr; omega⟩) (fun _ _ => rfl)
        rw [hbij]
        have hfac_Icc : ∀ a b : ℕ, a ≤ b →
            (a.factorial : ℝ) * ∏ r ∈ Finset.Icc (a + 1) b, (r : ℝ) = (b.factorial : ℝ) := by
          intro a b hab
          induction b with
          | zero =>
            have ha0 : a = 0 := by omega
            subst ha0; simp
          | succ b ihb =>
            by_cases h : a = b + 1
            · subst h; rw [Finset.Icc_eq_empty (by omega)]; simp
            · have hab' : a ≤ b := by omega
              have hIcc : Finset.Icc (a + 1) (b + 1) = insert (b + 1) (Finset.Icc (a + 1) b) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc]), ← mul_assoc,
                mul_comm (a.factorial : ℝ), mul_assoc, ihb hab', Nat.factorial_succ]
              push_cast; ring
        have hpos_i : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
        rw [eq_div_iff hpos_i, mul_comm]
        exact hfac_Icc i (2 * i - 1) (by omega)
    have hfac_high : ∏ j ∈ Finset.Icc (i + 1) M, |(i : ℝ) ^ 2 - (j : ℝ) ^ 2| =
        (((M - i).factorial : ℝ)) * (((M + i).factorial : ℝ) / ((2 * i).factorial : ℝ)) := by
      have hrew : ∀ j ∈ Finset.Icc (i + 1) M,
          |(i : ℝ) ^ 2 - (j : ℝ) ^ 2| = ((j - i : ℕ) : ℝ) * ((j + i : ℕ) : ℝ) := by
        intro j hj
        have hij : i < j := by have := (Finset.mem_Icc.mp hj).1; omega
        have hij_r : (i : ℝ) ≤ j := Nat.cast_le.mpr hij.le
        rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
        rw [Nat.cast_sub hij.le, Nat.cast_add]; ring
      rw [Finset.prod_congr rfl hrew, Finset.prod_mul_distrib]
      congr 1
      · have hbij : ∏ j ∈ Finset.Icc (i + 1) M, ((j - i : ℕ) : ℝ) =
            ∏ r ∈ Finset.Icc 1 (M - i), (r : ℝ) := by
          refine Finset.prod_bij (fun j _ => j - i) (fun j hj => by
            simp only [Finset.mem_Icc] at hj ⊢; omega) (fun a ha b hb hab => by
            simp only [Finset.mem_Icc] at ha hb; omega) (fun r hr => ⟨i + r, by
            simp only [Finset.mem_Icc] at hr ⊢; omega, by omega⟩) (fun _ _ => rfl)
        rw [hbij]
        have hfac : ∀ n : ℕ, ∏ r ∈ Finset.Icc 1 n, (r : ℝ) = (n.factorial : ℝ) := by
          intro n; induction n with
          | zero => simp
          | succ n ihn =>
            have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc]), ihn, Nat.factorial_succ]
            push_cast; ring
        exact hfac (M - i)
      · have hbij : ∏ j ∈ Finset.Icc (i + 1) M, ((j + i : ℕ) : ℝ) =
            ∏ r ∈ Finset.Icc (2 * i + 1) (M + i), (r : ℝ) := by
          refine Finset.prod_bij (fun j _ => j + i) (fun j hj => by
            simp only [Finset.mem_Icc] at hj ⊢; omega) (fun a _ b _ hab => by omega)
            (fun r hr => ⟨r - i, by simp only [Finset.mem_Icc] at hr ⊢; omega, by
              simp only [Finset.mem_Icc] at hr; omega⟩) (fun _ _ => rfl)
        rw [hbij]
        have hfac_Icc : ∀ a b : ℕ, a ≤ b →
            (a.factorial : ℝ) * ∏ r ∈ Finset.Icc (a + 1) b, (r : ℝ) = (b.factorial : ℝ) := by
          intro a b hab
          induction b with
          | zero =>
            have ha0 : a = 0 := by omega
            subst ha0; simp
          | succ b ihb =>
            by_cases h : a = b + 1
            · subst h; rw [Finset.Icc_eq_empty (by omega)]; simp
            · have hab' : a ≤ b := by omega
              have hIcc : Finset.Icc (a + 1) (b + 1) = insert (b + 1) (Finset.Icc (a + 1) b) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc]), ← mul_assoc,
                mul_comm (a.factorial : ℝ), mul_assoc, ihb hab', Nat.factorial_succ]
              push_cast; ring
        have hpos_2i : ((2 * i).factorial : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * i))
        rw [eq_div_iff hpos_2i, mul_comm]
        exact hfac_Icc (2 * i) (M + i) (by omega)
    rw [hfac_low, hfac_high]
    have hfac_i : (i.factorial : ℝ) = (i : ℝ) * ((i - 1).factorial : ℝ) := by
      have h1 : i = (i - 1) + 1 := by omega
      have hsub : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi, Nat.cast_one]
      conv_lhs => rw [h1, Nat.factorial_succ]
      push_cast; rw [hsub]; ring
    have hfac_2i : ((2 * i).factorial : ℝ) = (2 * (i : ℝ)) * ((2 * i - 1).factorial : ℝ) := by
      have h1 : 2 * i = (2 * i - 1) + 1 := by omega
      have hsub : ((2 * i - 1 : ℕ) : ℝ) = 2 * (i : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      conv_lhs => rw [h1, Nat.factorial_succ]
      push_cast; rw [hsub]; ring
    have hne1 : ((i - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hne2 : ((2 * i - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hne3 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) i)]
    rw [hfac_i, hfac_2i]
    field_simp [hne1, hne2, hne3]
  rw [hsplit_num, hden_eq, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  have hchoose : (M.factorial : ℝ) ^ 2 ≤ ((M - i).factorial : ℝ) * ((M + i).factorial : ℝ) := by
    have hnat : M.factorial * M.factorial ≤ (M - i).factorial * (M + i).factorial := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show M - i ≤ M by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show M ≤ M + i by omega)
      have hsub : M - (M - i) = i := by omega
      have hsub2 : M + i - M = i := by omega
      rw [hsub] at h1
      rw [hsub2] at h2
      have hch : M.choose (M - i) ≤ (M + i).choose M := by
        rw [Nat.choose_symm (show i ≤ M by omega),
          ← Nat.choose_symm (show M ≤ M + i by omega), hsub2]
        exact Nat.choose_le_choose i (by omega)
      have hmul : (M.choose (M - i)) * (M - i).factorial * i.factorial * M.factorial ≤
          ((M + i).choose M) * M.factorial * i.factorial * (M - i).factorial := by
        have hstep : M.choose (M - i) ≤ (M + i).choose M := hch
        calc M.choose (M - i) * (M - i).factorial * i.factorial * M.factorial
            = M.choose (M - i) * ((M - i).factorial * i.factorial * M.factorial) := by ring
          _ ≤ (M + i).choose M * ((M - i).factorial * i.factorial * M.factorial) :=
              Nat.mul_le_mul_right _ hstep
          _ = (M + i).choose M * M.factorial * i.factorial * (M - i).factorial := by ring
      rw [h1, h2] at hmul
      have hpos : 0 < M.factorial * i.factorial :=
        Nat.mul_pos (Nat.factorial_pos M) (Nat.factorial_pos i)
      have hmul' : M.factorial * M.factorial * (M.factorial * i.factorial) ≤
          (M - i).factorial * (M + i).factorial * (M.factorial * i.factorial) := by
        nlinarith [hmul]
      exact Nat.le_of_mul_le_mul_right hmul' hpos
    have hcast : ((M.factorial * M.factorial : ℕ) : ℝ) ≤
        (((M - i).factorial * (M + i).factorial : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith
  nlinarith

private lemma gridT_weight_ratio_le {K : ℕ} (hK : 1 ≤ K) (M : ℕ) (i : ℕ) (hi : 1 ≤ i)
    (hiM : i ≤ M) :
    (∏ j ∈ Finset.Icc 1 M, (gridT K j : ℝ)) /
      (∏ j ∈ (Finset.range (M + 1)).erase i, |(gridT K i : ℝ) - (gridT K j : ℝ)|) ≤
      2 * Real.exp (22 * K + 4) := by
  have hKpos : (0 : ℝ) < 4 * K := by positivity
  have hprod_t_pos : 0 < ∏ j ∈ Finset.Icc 1 M, (gridT K j : ℝ) :=
    Finset.prod_pos fun j hj => by
      have hj1 := (Finset.mem_Icc.mp hj).1
      have := gridT_lower hK j hj1
      exact lt_of_lt_of_le (by exact_mod_cast (show 0 < j by omega))
        (le_trans (le_max_left _ _) this)
  have hprod_d_pos : 0 < ∏ j ∈ (Finset.range (M + 1)).erase i,
      |(gridT K i : ℝ) - (gridT K j : ℝ)| :=
    Finset.prod_pos fun j hj => abs_pos.mpr (sub_ne_zero.mpr (by
      exact_mod_cast (gridT_strictMono hK).injective.ne (Finset.ne_of_mem_erase hj).symm))
  have hprod_q_pos : 0 < ∏ j ∈ Finset.Icc 1 M, ((j : ℝ) ^ 2 / (4 * K)) :=
    Finset.prod_pos fun j hj => by
      have := (Finset.mem_Icc.mp hj).1; positivity
  have hprod_qd_pos : 0 < ∏ j ∈ (Finset.range (M + 1)).erase i,
      (|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) :=
    Finset.prod_pos fun j hj => by
      have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hsqne : (i : ℝ) ^ 2 ≠ (j : ℝ) ^ 2 := by
        intro h
        have hij : (i : ℝ) = (j : ℝ) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j]
        exact hne (Nat.cast_injective hij)
      exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hsqne)) hKpos
  have hcard_eq : (Finset.Icc 1 M).card = ((Finset.range (M + 1)).erase i).card := by
    rw [Nat.card_Icc, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  have hcancel : (∏ j ∈ Finset.Icc 1 M, ((j : ℝ) ^ 2 / (4 * K))) /
      (∏ j ∈ (Finset.range (M + 1)).erase i, (|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K))) =
      (∏ j ∈ Finset.Icc 1 M, (j : ℝ) ^ 2) /
      (∏ j ∈ (Finset.range (M + 1)).erase i, |(i : ℝ) ^ 2 - (j : ℝ) ^ 2|) := by
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.prod_const,
      hcard_eq]
    have hpow : (4 * (K : ℝ)) ^ ((Finset.range (M + 1)).erase i).card ≠ 0 := by positivity
    field_simp [hpow]
  have hfact : (∏ j ∈ Finset.Icc 1 M, (gridT K j : ℝ)) /
      (∏ j ∈ (Finset.range (M + 1)).erase i, |(gridT K i : ℝ) - (gridT K j : ℝ)|) =
      (∏ j ∈ Finset.Icc 1 M, ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K)))) *
      (∏ j ∈ (Finset.range (M + 1)).erase i,
        ((|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) / |(gridT K i : ℝ) - (gridT K j : ℝ)|)) *
      ((∏ j ∈ Finset.Icc 1 M, (j : ℝ) ^ 2) /
        (∏ j ∈ (Finset.range (M + 1)).erase i, |(i : ℝ) ^ 2 - (j : ℝ) ^ 2|)) := by
    have hdiv1 : ∏ j ∈ Finset.Icc 1 M, ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))) =
        (∏ j ∈ Finset.Icc 1 M, (gridT K j : ℝ)) /
          (∏ j ∈ Finset.Icc 1 M, ((j : ℝ) ^ 2 / (4 * K))) := Finset.prod_div_distrib _ _
    have hdiv2 : ∏ j ∈ (Finset.range (M + 1)).erase i,
          ((|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) / |(gridT K i : ℝ) - (gridT K j : ℝ)|) =
        (∏ j ∈ (Finset.range (M + 1)).erase i, (|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K))) /
          (∏ j ∈ (Finset.range (M + 1)).erase i, |(gridT K i : ℝ) - (gridT K j : ℝ)|) :=
      Finset.prod_div_distrib _ _
    rw [← hcancel, hdiv1, hdiv2]
    field_simp [hprod_q_pos.ne', hprod_qd_pos.ne', hprod_d_pos.ne']
  rw [hfact]
  have hF1 : ∏ j ∈ Finset.Icc 1 M, ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K))) ≤
      Real.exp (6 * K) := prod_gridT_over_quad_le hK M
  have hF2 : ∏ j ∈ (Finset.range (M + 1)).erase i,
      ((|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) / |(gridT K i : ℝ) - (gridT K j : ℝ)|) ≤
      Real.exp (16 * K + 4) := by
    have hterm : ∀ j ∈ (Finset.range (M + 1)).erase i,
        (|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) / |(gridT K i : ℝ) - (gridT K j : ℝ)| ≤
          Real.exp ((|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹) := by
      intro j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      have hd_pos : 0 < |(gridT K i : ℝ) - (gridT K j : ℝ)| :=
        abs_pos.mpr (sub_ne_zero.mpr (by
          exact_mod_cast (gridT_strictMono hK).injective.ne hne.symm))
      have hle_plus_one : |(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K) ≤
          |(gridT K i : ℝ) - (gridT K j : ℝ)| + 1 := by
        rcases lt_or_gt_of_ne hne with hji | hij
        · have h1 := gridT_quad_sub_le hK j i hji
          have h2 : (gridT K j : ℝ) ≤ gridT K i := by
            exact_mod_cast (gridT_strictMono hK).monotone hji.le
          have h3 : (j : ℝ) ≤ i := Nat.cast_le.mpr hji.le
          rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)]
          linarith
        · have h1 := gridT_quad_sub_le hK i j hij
          have h2 : (gridT K i : ℝ) ≤ gridT K j := by
            exact_mod_cast (gridT_strictMono hK).monotone hij.le
          have h3 : (i : ℝ) ≤ j := Nat.cast_le.mpr hij.le
          rw [abs_sub_comm, abs_sub_comm (gridT K i : ℝ),
            abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)]
          linarith
      have hdiv_le : (|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) /
          |(gridT K i : ℝ) - (gridT K j : ℝ)| ≤
          1 + (|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹ := by
        rw [div_le_iff₀ hd_pos, add_mul, one_mul, inv_mul_cancel₀ hd_pos.ne']
        linarith
      exact hdiv_le.trans (by linarith [Real.add_one_le_exp (|(gridT K i : ℝ) -
        (gridT K j : ℝ)|)⁻¹])
    calc ∏ j ∈ (Finset.range (M + 1)).erase i,
          ((|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) / |(gridT K i : ℝ) - (gridT K j : ℝ)|)
        ≤ ∏ j ∈ (Finset.range (M + 1)).erase i,
            Real.exp ((|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹) :=
          Finset.prod_le_prod₀ (fun j hj => by
            have hne : j ≠ i := Finset.ne_of_mem_erase hj
            have hd_pos : 0 < |(gridT K i : ℝ) - (gridT K j : ℝ)| :=
              abs_pos.mpr (sub_ne_zero.mpr (by
                exact_mod_cast (gridT_strictMono hK).injective.ne hne.symm))
            positivity) hterm
      _ = Real.exp (∑ j ∈ (Finset.range (M + 1)).erase i,
            (|(gridT K i : ℝ) - (gridT K j : ℝ)|)⁻¹) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (16 * K + 4) := Real.exp_le_exp.mpr (sum_inv_gridT_diff_le hK (M + 1) i)
  have hF3 : (∏ j ∈ Finset.Icc 1 M, (j : ℝ) ^ 2) /
      (∏ j ∈ (Finset.range (M + 1)).erase i, |(i : ℝ) ^ 2 - (j : ℝ) ^ 2|) ≤ 2 :=
    prod_quad_over_sq_le M i hi hiM
  have h12 : (∏ j ∈ Finset.Icc 1 M, ((gridT K j : ℝ) / ((j : ℝ) ^ 2 / (4 * K)))) *
      (∏ j ∈ (Finset.range (M + 1)).erase i,
        ((|(i : ℝ) ^ 2 - (j : ℝ) ^ 2| / (4 * K)) / |(gridT K i : ℝ) - (gridT K j : ℝ)|)) ≤
      Real.exp (6 * K) * Real.exp (16 * K + 4) :=
    mul_le_mul hF1 hF2 (Finset.prod_nonneg fun j hj => by
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      have hd_pos : 0 < |(gridT K i : ℝ) - (gridT K j : ℝ)| :=
        abs_pos.mpr (sub_ne_zero.mpr (by
          exact_mod_cast (gridT_strictMono hK).injective.ne hne.symm))
      positivity) (Real.exp_nonneg _)
  have h123 := mul_le_mul h12 hF3 (div_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _)
    (Finset.prod_nonneg fun _ _ => abs_nonneg _)) (by positivity)
  calc _ ≤ Real.exp (6 * K) * Real.exp (16 * K + 4) * 2 := h123
    _ = 2 * Real.exp (22 * K + 4) := by rw [← Real.exp_add]; ring_nf

/-- **Small-error approximate degree lower bound for $\mathrm{AND}_m$**
: for every `m ≥ 1` and
`γ ∈ [2^{-m}, 1/3]`, `(1 / 25) * √(m * log₂(1 / γ)) < oneSidedApproxDegree γ (threshold m m)`.
-/
theorem and_oneSidedApproxDegree_lower {m : ℕ} {γ : ℝ} (hm : 1 ≤ m)
    (hγlo : (2 : ℝ) ^ (-(m : ℤ)) ≤ γ) (hγhi : γ ≤ 1 / 3) :
    (1 / 25 : ℝ) * Real.sqrt (m * Real.logb 2 (1 / γ)) <
      (oneSidedApproxDegree γ (threshold m m) : ℝ) := by
  have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγlo
  rw [oneSidedApproxDegree_and_eq_signApproxDegree hγpos.le, signApproxDegree_and_eq_or hγpos.le]
  set d := signApproxDegree γ (threshold m 1)
  have hlog_pos : 1 ≤ Real.logb 2 (1 / γ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one]
    rw [le_div_iff₀ hγpos]; linarith
  have hlog_le_m : Real.logb 2 (1 / γ) ≤ m := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
    have hpow : (2 : ℝ) ^ (m : ℝ) = (2 : ℝ) ^ m := Real.rpow_natCast 2 m
    rw [hpow, div_le_iff₀ hγpos]
    have hinv : (2 : ℝ) ^ (-(m : ℤ)) = ((2 : ℝ) ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hinv] at hγlo
    have hmul := mul_le_mul_of_nonneg_right hγlo (show (0 : ℝ) ≤ (2 : ℝ) ^ m by positivity)
    rw [inv_mul_cancel₀ (by positivity)] at hmul
    linarith
  by_cases hregime : Real.logb 2 (1 / γ) ≤ 200
  · -- Nisan–Szegedy regime
    have hns := one_sub_two_mul_mul_blockSensitivity_le
      (ε := Real.toNNReal (γ / 2)) (threshold m 1)
    rw [blockSensitivity_threshold_one_right,
      ← signApproxDegree_eq_approxDegree hγpos.le,
      Real.coe_toNNReal _ (by positivity)] at hns
    have hm_le : (m : ℝ) ≤ 3 * (d : ℝ) ^ 2 := by nlinarith
    have hd_pos : (0 : ℝ) < d := by
      by_contra h0
      have hd0 : d = 0 := by exact_mod_cast le_antisymm (not_lt.mp h0) (Nat.cast_nonneg d)
      rw [hd0, Nat.cast_zero] at hm_le
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hsq : ((1 / 25 : ℝ) * Real.sqrt (m * Real.logb 2 (1 / γ))) ^ 2 < (d : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have h1 : (m : ℝ) * Real.logb 2 (1 / γ) ≤ (m : ℝ) * 200 :=
        mul_le_mul_of_nonneg_left hregime (Nat.cast_nonneg m)
      nlinarith [sq_pos_of_pos hd_pos]
    nlinarith [Real.sqrt_nonneg (m * Real.logb 2 (1 / γ))]
  · -- Lagrange interpolation regime (`log₂(1 / γ) > 200`, `m > 200`)
    push Not at hregime
    set K : ℕ := ⌊Real.logb 2 (1 / γ) / 100⌋₊
    have hK_ge : 2 ≤ K := by
      refine (Nat.le_floor_iff (by positivity)).mpr ?_
      push_cast; linarith
    have hK_le : (K : ℝ) ≤ Real.logb 2 (1 / γ) / 100 := Nat.floor_le (by positivity)
    have hlt_K1 : Real.logb 2 (1 / γ) / 100 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlog_lt : Real.logb 2 (1 / γ) < 150 * (K : ℝ) := by
      have : (K : ℝ) + 1 ≤ (3 / 2 : ℝ) * K := by
        have : (2 : ℝ) ≤ K := by exact_mod_cast hK_ge
        linarith
      linarith
    have hm_gt : (200 : ℝ) < m := lt_of_lt_of_le hregime hlog_le_m
    have hK_le_m : (K : ℝ) ≤ (m : ℝ) / 100 := by linarith
    -- Show `2 * m * K < d ^ 2` by contradiction.
    have hd_sq : 2 * (m : ℝ) * (K : ℝ) < (d : ℝ) ^ 2 := by
      by_contra hle
      push Not at hle
      set N : ℕ := d + 1
      have hN_eq : N = d + 1 := rfl
      let s : Fin (N + 1) → ℕ := fun i =>
        if h : i.1 = 0 then 0 else 1 + gridT K (i.1 - 1)
      have hs_mono : StrictMono s := by
        intro a b hab
        change (if a.1 = 0 then 0 else 1 + gridT K (a.1 - 1)) <
          (if b.1 = 0 then 0 else 1 + gridT K (b.1 - 1))
        by_cases ha : a.1 = 0
        · have hb : b.1 ≠ 0 := by omega
          simp only [ha, hb, ↓reduceIte]; omega
        · have hb : b.1 ≠ 0 := by omega
          simp only [ha, hb, ↓reduceIte]
          have := gridT_strictMono (show 1 ≤ K by omega) (show a.1 - 1 < b.1 - 1 by omega)
          omega
      have hs_le_m : ∀ i : Fin (N + 1), s i ≤ m := by
        intro i
        have hle_last : s i ≤ s ⟨N, Nat.lt_succ_self N⟩ := hs_mono.monotone (Fin.le_last i)
        refine hle_last.trans ?_
        simp only [s, show N ≠ 0 by omega, ↓reduceDIte, show N - 1 = d by omega]
        unfold gridT
        by_cases hd2K : d ≤ 2 * K
        · simp only [hd2K, ↓reduceIte]
          have : (1 + d : ℝ) ≤ m := by
            have : (d : ℝ) ≤ 2 * K := by exact_mod_cast hd2K
            linarith
          exact_mod_cast this
        · simp only [hd2K, ↓reduceIte]
          have hdiv : ((d ^ 2 / (4 * K) : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 / (4 * K) := by
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
            exact_mod_cast Nat.div_mul_le_self (d ^ 2) (4 * K)
          have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
          have hbound : (1 : ℝ) + K + (d : ℝ) ^ 2 / (4 * K) ≤ m := by
            have hdiv_le : (d : ℝ) ^ 2 / (4 * K) ≤ (m : ℝ) / 2 := by
              rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
              linarith
            linarith
          have hcast : ((1 + (K + d ^ 2 / (4 * K)) : ℕ) : ℝ) ≤ m := by
            push_cast; linarith
          exact_mod_cast hcast
      obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_signApproxDegree hγpos.le (threshold m 1)
      obtain ⟨q, hqdeg, hq⟩ := exists_natDegree_le_eval_eq_layerAverage hp
      let u : ℝ[X] := q + 1
      have hu_deg : u.natDegree < N := by
        have : u.natDegree ≤ d := (natDegree_add_le _ _).trans (by simpa using hqdeg)
        omega
      have hu0 : 2 - γ ≤ u.eval 0 := by
        have h0 := hq 0 (by rw [Fintype.card_fin]; exact Nat.zero_le m)
        rw [Nat.cast_zero] at h0
        have hlayer : ({x : BitString m | weight x = 0} : Finset (BitString m)).Nonempty :=
          weightLayer_nonempty (Nat.zero_le m)
        have havg : 1 - γ ≤ layerAverage p 0 := by
          rw [layerAverage]
          refine le_expect hlayer fun x hx => ?_
          have hwx : weight x = 0 := (Finset.mem_filter.mp hx).2
          have htx : threshold m 1 x = false := by rw [threshold_apply, hwx]; decide
          have := (abs_le.mp (hpf x)).1
          rw [htx, signVal_false] at this
          linarith
        simp only [u, eval_add, eval_one, h0]; linarith
      have huj : ∀ j : ℕ, 1 ≤ j → j ≤ m → |u.eval (j : ℝ)| ≤ γ := by
        intro j hj1 hjm
        have hj := hq j (by rw [Fintype.card_fin]; exact hjm)
        have hlayer : ({x : BitString m | weight x = j} : Finset (BitString m)).Nonempty :=
          weightLayer_nonempty hjm
        have hlo : -1 - γ ≤ layerAverage p j := by
          rw [layerAverage]
          refine le_expect hlayer fun x hx => ?_
          have hwx : weight x = j := (Finset.mem_filter.mp hx).2
          have htx : threshold m 1 x = true := by
            rw [threshold_apply, hwx]; exact decide_eq_true hj1
          have := (abs_le.mp (hpf x)).1
          rw [htx, signVal_true] at this; linarith
        have hhi : layerAverage p j ≤ -1 + γ := by
          rw [layerAverage]
          refine expect_le hlayer fun x hx => ?_
          have hwx : weight x = j := (Finset.mem_filter.mp hx).2
          have htx : threshold m 1 x = true := by
            rw [threshold_apply, hwx]; exact decide_eq_true hj1
          have := (abs_le.mp (hpf x)).2
          rw [htx, signVal_true] at this; linarith
        simp only [u, eval_add, eval_one, hj, abs_le]
        constructor <;> linarith
      let sR : Fin (N + 1) → ℝ := fun i => (s i : ℝ)
      have hsR_inj : Function.Injective sR :=
        Nat.cast_injective.comp hs_mono.injective
      have hlag := lagrange_coeff_sum_eq_zero sR hsR_inj u hu_deg
      let w : Fin (N + 1) → ℝ := fun i =>
        (∏ j ∈ Finset.univ.erase i, (sR i - sR j))⁻¹
      have hw0_pos : 0 < |w 0| := by
        simp only [w, abs_inv]
        refine inv_pos.mpr (abs_pos.mpr (Finset.prod_ne_zero_iff.mpr fun j hj => ?_))
        exact sub_ne_zero.mpr (hsR_inj.ne (Finset.ne_of_mem_erase hj).symm)
      have hsplit0 : u.eval (sR 0) * w 0 +
          ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), u.eval (sR i) * w i = 0 := by
        rw [Finset.add_sum_erase Finset.univ (fun i => u.eval (sR i) * w i) (Finset.mem_univ _)]
        exact hlag
      have hmain : (2 - γ) * |w 0| ≤ γ * ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), |w i| := by
        have hs0 : sR 0 = 0 := by simp [sR, s]
        have h1 : |u.eval 0 * w 0| =
          |∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), u.eval (sR i) * w i| := by
          rw [← hs0]
          have : u.eval (sR 0) * w 0 =
            -(∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), u.eval (sR i) * w i) := by
            linarith
          rw [this, abs_neg]
        have h2 : |u.eval 0| * |w 0| ≤ γ * ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), |w i| := by
          rw [← abs_mul, h1]
          calc |∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), u.eval (sR i) * w i|
              ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), |u.eval (sR i) * w i| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), γ * |w i| := by
                refine Finset.sum_le_sum fun i hi => ?_
                rw [abs_mul]
                have hi0 : 1 ≤ s i := by
                  have hne : i ≠ 0 := Finset.ne_of_mem_erase hi
                  have hlt0 : (0 : Fin (N + 1)) < i := Fin.pos_of_ne_zero hne
                  have hlt_s := hs_mono hlt0
                  have hs0_nat : s 0 = 0 := by simp only [s, Fin.val_zero, ↓reduceDIte]
                  omega
                exact mul_le_mul_of_nonneg_right (huj (s i) hi0 (hs_le_m i)) (abs_nonneg _)
            _ = γ * ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), |w i| := (Finset.mul_sum _ _ _).symm
        have h3 : 2 - γ ≤ |u.eval 0| := hu0.trans (le_abs_self _)
        exact (mul_le_mul_of_nonneg_right h3 (abs_nonneg _)).trans h2
      -- Bound `∑_{i ≠ 0} |w i| / |w 0| ≤ exp (55 * K + 15)`.
      have hsum_ratio : ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), (|w i| / |w 0|) ≤
          Real.exp (55 * (K : ℝ) + 15) := by
        have hw_abs : ∀ i : Fin (N + 1), |w i| = (∏ j ∈ Finset.univ.erase i, |sR i - sR j|)⁻¹ := by
          intro i; simp only [w, abs_inv, Finset.abs_prod]
        have hw0_eq : |w 0|⁻¹ = ∏ r ∈ Finset.Icc 1 d, (1 + (gridT K r : ℝ)) := by
          rw [hw_abs, inv_inv]
          have hbij : ∏ j ∈ Finset.univ.erase (0 : Fin (N + 1)), |sR 0 - sR j| =
              ∏ r ∈ Finset.range N, (1 + (gridT K r : ℝ)) := by
            refine Finset.prod_bij (fun j _ => j.1 - 1)
              (fun j hj => Finset.mem_range.mpr (by
                have hne := Finset.ne_of_mem_erase hj; have := j.2; omega))
              (fun a ha b hb hab => by
                have ha0 : a.1 ≠ 0 := fun h => Finset.ne_of_mem_erase ha (Fin.ext h)
                have hb0 : b.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hb (Fin.ext h)
                exact Fin.ext (by omega))
              (fun r hr => ⟨⟨r + 1, by have := Finset.mem_range.mp hr; omega⟩,
                Finset.mem_erase.mpr ⟨by
                  intro h; have h' := congrArg Fin.val h; simp only [Fin.val_zero] at h'; omega,
                  Finset.mem_univ _⟩, by simp⟩)
              (fun j hj => ?_)
            have hne : j.1 ≠ 0 := by
              intro h0; exact Finset.ne_of_mem_erase hj (Fin.ext h0)
            simp only [sR, s, Fin.val_zero, ↓reduceDIte, hne, Nat.cast_zero, zero_sub, abs_neg]
            push_cast
            rw [abs_of_nonneg (by positivity)]
          rw [hbij]
          have hsplit : Finset.range N = insert 0 (Finset.Icc 1 d) := by
            ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
          rw [hsplit, Finset.prod_insert (by simp [Finset.mem_Icc]), gridT_zero]
          simp
        have hP_le : ∏ r ∈ Finset.Icc 1 d, (1 + ((gridT K r : ℝ))⁻¹) ≤
          Real.exp (16 * (K : ℝ) + 4) := by
          calc ∏ r ∈ Finset.Icc 1 d, (1 + ((gridT K r : ℝ))⁻¹)
              ≤ ∏ r ∈ Finset.Icc 1 d, Real.exp (((gridT K r : ℝ))⁻¹) :=
                Finset.prod_le_prod₀ (fun r hr => by positivity)
                  (fun r _ => by linarith [Real.add_one_le_exp (((gridT K r : ℝ))⁻¹)])
            _ = Real.exp (∑ r ∈ Finset.Icc 1 d, ((gridT K r : ℝ))⁻¹) := (Real.exp_sum _ _).symm
            _ ≤ Real.exp (16 * (K : ℝ) + 4) := by
                refine Real.exp_le_exp.mpr ?_
                have hset : Finset.Icc 1 d = (Finset.range (d + 1)).erase 0 := by
                  ext r; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
                rw [hset]
                have hrew : ∑ r ∈ (Finset.range (d + 1)).erase 0, ((gridT K r : ℝ))⁻¹ =
                    ∑ r ∈ (Finset.range (d +
                      1)).erase 0, (|(gridT K 0 : ℝ) - (gridT K r : ℝ)|)⁻¹ := by
                  refine Finset.sum_congr rfl fun r hr => ?_
                  have hr0 : 0 < r := by have := (Finset.mem_erase.mp hr).1; omega
                  have hgt : 0 < (gridT K r : ℝ) := by
                    have := gridT_lower (show 1 ≤ K by omega) r hr0
                    exact lt_of_lt_of_le (by exact_mod_cast hr0) (le_trans (le_max_left _ _) this)
                  rw [gridT_zero, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hgt]
                rw [hrew]
                exact sum_inv_gridT_diff_le (show 1 ≤ K by omega) (d + 1) 0
        have h1_idx : (⟨1, by omega⟩ : Fin (N + 1)) ∈ Finset.univ.erase (0 : Fin (N + 1)) :=
          Finset.mem_erase.mpr ⟨by
            intro h; have h' := congrArg Fin.val h; simp only [Fin.val_zero] at h'; omega,
            Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ h1_idx]
        have hterm1 : |w ⟨1, by omega⟩| / |w 0| ≤ Real.exp (16 * (K : ℝ) + 4) := by
          rw [div_eq_mul_inv, hw0_eq, hw_abs]
          have hden1 : ∏ j ∈ Finset.univ.erase (⟨1, by omega⟩ : Fin (N + 1)),
              |sR ⟨1, by omega⟩ - sR j| = ∏ r ∈ Finset.Icc 1 d, (gridT K r : ℝ) := by
            have h0m : (0 : Fin (N + 1)) ∈ Finset.univ.erase (⟨1, by omega⟩ : Fin (N + 1)) :=
              Finset.mem_erase.mpr ⟨by
                intro h; have h' := congrArg Fin.val h; simp only [Fin.val_zero] at h'; omega,
                Finset.mem_univ _⟩
            rw [← Finset.mul_prod_erase _ _ h0m]
            have h0val : |sR ⟨1, by omega⟩ - sR 0| = 1 := by
              have hs1 : s ⟨1, by omega⟩ = 1 := by
                simp only [s, show (1 : ℕ) ≠ 0 by decide, ↓reduceDIte, Nat.sub_self, gridT_zero,
                  Nat.add_zero]
              have hs0 : s 0 = 0 := by simp only [s, Fin.val_zero, ↓reduceDIte]
              simp only [sR, hs1, hs0, Nat.cast_one, Nat.cast_zero, sub_zero, abs_one]
            rw [h0val, one_mul]
            refine Finset.prod_bij (fun j _ => j.1 - 1)
              (fun j hj => by
                have h1 : j.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
                have h2 : j.1 ≠ 1 := fun h =>
                  Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj) (Fin.ext h)
                have hjlt := j.2
                exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
              (fun a ha b hb hab => by
                have ha0 : a.1 ≠ 0 := fun h => Finset.ne_of_mem_erase ha (Fin.ext h)
                have hb0 : b.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hb (Fin.ext h)
                exact Fin.ext (by omega))
              (fun r hr => ⟨⟨r + 1, by have := (Finset.mem_Icc.mp hr).2; omega⟩,
                Finset.mem_erase.mpr ⟨by
                  intro h; have h' := congrArg Fin.val h; simp only [Fin.val_zero] at h'; omega,
                  Finset.mem_erase.mpr ⟨by
                    have hr1 := (Finset.mem_Icc.mp hr).1
                    intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega,
                    Finset.mem_univ _⟩⟩, by simp⟩)
              (fun j hj => ?_)
            have h0 : j.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
            have h1 : j.1 ≠ 1 := fun h =>
              Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj) (Fin.ext h)
            have hs1 : s ⟨1, by omega⟩ = 1 := by
              simp only [s, show (1 : ℕ) ≠ 0 by decide, ↓reduceDIte, Nat.sub_self, gridT_zero,
                Nat.add_zero]
            have hsj : s j = 1 + gridT K (j.1 - 1) := by
              simp only [s, h0, ↓reduceDIte]
            simp only [sR, hs1, hsj]
            push_cast
            have hle : (0 : ℝ) ≤ (gridT K (j.1 - 1) : ℝ) := Nat.cast_nonneg _
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            ring
          rw [hden1, inv_mul_eq_div, ← Finset.prod_div_distrib]
          have hrew : ∏ r ∈ Finset.Icc 1 d, ((1 + (gridT K r : ℝ)) / (gridT K r : ℝ)) =
              ∏ r ∈ Finset.Icc 1 d, (1 + ((gridT K r : ℝ))⁻¹) := by
            refine Finset.prod_congr rfl fun r hr => ?_
            have hr1 := (Finset.mem_Icc.mp hr).1
            have hgt : (gridT K r : ℝ) ≠ 0 := by
              have := gridT_lower (show 1 ≤ K by omega) r hr1
              have hpos : (0 : ℝ) < gridT K r :=
                lt_of_lt_of_le (by exact_mod_cast (show 0 < r by omega))
                  (le_trans (le_max_left _ _) this)
              exact hpos.ne'
            field_simp [hgt]; ring
          rw [hrew]; exact hP_le
        have hrest : ∑ i ∈ (Finset.univ.erase (0 : Fin (N + 1))).erase ⟨1, by omega⟩,
            (|w i| / |w 0|) ≤ (16 * (K : ℝ) + 4) * (2 * Real.exp (38 * (K : ℝ) + 8)) := by
          have hterm_r : ∀ i ∈ (Finset.univ.erase (0 : Fin (N + 1))).erase ⟨1, by omega⟩,
              |w i| / |w 0| ≤
                ((1 + (gridT K (i.1 - 1) : ℝ))⁻¹) * (2 * Real.exp (38 * (K : ℝ) + 8)) := by
            intro i hi
            have hi1 : i.1 ≠ 1 := fun h => Finset.ne_of_mem_erase hi (Fin.ext h)
            have hi0 : i.1 ≠ 0 := fun h =>
              Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi) (Fin.ext h)
            set r := i.1 - 1
            have hr1 : 1 ≤ r := by omega
            have hrd : r ≤ d := by have := i.2; omega
            rw [div_eq_mul_inv, hw0_eq, hw_abs]
            have hden_i : ∏ j ∈ Finset.univ.erase i, |sR i - sR j| =
                (1 + (gridT K r : ℝ)) *
                  ∏ u ∈ (Finset.range (d + 1)).erase r, |(gridT K r : ℝ) - (gridT K u : ℝ)| := by
              have h0m : (0 : Fin (N + 1)) ∈ Finset.univ.erase i :=
                Finset.mem_erase.mpr ⟨fun h => hi0 (congrArg Fin.val h.symm), Finset.mem_univ _⟩
              rw [← Finset.mul_prod_erase _ _ h0m]
              have hs0i : |sR i - sR 0| = 1 + (gridT K r : ℝ) := by
                simp only [sR, s, Fin.val_zero, show i.1 ≠ 0 by omega, ↓reduceDIte, Nat.cast_zero,
                  sub_zero]
                push_cast
                rw [abs_of_nonneg (by positivity)]
              rw [hs0i]
              congr 1
              refine Finset.prod_bij (fun j _ => j.1 - 1)
                (fun j hj => by
                  have hj0 : j.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
                  have hji : j.1 ≠ i.1 := fun h =>
                    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj) (Fin.ext h)
                  have hjlt := j.2
                  exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩)
                (fun a ha b hb hab => by
                  have ha0 : a.1 ≠ 0 := fun h => Finset.ne_of_mem_erase ha (Fin.ext h)
                  have hb0 : b.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hb (Fin.ext h)
                  exact Fin.ext (by omega))
                (fun u hu => ⟨⟨u + 1, by
                  have hlt := Finset.mem_range.mp (Finset.mem_of_mem_erase hu)
                  omega⟩,
                  Finset.mem_erase.mpr ⟨by
                    intro h; have h' := congrArg Fin.val h; simp only [Fin.val_zero] at h'; omega,
                    Finset.mem_erase.mpr ⟨by
                      have hne := Finset.ne_of_mem_erase hu
                      intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega,
                      Finset.mem_univ _⟩⟩, by simp⟩)
                (fun j hj => ?_)
              have hj0 : j.1 ≠ 0 := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
              simp only [sR, s, show i.1 ≠ 0 by omega, show j.1 ≠ 0 by omega, ↓reduceDIte]
              push_cast; congr 1; simp only [r]; ring
            have hnum_eq : ∏ u ∈ Finset.Icc 1 d, (1 + (gridT K u : ℝ)) =
                (∏ u ∈ Finset.Icc 1 d, (1 + ((gridT K u : ℝ))⁻¹)) *
                  ∏ u ∈ Finset.Icc 1 d, (gridT K u : ℝ) := by
              rw [← Finset.prod_mul_distrib]
              refine Finset.prod_congr rfl fun u hu => ?_
              have hu1 := (Finset.mem_Icc.mp hu).1
              have hgt : (gridT K u : ℝ) ≠ 0 := by
                have := gridT_lower (show 1 ≤ K by omega) u hu1
                exact (lt_of_lt_of_le (by exact_mod_cast (show 0 < u by omega))
                  (le_trans (le_max_left _ _) this)).ne'
              field_simp [hgt]; ring
            rw [hden_i, hnum_eq, mul_inv]
            have hrear : ((1 + (gridT K r : ℝ))⁻¹ *
                (∏ u ∈ (Finset.range (d + 1)).erase r, |(gridT K r : ℝ) - (gridT K u : ℝ)|)⁻¹) *
                ((∏ u ∈ Finset.Icc 1 d, (1 + ((gridT K u : ℝ))⁻¹)) *
                  ∏ u ∈ Finset.Icc 1 d, (gridT K u : ℝ)) =
                (1 + (gridT K r : ℝ))⁻¹ *
                ((∏ u ∈ Finset.Icc 1 d, (1 + ((gridT K u : ℝ))⁻¹)) *
                  ((∏ u ∈ Finset.Icc 1 d, (gridT K u : ℝ)) /
                    ∏ u ∈ (Finset.range (d +
                      1)).erase r, |(gridT K r : ℝ) - (gridT K u : ℝ)|)) := by
              ring
            rw [hrear]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hrat := gridT_weight_ratio_le (show 1 ≤ K by omega) d r hr1 hrd
            calc (∏ u ∈ Finset.Icc 1 d, (1 + ((gridT K u : ℝ))⁻¹)) *
                  ((∏ u ∈ Finset.Icc 1 d, (gridT K u : ℝ)) /
                    ∏ u ∈ (Finset.range (d + 1)).erase r, |(gridT K r : ℝ) - (gridT K u : ℝ)|)
                ≤ Real.exp (16 * (K : ℝ) + 4) * (2 * Real.exp (22 * (K : ℝ) + 4)) :=
                  mul_le_mul hP_le hrat
                    (div_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
                      (Finset.prod_nonneg fun _ _ => abs_nonneg _)) (Real.exp_nonneg _)
              _ = 2 * Real.exp (38 * (K : ℝ) + 8) := by
                  have : Real.exp (16 * (K : ℝ) + 4) * Real.exp (22 * (K : ℝ) + 4) =
                      Real.exp (38 * (K : ℝ) + 8) := by rw [← Real.exp_add]; ring_nf
                  linarith
          calc ∑ i ∈ (Finset.univ.erase (0 : Fin (N + 1))).erase ⟨1, by omega⟩, (|w i| / |w 0|)
              ≤ ∑ i ∈ (Finset.univ.erase (0 : Fin (N + 1))).erase ⟨1, by omega⟩,
                  ((1 + (gridT K (i.1 - 1) : ℝ))⁻¹ * (2 * Real.exp (38 * (K : ℝ) + 8))) :=
                Finset.sum_le_sum hterm_r
            _ = (∑ i ∈ (Finset.univ.erase (0 : Fin (N + 1))).erase ⟨1, by omega⟩,
                  (1 + (gridT K (i.1 - 1) : ℝ))⁻¹) * (2 * Real.exp (38 * (K : ℝ) + 8)) :=
                (Finset.sum_mul _ _ _).symm
            _ ≤ (16 * (K : ℝ) + 4) * (2 * Real.exp (38 * (K : ℝ) + 8)) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                have hbij : ∑ i ∈ (Finset.univ.erase (0 : Fin (N + 1))).erase ⟨1, by omega⟩,
                    (1 + (gridT K (i.1 - 1) : ℝ))⁻¹ =
                    ∑ r ∈ Finset.Icc 1 d, (1 + (gridT K r : ℝ))⁻¹ := by
                  refine Finset.sum_bij (fun i _ => i.1 - 1)
                    (fun i hi => by
                      have h1 : i.1 ≠ 1 := fun h => Finset.ne_of_mem_erase hi (Fin.ext h)
                      have h0 : i.1 ≠ 0 := fun h =>
                        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi) (Fin.ext h)
                      have hilt := i.2
                      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
                    (fun a ha b hb hab => by
                      have ha0 : a.1 ≠ 0 := fun h =>
                        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha) (Fin.ext h)
                      have hb0 : b.1 ≠ 0 := fun h =>
                        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb) (Fin.ext h)
                      exact Fin.ext (by omega))
                    (fun r hr => ⟨⟨r + 1, by have := (Finset.mem_Icc.mp hr).2; omega⟩,
                      Finset.mem_erase.mpr ⟨by
                        have hr1 := (Finset.mem_Icc.mp hr).1
                        intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega,
                        Finset.mem_erase.mpr ⟨by
                          intro h; have h' := congrArg Fin.val h
                          simp only [Fin.val_zero] at h'; omega,
                          Finset.mem_univ _⟩⟩, by simp⟩)
                    (fun _ _ => rfl)
                rw [hbij]
                have hset : Finset.Icc 1 d = (Finset.range (d + 1)).erase 0 := by
                  ext r; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
                rw [hset]
                calc ∑ r ∈ (Finset.range (d + 1)).erase 0, (1 + (gridT K r : ℝ))⁻¹
                    ≤ ∑ r ∈ (Finset.range (d +
                      1)).erase 0, (|(gridT K 0 : ℝ) - (gridT K r : ℝ)|)⁻¹ := by
                      refine Finset.sum_le_sum fun r hr => ?_
                      have hr0 : 0 < r := by have := (Finset.mem_erase.mp hr).1; omega
                      have hgt : 0 < (gridT K r : ℝ) := by
                        have := gridT_lower (show 1 ≤ K by omega) r hr0
                        exact lt_of_lt_of_le (by exact_mod_cast hr0)
                          (le_trans (le_max_left _ _) this)
                      rw [gridT_zero, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hgt]
                      exact inv_anti₀ hgt (by linarith)
                  _ ≤ 16 * (K : ℝ) + 4 := sum_inv_gridT_diff_le (show 1 ≤ K by omega) (d + 1) 0
        have hlin : (16 * (K : ℝ) + 4) * 2 ≤ Real.exp (16 * (K : ℝ) + 6) := by
          have h1 : (16 * (K : ℝ) + 4) + 1 ≤ Real.exp (16 * (K : ℝ) + 4) :=
            Real.add_one_le_exp _
          have h2 : (2 : ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (2 : ℝ); linarith
          calc (16 * (K : ℝ) + 4) * 2
              ≤ Real.exp (16 * (K : ℝ) + 4) * Real.exp 2 := by
                nlinarith [Real.exp_nonneg (16 * (K : ℝ) + 4)]
            _ = Real.exp (16 * (K : ℝ) + 6) := by rw [← Real.exp_add]; ring_nf
        have hcomb : Real.exp (16 * (K : ℝ) + 4) +
            (16 * (K : ℝ) + 4) * (2 * Real.exp (38 * (K : ℝ) + 8)) ≤
            Real.exp (55 * (K : ℝ) + 15) := by
          have hprod_bound : (16 * (K : ℝ) + 4) * (2 * Real.exp (38 * (K : ℝ) + 8)) ≤
              Real.exp (54 * (K : ℝ) + 14) := by
            calc (16 * (K : ℝ) + 4) * (2 * Real.exp (38 * (K : ℝ) + 8))
                = ((16 * (K : ℝ) + 4) * 2) * Real.exp (38 * (K : ℝ) + 8) := by ring
              _ ≤ Real.exp (16 * (K : ℝ) + 6) * Real.exp (38 * (K : ℝ) + 8) :=
                  mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
              _ = Real.exp (54 * (K : ℝ) + 14) := by rw [← Real.exp_add]; ring_nf
          have hle1 : Real.exp (16 * (K : ℝ) + 4) ≤ Real.exp (54 * (K : ℝ) + 14) :=
            Real.exp_le_exp.mpr (by linarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K])
          have h2exp : 2 ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ); linarith
          calc Real.exp (16 * (K : ℝ) + 4) +
                (16 * (K : ℝ) + 4) * (2 * Real.exp (38 * (K : ℝ) + 8))
              ≤ 2 * Real.exp (54 * (K : ℝ) + 14) := by linarith
            _ ≤ Real.exp 1 * Real.exp (54 * (K : ℝ) + 14) :=
                mul_le_mul_of_nonneg_right h2exp (Real.exp_nonneg _)
            _ = Real.exp (54 * (K : ℝ) + 15) := by rw [← Real.exp_add]; ring_nf
            _ ≤ Real.exp (55 * (K : ℝ) + 15) :=
                Real.exp_le_exp.mpr (by linarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K])
        linarith
      -- Now compare `exp (55 * K + 15)` to `(2 - γ) / γ > exp (69 * K)`.
      have hsum_div : (2 - γ) / γ ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (N + 1)), (|w i| / |w 0|) := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        simp only [← div_eq_mul_inv]
        rw [div_le_div_iff₀ hγpos hw0_pos]
        linarith
      have hgap : Real.exp (55 * (K : ℝ) + 15) < (2 - γ) / γ := by
        have hlog2 : (0.693 : ℝ) < Real.log 2 := by
          have := Real.log_two_gt_d9; linarith
        have h69 : 55 * (K : ℝ) + 15 < 69 * (K : ℝ) := by
          have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK_ge
          linarith
        have hexp_lt : Real.exp (69 * (K : ℝ)) < 1 / γ := by
          have hpow_le : (2 : ℝ) ^ (100 * (K : ℝ)) ≤ 1 / γ := by
            rw [← Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
            linarith
          have he2 : Real.exp (69 * (K : ℝ)) < (2 : ℝ) ^ (100 * (K : ℝ)) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
            refine Real.exp_lt_exp.mpr ?_
            have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
            nlinarith
          exact lt_of_lt_of_le he2 hpow_le
        have hinv_lt : 1 / γ < (2 - γ) / γ := by
          rw [div_lt_div_iff_of_pos_right hγpos]; linarith
        exact (Real.exp_lt_exp.mpr h69).trans (hexp_lt.trans hinv_lt)
      linarith
    have hsq : ((1 / 25 : ℝ) * Real.sqrt (m * Real.logb 2 (1 / γ))) ^ 2 < (d : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have h1 : (m : ℝ) * Real.logb 2 (1 / γ) < 150 * (m : ℝ) * (K : ℝ) := by
        have hmpos : (0 : ℝ) < m := by positivity
        nlinarith
      nlinarith
    nlinarith [Real.sqrt_nonneg (m * Real.logb 2 (1 / γ))]

end CslibFrontier.QueryComplexity
