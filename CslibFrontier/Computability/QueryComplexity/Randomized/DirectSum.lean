/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized.Hardcore
public import CslibFrontier.Computability.QueryComplexity.Randomized.Resilience

import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strong threshold direct sum theorem and main direct sum theorems

This module proves:

- accuracy in terms of leaf hardcore density and advantage via `berSumCdf`.
- (`cor_threshold_from_stats_chernoff`,
 `lem_accuracy_from_hardcore_density_and_advantage`): exponential accuracy bound via `gExp`.
- zero-advantage bound `E[g_{δk/10}(Dens_H(ℓ))] ≤ exp(-0.121 δ k)`.
- Lipschitz-type bounds for `gExp`.
- threshold hardness of $f^{\otimes k}$ from a hardcore measure for $f$.
- (`thm_threshold_direct_sum`, `thm_threshold_direct_sum_forall`):
 strong threshold direct sum theorem for distributional query complexity.
- (`thm_strong_direct_sum`, `thm_strong_direct_sum_forall`) and (`thm_main_intro`,
`thm_main_intro_of_le`, `thm_main_intro_full_range`):
 strong direct sum theorems for distributional query complexity.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity.DirectSum

open Cslib Convexity Finset
open scoped BigOperators ENNReal NNReal

/-! ### The function `g_t(z) = min(1, exp(t - z / 4))` -/

/-- Auxiliary exponential-cap function $g_t(z) = \min(1, e^{t - z/4})$. -/
@[expose] noncomputable def gExp (thr z : ℝ) : ℝ :=
  min 1 (Real.exp (thr - z / 4))

theorem gExp_nonneg (thr z : ℝ) : 0 ≤ gExp thr z :=
  le_min zero_le_one (Real.exp_pos _).le

theorem gExp_le_one (thr z : ℝ) : gExp thr z ≤ 1 :=
  min_le_left _ _

theorem gExp_le_exp (thr z : ℝ) : gExp thr z ≤ Real.exp (thr - z / 4) :=
  min_le_right _ _

theorem gExp_eq_one_of_le (thr z : ℝ) (h : z ≤ 4 * thr) : gExp thr z = 1 := by
  unfold gExp
  exact min_eq_left (Real.one_le_exp (by linarith))

theorem gExp_eq_exp_of_ge (thr z : ℝ) (h : 4 * thr ≤ z) :
    gExp thr z = Real.exp (thr - z / 4) := by
  unfold gExp
  exact min_eq_right (Real.exp_le_one_iff.mpr (by linarith))

/-! ### -/

private theorem mem_support_leafCondPMF_path_eq_ds {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β)
    {X Y : Fin k → Fin n → Bool} (hX : prodPMF μ k X ≠ 0)
    (hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support) :
    pathBlock t Y = pathBlock t X := by
  classical
  rw [leafCondPMF_eq] at hY
  have hmapfst : (((prodPMF μ k).map fun Z ↦ (pathBlock t Z, Z)).map Prod.fst) =
      (prodPMF μ k).map (pathBlock t) := by
    rw [PMF.map_comp]; rfl
  have hsupp : pathBlock t X ∈
      (((prodPMF μ k).map fun Z ↦ (pathBlock t Z, Z)).map Prod.fst).support := by
    rw [hmapfst]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨X, (PMF.mem_support_iff _ _).mpr hX, rfl⟩
  have hjoint := (Cslib.Probability.PMF.mem_support_conditionalSnd_iff _ _ hsupp Y).mp hY
  obtain ⟨Z, _, hZ⟩ := (PMF.mem_support_map_iff _ _ _).mp hjoint
  have hZY : Z = Y := congrArg Prod.snd hZ
  have hZp : pathBlock t Z = pathBlock t X := congrArg Prod.fst hZ
  rwa [hZY] at hZp

/-- For any hardcore measure `H` (with values in `[0, 1]`), tree `T`, and threshold `thr ≥ 0`,
$\Pr_{X \sim \mu^k}[\lVert T(X) - f^{\otimes k}(X) \rVert_0 \le \mathrm{thr}] \le
 \mathbb{E}_{\ell \sim \mu^k(T)}[\Pr_{z \sim \mathrm{BerSum}(p(\ell))}[z \le \mathrm{thr}]]$
where $p(\ell)_i = (\mathrm{Dens}_H(\ell, i) - \mathrm{Adv}_H(\ell, i)) / 2$. -/
theorem lem_threshold_accuracy_from_stats {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {H : (Fin n → Bool) → ℝ} (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)) (thr : ℝ) :
    1 - randThresholdError μ f thr T ≤
      leafExpect μ T (fun t ℓ ↦
        berSumCdf (fun i ↦ (hardcoreDensityAt μ H t ℓ i - hardcoreAdvantageAt μ f H t ℓ i) / 2)
          thr) := by
  classical
  have hcompl : 1 - randThresholdError μ f thr T =
      T.weights.sum fun t w ↦ w *
        ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
          if (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) ≤ thr then 1 else 0 := by
    have hdet (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) :
        1 - detThresholdError μ f thr t =
          ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            if (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) ≤ thr then 1 else 0 := by
      rw [detThresholdError_eq_sum]
      have h1 : (1 : ℝ) = ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal :=
        (Cslib.Probability.PMF.sum_toReal (prodPMF μ k)).symm
      conv_lhs => arg 1; rw [h1]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun X _ ↦ ?_
      by_cases h : (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) ≤ thr
      · have hnot : ¬(thr < (hammingDist (evalBlock t X) (directProduct f k X) : ℝ)) :=
          not_lt.mpr h
        simp only [h, hnot, ite_true, ite_false, mul_one, mul_zero, sub_zero]
      · have hgt : thr < (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) :=
          lt_of_not_ge h
        simp only [h, hgt, ite_false, ite_true, mul_one, mul_zero, sub_self]
    calc 1 - randThresholdError μ f thr T
        = (T.weights.sum fun _ w ↦ w * (1 : ℝ)) -
            T.weights.sum fun t w ↦ w * detThresholdError μ f thr t := by
          rw [randThresholdError_eq_sum]
          simp [T.total]
      _ = T.weights.sum fun t w ↦ w * (1 - detThresholdError μ f thr t) := by
          simp only [Finsupp.sum, ← Finset.sum_sub_distrib, ← mul_sub]
      _ = _ := by simp_rw [hdet]
  rw [hcompl, leafExpect_eq_sum]
  refine Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
  rw [← sum_leafCondPMF_eq μ t
    (fun _ Y ↦ if (hammingDist (evalBlock t Y) (directProduct f k Y) : ℝ) ≤ thr then 1 else 0)]
  refine Finset.sum_le_sum fun X _ ↦ ?_
  by_cases hX : prodPMF μ k X = 0
  · simp [hX]
  · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have hsupp : pathBlock t X ∈ ((prodPMF μ k).map (pathBlock t)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨X, (PMF.mem_support_iff _ _).mpr hX, rfl⟩
    obtain ⟨ν, hν⟩ := claim_leaf_product μ t (pathBlock t X) hsupp
    let y : Fin k → Bool := evalBlock t X
    let q : Fin k → ℝ := fun i ↦ ∑ x : Fin n → Bool, (ν i x).toReal * if y i = f x then 0 else 1
    let p : Fin k → ℝ := fun i ↦
      (hardcoreDensityAt μ H t (pathBlock t X) i -
        hardcoreAdvantageAt μ f H t (pathBlock t X) i) / 2
    have hq_mem : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i ↦
      ⟨Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num),
       Cslib.Probability.PMF.sum_mul_le (ν i) _ 1 fun x ↦ by split_ifs <;> norm_num⟩
    have hp_mem : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      dsimp only [p]
      have h1 := hardcoreAdvantageAt_le_densityAt μ f hH t (pathBlock t X) i
      have h2 := hardcoreAdvantageAt_nonneg μ f H t (pathBlock t X) i
      have h3 := (hardcoreDensityAt_mem_Icc μ hH t (pathBlock t X) i).2
      exact ⟨by linarith, by linarith⟩
    have hprob_eq :
        (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
          if (hammingDist (evalBlock t Y) (directProduct f k Y) : ℝ) ≤ thr then 1 else 0) =
        berSumCdf q thr := by
      have hconst : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            if (hammingDist (evalBlock t Y) (directProduct f k Y) : ℝ) ≤ thr then 1 else 0) =
          ∑ Y : Fin k → Fin n → Bool, (Cslib.Probability.PMF.pi ν Y).toReal *
            if (trueCount (fun i ↦ decide (y i ≠ f (Y i))) : ℝ) ≤ thr then 1 else 0 := by
        rw [hν]
        refine Finset.sum_congr rfl fun Y _ ↦ ?_
        by_cases hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support
        · have hpath := mem_support_leafCondPMF_path_eq_ds μ t hX hY
          have hev : evalBlock t Y = y := DecisionTree.eval_eq_of_path_eq t hpath
          have hhd : hammingDist (evalBlock t Y) (directProduct f k Y) =
              trueCount (fun i ↦ decide (y i ≠ f (Y i))) := by
            rw [hev, hammingDist_eq_trueCount_decide]
            rfl
          rw [hhd]
        · have hY0 : Cslib.Probability.PMF.pi ν Y = 0 := by
            rw [← hν]; exact (PMF.apply_eq_zero_iff _ _).mpr hY
          simp [hY0]
      rw [hconst]
      have hmap : (Cslib.Probability.PMF.pi ν).map (fun Y i ↦ decide (y i ≠ f (Y i))) =
          berSumPMF q := by
        rw [berSumPMF_eq_pi, ← Cslib.Probability.PMF.pi_map ν (fun i x ↦ decide (y i ≠ f x))]
        congr 1
        funext i
        ext b
        apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
        rw [Cslib.Probability.PMF.map_apply_toReal]
        cases b
        · rw [bernoulliPMF_apply_false (hq_mem i).1 (hq_mem i).2]
          have h1 : (1 : ℝ) = ∑ x : Fin n → Bool, (ν i x).toReal :=
            (Cslib.Probability.PMF.sum_toReal (ν i)).symm
          rw [h1, show q i = ∑ x : Fin n → Bool, (ν i x).toReal * if y i = f x then 0 else 1
            from rfl, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          by_cases h : y i = f x <;> simp [h]
        · rw [bernoulliPMF_apply_true (hq_mem i).1 (hq_mem i).2]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          by_cases h : y i = f x <;> simp [h]
      rw [berSumCdf_eq_sum, ← hmap, Cslib.Probability.PMF.sum_map_mul]
    rw [hprob_eq]
    refine berSumCdf_antitone hp_mem hq_mem (fun i ↦ ?_) thr
    have hqi_eq : q i = (1 - ∑ Y : Fin k → Fin n → Bool,
        (leafCondPMF μ t (pathBlock t X) Y).toReal *
          (signBool (evalBlock t Y i) * signBool (f (Y i)))) / 2 := by
      have h1 : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (evalBlock t Y i) * signBool (f (Y i)))) =
          ∑ x : Fin n → Bool, (ν i x).toReal * (signBool (y i) * signBool (f x)) := by
        have hconst : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
              (signBool (evalBlock t Y i) * signBool (f (Y i)))) =
            ∑ Y : Fin k → Fin n → Bool, (Cslib.Probability.PMF.pi ν Y).toReal *
              (signBool (y i) * signBool (f (Y i))) := by
          rw [hν]
          refine Finset.sum_congr rfl fun Y _ ↦ ?_
          by_cases hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support
          · have hpath := mem_support_leafCondPMF_path_eq_ds μ t hX hY
            have hev : evalBlock t Y = y := DecisionTree.eval_eq_of_path_eq t hpath
            rw [hev]
          · have hY0 : Cslib.Probability.PMF.pi ν Y = 0 := by
              rw [← hν]; exact (PMF.apply_eq_zero_iff _ _).mpr hY
            simp [hY0]
        rw [hconst,
          Cslib.Probability.PMF.sum_pi_mul_eval ν i (fun x ↦ signBool (y i) * signBool (f x))]
      rw [h1]
      have hsum1 : (1 : ℝ) = ∑ x : Fin n → Bool, (ν i x).toReal :=
        (Cslib.Probability.PMF.sum_toReal (ν i)).symm
      calc q i = ∑ x : Fin n →
        Bool, (ν i x).toReal * ((1 - signBool (y i) * signBool (f x)) / 2) := by
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            rw [one_sub_signBool_mul_div_two]
        _ = (∑ x : Fin n → Bool, (ν i x).toReal -
              ∑ x : Fin n → Bool, (ν i x).toReal * (signBool (y i) * signBool (f x))) / 2 := by
            rw [← Finset.sum_sub_distrib, Finset.sum_div]
            exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ = _ := by rw [← hsum1]
    rw [hqi_eq]
    have hsplit : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
          (signBool (evalBlock t Y i) * signBool (f (Y i)))) ≤
        1 + hardcoreAdvantageAt μ f H t (pathBlock t X) i -
          hardcoreDensityAt μ H t (pathBlock t X) i := by
      have hdecomp : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (evalBlock t Y i) * signBool (f (Y i)))) =
          (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (f (Y i)) * signBool (evalBlock t Y i) * H (Y i))) +
          (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (f (Y i)) * signBool (evalBlock t Y i) * (1 - H (Y i)))) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hdecomp]
      have hpart1 : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (f (Y i)) * signBool (evalBlock t Y i) * H (Y i))) ≤
          hardcoreAdvantageAt μ f H t (pathBlock t X) i := by
        rw [hardcoreAdvantageAt_eq_abs]
        exact le_abs_self _
      have hpart2 : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (f (Y i)) * signBool (evalBlock t Y i) * (1 - H (Y i)))) ≤
          1 - hardcoreDensityAt μ H t (pathBlock t X) i := by
        have h1 : (1 : ℝ) = ∑ Y : Fin k → Fin n → Bool,
            (leafCondPMF μ t (pathBlock t X) Y).toReal :=
          (Cslib.Probability.PMF.sum_toReal _).symm
        calc (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
              (signBool (f (Y i)) * signBool (evalBlock t Y i) * (1 - H (Y i))))
            ≤ ∑ Y : Fin k → Fin n → Bool,
                (leafCondPMF μ t (pathBlock t X) Y).toReal * (1 - H (Y i)) := by
              refine Finset.sum_le_sum fun Y _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              have hprod_le : signBool (f (Y i)) * signBool (evalBlock t Y i) ≤ 1 := by
                rw [signBool_mul_eq_ite]; split_ifs <;> norm_num
              have h1H : 0 ≤ 1 - H (Y i) := sub_nonneg.mpr (hH (Y i)).2
              nlinarith
          _ = (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal) -
                hardcoreDensityAt μ H t (pathBlock t X) i := by
              rw [hardcoreDensityAt_eq_sum]
              simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
          _ = 1 - hardcoreDensityAt μ H t (pathBlock t X) i := by rw [← h1]
      linarith
    dsimp only [p]
    linarith

/-- Chernoff upper bound on `berSumCdf p thr`:
`berSumCdf p thr ≤ min 1 (exp(thr - (∑ i, p i) / 2))`. -/
theorem berSumCdf_le_min_exp {k : ℕ} {p : Fin k → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) {thr : ℝ} (hthr : 0 ≤ thr) :
    berSumCdf p thr ≤ min 1 (Real.exp (thr - (∑ i : Fin k, p i) / 2)) := by
  refine le_min ?_ ?_
  · rw [berSumCdf_eq_sum]
    exact Cslib.Probability.PMF.sum_mul_le (berSumPMF p) _ 1 fun _ ↦ by split_ifs <;> norm_num
  · set m : ℝ := ∑ i : Fin k, p i
    by_cases hm : m ≤ thr
    · rw [berSumCdf_eq_sum]
      exact (Cslib.Probability.PMF.sum_mul_le (berSumPMF p) _ 1 fun _ ↦ by
        split_ifs <;> norm_num).trans (Real.one_le_exp (by linarith))
    · push Not at hm
      have hmpos : 0 < m := lt_of_le_of_lt hthr hm
      have hscore : ∀ i : Fin k, ∀ b : Bool, b ∈ (bernoulliPMF (p i)).support →
          (if b = true then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
        intro _ b _; split_ifs <;> norm_num
      have hmean : (∑ i : Fin k, ∑ b : Bool,
          (bernoulliPMF (p i) b).toReal * if b = true then (1 : ℝ) else 0) = m := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Fintype.sum_bool, bernoulliPMF_apply_true (hp i).1 (hp i).2]
        simp
      have hch := (fact_chernoff (fun i : Fin k ↦ bernoulliPMF (p i))
        (fun _ b ↦ if b = true then (1 : ℝ) else 0) hscore).1 (t := thr)
      rw [hmean, ← berSumPMF_eq_pi] at hch
      have hcdf_eq : berSumCdf p thr =
          ∑ z : Fin k → Bool, (berSumPMF p z).toReal *
            if (∑ i : Fin k, if z i = true then (1 : ℝ) else 0) ≤ thr then 1 else 0 := by
        rw [berSumCdf_eq_sum]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [trueCount_cast_eq_sum]
      rw [hcdf_eq]
      refine (hch hmpos hm.le).trans (Real.exp_le_exp.mpr ?_)
      have hsq : 0 ≤ thr ^ 2 / (2 * m) := by positivity
      have hident : -((m - thr) ^ 2 / (2 * m)) = thr - m / 2 - thr ^ 2 / (2 * m) := by
        field_simp
        ring
      linarith

/-- For any hardcore measure `H`, tree `T`, and `thr ≥ 0`,
$\Pr_{X \sim \mu^k}[\lVert T(X) - f^{\otimes k}(X) \rVert_0 \le \mathrm{thr}] \le
 \mathbb{E}_{\ell \sim \mu^k(T)}[g_{\mathrm{thr}}(\mathrm{Dens}_H(\ell) -
 \mathrm{Adv}_H(\ell))]$. -/
theorem cor_threshold_from_stats_chernoff {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {H : (Fin n → Bool) → ℝ} (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool))
    {thr : ℝ} (hthr : 0 ≤ thr) :
    1 - randThresholdError μ f thr T ≤
      leafExpect μ T (fun t ℓ ↦
        gExp thr (hardcoreDensity μ H t ℓ - hardcoreAdvantage μ f H t ℓ)) := by
  refine (lem_threshold_accuracy_from_stats μ f hH T thr).trans ?_
  rw [leafExpect_eq_sum, leafExpect_eq_sum]
  refine Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
  refine Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have hp_mem : ∀ i : Fin k,
      (hardcoreDensityAt μ H t (pathBlock t X) i -
        hardcoreAdvantageAt μ f H t (pathBlock t X) i) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have h1 := hardcoreAdvantageAt_le_densityAt μ f hH t (pathBlock t X) i
    have h2 := hardcoreAdvantageAt_nonneg μ f H t (pathBlock t X) i
    have h3 := (hardcoreDensityAt_mem_Icc μ hH t (pathBlock t X) i).2
    exact ⟨by linarith, by linarith⟩
  refine (berSumCdf_le_min_exp hp_mem hthr).trans (le_of_eq ?_)
  have hsum : (∑ i : Fin k,
      (hardcoreDensityAt μ H t (pathBlock t X) i -
        hardcoreAdvantageAt μ f H t (pathBlock t X) i) / 2) =
      (hardcoreDensity μ H t (pathBlock t X) - hardcoreAdvantage μ f H t (pathBlock t X)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← hardcoreDensity_eq_sum,
      ← hardcoreAdvantage_eq_sum]
  rw [hsum, gExp]
  congr 2
  ring

/-- $\Pr_{X \sim \mu^k}[T(X) = f^{\otimes k}(X)] \le
 \mathbb{E}_{\ell \sim \mu^k(T)}[\exp(-(\mathrm{Dens}_H(\ell) - \mathrm{Adv}_H(\ell)) / 4)]$. -/
theorem lem_accuracy_from_hardcore_density_and_advantage {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {H : (Fin n → Bool) → ℝ} (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    1 - randProdDistError μ f T ≤
      leafExpect μ T (fun t ℓ ↦
        Real.exp (-((hardcoreDensity μ H t ℓ - hardcoreAdvantage μ f H t ℓ) / 4))) := by
  rw [randProdDistError_eq_randThresholdError]
  refine (cor_threshold_from_stats_chernoff μ f hH T (thr := 0) le_rfl).trans ?_
  rw [leafExpect_eq_sum, leafExpect_eq_sum]
  refine Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
  refine Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  simpa [zero_sub] using gExp_le_exp 0
    (hardcoreDensity μ H t (pathBlock t X) - hardcoreAdvantage μ f H t (pathBlock t X))

/-! ### -/

private theorem exp_neg_quarter_le : Real.exp (-(1 / 4 : ℝ)) ≤ 779 / 1000 := by
  have hsum : (∑ i ∈ Finset.range 4, ((1 / 4 : ℝ) ^ i / (Nat.factorial i : ℝ))) ≤
      Real.exp (1 / 4 : ℝ) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 4
  have hval : (∑ i ∈ Finset.range 4, ((1 / 4 : ℝ) ^ i / (Nat.factorial i : ℝ))) = 493 / 384 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  rw [hval] at hsum
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- $\mathbb{E}_{\ell \sim \mu^k(T)}[g_{\delta k / 10}(\mathrm{Dens}_H(\ell))] \le
 e^{-0.121 \delta k}$. -/
theorem lem_error_no_advantage {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    let δ := ∑ x : Fin n → Bool, (μ x).toReal * H x
    leafExpect μ T (fun t ℓ ↦ gExp (δ * k / 10) (hardcoreDensity μ H t ℓ)) ≤
      Real.exp (-(121 / 1000 : ℝ) * (δ * k)) := by
  intro δ
  have hδ0 : 0 ≤ δ := Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (hH x).1
  have hδ1 : δ ≤ 1 := Cslib.Probability.PMF.sum_mul_le μ H 1 fun x ↦ (hH x).2
  have hstep1 : leafExpect μ T (fun t ℓ ↦ gExp (δ * k / 10) (hardcoreDensity μ H t ℓ)) ≤
      Real.exp (δ * k / 10) *
        leafExpect μ T (fun t ℓ ↦ Real.exp (-(1 / 4 : ℝ) * hardcoreDensity μ H t ℓ)) := by
    simp only [leafExpect_eq_sum, Finsupp.sum]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    rw [← mul_assoc, mul_comm (Real.exp (δ * k / 10)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun X _ ↦ ?_
    rw [← mul_assoc, mul_comm (Real.exp (δ * k / 10)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    refine (gExp_le_exp _ _).trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hconv : ConvexOn ℝ Set.univ (fun z : ℝ ↦ Real.exp (-(1 / 4 : ℝ) * z)) :=
    convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ (-(1 / 4 : ℝ)))
  have hstep2 : leafExpect μ T (fun t ℓ ↦ Real.exp (-(1 / 4 : ℝ) * hardcoreDensity μ H t ℓ)) ≤
      Real.exp (-(1 - Real.exp (-(1 / 4 : ℝ))) * (δ * k)) := by
    refine (lem_resilience_general μ hH hconv T).trans ?_
    rw [mgf_binomial hδ0 hδ1 (-(1 / 4 : ℝ))]
    have hbase0 : 0 ≤ 1 + δ * (Real.exp (-(1 / 4 : ℝ)) - 1) := by
      have hexp := (Real.exp_pos (-(1 / 4 : ℝ))).le
      nlinarith
    have hbase1 : 1 + δ * (Real.exp (-(1 / 4 : ℝ)) - 1) ≤
        Real.exp (δ * (Real.exp (-(1 / 4 : ℝ)) - 1)) := by
      linarith [Real.add_one_le_exp (δ * (Real.exp (-(1 / 4 : ℝ)) - 1))]
    calc (1 + δ * (Real.exp (-(1 / 4 : ℝ)) - 1)) ^ k
        ≤ (Real.exp (δ * (Real.exp (-(1 / 4 : ℝ)) - 1))) ^ k :=
          pow_le_pow_left₀ hbase0 hbase1 k
      _ = Real.exp (-(1 - Real.exp (-(1 / 4 : ℝ))) * (δ * k)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  refine hstep1.trans ?_
  refine (mul_le_mul_of_nonneg_left hstep2 (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hnum := exp_neg_quarter_le
  have hdk : 0 ≤ δ * (k : ℝ) := by positivity
  nlinarith

/-- For all `z, Δ, t` with `0 ≤ Δ`, $g_t(z - \Delta) \le g_t(z) + \Delta / 4$. -/
theorem prop_lipschitz_bounds_unscaled {thr z Δ : ℝ} (hΔ : 0 ≤ Δ) :
    gExp thr (z - Δ) ≤ gExp thr z + Δ / 4 := by
  have hlip : ∀ {a b : ℝ}, a ≤ b → min 1 (Real.exp b) - min 1 (Real.exp a) ≤ b - a := by
    intro a b hab
    by_cases hb : b ≤ 0
    · have ha : a ≤ 0 := hab.trans hb
      rw [min_eq_right (Real.exp_le_one_iff.mpr hb), min_eq_right (Real.exp_le_one_iff.mpr ha)]
      have hsub := Real.add_one_le_exp (a - b)
      have hmul : Real.exp b * (1 + (a - b)) ≤ Real.exp b * Real.exp (a - b) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos b).le
      rw [← Real.exp_add, show b + (a - b) = a by ring] at hmul
      have hbe : Real.exp b ≤ 1 := Real.exp_le_one_iff.mpr hb
      nlinarith
    · push Not at hb
      rw [min_eq_left (Real.one_le_exp hb.le)]
      by_cases ha : a ≤ 0
      · rw [min_eq_right (Real.exp_le_one_iff.mpr ha)]
        have := Real.add_one_le_exp a
        linarith
      · push Not at ha
        rw [min_eq_left (Real.one_le_exp ha.le)]
        linarith
  have := hlip (a := thr - z / 4) (b := thr - (z - Δ) / 4) (by linarith)
  simp only [gExp]
  linarith

/-- For all `z, Δ, t` with `0 < t`, `0 ≤ Δ`, and `5 * t ≤
 z`, $g_t(z - \Delta) \le g_t(z) + \Delta / t$. -/
theorem prop_lipschitz_bounds_scaled {thr z Δ : ℝ} (hthr : 0 < thr) (hΔ : 0 ≤ Δ)
    (hz : 5 * thr ≤ z) :
    gExp thr (z - Δ) ≤ gExp thr z + Δ / thr := by
  have hz4 : 4 * thr ≤ z := by linarith
  have hgt_z : gExp thr z = Real.exp (thr - z / 4) := gExp_eq_exp_of_ge thr z hz4
  have hgap : thr ≤ z - 4 * thr := by linarith
  by_cases hbig : z - 4 * thr ≤ Δ
  · have hle1 : gExp thr (z - Δ) ≤ 1 := gExp_le_one _ _
    have hnn : 0 ≤ gExp thr z := gExp_nonneg _ _
    have h1 : 1 ≤ Δ / thr := (one_le_div hthr).mpr (hgap.trans hbig)
    linarith
  · push Not at hbig
    have hzΔ : 4 * thr ≤ z - Δ := by linarith
    rw [gExp_eq_exp_of_ge thr (z - Δ) hzΔ, hgt_z]
    have hconv : ConvexOn ℝ Set.univ (fun u : ℝ ↦ Real.exp (thr - u / 4)) := by
      have haff : ConvexOn ℝ Set.univ (fun u : ℝ ↦ Real.exp (-(1 / 4 : ℝ) * u + thr)) :=
        convexOn_exp.comp_affineMap
          { toFun := fun u ↦ -(1 / 4 : ℝ) * u + thr
            linear := LinearMap.mulLeft ℝ (-(1 / 4 : ℝ))
            map_vadd' := fun p v ↦ by simp [vadd_eq_add]; ring }
      simpa [sub_eq_add_neg, add_comm, mul_comm, div_eq_mul_inv] using haff
    have hsec : Real.exp (thr - (z - Δ) / 4) - Real.exp (thr - z / 4) ≤
        (Δ / (z - 4 * thr)) * (Real.exp (thr - (4 * thr) / 4) - Real.exp (thr - z / 4)) := by
      have hpos : 0 < z - 4 * thr := by linarith
      let s : ℝ := Δ / (z - 4 * thr)
      have hs0 : 0 ≤ s := div_nonneg hΔ hpos.le
      have hs1 : s ≤ 1 := (div_le_one hpos).mpr hbig.le
      have hcomb : s * (4 * thr) + (1 - s) * z = z - Δ := by
        simp only [s]
        field_simp
        ring
      have hc := hconv.2 (Set.mem_univ (4 * thr)) (Set.mem_univ z) hs0 (sub_nonneg.mpr hs1)
        (by ring)
      simp only [smul_eq_mul] at hc
      rw [hcomb] at hc
      linarith
    have h4 : Real.exp (thr - 4 * thr / 4) = 1 := by
      rw [show thr - 4 * thr / 4 = 0 by ring, Real.exp_zero]
    rw [h4] at hsec
    have hpos : 0 < z - 4 * thr := by linarith
    have hdiv : Δ / (z - 4 * thr) ≤ Δ / thr :=
      div_le_div_of_nonneg_left hΔ hthr hgap
    have hexp_nn : 0 ≤ Real.exp (thr - z / 4) := (Real.exp_pos _).le
    have hsub_le : 1 - Real.exp (thr - z / 4) ≤ 1 := by linarith
    have hmul : (Δ / (z - 4 * thr)) * (1 - Real.exp (thr - z / 4)) ≤ Δ / thr := by
      calc (Δ / (z - 4 * thr)) * (1 - Real.exp (thr - z / 4))
          ≤ (Δ / (z - 4 * thr)) * 1 := mul_le_mul_of_nonneg_left hsub_le (by positivity)
        _ = Δ / (z - 4 * thr) := mul_one _
        _ ≤ Δ / thr := hdiv
    linarith

/-! ### -/

private theorem exp_sum_lt_for_gt_forty {x : ℝ} (hx : 40 < x) :
    Real.exp (-(x / 8)) + Real.exp (-(121 / 1000 : ℝ) * x) ≤ Real.exp (-(x / 10)) := by
  have h1 : Real.exp (-(x / 40)) ≤ 1 / 2 := by
    have h40 : (1 : ℝ) ≤ x / 40 := by linarith
    have h := Real.add_one_le_exp (x / 40)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have h2 : Real.exp (-(21 / 1000 : ℝ) * x) ≤ 1 / 2 := by
    have h84 : (84 / 100 : ℝ) ≤ (21 / 1000 : ℝ) * x := by linarith
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (21 / 1000 : ℝ) * x by linarith) 3
    have hval : (∑ i ∈ Finset.range 3, ((21 / 1000 : ℝ) * x) ^ i / (Nat.factorial i : ℝ)) =
        1 + (21 / 1000 : ℝ) * x + ((21 / 1000 : ℝ) * x) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hval] at hsum
    have hge2 : (2 : ℝ) ≤ Real.exp ((21 / 1000 : ℝ) * x) := by nlinarith
    rw [show -(21 / 1000 : ℝ) * x = -((21 / 1000 : ℝ) * x) by ring, Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    exact hge2
  have hfactor : Real.exp (-(x / 8)) + Real.exp (-(121 / 1000 : ℝ) * x) =
      Real.exp (-(x / 10)) * (Real.exp (-(x / 40)) + Real.exp (-(21 / 1000 : ℝ) * x)) := by
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [hfactor]
  have hsum_le : Real.exp (-(x / 40)) + Real.exp (-(21 / 1000 : ℝ) * x) ≤ 1 := by linarith
  nlinarith [Real.exp_pos (-(x / 10))]

/-- If `f` has a `(γ, d)`-hardcore measure of density `δ` w.r.t. `μ` (with `0 ≤ γ`), then every
randomized tree `T` for $f^{\otimes k}$ of expected depth at most `k * d` satisfies
$\Pr_{X \sim \mu^k}[\lVert T(X) - f^{\otimes k}(X) \rVert_0 \le \delta k / 10] \le
 e^{-\delta k / 10} + 10 \gamma$. -/
theorem thm_bounds_from_hardcore {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {H : (Fin n → Bool) → ℝ} {γ d δ : ℝ}
    (hγ : 0 ≤ γ) (hH : IsHardcoreMeasure μ f γ d δ H)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool))
    (hdepth : randProdExpectedDepth μ T ≤ (k : ℝ) * d) :
    1 - randThresholdError μ f (δ * k / 10) T ≤ Real.exp (-(δ * k / 10)) + 10 * γ := by
  have hδ0 : 0 ≤ δ := by
    rw [← hH.density]
    exact Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (hH.mem_Icc x).1
  have hdk : 0 ≤ δ * (k : ℝ) := by positivity
  have hadv : leafExpect μ T (hardcoreAdvantage μ f H) ≤ γ * (δ * (k : ℝ)) := by
    have := lem_expected_total_hardcore_advantage μ f hH T (by linarith)
    rwa [claim_expected_total_hardcore_density μ hH.density T] at this
  have hno := lem_error_no_advantage μ hH.mem_Icc T
  rw [hH.density] at hno
  have hch := cor_threshold_from_stats_chernoff μ f hH.mem_Icc T (thr := δ * k / 10) (by positivity)
  refine hch.trans ?_
  by_cases hsmall : δ * (k : ℝ) ≤ 40
  · have hlip : leafExpect μ T (fun t ℓ ↦
        gExp (δ * k / 10) (hardcoreDensity μ H t ℓ - hardcoreAdvantage μ f H t ℓ)) ≤
        leafExpect μ T (fun t ℓ ↦ gExp (δ * k / 10) (hardcoreDensity μ H t ℓ)) +
          leafExpect μ T (hardcoreAdvantage μ f H) / 4 := by
      simp only [leafExpect_eq_sum, Finsupp.sum]
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ ↦ ?_
      rw [mul_div_assoc (T.weights t), ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun X _ ↦ ?_
      rw [mul_div_assoc (prodPMF μ k X).toReal, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      exact prop_lipschitz_bounds_unscaled (hardcoreAdvantage_nonneg μ f H t _)
    have hexp : Real.exp (-(121 / 1000 : ℝ) * (δ * k)) ≤ Real.exp (-(δ * k / 10)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  · push Not at hsmall
    have hthr_pos : 0 < δ * (k : ℝ) / 10 := by linarith
    have hres := (lem_resilience μ hH.mem_Icc T).1
    rw [hH.density] at hres
    have hsplit : leafExpect μ T (fun t ℓ ↦
        gExp (δ * k / 10) (hardcoreDensity μ H t ℓ - hardcoreAdvantage μ f H t ℓ)) ≤
        leafExpect μ T (fun t ℓ ↦ gExp (δ * k / 10) (hardcoreDensity μ H t ℓ)) +
          leafExpect μ T (fun t ℓ ↦ if hardcoreDensity μ H t ℓ ≤ δ * k / 2 then 1 else 0) +
          (10 / (δ * k)) * leafExpect μ T (hardcoreAdvantage μ f H) := by
      simp only [leafExpect_eq_sum, Finsupp.sum]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ ↦ ?_
      rw [← mul_assoc, mul_comm (10 / (δ * k)), mul_assoc, ← mul_add, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun X _ ↦ ?_
      rw [← mul_assoc, mul_comm (10 / (δ * k)), mul_assoc, ← mul_add, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      set z := hardcoreDensity μ H t (pathBlock t X)
      set Δ := hardcoreAdvantage μ f H t (pathBlock t X)
      have hΔ : 0 ≤ Δ := hardcoreAdvantage_nonneg μ f H t _
      by_cases hz : z ≤ δ * k / 2
      · simp only [hz, ite_true]
        have h1 := gExp_le_one (δ * k / 10) (z - Δ)
        have h2 := gExp_nonneg (δ * k / 10) z
        have h3 : 0 ≤ (10 / (δ * k)) * Δ := by positivity
        linarith
      · push Not at hz
        simp only [not_le.mpr hz, ite_false, add_zero]
        have h5 : 5 * (δ * k / 10) ≤ z := by linarith
        have hsc := prop_lipschitz_bounds_scaled hthr_pos hΔ h5
        have hdiv : Δ / (δ * k / 10) = (10 / (δ * k)) * Δ := by field_simp
        linarith
    have hterm : (10 / (δ * (k : ℝ))) * leafExpect μ T (hardcoreAdvantage μ f H) ≤ 10 * γ := by
      have hdk_pos : 0 < δ * (k : ℝ) := by linarith
      have h1 : (10 / (δ * (k : ℝ))) * leafExpect μ T (hardcoreAdvantage μ f H) ≤
          (10 / (δ * (k : ℝ))) * (γ * (δ * (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hadv (by positivity)
      have h2 : (10 / (δ * (k : ℝ))) * (γ * (δ * (k : ℝ))) = 10 * γ := by
        have hne : δ * (k : ℝ) ≠ 0 := by linarith
        rw [mul_comm γ, ← mul_assoc, div_mul_cancel₀ _ hne]
      linarith
    have hexp := exp_sum_lt_for_gt_forty hsmall
    linarith

/-! ###, 4.1, and 1.1: Strong Direct Sum Theorems -/

/-- For every `f`, `μ`, `k`, and `γ, δ ∈ (0, 1)`, every randomized tree `T` for $f^{\otimes k}$ with
error at most $1 - e^{-\delta k / 20} - \gamma$ at mistake threshold $\lfloor \delta k / 20 \rfloor$
has expected depth at least $\frac{\gamma^2 k}{4000 \log(1/\delta)} \cdot
 \overline{\mathrm{Depth}}^\mu(f, \delta)$. -/
theorem thm_threshold_direct_sum_forall {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool))
    (hT : randThresholdError μ f (⌊δ * k / 20⌋₊ : ℕ) T ≤
      1 - Real.exp (-(δ * k / 20)) - γ) :
    γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      randProdExpectedDepth μ T := by
  by_cases hpos : 0 < distDepth μ f δ
  · have hγ'_pos : 0 < γ / 20 := by linarith
    have hγ'_le : γ / 20 ≤ 1 := by linarith
    obtain ⟨H, hH⟩ := hardcoreTheorem μ f hγ'_pos hγ'_le hδ0 hpos
    by_contra! hlt
    have hd_eq : (k : ℝ) * ((γ / 20) ^ 2 / (10 * Real.log (1 / δ)) * distDepth μ f δ) =
        γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ := by ring
    have hbound := thm_bounds_from_hardcore μ f hγ'_pos.le hH T (by linarith)
    have hthr_eq : randThresholdError μ f ((δ / 2) * k / 10) T =
        randThresholdError μ f (⌊δ * k / 20⌋₊ : ℕ) T := by
      rw [randThresholdError_eq_sum, randThresholdError_eq_sum, Finsupp.sum, Finsupp.sum]
      refine Finset.sum_congr rfl fun t _ ↦ congrArg _ ?_
      rw [detThresholdError_eq_sum, detThresholdError_eq_sum]
      refine Finset.sum_congr rfl fun X _ ↦ congrArg _ ?_
      have hiff : (δ / 2) * (k : ℝ) / 10 <
            (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) ↔
          ((⌊δ * (k : ℝ) / 20⌋₊ : ℕ) : ℝ) <
            (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) := by
        rw [show (δ / 2) * (k : ℝ) / 10 = δ * (k : ℝ) / 20 by ring]
        constructor <;> intro h
        · exact lt_of_le_of_lt (Nat.floor_le (by positivity)) h
        · have hnat : ⌊δ * (k : ℝ) / 20⌋₊ < hammingDist (evalBlock t X) (directProduct f k X) := by
            exact_mod_cast h
          by_contra! hle
          have := (Nat.le_floor_iff (by positivity)).mpr hle
          omega
      simp [hiff]
    rw [hthr_eq, show (δ / 2) * (k : ℝ) / 10 = δ * (k : ℝ) / 20 by ring,
      show 10 * (γ / 20) = γ / 2 by ring] at hbound
    linarith
  · have hzero : distDepth μ f δ = 0 := le_antisymm (not_lt.mp hpos) (distDepth_nonneg μ f δ)
    rw [hzero, mul_zero]
    exact randProdExpectedDepth_nonneg μ T

/-- For every `f`, `μ`, `k`, and `γ, δ ∈ (0, 1)` with nonnegative error budget
`0 ≤ 1 - exp(-(δ k / 20)) - γ`,
$\overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, 1 - e^{-\delta k / 20} - \gamma,
 \lfloor \delta k / 20 \rfloor) \ge
 \frac{\gamma^2 k}{4000 \log(1/\delta)} \cdot \overline{\mathrm{Depth}}^\mu(f, \delta)$. -/
theorem thm_threshold_direct_sum {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ)
    (hε : 0 ≤ 1 - Real.exp (-(δ * k / 20)) - γ) :
    γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      thresholdDistDepth μ f k (1 - Real.exp (-(δ * k / 20)) - γ) ⌊δ * k / 20⌋₊ :=
  le_thresholdDistDepth μ f k hε _ fun T hT ↦
    thm_threshold_direct_sum_forall μ f hγ0 hγ1 hδ0 T hT

/-- Every randomized tree `T` for $f^{\otimes k}$ with error at most $1 - e^{-\delta k / 20} -
\gamma$
has expected depth at least $\frac{\gamma^2 k}{4000 \log(1/\delta)} \cdot
 \overline{\mathrm{Depth}}^\mu(f, \delta)$. -/
theorem thm_strong_direct_sum_forall {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool))
    (hT : randProdDistError μ f T ≤ 1 - Real.exp (-(δ * k / 20)) - γ) :
    γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      randProdExpectedDepth μ T := by
  refine thm_threshold_direct_sum_forall μ f hγ0 hγ1 hδ0 T ?_
  rw [randProdDistError_eq_randThresholdError] at hT
  rw [randThresholdError_eq_sum] at hT ⊢
  refine (Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)).trans hT
  rw [detThresholdError_eq_sum, detThresholdError_eq_sum]
  refine Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt (Nat.cast_nonneg _) h1) h2
  · exact zero_le_one
  · exact le_rfl

/-- For every `f`, `μ`, `k`, and `γ, δ ∈ (0, 1)` with `0 ≤ 1 - exp(-(δ k / 20)) - γ`,
$\overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, 1 - e^{-\delta k / 20} - \gamma) \ge
 \frac{\gamma^2 k}{4000 \log(1/\delta)} \cdot \overline{\mathrm{Depth}}^\mu(f, \delta)$. -/
theorem thm_strong_direct_sum {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ)
    (hε : 0 ≤ 1 - Real.exp (-(δ * k / 20)) - γ) :
    γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      prodDistDepth μ f k (1 - Real.exp (-(δ * k / 20)) - γ) :=
  (thm_threshold_direct_sum μ f hγ0 hγ1 hδ0 hε).trans
    (thresholdDistDepth_le_prodDistDepth μ f k hε _)

/-- for every `f`, `μ`, `k ≥ 1`, and `0 < ε ≤ 1/2`,
$\overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, \varepsilon) \ge
 \frac{\varepsilon^2 k}{64000 \log(k / (80 \varepsilon))} \cdot
 \overline{\mathrm{Depth}}^\mu(f, 80 \varepsilon / k)$. -/
theorem thm_main_intro {n k : ℕ} (hk : 1 ≤ k)
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ε ^ 2 * k / (64000 * Real.log (k / (80 * ε))) * distDepth μ f (80 * ε / k) ≤
      prodDistDepth μ f k ε := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  by_cases hδ : (1 / 2 : ℝ) ≤ 80 * ε / k
  · rw [distDepth_eq_zero_of_half_le μ f hδ, mul_zero]
    exact prodDistDepth_nonneg μ f k ε
  · push Not at hδ
    have hδ0 : 0 < 80 * ε / k := by positivity
    have hγ0 : 0 < ε / 4 := by linarith
    have hγ1 : ε / 4 < 1 := by linarith
    have h_err : ε ≤ 1 - Real.exp (-((80 * ε / k) * k / 20)) - ε / 4 := by
      have hsimp : (80 * ε / k) * (k : ℝ) / 20 = 4 * ε := by field_simp; ring
      rw [hsimp]
      have hexp : Real.exp (-(4 * ε)) ≤ 1 - (5 / 4 : ℝ) * ε := by
        by_cases hq : ε ≤ 1 / 4
        · have h := Real.exp_neg_le_one_sub_add_sq_div_two (show (0 : ℝ) ≤ 4 * ε by linarith)
          nlinarith
        · push Not at hq
          have h1 : Real.exp (-(4 * ε)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
          have h2 : Real.exp (-1) ≤ 3 / 8 := by
            have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
            have hval : (∑ i ∈ Finset.range 4, (1 : ℝ) ^ i / (Nat.factorial i : ℝ)) = 8 / 3 := by
              simp [Finset.sum_range_succ, Nat.factorial]; norm_num
            rw [hval] at hsum
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
            linarith
          linarith
      linarith
    have hε' : 0 ≤ 1 - Real.exp (-((80 * ε / k) * k / 20)) - ε / 4 := hε0.le.trans h_err
    have hmain := thm_strong_direct_sum μ f hγ0 hγ1 hδ0 hε'
    have hanti : prodDistDepth μ f k (1 - Real.exp (-((80 * ε / k) * k / 20)) - ε / 4) ≤
        prodDistDepth μ f k ε :=
      prodDistDepth_antitone_error μ f k hε0.le h_err
    have hcoef : (ε / 4) ^ 2 * k / (4000 * Real.log (1 / (80 * ε / k))) =
        ε ^ 2 * k / (64000 * Real.log (k / (80 * ε))) := by
      rw [one_div_div]
      ring
    rw [hcoef] at hmain
    exact hmain.trans hanti

/-- Parametric form of for every fixed ceiling `ε₀ < 1`:
for all `0 < ε ≤ ε₀`, `f`, `μ`, and `k ≥ 1`, choosing `δ = C * ε / k` and `γ = ((1 - ε₀)/2) * ε`
yields the $\tilde{\Omega}(\varepsilon^2 k) \cdot \overline{\mathrm{Depth}}^\mu(f,
\Theta(\varepsilon/k))$
bound. -/
theorem thm_main_intro_of_le {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {n k : ℕ} (_hk : 1 ≤ k) (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
        {ε : ℝ} (_hε0 : 0 < ε) (_hε1 : ε ≤ ε₀),
        c * (ε ^ 2 * k / Real.log (k / (C * ε))) * distDepth μ f (C * ε / k) ≤
          prodDistDepth μ f k ε := by
  let C : ℝ := 20 * (1 + Real.log (2 / (1 - ε₀))) / ε₀
  let γc : ℝ := (1 - ε₀) / 2
  have hpos_log : 0 < Real.log (2 / (1 - ε₀)) :=
    Real.log_pos (by rw [one_lt_div (by linarith)]; linarith)
  have hCpos : 0 < C := by positivity
  refine ⟨γc ^ 2 / 4000, C, by positivity, hCpos, ?_⟩
  intro n k hk μ f ε hε0 hε1
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  by_cases hδ : (1 / 2 : ℝ) ≤ C * ε / k
  · rw [distDepth_eq_zero_of_half_le μ f hδ, mul_zero]
    exact prodDistDepth_nonneg μ f k ε
  · push Not at hδ
    have hδ0 : 0 < C * ε / k := by positivity
    have hγ0 : 0 < γc * ε := by positivity
    have hγ1 : γc * ε < 1 := by
      have h1 : γc < 1 / 2 := by dsimp [γc]; linarith
      nlinarith
    have h_err : ε ≤ 1 - Real.exp (-((C * ε / k) * k / 20)) - γc * ε := by
      have hsimp : (C * ε / k) * (k : ℝ) / 20 =
          (1 + Real.log (2 / (1 - ε₀))) * (ε / ε₀) := by
        simp only [C]; field_simp
      rw [hsimp]
      have hexp : Real.exp (-((1 + Real.log (2 / (1 - ε₀))) * (ε / ε₀))) ≤
          1 - (1 + γc) * ε := by
        have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) ε₀)
            (fun u ↦ Real.exp (-((1 + Real.log (2 / (1 - ε₀))) * (u / ε₀)))) := by
          refine (convexOn_exp.comp_linearMap
            (LinearMap.mulLeft ℝ (-((1 + Real.log (2 / (1 - ε₀))) / ε₀)))).subset
            (Set.subset_univ _) (convex_Icc 0 ε₀) |>.congr fun u _ ↦ ?_
          dsimp; congr 1; ring
        have hsec := hconv.2 (Set.left_mem_Icc.mpr hε₀0.le) (Set.right_mem_Icc.mpr hε₀0.le)
          (show 0 ≤ 1 - ε / ε₀ by rw [sub_nonneg, div_le_one hε₀0]; exact hε1)
          (show 0 ≤ ε / ε₀ by positivity) (by ring)
        simp only [smul_eq_mul, zero_div, mul_zero, neg_zero, Real.exp_zero, mul_one,
          div_self (ne_of_gt hε₀0), zero_add, div_mul_cancel₀ _ (ne_of_gt hε₀0)] at hsec
        have hat1 : Real.exp (-(1 + Real.log (2 / (1 - ε₀)))) ≤ (1 - ε₀) / 2 := by
          rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
            Real.exp_log (div_pos (by norm_num) (by linarith)), inv_div]
          have he1 : (Real.exp 1)⁻¹ ≤ 1 := by
            rw [← Real.exp_neg]
            exact Real.exp_le_one_iff.mpr (by norm_num)
          nlinarith
        have hlin : (1 - ε / ε₀) + ε / ε₀ * ((1 - ε₀) / 2) = 1 - (1 + ε₀) / 2 * (ε / ε₀) := by
          ring
        have hε_div : (1 + γc) * ε ≤ (1 + ε₀) / 2 * (ε / ε₀) := by
          rw [mul_div_assoc', le_div_iff₀ hε₀0]
          dsimp only [γc]
          nlinarith [sq_nonneg (1 - ε₀)]
        have hmul : ε / ε₀ * Real.exp (-(1 + Real.log (2 / (1 - ε₀)))) ≤
            ε / ε₀ * ((1 - ε₀) / 2) :=
          mul_le_mul_of_nonneg_left hat1 (by positivity)
        linarith
      linarith
    have hε' : 0 ≤ 1 - Real.exp (-((C * ε / k) * k / 20)) - γc * ε := hε0.le.trans h_err
    have hmain := thm_strong_direct_sum μ f hγ0 hγ1 hδ0 hε'
    have hanti : prodDistDepth μ f k (1 - Real.exp (-((C * ε / k) * k / 20)) - γc * ε) ≤
        prodDistDepth μ f k ε :=
      prodDistDepth_antitone_error μ f k hε0.le h_err
    have hcoef : (γc * ε) ^ 2 * k / (4000 * Real.log (1 / (C * ε / k))) =
        γc ^ 2 / 4000 * (ε ^ 2 * k / Real.log (k / (C * ε))) := by
      rw [one_div_div]
      ring
    rw [hcoef] at hmain
    exact hmain.trans hanti

/-- Full-range `(0, 1)` corollary of showing explicit `(1 - ε)` dependence
when `ε` approaches `1`. -/
theorem thm_main_intro_full_range {n k : ℕ} (hk : 1 ≤ k)
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    let δ := 20 * Real.log (2 / (1 - ε)) / k
    (1 - ε) ^ 2 * k / (16000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      prodDistDepth μ f k ε := by
  intro δ
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  by_cases hδ : (1 / 2 : ℝ) ≤ δ
  · rw [distDepth_eq_zero_of_half_le μ f hδ, mul_zero]
    exact prodDistDepth_nonneg μ f k ε
  · push Not at hδ
    have hlog : 0 < Real.log (2 / (1 - ε)) :=
      Real.log_pos (by rw [one_lt_div (by linarith)]; linarith)
    have hδ0 : 0 < δ := by positivity
    have hγ0 : 0 < (1 - ε) / 2 := by linarith
    have hγ1 : (1 - ε) / 2 < 1 := by linarith
    have h_err : 1 - Real.exp (-(δ * k / 20)) - (1 - ε) / 2 = ε := by
      have hsimp : δ * (k : ℝ) / 20 = Real.log (2 / (1 - ε)) := by
        simp only [δ]; field_simp
      rw [hsimp, Real.exp_neg, Real.exp_log (div_pos (by norm_num) (by linarith)), inv_div]
      ring
    have hmain := thm_strong_direct_sum μ f hγ0 hγ1 hδ0 (by rw [h_err]; exact hε0.le)
    rw [h_err] at hmain
    refine le_trans ?_ hmain
    exact le_of_eq (by ring)

end CslibFrontier.Computability.QueryComplexity.DirectSum

end
