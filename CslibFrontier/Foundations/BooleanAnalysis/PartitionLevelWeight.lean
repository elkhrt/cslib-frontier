/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hypercontractive Level-Weight Bounds for Boolean Indicators and Message Partitions

General degree-`k` Fourier level-weight inequalities on the Boolean hypercube `{0, 1}^ι` derived
from `(1 + ρ, 2)`-hypercontractivity (`Cslib.BitString.noiseStability_le_lpNorm_sq`):

* `CslibFrontier.BooleanAnalysis.levelWeight_indicator_le_rpow`: for any `k : ℕ`, `0 < ρ ≤ 1`, and
  subset `A : Set (ι → Bool)`,
  $$W^k[1_A] \le \frac{1}{\rho^k} \left(\mathbb{E}_x[1_A(x)]\right)^{\frac{2}{1 + \rho}}.$$
* `CslibFrontier.BooleanAnalysis.sum_sqrt_levelWeight_indicator_fibers_le`: for any `k, l : ℕ` and
  `l`-bit encoding `enc : (ι → Bool) → BitString l` partitioning `{0, 1}^ι` into `2^l` message
  fibers,
  $$\sum_{m \in \{0, 1\}^l} \sqrt{W^k[1_{\{x \mid \mathrm{enc}(x) = m\}}]} \le
    2 \cdot (l + 1)^{k / 2}.$$
  At `k = 2`, this yields the $O(\sqrt{l + 1})$ Fourier level-2 partition bound underlying the
  $\Omega(\sqrt{n})$ one-way classical randomized communication lower bound for Hidden Matching
.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Finset Cslib Cslib.BitString
open scoped BigOperators

/-- **Degree-`k` hypercontractive level-weight bound for Boolean indicators**: for every `k : ℕ`,
`0 < ρ ≤ 1`, and subset `A : Set (ι → Bool)`,
$$W^k[1_A] \le \frac{1}{\rho^k} \left(\mathbb{E}_x [1_A(x)]\right)^{\frac{2}{1 + \rho}}.$$ -/
theorem levelWeight_indicator_le_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (A : Set (ι → Bool)) :
    levelWeight k (A.indicator 1) ≤
      (1 / ρ ^ k) * (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (2 / (1 + ρ)) := by
  have hdens_nn : 0 ≤ 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x :=
    Finset.expect_nonneg fun x _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
  by_cases hk : Fintype.card ι < k
  · rw [levelWeight_eq_zero_of_card_lt hk]
    positivity
  · have hmem : k ∈ Finset.range (Fintype.card ι + 1) := Finset.mem_range.mpr (by omega)
    have hstab : ρ ^ k * levelWeight k (A.indicator 1) ≤
        noiseStability ρ (A.indicator 1) := by
      rw [noiseStability_eq_sum_levelWeight]
      exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (pow_nonneg hρ0.le j)
        (levelWeight_nonneg j _)) hmem
    have hhyp : noiseStability ρ (A.indicator 1) ≤
        (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (2 / (1 + ρ)) := by
      calc noiseStability ρ (A.indicator 1)
        _ ≤ lpNorm (1 + ρ) (A.indicator 1) ^ 2 :=
            noiseStability_le_lpNorm_sq hρ0.le hρ1 (A.indicator 1)
        _ = ((𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (1 + ρ)⁻¹) ^ (2 : ℝ) := by
            rw [lpNorm_indicator_one (by linarith), Real.rpow_two]
        _ = (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (2 / (1 + ρ)) := by
            rw [← Real.rpow_mul hdens_nn, inv_mul_eq_div]
    have hρk : 0 < ρ ^ k := pow_pos hρ0 k
    rw [one_div_mul_eq_div, le_div_iff₀' hρk]
    exact hstab.trans hhyp

/-- **Hypercontractive partition inequality for `l`-bit encodings**: for every `k, l : ℕ` and
message map `enc : (ι → Bool) → BitString l`,
$$\sum_{m : \mathrm{BitString}\, l} \sqrt{W^k[1_{\{x \mid \mathrm{enc}(x) = m\}}]} \le
  2 \cdot (l + 1)^{k / 2}.$$ -/
theorem sum_sqrt_levelWeight_indicator_fibers_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k l : ℕ) (enc : (ι → Bool) → BitString l) :
    (∑ msg : BitString l,
      Real.sqrt (levelWeight k ({x : ι → Bool | enc x = msg}.indicator 1))) ≤
    2 * ((l : ℝ) + 1) ^ ((k : ℝ) / 2) := by
  classical
  let ρ : ℝ := 1 / ((l : ℝ) + 1)
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) l]) (by positivity)
  let α_m (msg : BitString l) : ℝ :=
    𝔼 x, ({x : ι → Bool | enc x = msg}.indicator (1 : (ι → Bool) → ℝ)) x
  have hα_nn : ∀ msg : BitString l, 0 ≤ α_m msg := fun msg ↦
    Finset.expect_nonneg fun x _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
  have hα_sum : ∑ msg : BitString l, α_m msg = 1 := by
    dsimp [α_m]
    rw [← Finset.expect_sum_comm]
    have hpt : ∀ x : ι → Bool,
        (∑ msg : BitString l,
          ({y : ι → Bool | enc y = msg}.indicator (1 : (ι → Bool) → ℝ)) x) = 1 := fun x ↦ by
      rw [Finset.sum_eq_single (enc x)]
      · simp
      · intro msg _ hne
        exact Set.indicator_of_notMem (by simpa using hne.symm) _
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    simp [hpt]
  have hpt_le : ∀ msg : BitString l,
      Real.sqrt (levelWeight k ({x : ι → Bool | enc x = msg}.indicator 1)) ≤
        ((l : ℝ) + 1) ^ ((k : ℝ) / 2) * (α_m msg) ^ (1 / (1 + ρ)) := by
    intro msg
    have hw := levelWeight_indicator_le_rpow k hρ0 hρ1 {x : ι → Bool | enc x = msg}
    calc Real.sqrt (levelWeight k ({x : ι → Bool | enc x = msg}.indicator 1))
      _ ≤ Real.sqrt ((1 / ρ ^ k) * (α_m msg) ^ (2 / (1 + ρ))) := Real.sqrt_le_sqrt hw
      _ = Real.sqrt (1 / ρ ^ k) * Real.sqrt ((α_m msg) ^ (2 / (1 + ρ))) :=
          Real.sqrt_mul (by positivity) _
      _ = ((l : ℝ) + 1) ^ ((k : ℝ) / 2) * (α_m msg) ^ (1 / (1 + ρ)) := by
          congr 1
          · have hinv : 1 / ρ ^ k = ((l : ℝ) + 1) ^ (k : ℝ) := by
              dsimp [ρ]
              rw [div_pow, one_pow, one_div_one_div, Real.rpow_natCast]
            rw [hinv, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
            ring_nf
          · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hα_nn msg)]
            congr 1; ring
  let p : ℝ := 1 / (1 + ρ)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]; exact div_le_one_of_le₀ (by linarith) (by positivity)
  have hconc := (Real.concaveOn_rpow hp0 hp1).le_map_sum
    (t := (Finset.univ : Finset (BitString l)))
    (w := fun _ ↦ (1 / (2 : ℝ) ^ l))
    (p := α_m)
    (fun _ _ ↦ by positivity)
    (by simp)
    (fun msg _ ↦ Set.mem_Ici.mpr (hα_nn msg))
  simp only [smul_eq_mul, ← Finset.mul_sum, hα_sum, mul_one] at hconc
  have hsum_αp : ∑ msg : BitString l, (α_m msg) ^ p ≤ 2 := by
    have h2l_pos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
    have hmul := mul_le_mul_of_nonneg_left hconc h2l_pos.le
    rw [← mul_assoc, mul_one_div_cancel h2l_pos.ne', one_mul] at hmul
    calc (∑ msg : BitString l, (α_m msg) ^ p)
      _ ≤ (2 : ℝ) ^ l * (1 / (2 : ℝ) ^ l) ^ p := hmul
      _ = (2 : ℝ) ^ ((l : ℝ) * (1 - p)) := by
          rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast (2 : ℝ) l,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_add (by norm_num)]
          congr 1; ring
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h1mp : 1 - p = (1 : ℝ) / ((l : ℝ) + 2) := by
            dsimp [p, ρ]; field_simp; ring
          rw [h1mp, mul_one_div]
          exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) l]) (by positivity)
      _ = 2 := Real.rpow_one 2
  calc (∑ msg : BitString l,
        Real.sqrt (levelWeight k ({x : ι → Bool | enc x = msg}.indicator 1)))
    _ ≤ ∑ msg : BitString l, ((l : ℝ) + 1) ^ ((k : ℝ) / 2) * (α_m msg) ^ p :=
        Finset.sum_le_sum fun msg _ ↦ hpt_le msg
    _ = ((l : ℝ) + 1) ^ ((k : ℝ) / 2) * ∑ msg : BitString l, (α_m msg) ^ p :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((l : ℝ) + 1) ^ ((k : ℝ) / 2) * 2 :=
        mul_le_mul_of_nonneg_left hsum_αp (by positivity)
    _ = 2 * ((l : ℝ) + 1) ^ ((k : ℝ) / 2) := mul_comm _ _

end CslibFrontier.BooleanAnalysis
