/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized.DirectSum

import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# XOR equivalence, tightness for Parity, lack of distributional error reduction, and witnesses

This module proves:

- the $k$-wise product tree $\tilde{T}$ achieves success probability on $f^{\otimes k}$ at least
 the advantage of $T$ on $f^{\oplus k}$.
- $\overline{\mathrm{Depth}}^{\mu^k}(f^{\oplus k}, \varepsilon / 2) \ge
 \overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, \varepsilon)$.
- (`claim_equivalence_direct_sum_xor`) and (`thm_strong_xor`,
 `thm_strong_xor_forall`): strong XOR lemma for distributional query complexity.
- leaves of depth `< n` err with
 probability `1/2` on `parity n` under the uniform distribution.
- $\overline{\mathrm{Depth}}^\mu(\mathsf{Par}, 1/4) = n / 2$ and
 $\overline{\mathrm{Depth}}^{\mu^k}(\mathsf{Par}^{\otimes k}, 1 - \gamma) \le
 2 \gamma k \cdot \overline{\mathrm{Depth}}^\mu(\mathsf{Par}, 1/4)$.
- **Counterexample for the corresponding result near `ε = 1`**
(`main_intro_counterexample_near_one`).
- distributional error reduction fails dramatically under the uniform distribution.
- **Joint non-vacuity witness** (`nonvacuity_hardcore_and_direct_sum`).
-/

public section

namespace CslibFrontier.Computability.QueryComplexity.DirectSum

open Cslib Convexity Finset
open scoped BigOperators ENNReal NNReal

/-! ### this module: Direct sum theorems imply XOR lemmas -/

private theorem mem_support_leafCondPMF_path_eq_xor {n k : ℕ} {β : Type*}
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

/-- For any `f`, `μ`, and deterministic tree `t : DecisionTree (Fin k × Fin n) Bool`, the $k$-wise
product tree $\tilde{t}$ satisfies
$\Pr_{X \sim \mu^k}[\tilde{t}(X) =
 f^{\otimes k}(X)] \ge \mathbb{E}_{X \sim \mu^k}[t(X) f^{\oplus k}(X)]$. -/
theorem lem_dpt_to_ds {n k : ℕ} (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    (t : DecisionTree (Fin k × Fin n) Bool) :
    (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
        (signBool (evalBlock t X) * signBool (directSum f k X))) ≤
      ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
        if evalBlock (productTree μ f t) X = directProduct f k X then 1 else 0 := by
  classical
  rw [← sum_leafCondPMF_eq μ t
    (fun _ Y ↦ signBool (evalBlock t Y) * signBool (directSum f k Y)),
    ← sum_leafCondPMF_eq μ t
    (fun _ Y ↦ if evalBlock (productTree μ f t) Y = directProduct f k Y then 1 else 0)]
  refine Finset.sum_le_sum fun X _ ↦ ?_
  by_cases hX : prodPMF μ k X = 0
  · simp [hX]
  · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have hsupp : pathBlock t X ∈ ((prodPMF μ k).map (pathBlock t)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨X, (PMF.mem_support_iff _ _).mpr hX, rfl⟩
    obtain ⟨ν, hν⟩ := claim_leaf_product μ t (pathBlock t X) hsupp
    let a : Fin k → ℝ := fun i ↦ ∑ x : Fin n → Bool, (ν i x).toReal * signBool (f x)
    have hmean_prod : ∀ g : Fin k → (Fin n → Bool) → ℝ,
        (∑ Y : Fin k → Fin n → Bool, (Cslib.Probability.PMF.pi ν Y).toReal *
          ∏ i : Fin k, g i (Y i)) =
        ∏ i : Fin k, ∑ x : Fin n → Bool, (ν i x).toReal * g i x := by
      intro g
      simp_rw [Cslib.Probability.PMF.pi_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum fun i x ↦ (ν i x).toReal * g i x).symm
    have hlhs :
        (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
          (signBool (evalBlock t Y) * signBool (directSum f k Y))) =
        signBool (evalBlock t X) * ∏ i : Fin k, a i := by
      have hconst : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            (signBool (evalBlock t Y) * signBool (directSum f k Y))) =
          ∑ Y : Fin k → Fin n → Bool, (Cslib.Probability.PMF.pi ν Y).toReal *
            (signBool (evalBlock t X) * ∏ i : Fin k, signBool (f (Y i))) := by
        rw [hν]
        refine Finset.sum_congr rfl fun Y _ ↦ ?_
        by_cases hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support
        · have hpath := mem_support_leafCondPMF_path_eq_xor μ t hX hY
          have hev : evalBlock t Y = evalBlock t X := DecisionTree.eval_eq_of_path_eq t hpath
          rw [hev, signBool_directSum]
        · have hY0 : Cslib.Probability.PMF.pi ν Y = 0 := by
            rw [← hν]; exact (PMF.apply_eq_zero_iff _ _).mpr hY
          simp [hY0]
      rw [hconst, ← hmean_prod]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    have hrhs :
        (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
          if evalBlock (productTree μ f t) Y = directProduct f k Y then 1 else 0) =
        ∏ i : Fin k, (1 + |a i|) / 2 := by
      have hconst : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            if evalBlock (productTree μ f t) Y = directProduct f k Y then 1 else 0) =
          ∑ Y : Fin k → Fin n → Bool, (Cslib.Probability.PMF.pi ν Y).toReal *
            ∏ i : Fin k,
              (if evalBlock (productTree μ f t) X i = f (Y i) then (1 : ℝ) else 0) := by
        rw [hν]
        refine Finset.sum_congr rfl fun Y _ ↦ ?_
        by_cases hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support
        · have hpath := mem_support_leafCondPMF_path_eq_xor μ t hX hY
          have hpt : evalBlock (productTree μ f t) Y = evalBlock (productTree μ f t) X := by
            funext i
            have h1 := eval_productTree μ f t Y i
            have h2 := eval_productTree μ f t X i
            rw [hpath] at h1
            have hiff := h1.trans h2.symm
            cases hY1 : evalBlock (productTree μ f t) Y i <;>
              cases hX1 : evalBlock (productTree μ f t) X i <;>
              simp [hY1, hX1] at hiff ⊢
          rw [hpt]
          congr 1
          by_cases heq : evalBlock (productTree μ f t) X = directProduct f k Y
          · rw [ite_eq_left heq]
            symm
            exact Finset.prod_eq_one fun i _ ↦ by simp [congrFun heq i, directProduct_apply]
          · rw [ite_eq_right heq]
            obtain ⟨i, hi⟩ : ∃ i, evalBlock (productTree μ f t) X i ≠ f (Y i) := by
              simpa [funext_iff, directProduct_apply] using heq
            exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
        · have hY0 : Cslib.Probability.PMF.pi ν Y = 0 := by
            rw [← hν]; exact (PMF.apply_eq_zero_iff _ _).mpr hY
          simp [hY0]
      rw [hconst, hmean_prod (fun i x ↦ if evalBlock (productTree μ f t) X i = f x then 1 else 0)]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      have hsign : signBool (evalBlock (productTree μ f t) X i) * a i = |a i| := by
        have h1 : (∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
            signBool (f (Y i))) = a i := by
          rw [hν, Cslib.Probability.PMF.sum_pi_mul_eval ν i (fun x ↦ signBool (f x))]
        have hev := eval_productTree μ f t X i
        rw [h1] at hev
        by_cases ha : 0 ≤ a i
        · have ht : evalBlock (productTree μ f t) X i = true := hev.mpr ha
          rw [ht, signBool_true, one_mul, abs_of_nonneg ha]
        · have hf : evalBlock (productTree μ f t) X i = false := by
            cases hc : evalBlock (productTree μ f t) X i
            · rfl
            · exact absurd (hev.mp hc) ha
          rw [hf, signBool_false, neg_one_mul, abs_of_neg (lt_of_not_ge ha)]
      have hsum1 : (1 : ℝ) = ∑ x : Fin n → Bool, (ν i x).toReal :=
        (Cslib.Probability.PMF.sum_toReal (ν i)).symm
      calc (∑ x : Fin n → Bool, (ν i x).toReal *
            if evalBlock (productTree μ f t) X i = f x then (1 : ℝ) else 0)
          = ∑ x : Fin n → Bool, (ν i x).toReal *
              ((1 + signBool (evalBlock (productTree μ f t) X i) * signBool (f x)) / 2) := by
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            rw [one_add_signBool_mul_div_two]
        _ = (∑ x : Fin n → Bool, (ν i x).toReal +
              signBool (evalBlock (productTree μ f t) X i) * a i) / 2 := by
            simp only [a, Finset.mul_sum]
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ = (1 + |a i|) / 2 := by rw [← hsum1, hsign]
    rw [hlhs, hrhs]
    have hstep1 : signBool (evalBlock t X) * ∏ i : Fin k, a i ≤ ∏ i : Fin k, |a i| := by
      have hle := le_abs_self (signBool (evalBlock t X) * ∏ i : Fin k, a i)
      rw [abs_mul, abs_signBool, one_mul, Finset.abs_prod] at hle
      exact hle
    have hstep2 : ∏ i : Fin k, |a i| ≤ ∏ i : Fin k, (1 + |a i|) / 2 := by
      refine Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
      have habs : |a i| ≤ 1 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        calc (∑ x : Fin n → Bool, |(ν i x).toReal * signBool (f x)|)
            = ∑ x : Fin n → Bool, (ν i x).toReal := by
              refine Finset.sum_congr rfl fun x _ ↦ ?_
              rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_signBool, mul_one]
          _ = 1 := Cslib.Probability.PMF.sum_toReal (ν i)
      linarith
    exact hstep1.trans hstep2

/-- For all `f`, `k`, `μ`, and `ε ≥ 0`,
$\overline{\mathrm{Depth}}^{\mu^k}(f^{\oplus k}, \varepsilon / 2) \ge
 \overline{\mathrm{Depth}}^{\mu^k}(f^{\otimes k}, \varepsilon)$. -/
theorem cor_xor_to_dp {n k : ℕ} (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {ε : ℝ} (hε : 0 ≤ ε) :
    prodDistDepth μ f k ε ≤ xorDistDepth μ f k (ε / 2) := by
  classical
  refine le_xorDistDepth μ f k (by linarith) fun T hT ↦ ?_
  let T' : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool) :=
    T.map (productTree μ f)
  have hdepth : randProdExpectedDepth μ T' = randProdExpectedDepth μ T := by
    rw [randProdExpectedDepth_eq_sum, randProdExpectedDepth_eq_sum]
    dsimp only [T']
    rw [StdSimplex.weights_map,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    dsimp only
    congr 1
    rw [detProdExpectedDepth_eq_sum, detProdExpectedDepth_eq_sum]
    refine Finset.sum_congr rfl fun X _ ↦ ?_
    rw [costBlock_eq_cost, cost_productTree, costBlock_eq_cost]
  have herr : randProdDistError μ f T' ≤ ε := by
    have hsucc : 1 - randProdDistError μ f T' ≥ 1 - 2 * randXorDistError μ f T := by
      have h1 : 1 - randProdDistError μ f T' =
          T.weights.sum fun t w ↦ w * ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            if evalBlock (productTree μ f t) X = directProduct f k X then 1 else 0 := by
        have hdet (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) :
            1 - detThresholdError μ f 0 t =
              ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
                if evalBlock t X = directProduct f k X then 1 else 0 := by
          rw [detThresholdError_eq_sum]
          have hsum1 : (1 : ℝ) = ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal :=
            (Cslib.Probability.PMF.sum_toReal (prodPMF μ k)).symm
          conv_lhs => arg 1; rw [hsum1]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun X _ ↦ ?_
          by_cases heq : evalBlock t X = directProduct f k X
          · have hhd : hammingDist (evalBlock t X) (directProduct f k X) = 0 :=
              hammingDist_eq_zero_iff.mpr heq
            rw [hhd]
            simp only [heq, Nat.cast_zero, lt_self_iff_false, ite_false, ite_true, mul_zero,
              mul_one, sub_zero]
          · have hhd : 0 < hammingDist (evalBlock t X) (directProduct f k X) :=
              Nat.pos_of_ne_zero (mt hammingDist_eq_zero_iff.mp heq)
            have hgt : (0 : ℝ) < (hammingDist (evalBlock t X) (directProduct f k X) : ℝ) := by
              exact_mod_cast hhd
            simp only [heq, hgt, ite_true, ite_false, mul_one, mul_zero, sub_self]
        calc 1 - randProdDistError μ f T'
            = (T'.weights.sum fun _ w ↦ w * (1 : ℝ)) -
                T'.weights.sum fun t w ↦ w * detThresholdError μ f 0 t := by
              rw [randProdDistError_eq_randThresholdError, randThresholdError_eq_sum]
              simp [T'.total]
          _ = T'.weights.sum fun t w ↦ w * (1 - detThresholdError μ f 0 t) := by
              simp only [Finsupp.sum, ← Finset.sum_sub_distrib, ← mul_sub]
          _ = T.weights.sum fun t w ↦ w * (1 - detThresholdError μ f 0 (productTree μ f t)) := by
              dsimp only [T']
              rw [StdSimplex.weights_map,
                Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
          _ = _ := by simp_rw [hdet]
      have h2 : 1 - 2 * randXorDistError μ f T =
          T.weights.sum fun t w ↦ w * ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            (signBool (evalBlock t X) * signBool (directSum f k X)) := by
        have hdet (t : DecisionTree (Fin k × Fin n) Bool) :
            1 - 2 * ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
              (if evalBlock t X = directSum f k X then 0 else 1) =
            ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
              (signBool (evalBlock t X) * signBool (directSum f k X)) := by
          have hsum1 : (1 : ℝ) = ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal :=
            (Cslib.Probability.PMF.sum_toReal (prodPMF μ k)).symm
          conv_lhs => arg 1; rw [hsum1]
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun X _ ↦ ?_
          rw [signBool_mul_eq_ite]
          split_ifs <;> ring
        calc 1 - 2 * randXorDistError μ f T
            = (T.weights.sum fun _ w ↦ w * (1 : ℝ)) -
                2 * T.weights.sum fun t w ↦ w * ∑ X : Fin k → Fin n → Bool,
                  (prodPMF μ k X).toReal * (if evalBlock t X = directSum f k X then 0 else 1) := by
              rw [randXorDistError_eq_sum]
              simp [T.total]
          _ = T.weights.sum fun t w ↦ w * (1 - 2 * ∑ X : Fin k → Fin n → Bool,
                (prodPMF μ k X).toReal * (if evalBlock t X = directSum f k X then 0 else 1)) := by
              simp only [Finsupp.sum]
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun _ _ ↦ by ring
          _ = _ := by simp_rw [hdet]
      rw [h1, h2]
      exact Finset.sum_le_sum fun t _ ↦
        mul_le_mul_of_nonneg_left (lem_dpt_to_ds μ f t) (T.weights_nonneg t)
    linarith
  rw [← hdepth]
  exact prodDistDepth_le μ f k herr

/-- any direct sum lower bound implies the corresponding
XOR lemma with half the error parameter. -/
theorem claim_equivalence_direct_sum_xor {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {M ε δ : ℝ} (hε : 0 ≤ ε)
    (hDP : M * distDepth μ f δ ≤ prodDistDepth μ f k ε) :
    M * distDepth μ f δ ≤ xorDistDepth μ f k (ε / 2) :=
  hDP.trans (cor_xor_to_dp μ f hε)

/-- Every randomized tree `T` for $f^{\oplus k}$ with error at most
$\frac{1}{2}(1 - e^{-\delta k / 20} - \gamma)$ has expected depth at least
$\frac{\gamma^2 k}{4000 \log(1/\delta)} \cdot \overline{\mathrm{Depth}}^\mu(f, \delta)$. -/
theorem thm_strong_xor_forall {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ)
    (T : RandomizedDecisionTree (Fin k × Fin n) Bool)
    (hT : randXorDistError μ f T ≤ (1 - Real.exp (-(δ * k / 20)) - γ) / 2) :
    γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      randProdExpectedDepth μ T := by
  by_cases hε : 0 ≤ 1 - Real.exp (-(δ * k / 20)) - γ
  · have h1 := claim_equivalence_direct_sum_xor μ f hε
      (thm_strong_direct_sum μ f hγ0 hγ1 hδ0 hε)
    exact h1.trans (xorDistDepth_le μ f k hT)
  · exfalso
    have hnn : 0 ≤ randXorDistError μ f T := by
      rw [randXorDistError_eq_sum]
      exact Finset.sum_nonneg fun t _ ↦ mul_nonneg (T.weights_nonneg t)
        (Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
    linarith

/-- For every `f`, `μ`, `k`, and `γ, δ ∈ (0, 1)` with `0 ≤ 1 - exp(-(δ k / 20)) - γ`,
$\overline{\mathrm{Depth}}^{\mu^k}(f^{\oplus k}, \frac{1}{2}(1 - e^{-\delta k / 20} - \gamma)) \ge
 \frac{\gamma^2 k}{4000 \log(1/\delta)} \cdot \overline{\mathrm{Depth}}^\mu(f, \delta)$. -/
theorem thm_strong_xor {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {γ δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ)
    (hε : 0 ≤ 1 - Real.exp (-(δ * k / 20)) - γ) :
    γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth μ f δ ≤
      xorDistDepth μ f k ((1 - Real.exp (-(δ * k / 20)) - γ) / 2) :=
  claim_equivalence_direct_sum_xor μ f hε (thm_strong_direct_sum μ f hγ0 hγ1 hδ0 hε)

/-! ### this module: Tightness — linear dependence on `γ` via Parity -/

private theorem length_path_eq_cost {ι β : Type*} (t : DecisionTree ι β) (x : ι → Bool) :
    (t.path x).length = t.cost x := by
  induction t with
  | leaf _ => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [DecisionTree.path, List.length_cons, DecisionTree.cost_node]
    cases x i <;> simp [ih₀, ih₁]

private theorem path_eq_of_forall_mem_queries {ι β : Type*} [DecidableEq ι]
    (t : DecisionTree ι β) {x y : ι → Bool} (h : ∀ i ∈ t.queries x, y i = x i) :
    t.path y = t.path x := by
  induction t with
  | leaf _ => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [DecisionTree.queries_node, Finset.mem_insert, forall_eq_or_imp] at h
    obtain ⟨hi, h⟩ := h
    simp only [DecisionTree.path, hi]
    cases hx : x i
    · rw [hx] at h; simp [ih₀ h]
    · rw [hx] at h; simp [ih₁ h]

/-- For any deterministic tree `t : DecisionTree (Fin n) Bool` and reachable leaf `ℓ` of length `<
n`,
the conditional error probability on `parity n` under the uniform distribution is `1 / 2`. -/
theorem prop_par_query_all {n : ℕ} (t : DecisionTree (Fin n) Bool) (ℓ : List Bool)
    (hreach : ∃ x : Fin n → Bool, t.path x = ℓ) (hlen : ℓ.length < n) :
    let unif := Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)
    let cond := Cslib.Probability.PMF.conditionalSnd (unif.map fun x ↦ (t.path x, x)) ℓ
    (∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 0 else 1) = 1 / 2 := by
  classical
  intro unif cond
  obtain ⟨x₀, hx₀⟩ := hreach
  have hcard_lt : (t.queries x₀).card < n := by
    calc (t.queries x₀).card ≤ t.cost x₀ := t.card_queries_le_cost x₀
      _ = (t.path x₀).length := (length_path_eq_cost t x₀).symm
      _ = ℓ.length := by rw [hx₀]
      _ < n := hlen
  have hex_i : ∃ i : Fin n, i ∉ t.queries x₀ := by
    by_contra! hall
    have hsub : Finset.univ ⊆ t.queries x₀ := fun i _ ↦ hall i
    have := Finset.card_le_card hsub
    simp at this
    omega
  obtain ⟨i₀, hi₀⟩ := hex_i
  let flip : (Fin n → Bool) → (Fin n → Bool) := fun x ↦ Function.update x i₀ (!x i₀)
  have hflip_inv : Function.Involutive flip := by
    intro x
    ext j
    by_cases hj : j = i₀
    · subst hj; simp [flip]
    · simp [flip, hj]
  have hflip_path : ∀ x, t.path x = ℓ → t.path (flip x) = ℓ := by
    intro x hx
    have hq : t.queries x = t.queries x₀ := by
      -- Since `t.path x = t.path x₀`, `x` and `x₀` follow the same queries!
      have hsame : ∀ (u : DecisionTree (Fin n) Bool) (a b : Fin n → Bool),
          u.path a = u.path b → u.queries a = u.queries b := by
        intro u
        induction u with
        | leaf _ => intro _ _ _; rfl
        | node j u₀ u₁ ih₀ ih₁ =>
          intro a b hp
          simp only [DecisionTree.path, List.cons.injEq] at hp
          have ha : a j = b j := hp.1
          simp only [DecisionTree.queries_node, ha]
          cases hb : b j
          · rw [hb] at ha
            simp only [ha, hb, Bool.cond_false] at hp
            simp [ih₀ a b hp.2]
          · rw [hb] at ha
            simp only [ha, hb, Bool.cond_true] at hp
            simp [ih₁ a b hp.2]
      exact hsame t x x₀ (hx.trans hx₀.symm)
    have hi_x : i₀ ∉ t.queries x := hq ▸ hi₀
    have hagree : ∀ j ∈ t.queries x, flip x j = x j := by
      intro j hj
      have hne : j ≠ i₀ := fun heq ↦ hi_x (heq ▸ hj)
      simp [flip, hne]
    exact (path_eq_of_forall_mem_queries t hagree).trans hx
  have hcond_flip : ∀ x, cond (flip x) = cond x := by
    intro x
    have hmapfst : ((unif.map fun y ↦ (t.path y, y)).map Prod.fst) = unif.map t.path := by
      rw [PMF.map_comp]; rfl
    have hsupp : ℓ ∈ ((unif.map fun y ↦ (t.path y, y)).map Prod.fst).support := by
      rw [hmapfst]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x₀, by simp [unif], hx₀⟩
    rw [Cslib.Probability.PMF.conditionalSnd_apply _ ℓ hsupp (flip x),
      Cslib.Probability.PMF.conditionalSnd_apply _ ℓ hsupp x]
    congr 1
    have hjoint : ∀ y, (unif.map fun z ↦ (t.path z, z)) (ℓ, y) =
        if t.path y = ℓ then unif y else 0 := by
      intro y
      rw [PMF.map_apply, tsum_eq_single y]
      · simp [eq_comm]
      · intro z hz; simp [hz.symm]
    rw [hjoint, hjoint]
    have hunif_eq : unif (flip x) = unif x := by simp [unif]
    rw [hunif_eq]
    by_cases hx : t.path x = ℓ
    · simp [hx, hflip_path x hx]
    · have hfx : t.path (flip x) ≠ ℓ := fun h ↦ hx (by simpa [hflip_inv x] using hflip_path _ h)
      simp [hx, hfx]
  have hsum_eq :
      (∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 0 else 1) =
      ∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 1 else 0 := by
    calc (∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 0 else 1)
        = ∑ x : Fin n → Bool, (cond (flip x)).toReal *
            if t.eval (flip x) = parity n (flip x) then 0 else 1 :=
          (Equiv.sum_comp hflip_inv.toPerm _).symm
      _ = ∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 1 else 0 := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [hcond_flip x]
          by_cases hx : x ∈ cond.support
          · have hmapfst : ((unif.map fun y ↦ (t.path y, y)).map Prod.fst) = unif.map t.path := by
              rw [PMF.map_comp]; rfl
            have hsupp : ℓ ∈ ((unif.map fun y ↦ (t.path y, y)).map Prod.fst).support := by
              rw [hmapfst]
              exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x₀, by simp [unif], hx₀⟩
            have hj := (Cslib.Probability.PMF.mem_support_conditionalSnd_iff _ ℓ hsupp x).mp hx
            obtain ⟨z, _, hz⟩ := (PMF.mem_support_map_iff _ _ _).mp hj
            have hpath : t.path x = ℓ := by
              obtain ⟨h1, h2⟩ := Prod.mk.inj hz
              rwa [h2] at h1
            have hev : t.eval (flip x) = t.eval x :=
              DecisionTree.eval_eq_of_path_eq t ((hflip_path x hpath).trans hpath.symm)
            rw [hev, parity_update_not]
            cases t.eval x <;> cases parity n x <;> simp
          · have h0 : cond x = 0 := (PMF.apply_eq_zero_iff _ _).mpr hx
            simp [h0]
  have hsum1 :
      (∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 0 else 1) +
      (∑ x : Fin n → Bool, (cond x).toReal * if t.eval x = parity n x then 1 else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc (∑ x : Fin n → Bool, (((cond x).toReal * if t.eval x = parity n x then 0 else 1) +
          ((cond x).toReal * if t.eval x = parity n x then 1 else 0)))
        = ∑ x : Fin n → Bool, (cond x).toReal := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          split_ifs <;> ring
      _ = 1 := Cslib.Probability.PMF.sum_toReal cond
  linarith

/-- Part (1) of the corresponding result:
$\overline{\mathrm{Depth}}^\mu(\mathsf{Par}, 1/4) = n / 2$ under the uniform distribution $\mu$. -/
theorem distDepth_parity_quarter (n : ℕ) :
    distDepth (Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)) (parity n) (1 / 4) =
      (n : ℝ) / 2 := by
  classical
  let unif := Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hpar0 : parity 0 = fun _ ↦ true := by
      funext x
      exact parity_zero x
    rw [hpar0, distDepth_const unif true (by norm_num)]
    norm_num
  refine le_antisymm ?_ ?_
  · obtain ⟨tAll, htAll, hdepth⟩ := DecisionTree.exists_computes (parity n)
    have hcost_all : detExpectedDepth unif tAll ≤ n := by
      rw [detExpectedDepth_eq_sum]
      refine (Cslib.Probability.PMF.sum_mul_le unif _ n fun x ↦ ?_).trans_eq rfl
      have hc : tAll.cost x ≤ n := by
        simpa using (tAll.cost_le_depth x).trans hdepth
      exact_mod_cast hc
    let T : RandomizedDecisionTree (Fin n) Bool :=
      StdSimplex.duple tAll (.leaf false) (s := 1 / 2) (t := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
    have herr : randDistError unif (parity n) T ≤ 1 / 4 := by
      rw [randDistError_eq_sum, StdSimplex.weights_duple,
        Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
        Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
      have h0 : detDistError unif (parity n) tAll = 0 :=
        detDistError_eq_zero_of_computes unif htAll
      have hleaf : detDistError unif (parity n) (.leaf false) ≤ 1 / 2 := by
        rw [detDistError_eq_sum]
        have h1 := prop_par_query_all (.leaf false : DecisionTree (Fin n) Bool) []
          ⟨fun _ ↦ false, rfl⟩ (by simpa using hn)
        have hcond : Cslib.Probability.PMF.conditionalSnd
            (unif.map fun x ↦ ((DecisionTree.leaf false : DecisionTree (Fin n) Bool).path x, x))
            [] = unif := by
          ext x
          have hmapfst : ((unif.map fun y ↦
              ((DecisionTree.leaf false : DecisionTree (Fin n) Bool).path y, y)).map Prod.fst) =
              PMF.pure [] := by
            ext ℓ; simp [PMF.map_comp, DecisionTree.path]
          rw [Cslib.Probability.PMF.conditionalSnd_apply _ [] (by rw [hmapfst]; simp) x,
            hmapfst, PMF.pure_apply_self, div_one, PMF.map_apply, tsum_eq_single x]
          · simp [DecisionTree.path]
          · intro z hz; simp [hz.symm]
        dsimp only at h1
        rw [hcond] at h1
        exact le_of_eq (by simpa using h1)
      linarith
    have hd : randExpectedDepthTree unif T ≤ (n : ℝ) / 2 := by
      rw [randExpectedDepthTree_eq_sum, StdSimplex.weights_duple,
        Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
        Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
      rw [detExpectedDepth_leaf]
      linarith
    exact (distDepth_le unif (parity n) herr).trans hd
  · refine le_distDepth unif (parity n) (by norm_num) fun T hT ↦ ?_
    have hdet_lb : ∀ t : DecisionTree (Fin n) Bool,
        (n : ℝ) * (1 - 2 * detDistError unif (parity n) t) ≤ detExpectedDepth unif t := by
      intro t
      have herr_ge : (1 / 2 : ℝ) * (∑ x : Fin n → Bool, (unif x).toReal *
          if t.cost x < n then 1 else 0) ≤ detDistError unif (parity n) t := by
        rw [detDistError_eq_sum,
          ← sum_conditionalSnd_map_fintype unif t.path
            (fun _ y ↦ if t.eval y = parity n y then 0 else 1)]
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun x _ ↦ ?_
        rw [← mul_assoc, mul_comm (1 / 2 : ℝ), mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        by_cases hlt : t.cost x < n
        · simp only [hlt, ite_true, mul_one]
          have hlen : (t.path x).length < n := by rwa [length_path_eq_cost]
          exact le_of_eq (prop_par_query_all t (t.path x) ⟨x, rfl⟩ hlen).symm
        · simp only [hlt, ite_false, mul_zero]
          exact Finset.sum_nonneg fun _ _ ↦
            mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
      have hcost_ge : (n : ℝ) * (1 - ∑ x : Fin n → Bool, (unif x).toReal *
          if t.cost x < n then 1 else 0) ≤ detExpectedDepth unif t := by
        rw [detExpectedDepth_eq_sum]
        have hsum1 : (1 : ℝ) = ∑ x : Fin n → Bool, (unif x).toReal :=
          (Cslib.Probability.PMF.sum_toReal unif).symm
        conv_lhs => arg 2; arg 1; rw [hsum1]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_le_sum fun x _ ↦ ?_
        by_cases hlt : t.cost x < n
        · simp only [hlt, ite_true, mul_one, sub_self, mul_zero]; positivity
        · push Not at hlt
          simp only [not_lt.mpr hlt, ite_false, mul_zero, sub_zero]
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hlt) ENNReal.toReal_nonneg
      nlinarith
    calc (n : ℝ) / 2
        ≤ (n : ℝ) * (1 - 2 * randDistError unif (parity n) T) := by nlinarith
      _ = T.weights.sum fun t w ↦ w * ((n : ℝ) * (1 - 2 * detDistError unif (parity n) t)) := by
          simp only [randDistError_eq_sum, Finsupp.sum]
          have h1 : (T.weights.sum fun _ w ↦ w * (1 : ℝ)) = 1 := by simp [T.total]
          simp only [Finsupp.sum] at h1
          calc (n : ℝ) * (1 -
            2 * ∑ t ∈ T.weights.support, T.weights t * detDistError unif (parity n) t)
              = (n : ℝ) * ((∑ t ∈ T.weights.support, T.weights t * (1 : ℝ)) -
                  ∑ t ∈ T.weights.support, T.weights t * (2 * detDistError unif (parity n) t)) := by
                rw [h1, Finset.mul_sum]
                congr 1; congr 1; exact Finset.sum_congr rfl fun _ _ ↦ by ring
            _ = (n : ℝ) * ∑ t ∈ T.weights.support, T.weights t * (1 -
              2 * detDistError unif (parity n) t) := by
                rw [← Finset.sum_sub_distrib]
                congr 1; exact Finset.sum_congr rfl fun _ _ ↦ by ring
            _ = ∑ t ∈ T.weights.support, T.weights t * ((n : ℝ) * (1 -
              2 * detDistError unif (parity n) t)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ randExpectedDepthTree unif T := by
          rw [randExpectedDepthTree_eq_sum]
          exact Finset.sum_le_sum fun t _ ↦
            mul_le_mul_of_nonneg_left (hdet_lb t) (T.weights_nonneg t)

/-- Under the uniform distribution $\mu$ on $\{0,1\}^n$, for all $\gamma \in [0, 1]$,
$\overline{\mathrm{Depth}}^{\mu^k}(\mathsf{Par}^{\otimes k}, 1 - \gamma) \le
 2 \gamma k \cdot \overline{\mathrm{Depth}}^\mu(\mathsf{Par}, 1/4)$. -/
theorem claim_linear_dependence_on_gamma (n k : ℕ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    let unif := Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)
    prodDistDepth unif (parity n) k (1 - γ) ≤
      2 * γ * (k : ℝ) * distDepth unif (parity n) (1 / 4) := by
  intro unif
  rw [distDepth_parity_quarter n]
  obtain ⟨tAll, htAll, hdepth⟩ := DecisionTree.exists_computes (directProductUncurry (parity n) k)
  let T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool) :=
    StdSimplex.duple tAll (.leaf fun _ ↦ false) (s := γ) (t := 1 - γ)
      hγ0 (sub_nonneg.mpr hγ1) (by ring)
  have herr : randProdDistError unif (parity n) T ≤ 1 - γ := by
    rw [randProdDistError_eq_randThresholdError, randThresholdError_eq_sum,
      StdSimplex.weights_duple,
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
    have h0 : detThresholdError unif (parity n) 0 tAll = 0 := by
      rw [detThresholdError_eq_sum]
      refine Finset.sum_eq_zero fun X _ ↦ ?_
      have hev : evalBlock tAll X = directProduct (parity n) k X := htAll (Function.uncurry X)
      simp [hammingDist_eq_zero_iff.mpr hev]
    have h1 : detThresholdError (k := k) unif (parity n) 0 (.leaf fun _ ↦ false) ≤ 1 := by
      rw [detThresholdError_eq_sum]
      exact Cslib.Probability.PMF.sum_mul_le (prodPMF unif k) _ 1 fun _ ↦ by
        split_ifs <;> norm_num
    rw [h0]
    nlinarith
  have hd : randProdExpectedDepth unif T ≤ γ * (k : ℝ) * (n : ℝ) := by
    rw [randProdExpectedDepth_eq_sum, StdSimplex.weights_duple,
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
    have hall : detProdExpectedDepth unif tAll ≤ (k : ℝ) * (n : ℝ) := by
      rw [detProdExpectedDepth_eq_sum]
      refine (Cslib.Probability.PMF.sum_mul_le (prodPMF unif k) _ ((k : ℝ) * (n : ℝ)) fun X ↦ ?_)
      have hc : costBlock tAll X ≤ k * n := by
        rw [costBlock_eq_cost]
        simpa [Fintype.card_prod] using (tAll.cost_le_depth (Function.uncurry X)).trans hdepth
      exact_mod_cast hc
    rw [detProdExpectedDepth_leaf]
    nlinarith
  calc prodDistDepth unif (parity n) k (1 - γ)
      ≤ randProdExpectedDepth unif T := prodDistDepth_le unif (parity n) k herr
    _ ≤ γ * (k : ℝ) * (n : ℝ) := hd
    _ = 2 * γ * (k : ℝ) * ((n : ℝ) / 2) := by ring

/-- **Counterexample for the corresponding result as `ε → 1⁻`**:
For any fixed positive constants `c, C` and polylog exponent `a ≥ 0`, the unguarded
`ε < 1` inequality of the corresponding result with error `Θ(ε / k)` fails as `ε → 1⁻` on `parity
1`. -/
theorem main_intro_counterexample_near_one {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ (n k : ℕ) (f : (Fin n → Bool) → Bool) (μ : PMF (Fin n → Bool)) (ε : ℝ),
      1 ≤ k ∧ 0 < ε ∧ ε < 1 ∧ 0 < C * ε / k ∧ C * ε / k ≤ 1 / 4 ∧
        prodDistDepth μ f k ε <
          c * (ε ^ 2 * k / (Real.log (k / (C * ε)) + 1)) * distDepth μ f (C * ε / k) := by
  let k : ℕ := max 1 (Nat.ceil (4 * C))
  have hk1 : 1 ≤ k := le_max_left 1 _
  have hkC : 4 * C ≤ (k : ℝ) := (Nat.le_ceil (4 * C)).trans (by exact_mod_cast le_max_right 1 _)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
  let unif := Cslib.Probability.PMF.uniformOfFintype (Fin 1 → Bool)
  have hlog_pos : 0 < Real.log ((k : ℝ) / (C * (1 / 2))) + 1 := by
    have hge1 : (1 : ℝ) ≤ (k : ℝ) / (C * (1 / 2)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [Real.log_nonneg hge1]
  let rhsMin : ℝ :=
    c * ((1 / 2 : ℝ) ^ 2 * (k : ℝ) / (Real.log ((k : ℝ) / (C * (1 / 2))) + 1)) * (1 / 2)
  have hrhsMin : 0 < rhsMin := by positivity
  let η : ℝ := min (1 / 4) (rhsMin / (2 * (k : ℝ)))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 4 := min_le_left _ _
  let ε : ℝ := 1 - η
  have hε_half : (1 / 2 : ℝ) ≤ ε := by dsimp [ε]; linarith
  have hε0 : 0 < ε := by linarith
  have hε1 : ε < 1 := by dsimp [ε]; linarith
  refine ⟨1, k, parity 1, unif, ε, hk1, hε0, hε1, by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hkR]
    nlinarith
  · have hlin := claim_linear_dependence_on_gamma 1 k hη0.le (by linarith)
    dsimp only at hlin
    rw [distDepth_parity_quarter 1] at hlin
    have hlhs : prodDistDepth unif (parity 1) k ε ≤ η * (k : ℝ) := by
      dsimp [ε]
      linarith
    have hdepth_ge : (1 / 2 : ℝ) ≤ distDepth unif (parity 1) (C * ε / k) := by
      have hle : C * ε / k ≤ 1 / 4 := by rw [div_le_iff₀ hkR]; nlinarith
      have hanti := distDepth_antitone unif (parity 1) (show 0 ≤ C * ε / k by positivity) hle
      rw [distDepth_parity_quarter 1] at hanti
      simpa using hanti
    have hlog_le : Real.log ((k : ℝ) / (C * ε)) + 1 ≤ Real.log ((k : ℝ) / (C * (1 / 2))) + 1 := by
      have hdiv : (k : ℝ) / (C * ε) ≤ (k : ℝ) / (C * (1 / 2)) :=
        div_le_div_of_nonneg_left hkR.le (by positivity) (by nlinarith)
      linarith [Real.log_le_log (by positivity) hdiv]
    have hlog_pos_ε : 0 < Real.log ((k : ℝ) / (C * ε)) + 1 := by
      have hge1 : (1 : ℝ) ≤ (k : ℝ) / (C * ε) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith [Real.log_nonneg hge1]
    have hrhs : rhsMin ≤
        c * (ε ^ 2 * k / (Real.log (k / (C * ε)) + 1)) * distDepth unif (parity 1) (C * ε / k) := by
      have hsq : (1 / 2 : ℝ) ^ 2 * (k : ℝ) ≤ ε ^ 2 * (k : ℝ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hkR.le
      have h1 : (1 / 2 : ℝ) ^ 2 * (k : ℝ) / (Real.log ((k : ℝ) / (C * (1 / 2))) + 1) ≤
          ε ^ 2 * (k : ℝ) / (Real.log ((k : ℝ) / (C * ε)) + 1) :=
        div_le_div₀ (by positivity) hsq hlog_pos_ε hlog_le
      have h2 : c * ((1 / 2 : ℝ) ^ 2 * (k : ℝ) / (Real.log ((k : ℝ) / (C * (1 / 2))) + 1)) ≤
          c * (ε ^ 2 * (k : ℝ) / (Real.log ((k : ℝ) / (C * ε)) + 1)) :=
        mul_le_mul_of_nonneg_left h1 hc.le
      have h3 : 0 ≤ c * ((1 / 2 : ℝ) ^ 2 * (k : ℝ) / (Real.log ((k : ℝ) / (C * (1 / 2))) + 1)) := by
        positivity
      dsimp only [rhsMin]
      nlinarith
    have hηk : η * (k : ℝ) ≤ rhsMin / 2 := by
      have := min_le_right (1 / 4 : ℝ) (rhsMin / (2 * (k : ℝ)))
      have hmul := mul_le_mul_of_nonneg_right this hkR.le
      have hsimp : rhsMin / (2 * (k : ℝ)) * (k : ℝ) = rhsMin / 2 := by field_simp
      linarith
    linarith

/-! ### the appendix: Failure of error reduction for distributional query complexity -/

private def fixFirstTrue {n : ℕ} (hn : 2 ≤ n) :
    DecisionTree (Fin n) Bool → DecisionTree (Fin (n - 1)) Bool
  | .leaf b => .leaf b
  | .node j t₀ t₁ =>
    if hj : j.1 = 0 then fixFirstTrue hn t₁
    else .node ⟨j.1 - 1, by omega⟩ (fixFirstTrue hn t₀) (fixFirstTrue hn t₁)

private theorem eval_fixFirstTrue {n : ℕ} (hn : 2 ≤ n) (t : DecisionTree (Fin n) Bool)
    (y : Fin (n - 1) → Bool) :
    (fixFirstTrue hn t).eval y =
      t.eval (fun k ↦ if _ : k.1 = 0 then true else y ⟨k.1 - 1, by omega⟩) := by
  induction t with
  | leaf b => rfl
  | node j t₀ t₁ ih₀ ih₁ =>
    simp only [fixFirstTrue]
    by_cases hj : j.1 = 0
    · simp only [hj, dite_true, DecisionTree.eval_node]
      exact ih₁
    · simp only [hj, dite_false, DecisionTree.eval_node]
      cases y ⟨j.1 - 1, by omega⟩
      · exact ih₀
      · exact ih₁

private theorem cost_fixFirstTrue_le {n : ℕ} (hn : 2 ≤ n) (t : DecisionTree (Fin n) Bool)
    (y : Fin (n - 1) → Bool) :
    (fixFirstTrue hn t).cost y ≤
      t.cost (fun k ↦ if _ : k.1 = 0 then true else y ⟨k.1 - 1, by omega⟩) := by
  induction t with
  | leaf b => exact le_rfl
  | node j t₀ t₁ ih₀ ih₁ =>
    simp only [fixFirstTrue]
    by_cases hj : j.1 = 0
    · simp only [hj, dite_true, DecisionTree.cost_node]
      exact ih₁.trans (Nat.le_succ _)
    · simp only [hj, dite_false, DecisionTree.cost_node]
      cases y ⟨j.1 - 1, by omega⟩
      · exact Nat.add_le_add_right ih₀ 1
      · exact Nat.add_le_add_right ih₁ 1

private def splitFinBool {n : ℕ} (hn : 2 ≤ n) :
    (Fin n → Bool) ≃ Bool × (Fin (n - 1) → Bool) :=
  { toFun := fun x ↦ (x ⟨0, by omega⟩, fun j ↦ x ⟨j.1 + 1, by omega⟩)
    invFun := fun p k ↦ if h : k.1 = 0 then p.1 else p.2 ⟨k.1 - 1, by omega⟩
    left_inv := fun x ↦ by
      ext k
      by_cases hk : k.1 = 0
      · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk
        simp [hk0]
      · simp only [hk, dite_false]
        congr 1
        ext
        dsimp only
        omega
    right_inv := fun ⟨b, y⟩ ↦ by
      ext
      · simp
      · simp }

/-- for every `n : ℕ`, under the uniform distribution $\mu$ on $\{0,1\}^n$,
there exists a Boolean function $f$ with $\overline{\mathrm{Depth}}^\mu(f, 1/4) = 0$ and
$\overline{\mathrm{Depth}}^\mu(f, 1/8) \ge (n - 1) / 4$. -/
theorem claim_no_boosting (n : ℕ) :
    let unif := Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)
    ∃ f : (Fin n → Bool) → Bool,
      distDepth unif f (1 / 4) = 0 ∧ ((n : ℝ) - 1) / 4 ≤ distDepth unif f (1 / 8) := by
  classical
  intro unif
  rcases lt_or_ge n 2 with hn | hn
  · refine ⟨fun _ ↦ false, distDepth_const unif false (by norm_num), ?_⟩
    have hnn := distDepth_nonneg unif (fun _ ↦ false) (1 / 8)
    have hle : ((n : ℝ) - 1) / 4 ≤ 0 := by
      have : (n : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ hn
      linarith
    exact hle.trans hnn
  · have hn1 : 1 ≤ n := by omega
    let i₀ : Fin n := ⟨0, by omega⟩
    let f : (Fin n → Bool) → Bool := fun x ↦
      if x i₀ = false then false
      else parity (n - 1) (fun j ↦ x ⟨j.1 + 1, by omega⟩)
    let e := splitFinBool hn
    have hcard_eq : (Fintype.card (Fin n → Bool) : ℝ) =
        2 * (Fintype.card (Fin (n - 1) → Bool) : ℝ) := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have hnat : (2 : ℕ) ^ n = 2 * (2 : ℕ) ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn1]
      exact_mod_cast hnat
    refine ⟨f, ?_, ?_⟩
    · refine le_antisymm ?_ (distDepth_nonneg unif f (1 / 4))
      have hleaf : detDistError unif f (.leaf false) = 1 / 4 := by
        rw [detDistError_eq_sum]
        have hsum : (∑ x : Fin n → Bool, (unif x).toReal * if false = f x then 0 else 1) =
            (1 / 2 : ℝ) * ∑ y : Fin (n - 1) → Bool,
              ((Cslib.Probability.PMF.uniformOfFintype (Fin (n - 1) → Bool) y).toReal *
                if false = parity (n - 1) y then 0 else 1) := by
          rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Fintype.sum_bool]
          have hfalse : (∑ y : Fin (n - 1) → Bool,
              (unif (e.symm (false, y))).toReal * if false = f (e.symm (false, y)) then 0 else 1) =
                0 := by
            refine Finset.sum_eq_zero fun y _ ↦ ?_
            have h0 : e.symm (false, y) i₀ = false := by simp [e, splitFinBool, i₀]
            simp [f, h0]
          rw [hfalse, add_zero, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          have h1 : e.symm (true, y) i₀ = true := by simp [e, splitFinBool, i₀]
          have h2 : (fun j : Fin (n - 1) ↦ e.symm (true, y) ⟨j.1 + 1, by omega⟩) = y := by
            funext j; simp [e, splitFinBool]
          simp only [f, h1, Bool.true_eq_false, ite_false, h2, unif,
            Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
            ENNReal.toReal_natCast, hcard_eq]
          ring
        have hleaf_eq : (∑ x : Fin n → Bool,
            (unif x).toReal * if (DecisionTree.leaf false).eval x = f x then 0 else 1) =
            ∑ x : Fin n → Bool, (unif x).toReal * if false = f x then 0 else 1 :=
          Finset.sum_congr rfl fun _ _ ↦ rfl
        rw [hleaf_eq, hsum]
        have hpar := prop_par_query_all (.leaf false : DecisionTree (Fin (n - 1)) Bool) []
          ⟨fun _ ↦ false, rfl⟩ (by simp; omega)
        have hcond : Cslib.Probability.PMF.conditionalSnd
            ((Cslib.Probability.PMF.uniformOfFintype (Fin (n - 1) → Bool)).map fun y ↦
              ((DecisionTree.leaf false : DecisionTree (Fin (n - 1)) Bool).path y, y)) [] =
            Cslib.Probability.PMF.uniformOfFintype (Fin (n - 1) → Bool) := by
          ext y
          have hmapfst : (((Cslib.Probability.PMF.uniformOfFintype (Fin (n - 1) → Bool)).map
              fun z ↦ ((DecisionTree.leaf false : DecisionTree (Fin (n - 1)) Bool).path z, z)).map
                Prod.fst) = PMF.pure [] := by
            ext ℓ; simp [PMF.map_comp, DecisionTree.path]
          rw [Cslib.Probability.PMF.conditionalSnd_apply _ [] (by rw [hmapfst]; simp) y,
            hmapfst, PMF.pure_apply_self, div_one, PMF.map_apply, tsum_eq_single y]
          · simp [DecisionTree.path]
          · intro z hz; simp [hz.symm]
        dsimp only at hpar
        rw [hcond] at hpar
        have hpar' : (∑ y : Fin (n - 1) → Bool,
            (Cslib.Probability.PMF.uniformOfFintype (Fin (n - 1) → Bool) y).toReal *
              if false = parity (n - 1) y then 0 else 1) = 1 / 2 := by
          simpa using hpar
        rw [hpar']
        norm_num
      have h0 : randExpectedDepthTree unif (StdSimplex.single (.leaf false)) = 0 := by
        rw [randExpectedDepthTree_single, detExpectedDepth_leaf]
      exact (distDepth_le unif f (by rw [randDistError_single, hleaf])).trans_eq h0
    · refine le_distDepth unif f (by norm_num) fun T hT ↦ ?_
      have hdet_lb : ∀ t : DecisionTree (Fin n) Bool,
          ((n : ℝ) - 1) / 2 * (1 - 4 * detDistError unif f t) ≤ detExpectedDepth unif t := by
        intro t
        let unif' := Cslib.Probability.PMF.uniformOfFintype (Fin (n - 1) → Bool)
        have herr_half : (1 / 2 : ℝ) * detDistError unif' (parity (n - 1)) (fixFirstTrue hn t) ≤
            detDistError unif f t := by
          rw [detDistError_eq_sum, detDistError_eq_sum]
          rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Fintype.sum_bool]
          have hnn : 0 ≤ ∑ y : Fin (n - 1) → Bool,
              (unif (e.symm (false, y))).toReal *
                if t.eval (e.symm (false, y)) = f (e.symm (false, y)) then 0 else 1 :=
            Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
          have htrue_eq : (∑ y : Fin (n - 1) → Bool,
              (unif (e.symm (true, y))).toReal *
                if t.eval (e.symm (true, y)) = f (e.symm (true, y)) then 0 else 1) =
              (1 / 2 : ℝ) * ∑ y : Fin (n - 1) → Bool,
                (unif' y).toReal *
                  if (fixFirstTrue hn t).eval y = parity (n - 1) y then 0 else 1 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            have h1 : e.symm (true, y) i₀ = true := by simp [e, splitFinBool, i₀]
            have h2 : (fun j : Fin (n - 1) ↦ e.symm (true, y) ⟨j.1 + 1, by omega⟩) = y := by
              funext j; simp [e, splitFinBool]
            have hf_eq : f (e.symm (true, y)) = parity (n - 1) y := by
              simp [f, h1, h2]
            have hev : t.eval (e.symm (true, y)) = (fixFirstTrue hn t).eval y :=
              (eval_fixFirstTrue hn t y).symm
            simp only [hf_eq, hev, unif, unif', Cslib.Probability.PMF.uniformOfFintype_apply,
              ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard_eq]
            ring
          linarith
        have hcost_half : (1 / 2 : ℝ) * detExpectedDepth unif' (fixFirstTrue hn t) ≤
            detExpectedDepth unif t := by
          rw [detExpectedDepth_eq_sum, detExpectedDepth_eq_sum]
          rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Fintype.sum_bool]
          have hnn : 0 ≤ ∑ y : Fin (n - 1) → Bool,
              (unif (e.symm (false, y))).toReal * (t.cost (e.symm (false, y)) : ℝ) :=
            Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
          have htrue_ge : (1 / 2 : ℝ) * ∑ y : Fin (n - 1) → Bool,
              (unif' y).toReal * ((fixFirstTrue hn t).cost y : ℝ) ≤
              ∑ y : Fin (n - 1) → Bool,
                (unif (e.symm (true, y))).toReal * (t.cost (e.symm (true, y)) : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun y _ ↦ ?_
            have hle_c : ((fixFirstTrue hn t).cost y : ℝ) ≤ (t.cost (e.symm (true, y)) : ℝ) :=
              Nat.cast_le.mpr (cost_fixFirstTrue_le hn t y)
            have hw : (unif (e.symm (true, y))).toReal = (1 / 2 : ℝ) * (unif' y).toReal := by
              simp only [unif, unif', Cslib.Probability.PMF.uniformOfFintype_apply,
                ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard_eq]
              ring
            rw [hw]
            nlinarith [ENNReal.toReal_nonneg (a := unif' y)]
          linarith
        have hpar_lb : ((n - 1 : ℕ) : ℝ) * (1 - 2 * detDistError unif' (parity (n -
          1)) (fixFirstTrue hn t)) ≤
            detExpectedDepth unif' (fixFirstTrue hn t) := by
          have herr_ge : (1 / 2 : ℝ) * (∑ y : Fin (n - 1) → Bool, (unif' y).toReal *
              if (fixFirstTrue hn t).cost y < n - 1 then 1 else 0) ≤
              detDistError unif' (parity (n - 1)) (fixFirstTrue hn t) := by
            rw [detDistError_eq_sum,
              ← sum_conditionalSnd_map_fintype unif' (fixFirstTrue hn t).path
                (fun _ y ↦ if (fixFirstTrue hn t).eval y = parity (n - 1) y then 0 else 1)]
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun y _ ↦ ?_
            rw [← mul_assoc, mul_comm (1 / 2 : ℝ), mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            by_cases hlt : (fixFirstTrue hn t).cost y < n - 1
            · simp only [hlt, ite_true, mul_one]
              exact le_of_eq (prop_par_query_all (fixFirstTrue hn t) ((fixFirstTrue hn t).path y)
                ⟨y, rfl⟩ (by rwa [length_path_eq_cost])).symm
            · simp only [hlt, ite_false, mul_zero]
              exact Finset.sum_nonneg fun _ _ ↦
                mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
          have hcost_ge : ((n - 1 : ℕ) : ℝ) * (1 - ∑ y : Fin (n - 1) → Bool, (unif' y).toReal *
              if (fixFirstTrue hn t).cost y < n - 1 then 1 else 0) ≤
              detExpectedDepth unif' (fixFirstTrue hn t) := by
            rw [detExpectedDepth_eq_sum]
            have hsum1 : (1 : ℝ) = ∑ y : Fin (n - 1) → Bool, (unif' y).toReal :=
              (Cslib.Probability.PMF.sum_toReal unif').symm
            conv_lhs => arg 2; arg 1; rw [hsum1]
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            refine Finset.sum_le_sum fun y _ ↦ ?_
            by_cases hlt : (fixFirstTrue hn t).cost y < n - 1
            · simp only [hlt, ite_true, mul_one, sub_self, mul_zero]; positivity
            · push Not at hlt
              simp only [not_lt.mpr hlt, ite_false, mul_zero, sub_zero]
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hlt) ENNReal.toReal_nonneg
          nlinarith
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
        rw [hcast] at hpar_lb
        nlinarith
      have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      calc ((n : ℝ) - 1) / 4
          ≤ ((n : ℝ) - 1) / 2 * (1 - 4 * randDistError unif f T) := by nlinarith
        _ = T.weights.sum fun t w ↦
              w * (((n : ℝ) - 1) / 2 * (1 - 4 * detDistError unif f t)) := by
            simp only [randDistError_eq_sum, Finsupp.sum]
            have h1 : (T.weights.sum fun _ w ↦ w * (1 : ℝ)) = 1 := by simp [T.total]
            simp only [Finsupp.sum] at h1
            calc ((n : ℝ) - 1) / 2 * (1 -
              4 * ∑ t ∈ T.weights.support, T.weights t * detDistError unif f t)
                = ((n : ℝ) - 1) / 2 * ((∑ t ∈ T.weights.support, T.weights t * (1 : ℝ)) -
                    ∑ t ∈ T.weights.support, T.weights t * (4 * detDistError unif f t)) := by
                  rw [h1, Finset.mul_sum]
                  congr 1; congr 1; exact Finset.sum_congr rfl fun _ _ ↦ by ring
              _ = ((n : ℝ) - 1) / 2 *
                    ∑ t ∈ T.weights.support, T.weights t * (1 - 4 * detDistError unif f t) := by
                  rw [← Finset.sum_sub_distrib]
                  congr 1; exact Finset.sum_congr rfl fun _ _ ↦ by ring
              _ = ∑ t ∈ T.weights.support,
                    T.weights t * (((n : ℝ) - 1) / 2 * (1 - 4 * detDistError unif f t)) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ ≤ randExpectedDepthTree unif T := by
            rw [randExpectedDepthTree_eq_sum]
            exact Finset.sum_le_sum fun t _ ↦
              mul_le_mul_of_nonneg_left (hdet_lb t) (T.weights_nonneg t)

/-! ### Non-degenerate joint-hypothesis non-vacuity witness -/

/-- Unconditional non-degenerate joint-hypothesis witness showing that all hypotheses of
`hardcoreTheorem`, `thm_bounds_from_hardcore`, `thm_threshold_direct_sum`,
`thm_strong_direct_sum`, `thm_main_intro`, and `thm_strong_xor` are jointly inhabited on
`n = 2`, `k = 200`, `f = parity 2`, `μ = Unif`, `γ = 1/4`, `δ = 1/4` with a strictly positive
distributional depth lower bound. -/
theorem nonvacuity_hardcore_and_direct_sum :
    let unif := Cslib.Probability.PMF.uniformOfFintype (Fin 2 → Bool)
    let γ : ℝ := 1 / 4
    let δ : ℝ := 1 / 4
    let k : ℕ := 200
    0 < γ ∧ γ < 1 ∧ 0 < δ ∧ δ < 1 ∧
      0 < distDepth unif (parity 2) δ ∧
      0 ≤ 1 - Real.exp (-(δ * k / 20)) - γ ∧
      0 < γ ^ 2 * k / (4000 * Real.log (1 / δ)) * distDepth unif (parity 2) δ ∧
      ∃ H : (Fin 2 → Bool) → ℝ,
        IsHardcoreMeasure unif (parity 2) γ
          (γ ^ 2 / (10 * Real.log (1 / δ)) * distDepth unif (parity 2) δ) (δ / 2) H := by
  intro unif γ δ k
  have hdepth : distDepth unif (parity 2) δ = 1 := by
    have := distDepth_parity_quarter 2
    norm_num at this
    exact this
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos (by dsimp [δ]; norm_num)
  have hε : 0 ≤ 1 - Real.exp (-(δ * k / 20)) - γ := by
    have hval : δ * (k : ℝ) / 20 = 5 / 2 := by dsimp [δ, k]; norm_num
    rw [hval]
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 / 2 by norm_num) 3
    have h3 : (∑ i ∈ Finset.range 3, (5 / 2 : ℝ) ^ i / (Nat.factorial i : ℝ)) = 53 / 8 := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    rw [h3] at hsum
    have hexp : Real.exp (-(5 / 2 : ℝ)) ≤ 8 / 53 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    dsimp [γ]
    linarith
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by rw [hdepth]; norm_num, hε, ?_, ?_⟩
  · rw [hdepth]
    dsimp [γ, k]
    positivity
  · exact hardcoreTheorem unif (parity 2) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hdepth]; norm_num)

end CslibFrontier.Computability.QueryComplexity.DirectSum

end
