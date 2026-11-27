/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalDepth

import CslibFrontier.Computability.DecisionTree.Composition
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Impagliazzo's Hardcore Theorem for query complexity and randomized error reduction

This module proves:

- every Boolean function `f` with `0 < distDepth μ f δ` and
 `γ, δ ∈ (0, 1)` admits a `(γ, d)`-hardcore measure of density `δ / 2` w.r.t. `μ`, where
 `d = (γ^2 / (10 * Real.log (1 / δ))) * distDepth μ f δ`.
- **Counterexample to the unguarded statement** (`hardcoreTheorem_counterexample`): when
 `distDepth μ f δ = 0` (for instance `f ≡ true`), no `(γ, 0)`-hardcore measure of density `δ / 2`
 exists for any `γ ∈ (0, 1)` and `δ > 0`.
- **Fact**: error reduction by
 majority repetition for expected-depth randomized query complexity
 $\overline{\mathrm{R}}(f, \delta) \le 10 \log(1/\delta) \cdot \overline{\mathrm{R}}(f, 1/4)$.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity.DirectSum

open Cslib Convexity Finset
open scoped BigOperators ENNReal NNReal

/-! ### Majority repetition of randomized decision trees -/

/-- Strict majority of a Boolean vector (`true` iff strictly more than half of the entries are
`true`). -/
@[expose] def majBool {r : ℕ} (v : Fin r → Bool) : Bool :=
  decide (r < 2 * trueCount v)

/-- Deterministic tree running `r` trees in sequence and taking the majority of their outputs. -/
def majTree {ι : Type*} {r : ℕ} (ts : Fin r → DecisionTree ι Bool) :
    DecisionTree ι Bool :=
  (DecisionTree.seqFin ts).map majBool

theorem cost_map {ι β γ : Type*} (g : β → γ) (t : DecisionTree ι β) (x : ι → Bool) :
    (t.map g).cost x = t.cost x := by
  induction t with
  | leaf _ => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [DecisionTree.map, DecisionTree.cost_node]
    cases x i <;> simp [ih₀, ih₁]

private theorem cost_seqFin {ι β : Type*} {r : ℕ} (ts : Fin r → DecisionTree ι β) (x : ι → Bool) :
    (DecisionTree.seqFin ts).cost x = ∑ j : Fin r, (ts j).cost x := by
  induction r with
  | zero => simp [DecisionTree.seqFin]
  | succ r ih =>
    simp only [DecisionTree.seqFin, DecisionTree.cost, DecisionTree.weightedCost_bind,
      DecisionTree.weightedCost_leaf, add_zero]
    rw [Fin.sum_univ_succ]
    exact congrArg ((ts 0).cost x + ·) (ih fun j ↦ ts j.succ)

theorem cost_majTree {ι : Type*} {r : ℕ} (ts : Fin r → DecisionTree ι Bool) (x : ι → Bool) :
    (majTree ts).cost x = ∑ j : Fin r, (ts j).cost x := by
  rw [majTree, cost_map, cost_seqFin]

theorem eval_majTree {ι : Type*} {r : ℕ} (ts : Fin r → DecisionTree ι Bool) (x : ι → Bool) :
    (majTree ts).eval x = majBool (fun j ↦ (ts j).eval x) := by
  simp [majTree]

/-- Extract a `PMF` over the finite support of a `StdSimplex`. -/
private noncomputable def supportPMF {α : Type*} (T : StdSimplex ℝ α) :
    PMF {a // a ∈ T.weights.support} :=
  PMF.ofFintype (fun s ↦ ENNReal.ofReal (T.weights s.1)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ ↦ T.weights_nonneg s.1)]
    have hsum : (∑ s : {a // a ∈ T.weights.support}, T.weights s.1) = 1 := by
      rw [Finset.sum_coe_sort T.weights.support (fun a ↦ T.weights a)]
      exact T.total
    rw [hsum, ENNReal.ofReal_one])

private theorem supportPMF_toReal {α : Type*} (T : StdSimplex ℝ α)
    (s : {a // a ∈ T.weights.support}) :
    (supportPMF T s).toReal = T.weights s.1 :=
  ENNReal.toReal_ofReal (T.weights_nonneg s.1)

/-- Sample `r` independent trees from `T` and output their majority. -/
noncomputable def majRandTree {ι : Type*} (T : RandomizedDecisionTree ι Bool) (r : ℕ) :
    RandomizedDecisionTree ι Bool :=
  let q : PMF (Fin r → {t // t ∈ T.weights.support}) :=
    Cslib.Probability.PMF.pi (fun _ : Fin r ↦ supportPMF T)
  (Cslib.Probability.PMF.toStdSimplex q).map (fun ts ↦ majTree fun j ↦ (ts j).1)

theorem expectedCost_majRandTree {ι : Type*} (T : RandomizedDecisionTree ι Bool)
    (r : ℕ) (x : ι → Bool) :
    (majRandTree T r).expectedCost x = (r : ℝ) * T.expectedCost x := by
  unfold majRandTree
  rw [RandomizedDecisionTree.expectedCost_map,
    Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
  simp only [Cslib.Probability.PMF.weights_toStdSimplex, cost_majTree, Nat.cast_sum]
  rw [Cslib.Probability.PMF.sum_pi_mul_sum (fun _ : Fin r ↦ supportPMF T)
    (fun _ s ↦ (s.1.cost x : ℝ))]
  simp only [supportPMF_toReal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [RandomizedDecisionTree.expectedCost_eq_sum, Finsupp.sum]
  exact Finset.sum_coe_sort T.weights.support (fun t ↦ T.weights t * (t.cost x : ℝ))

theorem randExpectedDepthTree_majRandTree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF (ι → Bool)) (T : RandomizedDecisionTree ι Bool) (r : ℕ) :
    randExpectedDepthTree μ (majRandTree T r) = (r : ℝ) * randExpectedDepthTree μ T := by
  have hswap : ∀ U : RandomizedDecisionTree ι Bool,
      randExpectedDepthTree μ U = ∑ x : ι → Bool, (μ x).toReal * U.expectedCost x := by
    intro U
    simp only [randExpectedDepthTree_eq_sum, detExpectedDepth_eq_sum,
      RandomizedDecisionTree.expectedCost_eq_sum, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _
  rw [hswap, hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [expectedCost_majRandTree]
  ring

theorem errorProb_majRandTree_le {ι : Type*} (T : RandomizedDecisionTree ι Bool)
    (f : (ι → Bool) → Bool) (r : ℕ) (x : ι → Bool) {γ : ℝ} (hγ : 0 ≤ γ)
    (hcorr : (1 + γ) / 2 ≤
      T.weights.sum fun t w ↦ w * if t.eval x = f x then (1 : ℝ) else 0) :
    (majRandTree T r).errorProb f x ≤ Real.exp (-(r : ℝ) * γ ^ 2 / 2) := by
  classical
  let q : PMF (Fin r → {t // t ∈ T.weights.support}) :=
    Cslib.Probability.PMF.pi (fun _ : Fin r ↦ supportPMF T)
  let score : Fin r → {t // t ∈ T.weights.support} → ℝ :=
    fun _ s ↦ if s.1.eval x = f x then 1 else 0
  have hscore : ∀ j s, s ∈ (supportPMF T).support → score j s ∈ Set.Icc (0 : ℝ) 1 := by
    intro _ s _
    dsimp only [score]
    split_ifs <;> norm_num
  have hmean_one (j : Fin r) : (1 + γ) / 2 ≤ ∑ s, (supportPMF T s).toReal * score j s := by
    refine hcorr.trans_eq ?_
    simp only [supportPMF_toReal, score, Finsupp.sum]
    exact (Finset.sum_coe_sort T.weights.support
      (fun t ↦ T.weights t * if t.eval x = f x then (1 : ℝ) else 0)).symm
  have hmean : (r : ℝ) * ((1 + γ) / 2) ≤
      ∑ j : Fin r, ∑ s, (supportPMF T s).toReal * score j s := by
    calc (r : ℝ) * ((1 + γ) / 2)
        = ∑ _j : Fin r, (1 + γ) / 2 := by simp
      _ ≤ ∑ j : Fin r, ∑ s, (supportPMF T s).toReal * score j s :=
          Finset.sum_le_sum fun j _ ↦ hmean_one j
  have hhoeff := Cslib.Probability.PMF.pi_sum_le_mean_sub_card_mul
    (fun _ : Fin r ↦ supportPMF T) score hscore (γ := γ / 2) (by linarith)
  have herr_eq : (majRandTree T r).errorProb f x =
      (q.toOuterMeasure {ts | majBool (fun j ↦ (ts j).1.eval x) ≠ f x}).toReal := by
    rw [RandomizedDecisionTree.errorProb_eq_sum, majRandTree, StdSimplex.weights_map,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
    simp only [Cslib.Probability.PMF.weights_toStdSimplex, eval_majTree]
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
    refine Finset.sum_congr rfl fun ts _ ↦ ?_
    by_cases h : majBool (fun j ↦ (ts j).1.eval x) = f x
    · simp only [Set.mem_ofPred_eq, h, ne_eq, not_true_eq_false, ite_false, ite_true, mul_zero]
    · simp only [Set.mem_ofPred_eq, h, ne_eq, not_false_eq_true, ite_true, ite_false, mul_one]
      rfl
  have hsub : {ts : Fin r → {t // t ∈ T.weights.support} |
        majBool (fun j ↦ (ts j).1.eval x) ≠ f x} ⊆
      {ts | ∑ j : Fin r, score j (ts j) ≤
        (∑ j : Fin r, ∑ s, (supportPMF T s).toReal * score j s) -
          (Fintype.card (Fin r) : ℝ) * (γ / 2)} := by
    intro ts hts
    simp only [Set.mem_ofPred_eq, Fintype.card_fin] at hts ⊢
    have hle_half : (∑ j : Fin r, score j (ts j)) ≤ (r : ℝ) / 2 := by
      have hcard : (∑ j : Fin r, score j (ts j)) =
          ((Finset.univ.filter fun j : Fin r ↦ (ts j).1.eval x = f x).card : ℝ) := by
        simp [score, Finset.sum_boole]
      rw [hcard]
      cases hfx : f x
      · have hmaj : majBool (fun j ↦ (ts j).1.eval x) = true := by
          cases hm : majBool (fun j ↦ (ts j).1.eval x)
          · exact absurd (hm.trans hfx.symm) hts
          · rfl
        have hgt : r < 2 * trueCount (fun j ↦ (ts j).1.eval x) := of_decide_eq_true hmaj
        have hcomp : (Finset.univ.filter fun j : Fin r ↦ (ts j).1.eval x = false).card +
            trueCount (fun j ↦ (ts j).1.eval x) = r := by
          rw [trueCount_eq_card_filter]
          have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (p := fun j : Fin r ↦ (ts j).1.eval x = true)
          simp only [Finset.card_univ, Fintype.card_fin] at this
          have heq : (Finset.univ.filter fun j : Fin r ↦ ¬((ts j).1.eval x = true)) =
              Finset.univ.filter fun j : Fin r ↦ (ts j).1.eval x = false := by
            ext j; simp
          rw [heq] at this
          omega
        have hle_nat : 2 * (Finset.univ.filter fun j : Fin r ↦ (ts j).1.eval x =
          false).card ≤ r := by
          omega
        have hle_real : (2 : ℝ) *
            ((Finset.univ.filter fun j : Fin r ↦ (ts j).1.eval x = false).card : ℝ) ≤ r := by
          exact_mod_cast hle_nat
        linarith
      · have hmaj : majBool (fun j ↦ (ts j).1.eval x) = false := by
          cases hm : majBool (fun j ↦ (ts j).1.eval x)
          · rfl
          · exact absurd (hm.trans hfx.symm) hts
        have hle_nat : 2 * trueCount (fun j ↦ (ts j).1.eval x) ≤ r :=
          Nat.le_of_not_lt (of_decide_eq_false hmaj)
        have hle_real : (2 : ℝ) * (trueCount (fun j ↦ (ts j).1.eval x) : ℝ) ≤ r := by
          exact_mod_cast hle_nat
        rw [← trueCount_eq_card_filter]
        linarith
    linarith
  rw [herr_eq]
  have hmono : (q.toOuterMeasure {ts | majBool (fun j ↦ (ts j).1.eval x) ≠ f x}).toReal ≤
      (q.toOuterMeasure {ts | ∑ j : Fin r, score j (ts j) ≤
        (∑ j : Fin r, ∑ s, (supportPMF T s).toReal * score j s) -
          (Fintype.card (Fin r) : ℝ) * (γ / 2)}).toReal :=
    ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
      (q.toOuterMeasure.mono hsub)
  refine hmono.trans (hhoeff.trans_eq ?_)
  simp only [Fintype.card_fin]
  congr 1
  ring

/-! ### Fact: Error reduction for expected-depth randomized query complexity -/

/-- For every Boolean function $f : \{0,1\}^n \to \{0,1\}$ and $\delta \in (0, 1]$,
$\overline{\mathrm{R}}(f, \delta) \le 10 \log(1/\delta) \cdot \overline{\mathrm{R}}(f, 1/4)$. -/
theorem fact_error_reduction_rand {n : ℕ} (f : (Fin n → Bool) → Bool)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    randExpectedDepth f δ ≤ 10 * Real.log (1 / δ) * randExpectedDepth f (1 / 4) := by
  by_cases hhalf : (1 / 2 : ℝ) ≤ δ
  · obtain ⟨T, hT, hd⟩ := QueryComplexity.exists_computes_depth_zero_of_le hhalf f
    have h0 : randExpectedDepth f δ = 0 := by
      refine le_antisymm ?_ (randExpectedDepth_nonneg f δ)
      refine randExpectedDepth_le f hT fun x ↦ ?_
      exact (RandomizedDecisionTree.expectedCost_le_depth).trans (by simp [hd])
    rw [h0]
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
    exact mul_nonneg (by positivity) (randExpectedDepth_nonneg f (1 / 4))
  · push Not at hhalf
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
      norm_num at this
      linarith
    have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (1 / δ) := by
      have h2le : (2 : ℝ) ≤ 1 / δ := by
        rw [le_div_iff₀ hδ0]
        linarith
      exact hlog2.trans (Real.log_le_log (by norm_num) h2le)
    by_cases hq : (1 / 4 : ℝ) ≤ δ
    · have hmono : randExpectedDepth f δ ≤ randExpectedDepth f (1 / 4) :=
        le_randExpectedDepth f (by norm_num) fun T d hT hd ↦
          randExpectedDepth_le f (hT.mono hq) hd
      have h10 : (1 : ℝ) ≤ 10 * Real.log (1 / δ) := by linarith
      have hrnn := randExpectedDepth_nonneg f (1 / 4)
      nlinarith
    · push Not at hq
      let r : ℕ := Nat.ceil (8 * Real.log (1 / δ))
      have hr_ge : 8 * Real.log (1 / δ) ≤ (r : ℝ) := Nat.le_ceil _
      have hr_le : (r : ℝ) ≤ 10 * Real.log (1 / δ) := by
        have hlt : (r : ℝ) < 8 * Real.log (1 / δ) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        linarith
      have hgoal : randExpectedDepth f δ / (r : ℝ) ≤ randExpectedDepth f (1 / 4) := by
        have hrpos : (0 : ℝ) < r := by linarith
        refine le_randExpectedDepth f (by norm_num) fun T d hT hd ↦ ?_
        have hcomp : (majRandTree T r).Computes δ f := by
          intro x
          have hcorr : (1 + (1 / 2 : ℝ)) / 2 ≤
              T.weights.sum fun t w ↦ w * if t.eval x = f x then (1 : ℝ) else 0 := by
            have herr := hT x
            rw [RandomizedDecisionTree.errorProb_eq_sum] at herr
            have hsum1 : (T.weights.sum fun t w ↦
                w * if t.eval x = f x then (1 : ℝ) else 0) +
                (T.weights.sum fun t w ↦
                  w * if t.eval x = f x then (0 : ℝ) else 1) = 1 := by
              simp only [Finsupp.sum, ← Finset.sum_add_distrib, ← mul_add]
              calc (∑ t ∈ T.weights.support, T.weights t *
                    ((if t.eval x = f x then (1 : ℝ) else 0) +
                     (if t.eval x = f x then 0 else 1)))
                  = ∑ t ∈ T.weights.support, T.weights t := by
                    refine Finset.sum_congr rfl fun t _ ↦ ?_
                    split_ifs <;> ring
                _ = 1 := T.total
            linarith
          have hmaj := errorProb_majRandTree_le T f r x (γ := 1 / 2) (by norm_num) hcorr
          refine hmaj.trans ?_
          have hexp : -(r : ℝ) * (1 / 2 : ℝ) ^ 2 / 2 ≤ -Real.log (1 / δ) := by linarith
          calc Real.exp (-(r : ℝ) * (1 / 2 : ℝ) ^ 2 / 2)
              ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.mpr hexp
            _ = δ := by
                rw [Real.exp_neg, Real.exp_log (div_pos one_pos hδ0), one_div, inv_inv]
        have hcost : ∀ x, (majRandTree T r).expectedCost x ≤ (r : ℝ) * d := by
          intro x
          rw [expectedCost_majRandTree]
          exact mul_le_mul_of_nonneg_left (hd x) (Nat.cast_nonneg r)
        have hle := randExpectedDepth_le f hcomp hcost
        rw [div_le_iff₀ hrpos]
        linarith
      have hrpos : (0 : ℝ) < r := by linarith
      have hrnn := randExpectedDepth_nonneg f (1 / 4)
      rw [div_le_iff₀ hrpos] at hgoal
      nlinarith

/-! ### Pruning decision trees to bounded depth -/

/-- Prune redundant queries using the partial assignment `ρ : Fin n → Option Bool`. -/
private def pruneAux {n : ℕ} (ρ : Fin n → Option Bool) :
    DecisionTree (Fin n) Bool → DecisionTree (Fin n) Bool
  | .leaf b => .leaf b
  | .node i t₀ t₁ =>
    match ρ i with
    | some false => pruneAux ρ t₀
    | some true => pruneAux ρ t₁
    | none =>
      .node i (pruneAux (Function.update ρ i (some false)) t₀)
        (pruneAux (Function.update ρ i (some true)) t₁)

/-- Prune every deterministic tree on `Fin n` to a read-once tree of depth at most `n`. -/
private def pruneTree {n : ℕ} (t : DecisionTree (Fin n) Bool) : DecisionTree (Fin n) Bool :=
  pruneAux (fun _ ↦ none) t

private theorem eval_pruneAux {n : ℕ} (ρ : Fin n → Option Bool)
    (t : DecisionTree (Fin n) Bool) (x : Fin n → Bool)
    (hρ : ∀ i b, ρ i = some b → x i = b) :
    (pruneAux ρ t).eval x = t.eval x := by
  induction t generalizing ρ with
  | leaf _ => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [pruneAux]
    cases h : ρ i with
    | none =>
      simp only [DecisionTree.eval_node]
      cases hx : x i
      · exact ih₀ (Function.update ρ i (some false)) fun j b hj ↦ by
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self, Option.some.injEq] at hj
            rw [hx, hj]
          · rw [Function.update_of_ne hji] at hj; exact hρ j b hj
      · exact ih₁ (Function.update ρ i (some true)) fun j b hj ↦ by
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self, Option.some.injEq] at hj
            rw [hx, hj]
          · rw [Function.update_of_ne hji] at hj; exact hρ j b hj
    | some b =>
      have hxb := hρ i b h
      cases b
      · simpa [DecisionTree.eval_node, hxb] using ih₀ ρ hρ
      · simpa [DecisionTree.eval_node, hxb] using ih₁ ρ hρ

private theorem cost_pruneAux_le {n : ℕ} (ρ : Fin n → Option Bool)
    (t : DecisionTree (Fin n) Bool) (x : Fin n → Bool)
    (hρ : ∀ i b, ρ i = some b → x i = b) :
    (pruneAux ρ t).cost x ≤ t.cost x := by
  induction t generalizing ρ with
  | leaf _ => exact le_rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [pruneAux]
    cases h : ρ i with
    | none =>
      simp only [DecisionTree.cost_node]
      cases hx : x i
      · exact Nat.add_le_add_right (ih₀ _ fun j b hj ↦ by
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self, Option.some.injEq] at hj
            rw [hx, hj]
          · rw [Function.update_of_ne hji] at hj; exact hρ j b hj) 1
      · exact Nat.add_le_add_right (ih₁ _ fun j b hj ↦ by
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self, Option.some.injEq] at hj
            rw [hx, hj]
          · rw [Function.update_of_ne hji] at hj; exact hρ j b hj) 1
    | some b =>
      have hxb := hρ i b h
      cases b
      · exact (ih₀ ρ hρ).trans (by simp [hxb])
      · exact (ih₁ ρ hρ).trans (by simp [hxb])

private theorem depth_pruneAux_le {n : ℕ} (ρ : Fin n → Option Bool)
    (t : DecisionTree (Fin n) Bool) :
    (pruneAux ρ t).depth ≤ (Finset.univ.filter fun i : Fin n ↦ ρ i = none).card := by
  induction t generalizing ρ with
  | leaf _ => simp [pruneAux]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [pruneAux]
    cases h : ρ i with
    | some b =>
      cases b
      · exact ih₀ ρ
      · exact ih₁ ρ
    | none =>
      have hcard (b : Bool) :
          (Finset.univ.filter fun j : Fin n ↦ Function.update ρ i (some b) j = none).card + 1 =
            (Finset.univ.filter fun j : Fin n ↦ ρ j = none).card := by
        have herase : (Finset.univ.filter fun j : Fin n ↦
            Function.update ρ i (some b) j = none) =
            (Finset.univ.filter fun j : Fin n ↦ ρ j = none).erase i := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        rw [herase, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)]
      simp only [DecisionTree.depth_node]
      have h0 := ih₀ (Function.update ρ i (some false))
      have h1 := ih₁ (Function.update ρ i (some true))
      have hc0 := hcard false
      have hc1 := hcard true
      omega

private theorem eval_pruneTree {n : ℕ} (t : DecisionTree (Fin n) Bool) (x : Fin n → Bool) :
    (pruneTree t).eval x = t.eval x :=
  eval_pruneAux _ t x fun _ _ h ↦ by simp at h

private theorem cost_pruneTree_le {n : ℕ} (t : DecisionTree (Fin n) Bool) (x : Fin n → Bool) :
    (pruneTree t).cost x ≤ t.cost x :=
  cost_pruneAux_le _ t x fun _ _ h ↦ by simp at h

private theorem depth_pruneTree_le {n : ℕ} (t : DecisionTree (Fin n) Bool) :
    (pruneTree t).depth ≤ n := by
  refine (depth_pruneAux_le _ t).trans ?_
  simp

private noncomputable def allTreesOfDepthLe (n : ℕ) : ℕ → Finset (DecisionTree (Fin n) Bool)
  | 0 => by classical exact {.leaf false, .leaf true}
  | d + 1 => by
    classical
    let prev := allTreesOfDepthLe n d
    exact prev ∪ (Finset.univ ×ˢ (prev ×ˢ prev)).image (fun x ↦ .node x.1 x.2.1 x.2.2)

private theorem mem_allTreesOfDepthLe {n d : ℕ} {t : DecisionTree (Fin n) Bool}
    (hd : t.depth ≤ d) : t ∈ allTreesOfDepthLe n d := by
  classical
  induction d generalizing t with
  | zero =>
    cases t with
    | leaf b =>
      cases b <;> simp [allTreesOfDepthLe]
    | node _ _ _ => simp at hd
  | succ d ih =>
    cases t with
    | leaf b =>
      simp only [allTreesOfDepthLe, Finset.mem_union]
      exact Or.inl (ih (by simp))
    | node i t₀ t₁ =>
      simp only [DecisionTree.depth_node] at hd
      simp only [allTreesOfDepthLe, Finset.mem_union, Finset.mem_image, Finset.mem_product,
        Finset.mem_univ, true_and, Prod.exists]
      exact Or.inr ⟨i, t₀, t₁, ⟨ih (by omega), ih (by omega)⟩, rfl⟩

/-! ### -/

/-- For every Boolean function `f : (Fin n → Bool) → Bool`, distribution `μ`, and `γ, δ ∈ (0, 1)`
with `0 < distDepth μ f δ`, there exists a `(γ, d)`-hardcore measure `H` for `f` of density
`δ / 2` w.r.t. `μ`, where `d = (γ ^ 2 / (10 * Real.log (1 / δ))) * distDepth μ f δ`. -/
theorem hardcoreTheorem {n : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) {γ δ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ0 : 0 < δ)
    (hpos : 0 < distDepth μ f δ) :
    ∃ H : (Fin n → Bool) → ℝ,
      IsHardcoreMeasure μ f γ
        (γ ^ 2 / (10 * Real.log (1 / δ)) * distDepth μ f δ) (δ / 2) H := by
  classical
  have hδ_half : δ < 1 / 2 := by
    by_contra! hge
    have h0 := distDepth_eq_zero_of_half_le μ f hge
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    norm_num at this
    linarith
  have hlog_pos : 0 < Real.log (1 / δ) := by
    have h2le : (2 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    linarith [hlog2.trans (Real.log_le_log (by norm_num) h2le)]
  set d : ℝ := γ ^ 2 / (10 * Real.log (1 / δ)) * distDepth μ f δ
  have hd_pos : 0 < d := by positivity
  set S : Finset (DecisionTree (Fin n) Bool) := allTreesOfDepthLe n n
  have hleaf_mem : DecisionTree.leaf false ∈ S :=
    mem_allTreesOfDepthLe (by simp)
  let X : Set ((Fin n → Bool) → ℝ) :=
    {H | (∀ x, H x ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ x : Fin n → Bool, (μ x).toReal * H x = δ / 2}
  let Y : Set (S → ℝ) :=
    {τ | (∀ t, 0 ≤ τ t) ∧ (∑ t : S, τ t = 1) ∧
      (∑ t : S, τ t * detExpectedDepth μ t.1) ≤ d}
  let M : ((Fin n → Bool) → ℝ) → (S → ℝ) → ℝ :=
    fun H τ ↦ ∑ x : Fin n → Bool,
      (μ x).toReal * signBool (f x) * (∑ t : S, τ t * signBool (t.1.eval x)) * H x
  have hne_X : X.Nonempty := by
    refine ⟨fun _ ↦ δ / 2, fun _ ↦ ⟨by linarith, by linarith⟩, ?_⟩
    rw [← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
  have hc_X : Convex ℝ X := by
    intro H₁ h₁ H₂ h₂ a b ha hb hab
    refine ⟨fun x ↦ ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := (h₁.1 x).1; have := (h₂.1 x).1; positivity
    · have h1 := (h₁.1 x).2; have h2 := (h₂.1 x).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      have hs1 : (∑ x : Fin n → Bool, (μ x).toReal * (a * H₁ x)) = a * (δ / 2) := by
        rw [← h₁.2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      have hs2 : (∑ x : Fin n → Bool, (μ x).toReal * (b * H₂ x)) = b * (δ / 2) := by
        rw [← h₂.2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hs1, hs2, ← add_mul, hab, one_mul]
  have hk_X : IsCompact X := by
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n → Bool ↦ Set.Icc (0 : ℝ) 1) :=
      isCompact_univ_pi fun _ ↦ isCompact_Icc
    have hclosed : IsClosed {H : (Fin n → Bool) → ℝ |
        ∑ x : Fin n → Bool, (μ x).toReal * H x = δ / 2} :=
      isClosed_eq (by fun_prop) continuous_const
    have hsub : X = (Set.pi Set.univ fun _ : Fin n → Bool ↦ Set.Icc (0 : ℝ) 1) ∩
        {H : (Fin n → Bool) → ℝ | ∑ x : Fin n → Bool, (μ x).toReal * H x = δ / 2} := by
      ext H
      simp only [X, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_ofPred_eq, Set.mem_Icc]
    rw [hsub]
    exact hbox.inter_right hclosed
  have hne_Y : Y.Nonempty := by
    let t₀ : S := ⟨.leaf false, hleaf_mem⟩
    refine ⟨fun t ↦ if t = t₀ then 1 else 0, fun t ↦ by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
    · simp
    · simp [t₀, hd_pos.le]
  have hc_Y : Convex ℝ Y := by
    intro τ₁ h₁ τ₂ h₂ a b ha hb hab
    refine ⟨fun t ↦ ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := h₁.1 t; have := h₂.1 t; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, h₁.2.1, h₂.2.1, mul_one, hab]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      have hs1 : (∑ t : S, a * τ₁ t * detExpectedDepth μ t.1) =
          a * ∑ t : S, τ₁ t * detExpectedDepth μ t.1 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      have hs2 : (∑ t : S, b * τ₂ t * detExpectedDepth μ t.1) =
          b * ∑ t : S, τ₂ t * detExpectedDepth μ t.1 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hs1, hs2]
      nlinarith [h₁.2.2, h₂.2.2]
  have hk_Y : IsCompact Y := by
    have hbox : IsCompact (Set.pi Set.univ fun _ : S ↦ Set.Icc (0 : ℝ) 1) :=
      isCompact_univ_pi fun _ ↦ isCompact_Icc
    have hc1 : IsClosed {τ : S → ℝ | ∑ t : S, τ t = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    have hc2 : IsClosed {τ : S → ℝ | ∑ t : S, τ t * detExpectedDepth μ t.1 ≤ d} :=
      isClosed_le (by fun_prop) continuous_const
    have hsub : Y = ((Set.pi Set.univ fun _ : S ↦ Set.Icc (0 : ℝ) 1) ∩
        {τ : S → ℝ | ∑ t : S, τ t = 1}) ∩
        {τ : S → ℝ | ∑ t : S, τ t * detExpectedDepth μ t.1 ≤ d} := by
      ext τ
      simp only [Y, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_Icc, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨⟨fun t ↦ ⟨h0 t, ?_⟩, h1⟩, h2⟩
        rw [← h1]
        exact Finset.single_le_sum (fun s _ ↦ h0 s) (Finset.mem_univ t)
      · rintro ⟨⟨h01, h1⟩, h2⟩
        exact ⟨fun t ↦ (h01 t).1, h1, h2⟩
    rw [hsub]
    exact (hbox.inter_right hc1).inter_right hc2
  have hM_cont_H : ∀ τ, Continuous fun H ↦ M H τ := fun τ ↦ by
    dsimp only [M]; fun_prop
  have hM_cont_τ : ∀ H, Continuous fun τ ↦ M H τ := fun H ↦ by
    dsimp only [M]; fun_prop
  have hM_conv : ∀ τ ∈ Y, ConvexOn ℝ X fun H ↦ M H τ := by
    intro τ _
    refine ⟨hc_X, fun H₁ _ H₂ _ a b _ _ _ ↦ le_of_eq ?_⟩
    simp only [M, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    congr 1 <;> rw [Finset.mul_sum] <;> exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hM_conc : ∀ H ∈ X, ConcaveOn ℝ Y fun τ ↦ M H τ := by
    intro H _
    refine ⟨hc_Y, fun τ₁ _ τ₂ _ a b _ _ _ ↦ le_of_eq ?_⟩
    simp only [M, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ by ring
  obtain ⟨H₀, hH₀, τ₀, hτ₀, hsaddle⟩ := Sion.exists_isSaddlePointOn
    hne_X hc_X hk_X
    (fun τ _ ↦ (hM_cont_H τ).continuousOn.lowerSemicontinuousOn)
    (fun τ hτ ↦ (hM_conv τ hτ).quasiconvexOn)
    hc_Y hne_Y hk_Y
    (fun H _ ↦ (hM_cont_τ H).continuousOn.upperSemicontinuousOn)
    (fun H hH ↦ (hM_conc H hH).quasiconcaveOn)
  refine ⟨H₀, hH₀.1, hH₀.2, ?_⟩
  by_contra! hex
  obtain ⟨T, hTd, hTcorr⟩ := hex
  let pτ : StdSimplex ℝ S :=
    { weights := Finsupp.equivFunOnFinite.symm (fun t : S ↦
        T.weights.sum fun u w ↦ if pruneTree u = t.1 then w else 0)
      nonneg := fun t ↦ Finset.sum_nonneg fun u _ ↦ by
        dsimp only
        split_ifs
        · exact T.weights_nonneg u
        · exact le_rfl
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
        change (∑ t : S, ∑ u ∈ T.weights.support, if pruneTree u = t.1 then T.weights u else 0) = 1
        rw [Finset.sum_comm]
        calc (∑ u ∈ T.weights.support, ∑ t : S, if pruneTree u = t.1 then T.weights u else 0)
            = ∑ u ∈ T.weights.support, T.weights u := by
              refine Finset.sum_congr rfl fun u _ ↦ ?_
              have hmem : pruneTree u ∈ S := mem_allTreesOfDepthLe (depth_pruneTree_le u)
              rw [Finset.sum_eq_single ⟨pruneTree u, hmem⟩]
              · simp
              · intro t _ hne
                have hne' : pruneTree u ≠ t.1 := fun heq ↦ hne (Subtype.ext heq.symm)
                simp [hne']
              · intro h; exact absurd (Finset.mem_univ _) h
          _ = 1 := T.total }
  have hpτ_mem : (fun t : S ↦ pτ.weights t) ∈ Y := by
    refine ⟨fun t ↦ pτ.weights_nonneg t, ?_, ?_⟩
    · have ht := pτ.total
      rwa [Finsupp.sum_fintype _ (fun _ w ↦ w) (fun _ ↦ rfl)] at ht
    · change (∑ t : S, (∑ u ∈ T.weights.support,
          if pruneTree u = t.1 then T.weights u else 0) * detExpectedDepth μ t.1) ≤ d
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      calc (∑ u ∈ T.weights.support, ∑ t : S,
            (if pruneTree u = t.1 then T.weights u else 0) * detExpectedDepth μ t.1)
          = ∑ u ∈ T.weights.support, T.weights u * detExpectedDepth μ (pruneTree u) := by
            refine Finset.sum_congr rfl fun u _ ↦ ?_
            have hmem : pruneTree u ∈ S := mem_allTreesOfDepthLe (depth_pruneTree_le u)
            rw [Finset.sum_eq_single ⟨pruneTree u, hmem⟩]
            · simp
            · intro t _ hne
              have hne' : pruneTree u ≠ t.1 := fun heq ↦ hne (Subtype.ext heq.symm)
              simp [hne']
            · intro h; exact absurd (Finset.mem_univ _) h
        _ ≤ ∑ u ∈ T.weights.support, T.weights u * detExpectedDepth μ u := by
            refine Finset.sum_le_sum fun u _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg u)
            rw [detExpectedDepth_eq_sum, detExpectedDepth_eq_sum]
            exact Finset.sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cost_pruneTree_le u x))
                ENNReal.toReal_nonneg
        _ ≤ d := by
            rw [randExpectedDepthTree_eq_sum, Finsupp.sum] at hTd
            exact hTd
  have hM_pτ : M H₀ (fun t ↦ pτ.weights t) =
      T.weights.sum fun u w ↦ w * ∑ x : Fin n → Bool,
        (μ x).toReal * (signBool (f x) * signBool (u.eval x) * H₀ x) := by
    change (∑ x : Fin n → Bool, (μ x).toReal * signBool (f x) *
      (∑ t : S, (∑ u ∈ T.weights.support, if pruneTree u = t.1 then T.weights u else 0) *
        signBool (t.1.eval x)) * H₀ x) =
      ∑ u ∈ T.weights.support, T.weights u * ∑ x : Fin n → Bool,
        (μ x).toReal * (signBool (f x) * signBool (u.eval x) * H₀ x)
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Finset.sum_mul]
    have hmem : pruneTree u ∈ S := mem_allTreesOfDepthLe (depth_pruneTree_le u)
    rw [Finset.sum_eq_single ⟨pruneTree u, hmem⟩]
    · simp only [ite_true, eval_pruneTree]; ring
    · intro t _ hne
      have hne' : pruneTree u ≠ t.1 := fun heq ↦ hne (Subtype.ext heq.symm)
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ _) h
  have hM_gt : ∀ H ∈ X, γ * (δ / 2) < M H τ₀ := by
    intro H hH
    have hs : M H₀ (fun t ↦ pτ.weights t) ≤ M H τ₀ := hsaddle H hH _ hpτ_mem
    linarith
  let g : (Fin n → Bool) → ℝ :=
    fun x ↦ signBool (f x) * (∑ t : S, τ₀ t * signBool (t.1.eval x))
  let bad : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦ g x < γ
  let pbad : ℝ := ∑ x ∈ bad, (μ x).toReal
  have hpbad_lt : pbad < δ / 2 := by
    by_contra! hpge
    have hppos : 0 < pbad := lt_of_lt_of_le (by linarith) hpge
    let Hbad : (Fin n → Bool) → ℝ := fun x ↦ if g x < γ then (δ / 2) / pbad else 0
    have hHbad_mem : Hbad ∈ X := by
      refine ⟨fun x ↦ ?_, ?_⟩
      · dsimp only [Hbad]
        split_ifs
        · exact ⟨by positivity, (div_le_one hppos).mpr hpge⟩
        · exact ⟨le_rfl, zero_le_one⟩
      · have hfilt : (∑ x : Fin n → Bool, (μ x).toReal * Hbad x) =
            (∑ x ∈ bad, (μ x).toReal) * ((δ / 2) / pbad) := by
          simp only [Hbad, mul_ite, mul_zero, ← Finset.sum_filter, bad, ← Finset.sum_mul]
        rw [hfilt]
        change pbad * ((δ / 2) / pbad) = δ / 2
        field_simp
    have hM_bad : M Hbad τ₀ < γ * (δ / 2) := by
      have hM_eq : M Hbad τ₀ = ∑ x ∈ bad, (μ x).toReal * g x * ((δ / 2) / pbad) := by
        simp only [M, g, Hbad, mul_ite, mul_zero, ← Finset.sum_filter, bad]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hM_eq]
      have hnonempty : ∃ x ∈ bad, 0 < (μ x).toReal := by
        by_contra! hall
        have : pbad ≤ 0 := Finset.sum_nonpos fun x hx ↦ hall x hx
        linarith
      have hstrict : (∑ x ∈ bad, (μ x).toReal * g x * ((δ / 2) / pbad)) <
          ∑ x ∈ bad, (μ x).toReal * γ * ((δ / 2) / pbad) := by
        refine Finset.sum_lt_sum (fun x hx ↦ ?_) ?_
        · have hgx : g x < γ := (Finset.mem_filter.mp hx).2
          have hfac : 0 ≤ (μ x).toReal * ((δ / 2) / pbad) := by positivity
          nlinarith
        · obtain ⟨x, hx, hμx⟩ := hnonempty
          refine ⟨x, hx, ?_⟩
          have hgx : g x < γ := (Finset.mem_filter.mp hx).2
          have hfac : 0 < (μ x).toReal * ((δ / 2) / pbad) := by positivity
          nlinarith
      refine hstrict.trans_eq ?_
      have hfac : (∑ x ∈ bad, (μ x).toReal * γ * ((δ / 2) / pbad)) =
          (∑ x ∈ bad, (μ x).toReal) * (γ * ((δ / 2) / pbad)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hfac]
      change pbad * (γ * ((δ / 2) / pbad)) = γ * (δ / 2)
      field_simp
    linarith [hM_gt Hbad hHbad_mem]
  let T₀ : RandomizedDecisionTree (Fin n) Bool :=
    (StdSimplex.mk (Finsupp.equivFunOnFinite.symm τ₀) hτ₀.1 (by
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
      exact hτ₀.2.1)).map Subtype.val
  have hT₀_depth : randExpectedDepthTree μ T₀ ≤ d := by
    rw [randExpectedDepthTree_eq_sum]
    dsimp only [T₀]
    rw [StdSimplex.weights_map,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
    exact hτ₀.2.2
  let r : ℕ := Nat.ceil (2 * Real.log (2 / δ) / γ ^ 2)
  have hr_ge : 2 * Real.log (2 / δ) / γ ^ 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hr_maj_err : randDistError μ f (majRandTree T₀ r) ≤ δ := by
    rw [randDistError_eq_sum_eval]
    have hsplit : (∑ x : Fin n → Bool, (μ x).toReal * (majRandTree T₀ r).errorProb f x) ≤
        pbad + (1 - pbad) * (δ / 2) := by
      have hsum_compl : (∑ x ∈ Finset.univ.filter (fun x ↦ ¬(g x < γ)), (μ x).toReal) =
          1 - pbad := by
        have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ g x < γ)
          (fun x ↦ (μ x).toReal)
        rw [Cslib.Probability.PMF.sum_toReal] at h
        change pbad + _ = 1 at h
        linarith
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ g x < γ)]
      refine add_le_add ?_ ?_
      · refine Finset.sum_le_sum fun x _ ↦ ?_
        have := RandomizedDecisionTree.errorProb_le_one (μ := majRandTree T₀ r) (f := f) (x := x)
        nlinarith [ENNReal.toReal_nonneg (a := μ x)]
      · calc (∑ x ∈ Finset.univ.filter (fun x ↦ ¬(g x < γ)),
              (μ x).toReal * (majRandTree T₀ r).errorProb f x)
            ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ ¬(g x < γ)), (μ x).toReal * (δ / 2) := by
              refine Finset.sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              have hgx : γ ≤ g x := not_lt.mp (Finset.mem_filter.mp hx).2
              have hcorr : (1 + γ) / 2 ≤
                  T₀.weights.sum fun t w ↦ w * if t.eval x = f x then (1 : ℝ) else 0 := by
                have hgx_eq : g x =
                  T₀.weights.sum fun t w ↦ w * (signBool (f x) * signBool (t.eval x)) := by
                  dsimp only [g, T₀]
                  rw [StdSimplex.weights_map,
                    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
                    Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _), Finset.mul_sum]
                  refine Finset.sum_congr rfl fun t _ ↦ ?_
                  change signBool (f x) * (τ₀ t * signBool (t.1.eval x)) =
                    τ₀ t * (signBool (f x) * signBool (t.1.eval x))
                  ring
                have hconv : (T₀.weights.sum fun t w ↦
                    w * if t.eval x = f x then (1 : ℝ) else 0) = (1 + g x) / 2 := by
                  rw [hgx_eq]
                  have h1 : (T₀.weights.sum fun t w ↦ w * (1 : ℝ)) = 1 := by
                    simp
                  simp only [Finsupp.sum] at h1 ⊢
                  calc (∑ t ∈ T₀.weights.support, T₀.weights t * if t.eval x = f x then 1 else 0)
                      = ∑ t ∈ T₀.weights.support, T₀.weights t *
                          ((1 + signBool (f x) * signBool (t.eval x)) / 2) := by
                        refine Finset.sum_congr rfl fun t _ ↦ ?_
                        rw [one_add_signBool_mul_div_two]
                        by_cases h : f x = t.eval x <;> simp [h, eq_comm]
                    _ = (∑ t ∈ T₀.weights.support, T₀.weights t * (1 : ℝ) +
                          ∑ t ∈ T₀.weights.support,
                            T₀.weights t * (signBool (f x) * signBool (t.eval x))) / 2 := by
                        rw [← Finset.sum_add_distrib, Finset.sum_div]
                        exact Finset.sum_congr rfl fun _ _ ↦ by ring
                    _ = (1 + ∑ t ∈ T₀.weights.support,
                          T₀.weights t * (signBool (f x) * signBool (t.eval x))) / 2 := by
                        rw [h1]
                rw [hconv]
                linarith
              refine (errorProb_majRandTree_le T₀ f r x hγ0.le hcorr).trans ?_
              have hexp : -(r : ℝ) * γ ^ 2 / 2 ≤ -Real.log (2 / δ) := by
                have hmul : 2 * Real.log (2 / δ) ≤ (r : ℝ) * γ ^ 2 := by
                  rwa [div_le_iff₀ (by positivity)] at hr_ge
                linarith
              calc Real.exp (-(r : ℝ) * γ ^ 2 / 2)
                  ≤ Real.exp (-Real.log (2 / δ)) := Real.exp_le_exp.mpr hexp
                _ = δ / 2 := by
                    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hδ0)]
                    field_simp
          _ = (1 - pbad) * (δ / 2) := by rw [← Finset.sum_mul, hsum_compl]
    have hpbad_nonneg : 0 ≤ pbad := Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
    nlinarith
  have hr_lt : (r : ℝ) * d < distDepth μ f δ := by
    have hlog2_le : Real.log (2 / δ) < 2 * Real.log (1 / δ) := by
      have hsplit : Real.log (2 / δ) = Real.log 2 + Real.log (1 / δ) := by
        rw [show (2 : ℝ) / δ = 2 * (1 / δ) by ring,
          Real.log_mul (by norm_num) (ne_of_gt (div_pos one_pos hδ0))]
      have hlog2_lt : Real.log 2 < Real.log (1 / δ) :=
        Real.log_lt_log (by norm_num) (by rw [lt_div_iff₀ hδ0]; linarith)
      linarith
    have hlog2_pos : 0 < Real.log (2 / δ) :=
      Real.log_pos (by rw [one_lt_div hδ0]; linarith)
    have hr_bound : (r : ℝ) < 6 * Real.log (1 / δ) / γ ^ 2 := by
      have hceil : (r : ℝ) < 2 * Real.log (2 / δ) / γ ^ 2 + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h1_lt : (1 : ℝ) < 2 * Real.log (1 / δ) / γ ^ 2 := by
        rw [lt_div_iff₀ (by positivity)]
        have hγsq : γ ^ 2 ≤ 1 := by nlinarith
        have hlog_gt : (1 / 2 : ℝ) < Real.log (1 / δ) := by
          have h2lt : (2 : ℝ) < 1 / δ := by rw [lt_div_iff₀ hδ0]; linarith
          exact lt_of_le_of_lt hlog2 (Real.log_lt_log (by norm_num) h2lt)
        nlinarith
      have h2_lt : 2 * Real.log (2 / δ) / γ ^ 2 < 4 * Real.log (1 / δ) / γ ^ 2 := by
        have hdiv := div_lt_div_of_pos_right (show 2 * Real.log (2 / δ) < 4 * Real.log (1 / δ) by
          linarith) (show 0 < γ ^ 2 by positivity)
        simpa [mul_div_assoc] using hdiv
      have hsum_eq : 4 * Real.log (1 / δ) / γ ^ 2 + 2 * Real.log (1 / δ) / γ ^ 2 =
          6 * Real.log (1 / δ) / γ ^ 2 := by ring
      linarith
    have hprod_eq : (6 * Real.log (1 / δ) / γ ^ 2) * d = (3 / 5) * distDepth μ f δ := by
      simp only [d]
      field_simp
      ring
    nlinarith
  have hdepth_le := distDepth_le μ f hr_maj_err
  have hdepth_maj : randExpectedDepthTree μ (majRandTree T₀ r) ≤ (r : ℝ) * d := by
    rw [randExpectedDepthTree_majRandTree]
    exact mul_le_mul_of_nonneg_left hT₀_depth (Nat.cast_nonneg r)
  linarith

/-- **Counterexample to the unguarded statement of the corresponding result**:
When `f` is the constant `true` function, `distDepth μ f δ = 0`, so `d = 0` for every real
factor `c`, yet no `(γ, 0)`-hardcore measure of density `δ / 2` exists for any `γ ∈ (0, 1)`
and `δ > 0`. -/
theorem hardcoreTheorem_counterexample {n : ℕ} (μ : PMF (Fin n → Bool))
    {γ δ : ℝ} (hγ1 : γ < 1) (hδ0 : 0 < δ) (c : ℝ) :
    ¬∃ H : (Fin n → Bool) → ℝ,
      IsHardcoreMeasure μ (fun _ ↦ true) γ
        (c * (γ ^ 2 / Real.log (1 / δ)) * distDepth μ (fun _ ↦ true) δ) (δ / 2) H := by
  rintro ⟨H, hH⟩
  have h0 : distDepth μ (fun _ ↦ true) δ = 0 := distDepth_const μ true hδ0.le
  have hcorr := hH.correlation_le (StdSimplex.single (.leaf true)) (by
    rw [h0, mul_zero, randExpectedDepthTree_single, detExpectedDepth_leaf])
  rw [StdSimplex.weights_single, Finsupp.sum_single_index (zero_mul _)] at hcorr
  simp only [one_mul, DecisionTree.eval_leaf, signBool_true, hH.density] at hcorr
  nlinarith

end CslibFrontier.Computability.QueryComplexity.DirectSum

end
