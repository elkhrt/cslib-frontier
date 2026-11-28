/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.MinCostFlow
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Additively Separable Grid Transport via Layered Minimum-Cost Flow

Formalizes the $(d + 1)$-layer minimum-cost network flow reduction for discrete optimal transport
between integral histograms on the $d$-dimensional grid $\{0, \dots, L - 1\}^d$ under any
additively separable cost $c(a, b) = \sum_{s = 0}^{d - 1} c_s(a_s, b_s)$
.

Instead of forming the dense $L^d \times L^d$ bipartite transportation graph ($L^{2d}$ arcs),
routing coordinates one axis per layer produces a $(d + 1)$-layer directed acyclic `CostNetwork`
with $(d + 1) L^d$ vertices and $d L^{d + 1}$ positive-capacity arcs whose minimum-cost integral
flow value equals the exact minimum separable transport plan cost and dominates the dual
Kantorovich lower bound against every real-valued fractional coupling.

## Main definitions

* `CslibFrontier.Algorithms.Lean.MaxFlow.IsIntegralTransportPlan`: integral transport matrix
  `M : (Fin d → Fin L) → (Fin d → Fin L) → ℕ` with prescribed row sums `p` and column sums `q`.
* `CslibFrontier.Algorithms.Lean.MaxFlow.separablePlanCost`: total separable cost
  `∑ a, ∑ b, M a b * ∑ s : Fin d, coordCost s (a s) (b s)`.
* `CslibFrontier.Algorithms.Lean.MaxFlow.separableGridCostNetwork`: the $(d + 1)$-layer
  `Cslib.Algorithms.Lean.MaxFlow.CostNetwork` on `Fin (d + 1) × (Fin d → Fin L)`.
* `CslibFrontier.Algorithms.Lean.MaxFlow.flowOfIntegralPlan`: canonical projection of an integral
  transport plan to a feasible flow on `separableGridCostNetwork`.

## Main results

* `CslibFrontier.Algorithms.Lean.MaxFlow.totalCost_flowOfIntegralPlan`: projecting an integral
  transport plan preserves total cost (`(flowOfIntegralPlan...).totalCost = separablePlanCost`).
* `CslibFrontier.Algorithms.Lean.MaxFlow.flow_le_supply_on_separableGridCostNetwork`:
  cut-conservation bound showing every arc flow on `separableGridCostNetwork` is strictly below
  `k + 1`.
* `CslibFrontier.Algorithms.Lean.MaxFlow.totalCost_le_realCoupling_of_isMinCost`: complementary
  slackness optimality against arbitrary real-valued couplings with marginals `p` and `q`.
-/

public section

namespace CslibFrontier.Algorithms.Lean.MaxFlow

open Finset
open Cslib.Algorithms.Lean.MaxFlow

/-- An integral transport plan between nonnegative integer histograms `p, q` on `(Fin d → Fin L)`
is a matrix `M` with row sums `p` and column sums `q`. -/
structure IsIntegralTransportPlan {d L : ℕ} (p q : (Fin d → Fin L) → ℕ)
    (M : (Fin d → Fin L) → (Fin d → Fin L) → ℕ) : Prop where
  /-- Row-sum marginal constraint `∑ b, M a b = p a`. -/
  row_sum : ∀ a, ∑ b, M a b = p a
  /-- Column-sum marginal constraint `∑ a, M a b = q b`. -/
  col_sum : ∀ b, ∑ a, M a b = q b

/-- Additively separable cost `∑ s : Fin d, coordCost s (a s) (b s)` between grid points `a, b`. -/
@[expose] def separablePairCost {d L : ℕ} (coordCost : Fin d → Fin L → Fin L → ℕ)
    (a b : Fin d → Fin L) : ℕ :=
  ∑ s : Fin d, coordCost s (a s) (b s)

/-- Total cost of an integral transport plan `M` under `separablePairCost coordCost`. -/
@[expose] def separablePlanCost {d L : ℕ} (coordCost : Fin d → Fin L → Fin L → ℕ)
    (M : (Fin d → Fin L) → (Fin d → Fin L) → ℕ) : ℕ :=
  ∑ a, ∑ b, M a b * separablePairCost coordCost a b

/-- Hybrid grid point after routing coordinates `0, …, t - 1` from `a` to `b`:
coordinates `< t.val` equal `b`, and coordinates `≥ t.val` equal `a`. -/
@[expose] def layerHybridPoint {d L : ℕ} (a b : Fin d → Fin L) (t : Fin (d + 1)) : Fin d → Fin L :=
  fun j => if j.val < t.val then b j else a j

@[simp]
theorem layerHybridPoint_zero {d L : ℕ} (a b : Fin d → Fin L) :
    layerHybridPoint a b 0 = a := by
  funext j
  simp [layerHybridPoint]

@[simp]
theorem layerHybridPoint_last {d L : ℕ} (a b : Fin d → Fin L) :
    layerHybridPoint a b (Fin.last d) = b := by
  funext j
  simp [layerHybridPoint, j.isLt]

theorem layerHybridPoint_succ {d L : ℕ} (a b : Fin d → Fin L) (s : Fin d) :
    layerHybridPoint a b s.succ = Function.update (layerHybridPoint a b s.castSucc) s (b s) := by
  funext j
  by_cases hjs : j = s
  · subst hjs
    simp [layerHybridPoint]
  · have hval : j.val ≠ s.val := fun h => hjs (Fin.ext h)
    have hiff : (j.val < s.val + 1) ↔ (j.val < s.val) := by omega
    simp only [layerHybridPoint, Fin.val_succ, Fin.val_castSucc, Function.update_of_ne hjs, hiff]

/-- Predicate characterizing valid single-axis transitions from layer `s.castSucc` to `s.succ`. -/
@[expose] def IsLayerStep {d L : ℕ} (u v : Fin (d + 1) × (Fin d → Fin L)) : Prop :=
  ∃ s : Fin d, u.1 = s.castSucc ∧ v.1 = s.succ ∧ ∀ j : Fin d, j ≠ s → u.2 j = v.2 j

instance instDecidableIsLayerStep {d L : ℕ} (u v : Fin (d + 1) × (Fin d → Fin L)) :
    Decidable (IsLayerStep u v) := by
  unfold IsLayerStep
  infer_instance

/-- If `IsLayerStep u v`, the layer index `s : Fin d` is uniquely determined by
`u.1 = s.castSucc`. -/
theorem isLayerStep_iff {d L : ℕ} {u v : Fin (d + 1) × (Fin d → Fin L)} :
    IsLayerStep u v ↔
      u.1.val < d ∧ v.1.val = u.1.val + 1 ∧ ∀ j : Fin d, j.val ≠ u.1.val → u.2 j = v.2 j := by
  constructor
  · rintro ⟨s, hu, hv, hj⟩
    refine ⟨by simp [hu], by simp [hu, hv], fun j hne => hj j ?_⟩
    intro heq
    apply hne
    simp [hu, heq]
  · rintro ⟨hlt, hv, hj⟩
    refine ⟨⟨u.1.val, hlt⟩, Fin.ext rfl, Fin.ext hv, fun j hne => hj j (Fin.val_ne_of_ne hne)⟩

/-- The $(d + 1)$-layer `CostNetwork` on `Fin (d + 1) × (Fin d → Fin L)` for histograms `p, q`
of total mass `k` and 1D coordinate costs `coordCost`. Valid single-axis arcs carry capacity
`k + 1` so every feasible flow of mass `k` is strictly unsaturated on every valid arc. -/
@[expose] def separableGridCostNetwork {d L : ℕ} (k : ℕ) (p q : (Fin d → Fin L) → ℕ)
    (coordCost : Fin d → Fin L → Fin L → ℕ) :
    CostNetwork (Fin (d + 1) × (Fin d → Fin L)) ℤ where
  cap u v := if IsLayerStep u v then k + 1 else 0
  cost u v :=
    if h : u.1.val < d ∧ v.1.val = u.1.val + 1 ∧
        (∀ j : Fin d, j.val ≠ u.1.val → u.2 j = v.2 j) then
      (coordCost ⟨u.1.val, h.1⟩ (u.2 ⟨u.1.val, h.1⟩) (v.2 ⟨u.1.val, h.1⟩) : ℤ)
    else 0
  balance u :=
    (if u.1 = 0 then (p u.2 : ℤ) else 0) - (if u.1 = Fin.last d then (q u.2 : ℤ) else 0)

@[simp]
theorem separableGridCostNetwork_cost_step {d L : ℕ} (k : ℕ) (p q : (Fin d → Fin L) → ℕ)
    (coordCost : Fin d → Fin L → Fin L → ℕ) (s : Fin d) (x : Fin d → Fin L) (c : Fin L) :
    (separableGridCostNetwork k p q coordCost).cost
      (s.castSucc, x) (s.succ, Function.update x s c) =
      (coordCost s (x s) c : ℤ) := by
  have hcond : (s.castSucc).val < d ∧ (s.succ).val = (s.castSucc).val + 1 ∧
      ∀ j : Fin d, j.val ≠ (s.castSucc).val → x j = Function.update x s c j := by
    refine ⟨s.isLt, rfl, fun j hj => ?_⟩
    have hjs : j ≠ s := fun h => hj (by simp [h])
    rw [Function.update_of_ne hjs]
  have hs_eq : (⟨(s.castSucc).val, hcond.1⟩ : Fin d) = s := Fin.ext rfl
  simp only [separableGridCostNetwork, dite_eq_left_of_eq_true (eq_true hcond), hs_eq,
    Function.update_self]

/-- Project an integral transport plan `M` (with total mass `k`) to a feasible flow on
`separableGridCostNetwork k p q coordCost`. -/
@[expose] def flowOfIntegralPlan {d L k : ℕ} {p q : (Fin d → Fin L) → ℕ}
    (coordCost : Fin d → Fin L → Fin L → ℕ)
    {M : (Fin d → Fin L) → (Fin d → Fin L) → ℕ}
    (hM : IsIntegralTransportPlan p q M) (hk : ∑ a, p a = k) :
    (separableGridCostNetwork k p q coordCost).Flow where
  toFun u v :=
    if h : u.1.val < d ∧ v.1.val = u.1.val + 1 ∧
        (∀ j : Fin d, j.val ≠ u.1.val → u.2 j = v.2 j) then
      ∑ a, ∑ b,
        if layerHybridPoint a b ⟨u.1.val, Nat.lt_succ_of_lt h.1⟩ = u.2 ∧
            layerHybridPoint a b ⟨v.1.val, v.1.isLt⟩ = v.2 then M a b else 0
    else 0
  le_cap u v := by
    by_cases h : u.1.val < d ∧ v.1.val = u.1.val + 1 ∧
        (∀ j : Fin d, j.val ≠ u.1.val → u.2 j = v.2 j)
    · have hstep : IsLayerStep u v := isLayerStep_iff.mpr h
      rw [dite_eq_left_of_eq_true <| eq_true h]
      simp only [separableGridCostNetwork, hstep, ↓reduceIte]
      calc
        (∑ a, ∑ b,
            if layerHybridPoint a b ⟨u.1.val, Nat.lt_succ_of_lt h.1⟩ = u.2 ∧
              layerHybridPoint a b ⟨v.1.val, v.1.isLt⟩ = v.2 then M a b else 0)
          ≤ ∑ a, ∑ b, M a b :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by split_ifs <;> omega
        _ = k := by simp_rw [hM.row_sum, hk]
        _ ≤ k + 1 := Nat.le_succ k
    · rw [dite_eq_right_of_eq_false <| eq_false h]
      exact Nat.zero_le _
  balance_eq x := by
    rcases x with ⟨t, z⟩
    have hout :
        (∑ v : Fin (d + 1) × (Fin d → Fin L),
          ((if h : t.val < d ∧ v.1.val = t.val + 1 ∧
              (∀ j : Fin d, j.val ≠ t.val → z j = v.2 j) then
            ∑ a, ∑ b,
              if layerHybridPoint a b ⟨t.val, Nat.lt_succ_of_lt h.1⟩ = z ∧
                layerHybridPoint a b ⟨v.1.val, v.1.isLt⟩ = v.2 then M a b else 0
          else 0 : ℕ) : ℤ)) =
          if t.val < d then
            ∑ a, ∑ b, if layerHybridPoint a b t = z then (M a b : ℤ) else 0
          else 0 := by
      by_cases ht : t.val < d
      · rw [ite_eq_left ht]
        let s : Fin d := ⟨t.val, ht⟩
        rw [Fintype.sum_prod_type]
        have hlayer : ∀ r : Fin (d + 1),
            (∑ y : Fin d → Fin L,
              ((if h : t.val < d ∧ r.val = t.val + 1 ∧
                  (∀ j : Fin d, j.val ≠ t.val → z j = y j) then
                ∑ a, ∑ b,
                  if layerHybridPoint a b ⟨t.val, Nat.lt_succ_of_lt h.1⟩ = z ∧
                    layerHybridPoint a b ⟨r.val, r.isLt⟩ = y then M a b else 0
              else 0 : ℕ) : ℤ)) =
              if r = s.succ then
                ∑ a, ∑ b, if layerHybridPoint a b t = z then (M a b : ℤ) else 0
              else 0 := by
          intro r
          by_cases hr : r = s.succ
          · subst hr
            rw [ite_eq_left rfl]
            have hpoint : ∀ y : Fin d → Fin L,
                ((if h : t.val < d ∧ s.succ.val = t.val + 1 ∧
                    (∀ j : Fin d, j.val ≠ t.val → z j = y j) then
                  ∑ a, ∑ b,
                    if layerHybridPoint a b ⟨t.val, Nat.lt_succ_of_lt h.1⟩ = z ∧
                      layerHybridPoint a b ⟨s.succ.val, s.succ.isLt⟩ = y then M a b else 0
                else 0 : ℕ) : ℤ) =
                ∑ a, ∑ b,
                  if layerHybridPoint a b s.castSucc = z ∧ layerHybridPoint a b s.succ = y then
                    (M a b : ℤ)
                  else 0 := by
              intro y
              by_cases hj : ∀ j : Fin d, j ≠ s → z j = y j
              · have hcond : t.val < d ∧ s.succ.val = t.val + 1 ∧
                    ∀ j : Fin d, j.val ≠ t.val → z j = y j :=
                  ⟨ht, rfl, fun j hne => hj j fun heq => hne (congrArg Fin.val heq)⟩
                rw [dite_eq_left_of_eq_true <| eq_true hcond, Nat.cast_sum]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Nat.cast_sum]
                refine Finset.sum_congr rfl fun b _ => ?_
                have h1 : (⟨t.val, Nat.lt_succ_of_lt ht⟩ : Fin (d + 1)) = s.castSucc := Fin.ext rfl
                have h2 : (⟨s.succ.val, s.succ.isLt⟩ : Fin (d + 1)) = s.succ := Fin.ext rfl
                rw [h1, h2]
                split_ifs <;> rfl
              · have hnot : ¬(t.val < d ∧ s.succ.val = t.val + 1 ∧
                    ∀ j : Fin d, j.val ≠ t.val → z j = y j) :=
                  fun hc => hj fun j hjs => hc.2.2 j (Fin.val_ne_of_ne hjs)
                rw [dite_eq_right_of_eq_false <| eq_false hnot, Nat.cast_zero]
                symm
                refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
                split_ifs with hab
                · exfalso
                  apply hj
                  intro j hjs
                  rw [← hab.1, ← hab.2, layerHybridPoint_succ, Function.update_of_ne hjs]
                · rfl
            simp_rw [hpoint]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            have ht_cs : s.castSucc = t := Fin.ext rfl
            rw [ht_cs]
            by_cases hz : layerHybridPoint a b t = z
            · simp [hz]
            · simp [hz]
          · rw [ite_eq_right hr]
            refine Finset.sum_eq_zero fun y _ => ?_
            have hnot : ¬(t.val < d ∧ r.val = t.val + 1 ∧
                ∀ j : Fin d, j.val ≠ t.val → z j = y j) := by
              intro hc
              exact hr (Fin.ext hc.2.1)
            simp [hnot]
        simp_rw [hlayer]
        simp
      · rw [ite_eq_right ht]
        refine Finset.sum_eq_zero fun v _ => ?_
        split_ifs with hc
        · exact False.elim (ht hc.1)
        · rfl
    have hin :
        (∑ u : Fin (d + 1) × (Fin d → Fin L),
          ((if h : u.1.val < d ∧ t.val = u.1.val + 1 ∧
              (∀ j : Fin d, j.val ≠ u.1.val → u.2 j = z j) then
            ∑ a, ∑ b,
              if layerHybridPoint a b ⟨u.1.val, Nat.lt_succ_of_lt h.1⟩ = u.2 ∧
                layerHybridPoint a b ⟨t.val, t.isLt⟩ = z then M a b else 0
          else 0 : ℕ) : ℤ)) =
          if 0 < t.val then
            ∑ a, ∑ b, if layerHybridPoint a b t = z then (M a b : ℤ) else 0
          else 0 := by
      by_cases ht0 : 0 < t.val
      · rw [ite_eq_left ht0]
        let s : Fin d := ⟨t.val - 1, by omega⟩
        rw [Fintype.sum_prod_type]
        have hlayer : ∀ r : Fin (d + 1),
            (∑ y : Fin d → Fin L,
              ((if h : r.val < d ∧ t.val = r.val + 1 ∧
                  (∀ j : Fin d, j.val ≠ r.val → y j = z j) then
                ∑ a, ∑ b,
                  if layerHybridPoint a b ⟨r.val, Nat.lt_succ_of_lt h.1⟩ = y ∧
                    layerHybridPoint a b ⟨t.val, t.isLt⟩ = z then M a b else 0
              else 0 : ℕ) : ℤ)) =
              if r = s.castSucc then
                ∑ a, ∑ b, if layerHybridPoint a b t = z then (M a b : ℤ) else 0
              else 0 := by
          intro r
          by_cases hr : r = s.castSucc
          · subst hr
            rw [ite_eq_left rfl]
            have ht_succ : t = s.succ := Fin.ext (by simp [s]; omega)
            have hpoint : ∀ y : Fin d → Fin L,
                ((if h : s.castSucc.val < d ∧ t.val = s.castSucc.val + 1 ∧
                    (∀ j : Fin d, j.val ≠ s.castSucc.val → y j = z j) then
                  ∑ a, ∑ b,
                    if layerHybridPoint a b ⟨s.castSucc.val, Nat.lt_succ_of_lt h.1⟩ = y ∧
                      layerHybridPoint a b ⟨t.val, t.isLt⟩ = z then M a b else 0
                else 0 : ℕ) : ℤ) =
                ∑ a, ∑ b,
                  if layerHybridPoint a b s.castSucc = y ∧ layerHybridPoint a b t = z then
                    (M a b : ℤ)
                  else 0 := by
              intro y
              by_cases hj : ∀ j : Fin d, j ≠ s → y j = z j
              · have hcond : s.castSucc.val < d ∧ t.val = s.castSucc.val + 1 ∧
                    ∀ j : Fin d, j.val ≠ s.castSucc.val → y j = z j :=
                  ⟨s.isLt, by simp [s]; omega,
                    fun j hne => hj j fun heq => hne (by simp [heq])⟩
                rw [dite_eq_left_of_eq_true <| eq_true hcond, Nat.cast_sum]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Nat.cast_sum]
                refine Finset.sum_congr rfl fun b _ => ?_
                have h1 : (⟨s.castSucc.val, Nat.lt_succ_of_lt s.isLt⟩ : Fin (d + 1)) = s.castSucc :=
                  Fin.ext rfl
                rw [h1]
                split_ifs <;> rfl
              · have hnot : ¬(s.castSucc.val < d ∧ t.val = s.castSucc.val + 1 ∧
                    ∀ j : Fin d, j.val ≠ s.castSucc.val → y j = z j) :=
                  fun hc => hj fun j hjs => hc.2.2 j (Fin.val_ne_of_ne hjs)
                rw [dite_eq_right_of_eq_false <| eq_false hnot, Nat.cast_zero]
                symm
                refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
                split_ifs with hab
                · exfalso
                  apply hj
                  intro j hjs
                  rw [← hab.1, ← hab.2, ht_succ, layerHybridPoint_succ, Function.update_of_ne hjs]
                · rfl
            simp_rw [hpoint]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            by_cases hz : layerHybridPoint a b t = z
            · simp [hz]
            · simp [hz]
          · rw [ite_eq_right hr]
            refine Finset.sum_eq_zero fun y _ => ?_
            split_ifs with hc
            · exfalso
              apply hr
              ext
              simp [s]
              omega
            · rfl
        simp_rw [hlayer]
        simp
      · rw [ite_eq_right ht0]
        refine Finset.sum_eq_zero fun u _ => ?_
        split_ifs with hc
        · omega
        · rfl
    change _ - _ =
      (if t = 0 then (p z : ℤ) else 0) - (if t = Fin.last d then (q z : ℤ) else 0)
    rw [hout, hin]
    have hzero_sum : (∑ a, ∑ b, if layerHybridPoint a b 0 = z then (M a b : ℤ) else 0) =
        (p z : ℤ) := by
      simp only [layerHybridPoint_zero]
      have hrow : ∀ a, (∑ b, if a = z then (M a b : ℤ) else 0) =
          if a = z then (p z : ℤ) else 0 := by
        intro a
        by_cases haz : a = z
        · subst haz
          simp only [↓reduceIte, ← Nat.cast_sum, hM.row_sum]
        · simp [haz]
      simp_rw [hrow]
      simp
    have hlast_sum :
        (∑ a, ∑ b, if layerHybridPoint a b (Fin.last d) = z then (M a b : ℤ) else 0) =
        (q z : ℤ) := by
      simp only [layerHybridPoint_last]
      rw [Finset.sum_comm]
      have hcol : ∀ b, (∑ a, if b = z then (M a b : ℤ) else 0) =
          if b = z then (q z : ℤ) else 0 := by
        intro b
        by_cases hbz : b = z
        · subst hbz
          simp only [↓reduceIte, ← Nat.cast_sum, hM.col_sum]
        · simp [hbz]
      simp_rw [hcol]
      simp
    by_cases ht_zero : t = 0
    · subst ht_zero
      by_cases hd0 : d = 0
      · subst hd0
        have hlast0 : (Fin.last 0 : Fin 1) = 0 := rfl
        have hpq : p z = q z := by
          have hp1 : ∑ a : Fin 0 → Fin L, p a = p z :=
            Finset.sum_eq_single (f := p) z
              (fun a _ ha => absurd (Subsingleton.elim a z) ha)
              (fun hz => absurd (Finset.mem_univ z) hz)
          have hq1 : ∑ b : Fin 0 → Fin L, q b = q z :=
            Finset.sum_eq_single (f := q) z
              (fun b _ hb => absurd (Subsingleton.elim b z) hb)
              (fun hz => absurd (Finset.mem_univ z) hz)
          have hsum_eq : ∑ a, p a = ∑ b, q b := by
            simp_rw [← hM.row_sum, ← hM.col_sum]
            exact Finset.sum_comm
          omega
        simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, hlast0, hpq, sub_self]
      · have hpos : (0 : Fin (d + 1)).val < d := Nat.pos_of_ne_zero hd0
        have hn0 : ¬(0 < (0 : Fin (d + 1)).val) := Nat.lt_irrefl 0
        have hne_last : (0 : Fin (d + 1)) ≠ Fin.last d := by
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        rw [ite_eq_left hpos, ite_eq_right hn0, hzero_sum, ite_eq_left rfl,
          ite_eq_right hne_last]
    · have ht_pos : 0 < t.val := Nat.pos_of_ne_zero fun h0 => ht_zero (Fin.ext h0)
      by_cases ht_last : t = Fin.last d
      · subst ht_last
        have hn_lt : ¬((Fin.last d).val < d) := by simp
        rw [ite_eq_right hn_lt, ite_eq_left ht_pos, hlast_sum, ite_eq_right ht_zero,
          ite_eq_left rfl]
      · have ht_lt : t.val < d :=
          lt_of_le_of_ne (Nat.le_of_lt_succ t.isLt) fun heq => ht_last (Fin.ext heq)
        rw [ite_eq_left ht_lt, ite_eq_left ht_pos, sub_self, ite_eq_right ht_zero,
          ite_eq_right ht_last, sub_zero]

/-- Projecting an integral transport plan `M` onto `separableGridCostNetwork` preserves total cost
identically: `(flowOfIntegralPlan coordCost hM hk).totalCost = separablePlanCost coordCost M`. -/
theorem totalCost_flowOfIntegralPlan {d L k : ℕ} {p q : (Fin d → Fin L) → ℕ}
    (coordCost : Fin d → Fin L → Fin L → ℕ)
    {M : (Fin d → Fin L) → (Fin d → Fin L) → ℕ}
    (hM : IsIntegralTransportPlan p q M) (hk : ∑ a, p a = k) :
    (flowOfIntegralPlan coordCost hM hk).totalCost = (separablePlanCost coordCost M : ℤ) := by
  unfold CostNetwork.Flow.totalCost
  rw [Fintype.sum_prod_type]
  have houter : ∀ r : Fin (d + 1),
      (∑ x : Fin d → Fin L, ∑ v : Fin (d + 1) × (Fin d → Fin L),
        (flowOfIntegralPlan coordCost hM hk (r, x) v) •
          (separableGridCostNetwork k p q coordCost).cost (r, x) v) =
        if hr : r.val < d then
          ∑ a, ∑ b, (M a b : ℤ) * (coordCost ⟨r.val, hr⟩ (a ⟨r.val, hr⟩) (b ⟨r.val, hr⟩) : ℤ)
        else 0 := by
    intro r
    by_cases hr : r.val < d
    · rw [dite_eq_left_of_eq_true <| eq_true hr]
      let s : Fin d := ⟨r.val, hr⟩
      change _ = ∑ a, ∑ b, (M a b : ℤ) * (coordCost s (a s) (b s) : ℤ)
      have hr_eq : r = s.castSucc := Fin.ext rfl
      rw [hr_eq]
      have hinner : ∀ x : Fin d → Fin L,
          (∑ v : Fin (d + 1) × (Fin d → Fin L),
            (flowOfIntegralPlan coordCost hM hk (s.castSucc, x) v) •
              (separableGridCostNetwork k p q coordCost).cost (s.castSucc, x) v) =
            ∑ a, ∑ b,
              if layerHybridPoint a b s.castSucc = x then
                (M a b : ℤ) * (coordCost s (a s) (b s) : ℤ)
              else 0 := by
        intro x
        rw [Fintype.sum_prod_type]
        have hv_layer : ∀ t : Fin (d + 1),
            (∑ y : Fin d → Fin L,
              (flowOfIntegralPlan coordCost hM hk (s.castSucc, x) (t, y)) •
                (separableGridCostNetwork k p q coordCost).cost (s.castSucc, x) (t, y)) =
              if t = s.succ then
                ∑ a, ∑ b,
                  if layerHybridPoint a b s.castSucc = x then
                    (M a b : ℤ) * (coordCost s (a s) (b s) : ℤ)
                  else 0
              else 0 := by
          intro t
          by_cases ht : t = s.succ
          · subst ht
            rw [ite_eq_left rfl]
            have hpt : ∀ y : Fin d → Fin L,
                (flowOfIntegralPlan coordCost hM hk (s.castSucc, x) (s.succ, y)) •
                  (separableGridCostNetwork k p q coordCost).cost (s.castSucc, x) (s.succ, y) =
                ∑ a, ∑ b,
                  if layerHybridPoint a b s.castSucc = x ∧ layerHybridPoint a b s.succ = y then
                    (M a b : ℤ) * (coordCost s (a s) (b s) : ℤ)
                  else 0 := by
              intro y
              by_cases hj : ∀ j : Fin d, j ≠ s → x j = y j
              · have hcond : s.castSucc.val < d ∧ s.succ.val = s.castSucc.val + 1 ∧
                    ∀ j : Fin d, j.val ≠ s.castSucc.val → x j = y j :=
                  ⟨s.isLt, rfl, fun j hne => hj j fun heq => hne (by simp [heq])⟩
                have hy_eq : y = Function.update x s (y s) := by
                  funext j
                  by_cases hjs : j = s
                  · subst hjs; simp
                  · rw [Function.update_of_ne hjs, hj j hjs]
                change (flowOfIntegralPlan coordCost hM hk (s.castSucc, x) (s.succ, y) : ℤ) *
                    (separableGridCostNetwork k p q coordCost).cost (s.castSucc, x) (s.succ, y) = _
                have hcost : (separableGridCostNetwork k p q coordCost).cost
                    (s.castSucc, x) (s.succ, y) = (coordCost s (x s) (y s) : ℤ) := by
                  conv_lhs => rw [hy_eq]
                  simp
                rw [hcost]
                dsimp only [flowOfIntegralPlan]
                rw [dite_eq_left_of_eq_true <| eq_true hcond, Nat.cast_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Nat.cast_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun b _ => ?_
                have h1 : (⟨s.castSucc.val, Nat.lt_succ_of_lt s.isLt⟩ : Fin (d + 1)) = s.castSucc :=
                  Fin.ext rfl
                have h2 : (⟨s.succ.val, s.succ.isLt⟩ : Fin (d + 1)) = s.succ := Fin.ext rfl
                rw [h1, h2]
                split_ifs with hab
                · have hxs : x s = a s := by
                    rw [← hab.1]
                    simp [layerHybridPoint]
                  have hys : y s = b s := by
                    rw [← hab.2]
                    simp [layerHybridPoint]
                  rw [hxs, hys]
                · simp
              · have hnot : ¬(s.castSucc.val < d ∧ s.succ.val = s.castSucc.val + 1 ∧
                    ∀ j : Fin d, j.val ≠ s.castSucc.val → x j = y j) :=
                  fun hc => hj fun j hjs => hc.2.2 j (Fin.val_ne_of_ne hjs)
                have hf0 : flowOfIntegralPlan coordCost hM hk (s.castSucc, x) (s.succ, y) = 0 := by
                  dsimp only [flowOfIntegralPlan]
                  rw [dite_eq_right_of_eq_false <| eq_false hnot]
                rw [hf0, zero_smul]
                symm
                refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
                split_ifs with hab
                · exfalso
                  apply hj
                  intro j hjs
                  rw [← hab.1, ← hab.2, layerHybridPoint_succ, Function.update_of_ne hjs]
                · rfl
            simp_rw [hpt]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            by_cases hx : layerHybridPoint a b s.castSucc = x
            · simp [hx]
            · simp [hx]
          · rw [ite_eq_right ht]
            refine Finset.sum_eq_zero fun y _ => ?_
            have hnot : ¬(s.castSucc.val < d ∧ t.val = s.castSucc.val + 1 ∧
                ∀ j : Fin d, j.val ≠ s.castSucc.val → x j = y j) :=
              fun hc => ht (Fin.ext hc.2.1)
            have hf0 : flowOfIntegralPlan coordCost hM hk (s.castSucc, x) (t, y) = 0 := by
              dsimp only [flowOfIntegralPlan]
              rw [dite_eq_right_of_eq_false <| eq_false hnot]
            rw [hf0, zero_smul]
        simp_rw [hv_layer]
        simp
      simp_rw [hinner]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [s]
    · rw [dite_eq_right_of_eq_false <| eq_false hr]
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun v _ => ?_
      have hf0 : flowOfIntegralPlan coordCost hM hk (r, x) v = 0 := by
        dsimp only [flowOfIntegralPlan]
        split_ifs with hc
        · exact False.elim (hr hc.1)
        · rfl
      rw [hf0, zero_smul]
  simp_rw [houter]
  have hsum_fin :
      (∑ r : Fin (d + 1),
        if hr : r.val < d then
          ∑ a, ∑ b, (M a b : ℤ) * (coordCost ⟨r.val, hr⟩ (a ⟨r.val, hr⟩) (b ⟨r.val, hr⟩) : ℤ)
        else 0) =
      ∑ s : Fin d, ∑ a, ∑ b, (M a b : ℤ) * (coordCost s (a s) (b s) : ℤ) := by
    let g : ℕ → ℤ := fun m =>
      if hm : m < d then
        ∑ a, ∑ b, (M a b : ℤ) * (coordCost ⟨m, hm⟩ (a ⟨m, hm⟩) (b ⟨m, hm⟩) : ℤ)
      else 0
    change (∑ r : Fin (d + 1), g r.val) = _
    rw [Fin.sum_univ_eq_sum_range g (d + 1), Finset.sum_range_succ,
      show g d = 0 by simp [g], add_zero, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [g, s.isLt]
  rw [hsum_fin, Finset.sum_comm]
  unfold separablePlanCost separablePairCost
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

/-- Cut-conservation bound: on `separableGridCostNetwork k p q coordCost` with `∑ a, p a = k`,
every feasible flow `f` carries at most `k` units on every directed pair `(u, v)`, hence is
strictly below `cap u v = k + 1` on every valid layer arc. -/
theorem flow_le_supply_on_separableGridCostNetwork {d L k : ℕ} {p q : (Fin d → Fin L) → ℕ}
    {coordCost : Fin d → Fin L → Fin L → ℕ} (hk : ∑ a, p a = k)
    (f : (separableGridCostNetwork k p q coordCost).Flow)
    (u v : Fin (d + 1) × (Fin d → Fin L)) :
    f u v ≤ k := by
  by_cases hstep : IsLayerStep u v
  · obtain ⟨s, hu1, hv1, _⟩ := hstep
    let S : Finset (Fin (d + 1) × (Fin d → Fin L)) :=
      Finset.univ.filter fun w => w.1.val ≤ s.val
    have hbal_sum :
        (∑ w ∈ S, ((∑ z, (f w z : ℤ)) - (∑ z, (f z w : ℤ)))) = (k : ℤ) := by
      simp_rw [f.balance_eq]
      have hS_eq : S =
        (Finset.univ.filter fun t : Fin (d + 1) => t.val ≤ s.val) ×ˢ Finset.univ := by
        ext ⟨t, x⟩
        simp [S]
      rw [hS_eq, Finset.sum_product]
      have hterm : ∀ t : Fin (d + 1), t.val ≤ s.val →
          (∑ x : Fin d → Fin L,
            (separableGridCostNetwork k p q coordCost).balance (t, x)) =
          if t = 0 then (k : ℤ) else 0 := by
        intro t hts
        have hne_last : t ≠ Fin.last d := by
          intro heq
          have hval := congrArg Fin.val heq
          simp at hval
          have := s.isLt
          omega
        by_cases ht0 : t = 0
        · subst ht0
          simp only [separableGridCostNetwork, ↓reduceIte, hne_last, sub_zero, ← Nat.cast_sum, hk]
        · simp [separableGridCostNetwork, ht0, hne_last]
      have hzero_mem : (0 : Fin (d + 1)) ∈
          Finset.univ.filter (fun t : Fin (d + 1) => t.val ≤ s.val) := by
        simp
      rw [Finset.sum_congr rfl fun t ht => hterm t (Finset.mem_filter.mp ht).2]
      simp [Finset.sum_ite_eq', hzero_mem]
    have hzero_nonstep : ∀ w z : Fin (d + 1) × (Fin d → Fin L),
        ¬IsLayerStep w z → f w z = 0 := by
      intro w z hns
      have hle := f.le_cap w z
      simp only [separableGridCostNetwork, hns, ↓reduceIte] at hle
      omega
    have hcut :
        (∑ w ∈ S, ((∑ z, (f w z : ℤ)) - (∑ z, (f z w : ℤ)))) =
          ∑ w ∈ S, ∑ z ∈ Sᶜ, (f w z : ℤ) := by
      rw [Finset.sum_sub_distrib]
      have hsplit1 : (∑ w ∈ S, ∑ z, (f w z : ℤ)) =
          (∑ w ∈ S, ∑ z ∈ S, (f w z : ℤ)) + (∑ w ∈ S, ∑ z ∈ Sᶜ, (f w z : ℤ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_add_sum_compl S]
      have hsplit2 : (∑ w ∈ S, ∑ z, (f z w : ℤ)) =
          (∑ w ∈ S, ∑ z ∈ S, (f z w : ℤ)) + (∑ w ∈ S, ∑ z ∈ Sᶜ, (f z w : ℤ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_add_sum_compl S]
      have hin_zero : ∑ w ∈ S, ∑ z ∈ Sᶜ, (f z w : ℤ) = 0 := by
        refine Finset.sum_eq_zero fun w hw => Finset.sum_eq_zero fun z hz => ?_
        have hw_le : w.1.val ≤ s.val := (Finset.mem_filter.mp hw).2
        have hz_gt : ¬z.1.val ≤ s.val := by simpa [S] using hz
        have hns : ¬IsLayerStep z w := by
          rintro ⟨r, hzr, hwr, _⟩
          have : w.1.val = z.1.val + 1 := by simp [hzr, hwr]
          omega
        simp [hzero_nonstep z w hns]
      have hcomm : (∑ w ∈ S, ∑ z ∈ S, (f z w : ℤ)) = ∑ w ∈ S, ∑ z ∈ S, (f w z : ℤ) :=
        Finset.sum_comm
      rw [hsplit1, hsplit2, hin_zero, add_zero, hcomm]
      ring
    rw [hcut] at hbal_sum
    have hu_mem : u ∈ S := by simp [S, hu1]
    have hv_mem : v ∈ Sᶜ := by simp [S, hv1]
    have hle1 : (f u v : ℤ) ≤ ∑ z ∈ Sᶜ, (f u z : ℤ) :=
      Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hv_mem
    have hle2 : (∑ z ∈ Sᶜ, (f u z : ℤ)) ≤ ∑ w ∈ S, ∑ z ∈ Sᶜ, (f w z : ℤ) :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hu_mem
    have hle_int : (f u v : ℤ) ≤ (k : ℤ) := (hle1.trans hle2).trans hbal_sum.le
    exact_mod_cast hle_int
  · have hle := f.le_cap u v
    simp only [separableGridCostNetwork, hstep, ↓reduceIte] at hle
    omega

/-- **Exact fractional optimality via complementary slackness**: if `f` is a minimum-cost integral
flow on `separableGridCostNetwork k p q coordCost` (`∑ a, p a = k`), then for ANY nonnegative real
matrix `W : (Fin d → Fin L) → (Fin d → Fin L) → ℝ` with row sums `p a` and column sums `q b`,
`(f.totalCost : ℝ) ≤ ∑ a, ∑ b, W a b * separablePairCost coordCost a b`. -/
theorem totalCost_le_realCoupling_of_isMinCost {d L k : ℕ} {p q : (Fin d → Fin L) → ℕ}
    {coordCost : Fin d → Fin L → Fin L → ℕ} (hk : ∑ a, p a = k)
    {f : (separableGridCostNetwork k p q coordCost).Flow} (hf : f.IsMinCost)
    {W : (Fin d → Fin L) → (Fin d → Fin L) → ℝ}
    (hW_nn : ∀ a b, 0 ≤ W a b)
    (hW_row : ∀ a, ∑ b, W a b = (p a : ℝ))
    (hW_col : ∀ b, ∑ a, W a b = (q b : ℝ)) :
    (f.totalCost : ℝ) ≤ ∑ a, ∑ b, W a b * (separablePairCost coordCost a b : ℝ) := by
  let N := separableGridCostNetwork k p q coordCost
  obtain ⟨π, hcs⟩ := (CostNetwork.isMinCost_iff_exists_compSlackness (M := N) (f := f)).mp hf
  -- Every valid single-axis step arc is strictly unsaturated (`f u v ≤ k < k + 1`), so dual
  -- feasibility `0 ≤ cost + π u - π v` holds on every hybrid step!
  have hstep_ineq : ∀ (a b : Fin d → Fin L) (s : Fin d),
      (π (s.succ, layerHybridPoint a b s.succ) : ℝ) -
        (π (s.castSucc, layerHybridPoint a b s.castSucc) : ℝ) ≤
        (coordCost s (a s) (b s) : ℝ) := by
    intro a b s
    let u : Fin (d + 1) × (Fin d → Fin L) := (s.castSucc, layerHybridPoint a b s.castSucc)
    let v : Fin (d + 1) × (Fin d → Fin L) := (s.succ, layerHybridPoint a b s.succ)
    have hv_eq : layerHybridPoint a b s.succ =
        Function.update (layerHybridPoint a b s.castSucc) s (b s) := layerHybridPoint_succ a b s
    have hstep : IsLayerStep u v := by
      refine ⟨s, rfl, rfl, fun j hjs => ?_⟩
      change layerHybridPoint a b s.castSucc j = layerHybridPoint a b s.succ j
      rw [hv_eq, Function.update_of_ne hjs]
    have hcap : N.cap u v = k + 1 := by simp [N, separableGridCostNetwork, hstep]
    have hlt_cap : f u v < N.cap u v := by
      have hle := flow_le_supply_on_separableGridCostNetwork hk f u v
      omega
    have hdual := hcs.1 u v hlt_cap
    have hcost : N.cost u v = (coordCost s (a s) (b s) : ℤ) := by
      have hus : layerHybridPoint a b s.castSucc s = a s := by simp [layerHybridPoint]
      dsimp only [N, u, v]
      rw [hv_eq, separableGridCostNetwork_cost_step, hus]
    rw [hcost] at hdual
    have hreal : (0 : ℝ) ≤ (coordCost s (a s) (b s) : ℝ) + (π u : ℝ) - (π v : ℝ) := by
      exact_mod_cast hdual
    linarith
  have htelescope : ∀ a b : Fin d → Fin L,
      (π (Fin.last d, b) : ℝ) - (π (0, a) : ℝ) ≤ (separablePairCost coordCost a b : ℝ) := by
    intro a b
    have hsum_tel :
        (∑ s : Fin d, ((π (s.succ, layerHybridPoint a b s.succ) : ℝ) -
          (π (s.castSucc, layerHybridPoint a b s.castSucc) : ℝ))) =
        (π (Fin.last d, b) : ℝ) - (π (0, a) : ℝ) := by
      let F : ℕ → ℝ := fun m =>
        if hm : m < d + 1 then (π (⟨m, hm⟩, layerHybridPoint a b ⟨m, hm⟩) : ℝ) else 0
      have hF_step : ∀ s : Fin d,
          (π (s.succ, layerHybridPoint a b s.succ) : ℝ) -
            (π (s.castSucc, layerHybridPoint a b s.castSucc) : ℝ) =
          F (s.val + 1) - F s.val := by
        intro s
        have h1 : s.val + 1 < d + 1 := Nat.succ_lt_succ s.isLt
        have h2 : s.val < d + 1 := Nat.lt_succ_of_lt s.isLt
        have hcs : s.castSucc = ⟨s.val, h2⟩ := Fin.ext rfl
        have hsc : s.succ = ⟨s.val + 1, h1⟩ := Fin.ext rfl
        simp only [F, h1, h2, ↓reduceDIte, hcs, hsc]
      have hsum_eq :
          (∑ s : Fin d, ((π (s.succ, layerHybridPoint a b s.succ) : ℝ) -
            (π (s.castSucc, layerHybridPoint a b s.castSucc) : ℝ))) =
          ∑ m ∈ Finset.range d, (F (m + 1) - F m) := by
        rw [← Fin.sum_univ_eq_sum_range (fun m => F (m + 1) - F m) d]
        exact Finset.sum_congr rfl fun s _ => hF_step s
      rw [hsum_eq, Finset.sum_range_sub F d]
      have hd1 : d < d + 1 := Nat.lt_succ_self d
      have h0 : 0 < d + 1 := Nat.zero_lt_succ d
      have hlast_eq : (⟨d, hd1⟩ : Fin (d + 1)) = Fin.last d := Fin.ext rfl
      have hzero_eq : (⟨0, h0⟩ : Fin (d + 1)) = 0 := Fin.ext rfl
      simp [F, hd1, h0, hlast_eq, hzero_eq, layerHybridPoint_last, layerHybridPoint_zero]
    rw [← hsum_tel]
    unfold separablePairCost
    push_cast
    exact Finset.sum_le_sum fun s _ => hstep_ineq a b s
  -- On `f`, complementary slackness forces `f u v * (cost u v + π u - π v) = 0` on every pair!
  have hf_eq_dual :
      (f.totalCost : ℝ) =
        (∑ b, (q b : ℝ) * (π (Fin.last d, b) : ℝ)) -
          (∑ a, (p a : ℝ) * (π (0, a) : ℝ)) := by
    have hterm_zero : ∀ u v : Fin (d + 1) × (Fin d → Fin L),
        (f u v : ℤ) * (N.cost u v + π u - π v) = 0 := by
      intro u v
      by_cases hf0 : f u v = 0
      · simp [hf0]
      · have hpos : 0 < f u v := Nat.pos_of_ne_zero hf0
        have hle0 := hcs.2 u v hpos
        have hstep : IsLayerStep u v := by
          by_contra hns
          have hcap := f.le_cap u v
          simp only [separableGridCostNetwork, hns, ↓reduceIte] at hcap
          omega
        have hlt_cap : f u v < N.cap u v := by
          have hle := flow_le_supply_on_separableGridCostNetwork hk f u v
          have hcap : N.cap u v = k + 1 := by simp [N, separableGridCostNetwork, hstep]
          omega
        have hge0 := hcs.1 u v hlt_cap
        have heq0 : N.cost u v + π u - π v = 0 := le_antisymm hle0 hge0
        simp [heq0]
    have hsum_zero :
        ∑ u, ∑ v, (f u v : ℤ) * (N.cost u v + π u - π v) = 0 :=
      Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => hterm_zero u v
    have hpot_sum :
        (∑ u, ∑ v, (f u v : ℤ) * (π u - π v)) = ∑ u, N.balance u * π u := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun u v => (f u v : ℤ) * π v), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← sub_mul, f.balance_eq u]
    have hexp :
        (∑ u, ∑ v, (f u v : ℤ) * (N.cost u v + π u - π v)) =
          f.totalCost + ∑ u, N.balance u * π u := by
      have h1 : ∀ u v, (f u v : ℤ) * (N.cost u v + π u - π v) =
          (f u v) • N.cost u v + (f u v : ℤ) * (π u - π v) := by
        intro u v
        simp only [nsmul_eq_mul]
        ring
      simp_rw [h1, Finset.sum_add_distrib]
      rw [hpot_sum]
      rfl
    have hbal_eval :
        ∑ u, N.balance u * π u =
          (∑ a, (p a : ℤ) * π (0, a)) - (∑ b, (q b : ℤ) * π (Fin.last d, b)) := by
      rw [Fintype.sum_prod_type]
      simp only [N, separableGridCostNetwork, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · have h0 : ∀ t : Fin (d + 1),
            (∑ a, (if t = 0 then (p a : ℤ) else 0) * π (t, a)) =
              if t = 0 then ∑ a, (p a : ℤ) * π (0, a) else 0 := by
          intro t
          by_cases ht : t = 0 <;> simp [ht]
        simp_rw [h0]
        simp
      · have hl : ∀ t : Fin (d + 1),
            (∑ b, (if t = Fin.last d then (q b : ℤ) else 0) * π (t, b)) =
              if t = Fin.last d then ∑ b, (q b : ℤ) * π (Fin.last d, b) else 0 := by
          intro t
          by_cases ht : t = Fin.last d <;> simp [ht]
        simp_rw [hl]
        simp
    have hcost_int : f.totalCost =
        (∑ b, (q b : ℤ) * π (Fin.last d, b)) - (∑ a, (p a : ℤ) * π (0, a)) := by
      linarith [hsum_zero, hexp, hbal_eval]
    exact_mod_cast hcost_int
  rw [hf_eq_dual]
  have hW_dual :
      (∑ b, (q b : ℝ) * (π (Fin.last d, b) : ℝ)) - (∑ a, (p a : ℝ) * (π (0, a) : ℝ)) =
        ∑ a, ∑ b, W a b * ((π (Fin.last d, b) : ℝ) - (π (0, a) : ℝ)) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, hW_col b]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_mul, hW_row a]
  rw [hW_dual]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (htelescope a b) (hW_nn a b)

end CslibFrontier.Algorithms.Lean.MaxFlow
