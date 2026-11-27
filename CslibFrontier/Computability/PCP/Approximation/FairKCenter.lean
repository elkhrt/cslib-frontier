/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.KCenter.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.PCP.Approximation.SetCover.ApproxReduction
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.MetricSpace.Isometry

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fair and Forbidden-Center Metric $k$-Center Optimization Problems

General finite-metric optimization theory and multi-tape polynomial-time encodings for constrained
metric $k$-center variants: unconstrained $k$-center, $k$-center with forbidden centers,
exact-quota fair $k$-center, and one-per-group fair $k$-center.

Every real-valued objective bridges directly to `Cslib.Algorithms.Lean.KCenter.centerDist`,
`radius`, and `optRadius`. Encoded rational-metric problem instances `ForbiddenKCenter` and
`FairKCenter` instantiate `Cslib.Complexity.MinOptProblem` for `ApproxPreservingReducible`
inapproximability reductions under `Turing.MultiTapeTM.ComputableInPolyTime`.

## Main definitions

* `CslibFrontier.Complexity.pointCenterDist`, `centerRadius`, `finsetDiam`,
  `minPairDist`: finite-metric covering radius, diameter, and minimum pairwise distance.
* `CslibFrontier.Complexity.FairPartition`: finite disjoint group partition with exact
  per-group center quotas.
* `CslibFrontier.Complexity.kCenterOpt`, `forbiddenCenterOpt`,
  `FairPartition.fairCenterOpt`, `FairPartition.onePerGroupOpt`: optimal covering radii.
* `CslibFrontier.Complexity.RatMetric`, `ForbiddenKCenter`, `FairKCenter`: binary
  multi-tape encoded rational-metric instances and `Cslib.Complexity.MinOptProblem` interfaces.
* `CslibFrontier.Complexity.fairKCenterExactFullAlg`: certified polynomial-time exact
  solver for `k = |U|` fair $k$-center.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Algorithms.Lean.KCenter Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity

/-! ### Metric Covering Objectives -/

section MetricObjectives

variable {U : Type*} [MetricSpace U]

/-- Distance `d(u, S) = min_{s ∈ S} dist u s` from a point `u` to a nonempty finite set `S`. -/
def pointCenterDist (S : Finset U) (hS : S.Nonempty) (u : U) : ℝ :=
  S.inf' hS (dist u)

/-- Exact bridge from `Cslib.Algorithms.Lean.KCenter.centerDist` to `pointCenterDist`. -/
theorem centerDist_eq_coe_pointCenterDist (S : Finset U) (hS : S.Nonempty) (u : U) :
    centerDist dist S u = (pointCenterDist S hS u : WithTop ℝ) := by
  classical
  obtain ⟨s, hs, hmin⟩ := Finset.exists_mem_eq_inf' hS (dist u)
  have h1 : centerDist dist S u ≤ (pointCenterDist S hS u : WithTop ℝ) := by
    rw [pointCenterDist, hmin]
    exact centerDist_le_of_mem hs
  have h2 : (pointCenterDist S hS u : WithTop ℝ) ≤ centerDist dist S u := by
    refine Finset.le_inf fun c hc ↦ ?_
    exact WithTop.coe_le_coe.mpr (Finset.inf'_le (dist u) hc)
  exact le_antisymm h1 h2

/-- `pointCenterDist S hS u` is always nonnegative. -/
theorem pointCenterDist_nonneg (S : Finset U) (hS : S.Nonempty) (u : U) :
    0 ≤ pointCenterDist S hS u :=
  (Finset.le_inf'_iff hS (dist u)).mpr fun _ _ ↦ dist_nonneg

/-- `pointCenterDist S hS u` is at most `dist u s` for every `s ∈ S`. -/
theorem pointCenterDist_le {S : Finset U} (hS : S.Nonempty) {s : U} (hs : s ∈ S) (u : U) :
    pointCenterDist S hS u ≤ dist u s :=
  Finset.inf'_le (dist u) hs

/-- Every point in `S` has distance `0` to `S`. -/
@[simp]
theorem pointCenterDist_eq_zero_of_mem {S : Finset U} (hS : S.Nonempty) {u : U} (hu : u ∈ S) :
    pointCenterDist S hS u = 0 :=
  le_antisymm ((pointCenterDist_le hS hu u).trans (by simp)) (pointCenterDist_nonneg S hS u)

/-- `pointCenterDist` attains its minimum at some center `s ∈ S`. -/
theorem exists_mem_pointCenterDist_eq (S : Finset U) (hS : S.Nonempty) (u : U) :
    ∃ s ∈ S, dist u s = pointCenterDist S hS u := by
  obtain ⟨s, hs, hmin⟩ := Finset.exists_mem_eq_inf' hS (dist u)
  exact ⟨s, hs, hmin.symm⟩

/-- `r ≤ pointCenterDist S hS u` iff every center in `S` is at distance at least `r` from `u`. -/
theorem le_pointCenterDist_iff {S : Finset U} (hS : S.Nonempty) {u : U} {r : ℝ} :
    r ≤ pointCenterDist S hS u ↔ ∀ s ∈ S, r ≤ dist u s :=
  Finset.le_inf'_iff hS (dist u)

/-- `pointCenterDist S hS u ≤ r` iff some center in `S` is within distance `r` of `u`. -/
theorem pointCenterDist_le_iff {S : Finset U} (hS : S.Nonempty) {u : U} {r : ℝ} :
    pointCenterDist S hS u ≤ r ↔ ∃ s ∈ S, dist u s ≤ r :=
  Finset.inf'_le_iff hS

/-- Enlarging the center set does not increase `pointCenterDist`. -/
theorem pointCenterDist_anti {S T : Finset U} (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T)
    (u : U) : pointCenterDist T hT u ≤ pointCenterDist S hS u :=
  (le_pointCenterDist_iff hS).mpr fun _ hs ↦ pointCenterDist_le hT (hST hs) u

variable [Fintype U] [Nonempty U]

/-- The $k$-center objective (covering radius) `max_{u ∈ U} d(u, S)` of a nonempty center set. -/
def centerRadius (S : Finset U) (hS : S.Nonempty) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (pointCenterDist S hS)

/-- Exact bridge from `Cslib.Algorithms.Lean.KCenter.radius` to `centerRadius`. -/
theorem radius_eq_coe_centerRadius (S : Finset U) (hS : S.Nonempty) :
    radius dist S = (centerRadius S hS : WithTop ℝ) := by
  have h1 : radius dist S ≤ (centerRadius S hS : WithTop ℝ) :=
    radius_le_iff.mpr fun v ↦ by
      rw [centerDist_eq_coe_pointCenterDist S hS v, WithTop.coe_le_coe]
      exact Finset.le_sup' (pointCenterDist S hS) (Finset.mem_univ v)
  have h2 : (centerRadius S hS : WithTop ℝ) ≤ radius dist S := by
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (pointCenterDist S hS)
    rw [centerRadius, hv, ← centerDist_eq_coe_pointCenterDist S hS v]
    exact centerDist_le_radius v
  exact le_antisymm h1 h2

/-- `centerRadius S hS` is always nonnegative. -/
theorem centerRadius_nonneg (S : Finset U) (hS : S.Nonempty) : 0 ≤ centerRadius S hS :=
  (pointCenterDist_nonneg S hS (Classical.arbitrary U)).trans
    (Finset.le_sup' (pointCenterDist S hS) (Finset.mem_univ _))

/-- Pointwise bound `pointCenterDist S hS u ≤ centerRadius S hS`. -/
theorem pointCenterDist_le_centerRadius (S : Finset U) (hS : S.Nonempty) (u : U) :
    pointCenterDist S hS u ≤ centerRadius S hS :=
  Finset.le_sup' (pointCenterDist S hS) (Finset.mem_univ u)

/-- `centerRadius S hS ≤ r` iff every point lies within distance `r` of `S`. -/
theorem centerRadius_le_iff {S : Finset U} (hS : S.Nonempty) {r : ℝ} :
    centerRadius S hS ≤ r ↔ ∀ u : U, pointCenterDist S hS u ≤ r := by
  simp only [centerRadius, Finset.sup'_le_iff, Finset.mem_univ, true_implies]

/-- `r ≤ centerRadius S hS` iff some point has distance at least `r` to `S`. -/
theorem le_centerRadius_iff {S : Finset U} (hS : S.Nonempty) {r : ℝ} :
    r ≤ centerRadius S hS ↔ ∃ u : U, r ≤ pointCenterDist S hS u := by
  simp only [centerRadius, Finset.le_sup'_iff, Finset.mem_univ, true_and]

/-- Selecting all points as centers yields radius `0`. -/
@[simp]
theorem centerRadius_univ : centerRadius (Finset.univ : Finset U) Finset.univ_nonempty = 0 :=
  le_antisymm ((centerRadius_le_iff Finset.univ_nonempty).mpr fun u ↦
    (pointCenterDist_eq_zero_of_mem Finset.univ_nonempty (Finset.mem_univ u)).le)
    (centerRadius_nonneg _ _)

end MetricObjectives

section MetricDiameter

/-- Finite metric diameter `D = max_{u, v ∈ U} dist u v`. -/
def finsetDiam (U : Type*) [Fintype U] [Nonempty U] [MetricSpace U] : ℝ :=
  (Finset.univ ×ˢ Finset.univ).sup'
    (Finset.univ_nonempty.product Finset.univ_nonempty) (fun p : U × U ↦ dist p.1 p.2)

variable {U : Type*} [Fintype U] [Nonempty U] [MetricSpace U]

/-- Every pairwise distance is bounded by `finsetDiam U`. -/
theorem dist_le_finsetDiam (u v : U) : dist u v ≤ finsetDiam U := by
  rw [finsetDiam]
  exact Finset.le_sup' (f := fun p : U × U ↦ dist p.1 p.2) (b := (u, v))
    (Finset.mem_product.mpr ⟨Finset.mem_univ u, Finset.mem_univ v⟩)

/-- `finsetDiam U` is nonnegative. -/
theorem finsetDiam_nonneg : 0 ≤ finsetDiam U :=
  dist_nonneg.trans (dist_le_finsetDiam (Classical.arbitrary U) (Classical.arbitrary U))

/-- Every nonempty center set has radius at most `finsetDiam U`. -/
theorem centerRadius_le_finsetDiam (S : Finset U) (hS : S.Nonempty) :
    centerRadius S hS ≤ finsetDiam U :=
  (centerRadius_le_iff hS).mpr fun u ↦ by
    obtain ⟨s, hs⟩ := hS
    exact (pointCenterDist_le ⟨s, hs⟩ hs u).trans (dist_le_finsetDiam u s)

end MetricDiameter

section MinPairDist

/-- Minimum distance `Δ = min_{u ≠ v} dist u v` between distinct points of `U` (returns `0` when
`Fintype.card U ≤ 1`). -/
noncomputable def minPairDist (U : Type*) [Fintype U] [MetricSpace U] : ℝ := by
  classical
  exact if h : ((Finset.univ ×ˢ Finset.univ).filter fun p : U × U ↦ p.1 ≠ p.2).Nonempty then
    ((Finset.univ ×ˢ Finset.univ).filter fun p : U × U ↦ p.1 ≠ p.2).inf' h
      (fun p : U × U ↦ dist p.1 p.2)
  else 0

variable {U : Type*} [Fintype U] [MetricSpace U]

/-- On any finite metric space with at least two points, `minPairDist U` is strictly positive. -/
theorem minPairDist_pos [Nontrivial U] : 0 < minPairDist U := by
  classical
  obtain ⟨u, v, huv⟩ := exists_pair_ne U
  have hne : ((Finset.univ ×ˢ Finset.univ).filter fun p : U × U ↦ p.1 ≠ p.2).Nonempty :=
    ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ u, Finset.mem_univ v⟩,
      huv⟩⟩
  simp only [minPairDist, dite_eq_left hne, Finset.lt_inf'_iff]
  exact fun p hp ↦ dist_pos.mpr (Finset.mem_filter.mp hp).2

/-- Every pair of distinct points satisfies `minPairDist U ≤ dist u v`. -/
theorem minPairDist_le {u v : U} (huv : u ≠ v) : minPairDist U ≤ dist u v := by
  classical
  have hmem : (u, v) ∈ (Finset.univ ×ˢ Finset.univ).filter fun p : U × U ↦ p.1 ≠ p.2 :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ u, Finset.mem_univ v⟩, huv⟩
  have hne : ((Finset.univ ×ˢ Finset.univ).filter fun p : U × U ↦ p.1 ≠ p.2).Nonempty :=
    ⟨(u, v), hmem⟩
  simp only [minPairDist, dite_eq_left hne]
  exact Finset.inf'_le (fun p : U × U ↦ dist p.1 p.2) hmem

end MinPairDist

/-! ### Unconstrained and Forbidden-Center $k$-Center -/

section UnconstrainedDefs

/-- Finite family of subsets of `U` of cardinality `k`. -/
def kCenterFinset (U : Type*) [Fintype U] (k : ℕ) : Finset (Finset U) :=
  Finset.univ.filter fun S : Finset U ↦ S.card = k

theorem kCenterFinset_nonempty {U : Type*} [Fintype U] (k : ℕ) (hk : k ≤ Fintype.card U) :
    (kCenterFinset U k).Nonempty := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset U)) (by simpa)
  exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩⟩

/-- Optimal unconstrained $k$-center radius over sets of exact size `k` (`1 ≤ k ≤ |U|`). -/
def kCenterOpt (U : Type*) [Fintype U] [Nonempty U] [MetricSpace U] (k : ℕ) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ Fintype.card U) : ℝ :=
  (kCenterFinset U k).attach.inf' ((kCenterFinset_nonempty k hk₂).attach) fun S ↦
    centerRadius S.1 (Finset.card_pos.mp (by
      have hcard : S.1.card = k := (Finset.mem_filter.mp S.2).2
      omega))

end UnconstrainedDefs

section UnconstrainedBridge

variable {U : Type*} [Fintype U] [Nonempty U] [MetricSpace U]

/-- Exact bridge between `kCenterOpt` and `Cslib.Algorithms.Lean.KCenter.optRadius`. -/
theorem optRadius_eq_coe_kCenterOpt (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ Fintype.card U) :
    optRadius (V := U) dist k = (kCenterOpt U k hk₁ hk₂ : WithTop ℝ) := by
  obtain ⟨S, hS, hSopt⟩ := exists_card_eq_radius_eq_optRadius (V := U) dist hk₂
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : S ∈ kCenterFinset U k := Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩
  have h1 : (kCenterOpt U k hk₁ hk₂ : WithTop ℝ) ≤ optRadius (V := U) dist k := by
    rw [← hSopt, radius_eq_coe_centerRadius S hSne, WithTop.coe_le_coe]
    exact Finset.inf'_le (f := fun T : {S // S ∈ kCenterFinset U k} ↦
      centerRadius T.1 (Finset.card_pos.mp (by
        have hcard : T.1.card = k := (Finset.mem_filter.mp T.2).2; omega)))
      (Finset.mem_attach _ ⟨S, hmem⟩)
  have h2 : optRadius (V := U) dist k ≤ (kCenterOpt U k hk₁ hk₂ : WithTop ℝ) := by
    obtain ⟨⟨T, hTmem⟩, -, hTmin⟩ := Finset.exists_mem_eq_inf'
      ((kCenterFinset_nonempty k hk₂).attach)
      (fun T : {S // S ∈ kCenterFinset U k} ↦
        centerRadius T.1 (Finset.card_pos.mp (by
          have hcard : T.1.card = k := (Finset.mem_filter.mp T.2).2; omega)))
    have hTcard : T.card = k := (Finset.mem_filter.mp hTmem).2
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    rw [kCenterOpt, hTmin, ← radius_eq_coe_centerRadius T hTne]
    exact optRadius_le_radius hTcard.le
  exact le_antisymm h2 h1

end UnconstrainedBridge

section ForbiddenFinset

/-- Finite family of feasible solutions for $k$-center with forbidden centers. -/
def forbiddenCenterFinset {U : Type*} (A : Finset U) (k : ℕ) : Finset (Finset U) :=
  A.powersetCard k

theorem forbiddenCenterFinset_nonempty {U : Type*} {A : Finset U} {k : ℕ} (hk : k ≤ A.card) :
    (forbiddenCenterFinset A k).Nonempty := by
  obtain ⟨S, hSA, hSk⟩ := Finset.exists_subset_card_eq hk
  exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSA, hSk⟩⟩

end ForbiddenFinset

section ForbiddenOpt

variable {U : Type*} [Fintype U] [Nonempty U] [MetricSpace U]

/-- Feasibility predicate for $k$-center with forbidden centers: `S ⊆ A` and `|S| = k`. -/
@[expose] def IsForbiddenCenterFeasible (A : Finset U) (k : ℕ) (S : Finset U) : Prop :=
  S ⊆ A ∧ S.card = k

/-- Optimal radius for $k$-center with forbidden centers (`A` = allowed centers, `1 ≤ k ≤ |A|`). -/
def forbiddenCenterOpt (A : Finset U) (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ A.card) : ℝ :=
  (forbiddenCenterFinset A k).attach.inf' ((forbiddenCenterFinset_nonempty hk₂).attach) fun S ↦
    centerRadius S.1 (Finset.card_pos.mp (by
      have hcard : S.1.card = k := (Finset.mem_powersetCard.mp S.2).2
      omega))

/-- Every feasible forbidden-center solution has radius at least `forbiddenCenterOpt`. -/
theorem forbiddenCenterOpt_le_radius {A : Finset U} {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ A.card)
    {S : Finset U} (hSA : S ⊆ A) (hSk : S.card = k) :
    forbiddenCenterOpt A k hk₁ hk₂ ≤
      centerRadius S (Finset.card_pos.mp (by omega)) := by
  have hmem : S ∈ forbiddenCenterFinset A k := Finset.mem_powersetCard.mpr ⟨hSA, hSk⟩
  exact Finset.inf'_le (f := fun T : {S // S ∈ forbiddenCenterFinset A k} ↦
    centerRadius T.1 (Finset.card_pos.mp (by
      have hcard : T.1.card = k := (Finset.mem_powersetCard.mp T.2).2; omega)))
    (Finset.mem_attach _ ⟨S, hmem⟩)

/-- Attainment of `forbiddenCenterOpt`. -/
theorem exists_forbiddenCenter_eq_opt (A : Finset U) (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ A.card) :
    ∃ S : Finset U, ∃ hS : S.Nonempty,
      S ⊆ A ∧ S.card = k ∧ centerRadius S hS = forbiddenCenterOpt A k hk₁ hk₂ := by
  obtain ⟨⟨S, hSmem⟩, -, hmin⟩ := Finset.exists_mem_eq_inf'
    ((forbiddenCenterFinset_nonempty hk₂).attach)
    (fun T : {S // S ∈ forbiddenCenterFinset A k} ↦
      centerRadius T.1 (Finset.card_pos.mp (by
        have hcard : T.1.card = k := (Finset.mem_powersetCard.mp T.2).2; omega)))
  obtain ⟨hSA, hSk⟩ := Finset.mem_powersetCard.mp hSmem
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨S, hSne, hSA, hSk, hmin.symm⟩

/-- `forbiddenCenterOpt` is nonnegative. -/
theorem forbiddenCenterOpt_nonneg (A : Finset U) (k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ A.card) :
    0 ≤ forbiddenCenterOpt A k hk₁ hk₂ := by
  obtain ⟨S, hS, -, -, hopt⟩ := exists_forbiddenCenter_eq_opt A k hk₁ hk₂
  exact hopt ▸ centerRadius_nonneg S hS

/-- Unconstrained $k$-center is a relaxation of forbidden-center $k$-center. -/
theorem kCenterOpt_le_forbiddenCenterOpt (A : Finset U) (k : ℕ) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ A.card) :
    kCenterOpt U k hk₁ (hk₂.trans (Finset.card_le_univ A)) ≤
      forbiddenCenterOpt A k hk₁ hk₂ := by
  obtain ⟨S, hS, -, hSk, hopt⟩ := exists_forbiddenCenter_eq_opt A k hk₁ hk₂
  rw [← hopt]
  have hmem : S ∈ kCenterFinset U k := Finset.mem_filter.mpr ⟨Finset.mem_univ S, hSk⟩
  exact Finset.inf'_le (f := fun T : {S // S ∈ kCenterFinset U k} ↦
    centerRadius T.1 (Finset.card_pos.mp (by
      have hcard : T.1.card = k := (Finset.mem_filter.mp T.2).2; omega)))
    (Finset.mem_attach _ ⟨S, hmem⟩)

/-- Packing-based $3$-approximation lemma: if `r ≥ forbiddenCenterOpt A k`, and `M` is a list of
points with assigned centers `c : U → U` such that `dist u (c u) ≤ r` and every later point in `M`
has distance strictly greater than `3 * r` from all earlier assigned centers, then
`M.length ≤ k`. -/
theorem length_le_of_forbidden_greedy_packing {A : Finset U} {k : ℕ} (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ A.card) {r : ℝ} (hr : forbiddenCenterOpt A k hk₁ hk₂ ≤ r)
    {M : List U} {c : U → U} (hcov : ∀ u ∈ M, dist u (c u) ≤ r)
    (hsep : M.Pairwise fun u v ↦ 3 * r < dist v (c u)) :
    M.length ≤ k := by
  obtain ⟨Sstar, hSstar, -, hSk, hSopt⟩ := exists_forbiddenCenter_eq_opt A k hk₁ hk₂
  have hrad : centerRadius Sstar hSstar ≤ r := by rw [hSopt]; exact hr
  have hSstar_rad : ∀ v : U, ∃ s ∈ Sstar, dist v s ≤ r := fun v ↦
    (pointCenterDist_le_iff hSstar).mp
      ((pointCenterDist_le_centerRadius Sstar hSstar v).trans hrad)
  have hpair : M.Pairwise fun a b ↦ 2 * r < dist a b := by
    refine hsep.imp_of_mem fun {u v} hu _ hgt ↦ ?_
    have htri : dist v (c u) ≤ dist v u + dist u (c u) := dist_triangle v u (c u)
    have hcu := hcov u hu
    rw [dist_comm v u] at htri
    linarith
  have hlen := length_le_card_of_pairwise_lt dist_comm dist_triangle
    (fun v _ ↦ hSstar_rad v) hpair
  exact hlen.trans hSk.le

end ForbiddenOpt

/-! ### Fair $k$-Center and One-Per-Group Fair $k$-Center -/

section FairPartitionDef

/-- A finite disjoint partition of `U` into `t` demographic groups with exact per-group center
requirements `req : Fin t → ℕ`. -/
@[ext]
structure FairPartition (U : Type*) [Fintype U] (t : ℕ) where
  /-- Group assignment of each point. -/
  group : U → Fin t
  /-- Required number of centers from each group. -/
  req : Fin t → ℕ

namespace FairPartition

variable {U : Type*} [Fintype U]

/-- The finite set of points belonging to group `g`. -/
def groupSet {t : ℕ} (P : FairPartition U t) (g : Fin t) : Finset U :=
  Finset.univ.filter fun u ↦ P.group u = g

/-- Membership characterization of `FairPartition.groupSet`. -/
@[simp]
theorem mem_groupSet {t : ℕ} (P : FairPartition U t) (g : Fin t) (u : U) :
    u ∈ P.groupSet g ↔ P.group u = g := by
  simp only [groupSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Total number of centers required across all groups. -/
@[expose] def totalReq {t : ℕ} (P : FairPartition U t) : ℕ :=
  ∑ g : Fin t, P.req g

/-- Feasibility of the fair partition itself: every group has at least `P.req g` points and the
total requirement equals `k`. -/
@[expose] def IsFeasible {t : ℕ} (P : FairPartition U t) (k : ℕ) : Prop :=
  1 ≤ k ∧ P.totalReq = k ∧ ∀ g : Fin t, P.req g ≤ (P.groupSet g).card

/-- Feasibility of a center set `S` under exact-quota fair constraints. -/
@[expose] def IsFairCenterFeasible {t : ℕ} (P : FairPartition U t) (S : Finset U) : Prop :=
  ∀ g : Fin t, (S.filter fun u ↦ P.group u = g).card = P.req g

/-- Bridge between `S.filter (fun u ↦ P.group u = g)` and `S ∩ P.groupSet g`. -/
theorem filter_group_eq_inter_groupSet [DecidableEq U] {t : ℕ} (P : FairPartition U t)
    (S : Finset U) (g : Fin t) :
    (S.filter fun u ↦ P.group u = g) = S ∩ P.groupSet g := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_inter, mem_groupSet]

/-- Characterization of `IsFairCenterFeasible` via `S ∩ P.groupSet g`. -/
theorem isFairCenterFeasible_iff_inter [DecidableEq U] {t : ℕ} (P : FairPartition U t)
    (S : Finset U) :
    P.IsFairCenterFeasible S ↔ ∀ g : Fin t, (S ∩ P.groupSet g).card = P.req g := by
  simp only [IsFairCenterFeasible, filter_group_eq_inter_groupSet]

/-- Feasibility predicate for one-per-group fair $k$-center (`P.req g = 1` for every `g`). -/
@[expose] def IsOnePerGroup {t : ℕ} (P : FairPartition U t) : Prop :=
  ∀ g : Fin t, P.req g = 1

/-- Every fair-feasible center set has total cardinality `P.totalReq`. -/
theorem card_eq_totalReq_of_isFairCenterFeasible {t : ℕ} {P : FairPartition U t} {S : Finset U}
    (hS : P.IsFairCenterFeasible S) : S.card = P.totalReq := by
  classical
  have hpart :
      (Finset.univ.biUnion fun g : Fin t ↦ S ∩ P.groupSet g) = S := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter, mem_groupSet]
    exact ⟨fun ⟨_, hu, _⟩ ↦ hu, fun hu ↦ ⟨P.group u, hu, rfl⟩⟩
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin t))
      (fun g ↦ S ∩ P.groupSet g) := by
    intro g₁ _ g₂ _ hne
    change Disjoint (S ∩ P.groupSet g₁) (S ∩ P.groupSet g₂)
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    have hg₁ : P.group u = g₁ := (mem_groupSet P g₁ u).mp (Finset.mem_inter.mp hu₁).2
    have hg₂ : P.group u = g₂ := (mem_groupSet P g₂ u).mp (Finset.mem_inter.mp hu₂).2
    exact hne (hg₁.symm.trans hg₂)
  rw [← hpart, Finset.card_biUnion hdisj, totalReq]
  exact Finset.sum_congr rfl fun g _ ↦ (isFairCenterFeasible_iff_inter P S).mp hS g

/-- Finite family of all fair-feasible center sets for partition `P`. -/
noncomputable def fairCenterFinset {t : ℕ} (P : FairPartition U t) : Finset (Finset U) := by
  classical
  exact Finset.univ.filter fun S : Finset U ↦ ∀ g : Fin t,
    (S.filter fun u ↦ P.group u = g).card = P.req g

theorem fairCenterFinset_nonempty {t : ℕ} {P : FairPartition U t} {k : ℕ}
    (hP : P.IsFeasible k) : (P.fairCenterFinset).Nonempty := by
  classical
  have hsub : ∀ g : Fin t, ∃ Sg : Finset U, Sg ⊆ P.groupSet g ∧ Sg.card = P.req g :=
    fun g ↦ Finset.exists_subset_card_eq (hP.2.2 g)
  choose Sg hSg_sub hSg_card using hsub
  refine ⟨Finset.univ.biUnion Sg, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun g ↦ ?_⟩⟩
  rw [filter_group_eq_inter_groupSet]
  have hdisj : ∀ g₁ g₂ : Fin t, g₁ ≠ g₂ → Disjoint (Sg g₁) (P.groupSet g₂) := by
    intro g₁ g₂ hne
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    have hg₁ : P.group u = g₁ := (mem_groupSet P g₁ u).mp (hSg_sub g₁ hu₁)
    have hg₂ : P.group u = g₂ := (mem_groupSet P g₂ u).mp hu₂
    exact hne (hg₁.symm.trans hg₂)
  have hinter : (Finset.univ.biUnion Sg) ∩ P.groupSet g = Sg g := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨g', hu'⟩, hug⟩
      by_cases hgg : g' = g
      · exact hgg ▸ hu'
      · exact absurd hug (Finset.disjoint_left.mp (hdisj g' g hgg) hu')
    · intro hu
      exact ⟨⟨g, hu⟩, hSg_sub g hu⟩
  rw [hinter, hSg_card g]

end FairPartition

end FairPartitionDef

section FairOpt

variable {U : Type*} [Fintype U] [Nonempty U] [MetricSpace U]

namespace FairPartition

/-- Optimal fair $k$-center radius for partition `P` (`P.IsFeasible k`). -/
noncomputable def fairCenterOpt {t : ℕ} (P : FairPartition U t) {k : ℕ}
    (hP : P.IsFeasible k) : ℝ :=
  (P.fairCenterFinset).attach.inf' ((fairCenterFinset_nonempty hP).attach) fun S ↦
    centerRadius S.1 (Finset.card_pos.mp (by
      classical
      have hfeas : P.IsFairCenterFeasible S.1 := (Finset.mem_filter.mp S.2).2
      rw [card_eq_totalReq_of_isFairCenterFeasible hfeas, hP.2.1]
      exact hP.1))

/-- Every fair-feasible solution has radius at least `P.fairCenterOpt hP`. -/
theorem fairCenterOpt_le_radius {t : ℕ} (P : FairPartition U t) {k : ℕ} (hP : P.IsFeasible k)
    {S : Finset U} (hS : P.IsFairCenterFeasible S) :
    P.fairCenterOpt hP ≤
      centerRadius S (Finset.card_pos.mp (by
        rw [card_eq_totalReq_of_isFairCenterFeasible hS, hP.2.1]; exact hP.1)) := by
  classical
  have hmem : S ∈ P.fairCenterFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩
  exact Finset.inf'_le (f := fun T : {S // S ∈ P.fairCenterFinset} ↦
    centerRadius T.1 (Finset.card_pos.mp (by
      have hfeas : P.IsFairCenterFeasible T.1 := (Finset.mem_filter.mp T.2).2
      rw [card_eq_totalReq_of_isFairCenterFeasible hfeas, hP.2.1]; exact hP.1)))
    (Finset.mem_attach _ ⟨S, hmem⟩)

/-- Attainment of `fairCenterOpt`. -/
theorem exists_fairCenter_eq_opt {t : ℕ} (P : FairPartition U t) {k : ℕ} (hP : P.IsFeasible k) :
    ∃ S : Finset U, ∃ hS : S.Nonempty,
      P.IsFairCenterFeasible S ∧ centerRadius S hS = P.fairCenterOpt hP := by
  classical
  obtain ⟨⟨S, hSmem⟩, -, hmin⟩ := Finset.exists_mem_eq_inf'
    ((fairCenterFinset_nonempty hP).attach)
    (fun T : {S // S ∈ P.fairCenterFinset} ↦
      centerRadius T.1 (Finset.card_pos.mp (by
        have hfeas : P.IsFairCenterFeasible T.1 := (Finset.mem_filter.mp T.2).2
        rw [card_eq_totalReq_of_isFairCenterFeasible hfeas, hP.2.1]; exact hP.1)))
  have hSfeas : P.IsFairCenterFeasible S := (Finset.mem_filter.mp hSmem).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by
    rw [card_eq_totalReq_of_isFairCenterFeasible hSfeas, hP.2.1]; exact hP.1)
  exact ⟨S, hSne, hSfeas, hmin.symm⟩

/-- `P.fairCenterOpt hP` is nonnegative. -/
theorem fairCenterOpt_nonneg {t : ℕ} (P : FairPartition U t) {k : ℕ} (hP : P.IsFeasible k) :
    0 ≤ P.fairCenterOpt hP := by
  obtain ⟨S, hS, -, hopt⟩ := exists_fairCenter_eq_opt P hP
  exact hopt ▸ centerRadius_nonneg S hS

/-- Optimal one-per-group fair $k$-center radius (specialization of `fairCenterOpt` when `t = k`
and `P.req = fun _ ↦ 1`). -/
noncomputable def onePerGroupOpt {k : ℕ} (P : FairPartition U k) (hP : P.IsFeasible k) : ℝ :=
  P.fairCenterOpt hP

/-- Unconstrained $k$-center is a relaxation of fair $k$-center. -/
theorem kCenterOpt_le_fairCenterOpt {t : ℕ} (P : FairPartition U t) {k : ℕ} (hP : P.IsFeasible k) :
    kCenterOpt U k hP.1 (by
      obtain ⟨S, -, hSfeas, -⟩ := exists_fairCenter_eq_opt P hP
      have hcard := card_eq_totalReq_of_isFairCenterFeasible hSfeas
      rw [hP.2.1] at hcard
      exact hcard ▸ Finset.card_le_univ S) ≤ P.fairCenterOpt hP := by
  obtain ⟨S, hS, hSfeas, hopt⟩ := exists_fairCenter_eq_opt P hP
  have hSk : S.card = k := (card_eq_totalReq_of_isFairCenterFeasible hSfeas).trans hP.2.1
  rw [← hopt]
  have hmem : S ∈ kCenterFinset U k := Finset.mem_filter.mpr ⟨Finset.mem_univ S, hSk⟩
  exact Finset.inf'_le (f := fun T : {S // S ∈ kCenterFinset U k} ↦
    centerRadius T.1 (Finset.card_pos.mp (by
      have hcard : T.1.card = k := (Finset.mem_filter.mp T.2).2
      have hk₁ : 1 ≤ k := hP.1
      omega)))
    (Finset.mem_attach _ ⟨S, hmem⟩)

/-- Forbidden-center $k$-center with allowed set `A` equals two-group fair $k$-center with
requirements `(k, 0)` on `(A, U \ A)`. -/
theorem forbiddenCenterOpt_eq_fairCenterOpt_zero (A : Finset U) (k : ℕ) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ A.card) :
    let P : FairPartition U 2 := by
      classical
      exact { group := fun u ↦ if u ∈ A then 0 else 1, req := ![k, 0] }
    have hP : P.IsFeasible k := by
      classical
      refine ⟨hk₁, ?_, fun g ↦ ?_⟩
      · simp [FairPartition.totalReq, Fin.sum_univ_two, P]
      · fin_cases g
        · have hgs : P.groupSet 0 = A := by
            ext u
            simp [FairPartition.mem_groupSet, P]
          simpa [P, hgs] using hk₂
        · exact Nat.zero_le _
    forbiddenCenterOpt A k hk₁ hk₂ = P.fairCenterOpt hP := by
  classical
  intro P hP
  apply le_antisymm
  · obtain ⟨S, hS, hSfeas, hopt⟩ := exists_fairCenter_eq_opt P hP
    rw [← hopt]
    have hSA : S ⊆ A := by
      intro u hu
      by_contra huA
      have hmem : u ∈ S ∩ P.groupSet 1 :=
        Finset.mem_inter.mpr ⟨hu, (mem_groupSet P 1 u).mpr (by simp [P, huA])⟩
      have hcard0 : (S ∩ P.groupSet 1).card = 0 :=
        (isFairCenterFeasible_iff_inter P S).mp hSfeas 1
      exact absurd (Finset.card_pos.mpr ⟨u, hmem⟩) (by omega)
    have hSk : S.card = k := (card_eq_totalReq_of_isFairCenterFeasible hSfeas).trans hP.2.1
    exact forbiddenCenterOpt_le_radius hk₁ hk₂ hSA hSk
  · obtain ⟨S, hS, hSA, hSk, hopt⟩ := exists_forbiddenCenter_eq_opt A k hk₁ hk₂
    rw [← hopt]
    refine fairCenterOpt_le_radius P hP ((isFairCenterFeasible_iff_inter P S).mpr fun g ↦ ?_)
    fin_cases g
    · have hinter : S ∩ P.groupSet 0 = S := by
        ext u
        simp only [Finset.mem_inter, mem_groupSet, P]
        exact ⟨fun h ↦ h.1, fun hu ↦ ⟨hu, by simp [hSA hu]⟩⟩
      simpa [P, hinter] using hSk
    · have hinter : S ∩ P.groupSet 1 = ∅ := by
        ext u
        simp only [Finset.mem_inter, mem_groupSet, Finset.notMem_empty, iff_false, not_and, P]
        intro hu
        simp [hSA hu]
      simp [P, hinter]

end FairPartition

end FairOpt

/-! ### Invariance Under Bijective Isometries -/

section IsometryPoint

variable {U V : Type*} [MetricSpace U] [MetricSpace V]

/-- `pointCenterDist` is preserved by any bijective isometry `e : U ≃ᵢ V`. -/
theorem isometry_pointCenterDist_eq (e : U ≃ᵢ V) (S : Finset U) (hS : S.Nonempty) (u : U) :
    pointCenterDist (S.map e.toEquiv.toEmbedding) hS.map (e u) =
      pointCenterDist S hS u := by
  classical
  simp only [pointCenterDist, Finset.inf'_map, Function.comp_def, Equiv.coe_toEmbedding,
    IsometryEquiv.coe_toEquiv, e.dist_eq]

end IsometryPoint

section Isometry

variable {U V : Type*} [Fintype U] [Nonempty U] [MetricSpace U]
variable [Fintype V] [Nonempty V] [MetricSpace V]

/-- `centerRadius` is preserved by any bijective isometry `e : U ≃ᵢ V`. -/
theorem isometry_centerRadius_eq (e : U ≃ᵢ V) (S : Finset U) (hS : S.Nonempty) :
    centerRadius (S.map e.toEquiv.toEmbedding) hS.map = centerRadius S hS := by
  apply le_antisymm
  · refine (centerRadius_le_iff hS.map).mpr fun v ↦ ?_
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [isometry_pointCenterDist_eq]
    exact pointCenterDist_le_centerRadius S hS u
  · refine (centerRadius_le_iff hS).mpr fun u ↦ ?_
    rw [← isometry_pointCenterDist_eq e S hS u]
    exact pointCenterDist_le_centerRadius _ _ (e u)

/-- `forbiddenCenterOpt` is invariant under bijective isometries. -/
theorem isometry_forbiddenCenterOpt_eq (e : U ≃ᵢ V) (A : Finset U) (k : ℕ) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ A.card) :
    forbiddenCenterOpt (A.map e.toEquiv.toEmbedding) k hk₁
      (by simpa [Finset.card_map] using hk₂) = forbiddenCenterOpt A k hk₁ hk₂ := by
  apply le_antisymm
  · obtain ⟨S, hS, hSA, hSk, hopt⟩ := exists_forbiddenCenter_eq_opt A k hk₁ hk₂
    rw [← hopt, ← isometry_centerRadius_eq e S hS]
    exact forbiddenCenterOpt_le_radius hk₁ (by simpa [Finset.card_map] using hk₂)
      (Finset.map_subset_map.mpr hSA) (by simpa [Finset.card_map] using hSk)
  · obtain ⟨T, hT, hTA, hTk, hopt⟩ :=
      exists_forbiddenCenter_eq_opt (A.map e.toEquiv.toEmbedding) k hk₁
        (by simpa [Finset.card_map] using hk₂)
    let S : Finset U := T.map e.symm.toEquiv.toEmbedding
    have hST : S.map e.toEquiv.toEmbedding = T := by
      ext v
      simp only [S, Finset.mem_map, Equiv.coe_toEmbedding, IsometryEquiv.coe_toEquiv]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; simpa using hw
      · intro hv; exact ⟨e.symm v, ⟨v, hv, rfl⟩, by simp⟩
    have hSA : S ⊆ A := by
      intro u hu
      obtain ⟨v, hvT, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨a, haA, hav⟩ := Finset.mem_map.mp (hTA hvT)
      have : a = e.symm v := by
        apply e.injective
        simpa using hav
      exact this ▸ haA
    have hSk : S.card = k := by simpa [S, Finset.card_map] using hTk
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hrad_eq : centerRadius T hT = centerRadius S hSne := by
      simpa only [hST] using isometry_centerRadius_eq e S hSne
    rw [← hopt, hrad_eq]
    exact forbiddenCenterOpt_le_radius hk₁ hk₂ hSA hSk

/-- `fairCenterOpt` is invariant under bijective isometries transporting the group partition. -/
theorem isometry_fairCenterOpt_eq {t : ℕ} (e : U ≃ᵢ V) (P : FairPartition U t) {k : ℕ}
    (hP : P.IsFeasible k) :
    let Q : FairPartition V t := { group := fun v ↦ P.group (e.symm v), req := P.req }
    have hQ : Q.IsFeasible k := by
      refine ⟨hP.1, hP.2.1, fun g ↦ ?_⟩
      have hmap : Q.groupSet g = (P.groupSet g).map e.toEquiv.toEmbedding := by
        ext v
        simp only [FairPartition.mem_groupSet, Finset.mem_map, Equiv.coe_toEmbedding,
          IsometryEquiv.coe_toEquiv, Q]
        exact ⟨fun hv ↦ ⟨e.symm v, hv, by simp⟩, fun ⟨u, hu, huv⟩ ↦ by subst huv; simpa using hu⟩
      simpa [hmap, Finset.card_map] using hP.2.2 g
    Q.fairCenterOpt hQ = P.fairCenterOpt hP := by
  classical
  intro Q hQ
  have hgroup : ∀ g : Fin t, Q.groupSet g = (P.groupSet g).map e.toEquiv.toEmbedding := by
    intro g
    ext v
    simp only [FairPartition.mem_groupSet, Finset.mem_map, Equiv.coe_toEmbedding,
      IsometryEquiv.coe_toEquiv, Q]
    exact ⟨fun hv ↦ ⟨e.symm v, hv, by simp⟩, fun ⟨u, hu, huv⟩ ↦ by subst huv; simpa using hu⟩
  apply le_antisymm
  · obtain ⟨S, hS, hSfeas, hopt⟩ := FairPartition.exists_fairCenter_eq_opt P hP
    rw [← hopt, ← isometry_centerRadius_eq e S hS]
    refine FairPartition.fairCenterOpt_le_radius Q hQ
      ((FairPartition.isFairCenterFeasible_iff_inter Q _).mpr fun g ↦ ?_)
    rw [hgroup g, ← Finset.map_inter, Finset.card_map]
    exact (FairPartition.isFairCenterFeasible_iff_inter P S).mp hSfeas g
  · obtain ⟨T, hT, hTfeas, hopt⟩ := FairPartition.exists_fairCenter_eq_opt Q hQ
    let S : Finset U := T.map e.symm.toEquiv.toEmbedding
    have hST : S.map e.toEquiv.toEmbedding = T := by
      ext v
      simp only [S, Finset.mem_map, Equiv.coe_toEmbedding, IsometryEquiv.coe_toEquiv]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; simpa using hw
      · intro hv; exact ⟨e.symm v, ⟨v, hv, rfl⟩, by simp⟩
    have hSfeas : P.IsFairCenterFeasible S :=
      (FairPartition.isFairCenterFeasible_iff_inter P S).mpr fun g ↦ by
        have hcard : ((S.map e.toEquiv.toEmbedding) ∩ Q.groupSet g).card =
            (S ∩ P.groupSet g).card := by
          rw [hgroup g, ← Finset.map_inter, Finset.card_map]
        rw [← hcard, hST]
        exact (FairPartition.isFairCenterFeasible_iff_inter Q T).mp hTfeas g
    have hSne : S.Nonempty := Finset.card_pos.mp (by
      rw [FairPartition.card_eq_totalReq_of_isFairCenterFeasible hSfeas, hP.2.1]; exact hP.1)
    have hrad_eq : centerRadius T hT = centerRadius S hSne := by
      simpa only [hST] using isometry_centerRadius_eq e S hSne
    rw [← hopt, hrad_eq]
    exact FairPartition.fairCenterOpt_le_radius P hP hSfeas

end Isometry

/-! ### Rational Distance Matrices and `RatMetric` -/

namespace RatDistMatrix

/-- Entry `(i, j)` of a rational distance matrix, defaulting to `0` out of range. -/
def getDist (D : List (List ℚ)) (i j : ℕ) : ℚ :=
  (D.getD i []).getD j 0

/-- Expansion of `getDist` as nested `List.getD`. -/
theorem getDist_eq_getD (D : List (List ℚ)) (i j : ℕ) :
    getDist D i j = (D.getD i []).getD j 0 := by rfl

/-- A list-of-lists rational distance matrix `D` is a finite metric on `Fin D.length` when it is
nonempty, square, definite (`d(i, j) = 0 ↔ i = j`), symmetric, and satisfies the triangle
inequality. -/
structure IsMetric (D : List (List ℚ)) : Prop where
  /-- The underlying finite point set is nonempty. -/
  nonempty : 0 < D.length
  /-- Every row has length `D.length`. -/
  length_row : ∀ row ∈ D, row.length = D.length
  /-- Distance vanishes precisely on the diagonal. -/
  eq_zero_iff : ∀ i < D.length, ∀ j < D.length, getDist D i j = 0 ↔ i = j
  /-- Distances are symmetric. -/
  symm : ∀ i < D.length, ∀ j < D.length, getDist D i j = getDist D j i
  /-- Distances satisfy the triangle inequality. -/
  triangle : ∀ i < D.length, ∀ j < D.length, ∀ l < D.length,
    getDist D i l ≤ getDist D i j + getDist D j l

/-- Diagonal entries of a metric matrix vanish. -/
theorem IsMetric.dist_self {D : List (List ℚ)} (hD : IsMetric D) {i : ℕ} (hi : i < D.length) :
    getDist D i i = 0 :=
  (hD.eq_zero_iff i hi i hi).mpr rfl

/-- Entries of a metric matrix are nonnegative. -/
theorem IsMetric.nonneg {D : List (List ℚ)} (hD : IsMetric D) {i j : ℕ} (hi : i < D.length)
    (hj : j < D.length) : 0 ≤ getDist D i j := by
  have h1 := hD.triangle i hi j hj i hi
  rw [hD.dist_self hi, hD.symm j hj i hi] at h1
  linarith

end RatDistMatrix

/-- A finite rational metric space represented by its `n × n` rational distance matrix. -/
@[ext]
structure RatMetric where
  /-- Rational distance matrix of size `n × n`. -/
  dist : List (List ℚ)
  /-- Proof that `dist` is a genuine finite metric. -/
  isMetric : RatDistMatrix.IsMetric dist

namespace RatMetric

/-- Number of points in a `RatMetric`. -/
abbrev n (M : RatMetric) : ℕ := M.dist.length

/-- Every `RatMetric` has at least one point. -/
theorem n_pos (M : RatMetric) : 0 < M.n := M.isMetric.nonempty

end RatMetric

/-- Vertex type of a `RatMetric`, carrying its canonical finite `MetricSpace` structure. -/
@[ext]
structure RatMetricVertex (M : RatMetric) where
  /-- Underlying `Fin M.n` index. -/
  val : Fin M.n
  deriving DecidableEq

namespace RatMetricVertex

/-- Equivalence between `RatMetricVertex M` and `Fin M.n`. -/
def equivFin (M : RatMetric) : RatMetricVertex M ≃ Fin M.n where
  toFun := RatMetricVertex.val
  invFun := RatMetricVertex.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintype (M : RatMetric) : Fintype (RatMetricVertex M) :=
  Fintype.ofEquiv (Fin M.n) (equivFin M).symm

instance instNonempty (M : RatMetric) : Nonempty (RatMetricVertex M) :=
  ⟨⟨⟨0, M.n_pos⟩⟩⟩

/-- Cardinality of `RatMetricVertex M` equals `M.n`. -/
@[simp]
theorem card_eq (M : RatMetric) : Fintype.card (RatMetricVertex M) = M.n := by
  rw [Fintype.card_congr (equivFin M), Fintype.card_fin]

instance instMetricSpace (M : RatMetric) : MetricSpace (RatMetricVertex M) where
  dist u v := (RatDistMatrix.getDist M.dist u.val.1 v.val.1 : ℝ)
  dist_self u := by exact_mod_cast M.isMetric.dist_self u.val.2
  dist_comm u v := by exact_mod_cast M.isMetric.symm u.val.1 u.val.2 v.val.1 v.val.2
  dist_triangle u v w := by
    exact_mod_cast M.isMetric.triangle u.val.1 u.val.2 v.val.1 v.val.2 w.val.1 w.val.2
  eq_of_dist_eq_zero {u v} h := by
    have hq : RatDistMatrix.getDist M.dist u.val.1 v.val.1 = 0 := by exact_mod_cast h
    have hval : u.val.1 = v.val.1 :=
      (M.isMetric.eq_zero_iff u.val.1 u.val.2 v.val.1 v.val.2).mp hq
    exact RatMetricVertex.ext (Fin.ext hval)

/-- Real distance on `RatMetricVertex M` equals the cast of the rational matrix entry. -/
theorem dist_eq (M : RatMetric) (u v : RatMetricVertex M) :
    dist u v = (RatDistMatrix.getDist M.dist u.val.1 v.val.1 : ℝ) := by rfl

end RatMetricVertex

/-- Center finset of `RatMetricVertex M` selected by a list of raw indices `l : List ℕ`. -/
def centersOfList (M : RatMetric) (l : List ℕ) : Finset (RatMetricVertex M) :=
  Finset.univ.filter fun u : RatMetricVertex M ↦ u.val.1 ∈ l

/-- Membership characterization for `centersOfList`. -/
theorem mem_centersOfList {M : RatMetric} {l : List ℕ} {u : RatMetricVertex M} :
    u ∈ centersOfList M l ↔ u.val.1 ∈ l := by
  simp only [centersOfList, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact cardinality of `centersOfList` for a duplicate-free list of in-range indices. -/
theorem card_centersOfList_of_nodup {M : RatMetric} {l : List ℕ} (hnodup : l.Nodup)
    (hlt : ∀ i ∈ l, i < M.n) : (centersOfList M l).card = l.length := by
  classical
  have hbij : (centersOfList M l).card = l.toFinset.card := by
    refine Finset.card_bij (fun u _ ↦ u.val.1)
      (fun u hu ↦ List.mem_toFinset.mpr (mem_centersOfList.mp hu))
      (fun _ _ _ _ h ↦ RatMetricVertex.ext (Fin.ext h)) ?_
    intro i hi
    have hil := List.mem_toFinset.mp hi
    exact ⟨⟨⟨i, hlt i hil⟩⟩, mem_centersOfList.mpr hil, rfl⟩
  rw [hbij, List.toFinset_card_of_nodup hnodup]

/-! ### Encoded `ForbiddenKCenter` and `FairKCenter` Instances -/

/-- An encoded instance of the $k$-center problem with forbidden centers over a rational metric. -/
@[ext]
structure ForbiddenKCenter where
  /-- Underlying finite rational metric space. -/
  metric : RatMetric
  /-- Indicator list of allowed centers (`true` = allowed, `false` = forbidden). -/
  allowed : List Bool
  /-- Number of centers to select. -/
  k : ℕ
  /-- The allowed-center indicator matches the point count. -/
  allowed_length : allowed.length = metric.n

namespace ForbiddenKCenter

/-- Whether vertex `u` is allowed to be selected as a center. -/
def isAllowed (I : ForbiddenKCenter) (u : RatMetricVertex I.metric) : Bool :=
  I.allowed.getD u.val.1 false

/-- Finset of allowed centers of `I`. -/
def allowedFinset (I : ForbiddenKCenter) : Finset (RatMetricVertex I.metric) :=
  Finset.univ.filter fun u ↦ I.isAllowed u = true

/-- Membership characterization of `ForbiddenKCenter.allowedFinset`. -/
@[simp]
theorem mem_allowedFinset (I : ForbiddenKCenter) (u : RatMetricVertex I.metric) :
    u ∈ I.allowedFinset ↔ I.isAllowed u = true := by
  simp only [allowedFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Instance feasibility: `1 ≤ k ≤ |A|`. -/
@[expose] def IsFeasible (I : ForbiddenKCenter) : Prop :=
  1 ≤ I.k ∧ I.k ≤ I.allowedFinset.card

/-- Center set represented by an output index list `l : List ℕ`. -/
def solFinset (I : ForbiddenKCenter) (l : List ℕ) : Finset (RatMetricVertex I.metric) :=
  centersOfList I.metric l

/-- Solution feasibility: `l` names a subset of allowed centers of exact cardinality `k`. -/
@[expose] def IsFeasibleSol (I : ForbiddenKCenter) (l : List ℕ) : Prop :=
  IsForbiddenCenterFeasible I.allowedFinset I.k (I.solFinset l)

/-- Optimal radius of a feasible `ForbiddenKCenter` instance. -/
def opt (I : ForbiddenKCenter) (hfeas : I.IsFeasible) : ℝ :=
  forbiddenCenterOpt I.allowedFinset I.k hfeas.1 hfeas.2

/-- Covering radius of a nonempty center set represented by `l`. -/
def solRadius (I : ForbiddenKCenter) (l : List ℕ) (h : (I.solFinset l).Nonempty) : ℝ :=
  centerRadius (I.solFinset l) h

/-- Solution `l` is an `α`-approximation for `I`. -/
@[expose] def IsApprox (I : ForbiddenKCenter) (hfeas : I.IsFeasible) (α : ℝ) (l : List ℕ) : Prop :=
  I.IsFeasibleSol l ∧ ∀ h : (I.solFinset l).Nonempty, I.solRadius l h ≤ α * I.opt hfeas

/-- Every feasible solution of a feasible instance is nonempty. -/
theorem solFinset_nonempty_of_isFeasibleSol {I : ForbiddenKCenter} (hfeas : I.IsFeasible)
    {l : List ℕ} (hsol : I.IsFeasibleSol l) : (I.solFinset l).Nonempty :=
  Finset.card_pos.mp (by rw [hsol.2]; exact hfeas.1)

/-- `MinOptProblem` interface for `ForbiddenKCenter`. -/
@[expose] noncomputable def toMinOptProblem : MinOptProblem ForbiddenKCenter (List ℕ) where
  IsValid := IsFeasible
  Feasible := IsFeasibleSol
  cost I l :=
    if h : (I.solFinset l).Nonempty then I.solRadius l h else finsetDiam (RatMetricVertex I.metric)
  opt I := by
    classical
    exact if h : I.IsFeasible then I.opt h else 0
  opt_le I l hfeas hsol := by
    classical
    have hne := solFinset_nonempty_of_isFeasibleSol hfeas hsol
    rw [dite_eq_left hfeas, dite_eq_left hne]
    exact forbiddenCenterOpt_le_radius hfeas.1 hfeas.2 hsol.1 hsol.2
  exists_opt I hfeas := by
    classical
    obtain ⟨S, hS, hSA, hSk, hopt⟩ := exists_forbiddenCenter_eq_opt I.allowedFinset I.k
      hfeas.1 hfeas.2
    let l : List ℕ := S.toList.map fun u ↦ u.val.1
    have hl : I.solFinset l = S := by
      ext u
      simp only [solFinset, mem_centersOfList, l, List.mem_map, Finset.mem_toList]
      exact ⟨fun ⟨v, hv, hvu⟩ ↦ (RatMetricVertex.ext (Fin.ext hvu)) ▸ hv,
        fun hu ↦ ⟨u, hu, rfl⟩⟩
    refine ⟨l, ⟨hl.symm ▸ hSA, hl.symm ▸ hSk⟩, ?_⟩
    have hne : (I.solFinset l).Nonempty := hl.symm ▸ hS
    rw [dite_eq_left hne, dite_eq_left hfeas]
    simpa only [solRadius, opt, hl] using hopt

end ForbiddenKCenter

/-- An encoded instance of the exact-quota fair $k$-center problem over a rational metric. -/
@[ext]
structure FairKCenter where
  /-- Underlying finite rational metric space. -/
  metric : RatMetric
  /-- Group index of each point. -/
  group : List ℕ
  /-- Required number of centers per group. -/
  req : List ℕ
  /-- Total number of centers to select. -/
  k : ℕ
  /-- Group assignment length matches point count. -/
  group_length : group.length = metric.n
  /-- Every assigned group index is in range of `req`. -/
  group_lt : ∀ g ∈ group, g < req.length

namespace FairKCenter

/-- Underlying `FairPartition` of a `FairKCenter` instance. -/
def toPartition (I : FairKCenter) : FairPartition (RatMetricVertex I.metric) I.req.length where
  group u := ⟨I.group[u.val.1]'(I.group_length.symm ▸ u.val.2),
    I.group_lt _ (List.getElem_mem _)⟩
  req g := I.req[g.1]'g.2

/-- Instance feasibility: `I.toPartition.IsFeasible I.k`. -/
@[expose] def IsFeasible (I : FairKCenter) : Prop :=
  I.toPartition.IsFeasible I.k

/-- Two-group non-degenerate regime: exactly two groups with `r₁, r₂ ≥ 1`. -/
@[expose] def IsTwoGroup (I : FairKCenter) : Prop :=
  I.req.length = 2 ∧ ∀ g : Fin I.req.length, 1 ≤ I.toPartition.req g

/-- One-per-group regime: `t = k` groups with `r_g = 1` for every `g`. -/
@[expose] def IsOnePerGroup (I : FairKCenter) : Prop :=
  I.req.length = I.k ∧ I.toPartition.IsOnePerGroup

/-- Center set represented by an output index list `l : List ℕ`. -/
def solFinset (I : FairKCenter) (l : List ℕ) : Finset (RatMetricVertex I.metric) :=
  centersOfList I.metric l

/-- Membership characterization of `FairKCenter.solFinset`. -/
theorem mem_solFinset (I : FairKCenter) (l : List ℕ) (u : RatMetricVertex I.metric) :
    u ∈ I.solFinset l ↔ u.val.1 ∈ l := mem_centersOfList

/-- Solution feasibility under exact-quota fairness constraints. -/
@[expose] def IsFeasibleSol (I : FairKCenter) (l : List ℕ) : Prop :=
  I.toPartition.IsFairCenterFeasible (I.solFinset l)

/-- Optimal radius of a feasible `FairKCenter` instance. -/
noncomputable def opt (I : FairKCenter) (hfeas : I.IsFeasible) : ℝ :=
  I.toPartition.fairCenterOpt hfeas

/-- Equation characterizing `FairKCenter.opt`. -/
theorem opt_eq (I : FairKCenter) (hfeas : I.IsFeasible) :
    I.opt hfeas = I.toPartition.fairCenterOpt hfeas := by rfl

/-- Covering radius of a nonempty center set represented by `l`. -/
def solRadius (I : FairKCenter) (l : List ℕ) (h : (I.solFinset l).Nonempty) : ℝ :=
  centerRadius (I.solFinset l) h

/-- Equation characterizing `FairKCenter.solRadius`. -/
theorem solRadius_eq (I : FairKCenter) (l : List ℕ) (h : (I.solFinset l).Nonempty) :
    I.solRadius l h = centerRadius (I.solFinset l) h := by rfl

/-- Solution `l` is an `α`-approximation for `I`. -/
@[expose] def IsApprox (I : FairKCenter) (hfeas : I.IsFeasible) (α : ℝ) (l : List ℕ) : Prop :=
  I.IsFeasibleSol l ∧ ∀ h : (I.solFinset l).Nonempty, I.solRadius l h ≤ α * I.opt hfeas

/-- Every feasible solution of a feasible fair instance is nonempty. -/
theorem solFinset_nonempty_of_isFeasibleSol {I : FairKCenter} (hfeas : I.IsFeasible)
    {l : List ℕ} (hsol : I.IsFeasibleSol l) : (I.solFinset l).Nonempty :=
  Finset.card_pos.mp (by
    rw [FairPartition.card_eq_totalReq_of_isFairCenterFeasible hsol, hfeas.2.1]
    exact hfeas.1)

/-- `MinOptProblem` interface for `FairKCenter` restricted to instances satisfying `P`. -/
@[expose] noncomputable def toMinOptProblem (P : FairKCenter → Prop) :
    MinOptProblem FairKCenter (List ℕ) where
  IsValid I := I.IsFeasible ∧ P I
  Feasible := IsFeasibleSol
  cost I l :=
    if h : (I.solFinset l).Nonempty then I.solRadius l h else finsetDiam (RatMetricVertex I.metric)
  opt I := by
    classical
    exact if h : I.IsFeasible then I.opt h else 0
  opt_le I l hvalid hsol := by
    classical
    have hfeas := hvalid.1
    have hne := solFinset_nonempty_of_isFeasibleSol hfeas hsol
    rw [dite_eq_left hfeas, dite_eq_left hne]
    exact FairPartition.fairCenterOpt_le_radius I.toPartition hfeas hsol
  exists_opt I hvalid := by
    classical
    have hfeas := hvalid.1
    obtain ⟨S, hS, hSfeas, hopt⟩ := FairPartition.exists_fairCenter_eq_opt I.toPartition hfeas
    let l : List ℕ := S.toList.map fun u ↦ u.val.1
    have hl : I.solFinset l = S := by
      ext u
      simp only [solFinset, mem_centersOfList, l, List.mem_map, Finset.mem_toList]
      exact ⟨fun ⟨v, hv, hvu⟩ ↦ (RatMetricVertex.ext (Fin.ext hvu)) ▸ hv,
        fun hu ↦ ⟨u, hu, rfl⟩⟩
    refine ⟨l, ?_, ?_⟩
    · change I.toPartition.IsFairCenterFeasible (I.solFinset l)
      rwa [hl]
    · have hne : (I.solFinset l).Nonempty := hl.symm ▸ hS
      rw [dite_eq_left hne, dite_eq_left hfeas]
      simpa only [solRadius, opt, hl] using hopt

end FairKCenter

/-! ### Multi-Tape Binary Encodings and Polynomial-Time Exact Full Solver -/

/-- Binary encoding of a rational distance matrix (`List (List ℚ)`), represented as a list of
rows of binary-encoded rationals. -/
abbrev encRatDistMatrix : List (List ℚ) ↪ List Bool :=
  encList (encList encRat)

/-- Binary encoding of a list of point indices (`List ℕ`), each index in binary. -/
abbrev encIndexList : List ℕ ↪ List Bool :=
  encList encNat

/-- Raw tuple encoding `(metric.dist, (allowed, k))` for `ForbiddenKCenter`. -/
abbrev encForbiddenRaw : List (List ℚ) × (List Bool × ℕ) ↪ List Bool :=
  encPair encRatDistMatrix (encPair (encList encBool) encNat)

/-- Binary encoding of `ForbiddenKCenter` via its data fields `(metric.dist, (allowed, k))`. -/
@[expose] def encForbiddenKCenter : ForbiddenKCenter ↪ List Bool where
  toFun I := encForbiddenRaw (I.metric.dist, (I.allowed, I.k))
  inj' I₁ I₂ h := by
    have h' := encForbiddenRaw.injective h
    exact ForbiddenKCenter.ext (RatMetric.ext (congrArg Prod.fst h'))
      (congrArg (fun p ↦ p.2.1) h') (congrArg (fun p ↦ p.2.2) h')

/-- Raw tuple encoding `(metric.dist, (group, (req, k)))` for `FairKCenter`. -/
abbrev encFairRaw : List (List ℚ) × (List ℕ × (List ℕ × ℕ)) ↪ List Bool :=
  encPair encRatDistMatrix (encPair (encList encNat) (encPair (encList encNat) encNat))

/-- Binary encoding of `FairKCenter` via its data fields `(metric.dist, (group, (req, k)))`. -/
@[expose] def encFairKCenter : FairKCenter ↪ List Bool where
  toFun I := encFairRaw (I.metric.dist, (I.group, (I.req, I.k)))
  inj' I₁ I₂ h := by
    have h' := encFairRaw.injective h
    exact FairKCenter.ext (RatMetric.ext (congrArg Prod.fst h'))
      (congrArg (fun p ↦ p.2.1) h') (congrArg (fun p ↦ p.2.2.1) h')
      (congrArg (fun p ↦ p.2.2.2) h')

/-- Reading the raw tuple of a `ForbiddenKCenter` instance is polynomial-time. -/
theorem computableInPolyTime_forbiddenRaw :
    ComputableInPolyTime (fun I : ForbiddenKCenter ↦ (I.metric.dist, (I.allowed, I.k)))
      encForbiddenKCenter encForbiddenRaw :=
  ComputableInPolyTime.of_eq fun _ ↦ rfl

/-- Reading the raw tuple of a `FairKCenter` instance is polynomial-time. -/
theorem computableInPolyTime_fairRaw :
    ComputableInPolyTime (fun I : FairKCenter ↦ (I.metric.dist, (I.group, (I.req, I.k))))
      encFairKCenter encFairRaw :=
  ComputableInPolyTime.of_eq fun _ ↦ rfl

@[fun_prop]
theorem computableInPolyTime_forbiddenDist :
    ComputableInPolyTime (fun I : ForbiddenKCenter ↦ I.metric.dist)
      encForbiddenKCenter encRatDistMatrix :=
  (fst _ _).comp computableInPolyTime_forbiddenRaw

@[fun_prop]
theorem computableInPolyTime_forbiddenAllowed :
    ComputableInPolyTime ForbiddenKCenter.allowed
      encForbiddenKCenter (encList encBool) :=
  ((fst _ _).comp (snd _ _)).comp computableInPolyTime_forbiddenRaw

@[fun_prop]
theorem computableInPolyTime_forbiddenK :
    ComputableInPolyTime ForbiddenKCenter.k encForbiddenKCenter encNat :=
  ((snd _ _).comp (snd _ _)).comp computableInPolyTime_forbiddenRaw

@[fun_prop]
theorem computableInPolyTime_fairDist :
    ComputableInPolyTime (fun I : FairKCenter ↦ I.metric.dist)
      encFairKCenter encRatDistMatrix :=
  (fst _ _).comp computableInPolyTime_fairRaw

@[fun_prop]
theorem computableInPolyTime_fairGroup :
    ComputableInPolyTime FairKCenter.group encFairKCenter (encList encNat) :=
  ((fst _ _).comp (snd _ _)).comp computableInPolyTime_fairRaw

@[fun_prop]
theorem computableInPolyTime_fairReq :
    ComputableInPolyTime FairKCenter.req encFairKCenter (encList encNat) :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp computableInPolyTime_fairRaw

@[fun_prop]
theorem computableInPolyTime_fairK :
    ComputableInPolyTime FairKCenter.k encFairKCenter encNat :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp computableInPolyTime_fairRaw

/-- Reading matrix entry `getDist D i j` at unary indices `(i, j)` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_getDist {γ : Type} {encIn : γ ↪ List Bool}
    {D : γ → List (List ℚ)} {i j : γ → ℕ}
    (hD : ComputableInPolyTime D encIn encRatDistMatrix)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x ↦ RatDistMatrix.getDist (D x) (i x) (j x)) encIn encRat :=
  listGetDWithInput (listGetDWithInput hD hi []) hj 0

/-- Exact polynomial-time solver for `FairKCenter` when `k = |U|`: selects every point. -/
def fairKCenterExactFullAlg (I : FairKCenter) : List ℕ :=
  (List.range I.metric.dist.length).map id

/-- `fairKCenterExactFullAlg` selects the full vertex set `Finset.univ`. -/
@[simp]
theorem solFinset_fairKCenterExactFullAlg (I : FairKCenter) :
    I.solFinset (fairKCenterExactFullAlg I) = Finset.univ := by
  ext u
  simp only [I.mem_solFinset, fairKCenterExactFullAlg, List.map_id_fun, id_eq, List.mem_range,
    u.val.2, Finset.mem_univ]

/-- `fairKCenterExactFullAlg` runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_fairKCenterExactFullAlg :
    ComputableInPolyTime fairKCenterExactFullAlg encFairKCenter encIndexList := by
  have hD : ComputableInPolyTime (fun I : FairKCenter ↦ I.metric.dist)
      encFairKCenter encRatDistMatrix := by fun_prop
  have hRange : ComputableInPolyTime (fun I : FairKCenter ↦ List.range I.metric.dist.length)
      encFairKCenter (encList encUnary) := range.comp ((length_list (encList encRat)).comp hD)
  exact mapWith (unary_to_binary.comp (snd encBool encUnary))
    (const (encIn := encFairKCenter) (encOut := encBool) false) hRange

/-- `fairKCenterExactFullAlg` returns an exact optimal solution (cost `0`) when
`I.k = I.metric.n`. -/
theorem fairKCenterExactFullAlg_isApprox (I : FairKCenter) (hfeas : I.IsFeasible)
    (hk : I.k = I.metric.n) : I.IsApprox hfeas 1 (fairKCenterExactFullAlg I) := by
  have hsol := solFinset_fairKCenterExactFullAlg I
  have hcard_sum : ∑ g : Fin I.req.length, (I.toPartition.groupSet g).card = I.metric.n := by
    have hunion :
        (Finset.univ.biUnion fun g : Fin I.req.length ↦ I.toPartition.groupSet g) =
          (Finset.univ : Finset (RatMetricVertex I.metric)) := by
      ext u
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, FairPartition.mem_groupSet,
        iff_true]
      exact ⟨I.toPartition.group u, rfl⟩
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin I.req.length))
        (fun g ↦ I.toPartition.groupSet g) := by
      intro g₁ _ g₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro u hu₁ hu₂
      exact hne (((FairPartition.mem_groupSet _ _ _).mp hu₁).symm.trans
        ((FairPartition.mem_groupSet _ _ _).mp hu₂))
    rw [← Finset.card_biUnion hdisj, hunion, Finset.card_univ, RatMetricVertex.card_eq]
  have hreq_eq :
      ∀ g : Fin I.req.length, I.toPartition.req g = (I.toPartition.groupSet g).card := by
    by_contra hne
    push Not at hne
    obtain ⟨g₀, hg₀⟩ := hne
    have hlt : I.toPartition.req g₀ < (I.toPartition.groupSet g₀).card :=
      lt_of_le_of_ne (hfeas.2.2 g₀) hg₀
    have hsum_lt :
        ∑ g : Fin I.req.length, I.toPartition.req g <
          ∑ g : Fin I.req.length, (I.toPartition.groupSet g).card :=
      Finset.sum_lt_sum (fun g _ ↦ hfeas.2.2 g) ⟨g₀, Finset.mem_univ g₀, hlt⟩
    have htot : ∑ g : Fin I.req.length, I.toPartition.req g = I.k := hfeas.2.1
    omega
  refine ⟨?_, ?_⟩
  · refine (FairPartition.isFairCenterFeasible_iff_inter _ _).mpr fun g ↦ ?_
    rw [hsol, Finset.univ_inter, ← hreq_eq g]
  · intro hne
    rw [I.solRadius_eq, one_mul, I.opt_eq]
    simp only [hsol, centerRadius_univ]
    exact FairPartition.fairCenterOpt_nonneg I.toPartition hfeas

end CslibFrontier.Complexity
