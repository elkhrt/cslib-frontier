/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/
module

public import CslibFrontier.Computability.Circuit.LinearArithmetic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# Rational Farkas Certificates and Automatic-Differentiation Subgradients for Linear Circuits

This module provides pure-rational Farkas infeasibility certificates on coordinate boxes
(`CslibFrontier.Computability.Circuit.checkFarkasInfeasible`,
`CslibFrontier.Computability.Circuit.checkGQVIFarkas`) together with syntactic convexity checking
and linear-time forward automatic-differentiation subgradients for linear arithmetic circuits
(`CslibFrontier.Computability.Circuit.isSyntacticallyConvexIn`,
`CslibFrontier.Computability.Circuit.autoDiffGradRat`,
`CslibFrontier.Computability.Circuit.autoDiffGradReal`).

## Main definitions

* `CslibFrontier.Computability.Circuit.ratDot`, `CslibFrontier.Computability.Circuit.ratL1Norm`,
  `CslibFrontier.Computability.Circuit.farkasBoxMin`: rational inner product, `ℓ₁` norm, and box
  minimum.
* `CslibFrontier.Computability.Circuit.checkFarkasInfeasible`,
  `CslibFrontier.Computability.Circuit.checkGQVIFarkas`: pure-rational Farkas infeasibility checks.
* `CslibFrontier.Computability.Circuit.isSyntacticallyConvexIn`: syntactic convexity predicate for a
  block of input wires of a `LinearArithCircuit`.
* `CslibFrontier.Computability.Circuit.autoDiffGradRat`,
  `CslibFrontier.Computability.Circuit.autoDiffGradReal`: forward automatic-differentiation
  subgradient.

## Main results

* `CslibFrontier.Computability.Circuit.farkas_infeasible_sound`: soundness of rational Farkas
  infeasibility checks on coordinate boxes.
* `CslibFrontier.Computability.Circuit.checkGQVIFarkas_sound`: soundness of Farkas GQVI optimality
  certificates on convex sets containing an `ℓ∞`-box.
* `CslibFrontier.Computability.Circuit.autoDiffGradReal_subgradient`: global subgradient inequality
  for `autoDiffGradReal` on syntactically convex circuits.
* `CslibFrontier.Computability.Circuit.autoDiffGradReal_eq_rat`: agreement of real and rational
  automatic-differentiation subgradients.
-/

public section

namespace CslibFrontier.Computability.Circuit

/-- Rational inner product `∑_{j < d} u_j * v_j`. -/
def ratDot (d : ℕ) (u v : List ℚ) : ℚ :=
  ((List.range d).map fun j => u.getD j 0 * v.getD j 0).sum

/-- Rational `ℓ₁` norm `∑_{j < d} |u_j|`. -/
def ratL1Norm (d : ℕ) (u : List ℚ) : ℚ :=
  ((List.range d).map fun j => |u.getD j 0|).sum

/-- Minimum of `⟨A, c⟩` over the coordinate box `c_j ∈ [lo_j, hi_j]` (`j < d`). -/
def farkasBoxMin (d : ℕ) (A lo hi : List ℚ) : ℚ :=
  ((List.range d).map fun j =>
    let aj := A.getD j 0
    Min.min (aj * lo.getD j 0) (aj * hi.getD j 0)).sum

@[simp]
theorem ratDot_zero (u v : List ℚ) : ratDot 0 u v = 0 := by
  simp [ratDot]

theorem ratDot_eq_sum (d : ℕ) (u v : List ℚ) :
    ratDot d u v = ((List.range d).map fun j => u.getD j 0 * v.getD j 0).sum := by rfl

@[simp]
theorem ratL1Norm_zero (u : List ℚ) : ratL1Norm 0 u = 0 := by
  simp [ratL1Norm]

theorem ratL1Norm_eq_sum (d : ℕ) (u : List ℚ) :
    ratL1Norm d u = ((List.range d).map fun j => |u.getD j 0|).sum := by rfl

theorem ratL1Norm_nonneg (d : ℕ) (u : List ℚ) : 0 ≤ ratL1Norm d u := by
  unfold ratL1Norm
  exact List.sum_nonneg fun q hq => by
    rcases List.mem_map.mp hq with ⟨_, _, rfl⟩
    exact abs_nonneg _

@[simp]
theorem farkasBoxMin_zero (A lo hi : List ℚ) : farkasBoxMin 0 A lo hi = 0 := by
  simp [farkasBoxMin]

@[simp]
theorem farkasBoxMin_replicate_zero (d : ℕ) (lo hi : List ℚ) :
    farkasBoxMin d (List.replicate d 0) lo hi = 0 := by
  unfold farkasBoxMin
  exact List.sum_eq_zero fun q hq => by
    rcases List.mem_map.mp hq with ⟨j, hj, rfl⟩
    have hjd := List.mem_range.mp hj
    simp [List.getD_eq_getElem?_getD, hjd]

theorem farkasBoxMin_eq_sum (d : ℕ) (A lo hi : List ℚ) :
    farkasBoxMin d A lo hi =
      ((List.range d).map fun j =>
        Min.min (A.getD j 0 * lo.getD j 0) (A.getD j 0 * hi.getD j 0)).sum := by rfl

/-- Pure-rational Farkas infeasibility check certifying that no `c` in the box `[lo, hi]` can
satisfy `⟨a_r, c - z_r⟩ + δ * ‖a_r‖₁ ≤ 0` simultaneously for all active halfspaces `(a_r, z_r)`
with multipliers `λ_r ≥ 0` (`r < k`). -/
def checkFarkasInfeasible (d : ℕ) (lo hi : List ℚ) (δ : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) : Bool :=
  let A : List ℚ := (List.range d).map fun j =>
    (hyps.map fun h => h.2.2 * h.1.getD j 0).sum
  let rhs : ℚ :=
    (hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ * ratL1Norm d h.1)).sum
  decide (rhs < farkasBoxMin d A lo hi)

theorem checkFarkasInfeasible_eq_decide (d : ℕ) (lo hi : List ℚ) (δ : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) :
    checkFarkasInfeasible d lo hi δ hyps =
      decide (((hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ * ratL1Norm d h.1)).sum) <
        farkasBoxMin d ((List.range d).map fun j =>
          (hyps.map fun h => h.2.2 * h.1.getD j 0).sum) lo hi) := by rfl

theorem checkFarkasInfeasible_of_forall_zero (d : ℕ) (lo hi : List ℚ) (δ : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) (hz : ∀ h ∈ hyps, h.2.2 = 0) :
    checkFarkasInfeasible d lo hi δ hyps = false := by
  have hA : ((List.range d).map fun j => (hyps.map fun h => h.2.2 * h.1.getD j 0).sum) =
      List.replicate d 0 := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact List.sum_eq_zero fun q hq => by
      rcases List.mem_map.mp hq with ⟨h, hh, rfl⟩; simp [hz h hh]
  have hrhs0 :
      (hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ * ratL1Norm d h.1)).sum = 0 :=
    List.sum_eq_zero fun q hq => by
      rcases List.mem_map.mp hq with ⟨h, hh, rfl⟩; simp [hz h hh]
  have hmin0 : farkasBoxMin d (List.replicate d 0) lo hi = 0 :=
    List.sum_eq_zero fun q hq => by
      rcases List.mem_map.mp hq with ⟨j, hj, rfl⟩
      have hjd := List.mem_range.mp hj
      simp [List.getD_eq_getElem?_getD, hjd]
  rw [checkFarkasInfeasible_eq_decide, hA, hrhs0, hmin0]
  decide

/-- Soundness of `checkFarkasInfeasible` (standard Lean axioms): if `c ∈ [lo, hi]` satisfies
`⟨a_r, c - z_r⟩ + δ * ‖a_r‖₁ ≤ 0` for every active entry `(a_r, z_r, λ_r)` with `λ_r ≥ 0`, then
`checkFarkasInfeasible` cannot return `true`. -/
theorem farkas_infeasible_sound (d : ℕ) (lo hi : List ℚ) (δ : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) (c : List ℝ)
    (hc : ∀ j < d, (lo.getD j 0 : ℝ) ≤ c.getD j 0 ∧ c.getD j 0 ≤ (hi.getD j 0 : ℝ))
    (hhyps : ∀ h ∈ hyps, 0 ≤ h.2.2 ∧
      ((List.range d).map fun j =>
        (h.1.getD j 0 : ℝ) * (c.getD j 0 - (h.2.1.getD j 0 : ℝ))).sum +
        (δ : ℝ) * (ratL1Norm d h.1 : ℝ) ≤ 0) :
    checkFarkasInfeasible d lo hi δ hyps = false := by
  simp only [checkFarkasInfeasible, decide_eq_false_iff_not, not_lt]
  set A : List ℚ := (List.range d).map fun j => (hyps.map fun h => h.2.2 * h.1.getD j 0).sum
  have hcast_sum : ∀ l : List ℚ, ((l.sum : ℚ) : ℝ) = (l.map fun q : ℚ => (q : ℝ)).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp [ih]
  -- Bound `farkasBoxMin ≤ ∑_j A_j * c_j` over `ℝ`.
  have hmin_le : (farkasBoxMin d A lo hi : ℝ) ≤
      ((List.range d).map fun j => (A.getD j 0 : ℝ) * c.getD j 0).sum := by
    rw [farkasBoxMin, hcast_sum, List.map_map]
    refine List.sum_le_sum fun j hj => ?_
    have hjd : j < d := List.mem_range.mp hj
    simp only [Function.comp_apply, Rat.cast_min, Rat.cast_mul]
    have hlo := (hc j hjd).1
    have hhi := (hc j hjd).2
    by_cases ha : (0 : ℝ) ≤ (A.getD j 0 : ℝ)
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hlo ha)
    · exact le_trans (min_le_right _ _)
        (mul_le_mul_of_nonpos_left hhi (le_of_not_ge ha))
  -- Rewrite `∑_j A_j * c_j = ∑_{h ∈ hyps} λ_h * ∑_j a_{h,j} * c_j`.
  have hswap : ((List.range d).map fun j => (A.getD j 0 : ℝ) * c.getD j 0).sum =
      (hyps.map fun h => (h.2.2 : ℝ) *
        ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * c.getD j 0).sum).sum := by
    have hAj : ∀ j ∈ List.range d, (A.getD j 0 : ℝ) * c.getD j 0 =
        (hyps.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * c.getD j 0)).sum := by
      intro j hj
      have hjd : j < d := List.mem_range.mp hj
      have hget : A.getD j 0 = (hyps.map fun h => h.2.2 * h.1.getD j 0).sum := by
        simp [A, List.getD_eq_getElem?_getD, hjd]
      rw [hget, hcast_sum, List.map_map]
      have hmul : ∀ hs : List (List ℚ × List ℚ × ℚ),
          (hs.map ((fun q : ℚ => (q : ℝ)) ∘ fun h => h.2.2 * h.1.getD j 0)).sum * c.getD j 0 =
          (hs.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * c.getD j 0)).sum := by
        intro hs; induction hs with
        | nil => simp
        | cons h t ih =>
          simp only [List.map_cons, Function.comp_apply, Rat.cast_mul, List.sum_cons, add_mul,
            mul_assoc, ih]
      exact hmul hyps
    rw [List.map_congr_left hAj]
    clear hAj hmin_le hhyps A
    induction hyps with
    | nil => simp
    | cons h t ih =>
      simp only [List.map_cons, List.sum_cons]
      have hsplit : ((List.range d).map fun j =>
            (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * c.getD j 0) +
              (t.map fun h' => (h'.2.2 : ℝ) * ((h'.1.getD j 0 : ℝ) * c.getD j 0)).sum).sum =
          ((List.range d).map fun j => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * c.getD j 0)).sum +
          ((List.range d).map fun j =>
            (t.map fun h' => (h'.2.2 : ℝ) * ((h'.1.getD j 0 : ℝ) * c.getD j 0)).sum).sum := by
        clear ih
        induction List.range d with
        | nil => simp
        | cons j js ih' => simp only [List.map_cons, List.sum_cons, ih']; ring
      rw [hsplit, ih]
      congr 1
      clear ih hsplit
      induction List.range d with
      | nil => simp
      | cons j js ih' => simp only [List.map_cons, List.sum_cons, ← ih', mul_add]
  -- Bound each `h ∈ hyps` using `hhyps`.
  have hsum_le : (hyps.map fun h => (h.2.2 : ℝ) *
        ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * c.getD j 0).sum).sum ≤
      (((hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ * ratL1Norm d h.1)).sum : ℚ) : ℝ) := by
    rw [hcast_sum, List.map_map]
    refine List.sum_le_sum fun h hh => ?_
    obtain ⟨hlam, hineq⟩ := hhyps h hh
    have hlamR : (0 : ℝ) ≤ (h.2.2 : ℝ) := by exact_mod_cast hlam
    simp only [Function.comp_apply, Rat.cast_mul, Rat.cast_sub]
    refine mul_le_mul_of_nonneg_left ?_ hlamR
    have hdiff : ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * c.getD j 0).sum -
          (ratDot d h.1 h.2.1 : ℝ) =
        ((List.range d).map fun j =>
          (h.1.getD j 0 : ℝ) * (c.getD j 0 - (h.2.1.getD j 0 : ℝ))).sum := by
      rw [ratDot, hcast_sum, List.map_map]
      induction List.range d with
      | nil => simp
      | cons j js ih =>
        simp only [List.map_cons, Function.comp_apply, Rat.cast_mul, List.sum_cons]
        linarith
    linarith
  have hfinal : (farkasBoxMin d A lo hi : ℝ) ≤
      (((hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ * ratL1Norm d h.1)).sum : ℚ) : ℝ) := by
    linarith
  exact_mod_cast hfinal

/-- Pure-rational Farkas optimality check for GQVI: checks whether `λ₀` on the halfspace
`⟨v, y - x⟩ + β / 2 ≤ 0` together with active separating hyperplanes `hyps` for `R(x)` leaves no
`δ_eff`-cube inside `[0, 1]^d`. -/
def checkGQVIFarkas (d : ℕ) (v x : List ℚ) (lam0 β δ_eff : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) : Bool :=
  let A : List ℚ := (List.range d).map fun j =>
    lam0 * v.getD j 0 + (hyps.map fun h => h.2.2 * h.1.getD j 0).sum
  let rhs : ℚ :=
    lam0 * (ratDot d v x - β / 2 - δ_eff * ratL1Norm d v) +
    (hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ_eff * ratL1Norm d h.1)).sum
  decide (rhs < farkasBoxMin d A (List.replicate d 0) (List.replicate d 1))

theorem checkGQVIFarkas_eq_decide (d : ℕ) (v x : List ℚ) (lam0 β δ_eff : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) :
    checkGQVIFarkas d v x lam0 β δ_eff hyps =
      decide (lam0 * (ratDot d v x - β / 2 - δ_eff * ratL1Norm d v) +
        (hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ_eff * ratL1Norm d h.1)).sum <
        farkasBoxMin d ((List.range d).map fun j =>
          lam0 * v.getD j 0 + (hyps.map fun h => h.2.2 * h.1.getD j 0).sum)
          (List.replicate d 0) (List.replicate d 1)) := by rfl


/-- **Soundness of `checkGQVIFarkas`** (standard Lean axioms): if `R(x) ⊆ [0, 1]^d` is convex,
contains an `ℓ∞`-box of radius `δ > 0` around some `c₀ ∈ [0, 1]^d`, `β > 0`, `v ∈ [-1, 1]^d`,
every active entry `(a_r, z_r, λ_r)` in `hyps` satisfies `λ_r ≥ 0` and separates `R(x)`, and
`checkGQVIFarkas d v x lam0 β δ_eff hyps = true` with `lam0 ≥ 0` and
`δ_eff = min δ 1 * min (1/2) (β / (4 * (d + 1)))`, then `⟨v, y - x⟩ + β ≥ 0` for all `y ∈ R(x)`. -/
theorem checkGQVIFarkas_sound (d : ℕ) (v x : List ℚ) (lam0 β δ : ℚ)
    (hyps : List (List ℚ × List ℚ × ℚ)) (R : Set (List ℝ))
    (hβ : 0 < β) (hδ : 0 < δ) (hlam0 : 0 ≤ lam0)
    (hv : ∀ j < d, -1 ≤ v.getD j 0 ∧ v.getD j 0 ≤ 1)
    (hRbox : ∀ y ∈ R, ∀ j < d, 0 ≤ y.getD j 0 ∧ y.getD j 0 ≤ 1)
    (hRconv : ∀ y₁ ∈ R, ∀ y₂ ∈ R, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((List.range d).map fun j => (1 - t) * y₁.getD j 0 + t * y₂.getD j 0) ∈ R)
    (hRball : ∃ c₀ : List ℝ, (∀ j < d, 0 ≤ c₀.getD j 0 ∧ c₀.getD j 0 ≤ 1) ∧
      ∀ z : List ℝ, (∀ j < d, |z.getD j 0 - c₀.getD j 0| ≤ (δ : ℝ)) →
        ((List.range d).map fun j => z.getD j 0) ∈ R)
    (hhyps : ∀ h ∈ hyps, 0 ≤ h.2.2 ∧
      (0 < h.2.2 → ∀ y ∈ R,
        ((List.range d).map fun j =>
          (h.1.getD j 0 : ℝ) * (y.getD j 0 - (h.2.1.getD j 0 : ℝ))).sum ≤ 0))
    (hcheck : checkGQVIFarkas d v x lam0 β
      (Min.min δ 1 * Min.min ((1 : ℚ) / 2) (β / (4 * ((d + 1 : ℕ) : ℚ)))) hyps = true) :
    ∀ y ∈ R, 0 ≤ ((List.range d).map fun j => (v.getD j 0 : ℝ) * (y.getD j 0 - (x.getD j 0 :
    ℝ))).sum +
      (β : ℝ) := by
  set tQ : ℚ := Min.min ((1 : ℚ) / 2) (β / (4 * ((d + 1 : ℕ) : ℚ)))
  set δ_eff : ℚ := Min.min δ 1 * tQ
  have htQ_pos : 0 < tQ := lt_min (by norm_num) (div_pos hβ (by positivity))
  have htQ_le : tQ ≤ 1 / 2 := min_le_left _ _
  have htQ_β : tQ * (d : ℚ) ≤ β / 4 := by
    have h1 : tQ ≤ β / (4 * ((d + 1 : ℕ) : ℚ)) := min_le_right _ _
    have hdn : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
    have hpos : (0 : ℚ) < 4 * ((d + 1 : ℕ) : ℚ) := by positivity
    calc tQ * (d : ℚ) ≤ (β / (4 * ((d + 1 : ℕ) : ℚ))) * (d : ℚ) :=
          mul_le_mul_of_nonneg_right h1 hdn
      _ = (β / 4) * ((d : ℚ) / ((d + 1 : ℕ) : ℚ)) := by ring
      _ ≤ (β / 4) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          rw [div_le_one (by positivity)]
          exact_mod_cast Nat.le_succ d
      _ = β / 4 := mul_one _
  have hδ_eff_le : δ_eff ≤ tQ * δ :=
    mul_le_mul_of_nonneg_right (min_le_left δ 1) htQ_pos.le |>.trans (le_of_eq (mul_comm _ _))
  have hδ_eff_d : δ_eff * (d : ℚ) ≤ β / 4 := by
    have h1 : δ_eff ≤ tQ := by
      calc δ_eff = Min.min δ 1 * tQ := by rfl
        _ ≤ 1 * tQ := mul_le_mul_of_nonneg_right (min_le_right δ 1) htQ_pos.le
        _ = tQ := one_mul _
    exact (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg d)).trans htQ_β
  obtain ⟨c₀, hc₀_box, hc₀_ball⟩ := hRball
  intro y hy
  set tR : ℝ := (tQ : ℝ)
  have htR0 : 0 ≤ tR := by dsimp only [tR]; exact_mod_cast htQ_pos.le
  have htR1 : tR ≤ 1 := by
    dsimp only [tR]
    exact_mod_cast (htQ_le.trans (by norm_num : (1 : ℚ) / 2 ≤ 1))
  let y' : List ℝ := (List.range d).map fun j => (1 - tR) * y.getD j 0 + tR * c₀.getD j 0
  have hy'_get : ∀ j < d, y'.getD j 0 = (1 - tR) * y.getD j 0 + tR * c₀.getD j 0 := fun j hj => by
    simp [y', List.getD_eq_getElem?_getD, hj]
  have hy'_box : ∀ j < d, 0 ≤ y'.getD j 0 ∧ y'.getD j 0 ≤ 1 := fun j hj => by
    rw [hy'_get j hj]
    have hyj := hRbox y hy j hj; have hcj := hc₀_box j hj
    constructor <;> nlinarith
  -- Every active hyperplane separates `y' + δ_eff * sign(a)` ∈ R(x)!
  have hcast_sum : ∀ l : List ℚ, ((l.sum : ℚ) : ℝ) = (l.map fun q : ℚ => (q : ℝ)).sum := by
    intro l; induction l with | nil => simp | cons a s ih => simp [ih]
  have hhyps_y' : ∀ h ∈ hyps,
      (h.2.2 : ℝ) * ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * y'.getD j 0).sum ≤
      (h.2.2 : ℝ) * ((ratDot d h.1 h.2.1 : ℝ) - (δ_eff : ℝ) * (ratL1Norm d h.1 : ℝ)) := by
    intro h hh
    obtain ⟨hlam, hsep⟩ := hhyps h hh
    rcases eq_or_lt_of_le hlam with h0 | hpos
    · rw [← h0]; simp
    · have hlamR : (0 : ℝ) ≤ (h.2.2 : ℝ) := by exact_mod_cast hlam
      refine mul_le_mul_of_nonneg_left ?_ hlamR
      let z_pert : List ℝ := (List.range d).map fun j =>
        y'.getD j 0 + (δ_eff : ℝ) * (if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1)
      have hz_mem : z_pert ∈ R := by
        let w : List ℝ := (List.range d).map fun j =>
          c₀.getD j 0 + ((δ_eff : ℝ) / tR) * (if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1)
        have hw_mem : ((List.range d).map fun j => w.getD j 0) ∈ R := by
          refine hc₀_ball w fun j hj => ?_
          have hwj : w.getD j 0 = c₀.getD j 0 +
              ((δ_eff : ℝ) / tR) * (if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1) := by
            simp [w, List.getD_eq_getElem?_getD, hj]
          rw [hwj, add_sub_cancel_left, abs_mul]
          have hsign : |if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1| = 1 := by split_ifs <;> norm_num
          rw [hsign, mul_one, abs_of_nonneg (div_nonneg (by exact_mod_cast (mul_pos (lt_min hδ (by
          norm_num)) htQ_pos).le) htR0)]
          rw [div_le_iff₀ (by dsimp only [tR]; exact_mod_cast htQ_pos), mul_comm]
          dsimp only [tR]; exact_mod_cast hδ_eff_le
        have hconv_eq : ((List.range d).map fun j =>
              (1 - tR) * y.getD j 0 + tR * ((List.range d).map fun j' => w.getD j' 0).getD j 0) =
            z_pert := by
          refine List.map_congr_left fun j hj => ?_
          have hjd := List.mem_range.mp hj
          have hwj : ((List.range d).map fun j' => w.getD j' 0).getD j 0 =
              c₀.getD j 0 + ((δ_eff : ℝ) / tR) * (if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1) := by
            simp [w, List.getD_eq_getElem?_getD, hjd]
          rw [hwj, hy'_get j hjd]
          have htne : tR ≠ 0 := ne_of_gt (by dsimp only [tR]; exact_mod_cast htQ_pos)
          field_simp [htne]; ring
        rw [← hconv_eq]
        exact hRconv y hy _ hw_mem tR htR0 htR1
      have hs := hsep hpos z_pert hz_mem
      have hterm : ((List.range d).map fun j =>
            (h.1.getD j 0 : ℝ) * (z_pert.getD j 0 - (h.2.1.getD j 0 : ℝ))).sum =
          ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * y'.getD j 0).sum -
          (ratDot d h.1 h.2.1 : ℝ) + (δ_eff : ℝ) * (ratL1Norm d h.1 : ℝ) := by
        rw [ratDot, ratL1Norm, hcast_sum, hcast_sum, List.map_map, List.map_map]
        have h1 : ∀ l : List ℕ,
            (l.map fun j => (h.1.getD j 0 : ℝ) *
              (y'.getD j 0 + (δ_eff : ℝ) * (if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1) -
                (h.2.1.getD j 0 : ℝ))).sum =
            (l.map fun j => (h.1.getD j 0 : ℝ) * y'.getD j 0).sum -
            (l.map fun j => (h.1.getD j 0 : ℝ) * (h.2.1.getD j 0 : ℝ)).sum +
            (δ_eff : ℝ) * (l.map fun j => |(h.1.getD j 0 : ℝ)|).sum := by
          intro l; induction l with
          | nil => simp
          | cons j js ih =>
            simp only [List.map_cons, List.sum_cons, ih]
            by_cases hsign : 0 ≤ h.1.getD j 0
            · have hsR : (0 : ℝ) ≤ (h.1.getD j 0 : ℝ) := by exact_mod_cast hsign
              simp only [hsign, ↓reduceIte, abs_of_nonneg hsR]; ring
            · have hsR : (h.1.getD j 0 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hsign)
              simp only [hsign, ↓reduceIte, abs_of_neg hsR]; ring
        have hcongr : ((List.range d).map fun j =>
              (h.1.getD j 0 : ℝ) * (z_pert.getD j 0 - (h.2.1.getD j 0 : ℝ))) =
            ((List.range d).map fun j => (h.1.getD j 0 : ℝ) *
              (y'.getD j 0 + (δ_eff : ℝ) * (if 0 ≤ h.1.getD j 0 then (1 : ℝ) else -1) -
                (h.2.1.getD j 0 : ℝ))) := by
          refine List.map_congr_left fun j hj => ?_
          have hjd := List.mem_range.mp hj
          simp [z_pert, List.getD_eq_getElem?_getD, hjd]
        rw [hcongr, h1]
        simp [Function.comp_def, Rat.cast_mul, Rat.cast_abs]
      linarith
  -- Now plug `y' ∈ [0, 1]^d` into `checkGQVIFarkas`.
  simp only [checkGQVIFarkas, decide_eq_true_eq] at hcheck
  set A : List ℚ := (List.range d).map fun j =>
    lam0 * v.getD j 0 + (hyps.map fun h => h.2.2 * h.1.getD j 0).sum
  have hcheckR : ((lam0 * (ratDot d v x - β / 2 - δ_eff * ratL1Norm d v) +
      (hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ_eff * ratL1Norm d h.1)).sum : ℚ) : ℝ) <
      (farkasBoxMin d A (List.replicate d 0) (List.replicate d 1) : ℝ) := by
    exact_mod_cast hcheck
  have hmin_le : (farkasBoxMin d A (List.replicate d 0) (List.replicate d 1) : ℝ) ≤
      ((List.range d).map fun j => (A.getD j 0 : ℝ) * y'.getD j 0).sum := by
    rw [farkasBoxMin, hcast_sum, List.map_map]
    refine List.sum_le_sum fun j hj => ?_
    have hjd := List.mem_range.mp hj
    have hlo0 : (List.replicate d (0 : ℚ)).getD j 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, hjd]
    have hhi1 : (List.replicate d (1 : ℚ)).getD j 0 = 1 := by
      simp [List.getD_eq_getElem?_getD, hjd]
    simp only [Function.comp_apply, hlo0, hhi1, Rat.cast_min, Rat.cast_zero, mul_zero, mul_one]
    have hyj := hy'_box j hjd
    by_cases ha : (0 : ℝ) ≤ (A.getD j 0 : ℝ)
    · exact le_trans (min_le_left _ _) (mul_nonneg ha hyj.1)
    · exact le_trans (min_le_right _ _)
        (by nlinarith [le_of_not_ge ha, hyj.2])
  have hA_expand : ((List.range d).map fun j => (A.getD j 0 : ℝ) * y'.getD j 0).sum =
      (lam0 : ℝ) * ((List.range d).map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum +
      (hyps.map fun h => (h.2.2 : ℝ) *
        ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * y'.getD j 0).sum).sum := by
    have hAj : ∀ j ∈ List.range d, (A.getD j 0 : ℝ) * y'.getD j 0 =
        (lam0 : ℝ) * ((v.getD j 0 : ℝ) * y'.getD j 0) +
        (hyps.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * y'.getD j 0)).sum := by
      intro j hj
      have hjd := List.mem_range.mp hj
      have hget : A.getD j 0 = lam0 * v.getD j 0 + (hyps.map fun h => h.2.2 * h.1.getD j 0).sum :=
      by
        simp [A, List.getD_eq_getElem?_getD, hjd]
      rw [hget, Rat.cast_add, Rat.cast_mul, add_mul, mul_assoc, hcast_sum, List.map_map]
      congr 1
      have hmul : ∀ hs : List (List ℚ × List ℚ × ℚ),
          (hs.map ((fun q : ℚ => (q : ℝ)) ∘ fun h => h.2.2 * h.1.getD j 0)).sum * y'.getD j 0 =
          (hs.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * y'.getD j 0)).sum := by
        intro hs; induction hs with
        | nil => simp
        | cons h t ih =>
          simp only [List.map_cons, Function.comp_apply, Rat.cast_mul, List.sum_cons, add_mul,
            mul_assoc, ih]
      exact hmul hyps
    rw [List.map_congr_left hAj]
    have hsplit : ∀ l : List ℕ,
        (l.map fun j => (lam0 : ℝ) * ((v.getD j 0 : ℝ) * y'.getD j 0) +
          (hyps.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * y'.getD j 0)).sum).sum =
        (lam0 : ℝ) * (l.map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum +
        (hyps.map fun h => (h.2.2 : ℝ) * (l.map fun j => (h.1.getD j 0 : ℝ) * y'.getD j 0).sum).sum
        := by
      intro l; induction l with
      | nil =>
        simp only [List.map_nil, List.sum_nil, mul_zero, zero_add]
        symm; exact List.sum_eq_zero fun q hq => by
          rcases List.mem_map.mp hq with ⟨_, _, rfl⟩; simp
      | cons j js ih =>
        simp only [List.map_cons, List.sum_cons, ih, mul_add]
        have hsum_add : ∀ hs : List (List ℚ × List ℚ × ℚ),
            (hs.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * y'.getD j 0)).sum +
            (hs.map fun h => (h.2.2 : ℝ) * (js.map fun k => (h.1.getD k 0 : ℝ) * y'.getD k
            0).sum).sum =
            (hs.map fun h => (h.2.2 : ℝ) * ((h.1.getD j 0 : ℝ) * y'.getD j 0) +
              (h.2.2 : ℝ) * (js.map fun k => (h.1.getD k 0 : ℝ) * y'.getD k 0).sum).sum := by
          intro hs; induction hs with
          | nil => simp
          | cons h t iht => simp only [List.map_cons, List.sum_cons, ← iht]; ring
        rw [← add_assoc, add_comm ((lam0 : ℝ) * _ + _), ← add_assoc, add_assoc]
        have hcomb := hsum_add hyps
        linarith
    exact hsplit (List.range d)
  have hhyps_sum : (hyps.map fun h => (h.2.2 : ℝ) *
        ((List.range d).map fun j => (h.1.getD j 0 : ℝ) * y'.getD j 0).sum).sum ≤
      (((hyps.map fun h => h.2.2 * (ratDot d h.1 h.2.1 - δ_eff * ratL1Norm d h.1)).sum : ℚ) : ℝ) :=
      by
    rw [hcast_sum, List.map_map]
    refine List.sum_le_sum fun h hh => ?_
    simpa [Function.comp_apply, Rat.cast_mul, Rat.cast_sub] using hhyps_y' h hh
  have hlam0_strict : (lam0 : ℝ) * ((ratDot d v x : ℝ) - (β : ℝ) / 2 -
        (δ_eff : ℝ) * (ratL1Norm d v : ℝ)) <
      (lam0 : ℝ) * ((List.range d).map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum := by
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at hcheckR
    linarith
  have hlam0_pos : (0 : ℝ) < (lam0 : ℝ) := by
    have hnn : (0 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · rw [← h0, zero_mul, zero_mul] at hlam0_strict; exact absurd hlam0_strict (lt_irrefl 0)
    · exact hpos
  have hvy' : (ratDot d v x : ℝ) - (β : ℝ) / 2 - (δ_eff : ℝ) * (ratL1Norm d v : ℝ) <
      ((List.range d).map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum :=
    lt_of_mul_lt_mul_left hlam0_strict hlam0_pos.le
  have hL1_le : (ratL1Norm d v : ℝ) ≤ (d : ℝ) := by
    rw [ratL1Norm, hcast_sum, List.map_map]
    have hfn : ((fun q : ℚ => (q : ℝ)) ∘ fun j => |v.getD j 0|) =
        fun j => |(v.getD j 0 : ℝ)| := by
      funext j; simp [Rat.cast_abs]
    rw [hfn]
    have : ((List.range d).map fun j => |(v.getD j 0 : ℝ)|).sum ≤
        ((List.range d).map fun _ => (1 : ℝ)).sum :=
      List.sum_le_sum fun j hj => by
        have hjd := List.mem_range.mp hj
        have h1 := hv j hjd
        rw [abs_le]; exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
    simpa using this
  have hshift : |((List.range d).map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum -
      ((List.range d).map fun j => (v.getD j 0 : ℝ) * y.getD j 0).sum| ≤ tR * (d : ℝ) := by
    have hdiff : ∀ l : List ℕ, (∀ j ∈ l, j < d) →
        |(l.map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum -
         (l.map fun j => (v.getD j 0 : ℝ) * y.getD j 0).sum| ≤ tR * (l.length : ℝ) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons j js ih =>
        intro hl
        have hjd := hl j (List.mem_cons_self ..)
        have h1 := hv j hjd
        have hyj := hRbox y hy j hjd
        have hcj := hc₀_box j hjd
        have hterm : |(v.getD j 0 : ℝ) * y'.getD j 0 - (v.getD j 0 : ℝ) * y.getD j 0| ≤ tR := by
          rw [← mul_sub, abs_mul, hy'_get j hjd]
          have hvabs : |(v.getD j 0 : ℝ)| ≤ 1 := by
            rw [abs_le]; exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
          have hyabs : |(1 - tR) * y.getD j 0 + tR * c₀.getD j 0 - y.getD j 0| ≤ tR := by
            rw [show (1 - tR) * y.getD j 0 + tR * c₀.getD j 0 - y.getD j 0 =
                tR * (c₀.getD j 0 - y.getD j 0) by ring, abs_mul, abs_of_nonneg htR0]
            have hcy : |c₀.getD j 0 - y.getD j 0| ≤ 1 := by rw [abs_le]; constructor <;> linarith
            nlinarith
          nlinarith [abs_nonneg (v.getD j 0 : ℝ)]
        have hih := ih (fun k hk => hl k (List.mem_cons_of_mem _ hk))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        set s' : ℝ := (js.map fun j => (v.getD j 0 : ℝ) * y'.getD j 0).sum
        set s : ℝ := (js.map fun j => (v.getD j 0 : ℝ) * y.getD j 0).sum
        have htri : |((v.getD j 0 : ℝ) * y'.getD j 0 + s') - ((v.getD j 0 : ℝ) * y.getD j 0 + s)| ≤
            |(v.getD j 0 : ℝ) * y'.getD j 0 - (v.getD j 0 : ℝ) * y.getD j 0| + |s' - s| := by
          rw [show ((v.getD j 0 : ℝ) * y'.getD j 0 + s') - ((v.getD j 0 : ℝ) * y.getD j 0 + s) =
              ((v.getD j 0 : ℝ) * y'.getD j 0 - (v.getD j 0 : ℝ) * y.getD j 0) + (s' - s) by ring]
          exact abs_add_le _ _
        linarith
    simpa using hdiff (List.range d) (fun j hj => List.mem_range.mp hj)
  have hvy_diff : ((List.range d).map fun j => (v.getD j 0 : ℝ) * (y.getD j 0 - (x.getD j 0 :
  ℝ))).sum =
      ((List.range d).map fun j => (v.getD j 0 : ℝ) * y.getD j 0).sum - (ratDot d v x : ℝ) := by
    rw [ratDot, hcast_sum, List.map_map]
    induction List.range d with
    | nil => simp
    | cons j js ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, Rat.cast_mul, ih]
      ring
  have hδdR : (δ_eff : ℝ) * (d : ℝ) ≤ (β : ℝ) / 4 := by exact_mod_cast hδ_eff_d
  have htdR : tR * (d : ℝ) ≤ (β : ℝ) / 4 := by dsimp only [tR]; exact_mod_cast htQ_β
  have hδnn : (0 : ℝ) ≤ (δ_eff : ℝ) := by
    exact_mod_cast (mul_pos (lt_min hδ (by norm_num)) htQ_pos).le
  rw [hvy_diff]
  linarith [(abs_le.mp hshift).2, mul_le_mul_of_nonneg_left hL1_le hδnn]


/-! ### Syntactic Convexity and Linear-Time Automatic-Differentiation Subgradients -/

/-- Refined wire-convexity state `(isConstInX, isAffineInX, isConvexInX)` for a circuit where
the convex variable occupies wires `[offset, offset + d)`. -/
def wireConvexity3Step (st : List (Bool × Bool × Bool)) : LinearGate → List (Bool × Bool × Bool)
  | .input idx => st ++ [st.getD idx (true, true, true)]
  | .const _ => st ++ [(true, true, true)]
  | .add i j =>
    let si := st.getD i (true, true, true)
    let sj := st.getD j (true, true, true)
    st ++ [(si.1 && sj.1, si.2.1 && sj.2.1, si.2.2 && sj.2.2)]
  | .sub i j =>
    let si := st.getD i (true, true, true)
    let sj := st.getD j (true, true, true)
    st ++ [(si.1 && sj.1, si.2.1 && sj.2.1, si.2.2 && sj.2.1)]
  | .scale q i =>
    let si := st.getD i (true, true, true)
    st ++ [(si.1, si.2.1, if 0 ≤ q then si.2.2 else si.2.1)]
  | .min i j =>
    let si := st.getD i (true, true, true)
    let sj := st.getD j (true, true, true)
    st ++ [(si.1 && sj.1, si.1 && sj.1, si.1 && sj.1)]
  | .max i j =>
    let si := st.getD i (true, true, true)
    let sj := st.getD j (true, true, true)
    st ++ [(si.1 && sj.1, si.1 && sj.1, si.2.2 && sj.2.2)]

@[simp]
theorem wireConvexity3Step_input (st : List (Bool × Bool × Bool)) (idx : ℕ) :
    wireConvexity3Step st (.input idx) = st ++ [st.getD idx (true, true, true)] := by rfl

@[simp]
theorem wireConvexity3Step_const (st : List (Bool × Bool × Bool)) (q : ℚ) :
    wireConvexity3Step st (.const q) = st ++ [(true, true, true)] := by rfl

@[simp]
theorem wireConvexity3Step_add (st : List (Bool × Bool × Bool)) (i j : ℕ) :
    wireConvexity3Step st (.add i j) =
      let si := st.getD i (true, true, true)
      let sj := st.getD j (true, true, true)
      st ++ [(si.1 && sj.1, si.2.1 && sj.2.1, si.2.2 && sj.2.2)] := by rfl

@[simp]
theorem wireConvexity3Step_sub (st : List (Bool × Bool × Bool)) (i j : ℕ) :
    wireConvexity3Step st (.sub i j) =
      let si := st.getD i (true, true, true)
      let sj := st.getD j (true, true, true)
      st ++ [(si.1 && sj.1, si.2.1 && sj.2.1, si.2.2 && sj.2.1)] := by rfl

@[simp]
theorem wireConvexity3Step_scale (st : List (Bool × Bool × Bool)) (q : ℚ) (i : ℕ) :
    wireConvexity3Step st (.scale q i) =
      let si := st.getD i (true, true, true)
      st ++ [(si.1, si.2.1, if 0 ≤ q then si.2.2 else si.2.1)] := by rfl

@[simp]
theorem wireConvexity3Step_min (st : List (Bool × Bool × Bool)) (i j : ℕ) :
    wireConvexity3Step st (.min i j) =
      let si := st.getD i (true, true, true)
      let sj := st.getD j (true, true, true)
      st ++ [(si.1 && sj.1, si.1 && sj.1, si.1 && sj.1)] := by rfl

@[simp]
theorem wireConvexity3Step_max (st : List (Bool × Bool × Bool)) (i j : ℕ) :
    wireConvexity3Step st (.max i j) =
      let si := st.getD i (true, true, true)
      let sj := st.getD j (true, true, true)
      st ++ [(si.1 && sj.1, si.1 && sj.1, si.2.2 && sj.2.2)] := by rfl

@[simp]
theorem length_wireConvexity3Step (st : List (Bool × Bool × Bool)) (g : LinearGate) :
    (wireConvexity3Step st g).length = st.length + 1 := by
  cases g <;> simp

/-- Initial `(isConst, isAffine, isConvex)` flags for wires `0..n-1` when the convex variable
occupies `[offset, offset + d)`. -/
def initConvexity3 (n offset d : ℕ) : List (Bool × Bool × Bool) :=
  (List.range n).map fun j =>
    if offset ≤ j ∧ j < offset + d then (false, true, true) else (true, true, true)

theorem initConvexity3_eq (n offset d : ℕ) :
    initConvexity3 n offset d = (List.range n).map fun j =>
      if offset ≤ j ∧ j < offset + d then (false, true, true) else (true, true, true) := by rfl

@[simp]
theorem length_initConvexity3 (n offset d : ℕ) :
    (initConvexity3 n offset d).length = n := by
  simp [initConvexity3]

/-- Syntactic convexity predicate: returns `true` iff output `0` of `C` is guaranteed convex in
the `d` input wires `[offset, offset + d)` (fixing all other inputs). -/
def isSyntacticallyConvexIn (C : LinearArithCircuit) (offset d : ℕ) : Bool :=
  let st := C.gates.foldl wireConvexity3Step (initConvexity3 C.numInputs offset d)
  (st.getD (C.outputs.getD 0 0) (true, true, true)).2.2

theorem isSyntacticallyConvexIn_eq (C : LinearArithCircuit) (offset d : ℕ) :
    isSyntacticallyConvexIn C offset d =
      ((C.gates.foldl wireConvexity3Step (initConvexity3 C.numInputs offset d)).getD
        (C.outputs.getD 0 0) (true, true, true)).2.2 := by rfl

/-- Automatic-differentiation forward pass computing `(wireValue, wireGrad)` in
`[offset, offset + d)` for every wire of a linear arithmetic circuit (over any ordered field
`α`). -/
def autoDiffStep {α : Type*} [Field α] [LinearOrder α] (d : ℕ)
    (st : List (α × List α)) (g : LinearGate) : List (α × List α) :=
  let zvec : List α := List.replicate d 0
  let getV (i : ℕ) : α := (st.getD i (0, zvec)).1
  let getG (i : ℕ) : List α := (st.getD i (0, zvec)).2
  let addV (u v : List α) : List α := (List.range d).map fun j => u.getD j 0 + v.getD j 0
  let subV (u v : List α) : List α := (List.range d).map fun j => u.getD j 0 - v.getD j 0
  let scaleV (c : α) (u : List α) : List α := (List.range d).map fun j => c * u.getD j 0
  let entry : α × List α := match g with
    | .input idx => (getV idx, getG idx)
    | .const q => ((q : α), zvec)
    | .add i j => (getV i + getV j, addV (getG i) (getG j))
    | .sub i j => (getV i - getV j, subV (getG i) (getG j))
    | .scale q i => ((q : α) * getV i, scaleV (q : α) (getG i))
    | .min i j =>
      if getV i ≤ getV j then (getV i, getG i) else (getV j, getG j)
    | .max i j =>
      if getV j ≤ getV i then (getV i, getG i) else (getV j, getG j)
  st ++ [entry]

theorem autoDiffStep_eq {α : Type*} [Field α] [LinearOrder α] (d : ℕ)
    (st : List (α × List α)) (g : LinearGate) :
    autoDiffStep d st g =
      let zvec : List α := List.replicate d 0
      let getV (i : ℕ) : α := (st.getD i (0, zvec)).1
      let getG (i : ℕ) : List α := (st.getD i (0, zvec)).2
      let addV (u v : List α) : List α := (List.range d).map fun j => u.getD j 0 + v.getD j 0
      let subV (u v : List α) : List α := (List.range d).map fun j => u.getD j 0 - v.getD j 0
      let scaleV (c : α) (u : List α) : List α := (List.range d).map fun j => c * u.getD j 0
      st ++ [match g with
        | .input idx => (getV idx, getG idx)
        | .const q => ((q : α), zvec)
        | .add i j => (getV i + getV j, addV (getG i) (getG j))
        | .sub i j => (getV i - getV j, subV (getG i) (getG j))
        | .scale q i => ((q : α) * getV i, scaleV (q : α) (getG i))
        | .min i j => if getV i ≤ getV j then (getV i, getG i) else (getV j, getG j)
        | .max i j => if getV j ≤ getV i then (getV i, getG i) else (getV j, getG j)] := by rfl

@[simp]
theorem length_autoDiffStep {α : Type*} [Field α] [LinearOrder α]
    (d : ℕ) (st : List (α × List α)) (g : LinearGate) :
    (autoDiffStep d st g).length = st.length + 1 := by
  simp [autoDiffStep]

/-- Initial `(value, grad)` list for `autoDiffStep` on input vector `x` when the active variables
occupy wires `[offset, offset + d)`. -/
def initAutoDiff {α : Type*} [Zero α] [One α]
    (n offset d : ℕ) (x : List α) : List (α × List α) :=
  (List.range n).map fun j =>
    (x.getD j 0, (List.range d).map fun k => if j = offset + k then (1 : α) else 0)

theorem initAutoDiff_eq {α : Type*} [Zero α] [One α]
    (n offset d : ℕ) (x : List α) :
    initAutoDiff n offset d x = (List.range n).map fun j =>
      (x.getD j 0, (List.range d).map fun k => if j = offset + k then (1 : α) else 0) := by rfl

@[simp]
theorem length_initAutoDiff {α : Type*} [Zero α] [One α]
    (n offset d : ℕ) (x : List α) :
    (initAutoDiff n offset d x).length = n := by
  simp [initAutoDiff]

/-- Automatic-differentiation subgradient of output `0` of `C` with respect to wires
`[offset, offset + d)` at input `x` (over `ℚ`). -/
def autoDiffGradRat (C : LinearArithCircuit) (offset d : ℕ) (x : List ℚ) : List ℚ :=
  if C.outputs.isEmpty then List.replicate d 0
  else
    let st := C.gates.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d (x.take
    C.numInputs))
    (st.getD (C.outputs.getD 0 0) (0, List.replicate d 0)).2

theorem autoDiffGradRat_eq (C : LinearArithCircuit) (offset d : ℕ) (x : List ℚ) :
    autoDiffGradRat C offset d x =
      if C.outputs.isEmpty then List.replicate d 0
      else
        ((C.gates.foldl (autoDiffStep d)
          (initAutoDiff C.numInputs offset d (x.take C.numInputs))).getD
          (C.outputs.getD 0 0) (0, List.replicate d 0)).2 := by rfl

/-- Automatic-differentiation subgradient over `ℝ`. -/
noncomputable def autoDiffGradReal (C : LinearArithCircuit) (offset d : ℕ) (x : List ℝ) : List ℝ :=
  if C.outputs.isEmpty then List.replicate d 0
  else
    let st := C.gates.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d (x.take
    C.numInputs))
    (st.getD (C.outputs.getD 0 0) (0, List.replicate d 0)).2

/-- **Global subgradient soundness of `autoDiffGradReal`** (standard Lean axioms): whenever
`isSyntacticallyConvexIn C offset d = true` and `u, x : List ℝ` of length `≥ C.numInputs` agree
outside `[offset, offset + d)`, `autoDiffGradReal C offset d x` is a genuine global subgradient
at `x`, i.e., `(evalReal C u)_0 ≥ (evalReal C x)_0 + ∑_{k < d} g_k * (u_{offset+k} - x_{offset+k})`.
-/
theorem autoDiffGradReal_subgradient (C : LinearArithCircuit) (offset d : ℕ)
    (hconv : isSyntacticallyConvexIn C offset d = true)
    {x u : List ℝ} (hxlen : C.numInputs ≤ x.length) (hulen : C.numInputs ≤ u.length)
    (hagree : ∀ j < C.numInputs, ¬ (offset ≤ j ∧ j < offset + d) → u.getD j 0 = x.getD j 0) :
    (evalReal C x).getD 0 0 +
      ((List.range d).map fun k =>
        (autoDiffGradReal C offset d x).getD k 0 *
          (u.getD (offset + k) 0 - x.getD (offset + k) 0)).sum ≤
    (evalReal C u).getD 0 0 := by
  by_cases ho : C.outputs.isEmpty
  · have hnil : C.outputs = [] := List.isEmpty_iff.mp ho
    have hz : ((List.range d).map fun k =>
        (List.replicate d (0 : ℝ)).getD k 0 *
          (u.getD (offset + k) 0 - x.getD (offset + k) 0)).sum = 0 :=
      List.sum_eq_zero fun r hr => by
        rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
        have hkd := List.mem_range.mp hk
        simp [List.getD_eq_getElem?_getD, hkd]
    rw [autoDiffGradReal, ite_eq_left_iff.mpr (fun h => (h ho).elim), evalReal_eq, evalReal_eq,
      hnil, List.map_nil, hz, add_zero]
    simp
  · have hpos : 0 < C.outputs.length := by
      have : C.outputs ≠ [] := fun h => by simp [h] at ho
      exact List.length_pos_of_ne_nil this
    set x' := x.take C.numInputs
    set u' := u.take C.numInputs
    have hx'len : x'.length = C.numInputs := List.length_take_of_le hxlen
    have hu'len : u'.length = C.numInputs := List.length_take_of_le hulen
    have hx'_get : ∀ j < C.numInputs, x'.getD j 0 = x.getD j 0 := fun j hj => by
      simp [x', List.getD_eq_getElem?_getD, hj]
    have hu'_get : ∀ j < C.numInputs, u'.getD j 0 = u.getD j 0 := fun j hj => by
      simp [u', List.getD_eq_getElem?_getD, hj]
    have hagree' : ∀ j < C.numInputs, ¬ (offset ≤ j ∧ j < offset + d) →
        u'.getD j 0 = x'.getD j 0 := fun j hj hn => by
      rw [hu'_get j hj, hx'_get j hj]; exact hagree j hj hn
    let dotGrad (g : List ℝ) : ℝ :=
      ((List.range d).map fun k => g.getD k 0 *
        (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)).sum
    -- Prove the invariant for every wire on `x', u'`:
    -- (1) `(autoDiff_x'.getD i).1 = (evalWires_x').getD i`,
    -- (2) `isConst` ⇒ `evalWires_u' = evalWires_x'` and `grad = 0`,
    -- (3) `isAffine` ⇒ `evalWires_u' = evalWires_x' + ⟨grad, u' - x'⟩`,
    -- (4) `isConvex` ⇒ `evalWires_u' ≥ evalWires_x' + ⟨grad, u' - x'⟩`.
    have hinv : ∀ (gs : List LinearGate),
        let stC := gs.foldl wireConvexity3Step (initConvexity3 C.numInputs offset d)
        let stA := gs.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d x')
        let wX := evalWires gs x'
        let wU := evalWires gs u'
        stC.length = C.numInputs + gs.length ∧
        stA.length = C.numInputs + gs.length ∧
        wX.length = C.numInputs + gs.length ∧
        wU.length = C.numInputs + gs.length ∧
        ∀ i, (stA.getD i (0, List.replicate d 0)).1 = wX.getD i 0 ∧
          ((stC.getD i (true, true, true)).1 = true →
            wU.getD i 0 = wX.getD i 0 ∧
            (∀ k < d, (stA.getD i (0, List.replicate d 0)).2.getD k 0 = 0)) ∧
          ((stC.getD i (true, true, true)).2.1 = true →
            wU.getD i 0 = wX.getD i 0 + dotGrad (stA.getD i (0, List.replicate d 0)).2) ∧
          ((stC.getD i (true, true, true)).2.2 = true →
            wX.getD i 0 + dotGrad (stA.getD i (0, List.replicate d 0)).2 ≤ wU.getD i 0) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        refine ⟨by simp [initConvexity3], by simp [initAutoDiff], by simp [hx'len],
          by simp [hu'len], fun i => ?_⟩
        by_cases hi : i < C.numInputs
        · simp only [List.foldl_nil, evalWires_nil, initConvexity3, initAutoDiff,
            List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
            Option.map_some, Option.getD_some]
          refine ⟨trivial, ?_, ?_, ?_⟩
          · intro hc
            have hnot : ¬ (offset ≤ i ∧ i < offset + d) := by
              intro h; simp [h] at hc
            refine ⟨hagree' i hi hnot, fun k hk => ?_⟩
            simp only [List.getElem?_range hk, Option.map_some, Option.getD_some,
              ite_eq_right_iff]
            intro heq; exfalso; apply hnot; omega
          · intro _
            by_cases hmem : offset ≤ i ∧ i < offset + d
            · have hidx : i - offset < d := by omega
              have hdot : dotGrad ((List.range d).map fun k => if i = offset + k then (1 : ℝ) else
              0) =
                  u'.getD i 0 - x'.getD i 0 := by
                dsimp only [dotGrad]
                have hcongr : ((List.range d).map fun k =>
                      (((List.range d).map fun k' => if i = offset + k' then (1 : ℝ) else 0).getD k
                      0) *
                        (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) =
                    ((List.range d).map fun k =>
                      if k = i - offset then u'.getD i 0 - x'.getD i 0 else 0) := by
                  refine List.map_congr_left fun k hk => ?_
                  have hkd : k < d := List.mem_range.mp hk
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkd,
                    Option.map_some, Option.getD_some]
                  by_cases hki : k = i - offset
                  · subst hki; have : i = offset + (i - offset) := by omega
                    simp [← this]
                  · have : i ≠ offset + k := by omega
                    simp [this, hki]
                rw [hcongr]
                have hsum_single : ∀ (n m : ℕ) (v : ℝ), m < n →
                    ((List.range n).map fun k => if k = m then v else 0).sum = v := by
                  intro n; induction n with
                  | zero => intro m _ hm; omega
                  | succ n ih =>
                    intro m v hm
                    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                      List.sum_singleton]
                    by_cases hmn : m < n
                    · rw [ih m v hmn, ite_eq_right_iff.mpr (by omega), add_zero]
                    · have hmeq : m = n := by omega
                      subst hmeq
                      have hzero : ((List.range m).map fun k => if k = m then v else 0).sum = 0 :=
                        List.sum_eq_zero fun r hr => by
                          rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
                          have := List.mem_range.mp hk; simp [show k ≠ m by omega]
                      rw [hzero, zero_add, ite_eq_left_iff.mpr (fun h => (h rfl).elim)]
                exact hsum_single d (i - offset) _ hidx
              rw [hdot]; simp [List.getD_eq_getElem?_getD]
            · have hdot : dotGrad ((List.range d).map fun k => if i = offset + k then (1 : ℝ) else
            0) = 0 := by
                refine List.sum_eq_zero fun r hr => ?_
                rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
                have hkd : k < d := List.mem_range.mp hk
                simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkd,
                  Option.map_some, Option.getD_some]
                have : i ≠ offset + k := by omega
                simp [this]
              rw [hdot, add_zero, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
              exact hagree' i hi hmem
          · intro _
            by_cases hmem : offset ≤ i ∧ i < offset + d
            · have hidx : i - offset < d := by omega
              have hdot : dotGrad ((List.range d).map fun k => if i = offset + k then (1 : ℝ) else
              0) =
                  u'.getD i 0 - x'.getD i 0 := by
                dsimp only [dotGrad]
                have hcongr : ((List.range d).map fun k =>
                      (((List.range d).map fun k' => if i = offset + k' then (1 : ℝ) else 0).getD k
                      0) *
                        (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) =
                    ((List.range d).map fun k =>
                      if k = i - offset then u'.getD i 0 - x'.getD i 0 else 0) := by
                  refine List.map_congr_left fun k hk => ?_
                  have hkd : k < d := List.mem_range.mp hk
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkd,
                    Option.map_some, Option.getD_some]
                  by_cases hki : k = i - offset
                  · subst hki; have : i = offset + (i - offset) := by omega
                    simp [← this]
                  · have : i ≠ offset + k := by omega
                    simp [this, hki]
                rw [hcongr]
                have hsum_single : ∀ (n m : ℕ) (v : ℝ), m < n →
                    ((List.range n).map fun k => if k = m then v else 0).sum = v := by
                  intro n; induction n with
                  | zero => intro m _ hm; omega
                  | succ n ih =>
                    intro m v hm
                    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                      List.sum_singleton]
                    by_cases hmn : m < n
                    · rw [ih m v hmn, ite_eq_right_iff.mpr (by omega), add_zero]
                    · have hmeq : m = n := by omega
                      subst hmeq
                      have hzero : ((List.range m).map fun k => if k = m then v else 0).sum = 0 :=
                        List.sum_eq_zero fun r hr => by
                          rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
                          have := List.mem_range.mp hk; simp [show k ≠ m by omega]
                      rw [hzero, zero_add, ite_eq_left_iff.mpr (fun h => (h rfl).elim)]
                exact hsum_single d (i - offset) _ hidx
              rw [hdot]; simp [List.getD_eq_getElem?_getD]
            · have hdot : dotGrad ((List.range d).map fun k => if i = offset + k then (1 : ℝ) else
            0) = 0 := by
                refine List.sum_eq_zero fun r hr => ?_
                rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
                have hkd : k < d := List.mem_range.mp hk
                simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkd,
                  Option.map_some, Option.getD_some]
                have : i ≠ offset + k := by omega
                simp [this]
              rw [hdot, add_zero, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD,
                hagree' i hi hmem]
        · have hge : C.numInputs ≤ i := Nat.le_of_not_lt hi
          have hnone : ∀ {β : Type} (l : List β) (def_ : β), l.length ≤ i → l.getD i def_ = def_ :=
          by
            intro β l def_ hl
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
          have hx0 : x'.getD i 0 = 0 := hnone x' 0 (hx'len.symm ▸ hge)
          have hu0 : u'.getD i 0 = 0 := hnone u' 0 (hu'len.symm ▸ hge)
          have hstC0 : (initConvexity3 C.numInputs offset d).getD i (true, true, true) =
              (true, true, true) := hnone _ _ (by simp [initConvexity3, hge])
          have hstA0 : (initAutoDiff C.numInputs offset d x').getD i (0, List.replicate d 0) =
              (0, List.replicate d 0) := hnone _ _ (by simp [initAutoDiff, hge])
          have hdot0 : dotGrad (List.replicate d 0) = 0 :=
            List.sum_eq_zero fun r hr => by
              rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
              have hkd : k < d := List.mem_range.mp hk
              simp [List.getD_eq_getElem?_getD, hkd]
          simp only [List.foldl_nil, evalWires_nil, hx0, hu0, hstC0, hstA0, hdot0, add_zero]
          refine ⟨trivial, fun _ => ⟨trivial, fun k hk => by simp [List.getD_eq_getElem?_getD, hk]⟩,
            fun _ => trivial, fun _ => le_refl _⟩
      | append_singleton gs g ih =>
        obtain ⟨hlC, hlA, hlX, hlU, hih⟩ := ih
        set stC := gs.foldl wireConvexity3Step (initConvexity3 C.numInputs offset d)
        set stA := gs.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d x')
        set wX := evalWires gs x'
        set wU := evalWires gs u'
        have hlen_step : (wireConvexity3Step stC g).length = stC.length + 1 := by
          cases g <;> simp [wireConvexity3Step]
        have hlenA_step : (autoDiffStep d stA g).length = stA.length + 1 := by
          simp [autoDiffStep]
        have hdot_zero : ∀ v : List ℝ, (∀ k < d, v.getD k 0 = 0) → dotGrad v = 0 := fun v hv =>
          List.sum_eq_zero fun r hr => by
            rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
            rw [hv k (List.mem_range.mp hk), zero_mul]
        have hdot_add : ∀ v₁ v₂ : List ℝ,
            dotGrad ((List.range d).map fun j => v₁.getD j 0 + v₂.getD j 0) =
              dotGrad v₁ + dotGrad v₂ := by
          intro v₁ v₂; dsimp only [dotGrad]
          have hmap : ((List.range d).map fun k =>
                (((List.range d).map fun j => v₁.getD j 0 + v₂.getD j 0).getD k 0) *
                  (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) =
              ((List.range d).map fun k =>
                v₁.getD k 0 * (u'.getD (offset + k) 0 - x'.getD (offset + k) 0) +
                v₂.getD k 0 * (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) := by
            refine List.map_congr_left fun k hk => ?_
            have hkd := List.mem_range.mp hk; simp [List.getD_eq_getElem?_getD, hkd]; ring
          rw [hmap]
          induction List.range d with
          | nil => simp
          | cons k ks ih' => simp only [List.map_cons, List.sum_cons, ih']; ring
        have hdot_sub : ∀ v₁ v₂ : List ℝ,
            dotGrad ((List.range d).map fun j => v₁.getD j 0 - v₂.getD j 0) =
              dotGrad v₁ - dotGrad v₂ := by
          intro v₁ v₂; dsimp only [dotGrad]
          have hmap : ((List.range d).map fun k =>
                (((List.range d).map fun j => v₁.getD j 0 - v₂.getD j 0).getD k 0) *
                  (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) =
              ((List.range d).map fun k =>
                v₁.getD k 0 * (u'.getD (offset + k) 0 - x'.getD (offset + k) 0) -
                v₂.getD k 0 * (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) := by
            refine List.map_congr_left fun k hk => ?_
            have hkd := List.mem_range.mp hk; simp [List.getD_eq_getElem?_getD, hkd]; ring
          rw [hmap]
          induction List.range d with
          | nil => simp
          | cons k ks ih' => simp only [List.map_cons, List.sum_cons, ih']; ring
        have hdot_scale : ∀ (c : ℝ) (v : List ℝ),
            dotGrad ((List.range d).map fun j => c * v.getD j 0) = c * dotGrad v := by
          intro c v; dsimp only [dotGrad]
          have hmap : ((List.range d).map fun k =>
                (((List.range d).map fun j => c * v.getD j 0).getD k 0) *
                  (u'.getD (offset + k) 0 - x'.getD (offset + k) 0)) =
              ((List.range d).map fun k =>
                c * (v.getD k 0 * (u'.getD (offset + k) 0 - x'.getD (offset + k) 0))) := by
            refine List.map_congr_left fun k hk => ?_
            have hkd := List.mem_range.mp hk; simp [List.getD_eq_getElem?_getD, hkd]; ring
          rw [hmap]
          induction List.range d with
          | nil => simp
          | cons k ks ih' => simp only [List.map_cons, List.sum_cons, ih']; ring
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, evalWires_append,
          evalWires_cons, evalWires_nil, List.length_append, List.length_singleton]
        refine ⟨by rw [hlen_step, hlC]; omega, by rw [hlenA_step, hlA]; omega,
          by rw [hlX]; omega, by rw [hlU]; omega, fun i => ?_⟩
        set N := C.numInputs + gs.length
        by_cases hi : i < N
        · have hC_i : (wireConvexity3Step stC g).getD i (true, true, true) =
              stC.getD i (true, true, true) := by
            cases g <;> simp [wireConvexity3Step, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (hlC.symm ▸ hi)]
          have hA_i : (autoDiffStep d stA g).getD i (0, List.replicate d 0) =
              stA.getD i (0, List.replicate d 0) := by
            simp [autoDiffStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (hlA.symm ▸
            hi)]
          have hX_i : (wX ++ [evalGate wX g]).getD i 0 = wX.getD i 0 := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlX.symm ▸ hi)]
          have hU_i : (wU ++ [evalGate wU g]).getD i 0 = wU.getD i 0 := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlU.symm ▸ hi)]
          rw [hC_i, hA_i, hX_i, hU_i]
          exact hih i
        · rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with rfl | hgt
          · have hX_l : (wX ++ [evalGate wX g]).getD N 0 = evalGate wX g := by
              simp [List.getD_eq_getElem?_getD, ← hlX]
            have hU_l : (wU ++ [evalGate wU g]).getD N 0 = evalGate wU g := by
              simp [List.getD_eq_getElem?_getD, ← hlU]
            have hA_l : (autoDiffStep d stA g).getD N (0, List.replicate d 0) =
                match g with
                | .input idx => ((stA.getD idx (0, List.replicate d 0)).1,
                    (stA.getD idx (0, List.replicate d 0)).2)
                | .const q => ((q : ℝ), List.replicate d 0)
                | .add i j => ((stA.getD i (0, List.replicate d 0)).1 +
                      (stA.getD j (0, List.replicate d 0)).1,
                    (List.range d).map fun k =>
                      (stA.getD i (0, List.replicate d 0)).2.getD k 0 +
                      (stA.getD j (0, List.replicate d 0)).2.getD k 0)
                | .sub i j => ((stA.getD i (0, List.replicate d 0)).1 -
                      (stA.getD j (0, List.replicate d 0)).1,
                    (List.range d).map fun k =>
                      (stA.getD i (0, List.replicate d 0)).2.getD k 0 -
                      (stA.getD j (0, List.replicate d 0)).2.getD k 0)
                | .scale q i => ((q : ℝ) * (stA.getD i (0, List.replicate d 0)).1,
                    (List.range d).map fun k =>
                      (q : ℝ) * (stA.getD i (0, List.replicate d 0)).2.getD k 0)
                | .min i j => if (stA.getD i (0, List.replicate d 0)).1 ≤
                      (stA.getD j (0, List.replicate d 0)).1
                    then stA.getD i (0, List.replicate d 0) else stA.getD j (0, List.replicate d 0)
                | .max i j => if (stA.getD j (0, List.replicate d 0)).1 ≤
                      (stA.getD i (0, List.replicate d 0)).1
                    then stA.getD i (0, List.replicate d 0) else stA.getD j (0, List.replicate d 0)
                    := by
              simp only [autoDiffStep, List.getD_eq_getElem?_getD, ← hlA,
                List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
                Option.getD_some]
              cases g <;> rfl
            rw [hX_l, hU_l, hA_l]
            cases g with
            | input idx =>
              have hC_l : (wireConvexity3Step stC (.input idx)).getD N (true, true, true) =
                  stC.getD idx (true, true, true) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]; simpa using hih idx
            | const q =>
              have hC_l : (wireConvexity3Step stC (.const q)).getD N (true, true, true) =
                  (true, true, true) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]
              refine ⟨by simp,
                fun _ => ⟨by simp, fun k hk => by simp [List.getD_eq_getElem?_getD, hk]⟩,
                fun _ => by
                  rw [hdot_zero _ (fun k hk => by simp [List.getD_eq_getElem?_getD, hk]), add_zero]
                  simp,
                fun _ => by
                  rw [hdot_zero _ (fun k hk => by simp [List.getD_eq_getElem?_getD, hk]), add_zero]
                  simp⟩
            | add i j =>
              have hC_l : (wireConvexity3Step stC (.add i j)).getD N (true, true, true) =
                  ((stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1,
                   (stC.getD i (true, true, true)).2.1 && (stC.getD j (true, true, true)).2.1,
                   (stC.getD i (true, true, true)).2.2 && (stC.getD j (true, true, true)).2.2) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]
              obtain ⟨h1i, hci, hai, hvi⟩ := hih i
              obtain ⟨h1j, hcj, haj, hvj⟩ := hih j
              refine ⟨by dsimp only; rw [evalGate_add, h1i, h1j], ?_, ?_, ?_⟩
              · intro h; simp only [Bool.and_eq_true] at h
                refine ⟨by rw [evalGate_add, evalGate_add, (hci h.1).1, (hcj h.2).1],
                  fun k hk => ?_⟩
                dsimp only
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
                  Option.map_some, Option.getD_some, (hci h.1).2 k hk, (hcj h.2).2 k hk, add_zero]
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                rw [hdot_add, evalGate_add, evalGate_add, hai h.1, haj h.2]; ring
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                rw [hdot_add, evalGate_add, evalGate_add]; linarith [hvi h.1, hvj h.2]
            | sub i j =>
              have hC_l : (wireConvexity3Step stC (.sub i j)).getD N (true, true, true) =
                  ((stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1,
                   (stC.getD i (true, true, true)).2.1 && (stC.getD j (true, true, true)).2.1,
                   (stC.getD i (true, true, true)).2.2 && (stC.getD j (true, true, true)).2.1) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]
              obtain ⟨h1i, hci, hai, hvi⟩ := hih i
              obtain ⟨h1j, hcj, haj, hvj⟩ := hih j
              refine ⟨by dsimp only; rw [evalGate_sub, h1i, h1j], ?_, ?_, ?_⟩
              · intro h; simp only [Bool.and_eq_true] at h
                refine ⟨by rw [evalGate_sub, evalGate_sub, (hci h.1).1, (hcj h.2).1],
                  fun k hk => ?_⟩
                dsimp only
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
                  Option.map_some, Option.getD_some, (hci h.1).2 k hk, (hcj h.2).2 k hk, sub_zero]
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                rw [hdot_sub, evalGate_sub, evalGate_sub, hai h.1, haj h.2]; ring
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                rw [hdot_sub, evalGate_sub, evalGate_sub, haj h.2]; linarith [hvi h.1]
            | scale q i =>
              have hC_l : (wireConvexity3Step stC (.scale q i)).getD N (true, true, true) =
                  ((stC.getD i (true, true, true)).1,
                   (stC.getD i (true, true, true)).2.1,
                   if 0 ≤ q then (stC.getD i (true, true, true)).2.2
                   else (stC.getD i (true, true, true)).2.1) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]
              obtain ⟨h1i, hci, hai, hvi⟩ := hih i
              refine ⟨by dsimp only; rw [evalGate_scale, h1i], ?_, ?_, ?_⟩
              · intro h
                refine ⟨by rw [evalGate_scale, evalGate_scale, (hci h).1], fun k hk => ?_⟩
                dsimp only
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
                  Option.map_some, Option.getD_some, (hci h).2 k hk, mul_zero]
              · intro h; dsimp only; rw [hdot_scale, evalGate_scale, evalGate_scale, hai h]; ring
              · intro h; dsimp only; rw [hdot_scale, evalGate_scale, evalGate_scale]
                by_cases hq : 0 ≤ q
                · simp only [hq, ↓reduceIte] at h
                  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
                  nlinarith [hvi h]
                · simp only [hq, ↓reduceIte] at h
                  rw [hai h]; linarith
            | min i j =>
              have hC_l : (wireConvexity3Step stC (.min i j)).getD N (true, true, true) =
                  ((stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1,
                   (stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1,
                   (stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]
              obtain ⟨h1i, hci, _, _⟩ := hih i
              obtain ⟨h1j, hcj, _, _⟩ := hih j
              refine ⟨by
                dsimp only; rw [evalGate_min, h1i, h1j]
                split_ifs with hle
                · rw [min_eq_left hle]; exact h1i
                · rw [min_eq_right (le_of_not_ge hle)]; exact h1j, ?_, ?_, ?_⟩
              · intro h; simp only [Bool.and_eq_true] at h
                refine ⟨by rw [evalGate_min, evalGate_min, (hci h.1).1, (hcj h.2).1],
                  fun k hk => ?_⟩
                dsimp only; split_ifs <;> [exact (hci h.1).2 k hk; exact (hcj h.2).2 k hk]
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                split_ifs
                · rw [hdot_zero _ (hci h.1).2, add_zero, evalGate_min, evalGate_min,
                    (hci h.1).1, (hcj h.2).1]
                · rw [hdot_zero _ (hcj h.2).2, add_zero, evalGate_min, evalGate_min,
                    (hci h.1).1, (hcj h.2).1]
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                split_ifs
                · rw [hdot_zero _ (hci h.1).2, add_zero, evalGate_min, evalGate_min,
                    (hci h.1).1, (hcj h.2).1]
                · rw [hdot_zero _ (hcj h.2).2, add_zero, evalGate_min, evalGate_min,
                    (hci h.1).1, (hcj h.2).1]
            | max i j =>
              have hC_l : (wireConvexity3Step stC (.max i j)).getD N (true, true, true) =
                  ((stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1,
                   (stC.getD i (true, true, true)).1 && (stC.getD j (true, true, true)).1,
                   (stC.getD i (true, true, true)).2.2 && (stC.getD j (true, true, true)).2.2) := by
                simp [wireConvexity3Step, List.getD_eq_getElem?_getD, ← hlC]
              rw [hC_l]
              obtain ⟨h1i, hci, _, hvi⟩ := hih i
              obtain ⟨h1j, hcj, _, hvj⟩ := hih j
              refine ⟨by
                dsimp only; rw [evalGate_max, h1i, h1j]
                split_ifs with hle
                · rw [max_eq_left hle]; exact h1i
                · rw [max_eq_right (le_of_not_ge hle)]; exact h1j, ?_, ?_, ?_⟩
              · intro h; simp only [Bool.and_eq_true] at h
                refine ⟨by rw [evalGate_max, evalGate_max, (hci h.1).1, (hcj h.2).1],
                  fun k hk => ?_⟩
                dsimp only; split_ifs <;> [exact (hci h.1).2 k hk; exact (hcj h.2).2 k hk]
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                split_ifs
                · rw [hdot_zero _ (hci h.1).2, add_zero, evalGate_max, evalGate_max,
                    (hci h.1).1, (hcj h.2).1]
                · rw [hdot_zero _ (hcj h.2).2, add_zero, evalGate_max, evalGate_max,
                    (hci h.1).1, (hcj h.2).1]
              · intro h; simp only [Bool.and_eq_true] at h
                dsimp only
                rw [evalGate_max, evalGate_max, h1i, h1j]
                split_ifs with hle
                · rw [max_eq_left hle]; exact (hvi h.1).trans (le_max_left _ _)
                · rw [max_eq_right (le_of_not_ge hle)]; exact (hvj h.2).trans (le_max_right _ _)
          · have hnone : ∀ {β : Type} (l : List β) (def_ : β), l.length ≤ i → l.getD i def_ = def_
          :=
              fun l def_ hl => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
            have hC0 : (wireConvexity3Step stC g).getD i (true, true, true) = (true, true, true) :=
              hnone _ _ (by rw [hlen_step, hlC]; omega)
            have hA0 : (autoDiffStep d stA g).getD i (0, List.replicate d 0) =
                (0, List.replicate d 0) := hnone _ _ (by rw [hlenA_step, hlA]; omega)
            have hX0 : (wX ++ [evalGate wX g]).getD i 0 = 0 := hnone _ _ (by simp [hlX]; omega)
            have hU0 : (wU ++ [evalGate wU g]).getD i 0 = 0 := hnone _ _ (by simp [hlU]; omega)
            rw [hC0, hA0, hX0, hU0]
            have hz : dotGrad (List.replicate d 0) = 0 :=
              hdot_zero _ (fun k hk => by simp [List.getD_eq_getElem?_getD, hk])
            rw [hz, add_zero]
            refine ⟨rfl, fun _ => ⟨rfl, fun k hk => by simp [List.getD_eq_getElem?_getD, hk]⟩,
              fun _ => rfl, fun _ => le_refl _⟩
    have hmain := ((hinv C.gates).2.2.2.2 (C.outputs.getD 0 0)).2.2.2 hconv
    have hgetX : (evalReal C x).getD 0 0 = (evalWires C.gates x').getD (C.outputs.getD 0 0) 0 := by
      simp [evalReal_eq, x', List.getD_eq_getElem?_getD, hpos]
    have hgetU : (evalReal C u).getD 0 0 = (evalWires C.gates u').getD (C.outputs.getD 0 0) 0 := by
      simp [evalReal_eq, u', List.getD_eq_getElem?_getD, hpos]
    rw [hgetX, hgetU]
    have hgrad_eq : ((List.range d).map fun k =>
          (autoDiffGradReal C offset d x).getD k 0 *
            (u.getD (offset + k) 0 - x.getD (offset + k) 0)).sum =
        dotGrad ((C.gates.foldl (autoDiffStep d)
          (initAutoDiff C.numInputs offset d x')).getD (C.outputs.getD 0 0)
          (0, List.replicate d 0)).2 := by
      -- For `offset + k < C.numInputs`, `u'`/`x'` match `u`/`x`; for `offset + k ≥ C.numInputs`,
      -- wire `offset + k` never appears as an active variable in `initAutoDiff`, so `grad_k = 0`!
      have hgrad_zero_oob : ∀ (gs : List LinearGate) (i k : ℕ),
          k < d → C.numInputs ≤ offset + k →
          ((gs.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d x')).getD i
            (0, List.replicate d 0)).2.getD k 0 = 0 := by
        intro gs; induction gs using List.reverseRecOn with
        | nil =>
          intro i k hk hge
          by_cases hi : i < C.numInputs
          · simp [initAutoDiff, List.getD_eq_getElem?_getD, hi, hk, show i ≠ offset + k by omega]
          · have hinit0 : (initAutoDiff C.numInputs offset d x').getD i (0, List.replicate d 0) =
                (0, List.replicate d 0) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [initAutoDiff]; omega)]
              rfl
            rw [List.foldl_nil, hinit0]
            simp [List.getD_eq_getElem?_getD, hk]
        | append_singleton gs g ih =>
          intro i k hk hge
          set stA := gs.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d x')
          have hlA : stA.length = C.numInputs + gs.length := (hinv gs).2.1
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
          by_cases hi : i < stA.length
          · rw [show (autoDiffStep d stA g).getD i (0, List.replicate d 0) =
                stA.getD i (0, List.replicate d 0) by
              simp [autoDiffStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]]
            exact ih i k hk hge
          · rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with rfl | hgt
            · have hA_l : (autoDiffStep d stA g).getD stA.length (0, List.replicate d 0) =
                  match g with
                  | .input idx => stA.getD idx (0, List.replicate d 0)
                  | .const q => ((q : ℝ), List.replicate d 0)
                  | .add a b => ((stA.getD a (0, List.replicate d 0)).1 +
                        (stA.getD b (0, List.replicate d 0)).1,
                      (List.range d).map fun j =>
                        (stA.getD a (0, List.replicate d 0)).2.getD j 0 +
                        (stA.getD b (0, List.replicate d 0)).2.getD j 0)
                  | .sub a b => ((stA.getD a (0, List.replicate d 0)).1 -
                        (stA.getD b (0, List.replicate d 0)).1,
                      (List.range d).map fun j =>
                        (stA.getD a (0, List.replicate d 0)).2.getD j 0 -
                        (stA.getD b (0, List.replicate d 0)).2.getD j 0)
                  | .scale q a => ((q : ℝ) * (stA.getD a (0, List.replicate d 0)).1,
                      (List.range d).map fun j =>
                        (q : ℝ) * (stA.getD a (0, List.replicate d 0)).2.getD j 0)
                  | .min a b => if (stA.getD a (0, List.replicate d 0)).1 ≤
                        (stA.getD b (0, List.replicate d 0)).1
                      then stA.getD a (0, List.replicate d 0)
                      else stA.getD b (0, List.replicate d 0)
                  | .max a b => if (stA.getD b (0, List.replicate d 0)).1 ≤
                        (stA.getD a (0, List.replicate d 0)).1
                      then stA.getD a (0, List.replicate d 0)
                      else stA.getD b (0, List.replicate d 0)
                      := by
                simp only [autoDiffStep, List.getD_eq_getElem?_getD,
                  List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
                  Option.getD_some]
              rw [hA_l]
              cases g with
              | input idx => exact ih idx k hk hge
              | const _ => simp [List.getD_eq_getElem?_getD, hk]
              | add a b =>
                dsimp only
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
                  Option.map_some, Option.getD_some, ih a k hk hge, ih b k hk hge, add_zero]
              | sub a b =>
                dsimp only
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
                  Option.map_some, Option.getD_some, ih a k hk hge, ih b k hk hge, sub_zero]
              | scale q a =>
                dsimp only
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
                  Option.map_some, Option.getD_some, ih a k hk hge, mul_zero]
              | min a b =>
                dsimp only; split_ifs <;> [exact ih a k hk hge; exact ih b k hk hge]
              | max a b =>
                dsimp only; split_ifs <;> [exact ih a k hk hge; exact ih b k hk hge]
            · have hA0 : (autoDiffStep d stA g).getD i (0, List.replicate d 0) =
                  (0, List.replicate d 0) := by
                rw [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by simp [autoDiffStep]; omega)]
                rfl
              rw [hA0]
              simp [List.getD_eq_getElem?_getD, hk]
      simp only [autoDiffGradReal, ho, Bool.false_eq_true, ↓reduceIte, dotGrad]
      refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
      have hkd := List.mem_range.mp hk
      by_cases hlt : offset + k < C.numInputs
      · rw [hu'_get _ hlt, hx'_get _ hlt]
      · rw [hgrad_zero_oob C.gates _ k hkd (Nat.le_of_not_lt hlt), zero_mul, zero_mul]
    rw [hgrad_eq]
    exact hmain

/-- Real automatic-differentiation subgradient coincides with rational `autoDiffGradRat` cast to
`ℝ`. -/
theorem autoDiffGradReal_eq_rat (C : LinearArithCircuit) (offset d : ℕ) (x : List ℚ) :
    autoDiffGradReal C offset d (x.map fun q : ℚ => (q : ℝ)) =
      (autoDiffGradRat C offset d x).map fun q : ℚ => (q : ℝ) := by
  have hcast : ∀ (gs : List LinearGate) (st : List (ℚ × List ℚ)),
      gs.foldl (autoDiffStep d) (st.map fun p => ((p.1 : ℝ), p.2.map fun q : ℚ => (q : ℝ))) =
      (gs.foldl (autoDiffStep d) st).map fun p => ((p.1 : ℝ), p.2.map fun q : ℚ => (q : ℝ)) := by
    intro gs
    induction gs with
    | nil => intro st; simp
    | cons g t ih =>
      intro st
      simp only [List.foldl_cons]
      have hstep : autoDiffStep d (st.map fun p => ((p.1 : ℝ), p.2.map fun q : ℚ => (q : ℝ))) g =
          (autoDiffStep d st g).map fun p => ((p.1 : ℝ), p.2.map fun q : ℚ => (q : ℝ)) := by
        have hget : ∀ i,
            ((st.map fun p => ((p.1 : ℝ), p.2.map fun q : ℚ => (q : ℝ))).getD i
              (0, List.replicate d 0)) =
            (((st.getD i (0, List.replicate d 0)).1 : ℝ),
              (st.getD i (0, List.replicate d 0)).2.map fun q : ℚ => (q : ℝ)) := by
          intro i
          by_cases hi : i < st.length
          · simp [List.getD_eq_getElem?_getD, hi]
          · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
        have hgetL : ∀ (l : List ℚ) (j : ℕ),
            (l.map fun q : ℚ => (q : ℝ)).getD j 0 = ((l.getD j 0 : ℚ) : ℝ) := by
          intro l; induction l with
          | nil => intro j; simp
          | cons a s ih' => intro j; cases j with | zero => simp | succ k => simpa using ih' k
        cases g <;>
          simp only [autoDiffStep, List.map_append, List.map_singleton, hget, List.map_map,
            Function.comp_def, hgetL, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_le,
            Rat.cast_id, List.map_replicate, Rat.cast_zero]
        · split_ifs <;> rfl
        · split_ifs <;> rfl
      rw [hstep]
      exact ih _
  by_cases ho : C.outputs.isEmpty
  · simp [autoDiffGradReal, autoDiffGradRat, ho]
  · simp only [autoDiffGradReal, autoDiffGradRat, ho, Bool.false_eq_true, ↓reduceIte]
    have hinit : initAutoDiff C.numInputs offset d ((x.map fun q : ℚ => (q : ℝ)).take C.numInputs) =
        (initAutoDiff C.numInputs offset d (x.take C.numInputs)).map
          fun p => ((p.1 : ℝ), p.2.map fun q : ℚ => (q : ℝ)) := by
      have hgetL : ∀ (l : List ℚ) (j : ℕ),
          (l.map fun q : ℚ => (q : ℝ)).getD j 0 = ((l.getD j 0 : ℚ) : ℝ) := by
        intro l; induction l with
        | nil => intro j; simp
        | cons a s ih' => intro j; cases j with | zero => simp | succ k => simpa using ih' k
      simp only [initAutoDiff, ← List.map_take, List.map_map, Function.comp_def, hgetL]
      refine List.map_congr_left fun j _ => ?_
      congr 1; refine List.map_congr_left fun k _ => ?_; split_ifs <;> simp
    rw [hinit, hcast]
    set st := C.gates.foldl (autoDiffStep d) (initAutoDiff C.numInputs offset d (x.take
    C.numInputs))
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases st[C.outputs[0]?.getD 0]? <;> simp


end CslibFrontier.Computability.Circuit
