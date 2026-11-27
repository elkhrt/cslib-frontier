/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.EditDistance.Grid
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Bounds.Defs

/-!
# Dynamic Time Warping: Bellman Optimality and Complexity Scaling

This module formalizes Dynamic Time Warping (DTW) sequence alignment over ordered additive
monoids via Bellman's dynamic-programming recurrence and connects it to the two-row suffix
`GridDP` combinator of `CslibFrontier.Algorithms.Lean.EditDistance.Grid`, together with the
combinatorial state-space scaling separating exact multi-sequence DTW (`T ^ N`) from
pairwise alignment (`N * T ^ 2`) and fixed-window kernel alignment (`(2 * W + 1) * N * T`).

## Main definitions

* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.IsWarpingStep`,
  `IsWarpingPathTo`, `IsWarpingPath`: valid 1-step monotone, continuous, boundary-anchored
  DTW warping paths on `ℕ × ℕ`.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.warpingPathCost`: cumulative local
  alignment cost along a warping path.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.dtwPrefix`, `optWarpingPath`: Bellman
  prefix dynamic-programming table and optimal traceback path.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.dtwGridDP`, `dtwList`: two-row suffix
  `GridDP` instantiation for DTW on `List α` valued in `WithTop R`.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.multiDtwGridSize`,
  `pairwiseDtwGridSize`, `windowedKernelGridSize`: exact cell/evaluation counts for
  `N`-way exact DTW, `N` pairwise DTW tables, and radius-`W` windowed alignment.

## Main results

* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.isWarpingPathTo_iff`: equivalence of
  inductive warping-path generation and boundary-and-chain DTW constraints.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.isLeast_dtwPrefix`: `dtwPrefix` computes
  the least cost over all valid DTW warping paths.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.dtwList_revPrefix_eq`: agreement between
  `dtwList` (`GridDP`) and `dtwPrefix`.
* `CslibFrontier.Algorithms.Lean.DynamicTimeWarping.two_pow_le_multiDtwGridSize`,
  `windowedKernelGridSize_lt_pairwiseDtwGridSize`: exponential lower bound `2 ^ N ≤ T ^ N`
  for multi-sequence DTW (`T ≥ 2`) versus strict linear-over-quadratic reduction
  `(2 * W + 1) * N * T < N * T ^ 2` for `2 * W + 1 < T`.
-/

public section

namespace CslibFrontier.Algorithms.Lean.DynamicTimeWarping

/-- Single-step monotonicity and 1-step continuity on `ℕ × ℕ`: each transition advances
diagonally `(i + 1, j + 1)`, vertically `(i + 1, j)`, or horizontally `(i, j + 1)`. -/
def IsWarpingStep (uv u'v' : ℕ × ℕ) : Prop :=
  u'v' = (uv.1 + 1, uv.2 + 1) ∨ u'v' = (uv.1 + 1, uv.2) ∨ u'v' = (uv.1, uv.2 + 1)

/-- Inductive characterization of valid DTW warping paths from `(0, 0)` to `(m, n)`. -/
inductive IsWarpingPathTo : ℕ → ℕ → List (ℕ × ℕ) → Prop
  /-- Origin path `[(0, 0)]`. -/
  | start : IsWarpingPathTo 0 0 [(0, 0)]
  /-- Diagonal step `(i, j) → (i + 1, j + 1)`. -/
  | diag {i j : ℕ} {p : List (ℕ × ℕ)} :
      IsWarpingPathTo i j p → IsWarpingPathTo (i + 1) (j + 1) (p ++ [(i + 1, j + 1)])
  /-- Vertical step `(i, j) → (i + 1, j)`. -/
  | vert {i j : ℕ} {p : List (ℕ × ℕ)} :
      IsWarpingPathTo i j p → IsWarpingPathTo (i + 1) j (p ++ [(i + 1, j)])
  /-- Horizontal step `(i, j) → (i, j + 1)`. -/
  | horiz {i j : ℕ} {p : List (ℕ × ℕ)} :
      IsWarpingPathTo i j p → IsWarpingPathTo i (j + 1) (p ++ [(i, j + 1)])

/-- Declarative boundary-and-chain predicate for valid DTW warping paths from `(0, 0)` to
`(m, n)`. -/
def IsWarpingPath (m n : ℕ) (p : List (ℕ × ℕ)) : Prop :=
  p.head? = some (0, 0) ∧ p.getLast? = some (m, n) ∧ p.IsChain IsWarpingStep

private lemma ne_nil_of_isWarpingPathTo {m n : ℕ} {p : List (ℕ × ℕ)}
    (h : IsWarpingPathTo m n p) : p ≠ [] := by
  cases h <;> simp

private lemma head?_of_isWarpingPathTo {m n : ℕ} {p : List (ℕ × ℕ)}
    (h : IsWarpingPathTo m n p) : p.head? = some (0, 0) := by
  induction h with
  | start => rfl
  | diag hp ih | vert hp ih | horiz hp ih =>
    rw [List.head?_append_of_ne_nil _ (ne_nil_of_isWarpingPathTo hp)]
    exact ih

private lemma getLast?_of_isWarpingPathTo {m n : ℕ} {p : List (ℕ × ℕ)}
    (h : IsWarpingPathTo m n p) : p.getLast? = some (m, n) := by
  cases h <;> simp

private lemma isChain_snoc_step {p : List (ℕ × ℕ)} {a b : ℕ × ℕ}
    (hp : p.IsChain IsWarpingStep) (hlast : p.getLast? = some a)
    (hab : IsWarpingStep a b) : (p ++ [b]).IsChain IsWarpingStep := by
  rw [List.isChain_append]
  refine ⟨hp, List.isChain_singleton b, ?_⟩
  intro x hx y hy
  rw [hlast] at hx
  injection hx with hx'
  injection hy with hy'
  subst hx' hy'
  exact hab

private lemma isChain_of_isWarpingPathTo {m n : ℕ} {p : List (ℕ × ℕ)}
    (h : IsWarpingPathTo m n p) : p.IsChain IsWarpingStep := by
  induction h with
  | start => exact List.isChain_singleton (0, 0)
  | diag hp ih =>
    exact isChain_snoc_step ih (getLast?_of_isWarpingPathTo hp) (Or.inl rfl)
  | vert hp ih =>
    exact isChain_snoc_step ih (getLast?_of_isWarpingPathTo hp) (Or.inr (Or.inl rfl))
  | horiz hp ih =>
    exact isChain_snoc_step ih (getLast?_of_isWarpingPathTo hp) (Or.inr (Or.inr rfl))

/-- Equivalence of `IsWarpingPathTo` and `IsWarpingPath`. -/
theorem isWarpingPathTo_iff (m n : ℕ) (p : List (ℕ × ℕ)) :
    IsWarpingPathTo m n p ↔ IsWarpingPath m n p := by
  constructor
  · intro h
    exact ⟨head?_of_isWarpingPathTo h, getLast?_of_isWarpingPathTo h,
      isChain_of_isWarpingPathTo h⟩
  · revert m n
    induction p using List.reverseRecOn with
    | nil =>
      rintro m n ⟨hhead, _, _⟩
      simp at hhead
    | append_singleton p' last ih =>
      rintro m n ⟨hhead, hlast, hchain⟩
      simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ []),
        List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      rcases p' with _ | ⟨hd, tl⟩
      · simp only [List.nil_append, List.head?_singleton, Option.some.injEq,
          Prod.mk.injEq] at hhead
        rcases hhead with ⟨rfl, rfl⟩
        exact IsWarpingPathTo.start
      · have hne : hd :: tl ≠ [] := List.cons_ne_nil hd tl
        rw [List.head?_append_of_ne_nil _ hne] at hhead
        rw [List.isChain_append] at hchain
        rcases hchain with ⟨hchain', _, hlink⟩
        let prev := (hd :: tl).getLast hne
        have hprev_opt : (hd :: tl).getLast? = some prev := List.getLast?_eq_some_getLast hne
        have hstep : IsWarpingStep prev (m, n) := hlink prev hprev_opt (m, n) (by simp)
        have hp' : IsWarpingPathTo prev.1 prev.2 (hd :: tl) :=
          ih prev.1 prev.2 ⟨hhead, by simpa using hprev_opt, hchain'⟩
        rcases prev with ⟨i, j⟩
        rcases hstep with h1 | h2 | h3
        · injection h1 with hi hj
          subst hi hj
          exact IsWarpingPathTo.diag hp'
        · injection h2 with hi hj
          subst hi hj
          exact IsWarpingPathTo.vert hp'
        · injection h3 with hi hj
          subst hi hj
          exact IsWarpingPathTo.horiz hp'

section Bellman

variable {α β R : Type*}

/-- Cumulative cost of a warping path `p` under local cost `c`. -/
def warpingPathCost [AddCommMonoid R] (c : α → β → R) (x : ℕ → α) (y : ℕ → β)
    (p : List (ℕ × ℕ)) : R :=
  (p.map fun uv ↦ c (x uv.1) (y uv.2)).sum

/-- Bellman prefix dynamic-programming table for DTW. -/
def dtwPrefix [AddCommMonoid R] [LinearOrder R] (c : α → β → R) (x : ℕ → α) (y : ℕ → β) :
    ℕ → ℕ → R
  | 0, 0 => c (x 0) (y 0)
  | i + 1, 0 => dtwPrefix c x y i 0 + c (x (i + 1)) (y 0)
  | 0, j + 1 => dtwPrefix c x y 0 j + c (x 0) (y (j + 1))
  | i + 1, j + 1 =>
      min (dtwPrefix c x y i j) (min (dtwPrefix c x y i (j + 1)) (dtwPrefix c x y (i + 1) j)) +
        c (x (i + 1)) (y (j + 1))

/-- Optimal DTW warping path extracted from `dtwPrefix` by Bellman traceback. -/
def optWarpingPath [AddCommMonoid R] [LinearOrder R] (c : α → β → R)
    (x : ℕ → α) (y : ℕ → β) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, 0 => [(0, 0)]
  | i + 1, 0 => optWarpingPath c x y i 0 ++ [(i + 1, 0)]
  | 0, j + 1 => optWarpingPath c x y 0 j ++ [(0, j + 1)]
  | i + 1, j + 1 =>
      let d := dtwPrefix c x y i j
      let u := dtwPrefix c x y i (j + 1)
      let l := dtwPrefix c x y (i + 1) j
      if d ≤ min u l then optWarpingPath c x y i j ++ [(i + 1, j + 1)]
      else if u ≤ l then optWarpingPath c x y i (j + 1) ++ [(i + 1, j + 1)]
      else optWarpingPath c x y (i + 1) j ++ [(i + 1, j + 1)]

private lemma warpingPathCost_append [AddCommMonoid R] (c : α → β → R) (x : ℕ → α)
    (y : ℕ → β) (p q : List (ℕ × ℕ)) :
    warpingPathCost c x y (p ++ q) = warpingPathCost c x y p + warpingPathCost c x y q := by
  simp only [warpingPathCost, List.map_append, List.sum_append]

/-- Lower bound: every valid DTW warping path to `(m, n)` costs at least `dtwPrefix c x y m n`. -/
theorem dtwPrefix_le_warpingPathCost [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
    (c : α → β → R) (x : ℕ → α) (y : ℕ → β) {m n : ℕ} {p : List (ℕ × ℕ)}
    (hp : IsWarpingPath m n p) :
    dtwPrefix c x y m n ≤ warpingPathCost c x y p := by
  have hto : IsWarpingPathTo m n p := (isWarpingPathTo_iff m n p).mpr hp
  clear hp
  induction hto with
  | start => simp [dtwPrefix, warpingPathCost]
  | @diag i j p' _ ih =>
    rw [dtwPrefix, warpingPathCost_append]
    simp only [warpingPathCost, List.map_singleton, List.sum_singleton]
    exact (add_le_add_left (min_le_left _ _) _).trans (add_le_add_left ih _)
  | @vert i j p' _ ih =>
    rw [warpingPathCost_append]
    simp only [warpingPathCost, List.map_singleton, List.sum_singleton]
    cases j with
    | zero =>
      rw [dtwPrefix]
      exact add_le_add_left ih _
    | succ j =>
      rw [dtwPrefix]
      exact (add_le_add_left ((min_le_right _ _).trans (min_le_left _ _)) _).trans
        (add_le_add_left ih _)
  | @horiz i j p' _ ih =>
    rw [warpingPathCost_append]
    simp only [warpingPathCost, List.map_singleton, List.sum_singleton]
    cases i with
    | zero =>
      rw [dtwPrefix]
      exact add_le_add_left ih _
    | succ i =>
      rw [dtwPrefix]
      exact (add_le_add_left ((min_le_right _ _).trans (min_le_right _ _)) _).trans
        (add_le_add_left ih _)

private lemma optWarpingPath_spec [AddCommMonoid R] [LinearOrder R]
    (c : α → β → R) (x : ℕ → α) (y : ℕ → β) :
    ∀ i j : ℕ, IsWarpingPathTo i j (optWarpingPath c x y i j) ∧
      warpingPathCost c x y (optWarpingPath c x y i j) = dtwPrefix c x y i j
  | 0, 0 => by
    rw [optWarpingPath]
    exact ⟨IsWarpingPathTo.start, by simp [warpingPathCost, dtwPrefix]⟩
  | i + 1, 0 => by
    obtain ⟨hp, hc⟩ := optWarpingPath_spec c x y i 0
    rw [optWarpingPath]
    refine ⟨IsWarpingPathTo.vert hp, ?_⟩
    rw [warpingPathCost_append, hc]
    simp [warpingPathCost, dtwPrefix]
  | 0, j + 1 => by
    obtain ⟨hp, hc⟩ := optWarpingPath_spec c x y 0 j
    rw [optWarpingPath]
    refine ⟨IsWarpingPathTo.horiz hp, ?_⟩
    rw [warpingPathCost_append, hc]
    simp [warpingPathCost, dtwPrefix]
  | i + 1, j + 1 => by
    obtain ⟨hpd, hcd⟩ := optWarpingPath_spec c x y i j
    obtain ⟨hpu, hcu⟩ := optWarpingPath_spec c x y i (j + 1)
    obtain ⟨hpl, hcl⟩ := optWarpingPath_spec c x y (i + 1) j
    rw [optWarpingPath, dtwPrefix]
    split_ifs with h1 h2
    · refine ⟨IsWarpingPathTo.diag hpd, ?_⟩
      rw [warpingPathCost_append, hcd, min_eq_left h1]
      simp [warpingPathCost]
    · refine ⟨IsWarpingPathTo.vert hpu, ?_⟩
      rw [warpingPathCost_append, hcu, min_eq_right (le_of_not_ge h1), min_eq_left h2]
      simp [warpingPathCost]
    · refine ⟨IsWarpingPathTo.horiz hpl, ?_⟩
      rw [warpingPathCost_append, hcl, min_eq_right (le_of_not_ge h1),
        min_eq_right (le_of_not_ge h2)]
      simp [warpingPathCost]

/-- **Bellman optimality of Dynamic Time Warping**: `dtwPrefix c x y m n` is the least
alignment cost over all valid DTW warping paths from `(0, 0)` to `(m, n)`. -/
theorem isLeast_dtwPrefix [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
    (c : α → β → R) (x : ℕ → α) (y : ℕ → β) (m n : ℕ) :
    IsLeast {r : R | ∃ p, IsWarpingPath m n p ∧ warpingPathCost c x y p = r}
      (dtwPrefix c x y m n) := by
  obtain ⟨hp, hc⟩ := optWarpingPath_spec c x y m n
  refine ⟨⟨optWarpingPath c x y m n, (isWarpingPathTo_iff m n _).mp hp, hc⟩, ?_⟩
  rintro r ⟨p, hp', rfl⟩
  exact dtwPrefix_le_warpingPathCost c x y hp'

/-- Two-row suffix `GridDP` table for Dynamic Time Warping over `List α` in `WithTop R`. -/
@[expose] def dtwGridDP [AddCommMonoid R] [LinearOrder R] (c : α → α → R) :
    Cslib.Algorithms.Lean.EditDistance.GridDP α (WithTop R) where
  nilNil := 0
  consNil _ _ := ⊤
  nilCons _ _ := ⊤
  consCons a b d u l := (c a b : WithTop R) + min d (min u l)

/-- Suffix-table DTW distance on `List α`. -/
@[expose] def dtwList [AddCommMonoid R] [LinearOrder R] (c : α → α → R)
    (x y : List α) : WithTop R :=
  (dtwGridDP c).value x y

/-- Reversed prefix list `[x i, ..., x 0]` for matching suffix `GridDP` evaluation. -/
def revPrefixList (x : ℕ → α) : ℕ → List α
  | 0 => [x 0]
  | i + 1 => x (i + 1) :: revPrefixList x i

/-- Exact agreement between `dtwList` (`GridDP.value`) on reversed prefixes and `dtwPrefix`. -/
theorem dtwList_revPrefix_eq [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
    (c : α → α → R) (x y : ℕ → α) :
    ∀ i j : ℕ,
      dtwList c (revPrefixList x i) (revPrefixList y j) =
        ((dtwPrefix c x y i j : R) : WithTop R)
  | 0, 0 => by
    rw [revPrefixList, revPrefixList, dtwList, (dtwGridDP c).value_cons_cons]
    change (c (x 0) (y 0) : WithTop R) + min 0 (min ⊤ ⊤) = _
    rw [min_top_right, min_top_right, add_zero, dtwPrefix]
  | i + 1, 0 => by
    have hprev := dtwList_revPrefix_eq c x y i 0
    have hne : revPrefixList x i ≠ [] := by cases i <;> simp [revPrefixList]
    have htop : dtwList c (revPrefixList x i) [] = ⊤ := by
      cases h : revPrefixList x i with
      | nil => exact absurd h hne
      | cons hd tl => rfl
    rw [revPrefixList, revPrefixList, dtwList, (dtwGridDP c).value_cons_cons]
    change (c (x (i + 1)) (y 0) : WithTop R) +
      min (dtwList c (revPrefixList x i) [])
        (min (dtwList c (revPrefixList x i) [y 0])
          (dtwList c (x (i + 1) :: revPrefixList x i) [])) = _
    have hprev' : dtwList c (revPrefixList x i) [y 0] =
        ((dtwPrefix c x y i 0 : R) : WithTop R) := by
      simpa only [revPrefixList] using hprev
    have htop2 : dtwList c (x (i + 1) :: revPrefixList x i) [] = ⊤ := rfl
    rw [htop, hprev', htop2, min_top_right, min_top_left, dtwPrefix, WithTop.coe_add, add_comm]
  | 0, j + 1 => by
    have hprev := dtwList_revPrefix_eq c x y 0 j
    have hne : revPrefixList y j ≠ [] := by cases j <;> simp [revPrefixList]
    have htop : dtwList c [] (revPrefixList y j) = ⊤ := by
      cases h : revPrefixList y j with
      | nil => exact absurd h hne
      | cons hd tl => rfl
    rw [revPrefixList, revPrefixList, dtwList, (dtwGridDP c).value_cons_cons]
    change (c (x 0) (y (j + 1)) : WithTop R) +
      min (dtwList c [] (revPrefixList y j))
        (min (dtwList c [] (y (j + 1) :: revPrefixList y j))
          (dtwList c [x 0] (revPrefixList y j))) = _
    have hprev' : dtwList c [x 0] (revPrefixList y j) =
        ((dtwPrefix c x y 0 j : R) : WithTop R) := by
      simpa only [revPrefixList] using hprev
    have htop2 : dtwList c [] (y (j + 1) :: revPrefixList y j) = ⊤ := rfl
    rw [htop, hprev', htop2, min_top_left, min_top_left, dtwPrefix, WithTop.coe_add, add_comm]
  | i + 1, j + 1 => by
    have hd := dtwList_revPrefix_eq c x y i j
    have hu := dtwList_revPrefix_eq c x y i (j + 1)
    have hl := dtwList_revPrefix_eq c x y (i + 1) j
    rw [revPrefixList, revPrefixList, dtwList, (dtwGridDP c).value_cons_cons]
    change (c (x (i + 1)) (y (j + 1)) : WithTop R) +
      min (dtwList c (revPrefixList x i) (revPrefixList y j))
        (min (dtwList c (revPrefixList x i) (y (j + 1) :: revPrefixList y j))
          (dtwList c (x (i + 1) :: revPrefixList x i) (revPrefixList y j))) = _
    have hu' : dtwList c (revPrefixList x i) (y (j + 1) :: revPrefixList y j) =
        ((dtwPrefix c x y i (j + 1) : R) : WithTop R) := by
      simpa only [revPrefixList] using hu
    have hl' : dtwList c (x (i + 1) :: revPrefixList x i) (revPrefixList y j) =
        ((dtwPrefix c x y (i + 1) j : R) : WithTop R) := by
      simpa only [revPrefixList] using hl
    rw [hd, hu', hl', ← WithTop.coe_min, ← WithTop.coe_min, dtwPrefix,
      WithTop.coe_add, add_comm]

end Bellman

section ComplexityScaling

/-- Number of dynamic-programming tensor cells for exact simultaneous `N`-sequence DTW on
sequences of length `T`: `Fintype.card (Fin N → Fin T) = T ^ N`. -/
def multiDtwGridSize (N T : ℕ) : ℕ :=
  T ^ N

/-- Number of dynamic-programming cells across `N` pairwise `T × T` DTW alignments (as in
DTW Barycenter Averaging per iteration). -/
def pairwiseDtwGridSize (N T : ℕ) : ℕ :=
  N * T ^ 2

/-- Number of kernel evaluations across `N` sequences of length `T` using a truncated
window of radius `W` (`2 * W + 1` taps per sample). -/
def windowedKernelGridSize (W N T : ℕ) : ℕ :=
  (2 * W + 1) * N * T

/-- Exact tensor-grid cardinality identity `Fintype.card (Fin N → Fin T) = multiDtwGridSize N T`. -/
theorem card_multiDtwGrid_eq (N T : ℕ) :
    Fintype.card (Fin N → Fin T) = multiDtwGridSize N T := by
  rw [Fintype.card_pi_const, Fintype.card_fin, multiDtwGridSize]

/-- Exponential lower bound `2 ^ N ≤ multiDtwGridSize N T` for sequence lengths `T ≥ 2`. -/
theorem two_pow_le_multiDtwGridSize (N : ℕ) {T : ℕ} (hT : 2 ≤ T) :
    2 ^ N ≤ multiDtwGridSize N T :=
  Nat.pow_le_pow_left hT N

/-- Strict linear-over-quadratic improvement: whenever `N ≥ 1` and `2 * W + 1 < T`,
windowed alignment evaluates strictly fewer cells than `N` pairwise `T × T` DTW tables. -/
theorem windowedKernelGridSize_lt_pairwiseDtwGridSize {W N T : ℕ}
    (hN : 0 < N) (hWT : 2 * W + 1 < T) :
    windowedKernelGridSize W N T < pairwiseDtwGridSize N T := by
  unfold windowedKernelGridSize pairwiseDtwGridSize
  have hNT : 0 < N * T := Nat.mul_pos hN (Nat.zero_lt_of_lt hWT)
  calc (2 * W + 1) * N * T = (2 * W + 1) * (N * T) := Nat.mul_assoc _ _ _
    _ < T * (N * T) := Nat.mul_lt_mul_of_pos_right hWT hNT
    _ = N * T ^ 2 := by rw [Nat.pow_two, ← Nat.mul_assoc, Nat.mul_comm T N, Nat.mul_assoc]

end ComplexityScaling

end CslibFrontier.Algorithms.Lean.DynamicTimeWarping
