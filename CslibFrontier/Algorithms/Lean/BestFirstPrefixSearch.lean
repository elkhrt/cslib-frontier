/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Best-First Monotone Prefix-Cost Search

This module formalizes generic best-first search over a finite candidate set `Ξ` with a monotone
non-decreasing prefix-cost table `v : ℕ → ι → ℝ` (the combinatorial core of best-first sphere
decoding, A*-style prefix search, and minimum-metric tree search).

## Main definitions

* `CslibFrontier.Algorithms.Lean.BestFirstPrefixSearch.IsMinimizerOn`: finite-set minimizer
  predicate.
* `CslibFrontier.Algorithms.Lean.BestFirstPrefixSearch.IsSmallestSubset`: `k`-element minimum
  prefix-cost candidate selection predicate.
* `CslibFrontier.Algorithms.Lean.BestFirstPrefixSearch.bestFirstLoop` /
  `CslibFrontier.Algorithms.Lean.BestFirstPrefixSearch.bestFirstSearch`: fuel-bounded best-first
  search expanding the branch with minimum current prefix cost until a branch reaches decision
  depth `depth`.

## Main results

* `exists_isSmallestSubset`: every finite type of cardinality `≥ k` admits a `k`-smallest subset.
* `bestFirstSearch_optimality`: exact optimality of `bestFirstSearch` at decision depth `depth`.
* `bestFirstSearch_expansion_bounds`: exact expansion-count bounds
  `depth - 1 ≤ expansions ≤ Ξ.card * (depth - 1)` and visited-node bounds
  `Ξ.card + (depth - 1) ≤ visited ≤ Ξ.card * depth`.
* `bestFirstSearch_pruning_sandwich`: exact instance-optimal pruning sandwich bounds in terms of
  the optimal decision-depth threshold `d* = v depth j_out`.
-/

public section

noncomputable section

open scoped BigOperators

namespace CslibFrontier.Algorithms.Lean.BestFirstPrefixSearch

/-- `j` minimizes `f` over the finite candidate set `S`. -/
def IsMinimizerOn {ι : Type*} (S : Finset ι) (f : ι → ℝ) (j : ι) : Prop :=
  j ∈ S ∧ ∀ k ∈ S, f j ≤ f k

/-- `Ξ` consists of `k` elements of `ι` achieving the smallest values of `f`. -/
def IsSmallestSubset {ι : Type*} (k : ℕ) (f : ι → ℝ) (Ξ : Finset ι) : Prop :=
  Ξ.card = k ∧ ∀ j ∈ Ξ, ∀ j' ∉ Ξ, f j ≤ f j'

/-- Deterministic selector returning an element of nonempty finite set `Ξ` that minimizes `f`. -/
def chooseMin {ι : Type*} (Ξ : Finset ι) (hΞ : Ξ.Nonempty) (f : ι → ℝ) : ι :=
  Classical.choose (Finset.exists_min_image Ξ f hΞ)

theorem chooseMin_mem {ι : Type*} (Ξ : Finset ι) (hΞ : Ξ.Nonempty) (f : ι → ℝ) :
    chooseMin Ξ hΞ f ∈ Ξ :=
  (Classical.choose_spec (Finset.exists_min_image Ξ f hΞ)).1

theorem chooseMin_le {ι : Type*} (Ξ : Finset ι) (hΞ : Ξ.Nonempty) (f : ι → ℝ)
    {k : ι} (hk : k ∈ Ξ) :
    f (chooseMin Ξ hΞ f) ≤ f k :=
  (Classical.choose_spec (Finset.exists_min_image Ξ f hΞ)).2 k hk

/-- Fuel-bounded best-first search loop expanding the branch with smallest current prefix cost
`v (len j) j` until some branch reaches target depth `depth`. Returns
`(selectedBranch, finalLengths, expansionsPerformed)`. -/
def bestFirstLoop {ι : Type*} [DecidableEq ι] (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    (depth : ℕ) (v : ℕ → ι → ℝ) : ℕ → (ι → ℕ) → ι × (ι → ℕ) × ℕ
  | 0, len => (chooseMin Ξ hΞ (fun j ↦ v (len j) j), len, 0)
  | fuel + 1, len =>
    let jMin := chooseMin Ξ hΞ (fun j ↦ v (len j) j)
    if len jMin = depth then (jMin, len, 0)
    else
      let res := bestFirstLoop Ξ hΞ depth v fuel (Function.update len jMin (len jMin + 1))
      (res.1, res.2.1, res.2.2 + 1)

/-- Full best-first search initialized at depth `1` with loop budget `depth * Ξ.card`. -/
def bestFirstSearch {ι : Type*} [DecidableEq ι] (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    (depth : ℕ) (v : ℕ → ι → ℝ) : ι × (ι → ℕ) × ℕ :=
  bestFirstLoop Ξ hΞ depth v (depth * Ξ.card) (fun _ ↦ 1)

theorem isMinimizerOn_iff {ι : Type*} (S : Finset ι) (f : ι → ℝ) (j : ι) :
    IsMinimizerOn S f j ↔ j ∈ S ∧ ∀ k ∈ S, f j ≤ f k := by
  rfl

theorem isSmallestSubset_iff {ι : Type*} (k : ℕ) (f : ι → ℝ) (Ξ : Finset ι) :
    IsSmallestSubset k f Ξ ↔ Ξ.card = k ∧ ∀ j ∈ Ξ, ∀ j' ∉ Ξ, f j ≤ f j' := by
  rfl

theorem bestFirstLoop_succ {ι : Type*} [DecidableEq ι] (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    (depth : ℕ) (v : ℕ → ι → ℝ) (fuel : ℕ) (len : ι → ℕ) :
    bestFirstLoop Ξ hΞ depth v (fuel + 1) len =
      let jMin := chooseMin Ξ hΞ (fun j ↦ v (len j) j)
      if len jMin = depth then (jMin, len, 0)
      else
        let res := bestFirstLoop Ξ hΞ depth v fuel (Function.update len jMin (len jMin + 1))
        (res.1, res.2.1, res.2.2 + 1) := by
  rfl

theorem bestFirstSearch_eq {ι : Type*} [DecidableEq ι] (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    (depth : ℕ) (v : ℕ → ι → ℝ) :
    bestFirstSearch Ξ hΞ depth v = bestFirstLoop Ξ hΞ depth v (depth * Ξ.card) (fun _ ↦ 1) := by
  rfl

/-- Every finite type `ι` of cardinality at least `k` has a `k`-smallest subset for any
real-valued cost function `f`. -/
theorem exists_isSmallestSubset {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : k ≤ Fintype.card ι) (f : ι → ℝ) :
    ∃ Ξ : Finset ι, IsSmallestSubset k f Ξ := by
  classical
  induction k with
  | zero =>
    refine ⟨∅, (isSmallestSubset_iff 0 f ∅).mpr ⟨rfl, ?_⟩⟩
    intro _ h
    exact absurd h (Finset.notMem_empty _)
  | succ k ih =>
    obtain ⟨S, hS⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨hScard, hSmin⟩ := (isSmallestSubset_iff k f S).mp hS
    have hcomp : (Finset.univ \ S).Nonempty := by
      have hcard_sdiff : (Finset.univ \ S).card = Fintype.card ι - k := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hScard]
      exact Finset.card_pos.mp (by omega)
    obtain ⟨x, hx_mem, hx_min⟩ := Finset.exists_min_image (Finset.univ \ S) f hcomp
    have hx_not_S : x ∉ S := (Finset.mem_sdiff.mp hx_mem).2
    refine ⟨insert x S, (isSmallestSubset_iff (k + 1) f (insert x S)).mpr ?_⟩
    refine ⟨Finset.card_insert_of_notMem hx_not_S ▸ congrArg Nat.succ hScard, ?_⟩
    intro j hj j' hj'
    have hj'_not_S : j' ∉ S := fun h ↦ hj' (Finset.mem_insert_of_mem h)
    have hj'_sdiff : j' ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j', hj'_not_S⟩
    rcases Finset.mem_insert.mp hj with rfl | hjS
    · exact hx_min j' hj'_sdiff
    · exact (hSmin j hjS x hx_not_S).trans (hx_min j' hj'_sdiff)

/-- Exact loop invariant for `bestFirstLoop` under monotone non-decreasing prefix costs `v`. -/
theorem bestFirstLoop_spec {ι : Type*} [DecidableEq ι] (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    (depth : ℕ) (v : ℕ → ι → ℝ)
    (hv : ∀ j ∈ Ξ, ∀ {l₁ l₂ : ℕ}, l₁ ≤ l₂ → v l₁ j ≤ v l₂ j) :
    ∀ (fuel : ℕ) (len : ι → ℕ),
      (∀ j ∈ Ξ, len j ≤ depth) →
      (∑ j ∈ Ξ, (depth - len j)) < fuel →
      let res := bestFirstLoop Ξ hΞ depth v fuel len
      res.1 ∈ Ξ ∧
      res.2.1 res.1 = depth ∧
      (∀ j ∈ Ξ, len j ≤ res.2.1 j ∧ res.2.1 j ≤ depth) ∧
      (∑ j ∈ Ξ, res.2.1 j = (∑ j ∈ Ξ, len j) + res.2.2) ∧
      (∀ j ∈ Ξ, v depth res.1 ≤ v depth j) ∧
      (∀ j ∈ Ξ, ∀ i : ℕ, i < depth → v i j < v depth res.1 → i < res.2.1 j) ∧
      (∀ j ∈ Ξ, ∀ i : ℕ, len j ≤ i → i < depth → v depth res.1 < v i j → res.2.1 j ≤ i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro len _ hfuel
    exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro len hle hfuel
    dsimp only
    rw [bestFirstLoop_succ]
    set jMin := chooseMin Ξ hΞ (fun j ↦ v (len j) j)
    have hjMin_mem : jMin ∈ Ξ := chooseMin_mem Ξ hΞ (fun j ↦ v (len j) j)
    have hjMin_le : ∀ k ∈ Ξ, v (len jMin) jMin ≤ v (len k) k :=
      fun k hk ↦ chooseMin_le Ξ hΞ (fun j ↦ v (len j) j) hk
    by_cases hdone : len jMin = depth
    · rw [ite_eq_left hdone]
      have hopt : ∀ j ∈ Ξ, v depth jMin ≤ v depth j := fun j hj ↦ by
        calc v depth jMin = v (len jMin) jMin := by rw [hdone]
          _ ≤ v (len j) j := hjMin_le j hj
          _ ≤ v depth j := hv j hj (hle j hj)
      refine ⟨hjMin_mem, hdone, fun j hj ↦ ⟨le_refl _, hle j hj⟩, by simp, hopt, ?_, ?_⟩
      · intro j hj i _ hlt
        by_contra hnot
        have hle_i : len j ≤ i := Nat.le_of_not_lt hnot
        have h1 : v (len j) j ≤ v i j := hv j hj hle_i
        have h2 : v depth jMin ≤ v (len j) j := by
          rw [← hdone]; exact hjMin_le j hj
        linarith
      · intro j _ i hji _ _
        exact hji
    · rw [ite_eq_right hdone]
      have hjMin_lt : len jMin < depth := Nat.lt_of_le_of_ne (hle jMin hjMin_mem) hdone
      let len' : ι → ℕ := Function.update len jMin (len jMin + 1)
      have hle' : ∀ j ∈ Ξ, len' j ≤ depth := by
        intro j hj
        by_cases h : j = jMin
        · subst h; simp [len']; omega
        · simp [len', h, hle j hj]
      have hrem : ∑ j ∈ Ξ, (depth - len' j) + 1 = ∑ j ∈ Ξ, (depth - len j) := by
        have hsplit1 := Finset.add_sum_erase Ξ (fun j ↦ depth - len' j) hjMin_mem
        have hsplit2 := Finset.add_sum_erase Ξ (fun j ↦ depth - len j) hjMin_mem
        have herase : ∑ j ∈ Ξ.erase jMin, (depth - len' j) =
            ∑ j ∈ Ξ.erase jMin, (depth - len j) := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          simp [len', (Finset.mem_erase.mp hj).1]
        have hval : depth - len' jMin + 1 = depth - len jMin := by
          simp [len']
          omega
        rw [← hsplit1, ← hsplit2, herase]
        omega
      have hfuel' : (∑ j ∈ Ξ, (depth - len' j)) < fuel := by omega
      have hih := ih len' hle' hfuel'
      rcases hih with ⟨hout_mem, hout_len, hbounds, hsum, hopt, hlow, hhigh⟩
      have hsum_len' : ∑ j ∈ Ξ, len' j = (∑ j ∈ Ξ, len j) + 1 := by
        have hsplit1 := Finset.add_sum_erase Ξ len' hjMin_mem
        have hsplit2 := Finset.add_sum_erase Ξ len hjMin_mem
        have herase : ∑ j ∈ Ξ.erase jMin, len' j = ∑ j ∈ Ξ.erase jMin, len j := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          simp [len', (Finset.mem_erase.mp hj).1]
        have hval : len' jMin = len jMin + 1 := by simp [len']
        rw [← hsplit1, ← hsplit2, herase, hval]
        omega
      refine ⟨hout_mem, hout_len, ?_, ?_, hopt, hlow, ?_⟩
      · intro j hj
        have hstep : len j ≤ len' j := by
          by_cases h : j = jMin
          · subst h; simp [len']
          · simp [len', h]
        exact ⟨hstep.trans (hbounds j hj).1, (hbounds j hj).2⟩
      · rw [hsum, hsum_len']
        ring
      · intro j hj i hji hi hlt
        refine hhigh j hj i ?_ hi hlt
        by_cases h : j = jMin
        · subst h
          simp only [len', Function.update_self]
          by_contra hnot
          have heq : len jMin = i := by omega
          have h2 : v (len jMin) jMin ≤ v (len (bestFirstLoop Ξ hΞ depth v fuel len').1)
              (bestFirstLoop Ξ hΞ depth v fuel len').1 :=
            hjMin_le _ hout_mem
          have h3 : v (len (bestFirstLoop Ξ hΞ depth v fuel len').1)
              (bestFirstLoop Ξ hΞ depth v fuel len').1 ≤
              v depth (bestFirstLoop Ξ hΞ depth v fuel len').1 :=
            hv _ hout_mem (hle _ hout_mem)
          rw [heq] at h2
          have hlt' : v depth (bestFirstLoop Ξ hΞ depth v fuel len').1 < v i jMin := hlt
          linarith [hlt']
        · simpa [len', h] using hji

private theorem bestFirstSearch_fuel_lt {ι : Type*} (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    {depth : ℕ} (hdepth : 1 ≤ depth) :
    ∑ _j ∈ Ξ, (depth - 1) < depth * Ξ.card := by
  rw [Finset.sum_const, smul_eq_mul]
  have hlt : depth - 1 < depth := by omega
  calc Ξ.card * (depth - 1) < Ξ.card * depth := Nat.mul_lt_mul_of_pos_left hlt hΞ.card_pos
    _ = depth * Ξ.card := Nat.mul_comm _ _

/-- Exact optimality of `bestFirstSearch` at decision depth `depth ≥ 1`. -/
theorem bestFirstSearch_optimality {ι : Type*} [DecidableEq ι] (Ξ : Finset ι) (hΞ : Ξ.Nonempty)
    {depth : ℕ} (hdepth : 1 ≤ depth) (v : ℕ → ι → ℝ)
    (hv : ∀ j ∈ Ξ, ∀ {l₁ l₂ : ℕ}, l₁ ≤ l₂ → v l₁ j ≤ v l₂ j) :
    IsMinimizerOn Ξ (v depth) (bestFirstSearch Ξ hΞ depth v).1 := by
  have h := bestFirstLoop_spec Ξ hΞ depth v hv (depth * Ξ.card) (fun _ ↦ 1)
    (fun _ _ ↦ hdepth) (bestFirstSearch_fuel_lt Ξ hΞ hdepth)
  rw [bestFirstSearch_eq, isMinimizerOn_iff]
  exact ⟨h.1, h.2.2.2.2.1⟩

/-- Exact node-expansion and visited-node count bounds for `bestFirstSearch`. -/
theorem bestFirstSearch_expansion_bounds {ι : Type*} [DecidableEq ι] (Ξ : Finset ι)
    (hΞ : Ξ.Nonempty) {depth : ℕ} (hdepth : 1 ≤ depth) (v : ℕ → ι → ℝ)
    (hv : ∀ j ∈ Ξ, ∀ {l₁ l₂ : ℕ}, l₁ ≤ l₂ → v l₁ j ≤ v l₂ j) :
    let res := bestFirstSearch Ξ hΞ depth v
    depth - 1 ≤ res.2.2 ∧
    res.2.2 ≤ Ξ.card * (depth - 1) ∧
    Ξ.card + (depth - 1) ≤ ∑ j ∈ Ξ, res.2.1 j ∧
    ∑ j ∈ Ξ, res.2.1 j ≤ Ξ.card * depth := by
  have h := bestFirstLoop_spec Ξ hΞ depth v hv (depth * Ξ.card) (fun _ ↦ 1)
    (fun _ _ ↦ hdepth) (bestFirstSearch_fuel_lt Ξ hΞ hdepth)
  dsimp only
  rw [bestFirstSearch_eq]
  rcases h with ⟨hout_mem, hout_len, hbounds, hsum, _, _, _⟩
  set res := bestFirstLoop Ξ hΞ depth v (depth * Ξ.card) (fun _ ↦ 1)
  have hsum_init : ∑ _j ∈ Ξ, (1 : ℕ) = Ξ.card := by simp
  have _ : ∑ j ∈ Ξ, res.2.1 j = Ξ.card + res.2.2 := by
    simpa [hsum_init] using hsum
  have hsum_le : ∑ j ∈ Ξ, res.2.1 j ≤ Ξ.card * depth := by
    calc ∑ j ∈ Ξ, res.2.1 j
        ≤ ∑ _j ∈ Ξ, depth := Finset.sum_le_sum fun j hj ↦ (hbounds j hj).2
      _ = Ξ.card * depth := by simp
  have hsum_ge : Ξ.card + (depth - 1) ≤ ∑ j ∈ Ξ, res.2.1 j := by
    have hsplit := Finset.add_sum_erase Ξ res.2.1 hout_mem
    have herase : Ξ.card - 1 ≤ ∑ j ∈ Ξ.erase res.1, res.2.1 j := by
      calc Ξ.card - 1 = (Ξ.erase res.1).card := (Finset.card_erase_of_mem hout_mem).symm
        _ = ∑ _j ∈ Ξ.erase res.1, 1 := by simp
        _ ≤ ∑ j ∈ Ξ.erase res.1, res.2.1 j :=
            Finset.sum_le_sum fun j hj ↦ (hbounds j (Finset.mem_of_mem_erase hj)).1
    have hcard_pos : 1 ≤ Ξ.card := hΞ.card_pos
    rw [← hsplit, hout_len]
    omega
  refine ⟨by omega, ?_, hsum_ge, hsum_le⟩
  have hmul : Ξ.card + Ξ.card * (depth - 1) = Ξ.card * depth := by
    have := Nat.mul_sub_one Ξ.card depth
    have hle_mul : Ξ.card ≤ Ξ.card * depth := Nat.le_mul_of_pos_right Ξ.card (by omega)
    omega
  omega

/-- Instance-optimal threshold-pruning sandwich bounds for `bestFirstSearch`. -/
theorem bestFirstSearch_pruning_sandwich {ι : Type*} [DecidableEq ι] (Ξ : Finset ι)
    (hΞ : Ξ.Nonempty) {depth : ℕ} (hdepth : 1 ≤ depth) (v : ℕ → ι → ℝ)
    (hv : ∀ j ∈ Ξ, ∀ {l₁ l₂ : ℕ}, l₁ ≤ l₂ → v l₁ j ≤ v l₂ j) :
    let res := bestFirstSearch Ξ hΞ depth v
    let dStar := v depth res.1
    Ξ.card + ∑ j ∈ Ξ, ((Finset.Ico 1 depth).filter (fun i ↦ v i j < dStar)).card ≤
      ∑ j ∈ Ξ, res.2.1 j ∧
    ∑ j ∈ Ξ, res.2.1 j ≤
      Ξ.card + ∑ j ∈ Ξ, ((Finset.Ico 1 depth).filter (fun i ↦ v i j ≤ dStar)).card := by
  have h := bestFirstLoop_spec Ξ hΞ depth v hv (depth * Ξ.card) (fun _ ↦ 1)
    (fun _ _ ↦ hdepth) (bestFirstSearch_fuel_lt Ξ hΞ hdepth)
  dsimp only
  rw [bestFirstSearch_eq]
  rcases h with ⟨_, _, hbounds, _, _, hlow, hhigh⟩
  set res := bestFirstLoop Ξ hΞ depth v (depth * Ξ.card) (fun _ ↦ 1)
  set dStar := v depth res.1
  have hbranch : ∀ j ∈ Ξ,
      1 + ((Finset.Ico 1 depth).filter (fun i ↦ v i j < dStar)).card ≤ res.2.1 j ∧
      res.2.1 j ≤ 1 + ((Finset.Ico 1 depth).filter (fun i ↦ v i j ≤ dStar)).card := by
    intro j hj
    have hlen1 : 1 ≤ res.2.1 j := (hbounds j hj).1
    have hlen2 : res.2.1 j ≤ depth := (hbounds j hj).2
    constructor
    · have hsub : (Finset.Ico 1 depth).filter (fun i ↦ v i j < dStar) ⊆
          Finset.Ico 1 (res.2.1 j) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
        exact ⟨hi.1.1, hlow j hj i hi.1.2 hi.2⟩
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega
    · have hsub : Finset.Ico 1 (res.2.1 j) ⊆
          (Finset.Ico 1 depth).filter (fun i ↦ v i j ≤ dStar) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
        refine ⟨⟨hi.1, lt_of_lt_of_le hi.2 hlen2⟩, ?_⟩
        by_contra hnot
        have hgt : dStar < v i j := lt_of_not_ge hnot
        have hle_i := hhigh j hj i hi.1 (lt_of_lt_of_le hi.2 hlen2) hgt
        omega
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hcard
      omega
  constructor
  · calc Ξ.card + ∑ j ∈ Ξ, ((Finset.Ico 1 depth).filter (fun i ↦ v i j < dStar)).card
        = ∑ j ∈ Ξ, (1 + ((Finset.Ico 1 depth).filter (fun i ↦ v i j < dStar)).card) := by
          rw [Finset.sum_add_distrib]; simp
      _ ≤ ∑ j ∈ Ξ, res.2.1 j := Finset.sum_le_sum fun j hj ↦ (hbranch j hj).1
  · calc ∑ j ∈ Ξ, res.2.1 j
        ≤ ∑ j ∈ Ξ, (1 + ((Finset.Ico 1 depth).filter (fun i ↦ v i j ≤ dStar)).card) :=
          Finset.sum_le_sum fun j hj ↦ (hbranch j hj).2
      _ = Ξ.card + ∑ j ∈ Ξ, ((Finset.Ico 1 depth).filter (fun i ↦ v i j ≤ dStar)).card := by
          rw [Finset.sum_add_distrib]; simp

end CslibFrontier.Algorithms.Lean.BestFirstPrefixSearch
