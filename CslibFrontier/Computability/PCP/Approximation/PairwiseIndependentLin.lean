/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.Hastad.Hardness
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.ZMod.Basic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pairwise-Independent Subgroups and Exact-$k$ Abelian Linear CSPs

This module develops balanced pairwise-independent subgroups of finite Abelian product groups
$\Gamma^k$, the zero-sum linear subgroup $H_k(\Gamma) = \{x \in \Gamma^k : \sum_i x_i = 0\}$,
shift-literal Abelian Max-CSPs, and exact-$k$ Abelian linear equation promise problems
(`GapExactKLinAbelian`), under standard Lean axioms.

## Main definitions

* `CslibFrontier.Complexity.IsBalancedPairwiseIndependentSubgroup`: balanced
  pairwise-independent subgroup $H \le \Gamma^k$, requiring every distinct coordinate pair
  $(i, j)$ to have uniform joint fiber cardinality $|H| / |\Gamma|^2$.
* `CslibFrontier.Complexity.zeroSumSubgroup`,
  `CslibFrontier.Complexity.zeroSumFinset`: the zero-sum subgroup
  $\{x \in \Gamma^k : \sum_i x_i = 0\}$ and its underlying `Finset`.
* `CslibFrontier.Complexity.abelianShiftSem`,
  `CslibFrontier.Complexity.abelianLinSem`: CSP semantics for Abelian shift predicates
  $(x_{v_i} + c_i)_i \in P$ and inhomogeneous linear equations $\sum_i x_{v_i} = b$.
* `CslibFrontier.Complexity.GapAbelianShiftCSP`,
  `CslibFrontier.Complexity.GapExactKLinAbelian`,
  `CslibFrontier.Complexity.GapExactKLinBool`: gap promise problems for Abelian shift
  CSPs, Abelian $k$-linear systems, and Boolean $k$-XOR systems on distinct variables.

## Main results

* `CslibFrontier.Complexity.card_zeroSumFinset`: $|H_{k+1}(\Gamma)| = |\Gamma|^k$.
* `CslibFrontier.Complexity.isBalancedPairwiseIndependentSubgroup_zeroSumSubgroup`: for
  every finite Abelian group $\Gamma$ and every $k \ge 3$, $H_k(\Gamma)$ is balanced and pairwise
  independent of density $1 / |\Gamma|$.
* `CslibFrontier.Complexity.not_isBalancedPairwiseIndependentSubgroup_zeroSumSubgroup_two`:
  sharpness at $k = 2$ for every nontrivial finite Abelian group $\Gamma$.
* `CslibFrontier.Complexity.polyTimeReducible_gapAbelianShift_zeroSum_gapExactKLin`:
  polynomial-time reduction from `GapAbelianShiftCSP (zeroSumFinset Γ k)` to
  `GapExactKLinAbelian Γ k`.
* `CslibFrontier.Complexity.GapExactKLinBool_npHard`: unconditional NP-hardness of
  `(1 - δ, 1 / 2 + ε)`-gap `Max-Ek-LIN-2` for every $k \ge 3$ under standard Lean axioms.

## Tags

CSP, pairwise independence, Abelian groups, Max-LIN, hardness of approximation
-/

public section

namespace CslibFrontier.Complexity

open Finset Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

/-! ### Balanced pairwise-independent subgroups and the zero-sum subgroup -/

open Classical in
/-- A subgroup $H \le \Gamma^k$ of a finite additive commutative group power is **balanced and
pairwise independent** if for every pair of distinct coordinates $i \neq j$ and every pair of
target values $(u, v) \in \Gamma \times \Gamma$, the joint fiber
$\{x \in H \mid x_i = u \wedge x_j = v\}$ has cardinality $|H| / |\Gamma|^2$. -/
@[expose] def IsBalancedPairwiseIndependentSubgroup {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] {k : ℕ}
    (H : AddSubgroup (Fin k → Γ)) : Prop :=
  ∀ ⦃i j : Fin k⦄, i ≠ j → ∀ u v : Γ,
    (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H ∧ x i = u ∧ x j = v).card *
      (Fintype.card Γ) ^ 2 =
      (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H).card

open Classical in
/-- Single-coordinate balance follows from pairwise independence whenever $k \ge 2$. -/
theorem card_fiber_mul_card_eq_of_isBalancedPairwiseIndependentSubgroup
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ] {k : ℕ} (hk : 2 ≤ k)
    {H : AddSubgroup (Fin k → Γ)} (hH : IsBalancedPairwiseIndependentSubgroup H)
    (i : Fin k) (u : Γ) :
    (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H ∧ x i = u).card * Fintype.card Γ =
      (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H).card := by
  have hex : ∃ j : Fin k, i ≠ j := by
    by_cases hi0 : i.val = 0
    · refine ⟨⟨1, by omega⟩, fun h ↦ ?_⟩
      have hv := congrArg Fin.val h
      simp [hi0] at hv
    · refine ⟨⟨0, by omega⟩, fun h ↦ hi0 ?_⟩
      exact congrArg Fin.val h
  obtain ⟨j, hij⟩ := hex
  have hpart : (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H ∧ x i = u).card =
      ∑ v : Γ, (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H ∧ x i = u ∧ x j = v).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨x j, h1, h2, rfl⟩, fun ⟨_, h1, h2, _⟩ ↦ ⟨h1, h2⟩⟩
    · intro v₁ _ v₂ _ hvne
      refine Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ hvne ?_
      simp only [Finset.mem_filter] at hx₁ hx₂
      exact hx₁.2.2.2.symm.trans hx₂.2.2.2
  have hsum := congrArg (· * (Fintype.card Γ) ^ 2) hpart
  rw [Finset.sum_mul] at hsum
  have hfib_eq (v : Γ) :
      (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H ∧ x i = u ∧ x j = v).card *
        (Fintype.card Γ) ^ 2 =
        (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ H).card := by
    rw [← hH hij u v]
    exact congrArg
      (fun d ↦ (@Finset.filter _ (fun x : Fin k → Γ ↦ x ∈ H ∧ x i = u ∧ x j = v) d
        Finset.univ).card * (Fintype.card Γ) ^ 2)
      (Subsingleton.elim _ _)
  simp_rw [hfib_eq] at hsum
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hpos : 0 < Fintype.card Γ := Fintype.card_pos
  nlinarith

/-- The zero-sum subgroup $H_k(\Gamma) = \{x \in \Gamma^k : \sum_i x_i = 0\}$. -/
def zeroSumSubgroup (Γ : Type*) [AddCommGroup Γ] (k : ℕ) : AddSubgroup (Fin k → Γ) where
  carrier := {x | ∑ i : Fin k, x i = 0}
  add_mem' {x y} hx hy := by
    change ∑ i : Fin k, (x i + y i) = 0
    rw [Finset.sum_add_distrib]
    change (∑ i : Fin k, x i) + (∑ i : Fin k, y i) = 0
    rw [hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' {x} hx := by
    change ∑ i : Fin k, -x i = 0
    rw [Finset.sum_neg_distrib]
    change -(∑ i : Fin k, x i) = 0
    rw [hx, neg_zero]

@[simp]
theorem mem_zeroSumSubgroup_iff {Γ : Type*} [AddCommGroup Γ] {k : ℕ} {x : Fin k → Γ} :
    x ∈ zeroSumSubgroup Γ k ↔ ∑ i : Fin k, x i = 0 :=
  Iff.rfl

/-- The `Finset` of zero-sum tuples $\{x \in \Gamma^k : \sum_i x_i = 0\}$. -/
def zeroSumFinset (Γ : Type*) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ] (k : ℕ) :
    Finset (Fin k → Γ) :=
  Finset.univ.filter fun x : Fin k → Γ ↦ ∑ i : Fin k, x i = 0

@[simp]
theorem mem_zeroSumFinset_iff {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    {k : ℕ} {x : Fin k → Γ} :
    x ∈ zeroSumFinset Γ k ↔ ∑ i : Fin k, x i = 0 := by
  simp [zeroSumFinset]

/-- Every inhomogeneous coset $\{x \in \Gamma^k : \sum_i x_i = b\}$ for $k \ge 1$ has cardinality
$|\Gamma|^{k - 1}$. -/
theorem card_filter_sum_eq {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    {k : ℕ} (hk : 1 ≤ k) (b : Γ) :
    (Finset.univ.filter fun x : Fin k → Γ ↦ ∑ i : Fin k, x i = b).card =
      (Fintype.card Γ) ^ (k - 1) := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let S := (Finset.univ : Finset (Fin k)).erase i₀
  let e : {x : Fin k → Γ // ∑ i : Fin k, x i = b} ≃ (S → Γ) :=
    { toFun := fun ⟨x, _⟩ j ↦ x j.1
      invFun := fun y ↦
        ⟨fun i ↦ if h : i =
          i₀ then b - ∑ j : S, y j else y ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩,
          by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), dite_eq_left rfl]
            have herase : (∑ i ∈ S,
                (if h : i = i₀ then b - ∑ j : S, y j
                 else y ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩)) =
                ∑ j : S, y j := by
              rw [← Finset.sum_attach S]
              refine Finset.sum_congr rfl fun ⟨i, hi⟩ _ ↦ ?_
              exact dite_eq_right (Finset.ne_of_mem_erase hi)
            rw [herase, sub_add_cancel]⟩
      left_inv := fun ⟨x, hx⟩ ↦ by
        ext i
        by_cases hi : i = i₀
        · subst hi
          simp only [↓reduceDIte]
          have hsum_S : (∑ s : S, x s.1) = ∑ j ∈ S, x j := Finset.sum_attach S x
          rw [hsum_S, ← hx, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
          abel
        · simp [hi]
      right_inv := fun y ↦ by
        ext ⟨i, hi⟩
        exact dite_eq_right (Finset.ne_of_mem_erase hi) }
  have hcard : Fintype.card {x : Fin k → Γ // ∑ i : Fin k, x i = b} = Fintype.card (S → Γ) :=
    Fintype.card_congr e
  rw [Fintype.card_subtype] at hcard
  rw [hcard, Fintype.card_fun, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ i₀),
    Finset.card_univ, Fintype.card_fin]

/-- Cardinality of `zeroSumFinset Γ k` for $k \ge 1$ is $|\Gamma|^{k - 1}$ (hence density
$1 / |\Gamma|$ in $\Gamma^k$). -/
theorem card_zeroSumFinset {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    {k : ℕ} (hk : 1 ≤ k) :
    (zeroSumFinset Γ k).card = (Fintype.card Γ) ^ (k - 1) :=
  card_filter_sum_eq hk 0

/-- For every finite Abelian group $\Gamma$ and every arity $k \ge 3$, the zero-sum subgroup
$H_k(\Gamma) = \{x \in \Gamma^k : \sum_i x_i = 0\}$ is balanced and pairwise independent. -/
theorem isBalancedPairwiseIndependentSubgroup_zeroSumSubgroup
    (Γ : Type*) [AddCommGroup Γ] [Fintype Γ] {k : ℕ} (hk : 3 ≤ k) :
    IsBalancedPairwiseIndependentSubgroup (zeroSumSubgroup Γ k) := by
  classical
  intro i j hij u v
  have hcard_H : (Finset.univ.filter fun x : Fin k → Γ ↦ x ∈ zeroSumSubgroup Γ k).card =
      (Fintype.card Γ) ^ (k - 1) := card_filter_sum_eq (by omega) 0
  -- Pick a third coordinate `l ∉ {i, j}` using `3 ≤ k`.
  have hex_l : ∃ l : Fin k, l ≠ i ∧ l ≠ j := by
    have hcard_er : ((Finset.univ : Finset (Fin k)) \ {i, j}).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ {i, j}),
        Finset.card_univ, Fintype.card_fin, Finset.card_pair hij]
      omega
    obtain ⟨l, hl⟩ := hcard_er
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact ⟨l, hl.2.1, hl.2.2⟩
  obtain ⟨l, hli, hlj⟩ := hex_l
  let R : Finset (Fin k) := Finset.univ \ {i, j, l}
  have hR_card : R.card = k - 3 := by
    have h3 : ({i, j, l} : Finset (Fin k)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hlj.symm]
      simp [hij, hli.symm]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, h3]
  have hpart : (Finset.univ : Finset (Fin k)) = insert i (insert j (insert l R)) := by
    ext t
    simp only [R, Finset.mem_univ, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton,
      true_and, true_iff]
    tauto
  have hi_not : i ∉ insert j (insert l R) := by simp [R, hij, hli.symm]
  have hj_not : j ∉ insert l R := by simp [R, hlj.symm]
  have hl_not : l ∉ R := by simp [R]
  let e : {x : Fin k → Γ // x ∈ zeroSumSubgroup Γ k ∧ x i = u ∧ x j = v} ≃ (R → Γ) :=
    { toFun := fun ⟨x, _⟩ r ↦ x r.1
      invFun := fun y ↦
        let yExt (t : Fin k) : Γ := if ht : t ∈ R then y ⟨t, ht⟩ else 0
        ⟨fun t ↦
          if t = i then u
          else if t = j then v
          else if t = l then -(u + v + ∑ r : R, y r)
          else yExt t,
          by
            refine ⟨?_, by simp, by simp [hij.symm]⟩
            rw [mem_zeroSumSubgroup_iff, hpart, Finset.sum_insert hi_not,
              Finset.sum_insert hj_not, Finset.sum_insert hl_not]
            simp only [↓reduceIte, hij.symm, hli, hlj]
            have hR_sum : (∑ t ∈ R,
                (if t = i then u
                 else if t = j then v
                 else if t = l then -(u + v + ∑ r : R, y r)
                 else yExt t)) = ∑ r : R, y r := by
              rw [← Finset.sum_attach R]
              refine Finset.sum_congr rfl fun ⟨t, ht⟩ _ ↦ ?_
              have ht' := ht
              simp only [R, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
                not_or] at ht'
              simp [yExt, ht, ht'.2.1, ht'.2.2.1, ht'.2.2.2]
            rw [hR_sum]
            abel⟩
      left_inv := fun ⟨x, hxsum, hxi, hxj⟩ ↦ by
        ext t
        by_cases hti : t = i
        · subst hti; simp [hxi]
        · by_cases htj : t = j
          · subst htj; simp [hti, hxj]
          · by_cases htl : t = l
            · rw [htl]
              simp only [hli, hlj, ↓reduceIte]
              rw [mem_zeroSumSubgroup_iff, hpart, Finset.sum_insert hi_not,
                Finset.sum_insert hj_not, Finset.sum_insert hl_not, hxi, hxj] at hxsum
              have hsum_R : (∑ r : R, x r.1) = ∑ s ∈ R, x s := Finset.sum_attach R x
              rw [hsum_R]
              have hzero : x l + (u + v + ∑ s ∈ R, x s) = 0 := by
                rw [← hxsum]; abel
              exact (eq_neg_of_add_eq_zero_left hzero).symm
            · have htR : t ∈ R := by
                simp [R, hti, htj, htl]
              simp [hti, htj, htl, htR]
      right_inv := fun y ↦ by
        ext ⟨t, ht⟩
        have ht' := ht
        simp only [R, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at ht'
        simp [ht, ht'.2.1, ht'.2.2.1, ht'.2.2.2] }
  have hcard_fib : (Finset.univ.filter fun x : Fin k → Γ ↦
      x ∈ zeroSumSubgroup Γ k ∧ x i = u ∧ x j = v).card = (Fintype.card Γ) ^ (k - 3) := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_subtype, Fintype.card_fun, Fintype.card_coe, hR_card] at hc
    exact hc
  rw [hcard_fib, hcard_H, ← pow_add]
  congr 1
  omega

/-- **Arity-2 sharpness**: for every nontrivial finite Abelian group $\Gamma$, the binary zero-sum
subgroup $H_2(\Gamma) = \{(x_0, x_1) \in \Gamma^2 : x_0 + x_1 = 0\}$ is **not** pairwise
independent, because $x_0 = 0$ forces $x_1 = 0$. -/
theorem not_isBalancedPairwiseIndependentSubgroup_zeroSumSubgroup_two
    (Γ : Type*) [AddCommGroup Γ] [Fintype Γ] [Nontrivial Γ] :
    ¬ IsBalancedPairwiseIndependentSubgroup (zeroSumSubgroup Γ 2) := by
  classical
  intro h
  obtain ⟨g, hg⟩ := exists_ne (0 : Γ)
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have hfib := h h01 0 g
  have hempty : (Finset.univ.filter fun x : Fin 2 → Γ ↦
      x ∈ zeroSumSubgroup Γ 2 ∧ x 0 = 0 ∧ x 1 = g) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro x _ ⟨hxsum, hx0, hx1⟩
    rw [mem_zeroSumSubgroup_iff, Fin.sum_univ_two, hx0, hx1, zero_add] at hxsum
    exact hg hxsum
  rw [hempty, Finset.card_empty, zero_mul] at hfib
  have hnonempty : 0 < (Finset.univ.filter fun x : Fin 2 → Γ ↦ x ∈ zeroSumSubgroup Γ 2).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (zeroSumSubgroup Γ 2).zero_mem⟩⟩
  omega

/-! ### Abelian shift CSPs, exact-$k$ Abelian linear systems, and Boolean $k$-XOR hardness -/

/-- CSP semantics for a $k$-ary predicate $P \subseteq \Gamma^k$ with group-translation literals
`shifts : Fin k → Γ`: evaluates `(fun i => vals[i] + shifts i) ∈ P` when `vals.length = k`. -/
@[expose] def abelianShiftSem {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] {k : ℕ}
    (P : Finset (Fin k → Γ)) (shifts : Fin k → Γ) (vals : List Γ) : Bool :=
  if h : vals.length = k then
    decide ((fun i : Fin k ↦ vals.get (i.cast h.symm) + shifts i) ∈ P)
  else
    false

/-- CSP semantics for inhomogeneous linear equations $\sum_i x_{v_i} = b$ over an additive
commutative group $\Gamma$. -/
@[expose] def abelianLinSem {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] (b : Γ) (vals : List Γ) :
    Bool :=
  decide (vals.sum = b)

/-- Gap promise problem for $k$-ary Abelian shift CSPs on $k$ distinct variables per constraint. -/
@[expose] noncomputable def GapAbelianShiftCSP {Γ : Type} [AddCommGroup Γ] [DecidableEq Γ] {k : ℕ}
    (P : Finset (Fin k → Γ)) (c s : ℝ) : PromiseProblem (CSP (Fin k → Γ) ℕ) :=
  (PromiseProblem.gapMax (fun F ↦ 1 - F.unsatVal (abelianShiftSem P))
    (fun _ ↦ c) (fun _ ↦ s)).restrict
    {F | ∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup}

/-- Gap promise problem for `Max-Ek-LIN-Γ`: systems of linear equations
$x_{v_1} + \dots + x_{v_k} = b$
on $k$ distinct variables over a finite Abelian group $\Gamma$. -/
@[expose] noncomputable def GapExactKLinAbelian (Γ : Type) [AddCommGroup Γ] [DecidableEq Γ]
    (k : ℕ) (c s : ℝ) : PromiseProblem (CSP Γ ℕ) :=
  (PromiseProblem.gapMax (fun F ↦ 1 - F.unsatVal abelianLinSem)
    (fun _ ↦ c) (fun _ ↦ s)).restrict
    {F | ∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup}

/-- Gap promise problem for Boolean `Max-Ek-LIN-2` (`Max-Ek-XORSAT`) on $k$ distinct variables per
equation (`CSP Bool ℕ` under `CSP.paritySem`). At $k = 3$, this coincides definitionally with
`Cslib.Complexity.GapExactThreeLin`. -/
@[expose] noncomputable def GapExactKLinBool (k : ℕ) (c s : ℝ) : PromiseProblem (CSP Bool ℕ) :=
  (PromiseProblem.gapMax (fun F ↦ 1 - F.unsatVal CSP.paritySem)
    (fun _ ↦ c) (fun _ ↦ s)).restrict
    {F | ∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup}

theorem mem_yes_GapExactKLinAbelian {Γ : Type} [AddCommGroup Γ] [DecidableEq Γ]
    {k : ℕ} {c s : ℝ} {F : CSP Γ ℕ} :
    F ∈ (GapExactKLinAbelian Γ k c s).yes ↔
      (∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup) ∧ c ≤ 1 - F.unsatVal abelianLinSem := by
  simp only [GapExactKLinAbelian, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

theorem mem_no_GapExactKLinAbelian {Γ : Type} [AddCommGroup Γ] [DecidableEq Γ]
    {k : ℕ} {c s : ℝ} (hsc : s < c) {F : CSP Γ ℕ} :
    F ∈ (GapExactKLinAbelian Γ k c s).no ↔
      (∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup) ∧ 1 - F.unsatVal abelianLinSem ≤ s := by
  simp only [GapExactKLinAbelian, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ c) (s := fun _ ↦ s) hsc,
    Set.mem_ofPred_eq, and_comm]

theorem mem_yes_GapExactKLinBool {k : ℕ} {c s : ℝ} {F : CSP Bool ℕ} :
    F ∈ (GapExactKLinBool k c s).yes ↔
      (∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup) ∧ c ≤ 1 - F.unsatVal CSP.paritySem := by
  simp only [GapExactKLinBool, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

theorem mem_no_GapExactKLinBool {k : ℕ} {c s : ℝ} (hsc : s < c) {F : CSP Bool ℕ} :
    F ∈ (GapExactKLinBool k c s).no ↔
      (∀ e ∈ F, e.scope.length = k ∧ e.scope.Nodup) ∧ 1 - F.unsatVal CSP.paritySem ≤ s := by
  simp only [GapExactKLinBool, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ c) (s := fun _ ↦ s) hsc,
    Set.mem_ofPred_eq, and_comm]

/-- Canonical binary encoding of `CSP (Fin k → Γ) ℕ` for a finite group `Γ`. -/
noncomputable abbrev encAbelianShiftCSP (Γ : Type) [Finite Γ] (k : ℕ) :
    CSP (Fin k → Γ) ℕ ↪ List Bool :=
  encCSP (encPi (encFinite Γ)) encNat

/-- Canonical binary encoding of `CSP Γ ℕ` for a finite group `Γ`. -/
noncomputable abbrev encAbelianLinCSP (Γ : Type) [Finite Γ] :
    CSP Γ ℕ ↪ List Bool :=
  encCSP (encFinite Γ) encNat

/-- Convert a shift-literal zero-sum constraint `(x_{v_i} + c_i)_i ∈ H_k(Γ)` into the equivalent
inhomogeneous equation `∑_i x_{v_i} = -∑_i c_i`. -/
def shiftZeroSumToLin {Γ : Type} [AddCommGroup Γ] {k : ℕ}
    (F : CSP (Fin k → Γ) ℕ) : CSP Γ ℕ :=
  F.map fun e ↦ ⟨-∑ i : Fin k, e.rel i, e.scope⟩

private theorem eval_abelianShiftSem_zeroSum_eq {Γ : Type} [AddCommGroup Γ] [Fintype Γ]
    [DecidableEq Γ] {k : ℕ} {e : Constraint (Fin k → Γ) ℕ} (he : e.scope.length = k)
    (σ : ℕ → Γ) :
    Constraint.eval (abelianShiftSem (zeroSumFinset Γ k)) σ e =
      Constraint.eval abelianLinSem σ ⟨-∑ i : Fin k, e.rel i, e.scope⟩ := by
  have hlen : (e.scope.map σ).length = k := by simp [he]
  simp only [Constraint.eval, abelianShiftSem, hlen, ↓reduceDIte, mem_zeroSumFinset_iff,
    abelianLinSem]
  have hsum_get : (∑ i : Fin k, (e.scope.map σ).get (i.cast hlen.symm)) =
      (e.scope.map σ).sum := by
    have hofFn : e.scope.map σ =
        List.ofFn (fun i : Fin k ↦ (e.scope.map σ).get (i.cast hlen.symm)) :=
      List.ext_getElem (by simp [hlen]) fun idx h1 h2 ↦ by simp
    conv_rhs => rw [hofFn, List.sum_ofFn]
  rw [Finset.sum_add_distrib, hsum_get]
  exact Bool.eq_iff_iff.mpr <| by
    simp only [decide_eq_true_eq]
    exact ⟨fun h ↦ eq_neg_of_add_eq_zero_left h, fun h ↦ by rw [h]; abel⟩

private theorem unsatVal_shiftZeroSumToLin {Γ : Type} [AddCommGroup Γ] [Fintype Γ]
    [DecidableEq Γ] {k : ℕ} {F : CSP (Fin k → Γ) ℕ} (hF : ∀ e ∈ F, e.scope.length = k) :
    (shiftZeroSumToLin F).unsatVal abelianLinSem =
      F.unsatVal (abelianShiftSem (zeroSumFinset Γ k)) := by
  have hcount (σ : ℕ → Γ) :
      (shiftZeroSumToLin F).countP (fun c ↦ !Constraint.eval abelianLinSem σ c) =
        F.countP (fun e ↦ !Constraint.eval (abelianShiftSem (zeroSumFinset Γ k)) σ e) := by
    rw [shiftZeroSumToLin, List.countP_map]
    refine List.countP_congr fun e he ↦ ?_
    simp only [Function.comp_apply, eval_abelianShiftSem_zeroSum_eq (hF e he) σ]
  have hlen : (shiftZeroSumToLin F).length = F.length := by simp [shiftZeroSumToLin]
  refine le_antisymm ?_ ?_
  · obtain ⟨σ, hσ⟩ := CSP.exists_countUnsat_div_eq_unsatVal (abelianShiftSem (zeroSumFinset Γ k)) F
    rw [← hσ, ← hcount σ, ← hlen]
    exact (shiftZeroSumToLin F).unsatVal_le abelianLinSem σ
  · refine (CSP.le_unsatVal_iff abelianLinSem (shiftZeroSumToLin F)).2 fun σ ↦ ?_
    rw [hcount σ, hlen]
    exact F.unsatVal_le (abelianShiftSem (zeroSumFinset Γ k)) σ

/-- Polynomial-time value-preserving reduction from `GapAbelianShiftCSP (zeroSumFinset Γ k) c s`
to `GapExactKLinAbelian Γ k c s`. -/
theorem polyTimeReducible_gapAbelianShift_zeroSum_gapExactKLin
    (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ] (k : ℕ) {c s : ℝ} (hsc : s < c) :
    PromiseProblem.PolyTimeReducible (encAbelianShiftCSP Γ k) (encAbelianLinCSP Γ)
      (GapAbelianShiftCSP (zeroSumFinset Γ k) c s) (GapExactKLinAbelian Γ k c s) := by
  have hnegSum_pt : ComputableInPolyTime (fun r : Fin k → Γ ↦ -∑ i : Fin k, r i)
      (encPi (encFinite Γ)) (encFinite Γ) :=
    ComputableInPolyTime.of_finite _
  have hmap_pt : ComputableInPolyTime (shiftZeroSumToLin (Γ := Γ) (k := k))
      (encAbelianShiftCSP Γ k) (encAbelianLinCSP Γ) := by
    unfold shiftZeroSumToLin
    exact ComputableInPolyTime.map
      (encConstraint_mk_polyTime (hnegSum_pt.comp (encConstraint_rel_polyTime .id'))
        (encConstraint_scope_polyTime .id'))
  refine ⟨shiftZeroSumToLin, hmap_pt, fun F hF ↦ ?_, fun F hF ↦ ?_⟩
  · simp only [GapAbelianShiftCSP, PromiseProblem.yes_restrict, Set.mem_inter_iff,
      PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq] at hF
    rw [mem_yes_GapExactKLinAbelian, unsatVal_shiftZeroSumToLin fun e he ↦ (hF.2 e he).1]
    refine ⟨?_, hF.1⟩
    intro e' he'
    rw [shiftZeroSumToLin, List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact hF.2 e he
  · simp only [GapAbelianShiftCSP, PromiseProblem.no_restrict, Set.mem_inter_iff,
      PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ c) (s := fun _ ↦ s) hsc,
      Set.mem_ofPred_eq] at hF
    rw [mem_no_GapExactKLinAbelian hsc, unsatVal_shiftZeroSumToLin fun e he ↦ (hF.2 e he).1]
    refine ⟨?_, hF.1⟩
    intro e' he'
    rw [shiftZeroSumToLin, List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact hF.2 e he

/-! ### Unconditional Boolean `Max-Ek-LIN-2` hardness for all $k \ge 3$ (0 megatheorems) -/

/-- Lift a Boolean `E3-LIN-2` system `F` to an `Ek-LIN-2` system ($k \ge 3$) by shifting all
original variables up by `k - 3` and appending `k - 3` shared global variables `0, ..., k - 4`.
Because `z ⊕ z ⊕ z = z` in `Bool`, shifting `x_v ↦ x_v ⊕ z` makes the satisfaction value
identically equal on every instance! -/
def liftThreeToKLinBool (k : ℕ) (F : CSP Bool ℕ) : CSP Bool ℕ :=
  F.map fun e ↦ ⟨e.rel, e.scope.map (· + (k - 3)) ++ List.range (k - 3)⟩

private theorem scopes_liftThreeToKLinBool {k : ℕ} (hk : 3 ≤ k) {F : CSP Bool ℕ}
    (hF : ∀ e ∈ F, e.scope.length = 3 ∧ e.scope.Nodup) :
    ∀ e' ∈ liftThreeToKLinBool k F, e'.scope.length = k ∧ e'.scope.Nodup := by
  intro e' he'
  rw [liftThreeToKLinBool, List.mem_map] at he'
  obtain ⟨e, he, rfl⟩ := he'
  obtain ⟨hlen, hnodup⟩ := hF e he
  refine ⟨by simp [hlen]; omega, ?_⟩
  refine List.nodup_append.mpr ⟨?_, List.nodup_range, fun u hu v hv huv ↦ ?_⟩
  · exact hnodup.map fun a b hab ↦ by omega
  · rw [List.mem_map] at hu
    obtain ⟨w, _, rfl⟩ := hu
    rw [List.mem_range] at hv
    omega

private theorem xor_three_bool (z : Bool) : Bool.xor (Bool.xor z z) z = z := by
  cases z <;> rfl

private theorem foldl_xor_init (l : List Bool) (init : Bool) :
    l.foldl Bool.xor init = Bool.xor init (l.foldl Bool.xor false) := by
  induction l generalizing init with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (Bool.xor init b), ih b]
    cases init <;> cases b <;> cases (bs.foldl Bool.xor false) <;> rfl

private theorem foldl_xor_append (l₁ l₂ : List Bool) :
    (l₁ ++ l₂).foldl Bool.xor false =
      Bool.xor (l₁.foldl Bool.xor false) (l₂.foldl Bool.xor false) := by
  rw [List.foldl_append, foldl_xor_init]

private theorem unsatVal_liftThreeToKLinBool {k : ℕ} {F : CSP Bool ℕ}
    (hF : ∀ e ∈ F, e.scope.length = 3) :
    (liftThreeToKLinBool k F).unsatVal CSP.paritySem = F.unsatVal CSP.paritySem := by
  -- Forward direction: given `σ : ℕ → Bool`, set fresh `< k - 3` variables to `false`.
  refine le_antisymm ?_ ?_
  · obtain ⟨σ, hσ⟩ := CSP.exists_countUnsat_div_eq_unsatVal CSP.paritySem F
    let σ' : ℕ → Bool := fun v ↦ if v < k - 3 then false else σ (v - (k - 3))
    have hcount : (liftThreeToKLinBool k F).countP (fun c ↦ !Constraint.eval CSP.paritySem σ' c) =
        F.countP (fun e ↦ !Constraint.eval CSP.paritySem σ e) := by
      rw [liftThreeToKLinBool, List.countP_map]
      refine List.countP_congr fun e he ↦ ?_
      simp only [Function.comp_apply, Constraint.eval, CSP.paritySem, List.map_append,
        List.map_map, foldl_xor_append]
      have hmap1 : List.map (σ' ∘ fun x ↦ x + (k - 3)) e.scope = e.scope.map σ := by
        refine List.map_congr_left fun x _ ↦ ?_
        dsimp only [Function.comp_apply, σ']
        rw [ite_eq_right (by omega), Nat.add_sub_cancel]
      have hmap2 : ((List.range (k - 3)).map σ').foldl Bool.xor false = false := by
        have hall : (List.range (k - 3)).map σ' = List.replicate (k - 3) false := by
          rw [List.eq_replicate_iff]
          refine ⟨by simp, fun b hb ↦ ?_⟩
          rw [List.mem_map] at hb
          obtain ⟨i, hi, rfl⟩ := hb
          exact ite_eq_left (List.mem_range.mp hi)
        rw [hall]
        clear *-
        induction (k - 3) with
        | zero => rfl
        | succ n ih => simpa [List.replicate_succ] using ih
      rw [hmap1, hmap2, Bool.xor_false]
    have hlen : (liftThreeToKLinBool k F).length = F.length := by simp [liftThreeToKLinBool]
    rw [← hσ, ← hcount, ← hlen]
    exact (liftThreeToKLinBool k F).unsatVal_le CSP.paritySem σ'
  · -- Reverse direction: given `σ' : ℕ → Bool`, let `z` be the XOR of `0 .. k - 4` and shift `σ'`.
    refine (CSP.le_unsatVal_iff CSP.paritySem (liftThreeToKLinBool k F)).2 fun σ' ↦ ?_
    let z : Bool := ((List.range (k - 3)).map σ').foldl Bool.xor false
    let σ : ℕ → Bool := fun v ↦ Bool.xor (σ' (v + (k - 3))) z
    have hcount : (liftThreeToKLinBool k F).countP (fun c ↦ !Constraint.eval CSP.paritySem σ' c) =
        F.countP (fun e ↦ !Constraint.eval CSP.paritySem σ e) := by
      rw [liftThreeToKLinBool, List.countP_map]
      refine List.countP_congr fun e he ↦ ?_
      have h3 := hF e he
      rcases e with ⟨rel, scope⟩
      rcases scope with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, _ | _⟩⟩⟩ <;> simp at h3
      simp only [Function.comp_apply, Constraint.eval, CSP.paritySem, List.map_append,
        List.map_cons, List.map_nil, foldl_xor_append, List.foldl_cons, List.foldl_nil,
        Bool.false_xor]
      dsimp only [σ, z]
      generalize σ' (v₁ + (k - 3)) = b₁
      generalize σ' (v₂ + (k - 3)) = b₂
      generalize σ' (v₃ + (k - 3)) = b₃
      generalize ((List.range (k - 3)).map σ').foldl Bool.xor false = bz
      cases b₁ <;> cases b₂ <;> cases b₃ <;> cases bz <;> cases rel <;> decide
    have hlen : (liftThreeToKLinBool k F).length = F.length := by simp [liftThreeToKLinBool]
    rw [hcount, hlen]
    exact F.unsatVal_le CSP.paritySem σ

/-- **Unconditional Boolean `Max-Ek-LIN-2` (`Max-Ek-XORSAT`) $(1 - \delta, 1/2 + \varepsilon)$
NP-hardness for all $k \ge 3$** under standard Lean axioms (`0` megatheorems), proved from
`Cslib.Complexity.GapExactThreeLin_npHard` via `liftThreeToKLinBool`. -/
theorem GapExactKLinBool_npHard {k : ℕ} (hk : 3 ≤ k) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : 1 / 2 + ε < 1 - δ) :
    PromiseProblem.NPHard (encCSP encBool encNat) (GapExactKLinBool k (1 - δ) (1 / 2 + ε)) := by
  have hpt : ComputableInPolyTime (liftThreeToKLinBool k)
      (encCSP encBool encNat) (encCSP encBool encNat) := by
    unfold liftThreeToKLinBool
    have hshift : ComputableInPolyTime (fun x : ℕ ↦ x + (k - 3)) encNat encNat :=
      ComputableInPolyTime.binary_add' .id' (.const (k - 3))
    have hscope : ComputableInPolyTime
        (fun e : Constraint Bool ℕ ↦ e.scope.map (· + (k - 3)) ++ List.range (k - 3))
        (encConstraint encBool encNat) (encList encNat) :=
      (ComputableInPolyTime.listAppend encNat).comp
        (((ComputableInPolyTime.map hshift).comp (encConstraint_scope_polyTime .id')).prod
          (.const (List.range (k - 3))))
    exact ComputableInPolyTime.map
      (encConstraint_mk_polyTime (encConstraint_rel_polyTime .id') hscope)
  refine (GapExactThreeLin_npHard hδ hε h).trans ⟨liftThreeToKLinBool k, hpt,
    fun F hF ↦ ?_, fun F hF ↦ ?_⟩
  · rw [mem_yes_GapExactThreeLin] at hF
    rw [mem_yes_GapExactKLinBool, unsatVal_liftThreeToKLinBool fun e he ↦ (hF.1 e he).1]
    exact ⟨scopes_liftThreeToKLinBool hk hF.1, hF.2⟩
  · rw [mem_no_GapExactThreeLin h] at hF
    rw [mem_no_GapExactKLinBool h, unsatVal_liftThreeToKLinBool fun e he ↦ (hF.1 e he).1]
    exact ⟨scopes_liftThreeToKLinBool hk hF.1, hF.2⟩

end CslibFrontier.Complexity
