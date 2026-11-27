/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.Expander.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-Sided Bipartite Vertex Expanders and the Bipartite Half

This module extends `Cslib.Bipartite` with general two-sided bipartite vertex expansion, bucketed
second-order Bonferroni neighborhood lower bounds, and the bipartite-half transformation from
two-sided bipartite expanders to undirected simple-graph expanders.

## Main definitions

- `CslibFrontier.Bipartite.leftNeighbors`: left neighborhood of a subset of right vertices in a
  bipartite graph `G : L → R → Prop`.
- `CslibFrontier.Bipartite.IsLeftRegular`, `CslibFrontier.Bipartite.IsRightRegular`: one-sided
  exact degree regularity predicates.
- `CslibFrontier.Bipartite.IsTwoSidedExpander`: two-sided `(kL, αL, kR, αR)` bipartite vertex
  expansion predicate.
- `CslibFrontier.Bipartite.IsTwoSidedLosslessExpander`: biregular two-sided `(kL, εL, kR, εR)`
  lossless bipartite vertex expansion predicate.
- `CslibFrontier.Bipartite.bipartiteHalfRel`, `CslibFrontier.Bipartite.bipartiteHalfSimpleGraph`:
  reflexive and loopless bipartite half graphs on the left vertex set.
- `CslibFrontier.Bipartite.IsRegularLosslessExpander`,
  `CslibFrontier.Bipartite.IsMaxDegreeLosslessExpander`: small-set lossless vertex expansion
  predicates on finite undirected simple graphs.

## Main results

- `CslibFrontier.Bipartite.sum_lt_mul_le_sq_div`: pairwise product inequality
  `∑_{i < j} x_i x_j ≤ (n - 1) S^2 / (2 n)` for `x : Fin n → ℝ` with sum `S`.
- `CslibFrontier.Bipartite.two_mul_sum_card_le_two_mul_card_biUnion_add_offDiag`: additive
  second-order Bonferroni union lower bound.
- `CslibFrontier.Bipartite.card_leftNeighbors_ge_of_bucket_overlap`: right-to-left vertex expansion
  from right-regularity, intra-bucket disjointness, and an inter-bucket common-neighbor bound.
- `CslibFrontier.Bipartite.bipartiteHalfRel_degree_bounds` and
  `CslibFrontier.Bipartite.IsTwoSidedExpander.bipartiteHalfRel_isVertexExpander`: degree bounds and
  composed expansion factor `αL * αR` of the bipartite half of a two-sided bipartite expander.
-/

public section

open Finset
open scoped BigOperators

namespace CslibFrontier.Bipartite

section PairwiseInequalities

/-- Off-diagonal square identity on a finite index set:
`∑_{i ≠ j} x_i x_j + ∑_i x_i^2 = (∑_i x_i)^2`. -/
theorem sum_offDiag_mul_add_sum_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ p ∈ s.offDiag, x p.1 * x p.2) + ∑ i ∈ s, x i ^ 2 = (∑ i ∈ s, x i) ^ 2 := by
  classical
  have hprod : (∑ i ∈ s, x i) ^ 2 = ∑ p ∈ s ×ˢ s, x p.1 * x p.2 := by
    rw [sq, sum_mul_sum, ← sum_product']
  have hunion : s.offDiag ∪ s.diag = s ×ˢ s := by
    ext ⟨a, b⟩
    simp only [mem_union, mem_offDiag, mem_diag, mem_product]
    by_cases hab : a = b <;> simp [hab]
  have hdisj : Disjoint s.offDiag s.diag := by
    rw [disjoint_left]
    intro ⟨a, b⟩ h1 h2
    exact (mem_offDiag.mp h1).2.2 (mem_diag.mp h2).2
  rw [hprod, ← hunion, sum_union hdisj]
  congr 1
  rw [diag, sum_map]
  refine sum_congr rfl fun i _ ↦ ?_
  simp [sq]

/-- Cauchy–Schwarz bound on the sum of squares over a `Finset`:
`(∑_{i ∈ s} x_i)^2 ≤ #s * ∑_{i ∈ s} x_i^2`. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, x i) ^ 2 ≤ (#s : ℝ) * ∑ i ∈ s, x i ^ 2 := by
  have hnonneg : (0 : ℝ) ≤ ∑ i ∈ s, ∑ j ∈ s, (x i - x j) ^ 2 :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  have hexpand :
      (∑ i ∈ s, ∑ j ∈ s, (x i - x j) ^ 2) =
        2 * (#s : ℝ) * (∑ i ∈ s, x i ^ 2) - 2 * (∑ i ∈ s, x i) ^ 2 := by
    have h1 : ∀ i ∈ s,
        (∑ j ∈ s, (x i - x j) ^ 2) =
          (#s : ℝ) * x i ^ 2 - 2 * x i * (∑ j ∈ s, x j) + ∑ j ∈ s, x j ^ 2 := by
      intro i _
      have hsub : ∀ j ∈ s, (x i - x j) ^ 2 = x i ^ 2 - 2 * x i * x j + x j ^ 2 :=
        fun _ _ ↦ by ring
      rw [sum_congr rfl hsub, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
        ← mul_sum]
    rw [sum_congr rfl h1, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    have hmul : (∑ x_1 ∈ s, 2 * x x_1 * ∑ j ∈ s, x j) = 2 * (∑ i ∈ s, x i) ^ 2 := by
      have hfactor : ∀ i ∈ s, 2 * x i * (∑ j ∈ s, x j) = x i * (2 * ∑ j ∈ s, x j) :=
        fun _ _ ↦ by ring
      rw [sum_congr rfl hfactor, ← sum_mul]
      ring
    linarith
  linarith

/-- Off-diagonal pairwise product upper bound on a nonempty finite type:
`∑_{i ≠ j} x_i x_j ≤ ((q - 1) / q) * (∑_i x_i)^2`. -/
theorem sum_offDiag_mul_le {β : Type*} [Fintype β]
    (hβ : 0 < Fintype.card β) (x : β → ℝ) :
    ∑ p ∈ (univ : Finset β).offDiag, x p.1 * x p.2 ≤
      ((Fintype.card β : ℝ) - 1) / (Fintype.card β : ℝ) * (∑ i : β, x i) ^ 2 := by
  have hq : (0 : ℝ) < (Fintype.card β : ℝ) := Nat.cast_pos.mpr hβ
  have hcs := sq_sum_le_card_mul_sum_sq (univ : Finset β) x
  rw [card_univ] at hcs
  have hid := sum_offDiag_mul_add_sum_sq (univ : Finset β) x
  have hmul :
      (Fintype.card β : ℝ) * (∑ p ∈ (univ : Finset β).offDiag, x p.1 * x p.2) ≤
        ((Fintype.card β : ℝ) - 1) * (∑ i : β, x i) ^ 2 := by
    nlinarith
  calc
    ∑ p ∈ (univ : Finset β).offDiag, x p.1 * x p.2 =
        ((Fintype.card β : ℝ) * ∑ p ∈ (univ : Finset β).offDiag, x p.1 * x p.2) /
          (Fintype.card β : ℝ) := by
      field_simp
    _ ≤ (((Fintype.card β : ℝ) - 1) * (∑ i : β, x i) ^ 2) / (Fintype.card β : ℝ) :=
      div_le_div_of_nonneg_right hmul hq.le
    _ = ((Fintype.card β : ℝ) - 1) / (Fintype.card β : ℝ) * (∑ i : β, x i) ^ 2 := by
      ring

/-- Ordered pairwise product bound: for `x : Fin n → ℝ` (`0 < n`),
`∑_{i < j} x_i x_j ≤ (n - 1) * (∑_i x_i)^2 / (2 * n)`. -/
theorem sum_lt_mul_le_sq_div {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ p ∈ (univ : Finset (Fin n × Fin n)).filter (fun p ↦ p.1 < p.2), x p.1 * x p.2 ≤
      ((n : ℝ) - 1) * (∑ i : Fin n, x i) ^ 2 / (2 * (n : ℝ)) := by
  let ltSet : Finset (Fin n × Fin n) := univ.filter fun p ↦ p.1 < p.2
  let gtSet : Finset (Fin n × Fin n) := univ.filter fun p ↦ p.2 < p.1
  have hdisj : Disjoint ltSet gtSet := by
    rw [disjoint_filter]
    intro p _ h1 h2
    exact lt_asymm h1 h2
  have hunion : ltSet ∪ gtSet = (univ : Finset (Fin n)).offDiag := by
    ext ⟨i, j⟩
    simp only [ltSet, gtSet, mem_union, mem_filter, mem_univ, true_and, mem_offDiag,
      ne_iff_lt_or_gt]
  have hswap : ∑ p ∈ gtSet, x p.1 * x p.2 = ∑ p ∈ ltSet, x p.1 * x p.2 := by
    refine sum_nbij' Prod.swap Prod.swap (fun p hp ↦ ?_) (fun p hp ↦ ?_)
      (fun _ _ ↦ Prod.swap_swap _) (fun _ _ ↦ Prod.swap_swap _) (fun p _ ↦ mul_comm _ _)
    · simp only [gtSet, ltSet, mem_filter, mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact hp
    · simp only [gtSet, ltSet, mem_filter, mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact hp
  have hoff := sum_offDiag_mul_le (β := Fin n) (by simpa using hn) x
  rw [Fintype.card_fin, ← hunion, sum_union hdisj, hswap] at hoff
  have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    ∑ p ∈ ltSet, x p.1 * x p.2 ≤
        (((n : ℝ) - 1) / (n : ℝ) * (∑ i : Fin n, x i) ^ 2) / 2 := by
      linarith
    _ = ((n : ℝ) - 1) * (∑ i : Fin n, x i) ^ 2 / (2 * (n : ℝ)) := by
      field_simp

/-- Additive second-order Bonferroni lower bound on the cardinality of a finite union:
`2 * ∑_{u ∈ T} #(A u) ≤ 2 * #(⋃_{u ∈ T} A u) + ∑_{(u, v) ∈ T.offDiag} #(A u ∩ A v)`. -/
theorem two_mul_sum_card_le_two_mul_card_biUnion_add_offDiag
    {ι α : Type*} [DecidableEq α] (T : Finset ι) (A : ι → Finset α) :
    2 * ∑ u ∈ T, #(A u) ≤
      2 * #(T.biUnion A) + ∑ p ∈ T.offDiag, #(A p.1 ∩ A p.2) := by
  classical
  let U := T.biUnion A
  let m : α → ℕ := fun x ↦ #(T.filter fun u ↦ x ∈ A u)
  have hsum1 : ∑ u ∈ T, #(A u) = ∑ x ∈ U, m x := by
    simp only [m, card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun u hu ↦ ?_
    have hsub : A u ⊆ U := subset_biUnion_of_mem A hu
    rw [← sum_subset hsub]
    · simp
    · intro x _ hx
      simp [hx]
  have hsum2 : ∑ p ∈ T.offDiag, #(A p.1 ∩ A p.2) = ∑ x ∈ U, m x * (m x - 1) := by
    have hpair : ∀ x ∈ U,
        #(T.offDiag.filter fun p ↦ x ∈ A p.1 ∧ x ∈ A p.2) = m x * (m x - 1) := by
      intro x _
      have heq :
          (T.offDiag.filter fun p ↦ x ∈ A p.1 ∧ x ∈ A p.2) =
            (T.filter fun u ↦ x ∈ A u).offDiag := by
        ext ⟨u, v⟩
        simp only [mem_filter, mem_offDiag]
        tauto
      rw [heq, offDiag_card]
      exact (Nat.mul_sub_one (m x) (m x)).symm
    have hswap :
        ∑ p ∈ T.offDiag, #(A p.1 ∩ A p.2) =
          ∑ x ∈ U, #(T.offDiag.filter fun p ↦ x ∈ A p.1 ∧ x ∈ A p.2) := by
      simp only [card_eq_sum_ones, sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun p hp ↦ ?_
      have hp1 : p.1 ∈ T := (mem_offDiag.mp hp).1
      have hsub : A p.1 ∩ A p.2 ⊆ U :=
        inter_subset_left.trans (subset_biUnion_of_mem A hp1)
      rw [← sum_subset hsub]
      · refine sum_congr rfl fun x hx ↦ ?_
        rw [mem_inter] at hx
        simp [hx]
      · intro x _ hx
        rw [mem_inter] at hx
        simp [hx]
    rw [hswap, sum_congr rfl hpair]
  have hU : #(T.biUnion A) = ∑ _x ∈ U, 1 := by simp [U]
  rw [hsum1, hsum2, hU, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x hx ↦ ?_
  obtain ⟨u, hu, hxu⟩ := mem_biUnion.mp hx
  have hm_pos : 1 ≤ m x := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hxu⟩⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm_pos
  rw [hk, Nat.add_sub_cancel_left, add_mul, one_mul]
  have hkk : k ≤ k * k := Nat.le_mul_self k
  omega

end PairwiseInequalities

section TwoSidedExpansion

variable {L R : Type*}

/-- Left neighborhood of a subset `T : Finset R` of right vertices in `G : L → R → Prop`. -/
@[expose]
def leftNeighbors [Fintype L] (G : L → R → Prop) [∀ l r, Decidable (G l r)]
    (T : Finset R) : Finset L :=
  Cslib.Bipartite.neighbors (Function.swap G) T

@[simp]
theorem mem_leftNeighbors [Fintype L] {G : L → R → Prop} [∀ l r, Decidable (G l r)]
    {T : Finset R} {l : L} :
    l ∈ leftNeighbors G T ↔ ∃ r ∈ T, G l r := by
  simp [leftNeighbors, Function.swap]

/-- Every left vertex has exact degree `c`. -/
@[expose]
def IsLeftRegular [Fintype R] (G : L → R → Prop) [∀ l r, Decidable (G l r)] (c : ℕ) : Prop :=
  ∀ l : L, #(univ.bipartiteAbove G l) = c

/-- Every right vertex has exact degree `d`. -/
@[expose]
def IsRightRegular [Fintype L] (G : L → R → Prop) [∀ l r, Decidable (G l r)] (d : ℕ) : Prop :=
  ∀ r : R, #(univ.bipartiteBelow G r) = d

/-- Two-sided `(kL, αL, kR, αR)` bipartite vertex expansion predicate. -/
@[expose]
def IsTwoSidedExpander [Fintype L] [Fintype R] (G : L → R → Prop)
    [∀ l r, Decidable (G l r)] (kL : ℕ) (αL : ℝ) (kR : ℕ) (αR : ℝ) : Prop :=
  Cslib.Bipartite.IsVertexExpander G kL αL ∧
    Cslib.Bipartite.IsVertexExpander (Function.swap G) kR αR

/-- A `(c, d)`-biregular bipartite graph is a two-sided `(kL, εL, kR, εR)`-lossless expander when
left subsets up to `kL` expand by `(1 - εL) * c` and right subsets up to `kR` expand by
`(1 - εR) * d`. -/
@[expose]
def IsTwoSidedLosslessExpander [Fintype L] [Fintype R] (G : L → R → Prop)
    [∀ l r, Decidable (G l r)] (c d kL : ℕ) (εL : ℝ) (kR : ℕ) (εR : ℝ) : Prop :=
  Cslib.Bipartite.IsBiregular G c d ∧
    IsTwoSidedExpander G kL ((1 - εL) * (c : ℝ)) kR ((1 - εR) * (d : ℝ))

/-- Right-to-left vertex expansion from right-regularity, disjointness within buckets of a map
`seed : R → β`, and a uniform overlap bound `B` across distinct buckets. -/
theorem card_leftNeighbors_ge_of_bucket_overlap
    {β : Type*} [Fintype L] [DecidableEq L] [Fintype β]
    (hβ : 0 < Fintype.card β) {G : L → R → Prop} [∀ l r, Decidable (G l r)]
    {d B : ℕ} (hreg : IsRightRegular G d) (seed : R → β)
    (hsame : ∀ r₁ r₂ : R, seed r₁ = seed r₂ → r₁ ≠ r₂ →
      Disjoint (univ.bipartiteBelow G r₁) (univ.bipartiteBelow G r₂))
    (hdiff : ∀ r₁ r₂ : R, seed r₁ ≠ seed r₂ →
      #(univ.bipartiteBelow G r₁ ∩ univ.bipartiteBelow G r₂) ≤ B)
    (T : Finset R) :
    (d : ℝ) * (#T : ℝ) -
        ((Fintype.card β : ℝ) - 1) / (2 * (Fintype.card β : ℝ)) * (B : ℝ) * (#T : ℝ) ^ 2 ≤
      (#(leftNeighbors G T) : ℝ) := by
  classical
  let A : R → Finset L := fun r ↦ univ.bipartiteBelow G r
  have hbiUnion : T.biUnion A = leftNeighbors G T := by
    ext l
    simp [A, mem_biUnion, mem_bipartiteBelow]
  have hbonf := two_mul_sum_card_le_two_mul_card_biUnion_add_offDiag T A
  have hsumA : ∑ r ∈ T, #(A r) = #T * d := by
    calc
      ∑ r ∈ T, #(A r) = ∑ _r ∈ T, d := sum_congr rfl fun r _ ↦ hreg r
      _ = #T * d := by simp
  rw [hsumA, hbiUnion] at hbonf
  let t : β → ℕ := fun y ↦ #(T.filter fun r ↦ seed r = y)
  have ht_sum : ∑ y : β, (t y : ℝ) = (#T : ℝ) := by
    have hnat : ∑ y : β, t y = #T := by
      simpa [t] using (card_eq_sum_card_fiberwise (f := seed) (s := T) (t := univ)
        fun _ _ ↦ mem_univ _).symm
    exact_mod_cast hnat
  have hoff_bound :
      ∑ p ∈ T.offDiag, #(A p.1 ∩ A p.2) ≤
        B * ∑ yp ∈ (univ : Finset β).offDiag, t yp.1 * t yp.2 := by
    have hpoint : ∀ p ∈ T.offDiag,
        #(A p.1 ∩ A p.2) ≤ if seed p.1 = seed p.2 then 0 else B := by
      intro ⟨r₁, r₂⟩ hp
      rw [mem_offDiag] at hp
      split_ifs with hs
      · rw [disjoint_iff_inter_eq_empty.mp (hsame r₁ r₂ hs hp.2.2), card_empty]
      · exact hdiff r₁ r₂ hs
    calc
      ∑ p ∈ T.offDiag, #(A p.1 ∩ A p.2) ≤
          ∑ p ∈ T.offDiag, if seed p.1 = seed p.2 then 0 else B := sum_le_sum hpoint
      _ = ∑ _p ∈ T.offDiag.filter (fun p ↦ seed p.1 ≠ seed p.2), B := by
          rw [sum_filter]
          refine sum_congr rfl fun p _ ↦ ?_
          by_cases h : seed p.1 = seed p.2 <;> simp [h]
      _ = B * #(T.offDiag.filter fun p ↦ seed p.1 ≠ seed p.2) := by
          simp [mul_comm]
      _ = B * ∑ yp ∈ (univ : Finset β).offDiag, t yp.1 * t yp.2 := by
          congr 1
          have hpart :
              (T.offDiag.filter fun p ↦ seed p.1 ≠ seed p.2) =
                (univ : Finset β).offDiag.biUnion fun yp ↦
                  (T.filter fun r ↦ seed r = yp.1) ×ˢ (T.filter fun r ↦ seed r = yp.2) := by
            ext ⟨r₁, r₂⟩
            simp only [mem_filter, mem_offDiag, mem_biUnion, mem_univ, true_and, mem_product]
            constructor
            · rintro ⟨⟨hr₁, hr₂, _⟩, hne⟩
              exact ⟨(seed r₁, seed r₂), hne, ⟨hr₁, rfl⟩, ⟨hr₂, rfl⟩⟩
            · rintro ⟨⟨y₁, y₂⟩, hyne, ⟨hr₁, rfl⟩, ⟨hr₂, rfl⟩⟩
              exact ⟨⟨hr₁, hr₂, fun h ↦ hyne (congrArg seed h)⟩, hyne⟩
          rw [hpart, card_biUnion]
          · refine sum_congr rfl fun yp _ ↦ ?_
            rw [card_product]
          · intro yp₁ _ yp₂ _ hne
            change Disjoint _ _
            rw [disjoint_left]
            intro ⟨r₁, r₂⟩ h1 h2
            simp only [mem_product, mem_filter] at h1 h2
            exact hne (Prod.ext (h1.1.2.symm.trans h2.1.2) (h1.2.2.symm.trans h2.2.2))
  have hbonfR :
      2 * ((d : ℝ) * (#T : ℝ)) ≤
        2 * (#(leftNeighbors G T) : ℝ) +
          (B : ℝ) * ∑ yp ∈ (univ : Finset β).offDiag, (t yp.1 : ℝ) * (t yp.2 : ℝ) := by
    have h1 : 2 * (#T * d) ≤
        2 * #(leftNeighbors G T) + B * ∑ yp ∈ (univ : Finset β).offDiag, t yp.1 * t yp.2 :=
      hbonf.trans (Nat.add_le_add_left hoff_bound _)
    have h2 : (2 * ((#T : ℝ) * (d : ℝ))) ≤
        2 * (#(leftNeighbors G T) : ℝ) +
          (B : ℝ) * ∑ yp ∈ (univ : Finset β).offDiag, (t yp.1 : ℝ) * (t yp.2 : ℝ) := by
      exact_mod_cast h1
    linarith
  have hcs := sum_offDiag_mul_le hβ (fun y ↦ (t y : ℝ))
  rw [ht_sum] at hcs
  have hBcs :
      (B : ℝ) * ∑ yp ∈ (univ : Finset β).offDiag, (t yp.1 : ℝ) * (t yp.2 : ℝ) ≤
        (B : ℝ) * (((Fintype.card β : ℝ) - 1) / (Fintype.card β : ℝ) * (#T : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg B)
  have hq : (0 : ℝ) < (Fintype.card β : ℝ) := Nat.cast_pos.mpr hβ
  have hrew :
      (B : ℝ) * (((Fintype.card β : ℝ) - 1) / (Fintype.card β : ℝ) * (#T : ℝ) ^ 2) =
        2 * (((Fintype.card β : ℝ) - 1) / (2 * (Fintype.card β : ℝ)) *
          (B : ℝ) * (#T : ℝ) ^ 2) := by
    field_simp
  linarith

end TwoSidedExpansion

section BipartiteHalf

variable {L R : Type*}

/-- Reflexive bipartite half relation on `L`: `u` and `v` are related iff they share a common right
neighbor in `G`. -/
@[expose]
def bipartiteHalfRel (G : L → R → Prop) (u v : L) : Prop :=
  ∃ r : R, G u r ∧ G v r

instance instDecidableBipartiteHalfRel [Fintype R] (G : L → R → Prop)
    [∀ l r, Decidable (G l r)] (u v : L) : Decidable (bipartiteHalfRel G u v) :=
  Fintype.decidableExistsFintype

/-- The neighborhood of `S` in `bipartiteHalfRel G` equals `leftNeighbors G (neighbors G S)`. -/
theorem neighbors_bipartiteHalfRel_eq [Fintype L] [Fintype R]
    (G : L → R → Prop) [∀ l r, Decidable (G l r)] (S : Finset L) :
    Cslib.Bipartite.neighbors (bipartiteHalfRel G) S =
      leftNeighbors G (Cslib.Bipartite.neighbors G S) := by
  ext w
  simp only [Cslib.Bipartite.mem_neighbors, mem_leftNeighbors, bipartiteHalfRel]
  constructor
  · rintro ⟨u, hu, r, hur, hwr⟩
    exact ⟨r, ⟨u, hu, hur⟩, hwr⟩
  · rintro ⟨r, ⟨u, hu, hur⟩, hwr⟩
    exact ⟨u, hu, r, hur, hwr⟩

/-- Degree bounds `[c * αR, c * d]` for every vertex in `bipartiteHalfRel G`. -/
theorem bipartiteHalfRel_degree_bounds [Fintype L] [Fintype R]
    {G : L → R → Prop} [∀ l r, Decidable (G l r)]
    {c d kL kR : ℕ} {αL αR : ℝ}
    (hbi : Cslib.Bipartite.IsBiregular G c d)
    (hexp : IsTwoSidedExpander G kL αL kR αR) (hckR : c ≤ kR) (u : L) :
    (c : ℝ) * αR ≤ (#(univ.bipartiteAbove (bipartiteHalfRel G) u) : ℝ) ∧
      #(univ.bipartiteAbove (bipartiteHalfRel G) u) ≤ c * d := by
  have hsingle :
      univ.bipartiteAbove (bipartiteHalfRel G) u =
        leftNeighbors G (univ.bipartiteAbove G u) := by
    ext w
    simp [mem_bipartiteAbove, bipartiteHalfRel]
  rw [hsingle]
  have hu_card : #(univ.bipartiteAbove G u) = c := hbi.1 u
  have hlow := hexp.2 (univ.bipartiteAbove G u) (hu_card.le.trans hckR)
  have heq : Cslib.Bipartite.neighbors (Function.swap G) (univ.bipartiteAbove G u) =
      leftNeighbors G (univ.bipartiteAbove G u) := by
    ext l; simp [Function.swap]
  rw [hu_card, heq] at hlow
  have hhigh :
      #(leftNeighbors G (univ.bipartiteAbove G u)) ≤ d * #(univ.bipartiteAbove G u) :=
    Cslib.Bipartite.card_neighbors_le (fun r ↦ (hbi.2 r).le) (univ.bipartiteAbove G u)
  rw [hu_card, mul_comm] at hhigh
  exact ⟨by linarith, hhigh⟩

/-- Two-step expansion of the reflexive bipartite half: if `G` is `(c, d)`-biregular and a
two-sided `(kL, αL, kR, αR)`-expander with `0 ≤ αR`, then `bipartiteHalfRel G` expands subsets of
size at most `min kL (kR / c)` by factor `αL * αR`. -/
theorem IsTwoSidedExpander.bipartiteHalfRel_isVertexExpander
    [Fintype L] [Fintype R] {G : L → R → Prop} [∀ l r, Decidable (G l r)]
    {c d kL kR : ℕ} {αL αR : ℝ}
    (hbi : Cslib.Bipartite.IsBiregular G c d)
    (hexp : IsTwoSidedExpander G kL αL kR αR) (hαR : 0 ≤ αR) :
    Cslib.Bipartite.IsVertexExpander (bipartiteHalfRel G) (min kL (kR / c)) (αL * αR) := by
  intro S hS
  rw [neighbors_bipartiteHalfRel_eq]
  have hSL : #S ≤ kL := hS.trans (Nat.min_le_left _ _)
  have hSR : c * #S ≤ kR :=
    (Nat.mul_le_mul_left c (hS.trans (Nat.min_le_right _ _))).trans (Nat.mul_div_le kR c)
  have hN_le : #(Cslib.Bipartite.neighbors G S) ≤ kR :=
    (Cslib.Bipartite.card_neighbors_le hbi.isLeftBounded S).trans hSR
  have hstep1 := hexp.1 S hSL
  have hstep2 := hexp.2 (Cslib.Bipartite.neighbors G S) hN_le
  have heq : Cslib.Bipartite.neighbors (Function.swap G) (Cslib.Bipartite.neighbors G S) =
      leftNeighbors G (Cslib.Bipartite.neighbors G S) := by
    ext l; simp [Function.swap]
  rw [heq] at hstep2
  calc
    αL * αR * (#S : ℝ) = αR * (αL * (#S : ℝ)) := by ring
    _ ≤ αR * (#(Cslib.Bipartite.neighbors G S) : ℝ) := mul_le_mul_of_nonneg_left hstep1 hαR
    _ ≤ (#(leftNeighbors G (Cslib.Bipartite.neighbors G S)) : ℝ) := hstep2

/-- Loopless simple-graph bipartite half on `L`. -/
@[expose]
def bipartiteHalfSimpleGraph (G : L → R → Prop) : SimpleGraph L where
  Adj u v := u ≠ v ∧ ∃ r : R, G u r ∧ G v r
  symm.symm _ _ := fun ⟨hne, r, h1, h2⟩ ↦ ⟨hne.symm, r, h2, h1⟩
  loopless.irrefl _ h := h.1 rfl

instance instDecidableRelBipartiteHalfSimpleGraph [DecidableEq L] [Fintype R]
    (G : L → R → Prop) [∀ l r, Decidable (G l r)] :
    DecidableRel (bipartiteHalfSimpleGraph G).Adj :=
  fun u v ↦ inferInstanceAs (Decidable (u ≠ v ∧ ∃ r : R, G u r ∧ G v r))

/-- Removing self-loops from `bipartiteHalfRel G` reduces the neighborhood size of any subset `S`
by at most `#S`. -/
theorem card_neighbors_bipartiteHalfRel_le_card_biUnion_add
    [Fintype L] [DecidableEq L] [Fintype R]
    (G : L → R → Prop) [∀ l r, Decidable (G l r)] (S : Finset L) :
    #(Cslib.Bipartite.neighbors (bipartiteHalfRel G) S) ≤
      #(S.biUnion fun u ↦ (bipartiteHalfSimpleGraph G).neighborFinset u) + #S := by
  have hsub :
      Cslib.Bipartite.neighbors (bipartiteHalfRel G) S ⊆
        (S.biUnion fun u ↦ (bipartiteHalfSimpleGraph G).neighborFinset u) ∪ S := by
    intro v hv
    obtain ⟨u, hu, r, hur, hvr⟩ := Cslib.Bipartite.mem_neighbors.mp hv
    by_cases huv : u = v
    · exact mem_union_right _ (huv ▸ hu)
    · refine mem_union_left _ (mem_biUnion.mpr ⟨u, hu, ?_⟩)
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨huv, r, hur, hvr⟩
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- Small-set regular `(K, ε)`-lossless vertex expansion predicate on a `D`-regular simple graph. -/
@[expose]
def IsRegularLosslessExpander {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D K : ℕ) (ε : ℝ) : Prop :=
  G.IsRegularOfDegree D ∧
    ∀ S : Finset V, #S ≤ K →
      (1 - ε) * (D : ℝ) * (#S : ℝ) ≤ (#(S.biUnion fun v ↦ G.neighborFinset v) : ℝ)

/-- Small-set max-degree `(K, ε)`-lossless vertex expansion predicate on a simple graph. -/
@[expose]
def IsMaxDegreeLosslessExpander {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℕ) (ε : ℝ) : Prop :=
  ∀ S : Finset V, #S ≤ K →
    (1 - ε) * (G.maxDegree : ℝ) * (#S : ℝ) ≤ (#(S.biUnion fun v ↦ G.neighborFinset v) : ℝ)

end BipartiteHalf

end CslibFrontier.Bipartite
