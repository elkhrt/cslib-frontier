/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Algorithms.Lean.Query.Submodular.ValueQuery
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential Value-Query Lower Bound for Slice-Submodular Set Functions

This module proves that any deterministic adaptive value-query algorithm (`FreeM (ValueQuery α ℝ)`)
achieving any constant approximation factor `c > 0` for maximizing nonnegative set functions on a
finite ground set `E` whose restrictions to the `2 ^ r` slices `Π(A, B) = {S ⊆ E | S ∩ B = A}`
(for some `B ⊆ E` with `|B| ≤ r`) are submodular requires at least `2 ^ r` value queries.

All declarations hold under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)
with zero `PaperLib`, `TauCeti`, or `Papers` dependencies.

## Main definitions

* `CslibFrontier.Query.sliceRestrict`: restriction `S ↦ f (A ∪ (S \ B))` of a set function `f` to
  the slice `Π(A, B)`.
* `CslibFrontier.Query.HasSliceSubmodularRankLe`: predicate asserting that `f` admits a subset
  `B ⊆ E` of cardinality at most `r` on which every slice restriction `sliceRestrict f A B` is
  submodular (`Cslib.Algorithms.Lean.Submodular.IsSubmodular`).

## Main results

* `CslibFrontier.Query.slice_submodular_query_lower_bound`: for any nonempty finite ground set
  `E : Finset α`, `r ≤ E.card`, and `c > 0`, no `FreeM (ValueQuery α ℝ) (Finset α)` program can
  make strictly fewer than `2 ^ r` queries and achieve a `c`-approximation across all nonnegative
  set functions with `HasSliceSubmodularRankLe E f r`.
-/

public section

namespace CslibFrontier.Query

open Cslib
open Cslib.Query
open Cslib.Algorithms.Lean.Submodular

/-- Restriction of a set function `f : Finset α → ℝ` to the slice `{S | S ∩ B = A}`, parameterized
by subsets `D : Finset α` via `D ↦ f (A ∪ (D \ B))`. -/
def sliceRestrict {α : Type} [DecidableEq α] (f : Finset α → ℝ) (A B : Finset α)
    (D : Finset α) : ℝ :=
  f (A ∪ (D \ B))

/-- A set function `f : Finset α → ℝ` has slice-submodular rank at most `r + 1` on `E` if there
exists `B ⊆ E` with `B.card ≤ r` such that every slice restriction `sliceRestrict f A B` (`A ⊆ B`)
is submodular. -/
def HasSliceSubmodularRankLe {α : Type} [DecidableEq α] (E : Finset α)
    (f : Finset α → ℝ) (r : ℕ) : Prop :=
  ∃ B ⊆ E, B.card ≤ r ∧ ∀ A ⊆ B, IsSubmodular (sliceRestrict f A B)

private lemma exists_unqueried_slice {α : Type} [DecidableEq α] {r : ℕ} (B : Finset α)
    (hB : B.card = r) (Q : Finset (Finset α)) (hQ : Q.card < 2 ^ r) :
    ∃ A₀ ⊆ B, ∀ S ∈ Q, S ∩ B ≠ A₀ := by
  have hcard : (Q.image (fun S ↦ S ∩ B)).card < B.powerset.card := by
    rw [Finset.card_powerset, hB]
    exact Finset.card_image_le.trans_lt hQ
  obtain ⟨A₀, hA₀B, hA₀not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨A₀, Finset.mem_powerset.mp hA₀B, fun S hS hEq ↦ hA₀not ?_⟩
  exact Finset.mem_image.mpr ⟨S, hS, hEq⟩

private lemma sliceConst_hasSliceSubmodularRankLe {α : Type} [DecidableEq α] {E B : Finset α}
    {r : ℕ} (hBE : B ⊆ E) (hB : B.card ≤ r) (A₀ : Finset α) (c₁ c₂ : ℝ) :
    HasSliceSubmodularRankLe E (fun S ↦ if S ∩ B = A₀ then c₁ else c₂) r := by
  refine ⟨B, hBE, hB, fun A hAB ↦ ?_⟩
  have hconst : ∀ D : Finset α,
      sliceRestrict (fun S ↦ if S ∩ B = A₀ then c₁ else c₂) A B D =
        if A = A₀ then c₁ else c₂ := fun D ↦ by
    unfold sliceRestrict
    have hinter : (A ∪ (D \ B)) ∩ B = A := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxA | ⟨_, hxB⟩, hxB'⟩
        · exact hxA
        · exact absurd hxB' hxB
      · intro hxA; exact ⟨Or.inl hxA, hAB hxA⟩
    dsimp only
    rw [hinter]
  intro D₁ D₂
  simp only [hconst]
  exact le_rfl

/-- **Exponential Value-Query Lower Bound for Slice-Submodular Maximization**: for any finite
ground set `E : Finset α` with `1 ≤ E.card`, any `r ≤ E.card`, and any constant `c > 0`, no
deterministic value-query program `p : FreeM (ValueQuery α ℝ) (Finset α)` making strictly fewer
than `2 ^ r` queries can achieve a `c`-approximation across all nonnegative set functions with
`HasSliceSubmodularRankLe E f r`. -/
theorem slice_submodular_query_lower_bound {α : Type} [DecidableEq α] {E : Finset α}
    (hE : 1 ≤ E.card) {r : ℕ} (hrE : r ≤ E.card) {c : ℝ} (hc : 0 < c) :
    ¬ ∃ prog : FreeM (ValueQuery α ℝ) (Finset α),
      ∀ f : Finset α → ℝ, (∀ S, 0 ≤ f S) → HasSliceSubmodularRankLe E f r →
        prog.countQueries (ValueQuery.oracleOf f) < 2 ^ r ∧
          ∀ Ω ⊆ E, c * f Ω ≤ f (prog.eval (ValueQuery.oracleOf f)) := by
  rintro ⟨prog, hprog⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · let f₀ : Finset α → ℝ := fun _ ↦ 0
    have hf₀_rk : HasSliceSubmodularRankLe E f₀ 0 := by
      simpa [f₀] using sliceConst_hasSliceSubmodularRankLe (Finset.empty_subset E) le_rfl ∅ 0 0
    obtain ⟨hcost0, _⟩ := hprog f₀ (fun _ ↦ le_rfl) hf₀_rk
    have hQ0 : ValueQuery.queriedSets (ValueQuery.oracleOf f₀) prog = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp
        ((ValueQuery.card_queriedSets_le_countQueries _ prog).trans (Nat.lt_one_iff.mp hcost0).le))
    let Sstar := prog.eval (ValueQuery.oracleOf f₀)
    obtain ⟨e, heE⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hE)
    let f₁ : Finset α → ℝ := fun S ↦ if (e ∈ S ↔ e ∉ Sstar) then 1 else 0
    have hf₁_nn : ∀ S, 0 ≤ f₁ S := fun S ↦ by dsimp [f₁]; split_ifs <;> norm_num
    have hf₁_rk : HasSliceSubmodularRankLe E f₁ 0 := by
      refine ⟨∅, Finset.empty_subset E, by simp, fun A hA ↦ ?_⟩
      obtain rfl : A = ∅ := Finset.subset_empty.mp hA
      intro D₁ D₂
      simp only [sliceRestrict, Finset.empty_union, Finset.sdiff_empty, f₁]
      by_cases he1 : e ∈ D₁ <;> by_cases he2 : e ∈ D₂ <;> by_cases heS : e ∈ Sstar <;>
        simp [he1, he2, heS]
    have hev : prog.eval (ValueQuery.oracleOf f₁) = Sstar :=
      (ValueQuery.eval_eq_of_agree_on_queriedSets prog (by simp [hQ0])).symm
    let Ω : Finset α := if e ∈ Sstar then ∅ else {e}
    have hΩE : Ω ⊆ E := by
      dsimp only [Ω]; split_ifs
      · exact Finset.empty_subset E
      · exact Finset.singleton_subset_iff.mpr heE
    have hf₁_S : f₁ Sstar = 0 := by simp [f₁]
    have hf₁_Ω : f₁ Ω = 1 := by
      dsimp only [f₁, Ω]; by_cases heS : e ∈ Sstar <;> simp [heS]
    have hapx := (hprog f₁ hf₁_nn hf₁_rk).2 Ω hΩE
    rw [hev, hf₁_S, hf₁_Ω] at hapx
    linarith
  · obtain ⟨B, hBE, hBcard⟩ := Finset.exists_subset_card_eq hrE
    let f₀ : Finset α → ℝ := fun _ ↦ 1
    have hf₀_rk : HasSliceSubmodularRankLe E f₀ r := by
      simpa [f₀] using sliceConst_hasSliceSubmodularRankLe hBE hBcard.le ∅ 1 1
    obtain ⟨hcost0, _⟩ := hprog f₀ (fun _ ↦ by norm_num) hf₀_rk
    obtain ⟨A₀, hA₀B, hA₀unq⟩ := exists_unqueried_slice B hBcard
      (ValueQuery.queriedSets (ValueQuery.oracleOf f₀) prog)
      ((ValueQuery.card_queriedSets_le_countQueries _ prog).trans_lt hcost0)
    let Sstar := prog.eval (ValueQuery.oracleOf f₀)
    by_cases hhit : Sstar ∩ B = A₀
    · let f₁ : Finset α → ℝ := fun S ↦ if S ∩ B = A₀ then 0 else 1
      have hf₁_nn : ∀ S, 0 ≤ f₁ S := fun S ↦ by dsimp [f₁]; split_ifs <;> norm_num
      have hf₁_rk : HasSliceSubmodularRankLe E f₁ r :=
        sliceConst_hasSliceSubmodularRankLe hBE hBcard.le A₀ 0 1
      have hev : prog.eval (ValueQuery.oracleOf f₁) = Sstar :=
        (ValueQuery.eval_eq_of_agree_on_queriedSets prog fun S hS ↦ by
          simp [ValueQuery.oracleOf_value, f₀, f₁, hA₀unq S hS]).symm
      have hBne : B.Nonempty := Finset.card_pos.mp (hBcard ▸ hr_pos)
      obtain ⟨A₁, hA₁B, hA₁ne⟩ : ∃ A₁ ⊆ B, A₁ ≠ A₀ := by
        by_cases h0 : A₀ = ∅
        · exact ⟨B, Finset.Subset.rfl, by rw [h0]; exact hBne.ne_empty⟩
        · exact ⟨∅, Finset.empty_subset B, Ne.symm h0⟩
      have hf₁_S : f₁ Sstar = 0 := by simp [f₁, hhit]
      have hf₁_A₁ : f₁ A₁ = 1 := by simp [f₁, Finset.inter_eq_left.mpr hA₁B, hA₁ne]
      have hapx := (hprog f₁ hf₁_nn hf₁_rk).2 A₁ (hA₁B.trans hBE)
      rw [hev, hf₁_S, hf₁_A₁] at hapx
      linarith
    · let C : ℝ := 1 / c + 2
      let f₁ : Finset α → ℝ := fun S ↦ if S ∩ B = A₀ then C else 1
      have hC_nn : 0 ≤ C := by positivity
      have hf₁_nn : ∀ S, 0 ≤ f₁ S := fun S ↦ by dsimp [f₁]; split_ifs <;> linarith
      have hf₁_rk : HasSliceSubmodularRankLe E f₁ r :=
        sliceConst_hasSliceSubmodularRankLe hBE hBcard.le A₀ C 1
      have hev : prog.eval (ValueQuery.oracleOf f₁) = Sstar :=
        (ValueQuery.eval_eq_of_agree_on_queriedSets prog fun S hS ↦ by
          simp [ValueQuery.oracleOf_value, f₀, f₁, hA₀unq S hS]).symm
      have hf₁_S : f₁ Sstar = 1 := by simp [f₁, hhit]
      have hf₁_A₀ : f₁ A₀ = C := by simp [f₁, Finset.inter_eq_left.mpr hA₀B]
      have hapx := (hprog f₁ hf₁_nn hf₁_rk).2 A₀ (hA₀B.trans hBE)
      rw [hev, hf₁_S, hf₁_A₀] at hapx
      have hcC : c * C = 1 + 2 * c := by simp only [C]; field_simp [hc.ne']
      linarith

end CslibFrontier.Query
