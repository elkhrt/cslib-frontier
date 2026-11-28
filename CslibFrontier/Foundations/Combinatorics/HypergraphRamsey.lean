/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

/-!
# Two-Color Hypergraph Ramsey Theorem

This module proves the finite two-color $r$-uniform hypergraph Ramsey theorem via the standard
Erdős–Rado double induction on uniformity $r$ and target clique sum $a + b$.

## Main results

* `CslibFrontier.Combinatorics.exists_hypergraph_ramsey`: for every uniformity $r$ and target
  clique sizes $a, b \in \mathbb{N}$, there exists $N \in \mathbb{N}$ such that every two-coloring
  of the $r$-element subsets of a finite set of cardinality at least $N$ admits either a
  `false`-monochromatic subset of size $a$ or a `true`-monochromatic subset of size $b$.
* `CslibFrontier.Combinatorics.exists_hypergraph_ramsey_sym`: symmetric form guaranteeing a
  monochromatic subset of size $m$ in some color.
-/

namespace CslibFrontier.Combinatorics

public section

universe u

/-- **Two-color $r$-uniform hypergraph Ramsey theorem**: for every uniformity $r$ and target sizes
$a, b \in \mathbb{N}$, there exists $N \in \mathbb{N}$ such that every two-coloring of the
$r$-element subsets of a finite set $U$ with $|U| \ge N$ admits either a `false`-monochromatic
subset of size $a$ or a `true`-monochromatic subset of size $b$. -/
theorem exists_hypergraph_ramsey :
    ∀ (r a b : ℕ), ∃ N : ℕ, ∀ {α : Type u} [DecidableEq α] (U : Finset α),
      N ≤ U.card → ∀ c : Finset α → Bool,
        (∃ W ⊆ U, W.card = a ∧ ∀ S ⊆ W, S.card = r → c S = false) ∨
        (∃ W ⊆ U, W.card = b ∧ ∀ S ⊆ W, S.card = r → c S = true) := by
  intro r
  induction r with
  | zero =>
    intro a b
    refine ⟨max a b, fun U hU c ↦ ?_⟩
    cases hc : c ∅
    · left
      obtain ⟨W, hWU, hWc⟩ := Finset.exists_subset_card_eq ((le_max_left a b).trans hU)
      refine ⟨W, hWU, hWc, fun S _ hS ↦ ?_⟩
      rw [Finset.card_eq_zero.mp hS, hc]
    · right
      obtain ⟨W, hWU, hWc⟩ := Finset.exists_subset_card_eq ((le_max_right a b).trans hU)
      refine ⟨W, hWU, hWc, fun S _ hS ↦ ?_⟩
      rw [Finset.card_eq_zero.mp hS, hc]
  | succ r ih_r =>
    intro a b
    suffices hsum : ∀ s a b : ℕ, a + b = s →
        ∃ N : ℕ, ∀ {α : Type u} [DecidableEq α] (U : Finset α),
          N ≤ U.card → ∀ c : Finset α → Bool,
            (∃ W ⊆ U, W.card = a ∧ ∀ S ⊆ W, S.card = r + 1 → c S = false) ∨
            (∃ W ⊆ U, W.card = b ∧ ∀ S ⊆ W, S.card = r + 1 → c S = true) by
      exact hsum (a + b) a b rfl
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih_s =>
      intro a b hab
      by_cases ha : a ≤ r
      · refine ⟨a, fun U hU c ↦ Or.inl ?_⟩
        obtain ⟨W, hWU, hWc⟩ := Finset.exists_subset_card_eq hU
        refine ⟨W, hWU, hWc, fun S hSW hSc ↦ ?_⟩
        have := Finset.card_le_card hSW
        omega
      · by_cases hb : b ≤ r
        · refine ⟨b, fun U hU c ↦ Or.inr ?_⟩
          obtain ⟨W, hWU, hWc⟩ := Finset.exists_subset_card_eq hU
          refine ⟨W, hWU, hWc, fun S hSW hSc ↦ ?_⟩
          have := Finset.card_le_card hSW
          omega
        · obtain ⟨A, hA⟩ := ih_s (a - 1 + b) (by omega) (a - 1) b rfl
          obtain ⟨B, hB⟩ := ih_s (a + (b - 1)) (by omega) a (b - 1) rfl
          obtain ⟨M, hM⟩ := ih_r A B
          refine ⟨M + 1, fun U hU c ↦ ?_⟩
          have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨v, hv⟩ := hUne
          let U' := U.erase v
          have hU' : M ≤ U'.card := by rw [Finset.card_erase_of_mem hv]; omega
          rcases hM U' hU' (fun S ↦ c (insert v S)) with
            ⟨V, hVU', hVc, hVmono⟩ | ⟨V, hVU', hVc, hVmono⟩
          · have hvV : v ∉ V := fun h ↦ (Finset.notMem_erase v U) (hVU' h)
            have hVU : V ⊆ U := hVU'.trans (Finset.erase_subset v U)
            rcases hA V (by omega) c with ⟨W', hW'V, hW'c, hW'mono⟩ | ⟨W, hWV, hWc, hWmono⟩
            · left
              have hvW' : v ∉ W' := fun h ↦ hvV (hW'V h)
              refine ⟨insert v W', Finset.insert_subset hv (hW'V.trans hVU), ?_, ?_⟩
              · rw [Finset.card_insert_of_notMem hvW']; omega
              · intro S hSW hSc
                by_cases hvS : v ∈ S
                · have hSe : S.erase v ⊆ V := fun x hx ↦ by
                    have hx' := hSW (Finset.erase_subset v S hx)
                    rcases Finset.mem_insert.mp hx' with rfl | hxW'
                    · exact absurd rfl (Finset.ne_of_mem_erase hx)
                    · exact hW'V hxW'
                  have hSec : (S.erase v).card = r := by
                    rw [Finset.card_erase_of_mem hvS]; omega
                  have hSins : insert v (S.erase v) = S := Finset.insert_erase hvS
                  rw [← hSins]
                  exact hVmono (S.erase v) hSe hSec
                · have hSW' : S ⊆ W' := fun x hx ↦ by
                    rcases Finset.mem_insert.mp (hSW hx) with rfl | hxW'
                    · exact absurd hx hvS
                    · exact hxW'
                  exact hW'mono S hSW' hSc
            · exact Or.inr ⟨W, hWV.trans hVU, hWc, hWmono⟩
          · have hvV : v ∉ V := fun h ↦ (Finset.notMem_erase v U) (hVU' h)
            have hVU : V ⊆ U := hVU'.trans (Finset.erase_subset v U)
            rcases hB V (by omega) c with ⟨W, hWV, hWc, hWmono⟩ | ⟨W', hW'V, hW'c, hW'mono⟩
            · exact Or.inl ⟨W, hWV.trans hVU, hWc, hWmono⟩
            · right
              have hvW' : v ∉ W' := fun h ↦ hvV (hW'V h)
              refine ⟨insert v W', Finset.insert_subset hv (hW'V.trans hVU), ?_, ?_⟩
              · rw [Finset.card_insert_of_notMem hvW']; omega
              · intro S hSW hSc
                by_cases hvS : v ∈ S
                · have hSe : S.erase v ⊆ V := fun x hx ↦ by
                    have hx' := hSW (Finset.erase_subset v S hx)
                    rcases Finset.mem_insert.mp hx' with rfl | hxW'
                    · exact absurd rfl (Finset.ne_of_mem_erase hx)
                    · exact hW'V hxW'
                  have hSec : (S.erase v).card = r := by
                    rw [Finset.card_erase_of_mem hvS]; omega
                  have hSins : insert v (S.erase v) = S := Finset.insert_erase hvS
                  rw [← hSins]
                  exact hVmono (S.erase v) hSe hSec
                · have hSW' : S ⊆ W' := fun x hx ↦ by
                    rcases Finset.mem_insert.mp (hSW hx) with rfl | hxW'
                    · exact absurd hx hvS
                    · exact hxW'
                  exact hW'mono S hSW' hSc

/-- Symmetric form of the two-color $r$-uniform hypergraph Ramsey theorem: every sufficiently
large finite set admits a monochromatic subset of size $m$ for any two-coloring of its
$r$-element subsets. -/
theorem exists_hypergraph_ramsey_sym (r m : ℕ) :
    ∃ N : ℕ, ∀ {α : Type u} [DecidableEq α] (U : Finset α),
      N ≤ U.card → ∀ c : Finset α → Bool,
        ∃ b : Bool, ∃ W ⊆ U, W.card = m ∧ ∀ S ⊆ W, S.card = r → c S = b := by
  obtain ⟨N, hN⟩ := exists_hypergraph_ramsey.{u} r m m
  refine ⟨N, fun U hU c ↦ ?_⟩
  rcases hN U hU c with ⟨W, hWU, hWc, hW⟩ | ⟨W, hWU, hWc, hW⟩
  · exact ⟨false, W, hWU, hWc, hW⟩
  · exact ⟨true, W, hWU, hWc, hW⟩

end

end CslibFrontier.Combinatorics
