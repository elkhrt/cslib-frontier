/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Complexity.Classes.P.Finite
import CslibFrontier.Computability.Complexity.Classes.P.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Complexity.Reduction

/-!
# Finite Symmetric-Difference Invariance of Complexity Classes

Languages whose symmetric difference `(L \ L') ∪ (L' \ L)` is finite share the same membership in
`P`, `NP`, `coNP`, and `PSPACE`, and more generally in any complexity class closed under
intersection and union with `P`.

## Main results

* `Cslib.Complexity.mem_iff_of_finite_symmDiff`: generic finite symmetric-difference invariance
  for classes closed under intersection and union with `P`.
* `Cslib.Complexity.mem_P_iff_of_finite_symmDiff`: finite invariance of `P`.
* `Cslib.Complexity.mem_NP_iff_of_finite_symmDiff`: finite invariance of `NP`.
* `Cslib.Complexity.mem_coNP_iff_of_finite_symmDiff`: finite invariance of `coNP`.
* `Cslib.Complexity.mem_PSPACE_iff_of_finite_symmDiff`: finite invariance of `PSPACE`.
-/

public section

namespace Cslib.Complexity

private theorem eq_diff_union_of_symmDiff {α : Type*} (L L' : Set α) :
    L' = (L ∩ (L \ L')ᶜ) ∪ (L' \ L) := by
  ext x
  by_cases h1 : x ∈ L <;> by_cases h2 : x ∈ L' <;> simp [h1, h2]

/-- Any class of languages over `α` closed under intersection and union with `P enc` is invariant
under finite symmetric differences. -/
theorem mem_iff_of_finite_symmDiff {α : Type} {enc : α ↪ List Bool} {C : Set (Set α)}
    (hInter : ∀ {A B : Set α}, A ∈ C → B ∈ P enc → A ∩ B ∈ C)
    (hUnion : ∀ {A B : Set α}, A ∈ C → B ∈ P enc → A ∪ B ∈ C)
    {L L' : Set α} (hfin : ((L \ L') ∪ (L' \ L)).Finite) : L ∈ C ↔ L' ∈ C := by
  have h1 : (L \ L').Finite := hfin.subset Set.subset_union_left
  have h2 : (L' \ L).Finite := hfin.subset Set.subset_union_right
  have step : ∀ {A B : Set α}, (A \ B).Finite → (B \ A).Finite → A ∈ C → B ∈ C := by
    intro A B hAB hBA hA
    rw [eq_diff_union_of_symmDiff A B]
    exact hUnion (hInter hA (compl_mem_P hAB.mem_P)) hBA.mem_P
  exact ⟨step h1 h2, step h2 h1⟩

/-- Languages with finite symmetric difference have identical membership in `P enc`. -/
theorem mem_P_iff_of_finite_symmDiff {α : Type} {enc : α ↪ List Bool} {L L' : Set α}
    (hfin : ((L \ L') ∪ (L' \ L)).Finite) : L ∈ P enc ↔ L' ∈ P enc :=
  mem_iff_of_finite_symmDiff (fun hA hB => inter_mem_P hA hB) (fun hA hB => union_mem_P hA hB) hfin

/-- Languages with finite symmetric difference have identical membership in `NP enc`. -/
theorem mem_NP_iff_of_finite_symmDiff {α : Type} {enc : α ↪ List Bool} {L L' : Set α}
    (hfin : ((L \ L') ∪ (L' \ L)).Finite) : L ∈ NP enc ↔ L' ∈ NP enc :=
  mem_iff_of_finite_symmDiff (fun hA hB => inter_mem_NP hA (P_subset_NP hB))
    (fun hA hB => union_mem_NP hA (P_subset_NP hB)) hfin

/-- Languages with finite symmetric difference have identical membership in `coNP enc`. -/
theorem mem_coNP_iff_of_finite_symmDiff {α : Type} {enc : α ↪ List Bool} {L L' : Set α}
    (hfin : ((L \ L') ∪ (L' \ L)).Finite) : L ∈ coNP enc ↔ L' ∈ coNP enc :=
  mem_iff_of_finite_symmDiff (fun hA hB => inter_mem_coNP hA (P_subset_coNP hB))
    (fun hA hB => union_mem_coNP hA (P_subset_coNP hB)) hfin

/-- Languages with finite symmetric difference have identical membership in `PSPACE enc`. -/
theorem mem_PSPACE_iff_of_finite_symmDiff {α : Type} {enc : α ↪ List Bool} {L L' : Set α}
    (hfin : ((L \ L') ∪ (L' \ L)).Finite) : L ∈ PSPACE enc ↔ L' ∈ PSPACE enc :=
  mem_iff_of_finite_symmDiff (fun hA hB => inter_mem_PSPACE hA (P_subset_PSPACE hB))
    (fun hA hB => union_mem_PSPACE hA (P_subset_PSPACE hB)) hfin

end Cslib.Complexity
