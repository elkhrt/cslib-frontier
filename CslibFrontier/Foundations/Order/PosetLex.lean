module

public import Mathlib.Order.WellFoundedSet

/-!
# Poset-Lexicographic Order on Tuples

This module defines the poset-lexicographic partial order `CslibFrontier.Order.PosetLex P L` on
functions `P → L` indexed by a well-founded partial order `P` with values in a linear order `L`:
`f ≤ g` holds iff for every `z : P`, either `f z ≤ g z` or there exists a strictly smaller index
`z' < z` with `f z' < g z'`.

This generalizes the standard lexicographic order on linearly ordered index types to arbitrary
well-founded posets, such as degree-complexity tuples indexed by partially ordered basis elements.

## Main definitions

- `CslibFrontier.Order.PosetLex`: type synonym for `P → L` carrying the poset-lexicographic order.
- `CslibFrontier.Order.toPosetLex` and `CslibFrontier.Order.ofPosetLex`: equivalence maps.
- `CslibFrontier.Order.HasUniqueMinUnder`: predicate asserting existence of a unique minimum
  element of a set with respect to a `PosetLex`-valued complexity measure.

## Main results

- `CslibFrontier.Order.instPartialOrderPosetLex`: `PosetLex P L` forms a `PartialOrder` whenever
  `P` is a well-founded partial order and `L` is a linear order.
- `CslibFrontier.Order.posetLex_le_of_pointwise`: pointwise inequality implies poset-lexicographic
  inequality.
-/

public section

namespace CslibFrontier.Order

/-- Type synonym for tuples `P → L` ordered by the poset-lexicographic relation: `f ≤ g` iff for
every `z : P`, either `f z ≤ g z` or there exists `z' < z` with `f z' < g z'`. -/
@[expose]
def PosetLex (P : Type*) (L : Type*) : Type _ :=
  P → L

/-- Equivalence from `P → L` to `PosetLex P L`. -/
@[expose]
def toPosetLex {P L : Type*} : (P → L) ≃ PosetLex P L :=
  Equiv.refl _

/-- Equivalence from `PosetLex P L` to `P → L`. -/
@[expose]
def ofPosetLex {P L : Type*} : PosetLex P L ≃ (P → L) :=
  Equiv.refl _

@[simp]
theorem ofPosetLex_toPosetLex {P L : Type*} (f : P → L) : ofPosetLex (toPosetLex f) = f :=
  rfl

@[simp]
theorem toPosetLex_ofPosetLex {P L : Type*} (f : PosetLex P L) : toPosetLex (ofPosetLex f) = f :=
  rfl

section PartialOrder

variable {P L : Type*} [PartialOrder P] [LinearOrder L]

instance instLEPosetLex : LE (PosetLex P L) where
  le f g := ∀ z : P, ofPosetLex f z ≤ ofPosetLex g z ∨
    ∃ z' : P, z' < z ∧ ofPosetLex f z' < ofPosetLex g z'

theorem posetLex_le_iff {f g : PosetLex P L} :
    f ≤ g ↔ ∀ z : P, ofPosetLex f z ≤ ofPosetLex g z ∨
      ∃ z' : P, z' < z ∧ ofPosetLex f z' < ofPosetLex g z' :=
  Iff.rfl

theorem posetLex_le_of_pointwise {f g : PosetLex P L} (h : ∀ z, ofPosetLex f z ≤ ofPosetLex g z) :
    f ≤ g :=
  fun z => Or.inl (h z)

/-- Predicate asserting that a set `F` has a unique element minimizing a `PosetLex`-valued
complexity measure `d`. -/
def HasUniqueMinUnder {α : Type*} (F : Set α) (d : α → PosetLex P L) : Prop :=
  ∃! y, y ∈ F ∧ ∀ y' ∈ F, d y ≤ d y'

theorem hasUniqueMinUnder_iff {α : Type*} {F : Set α} {d : α → PosetLex P L} :
    HasUniqueMinUnder F d ↔ ∃! y, y ∈ F ∧ ∀ y' ∈ F, d y ≤ d y' := by
  unfold HasUniqueMinUnder
  rfl

variable [WellFoundedLT P]

theorem posetLex_le_trans {f g h : PosetLex P L} (hfg : f ≤ g) (hgh : g ≤ h) : f ≤ h := by
  intro z
  let S : Set P := {u : P | u ≤ z ∧ (ofPosetLex f u ≠ ofPosetLex g u ∨
    ofPosetLex g u ≠ ofPosetLex h u)}
  by_cases hSne : S.Nonempty
  · obtain ⟨u, huS, humin⟩ := wellFounded_lt.has_min S hSne
    have hprev : ∀ v < u, ofPosetLex f v = ofPosetLex g v ∧ ofPosetLex g v = ofPosetLex h v := by
      intro v hv
      by_contra hne
      push Not at hne
      have hvS : v ∈ S := ⟨le_trans (le_of_lt hv) huS.1, by
        by_cases h1 : ofPosetLex f v = ofPosetLex g v
        · exact Or.inr (hne h1)
        · exact Or.inl h1⟩
      exact humin v hvS hv
    have hfg_u : ofPosetLex f u ≤ ofPosetLex g u := by
      rcases hfg u with hle | ⟨v, hv, hlt⟩
      · exact hle
      · rw [(hprev v hv).1] at hlt; exact absurd hlt (lt_irrefl _)
    have hgh_u : ofPosetLex g u ≤ ofPosetLex h u := by
      rcases hgh u with hle | ⟨v, hv, hlt⟩
      · exact hle
      · rw [(hprev v hv).2] at hlt; exact absurd hlt (lt_irrefl _)
    have hlt_u : ofPosetLex f u < ofPosetLex h u := by
      rcases huS.2 with hne1 | hne2
      · exact lt_of_lt_of_le (lt_of_le_of_ne hfg_u hne1) hgh_u
      · exact lt_of_le_of_lt hfg_u (lt_of_le_of_ne hgh_u hne2)
    rcases eq_or_lt_of_le huS.1 with rfl | hltz
    · exact Or.inl (le_of_lt hlt_u)
    · exact Or.inr ⟨u, hltz, hlt_u⟩
  · have hz_eq : ofPosetLex f z = ofPosetLex h z := by
      have hnot : ¬ (z ≤ z ∧ (ofPosetLex f z ≠ ofPosetLex g z ∨
          ofPosetLex g z ≠ ofPosetLex h z)) := fun hz => hSne ⟨z, hz⟩
      push Not at hnot
      exact (hnot le_rfl).1.trans (hnot le_rfl).2
    exact Or.inl (le_of_eq hz_eq)

theorem posetLex_le_antisymm {f g : PosetLex P L} (hfg : f ≤ g) (hgf : g ≤ f) : f = g := by
  by_contra hne
  have hSne : {u : P | ofPosetLex f u ≠ ofPosetLex g u}.Nonempty := by
    by_contra hemp
    apply hne
    apply ofPosetLex.injective
    funext u
    by_contra hu
    exact hemp ⟨u, hu⟩
  obtain ⟨u, hu, humin⟩ := wellFounded_lt.has_min _ hSne
  have hprev : ∀ v < u, ofPosetLex f v = ofPosetLex g v := by
    intro v hv
    by_contra hfv
    exact humin v hfv hv
  have hfg_u : ofPosetLex f u ≤ ofPosetLex g u := by
    rcases hfg u with hle | ⟨v, hv, hlt⟩
    · exact hle
    · rw [hprev v hv] at hlt; exact absurd hlt (lt_irrefl _)
  have hgf_u : ofPosetLex g u ≤ ofPosetLex f u := by
    rcases hgf u with hle | ⟨v, hv, hlt⟩
    · exact hle
    · rw [hprev v hv] at hlt; exact absurd hlt (lt_irrefl _)
  exact hu (le_antisymm hfg_u hgf_u)

/-- `PosetLex P L` is a partial order whenever `P` is a well-founded partial order and `L` is a
linear order. -/
instance instPartialOrderPosetLex : PartialOrder (PosetLex P L) where
  le := (· ≤ ·)
  le_refl f z := Or.inl (le_refl _)
  le_trans _ _ _ := posetLex_le_trans
  le_antisymm _ _ := posetLex_le_antisymm

end PartialOrder

end CslibFrontier.Order
