/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
public import Mathlib.Data.Fintype.Pi

import CslibFrontier.Foundations.Quantum.Measurement.Overlap
import CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap
import Mathlib.Data.Fintype.Card

/-!
# Quantum Adversary Relation and Lower Bound for Element Distinctness

This module develops the combinatorial adversary relation between injective and almost-injective
maps `f : ι → ι` on a finite domain `ι` and derives the standard `Ω(√|ι|)` quantum value-query
lower bound for element distinctness under standard Lean axioms.

## Main definitions

* `CslibFrontier.QuantumQuery.IsAlmostInjective`: a map `f : ι → α` on a finite domain `ι` whose
  image has cardinality `|ι| - 1` (`#(univ.image f) + 1 = Fintype.card ι`), so exactly one unordered
  pair of distinct inputs collides.
* `CslibFrontier.QuantumQuery.elemDistinctBool`: Boolean decision predicate
  `decide (Function.Injective f)` for element distinctness.
* `CslibFrontier.QuantumQuery.elemDistinctRel`: single-coordinate perturbation relation between
  injective maps `f : ι → ι` and almost-injective maps `g : ι → ι`.

## Main results

* `CslibFrontier.QuantumQuery.card_elemDistinctRel_fst`: every injective `f : ι → ι` has
  `|ι| * (|ι| - 1)` almost-injective neighbors in `elemDistinctRel ι`.
* `CslibFrontier.QuantumQuery.card_elemDistinctRel_snd`: every almost-injective `g : ι → ι`
  occurring in `elemDistinctRel ι` has `2` injective neighbors.
* `CslibFrontier.QuantumQuery.card_elemDistinctRel_diff_fst`: at each coordinate `i`, an injective
  `f` differs from `|ι| - 1` neighbors in `elemDistinctRel ι`.
* `CslibFrontier.QuantumQuery.card_elemDistinctRel_diff_snd_le`: at each coordinate `i`, an
  almost-injective `g` differs from at most `1` neighbor in `elemDistinctRel ι`.
* `CslibFrontier.QuantumQuery.one_sub_two_mul_sqrt_mul_sqrt_le_of_elementDistinctness`:
  bounded-error quantum value-query algorithms deciding element distinctness on `ι → ι` (`2 ≤ |ι|`)
  satisfy `(1 - 2 * √(ε * (1 - ε))) * √(2 * |ι|) ≤ 2 * T`.
-/

public section

namespace CslibFrontier.QuantumQuery

open Finset Cslib.Quantum

section Combinatorics

variable {ι α : Type*} [Fintype ι]

/-- A map `f : ι → α` on a finite domain `ι` is *almost injective* if its image has cardinality
`|ι| - 1`, equivalently if `f` has a unique colliding pair of distinct domain elements. -/
def IsAlmostInjective [DecidableEq α] (f : ι → α) : Prop :=
  #(univ.image f) + 1 = Fintype.card ι

instance instDecidableIsAlmostInjective [DecidableEq α] (f : ι → α) :
    Decidable (IsAlmostInjective f) :=
  inferInstanceAs (Decidable (#(univ.image f) + 1 = Fintype.card ι))

/-- The image of an almost-injective map `f : ι → α` has cardinality `Fintype.card ι - 1`. -/
theorem IsAlmostInjective.card_image_eq [DecidableEq α] {f : ι → α} (hf : IsAlmostInjective f) :
    #(univ.image f) = Fintype.card ι - 1 := by
  rw [IsAlmostInjective] at hf
  omega

/-- An almost-injective map is not injective. -/
theorem IsAlmostInjective.not_injective [DecidableEq α] {f : ι → α} (hf : IsAlmostInjective f) :
    ¬ Function.Injective f := by
  intro hinj
  have hcard : #(univ.image f) = Fintype.card ι := by
    rw [card_image_of_injective _ hinj, card_univ]
  rw [IsAlmostInjective, hcard] at hf
  omega

/-- Boolean decision predicate for element distinctness on `ι → α`: `true` iff `f` is injective. -/
def elemDistinctBool [DecidableEq α] (f : ι → α) : Bool :=
  decide (Function.Injective f)

@[simp]
theorem elemDistinctBool_eq_true_iff [DecidableEq α] {f : ι → α} :
    elemDistinctBool f = true ↔ Function.Injective f :=
  decide_eq_true_iff

@[simp]
theorem elemDistinctBool_eq_false_iff [DecidableEq α] {f : ι → α} :
    elemDistinctBool f = false ↔ ¬ Function.Injective f :=
  decide_eq_false_iff_not

variable [DecidableEq ι]

/-- Updating an injective map `f : ι → ι` at `i` to any `y ≠ f i` yields an almost-injective map. -/
theorem isAlmostInjective_update_of_injective {f : ι → ι} (hf : Function.Injective f) (i y : ι)
    (hy : y ≠ f i) : IsAlmostInjective (Function.update f i y) := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  obtain ⟨j, rfl⟩ := hsurj y
  have hij : j ≠ i := fun h => hy (congrArg f h)
  have himg : univ.image (Function.update f i (f j)) = (univ.erase i).image f := by
    ext z
    simp only [mem_image, mem_erase, mem_univ, true_and, and_true]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      by_cases hx : x = i
      · subst hx
        exact ⟨j, hij, by simp⟩
      · exact ⟨x, hx, by simp [hx]⟩
    · rintro ⟨x, hxi, rfl⟩
      exact ⟨x, by simp [hxi]⟩
  have hi_mem : i ∈ (univ : Finset ι) := mem_univ i
  rw [IsAlmostInjective, himg, card_image_of_injective _ hf, card_erase_of_mem hi_mem, card_univ]
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

/-- Single-coordinate perturbation relation on `κ → κ` pairing injective maps `f` with
almost-injective maps `g` that differ from `f` at a single coordinate. -/
def elemDistinctRel (κ : Type*) [Fintype κ] [DecidableEq κ] : Finset ((κ → κ) × (κ → κ)) :=
  univ.filter fun p =>
    Function.Injective p.1 ∧ IsAlmostInjective p.2 ∧ #{i : κ | p.1 i ≠ p.2 i} = 1

/-- Membership characterization for `elemDistinctRel ι`. -/
theorem mem_elemDistinctRel {p : (ι → ι) × (ι → ι)} :
    p ∈ elemDistinctRel ι ↔
      Function.Injective p.1 ∧ IsAlmostInjective p.2 ∧ #{i : ι | p.1 i ≠ p.2 i} = 1 := by
  simp [elemDistinctRel]

private theorem card_ne_update_self (f : ι → ι) (i y : ι) (hy : y ≠ f i) :
    #{x : ι | f x ≠ Function.update f i y x} = 1 := by
  have hset : ({x : ι | f x ≠ Function.update f i y x} : Finset ι) = {i} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    by_cases hx : x = i
    · subst hx
      simp [hy.symm]
    · simp [hx]
  rw [hset, card_singleton]

/-- When `2 ≤ Fintype.card ι`, `elemDistinctRel ι` is nonempty. -/
theorem elemDistinctRel_nonempty (hcard : 2 ≤ Fintype.card ι) :
    (elemDistinctRel ι).Nonempty := by
  have hnt : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine ⟨(id, Function.update id i j), mem_elemDistinctRel.mpr ⟨Function.injective_id, ?_, ?_⟩⟩
  · exact isAlmostInjective_update_of_injective Function.injective_id i j hij.symm
  · exact card_ne_update_self id i j hij.symm

/-- At a fixed coordinate `i`, every injective `f : ι → ι` has exactly `|ι| - 1` almost-injective
partners in `elemDistinctRel ι` differing from `f` at `i`. -/
theorem card_elemDistinctRel_diff_fst {f : ι → ι} (hf : Function.Injective f) (i : ι) :
    #{q ∈ elemDistinctRel ι | q.1 i ≠ q.2 i ∧ q.1 = f} = Fintype.card ι - 1 := by
  have himg : ({q ∈ elemDistinctRel ι | q.1 i ≠ q.2 i ∧ q.1 = f} : Finset _) =
      (univ.erase (f i)).image (fun y => (f, Function.update f i y)) := by
    ext ⟨f', g⟩
    simp only [mem_filter, mem_elemDistinctRel, mem_image, mem_erase, mem_univ, and_true,
      Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨_, _, h1⟩, hne_i, hf_eq⟩
      subst hf_eq
      refine ⟨g i, hne_i.symm, rfl, ?_⟩
      obtain ⟨k, hk⟩ := card_eq_one.mp h1
      have hik : i = k := mem_singleton.mp (hk ▸ mem_filter.mpr ⟨mem_univ i, hne_i⟩)
      subst hik
      ext x
      by_cases hx : x = i
      · subst hx; simp
      · have hnot : x ∉ ({i} : Finset ι) := by simp [hx]
        rw [← hk, mem_filter] at hnot
        have heq : f' x = g x := by simpa using hnot
        rw [Function.update_of_ne hx, heq]
    · rintro ⟨y, hy, rfl, rfl⟩
      refine ⟨⟨hf, isAlmostInjective_update_of_injective hf i y hy,
        card_ne_update_self f i y hy⟩, ?_, rfl⟩
      simp [hy.symm]
  rw [himg, card_image_of_injective, card_erase_of_mem (mem_univ _), card_univ]
  intro y₁ y₂ h
  have h2 := congrFun (Prod.mk.inj h).2 i
  simpa using h2

/-- Every injective `f : ι → ι` lies in exactly `|ι| * (|ι| - 1)` pairs of `elemDistinctRel ι`. -/
theorem card_elemDistinctRel_fst {f : ι → ι} (hf : Function.Injective f) :
    #{q ∈ elemDistinctRel ι | q.1 = f} = Fintype.card ι * (Fintype.card ι - 1) := by
  have hpart : ({q ∈ elemDistinctRel ι | q.1 = f} : Finset _) =
      univ.biUnion (fun i : ι => {q ∈ elemDistinctRel ι | q.1 i ≠ q.2 i ∧ q.1 = f}) := by
    ext q
    simp only [mem_filter, mem_elemDistinctRel, mem_biUnion, mem_univ, true_and]
    refine ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ?_, fun ⟨i, ⟨h1, h2, h3⟩, _, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < #{i : ι | q.1 i ≠ q.2 i})
    exact ⟨i, ⟨h1, h2, h3⟩, (mem_filter.mp hi).2, h4⟩
  rw [hpart, card_biUnion]
  · simp [card_elemDistinctRel_diff_fst hf]
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro q hqi hqj
    obtain ⟨hqR, hnei, _⟩ := mem_filter.mp hqi
    obtain ⟨_, hnej, _⟩ := mem_filter.mp hqj
    obtain ⟨k, hk⟩ := card_eq_one.mp (mem_elemDistinctRel.mp hqR).2.2
    have hik : i = k := mem_singleton.mp (hk ▸ mem_filter.mpr ⟨mem_univ i, hnei⟩)
    have hjk : j = k := mem_singleton.mp (hk ▸ mem_filter.mpr ⟨mem_univ j, hnej⟩)
    exact hij (hik.trans hjk.symm)

omit [Fintype ι] in
private theorem eq_update_missing_of_mem_elemDistinctRel [Finite ι] {f₀ f g : ι → ι} {i₀ k : ι}
    (hf₀ : Function.Injective f₀) (hg_eq : g = Function.update f₀ i₀ (g i₀))
    (hne₀ : f₀ i₀ ≠ g i₀) (hf : Function.Injective f) (hf_eq : f = Function.update g k (f k)) :
    f k = f₀ i₀ := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  obtain ⟨x, hx⟩ := hsurj (f₀ i₀)
  by_cases hxk : x = k
  · exact hxk ▸ hx
  · exfalso
    have hfx : f x = g x := by rw [hf_eq, Function.update_of_ne hxk]
    rw [hfx, hg_eq] at hx
    by_cases hxi₀ : x = i₀
    · subst hxi₀
      simp only [Function.update_self] at hx
      exact hne₀ hx.symm
    · rw [Function.update_of_ne hxi₀] at hx
      exact hxi₀ (hf₀ hx)

/-- At any coordinate `k`, an almost-injective `g : ι → ι` differs from at most `1` injective
partner in `elemDistinctRel ι`. -/
theorem card_elemDistinctRel_diff_snd_le (g : ι → ι) (k : ι) :
    #{q ∈ elemDistinctRel ι | q.1 k ≠ q.2 k ∧ q.2 = g} ≤ 1 := by
  refine card_le_one.mpr fun ⟨f₁, g₁⟩ h₁ ⟨f₂, g₂⟩ h₂ => ?_
  obtain ⟨hR₁, hne₁, hg₁⟩ := mem_filter.mp h₁
  obtain ⟨hR₂, hne₂, hg₂⟩ := mem_filter.mp h₂
  dsimp only at hg₁ hg₂ hne₁ hne₂
  rw [hg₁] at hR₁ hne₁
  rw [hg₂] at hR₂ hne₂
  obtain ⟨hf₁, _, hcard₁⟩ := mem_elemDistinctRel.mp hR₁
  obtain ⟨hf₂, _, hcard₂⟩ := mem_elemDistinctRel.mp hR₂
  dsimp only at hf₁ hf₂ hcard₁ hcard₂
  have hg_f₁ : g = Function.update f₁ k (g k) := by
    obtain ⟨m, hm⟩ := card_eq_one.mp hcard₁
    have hkm : k = m := mem_singleton.mp (hm ▸ mem_filter.mpr ⟨mem_univ k, hne₁⟩)
    subst hkm
    ext x
    by_cases hxk : x = k
    · subst hxk; simp
    · have hnot : x ∉ ({k} : Finset ι) := by simp [hxk]
      rw [← hm, mem_filter] at hnot
      have heq : f₁ x = g x := by simpa using hnot
      rw [Function.update_of_ne hxk, heq]
  have hf₂_upd : f₂ = Function.update g k (f₂ k) := by
    obtain ⟨m, hm⟩ := card_eq_one.mp hcard₂
    have hkm : k = m := mem_singleton.mp (hm ▸ mem_filter.mpr ⟨mem_univ k, hne₂⟩)
    subst hkm
    ext x
    by_cases hxk : x = k
    · subst hxk; simp
    · have hnot : x ∉ ({k} : Finset ι) := by simp [hxk]
      rw [← hm, mem_filter] at hnot
      have heq : f₂ x = g x := by simpa using hnot
      rw [Function.update_of_ne hxk, heq]
  have hf₁_upd : f₁ = Function.update g k (f₁ k) := by
    ext x
    by_cases hxk : x = k
    · subst hxk; simp
    · rw [Function.update_of_ne hxk, hg_f₁, Function.update_of_ne hxk]
  have hval : f₂ k = f₁ k :=
    eq_update_missing_of_mem_elemDistinctRel hf₁ hg_f₁ hne₁ hf₂ hf₂_upd
  exact Prod.ext (hf₁_upd.trans (hval ▸ hf₂_upd.symm)) (hg₁.trans hg₂.symm)

/-- Every pair `(f, g) ∈ elemDistinctRel ι` has exactly `2` partners with second coordinate `g`. -/
theorem card_elemDistinctRel_snd {p : (ι → ι) × (ι → ι)} (hp : p ∈ elemDistinctRel ι) :
    #{q ∈ elemDistinctRel ι | q.2 = p.2} = 2 := by
  obtain ⟨f₀, g⟩ := p
  obtain ⟨hf₀, hg_almost, hcard₀⟩ := mem_elemDistinctRel.mp hp
  dsimp only at hf₀ hg_almost hcard₀ ⊢
  obtain ⟨i₀, hi₀⟩ := card_eq_one.mp hcard₀
  have hmem_i₀ : i₀ ∈ ({i : ι | f₀ i ≠ g i} : Finset ι) := hi₀ ▸ mem_singleton_self i₀
  have hne₀ : f₀ i₀ ≠ g i₀ := (mem_filter.mp hmem_i₀).2
  have hg_eq : g = Function.update f₀ i₀ (g i₀) := by
    ext x
    by_cases hx : x = i₀
    · subst hx; simp
    · have hnot : x ∉ ({i₀} : Finset ι) := by simp [hx]
      rw [← hi₀, mem_filter] at hnot
      have heq : f₀ x = g x := by simpa using hnot
      rw [Function.update_of_ne hx, heq]
  have hsurj₀ : Function.Surjective f₀ := Finite.injective_iff_surjective.mp hf₀
  obtain ⟨j₀, hj₀⟩ := hsurj₀ (g i₀)
  have hij₀ : i₀ ≠ j₀ := fun h => hne₀ ((congrArg f₀ h).trans hj₀)
  have hg_eq' : g = Function.update f₀ i₀ (f₀ j₀) := by rw [hj₀]; exact hg_eq
  let f₁ : ι → ι := f₀ ∘ Equiv.swap i₀ j₀
  have hf₁_inj : Function.Injective f₁ := hf₀.comp (Equiv.injective _)
  have hf₁_mem : (f₁, g) ∈ elemDistinctRel ι := by
    refine mem_elemDistinctRel.mpr ⟨hf₁_inj, hg_almost, ?_⟩
    have hg_f₁ : g = Function.update f₁ j₀ (f₁ i₀) := by
      ext x
      rcases eq_or_ne x j₀ with rfl | hxj
      · simp [f₁, hg_eq', hij₀.symm]
      · rcases eq_or_ne x i₀ with rfl | hxi
        · rw [hg_eq', Function.update_self, Function.update_of_ne hij₀]
          simp [f₁]
        · simp [f₁, hg_eq', hxi, hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]
    have hne₁ : f₁ i₀ ≠ f₁ j₀ := hf₁_inj.ne hij₀
    rw [hg_f₁]
    exact card_ne_update_self f₁ j₀ (f₁ i₀) hne₁
  have hpair_ne : (f₀, g) ≠ (f₁, g) := by
    intro heq
    have hval := congrFun (Prod.mk.inj heq).1 i₀
    simp only [f₁, Function.comp_apply, Equiv.swap_apply_left] at hval
    exact hij₀ (hf₀ hval)
  have hset : ({q ∈ elemDistinctRel ι | q.2 = g} : Finset _) = {(f₀, g), (f₁, g)} := by
    ext ⟨f, g'⟩
    simp only [mem_filter, mem_insert, mem_singleton, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨hR, hg'⟩
      rw [hg'] at hR ⊢
      obtain ⟨hf, _, hcard⟩ := mem_elemDistinctRel.mp hR
      dsimp only at hf hcard
      obtain ⟨k, hk⟩ := card_eq_one.mp hcard
      have hf_upd : f = Function.update g k (f k) := by
        ext x
        rcases eq_or_ne x k with rfl | hxk
        · simp
        · have hnot : x ∉ ({k} : Finset ι) := by simp [hxk]
          rw [← hk, mem_filter] at hnot
          have heq : f x = g x := by simpa using hnot
          rw [Function.update_of_ne hxk, heq]
      have hfk : f k = f₀ i₀ :=
        eq_update_missing_of_mem_elemDistinctRel hf₀ hg_eq hne₀ hf hf_upd
      have hk_or : k = i₀ ∨ k = j₀ := by
        by_contra! hneither
        have hfi : f i₀ = g i₀ := by rw [hf_upd, Function.update_of_ne hneither.1.symm]
        have hfj : f j₀ = g j₀ := by rw [hf_upd, Function.update_of_ne hneither.2.symm]
        have hgj : g j₀ = f₀ j₀ := by rw [hg_eq', Function.update_of_ne hij₀.symm]
        exact hij₀ (hf (hfi.trans (hj₀.symm.trans (hgj.symm.trans hfj.symm))))
      rcases hk_or with hk_eq | hk_eq
      · subst k
        left
        refine ⟨?_, rfl⟩
        ext x
        rcases eq_or_ne x i₀ with rfl | hxi
        · exact hfk
        · rw [hf_upd, Function.update_of_ne hxi, hg_eq', Function.update_of_ne hxi]
      · subst k
        right
        refine ⟨?_, rfl⟩
        ext x
        rcases eq_or_ne x j₀ with rfl | hxj
        · rw [hfk]
          simp [f₁]
        · rcases eq_or_ne x i₀ with rfl | hxi
          · rw [hf_upd, Function.update_of_ne hij₀, hg_eq', Function.update_self]
            simp [f₁]
          · rw [hf_upd, Function.update_of_ne hxj]
            simp [f₁, hg_eq', hxi, Equiv.swap_apply_of_ne_of_ne hxi hxj]
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hp, rfl⟩
      · exact ⟨hf₁_mem, rfl⟩
  rw [hset, card_pair hpair_ne]

end Combinatorics

/-! ### Standard quantum value-query lower bound for element distinctness -/

section QuantumLowerBound

variable {ι V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Fintype W]

/-- **Ambainis adversary lower bound for element distinctness**: any `T`-query quantum value-query
algorithm `(step, U, ψ₀)` with `‖ψ₀‖ = 1` and classical readout `out : ι × V × W → Bool` that
decides `elemDistinctBool` on `ι → ι` (`2 ≤ Fintype.card ι`) with error at most `ε` (`2 * ε ≤ 1`)
satisfies `(1 - 2 * √(ε * (1 - ε))) * √(2 * Fintype.card ι) ≤ 2 * T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_of_elementDistinctness
    (hcard : 2 ≤ Fintype.card ι)
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → Bool) {ε : ℝ}
    (h_inj : ∀ f : ι → ι, Function.Injective f →
      1 - ε ≤ measureProb (runValue step U ψ₀ f T) {q | out q = true})
    (h_almost : ∀ g : ι → ι, IsAlmostInjective g →
      1 - ε ≤ measureProb (runValue step U ψ₀ g T) {q | out q = false})
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * √(2 * (Fintype.card ι : ℝ)) ≤ 2 * T := by
  have hR := elemDistinctRel_nonempty (ι := ι) hcard
  have hne : ∀ p ∈ elemDistinctRel ι, elemDistinctBool p.1 ≠ elemDistinctBool p.2 := by
    intro p hp
    obtain ⟨hf, hg, _⟩ := mem_elemDistinctRel.mp hp
    rw [elemDistinctBool_eq_true_iff.mpr hf, elemDistinctBool_eq_false_iff.mpr hg.not_injective]
    decide
  have h₁ : ∀ p ∈ elemDistinctRel ι,
      1 - ε ≤ measureProb (runValue step U ψ₀ p.1 T) {q | out q = elemDistinctBool p.1} := by
    intro p hp
    obtain ⟨hf, _, _⟩ := mem_elemDistinctRel.mp hp
    rw [elemDistinctBool_eq_true_iff.mpr hf]
    exact h_inj p.1 hf
  have h₂ : ∀ p ∈ elemDistinctRel ι,
      1 - ε ≤ measureProb (runValue step U ψ₀ p.2 T) {q | out q = elemDistinctBool p.2} := by
    intro p hp
    obtain ⟨_, hg, _⟩ := mem_elemDistinctRel.mp hp
    rw [elemDistinctBool_eq_false_iff.mpr hg.not_injective]
    exact h_almost p.2 hg
  have hmain := one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value step U hψ₀ T out
    elemDistinctBool hR hne h₁ h₂ hε
    (m := Fintype.card ι * (Fintype.card ι - 1)) (m' := 2) (L := Fintype.card ι - 1)
    (fun p hp => (card_elemDistinctRel_fst (mem_elemDistinctRel.mp hp).1).ge)
    (fun p hp => (card_elemDistinctRel_snd hp).ge)
    (fun p hp i _ => by
      have hfst := (card_elemDistinctRel_diff_fst (mem_elemDistinctRel.mp hp).1 i).le
      have hsnd := card_elemDistinctRel_diff_snd_le (ι := ι) p.2 i
      exact (Nat.mul_le_mul hfst hsnd).trans_eq (Nat.mul_one _))
  set d : ℕ := Fintype.card ι - 1
  have hd_pos : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hmul : (((Fintype.card ι * d : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) =
      (2 * (Fintype.card ι : ℝ)) * (d : ℝ) := by
    push_cast; ring
  have hsqrt : √((((Fintype.card ι * d : ℕ) : ℝ) * ((2 : ℕ) : ℝ))) =
      √(2 * (Fintype.card ι : ℝ)) * √(d : ℝ) := by
    rw [hmul, Real.sqrt_mul (by positivity)]
  rw [hsqrt] at hmain
  refine le_of_mul_le_mul_right ?_ hd_pos
  linarith

-- Non-vacuity witness on `Fin 4`: `elemDistinctRel (Fin 4)` is nonempty with `m = 12, m' = 2`.
private example : (elemDistinctRel (Fin 4)).Nonempty ∧
    #{q ∈ elemDistinctRel (Fin 4) | q.1 = id} = 12 :=
  ⟨elemDistinctRel_nonempty (by decide), card_elemDistinctRel_fst Function.injective_id⟩

end QuantumLowerBound

end CslibFrontier.QuantumQuery
