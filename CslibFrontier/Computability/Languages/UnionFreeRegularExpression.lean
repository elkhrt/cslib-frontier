/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.DFA
public import Mathlib.Computability.RegularExpressions

import Cslib.Computability.Languages.RegularLanguage
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# Union-Free Regular Expressions and Finite Union-Free Decompositions

Building on `Cslib.Computability.Languages.RegularLanguage`, this module defines union-free regular
expressions (`RegularExpression.IsUnionFree`) and union-free languages (`Language.IsUnionFree`),
proves that every regular expression and every regular language over a finite alphabet decomposes
into a finite sum of union-free languages via the Kleene algebra identity
`(L₁ + L₂)∗ = (L₁∗ * L₂∗)∗`, and establishes uniqueness of minimal-length words in union-free
languages (whence every finite union-free language is a subsingleton).

## Main definitions

* `CslibFrontier.Computability.Languages.RegularExpression.IsUnionFree`: regular expressions built
  without `+`.
* `CslibFrontier.Computability.Languages.Language.IsUnionFree`: languages denoted by a union-free
  regular expression.

## Main results

* `RegularExpression.exists_unionFree_list`,
  `Language.exists_unionFree_list_of_isRegular`: finite union-free decomposition of regular
  expressions and regular languages over finite alphabets.
* `RegularExpression.IsUnionFree.eq_of_min_length`,
  `Language.IsUnionFree.eq_of_min_length`,
  `Language.IsUnionFree.subsingleton_of_finite`: minimal-length word uniqueness and finiteness
  rigidity for union-free languages.
-/

public section

open scoped Computability

universe u

namespace CslibFrontier.Computability.Languages

namespace RegularExpression

variable {α : Type u}

/-- Syntactic predicate characterizing regular expressions containing no union (`+`) operator. -/
inductive IsUnionFree : _root_.RegularExpression α → Prop
  | zero : IsUnionFree 0
  | epsilon : IsUnionFree 1
  | char (a : α) : IsUnionFree (_root_.RegularExpression.char a)
  | comp {P Q : _root_.RegularExpression α} : IsUnionFree P → IsUnionFree Q → IsUnionFree (P * Q)
  | star {P : _root_.RegularExpression α} : IsUnionFree P → IsUnionFree P.star

private lemma mem_list_sum_iff {β : Type*} (Ls : List (_root_.Language β)) (w : List β) :
    w ∈ Ls.sum ↔ ∃ L ∈ Ls, w ∈ L := by
  induction Ls with
  | nil => simp [_root_.Language.notMem_zero]
  | cons L Ls ih =>
    simp only [List.sum_cons, _root_.Language.mem_add, List.mem_cons, ih]
    exact ⟨by rintro (hw | ⟨L', hL', hw⟩); exacts [⟨L, Or.inl rfl, hw⟩, ⟨L', Or.inr hL', hw⟩],
           by rintro ⟨L', rfl | hL', hw⟩; exacts [Or.inl hw, Or.inr ⟨L', hL', hw⟩]⟩

private lemma kstar_add_eq (L₁ L₂ : _root_.Language α) : (L₁ + L₂)∗ = (L₁∗ * L₂∗)∗ := by
  apply le_antisymm
  · apply kstar_mono
    refine sup_le ?_ ?_
    · calc L₁ = L₁ * 1 := (mul_one L₁).symm
        _ ≤ L₁∗ * 1 := mul_le_mul' le_kstar le_rfl
        _ ≤ L₁∗ * L₂∗ := mul_le_mul' le_rfl one_le_kstar
    · calc L₂ = 1 * L₂ := (one_mul L₂).symm
        _ ≤ 1 * L₂∗ := mul_le_mul' le_rfl le_kstar
        _ ≤ L₁∗ * L₂∗ := mul_le_mul' one_le_kstar le_rfl
  · have h1 : L₁∗ ≤ (L₁ + L₂)∗ := kstar_mono le_sup_left
    have h2 : L₂∗ ≤ (L₁ + L₂)∗ := kstar_mono le_sup_right
    calc (L₁∗ * L₂∗)∗ ≤ ((L₁ + L₂)∗ * (L₁ + L₂)∗)∗ :=
          kstar_mono (mul_le_mul' h1 h2)
      _ = ((L₁ + L₂)∗)∗ := by rw [kstar_mul_kstar]
      _ = (L₁ + L₂)∗ := kstar_idem _

private def ufStarOfList : List (_root_.RegularExpression α) → _root_.RegularExpression α
  | [] => 1
  | r :: rs => (r.star * ufStarOfList rs).star

private lemma isUnionFree_ufStarOfList {rs : List (_root_.RegularExpression α)}
    (hrs : ∀ r ∈ rs, IsUnionFree r) : IsUnionFree (ufStarOfList rs) := by
  induction rs with
  | nil => exact .epsilon
  | cons r rs ih =>
    refine .star (.comp (.star (hrs r List.mem_cons_self)) ?_)
    exact ih fun q hq ↦ hrs q (List.mem_cons_of_mem _ hq)

private lemma matches'_ufStarOfList (rs : List (_root_.RegularExpression α)) :
    (ufStarOfList rs).matches' = ((rs.map _root_.RegularExpression.matches').sum)∗ := by
  induction rs with
  | nil =>
    simp only [ufStarOfList, _root_.RegularExpression.matches'_epsilon, List.map_nil,
      List.sum_nil]
    ext w
    rw [_root_.Language.mem_one, _root_.Language.mem_kstar]
    constructor
    · rintro rfl; exact ⟨[], rfl, fun _ h ↦ by simp at h⟩
    · rintro ⟨S, rfl, hS⟩
      induction S with
      | nil => rfl
      | cons y _ _ =>
        exact absurd (hS y List.mem_cons_self) (_root_.Language.notMem_zero y)
  | cons r rs ih =>
    simp only [ufStarOfList, _root_.RegularExpression.matches'_star,
      _root_.RegularExpression.matches'_mul, List.map_cons, List.sum_cons]
    rw [ih, ← kstar_add_eq]

private def toUnionFreeList :
    _root_.RegularExpression α → List (_root_.RegularExpression α)
  | 0 => [0]
  | 1 => [1]
  | _root_.RegularExpression.char a => [_root_.RegularExpression.char a]
  | P + Q => toUnionFreeList P ++ toUnionFreeList Q
  | P * Q => (toUnionFreeList P).flatMap fun p ↦ (toUnionFreeList Q).map fun q ↦ p * q
  | _root_.RegularExpression.star P => [ufStarOfList (toUnionFreeList P)]

private lemma isUnionFree_mem_toUnionFreeList (r : _root_.RegularExpression α) :
    ∀ u ∈ toUnionFreeList r, IsUnionFree u := by
  induction r with
  | zero =>
    intro u hu; simp only [toUnionFreeList, List.mem_singleton] at hu; subst hu; exact .zero
  | epsilon =>
    intro u hu; simp only [toUnionFreeList, List.mem_singleton] at hu; subst hu; exact .epsilon
  | char a =>
    intro u hu; simp only [toUnionFreeList, List.mem_singleton] at hu; subst hu; exact .char a
  | plus P Q ihP ihQ =>
    intro u hu
    rcases List.mem_append.mp (by simpa [toUnionFreeList] using hu) with hP | hQ
    · exact ihP u hP
    · exact ihQ u hQ
  | comp P Q ihP ihQ =>
    intro u hu
    simp only [toUnionFreeList, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨p, hp, q, hq, rfl⟩ := hu
    exact .comp (ihP p hp) (ihQ q hq)
  | star P ihP =>
    intro u hu
    simp only [toUnionFreeList, List.mem_singleton] at hu
    subst hu
    exact isUnionFree_ufStarOfList ihP

private lemma matches'_toUnionFreeList (r : _root_.RegularExpression α) :
    ((toUnionFreeList r).map _root_.RegularExpression.matches').sum = r.matches' := by
  induction r with
  | zero => simp [toUnionFreeList]
  | epsilon => simp [toUnionFreeList]
  | char a => simp [toUnionFreeList]
  | plus P Q ihP ihQ =>
    simp only [toUnionFreeList, List.map_append, List.sum_append, ihP, ihQ]
    rfl
  | comp P Q ihP ihQ =>
    ext w
    simp only [toUnionFreeList, mem_list_sum_iff, List.mem_map, List.mem_flatMap]
    constructor
    · rintro ⟨L, ⟨u, ⟨p, hp, q, hq, rfl⟩, rfl⟩, hw⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := _root_.Language.mem_mul.mp hw
      have ha' : a ∈ ((toUnionFreeList P).map _root_.RegularExpression.matches').sum :=
        (mem_list_sum_iff _ a).mpr ⟨p.matches', List.mem_map.mpr ⟨p, hp, rfl⟩, ha⟩
      have hb' : b ∈ ((toUnionFreeList Q).map _root_.RegularExpression.matches').sum :=
        (mem_list_sum_iff _ b).mpr ⟨q.matches', List.mem_map.mpr ⟨q, hq, rfl⟩, hb⟩
      exact _root_.Language.append_mem_mul (ihP ▸ ha') (ihQ ▸ hb')
    · intro hw
      obtain ⟨a, ha, b, hb, rfl⟩ := _root_.Language.mem_mul.mp hw
      have ha' : a ∈ ((toUnionFreeList P).map _root_.RegularExpression.matches').sum :=
        ihP.symm ▸ ha
      have hb' : b ∈ ((toUnionFreeList Q).map _root_.RegularExpression.matches').sum :=
        ihQ.symm ▸ hb
      obtain ⟨La, hLa, ha''⟩ := (mem_list_sum_iff _ a).mp ha'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hLa
      obtain ⟨Lb, hLb, hb''⟩ := (mem_list_sum_iff _ b).mp hb'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hLb
      exact ⟨(p * q).matches', ⟨p * q, ⟨p, hp, q, hq, rfl⟩, rfl⟩,
        _root_.Language.append_mem_mul ha'' hb''⟩
  | star P ihP =>
    simp [toUnionFreeList, matches'_ufStarOfList, ihP]

/-- Every regular expression `r` splits as a finite sum of union-free regular expressions. -/
theorem exists_unionFree_list (r : _root_.RegularExpression α) :
    ∃ rs : List (_root_.RegularExpression α),
      (∀ u ∈ rs, IsUnionFree u) ∧
      ((rs.map _root_.RegularExpression.matches').sum = r.matches') :=
  ⟨toUnionFreeList r, isUnionFree_mem_toUnionFreeList r, matches'_toUnionFreeList r⟩

/-- Uniqueness of minimal-length words in `r.matches'` for any union-free regular expression `r`.
-/
theorem IsUnionFree.eq_of_min_length {r : _root_.RegularExpression α} (hr : IsUnionFree r)
    {u v : List α} (hu : u ∈ r.matches') (hv : v ∈ r.matches')
    (hmin_u : ∀ w ∈ r.matches', u.length ≤ w.length)
    (hmin_v : ∀ w ∈ r.matches', v.length ≤ w.length) : u = v := by
  induction hr generalizing u v with
  | zero => exact False.elim hu
  | epsilon =>
    change u = [] at hu; change v = [] at hv; exact hu.trans hv.symm
  | char a =>
    change u = [a] at hu; change v = [a] at hv; exact hu.trans hv.symm
  | @comp P Q _ _ ihP ihQ =>
    simp only [_root_.RegularExpression.matches'_mul] at hu hv hmin_u hmin_v
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := _root_.Language.mem_mul.mp hu
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := _root_.Language.mem_mul.mp hv
    have hu₁_min : ∀ p ∈ P.matches', u₁.length ≤ p.length := fun p hp ↦ by
      have hle := hmin_u (p ++ u₂) (_root_.Language.append_mem_mul hp hu₂)
      simp only [List.length_append] at hle; omega
    have hv₁_min : ∀ p ∈ P.matches', v₁.length ≤ p.length := fun p hp ↦ by
      have hle := hmin_v (p ++ v₂) (_root_.Language.append_mem_mul hp hv₂)
      simp only [List.length_append] at hle; omega
    have hu₂_min : ∀ q ∈ Q.matches', u₂.length ≤ q.length := fun q hq ↦ by
      have hle := hmin_u (u₁ ++ q) (_root_.Language.append_mem_mul hu₁ hq)
      simp only [List.length_append] at hle; omega
    have hv₂_min : ∀ q ∈ Q.matches', v₂.length ≤ q.length := fun q hq ↦ by
      have hle := hmin_v (v₁ ++ q) (_root_.Language.append_mem_mul hv₁ hq)
      simp only [List.length_append] at hle; omega
    rw [ihP hu₁ hv₁ hu₁_min hv₁_min, ihQ hu₂ hv₂ hu₂_min hv₂_min]
  | @star P _ _ =>
    simp only [_root_.RegularExpression.matches'_star] at hmin_u hmin_v
    have hu0 : u.length ≤ 0 := hmin_u [] (_root_.Language.nil_mem_kstar _)
    have hv0 : v.length ≤ 0 := hmin_v [] (_root_.Language.nil_mem_kstar _)
    rw [List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hu0),
      List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hv0)]

end RegularExpression

namespace Language

variable {α : Type u}

/-- A language is union-free if it is denoted by a union-free regular expression. -/
def IsUnionFree (L : _root_.Language α) : Prop :=
  ∃ r : _root_.RegularExpression α, RegularExpression.IsUnionFree r ∧ r.matches' = L

/-- Every union-free language is regular. -/
theorem IsUnionFree.isRegular {L : _root_.Language α} (h : IsUnionFree L) : L.IsRegular := by
  obtain ⟨r, _, rfl⟩ := h
  exact Cslib.Language.IsRegular.regex r

/-- Every regular language over a finite alphabet is a finite union (`List.sum`) of union-free
languages. -/
theorem exists_unionFree_list_of_isRegular [Finite α] {L : _root_.Language α}
    (hL : L.IsRegular) :
    ∃ Ls : List (_root_.Language α),
      (∀ S ∈ Ls, IsUnionFree S) ∧ L = Ls.sum := by
  obtain ⟨r, rfl⟩ := Cslib.Language.IsRegular.iff_regex.mp hL
  obtain ⟨rs, hrs, hsum⟩ := RegularExpression.exists_unionFree_list r
  refine ⟨rs.map _root_.RegularExpression.matches', ?_, hsum.symm⟩
  intro S hS
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hS
  exact ⟨u, hrs u hu, rfl⟩

/-- Any two words of minimal length in a union-free language are equal. -/
theorem IsUnionFree.eq_of_min_length {L : _root_.Language α} (hL : IsUnionFree L)
    {u v : List α} (hu : u ∈ L) (hv : v ∈ L)
    (hmin_u : ∀ w ∈ L, u.length ≤ w.length)
    (hmin_v : ∀ w ∈ L, v.length ≤ w.length) : u = v := by
  obtain ⟨r, hr, rfl⟩ := hL
  exact hr.eq_of_min_length hu hv hmin_u hmin_v

private def repeatWord (u : List α) : ℕ → List α
  | 0 => []
  | k + 1 => u ++ repeatWord u k

private lemma length_repeatWord (u : List α) (k : ℕ) :
    (repeatWord u k).length = k * u.length := by
  induction k with
  | zero => simp [repeatWord]
  | succ k ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

private lemma repeatWord_mem_kstar {L : _root_.Language α} {x : List α} (hx : x ∈ L)
    (k : ℕ) : repeatWord x k ∈ L∗ := by
  induction k with
  | zero => simpa [repeatWord] using _root_.Language.nil_mem_kstar L
  | succ k ih =>
    dsimp only [repeatWord]
    obtain ⟨S, hS_eq, hS⟩ := _root_.Language.mem_kstar.mp ih
    exact _root_.Language.mem_kstar.mpr ⟨x :: S, by simp [hS_eq], fun y hy ↦ by
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hx
      · exact hS y hy'⟩

/-- Every finite union-free language is a subsingleton (contains at most one word). -/
theorem IsUnionFree.subsingleton_of_finite {L : _root_.Language α} (hL : IsUnionFree L)
    (hfin : (L : Set (List α)).Finite) : (L : Set (List α)).Subsingleton := by
  obtain ⟨r, hr, rfl⟩ := hL
  induction hr with
  | zero => exact Set.subsingleton_empty
  | epsilon => exact Set.subsingleton_singleton
  | char a => exact Set.subsingleton_singleton
  | @comp P Q _ _ ihP ihQ =>
    simp only [_root_.RegularExpression.matches'_mul] at hfin ⊢
    intro u hu v hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := _root_.Language.mem_mul.mp hu
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := _root_.Language.mem_mul.mp hv
    have hPfin : (P.matches' : Set (List α)).Finite := by
      have hinj : Function.Injective (fun p : List α ↦ p ++ u₂) :=
        fun _ _ h ↦ List.append_cancel_right h
      exact Set.Finite.of_finite_image (f := fun p : List α ↦ p ++ u₂)
        (hfin.subset (by rintro _ ⟨p, hp, rfl⟩; exact _root_.Language.append_mem_mul hp hu₂))
        hinj.injOn
    have hQfin : (Q.matches' : Set (List α)).Finite := by
      have hinj : Function.Injective (fun q : List α ↦ u₁ ++ q) :=
        fun _ _ h ↦ List.append_cancel_left h
      exact Set.Finite.of_finite_image (f := fun q : List α ↦ u₁ ++ q)
        (hfin.subset (by rintro _ ⟨q, hq, rfl⟩; exact _root_.Language.append_mem_mul hu₁ hq))
        hinj.injOn
    rw [ihP hPfin hu₁ hv₁, ihQ hQfin hu₂ hv₂]
  | @star P _ _ =>
    simp only [_root_.RegularExpression.matches'_star] at hfin ⊢
    have hno_ne : ∀ x ∈ P.matches', x = [] := by
      intro x hx
      by_contra hne
      have hxlen : 1 ≤ x.length := List.length_pos_iff.mpr hne
      have hinj : Function.Injective (fun k : ℕ ↦ repeatWord x k) := fun m n hmn ↦ by
        have hlen := congrArg List.length hmn
        simp only [length_repeatWord] at hlen
        exact Nat.eq_of_mul_eq_mul_right hxlen hlen
      have hsub : Set.range (fun k : ℕ ↦ repeatWord x k) ⊆
          (((P.matches')∗ : _root_.Language α) : Set (List α)) := by
        rintro _ ⟨k, rfl⟩
        exact repeatWord_mem_kstar hx k
      exact Set.infinite_range_of_injective hinj (hfin.subset hsub)
    intro u hu v hv
    obtain ⟨Su, rfl, hSu⟩ := _root_.Language.mem_kstar.mp hu
    obtain ⟨Sv, rfl, hSv⟩ := _root_.Language.mem_kstar.mp hv
    have hflat : ∀ S : List (List α), (∀ y ∈ S, y ∈ P.matches') → S.flatten = [] := by
      intro S hS; induction S with
      | nil => rfl
      | cons y S ih =>
        rw [List.flatten_cons, hno_ne y (hS y List.mem_cons_self), List.nil_append]
        exact ih fun z hz ↦ hS z (List.mem_cons_of_mem _ hz)
    rw [hflat Su hSu, hflat Sv hSv]

end Language

end CslibFrontier.Computability.Languages
