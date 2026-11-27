/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

/-!
# Unique-Disjointness Rectangle Covering Lower Bound

This module formalizes the combinatorial rectangle covering lower bound for the
unique-disjointness problem on subsets of a finite ground set `α`, following the elementary
inductive proof of Kaibel and Weltge.

If `A, B : Finset (Finset α)` form a rectangle avoiding intersections of cardinality `1`
(i.e. `(a ∩ b).card ≠ 1` for all `a ∈ A` and `b ∈ B`), then `A ×ˢ B` contains at most
`2 ^ Fintype.card α` disjoint pairs `(a, b)`. Since the total number of disjoint pairs of subsets
of `α` is `3 ^ Fintype.card α`, any family of rectangles avoiding unit intersections that covers
all disjoint pairs must have size at least `(3 / 2) ^ Fintype.card α`.

## Main definitions

* `CslibFrontier.Computability.Communication.disjointPairs`: the finset of disjoint pairs `(a, b)`
  in `A ×ˢ B`.
* `CslibFrontier.Computability.Communication.AvoidsUnitIntersection`: the predicate asserting that
  no `a ∈ A` and `b ∈ B` intersect in a singleton (`(a ∩ b).card ≠ 1`).

## Main results

* `CslibFrontier.Computability.Communication.card_disjointPairs_le_two_pow`: Kaibel–Weltge upper
  bound `(disjointPairs A B).card ≤ 2 ^ Fintype.card α` for every rectangle avoiding unit
  intersections.
* `CslibFrontier.Computability.Communication.card_disjointPairs_univ`: there are exactly
  `3 ^ Fintype.card α` disjoint pairs of subsets of `α`.
* `CslibFrontier.Computability.Communication.three_pow_le_card_mul_two_pow_of_cover`: any cover of
  all disjoint pairs by rectangles avoiding unit intersections satisfies
  `3 ^ Fintype.card α ≤ I.card * 2 ^ Fintype.card α`.
-/

public section

open Finset

namespace CslibFrontier.Computability.Communication

section Core

variable {α : Type*} [DecidableEq α]

/-- The finset of disjoint pairs `(a, b) ∈ A ×ˢ B`. -/
def disjointPairs (A B : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (A ×ˢ B).filter fun p ↦ Disjoint p.1 p.2

/-- A rectangle `A × B` avoids unit intersections if no `a ∈ A` and `b ∈ B` satisfy
`(a ∩ b).card = 1`. -/
@[expose] def AvoidsUnitIntersection (A B : Finset (Finset α)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, (a ∩ b).card ≠ 1

lemma mem_disjointPairs {A B : Finset (Finset α)} {p : Finset α × Finset α} :
    p ∈ disjointPairs A B ↔ p.1 ∈ A ∧ p.2 ∈ B ∧ Disjoint p.1 p.2 := by
  simp [disjointPairs, and_assoc]

lemma disjointPairs_union_right (A B₁ B₂ : Finset (Finset α)) :
    disjointPairs A (B₁ ∪ B₂) = disjointPairs A B₁ ∪ disjointPairs A B₂ := by
  ext p
  simp only [mem_disjointPairs, mem_union]
  tauto

lemma disjointPairs_inter_right (A B₁ B₂ : Finset (Finset α)) :
    disjointPairs A (B₁ ∩ B₂) = disjointPairs A B₁ ∩ disjointPairs A B₂ := by
  ext p
  simp only [mem_disjointPairs, mem_inter]
  tauto

lemma disjointPairs_union_left (A₁ A₂ B : Finset (Finset α)) :
    disjointPairs (A₁ ∪ A₂) B = disjointPairs A₁ B ∪ disjointPairs A₂ B := by
  ext p
  simp only [mem_disjointPairs, mem_union]
  tauto

lemma disjointPairs_inter_left (A₁ A₂ B : Finset (Finset α)) :
    disjointPairs (A₁ ∩ A₂) B = disjointPairs A₁ B ∩ disjointPairs A₂ B := by
  ext p
  simp only [mem_disjointPairs, mem_inter]
  tauto

lemma disjointPairs_mono {A₁ A₂ B₁ B₂ : Finset (Finset α)} (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    disjointPairs A₁ B₁ ⊆ disjointPairs A₂ B₂ := by
  intro p hp
  rw [mem_disjointPairs] at hp ⊢
  exact ⟨hA hp.1, hB hp.2.1, hp.2.2⟩

lemma card_disjointPairs_add_inter_right (A B₁ B₂ : Finset (Finset α)) :
    (disjointPairs A B₁).card + (disjointPairs A B₂).card =
      (disjointPairs A (B₁ ∪ B₂)).card + (disjointPairs A (B₁ ∩ B₂)).card := by
  rw [disjointPairs_union_right, disjointPairs_inter_right, card_union_add_card_inter]

lemma card_disjointPairs_add_inter_left (A₁ A₂ B : Finset (Finset α)) :
    (disjointPairs A₁ B).card + (disjointPairs A₂ B).card =
      (disjointPairs (A₁ ∪ A₂) B).card + (disjointPairs (A₁ ∩ A₂) B).card := by
  rw [disjointPairs_union_left, disjointPairs_inter_left, card_union_add_card_inter]

lemma avoidsUnitIntersection_union_right {A B₁ B₂ : Finset (Finset α)}
    (h₁ : AvoidsUnitIntersection A B₁) (h₂ : AvoidsUnitIntersection A B₂) :
    AvoidsUnitIntersection A (B₁ ∪ B₂) := by
  intro a ha b hb
  rcases mem_union.mp hb with hb₁ | hb₂
  · exact h₁ a ha b hb₁
  · exact h₂ a ha b hb₂

lemma avoidsUnitIntersection_union_left {A₁ A₂ B : Finset (Finset α)}
    (h₁ : AvoidsUnitIntersection A₁ B) (h₂ : AvoidsUnitIntersection A₂ B) :
    AvoidsUnitIntersection (A₁ ∪ A₂) B := by
  intro a ha b hb
  rcases mem_union.mp ha with ha₁ | ha₂
  · exact h₁ a ha₁ b hb
  · exact h₂ a ha₂ b hb

end Core

private def dropLastFinset {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n ↦ i.castSucc ∈ s

private lemma mem_dropLastFinset {n : ℕ} {s : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ dropLastFinset s ↔ i.castSucc ∈ s := by
  simp [dropLastFinset]

private lemma dropLastFinset_inter {n : ℕ} (s t : Finset (Fin (n + 1))) :
    dropLastFinset (s ∩ t) = dropLastFinset s ∩ dropLastFinset t := by
  ext i
  simp [mem_dropLastFinset]

private lemma card_inter_eq_of_last_not_mem {n : ℕ} {s t : Finset (Fin (n + 1))}
    (h : ¬ (Fin.last n ∈ s ∧ Fin.last n ∈ t)) :
    (s ∩ t).card = (dropLastFinset s ∩ dropLastFinset t).card := by
  rw [← dropLastFinset_inter]
  refine (Finset.card_bij (fun (i : Fin n) _ ↦ i.castSucc) ?_ ?_ ?_).symm
  · intro i hi
    exact mem_dropLastFinset.mp hi
  · intro i _ j _ hij
    exact Fin.castSucc_injective n hij
  · intro x hx
    refine ⟨x.castPred (fun hlast ↦ h ?_), ?_, Fin.castSucc_castPred x _⟩
    · subst hlast
      exact mem_inter.mp hx
    · rw [mem_dropLastFinset, Fin.castSucc_castPred]
      exact hx

private lemma card_inter_eq_succ_of_last_mem {n : ℕ} {s t : Finset (Fin (n + 1))}
    (hs : Fin.last n ∈ s) (ht : Fin.last n ∈ t) :
    (s ∩ t).card = (dropLastFinset s ∩ dropLastFinset t).card + 1 := by
  have hmem : Fin.last n ∈ s ∩ t := mem_inter.mpr ⟨hs, ht⟩
  rw [← Finset.card_erase_add_one hmem, ← dropLastFinset_inter]
  congr 1
  refine (Finset.card_bij (fun (i : Fin n) _ ↦ i.castSucc) ?_ ?_ ?_).symm
  · intro i hi
    exact mem_erase.mpr ⟨Fin.castSucc_ne_last i, mem_dropLastFinset.mp hi⟩
  · intro i _ j _ hij
    exact Fin.castSucc_injective n hij
  · intro x hx
    rcases mem_erase.mp hx with ⟨hne, hxt⟩
    exact ⟨x.castPred hne, by rw [mem_dropLastFinset, Fin.castSucc_castPred]; exact hxt,
      Fin.castSucc_castPred x hne⟩

private lemma disjoint_iff_dropLast {n : ℕ} {s t : Finset (Fin (n + 1))} :
    Disjoint s t ↔
      Disjoint (dropLastFinset s) (dropLastFinset t) ∧ ¬ (Fin.last n ∈ s ∧ Fin.last n ∈ t) := by
  constructor
  · intro h
    refine ⟨?_, fun ⟨hs, ht⟩ ↦ Finset.disjoint_left.mp h hs ht⟩
    rw [Finset.disjoint_left]
    intro i his hit
    exact Finset.disjoint_left.mp h (mem_dropLastFinset.mp his) (mem_dropLastFinset.mp hit)
  · rintro ⟨hd, hlast⟩
    rw [Finset.disjoint_left]
    intro x hxs hxt
    by_cases hx : x = Fin.last n
    · subst hx; exact hlast ⟨hxs, hxt⟩
    · have hxs' : x.castPred hx ∈ dropLastFinset s := by
        rw [mem_dropLastFinset, Fin.castSucc_castPred]; exact hxs
      have hxt' : x.castPred hx ∈ dropLastFinset t := by
        rw [mem_dropLastFinset, Fin.castSucc_castPred]; exact hxt
      exact Finset.disjoint_left.mp hd hxs' hxt'

private lemma dropLastFinset_injOn_not_mem {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    (hS : ∀ s ∈ S, Fin.last n ∉ s) :
    Set.InjOn dropLastFinset (S : Set (Finset (Fin (n + 1)))) := by
  intro s hs t ht hst
  ext x
  by_cases hx : x = Fin.last n
  · subst hx; simp [hS s hs, hS t ht]
  · have := Finset.ext_iff.mp hst (x.castPred hx)
    simpa [mem_dropLastFinset, Fin.castSucc_castPred] using this

private lemma dropLastFinset_injOn_mem {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    (hS : ∀ s ∈ S, Fin.last n ∈ s) :
    Set.InjOn dropLastFinset (S : Set (Finset (Fin (n + 1)))) := by
  intro s hs t ht hst
  ext x
  by_cases hx : x = Fin.last n
  · subst hx; simp [hS s hs, hS t ht]
  · have := Finset.ext_iff.mp hst (x.castPred hx)
    simpa [mem_dropLastFinset, Fin.castSucc_castPred] using this

private lemma card_disjointPairs_fin_le_two_pow :
    ∀ (n : ℕ) (A B : Finset (Finset (Fin n))),
      AvoidsUnitIntersection A B → (disjointPairs A B).card ≤ 2 ^ n
  | 0, A, B, _ => by
      have hsub : disjointPairs A B ⊆ ({(∅, ∅)} : Finset (Finset (Fin 0) × Finset (Fin 0))) := by
        rintro ⟨a, b⟩ _
        simp [Subsingleton.elim a ∅, Subsingleton.elim b ∅]
      calc (disjointPairs A B).card
          ≤ ({(∅, ∅)} : Finset (Finset (Fin 0) × Finset (Fin 0))).card := card_le_card hsub
        _ = 1 := by simp
        _ = 2 ^ 0 := by norm_num
  | n + 1, A, B, havoid => by
      let A0_raw := A.filter (fun s ↦ Fin.last n ∉ s)
      let A1_raw := A.filter (fun s ↦ Fin.last n ∈ s)
      let B0_raw := B.filter (fun s ↦ Fin.last n ∉ s)
      let B1_raw := B.filter (fun s ↦ Fin.last n ∈ s)
      let A0 := A0_raw.image dropLastFinset
      let A1 := A1_raw.image dropLastFinset
      let B0 := B0_raw.image dropLastFinset
      let B1 := B1_raw.image dropLastFinset
      have hA0_inj : Set.InjOn dropLastFinset (A0_raw : Set (Finset (Fin (n + 1)))) :=
        dropLastFinset_injOn_not_mem (S := A0_raw) (fun s hs ↦ (mem_filter.mp hs).2)
      have hA1_inj : Set.InjOn dropLastFinset (A1_raw : Set (Finset (Fin (n + 1)))) :=
        dropLastFinset_injOn_mem (S := A1_raw) (fun s hs ↦ (mem_filter.mp hs).2)
      have hB0_inj : Set.InjOn dropLastFinset (B0_raw : Set (Finset (Fin (n + 1)))) :=
        dropLastFinset_injOn_not_mem (S := B0_raw) (fun s hs ↦ (mem_filter.mp hs).2)
      have hB1_inj : Set.InjOn dropLastFinset (B1_raw : Set (Finset (Fin (n + 1)))) :=
        dropLastFinset_injOn_mem (S := B1_raw) (fun s hs ↦ (mem_filter.mp hs).2)
      have hD11 : disjointPairs A1 B1 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro ⟨a, b⟩ hab
        rw [mem_disjointPairs] at hab
        rcases mem_image.mp hab.1 with ⟨a', ha', rfl⟩
        rcases mem_image.mp hab.2.1 with ⟨b', hb', rfl⟩
        have ha'm := (mem_filter.mp ha').1
        have ha'l := (mem_filter.mp ha').2
        have hb'm := (mem_filter.mp hb').1
        have hb'l := (mem_filter.mp hb').2
        have hcard := card_inter_eq_succ_of_last_mem ha'l hb'l
        have hzero : (dropLastFinset a' ∩ dropLastFinset b').card = 0 :=
          Finset.card_eq_zero.mpr (Finset.disjoint_iff_inter_eq_empty.mp hab.2.2)
        rw [hzero, zero_add] at hcard
        exact havoid a' ha'm b' hb'm hcard
      have h_av_00 : AvoidsUnitIntersection A0 B0 := by
        intro a ha b hb
        rcases mem_image.mp ha with ⟨a', ha', rfl⟩
        rcases mem_image.mp hb with ⟨b', hb', rfl⟩
        have hcard := card_inter_eq_of_last_not_mem (s := a') (t := b')
          (fun h ↦ (mem_filter.mp ha').2 h.1)
        rw [← hcard]
        exact havoid a' (mem_filter.mp ha').1 b' (mem_filter.mp hb').1
      have h_av_01 : AvoidsUnitIntersection A0 B1 := by
        intro a ha b hb
        rcases mem_image.mp ha with ⟨a', ha', rfl⟩
        rcases mem_image.mp hb with ⟨b', hb', rfl⟩
        have hcard := card_inter_eq_of_last_not_mem (s := a') (t := b')
          (fun h ↦ (mem_filter.mp ha').2 h.1)
        rw [← hcard]
        exact havoid a' (mem_filter.mp ha').1 b' (mem_filter.mp hb').1
      have h_av_10 : AvoidsUnitIntersection A1 B0 := by
        intro a ha b hb
        rcases mem_image.mp ha with ⟨a', ha', rfl⟩
        rcases mem_image.mp hb with ⟨b', hb', rfl⟩
        have hcard := card_inter_eq_of_last_not_mem (s := a') (t := b')
          (fun h ↦ (mem_filter.mp hb').2 h.2)
        rw [← hcard]
        exact havoid a' (mem_filter.mp ha').1 b' (mem_filter.mp hb').1
      have h_ih_right : (disjointPairs A0 (B0 ∪ B1)).card ≤ 2 ^ n :=
        card_disjointPairs_fin_le_two_pow n A0 (B0 ∪ B1)
          (avoidsUnitIntersection_union_right h_av_00 h_av_01)
      have h_ih_left : (disjointPairs (A0 ∪ A1) B0).card ≤ 2 ^ n :=
        card_disjointPairs_fin_le_two_pow n (A0 ∪ A1) B0
          (avoidsUnitIntersection_union_left h_av_00 h_av_10)
      have h_disj_inter :
          Disjoint (disjointPairs A0 (B0 ∩ B1)) (disjointPairs (A0 ∩ A1) B0) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rw [mem_disjointPairs] at hp1 hp2
        have hmem : p ∈ disjointPairs A1 B1 :=
          mem_disjointPairs.mpr ⟨(mem_inter.mp hp2.1).2, (mem_inter.mp hp1.2.1).2, hp1.2.2⟩
        rw [hD11] at hmem
        exact Finset.notMem_empty p hmem
      have h_inter_le :
          (disjointPairs A0 (B0 ∩ B1)).card + (disjointPairs (A0 ∩ A1) B0).card ≤
            (disjointPairs A0 B0).card := by
        rw [← Finset.card_union_of_disjoint h_disj_inter]
        refine card_le_card (Finset.union_subset ?_ ?_)
        · exact disjointPairs_mono Subset.rfl inter_subset_left
        · exact disjointPairs_mono inter_subset_left Subset.rfl
      have h_split_card : ∀ (X Y : Finset (Finset (Fin (n + 1))))
          (hX : ∀ s ∈ X, Fin.last n ∉ s ∨ ∀ s' ∈ X, Fin.last n ∈ s')
          (hXinj : Set.InjOn dropLastFinset (X : Set (Finset (Fin (n + 1)))))
          (hYinj : Set.InjOn dropLastFinset (Y : Set (Finset (Fin (n + 1)))))
          (hlast : ∀ a ∈ X, ∀ b ∈ Y, ¬ (Fin.last n ∈ a ∧ Fin.last n ∈ b)),
          (disjointPairs X Y).card =
            (disjointPairs (X.image dropLastFinset) (Y.image dropLastFinset)).card := by
        intro X Y _ hXinj hYinj hlast
        refine Finset.card_bij (fun p _ ↦ (dropLastFinset p.1, dropLastFinset p.2)) ?_ ?_ ?_
        · intro p hp
          rw [mem_disjointPairs] at hp ⊢
          exact ⟨mem_image_of_mem _ hp.1, mem_image_of_mem _ hp.2.1,
            (disjoint_iff_dropLast.mp hp.2.2).1⟩
        · intro p hp q hq hpq
          rw [mem_disjointPairs] at hp hq
          have h1 := hXinj hp.1 hq.1 (Prod.mk.inj hpq).1
          have h2 := hYinj hp.2.1 hq.2.1 (Prod.mk.inj hpq).2
          exact Prod.ext h1 h2
        · rintro ⟨a, b⟩ hab
          rw [mem_disjointPairs] at hab
          rcases mem_image.mp hab.1 with ⟨a', ha', rfl⟩
          rcases mem_image.mp hab.2.1 with ⟨b', hb', rfl⟩
          exact ⟨(a', b'), mem_disjointPairs.mpr
            ⟨ha', hb', disjoint_iff_dropLast.mpr ⟨hab.2.2, hlast a' ha' b' hb'⟩⟩, rfl⟩
      have hD_eq : (disjointPairs A B).card =
          (disjointPairs A0 B0).card + (disjointPairs A0 B1).card +
            (disjointPairs A1 B0).card := by
        have h_partA : A0_raw ∪ A1_raw = A := by
          ext s; simp only [A0_raw, A1_raw, mem_union, mem_filter]; tauto
        have h_partB : B0_raw ∪ B1_raw = B := by
          ext s; simp only [B0_raw, B1_raw, mem_union, mem_filter]; tauto
        have h_disjA : Disjoint A0_raw A1_raw := by
          rw [Finset.disjoint_left]
          intro s hs0 hs1
          exact (mem_filter.mp hs0).2 (mem_filter.mp hs1).2
        have h_disjB : Disjoint B0_raw B1_raw := by
          rw [Finset.disjoint_left]
          intro s hs0 hs1
          exact (mem_filter.mp hs0).2 (mem_filter.mp hs1).2
        have hD11_raw : disjointPairs A1_raw B1_raw = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          rintro ⟨a, b⟩ hab
          rw [mem_disjointPairs] at hab
          exact Finset.disjoint_left.mp hab.2.2 (mem_filter.mp hab.1).2 (mem_filter.mp hab.2.1).2
        have hdecomp : disjointPairs A B =
            disjointPairs A0_raw B0_raw ∪ disjointPairs A0_raw B1_raw ∪
              disjointPairs A1_raw B0_raw := by
          rw [← h_partA, ← h_partB, disjointPairs_union_left, disjointPairs_union_right,
            disjointPairs_union_right, hD11_raw, union_empty, union_assoc]
        have hd1 : Disjoint (disjointPairs A0_raw B0_raw) (disjointPairs A0_raw B1_raw) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          rw [mem_disjointPairs] at hp1 hp2
          exact Finset.disjoint_left.mp h_disjB hp1.2.1 hp2.2.1
        have hd2 : Disjoint (disjointPairs A0_raw B0_raw ∪ disjointPairs A0_raw B1_raw)
            (disjointPairs A1_raw B0_raw) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          rw [mem_disjointPairs] at hp2
          rcases mem_union.mp hp1 with hp | hp <;>
            exact Finset.disjoint_left.mp h_disjA (mem_disjointPairs.mp hp).1 hp2.1
        rw [hdecomp, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
        have c00 := h_split_card A0_raw B0_raw (fun s hs ↦ Or.inl (mem_filter.mp hs).2)
          hA0_inj hB0_inj (fun a ha _ _ h ↦ (mem_filter.mp ha).2 h.1)
        have c01 := h_split_card A0_raw B1_raw (fun s hs ↦ Or.inl (mem_filter.mp hs).2)
          hA0_inj hB1_inj (fun a ha _ _ h ↦ (mem_filter.mp ha).2 h.1)
        have c10 := h_split_card A1_raw B0_raw (fun _ _ ↦ Or.inr (fun s hs ↦ (mem_filter.mp hs).2))
          hA1_inj hB0_inj (fun _ _ b hb h ↦ (mem_filter.mp hb).2 h.2)
        rw [c00, c01, c10]
      have h1 := card_disjointPairs_add_inter_right A0 B0 B1
      have h2 := card_disjointPairs_add_inter_left A0 A1 B0
      rw [hD_eq]
      have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega

/-- **Kaibel–Weltge Rectangle Bound**: every rectangle `A × B` of subsets of `α` avoiding unit
intersections (`(a ∩ b).card ≠ 1`) contains at most `2 ^ Fintype.card α` disjoint pairs. -/
theorem card_disjointPairs_le_two_pow {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset (Finset α)} (h : AvoidsUnitIntersection A B) :
    (disjointPairs A B).card ≤ 2 ^ Fintype.card α := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let mapS : Finset α → Finset (Fin (Fintype.card α)) := fun s ↦ s.map e.toEmbedding
  have hmap_inj : Function.Injective mapS := fun s t hst ↦ by
    ext x
    have := Finset.ext_iff.mp hst (e x)
    simpa [mapS] using this
  have hmap_card : ∀ s t : Finset α, (mapS s ∩ mapS t).card = (s ∩ t).card := by
    intro s t
    have hmap_inter : mapS (s ∩ t) = mapS s ∩ mapS t := by
      ext y
      simp only [mapS, mem_inter, mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
      · rintro ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
        have hEq : x = x' := e.injective hxx'.symm
        subst hEq
        exact ⟨x, ⟨hx, hx'⟩, rfl⟩
    rw [← hmap_inter, Finset.card_map]
  have hmap_disj : ∀ s t : Finset α, Disjoint (mapS s) (mapS t) ↔ Disjoint s t := by
    intro s t
    simp [mapS, Finset.disjoint_map]
  let A' : Finset (Finset (Fin (Fintype.card α))) := A.image mapS
  let B' : Finset (Finset (Fin (Fintype.card α))) := B.image mapS
  have havoid' : AvoidsUnitIntersection A' B' := by
    intro a' ha' b' hb'
    rcases mem_image.mp ha' with ⟨a, ha, rfl⟩
    rcases mem_image.mp hb' with ⟨b, hb, rfl⟩
    rw [hmap_card]
    exact h a ha b hb
  have hcard_eq : (disjointPairs A B).card = (disjointPairs A' B').card := by
    refine Finset.card_bij (fun p _ ↦ (mapS p.1, mapS p.2)) ?_ ?_ ?_
    · intro p hp
      rw [mem_disjointPairs] at hp ⊢
      exact ⟨mem_image_of_mem _ hp.1, mem_image_of_mem _ hp.2.1, (hmap_disj _ _).mpr hp.2.2⟩
    · intro p _ q _ hpq
      exact Prod.ext (hmap_inj (Prod.mk.inj hpq).1) (hmap_inj (Prod.mk.inj hpq).2)
    · rintro ⟨a', b'⟩ hab
      rw [mem_disjointPairs] at hab
      rcases mem_image.mp hab.1 with ⟨a, ha, rfl⟩
      rcases mem_image.mp hab.2.1 with ⟨b, hb, rfl⟩
      exact ⟨(a, b), mem_disjointPairs.mpr ⟨ha, hb, (hmap_disj _ _).mp hab.2.2⟩, rfl⟩
  rw [hcard_eq]
  exact card_disjointPairs_fin_le_two_pow (Fintype.card α) A' B' havoid'

/-- The total number of disjoint pairs of subsets of a finite type `α` is `3 ^ Fintype.card α`. -/
theorem card_disjointPairs_univ {α : Type*} [Fintype α] [DecidableEq α] :
    (disjointPairs (Finset.univ : Finset (Finset α)) Finset.univ).card = 3 ^ Fintype.card α := by
  let enc : Finset α × Finset α → (α → Fin 3) := fun p x ↦
    if x ∈ p.1 then 0 else if x ∈ p.2 then 1 else 2
  have hcard : (disjointPairs (Finset.univ : Finset (Finset α)) Finset.univ).card =
      (Finset.univ : Finset (α → Fin 3)).card := by
    refine Finset.card_bij (fun p _ ↦ enc p) ?_ ?_ ?_
    · intro _ _; exact mem_univ _
    · intro p hp q hq hpq
      rw [mem_disjointPairs] at hp hq
      ext x
      · have hx := congr_fun hpq x
        simp only [enc] at hx
        by_cases h1 : x ∈ p.1 <;> by_cases h2 : x ∈ q.1
        · simp [h1, h2]
        · exfalso
          simp only [h1, ↓reduceIte, h2] at hx
          split_ifs at hx <;> simp at hx
        · exfalso
          simp only [h1, ↓reduceIte, h2] at hx
          split_ifs at hx <;> simp at hx
        · simp [h1, h2]
      · have hx := congr_fun hpq x
        have hp_not : ∀ h : x ∈ p.2, x ∉ p.1 := fun h h' ↦ Finset.disjoint_left.mp hp.2.2 h' h
        have hq_not : ∀ h : x ∈ q.2, x ∉ q.1 := fun h h' ↦ Finset.disjoint_left.mp hq.2.2 h' h
        simp only [enc] at hx
        by_cases h1 : x ∈ p.2 <;> by_cases h2 : x ∈ q.2
        · simp [h1, h2]
        · exfalso
          have hp1 : x ∉ p.1 := hp_not h1
          simp only [hp1, ↓reduceIte, h1, h2] at hx
          split_ifs at hx <;> simp at hx
        · exfalso
          have hq1 : x ∉ q.1 := hq_not h2
          simp only [hq1, ↓reduceIte, h1, h2] at hx
          split_ifs at hx <;> simp at hx
        · simp [h1, h2]
    · intro f _
      let a : Finset α := Finset.univ.filter fun x ↦ f x = 0
      let b : Finset α := Finset.univ.filter fun x ↦ f x = 1
      refine ⟨(a, b), mem_disjointPairs.mpr ⟨mem_univ _, mem_univ _, ?_⟩, ?_⟩
      · rw [Finset.disjoint_left]
        intro x hxa hxb
        have h0 := (mem_filter.mp hxa).2
        have h1 := (mem_filter.mp hxb).2
        omega
      · funext x
        simp only [enc, a, b, mem_filter, mem_univ, true_and]
        have hfx : f x = 0 ∨ f x = 1 ∨ f x = 2 := by
          rcases f x with ⟨v, hv⟩
          match v, hv with
          | 0, _ => exact Or.inl rfl
          | 1, _ => exact Or.inr (Or.inl rfl)
          | 2, _ => exact Or.inr (Or.inr rfl)
        rcases hfx with h | h | h <;> simp [h]
  rw [hcard, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- Any family of rectangles avoiding unit intersections that covers all disjoint pairs of subsets
of `α` has cardinality satisfying `3 ^ Fintype.card α ≤ I.card * 2 ^ Fintype.card α`. -/
theorem three_pow_le_card_mul_two_pow_of_cover {α ι : Type*} [Fintype α] [DecidableEq α]
    {I : Finset ι} {A B : ι → Finset (Finset α)}
    (havoid : ∀ i ∈ I, AvoidsUnitIntersection (A i) (B i))
    (hcover : ∀ a b : Finset α, Disjoint a b → ∃ i ∈ I, a ∈ A i ∧ b ∈ B i) :
    3 ^ Fintype.card α ≤ I.card * 2 ^ Fintype.card α := by
  have hsub : disjointPairs (Finset.univ : Finset (Finset α)) Finset.univ ⊆
      I.biUnion fun i ↦ disjointPairs (A i) (B i) := by
    intro p hp
    rw [mem_disjointPairs] at hp
    rcases hcover p.1 p.2 hp.2.2 with ⟨i, hi, ha, hb⟩
    exact mem_biUnion.mpr ⟨i, hi, mem_disjointPairs.mpr ⟨ha, hb, hp.2.2⟩⟩
  calc 3 ^ Fintype.card α
      = (disjointPairs (Finset.univ : Finset (Finset α)) Finset.univ).card :=
        card_disjointPairs_univ.symm
    _ ≤ (I.biUnion fun i ↦ disjointPairs (A i) (B i)).card := card_le_card hsub
    _ ≤ ∑ i ∈ I, (disjointPairs (A i) (B i)).card := card_biUnion_le
    _ ≤ ∑ _i ∈ I, 2 ^ Fintype.card α :=
        Finset.sum_le_sum fun i hi ↦ card_disjointPairs_le_two_pow (havoid i hi)
    _ = I.card * 2 ^ Fintype.card α := by simp

end CslibFrontier.Computability.Communication
