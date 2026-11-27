/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.WordUnavoidability.ReductionBasic

import Mathlib.Data.List.Nodup

/-!
# Block-Pair Inversion Lemmas and Duplicate-Free Separator Base Cases

This module proves targeted left- and right-component inversion lemmas for `GadgetBlockPair`
across
all blocks of `clauseGadgetBlocks φ`, together with the base-case lemma
`isUnavoidable_deleteLetters_of_contains_nonSep` showing that once all non-separator letters have
been deleted, the remaining duplicate-free separator skeleton is unavoidable.
-/

public section

namespace CslibFrontier.Complexity

open CslibFrontier.Word Cslib.Logic.PL

section BlockClassification

theorem lit_var_mem_distinctVars {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3)
    {j : ℕ} (hj : j < φ.length) (k : Fin 3) :
    (clauseLitAt φ[j] k).1 ∈ φ.distinctVars := by
  have hcl : φ[j] ∈ φ := List.getElem_mem hj
  have hlen : φ[j].length = 3 := h3 φ[j] hcl
  have heq := clauseLitAt_eq_getElem hlen k
  have hmem : clauseLitAt φ[j] k ∈ φ[j] := heq ▸ List.getElem_mem (by omega)
  exact CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr ⟨φ[j], hcl, (clauseLitAt φ[j] k).2, hmem⟩)

theorem GadgetBlockPair.not_mem_left {φ : CNF ℕ} {B : Set ClauseGadgetLetter}
    {x y : ClauseGadgetLetter} (h : GadgetBlockPair φ B x y) : x ∉ B := by
  rcases h with ⟨_, _, blk, _, hxy⟩
  exact (mem_deleteLetters.mp (hxy.subset (List.mem_cons_self ..))).2

theorem GadgetBlockPair.not_mem_right {φ : CNF ℕ} {B : Set ClauseGadgetLetter}
    {x y : ClauseGadgetLetter} (h : GadgetBlockPair φ B x y) : y ∉ B := by
  rcases h with ⟨_, _, blk, _, hxy⟩
  exact (mem_deleteLetters.mp (hxy.subset (by simp))).2

/-- Contiguous `2`-factor pairs contributed by the `2`-letter blocks of `origClauseBlocks j`. -/
@[expose]
def OrigPair2 (j : ℕ) (x y : ClauseGadgetLetter) : Prop :=
  (x = .ao j ∧ y = .orig j 0) ∨ (x = .bo j ∧ y = .orig j 0) ∨
  (x = .bo j ∧ y = .orig j 1) ∨ (x = .co j ∧ y = .orig j 1) ∨
  (x = .co j ∧ y = .orig j 2) ∨ (x = .do_ j ∧ y = .orig j 2) ∨
  (x = .do_ j ∧ y = .ao j) ∨ (x = .ao j ∧ y = .bo j) ∨
  (x = .ao j ∧ y = .co j) ∨ (x = .ao j ∧ y = .do_ j)

/-- Contiguous `2`-factor pairs contributed by the `2`-letter blocks of `varPosBlocks v`. -/
@[expose]
def VarPair2 (v : ℕ) (x y : ClauseGadgetLetter) : Prop :=
  (x = .ap v ∧ y = .px v) ∨ (x = .bp v ∧ y = .px v) ∨
  (x = .bp v ∧ y = .py v) ∨ (x = .cp v ∧ y = .py v) ∨
  (x = .cp v ∧ y = .ap v) ∨ (x = .ap v ∧ y = .bp v) ∨
  (x = .ap v ∧ y = .cp v)

/-- Contiguous `2`-factor pairs contributed by the `2`-letter blocks of `occTapBlocks j k lit`. -/
@[expose]
def TapPair2 (j : ℕ) (k : Fin 3) (lit : Literal ℕ) (x y : ClauseGadgetLetter) : Prop :=
  (x = .an j k ∧ y = .bn j k) ∨ (x = .qo j k ∧ y = .bn j k) ∨
  (x = .qo j k ∧ y = .cn j k) ∨ (x = .qv j k ∧ y = .cn j k) ∨
  (x = .qv j k ∧ y = .an j k) ∨ (x = .bn j k ∧ y = .an j k) ∨
  (x = .cn j k ∧ y = .an j k) ∨ (x = .ao j ∧ y = .go j k) ∨
  (x = .go j k ∧ y = .an j k) ∨ (x = .ap lit.1 ∧ y = .gv j k) ∨
  (x = .gv j k ∧ y = .an j k)

theorem gadgetBlockPair_decomp {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B x y) :
    x ∉ B ∧ y ∉ B ∧ (
      (∃ j < φ.length, OrigPair2 j x y) ∨
      (∃ v ∈ φ.distinctVars, VarPair2 v x y) ∨
      (∃ (j : ℕ) (hj : j < φ.length) (k : Fin 3), TapPair2 j k (clauseLitAt φ[j] k) x y) ∨
      (∃ j < φ.length, ∃ k : Fin 3,
        [x, y] <:+: deleteLetters B [.go j k, .orig j k, .qo j k, .go j k]) ∨
      (∃ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
        [x, y] <:+: deleteLetters B
          [.gv j k, conflictVarSlot (clauseLitAt φ[j] k), .qv j k, .gv j k])) := by
  refine ⟨h.not_mem_left, h.not_mem_right, ?_⟩
  rcases h with ⟨_, _, blk, hblk, hxy⟩
  rcases mem_clauseGadgetBlocks_iff.mp hblk with ⟨j, hj, ho⟩ | ⟨v, hv, hvp⟩ | ⟨j, hj, k, ht⟩
  · left
    refine ⟨j, hj, ?_⟩
    rw [mem_origClauseBlocks_iff] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      { obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy; simp [OrigPair2] }
  · right; left
    refine ⟨v, hv, ?_⟩
    rw [mem_varPosBlocks_iff] at hvp
    rcases hvp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      { obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy; simp [VarPair2] }
  · rw [mem_occTapBlocks_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, k, hxy⟩)))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, k, hxy⟩)))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))
    · obtain ⟨rfl, rfl, _, _⟩ := infix_pair_two_gadget.mp hxy
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, by simp [TapPair2]⟩))

theorem left_orig {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {k : Fin 3}
    {y : ClauseGadgetLetter} (h : GadgetBlockPair φ B (.orig j k) y) :
    j < φ.length ∧ ((y = .qo j k ∧ .qo j k ∉ B) ∨ (y = .go j k ∧ .qo j k ∈ B)) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v, _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', hj', k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨h1, rfl, _, hq⟩ | ⟨_, h1 | h2 | h3 | h4 | h5⟩
    · injection h1 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl ⟨rfl, hq⟩⟩
    · simp at h1
    · simp at h2
    · simp at h3
    · rcases h4 with ⟨h1, rfl, _, hq⟩
      injection h1 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr ⟨rfl, hq⟩⟩
    · simp at h5
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_px {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {v : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.px v) y) :
    ∃ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
      conflictVarSlot (clauseLitAt φ[j] k) = .px v ∧
      ((y = .qv j k ∧ .qv j k ∉ B) ∨ (y = .gv j k ∧ .qv j k ∈ B)) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩
    · rw [hpv] at hg; simp at hg
    · rw [hpv] at hg
      rcases hg with ⟨h1, rfl, _, hq⟩ | ⟨_, h1 | h2 | h3 | h4 | h5⟩
      · injection h1 with hv_eq; subst hv_eq; exact ⟨j', hj', k', hpv, Or.inl ⟨rfl, hq⟩⟩
      · simp at h1
      · simp at h2
      · simp at h3
      · rcases h4 with ⟨h1, rfl, _, hq⟩
        injection h1 with hv_eq; subst hv_eq; exact ⟨j', hj', k', hpv, Or.inr ⟨rfl, hq⟩⟩
      · simp at h5

theorem left_py {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {v : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.py v) y) :
    ∃ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
      conflictVarSlot (clauseLitAt φ[j] k) = .py v ∧
      ((y = .qv j k ∧ .qv j k ∉ B) ∨ (y = .gv j k ∧ .qv j k ∈ B)) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩
    · rw [hpv] at hg
      rcases hg with ⟨h1, rfl, _, hq⟩ | ⟨_, h1 | h2 | h3 | h4 | h5⟩
      · injection h1 with hv_eq; subst hv_eq; exact ⟨j', hj', k', hpv, Or.inl ⟨rfl, hq⟩⟩
      · simp at h1
      · simp at h2
      · simp at h3
      · rcases h4 with ⟨h1, rfl, _, hq⟩
        injection h1 with hv_eq; subst hv_eq; exact ⟨j', hj', k', hpv, Or.inr ⟨rfl, hq⟩⟩
      · simp at h5
    · rw [hpv] at hg; simp at hg

theorem right_qo {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.qo j k)) :
    j < φ.length ∧ ((x = .orig j k ∧ .orig j k ∉ B) ∨ (x = .go j k ∧ .orig j k ∈ B)) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', hj', k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨rfl, h2, hp, _⟩ | ⟨_, h1 | h2 | h3 | h4 | h5⟩
    · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl ⟨rfl, hp⟩⟩
    · simp at h1
    · simp at h2
    · rcases h3 with ⟨rfl, h2, hp, _⟩
      injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr ⟨rfl, hp⟩⟩
    · simp at h4
    · simp at h5
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_qv {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.qv j k)) :
    ∃ hj : j < φ.length,
      (x = conflictVarSlot (clauseLitAt φ[j] k) ∧ conflictVarSlot (clauseLitAt φ[j] k) ∉ B) ∨
      (x = .gv j k ∧ conflictVarSlot (clauseLitAt φ[j] k) ∈ B) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg
        rcases hg with ⟨rfl, h2, hp, _⟩ | ⟨_, h1 | h2 | h3 | h4 | h5⟩
        · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq
          exact ⟨hj', Or.inl ⟨hpv.symm, hpv ▸ hp⟩⟩
        · simp at h1
        · simp at h2
        · rcases h3 with ⟨rfl, h2, hp, _⟩
          injection h2 with hj_eq hk_eq; subst hj_eq hk_eq
          exact ⟨hj', Or.inr ⟨rfl, hpv ▸ hp⟩⟩
        · simp at h4
        · simp at h5 }

theorem left_an {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {k : Fin 3}
    {y : ClauseGadgetLetter} (h : GadgetBlockPair φ B (.an j k) y) :
    j < φ.length ∧ y = .bn j k := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2, ClauseGadgetLetter.an.injEq] at hp
    rcases hp with ⟨⟨rfl, rfl⟩, rfl⟩ | hp
    · exact ⟨hj', rfl⟩
    · simp at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_bn_cn {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {k : Fin 3}
    {x y : ClauseGadgetLetter} (hx : x = .bn j k ∨ x = .cn j k) (h : GadgetBlockPair φ B x y) :
    j < φ.length ∧ y = .an j k := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · rcases hx with rfl | rfl <;> simp [OrigPair2] at hp
  · rcases hx with rfl | rfl <;> simp [VarPair2] at hp
  · rcases hx with rfl | rfl
    · simp only [TapPair2] at hp
      rcases hp with hm | hm | hm | hm | hm | ⟨h6, rfl⟩ | hm
      · simp at hm
      · simp at hm
      · simp at hm
      · simp at hm
      · simp at hm
      · injection h6 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', rfl⟩
      · simp at hm
    · simp only [TapPair2] at hp
      rcases hp with hm | hm | hm | hm | hm | hm | ⟨h7, rfl⟩ | hm
      · simp at hm
      · simp at hm
      · simp at hm
      · simp at hm
      · simp at hm
      · simp at hm
      · injection h7 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', rfl⟩
      · simp at hm
  · rcases hx with rfl | rfl <;> { rw [infix_pair_guard4] at hg; simp at hg }
  · rcases hx with rfl | rfl <;>
      { rw [infix_pair_guard4] at hg
        rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
          { rw [hpv] at hg; simp at hg } }

theorem right_bn {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.bn j k)) :
    j < φ.length ∧ (x = .an j k ∨ x = .qo j k) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with ⟨rfl, h1⟩ | ⟨rfl, h2⟩ | h3
    · injection h1 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr rfl⟩
    · simp at h3
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_cn {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.cn j k)) :
    j < φ.length ∧ (x = .qo j k ∨ x = .qv j k) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with h1 | h2 | ⟨rfl, h3⟩ | ⟨rfl, h4⟩ | h5
    · simp at h1
    · simp at h2
    · injection h3 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h4 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr rfl⟩
    · simp at h5
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_an {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.an j k)) :
    j < φ.length ∧
      (x = .qv j k ∨ x = .bn j k ∨ x = .cn j k ∨ x = .go j k ∨ x = .gv j k) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | ⟨rfl, h5⟩ | ⟨rfl, h6⟩ | ⟨rfl, h7⟩ | h8 | ⟨rfl, h9⟩ |
        h10 | ⟨rfl, h11⟩
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · injection h5 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h6 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr (Or.inl rfl)⟩
    · injection h7 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr (Or.inr (Or.inl rfl))⟩
    · simp at h8
    · injection h9 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · simp at h10
    · injection h11 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_qo {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {k : Fin 3}
    {y : ClauseGadgetLetter} (h : GadgetBlockPair φ B (.qo j k) y) :
    j < φ.length ∧ (y = .bn j k ∨ y = .cn j k ∨ y = .go j k) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', hj', k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with h1 | ⟨h2, rfl⟩ | ⟨h3, rfl⟩ | h4
    · simp at h1
    · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h3 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr (Or.inl rfl)⟩
    · simp at h4
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨h1, _⟩ | ⟨_, h1 | ⟨h2, rfl, _⟩ | h3 | h4 | h5⟩
    · simp at h1
    · simp at h1
    · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr (Or.inr rfl)⟩
    · simp at h3
    · simp at h4
    · simp at h5
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_go {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.go j k)) :
    j < φ.length ∧ (x = .ao j ∨ x = .qo j k ∨ (x = .orig j k ∧ .orig j k ∉ B) ∨
      (x = .go j k ∧ .orig j k ∈ B ∧ .qo j k ∈ B)) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', hj', k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | ⟨rfl, h8⟩ | h9
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · simp at h5
    · simp at h6
    · simp at h7
    · injection h8 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
    · simp at h9
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨_, h1, _⟩ | ⟨_, h1 | ⟨rfl, h2, _⟩ | h3 | ⟨rfl, h4, hp, _⟩ | ⟨rfl, h5, hp, hq⟩⟩
    · simp at h1
    · simp at h1
    · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr (Or.inl rfl)⟩
    · simp at h3
    · injection h4 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inl ⟨rfl, hp⟩))⟩
    · injection h5 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inr ⟨rfl, hp, hq⟩))⟩
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_go {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {k : Fin 3}
    {y : ClauseGadgetLetter} (h : GadgetBlockPair φ B (.go j k) y) :
    j < φ.length ∧ (y = .an j k ∨ (y = .orig j k ∧ .orig j k ∉ B) ∨
      (y = .qo j k ∧ .orig j k ∈ B) ∨ (y = .go j k ∧ .orig j k ∈ B ∧ .qo j k ∈ B)) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', hj', k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | ⟨h9, rfl⟩ | h10
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · simp at h5
    · simp at h6
    · simp at h7
    · simp at h8
    · injection h9 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
    · simp at h10
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨h1, _⟩ | ⟨_, ⟨h1, rfl, hp⟩ | h2 | ⟨h3, rfl, hp, _⟩ | h4 | ⟨h5, rfl, hp, hq⟩⟩
    · simp at h1
    · injection h1 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inr (Or.inl ⟨rfl, hp⟩)⟩
    · simp at h2
    · injection h3 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inl ⟨rfl, hp⟩))⟩
    · simp at h4
    · injection h5 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inr ⟨rfl, hp, hq⟩))⟩
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_gv {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {k : Fin 3}
    {y : ClauseGadgetLetter} (h : GadgetBlockPair φ B (.gv j k) y) :
    ∃ hj : j < φ.length,
      y = .an j k ∨
      (y = conflictVarSlot (clauseLitAt φ[j] k) ∧ conflictVarSlot (clauseLitAt φ[j] k) ∉ B) ∨
      (y = .qv j k ∧ conflictVarSlot (clauseLitAt φ[j] k) ∈ B) ∨
      (y = .gv j k ∧ conflictVarSlot (clauseLitAt φ[j] k) ∈ B ∧ .qv j k ∈ B) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', _, hp⟩ | ⟨j', hj', k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp [VarPair2] at hp
  · simp only [TapPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | ⟨h11, rfl⟩
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · simp at h5
    · simp at h6
    · simp at h7
    · simp at h8
    · simp at h9
    · simp at h10
    · injection h11 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl rfl⟩
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg
        rcases hg with ⟨h1, _⟩ | ⟨_, ⟨h1, rfl, hp⟩ | h2 | ⟨h3, rfl, hp, _⟩ | h4 | ⟨h5, rfl, hp, hq⟩⟩
        · simp at h1
        · injection h1 with hj_eq hk_eq; subst hj_eq hk_eq
          exact ⟨hj', Or.inr (Or.inl ⟨hpv.symm, hpv ▸ hp⟩)⟩
        · simp at h2
        · injection h3 with hj_eq hk_eq; subst hj_eq hk_eq
          exact ⟨hj', Or.inr (Or.inr (Or.inl ⟨rfl, hpv ▸ hp⟩))⟩
        · simp at h4
        · injection h5 with hj_eq hk_eq; subst hj_eq hk_eq
          exact ⟨hj', Or.inr (Or.inr (Or.inr ⟨rfl, hpv ▸ hp, hq⟩))⟩ }

theorem left_cp {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {v : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.cp v) y) :
    v ∈ φ.distinctVars ∧ (y = .py v ∨ y = .ap v) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', hv', hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp only [VarPair2] at hp
    rcases hp with h1 | h2 | h3 | ⟨h4, rfl⟩ | ⟨h5, rfl⟩ | h6
    · simp at h1
    · simp at h2
    · simp at h3
    · injection h4 with hv_eq; subst hv_eq; exact ⟨hv', Or.inl rfl⟩
    · injection h5 with hv_eq; subst hv_eq; exact ⟨hv', Or.inr rfl⟩
    · simp at h6
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_bp {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {v : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.bp v) y) :
    v ∈ φ.distinctVars ∧ (y = .px v ∨ y = .py v) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', hv', hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp only [VarPair2] at hp
    rcases hp with h1 | ⟨h2, rfl⟩ | ⟨h3, rfl⟩ | h4
    · simp at h1
    · injection h2 with hv_eq; subst hv_eq; exact ⟨hv', Or.inl rfl⟩
    · injection h3 with hv_eq; subst hv_eq; exact ⟨hv', Or.inr rfl⟩
    · simp at h4
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_ap {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {v : ℕ}
    (h : GadgetBlockPair φ B x (.ap v)) :
    v ∈ φ.distinctVars ∧ x = .cp v := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', hv', hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp only [VarPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | ⟨rfl, h5⟩ | h6
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · injection h5 with hv_eq; subst hv_eq; exact ⟨hv', rfl⟩
    · simp at h6
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_bp_cp {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x y : ClauseGadgetLetter} {v : ℕ}
    (hy : y = .bp v ∨ y = .cp v) (h : GadgetBlockPair φ B x y) :
    v ∈ φ.distinctVars ∧ x = .ap v := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', hv', hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · rcases hy with rfl | rfl <;> simp [OrigPair2] at hp
  · rcases hy with rfl | rfl
    · simp only [VarPair2] at hp
      rcases hp with h1 | h2 | h3 | h4 | h5 | ⟨rfl, h6⟩ | h7
      · simp at h1
      · simp at h2
      · simp at h3
      · simp at h4
      · simp at h5
      · injection h6 with hv_eq; subst hv_eq; exact ⟨hv', rfl⟩
      · simp at h7
    · simp only [VarPair2] at hp
      rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | ⟨rfl, h7⟩
      · simp at h1
      · simp at h2
      · simp at h3
      · simp at h4
      · simp at h5
      · simp at h6
      · injection h7 with hv_eq; subst hv_eq; exact ⟨hv', rfl⟩
  · rcases hy with rfl | rfl <;> simp [TapPair2] at hp
  · rcases hy with rfl | rfl <;> { rw [infix_pair_guard4] at hg; simp at hg }
  · rcases hy with rfl | rfl <;>
      { rw [infix_pair_guard4] at hg
        rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
          { rw [hpv] at hg; simp at hg } }

theorem right_py {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {v : ℕ}
    (h : GadgetBlockPair φ B x (.py v)) :
    (v ∈ φ.distinctVars ∧ (x = .bp v ∨ x = .cp v)) ∨
    (∃ (j : ℕ) (hj : j < φ.length) (k : Fin 3),
      clauseLitAt φ[j] k = (v, true) ∧ x = .gv j k) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', _, hp⟩ | ⟨v', hv', hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp [OrigPair2] at hp
  · simp only [VarPair2] at hp
    rcases hp with h1 | h2 | ⟨rfl, h3⟩ | ⟨rfl, h4⟩ | h5
    · simp at h1
    · simp at h2
    · injection h3 with hv_eq; subst hv_eq; exact Or.inl ⟨hv', Or.inl rfl⟩
    · injection h4 with hv_eq; subst hv_eq; exact Or.inl ⟨hv', Or.inr rfl⟩
    · simp at h5
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨hpol, hpv⟩ | ⟨_, hpv⟩
    · rw [hpv] at hg
      rcases hg with ⟨_, h1, _⟩ | ⟨_, ⟨rfl, h1, _⟩ | h2 | h3 | h4 | h5⟩
      · simp at h1
      · injection h1 with hv_eq; subst hv_eq
        refine Or.inr ⟨j', hj', k', ?_, rfl⟩
        rcases hlit : clauseLitAt φ[j'] k' with ⟨w, b⟩
        rw [hlit] at hpol
        exact Prod.ext rfl hpol
      · simp at h2
      · simp at h3
      · simp at h4
      · simp at h5
    · rw [hpv] at hg; simp at hg

theorem left_do {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.do_ j) y) :
    j < φ.length ∧ (y = .orig j 2 ∨ y = .ao j) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', hj', hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp only [OrigPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | ⟨h6, rfl⟩ | ⟨h7, rfl⟩ | h8
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · simp at h5
    · injection h6 with hj_eq; subst hj_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h7 with hj_eq; subst hj_eq; exact ⟨hj', Or.inr rfl⟩
    · simp at h8
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_co {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.co j) y) :
    j < φ.length ∧ (y = .orig j 1 ∨ y = .orig j 2) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', hj', hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp only [OrigPair2] at hp
    rcases hp with h1 | h2 | h3 | ⟨h4, rfl⟩ | ⟨h5, rfl⟩ | h6
    · simp at h1
    · simp at h2
    · simp at h3
    · injection h4 with hj_eq; subst hj_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h5 with hj_eq; subst hj_eq; exact ⟨hj', Or.inr rfl⟩
    · simp at h6
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem left_bo {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {j : ℕ} {y : ClauseGadgetLetter}
    (h : GadgetBlockPair φ B (.bo j) y) :
    j < φ.length ∧ (y = .orig j 0 ∨ y = .orig j 1) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', hj', hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp only [OrigPair2] at hp
    rcases hp with h1 | ⟨h2, rfl⟩ | ⟨h3, rfl⟩ | h4
    · simp at h1
    · injection h2 with hj_eq; subst hj_eq; exact ⟨hj', Or.inl rfl⟩
    · injection h3 with hj_eq; subst hj_eq; exact ⟨hj', Or.inr rfl⟩
    · simp at h4
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_ao {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    (h : GadgetBlockPair φ B x (.ao j)) :
    j < φ.length ∧ x = .do_ j := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', hj', hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp only [OrigPair2] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | ⟨rfl, h7⟩ | h8
    · simp at h1
    · simp at h2
    · simp at h3
    · simp at h4
    · simp at h5
    · simp at h6
    · injection h7 with hj_eq; subst hj_eq; exact ⟨hj', rfl⟩
    · simp at h8
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg; simp at hg
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

theorem right_bo_co_do {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x y : ClauseGadgetLetter} {j : ℕ}
    (hy : y = .bo j ∨ y = .co j ∨ y = .do_ j) (h : GadgetBlockPair φ B x y) :
    j < φ.length ∧ x = .ao j := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', hj', hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', _, k', hg⟩ | ⟨j', hj', k', hg⟩
  · rcases hy with rfl | rfl | rfl
    · simp only [OrigPair2] at hp
      rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | ⟨rfl, h8⟩ | h9
      · simp at h1
      · simp at h2
      · simp at h3
      · simp at h4
      · simp at h5
      · simp at h6
      · simp at h7
      · injection h8 with hj_eq; subst hj_eq; exact ⟨hj', rfl⟩
      · simp at h9
    · simp only [OrigPair2] at hp
      rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | ⟨rfl, h9⟩ | h10
      · simp at h1
      · simp at h2
      · simp at h3
      · simp at h4
      · simp at h5
      · simp at h6
      · simp at h7
      · simp at h8
      · injection h9 with hj_eq; subst hj_eq; exact ⟨hj', rfl⟩
      · simp at h10
    · simp only [OrigPair2] at hp
      rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | ⟨rfl, h10⟩
      · simp at h1
      · simp at h2
      · simp at h3
      · simp at h4
      · simp at h5
      · simp at h6
      · simp at h7
      · simp at h8
      · simp at h9
      · injection h10 with hj_eq; subst hj_eq; exact ⟨hj', rfl⟩
  · rcases hy with rfl | rfl | rfl <;> simp [VarPair2] at hp
  · rcases hy with rfl | rfl | rfl <;> simp [TapPair2] at hp
  · rcases hy with rfl | rfl | rfl <;> { rw [infix_pair_guard4] at hg; simp at hg }
  · rcases hy with rfl | rfl | rfl <;>
      { rw [infix_pair_guard4] at hg
        rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
          { rw [hpv] at hg; simp at hg } }

theorem right_orig {φ : CNF ℕ} {B : Set ClauseGadgetLetter} {x : ClauseGadgetLetter} {j : ℕ}
    {k : Fin 3} (h : GadgetBlockPair φ B x (.orig j k)) :
    j < φ.length ∧
      ((k = 0 ∧ (x = .ao j ∨ x = .bo j)) ∨
       (k = 1 ∧ (x = .bo j ∨ x = .co j)) ∨
       (k = 2 ∧ (x = .co j ∨ x = .do_ j)) ∨
       x = .go j k) := by
  rcases (gadgetBlockPair_decomp h).2.2 with ⟨j', hj', hp⟩ | ⟨v', _, hp⟩ | ⟨j', _, k', hp⟩ |
      ⟨j', hj', k', hg⟩ | ⟨j', hj', k', hg⟩
  · simp only [OrigPair2] at hp
    rcases hp with ⟨rfl, h1⟩ | ⟨rfl, h2⟩ | ⟨rfl, h3⟩ | ⟨rfl, h4⟩ | ⟨rfl, h5⟩ | ⟨rfl, h6⟩ | h7
    · injection h1 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl ⟨rfl, Or.inl rfl⟩⟩
    · injection h2 with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', Or.inl ⟨rfl, Or.inr rfl⟩⟩
    · injection h3 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
    · injection h4 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
    · injection h5 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))⟩
    · injection h6 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))⟩
    · simp at h7
  · simp [VarPair2] at hp
  · simp [TapPair2] at hp
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨_, h1, _⟩ | ⟨_, ⟨rfl, h1, _⟩ | h2 | h3 | h4 | h5⟩
    · simp at h1
    · injection h1 with hj_eq hk_eq; subst hj_eq hk_eq
      exact ⟨hj', Or.inr (Or.inr (Or.inr rfl))⟩
    · simp at h2
    · simp at h3
    · simp at h4
    · simp at h5
  · rw [infix_pair_guard4] at hg
    rcases conflictVarSlot_cases (clauseLitAt φ[j'] k') with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { rw [hpv] at hg; simp at hg }

end BlockClassification

section NodupSeparators

private theorem nodup_of_forall_count_le_one {A : Type*} [DecidableEq A] :
    ∀ {l : List A}, (∀ a ∈ l, l.count a ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | a :: as, h => by
    have hc := h a (List.mem_cons_self ..)
    rw [List.count_cons_self] at hc
    have ha_not : a ∉ as := List.count_eq_zero.mp (by omega)
    refine List.nodup_cons.mpr ⟨ha_not, nodup_of_forall_count_le_one fun b hb ↦ ?_⟩
    have hcb := h b (List.mem_cons_of_mem a hb)
    rw [List.count_cons] at hcb
    omega

private theorem isUnavoidable_of_nodup {A : Type*} :
    ∀ {w : List A}, w.Nodup → IsUnavoidable w
  | [], _ => isUnavoidable_nil
  | a :: ws, hw => by
    rcases List.nodup_cons.mp hw with ⟨ha_not, hnd⟩
    have hfree : IsFreeLetter (a :: ws) a := by
      refine isFreeLetter_iff.mpr ⟨List.mem_cons_self .., fun hch ↦ ?_⟩
      rcases hasAlternatingChain_iff_reflTransGen.mp hch with ⟨b, _, s, t, hst⟩
      cases s with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at hst
        have hmem : a ∈ ws := by rw [← hst.2]; simp
        exact ha_not hmem
      | cons c cs =>
        simp only [List.cons_append, List.cons.injEq] at hst
        have hin : [b, a] <:+: ws := ⟨cs, t, hst.2⟩
        exact ha_not (hin.subset (by simp))
    have hdel : deleteLetter a (a :: ws) = ws := by
      rw [deleteLetter_cons_eq, deleteLetter_eq_deleteLetters]
      exact deleteLetters_eq_self fun x hx hxa ↦
        ha_not (by simpa [Set.mem_singleton_iff.mp hxa] using hx)
    have hun : IsUnavoidable (deleteLetter a (a :: ws)) := by
      rw [hdel]
      exact isUnavoidable_of_nodup hnd
    exact hfree.isUnavoidable_of_deleteLetter hun

theorem isUnavoidable_deleteLetters_of_contains_nonSep {φ : CNF ℕ}
    {B : Set ClauseGadgetLetter} (hcov : ∀ u ∈ clauseGadgetPattern φ, u.isSep = false → u ∈ B) :
    IsUnavoidable (deleteLetters B (clauseGadgetPattern φ)) := by
  refine isUnavoidable_of_nodup (nodup_of_forall_count_le_one fun u hu ↦ ?_)
  rcases mem_deleteLetters.mp hu with ⟨hup, huB⟩
  cases hs : u.isSep
  · exact absurd (hcov u hup hs) huB
  · rcases ClauseGadgetLetter.isSep_eq_true_iff.mp hs with ⟨z, rfl⟩
    exact count_sep_deleteLetters_clauseGadgetPattern φ B z

end NodupSeparators

end CslibFrontier.Complexity

end
