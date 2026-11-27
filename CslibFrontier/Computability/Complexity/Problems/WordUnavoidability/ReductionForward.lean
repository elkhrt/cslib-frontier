/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.WordUnavoidability.ReductionPairs

/-!
# Forward Direction of the `3`-CNF Unavoidability Reduction

This module proves `satisfiable_imp_isUnavoidable_clauseGadgetPattern`: every satisfiable `3`-CNF
formula `φ` produces an unavoidable word pattern `clauseGadgetPattern φ` via an explicit
`12`-round
free-set deletion schedule reducing `clauseGadgetPattern φ` to its duplicate-free separator
skeleton.
-/

public section

namespace CslibFrontier.Complexity

open CslibFrontier.Word Cslib.Logic.PL

private def litAt (φ : CNF ℕ) (j : ℕ) (k : Fin 3) : Literal ℕ :=
  clauseLitAt (φ.getD j []) k

private theorem litAt_eq {φ : CNF ℕ} {j : ℕ} (hj : j < φ.length) (k : Fin 3) :
    litAt φ j k = clauseLitAt φ[j] k := by
  simp [litAt, List.getD_eq_getElem?_getD, hj]

private def litTrue (φ : CNF ℕ) (σ : ℕ → Bool) (j : ℕ) (k : Fin 3) : Bool :=
  Literal.eval σ (litAt φ j k)

private def roundSet (φ : CNF ℕ) (σ : ℕ → Bool) : ℕ → Set ClauseGadgetLetter
  | 1 => {u | (∃ v ∈ φ.distinctVars, (σ v = true ∧ u = .px v) ∨ (σ v = false ∧ u = .py v)) ∨
              (∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ litTrue φ σ j k = true ∧ u = .orig j k)}
  | 2 => {u | ∃ (j : ℕ) (k : Fin 3), j < φ.length ∧
              ((litTrue φ σ j k = false ∧ u = .qo j k) ∨
               (litTrue φ σ j k = true ∧ u = .qv j k))}
  | 3 => {u | ∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ litTrue φ σ j k = false ∧ u = .an j k}
  | 4 => {u | ∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ litTrue φ σ j k = false ∧
              (u = .bn j k ∨ u = .cn j k)}
  | 5 => {u | ∃ v ∈ φ.distinctVars, u = .ap v}
  | 6 => {u | ∃ v ∈ φ.distinctVars, u = .bp v ∨ u = .cp v}
  | 7 => {u | ∃ j < φ.length, u = .ao j}
  | 8 => {u | ∃ j < φ.length, u = .bo j ∨ u = .co j ∨ u = .do_ j}
  | 9 => {u | ∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ litTrue φ σ j k = true ∧ u = .an j k}
  | 10 => {u | ∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ litTrue φ σ j k = true ∧
               (u = .bn j k ∨ u = .cn j k)}
  | 11 => {u | u.isGuard = true}
  | 12 => {u | u.isSep = false}
  | _ => ∅

private def cumB (φ : CNF ℕ) (σ : ℕ → Bool) : ℕ → Set ClauseGadgetLetter
  | 0 => ∅
  | t + 1 => cumB φ σ t ∪ roundSet φ σ (t + 1)

private theorem roundSet_nonSep (φ : CNF ℕ) (σ : ℕ → Bool) (r : ℕ) :
    ∀ u ∈ roundSet φ σ r, u.isSep = false := by
  intro u hu
  match r with
  | 1 =>
    rcases hu with ⟨_, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl
  | 2 =>
    rcases hu with ⟨_, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> rfl
  | 3 => rcases hu with ⟨_, _, _, _, rfl⟩; rfl
  | 4 => rcases hu with ⟨_, _, _, _, rfl | rfl⟩ <;> rfl
  | 5 => rcases hu with ⟨_, _, rfl⟩; rfl
  | 6 => rcases hu with ⟨_, _, rfl | rfl⟩ <;> rfl
  | 7 => rcases hu with ⟨_, _, rfl⟩; rfl
  | 8 => rcases hu with ⟨_, _, rfl | rfl | rfl⟩ <;> rfl
  | 9 => rcases hu with ⟨_, _, _, _, rfl⟩; rfl
  | 10 => rcases hu with ⟨_, _, _, _, rfl | rfl⟩ <;> rfl
  | 11 => cases u <;> first | rfl | simp [roundSet] at hu
  | 12 => exact hu
  | 0 => exact False.elim hu
  | n + 13 => exact False.elim hu

private theorem sep_not_mem_cumB (φ : CNF ℕ) (σ : ℕ → Bool) :
    ∀ (t z : ℕ), ClauseGadgetLetter.sep z ∉ cumB φ σ t
  | 0, _ => Set.notMem_empty _
  | t + 1, z => by
    rintro (h₁ | h₂)
    · exact sep_not_mem_cumB φ σ t z h₁
    · have hs := roundSet_nonSep φ σ (t + 1) (.sep z) h₂
      simp at hs

private theorem cumB_mono {φ : CNF ℕ} {σ : ℕ → Bool} {s t : ℕ} (hst : s ≤ t) :
    cumB φ σ s ⊆ cumB φ σ t := by
  induction hst with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact ih.trans Set.subset_union_left

private theorem roundSet_subset_cumB {φ : CNF ℕ} {σ : ℕ → Bool} {r t : ℕ}
    (hr1 : 1 ≤ r) (hrt : r ≤ t) : roundSet φ σ r ⊆ cumB φ σ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr1
  exact Set.subset_union_right.trans (cumB_mono hrt)

private theorem orig_mem_roundSet1_iff {φ : CNF ℕ} {σ : ℕ → Bool} {j : ℕ} {k : Fin 3} :
    ClauseGadgetLetter.orig j k ∈ roundSet φ σ 1 ↔ j < φ.length ∧ litTrue φ σ j k = true := by
  simp only [roundSet, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨j', k', hj', ht, h⟩)
    · simp at h
    · simp at h
    · injection h with hj_eq hk_eq; subst hj_eq hk_eq; exact ⟨hj', ht⟩
  · rintro ⟨hj, ht⟩
    exact Or.inr ⟨j, k, hj, ht, rfl⟩

private theorem conflictVar_mem_roundSet1_iff {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3)
    {σ : ℕ → Bool} {j : ℕ} (hj : j < φ.length) (k : Fin 3) :
    conflictVarSlot (clauseLitAt φ[j] k) ∈ roundSet φ σ 1 ↔ litTrue φ σ j k = false := by
  have hv_mem := lit_var_mem_distinctVars h3 hj k
  have hlt_eq : litTrue φ σ j k = Literal.eval σ (clauseLitAt φ[j] k) := by
    simp [litTrue, litAt_eq hj k]
  rw [hlt_eq]
  rcases hlit : clauseLitAt φ[j] k with ⟨v, pol⟩
  have hv' : v ∈ φ.distinctVars := by simpa [hlit] using hv_mem
  cases pol
  · simp only [conflictVarSlot_mk_false, Literal.eval_mk, roundSet,
      Set.mem_ofPred_eq]
    constructor
    · rintro (⟨v', _, ⟨hσv, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩)
      · injection h with hv_eq; subst hv_eq; simp [hσv]
      · simp at h
      · simp at h
    · intro hσv
      have htrue : σ v = true := by cases h : σ v <;> simp_all
      exact Or.inl ⟨v, hv', Or.inl ⟨htrue, rfl⟩⟩
  · simp only [conflictVarSlot_mk_true, Literal.eval_mk, roundSet, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨v', _, ⟨_, h⟩ | ⟨hσv, h⟩⟩ | ⟨_, _, _, _, h⟩)
      · simp at h
      · injection h with hv_eq; subst hv_eq; simp [hσv]
      · simp at h
    · intro hσv
      have hfalse : σ v = false := by cases h : σ v <;> simp_all
      exact Or.inl ⟨v, hv', Or.inr ⟨hfalse, rfl⟩⟩

private theorem not_orig_px_py_qo_qv_in_round_3_to_10 (φ : CNF ℕ) (σ : ℕ → Bool) {r : ℕ}
    (hr3 : 3 ≤ r) (hr10 : r ≤ 10) {u : ClauseGadgetLetter} (hu : u ∈ roundSet φ σ r) :
    (∀ j k, u ≠ .orig j k ∧ u ≠ .qo j k ∧ u ≠ .qv j k) ∧
    (∀ v, u ≠ .px v ∧ u ≠ .py v) := by
  have hr_cases : r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 := by omega
  rcases hr_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hu with ⟨_, _, _, _, rfl⟩; simp
  · rcases hu with ⟨_, _, _, _, rfl | rfl⟩ <;> simp
  · rcases hu with ⟨_, _, rfl⟩; simp
  · rcases hu with ⟨_, _, rfl | rfl⟩ <;> simp
  · rcases hu with ⟨_, _, rfl⟩; simp
  · rcases hu with ⟨_, _, rfl | rfl | rfl⟩ <;> simp
  · rcases hu with ⟨_, _, _, _, rfl⟩; simp
  · rcases hu with ⟨_, _, _, _, rfl | rfl⟩ <;> simp

private theorem cumB10_guard_go_exclusive {φ : CNF ℕ} {σ : ℕ → Bool} {j : ℕ} (hj : j < φ.length)
    (k : Fin 3) :
    (ClauseGadgetLetter.orig j k ∈ cumB φ σ 10 ↔ litTrue φ σ j k = true) ∧
    (ClauseGadgetLetter.qo j k ∈ cumB φ σ 10 ↔ litTrue φ σ j k = false) := by
  have horig : ∀ t ≤ 10, 1 ≤ t →
      (ClauseGadgetLetter.orig j k ∈ cumB φ σ t ↔ litTrue φ σ j k = true) := by
    intro t ht10 ht1
    constructor
    · intro hm
      induction t with
      | zero => omega
      | succ t ih =>
        rcases hm with hm1 | hm2
        · by_cases ht0 : t = 0
          · subst ht0; exact False.elim hm1
          · exact ih (by omega) (by omega) hm1
        · by_cases ht0 : t = 0
          · subst ht0; exact (orig_mem_roundSet1_iff.mp hm2).2
          · by_cases ht1' : t = 1
            · subst ht1'
              rcases hm2 with ⟨_, _, _, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> simp at h
            · exfalso
              exact ((not_orig_px_py_qo_qv_in_round_3_to_10 φ σ (by omega) (by omega) hm2).1
                j k).1 rfl
    · intro hlt
      exact roundSet_subset_cumB (r := 1) (by decide) ht1
        (orig_mem_roundSet1_iff.mpr ⟨hj, hlt⟩)
  have hqo : ∀ t ≤ 10, 2 ≤ t →
      (ClauseGadgetLetter.qo j k ∈ cumB φ σ t ↔ litTrue φ σ j k = false) := by
    intro t ht10 ht2
    constructor
    · intro hm
      induction t with
      | zero => omega
      | succ t ih =>
        rcases hm with hm1 | hm2
        · by_cases ht1' : t ≤ 1
          · have ht_eq : t = 0 ∨ t = 1 := by omega
            rcases ht_eq with rfl | rfl
            · exact False.elim hm1
            · rcases hm1 with h0 | h1
              · exact False.elim h0
              · rcases h1 with ⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩ <;> simp at h
          · exact ih (by omega) (by omega) hm1
        · by_cases ht1' : t = 1
          · subst ht1'
            rcases hm2 with ⟨j', k', _, ⟨hf, h⟩ | ⟨_, h⟩⟩
            · injection h with hj_eq hk_eq; subst hj_eq hk_eq; exact hf
            · simp at h
          · exfalso
            exact ((not_orig_px_py_qo_qv_in_round_3_to_10 φ σ (by omega) (by omega) hm2).1
              j k).2.1 rfl
    · intro hlf
      exact roundSet_subset_cumB (r := 2) (by decide) ht2 ⟨j, k, hj, Or.inl ⟨hlf, rfl⟩⟩
  exact ⟨horig 10 (Nat.le_refl _) (by decide), hqo 10 (Nat.le_refl _) (by decide)⟩

private theorem cumB10_guard_gv_exclusive {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3)
    {σ : ℕ → Bool} {j : ℕ} (hj : j < φ.length) (k : Fin 3) :
    (conflictVarSlot (clauseLitAt φ[j] k) ∈ cumB φ σ 10 ↔ litTrue φ σ j k = false) ∧
    (ClauseGadgetLetter.qv j k ∈ cumB φ σ 10 ↔ litTrue φ σ j k = true) := by
  let pvar := conflictVarSlot (clauseLitAt φ[j] k)
  have hpvar_ne : ∀ r, 3 ≤ r → r ≤ 10 → pvar ∉ roundSet φ σ r := by
    intro r hr3 hr10 hm
    have hnot := (not_orig_px_py_qo_qv_in_round_3_to_10 φ σ hr3 hr10 hm).2
    rcases conflictVarSlot_cases (clauseLitAt φ[j] k) with ⟨_, hpv⟩ | ⟨_, hpv⟩
    · exact (hnot _).2 hpv
    · exact (hnot _).1 hpv
  have hpvar_not2 : pvar ∉ roundSet φ σ 2 := by
    intro hm
    rcases hm with ⟨_, _, _, ⟨_, h⟩ | ⟨_, h⟩⟩ <;>
      rcases conflictVarSlot_cases (clauseLitAt φ[j] k) with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
      { dsimp [pvar] at h; rw [hpv] at h; simp at h }
  have hpvar : pvar ∈ cumB φ σ 10 ↔ litTrue φ σ j k = false := by
    constructor
    · intro hm
      have haux : ∀ t ≤ 10, pvar ∈ cumB φ σ t → pvar ∈ roundSet φ σ 1 := by
        intro t ht10 hmt
        induction t with
        | zero => exact False.elim hmt
        | succ t ih =>
          rcases hmt with hm1 | hm2
          · exact ih (by omega) hm1
          · by_cases ht0 : t = 0
            · subst ht0; exact hm2
            · by_cases ht1 : t = 1
              · subst ht1; exact False.elim (hpvar_not2 hm2)
              · exact False.elim (hpvar_ne (t + 1) (by omega) ht10 hm2)
      exact (conflictVar_mem_roundSet1_iff h3 hj k).mp (haux 10 (Nat.le_refl _) hm)
    · intro hlf
      exact roundSet_subset_cumB (r := 1) (t := 10) (by decide) (by decide)
        ((conflictVar_mem_roundSet1_iff h3 hj k).mpr hlf)
  have hqv : ClauseGadgetLetter.qv j k ∈ cumB φ σ 10 ↔ litTrue φ σ j k = true := by
    constructor
    · intro hm
      have haux : ∀ t ≤ 10, ClauseGadgetLetter.qv j k ∈ cumB φ σ t →
          ClauseGadgetLetter.qv j k ∈ roundSet φ σ 2 := by
        intro t ht10 hmt
        induction t with
        | zero => exact False.elim hmt
        | succ t ih =>
          rcases hmt with hm1 | hm2
          · exact ih (by omega) hm1
          · by_cases ht0 : t = 0
            · subst ht0
              rcases hm2 with ⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩ <;> simp at h
            · by_cases ht1 : t = 1
              · subst ht1; exact hm2
              · exfalso
                exact ((not_orig_px_py_qo_qv_in_round_3_to_10 φ σ (by omega) ht10 hm2).1
                  j k).2.2 rfl
      rcases haux 10 (Nat.le_refl _) hm with ⟨j', k', _, ⟨_, h⟩ | ⟨hlt, h⟩⟩
      · simp at h
      · injection h with hj_eq hk_eq; subst hj_eq hk_eq; exact hlt
    · intro hlt
      exact roundSet_subset_cumB (r := 2) (t := 10) (by decide) (by decide)
        ⟨j, k, hj, Or.inr ⟨hlt, rfl⟩⟩
  exact ⟨hpvar, hqv⟩

private theorem freeSet_round1 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 0) (clauseGadgetPattern φ)) (roundSet φ σ 1) := by
  refine isFreeSet_of_closed_left_region (sep_not_mem_cumB φ σ 0) (roundSet_nonSep φ σ 1)
    Set.Subset.rfl ?_ ?_
  · intro u hu c w huc hwc
    rcases hu with ⟨v, hv, ⟨hσ, rfl⟩ | ⟨hσ, rfl⟩⟩ | ⟨j, k, hj, ht, rfl⟩
    · obtain ⟨j, _, k, hpv, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_px huc
      · obtain ⟨_, ⟨hw_eq, _⟩ | ⟨_, hcB⟩⟩ := right_qv hwc
        · rw [hw_eq, hpv]; exact Or.inl ⟨v, hv, Or.inl ⟨hσ, rfl⟩⟩
        · exact False.elim hcB
      · exact False.elim hq
    · obtain ⟨j, _, k, hpv, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_py huc
      · obtain ⟨_, ⟨hw_eq, _⟩ | ⟨_, hcB⟩⟩ := right_qv hwc
        · rw [hw_eq, hpv]; exact Or.inl ⟨v, hv, Or.inr ⟨hσ, rfl⟩⟩
        · exact False.elim hcB
      · exact False.elim hq
    · obtain ⟨_, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_orig huc
      · obtain ⟨_, ⟨rfl, _⟩ | ⟨_, hoB⟩⟩ := right_qo hwc
        · exact Or.inr ⟨j, k, hj, ht, rfl⟩
        · exact False.elim hoB
      · exact False.elim hq
  · intro u hu y hy huy
    rcases hu with ⟨v, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ | ⟨j, k, _, _, rfl⟩
    · obtain ⟨j, _, k, _, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_px huy
      · rcases hy with ⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩ <;> simp at h
      · exact False.elim hq
    · obtain ⟨j, _, k, _, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_py huy
      · rcases hy with ⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩ <;> simp at h
      · exact False.elim hq
    · obtain ⟨_, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_orig huy
      · rcases hy with ⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩ <;> simp at h
      · exact False.elim hq

private theorem freeSet_round2 {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 1) (clauseGadgetPattern φ)) (roundSet φ σ 2) := by
  let S : Set ClauseGadgetLetter :=
    {u | u.isSep = false ∧ (∀ v, u ≠ .px v ∧ u ≠ .py v) ∧ (∀ j k, u ≠ .orig j k)}
  have hB1_eq : cumB φ σ 1 = roundSet φ σ 1 := Set.empty_union _
  have hno_q_B1 : ∀ j k, ClauseGadgetLetter.qo j k ∉ cumB φ σ 1 ∧
      ClauseGadgetLetter.qv j k ∉ cumB φ σ 1 := by
    intro j k; rw [hB1_eq]; constructor <;>
      { rintro (⟨_, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨_, _, _, _, h⟩) <;> simp at h }
  refine isFreeSet_of_closed_left_region (S := S) (sep_not_mem_cumB φ σ 1) (roundSet_nonSep φ σ 2)
    ?_ ?_ ?_
  · intro u hu
    rcases hu with ⟨_, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> exact ⟨rfl, by simp, by simp⟩
  · intro u hu c w huc hwc
    refine ⟨hwc.1, fun v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩, fun j k ho ↦ ?_⟩
    · subst hv
      obtain ⟨j, _, k, hpv, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_px hwc
      · obtain ⟨_, ⟨hu_eq, _⟩ | ⟨_, hcB⟩⟩ := right_qv huc
        · exact (hu.2.1 v).1 (hu_eq.trans hpv)
        · exact False.elim (hwc.not_mem_left (hpv ▸ hcB))
      · exact False.elim ((hno_q_B1 j k).2 hq)
    · subst hv
      obtain ⟨j, _, k, hpv, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_py hwc
      · obtain ⟨_, ⟨hu_eq, _⟩ | ⟨_, hcB⟩⟩ := right_qv huc
        · exact (hu.2.1 v).2 (hu_eq.trans hpv)
        · exact False.elim (hwc.not_mem_left (hpv ▸ hcB))
      · exact False.elim ((hno_q_B1 j k).2 hq)
    · subst ho
      obtain ⟨_, ⟨rfl, _⟩ | ⟨_, hq⟩⟩ := left_orig hwc
      · obtain ⟨_, ⟨rfl, _⟩ | ⟨_, hoB⟩⟩ := right_qo huc
        · exact hu.2.2 j k rfl
        · exact False.elim (hwc.not_mem_left hoB)
      · exact False.elim ((hno_q_B1 j k).1 hq)
  · intro u hu y hy huy
    rcases hy with ⟨j, k, hj, ⟨hlf, rfl⟩ | ⟨hlt, rfl⟩⟩
    · obtain ⟨_, ⟨rfl, _⟩ | ⟨_, hoB⟩⟩ := right_qo huy
      · exact hu.2.2 j k rfl
      · rw [hB1_eq, orig_mem_roundSet1_iff] at hoB
        rw [hoB.2] at hlf; cases hlf
    · obtain ⟨_, ⟨hu_eq, _⟩ | ⟨_, hcB⟩⟩ := right_qv huy
      · rcases conflictVarSlot_cases (clauseLitAt φ[j] k) with ⟨_, hpv⟩ | ⟨_, hpv⟩
        · exact (hu.2.1 _).2 (hu_eq.trans hpv)
        · exact (hu.2.1 _).1 (hu_eq.trans hpv)
      · rw [hB1_eq, conflictVar_mem_roundSet1_iff h3 hj k] at hcB
        rw [hcB] at hlt; cases hlt

private theorem freeSet_round3 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 2) (clauseGadgetPattern φ)) (roundSet φ σ 3) := by
  refine isFreeSet_of_closed_left_region (sep_not_mem_cumB φ σ 2) (roundSet_nonSep φ σ 3)
    Set.Subset.rfl ?_ ?_
  · intro u hu c w huc hwc
    rcases hu with ⟨j, k, hj, hlf, rfl⟩
    obtain ⟨_, rfl⟩ := left_an huc
    obtain ⟨_, rfl | rfl⟩ := right_bn hwc
    · exact ⟨j, k, hj, hlf, rfl⟩
    · exfalso
      exact hwc.not_mem_left
        (roundSet_subset_cumB (r := 2) (t := 2) (by decide) (Nat.le_refl _)
          ⟨j, k, hj, Or.inl ⟨hlf, rfl⟩⟩)
  · intro u hu y hy huy
    rcases hu with ⟨j, k, _, _, rfl⟩
    obtain ⟨_, rfl⟩ := left_an huy
    rcases hy with ⟨_, _, _, _, h⟩
    simp at h

private theorem freeSet_round4 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 3) (clauseGadgetPattern φ)) (roundSet φ σ 4) := by
  refine isFreeSet_of_no_left (sep_not_mem_cumB φ σ 3) (roundSet_nonSep φ σ 4) ?_
  intro x hx c hxc
  rcases hx with ⟨j, k, hj, hlf, hbc⟩
  obtain ⟨_, rfl⟩ := left_bn_cn hbc hxc
  exact hxc.not_mem_right
    (roundSet_subset_cumB (r := 3) (t := 3) (by decide) (Nat.le_refl _) ⟨j, k, hj, hlf, rfl⟩)

private theorem freeSet_round5 {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 4) (clauseGadgetPattern φ)) (roundSet φ σ 5) := by
  let T : Set ClauseGadgetLetter :=
    {u | (∃ v, u = .cp v) ∨
         (∃ v, σ v = true ∧ u = .bp v) ∨
         (∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ (litAt φ j k).2 = true ∧
            litTrue φ σ j k = true ∧
            (u = .gv j k ∨ u = .go j k ∨ u = .bn j k ∨ u = .cn j k))}
  let S : Set ClauseGadgetLetter := {u | u.isSep = false ∧ u ∉ T}
  have hT_closed : ∀ u ∈ T, ∀ c w,
      GadgetBlockPair φ (cumB φ σ 4) u c → GadgetBlockPair φ (cumB φ σ 4) w c → w ∈ T := by
    intro u hu c w huc hwc
    have hpy_step : ∀ v ∈ φ.distinctVars, σ v = true →
        GadgetBlockPair φ (cumB φ σ 4) w (.py v) → w ∈ T := by
      intro v _ hσv hw_py
      rcases right_py hw_py with ⟨_, rfl | rfl⟩ | ⟨j, hj, k, hlit, rfl⟩
      · exact Or.inr (Or.inl ⟨v, hσv, rfl⟩)
      · exact Or.inl ⟨v, rfl⟩
      · have hla : litAt φ j k = (v, true) := (litAt_eq hj k).trans hlit
        have hlt : litTrue φ σ j k = true := by simp [litTrue, hla, hσv]
        exact Or.inr (Or.inr ⟨j, k, hj, by simp [hla], hlt, Or.inl rfl⟩)
    have han_step : ∀ (j : ℕ) (k : Fin 3), j < φ.length → (litAt φ j k).2 = true →
        litTrue φ σ j k = true → GadgetBlockPair φ (cumB φ σ 4) w (.an j k) → w ∈ T := by
      intro j k hj hpol hlt hw_an
      obtain ⟨_, rfl | rfl | rfl | rfl | rfl⟩ := right_an hw_an
      · exfalso
        exact hw_an.not_mem_left
          (roundSet_subset_cumB (r := 2) (t := 4) (by decide) (by decide)
            ⟨j, k, hj, Or.inr ⟨hlt, rfl⟩⟩)
      · exact Or.inr (Or.inr ⟨j, k, hj, hpol, hlt, Or.inr (Or.inr (Or.inl rfl))⟩)
      · exact Or.inr (Or.inr ⟨j, k, hj, hpol, hlt, Or.inr (Or.inr (Or.inr rfl))⟩)
      · exact Or.inr (Or.inr ⟨j, k, hj, hpol, hlt, Or.inr (Or.inl rfl)⟩)
      · exact Or.inr (Or.inr ⟨j, k, hj, hpol, hlt, Or.inl rfl⟩)
    rcases hu with ⟨v, rfl⟩ | ⟨v, hσv, rfl⟩ | ⟨j, k, hj, hpol, hlt, hug⟩
    · obtain ⟨hv, rfl | rfl⟩ := left_cp huc
      · cases hσ : σ v
        · exfalso
          exact huc.not_mem_right
            (roundSet_subset_cumB (r := 1) (t := 4) (by decide) (by decide)
              (Or.inl ⟨v, hv, Or.inr ⟨hσ, rfl⟩⟩))
        · exact hpy_step v hv hσ hwc
      · obtain ⟨_, rfl⟩ := right_ap hwc
        exact Or.inl ⟨v, rfl⟩
    · obtain ⟨hv, rfl | rfl⟩ := left_bp huc
      · exfalso
        exact huc.not_mem_right
          (roundSet_subset_cumB (r := 1) (t := 4) (by decide) (by decide)
            (Or.inl ⟨v, hv, Or.inl ⟨hσv, rfl⟩⟩))
      · exact hpy_step v hv hσv hwc
    · rcases hug with rfl | rfl | rfl | rfl
      · have hqv_mem : ClauseGadgetLetter.qv j k ∈ cumB φ σ 4 :=
          roundSet_subset_cumB (r := 2) (t := 4) (by decide) (by decide)
            ⟨j, k, hj, Or.inr ⟨hlt, rfl⟩⟩
        obtain ⟨_, rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, hpv_in, _⟩⟩ := left_gv huc
        · exact han_step j k hj hpol hlt hwc
        · have hpol_cl : (clauseLitAt φ[j] k).2 = true := by rwa [← litAt_eq hj k]
          have hpv : conflictVarSlot (clauseLitAt φ[j] k) = .py (clauseLitAt φ[j] k).1 :=
            conflictVarSlot_of_true hpol_cl
          rw [hpv] at huc hwc
          have hσ_true : σ (clauseLitAt φ[j] k).1 = true := by
            have hev : Literal.eval σ (clauseLitAt φ[j] k) = true := by
              simpa [litTrue, litAt_eq hj k] using hlt
            rcases hcl : clauseLitAt φ[j] k with ⟨v₀, b₀⟩
            rw [hcl] at hpol_cl hev
            simp only at hpol_cl
            subst hpol_cl
            simpa using hev
          rcases right_py hwc with ⟨_, rfl | rfl⟩ | ⟨j', hj', k', hlit', rfl⟩
          · exact Or.inr (Or.inl ⟨_, hσ_true, rfl⟩)
          · exact Or.inl ⟨_, rfl⟩
          · have hla' : litAt φ j' k' = ((clauseLitAt φ[j] k).1, true) :=
              (litAt_eq hj' k').trans hlit'
            have hlt' : litTrue φ σ j' k' = true := by simp [litTrue, hla', hσ_true]
            exact Or.inr (Or.inr ⟨j', k', hj', by simp [hla'], hlt', Or.inl rfl⟩)
        · exact False.elim (huc.not_mem_right hqv_mem)
        · exfalso
          have hf := (cumB10_guard_gv_exclusive h3 (σ := σ) hj k).1.mp
            (cumB_mono (by decide) hpv_in)
          rw [hlt] at hf; cases hf
      · have horig_mem : ClauseGadgetLetter.orig j k ∈ cumB φ σ 4 :=
          roundSet_subset_cumB (r := 1) (t := 4) (by decide) (by decide)
            (orig_mem_roundSet1_iff.mpr ⟨hj, hlt⟩)
        obtain ⟨_, rfl | ⟨_, ho⟩ | ⟨rfl, _⟩ | ⟨_, _, hqo⟩⟩ := left_go huc
        · exact han_step j k hj hpol hlt hwc
        · exact False.elim (ho horig_mem)
        · obtain ⟨_, ⟨_, ho⟩ | ⟨rfl, _⟩⟩ := right_qo hwc
          · exact False.elim (ho horig_mem)
          · exact Or.inr (Or.inr ⟨j, k, hj, hpol, hlt, Or.inr (Or.inl rfl)⟩)
        · exfalso
          have hf := (cumB10_guard_go_exclusive (σ := σ) hj k).2.mp (cumB_mono (by decide) hqo)
          rw [hlt] at hf; cases hf
      · obtain ⟨_, rfl⟩ := left_bn_cn (Or.inl rfl) huc
        exact han_step j k hj hpol hlt hwc
      · obtain ⟨_, rfl⟩ := left_bn_cn (Or.inr rfl) huc
        exact han_step j k hj hpol hlt hwc
  refine isFreeSet_of_closed_left_region (S := S) (sep_not_mem_cumB φ σ 4) (roundSet_nonSep φ σ 5)
    ?_ ?_ ?_
  · rintro _ ⟨v, _, rfl⟩
    refine ⟨rfl, ?_⟩
    rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h | h | h | h⟩) <;> simp at h
  · intro u hu c w huc hwc
    exact ⟨hwc.1, fun hwT ↦ hu.2 (hT_closed w hwT c u hwc huc)⟩
  · rintro u hu _ ⟨v, _, rfl⟩ huy
    obtain ⟨_, rfl⟩ := right_ap huy
    exact hu.2 (Or.inl ⟨v, rfl⟩)

private theorem freeSet_round6 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 5) (clauseGadgetPattern φ)) (roundSet φ σ 6) := by
  refine isFreeSet_of_no_right (sep_not_mem_cumB φ σ 5) (roundSet_nonSep φ σ 6) ?_
  intro y hy b hby
  rcases hy with ⟨v, hv, hbc⟩
  obtain ⟨_, rfl⟩ := right_bp_cp hbc hby
  exact hby.not_mem_left
    (roundSet_subset_cumB (r := 5) (t := 5) (by decide) (Nat.le_refl _) ⟨v, hv, rfl⟩)

private theorem freeSet_round7 {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3)
    {σ : ℕ → Bool} (hσ : φ.eval σ = true) :
    IsFreeSet (deleteLetters (cumB φ σ 6) (clauseGadgetPattern φ)) (roundSet φ σ 7) := by
  let T : Set ClauseGadgetLetter :=
    {u | (∃ j, u = .do_ j) ∨
         (∃ j < φ.length, litTrue φ σ j 2 = false ∧ (u = .co j ∨ u = .go j 2)) ∨
         (∃ j < φ.length, litTrue φ σ j 2 = false ∧ litTrue φ σ j 1 = false ∧
            (u = .bo j ∨ u = .go j 1))}
  let S : Set ClauseGadgetLetter := {u | u.isSep = false ∧ u ∉ T}
  have hclause_some_true : ∀ j < φ.length,
      litTrue φ σ j 0 = true ∨ litTrue φ σ j 1 = true ∨ litTrue φ σ j 2 = true := by
    intro j hj
    have hcl_mem : φ[j] ∈ φ := List.getElem_mem hj
    have hcl_ev : Clause.eval σ φ[j] = true := (CNF.eval_eq_true_iff σ φ).mp hσ φ[j] hcl_mem
    obtain ⟨l, hl_mem, hl_ev⟩ := (Clause.eval_eq_true_iff σ φ[j]).mp hcl_ev
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hl_mem
    have hlen : φ[j].length = 3 := h3 φ[j] hcl_mem
    have hidx3 : idx = 0 ∨ idx = 1 ∨ idx = 2 := by omega
    rcases hidx3 with rfl | rfl | rfl
    · left
      have heq := clauseLitAt_eq_getElem hlen 0
      simp [litTrue, litAt_eq hj 0, heq, hl_ev]
    · right; left
      have heq := clauseLitAt_eq_getElem hlen 1
      simp [litTrue, litAt_eq hj 1, heq, hl_ev]
    · right; right
      have heq := clauseLitAt_eq_getElem hlen 2
      simp [litTrue, litAt_eq hj 2, heq, hl_ev]
  have horig_not_true : ∀ j < φ.length, ∀ k : Fin 3,
      ClauseGadgetLetter.orig j k ∉ cumB φ σ 6 → litTrue φ σ j k = false := by
    intro j hj k hno
    cases hlt : litTrue φ σ j k
    · rfl
    · exfalso
      exact hno (roundSet_subset_cumB (r := 1) (t := 6) (by decide) (by decide)
        (orig_mem_roundSet1_iff.mpr ⟨hj, hlt⟩))
  have hT_closed : ∀ u ∈ T, ∀ c w,
      GadgetBlockPair φ (cumB φ σ 6) u c → GadgetBlockPair φ (cumB φ σ 6) w c → w ∈ T := by
    intro u hu c w huc hwc
    rcases hu with ⟨j, rfl⟩ | ⟨j, hj, hf2, rfl | rfl⟩ | ⟨j, hj, hf2, hf1, rfl | rfl⟩
    · obtain ⟨hj, rfl | rfl⟩ := left_do huc
      · have hf2 : litTrue φ σ j 2 = false := horig_not_true j hj 2 huc.not_mem_right
        obtain ⟨_, ⟨hk, _⟩ | ⟨hk, _⟩ | ⟨_, rfl | rfl⟩ | rfl⟩ := right_orig hwc
        · cases hk
        · cases hk
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inl rfl⟩)
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inr rfl⟩)
      · obtain ⟨_, rfl⟩ := right_ao hwc
        exact Or.inl ⟨j, rfl⟩
    · obtain ⟨_, rfl | rfl⟩ := left_co huc
      · have hf1 : litTrue φ σ j 1 = false := horig_not_true j hj 1 huc.not_mem_right
        obtain ⟨_, ⟨hk, _⟩ | ⟨_, rfl | rfl⟩ | ⟨hk, _⟩ | rfl⟩ := right_orig hwc
        · cases hk
        · exact Or.inr (Or.inr ⟨j, hj, hf2, hf1, Or.inl rfl⟩)
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inl rfl⟩)
        · cases hk
        · exact Or.inr (Or.inr ⟨j, hj, hf2, hf1, Or.inr rfl⟩)
      · obtain ⟨_, ⟨hk, _⟩ | ⟨hk, _⟩ | ⟨_, rfl | rfl⟩ | rfl⟩ := right_orig hwc
        · cases hk
        · cases hk
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inl rfl⟩)
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inr rfl⟩)
    · have hqo2 : ClauseGadgetLetter.qo j 2 ∈ cumB φ σ 6 :=
        roundSet_subset_cumB (r := 2) (t := 6) (by decide) (by decide) ⟨j, 2, hj, Or.inl ⟨hf2, rfl⟩⟩
      have han2 : ClauseGadgetLetter.an j 2 ∈ cumB φ σ 6 :=
        roundSet_subset_cumB (r := 3) (t := 6) (by decide) (by decide) ⟨j, 2, hj, hf2, rfl⟩
      obtain ⟨_, rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, ho2, _⟩⟩ := left_go huc
      · exact False.elim (huc.not_mem_right han2)
      · obtain ⟨_, ⟨hk, _⟩ | ⟨hk, _⟩ | ⟨_, rfl | rfl⟩ | rfl⟩ := right_orig hwc
        · cases hk
        · cases hk
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inl rfl⟩)
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inr rfl⟩)
      · exact False.elim (huc.not_mem_right hqo2)
      · have := (cumB10_guard_go_exclusive (σ := σ) hj 2).1.mp (cumB_mono (by decide) ho2)
        rw [hf2] at this; cases this
    · obtain ⟨_, rfl | rfl⟩ := left_bo huc
      · exfalso
        have hf0 : litTrue φ σ j 0 = false := horig_not_true j hj 0 huc.not_mem_right
        rcases hclause_some_true j hj with h0 | h1 | h2
        · rw [hf0] at h0; cases h0
        · rw [hf1] at h1; cases h1
        · rw [hf2] at h2; cases h2
      · obtain ⟨_, ⟨hk, _⟩ | ⟨_, rfl | rfl⟩ | ⟨hk, _⟩ | rfl⟩ := right_orig hwc
        · cases hk
        · exact Or.inr (Or.inr ⟨j, hj, hf2, hf1, Or.inl rfl⟩)
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inl rfl⟩)
        · cases hk
        · exact Or.inr (Or.inr ⟨j, hj, hf2, hf1, Or.inr rfl⟩)
    · have hqo1 : ClauseGadgetLetter.qo j 1 ∈ cumB φ σ 6 :=
        roundSet_subset_cumB (r := 2) (t := 6) (by decide) (by decide) ⟨j, 1, hj, Or.inl ⟨hf1, rfl⟩⟩
      have han1 : ClauseGadgetLetter.an j 1 ∈ cumB φ σ 6 :=
        roundSet_subset_cumB (r := 3) (t := 6) (by decide) (by decide) ⟨j, 1, hj, hf1, rfl⟩
      obtain ⟨_, rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, ho1, _⟩⟩ := left_go huc
      · exact False.elim (huc.not_mem_right han1)
      · obtain ⟨_, ⟨hk, _⟩ | ⟨_, rfl | rfl⟩ | ⟨hk, _⟩ | rfl⟩ := right_orig hwc
        · cases hk
        · exact Or.inr (Or.inr ⟨j, hj, hf2, hf1, Or.inl rfl⟩)
        · exact Or.inr (Or.inl ⟨j, hj, hf2, Or.inl rfl⟩)
        · cases hk
        · exact Or.inr (Or.inr ⟨j, hj, hf2, hf1, Or.inr rfl⟩)
      · exact False.elim (huc.not_mem_right hqo1)
      · have := (cumB10_guard_go_exclusive (σ := σ) hj 1).1.mp (cumB_mono (by decide) ho1)
        rw [hf1] at this; cases this
  refine isFreeSet_of_closed_left_region (S := S) (sep_not_mem_cumB φ σ 6) (roundSet_nonSep φ σ 7)
    ?_ ?_ ?_
  · rintro _ ⟨j, _, rfl⟩
    refine ⟨rfl, ?_⟩
    rintro (⟨_, h⟩ | ⟨_, _, _, h | h⟩ | ⟨_, _, _, _, h | h⟩) <;> simp at h
  · intro u hu c w huc hwc
    exact ⟨hwc.1, fun hwT ↦ hu.2 (hT_closed w hwT c u hwc huc)⟩
  · rintro u hu _ ⟨j, _, rfl⟩ huy
    obtain ⟨_, rfl⟩ := right_ao huy
    exact hu.2 (Or.inl ⟨j, rfl⟩)

private theorem freeSet_round8 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 7) (clauseGadgetPattern φ)) (roundSet φ σ 8) := by
  refine isFreeSet_of_no_right (sep_not_mem_cumB φ σ 7) (roundSet_nonSep φ σ 8) ?_
  intro y hy b hby
  rcases hy with ⟨j, hj, hbcd⟩
  obtain ⟨_, rfl⟩ := right_bo_co_do hbcd hby
  exact hby.not_mem_left
    (roundSet_subset_cumB (r := 7) (t := 7) (by decide) (Nat.le_refl _) ⟨j, hj, rfl⟩)

private theorem freeSet_round9 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 8) (clauseGadgetPattern φ)) (roundSet φ σ 9) := by
  let S : Set ClauseGadgetLetter :=
    {u | ∃ (j : ℕ) (k : Fin 3), j < φ.length ∧ litTrue φ σ j k = true ∧
          (u = .an j k ∨ u = .qo j k)}
  refine isFreeSet_of_closed_left_region (S := S) (sep_not_mem_cumB φ σ 8) (roundSet_nonSep φ σ 9)
    ?_ ?_ ?_
  · rintro _ ⟨j, k, hj, hlt, rfl⟩
    exact ⟨j, k, hj, hlt, Or.inl rfl⟩
  · intro u hu c w huc hwc
    rcases hu with ⟨j, k, hj, hlt, rfl | rfl⟩
    · obtain ⟨_, rfl⟩ := left_an huc
      obtain ⟨_, rfl | rfl⟩ := right_bn hwc
      · exact ⟨j, k, hj, hlt, Or.inl rfl⟩
      · exact ⟨j, k, hj, hlt, Or.inr rfl⟩
    · obtain ⟨_, rfl | rfl | rfl⟩ := left_qo huc
      · obtain ⟨_, rfl | rfl⟩ := right_bn hwc
        · exact ⟨j, k, hj, hlt, Or.inl rfl⟩
        · exact ⟨j, k, hj, hlt, Or.inr rfl⟩
      · obtain ⟨_, rfl | rfl⟩ := right_cn hwc
        · exact ⟨j, k, hj, hlt, Or.inr rfl⟩
        · exfalso
          exact hwc.not_mem_left
            (roundSet_subset_cumB (r := 2) (t := 8) (by decide) (by decide)
              ⟨j, k, hj, Or.inr ⟨hlt, rfl⟩⟩)
      · obtain ⟨_, rfl | rfl | ⟨_, ho⟩ | ⟨_, _, hqo⟩⟩ := right_go hwc
        · exfalso
          exact hwc.not_mem_left
            (roundSet_subset_cumB (r := 7) (t := 8) (by decide) (by decide) ⟨j, hj, rfl⟩)
        · exact ⟨j, k, hj, hlt, Or.inr rfl⟩
        · exfalso
          exact ho (roundSet_subset_cumB (r := 1) (t := 8) (by decide) (by decide)
            (orig_mem_roundSet1_iff.mpr ⟨hj, hlt⟩))
        · exfalso
          have hf := (cumB10_guard_go_exclusive (σ := σ) hj k).2.mp (cumB_mono (by decide) hqo)
          rw [hlt] at hf; cases hf
  · rintro u ⟨j, k, _, _, rfl | rfl⟩ _ ⟨j', k', _, _, rfl⟩ huy
    · obtain ⟨_, h⟩ := left_an huy; simp at h
    · obtain ⟨_, h | h | h⟩ := left_qo huy <;> simp at h

private theorem freeSet_round10 (φ : CNF ℕ) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 9) (clauseGadgetPattern φ)) (roundSet φ σ 10) := by
  refine isFreeSet_of_no_left (sep_not_mem_cumB φ σ 9) (roundSet_nonSep φ σ 10) ?_
  intro x hx c hxc
  rcases hx with ⟨j, k, hj, hlt, hbc⟩
  obtain ⟨_, rfl⟩ := left_bn_cn hbc hxc
  exact hxc.not_mem_right
    (roundSet_subset_cumB (r := 9) (t := 9) (by decide) (Nat.le_refl _) ⟨j, k, hj, hlt, rfl⟩)

private theorem gadgetBlockPair_cumB10_bipartite {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3)
    {σ : ℕ → Bool} {x y : ClauseGadgetLetter} (h : GadgetBlockPair φ (cumB φ σ 10) x y) :
    x.isGuard ≠ y.isGuard := by
  obtain ⟨hxB, hyB, hcases⟩ := gadgetBlockPair_decomp h
  have hao_in : ∀ j < φ.length, ClauseGadgetLetter.ao j ∈ cumB φ σ 10 := fun j hj ↦
    roundSet_subset_cumB (r := 7) (t := 10) (by decide) (by decide) ⟨j, hj, rfl⟩
  have hbo_in : ∀ j < φ.length, ClauseGadgetLetter.bo j ∈ cumB φ σ 10 := fun j hj ↦
    roundSet_subset_cumB (r := 8) (t := 10) (by decide) (by decide) ⟨j, hj, Or.inl rfl⟩
  have hco_in : ∀ j < φ.length, ClauseGadgetLetter.co j ∈ cumB φ σ 10 := fun j hj ↦
    roundSet_subset_cumB (r := 8) (t := 10) (by decide) (by decide) ⟨j, hj, Or.inr (Or.inl rfl)⟩
  have hdo_in : ∀ j < φ.length, ClauseGadgetLetter.do_ j ∈ cumB φ σ 10 := fun j hj ↦
    roundSet_subset_cumB (r := 8) (t := 10) (by decide) (by decide) ⟨j, hj, Or.inr (Or.inr rfl)⟩
  have hap_in : ∀ v ∈ φ.distinctVars, ClauseGadgetLetter.ap v ∈ cumB φ σ 10 := fun v hv ↦
    roundSet_subset_cumB (r := 5) (t := 10) (by decide) (by decide) ⟨v, hv, rfl⟩
  have hbp_in : ∀ v ∈ φ.distinctVars, ClauseGadgetLetter.bp v ∈ cumB φ σ 10 := fun v hv ↦
    roundSet_subset_cumB (r := 6) (t := 10) (by decide) (by decide) ⟨v, hv, Or.inl rfl⟩
  have hcp_in : ∀ v ∈ φ.distinctVars, ClauseGadgetLetter.cp v ∈ cumB φ σ 10 := fun v hv ↦
    roundSet_subset_cumB (r := 6) (t := 10) (by decide) (by decide) ⟨v, hv, Or.inr rfl⟩
  have han_in : ∀ j < φ.length, ∀ k : Fin 3, ClauseGadgetLetter.an j k ∈ cumB φ σ 10 := by
    intro j hj k
    cases hlt : litTrue φ σ j k
    · exact roundSet_subset_cumB (r := 3) (t := 10) (by decide) (by decide) ⟨j, k, hj, hlt, rfl⟩
    · exact roundSet_subset_cumB (r := 9) (t := 10) (by decide) (by decide) ⟨j, k, hj, hlt, rfl⟩
  have hbn_in : ∀ j < φ.length, ∀ k : Fin 3, ClauseGadgetLetter.bn j k ∈ cumB φ σ 10 := by
    intro j hj k
    cases hlt : litTrue φ σ j k
    · exact roundSet_subset_cumB (r := 4) (t := 10) (by decide) (by decide)
        ⟨j, k, hj, hlt, Or.inl rfl⟩
    · exact roundSet_subset_cumB (r := 10) (t := 10) (by decide) (by decide)
        ⟨j, k, hj, hlt, Or.inl rfl⟩
  have hcn_in : ∀ j < φ.length, ∀ k : Fin 3, ClauseGadgetLetter.cn j k ∈ cumB φ σ 10 := by
    intro j hj k
    cases hlt : litTrue φ σ j k
    · exact roundSet_subset_cumB (r := 4) (t := 10) (by decide) (by decide)
        ⟨j, k, hj, hlt, Or.inr rfl⟩
    · exact roundSet_subset_cumB (r := 10) (t := 10) (by decide) (by decide)
        ⟨j, k, hj, hlt, Or.inr rfl⟩
  rcases hcases with ⟨j, hj, hp⟩ | ⟨v, hv, hp⟩ | ⟨j, hj, k, hp⟩ | ⟨j, hj, k, hg⟩ |
      ⟨j, hj, k, hg⟩
  · rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
        ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact False.elim (hxB (hao_in j hj))
    · exact False.elim (hxB (hbo_in j hj))
    · exact False.elim (hxB (hbo_in j hj))
    · exact False.elim (hxB (hco_in j hj))
    · exact False.elim (hxB (hco_in j hj))
    · exact False.elim (hxB (hdo_in j hj))
    · exact False.elim (hxB (hdo_in j hj))
    · exact False.elim (hxB (hao_in j hj))
    · exact False.elim (hxB (hao_in j hj))
    · exact False.elim (hxB (hao_in j hj))
  · rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact False.elim (hxB (hap_in v hv))
    · exact False.elim (hxB (hbp_in v hv))
    · exact False.elim (hxB (hbp_in v hv))
    · exact False.elim (hxB (hcp_in v hv))
    · exact False.elim (hxB (hcp_in v hv))
    · exact False.elim (hxB (hap_in v hv))
    · exact False.elim (hxB (hap_in v hv))
  · rcases hp with ⟨rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
        ⟨rfl, _⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact False.elim (hxB (han_in j hj k))
    · exact False.elim (hyB (hbn_in j hj k))
    · exact False.elim (hyB (hcn_in j hj k))
    · exact False.elim (hyB (hcn_in j hj k))
    · exact False.elim (hyB (han_in j hj k))
    · exact False.elim (hyB (han_in j hj k))
    · exact False.elim (hyB (han_in j hj k))
    · exact False.elim (hxB (hao_in j hj))
    · exact False.elim (hyB (han_in j hj k))
    · exact False.elim (hxB (hap_in _ (lit_var_mem_distinctVars h3 hj k)))
    · exact False.elim (hyB (han_in j hj k))
  · obtain ⟨horig_iff, hqo_iff⟩ := cumB10_guard_go_exclusive (σ := σ) hj k
    rw [infix_pair_guard4] at hg
    rcases hg with ⟨_, _, hp, hq⟩ | ⟨_, ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ |
        ⟨rfl, rfl, _⟩ | ⟨_, _, hp, hq⟩⟩
    · exfalso
      cases hlt : litTrue φ σ j k
      · exact hq (hqo_iff.mpr hlt)
      · exact hp (horig_iff.mpr hlt)
    · simp
    · simp
    · simp
    · simp
    · exfalso
      have h1 := horig_iff.mp hp
      have h2 := hqo_iff.mp hq
      rw [h1] at h2; cases h2
  · obtain ⟨hpvar_iff, hqv_iff⟩ := cumB10_guard_gv_exclusive h3 (σ := σ) hj k
    have hpv_ng : (conflictVarSlot (clauseLitAt φ[j] k)).isGuard = false := by
      rcases conflictVarSlot_cases (clauseLitAt φ[j] k) with ⟨_, hpv⟩ | ⟨_, hpv⟩ <;>
        simp [hpv]
    rw [infix_pair_guard4] at hg
    rcases hg with ⟨_, _, hp, hq⟩ | ⟨_, ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ |
        ⟨rfl, rfl, _⟩ | ⟨_, _, hp, hq⟩⟩
    · exfalso
      cases hlt : litTrue φ σ j k
      · exact hp (hpvar_iff.mpr hlt)
      · exact hq (hqv_iff.mpr hlt)
    · rw [hpv_ng]; simp
    · simp
    · simp
    · rw [hpv_ng]; simp
    · exfalso
      have h1 := hpvar_iff.mp hp
      have h2 := hqv_iff.mp hq
      rw [h1] at h2; cases h2

private theorem freeSet_round11 {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 10) (clauseGadgetPattern φ)) (roundSet φ σ 11) := by
  refine isFreeSet_of_closed_left_region (sep_not_mem_cumB φ σ 10) (roundSet_nonSep φ σ 11)
    Set.Subset.rfl ?_ ?_
  · intro u hu c w huc hwc
    have h1 := gadgetBlockPair_cumB10_bipartite h3 huc
    have h2 := gadgetBlockPair_cumB10_bipartite h3 hwc
    have hu_g : u.isGuard = true := hu
    have hc_ng : c.isGuard = false := by cases hc : c.isGuard <;> simp_all
    cases hw : w.isGuard
    · rw [hw, hc_ng] at h2; exact absurd rfl h2
    · exact hw
  · intro u hu y hy huy
    have h1 := gadgetBlockPair_cumB10_bipartite h3 huy
    have hu_g : u.isGuard = true := hu
    have hy_g : y.isGuard = true := hy
    exact h1 (hu_g.trans hy_g.symm)

private theorem freeSet_round12 {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) (σ : ℕ → Bool) :
    IsFreeSet (deleteLetters (cumB φ σ 11) (clauseGadgetPattern φ)) (roundSet φ σ 12) := by
  refine isFreeSet_of_no_left (sep_not_mem_cumB φ σ 11) (roundSet_nonSep φ σ 12) ?_
  intro x _ c hxc
  have hsub : cumB φ σ 10 ⊆ cumB φ σ 11 := cumB_mono (by decide)
  have hx11 := hxc.not_mem_left
  have hc11 := hxc.not_mem_right
  have hx := hxc.1
  have hc := hxc.2.1
  have hx_ng : x.isGuard = false := by
    cases hxg : x.isGuard
    · rfl
    · exact False.elim (hx11 (Or.inr hxg))
  have hc_ng : c.isGuard = false := by
    cases hcg : c.isGuard
    · rfl
    · exact False.elim (hc11 (Or.inr hcg))
  rcases (gadgetBlockPair_decomp hxc).2.2 with ⟨j, hj, hp⟩ | ⟨v, hv, hp⟩ | ⟨j, hj, k, hp⟩ |
      ⟨j, hj, k, hg⟩ | ⟨j, hj, k, hg⟩
  · have hp10 : GadgetBlockPair φ (cumB φ σ 10) x c := by
      refine ⟨hx, hc, [x, c], mem_clauseGadgetBlocks_iff.mpr (Or.inl ⟨j, hj, ?_⟩),
        infix_pair_two_gadget.mpr ⟨rfl, rfl, fun h ↦ hx11 (hsub h), fun h ↦ hc11 (hsub h)⟩⟩
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [mem_origClauseBlocks_iff]
    exact gadgetBlockPair_cumB10_bipartite h3 hp10 (hx_ng.trans hc_ng.symm)
  · have hp10 : GadgetBlockPair φ (cumB φ σ 10) x c := by
      refine ⟨hx, hc, [x, c], mem_clauseGadgetBlocks_iff.mpr (Or.inr (Or.inl ⟨v, hv, ?_⟩)),
        infix_pair_two_gadget.mpr ⟨rfl, rfl, fun h ↦ hx11 (hsub h), fun h ↦ hc11 (hsub h)⟩⟩
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [mem_varPosBlocks_iff]
    exact gadgetBlockPair_cumB10_bipartite h3 hp10 (hx_ng.trans hc_ng.symm)
  · have hp10 : GadgetBlockPair φ (cumB φ σ 10) x c := by
      refine ⟨hx, hc, [x, c], mem_clauseGadgetBlocks_iff.mpr (Or.inr (Or.inr ⟨j, hj, k, ?_⟩)),
        infix_pair_two_gadget.mpr ⟨rfl, rfl, fun h ↦ hx11 (hsub h), fun h ↦ hc11 (hsub h)⟩⟩
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [mem_occTapBlocks_iff]
    exact gadgetBlockPair_cumB10_bipartite h3 hp10 (hx_ng.trans hc_ng.symm)
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨_, _, hp, hq⟩ | ⟨hgB, _⟩
    · obtain ⟨horig_iff, hqo_iff⟩ := cumB10_guard_go_exclusive (σ := σ) hj k
      cases hlt : litTrue φ σ j k
      · exact hq (hsub (hqo_iff.mpr hlt))
      · exact hp (hsub (horig_iff.mpr hlt))
    · exact hgB (Or.inr rfl)
  · rw [infix_pair_guard4] at hg
    rcases hg with ⟨_, _, hp, hq⟩ | ⟨hgB, _⟩
    · obtain ⟨hpvar_iff, hqv_iff⟩ := cumB10_guard_gv_exclusive h3 (σ := σ) hj k
      cases hlt : litTrue φ σ j k
      · exact hp (hsub (hpvar_iff.mpr hlt))
      · exact hq (hsub (hqv_iff.mpr hlt))
    · exact hgB (Or.inr rfl)

/-- If a `3`-CNF formula `φ` is satisfiable, then `clauseGadgetPattern φ` is
unavoidable. -/
theorem satisfiable_imp_isUnavoidable_clauseGadgetPattern {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length = 3) (hsat : φ.Satisfiable) :
    IsUnavoidable (clauseGadgetPattern φ) := by
  rcases hsat with ⟨σ, hσ⟩
  have h12 : IsUnavoidable (deleteLetters (cumB φ σ 12) (clauseGadgetPattern φ)) :=
    isUnavoidable_deleteLetters_of_contains_nonSep fun _ _ hns ↦ Or.inr hns
  have hstep : ∀ t : ℕ,
      IsFreeSet (deleteLetters (cumB φ σ t) (clauseGadgetPattern φ)) (roundSet φ σ (t + 1)) →
      IsUnavoidable (deleteLetters (cumB φ σ (t + 1)) (clauseGadgetPattern φ)) →
      IsUnavoidable (deleteLetters (cumB φ σ t) (clauseGadgetPattern φ)) := by
    intro t hfs hun
    exact hfs.isUnavoidable_of_deleteLetters
      (by simpa only [CslibFrontier.Word.deleteLetters_deleteLetters, cumB] using hun)
  have h11 := hstep 11 (freeSet_round12 h3 σ) h12
  have h10 := hstep 10 (freeSet_round11 h3 σ) h11
  have h9 := hstep 9 (freeSet_round10 φ σ) h10
  have h8 := hstep 8 (freeSet_round9 φ σ) h9
  have h7 := hstep 7 (freeSet_round8 φ σ) h8
  have h6 := hstep 6 (freeSet_round7 h3 hσ) h7
  have h5 := hstep 5 (freeSet_round6 φ σ) h6
  have h4 := hstep 4 (freeSet_round5 h3 σ) h5
  have h3' := hstep 3 (freeSet_round4 φ σ) h4
  have h2 := hstep 2 (freeSet_round3 φ σ) h3'
  have h1 := hstep 1 (freeSet_round2 h3 σ) h2
  have h0 := hstep 0 (freeSet_round1 φ σ) h1
  have hempty : deleteLetters (cumB φ σ 0) (clauseGadgetPattern φ) = clauseGadgetPattern φ :=
    deleteLetters_eq_self fun _ _ h ↦ h
  rwa [hempty] at h0

end CslibFrontier.Complexity

end
