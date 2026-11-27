/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.RestrictedThreeExactCover

import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# NP-Completeness of Restricted Exact Cover by 3-Sets (`RX3C`)

This module completes the self-contained polynomial-time reduction from
`Cslib.Complexity.PositiveOneInExactThreeSATThree` to `RX3C`,
proving `toRX3C_mem_iff`, `RX3C_npHard`, and `RX3C_npComplete`.
-/

public section

namespace Cslib.Complexity

open Finset Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

section RX3CHardness

/-- Local set indices selected inside a variable gadget when `v` has truth value `tv`. -/
private def varGadgetSelect (φ : CNF ℕ) (v : ℕ) (tv : Bool) : Finset ℕ :=
  let d := (clauseIndices φ v).length
  if d = 1 then if tv then {0, 1, 2} else {3, 4}
  else if d = 2 then if tv then {0, 1, 2, 4} else {3, 4}
  else if tv then {0, 1, 2, 3, 4, 5} else {6, 7, 8}

/-- Starting index of gadget `i`'s sets inside `(toRX3C φ).sets`. -/
private def setOffset (φ : CNF ℕ) (V : List ℕ) (i : ℕ) : ℕ :=
  ((V.take i).map fun v ↦ (varGadgetSets φ v 0).length).sum

private theorem varGadgetSets_length_indep (φ : CNF ℕ) (v b₁ b₂ : ℕ) :
    (varGadgetSets φ v b₁).length = (varGadgetSets φ v b₂).length := by
  unfold varGadgetSets; dsimp only; split_ifs <;> rfl

private theorem setOffset_succ (φ : CNF ℕ) (V : List ℕ) (i : ℕ) (hi : i < V.length) :
    setOffset φ V (i + 1) = setOffset φ V i + (varGadgetSets φ (V[i]'hi) 0).length := by
  unfold setOffset
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]

private theorem setOffset_mono (φ : CNF ℕ) (V : List ℕ) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ V.length) :
    setOffset φ V i ≤ setOffset φ V j := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0; exact le_rfl
  | succ k ih =>
    by_cases h : i ≤ k
    · exact (ih h (by omega)).trans (by rw [setOffset_succ φ V k (by omega)]; omega)
    · have hik : i = k + 1 := by omega
      subst hik; exact le_rfl

private theorem setOffset_add_le (φ : CNF ℕ) (V : List ℕ) {i j : ℕ} (hij : i < j)
    (hj : j ≤ V.length) :
    setOffset φ V i + (varGadgetSets φ (V[i]'(by omega)) 0).length ≤ setOffset φ V j := by
  rw [← setOffset_succ φ V i (by omega)]
  exact setOffset_mono φ V (by omega) hj

private theorem flatMap_range_getElem (φ : CNF ℕ) (V : List ℕ) :
    ∀ n (hn : n ≤ V.length),
      ((List.range n).flatMap fun i ↦
        varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)).length = setOffset φ V n ∧
      ∀ i (hi : i < n) k (hk : k < (varGadgetSets φ (V[i]'(by omega)) 0).length),
        (((List.range n).flatMap fun j ↦
          varGadgetSets φ (V.getD j 0) (varDummyBase φ V j))[setOffset φ V i + k]'(by
            have h1 := setOffset_add_le φ V hi hn
            have hlen_eq : ((List.range n).flatMap fun j ↦
                varGadgetSets φ (V.getD j 0) (varDummyBase φ V j)).length = setOffset φ V n := by
              clear h1 hk hi
              induction n with
              | zero => simp [setOffset]
              | succ m ihm =>
                rw [List.range_succ, List.flatMap_append, List.length_append,
                  List.flatMap_singleton, setOffset_succ φ V m (by omega),
                  ihm (by omega), List.getD_eq_getElem _ _ (by omega),
                  varGadgetSets_length_indep φ _ _ 0]
            omega)) =
          (varGadgetSets φ (V[i]'(by omega)) (varDummyBase φ V i))[k]'(by
            rw [varGadgetSets_length_indep φ _ _ 0]; exact hk) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨by simp [setOffset], fun i hi _ _ ↦ (Nat.not_lt_zero i hi).elim⟩
  | succ m ih =>
    intro hm
    obtain ⟨ihlen, ihget⟩ := ih (by omega)
    have hlen : ((List.range (m + 1)).flatMap fun j ↦
        varGadgetSets φ (V.getD j 0) (varDummyBase φ V j)).length = setOffset φ V (m + 1) := by
      rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton,
        setOffset_succ φ V m (by omega), ihlen, List.getD_eq_getElem _ _ (by omega),
        varGadgetSets_length_indep φ _ _ 0]
    refine ⟨hlen, fun i hi k hk ↦ ?_⟩
    have hfl : ((List.range (m + 1)).flatMap fun j ↦
        varGadgetSets φ (V.getD j 0) (varDummyBase φ V j)) =
        ((List.range m).flatMap fun j ↦
          varGadgetSets φ (V.getD j 0) (varDummyBase φ V j)) ++
        varGadgetSets φ (V.getD m 0) (varDummyBase φ V m) := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp only [hfl]
    by_cases him : i < m
    · have hlt_l : setOffset φ V i + k <
          ((List.range m).flatMap fun j ↦
            varGadgetSets φ (V.getD j 0) (varDummyBase φ V j)).length := by
        rw [ihlen]; have := setOffset_add_le φ V him (by omega); omega
      rw [List.getElem_append_left hlt_l]
      exact ihget i him k hk
    · have hieq : i = m := by omega
      subst hieq
      have hge_l : ((List.range i).flatMap fun j ↦
          varGadgetSets φ (V.getD j 0) (varDummyBase φ V j)).length ≤ setOffset φ V i + k := by
        rw [ihlen]; omega
      rw [List.getElem_append_right hge_l]
      have hVget : V.getD i 0 = V[i]'(by omega) := List.getD_eq_getElem _ _ (by omega)
      simp only [ihlen, Nat.add_sub_cancel_left, hVget]

private theorem filter_card_eq_one_of_mem {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p]
    {k : ℕ} (hk : k ∈ s) (hp : p k) (hother : ∀ j ∈ s, j ≠ k → ¬ p j) :
    (s.filter p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hjs, hpj⟩ ↦ by_contra fun hne ↦ hother j hjs hne hpj, fun h ↦ h ▸ ⟨hk, hp⟩⟩

private theorem varGadgetSelect_mem_card_dummy (φ : CNF ℕ) (v b t : ℕ) (tv : Bool)
    (hb : 3 * φ.length ≤ b) (h1 : 1 ≤ (clauseIndices φ v).length)
    (h3 : (clauseIndices φ v).length ≤ 3) (hge : b ≤ t) (hlt : t < b + varDummyCount φ v) :
    ((varGadgetSelect φ v tv).filter fun k ↦
      t ∈ tripleFinset ((varGadgetSets φ v b).getD k (0, 0, 0))).card = 1 := by
  unfold varGadgetSelect varGadgetSets
  unfold varDummyCount at hlt
  have hcases : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hcases with h | h | h
  · dsimp only at hlt ⊢
    simp only [h, show (1 : ℕ) ≠ 3 by omega, ↓reduceIte] at hlt ⊢
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj1
    obtain ⟨d, hd, rfl⟩ : ∃ d < 6, t = b + d := ⟨t - b, by omega, by omega⟩
    cases tv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      interval_cases d
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
    · simp only [↓reduceIte]
      interval_cases d
      · refine filter_card_eq_one_of_mem (k := 0) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 1) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 2) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 0) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 1) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 2) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
  · dsimp only at hlt ⊢
    simp only [h, show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ 3 by omega, ↓reduceIte] at hlt ⊢
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj1
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj2
    obtain ⟨d, hd, rfl⟩ : ∃ d < 6, t = b + d := ⟨t - b, by omega, by omega⟩
    cases tv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      interval_cases d
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp_all [tripleFinset]
    · simp only [↓reduceIte]
      interval_cases d
      · refine filter_card_eq_one_of_mem (k := 0) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 1) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 2) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
  · dsimp only at hlt ⊢
    simp only [h, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte] at hlt ⊢
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj1
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj2
    have hj3 := clauseIndices_getD_lt φ v 2 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj3
    obtain ⟨d, hd, rfl⟩ : ∃ d < 9, t = b + d := ⟨t - b, by omega, by omega⟩
    cases tv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      interval_cases d
      · refine filter_card_eq_one_of_mem (k := 6) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 7) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 8) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 6) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 7) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 8) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 6) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 7) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
      · refine filter_card_eq_one_of_mem (k := 8) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp_all [tripleFinset]
    · simp only [↓reduceIte]
      interval_cases d
      · refine filter_card_eq_one_of_mem (k := 0) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 1) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 2) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 5) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 3) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 4) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega
      · refine filter_card_eq_one_of_mem (k := 5) (by decide)
          (by simp [tripleFinset]) fun k hk hne ↦ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega

private theorem varGadgetSelect_mem_card_clause (φ : CNF ℕ) (v b j r : ℕ) (tv : Bool)
    (hb : 3 * φ.length ≤ b) (h1 : 1 ≤ (clauseIndices φ v).length)
    (h3 : (clauseIndices φ v).length ≤ 3) (hj : j < φ.length) (hr : r < 3) :
    ((varGadgetSelect φ v tv).filter fun k ↦
      3 * j + r ∈ tripleFinset ((varGadgetSets φ v b).getD k (0, 0, 0))).card =
      if tv = true ∧ j ∈ clauseIndices φ v then 1 else 0 := by
  unfold varGadgetSelect varGadgetSets
  have hcases : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hcases with h | h | h
  · dsimp only
    simp only [h, ↓reduceIte]
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj1
    have hmem : j ∈ clauseIndices φ v ↔ j = (clauseIndices φ v).getD 0 0 := by
      rcases hl : clauseIndices φ v with _ | ⟨x, _ | _⟩ <;> simp_all
    simp only [hmem]
    cases tv
    · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [tripleFinset] <;> omega
    · simp only [true_and, ↓reduceIte]
      by_cases hjeq : j = (clauseIndices φ v).getD 0 0
      · simp only [hjeq, ↓reduceIte]
        interval_cases r
        · refine filter_card_eq_one_of_mem (k := 0) (by decide)
            (by simp [tripleFinset]) fun k hk hne ↦ ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
        · refine filter_card_eq_one_of_mem (k := 1) (by decide)
            (by simp [tripleFinset]) fun k hk hne ↦ ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
        · refine filter_card_eq_one_of_mem (k := 2) (by decide)
            (by simp [tripleFinset]) fun k hk hne ↦ ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · simp only [hjeq, ↓reduceIte]
        simp only [List.getD_eq_getElem?_getD] at hjeq
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
  · dsimp only
    simp only [h, ↓reduceIte, show (2 : ℕ) ≠ 1 by omega]
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj1 hj2 hne01
    have hmem : j ∈ clauseIndices φ v ↔
        j = (clauseIndices φ v).getD 0 0 ∨ j = (clauseIndices φ v).getD 1 0 := by
      rcases hl : clauseIndices φ v with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp_all
    simp only [hmem]
    cases tv
    · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [tripleFinset] <;> omega
    · simp only [true_and, ↓reduceIte]
      by_cases hjeq : j = (clauseIndices φ v).getD 0 0 ∨ j = (clauseIndices φ v).getD 1 0
      · simp only [hjeq, ↓reduceIte]
        rcases hjeq with hjeq | hjeq
        · rw [hjeq]
          interval_cases r
          · refine filter_card_eq_one_of_mem (k := 0) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 1) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 2) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
        · rw [hjeq]
          interval_cases r
          · refine filter_card_eq_one_of_mem (k := 0) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 1) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 2) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
      · simp only [hjeq, ↓reduceIte]
        simp only [List.getD_eq_getElem?_getD] at hjeq
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
  · dsimp only
    simp only [h, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega]
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    have hj3 := clauseIndices_getD_lt φ v 2 (by omega)
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    have hne02 := clauseIndices_getD_ne φ v 0 2 (by omega) (by omega) (by omega)
    have hne12 := clauseIndices_getD_ne φ v 1 2 (by omega) (by omega) (by omega)
    simp only [List.getD_eq_getElem?_getD] at hj1 hj2 hj3 hne01 hne02 hne12
    have hmem : j ∈ clauseIndices φ v ↔
        j = (clauseIndices φ v).getD 0 0 ∨ j = (clauseIndices φ v).getD 1 0 ∨
          j = (clauseIndices φ v).getD 2 0 := by
      rcases hl : clauseIndices φ v with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
    simp only [hmem]
    cases tv
    · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> simp [tripleFinset] <;> omega
    · simp only [true_and, ↓reduceIte]
      by_cases hjeq : j = (clauseIndices φ v).getD 0 0 ∨
          j = (clauseIndices φ v).getD 1 0 ∨ j = (clauseIndices φ v).getD 2 0
      · simp only [hjeq, ↓reduceIte]
        rcases hjeq with hjeq | hjeq | hjeq
        · rw [hjeq]
          interval_cases r
          · refine filter_card_eq_one_of_mem (k := 0) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 1) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 2) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
        · rw [hjeq]
          interval_cases r
          · refine filter_card_eq_one_of_mem (k := 0) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 1) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 2) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
        · rw [hjeq]
          interval_cases r
          · refine filter_card_eq_one_of_mem (k := 3) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 4) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
          · refine filter_card_eq_one_of_mem (k := 5) (by decide)
              (by simp [tripleFinset]) fun k hk hne ↦ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [tripleFinset] <;> omega
      · simp only [hjeq, ↓reduceIte]
        simp only [List.getD_eq_getElem?_getD] at hjeq
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [tripleFinset] <;> omega

/-- Equivalence of `PositiveOneInExactThreeSATThree` and `RX3C` under `toRX3C`. -/
theorem toRX3C_mem_iff (φ : CNF ℕ) :
    toRX3C φ ∈ RX3C ↔ φ ∈ PositiveOneInExactThreeSATThree := by
  classical
  by_cases hsyn : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · rw [PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck, and_iff_right hsyn]
    have hvalid := toRX3C_isValidRX3C φ hsyn
    obtain ⟨hex, hpos, hcnt⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hsyn
    have hpos' := (OneSAT.positiveCheck_iff φ).mp hpos
    unfold RX3C OneSAT
    simp only [Set.mem_ofPred_eq]
    rw [and_iff_right hvalid]
    have hto : toRX3C φ =
        ⟨3 * φ.length + (φ.distinctVars.map (varDummyCount φ)).sum,
          (List.range φ.distinctVars.length).flatMap fun i ↦
            varGadgetSets φ (φ.distinctVars.getD i 0) (varDummyBase φ φ.distinctVars i)⟩ := by
      simp [toRX3C, hsyn]
    rw [hto]
    set V := φ.distinctVars
    set numEl := 3 * φ.length + (V.map (varDummyCount φ)).sum
    set sets := (List.range V.length).flatMap fun i ↦
      varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)
    have hv_deg : ∀ i (hi : i < V.length),
        1 ≤ (clauseIndices φ (V[i]'hi)).length ∧ (clauseIndices φ (V[i]'hi)).length ≤ 3 := by
      intro i hi
      refine ⟨clauseIndices_length_pos_of_mem_distinctVars φ hex (List.getElem_mem hi), ?_⟩
      rw [clauseIndices_length_eq_count φ hex]; exact hcnt _
    obtain ⟨hsets_len, hsets_get⟩ := flatMap_range_getElem φ V V.length le_rfl
    have hsel_lt : ∀ i (hi : i < V.length) (tv : Bool) (k : ℕ),
        k ∈ varGadgetSelect φ (V[i]'hi) tv → k < (varGadgetSets φ (V[i]'hi) 0).length := by
      intro i hi tv k hk
      have hd := hv_deg i hi
      unfold varGadgetSelect at hk; unfold varGadgetSets
      have hc : (clauseIndices φ (V[i]'hi)).length = 1 ∨ (clauseIndices φ (V[i]'hi)).length = 2 ∨
          (clauseIndices φ (V[i]'hi)).length = 3 := by omega
      rcases hc with h | h | h
      · dsimp only at hk ⊢
        simp only [h, ↓reduceIte] at hk ⊢
        cases tv <;> simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_insert,
            Finset.mem_singleton] at hk <;>
          rcases hk with rfl | rfl | rfl <;> (simp only [List.length_cons, List.length_nil]; omega)
      · dsimp only at hk ⊢
        simp only [h, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hk ⊢
        cases tv <;> simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_insert,
            Finset.mem_singleton] at hk <;>
          rcases hk with rfl | rfl | rfl | rfl <;>
            (simp only [List.length_cons, List.length_nil]; omega)
      · dsimp only at hk ⊢
        simp only [h, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte] at hk ⊢
        cases tv <;> simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_insert,
            Finset.mem_singleton] at hk <;>
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
            (simp only [List.length_cons, List.length_nil]; omega)
    have hidx_range : ∀ idx : Fin sets.length,
        ∃ i, ∃ hi : i < V.length, ∃ k, ∃ hk : k < (varGadgetSets φ (V[i]'hi) 0).length,
          idx.1 = setOffset φ V i + k := by
      intro ⟨m, hm⟩
      rw [hsets_len] at hm
      suffices ∀ n (hn : n ≤ V.length), m < setOffset φ V n →
          ∃ i, ∃ hi : i < n, ∃ k, ∃ hk : k < (varGadgetSets φ (V[i]'(by omega)) 0).length,
            m = setOffset φ V i + k by
        obtain ⟨i, hi, k, hk, heq⟩ := this V.length le_rfl hm
        exact ⟨i, hi, k, hk, heq⟩
      intro n
      induction n with
      | zero => intro _ hlt; simp [setOffset] at hlt
      | succ p ih =>
        intro hp hlt
        rw [setOffset_succ φ V p (by omega)] at hlt
        by_cases h : m < setOffset φ V p
        · obtain ⟨i, hi, k, hk, heq⟩ := ih (by omega) h
          exact ⟨i, by omega, k, hk, heq⟩
        · exact ⟨p, Nat.lt_succ_self p, m - setOffset φ V p, by omega, by omega⟩
    -- Helper relating clause exact-one count to sum over `V`:
    have hclause_sum : ∀ (τ : ℕ → Bool) (j : ℕ) (hj : j < φ.length),
        (φ[j].countP (Literal.eval τ)) =
          ∑ i ∈ Finset.univ (α := Fin V.length),
            if τ (V[i.1]'i.2) = true ∧ j ∈ clauseIndices φ (V[i.1]'i.2) then 1 else 0 := by
      intro τ j hj
      have hnd_V : V.Nodup := CNF.nodup_distinctVars φ
      have hnd_c : (φ[j].map Prod.fst).Nodup := (hex _ (List.getElem_mem hj)).2
      have hpos_j : ∀ l ∈ φ[j], l.2 = true := hpos' _ (List.getElem_mem hj)
      have h1 : φ[j].countP (Literal.eval τ) =
          (φ[j].map Prod.fst).countP (fun v ↦ τ v) := by
        rw [List.countP_map]
        refine List.countP_congr fun l hl ↦ ?_
        simp [Literal.eval, hpos_j l hl]
      rw [h1, List.countP_eq_length_filter,
        ← List.toFinset_card_of_nodup (hnd_c.filter _)]
      have h2 : ∑ i ∈ (Finset.univ : Finset (Fin V.length)),
          (if τ (V[i.1]'i.2) = true ∧ j ∈ clauseIndices φ (V[i.1]'i.2) then 1 else 0) =
          (Finset.univ.filter fun i : Fin V.length ↦
            τ (V[i.1]'i.2) = true ∧ j ∈ clauseIndices φ (V[i.1]'i.2)).card := by
        rw [Finset.card_filter]
      rw [h2]
      have hmem_V : ∀ v ∈ φ[j].map Prod.fst, v ∈ V := fun v hv ↦ by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact CNF.mem_distinctVars.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr
          ⟨φ[j], List.getElem_mem hj, hl⟩, rfl⟩)
      refine Finset.card_bij (fun v hv ↦ ⟨V.idxOf v, List.idxOf_lt_length_iff.mpr
        (hmem_V v (List.mem_filter.mp (List.mem_toFinset.mp hv)).1)⟩) ?_ ?_ ?_
      · intro v hv
        have hf := List.mem_filter.mp (List.mem_toFinset.mp hv)
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · simpa [List.getElem_idxOf] using hf.2
        · rw [List.getElem_idxOf, mem_clauseIndices_iff, List.getD_eq_getElem _ _ hj]
          exact ⟨hj, hf.1⟩
      · intro v₁ hv₁ v₂ hv₂ hEq
        have hv1 := hmem_V v₁ (List.mem_filter.mp (List.mem_toFinset.mp hv₁)).1
        exact (List.idxOf_inj hv1).mp (congrArg Fin.val hEq)
      · intro i hi
        have hif := (Finset.mem_filter.mp hi).2
        have hmem_c : V[i.1] ∈ φ[j].map Prod.fst := by
          have := (mem_clauseIndices_iff φ (V[i.1]) j).mp hif.2
          rw [List.getD_eq_getElem _ _ hj] at this; exact this.2
        refine ⟨V[i.1], List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hmem_c, hif.1⟩), ?_⟩
        exact Fin.ext (List.Nodup.idxOf_getElem hnd_V i.1 i.2)
    rw [Iff.comm]
    constructor
    · rintro ⟨τ, hτ⟩
      -- Build exact cover `C'` by taking `varGadgetSelect φ (V[i]) (τ (V[i]))` in each gadget `i`:
      let C' : Finset (Fin sets.length) := Finset.univ.filter fun idx ↦
        ∃ i, ∃ hi : i < V.length, ∃ k ∈ varGadgetSelect φ (V[i]'hi) (τ (V[i]'hi)),
          idx.1 = setOffset φ V i + k
      have hmem_C' : ∀ idx : Fin sets.length, idx ∈ C' ↔
          ∃ i, ∃ hi : i < V.length, ∃ k ∈ varGadgetSelect φ (V[i]'hi) (τ (V[i]'hi)),
            idx.1 = setOffset φ V i + k := fun idx ↦ by
        simp [C']
      refine ⟨C', fun t ht ↦ ?_⟩
      -- Split `(C'.filter ...).card` as a sum over `i : Fin V.length` of per-gadget counts:
      have hsplit_card : (C'.filter fun idx ↦ t ∈ tripleFinset (sets[idx.1]'idx.2)).card =
          ∑ i ∈ (Finset.univ : Finset (Fin V.length)),
            ((varGadgetSelect φ (V[i.1]'i.2) (τ (V[i.1]'i.2))).filter fun k ↦
              t ∈ tripleFinset ((varGadgetSets φ (V[i.1]'i.2) (varDummyBase φ V i.1)).getD k
                (0, 0, 0))).card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij
          (fun idx hidx ↦
            let hex := (hmem_C' idx).mp (Finset.mem_filter.mp hidx).1
            ⟨⟨Classical.choose hex, Classical.choose (Classical.choose_spec hex)⟩,
              Classical.choose (Classical.choose_spec (Classical.choose_spec hex))⟩)
          ?_ ?_ ?_
        · intro idx hidx
          have hmem_t := (Finset.mem_filter.mp hidx).2
          have hex := (hmem_C' idx).mp (Finset.mem_filter.mp hidx).1
          set i := Classical.choose hex
          have hi : i < V.length := Classical.choose (Classical.choose_spec hex)
          set k := Classical.choose (Classical.choose_spec (Classical.choose_spec hex))
          have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex))
          refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨hspec.1, ?_⟩⟩
          have hklt := hsel_lt i hi (τ (V[i]'hi)) k hspec.1
          have hget_eq : sets[idx.1]'idx.2 =
              (varGadgetSets φ (V[i]'hi) (varDummyBase φ V i))[k]'(by
                rw [varGadgetSets_length_indep φ _ _ 0]; exact hklt) := by
            have := hsets_get i hi k hklt
            convert this using 1
            have hfin : idx = ⟨setOffset φ V i + k, by
                rw [hsets_len]; have := setOffset_add_le φ V hi le_rfl; omega⟩ := Fin.ext hspec.2
            exact congrArg (fun p : Fin sets.length ↦ sets[p.1]'p.2) hfin
          rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hklt),
            ← hget_eq]
          exact hmem_t
        · intro a ha b hb hEq
          have ha' := (hmem_C' a).mp (Finset.mem_filter.mp ha).1
          have hb' := (hmem_C' b).mp (Finset.mem_filter.mp hb).1
          have hia : Classical.choose ha' = Classical.choose hb' :=
            congrArg (fun p ↦ p.1.1) hEq
          have hka : Classical.choose (Classical.choose_spec (Classical.choose_spec ha')) =
              Classical.choose (Classical.choose_spec (Classical.choose_spec hb')) :=
            congrArg (fun p ↦ p.2) hEq
          have ha_eq := (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec ha'))).2
          have hb_eq := (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec hb'))).2
          exact Fin.ext (ha_eq.trans ((congrArg₂ (fun x y ↦ setOffset φ V x + y) hia hka).trans
            hb_eq.symm))
        · rintro ⟨⟨i, hi⟩, k⟩ hmem
          have hf := Finset.mem_filter.mp (Finset.mem_sigma.mp hmem).2
          have hklt := hsel_lt i hi (τ (V[i]'hi)) k hf.1
          have hlt_len : setOffset φ V i + k < sets.length := by
            rw [hsets_len]; have := setOffset_add_le φ V hi le_rfl; omega
          refine ⟨⟨setOffset φ V i + k, hlt_len⟩, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨(hmem_C' _).mpr ⟨i, hi, k, hf.1, rfl⟩, ?_⟩
            have hget := hsets_get i hi k hklt
            rw [hget]
            have hf2 := hf.2
            rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hklt)]
              at hf2
            exact hf2
          · -- Uniqueness of `(i, k)` representation of `setOffset φ V i + k`:
            have hex : ∃ i', ∃ hi' : i' < V.length,
              ∃ k' ∈ varGadgetSelect φ (V[i']'hi') (τ (V[i']'hi')),
                setOffset φ V i + k = setOffset φ V i' + k' := ⟨i, hi, k, hf.1, rfl⟩
            set i' := Classical.choose hex
            have hi' : i' < V.length := Classical.choose (Classical.choose_spec hex)
            set k' := Classical.choose (Classical.choose_spec (Classical.choose_spec hex))
            have hsp := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex))
            have hsp2 : setOffset φ V i + k = setOffset φ V i' + k' := hsp.2
            have hk'lt := hsel_lt i' hi' (τ (V[i']'hi')) k' hsp.1
            have hi_eq : i' = i := by
              by_contra hne
              rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
              · have := setOffset_add_le φ V hlt (by omega); omega
              · have := setOffset_add_le φ V hgt (by omega); omega
            have hk_eq : k' = k := by
              rw [hi_eq] at hsp2; omega
            exact Sigma.ext (Fin.ext hi_eq) (heq_of_eq hk_eq)
      rw [hsplit_card]
      by_cases hcl : t < 3 * φ.length
      · let j := t / 3
        let r := t % 3
        have hj : j < φ.length := by omega
        have hr : r < 3 := by omega
        have ht_eq : t = 3 * j + r := by omega
        have hsum_eq : ∑ i ∈ (Finset.univ : Finset (Fin V.length)),
            ((varGadgetSelect φ (V[i.1]'i.2) (τ (V[i.1]'i.2))).filter fun k ↦
              t ∈ tripleFinset ((varGadgetSets φ (V[i.1]'i.2) (varDummyBase φ V i.1)).getD k
                (0, 0, 0))).card =
            ∑ i ∈ (Finset.univ : Finset (Fin V.length)),
              if τ (V[i.1]'i.2) = true ∧ j ∈ clauseIndices φ (V[i.1]'i.2) then 1 else 0 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [ht_eq]
          exact varGadgetSelect_mem_card_clause φ (V[i.1]'i.2) (varDummyBase φ V i.1) j r
            (τ (V[i.1]'i.2)) (varDummyBase_ge φ V i.1) (hv_deg i.1 i.2).1 (hv_deg i.1 i.2).2 hj hr
        rw [hsum_eq, ← hclause_sum τ j hj]
        have hev : φ[j].evalOne τ = true :=
          List.all_eq_true.mp hτ φ[j] (List.getElem_mem hj)
        simpa [Clause.evalOne] using hev
      · have hge : 3 * φ.length ≤ t := by omega
        have hlt_end : t < varDummyBase φ V V.length := by rw [varDummyBase_end]; exact ht
        obtain ⟨i₀, hi₀, ht_ge, ht_lt⟩ := varDummyBase_find φ V hge hlt_end
        rw [Finset.sum_eq_single (⟨i₀, hi₀⟩ : Fin V.length)]
        · exact varGadgetSelect_mem_card_dummy φ (V[i₀]'hi₀) (varDummyBase φ V i₀) t
            (τ (V[i₀]'hi₀)) (varDummyBase_ge φ V i₀) (hv_deg i₀ hi₀).1 (hv_deg i₀ hi₀).2
            ht_ge ht_lt
        · intro i _ hine
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro k hk
          have hklt := hsel_lt i.1 i.2 (τ (V[i.1]'i.2)) k hk
          have hmem : (varGadgetSets φ (V[i.1]'i.2) (varDummyBase φ V i.1)).getD k (0, 0, 0) ∈
              varGadgetSets φ (V[i.1]'i.2) (varDummyBase φ V i.1) := by
            rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hklt)]
            exact List.getElem_mem _
          have hbnd := varGadgetSets_mem_bounds φ (V[i.1]'i.2) (varDummyBase φ V i.1) numEl
            (varDummyBase_ge φ V i.1)
            (by
              dsimp only [numEl]; rw [← varDummyBase_end]
              exact varDummyBase_add_le φ V i.2 le_rfl)
            (hv_deg i.1 i.2).1 (hv_deg i.1 i.2).2 hmem
          have hne_val : i.1 ≠ i₀ := fun h ↦ hine (Fin.ext h)
          have hout : t < varDummyBase φ V i.1 ∨
              varDummyBase φ V i.1 + varDummyCount φ (V[i.1]'i.2) ≤ t := by
            rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
            · right; exact (varDummyBase_add_le φ V hlt (by omega)).trans ht_ge
            · left; exact ht_lt.trans_le (varDummyBase_add_le φ V hgt (by omega))
          simp only [tripleFinset, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨by omega, by omega, by omega⟩
        · intro h; exact (h (Finset.mem_univ _)).elim
    · rintro ⟨C', hC'⟩
      -- Read off satisfying assignment from copy `0` (`3 * j + 0`) via set `0` of each gadget:
      let ind : (i : ℕ) → i < V.length → ℕ → ℕ := fun i hi k ↦
        if hk : k < (varGadgetSets φ (V[i]'hi) 0).length then
          if (⟨setOffset φ V i + k, by
              rw [hsets_len]; have := setOffset_add_le φ V hi le_rfl; omega⟩ :
            Fin sets.length) ∈ C' then 1 else 0
        else 0
      -- Exact cover equation on dummy `t = b + d` in gadget `i`:
      have hdummy_eq : ∀ (i : ℕ) (hi : i < V.length) (d : ℕ)
          (hd : d < varDummyCount φ (V[i]'hi)),
          ∑ k ∈ Finset.range (varGadgetSets φ (V[i]'hi) 0).length,
            (if varDummyBase φ V i + d ∈
                tripleFinset ((varGadgetSets φ (V[i]'hi) (varDummyBase φ V i)).getD k (0, 0, 0))
              then ind i hi k else 0) = 1 := by
        intro i hi d hd
        have ht_lt : varDummyBase φ V i + d < numEl := by
          have := varDummyBase_add_le φ V hi le_rfl
          rw [varDummyBase_end] at this; omega
        have hcov := hC' (varDummyBase φ V i + d) ht_lt
        rw [← hcov]
        -- Bijection between `C'.filter (dummy ∈ triple)` and local indices `k` in gadget `i`:
        have hsum_card : ∑ k ∈ Finset.range (varGadgetSets φ (V[i]'hi) 0).length,
            (if varDummyBase φ V i + d ∈
                tripleFinset ((varGadgetSets φ (V[i]'hi) (varDummyBase φ V i)).getD k (0, 0, 0))
              then ind i hi k else 0) =
            ((Finset.range (varGadgetSets φ (V[i]'hi) 0).length).filter fun k ↦
              varDummyBase φ V i + d ∈
                tripleFinset ((varGadgetSets φ (V[i]'hi) (varDummyBase φ V i)).getD k (0, 0, 0)) ∧
              ind i hi k = 1).card := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          have hklt := Finset.mem_range.mp hk
          simp only [ind, hklt, ↓reduceDIte]
          split_ifs <;> simp_all
        rw [hsum_card]
        refine Finset.card_bij (fun k hk ↦ ⟨setOffset φ V i + k, by
            have hklt := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
            rw [hsets_len]; have := setOffset_add_le φ V hi le_rfl; omega⟩) ?_ ?_ ?_
        · intro k hk
          have hf := Finset.mem_filter.mp hk
          have hklt := Finset.mem_range.mp hf.1
          have hind1 : (⟨setOffset φ V i + k, by
              rw [hsets_len]; have := setOffset_add_le φ V hi le_rfl; omega⟩ :
            Fin sets.length) ∈ C' := by
            by_contra hnot; simp [ind, hklt, hnot] at hf
          refine Finset.mem_filter.mpr ⟨hind1, ?_⟩
          rw [hsets_get i hi k hklt]
          have hf1 := hf.2.1
          rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hklt)]
            at hf1
          exact hf1
        · intro k₁ _ k₂ _ hEq
          have hval : setOffset φ V i + k₁ = setOffset φ V i + k₂ := congrArg Fin.val hEq
          omega
        · intro idx hidx
          have hmemC := (Finset.mem_filter.mp hidx).1
          have hmemt := (Finset.mem_filter.mp hidx).2
          obtain ⟨i', hi', k, hk, hidx_eq⟩ := hidx_range idx
          have hget_eq : sets[idx.1]'idx.2 =
              (varGadgetSets φ (V[i']'hi') (varDummyBase φ V i'))[k]'(by
                rw [varGadgetSets_length_indep φ _ _ 0]; exact hk) := by
            have := hsets_get i' hi' k hk
            convert this using 1
            have hfin : idx = ⟨setOffset φ V i' + k, by
                rw [hsets_len]; have := setOffset_add_le φ V hi' le_rfl; omega⟩ := Fin.ext hidx_eq
            exact congrArg (fun m : Fin sets.length ↦ sets[m.1]'m.2) hfin
          have hmem_v : sets[idx.1]'idx.2 ∈ varGadgetSets φ (V[i']'hi') (varDummyBase φ V i') := by
            rw [hget_eq]; exact List.getElem_mem _
          have hi'_eq : i' = i := by
            have hbnd := varGadgetSets_mem_bounds φ (V[i']'hi') (varDummyBase φ V i') numEl
              (varDummyBase_ge φ V i')
              (by
                dsimp only [numEl]; rw [← varDummyBase_end]
                exact varDummyBase_add_le φ V hi' le_rfl)
              (hv_deg i' hi').1 (hv_deg i' hi').2 hmem_v
            have hbase_i := varDummyBase_ge φ V i
            by_contra hne
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · have := varDummyBase_add_le φ V hlt (by omega)
              simp only [tripleFinset, Finset.mem_insert, Finset.mem_singleton] at hmemt
              rcases hmemt with h | h | h <;> omega
            · have := varDummyBase_add_le φ V hgt (by omega)
              simp only [tripleFinset, Finset.mem_insert, Finset.mem_singleton] at hmemt
              rcases hmemt with h | h | h <;> omega
          subst hi'_eq
          refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_, ?_⟩,
            Fin.ext hidx_eq.symm⟩
          · rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hk),
              ← hget_eq]
            exact hmemt
          · simp only [ind, hk, ↓reduceDIte]
            have hmem' : (⟨setOffset φ V i' + k, hidx_eq ▸ idx.2⟩ : Fin sets.length) ∈ C' := by
              convert hmemC using 1; exact Fin.ext hidx_eq.symm
            simp [hmem']
      -- Crucial consequence: for `deg = 3`, `ind i hi 0 = ind i hi 3` (`a₀ = b₀`):
      have ha0_eq_b0 : ∀ (i : ℕ) (hi : i < V.length),
          (clauseIndices φ (V[i]'hi)).length = 3 → ind i hi 0 = ind i hi 3 := by
        intro i hi hdeg3
        have hb := varDummyBase_ge φ V i
        have hj1 := clauseIndices_getD_lt φ (V[i]'hi) 0 (by omega)
        have hj2 := clauseIndices_getD_lt φ (V[i]'hi) 1 (by omega)
        have hj3 := clauseIndices_getD_lt φ (V[i]'hi) 2 (by omega)
        have hlen12 : (varGadgetSets φ (V[i]'hi) 0).length = 12 := by
          rw [varGadgetSets_length φ _ _ (by omega) (by omega), hdeg3]; simp [varDummyCount, hdeg3]
        have hvc : varDummyCount φ (V[i]'hi) = 9 := by simp [varDummyCount, hdeg3]
        have heq0 := hdummy_eq i hi 0 (by omega)
        have heq3 := hdummy_eq i hi 3 (by omega)
        have heq4 := hdummy_eq i hi 4 (by omega)
        have heq6 := hdummy_eq i hi 6 (by omega)
        have heq7 := hdummy_eq i hi 7 (by omega)
        have eval_sum : ∀ d < 9,
            ∑ k ∈ Finset.range (varGadgetSets φ (V[i]'hi) 0).length,
              (if varDummyBase φ V i + d ∈
                  tripleFinset ((varGadgetSets φ (V[i]'hi) (varDummyBase φ V i)).getD k (0, 0, 0))
                then ind i hi k else 0) =
            ∑ k ∈ Finset.range 12,
              (if varDummyBase φ V i + d ∈
                  tripleFinset ((varGadgetSets φ (V[i]'hi) (varDummyBase φ V i)).getD k (0, 0, 0))
                then ind i hi k else 0) := by intro d _; rw [hlen12]
        rw [eval_sum 0 (by omega)] at heq0
        rw [eval_sum 3 (by omega)] at heq3
        rw [eval_sum 4 (by omega)] at heq4
        rw [eval_sum 6 (by omega)] at heq6
        rw [eval_sum 7 (by omega)] at heq7
        -- Compute each of the 5 sums explicitly on `Finset.range 12`:
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, varGadgetSets, hdeg3,
          ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
          List.getD_cons_zero, List.getD_cons_succ,
          tripleFinset, Finset.mem_insert, Finset.mem_singleton] at heq0 heq3 heq4 heq6 heq7
        simp only [show varDummyBase φ V i + 0 ≠
          3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 0 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 0 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 1 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 1 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 2 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 2 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 0 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 1 by omega,
          show varDummyBase φ V i + 0 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 2 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 0 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 0 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 1 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 1 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 2 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 2 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 0 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 1 by omega,
          show varDummyBase φ V i + 3 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 2 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 0 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 0 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 1 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 1 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 2 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 2 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 0 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 1 by omega,
          show varDummyBase φ V i + 4 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 2 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 0 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 0 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 1 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 1 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 2 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 2 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 0 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 1 by omega,
          show varDummyBase φ V i + 6 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 2 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 0 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 0 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 1 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 1 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 0 0 + 2 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 1 0 + 2 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 0 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 1 by omega,
          show varDummyBase φ V i + 7 ≠ 3 * (clauseIndices φ (V[i]'hi)).getD 2 0 + 2 by omega,
          Nat.add_left_cancel_iff] at heq0 heq3 heq4 heq6 heq7
        simp only [OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, or_self,
          or_false, false_or, ↓reduceIte, add_zero, zero_add] at heq0 heq3 heq4 heq6 heq7
        omega
      -- Define `τ` from `ind i hi 0`:
      let τ : ℕ → Bool := fun v ↦
        if h : v ∈ V then decide (ind (V.idxOf v) (List.idxOf_lt_length_iff.mpr h) 0 = 1)
        else false
      have hτ_val : ∀ (i : ℕ) (hi : i < V.length),
          (if τ (V[i]'hi) = true then 1 else 0) = ind i hi 0 := by
        intro i hi
        have hmem : V[i] ∈ V := List.getElem_mem hi
        have hidx : V.idxOf (V[i]'hi) = i :=
          List.Nodup.idxOf_getElem (CNF.nodup_distinctVars φ) i hi
        simp only [τ, hmem, ↓reduceDIte, hidx, decide_eq_true_eq]
        have h01 : ind i hi 0 = 0 ∨ ind i hi 0 = 1 := by
          simp only [ind]; split_ifs <;> omega
        rcases h01 with h0 | h1
        · simp [h0]
        · simp [h1]
      refine ⟨τ, List.all_eq_true.mpr fun c hc ↦ ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
      simp only [Clause.evalOne, beq_iff_eq]
      rw [hclause_sum τ j hj]
      have hcov0 := hC' (3 * j) (by dsimp only [numEl]; omega)
      -- Show `(C'.filter (3*j ∈ triple)).card = ∑ i, if τ(V[i]) ∧ j ∈ cs_i then 1 else 0`:
      have hcard_sum : (C'.filter fun idx ↦ 3 * j ∈ tripleFinset (sets[idx.1]'idx.2)).card =
          ∑ i ∈ (Finset.univ : Finset (Fin V.length)),
            ((Finset.range (varGadgetSets φ (V[i.1]'i.2) 0).length).filter fun k ↦
              3 * j ∈ tripleFinset ((varGadgetSets φ (V[i.1]'i.2) (varDummyBase φ V i.1)).getD k
                (0, 0, 0)) ∧ ind i.1 i.2 k = 1).card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij
          (fun idx hidx ↦
            let hex := hidx_range idx
            ⟨⟨Classical.choose hex, Classical.choose (Classical.choose_spec hex)⟩,
              Classical.choose (Classical.choose_spec (Classical.choose_spec hex))⟩)
          ?_ ?_ ?_
        · intro idx hidx
          have hmemC := (Finset.mem_filter.mp hidx).1
          have hmemt := (Finset.mem_filter.mp hidx).2
          set hex := hidx_range idx
          set i := Classical.choose hex
          have hi : i < V.length := Classical.choose (Classical.choose_spec hex)
          set k := Classical.choose (Classical.choose_spec (Classical.choose_spec hex))
          have hk : k < (varGadgetSets φ (V[i]'hi) 0).length :=
            Classical.choose (Classical.choose_spec (Classical.choose_spec
              (Classical.choose_spec hex)))
          have heq : idx.1 = setOffset φ V i + k :=
            Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
              (Classical.choose_spec hex)))
          refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, ?_, ?_⟩⟩
          · have hget := hsets_get i hi k hk
            rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hk),
              ← hget]
            convert hmemt using 2
            have hfin : (⟨setOffset φ V i + k, by
                have h1 := setOffset_add_le φ V hi le_rfl
                change sets.length = setOffset φ V V.length at hsets_len; omega⟩ :
                Fin sets.length) = idx := Fin.ext heq.symm
            exact congrArg (fun m : Fin sets.length ↦ sets[m.1]'m.2) hfin
          · change (if hk' : k < (varGadgetSets φ (V[i]'hi) 0).length then
              if (⟨setOffset φ V i + k, _⟩ : Fin sets.length) ∈ C' then 1 else 0 else 0) = 1
            simp only [hk, ↓reduceDIte]
            have hmem' : (⟨setOffset φ V i + k, heq ▸ idx.2⟩ : Fin sets.length) ∈ C' := by
              convert hmemC using 1; exact Fin.ext heq.symm
            simp only [hmem', ↓reduceIte]
        · intro a _ b _ hEq
          have ha := hidx_range a; have hb := hidx_range b
          have hia : Classical.choose ha = Classical.choose hb := congrArg (fun p ↦ p.1.1) hEq
          have hka : Classical.choose (Classical.choose_spec (Classical.choose_spec ha)) =
              Classical.choose (Classical.choose_spec (Classical.choose_spec hb)) :=
            congrArg (fun p ↦ p.2) hEq
          have ha_eq := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec ha)))
          have hb_eq := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec hb)))
          exact Fin.ext (ha_eq.trans ((congrArg₂ (fun x y ↦ setOffset φ V x + y) hia hka).trans
            hb_eq.symm))
        · rintro ⟨⟨i, hi⟩, k⟩ hmem
          have hf := Finset.mem_filter.mp (Finset.mem_sigma.mp hmem).2
          have hk := Finset.mem_range.mp hf.1
          dsimp only at hk
          have hlt_s : setOffset φ V i + k < sets.length := by
            have h1 := setOffset_add_le φ V hi le_rfl
            change sets.length = setOffset φ V V.length at hsets_len
            omega
          have hind1 : (⟨setOffset φ V i + k, hlt_s⟩ : Fin sets.length) ∈ C' := by
            by_contra hnot; simp [ind, hk, hnot] at hf
          refine ⟨⟨setOffset φ V i + k, hlt_s⟩, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨hind1, ?_⟩
            rw [hsets_get i hi k hk]
            have hf1 := hf.2.1
            rw [List.getD_eq_getElem _ _ (by rw [varGadgetSets_length_indep φ _ _ 0]; exact hk)]
              at hf1
            exact hf1
          · set hex := hidx_range ⟨setOffset φ V i + k, hlt_s⟩
            set i' := Classical.choose hex
            have hi' := Classical.choose (Classical.choose_spec hex)
            set k' := Classical.choose (Classical.choose_spec (Classical.choose_spec hex))
            have hk' := Classical.choose (Classical.choose_spec (Classical.choose_spec
              (Classical.choose_spec hex)))
            have hsp : setOffset φ V i + k = setOffset φ V i' + k' :=
              Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
                (Classical.choose_spec hex)))
            have hi_eq : i' = i := by
              by_contra hne
              rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
              · have h1 := setOffset_add_le φ V hlt (by omega)
                change i' < V.length at hi'
                change k' < (varGadgetSets φ (V[i']'hi') 0).length at hk'
                omega
              · have h1 := setOffset_add_le φ V hgt (by omega)
                omega
            have hk_eq : k' = k := by rw [hi_eq] at hsp; omega
            exact Sigma.ext (Fin.ext hi_eq) (heq_of_eq hk_eq)
      refine Eq.trans ?_ hcov0
      rw [hcard_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      -- Per-gadget contribution to `3 * j`:
      rw [Finset.card_filter]
      have hdg := hv_deg i.1 i.2
      have hbi := varDummyBase_ge φ V i.1
      have hlen_g : (varGadgetSets φ (V[i.1]'i.2) 0).length =
          if (clauseIndices φ (V[i.1]'i.2)).length = 1 then 7
          else if (clauseIndices φ (V[i.1]'i.2)).length = 2 then 8 else 12 := by
        unfold varGadgetSets; dsimp only; split_ifs <;> rfl
      have hcases : (clauseIndices φ (V[i.1]'i.2)).length = 1 ∨
          (clauseIndices φ (V[i.1]'i.2)).length = 2 ∨
          (clauseIndices φ (V[i.1]'i.2)).length = 3 := by omega
      have h01 : ind i.1 i.2 0 = 0 ∨ ind i.1 i.2 0 = 1 := by
        dsimp only [ind]; split_ifs <;> omega
      rcases hcases with h | h | h
      · have hj1 := clauseIndices_getD_lt φ (V[i.1]'i.2) 0 (by omega)
        have hmem_c : j ∈ clauseIndices φ (V[i.1]'i.2) ↔
            j = (clauseIndices φ (V[i.1]'i.2)).getD 0 0 := by
          cases hl : clauseIndices φ (V[i.1]'i.2) with
          | nil => simp [hl] at h
          | cons x xs =>
            cases xs with
            | nil => simp only [List.mem_singleton, List.getD_cons_zero]
            | cons y ys => simp [hl] at h
        rw [hlen_g]
        simp only [hmem_c, h, ↓reduceIte, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          varGadgetSets, List.getD_cons_zero, List.getD_cons_succ, tripleFinset,
          Finset.mem_insert, Finset.mem_singleton]
        simp only [show ∀ m : ℕ, 3 * j ≠ varDummyBase φ V i.1 + m by intro m; omega,
          show 3 * j ≠ varDummyBase φ V i.1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 + 1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 + 2 by omega,
          or_false, false_and, ↓reduceIte, add_zero]
        by_cases hjeq : j = (clauseIndices φ (V[i.1]'i.2)).getD 0 0
        · simp only [hjeq, and_true, true_and]
          rw [hτ_val i.1 i.2]
          rcases h01 with h | h <;> simp [h]
        · simp only [hjeq, and_false, ↓reduceIte,
            show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 by omega, false_and]
      · have hj1 := clauseIndices_getD_lt φ (V[i.1]'i.2) 0 (by omega)
        have hj2 := clauseIndices_getD_lt φ (V[i.1]'i.2) 1 (by omega)
        have hmem_c : j ∈ clauseIndices φ (V[i.1]'i.2) ↔
            j = (clauseIndices φ (V[i.1]'i.2)).getD 0 0 ∨
            j = (clauseIndices φ (V[i.1]'i.2)).getD 1 0 := by
          cases hl : clauseIndices φ (V[i.1]'i.2) with
          | nil => simp [hl] at h
          | cons x xs =>
            cases xs with
            | nil => simp [hl] at h
            | cons y ys =>
              cases ys with
              | nil =>
                simp only [List.mem_cons, List.not_mem_nil, or_false, List.getD_cons_zero,
                  List.getD_cons_succ]
              | cons z zs => simp [hl] at h
        rw [hlen_g]
        simp only [hmem_c, h, ↓reduceIte, show (2 : ℕ) ≠ 1 by omega, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add, varGadgetSets, List.getD_cons_zero, List.getD_cons_succ,
          tripleFinset, Finset.mem_insert, Finset.mem_singleton]
        simp only [show ∀ m : ℕ, 3 * j ≠ varDummyBase φ V i.1 + m by intro m; omega,
          show 3 * j ≠ varDummyBase φ V i.1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 + 1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 + 1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 + 2 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 + 2 by omega,
          or_false, false_and, ↓reduceIte, add_zero]
        by_cases hjeq : j = (clauseIndices φ (V[i.1]'i.2)).getD 0 0 ∨
            j = (clauseIndices φ (V[i.1]'i.2)).getD 1 0
        · have h3eq : 3 * j = 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 ∨
              3 * j = 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 := by omega
          simp only [hjeq, h3eq, and_true, true_and]
          rw [hτ_val i.1 i.2]
          rcases h01 with h | h <;> simp [h]
        · have h3ne : ¬ (3 * j = 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 ∨
              3 * j = 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0) := by omega
          simp only [hjeq, h3ne, and_false, false_and, ↓reduceIte]
      · have hj1 := clauseIndices_getD_lt φ (V[i.1]'i.2) 0 (by omega)
        have hj2 := clauseIndices_getD_lt φ (V[i.1]'i.2) 1 (by omega)
        have hj3 := clauseIndices_getD_lt φ (V[i.1]'i.2) 2 (by omega)
        have hne01 := clauseIndices_getD_ne φ (V[i.1]'i.2) 0 1 (by omega) (by omega) (by omega)
        have hne02 := clauseIndices_getD_ne φ (V[i.1]'i.2) 0 2 (by omega) (by omega) (by omega)
        have hne12 := clauseIndices_getD_ne φ (V[i.1]'i.2) 1 2 (by omega) (by omega) (by omega)
        have hmem_c : j ∈ clauseIndices φ (V[i.1]'i.2) ↔
            j = (clauseIndices φ (V[i.1]'i.2)).getD 0 0 ∨
            j = (clauseIndices φ (V[i.1]'i.2)).getD 1 0 ∨
            j = (clauseIndices φ (V[i.1]'i.2)).getD 2 0 := by
          cases hl : clauseIndices φ (V[i.1]'i.2) with
          | nil => simp [hl] at h
          | cons x xs =>
            cases xs with
            | nil => simp [hl] at h
            | cons y ys =>
              cases ys with
              | nil => simp [hl] at h
              | cons z zs =>
                cases zs with
                | nil =>
                  simp only [List.mem_cons, List.not_mem_nil, or_false, List.getD_cons_zero,
                    List.getD_cons_succ]
                | cons w ws => simp [hl] at h
        rw [hlen_g]
        simp only [hmem_c, h, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_zero, zero_add, varGadgetSets,
          List.getD_cons_zero, List.getD_cons_succ, tripleFinset, Finset.mem_insert,
          Finset.mem_singleton]
        simp only [show ∀ m : ℕ, 3 * j ≠ varDummyBase φ V i.1 + m by intro m; omega,
          show 3 * j ≠ varDummyBase φ V i.1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 + 1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 + 1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 + 1 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 + 2 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 + 2 by omega,
          show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 + 2 by omega,
          or_false, false_and, ↓reduceIte, add_zero]
        have heq03 := ha0_eq_b0 i.1 i.2 h
        rcases eq_or_ne j ((clauseIndices φ (V[i.1]'i.2)).getD 0 0) with rfl | hj0
        · simp only [true_or, and_true, true_and, ↓reduceIte,
            show 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 ≠
              3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 by omega, false_and, add_zero]
          rw [hτ_val i.1 i.2]
          rcases h01 with h | h <;> simp [h]
        · rcases eq_or_ne j ((clauseIndices φ (V[i.1]'i.2)).getD 1 0) with rfl | hj1'
          · simp only [true_or, or_true, and_true, true_and, ↓reduceIte,
              show 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 ≠
                3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 by omega, false_and, add_zero]
            rw [hτ_val i.1 i.2]
            rcases h01 with h | h <;> simp [h]
          · rcases eq_or_ne j ((clauseIndices φ (V[i.1]'i.2)).getD 2 0) with rfl | hj2'
            · simp only [or_true, and_true, true_and, ↓reduceIte,
                show 3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 ≠
                  3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 by omega,
                show 3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 ≠
                  3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 by omega,
                or_self, false_and, zero_add, ← heq03]
              rw [hτ_val i.1 i.2]
              rcases h01 with h | h <;> simp [h]
            · simp only [hj0, hj1', hj2', or_self, and_false, ↓reduceIte,
                show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 0 0 by omega,
                show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 1 0 by omega,
                show 3 * j ≠ 3 * (clauseIndices φ (V[i.1]'i.2)).getD 2 0 by omega,
                false_and]
  · simp only [toRX3C, hsyn]
    exact iff_of_false rx3cNoInst_not_mem fun hmem ↦
      hsyn ((PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck φ).mp hmem).1

section PolyTimeToRX3C

attribute [local irreducible] encRX3C encNat encUnary

private theorem computableInPolyTime_toRX3C :
    ComputableInPolyTime toRX3C encCNF encRX3C := by
  have hsyn : ComputableInPolyTime PositiveOneInExactThreeSATThree.syntaxCheck encCNF encBool :=
    PositiveOneInExactThreeSATThree.computableInPolyTime_syntaxCheck
  have hV : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.distinctVars) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars
  have hlenφ : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
    length_list (encClause encNat)
  have hlenV : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.distinctVars.length) encCNF encUnary :=
    (length_list encNat).comp hV
  have hci : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ clauseIndices p.1 p.2)
      (encPair encCNF encNat) (encList encUnary) := by
    unfold clauseIndices
    refine filterWithInput (ComputableInPolyTime.range.comp (hlenφ.comp (fst _ _))) ?_
    let encQ := encPair (encPair encCNF encNat) encUnary
    have hcl : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ q.1.1.getD q.2 [])
        encQ (encClause encNat) :=
      listGetDWithInput ((fst encCNF encNat).comp (fst _ _)) (snd _ _) []
    have hvars : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ ↦ (q.1.1.getD q.2 []).map Prod.fst) encQ (encList encNat) :=
      (map (fst encNat encBool)).comp hcl
    exact contains hvars ((snd _ _).comp (fst _ _))
  have hci_len : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (clauseIndices p.1 p.2).length)
      (encPair encCNF encNat) encUnary := (length_list encUnary).comp hci
  have hcount3 : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ ↦ p.2.countP fun v ↦ decide ((clauseIndices p.1 v).length = 3))
      (encPair encCNF (encList encNat)) encUnary := by
    refine countPWithInput (snd _ _) ?_
    exact (hci_len.comp ((fst _ _).comp (fst _ _) |>.prod (snd _ _))).decide_eq' (const 3)
  have hsum_d : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ ↦ (p.2.map (varDummyCount p.1)).sum)
      (encPair encCNF (encList encNat)) encUnary := by
    have h1 : ComputableInPolyTime
        (fun p : CNF ℕ × List ℕ ↦
          6 * p.2.length + 3 * (p.2.countP fun v ↦ decide ((clauseIndices p.1 v).length = 3)))
        (encPair encCNF (encList encNat)) encUnary :=
      unary_add' (unary_mul' (const 6) ((length_list encNat).comp (snd _ _)))
        (unary_mul' (const 3) hcount3)
    exact h1.of_enc_eq fun p ↦ by rw [sum_varDummyCount_eq]
  have hnumEl : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ 3 * φ.length + (φ.distinctVars.map (varDummyCount φ)).sum)
      encCNF encNat :=
    unary_to_binary.comp (unary_add' (unary_mul' (const 3) hlenφ)
      (hsum_d.comp (id'.prod hV)))
  have hbase : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ varDummyBase p.1 p.1.distinctVars p.2)
      (encPair encCNF encUnary) encUnary := by
    unfold varDummyBase
    have htake : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ p.1.distinctVars.take p.2)
        (encPair encCNF encUnary) (encList encNat) :=
      listTakeWithInput (hV.comp (fst _ _)) (snd _ _)
    exact unary_add' (unary_mul' (const 3) (hlenφ.comp (fst _ _)))
      (hsum_d.comp ((fst _ _).prod htake))
  have hsets : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range φ.distinctVars.length).flatMap fun i ↦
        varGadgetSets φ (φ.distinctVars.getD i 0) (varDummyBase φ φ.distinctVars i))
      encCNF (encList (encPair encNat (encPair encNat encNat))) := by
    refine flatMapWithInput (ComputableInPolyTime.range.comp hlenV) ?_
    let encP := encPair encCNF encUnary
    have hv_i : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ p.1.distinctVars.getD p.2 0)
        encP encNat := listGetDWithInput (hV.comp (fst _ _)) (snd _ _) 0
    have hcs_i :
        ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ clauseIndices p.1 (p.1.distinctVars.getD p.2 0))
        encP (encList encUnary) := hci.comp ((fst _ _).prod hv_i)
    have hclen_i : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).length)
        encP encUnary := (length_list encUnary).comp hcs_i
    have hj : ∀ k : ℕ, ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD k 0)
        encP encUnary := fun k ↦ listGetDWithInput hcs_i (const k) 0
    have h3j : ∀ k r : ℕ, ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ 3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD k 0 + r)
        encP encNat := fun k r ↦
      unary_to_binary.comp (unary_add' (unary_mul' (const 3) (hj k)) (const r))
    have hbr : ∀ r : ℕ, ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ varDummyBase p.1 p.1.distinctVars p.2 + r) encP encNat := fun r ↦
      unary_to_binary.comp (unary_add' hbase (const r))
    let encT := encPair encNat (encPair encNat encNat)
    have hmk : ∀ (a b c : CNF ℕ × ℕ → ℕ),
        ComputableInPolyTime a encP encNat →
        ComputableInPolyTime b encP encNat →
        ComputableInPolyTime c encP encNat →
        ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (a p, b p, c p)) encP encT :=
      fun _ _ _ ha hb hc ↦ ha.prod (hb.prod hc)
    have hl1 : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦
        [(3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 0,
          varDummyBase p.1 p.1.distinctVars p.2 + 0,
          varDummyBase p.1 p.1.distinctVars p.2 + 3),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 4),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 2,
          varDummyBase p.1 p.1.distinctVars p.2 + 2,
          varDummyBase p.1 p.1.distinctVars p.2 + 5),
         (varDummyBase p.1 p.1.distinctVars p.2 + 0, varDummyBase p.1 p.1.distinctVars p.2 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 2),
         (varDummyBase p.1 p.1.distinctVars p.2 + 3, varDummyBase p.1 p.1.distinctVars p.2 + 4,
          varDummyBase p.1 p.1.distinctVars p.2 + 5),
         (varDummyBase p.1 p.1.distinctVars p.2 + 0, varDummyBase p.1 p.1.distinctVars p.2 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 5),
         (varDummyBase p.1 p.1.distinctVars p.2 + 2, varDummyBase p.1 p.1.distinctVars p.2 + 3,
          varDummyBase p.1 p.1.distinctVars p.2 + 4)]) encP (encList encT) := by
      refine cons' (hmk _ _ _ (h3j 0 0) (hbr 0) (hbr 3))
        (cons' (hmk _ _ _ (h3j 0 1) (hbr 1) (hbr 4))
        (cons' (hmk _ _ _ (h3j 0 2) (hbr 2) (hbr 5))
        (cons' (hmk _ _ _ (hbr 0) (hbr 1) (hbr 2))
        (cons' (hmk _ _ _ (hbr 3) (hbr 4) (hbr 5))
        (cons' (hmk _ _ _ (hbr 0) (hbr 1) (hbr 5))
        (cons' (hmk _ _ _ (hbr 2) (hbr 3) (hbr 4)) (const [])))))))
    have hl2 : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦
        [(3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 0,
          3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 1 0 + 0,
          varDummyBase p.1 p.1.distinctVars p.2 + 0),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 1,
          3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 1 0 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 1),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 2,
          3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 1 0 + 2,
          varDummyBase p.1 p.1.distinctVars p.2 + 2),
         (varDummyBase p.1 p.1.distinctVars p.2 + 0, varDummyBase p.1 p.1.distinctVars p.2 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 2),
         (varDummyBase p.1 p.1.distinctVars p.2 + 3, varDummyBase p.1 p.1.distinctVars p.2 + 4,
          varDummyBase p.1 p.1.distinctVars p.2 + 5),
         (varDummyBase p.1 p.1.distinctVars p.2 + 0, varDummyBase p.1 p.1.distinctVars p.2 + 3,
          varDummyBase p.1 p.1.distinctVars p.2 + 4),
         (varDummyBase p.1 p.1.distinctVars p.2 + 1, varDummyBase p.1 p.1.distinctVars p.2 + 4,
          varDummyBase p.1 p.1.distinctVars p.2 + 5),
         (varDummyBase p.1 p.1.distinctVars p.2 + 2, varDummyBase p.1 p.1.distinctVars p.2 + 5,
          varDummyBase p.1 p.1.distinctVars p.2 + 3)]) encP (encList encT) := by
      refine cons' (hmk _ _ _ (h3j 0 0) (h3j 1 0) (hbr 0))
        (cons' (hmk _ _ _ (h3j 0 1) (h3j 1 1) (hbr 1))
        (cons' (hmk _ _ _ (h3j 0 2) (h3j 1 2) (hbr 2))
        (cons' (hmk _ _ _ (hbr 0) (hbr 1) (hbr 2))
        (cons' (hmk _ _ _ (hbr 3) (hbr 4) (hbr 5))
        (cons' (hmk _ _ _ (hbr 0) (hbr 3) (hbr 4))
        (cons' (hmk _ _ _ (hbr 1) (hbr 4) (hbr 5))
        (cons' (hmk _ _ _ (hbr 2) (hbr 5) (hbr 3)) (const []))))))))
    have hl3 : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦
        [(3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 0,
          3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 1 0 + 0,
          varDummyBase p.1 p.1.distinctVars p.2 + 0),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 1,
          3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 1 0 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 1),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 0 0 + 2,
          3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 1 0 + 2,
          varDummyBase p.1 p.1.distinctVars p.2 + 2),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 2 0 + 0,
          varDummyBase p.1 p.1.distinctVars p.2 + 3,
          varDummyBase p.1 p.1.distinctVars p.2 + 6),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 2 0 + 1,
          varDummyBase p.1 p.1.distinctVars p.2 + 4,
          varDummyBase p.1 p.1.distinctVars p.2 + 7),
         (3 * (clauseIndices p.1 (p.1.distinctVars.getD p.2 0)).getD 2 0 + 2,
          varDummyBase p.1 p.1.distinctVars p.2 + 5,
          varDummyBase p.1 p.1.distinctVars p.2 + 8),
         (varDummyBase p.1 p.1.distinctVars p.2 + 0, varDummyBase p.1 p.1.distinctVars p.2 + 3,
          varDummyBase p.1 p.1.distinctVars p.2 + 6),
         (varDummyBase p.1 p.1.distinctVars p.2 + 1, varDummyBase p.1 p.1.distinctVars p.2 + 4,
          varDummyBase p.1 p.1.distinctVars p.2 + 7),
         (varDummyBase p.1 p.1.distinctVars p.2 + 2, varDummyBase p.1 p.1.distinctVars p.2 + 5,
          varDummyBase p.1 p.1.distinctVars p.2 + 8),
         (varDummyBase p.1 p.1.distinctVars p.2 + 0, varDummyBase p.1 p.1.distinctVars p.2 + 4,
          varDummyBase p.1 p.1.distinctVars p.2 + 8),
         (varDummyBase p.1 p.1.distinctVars p.2 + 1, varDummyBase p.1 p.1.distinctVars p.2 + 5,
          varDummyBase p.1 p.1.distinctVars p.2 + 6),
         (varDummyBase p.1 p.1.distinctVars p.2 + 2, varDummyBase p.1 p.1.distinctVars p.2 + 3,
          varDummyBase p.1 p.1.distinctVars p.2 + 7)]) encP (encList encT) := by
      refine cons' (hmk _ _ _ (h3j 0 0) (h3j 1 0) (hbr 0))
        (cons' (hmk _ _ _ (h3j 0 1) (h3j 1 1) (hbr 1))
        (cons' (hmk _ _ _ (h3j 0 2) (h3j 1 2) (hbr 2))
        (cons' (hmk _ _ _ (h3j 2 0) (hbr 3) (hbr 6))
        (cons' (hmk _ _ _ (h3j 2 1) (hbr 4) (hbr 7))
        (cons' (hmk _ _ _ (h3j 2 2) (hbr 5) (hbr 8))
        (cons' (hmk _ _ _ (hbr 0) (hbr 3) (hbr 6))
        (cons' (hmk _ _ _ (hbr 1) (hbr 4) (hbr 7))
        (cons' (hmk _ _ _ (hbr 2) (hbr 5) (hbr 8))
        (cons' (hmk _ _ _ (hbr 0) (hbr 4) (hbr 8))
        (cons' (hmk _ _ _ (hbr 1) (hbr 5) (hbr 6))
        (cons' (hmk _ _ _ (hbr 2) (hbr 3) (hbr 7)) (const []))))))))))))
    have hc1 := hclen_i.decide_eq' (const 1)
    have hc2 := hclen_i.decide_eq' (const 2)
    exact (hc1.ite_decide hl1 (hc2.ite_decide hl2 hl3)).of_enc_eq fun p ↦ by
      unfold varGadgetSets; rfl
  unfold toRX3C
  exact (hsyn.ite (encRX3C_mk_polyTime hnumEl hsets) (const rx3cNoInst)).of_enc_eq fun _ ↦ by
    rfl

end PolyTimeToRX3C

/-- **NP-hardness of `RX3C`**. -/
theorem RX3C_npHard : NPHard encRX3C RX3C :=
  PositiveOneInExactThreeSATThree_npHard.trans
    ⟨toRX3C, computableInPolyTime_toRX3C, fun φ ↦ (toRX3C_mem_iff φ).symm⟩

/-- **NP-completeness of `RX3C`**. -/
theorem RX3C_npComplete : NPComplete encRX3C RX3C :=
  ⟨RX3C_mem_NP, RX3C_npHard⟩

end RX3CHardness

end Cslib.Complexity
