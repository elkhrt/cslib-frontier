/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.ThreeExactCoverRegular.Gadgets

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Common
import Mathlib.Tactic.IntervalCases

/-!
# 3-Regular Exact Cover by 3-Sets (`3XC-3`)

Formalizes `ThreeExactCoverRegular` (exact cover by `3`-sets where every universe element occurs in
exactly `3` triples) and proves `ThreeExactCoverRegular_npComplete` via a linear-size
polynomial-time reduction from `PositiveOneInExactThreeSATThree`.

## Main definitions

- `Cslib.Complexity.ThreeExactCoverRegular`: `3`-regular exact cover by `3`-sets.
- `Cslib.Complexity.ThreeExactCoverRegular.reduce3Reg`: linear-size polynomial-time reduction.

## Main results

- `Cslib.Complexity.ThreeExactCoverRegular.reduce3Reg_always_regular`: exact `3`-regularity.
- `Cslib.Complexity.ThreeExactCoverRegular_npComplete`: `NP`-completeness under `encNatSetList`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **3-regular Exact Cover by 3-sets** (`3XC-3`): a duplicate-free list `C` of `3`-element sets
such that every element of `C.flatten` occurs in exactly `3` sets of `C`, admitting an exact
cover `D ⊆ C`. -/
@[expose] def ThreeExactCoverRegular : Set (List (List ℕ)) :=
  {C | C.Nodup ∧ (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧
    (∀ u ∈ C.flatten, C.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
    ∃ D : Finset (List ℕ), IsExactCover C D}

namespace ThreeExactCoverRegular

/-- A fixed `9`-element, `9`-set, `3`-regular YES-instance (`3 × 3` grid rows, columns, and
cyclic diagonals). -/
@[expose] def yesInstance : List (List ℕ) :=
  [[0, 1, 2], [3, 4, 5], [6, 7, 8],
   [0, 3, 6], [1, 4, 7], [2, 5, 8],
   [0, 4, 8], [1, 5, 6], [2, 3, 7]]

/-- A fixed `6`-element, `6`-set, `3`-regular NO-instance (no two sets are disjoint). -/
@[expose] def noInstance : List (List ℕ) :=
  [[0, 1, 3], [0, 1, 4], [0, 2, 5], [1, 2, 5], [2, 3, 4], [3, 4, 5]]

/-- Duplicate-free list of occurring variables of `φ`, preserving first-occurrence order. -/
@[expose] def distinctVars (φ : CNF ℕ) : List ℕ :=
  selectDistinct φ.vars (List.replicate φ.vars.length true)

/-- Exact variable-gadget offset `base` for the `idx`-th distinct variable of `φ`:
`3 * φ.length + 6 * ∑_{r < idx} (occ φ v_r).length`. -/
@[expose] def varBase (φ : CNF ℕ) (idx : ℕ) : ℕ :=
  3 * φ.length +
    6 * (((distinctVars φ).take idx).flatMap (ThreeExactCover.occ φ)).length

/-- Linear-size reduction from `PositiveOneInExactThreeSATThree` to `ThreeExactCoverRegular`. -/
@[expose] def reduce3Reg (φ : CNF ℕ) : List (List ℕ) :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    if φ.isEmpty then yesInstance
    else (distinctVars φ).zipIdx.flatMap fun p ↦
      varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1)
  else noInstance

/-! ### Polynomial-time computability of `reduce3Reg` -/

open ComputableInPolyTime

private theorem computableInPolyTime_occ_unary :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ ThreeExactCover.occ p.1 p.2)
      (encPair encCNF encNat) (encList encUnary) := by
  unfold ThreeExactCover.occ
  have h1 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ (q.1.1.getD q.2 []).map Prod.fst)
      (encPair (encPair encCNF encNat) encUnary) (encList encNat) := by
    unfold encCNF
    fun_prop
  exact ComputableInPolyTime.filterWithInput (encA := encUnary) (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_occ_nat :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ ThreeExactCover.occ p.1 p.2)
      (encPair encCNF encNat) (encList encNat) := by
  simpa using (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp
    computableInPolyTime_occ_unary

private theorem computableInPolyTime_distinctVars :
    ComputableInPolyTime distinctVars encCNF (encList encNat) := by
  unfold distinctVars CNF.vars
  have hvars : ComputableInPolyTime (fun φ : CNF ℕ ↦ (List.flatten φ).map Prod.fst)
      encCNF (encList encNat) := by unfold encCNF; fun_prop
  have hrep : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ List.replicate ((List.flatten φ).map Prod.fst).length true)
      encCNF encBits :=
    (ComputableInPolyTime.bitsReplicate true).comp
      ((ComputableInPolyTime.length_list encNat).comp hvars)
  exact (computableInPolyTime_selectDistinct encNat).comp (hvars.pair hrep)

attribute [local fun_prop] computableInPolyTime_occ_nat computableInPolyTime_distinctVars

private theorem computableInPolyTime_varBase :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ varBase p.1 p.2)
      (encPair encCNF encUnary) encUnary := by
  unfold varBase
  have htake : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ (distinctVars p.1).take p.2)
      (encPair encCNF encUnary) (encList encNat) := by
    fun_prop
  have hq : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ ↦ (q.1.1, q.2))
      (encPair (encPair encCNF encUnary) encNat) (encPair encCNF encNat) := by
    fun_prop
  have hflat : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ ((distinctVars p.1).take p.2).flatMap (ThreeExactCover.occ p.1))
      (encPair encCNF encUnary) (encList encNat) :=
    ComputableInPolyTime.flatMapWithInput htake (computableInPolyTime_occ_nat.comp hq)
  have hlen : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ (((distinctVars p.1).take p.2).flatMap (ThreeExactCover.occ p.1)).length)
      (encPair encCNF encUnary) encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hflat
  have h6 : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦
        6 * (((distinctVars p.1).take p.2).flatMap (ThreeExactCover.occ p.1)).length)
      (encPair encCNF encUnary) encUnary :=
    ComputableInPolyTime.unary_mul' (.const 6) hlen
  have h3 : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ 3 * p.1.length)
      (encPair encCNF encUnary) encUnary := by
    unfold encCNF
    fun_prop
  exact ComputableInPolyTime.unary_add' h3 h6

attribute [local fun_prop] computableInPolyTime_varGadget

/-- The linear-size reduction `reduce3Reg` is computable in polynomial time. -/
theorem computableInPolyTime_reduce3Reg :
    ComputableInPolyTime reduce3Reg encCNF encNatSetList := by
  unfold reduce3Reg
  have hbase_bin : ComputableInPolyTime (fun p : CNF ℕ × (ℕ × ℕ) ↦ varBase p.1 p.2.2)
      (encPair encCNF (encPair encNat encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (computableInPolyTime_varBase.comp
        ((ComputableInPolyTime.fst _ _).prod
          ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))))
  have hocc_p : ComputableInPolyTime
      (fun p : CNF ℕ × (ℕ × ℕ) ↦ ThreeExactCover.occ p.1 p.2.1)
      (encPair encCNF (encPair encNat encUnary)) (encList encNat) :=
    computableInPolyTime_occ_nat.comp
      ((ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)))
  have hstep : ComputableInPolyTime
      (fun p : CNF ℕ × (ℕ × ℕ) ↦ varGadget (varBase p.1 p.2.2) (ThreeExactCover.occ p.1 p.2.1))
      (encPair encCNF (encPair encNat encUnary)) encNatSetList :=
    computableInPolyTime_varGadget.comp (hbase_bin.prod hocc_p)
  have hzip : ComputableInPolyTime (fun φ : CNF ℕ ↦ (distinctVars φ).zipIdx)
      encCNF (encList (encPair encNat encUnary)) :=
    (ComputableInPolyTime.zipIdx encNat).comp computableInPolyTime_distinctVars
  have hflat : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (distinctVars φ).zipIdx.flatMap fun p ↦
        varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1))
      encCNF encNatSetList :=
    ComputableInPolyTime.flatMapWithInput hzip hstep
  have hempty : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.isEmpty) encCNF encBool := by
    unfold encCNF
    fun_prop
  exact ComputableInPolyTime.ite' PositiveOneInExactThreeSATThree.computableInPolyTime_syntaxCheck
    (ComputableInPolyTime.ite' hempty (.const yesInstance) hflat) (.const noInstance)

/-! ### Membership in `NP` -/

private def isTriple (S : List ℕ) : Bool :=
  (S.length == 3) && (S.getD 0 0 != S.getD 1 0) && (S.getD 0 0 != S.getD 2 0) &&
    (S.getD 1 0 != S.getD 2 0)

private lemma isTriple_iff (S : List ℕ) : isTriple S = true ↔ S.length = 3 ∧ S.Nodup := by
  rcases S with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  all_goals simp [isTriple, List.getD, List.nodup_cons, and_assoc, and_left_comm, and_comm]

private def check3Reg (x : List (List ℕ) × List (List ℕ)) : Bool :=
  (x.1.all fun S ↦ decide (x.1.count S == 1)) &&
    x.1.all isTriple &&
    (x.1.flatten.all fun u ↦ decide (x.1.countP (fun S ↦ decide (u ∈ S)) == 3)) &&
    (x.1.flatten.all fun u ↦ decide ((x.2.filter fun S ↦ decide (u ∈ S)).length == 1))

private lemma check3Reg_iff (C l : List (List ℕ)) (hl : l.Nodup) :
    check3Reg (C, l) = true ↔
      C.Nodup ∧ (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧
      (∀ u ∈ C.flatten, C.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
      ∀ u ∈ C.flatten, (l.toFinset.filter (u ∈ ·)).card = 1 := by
  simp only [check3Reg, Bool.and_eq_true, List.all_eq_true, isTriple_iff, decide_eq_true_eq,
    beq_iff_eq, and_assoc]
  have hnd : (∀ S ∈ C, C.count S = 1) ↔ C.Nodup := by
    rw [List.nodup_iff_count_le_one]
    refine ⟨fun h S ↦ ?_, fun h S hS ↦ le_antisymm (h S) (List.count_pos_iff.mpr hS)⟩
    by_cases hS : S ∈ C
    · exact (h S hS).le
    · simp [List.count_eq_zero.mpr hS]
  refine and_congr hnd (and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun u _ ↦ ?_)))
  rw [← List.toFinset_card_of_nodup (hl.filter fun S ↦ decide (u ∈ S)), List.toFinset_filter]
  simp

private theorem computableInPolyTime_check3Reg :
    ComputableInPolyTime check3Reg (encPair encNatSetList encNatSetList) encBool := by
  unfold check3Reg isTriple
  fun_prop

/-- `ThreeExactCoverRegular` belongs to `NP`. -/
theorem ThreeExactCoverRegular_mem_NP : ThreeExactCoverRegular ∈ NP encNatSetList := by
  convert mem_NP_of_subsetWitness (enc := encNatSetList) (encγ := encList encNat)
    (vs := fun C ↦ C) (check := check3Reg)
    (P := fun C D ↦ C.Nodup ∧ (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧
      (∀ u ∈ C.flatten, C.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
      ∀ u ∈ C.flatten, (D.filter (u ∈ ·)).card = 1)
    (by fun_prop) computableInPolyTime_check3Reg (fun C l hl _ ↦ check3Reg_iff C l hl) using 1
  ext C
  simp only [ThreeExactCoverRegular, IsExactCover, Set.mem_ofPred_eq]
  tauto

/-! ### Exact-cover properties of fixed boundary instances -/

/-- `yesInstance` belongs to `ThreeExactCoverRegular` with exact cover
`{[0, 1, 2], [3, 4, 5], [6, 7, 8]}`. -/
theorem yesInstance_mem : yesInstance ∈ ThreeExactCoverRegular := by
  refine ⟨by decide, by decide, by decide,
    {([0, 1, 2] : List ℕ), [3, 4, 5], [6, 7, 8]}, by decide, by decide⟩

/-- `noInstance` has no exact cover, hence does not belong to `ThreeExactCoverRegular`. -/
theorem noInstance_notMem : noInstance ∉ ThreeExactCoverRegular := by
  rintro ⟨-, -, -, D, hDC, hD⟩
  have hsub : D ⊆ noInstance.toFinset := fun S hS ↦ List.mem_toFinset.mpr (hDC S hS)
  have hpow : ∀ E ∈ noInstance.toFinset.powerset,
      ¬ ∀ u ∈ noInstance.flatten, (E.filter (u ∈ ·)).card = 1 := by decide
  exact hpow D (Finset.mem_powerset.mpr hsub) hD

/-- `noInstance` still satisfies the `3`-uniform, `3`-regular structural invariants (`n' = m' = 6`).
-/
theorem noInstance_regular :
    noInstance.Nodup ∧ (∀ S ∈ noInstance, S.length = 3 ∧ S.Nodup) ∧
    (∀ u ∈ noInstance.flatten, noInstance.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
    (∀ u, u ∈ noInstance.flatten ↔ u < 6) ∧ noInstance.length = 6 := by
  refine ⟨by decide, by decide, by decide, fun u ↦ ?_, by decide⟩
  constructor
  · intro hu
    have : u ∈ ([0, 1, 2, 3, 4, 5] : List ℕ) := by
      have hsub : ∀ x ∈ noInstance.flatten, x ∈ ([0, 1, 2, 3, 4, 5] : List ℕ) := by decide
      exact hsub u hu
    rcases (by simpa using this : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro hu
    interval_cases u <;> decide

/-- `yesInstance` satisfies the `3`-uniform, `3`-regular structural invariants (`n' = m' = 9`). -/
theorem yesInstance_regular :
    yesInstance.Nodup ∧ (∀ S ∈ yesInstance, S.length = 3 ∧ S.Nodup) ∧
    (∀ u ∈ yesInstance.flatten, yesInstance.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
    (∀ u, u ∈ yesInstance.flatten ↔ u < 9) ∧ yesInstance.length = 9 := by
  refine ⟨by decide, by decide, by decide, fun u ↦ ?_, by decide⟩
  constructor
  · intro hu
    have hsub : ∀ x ∈ yesInstance.flatten, x < 9 := by decide
    exact hsub u hu
  · intro hu
    interval_cases u <;> decide

/-! ### Structural lemmas for `distinctVars`, `varBase`, and `varGadget` -/

/-- Membership in `distinctVars φ` coincides with membership in `φ.vars`. -/
private theorem mem_distinctVars {φ : CNF ℕ} {v : ℕ} :
    v ∈ distinctVars φ ↔ v ∈ φ.vars := by
  simp only [distinctVars, mem_selectDistinct, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, List.idxOf_lt_length_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by simp [h]⟩⟩

/-- `distinctVars φ` has no duplicate elements. -/
private theorem nodup_distinctVars (φ : CNF ℕ) : (distinctVars φ).Nodup :=
  nodup_selectDistinct _ _

/-- Membership in `ThreeExactCover.occ φ v` characterizes clauses containing variable `v`. -/
private theorem mem_occ {φ : CNF ℕ} {v j : ℕ} :
    j ∈ ThreeExactCover.occ φ v ↔ j < φ.length ∧ v ∈ (φ.getD j []).map Prod.fst := by
  simp [ThreeExactCover.occ]

/-- `ThreeExactCover.occ φ v` has no duplicate clause indices. -/
private theorem nodup_occ (φ : CNF ℕ) (v : ℕ) : (ThreeExactCover.occ φ v).Nodup :=
  List.nodup_range.filter _

/-- Every variable occurring in `φ.vars` appears in at least one clause. -/
private theorem length_occ_pos_of_mem_vars {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) :
    1 ≤ (ThreeExactCover.occ φ v).length := by
  have h1 : ∃ j < φ.length, v ∈ (φ.getD j []).map Prod.fst := by
    rw [CNF.vars, List.mem_map] at hv
    rcases hv with ⟨⟨w, b⟩, hwb, rfl⟩
    rw [List.mem_flatten] at hwb
    rcases hwb with ⟨c, hc, hwc⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    refine ⟨j, hj, List.mem_map.mpr ⟨(w, b), ?_, rfl⟩⟩
    simpa [List.getD_eq_getElem?_getD, hj] using hwc
  rcases h1 with ⟨j, hj, hvj⟩
  exact List.length_pos_of_mem (mem_occ.mpr ⟨hj, hvj⟩)

private lemma list_length_filter_eq_sum {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map fun x ↦ if p x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hp : p a <;> simp [hp, ih, Nat.add_comm]

private lemma list_sum_map_sum_comm {α β : Type*} (l₁ : List α) (l₂ : List β)
    (f : α → β → ℕ) :
    (l₁.map fun a ↦ (l₂.map fun b ↦ f a b).sum).sum =
      (l₂.map fun b ↦ (l₁.map fun a ↦ f a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    clear ih
    induction l₂ with
    | nil => simp
    | cons b s ih2 => simp only [List.map_cons, List.sum_cons]; omega

private lemma list_count_flatten {α : Type*} [BEq α] (L : List (List α)) (a : α) :
    L.flatten.count a = (L.map fun l ↦ l.count a).sum := by
  induction L with
  | nil => simp
  | cons l t ih => simp [List.count_append, ih]

/-- The number of clauses containing `v` is at most the total count of `v` in `φ.vars`. -/
private theorem length_occ_le_count_vars (φ : CNF ℕ) (v : ℕ) :
    (ThreeExactCover.occ φ v).length ≤ φ.vars.count v := by
  have hsub : (ThreeExactCover.occ φ v).Sublist (List.range φ.length) := List.filter_sublist
  have hlen : (ThreeExactCover.occ φ v).length =
      ((List.range φ.length).map fun j ↦
        if v ∈ (φ.getD j []).map Prod.fst then 1 else 0).sum := by
    rw [ThreeExactCover.occ, list_length_filter_eq_sum]
    simp
  rw [hlen]
  have hcount : φ.vars.count v =
      ((List.range φ.length).map fun j ↦ ((φ.getD j []).map Prod.fst).count v).sum := by
    have hflat : φ.vars =
      ((List.range φ.length).map fun j ↦ (φ.getD j []).map Prod.fst).flatten := by
      have h1 : φ = (List.range φ.length).map (fun j ↦ φ.getD j []) := by
        refine List.ext_getElem (by simp) fun i hi _ ↦ ?_
        simp [List.getD_eq_getElem?_getD, hi]
      conv_lhs => rw [h1, CNF.vars, List.map_flatten, List.map_map]
      simp [Function.comp_def]
    rw [hflat, list_count_flatten, List.map_map]
    rfl
  rw [hcount]
  refine List.sum_le_sum fun j _ ↦ ?_
  split_ifs with h
  · exact List.count_pos_iff.mpr h
  · exact Nat.zero_le _

/-- For a syntactically valid 3-SAT formula `φ`, the sum of occurrence counts over `distinctVars φ`
equals `3 * φ.length`. -/
private theorem sum_length_occ_eq (φ : CNF ℕ)
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) :
    ((distinctVars φ).flatMap (ThreeExactCover.occ φ)).length = 3 * φ.length := by
  have hsyn := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  have hcount_clause : ∀ j < φ.length,
      ((distinctVars φ).countP fun v ↦ decide (j ∈ ThreeExactCover.occ φ v)) = 3 := by
    intro j hj
    have hcl := hsyn.1 φ[j] (List.getElem_mem hj)
    have hsub : ∀ v, decide (j ∈ ThreeExactCover.occ φ v) =
        decide (v ∈ (φ[j]).map Prod.fst) := fun v ↦ by
      simp [mem_occ, hj, List.getD_eq_getElem?_getD]
    simp_rw [hsub]
    have hperm : ((distinctVars φ).filter fun v ↦ decide (v ∈ (φ[j]).map Prod.fst)).length =
        ((φ[j]).map Prod.fst).length := by
      have hnd1 : ((distinctVars φ).filter fun v ↦ decide (v ∈ (φ[j]).map Prod.fst)).Nodup :=
        (nodup_distinctVars φ).filter _
      have hnd2 : ((φ[j]).map Prod.fst).Nodup := hcl.2
      have hmem : ∀ v, v ∈ ((distinctVars φ).filter fun v ↦ decide (v ∈ (φ[j]).map Prod.fst)) ↔
          v ∈ (φ[j]).map Prod.fst := fun v ↦ by
        simp only [List.mem_filter, decide_eq_true_eq, mem_distinctVars, and_iff_right_iff_imp]
        intro hv
        rw [CNF.vars, List.mem_map]
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        exact ⟨l, List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl⟩, rfl⟩
      rw [← List.toFinset_card_of_nodup hnd1, ← List.toFinset_card_of_nodup hnd2]
      congr 1; ext v; simp only [List.mem_toFinset, hmem]
    rw [List.countP_eq_length_filter, hperm, List.length_map, hcl.1]
  rw [List.length_flatMap]
  have hswap : ((distinctVars φ).map fun v ↦ (ThreeExactCover.occ φ v).length).sum =
      ((List.range φ.length).map fun j ↦
        (distinctVars φ).countP fun v ↦ decide (j ∈ ThreeExactCover.occ φ v)).sum := by
    have h1 : ∀ v ∈ distinctVars φ, (ThreeExactCover.occ φ v).length =
        ((List.range φ.length).map fun j ↦ if j ∈ ThreeExactCover.occ φ v then 1 else 0).sum := by
      intro v _
      rw [ThreeExactCover.occ, list_length_filter_eq_sum]
      refine congrArg List.sum (List.map_congr_left fun j hj ↦ ?_)
      simp [List.mem_range.mp hj]
    have h2 : ∀ j ∈ List.range φ.length,
        ((distinctVars φ).countP fun v ↦ decide (j ∈ ThreeExactCover.occ φ v)) =
        ((distinctVars φ).map fun v ↦ if j ∈ ThreeExactCover.occ φ v then 1 else 0).sum := by
      intro j _
      rw [List.countP_eq_length_filter, list_length_filter_eq_sum]; simp
    calc ((distinctVars φ).map fun v ↦ (ThreeExactCover.occ φ v).length).sum
        = ((distinctVars φ).map fun v ↦
            ((List.range φ.length).map fun j ↦
              if j ∈ ThreeExactCover.occ φ v then 1 else 0).sum).sum := by
          congr 1; exact List.map_congr_left h1
      _ = ((List.range φ.length).map fun j ↦
            ((distinctVars φ).map fun v ↦
              if j ∈ ThreeExactCover.occ φ v then 1 else 0).sum).sum :=
          list_sum_map_sum_comm _ _ _
      _ = _ := by congr 1; exact List.map_congr_left fun j hj ↦ (h2 j hj).symm
  rw [hswap]
  have hall : (List.range φ.length).map (fun j ↦
      (distinctVars φ).countP fun v ↦ decide (j ∈ ThreeExactCover.occ φ v)) =
      List.replicate φ.length 3 := by
    refine List.ext_getElem (by simp) fun j hj _ ↦ ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hcount_clause j (by simpa using hj)
  rw [hall, List.sum_replicate, smul_eq_mul, mul_comm]

/-- Step recurrence for the variable-gadget offset `varBase φ (idx + 1)`. -/
private theorem varBase_succ {φ : CNF ℕ} {idx : ℕ} (hidx : idx < (distinctVars φ).length) :
    varBase φ (idx + 1) =
      varBase φ idx + 6 * (ThreeExactCover.occ φ (distinctVars φ)[idx]).length := by
  simp only [varBase, List.take_succ_eq_append_getElem hidx, List.flatMap_append,
    List.flatMap_singleton, List.length_append]
  omega

/-- Monotonicity of `varBase φ` in the variable index. -/
private theorem varBase_mono {φ : CNF ℕ} {i j : ℕ} (hij : i ≤ j) : varBase φ i ≤ varBase φ j := by
  simp only [varBase]
  have hpre : ((distinctVars φ).take i).IsPrefix ((distinctVars φ).take j) := by
    have hsplit : (distinctVars φ).take i = ((distinctVars φ).take j).take i := by
      rw [List.take_take, Nat.min_eq_left hij]
    rw [hsplit]
    exact List.take_prefix i _
  have hlen : (((distinctVars φ).take i).flatMap (ThreeExactCover.occ φ)).length ≤
      (((distinctVars φ).take j).flatMap (ThreeExactCover.occ φ)).length :=
    (hpre.flatMap _).length_le
  omega

/-- Total gadget offset `varBase φ (distinctVars φ).length = 21 * φ.length`. -/
private theorem varBase_eq_total {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) :
    varBase φ (distinctVars φ).length = 21 * φ.length := by
  simp only [varBase, List.take_length, sum_length_occ_eq φ hs]
  omega

private lemma map_fst_zipIdx {α : Type*} (l : List α) : l.zipIdx.map Prod.fst = l := by
  refine List.ext_getElem (by simp) fun i hi _ ↦ ?_
  simp

private lemma nodup_zipIdx {α : Type*} (l : List α) : l.zipIdx.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij hEq
  have := congrArg Prod.snd hEq
  simp only [List.getElem_zipIdx] at this
  omega

private lemma mem_zipIdx_of_getElem {α : Type*} {l : List α} {i : ℕ} (hi : i < l.length) :
    (l[i], i) ∈ l.zipIdx := by
  refine List.mem_iff_getElem.mpr ⟨i, by simpa using hi, ?_⟩
  simp [List.getElem_zipIdx]

private lemma idxOf_getElem_of_nodup {l : List ℕ} (hnd : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l.idxOf l[i] = i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero => exact List.idxOf_cons_eq t rfl
    | succ k =>
      have hk : k < t.length := by simpa using hi
      have hne : a ≠ t[k] := fun h ↦ hnd.1 (h ▸ List.getElem_mem hk)
      rw [List.getElem_cons_succ, List.idxOf_cons_ne t hne, ih hnd.2 hk]

private lemma mem_zipIdx_distinctVars {φ : CNF ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (distinctVars φ).zipIdx) :
    p.2 < (distinctVars φ).length ∧ (distinctVars φ)[p.2]? = some p.1 ∧
      p.1 ∈ distinctVars φ := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hp
  have hi' : i < (distinctVars φ).length := by simpa using hi
  simp only [List.getElem_zipIdx, Nat.zero_add] at hget
  subst hget
  exact ⟨hi', List.getElem?_eq_getElem hi', List.getElem_mem hi'⟩

/-! ### Structural invariants & exact-cover equivalence for `reduce3Reg` -/

private lemma occ_bounds {φ : CNF ℕ} (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    {v : ℕ} (hv : v ∈ distinctVars φ) :
    1 ≤ (ThreeExactCover.occ φ v).length ∧ (ThreeExactCover.occ φ v).length ≤ 3 := by
  have hsyn := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  have hv' : v ∈ φ.vars := mem_distinctVars.mp hv
  exact ⟨length_occ_pos_of_mem_vars hv',
    (length_occ_le_count_vars φ v).trans (hsyn.2.2 v)⟩

private lemma occ_lt_base {φ : CNF ℕ} {idx : ℕ} {j : ℕ}
    (hj : j ∈ ThreeExactCover.occ φ ((distinctVars φ).getD idx 0)) :
    3 * j + 2 < varBase φ idx := by
  have hlt := (mem_occ.mp hj).1
  simp only [varBase]
  omega

/-- Structural regularity of `reduce3Reg φ` for every syntactically valid nonempty formula `φ`:
`C.Nodup`, `3`-uniform, `3`-regular, contiguous universe `0, …, 21 * φ.length - 1`, and
`C.length = 21 * φ.length`. -/
theorem reduce3Reg_regular {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) (hne : φ.isEmpty = false) :
    let C := reduce3Reg φ
    C.Nodup ∧ (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧
    (∀ u ∈ C.flatten, C.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
    (∀ u, u ∈ C.flatten ↔ u < 21 * φ.length) ∧ C.length = 21 * φ.length := by
  have hsyn := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  have hC : reduce3Reg φ = (distinctVars φ).zipIdx.flatMap fun p ↦
      varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1) := by
    simp [reduce3Reg, hs, hne]
  rw [hC]
  set L := (distinctVars φ).zipIdx
  let Gf := fun p : ℕ × ℕ ↦ varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1)
  have hp_mem : ∀ p ∈ L, p.2 < (distinctVars φ).length ∧ (distinctVars φ)[p.2]? = some p.1 ∧
      p.1 ∈ distinctVars φ := fun _ hp ↦ mem_zipIdx_distinctVars hp
  have hgp : ∀ p ∈ L,
      (Gf p).Nodup ∧ (Gf p).length = 7 * (ThreeExactCover.occ φ p.1).length ∧
      (∀ S ∈ Gf p, S.length = 3 ∧ S.Nodup) ∧
      (∀ t < 6 * (ThreeExactCover.occ φ p.1).length,
        (Gf p).countP (fun S ↦ decide (varBase φ p.2 + t ∈ S)) = 3) ∧
      (∀ u, u ∈ (Gf p).flatten →
        (∃ j ∈ ThreeExactCover.occ φ p.1, ∃ c < 3, u = 3 * j + c) ∨
        (varBase φ p.2 ≤ u ∧ u < varBase φ (p.2 + 1))) ∧
      (∀ j ∈ ThreeExactCover.occ φ p.1, ∀ c < 3,
        (Gf p).countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
      (∀ u, u < varBase φ p.2 →
        (∀ j ∈ ThreeExactCover.occ φ p.1, ∀ c < 3, u ≠ 3 * j + c) →
        (Gf p).countP (fun S ↦ decide (u ∈ S)) = 0) ∧
      (∀ u, varBase φ (p.2 + 1) ≤ u → (Gf p).countP (fun S ↦ decide (u ∈ S)) = 0) := by
    intro p hp
    rcases hp_mem p hp with ⟨hlt, hget, hv⟩
    have hsucc := varBase_succ hlt
    have hget' : (distinctVars φ)[p.2] = p.1 :=
      Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hget)
    rw [hget'] at hsucc
    have hlt_b : ∀ j ∈ ThreeExactCover.occ φ p.1, 3 * j + 2 < varBase φ p.2 := fun j hj ↦ by
      have := (mem_occ.mp hj).1; simp only [varBase]; omega
    simpa [Gf, hsucc] using varGadget_props (occ_bounds hs hv) (nodup_occ φ p.1) hlt_b
  have hlen : (L.flatMap Gf).length = 21 * φ.length := by
    rw [List.length_flatMap]
    have hmap : L.map (fun p ↦ (Gf p).length) =
        (distinctVars φ).map (fun v ↦ 7 * (ThreeExactCover.occ φ v).length) := by
      have h1 : L.map (fun p ↦ (Gf p).length) =
        L.map (fun p ↦ 7 * (ThreeExactCover.occ φ p.1).length) :=
        List.map_congr_left fun p hp ↦ (hgp p hp).2.1
      rw [h1, show (fun p : ℕ × ℕ ↦ 7 * (ThreeExactCover.occ φ p.1).length) =
          (fun v ↦ 7 * (ThreeExactCover.occ φ v).length) ∘ Prod.fst from rfl,
        ← List.map_map, map_fst_zipIdx]
    rw [hmap]
    have hsum7 : ((distinctVars φ).map (fun v ↦ 7 * (ThreeExactCover.occ φ v).length)).sum =
        7 * ((distinctVars φ).flatMap (ThreeExactCover.occ φ)).length := by
      rw [List.length_flatMap]
      induction distinctVars φ with
      | nil => simp
      | cons a l ih => simp [List.map_cons, List.sum_cons, ih, mul_add]
    rw [hsum7, sum_length_occ_eq φ hs]; omega
  have hdisj_G : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → ∀ S ∈ Gf p, S ∉ Gf q := by
    intro p hp q hq hpq S hSp hSq
    have hne_idx : p.2 ≠ q.2 := fun heq ↦ by
      apply hpq
      rcases hp_mem p hp with ⟨_, hg1, _⟩
      rcases hp_mem q hq with ⟨_, hg2, _⟩
      rw [heq] at hg1
      exact Prod.ext (Option.some.inj (hg1.symm.trans hg2)) heq
    have hSlen : S.length = 3 := ((hgp p hp).2.2.1 S hSp).1
    rcases List.length_eq_three.mp hSlen with ⟨x0, x1, x2, rfl⟩
    have hmem_int : ∀ z ∈ ([x0, x1, x2] : List ℕ),
        (z < 3 * φ.length) ∨ (varBase φ p.2 ≤ z ∧ z < varBase φ (p.2 + 1)) := fun z hz ↦ by
      have hu := (hgp p hp).2.2.2.2.1 z (List.mem_flatten.mpr ⟨_, hSp, hz⟩)
      rcases hu with ⟨j, hj, c, hc, rfl⟩ | h
      · exact Or.inl (by have := (mem_occ.mp hj).1; omega)
      · exact Or.inr h
    have hmem_int_q : ∀ z ∈ ([x0, x1, x2] : List ℕ),
        (z < 3 * φ.length) ∨ (varBase φ q.2 ≤ z ∧ z < varBase φ (q.2 + 1)) := fun z hz ↦ by
      have hu := (hgp q hq).2.2.2.2.1 z (List.mem_flatten.mpr ⟨_, hSq, hz⟩)
      rcases hu with ⟨j, hj, c, hc, rfl⟩ | h
      · exact Or.inl (by have := (mem_occ.mp hj).1; omega)
      · exact Or.inr h
    -- Every set in Gf p has at least 2 elements ≥ 3 * φ.length, which belong to p's disjoint block!
    have hge_x1 : 3 * φ.length ≤ x1 := by
      have := (hgp p hp).2.2.2.2.1 x1 (List.mem_flatten.mpr ⟨_, hSp, by simp⟩)
      -- Wait: in Gf, every set [e, a, b] or [a, b, c] has elements 1 and 2 in [base, base+6d)!
      rcases hp_mem p hp with ⟨hlt, _, hv⟩
      have hO := occ_bounds hs hv
      have hsucc := varBase_succ hlt
      have hbase_ge : 3 * φ.length ≤ varBase φ p.2 := by simp [varBase]
      -- Directly check from varGadget_props? No, x0, x1, x2: at most one can be < 3 * φ.length
      -- because any element < base in Gf p has count 1 in Gf p? Even simpler:
      -- Check by case on hmem_int x1 and x2! Actually x1 might be < 3*φ.length if only 1 is?
      -- Wait: every set in gadget1/2/3 has at most 1 element < base!
      rcases hmem_int x1 (by simp) with hx1 | hx1
      · exfalso
        have hge := second_ge_of_mem_varGadget hO hSp
        omega
      · exact (by simp [varBase] : 3 * φ.length ≤ varBase φ p.2).trans hx1.1
    have hp_int := (hmem_int x1 (by simp)).resolve_left (by omega)
    have hq_int := (hmem_int_q x1 (by simp)).resolve_left (by omega)
    rcases Nat.lt_or_gt_of_ne hne_idx with hlt | hgt
    · have := varBase_mono (φ := φ) (show p.2 + 1 ≤ q.2 by omega); omega
    · have := varBase_mono (φ := φ) (show q.2 + 1 ≤ p.2 by omega); omega
  have hnodup : (L.flatMap Gf).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun p hp ↦ (hgp p hp).1, ?_⟩
    have hndL : L.Nodup := nodup_zipIdx _
    refine List.Pairwise.imp_of_mem ?_ hndL
    intro p q hp hq hpq S hSp hSq
    exact hdisj_G p hp q hq hpq S hSp hSq
  have h3unif : ∀ S ∈ L.flatMap Gf, S.length = 3 ∧ S.Nodup := fun S hS ↦ by
    rcases List.mem_flatMap.mp hS with ⟨p, hp, hSp⟩
    exact (hgp p hp).2.2.1 S hSp
  have hmem_flat : ∀ u, u ∈ (L.flatMap Gf).flatten ↔ u < 21 * φ.length := by
    intro u
    constructor
    · intro hu
      rcases List.mem_flatten.mp hu with ⟨S, hS, huS⟩
      rcases List.mem_flatMap.mp hS with ⟨p, hp, hSp⟩
      rcases (hgp p hp).2.2.2.2.1 u (List.mem_flatten.mpr ⟨S, hSp, huS⟩) with ⟨j, hj, c, hc,
        rfl⟩ | h
      · have := (mem_occ.mp hj).1; omega
      · have hlt := (hp_mem p hp).1
        exact h.2.trans_le ((varBase_mono (φ := φ) (Nat.succ_le_of_lt hlt)).trans_eq
          (varBase_eq_total hs))
    · intro hu
      by_cases hlt3 : u < 3 * φ.length
      · have hj : u / 3 < φ.length := by omega
        have hcl := hsyn.1 φ[u / 3] (List.getElem_mem hj)
        have hne_c : φ[u / 3] ≠ [] := by intro he; simp [he] at hcl
        obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne_c
        have hv_mem : l.1 ∈ φ.vars := by
          rw [CNF.vars, List.mem_map]
          exact ⟨l, List.mem_flatten.mpr ⟨φ[u / 3], List.getElem_mem hj, hl⟩, rfl⟩
        have hv_d : l.1 ∈ distinctVars φ := mem_distinctVars.mpr hv_mem
        obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hv_d
        have hp_L : (l.1, idx) ∈ L := by
          simpa [hget] using mem_zipIdx_of_getElem hidx
        have hocc_j : u / 3 ∈ ThreeExactCover.occ φ l.1 := by
          rw [mem_occ]
          refine ⟨hj, List.mem_map.mpr ⟨l, ?_, rfl⟩⟩
          simpa [List.getD_eq_getElem?_getD, hj] using hl
        have hcnt := (hgp (l.1, idx) hp_L).2.2.2.2.2.1 (u / 3) hocc_j (u % 3) (by omega)
        have hpos : 0 < (Gf (l.1, idx)).countP (fun S ↦ decide (3 * (u / 3) + u % 3 ∈ S)) := by
          omega
        obtain ⟨S, hSp, huS⟩ := List.countP_pos_iff.mp hpos
        have heq : 3 * (u / 3) + u % 3 = u := by omega
        rw [heq] at huS
        exact List.mem_flatten.mpr ⟨S, List.mem_flatMap.mpr ⟨(l.1, idx), hp_L, hSp⟩,
          of_decide_eq_true huS⟩
      · -- `u ∈ [3 * φ.length, 21 * φ.length)`: lies in `[varBase φ idx, varBase φ (idx + 1))`.
        have h0 : varBase φ 0 = 3 * φ.length := by simp [varBase]
        have htot : varBase φ (distinctVars φ).length = 21 * φ.length := varBase_eq_total hs
        have hex : ∃ idx < (distinctVars φ).length, varBase φ idx ≤ u ∧
          u < varBase φ (idx + 1) := by
          have : ∀ n ≤ (distinctVars φ).length, varBase φ 0 ≤ u → u < varBase φ n →
              ∃ idx < n, varBase φ idx ≤ u ∧ u < varBase φ (idx + 1) := by
            intro n
            induction n with
            | zero => intro _ h1 h2; omega
            | succ k ih =>
              intro hk h1 h2
              by_cases hku : varBase φ k ≤ u
              · exact ⟨k, Nat.lt_succ_self k, hku, h2⟩
              · obtain ⟨idx, hidx, hlo, hhi⟩ := ih (by omega) h1 (by omega)
                exact ⟨idx, hidx.trans (Nat.lt_succ_self k), hlo, hhi⟩
          exact this (distinctVars φ).length le_rfl (by omega) (by omega)
        rcases hex with ⟨idx, hidx, hlo, hhi⟩
        set v := (distinctVars φ)[idx]
        have hp_L : (v, idx) ∈ L := mem_zipIdx_of_getElem hidx
        have hsucc : varBase φ (idx + 1) =
            varBase φ idx + 6 * (ThreeExactCover.occ φ v).length := varBase_succ hidx
        have hcnt := (hgp (v, idx) hp_L).2.2.2.1 (u - varBase φ idx) (by dsimp only; omega)
        have hpos : 0 < (Gf (v, idx)).countP (fun S ↦ decide (varBase φ idx +
          (u - varBase φ idx) ∈ S)) := by dsimp only at hcnt; omega
        obtain ⟨S, hSp, huS⟩ := List.countP_pos_iff.mp hpos
        rw [Nat.add_sub_cancel' hlo] at huS
        exact List.mem_flatten.mpr ⟨S, List.mem_flatMap.mpr ⟨(v, idx), hp_L, hSp⟩,
          of_decide_eq_true huS⟩
  have h3reg : ∀ u ∈ (L.flatMap Gf).flatten, (L.flatMap Gf).countP (fun S ↦ decide (u ∈ S)) =
    3 := by
    intro u hu
    have hlt21 : u < 21 * φ.length := (hmem_flat u).mp hu
    rw [List.countP_flatMap]
    simp only [Function.comp_def]
    by_cases hlt3 : u < 3 * φ.length
    · -- Clause-copy element u = 3 * j + c: appears once in each of the 3 variables of clause j!
      have hj : u / 3 < φ.length := by omega
      have hcl := hsyn.1 φ[u / 3] (List.getElem_mem hj)
      have hmap_eq : L.map (fun p ↦ (Gf p).countP (fun S ↦ decide (u ∈ S))) =
          (distinctVars φ).map (fun v ↦ if u / 3 ∈ ThreeExactCover.occ φ v then 1 else 0) := by
        have h1 : L.map (fun p ↦ (Gf p).countP (fun S ↦ decide (u ∈ S))) =
            L.map (fun p ↦ if u / 3 ∈ ThreeExactCover.occ φ p.1 then 1 else 0) := by
          refine List.map_congr_left fun p hp ↦ ?_
          split_ifs with hocc
          · have heq : 3 * (u / 3) + u % 3 = u := by omega
            simpa [heq] using (hgp p hp).2.2.2.2.2.1 (u / 3) hocc (u % 3) (by omega)
          · refine (hgp p hp).2.2.2.2.2.2.1 u (by simp [varBase]; omega) fun j hj' c hc heq ↦ ?_
            have : j = u / 3 := by omega
            exact hocc (this ▸ hj')
        rw [h1, show (fun p : ℕ × ℕ ↦ if u / 3 ∈ ThreeExactCover.occ φ p.1 then 1 else 0) =
            (fun v ↦ if u / 3 ∈ ThreeExactCover.occ φ v then 1 else 0) ∘ Prod.fst from rfl,
          ← List.map_map, map_fst_zipIdx]
      rw [hmap_eq]
      have hcntP : ((distinctVars φ).map fun v ↦
          if u / 3 ∈ ThreeExactCover.occ φ v then 1 else 0).sum =
          ((distinctVars φ).filter fun v ↦ decide (u / 3 ∈ ThreeExactCover.occ φ v)).length := by
        rw [list_length_filter_eq_sum]; simp
      rw [hcntP]
      have hnd1 :
          ((distinctVars φ).filter fun v ↦ decide (u / 3 ∈ ThreeExactCover.occ φ v)).Nodup :=
        (nodup_distinctVars φ).filter _
      have hmem : ∀ v, v ∈ ((distinctVars φ).filter fun v ↦
          decide (u / 3 ∈ ThreeExactCover.occ φ v)) ↔ v ∈ (φ[u / 3]).map Prod.fst := fun v ↦ by
        simp only [List.mem_filter, decide_eq_true_eq, mem_distinctVars, mem_occ, hj, true_and,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
          and_iff_right_iff_imp]
        intro hv
        rw [CNF.vars, List.mem_map]
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        exact ⟨l, List.mem_flatten.mpr ⟨φ[u / 3], List.getElem_mem hj, hl⟩, rfl⟩
      rw [← List.toFinset_card_of_nodup hnd1,
        show ((distinctVars φ).filter fun v ↦ decide (u / 3 ∈ ThreeExactCover.occ φ v)).toFinset =
          ((φ[u / 3]).map Prod.fst).toFinset from by
          ext v; simp only [List.mem_toFinset]; exact hmem v,
        List.toFinset_card_of_nodup hcl.2, List.length_map, hcl.1]
    · -- Internal element `u ∈ [varBase φ idx, varBase φ (idx + 1))`: 3 times in `p_idx`.
      have h0 : varBase φ 0 = 3 * φ.length := by simp [varBase]
      have htot : varBase φ (distinctVars φ).length = 21 * φ.length := varBase_eq_total hs
      have hex : ∃ idx < (distinctVars φ).length, varBase φ idx ≤ u ∧ u < varBase φ (idx + 1) := by
        have : ∀ n ≤ (distinctVars φ).length, varBase φ 0 ≤ u → u < varBase φ n →
            ∃ idx < n, varBase φ idx ≤ u ∧ u < varBase φ (idx + 1) := by
          intro n; induction n with
          | zero => intro _ h1 h2; omega
          | succ k ih =>
            intro hk h1 h2
            by_cases hku : varBase φ k ≤ u
            · exact ⟨k, Nat.lt_succ_self k, hku, h2⟩
            · obtain ⟨idx, hidx, hlo, hhi⟩ := ih (by omega) h1 (by omega)
              exact ⟨idx, hidx.trans (Nat.lt_succ_self k), hlo, hhi⟩
        exact this (distinctVars φ).length le_rfl (by omega) (by omega)
      rcases hex with ⟨idx, hidx, hlo, hhi⟩
      set v := (distinctVars φ)[idx]
      have hp_L : (v, idx) ∈ L := mem_zipIdx_of_getElem hidx
      have hother : ∀ q ∈ L, q ≠ (v, idx) → (Gf q).countP (fun S ↦ decide (u ∈ S)) = 0 := by
        intro q hq hne_q
        have hne_i : q.2 ≠ idx := fun heq ↦ by
          apply hne_q
          rcases hp_mem q hq with ⟨_, hg, _⟩
          rw [heq, List.getElem?_eq_getElem hidx] at hg
          exact Prod.ext (Option.some.inj hg.symm) heq
        rcases Nat.lt_or_gt_of_ne hne_i with hlt | hgt
        · exact (hgp q hq).2.2.2.2.2.2.2 u ((varBase_mono (Nat.succ_le_of_lt hlt)).trans hlo)
        · refine (hgp q hq).2.2.2.2.2.2.1 u (hhi.trans_le (varBase_mono (Nat.succ_le_of_lt hgt))) ?_
          intro j hj c hc; have := (mem_occ.mp hj).1; omega
      have hsum_fin : (L.map (fun q ↦ (Gf q).countP (fun S ↦ decide (u ∈ S)))).sum =
          ∑ q ∈ L.toFinset, (Gf q).countP (fun S ↦ decide (u ∈ S)) := by
        rw [← List.sum_toFinset _ (nodup_zipIdx _)]
      rw [hsum_fin, Finset.sum_eq_single (v, idx)]
      · have hsucc : varBase φ (idx + 1) =
            varBase φ idx + 6 * (ThreeExactCover.occ φ v).length := varBase_succ hidx
        have := (hgp (v, idx) hp_L).2.2.2.1 (u - varBase φ idx) (by dsimp only; omega)
        rwa [Nat.add_sub_cancel' hlo] at this
      · intro q hq hne_q; exact hother q (List.mem_toFinset.mp hq) hne_q
      · intro hnot; exact absurd (List.mem_toFinset.mpr hp_L) hnot
  exact ⟨hnodup, h3unif, h3reg, hmem_flat, hlen⟩

/-- Forward soundness: if `reduce3Reg φ ∈ ThreeExactCoverRegular`, then
`φ ∈ PositiveOneInExactThreeSATThree`. -/
theorem oneSatisfiable_of_mem {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    (h : reduce3Reg φ ∈ ThreeExactCoverRegular) : φ.OneSatisfiable := by
  by_cases hne : φ.isEmpty = true
  · have : φ = [] := List.isEmpty_iff.mp hne
    subst this
    exact ⟨fun _ ↦ false, by simp [CNF.evalOne]⟩
  · have hne' : φ.isEmpty = false := Bool.eq_false_iff.mpr hne
    have hsyn := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
    have hC : reduce3Reg φ = (distinctVars φ).zipIdx.flatMap fun p ↦
        varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1) := by
      simp [reduce3Reg, hs, hne']
    rcases h with ⟨_, _, _, D, hDC, hD⟩
    rw [hC] at hDC hD
    set L := (distinctVars φ).zipIdx
    let Gf := fun p : ℕ × ℕ ↦ varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1)
    have hreg := reduce3Reg_regular hs hne'
    rw [hC] at hreg
    have hp_mem : ∀ p ∈ L, p.2 < (distinctVars φ).length ∧ (distinctVars φ)[p.2]? = some p.1 ∧
      p.1 ∈ distinctVars φ := fun _ hp ↦ mem_zipIdx_distinctVars hp
    -- For each p ∈ L, D ∩ Gf p satisfies varGadget_forcing!
    have hforce : ∀ p ∈ L,
        (∀ j ∈ ThreeExactCover.occ φ p.1, ∀ c < 3,
          ((D.filter fun S ↦ S ∈ Gf p).filter (3 * j + c ∈ ·)).card = 1) ∨
        (∀ j ∈ ThreeExactCover.occ φ p.1, ∀ c < 3,
          ((D.filter fun S ↦ S ∈ Gf p).filter (3 * j + c ∈ ·)).card = 0) := by
      intro p hp
      rcases hp_mem p hp with ⟨hlt, hget, hv⟩
      have hsucc := varBase_succ hlt
      have hget' : (distinctVars φ)[p.2] = p.1 :=
        Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hget)
      rw [hget'] at hsucc
      have hlt_b : ∀ j ∈ ThreeExactCover.occ φ p.1, 3 * j + 2 < varBase φ p.2 := fun j hj ↦ by
        have := (mem_occ.mp hj).1; simp only [varBase]; omega
      refine varGadget_forcing (occ_bounds hs hv) (nodup_occ φ p.1) hlt_b fun t ht ↦ ?_
      have hu_lt : varBase φ p.2 + t < 21 * φ.length := by
        have := (varBase_mono (φ := φ) (show p.2 + 1 ≤ (distinctVars φ).length by omega)).trans_eq
          (varBase_eq_total hs)
        omega
      have hu_mem : varBase φ p.2 + t ∈ (L.flatMap Gf).flatten := (hreg.2.2.2.1 _).mpr hu_lt
      have hEq : (D.filter fun S ↦ S ∈ Gf p).filter (varBase φ p.2 + t ∈ ·) =
          D.filter (varBase φ p.2 + t ∈ ·) := by
        ext S
        simp only [Finset.mem_filter]
        refine ⟨fun ⟨⟨hSD, _⟩, huS⟩ ↦ ⟨hSD, huS⟩, fun ⟨hSD, huS⟩ ↦ ⟨⟨hSD, ?_⟩, huS⟩⟩
        rcases List.mem_flatMap.mp (hDC S hSD) with ⟨q, hq, hSq⟩
        by_cases hqp : q = p
        · exact hqp ▸ hSq
        · exfalso
          have hne_i : q.2 ≠ p.2 := fun heq ↦ by
            apply hqp
            rcases hp_mem q hq with ⟨_, hg1, _⟩
            rw [heq] at hg1
            exact Prod.ext (Option.some.inj (hg1.symm.trans hget)) heq
          rcases Nat.lt_or_gt_of_ne hne_i with hlt_q | hgt_q
          · have hbase_le : varBase φ (q.2 + 1) ≤ varBase φ p.2 :=
              varBase_mono (Nat.succ_le_of_lt hlt_q)
            have hget_q' := (hp_mem q hq).2.1
            rw [List.getElem?_eq_getElem (hp_mem q hq).1] at hget_q'
            have hget_q : (distinctVars φ)[q.2] = q.1 := Option.some.inj hget_q'
            have hsucc_q := varBase_succ (hp_mem q hq).1
            rw [hget_q] at hsucc_q
            have hlt_bq : ∀ j ∈ ThreeExactCover.occ φ q.1, 3 * j + 2 < varBase φ q.2 :=
              fun j hj ↦ by
              have := (mem_occ.mp hj).1; simp only [varBase]; omega
            have h0 := (varGadget_props (occ_bounds hs (hp_mem q hq).2.2) (nodup_occ φ q.1)
              hlt_bq).2.2.2.2.2.2.2 (varBase φ p.2 + t) (by omega)
            have := List.countP_eq_zero.mp h0 S hSq
            simp [huS] at this
          · have hbase_le : varBase φ (p.2 + 1) ≤ varBase φ q.2 :=
              varBase_mono (Nat.succ_le_of_lt hgt_q)
            have hlt_bq : ∀ j ∈ ThreeExactCover.occ φ q.1, 3 * j + 2 < varBase φ q.2 :=
              fun j hj ↦ by
              have := (mem_occ.mp hj).1; simp only [varBase]; omega
            have h0 := (varGadget_props (occ_bounds hs (hp_mem q hq).2.2) (nodup_occ φ q.1)
              hlt_bq).2.2.2.2.2.2.1 (varBase φ p.2 + t) (by omega) (fun j hj c hc ↦ by
                have := (mem_occ.mp hj).1; simp only [varBase]; omega)
            have := List.countP_eq_zero.mp h0 S hSq
            simp [huS] at this
      rw [hEq]
      exact hD _ hu_mem
    -- Define the satisfying exact-one assignment τ!
    let τ : ℕ → Bool := fun v ↦
      if h : v ∈ distinctVars φ then
        decide (∀ j ∈ ThreeExactCover.occ φ v,
          ((D.filter fun S ↦ S ∈ varGadget (varBase φ ((distinctVars φ).idxOf v))
            (ThreeExactCover.occ φ v)).filter (3 * j ∈ ·)).card = 1)
      else false
    refine ⟨τ, ?_⟩
    rw [CNF.evalOne, List.all_eq_true]
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    rw [Clause.evalOne, beq_iff_eq]
    have hcl := hsyn.1 φ[j] (List.getElem_mem hj)
    have hpos_cl := (OneSAT.positiveCheck_iff φ).mp hsyn.2.1 φ[j] (List.getElem_mem hj)
    have hu_mem : 3 * j ∈ (L.flatMap Gf).flatten := (hreg.2.2.2.1 (3 * j)).mpr (by omega)
    have hD_j := hD (3 * j) hu_mem
    -- Partition D.filter (3 * j ∈ ·) by the variable gadget p ∈ L containing S
    have hpart : ∀ v ∈ (φ[j]).map Prod.fst,
        ∃ idx, (v, idx) ∈ L ∧ idx = (distinctVars φ).idxOf v := fun v hv ↦ by
      have hv_d : v ∈ distinctVars φ := by
        rw [mem_distinctVars, CNF.vars, List.mem_map]
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        exact ⟨l, List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl⟩, rfl⟩
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hv_d
      have hidx_eq : (distinctVars φ).idxOf v = idx := by
        rw [← hget]; exact idxOf_getElem_of_nodup (nodup_distinctVars φ) hidx
      exact ⟨idx, by simpa [hget] using mem_zipIdx_of_getElem hidx, hidx_eq.symm⟩
    have hsum_eq : (D.filter (3 * j ∈ ·)).card =
        ∑ v ∈ ((φ[j]).map Prod.fst).toFinset,
          ((D.filter fun S ↦ S ∈ Gf (v, (distinctVars φ).idxOf v)).filter (3 * j ∈ ·)).card := by
      have hbi : D.filter (3 * j ∈ ·) =
          (((φ[j]).map Prod.fst).toFinset).biUnion fun v ↦
            (D.filter fun S ↦ S ∈ Gf (v, (distinctVars φ).idxOf v)).filter (3 * j ∈ ·) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset]
        constructor
        · rintro ⟨hSD, hjS⟩
          rcases List.mem_flatMap.mp (hDC S hSD) with ⟨p, hp, hSp⟩
          rcases hp_mem p hp with ⟨hlt, hget, hv⟩
          have hget' : (distinctVars φ)[p.2] = p.1 :=
            Option.some.inj (by rwa [List.getElem?_eq_getElem hlt] at hget)
          have hidx_eq : (distinctVars φ).idxOf p.1 = p.2 := by
            rw [← hget']; exact idxOf_getElem_of_nodup (nodup_distinctVars φ) hlt
          have hj_occ : j ∈ ThreeExactCover.occ φ p.1 := by
            by_contra hnot
            have h0 := (varGadget_props (base := varBase φ p.2) (occ_bounds hs hv)
              (nodup_occ φ p.1) (fun j' hj' ↦ by
                have := (mem_occ.mp hj').1; dsimp only [varBase]; omega)).2.2.2.2.2.2.1
              (3 * j) (by dsimp only [varBase]; omega) (fun j' hj' c hc heq ↦ by
                have : j' = j := by omega
                exact hnot (this ▸ hj'))
            have := List.countP_eq_zero.mp h0 S hSp
            simp [hjS] at this
          have hv_cl : p.1 ∈ (φ[j]).map Prod.fst := by
            simpa [mem_occ, hj, List.getD_eq_getElem?_getD] using hj_occ
          exact ⟨p.1, hv_cl, ⟨hSD, hidx_eq ▸ hSp⟩, hjS⟩
        · rintro ⟨v, _, ⟨hSD, _⟩, hjS⟩
          exact ⟨hSD, hjS⟩
      rw [hbi, Finset.card_biUnion]
      intro v1 hv1 v2 hv2 hne_v
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro S hS1 hS2
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hS1).1).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hS2).1).2
      obtain ⟨i1, hp1, rfl⟩ := hpart v1 (List.mem_toFinset.mp hv1)
      obtain ⟨i2, hp2, rfl⟩ := hpart v2 (List.mem_toFinset.mp hv2)
      -- distinct gadgets are disjoint!
      have hpq : (v1, (distinctVars φ).idxOf v1) ≠ (v2, (distinctVars φ).idxOf v2) := fun heq ↦
        hne_v (congrArg Prod.fst heq)
      have hnd := hreg.1
      rw [List.nodup_flatMap] at hnd
      have hpw := hnd.2
      have hdisj : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → ∀ Z ∈ Gf p, Z ∉ Gf q := by
        intro p hp q hq hne_pq Z hZp hZq
        rcases List.mem_iff_getElem.mp hp with ⟨a, ha, rfl⟩
        rcases List.mem_iff_getElem.mp hq with ⟨b, hb, rfl⟩
        rcases Nat.lt_or_gt_of_ne (show a ≠ b by rintro rfl; exact hne_pq rfl) with hab | hba
        · exact (List.pairwise_iff_getElem.mp hpw a b ha hb hab) hZp hZq
        · exact (List.pairwise_iff_getElem.mp hpw b a hb ha hba) hZq hZp
      exact hdisj _ hp1 _ hp2 hpq S h1 h2
    have hcount_eq : (φ[j]).countP (Literal.eval τ) =
        ∑ v ∈ ((φ[j]).map Prod.fst).toFinset,
          ((D.filter fun S ↦ S ∈ Gf (v, (distinctVars φ).idxOf v)).filter (3 * j ∈ ·)).card := by
      have h1 : (φ[j]).countP (Literal.eval τ) = ((φ[j]).map Prod.fst).countP τ := by
        rw [List.countP_map]
        refine List.countP_congr fun l hl ↦ ?_
        simp [Literal.eval, hpos_cl l hl]
      rw [h1, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hcl.2.filter _),
        List.toFinset_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v hv ↦ ?_
      have hv_cl := List.mem_toFinset.mp hv
      obtain ⟨idx, hp_L, rfl⟩ := hpart v hv_cl
      have hv_d := (hp_mem _ hp_L).2.2
      have hj_occ : j ∈ ThreeExactCover.occ φ v := by
        rw [mem_occ]; simpa [hj, List.getD_eq_getElem?_getD] using hv_cl
      rcases hforce _ hp_L with hT | hF
      · have hτ : τ v = true := by
          simp only [τ, hv_d, ↓reduceDIte, decide_eq_true_eq]
          intro j' hj'; exact hT j' hj' 0 (by omega)
        have hT0 := hT j hj_occ 0 (by omega)
        simp only [add_zero] at hT0
        rw [hτ]; simp only [↓reduceIte]; exact hT0.symm
      · have hF0 := hF j hj_occ 0 (by omega)
        simp only [add_zero] at hF0
        have hτ : τ v = false := by
          simp only [τ, hv_d, ↓reduceDIte, decide_eq_false_iff_not]
          intro h; have h1 := h j hj_occ; dsimp only [Gf] at hF0; omega
        rw [hτ]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hF0.symm
    rw [hcount_eq, ← hsum_eq, hD_j]

/-- Reverse soundness: if `φ ∈ PositiveOneInExactThreeSATThree`, then
`reduce3Reg φ ∈ ThreeExactCoverRegular`. -/
theorem mem_of_oneSatisfiable {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    (h : φ.OneSatisfiable) : reduce3Reg φ ∈ ThreeExactCoverRegular := by
  by_cases hne : φ.isEmpty = true
  · simpa [reduce3Reg, hs, hne] using yesInstance_mem
  · have hne' : φ.isEmpty = false := Bool.eq_false_iff.mpr hne
    have hsyn := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
    have hreg := reduce3Reg_regular hs hne'
    have hC : reduce3Reg φ = (distinctVars φ).zipIdx.flatMap fun p ↦
        varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1) := by
      simp [reduce3Reg, hs, hne']
    rcases h with ⟨τ, hτ⟩
    set L := (distinctVars φ).zipIdx
    let Gf := fun p : ℕ × ℕ ↦ varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1)
    let Df := fun p : ℕ × ℕ ↦
      if τ p.1 then gadgetTrue (varBase φ p.2) (ThreeExactCover.occ φ p.1)
      else gadgetFalse (varBase φ p.2) (ThreeExactCover.occ φ p.1)
    let DList := L.flatMap Df
    have hp_mem : ∀ p ∈ L, p.2 < (distinctVars φ).length ∧ (distinctVars φ)[p.2]? = some p.1 ∧
      p.1 ∈ distinctVars φ := fun _ hp ↦ mem_zipIdx_distinctVars hp
    have hD_sub : ∀ S ∈ DList, S ∈ reduce3Reg φ := fun S hS ↦ by
      rw [hC]
      rcases List.mem_flatMap.mp hS with ⟨p, hp, hSp⟩
      refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
      have hv := (hp_mem p hp).2.2
      have hlt_b : ∀ j ∈ ThreeExactCover.occ φ p.1, 3 * j + 2 < varBase φ p.2 := fun j hj ↦ by
        have := (mem_occ.mp hj).1; simp only [varBase]; omega
      dsimp [Df] at hSp; split_ifs at hSp
      · exact (gadgetTrue_props (occ_bounds hs hv) (nodup_occ φ p.1) hlt_b).1 S hSp
      · exact (gadgetFalse_props (occ_bounds hs hv)).1 S hSp
    have hD_nd : DList.Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun p hp ↦ ?_, ?_⟩
      · have hv := (hp_mem p hp).2.2
        have hlt_b : ∀ j ∈ ThreeExactCover.occ φ p.1, 3 * j + 2 < varBase φ p.2 := fun j hj ↦ by
          have := (mem_occ.mp hj).1; simp only [varBase]; omega
        dsimp [Df]; split_ifs
        · exact (gadgetTrue_props (occ_bounds hs hv) (nodup_occ φ p.1) hlt_b).2.1
        · exact (gadgetFalse_props (occ_bounds hs hv)).2.1
      · have hndC := hreg.1
        rw [hC, List.nodup_flatMap] at hndC
        refine List.Pairwise.imp_of_mem ?_ hndC.2
        intro p q hp hq hdisj S hSp hSq
        have hlt_bp : ∀ j ∈ ThreeExactCover.occ φ p.1, 3 * j + 2 < varBase φ p.2 := fun j hj ↦ by
          have := (mem_occ.mp hj).1; simp only [varBase]; omega
        have hlt_bq : ∀ j ∈ ThreeExactCover.occ φ q.1, 3 * j + 2 < varBase φ q.2 := fun j hj ↦ by
          have := (mem_occ.mp hj).1; simp only [varBase]; omega
        have hSp' : S ∈ Gf p := by
          dsimp [Df] at hSp; split_ifs at hSp
          · exact (gadgetTrue_props (occ_bounds hs (hp_mem p hp).2.2)
            (nodup_occ φ p.1) hlt_bp).1 S hSp
          · exact (gadgetFalse_props (occ_bounds hs (hp_mem p hp).2.2)).1 S hSp
        have hSq' : S ∈ Gf q := by
          dsimp [Df] at hSq; split_ifs at hSq
          · exact (gadgetTrue_props (occ_bounds hs (hp_mem q hq).2.2)
            (nodup_occ φ q.1) hlt_bq).1 S hSq
          · exact (gadgetFalse_props (occ_bounds hs (hp_mem q hq).2.2)).1 S hSq
        exact hdisj hSp' hSq'
    refine ⟨hreg.1, hreg.2.1, hreg.2.2.1, DList.toFinset,
      fun S hS ↦ hD_sub S (List.mem_toFinset.mp hS), fun u hu ↦ ?_⟩
    have hfilt : DList.toFinset.filter (u ∈ ·) =
        (DList.filter fun S ↦ decide (u ∈ S)).toFinset := by
      ext S; simp
    rw [hfilt, List.toFinset_card_of_nodup (hD_nd.filter _),
      ← List.countP_eq_length_filter, List.countP_flatMap]
    simp only [Function.comp_def]
    have hlt21 : u < 21 * φ.length := (hreg.2.2.2.1 u).mp hu
    by_cases hlt3 : u < 3 * φ.length
    · have hj : u / 3 < φ.length := by omega
      have hcl := hsyn.1 φ[u / 3] (List.getElem_mem hj)
      have hpos_cl := (OneSAT.positiveCheck_iff φ).mp hsyn.2.1 φ[u / 3] (List.getElem_mem hj)
      have heval : (φ[u / 3]).countP (Literal.eval τ) = 1 := by
        rw [CNF.evalOne, List.all_eq_true] at hτ
        simpa [Clause.evalOne] using hτ φ[u / 3] (List.getElem_mem hj)
      have hmap_eq : L.map (fun p ↦ (Df p).countP (fun S ↦ decide (u ∈ S))) =
          (distinctVars φ).map (fun v ↦
            if u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true then 1 else 0) := by
        have h1 : L.map (fun p ↦ (Df p).countP (fun S ↦ decide (u ∈ S))) =
            L.map (fun p ↦ if u / 3 ∈ ThreeExactCover.occ φ p.1 ∧ τ p.1 = true then 1 else 0) := by
          refine List.map_congr_left fun p hp ↦ ?_
          have hv := (hp_mem p hp).2.2
          have hlt_b : ∀ j ∈ ThreeExactCover.occ φ p.1, 3 * j + 2 < varBase φ p.2 := fun j hj ↦ by
            have := (mem_occ.mp hj).1; simp only [varBase]; omega
          dsimp [Df]
          by_cases hτp : τ p.1 = true
          · simp only [hτp, ↓reduceIte, and_true]
            split_ifs with hcond
            · have heq : 3 * (u / 3) + u % 3 = u := by omega
              simpa [heq] using
                (gadgetTrue_props (occ_bounds hs hv) (nodup_occ φ p.1) hlt_b).2.2.2.1
                  (u / 3) hcond (u % 3) (by omega)
            · refine (gadgetTrue_props (occ_bounds hs hv) (nodup_occ φ p.1) hlt_b).2.2.2.2.1
                u (by simp [varBase]; omega) fun j hj' c hc heq ↦ ?_
              have : j = u / 3 := by omega
              exact hcond (this ▸ hj')
          · simpa [hτp] using
              (gadgetFalse_props (base := varBase φ p.2) (occ_bounds hs hv)).2.2.2.1 u
                (by simp [varBase]; omega)
        rw [h1, show (fun p : ℕ × ℕ ↦
              if u / 3 ∈ ThreeExactCover.occ φ p.1 ∧ τ p.1 = true then 1 else 0) =
            (fun v ↦ if u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true then 1 else 0) ∘ Prod.fst
            from rfl,
          ← List.map_map, map_fst_zipIdx]
      rw [hmap_eq]
      have hcntP : ((distinctVars φ).map fun v ↦
          if u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true then 1 else 0).sum =
          ((distinctVars φ).filter fun v ↦
            decide (u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true)).length := by
        rw [list_length_filter_eq_sum]; simp
      rw [hcntP]
      have hnd1 : ((distinctVars φ).filter fun v ↦
          decide (u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true)).Nodup :=
        (nodup_distinctVars φ).filter _
      have hnd2 : (((φ[u / 3]).map Prod.fst).filter τ).Nodup := hcl.2.filter _
      have hmem : ∀ v, v ∈ ((distinctVars φ).filter fun v ↦
          decide (u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true)) ↔
          v ∈ ((φ[u / 3]).map Prod.fst).filter τ := fun v ↦ by
        simp only [List.mem_filter, decide_eq_true_eq, mem_distinctVars, mem_occ, hj, true_and,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
        refine ⟨fun ⟨_, h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, h1, h2⟩⟩
        rw [CNF.vars, List.mem_map]
        rcases List.mem_map.mp h1 with ⟨l, hl, rfl⟩
        exact ⟨l, List.mem_flatten.mpr ⟨φ[u / 3], List.getElem_mem hj, hl⟩, rfl⟩
      rw [← List.toFinset_card_of_nodup hnd1,
        show ((distinctVars φ).filter fun v ↦
          decide (u / 3 ∈ ThreeExactCover.occ φ v ∧ τ v = true)).toFinset =
          (((φ[u / 3]).map Prod.fst).filter τ).toFinset from by
          ext v; simp only [List.mem_toFinset]; exact hmem v,
        List.toFinset_card_of_nodup hnd2, ← List.countP_eq_length_filter]
      have hcl_eq : ((φ[u / 3]).map Prod.fst).countP τ = (φ[u / 3]).countP (Literal.eval τ) := by
        rw [List.countP_map]
        exact List.countP_congr fun l hl ↦ by simp [Literal.eval, hpos_cl l hl]
      rw [hcl_eq, heval]
    · have h0 : varBase φ 0 = 3 * φ.length := by simp [varBase]
      have htot : varBase φ (distinctVars φ).length = 21 * φ.length := varBase_eq_total hs
      have hex : ∃ idx < (distinctVars φ).length, varBase φ idx ≤ u ∧ u < varBase φ (idx + 1) := by
        have : ∀ n ≤ (distinctVars φ).length, varBase φ 0 ≤ u → u < varBase φ n →
            ∃ idx < n, varBase φ idx ≤ u ∧ u < varBase φ (idx + 1) := by
          intro n; induction n with
          | zero => intro _ h1 h2; omega
          | succ k ih =>
            intro hk h1 h2
            by_cases hku : varBase φ k ≤ u
            · exact ⟨k, Nat.lt_succ_self k, hku, h2⟩
            · obtain ⟨idx, hidx, hlo, hhi⟩ := ih (by omega) h1 (by omega)
              exact ⟨idx, hidx.trans (Nat.lt_succ_self k), hlo, hhi⟩
        exact this (distinctVars φ).length le_rfl (by omega) (by omega)
      rcases hex with ⟨idx, hidx, hlo, hhi⟩
      set v := (distinctVars φ)[idx]
      have hp_L : (v, idx) ∈ L := mem_zipIdx_of_getElem hidx
      have hsum_fin : (L.map (fun q ↦ (Df q).countP (fun S ↦ decide (u ∈ S)))).sum =
          ∑ q ∈ L.toFinset, (Df q).countP (fun S ↦ decide (u ∈ S)) := by
        rw [← List.sum_toFinset _ (nodup_zipIdx _)]
      rw [hsum_fin, Finset.sum_eq_single (v, idx)]
      · have hsucc : varBase φ (idx + 1) =
            varBase φ idx + 6 * (ThreeExactCover.occ φ v).length := varBase_succ hidx
        have hv := (hp_mem (v, idx) hp_L).2.2
        have hlt_b : ∀ j ∈ ThreeExactCover.occ φ v, 3 * j + 2 < varBase φ idx := fun j hj ↦ by
          have := (mem_occ.mp hj).1; simp only [varBase]; omega
        dsimp [Df]; split_ifs
        · have := (gadgetTrue_props (occ_bounds hs hv) (nodup_occ φ v) hlt_b).2.2.1
            (u - varBase φ idx) (by dsimp only; omega)
          rwa [Nat.add_sub_cancel' hlo] at this
        · have := (gadgetFalse_props (base := varBase φ idx) (occ_bounds hs hv)).2.2.1
            (u - varBase φ idx) (by dsimp only; omega)
          rwa [Nat.add_sub_cancel' hlo] at this
      · intro q hq hne_q
        have hq' := List.mem_toFinset.mp hq
        have hne_i : q.2 ≠ idx := fun heq ↦ by
          apply hne_q
          rcases hp_mem q hq' with ⟨_, hg, _⟩
          rw [heq, List.getElem?_eq_getElem hidx] at hg
          exact Prod.ext (Option.some.inj hg.symm) heq
        have hlt_bq : ∀ j ∈ ThreeExactCover.occ φ q.1, 3 * j + 2 < varBase φ q.2 := fun j hj ↦ by
          have := (mem_occ.mp hj).1; simp only [varBase]; omega
        have hq_lt := (hp_mem q hq').1
        have hsucc_q := varBase_succ hq_lt
        have hget_q' := (hp_mem q hq').2.1
        rw [List.getElem?_eq_getElem hq_lt] at hget_q'
        have hget_q : (distinctVars φ)[q.2] = q.1 := Option.some.inj hget_q'
        rw [hget_q] at hsucc_q
        have hvq := (hp_mem q hq').2.2
        rcases Nat.lt_or_gt_of_ne hne_i with hlt | hgt
        · have hle : varBase φ q.2 + 6 * (ThreeExactCover.occ φ q.1).length ≤ u := by
            rw [← hsucc_q]; exact (varBase_mono (Nat.succ_le_of_lt hlt)).trans hlo
          dsimp [Df]; split_ifs
          · exact (gadgetTrue_props (occ_bounds hs hvq) (nodup_occ φ q.1) hlt_bq).2.2.2.2.2 u hle
          · exact (gadgetFalse_props (occ_bounds hs hvq)).2.2.2.2 u hle
        · have hlt_u : u < varBase φ q.2 := hhi.trans_le (varBase_mono (Nat.succ_le_of_lt hgt))
          dsimp [Df]; split_ifs
          · exact (gadgetTrue_props (occ_bounds hs hvq) (nodup_occ φ q.1) hlt_bq).2.2.2.2.1 u hlt_u
              (fun j hj c hc ↦ by have := (mem_occ.mp hj).1; omega)
          · exact (gadgetFalse_props (occ_bounds hs hvq)).2.2.2.1 u hlt_u
      · intro hnot; exact absurd (List.mem_toFinset.mpr hp_L) hnot

/-- Exact correctness of `reduce3Reg`: `reduce3Reg φ ∈ ThreeExactCoverRegular ↔
φ ∈ PositiveOneInExactThreeSATThree`. -/
theorem reduce3Reg_mem_iff (φ : CNF ℕ) :
    reduce3Reg φ ∈ ThreeExactCoverRegular ↔ φ ∈ PositiveOneInExactThreeSATThree := by
  rw [PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck]
  by_cases hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · exact ⟨fun h ↦ ⟨hs, oneSatisfiable_of_mem hs h⟩, fun h ↦ mem_of_oneSatisfiable hs h.2⟩
  · simpa [reduce3Reg, hs] using noInstance_notMem

/-- Structural regularity for ALL outputs of `reduce3Reg φ`: `3`-uniform, `3`-regular, contiguous
universe `[0, n')`, `m' = n'`, and `3 ∣ n'` with `n' ≥ 6`. -/
theorem reduce3Reg_always_regular (φ : CNF ℕ) :
    let C := reduce3Reg φ
    C.Nodup ∧ (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧
    (∀ u ∈ C.flatten, C.countP (fun S ↦ decide (u ∈ S)) = 3) ∧
    (∀ u, u ∈ C.flatten ↔ u < C.length) ∧ 3 ∣ C.length ∧ 6 ≤ C.length := by
  unfold reduce3Reg
  split_ifs with hs hne
  · rcases yesInstance_regular with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, fun u ↦ by rw [h5]; exact h4 u, by omega, by omega⟩
  · have hne' : φ.isEmpty = false := Bool.eq_false_iff.mpr hne
    have hreg := reduce3Reg_regular hs hne'
    have hC : reduce3Reg φ = (distinctVars φ).zipIdx.flatMap fun p ↦
        varGadget (varBase φ p.2) (ThreeExactCover.occ φ p.1) := by
      simp [reduce3Reg, hs, hne']
    rw [hC] at hreg
    have hpos : 1 ≤ φ.length := by
      cases φ with
      | nil => simp at hne
      | cons _ _ => simp
    exact ⟨hreg.1, hreg.2.1, hreg.2.2.1, fun u ↦ by rw [hreg.2.2.2.2]; exact hreg.2.2.2.1 u,
      ⟨7 * φ.length, by omega⟩, by omega⟩
  · rcases noInstance_regular with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, fun u ↦ by rw [h5]; exact h4 u, by omega, by omega⟩

end ThreeExactCoverRegular

/-- `PositiveOneInExactThreeSATThree` reduces in polynomial time to `ThreeExactCoverRegular`. -/
theorem polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeExactCoverRegular :
    PolyTimeReducible encCNF encNatSetList
      PositiveOneInExactThreeSATThree ThreeExactCoverRegular :=
  ⟨ThreeExactCoverRegular.reduce3Reg, ThreeExactCoverRegular.computableInPolyTime_reduce3Reg,
    fun φ ↦ (ThreeExactCoverRegular.reduce3Reg_mem_iff φ).symm⟩

/-- `ThreeExactCoverRegular` is `NP`-hard. -/
theorem ThreeExactCoverRegular_npHard : NPHard encNatSetList ThreeExactCoverRegular :=
  PositiveOneInExactThreeSATThree_npHard.trans
    polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeExactCoverRegular

/-- **3-regular Exact Cover by 3-sets (`3XC-3`) is `NP`-complete.** -/
theorem ThreeExactCoverRegular_npComplete : NPComplete encNatSetList ThreeExactCoverRegular :=
  ⟨ThreeExactCoverRegular.ThreeExactCoverRegular_mem_NP, ThreeExactCoverRegular_npHard⟩

end Cslib.Complexity
