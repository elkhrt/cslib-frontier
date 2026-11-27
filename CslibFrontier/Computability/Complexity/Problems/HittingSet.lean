/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Hitting Set and Set-System Incidence Duality

Unweighted **Hitting Set** (`Cslib.Complexity.HittingSet`) over the shared binary-labeled
set-system representation `Cslib.Complexity.SetSystem` (`Cslib.Complexity.encSetSystem`), together
with polynomial-time incidence transposition (`Cslib.Complexity.SetSystem.transpose`) witnessing
exact duality between `SetCover` and `HittingSet`
.

An instance `(S, k)` belongs to `Cslib.Complexity.HittingSet` when at most `k` ground elements
selected by index `Fin S.ground.length` intersect every candidate subset `A ∈ S.sets`. Incidence
transposition maps `S` to `S.transpose`, whose ground list is `List.range S.sets.length` and whose
candidate subsets record, for each `x ∈ S.ground`, the indices `i < S.sets.length` with
`x ∈ S.sets[i]`. A single transposition exchanges covering and hitting in both directions:

* `(S, k) ∈ HittingSet ↔ (S.transpose, k) ∈ SetCover`, yielding a polynomial-time many-one
  reduction `PolyTimeReducible encHittingSet encSetCover HittingSet SetCover` and transferring the
  greedy `(1 + ln |S.sets|)`-approximation guarantee (`greedyHittingIndices_length_le_one_add_log`).
* `(S, k) ∈ SetCover ↔ (S.transpose, k) ∈ HittingSet`, yielding the converse polynomial-time
  many-one reduction `PolyTimeReducible encSetCover encHittingSet SetCover HittingSet`.

## Main definitions

* `Cslib.Complexity.encHittingSet`: framed binary pair encoding of `(S : SetSystem) × (k : ℕ)`.
* `Cslib.Complexity.SetSystem.IsHittingSet`, `Cslib.Complexity.SetSystem.Hittable`,
  `Cslib.Complexity.SetSystem.optHittingSetSize`: hitting-set predicate, hittability, and minimum
  hitting-set cardinality.
* `Cslib.Complexity.SetSystem.transpose`: incidence-transpose `SetSystem` exchanging ground
  elements and candidate subsets.
* `Cslib.Complexity.SetSystem.greedyHittingIndices`: greedy hitting-set index selection obtained
  via `SetSystem.transpose`.
* `Cslib.Complexity.HittingSet`: unweighted Hitting Set decision problem.

## Main results

* `Cslib.Complexity.HittingSet_mem_NP`: membership of `HittingSet` in `NP` via subset witnesses.
* `Cslib.Complexity.SetSystem.computableInPolyTime_transpose`: polynomial-time computability of
  incidence transposition.
* `Cslib.Complexity.HittingSet_polyTimeReducible_SetCover`,
  `Cslib.Complexity.SetCover_polyTimeReducible_HittingSet`: mutual polynomial-time Karp reductions
  between `HittingSet` and `SetCover`.
* `Cslib.Complexity.SetSystem.greedyHittingIndices_isHittingSet`,
  `Cslib.Complexity.SetSystem.greedyHittingIndices_length_le_one_add_log`: greedy logarithmic
  approximation guarantee for minimum hitting sets.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- Framed pair encoding of a `SetSystem` (binary element labels) and binary target size `k`. -/
abbrev encHittingSet : SetSystem × ℕ ↪ List Bool := encPair encSetSystem encNat

namespace SetSystem

/-- A selection `H` of ground indices hits `S` when every candidate subset `A ∈ S.sets` contains
`S.ground[j]` for some `j ∈ H`. -/
@[expose] def IsHittingSet (S : SetSystem) (H : Finset (Fin S.ground.length)) : Prop :=
  ∀ A ∈ S.sets, ∃ j ∈ H, S.ground[j] ∈ A

/-- A set system is hittable when some finite selection of ground indices hits every subset in
`S.sets`. -/
@[expose] def Hittable (S : SetSystem) : Prop :=
  ∃ H : Finset (Fin S.ground.length), S.IsHittingSet H

/-- Boolean test for whether every subset in `S.sets` contains at least one element of
`S.ground`. -/
@[expose] def hittableBool (S : SetSystem) : Bool :=
  S.sets.all fun A => S.ground.any fun x => decide (x ∈ A)

theorem hittableBool_eq_true_iff (S : SetSystem) : S.hittableBool = true ↔ S.Hittable := by
  simp only [hittableBool, List.all_eq_true, List.any_eq_true, decide_eq_true_eq, Hittable,
    IsHittingSet]
  constructor
  · intro h
    refine ⟨Finset.univ, fun A hA => ?_⟩
    obtain ⟨x, hxG, hxA⟩ := h A hA
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hxG
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, hxA⟩
  · rintro ⟨H, hH⟩ A hA
    obtain ⟨j, -, hjA⟩ := hH A hA
    exact ⟨S.ground[j], List.getElem_mem j.isLt, hjA⟩

@[fun_prop] theorem computableInPolyTime_hittableBool :
    ComputableInPolyTime hittableBool encSetSystem encBool := by
  fun_prop [hittableBool]

/-- Boolean check that a list `J` of natural-number ground indices specifies a hitting set of
`S`. -/
@[expose] def isHittingSetList (S : SetSystem) (J : List ℕ) : Bool :=
  J.all (fun j => decide (j < S.ground.length)) &&
    S.sets.all fun A => J.any fun j => decide (S.ground.getD j 0 ∈ A)

theorem isHittingSetList_eq_true_iff (S : SetSystem) (J : List ℕ) :
    S.isHittingSetList J = true ↔
      (∀ j ∈ J, j < S.ground.length) ∧
        ∀ A ∈ S.sets, ∃ j ∈ J, ∃ hj : j < S.ground.length, S.ground[j]'hj ∈ A := by
  simp only [isHittingSetList, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hbound, hhit⟩
    refine ⟨hbound, fun A hA => ?_⟩
    obtain ⟨j, hjJ, hjA⟩ := hhit A hA
    have hj := hbound j hjJ
    rw [List.getD_eq_getElem _ _ hj] at hjA
    exact ⟨j, hjJ, hj, hjA⟩
  · rintro ⟨hbound, hhit⟩
    refine ⟨hbound, fun A hA => ?_⟩
    obtain ⟨j, hjJ, hj, hjA⟩ := hhit A hA
    exact ⟨j, hjJ, by rwa [List.getD_eq_getElem _ _ hj]⟩

private theorem isHittingSetList_toFinset_iff (S : SetSystem) {J : List ℕ}
    (hJ : ∀ j ∈ J, j < S.ground.length) :
    S.isHittingSetList J = true ↔
      S.IsHittingSet (Finset.univ.filter fun j : Fin S.ground.length => (j : ℕ) ∈ J.toFinset) := by
  rw [isHittingSetList_eq_true_iff]
  refine ⟨fun ⟨_, hhit⟩ A hA => ?_, fun hhit => ⟨hJ, fun A hA => ?_⟩⟩
  · obtain ⟨j, hjJ, hj, hjA⟩ := hhit A hA
    exact ⟨⟨j, hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, List.mem_toFinset.2 hjJ⟩, hjA⟩
  · obtain ⟨j, hjH, hjA⟩ := hhit A hA
    exact ⟨j, List.mem_toFinset.1 (Finset.mem_filter.1 hjH).2, j.isLt, hjA⟩

@[fun_prop] theorem computableInPolyTime_isHittingSetList :
    ComputableInPolyTime (fun p : SetSystem × List ℕ => p.1.isHittingSetList p.2)
      (encPair encSetSystem (encList encUnary)) encBool := by
  fun_prop [isHittingSetList]

/-- Minimum cardinality of a hitting set of `S` when `S.Hittable` holds (and `0` otherwise). -/
noncomputable def optHittingSetSize (S : SetSystem) : ℕ :=
  open Classical in
  if h : S.Hittable then
    Nat.find (⟨S.ground.length, h.choose, h.choose_spec,
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)⟩ :
      ∃ n : ℕ, ∃ H : Finset (Fin S.ground.length), S.IsHittingSet H ∧ H.card ≤ n)
  else 0

theorem optHittingSetSize_le {S : SetSystem} {H : Finset (Fin S.ground.length)}
    (hH : S.IsHittingSet H) : S.optHittingSetSize ≤ H.card := by
  classical
  have hS : S.Hittable := ⟨H, hH⟩
  rw [optHittingSetSize]
  split_ifs
  exact Nat.find_min' _ ⟨H, hH, le_rfl⟩

theorem optHittingSetSize_eq_zero_of_not_hittable {S : SetSystem} (hS : ¬ S.Hittable) :
    S.optHittingSetSize = 0 := by
  classical
  rw [optHittingSetSize]
  split_ifs
  rfl

theorem exists_isHittingSet_optHittingSetSize {S : SetSystem} (hS : S.Hittable) :
    ∃ H : Finset (Fin S.ground.length), S.IsHittingSet H ∧ H.card = S.optHittingSetSize := by
  classical
  rw [optHittingSetSize]
  split_ifs
  generalize_proofs h
  obtain ⟨H, hH, hcard⟩ := Nat.find_spec h
  exact ⟨H, hH, le_antisymm hcard (Nat.find_min' h ⟨H, hH, le_rfl⟩)⟩

theorem optHittingSetSize_le_iff {S : SetSystem} (hS : S.Hittable) {k : ℕ} :
    S.optHittingSetSize ≤ k ↔
      ∃ H : Finset (Fin S.ground.length), S.IsHittingSet H ∧ H.card ≤ k := by
  refine ⟨fun h => ?_, fun ⟨H, hH, hk⟩ => (optHittingSetSize_le hH).trans hk⟩
  obtain ⟨H, hH, hcard⟩ := exists_isHittingSet_optHittingSetSize hS
  exact ⟨H, hH, hcard ▸ h⟩

theorem le_optHittingSetSize_iff {S : SetSystem} (hS : S.Hittable) {k : ℕ} :
    k ≤ S.optHittingSetSize ↔
      ∀ H : Finset (Fin S.ground.length), S.IsHittingSet H → k ≤ H.card := by
  refine ⟨fun hk H hH => hk.trans (optHittingSetSize_le hH), fun h => ?_⟩
  obtain ⟨H, hH, hcard⟩ := exists_isHittingSet_optHittingSetSize hS
  rw [← hcard]
  exact h H hH

/-! ### Incidence transposition and Set Cover ↔ Hitting Set duality -/

/-- Incidence-transpose set system `S.transpose`: ground elements are subset indices
`0, …, S.sets.length - 1`, and for each `x ∈ S.ground` the corresponding subset collects all
indices `i < S.sets.length` such that `x ∈ S.sets[i]`. -/
@[expose] def transpose (S : SetSystem) : SetSystem where
  ground := List.range S.sets.length
  sets := S.ground.map fun x =>
    (List.range S.sets.length).filter fun i => decide (x ∈ S.sets.getD i [])

@[simp] theorem transpose_ground (S : SetSystem) :
    S.transpose.ground = List.range S.sets.length := rfl

@[simp] theorem transpose_ground_length (S : SetSystem) :
    S.transpose.ground.length = S.sets.length := List.length_range

@[simp] theorem transpose_sets_length (S : SetSystem) :
    S.transpose.sets.length = S.ground.length := List.length_map _

@[fun_prop] theorem computableInPolyTime_transpose :
    ComputableInPolyTime transpose encSetSystem encSetSystem := by
  have hground_u : ComputableInPolyTime (fun S : SetSystem => List.range S.sets.length)
      encSetSystem (encList encUnary) := by fun_prop
  have hground : ComputableInPolyTime (fun S : SetSystem => List.range S.sets.length)
      encSetSystem (encList encNat) := by
    simpa only [List.map_id'] using
      mapWithInput (f := fun _ (n : ℕ) => n) hground_u
        (unary_to_binary.comp (snd encSetSystem encUnary))
  have hfilt_u : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        (List.range p.1.sets.length).filter fun i => decide (p.2 ∈ p.1.sets.getD i []))
      (encPair encSetSystem encNat) (encList encUnary) := by fun_prop
  have hfilt : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        (List.range p.1.sets.length).filter fun i => decide (p.2 ∈ p.1.sets.getD i []))
      (encPair encSetSystem encNat) (encList encNat) := by
    simpa only [List.map_id'] using
      mapWithInput (f := fun _ (n : ℕ) => n) hfilt_u
        (unary_to_binary.comp (snd (encPair encSetSystem encNat) encUnary))
  have hsets : ComputableInPolyTime
      (fun S : SetSystem => S.ground.map fun x =>
        (List.range S.sets.length).filter fun i => decide (x ∈ S.sets.getD i []))
      encSetSystem encNatSetList :=
    mapWithInput (by fun_prop) hfilt
  exact computableInPolyTime_setSystemMk hground hsets

/-- Canonical index equivalence `Fin S.ground.length ≃ Fin S.transpose.sets.length`. -/
@[expose] def groundIdxToTransposeSetIdx (S : SetSystem) :
    Fin S.ground.length ≃ Fin S.transpose.sets.length where
  toFun j := ⟨j.1, by simp [transpose]⟩
  invFun j := ⟨j.1, by simpa [transpose] using j.2⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

/-- Canonical index equivalence `Fin S.sets.length ≃ Fin S.transpose.ground.length`. -/
@[expose] def setIdxToTransposeGroundIdx (S : SetSystem) :
    Fin S.sets.length ≃ Fin S.transpose.ground.length where
  toFun i := ⟨i.1, by simp [transpose]⟩
  invFun i := ⟨i.1, by simpa [transpose] using i.2⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

theorem transpose_isCover_iff_isHittingSet (S : SetSystem) (H : Finset (Fin S.ground.length)) :
    S.transpose.IsCover (H.map (groundIdxToTransposeSetIdx S).toEmbedding) ↔ S.IsHittingSet H := by
  constructor
  · intro hcov A hA
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hA
    obtain ⟨j', hj'C, hij⟩ := hcov i (List.mem_range.2 hi)
    obtain ⟨j, hjH, rfl⟩ := Finset.mem_map.1 hj'C
    have hij' : i ∈ S.transpose.sets[j.1]'(by simp [transpose, j.isLt]) := hij
    simp only [transpose, List.getElem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hij'
    have hdec := hij'.2
    rw [List.getD_eq_getElem _ _ hi] at hdec
    exact ⟨j, hjH, hdec⟩
  · intro hhit i hi_mem
    have hi : i < S.sets.length := List.mem_range.1 hi_mem
    obtain ⟨j, hjH, hjA⟩ := hhit (S.sets[i]'hi) (List.getElem_mem hi)
    refine ⟨groundIdxToTransposeSetIdx S j, Finset.mem_map_of_mem _ hjH, ?_⟩
    change i ∈ S.transpose.sets[j.1]'(by simp [transpose, j.isLt])
    simp only [transpose, List.getElem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hi, by rwa [List.getD_eq_getElem _ _ hi]⟩

theorem transpose_isHittingSet_iff_isCover (S : SetSystem) (C : Finset (Fin S.sets.length)) :
    S.transpose.IsHittingSet (C.map (setIdxToTransposeGroundIdx S).toEmbedding) ↔ S.IsCover C := by
  constructor
  · intro hhit u hu
    have hB_mem : ((List.range S.sets.length).filter
        fun i => decide (u ∈ S.sets.getD i [])) ∈ S.transpose.sets :=
      List.mem_map_of_mem hu
    obtain ⟨i', hi'C, hi'B⟩ := hhit _ hB_mem
    obtain ⟨i, hiC, rfl⟩ := Finset.mem_map.1 hi'C
    have hi'B0 : S.transpose.ground[i.1]'(by simp [transpose, i.isLt]) ∈
        (List.range S.sets.length).filter (fun idx => decide (u ∈ S.sets.getD idx [])) := hi'B
    simp only [transpose, List.getElem_range, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hi'B0
    have hdec := hi'B0.2
    rw [List.getD_eq_getElem _ _ i.isLt] at hdec
    exact ⟨i, hiC, hdec⟩
  · intro hcov B hB
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hB
    obtain ⟨i, hiC, hui⟩ := hcov u hu
    refine ⟨setIdxToTransposeGroundIdx S i, Finset.mem_map_of_mem _ hiC, ?_⟩
    change S.transpose.ground[i.1]'(by simp [transpose, i.isLt]) ∈
      (List.range S.sets.length).filter fun idx => decide (u ∈ S.sets.getD idx [])
    simp only [transpose, List.getElem_range, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨i.isLt, by rwa [List.getD_eq_getElem _ _ i.isLt]⟩

theorem transpose_coverable_iff_hittable (S : SetSystem) :
    S.transpose.Coverable ↔ S.Hittable := by
  constructor
  · rintro ⟨C', hC'⟩
    let H := C'.map (groundIdxToTransposeSetIdx S).symm.toEmbedding
    have hmap : H.map (groundIdxToTransposeSetIdx S).toEmbedding = C' := by
      ext x
      simp [H]
    rw [← hmap] at hC'
    exact ⟨H, (transpose_isCover_iff_isHittingSet S H).1 hC'⟩
  · rintro ⟨H, hH⟩
    exact ⟨_, (transpose_isCover_iff_isHittingSet S H).2 hH⟩

theorem transpose_optCoverSize_eq_optHittingSetSize (S : SetSystem) :
    S.transpose.optCoverSize = S.optHittingSetSize := by
  by_cases hH : S.Hittable
  · have hC : S.transpose.Coverable := (transpose_coverable_iff_hittable S).2 hH
    apply le_antisymm
    · obtain ⟨H, hH_hit, hH_card⟩ := exists_isHittingSet_optHittingSetSize hH
      have hcov := (transpose_isCover_iff_isHittingSet S H).2 hH_hit
      exact (optCoverSize_le hcov).trans_eq ((Finset.card_map _).trans hH_card)
    · obtain ⟨C', hC'_cov, hC'_card⟩ := exists_isCover_optCoverSize hC
      let H := C'.map (groundIdxToTransposeSetIdx S).symm.toEmbedding
      have hmap : H.map (groundIdxToTransposeSetIdx S).toEmbedding = C' := by
        ext x
        simp [H]
      have hhit : S.IsHittingSet H :=
        (transpose_isCover_iff_isHittingSet S H).1 (hmap.symm ▸ hC'_cov)
      exact (optHittingSetSize_le hhit).trans_eq ((Finset.card_map _).trans hC'_card)
  · have hnotC : ¬ S.transpose.Coverable := fun hC => hH ((transpose_coverable_iff_hittable S).1 hC)
    rw [optCoverSize_eq_zero_of_not_coverable hnotC,
      optHittingSetSize_eq_zero_of_not_hittable hH]

/-- Greedy hitting-set ground indices computed by running `SetCover.greedy` on `S.transpose`. -/
@[expose] noncomputable def greedyHittingIndices (S : SetSystem) : List (Fin S.ground.length) :=
  S.transpose.greedyIndices.map (groundIdxToTransposeSetIdx S).symm

theorem greedyHittingIndices_isHittingSet {S : SetSystem} (hS : S.Hittable) :
    S.IsHittingSet S.greedyHittingIndices.toFinset := by
  have hC : S.transpose.Coverable := (transpose_coverable_iff_hittable S).2 hS
  have hcov := S.transpose.greedyIndices_isCover hC
  refine (transpose_isCover_iff_isHittingSet S S.greedyHittingIndices.toFinset).1 ?_
  have heq : S.greedyHittingIndices.toFinset.map (groundIdxToTransposeSetIdx S).toEmbedding =
      S.transpose.greedyIndices.toFinset := by
    ext x
    simp [greedyHittingIndices]
  rwa [heq]

theorem greedyHittingIndices_length_le_one_add_log {S : SetSystem} (hS : S.Hittable) :
    (S.greedyHittingIndices.length : ℝ) ≤
      (1 + Real.log S.sets.length) * S.optHittingSetSize := by
  have hC : S.transpose.Coverable := (transpose_coverable_iff_hittable S).2 hS
  have hbound := S.transpose.greedyIndices_length_le_one_add_log hC
  have hcard : S.transpose.ground.toFinset.card = S.sets.length := by
    rw [transpose_ground, List.toFinset_card_of_nodup List.nodup_range, List.length_range]
  simpa only [greedyHittingIndices, List.length_map, hcard,
    transpose_optCoverSize_eq_optHittingSetSize] using hbound

end SetSystem

/-- **Unweighted Hitting Set**: pairs `(S, k)` admitting a selection of at most `k` ground indices
hitting every subset in `S.sets`. -/
@[expose] def HittingSet : Set (SetSystem × ℕ) :=
  {p | ∃ H : Finset (Fin p.1.ground.length), p.1.IsHittingSet H ∧ H.card ≤ p.2}

theorem mem_HittingSet_iff {S : SetSystem} {k : ℕ} :
    (S, k) ∈ HittingSet ↔ ∃ H : Finset (Fin S.ground.length), S.IsHittingSet H ∧ H.card ≤ k :=
  Iff.rfl

theorem mem_HittingSet_iff_optHittingSetSize {S : SetSystem} {k : ℕ} :
    (S, k) ∈ HittingSet ↔ S.Hittable ∧ S.optHittingSetSize ≤ k := by
  refine ⟨fun ⟨H, hH, hk⟩ => ⟨⟨H, hH⟩, (SetSystem.optHittingSetSize_le hH).trans hk⟩,
    fun ⟨hS, hk⟩ => (SetSystem.optHittingSetSize_le_iff hS).1 hk⟩

theorem transpose_mem_SetCover_iff {S : SetSystem} {k : ℕ} :
    (S.transpose, k) ∈ SetCover ↔ (S, k) ∈ HittingSet := by
  rw [mem_SetCover_iff_optCoverSize, mem_HittingSet_iff_optHittingSetSize,
    SetSystem.transpose_coverable_iff_hittable,
    SetSystem.transpose_optCoverSize_eq_optHittingSetSize]

theorem transpose_mem_HittingSet_iff {S : SetSystem} {k : ℕ} :
    (S.transpose, k) ∈ HittingSet ↔ (S, k) ∈ SetCover := by
  simp only [mem_HittingSet_iff, mem_SetCover_iff]
  constructor
  · rintro ⟨H', hH', hk⟩
    let C := H'.map (SetSystem.setIdxToTransposeGroundIdx S).symm.toEmbedding
    have hmap : C.map (SetSystem.setIdxToTransposeGroundIdx S).toEmbedding = H' := by
      ext x
      simp only [C, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact ⟨C, (SetSystem.transpose_isHittingSet_iff_isCover S C).1 (hmap.symm ▸ hH'),
      (Finset.card_map _).trans_le hk⟩
  · rintro ⟨C, hC, hk⟩
    exact ⟨C.map (SetSystem.setIdxToTransposeGroundIdx S).toEmbedding,
      (SetSystem.transpose_isHittingSet_iff_isCover S C).2 hC, (Finset.card_map _).trans_le hk⟩

/-- Unweighted Hitting Set is in `NP` via subset witnesses over `List.range S.ground.length`. -/
theorem HittingSet_mem_NP : HittingSet ∈ NP encHittingSet := by
  let vs : SetSystem × ℕ → List ℕ := fun p => List.range p.1.ground.length
  let check : (SetSystem × ℕ) × List ℕ → Bool := fun q =>
    decide (q.2.length ≤ q.1.2) && q.1.1.isHittingSetList q.2
  have hvs : ComputableInPolyTime vs encHittingSet (encList encUnary) := by fun_prop
  have hcheck : ComputableInPolyTime check
      (encPair encHittingSet (encList encUnary)) encBool := by
    have hlen : ComputableInPolyTime (fun q : (SetSystem × ℕ) × List ℕ => q.2.length)
        (encPair encHittingSet (encList encUnary)) encNat :=
      ComputableInPolyTime.unary_to_binary.comp
        ((ComputableInPolyTime.length_list encUnary).comp (snd encHittingSet (encList encUnary)))
    exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.binary_le' hlen (by fun_prop))
      (by fun_prop)
  let P : (SetSystem × ℕ) → Finset ℕ → Prop := fun p J =>
    p.1.IsHittingSet (Finset.univ.filter fun j : Fin p.1.ground.length => (j : ℕ) ∈ J) ∧
      J.card ≤ p.2
  have hP : ∀ (p : SetSystem × ℕ) (l : List ℕ), l.Nodup → (∀ j ∈ l, j ∈ vs p) →
      (check (p, l) = true ↔ P p l.toFinset) := by
    intro p l hnd hmem
    have hlt : ∀ j ∈ l, j < p.1.ground.length := fun j hj => List.mem_range.1 (hmem j hj)
    simp only [check, P, Bool.and_eq_true, decide_eq_true_eq,
      SetSystem.isHittingSetList_toFinset_iff p.1 hlt, List.toFinset_card_of_nodup hnd, and_comm]
  have hmem := mem_NP_of_subsetWitness (encγ := encUnary) (P := P) hvs hcheck hP
  have hEq : HittingSet = {p | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ vs p) ∧ P p S} := by
    ext ⟨S, k⟩
    constructor
    · rintro ⟨H, hhit, hcard⟩
      refine ⟨H.image Fin.val, fun x hx => ?_, ?_, Finset.card_image_le.trans hcard⟩
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
        exact List.mem_range.2 j.isLt
      · have hfilt : Finset.univ.filter
            (fun j : Fin S.ground.length => (j : ℕ) ∈ H.image Fin.val) = H := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
          exact ⟨fun ⟨j', hj', hjj⟩ => Fin.ext hjj ▸ hj', fun hj => ⟨j, hj, rfl⟩⟩
        rwa [hfilt]
    · rintro ⟨J, -, hhit, hcard⟩
      exact ⟨_, hhit, (card_filter_mem_le_card J).trans hcard⟩
  rwa [hEq]

/-- Polynomial-time many-one reduction from `HittingSet` to `SetCover` via incidence
transposition (`(S, k) ↦ (S.transpose, k)`). -/
theorem HittingSet_polyTimeReducible_SetCover :
    PolyTimeReducible encHittingSet encSetCover HittingSet SetCover :=
  ⟨fun p => (p.1.transpose, p.2), by fun_prop, fun ⟨_, _⟩ => transpose_mem_SetCover_iff.symm⟩

/-- Polynomial-time many-one reduction from `SetCover` to `HittingSet` via incidence
transposition (`(S, k) ↦ (S.transpose, k)`). -/
theorem SetCover_polyTimeReducible_HittingSet :
    PolyTimeReducible encSetCover encHittingSet SetCover HittingSet :=
  ⟨fun p => (p.1.transpose, p.2), by fun_prop, fun ⟨_, _⟩ => transpose_mem_HittingSet_iff.symm⟩

end Cslib.Complexity
