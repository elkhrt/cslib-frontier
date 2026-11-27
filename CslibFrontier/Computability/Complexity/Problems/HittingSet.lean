/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.PCP.Approximation.SetCover.LundYannakakis
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.SelectDistinct
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD

/-!
# Hitting Set: Dual Equivalence with Set Cover, Dominating Set Reduction, and `W[2]` Membership

Under standard Lean axioms, this module formalizes the classic **Hitting Set** problem over
`Cslib.Complexity.SetSystem`, establishes its exact polynomial-time, FPT, and
approximation-preserving duality with `Cslib.Complexity.SetCover`, reduces `DominatingSet` to
`SetCover` and `HittingSet`, and proves that `HittingSet` and `SetCover` belong to **`W[2]`**
(see `CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.HittingSet` for matching
`W[2]`-hardness):

1. **Hitting Set (`IsHittingSet`, `HittingSet`, `Hittable`, `optHittingSize`, `minHittingSet`)**:
   given `(S, k)` (`S : SetSystem`), select at most `k` elements of `S.ground` intersecting every
   candidate set `A ∈ S.sets`.
2. **Incidence transposition (`transposeSetSystem`)**: swapping ground elements and candidate-set
   indices gives a single involutive polynomial-time, parameter-preserving, optimum-preserving, and
   ratio-1 approximation-preserving reduction in both directions (`SetCover ↔ HittingSet`),
   yielding `NP`-completeness and unconditional constant-factor `NP`-inapproximability of
   `HittingSet`.
3. **Closed-neighborhood reduction (`dominatingSetToSetSystem`, `dominatingSetToHittingSystem`)**:
   maps any graph `G` to a `Coverable` / `Hittable` set system whose covers and hitting sets of
   size `≤ k` correspond 1-to-1 to dominating sets of `G` of size `≤ k`.
4. **Membership in `W[2]` and specification-driven set systems (`hittingSet_mem_W`,
   `setCover_mem_W`, `ofSpecSetSystem`)**: membership in `W[2]` via a two-layer `AND`-of-`OR`s
   `WeftCircuit 2 2` with `k` dummy padding inputs, together with a reusable polynomial-time
   specification-driven `SetSystem` builder.

## Main definitions

* `Cslib.Complexity.encHittingSet`,
  `Cslib.Complexity.IsHittingSet`, `Cslib.Complexity.HittingSet`,
  `Cslib.Complexity.Hittable`, `Cslib.Complexity.isHittingList`,
  `Cslib.Complexity.optHittingSize`,
  `Cslib.Complexity.minHittingSet`: Hitting Set decision and optimization carriers.
* `Cslib.Complexity.transposeSetSystem`: dual incidence transposition between
  `SetCover` and `HittingSet`.
* `Cslib.Complexity.dominatingSetToSetSystem`,
  `Cslib.Complexity.dominatingSetToHittingSystem`: closed-neighborhood reductions
  from `DominatingSet`.
* `Cslib.Complexity.ofSpecSetSystem`: generic specification-driven set-system
  constructor.

## Main results

* `Cslib.Complexity.transposeSetSystem_setCover_iff`,
  `Cslib.Complexity.transposeSetSystem_hittingSet_iff`,
  `Cslib.Complexity.approxPreservingReducible_setCover_hittingSet`: exact duality.
* `Cslib.Complexity.hittingSet_npComplete`,
  `Cslib.Complexity.P_eq_NP_of_hittingSet_approx_const`: `NP`-completeness and
  constant-factor inapproximability.
* `Cslib.Complexity.dominatingSetToHittingSystem_mem_iff`: exact dominating-set to
  hitting-set reduction.
* `Cslib.Complexity.hittingSet_mem_W`,
  `Cslib.Complexity.setCover_mem_W`: membership of `HittingSet` and `SetCover` in
  `W[2]`.
* `Cslib.Complexity.mem_hittingSet_ofSpecSetSystem_iff`,
  `Cslib.Complexity.computableInPolyTime_ofSpecSetSystem`: correctness and
  polynomial-time certificate for `ofSpecSetSystem`.

## Tags

hitting set, set cover, dominating set, W[2] membership, approximation-preserving reduction
-/

public section

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Turing.MultiTapeTM ComputableInPolyTime

namespace Cslib.Complexity

/-! ### 1. Hitting Set Decision and Optimization Definitions -/

/-- Framed binary encoding of `(SetSystem, k)` instances of `HittingSet`. -/
abbrev encHittingSet : SetSystem × ℕ ↪ List Bool := encSetCover

/-- A finite set `H` is a hitting set of `S : SetSystem` when every element of `H` belongs to
`S.ground` and every set `A ∈ S.sets` intersects `H`. -/
@[expose] def IsHittingSet (S : SetSystem) (H : Finset ℕ) : Prop :=
  (∀ u ∈ H, u ∈ S.ground) ∧ ∀ A ∈ S.sets, ∃ u ∈ H, u ∈ A

/-- **Hitting Set**: pairs `(S, k)` admitting a hitting set `H` of cardinality at most `k`. -/
@[expose] def HittingSet : Set (SetSystem × ℕ) :=
  {p | ∃ H : Finset ℕ, IsHittingSet p.1 H ∧ H.card ≤ p.2}

/-- Unfolding characterization of `HittingSet`. -/
theorem mem_hittingSet_iff {S : SetSystem} {k : ℕ} :
    (S, k) ∈ HittingSet ↔ ∃ H : Finset ℕ, IsHittingSet S H ∧ H.card ≤ k := by
  unfold IsHittingSet HittingSet; rfl

/-- A set system `S` is hittable when some subset of `S.ground` hits every set in `S.sets`. -/
@[expose] def Hittable (S : SetSystem) : Prop :=
  ∃ H : Finset ℕ, IsHittingSet S H

/-- Executable Boolean test for `Hittable S`. -/
@[expose] def hittableBool (S : SetSystem) : Bool :=
  S.sets.all fun A => S.ground.any fun u => decide (u ∈ A)

/-- `hittableBool S` evaluates to `true` if and only if `Hittable S`. -/
theorem hittableBool_eq_true_iff (S : SetSystem) :
    hittableBool S = true ↔ Hittable S := by
  simp only [hittableBool, List.all_eq_true, List.any_eq_true, decide_eq_true_eq, Hittable,
    IsHittingSet]
  constructor
  · intro h
    refine ⟨S.ground.toFinset, fun _ hu => List.mem_toFinset.1 hu, fun A hA => ?_⟩
    obtain ⟨u, huG, huA⟩ := h A hA
    exact ⟨u, List.mem_toFinset.2 huG, huA⟩
  · rintro ⟨H, hHG, hcov⟩ A hA
    obtain ⟨u, huH, huA⟩ := hcov A hA
    exact ⟨u, hHG u huH, huA⟩

/-- Polynomial-time certificate for `hittableBool`. -/
@[fun_prop]
theorem computableInPolyTime_hittableBool :
    ComputableInPolyTime hittableBool encSetSystem encBool := by
  unfold hittableBool
  fun_prop

/-- Executable Boolean verifier checking whether a list `L` of elements forms a hitting set of
`S`. -/
@[expose] def isHittingList (S : SetSystem) (L : List ℕ) : Bool :=
  L.all (fun u => decide (u ∈ S.ground)) &&
    S.sets.all fun A => L.any fun u => decide (u ∈ A)

/-- Correctness of `isHittingList`. -/
theorem isHittingList_eq_true_iff (S : SetSystem) (L : List ℕ) :
    isHittingList S L = true ↔ IsHittingSet S L.toFinset := by
  simp [isHittingList, IsHittingSet, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq]

/-- Polynomial-time certificate for `isHittingList`. -/
@[fun_prop]
theorem computableInPolyTime_isHittingList :
    ComputableInPolyTime (fun p : SetSystem × List ℕ => isHittingList p.1 p.2)
      (encPair encSetSystem (encList encNat)) encBool := by
  unfold isHittingList
  fun_prop

/-- Minimum cardinality of a hitting set of `S` when `Hittable S` holds (and `0` otherwise). -/
noncomputable def optHittingSize (S : SetSystem) : ℕ := by
  classical
  exact if h : Hittable S then
    Nat.find (⟨h.choose.card, h.choose, h.choose_spec, le_rfl⟩ :
      ∃ n : ℕ, ∃ H : Finset ℕ, IsHittingSet S H ∧ H.card ≤ n)
  else 0

/-- Every hitting set of `S` has cardinality at least `optHittingSize S`. -/
theorem optHittingSize_le {S : SetSystem} {H : Finset ℕ} (hH : IsHittingSet S H) :
    optHittingSize S ≤ H.card := by
  classical
  have hS : Hittable S := ⟨H, hH⟩
  simp only [optHittingSize, hS, ↓reduceDIte]
  exact Nat.find_min' _ ⟨H, hH, le_rfl⟩

/-- Every hittable set system admits a hitting set of cardinality `optHittingSize S`. -/
theorem exists_isHittingSet_optHittingSize {S : SetSystem} (hS : Hittable S) :
    ∃ H : Finset ℕ, IsHittingSet S H ∧ H.card = optHittingSize S := by
  classical
  have hex : ∃ n : ℕ, ∃ H : Finset ℕ, IsHittingSet S H ∧ H.card ≤ n :=
    ⟨hS.choose.card, hS.choose, hS.choose_spec, le_rfl⟩
  obtain ⟨H, hH, hle⟩ := Nat.find_spec hex
  have heq : optHittingSize S = Nat.find hex := by simp only [optHittingSize, hS, ↓reduceDIte]
  exact ⟨H, hH, le_antisymm (heq ▸ hle) (optHittingSize_le hH)⟩

/-- On hittable set systems, `(S, k) ∈ HittingSet` iff `optHittingSize S ≤ k`. -/
theorem mem_hittingSet_iff_optHittingSize_le {S : SetSystem} (hS : Hittable S) {k : ℕ} :
    (S, k) ∈ HittingSet ↔ optHittingSize S ≤ k := by
  rw [mem_hittingSet_iff]
  constructor
  · rintro ⟨H, hH, hle⟩
    exact (optHittingSize_le hH).trans hle
  · intro hle
    obtain ⟨H, hH, hcard⟩ := exists_isHittingSet_optHittingSize hS
    exact ⟨H, hH, hcard.le.trans hle⟩

/-- Minimization problem packaging of `HittingSet` on hittable set systems. -/
@[expose] noncomputable def minHittingSet : MinOptProblem SetSystem (List ℕ) where
  IsValid := Hittable
  Feasible S L := isHittingList S L = true
  cost _ L := (L.length : ℝ)
  opt S := (optHittingSize S : ℝ)
  opt_le S L _ hL := by
    have hH := (isHittingList_eq_true_iff S L).1 hL
    have hle : optHittingSize S ≤ L.length := (optHittingSize_le hH).trans L.toFinset_card_le
    exact_mod_cast hle
  exists_opt S hS := by
    obtain ⟨H, hH, hcard⟩ := exists_isHittingSet_optHittingSize hS
    refine ⟨H.toList, (isHittingList_eq_true_iff S H.toList).2 ?_, ?_⟩
    · simpa [Finset.toList_toFinset] using hH
    · simp [Finset.length_toList, hcard]

@[simp]
theorem minHittingSet_isValid (S : SetSystem) :
    minHittingSet.IsValid S = Hittable S := by
  unfold Hittable; rfl

@[simp]
theorem minHittingSet_feasible (S : SetSystem) (L : List ℕ) :
    minHittingSet.Feasible S L = (isHittingList S L = true) := rfl

@[simp]
theorem minHittingSet_cost (S : SetSystem) (L : List ℕ) :
    minHittingSet.cost S L = (L.length : ℝ) := rfl

@[simp]
theorem minHittingSet_opt (S : SetSystem) :
    minHittingSet.opt S = (optHittingSize S : ℝ) := by
  unfold optHittingSize; rfl

/-! ### 2. Incidence Transposition (`SetCover ↔ HittingSet`) -/

/-- Dual incidence transposition of a set system: ground elements become candidate-set indices
`0, …, |S.sets| -
  1`, and each `u ∈ S.ground` defines the set of indices `i` with `u ∈ S.sets[i]`. -/
@[expose] def transposeSetSystem (S : SetSystem) : SetSystem :=
  ⟨List.range S.sets.length,
    S.ground.map fun u => (List.range S.sets.length).filter fun i =>
      decide (u ∈ S.sets.getD i [])⟩

/-- Polynomial-time certificate for `transposeSetSystem`. -/
@[fun_prop]
theorem computableInPolyTime_transposeSetSystem :
    ComputableInPolyTime transposeSetSystem encSetSystem encSetSystem := by
  have hr : ComputableInPolyTime (fun S : SetSystem => List.range S.sets.length)
      encSetSystem (encList encNat) := by
    have h1 : ComputableInPolyTime (fun S : SetSystem => List.range S.sets.length)
        encSetSystem (encList encUnary) := by fun_prop
    have h2 : ComputableInPolyTime (List.map (fun n : ℕ => n))
        (encList encUnary) (encList encNat) := map unary_to_binary
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using h2.comp h1
  have hsets : ComputableInPolyTime
      (fun S : SetSystem => S.ground.map fun u =>
        (List.range S.sets.length).filter fun i => decide (u ∈ S.sets.getD i []))
      encSetSystem encNatSetList := by
    refine mapWithInput (by fun_prop) ?_
    refine filterWithInput (hr.comp (fst _ _)) ?_
    have hget := listGetD_binary (encA := encList encNat) (encL := encNatSetList) ([] : List ℕ)
      (by fun_prop : ComputableInPolyTime (fun q : (SetSystem × ℕ) × ℕ => q.1.1.sets)
        (encPair (encPair encSetSystem encNat) encNat) encNatSetList)
      (snd _ _)
    have hu : ComputableInPolyTime (fun q : (SetSystem × ℕ) × ℕ => q.1.2)
        (encPair (encPair encSetSystem encNat) encNat) encNat := (snd _ _).comp (fst _ _)
    exact (by fun_prop : ComputableInPolyTime (fun r : ℕ × List ℕ => decide (r.1 ∈ r.2))
      (encPair encNat (encList encNat)) encBool).comp (hu.prod hget)
  unfold transposeSetSystem
  exact computableInPolyTime_setSystemMk hr hsets

/-- `S` is `Coverable` if and only if `transposeSetSystem S` is `Hittable`. -/
theorem hittable_transposeSetSystem_iff_coverable (S : SetSystem) :
    Hittable (transposeSetSystem S) ↔ S.Coverable := by
  rw [← hittableBool_eq_true_iff, ← SetSystem.coverableBool_eq_true_iff]
  simp only [hittableBool, SetSystem.coverableBool, transposeSetSystem, List.all_map,
    Function.comp_def, List.all_eq_true, List.any_eq_true, List.mem_range, List.mem_filter,
    decide_eq_true_eq]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨i, _, _, hui⟩
    have hi : i < S.sets.length := by
      by_contra hge
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hge)] at hui
      cases hui
    rw [List.getD_eq_getElem _ _ hi] at hui
    exact ⟨S.sets[i], List.getElem_mem hi, hui⟩
  · rintro ⟨A, hA, hui⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hA
    exact ⟨i, hi, ⟨hi, by rwa [List.getD_eq_getElem _ _ hi]⟩⟩

/-- `(transposeSetSystem S, k)` belongs to `HittingSet` if and only if `(S, k) ∈ SetCover`. -/
theorem transposeSetSystem_setCover_iff (S : SetSystem) (k : ℕ) :
    (transposeSetSystem S, k) ∈ HittingSet ↔ (S, k) ∈ SetCover := by
  classical
  rw [mem_hittingSet_iff, mem_SetCover_iff]
  constructor
  · rintro ⟨H, ⟨hHG, hHcov⟩, hcard⟩
    let C : Finset (Fin S.sets.length) :=
      Finset.univ.filter fun i : Fin S.sets.length => i.1 ∈ H
    have hCcard : C.card ≤ H.card := by
      have himg : C.image Fin.val ⊆ H := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact (Finset.mem_filter.1 hi).2
      rw [← Finset.card_image_of_injective C Fin.val_injective]
      exact Finset.card_le_card himg
    refine ⟨C, fun u hu => ?_, hCcard.trans hcard⟩
    have hAu : ((List.range S.sets.length).filter fun i => decide (u ∈ S.sets.getD i [])) ∈
        (transposeSetSystem S).sets := List.mem_map_of_mem hu
    obtain ⟨i, hiH, hiF⟩ := hHcov _ hAu
    obtain ⟨hi_lt, hui⟩ := List.mem_filter.1 hiF
    have hi_lt' : i < S.sets.length := List.mem_range.1 hi_lt
    rw [decide_eq_true_eq, List.getD_eq_getElem _ _ hi_lt'] at hui
    exact ⟨⟨i, hi_lt'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hiH⟩, hui⟩
  · rintro ⟨C, hC, hcard⟩
    let H : Finset ℕ := C.image Fin.val
    refine ⟨H, ⟨?_, ?_⟩, Finset.card_image_le.trans hcard⟩
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hi
      exact List.mem_range.2 j.isLt
    · intro A hA
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hA
      obtain ⟨j, hjC, huj⟩ := hC u hu
      refine ⟨j.1, Finset.mem_image_of_mem _ hjC,
        List.mem_filter.2 ⟨List.mem_range.2 j.isLt, decide_eq_true ?_⟩⟩
      rwa [List.getD_eq_getElem _ _ j.isLt]

/-- `(transposeSetSystem S, k)` belongs to `SetCover` if and only if `(S, k) ∈ HittingSet`. -/
theorem transposeSetSystem_hittingSet_iff (S : SetSystem) (k : ℕ) :
    (transposeSetSystem S, k) ∈ SetCover ↔ (S, k) ∈ HittingSet := by
  classical
  rw [mem_SetCover_iff, mem_hittingSet_iff]
  constructor
  · rintro ⟨C, hC, hcard⟩
    have hlen : (transposeSetSystem S).sets.length = S.ground.length := by
      simp [transposeSetSystem]
    let H : Finset ℕ := C.image fun i => S.ground[i.1]'(i.isLt.trans_eq hlen)
    refine ⟨H, ⟨?_, ?_⟩, Finset.card_image_le.trans hcard⟩
    · intro u hu
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hu
      exact List.getElem_mem _
    · intro A hA
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hA
      have hjG : j ∈ (transposeSetSystem S).ground := List.mem_range.2 hj
      obtain ⟨i, hiC, hij⟩ := hC j hjG
      have hi_lt : i.1 < S.ground.length := i.isLt.trans_eq hlen
      have hset_eq : (transposeSetSystem S).sets[i] =
          (List.range S.sets.length).filter fun idx =>
            decide ((S.ground[i.1]'hi_lt) ∈ S.sets.getD idx []) := by
        rw [Fin.getElem_fin]
        simp [transposeSetSystem]
      rw [hset_eq, List.mem_filter, decide_eq_true_eq, List.getD_eq_getElem _ _ hj] at hij
      exact ⟨S.ground[i.1]'hi_lt, Finset.mem_image_of_mem _ hiC, hij.2⟩
  · rintro ⟨H, ⟨hHG, hHcov⟩, hcard⟩
    have hlen : (transposeSetSystem S).sets.length = S.ground.length := by
      simp [transposeSetSystem]
    have hidx_lt (u : ℕ) (hu : u ∈ H) : S.ground.idxOf u < (transposeSetSystem S).sets.length :=
      hlen ▸ List.idxOf_lt_length_of_mem (hHG u hu)
    let C : Finset (Fin (transposeSetSystem S).sets.length) :=
      H.attach.image fun u => ⟨S.ground.idxOf u.1, hidx_lt u.1 u.2⟩
    refine ⟨C, ?_, (Finset.card_image_le.trans (by simp)).trans hcard⟩
    intro j hjG
    have hj_lt : j < S.sets.length := List.mem_range.1 hjG
    obtain ⟨u, huH, huj⟩ := hHcov S.sets[j] (List.getElem_mem hj_lt)
    refine ⟨⟨S.ground.idxOf u, hidx_lt u huH⟩,
      Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨u, huH⟩), ?_⟩
    have hu_lt : S.ground.idxOf u < S.ground.length := List.idxOf_lt_length_of_mem (hHG u huH)
    have hget_u : S.ground[S.ground.idxOf u]'hu_lt = u := List.getElem_idxOf hu_lt
    simp only [transposeSetSystem, Fin.getElem_fin, List.getElem_map, hget_u, List.mem_filter,
      List.mem_range, decide_eq_true_eq]
    exact ⟨hj_lt, by rwa [List.getD_eq_getElem _ _ hj_lt]⟩

/-- Optimum equality under `transposeSetSystem`:
`optHittingSize (transposeSetSystem S) = S.optCoverSize`. -/
theorem optHittingSize_transposeSetSystem (S : SetSystem) :
    optHittingSize (transposeSetSystem S) = S.optCoverSize := by
  by_cases hS : S.Coverable
  · have hH : Hittable (transposeSetSystem S) := (hittable_transposeSetSystem_iff_coverable S).2 hS
    refine le_antisymm ?_ ?_
    · obtain ⟨C, hC, hcard⟩ := SetSystem.exists_isCover_optCoverSize hS
      have hm : (transposeSetSystem S, S.optCoverSize) ∈ HittingSet :=
        (transposeSetSystem_setCover_iff S S.optCoverSize).2 (mem_SetCover_iff.2 ⟨C, hC, hcard.le⟩)
      exact (mem_hittingSet_iff_optHittingSize_le hH).1 hm
    · obtain ⟨H, hHm, hcard⟩ := exists_isHittingSet_optHittingSize hH
      have hm : (S, optHittingSize (transposeSetSystem S)) ∈ SetCover :=
        (transposeSetSystem_setCover_iff S _).1 (mem_hittingSet_iff.2 ⟨H, hHm, hcard.le⟩)
      obtain ⟨C, hC, hCcard⟩ := mem_SetCover_iff.1 hm
      exact (SetSystem.optCoverSize_le hC).trans hCcard
  · have hH : ¬ Hittable (transposeSetSystem S) :=
      mt (hittable_transposeSetSystem_iff_coverable S).1 hS
    rw [SetSystem.optCoverSize_eq_zero_of_not_coverable hS]
    simp [optHittingSize, hH]

/-- Approximation-preserving reduction from `minSetCover` to `minHittingSet` with identity ratio. -/
theorem approxPreservingReducible_setCover_hittingSet :
    ApproxPreservingReducible minSetCover minHittingSet
      encSetSystem encSetSystem (encList encNat) (encList encNat) (fun _ ρ => ρ) := by
  let liftSol (S : SetSystem) (L : List ℕ) : List ℕ :=
    L.filter fun i => decide (i < S.sets.length)
  have hlift_poly : ComputableInPolyTime (fun p : SetSystem × List ℕ => liftSol p.1 p.2)
      (encPair encSetSystem (encList encNat)) (encList encNat) := by
    refine filterWithInput (snd _ _) ?_
    exact binary_lt' (snd _ _) (unary_to_binary.comp (by fun_prop))
  refine ⟨transposeSetSystem, liftSol, computableInPolyTime_transposeSetSystem, hlift_poly,
    fun S hS => (hittable_transposeSetSystem_iff_coverable S).2 hS,
    fun S L _ hL => ?_, fun S ρ L _ _ hcost => ?_⟩
  · obtain ⟨hLG, hLcov⟩ := (isHittingList_eq_true_iff (transposeSetSystem S) L).1 hL
    refine (S.isCoverList_eq_true_iff (liftSol S L)).2 ⟨?_, ?_⟩
    · intro i hi
      exact decide_eq_true_iff.1 (List.mem_filter.1 hi).2
    · intro u hu
      have hAu : ((List.range S.sets.length).filter fun i => decide (u ∈ S.sets.getD i [])) ∈
          (transposeSetSystem S).sets := List.mem_map_of_mem hu
      obtain ⟨i, hiL, hiF⟩ := hLcov _ hAu
      have hi_lt : i < S.sets.length := List.mem_range.1 (List.mem_filter.1 hiF).1
      have hui : u ∈ S.sets[i]'hi_lt := by
        have h1 := decide_eq_true_iff.1 (List.mem_filter.1 hiF).2
        rwa [List.getD_eq_getElem _ _ hi_lt] at h1
      exact ⟨i, List.mem_filter.2 ⟨List.mem_toFinset.1 hiL, decide_eq_true hi_lt⟩, hi_lt, hui⟩
  · have hlen : (liftSol S L).length ≤ L.length := (List.filter_sublist).length_le
    have hlen_real : ((liftSol S L).length : ℝ) ≤ L.length := by exact_mod_cast hlen
    calc minSetCover.cost S (liftSol S L)
        = ((liftSol S L).length : ℝ) := rfl
      _ ≤ (L.length : ℝ) := hlen_real
      _ ≤ ρ * minHittingSet.opt (transposeSetSystem S) := hcost
      _ = ρ * minSetCover.opt S := by
          simp [minHittingSet, minSetCover, optHittingSize_transposeSetSystem]

/-- `SetCover` reduces to `HittingSet` in polynomial time. -/
theorem polyTimeReducible_setCover_hittingSet :
    PolyTimeReducible encSetCover encHittingSet SetCover HittingSet :=
  ⟨fun p => (transposeSetSystem p.1, p.2),
    (computableInPolyTime_transposeSetSystem.comp (fst _ _)).prod (snd _ _),
    fun ⟨S, k⟩ => (transposeSetSystem_setCover_iff S k).symm⟩

/-- `HittingSet` reduces to `SetCover` in polynomial time. -/
theorem polyTimeReducible_hittingSet_setCover :
    PolyTimeReducible encHittingSet encSetCover HittingSet SetCover :=
  ⟨fun p => (transposeSetSystem p.1, p.2),
    (computableInPolyTime_transposeSetSystem.comp (fst _ _)).prod (snd _ _),
    fun ⟨S, k⟩ => (transposeSetSystem_hittingSet_iff S k).symm⟩

/-- `SetCover` FPT-reduces to `HittingSet` preserving `k`. -/
theorem fptReducible_setCover_hittingSet :
    FPTReducible encSetCover encHittingSet Prod.snd Prod.snd SetCover HittingSet :=
  FPTReducible.of_computableInPolyTime
    ((computableInPolyTime_transposeSetSystem.comp (fst _ _)).prod (snd _ _))
    (h := id) (fun _ => le_rfl) fun ⟨S, k⟩ => (transposeSetSystem_setCover_iff S k).symm

/-- `HittingSet` FPT-reduces to `SetCover` preserving `k`. -/
theorem fptReducible_hittingSet_setCover :
    FPTReducible encHittingSet encSetCover Prod.snd Prod.snd HittingSet SetCover :=
  FPTReducible.of_computableInPolyTime
    ((computableInPolyTime_transposeSetSystem.comp (fst _ _)).prod (snd _ _))
    (h := id) (fun _ => le_rfl) fun ⟨S, k⟩ => (transposeSetSystem_hittingSet_iff S k).symm

/-- **`HittingSet` belongs to `NP`**. -/
theorem hittingSet_mem_NP : HittingSet ∈ NP encHittingSet :=
  polyTimeReducible_hittingSet_setCover.mem_NP SetCover_mem_NP

/-- **`HittingSet` is `NP`-hard**. -/
theorem hittingSet_npHard : NPHard encHittingSet HittingSet :=
  (PromiseProblem.npHard_ofSet_iff.1
    ((GapSetCover_npHard (c := 2) (by norm_num)).mono
      (fun ⟨S, k⟩ h => by
        obtain ⟨_, hopt⟩ := mem_yes_GapSetCoverFn.1 h
        obtain ⟨C, hC, hcard⟩ := SetSystem.exists_isCover_optCoverSize
          (mem_yes_GapSetCoverFn.1 h).1
        exact mem_SetCover_iff.2 ⟨C, hC, hcard.le.trans hopt⟩)
      (fun ⟨S, k⟩ h => by
        obtain ⟨_, hopt, hlt⟩ := mem_no_GapSetCoverFn.1 h
        intro hm
        obtain ⟨C, hC, hcard⟩ := mem_SetCover_iff.1 hm
        have hle := (SetSystem.optCoverSize_le hC).trans hcard
        have hle' : (S.optCoverSize : ℝ) ≤ k := by exact_mod_cast hle
        linarith))).trans polyTimeReducible_setCover_hittingSet

/-- **`HittingSet` is `NP`-complete**. -/
theorem hittingSet_npComplete : NPComplete encHittingSet HittingSet :=
  ⟨hittingSet_mem_NP, hittingSet_npHard⟩

/-- Unconditional constant-factor inapproximability of `minHittingSet`: any polynomial-time
constant-factor `ρ`-approximation algorithm (`0 ≤ ρ`) for `minHittingSet` implies `P = NP`. -/
theorem P_eq_NP_of_hittingSet_approx_const
    {A : SetSystem → List ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hA : ComputableInPolyTime A encSetSystem (encList encNat))
    (happrox : minHittingSet.IsApprox (fun _ => ρ) A)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc := by
  obtain ⟨A₁, hA₁, happrox₁⟩ :=
    approxPreservingReducible_setCover_hittingSet.comp_isApprox hA happrox
  have hr : 1 < max ρ 1 + 1 := by linarith [le_max_right ρ 1]
  have hlt : ρ < max ρ 1 + 1 := by linarith [le_max_left ρ 1]
  exact P_eq_NP_of_setCover_approx (GapSetCover_npHard hr) hρ0 hlt hA₁ happrox₁ enc

/-! ### 3. Closed-Neighborhood Reduction from `DominatingSet` to `SetCover` and `HittingSet` -/

/-- Closed-neighborhood `SetSystem` of an undirected graph `G`: ground set `G.vertices`, and one
closed neighborhood `s :: G.vertices.filter (G.adjBool · s)` for each `s ∈ G.vertices`. -/
@[expose] def dominatingSetToSetSystem (G : Graph) : SetSystem :=
  ⟨G.vertices, G.vertices.map fun s => s :: G.vertices.filter fun v => G.adjBool v s⟩

/-- Closed-neighborhood `HittingSet` system of `G`:
`transposeSetSystem (dominatingSetToSetSystem G)`. -/
@[expose] def dominatingSetToHittingSystem (G : Graph) : SetSystem :=
  transposeSetSystem (dominatingSetToSetSystem G)

/-- Polynomial-time certificate for `dominatingSetToSetSystem`. -/
@[fun_prop]
theorem computableInPolyTime_dominatingSetToSetSystem :
    ComputableInPolyTime dominatingSetToSetSystem encGraph encSetSystem := by
  have hsets : ComputableInPolyTime
      (fun G : Graph => G.vertices.map fun s => s :: G.vertices.filter fun v => G.adjBool v s)
      encGraph encNatSetList := by
    refine mapWithInput (by fun_prop) ?_
    have hs : ComputableInPolyTime (fun p : Graph × ℕ => p.2)
        (encPair encGraph encNat) encNat := snd _ _
    have hfilt : ComputableInPolyTime
        (fun p : Graph × ℕ => p.1.vertices.filter fun v => p.1.adjBool v p.2)
        (encPair encGraph encNat) (encList encNat) := by
      refine filterWithInput (by fun_prop) ?_
      fun_prop
    exact cons' hs hfilt
  unfold dominatingSetToSetSystem
  exact computableInPolyTime_setSystemMk (by fun_prop) hsets

/-- Polynomial-time certificate for `dominatingSetToHittingSystem`. -/
@[fun_prop]
theorem computableInPolyTime_dominatingSetToHittingSystem :
    ComputableInPolyTime dominatingSetToHittingSystem encGraph encSetSystem :=
  computableInPolyTime_transposeSetSystem.comp computableInPolyTime_dominatingSetToSetSystem

/-- `dominatingSetToSetSystem G` is always `Coverable`. -/
theorem coverable_dominatingSetToSetSystem (G : Graph) :
    (dominatingSetToSetSystem G).Coverable := by
  refine ⟨Finset.univ, fun v hv => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
  have hi' : i < (dominatingSetToSetSystem G).sets.length := by
    simpa [dominatingSetToSetSystem] using hi
  refine ⟨⟨i, hi'⟩, Finset.mem_univ _, ?_⟩
  simp [dominatingSetToSetSystem]

/-- `dominatingSetToHittingSystem G` is always `Hittable`. -/
theorem hittable_dominatingSetToHittingSystem (G : Graph) :
    Hittable (dominatingSetToHittingSystem G) :=
  (hittable_transposeSetSystem_iff_coverable _).2 (coverable_dominatingSetToSetSystem G)

/-- `(dominatingSetToSetSystem G, k) ∈ SetCover` if and only if `G` admits a dominating set of at
most `k` declared vertices. -/
theorem dominatingSetToSetSystem_mem_setCover_iff (G : Graph) (k : ℕ) :
    (dominatingSetToSetSystem G, k) ∈ SetCover ↔
      ∃ D : Finset ℕ, (∀ v ∈ D, v ∈ G.vertices) ∧
        (∀ v ∈ G.vertices, v ∈ D ∨ ∃ s ∈ D, G.toSimpleGraph.Adj v s) ∧ D.card ≤ k := by
  classical
  rw [mem_SetCover_iff]
  have hlen : (dominatingSetToSetSystem G).sets.length = G.vertices.length := by
    simp [dominatingSetToSetSystem]
  constructor
  · rintro ⟨C, hC, hcard⟩
    let D : Finset ℕ := C.image fun i => G.vertices[i.1]'(i.isLt.trans_eq hlen)
    refine ⟨D, ?_, ?_, Finset.card_image_le.trans hcard⟩
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
      exact List.getElem_mem _
    · intro v hv
      obtain ⟨i, hiC, hvi⟩ := hC v hv
      have hi_lt : i.1 < G.vertices.length := i.isLt.trans_eq hlen
      have hset : (dominatingSetToSetSystem G).sets[i] =
          (G.vertices[i.1]'hi_lt) ::
            G.vertices.filter (fun u => G.adjBool u (G.vertices[i.1]'hi_lt)) := by
        rw [Fin.getElem_fin]
        simp [dominatingSetToSetSystem]
      rw [hset, List.mem_cons] at hvi
      rcases hvi with rfl | hfilt
      · exact Or.inl (Finset.mem_image_of_mem _ hiC)
      · have hadj := (G.adjBool_eq_true_iff _ _).1 (List.mem_filter.1 hfilt).2
        exact Or.inr ⟨G.vertices[i.1]'hi_lt, Finset.mem_image_of_mem _ hiC, hadj⟩
  · rintro ⟨D, hDV, hDdom, hcard⟩
    have hidx_lt (s : ℕ) (hs : s ∈ D) :
        G.vertices.idxOf s < (dominatingSetToSetSystem G).sets.length :=
      hlen ▸ List.idxOf_lt_length_of_mem (hDV s hs)
    let C : Finset (Fin (dominatingSetToSetSystem G).sets.length) :=
      D.attach.image fun s => ⟨G.vertices.idxOf s.1, hidx_lt s.1 s.2⟩
    refine ⟨C, ?_, (Finset.card_image_le.trans (by simp)).trans hcard⟩
    intro v hv
    rcases hDdom v hv with hvD | ⟨s, hsD, hadj⟩
    · have hv_lt : G.vertices.idxOf v < G.vertices.length := List.idxOf_lt_length_of_mem hv
      refine ⟨⟨G.vertices.idxOf v, hidx_lt v hvD⟩,
        Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨v, hvD⟩), ?_⟩
      simp [dominatingSetToSetSystem, List.getElem_idxOf hv_lt]
    · have hs_lt : G.vertices.idxOf s < G.vertices.length :=
        List.idxOf_lt_length_of_mem (hDV s hsD)
      refine ⟨⟨G.vertices.idxOf s, hidx_lt s hsD⟩,
        Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨s, hsD⟩), ?_⟩
      simp only [dominatingSetToSetSystem, Fin.getElem_fin, List.getElem_map,
        List.getElem_idxOf hs_lt, List.mem_cons, List.mem_filter, Graph.adjBool_eq_true_iff]
      exact Or.inr ⟨hv, hadj⟩

/-- `(dominatingSetToHittingSystem G, k) ∈ HittingSet` if and only if `G` admits a dominating set
of at most `k` declared vertices. -/
theorem dominatingSetToHittingSystem_mem_iff (G : Graph) (k : ℕ) :
    (dominatingSetToHittingSystem G, k) ∈ HittingSet ↔
      ∃ D : Finset ℕ, (∀ v ∈ D, v ∈ G.vertices) ∧
        (∀ v ∈ G.vertices, v ∈ D ∨ ∃ s ∈ D, G.toSimpleGraph.Adj v s) ∧ D.card ≤ k := by
  rw [dominatingSetToHittingSystem, transposeSetSystem_setCover_iff,
    dominatingSetToSetSystem_mem_setCover_iff]

/-! ### 4. Membership of `HittingSet` and `SetCover` in `W[2]` -/

private def hsDistinctGround (S : SetSystem) : List ℕ :=
  selectDistinct S.ground (List.replicate S.ground.length true)

private lemma mem_hsDistinctGround_iff {S : SetSystem} {u : ℕ} :
    u ∈ hsDistinctGround S ↔ u ∈ S.ground :=
  mem_selectDistinct_replicate

private lemma nodup_hsDistinctGround (S : SetSystem) : (hsDistinctGround S).Nodup :=
  nodup_selectDistinct _ _

private def hsOrArgLists (S : SetSystem) : List (List ℕ) :=
  let U := hsDistinctGround S
  S.sets.map fun A => (List.range U.length).filter fun i => decide (U.getD i 0 ∈ A)

private def hsCircuitGates (nInputs : ℕ) (orArgs : List (List ℕ)) :
    List (Unbounded.Op × List ℕ) :=
  (orArgs.map fun l => (Unbounded.Op.or l.length, l)) ++
    [(Unbounded.Op.and orArgs.length, (List.range orArgs.length).map (nInputs + ·))]

private def hsCircuitCode (S : SetSystem) (k : ℕ) :
    List (Unbounded.Op × List ℕ) × List ℕ :=
  let U := hsDistinctGround S
  let pad := min k U.length
  let nInputs := U.length + pad
  let orArgs := hsOrArgLists S
  (hsCircuitGates nInputs orArgs, [nInputs + orArgs.length])

private lemma lt_of_mem_hsOrArgLists {S : SetSystem} {l : List ℕ} (hl : l ∈ hsOrArgLists S) :
    ∀ i ∈ l, i < (hsDistinctGround S).length := by
  obtain ⟨A, _, rfl⟩ := List.mem_map.1 hl
  intro i hi
  exact List.mem_range.1 (List.mem_filter.1 hi).1

private lemma isCodeFrom_hsCircuitGates {nInputs : ℕ} {orArgs : List (List ℕ)}
    (hor : ∀ l ∈ orArgs, ∀ i ∈ l, i < nInputs) :
    Program.IsCodeFrom Unbounded.signature nInputs 0 (hsCircuitGates nInputs orArgs) := by
  rw [hsCircuitGates, Program.isCodeFrom_append]
  refine ⟨Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun l hl =>
      ⟨rfl, fun i hi => (hor l hl i hi).trans_le (Nat.le_add_right _ _)⟩),
    Program.isCodeFrom_of_forall (List.forall_mem_singleton.2 ⟨by simp,
      List.forall_mem_map.2 fun j hj => ?_⟩)⟩
  simp only [List.mem_range, List.length_map] at hj ⊢
  omega

private lemma isSome_ofCode_hsCircuitCode (S : SetSystem) (k : ℕ) :
    (Circuit.ofCode ((hsDistinctGround S).length + min k (hsDistinctGround S).length) 1
      (hsCircuitCode S k) :
      Option (Circuit Unbounded.signature _ 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_hsCircuitGates fun l hl i hi =>
      (lt_of_mem_hsOrArgLists hl i hi).trans_le (Nat.le_add_right _ _), rfl, ?_⟩
  simp only [hsCircuitCode, hsCircuitGates, List.mem_singleton, forall_eq, List.length_append,
    List.length_map, List.length_singleton]
  omega

private def hsToCircuit (S : SetSystem) (k : ℕ) : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨(hsDistinctGround S).length + min k (hsDistinctGround S).length,
    (Circuit.ofCode _ 1 (hsCircuitCode S k)).get (isSome_ofCode_hsCircuitCode S k)⟩

private lemma code_hsToCircuit (S : SetSystem) (k : ℕ) :
    (hsToCircuit S k).2.code = hsCircuitCode S k :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

private lemma depth_hsToCircuit_le (S : SetSystem) (k : ℕ) :
    (hsToCircuit S k).2.depth ≤ 2 := by
  rw [← Circuit.depthWith_one]
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  rw [code_hsToCircuit] at hv
  dsimp only [hsCircuitCode] at hv
  rw [hsCircuitGates] at hv
  have hlayer : ∀ w ∈ evalCode (depthInterpretation (σ := Unbounded.signature) 1) 0
      (List.replicate ((hsDistinctGround S).length + min k (hsDistinctGround S).length) 0)
      (((hsOrArgLists S).map fun l => (Unbounded.Op.or l.length, l)) ++
        [(Unbounded.Op.and (hsOrArgLists S).length,
          (List.range (hsOrArgLists S).length).map
            (((hsDistinctGround S).length + min k (hsDistinctGround S).length) + ·))]),
      w ≤ 0 + 1 + 1 := by
    rw [evalCode_append]
    refine le_of_mem_evalCode_depth_layer _ _ _
      (List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_))
      (le_of_mem_evalCode_depth_layer _ _ _
        (List.forall_mem_map.2 fun l hl i hi => ?_)
        (fun _ hw => (List.eq_of_mem_replicate hw).le)
        (List.forall_mem_map.2 fun _ _ => le_rfl))
      (by simp)
    · simp only [List.mem_range, length_evalCode, List.length_replicate, List.length_map] at hj ⊢
      omega
    · have hlt := lt_of_mem_hsOrArgLists hl i hi
      simp only [List.length_replicate]
      omega
  exact hlayer v hv

private lemma weft_hsToCircuit_le (S : SetSystem) (k : ℕ) :
    (hsToCircuit S k).2.weft ≤ 2 :=
  (hsToCircuit S k).2.weft_le_depth.trans (depth_hsToCircuit_le S k)

private lemma evalCode_hsCircuitGates {nInputs : ℕ} {orArgs : List (List ℕ)}
    (hor : ∀ l ∈ orArgs, ∀ i ∈ l, i < nInputs) (x : List Bool) (hx : x.length = nInputs) :
    (evalCode Unbounded.interpretation false x (hsCircuitGates nInputs orArgs)).getD
        (nInputs + orArgs.length) false =
      decide (∀ l ∈ orArgs, ∃ i ∈ l, x.getD i false = true) := by
  subst hx
  rw [hsCircuitGates, evalCode_append]
  have h1 : evalCode Unbounded.interpretation false x
      (orArgs.map fun l => (Unbounded.Op.or l.length, l)) =
      x ++ orArgs.map fun l => decide (∃ i ∈ l, x.getD i false = true) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun l _ => ?_
      simp only [Function.comp_apply, Unbounded.interpretation]
      rw [decide_eq_decide]
      constructor
      · rintro ⟨a, ha⟩
        have ha_lt : a.val < l.length := a.isLt
        rw [List.getElem?_eq_getElem ha_lt, Option.elim_some] at ha
        exact ⟨l[a.val]'ha_lt, List.getElem_mem ha_lt, ha⟩
      · rintro ⟨i, hil, hxi⟩
        obtain ⟨idx, hidx_lt, rfl⟩ := List.mem_iff_getElem.1 hil
        refine ⟨⟨idx, hidx_lt⟩, ?_⟩
        rw [List.getElem?_eq_getElem hidx_lt, Option.elim_some]
        exact hxi
    · exact List.forall_mem_map.2 fun l hl i hi => hor l hl i hi
  rw [h1, evalCode_layer]
  · have hlen : (x ++ orArgs.map fun l => decide (∃ i ∈ l, x.getD i false = true)).length =
        x.length + orArgs.length := by simp
    rw [← hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [List.map_singleton, List.getD_cons_zero, Unbounded.interpretation_and]
    rw [decide_eq_decide, List.forall_mem_iff_getElem, Fin.forall_iff]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp only [Option.elim_some, List.getElem_map, List.getElem_range]
    rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, decide_eq_true_eq]
  · refine List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_)
    simp only [List.mem_range, List.length_append, List.length_map] at hj ⊢
    omega

private lemma hsToCircuit_satisfiableWithWeight_iff {S : SetSystem} {k : ℕ}
    (hk : k ≤ (hsDistinctGround S).length) :
    (hsToCircuit S k).2.SatisfiableWithWeight Unbounded.interpretation k ↔
      (S, k) ∈ HittingSet := by
  classical
  set U := hsDistinctGround S with hU_def
  have hpad : min k U.length = k := Nat.min_eq_left hk
  have hfst : (hsToCircuit S k).1 = U.length + min k U.length := rfl
  have hout : ((hsToCircuit S k).2.outputs 0).toNat =
      U.length + min k U.length + (hsOrArgLists S).length :=
    congrArg (fun c => c.2.headD 0) (code_hsToCircuit S k)
  have heval (x : BitString (hsToCircuit S k).1) :
      (hsToCircuit S k).2.eval Unbounded.interpretation x 0 =
        decide (∀ l ∈ hsOrArgLists S, ∃ i ∈ l, (List.ofFn x).getD i false = true) := by
    rw [Circuit.eval_eq_getD _ _ false, hout, code_hsToCircuit]
    exact evalCode_hsCircuitGates
      (fun l hl i hi => (lt_of_mem_hsOrArgLists hl i hi).trans_le (Nat.le_add_right _ _))
      (List.ofFn x) (by simp [hfst, ← hU_def])
  simp only [Circuit.SatisfiableWithWeight, heval, decide_eq_true_eq, mem_hittingSet_iff]
  constructor
  · rintro ⟨x, hwt, hx⟩
    let H : Finset ℕ :=
      ((Finset.univ.filter fun i : Fin (hsToCircuit S k).1 =>
        i.1 < U.length ∧ x i = true).image fun i => U.getD i.1 0)
    have hHcard : H.card ≤ k := by
      refine (Finset.card_image_le.trans ?_).trans hwt.le
      rw [BitString.weight]
      exact Finset.card_le_card fun i hi =>
        Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2.2⟩
    refine ⟨H, ⟨?_, ?_⟩, hHcard⟩
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
      have hi_lt : i.1 < U.length := (Finset.mem_filter.1 hi).2.1
      rw [List.getD_eq_getElem _ _ hi_lt]
      exact mem_hsDistinctGround_iff.1 (List.getElem_mem hi_lt)
    · intro A hA
      have hl : ((List.range U.length).filter fun i => decide (U.getD i 0 ∈ A)) ∈
          hsOrArgLists S := List.mem_map_of_mem hA
      obtain ⟨i, hil, hxi⟩ := hx _ hl
      have hi_lt : i < U.length := List.mem_range.1 (List.mem_filter.1 hil).1
      have huA : U.getD i 0 ∈ A := decide_eq_true_iff.1 (List.mem_filter.1 hil).2
      have hi_tot : i < (hsToCircuit S k).1 := by rw [hfst]; omega
      have hxi' : x ⟨i, hi_tot⟩ = true := by
        rw [List.getD_eq_getElem _ _ (by simp [hi_tot]), List.getElem_ofFn] at hxi
        exact hxi
      exact ⟨U.getD i 0, Finset.mem_image.2
        ⟨⟨i, hi_tot⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi_lt, hxi'⟩, rfl⟩, huA⟩
  · rintro ⟨H, ⟨hHG, hHcov⟩, hcard⟩
    let H_idx : Finset ℕ := H.image U.idxOf
    have hH_idx_lt : ∀ i ∈ H_idx, i < U.length := by
      intro i hi
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi
      exact List.idxOf_lt_length_of_mem (mem_hsDistinctGround_iff.2 (hHG u hu))
    have hH_idx_card : H_idx.card ≤ k := Finset.card_image_le.trans hcard
    let padCount := k - H_idx.card
    let x : BitString (hsToCircuit S k).1 := fun i =>
      if i.1 < U.length then decide (i.1 ∈ H_idx)
      else decide (i.1 < U.length + padCount)
    refine ⟨x, ?_, ?_⟩
    · have hpart : (Finset.univ.filter fun i : Fin (hsToCircuit S k).1 =>
          x i = true).image Fin.val =
          H_idx ∪ ((Finset.range padCount).image (U.length + ·)) := by
        ext j
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union, Finset.mem_range, x]
        constructor
        · rintro ⟨i, hi, rfl⟩
          split_ifs at hi with hlt
          · exact Or.inl (decide_eq_true_iff.1 hi)
          · exact Or.inr ⟨i.1 - U.length, by have := decide_eq_true_iff.1 hi; omega, by omega⟩
        · rintro (hjH | ⟨r, hr, rfl⟩)
          · have hj_lt := hH_idx_lt j hjH
            have hj_tot : j < (hsToCircuit S k).1 := by rw [hfst]; omega
            exact ⟨⟨j, hj_tot⟩, by simp [hj_lt, hjH], rfl⟩
          · have hj_tot : U.length + r < (hsToCircuit S k).1 := by rw [hfst, hpad]; omega
            exact ⟨⟨U.length + r, hj_tot⟩, by simp; omega, rfl⟩
      have hdisj : Disjoint H_idx ((Finset.range padCount).image (U.length + ·)) := by
        refine Finset.disjoint_left.2 fun j hjH hjR => ?_
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hjR
        have := hH_idx_lt _ hjH
        omega
      rw [BitString.weight, ← Finset.card_image_of_injective _ Fin.val_injective, hpart,
        Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective (Finset.range padCount)
          (fun a b (h : U.length + a = U.length + b) => by omega), Finset.card_range]
      omega
    · intro l hl
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hl
      obtain ⟨u, huH, huA⟩ := hHcov A hA
      have huU : u ∈ U := mem_hsDistinctGround_iff.2 (hHG u huH)
      let i := U.idxOf u
      have hi_lt : i < U.length := List.idxOf_lt_length_of_mem huU
      have hi_tot : i < (hsToCircuit S k).1 := by rw [hfst]; omega
      refine ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi_lt, decide_eq_true ?_⟩, ?_⟩
      · rw [List.getD_eq_getElem _ _ hi_lt, List.getElem_idxOf hi_lt]
        exact huA
      · rw [List.getD_eq_getElem _ _ (by simp [hi_tot]), List.getElem_ofFn]
        simp only [x, hi_lt, ↓reduceIte, decide_eq_true_eq]
        exact Finset.mem_image_of_mem _ huH

private def hsYesInstance : WCSInstance 2 2 :=
  ⟨⟨WCS.trueCircuit, by decide, by decide⟩, 0⟩

private def hsNoInstance : WCSInstance 2 2 :=
  ⟨⟨WCS.falseCircuit, by decide, by decide⟩, 0⟩

private def hittingSetToWCS (p : SetSystem × ℕ) : WCSInstance 2 2 :=
  if decide (p.2 ≤ (hsDistinctGround p.1).length) then
    ⟨⟨hsToCircuit p.1 p.2, weft_hsToCircuit_le p.1 p.2, depth_hsToCircuit_le p.1 p.2⟩, p.2⟩
  else if hittableBool p.1 then
    hsYesInstance
  else
    hsNoInstance

private lemma hittingSetToWCS_mem_iff (p : SetSystem × ℕ) :
    hittingSetToWCS p ∈ WCS 2 2 ↔ p ∈ HittingSet := by
  obtain ⟨S, k⟩ := p
  unfold hittingSetToWCS
  dsimp only
  by_cases hk : k ≤ (hsDistinctGround S).length
  · simp only [hk, decide_true, ↓reduceIte, mem_WCS]
    exact hsToCircuit_satisfiableWithWeight_iff hk
  · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hk_gt : (hsDistinctGround S).length < k := Nat.lt_of_not_le hk
    by_cases hhit : hittableBool S = true
    · simp only [hhit, ↓reduceIte, hsYesInstance, mem_WCS]
      have hyes : WCS.trueCircuit.2.SatisfiableWithWeight Unbounded.interpretation 0 :=
        ⟨fun _ => false, Nat.eq_zero_of_le_zero (BitString.weight_le_length _), rfl⟩
      refine ⟨fun _ => ?_, fun _ => hyes⟩
      obtain ⟨H, hH⟩ := (hittableBool_eq_true_iff S).1 hhit
      let H' : Finset ℕ := (hsDistinctGround S).toFinset
      refine mem_hittingSet_iff.2 ⟨H', ⟨fun u hu =>
        mem_hsDistinctGround_iff.1 (List.mem_toFinset.1 hu), ?_⟩,
        (hsDistinctGround S).toFinset_card_le.trans hk_gt.le⟩
      intro A hA
      obtain ⟨u, huH, huA⟩ := hH.2 A hA
      exact ⟨u, List.mem_toFinset.2 (mem_hsDistinctGround_iff.2 (hH.1 u huH)), huA⟩
    · simp only [hhit, Bool.false_eq_true, ↓reduceIte, hsNoInstance, mem_WCS]
      have hno : ¬ WCS.falseCircuit.2.SatisfiableWithWeight Unbounded.interpretation 0 :=
        fun ⟨_, _, hx⟩ => Bool.false_ne_true hx
      refine ⟨fun h => absurd h hno, fun hm => ?_⟩
      obtain ⟨H, hH, _⟩ := mem_hittingSet_iff.1 hm
      exact absurd ((hittableBool_eq_true_iff S).2 ⟨H, hH⟩) hhit

private lemma computableInPolyTime_hittingSetToWCS :
    ComputableInPolyTime hittingSetToWCS encHittingSet (encWCS 2 2) := by
  have hU : ComputableInPolyTime (fun p : SetSystem × ℕ => hsDistinctGround p.1)
      encHittingSet (encList encNat) := by
    have hg : ComputableInPolyTime (fun p : SetSystem × ℕ => p.1.ground)
        encHittingSet (encList encNat) := by fun_prop
    unfold hsDistinctGround
    exact (computableInPolyTime_selectDistinct encNat).comp
      (hg.prod ((bitsReplicate true).comp ((length_list encNat).comp hg)))
  have hUlen : ComputableInPolyTime (fun p : SetSystem × ℕ => (hsDistinctGround p.1).length)
      encHittingSet encUnary := (length_list encNat).comp hU
  have hpad : ComputableInPolyTime
      (fun p : SetSystem × ℕ => min p.2 (hsDistinctGround p.1).length)
      encHittingSet encUnary := by
    simpa only [Nat.min_comm] using binary_min_unary' hUlen (snd _ _)
  have hnIn : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        (hsDistinctGround p.1).length + min p.2 (hsDistinctGround p.1).length)
      encHittingSet encUnary :=
    unary_add' hUlen hpad
  have hrU : ComputableInPolyTime
      (fun p : SetSystem × ℕ => List.range (hsDistinctGround p.1).length)
      encHittingSet (encList encNat) := by
    have hr : ComputableInPolyTime
        (fun p : SetSystem × ℕ => List.range (hsDistinctGround p.1).length)
        encHittingSet (encList encUnary) := range.comp hUlen
    have hm : ComputableInPolyTime (List.map (fun n : ℕ => n))
        (encList encUnary) (encList encNat) := map unary_to_binary
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using hm.comp hr
  have horArgs : ComputableInPolyTime
      (fun p : SetSystem × ℕ => hsOrArgLists p.1)
      encHittingSet encNatSetList := by
    unfold hsOrArgLists
    refine mapWithInput (by fun_prop) ?_
    refine filterWithInput (hrU.comp (fst _ _)) ?_
    have hget := listGetD_binary (encA := encNat) (encL := encList encNat) 0
      (hU.comp ((fst encHittingSet (encList encNat)).comp (fst _ _))) (snd _ _)
    have hA : ComputableInPolyTime (fun q : ((SetSystem × ℕ) × List ℕ) × ℕ => q.1.2)
        (encPair (encPair encHittingSet (encList encNat)) encNat) (encList encNat) :=
      (snd _ _).comp (fst _ _)
    exact (by fun_prop : ComputableInPolyTime (fun r : ℕ × List ℕ => decide (r.1 ∈ r.2))
      (encPair encNat (encList encNat)) encBool).comp (hget.prod hA)
  have horGates : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        (hsOrArgLists p.1).map fun l => ((Unbounded.Op.or l.length, l) : Unbounded.Op × List ℕ))
      encHittingSet (encList (Circuit.encGate Unbounded.encOp)) := by
    refine mapWithInput horArgs ?_
    have hllen : ComputableInPolyTime (fun q : (SetSystem × ℕ) × List ℕ => q.2.length)
        (encPair encHittingSet (encList encNat)) encUnary :=
      (length_list encNat).comp (snd _ _)
    exact (Unbounded.computableInPolyTime_or.comp hllen).prod (snd _ _)
  have hmSets : ComputableInPolyTime
      (fun p : SetSystem × ℕ => (hsOrArgLists p.1).length)
      encHittingSet encUnary := (length_list (encList encNat)).comp horArgs
  have handGate : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        [((Unbounded.Op.and (hsOrArgLists p.1).length,
          (List.range (hsOrArgLists p.1).length).map
            (((hsDistinctGround p.1).length + min p.2 (hsDistinctGround p.1).length) + ·)) :
          Unbounded.Op × List ℕ)])
      encHittingSet (encList (Circuit.encGate Unbounded.encOp)) := by
    refine cons' ((Unbounded.computableInPolyTime_and.comp hmSets).prod ?_) (const [])
    refine mapWithInput (range.comp hmSets) ?_
    have hn' := hnIn.comp (fst encHittingSet encUnary)
    exact unary_to_binary.comp (unary_add' hn' (snd encHittingSet encUnary))
  have hcode : ComputableInPolyTime
      (fun p : SetSystem × ℕ => hsCircuitCode p.1 p.2)
      encHittingSet (Circuit.encCode Unbounded.encOp) := by
    unfold hsCircuitCode hsCircuitGates
    exact (listAppend' horGates handGate).prod
      (cons' (unary_to_binary.comp (unary_add' hnIn hmSets)) (const []))
  have hmain : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        (((hsDistinctGround p.1).length + min p.2 (hsDistinctGround p.1).length,
           hsCircuitCode p.1 p.2), p.2))
      encHittingSet
      (encPair (encPair encUnary (Circuit.encCode Unbounded.encOp)) encNat) :=
    (hnIn.prod hcode).prod (snd _ _)
  have hmainWCS : ComputableInPolyTime
      (fun p : SetSystem × ℕ =>
        (⟨⟨hsToCircuit p.1 p.2, weft_hsToCircuit_le p.1 p.2, depth_hsToCircuit_le p.1 p.2⟩,
          p.2⟩ : WCSInstance 2 2))
      encHittingSet (encWCS 2 2) :=
    hmain.of_enc_eq fun _ => by
      simp only [encWCS_apply, encPair_apply, encWeftCircuit_apply, Circuit.encCircuit_apply,
        code_hsToCircuit]
      rfl
  have hcond : ComputableInPolyTime
      (fun p : SetSystem × ℕ => decide (p.2 ≤ (hsDistinctGround p.1).length))
      encHittingSet encBool :=
    binary_le' (snd _ _) (unary_to_binary.comp hUlen)
  have hhit : ComputableInPolyTime (fun p : SetSystem × ℕ => hittableBool p.1)
      encHittingSet encBool :=
    computableInPolyTime_hittableBool.comp (fst _ _)
  unfold hittingSetToWCS
  exact hcond.ite hmainWCS (hhit.ite (const hsYesInstance) (const hsNoInstance))

/-- **`HittingSet` belongs to `W[2]`** with parameter `k`. -/
theorem hittingSet_mem_W : HittingSet ∈ W 2 encHittingSet Prod.snd :=
  ⟨2, FPTReducible.of_computableInPolyTime computableInPolyTime_hittingSetToWCS
    (h := id) (fun p => by
      unfold hittingSetToWCS hsYesInstance hsNoInstance
      split_ifs <;> simp)
    fun p => (hittingSetToWCS_mem_iff p).symm⟩

/-- **`SetCover` belongs to `W[2]`** with parameter `k`. -/
theorem setCover_mem_W : SetCover ∈ W 2 encSetCover Prod.snd :=
  fptReducible_setCover_hittingSet.mem_W hittingSet_mem_W

/-! ### 5. Specification-Driven `SetSystem` Construction -/

/-- Construct a `SetSystem` on positions `0, …, vs.length - 1` from a list of set specifications
`specs` and a Boolean incidence test `mem`. -/
@[expose] def ofSpecSetSystem {V T : Type} (vs : List V) (specs : List T)
    (mem : T → V → Bool) : SetSystem :=
  ⟨List.range vs.length,
    specs.map fun t => (vs.zipIdx.filter fun p => mem t p.1).map Prod.snd⟩

/-- Characterization of `HittingSet` on `ofSpecSetSystem vs specs mem`. -/
theorem mem_hittingSet_ofSpecSetSystem_iff {V T : Type}
    {vs : List V} {specs : List T} {mem : T → V → Bool} {k : ℕ} :
    (ofSpecSetSystem vs specs mem, k) ∈ HittingSet ↔
      ∃ H : Finset V, H.card ≤ k ∧ (∀ v ∈ H, v ∈ vs) ∧
        ∀ t ∈ specs, ∃ v ∈ H, mem t v = true := by
  classical
  rw [mem_hittingSet_iff]
  constructor
  · rintro ⟨I, ⟨hIG, hIcov⟩, hcard⟩
    have hlt (i : ℕ) (hi : i ∈ I) : i < vs.length := List.mem_range.1 (hIG i hi)
    let H : Finset V := I.attach.image fun i => vs[i.1]'(hlt i.1 i.2)
    refine ⟨H, (Finset.card_image_le.trans (by simp)).trans hcard, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
      exact List.getElem_mem _
    · intro t ht
      have hAt : ((vs.zipIdx.filter fun p => mem t p.1).map Prod.snd) ∈
          (ofSpecSetSystem vs specs mem).sets := List.mem_map_of_mem ht
      obtain ⟨i, hiI, hiA⟩ := hIcov _ hAt
      have hex : ∃ p ∈ vs.zipIdx, mem t p.1 = true ∧ p.2 = i := by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hiA
        exact ⟨p, (List.mem_filter.1 hp).1, (List.mem_filter.1 hp).2, rfl⟩
      obtain ⟨j, hj_lt, hmem, rfl⟩ := List.exists_mem_zipIdx'.1 hex
      exact ⟨vs[j]'hj_lt, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨j, hiI⟩), hmem⟩
  · rintro ⟨H, hcard, hHvs, hHcov⟩
    let I : Finset ℕ := H.image vs.idxOf
    refine ⟨I, ⟨?_, ?_⟩, Finset.card_image_le.trans hcard⟩
    · intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
      exact List.mem_range.2 (List.idxOf_lt_length_of_mem (hHvs v hv))
    · intro A hA
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hA
      obtain ⟨v, hvH, hmem⟩ := hHcov t ht
      let i := vs.idxOf v
      have hi_lt : i < vs.length := List.idxOf_lt_length_of_mem (hHvs v hvH)
      have hget : vs[i]'hi_lt = v := List.getElem_idxOf hi_lt
      have hpair_eq : (vs[i]'hi_lt, i) = (v, i) := Prod.ext hget rfl
      obtain ⟨p, hp_zip, hp_eq⟩ := (List.exists_mem_zipIdx' (l := vs)
        (p := fun q => q = (v, i))).2 ⟨i, hi_lt, hpair_eq⟩
      subst hp_eq
      exact ⟨i, Finset.mem_image_of_mem _ hvH,
        List.mem_map.2 ⟨(v, i), List.mem_filter.2 ⟨hp_zip, hmem⟩, rfl⟩⟩

/-- Polynomial-time certificate for `ofSpecSetSystem`. -/
theorem computableInPolyTime_ofSpecSetSystem {γ V T : Type}
    {encIn : γ ↪ List Bool} {encV : V ↪ List Bool} {encT : T ↪ List Bool}
    {vs : γ → List V} {specs : γ → List T} {mem : γ → T → V → Bool}
    (hvs : ComputableInPolyTime vs encIn (encList encV))
    (hspecs : ComputableInPolyTime specs encIn (encList encT))
    (hmem : ComputableInPolyTime (fun p : γ × (T × V) => mem p.1 p.2.1 p.2.2)
      (encPair encIn (encPair encT encV)) encBool) :
    ComputableInPolyTime (fun a => ofSpecSetSystem (vs a) (specs a) (mem a))
      encIn encSetSystem := by
  have hz : ComputableInPolyTime (fun a => (vs a).zipIdx)
      encIn (encList (encPair encV encUnary)) :=
    (zipIdx encV).comp hvs
  have hr : ComputableInPolyTime (fun a => List.range (vs a).length)
      encIn (encList encNat) := by
    have h1 : ComputableInPolyTime (fun a => List.range (vs a).length)
        encIn (encList encUnary) := range.comp ((length_list encV).comp hvs)
    have h2 : ComputableInPolyTime (List.map (fun n : ℕ => n))
        (encList encUnary) (encList encNat) := map unary_to_binary
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using h2.comp h1
  have hsets : ComputableInPolyTime
      (fun a => (specs a).map fun t =>
        ((vs a).zipIdx.filter fun p => mem a t p.1).map Prod.snd)
      encIn encNatSetList := by
    refine mapWithInput hspecs ?_
    have hfilt : ComputableInPolyTime
        (fun p : γ × T => ((vs p.1).zipIdx.filter fun q => mem p.1 p.2 q.1))
        (encPair encIn encT) (encList (encPair encV encUnary)) := by
      refine filterWithInput (hz.comp (fst _ _)) ?_
      have harg : ComputableInPolyTime
          (fun q : (γ × T) × (V × ℕ) => (q.1.1, (q.1.2, q.2.1)))
          (encPair (encPair encIn encT) (encPair encV encUnary))
          (encPair encIn (encPair encT encV)) := by fun_prop
      exact hmem.comp harg
    refine mapWithInput hfilt ?_
    exact unary_to_binary.comp ((snd encV encUnary).comp (snd _ _))
  unfold ofSpecSetSystem
  exact computableInPolyTime_setSystemMk hr hsets

end Cslib.Complexity
