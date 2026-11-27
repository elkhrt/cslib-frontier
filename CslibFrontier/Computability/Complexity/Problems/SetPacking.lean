/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import Mathlib.Data.ZMod.Basic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Parameterized Set Packing, Exact $r$-Covering, and $r$-VectorSum

This module defines the parameterized `SetPacking`, `ExactCover`, and $\mathbb{F}_2^d$ `VectorSum`
decision problems over canonical framed multi-tape encodings, provides polynomial-time structural
combinators, and proves membership of all three problems in `NP`.

## Main definitions

* `CslibFrontier.ParameterizedComplexity.IsOverGround`,
  `CslibFrontier.ParameterizedComplexity.IsDisjointSelection`,
  `CslibFrontier.ParameterizedComplexity.isOverGroundBool`: well-formedness of candidate sets over
  `S.ground`, pairwise disjointness of index selections in `Cslib.Complexity.SetSystem`, and its
  polynomial-time Boolean checker.
* `CslibFrontier.ParameterizedComplexity.SetPacking`: instances `(S, r)` over `S.ground` admitting
  at
  least `r` pairwise-disjoint sets.
* `CslibFrontier.ParameterizedComplexity.ExactCover`: instances `(S, r)` over `S.ground` admitting
  at
  most `r` pairwise-disjoint sets covering `S.ground`.
* `CslibFrontier.ParameterizedComplexity.VectorSumInstance`,
  `CslibFrontier.ParameterizedComplexity.encVectorSumInstance`,
  `CslibFrontier.ParameterizedComplexity.VectorSumInstance.WellFormed`,
  `CslibFrontier.ParameterizedComplexity.boolListToF2`,
  `CslibFrontier.ParameterizedComplexity.VectorSum`: instances `(vectors, target, dim, r)` over
  $\mathbb{F}_2^{\mathrm{dim}}$ (`Fin dim → ZMod 2`) asking whether at most `r` vectors sum to
  `target`.

## Main results

* `CslibFrontier.ParameterizedComplexity.setPacking_mem_NP`,
  `CslibFrontier.ParameterizedComplexity.exactCover_mem_NP`,
  `CslibFrontier.ParameterizedComplexity.vectorSum_mem_NP`: membership in `NP` via polynomial-time
  subset-witness verifiers.
-/

public section

namespace CslibFrontier.ParameterizedComplexity

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Problem Definitions and Multi-Tape Encodings -/

/-- Every candidate set in `S.sets` consists solely of elements from `S.ground`. -/
@[expose]
def IsOverGround (S : SetSystem) : Prop :=
  ∀ A ∈ S.sets, ∀ x ∈ A, x ∈ S.ground

/-- Semantic characterization of `IsOverGround`. -/
theorem isOverGround_iff (S : SetSystem) :
    IsOverGround S ↔ ∀ A ∈ S.sets, ∀ x ∈ A, x ∈ S.ground :=
  Iff.rfl

/-- The candidate sets indexed by `C` are pairwise disjoint as finite subsets of `ℕ`. -/
@[expose]
def IsDisjointSelection (S : SetSystem) (C : Finset (Fin S.sets.length)) : Prop :=
  (C : Set (Fin S.sets.length)).Pairwise fun i j =>
    Disjoint (S.sets[i].toFinset) (S.sets[j].toFinset)

/-- Semantic characterization of `IsDisjointSelection`. -/
theorem isDisjointSelection_iff (S : SetSystem) (C : Finset (Fin S.sets.length)) :
    IsDisjointSelection S C ↔
      (C : Set (Fin S.sets.length)).Pairwise fun i j =>
        Disjoint (S.sets[i].toFinset) (S.sets[j].toFinset) :=
  Iff.rfl

/-- **Parameterized Set Packing (`PSP`)**: well-formed instances `(S, r)` over `S.ground` admitting
at least `r` pairwise-disjoint candidate sets. -/
@[expose]
def SetPacking : Set (SetSystem × ℕ) :=
  {p | IsOverGround p.1 ∧
    ∃ C : Finset (Fin p.1.sets.length), p.2 ≤ C.card ∧ IsDisjointSelection p.1 C}

/-- Membership characterization for `SetPacking`. -/
theorem mem_setPacking_iff {p : SetSystem × ℕ} :
    p ∈ SetPacking ↔
      IsOverGround p.1 ∧
        ∃ C : Finset (Fin p.1.sets.length), p.2 ≤ C.card ∧ IsDisjointSelection p.1 C :=
  Iff.rfl

/-- **Exact $r$-Covering (`ExactCover`)**: well-formed instances `(S, r)` over `S.ground` admitting
at most `r` pairwise-disjoint candidate sets whose union covers `S.ground`. -/
@[expose]
def ExactCover : Set (SetSystem × ℕ) :=
  {p | IsOverGround p.1 ∧
    ∃ C : Finset (Fin p.1.sets.length),
      C.card ≤ p.2 ∧ p.1.IsCover C ∧ IsDisjointSelection p.1 C}

/-- Membership characterization for `ExactCover`. -/
theorem mem_exactCover_iff {p : SetSystem × ℕ} :
    p ∈ ExactCover ↔
      IsOverGround p.1 ∧
        ∃ C : Finset (Fin p.1.sets.length),
          C.card ≤ p.2 ∧ p.1.IsCover C ∧ IsDisjointSelection p.1 C :=
  Iff.rfl

/-- An instance `(vectors, target, dim, r)` of **$r$-VectorSum** over
$\mathbb{F}_2^{\mathrm{dim}}$. -/
@[ext]
structure VectorSumInstance where
  /-- Collection of candidate bit vectors in $\mathbb{F}_2^{\mathrm{dim}}$. -/
  vectors : List (List Bool)
  /-- Target bit vector $\vec{b} \in \mathbb{F}_2^{\mathrm{dim}}$. -/
  target : List Bool
  /-- Ambient dimension $d$. -/
  dim : ℕ
  /-- Solution cardinality budget $r$. -/
  r : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed binary encoding of `VectorSumInstance`. -/
def encVectorSumInstance : VectorSumInstance ↪ List Bool :=
  ⟨fun x =>
    encPair (encPair (encList encBits) encBits) (encPair encNat encNat)
      ((x.vectors, x.target), (x.dim, x.r)),
   fun a b h => by
    have h' := (encPair (encPair (encList encBits) encBits) (encPair encNat encNat)).injective h
    cases a; cases b; simp_all⟩

/-- Explicit representation of `encVectorSumInstance` via `encPair`. -/
theorem encVectorSumInstance_apply (x : VectorSumInstance) :
    encVectorSumInstance x =
      encPair (encPair (encList encBits) encBits) (encPair encNat encNat)
        ((x.vectors, x.target), (x.dim, x.r)) := by
  rfl

private theorem computableInDegree_vectorSumFields :
    ComputableInDegree
      (fun x : VectorSumInstance => ((x.vectors, x.target), (x.dim, x.r)))
      encVectorSumInstance
      (encPair (encPair (encList encBits) encBits) (encPair encNat encNat)) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `VectorSumInstance.vectors` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_vectorSumVectors {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → VectorSumInstance} (hg : ComputableInPolyTime g encIn encVectorSumInstance) :
    ComputableInPolyTime (fun x => (g x).vectors) encIn (encList encBits) :=
  (ComputableInDegree.fst' (ComputableInDegree.fst'
    computableInDegree_vectorSumFields)).computableInPolyTime.comp hg

/-- Projecting `VectorSumInstance.target` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_vectorSumTarget {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → VectorSumInstance} (hg : ComputableInPolyTime g encIn encVectorSumInstance) :
    ComputableInPolyTime (fun x => (g x).target) encIn encBits :=
  (ComputableInDegree.snd' (ComputableInDegree.fst'
    computableInDegree_vectorSumFields)).computableInPolyTime.comp hg

/-- Projecting `VectorSumInstance.dim` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_vectorSumDim {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → VectorSumInstance} (hg : ComputableInPolyTime g encIn encVectorSumInstance) :
    ComputableInPolyTime (fun x => (g x).dim) encIn encNat :=
  (ComputableInDegree.fst' (ComputableInDegree.snd'
    computableInDegree_vectorSumFields)).computableInPolyTime.comp hg

/-- Projecting `VectorSumInstance.r` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_vectorSumR {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → VectorSumInstance} (hg : ComputableInPolyTime g encIn encVectorSumInstance) :
    ComputableInPolyTime (fun x => (g x).r) encIn encNat :=
  (ComputableInDegree.snd' (ComputableInDegree.snd'
    computableInDegree_vectorSumFields)).computableInPolyTime.comp hg

/-- Constructing a `VectorSumInstance` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_vectorSumMk {γ : Type} {encIn : γ ↪ List Bool}
    {vs : γ → List (List Bool)} {tgt : γ → List Bool} {d r : γ → ℕ}
    (hvs : ComputableInPolyTime vs encIn (encList encBits))
    (htgt : ComputableInPolyTime tgt encIn encBits)
    (hd : ComputableInPolyTime d encIn encNat)
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => VectorSumInstance.mk (vs x) (tgt x) (d x) (r x))
      encIn encVectorSumInstance :=
  ((hvs.prod htgt).prod (hd.prod hr)).of_enc_eq fun _ => rfl

/-- Syntactic well-formedness of a `VectorSumInstance`: `target` and all `vectors` have length
`dim`. -/
@[expose]
def VectorSumInstance.WellFormed (x : VectorSumInstance) : Prop :=
  x.target.length = x.dim ∧ ∀ v ∈ x.vectors, v.length = x.dim

/-- Semantic characterization of `VectorSumInstance.WellFormed`. -/
theorem VectorSumInstance.wellFormed_iff (x : VectorSumInstance) :
    x.WellFormed ↔ x.target.length = x.dim ∧ ∀ v ∈ x.vectors, v.length = x.dim :=
  Iff.rfl

/-- Interpret a Boolean list `v` of length `d` as a vector in $\mathbb{F}_2^d$
(`Fin d → ZMod 2`). -/
@[expose]
def boolListToF2 (d : ℕ) (v : List Bool) : Fin d → ZMod 2 :=
  fun t => if v.getD t.1 false then 1 else 0

/-- Coordinate evaluation of `boolListToF2`. -/
theorem boolListToF2_apply (d : ℕ) (v : List Bool) (t : Fin d) :
    boolListToF2 d v t = if v.getD t.1 false then 1 else 0 :=
  rfl

/-- **$r$-VectorSum (`VectorSum`)**: well-formed instances `(vectors, target, dim, r)` admitting at
most `r` indices whose vectors sum to `target` in $\mathbb{F}_2^{\mathrm{dim}}$. -/
@[expose]
def VectorSum : Set VectorSumInstance :=
  {x | x.WellFormed ∧
    ∃ J : Finset (Fin x.vectors.length),
      J.card ≤ x.r ∧
      (∑ j ∈ J, boolListToF2 x.dim x.vectors[j]) = boolListToF2 x.dim x.target}

/-! ### 2. Boolean Verifiers and `NP` Membership -/

/-- Executable Boolean test for `IsOverGround`. -/
def isOverGroundBool (S : SetSystem) : Bool :=
  S.sets.all fun A => A.all fun x => decide (x ∈ S.ground)

/-- `isOverGroundBool` decides `IsOverGround`. -/
theorem isOverGroundBool_eq_true_iff (S : SetSystem) :
    isOverGroundBool S = true ↔ IsOverGround S := by
  simp [isOverGroundBool, IsOverGround]

open ComputableInPolyTime in
/-- `isOverGroundBool` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_isOverGroundBool :
    ComputableInPolyTime isOverGroundBool encSetSystem encBool := by
  unfold isOverGroundBool
  fun_prop

private def isDisjointList (S : SetSystem) (I : List ℕ) : Bool :=
  I.all (fun i => decide (i < S.sets.length)) &&
    I.all fun i => I.all fun j =>
      decide (i = j) || (S.sets.getD i []).all fun x => decide (x ∉ S.sets.getD j [])

open ComputableInPolyTime in
private theorem computableInPolyTime_isDisjointList :
    ComputableInPolyTime (fun p : SetSystem × List ℕ => isDisjointList p.1 p.2)
      (encPair encSetSystem (encList encUnary)) encBool := by
  unfold isDisjointList
  fun_prop

private theorem isDisjointList_toFinset_iff (S : SetSystem) {I : List ℕ}
    (hI : ∀ i ∈ I, i < S.sets.length) :
    isDisjointList S I = true ↔
      IsDisjointSelection S (Finset.univ.filter fun i : Fin S.sets.length => (i : ℕ) ∈ I.toFinset)
        := by
  simp only [isDisjointList, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, IsDisjointSelection, Set.Pairwise, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_toFinset, Finset.disjoint_left]
  refine ⟨fun ⟨_, hdisj⟩ i hi j hj hij x hxi hxj => ?_, fun h => ⟨hI, fun i hi j hj => ?_⟩⟩
  · have hne : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hij
    have hd := (hdisj i hi j hj).resolve_left hne x
      (by rwa [List.getD_eq_getElem _ _ i.isLt] : x ∈ S.sets.getD i [])
    rw [List.getD_eq_getElem _ _ j.isLt] at hd
    exact hd hxj
  · by_cases hij : i = j
    · exact Or.inl hij
    · right
      intro x hxi hxj
      have hi_lt := hI i hi
      have hj_lt := hI j hj
      rw [List.getD_eq_getElem _ _ hi_lt] at hxi
      rw [List.getD_eq_getElem _ _ hj_lt] at hxj
      exact @h ⟨i, hi_lt⟩ hi ⟨j, hj_lt⟩ hj (fun he => hij (congrArg Fin.val he)) x hxi hxj

private theorem filter_image_val_eq_fin {n : ℕ} (C : Finset (Fin n)) :
    Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ C.image Fin.val) = C := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
  exact ⟨fun ⟨j, hj, hij⟩ => Fin.ext hij ▸ hj, fun hi => ⟨i, hi, rfl⟩⟩

private theorem card_filter_mem_eq_of_lt {n : ℕ} {I_set : Finset ℕ}
    (hI : ∀ v ∈ I_set, v < n) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ I_set)).card = I_set.card :=
  Finset.card_bij (fun i _ => (i : ℕ))
    (fun _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ _ h => Fin.ext h)
    (fun v hv => ⟨⟨v, hI v hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩)

/-- **`SetPacking` belongs to `NP`**, verified by subset witnesses over candidate set indices. -/
theorem setPacking_mem_NP : SetPacking ∈ NP encSetCover := by
  let vs : SetSystem × ℕ → List ℕ := fun p => List.range p.1.sets.length
  let check : (SetSystem × ℕ) × List ℕ → Bool := fun q =>
    isOverGroundBool q.1.1 && decide (q.1.2 ≤ q.2.length) && isDisjointList q.1.1 q.2
  let P : SetSystem × ℕ → Finset ℕ → Prop := fun p I_set =>
    IsOverGround p.1 ∧ p.2 ≤ I_set.card ∧
      IsDisjointSelection p.1 (Finset.univ.filter fun i => (i : ℕ) ∈ I_set)
  have hset : SetPacking = {p | ∃ I_set : Finset ℕ, (∀ v ∈ I_set, v ∈ vs p) ∧ P p I_set} := by
    ext p
    simp only [SetPacking, Set.mem_ofPred_eq, vs, List.mem_range, P]
    constructor
    · rintro ⟨hover, C, hcard, hdisj⟩
      refine ⟨C.image Fin.val, fun v hv => ?_, hover, ?_, ?_⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact i.isLt
      · rwa [Finset.card_image_of_injective _ Fin.val_injective]
      · rwa [filter_image_val_eq_fin]
    · rintro ⟨I_set, hsub, hover, hcard, hdisj⟩
      exact ⟨hover, _, (card_filter_mem_eq_of_lt hsub).symm ▸ hcard, hdisj⟩
  rw [hset]
  refine mem_NP_of_subsetWitness (enc := encSetCover) (encγ := encUnary)
    (vs := vs) (check := check) (P := P)
    (ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.length_list (encList encNat)).comp
        (computableInPolyTime_setSystemSets.comp (ComputableInPolyTime.fst _ _))))
    ?_ (fun p l hnd hl => ?_)
  · open ComputableInPolyTime in
    exact bool_and'
      (bool_and'
        (computableInPolyTime_isOverGroundBool.comp ((fst _ _).comp (fst _ _)))
        (binary_le' ((snd _ _).comp (fst _ _))
          (unary_to_binary.comp ((length_list encUnary).comp (snd _ _)))))
      (computableInPolyTime_isDisjointList.comp
        (((fst _ _).comp (fst _ _)).prod (snd _ _)))
  · have hl_lt : ∀ i ∈ l, i < p.1.sets.length := fun i hi => List.mem_range.mp (hl i hi)
    simp only [check, P, Bool.and_eq_true, isOverGroundBool_eq_true_iff, decide_eq_true_eq,
      List.toFinset_card_of_nodup hnd, isDisjointList_toFinset_iff p.1 hl_lt, and_assoc]

/-- **`ExactCover` belongs to `NP`**, verified by subset witnesses over candidate set indices. -/
theorem exactCover_mem_NP : ExactCover ∈ NP encSetCover := by
  let vs : SetSystem × ℕ → List ℕ := fun p => List.range p.1.sets.length
  let check : (SetSystem × ℕ) × List ℕ → Bool := fun q =>
    isOverGroundBool q.1.1 && decide (q.2.length ≤ q.1.2) &&
      q.1.1.isCoverList q.2 && isDisjointList q.1.1 q.2
  let P : SetSystem × ℕ → Finset ℕ → Prop := fun p I_set =>
    IsOverGround p.1 ∧ I_set.card ≤ p.2 ∧
      p.1.IsCover (Finset.univ.filter fun i => (i : ℕ) ∈ I_set) ∧
      IsDisjointSelection p.1 (Finset.univ.filter fun i => (i : ℕ) ∈ I_set)
  have hset : ExactCover = {p | ∃ I_set : Finset ℕ, (∀ v ∈ I_set, v ∈ vs p) ∧ P p I_set} := by
    ext p
    simp only [ExactCover, Set.mem_ofPred_eq, vs, List.mem_range, P]
    constructor
    · rintro ⟨hover, C, hcard, hcov, hdisj⟩
      refine ⟨C.image Fin.val, fun v hv => ?_, hover, ?_, ?_, ?_⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact i.isLt
      · rwa [Finset.card_image_of_injective _ Fin.val_injective]
      · rwa [filter_image_val_eq_fin]
      · rwa [filter_image_val_eq_fin]
    · rintro ⟨I_set, hsub, hover, hcard, hcov, hdisj⟩
      exact ⟨hover, _, (card_filter_mem_eq_of_lt hsub).symm ▸ hcard, hcov, hdisj⟩
  rw [hset]
  refine mem_NP_of_subsetWitness (enc := encSetCover) (encγ := encUnary)
    (vs := vs) (check := check) (P := P)
    (ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.length_list (encList encNat)).comp
        (computableInPolyTime_setSystemSets.comp (ComputableInPolyTime.fst _ _))))
    ?_ (fun p l hnd hl => ?_)
  · open ComputableInPolyTime in
    have hpair : ComputableInPolyTime (fun q : (SetSystem × ℕ) × List ℕ => (q.1.1, q.2))
        (encWithEntries encSetCover encUnary) (encPair encSetSystem (encList encUnary)) :=
      ((fst _ _).comp (fst _ _)).prod (snd _ _)
    exact bool_and'
      (bool_and'
        (bool_and'
          (computableInPolyTime_isOverGroundBool.comp ((fst _ _).comp (fst _ _)))
          (binary_le' (unary_to_binary.comp ((length_list encUnary).comp (snd _ _)))
            ((snd _ _).comp (fst _ _))))
        (SetSystem.computableInPolyTime_isCoverList.comp hpair))
      (computableInPolyTime_isDisjointList.comp hpair)
  · have hl_lt : ∀ i ∈ l, i < p.1.sets.length := fun i hi => List.mem_range.mp (hl i hi)
    have hcov_iff : p.1.isCoverList l = true ↔
        p.1.IsCover (Finset.univ.filter fun i => (i : ℕ) ∈ l.toFinset) := by
      rw [SetSystem.isCoverList_eq_true_iff]
      refine ⟨fun ⟨_, hc⟩ u hu => ?_, fun hc => ⟨hl_lt, fun u hu => ?_⟩⟩
      · obtain ⟨i, hi_l, hi_lt, hui⟩ := hc u hu
        exact ⟨⟨i, hi_lt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.mem_toFinset.mpr hi_l⟩, hui⟩
      · obtain ⟨idx, hidx, hui⟩ := hc u hu
        exact ⟨idx.1, List.mem_toFinset.mp (Finset.mem_filter.mp hidx).2, idx.isLt, hui⟩
    simp only [check, P, Bool.and_eq_true, isOverGroundBool_eq_true_iff, decide_eq_true_eq,
      List.toFinset_card_of_nodup hnd, hcov_iff, isDisjointList_toFinset_iff p.1 hl_lt, and_assoc]

private def xorCoord (vs : List (List Bool)) (I : List ℕ) (t : ℕ) : Bool :=
  I.foldl (fun b j => xor b ((vs.getD j []).getD t false)) false

private def vectorSumCheck (x : VectorSumInstance) (I : List ℕ) : Bool :=
  decide (x.target.length = x.dim) &&
    x.vectors.all (fun v => decide (v.length = x.dim)) &&
    decide (I.length ≤ x.r) &&
    I.all (fun j => decide (j < x.vectors.length)) &&
    (List.range x.target.length).all fun t =>
      xorCoord x.vectors I t == x.target.getD t false

private theorem bool_toZMod2_xor (a b : Bool) :
    (if xor a b then (1 : ZMod 2) else 0) =
      (if a then (1 : ZMod 2) else 0) + (if b then (1 : ZMod 2) else 0) := by
  cases a <;> cases b <;> decide

private theorem xorCoord_toZMod2 (vs : List (List Bool)) (t : ℕ) :
    ∀ (I : List ℕ) (acc : Bool), I.Nodup → (∀ j ∈ I, j < vs.length) →
      (if I.foldl (fun b j => xor b ((vs.getD j []).getD t false)) acc then (1 : ZMod 2) else 0) =
        (if acc then (1 : ZMod 2) else 0) +
          ∑ j ∈ Finset.univ.filter (fun i : Fin vs.length => (i : ℕ) ∈ I.toFinset),
            (if vs[j].getD t false then (1 : ZMod 2) else 0)
  | [], acc, _, _ => by simp
  | j :: js, acc, hnd, hlt => by
    obtain ⟨hj_not, hnd_js⟩ := List.nodup_cons.mp hnd
    have hj_lt : j < vs.length := hlt j List.mem_cons_self
    have hlt_js : ∀ i ∈ js, i < vs.length := fun i hi => hlt i (List.mem_cons_of_mem _ hi)
    change (if js.foldl (fun b i => xor b ((vs.getD i []).getD t false))
        (xor acc ((vs.getD j []).getD t false)) then (1 : ZMod 2) else 0) = _
    rw [xorCoord_toZMod2 vs t js _ hnd_js hlt_js, bool_toZMod2_xor]
    have hfilt :
        (Finset.univ.filter fun i : Fin vs.length => (i : ℕ) ∈ (j :: js).toFinset) =
          insert ⟨j, hj_lt⟩
            (Finset.univ.filter fun i : Fin vs.length => (i : ℕ) ∈ js.toFinset) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.toFinset_cons,
        Finset.mem_insert, List.mem_toFinset, Fin.ext_iff]
    have hnot_in : (⟨j, hj_lt⟩ : Fin vs.length) ∉
        Finset.univ.filter (fun i : Fin vs.length => (i : ℕ) ∈ js.toFinset) := by
      simp [hj_not]
    rw [hfilt, Finset.sum_insert hnot_in, List.getD_eq_getElem _ _ hj_lt]
    simp only [Fin.getElem_fin]
    ring

open ComputableInPolyTime in
private theorem computableInPolyTime_vectorSumCheck :
    ComputableInPolyTime (fun p : VectorSumInstance × List ℕ => vectorSumCheck p.1 p.2)
      (encPair encVectorSumInstance (encList encUnary)) encBool := by
  let encIn := encPair encVectorSumInstance (encList encUnary)
  have hc1 : ComputableInPolyTime
      (fun p : VectorSumInstance × List ℕ => decide (p.1.target.length = p.1.dim))
      encIn encBool :=
    decide_eq' (unary_to_binary.comp (length_bits_comp
      (computableInPolyTime_vectorSumTarget (fst _ _))))
      (computableInPolyTime_vectorSumDim (fst _ _))
  have hc2 : ComputableInPolyTime
      (fun p : VectorSumInstance × List ℕ =>
        p.1.vectors.all fun v => decide (v.length = p.1.dim))
      encIn encBool :=
    allWithInput (computableInPolyTime_vectorSumVectors (fst _ _))
      (decide_eq' (unary_to_binary.comp (length_bits_comp (snd _ encBits)))
        (computableInPolyTime_vectorSumDim ((fst _ _).comp (fst _ encBits))))
  have hc3 : ComputableInPolyTime
      (fun p : VectorSumInstance × List ℕ => decide (p.2.length ≤ p.1.r))
      encIn encBool :=
    binary_le' (unary_to_binary.comp ((length_list encUnary).comp (snd _ _)))
      (computableInPolyTime_vectorSumR (fst _ _))
  have hc4 : ComputableInPolyTime
      (fun p : VectorSumInstance × List ℕ => p.2.all fun j => decide (j < p.1.vectors.length))
      encIn encBool :=
    allWithInput (snd _ (encList encUnary))
      (unary_lt' (snd _ encUnary)
        ((length_list encBits).comp
          (computableInPolyTime_vectorSumVectors ((fst _ _).comp (fst _ encUnary)))))
  have hxor : ComputableInPolyTime
      (fun q : (VectorSumInstance × List ℕ) × ℕ => xorCoord q.1.1.vectors q.1.2 q.2)
      (encPair encIn encUnary) encBool := by
    unfold xorCoord
    refine foldlWith (encA := encUnary) (encL := encList encUnary) (encB := encBool)
      (par := fun q : (VectorSumInstance × List ℕ) × ℕ => (q.1.1.vectors, q.2))
      (list := fun q => q.1.2)
      (step := fun pt b j => xor b ((pt.1.getD j []).getD pt.2 false))
      ((computableInPolyTime_vectorSumVectors ((fst _ _).comp (fst _ encUnary))).prod
        (snd _ encUnary))
      ((snd _ (encList encUnary)).comp (fst _ encUnary))
      (const false)
      ?_
      (B := fun _ => 1) (.const 1) (fun _ _ _ => by simp)
    have hbit : ComputableInPolyTime
        (fun r : ((List (List Bool) × ℕ) × Bool) × ℕ =>
          ((r.1.1.1.getD r.2 []).getD r.1.1.2 false))
        (encPair (encPair (encPair (encList encBits) encUnary) encBool) encUnary) encBool :=
      bitsGetDWithInput
        (listGetDWithInput
          ((fst (encList encBits) encUnary).comp
            ((fst _ encBool).comp (fst _ encUnary)))
          (snd _ encUnary) [])
        ((snd (encList encBits) encUnary).comp
          ((fst _ encBool).comp (fst _ encUnary))) false
    exact (of_finite (fun p : Bool × Bool => xor p.1 p.2)).comp
      (((snd _ encBool).comp (fst _ encUnary)).prod hbit)
  have hc5 : ComputableInPolyTime
      (fun p : VectorSumInstance × List ℕ =>
        (List.range p.1.target.length).all fun t =>
          xorCoord p.1.vectors p.2 t == p.1.target.getD t false)
      encIn encBool :=
    allWithInput
      (range.comp (length_bits_comp (computableInPolyTime_vectorSumTarget (fst _ _))))
      ((of_finite (fun p : Bool × Bool => p.1 == p.2)).comp
        (hxor.prod (bitsGetDWithInput
          (computableInPolyTime_vectorSumTarget ((fst _ _).comp (fst _ encUnary)))
          (snd _ encUnary) false)))
  exact bool_and' (bool_and' (bool_and' (bool_and' hc1 hc2) hc3) hc4) hc5

/-- **`VectorSum` belongs to `NP`**, verified by subset witnesses over vector indices. -/
theorem vectorSum_mem_NP : VectorSum ∈ NP encVectorSumInstance := by
  let vs : VectorSumInstance → List ℕ := fun x => List.range x.vectors.length
  let check : VectorSumInstance × List ℕ → Bool := fun p => vectorSumCheck p.1 p.2
  let P : VectorSumInstance → Finset ℕ → Prop := fun x I_set =>
    x.WellFormed ∧ I_set.card ≤ x.r ∧
      (∑ j ∈ Finset.univ.filter (fun i : Fin x.vectors.length => (i : ℕ) ∈ I_set),
        boolListToF2 x.dim x.vectors[j]) = boolListToF2 x.dim x.target
  have hset : VectorSum = {x | ∃ I_set : Finset ℕ, (∀ v ∈ I_set, v ∈ vs x) ∧ P x I_set} := by
    ext x
    simp only [VectorSum, Set.mem_ofPred_eq, vs, List.mem_range, P]
    constructor
    · rintro ⟨hwf, J, hcard, hsum⟩
      refine ⟨J.image Fin.val, fun v hv => ?_, hwf, ?_, ?_⟩
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
        exact j.isLt
      · rwa [Finset.card_image_of_injective _ Fin.val_injective]
      · rwa [filter_image_val_eq_fin]
    · rintro ⟨I_set, hsub, hwf, hcard, hsum⟩
      exact ⟨hwf, _, (card_filter_mem_eq_of_lt hsub).symm ▸ hcard, hsum⟩
  rw [hset]
  refine mem_NP_of_subsetWitness (enc := encVectorSumInstance) (encγ := encUnary)
    (vs := vs) (check := check) (P := P)
    (by unfold vs; fun_prop) computableInPolyTime_vectorSumCheck (fun x l hnd hl => ?_)
  have hl_lt : ∀ j ∈ l, j < x.vectors.length := fun j hj => List.mem_range.mp (hl j hj)
  simp only [check, vectorSumCheck, P, VectorSumInstance.WellFormed, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.toFinset_card_of_nodup hnd]
  constructor
  · rintro ⟨⟨⟨⟨htgt_len, hvec_len⟩, hcard⟩, _⟩, hcoords⟩
    refine ⟨⟨htgt_len, hvec_len⟩, hcard, ?_⟩
    ext ⟨t, ht⟩
    simp only [Finset.sum_apply, boolListToF2]
    have ht_tgt : t < x.target.length := htgt_len.symm ▸ ht
    have hcoord_eq := hcoords t ht_tgt
    have hxor_eq := xorCoord_toZMod2 x.vectors t l false hnd hl_lt
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hxor_eq
    rw [← hxor_eq]
    change (if xorCoord x.vectors l t = true then (1 : ZMod 2) else 0) = _
    rw [hcoord_eq]
  · rintro ⟨⟨htgt_len, hvec_len⟩, hcard, hsum⟩
    refine ⟨⟨⟨⟨htgt_len, hvec_len⟩, hcard⟩, hl_lt⟩, fun t ht => ?_⟩
    have ht_dim : t < x.dim := htgt_len ▸ ht
    have hxor_eq := xorCoord_toZMod2 x.vectors t l false hnd hl_lt
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hxor_eq
    have heval := congrFun hsum ⟨t, ht_dim⟩
    simp only [Finset.sum_apply, boolListToF2] at heval
    have h1 : (if xorCoord x.vectors l t then (1 : ZMod 2) else 0) =
        (if x.target.getD t false then (1 : ZMod 2) else 0) :=
      hxor_eq.trans heval
    cases hL : xorCoord x.vectors l t <;> cases hR : x.target.getD t false <;> simp_all

end CslibFrontier.ParameterizedComplexity
