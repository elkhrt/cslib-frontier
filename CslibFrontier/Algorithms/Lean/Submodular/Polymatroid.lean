/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Sym.Card

/-!
# Discrete Polymatroids, Duality, Truncation, and Elongation

This module develops integer-valued submodular rank functions and discrete polymatroids on a finite
ground type `ι`, extending `Cslib.Algorithms.Lean.Submodular.IsSubmodular`. A `RankPolymatroid ι`
bundles a normalized (`rk ∅ = 0`), monotone, submodular rank function `rk : Finset ι → ℕ` with its
associated discrete polymatroid point set `polymatroidPts P ⊆ (ι → ℕ)` and basis set
`polymatroidBases P`.

We prove downward closure, the discrete polymatroid exchange/augmentation property, the uniform
sum characterization of bases `∑ i, α i = P Finset.univ`, box-bounded polymatroid duality (with
involutivity and basis reflection `α ↦ n - α`), rank truncation `min (P I) (P Finset.univ - 1)`,
and polymatroid elongation via dual-truncation-dual, together with their point-set and basis-set
descriptions, submodular truncation-elongation format criteria, and weak-composition basis
cardinality bounds.

## Main definitions

* `Cslib.Algorithms.Lean.Submodular.RankPolymatroid`: normalized monotone submodular rank function
  `Finset ι → ℕ`.
* `Cslib.Algorithms.Lean.Submodular.polymatroidPts`: discrete polymatroid
  `{α : ι → ℕ | ∀ I, ∑ i ∈ I, α i ≤ P I}`.
* `Cslib.Algorithms.Lean.Submodular.IsPolymatroidBasis`,
  `Cslib.Algorithms.Lean.Submodular.polymatroidBases`: maximal integer points of `polymatroidPts P`.
* `Cslib.Algorithms.Lean.Submodular.RankPolymatroid.dual`: box-bounded dual rank polymatroid.
* `Cslib.Algorithms.Lean.Submodular.RankPolymatroid.truncate`: rank truncation at
  `P Finset.univ - 1`.
* `Cslib.Algorithms.Lean.Submodular.RankPolymatroid.elongate`: polymatroid elongation via
  `(P.dual.truncate).dual`.

## Main results

* `Cslib.Algorithms.Lean.Submodular.exists_add_single_mem_polymatroidPts_of_sum_lt`: augmentation
  property for points of smaller coordinate sum.
* `Cslib.Algorithms.Lean.Submodular.isPolymatroidBasis_iff_mem_and_sum_eq`: a point of
  `polymatroidPts P` is a basis if and only if `∑ i, α i = P Finset.univ`.
* `Cslib.Algorithms.Lean.Submodular.RankPolymatroid.dual_dual`,
  `Cslib.Algorithms.Lean.Submodular.polymatroidBases_dual`: duality is involutive and reflects
  bases via `α ↦ n - α`.
* `Cslib.Algorithms.Lean.Submodular.polymatroidPts_truncate`,
  `Cslib.Algorithms.Lean.Submodular.polymatroidBases_truncate`: unit-step downward characterization
  of the truncated polymatroid and its bases.
* `Cslib.Algorithms.Lean.Submodular.polymatroidPts_elongate`,
  `Cslib.Algorithms.Lean.Submodular.polymatroidBases_elongate`: unit-step upward characterization
  of the elongated polymatroid and its bases.
* `Cslib.Algorithms.Lean.Submodular.polymatroidBases_ncard_le_choose`: stars-and-bars bound on the
  number of bases of `RankPolymatroid (Fin l)`.
-/

public section

namespace Cslib.Algorithms.Lean.Submodular

section RankPolymatroid

/-- An integer-valued polymatroid rank function `rk : Finset ι → ℕ`: normalized (`rk ∅ = 0`),
monotone (`I ⊆ J → rk I ≤ rk J`), and submodular (`rk (I ∪ J) + rk (I ∩ J) ≤ rk I + rk J`). -/
@[ext]
structure RankPolymatroid (ι : Type*) [DecidableEq ι] where
  /-- Rank assigned to each finite subset of `ι`. -/
  rk : Finset ι → ℕ
  /-- Empty-set normalization `rk ∅ = 0`. -/
  rk_empty : rk ∅ = 0
  /-- Monotonicity with respect to subset inclusion. -/
  rk_mono : Monotone rk
  /-- Submodular inequality `rk (I ∪ J) + rk (I ∩ J) ≤ rk I + rk J`. -/
  rk_submod : IsSubmodular rk

instance instDFunLikeRankPolymatroid {ι : Type*} [DecidableEq ι] :
    DFunLike (RankPolymatroid ι) (Finset ι) (fun _ ↦ ℕ) where
  coe := RankPolymatroid.rk
  coe_injective P Q h := by
    cases P
    cases Q
    congr

@[simp]
theorem rk_eq_coe {ι : Type*} [DecidableEq ι] (P : RankPolymatroid ι) (I : Finset ι) :
    P.rk I = P I := rfl

/-- The identically zero rank polymatroid on `ι`. -/
def zeroRankPolymatroid (ι : Type*) [DecidableEq ι] : RankPolymatroid ι where
  rk _ := 0
  rk_empty := rfl
  rk_mono _ _ _ := le_rfl
  rk_submod _ _ := le_rfl

instance instInhabitedRankPolymatroid {ι : Type*} [DecidableEq ι] :
    Inhabited (RankPolymatroid ι) :=
  ⟨zeroRankPolymatroid ι⟩

@[simp]
theorem zeroRankPolymatroid_apply {ι : Type*} [DecidableEq ι] (I : Finset ι) :
    zeroRankPolymatroid ι I = 0 := by rfl

/-- Modular rank polymatroid `I ↦ ∑ i ∈ I, w i` attached to weights `w : ι → ℕ`. -/
def modularRankPolymatroid {ι : Type*} [DecidableEq ι] (w : ι → ℕ) : RankPolymatroid ι where
  rk := modularSum w
  rk_empty := modularSum_empty w
  rk_mono := monotone_modularSum fun _ ↦ Nat.zero_le _
  rk_submod := isSubmodular_modularSum w

@[simp]
theorem modularRankPolymatroid_apply {ι : Type*} [DecidableEq ι] (w : ι → ℕ) (I : Finset ι) :
    modularRankPolymatroid w I = ∑ i ∈ I, w i := by rfl

namespace RankPolymatroid

variable {ι : Type*} [DecidableEq ι]

/-- The empty set has rank zero in every `RankPolymatroid`. -/
@[simp]
theorem apply_empty (P : RankPolymatroid ι) : P ∅ = 0 := P.rk_empty

/-- Monotonicity of a `RankPolymatroid` with respect to subset inclusion. -/
theorem apply_mono (P : RankPolymatroid ι) {I J : Finset ι} (hIJ : I ⊆ J) : P I ≤ P J :=
  P.rk_mono hIJ

/-- Submodular inequality `P (I ∪ J) + P (I ∩ J) ≤ P I + P J`. -/
theorem apply_union_add_inter_le (P : RankPolymatroid ι) (I J : Finset ι) :
    P (I ∪ J) + P (I ∩ J) ≤ P I + P J :=
  P.rk_submod I J

/-- Subadditivity `P (I ∪ J) ≤ P I + P J` of any `RankPolymatroid`. -/
theorem apply_union_le (P : RankPolymatroid ι) (I J : Finset ι) :
    P (I ∪ J) ≤ P I + P J :=
  (Nat.le_add_right _ (P (I ∩ J))).trans (P.apply_union_add_inter_le I J)

/-- Difference subadditivity `P (I ∪ J) ≤ P I + P (J \ I)`. -/
theorem apply_union_sdiff_le (P : RankPolymatroid ι) (I J : Finset ι) :
    P (I ∪ J) ≤ P I + P (J \ I) := by
  have hunion : I ∪ (J \ I) = I ∪ J := Finset.union_sdiff_self_eq_union
  have hinter : I ∩ (J \ I) = ∅ := Finset.inter_sdiff_self I J
  have h := P.apply_union_add_inter_le I (J \ I)
  rwa [hunion, hinter, P.apply_empty, add_zero] at h

/-- Truncating a `RankPolymatroid` at `c : ℕ` yields a `RankPolymatroid`. -/
def minConst (P : RankPolymatroid ι) (c : ℕ) : RankPolymatroid ι where
  rk I := min (P I) c
  rk_empty := by simp
  rk_mono := monotone_min_const P.rk_mono c
  rk_submod := P.rk_submod.min_const P.rk_mono c

@[simp]
theorem minConst_apply (P : RankPolymatroid ι) (c : ℕ) (I : Finset ι) :
    P.minConst c I = min (P I) c := by rfl

end RankPolymatroid

end RankPolymatroid

section DiscretePolymatroid

/-- The discrete polymatroid point set `{α : ι → ℕ | ∀ I : Finset ι, ∑ i ∈ I, α i ≤ P I}`
associated to a rank polymatroid `P`. -/
@[expose] def polymatroidPts {ι : Type*} [DecidableEq ι] (P : RankPolymatroid ι) : Set (ι → ℕ) :=
  {α | ∀ I : Finset ι, ∑ i ∈ I, α i ≤ P I}

/-- Membership in `polymatroidPts P` unfolds to the subset-sum inequalities. -/
theorem mem_polymatroidPts_iff {ι : Type*} [DecidableEq ι] {P : RankPolymatroid ι} {α : ι → ℕ} :
    α ∈ polymatroidPts P ↔ ∀ I : Finset ι, ∑ i ∈ I, α i ≤ P I := Iff.rfl

/-- The zero vector belongs to every discrete polymatroid. -/
@[simp]
theorem zero_mem_polymatroidPts {ι : Type*} [DecidableEq ι] (P : RankPolymatroid ι) :
    (0 : ι → ℕ) ∈ polymatroidPts P := by
  intro I
  simp

/-- Discrete polymatroids are downward closed under coordinatewise order. -/
theorem mem_polymatroidPts_of_le {ι : Type*} [DecidableEq ι] {P : RankPolymatroid ι}
    {α β : ι → ℕ} (hα : α ∈ polymatroidPts P) (hβα : β ≤ α) : β ∈ polymatroidPts P := by
  intro I
  exact (Finset.sum_le_sum fun i _ ↦ hβα i).trans (hα I)

/-- Every point `α ∈ polymatroidPts P` has total sum `∑ i, α i ≤ P Finset.univ`. -/
theorem sum_univ_le_of_mem_polymatroidPts {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {α : ι → ℕ} (hα : α ∈ polymatroidPts P) :
    ∑ i, α i ≤ P Finset.univ :=
  hα Finset.univ

/-- Every point `α ∈ polymatroidPts P` satisfies `α i ≤ P {i}` at each coordinate `i`. -/
theorem apply_le_singleton_of_mem_polymatroidPts {ι : Type*} [DecidableEq ι]
    {P : RankPolymatroid ι} {α : ι → ℕ} (hα : α ∈ polymatroidPts P) (i : ι) :
    α i ≤ P {i} := by
  simpa using hα {i}

/-- Every point of `polymatroidPts P` is coordinatewise bounded by `n` under `hbound`. -/
theorem le_of_mem_polymatroidPts_of_le_sum {ι : Type*} [DecidableEq ι]
    {P : RankPolymatroid ι} {n α : ι → ℕ}
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) (hα : α ∈ polymatroidPts P) :
    α ≤ n :=
  fun i ↦ (apply_le_singleton_of_mem_polymatroidPts hα i).trans (by simpa using hbound {i})

private theorem tight_union {ι : Type*} [DecidableEq ι] {P : RankPolymatroid ι} {β : ι → ℕ}
    (hβ : β ∈ polymatroidPts P) {I J : Finset ι}
    (hI : ∑ i ∈ I, β i = P I) (hJ : ∑ i ∈ J, β i = P J) :
    ∑ i ∈ I ∪ J, β i = P (I ∪ J) := by
  have hsub := P.apply_union_add_inter_le I J
  have hsum : (∑ i ∈ I ∪ J, β i) + ∑ i ∈ I ∩ J, β i = (∑ i ∈ I, β i) + ∑ i ∈ J, β i :=
    Finset.sum_union_inter
  have hu := hβ (I ∪ J)
  have hi := hβ (I ∩ J)
  omega

private theorem tight_biUnion {ι : Type*} [DecidableEq ι] {P : RankPolymatroid ι} {β : ι → ℕ}
    (hβ : β ∈ polymatroidPts P) (S : Finset ι) {T : ι → Finset ι}
    (hT : ∀ i ∈ S, ∑ j ∈ T i, β j = P (T i)) :
    ∑ j ∈ S.biUnion T, β j = P (S.biUnion T) := by
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert]
    exact tight_union hβ (hT a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hT i (Finset.mem_insert_of_mem hi))

private theorem sum_pi_single_one_of_mem {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {i : ι} (hi : i ∈ I) :
    ∑ j ∈ I, (Pi.single i 1 : ι → ℕ) j = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact Pi.single_eq_of_ne hji 1
  · intro hnot
    exact False.elim (hnot hi)

private theorem sum_pi_single_one_of_notMem {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {i : ι} (hi : i ∉ I) :
    ∑ j ∈ I, (Pi.single i 1 : ι → ℕ) j = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ Pi.single_eq_of_ne ?_ 1
  intro hji
  exact hi (hji ▸ hj)

private theorem sum_add_single_of_mem {ι : Type*} [DecidableEq ι] (β : ι → ℕ)
    {I : Finset ι} {i : ι} (hi : i ∈ I) :
    ∑ j ∈ I, (β + (Pi.single i 1 : ι → ℕ)) j = (∑ j ∈ I, β j) + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_pi_single_one_of_mem hi]

private theorem sum_add_single_of_notMem {ι : Type*} [DecidableEq ι] (β : ι → ℕ)
    {I : Finset ι} {i : ι} (hi : i ∉ I) :
    ∑ j ∈ I, (β + (Pi.single i 1 : ι → ℕ)) j = ∑ j ∈ I, β j := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_pi_single_one_of_notMem hi, add_zero]

/-- If `β ∈ polymatroidPts P` has total sum strictly below `P Finset.univ`, some unit coordinate
increment `β + Pi.single i 1` remains in `polymatroidPts P`. -/
theorem exists_add_single_mem_polymatroidPts_of_sum_lt_rk_univ
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : RankPolymatroid ι}
    {β : ι → ℕ} (hβ : β ∈ polymatroidPts P) (hlt : ∑ i, β i < P Finset.univ) :
    ∃ i : ι, β + (Pi.single i 1 : ι → ℕ) ∈ polymatroidPts P := by
  by_contra hnone
  push Not at hnone
  have hex : ∀ i : ι, ∃ I : Finset ι, i ∈ I ∧ ∑ j ∈ I, β j = P I := by
    intro i
    have hi := hnone i
    rw [mem_polymatroidPts_iff] at hi
    push Not at hi
    obtain ⟨I, hI⟩ := hi
    by_cases him : i ∈ I
    · have hsum := sum_add_single_of_mem β him
      have hle := hβ I
      exact ⟨I, him, by omega⟩
    · have hsum := sum_add_single_of_notMem β him
      exact False.elim ((hβ I).not_gt (hsum ▸ hI))
  choose T hTmem hTtight using hex
  have huniv : Finset.univ.biUnion T = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    exact ⟨x, hTmem x⟩
  have htight := tight_biUnion hβ Finset.univ (fun i _ ↦ hTtight i)
  rw [huniv] at htight
  exact hlt.ne htight

/-- **Discrete Polymatroid Augmentation**: for `α, β ∈
polymatroidPts P` with `∑ i, β i < ∑ i, α i`, there exists `i : ι` such that
`β + Pi.single i 1 ∈ polymatroidPts P`.
-/
theorem exists_add_single_mem_polymatroidPts_of_sum_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : RankPolymatroid ι} {α β : ι → ℕ}
    (hα : α ∈ polymatroidPts P) (hβ : β ∈ polymatroidPts P)
    (hlt : ∑ i, β i < ∑ i, α i) :
    ∃ i : ι, β + (Pi.single i 1 : ι → ℕ) ∈ polymatroidPts P :=
  exists_add_single_mem_polymatroidPts_of_sum_lt_rk_univ hβ
    (hlt.trans_le (sum_univ_le_of_mem_polymatroidPts hα))

/-- A vector `α : ι → ℕ` is a **basis** of the discrete polymatroid `P` if `α ∈ polymatroidPts P`
and no strictly larger vector belongs to `polymatroidPts P`. -/
@[expose] def IsPolymatroidBasis {ι : Type*} [DecidableEq ι] (P : RankPolymatroid ι)
    (α : ι → ℕ) : Prop :=
  α ∈ polymatroidPts P ∧ ∀ β ∈ polymatroidPts P, α ≤ β → β = α

/-- The set of basis vectors of a discrete polymatroid `P`. -/
@[expose] def polymatroidBases {ι : Type*} [DecidableEq ι] (P : RankPolymatroid ι) :
    Set (ι → ℕ) :=
  {α | IsPolymatroidBasis P α}

/-- Membership in `polymatroidBases P` unfolds to `IsPolymatroidBasis P`. -/
theorem mem_polymatroidBases_iff {ι : Type*} [DecidableEq ι] {P : RankPolymatroid ι}
    {α : ι → ℕ} :
    α ∈ polymatroidBases P ↔ IsPolymatroidBasis P α := Iff.rfl

/-- **Basis Sum Characterization**: `α` is a basis of `P` if and only if `α ∈ polymatroidPts P`
and `∑ i, α i = P Finset.univ`. -/
theorem isPolymatroidBasis_iff_mem_and_sum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {α : ι → ℕ} :
    IsPolymatroidBasis P α ↔ α ∈ polymatroidPts P ∧ ∑ i, α i = P Finset.univ := by
  refine ⟨fun ⟨hα, hmax⟩ ↦ ⟨hα, ?_⟩, fun ⟨hα, hsum⟩ ↦ ⟨hα, fun β hβ hle ↦ ?_⟩⟩
  · have hle := sum_univ_le_of_mem_polymatroidPts hα
    by_contra hne
    obtain ⟨i, hi⟩ := exists_add_single_mem_polymatroidPts_of_sum_lt_rk_univ hα
      (lt_of_le_of_ne hle hne)
    have hle' : α ≤ α + (Pi.single i 1 : ι → ℕ) := fun j ↦ Nat.le_add_right _ _
    have heq := congrFun (hmax _ hi hle') i
    simp at heq
  · have hsumβ : ∑ i, β i ≤ ∑ i, α i := hsum.symm ▸ sum_univ_le_of_mem_polymatroidPts hβ
    have heq : ∑ i, α i = ∑ i, β i := le_antisymm (Finset.sum_le_sum fun i _ ↦ hle i) hsumβ
    funext i
    exact ((Finset.sum_eq_sum_iff_of_le fun j _ ↦ hle j).mp heq i (Finset.mem_univ i)).symm

/-- Every basis `α ∈ polymatroidBases P` has coordinate sum `∑ i, α i = P Finset.univ`. -/
theorem sum_univ_eq_of_isPolymatroidBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {α : ι → ℕ} (hα : IsPolymatroidBasis P α) :
    ∑ i, α i = P Finset.univ :=
  (isPolymatroidBasis_iff_mem_and_sum_eq.mp hα).2

/-- Every point `β ∈ polymatroidPts P` is dominated by at least one basis
`α ∈ polymatroidBases P`. -/
theorem exists_mem_polymatroidBases_ge {ι : Type*} [Finite ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {β : ι → ℕ}
    (hβ : β ∈ polymatroidPts P) : ∃ α ∈ polymatroidBases P, β ≤ α := by
  let _ := Fintype.ofFinite ι
  have haux : ∀ k : ℕ, ∀ γ : ι → ℕ, γ ∈ polymatroidPts P →
      P Finset.univ - ∑ i, γ i = k → ∃ α ∈ polymatroidBases P, γ ≤ α := by
    intro k
    induction k with
    | zero =>
      intro γ hγ hk
      have hle := sum_univ_le_of_mem_polymatroidPts hγ
      have hsum : ∑ i, γ i = P Finset.univ := by omega
      exact ⟨γ, isPolymatroidBasis_iff_mem_and_sum_eq.mpr ⟨hγ, hsum⟩, le_rfl⟩
    | succ k ih =>
      intro γ hγ hk
      have hlt : ∑ i, γ i < P Finset.univ := by omega
      obtain ⟨i, hi⟩ := exists_add_single_mem_polymatroidPts_of_sum_lt_rk_univ hγ hlt
      have hsum' := sum_add_single_of_mem γ (Finset.mem_univ i)
      obtain ⟨α, hα, hle⟩ := ih (γ + (Pi.single i 1 : ι → ℕ)) hi (by omega)
      exact ⟨α, hα, le_trans (fun j ↦ Nat.le_add_right _ _) hle⟩
  exact haux (P Finset.univ - ∑ i, β i) β hβ rfl

/-- A vector belongs to `polymatroidPts P` if and only if it lies coordinatewise below some basis
of `P`. -/
theorem mem_polymatroidPts_iff_exists_basis_ge {ι : Type*} [Finite ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {β : ι → ℕ} :
    β ∈ polymatroidPts P ↔ ∃ α ∈ polymatroidBases P, β ≤ α :=
  ⟨exists_mem_polymatroidBases_ge, fun ⟨_, hα, hle⟩ ↦ mem_polymatroidPts_of_le hα.1 hle⟩

/-- Every discrete polymatroid has at least one basis. -/
theorem polymatroidBases_nonempty {ι : Type*} [Finite ι] [DecidableEq ι]
    (P : RankPolymatroid ι) : (polymatroidBases P).Nonempty := by
  obtain ⟨α, hα, -⟩ := exists_mem_polymatroidBases_ge (zero_mem_polymatroidPts P)
  exact ⟨α, hα⟩

/-! ### Box-Bounded Dual Polymatroid -/

private theorem sum_sub_add_sum_eq {ι : Type*} {n β : ι → ℕ} (hle : β ≤ n) (I : Finset ι) :
    (∑ i ∈ I, (n i - β i)) + ∑ i ∈ I, β i = ∑ i ∈ I, n i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hle i)

private theorem sum_add_sum_sdiff_eq {ι : Type*} [DecidableEq ι] {I J : Finset ι}
    (hIJ : I ⊆ J) (f : ι → ℕ) :
    (∑ i ∈ I, f i) + ∑ i ∈ J \ I, f i = ∑ i ∈ J, f i := by
  rw [add_comm, Finset.sum_sdiff hIJ]

/-- Under `∀ I, P I ≤ ∑ i ∈ I, n i`, `P Finset.univ ≤ P (Finset.univ \ I) + ∑ i ∈ I, n i`. -/
theorem rk_univ_le_sdiff_add_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) {n : ι → ℕ}
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) (I : Finset ι) :
    P Finset.univ ≤ P (Finset.univ \ I) + ∑ i ∈ I, n i := by
  have hunion : (Finset.univ \ I) ∪ I = Finset.univ :=
    Finset.sdiff_union_of_subset (Finset.subset_univ I)
  calc
    P Finset.univ = P ((Finset.univ \ I) ∪ I) := by rw [hunion]
    _ ≤ P (Finset.univ \ I) + P I := P.apply_union_le _ _
    _ ≤ P (Finset.univ \ I) + ∑ i ∈ I, n i := Nat.add_le_add_left (hbound I) _

/-- The **dual rank polymatroid** of `P` with respect to a box bound `n : ι → ℕ` satisfying
`∀ I, P I ≤ ∑ i ∈ I, n i`, with rank `I ↦ P (Finset.univ \ I) + (∑ i ∈ I, n i) - P Finset.univ`. -/
def RankPolymatroid.dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) : RankPolymatroid ι where
  rk I := P (Finset.univ \ I) + (∑ i ∈ I, n i) - P Finset.univ
  rk_empty := by simp
  rk_mono I J hIJ := by
    have hsdiff : Finset.univ \ I = (Finset.univ \ J) ∪ (J \ I) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
      tauto
    have hsub : P (Finset.univ \ I) ≤ P (Finset.univ \ J) + ∑ i ∈ J \ I, n i := by
      rw [hsdiff]
      exact (P.apply_union_le _ _).trans (Nat.add_le_add_left (hbound (J \ I)) _)
    have hsum := sum_add_sum_sdiff_eq hIJ n
    have hI := rk_univ_le_sdiff_add_sum P hbound I
    have hJ := rk_univ_le_sdiff_add_sum P hbound J
    dsimp only
    omega
  rk_submod I J := by
    have hu : Finset.univ \ (I ∪ J) = (Finset.univ \ I) ∩ (Finset.univ \ J) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_univ, true_and]
      tauto
    have hi : Finset.univ \ (I ∩ J) = (Finset.univ \ I) ∪ (Finset.univ \ J) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union, Finset.mem_univ, true_and]
      tauto
    have hP : P (Finset.univ \ (I ∪ J)) + P (Finset.univ \ (I ∩ J)) ≤
        P (Finset.univ \ I) + P (Finset.univ \ J) := by
      rw [hu, hi, add_comm (P ((Finset.univ \ I) ∩ (Finset.univ \ J)))]
      exact P.apply_union_add_inter_le _ _
    have hsum : (∑ i ∈ I ∪ J, n i) + ∑ i ∈ I ∩ J, n i = (∑ i ∈ I, n i) + ∑ i ∈ J, n i :=
      Finset.sum_union_inter
    have h1 := rk_univ_le_sdiff_add_sum P hbound (I ∪ J)
    have h2 := rk_univ_le_sdiff_add_sum P hbound (I ∩ J)
    have h3 := rk_univ_le_sdiff_add_sum P hbound I
    have h4 := rk_univ_le_sdiff_add_sum P hbound J
    dsimp only
    omega

@[simp]
theorem RankPolymatroid.dual_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) (I : Finset ι) :
    P.dual n hbound I = P (Finset.univ \ I) + (∑ i ∈ I, n i) - P Finset.univ := by rfl

theorem RankPolymatroid.dual_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    P.dual n hbound Finset.univ = (∑ i, n i) - P Finset.univ := by
  simp [RankPolymatroid.dual_apply]

/-- The dual rank polymatroid satisfies the same box bound `P.dual n hbound I ≤ ∑ i ∈ I, n i`. -/
theorem RankPolymatroid.dual_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) (I : Finset ι) :
    P.dual n hbound I ≤ ∑ i ∈ I, n i := by
  have hle : P (Finset.univ \ I) ≤ P Finset.univ := P.apply_mono (Finset.subset_univ _)
  have := P.dual_apply n hbound I
  omega

/-- Polymatroid duality with respect to `n` is an involution: `(P.dual n _).dual n _ = P`. -/
@[simp]
theorem RankPolymatroid.dual_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    (P.dual n hbound).dual n (P.dual_le_sum n hbound) = P := by
  ext I
  have hcomp : Finset.univ \ (Finset.univ \ I) = I := by ext x; simp
  have hsum : (∑ i ∈ Finset.univ \ I, n i) + ∑ i ∈ I, n i = ∑ i, n i := by
    rw [add_comm]
    exact sum_add_sum_sdiff_eq (Finset.subset_univ I) n
  have huniv := hbound Finset.univ
  have hI := P.apply_mono (Finset.subset_univ I)
  have hrk := rk_univ_le_sdiff_add_sum P hbound (Finset.univ \ I)
  rw [hcomp] at hrk
  simp only [rk_eq_coe, dual_apply, hcomp, Finset.sdiff_self, apply_empty, zero_add]
  omega

/-- A vector `β` is a basis of `P.dual n hbound` if and only if `β ≤ n`,
`∑ i, β i = (∑ i, n i) - P Finset.univ`, and `∀ I, ∑ i ∈ I, (n i - β i) ≤ P I`. -/
theorem mem_polymatroidBases_dual_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {n β : ι → ℕ}
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    β ∈ polymatroidBases (P.dual n hbound) ↔
      β ≤ n ∧ ∑ i, β i = (∑ i, n i) - P Finset.univ ∧
        ∀ I : Finset ι, ∑ i ∈ I, (n i - β i) ≤ P I := by
  rw [mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq, RankPolymatroid.dual_univ]
  have huniv := hbound Finset.univ
  refine ⟨fun ⟨hβ, hsum⟩ ↦ ?_, fun ⟨hle, hsum, hI⟩ ↦ ⟨fun I ↦ ?_, hsum⟩⟩
  · have hle : β ≤ n := le_of_mem_polymatroidPts_of_le_sum (P.dual_le_sum n hbound) hβ
    refine ⟨hle, hsum, fun I ↦ ?_⟩
    have hdu := hβ (Finset.univ \ I)
    rw [RankPolymatroid.dual_apply, show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hdu
    have hsplitβ := sum_add_sum_sdiff_eq (Finset.subset_univ I) β
    have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
    have hsubI := sum_sub_add_sum_eq hle I
    have hrk := rk_univ_le_sdiff_add_sum P hbound (Finset.univ \ I)
    rw [show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hrk
    omega
  · have hdu := hI (Finset.univ \ I)
    have hsplitβ := sum_add_sum_sdiff_eq (Finset.subset_univ I) β
    have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
    have hsubC := sum_sub_add_sum_eq hle (Finset.univ \ I)
    have hrk := rk_univ_le_sdiff_add_sum P hbound I
    rw [RankPolymatroid.dual_apply]
    omega

/-- **Basis Reflection under Duality**: the basis set of `P.dual n hbound` is the reflection
`(fun α ↦ n - α) '' polymatroidBases P` of the basis set of `P`. -/
theorem polymatroidBases_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    polymatroidBases (P.dual n hbound) = (fun α ↦ n - α) '' polymatroidBases P := by
  have huniv := hbound Finset.univ
  ext β
  rw [mem_polymatroidBases_dual_iff hbound, Set.mem_image]
  refine ⟨fun ⟨hle, hsum, hI⟩ ↦ ⟨n - β, ?_, ?_⟩, ?_⟩
  · rw [mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq]
    have hsub := sum_sub_add_sum_eq hle Finset.univ
    have heq_sub : ∑ i, (n - β) i = ∑ i, (n i - β i) := rfl
    exact ⟨hI, by rw [heq_sub]; omega⟩
  · funext i
    exact Nat.sub_sub_self (hle i)
  · rintro ⟨α, hα, rfl⟩
    rw [mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq] at hα
    have hleα : α ≤ n := le_of_mem_polymatroidPts_of_le_sum hbound hα.1
    have hsub := sum_sub_add_sum_eq hleα Finset.univ
    have heq_sub : ∑ i, (n - α) i = ∑ i, (n i - α i) := rfl
    refine ⟨fun i ↦ Nat.sub_le _ _, by rw [heq_sub]; omega, fun I ↦ ?_⟩
    have heq : ∀ i ∈ I, n i - (n - α) i = α i := fun i _ ↦ Nat.sub_sub_self (hleα i)
    rw [Finset.sum_congr rfl heq]
    exact hα.1 I

/-! ### Truncation and Elongation of Discrete Polymatroids -/

/-- The **truncation** of a rank polymatroid `P`, capping every rank value at
`P Finset.univ - 1`. -/
def RankPolymatroid.truncate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) : RankPolymatroid ι :=
  P.minConst (P Finset.univ - 1)

@[simp]
theorem RankPolymatroid.truncate_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (I : Finset ι) :
    P.truncate I = min (P I) (P Finset.univ - 1) := by rfl

theorem RankPolymatroid.truncate_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) :
    P.truncate Finset.univ = P Finset.univ - 1 := by
  simp [RankPolymatroid.truncate_apply]

/-- When `1 ≤ P Finset.univ`, `polymatroidPts P.truncate` consists of all unit-coordinate
decrements `α - Pi.single j 1` of points `α ∈ polymatroidPts P` with `1 ≤ α j`. -/
theorem polymatroidPts_truncate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} (hpos : 1 ≤ P Finset.univ) :
    polymatroidPts P.truncate =
      {β | ∃ α ∈ polymatroidPts P, ∃ j : ι, 1 ≤ α j ∧ β = α - (Pi.single j 1 : ι → ℕ)} := by
  ext β
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun hβ ↦ ?_, ?_⟩
  · have hβP : β ∈ polymatroidPts P := fun I ↦ (hβ I).trans (min_le_left _ _)
    have hsum : ∑ i, β i ≤ P Finset.univ - 1 := by simpa using hβ Finset.univ
    obtain ⟨j, hj⟩ := exists_add_single_mem_polymatroidPts_of_sum_lt_rk_univ hβP (by omega)
    refine ⟨β + (Pi.single j 1 : ι → ℕ), hj, j, by simp, ?_⟩
    funext i
    by_cases hij : i = j <;> simp [hij]
  · rintro ⟨α, hα, j, hj, rfl⟩
    intro I
    let ej : ι → ℕ := Pi.single j 1
    have hleα : α - ej ≤ α := fun i ↦ Nat.sub_le _ _
    have hI : ∑ i ∈ I, (α - ej) i ≤ P I :=
      (Finset.sum_le_sum fun i _ ↦ hleα i).trans (hα I)
    have h1 : ∑ i : ι, ej i = 1 := sum_pi_single_one_of_mem (Finset.mem_univ j)
    have h2 := sum_sub_add_sum_eq (β := ej) (n := α)
      (fun i ↦ by by_cases hij : i = j <;> simp [ej, hij, hj]) Finset.univ
    have heq_sub : ∑ i, (α - ej) i = ∑ i, (α i - ej i) := rfl
    have huniv := sum_univ_le_of_mem_polymatroidPts hα
    have hsub : ∑ i ∈ I, (α - ej) i ≤ ∑ i, (α - ej) i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ I)
    rw [RankPolymatroid.truncate_apply, le_min_iff]
    refine ⟨hI, ?_⟩
    change ∑ i ∈ I, (α - ej) i ≤ P Finset.univ - 1
    rw [heq_sub] at hsub
    omega

/-- When `1 ≤ P Finset.univ`, `polymatroidBases P.truncate` consists of all unit-coordinate
decrements `α - Pi.single j 1` of bases `α ∈ polymatroidBases P` with `1 ≤ α j`. -/
theorem polymatroidBases_truncate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} (hpos : 1 ≤ P Finset.univ) :
    polymatroidBases P.truncate =
      {β | ∃ α ∈ polymatroidBases P, ∃ j : ι, 1 ≤ α j ∧ β = α - (Pi.single j 1 : ι → ℕ)} := by
  ext β
  rw [mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq,
    RankPolymatroid.truncate_univ, polymatroidPts_truncate hpos]
  simp only [Set.mem_ofPred_eq, mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq]
  refine ⟨fun ⟨⟨α, hα, j, hj, hβ⟩, hsum⟩ ↦ ⟨α, ⟨hα, ?_⟩, j, hj, hβ⟩,
    fun ⟨α, ⟨hα, hsum⟩, j, hj, hβ⟩ ↦ ⟨⟨α, hα, j, hj, hβ⟩, ?_⟩⟩
  · subst hβ
    let ej : ι → ℕ := Pi.single j 1
    have h2 := sum_sub_add_sum_eq (β := ej) (n := α)
      (fun i ↦ by by_cases hij : i = j <;> simp [ej, hij, hj]) Finset.univ
    have h1 : ∑ i : ι, ej i = 1 := sum_pi_single_one_of_mem (Finset.mem_univ j)
    have heq_sub : ∑ i, (α - ej) i = ∑ i, (α i - ej i) := rfl
    have huniv := sum_univ_le_of_mem_polymatroidPts hα
    change ∑ i, (α - ej) i = P Finset.univ - 1 at hsum
    rw [heq_sub] at hsum
    omega
  · subst hβ
    let ej : ι → ℕ := Pi.single j 1
    have h2 := sum_sub_add_sum_eq (β := ej) (n := α)
      (fun i ↦ by by_cases hij : i = j <;> simp [ej, hij, hj]) Finset.univ
    have h1 : ∑ i : ι, ej i = 1 := sum_pi_single_one_of_mem (Finset.mem_univ j)
    have heq_sub : ∑ i, (α - ej) i = ∑ i, (α i - ej i) := rfl
    change ∑ i, (α - ej) i = P Finset.univ - 1
    rw [heq_sub]
    omega

/-- The **elongation** of `P` with respect to a box bound `n : ι → ℕ`, defined as the dual of the
truncation of the dual `(P.dual n hbound).truncate.dual n _`. -/
def RankPolymatroid.elongate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) : RankPolymatroid ι :=
  (P.dual n hbound).truncate.dual n fun I ↦
    (P.dual n hbound).truncate_apply I ▸ (min_le_left _ _).trans (P.dual_le_sum n hbound I)

/-- The elongation of `P` equals the dual of the truncation of the dual of `P`. -/
theorem RankPolymatroid.dual_truncate_dual_eq_elongate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    (P.dual n hbound).truncate.dual n
      (fun I ↦
        (P.dual n hbound).truncate_apply I ▸ (min_le_left _ _).trans (P.dual_le_sum n hbound I)) =
      P.elongate n hbound := by rfl

@[simp]
theorem RankPolymatroid.elongate_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    P.elongate n hbound Finset.univ = min (P Finset.univ + 1) (∑ i, n i) := by
  have huniv := hbound Finset.univ
  unfold RankPolymatroid.elongate
  rw [RankPolymatroid.dual_univ, RankPolymatroid.truncate_univ, RankPolymatroid.dual_univ]
  omega

/-- For nonempty `I`, `(P.elongate n hbound) I = min (P I + 1) (∑ i ∈ I, n i)`. -/
theorem RankPolymatroid.elongate_apply_of_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) {I : Finset ι} (hI : I.Nonempty) :
    P.elongate n hbound I = min (P I + 1) (∑ i ∈ I, n i) := by
  have _ := hI
  have huniv := hbound Finset.univ
  have hcomp : Finset.univ \ (Finset.univ \ I) = I := by ext x; simp
  have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
  have hrk := rk_univ_le_sdiff_add_sum P hbound (Finset.univ \ I)
  rw [hcomp] at hrk
  have hPI := hbound I
  have hPC := hbound (Finset.univ \ I)
  have hleU := P.apply_mono (Finset.subset_univ I)
  unfold RankPolymatroid.elongate
  rw [RankPolymatroid.dual_apply, RankPolymatroid.truncate_apply, RankPolymatroid.dual_apply,
    hcomp, RankPolymatroid.truncate_univ, RankPolymatroid.dual_univ]
  omega

/-- When `P Finset.univ < ∑ i, n i`, the bases of `P.elongate n hbound` are precisely the
unit-coordinate increments `α + Pi.single j 1` of bases `α ∈ polymatroidBases P` with
`α j < n j`. -/
theorem polymatroidBases_elongate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : RankPolymatroid ι} {n : ι → ℕ}
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) (hlt : P Finset.univ < ∑ i, n i) :
    polymatroidBases (P.elongate n hbound) =
      {β | ∃ α ∈ polymatroidBases P, ∃ j : ι, α j < n j ∧ β = α + (Pi.single j 1 : ι → ℕ)} := by
  have hpos : 1 ≤ (P.dual n hbound) Finset.univ := by
    simp only [RankPolymatroid.dual_univ]
    omega
  rw [← RankPolymatroid.dual_truncate_dual_eq_elongate, polymatroidBases_dual,
    polymatroidBases_truncate hpos, polymatroidBases_dual]
  ext β
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨γ, ⟨δ, ⟨α, hα, rfl⟩, j, hj, rfl⟩, rfl⟩
    have hleα : α ≤ n := le_of_mem_polymatroidPts_of_le_sum hbound hα.1
    have hj' : α j < n j := by
      simp only [Pi.sub_apply] at hj
      omega
    refine ⟨α, hα, j, hj', ?_⟩
    funext i
    have hle_i : α i ≤ n i := hleα i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_same]
      omega
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne hij]
      omega
  · rintro ⟨α, hα, j, hj, rfl⟩
    have hleα : α ≤ n := le_of_mem_polymatroidPts_of_le_sum hbound hα.1
    refine ⟨(n - α) - (Pi.single j 1 : ι → ℕ), ⟨n - α, ⟨α, hα, rfl⟩, j, ?_, rfl⟩, ?_⟩
    · simp only [Pi.sub_apply]; omega
    · funext i
      have hle_i : α i ≤ n i := hleα i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_same]
        omega
      · simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne hij]
        omega

/-- Point-set description of `P.elongate n hbound`: `polymatroidPts (P.elongate n hbound)` equals
`polymatroidPts P ∪ {γ | ∃ α ∈ polymatroidPts P, ∃ j, α j < n j ∧ γ = α + Pi.single j 1}`. -/
theorem polymatroidPts_elongate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : RankPolymatroid ι) (n : ι → ℕ)
    (hbound : ∀ I : Finset ι, P I ≤ ∑ i ∈ I, n i) :
    polymatroidPts (P.elongate n hbound) =
      polymatroidPts P ∪
        {γ | ∃ α ∈ polymatroidPts P, ∃ j : ι, α j < n j ∧ γ = α + (Pi.single j 1 : ι → ℕ)} := by
  ext γ
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hγ
    by_cases hlt : P Finset.univ < ∑ i, n i
    · obtain ⟨β, hβ, hγβ⟩ := exists_mem_polymatroidBases_ge hγ
      rw [polymatroidBases_elongate hbound hlt] at hβ
      obtain ⟨α₀, hα₀, j, hj, rfl⟩ := hβ
      by_cases hγj : γ j = 0
      · refine Or.inl (mem_polymatroidPts_of_le hα₀.1 fun i ↦ ?_)
        by_cases hij : i = j
        · subst hij
          exact hγj ▸ Nat.zero_le _
        · simpa [Pi.add_apply, Pi.single_eq_of_ne hij] using hγβ i
      · refine Or.inr ⟨γ - (Pi.single j 1 : ι → ℕ), ?_, j, ?_, ?_⟩
        · refine mem_polymatroidPts_of_le hα₀.1 fun i ↦ ?_
          by_cases hij : i = j
          · subst hij
            have hle_j : γ i ≤ α₀ i + 1 := by
              simpa [Pi.add_apply] using hγβ i
            simp only [Pi.sub_apply, Pi.single_eq_same]
            omega
          · simpa [Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne hij] using hγβ i
        · have hle_j : γ j ≤ α₀ j + 1 := by
            simpa [Pi.add_apply] using hγβ j
          simp only [Pi.sub_apply, Pi.single_eq_same]
          omega
        · funext i
          by_cases hij : i = j
          · subst hij
            simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_same]
            omega
          · simp [Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne hij]
    · refine Or.inl fun I ↦ ?_
      by_cases hI : I.Nonempty
      · have he := P.elongate_apply_of_nonempty n hbound hI
        have huniv := hbound Finset.univ
        have heqU : P Finset.univ = ∑ i, n i := le_antisymm huniv (not_lt.mp hlt)
        have hrk := rk_univ_le_sdiff_add_sum P hbound (Finset.univ \ I)
        rw [show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hrk
        have hPC := hbound (Finset.univ \ I)
        have hPI := hbound I
        have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
        have heqI : P I = ∑ i ∈ I, n i := by omega
        have hγI := hγ I
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hI]
        simp
  · rintro (hγ | ⟨α, hα, j, hj, rfl⟩)
    · intro I
      by_cases hI : I.Nonempty
      · rw [P.elongate_apply_of_nonempty n hbound hI, le_min_iff]
        exact ⟨(hγ I).trans (Nat.le_succ _), (hγ I).trans (hbound I)⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp hI]
        simp
    · intro I
      by_cases hI : I.Nonempty
      · rw [P.elongate_apply_of_nonempty n hbound hI, le_min_iff]
        have hleα : α ≤ n := le_of_mem_polymatroidPts_of_le_sum hbound hα
        by_cases hjI : j ∈ I
        · have hsum := sum_add_single_of_mem α hjI
          have hsum_le_n : (∑ i ∈ I, α i) + 1 ≤ ∑ i ∈ I, n i := by
            rw [← Finset.sum_erase_add _ _ hjI, ← Finset.sum_erase_add _ _ hjI]
            have her := Finset.sum_le_sum fun i (_ : i ∈ I.erase j) ↦ hleα i
            omega
          exact ⟨hsum ▸ Nat.add_le_add_right (hα I) 1, hsum ▸ hsum_le_n⟩
        · have hsum := sum_add_single_of_notMem α hjI
          exact ⟨hsum ▸ (hα I).trans (Nat.le_succ _), hsum ▸ (hα I).trans (hbound I)⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp hI]
        simp

/-! ### Submodular Format Criteria for Truncation and Elongation -/

/-- For `α ≤ n` of total sum `(∑ i, n i) - δ Finset.univ - 1` (with `δ Finset.univ < ∑ i, n i`),
`α` is a basis of `(δ.dual n hbound).truncate` if and only if
`∀ I, I.Nonempty → ∑ i ∈ I, (n i - α i) ≤ δ I + 1`. -/
theorem mem_polymatroidBases_truncate_dual_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {δ : RankPolymatroid ι} {n α : ι → ℕ}
    (hbound : ∀ I : Finset ι, δ I ≤ ∑ i ∈ I, n i) (hlt : δ Finset.univ < ∑ i, n i)
    (hle : α ≤ n) (hsum : ∑ i, α i = (∑ i, n i) - δ Finset.univ - 1) :
    α ∈ polymatroidBases (δ.dual n hbound).truncate ↔
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (n i - α i) ≤ δ I + 1 := by
  rw [mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq,
    RankPolymatroid.truncate_univ, RankPolymatroid.dual_univ]
  simp only [hsum, and_true, mem_polymatroidPts_iff, RankPolymatroid.truncate_apply,
    RankPolymatroid.dual_apply, le_min_iff]
  have hsubU := sum_sub_add_sum_eq hle Finset.univ
  refine ⟨fun h I hI ↦ ?_, fun h I ↦ ⟨?_, ?_⟩⟩
  · have _ := hI
    have hC := (h (Finset.univ \ I)).1
    rw [show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hC
    have hsplitα := sum_add_sum_sdiff_eq (Finset.subset_univ I) α
    have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
    have hsubI := sum_sub_add_sum_eq hle I
    have hrk := rk_univ_le_sdiff_add_sum δ hbound (Finset.univ \ I)
    rw [show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hrk
    omega
  · by_cases hC : (Finset.univ \ I).Nonempty
    · have hCI := h (Finset.univ \ I) hC
      have hsplitα := sum_add_sum_sdiff_eq (Finset.subset_univ I) α
      have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
      have hsubC := sum_sub_add_sum_eq hle (Finset.univ \ I)
      have hrk := rk_univ_le_sdiff_add_sum δ hbound I
      omega
    · have hIeq : I = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        by_contra hx
        exact hC ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩
      subst hIeq
      simp only [Finset.sdiff_self, RankPolymatroid.apply_empty, zero_add]
      omega
  · have hleU := Finset.sum_le_sum_of_subset (Finset.subset_univ I) (f := α)
    omega

/-- For `α ≤ n` of total sum `(∑ i, n i) - δ Finset.univ` (with `δ Finset.univ < ∑ i, n i`),
`α` is a basis of `((δ.dual n hbound).truncate).elongate n _` if and only if
`∀ I, I.Nonempty → ∑ i ∈ I, (n i - α i) ≤ δ I + 1`. -/
theorem mem_polymatroidBases_elongate_truncate_dual_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {δ : RankPolymatroid ι} {n α : ι → ℕ}
    (hbound : ∀ I : Finset ι, δ I ≤ ∑ i ∈ I, n i)
    (hPbound : ∀ I : Finset ι, (δ.dual n hbound).truncate I ≤ ∑ i ∈ I, n i)
    (hlt : δ Finset.univ < ∑ i, n i)
    (hle : α ≤ n) (hsum : ∑ i, α i = (∑ i, n i) - δ Finset.univ) :
    α ∈ polymatroidBases (((δ.dual n hbound).truncate).elongate n hPbound) ↔
      ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, (n i - α i) ≤ δ I + 1 := by
  have hPuniv : (δ.dual n hbound) Finset.univ = (∑ i, n i) - δ Finset.univ :=
    RankPolymatroid.dual_univ δ n hbound
  rw [mem_polymatroidBases_iff, isPolymatroidBasis_iff_mem_and_sum_eq,
    RankPolymatroid.elongate_univ, RankPolymatroid.truncate_univ]
  have hmin_eq : min ((δ.dual n hbound) Finset.univ - 1 + 1) (∑ i, n i) =
      (∑ i, n i) - δ Finset.univ := by
    rw [hPuniv]
    omega
  rw [hmin_eq]
  simp only [hsum, and_true, mem_polymatroidPts_iff]
  have hsubU := sum_sub_add_sum_eq hle Finset.univ
  refine ⟨fun h I hI ↦ ?_, fun h I ↦ ?_⟩
  · have _ := hI
    by_cases hIU : I = Finset.univ
    · subst hIU
      omega
    · have hCne : (Finset.univ \ I).Nonempty := by
        by_contra hCe
        apply hIU
        ext x
        simp only [Finset.mem_univ, iff_true]
        by_contra hx
        exact hCe ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩
      have hC := h (Finset.univ \ I)
      rw [RankPolymatroid.elongate_apply_of_nonempty _ _ hPbound hCne,
        RankPolymatroid.truncate_apply, hPuniv, RankPolymatroid.dual_apply,
        show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hC
      have hsplitα := sum_add_sum_sdiff_eq (Finset.subset_univ I) α
      have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
      have hsubI := sum_sub_add_sum_eq hle I
      have hrk := rk_univ_le_sdiff_add_sum δ hbound (Finset.univ \ I)
      rw [show Finset.univ \ (Finset.univ \ I) = I by ext x; simp] at hrk
      omega
  · by_cases hIne : I.Nonempty
    · rw [RankPolymatroid.elongate_apply_of_nonempty _ _ hPbound hIne,
        RankPolymatroid.truncate_apply, hPuniv, le_min_iff]
      refine ⟨?_, Finset.sum_le_sum fun i _ ↦ hle i⟩
      by_cases hCne : (Finset.univ \ I).Nonempty
      · have hCI := h (Finset.univ \ I) hCne
        have hsplitα := sum_add_sum_sdiff_eq (Finset.subset_univ I) α
        have hsplitn := sum_add_sum_sdiff_eq (Finset.subset_univ I) n
        have hsubC := sum_sub_add_sum_eq hle (Finset.univ \ I)
        have hrk := rk_univ_le_sdiff_add_sum δ hbound I
        have hleU := Finset.sum_le_sum_of_subset (Finset.subset_univ I) (f := α)
        simp only [RankPolymatroid.dual_apply]
        omega
      · have hIeq : I = Finset.univ := by
          ext x
          simp only [Finset.mem_univ, iff_true]
          by_contra hx
          exact hCne ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩
        subst hIeq
        simp only [RankPolymatroid.dual_apply, Finset.sdiff_self,
          RankPolymatroid.apply_empty, zero_add]
        omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hIne]
      simp

private theorem sum_multiset_count_fin {l : ℕ} (M : Multiset (Fin l)) :
    ∑ i : Fin l, Multiset.count i M = Multiset.card M := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have hcons : ∀ i : Fin l,
        Multiset.count i (a ::ₘ M) = (if i = a then 1 else 0) + Multiset.count i M := fun i ↦ by
      rw [Multiset.count_cons, Nat.add_comm]
    simp_rw [hcons]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

/-- **Stars-and-Bars Weak-Composition Cardinality**: for `1 ≤ l` and `m : ℕ`, the number of weak
compositions `α : Fin l → ℕ` with `∑ i, α i = m` is `(m + l - 1).choose (l - 1)`. -/
theorem card_antidiagonalTuple_eq_choose {l : ℕ} (hl : 1 ≤ l) (m : ℕ) :
    (Finset.Nat.antidiagonalTuple l m).card = (m + l - 1).choose (l - 1) := by
  let e : Sym (Fin l) m ≃ Finset.Nat.antidiagonalTuple l m :=
    { toFun := fun s ↦ ⟨fun i ↦ Multiset.count i s.1,
        Finset.Nat.mem_antidiagonalTuple.mpr ((sum_multiset_count_fin s.1).trans s.2)⟩
      invFun := fun x ↦ ⟨∑ i : Fin l, Multiset.replicate (x.1 i) i, by
        rw [Multiset.card_sum]
        simpa [Multiset.card_replicate] using Finset.Nat.mem_antidiagonalTuple.mp x.2⟩
      left_inv := fun s ↦ Subtype.ext (Multiset.ext.mpr fun j ↦ by
        rw [Multiset.count_sum']
        simp only [Multiset.count_replicate]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          exact ite_eq_right hij
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ j)))
      right_inv := fun x ↦ Subtype.ext (funext fun j ↦ by
        dsimp only
        rw [Multiset.count_sum']
        simp only [Multiset.count_replicate]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          exact ite_eq_right hij
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ j))) }
  have hcard : (Finset.Nat.antidiagonalTuple l m).card = Fintype.card (Sym (Fin l) m) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr e.symm
  rw [hcard, Sym.card_sym_eq_choose, Fintype.card_fin]
  have hadd : l + m - 1 = m + (l - 1) := by omega
  rw [hadd, Nat.choose_symm_add]
  congr 1
  omega

/-- **Polymatroid Basis Cardinality Bound**: for `1 ≤ l`, any discrete polymatroid
`δ : RankPolymatroid (Fin l)` has at most `(δ Finset.univ + l - 1).choose (l - 1)` bases. -/
theorem polymatroidBases_ncard_le_choose {l : ℕ} (hl : 1 ≤ l) (δ : RankPolymatroid (Fin l)) :
    (polymatroidBases δ).ncard ≤ (δ Finset.univ + l - 1).choose (l - 1) := by
  have hsub : polymatroidBases δ ⊆
      (Finset.Nat.antidiagonalTuple l (δ Finset.univ) : Set (Fin l → ℕ)) := by
    intro α hα
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]
    exact sum_univ_eq_of_isPolymatroidBasis hα
  calc
    (polymatroidBases δ).ncard
      ≤ (Finset.Nat.antidiagonalTuple l (δ Finset.univ) : Set (Fin l → ℕ)).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.Nat.antidiagonalTuple l (δ Finset.univ)).card := Set.ncard_coe_finset _
    _ = (δ Finset.univ + l - 1).choose (l - 1) :=
      card_antidiagonalTuple_eq_choose hl (δ Finset.univ)

end DiscretePolymatroid

end Cslib.Algorithms.Lean.Submodular
