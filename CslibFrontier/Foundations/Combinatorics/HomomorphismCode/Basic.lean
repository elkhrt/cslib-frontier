/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.InformationTheory.Hamming

import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Homomorphism Codes, Affine Homomorphisms, and Maximum Agreement

This module develops the foundational theory of homomorphism codes over finite domain groups and
arbitrary (possibly infinite) codomain groups:

- Density, equalizers, normalized agreement, and normalized Hamming distance on finite domains;
- Code maximum agreement `Λ_C`, minimum distance `1 - Λ_C`, list balls, and maximum list size;
- Affine-closed subsets, affine closure, and affine homomorphisms `aHom(G, H)`;
- Equivalence of maximum agreement for `Hom(G, H)` and `aHom(G, H)`, subgroup-density bounds,
  the irrelevant kernel, and the minimum nonzero maximum agreement `Λ_G^*`.

All results in this module are proved under standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Main definitions

- `CslibFrontier.HomomorphismCode.density`: normalized cardinality `|S| / |α|` of a subset of a
  finite type.
- `CslibFrontier.HomomorphismCode.equalizer`, `CslibFrontier.HomomorphismCode.equalizerFamily`:
  agreement sets of functions.
- `CslibFrontier.HomomorphismCode.agreement`, `CslibFrontier.HomomorphismCode.normHammingDist`:
  normalized agreement and distance.
- `CslibFrontier.HomomorphismCode.codeMaxAgreement`, `CslibFrontier.HomomorphismCode.codeMinDist`:
  maximum pairwise agreement
  and minimum normalized distance of a code.
- `CslibFrontier.HomomorphismCode.codeListAgr`, `CslibFrontier.HomomorphismCode.maxListSize`:
  agreement lists and maximum list
  size.
- `CslibFrontier.HomomorphismCode.IsAffineClosed`, `CslibFrontier.HomomorphismCode.affineClosure`:
  affine-closed subsets of a
  group and the smallest affine-closed superset of a subset.
- `CslibFrontier.HomomorphismCode.AffineMonoidHom`: affine homomorphisms `φ(a b⁻¹ c) = φ(a) φ(b)⁻¹
  φ(c)`.
- `CslibFrontier.HomomorphismCode.homCode`, `CslibFrontier.HomomorphismCode.aHomCode`,
  `CslibFrontier.HomomorphismCode.homMaxAgreement`:
  homomorphism and affine homomorphism codes and their maximum agreement `Λ_{G, H}`.
- `CslibFrontier.HomomorphismCode.irrelevantKernel`,
  `CslibFrontier.HomomorphismCode.IsIrrelevant`: the intersection of kernels
  of all homomorphisms `G →* H`.
- `CslibFrontier.HomomorphismCode.minMaxAgreement`: the codomain-independent lower bound `Λ_G^*`.

## Main results

- `CslibFrontier.HomomorphismCode.isAffineClosed_iff_empty_or_leftCoset`: an affine-closed subset
  of a group is
  empty or a left coset of a subgroup.
- `CslibFrontier.HomomorphismCode.AffineMonoidHom.equivProd`: bijection `aHom(G, H) ≃ H × Hom(G,
  H)`.
- `CslibFrontier.HomomorphismCode.codeMaxAgreement_homCode_eq`: `Λ_{Hom(G, H)} = Λ_{aHom(G, H)}`.
- `CslibFrontier.HomomorphismCode.homMaxAgreement_le_max_proper_subgroup_density`: `Λ_{G, H}` is
  bounded by the
  largest density of a proper subgroup of `G`.
- `CslibFrontier.HomomorphismCode.homMaxAgreement_quotient_eq`: invariance of `Λ_{G, H}` under
  irrelevant normal
  subgroups.
- `CslibFrontier.HomomorphismCode.minMaxAgreement_le_homMaxAgreement`: `Λ_G^* ≤ Λ_{G, H}` for all
  codomains `H`
  in any universe with `Λ_{G, H} ≠ 0`.
- `CslibFrontier.HomomorphismCode.isSimpleGroup_minMaxAgreement_eq`: for a finite simple group `G`,
  `Λ_G^* = Λ_{G, G}`, and for `|G| > 2` this equals the maximum fixed-point density of a
  nontrivial automorphism.
-/

public section

namespace CslibFrontier.HomomorphismCode

open scoped Pointwise

/-! ### Density, Equalizers, Agreement, and General Codes -/

section GeneralCodes

variable {α β : Type*}

/-- Normalized cardinality (density) `|S| / |α|` of a subset `S` of a finite type `α`. -/
@[expose]
noncomputable def density [Fintype α] (S : Set α) : ℝ :=
  (S.ncard : ℝ) / (Fintype.card α : ℝ)

/-- Equalizer `{x | f x = g x}` of two functions. -/
@[expose]
def equalizer (f g : α → β) : Set α :=
  {x | f x = g x}

/-- Common equalizer of a family of functions. -/
@[expose]
def equalizerFamily (Φ : Set (α → β)) : Set α :=
  {x | ∀ f ∈ Φ, ∀ g ∈ Φ, f x = g x}

/-- Normalized agreement `μ(Eq(f, g))` between two functions on a finite domain. -/
@[expose]
noncomputable def agreement [Fintype α] (f g : α → β) : ℝ :=
  density (equalizer f g)

/-- Normalized Hamming distance `1 - agr(f, g)` between two functions on a finite domain. -/
@[expose]
noncomputable def normHammingDist [Fintype α] (f g : α → β) : ℝ :=
  1 - agreement f g

@[simp]
theorem mem_equalizer_iff {f g : α → β} {x : α} :
    x ∈ equalizer f g ↔ f x = g x :=
  Iff.rfl

theorem mem_equalizerFamily_iff {Φ : Set (α → β)} {x : α} :
    x ∈ equalizerFamily Φ ↔ ∀ f ∈ Φ, ∀ g ∈ Φ, f x = g x :=
  Iff.rfl

theorem equalizer_comm (f g : α → β) : equalizer f g = equalizer g f := by
  ext x
  exact eq_comm

@[simp]
theorem equalizer_self (f : α → β) : equalizer f f = Set.univ := by
  ext x
  simp [equalizer]

theorem density_eq_ncard_div [Fintype α] (S : Set α) :
    density S = (S.ncard : ℝ) / (Fintype.card α : ℝ) :=
  rfl

theorem agreement_eq_density_equalizer [Fintype α] (f g : α → β) :
    agreement f g = density (equalizer f g) :=
  rfl

theorem agreement_eq_ncard_div [Fintype α] (f g : α → β) :
    agreement f g = ((equalizer f g).ncard : ℝ) / (Fintype.card α : ℝ) :=
  rfl

theorem density_nonneg [Fintype α] (S : Set α) : 0 ≤ density S := by
  unfold density
  positivity

theorem density_le_one [Fintype α] (S : Set α) : density S ≤ 1 := by
  unfold density
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [Fintype.card_eq_zero]
  · have hpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    rw [div_le_one hpos]
    exact_mod_cast (Set.ncard_le_ncard (Set.subset_univ S)).trans_eq (by simp [Set.ncard_univ])

theorem density_mono [Fintype α] {S T : Set α} (h : S ⊆ T) : density S ≤ density T := by
  unfold density
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Set.ncard_le_ncard h)) (Nat.cast_nonneg _)

@[simp]
theorem density_empty [Fintype α] : density (∅ : Set α) = 0 := by
  simp [density]

@[simp]
theorem density_univ [Fintype α] [Nonempty α] : density (Set.univ : Set α) = 1 := by
  have hpos : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [density, Set.ncard_univ, hpos]

theorem density_coe [Fintype α] (s : Finset α) :
    density (s : Set α) = (s.card : ℝ) / (Fintype.card α : ℝ) := by
  simp [density]

theorem density_subgroup {G : Type*} [Group G] [Fintype G] (K : Subgroup G) :
    density (K : Set G) = 1 / (K.index : ℝ) := by
  classical
  have hmul := Subgroup.index_mul_card K
  have hcard : (K : Set G).ncard = Nat.card K := (Nat.card_coe_set_eq (K : Set G)).symm
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hidx : (K.index : ℝ) ≠ 0 := by
    intro h0
    have h0' : K.index = 0 := by exact_mod_cast h0
    rw [h0', zero_mul] at hmul
    exact Fintype.card_ne_zero (Nat.card_eq_fintype_card.symm.trans hmul.symm)
  unfold density
  rw [hcard, div_eq_div_iff hG hidx, one_mul]
  have hmulR : (K.index : ℝ) * (Nat.card K : ℝ) = (Fintype.card G : ℝ) := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hmul
  linarith

theorem density_leftCoset {G : Type*} [Group G] [Fintype G] (a : G) (K : Subgroup G) :
    density (a • (K : Set G)) = density (K : Set G) := by
  unfold density
  congr 1
  exact_mod_cast Set.ncard_image_of_injective (K : Set G) (mul_right_injective a)

theorem agreement_nonneg [Fintype α] (f g : α → β) : 0 ≤ agreement f g :=
  density_nonneg _

theorem agreement_le_one [Fintype α] (f g : α → β) : agreement f g ≤ 1 :=
  density_le_one _

theorem agreement_comm [Fintype α] (f g : α → β) : agreement f g = agreement g f := by
  simp [agreement, equalizer_comm]

@[simp]
theorem agreement_self [Fintype α] [Nonempty α] (f : α → β) : agreement f f = 1 := by
  simp [agreement]

theorem agreement_eq_one_iff [Fintype α] [Nonempty α] {f g : α → β} :
    agreement f g = 1 ↔ f = g := by
  constructor
  · intro h
    have hpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    have hcard : (equalizer f g).ncard = Fintype.card α := by
      unfold agreement density at h
      rw [div_eq_one_iff_eq hpos.ne'] at h
      exact_mod_cast h
    have heq : equalizer f g = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
    funext x
    have hx : x ∈ equalizer f g := by rw [heq]; trivial
    exact hx
  · rintro rfl
    exact agreement_self f

theorem normHammingDist_nonneg [Fintype α] (f g : α → β) : 0 ≤ normHammingDist f g :=
  sub_nonneg.mpr (agreement_le_one f g)

theorem normHammingDist_le_one [Fintype α] (f g : α → β) : normHammingDist f g ≤ 1 :=
  sub_le_self 1 (agreement_nonneg f g)

theorem normHammingDist_comm [Fintype α] (f g : α → β) :
    normHammingDist f g = normHammingDist g f := by
  simp [normHammingDist, agreement_comm]

@[simp]
theorem normHammingDist_self [Fintype α] [Nonempty α] (f : α → β) :
    normHammingDist f f = 0 := by
  simp [normHammingDist]

theorem normHammingDist_eq_hammingDist_div [Fintype α] [Nonempty α] [DecidableEq β]
    (f g : α → β) :
    normHammingDist f g = (hammingDist f g : ℝ) / (Fintype.card α : ℝ) := by
  classical
  have hpos : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Finset.univ.filter (fun x => f x = g x)).card + hammingDist f g =
      Fintype.card α := by
    rw [hammingDist]
    simpa only [Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun x => f x = g x)
  have hncard : (equalizer f g).ncard = (Finset.univ.filter (fun x => f x = g x)).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Set.mem_toFinset]
    rfl
  unfold normHammingDist agreement density
  rw [hncard, one_sub_div hpos]
  congr 1
  have hsumR : ((Finset.univ.filter (fun x => f x = g x)).card : ℝ) + (hammingDist f g : ℝ) =
      (Fintype.card α : ℝ) := by exact_mod_cast hsum
  linarith

/-- The maximum pairwise agreement `Λ_C` of a code `C ⊆ (α → β)`, with the convention `0` when
`|C| ≤ 1`. -/
@[expose]
noncomputable def codeMaxAgreement [Fintype α] (C : Set (α → β)) : ℝ :=
  sSup (insert (0 : ℝ) {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r})

/-- The minimum normalized Hamming distance `mindist(C) = 1 - Λ_C` of a code `C`. -/
@[expose]
noncomputable def codeMinDist [Fintype α] (C : Set (α → β)) : ℝ :=
  1 - codeMaxAgreement C

/-- The set of codewords in `C` within normalized Hamming distance `ρ` of `f`. -/
@[expose]
def codeList [Fintype α] (C : Set (α → β)) (f : α → β) (ρ : ℝ) : Set (α → β) :=
  {w ∈ C | normHammingDist w f ≤ ρ}

/-- The set of codewords in `C` having agreement at least `lam` with `f`. -/
@[expose]
def codeListAgr [Fintype α] (C : Set (α → β)) (f : α → β) (lam : ℝ) : Set (α → β) :=
  {w ∈ C | lam ≤ agreement w f}

theorem mem_codeListAgr_iff [Fintype α] {C : Set (α → β)} {f : α → β} {lam : ℝ} {w : α → β} :
    w ∈ codeListAgr C f lam ↔ w ∈ C ∧ lam ≤ agreement w f :=
  Iff.rfl

/-- Maximum list size `ℓ(C, lam)` over all received words `f : α → β` at agreement `lam`. -/
@[expose]
noncomputable def maxListSize [Fintype α] (C : Set (α → β)) (lam : ℝ) : ℕ∞ :=
  ⨆ f : α → β, (codeListAgr C f lam).encard

/-- A class of codes is `CombEcon` (combinatorially economically list-decodable) if there is a
polynomial `P(1/ε)` bound on `ℓ(C, Λ_C + ε)` uniform across the class. -/
@[expose]
def IsCombEconClass {ι : Type*} (C : ι → Σ (α : Type*) (β : Type*), Fintype α × Set (α → β)) :
    Prop :=
  ∃ (K : ℝ) (d : ℕ), 0 < K ∧
    ∀ (i : ι) (ε : ℝ), 0 < ε →
      @maxListSize (C i).1 (C i).2.1 (C i).2.2.1 (C i).2.2.2
        (@codeMaxAgreement (C i).1 (C i).2.1 (C i).2.2.1 (C i).2.2.2 + ε) ≤
        (Nat.floor (K * (1 / ε) ^ d) : ℕ∞)

private theorem agreement_set_finite [Fintype α] (C : Set (α → β)) :
    (insert (0 : ℝ) {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r}).Finite := by
  refine Set.Finite.insert 0 ?_
  have hsub : {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r} ⊆
      (fun k : ℕ => (k : ℝ) / (Fintype.card α : ℝ)) '' (Set.Iic (Fintype.card α)) := by
    rintro r ⟨φ, -, ψ, -, -, rfl⟩
    refine ⟨(equalizer φ ψ).ncard, ?_, rfl⟩
    exact (Set.ncard_le_ncard (Set.subset_univ _)).trans_eq (by simp [Set.ncard_univ])
  exact ((Set.finite_Iic (Fintype.card α)).image _).subset hsub

theorem codeMaxAgreement_nonneg [Fintype α] (C : Set (α → β)) :
    0 ≤ codeMaxAgreement C :=
  le_csSup (agreement_set_finite C).bddAbove (Set.mem_insert 0 _)

theorem agreement_le_codeMaxAgreement [Fintype α] {C : Set (α → β)} {φ ψ : α → β}
    (hφ : φ ∈ C) (hψ : ψ ∈ C) (hne : φ ≠ ψ) :
    agreement φ ψ ≤ codeMaxAgreement C :=
  le_csSup (agreement_set_finite C).bddAbove (Set.mem_insert_of_mem _ ⟨φ, hφ, ψ, hψ, hne, rfl⟩)

theorem codeMaxAgreement_le_one [Fintype α] (C : Set (α → β)) :
    codeMaxAgreement C ≤ 1 := by
  refine csSup_le (Set.insert_nonempty 0 _) ?_
  rintro r (rfl | ⟨φ, -, ψ, -, -, rfl⟩)
  · norm_num
  · exact agreement_le_one φ ψ

theorem codeMaxAgreement_lt_one [Fintype α] [Nonempty α] (C : Set (α → β)) :
    codeMaxAgreement C < 1 := by
  have hfin := agreement_set_finite C
  have hne : (insert (0 : ℝ) {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r}).Nonempty :=
    Set.insert_nonempty 0 _
  obtain ⟨r, hr, hmax⟩ := hfin.toFinset.exists_max_image id (hfin.toFinset_nonempty.mpr hne)
  have hr' : r ∈ insert (0 : ℝ) {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r} :=
    hfin.mem_toFinset.mp hr
  have hsup : codeMaxAgreement C = r :=
    le_antisymm (csSup_le hne fun x hx => hmax x (hfin.mem_toFinset.mpr hx))
      (le_csSup hfin.bddAbove hr')
  rw [hsup]
  rcases hr' with rfl | ⟨φ, -, ψ, -, hne', rfl⟩
  · norm_num
  · exact lt_of_le_of_ne (agreement_le_one φ ψ) (fun h1 => hne' (agreement_eq_one_iff.mp h1))

theorem codeMaxAgreement_eq_zero_of_subsingleton [Fintype α] {C : Set (α → β)}
    (hC : C.Subsingleton) : codeMaxAgreement C = 0 := by
  have h : {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro φ hφ ψ hψ hne
    exact absurd (hC hφ hψ) hne
  simp [codeMaxAgreement, h]

theorem exists_agreement_eq_codeMaxAgreement [Fintype α] {C : Set (α → β)}
    (hC : C.Nontrivial) :
    ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = codeMaxAgreement C := by
  obtain ⟨φ₀, hφ₀, ψ₀, hψ₀, hne₀⟩ := hC
  let S : Set ℝ := {r : ℝ | ∃ φ ∈ C, ∃ ψ ∈ C, φ ≠ ψ ∧ agreement φ ψ = r}
  have hSne : S.Nonempty := ⟨agreement φ₀ ψ₀, φ₀, hφ₀, ψ₀, hψ₀, hne₀, rfl⟩
  have hSfin : S.Finite := (agreement_set_finite C).subset (Set.subset_insert 0 S)
  obtain ⟨r, hr, hmax⟩ := hSfin.toFinset.exists_max_image id (hSfin.toFinset_nonempty.mpr hSne)
  have hr' : r ∈ S := hSfin.mem_toFinset.mp hr
  have hsup : codeMaxAgreement C = r := by
    refine le_antisymm (csSup_le (Set.insert_nonempty 0 S) ?_) ?_
    · rintro x (rfl | hx)
      · obtain ⟨φ, -, ψ, -, -, rfl⟩ := hr'
        exact agreement_nonneg φ ψ
      · exact hmax x (hSfin.mem_toFinset.mpr hx)
    · exact le_csSup (agreement_set_finite C).bddAbove (Set.mem_insert_of_mem 0 hr')
  rcases hr' with ⟨φ, hφ, ψ, hψ, hne, hagr⟩
  exact ⟨φ, hφ, ψ, hψ, hne, hagr.trans hsup.symm⟩

theorem codeMaxAgreement_mono [Fintype α] {C₁ C₂ : Set (α → β)} (h : C₁ ⊆ C₂) :
    codeMaxAgreement C₁ ≤ codeMaxAgreement C₂ := by
  refine csSup_le (Set.insert_nonempty 0 _) ?_
  rintro r (rfl | ⟨φ, hφ, ψ, hψ, hne, rfl⟩)
  · exact codeMaxAgreement_nonneg C₂
  · exact agreement_le_codeMaxAgreement (h hφ) (h hψ) hne

theorem codeList_eq_codeListAgr [Fintype α] (C : Set (α → β)) (f : α → β) (lam : ℝ) :
    codeList C f (1 - lam) = codeListAgr C f lam := by
  ext w
  simp only [codeList, codeListAgr, normHammingDist, Set.mem_sep_iff]
  constructor <;> rintro ⟨hw, h⟩ <;> exact ⟨hw, by linarith⟩

theorem codeList_minDist_sub [Fintype α] (C : Set (α → β)) (f : α → β) (ε : ℝ) :
    codeList C f (codeMinDist C - ε) = codeListAgr C f (codeMaxAgreement C + ε) := by
  rw [← codeList_eq_codeListAgr]
  congr 1
  unfold codeMinDist
  ring

theorem codeListAgr_encard_le_maxListSize [Fintype α] (C : Set (α → β)) (f : α → β) (lam : ℝ) :
    (codeListAgr C f lam).encard ≤ maxListSize C lam :=
  le_iSup (fun g : α → β => (codeListAgr C g lam).encard) f

theorem maxListSize_le_iff [Fintype α] (C : Set (α → β)) (lam : ℝ) (L : ℕ∞) :
    maxListSize C lam ≤ L ↔ ∀ f : α → β, (codeListAgr C f lam).encard ≤ L :=
  iSup_le_iff

theorem maxListSize_antitone [Fintype α] (C : Set (α → β)) {lam₁ lam₂ : ℝ} (h : lam₁ ≤ lam₂) :
    maxListSize C lam₂ ≤ maxListSize C lam₁ := by
  refine iSup_mono fun f => Set.encard_le_encard ?_
  rintro w ⟨hw, hagr⟩
  exact ⟨hw, h.trans hagr⟩

theorem maxListSize_mono_code [Fintype α] {C₁ C₂ : Set (α → β)} (h : C₁ ⊆ C₂) (lam : ℝ) :
    maxListSize C₁ lam ≤ maxListSize C₂ lam := by
  refine iSup_mono fun f => Set.encard_le_encard ?_
  rintro w ⟨hw, hagr⟩
  exact ⟨h hw, hagr⟩

theorem encard_le_floor_iff {γ : Type*} {S : Set γ} {B : ℝ} (hB : 0 ≤ B) :
    S.encard ≤ (Nat.floor B : ℕ∞) ↔ ∀ t : Finset γ, (t : Set γ) ⊆ S → (t.card : ℝ) ≤ B := by
  classical
  constructor
  · intro hS t ht
    have h1 : (t.card : ℕ∞) ≤ (Nat.floor B : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard]
      exact (Set.encard_le_encard ht).trans hS
    have h2 : t.card ≤ Nat.floor B := Nat.cast_le.mp h1
    exact (Nat.cast_le.mpr h2).trans (Nat.floor_le hB)
  · intro hbound
    by_contra hlt
    push Not at hlt
    have hM1 : ((Nat.floor B + 1 : ℕ) : ℕ∞) ≤ S.encard := by
      simpa [Nat.cast_add, Nat.cast_one] using Order.add_one_le_of_lt hlt
    obtain ⟨t, ht_sub, ht_card⟩ := Set.exists_subset_encard_eq hM1
    have htFin : t.Finite := Set.finite_of_encard_eq_coe ht_card
    have hc : htFin.toFinset.card = Nat.floor B + 1 := by
      rw [← Nat.cast_inj (R := ℕ∞), ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
      exact ht_card
    have hle := hbound htFin.toFinset (by simpa using ht_sub)
    have hgt : B < (Nat.floor B + 1 : ℕ) := by simpa using Nat.lt_floor_add_one B
    rw [hc] at hle
    linarith

theorem maxListSize_le_floor_iff [Fintype α] (C : Set (α → β)) (lam : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    maxListSize C lam ≤ (Nat.floor B : ℕ∞) ↔
      ∀ (f : α → β) (t : Finset (α → β)), (t : Set (α → β)) ⊆ codeListAgr C f lam →
        (t.card : ℝ) ≤ B := by
  simp_rw [maxListSize_le_iff, encard_le_floor_iff hB]

theorem maxListSize_eq_zero_of_one_lt [Fintype α] (C : Set (α → β)) {lam : ℝ} (h : 1 < lam) :
    maxListSize C lam = 0 := by
  rw [← le_zero_iff, maxListSize_le_iff]
  intro f
  have hemp : codeListAgr C f lam = ∅ := by
    ext w
    simp only [codeListAgr, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro _
    linarith [agreement_le_one w f]
  simp [hemp]

end GeneralCodes

/-! ### Affine-Closed Subsets and Affine Closure -/

section AffineClosure

variable {G : Type*} [Group G]

/-- A subset `S` of a group `G` is affine-closed if `a * b⁻¹ * c ∈ S` for all `a, b, c ∈ S`. -/
@[expose] def IsAffineClosed (S : Set G) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a * b⁻¹ * c ∈ S

/-- The affine closure `⟨S⟩_aff` is the smallest affine-closed subset of `G` containing `S`. -/
@[expose]
def affineClosure (S : Set G) : Set G :=
  ⋂ (T : Set G) (_ : S ⊆ T) (_ : IsAffineClosed T), T

theorem isAffineClosed_empty : IsAffineClosed (∅ : Set G) :=
  fun _ h => h.elim

theorem isAffineClosed_leftCoset (a : G) (K : Subgroup G) :
    IsAffineClosed (a • (K : Set G)) := by
  intro x hx y hy z hz
  obtain ⟨k₁, hk₁, rfl⟩ := Set.mem_smul_set.mp hx
  obtain ⟨k₂, hk₂, rfl⟩ := Set.mem_smul_set.mp hy
  obtain ⟨k₃, hk₃, rfl⟩ := Set.mem_smul_set.mp hz
  refine Set.mem_smul_set.mpr ⟨k₁ * k₂⁻¹ * k₃, K.mul_mem (K.mul_mem hk₁ (K.inv_mem hk₂)) hk₃, ?_⟩
  simp only [smul_eq_mul]
  group

theorem isAffineClosed_iff_empty_or_leftCoset {S : Set G} :
    IsAffineClosed S ↔ S = ∅ ∨ ∃ (a : G) (K : Subgroup G), S = a • (K : Set G) := by
  constructor
  · intro hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact Or.inl rfl
    · right
      let K : Subgroup G :=
        { carrier := (fun x => a⁻¹ * x) '' S
          mul_mem' := by
            rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
            refine ⟨x * a⁻¹ * y, hS x hx a ha y hy, ?_⟩
            group
          one_mem' := ⟨a, ha, inv_mul_cancel a⟩
          inv_mem' := by
            rintro _ ⟨x, hx, rfl⟩
            refine ⟨a * x⁻¹ * a, hS a ha x hx a ha, ?_⟩
            group }
      refine ⟨a, K, ?_⟩
      ext x
      constructor
      · intro hx
        exact Set.mem_smul_set.mpr ⟨a⁻¹ * x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
      · intro hx
        obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hx
        simpa [smul_eq_mul] using hy
  · rintro (rfl | ⟨a, K, rfl⟩)
    · exact isAffineClosed_empty
    · exact isAffineClosed_leftCoset a K

theorem subset_affineClosure (S : Set G) : S ⊆ affineClosure S := by
  intro x hx
  simp only [affineClosure, Set.mem_iInter]
  intro T hST _
  exact hST hx

theorem isAffineClosed_affineClosure (S : Set G) : IsAffineClosed (affineClosure S) := by
  intro a ha b hb c hc
  simp only [affineClosure, Set.mem_iInter] at ha hb hc ⊢
  intro T hST hT
  exact hT a (ha T hST hT) b (hb T hST hT) c (hc T hST hT)

theorem affineClosure_le {S T : Set G} (hST : S ⊆ T) (hT : IsAffineClosed T) :
    affineClosure S ⊆ T := by
  intro x hx
  simp only [affineClosure, Set.mem_iInter] at hx
  exact hx T hST hT

@[simp]
theorem affineClosure_empty : affineClosure (∅ : Set G) = ∅ :=
  Set.Subset.antisymm (affineClosure_le (Set.empty_subset _) isAffineClosed_empty)
    (Set.empty_subset _)

theorem affineClosure_eq_leftCoset_of_mem {S : Set G} {q : G} (hq : q ∈ S) :
    affineClosure S = q • (Subgroup.closure ((fun r => q⁻¹ * r) '' S) : Set G) := by
  let K : Subgroup G := Subgroup.closure ((fun r => q⁻¹ * r) '' S)
  refine Set.Subset.antisymm ?_ ?_
  · refine affineClosure_le ?_ (isAffineClosed_leftCoset q K)
    intro r hr
    refine ⟨q⁻¹ * r, Subgroup.subset_closure ⟨r, hr, rfl⟩, ?_⟩
    simp [smul_eq_mul]
  · obtain ⟨a, L, hL⟩ :=
      (isAffineClosed_iff_empty_or_leftCoset.mp (isAffineClosed_affineClosure S)).resolve_left
        (Set.Nonempty.ne_empty ⟨q, subset_affineClosure S hq⟩)
    rw [hL]
    have hqL : q ∈ a • (L : Set G) := hL ▸ subset_affineClosure S hq
    obtain ⟨k₀, hk₀, hqk₀⟩ := hqL
    have hcoset : a • (L : Set G) = q • (L : Set G) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨k₀⁻¹ * k, L.mul_mem (L.inv_mem hk₀) hk, ?_⟩
        rw [← hqk₀]; simp only [smul_eq_mul]; group
      · rintro ⟨k, hk, rfl⟩
        refine ⟨k₀ * k, L.mul_mem hk₀ hk, ?_⟩
        rw [← hqk₀]; simp only [smul_eq_mul]; group
    rw [hcoset]
    have hKle : K ≤ L := by
      rw [Subgroup.closure_le]
      rintro _ ⟨r, hr, rfl⟩
      have hrL : r ∈ q • (L : Set G) := by
        rw [← hcoset, ← hL]
        exact subset_affineClosure S hr
      obtain ⟨k, hk, rfl⟩ := hrL
      simpa [smul_eq_mul] using hk
    exact fun x ⟨k, hk, hx⟩ => ⟨k, hKle hk, hx⟩

theorem density_affineClosure_of_mem [Fintype G] {S : Set G} {q : G} (hq : q ∈ S) :
    density (affineClosure S) =
      density (Subgroup.closure ((fun r => q⁻¹ * r) '' S) : Set G) := by
  rw [affineClosure_eq_leftCoset_of_mem hq, density_leftCoset]

end AffineClosure

/-! ### Affine Homomorphisms -/

section AffineHom

/-- An affine homomorphism `φ : G → H` satisfies `φ(a b⁻¹ c) = φ(a) φ(b)⁻¹ φ(c)` for all
`a, b, c ∈ G`; equivalently, `φ` is a left (or right) translate of a group homomorphism. -/
@[ext]
structure AffineMonoidHom (G H : Type*) [Group G] [Group H] where
  /-- The underlying function. -/
  toFun : G → H
  /-- Preservation of the affine ternary operation `a * b⁻¹ * c`. -/
  map_affine' : ∀ a b c : G, toFun (a * b⁻¹ * c) = toFun a * (toFun b)⁻¹ * toFun c

variable {G H : Type*} [Group G] [Group H]

instance : FunLike (AffineMonoidHom G H) G H where
  coe := AffineMonoidHom.toFun
  coe_injective f g h := by cases f; cases g; congr

namespace AffineMonoidHom

theorem map_affine (φ : AffineMonoidHom G H) (a b c : G) :
    φ (a * b⁻¹ * c) = φ a * (φ b)⁻¹ * φ c :=
  φ.map_affine' a b c

/-- Construct an affine homomorphism `g ↦ h * φ₀ g` from an element `h : H` and a group
homomorphism `φ₀ : G →* H`. -/
def mkOfHom (h : H) (φ₀ : G →* H) : AffineMonoidHom G H where
  toFun g := h * φ₀ g
  map_affine' a b c := by
    simp only [map_mul, map_inv, mul_inv_rev]
    group

@[simp]
theorem mkOfHom_apply (h : H) (φ₀ : G →* H) (g : G) :
    mkOfHom h φ₀ g = h * φ₀ g := by
  rfl

/-- Embed a group homomorphism as an affine homomorphism (with translate `1`). -/
def ofMonoidHom (φ₀ : G →* H) : AffineMonoidHom G H :=
  mkOfHom 1 φ₀

@[simp]
theorem ofMonoidHom_apply (φ₀ : G →* H) (g : G) :
    ofMonoidHom φ₀ g = φ₀ g := by
  exact one_mul _

theorem ofMonoidHom_injective : Function.Injective (ofMonoidHom (G := G) (H := H)) := by
  intro φ ψ h
  ext g
  have hg := DFunLike.congr_fun h g
  simpa only [ofMonoidHom_apply] using hg

/-- The unique base homomorphism `φ₀(g) = φ(1)⁻¹ * φ(g)` associated to an affine homomorphism. -/
def baseHom (φ : AffineMonoidHom G H) : G →* H where
  toFun g := (φ 1)⁻¹ * φ g
  map_one' := inv_mul_cancel _
  map_mul' x y := by
    have h := φ.map_affine x 1 y
    simp only [inv_one, mul_one] at h
    rw [h]
    group

theorem baseHom_apply (φ : AffineMonoidHom G H) (g : G) :
    φ.baseHom g = (φ 1)⁻¹ * φ g := by
  rfl

theorem mul_baseHom_apply (φ : AffineMonoidHom G H) (g : G) :
    φ 1 * φ.baseHom g = φ g := by
  simp [baseHom_apply]

theorem baseHom_eq_of_eq (φ : AffineMonoidHom G H) (a g : G) :
    (φ a)⁻¹ * φ (a * g) = φ.baseHom g := by
  have h := φ.map_affine a 1 g
  simp only [inv_one, mul_one] at h
  rw [h, baseHom_apply]
  group

theorem eq_mul_baseHom (φ : AffineMonoidHom G H) (a g : G) :
    φ g = φ a * φ.baseHom (a⁻¹ * g) := by
  have h := φ.baseHom_eq_of_eq a (a⁻¹ * g)
  rw [mul_inv_cancel_left] at h
  rw [← h, mul_inv_cancel_left]

@[simp]
theorem mkOfHom_baseHom (φ : AffineMonoidHom G H) :
    mkOfHom (φ 1) φ.baseHom = φ := by
  ext g
  exact φ.mul_baseHom_apply g

@[simp]
theorem baseHom_mkOfHom (h : H) (φ₀ : G →* H) :
    (mkOfHom h φ₀).baseHom = φ₀ := by
  ext g
  simp [baseHom_apply, mkOfHom_apply]

theorem mkOfHom_one (h : H) (φ₀ : G →* H) :
    mkOfHom h φ₀ 1 = h := by
  simp [mkOfHom_apply]

/-- Equivalence between `AffineMonoidHom G H` and `H × (G →* H)` sending `φ` to `(φ 1, φ.baseHom)`.
-/
def equivProd : AffineMonoidHom G H ≃ H × (G →* H) where
  toFun φ := (φ 1, φ.baseHom)
  invFun p := mkOfHom p.1 p.2
  left_inv φ := mkOfHom_baseHom φ
  right_inv p := Prod.ext (mkOfHom_one p.1 p.2) (baseHom_mkOfHom p.1 p.2)

/-- Right-translate representation `φ(g) = φ.rightBaseHom g * φ 1`. -/
def rightBaseHom (φ : AffineMonoidHom G H) : G →* H where
  toFun g := φ g * (φ 1)⁻¹
  map_one' := mul_inv_cancel _
  map_mul' x y := by
    have h := φ.map_affine x 1 y
    simp only [inv_one, mul_one] at h
    rw [h]
    group

theorem rightBaseHom_mul (φ : AffineMonoidHom G H) (g : G) :
    φ.rightBaseHom g * φ 1 = φ g := by
  simp [rightBaseHom]

/-- Characterization of affine homomorphisms between left cosets `a • G₁` and `b • H₁`. -/
theorem affine_coset_iff {G₁ : Subgroup G} {H₁ : Subgroup H} (a : G) (b : H)
    (f : ↥(a • (G₁ : Set G)) → ↥(b • (H₁ : Set H))) :
    (∀ x y z : ↥(a • (G₁ : Set G)),
        (f x : H) * (f y : H)⁻¹ * (f z : H) =
          (f ⟨(x : G) * (y : G)⁻¹ * (z : G),
            isAffineClosed_leftCoset a G₁ _ x.2 _ y.2 _ z.2⟩ : H)) ↔
      ∃ (h : H) (φ₀ : G₁ →* H₁),
        h ∈ b • (H₁ : Set H) ∧
          ∀ g : G₁, (f ⟨a * g, ⟨g, g.2, rfl⟩⟩ : H) = h * (φ₀ g : H) := by
  constructor
  · intro haff
    have ha : a ∈ a • (G₁ : Set G) := ⟨1, G₁.one_mem, mul_one a⟩
    let h : H := (f ⟨a, ha⟩ : H)
    have hh : h ∈ b • (H₁ : Set H) := (f ⟨a, ha⟩).2
    let φ₀ : G₁ →* H₁ :=
      { toFun := fun g =>
          ⟨h⁻¹ * (f ⟨a * g, ⟨g, g.2, rfl⟩⟩ : H), by
            obtain ⟨u₁, hu₁, h₁⟩ := Set.mem_smul_set.mp hh
            obtain ⟨u₂, hu₂, h₂⟩ := Set.mem_smul_set.mp (f ⟨a * g, ⟨g, g.2, rfl⟩⟩).2
            have heq : h⁻¹ * (f ⟨a * g, ⟨g, g.2, rfl⟩⟩ : H) = u₁⁻¹ * u₂ := by
              rw [← h₁, ← h₂]; simp only [smul_eq_mul]; group
            rw [heq]
            exact H₁.mul_mem (H₁.inv_mem hu₁) hu₂⟩
        map_one' := by
          apply Subtype.ext
          change h⁻¹ * (f ⟨a * (1 : G₁), ⟨1, G₁.one_mem, rfl⟩⟩ : H) = 1
          have ha1 : (⟨a * (1 : G₁), ⟨1, G₁.one_mem, rfl⟩⟩ : ↥(a • (G₁ : Set G))) = ⟨a, ha⟩ :=
            Subtype.ext (mul_one a)
          rw [ha1]
          exact inv_mul_cancel h
        map_mul' := fun x y => by
          apply Subtype.ext
          change h⁻¹ * (f ⟨a * (x * y : G₁), ⟨x * y, (x * y).2, rfl⟩⟩ : H) =
            (h⁻¹ * (f ⟨a * x, ⟨x, x.2, rfl⟩⟩ : H)) * (h⁻¹ * (f ⟨a * y, ⟨y, y.2, rfl⟩⟩ : H))
          have hxy := haff ⟨a * x, ⟨x, x.2, rfl⟩⟩ ⟨a, ha⟩ ⟨a * y, ⟨y, y.2, rfl⟩⟩
          have hsub : (⟨a * (x : G) * a⁻¹ * (a * (y : G)),
              isAffineClosed_leftCoset a G₁ _ ⟨x, x.2, rfl⟩ _ ha _ ⟨y, y.2, rfl⟩⟩ :
              ↥(a • (G₁ : Set G))) = ⟨a * (x * y : G₁), ⟨x * y, (x * y).2, rfl⟩⟩ := by
            apply Subtype.ext
            simp only [Subgroup.coe_mul]
            group
          rw [hsub] at hxy
          rw [← hxy]
          dsimp only [h]
          group }
    refine ⟨h, φ₀, hh, fun g => ?_⟩
    change (f ⟨a * g, ⟨g, g.2, rfl⟩⟩ : H) = h * (h⁻¹ * (f ⟨a * g, ⟨g, g.2, rfl⟩⟩ : H))
    group
  · rintro ⟨h, φ₀, -, hf⟩ x y z
    obtain ⟨gx, hgx, hx⟩ := Set.mem_smul_set.mp x.2
    obtain ⟨gy, hgy, hy⟩ := Set.mem_smul_set.mp y.2
    obtain ⟨gz, hgz, hz⟩ := Set.mem_smul_set.mp z.2
    have hx' : x = ⟨a * gx, ⟨gx, hgx, rfl⟩⟩ := Subtype.ext hx.symm
    have hy' : y = ⟨a * gy, ⟨gy, hgy, rfl⟩⟩ := Subtype.ext hy.symm
    have hz' : z = ⟨a * gz, ⟨gz, hgz, rfl⟩⟩ := Subtype.ext hz.symm
    have hxyz : (⟨(x : G) * (y : G)⁻¹ * (z : G),
        isAffineClosed_leftCoset a G₁ _ x.2 _ y.2 _ z.2⟩ : ↥(a • (G₁ : Set G))) =
        ⟨a * (⟨gx, hgx⟩ * ⟨gy, hgy⟩⁻¹ * ⟨gz, hgz⟩ : G₁),
          ⟨_, (⟨gx, hgx⟩ * ⟨gy, hgy⟩⁻¹ * ⟨gz, hgz⟩ : G₁).2, rfl⟩⟩ := by
      apply Subtype.ext
      rw [hx', hy', hz']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hxyz, hx', hy', hz', hf ⟨gx, hgx⟩, hf ⟨gy, hgy⟩, hf ⟨gz, hgz⟩, hf]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group

end AffineMonoidHom

end AffineHom

/-! ### Homomorphism Codes and Maximum Agreement -/

section HomCode

/-- The homomorphism code `Hom(G, H)` as a subset of `G → H`. -/
@[expose]
def homCode (G H : Type*) [Group G] [Group H] : Set (G → H) :=
  Set.range (fun φ : G →* H => (φ : G → H))

/-- The affine homomorphism code `aHom(G, H)` as a subset of `G → H`. -/
@[expose]
def aHomCode (G H : Type*) [Group G] [Group H] : Set (G → H) :=
  Set.range (fun φ : AffineMonoidHom G H => (φ : G → H))

/-- The maximum agreement `Λ_{G, H} = Λ_{aHom(G, H)}` of the homomorphism code `aHom(G, H)`. -/
@[expose]
noncomputable def homMaxAgreement (G H : Type*) [Group G] [Fintype G] [Group H] : ℝ :=
  codeMaxAgreement (aHomCode G H)

theorem homMaxAgreement_eq_codeMaxAgreement (G H : Type*) [Group G] [Fintype G] [Group H] :
    homMaxAgreement G H = codeMaxAgreement (aHomCode G H) :=
  rfl

theorem homCode_subset_aHomCode (G H : Type*) [Group G] [Group H] :
    homCode G H ⊆ aHomCode G H := by
  rintro _ ⟨φ, rfl⟩
  exact ⟨AffineMonoidHom.ofMonoidHom φ, funext fun g => one_mul (φ g)⟩

variable {G H : Type*} [Group G] [Group H]

/-- The equalizer of two group homomorphisms is a subgroup of `G`. -/
def equalizerSubgroup (φ ψ : G →* H) : Subgroup G where
  carrier := equalizer φ ψ
  one_mem' := by simp [equalizer]
  mul_mem' := by
    intro a b ha hb
    change φ (a * b) = ψ (a * b)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change φ a⁻¹ = ψ a⁻¹
    rw [map_inv, map_inv, ha]

@[simp]
theorem coe_equalizerSubgroup (φ ψ : G →* H) :
    (equalizerSubgroup φ ψ : Set G) = equalizer φ ψ := by
  rfl

@[simp]
theorem mem_equalizerSubgroup_iff (φ ψ : G →* H) (x : G) :
    x ∈ equalizerSubgroup φ ψ ↔ φ x = ψ x :=
  Iff.rfl

theorem equalizer_affineMonoidHom_eq_leftCoset (φ ψ : AffineMonoidHom G H) {g : G}
    (hg : g ∈ equalizer φ ψ) :
    equalizer φ ψ = g • (equalizerSubgroup φ.baseHom ψ.baseHom : Set G) := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ * x, ?_, by simp [smul_eq_mul]⟩
    change φ.baseHom (g⁻¹ * x) = ψ.baseHom (g⁻¹ * x)
    rw [← φ.baseHom_eq_of_eq g (g⁻¹ * x), ← ψ.baseHom_eq_of_eq g (g⁻¹ * x),
      mul_inv_cancel_left]
    change φ g = ψ g at hg
    change φ x = ψ x at hx
    rw [hg, hx]
  · rintro ⟨k, hk, rfl⟩
    change φ (g * k) = ψ (g * k)
    change φ g = ψ g at hg
    change φ.baseHom k = ψ.baseHom k at hk
    rw [φ.eq_mul_baseHom g (g * k), ψ.eq_mul_baseHom g (g * k), inv_mul_cancel_left, hg, hk]

theorem isAffineClosed_equalizer_affineMonoidHom (φ ψ : AffineMonoidHom G H) :
    IsAffineClosed (equalizer φ ψ) := by
  rw [isAffineClosed_iff_empty_or_leftCoset]
  rcases (equalizer φ ψ).eq_empty_or_nonempty with hemp | ⟨g, hg⟩
  · exact Or.inl hemp
  · exact Or.inr ⟨g, equalizerSubgroup φ.baseHom ψ.baseHom,
      equalizer_affineMonoidHom_eq_leftCoset φ ψ hg⟩

theorem affineClosure_subset_equalizer {φ ψ : AffineMonoidHom G H} {S : Set G}
    (hS : ∀ x ∈ S, φ x = ψ x) :
    affineClosure S ⊆ equalizer φ ψ :=
  affineClosure_le hS (isAffineClosed_equalizer_affineMonoidHom φ ψ)

/-- Proposition (Guo): `Λ_{Hom(G, H)} = Λ_{aHom(G, H)}`. -/
theorem codeMaxAgreement_homCode_eq [Fintype G] :
    codeMaxAgreement (homCode G H) = homMaxAgreement G H := by
  refine le_antisymm (codeMaxAgreement_mono (homCode_subset_aHomCode G H)) ?_
  refine csSup_le (Set.insert_nonempty 0 _) ?_
  rintro r (rfl | ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, rfl⟩)
  · exact codeMaxAgreement_nonneg _
  · rcases (equalizer (φ : G → H) ψ).eq_empty_or_nonempty with hemp | ⟨g, hg⟩
    · have h0 : agreement (φ : G → H) ψ = 0 := by simp [agreement, hemp]
      rw [h0]
      exact codeMaxAgreement_nonneg _
    · have hbase_ne : (φ.baseHom : G → H) ≠ ψ.baseHom := by
        intro hEq
        apply hne
        funext x
        change φ x = ψ x
        have hEq' : φ.baseHom = ψ.baseHom := DFunLike.coe_injective hEq
        rw [φ.eq_mul_baseHom g x, ψ.eq_mul_baseHom g x, hEq']
        exact congrArg (· * ψ.baseHom (g⁻¹ * x)) hg
      have hagr : agreement (φ : G → H) ψ = agreement (φ.baseHom : G → H) ψ.baseHom := by
        unfold agreement
        rw [equalizer_affineMonoidHom_eq_leftCoset φ ψ hg, density_leftCoset]
        rfl
      rw [hagr]
      exact agreement_le_codeMaxAgreement ⟨φ.baseHom, rfl⟩ ⟨ψ.baseHom, rfl⟩ hbase_ne

theorem homMaxAgreement_le_max_proper_subgroup_density [Fintype G] :
    ∀ φ ψ : G →* H, φ ≠ ψ →
      ∃ K : Subgroup G, K ≠ ⊤ ∧ agreement (φ : G → H) ψ = density (K : Set G) := by
  intro φ ψ hne
  refine ⟨equalizerSubgroup φ ψ, ?_, rfl⟩
  intro htop
  apply hne
  ext x
  have hx : x ∈ equalizerSubgroup φ ψ := by rw [htop]; trivial
  exact hx

theorem homMaxAgreement_le_half_of_nontrivial [Fintype G] :
    homMaxAgreement G H ≤ 1 / 2 ∨ homMaxAgreement G H = 0 := by
  by_cases h0 : homMaxAgreement G H = 0
  · exact Or.inr h0
  · left
    rw [← codeMaxAgreement_homCode_eq] at h0 ⊢
    have hnt : (homCode G H).Nontrivial := by
      by_contra hsub
      rw [Set.not_nontrivial_iff] at hsub
      exact h0 (codeMaxAgreement_eq_zero_of_subsingleton hsub)
    obtain ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, hmax⟩ := exists_agreement_eq_codeMaxAgreement hnt
    rw [← hmax]
    have hne' : φ ≠ ψ := fun h => hne (by rw [h])
    obtain ⟨K, hK, hagr⟩ := homMaxAgreement_le_max_proper_subgroup_density φ ψ hne'
    rw [hagr, density_subgroup]
    have hidx : 2 ≤ K.index := by
      have hne1 : K.index ≠ 1 := by
        intro h1
        exact hK (Subgroup.index_eq_one.mp h1)
      have hpos : 0 < K.index := by
        have hmul := Subgroup.index_mul_card K
        by_contra hle
        have h0' : K.index = 0 := Nat.eq_zero_of_le_zero (not_lt.mp hle)
        rw [h0', zero_mul] at hmul
        exact Fintype.card_ne_zero (Nat.card_eq_fintype_card.symm.trans hmul.symm)
      omega
    have hidxR : (2 : ℝ) ≤ (K.index : ℝ) := by exact_mod_cast hidx
    exact one_div_le_one_div_of_le (by norm_num) hidxR

theorem homMaxAgreement_lt_one [Fintype G] : homMaxAgreement G H < 1 :=
  codeMaxAgreement_lt_one (aHomCode G H)

theorem eq_of_eqOn_of_homMaxAgreement_lt [Fintype G] {S : Set G}
    (hS : homMaxAgreement G H < density (affineClosure S))
    {φ ψ : AffineMonoidHom G H} (hagree : ∀ x ∈ S, φ x = ψ x) :
    φ = ψ := by
  by_contra hne
  have hne' : (φ : G → H) ≠ ψ := fun h => hne (DFunLike.coe_injective h)
  have hle : density (affineClosure S) ≤ agreement (φ : G → H) ψ :=
    density_mono (affineClosure_subset_equalizer hagree)
  have hle' : agreement (φ : G → H) ψ ≤ homMaxAgreement G H :=
    agreement_le_codeMaxAgreement ⟨φ, rfl⟩ ⟨ψ, rfl⟩ hne'
  linarith

theorem eq_of_eqOn_of_homMaxAgreement_lt_hom [Fintype G] {S : Set G}
    (hS : homMaxAgreement G H < density (Subgroup.closure S : Set G))
    {φ ψ : G →* H} (hagree : ∀ x ∈ S, φ x = ψ x) :
    φ = ψ := by
  by_contra hne
  have hne' : (φ : G → H) ≠ ψ := fun h => hne (DFunLike.coe_injective h)
  have hsub : (Subgroup.closure S : Set G) ⊆ equalizer (φ : G → H) ψ := by
    change (Subgroup.closure S : Set G) ⊆ (equalizerSubgroup φ ψ : Set G)
    rw [SetLike.coe_subset_coe, Subgroup.closure_le]
    exact hagree
  have hle : density (Subgroup.closure S : Set G) ≤ agreement (φ : G → H) ψ := density_mono hsub
  have hle' : agreement (φ : G → H) ψ ≤ homMaxAgreement G H :=
    agreement_le_codeMaxAgreement (homCode_subset_aHomCode G H ⟨φ, rfl⟩)
      (homCode_subset_aHomCode G H ⟨ψ, rfl⟩) hne'
  linarith

theorem homMaxAgreement_mono_codomain [Fintype G] {K : Type*} [Group K] (f : H →* K)
    (hf : Function.Injective f) :
    homMaxAgreement G H ≤ homMaxAgreement G K := by
  rw [← codeMaxAgreement_homCode_eq, ← codeMaxAgreement_homCode_eq]
  refine csSup_le (Set.insert_nonempty 0 _) ?_
  rintro r (rfl | ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, rfl⟩)
  · exact codeMaxAgreement_nonneg _
  · have hne' : (f.comp φ : G → K) ≠ f.comp ψ := by
      intro hEq
      apply hne
      funext x
      exact hf (congrFun hEq x)
    have hagr : agreement (φ : G → H) ψ = agreement (f.comp φ : G → K) (f.comp ψ) := by
      unfold agreement
      congr 1
      ext x
      simp only [mem_equalizer_iff, MonoidHom.comp_apply]
      exact ⟨fun h => congrArg f h, fun h => hf h⟩
    rw [hagr]
    exact agreement_le_codeMaxAgreement ⟨f.comp φ, rfl⟩ ⟨f.comp ψ, rfl⟩ hne'

private theorem homMaxAgreement_le_of_mulEquiv {A B : Type*} [Group A] [Fintype A] [Group B]
    [Fintype B] (e' : A ≃* B) :
    homMaxAgreement A H ≤ homMaxAgreement B H := by
  rw [← codeMaxAgreement_homCode_eq, ← codeMaxAgreement_homCode_eq]
  refine csSup_le (Set.insert_nonempty 0 _) ?_
  rintro r (rfl | ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, rfl⟩)
  · exact codeMaxAgreement_nonneg _
  · have hne' : (φ.comp e'.symm.toMonoidHom : B → H) ≠ ψ.comp e'.symm.toMonoidHom := by
      intro hEq
      apply hne
      funext x
      have := congrFun hEq (e' x)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        using this
    have hagr : agreement (φ : A → H) ψ =
        agreement (φ.comp e'.symm.toMonoidHom : B → H) (ψ.comp e'.symm.toMonoidHom) := by
      unfold agreement density
      have hc : Fintype.card A = Fintype.card B := Fintype.card_congr e'.toEquiv
      rw [hc]
      congr 1
      have himg : equalizer (φ.comp e'.symm.toMonoidHom : B → H) (ψ.comp e'.symm.toMonoidHom) =
          e' '' equalizer (φ : A → H) ψ := by
        ext y
        simp only [mem_equalizer_iff, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          Set.mem_image]
        constructor
        · intro hy
          exact ⟨e'.symm y, hy, e'.apply_symm_apply y⟩
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
      rw [himg, Set.ncard_image_of_injective _ e'.injective]
    rw [hagr]
    exact agreement_le_codeMaxAgreement ⟨φ.comp e'.symm.toMonoidHom, rfl⟩
      ⟨ψ.comp e'.symm.toMonoidHom, rfl⟩ hne'

theorem homMaxAgreement_congr_domain [Fintype G] {G' : Type*} [Group G'] [Fintype G']
    (e : G ≃* G') :
    homMaxAgreement G H = homMaxAgreement G' H :=
  le_antisymm (homMaxAgreement_le_of_mulEquiv e) (homMaxAgreement_le_of_mulEquiv e.symm)

end HomCode

section Irrelevant

/-- The `(G, H)`-irrelevant kernel: intersection of kernels of all homomorphisms `G →* H`. -/
@[expose]
def irrelevantKernel (G H : Type*) [Group G] [Group H] : Subgroup G :=
  ⨅ φ : G →* H, φ.ker

theorem mem_irrelevantKernel_iff {G H : Type*} [Group G] [Group H] {x : G} :
    x ∈ irrelevantKernel G H ↔ ∀ φ : G →* H, φ x = 1 := by
  simp [irrelevantKernel, Subgroup.mem_iInf, MonoidHom.mem_ker]

instance irrelevantKernel_normal {G H : Type*} [Group G] [Group H] :
    (irrelevantKernel G H).Normal :=
  ⟨fun x hx g => mem_irrelevantKernel_iff.mpr fun φ => by
    simp [map_mul, map_inv, mem_irrelevantKernel_iff.mp hx φ]⟩

/-- A subgroup `N ≤ G` is `(G, H)`-irrelevant if it lies inside `irrelevantKernel G H`. -/
@[expose]
def IsIrrelevant (G H : Type*) [Group G] [Group H] (N : Subgroup G) : Prop :=
  N ≤ irrelevantKernel G H

theorem isIrrelevant_iff {G H : Type*} [Group G] [Group H] {N : Subgroup G} :
    IsIrrelevant G H N ↔ ∀ φ : G →* H, N ≤ φ.ker := by
  simp [IsIrrelevant, irrelevantKernel]

/-- Every homomorphism `G →* H` factors uniquely through `G ⧸ N` when `N` is irrelevant. -/
theorem homMaxAgreement_quotient_eq {G H : Type*} [Group G] [Group H] [Fintype G]
    (N : Subgroup G) [N.Normal] (hN : IsIrrelevant G H N) :
    let _ := Fintype.ofFinite (G ⧸ N)
    homMaxAgreement (G ⧸ N) H = homMaxAgreement G H := by
  classical
  intro _
  rw [← codeMaxAgreement_homCode_eq, ← codeMaxAgreement_homCode_eq]
  have hlift_eq : ∀ φ ψ : (G ⧸ N) →* H,
      agreement (φ.comp (QuotientGroup.mk' N) : G → H) (ψ.comp (QuotientGroup.mk' N)) =
        agreement (φ : G ⧸ N → H) ψ := by
    intro φ ψ
    let π := QuotientGroup.mk' N
    have hK : equalizerSubgroup (φ.comp π) (ψ.comp π) = (equalizerSubgroup φ ψ).comap π := rfl
    change density (equalizerSubgroup (φ.comp π) (ψ.comp π) : Set G) =
      density (equalizerSubgroup φ ψ : Set (G ⧸ N))
    rw [hK, density_subgroup, density_subgroup, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective N)]
  refine le_antisymm ?_ ?_
  · refine csSup_le (Set.insert_nonempty 0 _) ?_
    rintro r (rfl | ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, rfl⟩)
    · exact codeMaxAgreement_nonneg _
    · have hne' : (φ.comp (QuotientGroup.mk' N) : G → H) ≠ ψ.comp (QuotientGroup.mk' N) := by
        intro hEq
        apply hne
        funext q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
        exact congrFun hEq x
      rw [← hlift_eq φ ψ]
      exact agreement_le_codeMaxAgreement ⟨φ.comp (QuotientGroup.mk' N), rfl⟩
        ⟨ψ.comp (QuotientGroup.mk' N), rfl⟩ hne'
  · refine csSup_le (Set.insert_nonempty 0 _) ?_
    rintro r (rfl | ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, rfl⟩)
    · exact codeMaxAgreement_nonneg _
    · let φ' : (G ⧸ N) →* H := QuotientGroup.lift N φ (fun x hx => isIrrelevant_iff.mp hN φ hx)
      let ψ' : (G ⧸ N) →* H := QuotientGroup.lift N ψ (fun x hx => isIrrelevant_iff.mp hN ψ hx)
      have hφ' : φ'.comp (QuotientGroup.mk' N) = φ := by ext x; rfl
      have hψ' : ψ'.comp (QuotientGroup.mk' N) = ψ := by ext x; rfl
      have hne' : (φ' : G ⧸ N → H) ≠ ψ' := by
        intro hEq
        apply hne
        funext x
        change φ'.comp (QuotientGroup.mk' N) x = ψ'.comp (QuotientGroup.mk' N) x
        simp [hEq]
      have hagr : agreement (φ : G → H) ψ = agreement (φ' : G ⧸ N → H) ψ' := by
        rw [← hφ', ← hψ', hlift_eq]
      rw [hagr]
      exact agreement_le_codeMaxAgreement ⟨φ', rfl⟩ ⟨ψ', rfl⟩ hne'

/-- The codomain-independent minimum nonzero maximum agreement `Λ_G^*` of a finite group `G`. -/
@[expose]
noncomputable def minMaxAgreement.{u} (G : Type u) [Group G] [Fintype G] : ℝ :=
  sInf {r : ℝ | ∃ (H : Type u) (_ : Group H), homMaxAgreement G H = r ∧ r ≠ 0}

theorem minMaxAgreement_eq_sInf.{u} (G : Type u) [Group G] [Fintype G] :
    minMaxAgreement G =
      sInf {r : ℝ | ∃ (H : Type u) (_ : Group H), homMaxAgreement G H = r ∧ r ≠ 0} :=
  rfl

theorem homMaxAgreement_self_pos {G : Type*} [Group G] [Fintype G] (hG : 1 < Fintype.card G) :
    0 < homMaxAgreement G G := by
  rw [← codeMaxAgreement_homCode_eq]
  have hne : (MonoidHom.id G : G → G) ≠ (1 : G →* G) := by
    intro hEq
    have hnt : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hG
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    exact hx (congrFun hEq x)
  have hpos : (0 : ℝ) < agreement (MonoidHom.id G : G → G) (1 : G →* G) := by
    unfold agreement density
    apply div_pos
    · have hnc : 0 < (equalizer (MonoidHom.id G : G → G) (1 : G →* G)).ncard := by
        rw [Set.ncard_pos]
        exact ⟨(1 : G), by simp [equalizer]⟩
      exact_mod_cast hnc
    · exact Nat.cast_pos.mpr Fintype.card_pos
  exact lt_of_lt_of_le hpos
    (agreement_le_codeMaxAgreement ⟨MonoidHom.id G, rfl⟩ ⟨1, rfl⟩ hne)

/-- Every value `Λ_{G, H}` (for `H` in any universe `v`) is realized by a quotient of
`FreeGroup (G ⊕ G)` in the same universe as `G`. -/
theorem exists_same_universe_homMaxAgreement_eq.{u, v} {G : Type u} [Group G] [Fintype G]
    (H : Type v) [Group H] (hpos : homMaxAgreement G H ≠ 0) :
    ∃ (H' : Type u) (_ : Group H'), homMaxAgreement G H' = homMaxAgreement G H := by
  rw [← codeMaxAgreement_homCode_eq] at hpos
  have hnt : (homCode G H).Nontrivial := by
    by_contra hsub
    rw [Set.not_nontrivial_iff] at hsub
    exact hpos (codeMaxAgreement_eq_zero_of_subsingleton hsub)
  obtain ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, hmax⟩ := exists_agreement_eq_codeMaxAgreement hnt
  let f : FreeGroup (G ⊕ G) →* H := FreeGroup.lift (Sum.elim φ ψ)
  let H' : Type u := FreeGroup (G ⊕ G) ⧸ f.ker
  let e : H' ≃* f.range := QuotientGroup.quotientKerEquivRange f
  have hle : homMaxAgreement G H' ≤ homMaxAgreement G H :=
    homMaxAgreement_mono_codomain (f.range.subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective)
  let φ' : G →* H' :=
    e.symm.toMonoidHom.comp (φ.codRestrict f.range fun g => ⟨FreeGroup.of (Sum.inl g), by
      simp [f]⟩)
  let ψ' : G →* H' :=
    e.symm.toMonoidHom.comp (ψ.codRestrict f.range fun g => ⟨FreeGroup.of (Sum.inr g), by
      simp [f]⟩)
  have hφ' : ∀ g, (f.range.subtype.comp e.toMonoidHom) (φ' g) = φ g := by
    intro g
    simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      MulEquiv.apply_symm_apply]
    rfl
  have hψ' : ∀ g, (f.range.subtype.comp e.toMonoidHom) (ψ' g) = ψ g := by
    intro g
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      MulEquiv.apply_symm_apply]
    rfl
  have hne' : (φ' : G → H') ≠ ψ' := by
    intro hEq
    apply hne
    funext g
    change φ g = ψ g
    rw [← hφ' g, ← hψ' g, congrFun hEq g]
  have hagr : agreement (φ' : G → H') ψ' = agreement (φ : G → H) ψ := by
    unfold agreement
    congr 1
    ext g
    simp only [mem_equalizer_iff]
    constructor
    · intro hg
      rw [← hφ' g, ← hψ' g, hg]
    · intro hg
      apply Subtype.val_injective.comp e.injective
      change (f.range.subtype.comp e.toMonoidHom) (φ' g) =
        (f.range.subtype.comp e.toMonoidHom) (ψ' g)
      rw [hφ' g, hψ' g, hg]
  have hge : codeMaxAgreement (homCode G H) ≤ homMaxAgreement G H' := by
    rw [← codeMaxAgreement_homCode_eq, ← hmax, ← hagr]
    exact agreement_le_codeMaxAgreement ⟨φ', rfl⟩ ⟨ψ', rfl⟩ hne'
  rw [codeMaxAgreement_homCode_eq] at hge
  exact ⟨H', inferInstance, le_antisymm hle hge⟩

theorem minMaxAgreement_le_homMaxAgreement.{u, v} {G : Type u} [Group G] [Fintype G]
    (H : Type v) [Group H] (hpos : homMaxAgreement G H ≠ 0) :
    minMaxAgreement G ≤ homMaxAgreement G H := by
  obtain ⟨H', _, hH'⟩ := exists_same_universe_homMaxAgreement_eq H hpos
  rw [← hH']
  refine csInf_le ⟨0, ?_⟩ ⟨H', inferInstance, rfl, hH'.symm ▸ hpos⟩
  rintro r ⟨H'', _, rfl, -⟩
  exact codeMaxAgreement_nonneg _

theorem minMaxAgreement_pos.{u} {G : Type u} [Group G] [Fintype G] (hG : 1 < Fintype.card G) :
    0 < minMaxAgreement G := by
  let S : Set ℝ := {r : ℝ | ∃ (H : Type u) (_ : Group H), homMaxAgreement G H = r ∧ r ≠ 0}
  have hSne : S.Nonempty := ⟨homMaxAgreement G G, G, inferInstance, rfl,
    (homMaxAgreement_self_pos hG).ne'⟩
  have hSfin : S.Finite := by
    have hsub : S ⊆ (fun k : ℕ => (k : ℝ) / (Fintype.card G : ℝ)) ''
        (Set.Iic (Fintype.card G)) := by
      rintro r ⟨H, _, rfl, hr0⟩
      rw [← codeMaxAgreement_homCode_eq] at hr0 ⊢
      have hnt : (homCode G H).Nontrivial := by
        by_contra hsub
        rw [Set.not_nontrivial_iff] at hsub
        exact hr0 (codeMaxAgreement_eq_zero_of_subsingleton hsub)
      obtain ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, _, hmax⟩ := exists_agreement_eq_codeMaxAgreement hnt
      refine ⟨(equalizer (φ : G → H) ψ).ncard, ?_, hmax⟩
      exact (Set.ncard_le_ncard (Set.subset_univ _)).trans_eq (by simp [Set.ncard_univ])
    exact ((Set.finite_Iic (Fintype.card G)).image _).subset hsub
  obtain ⟨r, hr, hmin⟩ := hSfin.toFinset.exists_min_image id (hSfin.toFinset_nonempty.mpr hSne)
  have hr' : r ∈ S := hSfin.mem_toFinset.mp hr
  have hinf : minMaxAgreement G = r :=
    le_antisymm (csInf_le ⟨0, fun x ⟨_, _, hx, _⟩ => hx ▸ codeMaxAgreement_nonneg _⟩ hr')
      (le_csInf hSne fun x hx => hmin x (hSfin.mem_toFinset.mpr hx))
  rw [hinf]
  obtain ⟨H, _, rfl, hr0⟩ := hr'
  exact lt_of_le_of_ne (codeMaxAgreement_nonneg _) hr0.symm

/-- For a finite simple group `G`, `Λ_G^* = Λ_{G, G}`. -/
theorem isSimpleGroup_minMaxAgreement_eq.{u} (G : Type u) [Group G] [Fintype G]
    [IsSimpleGroup G] :
    minMaxAgreement G = homMaxAgreement G G := by
  have hG : 1 < Fintype.card G := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  refine le_antisymm (minMaxAgreement_le_homMaxAgreement G (homMaxAgreement_self_pos hG).ne') ?_
  refine le_csInf ⟨homMaxAgreement G G, G, inferInstance, rfl, (homMaxAgreement_self_pos hG).ne'⟩ ?_
  rintro r ⟨H, _, rfl, hr0⟩
  rw [← codeMaxAgreement_homCode_eq] at hr0
  have hnt : (homCode G H).Nontrivial := by
    by_contra hsub
    rw [Set.not_nontrivial_iff] at hsub
    exact hr0 (codeMaxAgreement_eq_zero_of_subsingleton hsub)
  obtain ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, -⟩ := exists_agreement_eq_codeMaxAgreement hnt
  have hex : ∃ θ : G →* H, Function.Injective θ := by
    by_cases hφ : φ = 1
    · have hψ : ψ ≠ 1 := fun h => hne (by rw [hφ, h])
      refine ⟨ψ, (MonoidHom.ker_eq_bot_iff ψ).mp ?_⟩
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker).resolve_right
        (fun htop => hψ (by ext x; exact (MonoidHom.mem_ker.mp (htop ▸ trivial))))
    · refine ⟨φ, (MonoidHom.ker_eq_bot_iff φ).mp ?_⟩
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker).resolve_right
        (fun htop => hφ (by ext x; exact (MonoidHom.mem_ker.mp (htop ▸ trivial))))
  obtain ⟨θ, hθ⟩ := hex
  exact homMaxAgreement_mono_codomain θ hθ

/-- For a finite simple group `G` with `|G| > 2`, `Λ_{G, G}` equals the largest density of the
fixed-point set of a nontrivial automorphism of `G`. -/
theorem isSimpleGroup_homMaxAgreement_self_eq_max_aut_fixed (G : Type*) [Group G] [Fintype G]
    [IsSimpleGroup G] (hG2 : 2 < Fintype.card G) :
    homMaxAgreement G G =
      sSup {r : ℝ | ∃ σ : MulAut G, σ ≠ 1 ∧ density {x : G | σ x = x} = r} := by
  have hG1 : 1 < Fintype.card G := by omega
  let S : Set ℝ := {r : ℝ | ∃ σ : MulAut G, σ ≠ 1 ∧ density {x : G | σ x = x} = r}
  have hSne : S.Nonempty := by
    by_cases hab : ∀ a b : G, a * b = b * a
    · -- Abelian simple group of prime order `p > 2`: inversion `x ↦ x⁻¹` is a nontrivial aut.
      let invAut : MulAut G :=
        { toFun := fun x => x⁻¹
          invFun := fun x => x⁻¹
          left_inv := inv_inv
          right_inv := inv_inv
          map_mul' := fun a b => by rw [mul_inv_rev, hab] }
      have hinv_ne : invAut ≠ 1 := by
        intro h1
        have hsq : ∀ x : G, x * x = 1 := fun x => by
          have hx : x⁻¹ = x := DFunLike.congr_fun h1 x
          simpa [hx] using mul_inv_cancel x
        have hord2 : ∃ x : G, x ≠ 1 := exists_ne 1
        obtain ⟨x, hx⟩ := hord2
        let K : Subgroup G := Subgroup.zpowers x
        have : K.Normal := ⟨fun a ha g => by
          rw [hab g a, mul_inv_cancel_right]; exact ha⟩
        have hKtop : K = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_left
          (fun hbot => hx (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers x)))
        have hcardK : Fintype.card G ≤ 2 := by
          have hsub : (Set.univ : Set G) ⊆ ({1, x} : Set G) := by
            intro y _
            have hy : y ∈ K := by rw [hKtop]; trivial
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            have heven : ∀ m : ℕ, x ^ m = 1 ∨ x ^ m = x := by
              intro m
              induction m with
              | zero => left; simp
              | succ m ih =>
                rcases ih with h | h
                · right; simp [pow_succ, h]
                · left; simp [pow_succ, h, hsq x]
            rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
            · simpa using heven m
            · rw [zpow_neg, zpow_natCast]
              rcases heven m with h | h
              · left; simp [h]
              · right; rw [h]; exact Set.mem_singleton_iff.mpr (mul_eq_one_iff_inv_eq.mp (hsq x))
          have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
          exact hle.trans (by
            simpa using (Set.ncard_insert_le (1 : G) {x}).trans (by simp [Set.ncard_singleton]))
        omega
      exact ⟨_, invAut, hinv_ne, rfl⟩
    · push Not at hab
      obtain ⟨a, b, hab⟩ := hab
      refine ⟨_, MulAut.conj a, ?_, rfl⟩
      intro h1
      have hconj := DFunLike.congr_fun h1 b
      simp only [MulAut.conj_apply, MulAut.one_apply] at hconj
      exact hab (by have h := congrArg (· * a) hconj; simpa [mul_assoc] using h)
  have hSfin : S.Finite := by
    have hsub : S ⊆ (fun k : ℕ => (k : ℝ) / (Fintype.card G : ℝ)) ''
        (Set.Iic (Fintype.card G)) := by
      rintro r ⟨σ, -, rfl⟩
      exact ⟨{x : G | σ x = x}.ncard,
        (Set.ncard_le_ncard (Set.subset_univ _)).trans_eq (by simp [Set.ncard_univ]), rfl⟩
    exact ((Set.finite_Iic (Fintype.card G)).image _).subset hsub
  rw [← codeMaxAgreement_homCode_eq]
  refine le_antisymm ?_ ?_
  · refine csSup_le (Set.insert_nonempty 0 _) ?_
    rintro r (rfl | ⟨_, ⟨φ, rfl⟩, _, ⟨ψ, rfl⟩, hne, rfl⟩)
    · obtain ⟨r₀, hr₀⟩ := hSne
      have hr0_nn : 0 ≤ r₀ := by
        obtain ⟨σ, -, rfl⟩ := hr₀
        exact density_nonneg _
      exact hr0_nn.trans (le_csSup hSfin.bddAbove hr₀)
    · have haut : ∀ θ : G →* G, θ ≠ 1 → Function.Bijective θ := by
        intro θ hθ
        have hinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp <|
          (IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker).resolve_right
            (fun htop => hθ (by ext x; exact MonoidHom.mem_ker.mp (htop ▸ trivial)))
        exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
      by_cases hφ : φ = 1
      · have hψ : ψ ≠ 1 := fun h => hne (by rw [hφ, h])
        have hEq : equalizer (φ : G → G) ψ = {1} := by
          ext x
          simp only [mem_equalizer_iff, hφ, MonoidHom.one_apply, Set.mem_singleton_iff]
          exact ⟨fun h => (haut ψ hψ).1 (by rw [← h, map_one]), fun h => by rw [h, map_one]⟩
        obtain ⟨r₀, hr₀⟩ := hSne
        obtain ⟨σ, hσ, rfl⟩ := hr₀
        have h1mem : (1 : G) ∈ {x : G | σ x = x} := map_one σ
        have hle : density ({1} : Set G) ≤ density {x : G | σ x = x} :=
          density_mono (Set.singleton_subset_iff.mpr h1mem)
        exact (by rw [agreement, hEq]; exact hle : agreement (φ : G → G) ψ ≤ _).trans
          (le_csSup hSfin.bddAbove ⟨σ, hσ, rfl⟩)
      · by_cases hψ : ψ = 1
        · have hEq : equalizer (φ : G → G) ψ = {1} := by
            ext x
            simp only [mem_equalizer_iff, hψ, MonoidHom.one_apply, Set.mem_singleton_iff]
            exact ⟨fun h => (haut φ hφ).1 (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
          obtain ⟨r₀, hr₀⟩ := hSne
          obtain ⟨σ, hσ, rfl⟩ := hr₀
          have hle : density ({1} : Set G) ≤ density {x : G | σ x = x} :=
            density_mono (Set.singleton_subset_iff.mpr (map_one σ))
          exact (by rw [agreement, hEq]; exact hle : agreement (φ : G → G) ψ ≤ _).trans
            (le_csSup hSfin.bddAbove ⟨σ, hσ, rfl⟩)
        · let eφ : MulAut G := MulEquiv.ofBijective φ (haut φ hφ)
          let eψ : MulAut G := MulEquiv.ofBijective ψ (haut ψ hψ)
          let σ : MulAut G := eψ.trans eφ.symm
          have hσ : σ ≠ 1 := by
            intro h1
            apply hne
            funext x
            have hx : eφ.symm (eψ x) = x := DFunLike.congr_fun h1 x
            have := congrArg eφ hx
            simpa [eφ, eψ] using this.symm
          have hEq : equalizer (φ : G → G) ψ = {x : G | σ x = x} := by
            ext x
            simp only [mem_equalizer_iff, Set.mem_ofPred_eq, σ, MulEquiv.trans_apply]
            constructor
            · intro hx
              change eφ.symm (ψ x) = x
              rw [← hx]
              exact eφ.symm_apply_apply x
            · intro hx
              have := congrArg eφ hx
              simpa [eφ, eψ] using this.symm
          exact le_csSup hSfin.bddAbove ⟨σ, hσ, by rw [agreement, hEq]⟩
  · refine csSup_le hSne ?_
    rintro r ⟨σ, hσ, rfl⟩
    have hne : (σ.toMonoidHom : G → G) ≠ (MonoidHom.id G : G → G) := by
      intro hEq
      exact hσ (MulEquiv.ext fun x => congrFun hEq x)
    exact agreement_le_codeMaxAgreement ⟨σ.toMonoidHom, rfl⟩ ⟨MonoidHom.id G, rfl⟩ hne

end Irrelevant

end CslibFrontier.HomomorphismCode
