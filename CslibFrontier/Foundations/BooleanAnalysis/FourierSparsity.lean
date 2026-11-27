/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fourier Sparsity and Subcube Restrictions of Boolean Functions

For a Boolean function `f : (ι → Bool) → Bool` over a finite coordinate index type `ι`, viewing
outputs in `{0, 1} ⊆ ℝ` via `Cslib.BitString.bitVal ℝ` yields the `{0, 1}`-valued Walsh–Fourier
expansion `bitVal ℝ (f x) = ∑ S, boolFourierCoeff f S * chi ℝ S x`. The total Fourier sparsity
`fourierSparsity f` counts all subsets `S` with nonzero `{0, 1}`-Fourier coefficient, while
`nonemptyFourierSparsity f` counts nonempty subsets `S` with nonzero coefficient and
`signFourierSparsity f` counts nonzero coefficients in the `±1` encoding `signVal ∘ f`.

When `f` becomes constant on a subcube fixing `S : Finset ι` to `ρ : S → Bool`, grouping the
Fourier support of `f` into buckets indexed by `T ⊆ {i : ι // i ∉ S}` shows that every active
nonempty bucket has cardinality at least `2`. Consequently, for every assignment `ρ' : S → Bool`
to the same coordinate set `S`, the restricted function `subcubeRestrict f S ρ'` satisfies
`2 * nonemptyFourierSparsity (subcubeRestrict f S ρ') ≤ nonemptyFourierSparsity f`.

## Main definitions

* `Cslib.BitString.boolFourierCoeff`: `{0, 1}`-valued Walsh–Fourier coefficient of `f`.
* `Cslib.BitString.fourierSupport`, `Cslib.BitString.nonemptyFourierSupport`: full and
  nonempty-frequency `{0, 1}`-Fourier supports of `f`.
* `Cslib.BitString.fourierSparsity`, `Cslib.BitString.nonemptyFourierSparsity`,
  `Cslib.BitString.signFourierSparsity`: total `{0, 1}`, nonempty-frequency `{0, 1}`, and `±1`
  Fourier sparsities.
* `Cslib.BitString.subcubeRestrict`: restriction of `f` to the free coordinates outside
  `S : Finset ι` under an assignment `ρ : S → Bool`.
* `Cslib.BitString.fourierBucket`: bucket of Fourier support sets having prescribed trace outside
  `S`.

## Main results

* `Cslib.BitString.boolFourier_inversion`, `Cslib.BitString.boolFourierCoeff_eq_of_sum_eq`,
  `Cslib.BitString.eq_of_boolFourierCoeff_eq`: expansion and uniqueness.
* `Cslib.BitString.nonemptyFourierSparsity_eq_zero_iff_isConst`: nonempty-frequency Fourier
  sparsity vanishes if and only if `f` is constant.
* `Cslib.BitString.fourierSparsity_parityOn`, `Cslib.BitString.nonemptyFourierSparsity_parityOn`,
  `Cslib.BitString.signFourierSparsity_parityOn`: exact sparsities of parity functions.
* `Cslib.BitString.boolFourierCoeff_subcubeRestrict`: bucket expansion of restricted Fourier
  coefficients.
* `Cslib.BitString.two_mul_nonemptyFourierSparsity_subcubeRestrict_le`: sparsity-halving inequality
  under subcube restriction when a sibling subcube makes `f` constant.
-/

public section

open scoped BigOperators
open Cslib

namespace Cslib.BitString

section Sparsity

variable {ι : Type*} [Fintype ι]

/-- The `{0, 1}`-valued Walsh–Fourier coefficient `f̂(S) = 𝔼 x, bitVal ℝ (f x) * χ_S(x)` of a
Boolean function `f : (ι → Bool) → Bool`. -/
noncomputable def boolFourierCoeff (f : (ι → Bool) → Bool) (S : Finset ι) : ℝ := by
  classical
  exact fourierCoeff (fun x ↦ bitVal ℝ (f x)) S

/-- `{0, 1}`-valued Walsh–Fourier inversion formula
`bitVal ℝ (f x) = ∑ S, boolFourierCoeff f S * chi ℝ S x`. -/
theorem boolFourier_inversion (f : (ι → Bool) → Bool) (x : ι → Bool) :
    bitVal ℝ (f x) = ∑ S : Finset ι, boolFourierCoeff f S * chi ℝ S x := by
  classical
  exact (sum_fourierCoeff_mul_chi (fun y ↦ bitVal ℝ (f y)) x).symm

/-- Uniqueness of `{0, 1}`-valued Walsh–Fourier coefficients: any character expansion of
`bitVal ℝ ∘ f` coincides with `boolFourierCoeff f`. -/
theorem boolFourierCoeff_eq_of_sum_eq {f : (ι → Bool) → Bool} {coeff : Finset ι → ℝ}
    (h : ∀ x : ι → Bool, bitVal ℝ (f x) = ∑ S : Finset ι, coeff S * chi ℝ S x)
    (S : Finset ι) : boolFourierCoeff f S = coeff S := by
  classical
  have hfun : (fun x ↦ bitVal ℝ (f x)) = fun x ↦ ∑ T : Finset ι, coeff T * chi ℝ T x :=
    funext h
  change fourierCoeff (fun x ↦ bitVal ℝ (f x)) S = coeff S
  rw [hfun, fourierCoeff_sum_mul_chi]

private lemma bitVal_real_injective {a b : Bool} (h : bitVal ℝ a = bitVal ℝ b) : a = b := by
  cases a <;> cases b <;> simp [bitVal_false, bitVal_true] at h <;> rfl

/-- Two Boolean functions with identical `{0, 1}`-valued Walsh–Fourier coefficients are equal. -/
theorem eq_of_boolFourierCoeff_eq {f g : (ι → Bool) → Bool}
    (h : ∀ S : Finset ι, boolFourierCoeff f S = boolFourierCoeff g S) : f = g := by
  funext x
  apply bitVal_real_injective
  rw [boolFourier_inversion f x, boolFourier_inversion g x]
  exact Finset.sum_congr rfl fun S _ ↦ by rw [h S]

private lemma boolFourierCoeff_eq_fourierCoeff [DecidableEq ι] (f : (ι → Bool) → Bool)
    (S : Finset ι) :
    boolFourierCoeff f S = fourierCoeff (fun x ↦ bitVal ℝ (f x)) S := by
  unfold boolFourierCoeff
  exact congrFun (congrFun (congrArg (fun d ↦ @fourierCoeff ι _ d)
    (Subsingleton.elim _ _)) _) S

/-- Relationship between `{0, 1}`-valued and `±1`-valued Fourier coefficients on nonempty sets `S`:
`boolFourierCoeff f S = -fourierCoeff (signVal ∘ f) S / 2`. -/
theorem boolFourierCoeff_eq_neg_signVal_div_two [DecidableEq ι] (f : (ι → Bool) → Bool)
    {S : Finset ι} (hS : S.Nonempty) :
    boolFourierCoeff f S = -fourierCoeff (fun x ↦ signVal (f x)) S / 2 := by
  have hfun : (fun x : ι → Bool ↦ signVal (f x)) = fun x ↦ (1 : ℝ) - 2 * bitVal ℝ (f x) :=
    funext fun x ↦ signVal_eq_one_sub_two_mul_bitVal (f x)
  have h1 : fourierCoeff (fun x ↦ signVal (f x)) S =
      (if S = ∅ then (1 : ℝ) else 0) - 2 * fourierCoeff (fun x ↦ bitVal ℝ (f x)) S := by
    rw [hfun, fourierCoeff_sub, fourierCoeff_const, fourierCoeff_const_mul]
  rw [ite_eq_right hS.ne_empty] at h1
  rw [boolFourierCoeff_eq_fourierCoeff]
  linarith

/-- The `{0, 1}`-Fourier support `{S ⊆ ι | boolFourierCoeff f S ≠ 0}` of `f`. -/
noncomputable def fourierSupport (f : (ι → Bool) → Bool) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun S ↦ boolFourierCoeff f S ≠ 0

/-- Membership in `fourierSupport f` characterizes nonzero `{0, 1}`-Fourier coefficients. -/
theorem mem_fourierSupport_iff {f : (ι → Bool) → Bool} {S : Finset ι} :
    S ∈ fourierSupport f ↔ boolFourierCoeff f S ≠ 0 := by
  classical
  unfold fourierSupport
  simp

/-- The nonempty-frequency `{0, 1}`-Fourier support `{S ⊆ ι | S.Nonempty ∧ f̂(S) ≠ 0}` of `f`. -/
noncomputable def nonemptyFourierSupport (f : (ι → Bool) → Bool) : Finset (Finset ι) :=
  (fourierSupport f).filter fun S ↦ S.Nonempty

/-- Membership in `nonemptyFourierSupport f` characterizes nonempty sets with `f̂(S) ≠ 0`. -/
theorem mem_nonemptyFourierSupport_iff {f : (ι → Bool) → Bool} {S : Finset ι} :
    S ∈ nonemptyFourierSupport f ↔ boolFourierCoeff f S ≠ 0 ∧ S.Nonempty := by
  simp [nonemptyFourierSupport, mem_fourierSupport_iff]

/-- Total `{0, 1}`-valued Fourier sparsity `spar(f) = |{S ⊆ ι | f̂(S) ≠ 0}|`. -/
noncomputable def fourierSparsity (f : (ι → Bool) → Bool) : ℕ :=
  (fourierSupport f).card

/-- Nonempty-frequency `{0, 1}`-valued Fourier sparsity
`spar̃(f) = |{S ⊆ ι | S ≠ ∅ ∧ f̂(S) ≠ 0}|`. -/
noncomputable def nonemptyFourierSparsity (f : (ι → Bool) → Bool) : ℕ :=
  (nonemptyFourierSupport f).card

/-- Cardinality of `fourierSupport f` equals `fourierSparsity f`. -/
theorem card_fourierSupport (f : (ι → Bool) → Bool) :
    (fourierSupport f).card = fourierSparsity f := by rfl

/-- Cardinality of `nonemptyFourierSupport f` equals `nonemptyFourierSparsity f`. -/
theorem card_nonemptyFourierSupport (f : (ι → Bool) → Bool) :
    (nonemptyFourierSupport f).card = nonemptyFourierSparsity f := by rfl

/-- `±1`-encoding Fourier sparsity `spar̂(f) = |{S ⊆ ι | fourierCoeff (signVal ∘ f) S ≠ 0}|`. -/
noncomputable def signFourierSparsity (f : (ι → Bool) → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset ι ↦ fourierCoeff (fun x ↦ signVal (f x)) S ≠ 0).card

/-- Nonempty-frequency Fourier sparsity is at most total Fourier sparsity. -/
theorem nonemptyFourierSparsity_le_fourierSparsity (f : (ι → Bool) → Bool) :
    nonemptyFourierSparsity f ≤ fourierSparsity f :=
  Finset.card_filter_le _ _

/-- Total Fourier sparsity exceeds nonempty-frequency Fourier sparsity by at most `1`. -/
theorem fourierSparsity_le_nonemptyFourierSparsity_add_one (f : (ι → Bool) → Bool) :
    fourierSparsity f ≤ nonemptyFourierSparsity f + 1 := by
  classical
  refine (Finset.card_le_card (t := insert ∅ (nonemptyFourierSupport f)) fun S hS ↦ ?_).trans
    (Finset.card_insert_le ∅ _)
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (mem_nonemptyFourierSupport_iff.mpr ⟨mem_fourierSupport_iff.mp hS, hne⟩)

/-- Nonempty-frequency `{0, 1}`-Fourier sparsity is at most `±1`-encoding Fourier sparsity. -/
theorem nonemptyFourierSparsity_le_signFourierSparsity (f : (ι → Bool) → Bool) :
    nonemptyFourierSparsity f ≤ signFourierSparsity f := by
  classical
  unfold nonemptyFourierSparsity signFourierSparsity
  refine Finset.card_le_card fun S hS ↦ ?_
  obtain ⟨hne0, hSne⟩ := mem_nonemptyFourierSupport_iff.mp hS
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ S, fun hsign0 ↦ hne0 ?_⟩
  rw [boolFourierCoeff_eq_neg_signVal_div_two f hSne, hsign0]
  ring

/-- Nonempty-frequency Fourier sparsity vanishes if and only if `f` is a constant function. -/
theorem nonemptyFourierSparsity_eq_zero_iff_isConst (f : (ι → Bool) → Bool) :
    nonemptyFourierSparsity f = 0 ↔ Function.IsConst f := by
  rw [nonemptyFourierSparsity, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_nonemptyFourierSupport_iff, not_and]
  refine ⟨fun hzero x y ↦ ?_, fun hconst S hne hS ↦ ?_⟩
  · have hval : ∀ z : ι → Bool, bitVal ℝ (f z) = boolFourierCoeff f ∅ := fun z ↦ by
      rw [boolFourier_inversion f z, Finset.sum_eq_single ∅]
      · simp
      · intro S _ hS0
        have hc : boolFourierCoeff f S = 0 :=
          by_contra fun hne ↦ hzero S hne (Finset.nonempty_iff_ne_empty.mpr hS0)
        rw [hc, zero_mul]
      · intro hm
        exact absurd (Finset.mem_univ ∅) hm
    exact bitVal_real_injective ((hval x).trans (hval y).symm)
  · classical
    have hfun : (fun x : ι → Bool ↦ bitVal ℝ (f x)) = fun _ ↦ bitVal ℝ (f (fun _ ↦ false)) :=
      funext fun x ↦ congrArg (bitVal ℝ) (hconst x _)
    have hc0 : boolFourierCoeff f S = 0 := by
      change fourierCoeff (fun x ↦ bitVal ℝ (f x)) S = 0
      rw [hfun, fourierCoeff_const, ite_eq_right hS.ne_empty]
    exact hne hc0

/-- Every nonconstant Boolean function has nonempty-frequency Fourier sparsity at least `1`. -/
theorem one_le_nonemptyFourierSparsity_of_not_isConst {f : (ι → Bool) → Bool}
    (hf : ¬ Function.IsConst f) : 1 ≤ nonemptyFourierSparsity f :=
  Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hf ((nonemptyFourierSparsity_eq_zero_iff_isConst f).mp h0)

/-- Any Boolean function attaining `true` has total `{0, 1}`-Fourier sparsity at least `1`. -/
theorem one_le_fourierSparsity_of_exists_true {f : (ι → Bool) → Bool}
    (hx : ∃ x, f x = true) : 1 ≤ fourierSparsity f := by
  obtain ⟨x, hx⟩ := hx
  rw [fourierSparsity, Finset.one_le_card]
  by_contra! hemp
  have hinv := boolFourier_inversion f x
  have hsum : (∑ S : Finset ι, boolFourierCoeff f S * chi ℝ S x) = 0 :=
    Finset.sum_eq_zero fun S _ ↦ by
      have hc : boolFourierCoeff f S = 0 :=
        by_contra fun hne ↦ Finset.notMem_empty S (hemp ▸ mem_fourierSupport_iff.mpr hne)
      rw [hc, zero_mul]
  rw [hx, bitVal_true, hsum] at hinv
  norm_num at hinv

/-- Every Boolean function has `±1`-encoding Fourier sparsity at least `1`. -/
theorem one_le_signFourierSparsity (f : (ι → Bool) → Bool) : 1 ≤ signFourierSparsity f := by
  classical
  unfold signFourierSparsity
  rw [Finset.one_le_card]
  by_contra! hemp
  have hp := sum_fourierCoeff_sq_signVal f
  have hsum : (∑ S : Finset ι, fourierCoeff (fun x ↦ signVal (f x)) S ^ 2) = 0 :=
    Finset.sum_eq_zero fun S _ ↦ by
      have hc : fourierCoeff (fun x ↦ signVal (f x)) S = 0 :=
        by_contra fun hne ↦
          Finset.notMem_empty S (hemp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ S, hne⟩)
      rw [hc, sq, zero_mul]
  linarith

/-- The identically `false` Boolean function has `{0, 1}`-Fourier sparsity `0`. -/
@[simp] theorem fourierSparsity_const_false :
    fourierSparsity (fun _ : ι → Bool ↦ false) = 0 := by
  rw [fourierSparsity, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro S
  rw [mem_fourierSupport_iff, not_not]
  classical
  change fourierCoeff (fun _ : ι → Bool ↦ bitVal ℝ false) S = 0
  simp [bitVal_false, fourierCoeff_const]

/-- The identically `true` Boolean function has `{0, 1}`-Fourier sparsity `1`. -/
@[simp] theorem fourierSparsity_const_true :
    fourierSparsity (fun _ : ι → Bool ↦ true) = 1 := by
  have hsupp : fourierSupport (fun _ : ι → Bool ↦ true) = {∅} := by
    ext S
    rw [mem_fourierSupport_iff, Finset.mem_singleton]
    classical
    change fourierCoeff (fun _ : ι → Bool ↦ bitVal ℝ true) S ≠ 0 ↔ S = ∅
    rw [bitVal_true, fourierCoeff_const]
    by_cases hS : S = ∅ <;> simp [hS]
  rw [fourierSparsity, hsupp, Finset.card_singleton]

/-- Every constant Boolean function has nonempty-frequency Fourier sparsity `0`. -/
@[simp] theorem nonemptyFourierSparsity_const (b : Bool) :
    nonemptyFourierSparsity (fun _ : ι → Bool ↦ b) = 0 :=
  (nonemptyFourierSparsity_eq_zero_iff_isConst _).mpr fun _ _ ↦ rfl

private lemma boolFourierCoeff_parityOn [DecidableEq ι] (s : Finset ι) (S : Finset ι) :
    boolFourierCoeff (parityOn s) S =
      (if S = ∅ then (1 / 2 : ℝ) else 0) - (if S = s then (1 / 2 : ℝ) else 0) := by
  have hfun : (fun x : ι → Bool ↦ bitVal ℝ (parityOn s x)) =
      fun x ↦ (1 / 2 : ℝ) - (1 / 2 : ℝ) * signVal (parityOn s x) := funext fun x ↦ by
    have h1 := signVal_eq_one_sub_two_mul_bitVal (parityOn s x)
    linarith
  rw [boolFourierCoeff_eq_fourierCoeff, hfun, fourierCoeff_sub, fourierCoeff_const,
    fourierCoeff_const_mul, fourierCoeff_signVal_parityOn]
  split_ifs <;> ring

/-- For any nonempty coordinate subset `s`, `parityOn s` has `{0, 1}`-Fourier sparsity `2`
(supported on `{∅, s}`). -/
theorem fourierSparsity_parityOn {s : Finset ι} (hs : s.Nonempty) :
    fourierSparsity (parityOn s) = 2 := by
  classical
  have hs0 : s ≠ ∅ := hs.ne_empty
  have hsupp : fourierSupport (parityOn s) = {∅, s} := by
    ext S
    rw [mem_fourierSupport_iff, Finset.mem_insert, Finset.mem_singleton, boolFourierCoeff_parityOn]
    by_cases hS0 : S = ∅
    · subst hS0
      rw [ite_eq_left rfl, ite_eq_right hs0.symm]
      norm_num
    · by_cases hSs : S = s
      · subst hSs
        rw [ite_eq_right hs0, ite_eq_left rfl]
        norm_num
      · rw [ite_eq_right hS0, ite_eq_right hSs]
        norm_num [hS0, hSs]
  rw [fourierSparsity, hsupp, Finset.card_pair hs0.symm]

/-- For any nonempty coordinate subset `s`, `parityOn s` has nonempty-frequency `{0, 1}`-Fourier
sparsity `1`. -/
theorem nonemptyFourierSparsity_parityOn {s : Finset ι} (hs : s.Nonempty) :
    nonemptyFourierSparsity (parityOn s) = 1 := by
  classical
  have hs0 : s ≠ ∅ := hs.ne_empty
  have hsupp : nonemptyFourierSupport (parityOn s) = {s} := by
    ext S
    rw [mem_nonemptyFourierSupport_iff, Finset.mem_singleton, boolFourierCoeff_parityOn]
    by_cases hSs : S = s
    · subst hSs
      rw [ite_eq_right hs0, ite_eq_left rfl]
      norm_num
      exact hs
    · by_cases hS0 : S = ∅
      · subst hS0
        exact ⟨fun h ↦ (Finset.not_nonempty_empty h.2).elim, fun h ↦ (hs0 h.symm).elim⟩
      · rw [ite_eq_right hS0, ite_eq_right hSs]
        norm_num [hSs]
  rw [nonemptyFourierSparsity, hsupp, Finset.card_singleton]

/-- For any coordinate subset `s`, `parityOn s` has `±1`-encoding Fourier sparsity `1`. -/
@[simp] theorem signFourierSparsity_parityOn (s : Finset ι) :
    signFourierSparsity (parityOn s) = 1 := by
  classical
  unfold signFourierSparsity
  have hsupp : (Finset.univ.filter
      fun S : Finset ι ↦ fourierCoeff (fun x ↦ signVal (parityOn s x)) S ≠ 0) = {s} := by
    ext S
    rw [Finset.mem_filter, Finset.mem_singleton, fourierCoeff_signVal_parityOn]
    by_cases hSs : S = s <;> simp [hSs]
  rw [hsupp, Finset.card_singleton]

end Sparsity

section EquivInvariance

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Reindexing coordinates along `e : ι₁ ≃ ι₂` transports `{0, 1}`-Fourier coefficients via
`Finset.map e.toEmbedding`. -/
theorem boolFourierCoeff_comp_equiv (e : ι₁ ≃ ι₂) (f : (ι₁ → Bool) → Bool) (S : Finset ι₁) :
    boolFourierCoeff (fun y : ι₂ → Bool ↦ f (fun i ↦ y (e i))) (S.map e.toEmbedding) =
      boolFourierCoeff f S := by
  classical
  change fourierCoeff (fun y : ι₂ → Bool ↦ bitVal ℝ (f (fun i ↦ y (e.symm.symm i))))
    (S.map e.toEmbedding) = fourierCoeff (fun x ↦ bitVal ℝ (f x)) S
  rw [fourierCoeff_comp_arrowCongr e.symm (fun x ↦ bitVal ℝ (f x)) (S.map e.toEmbedding)]
  congr 1
  ext i
  simp

private lemma fourierSupport_comp_equiv (e : ι₁ ≃ ι₂) (f : (ι₁ → Bool) → Bool) :
    fourierSupport (fun y : ι₂ → Bool ↦ f (fun i ↦ y (e i))) =
      (fourierSupport f).map (Finset.mapEmbedding e.toEmbedding).toEmbedding := by
  ext T
  simp only [mem_fourierSupport_iff, Finset.mem_map, RelEmbedding.coe_toEmbedding]
  refine ⟨fun hT ↦ ?_, fun ⟨S, hS, hST⟩ ↦ ?_⟩
  · have hmap_eq : (T.map e.symm.toEmbedding).map e.toEmbedding = T := by
      ext j
      simp
    refine ⟨T.map e.symm.toEmbedding, ?_, hmap_eq⟩
    have heq := boolFourierCoeff_comp_equiv e f (T.map e.symm.toEmbedding)
    rw [hmap_eq] at heq
    exact heq ▸ hT
  · subst hST
    change boolFourierCoeff _ (S.map e.toEmbedding) ≠ 0
    rwa [boolFourierCoeff_comp_equiv]

/-- Total `{0, 1}`-Fourier sparsity is invariant under coordinate equivalences. -/
theorem fourierSparsity_comp_equiv (e : ι₁ ≃ ι₂) (f : (ι₁ → Bool) → Bool) :
    fourierSparsity (fun y : ι₂ → Bool ↦ f (fun i ↦ y (e i))) = fourierSparsity f := by
  rw [fourierSparsity, fourierSupport_comp_equiv e f, Finset.card_map, ← fourierSparsity]

/-- Nonempty-frequency `{0, 1}`-Fourier sparsity is invariant under coordinate equivalences. -/
theorem nonemptyFourierSparsity_comp_equiv (e : ι₁ ≃ ι₂) (f : (ι₁ → Bool) → Bool) :
    nonemptyFourierSparsity (fun y : ι₂ → Bool ↦ f (fun i ↦ y (e i))) =
      nonemptyFourierSparsity f := by
  have hmap : nonemptyFourierSupport (fun y : ι₂ → Bool ↦ f (fun i ↦ y (e i))) =
      (nonemptyFourierSupport f).map (Finset.mapEmbedding e.toEmbedding).toEmbedding := by
    ext T
    simp only [nonemptyFourierSupport, Finset.mem_filter, fourierSupport_comp_equiv e f,
      Finset.mem_map, RelEmbedding.coe_toEmbedding]
    refine ⟨fun ⟨⟨S, hS, hST⟩, hne⟩ ↦ ⟨S, ⟨hS, ?_⟩, hST⟩,
      fun ⟨S, ⟨hS, hne⟩, hST⟩ ↦ ⟨⟨S, hS, hST⟩, hST ▸ hne.map⟩⟩
    rcases hST ▸ hne with ⟨j, hj⟩
    rcases Finset.mem_map.mp hj with ⟨i, hi, _⟩
    exact ⟨i, hi⟩
  rw [nonemptyFourierSparsity, hmap, Finset.card_map, ← nonemptyFourierSparsity]

end EquivInvariance

section SubcubeRestriction

/-- Restriction `f|(S, ρ)` of `f : (ι → Bool) → α` to the free coordinates `{i : ι // i ∉ S}`
obtained by fixing coordinates in `S : Finset ι` according to `ρ : S → Bool`. -/
def subcubeRestrict {ι α : Type*} [DecidableEq ι] (f : (ι → Bool) → α) (S : Finset ι)
    (ρ : S → Bool) (y : {i : ι // i ∉ S} → Bool) : α :=
  f fun i ↦ if h : i ∈ S then ρ ⟨i, h⟩ else y ⟨i, h⟩

/-- Evaluating `subcubeRestrict f S` on coordinate restrictions of `a` and `y` recovers
`f (S.piecewise a y)`. -/
theorem subcubeRestrict_eq_piecewise {ι α : Type*} [DecidableEq ι] (f : (ι → Bool) → α)
    (S : Finset ι) (a y : ι → Bool) :
    subcubeRestrict f S (fun i : S ↦ a i.1) (fun j : {i : ι // i ∉ S} ↦ y j.1) =
      f (S.piecewise a y) := by
  unfold subcubeRestrict
  rfl

/-- If `x : ι → Bool` agrees with `ρ` on `S` and with `y` outside `S`, then
`subcubeRestrict f S ρ y = f x`. -/
theorem subcubeRestrict_congr_arg {ι α : Type*} [DecidableEq ι] (f : (ι → Bool) → α)
    (S : Finset ι) (ρ : S → Bool) (y : {i : ι // i ∉ S} → Bool) {x : ι → Bool}
    (hS : ∀ i : S, x i.1 = ρ i) (hnot : ∀ j : {i : ι // i ∉ S}, x j.1 = y j) :
    subcubeRestrict f S ρ y = f x := by
  unfold subcubeRestrict
  congr 1
  ext i
  by_cases hi : i ∈ S
  · rw [dite_eq_left hi, hS ⟨i, hi⟩]
  · rw [dite_eq_right hi, hnot ⟨i, hi⟩]

section BucketCalculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Fourier-support bucket `B_T = {W ⊆ ι | W ∩ Sᶜ = T ∧ f̂(W) ≠ 0}` associated to a subset
`T` of the free coordinates `{i : ι // i ∉ S}`. -/
noncomputable def fourierBucket (f : (ι → Bool) → Bool) (S : Finset ι)
    (T : Finset {i : ι // i ∉ S}) : Finset (Finset ι) :=
  (fourierSupport f).filter fun W ↦ Finset.univ.filter (fun j : {i : ι // i ∉ S} ↦ j.1 ∈ W) = T

/-- Membership in `fourierBucket f S T`. -/
theorem mem_fourierBucket_iff {f : (ι → Bool) → Bool} {S : Finset ι}
    {T : Finset {i : ι // i ∉ S}} {W : Finset ι} :
    W ∈ fourierBucket f S T ↔
      boolFourierCoeff f W ≠ 0 ∧
        Finset.univ.filter (fun j : {i : ι // i ∉ S} ↦ j.1 ∈ W) = T := by
  simp [fourierBucket, mem_fourierSupport_iff]

private def splitFinsetEquiv (S : Finset ι) :
    (Finset {i : ι // i ∉ S} × Finset S) ≃ Finset ι where
  toFun p := p.1.map (Function.Embedding.subtype _) ∪ p.2.map (Function.Embedding.subtype _)
  invFun W := (Finset.univ.filter (fun j : {i : ι // i ∉ S} ↦ j.1 ∈ W),
    Finset.univ.filter (fun j : S ↦ j.1 ∈ W))
  left_inv := fun ⟨T, R⟩ ↦ by
    ext j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_map, Function.Embedding.coe_subtype]
    · exact ⟨fun h ↦ h.elim (fun ⟨k, hk, hkj⟩ ↦ Subtype.ext hkj ▸ hk)
        (fun ⟨k, _, hkj⟩ ↦ (j.2 (hkj ▸ k.2)).elim), fun hj ↦ Or.inl ⟨j, hj, rfl⟩⟩
    · exact ⟨fun h ↦ h.elim (fun ⟨k, _, hkj⟩ ↦ (k.2 (hkj.symm ▸ j.2)).elim)
        (fun ⟨k, hk, hkj⟩ ↦ Subtype.ext hkj ▸ hk), fun hj ↦ Or.inr ⟨j, hj, rfl⟩⟩
  right_inv W := by
    ext i
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.Embedding.coe_subtype]
    by_cases hi : i ∈ S
    · exact ⟨fun h ↦ h.elim (fun ⟨k, _, hki⟩ ↦ (k.2 (hki.symm ▸ hi)).elim)
        (fun ⟨k, hk, hki⟩ ↦ hki ▸ hk), fun hiW ↦ Or.inr ⟨⟨i, hi⟩, hiW, rfl⟩⟩
    · exact ⟨fun h ↦ h.elim (fun ⟨k, hk, hki⟩ ↦ hki ▸ hk)
        (fun ⟨k, _, hki⟩ ↦ (hi (hki ▸ k.2)).elim), fun hiW ↦ Or.inl ⟨⟨i, hi⟩, hiW, rfl⟩⟩

private lemma chi_split_subcube (S : Finset ι) (ρ' : S → Bool)
    (T : Finset {i : ι // i ∉ S}) (R : Finset S) (y : {i : ι // i ∉ S} → Bool) :
    chi ℝ (splitFinsetEquiv S (T, R)) (fun i ↦ if h : i ∈ S then ρ' ⟨i, h⟩ else y ⟨i, h⟩) =
      chi ℝ R ρ' * chi ℝ T y := by
  have hdisj : Disjoint (T.map (Function.Embedding.subtype _))
      (R.map (Function.Embedding.subtype _)) := Finset.disjoint_left.mpr fun _ hiT hiR ↦ by
    rcases Finset.mem_map.mp hiT with ⟨j, _, rfl⟩
    rcases Finset.mem_map.mp hiR with ⟨k, _, hkj⟩
    change k.1 = j.1 at hkj
    exact j.2 (hkj ▸ k.2)
  change chi ℝ (T.map (Function.Embedding.subtype _) ∪ R.map (Function.Embedding.subtype _)) _ = _
  rw [chi_union hdisj, mul_comm]
  refine congr_arg₂ (· * ·) ?_ ?_
  · simp only [chi, Finset.prod_map, Function.Embedding.coe_subtype]
    exact Finset.prod_congr rfl fun k _ ↦ by simp [k.2]
  · simp only [chi, Finset.prod_map, Function.Embedding.coe_subtype]
    exact Finset.prod_congr rfl fun j _ ↦ by simp [j.2]

/-- Subset-sum expansion of `boolFourierCoeff (subcubeRestrict f S ρ') T` over `R ⊆ S`. -/
theorem boolFourierCoeff_subcubeRestrict_eq_sum_subsets (f : (ι → Bool) → Bool) (S : Finset ι)
    (ρ' : S → Bool) (T : Finset {i : ι // i ∉ S}) :
    boolFourierCoeff (subcubeRestrict f S ρ') T =
      ∑ R : Finset S, boolFourierCoeff f
        (T.map (Function.Embedding.subtype _) ∪ R.map (Function.Embedding.subtype _)) *
        chi ℝ R ρ' := by
  refine boolFourierCoeff_eq_of_sum_eq (f := subcubeRestrict f S ρ')
    (coeff := fun T' ↦ ∑ R : Finset S, boolFourierCoeff f
      (T'.map (Function.Embedding.subtype _) ∪ R.map (Function.Embedding.subtype _)) *
      chi ℝ R ρ') (fun y ↦ ?_) T
  rw [subcubeRestrict, boolFourier_inversion f]
  have hbij := Fintype.sum_equiv (splitFinsetEquiv S)
    (fun p : Finset {i : ι // i ∉ S} × Finset S ↦ boolFourierCoeff f (splitFinsetEquiv S p) *
      chi ℝ (splitFinsetEquiv S p) (fun i ↦ if h : i ∈ S then ρ' ⟨i, h⟩ else y ⟨i, h⟩))
    (fun W : Finset ι ↦ boolFourierCoeff f W *
      chi ℝ W (fun i ↦ if h : i ∈ S then ρ' ⟨i, h⟩ else y ⟨i, h⟩)) (fun _ ↦ rfl)
  rw [← hbij, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun T' _ ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun R _ ↦ by
    rw [chi_split_subcube, ← mul_assoc]
    rfl

/-- Bucket expansion of the `{0, 1}`-Fourier coefficient of `subcubeRestrict f S ρ'`. -/
theorem boolFourierCoeff_subcubeRestrict (f : (ι → Bool) → Bool) (S : Finset ι)
    (ρ' : S → Bool) (T : Finset {i : ι // i ∉ S}) :
    boolFourierCoeff (subcubeRestrict f S ρ') T =
      ∑ W ∈ fourierBucket f S T,
        boolFourierCoeff f W * chi ℝ (Finset.univ.filter (fun j : S ↦ j.1 ∈ W)) ρ' := by
  rw [boolFourierCoeff_subcubeRestrict_eq_sum_subsets]
  let g : Finset S → Finset ι :=
    fun R ↦ T.map (Function.Embedding.subtype _) ∪ R.map (Function.Embedding.subtype _)
  have hg_inj : Function.Injective g := fun R₁ R₂ h ↦ by
    have heq := ((splitFinsetEquiv S).left_inv (T, R₁)).symm.trans
      ((congr_arg ((splitFinsetEquiv S).symm) h).trans ((splitFinsetEquiv S).left_inv (T, R₂)))
    exact (Prod.mk.inj heq).2
  let emb : Finset S ↪ Finset ι := ⟨g, hg_inj⟩
  have hsub : fourierBucket f S T ⊆ Finset.univ.map emb := fun W hW ↦ by
    obtain ⟨_, hWT⟩ := mem_fourierBucket_iff.mp hW
    refine Finset.mem_map.mpr ⟨Finset.univ.filter (fun j : S ↦ j.1 ∈ W), Finset.mem_univ _, ?_⟩
    have hpair : (splitFinsetEquiv S).symm W =
        (T, Finset.univ.filter (fun j : S ↦ j.1 ∈ W)) := Prod.ext hWT rfl
    exact (congr_arg (splitFinsetEquiv S) hpair.symm).trans
      ((splitFinsetEquiv S).apply_symm_apply W)
  have hmap_sum : (∑ R : Finset S, boolFourierCoeff f (g R) * chi ℝ R ρ') =
      ∑ W ∈ Finset.univ.map emb,
        boolFourierCoeff f W * chi ℝ (Finset.univ.filter (fun j : S ↦ j.1 ∈ W)) ρ' := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun R _ ↦
      congr_arg (fun U ↦ boolFourierCoeff f (g R) * chi ℝ U ρ')
        (congr_arg Prod.snd ((splitFinsetEquiv S).left_inv (T, R))).symm
  change (∑ R : Finset S, boolFourierCoeff f (g R) * chi ℝ R ρ') = _
  rw [hmap_sum]
  symm
  refine Finset.sum_subset hsub fun W hWmap hWnot ↦ ?_
  rcases Finset.mem_map.mp hWmap with ⟨R, _, rfl⟩
  have hWT := congr_arg Prod.fst ((splitFinsetEquiv S).left_inv (T, R))
  have hc : boolFourierCoeff f (emb R) = 0 :=
    by_contra fun hne ↦ hWnot (mem_fourierBucket_iff.mpr ⟨hne, hWT⟩)
  rw [hc, zero_mul]

private lemma two_le_card_fourierBucket_of_isConst {f : (ι → Bool) → Bool} {S : Finset ι}
    {ρ : S → Bool} (hconst : Function.IsConst (subcubeRestrict f S ρ))
    {T : Finset {i : ι // i ∉ S}} (hT : T.Nonempty) (hne : (fourierBucket f S T).Nonempty) :
    2 ≤ (fourierBucket f S T).card := by
  have hzero : boolFourierCoeff (subcubeRestrict f S ρ) T = 0 := by
    by_contra hne0
    have hmem : T ∈ nonemptyFourierSupport (subcubeRestrict f S ρ) :=
      mem_nonemptyFourierSupport_iff.mpr ⟨hne0, hT⟩
    have h0 := (nonemptyFourierSparsity_eq_zero_iff_isConst (subcubeRestrict f S ρ)).mpr hconst
    rw [nonemptyFourierSparsity, Finset.card_eq_zero] at h0
    exact Finset.notMem_empty T (h0 ▸ hmem)
  rw [boolFourierCoeff_subcubeRestrict] at hzero
  by_contra! hlt
  obtain ⟨W, hW_eq⟩ :=
    Finset.card_eq_one.mp (le_antisymm (Nat.lt_succ_iff.mp hlt) (Finset.one_le_card.mpr hne))
  have hW_mem : W ∈ fourierBucket f S T := hW_eq ▸ Finset.mem_singleton_self W
  rw [hW_eq, Finset.sum_singleton, mul_eq_zero] at hzero
  rcases hzero with hf0 | hchar0
  · exact (mem_fourierBucket_iff.mp hW_mem).1 hf0
  · have habs := abs_chi (Finset.univ.filter (fun j : S ↦ j.1 ∈ W)) ρ
    rw [hchar0, abs_zero] at habs
    norm_num at habs

/-- **Sparsity halving under subcube restriction**: if `subcubeRestrict f S ρ` is constant for some
`ρ : S → Bool`, then
`2 * nonemptyFourierSparsity (subcubeRestrict f S ρ') ≤ nonemptyFourierSparsity f`
for every `ρ' : S → Bool`. -/
theorem two_mul_nonemptyFourierSparsity_subcubeRestrict_le (f : (ι → Bool) → Bool) (S : Finset ι)
    (ρ ρ' : S → Bool) (hconst : Function.IsConst (subcubeRestrict f S ρ)) :
    2 * nonemptyFourierSparsity (subcubeRestrict f S ρ') ≤ nonemptyFourierSparsity f := by
  classical
  let active := (Finset.univ : Finset (Finset {i : ι // i ∉ S})).filter
    fun T ↦ T.Nonempty ∧ (fourierBucket f S T).Nonempty
  have hsub_supp : nonemptyFourierSupport (subcubeRestrict f S ρ') ⊆ active := fun T hT ↦ by
    obtain ⟨hne0, hTne⟩ := mem_nonemptyFourierSupport_iff.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ T, hTne, ?_⟩
    by_contra! hemp
    rw [boolFourierCoeff_subcubeRestrict, hemp, Finset.sum_empty] at hne0
    exact hne0 rfl
  have hbiUnion_sub : active.biUnion (fourierBucket f S) ⊆ nonemptyFourierSupport f := fun W hW ↦ by
    rcases Finset.mem_biUnion.mp hW with ⟨T, hTact, hWT⟩
    obtain ⟨hfW, hfilt⟩ := mem_fourierBucket_iff.mp hWT
    obtain ⟨j, hjT⟩ := (Finset.mem_filter.mp hTact).2.1
    rw [← hfilt, Finset.mem_filter] at hjT
    exact mem_nonemptyFourierSupport_iff.mpr ⟨hfW, ⟨j.1, hjT.2⟩⟩
  have hdisj : (active : Set (Finset {i : ι // i ∉ S})).PairwiseDisjoint (fourierBucket f S) :=
    fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun _ hW₁ hW₂ ↦
      hne ((mem_fourierBucket_iff.mp hW₁).2.symm.trans (mem_fourierBucket_iff.mp hW₂).2)
  calc
    2 * nonemptyFourierSparsity (subcubeRestrict f S ρ')
        ≤ 2 * active.card := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub_supp)
    _ = ∑ _T ∈ active, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ T ∈ active, (fourierBucket f S T).card := Finset.sum_le_sum fun T hT ↦
        two_le_card_fourierBucket_of_isConst hconst
          (Finset.mem_filter.mp hT).2.1 (Finset.mem_filter.mp hT).2.2
    _ = (active.biUnion (fourierBucket f S)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ nonemptyFourierSparsity f := Finset.card_le_card hbiUnion_sub

end BucketCalculus

end SubcubeRestriction

end Cslib.BitString
