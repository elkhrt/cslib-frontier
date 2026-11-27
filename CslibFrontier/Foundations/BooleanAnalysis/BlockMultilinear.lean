/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Quadratic Block-Multilinear Decoupling and Unitary Block-Encoding

This module establishes two textbook linear-algebraic ingredients for quantum query and
communication protocols evaluating degree-`2` polynomials under standard Lean axioms:

1. **Degree-`2` block-multilinear decoupling**
: every normalized degree-`≤ 2` polynomial `p : (ι → Bool) → ℝ` (`|p x| ≤ 1`) lifts to a
   symmetric bilinear form `A : Matrix (Option ι) (Option ι) ℝ` on `Option ι` reproducing `p x`
   along the diagonal `(1, signVal (x ·))` and bounded by `3` on all `±1` sign vectors.
2. **Spectral norm control and unitary block-encoding dilation**: any real matrix `A` whose `±1`
   bilinear form is bounded by `B` has complex Euclidean operator norm at most `B`, and any complex
   matrix `M : Matrix κ κ ℂ` bounded in operator norm by `c > 0` dilates to a unitary matrix
   `U ∈ Matrix.unitaryGroup (κ ⊕ κ) ℂ` whose upper-left `κ × κ` block is `c⁻¹ • M`.

## Main definitions

* `CslibFrontier.BooleanAnalysis.liftSignVec`: lifted `±1` vector `(1, signVal (x ·))` on
  `Option ι`.
* `CslibFrontier.BooleanAnalysis.decouplingMatrix`: canonical symmetric bilinear matrix associated
  to a polynomial `p : (ι → Bool) → ℝ`.

## Main results

* `CslibFrontier.BooleanAnalysis.dotProduct_decouplingMatrix_liftSignVec`: diagonal evaluation
  identity `liftSignVec x ⬝ᵥ decouplingMatrix p *ᵥ liftSignVec x = p x` for `p ∈ lowDegree ℝ ι 2`.
* `CslibFrontier.BooleanAnalysis.abs_dotProduct_decouplingMatrix_le_three`: uniform `±1` bilinear
  bound `≤ 3` when `|p x| ≤ 1` everywhere.
* `CslibFrontier.BooleanAnalysis.exists_bilinear_decoupling_le_three`: combined degree-`2`
  decoupling existence theorem.
* `CslibFrontier.BooleanAnalysis.norm_toEuclideanLin_complex_le_of_bilinear_bound`: operator norm
  bound `‖A_{ℂ} v‖₂ ≤ B ‖v‖₂` from `|uᵀ A w| ≤ B` on `±1` vectors.
* `CslibFrontier.BooleanAnalysis.exists_unitary_blockEncoding`: Halmos unitary dilation of a complex
  contraction `c⁻¹ • M` into `Matrix.unitaryGroup (κ ⊕ κ) ℂ`.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Finset Matrix Cslib.BitString
open scoped BigOperators MatrixOrder ComplexOrder

section Decoupling

/-- Lifts a Boolean input `x : ι → Bool` to the `(1 + |ι|)`-dimensional `±1` real vector on
`Option ι` sending `none ↦ 1` and `some i ↦ signVal (x i)`. -/
def liftSignVec {ι : Type*} (x : ι → Bool) : Option ι → ℝ
  | none => 1
  | some i => signVal (x i)

@[simp]
theorem liftSignVec_none {ι : Type*} (x : ι → Bool) : liftSignVec x none = 1 := by
  rfl

@[simp]
theorem liftSignVec_some {ι : Type*} (x : ι → Bool) (i : ι) :
    liftSignVec x (some i) = signVal (x i) := by
  rfl

/-- The Euclidean `ℓ₂` norm squared of `liftSignVec x` is `Fintype.card ι + 1`. -/
theorem sum_sq_liftSignVec {ι : Type*} [Fintype ι] (x : ι → Bool) :
    ∑ k : Option ι, liftSignVec x k ^ 2 = (Fintype.card ι : ℝ) + 1 := by
  rw [Fintype.sum_option, liftSignVec_none, one_pow]
  have hsum : ∑ i : ι, liftSignVec x (some i) ^ 2 = (Fintype.card ι : ℝ) := by
    simp only [liftSignVec_some, sq, signVal_mul_self, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetric `(Option ι) × (Option ι)` decoupling matrix of `p : (ι → Bool) → ℝ`, placing
`p̂(∅)` at `(none, none)`, `p̂({i}) / 2` on the borders, and `p̂({i, j}) / 2` off the diagonal on
`some × some`. -/
noncomputable def decouplingMatrix (p : (ι → Bool) → ℝ) : Matrix (Option ι) (Option ι) ℝ
  | none, none => fourierCoeff p ∅
  | none, some j => fourierCoeff p {j} / 2
  | some i, none => fourierCoeff p {i} / 2
  | some i, some j => if i = j then 0 else fourierCoeff p {i, j} / 2

/-- `decouplingMatrix p` is symmetric. -/
theorem transpose_decouplingMatrix (p : (ι → Bool) → ℝ) :
    (decouplingMatrix p)ᵀ = decouplingMatrix p := by
  ext a b
  cases a with
  | none => cases b <;> rfl
  | some i =>
    cases b with
    | none => rfl
    | some j =>
      simp only [transpose_apply, decouplingMatrix]
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji, Finset.pair_comm]

private theorem sum_ordered_pairs_eq_two_mul_card_two (g : Finset ι → ℝ) :
    (∑ i : ι, ∑ j : ι, if i = j then 0 else g {i, j}) =
      2 * ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2), g S := by
  have hfiber :
      (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2),
        ∑ p ∈ (Finset.univ : Finset (ι × ι)).filter
          (fun p ↦ p.1 ≠ p.2 ∧ ({p.1, p.2} : Finset ι) = S), g S) =
      ∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p ↦ p.1 ≠ p.2), g {p.1, p.2} := by
    have hinner :
        (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2),
          ∑ p ∈ (Finset.univ : Finset (ι × ι)).filter
            (fun p ↦ p.1 ≠ p.2 ∧ ({p.1, p.2} : Finset ι) = S), g S) =
        (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2),
          ∑ p ∈ (Finset.univ : Finset (ι × ι)).filter
            (fun p ↦ p.1 ≠ p.2 ∧ ({p.1, p.2} : Finset ι) = S), g {p.1, p.2}) :=
      Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun p hp ↦ by
        rw [(Finset.mem_filter.mp hp).2.2]
    rw [hinner, ← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun p _ ↦ rfl
      ext ⟨i, j⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨S, _, hij, _⟩ ↦ hij,
        fun hij ↦ ⟨{i, j}, Finset.card_pair hij, hij, rfl⟩⟩
    · intro S₁ _ S₂ _ hne
      exact Finset.disjoint_left.mpr fun p hp₁ hp₂ ↦
        hne ((Finset.mem_filter.mp hp₁).2.2.symm.trans (Finset.mem_filter.mp hp₂).2.2)
  have htwo (S : Finset ι) (hS : S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2)) :
      #((Finset.univ : Finset (ι × ι)).filter
        (fun p ↦ p.1 ≠ p.2 ∧ ({p.1, p.2} : Finset ι) = S)) = 2 := by
    rw [Finset.mem_filter] at hS
    obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hS.2
    subst hSab
    have hset : (Finset.univ : Finset (ι × ι)).filter
        (fun p ↦ p.1 ≠ p.2 ∧ ({p.1, p.2} : Finset ι) = {a, b}) = {(a, b), (b, a)} := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨huv, heq⟩
        have hu : u = a ∨ u = b := by
          simpa using (heq ▸ Finset.mem_insert_self u {v} : u ∈ ({a, b} : Finset ι))
        have hv : v = a ∨ v = b := by
          simpa using (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v) :
            v ∈ ({a, b} : Finset ι))
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact False.elim (huv rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (huv rfl)
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hab, rfl⟩
        · exact ⟨hab.symm, Finset.pair_comm _ _⟩
    rw [hset, Finset.card_pair (fun h ↦ hab (Prod.mk.inj h).1)]
  have hlhs_prod :
      (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p ↦ p.1 ≠ p.2), g {p.1, p.2}) =
        ∑ i : ι, ∑ j : ι, if i = j then 0 else g {i, j} := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hij : i = j <;> simp [hij]
  rw [← hlhs_prod, ← hfiber, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  rw [Finset.sum_const, htwo S hS, nsmul_eq_mul, Nat.cast_ofNat]

/-- Evaluating the bilinear form of `decouplingMatrix p` at `(liftSignVec x, liftSignVec x)`
recovers `p x` whenever `p ∈ lowDegree ℝ ι 2`. -/
theorem dotProduct_decouplingMatrix_liftSignVec {p : (ι → Bool) → ℝ}
    (hp : p ∈ lowDegree ℝ ι 2) (x : ι → Bool) :
    liftSignVec x ⬝ᵥ decouplingMatrix p *ᵥ liftSignVec x = p x := by
  rw [dotProduct, Fintype.sum_option]
  simp only [mulVec, dotProduct, Fintype.sum_option, liftSignVec_none, liftSignVec_some,
    decouplingMatrix, one_mul, mul_one]
  have hquad :
      (∑ i : ι, signVal (x i) *
        (fourierCoeff p {i} / 2 +
          ∑ j : ι, (if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (x j))) =
        (∑ i : ι, fourierCoeff p {i} * signVal (x i)) / 2 +
          ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2),
            fourierCoeff p S * chi ℝ S x := by
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    · have hrew :
          (∑ i : ι, ∑ j : ι, signVal (x i) *
            ((if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (x j))) =
          (∑ i : ι, ∑ j : ι, if i = j then 0 else
            (fourierCoeff p {i, j} * chi ℝ {i, j} x) / 2) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hij : i = j
        · simp [hij]
        · simp only [hij, ↓reduceIte, chi_eq_prod_signVal, Finset.prod_pair hij]
          ring
      rw [hrew, sum_ordered_pairs_eq_two_mul_card_two
        (fun S ↦ (fourierCoeff p S * chi ℝ S x) / 2), Finset.mul_sum]
      exact Finset.sum_congr rfl fun S _ ↦ by ring
  rw [hquad]
  have hlin_half : (∑ j : ι, fourierCoeff p {j} / 2 * signVal (x j)) =
      (∑ j : ι, fourierCoeff p {j} * signVal (x j)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlin_half]
  have hsum2 : p x = fourierCoeff p ∅ + (∑ i : ι, fourierCoeff p {i} * signVal (x i)) +
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2),
        fourierCoeff p S * chi ℝ S x := by
    rw [← sum_fourierCoeff_mul_chi p x]
    have hle2 : (∑ S : Finset ι, fourierCoeff p S * chi ℝ S x) =
        ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 2),
          fourierCoeff p S * chi ℝ S x := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun S _ hS ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hS
      rw [fourierCoeff_eq_zero_of_mem_lowDegree hp hS, zero_mul]
    rw [hle2]
    have hpart : (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 2) =
        ((Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 1)) ∪
          ((Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2)) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdisj : Disjoint
        ((Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 1))
        ((Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S = 2)) :=
      Finset.disjoint_left.mpr fun S h1 h2 ↦ by
        simp only [Finset.mem_filter] at h1 h2
        omega
    rw [hpart, Finset.sum_union hdisj]
    congr 1
    have hcard1 : (Finset.univ : Finset (Finset ι)).filter (fun S ↦ #S ≤ 1) =
        insert (∅ : Finset ι) (Finset.univ.image (fun i : ι ↦ ({i} : Finset ι))) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_image]
      constructor
      · intro hS
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with h0 | h1
        · exact Or.inl (Finset.card_eq_zero.mp h0)
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
          exact Or.inr ⟨i, rfl⟩
      · rintro (rfl | ⟨i, rfl⟩) <;> simp
    rw [hcard1, Finset.sum_insert (by simp), chi_empty, mul_one,
      Finset.sum_image (fun i _ j _ hij ↦ Finset.singleton_injective hij)]
    exact congrArg (fourierCoeff p ∅ + ·) (Finset.sum_congr rfl fun i _ ↦ by rw [chi_singleton])
  linarith

private noncomputable def patchAvg (p : (ι → Bool) → ℝ) (S : Finset ι) (u : ι → Bool) : ℝ :=
  𝔼 z : ι → Bool, p (fun i ↦ if i ∈ S then u i else z i)

private theorem abs_patchAvg_le_one {p : (ι → Bool) → ℝ} (hnorm : ∀ x, |p x| ≤ 1)
    (S : Finset ι) (u : ι → Bool) : |patchAvg p S u| ≤ 1 := by
  dsimp only [patchAvg]
  exact (Finset.abs_expect_le _ _).trans
    (Finset.expect_le Finset.univ_nonempty fun z _ ↦ hnorm _)

private theorem expect_chi_patch (S T : Finset ι) (u : ι → Bool) :
    (𝔼 z : ι → Bool, chi ℝ T (fun i ↦ if i ∈ S then u i else z i)) =
      if T ⊆ S then chi ℝ T u else 0 := by
  have hsplit (z : ι → Bool) :
      chi ℝ T (fun i ↦ if i ∈ S then u i else z i) =
        chi ℝ (T ∩ S) u * chi ℝ (T \ S) z := by
    have hunion : T = (T ∩ S) ∪ (T \ S) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      by_cases hi : i ∈ S <;> simp [hi]
    have hdisj : Disjoint (T ∩ S) (T \ S) :=
      Finset.disjoint_left.mpr fun i h1 h2 ↦
        (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
    conv_lhs => rw [hunion]
    rw [chi_union hdisj]
    congr 1
    · simp only [chi_eq_prod_signVal]
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      simp [(Finset.mem_inter.mp hi).2]
    · simp only [chi_eq_prod_signVal]
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      simp [(Finset.mem_sdiff.mp hi).2]
  simp_rw [hsplit]
  rw [← Finset.mul_expect, expect_chi]
  by_cases hTS : T ⊆ S
  · have hsdiff : T \ S = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hTS
    simp [hTS, hsdiff]
  · have hsdiff : T \ S ≠ ∅ := fun h ↦ hTS (Finset.sdiff_eq_empty_iff_subset.mp h)
    simp [hTS, hsdiff]

private theorem patchAvg_eq {p : (ι → Bool) → ℝ} (hp : p ∈ lowDegree ℝ ι 2)
    (S : Finset ι) (u : ι → Bool) :
    patchAvg p S u = fourierCoeff p ∅ + (∑ i ∈ S, fourierCoeff p {i} * signVal (u i)) +
      ∑ i ∈ S, ∑ j ∈ S,
        if i = j then 0 else (fourierCoeff p {i, j} / 2) * signVal (u i) * signVal (u j) := by
  dsimp only [patchAvg]
  have hexp : (𝔼 z : ι → Bool, p (fun i ↦ if i ∈ S then u i else z i)) =
      ∑ T : Finset ι, fourierCoeff p T * (if T ⊆ S then chi ℝ T u else 0) := by
    conv_lhs =>
      arg 2
      ext z
      rw [← sum_fourierCoeff_mul_chi p (fun i ↦ if i ∈ S then u i else z i)]
    rw [Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun T _ ↦ ?_
    rw [← Finset.mul_expect, expect_chi_patch]
  rw [hexp]
  have hle2 : (∑ T : Finset ι, fourierCoeff p T * (if T ⊆ S then chi ℝ T u else 0)) =
      ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T ≤ 2 ∧ T ⊆ S),
        fourierCoeff p T * chi ℝ T u := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_subset (fun T hT ↦ ?_) (fun T hT hnot ↦ ?_)
    · simp only [Finset.mem_filter] at hT ⊢
      exact ⟨hT.1, hT.2.2⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hnot
      have hgt : 2 < #T := not_le.mp fun hle ↦ hnot ⟨hle, hT⟩
      rw [fourierCoeff_eq_zero_of_mem_lowDegree hp hgt, zero_mul]
  rw [hle2]
  have hpart : (Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T ≤ 2 ∧ T ⊆ S) =
      insert (∅ : Finset ι)
        ((S.image fun i ↦ ({i} : Finset ι)) ∪
          ((Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2 ∧ T ⊆ S))) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hcard, hsub⟩
      rcases Nat.le_succ_iff.mp hcard with hle1 | h2
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
        · exact Or.inl (Finset.card_eq_zero.mp h0)
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
          exact Or.inr (Or.inl ⟨i, hsub (Finset.mem_singleton_self i), rfl⟩)
      · exact Or.inr (Or.inr ⟨h2, hsub⟩)
    · rintro (rfl | ⟨i, hi, rfl⟩ | ⟨h2, hsub⟩)
      · simp
      · exact ⟨by simp, Finset.singleton_subset_iff.mpr hi⟩
      · exact ⟨h2.le, hsub⟩
  have hnot_empty : (∅ : Finset ι) ∉
      (S.image fun i ↦ ({i} : Finset ι)) ∪
        ((Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2 ∧ T ⊆ S)) := by
    simp
  have hdisj : Disjoint (S.image fun i ↦ ({i} : Finset ι))
      ((Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2 ∧ T ⊆ S)) :=
    Finset.disjoint_left.mpr fun T h1 h2 ↦ by
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      simp only [Finset.mem_filter] at h2
      have := h2.2.1
      simp at this
  rw [hpart, Finset.sum_insert hnot_empty, Finset.sum_union hdisj, chi_empty, mul_one,
    Finset.sum_image (fun i _ j _ hij ↦ Finset.singleton_injective hij), ← add_assoc]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rw [chi_singleton]
  · have hall2 :
        (∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2 ∧ T ⊆ S),
          fourierCoeff p T * chi ℝ T u) =
        ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2),
          if T ⊆ S then fourierCoeff p T * chi ℝ T u else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext T
      simp
    rw [hall2]
    have hpairs := sum_ordered_pairs_eq_two_mul_card_two
      (fun T ↦ if T ⊆ S then (fourierCoeff p T * chi ℝ T u) / 2 else 0)
    have hrhs_eq :
        (2 * ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2),
          if T ⊆ S then (fourierCoeff p T * chi ℝ T u) / 2 else 0) =
        ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T ↦ #T = 2),
          if T ⊆ S then fourierCoeff p T * chi ℝ T u else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      split_ifs <;> ring
    rw [← hrhs_eq, ← hpairs]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · refine Finset.sum_congr rfl fun j hj ↦ ?_
        by_cases hij : i = j
        · simp [hij]
        · have hsub : ({i, j} : Finset ι) ⊆ S :=
            Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩
          simp only [hij, ↓reduceIte, hsub, chi_eq_prod_signVal, Finset.prod_pair hij]
          ring
      · intro j _ hjS
        by_cases hij : i = j
        · simp [hij]
        · have hnot : ¬ ({i, j} : Finset ι) ⊆ S := fun h ↦
            hjS (h (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))
          simp [hij, hnot]
    · intro i _ hiS
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases hij : i = j
      · simp [hij]
      · have hnot : ¬ ({i, j} : Finset ι) ⊆ S := fun h ↦
          hiS (h (Finset.mem_insert_self i {j}))
        simp [hij, hnot]

/-- **Aaronson–Ambainis–Iraids–Kokainis–Smotrovs bilinear bound**: for any normalized polynomial
`p ∈ lowDegree ℝ ι 2` (`∀ x, |p x| ≤ 1`), the bilinear form of `decouplingMatrix p` is bounded in
magnitude by `3` on all `±1` vectors `(x, y) : (Option ι → Bool)²`. -/
theorem abs_dotProduct_decouplingMatrix_le_three {p : (ι → Bool) → ℝ}
    (hp : p ∈ lowDegree ℝ ι 2) (hnorm : ∀ x, |p x| ≤ 1)
    (x y : Option ι → Bool) :
    |(fun k ↦ signVal (x k)) ⬝ᵥ decouplingMatrix p *ᵥ (fun k ↦ signVal (y k))| ≤ 3 := by
  let u : ι → Bool := fun i ↦ x (some i)
  let u_not : ι → Bool := fun i ↦ !u i
  let v : ι → Bool := fun i ↦ y (some i)
  let S : Finset ι := Finset.univ.filter fun i ↦ u i = v i
  have hSc : Sᶜ = Finset.univ.filter fun i ↦ u i ≠ v i := by
    ext i
    simp [S]
  have hv_on_S {i : ι} (hi : i ∈ S) : signVal (v i) = signVal (u i) := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hi]
  have hv_on_Sc {i : ι} (hi : i ∈ Sᶜ) : signVal (v i) = -signVal (u i) := by
    rw [hSc, Finset.mem_filter] at hi
    have hne := hi.2
    cases hu : u i <;> cases hv : v i <;> simp_all
  let L (T : Finset ι) : ℝ := ∑ i ∈ T, fourierCoeff p {i} * signVal (u i)
  let Q (T : Finset ι) : ℝ :=
    ∑ i ∈ T, ∑ j ∈ T,
      if i = j then 0 else (fourierCoeff p {i, j} / 2) * signVal (u i) * signVal (u j)
  have hpatch_pos (T : Finset ι) : patchAvg p T u = fourierCoeff p ∅ + L T + Q T :=
    patchAvg_eq hp T u
  have hpatch_neg (T : Finset ι) : patchAvg p T u_not = fourierCoeff p ∅ - L T + Q T := by
    rw [patchAvg_eq hp T u_not]
    have hL : (∑ i ∈ T, fourierCoeff p {i} * signVal (u_not i)) = -L T := by
      simp only [u_not, signVal_not, mul_neg, Finset.sum_neg_distrib, L]
    have hQ : (∑ i ∈ T, ∑ j ∈ T,
        if i = j then 0 else (fourierCoeff p {i, j} / 2) * signVal (u_not i) * signVal (u_not j)) =
          Q T :=
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
        simp only [u_not, signVal_not]
        split_ifs <;> ring
    rw [hL, hQ]
    ring
  have hpatch_empty : patchAvg p ∅ u = fourierCoeff p ∅ := by
    rw [hpatch_pos ∅]
    simp [L, Q]
  have hbilin :
      (fun k ↦ signVal (x k)) ⬝ᵥ decouplingMatrix p *ᵥ (fun k ↦ signVal (y k)) =
        fourierCoeff p ∅ * signVal (x none) * signVal (y none) +
          (signVal (x none) * (L S - L Sᶜ) + signVal (y none) * (L S + L Sᶜ)) / 2 +
          (Q S - Q Sᶜ) := by
    rw [dotProduct, Fintype.sum_option]
    simp only [mulVec, dotProduct, Fintype.sum_option, decouplingMatrix]
    have hlin_u : (∑ i : ι, signVal (u i) * (fourierCoeff p {i} / 2 * signVal (y none))) =
        signVal (y none) * (L S + L Sᶜ) / 2 := by
      have hsplitL : (∑ i : ι, fourierCoeff p {i} * signVal (u i)) = L S + L Sᶜ :=
        (Finset.sum_add_sum_compl S (fun i ↦ fourierCoeff p {i} * signVal (u i))).symm
      calc
        (∑ i : ι, signVal (u i) * (fourierCoeff p {i} / 2 * signVal (y none)))
            = signVal (y none) * (∑ i : ι, fourierCoeff p {i} * signVal (u i)) / 2 := by
                rw [Finset.mul_sum, Finset.sum_div]
                exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = signVal (y none) * (L S + L Sᶜ) / 2 := by rw [hsplitL]
    have hlin_v : (∑ j : ι, fourierCoeff p {j} / 2 * signVal (v j)) = (L S - L Sᶜ) / 2 := by
      have hsplitV : (∑ j : ι, fourierCoeff p {j} * signVal (v j)) = L S - L Sᶜ := by
        rw [← Finset.sum_add_sum_compl S (fun j ↦ fourierCoeff p {j} * signVal (v j))]
        have h1 : ∑ j ∈ S, fourierCoeff p {j} * signVal (v j) = L S :=
          Finset.sum_congr rfl fun j hj ↦ by rw [hv_on_S hj]
        have h2 : ∑ j ∈ Sᶜ, fourierCoeff p {j} * signVal (v j) = -L Sᶜ := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j hj ↦ by rw [hv_on_Sc hj]; ring
        rw [h1, h2]
        ring
      rw [← hsplitV, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hquad_uv :
        (∑ i : ι, signVal (u i) *
          ∑ j : ι, (if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (v j)) =
        Q S - Q Sᶜ := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_sum_compl S]
      have hrowS :
          (∑ i ∈ S, ∑ j : ι, signVal (u i) *
            ((if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (v j))) =
          Q S + ∑ i ∈ S, ∑ j ∈ Sᶜ,
            -(fourierCoeff p {i, j} / 2 * signVal (u i) * signVal (u j)) := by
        have hinner (i : ι) (hi : i ∈ S) :
            (∑ j : ι, signVal (u i) *
              ((if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (v j))) =
            (∑ j ∈ S, if i = j then 0 else
              (fourierCoeff p {i, j} / 2) * signVal (u i) * signVal (u j)) +
            (∑ j ∈ Sᶜ, -(fourierCoeff p {i, j} / 2 * signVal (u i) * signVal (u j))) := by
          rw [← Finset.sum_add_sum_compl S]
          congr 1
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            rw [hv_on_S hj]
            split_ifs <;> ring
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            have hij : i ≠ j := fun h ↦ Finset.mem_compl.mp hj (h ▸ hi)
            rw [hv_on_Sc hj]
            simp only [hij, ↓reduceIte]
            ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
      have hrowSc :
          (∑ i ∈ Sᶜ, ∑ j : ι, signVal (u i) *
            ((if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (v j))) =
          (∑ i ∈ Sᶜ, ∑ j ∈ S,
            (fourierCoeff p {i, j} / 2 * signVal (u i) * signVal (u j))) - Q Sᶜ := by
        have hinner (i : ι) (hi : i ∈ Sᶜ) :
            (∑ j : ι, signVal (u i) *
              ((if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (v j))) =
            (∑ j ∈ S, (fourierCoeff p {i, j} / 2 * signVal (u i) * signVal (u j))) -
            (∑ j ∈ Sᶜ, if i = j then 0 else
              (fourierCoeff p {i, j} / 2) * signVal (u i) * signVal (u j)) := by
          rw [← Finset.sum_add_sum_compl S, sub_eq_add_neg, ← Finset.sum_neg_distrib]
          congr 1
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            have hij : i ≠ j := fun h ↦ Finset.mem_compl.mp hi (h ▸ hj)
            rw [hv_on_S hj]
            simp only [hij, ↓reduceIte]
            ring
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            rw [hv_on_Sc hj]
            split_ifs <;> ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
      rw [hrowS, hrowSc]
      have hcancel :
          (∑ i ∈ S, ∑ j ∈ Sᶜ,
            -(fourierCoeff p {i, j} / 2 * signVal (u i) * signVal (u j))) +
          (∑ i ∈ Sᶜ, ∑ j ∈ S,
            (fourierCoeff p {i, j} / 2 * signVal (u i) * signVal (u j))) = 0 := by
        simp only [Finset.sum_neg_distrib, neg_add_eq_zero]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by
          rw [Finset.pair_comm]
          ring
      linarith
    have hsplit_sum :
        (∑ i : ι, signVal (x (some i)) *
          (fourierCoeff p {i} / 2 * signVal (y none) +
            ∑ j : ι, (if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (y (some j)))) =
        signVal (y none) * (L S + L Sᶜ) / 2 + (Q S - Q Sᶜ) := by
      calc
        (∑ i : ι, signVal (x (some i)) *
            (fourierCoeff p {i} / 2 * signVal (y none) +
              ∑ j : ι, (if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (y (some j))))
            = (∑ i : ι, signVal (u i) * (fourierCoeff p {i} / 2 * signVal (y none))) +
                (∑ i : ι, signVal (u i) *
                  ∑ j : ι, (if i = j then 0 else fourierCoeff p {i, j} / 2) * signVal (v j)) := by
                  rw [← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun i _ ↦ mul_add _ _ _
        _ = signVal (y none) * (L S + L Sᶜ) / 2 + (Q S - Q Sᶜ) := by
              rw [hlin_u, hquad_uv]
    dsimp only [v] at hlin_v
    rw [hsplit_sum, hlin_v]
    ring
  rw [hbilin]
  have hb1 := abs_patchAvg_le_one hnorm S u
  have hb2 := abs_patchAvg_le_one hnorm S u_not
  have hb3 := abs_patchAvg_le_one hnorm Sᶜ u
  have hb4 := abs_patchAvg_le_one hnorm Sᶜ u_not
  have hb0 := abs_patchAvg_le_one hnorm ∅ u
  rw [hpatch_pos S] at hb1
  rw [hpatch_neg S] at hb2
  rw [hpatch_pos Sᶜ] at hb3
  rw [hpatch_neg Sᶜ] at hb4
  rw [hpatch_empty] at hb0
  rw [abs_le] at hb1 hb2 hb3 hb4 hb0 ⊢
  cases hx0 : x none <;> cases hy0 : y none <;>
    simp only [signVal_false, signVal_true] <;> constructor <;> linarith

omit [DecidableEq ι] in
/-- **Degree-`2` block-multilinear decoupling theorem**: every
normalized degree-`≤ 2` real polynomial `p` on `ι → Bool` (`|p x| ≤ 1`) is realized along the
diagonal `(liftSignVec x, liftSignVec x)` by a real matrix `A : Matrix (Option ι) (Option ι) ℝ`
whose bilinear form on all `±1` vectors has magnitude at most `3`.
-/
theorem exists_bilinear_decoupling_le_three {p : (ι → Bool) → ℝ}
    (hp : p ∈ lowDegree ℝ ι 2) (hnorm : ∀ x, |p x| ≤ 1) :
    ∃ A : Matrix (Option ι) (Option ι) ℝ,
      (∀ x : ι → Bool, liftSignVec x ⬝ᵥ A *ᵥ liftSignVec x = p x) ∧
      (∀ x y : Option ι → Bool,
        |(fun k ↦ signVal (x k)) ⬝ᵥ A *ᵥ (fun k ↦ signVal (y k))| ≤ 3) := by
  classical
  exact ⟨decouplingMatrix p, dotProduct_decouplingMatrix_liftSignVec hp,
    abs_dotProduct_decouplingMatrix_le_three hp hnorm⟩

end Decoupling

section OperatorNormAndBlockEncoding

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- If a real matrix `A : Matrix κ κ ℝ` has `|uᵀ A w| ≤ B` on all `±1` vectors `u, w`, then its
real Euclidean operator norm `‖A.toEuclideanLin v‖` is at most `B * ‖v‖`. -/
theorem norm_toEuclideanLin_real_le_of_bilinear_bound (A : Matrix κ κ ℝ) {B : ℝ}
    (hA : ∀ x y : κ → Bool, |(fun i ↦ signVal (x i)) ⬝ᵥ A *ᵥ (fun j ↦ signVal (y j))| ≤ B)
    (v : EuclideanSpace ℝ κ) :
    ‖A.toEuclideanLin v‖ ≤ B * ‖v‖ := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have hv0 : v = 0 := Subsingleton.elim _ _
    rw [hv0, map_zero, norm_zero, mul_zero]
  · let x : κ → Bool := fun i ↦ decide ((A *ᵥ v.ofLp) i < 0)
    have hx_abs (i : κ) : signVal (x i) * (A *ᵥ v.ofLp) i = |(A *ᵥ v.ofLp) i| := by
      dsimp only [x]
      by_cases hlt : (A *ᵥ v.ofLp) i < 0
      · simp [hlt, abs_of_neg hlt]
      · simp [hlt, abs_of_nonneg (not_lt.mp hlt)]
    have hl2_le_l1 : ‖A.toEuclideanLin v‖ ≤ ∑ i : κ, |(A *ᵥ v.ofLp) i| := by
      have hsq : ‖A.toEuclideanLin v‖ ^ 2 ≤ (∑ i : κ, |(A *ᵥ v.ofLp) i|) ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
        have hcoe : ∀ i : κ, (A.toEuclideanLin v).ofLp i = (A *ᵥ v.ofLp) i := fun _ ↦ rfl
        simp_rw [hcoe, Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ abs_nonneg _
      exact le_of_pow_le_pow_left₀ (by norm_num)
        (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) hsq
    let uT : κ → ℝ := Aᵀ *ᵥ fun i ↦ signVal (x i)
    let y : κ → Bool := fun j ↦ decide (uT j < 0)
    have hy_abs (j : κ) : signVal (y j) * uT j = |uT j| := by
      dsimp only [y]
      by_cases hlt : uT j < 0
      · simp [hlt, abs_of_neg hlt]
      · simp [hlt, abs_of_nonneg (not_lt.mp hlt)]
    have hcoord_le (j : κ) : |v.ofLp j| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have hl1_le : ∑ i : κ, |(A *ᵥ v.ofLp) i| ≤ ‖v‖ * ∑ j : κ, |uT j| := by
      calc
        ∑ i : κ, |(A *ᵥ v.ofLp) i|
            = (fun i ↦ signVal (x i)) ⬝ᵥ (A *ᵥ v.ofLp) := by
                rw [dotProduct]
                exact Finset.sum_congr rfl fun i _ ↦ (hx_abs i).symm
        _ = uT ⬝ᵥ v.ofLp := by
              rw [dotProduct_mulVec, ← mulVec_transpose]
        _ ≤ ∑ j : κ, |uT j| * |v.ofLp j| := by
              rw [dotProduct]
              exact Finset.sum_le_sum fun j _ ↦ (le_abs_self _).trans_eq (abs_mul _ _)
        _ ≤ ∑ j : κ, |uT j| * ‖v‖ :=
              Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hcoord_le j) (abs_nonneg _)
        _ = ‖v‖ * ∑ j : κ, |uT j| := by rw [← Finset.sum_mul, mul_comm]
    have huT_le : ∑ j : κ, |uT j| ≤ B := by
      calc
        ∑ j : κ, |uT j|
            = (fun j ↦ signVal (y j)) ⬝ᵥ uT := by
                rw [dotProduct]
                exact Finset.sum_congr rfl fun j _ ↦ (hy_abs j).symm
        _ = (fun i ↦ signVal (x i)) ⬝ᵥ A *ᵥ (fun j ↦ signVal (y j)) := by
              dsimp only [uT]
              rw [dotProduct_comm, ← vecMul_transpose, transpose_transpose, dotProduct_mulVec]
        _ ≤ B := (le_abs_self _).trans (hA x y)
    calc
      ‖A.toEuclideanLin v‖ ≤ ‖v‖ * ∑ j : κ, |uT j| := hl2_le_l1.trans hl1_le
      _ ≤ ‖v‖ * B := mul_le_mul_of_nonneg_left huT_le (norm_nonneg v)
      _ = B * ‖v‖ := mul_comm _ _

/-- Complexified operator norm bound `‖(A.map Complex.ofReal).toEuclideanLin w‖ ≤ B * ‖w‖` for a
real matrix `A` whose `±1` bilinear form is bounded by `B`. -/
theorem norm_toEuclideanLin_complex_le_of_bilinear_bound (A : Matrix κ κ ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ x y : κ → Bool, |(fun i ↦ signVal (x i)) ⬝ᵥ A *ᵥ (fun j ↦ signVal (y j))| ≤ B)
    (w : EuclideanSpace ℂ κ) :
    ‖(A.map Complex.ofReal).toEuclideanLin w‖ ≤ B * ‖w‖ := by
  let wRe : EuclideanSpace ℝ κ := WithLp.toLp 2 fun j ↦ (w.ofLp j).re
  let wIm : EuclideanSpace ℝ κ := WithLp.toLp 2 fun j ↦ (w.ofLp j).im
  have hre := norm_toEuclideanLin_real_le_of_bilinear_bound A hA wRe
  have him := norm_toEuclideanLin_real_le_of_bilinear_bound A hA wIm
  have hnorm_w : ‖wRe‖ ^ 2 + ‖wIm‖ ^ 2 = ‖w‖ ^ 2 := by
    simp only [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
      Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp [wRe, wIm]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hnorm_Aw :
      ‖(A.map Complex.ofReal).toEuclideanLin w‖ ^ 2 =
        ‖A.toEuclideanLin wRe‖ ^ 2 + ‖A.toEuclideanLin wIm‖ ^ 2 := by
    simp only [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
      Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hentry : ((A.map Complex.ofReal).toEuclideanLin w).ofLp i =
        (((A.toEuclideanLin wRe).ofLp i : ℝ) : ℂ) +
          (((A.toEuclideanLin wIm).ofLp i : ℝ) : ℂ) * Complex.I := by
      change ((A.map Complex.ofReal) *ᵥ w.ofLp) i =
        (((A *ᵥ wRe.ofLp) i : ℝ) : ℂ) + (((A *ᵥ wIm.ofLp) i : ℝ) : ℂ) * Complex.I
      simp only [mulVec, dotProduct, map_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hj : w.ofLp j = ((wRe.ofLp j : ℝ) : ℂ) + ((wIm.ofLp j : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im (w.ofLp j)).symm
      conv_lhs => rw [hj]
      ring
    rw [hentry, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hsq : ‖(A.map Complex.ofReal).toEuclideanLin w‖ ^ 2 ≤ (B * ‖w‖) ^ 2 := by
    rw [hnorm_Aw, mul_pow, ← hnorm_w, mul_add]
    exact add_le_add
      ((pow_le_pow_left₀ (norm_nonneg _) hre 2).trans_eq (mul_pow _ _ _))
      ((pow_le_pow_left₀ (norm_nonneg _) him 2).trans_eq (mul_pow _ _ _))
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq

private theorem star_dotProduct_self_eq_norm_sq {α : Type*} [Fintype α] (z : α → ℂ) :
    star z ⬝ᵥ z = ((‖(WithLp.toLp 2 z : EuclideanSpace ℂ α)‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply Complex.ext
  · simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  · simp [sq, mul_comm]

/-- **Unitary block-encoding dilation**: for any
complex matrix `M : Matrix κ κ ℂ` and `c > 0` satisfying `‖M.toEuclideanLin v‖ ≤ c * ‖v‖` for all
`v`, there exists a unitary matrix `U ∈ Matrix.unitaryGroup (κ ⊕ κ) ℂ` whose upper-left `κ × κ`
block equals `(c : ℂ)⁻¹ • M`, so that for every `y : κ → ℂ`,
`U *ᵥ Sum.elim y 0 = Sum.elim ((c : ℂ)⁻¹ • (M *ᵥ y)) φ` for some `φ : κ → ℂ`.
-/
theorem exists_unitary_blockEncoding (M : Matrix κ κ ℂ) {c : ℝ} (hc : 0 < c)
    (hM : ∀ v : EuclideanSpace ℂ κ, ‖M.toEuclideanLin v‖ ≤ c * ‖v‖) :
    ∃ U ∈ Matrix.unitaryGroup (κ ⊕ κ) ℂ,
      ∀ i j : κ, U (Sum.inl i) (Sum.inl j) = (c : ℂ)⁻¹ * M i j := by
  let A : Matrix κ κ ℂ := ((c : ℂ)⁻¹) • M
  have hA_norm (v : EuclideanSpace ℂ κ) : ‖A.toEuclideanLin v‖ ≤ ‖v‖ := by
    have hsmul : A.toEuclideanLin v = ((c : ℂ)⁻¹) • M.toEuclideanLin v := by
      dsimp only [A]
      rw [map_smul, LinearMap.smul_apply]
    rw [hsmul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
    exact (inv_mul_le_iff₀ hc).mpr (hM v)
  have hdef_psd : (1 - Aᴴ * A).PosSemidef := by
    have hherm : (1 - Aᴴ * A).IsHermitian :=
      isHermitian_one.sub (posSemidef_conjTranspose_mul_self A).isHermitian
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨hherm, fun x ↦ ?_⟩
    let vx : EuclideanSpace ℂ κ := WithLp.toLp 2 x
    have hAx_eq : A.toEuclideanLin vx = WithLp.toLp 2 (A *ᵥ x) := by
      ext i
      rfl
    have h1 : star x ⬝ᵥ ((1 - Aᴴ * A) *ᵥ x) =
        ((‖vx‖ ^ 2 - ‖A.toEuclideanLin vx‖ ^ 2 : ℝ) : ℂ) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec]
      have hstar : vecMul (star x) Aᴴ = star (A *ᵥ x) := by
        ext j
        simp [vecMul, mulVec, dotProduct, mul_comm]
      rw [hstar, hAx_eq, star_dotProduct_self_eq_norm_sq x,
        star_dotProduct_self_eq_norm_sq (A *ᵥ x), Complex.ofReal_sub]
    rw [h1, Complex.nonneg_iff]
    exact ⟨sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (hA_norm vx) 2), rfl⟩
  obtain ⟨B, hB_sq⟩ : ∃ B : Matrix κ κ ℂ, Bᴴ * B = 1 - Aᴴ * A := by
    let B₀ : Matrix κ κ ℂ := CFC.sqrt (1 - Aᴴ * A)
    have hB_psd : B₀.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - Aᴴ * A))
    refine ⟨B₀, ?_⟩
    rw [hB_psd.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self (1 - Aᴴ * A) hdef_psd.nonneg
  let V : Matrix (κ ⊕ κ) κ ℂ := Sum.elim A B
  have hV_gram : Vᴴ * V = 1 := by
    have hsplit : Vᴴ * V = Aᴴ * A + Bᴴ * B := by
      ext i j
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, Matrix.mul_apply,
        Matrix.mul_apply]
      rfl
    rw [hsplit, hB_sq, add_sub_cancel]
  let E₁ := EuclideanSpace ℂ κ
  let E₂ := EuclideanSpace ℂ (κ ⊕ κ)
  let inlIso : E₁ →ₗᵢ[ℂ] E₂ :=
    { toLinearMap :=
        { toFun := fun v ↦ WithLp.toLp 2 (Sum.elim v.ofLp 0)
          map_add' := fun u v ↦ by
            ext p
            change Sum.elim ((u + v).ofLp) (0 : κ → ℂ) p =
              ((WithLp.toLp 2 (Sum.elim u.ofLp 0) : E₂) +
                (WithLp.toLp 2 (Sum.elim v.ofLp 0) : E₂)).ofLp p
            rw [WithLp.ofLp_add, WithLp.ofLp_add]
            cases p <;> simp
          map_smul' := fun r v ↦ by
            ext p
            change Sum.elim ((r • v).ofLp) (0 : κ → ℂ) p =
              (r • (WithLp.toLp 2 (Sum.elim v.ofLp 0) : E₂)).ofLp p
            rw [WithLp.ofLp_smul, WithLp.ofLp_smul]
            cases p <;> simp }
      norm_map' := fun v ↦ by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        rw [Fintype.sum_sum_type]
        simp [WithLp.ofLp_toLp] }
  let V_iso : E₁ →ₗᵢ[ℂ] E₂ :=
    { toLinearMap := V.toEuclideanLin
      norm_map' := fun v ↦ by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
        apply Complex.ofReal_injective
        have hv_eq : V.toEuclideanLin v = WithLp.toLp 2 (V *ᵥ v.ofLp) := by
          ext p
          rfl
        have hv_self : v = WithLp.toLp 2 v.ofLp := by
          ext i
          rfl
        have h1 : ((‖V.toEuclideanLin v‖ ^ 2 : ℝ) : ℂ) = star (V *ᵥ v.ofLp) ⬝ᵥ (V *ᵥ v.ofLp) := by
          rw [hv_eq]
          exact (star_dotProduct_self_eq_norm_sq (V *ᵥ v.ofLp)).symm
        have h2 : ((‖v‖ ^ 2 : ℝ) : ℂ) = star v.ofLp ⬝ᵥ v.ofLp := by
          conv_lhs => rw [hv_self]
          exact (star_dotProduct_self_eq_norm_sq v.ofLp).symm
        have hstarV : star (V *ᵥ v.ofLp) = vecMul (star v.ofLp) Vᴴ := by
          ext p
          simp [vecMul, mulVec, dotProduct, mul_comm]
        rw [h1, h2, hstarV, ← dotProduct_mulVec, mulVec_mulVec, hV_gram, one_mulVec] }
  let S : Submodule ℂ E₂ := LinearMap.range inlIso.toLinearMap
  let inlToS : E₁ →ₗᵢ[ℂ] S :=
    { toLinearMap := inlIso.toLinearMap.rangeRestrict
      norm_map' := fun v ↦ inlIso.norm_map v }
  let eS : E₁ ≃ₗᵢ[ℂ] S := LinearIsometryEquiv.ofSurjective inlToS
    (fun ⟨_, y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩)
  let L : S →ₗᵢ[ℂ] E₂ := V_iso.comp eS.symm.toLinearIsometry
  let U_iso : E₂ →ₗᵢ[ℂ] E₂ := L.extend
  let U : Matrix (κ ⊕ κ) (κ ⊕ κ) ℂ := Matrix.toEuclideanLin.symm U_iso.toLinearMap
  have hU_lin : U.toEuclideanLin = U_iso.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hU_unit : U ∈ Matrix.unitaryGroup (κ ⊕ κ) ℂ := by
    have hUU : Uᴴ * U = 1 := by
      apply Matrix.toEuclideanLin.injective
      apply LinearMap.ext
      intro x
      have hmul : (Uᴴ * U).toEuclideanLin x = Uᴴ.toEuclideanLin (U.toEuclideanLin x) := by
        ext p
        change ((Uᴴ * U) *ᵥ x.ofLp) p = (Uᴴ *ᵥ (U *ᵥ x.ofLp)) p
        rw [mulVec_mulVec]
      have hone : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) ℂ).toEuclideanLin x = x := by
        ext p
        change (1 *ᵥ x.ofLp) p = x.ofLp p
        rw [one_mulVec]
      rw [hmul, hone]
      apply ext_inner_left ℂ
      intro y
      have hadj : Uᴴ.toEuclideanLin = LinearMap.adjoint U.toEuclideanLin :=
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint U
      rw [hadj, LinearMap.adjoint_inner_right, hU_lin]
      exact U_iso.inner_map_map y x
    exact (Matrix.mem_unitaryGroup_iff').mpr hUU
  refine ⟨U, hU_unit, fun i j ↦ ?_⟩
  let ej : E₁ := WithLp.toLp 2 (Pi.single j 1)
  have hinl_ej : inlIso ej = WithLp.toLp 2 (Pi.single (Sum.inl j) 1) := by
    ext p
    cases p <;> simp [inlIso, ej, Pi.single_apply]
  have heS_symm : eS.symm ⟨inlIso ej, LinearMap.mem_range_self _ ej⟩ = ej :=
    eS.symm_apply_apply ej
  have hU_ej : U.toEuclideanLin (inlIso ej) = V.toEuclideanLin ej := by
    rw [hU_lin]
    change L.extend (inlIso ej) = V.toEuclideanLin ej
    rw [L.extend_apply ⟨inlIso ej, LinearMap.mem_range_self _ ej⟩]
    change V_iso (eS.symm ⟨inlIso ej, LinearMap.mem_range_self _ ej⟩) = V.toEuclideanLin ej
    rw [heS_symm]
    rfl
  have hcol : (U *ᵥ (Pi.single (Sum.inl j) (1 : ℂ))) (Sum.inl i) =
      (V *ᵥ ej.ofLp) (Sum.inl i) := by
    have h := congrArg (fun v : E₂ ↦ v.ofLp (Sum.inl i)) hU_ej
    rw [hinl_ej] at h
    exact h
  have hUL : (U *ᵥ (Pi.single (Sum.inl j) (1 : ℂ))) (Sum.inl i) = U (Sum.inl i) (Sum.inl j) := by
    simp [mulVec, dotProduct, Pi.single_apply]
  have hVA : (V *ᵥ ej.ofLp) (Sum.inl i) = (c : ℂ)⁻¹ * M i j := by
    change (A i) ⬝ᵥ ej.ofLp = (c : ℂ)⁻¹ * M i j
    simp [A, dotProduct, ej, Pi.single_apply]
  exact hUL.symm.trans (hcol.trans hVA)

end OperatorNormAndBlockEncoding

end CslibFrontier.BooleanAnalysis
