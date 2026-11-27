/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Nondeterministic.CoverNumber
public import CslibFrontier.Computability.Communication.Nondeterministic.Functions
public import CslibFrontier.Computability.Communication.Nondeterministic.PartitionCover
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank

/-!
# Ordered-semiring completion rank of partial Boolean relations and exact cover numbers

For a partial Boolean relation `R : X → Y → Bool → Prop` and target output `z : Bool`, an
`S`-valued matrix `M : Matrix X Y S` *completes* `R` (`IsMatrixCompletion S z R M`) if `M x y = 1`
whenever `!z` is unacceptable (`¬ R x y (!z)`) and `M x y = 0` whenever `z` is unacceptable
(`¬ R x y z`). Its minimum nonnegative factorization rank `completionNonnegRank S z R` generalizes
`partitionCoverNumber` (`S = ℕ`, `partitionCoverNumber_eq_iInf_nonnegRank_nat`) to arbitrary ordered
semirings such as `ℝ` (`rk_{ℝ+}` of [Sergeev2026UniqueDisjointness, §1, p. 2]), satisfying the
universal monotone rank chain
`coverNumber z R Set.univ Set.univ ≤ completionNonnegRank S z R` and
`completionNonnegRank S z R ≤ partitionCoverNumber z R Set.univ Set.univ`
(`coverNumber_le_completionNonnegRank`, `completionNonnegRank_le_partitionCoverNumber`).

We also record the exact `coverNumberFun` values for `disjointness` (`2 ^ n`,
`coverNumberFun_disjointness`) and sharp bounds for `false`-covers of the inner product modulo two
(`2 ^ (v - 1) < coverNumberFun false (· ⬝ᵥ ·) Set.univ Set.univ ≤ 2 ^ v - 1` for `v ≥ 2`, hence
`ecomplexityFun false (· ⬝ᵥ ·) Set.univ Set.univ = v`).

## Main definitions

* `Cslib.Communication.Nondeterministic.IsMatrixCompletion`: matrix completions of a partial
  Boolean relation `R` over a semiring `S`.
* `Cslib.Communication.Nondeterministic.completionNonnegRank`: minimum `Matrix.nonnegRank` over
  all `S`-valued completions of `R`.

## Main results

* `Cslib.Communication.Nondeterministic.completionNonnegRank_nat_eq_partitionCoverNumber`:
  `completionNonnegRank ℕ z R = partitionCoverNumber z R Set.univ Set.univ`.
* `Cslib.Communication.Nondeterministic.coverNumber_le_completionNonnegRank`:
  `coverNumber z R Set.univ Set.univ ≤ completionNonnegRank S z R` over any ordered semiring
  without zero divisors (`1 ≠ 0`).
* `Cslib.Communication.Nondeterministic.completionNonnegRank_le_partitionCoverNumber`:
  `completionNonnegRank S z R ≤ partitionCoverNumber z R Set.univ Set.univ` over any ordered
  semiring.
* `Cslib.Communication.Nondeterministic.coverNumberFun_disjointness`:
  `coverNumberFun true disjointness Set.univ Set.univ = 2 ^ v`.
* `Cslib.Communication.Nondeterministic.two_pow_pred_lt_coverNumberFun_false_dotProduct`,
  `Cslib.Communication.Nondeterministic.coverNumberFun_false_dotProduct_le_sub_one`,
  `Cslib.Communication.Nondeterministic.ecomplexityFun_false_dotProduct_eq`: sharp cover-number
  bounds and exact nondeterministic `0`-complexity for inner product modulo two.
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

open Finset Matrix

section CompletionRank

variable {X Y : Type*}

/-- `M : Matrix X Y S` completes the partial Boolean relation `R` for answer `z`: `M x y = 1` where
`!z` is unacceptable and `M x y = 0` where `z` is unacceptable. -/
@[expose] def IsMatrixCompletion (S : Type*) [Zero S] [One S] (z : Bool)
    (R : X → Y → Bool → Prop) (M : Matrix X Y S) : Prop :=
  (∀ x y, ¬ R x y (!z) → M x y = 1) ∧ (∀ x y, ¬ R x y z → M x y = 0)

/-- The minimum `Matrix.nonnegRank` over all `S`-valued matrix completions of `R`. -/
noncomputable def completionNonnegRank (S : Type*) [Semiring S] [PartialOrder S] (z : Bool)
    (R : X → Y → Bool → Prop) : ℕ∞ :=
  ⨅ (M : Matrix X Y S) (_ : IsMatrixCompletion S z R M), M.nonnegRank

/-- Over `ℕ`, `completionNonnegRank` coincides with `partitionCoverNumber`. -/
theorem completionNonnegRank_nat_eq_partitionCoverNumber (z : Bool) (R : X → Y → Bool → Prop) :
    completionNonnegRank ℕ z R = partitionCoverNumber z R Set.univ Set.univ :=
  (partitionCoverNumber_eq_iInf_nonnegRank_nat z R).symm

/-- **Covering rank is at most ordered-semiring completion rank** (`rk_∨ ≤ rk_{S+}`). -/
theorem coverNumber_le_completionNonnegRank (S : Type*) [Semiring S] [PartialOrder S]
    [IsOrderedRing S] [NoZeroDivisors S] [Nontrivial S] (z : Bool) (R : X → Y → Bool → Prop) :
    coverNumber z R Set.univ Set.univ ≤ completionNonnegRank S z R := by
  refine le_iInf fun M => le_iInf fun ⟨h1, h0⟩ => ?_
  refine Matrix.le_nonnegRank_iff.2 fun r ⟨T, U, hT, hU, hTU⟩ => ?_
  refine coverNumber_le_iff.2 ⟨fun i => ({x | T x i ≠ 0}, {y | U i y ≠ 0}), ?_, ?_⟩
  · intro i x _ hx y _ hy
    by_contra hRz
    have hM0 : M x y = 0 := h0 x y hRz
    rw [← hTU] at hM0
    exact (Matrix.mul_apply_ne_zero_iff_of_nonneg hT hU x y).2 ⟨i, hx, hy⟩ hM0
  · intro x _ y _ hRnz
    have hM1 : M x y = 1 := h1 x y hRnz
    rw [← hTU] at hM1
    exact (Matrix.mul_apply_ne_zero_iff_of_nonneg hT hU x y).1 (by rw [hM1]; exact one_ne_zero)

/-- **Ordered-semiring completion rank is at most partition rank** (`rk_{S+} ≤ rk_+`). -/
theorem completionNonnegRank_le_partitionCoverNumber (S : Type*) [Semiring S] [PartialOrder S]
    [IsOrderedRing S] (z : Bool) (R : X → Y → Bool → Prop) :
    completionNonnegRank S z R ≤ partitionCoverNumber z R Set.univ Set.univ := by
  rw [← completionNonnegRank_nat_eq_partitionCoverNumber]
  refine le_iInf fun M => le_iInf fun ⟨h1, h0⟩ => ?_
  refine Matrix.le_nonnegRank_iff.2 fun r ⟨T, U, _, _, hTU⟩ => ?_
  let M' : Matrix X Y S := M.map (Nat.cast : ℕ → S)
  let T' : Matrix X (Fin r) S := T.map (Nat.cast : ℕ → S)
  let U' : Matrix (Fin r) Y S := U.map (Nat.cast : ℕ → S)
  have hcomp : IsMatrixCompletion S z R M' :=
    ⟨fun x y h => by simp [M', h1 x y h], fun x y h => by simp [M', h0 x y h]⟩
  have hfac : M'.HasNonnegFactorization (Fin r) := by
    refine ⟨T', U', fun _ _ => Nat.cast_nonneg _, fun _ _ => Nat.cast_nonneg _, ?_⟩
    ext x y
    simp only [M', T', U', Matrix.mul_apply, Matrix.map_apply, ← hTU]
    push_cast
    rfl
  exact iInf_le_of_le M' (iInf_le_of_le hcomp
    (hfac.nonnegRank_le.trans_eq (by rw [Fintype.card_fin])))

end CompletionRank

section ExactCoverNumbers

/-- **Disjointness on `v`-bit strings has exact cover number `2 ^ v`.** -/
theorem coverNumberFun_disjointness (v : ℕ) :
    coverNumberFun true (disjointness : BitString v → BitString v → Bool) Set.univ Set.univ =
      (2 ^ v : ℕ) := by
  refine le_antisymm ?_ ?_
  · exact ecomplexity_le_iff_coverNumber_le.1 (ecomplexityFun_disjointness v).le
  · have hfool := card_le_coverNumberFun_of_isFoolingSet
      (isFoolingSet_disjointness (univ : Finset (BitString v)))
      (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)
    rwa [card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), card_univ,
      BitString.card] at hfool

/-- For `v ≥ 1`, any `false`-cover of the inner product on `v`-bit strings uses strictly more than
`2 ^ (v - 1)` rectangles. -/
theorem two_pow_pred_lt_coverNumberFun_false_dotProduct {v : ℕ} (hv : 1 ≤ v) :
    ((2 ^ (v - 1) : ℕ) : ℕ∞) <
      coverNumberFun false (fun x y : BitString v => x ⬝ᵥ y) Set.univ Set.univ := by
  by_contra hle
  push Not at hle
  have hcomp : ecomplexityFun false (fun x y : BitString v => x ⬝ᵥ y) Set.univ Set.univ ≤
      (v - 1 : ℕ) := ecomplexity_le_iff_coverNumber_le.2 hle
  have hle' : (v : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) :=
    (le_ecomplexityFun_false_dotProduct v).trans hcomp
  have : v ≤ v - 1 := by exact_mod_cast hle'
  omega

/-- For `v ≥ 2`, the `2 ^ v - 1` subspaces `{0, a} × a⊥` (`a ≠ 0`) form a `false`-cover of the
inner product modulo two, so `coverNumberFun false (· ⬝ᵥ ·) Set.univ Set.univ ≤ 2 ^ v - 1`. -/
theorem coverNumberFun_false_dotProduct_le_sub_one {v : ℕ} (hv : 2 ≤ v) :
    coverNumberFun false (fun x y : BitString v => x ⬝ᵥ y) Set.univ Set.univ ≤
      ((2 ^ v - 1 : ℕ) : ℕ∞) := by
  let κ := {a : BitString v // a ≠ 0}
  let C : κ → Set (BitString v) × Set (BitString v) :=
    fun a => ({0, a.1}, {b | (a.1 ⬝ᵥ b) = false})
  have hcov : IsCover false (fun (x y : BitString v) b => (x ⬝ᵥ y) = b) Set.univ Set.univ C := by
    rw [isCover_fun_iff]
    refine ⟨fun _a _x _ hx _y _ hy => ?_, fun x _ y _ hxy => ?_⟩
    · rcases hx with rfl | rfl
      · simp; rfl
      · exact hy
    · by_cases hx : x = 0
      · subst hx
        by_cases hy : y = fun _ => true
        · subst hy
          let i₀ : Fin v := ⟨0, by omega⟩
          let i₁ : Fin v := ⟨1, by omega⟩
          have hi : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀, i₁] at this
          let a₀ : BitString v := fun i => decide (i = i₀ ∨ i = i₁)
          have ha₀ : a₀ ≠ 0 := by
            intro h0
            have := congrFun h0 i₀
            simp [a₀] at this
          refine ⟨⟨a₀, ha₀⟩, Or.inl rfl, ?_⟩
          change (∑ i : Fin v, a₀ i * true) = false
          have hpair : ∑ i : Fin v, a₀ i * true =
              ∑ _i ∈ ({i₀, i₁} : Finset (Fin v)), (true : Bool) := by
            rw [← Finset.sum_subset (Finset.subset_univ ({i₀, i₁} : Finset (Fin v)))]
            · refine Finset.sum_congr rfl fun i hi => ?_
              rw [Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with rfl | rfl <;> simp [a₀] <;> rfl
            · intro i _ hi
              rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
              simp [a₀, hi]
              rfl
          rw [hpair, Finset.sum_pair hi]
          rfl
        · obtain ⟨j, hj⟩ : ∃ j : Fin v, y j = false := by
            by_contra hall
            push Not at hall
            exact hy (funext fun j => Bool.eq_true_of_not_eq_false (hall j))
          let a₀ : BitString v := fun i => decide (i = j)
          have ha₀ : a₀ ≠ 0 := by
            intro h0
            have := congrFun h0 j
            simp [a₀] at this
          refine ⟨⟨a₀, ha₀⟩, Or.inl rfl, ?_⟩
          change (∑ i : Fin v, a₀ i * y i) = false
          rw [Finset.sum_eq_single j]
          · simp [a₀, hj]; rfl
          · intro i _ hij; simp [a₀, hij]; cases y i <;> rfl
          · intro h; exact absurd (Finset.mem_univ j) h
      · exact ⟨⟨x, hx⟩, Or.inr rfl, hxy⟩
  have hcard : Fintype.card κ = 2 ^ v - 1 := by
    have hsum : Fintype.card κ + 1 = Fintype.card (BitString v) := by
      rw [Fintype.card_subtype]
      have h2 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (BitString v))) (p := fun a => a ≠ 0)
      simpa only [ne_eq, not_not, Finset.filter_eq', Finset.mem_univ, ↓reduceIte,
        Finset.card_singleton, Finset.card_univ] using h2
    rw [BitString.card] at hsum
    omega
  exact hcov.coverNumberFun_le.trans_eq (by rw [hcard])

/-- Exact nondeterministic `0`-communication complexity of inner product modulo two:
`N⁰(IP_v) = v` for all `v : ℕ`. -/
theorem ecomplexityFun_false_dotProduct_eq (v : ℕ) :
    ecomplexityFun false (fun x y : BitString v => x ⬝ᵥ y) Set.univ Set.univ = v := by
  refine le_antisymm ?_ (le_ecomplexityFun_false_dotProduct v)
  refine ecomplexityFun_le_iff.2 ⟨fun w => ({w}, {y | (w ⬝ᵥ y) = false}),
    isCover_fun_iff.2 ⟨fun _w _x _ hx _y _ hy => ?_, fun x _ _y _ hxy => ⟨x, rfl, hxy⟩⟩⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hy

end ExactCoverNumbers

end Nondeterministic

end Cslib.Communication
