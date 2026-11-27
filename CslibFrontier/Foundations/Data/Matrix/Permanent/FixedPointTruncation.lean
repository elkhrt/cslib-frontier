/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.LinearAlgebra.Matrix.Permanent

import Mathlib.Data.Nat.Choose.Sum

/-!
# Fixed-Point Inclusion-Exclusion and Off-Diagonal Attenuation for Matrix Permanents

This module develops two algebraic identities connecting permutation fixed points and matrix
permanents that arise in algebraic complexity and linear-optical sampling (boson sampling)
distinguishability theory:

1. **Takács generalized fixed-point inclusion-exclusion**: for any weight `f : Equiv.Perm α → R`
   on the symmetric group of a finite type `α` of cardinality `N`, letting
   `fixedSubsetSum f s = ∑_{#I = s} ∑_{∀ i ∈ I, σ i = i} f σ`, one expresses both the exact
   fixed-point stratum `∑_{#fix(σ) = n} f σ` and the tail sum `∑_{#fix(σ) < N - K} f σ` as
   explicit alternating binomial combinations of `fixedSubsetSum f s`. When
   `f σ = ∏ i, B i (σ i)`, each `fixedSubsetSum` evaluates to a sum of principal-submatrix
   permanents weighted by complementary diagonal entries.
2. **Off-diagonal attenuation of permanents**: scaling every off-diagonal entry of `A` by `ξ`
   while preserving the diagonal decomposes `permanent (attenuateOffDiag ξ A)` by permutation
   support size `∑ σ, ξ ^ #σ.support * ∏ i, A i (σ i)`, interpolating smoothly between the
   diagonal product (`ξ = 0`) and the full matrix permanent (`ξ = 1`).

## Main definitions

* `CslibFrontier.Matrix.fixedFinset`: finite set `{x : α | σ x = x}` of fixed points of a
  permutation `σ : Equiv.Perm α`.
* `CslibFrontier.Matrix.fixedSubsetSum`: sum of `f σ` over `s`-element subsets `I ⊆ α` and
  permutations `σ` fixing `I` pointwise.
* `CslibFrontier.Matrix.attenuateOffDiag`: matrix obtained by scaling off-diagonal entries of `A`
  by `ξ` while keeping diagonal entries unchanged.

## Main results

* `CslibFrontier.Matrix.sum_neg_one_pow_mul_choose_of_lt` and
  `CslibFrontier.Matrix.sum_neg_one_pow_mul_choose_self`: closed-form partial alternating
  binomial sums.
* `CslibFrontier.Matrix.sum_perm_fixed_eq_inclusion_exclusion`: exact fixed-point stratum
  formula `∑_{#fix(σ) = n} f σ = ∑_{s = n}^N (-1)^{s - n} C(s, n) fixedSubsetSum f s`.
* `CslibFrontier.Matrix.sum_perm_fixed_lt_eq_fixedSubsetSum`: truncated tail-sum identity
  `∑_{#fix(σ) < N - K} f σ = f_0 - ∑_{s = N - K}^N (-1)^{s - (N - K)} C(s - 1, N - K - 1) f_s`.
* `CslibFrontier.Matrix.fixedSubsetSum_prod_eq_sum_permanent` and
  `CslibFrontier.Matrix.sum_perm_fixed_lt_prod_eq_permanent_sub`: principal-submatrix permanent
  expansion of `fixedSubsetSum` and of fixed-point-truncated permanents.
* `CslibFrontier.Matrix.permanent_attenuateOffDiag`: support-graded permanent expansion of
  `attenuateOffDiag ξ A`, with specializations at `ξ = 0` and `ξ = 1`.
-/

public section

open scoped BigOperators

namespace CslibFrontier.Matrix

section AlternatingBinomial

/-- Partial alternating sum of binomial coefficients: for `m < s`,
`∑_{n=0}^m (-1)^n C(s, n) = (-1)^m C(s - 1, m)`. -/
theorem sum_neg_one_pow_mul_choose_of_lt {R : Type*} [CommRing R] {m s : ℕ} (hms : m < s) :
    (∑ n ∈ Finset.range (m + 1), (-1 : R) ^ n * (s.choose n : R)) =
      (-1 : R) ^ m * ((s - 1).choose m : R) := by
  rcases s with _ | s'
  · omega
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega), Nat.choose_succ_succ s' k, Nat.cast_add, mul_add]
    have hsign : (-1 : R) ^ (k + 1) = -((-1 : R) ^ k) := by rw [pow_succ]; ring
    rw [hsign]
    ring

/-- Full alternating sum of binomial coefficients: `1` for `s = 0` and `0` for `s ≥ 1`. -/
theorem sum_neg_one_pow_mul_choose_self {R : Type*} [CommRing R] (s : ℕ) :
    (∑ n ∈ Finset.range (s + 1), (-1 : R) ^ n * (s.choose n : R)) =
      if s = 0 then 1 else 0 := by
  rcases s with _ | s'
  · simp
  · simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hz : (∑ n ∈ Finset.range (s' + 1 + 1), (-1 : ℤ) ^ n * ((s' + 1).choose n : ℤ)) = 0 := by
      simpa [mul_comm] using Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero s')
    have hcast : ((∑ n ∈ Finset.range (s' + 1 + 1),
        (-1 : ℤ) ^ n * ((s' + 1).choose n : ℤ) : ℤ) : R) = 0 := by rw [hz, Int.cast_zero]
    simpa using hcast

end AlternatingBinomial

section FixedPointInclusionExclusion

variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

/-- Finite set of fixed points `{x : α | σ x = x}` of a permutation `σ : Equiv.Perm α`. -/
def fixedFinset (σ : Equiv.Perm α) : Finset α :=
  Finset.univ.filter fun x ↦ σ x = x

/-- Membership in `fixedFinset σ` holds iff `σ x = x`. -/
@[simp]
theorem mem_fixedFinset {σ : Equiv.Perm α} {x : α} :
    x ∈ fixedFinset σ ↔ σ x = x := by
  simp [fixedFinset]

/-- Relation `#(fixedFinset σ) = card α - #σ.support`. -/
theorem card_fixedFinset (σ : Equiv.Perm α) :
    (fixedFinset σ).card = Fintype.card α - σ.support.card := by
  have hcompl : fixedFinset σ = σ.supportᶜ := by
    ext x
    simp [fixedFinset, Equiv.Perm.mem_support]
  rw [hcompl, Finset.card_compl]

/-- Sum of a permutation weight `f : Equiv.Perm α → R` over all `s`-element subsets `I ⊆ α` and
all permutations fixing `I` pointwise. -/
def fixedSubsetSum (f : Equiv.Perm α → R) (s : ℕ) : R :=
  ∑ I ∈ Finset.univ.powersetCard s,
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦ ∀ i ∈ I, σ i = i), f σ

/-- At `s = 0`, `fixedSubsetSum f 0` sums `f` over all permutations in `Equiv.Perm α`. -/
@[simp]
theorem fixedSubsetSum_zero (f : Equiv.Perm α → R) :
    fixedSubsetSum f 0 = ∑ σ : Equiv.Perm α, f σ := by
  simp [fixedSubsetSum]

/-- Double-counting formula `fixedSubsetSum f s = ∑ σ, C(#fix(σ), s) * f σ`. -/
theorem fixedSubsetSum_eq_sum_choose (f : Equiv.Perm α → R) (s : ℕ) :
    fixedSubsetSum f s =
      ∑ σ : Equiv.Perm α, ((fixedFinset σ).card.choose s : R) * f σ := by
  unfold fixedSubsetSum
  have hswap :
      (∑ I ∈ Finset.univ.powersetCard s,
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦ ∀ i ∈ I, σ i = i), f σ) =
      ∑ σ : Equiv.Perm α,
        ∑ I ∈ (Finset.univ.powersetCard s).filter (fun I ↦ ∀ i ∈ I, σ i = i), f σ := by
    simp_rw [Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have hset : ((Finset.univ.powersetCard s).filter fun I : Finset α ↦ ∀ i ∈ I, σ i = i) =
      (fixedFinset σ).powersetCard s := by
    ext I
    simp [Finset.mem_powersetCard, Finset.subset_iff, fixedFinset, and_comm]
  rw [hset, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- Takács generalized inclusion-exclusion for the exact fixed-point stratum `#fix(σ) = n`. -/
theorem sum_perm_fixed_eq_inclusion_exclusion (f : Equiv.Perm α → R) (n : ℕ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦ (fixedFinset σ).card = n), f σ) =
      ∑ s ∈ Finset.Icc n (Fintype.card α),
        (-1 : R) ^ (s - n) * (s.choose n : R) * fixedSubsetSum f s := by
  simp_rw [fixedSubsetSum_eq_sum_choose, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  set r := (fixedFinset σ).card
  have hrN : r ≤ Fintype.card α := Finset.card_le_univ _
  by_cases hnr : n ≤ r
  · have hsub : Finset.Icc n r ⊆ Finset.Icc n (Fintype.card α) :=
      Finset.Icc_subset_Icc_right hrN
    have hvan : ∀ s ∈ Finset.Icc n (Fintype.card α), s ∉ Finset.Icc n r →
        (-1 : R) ^ (s - n) * (s.choose n : R) * (r.choose s : R) = 0 := by
      intro s hs hns
      have hgt : r < s := by
        have := Finset.mem_Icc.mp hs
        rw [Finset.mem_Icc] at hns
        omega
      simp [Nat.choose_eq_zero_of_lt hgt]
    rw [← Finset.sum_subset hsub hvan]
    have hreidx : (∑ s ∈ Finset.Icc n r,
        (-1 : R) ^ (s - n) * (s.choose n : R) * (r.choose s : R)) =
        (r.choose n : R) *
          ∑ j ∈ Finset.range (r - n + 1), (-1 : R) ^ j * ((r - n).choose j : R) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun s _ ↦ s - n) ?_ ?_ ?_ ?_
      · intro s hs; exact Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hs; omega)
      · intro a ha b hb h
        have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega
      · intro j hj
        have := Finset.mem_range.mp hj
        exact ⟨n + j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro s hs
        obtain ⟨hns, hsr⟩ := Finset.mem_Icc.mp hs
        have hch : s.choose n * r.choose s = r.choose n * (r - n).choose (s - n) := by
          rw [mul_comm (s.choose n), Nat.choose_mul (n := r) (k := s) (s := n) hns]
        calc (-1 : R) ^ (s - n) * (s.choose n : R) * (r.choose s : R)
            = (-1 : R) ^ (s - n) * ((s.choose n * r.choose s : ℕ) : R) := by push_cast; ring
          _ = (r.choose n : R) * ((-1 : R) ^ (s - n) * ((r - n).choose (s - n) : R)) := by
              rw [hch]; push_cast; ring
    rw [hreidx, sum_neg_one_pow_mul_choose_self]
    by_cases hrn : r = n
    · subst hrn; simp
    · have hne : r - n ≠ 0 := by omega
      simp [hrn, hne]
  · have hrn : r ≠ n := by omega
    rw [ite_eq_right hrn]
    symm
    refine mul_eq_zero_of_left (Finset.sum_eq_zero fun s hs ↦ ?_) _
    have hgt : r < s := by have := Finset.mem_Icc.mp hs; omega
    simp [Nat.choose_eq_zero_of_lt hgt]

/-- Tail inclusion-exclusion over permutations fixing strictly fewer than `card α - K` elements
(i.e. moving at least `K + 1` elements). -/
theorem sum_perm_fixed_lt_eq_fixedSubsetSum (f : Equiv.Perm α → R) {K : ℕ}
    (hK : K < Fintype.card α) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦
        (fixedFinset σ).card < Fintype.card α - K), f σ) =
      fixedSubsetSum f 0 -
        ∑ s ∈ Finset.Icc (Fintype.card α - K) (Fintype.card α),
          (-1 : R) ^ (s - (Fintype.card α - K)) *
            ((s - 1).choose (Fintype.card α - K - 1) : R) * fixedSubsetSum f s := by
  set N := Fintype.card α
  set m := N - K - 1
  have hm1 : m + 1 = N - K := by omega
  have hpart : (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦ (fixedFinset σ).card < N - K),
      f σ) =
      ∑ n ∈ Finset.range (m + 1),
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦ (fixedFinset σ).card = n), f σ := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, hm1]
      exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨_, hn, he⟩ ↦ he ▸ hn⟩
    · intro a _ b _ hne
      exact Finset.disjoint_left.mpr fun σ h1 h2 ↦
        hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hpart]
  simp_rw [sum_perm_fixed_eq_inclusion_exclusion]
  have hexch : (∑ n ∈ Finset.range (m + 1),
      ∑ s ∈ Finset.Icc n N, (-1 : R) ^ (s - n) * (s.choose n : R) * fixedSubsetSum f s) =
      ∑ s ∈ Finset.range (N + 1),
        (∑ n ∈ Finset.range (min m s + 1), (-1 : R) ^ (s - n) * (s.choose n : R)) *
          fixedSubsetSum f s := by
    simp_rw [Finset.sum_mul]
    calc (∑ n ∈ Finset.range (m + 1),
            ∑ s ∈ Finset.Icc n N, (-1 : R) ^ (s - n) * (s.choose n : R) * fixedSubsetSum f s)
        = ∑ n ∈ Finset.range (m + 1), ∑ s ∈ Finset.range (N + 1),
            if n ≤ s then (-1 : R) ^ (s - n) * (s.choose n : R) * fixedSubsetSum f s else 0 := by
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          rw [← Finset.sum_filter]
          congr 1; ext s
          simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
      _ = ∑ s ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (m + 1),
            if n ≤ s then (-1 : R) ^ (s - n) * (s.choose n : R) * fixedSubsetSum f s else 0 :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [← Finset.sum_filter]
          congr 1; ext n
          simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hexch]
  have hcoeff : ∀ s ∈ Finset.range (N + 1),
      (∑ n ∈ Finset.range (min m s + 1), (-1 : R) ^ (s - n) * (s.choose n : R)) =
        if s = 0 then 1
        else if s ≤ m then 0
        else (-1 : R) ^ (s - m) * ((s - 1).choose m : R) := by
    intro s _
    have hpull : ∀ k ≤ s,
        (∑ n ∈ Finset.range (k + 1), (-1 : R) ^ (s - n) * (s.choose n : R)) =
          (-1 : R) ^ s * ∑ n ∈ Finset.range (k + 1), (-1 : R) ^ n * (s.choose n : R) := by
      intro k hk
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hns : n ≤ s := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)).trans hk
      have hsign : (-1 : R) ^ s * (-1 : R) ^ n = (-1 : R) ^ (s - n) := by
        have hs : s = (s - n) + n := (Nat.sub_add_cancel hns).symm
        conv_lhs => rw [hs, pow_add]
        rw [mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
      rw [← mul_assoc, hsign]
    by_cases hs0 : s = 0
    · subst hs0; simp
    · rw [ite_eq_right hs0]
      by_cases hsm : s ≤ m
      · rw [ite_eq_left hsm, min_eq_right hsm, hpull s le_rfl, sum_neg_one_pow_mul_choose_self,
          ite_eq_right hs0, mul_zero]
      · have hms : m < s := by omega
        rw [ite_eq_right hsm, min_eq_left hms.le, hpull m hms.le,
          sum_neg_one_pow_mul_choose_of_lt hms,
          ← mul_assoc]
        congr 1
        have hs : s = (s - m) + m := (Nat.sub_add_cancel hms.le).symm
        conv_lhs => rw [hs, pow_add]
        rw [mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
  have hsplit : (∑ s ∈ Finset.range (N + 1),
      (if s = 0 then (1 : R)
        else if s ≤ m then 0
        else (-1 : R) ^ (s - m) * ((s - 1).choose m : R)) * fixedSubsetSum f s) =
      fixedSubsetSum f 0 +
        ∑ s ∈ Finset.Icc (N - K) N,
          (-1 : R) ^ (s - m) * ((s - 1).choose m : R) * fixedSubsetSum f s := by
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, one_mul, Nat.succ_ne_zero, Nat.add_sub_cancel,
      add_comm (fixedSubsetSum f 0)]
    congr 1
    have hre : (∑ k ∈ Finset.range N,
        (if k + 1 ≤ m then (0 : R)
          else (-1 : R) ^ (k + 1 - m) * (k.choose m : R)) * fixedSubsetSum f (k + 1)) =
        ∑ s ∈ Finset.Icc 1 N,
          (if s ≤ m then (0 : R)
            else (-1 : R) ^ (s - m) * ((s - 1).choose m : R)) * fixedSubsetSum f s :=
      Finset.sum_bij (fun k _ ↦ k + 1)
        (fun k hk ↦ Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hk; omega⟩)
        (fun _ _ _ _ h ↦ Nat.succ.inj h)
        (fun s hs ↦ ⟨s - 1, Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hs; omega),
          by have := Finset.mem_Icc.mp hs; omega⟩)
        (fun _ _ ↦ by simp)
    rw [hre]
    have hsub_icc : Finset.Icc (N - K) N ⊆ Finset.Icc 1 N := fun s hs ↦
      Finset.mem_Icc.mpr ⟨by have := Finset.mem_Icc.mp hs; omega, (Finset.mem_Icc.mp hs).2⟩
    rw [← Finset.sum_subset hsub_icc fun s hs hns ↦ by
      have hle : s ≤ m := by have := Finset.mem_Icc.mp hs; rw [Finset.mem_Icc] at hns; omega
      simp [hle]]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hnle : ¬ s ≤ m := by have := Finset.mem_Icc.mp hs; omega
    simp [hnle]
  rw [Finset.sum_congr rfl fun s hs ↦ by rw [hcoeff s hs], hsplit, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hge : N - K ≤ s := (Finset.mem_Icc.mp hs).1
  have hpow : (-1 : R) ^ (s - m) = -((-1 : R) ^ (s - (N - K))) := by
    rw [show s - m = (s - (N - K)) + 1 by omega, pow_succ]; ring
  rw [hpow]; ring

/-- Principal-submatrix permanent formula for `fixedSubsetSum` of a matrix product weight
`σ ↦ ∏ i, B i (σ i)`:
`fixedSubsetSum (fun σ ↦ ∏ i, B i (σ i)) s =
  ∑_{#I = s} (∏ i ∈ I, B i i) * permanent (B[Iᶜ | Iᶜ])`. -/
theorem fixedSubsetSum_prod_eq_sum_permanent (B : Matrix α α R) (s : ℕ) :
    fixedSubsetSum (fun σ ↦ ∏ i : α, B (σ i) i) s =
      ∑ I ∈ Finset.univ.powersetCard s,
        (∏ i ∈ I, B i i) *
          (B.submatrix (Subtype.val : (Iᶜ : Finset α) → α) Subtype.val).permanent := by
  unfold fixedSubsetSum
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [Matrix.permanent, Finset.mul_sum]
  let toFix : Equiv.Perm (Iᶜ : Finset α) → Equiv.Perm α := Equiv.Perm.ofSubtype
  symm
  refine Finset.sum_bij (fun τ _ ↦ toFix τ) ?_ ?_ ?_ ?_
  · intro τ _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi ↦ ?_⟩
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp [hi])
  · intro τ₁ _ τ₂ _ h
    exact Equiv.Perm.ofSubtype_injective h
  · intro σ hσ
    have hfix := (Finset.mem_filter.mp hσ).2
    have hinv : ∀ x : α, σ x ∈ Iᶜ ↔ x ∈ Iᶜ := fun x ↦ by
      simp only [Finset.mem_compl]
      exact ⟨fun h hx ↦ h (by rwa [hfix x hx]),
        fun h hx ↦ h (σ.injective (hfix (σ x) hx) ▸ hx)⟩
    refine ⟨σ.subtypePerm hinv, Finset.mem_univ _, ?_⟩
    ext x
    by_cases hx : x ∈ Iᶜ
    · simp [toFix, Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    · have hxI : x ∈ I := Finset.notMem_compl.mp hx
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx, hfix x hxI]
  · intro τ _
    rw [← Finset.prod_sdiff (Finset.subset_univ I), Finset.sdiff_eq_inter_compl,
      Finset.univ_inter, mul_comm (∏ i ∈ Iᶜ, _)]
    congr 1
    · exact Finset.prod_congr rfl fun i hi ↦ by
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp [hi])]
    · rw [← Finset.prod_coe_sort Iᶜ]
      exact Finset.prod_congr rfl fun ⟨i, hi⟩ _ ↦ by
        simp [toFix, Equiv.Perm.ofSubtype_apply_of_mem τ hi]

/-- Closed-form principal-permanent expansion of a fixed-point-truncated matrix permanent
`∑_{#fix(σ) < card α - K} ∏ i, B i (σ i)`. -/
theorem sum_perm_fixed_lt_prod_eq_permanent_sub (B : Matrix α α R) {K : ℕ}
    (hK : K < Fintype.card α) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α ↦
        (fixedFinset σ).card < Fintype.card α - K), ∏ i : α, B (σ i) i) =
      B.permanent -
        ∑ s ∈ Finset.Icc (Fintype.card α - K) (Fintype.card α),
          (-1 : R) ^ (s - (Fintype.card α - K)) *
            ((s - 1).choose (Fintype.card α - K - 1) : R) *
            (∑ I ∈ Finset.univ.powersetCard s,
              (∏ i ∈ I, B i i) *
                (B.submatrix (Subtype.val : (Iᶜ : Finset α) → α) Subtype.val).permanent) := by
  rw [sum_perm_fixed_lt_eq_fixedSubsetSum _ hK, fixedSubsetSum_zero]
  simp_rw [fixedSubsetSum_prod_eq_sum_permanent]
  rfl

end FixedPointInclusionExclusion

section OffDiagAttenuation

variable {α R : Type*} [DecidableEq α]

/-- Off-diagonal attenuation of a square matrix: diagonal entries stay unchanged while off-diagonal
entries are scaled by `ξ`. -/
def attenuateOffDiag [SMul R R] (ξ : R) (A : Matrix α α R) : Matrix α α R :=
  Matrix.of fun i j ↦ if i = j then A i j else ξ • A i j

/-- Diagonal entries of `attenuateOffDiag ξ A` coincide with those of `A`. -/
@[simp]
theorem attenuateOffDiag_apply_self [SMul R R] (ξ : R) (A : Matrix α α R) (i : α) :
    attenuateOffDiag ξ A i i = A i i := by
  simp [attenuateOffDiag]

/-- Off-diagonal entries of `attenuateOffDiag ξ A` are scaled by `ξ`. -/
@[simp]
theorem attenuateOffDiag_apply_of_ne [SMul R R] (ξ : R) (A : Matrix α α R) {i j : α}
    (h : i ≠ j) :
    attenuateOffDiag ξ A i j = ξ • A i j := by
  simp [attenuateOffDiag, h]

/-- Support-graded permanent identity for an off-diagonal-attenuated matrix:
`(attenuateOffDiag ξ A).permanent = ∑ σ, ξ ^ #σ.support * ∏ i, A i (σ i)`. -/
theorem permanent_attenuateOffDiag [Fintype α] [CommRing R] (ξ : R) (A : Matrix α α R) :
    (attenuateOffDiag ξ A).permanent =
      ∑ σ : Equiv.Perm α, ξ ^ σ.support.card * ∏ i : α, A (σ i) i := by
  classical
  rw [Matrix.permanent]
  refine Fintype.sum_congr _ _ fun σ ↦ ?_
  have hsplit : ∀ i : α,
      attenuateOffDiag ξ A (σ i) i = (if σ i = i then 1 else ξ) * A (σ i) i := fun i ↦ by
    by_cases h : σ i = i
    · simp [attenuateOffDiag, h]
    · simp [attenuateOffDiag, h]
  simp_rw [hsplit, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter_ne_one]
  have hfilt : (Finset.univ.filter fun i : α ↦ (if σ i = i then (1 : R) else ξ) ≠ 1) ⊆
      σ.support := fun i hi ↦ by
    have hne := (Finset.mem_filter.mp hi).2
    rw [Equiv.Perm.mem_support]
    intro heq
    simp [heq] at hne
  rw [Finset.prod_subset hfilt (fun i _ hni ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hni; exact hni)]
  have hval : ∀ i ∈ σ.support, (if σ i = i then (1 : R) else ξ) = ξ := fun i hi ↦
    ite_eq_right (Equiv.Perm.mem_support.mp hi)
  rw [Finset.prod_congr rfl hval, Finset.prod_const]

/-- At `ξ = 0`, the permanent of `attenuateOffDiag 0 A` collapses to the diagonal product; at
`ξ = 1`, it recovers `A.permanent`. -/
theorem permanent_attenuateOffDiag_zero_and_one [Fintype α] [CommRing R] (A : Matrix α α R) :
    (attenuateOffDiag 0 A).permanent = (∏ i : α, A i i) ∧
      (attenuateOffDiag 1 A).permanent = A.permanent := by
  refine ⟨?_, ?_⟩
  · rw [permanent_attenuateOffDiag, Finset.sum_eq_single (1 : Equiv.Perm α)]
    · simp
    · intro σ _ hne
      have hpos : σ.support.card ≠ 0 := by
        rw [ne_eq, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]; exact hne
      simp [zero_pow hpos]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [permanent_attenuateOffDiag]
    simp [Matrix.permanent]

end OffDiagAttenuation

end CslibFrontier.Matrix
