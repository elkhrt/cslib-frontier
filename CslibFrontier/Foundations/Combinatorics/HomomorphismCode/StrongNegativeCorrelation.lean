/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Card
public import CslibFrontier.Foundations.Combinatorics.HomomorphismCode.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strong Negative Correlation, Sphere Packing, and Bucket Splitting

This module proves the strong negative correlation bound for families of subsets with small
pairwise intersections and derives its coding-theoretic consequences:

- The strong negative correlation bound `r ≤ 1 / (4 τ) + 1`;
- The SNC list-size bound `ℓ(C, ρ) ≤ 1 / (4 (ρ² - Λ)) + 1` for `√Λ < ρ ≤ 1`;
- The sphere packing bound `|Ψ| ≤ 1 / (4 (Λ + ε) ε) + 1` for pairwise `≤ Λ²`-agreeing subsets
  of a homomorphism code list (including existence of maximal such subsets even for infinite
  codomains);
- The large-`ε` lemma (`Λ ≤ ε² / 2 → ℓ(aHom(G, H), Λ + ε) ≤ 1 / (2 ε²) + 1`);
- The bucket-splitting lemma decomposing any homomorphism code list into at most
  `1 / (4 (Λ + ε) ε) + 1` spheres of agreement `> Λ²`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main definitions

- `CslibFrontier.HomomorphismCode.IsStronglyNegativelyCorrelated`: `(ρ, τ)`-strong negative
  correlation of a
  family of subsets of a finite set.
- `CslibFrontier.HomomorphismCode.bucket`: the bucket `L_ψ = {φ ∈ L | agr(φ, ψ) > Λ²}` around `ψ`.

## Main results

- `CslibFrontier.HomomorphismCode.card_le_of_isStronglyNegativelyCorrelated`: `r ≤ 1 / (4 τ) + 1`.
- `CslibFrontier.HomomorphismCode.maxListSize_le_of_sqrt_codeMaxAgreement_lt`: general code SNC
  list bound.
- `CslibFrontier.HomomorphismCode.card_le_sphere_packing`: sphere packing bound on `Ψ`.
- `CslibFrontier.HomomorphismCode.maxListSize_le_of_homMaxAgreement_le_half_sq`: large-`ε`
  list-size bound.
- `CslibFrontier.HomomorphismCode.exists_bucket_covering`: bucket-splitting lemma for `aHom(G, H)`
  and
  `Hom(G, H)`.
-/

public section

namespace CslibFrontier.HomomorphismCode

open scoped BigOperators

/-! ### Strong Negative Correlation Bound -/

section SNC

variable {α ι : Type*}

/-- A family of subsets `S : ι → Set α` of a finite type `α` is `(ρ, τ)`-strongly negatively
correlated if `μ(S i) ≥ ρ` for all `i` and `μ(S i ∩ S j) ≤ ρ² - τ` for all `i ≠ j`. -/
@[expose]
def IsStronglyNegativelyCorrelated [Fintype α] (S : ι → Set α) (ρ τ : ℝ) : Prop :=
  (∀ i, ρ ≤ density (S i)) ∧ ∀ i j, i ≠ j → density (S i ∩ S j) ≤ ρ ^ 2 - τ

/-- Strong negative correlation bound: any `(ρ, τ)`-strongly negatively correlated finite family
has size at most `1 / (4 τ) + 1`. -/
theorem card_le_of_isStronglyNegativelyCorrelated [Fintype α] [Fintype ι]
    {S : ι → Set α} {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    (hS : IsStronglyNegativelyCorrelated S ρ τ) :
    (Fintype.card ι : ℝ) ≤ 1 / (4 * τ) + 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : (Fintype.card ι : ℝ) = 0 := by simp [Fintype.card_eq_zero]
    rw [h0]
    positivity
  rcases isEmpty_or_nonempty α with hα | hα
  · obtain ⟨i₀⟩ := hι
    have h0 : density (S i₀) = 0 := by
      rw [density_eq_ncard_div]; simp [Fintype.card_eq_zero]
    linarith [hS.1 i₀]
  let n : ℝ := Fintype.card α
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let Z : ι → α → ℝ := fun i x => if x ∈ S i then 1 else 0
  have hEZ : ∀ i, (∑ x : α, Z i x) / n = density (S i) := by
    intro i
    rw [density_eq_ncard_div]
    simp only [Z, Finset.sum_boole, n]
    congr 1
    rw [Set.ncard_eq_toFinset_card']
    congr 2
    ext x
    simp
  have hEZZ : ∀ i j, (∑ x : α, Z i x * Z j x) / n = density (S i ∩ S j) := by
    intro i j
    have hprod : ∀ x : α, Z i x * Z j x = if x ∈ S i ∩ S j then 1 else 0 := by
      intro x
      simp only [Z, Set.mem_inter_iff]
      by_cases h1 : x ∈ S i <;> by_cases h2 : x ∈ S j <;> simp [h1, h2]
    simp_rw [hprod]
    rw [density_eq_ncard_div]
    simp only [Finset.sum_boole, n]
    congr 1
    rw [Set.ncard_eq_toFinset_card']
    congr 2
    ext x
    simp
  let m : ι → ℝ := fun i => density (S i)
  have hvar_nonneg : 0 ≤ (∑ x : α, (∑ i : ι, (Z i x - m i)) ^ 2) / n := by
    apply div_nonneg _ hn.le
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  have hexpand :
      (∑ x : α, (∑ i : ι, (Z i x - m i)) ^ 2) / n =
        ∑ i : ι, m i * (1 - m i) +
          ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (density (S i ∩ S j) - m i * m j) := by
    have hsq : ∀ x : α, (∑ i : ι, (Z i x - m i)) ^ 2 =
        ∑ i : ι, ∑ j : ι, (Z i x - m i) * (Z j x - m j) := by
      intro x
      rw [sq, Finset.sum_mul_sum]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hswap : ∀ i : ι,
        (∑ x : α, ∑ j : ι, (Z i x - m i) * (Z j x - m j)) =
          ∑ j : ι, ∑ x : α, (Z i x - m i) * (Z j x - m j) :=
      fun _ => Finset.sum_comm
    simp_rw [hswap]
    rw [div_eq_mul_inv, Finset.sum_mul]
    simp_rw [← div_eq_mul_inv]
    have hterm : ∀ i : ι,
        (∑ j : ι, ∑ x : α, (Z i x - m i) * (Z j x - m j)) / n =
          m i * (1 - m i) + ∑ j ∈ Finset.univ.erase i, (density (S i ∩ S j) - m i * m j) := by
      intro i
      rw [div_eq_mul_inv, Finset.sum_mul]
      simp_rw [← div_eq_mul_inv]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      congr 1
      · have hdiag : ∀ x : α, (Z i x - m i) * (Z i x - m i) =
            Z i x - 2 * m i * Z i x + m i ^ 2 := by
          intro x
          have hZ2 : Z i x * Z i x = Z i x := by
            simp only [Z]; split_ifs <;> norm_num
          nlinarith [hZ2]
        simp_rw [hdiag, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hEZi := hEZ i
        have hsumZ : ∑ x : α, Z i x = m i * n := by
          have := (div_eq_iff hn.ne').mp hEZi
          exact this
        rw [hsumZ]
        field_simp [hn.ne']
        ring
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hcross : ∀ x : α, (Z i x - m i) * (Z j x - m j) =
            Z i x * Z j x - m i * Z j x - m j * Z i x + m i * m j := by
          intro x; ring
        simp_rw [hcross, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hsumZi : ∑ x : α, Z i x = m i * n := (div_eq_iff hn.ne').mp (hEZ i)
        have hsumZj : ∑ x : α, Z j x = m j * n := (div_eq_iff hn.ne').mp (hEZ j)
        have hsumZZ : ∑ x : α, Z i x * Z j x = density (S i ∩ S j) * n :=
          (div_eq_iff hn.ne').mp (hEZZ i j)
        rw [hsumZi, hsumZj, hsumZZ]
        field_simp [hn.ne']
        ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
  rw [hexpand] at hvar_nonneg
  have hdiag_le : ∑ i : ι, m i * (1 - m i) ≤ (Fintype.card ι : ℝ) / 4 := by
    have h1 : ∀ i : ι, m i * (1 - m i) ≤ 1 / 4 := fun i => by nlinarith [sq_nonneg (m i - 1 / 2)]
    calc
      ∑ i : ι, m i * (1 - m i) ≤ ∑ _i : ι, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
      _ = (Fintype.card ι : ℝ) / 4 := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hoff_le :
      ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (density (S i ∩ S j) - m i * m j) ≤
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * (-τ) := by
    have h2 : ∀ i : ι, ∀ j ∈ Finset.univ.erase i, density (S i ∩ S j) - m i * m j ≤ -τ := by
      intro i j hj
      have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hcov := hS.2 i j hne
      have hmi : ρ ≤ m i := hS.1 i
      have hmj : ρ ≤ m j := hS.1 j
      have hprod : ρ ^ 2 ≤ m i * m j := by nlinarith
      linarith
    calc
      ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (density (S i ∩ S j) - m i * m j)
          ≤ ∑ i : ι, ∑ _j ∈ Finset.univ.erase i, (-τ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => h2 i j hj
      _ = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * (-τ) := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, nsmul_eq_mul]
        have hcard1 : 1 ≤ Fintype.card ι := Fintype.card_pos
        rw [Nat.cast_sub hcard1, Nat.cast_one]
        ring
  have hcomb : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / 4 +
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * (-τ) := by
    linarith
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hdiv : (0 : ℝ) ≤ 1 / 4 - ((Fintype.card ι : ℝ) - 1) * τ := by
    have hmul : (Fintype.card ι : ℝ) * (1 / 4 - ((Fintype.card ι : ℝ) - 1) * τ) =
        (Fintype.card ι : ℝ) / 4 +
          (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * (-τ) := by ring
    nlinarith [hmul, hcomb, hr]
  have hle1 : ((Fintype.card ι : ℝ) - 1) * τ ≤ 1 / 4 := by linarith
  have hle2 : (Fintype.card ι : ℝ) - 1 ≤ (1 / 4) / τ := (le_div_iff₀ hτ).mpr hle1
  have h4 : (1 / 4 : ℝ) / τ = 1 / (4 * τ) := by field_simp [hτ.ne']
  linarith

/-- Strict strong negative correlation bound when `|ι| ≥ 2` and `τ < τ'` (useful for strict
inequalities when slack exists). -/
theorem card_lt_of_isStronglyNegativelyCorrelated_of_lt [Fintype α] [Fintype ι]
    {S : ι → Set α} {ρ τ τ' : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) (hτ' : τ < τ')
    (hS : IsStronglyNegativelyCorrelated S ρ τ') :
    (Fintype.card ι : ℝ) < 1 / (4 * τ) + 1 := by
  have hle := card_le_of_isStronglyNegativelyCorrelated hρ (hτ.trans hτ') hS
  have hlt : 1 / (4 * τ') < 1 / (4 * τ) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- General code SNC list-size bound: for any code `C` with maximum agreement `Λ` and any
`√Λ < ρ ≤ 1` (equivalently `Λ < ρ²`), `ℓ(C, ρ) ≤ 1 / (4 (ρ² - Λ)) + 1`. -/
theorem maxListSize_le_of_sqrt_codeMaxAgreement_lt {α β : Type*} [Fintype α]
    (C : Set (α → β)) {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ : codeMaxAgreement C < ρ ^ 2) :
    maxListSize C ρ ≤ (Nat.floor (1 / (4 * (ρ ^ 2 - codeMaxAgreement C)) + 1) : ℕ∞) := by
  classical
  let τ : ℝ := ρ ^ 2 - codeMaxAgreement C
  have hτ : 0 < τ := sub_pos.mpr hρ
  rw [maxListSize_le_floor_iff C ρ (by positivity)]
  intro f B hB
  have hSNC : IsStronglyNegativelyCorrelated (fun w : B => equalizer f w.1) ρ τ := by
    constructor
    · intro w
      rw [← agreement_eq_density_equalizer, agreement_comm]
      exact (hB w.2).2
    · intro w₁ w₂ hne
      have hne' : w₁.1 ≠ w₂.1 := fun h => hne (Subtype.ext h)
      have hsub : equalizer f w₁.1 ∩ equalizer f w₂.1 ⊆ equalizer w₁.1 w₂.1 := by
        intro x hx
        exact hx.1.symm.trans hx.2
      have hle1 : density (equalizer f w₁.1 ∩ equalizer f w₂.1) ≤ agreement w₁.1 w₂.1 :=
        density_mono hsub
      have hle2 : agreement w₁.1 w₂.1 ≤ codeMaxAgreement C :=
        agreement_le_codeMaxAgreement (hB w₁.2).1 (hB w₂.2).1 hne'
      linarith
  have h := card_le_of_isStronglyNegativelyCorrelated hρ_pos hτ hSNC
  simpa only [Fintype.card_coe] using h

end SNC

/-! ### Sphere Packing, Large `ε`, and Bucket Splitting -/

section SpherePacking

variable {G H : Type*} [Group G] [Fintype G] [Group H]

/-- Sphere packing bound for homomorphism codes (and general codes): any subset `Ψ` of
`L(aHom(G, H), f, Λ + ε)` whose distinct elements have pairwise agreement at most `Λ²` has
cardinality at most `1 / (4 (Λ + ε) ε) + 1`. -/
theorem card_le_sphere_packing_finset (f : G → H) {ε : ℝ} (hε : 0 < ε)
    {Ψ : Finset (G → H)}
    (hΨ_sub : (Ψ : Set (G → H)) ⊆ codeListAgr (aHomCode G H) f (homMaxAgreement G H + ε))
    (hΨ_pair : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ψ₁ ≠ ψ₂ →
      agreement ψ₁ ψ₂ ≤ (homMaxAgreement G H) ^ 2) :
    (Ψ.card : ℝ) ≤ 1 / (4 * (homMaxAgreement G H + ε) * ε) + 1 := by
  let Λ := homMaxAgreement G H
  have hΛ : 0 ≤ Λ := codeMaxAgreement_nonneg _
  have hρ : 0 < Λ + ε := by linarith
  have hτ : 0 < (Λ + ε) * ε := mul_pos hρ hε
  have hSNC : IsStronglyNegativelyCorrelated (fun ψ : Ψ => equalizer f ψ.1) (Λ + ε)
      ((Λ + ε) * ε) := by
    constructor
    · intro ψ
      rw [← agreement_eq_density_equalizer, agreement_comm]
      exact (hΨ_sub ψ.2).2
    · intro ψ₁ ψ₂ hne
      have hne' : ψ₁.1 ≠ ψ₂.1 := fun h => hne (Subtype.ext h)
      have hle1 : density (equalizer f ψ₁.1 ∩ equalizer f ψ₂.1) ≤ agreement ψ₁.1 ψ₂.1 :=
        density_mono (fun x hx => hx.1.symm.trans hx.2)
      have hle2 : agreement ψ₁.1 ψ₂.1 ≤ Λ ^ 2 := hΨ_pair ψ₁.1 ψ₁.2 ψ₂.1 ψ₂.2 hne'
      have hgap : Λ ^ 2 ≤ (Λ + ε) ^ 2 - (Λ + ε) * ε := by nlinarith
      linarith
  have h := card_le_of_isStronglyNegativelyCorrelated hρ hτ hSNC
  simpa only [Fintype.card_coe, mul_assoc] using h

/-- Strict sphere packing bound when `Λ > 0` and `Ψ` has at least `2` elements. -/
theorem card_lt_sphere_packing_finset_of_pos (f : G → H) {ε : ℝ} (hε : 0 < ε)
    (hΛ_pos : 0 < homMaxAgreement G H) {Ψ : Finset (G → H)}
    (hΨ_sub : (Ψ : Set (G → H)) ⊆ codeListAgr (aHomCode G H) f (homMaxAgreement G H + ε))
    (hΨ_pair : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ψ₁ ≠ ψ₂ →
      agreement ψ₁ ψ₂ ≤ (homMaxAgreement G H) ^ 2) :
    (Ψ.card : ℝ) < 1 / (4 * (homMaxAgreement G H + ε) * ε) + 1 := by
  let Λ := homMaxAgreement G H
  have hρ : 0 < Λ + ε := by linarith
  have hτ : 0 < (Λ + ε) * ε := mul_pos hρ hε
  have hτ' : (Λ + ε) * ε < 2 * Λ * ε + ε ^ 2 := by nlinarith
  have hSNC : IsStronglyNegativelyCorrelated (fun ψ : Ψ => equalizer f ψ.1) (Λ + ε)
      (2 * Λ * ε + ε ^ 2) := by
    constructor
    · intro ψ
      rw [← agreement_eq_density_equalizer, agreement_comm]
      exact (hΨ_sub ψ.2).2
    · intro ψ₁ ψ₂ hne
      have hne' : ψ₁.1 ≠ ψ₂.1 := fun h => hne (Subtype.ext h)
      have hle1 : density (equalizer f ψ₁.1 ∩ equalizer f ψ₂.1) ≤ agreement ψ₁.1 ψ₂.1 :=
        density_mono (fun x hx => hx.1.symm.trans hx.2)
      have hle2 : agreement ψ₁.1 ψ₂.1 ≤ Λ ^ 2 := hΨ_pair ψ₁.1 ψ₁.2 ψ₂.1 ψ₂.2 hne'
      have hgap : Λ ^ 2 = (Λ + ε) ^ 2 - (2 * Λ * ε + ε ^ 2) := by ring
      linarith
  have h := card_lt_of_isStronglyNegativelyCorrelated_of_lt hρ hτ hτ' hSNC
  simpa only [Fintype.card_coe, mul_assoc] using h

/-- Sphere packing bound for a subset `Ψ` (possibly in an infinite codomain `H`). -/
theorem encard_le_sphere_packing (f : G → H) {ε : ℝ} (hε : 0 < ε)
    {Ψ : Set (G → H)}
    (hΨ_sub : Ψ ⊆ codeListAgr (aHomCode G H) f (homMaxAgreement G H + ε))
    (hΨ_pair : ∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ψ₁ ≠ ψ₂ →
      agreement ψ₁ ψ₂ ≤ (homMaxAgreement G H) ^ 2) :
    Ψ.encard ≤ (Nat.floor (1 / (4 * (homMaxAgreement G H + ε) * ε) + 1) : ℕ∞) := by
  have hΛ : 0 ≤ homMaxAgreement G H := codeMaxAgreement_nonneg _
  rw [encard_le_floor_iff (by positivity)]
  intro t ht
  exact card_le_sphere_packing_finset f hε (ht.trans hΨ_sub)
    (fun ψ₁ h₁ ψ₂ h₂ => hΨ_pair ψ₁ (ht h₁) ψ₂ (ht h₂))

/-- Large-`ε` lemma: if `Λ_{G, H} ≤ ε² / 2`, then
`ℓ(aHom(G, H), Λ_{G, H} + ε) ≤ 1 / (2 ε²) + 1`. -/
theorem maxListSize_le_of_homMaxAgreement_le_half_sq {ε : ℝ} (hε : 0 < ε)
    (hΛ : homMaxAgreement G H ≤ ε ^ 2 / 2) :
    maxListSize (aHomCode G H) (homMaxAgreement G H + ε) ≤
      (Nat.floor (1 / (2 * ε ^ 2) + 1) : ℕ∞) := by
  let Λ := homMaxAgreement G H
  have hΛ0 : 0 ≤ Λ := codeMaxAgreement_nonneg _
  have hlt : Λ < (Λ + ε) ^ 2 := by nlinarith
  have h1 := maxListSize_le_of_sqrt_codeMaxAgreement_lt (aHomCode G H) (by linarith) hlt
  refine h1.trans (Nat.cast_le.mpr (Nat.floor_mono ?_))
  have hden : ε ^ 2 / 2 ≤ (Λ + ε) ^ 2 - Λ := by nlinarith
  have h4 : 4 * (ε ^ 2 / 2) = 2 * ε ^ 2 := by ring
  have hle : 1 / (4 * ((Λ + ε) ^ 2 - Λ)) ≤ 1 / (2 * ε ^ 2) := by
    rw [← h4]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  dsimp only [Λ] at hle ⊢
  rw [homMaxAgreement_eq_codeMaxAgreement] at hle ⊢
  linarith

/-- The bucket `L_ψ = {φ ∈ L | agr(φ, ψ) > Λ²}` for a code `C` and center `ψ`. -/
@[expose]
def bucket (C : Set (G → H)) (f : G → H) (ε : ℝ) (ψ : G → H) : Set (G → H) :=
  {φ ∈ codeListAgr C f (homMaxAgreement G H + ε) | (homMaxAgreement G H) ^ 2 < agreement φ ψ}

/-- Bucket-splitting lemma: for any subcode `C ⊆ aHom(G, H)` (in particular `aHom(G, H)` or
`Hom(G, H)`), received word `f`, and `ε > 0`, there is a finite set `Ψ ⊆ L(C, f, Λ + ε)` of size
at most `1 / (4 (Λ + ε) ε) + 1` whose buckets cover `L(C, f, Λ + ε)`. -/
theorem exists_bucket_covering {C : Set (G → H)} (hC : C ⊆ aHomCode G H) (f : G → H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : Finset (G → H),
      (Ψ : Set (G → H)) ⊆ codeListAgr C f (homMaxAgreement G H + ε) ∧
      (∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ψ₁ ≠ ψ₂ → agreement ψ₁ ψ₂ ≤ (homMaxAgreement G H) ^ 2) ∧
      (Ψ.card : ℝ) ≤ 1 / (4 * (homMaxAgreement G H + ε) * ε) + 1 ∧
      codeListAgr C f (homMaxAgreement G H + ε) ⊆ ⋃ ψ ∈ Ψ, bucket C f ε ψ := by
  classical
  let L := codeListAgr C f (homMaxAgreement G H + ε)
  let Λ := homMaxAgreement G H
  let B : ℕ := Nat.floor (1 / (4 * (Λ + ε) * ε) + 1)
  have hcard_le : ∀ Ψ : Finset (G → H), (Ψ : Set (G → H)) ⊆ L →
      (∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ψ₁ ≠ ψ₂ → agreement ψ₁ ψ₂ ≤ Λ ^ 2) →
      Ψ.card ≤ B := by
    intro Ψ hsub hpair
    have hsub' : (Ψ : Set (G → H)) ⊆ codeListAgr (aHomCode G H) f (Λ + ε) :=
      hsub.trans fun w hw => ⟨hC hw.1, hw.2⟩
    exact Nat.le_floor (card_le_sphere_packing_finset f hε hsub' hpair)
  let P : ℕ → Prop := fun k => ∃ Ψ : Finset (G → H),
    (Ψ : Set (G → H)) ⊆ L ∧
    (∀ ψ₁ ∈ Ψ, ∀ ψ₂ ∈ Ψ, ψ₁ ≠ ψ₂ → agreement ψ₁ ψ₂ ≤ Λ ^ 2) ∧
    Ψ.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  have hPmax : ∃ k ≤ B, P k ∧ ∀ m, P m → m ≤ k := by
    let S : Finset ℕ := (Finset.range (B + 1)).filter (fun k => P k)
    have hSne : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP0⟩⟩
    obtain ⟨k, hkS, hkmax⟩ := S.exists_max_image id hSne
    have hkP : P k := (Finset.mem_filter.mp hkS).2
    have hkB : k ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hkS).1)
    refine ⟨k, hkB, hkP, fun m hm => ?_⟩
    obtain ⟨Ψ, hsub, hpair, rfl⟩ := hm
    have hmB : Ψ.card ≤ B := hcard_le Ψ hsub hpair
    exact hkmax Ψ.card (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      ⟨Ψ, hsub, hpair, rfl⟩⟩)
  obtain ⟨k, -, ⟨Ψ, hΨsub, hΨpair, rfl⟩, hmax⟩ := hPmax
  refine ⟨Ψ, hΨsub, hΨpair, ?_, ?_⟩
  · have hsub' : (Ψ : Set (G → H)) ⊆ codeListAgr (aHomCode G H) f (Λ + ε) :=
      hΨsub.trans fun w hw => ⟨hC hw.1, hw.2⟩
    exact card_le_sphere_packing_finset f hε hsub' hΨpair
  · intro φ hφ
    by_contra hnot
    simp only [Set.mem_iUnion, bucket, Set.mem_sep_iff, not_exists, not_and] at hnot
    have hφ_notmem : φ ∉ Ψ := by
      intro hmem
      have hgt : Λ ^ 2 < agreement φ φ := by
        rw [agreement_self]
        have hlt1 : Λ < 1 := homMaxAgreement_lt_one
        have hΛ0 : 0 ≤ Λ := codeMaxAgreement_nonneg _
        nlinarith
      exact not_lt_of_ge (by
        have := hnot φ hmem hφ
        linarith) hgt
    let Ψ' := insert φ Ψ
    have hΨ'sub : (Ψ' : Set (G → H)) ⊆ L := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact hφ
      · exact hΨsub hw'
    have hΨ'pair : ∀ ψ₁ ∈ Ψ', ∀ ψ₂ ∈ Ψ', ψ₁ ≠ ψ₂ → agreement ψ₁ ψ₂ ≤ Λ ^ 2 := by
      intro ψ₁ h₁ ψ₂ h₂ hne
      rcases Finset.mem_insert.mp h₁ with rfl | h₁' <;>
        rcases Finset.mem_insert.mp h₂ with rfl | h₂'
      · exact absurd rfl hne
      · exact not_lt.mp (hnot ψ₂ h₂' hφ)
      · rw [agreement_comm]
        exact not_lt.mp (hnot ψ₁ h₁' hφ)
      · exact hΨpair ψ₁ h₁' ψ₂ h₂' hne
    have hle := hmax Ψ'.card ⟨Ψ', hΨ'sub, hΨ'pair, rfl⟩
    rw [Finset.card_insert_of_notMem hφ_notmem] at hle
    omega

end SpherePacking

end CslibFrontier.HomomorphismCode
