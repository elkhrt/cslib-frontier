module

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Slice rank of order-three tensors and diagonal support bounds

An order-three tensor `T : Cslib.Tensor K X Y Z` over a semiring `K` has *slice rank* at most `r`
(`HasSliceRank r T`) when `T` decomposes as a sum of `rX` `X`-slices, `rY` `Y`-slices, and `rZ`
`Z`-slices with `rX + rY + rZ = r`, where each slice factors as a function of one leg multiplied by
a function of the complementary two legs. The *slice rank* `sliceRank T` is the minimum such `r`.

Slice rank is bounded above by the cardinality of each leg (`hasSliceRank_card_X`) and is monotone
under bilinear restrictions (`sliceRank_le_of_isRestriction`). Over any field `K`, if `D` is a
diagonal (independent) tensor—meaning any two nonzero entries of `D` that share a coordinate in any
single leg coincide in all three legs (`IsDiagonalTensor D`)—then the support cardinality
`supportCard D` is bounded above by `sliceRank D` (`supportCard_le_sliceRank_of_isDiagonalTensor`),
and in particular the unit tensor `Cslib.Tensor.unit n` over a field has slice rank equal to `n`
(`sliceRank_unit`).

## Main definitions

* `CslibFrontier.Foundations.LinearAlgebra.Tensor.HasSliceRank`: predicate that an order-three
  tensor decomposes into `r` coordinate slices.
* `CslibFrontier.Foundations.LinearAlgebra.Tensor.sliceRank`: minimum slice-decomposition size of a
  finite order-three tensor.
* `CslibFrontier.Foundations.LinearAlgebra.Tensor.tensorSupport`, `supportCard`: finite support and
  support cardinality of an order-three tensor.
* `CslibFrontier.Foundations.LinearAlgebra.Tensor.IsDiagonalTensor`: pairwise leg-disjointness of
  distinct nonzero entries of an order-three tensor.

## Main results

* `CslibFrontier.Foundations.LinearAlgebra.Tensor.hasSliceRank_card_X`,
  `hasSliceRank_sliceRank`, `sliceRank_le_of_hasSliceRank`: existence and minimality of slice rank.
* `CslibFrontier.Foundations.LinearAlgebra.Tensor.sliceRank_le_of_isRestriction`: monotonicity of
  slice rank under tensor restrictions.
* `CslibFrontier.Foundations.LinearAlgebra.Tensor.supportCard_le_sliceRank_of_isDiagonalTensor`:
  hyperplane-contraction lower bound `supportCard D ≤ sliceRank D` for diagonal tensors over any
  field.
* `CslibFrontier.Foundations.LinearAlgebra.Tensor.sliceRank_unit`: exact slice rank
  `sliceRank (Cslib.Tensor.unit n) = n` over any field.
-/

public section

namespace CslibFrontier.Foundations.LinearAlgebra.Tensor

open Cslib Finset
open scoped BigOperators

variable {K X Y Z X' Y' Z' : Type*}

/-- An order-three tensor `T` has slice rank at most `r` if `T` decomposes into `rX` `X`-slices,
`rY` `Y`-slices, and `rZ` `Z`-slices with `rX + rY + rZ = r`. -/
def HasSliceRank [Semiring K] (r : ℕ) (T : Tensor K X Y Z) : Prop :=
  ∃ rX rY rZ : ℕ, rX + rY + rZ = r ∧
    ∃ (uX : Fin rX → X → K) (MX : Fin rX → Y → Z → K)
      (uY : Fin rY → Y → K) (MY : Fin rY → X → Z → K)
      (uZ : Fin rZ → Z → K) (MZ : Fin rZ → X → Y → K),
      ∀ x y z, T x y z =
        (∑ i : Fin rX, uX i x * MX i y z) +
        (∑ j : Fin rY, uY j y * MY j x z) +
        (∑ k : Fin rZ, uZ k z * MZ k x y)

/-- Explicit characterization of `HasSliceRank`. -/
theorem hasSliceRank_iff [Semiring K] {r : ℕ} {T : Tensor K X Y Z} :
    HasSliceRank r T ↔
      ∃ rX rY rZ : ℕ, rX + rY + rZ = r ∧
        ∃ (uX : Fin rX → X → K) (MX : Fin rX → Y → Z → K)
          (uY : Fin rY → Y → K) (MY : Fin rY → X → Z → K)
          (uZ : Fin rZ → Z → K) (MZ : Fin rZ → X → Y → K),
          ∀ x y z, T x y z =
            (∑ i : Fin rX, uX i x * MX i y z) +
            (∑ j : Fin rY, uY j y * MY j x z) +
            (∑ k : Fin rZ, uZ k z * MZ k x y) := by
  rfl

/-- Every finite order-three tensor `T` has slice rank at most `Fintype.card X` via coordinate
`X`-slices. -/
theorem hasSliceRank_card_X [Semiring K] [Fintype X] (T : Tensor K X Y Z) :
    HasSliceRank (Fintype.card X) T := by
  classical
  let e := Fintype.equivFin X
  refine ⟨Fintype.card X, 0, 0, by omega,
    fun i x ↦ if e x = i then 1 else 0,
    fun i y z ↦ T (e.symm i) y z,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro x y z
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [Fintype.sum_eq_single (e x) (fun i hi ↦ by simp [hi.symm])]
  simp

/-- The slice rank of a finite order-three tensor `T`, defined as the least `r` satisfying
`HasSliceRank r T`. -/
noncomputable def sliceRank [Semiring K] (T : Tensor K X Y Z) : ℕ :=
  sInf {r : ℕ | HasSliceRank r T}

/-- Every finite order-three tensor achieves its slice rank. -/
theorem hasSliceRank_sliceRank [Semiring K] [Finite X] (T : Tensor K X Y Z) :
    HasSliceRank (sliceRank T) T := by
  cases nonempty_fintype X
  have hne : {r : ℕ | HasSliceRank r T}.Nonempty := ⟨Fintype.card X, hasSliceRank_card_X T⟩
  exact Nat.sInf_mem hne

/-- Any slice decomposition of size `r` bounds `sliceRank T` from above. -/
theorem sliceRank_le_of_hasSliceRank [Semiring K]
    {r : ℕ} {T : Tensor K X Y Z} (h : HasSliceRank r T) :
    sliceRank T ≤ r :=
  Nat.sInf_le h

/-- Slice rank is monotone under bilinear restrictions `Tensor.IsRestriction A B`. -/
theorem sliceRank_le_of_isRestriction [CommSemiring K]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {A : Tensor K X Y Z} {B : Tensor K X' Y' Z'} (hres : Tensor.IsRestriction A B) :
    sliceRank A ≤ sliceRank B := by
  obtain ⟨α, β, γ, rfl⟩ := hres
  obtain ⟨rX, rY, rZ, hr, uX, MX, uY, MY, uZ, MZ, hB⟩ :=
    hasSliceRank_iff.1 (hasSliceRank_sliceRank B)
  refine sliceRank_le_of_hasSliceRank ⟨rX, rY, rZ, hr,
    fun i x ↦ ∑ x' : X', α x' x * uX i x',
    fun i y z ↦ ∑ y' : Y', ∑ z' : Z', β y' y * γ z z' * MX i y' z',
    fun j y ↦ ∑ y' : Y', β y' y * uY j y',
    fun j x z ↦ ∑ x' : X', ∑ z' : Z', α x' x * γ z z' * MY j x' z',
    fun k z ↦ ∑ z' : Z', γ z z' * uZ k z',
    fun k x y ↦ ∑ x' : X', ∑ y' : Y', α x' x * β y' y * MZ k x' y', ?_⟩
  intro x y z
  simp only [Tensor.restrict, hB]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · symm
      calc ∑ i : Fin rX, (∑ x' : X', α x' x * uX i x') *
              ∑ y' : Y', ∑ z' : Z', β y' y * γ z z' * MX i y' z'
          = ∑ i : Fin rX, ∑ x' : X', ∑ y' : Y', ∑ z' : Z',
              α x' x * β y' y * γ z z' * (uX i x' * MX i y' z') := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun x' _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y' _ ↦ ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z' _ ↦ by ring
        _ = ∑ x' : X', ∑ y' : Y', ∑ z' : Z',
              α x' x * β y' y * γ z z' * ∑ i : Fin rX, uX i x' * MX i y' z' := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ ↦ ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y' _ ↦ ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z' _ ↦ ?_
            rw [Finset.mul_sum]
    · symm
      calc ∑ j : Fin rY, (∑ y' : Y', β y' y * uY j y') *
              ∑ x' : X', ∑ z' : Z', α x' x * γ z z' * MY j x' z'
          = ∑ j : Fin rY, ∑ x' : X', ∑ y' : Y', ∑ z' : Z',
              α x' x * β y' y * γ z z' * (uY j y' * MY j x' z') := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ ↦ Finset.sum_congr rfl fun y' _ ↦
              Finset.sum_congr rfl fun z' _ ↦ by ring
        _ = ∑ x' : X', ∑ y' : Y', ∑ z' : Z',
              α x' x * β y' y * γ z z' * ∑ j : Fin rY, uY j y' * MY j x' z' := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ ↦ ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y' _ ↦ ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z' _ ↦ ?_
            rw [Finset.mul_sum]
  · symm
    calc ∑ k : Fin rZ, (∑ z' : Z', γ z z' * uZ k z') *
            ∑ x' : X', ∑ y' : Y', α x' x * β y' y * MZ k x' y'
        = ∑ k : Fin rZ, ∑ x' : X', ∑ y' : Y', ∑ z' : Z',
            α x' x * β y' y * γ z z' * (uZ k z' * MZ k x' y') := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x' _ ↦ ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y' _ ↦ Finset.sum_congr rfl fun z' _ ↦ by ring
      _ = ∑ x' : X', ∑ y' : Y', ∑ z' : Z',
            α x' x * β y' y * γ z z' * ∑ k : Fin rZ, uZ k z' * MZ k x' y' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x' _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y' _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z' _ ↦ ?_
          rw [Finset.mul_sum]

/-- Finite support `{(x, y, z) | T x y z ≠ 0}` of an order-three tensor. -/
noncomputable def tensorSupport [Zero K] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Finset (X × Y × Z) := by
  classical
  exact Finset.univ.filter fun p ↦ T p.1 p.2.1 p.2.2 ≠ 0

/-- Membership in `tensorSupport T` holds iff the corresponding entry of `T` is nonzero. -/
@[simp]
theorem mem_tensorSupport [Zero K] [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {p : X × Y × Z} :
    p ∈ tensorSupport T ↔ T p.1 p.2.1 p.2.2 ≠ 0 := by
  classical
  simp [tensorSupport]

/-- Number of nonzero entries of a finite order-three tensor `T`. -/
noncomputable def supportCard [Zero K] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ :=
  #(tensorSupport T)

/-- Unfolding equation `supportCard T = #(tensorSupport T)`. -/
theorem supportCard_eq_card_tensorSupport [Zero K] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) :
    supportCard T = #(tensorSupport T) := by
  rfl

/-- An order-three tensor `D` is *diagonal* (or *independent*) if any two nonzero entries that agree
in any one coordinate agree in all three coordinates. -/
def IsDiagonalTensor [Zero K] (D : Tensor K X Y Z) : Prop :=
  ∀ ⦃x₁ x₂ : X⦄ ⦃y₁ y₂ : Y⦄ ⦃z₁ z₂ : Z⦄,
    D x₁ y₁ z₁ ≠ 0 → D x₂ y₂ z₂ ≠ 0 →
      (x₁ = x₂ → y₁ = y₂ ∧ z₁ = z₂) ∧
      (y₁ = y₂ → x₁ = x₂ ∧ z₁ = z₂) ∧
      (z₁ = z₂ → x₁ = x₂ ∧ y₁ = y₂)

/-- Explicit characterization of `IsDiagonalTensor`. -/
theorem isDiagonalTensor_iff [Zero K] {D : Tensor K X Y Z} :
    IsDiagonalTensor D ↔
      ∀ ⦃x₁ x₂ : X⦄ ⦃y₁ y₂ : Y⦄ ⦃z₁ z₂ : Z⦄,
        D x₁ y₁ z₁ ≠ 0 → D x₂ y₂ z₂ ≠ 0 →
          (x₁ = x₂ → y₁ = y₂ ∧ z₁ = z₂) ∧
          (y₁ = y₂ → x₁ = x₂ ∧ z₁ = z₂) ∧
          (z₁ = z₂ → x₁ = x₂ ∧ y₁ = y₂) := by
  rfl

private theorem finrank_injective_card_le {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (L : (α → K) →ₗ[K] (β → K)) (hL : Function.Injective L) :
    Fintype.card α ≤ Fintype.card β := by
  have hle := LinearMap.finrank_le_finrank_of_injective hL
  simpa [Module.finrank_pi] using hle

/-- Over any field `K`, the support cardinality of a diagonal tensor `D` is at most its slice rank.
-/
theorem supportCard_le_sliceRank_of_isDiagonalTensor [Field K]
    [Fintype X] [Fintype Y] [Fintype Z] {D : Tensor K X Y Z} (hI : IsDiagonalTensor D) :
    supportCard D ≤ sliceRank D := by
  classical
  obtain ⟨rX, rY, rZ, hr, uX, MX, uY, MY, uZ, MZ, hD_eq⟩ :=
    hasSliceRank_iff.1 (hasSliceRank_sliceRank D)
  set S := tensorSupport D
  let Φ : (S → K) →ₗ[K] (Fin rZ → K) :=
    { toFun := fun φ k ↦ ∑ t : S, φ t * uZ k t.1.2.2
      map_add' := fun φ₁ φ₂ ↦ funext fun k ↦ by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c φ ↦ funext fun k ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  let suppSizes : Set ℕ :=
    {m : ℕ | ∃ φ : S → K, Φ φ = 0 ∧ #(Finset.univ.filter fun t : S ↦ φ t ≠ 0) = m}
  have hsupp_ne : suppSizes.Nonempty := ⟨0, 0, map_zero Φ, by simp⟩
  have hsupp_bdd : BddAbove suppSizes :=
    ⟨Fintype.card S, by rintro _ ⟨φ, _, rfl⟩; exact Finset.card_le_univ _⟩
  obtain ⟨φ, hΦφ, hφ_max_eq⟩ := Nat.sSup_mem hsupp_ne hsupp_bdd
  let U_pos : Finset S := Finset.univ.filter fun t : S ↦ φ t ≠ 0
  let U_zero : Finset S := Finset.univ.filter fun t : S ↦ φ t = 0
  have hpart_S : #U_pos + #U_zero = Fintype.card S := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset S)) (p := fun t : S ↦ φ t ≠ 0)
    simpa [U_pos, U_zero] using h
  have hU_zero_le : #U_zero ≤ rZ := by
    by_contra! hgt
    let Ψ : (U_zero → K) →ₗ[K] (Fin rZ → K) :=
      { toFun := fun g ↦ Φ (fun t : S ↦ if ht : t ∈ U_zero then g ⟨t, ht⟩ else 0)
        map_add' := fun g₁ g₂ ↦ by
          rw [← map_add]
          congr 1
          funext t
          by_cases ht : t ∈ U_zero <;> simp [ht]
        map_smul' := fun c g ↦ by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext t
          by_cases ht : t ∈ U_zero <;> simp [ht] }
    have hnot_inj : ¬ Function.Injective Ψ := by
      intro hinj
      have hcard := finrank_injective_card_le Ψ hinj
      simp only [Fintype.card_coe, Fintype.card_fin] at hcard
      exact hgt.not_ge hcard
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hnot_inj
    push Not at hnot_inj
    obtain ⟨g, hg_ker, hg_ne⟩ := hnot_inj
    have hex_t0 : ∃ t₀ : U_zero, g t₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hg_ne (funext hall)
    obtain ⟨t₀, ht₀⟩ := hex_t0
    let φ' : S → K := fun t ↦ φ t + if ht : t ∈ U_zero then g ⟨t, ht⟩ else 0
    have hΦφ' : Φ φ' = 0 := by
      have hadd : φ' = φ + (fun t : S ↦ if ht : t ∈ U_zero then g ⟨t, ht⟩ else 0) := rfl
      rw [hadd, map_add, hΦφ, zero_add]
      exact hg_ker
    let U_pos' : Finset S := Finset.univ.filter fun t : S ↦ φ' t ≠ 0
    have hsub_strict : Insert.insert t₀.1 U_pos ⊆ U_pos' := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht_pos
      · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        have hφ0 : φ t₀.1 = 0 := (Finset.mem_filter.1 t₀.2).2
        simp [φ', t₀.2, hφ0, ht₀]
      · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        have hφ_ne : φ t ≠ 0 := (Finset.mem_filter.1 ht_pos).2
        have ht_not : t ∉ U_zero := by simp [U_zero, hφ_ne]
        simp [φ', ht_not, hφ_ne]
    have ht₀_not : t₀.1 ∉ U_pos := by
      have hφ0 : φ t₀.1 = 0 := (Finset.mem_filter.1 t₀.2).2
      simp [U_pos, hφ0]
    have hcard_gt : #U_pos < #U_pos' := by
      calc #U_pos
          < #(Insert.insert t₀.1 U_pos) := by rw [Finset.card_insert_of_notMem ht₀_not]; omega
        _ ≤ #U_pos' := Finset.card_le_card hsub_strict
    have hle_sup : #U_pos' ≤ sSup suppSizes :=
      le_csSup hsupp_bdd ⟨φ', hΦφ', rfl⟩
    dsimp only [U_pos] at hcard_gt
    rw [hφ_max_eq] at hcard_gt
    exact hle_sup.not_gt hcard_gt
  have hinjZ : Function.Injective (fun t : S ↦ t.1.2.2) := by
    intro t₁ t₂ hz
    obtain ⟨hx, hy⟩ :=
      ((isDiagonalTensor_iff.1 hI) (mem_tensorSupport.1 t₁.2) (mem_tensorSupport.1 t₂.2)).2.2 hz
    exact Subtype.ext (Prod.ext hx (Prod.ext hy hz))
  let h : Z → K := fun z ↦
    if hz : ∃ t : S, t.1.2.2 = z then φ (Classical.choose hz) else 0
  have hh_apply : ∀ t : S, h t.1.2.2 = φ t := by
    intro t
    have hex : ∃ t' : S, t'.1.2.2 = t.1.2.2 := ⟨t, rfl⟩
    dsimp only [h]
    rw [dite_eq_left_of_eq_true (eq_true hex), hinjZ (Classical.choose_spec hex)]
  have hh_orth : ∀ k : Fin rZ, ∑ z : Z, h z * uZ k z = 0 := by
    intro k
    have hsum_eq : ∑ z : Z, h z * uZ k z = ∑ t : S, φ t * uZ k t.1.2.2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun t : S ↦ t.1.2.2))]
      · rw [Finset.sum_image (fun t₁ _ t₂ _ hz ↦ hinjZ hz)]
        exact Finset.sum_congr rfl fun t _ ↦ by rw [hh_apply t]
      · intro z _ hz_not
        have hno : ¬ ∃ t : S, t.1.2.2 = z := fun ⟨t, htz⟩ ↦
          hz_not (Finset.mem_image.2 ⟨t, Finset.mem_univ t, htz⟩)
        dsimp only [h]
        split_ifs
        exact zero_mul _
    rw [hsum_eq]
    exact congrFun hΦφ k
  let B_mat : X → Y → K := fun x y ↦ ∑ z : Z, h z * D x y z
  have hB_diag : ∀ t₁ t₂ : U_pos,
      B_mat t₁.1.1.1 t₂.1.1.2.1 =
        if t₁ = t₂ then φ t₁.1 * D t₁.1.1.1 t₁.1.1.2.1 t₁.1.1.2.2 else 0 := by
    intro t₁ t₂
    dsimp only [B_mat]
    by_cases heq : t₁ = t₂
    · subst heq
      simp only [↓reduceIte]
      rw [Fintype.sum_eq_single t₁.1.1.2.2]
      · rw [hh_apply t₁.1]
      · intro z hz
        have hD0 : D t₁.1.1.1 t₁.1.1.2.1 z = 0 := by
          by_contra hne
          obtain ⟨_, hzeq⟩ :=
            ((isDiagonalTensor_iff.1 hI) hne (mem_tensorSupport.1 t₁.1.2)).1 rfl
          exact hz hzeq
        simp [hD0]
    · simp only [heq, ↓reduceIte]
      refine Finset.sum_eq_zero fun z _ ↦ ?_
      have hD0 : D t₁.1.1.1 t₂.1.1.2.1 z = 0 := by
        by_contra hne
        obtain ⟨hy_eq, hz_eq⟩ :=
          ((isDiagonalTensor_iff.1 hI) hne (mem_tensorSupport.1 t₁.1.2)).1 rfl
        obtain ⟨hx_eq, hz_eq2⟩ :=
          ((isDiagonalTensor_iff.1 hI) hne (mem_tensorSupport.1 t₂.1.2)).2.1 rfl
        have ht12 : t₁.1 = t₂.1 :=
          Subtype.ext (Prod.ext hx_eq (Prod.ext hy_eq.symm (hz_eq.symm.trans hz_eq2)))
        exact heq (Subtype.ext ht12)
      simp [hD0]
  have hB_slice : ∀ x y,
      B_mat x y =
        (∑ i : Fin rX, uX i x * (∑ z : Z, h z * MX i y z)) +
        (∑ j : Fin rY, (∑ z : Z, h z * MY j x z) * uY j y) := by
    intro x y
    dsimp only [B_mat]
    simp_rw [hD_eq, mul_add, Finset.sum_add_distrib]
    have hz0 : ∑ z : Z, h z * ∑ k : Fin rZ, uZ k z * MZ k x y = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      have h1 : (∑ z : Z, h z * (uZ k z * MZ k x y)) =
          (∑ z : Z, h z * uZ k z) * MZ k x y := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun z _ ↦ by ring
      rw [h1, hh_orth k, zero_mul]
    rw [hz0, add_zero]
    congr 1
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun z _ ↦ by ring
    · simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun z _ ↦ by ring
  let L₁ : (U_pos → K) →ₗ[K] (Fin rX ⊕ Fin rY → K) :=
    { toFun := fun w s ↦
        match s with
        | Sum.inl i => ∑ t₁ : U_pos, w t₁ * uX i t₁.1.1.1
        | Sum.inr j => ∑ t₁ : U_pos, w t₁ * (∑ z : Z, h z * MY j t₁.1.1.1 z)
      map_add' := fun w₁ w₂ ↦ funext fun s ↦ by
        cases s <;> simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c w ↦ funext fun s ↦ by
        cases s <;> simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hL₁_inj : Function.Injective L₁ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    funext t₂
    have hdiag_sum : ∑ t₁ : U_pos, w t₁ * B_mat t₁.1.1.1 t₂.1.1.2.1 = 0 := by
      simp_rw [hB_slice, mul_add, Finset.sum_add_distrib]
      have hsX : ∑ t₁ : U_pos, w t₁ *
          ∑ i : Fin rX, uX i t₁.1.1.1 * (∑ z : Z, h z * MX i t₂.1.1.2.1 z) = 0 := by
        have hdist : ∀ t₁ : U_pos,
            w t₁ * ∑ i : Fin rX, uX i t₁.1.1.1 * (∑ z : Z, h z * MX i t₂.1.1.2.1 z) =
              ∑ i : Fin rX, w t₁ * (uX i t₁.1.1.1 * ∑ z : Z, h z * MX i t₂.1.1.2.1 z) :=
          fun _ ↦ Finset.mul_sum _ _ _
        simp_rw [hdist]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        have h0 := congrFun hw (Sum.inl i)
        simp only [L₁, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
        have hpull : (∑ t₁ : U_pos, w t₁ *
            (uX i t₁.1.1.1 * ∑ z : Z, h z * MX i t₂.1.1.2.1 z)) =
            (∑ t₁ : U_pos, w t₁ * uX i t₁.1.1.1) * (∑ z : Z, h z * MX i t₂.1.1.2.1 z) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        rw [hpull, h0, zero_mul]
      have hsY : ∑ t₁ : U_pos, w t₁ *
          ∑ j : Fin rY, (∑ z : Z, h z * MY j t₁.1.1.1 z) * uY j t₂.1.1.2.1 = 0 := by
        have hdist : ∀ t₁ : U_pos,
            w t₁ * ∑ j : Fin rY, (∑ z : Z, h z * MY j t₁.1.1.1 z) * uY j t₂.1.1.2.1 =
              ∑ j : Fin rY, w t₁ * ((∑ z : Z, h z * MY j t₁.1.1.1 z) * uY j t₂.1.1.2.1) :=
          fun _ ↦ Finset.mul_sum _ _ _
        simp_rw [hdist]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        have h0 := congrFun hw (Sum.inr j)
        simp only [L₁, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
        have hpull : (∑ t₁ : U_pos, w t₁ *
            ((∑ z : Z, h z * MY j t₁.1.1.1 z) * uY j t₂.1.1.2.1)) =
            (∑ t₁ : U_pos, w t₁ * (∑ z : Z, h z * MY j t₁.1.1.1 z)) * uY j t₂.1.1.2.1 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        rw [hpull, h0, zero_mul]
      rw [hsX, hsY, add_zero]
    rw [Fintype.sum_eq_single t₂] at hdiag_sum
    · rw [hB_diag t₂ t₂] at hdiag_sum
      simp only [↓reduceIte] at hdiag_sum
      have hφ_ne : φ t₂.1 ≠ 0 := (Finset.mem_filter.1 t₂.2).2
      have hD_ne : D t₂.1.1.1 t₂.1.1.2.1 t₂.1.1.2.2 ≠ 0 := mem_tensorSupport.1 t₂.1.2
      exact (mul_eq_zero.1 hdiag_sum).resolve_right (mul_ne_zero hφ_ne hD_ne)
    · intro t₁ ht₁
      rw [hB_diag t₁ t₂]
      simp [ht₁]
  have hU_pos_le : #U_pos ≤ rX + rY := by
    have hcard := finrank_injective_card_le L₁ hL₁_inj
    simpa [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using hcard
  have hS_le : Fintype.card S ≤ sliceRank D := by
    linarith [hpart_S, hU_pos_le, hU_zero_le, hr]
  rw [supportCard_eq_card_tensorSupport]
  rwa [Fintype.card_coe] at hS_le

/-- The unit tensor `Tensor.unit n` is a diagonal tensor. -/
theorem isDiagonalTensor_unit [Zero K] [One K] (n : ℕ) :
    IsDiagonalTensor (Tensor.unit n : Tensor K (Fin n) (Fin n) (Fin n)) := by
  refine isDiagonalTensor_iff.2 fun i₁ i₂ j₁ j₂ k₁ k₂ h₁ h₂ ↦ ?_
  simp only [Tensor.unit_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at h₁ h₂
  obtain ⟨⟨rfl, rfl⟩, _⟩ := h₁
  obtain ⟨⟨rfl, rfl⟩, _⟩ := h₂
  exact ⟨fun h ↦ ⟨h, h⟩, fun h ↦ ⟨h, h⟩, fun h ↦ ⟨h, h⟩⟩

/-- Over any field `K`, the unit tensor `Tensor.unit n` has slice rank equal to `n`. -/
@[simp]
theorem sliceRank_unit (K : Type*) [Field K] (n : ℕ) :
    sliceRank (Tensor.unit n : Tensor K (Fin n) (Fin n) (Fin n)) = n := by
  apply le_antisymm
  · have h := sliceRank_le_of_hasSliceRank (hasSliceRank_card_X (Tensor.unit n : Tensor K _ _ _))
    simpa using h
  · have hdiag := supportCard_le_sliceRank_of_isDiagonalTensor (isDiagonalTensor_unit (K := K) n)
    have hsupp : tensorSupport (Tensor.unit n : Tensor K (Fin n) (Fin n) (Fin n)) =
        (Finset.univ : Finset (Fin n)).image fun i ↦ (i, i, i) := by
      ext ⟨i, j, k⟩
      simp only [mem_tensorSupport, Tensor.unit_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
        imp_false, Classical.not_not, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨i, rfl, rfl, rfl⟩
      · rintro ⟨a, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
    have hcard : supportCard (Tensor.unit n : Tensor K (Fin n) (Fin n) (Fin n)) = n := by
      rw [supportCard_eq_card_tensorSupport, hsupp,
        Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).1),
        Finset.card_univ, Fintype.card_fin]
    rwa [hcard] at hdiag

end CslibFrontier.Foundations.LinearAlgebra.Tensor
