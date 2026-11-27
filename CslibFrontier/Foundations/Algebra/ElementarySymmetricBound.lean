/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Cast

/-!
# Elementary Symmetric Polynomial Upper Bound via Multinomial Expansion

This module proves the elementary upper bound comparing the `r`-th elementary symmetric
polynomial `e_r(a_1, …, a_t)` of nonnegative elements in an ordered commutative semiring to the
`r`-th power of their sum divided by `r!`. All results are proved under standard Lean axioms.

## Main results

* `CslibFrontier.MvPolynomial.factorial_mul_esymm_le_sum_pow`: for nonnegative `a i` over `i ∈ s` in
  an
  ordered commutative semiring, `r! * e_r(a) ≤ (∑ i ∈ s, a i) ^ r`.
* `CslibFrontier.MvPolynomial.esymm_le_sum_pow_div_factorial`: for nonnegative `a i` over `i ∈ s` in
  a
  linearly ordered field, `e_r(a) ≤ (∑ i ∈ s, a i) ^ r / r!`.
* `CslibFrontier.MvPolynomial.eval_esymm_le_sum_pow_div_factorial`: the same inequality stated
  directly
  for `MvPolynomial.eval a (MvPolynomial.esymm σ R r)`.
-/

public section

namespace CslibFrontier.MvPolynomial

section Semiring

variable {ι R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

/-- For nonnegative elements `a i` (`i ∈ s`), `r! * e_r(a) ≤ (∑ i ∈ s, a i) ^ r`. -/
theorem factorial_mul_esymm_le_sum_pow (s : Finset ι) (a : ι → R)
    (ha : ∀ i ∈ s, 0 ≤ a i) (r : ℕ) :
    (r.factorial : R) * (s.val.map a).esymm r ≤ (∑ i ∈ s, a i) ^ r := by
  classical
  rw [Finset.esymm_map_val, Finset.mul_sum]
  let injFun : Finset (Fin r → s) :=
    Finset.univ.filter fun f : Fin r → s ↦ Function.Injective f
  have hle_sum :
      ∑ f ∈ injFun, ∏ j : Fin r, a (f j).1 ≤
        ∑ f ∈ (Finset.univ : Finset (Fin r → s)), ∏ j : Fin r, a (f j).1 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro f _ _
    exact Finset.prod_nonneg fun j _ ↦ ha (f j).1 (f j).2
  have hrew : (∑ i ∈ s, a i) ^ r =
      ∑ f ∈ (Finset.univ : Finset (Fin r → s)), ∏ j : Fin r, a (f j).1 := by
    rw [Finset.sum_pow']
    symm
    refine Finset.sum_bij (fun f _ ↦ fun j ↦ (f j).1) ?_ ?_ ?_ ?_
    · intro f _
      exact Fintype.mem_piFinset.mpr fun j ↦ (f j).2
    · intro f₁ _ f₂ _ h
      funext j
      exact Subtype.ext (congrFun h j)
    · intro g hg
      refine ⟨fun j ↦ ⟨g j, Fintype.mem_piFinset.mp hg j⟩, Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  rw [← hrew] at hle_sum
  refine le_trans (le_of_eq ?_) hle_sum
  have hfib :
      ∑ f ∈ injFun, ∏ j : Fin r, a (f j).1 =
        ∑ t ∈ s.powersetCard r,
          ∑ f ∈ injFun.filter (fun f ↦ Finset.univ.image (fun j ↦ (f j).1) = t),
            ∏ j : Fin r, a (f j).1 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin r → s ↦
      Finset.univ.image (fun j ↦ (f j).1))]
    intro f hf
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact (f j).2
    · rw [Finset.card_image_of_injective]
      · exact Fintype.card_fin r
      · intro j₁ j₂ h
        exact (Finset.mem_filter.mp hf).2 (Subtype.ext h)
  rw [hfib]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hconst : ∀ f ∈ injFun.filter (fun f ↦ Finset.univ.image (fun j ↦ (f j).1) = t),
      ∏ j : Fin r, a (f j).1 = ∏ i ∈ t, a i := by
    intro f hf
    have hmem := Finset.mem_filter.mp hf
    have hinj : Function.Injective (fun j : Fin r ↦ (f j).1) := fun j₁ j₂ h ↦
      (Finset.mem_filter.mp hmem.1).2 (Subtype.ext h)
    rw [← hmem.2, Finset.prod_image (fun j₁ _ j₂ _ h ↦ hinj h)]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hcard :
      (injFun.filter (fun f ↦ Finset.univ.image (fun j ↦ (f j).1) = t)).card =
        Fintype.card (Fin r ≃ t) := by
    refine Finset.card_bij
      (fun f hf ↦ Equiv.ofBijective
        (fun j ↦ ⟨(f j).1, by
          rw [← (Finset.mem_filter.mp hf).2]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
        ?_) ?_ ?_ ?_
    · have hmem := Finset.mem_filter.mp hf
      have hinj : Function.Injective (fun j : Fin r ↦ (f j).1) := fun j₁ j₂ h ↦
        (Finset.mem_filter.mp hmem.1).2 (Subtype.ext h)
      have hcard_eq : Fintype.card (Fin r) = Fintype.card t := by
        rw [Fintype.card_fin, Fintype.card_coe, (Finset.mem_powersetCard.mp ht).2]
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, hcard_eq⟩
      intro j₁ j₂ h
      exact hinj (congrArg (fun x : t ↦ x.1) h)
    · intro _ _
      exact Finset.mem_univ _
    · intro f₁ _ f₂ _ h
      funext j
      exact Subtype.ext (congrArg (fun x : t ↦ x.1) (Equiv.ext_iff.mp h j))
    · intro e _
      have ht_sub := (Finset.mem_powersetCard.mp ht).1
      refine ⟨fun j ↦ ⟨(e j).1, ht_sub (e j).2⟩, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, fun j₁ j₂ h ↦
          e.injective (Subtype.ext (congrArg (fun x : s ↦ x.1) h))⟩, ?_⟩
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, rfl⟩
          exact (e j).2
        · intro hx
          exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      · ext j
        rfl
  have heq : Fin r ≃ t := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, (Finset.mem_powersetCard.mp ht).2])
  have hcard_perm : Fintype.card (Fin r ≃ t) = r.factorial := by
    rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin r)) heq.symm),
      Fintype.card_perm, Fintype.card_fin]
  rw [hcard, hcard_perm]

end Semiring

section Field

variable {ι σ R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- For nonnegative elements `a i` (`i ∈ s`) in a linearly ordered field,
`e_r(a) ≤ (∑ i ∈ s, a i) ^ r / r!`. -/
theorem esymm_le_sum_pow_div_factorial (s : Finset ι) (a : ι → R)
    (ha : ∀ i ∈ s, 0 ≤ a i) (r : ℕ) :
    (s.val.map a).esymm r ≤ (∑ i ∈ s, a i) ^ r / (r.factorial : R) := by
  have hpos : (0 : R) < (r.factorial : R) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  rw [le_div_iff₀ hpos, mul_comm]
  exact factorial_mul_esymm_le_sum_pow s a ha r

/-- Evaluating `MvPolynomial.esymm σ R r` at nonnegative inputs `a : σ → R` satisfies
`eval a (esymm σ R r) ≤ (∑ i, a i) ^ r / r!`. -/
theorem eval_esymm_le_sum_pow_div_factorial [Fintype σ] (a : σ → R)
    (ha : ∀ i, 0 ≤ a i) (r : ℕ) :
    _root_.MvPolynomial.eval a (_root_.MvPolynomial.esymm σ R r) ≤
      (∑ i, a i) ^ r / (r.factorial : R) := by
  classical
  have heval :
      _root_.MvPolynomial.eval a (_root_.MvPolynomial.esymm σ R r) =
        ((Finset.univ : Finset σ).val.map a).esymm r := by
    rw [_root_.MvPolynomial.esymm_eq_sum_subtype, Finset.esymm_map_val, map_sum]
    have hsub :
        (∑ t : {t : Finset σ // t.card = r},
          (_root_.MvPolynomial.eval a) (∏ i ∈ (t : Finset σ), _root_.MvPolynomial.X i)) =
          ∑ t ∈ (Finset.univ : Finset σ).powersetCard r, ∏ i ∈ t, a i := by
      refine Finset.sum_bij (fun t _ ↦ (t : Finset σ)) ?_ ?_ ?_ ?_
      · intro t _
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, t.2⟩
      · intro t₁ _ t₂ _ h
        exact Subtype.ext h
      · intro t ht
        exact ⟨⟨t, (Finset.mem_powersetCard.mp ht).2⟩, Finset.mem_univ _, rfl⟩
      · intro t _
        simp [map_prod]
    exact hsub
  rw [heval]
  exact esymm_le_sum_pow_div_factorial Finset.univ a (fun i _ ↦ ha i) r

end Field

end CslibFrontier.MvPolynomial
