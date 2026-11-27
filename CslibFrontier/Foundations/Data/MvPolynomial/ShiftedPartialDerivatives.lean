/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.Data.MvPolynomial.PartialDerivatives
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Shifted Partial Derivative Spaces, Invariance, and Identity-Minor Lower Bounds

This module develops Kayal's shifted partial derivative spaces and rank measures for multivariate
polynomials, extending `CslibFrontier.Foundations.Data.MvPolynomial.PartialDerivatives` with
monomial shifts, squarefree and multi-index partial derivative operators, restriction and
field-extension invariance, product inequalities, the private-monomial diagonal-minor criterion,
and characteristic-independent lower bounds for the permanent polynomial and selector-coupled
disjoint-block products.

## Main definitions

* `CslibFrontier.MvPolynomial.finsetMonomialExp`: squarefree exponent `∑ i ∈ S, single i 1`.
* `CslibFrontier.MvPolynomial.setPDeriv`: squarefree mixed partial derivative operator `∂_S`.
* `CslibFrontier.MvPolynomial.multiPDeriv`: multi-index partial derivative operator `∂^α`.
* `CslibFrontier.MvPolynomial.restrictFree`, `CslibFrontier.MvPolynomial.specializeRight`:
  partial variable restriction and right-block specialization algebra homomorphisms.
* `CslibFrontier.MvPolynomial.shiftedPartialSpan`, `CslibFrontier.MvPolynomial.shiftedPartialRank`:
  exact-order squarefree shifted partial derivative subspace and dimension `Γ_{κ,ℓ}(p)`.
* `CslibFrontier.MvPolynomial.multilinearShiftedPartialSpan`,
  `CslibFrontier.MvPolynomial.multilinearShiftedPartialRank`: squarefree-shift subspace and rank.
* `CslibFrontier.MvPolynomial.multiShiftedPartialSpan`,
  `CslibFrontier.MvPolynomial.multiShiftedPartialRank`: multi-index shifted partial derivative
  subspace and rank.
* `CslibFrontier.MvPolynomial.cumShiftedPartialSpan`,
  `CslibFrontier.MvPolynomial.cumShiftedPartialRank`: cumulative (`|S| ≤ κ`, `deg β ≤ ℓ`) subspace
  and rank.
* `CslibFrontier.MvPolynomial.IsPartialMatching`, `CslibFrontier.MvPolynomial.permanentPoly`,
  `CslibFrontier.MvPolynomial.subpermanentPoly`: partial matchings, generic `n × n` permanent
  polynomial, and complementary subpermanent polynomials.
* `CslibFrontier.MvPolynomial.selectorProduct`, `CslibFrontier.MvPolynomial.selectorSet`:
  selector-coupled block product `∏ c, (1 - z_c * P_c(u))` and selector derivative sets.

## Main results

* `CslibFrontier.MvPolynomial.multiPDeriv_eq_iteratedPDeriv`,
  `CslibFrontier.MvPolynomial.setPDeriv_image_eq_iteratedPDeriv`,
  `CslibFrontier.MvPolynomial.range_partialDerivatives_eq_multiShiftedPartialSpan`: exact
  agreement with `MvPolynomial.iteratedPDeriv` and `MvPolynomial.partialDerivatives`.
* `CslibFrontier.MvPolynomial.coeff_setPDeriv`, `CslibFrontier.MvPolynomial.setPDeriv_mul`:
  coefficient formula and multivariate Leibniz rule for `setPDeriv`.
* `CslibFrontier.MvPolynomial.shiftedPartialRank_sum_le`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_eq_zero_of_local_sum`: subadditivity and additive
  support-locality collapse.
* `CslibFrontier.MvPolynomial.shiftedPartialRank_restrictFree_le`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_le_add_disjoint`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_le_rename`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_rename_equiv`: restriction, disjoint-additive,
  and injective/bijective renaming monotonicity.
* `CslibFrontier.MvPolynomial.linearIndependent_map_of_field`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_map_eq`: field-extension invariance.
* `CslibFrontier.MvPolynomial.shiftedPartialRank_le_mul_disjoint`,
  `CslibFrontier.MvPolynomial.cumShiftedPartialRank_mul_le`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_zero_mul_fresh_X`: disjoint-product monotonicity,
  bounded-factor shift trade-off, and fresh-variable Pascal identity.
* `CslibFrontier.MvPolynomial.card_le_shiftedPartialRank_of_private_monomial`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_zero_prod_X`,
  `CslibFrontier.MvPolynomial.choose_sq_le_shiftedPartialRank_permanentPoly`,
  `CslibFrontier.MvPolynomial.shiftedPartialRank_zero_permanentPoly`,
  `CslibFrontier.MvPolynomial.choose_le_shiftedPartialRank_selectorProduct`: private-monomial
  criterion and characteristic-independent lower bounds (and exact shift-`0` ranks) for `∏ i, X i`,
  `permanentPoly`, and `selectorProduct`.
-/

public section

namespace CslibFrontier.MvPolynomial

open _root_.MvPolynomial

universe u v w

/-! ### Squarefree and multi-index partial derivative operators -/

section Semiring

variable {R : Type u} [CommSemiring R] {σ : Type v}

/-- First-order partial derivative operators on `MvPolynomial σ R` commute pairwise. -/
theorem pderiv_comm (i j : σ) :
    Commute ((pderiv i).toLinearMap : Module.End R (MvPolynomial σ R))
      (pderiv j).toLinearMap := by
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  · apply LinearMap.ext; intro p; apply MvPolynomial.ext; intro m
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply, Derivation.coeFn_coe, coeff_pderiv,
      Finsupp.add_apply, Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij),
      add_zero]
    rw [add_assoc, add_comm (Finsupp.single i 1) (Finsupp.single j 1), ← add_assoc]
    ring

/-- The squarefree indicator exponent `∑ i ∈ S, Finsupp.single i 1` of a finite set `S`. -/
noncomputable def finsetMonomialExp (S : Finset σ) : σ →₀ ℕ :=
  S.sum fun i ↦ Finsupp.single i 1

@[simp] theorem finsetMonomialExp_empty : finsetMonomialExp (∅ : Finset σ) = 0 := by
  simp [finsetMonomialExp]

@[simp] theorem finsetMonomialExp_singleton (i : σ) :
    finsetMonomialExp ({i} : Finset σ) = Finsupp.single i 1 := by simp [finsetMonomialExp]

theorem finsetMonomialExp_insert [DecidableEq σ] {i : σ} {S : Finset σ} (hi : i ∉ S) :
    finsetMonomialExp (insert i S) = Finsupp.single i 1 + finsetMonomialExp S := by
  simpa [finsetMonomialExp] using Finset.sum_insert hi

@[simp] theorem finsetMonomialExp_apply [DecidableEq σ] (S : Finset σ) (i : σ) :
    finsetMonomialExp S i = if i ∈ S then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [finsetMonomialExp_insert ha, Finsupp.add_apply, ih, Finsupp.single_apply]
    by_cases hia : i = a
    · subst hia; simp [ha]
    · simp [hia, Ne.symm hia]

@[simp] theorem degree_finsetMonomialExp (S : Finset σ) :
    (finsetMonomialExp S).degree = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [finsetMonomialExp_insert ha, map_add, Finsupp.degree_single, ih,
      Finset.card_insert_of_notMem ha, add_comm]

@[simp] theorem support_finsetMonomialExp (S : Finset σ) :
    (finsetMonomialExp S).support = S := by classical ext i; simp [Finsupp.mem_support_iff]

theorem finsetMonomialExp_union [DecidableEq σ] {S T : Finset σ} (h : Disjoint S T) :
    finsetMonomialExp (S ∪ T) = finsetMonomialExp S + finsetMonomialExp T := by
  ext i
  simp only [finsetMonomialExp_apply, Finsupp.add_apply, Finset.mem_union]
  by_cases hiS : i ∈ S
  · simp [hiS, Finset.disjoint_left.mp h hiS]
  · simp [hiS]

theorem finsetMonomialExp_injective : Function.Injective (finsetMonomialExp (σ := σ)) := by
  classical
  intro S T h
  rw [← support_finsetMonomialExp S, ← support_finsetMonomialExp T, h]

theorem monomial_finsetMonomialExp (S : Finset σ) :
    (monomial (finsetMonomialExp S) (1 : R) : MvPolynomial σ R) = ∏ i ∈ S, X i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [finsetMonomialExp_insert ha, Finset.prod_insert ha, ← ih, X, monomial_mul_monomial,
      one_mul]

/-- Squarefree mixed partial derivative operator `∂_S = ∏ i ∈ S, ∂_{x_i}` on `MvPolynomial σ R`. -/
noncomputable def setPDeriv (S : Finset σ) : Module.End R (MvPolynomial σ R) :=
  S.noncommProd (fun i ↦ (pderiv i).toLinearMap) (fun i _ j _ _ ↦ pderiv_comm i j)

@[simp] theorem setPDeriv_empty :
    setPDeriv (∅ : Finset σ) = (1 : Module.End R (MvPolynomial σ R)) :=
  Finset.noncommProd_empty _ _

theorem setPDeriv_empty_apply (p : MvPolynomial σ R) : setPDeriv (∅ : Finset σ) p = p := by
  simp

@[simp] theorem setPDeriv_singleton (i : σ) (p : MvPolynomial σ R) :
    setPDeriv ({i} : Finset σ) p = pderiv i p := by simp [setPDeriv]

theorem setPDeriv_insert [DecidableEq σ] {i : σ} {S : Finset σ} (hi : i ∉ S)
    (p : MvPolynomial σ R) : setPDeriv (insert i S) p = pderiv i (setPDeriv S p) :=
  DFunLike.congr_fun (Finset.noncommProd_insert_of_notMem S i
    (fun k ↦ (pderiv k).toLinearMap) (fun a _ b _ _ ↦ pderiv_comm a b) hi) p

theorem setPDeriv_union [DecidableEq σ] {S T : Finset σ} (h : Disjoint S T)
    (p : MvPolynomial σ R) : setPDeriv (S ∪ T) p = setPDeriv S (setPDeriv T p) :=
  DFunLike.congr_fun (Finset.noncommProd_union_of_disjoint h
    (fun k ↦ (pderiv k).toLinearMap) (fun a _ b _ _ ↦ pderiv_comm a b)) p

/-- Exact monomial-coefficient formula for `setPDeriv S p`. -/
@[simp] theorem coeff_setPDeriv (S : Finset σ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (setPDeriv S p).coeff m =
      (∏ i ∈ S, ((m i : R) + 1)) * p.coeff (m + finsetMonomialExp S) := by
  classical
  induction S using Finset.induction_on generalizing m with
  | empty => simp
  | insert a S ha ih =>
    rw [setPDeriv_insert ha, coeff_pderiv, ih, Finset.prod_insert ha, finsetMonomialExp_insert ha]
    have hprod : (∏ i ∈ S, ((((m + Finsupp.single a (1 : ℕ)) i : ℕ) : R) + 1)) =
        ∏ i ∈ S, ((m i : R) + 1) :=
      Finset.prod_congr rfl fun i hi ↦ by
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (fun h : i = a ↦ ha (h ▸ hi)), add_zero]
    rw [hprod, ← add_assoc]; ring

theorem setPDeriv_C {S : Finset σ} (hS : S.Nonempty) (c : R) :
    setPDeriv S (C c : MvPolynomial σ R) = 0 := by
  classical
  apply MvPolynomial.ext; intro m; obtain ⟨a, ha⟩ := hS
  rw [coeff_setPDeriv, coeff_C]
  have hne : (0 : σ →₀ ℕ) ≠ m + finsetMonomialExp S := fun hEq ↦ by
    have := DFunLike.congr_fun hEq a; simp [ha] at this
  simp only [hne, ↓reduceIte, mul_zero]; rfl

/-- Characteristic-free squarefree derivative of a squarefree monomial. -/
theorem setPDeriv_finsetMonomial [DecidableEq σ] (S T : Finset σ) (c : R) :
    setPDeriv S (monomial (finsetMonomialExp T) c) =
      if S ⊆ T then monomial (finsetMonomialExp (T \ S)) c else 0 := by
  ext m; rw [coeff_setPDeriv, coeff_monomial]
  by_cases hST : S ⊆ T
  · simp only [hST, ↓reduceIte, coeff_monomial]
    by_cases h1 : finsetMonomialExp T = m + finsetMonomialExp S
    · have hm : finsetMonomialExp (T \ S) = m := by
        ext i
        have hi := DFunLike.congr_fun h1 i
        simp only [Finsupp.add_apply, finsetMonomialExp_apply, Finset.mem_sdiff] at hi ⊢
        by_cases hiS : i ∈ S
        · simp [hiS, hST hiS] at hi ⊢; omega
        · by_cases hiT : i ∈ T <;> simp [hiS, hiT] at hi ⊢ <;> omega
      have hprod : (∏ i ∈ S, ((m i : R) + 1)) = 1 := by
        rw [← hm]; exact Finset.prod_eq_one fun i hi ↦ by simp [hi]
      simp [h1, hm, hprod]
    · have hm : finsetMonomialExp (T \ S) ≠ m := fun hEq ↦ h1 <| by
        rw [← hEq, ← finsetMonomialExp_union disjoint_sdiff_self_left,
          Finset.sdiff_union_of_subset hST]
      simp [h1, hm]
  · have h1 : finsetMonomialExp T ≠ m + finsetMonomialExp S := fun hEq ↦ by
      obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
      have hi := DFunLike.congr_fun hEq i; simp [hiS, hiT] at hi
    simp [hST, h1]

theorem setPDeriv_eq_zero_of_not_subset_vars {S : Finset σ} {p : MvPolynomial σ R}
    (hS : ¬ S ⊆ p.vars) : setPDeriv S p = 0 := by
  classical
  obtain ⟨i, hiS, hip⟩ := Finset.not_subset.mp hS
  rw [← Finset.insert_erase hiS, Finset.insert_eq, Finset.union_comm,
    setPDeriv_union (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase i S)),
    setPDeriv_singleton, pderiv_eq_zero_of_notMem_vars hip, map_zero]

theorem totalDegree_setPDeriv_le (S : Finset σ) (p : MvPolynomial σ R) :
    (setPDeriv S p).totalDegree ≤ p.totalDegree - S.card := by
  refine Finset.sup_le fun m hm ↦ ?_
  rw [mem_support_iff, coeff_setPDeriv] at hm
  have hle := le_totalDegree (mem_support_iff.mpr (right_ne_zero_of_mul hm))
  have hdeg : (m + finsetMonomialExp S).sum (fun _ e ↦ e) = m.sum (fun _ e ↦ e) + S.card := by
    change (m + finsetMonomialExp S).degree = m.degree + S.card
    rw [map_add, degree_finsetMonomialExp]
  omega

theorem setPDeriv_mem_restrictDegree (S : Finset σ) {p : MvPolynomial σ R} {d : ℕ}
    (hp : p ∈ restrictDegree σ R d) : setPDeriv S p ∈ restrictDegree σ R d := by
  rw [mem_restrictDegree] at hp ⊢
  intro m hm i
  rw [mem_support_iff, coeff_setPDeriv] at hm
  have hle := hp _ (mem_support_iff.mpr (right_ne_zero_of_mul hm)) i
  rw [Finsupp.add_apply] at hle; omega

theorem notMem_vars_setPDeriv_of_restrictDegree_one {S : Finset σ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictDegree σ R 1) {i : σ} (hi : i ∈ S) : i ∉ (setPDeriv S p).vars := by
  classical
  rw [mem_restrictDegree] at hp
  rw [vars_def, Multiset.mem_toFinset, mem_degrees]
  rintro ⟨m, hm, hmi⟩
  rw [coeff_setPDeriv] at hm
  have hle := hp _ (mem_support_iff.mpr (right_ne_zero_of_mul hm)) i
  rw [Finsupp.mem_support_iff] at hmi
  simp only [Finsupp.add_apply, finsetMonomialExp_apply, hi, ↓reduceIte] at hle; omega

theorem setPDeriv_mul_of_disjoint_vars {S : Finset σ} (p : MvPolynomial σ R)
    {q : MvPolynomial σ R} (hq : Disjoint S q.vars) :
    setPDeriv S (p * q) = setPDeriv S p * q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.disjoint_insert_left] at hq
    rw [setPDeriv_insert ha, ih hq.2, Derivation.leibniz, pderiv_eq_zero_of_notMem_vars hq.1,
      smul_zero, zero_add, smul_eq_mul, mul_comm q (pderiv a _), ← setPDeriv_insert ha]

theorem setPDeriv_rename {τ : Type w} [DecidableEq τ] {f : σ → τ} (hf : Function.Injective f)
    (S : Finset σ) (p : MvPolynomial σ R) :
    setPDeriv (S.image f) (rename f p) = rename f (setPDeriv S p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hfa : f a ∉ S.image f := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro x hx hfx; exact ha (hf hfx ▸ hx)
    rw [Finset.image_insert, setPDeriv_insert hfa, ih, pderiv_rename hf, setPDeriv_insert ha]

theorem setPDeriv_map {R' : Type w} [CommSemiring R'] (φ : R →+* R') (S : Finset σ)
    (p : MvPolynomial σ R) : setPDeriv S (map φ p) = map φ (setPDeriv S p) := by
  ext m; simp [coeff_map, map_prod]

/-- Multivariate Leibniz rule for squarefree mixed partial derivatives. -/
theorem setPDeriv_mul [DecidableEq σ] (S : Finset σ) (p q : MvPolynomial σ R) :
    setPDeriv S (p * q) = ∑ A ∈ S.powerset, setPDeriv A p * setPDeriv (S \ A) q := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [setPDeriv_insert ha, ih, map_sum, Finset.powerset_insert,
      Finset.sum_union (Finset.disjoint_left.mpr fun A hA hAi ↦ by
        rcases Finset.mem_image.mp hAi with ⟨B, _, rfl⟩
        exact ha (Finset.mem_powerset.mp hA (Finset.mem_insert_self a B))),
      Finset.sum_image (fun B hB C hC hBC ↦ by
        have haB : a ∉ B := fun h ↦ ha (Finset.mem_powerset.mp hB h)
        have haC : a ∉ C := fun h ↦ ha (Finset.mem_powerset.mp hC h)
        simpa [haB, haC] using congr_arg (fun T ↦ T.erase a) hBC),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    have haA : a ∉ A := fun h ↦ ha (Finset.mem_powerset.mp hA h)
    have haSA : a ∉ S \ A := fun h ↦ ha (Finset.sdiff_subset h)
    have hsdiff1 : insert a S \ A = insert a (S \ A) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]; by_cases hx : x = a <;> simp [hx, haA]
    have hsdiff2 : insert a S \ insert a A = S \ A := by
      ext x; by_cases hx : x = a <;> simp [hx, ha, haA]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hsdiff1, hsdiff2, setPDeriv_insert haA,
      setPDeriv_insert haSA, mul_comm (setPDeriv (S \ A) q)]

/-- Multi-index partial derivative operator `∂^α = ∏ i ∈ α.support, (∂_{x_i})^{α i}`. -/
noncomputable def multiPDeriv (α : σ →₀ ℕ) : Module.End R (MvPolynomial σ R) :=
  α.support.noncommProd (fun i ↦ ((pderiv i).toLinearMap) ^ (α i))
    (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow (α i) (α j))

@[simp] theorem multiPDeriv_zero :
    multiPDeriv (0 : σ →₀ ℕ) = (1 : Module.End R (MvPolynomial σ R)) := by simp [multiPDeriv]

@[simp] theorem multiPDeriv_single_one (i : σ) (p : MvPolynomial σ R) :
    multiPDeriv (Finsupp.single i 1) p = pderiv i p := by classical simp [multiPDeriv]

theorem multiPDeriv_add (α β : σ →₀ ℕ) :
    multiPDeriv (R := R) (α + β) = multiPDeriv α * multiPDeriv β := by
  classical
  set U := α.support ∪ β.support
  let Fpow : (σ →₀ ℕ) → σ → Module.End R (MvPolynomial σ R) :=
    fun γ i ↦ (pderiv i).toLinearMap ^ γ i
  have hexp : ∀ γ : σ →₀ ℕ, γ.support ⊆ U → multiPDeriv (R := R) γ =
      U.noncommProd (Fpow γ) (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _) := fun γ hγ ↦ by
    have h1 := Finset.noncommProd_union_of_disjoint
      (disjoint_sdiff_self_left (x := γ.support) (y := U)) (Fpow γ)
      (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _)
    have hone : ∀ T : Finset σ, (∀ i ∈ T, Fpow γ i = 1) →
        T.noncommProd (Fpow γ) (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _) = 1 := by
      intro T; induction T using Finset.induction_on with
      | empty => intro _; exact Finset.noncommProd_empty _ _
      | insert a T ha ih =>
        intro hT
        refine (Finset.noncommProd_insert_of_notMem T a (Fpow γ)
          (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _) ha).trans ?_
        rw [hT a (Finset.mem_insert_self a T), one_mul]
        exact ih fun i hi ↦ hT i (Finset.mem_insert_of_mem hi)
    have h2 : U.noncommProd (Fpow γ) (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _) =
        (U \ γ.support ∪ γ.support).noncommProd (Fpow γ)
          (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _) :=
      Finset.noncommProd_congr (Finset.sdiff_union_of_subset hγ).symm (fun _ _ ↦ rfl) _
    rw [h2, h1, hone _ fun i hi ↦ by
      rw [Finset.mem_sdiff, Finsupp.notMem_support_iff] at hi; simp [Fpow, hi.2], one_mul]; rfl
  rw [hexp (α + β) Finsupp.support_add, hexp α Finset.subset_union_left,
    hexp β Finset.subset_union_right,
    ← Finset.noncommProd_mul_distrib (s := U) (Fpow α) (Fpow β)
      (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _)
      (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _)
      (fun i _ j _ _ ↦ (pderiv_comm i j).pow_pow _ _)]
  exact Finset.noncommProd_congr rfl (fun i _ ↦ by simp [Fpow, pow_add]) _

theorem multiPDeriv_add_apply (α β : σ →₀ ℕ) (p : MvPolynomial σ R) :
    multiPDeriv (α + β) p = multiPDeriv α (multiPDeriv β p) := by
  rw [multiPDeriv_add, Module.End.mul_eq_comp, LinearMap.comp_apply]

theorem multiPDeriv_finsetMonomialExp (S : Finset σ) :
    multiPDeriv (R := R) (finsetMonomialExp S) = setPDeriv S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    apply LinearMap.ext; intro p
    rw [finsetMonomialExp_insert ha, multiPDeriv_add_apply, multiPDeriv_single_one, ih,
      setPDeriv_insert ha]

/-- Exact bridge to `MvPolynomial.iteratedPDeriv`: `multiPDeriv` along the multiplicity vector of a
tuple `α : Fin k → σ` coincides with `iteratedPDeriv α`. -/
theorem multiPDeriv_eq_iteratedPDeriv {k : ℕ} (α : Fin k → σ) :
    multiPDeriv (R := R) (∑ i : Fin k, Finsupp.single (α i) 1) = iteratedPDeriv α := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply LinearMap.ext; intro p
    rw [Fin.sum_univ_succ, multiPDeriv_add_apply, multiPDeriv_single_one, iteratedPDeriv_succ_apply]
    exact congr_arg (pderiv (α 0)) (DFunLike.congr_fun (ih (Fin.tail α)) p)

/-- On an injective tuple `α : Fin k → σ`, `setPDeriv` along the image set coincides with
`MvPolynomial.iteratedPDeriv α`. -/
theorem setPDeriv_image_eq_iteratedPDeriv [DecidableEq σ] {k : ℕ} {α : Fin k → σ}
    (hα : Function.Injective α) :
    setPDeriv (R := R) (Finset.univ.image α) = iteratedPDeriv α := by
  rw [← multiPDeriv_finsetMonomialExp, ← multiPDeriv_eq_iteratedPDeriv]
  congr 1
  unfold finsetMonomialExp
  exact Finset.sum_image fun i _ j _ hij ↦ hα hij

theorem multiPDeriv_eq_zero_of_two_le {α : σ →₀ ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictDegree σ R 1) {i : σ} (hi : 2 ≤ α i) : multiPDeriv α p = 0 := by
  classical
  have hsplit : α = Finsupp.single i 1 + (Finsupp.single i 1 + (α - Finsupp.single i 2)) := by
    ext j; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij; simp; omega
    · simp [hij]
  have hpres : ∀ β : σ →₀ ℕ, multiPDeriv β p ∈ restrictDegree σ R 1 := by
    intro β; induction β using Finsupp.induction with
    | zero => simpa
    | single_add j n β _ hn ih =>
      induction n with
      | zero => exact (hn rfl).elim
      | succ n ihn =>
        have hs : Finsupp.single j (n + 1) + β =
            Finsupp.single j 1 + (Finsupp.single j n + β) := by
          ext k; simp [Finsupp.single_apply]; omega
        rw [hs, multiPDeriv_add_apply, ← finsetMonomialExp_singleton, multiPDeriv_finsetMonomialExp]
        rcases eq_or_ne n 0 with rfl | hn0
        · simpa using setPDeriv_mem_restrictDegree {j} ih
        · exact setPDeriv_mem_restrictDegree {j} (ihn hn0)
  rw [hsplit, multiPDeriv_add_apply, multiPDeriv_add_apply, multiPDeriv_single_one,
    multiPDeriv_single_one]
  refine pderiv_eq_zero_of_notMem_vars ?_
  rw [← setPDeriv_singleton]
  exact notMem_vars_setPDeriv_of_restrictDegree_one (hpres _) (Finset.mem_singleton_self i)

/-! ### Partial variable restrictions and right-block specializations -/

/-- Partial variable restriction specializing each variable with `ρ i = some c` to `c` and
projecting onto the surviving free variables `{i : σ // ρ i = none}`. -/
noncomputable def restrictFree (ρ : σ → Option R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial {i : σ // ρ i = none} R :=
  aeval fun i ↦ match h : ρ i with | none => X ⟨i, h⟩ | some c => C c

@[simp] theorem restrictFree_X_none (ρ : σ → Option R) (i : {i : σ // ρ i = none}) :
    restrictFree ρ (X i.1) = X i := by
  rcases i with ⟨i, hi⟩; simp only [restrictFree, aeval_X]
  split <;> rename_i h
  · rfl
  · rw [hi] at h; cases h

@[simp] theorem restrictFree_X_some (ρ : σ → Option R) {i : σ} {c : R} (hi : ρ i = some c) :
    restrictFree ρ (X i) = C c := by
  simp only [restrictFree, aeval_X]; split <;> rename_i h <;> rw [hi] at h <;> cases h; rfl

theorem restrictFree_monomial_mapDomain (ρ : σ → Option R) (β : {i : σ // ρ i = none} →₀ ℕ) :
    restrictFree ρ (monomial (β.mapDomain Subtype.val) 1) = monomial β 1 := by
  have hcomp : (restrictFree ρ).comp (rename (R := R) Subtype.val) = AlgHom.id R _ :=
    algHom_ext fun i ↦ by simp
  simpa [rename_monomial] using DFunLike.congr_fun hcomp (monomial β 1)

theorem pderiv_restrictFree (ρ : σ → Option R) (i : {i : σ // ρ i = none})
    (p : MvPolynomial σ R) : pderiv i (restrictFree ρ p) = restrictFree ρ (pderiv i.1 p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq => simp [ihp, ihq]
  | mul_X p j ih =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul, ih]
    cases hρ : ρ j with
    | none =>
      rw [restrictFree_X_none ρ ⟨j, hρ⟩, pderiv_X, pderiv_X, Pi.single_apply, Pi.single_apply]
      by_cases hji : (⟨j, hρ⟩ : {k : σ // ρ k = none}) = i
      · subst hji; simp
      · simp [hji, show j ≠ i.1 from fun h ↦ hji (Subtype.ext h)]
    | some c =>
      have hjv : i.1 ≠ j := fun h ↦ by rw [← h, i.2] at hρ; cases hρ
      simp [restrictFree_X_some ρ hρ, pderiv_X, Pi.single_eq_of_ne hjv.symm]

theorem setPDeriv_restrictFree (ρ : σ → Option R) (S : Finset {i : σ // ρ i = none})
    (p : MvPolynomial σ R) : setPDeriv S (restrictFree ρ p) =
      restrictFree ρ (setPDeriv (S.map ⟨Subtype.val, Subtype.val_injective⟩) p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ha' : a.1 ∉ S.map ⟨Subtype.val, Subtype.val_injective⟩ := by simp [ha]
    rw [setPDeriv_insert ha, ih, Finset.map_insert, Function.Embedding.coeFn_mk,
      setPDeriv_insert ha', pderiv_restrictFree]

/-- Specialization of the right variable block `ν` in `MvPolynomial (σ ⊕ ν) R` to constants `c`. -/
noncomputable def specializeRight {ν : Type w} (c : ν → R) :
    MvPolynomial (σ ⊕ ν) R →ₐ[R] MvPolynomial σ R :=
  aeval (Sum.elim X (C ∘ c))

@[simp] theorem specializeRight_X_inl {ν : Type w} (c : ν → R) (i : σ) :
    specializeRight c (X (Sum.inl i)) = X i := by simp [specializeRight]

@[simp] theorem specializeRight_X_inr {ν : Type w} (c : ν → R) (j : ν) :
    specializeRight (σ := σ) c (X (Sum.inr j)) = C (c j) := by simp [specializeRight]

@[simp] theorem specializeRight_rename_inl {ν : Type w} (c : ν → R) (p : MvPolynomial σ R) :
    specializeRight c (rename Sum.inl p) = p :=
  DFunLike.congr_fun (algHom_ext fun i ↦ by simp [specializeRight] :
    (specializeRight c).comp (rename (R := R) (Sum.inl : σ → σ ⊕ ν)) = AlgHom.id R _) p

@[simp] theorem specializeRight_rename_inr {ν : Type w} (c : ν → R) (q : MvPolynomial ν R) :
    specializeRight (σ := σ) c (rename Sum.inr q) = C (eval c q) := by
  have hcomp : ((specializeRight (σ := σ) c).toRingHom).comp
      (rename (R := R) (Sum.inr : ν → σ ⊕ ν)).toRingHom = C.comp (eval c) :=
    ringHom_ext (fun r ↦ by simp [specializeRight]) (fun j ↦ by simp [specializeRight])
  exact DFunLike.congr_fun hcomp q

theorem pderiv_specializeRight {ν : Type w} (c : ν → R) (i : σ) (p : MvPolynomial (σ ⊕ ν) R) :
    pderiv i (specializeRight c p) = specializeRight c (pderiv (Sum.inl i) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [specializeRight]
  | add p q ihp ihq => simp [ihp, ihq]
  | mul_X p s ih =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul, ih]
    cases s with
    | inl j =>
      simp only [specializeRight, aeval_X, Sum.elim_inl, pderiv_X, Pi.single_apply, Sum.inl.injEq]
      by_cases hji : j = i <;> simp [hji]
    | inr j => simp [specializeRight, pderiv_X]

theorem setPDeriv_specializeRight {ν : Type w} (c : ν → R) (S : Finset σ)
    (p : MvPolynomial (σ ⊕ ν) R) : setPDeriv S (specializeRight c p) =
      specializeRight c (setPDeriv (S.map ⟨Sum.inl, Sum.inl_injective⟩) p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ha' : (Sum.inl a : σ ⊕ ν) ∉ S.map ⟨Sum.inl, Sum.inl_injective⟩ := by simp [ha]
    rw [setPDeriv_insert ha, ih, Finset.map_insert, Function.Embedding.coeFn_mk,
      setPDeriv_insert ha', pderiv_specializeRight]

/-! ### Shifted partial derivative subspaces and rank measures -/

/-- Exact-order squarefree shifted partial derivative subspace spanned by `x^β * ∂_S p` with
`S.card = κ` and `β.degree ≤ ℓ`. -/
@[expose] noncomputable def shiftedPartialSpan (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {q | ∃ (S : Finset σ) (β : σ →₀ ℕ),
    S.card = κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * setPDeriv S p}

/-- Exact-order squarefree shifted partial derivative rank `Γ_{κ,ℓ}(p)`. -/
@[expose] noncomputable def shiftedPartialRank (κ ℓ : ℕ) (p : MvPolynomial σ R) : ℕ :=
  Module.finrank R (shiftedPartialSpan κ ℓ p)

/-- Squarefree-shift shifted partial derivative subspace (`S.card = κ`, `T.card ≤ ℓ`). -/
@[expose] noncomputable def multilinearShiftedPartialSpan (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {q | ∃ (S T : Finset σ),
    S.card = κ ∧ T.card ≤ ℓ ∧ q = monomial (finsetMonomialExp T) 1 * setPDeriv S p}

/-- Squarefree-shift shifted partial derivative rank of `p`. -/
@[expose] noncomputable def multilinearShiftedPartialRank (κ ℓ : ℕ) (p : MvPolynomial σ R) : ℕ :=
  Module.finrank R (multilinearShiftedPartialSpan κ ℓ p)

/-- Multi-index shifted partial derivative subspace (`α.degree = κ`, `β.degree ≤ ℓ`). -/
@[expose] noncomputable def multiShiftedPartialSpan (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {q | ∃ (α β : σ →₀ ℕ),
    α.degree = κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * multiPDeriv α p}

/-- Multi-index shifted partial derivative rank of `p`. -/
@[expose] noncomputable def multiShiftedPartialRank (κ ℓ : ℕ) (p : MvPolynomial σ R) : ℕ :=
  Module.finrank R (multiShiftedPartialSpan κ ℓ p)

/-- Cumulative shifted partial derivative subspace (`S.card ≤ κ`, `β.degree ≤ ℓ`). -/
@[expose] noncomputable def cumShiftedPartialSpan (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {q | ∃ (S : Finset σ) (β : σ →₀ ℕ),
    S.card ≤ κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * setPDeriv S p}

/-- Cumulative shifted partial derivative rank `Γ_{≤ κ, ℓ}(p)`. -/
@[expose] noncomputable def cumShiftedPartialRank (κ ℓ : ℕ) (p : MvPolynomial σ R) : ℕ :=
  Module.finrank R (cumShiftedPartialSpan κ ℓ p)

/-- At shift `ℓ = 0`, `multiShiftedPartialSpan k 0 p` equals the range of upstream
`MvPolynomial.partialDerivatives k p`. -/
theorem range_partialDerivatives_eq_multiShiftedPartialSpan [Fintype σ] (k : ℕ)
    (p : MvPolynomial σ R) :
    LinearMap.range (partialDerivatives k p) = multiShiftedPartialSpan k 0 p := by
  rw [range_partialDerivatives, multiShiftedPartialSpan]
  congr 1; ext q; constructor
  · rintro ⟨α, rfl⟩
    refine ⟨∑ i : Fin k, Finsupp.single (α i) 1, 0, ?_, le_rfl, ?_⟩
    · simp [map_sum]
    · simp [multiPDeriv_eq_iteratedPDeriv]
  · rintro ⟨μ, β, hμ, hβ, rfl⟩
    have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff β).mp (Nat.eq_zero_of_le_zero hβ)
    subst hβ0
    obtain ⟨j, α, rfl⟩ := Finsupp.exists_fin_sum_single_one_eq μ
    have hjk : j = k := by simpa [map_sum] using hμ
    subst hjk
    exact ⟨α, by simp [multiPDeriv_eq_iteratedPDeriv]⟩

theorem mem_shiftedPartialSpan {κ ℓ : ℕ} {p : MvPolynomial σ R} {S : Finset σ} (hS : S.card = κ)
    {β : σ →₀ ℕ} (hβ : β.degree ≤ ℓ) :
    monomial β 1 * setPDeriv S p ∈ shiftedPartialSpan κ ℓ p :=
  Submodule.subset_span ⟨S, β, hS, hβ, rfl⟩

theorem shiftedPartialSpan_le_iff {κ ℓ : ℕ} {p : MvPolynomial σ R}
    {W : Submodule R (MvPolynomial σ R)} : shiftedPartialSpan κ ℓ p ≤ W ↔
      ∀ (S : Finset σ) (β : σ →₀ ℕ), S.card = κ → β.degree ≤ ℓ →
        monomial β 1 * setPDeriv S p ∈ W := by
  rw [shiftedPartialSpan, Submodule.span_le]
  exact ⟨fun h S β hS hβ ↦ h ⟨S, β, hS, hβ, rfl⟩,
    by rintro h _ ⟨S, β, hS, hβ, rfl⟩; exact h S β hS hβ⟩

theorem cumShiftedPartialSpan_le_iff {κ ℓ : ℕ} {p : MvPolynomial σ R}
    {W : Submodule R (MvPolynomial σ R)} : cumShiftedPartialSpan κ ℓ p ≤ W ↔
      ∀ (S : Finset σ) (β : σ →₀ ℕ), S.card ≤ κ → β.degree ≤ ℓ →
        monomial β 1 * setPDeriv S p ∈ W := by
  rw [cumShiftedPartialSpan, Submodule.span_le]
  exact ⟨fun h S β hS hβ ↦ h ⟨S, β, hS, hβ, rfl⟩,
    by rintro h _ ⟨S, β, hS, hβ, rfl⟩; exact h S β hS hβ⟩

theorem multilinearShiftedPartialSpan_le (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    multilinearShiftedPartialSpan κ ℓ p ≤ shiftedPartialSpan κ ℓ p :=
  Submodule.span_mono fun _ ⟨S, T, hS, hT, hq⟩ ↦
    ⟨S, finsetMonomialExp T, hS, (degree_finsetMonomialExp T).trans_le hT, hq⟩

theorem shiftedPartialSpan_le_multi (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    shiftedPartialSpan κ ℓ p ≤ multiShiftedPartialSpan κ ℓ p :=
  Submodule.span_mono fun _ ⟨S, β, hS, hβ, hq⟩ ↦
    ⟨finsetMonomialExp S, β, (degree_finsetMonomialExp S).trans hS, hβ,
      by rwa [multiPDeriv_finsetMonomialExp]⟩

theorem shiftedPartialSpan_le_cum (κ ℓ : ℕ) (p : MvPolynomial σ R) :
    shiftedPartialSpan κ ℓ p ≤ cumShiftedPartialSpan κ ℓ p :=
  Submodule.span_mono fun _ ⟨S, β, hS, hβ, hq⟩ ↦ ⟨S, β, hS.le, hβ, hq⟩

/-- On multilinear polynomials, multi-index and squarefree shifted partial derivative spans
agree. -/
theorem multiShiftedPartialSpan_eq_of_restrictDegree_one (κ ℓ : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ restrictDegree σ R 1) :
    multiShiftedPartialSpan κ ℓ p = shiftedPartialSpan κ ℓ p := by
  classical
  apply le_antisymm _ (shiftedPartialSpan_le_multi κ ℓ p)
  rw [multiShiftedPartialSpan, Submodule.span_le]
  rintro _ ⟨α, β, hα, hβ, rfl⟩
  by_cases hsq : ∀ i, α i ≤ 1
  · have hEq : α = finsetMonomialExp α.support := by
      ext i; rw [finsetMonomialExp_apply]
      by_cases hi : i ∈ α.support
      · have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
        have := hsq i; simp only [hi, ↓reduceIte]; omega
      · simp [hi, Finsupp.notMem_support_iff.mp hi]
    rw [hEq, multiPDeriv_finsetMonomialExp]
    exact mem_shiftedPartialSpan (by rw [← degree_finsetMonomialExp, ← hEq, hα]) hβ
  · push Not at hsq; obtain ⟨i, hi⟩ := hsq
    rw [multiPDeriv_eq_zero_of_two_le hp hi, mul_zero]; exact Submodule.zero_mem _

theorem shiftedPartialSpan_add_C_of_pos {κ : ℕ} (hκ : 0 < κ) (ℓ : ℕ) (p : MvPolynomial σ R)
    (c : R) : shiftedPartialSpan κ ℓ (p + C c) = shiftedPartialSpan κ ℓ p := by
  rw [shiftedPartialSpan, shiftedPartialSpan]; congr 1; ext q
  constructor <;> rintro ⟨S, β, hS, hβ, rfl⟩ <;> refine ⟨S, β, hS, hβ, ?_⟩ <;>
    simp [setPDeriv_C (Finset.card_pos.mp (hS ▸ hκ)) c]

theorem shiftedPartialSpan_add_le (κ ℓ : ℕ) (p q : MvPolynomial σ R) :
    shiftedPartialSpan κ ℓ (p + q) ≤ shiftedPartialSpan κ ℓ p ⊔ shiftedPartialSpan κ ℓ q := by
  rw [shiftedPartialSpan_le_iff]; intro S β hS hβ; rw [map_add, mul_add]
  exact Submodule.add_mem_sup (mem_shiftedPartialSpan hS hβ) (mem_shiftedPartialSpan hS hβ)

private theorem finite_degree_le [Finite σ] (d : ℕ) : {γ : σ →₀ ℕ | γ.degree ≤ d}.Finite := by
  cases nonempty_fintype σ
  let e : {γ : σ →₀ ℕ // γ.degree ≤ d} → (σ → Fin (d + 1)) :=
    fun γ i ↦ ⟨γ.1 i, Nat.lt_succ_of_le ((Finsupp.le_degree i γ.1).trans γ.2)⟩
  exact Set.finite_coe_iff.mp (Finite.of_injective e fun _ _ h ↦
    Subtype.ext (Finsupp.ext fun i ↦ Fin.ext_iff.mp (congr_fun h i)))

end Semiring

/-! ### Finite-dimensionality, monotonicity, field-extension invariance, and product bounds -/

section Field

variable {F : Type u} [Field F] {σ : Type v}

instance instModuleFiniteShiftedPartialSpan [Finite σ] (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    Module.Finite F (shiftedPartialSpan κ ℓ p) := by
  classical
  cases nonempty_fintype σ
  have hfin : {q : MvPolynomial σ F | ∃ (S : Finset σ) (β : σ →₀ ℕ),
      S.card = κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * setPDeriv S p}.Finite := by
    refine ((Set.toFinite (Set.univ : Set (Finset σ))).prod (finite_degree_le ℓ) |>.image
      fun x ↦ monomial x.2 1 * setPDeriv x.1 p).subset ?_
    rintro _ ⟨S, β, _, hβ, rfl⟩; exact ⟨(S, β), ⟨trivial, hβ⟩, rfl⟩
  exact Module.Finite.iff_fg.mpr ⟨hfin.toFinset, by simp [shiftedPartialSpan]⟩

instance instModuleFiniteMultilinearShiftedPartialSpan [Finite σ] (κ ℓ : ℕ)
    (p : MvPolynomial σ F) : Module.Finite F (multilinearShiftedPartialSpan κ ℓ p) :=
  Submodule.finiteDimensional_of_le (multilinearShiftedPartialSpan_le κ ℓ p)

instance instModuleFiniteMultiShiftedPartialSpan [Finite σ] (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    Module.Finite F (multiShiftedPartialSpan κ ℓ p) := by
  classical
  have hfin : {q : MvPolynomial σ F | ∃ (α β : σ →₀ ℕ),
      α.degree = κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * multiPDeriv α p}.Finite := by
    refine (((finite_degree_le κ).prod (finite_degree_le ℓ)).image
      fun x ↦ monomial x.2 1 * multiPDeriv x.1 p).subset ?_
    rintro _ ⟨α, β, hα, hβ, rfl⟩; exact ⟨(α, β), ⟨hα.le, hβ⟩, rfl⟩
  exact Module.Finite.iff_fg.mpr ⟨hfin.toFinset, by simp [multiShiftedPartialSpan]⟩

instance instModuleFiniteCumShiftedPartialSpan [Finite σ] (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    Module.Finite F (cumShiftedPartialSpan κ ℓ p) := by
  classical
  cases nonempty_fintype σ
  have hfin : {q : MvPolynomial σ F | ∃ (S : Finset σ) (β : σ →₀ ℕ),
      S.card ≤ κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * setPDeriv S p}.Finite := by
    refine ((Set.toFinite (Set.univ : Set (Finset σ))).prod (finite_degree_le ℓ) |>.image
      fun x ↦ monomial x.2 1 * setPDeriv x.1 p).subset ?_
    rintro _ ⟨S, β, _, hβ, rfl⟩; exact ⟨(S, β), ⟨trivial, hβ⟩, rfl⟩
  exact Module.Finite.iff_fg.mpr ⟨hfin.toFinset, by simp [cumShiftedPartialSpan]⟩

theorem multilinearShiftedPartialRank_le [Finite σ] (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    multilinearShiftedPartialRank κ ℓ p ≤ shiftedPartialRank κ ℓ p :=
  Submodule.finrank_mono (multilinearShiftedPartialSpan_le κ ℓ p)

theorem multiShiftedPartialRank_eq_of_restrictDegree_one (κ ℓ : ℕ) {p : MvPolynomial σ F}
    (hp : p ∈ restrictDegree σ F 1) :
    multiShiftedPartialRank κ ℓ p = shiftedPartialRank κ ℓ p := by
  rw [multiShiftedPartialRank, shiftedPartialRank,
    multiShiftedPartialSpan_eq_of_restrictDegree_one κ ℓ hp]

theorem shiftedPartialRank_le_cum [Finite σ] (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ p ≤ cumShiftedPartialRank κ ℓ p :=
  Submodule.finrank_mono (shiftedPartialSpan_le_cum κ ℓ p)

@[simp] theorem shiftedPartialRank_zero (κ ℓ : ℕ) :
    shiftedPartialRank κ ℓ (0 : MvPolynomial σ F) = 0 := by
  have hbot : shiftedPartialSpan κ ℓ (0 : MvPolynomial σ F) = ⊥ := by
    rw [shiftedPartialSpan, Submodule.span_eq_bot]; rintro _ ⟨_, _, _, _, rfl⟩; simp
  rw [shiftedPartialRank, hbot, finrank_bot]

theorem shiftedPartialRank_add_C_eq {κ : ℕ} (hκ : 0 < κ) (ℓ : ℕ) (p : MvPolynomial σ F) (c : F) :
    shiftedPartialRank κ ℓ (p + C c) = shiftedPartialRank κ ℓ p := by
  rw [shiftedPartialRank, shiftedPartialRank, shiftedPartialSpan_add_C_of_pos hκ]

theorem shiftedPartialRank_add_le [Finite σ] (κ ℓ : ℕ) (p q : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ (p + q) ≤ shiftedPartialRank κ ℓ p + shiftedPartialRank κ ℓ q := by
  have h1 := Submodule.finrank_mono (shiftedPartialSpan_add_le κ ℓ p q)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (shiftedPartialSpan κ ℓ p) (shiftedPartialSpan κ ℓ q)
  unfold shiftedPartialRank; omega

/-- Subadditivity of `shiftedPartialRank` over finite sums. -/
theorem shiftedPartialRank_sum_le [Finite σ] (κ ℓ : ℕ) {α : Type*} (s : Finset α)
    (f : α → MvPolynomial σ F) :
    shiftedPartialRank κ ℓ (∑ a ∈ s, f a) ≤ ∑ a ∈ s, shiftedPartialRank κ ℓ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (shiftedPartialRank_add_le κ ℓ _ _).trans (Nat.add_le_add_left ih _)

/-- Additive support-locality vanishing: sums of terms each on fewer than `κ` variables have
order-`κ` shifted partial derivative rank `0`. -/
theorem shiftedPartialRank_eq_zero_of_local_sum {α : Type*} (s : Finset α)
    (q : α → MvPolynomial σ F) (c : F) {κ : ℕ} (hκ : 0 < κ) (ℓ : ℕ)
    (hloc : ∀ a ∈ s, (q a).vars.card < κ) :
    shiftedPartialRank κ ℓ (C c + ∑ a ∈ s, q a) = 0 := by
  suffices shiftedPartialSpan κ ℓ (C c + ∑ a ∈ s, q a) = ⊥ by
    rw [shiftedPartialRank, this, finrank_bot]
  rw [add_comm, shiftedPartialSpan_add_C_of_pos hκ, shiftedPartialSpan, Submodule.span_eq_bot]
  rintro _ ⟨S, _, hS, _, rfl⟩
  rw [map_sum, Finset.sum_eq_zero, mul_zero]; intro a ha
  refine setPDeriv_eq_zero_of_not_subset_vars fun hsub ↦ ?_
  have := (Finset.card_le_card hsub).trans_lt (hloc a ha); omega

@[gcongr] theorem shiftedPartialRank_mono_shift [Finite σ] (κ : ℕ) {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ')
    (p : MvPolynomial σ F) : shiftedPartialRank κ ℓ p ≤ shiftedPartialRank κ ℓ' p :=
  Submodule.finrank_mono <| Submodule.span_mono fun _ ⟨S, β, hS, hβ, hq⟩ ↦
    ⟨S, β, hS, hβ.trans hℓ, hq⟩

/-- Variable-restriction monotonicity: fixing variables to constants cannot increase
`shiftedPartialRank`. -/
theorem shiftedPartialRank_restrictFree_le [Finite σ] (ρ : σ → Option F) (κ ℓ : ℕ)
    (p : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ (restrictFree ρ p) ≤ shiftedPartialRank κ ℓ p := by
  have hsub : shiftedPartialSpan κ ℓ (restrictFree ρ p) ≤
      (shiftedPartialSpan κ ℓ p).map (restrictFree ρ).toLinearMap := by
    rw [shiftedPartialSpan_le_iff]; intro S β hS hβ
    rw [setPDeriv_restrictFree, ← restrictFree_monomial_mapDomain ρ β, ← map_mul]
    exact Submodule.mem_map_of_mem
      (mem_shiftedPartialSpan (by simpa using hS) (by rwa [Finsupp.degree_mapDomain]))
  exact (Submodule.finrank_mono hsub).trans (Submodule.finrank_map_le _ _)

theorem shiftedPartialRank_specializeRight_le {ν : Type*} [Finite σ] [Finite ν]
    (c : ν → F) (κ ℓ : ℕ) (p : MvPolynomial (σ ⊕ ν) F) :
    shiftedPartialRank κ ℓ (specializeRight c p) ≤ shiftedPartialRank κ ℓ p := by
  have hsub : shiftedPartialSpan κ ℓ (specializeRight c p) ≤
      (shiftedPartialSpan κ ℓ p).map (specializeRight c).toLinearMap := by
    rw [shiftedPartialSpan_le_iff]; intro S β hS hβ
    have hmon : specializeRight c (monomial (β.mapDomain (Sum.inl : σ → σ ⊕ ν)) (1 : F)) =
        monomial β 1 := by
      simpa [rename_monomial] using specializeRight_rename_inl c (monomial β (1 : F))
    rw [setPDeriv_specializeRight, ← hmon, ← map_mul]
    exact Submodule.mem_map_of_mem
      (mem_shiftedPartialSpan (by simpa using hS) (by rwa [Finsupp.degree_mapDomain]))
  exact (Submodule.finrank_mono hsub).trans (Submodule.finrank_map_le _ _)

/-- Syntactic extraction for additively separable polynomials `Q(u) + R(v)` when `κ ≥ 1`. -/
theorem shiftedPartialRank_le_add_disjoint {ν : Type*} [Finite σ] [Finite ν] {κ : ℕ}
    (hκ : 0 < κ) (ℓ : ℕ) (Q : MvPolynomial σ F) (R : MvPolynomial ν F) :
    shiftedPartialRank κ ℓ Q ≤ shiftedPartialRank κ ℓ (rename Sum.inl Q + rename Sum.inr R) := by
  have h := shiftedPartialRank_specializeRight_le (0 : ν → F) κ ℓ
    (rename Sum.inl Q + rename Sum.inr R)
  rwa [map_add, specializeRight_rename_inl, specializeRight_rename_inr,
    shiftedPartialRank_add_C_eq hκ] at h

/-- Injective variable renaming does not decrease `shiftedPartialRank`. -/
theorem shiftedPartialRank_le_rename {τ : Type w} [Finite τ] {f : σ → τ}
    (hf : Function.Injective f) (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ p ≤ shiftedPartialRank κ ℓ (rename f p) := by
  classical
  have hinj : Function.Injective (rename (R := F) f).toLinearMap := rename_injective f hf
  rw [shiftedPartialRank, (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
  refine Submodule.finrank_mono ?_
  rw [shiftedPartialSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨S, β, hS, hβ, rfl⟩, rfl⟩
  change rename f (monomial β 1 * setPDeriv S p) ∈ shiftedPartialSpan κ ℓ (rename f p)
  rw [map_mul, rename_monomial, ← setPDeriv_rename hf]
  exact mem_shiftedPartialSpan ((Finset.card_image_of_injective S hf).trans hS)
    (by rwa [Finsupp.degree_mapDomain])

/-- Bijective variable renaming preserves `shiftedPartialRank`. -/
theorem shiftedPartialRank_rename_equiv {τ : Type w} [Finite σ] [Finite τ] (e : σ ≃ τ)
    (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ (rename e p) = shiftedPartialRank κ ℓ p := by
  refine le_antisymm ?_ (shiftedPartialRank_le_rename e.injective κ ℓ p)
  have h := shiftedPartialRank_le_rename e.symm.injective κ ℓ (rename e p)
  rwa [show rename (R := F) e.symm (rename e p) = p by simp [rename_rename]] at h

/-- Linear independence of multivariate polynomials is preserved along arbitrary field
extensions. -/
theorem linearIndependent_map_of_field {K : Type w} [Field K] (φ : F →+* K) :
    ∀ {r : ℕ} {g : Fin r → MvPolynomial σ F},
      LinearIndependent F g → LinearIndependent K (fun i ↦ map φ (g i))
  | 0, _, _ => linearIndependent_empty_type
  | r + 1, g, hg => by
    have hsupp : (g 0).support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun h ↦ hg.ne_zero 0 (support_eq_empty.mp h)
    obtain ⟨m₀, hm₀⟩ := hsupp
    set c₀ : F := (g 0).coeff m₀
    have hc₀ : c₀ ≠ 0 := mem_support_iff.mp hm₀
    let α : Fin r → F := fun j ↦ (g j.succ).coeff m₀ * c₀⁻¹
    let g' : Fin r → MvPolynomial σ F := fun j ↦ g j.succ - α j • g 0
    have hg'_coeff : ∀ j : Fin r, (g' j).coeff m₀ = 0 := fun j ↦ by simp [g', α, c₀, hc₀]
    have hg'_ind : LinearIndependent F g' := by
      rw [Fintype.linearIndependent_iff] at hg ⊢; intro a ha j
      refine hg (Fin.cases (- ∑ k : Fin r, a k * α k) a) ?_ j.succ
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, neg_smul, Finset.sum_smul, mul_smul]
      have hsub : ∑ k : Fin r, a k • g k.succ =
          ∑ k : Fin r, a k • g' k + ∑ k : Fin r, a k • α k • g 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ ↦ by simp [g', smul_sub]
      rw [hsub, ha, zero_add, neg_add_cancel]
    have hK' := linearIndependent_map_of_field φ hg'_ind
    rw [Fintype.linearIndependent_iff] at hK' ⊢; intro μ hμ
    have hsplit : (μ 0 + ∑ j : Fin r, μ j.succ * φ (α j)) • map φ (g 0) +
        ∑ j : Fin r, μ j.succ • map φ (g' j) = 0 := by
      rw [← hμ, Fin.sum_univ_succ, add_smul, add_assoc]; congr 1
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hm : map φ (g' j) = map φ (g j.succ) - φ (α j) • map φ (g 0) := by
        simp [g', map_sub, smul_eq_C_mul, map_C]
      rw [hm, smul_sub, mul_smul, add_sub_cancel]
    have hlead : μ 0 + ∑ j : Fin r, μ j.succ * φ (α j) = 0 := by
      have hc := congr_arg (fun q : MvPolynomial σ K ↦ q.coeff m₀) hsplit
      simp [coeff_map, hg'_coeff] at hc; exact hc.resolve_right hc₀
    rw [hlead, zero_smul, zero_add] at hsplit
    have htail : ∀ j : Fin r, μ j.succ = 0 := hK' _ hsplit
    exact fun i ↦ Fin.cases (by simpa [htail] using hlead) htail i

/-- Field-extension invariance of `shiftedPartialRank` across arbitrary universe levels. -/
theorem shiftedPartialRank_map_eq {K : Type w} [Field K] [Finite σ] (φ : F →+* K)
    (κ ℓ : ℕ) (p : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ (map φ p) = shiftedPartialRank κ ℓ p := by
  set G : Set (MvPolynomial σ F) := {q | ∃ (S : Finset σ) (β : σ →₀ ℕ),
    S.card = κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * setPDeriv S p}
  have himg : map φ '' G = {q | ∃ (S : Finset σ) (β : σ →₀ ℕ),
      S.card = κ ∧ β.degree ≤ ℓ ∧ q = monomial β 1 * setPDeriv S (map φ p)} := by
    ext q; constructor
    · rintro ⟨_, ⟨S, β, hS, hβ, rfl⟩, rfl⟩
      exact ⟨S, β, hS, hβ, by simp [map_monomial, setPDeriv_map]⟩
    · rintro ⟨S, β, hS, hβ, rfl⟩
      exact ⟨monomial β 1 * setPDeriv S p, ⟨S, β, hS, hβ, rfl⟩,
        by simp [map_monomial, setPDeriv_map]⟩
  rw [shiftedPartialRank, shiftedPartialRank, shiftedPartialSpan, shiftedPartialSpan, ← himg]
  set V := Submodule.span F G
  set W := Submodule.span K (map φ '' G)
  have hfin : Module.Finite F V := instModuleFiniteShiftedPartialSpan κ ℓ p
  have hmap_mem : ∀ v ∈ V, map φ v ∈ W := fun v hv ↦
    Submodule.span_induction (fun g hg ↦ Submodule.subset_span ⟨g, hg, rfl⟩) (by simp)
      (fun a b _ _ ha hb ↦ by rw [map_add]; exact W.add_mem ha hb)
      (fun c a _ ha ↦ by
        rw [show map φ (c • a) = φ c • map φ a by simp [smul_eq_C_mul, map_C]]
        exact W.smul_mem (φ c) ha) hv
  let b := Module.finBasis F V
  let g : Fin (Module.finrank F V) → MvPolynomial σ F := fun i ↦ (b i).1
  have hg_ind : LinearIndependent F g := b.linearIndependent.map' V.subtype V.ker_subtype
  have hK_ind : LinearIndependent K (fun i ↦ map φ (g i)) := linearIndependent_map_of_field φ hg_ind
  have hW : W = Submodule.span K (Set.range fun i ↦ map φ (g i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨q, hq, rfl⟩
      have hval := congr_arg Subtype.val (b.sum_repr ⟨q, Submodule.subset_span hq⟩)
      push_cast at hval
      rw [← hval, map_sum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [show map φ (b.repr ⟨q, Submodule.subset_span hq⟩ i • g i) =
          φ (b.repr ⟨q, Submodule.subset_span hq⟩ i) • map φ (g i) by simp [smul_eq_C_mul, map_C]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hmap_mem (g i) (b i).2
  rw [hW, finrank_span_eq_card hK_ind, Fintype.card_fin]

/-- Active-variable upper bound on unshifted partial derivative rank. -/
theorem shiftedPartialRank_zero_le_choose_vars (κ : ℕ) (p : MvPolynomial σ F) :
    shiftedPartialRank κ 0 p ≤ p.vars.card.choose κ := by
  classical
  set G := (Finset.powersetCard κ p.vars).image fun S ↦ setPDeriv S p
  have hsub : shiftedPartialSpan κ 0 p ≤ Submodule.span F (G : Set (MvPolynomial σ F)) := by
    rw [shiftedPartialSpan_le_iff]; intro S β hS hβ
    have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hβ)
    subst hβ0; simp only [monomial_zero', map_one, one_mul]
    by_cases hsub' : S ⊆ p.vars
    · exact Submodule.subset_span
        (Finset.mem_image_of_mem _ (Finset.mem_powersetCard.mpr ⟨hsub', hS⟩))
    · rw [setPDeriv_eq_zero_of_not_subset_vars hsub']; exact Submodule.zero_mem _
  have : Module.Finite F (Submodule.span F (G : Set (MvPolynomial σ F))) :=
    Module.Finite.span_of_finite F G.finite_toSet
  calc shiftedPartialRank κ 0 p
      ≤ Module.finrank F (Submodule.span F (G : Set (MvPolynomial σ F))) :=
        Submodule.finrank_mono hsub
    _ ≤ G.card := (finrank_span_le_card (G : Set (MvPolynomial σ F))).trans_eq
        (by rw [Finset.toFinset_coe])
    _ ≤ (Finset.powersetCard κ p.vars).card := Finset.card_image_le
    _ = p.vars.card.choose κ := Finset.card_powersetCard κ p.vars

/-- Multiplying by any nonzero polynomial on disjoint variables never decreases
`shiftedPartialRank` (over any field, including finite fields). -/
theorem shiftedPartialRank_le_mul_disjoint {ν : Type w} [Finite σ] [Finite ν] (κ ℓ : ℕ)
    (p : MvPolynomial σ F) {q : MvPolynomial ν F} (hq : q ≠ 0) :
    shiftedPartialRank κ ℓ p ≤ shiftedPartialRank κ ℓ (rename Sum.inl p * rename Sum.inr q) := by
  classical
  have hqr : (rename (Sum.inr : ν → σ ⊕ ν) q : MvPolynomial (σ ⊕ ν) F) ≠ 0 := fun h ↦
    hq (rename_injective _ Sum.inr_injective (by simpa using h))
  let Φ : MvPolynomial σ F →ₗ[F] MvPolynomial (σ ⊕ ν) F :=
    (LinearMap.mulRight F (rename Sum.inr q)).comp (rename (R := F) Sum.inl).toLinearMap
  have hΦinj : Function.Injective Φ := fun _ _ hab ↦
    rename_injective _ Sum.inl_injective (mul_right_cancel₀ hqr hab)
  change Module.finrank F (shiftedPartialSpan κ ℓ p) ≤ _
  rw [(Submodule.equivMapOfInjective Φ hΦinj _).finrank_eq]
  refine Submodule.finrank_mono ?_
  rw [Submodule.map_le_iff_le_comap, shiftedPartialSpan_le_iff]; intro S β hS hβ
  rw [Submodule.mem_comap]
  change rename Sum.inl (monomial β 1 * setPDeriv S p) * rename Sum.inr q ∈
    shiftedPartialSpan κ ℓ (rename Sum.inl p * rename Sum.inr q)
  rw [map_mul, rename_monomial, mul_assoc, ← setPDeriv_rename Sum.inl_injective]
  have hdisj : Disjoint (S.image (Sum.inl : σ → σ ⊕ ν)) (rename Sum.inr q).vars :=
    Finset.disjoint_left.mpr fun _ hx hxv ↦ by
      rcases Finset.mem_image.mp hx with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp (vars_rename Sum.inr q hxv) with ⟨_, _, hb⟩; cases hb
  rw [← setPDeriv_mul_of_disjoint_vars _ hdisj]
  exact mem_shiftedPartialSpan ((Finset.card_image_of_injective S Sum.inl_injective).trans hS)
    (by rwa [Finsupp.degree_mapDomain])

/-- Bounded-degree factor inequality for cumulative shifted partial derivative rank. -/
theorem cumShiftedPartialRank_mul_le [Finite σ] (κ ℓ : ℕ) (p q : MvPolynomial σ F) :
    cumShiftedPartialRank κ ℓ (p * q) ≤ cumShiftedPartialRank κ (ℓ + q.totalDegree) p := by
  classical
  refine Submodule.finrank_mono ?_
  rw [cumShiftedPartialSpan_le_iff]; intro S β hS hβ
  rw [setPDeriv_mul, Finset.mul_sum]
  refine Submodule.sum_mem _ fun A hA ↦ ?_
  set r := setPDeriv (S \ A) q
  rw [r.as_sum, mul_comm (setPDeriv A p), ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem (cumShiftedPartialSpan κ (ℓ + q.totalDegree) p) fun γ hγ ↦ ?_
  have hγdeg : (β + γ).degree ≤ ℓ + q.totalDegree := by
    rw [map_add]
    have h1 : γ.degree ≤ q.totalDegree :=
      (le_totalDegree hγ).trans ((totalDegree_setPDeriv_le _ _).trans (Nat.sub_le _ _))
    omega
  rw [show monomial β (1 : F) * monomial γ (r.coeff γ) * setPDeriv A p =
      r.coeff γ • (monomial (β + γ) 1 * setPDeriv A p) by
    rw [monomial_mul_monomial, one_mul, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨A, β + γ, (Finset.card_le_card (Finset.mem_powerset.mp hA)).trans hS, hγdeg, rfl⟩)

theorem shiftedPartialRank_mul_le_cum [Finite σ] (κ ℓ : ℕ) (p q : MvPolynomial σ F) :
    shiftedPartialRank κ ℓ (p * q) ≤ cumShiftedPartialRank κ (ℓ + q.totalDegree) p :=
  (shiftedPartialRank_le_cum κ ℓ (p * q)).trans (cumShiftedPartialRank_mul_le κ ℓ p q)

/-- Exact Pascal recurrence for unshifted partial-derivative rank under multiplication by a fresh
indeterminate `y`. -/
theorem shiftedPartialRank_zero_mul_fresh_X [Finite σ] (κ : ℕ) (p : MvPolynomial σ F) :
    shiftedPartialRank (κ + 1) 0 (rename (Sum.inl : σ → σ ⊕ Unit) p * X (Sum.inr ())) =
      shiftedPartialRank (κ + 1) 0 p + shiftedPartialRank κ 0 p := by
  classical
  set y : MvPolynomial (σ ⊕ Unit) F := X (Sum.inr ())
  set V₁ := (shiftedPartialSpan (κ + 1) 0 p).map
    ((LinearMap.mulRight F y).comp (rename (R := F) Sum.inl).toLinearMap)
  set V₀ := (shiftedPartialSpan κ 0 p).map (rename (R := F) Sum.inl).toLinearMap
  have hspan : shiftedPartialSpan (κ + 1) 0 (rename Sum.inl p * y) = V₁ ⊔ V₀ := by
    apply le_antisymm
    · rw [shiftedPartialSpan_le_iff]; intro S β hS hβ
      have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hβ)
      subst hβ0; simp only [monomial_zero', map_one, one_mul]
      let S₀ : Finset σ := S.preimage Sum.inl Sum.inl_injective.injOn
      by_cases hy : Sum.inr () ∈ S
      · have hSeq : S = insert (Sum.inr ()) (S₀.image Sum.inl) := by
          ext z; cases z with
          | inl i => simp [S₀]
          | inr u => cases u; simp [hy]
        have hnot : Sum.inr () ∉ S₀.image (Sum.inl : σ → σ ⊕ Unit) := by simp
        have hcard : S₀.card = κ := by
          have := congr_arg Finset.card hSeq
          rw [hS, Finset.card_insert_of_notMem hnot,
            Finset.card_image_of_injective _ Sum.inl_injective] at this; omega
        have hdisj : Disjoint (S₀.image (Sum.inl : σ → σ ⊕ Unit)) y.vars := by simp [y, vars_X]
        have hnotp : Sum.inr () ∉ (rename (Sum.inl : σ → σ ⊕ Unit) (setPDeriv S₀ p)).vars :=
          fun hm ↦ by rcases Finset.mem_image.mp (vars_rename Sum.inl _ hm) with ⟨_, _, h⟩; cases h
        rw [hSeq, setPDeriv_insert hnot, setPDeriv_mul_of_disjoint_vars _ hdisj,
          setPDeriv_rename Sum.inl_injective, Derivation.leibniz,
          pderiv_eq_zero_of_notMem_vars hnotp, show pderiv (Sum.inr ()) y = 1 by simp [y],
          smul_zero, add_zero, smul_eq_mul, mul_one]
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem
          (by simpa using mem_shiftedPartialSpan (p := p) hcard (β := 0) le_rfl))
      · have hSeq : S = S₀.image Sum.inl := by
          ext z; cases z with
          | inl i => simp [S₀]
          | inr u => cases u; simp [hy]
        have hcard : S₀.card = κ + 1 := by
          have := congr_arg Finset.card hSeq
          rwa [hS, Finset.card_image_of_injective _ Sum.inl_injective, eq_comm] at this
        have hdisj : Disjoint (S₀.image (Sum.inl : σ → σ ⊕ Unit)) y.vars := by simp [y, vars_X]
        rw [hSeq, setPDeriv_mul_of_disjoint_vars _ hdisj, setPDeriv_rename Sum.inl_injective]
        exact Submodule.mem_sup_left (Submodule.mem_map_of_mem
          (by simpa using mem_shiftedPartialSpan (p := p) hcard (β := 0) le_rfl))
    · refine sup_le ?_ ?_
      · rw [Submodule.map_le_iff_le_comap, shiftedPartialSpan_le_iff]; intro S β hS hβ
        have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hβ)
        subst hβ0
        have hdisj : Disjoint (S.image (Sum.inl : σ → σ ⊕ Unit)) y.vars := by simp [y, vars_X]
        change rename Sum.inl (monomial 0 1 * setPDeriv S p) * y ∈
          shiftedPartialSpan (κ + 1) 0 (rename Sum.inl p * y)
        rw [monomial_zero', map_one, one_mul, ← setPDeriv_rename Sum.inl_injective,
          ← setPDeriv_mul_of_disjoint_vars _ hdisj]
        simpa using mem_shiftedPartialSpan (p := rename Sum.inl p * y)
          ((Finset.card_image_of_injective S Sum.inl_injective).trans hS) (β := 0) le_rfl
      · rw [Submodule.map_le_iff_le_comap, shiftedPartialSpan_le_iff]; intro S β hS hβ
        have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hβ)
        subst hβ0
        have hnot : Sum.inr () ∉ S.image (Sum.inl : σ → σ ⊕ Unit) := by simp
        have hdisj : Disjoint (S.image (Sum.inl : σ → σ ⊕ Unit)) y.vars := by simp [y, vars_X]
        have hnotp : Sum.inr () ∉ (rename (Sum.inl : σ → σ ⊕ Unit) (setPDeriv S p)).vars :=
          fun hm ↦ by rcases Finset.mem_image.mp (vars_rename Sum.inl _ hm) with ⟨_, _, h⟩; cases h
        have hderiv : setPDeriv (insert (Sum.inr ()) (S.image Sum.inl))
            (rename Sum.inl p * y) = rename Sum.inl (setPDeriv S p) := by
          rw [setPDeriv_insert hnot, setPDeriv_mul_of_disjoint_vars _ hdisj,
            setPDeriv_rename Sum.inl_injective, Derivation.leibniz,
            pderiv_eq_zero_of_notMem_vars hnotp, show pderiv (Sum.inr ()) y = 1 by simp [y]]
          simp
        have hcard : (insert (Sum.inr () : σ ⊕ Unit)
            (S.image (Sum.inl : σ → σ ⊕ Unit))).card = κ + 1 := by
          rw [Finset.card_insert_of_notMem hnot,
            Finset.card_image_of_injective S Sum.inl_injective, hS]
        have hmem := mem_shiftedPartialSpan (p := rename Sum.inl p * y) hcard (β := 0) le_rfl
        rw [monomial_zero', map_one, one_mul, hderiv] at hmem
        rw [Submodule.mem_comap]
        change rename Sum.inl (monomial 0 1 * setPDeriv S p) ∈
          shiftedPartialSpan (κ + 1) 0 (rename Sum.inl p * y)
        simpa using hmem
  have hdisjV : Disjoint V₁ V₀ := by
    rw [Submodule.disjoint_def]; rintro _ ⟨a, _, rfl⟩ ⟨b, _, heq⟩
    change rename Sum.inl b = rename Sum.inl a * y at heq
    have hspec := congr_arg (specializeRight (σ := σ) (0 : Unit → F)) heq
    simp only [map_mul, specializeRight_rename_inl, y, specializeRight_X_inr, Pi.zero_apply,
      map_zero, mul_zero] at hspec
    simpa [hspec] using heq.symm
  have hfin1 : Module.finrank F V₁ = shiftedPartialRank (κ + 1) 0 p :=
    (Submodule.equivMapOfInjective _ (fun _ _ h ↦
      rename_injective _ Sum.inl_injective (mul_right_cancel₀ (X_ne_zero _) h)) _).symm.finrank_eq
  have hfin0 : Module.finrank F V₀ = shiftedPartialRank κ 0 p :=
    (Submodule.equivMapOfInjective _ (rename_injective _ Sum.inl_injective) _).symm.finrank_eq
  have : Module.Finite F V₁ := Module.Finite.map _ _
  have : Module.Finite F V₀ := Module.Finite.map _ _
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₀
  rw [hdisjV.eq_bot, finrank_bot, add_zero, hfin1, hfin0] at hsup
  rw [shiftedPartialRank, hspan, hsup]

/-! ### Private-monomial diagonal-minor criterion and elementary product -/

/-- Any family of multivariate polynomials admitting private witness monomials (nonzero on the
diagonal, zero off the diagonal) is linearly independent over `F`. -/
theorem linearIndependent_of_private_monomial {I : Type*} {g : I → MvPolynomial σ F}
    (μ : I → σ →₀ ℕ) (hdiag : ∀ i, (g i).coeff (μ i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → (g i).coeff (μ j) = 0) : LinearIndependent F g := by
  classical
  rw [linearIndependent_iff']; intro s c hsum j hj
  have hc := congr_arg (fun q : MvPolynomial σ F ↦ q.coeff (μ j)) hsum
  rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finset.sum_eq_single j] at hc
  · rw [coeff_smul, smul_eq_mul] at hc; exact (mul_eq_zero.mp hc).resolve_right (hdiag j)
  · intro i _ hij; rw [coeff_smul, hoff i j hij, smul_zero]
  · intro hnot; exact (hnot hj).elim

/-- Private-monomial diagonal-minor lower bound for `shiftedPartialRank`. -/
theorem card_le_shiftedPartialRank_of_private_monomial {I : Type*} [Fintype I] [Finite σ]
    (κ ℓ : ℕ) (p : MvPolynomial σ F) (rowS : I → Finset σ) (rowβ : I → σ →₀ ℕ)
    (μ : I → σ →₀ ℕ) (hcard : ∀ i, (rowS i).card = κ) (hdeg : ∀ i, (rowβ i).degree ≤ ℓ)
    (hdiag : ∀ i, (monomial (rowβ i) 1 * setPDeriv (rowS i) p).coeff (μ i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → (monomial (rowβ i) 1 * setPDeriv (rowS i) p).coeff (μ j) = 0) :
    Fintype.card I ≤ shiftedPartialRank κ ℓ p := by
  let g : I → shiftedPartialSpan κ ℓ p := fun i ↦
    ⟨monomial (rowβ i) 1 * setPDeriv (rowS i) p, mem_shiftedPartialSpan (hcard i) (hdeg i)⟩
  have hind : LinearIndependent F g :=
    (linearIndependent_of_private_monomial μ hdiag hoff).of_comp (shiftedPartialSpan κ ℓ p).subtype
  exact hind.fintype_card_le_finrank

/-- Private-monomial diagonal-minor lower bound for `multilinearShiftedPartialRank`. -/
theorem card_le_multilinearShiftedPartialRank_of_private_monomial {I : Type*} [Fintype I]
    [Finite σ] (κ ℓ : ℕ) (p : MvPolynomial σ F) (rowS rowT : I → Finset σ) (μ : I → σ →₀ ℕ)
    (hcard : ∀ i, (rowS i).card = κ) (hdeg : ∀ i, (rowT i).card ≤ ℓ)
    (hdiag : ∀ i, (monomial (finsetMonomialExp (rowT i)) 1 * setPDeriv (rowS i) p).coeff (μ i) ≠ 0)
    (hoff : ∀ i j, i ≠ j →
      (monomial (finsetMonomialExp (rowT i)) 1 * setPDeriv (rowS i) p).coeff (μ j) = 0) :
    Fintype.card I ≤ multilinearShiftedPartialRank κ ℓ p := by
  let g : I → multilinearShiftedPartialSpan κ ℓ p := fun i ↦
    ⟨monomial (finsetMonomialExp (rowT i)) 1 * setPDeriv (rowS i) p,
      Submodule.subset_span ⟨rowS i, rowT i, hcard i, hdeg i, rfl⟩⟩
  have hind : LinearIndependent F g :=
    (linearIndependent_of_private_monomial μ hdiag hoff).of_comp
      (multilinearShiftedPartialSpan κ ℓ p).subtype
  exact hind.fintype_card_le_finrank

/-- Shifted partial derivative rank lower bound for the full monomial product `∏ i : σ, X i`. -/
theorem choose_le_shiftedPartialRank_prod_X [Fintype σ] (κ ℓ : ℕ) :
    (Fintype.card σ).choose κ ≤ shiftedPartialRank κ ℓ (∏ i : σ, (X i : MvPolynomial σ F)) := by
  classical
  let I := {S : Finset σ // S ∈ Finset.powersetCard κ (Finset.univ : Finset σ)}
  have hcardI : Fintype.card I = (Fintype.card σ).choose κ := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]
  rw [← hcardI, ← monomial_finsetMonomialExp (R := F) Finset.univ]
  refine (card_le_multilinearShiftedPartialRank_of_private_monomial κ ℓ _
    (fun S : I ↦ S.1) (fun _ ↦ ∅) (fun S : I ↦ finsetMonomialExp (Finset.univ \ S.1))
    (fun S ↦ (Finset.mem_powersetCard.mp S.2).2) (fun _ ↦ by simp)
    (fun S ↦ by simp [setPDeriv_finsetMonomial]) fun S T hST ↦ ?_).trans
    (multilinearShiftedPartialRank_le κ ℓ _)
  simp only [finsetMonomialExp_empty, monomial_zero', map_one, one_mul, setPDeriv_finsetMonomial,
    Finset.subset_univ, ↓reduceIte, coeff_monomial]
  refine ite_eq_right fun hEq ↦ hST <| Subtype.ext ?_
  rw [← compl_compl S.1, ← compl_compl T.1]
  exact congr_arg compl (finsetMonomialExp_injective hEq)

/-- Exact unshifted order-`κ` rank of the full monomial product `∏ i : σ, X i`. -/
theorem shiftedPartialRank_zero_prod_X [Fintype σ] (κ : ℕ) :
    shiftedPartialRank κ 0 (∏ i : σ, (X i : MvPolynomial σ F)) = (Fintype.card σ).choose κ := by
  classical
  refine le_antisymm ?_ (choose_le_shiftedPartialRank_prod_X κ 0)
  refine (shiftedPartialRank_zero_le_choose_vars κ _).trans
    (Nat.choose_le_choose κ ((Finset.card_le_card (Finset.subset_univ _)).trans_eq
      Finset.card_univ))

end Field

/-! ### Permanent polynomial identity minor and `(n.choose κ) ^ 2` lower bound -/

section Permanent

/-- A finite subset `M ⊆ Fin n × Fin n` is a partial matching if no two distinct elements share a
row or a column. -/
def IsPartialMatching {n : ℕ} (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.1 = e₂.1 → e₁ = e₂) ∧ (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁.2 = e₂.2 → e₁ = e₂)

/-- The generic `n × n` permanent polynomial over `R`, defined via `Matrix.permanent`. -/
noncomputable def permanentPoly (R : Type u) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R :=
  (Matrix.of fun i j : Fin n ↦ (X (i, j) : MvPolynomial (Fin n × Fin n) R)).permanent

/-- The complementary subpermanent polynomial on rows `Aᶜ` and columns `Bᶜ`. -/
noncomputable def subpermanentPoly (R : Type u) [CommSemiring R] {n : ℕ}
    (A B : Finset (Fin n)) : MvPolynomial (Fin n × Fin n) R :=
  ∑ e : ↥(Aᶜ : Finset (Fin n)) ≃ ↥(Bᶜ : Finset (Fin n)),
    monomial (finsetMonomialExp
      (Finset.univ.image fun i : ↥(Aᶜ : Finset (Fin n)) ↦ (i.1, (e i).1))) 1

theorem permanentPoly_eq_sum (R : Type u) [CommSemiring R] (n : ℕ) :
    permanentPoly R n = ∑ π : Equiv.Perm (Fin n),
      monomial (finsetMonomialExp (Finset.univ.image fun i : Fin n ↦ (i, π i))) 1 := by
  unfold permanentPoly Matrix.permanent
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [monomial_finsetMonomialExp, Finset.prod_image (fun _ _ _ _ h ↦ (Prod.mk.inj h).1)]
  simp only [Matrix.of_apply, Equiv.inv_apply]
  rw [← Equiv.prod_comp π fun i ↦ X (π⁻¹ i, i)]; simp

variable {R : Type u} [CommSemiring R]

theorem setPDeriv_permanentPoly_eq_zero_of_not_isPartialMatching {n : ℕ}
    {M : Finset (Fin n × Fin n)} (hM : ¬ IsPartialMatching M) :
    setPDeriv M (permanentPoly R n) = 0 := by
  rw [permanentPoly_eq_sum, map_sum]
  refine Finset.sum_eq_zero fun π _ ↦ ?_
  rw [setPDeriv_finsetMonomial, ite_eq_right]; intro hsub; apply hM
  refine ⟨fun e₁ h₁ e₂ h₂ hfst ↦ ?_, fun e₁ h₁ e₂ h₂ hsnd ↦ ?_⟩
  · rcases Finset.mem_image.mp (hsub h₁) with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp (hsub h₂) with ⟨_, _, rfl⟩; cases hfst; rfl
  · rcases Finset.mem_image.mp (hsub h₁) with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp (hsub h₂) with ⟨_, _, rfl⟩; cases π.injective hsnd; rfl

theorem setPDeriv_permanentPoly_of_isPartialMatching {n : ℕ} {M : Finset (Fin n × Fin n)}
    (hM : IsPartialMatching M) : setPDeriv M (permanentPoly R n) =
      subpermanentPoly R (M.image Prod.fst) (M.image Prod.snd) := by
  set A := M.image Prod.fst; set B := M.image Prod.snd
  have hrow_ex : ∀ a : ↥A, ∃ b : ↥B, (a.1, b.1) ∈ M := fun ⟨a, ha⟩ ↦ by
    rcases Finset.mem_image.mp ha with ⟨⟨i, j⟩, hij, rfl⟩
    exact ⟨⟨j, Finset.mem_image_of_mem Prod.snd hij⟩, hij⟩
  let mFun : ↥A → ↥B := fun a ↦ Classical.choose (hrow_ex a)
  have hmFun_mem : ∀ a : ↥A, (a.1, (mFun a).1) ∈ M := fun a ↦ Classical.choose_spec (hrow_ex a)
  let eM : ↥A ≃ ↥B := Equiv.ofBijective mFun
    ⟨fun a₁ a₂ h ↦ Subtype.ext (Prod.mk.inj (hM.2 _ (hmFun_mem a₁) _ (hmFun_mem a₂)
        (congr_arg Subtype.val h))).1,
      fun ⟨b, hb⟩ ↦ by
        rcases Finset.mem_image.mp hb with ⟨⟨i, j⟩, hij, rfl⟩
        let a : ↥A := ⟨i, Finset.mem_image_of_mem Prod.fst hij⟩
        exact ⟨a, Subtype.ext (Prod.mk.inj (hM.1 _ (hmFun_mem a) _ hij rfl)).2⟩⟩
  have heM_mem : ∀ a : ↥A, (a.1, (eM a).1) ∈ M := hmFun_mem
  let liftEquiv : (↥(Aᶜ : Finset (Fin n)) ≃ ↥(Bᶜ : Finset (Fin n))) → Equiv.Perm (Fin n) :=
    fun e ↦
      { toFun := fun x ↦ if hx : x ∈ A then (eM ⟨x, hx⟩).1 else (e ⟨x, Finset.mem_compl.mpr hx⟩).1
        invFun := fun y ↦ if hy : y ∈ B then (eM.symm ⟨y, hy⟩).1
          else (e.symm ⟨y, Finset.mem_compl.mpr hy⟩).1
        left_inv := fun x ↦ by
          by_cases hx : x ∈ A
          · simp [hx, (eM ⟨x, hx⟩).2]
          · simp [hx, Finset.mem_compl.mp (e ⟨x, Finset.mem_compl.mpr hx⟩).2]
        right_inv := fun y ↦ by
          by_cases hy : y ∈ B
          · simp [hy, (eM.symm ⟨y, hy⟩).2]
          · simp [hy, Finset.mem_compl.mp (e.symm ⟨y, Finset.mem_compl.mpr hy⟩).2] }
  have hlift_A : ∀ e (a : ↥A), liftEquiv e a.1 = (eM a).1 := fun e a ↦ by simp [liftEquiv, a.2]
  have hlift_Ac : ∀ e (i : ↥(Aᶜ : Finset (Fin n))), liftEquiv e i.1 = (e i).1 := fun e i ↦ by
    simp [liftEquiv, Finset.mem_compl.mp i.2]
  have hsub_iff : ∀ π : Equiv.Perm (Fin n),
      M ⊆ (Finset.univ.image fun i : Fin n ↦ (i, π i)) ↔ ∀ e ∈ M, π e.1 = e.2 := fun π ↦
    ⟨fun h ⟨i, j⟩ hij ↦ by
      rcases Finset.mem_image.mp (h hij) with ⟨_, _, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩; rfl,
      fun h ⟨i, j⟩ hij ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [h _ hij]⟩⟩
  rw [permanentPoly_eq_sum, map_sum]; simp_rw [setPDeriv_finsetMonomial]
  rw [← Finset.sum_filter, subpermanentPoly]
  refine (Finset.sum_bij (fun e _ ↦ liftEquiv e) ?_ ?_ ?_ ?_).symm
  · intro e _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsub_iff _).mpr fun ⟨i, j⟩ hij ↦ ?_⟩
    let a : ↥A := ⟨i, Finset.mem_image_of_mem Prod.fst hij⟩
    rw [hlift_A e a, (Prod.mk.inj (hM.1 _ (heM_mem a) _ hij rfl)).2]
  · intro e₁ _ e₂ _ hEq; ext i : 1
    exact Subtype.ext ((hlift_Ac e₁ i).symm.trans ((Equiv.congr_fun hEq i.1).trans (hlift_Ac e₂ i)))
  · intro π hπ; rw [Finset.mem_filter, hsub_iff] at hπ
    have hmap_Ac : ∀ i : ↥(Aᶜ : Finset (Fin n)), π i.1 ∈ Bᶜ := fun i ↦ by
      rw [Finset.mem_compl]; intro hb
      rcases Finset.mem_image.mp hb with ⟨⟨i', j'⟩, hij', hjeq⟩
      exact (Finset.mem_compl.mp i.2)
        (π.injective ((hπ.2 _ hij').trans hjeq) ▸ Finset.mem_image_of_mem Prod.fst hij')
    let f : ↥(Aᶜ : Finset (Fin n)) → ↥(Bᶜ : Finset (Fin n)) := fun i ↦ ⟨π i.1, hmap_Ac i⟩
    have hcard_eq : Fintype.card ↥(Aᶜ : Finset (Fin n)) = Fintype.card ↥(Bᶜ : Finset (Fin n)) := by
      rw [Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Finset.card_compl,
        Finset.card_image_of_injOn fun _ h₁ _ h₂ h ↦ hM.1 _ h₁ _ h₂ h,
        Finset.card_image_of_injOn fun _ h₁ _ h₂ h ↦ hM.2 _ h₁ _ h₂ h]
    let e : ↥(Aᶜ : Finset (Fin n)) ≃ ↥(Bᶜ : Finset (Fin n)) := Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr
        ⟨fun _ _ h ↦ Subtype.ext (π.injective (congr_arg Subtype.val h)), hcard_eq⟩)
    refine ⟨e, Finset.mem_univ _, Equiv.ext fun x ↦ ?_⟩
    by_cases hx : x ∈ A
    · exact (hlift_A e ⟨x, hx⟩).trans (hπ.2 _ (hmFun_mem ⟨x, hx⟩)).symm
    · exact hlift_Ac e ⟨x, Finset.mem_compl.mpr hx⟩
  · intro e _; apply congr_arg (fun S ↦ monomial (finsetMonomialExp S) (1 : R)); ext ⟨i, j⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨k, rfl, rfl⟩
      exact ⟨⟨k.1, rfl, hlift_Ac e k⟩,
        fun hm ↦ (Finset.mem_compl.mp k.2) (Finset.mem_image_of_mem Prod.fst hm)⟩
    · rintro ⟨⟨k, rfl, rfl⟩, hnot⟩
      by_cases hk : k ∈ A
      · exact (hnot (by have := heM_mem ⟨k, hk⟩; rwa [← hlift_A e ⟨k, hk⟩] at this)).elim
      · exact ⟨⟨k, Finset.mem_compl.mpr hk⟩, rfl, (hlift_Ac e ⟨k, Finset.mem_compl.mpr hk⟩).symm⟩

/-- Canonical witness monomial attached to equal-size row and column sets `A, B ⊆ Fin n`. -/
noncomputable def subpermanentWitnessExp {n : ℕ} (A B : Finset (Fin n))
    (hcard : A.card = B.card) : Fin n × Fin n →₀ ℕ :=
  have hc : (Aᶜ : Finset (Fin n)).card = (Bᶜ : Finset (Fin n)).card := by
    rw [Finset.card_compl, Finset.card_compl, hcard]
  let e₀ : ↥(Aᶜ : Finset (Fin n)) ≃ ↥(Bᶜ : Finset (Fin n)) :=
    ((Aᶜ.orderIsoOfFin rfl).symm.toEquiv.trans (Equiv.cast (by rw [hc]))).trans
      (Bᶜ.orderIsoOfFin rfl).toEquiv
  finsetMonomialExp (Finset.univ.image fun i : ↥(Aᶜ : Finset (Fin n)) ↦ (i.1, (e₀ i).1))

/-- Exact identity minor for `subpermanentPoly` over any commutative semiring `R`. -/
theorem permanentPoly_minor_coeff {n : ℕ} {A B A' B' : Finset (Fin n)}
    (hAB : A.card = B.card) (hA'B' : A'.card = B'.card) :
    (subpermanentPoly R A B).coeff (subpermanentWitnessExp A' B' hA'B') =
      if A = A' ∧ B = B' then 1 else 0 := by
  rw [subpermanentPoly, coeff_sum]
  split_ifs with hEq
  · rcases hEq with ⟨rfl, rfl⟩
    have hc : (Aᶜ : Finset (Fin n)).card = (Bᶜ : Finset (Fin n)).card := by
      rw [Finset.card_compl, Finset.card_compl, hAB]
    let e₀ : ↥(Aᶜ : Finset (Fin n)) ≃ ↥(Bᶜ : Finset (Fin n)) :=
      ((Aᶜ.orderIsoOfFin rfl).symm.toEquiv.trans (Equiv.cast (by rw [hc]))).trans
        (Bᶜ.orderIsoOfFin rfl).toEquiv
    rw [Finset.sum_eq_single e₀]
    · simp [subpermanentWitnessExp, e₀]
    · intro e _ he; rw [coeff_monomial, ite_eq_right]; intro hmon
      have hset := finsetMonomialExp_injective hmon
      apply he; ext i
      have hmem : (i.1, (e i).1) ∈
          Finset.univ.image (fun k : ↥(Aᶜ : Finset (Fin n)) ↦ (k.1, (e₀ k).1)) :=
        hset ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)
      rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
      have hki : k = i := Subtype.ext (Prod.mk.inj hk).1
      subst hki; exact congr_arg Fin.val (Prod.mk.inj hk).2.symm
    · intro h; exact (h (Finset.mem_univ e₀)).elim
  · refine Finset.sum_eq_zero fun e _ ↦ ?_
    rw [coeff_monomial, ite_eq_right]; intro hmon
    have hset := finsetMonomialExp_injective hmon
    apply hEq
    have hfst : Aᶜ = A'ᶜ := by
      have := congr_arg (fun S : Finset (Fin n × Fin n) ↦ S.image Prod.fst) hset
      ext x; simpa [subpermanentWitnessExp, Finset.image_image, Function.comp_def] using
        Finset.ext_iff.mp this x
    have hsnd : Bᶜ = B'ᶜ := by
      have := congr_arg (fun S : Finset (Fin n × Fin n) ↦ S.image Prod.snd) hset
      ext y
      have hy := Finset.ext_iff.mp this y
      simp only [Finset.image_image, Function.comp_def, Finset.mem_image,
        Finset.mem_univ, true_and] at hy
      refine ⟨fun hBy ↦ ?_, fun hB'y ↦ ?_⟩
      · rcases hy.mp ⟨e.symm ⟨y, hBy⟩, by simp⟩ with ⟨_, rfl⟩; exact Finset.coe_mem _
      · have hc' : (A'ᶜ : Finset (Fin n)).card = (B'ᶜ : Finset (Fin n)).card := by
          rw [Finset.card_compl, Finset.card_compl, hA'B']
        let e₀' : ↥(A'ᶜ : Finset (Fin n)) ≃ ↥(B'ᶜ : Finset (Fin n)) :=
          ((A'ᶜ.orderIsoOfFin rfl).symm.toEquiv.trans (Equiv.cast (by rw [hc']))).trans
            (B'ᶜ.orderIsoOfFin rfl).toEquiv
        rcases hy.mpr ⟨e₀'.symm ⟨y, hB'y⟩, by simp [e₀']⟩ with ⟨i, rfl⟩; exact (e i).2
    exact ⟨by rw [← compl_compl A, ← compl_compl A', hfst],
      by rw [← compl_compl B, ← compl_compl B', hsnd]⟩

private noncomputable def canonicalMatching {n : ℕ} (A B : Finset (Fin n)) (h : A.card = B.card) :
    Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin A.card)).image fun k ↦
    ((A.orderIsoOfFin rfl k).1, (B.orderIsoOfFin h.symm k).1)

/-- Linear independence of all `(n - κ) × (n - κ)` subpermanent polynomials over any field `F`. -/
theorem linearIndependent_subpermanentPoly (F : Type u) [Field F] (n κ : ℕ) :
    LinearIndependent F
      (fun P : {P : Finset (Fin n) × Finset (Fin n) //
        P.1 ∈ Finset.powersetCard κ Finset.univ ∧ P.2 ∈ Finset.powersetCard κ Finset.univ} ↦
        subpermanentPoly F P.1.1 P.1.2) := by
  have hcard : ∀ P : {P : Finset (Fin n) × Finset (Fin n) //
      P.1 ∈ Finset.powersetCard κ Finset.univ ∧ P.2 ∈ Finset.powersetCard κ Finset.univ},
      P.1.1.card = P.1.2.card := fun P ↦
    (Finset.mem_powersetCard.mp P.2.1).2.trans (Finset.mem_powersetCard.mp P.2.2).2.symm
  refine linearIndependent_of_private_monomial
    (fun P ↦ subpermanentWitnessExp P.1.1 P.1.2 (hcard P))
    (fun P ↦ by simp [permanentPoly_minor_coeff (hcard P) (hcard P)]) fun P Q hPQ ↦ ?_
  rw [permanentPoly_minor_coeff (hcard P) (hcard Q), ite_eq_right]
  exact fun ⟨h1, h2⟩ ↦ hPQ (Subtype.ext (Prod.ext h1 h2))

/-- Shifted partial derivative lower bound `(n.choose κ) ^ 2` for `permanentPoly F n` over any
field `F` and every shift budget `ℓ : ℕ`. -/
theorem choose_sq_le_shiftedPartialRank_permanentPoly (F : Type u) [Field F] (n κ ℓ : ℕ) :
    (n.choose κ) ^ 2 ≤ shiftedPartialRank κ ℓ (permanentPoly F n) := by
  let Idx := {P : Finset (Fin n) × Finset (Fin n) //
    P ∈ Finset.powersetCard κ Finset.univ ×ˢ Finset.powersetCard κ Finset.univ}
  have hIdx : Fintype.card Idx = (n.choose κ) ^ 2 := by
    rw [Fintype.card_coe, Finset.card_product, Finset.card_powersetCard, Finset.card_fin, sq]
  have hAB : ∀ P : Idx, P.1.1.card = P.1.2.card := fun P ↦
    (Finset.mem_powersetCard.mp (Finset.mem_product.mp P.2).1).2.trans
      (Finset.mem_powersetCard.mp (Finset.mem_product.mp P.2).2).2.symm
  have hpm : ∀ P : Idx, IsPartialMatching (canonicalMatching P.1.1 P.1.2 (hAB P)) := fun P ↦ by
    refine ⟨fun _ h₁ _ h₂ hf ↦ ?_, fun _ h₁ _ h₂ hs ↦ ?_⟩
    · rcases Finset.mem_image.mp h₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h₂ with ⟨_, _, rfl⟩
      rw [(P.1.1.orderIsoOfFin rfl).injective (Subtype.ext hf)]
    · rcases Finset.mem_image.mp h₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h₂ with ⟨_, _, rfl⟩
      rw [(P.1.2.orderIsoOfFin (hAB P).symm).injective (Subtype.ext hs)]
  have hfst : ∀ P : Idx, (canonicalMatching P.1.1 P.1.2 (hAB P)).image Prod.fst = P.1.1 :=
    fun P ↦ by
      ext x; simp only [canonicalMatching, Finset.image_image, Function.comp_def,
        Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨k, hk⟩ ↦ hk ▸ (P.1.1.orderIsoOfFin rfl k).2,
        fun hx ↦ ⟨(P.1.1.orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp⟩⟩
  have hsnd : ∀ P : Idx, (canonicalMatching P.1.1 P.1.2 (hAB P)).image Prod.snd = P.1.2 :=
    fun P ↦ by
      ext y; simp only [canonicalMatching, Finset.image_image, Function.comp_def,
        Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨k, hk⟩ ↦ hk ▸ (P.1.2.orderIsoOfFin (hAB P).symm k).2,
        fun hy ↦ ⟨(P.1.2.orderIsoOfFin (hAB P).symm).symm ⟨y, hy⟩, by simp⟩⟩
  rw [← hIdx]
  refine card_le_shiftedPartialRank_of_private_monomial κ ℓ (permanentPoly F n)
    (fun P : Idx ↦ canonicalMatching P.1.1 P.1.2 (hAB P)) (fun _ ↦ 0)
    (fun P : Idx ↦ subpermanentWitnessExp P.1.1 P.1.2 (hAB P))
    (fun P ↦ by
      rw [canonicalMatching, Finset.card_image_of_injective _ (fun _ _ hEq ↦
        (P.1.1.orderIsoOfFin rfl).injective (Subtype.ext (Prod.mk.inj hEq).1)), Finset.card_fin,
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp P.2).1).2])
    (fun _ ↦ by simp)
    (fun P ↦ by simp [setPDeriv_permanentPoly_of_isPartialMatching (hpm P), hfst P, hsnd P,
      permanentPoly_minor_coeff (hAB P) (hAB P)])
    fun P Q hPQ ↦ ?_
  simp only [monomial_zero', map_one, one_mul,
    setPDeriv_permanentPoly_of_isPartialMatching (hpm P), hfst P, hsnd P,
    permanentPoly_minor_coeff (hAB P) (hAB Q)]
  exact ite_eq_right fun ⟨h1, h2⟩ ↦ hPQ (Subtype.ext (Prod.ext h1 h2))

/-- Exact unshifted order-`κ` partial-derivative rank of `permanentPoly F n` over any field `F`. -/
theorem shiftedPartialRank_zero_permanentPoly (F : Type u) [Field F] (n κ : ℕ) :
    shiftedPartialRank κ 0 (permanentPoly F n) = (n.choose κ) ^ 2 := by
  classical
  apply le_antisymm _ (choose_sq_le_shiftedPartialRank_permanentPoly F n κ 0)
  set P := Finset.powersetCard κ (Finset.univ : Finset (Fin n)) ×ˢ
    Finset.powersetCard κ (Finset.univ : Finset (Fin n))
  set G := P.image fun x ↦ subpermanentPoly F x.1 x.2
  have hsub : shiftedPartialSpan κ 0 (permanentPoly F n) ≤
      Submodule.span F (G : Set (MvPolynomial (Fin n × Fin n) F)) := by
    rw [shiftedPartialSpan_le_iff]; intro M β hM hβ
    have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hβ)
    subst hβ0; simp only [monomial_zero', map_one, one_mul]
    by_cases hmatch : IsPartialMatching M
    · rw [setPDeriv_permanentPoly_of_isPartialMatching hmatch]
      refine Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ (a := (M.image Prod.fst, M.image Prod.snd)) ?_))
      simp [P, Finset.mem_powersetCard,
        Finset.card_image_of_injOn fun _ h₁ _ h₂ h ↦ hmatch.1 _ h₁ _ h₂ h,
        Finset.card_image_of_injOn fun _ h₁ _ h₂ h ↦ hmatch.2 _ h₁ _ h₂ h, hM]
    · rw [setPDeriv_permanentPoly_eq_zero_of_not_isPartialMatching hmatch]
      exact Submodule.zero_mem _
  have : Module.Finite F (Submodule.span F (G : Set (MvPolynomial (Fin n × Fin n) F))) :=
    Module.Finite.span_of_finite F G.finite_toSet
  calc shiftedPartialRank κ 0 (permanentPoly F n)
      ≤ Module.finrank F (Submodule.span F (G : Set (MvPolynomial (Fin n × Fin n) F))) :=
        Submodule.finrank_mono hsub
    _ ≤ G.card := (finrank_span_le_card (G : Set (MvPolynomial (Fin n × Fin n) F))).trans_eq
        (by rw [Finset.toFinset_coe])
    _ ≤ P.card := Finset.card_image_le
    _ = (n.choose κ) ^ 2 := by
      rw [Finset.card_product, Finset.card_powersetCard, Finset.card_fin, sq]

end Permanent

/-! ### Selector-coupled disjoint-block products and signed identity minor -/

section SelectorProduct

variable {R : Type u} [CommRing R] {υ : Type v} {ι : Type w}

/-- Selector-coupled block product `∏ c : ι, (1 - z_c * P_c(u))` in `MvPolynomial (υ ⊕ ι) R`. -/
noncomputable def selectorProduct [Fintype ι] (P : ι → MvPolynomial υ R) :
    MvPolynomial (υ ⊕ ι) R :=
  ∏ c : ι, (1 - X (Sum.inr c) * rename Sum.inl (P c))

/-- Selector variable set `{Sum.inr c | c ∈ I}` corresponding to `I : Finset ι`. -/
def selectorSet (I : Finset ι) : Finset (υ ⊕ ι) :=
  I.map ⟨Sum.inr, Sum.inr_injective⟩

@[simp] theorem card_selectorSet (I : Finset ι) : (selectorSet (υ := υ) I).card = I.card :=
  Finset.card_map _

private theorem vars_prod_subset {α τ : Type*} [DecidableEq τ] (s : Finset α)
    {f : α → MvPolynomial τ R} : (∏ c ∈ s, f c).vars ⊆ s.biUnion fun c ↦ (f c).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.biUnion_insert]
    exact (vars_mul _ _).trans (Finset.union_subset_union_right ih)

/-- Exact selector-derivative formula for `selectorProduct P`. -/
theorem setPDeriv_selectorSet_selectorProduct [Fintype ι] [DecidableEq ι]
    (P : ι → MvPolynomial υ R) (I : Finset ι) :
    setPDeriv (selectorSet I) (selectorProduct P) =
      C ((-1 : R) ^ I.card) * (∏ c ∈ I, rename Sum.inl (P c)) *
        ∏ c ∈ Iᶜ, (1 - X (Sum.inr c) * rename Sum.inl (P c)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  classical
  induction I using Finset.induction_on with
  | empty => simp [selectorSet, selectorProduct]
  | insert a I ha ih =>
    have ha' : (Sum.inr a : υ ⊕ ι) ∉ selectorSet (υ := υ) I := by simp [selectorSet, ha]
    have hcompl : Iᶜ = insert a (insert a I)ᶜ := by
      ext c; simp only [Finset.mem_compl, Finset.mem_insert]; by_cases hc : c = a <;> simp [hc, ha]
    have ha_nc : a ∉ (insert a I)ᶜ := by simp
    have hnot_inl : ∀ q : MvPolynomial υ R,
        (Sum.inr a : υ ⊕ ι) ∉ (rename (Sum.inl : υ → υ ⊕ ι) q).vars := fun q hm ↦ by
      rcases Finset.mem_image.mp (vars_rename Sum.inl q hm) with ⟨_, _, hv⟩; cases hv
    have hnot_left : (Sum.inr a : υ ⊕ ι) ∉
        (C ((-1 : R) ^ I.card) * ∏ c ∈ I, rename (Sum.inl : υ → υ ⊕ ι) (P c)).vars := fun hm ↦ by
      rcases Finset.mem_union.mp (vars_mul _ _ hm) with hC | hP
      · rw [vars_C] at hC; exact Finset.notMem_empty _ hC
      · rcases Finset.mem_biUnion.mp (vars_prod_subset _ hP) with ⟨c, _, hc⟩
        exact hnot_inl (P c) hc
    have hnot_rest : (Sum.inr a : υ ⊕ ι) ∉
        (∏ c ∈ (insert a I)ᶜ, (1 - X (Sum.inr c) * rename (Sum.inl : υ → υ ⊕ ι) (P c))).vars := by
      intro hm
      rcases Finset.mem_biUnion.mp (vars_prod_subset _ hm) with ⟨c, hc, hcv⟩
      have hca : c ≠ a := fun h ↦ ha_nc (h ▸ hc)
      rw [sub_eq_add_neg, neg_eq_neg_one_mul] at hcv
      rcases Finset.mem_union.mp (vars_add_subset _ _ hcv) with h1 | h2
      · rw [← C_1, vars_C] at h1; exact Finset.notMem_empty _ h1
      · rcases Finset.mem_union.mp (vars_mul _ _ h2) with hn | h2
        · rw [show (-1 : MvPolynomial (υ ⊕ ι) R) = C (-1) by simp, vars_C] at hn
          exact Finset.notMem_empty _ hn
        · rcases Finset.mem_union.mp (vars_mul _ _ h2) with hx | hp
          · rw [vars_X] at hx; exact hca (Sum.inr_injective (Finset.mem_singleton.mp hx).symm)
          · exact hnot_inl (P c) hp
    have hfac : pderiv (Sum.inr a) (1 - X (Sum.inr a) * rename (Sum.inl : υ → υ ⊕ ι) (P a)) =
        - rename Sum.inl (P a) := by
      rw [map_sub, ← C_1, pderiv_C, zero_sub, Derivation.leibniz,
        pderiv_eq_zero_of_notMem_vars (hnot_inl (P a)), pderiv_X_self]
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add]
    have hsel_ins : selectorSet (υ := υ) (insert a I) = insert (Sum.inr a) (selectorSet I) := by
      simp [selectorSet]
    rw [hsel_ins, setPDeriv_insert ha', ih, hcompl, Finset.prod_insert ha_nc, ← mul_assoc,
      mul_right_comm _ (1 - X (Sum.inr a) * rename Sum.inl (P a)), Derivation.leibniz,
      pderiv_eq_zero_of_notMem_vars (fun hm ↦
        (Finset.mem_union.mp (vars_mul _ _ hm)).elim hnot_left hnot_rest),
      hfac, smul_zero, add_zero, smul_eq_mul, Finset.card_insert_of_notMem ha,
      Finset.prod_insert ha, pow_succ, map_mul, map_neg, map_one]
    ring

private theorem coeff_prod_disjoint_blocks [DecidableEq ι] [DecidableEq υ]
    {P : ι → MvPolynomial υ R} {block : ι → Finset υ} {U : Finset ι}
    (hdisj : (U : Set ι).Pairwise fun c₁ c₂ ↦ Disjoint (block c₁) (block c₂))
    (hvars : ∀ c ∈ U, (P c).vars ⊆ block c) {I : Finset ι} (hIU : I ⊆ U)
    (tag : ι → υ →₀ ℕ) (htag_supp : ∀ c ∈ U, (tag c).support ⊆ block c) :
    (∏ c ∈ I, P c).coeff (∑ c ∈ U, tag c) =
      if ∀ c ∈ U \ I, tag c = 0 then ∏ c ∈ I, (P c).coeff (tag c) else 0 := by
  have hsum_app : ∀ (S : Finset ι) (x : υ), (∑ c ∈ S, tag c) x = ∑ c ∈ S, tag c x := fun S x ↦ by
    induction S using Finset.induction_on with
    | empty => simp
    | insert b S hb ihS => rw [Finset.sum_insert hb, Finsupp.add_apply, ihS, Finset.sum_insert hb]
  split_ifs with hzero
  · have hsum_eq : ∑ c ∈ U, tag c = ∑ c ∈ I, tag c := by
      rw [← Finset.sdiff_union_of_subset hIU, Finset.sum_union disjoint_sdiff_self_left,
        Finset.sum_eq_zero hzero, zero_add]
    rw [hsum_eq]; clear hzero hsum_eq
    induction I using Finset.induction_on with
    | empty => simp
    | insert a I ha ih =>
      have haU : a ∈ U := hIU (Finset.mem_insert_self a I)
      have hIU' : I ⊆ U := (Finset.subset_insert a I).trans hIU
      have hdisj_a : ∀ c ∈ I, Disjoint (block a) (block c) := fun c hc ↦
        hdisj haU (hIU' hc) fun h ↦ ha (h ▸ hc)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, coeff_mul,
        Finset.sum_eq_single (tag a, ∑ c ∈ I, tag c)]
      · rw [ih hIU']
      · rintro ⟨m₁, m₂⟩ hanti hne; rw [Finset.mem_antidiagonal] at hanti
        by_cases h1 : (P a).coeff m₁ = 0
        · simp [h1]
        · by_cases h2 : (∏ c ∈ I, P c).coeff m₂ = 0
          · simp [h2]
          · exfalso; apply hne
            have hm₁_supp : m₁.support ⊆ block a := fun v hv ↦
              hvars a haU (by rw [vars_def, Multiset.mem_toFinset, mem_degrees]; exact ⟨m₁, h1, hv⟩)
            have hm₂_disj : ∀ v ∈ block a, m₂ v = 0 := fun v hva ↦ by
              by_contra hmv
              have hvp : v ∈ (∏ c ∈ I, P c).vars := by
                rw [vars_def, Multiset.mem_toFinset, mem_degrees]
                exact ⟨m₂, h2, Finsupp.mem_support_iff.mpr hmv⟩
              rcases Finset.mem_biUnion.mp (vars_prod_subset _ hvp) with ⟨c, hc, hvc⟩
              exact Finset.disjoint_left.mp (hdisj_a c hc) hva (hvars c (hIU' hc) hvc)
            have hsum_disj : ∀ v ∈ block a, (∑ c ∈ I, tag c) v = 0 := fun v hva ↦ by
              rw [hsum_app]
              exact Finset.sum_eq_zero fun c hc ↦ Finsupp.notMem_support_iff.mp fun hvc ↦
                Finset.disjoint_left.mp (hdisj_a c hc) hva (htag_supp c (hIU' hc) hvc)
            have hm₁_eq : m₁ = tag a := by
              ext v; have hv := DFunLike.congr_fun hanti v
              simp only [Finsupp.add_apply] at hv
              by_cases hva : v ∈ block a
              · rwa [hm₂_disj v hva, hsum_disj v hva, add_zero, add_zero] at hv
              · rw [Finsupp.notMem_support_iff.mp fun h ↦ hva (hm₁_supp h),
                  Finsupp.notMem_support_iff.mp fun h ↦ hva (htag_supp a haU h)]
            subst hm₁_eq; exact Prod.ext rfl (add_left_cancel hanti)
      · intro hnot; exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim
  · push Not at hzero; obtain ⟨c₀, hc₀, htag_ne⟩ := hzero; rw [Finset.mem_sdiff] at hc₀
    obtain ⟨v, hv⟩ : ∃ v, tag c₀ v ≠ 0 := by
      by_contra h; push Not at h; exact htag_ne (Finsupp.ext h)
    have hvb : v ∈ block c₀ := htag_supp c₀ hc₀.1 (Finsupp.mem_support_iff.mpr hv)
    have hvsum : (∑ c ∈ U, tag c) v ≠ 0 := by
      rw [hsum_app]
      exact ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero hv)
        (Finset.single_le_sum (f := fun c ↦ tag c v) (fun _ _ ↦ Nat.zero_le _) hc₀.1))
    by_contra hne
    have hvp : v ∈ (∏ c ∈ I, P c).vars := by
      rw [vars_def, Multiset.mem_toFinset, mem_degrees]
      exact ⟨_, hne, Finsupp.mem_support_iff.mpr hvsum⟩
    rcases Finset.mem_biUnion.mp (vars_prod_subset _ hvp) with ⟨c, hc, hvc⟩
    exact Finset.disjoint_left.mp (hdisj hc₀.1 (hIU hc) fun h ↦ hc₀.2 (h ▸ hc))
      hvb (hvars c (hIU hc) hvc)

/-- Exact signed diagonal-minor identity for `selectorProduct P` over any commutative ring `R`. -/
theorem selectorProduct_minor_coeff [Fintype ι] [DecidableEq ι] {P : ι → MvPolynomial υ R}
    {block : ι → Finset υ} {U : Finset ι}
    (hdisj : (U : Set ι).Pairwise fun c₁ c₂ ↦ Disjoint (block c₁) (block c₂))
    (hvars : ∀ c ∈ U, (P c).vars ⊆ block c) (hconst : ∀ c ∈ U, (P c).coeff 0 = 0)
    {tag : ι → υ →₀ ℕ} (htag_ne : ∀ c ∈ U, tag c ≠ 0)
    (htag_supp : ∀ c ∈ U, (tag c).support ⊆ block c)
    {I J : Finset ι} (hIU : I ⊆ U) (hJU : J ⊆ U) :
    (setPDeriv (selectorSet I) (selectorProduct P)).coeff
        ((∑ c ∈ J, tag c).mapDomain Sum.inl) =
      if I = J then (-1 : R) ^ I.card * ∏ c ∈ I, (P c).coeff (tag c) else 0 := by
  classical
  have hspec_coeff : ∀ (q : MvPolynomial (υ ⊕ ι) R) (μ : υ →₀ ℕ),
      (specializeRight (0 : ι → R) q).coeff μ = q.coeff (μ.mapDomain Sum.inl) := by
    intro q; induction q using MvPolynomial.induction_on with
    | C a =>
      intro μ
      change (specializeRight (0 : ι → R) (algebraMap R _ a)).coeff μ = (C a).coeff _
      rw [AlgHom.commutes]
      change (C a : MvPolynomial υ R).coeff μ = (C a).coeff _
      rw [coeff_C, coeff_C]
      by_cases hμ : μ = 0
      · subst hμ; simp
      · have hm : (0 : (υ ⊕ ι) →₀ ℕ) ≠ μ.mapDomain Sum.inl := fun h ↦
          hμ (Finsupp.mapDomain_injective Sum.inl_injective (by simpa using h.symm))
        simp [Ne.symm hμ, hm]
    | add _ _ h₁ h₂ => intro μ; simp [h₁ μ, h₂ μ]
    | mul_X p s ih =>
      intro μ; rw [map_mul]
      cases s with
      | inl v =>
        have hmap : ∀ (ξ : υ →₀ ℕ) (w : υ),
            ξ.mapDomain (Sum.inl : υ → υ ⊕ ι) (Sum.inl w) = ξ w := fun ξ w ↦ by
          induction ξ using Finsupp.induction with
          | zero => simp
          | single_add a b s _ _ ih =>
            simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.single_apply, ih]
        rw [specializeRight_X_inl, coeff_mul_X', coeff_mul_X']
        by_cases hv : v ∈ μ.support
        · have hv' : Sum.inl v ∈ (μ.mapDomain (Sum.inl : υ → υ ⊕ ι)).support := by
            simpa [hmap] using hv
          have hsub : (μ - Finsupp.single v 1).mapDomain (Sum.inl : υ → υ ⊕ ι) =
              μ.mapDomain Sum.inl - Finsupp.single (Sum.inl v) 1 := by
            ext (w | c)
            · simp [hmap, Finsupp.single_apply]
            · simp [Finsupp.mapDomain_of_notMem_range]
          simp only [hv, hv', ↓reduceIte]; rw [ih, hsub]
        · have hv' : Sum.inl v ∉ (μ.mapDomain (Sum.inl : υ → υ ⊕ ι)).support := by
            simpa [hmap] using hv
          simp only [hv, hv', ↓reduceIte]
      | inr c =>
        rw [specializeRight_X_inr, Pi.zero_apply, map_zero, mul_zero, coeff_mul_X']
        have hnot : (Sum.inr c : υ ⊕ ι) ∉ (μ.mapDomain (Sum.inl : υ → υ ⊕ ι)).support := by
          rw [Finsupp.mem_support_iff, Finsupp.mapDomain_of_notMem_range]
          · exact not_not.mpr rfl
          · rintro ⟨_, hv⟩; cases hv
        rw [ite_eq_right hnot]; rfl
  rw [← hspec_coeff, setPDeriv_selectorSet_selectorProduct]
  have hspec_rhs : specializeRight (0 : ι → R)
      (C ((-1 : R) ^ I.card) * (∏ c ∈ I, rename Sum.inl (P c)) *
        ∏ c ∈ Iᶜ, (1 - X (Sum.inr c) * rename Sum.inl (P c))) =
      C ((-1 : R) ^ I.card) * ∏ c ∈ I, P c := by
    simp [map_prod, show ∀ c : ι, specializeRight (0 : ι → R)
      (1 - X (Sum.inr c) * rename Sum.inl (P c)) = 1 from fun _ ↦ by simp [specializeRight_X_inr]]
  rw [hspec_rhs, coeff_C_mul]
  let tagJ : ι → υ →₀ ℕ := fun c ↦ if c ∈ J then tag c else 0
  have hsumJ : ∑ c ∈ J, tag c = ∑ c ∈ U, tagJ c := by
    rw [← Finset.sum_filter]; congr 1; ext c
    simp only [Finset.mem_filter, iff_and_self]; exact fun hc ↦ hJU hc
  have htagJ_supp : ∀ c ∈ U, (tagJ c).support ⊆ block c := fun c hc ↦ by
    dsimp [tagJ]; split_ifs <;> [exact htag_supp c hc; simp]
  rw [hsumJ, coeff_prod_disjoint_blocks hdisj hvars hIU tagJ htagJ_supp]
  by_cases hJI : J ⊆ I
  · rw [ite_eq_left fun c hc ↦ by
      have hcJ : c ∉ J := fun h ↦ (Finset.mem_sdiff.mp hc).2 (hJI h); simp [tagJ, hcJ]]
    by_cases hIJ : I = J
    · subst hIJ; rw [ite_eq_left rfl]
      congr 1; exact Finset.prod_congr rfl fun c hc ↦ by simp [tagJ, hc]
    · rw [ite_eq_right hIJ]
      obtain ⟨c₀, hc₀I, hc₀J⟩ : ∃ c₀ ∈ I, c₀ ∉ J := by
        by_contra h; push Not at h; exact hIJ (Finset.Subset.antisymm h hJI)
      rw [Finset.prod_eq_zero hc₀I, mul_zero]; simp [tagJ, hc₀J, hconst c₀ (hIU hc₀I)]
  · obtain ⟨c₀, hc₀J, hc₀I⟩ := Finset.not_subset.mp hJI
    have hnot : ¬ ∀ c ∈ U \ I, tagJ c = 0 := fun h ↦ by
      have := h c₀ (Finset.mem_sdiff.mpr ⟨hJU hc₀J, hc₀I⟩)
      simp [tagJ, hc₀J, htag_ne c₀ (hJU hc₀J)] at this
    rw [ite_eq_right hnot, ite_eq_right (fun h : I = J ↦ hc₀I (h ▸ hc₀J)), mul_zero]

/-- Characteristic-independent shifted partial derivative rank lower bound `U.card.choose κ` for
selector-coupled block products `∏ c, (1 - z_c * P_c(u))` over any field `F`. -/
theorem choose_le_shiftedPartialRank_selectorProduct {F : Type u} [Field F] [Finite υ] [Fintype ι]
    (κ ℓ : ℕ) (P : ι → MvPolynomial υ F) (block : ι → Finset υ) (U : Finset ι)
    (hdisj : (U : Set ι).Pairwise fun c₁ c₂ ↦ Disjoint (block c₁) (block c₂))
    (hvars : ∀ c ∈ U, (P c).vars ⊆ block c) (hconst : ∀ c ∈ U, (P c).coeff 0 = 0)
    (tag : ι → υ →₀ ℕ) (htag_ne : ∀ c ∈ U, tag c ≠ 0)
    (htag_supp : ∀ c ∈ U, (tag c).support ⊆ block c)
    (htag_coeff : ∀ c ∈ U, (P c).coeff (tag c) ≠ 0) :
    U.card.choose κ ≤ shiftedPartialRank κ ℓ (selectorProduct P) := by
  classical
  let Idx := {I : Finset ι // I ∈ Finset.powersetCard κ U}
  have hcard : Fintype.card Idx = U.card.choose κ := by
    rw [Fintype.card_coe, Finset.card_powersetCard]
  rw [← hcard]
  refine card_le_shiftedPartialRank_of_private_monomial κ ℓ (selectorProduct P)
    (fun I : Idx ↦ selectorSet I.1) (fun _ ↦ 0)
    (fun I : Idx ↦ (∑ c ∈ I.1, tag c).mapDomain Sum.inl)
    (fun I ↦ (card_selectorSet I.1).trans (Finset.mem_powersetCard.mp I.2).2)
    (fun _ ↦ by simp) (fun I ↦ ?_) fun I J hIJ ↦ ?_
  · have hIU : I.1 ⊆ U := (Finset.mem_powersetCard.mp I.2).1
    rw [monomial_zero', C_1, one_mul,
      selectorProduct_minor_coeff hdisj hvars hconst htag_ne htag_supp hIU hIU, ite_eq_left rfl]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun c hc ↦ htag_coeff c (hIU hc))
  · have hIU : I.1 ⊆ U := (Finset.mem_powersetCard.mp I.2).1
    have hJU : J.1 ⊆ U := (Finset.mem_powersetCard.mp J.2).1
    rw [monomial_zero', C_1, one_mul,
      selectorProduct_minor_coeff hdisj hvars hconst htag_ne htag_supp hIU hJU,
      ite_eq_right fun h ↦ hIJ (Subtype.ext h)]

end SelectorProduct

end CslibFrontier.MvPolynomial
