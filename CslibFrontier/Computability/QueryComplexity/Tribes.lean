/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Computability.QueryComplexity.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import CslibFrontier.Foundations.BooleanAnalysis.Tribes

import Mathlib.Combinatorics.Nullstellensatz

/-!
# Exact Degree and Sensitivity of Tribes and Tightness of Huang's Theorem

This module establishes the exact real polynomial degree and global Boolean sensitivity of
`Cslib.BitString.tribes w s` (width `w`, `s` tribes on `s * w` bits), proving quadratic tightness
`deg(Tribes_{s,s}) = s(Tribes_{s,s})²` of Huang's Sensitivity Theorem
(`Cslib.QueryComplexity.degree_le_sensitivity_sq`), together with the
Chung–Füredi–Graham–Seymour balanced tribes construction proving exact tightness `⌈√n⌉`
of Huang's induced hypercube subgraph theorem
(`Cslib.BitString.exists_mem_sqrt_card_le_card_update_mem`).

## Main definitions

* `CslibFrontier.QueryComplexity.cfgsNumTribes`, `CslibFrontier.QueryComplexity.cfgsTribePart`,
  `CslibFrontier.QueryComplexity.cfgsTribes`: the Chung–Füredi–Graham–Seymour balanced modulo-`r_n`
  tribes partition and Boolean function on `BitString n`.

## Main results

* `CslibFrontier.QueryComplexity.eq_multilinearExtension_of_degreeOf_le_one_of_eval_eq`,
  `CslibFrontier.QueryComplexity.totalDegree_multilinearExtension_le_of_eval_eq`,
  `CslibFrontier.QueryComplexity.totalDegree_multilinearExtension_eq_degree`: uniqueness,
  total-degree minimality, and exact `QueryComplexity.degree` equality for
  `Cslib.BitString.multilinearExtension`.
* `CslibFrontier.QueryComplexity.multilinearExtension_tribes`,
  `CslibFrontier.QueryComplexity.degree_tribes`,
  `CslibFrontier.QueryComplexity.sensitivity_tribes`,
  `CslibFrontier.QueryComplexity.degree_tribes_self_eq_sensitivity_sq`: for `1 ≤ w` and `1 ≤ s`,
  `degree (tribes w s) = s * w` and `sensitivity (tribes w s) = max w s`; for `1 ≤ s`,
  `degree (tribes s s) = s ^ 2`, `sensitivity (tribes s s) = s`, and
  `degree (tribes s s) = sensitivity (tribes s s) ^ 2`.
* `CslibFrontier.QueryComplexity.degree_cfgsTribes`,
  `CslibFrontier.QueryComplexity.sensitivity_cfgsTribes_le`,
  `CslibFrontier.QueryComplexity.exists_card_eq_half_add_one_forall_card_update_mem_le`: for
  `1 ≤ n`, there exists `V : Finset (BitString n)` of size `2 ^ (n - 1) + 1` such that every vertex
  in `V` (and every vertex in `Vᶜ`) has at most `⌈√n⌉` hypercube neighbors in the same set.
-/

public section

namespace CslibFrontier.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity MvPolynomial

/-! ### 1. Multilinear Extension Uniqueness and Exact Query-Complexity Degree -/

private lemma eq_zero_of_degreeOf_lt_two_of_eval_bitVal_eq_zero {ι K : Type*} [Field K]
    [Fintype ι] {p : MvPolynomial ι K} (hdeg : ∀ i : ι, p.degreeOf i ≤ 1)
    (heval : ∀ z : ι → Bool, p.eval (fun i ↦ bitVal K (z i)) = 0) :
    p = 0 := by
  classical
  refine p.eq_zero_of_eval_zero_at_prod_finset (fun _ ↦ ({0, 1} : Finset K))
    (fun i ↦ (hdeg i).trans_lt (by rw [Finset.card_pair (zero_ne_one' K)]; exact Nat.one_lt_two))
    fun u hu ↦ ?_
  let z : ι → Bool := fun i ↦ decide (u i = 1)
  have huz : u = fun i ↦ bitVal K (z i) := funext fun i ↦ by
    rcases Finset.mem_insert.mp (hu i) with h0 | h1
    · simp [z, h0, bitVal, zero_ne_one' K]
    · simp [z, Finset.mem_singleton.mp h1, bitVal]
  exact huz ▸ heval z

private lemma degreeOf_neg_eq {ι R : Type*} [CommRing R] (i : ι) (p : MvPolynomial ι R) :
    (-p).degreeOf i = p.degreeOf i := by
  simp only [degreeOf_eq_sup, support_neg]

private lemma degreeOf_X_le_ite {ι R : Type*} [CommSemiring R] [DecidableEq ι] (j i : ι) :
    (X j : MvPolynomial ι R).degreeOf i ≤ if i = j then 1 else 0 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · rw [Subsingleton.elim (X j : MvPolynomial ι R) 0, degreeOf_zero]
    exact Nat.zero_le _
  · rw [degreeOf_X]

private lemma degreeOf_affine_X_le {ι R : Type*} [CommRing R] [DecidableEq ι]
    (a b : R) (j i : ι) :
    (C a + C b * X j).degreeOf i ≤ if i = j then 1 else 0 := by
  refine (degreeOf_add_le i _ _).trans (max_le (by simp) ?_)
  exact (degreeOf_C_mul_le (X j) i b).trans (degreeOf_X_le_ite j i)

private lemma degreeOf_prod_X_le_one {ι R : Type*} [CommRing R] (s : Finset ι) (i : ι) :
    (∏ j ∈ s, (X j : MvPolynomial ι R)).degreeOf i ≤ 1 := by
  classical
  refine (degreeOf_prod_le i s _).trans ?_
  refine (Finset.sum_le_sum fun j _ ↦ degreeOf_X_le_ite (R := R) j i).trans ?_
  by_cases hi : i ∈ s
  · rw [Finset.sum_eq_single i (fun j _ hj ↦ ite_eq_right_iff.mpr fun h ↦ absurd h.symm hj)
      (fun h ↦ absurd hi h)]
    simp
  · rw [Finset.sum_eq_zero fun j hj ↦
      ite_eq_right_iff.mpr fun (h : i = j) ↦ absurd (h.symm ▸ hj) hi]
    exact Nat.zero_le 1

/-- Every coordinate degree of `Cslib.BitString.indicatorPoly` is at most `1`. -/
theorem degreeOf_indicatorPoly_le_one {ι R : Type*} [CommRing R] [Fintype ι]
    (a : ι → Bool) (i : ι) :
    (indicatorPoly a : MvPolynomial ι R).degreeOf i ≤ 1 := by
  classical
  refine (degreeOf_prod_le i Finset.univ _).trans ?_
  refine (Finset.sum_le_sum (g := fun j : ι ↦ if i = j then 1 else 0) fun j _ ↦ ?_).trans (by simp)
  cases ha : a j
  · simpa [ha, sub_eq_add_neg] using degreeOf_affine_X_le (1 : R) (-1) j i
  · simpa [ha] using degreeOf_X_le_ite (R := R) j i

/-- Every coordinate degree of `Cslib.BitString.multilinearExtension` is at most `1`. -/
theorem degreeOf_multilinearExtension_le_one {ι R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → R) (i : ι) :
    (multilinearExtension g).degreeOf i ≤ 1 := by
  refine (degreeOf_sum_le i Finset.univ _).trans (Finset.sup_le fun a _ ↦ ?_)
  exact (degreeOf_C_mul_le _ i _).trans (degreeOf_indicatorPoly_le_one a i)

/-- **Multilinear uniqueness**: over any field `K`, any polynomial `p : MvPolynomial ι K` of
individual variable degree at most `1` agreeing with `g` on `{0, 1}^ι` equals
`multilinearExtension g`. -/
theorem eq_multilinearExtension_of_degreeOf_le_one_of_eval_eq {ι K : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {p : MvPolynomial ι K} {g : (ι → Bool) → K}
    (hp : ∀ i : ι, p.degreeOf i ≤ 1)
    (heval : ∀ z : ι → Bool, p.eval (fun i ↦ bitVal K (z i)) = g z) :
    p = multilinearExtension g := by
  refine sub_eq_zero.mp (eq_zero_of_degreeOf_lt_two_of_eval_bitVal_eq_zero (fun i ↦ ?_) fun z ↦ ?_)
  · rw [sub_eq_add_neg]
    exact (degreeOf_add_le i _ _).trans (max_le (hp i)
      ((degreeOf_neg_eq i _).trans_le (degreeOf_multilinearExtension_le_one g i)))
  · rw [eval_sub, heval z, eval_multilinearExtension, sub_self]

private lemma card_support_le_totalDegree {ι R : Type*} [CommSemiring R] {p : MvPolynomial ι R}
    {m : ι →₀ ℕ} (hm : m ∈ p.support) : m.support.card ≤ p.totalDegree := by
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun _ hi ↦ Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- **Total-degree minimality**: `multilinearExtension g` minimizes total degree among all
polynomials over a field `K` agreeing with `g` on `{0, 1}^ι`. -/
theorem totalDegree_multilinearExtension_le_of_eval_eq {ι K : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {p : MvPolynomial ι K} {g : (ι → Bool) → K}
    (heval : ∀ z : ι → Bool, p.eval (fun i ↦ bitVal K (z i)) = g z) :
    (multilinearExtension g).totalDegree ≤ p.totalDegree := by
  let q : MvPolynomial ι K := ∑ m ∈ p.support, C (p.coeff m) * ∏ i ∈ m.support, X i
  have hq_deg : ∀ i : ι, q.degreeOf i ≤ 1 := fun i ↦
    (degreeOf_sum_le i p.support _).trans (Finset.sup_le fun m _ ↦
      (degreeOf_C_mul_le _ i _).trans (degreeOf_prod_X_le_one m.support i))
  have hq_eval : ∀ z : ι → Bool, q.eval (fun i ↦ bitVal K (z i)) = g z := fun z ↦ by
    rw [← heval z]
    conv_rhs => rw [p.as_sum]
    simp only [q, map_sum, map_mul, eval_C, map_prod, eval_X, eval_monomial, Finsupp.prod]
    exact Finset.sum_congr rfl fun m _ ↦ congrArg (p.coeff m * ·)
      (Finset.prod_congr rfl fun i hi ↦ (bitVal_pow (z i) (Finsupp.mem_support_iff.mp hi)).symm)
  rw [← eq_multilinearExtension_of_degreeOf_le_one_of_eval_eq hq_deg hq_eval]
  refine totalDegree_finsetSum_le fun m hm ↦ ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd m.support _).trans ?_
  calc (∑ i ∈ m.support, (X i : MvPolynomial ι K).totalDegree)
      ≤ ∑ _i ∈ m.support, 1 := Finset.sum_le_sum fun i _ ↦ (totalDegree_X (R := K) i).le
    _ = m.support.card := by simp
    _ ≤ p.totalDegree := card_support_le_totalDegree hm

private lemma aeval_bitVal_apply {ι K : Type*} [CommRing K] (q : MvPolynomial ι K)
    (z : ι → Bool) :
    (aeval (fun i (x : ι → Bool) ↦ bitVal K (x i)) q) z =
      eval (fun i ↦ bitVal K (z i)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | mul_X p₁ i ih => simp [ih]

/-- For every `f : BooleanFunction n`, `(multilinearExtension (bitVal ℝ ∘ f)).totalDegree` equals
`Cslib.QueryComplexity.degree f`. -/
theorem totalDegree_multilinearExtension_eq_degree {n : ℕ} (f : BooleanFunction n) :
    (multilinearExtension (fun x ↦ bitVal ℝ (f x))).totalDegree = degree f := by
  change _ = Cslib.BitString.totalDegree (fun x ↦ bitVal ℝ (f x))
  apply le_antisymm
  · have hmem := mem_lowDegree_totalDegree (fun x ↦ bitVal ℝ (f x))
    rw [lowDegree_eq_map_restrictTotalDegree] at hmem
    obtain ⟨p, hp, hpeq⟩ := hmem
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hp
    refine (totalDegree_multilinearExtension_le_of_eval_eq fun z ↦ ?_).trans hp
    have hz := congrFun hpeq z
    rw [AlgHom.toLinearMap_apply] at hz
    rw [← aeval_bitVal_apply, hz]
  · refine totalDegree_le_of_mem_lowDegree ?_
    rw [lowDegree_eq_map_restrictTotalDegree]
    refine ⟨multilinearExtension (fun x ↦ bitVal ℝ (f x)),
      (mem_restrictTotalDegree _ _ _).mpr le_rfl, funext fun z ↦ ?_⟩
    rw [AlgHom.toLinearMap_apply, aeval_bitVal_apply, eval_multilinearExtension]

/-! ### 2. General Disjoint-Block Tribes -/

private lemma coeff_sum_single_prod_affine {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∏ j ∈ s, (C (a j) + C (b j) * X j)).coeff (∑ j ∈ s, Finsupp.single j 1) = ∏ j ∈ s, b j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    set P := ∏ j ∈ s, (C (a j) + C (b j) * X j)
    have hdeg_i : P.degreeOf i = 0 := by
      refine Nat.eq_zero_of_le_zero ((degreeOf_prod_le i s _).trans ?_)
      rw [Finset.sum_eq_zero fun j hj ↦ ?_]
      have hij : i ≠ j := (ne_of_mem_of_not_mem hj hi).symm
      exact Nat.eq_zero_of_le_zero ((degreeOf_affine_X_le (a j) (b j) j i).trans_eq (by simp [hij]))
    have hadd : ∀ (p q : MvPolynomial ι ℝ) (m : ι →₀ ℕ),
        (p + q).coeff m = p.coeff m + q.coeff m := fun p q m ↦ by
      simp
    rw [Finset.prod_insert hi, Finset.sum_insert hi, add_mul, hadd, coeff_C_mul]
    have hzero : P.coeff (Finsupp.single i 1 + ∑ j ∈ s, Finsupp.single j 1) = 0 := by
      refine notMem_support_iff.mp (notMem_support_of_degreeOf_lt i ?_)
      rw [hdeg_i, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    have hmulX : (C (b i) * X i * P).coeff
        (Finsupp.single i 1 + ∑ j ∈ s, Finsupp.single j 1) = b i * ∏ j ∈ s, b j := by
      rw [mul_assoc, coeff_C_mul, coeff_X_mul, ih]
    rw [hzero, mul_zero, zero_add, hmulX, Finset.prod_insert hi]

private def blockTribes {n r : ℕ} (P : Fin r → Finset (Fin n)) : BooleanFunction n :=
  fun z ↦ decide (∃ t : Fin r, ∀ j ∈ P t, z j = true)

private lemma sensitivity_blockTribes_le {n r k : ℕ} (P : Fin r → Finset (Fin n))
    (hcard : ∀ t : Fin r, (P t).card ≤ k) (hr : r ≤ k) :
    sensitivity (blockTribes P) ≤ k := by
  refine Finset.sup_le fun z _ ↦ ?_
  by_cases hz : blockTribes P z = true
  · obtain ⟨t₀, ht₀⟩ := of_decide_eq_true hz
    have hsub : sensitiveCoords (blockTribes P) z ⊆ P t₀ := fun i hi ↦ by
      have hne : blockTribes P (Function.update z i (!z i)) ≠ blockTribes P z :=
        mem_sensitiveCoords.mp hi
      by_contra hni
      refine hne ?_
      rw [hz]
      exact decide_eq_true ⟨t₀, fun j hj ↦ by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hni)]
        exact ht₀ j hj⟩
    exact (Finset.card_le_card hsub).trans (hcard t₀)
  · have hzf : blockTribes P z = false := Bool.eq_false_iff.mpr hz
    have hex_t : ∀ i ∈ sensitiveCoords (blockTribes P) z,
        ∃ t : Fin r, i ∈ P t ∧ ∀ j ∈ P t, j ≠ i → z j = true := fun i hi ↦ by
      have hne : blockTribes P (Function.update z i (!z i)) ≠ blockTribes P z :=
        mem_sensitiveCoords.mp hi
      have hft : blockTribes P (Function.update z i (!z i)) = true :=
        Bool.eq_true_of_not_eq_false (hzf ▸ hne)
      obtain ⟨t, ht⟩ := of_decide_eq_true hft
      have hother : ∀ j ∈ P t, j ≠ i → z j = true := fun j hj hji ↦ by
        simpa [Function.update_of_ne hji] using ht j hj
      have hi_in : i ∈ P t := by
        by_contra hni
        exact hz (decide_eq_true ⟨t, fun j hj ↦ hother j hj (ne_of_mem_of_not_mem hj hni)⟩)
      exact ⟨t, hi_in, hother⟩
    choose tFn htFn using hex_t
    let fMap : {i : Fin n // i ∈ sensitiveCoords (blockTribes P) z} → Fin r :=
      fun i ↦ tFn i.1 i.2
    have hfinj : Function.Injective fMap := fun i₁ i₂ hteq ↦ by
      by_contra hne
      have hne_val : i₁.1 ≠ i₂.1 := fun hv ↦ hne (Subtype.ext hv)
      obtain ⟨hi₁_in, _⟩ := htFn i₁.1 i₁.2
      obtain ⟨_, hother₂⟩ := htFn i₂.1 i₂.2
      have hteq' : tFn i₁.1 i₁.2 = tFn i₂.1 i₂.2 := hteq
      have hzi₁_true : z i₁.1 = true := hother₂ i₁.1 (hteq' ▸ hi₁_in) hne_val
      have hall : ∀ j ∈ P (tFn i₁.1 i₁.2), z j = true := fun j hj ↦
        if hji : j = i₁.1 then hji ▸ hzi₁_true else (htFn i₁.1 i₁.2).2 j hj hji
      exact hz (decide_eq_true ⟨tFn i₁.1 i₁.2, hall⟩)
    calc sensitivityAt (blockTribes P) z
        = Fintype.card {i : Fin n // i ∈ sensitiveCoords (blockTribes P) z} :=
          (Fintype.card_coe _).symm
      _ ≤ Fintype.card (Fin r) := Fintype.card_le_of_injective fMap hfinj
      _ = r := Fintype.card_fin r
      _ ≤ k := hr

private noncomputable def blockTribesPoly {n r : ℕ} (P : Fin r → Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  1 - ∏ t : Fin r, (1 - ∏ j ∈ P t, X j)

private lemma multilinearExtension_blockTribes {n r : ℕ} (P : Fin r → Finset (Fin n))
    (hdisj : ∀ t₁ t₂ : Fin r, t₁ ≠ t₂ → Disjoint (P t₁) (P t₂)) :
    multilinearExtension (fun z ↦ bitVal ℝ (blockTribes P z)) = blockTribesPoly P := by
  symm
  refine eq_multilinearExtension_of_degreeOf_le_one_of_eval_eq (fun i ↦ ?_) (fun z ↦ ?_)
  · rw [blockTribesPoly, sub_eq_add_neg]
    refine (degreeOf_add_le i _ _).trans (max_le (by simp) ?_)
    rw [degreeOf_neg_eq]
    refine (degreeOf_prod_le i Finset.univ _).trans ?_
    have hfac : ∀ t : Fin r,
        (1 - ∏ j ∈ P t, (X j : MvPolynomial (Fin n) ℝ)).degreeOf i ≤
          if i ∈ P t then 1 else 0 := fun t ↦ by
      rw [sub_eq_add_neg]
      refine (degreeOf_add_le i _ _).trans (max_le (by simp) ?_)
      rw [degreeOf_neg_eq]
      by_cases hi : i ∈ P t
      · simpa [hi] using degreeOf_prod_X_le_one (P t) i
      · simp only [hi, ↓reduceIte]
        refine (degreeOf_prod_le i (P t) _).trans ?_
        rw [Finset.sum_eq_zero fun j hj ↦ by
          rw [degreeOf_X]
          exact ite_eq_right_iff.mpr fun (h : i = j) ↦ absurd (h.symm ▸ hj) hi]
    refine (Finset.sum_le_sum fun t _ ↦ hfac t).trans ?_
    by_cases hex : ∃ t : Fin r, i ∈ P t
    · obtain ⟨t₀, ht₀⟩ := hex
      rw [Finset.sum_eq_single t₀ (fun t _ hne ↦ ite_eq_right_iff.mpr fun hit ↦
        (Finset.disjoint_left.mp (hdisj t₀ t hne.symm) ht₀ hit).elim)
        (fun h ↦ absurd (Finset.mem_univ t₀) h)]
      simp [ht₀]
    · push Not at hex
      rw [Finset.sum_eq_zero fun t _ ↦ by simp [hex t]]
      exact Nat.zero_le 1
  · simp only [blockTribesPoly, map_sub, map_one, map_prod, eval_X]
    by_cases h : blockTribes P z = true
    · obtain ⟨t₀, ht₀⟩ := of_decide_eq_true h
      have hfactor : (1 : ℝ) - (∏ j ∈ P t₀, bitVal ℝ (z j)) = 0 := by
        rw [Finset.prod_eq_one fun j hj ↦ by simp [ht₀ j hj], sub_self]
      rw [h, bitVal_true, Finset.prod_eq_zero (Finset.mem_univ t₀) hfactor, sub_zero]
    · have hf : blockTribes P z = false := Bool.eq_false_iff.mpr h
      have hnot : ∀ t : Fin r, ∃ j ∈ P t, z j = false := fun t ↦ by
        by_contra! hall
        exact h (decide_eq_true ⟨t, fun j hj ↦ Bool.eq_true_of_not_eq_false (hall j hj)⟩)
      have hprod_one : (∏ t : Fin r, ((1 : ℝ) - ∏ j ∈ P t, bitVal ℝ (z j))) = 1 :=
        Finset.prod_eq_one fun t _ ↦ by
          obtain ⟨j₀, hj₀, hzj₀⟩ := hnot t
          rw [Finset.prod_eq_zero hj₀ (by simp [hzj₀]), sub_zero]
      rw [hf, bitVal_false, hprod_one, sub_self]

private lemma support_subset_of_blockProd {n r : ℕ} (P : Fin r → Finset (Fin n)) :
    ∀ (A : Finset (Fin r)) {m : Fin n →₀ ℕ},
      m ∈ (∏ t ∈ A, (1 - ∏ j ∈ P t, (X j : MvPolynomial (Fin n) ℝ))).support →
        m.support ⊆ A.biUnion P := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra h0
      exact mem_support_iff.mp hm
        (by rw [coeff_one]; exact ite_eq_right_iff.mpr fun h ↦ absurd h.symm h0)
    simp [hm0]
  | insert t₀ A ht₀ ih =>
    intro m hm
    rw [Finset.prod_insert ht₀] at hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    refine Finsupp.support_add.trans (Finset.union_subset ?_ ?_)
    · intro i hi
      have hdeg1 : 1 ≤ (1 - ∏ j ∈ P t₀, (X j : MvPolynomial (Fin n) ℝ)).degreeOf i :=
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)).trans
          (le_degreeOf_of_mem_support i hm₁)
      have hiP : i ∈ P t₀ := by
        by_contra hni
        have h0 : (1 - ∏ j ∈ P t₀, (X j : MvPolynomial (Fin n) ℝ)).degreeOf i ≤ 0 := by
          rw [sub_eq_add_neg]
          refine (degreeOf_add_le i _ _).trans (max_le (by simp) ?_)
          rw [degreeOf_neg_eq]
          refine (degreeOf_prod_le i (P t₀) _).trans ?_
          rw [Finset.sum_eq_zero fun j hj ↦ by
            rw [degreeOf_X]
            exact ite_eq_right_iff.mpr fun h ↦ absurd (h ▸ hj) hni]
        omega
      exact Finset.mem_biUnion.mpr ⟨t₀, Finset.mem_insert_self t₀ A, hiP⟩
    · exact (ih hm₂).trans (Finset.biUnion_subset_biUnion_of_subset_left P
        (Finset.subset_insert t₀ A))

private lemma topCoeff_blockTribesPoly {n r : ℕ} (hr : 1 ≤ r) (P : Fin r → Finset (Fin n))
    (hdisj : ∀ t₁ t₂ : Fin r, t₁ ≠ t₂ → Disjoint (P t₁) (P t₂))
    (hne : ∀ t : Fin r, (P t).Nonempty) (hcov : Finset.univ.biUnion P = Finset.univ) :
    (blockTribesPoly P).coeff (∑ j : Fin n, Finsupp.single j 1) = (-1 : ℝ) ^ (r + 1) := by
  have hprod_coeff : ∀ A : Finset (Fin r),
      (∏ t ∈ A, (1 - ∏ j ∈ P t, (X j : MvPolynomial (Fin n) ℝ))).coeff
        (∑ t ∈ A, ∑ j ∈ P t, Finsupp.single j 1) = (-1 : ℝ) ^ A.card := fun A ↦ by
    induction A using Finset.induction_on with
    | empty => simp
    | insert t₀ A ht₀ ih =>
      set Q : MvPolynomial (Fin n) ℝ := ∏ j ∈ P t₀, X j
      set R : MvPolynomial (Fin n) ℝ := ∏ t ∈ A, (1 - ∏ j ∈ P t, X j)
      set m₀ : Fin n →₀ ℕ := ∑ j ∈ P t₀, Finsupp.single j 1
      set mA : Fin n →₀ ℕ := ∑ t ∈ A, ∑ j ∈ P t, Finsupp.single j 1
      have hR_supp : ∀ m ∈ R.support, Disjoint m.support (P t₀) := fun m hm ↦
        Finset.disjoint_left.mpr fun i him hiP ↦ by
          obtain ⟨t, htA, hit⟩ := Finset.mem_biUnion.mp (support_subset_of_blockProd P A hm him)
          exact Finset.disjoint_left.mp (hdisj t₀ t (ne_of_mem_of_not_mem htA ht₀).symm) hiP hit
      have hQ_supp : ∀ m ∈ Q.support, m.support ⊆ P t₀ := fun m hm i him ↦ by
        by_contra hni
        have h1 : 1 ≤ Q.degreeOf i :=
          (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp him)).trans
            (le_degreeOf_of_mem_support i hm)
        have h0 : Q.degreeOf i ≤ 0 := (degreeOf_prod_le i (P t₀) _).trans
          (by rw [Finset.sum_eq_zero fun j hj ↦ by
            rw [degreeOf_X]; exact ite_eq_right_iff.mpr fun h ↦ absurd (h ▸ hj) hni])
        omega
      rw [Finset.prod_insert ht₀, Finset.sum_insert ht₀]
      change ((1 - Q) * R).coeff (m₀ + mA) = (-1 : ℝ) ^ (insert t₀ A).card
      rw [sub_mul, one_mul, coeff_sub]
      have hR0 : R.coeff (m₀ + mA) = 0 := by
        obtain ⟨j₀, hj₀⟩ := hne t₀
        have hj₀_pos : (m₀ + mA) j₀ ≠ 0 := by
          have hm₀_j₀ : m₀ j₀ = 1 := by
            simp only [m₀, Finset.sum_apply']
            rw [Finset.sum_eq_single j₀ (fun j _ hj ↦ Finsupp.single_eq_of_ne hj.symm)
              (fun h ↦ absurd hj₀ h), Finsupp.single_eq_same]
          rw [Finsupp.add_apply, hm₀_j₀]
          omega
        by_contra hne0
        exact Finset.disjoint_left.mp (hR_supp _ (mem_support_iff.mpr hne0))
          (Finsupp.mem_support_iff.mpr hj₀_pos) hj₀
      have hmul_coeff : (Q * R).coeff (m₀ + mA) = Q.coeff m₀ * R.coeff mA := by
        rw [coeff_mul]
        have hmem_anti : (m₀, mA) ∈ Finset.antidiagonal (m₀ + mA) :=
          Finset.mem_antidiagonal.mpr rfl
        rw [Finset.sum_eq_single (m₀, mA) (fun pq hpq hne_pq ↦ ?_) (fun h ↦ absurd hmem_anti h)]
        have hpq_eq : pq.1 + pq.2 = m₀ + mA := Finset.mem_antidiagonal.mp hpq
        by_contra hprod_ne
        have hp_mem := mem_support_iff.mpr (left_ne_zero_of_mul hprod_ne)
        have hq_mem := mem_support_iff.mpr (right_ne_zero_of_mul hprod_ne)
        have hp_eq : pq.1 = m₀ := by
          ext i
          have hsum_i := congrFun (congrArg DFunLike.coe hpq_eq) i
          simp only [Finsupp.coe_add, Pi.add_apply] at hsum_i
          by_cases hi : i ∈ P t₀
          · have hq_i : pq.2 i = 0 := Finsupp.notMem_support_iff.mp
              (Finset.disjoint_right.mp (hR_supp pq.2 hq_mem) hi)
            have hmA_i : mA i = 0 := by
              simp only [mA, Finset.sum_apply']
              exact Finset.sum_eq_zero fun t ht ↦ Finset.sum_eq_zero fun j hj ↦
                Finsupp.single_eq_of_ne fun hij ↦ Finset.disjoint_left.mp
                  (hdisj t₀ t (ne_of_mem_of_not_mem ht ht₀).symm) hi (hij ▸ hj)
            omega
          · have hp_i : pq.1 i = 0 :=
              Finsupp.notMem_support_iff.mp fun h ↦ hi (hQ_supp pq.1 hp_mem h)
            have hm₀_i : m₀ i = 0 := by
              simp only [m₀, Finset.sum_apply']
              exact Finset.sum_eq_zero fun j hj ↦
                Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hj hi).symm
            omega
        exact hne_pq (Prod.ext hp_eq (add_left_cancel (hp_eq ▸ hpq_eq)))
      have hQ_coeff : Q.coeff m₀ = 1 := by
        simpa [Q, m₀] using coeff_sum_single_prod_affine (P t₀) (fun _ ↦ 0) (fun _ ↦ 1)
      rw [hR0, zero_sub, hmul_coeff, hQ_coeff, one_mul, ih,
        Finset.card_insert_of_notMem ht₀, pow_succ]
      ring
  have hsum_univ : (∑ t : Fin r, ∑ j ∈ P t, Finsupp.single j (1 : ℕ)) =
      ∑ j : Fin n, Finsupp.single j 1 := by
    rw [← Finset.sum_biUnion (fun t₁ _ t₂ _ h ↦ hdisj t₁ t₂ h), hcov]
  obtain ⟨j₁, -⟩ := hne ⟨0, hr⟩
  have hm_ne : (∑ j : Fin n, Finsupp.single j (1 : ℕ)) ≠ 0 := fun h0 ↦ by
    have := congrFun (congrArg DFunLike.coe h0) j₁; simp at this
  have hone0 : (1 : MvPolynomial (Fin n) ℝ).coeff (∑ j : Fin n, Finsupp.single j 1) = 0 := by
    rw [coeff_one]; exact ite_eq_right_iff.mpr fun h ↦ absurd h.symm hm_ne
  rw [blockTribesPoly, coeff_sub, hone0, zero_sub, ← hsum_univ, hprod_coeff Finset.univ,
    Finset.card_univ, Fintype.card_fin, pow_add, pow_one]
  ring

/-! ### 3. Exact Polynomial Degree and Sensitivity of `Cslib.BitString.tribes` -/

private def stdTribeBlock (w s : ℕ) (j : Fin s) : Finset (Fin (s * w)) :=
  Finset.univ.map ⟨fun i : Fin w ↦ finProdFinEquiv (j, i), fun _ _ h ↦ by simpa using h⟩

private lemma mem_stdTribeBlock {w s : ℕ} {j : Fin s} {k : Fin (s * w)} :
    k ∈ stdTribeBlock w s j ↔ (finProdFinEquiv.symm k).1 = j := by
  simp only [stdTribeBlock, Finset.mem_map, Finset.mem_univ, true_and]
  refine ⟨?_, fun h ↦ ⟨(finProdFinEquiv.symm k).2, h ▸ finProdFinEquiv.apply_symm_apply k⟩⟩
  rintro ⟨i, rfl⟩
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)

private lemma card_stdTribeBlock (w s : ℕ) (j : Fin s) : (stdTribeBlock w s j).card = w := by
  simp [stdTribeBlock]

private lemma disjoint_stdTribeBlock {w s : ℕ} {j₁ j₂ : Fin s} (h : j₁ ≠ j₂) :
    Disjoint (stdTribeBlock w s j₁) (stdTribeBlock w s j₂) :=
  Finset.disjoint_left.mpr fun _ h₁ h₂ ↦ h ((mem_stdTribeBlock.mp h₁).symm.trans
    (mem_stdTribeBlock.mp h₂))

private lemma biUnion_stdTribeBlock (w s : ℕ) :
    Finset.univ.biUnion (stdTribeBlock w s) = Finset.univ :=
  Finset.eq_univ_iff_forall.mpr fun k ↦
    Finset.mem_biUnion.mpr ⟨(finProdFinEquiv.symm k).1, Finset.mem_univ _,
      mem_stdTribeBlock.mpr rfl⟩

private lemma tribes_eq_blockTribes (w s : ℕ) :
    tribes w s = blockTribes (stdTribeBlock w s) := by
  ext z
  rw [Bool.eq_iff_iff, tribes_eq_true_iff]
  change (∃ j : Fin s, ∀ i : Fin w, z (finProdFinEquiv (j, i)) = true) ↔
    decide (∃ j : Fin s, ∀ k ∈ stdTribeBlock w s j, z k = true) = true
  rw [decide_eq_true_iff]
  refine exists_congr fun j ↦ ⟨fun h k hk ↦ ?_, fun h i ↦ h _ ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hk; exact h i
  · exact Finset.mem_map_of_mem _ (Finset.mem_univ i)

/-- Explicit real multilinear extension of `Cslib.BitString.tribes w s`. -/
theorem multilinearExtension_tribes (w s : ℕ) :
    multilinearExtension (fun z ↦ bitVal ℝ (tribes w s z)) =
      1 - ∏ j : Fin s, (1 - ∏ i : Fin w, X (finProdFinEquiv (j, i))) := by
  rw [tribes_eq_blockTribes,
    multilinearExtension_blockTribes (stdTribeBlock w s) fun _ _ h ↦ disjoint_stdTribeBlock h]
  simp only [blockTribesPoly, stdTribeBlock, Finset.prod_map]
  rfl

/-- For `1 ≤ w` and `1 ≤ s`, the top multilinear coefficient of `tribes w s` is `(-1) ^ (s + 1)`. -/
theorem topCoeff_multilinearExtension_tribes {w s : ℕ} (hw : 1 ≤ w) (hs : 1 ≤ s) :
    (multilinearExtension (fun z ↦ bitVal ℝ (tribes w s z))).coeff
        (∑ k : Fin (s * w), Finsupp.single k 1) = (-1 : ℝ) ^ (s + 1) := by
  rw [tribes_eq_blockTribes,
    multilinearExtension_blockTribes (stdTribeBlock w s) fun _ _ h ↦ disjoint_stdTribeBlock h]
  exact topCoeff_blockTribesPoly hs (stdTribeBlock w s) (fun _ _ h ↦ disjoint_stdTribeBlock h)
    (fun j ↦ Finset.card_pos.mp (by rw [card_stdTribeBlock]; exact hw))
    (biUnion_stdTribeBlock w s)

/-- For `1 ≤ w` and `1 ≤ s`, `tribes w s` has full polynomial degree `s * w`. -/
theorem degree_tribes {w s : ℕ} (hw : 1 ≤ w) (hs : 1 ≤ s) :
    degree (tribes w s) = s * w := by
  rw [← totalDegree_multilinearExtension_eq_degree]
  refine le_antisymm ((totalDegree_multilinearExtension_le _).trans_eq (Fintype.card_fin _)) ?_
  have hmem : (∑ k : Fin (s * w), Finsupp.single k (1 : ℕ)) ∈
      (multilinearExtension (fun z ↦ bitVal ℝ (tribes w s z))).support :=
    mem_support_iff.mpr (by rw [topCoeff_multilinearExtension_tribes hw hs]; positivity)
  have hsupp : (∑ k : Fin (s * w), Finsupp.single k (1 : ℕ)).support = Finset.univ := by
    ext k; simp
  calc s * w = (∑ k : Fin (s * w), Finsupp.single k (1 : ℕ)).support.card := by simp [hsupp]
    _ ≤ _ := card_support_le_totalDegree hmem

/-- Pointwise sensitivity of `tribes w s` (`1 ≤ w`, `1 ≤ s`) at the indicator of tribe `0` is
`w`. -/
theorem sensitivityAt_tribes_firstTribe {w s : ℕ} (hw : 1 ≤ w) (hs : 1 ≤ s) :
    sensitivityAt (tribes w s) (fun k ↦ decide ((finProdFinEquiv.symm k).1.1 = 0)) = w := by
  set x₀ : BitString (s * w) := fun k ↦ decide ((finProdFinEquiv.symm k).1.1 = 0)
  let j₀ : Fin s := ⟨0, hs⟩
  let i₀ : Fin w := ⟨0, hw⟩
  have hx₀_true : tribes w s x₀ = true :=
    tribes_eq_true_iff.mpr ⟨j₀, fun i ↦ by simp [x₀, j₀]⟩
  have hsens_eq : sensitiveCoords (tribes w s) x₀ = stdTribeBlock w s j₀ := by
    ext k
    rw [mem_sensitiveCoords, mem_stdTribeBlock]
    change tribes w s (Function.update x₀ k (!x₀ k)) ≠ tribes w s x₀ ↔ _
    rw [hx₀_true]
    refine ⟨fun hflip ↦ ?_, fun hkj hflip ↦ ?_⟩
    · by_contra hne
      refine hflip (tribes_eq_true_iff.mpr ⟨j₀, fun i ↦ ?_⟩)
      have hki : finProdFinEquiv (j₀, i) ≠ k := fun h ↦
        hne (by rw [← h, finProdFinEquiv.symm_apply_apply])
      rw [Function.update_of_ne hki]
      simp [x₀, j₀]
    · obtain ⟨j, hj⟩ := tribes_eq_true_iff.mp hflip
      by_cases hjj : j = j₀
      · subst hjj
        have hk_eq : finProdFinEquiv (j₀, (finProdFinEquiv.symm k).2) = k := by
          rw [← hkj]; exact finProdFinEquiv.apply_symm_apply k
        have hv := hj (finProdFinEquiv.symm k).2
        have hx₀k : x₀ k = true := decide_eq_true (by rw [hkj])
        rw [hk_eq, Function.update_self, hx₀k] at hv
        exact absurd hv (by decide)
      · have hki : finProdFinEquiv (j, i₀) ≠ k := fun h ↦
          hjj (by rw [← hkj, ← h, finProdFinEquiv.symm_apply_apply])
        have hv := hj i₀
        rw [Function.update_of_ne hki] at hv
        have hj0 : j.1 ≠ 0 := fun h ↦ hjj (Fin.ext h)
        simp only [x₀, finProdFinEquiv.symm_apply_apply, decide_eq_true_eq] at hv
        exact hj0 hv
  exact (congrArg Finset.card hsens_eq).trans (card_stdTribeBlock w s j₀)

private lemma sensitivityAt_tribes_almostAll {w s : ℕ} (hw : 1 ≤ w) :
    sensitivityAt (tribes w s) (fun k ↦ decide ((finProdFinEquiv.symm k).2.1 ≠ 0)) = s := by
  set x₁ : BitString (s * w) := fun k ↦ decide ((finProdFinEquiv.symm k).2.1 ≠ 0)
  let i₀ : Fin w := ⟨0, hw⟩
  have hx₁_false : tribes w s x₁ = false :=
    Bool.eq_false_iff.mpr fun h ↦ by
      obtain ⟨j, hj⟩ := tribes_eq_true_iff.mp h
      have hv := hj i₀
      simp [x₁, i₀] at hv
  let S : Finset (Fin (s * w)) :=
    Finset.univ.map ⟨fun j : Fin s ↦ finProdFinEquiv (j, i₀), fun _ _ h ↦ by simpa using h⟩
  have hsens_eq : sensitiveCoords (tribes w s) x₁ = S := by
    ext k
    rw [mem_sensitiveCoords]
    change tribes w s (Function.update x₁ k (!x₁ k)) ≠ tribes w s x₁ ↔ k ∈ S
    rw [hx₁_false]
    refine ⟨fun hflip ↦ ?_, fun hkS ↦ ?_⟩
    · have ht : tribes w s (Function.update x₁ k (!x₁ k)) = true :=
        Bool.eq_true_of_not_eq_false hflip
      obtain ⟨j, hj⟩ := tribes_eq_true_iff.mp ht
      have hjk : finProdFinEquiv (j, i₀) = k := by
        by_contra hne
        have hv := hj i₀
        rw [Function.update_of_ne hne] at hv
        simp [x₁, i₀] at hv
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hjk⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hkS
      have ht : tribes w s
          (Function.update x₁ (finProdFinEquiv (j, i₀)) (!x₁ (finProdFinEquiv (j, i₀)))) = true :=
        tribes_eq_true_iff.mpr ⟨j, fun i ↦ by
          by_cases hii : i = i₀
          · subst hii; simp [x₁, i₀]
          · have hne : finProdFinEquiv (j, i) ≠ finProdFinEquiv (j, i₀) :=
              finProdFinEquiv.injective.ne fun h ↦ hii (Prod.mk.inj h).2
            rw [Function.update_of_ne hne]
            have hi0 : i.1 ≠ 0 := fun h ↦ hii (Fin.ext h)
            simp only [x₁, finProdFinEquiv.symm_apply_apply, ne_eq, decide_eq_true_eq]
            exact hi0⟩
      change tribes w s
        (Function.update x₁ (finProdFinEquiv (j, i₀)) (!x₁ (finProdFinEquiv (j, i₀)))) ≠ false
      rw [ht]
      decide
  exact (congrArg Finset.card hsens_eq).trans (by simp [S])

/-- For `1 ≤ w` and `1 ≤ s`, `tribes w s` has exact global sensitivity `max w s`. -/
theorem sensitivity_tribes {w s : ℕ} (hw : 1 ≤ w) (hs : 1 ≤ s) :
    sensitivity (tribes w s) = max w s := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · rw [tribes_eq_blockTribes]
    exact sensitivity_blockTribes_le (stdTribeBlock w s)
      (fun j ↦ (card_stdTribeBlock w s j).trans_le (le_max_left w s)) (le_max_right w s)
  · exact (sensitivityAt_tribes_firstTribe hw hs).symm.le.trans (sensitivityAt_le_sensitivity _ _)
  · exact (sensitivityAt_tribes_almostAll hw).symm.le.trans (sensitivityAt_le_sensitivity _ _)

/-- **Quadratic tightness of Huang's sensitivity theorem**: for every `1 ≤ s`, the balanced square
tribes function `tribes s s` satisfies `degree (tribes s s) = s ^ 2`,
`sensitivity (tribes s s) = s`, and hence `degree (tribes s s) = sensitivity (tribes s s) ^ 2`. -/
theorem degree_tribes_self_eq_sensitivity_sq {s : ℕ} (hs : 1 ≤ s) :
    degree (tribes s s) = s ^ 2 ∧
    sensitivity (tribes s s) = s ∧
    degree (tribes s s) = sensitivity (tribes s s) ^ 2 := by
  have hd : degree (tribes s s) = s ^ 2 := (degree_tribes hs hs).trans (sq s).symm
  have hsens : sensitivity (tribes s s) = s := (sensitivity_tribes hs hs).trans (max_self s)
  exact ⟨hd, hsens, by rw [hd, hsens]⟩

/-! ### 4. Chung–Füredi–Graham–Seymour Balanced Tribes and Optimal Hypercube Subgraphs -/

/-- Number of tribes `r_n := ⌈n / ⌈√n⌉⌉` in the Chung–Füredi–Graham–Seymour partition of `Fin n`. -/
noncomputable def cfgsNumTribes (n : ℕ) : ℕ :=
  (n + Nat.ceil (Real.sqrt (n : ℝ)) - 1) / Nat.ceil (Real.sqrt (n : ℝ))

/-- The `t`-th residue-class tribe `{j : Fin n | j.1 % cfgsNumTribes n = t.1}`. -/
noncomputable def cfgsTribePart (n : ℕ) (t : Fin (cfgsNumTribes n)) : Finset (Fin n) :=
  Finset.univ.filter fun j : Fin n ↦ j.1 % cfgsNumTribes n = t.1

/-- The Chung–Füredi–Graham–Seymour balanced tribes function on `BitString n`. -/
noncomputable def cfgsTribes (n : ℕ) : BooleanFunction n :=
  fun z ↦ decide (∃ t : Fin (cfgsNumTribes n), ∀ j ∈ cfgsTribePart n t, z j = true)

private lemma cfgs_props {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ cfgsNumTribes n ∧
    cfgsNumTribes n ≤ Nat.ceil (Real.sqrt (n : ℝ)) ∧
    (∀ t₁ t₂ : Fin (cfgsNumTribes n), t₁ ≠ t₂ →
      Disjoint (cfgsTribePart n t₁) (cfgsTribePart n t₂)) ∧
    (∀ t : Fin (cfgsNumTribes n), (cfgsTribePart n t).Nonempty) ∧
    (∀ t : Fin (cfgsNumTribes n), (cfgsTribePart n t).card ≤ Nat.ceil (Real.sqrt (n : ℝ))) ∧
    Finset.univ.biUnion (cfgsTribePart n) = Finset.univ := by
  set k := Nat.ceil (Real.sqrt (n : ℝ))
  set r := cfgsNumTribes n
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr <| by
    rw [ne_eq, Nat.ceil_eq_zero]
    exact not_le.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hn_le_kk : n ≤ k * k := by
    have hsq : Real.sqrt (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (Nat.le_ceil _) 2
    rw [Real.sq_sqrt (Nat.cast_nonneg n), sq] at hsq
    exact_mod_cast hsq
  have hr_pos : 1 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hr_le_k : r ≤ k := Nat.le_of_lt_succ <| (Nat.div_lt_iff_lt_mul (by omega)).mpr <| by
    calc n + k - 1 < n + k := by omega
      _ ≤ k * k + k := Nat.add_le_add_right hn_le_kk k
      _ = (k + 1) * k := by ring
  have hr_le_n : r ≤ n := Nat.le_of_lt_succ <| (Nat.div_lt_iff_lt_mul (by omega)).mpr <| by
    have hnk : n ≤ n * k := by simpa using Nat.mul_le_mul_left n hk_pos
    calc n + k - 1 < n + k := by omega
      _ ≤ n * k + k := Nat.add_le_add_right hnk k
      _ = (n + 1) * k := by ring
  have hn_le_rk : n ≤ r * k := by
    have hdiv : k * r + (n + k - 1) % k = n + k - 1 := Nat.div_add_mod (n + k - 1) k
    have hmod : (n + k - 1) % k < k := Nat.mod_lt (n + k - 1) (by omega)
    rw [mul_comm]
    omega
  refine ⟨hr_pos, hr_le_k,
    fun t₁ t₂ hne ↦ Finset.disjoint_filter.mpr fun _ _ h₁ h₂ ↦ hne (Fin.ext (h₁.symm.trans h₂)),
    fun t ↦ ⟨⟨t.1, lt_of_lt_of_le t.2 hr_le_n⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.mod_eq_of_lt t.2⟩⟩,
    fun t ↦ ?_,
    Finset.eq_univ_iff_forall.mpr fun j ↦ Finset.mem_biUnion.mpr
      ⟨⟨j.1 % r, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩⟩
  let qMap : {j : Fin n // j ∈ cfgsTribePart n t} → Fin k := fun j ↦
    ⟨j.1.1 / r, (Nat.div_lt_iff_lt_mul (by omega)).mpr
      (by rw [mul_comm]; exact lt_of_lt_of_le j.1.2 hn_le_rk)⟩
  have hq_inj : Function.Injective qMap := fun j₁ j₂ hq ↦ Subtype.ext <| Fin.ext <| by
    rw [← Nat.div_add_mod j₁.1.1 r, ← Nat.div_add_mod j₂.1.1 r,
      show j₁.1.1 / r = j₂.1.1 / r from congrArg Fin.val hq,
      (Finset.mem_filter.mp j₁.2).2, (Finset.mem_filter.mp j₂.2).2]
  rw [← Fintype.card_coe]
  exact (Fintype.card_le_of_injective qMap hq_inj).trans_eq (Fintype.card_fin k)

/-- For `1 ≤ n`, `cfgsTribes n` has sensitivity at most `⌈√n⌉`. -/
theorem sensitivity_cfgsTribes_le {n : ℕ} (hn : 1 ≤ n) :
    sensitivity (cfgsTribes n) ≤ Nat.ceil (Real.sqrt (n : ℝ)) := by
  obtain ⟨-, hr_le_k, -, -, hcard, -⟩ := cfgs_props hn
  exact sensitivity_blockTribes_le (cfgsTribePart n) hcard hr_le_k

private lemma topCoeff_multilinearExtension_cfgsTribes {n : ℕ} (hn : 1 ≤ n) :
    (multilinearExtension (fun z ↦ bitVal ℝ (cfgsTribes n z))).coeff
        (∑ j : Fin n, Finsupp.single j 1) = (-1 : ℝ) ^ (cfgsNumTribes n + 1) := by
  obtain ⟨hr_pos, -, hdisj, hne, -, hcov⟩ := cfgs_props hn
  change (multilinearExtension (fun z ↦ bitVal ℝ (blockTribes (cfgsTribePart n) z))).coeff _ = _
  rw [multilinearExtension_blockTribes (cfgsTribePart n) hdisj]
  exact topCoeff_blockTribesPoly hr_pos (cfgsTribePart n) hdisj hne hcov

/-- For `1 ≤ n`, `cfgsTribes n` has full polynomial degree `n`. -/
theorem degree_cfgsTribes {n : ℕ} (hn : 1 ≤ n) : degree (cfgsTribes n) = n := by
  rw [← totalDegree_multilinearExtension_eq_degree]
  refine le_antisymm ((totalDegree_multilinearExtension_le _).trans_eq (Fintype.card_fin _)) ?_
  have hmem : (∑ j : Fin n, Finsupp.single j (1 : ℕ)) ∈
      (multilinearExtension (fun z ↦ bitVal ℝ (cfgsTribes n z))).support :=
    mem_support_iff.mpr (by rw [topCoeff_multilinearExtension_cfgsTribes hn]; positivity)
  have hsupp : (∑ j : Fin n, Finsupp.single j (1 : ℕ)).support = Finset.univ := by ext j; simp
  calc n = (∑ j : Fin n, Finsupp.single j (1 : ℕ)).support.card := by simp [hsupp]
    _ ≤ _ := card_support_le_totalDegree hmem

private lemma topCoeff_indicatorPoly {n : ℕ} (a : BitString n) :
    (indicatorPoly a : MvPolynomial (Fin n) ℝ).coeff (∑ i : Fin n, Finsupp.single i 1) =
      (-1 : ℝ) ^ n * signVal (parity n a) := by
  have hrew : (indicatorPoly a : MvPolynomial (Fin n) ℝ) =
      ∏ j : Fin n, (C (if a j then (0 : ℝ) else 1) + C (if a j then (1 : ℝ) else -1) * X j) :=
    Finset.prod_congr rfl fun j _ ↦ by cases a j <;> simp [sub_eq_add_neg]
  rw [hrew, coeff_sum_single_prod_affine]
  have hfac : ∀ j : Fin n, (if a j then (1 : ℝ) else -1) = (-1 : ℝ) * signVal (a j) :=
    fun j ↦ by cases a j <;> norm_num
  simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [parity, ← chi_eq_signVal_parityOn, chi_eq_prod_signVal]

private lemma sum_signVal_parity {n : ℕ} (hn : 1 ≤ n) :
    (∑ a : BitString n, signVal (parity n a)) = 0 := by
  let i₀ : Fin n := ⟨0, hn⟩
  let e : BitString n ≃ BitString n :=
    Function.Involutive.toPerm (fun a ↦ Function.update a i₀ (!a i₀)) fun a ↦ by
      ext j; by_cases hj : j = i₀ <;> simp [hj]
  have hflip : (∑ a : BitString n, signVal (parity n a)) =
      -(∑ a : BitString n, signVal (parity n a)) := by
    conv_lhs => rw [← Equiv.sum_comp e]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    change signVal (parityOn Finset.univ (Function.update a i₀ (!a i₀))) =
      -signVal (parityOn Finset.univ a)
    rw [parityOn_update_not (Finset.mem_univ i₀), signVal_not]
  linarith

private lemma two_mul_sign_mul_topCoeff_multilinearExtension {n : ℕ} (hn : 1 ≤ n)
    (f : BooleanFunction n) :
    2 * (-1 : ℝ) ^ n *
        (multilinearExtension (fun z ↦ bitVal ℝ (f z))).coeff (∑ i : Fin n, Finsupp.single i 1) =
      2 * ((Finset.univ.filter fun z : BitString n ↦ (f z ^^ parity n z) = true).card : ℝ) -
        (2 ^ n : ℝ) := by
  rw [multilinearExtension, coeff_sum]
  simp_rw [coeff_C_mul, topCoeff_indicatorPoly]
  rw [Finset.mul_sum]
  have hterm : ∀ a : BitString n,
      2 * (-1 : ℝ) ^ n * (bitVal ℝ (f a) * ((-1 : ℝ) ^ n * signVal (parity n a))) =
        signVal (parity n a) + (2 * bitVal ℝ (f a ^^ parity n a) - 1) := fun a ↦ by
    have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    have hprod : 2 * (-1 : ℝ) ^ n * (bitVal ℝ (f a) * ((-1 : ℝ) ^ n * signVal (parity n a))) =
        2 * bitVal ℝ (f a) * signVal (parity n a) := by
      calc 2 * (-1 : ℝ) ^ n * (bitVal ℝ (f a) * ((-1 : ℝ) ^ n * signVal (parity n a)))
          = 2 * bitVal ℝ (f a) * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * signVal (parity n a) := by ring
        _ = 2 * bitVal ℝ (f a) * signVal (parity n a) := by rw [hsq, mul_one]
    rw [hprod]
    cases f a <;> cases parity n a <;> norm_num
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, sum_signVal_parity hn, zero_add, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have hsum_card : (∑ a : BitString n, bitVal ℝ (f a ^^ parity n a)) =
      ((Finset.univ.filter fun z : BitString n ↦ (f z ^^ parity n z) = true).card : ℝ) := by
    have hbv : ∀ a : BitString n, bitVal ℝ (f a ^^ parity n a) =
        if (f a ^^ parity n a) = true then (1 : ℝ) else 0 :=
      fun a ↦ by cases (f a ^^ parity n a) <;> simp
    simp_rw [hbv]
    rw [Finset.sum_boole]
  rw [hsum_card, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  simp

/-- **Chung–Füredi–Graham–Seymour tightness of Huang's induced hypercube bound**: for every
`1 ≤ n`, there exists `V : Finset (BitString n)` of exact size `2 ^ (n - 1) + 1` such that every
`x ∈ V` has at most `⌈√n⌉` hypercube neighbors in `V`, and every `x ∈ Vᶜ` has at most `⌈√n⌉`
hypercube neighbors in `Vᶜ` (matching `Cslib.BitString.exists_mem_sqrt_card_le_card_update_mem`).
-/
theorem exists_card_eq_half_add_one_forall_card_update_mem_le {n : ℕ} (hn : 1 ≤ n) :
    ∃ V : Finset (BitString n),
      V.card = 2 ^ (n - 1) + 1 ∧
      (∀ x ∈ V,
        (Finset.univ.filter fun i : Fin n ↦ Function.update x i (!x i) ∈ V).card ≤
          Nat.ceil (Real.sqrt (n : ℝ))) ∧
      (∀ x ∈ Vᶜ,
        (Finset.univ.filter fun i : Fin n ↦ Function.update x i (!x i) ∈ Vᶜ).card ≤
          Nat.ceil (Real.sqrt (n : ℝ))) := by
  set f := cfgsTribes n
  set k := Nat.ceil (Real.sqrt (n : ℝ))
  let fiber (b : Bool) : Finset (BitString n) :=
    Finset.univ.filter fun z ↦ (f z ^^ parity n z) = b
  have hfiber_deg : ∀ (b : Bool), ∀ x ∈ fiber b,
      (Finset.univ.filter fun i : Fin n ↦ Function.update x i (!x i) ∈ fiber b).card ≤ k := by
    intro b x hx
    have hxb : (f x ^^ parity n x) = b := (Finset.mem_filter.mp hx).2
    have heq : (Finset.univ.filter fun i : Fin n ↦ Function.update x i (!x i) ∈ fiber b) =
        sensitiveCoords f x := by
      ext i
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, mem_sensitiveCoords]
      change (f (Function.update x i (!x i)) ^^ parity n (Function.update x i (!x i))) = b ↔
        f (Function.update x i (!x i)) ≠ f x
      have hp : parity n (Function.update x i (!x i)) = !parity n x := by
        simpa only [parity] using parityOn_update_not (Finset.mem_univ i) x
      rw [hp, ← hxb]
      cases f (Function.update x i (!x i)) <;> cases f x <;> cases parity n x <;> decide
    rw [heq]
    exact (sensitivityAt_le_sensitivity f x).trans (sensitivity_cfgsTribes_le hn)
  have hcompl : (fiber true)ᶜ = fiber false := by ext z; simp [fiber]
  have hid := two_mul_sign_mul_topCoeff_multilinearExtension hn f
  rw [topCoeff_multilinearExtension_cfgsTribes hn] at hid
  have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rcases n with _ | m
    · omega
    · simp [Nat.pow_succ']
  rcases (by rw [← pow_add]; exact neg_one_pow_eq_or ℝ (n + (cfgsNumTribes n + 1)) :
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ (cfgsNumTribes n + 1) = 1 ∨
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ (cfgsNumTribes n + 1) = -1) with hpos | hneg
  · have hcard : (fiber true).card = 2 ^ (n - 1) + 1 := by
      have hR : (2 * (fiber true).card : ℝ) = ((2 ^ n + 2 : ℕ) : ℝ) := by
        dsimp [fiber]; push_cast; linarith
      have hN : 2 * (fiber true).card = 2 ^ n + 2 := by exact_mod_cast hR
      omega
    exact ⟨fiber true, hcard, hfiber_deg true, hcompl ▸ hfiber_deg false⟩
  · have hsum : (fiber true).card + (fiber false).card = 2 ^ n := by
      rw [← hcompl, Finset.card_add_card_compl, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
    have hcard : (fiber false).card = 2 ^ (n - 1) + 1 := by
      have hR : (2 * (fiber true).card + 2 : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
        dsimp [fiber]; push_cast; linarith
      have hN : 2 * (fiber true).card + 2 = 2 ^ n := by exact_mod_cast hR
      omega
    have hcompl_f : (fiber false)ᶜ = fiber true := by rw [← hcompl, compl_compl]
    exact ⟨fiber false, hcard, hfiber_deg false, hcompl_f ▸ hfiber_deg true⟩

end CslibFrontier.QueryComplexity
