module

public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real-Root Bounds for Sparse Polynomials and Sums of Products

This module derives quantitative upper bounds on the number of real roots of univariate real
polynomials from Descartes' rule of signs (`Polynomial.roots_countP_pos_le_signVariations`):

## Main definitions

* `CslibFrontier.Polynomial.InRealSPS`: representation of a univariate real polynomial as a sum of
  `k` products of `m` real polynomials, each with support cardinality at most `t`.

## Main results

* `CslibFrontier.Polynomial.signVariations_le_card_support_sub_one`: the number of sign variations
  of a real polynomial is at most `P.support.card - 1`.
* `CslibFrontier.Polynomial.roots_countP_ne_zero_le`: every real polynomial `P` has at most
  `2 * (P.support.card - 1)` nonzero real roots counted with multiplicity.
* `CslibFrontier.Polynomial.card_roots_toFinset_le_of_support_card`: every nonzero real polynomial
  `P` has at most `2 * P.support.card - 1` distinct real roots.
* `CslibFrontier.Polynomial.real_roots_bound_k_eq_one`: a nonzero product of `m` real polynomials
  each with at most `t` monomials has at most `2 * m * (t - 1) + 1` distinct real roots.
* `CslibFrontier.Polynomial.real_roots_bound_general`: a nonzero sum of `k` products of `m` real
  polynomials each with at most `t` monomials (`k, t ≥ 1`) has at most `2 * k * t ^ m - 1`
  distinct real roots.
-/

public section

namespace CslibFrontier.Polynomial

open Finset

/-- A univariate real polynomial admits a `(k, m, t)` sum-of-products-of-sparse representation
when it equals `∑ i : Fin k, ∏ j : Fin m, g i j` with each factor `g i j` having at most `t`
nonzero monomials. -/
def InRealSPS (k m t : ℕ) (f : Polynomial ℝ) : Prop :=
  ∃ g : Fin k → Fin m → Polynomial ℝ,
    f = ∑ i, ∏ j, g i j ∧ ∀ i j, (g i j).support.card ≤ t

/-- Characterization of `InRealSPS`. -/
theorem inRealSPS_iff {k m t : ℕ} {f : Polynomial ℝ} :
    InRealSPS k m t f ↔
      ∃ g : Fin k → Fin m → Polynomial ℝ,
        f = ∑ i, ∏ j, g i j ∧ ∀ i j, (g i j).support.card ≤ t :=
  Iff.rfl

/-- The number of sign variations of a real polynomial is at most `P.support.card - 1`. -/
theorem signVariations_le_card_support_sub_one (P : Polynomial ℝ) :
    Polynomial.signVariations P ≤ P.support.card - 1 := by
  have haux : ∀ n : ℕ, ∀ P : Polynomial ℝ,
      P.support.card = n → Polynomial.signVariations P ≤ n - 1 := by
    intro n
    induction n with
    | zero =>
      intro P hP
      have h0 : P = 0 := Polynomial.support_eq_empty.mp (Finset.card_eq_zero.mp hP)
      subst h0; simp
    | succ n ih =>
      intro P hP
      have hP0 : P ≠ 0 := by
        intro h0; subst h0; simp at hP
      cases n with
      | zero =>
        have hE0 : P.eraseLead = 0 := by
          have hc := Polynomial.card_support_eraseLead_add_one hP0
          have : P.eraseLead.support.card = 0 := by omega
          exact Polynomial.support_eq_empty.mp (Finset.card_eq_zero.mp this)
        rw [Polynomial.signVariations_eq_eraseLead_add_ite hP0, hE0]
        simp [hP0]
      | succ m =>
        have hc := Polynomial.card_support_eraseLead_add_one hP0
        have hrec := ih P.eraseLead (by omega)
        have hstep := Polynomial.signVariations_le_eraseLead_succ (P := P)
        omega
  exact haux P.support.card P rfl

/-- Composing a real polynomial with `-X` multiplies the `d`-th coefficient by `(-1)^d`. -/
private theorem coeff_comp_neg_X (P : Polynomial ℝ) (d : ℕ) :
    (P.comp (-Polynomial.X)).coeff d = (-1 : ℝ) ^ d * P.coeff d := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, ihp, ihq, mul_add]
  | monomial k a =>
    rw [Polynomial.monomial_comp, neg_pow, ← Polynomial.C_mul_X_pow_eq_monomial,
      show (-1 : Polynomial ℝ) ^ k = Polynomial.C ((-1 : ℝ) ^ k) by simp,
      ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    by_cases hkd : d = k
    · subst hkd; simp [mul_comm]
    · simp [hkd]

/-- Composing a real polynomial with `-X` preserves the support cardinality. -/
private theorem card_support_comp_neg_X (P : Polynomial ℝ) :
    (P.comp (-Polynomial.X)).support.card = P.support.card := by
  have hsupp : (P.comp (-Polynomial.X)).support = P.support := by
    ext d
    simp only [Polynomial.mem_support_iff, coeff_comp_neg_X]
    have hne : (-1 : ℝ) ^ d ≠ 0 := pow_ne_zero d (by norm_num)
    simp [hne]
  rw [hsupp]

/-- Every real polynomial `P` has at most `2 * (P.support.card - 1)` nonzero real roots counted
with multiplicity. -/
theorem roots_countP_ne_zero_le (P : Polynomial ℝ) :
    P.roots.countP (fun x : ℝ ↦ decide (x ≠ 0)) ≤ 2 * (P.support.card - 1) := by
  have hpos : P.roots.countP (fun x : ℝ ↦ decide (0 < x)) ≤ P.support.card - 1 :=
    (Polynomial.roots_countP_pos_le_signVariations (P := P)).trans
      (signVariations_le_card_support_sub_one P)
  have hneg : P.roots.countP (fun x : ℝ ↦ decide (x < 0)) ≤ P.support.card - 1 := by
    have h1 : (P.comp (-Polynomial.X)).roots.countP (fun x : ℝ ↦ decide (0 < x)) ≤
        (P.comp (-Polynomial.X)).support.card - 1 :=
      (Polynomial.roots_countP_pos_le_signVariations (P := P.comp (-Polynomial.X))).trans
        (signVariations_le_card_support_sub_one _)
    rw [card_support_comp_neg_X, Polynomial.roots_comp_neg_X, Multiset.countP_map] at h1
    rw [Multiset.countP_eq_card_filter]
    simpa [Function.comp_def] using h1
  have hsplit : P.roots.countP (fun x : ℝ ↦ decide (x ≠ 0)) =
      P.roots.countP (fun x : ℝ ↦ decide (0 < x)) +
      P.roots.countP (fun x : ℝ ↦ decide (x < 0)) := by
    induction P.roots using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.countP_cons, ih]
      rcases lt_trichotomy a 0 with hlt | rfl | hgt
      · simp [hlt, ne_of_lt hlt, not_lt.mpr (le_of_lt hlt)]; omega
      · simp
      · simp [hgt, ne_of_gt hgt, not_lt.mpr (le_of_lt hgt)]; omega
  omega

/-- Every real polynomial `P` has at most `2 * (P.support.card - 1)` distinct nonzero real
roots. -/
theorem card_nonzero_roots_toFinset_le (P : Polynomial ℝ) :
    (P.roots.toFinset.filter fun x : ℝ ↦ x ≠ 0).card ≤ 2 * (P.support.card - 1) := by
  have h1 : (P.roots.toFinset.filter fun x : ℝ ↦ x ≠ 0).card ≤
      P.roots.countP (fun x : ℝ ↦ decide (x ≠ 0)) := by
    rw [Multiset.countP_eq_card_filter]
    have hsub : P.roots.toFinset.filter (fun x : ℝ ↦ x ≠ 0) =
        (P.roots.filter (fun x : ℝ ↦ decide (x ≠ 0))).toFinset := by
      ext x
      simp [Multiset.mem_toFinset]
    rw [hsub]
    exact Multiset.toFinset_card_le _
  exact h1.trans (roots_countP_ne_zero_le P)

/-- Every nonzero real polynomial `P` has at most `2 * P.support.card - 1` distinct real roots. -/
theorem card_roots_toFinset_le_of_support_card {P : Polynomial ℝ} (hP : P ≠ 0) :
    P.roots.toFinset.card ≤ 2 * P.support.card - 1 := by
  have hcard1 : 1 ≤ P.support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  have hpart : P.roots.toFinset.card =
      (P.roots.toFinset.filter fun x : ℝ ↦ x ≠ 0).card +
      (P.roots.toFinset.filter fun x : ℝ ↦ x = 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := P.roots.toFinset) (p := fun x : ℝ ↦ x ≠ 0)
    simpa [not_not] using this.symm
  have h0 : (P.roots.toFinset.filter fun x : ℝ ↦ x = 0).card ≤ 1 := by
    refine (Finset.card_le_card (t := ({0} : Finset ℝ)) ?_).trans (by simp)
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2]
  have hnz := card_nonzero_roots_toFinset_le P
  omega

/-- Every nonzero product of `m` real polynomials, each with at most `t` monomials, has at most
`2 * m * (t - 1) + 1` distinct real roots. -/
theorem real_roots_bound_k_eq_one {m t : ℕ} {f : Polynomial ℝ} (hf : InRealSPS 1 m t f)
    (hf0 : f ≠ 0) :
    f.roots.toFinset.card ≤ 2 * m * (t - 1) + 1 := by
  obtain ⟨g, hfeq, hsupp⟩ := inRealSPS_iff.mp hf
  have hprod : f = ∏ j : Fin m, g 0 j := by simpa [Fin.sum_univ_one] using hfeq
  have hgnz : ∀ j : Fin m, g 0 j ≠ 0 := fun j h0 ↦
    hf0 (by rw [hprod]; exact Finset.prod_eq_zero (Finset.mem_univ j) h0)
  have hpart : f.roots.toFinset.card =
      (f.roots.toFinset.filter fun x : ℝ ↦ x ≠ 0).card +
      (f.roots.toFinset.filter fun x : ℝ ↦ x = 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := f.roots.toFinset) (p := fun x : ℝ ↦ x ≠ 0)
    simpa [not_not] using this.symm
  have h0 : (f.roots.toFinset.filter fun x : ℝ ↦ x = 0).card ≤ 1 := by
    refine (Finset.card_le_card (t := ({0} : Finset ℝ)) ?_).trans (by simp)
    intro x hx; simp [(Finset.mem_filter.mp hx).2]
  have hsub : f.roots.toFinset.filter (fun x : ℝ ↦ x ≠ 0) ⊆
      Finset.univ.biUnion fun j : Fin m ↦ (g 0 j).roots.toFinset.filter (fun x : ℝ ↦ x ≠ 0) := by
    intro x hx
    obtain ⟨hxR, hx0⟩ := Finset.mem_filter.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def, hprod,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hxR
    obtain ⟨j, -, hj⟩ := hxR
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨?_, hx0⟩⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hgnz j)]
    exact hj
  have hnz : (f.roots.toFinset.filter fun x : ℝ ↦ x ≠ 0).card ≤ 2 * m * (t - 1) := by
    calc (f.roots.toFinset.filter fun x : ℝ ↦ x ≠ 0).card
        ≤ (Finset.univ.biUnion fun j : Fin m ↦
            (g 0 j).roots.toFinset.filter (fun x : ℝ ↦ x ≠ 0)).card := Finset.card_le_card hsub
      _ ≤ ∑ j : Fin m, ((g 0 j).roots.toFinset.filter (fun x : ℝ ↦ x ≠ 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ j : Fin m, 2 * ((g 0 j).support.card - 1) :=
          Finset.sum_le_sum fun j _ ↦ card_nonzero_roots_toFinset_le (g 0 j)
      _ ≤ ∑ _j : Fin m, 2 * (t - 1) :=
          Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right (hsupp 0 j) 1)
      _ = 2 * m * (t - 1) := by simp; ring
  omega

/-- Support cardinality of a product of `m` real polynomials each with at most `t` monomials is at
most `t ^ m`. -/
private theorem card_support_prod_le {m t : ℕ} (g : Fin m → Polynomial ℝ)
    (hg : ∀ j, (g j).support.card ≤ t) :
    (∏ j : Fin m, g j).support.card ≤ t ^ m := by
  induction m with
  | zero =>
    have h1 : (1 : Polynomial ℝ) = Polynomial.monomial 0 1 := by simp
    simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero]
    rw [h1, Polynomial.support_monomial 0 one_ne_zero]; simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc, pow_succ]
    have h1 := ih (fun j ↦ g j.castSucc) (fun j ↦ hg j.castSucc)
    have h2 := hg (Fin.last m)
    have hmul : ∀ P Q : Polynomial ℝ, (P * Q).support.card ≤ P.support.card * Q.support.card := by
      intro P Q
      have hsub : (P * Q).support ⊆ (P.support ×ˢ Q.support).image (fun p ↦ p.1 + p.2) := by
        intro d hd
        rw [Polynomial.mem_support_iff, Polynomial.coeff_mul] at hd
        by_contra hnot
        apply hd
        refine Finset.sum_eq_zero fun pq hpq ↦ ?_
        by_cases h1' : pq.1 ∈ P.support
        · by_cases h2' : pq.2 ∈ Q.support
          · exfalso; apply hnot
            exact Finset.mem_image.mpr ⟨pq, Finset.mem_product.mpr ⟨h1', h2'⟩,
              Finset.mem_antidiagonal.mp hpq⟩
          · rw [Polynomial.notMem_support_iff.mp h2']; simp
        · rw [Polynomial.notMem_support_iff.mp h1']; simp
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
    exact (hmul _ _).trans (Nat.mul_le_mul h1 h2)

/-- Every nonzero sum of `k` products of `m` real polynomials, each with at most `t` monomials
(`k, t ≥ 1`), has at most `2 * k * t ^ m - 1` distinct real roots. -/
theorem real_roots_bound_general {k m t : ℕ} {f : Polynomial ℝ} (hf : InRealSPS k m t f)
    (hf0 : f ≠ 0) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    f.roots.toFinset.card ≤ 2 * k * t ^ m - 1 := by
  obtain ⟨g, hfeq, hsupp⟩ := inRealSPS_iff.mp hf
  have hfSupp : f.support.card ≤ k * t ^ m := by
    rw [hfeq]
    have hsum : ∀ s : Finset (Fin k),
        (∑ i ∈ s, ∏ j : Fin m, g i j).support.card ≤
          ∑ i ∈ s, (∏ j : Fin m, g i j).support.card := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact ((Finset.card_le_card Polynomial.support_add).trans
          (Finset.card_union_le _ _)).trans (Nat.add_le_add_left ih _)
    calc (∑ i : Fin k, ∏ j : Fin m, g i j).support.card
        ≤ ∑ i : Fin k, (∏ j : Fin m, g i j).support.card := hsum Finset.univ
      _ ≤ ∑ _i : Fin k, t ^ m := Finset.sum_le_sum fun i _ ↦ card_support_prod_le (g i) (hsupp i)
      _ = k * t ^ m := by simp
  have h1 := card_roots_toFinset_le_of_support_card hf0
  have hkt : 1 ≤ k * t ^ m := Nat.mul_pos hk (Nat.pow_pos ht)
  have hmul : 2 * f.support.card ≤ 2 * (k * t ^ m) := Nat.mul_le_mul_left 2 hfSupp
  have hassoc : 2 * (k * t ^ m) = 2 * k * t ^ m := by ring
  omega

end CslibFrontier.Polynomial
