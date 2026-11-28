/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Roots-of-unity hitting sets for sparse univariate polynomials

Over a field of characteristic zero, any nonzero univariate polynomial of degree at most `d ≥ 2`
with at most `m` nonzero monomials vanishes modulo `X ^ p - 1` for strictly fewer than `m * log d`
primes `p`, and likewise is divisible by the `p`-th cyclotomic polynomial `Φ_p` for strictly fewer
than `m * log d` primes `p`. Consequently, for any finite set `P` of at least `m * log d` primes,
both the set of all `p`-th roots of unity and the smaller set of primitive `p`-th roots of unity
(for `p ∈ P`) in an algebraically closed extension form a hitting set for all `m`-sparse
univariate polynomials of degree at most `d`.

This complements the prime-power hitting set for multivariate sparse polynomials with a
roots-of-unity construction tailored to univariate sparse polynomials and yields a direct
lower-bound principle: any nonzero multiple of `∏ p ∈ P, (X ^ p - 1)` lies outside every class of
univariate polynomials hit by the `p`-th roots of unity for `p ∈ P`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.rootsOfUnityHittingSet`: the `Finset` of
  1-dimensional points `(θ)` where `θ` ranges over all `p`-th roots of unity for `p ∈ P`.
* `CslibFrontier.Computability.Circuit.Arithmetic.primitiveRootsOfUnityHittingSet`: the `Finset`
  of 1-dimensional points `(θ)` where `θ` ranges over all primitive `p`-th roots of unity for
  `p ∈ P`.

## Main results

* `card_primes_X_pow_sub_one_dvd_lt`: fewer than `m * Real.log d` primes `p` satisfy
  `X ^ p - 1 ∣ f` for a nonzero `m`-sparse polynomial `f` of degree at most `d ≥ 2`.
* `card_primes_cyclotomic_dvd_lt`: fewer than `m * Real.log d` primes `p` satisfy
  `cyclotomic p K ∣ f` under the same hypotheses.
* `isHittingSet_primitiveRootsOfUnityHittingSet` and `isHittingSet_rootsOfUnityHittingSet`:
  `Cslib.Circuits.Arithmetic.IsHittingSet` certificates for `m`-sparse univariate polynomials of
  degree at most `d ≥ 2`.
* `not_mem_of_primeProd_dvd`: any nonzero multiple of `∏ p ∈ P, (X₀ ^ p - 1)` lies outside any
  polynomial class hit by `rootsOfUnityHittingSet P`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic

open Polynomial Finset Cslib.Circuits.Arithmetic

/-- The `Finset` of 1-variable evaluation points `(θ)` as `θ` ranges over all `p`-th roots of
unity in `F` for `p ∈ P`. -/
noncomputable def rootsOfUnityHittingSet {F : Type*} [Field F] [DecidableEq F]
    (P : Finset ℕ) : Finset (Fin 1 → F) :=
  (P.biUnion fun p => Polynomial.nthRootsFinset p (1 : F)).image fun θ _ => θ

/-- The `Finset` of 1-variable evaluation points `(θ)` as `θ` ranges over all primitive `p`-th
roots of unity in `F` for `p ∈ P`. -/
noncomputable def primitiveRootsOfUnityHittingSet {F : Type*} [Field F] [DecidableEq F]
    (P : Finset ℕ) : Finset (Fin 1 → F) :=
  (P.biUnion fun p => primitiveRoots p F).image fun θ _ => θ

/-- Primitive `p`-th roots of unity form a subset of all `p`-th roots of unity when every
`p ∈ P` is positive. -/
theorem primitiveRootsOfUnityHittingSet_subset {F : Type*} [Field F] [DecidableEq F]
    {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    primitiveRootsOfUnityHittingSet (F := F) P ⊆ rootsOfUnityHittingSet P := by
  intro pt hpt
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hpt
  obtain ⟨p, hp, hprim⟩ := Finset.mem_biUnion.mp hθ
  refine Finset.mem_image.mpr ⟨θ, Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩, rfl⟩
  rw [Polynomial.mem_nthRootsFinset (hP p hp)]
  exact ((mem_primitiveRoots (hP p hp)).mp hprim).pow_eq_one

private lemma X_pow_sub_one_dvd_X_pow_sub_mod {K : Type*} [CommRing K] (p e : ℕ) :
    (X ^ p - 1 : K[X]) ∣ X ^ e - X ^ (e % p) := by
  have he : p * (e / p) + e % p = e := Nat.div_add_mod e p
  have h1 : (X ^ e - X ^ (e % p) : K[X]) = X ^ (e % p) * ((X ^ p) ^ (e / p) - 1) := by
    calc (X ^ e - X ^ (e % p) : K[X])
        = X ^ (p * (e / p) + e % p) - X ^ (e % p) := by rw [he]
      _ = X ^ (e % p) * ((X ^ p) ^ (e / p) - 1) := by rw [pow_add, pow_mul]; ring
  rw [h1]
  have hdvd : (X ^ p - 1 : K[X]) ∣ (X ^ p) ^ (e / p) - 1 := by
    simpa using sub_dvd_pow_sub_pow (X ^ p : K[X]) 1 (e / p)
  exact dvd_mul_of_dvd_right hdvd _

private noncomputable def modXPowSubOne {K : Type*} [CommRing K] (p : ℕ) (f : K[X]) : K[X] :=
  ∑ e ∈ f.support, C (f.coeff e) * X ^ (e % p)

private lemma X_pow_sub_one_dvd_sub_modXPowSubOne {K : Type*} [CommRing K] (p : ℕ)
    (f : K[X]) : (X ^ p - 1 : K[X]) ∣ f - modXPowSubOne p f := by
  have hf : f = ∑ e ∈ f.support, C (f.coeff e) * X ^ e := f.as_sum_support_C_mul_X_pow
  have hsub : f - modXPowSubOne p f =
      ∑ e ∈ f.support, C (f.coeff e) * (X ^ e - X ^ (e % p)) := by
    rw [modXPowSubOne]
    conv_lhs => arg 1; rw [hf]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hsub]
  exact Finset.dvd_sum fun e _ => dvd_mul_of_dvd_right (X_pow_sub_one_dvd_X_pow_sub_mod p e) _

private lemma coeff_modXPowSubOne {K : Type*} [CommRing K] (p : ℕ) (f : K[X]) (r : ℕ) :
    (modXPowSubOne p f).coeff r = ∑ e ∈ f.support with e % p = r, f.coeff e := by
  classical
  rw [modXPowSubOne, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

private lemma natDegree_modXPowSubOne_lt {K : Type*} [CommRing K] {p : ℕ} (hp : 0 < p)
    (f : K[X]) : (modXPowSubOne p f).natDegree < p := by
  classical
  have hle : (modXPowSubOne p f).natDegree ≤ p - 1 := by
    refine (natDegree_sum_le f.support _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun e _ => Nat.le_sub_one_of_lt ?_⟩
    exact (natDegree_C_mul_X_pow_le (f.coeff e) (e % p)).trans_lt (Nat.mod_lt e hp)
  omega

private lemma exists_other_modEq_of_X_pow_sub_one_dvd {K : Type*} [CommRing K] [IsDomain K]
    {p : ℕ} (hp : 0 < p) {f : K[X]} (hdvd : (X ^ p - 1 : K[X]) ∣ f)
    {e₀ : ℕ} (he₀ : e₀ ∈ f.support) :
    ∃ e ∈ f.support, e ≠ e₀ ∧ e % p = e₀ % p := by
  classical
  have hg_dvd : (X ^ p - 1 : K[X]) ∣ modXPowSubOne p f := by
    have h1 := X_pow_sub_one_dvd_sub_modXPowSubOne p f
    have h2 : modXPowSubOne p f = f - (f - modXPowSubOne p f) := by ring
    rw [h2]
    exact dvd_sub hdvd h1
  have hg_zero : modXPowSubOne p f = 0 := by
    by_contra hg0
    have hdeg_le : (X ^ p - 1 : K[X]).natDegree ≤ (modXPowSubOne p f).natDegree :=
      natDegree_le_of_dvd hg_dvd hg0
    have hdeg_p : (X ^ p - 1 : K[X]).natDegree = p := by
      rw [← map_one C, natDegree_X_pow_sub_C]
    have hlt := natDegree_modXPowSubOne_lt hp f
    omega
  have hcoeff0 : (modXPowSubOne p f).coeff (e₀ % p) = 0 := by rw [hg_zero, coeff_zero]
  rw [coeff_modXPowSubOne] at hcoeff0
  by_contra hno
  push Not at hno
  have hfilt : (f.support.filter fun e => e % p = e₀ % p) = {e₀} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hmod⟩
      by_contra hne
      exact hno e he hne hmod
    · rintro rfl
      exact ⟨he₀, rfl⟩
  rw [hfilt, Finset.sum_singleton] at hcoeff0
  exact (mem_support_iff.mp he₀) hcoeff0

private lemma three_pow_lt_prod_primes {S : Finset ℕ} (hP : ∀ p ∈ S, p.Prime)
    (hcard : 3 ≤ S.card) : 3 ^ S.card < ∏ p ∈ S, p := by
  classical
  let small : Finset ℕ := {2, 3, 5}
  let A := S ∩ small
  let B := S \ small
  have hdisj : Disjoint A B := (Finset.disjoint_sdiff_inter S small).symm
  have hunion : A ∪ B = S := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_inter S small
  have hcard_eq : A.card + B.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hprod_eq : (∏ p ∈ A, p) * (∏ p ∈ B, p) = ∏ p ∈ S, p := by
    rw [← Finset.prod_union hdisj, hunion]
  have hB_ge : 7 ^ B.card ≤ ∏ p ∈ B, p := by
    calc 7 ^ B.card = ∏ _ ∈ B, 7 := by simp
      _ ≤ ∏ p ∈ B, p := Finset.prod_le_prod fun p hp => by
          have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
          have hns : p ∉ small := (Finset.mem_sdiff.mp hp).2
          have hpr : p.Prime := hP p hpS
          have h2 : p ≠ 2 := fun h => hns (by simp [small, h])
          have h3 : p ≠ 3 := fun h => hns (by simp [small, h])
          have h5 : p ≠ 5 := fun h => hns (by simp [small, h])
          have hge2 := hpr.two_le
          have h4 : p ≠ 4 := fun h => by subst h; exact absurd hpr (by decide)
          have h6 : p ≠ 6 := fun h => by subst h; exact absurd hpr (by decide)
          omega
  have hA_sub : A ⊆ small := Finset.inter_subset_right
  have hA_card : A.card ≤ 3 := (Finset.card_le_card hA_sub).trans (by decide)
  rw [← hcard_eq, ← hprod_eq]
  have hpow_step : ∀ k : ℕ, 3 ^ k ≤ 7 ^ k := fun k => Nat.pow_le_pow_left (by decide) k
  interval_cases hAc : A.card
  · have hB3 : 3 ≤ B.card := by omega
    have hA1 : ∏ p ∈ A, p = 1 := by
      rw [Finset.card_eq_zero.mp hAc, Finset.prod_empty]
    rw [hA1, zero_add, one_mul]
    exact (Nat.pow_lt_pow_left (by decide : 3 < 7) (by omega)).trans_le hB_ge
  · have hB2 : 2 ≤ B.card := by omega
    have hA2 : 2 ≤ ∏ p ∈ A, p := by
      obtain ⟨p, hpA⟩ := Finset.card_eq_one.mp hAc
      rw [hpA, Finset.prod_singleton]
      have hp_mem : p ∈ A := by rw [hpA]; simp
      exact (hP p (Finset.mem_inter.mp hp_mem).1).two_le
    have h7b : 3 ^ (1 + B.card) < 2 * 7 ^ B.card := by
      obtain ⟨k, hkB⟩ := Nat.exists_eq_add_of_le' hB2
      rw [hkB]
      calc 3 ^ (1 + (k + 2)) = 27 * 3 ^ k := by ring
        _ ≤ 27 * 7 ^ k := Nat.mul_le_mul_left 27 (hpow_step k)
        _ < 98 * 7 ^ k := by
          have : 0 < 7 ^ k := by positivity
          omega
        _ = 2 * 7 ^ (k + 2) := by ring
    exact h7b.trans_le (Nat.mul_le_mul hA2 hB_ge)
  · have hB1 : 1 ≤ B.card := by omega
    have hA6 : 6 ≤ ∏ p ∈ A, p := by
      obtain ⟨p, q, hpq, hpqA⟩ := Finset.card_eq_two.mp hAc
      rw [hpqA, Finset.prod_pair hpq]
      have hp_mem : p ∈ A := by rw [hpqA]; simp
      have hq_mem : q ∈ A := by rw [hpqA]; simp
      have hp2 : 2 ≤ p := (hP p (Finset.mem_inter.mp hp_mem).1).two_le
      have hq2 : 2 ≤ q := (hP q (Finset.mem_inter.mp hq_mem).1).two_le
      have : (2 ≤ p ∧ 3 ≤ q) ∨ (3 ≤ p ∧ 2 ≤ q) := by omega
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith
    have h7b : 3 ^ (2 + B.card) < 6 * 7 ^ B.card := by
      obtain ⟨k, hkB⟩ := Nat.exists_eq_add_of_le' hB1
      rw [hkB]
      calc 3 ^ (2 + (k + 1)) = 27 * 3 ^ k := by ring
        _ ≤ 27 * 7 ^ k := Nat.mul_le_mul_left 27 (hpow_step k)
        _ < 42 * 7 ^ k := by
          have : 0 < 7 ^ k := by positivity
          omega
        _ = 6 * 7 ^ (k + 1) := by ring
    exact h7b.trans_le (Nat.mul_le_mul hA6 hB_ge)
  · have hAeq : A = small := Finset.eq_of_subset_of_card_le hA_sub (by rw [hAc]; decide)
    have hA30 : ∏ p ∈ A, p = 30 := by rw [hAeq]; decide
    rw [hA30]
    calc 3 ^ (3 + B.card) = 27 * 3 ^ B.card := by ring
      _ ≤ 27 * 7 ^ B.card := Nat.mul_le_mul_left 27 (hpow_step B.card)
      _ < 30 * 7 ^ B.card := by
        have : 0 < 7 ^ B.card := by positivity
        omega
      _ ≤ 30 * ∏ p ∈ B, p := Nat.mul_le_mul_left 30 hB_ge

private lemma one_lt_two_mul_log_two : (1 : ℝ) < 2 * Real.log 2 := by
  have hexp : Real.exp 1 < (2 : ℝ) ^ (2 : ℕ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp, Real.log_pow, Nat.cast_ofNat] at hlog

private lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp] at hlog

/-- A nonzero univariate polynomial of degree at most `d ≥ 2` with at most `m` nonzero monomials
over any field is divisible by `X ^ p - 1` for strictly fewer than `m * Real.log d` primes `p`. -/
theorem card_primes_X_pow_sub_one_dvd_lt {K : Type*} [Field K]
    {f : K[X]} (hf0 : f ≠ 0) {d m : ℕ} (hd : 2 ≤ d)
    (hdeg : f.natDegree ≤ d) (hsupp : f.support.card ≤ m)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ (X ^ p - 1 : K[X]) ∣ f) :
    (S.card : ℝ) < (m : ℝ) * Real.log (d : ℝ) := by
  classical
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf0
  have hm1 : 1 ≤ m := hne.card_pos.trans_le hsupp
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogd_ge : Real.log 2 ≤ Real.log (d : ℝ) :=
    Real.log_le_log two_pos (by exact_mod_cast hd)
  let e₀ := f.support.min' hne
  have he₀_mem : e₀ ∈ f.support := Finset.min'_mem f.support hne
  let D : ℕ := ∏ e ∈ f.support.erase e₀, (e - e₀)
  have hD_pos : 0 < D := Finset.prod_pos fun e he => by
    have hne_e : e ≠ e₀ := (Finset.mem_erase.mp he).1
    have hle_e : e₀ ≤ e := Finset.min'_le f.support e (Finset.mem_erase.mp he).2
    omega
  have hD_le : D ≤ d ^ (m - 1) := by
    calc D = ∏ e ∈ f.support.erase e₀, (e - e₀) := rfl
      _ ≤ ∏ _ ∈ f.support.erase e₀, d := Finset.prod_le_prod fun e he => by
          have he_mem : e ∈ f.support := (Finset.mem_erase.mp he).2
          have he_le : e ≤ f.natDegree := Polynomial.le_natDegree_of_mem_supp e he_mem
          omega
      _ = d ^ (f.support.erase e₀).card := by simp
      _ ≤ d ^ (m - 1) := by
          apply Nat.pow_le_pow_right (by omega)
          rw [Finset.card_erase_of_mem he₀_mem]
          omega
  have hprod_dvd_D : (∏ p ∈ S, p) ∣ D := by
    refine Finset.prod_primes_dvd D (fun p hp => (hS p hp).1.prime) fun p hp => ?_
    obtain ⟨hp_prime, hp_dvd⟩ := hS p hp
    obtain ⟨e, he_mem, he_ne, he_mod⟩ :=
      exists_other_modEq_of_X_pow_sub_one_dvd hp_prime.pos hp_dvd he₀_mem
    have hle : e₀ ≤ e := Finset.min'_le f.support e he_mem
    have hp_sub : p ∣ (e - e₀) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have hsub := Nat.ModEq.sub_right hle le_rfl he_mod
      simpa [Nat.ModEq] using hsub
    exact hp_sub.trans (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨he_ne, he_mem⟩))
  have hprod_le_D : ∏ p ∈ S, p ≤ D := Nat.le_of_dvd hD_pos hprod_dvd_D
  by_cases h0 : S.card = 0
  · rw [h0, Nat.cast_zero]
    exact mul_pos (by exact_mod_cast (by omega : 0 < m)) (hlog2_pos.trans_le hlogd_ge)
  by_cases h1 : S.card = 1
  · rw [h1, Nat.cast_one]
    have h2m : 2 ≤ m := by
      by_contra hm_lt
      have herase : (f.support.erase e₀).card = 0 := by
        rw [Finset.card_erase_of_mem he₀_mem]; omega
      have hD1 : D = 1 := by simp [D, Finset.card_eq_zero.mp herase]
      obtain ⟨p, hpS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      have hp2 : 2 ≤ p := (hS p hpS).1.two_le
      have : p ≤ 1 := (Nat.le_of_dvd hD_pos
        ((Finset.dvd_prod_of_mem id hpS).trans hprod_dvd_D)).trans_eq hD1
      omega
    calc (1 : ℝ) < 2 * Real.log 2 := one_lt_two_mul_log_two
      _ ≤ (m : ℝ) * Real.log (d : ℝ) :=
        mul_le_mul (by exact_mod_cast h2m) hlogd_ge hlog2_pos.le (by positivity)
  by_cases h2 : S.card = 2
  · rw [h2, Nat.cast_ofNat]
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp h2
    have hp_pr : p.Prime := (hS p (by simp)).1
    have hq_pr : q.Prime := (hS q (by simp)).1
    have hpq_ge6 : 6 ≤ p * q := by
      have hp2 := hp_pr.two_le
      have hq2 := hq_pr.two_le
      have : (2 ≤ p ∧ 3 ≤ q) ∨ (3 ≤ p ∧ 2 ≤ q) := by omega
      rcases this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> nlinarith
    have hmax_ge3 : 3 ≤ max p q := by
      have hp2 := hp_pr.two_le
      have hq2 := hq_pr.two_le
      omega
    have hd3 : 3 ≤ d := by
      have hmem_max : max p q ∈ ({p, q} : Finset ℕ) := by
        rcases le_total p q with h | h <;> simp [h]
      obtain ⟨hpr_m, hdvd_m⟩ := hS (max p q) hmem_max
      obtain ⟨e, he_mem, he_ne, he_mod⟩ :=
        exists_other_modEq_of_X_pow_sub_one_dvd hpr_m.pos hdvd_m he₀_mem
      have hle : e₀ ≤ e := Finset.min'_le f.support e he_mem
      have hpos_sub : 0 < e - e₀ := by omega
      have hdiv : max p q ∣ (e - e₀) := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have hsub := Nat.ModEq.sub_right hle le_rfl he_mod
        simpa [Nat.ModEq] using hsub
      have hle_sub : max p q ≤ e - e₀ := Nat.le_of_dvd hpos_sub hdiv
      have he_le : e ≤ d := (Polynomial.le_natDegree_of_mem_supp e he_mem).trans hdeg
      omega
    have h6_le : 6 ≤ d ^ (m - 1) := by
      have hpr : ∏ r ∈ ({p, q} : Finset ℕ), r = p * q := Finset.prod_pair hpq
      exact hpq_ge6.trans ((hpr ▸ hprod_le_D).trans hD_le)
    have h2m : 2 ≤ m := by
      by_contra hlt
      have hm1' : m - 1 = 0 := by omega
      rw [hm1', pow_zero] at h6_le
      omega
    by_cases hm2 : m = 2
    · rw [hm2] at h6_le ⊢
      simp only [Nat.reduceSub, pow_one] at h6_le
      have hlog6 : (1 : ℝ) < Real.log (d : ℝ) :=
        one_lt_log_three.trans_le
          (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : 3 ≤ d)))
      push_cast
      linarith
    · have hm3 : 3 ≤ m := by omega
      have hlog3 : (1 : ℝ) < Real.log (d : ℝ) :=
        one_lt_log_three.trans_le (Real.log_le_log (by positivity) (by exact_mod_cast hd3))
      have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      nlinarith
  · have hcard3 : 3 ≤ S.card := by omega
    have hprod_gt : 3 ^ S.card < ∏ p ∈ S, p :=
      three_pow_lt_prod_primes (fun p hp => (hS p hp).1) hcard3
    have hexp_lt : Real.exp (S.card : ℝ) < (d : ℝ) ^ m := by
      have hexp3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp (S.card : ℝ) = (Real.exp 1) ^ S.card := by
            rw [← Real.exp_nat_mul, mul_one]
        _ < (3 : ℝ) ^ S.card := by gcongr
        _ < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hprod_gt
        _ ≤ ((d ^ (m - 1) : ℕ) : ℝ) := by exact_mod_cast (hprod_le_D.trans hD_le)
        _ ≤ ((d ^ m : ℕ) : ℝ) := by
            exact_mod_cast Nat.pow_le_pow_right (by omega) (Nat.sub_le m 1)
        _ = (d : ℝ) ^ m := by push_cast; rfl
    have hlog := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp, Real.log_pow] at hlog

private lemma isCoprime_cyclotomic_prime {K : Type*} [Field K] [CharZero K]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsCoprime (Polynomial.cyclotomic p K) (Polynomial.cyclotomic q K) := by
  suffices hQ : IsCoprime (Polynomial.cyclotomic p ℚ) (Polynomial.cyclotomic q ℚ) by
    simpa [Polynomial.map_cyclotomic] using hQ.map (Polynomial.mapRingHom (algebraMap ℚ K))
  have hirr_p := Polynomial.cyclotomic.irreducible_rat hp.pos
  have hirr_q := Polynomial.cyclotomic.irreducible_rat hq.pos
  refine hirr_p.coprime_iff_not_dvd.mpr fun hdvd => ?_
  have hassoc : Associated (Polynomial.cyclotomic p ℚ) (Polynomial.cyclotomic q ℚ) :=
    hirr_p.associated_of_dvd hirr_q hdvd
  have heq : Polynomial.cyclotomic p ℚ = Polynomial.cyclotomic q ℚ :=
    Polynomial.eq_of_monic_of_associated (Polynomial.cyclotomic.monic p ℚ)
      (Polynomial.cyclotomic.monic q ℚ) hassoc
  have hdeg := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_cyclotomic, Polynomial.natDegree_cyclotomic,
    Nat.totient_prime hp, Nat.totient_prime hq] at hdeg
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  omega

private lemma isCoprime_X_sub_one_cyclotomic_prime {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) :
    IsCoprime (X - 1 : K[X]) (Polynomial.cyclotomic p K) := by
  have : Fact p.Prime := ⟨hp⟩
  have heval : (Polynomial.cyclotomic p K).eval 1 = (p : K) := by
    rw [Polynomial.cyclotomic_prime, Polynomial.eval_finsetSum]
    simp
  have hne : (Polynomial.cyclotomic p K).eval 1 ≠ 0 := by
    rw [heval]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  have hirr : Irreducible (X - 1 : K[X]) := Polynomial.irreducible_X_sub_C (1 : K)
  refine hirr.coprime_iff_not_dvd.mpr fun hdvd => ?_
  exact hne (Polynomial.dvd_iff_isRoot.mp hdvd)

/-- A nonzero univariate polynomial of degree at most `d ≥ 2` with at most `m` nonzero monomials
over a field of characteristic zero is divisible by `cyclotomic p K` for strictly fewer than
`m * Real.log d` primes `p`. -/
theorem card_primes_cyclotomic_dvd_lt {K : Type*} [Field K] [CharZero K]
    {f : K[X]} (hf0 : f ≠ 0) {d m : ℕ} (hd : 2 ≤ d)
    (hdeg : f.natDegree ≤ d) (hsupp : f.support.card ≤ m)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ Polynomial.cyclotomic p K ∣ f) :
    (S.card : ℝ) < (m : ℝ) * Real.log (d : ℝ) := by
  classical
  by_cases hf1 : f.eval 1 = 0
  · have hX1 : (X - 1 : K[X]) ∣ f := Polynomial.dvd_iff_isRoot.mpr hf1
    refine card_primes_X_pow_sub_one_dvd_lt hf0 hd hdeg hsupp fun p hp => ?_
    obtain ⟨hp_pr, hp_cyc⟩ := hS p hp
    have : Fact p.Prime := ⟨hp_pr⟩
    refine ⟨hp_pr, ?_⟩
    rw [← Polynomial.cyclotomic_prime_mul_X_sub_one K p]
    exact (isCoprime_X_sub_one_cyclotomic_prime hp_pr).symm.mul_dvd hp_cyc hX1
  · have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf0
    have hm1 : 1 ≤ m := hne.card_pos.trans_le hsupp
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlogd_ge : Real.log 2 ≤ Real.log (d : ℝ) :=
      Real.log_le_log two_pos (by exact_mod_cast hd)
    by_cases hS0 : S.card = 0
    · rw [hS0, Nat.cast_zero]
      exact mul_pos (by exact_mod_cast (by omega : 0 < m)) (hlog2_pos.trans_le hlogd_ge)
    have hp_le_m : ∀ p ∈ S, p ≤ m := fun p hp => by
      obtain ⟨hp_pr, hp_cyc⟩ := hS p hp
      have : Fact p.Prime := ⟨hp_pr⟩
      have hcyc_dvd_sub : Polynomial.cyclotomic p K ∣ f - modXPowSubOne p f :=
        (Polynomial.cyclotomic.dvd_X_pow_sub_one p K).trans
          (X_pow_sub_one_dvd_sub_modXPowSubOne p f)
      have hcyc_dvd_g : Polynomial.cyclotomic p K ∣ modXPowSubOne p f := by
        have h2 : modXPowSubOne p f = f - (f - modXPowSubOne p f) := by ring
        rw [h2]
        exact dvd_sub hp_cyc hcyc_dvd_sub
      obtain ⟨q, hq⟩ := hcyc_dvd_g
      have hdeg_g := natDegree_modXPowSubOne_lt hp_pr.pos f
      have hdeg_cyc : (Polynomial.cyclotomic p K).natDegree = p - 1 := by
        rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp_pr]
      have hq_deg0 : q.natDegree = 0 := by
        by_cases hq0 : q = 0
        · simp [hq0]
        · have hmul := natDegree_mul (Polynomial.cyclotomic_ne_zero p K) hq0
          rw [← hq, hdeg_cyc] at hmul
          omega
      have hq_eq : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg0
      have hg1 : (modXPowSubOne p f).eval 1 = f.eval 1 := by
        have hsub1 : (f - modXPowSubOne p f).eval 1 = 0 := by
          have h1 : (X - 1 : K[X]) ∣ f - modXPowSubOne p f := by
            have hx : (X - 1 : K[X]) ∣ X ^ p - 1 := by
              rw [← Polynomial.cyclotomic_prime_mul_X_sub_one K p]
              exact dvd_mul_left _ _
            exact hx.trans (X_pow_sub_one_dvd_sub_modXPowSubOne p f)
          exact Polynomial.dvd_iff_isRoot.mp h1
        rw [eval_sub, sub_eq_zero] at hsub1
        exact hsub1.symm
      have hc_ne : q.coeff 0 ≠ 0 := by
        intro hc0
        rw [hq_eq, hc0, map_zero, mul_zero] at hq
        rw [hq, eval_zero] at hg1
        exact hf1 hg1.symm
      have hsub_img : Finset.range p ⊆ f.support.image (· % p) := by
        intro r hr
        have hcoeff_r : (modXPowSubOne p f).coeff r ≠ 0 := by
          rw [hq, hq_eq, mul_comm, coeff_C_mul, Polynomial.cyclotomic_prime,
            Polynomial.finsetSum_coeff]
          simp only [coeff_X_pow]
          rw [Finset.sum_ite_eq (Finset.range p) r]
          simpa [hr] using hc_ne
        rw [coeff_modXPowSubOne] at hcoeff_r
        obtain ⟨e, he, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff_r
        exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
      calc p = (Finset.range p).card := (Finset.card_range p).symm
        _ ≤ (f.support.image (· % p)).card := Finset.card_le_card hsub_img
        _ ≤ f.support.card := Finset.card_image_le
        _ ≤ m := hsupp
    have hS_sub : S ⊆ Finset.Icc 2 m := fun p hp =>
      Finset.mem_Icc.mpr ⟨(hS p hp).1.two_le, hp_le_m p hp⟩
    obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hS0)
    have hm2 : 2 ≤ m := (hS p₀ hp₀).1.two_le.trans (hp_le_m p₀ hp₀)
    have hScard_lt_m : S.card < m := by
      have h1 : S.card ≤ (Finset.Icc 2 m).card := Finset.card_le_card hS_sub
      rw [Nat.card_Icc] at h1
      omega
    by_cases hd3 : 3 ≤ d
    · have hlog3 : (1 : ℝ) < Real.log (d : ℝ) :=
        one_lt_log_three.trans_le (Real.log_le_log (by positivity) (by exact_mod_cast hd3))
      have hScard_lt : (S.card : ℝ) < (m : ℝ) := by exact_mod_cast hScard_lt_m
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      nlinarith
    · have hd2 : d = 2 := by omega
      have hprod_dvd : (∏ p ∈ S, Polynomial.cyclotomic p K) ∣ f := by
        refine Finset.prod_dvd_of_coprime ?_ (fun p hp => (hS p hp).2)
        intro p hp q hq hpq
        exact isCoprime_cyclotomic_prime (hS p hp).1 (hS q hq).1 hpq
      have hdeg_prod : (∏ p ∈ S, Polynomial.cyclotomic p K).natDegree =
          ∑ p ∈ S, (p - 1) := by
        rw [Polynomial.natDegree_prod_of_monic _ _ (fun p _ => Polynomial.cyclotomic.monic p K)]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime (hS p hp).1]
      have hsum_le : ∑ p ∈ S, (p - 1) ≤ 2 := by
        rw [← hdeg_prod]
        exact (natDegree_le_of_dvd hprod_dvd hf0).trans (hdeg.trans_eq hd2)
      have hScard1 : S.card = 1 := by
        by_contra hne1
        obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
        have hsub2 : ({p, q} : Finset ℕ) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hsum2 : (p - 1) + (q - 1) ≤ ∑ r ∈ S, (r - 1) := by
          rw [← Finset.sum_pair hpq (f := fun r => r - 1)]
          exact Finset.sum_le_sum_of_subset hsub2
        have hp2 := (hS p hp).1.two_le
        have hq2 := (hS q hq).1.two_le
        omega
      rw [hScard1, Nat.cast_one, hd2]
      calc (1 : ℝ) < 2 * Real.log 2 := one_lt_two_mul_log_two
        _ ≤ (m : ℝ) * Real.log (2 : ℕ) := by
          push_cast
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm2) hlog2_pos.le

private lemma eval_uniqueAlgEquiv {F : Type*} [Field F] (x : F) (p : MvPolynomial (Fin 1) F) :
    MvPolynomial.eval (fun _ : Fin 1 => x) p =
      Polynomial.eval x (MvPolynomial.uniqueAlgEquiv F (Fin 1) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [hp]

/-- For a finite set `P` of at least `m * Real.log d` primes (`2 ≤ d`), the primitive `p`-th
roots of unity (`p ∈ P`) in an algebraically closed field `F` of characteristic zero form a
hitting set for all 1-variate polynomials of degree at most `d` with at most `m` monomials. -/
theorem isHittingSet_primitiveRootsOfUnityHittingSet {F : Type*} [Field F] [CharZero F]
    [IsAlgClosed F] [DecidableEq F]
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {d m : ℕ} (hd : 2 ≤ d) (hcard : (m : ℝ) * Real.log (d : ℝ) ≤ (P.card : ℝ)) :
    IsHittingSet (primitiveRootsOfUnityHittingSet (F := F) P)
      {p : MvPolynomial (Fin 1) F |
        (MvPolynomial.uniqueAlgEquiv F (Fin 1) p).natDegree ≤ d ∧
        (MvPolynomial.uniqueAlgEquiv F (Fin 1) p).support.card ≤ m} := by
  intro f ⟨hdeg, hsupp⟩ hf0
  let e := MvPolynomial.uniqueAlgEquiv F (Fin 1)
  have hf'0 : e f ≠ 0 := fun h0 => hf0 (e.injective (by simpa using h0))
  by_contra hall
  push Not at hall
  have hdvd : ∀ p ∈ P, p.Prime ∧ Polynomial.cyclotomic p F ∣ e f := fun p hp => by
    have hp_pr := hP p hp
    have : NeZero (p : F) := ⟨Nat.cast_ne_zero.mpr hp_pr.ne_zero⟩
    refine ⟨hp_pr, ?_⟩
    have hsep := Polynomial.separable_cyclotomic p F
    have hsplits : (Polynomial.cyclotomic p F).Splits := IsAlgClosed.splits _
    rw [hsplits.eq_prod_roots_of_monic (Polynomial.cyclotomic.monic p F)]
    have hnd := Polynomial.nodup_roots hsep
    have hprod_eq : ((Polynomial.cyclotomic p F).roots.map fun a => X - C a).prod =
        ∏ θ ∈ (Polynomial.cyclotomic p F).roots.toFinset, (X - C θ) := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [hprod_eq]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
    · intro θ hθ_mem
      have hθ_root : θ ∈ (Polynomial.cyclotomic p F).roots := Multiset.mem_toFinset.mp hθ_mem
      have hroot := (Polynomial.mem_roots (Polynomial.cyclotomic_ne_zero p F)).mp hθ_root
      have hprim := (Polynomial.isRoot_cyclotomic_iff_charZero hp_pr.pos).mp hroot
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, ← eval_uniqueAlgEquiv]
      exact hall (fun _ => θ) (Finset.mem_image.mpr
        ⟨θ, Finset.mem_biUnion.mpr ⟨p, hp, (mem_primitiveRoots hp_pr.pos).mpr hprim⟩, rfl⟩)
  have hlt := card_primes_cyclotomic_dvd_lt hf'0 hd hdeg hsupp hdvd
  linarith

/-- For a finite set `P` of at least `m * Real.log d` primes (`2 ≤ d`), all `p`-th roots of unity
(`p ∈ P`) in an algebraically closed field `F` of characteristic zero form a hitting set for all
1-variate polynomials of degree at most `d` with at most `m` monomials. -/
theorem isHittingSet_rootsOfUnityHittingSet {F : Type*} [Field F] [CharZero F]
    [IsAlgClosed F] [DecidableEq F]
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {d m : ℕ} (hd : 2 ≤ d) (hcard : (m : ℝ) * Real.log (d : ℝ) ≤ (P.card : ℝ)) :
    IsHittingSet (rootsOfUnityHittingSet (F := F) P)
      {p : MvPolynomial (Fin 1) F |
        (MvPolynomial.uniqueAlgEquiv F (Fin 1) p).natDegree ≤ d ∧
        (MvPolynomial.uniqueAlgEquiv F (Fin 1) p).support.card ≤ m} :=
  (isHittingSet_primitiveRootsOfUnityHittingSet hP hd hcard).mono
    (primitiveRootsOfUnityHittingSet_subset fun p hp => (hP p hp).pos) Set.Subset.rfl

/-- Lower-bound principle from roots-of-unity hitting sets: if `rootsOfUnityHittingSet P` hits a
class `𝒞` of 1-variate polynomials, then no nonzero multiple of `∏ p ∈ P, (X₀ ^ p - 1)` belongs
to `𝒞`. -/
theorem not_mem_of_primeProd_dvd {F : Type*} [Field F] [DecidableEq F]
    {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) {𝒞 : Set (MvPolynomial (Fin 1) F)}
    (hhit : IsHittingSet (rootsOfUnityHittingSet (F := F) P) 𝒞)
    {Q : MvPolynomial (Fin 1) F} (hQ0 : Q ≠ 0)
    (hdvd : (∏ p ∈ P, (MvPolynomial.X 0 ^ p - 1 : MvPolynomial (Fin 1) F)) ∣ Q) :
    Q ∉ 𝒞 := by
  intro hmem
  obtain ⟨pt, hpt, hne⟩ := hhit Q hmem hQ0
  obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hpt
  obtain ⟨p, hp, hroot⟩ := Finset.mem_biUnion.mp hθ
  have hpow : θ ^ p = 1 := (Polynomial.mem_nthRootsFinset (hP p hp) (1 : F)).mp hroot
  obtain ⟨R, rfl⟩ := hdvd
  apply hne
  rw [map_mul, map_prod]
  have hzero : ∏ q ∈ P, MvPolynomial.eval (fun _ : Fin 1 => θ)
      (MvPolynomial.X 0 ^ q - 1 : MvPolynomial (Fin 1) F) = 0 :=
    Finset.prod_eq_zero hp (by simp [hpow])
  rw [hzero, zero_mul]

end CslibFrontier.Computability.Circuit.Arithmetic
