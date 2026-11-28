/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Nat.Log

import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Klivans–Spielman Modular Univariate Map for Sparse Polynomials

This module defines the modular Kronecker-style univariate specialization map
`x_i ↦ u ^ ((D + 1) ^ i mod p)` on multivariate polynomials over any commutative semiring,
proves its degree bound, and establishes the existence of a small modulus `p` that
simultaneously preserves nonvanishing of `M` sparse multivariate polynomials of bounded
total degree and support size.

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.HittingSet.ksModMap`: the univariate algebra homomorphism
  sending `X i` to `Polynomial.X ^ ((D + 1) ^ (i : ℕ) % p)`.

## Main results

* `CslibFrontier.Circuits.Arithmetic.HittingSet.natDegree_ksModMap_le`: degree bound
  `(ksModMap F n D p f).natDegree ≤ D * p` when `f.totalDegree ≤ D` and `0 < p`.
* `CslibFrontier.Circuits.Arithmetic.HittingSet.exists_ksModMap_ne_zero`: given `M` nonzero
  `n`-variate polynomials of total degree at most `D` and support size at most `S`, there exists
  `1 ≤ p ≤ 2 * (Nat.log 2 (D + 1) + 1) * n * M * S + 6` keeping all `M` images nonzero.
-/

public section

namespace CslibFrontier.Circuits.Arithmetic.HittingSet

open Finset MvPolynomial

/-- The modular univariate specialization map `F[x_0, ..., x_{n-1}] → F[u]` sending
`x_i ↦ u ^ ((D + 1) ^ i mod p)`. -/
noncomputable def ksModMap (F : Type*) [CommSemiring F] (n D p : ℕ) :
    MvPolynomial (Fin n) F →ₐ[F] Polynomial F :=
  aeval fun i : Fin n ↦ Polynomial.X ^ ((D + 1) ^ (i : ℕ) % p)

/-- Image of a variable under `ksModMap`. -/
theorem ksModMap_X (F : Type*) [CommSemiring F] (n D p : ℕ) (i : Fin n) :
    ksModMap F n D p (X i) = Polynomial.X ^ ((D + 1) ^ (i : ℕ) % p) :=
  aeval_X _ i

/-- Image of a constant under `ksModMap`. -/
theorem ksModMap_C (F : Type*) [CommSemiring F] (n D p : ℕ) (c : F) :
    ksModMap F n D p (C c) = Polynomial.C c := by
  simp [ksModMap]

/-- Degree bound for the modular univariate map: if `f.totalDegree ≤ D` and `0 < p`, then
`(ksModMap F n D p f).natDegree ≤ D * p`. -/
theorem natDegree_ksModMap_le {F : Type*} [CommSemiring F] {n D p : ℕ}
    (hp : 0 < p) {f : MvPolynomial (Fin n) F} (hd : f.totalDegree ≤ D) :
    (ksModMap F n D p f).natDegree ≤ D * p := by
  refine (MvPolynomial.natDegree_aeval_le_mul (k := p) (fun i ↦ ?_) f).trans
    (Nat.mul_le_mul_right p hd)
  exact (Polynomial.natDegree_X_pow_le _).trans (le_of_lt (Nat.mod_lt _ hp))

/-- Simultaneous nonvanishing under the modular univariate specialization map: given `M` nonzero
polynomials in `F[x_0, ..., x_{n-1}]` of total degree at most `D` and support size at most `S`,
there exists a modulus `1 ≤ p ≤ 2 * (Nat.log 2 (D + 1) + 1) * n * M * S + 6` keeping all `M`
univariate images nonzero. -/
theorem exists_ksModMap_ne_zero {F : Type*} [CommRing F]
    {n M D S : ℕ} (f : Fin M → MvPolynomial (Fin n) F)
    (hne : ∀ j, f j ≠ 0) (hd : ∀ j, (f j).totalDegree ≤ D)
    (hs : ∀ j, (f j).support.card ≤ S) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ 2 * (Nat.log 2 (D + 1) + 1) * n * M * S + 6 ∧
      ∀ j : Fin M, ksModMap F n D p (f j) ≠ 0 := by
  classical
  set B := D + 1
  have hB_pos : 0 < B := Nat.succ_pos D
  let enc : (Fin n →₀ ℕ) → ℕ := fun α ↦ ∑ i : Fin n, α i * B ^ (i : ℕ)
  have henc_inj : ∀ α β : Fin n →₀ ℕ,
      (∀ i, α i < B) → (∀ i, β i < B) → enc α = enc β → α = β := by
    have hgen : ∀ (k : ℕ) (a b : Fin k → ℕ),
        (∀ i, a i < B) → (∀ i, b i < B) →
        ∑ i : Fin k, a i * B ^ (i : ℕ) = ∑ i : Fin k, b i * B ^ (i : ℕ) → a = b := by
      intro k
      induction k with
      | zero => intro a b _ _ _; exact Subsingleton.elim a b
      | succ k ih =>
        intro a b ha hb hsum
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
        simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc,
          ← Finset.sum_mul] at hsum
        have hmod : a 0 = b 0 := by
          have h1 := congrArg (· % B) hsum
          simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ha 0),
            Nat.mod_eq_of_lt (hb 0)] at h1
          exact h1
        have hdiv : ∑ i : Fin k, a i.succ * B ^ (i : ℕ) =
            ∑ i : Fin k, b i.succ * B ^ (i : ℕ) := by
          have h1 : (∑ i : Fin k, a i.succ * B ^ (i : ℕ)) * B =
              (∑ i : Fin k, b i.succ * B ^ (i : ℕ)) * B := by omega
          exact Nat.eq_of_mul_eq_mul_right hB_pos h1
        have htail := ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)
          (fun i ↦ ha i.succ) (fun i ↦ hb i.succ) hdiv
        ext i
        cases i using Fin.cases with
        | zero => exact hmod
        | succ j => exact congrFun htail j
    intro α β hα hβ heq
    have hfun := hgen n (fun i ↦ α i) (fun i ↦ β i) hα hβ heq
    ext i
    exact congrFun hfun i
  have henc_lt : ∀ α : Fin n →₀ ℕ, (∀ i, α i < B) → enc α < B ^ n := by
    have hgen : ∀ (k : ℕ) (a : Fin k → ℕ), (∀ i, a i < B) →
        ∑ i : Fin k, a i * B ^ (i : ℕ) < B ^ k := by
      intro k
      induction k with
      | zero => intro a _; simp
      | succ k ih =>
        intro a ha
        rw [Fin.sum_univ_succ, pow_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc,
          ← Finset.sum_mul]
        have htail := ih (fun i ↦ a i.succ) (fun i ↦ ha i.succ)
        have h0 := ha 0
        have h1 : (∑ i : Fin k, a i.succ * B ^ (i : ℕ)) + 1 ≤ B ^ k := htail
        calc a 0 + (∑ i : Fin k, a i.succ * B ^ (i : ℕ)) * B
            < B + (∑ i : Fin k, a i.succ * B ^ (i : ℕ)) * B := Nat.add_lt_add_right h0 _
          _ = ((∑ i : Fin k, a i.succ * B ^ (i : ℕ)) + 1) * B := by ring
          _ ≤ B ^ k * B := Nat.mul_le_mul_right B h1
    intro α hα
    exact hgen n (fun i ↦ α i) hα
  have hsupp_ne : ∀ j, (f j).support.Nonempty := fun j ↦ by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]; exact hne j
  choose α₀ hα₀ using hsupp_ne
  have hcoord_lt : ∀ j (β : Fin n →₀ ℕ), β ∈ (f j).support → ∀ i, β i < B := by
    intro j β hβ i
    have hle : β i ≤ (f j).totalDegree := by
      have h1 : β i ≤ β.sum (fun _ e ↦ e) := by
        rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
        exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      exact h1.trans (le_totalDegree hβ)
    have := hd j
    omega
  let N : ℕ := ∏ j : Fin M, ∏ β ∈ (f j).support.erase (α₀ j),
    (if enc (α₀ j) ≤ enc β then enc β - enc (α₀ j) else enc (α₀ j) - enc β)
  have hN_pos : 0 < N := by
    refine Finset.prod_pos fun j _ ↦ Finset.prod_pos fun β hβ ↦ ?_
    have hne_β : β ≠ α₀ j := (Finset.mem_erase.mp hβ).1
    have hmem_β : β ∈ (f j).support := (Finset.mem_erase.mp hβ).2
    have hne_enc : enc (α₀ j) ≠ enc β := fun h ↦ hne_β
      (henc_inj (α₀ j) β (hcoord_lt j _ (hα₀ j)) (hcoord_lt j _ hmem_β) h).symm
    split_ifs <;> omega
  set K := (Nat.log 2 B + 1) * n * M * S
  have hN_le : N ≤ 2 ^ K := by
    have hB_lt : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self one_lt_two B
    have hfactor_le : ∀ j (β : Fin n →₀ ℕ), β ∈ (f j).support.erase (α₀ j) →
        (if enc (α₀ j) ≤ enc β then enc β - enc (α₀ j) else enc (α₀ j) - enc β) ≤
        2 ^ ((Nat.log 2 B + 1) * n) := by
      intro j β hβ
      have h1 : enc (α₀ j) < B ^ n := henc_lt _ (hcoord_lt j _ (hα₀ j))
      have h2 : enc β < B ^ n := henc_lt _ (hcoord_lt j _ (Finset.mem_erase.mp hβ).2)
      have h3 : B ^ n ≤ 2 ^ ((Nat.log 2 B + 1) * n) := by
        rw [pow_mul]
        exact Nat.pow_le_pow_left hB_lt.le n
      split_ifs <;> omega
    have hinner : ∀ j : Fin M,
        (∏ β ∈ (f j).support.erase (α₀ j),
          (if enc (α₀ j) ≤ enc β then enc β - enc (α₀ j) else enc (α₀ j) - enc β)) ≤
        (2 ^ ((Nat.log 2 B + 1) * n)) ^ S := fun j ↦ by
      calc _ ≤ ∏ _β ∈ (f j).support.erase (α₀ j), 2 ^ ((Nat.log 2 B + 1) * n) :=
            Finset.prod_le_prod fun β hβ ↦ hfactor_le j β hβ
        _ = (2 ^ ((Nat.log 2 B + 1) * n)) ^ ((f j).support.erase (α₀ j)).card := by
            rw [Finset.prod_const]
        _ ≤ (2 ^ ((Nat.log 2 B + 1) * n)) ^ S :=
            Nat.pow_le_pow_right (pow_pos two_pos _)
              ((Finset.card_erase_le).trans (hs j))
    calc N ≤ ∏ _j : Fin M, (2 ^ ((Nat.log 2 B + 1) * n)) ^ S :=
          Finset.prod_le_prod fun j _ ↦ hinner j
      _ = ((2 ^ ((Nat.log 2 B + 1) * n)) ^ S) ^ M := by simp
      _ = 2 ^ K := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          simp only [K]; ring
  set P := 2 * K + 6
  have hex_p : ∃ p ∈ Finset.Icc 1 P, ¬ p ∣ N := by
    by_contra hall
    push Not at hall
    have hdvd : Nat.lcmUpto P ∣ N := Finset.lcm_dvd hall
    have hle_N : Nat.lcmUpto P ≤ N := Nat.le_of_dvd hN_pos hdvd
    have hcheb : 2 ^ P ≤ (P + 1) * Nat.lcmUpto P := Chebyshev.two_pow_le_mul_lcmUpto P
    have hsmall : P + 1 < 2 ^ (K + 6) := by
      have hlin : ∀ m : ℕ, 2 * m + 7 < 2 ^ (m + 6) := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih =>
          rw [show m + 1 + 6 = (m + 6) + 1 by omega, pow_succ]
          omega
      exact hlin K
    have hlt : (P + 1) * N < 2 ^ P := by
      calc (P + 1) * N ≤ (P + 1) * 2 ^ K := Nat.mul_le_mul_left _ hN_le
        _ < 2 ^ (K + 6) * 2 ^ K := Nat.mul_lt_mul_of_pos_right hsmall (pow_pos two_pos K)
        _ = 2 ^ P := by rw [← pow_add]; congr 1; omega
    have hge : 2 ^ P ≤ (P + 1) * N := hcheb.trans (Nat.mul_le_mul_left _ hle_N)
    omega
  obtain ⟨p, hpIcc, hndvd⟩ := hex_p
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp1, hpP⟩
  refine ⟨p, hp1, by simpa only [P, K, mul_assoc] using hpP, fun j ↦ ?_⟩
  let degMod : (Fin n →₀ ℕ) → ℕ := fun α ↦ ∑ i : Fin n, α i * (B ^ (i : ℕ) % p)
  have hmod_eq : ∀ α : Fin n →₀ ℕ, degMod α % p = enc α % p := by
    intro α
    have hcong : ∀ s : Finset (Fin n),
        (∑ i ∈ s, α i * (B ^ (i : ℕ) % p)) ≡ (∑ i ∈ s, α i * B ^ (i : ℕ)) [MOD p] := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [Nat.ModEq]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        refine Nat.ModEq.add ?_ ih
        exact Nat.ModEq.mul_left _ (Nat.mod_modEq _ p)
    exact hcong Finset.univ
  have hcoeff_eq : (ksModMap F n D p (f j)).coeff (degMod (α₀ j)) = (f j).coeff (α₀ j) := by
    conv_lhs => enter [1]; rw [(f j).as_sum, map_sum]
    rw [Polynomial.finsetSum_coeff]
    have hmon : ∀ β : Fin n →₀ ℕ,
        ksModMap F n D p (monomial β ((f j).coeff β)) =
          Polynomial.C ((f j).coeff β) * Polynomial.X ^ (degMod β) := fun β ↦ by
      rw [ksModMap, aeval_monomial, Polynomial.algebraMap_eq]
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [degMod, B, ← pow_mul, mul_comm (β _), Finset.prod_pow_eq_pow_sum]
    simp_rw [hmon, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (α₀ j)]
    · simp
    · intro β hβ hne_β
      have hne_deg : degMod (α₀ j) ≠ degMod β := by
        intro heq
        have hcong : enc (α₀ j) % p = enc β % p := by
          rw [← hmod_eq (α₀ j), ← hmod_eq β, heq]
        have hdvd_diff : p ∣ (if enc (α₀ j) ≤ enc β then enc β - enc (α₀ j)
            else enc (α₀ j) - enc β) := by
          split_ifs with hle
          · exact (Nat.modEq_iff_dvd' hle).mp hcong
          · exact (Nat.modEq_iff_dvd' (Nat.le_of_not_ge hle)).mp hcong.symm
        have hdvd_inner : (if enc (α₀ j) ≤ enc β then enc β - enc (α₀ j)
            else enc (α₀ j) - enc β) ∣
            ∏ β' ∈ (f j).support.erase (α₀ j),
              (if enc (α₀ j) ≤ enc β' then enc β' - enc (α₀ j) else enc (α₀ j) - enc β') :=
          Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne_β, hβ⟩)
        have hdvd_N : (∏ β' ∈ (f j).support.erase (α₀ j),
              (if enc (α₀ j) ≤ enc β' then enc β' - enc (α₀ j) else enc (α₀ j) - enc β')) ∣ N :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        exact hndvd ((hdvd_diff.trans hdvd_inner).trans hdvd_N)
      simp [hne_deg]
    · intro h; exact absurd (hα₀ j) h
  intro h0
  rw [h0, Polynomial.coeff_zero] at hcoeff_eq
  exact mem_support_iff.mp (hα₀ j) hcoeff_eq.symm

end CslibFrontier.Circuits.Arithmetic.HittingSet
