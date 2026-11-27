/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import CslibFrontier.Computability.RAM.Cost
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Coefficient Infinity Norm and Binary Bit Size of Integer Multivariate Polynomials

This module defines the coefficient infinity norm `coeffNormInf` and the maximum binary coefficient
bit size `maxCoeffBitSize` of integer multivariate polynomials `MvPolynomial σ ℤ`, complementing
`MvPolynomial.coeffNorm1` and `Cslib.RAM.bitLength`.

We prove support cardinality bounds in terms of total degree and variable count, sharp
submultiplicative bounds for `coeffNormInf (f * g)` via monomial support size, and additive
logarithmic bit-size bounds for binary products, finite products, and powers of multivariate
integer polynomials.

## Main definitions

* `MvPolynomial.coeffNormInf`: maximum absolute coefficient `sup_{m ∈ f.support} |f_m|`.
* `MvPolynomial.maxCoeffBitSize`: binary bit size `Cslib.RAM.bitLength (coeffNormInf f)`.

## Main results

* `MvPolynomial.card_support_le_pow_totalDegree_add_one`: `#f.support ≤ (deg f + 1) ^ |σ|`.
* `MvPolynomial.coeffNormInf_mul_le_min_card_support`: sharp bound
  `coeffNormInf (f * g) ≤ min #f.support #g.support * coeffNormInf f * coeffNormInf g`.
* `MvPolynomial.maxCoeffBitSize_mul_le`: bit-size bound
  `maxCoeffBitSize (f * g) ≤ τ₁ + τ₂ + |σ| * bitLength (min d₁ d₂)`.
* `MvPolynomial.maxCoeffBitSize_prod_fin_succ_le`,
  `MvPolynomial.maxCoeffBitSize_pow_le`: bit-size bounds for finite products and powers.
-/

public section

namespace MvPolynomial

open Cslib.RAM

section CoeffNormInf

variable {σ : Type*}

/-- The infinity norm (maximum absolute value of coefficients) of an integer multivariate
polynomial `f : MvPolynomial σ ℤ`. -/
@[expose] noncomputable def coeffNormInf (f : MvPolynomial σ ℤ) : ℕ :=
  f.support.sup fun m ↦ (f.coeff m).natAbs

@[simp]
theorem coeffNormInf_zero : coeffNormInf (0 : MvPolynomial σ ℤ) = 0 := by
  simp [coeffNormInf]

/-- Every coefficient of `f` has absolute value at most `coeffNormInf f`. -/
theorem natAbs_coeff_le_coeffNormInf (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (f.coeff m).natAbs ≤ coeffNormInf f := by
  by_cases hm : m ∈ f.support
  · exact Finset.le_sup (f := fun μ ↦ (f.coeff μ).natAbs) hm
  · rw [notMem_support_iff.mp hm]
    simp

/-- `coeffNormInf f ≤ B` if and only if every coefficient of `f` has absolute value at most `B`. -/
theorem coeffNormInf_le_iff {f : MvPolynomial σ ℤ} {B : ℕ} :
    coeffNormInf f ≤ B ↔ ∀ m : σ →₀ ℕ, (f.coeff m).natAbs ≤ B := by
  rw [coeffNormInf, Finset.sup_le_iff]
  refine ⟨fun h m ↦ ?_, fun h m _ ↦ h m⟩
  by_cases hm : m ∈ f.support
  · exact h m hm
  · rw [notMem_support_iff.mp hm]
    simp

@[simp]
theorem coeffNormInf_monomial (m : σ →₀ ℕ) (a : ℤ) :
    coeffNormInf (monomial m a) = a.natAbs := by
  classical
  refine le_antisymm (coeffNormInf_le_iff.mpr fun μ ↦ ?_) ?_
  · rw [coeff_monomial]
    split_ifs <;> simp
  · simpa using natAbs_coeff_le_coeffNormInf (monomial m a) m

theorem coeffNormInf_C (a : ℤ) : coeffNormInf (C a : MvPolynomial σ ℤ) = a.natAbs :=
  coeffNormInf_monomial 0 a

@[simp]
theorem coeffNormInf_one : coeffNormInf (1 : MvPolynomial σ ℤ) = 1 :=
  coeffNormInf_C 1

@[simp]
theorem coeffNormInf_X (i : σ) : coeffNormInf (X i : MvPolynomial σ ℤ) = 1 :=
  coeffNormInf_monomial _ 1

@[simp]
theorem coeffNormInf_neg (f : MvPolynomial σ ℤ) : coeffNormInf (-f) = coeffNormInf f := by
  refine le_antisymm
    (coeffNormInf_le_iff.mpr fun m ↦ by simpa using natAbs_coeff_le_coeffNormInf f m)
    (coeffNormInf_le_iff.mpr fun m ↦ by simpa using natAbs_coeff_le_coeffNormInf (-f) m)

/-- Triangle inequality for `coeffNormInf`. -/
theorem coeffNormInf_add_le (f g : MvPolynomial σ ℤ) :
    coeffNormInf (f + g) ≤ coeffNormInf f + coeffNormInf g :=
  coeffNormInf_le_iff.mpr fun m ↦ by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (Int.natAbs_add_le _ _).trans
      (Nat.add_le_add (natAbs_coeff_le_coeffNormInf f m) (natAbs_coeff_le_coeffNormInf g m))

/-- Finite-sum triangle inequality for `coeffNormInf`. -/
theorem coeffNormInf_sum_le {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℤ) :
    coeffNormInf (∑ i ∈ s, p i) ≤ ∑ i ∈ s, coeffNormInf (p i) :=
  Finset.le_sum_of_subadditive coeffNormInf coeffNormInf_zero.le coeffNormInf_add_le s p

/-- The infinity norm is bounded above by the `ℓ₁` coefficient norm `coeffNorm1`. -/
theorem coeffNormInf_le_coeffNorm1 (f : MvPolynomial σ ℤ) :
    coeffNormInf f ≤ coeffNorm1 f :=
  coeffNormInf_le_iff.mpr (natAbs_coeff_le_coeffNorm1 f)

/-- The `ℓ₁` coefficient norm is at most `#f.support * coeffNormInf f`. -/
theorem coeffNorm1_le_card_support_mul_coeffNormInf (f : MvPolynomial σ ℤ) :
    coeffNorm1 f ≤ f.support.card * coeffNormInf f := by
  rw [coeffNorm1]
  calc
    ∑ m ∈ f.support, (f.coeff m).natAbs ≤ ∑ _m ∈ f.support, coeffNormInf f :=
      Finset.sum_le_sum fun m _ ↦ natAbs_coeff_le_coeffNormInf f m
    _ = f.support.card * coeffNormInf f := by simp

private theorem coeffNormInf_monomial_mul_le (a : σ →₀ ℕ) (c : ℤ) (g : MvPolynomial σ ℤ) :
    coeffNormInf (monomial a c * g) ≤ c.natAbs * coeffNormInf g := by
  classical
  refine coeffNormInf_le_iff.mpr fun m ↦ ?_
  conv_lhs => rw [g.as_sum, Finset.mul_sum]
  simp_rw [monomial_mul_monomial]
  rw [coeff_sum]
  by_cases hex : ∃ b ∈ g.support, a + b = m
  · obtain ⟨b, hb, rfl⟩ := hex
    rw [Finset.sum_eq_single b]
    · rw [coeff_monomial]
      simp only [↓reduceIte, Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (natAbs_coeff_le_coeffNormInf g b)
    · intro b' _ hb'
      rw [coeff_monomial]
      split_ifs with h
      · exact False.elim (hb' (add_left_cancel h))
      · rfl
    · intro hnot
      exact False.elim (hnot hb)
  · push Not at hex
    have hzero : ∀ b ∈ g.support,
        (monomial (a + b) (c * g.coeff b)).coeff m = 0 := by
      intro b hb
      rw [coeff_monomial]
      split_ifs with h
      · exact False.elim (hex b hb h)
      · rfl
    rw [Finset.sum_eq_zero hzero]
    simp

/-- Sharp left-support bound:
`coeffNormInf (f * g) ≤ #f.support * coeffNormInf f * coeffNormInf g`. -/
theorem coeffNormInf_mul_le_card_support_left (f g : MvPolynomial σ ℤ) :
    coeffNormInf (f * g) ≤ f.support.card * coeffNormInf f * coeffNormInf g := by
  conv_lhs => rw [f.as_sum, Finset.sum_mul]
  calc
    coeffNormInf (∑ a ∈ f.support, monomial a (f.coeff a) * g)
        ≤ ∑ a ∈ f.support, coeffNormInf (monomial a (f.coeff a) * g) :=
      coeffNormInf_sum_le _ _
    _ ≤ ∑ _a ∈ f.support, coeffNormInf f * coeffNormInf g :=
      Finset.sum_le_sum fun a _ ↦
        (coeffNormInf_monomial_mul_le a (f.coeff a) g).trans
          (Nat.mul_le_mul_right _ (natAbs_coeff_le_coeffNormInf f a))
    _ = f.support.card * coeffNormInf f * coeffNormInf g := by
      simp [Nat.mul_assoc]

/-- Symmetric support bound for `coeffNormInf (f * g)` using `min #f.support #g.support`. -/
theorem coeffNormInf_mul_le_min_card_support (f g : MvPolynomial σ ℤ) :
    coeffNormInf (f * g) ≤
      min f.support.card g.support.card * coeffNormInf f * coeffNormInf g := by
  rcases le_total f.support.card g.support.card with hfg | hgf
  · rw [min_eq_left hfg]
    exact coeffNormInf_mul_le_card_support_left f g
  · rw [min_eq_right hgf, mul_comm f g, mul_right_comm (g.support.card) (coeffNormInf f)]
    exact coeffNormInf_mul_le_card_support_left g f

/-- The number of nonzero monomials of `f : MvPolynomial σ ℤ` is at most
`(f.totalDegree + 1) ^ Fintype.card σ`. -/
theorem card_support_le_pow_totalDegree_add_one [Fintype σ] (f : MvPolynomial σ ℤ) :
    f.support.card ≤ (f.totalDegree + 1) ^ Fintype.card σ := by
  classical
  let box : Finset (σ → ℕ) := Fintype.piFinset fun _ : σ ↦ Finset.range (f.totalDegree + 1)
  have hsub : f.support.image (fun m : σ →₀ ℕ ↦ (⇑m : σ → ℕ)) ⊆ box := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hmi : m i ≤ m.sum fun _ e ↦ e :=
      Finsupp.single_eval_le_sum m (g := id) rfl (fun _ ↦ Nat.zero_le _) i
    exact Nat.lt_succ_of_le (hmi.trans (le_totalDegree hm))
  have hcard_img : (f.support.image fun m : σ →₀ ℕ ↦ (⇑m : σ → ℕ)).card = f.support.card :=
    Finset.card_image_of_injective _ DFunLike.coe_injective
  have hcard_box : box.card = (f.totalDegree + 1) ^ Fintype.card σ := by
    simp [box]
  exact hcard_img ▸ hcard_box ▸ Finset.card_le_card hsub

end CoeffNormInf

section BitSize

variable {σ : Type*}

/-- The maximum binary coefficient bit size `⌊log₂ (coeffNormInf f)⌋ + 1` of an integer
multivariate polynomial `f : MvPolynomial σ ℤ` (with `0` having bit size `1`). -/
@[expose] noncomputable def maxCoeffBitSize (f : MvPolynomial σ ℤ) : ℕ :=
  bitLength (coeffNormInf f)

@[simp]
theorem maxCoeffBitSize_zero : maxCoeffBitSize (0 : MvPolynomial σ ℤ) = 1 := by
  simp [maxCoeffBitSize]

@[simp]
theorem maxCoeffBitSize_one : maxCoeffBitSize (1 : MvPolynomial σ ℤ) = 1 := by
  simp [maxCoeffBitSize, bitLength]

/-- Every polynomial has bit size at least `1`. -/
theorem one_le_maxCoeffBitSize (f : MvPolynomial σ ℤ) : 1 ≤ maxCoeffBitSize f :=
  one_le_bitLength _

/-- Every individual coefficient of `f` has binary bit length at most `maxCoeffBitSize f`. -/
theorem bitLength_coeff_le_maxCoeffBitSize (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    bitLength (f.coeff m).natAbs ≤ maxCoeffBitSize f :=
  bitLength_mono (natAbs_coeff_le_coeffNormInf f m)

/-- `coeffNormInf f < 2 ^ τ` whenever `maxCoeffBitSize f ≤ τ`. -/
theorem coeffNormInf_lt_two_pow_of_maxCoeffBitSize_le {f : MvPolynomial σ ℤ} {τ : ℕ}
    (hτ : maxCoeffBitSize f ≤ τ) : coeffNormInf f < 2 ^ τ := by
  have hne : τ ≠ 0 := Nat.ne_of_gt ((one_le_maxCoeffBitSize f).trans hτ)
  exact (bitLength_le_iff hne).mp hτ

/-- **Sharp Product Bit-Size Bound**: for `f₁, f₂ : MvPolynomial σ ℤ` in `ν = Fintype.card σ`
variables of total degrees at most `d₁, d₂` and bit sizes at most `τ₁, τ₂`, `f₁ * f₂` has total
degree at most `d₁ + d₂` and bit size at most `τ₁ + τ₂ + ν * bitLength (min d₁ d₂)`. -/
theorem maxCoeffBitSize_mul_le [Fintype σ] {f₁ f₂ : MvPolynomial σ ℤ} {d₁ d₂ τ₁ τ₂ : ℕ}
    (hd₁ : f₁.totalDegree ≤ d₁) (hd₂ : f₂.totalDegree ≤ d₂)
    (hτ₁ : maxCoeffBitSize f₁ ≤ τ₁) (hτ₂ : maxCoeffBitSize f₂ ≤ τ₂) :
    (f₁ * f₂).totalDegree ≤ d₁ + d₂ ∧
      maxCoeffBitSize (f₁ * f₂) ≤ τ₁ + τ₂ + Fintype.card σ * bitLength (min d₁ d₂) := by
  refine ⟨(totalDegree_mul f₁ f₂).trans (Nat.add_le_add hd₁ hd₂), ?_⟩
  have hτ₁_pos : 1 ≤ τ₁ := (one_le_maxCoeffBitSize f₁).trans hτ₁
  have hne : τ₁ + τ₂ + Fintype.card σ * bitLength (min d₁ d₂) ≠ 0 := by omega
  rw [maxCoeffBitSize, bitLength_le_iff hne]
  have hc₁ : coeffNormInf f₁ < 2 ^ τ₁ := coeffNormInf_lt_two_pow_of_maxCoeffBitSize_le hτ₁
  have hc₂ : coeffNormInf f₂ < 2 ^ τ₂ := coeffNormInf_lt_two_pow_of_maxCoeffBitSize_le hτ₂
  have hs₁ : f₁.support.card ≤ (d₁ + 1) ^ Fintype.card σ :=
    (card_support_le_pow_totalDegree_add_one f₁).trans (Nat.pow_le_pow_left (by omega) _)
  have hs₂ : f₂.support.card ≤ (d₂ + 1) ^ Fintype.card σ :=
    (card_support_le_pow_totalDegree_add_one f₂).trans (Nat.pow_le_pow_left (by omega) _)
  have hmin_supp : min f₁.support.card f₂.support.card ≤ (min d₁ d₂ + 1) ^ Fintype.card σ := by
    rcases le_total d₁ d₂ with hle | hge
    · rw [min_eq_left hle]
      exact (min_le_left _ _).trans hs₁
    · rw [min_eq_right hge]
      exact (min_le_right _ _).trans hs₂
  have hdeg_pow : (min d₁ d₂ + 1) ^ Fintype.card σ ≤
      2 ^ (Fintype.card σ * bitLength (min d₁ d₂)) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (lt_two_pow_bitLength (min d₁ d₂)) _
  have hprod_lt : coeffNormInf f₁ * coeffNormInf f₂ < 2 ^ (τ₁ + τ₂) := by
    rw [pow_add]
    exact mul_lt_mul'' hc₁ hc₂ (Nat.zero_le _) (Nat.zero_le _)
  have hpos_pow : 0 < 2 ^ (Fintype.card σ * bitLength (min d₁ d₂)) := Nat.two_pow_pos _
  calc
    coeffNormInf (f₁ * f₂)
        ≤ min f₁.support.card f₂.support.card * (coeffNormInf f₁ * coeffNormInf f₂) := by
      simpa only [Nat.mul_assoc] using coeffNormInf_mul_le_min_card_support f₁ f₂
    _ ≤ 2 ^ (Fintype.card σ * bitLength (min d₁ d₂)) * (coeffNormInf f₁ * coeffNormInf f₂) :=
      Nat.mul_le_mul_right _ (hmin_supp.trans hdeg_pow)
    _ < 2 ^ (Fintype.card σ * bitLength (min d₁ d₂)) * 2 ^ (τ₁ + τ₂) :=
      (Nat.mul_lt_mul_left hpos_pow).mpr hprod_lt
    _ = 2 ^ (τ₁ + τ₂ + Fintype.card σ * bitLength (min d₁ d₂)) := by
      rw [← pow_add, add_comm]

/-- **Finite Product Bit-Size Bound**: for `m + 1` polynomials `f : Fin (m + 1) → MvPolynomial σ ℤ`
of total degrees `≤ d i` and bit sizes `≤ τ i`, `∏ i, f i` has total degree `≤ ∑ i, d i` and bit
size `≤ ∑ i, τ i + Fintype.card σ * ∑ j : Fin m, bitLength (d j.castSucc)`. -/
theorem maxCoeffBitSize_prod_fin_succ_le [Fintype σ] :
    ∀ {m : ℕ} {f : Fin (m + 1) → MvPolynomial σ ℤ} {d τ : Fin (m + 1) → ℕ},
      (∀ i, (f i).totalDegree ≤ d i) →
      (∀ i, maxCoeffBitSize (f i) ≤ τ i) →
      (∏ i, f i).totalDegree ≤ ∑ i, d i ∧
        maxCoeffBitSize (∏ i, f i) ≤
          (∑ i, τ i) + Fintype.card σ * ∑ j : Fin m, bitLength (d j.castSucc)
  | 0, f, d, τ, hd, hτ => by
    simpa using ⟨hd 0, hτ 0⟩
  | m + 1, f, d, τ, hd, hτ => by
    obtain ⟨hdeg_tail, hbit_tail⟩ := maxCoeffBitSize_prod_fin_succ_le
      (f := fun j : Fin (m + 1) ↦ f j.succ)
      (d := fun j : Fin (m + 1) ↦ d j.succ)
      (τ := fun j : Fin (m + 1) ↦ τ j.succ)
      (fun j ↦ hd j.succ) (fun j ↦ hτ j.succ)
    obtain ⟨hdeg, hbit⟩ := maxCoeffBitSize_mul_le (hd 0) hdeg_tail (hτ 0) hbit_tail
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ d, Fin.sum_univ_succ τ,
      Fin.sum_univ_succ (fun j : Fin (m + 1) ↦ bitLength (d j.castSucc))]
    refine ⟨hdeg, hbit.trans ?_⟩
    have hmin : bitLength (min (d 0) (∑ x : Fin (m + 1), d x.succ)) ≤ bitLength (d 0) :=
      bitLength_mono (min_le_left _ _)
    have h0 : ((0 : Fin (m + 1)).castSucc : Fin (m + 2)) = 0 := Fin.ext rfl
    have hfin : ∀ x : Fin m,
        ((x.castSucc : Fin (m + 1)).succ : Fin (m + 2)) = (x.succ : Fin (m + 1)).castSucc :=
      fun _ ↦ Fin.ext rfl
    rw [h0]
    simp_rw [hfin]
    have hmul := Nat.mul_le_mul_left (Fintype.card σ) hmin
    have hdistrib : Fintype.card σ *
        (bitLength (d 0) + ∑ x : Fin m, bitLength (d x.succ.castSucc)) =
        Fintype.card σ * bitLength (d 0) +
          Fintype.card σ * ∑ x : Fin m, bitLength (d x.succ.castSucc) :=
      Nat.mul_add _ _ _
    omega

/-- **Power Bit-Size Bound**: for `1 ≤ m` and `f : MvPolynomial σ ℤ` with `f.totalDegree ≤ d` and
`maxCoeffBitSize f ≤ τ`, `f ^ m` has total degree `≤ m * d` and bit size
`≤ m * τ + (m - 1) * Fintype.card σ * bitLength d`. -/
theorem maxCoeffBitSize_pow_le [Fintype σ] {f : MvPolynomial σ ℤ} {d τ m : ℕ}
    (hm : 1 ≤ m) (hd : f.totalDegree ≤ d) (hτ : maxCoeffBitSize f ≤ τ) :
    (f ^ m).totalDegree ≤ m * d ∧
      maxCoeffBitSize (f ^ m) ≤ m * τ + (m - 1) * Fintype.card σ * bitLength d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨hdeg, hbit⟩ := maxCoeffBitSize_prod_fin_succ_le
    (m := k) (f := fun _ ↦ f) (d := fun _ ↦ d) (τ := fun _ ↦ τ)
    (fun _ ↦ hd) (fun _ ↦ hτ)
  simp only [Finset.prod_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hdeg hbit
  rw [add_comm 1 k]
  exact ⟨by simpa [smul_eq_mul] using hdeg,
    by simpa [smul_eq_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbit⟩

end BitSize

end MvPolynomial
