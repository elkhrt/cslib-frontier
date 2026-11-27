/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Paley Type I and Type II Hadamard Matrices over Finite Fields

For a finite field $\mathbb{F}_q$ of odd cardinality $q$, Paley constructed two infinite
families of Hadamard matrices using the quadratic character $\chi : \mathbb{F}_q \to \{-1, 0, 1\}$:

* **Paley Type I** ($q \equiv 3 \pmod{4}$): a bordered Hadamard matrix of order $q + 1$ indexed by
  `Option F`, with `1` along the `none` border, `-1` on the interior diagonal, and $\chi(x - y)$
  at distinct interior positions $(x, y)$.
* **Paley Type II** ($q \equiv 1 \pmod{4}$): a symmetric Hadamard matrix of order $2(q + 1)$
  indexed by `Option F × Fin 2`, built from the symmetric Paley conference matrix $S$ of order
  $q + 1$ (satisfying $S^2 = q I_{q + 1}$) as $S \otimes A_2 + I_{q + 1} \otimes B_2$ with
  $A_2 = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ and
  $B_2 = \begin{pmatrix} 1 & -1 \\ -1 & -1 \end{pmatrix}$.

This module constructs both families over arbitrary finite fields, proves the Jacobsthal character
sum identity $\sum_{x \in \mathbb{F}_q} \chi(x)\chi(x + a) = -1$ ($a \neq 0$), establishes
`Matrix.IsHadamard` for both constructions and their integer-cast images in any `*`-ring, and
proves congruence sharpness on `ZMod 5` and `ZMod 3`.

## Main definitions

* `CslibFrontier.Matrix.paleyTypeIBorderMatrix`: bordered Paley Type I integer matrix on `Option F`.
* `CslibFrontier.Matrix.paleyConferenceMatrix`: bordered Paley conference matrix on `Option F`.
* `CslibFrontier.Matrix.paleyTypeIIBorderMatrix`: Paley Type II integer matrix on
  `Option F × Fin 2`.

## Main results

* `CslibFrontier.Matrix.isHadamard_map_intCast`: casting an integer Hadamard matrix into any
  `*`-ring preserves `Matrix.IsHadamard`.
* `CslibFrontier.Matrix.quadraticChar_jacobsthal_sum`: the Jacobsthal character sum over any finite
  field of characteristic different from `2` equals `-1` for nonzero shifts.
* `CslibFrontier.Matrix.isHadamard_paleyTypeIBorderMatrix`: `paleyTypeIBorderMatrix F` is a Hadamard
  matrix whenever `Fintype.card F % 4 = 3`.
* `CslibFrontier.Matrix.paleyConferenceMatrix_transpose`,
  `CslibFrontier.Matrix.paleyConferenceMatrix_mul_self`: for `Fintype.card F % 4 = 1`, the Paley
  conference matrix is symmetric and satisfies $S^2 = q I$.
* `CslibFrontier.Matrix.isHadamard_paleyTypeIIBorderMatrix`,
  `CslibFrontier.Matrix.paleyTypeIIBorderMatrix_transpose`: `paleyTypeIIBorderMatrix F` is a
  symmetric Hadamard matrix whenever `Fintype.card F % 4 = 1`.
* `CslibFrontier.Matrix.not_isHadamard_paleyTypeIBorderMatrix_zmod5`,
  `CslibFrontier.Matrix.not_isHadamard_paleyTypeIIBorderMatrix_zmod3`: sharpness of the modulo-`4`
  congruence hypotheses.
-/

public section

namespace CslibFrontier.Matrix

open scoped BigOperators Kronecker _root_.Matrix

/-! ### 1. Integer Hadamard base change and finite-field Jacobsthal sums -/

section CharacterSums

/-- Casting an integer Hadamard matrix via `Int.castRingHom R` yields a Hadamard matrix over any
`*`-ring `R`. -/
theorem isHadamard_map_intCast {n R : Type*} [Fintype n] [DecidableEq n] [Ring R] [StarRing R]
    {H : Matrix n n ℤ} (hH : H.IsHadamard) : (H.map (Int.castRingHom R)).IsHadamard := by
  have hconj : _root_.Matrix.conjTranspose (H.map (Int.castRingHom R)) =
      (_root_.Matrix.conjTranspose H).map (Int.castRingHom R) := by
    ext i j
    simp [star_intCast]
  refine ⟨fun i j ↦ ?_, ?_, ?_⟩
  · rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j) with h1 | hm1
    · simp [h1]
    · simp only [_root_.Matrix.map_apply, hm1, eq_intCast, Int.cast_neg, Int.cast_one]
      exact Unitary.mem_iff.mpr ⟨by simp, by simp⟩
  · rw [hconj, ← _root_.Matrix.map_mul, hH.mul_conjTranspose]
    ext i j
    simp only [_root_.Matrix.map_apply, _root_.Matrix.smul_apply, _root_.Matrix.one_apply,
      smul_eq_mul, map_mul, map_natCast]
    by_cases hij : i = j <;> simp [hij]
  · rw [hconj, ← _root_.Matrix.map_mul, hH.conjTranspose_mul]
    ext i j
    simp only [_root_.Matrix.map_apply, _root_.Matrix.smul_apply, _root_.Matrix.one_apply,
      smul_eq_mul, map_mul, map_natCast]
    by_cases hij : i = j <;> simp [hij]

private lemma ringChar_ne_two_of_card_odd {F : Type*} [Field F] [Fintype F]
    (hodd : Fintype.card F % 2 = 1) : ringChar F ≠ 2 := by
  intro h2
  have htwo : (2 : F) = 0 := by
    simpa [h2] using (ringChar.Nat.cast_ringChar (R := F))
  have hord : addOrderOf (1 : F) = 2 := by
    refine addOrderOf_eq_prime (p := 2) ?_ one_ne_zero
    simpa [two_nsmul] using htwo
  have hdvd : 2 ∣ Fintype.card F := hord ▸ addOrderOf_dvd_card (x := (1 : F))
  omega

/-- **Jacobsthal character sum**: over any finite field `F` with `ringChar F ≠ 2`, for every
nonzero shift `a : F`,
$$\sum_{x \in F} \chi(x)\chi(x + a) = -1.$$ -/
theorem quadraticChar_jacobsthal_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ x : F, quadraticChar F x * quadraticChar F (x + a) = -1 := by
  classical
  have hterm : ∀ x : F,
      quadraticChar F x * quadraticChar F (x + a) =
        quadraticChar F (1 + a * x⁻¹) - if x = 0 then 1 else 0 := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · have hxa : x + a = x * (1 + a * x⁻¹) := by
        calc x + a = x + a * (x * x⁻¹) := by rw [mul_inv_cancel₀ hx, mul_one]
          _ = x * (1 + a * x⁻¹) := by ring
      rw [hxa, map_mul, ← mul_assoc, ← pow_two, quadraticChar_sq_one hx, one_mul,
        ite_eq_right hx, sub_zero]
  simp_rw [hterm, Finset.sum_sub_distrib]
  let e : F ≃ F :=
    (Equiv.inv F).trans ((Equiv.mulLeft₀ a ha).trans (Equiv.addLeft (1 : F)))
  have hsum_e : ∑ x : F, quadraticChar F (1 + a * x⁻¹) = 0 := by
    have he : ∀ x : F, quadraticChar F (1 + a * x⁻¹) = quadraticChar F (e x) := fun x ↦ by
      simp [e]
    simp_rw [he]
    rw [Equiv.sum_comp e, quadraticChar_sum_zero hchar]
  rw [hsum_e, Finset.sum_ite_eq' Finset.univ (0 : F)]
  simp

private lemma sum_quadraticChar_sub_eq_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (x : F) :
    ∑ z : F, quadraticChar F (x - z) = 0 :=
  (Equiv.sum_comp (Equiv.subLeft x) (quadraticChar F)).trans (quadraticChar_sum_zero hchar)

private lemma sum_quadraticChar_sub_mul_eq_neg_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) {x y : F} (hxy : x ≠ y) :
    ∑ z : F, quadraticChar F (x - z) * quadraticChar F (y - z) = -1 := by
  have ha : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hterm : ∀ z : F,
      quadraticChar F (x - z) * quadraticChar F (y - z) =
        quadraticChar F (x - z) * quadraticChar F ((x - z) + (y - x)) := fun z ↦ by
    congr 2; ring
  simp_rw [hterm]
  exact (Equiv.sum_comp (Equiv.subLeft x)
      (fun u : F ↦ quadraticChar F u * quadraticChar F (u + (y - x)))).trans
    (quadraticChar_jacobsthal_sum hchar ha)

private lemma sum_quadraticChar_sub_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    ∑ z : F, quadraticChar F (x - z) * quadraticChar F (x - z) = (Fintype.card F : ℤ) - 1 := by
  classical
  have hterm : ∀ z : F,
      quadraticChar F (x - z) * quadraticChar F (x - z) = 1 - if z = x then (1 : ℤ) else 0 := by
    intro z
    by_cases hz : z = x
    · subst hz; simp
    · have hne : x - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
      rw [← pow_two, quadraticChar_sq_one hne, ite_eq_right hz, sub_zero]
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp

end CharacterSums

/-! ### 2. Paley Type I Hadamard matrices (`q ≡ 3 mod 4`) -/

section PaleyTypeI

/-- **Bordered Paley Type I matrix** over a field `F`: indexed by `Option F`, with `1` along the
`none` bordering row and column, `-1` on the interior diagonal `(some x, some x)`, and
`quadraticCharFun F (x - y)` at distinct interior positions `(some x, some y)`. When `F` is finite
with `Fintype.card F % 4 = 3`, this is a Hadamard matrix of order `Fintype.card F + 1`. -/
noncomputable def paleyTypeIBorderMatrix (F : Type*) [Field F] :
    Matrix (Option F) (Option F) ℤ
  | none, _ => 1
  | some _, none => 1
  | some x, some y =>
      @ite _ (x = y) (Classical.propDecidable _) (-1)
        (@quadraticCharFun F _ (Classical.decEq F) (Classical.decPred _) (x - y))

@[simp]
theorem paleyTypeIBorderMatrix_none_left (F : Type*) [Field F] (j : Option F) :
    paleyTypeIBorderMatrix F none j = 1 := by
  unfold paleyTypeIBorderMatrix; rfl

@[simp]
theorem paleyTypeIBorderMatrix_none_right (F : Type*) [Field F] (i : Option F) :
    paleyTypeIBorderMatrix F i none = 1 := by
  cases i <;> (unfold paleyTypeIBorderMatrix; rfl)

@[simp]
theorem paleyTypeIBorderMatrix_some_self (F : Type*) [Field F] (x : F) :
    paleyTypeIBorderMatrix F (some x) (some x) = -1 := by
  simp [paleyTypeIBorderMatrix]

/-- Off-diagonal interior entry of `paleyTypeIBorderMatrix F`. -/
theorem paleyTypeIBorderMatrix_some_of_ne (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    {x y : F} (hxy : x ≠ y) :
    paleyTypeIBorderMatrix F (some x) (some y) = quadraticChar F (x - y) := by
  unfold paleyTypeIBorderMatrix
  dsimp only
  rw [ite_eq_right hxy, quadraticChar_apply]
  unfold quadraticCharFun
  split_ifs <;> rfl

/-- Interior entry formula for `paleyTypeIBorderMatrix F` using any `DecidableEq F`. -/
theorem paleyTypeIBorderMatrix_some_some (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (x y : F) :
    paleyTypeIBorderMatrix F (some x) (some y) =
      if x = y then -1 else quadraticChar F (x - y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [ite_eq_right hxy, paleyTypeIBorderMatrix_some_of_ne F hxy]

/-- Every entry of `paleyTypeIBorderMatrix F` is `1` or `-1`. -/
theorem paleyTypeIBorderMatrix_entry_eq_one_or_neg_one (F : Type*) [Field F]
    (i j : Option F) :
    paleyTypeIBorderMatrix F i j = 1 ∨ paleyTypeIBorderMatrix F i j = -1 := by
  cases i with
  | none => exact Or.inl (by simp)
  | some x =>
    cases j with
    | none => exact Or.inl (by simp)
    | some y =>
      unfold paleyTypeIBorderMatrix quadraticCharFun
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [hxy, ite_false, sub_ne_zero.mpr hxy]
        split_ifs <;> simp

/-- **Paley's Theorem (Type I)**: for every finite field `F` with `Fintype.card F % 4 = 3`,
`paleyTypeIBorderMatrix F` is a Hadamard matrix of order `Fintype.card F + 1`. -/
theorem isHadamard_paleyTypeIBorderMatrix (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F % 4 = 3) : (paleyTypeIBorderMatrix F).IsHadamard := by
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_card_odd (by omega)
  have hneg1 : quadraticChar F (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_three_mod_four hF]
  have hodd_chi : ∀ a : F, quadraticChar F (-a) = -quadraticChar F a := fun a ↦ by
    rw [neg_eq_neg_one_mul, map_mul, hneg1, neg_one_mul]
  refine _root_.Matrix.IsHadamard.of_mul_conjTranspose
    (fun i j ↦ Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      (paleyTypeIBorderMatrix_entry_eq_one_or_neg_one F i j)) ?_
    (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by simp [Fintype.card_option])))
  ext i j
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.conjTranspose_apply, star_trivial,
    _root_.Matrix.smul_apply, _root_.Matrix.one_apply, smul_eq_mul,
    Fintype.card_option, Nat.cast_add, Nat.cast_one]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, mul_one]
    have hsq : ∀ k : Option F,
        paleyTypeIBorderMatrix F i k * paleyTypeIBorderMatrix F i k = 1 := fun k ↦ by
      rcases paleyTypeIBorderMatrix_entry_eq_one_or_neg_one F i k with h | h <;> simp [h]
    simp [hsq]
  · rw [ite_eq_right hij, mul_zero, Fintype.sum_option]
    cases i with
    | none =>
      cases j with
      | none => exact absurd rfl hij
      | some y =>
        simp only [paleyTypeIBorderMatrix_none_left, paleyTypeIBorderMatrix_none_right, one_mul]
        have hterm : ∀ z : F,
            paleyTypeIBorderMatrix F (some y) (some z) =
              quadraticChar F (y - z) - if z = y then 1 else 0 := fun z ↦ by
          by_cases hzy : z = y
          · subst hzy; simp
          · rw [paleyTypeIBorderMatrix_some_of_ne F (Ne.symm hzy), ite_eq_right hzy, sub_zero]
        simp_rw [hterm, Finset.sum_sub_distrib, sum_quadraticChar_sub_eq_zero hchar y]
        simp
    | some x =>
      cases j with
      | none =>
        simp only [paleyTypeIBorderMatrix_none_left, paleyTypeIBorderMatrix_none_right, mul_one]
        have hterm : ∀ z : F,
            paleyTypeIBorderMatrix F (some x) (some z) =
              quadraticChar F (x - z) - if z = x then 1 else 0 := fun z ↦ by
          by_cases hzx : z = x
          · subst hzx; simp
          · rw [paleyTypeIBorderMatrix_some_of_ne F (Ne.symm hzx), ite_eq_right hzx, sub_zero]
        simp_rw [hterm, Finset.sum_sub_distrib, sum_quadraticChar_sub_eq_zero hchar x]
        simp
      | some y =>
        have hxy : x ≠ y := fun h ↦ hij (congrArg some h)
        simp only [paleyTypeIBorderMatrix_none_right, mul_one]
        have hterm : ∀ z : F,
            paleyTypeIBorderMatrix F (some x) (some z) *
                paleyTypeIBorderMatrix F (some y) (some z) =
              quadraticChar F (x - z) * quadraticChar F (y - z) -
                (if z = x then quadraticChar F (y - x) else 0) -
                (if z = y then quadraticChar F (x - y) else 0) := by
          intro z
          by_cases hzx : z = x
          · subst hzx
            have hyx : y ≠ z := hxy.symm
            simp [paleyTypeIBorderMatrix_some_of_ne F hyx, hxy]
          · by_cases hzy : z = y
            · subst hzy
              simp [paleyTypeIBorderMatrix_some_of_ne F hxy, hzx]
            · rw [paleyTypeIBorderMatrix_some_of_ne F (Ne.symm hzx),
                paleyTypeIBorderMatrix_some_of_ne F (Ne.symm hzy), ite_eq_right hzx,
                ite_eq_right hzy, sub_zero, sub_zero]
        simp_rw [hterm, Finset.sum_sub_distrib]
        rw [sum_quadraticChar_sub_mul_eq_neg_one hchar hxy,
          Finset.sum_ite_eq' Finset.univ x, Finset.sum_ite_eq' Finset.univ y]
        simp only [Finset.mem_univ, ite_true]
        have hskew : quadraticChar F (y - x) = -quadraticChar F (x - y) := by
          have : y - x = -(x - y) := by ring
          rw [this, hodd_chi]
        rw [hskew]
        ring

/-- **Sharpness of `Fintype.card F % 4 = 3`**: `paleyTypeIBorderMatrix (ZMod 5)` is not a Hadamard
matrix because `5 % 4 = 1`, so `χ(-1) = 1` violates skew-symmetry of the Paley core. -/
theorem not_isHadamard_paleyTypeIBorderMatrix_zmod5 :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    ¬ (paleyTypeIBorderMatrix (ZMod 5)).IsHadamard := by
  have hs01 : some (0 : ZMod 5) ≠ some (1 : ZMod 5) := by decide
  have h01 : (0 : ZMod 5) ≠ 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  dsimp only
  intro hH
  have hrow := congrFun (congrFun hH.mul_conjTranspose (some (0 : ZMod 5))) (some (1 : ZMod 5))
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.conjTranspose_apply, star_trivial,
    _root_.Matrix.smul_apply, _root_.Matrix.one_apply, smul_eq_mul, hs01, ite_false, mul_zero,
    Fintype.sum_option, paleyTypeIBorderMatrix_none_right, mul_one] at hrow
  have hchar : ringChar (ZMod 5) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; decide
  have hterm : ∀ z : ZMod 5,
      paleyTypeIBorderMatrix (ZMod 5) (some 0) (some z) *
          paleyTypeIBorderMatrix (ZMod 5) (some 1) (some z) =
        quadraticChar (ZMod 5) (0 - z) * quadraticChar (ZMod 5) (1 - z) -
          (if z = 0 then quadraticChar (ZMod 5) 1 else 0) -
          (if z = 1 then quadraticChar (ZMod 5) (-1) else 0) := by
    intro z
    by_cases hz0 : z = 0
    · subst hz0
      simp [paleyTypeIBorderMatrix_some_of_ne (ZMod 5) h01.symm, h01]
    · by_cases hz1 : z = 1
      · subst hz1
        simpa [hz0] using congrArg (- ·)
          (paleyTypeIBorderMatrix_some_of_ne (ZMod 5) h01)
      · rw [paleyTypeIBorderMatrix_some_of_ne (ZMod 5) (Ne.symm hz0),
          paleyTypeIBorderMatrix_some_of_ne (ZMod 5) (Ne.symm hz1),
          ite_eq_right hz0, ite_eq_right hz1, sub_zero, sub_zero]
  simp_rw [hterm, Finset.sum_sub_distrib] at hrow
  rw [sum_quadraticChar_sub_mul_eq_neg_one hchar h01,
    Finset.sum_ite_eq' Finset.univ (0 : ZMod 5),
    Finset.sum_ite_eq' Finset.univ (1 : ZMod 5)] at hrow
  have hneg1 : quadraticChar (ZMod 5) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card 5, ZMod.χ₄_nat_one_mod_four (by decide)]
  simp [hneg1] at hrow

end PaleyTypeI

/-! ### 3. Paley conference matrices and Paley Type II Hadamard matrices (`q ≡ 1 mod 4`) -/

section PaleyTypeII

/-- **Bordered Paley conference matrix** over a field `F`: indexed by `Option F`, with `0` at
`(none, none)` and on the interior diagonal `(some x, some x)`, `1` at `(none, some y)` and
`(some x, none)`, and `quadraticCharFun F (x - y)` at `(some x, some y)`. When `F` is finite with
`Fintype.card F % 4 = 1`, this is a symmetric conference matrix satisfying
`S * S = Fintype.card F • 1`. -/
noncomputable def paleyConferenceMatrix (F : Type*) [Field F] :
    Matrix (Option F) (Option F) ℤ
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some x, some y => @quadraticCharFun F _ (Classical.decEq F) (Classical.decPred _) (x - y)

theorem paleyConferenceMatrix_none_none (F : Type*) [Field F] :
    paleyConferenceMatrix F none none = 0 := by
  unfold paleyConferenceMatrix; rfl

@[simp]
theorem paleyConferenceMatrix_none_some (F : Type*) [Field F] (y : F) :
    paleyConferenceMatrix F none (some y) = 1 := by
  unfold paleyConferenceMatrix; rfl

@[simp]
theorem paleyConferenceMatrix_some_none (F : Type*) [Field F] (x : F) :
    paleyConferenceMatrix F (some x) none = 1 := by
  unfold paleyConferenceMatrix; rfl

@[simp]
theorem paleyConferenceMatrix_some_some (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (x y : F) :
    paleyConferenceMatrix F (some x) (some y) = quadraticChar F (x - y) := by
  unfold paleyConferenceMatrix
  dsimp only
  rw [quadraticChar_apply]
  unfold quadraticCharFun
  split_ifs <;> rfl

@[simp]
theorem paleyConferenceMatrix_diag (F : Type*) [Field F] (i : Option F) :
    paleyConferenceMatrix F i i = 0 := by
  cases i with
  | none => exact paleyConferenceMatrix_none_none F
  | some x =>
    unfold paleyConferenceMatrix quadraticCharFun
    simp

/-- Off-diagonal entries of `paleyConferenceMatrix F` belong to `{1, -1}`. -/
theorem paleyConferenceMatrix_of_ne_eq_one_or_neg_one (F : Type*) [Field F]
    {i j : Option F} (hij : i ≠ j) :
    paleyConferenceMatrix F i j = 1 ∨ paleyConferenceMatrix F i j = -1 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some _ => exact Or.inl (by simp)
  | some x =>
    cases j with
    | none => exact Or.inl (by simp)
    | some y =>
      have hxy : x ≠ y := fun h ↦ hij (congrArg some h)
      unfold paleyConferenceMatrix quadraticCharFun
      simp only [sub_ne_zero.mpr hxy, ite_false]
      split_ifs <;> simp

/-- For a finite field `F` with `Fintype.card F % 4 = 1`, `paleyConferenceMatrix F` is
symmetric. -/
theorem paleyConferenceMatrix_transpose (F : Type*) [Field F] [Fintype F]
    (hF : Fintype.card F % 4 = 1) :
    (paleyConferenceMatrix F)ᵀ = paleyConferenceMatrix F := by
  classical
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_card_odd (by omega)
  have hneg1 : quadraticChar F (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_one_mod_four hF]
  ext i j
  cases i with
  | none => cases j <;> rfl
  | some x =>
    cases j with
    | none => rfl
    | some y =>
      simp only [_root_.Matrix.transpose_apply, paleyConferenceMatrix_some_some]
      have hsub : y - x = (-1) * (x - y) := by ring
      rw [hsub, map_mul, hneg1, one_mul]

/-- For a finite field `F` of odd cardinality, the Paley conference matrix satisfies
`paleyConferenceMatrix F * (paleyConferenceMatrix F)ᵀ = Fintype.card F • 1`. -/
theorem paleyConferenceMatrix_mul_transpose (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hodd : Fintype.card F % 2 = 1) :
    paleyConferenceMatrix F * (paleyConferenceMatrix F)ᵀ =
      (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_card_odd hodd
  ext i j
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.transpose_apply, _root_.Matrix.smul_apply,
    _root_.Matrix.one_apply, smul_eq_mul, Fintype.sum_option]
  cases i with
  | none =>
    cases j with
    | none => simp
    | some y =>
      simp only [paleyConferenceMatrix_none_none, paleyConferenceMatrix_some_none, mul_one,
        zero_add, paleyConferenceMatrix_none_some, paleyConferenceMatrix_some_some, one_mul,
        reduceCtorEq, ite_false, mul_zero]
      exact sum_quadraticChar_sub_eq_zero hchar y
  | some x =>
    cases j with
    | none =>
      simp only [paleyConferenceMatrix_some_none, paleyConferenceMatrix_none_none, mul_zero,
        zero_add, paleyConferenceMatrix_some_some, paleyConferenceMatrix_none_some, mul_one,
        reduceCtorEq, ite_false]
      exact sum_quadraticChar_sub_eq_zero hchar x
    | some y =>
      simp only [paleyConferenceMatrix_some_none, mul_one, paleyConferenceMatrix_some_some,
        Option.some.injEq]
      by_cases hxy : x = y
      · subst hxy
        rw [ite_eq_left rfl, mul_one, sum_quadraticChar_sub_sq x]
        ring
      · rw [ite_eq_right hxy, mul_zero, sum_quadraticChar_sub_mul_eq_neg_one hchar hxy]
        ring

/-- For a finite field `F` with `Fintype.card F % 4 = 1`, the Paley conference matrix satisfies
`S * S = Fintype.card F • 1`. -/
theorem paleyConferenceMatrix_mul_self (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F % 4 = 1) :
    paleyConferenceMatrix F * paleyConferenceMatrix F =
      (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
  have hsym := paleyConferenceMatrix_transpose F hF
  simpa [hsym] using paleyConferenceMatrix_mul_transpose F (by omega)

private def paleyBlockA : Matrix (Fin 2) (Fin 2) ℤ :=
  _root_.Matrix.of fun a b ↦ if a = 1 ∧ b = 1 then -1 else 1

private def paleyBlockB : Matrix (Fin 2) (Fin 2) ℤ :=
  _root_.Matrix.of fun a b ↦ if a = 0 ∧ b = 0 then 1 else -1

private lemma paleyBlockA_transpose : paleyBlockAᵀ = paleyBlockA := by
  ext a b; fin_cases a <;> fin_cases b <;> decide

private lemma paleyBlockB_transpose : paleyBlockBᵀ = paleyBlockB := by
  ext a b; fin_cases a <;> fin_cases b <;> decide

private lemma paleyBlockA_sq : paleyBlockA * paleyBlockA =
    (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext a b; fin_cases a <;> fin_cases b <;> decide

private lemma paleyBlockB_sq : paleyBlockB * paleyBlockB =
    (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext a b; fin_cases a <;> fin_cases b <;> decide

private lemma paleyBlock_anticomm :
    paleyBlockA * paleyBlockB + paleyBlockB * paleyBlockA = 0 := by
  ext a b; fin_cases a <;> fin_cases b <;> decide

/-- **Bordered Paley Type II matrix** over a field `F`: indexed by `Option F × Fin 2`, replacing
each diagonal `0` of `paleyConferenceMatrix F` by the $2 \times 2$ block `[[1, -1], [-1, -1]]`
and each off-diagonal entry $s \in \{\pm 1\}$ by $s \cdot [[1, 1], [1, -1]]$. When `F` is finite
with `Fintype.card F % 4 = 1`, this is a symmetric Hadamard matrix of order
`2 * (Fintype.card F + 1)`. -/
noncomputable def paleyTypeIIBorderMatrix (F : Type*) [Field F] :
    Matrix (Option F × Fin 2) (Option F × Fin 2) ℤ :=
  _root_.Matrix.of fun p q ↦
    @ite _ (p.1 = q.1) (Classical.propDecidable _)
      (if p.2 = 0 ∧ q.2 = 0 then 1 else -1)
      (paleyConferenceMatrix F p.1 q.1 * if p.2 = 1 ∧ q.2 = 1 then -1 else 1)

/-- Entrywise formula for `paleyTypeIIBorderMatrix F` using any `DecidableEq F`. -/
theorem paleyTypeIIBorderMatrix_apply (F : Type*) [Field F] [DecidableEq F]
    (p q : Option F × Fin 2) :
    paleyTypeIIBorderMatrix F p q =
      if p.1 = q.1 then
        if p.2 = 0 ∧ q.2 = 0 then 1 else -1
      else
        paleyConferenceMatrix F p.1 q.1 * if p.2 = 1 ∧ q.2 = 1 then -1 else 1 := by
  unfold paleyTypeIIBorderMatrix
  simp only [_root_.Matrix.of_apply]
  by_cases h : p.1 = q.1 <;> simp [h]

private lemma paleyTypeIIBorderMatrix_eq_kronecker (F : Type*) [Field F] [DecidableEq F] :
    paleyTypeIIBorderMatrix F =
      paleyConferenceMatrix F ⊗ₖ paleyBlockA +
        (1 : Matrix (Option F) (Option F) ℤ) ⊗ₖ paleyBlockB := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [paleyTypeIIBorderMatrix_apply]
  by_cases hij : i = j
  · subst hij
    simp [paleyBlockB]
  · simp [hij, paleyBlockA]

/-- Every entry of `paleyTypeIIBorderMatrix F` is `1` or `-1`. -/
theorem paleyTypeIIBorderMatrix_entry_eq_one_or_neg_one (F : Type*) [Field F]
    (p q : Option F × Fin 2) :
    paleyTypeIIBorderMatrix F p q = 1 ∨ paleyTypeIIBorderMatrix F p q = -1 := by
  classical
  rw [paleyTypeIIBorderMatrix_apply]
  split_ifs with h1 h2 h3
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rcases paleyConferenceMatrix_of_ne_eq_one_or_neg_one F h1 with hs | hs <;> simp [hs]
  · rcases paleyConferenceMatrix_of_ne_eq_one_or_neg_one F h1 with hs | hs <;> simp [hs]

/-- For a finite field `F` with `Fintype.card F % 4 = 1`, `paleyTypeIIBorderMatrix F` is
symmetric. -/
theorem paleyTypeIIBorderMatrix_transpose (F : Type*) [Field F] [Fintype F]
    (hF : Fintype.card F % 4 = 1) :
    (paleyTypeIIBorderMatrix F)ᵀ = paleyTypeIIBorderMatrix F := by
  classical
  rw [paleyTypeIIBorderMatrix_eq_kronecker, _root_.Matrix.transpose_add,
    ← _root_.Matrix.kroneckerMap_transpose, ← _root_.Matrix.kroneckerMap_transpose,
    paleyConferenceMatrix_transpose F hF, paleyBlockA_transpose, _root_.Matrix.transpose_one,
    paleyBlockB_transpose]

/-- **Paley's Theorem (Type II)**: for every finite field `F` with `Fintype.card F % 4 = 1`,
`paleyTypeIIBorderMatrix F` is a Hadamard matrix of order `2 * (Fintype.card F + 1)`. -/
theorem isHadamard_paleyTypeIIBorderMatrix (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F % 4 = 1) : (paleyTypeIIBorderMatrix F).IsHadamard := by
  refine _root_.Matrix.IsHadamard.of_mul_conjTranspose
    (fun p q ↦ Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      (paleyTypeIIBorderMatrix_entry_eq_one_or_neg_one F p q)) ?_
    (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by simp [Fintype.card_option])))
  have hct : _root_.Matrix.conjTranspose (paleyTypeIIBorderMatrix F) =
      paleyTypeIIBorderMatrix F := by
    rw [_root_.Matrix.conjTranspose_eq_transpose_of_trivial, paleyTypeIIBorderMatrix_transpose F hF]
  rw [hct, paleyTypeIIBorderMatrix_eq_kronecker]
  set S := paleyConferenceMatrix F
  set I : Matrix (Option F) (Option F) ℤ := 1
  have hprod :
      (S ⊗ₖ paleyBlockA + I ⊗ₖ paleyBlockB) * (S ⊗ₖ paleyBlockA + I ⊗ₖ paleyBlockB) =
        (S * S) ⊗ₖ (paleyBlockA * paleyBlockA) +
          S ⊗ₖ (paleyBlockA * paleyBlockB + paleyBlockB * paleyBlockA) +
          I ⊗ₖ (paleyBlockB * paleyBlockB) := by
    rw [_root_.Matrix.add_mul, _root_.Matrix.mul_add, _root_.Matrix.mul_add,
      ← _root_.Matrix.mul_kronecker_mul, ← _root_.Matrix.mul_kronecker_mul,
      ← _root_.Matrix.mul_kronecker_mul, ← _root_.Matrix.mul_kronecker_mul,
      _root_.Matrix.mul_one, _root_.Matrix.one_mul, _root_.Matrix.mul_one,
      _root_.Matrix.kronecker_add]
    abel
  rw [hprod, paleyConferenceMatrix_mul_self F hF, paleyBlockA_sq, paleyBlockB_sq,
    paleyBlock_anticomm, _root_.Matrix.kronecker_zero, add_zero]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [_root_.Matrix.add_apply, _root_.Matrix.kroneckerMap_apply, _root_.Matrix.smul_apply,
    _root_.Matrix.one_apply, smul_eq_mul, Prod.mk.injEq,
    Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, I]
  by_cases hij : i = j <;> by_cases hab : a = b <;> simp [hij, hab]
  ring

/-- **Sharpness of `Fintype.card F % 4 = 1`**: `paleyTypeIIBorderMatrix (ZMod 3)` is not a Hadamard
matrix because `3 % 4 = 3`, so `S` is not symmetric on the interior and the cross term
`S * B₂ + B₂ * Sᵀ` fails to cancel. -/
theorem not_isHadamard_paleyTypeIIBorderMatrix_zmod3 :
    let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    ¬ (paleyTypeIIBorderMatrix (ZMod 3)).IsHadamard := by
  have hpq : ((some (0 : ZMod 3), (0 : Fin 2)) : Option (ZMod 3) × Fin 2) ≠ (some 1, 1) := by
    decide
  have h10_eq : (1 - 0 : ZMod 3) = 1 ^ 2 := by decide
  have h1_ne : (1 : ZMod 3) ≠ 0 := by decide
  have h02_eq : (0 - 2 : ZMod 3) = 1 - 0 := by decide
  have h12_eq : (1 - 2 : ZMod 3) = 0 - 1 := by decide
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have hn01 : (0 : ZMod 3) ≠ 1 := by decide
  have hn10 : (1 : ZMod 3) ≠ 0 := by decide
  have hn02 : (0 : ZMod 3) ≠ 2 := by decide
  have hn12 : (1 : ZMod 3) ≠ 2 := by decide
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  dsimp only
  intro hH
  have hrow := congrFun (congrFun hH.mul_conjTranspose (some (0 : ZMod 3), 0))
    (some (1 : ZMod 3), 1)
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.conjTranspose_apply, star_trivial,
    _root_.Matrix.smul_apply, _root_.Matrix.one_apply, smul_eq_mul, hpq, ite_false, mul_zero,
    Fintype.sum_prod_type, Fintype.sum_option,
    Fin.sum_univ_two, paleyTypeIIBorderMatrix_apply] at hrow
  have h10 : quadraticChar (ZMod 3) (1 - 0) = 1 := by
    rw [h10_eq, map_pow, quadraticChar_sq_one h1_ne]
  have h01 : quadraticChar (ZMod 3) (0 - 1) = -1 := by
    have hchar : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
    simpa using (quadraticChar_neg_one (F := ZMod 3) hchar).trans
      (by rw [ZMod.card 3]; exact ZMod.χ₄_nat_three_mod_four (by decide))
  have h02 : quadraticChar (ZMod 3) (0 - 2) = 1 := by
    rw [h02_eq, h10]
  have h12 : quadraticChar (ZMod 3) (1 - 2) = -1 := by
    rw [h12_eq, h01]
  simp only [Fin.isValue, paleyConferenceMatrix_some_none, paleyConferenceMatrix_some_some,
    Option.some.injEq, reduceCtorEq, ite_false, ite_true, and_self, one_ne_zero, zero_ne_one,
    and_false, false_and, mul_one, mul_neg] at hrow
  rw [huniv] at hrow
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    or_self, not_false_eq_true, hn01, hn10, hn02, hn12, ite_true, ite_false,
    h10, h01, h02, h12] at hrow
  norm_num at hrow

end PaleyTypeII

end CslibFrontier.Matrix
