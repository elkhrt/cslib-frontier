/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier Analysis and Low-Degree Influences on Discrete Product Spaces

This module develops textbook Fourier analysis, Efron–Stein / ANOVA orthogonal decompositions,
low-degree influences, coordinate minors, and coordinate regrouping on discrete product domains
`Fin r → Fin D` under standard Lean axioms:

1. Uniform expectation, inner product, and `L²` norm on `Fin r → Fin D` and
   `(Fin r → Fin D) → Fin ℓ → ℝ`.
2. Coordinate conditional expectation `coordExpect` and the basis-independent Efron–Stein / ANOVA
   orthogonal decomposition `anovaComponent`, together with equivalence to product orthonormal
   Fourier bases (`fourierCoeff`).
3. Low-degree influences `lowDegInfluence` and `lowDegVecInfluence`, their basis independence,
   Parseval degree bounds, permutation minor equivariance, convexity under averaging, and sharp
   coordinate-regrouping bounds for paired coordinates (`2`-to-`1`).

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.uniformExpect`,
  `CslibFrontier.Foundations.BooleanAnalysis.uniformInner`,
  `CslibFrontier.Foundations.BooleanAnalysis.uniformVecInner`: uniform expectations and inner
  products.
* `CslibFrontier.Foundations.BooleanAnalysis.coordExpect`,
  `CslibFrontier.Foundations.BooleanAnalysis.anovaComponent`:
  coordinate conditional expectation and orthogonal ANOVA components.
* `CslibFrontier.Foundations.BooleanAnalysis.IsOrthBasisOnFin`,
  `CslibFrontier.Foundations.BooleanAnalysis.tensorBasis`,
  `CslibFrontier.Foundations.BooleanAnalysis.fourierCoeff`: constant-`1` orthonormal bases and
  Fourier
  coefficients.
* `CslibFrontier.Foundations.BooleanAnalysis.lowDegInfluence`,
  `CslibFrontier.Foundations.BooleanAnalysis.lowDegVecInfluence`:
  basis-independent low-degree influences.
* `CslibFrontier.Foundations.BooleanAnalysis.vecMinor`,
  `CslibFrontier.Foundations.BooleanAnalysis.funMinor`:
  coordinate and function minors.
* `CslibFrontier.Foundations.BooleanAnalysis.pairIndexEquiv`,
  `CslibFrontier.Foundations.BooleanAnalysis.regroupFun2`:
  pairing of coordinates for `2`-to-`1` regrouping.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.sum_anovaComponent`,
  `CslibFrontier.Foundations.BooleanAnalysis.uniformInner_anovaComponent_eq_zero`,
  `CslibFrontier.Foundations.BooleanAnalysis.uniformL2Sq_eq_sum_anovaComponent`: orthogonal ANOVA
  decomposition.
* `CslibFrontier.Foundations.BooleanAnalysis.fourier_expansion`,
  `CslibFrontier.Foundations.BooleanAnalysis.parseval_fourier`:
  Fourier expansion and Parseval identity in any constant-`1` orthonormal basis.
* `CslibFrontier.Foundations.BooleanAnalysis.lowDegInfluence_eq_sum_fourierCoeff`: basis
  independence of
  low-degree influence.
* `CslibFrontier.Foundations.BooleanAnalysis.sum_lowDegInfluence_le`,
  `CslibFrontier.Foundations.BooleanAnalysis.lowDegInfluence_funMinor`,
  `CslibFrontier.Foundations.BooleanAnalysis.lowDegInfluence_avg_le`: Parseval degree bound, minor
  equivariance,
  and convexity.
* `CslibFrontier.Foundations.BooleanAnalysis.lowDegInfluence_regroupFun2_le`,
  `CslibFrontier.Foundations.BooleanAnalysis.lowDegVecInfluence_regroupFun2_le`: sharp coordinate
  regrouping
  bound with degree `2 * d`.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Foundations.BooleanAnalysis

/-! ### Uniform expectation and inner products -/

/-- Uniform expectation of `f : (Fin r → Fin D) → ℝ` over `[D]^r`. -/
@[expose] noncomputable def uniformExpect {D r : ℕ} (f : (Fin r → Fin D) → ℝ) : ℝ :=
  (∑ x : Fin r → Fin D, f x) / ((D ^ r : ℕ) : ℝ)

/-- Uniform `L²` inner product of `f, g : (Fin r → Fin D) → ℝ`. -/
@[expose] noncomputable def uniformInner {D r : ℕ} (f g : (Fin r → Fin D) → ℝ) : ℝ :=
  uniformExpect fun x => f x * g x

/-- Uniform squared `L²` norm of `f : (Fin r → Fin D) → ℝ`. -/
@[expose] noncomputable def uniformL2Sq {D r : ℕ} (f : (Fin r → Fin D) → ℝ) : ℝ :=
  uniformInner f f

/-- Uniform `L²` inner product of vector-valued functions `(Fin r → Fin D) → Fin ℓ → ℝ`. -/
@[expose] noncomputable def uniformVecInner {D r ℓ : ℕ}
    (f g : (Fin r → Fin D) → Fin ℓ → ℝ) : ℝ :=
  ∑ j : Fin ℓ, uniformInner (fun x => f x j) (fun x => g x j)

/-- Uniform squared `L²` norm of a vector-valued function `(Fin r → Fin D) → Fin ℓ → ℝ`. -/
@[expose] noncomputable def uniformVecL2Sq {D r ℓ : ℕ} (f : (Fin r → Fin D) → Fin ℓ → ℝ) : ℝ :=
  uniformVecInner f f

theorem uniformExpect_const {D r : ℕ} (hD : 0 < D) (c : ℝ) :
    uniformExpect (fun _ : Fin r → Fin D => c) = c := by
  have hpos : (0 : ℝ) < ((D ^ r : ℕ) : ℝ) := Nat.cast_pos.mpr (pow_pos hD r)
  simp only [uniformExpect, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_fin, Finset.prod_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hpos.ne'

theorem uniformExpect_add {D r : ℕ} (f g : (Fin r → Fin D) → ℝ) :
    uniformExpect (fun x => f x + g x) = uniformExpect f + uniformExpect g := by
  simp [uniformExpect, Finset.sum_add_distrib, add_div]

theorem uniformExpect_sub {D r : ℕ} (f g : (Fin r → Fin D) → ℝ) :
    uniformExpect (fun x => f x - g x) = uniformExpect f - uniformExpect g := by
  simp [uniformExpect, Finset.sum_sub_distrib, sub_div]

theorem uniformExpect_const_mul {D r : ℕ} (c : ℝ) (f : (Fin r → Fin D) → ℝ) :
    uniformExpect (fun x => c * f x) = c * uniformExpect f := by
  simp [uniformExpect, ← Finset.mul_sum, mul_div_assoc]

theorem uniformExpect_sum {ι : Type*} {D r : ℕ} (s : Finset ι)
    (f : ι → (Fin r → Fin D) → ℝ) :
    uniformExpect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, uniformExpect (f i) := by
  simp only [uniformExpect, Finset.sum_div]
  rw [Finset.sum_comm]

theorem uniformExpect_nonneg {D r : ℕ} {f : (Fin r → Fin D) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ uniformExpect f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem uniformExpect_mono {D r : ℕ} {f g : (Fin r → Fin D) → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformExpect f ≤ uniformExpect g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

theorem uniformExpect_le_const {D r : ℕ} (hD : 0 < D) {f : (Fin r → Fin D) → ℝ} {c : ℝ}
    (h : ∀ x, f x ≤ c) : uniformExpect f ≤ c := by
  calc
    uniformExpect f ≤ uniformExpect (fun _ => c) := uniformExpect_mono h
    _ = c := uniformExpect_const hD c

theorem uniformInner_comm {D r : ℕ} (f g : (Fin r → Fin D) → ℝ) :
    uniformInner f g = uniformInner g f := by
  simp [uniformInner, mul_comm]

theorem uniformInner_add_left {D r : ℕ} (f₁ f₂ g : (Fin r → Fin D) → ℝ) :
    uniformInner (fun x => f₁ x + f₂ x) g = uniformInner f₁ g + uniformInner f₂ g := by
  simp only [uniformInner, add_mul, uniformExpect_add]

theorem uniformInner_add_right {D r : ℕ} (f g₁ g₂ : (Fin r → Fin D) → ℝ) :
    uniformInner f (fun x => g₁ x + g₂ x) = uniformInner f g₁ + uniformInner f g₂ := by
  simp only [uniformInner, mul_add, uniformExpect_add]

theorem uniformInner_const_mul_left {D r : ℕ} (c : ℝ) (f g : (Fin r → Fin D) → ℝ) :
    uniformInner (fun x => c * f x) g = c * uniformInner f g := by
  simp only [uniformInner, mul_assoc, uniformExpect_const_mul]

theorem uniformInner_const_mul_right {D r : ℕ} (c : ℝ) (f g : (Fin r → Fin D) → ℝ) :
    uniformInner f (fun x => c * g x) = c * uniformInner f g := by
  rw [uniformInner_comm, uniformInner_const_mul_left, uniformInner_comm]

theorem uniformInner_sum_left {ι : Type*} {D r : ℕ} (s : Finset ι)
    (f : ι → (Fin r → Fin D) → ℝ) (g : (Fin r → Fin D) → ℝ) :
    uniformInner (fun x => ∑ i ∈ s, f i x) g = ∑ i ∈ s, uniformInner (f i) g := by
  simp only [uniformInner, Finset.sum_mul, uniformExpect_sum]

theorem uniformInner_sum_right {ι : Type*} {D r : ℕ} (s : Finset ι)
    (f : (Fin r → Fin D) → ℝ) (g : ι → (Fin r → Fin D) → ℝ) :
    uniformInner f (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, uniformInner f (g i) := by
  simp only [uniformInner, Finset.mul_sum, uniformExpect_sum]

theorem uniformL2Sq_nonneg {D r : ℕ} (f : (Fin r → Fin D) → ℝ) :
    0 ≤ uniformL2Sq f :=
  uniformExpect_nonneg fun x => mul_self_nonneg (f x)

theorem uniformVecInner_eq_uniformExpect {D r ℓ : ℕ} (f g : (Fin r → Fin D) → Fin ℓ → ℝ) :
    uniformVecInner f g = uniformExpect fun x => ∑ j : Fin ℓ, f x j * g x j := by
  rw [uniformVecInner]
  simp only [uniformInner]
  rw [← uniformExpect_sum]

theorem uniformVecL2Sq_nonneg {D r ℓ : ℕ} (f : (Fin r → Fin D) → Fin ℓ → ℝ) :
    0 ≤ uniformVecL2Sq f := by
  rw [uniformVecL2Sq, uniformVecInner]
  exact Finset.sum_nonneg fun _ _ => uniformL2Sq_nonneg _

theorem uniformVecL2Sq_le_one_of_simplex {D r ℓ : ℕ} (hD : 0 < D)
    {f : (Fin r → Fin D) → Fin ℓ → ℝ}
    (h0 : ∀ x j, 0 ≤ f x j) (hsum : ∀ x, ∑ j, f x j = 1) :
    uniformVecL2Sq f ≤ 1 := by
  rw [uniformVecL2Sq, uniformVecInner_eq_uniformExpect]
  refine uniformExpect_le_const hD fun x => ?_
  have hle1 : ∀ j, f x j ≤ 1 := fun j =>
    (Finset.single_le_sum (fun i _ => h0 x i) (Finset.mem_univ j)).trans_eq (hsum x)
  calc
    ∑ j, f x j * f x j ≤ ∑ j, f x j * 1 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle1 j) (h0 x j)
    _ = 1 := by simp [hsum x]

/-! ### Alternating-sum cancellation helper -/

/-- For `A ⊂ B`, `∑_{A ⊆ T ⊆ B} (-1)^(B.card - T.card) = 0`. -/
private theorem sum_alternating_interval_eq_zero {α : Type*} [DecidableEq α]
    {A B : Finset α} (hAB : A ⊂ B) :
    ∑ T ∈ B.powerset.filter (fun T => A ⊆ T), (-1 : ℝ) ^ (B.card - T.card) = 0 := by
  obtain ⟨i₀, hi₀B, hi₀A⟩ := Finset.exists_of_ssubset hAB
  let P := B.powerset.filter (fun T => A ⊆ T)
  rw [← Finset.sum_filter_add_sum_filter_not P (fun T => i₀ ∈ T)]
  have hbij : ∑ T ∈ P.filter (fun T => i₀ ∈ T), (-1 : ℝ) ^ (B.card - T.card) =
      - ∑ T ∈ P.filter (fun T => i₀ ∉ T), (-1 : ℝ) ^ (B.card - T.card) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun T _ => T.erase i₀) ?_ ?_ ?_ ?_
    · intro T hT
      simp only [P, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      refine ⟨⟨(Finset.erase_subset i₀ T).trans hT.1.1, ?_⟩, Finset.notMem_erase i₀ T⟩
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun h => hi₀A (h ▸ hj), hT.1.2 hj⟩
    · intro a ha b hb h
      simp only [Finset.mem_filter] at ha hb
      rw [← Finset.insert_erase ha.2, ← Finset.insert_erase hb.2, h]
    · intro T hT
      simp only [P, Finset.mem_filter, Finset.mem_powerset] at hT
      refine ⟨insert i₀ T, ?_, Finset.erase_insert hT.2⟩
      simp only [P, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨⟨Finset.insert_subset hi₀B hT.1.1, hT.1.2.trans (Finset.subset_insert i₀ T)⟩,
        Finset.mem_insert_self i₀ T⟩
    · intro T hT
      simp only [P, Finset.mem_filter, Finset.mem_powerset] at hT
      have hle : T.card ≤ B.card := Finset.card_le_card hT.1.1
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨i₀, hT.2⟩
      rw [Finset.card_erase_of_mem hT.2]
      have hsub : B.card - (T.card - 1) = (B.card - T.card) + 1 := by omega
      rw [hsub, pow_succ]
      ring
  linarith

/-! ### Coordinate conditional expectation and orthogonal ANOVA decomposition -/

/-- Coordinate conditional expectation `E_S f` averaging over all coordinates outside `S`. -/
noncomputable def coordExpect {D r : ℕ} (S : Finset (Fin r)) (f : (Fin r → Fin D) → ℝ)
    (x : Fin r → Fin D) : ℝ :=
  (∑ y : Fin r → Fin D with ∀ i ∈ S, y i = x i, f y) / ((D ^ (r - S.card) : ℕ) : ℝ)

/-- Number of points `y : Fin r → Fin D` agreeing with `x` on `S` is `D ^ (r - S.card)`. -/
private theorem card_agree_eq {D r : ℕ} (S : Finset (Fin r)) (x : Fin r → Fin D) :
    (Finset.univ.filter fun y : Fin r → Fin D => ∀ i ∈ S, y i = x i).card = D ^ (r - S.card) := by
  classical
  let e : {y : Fin r → Fin D // ∀ i ∈ S, y i = x i} ≃ ({i : Fin r // i ∉ S} → Fin D) :=
    { toFun := fun y i => y.1 i.1
      invFun := fun g =>
        ⟨fun i => if h : i ∈ S then x i else g ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun y => by
        ext i
        by_cases hi : i ∈ S
        · simp [hi, y.2 i hi]
        · simp [hi]
      right_inv := fun g => by
        ext ⟨i, hi⟩
        simp [hi] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_subtype]
  congr 1
  have hcompl : (Finset.univ.filter fun i : Fin r => i ∉ S) = Sᶜ := by
    ext i; simp
  rw [hcompl, Finset.card_compl, Fintype.card_fin]

theorem coordExpect_univ {D r : ℕ} (f : (Fin r → Fin D) → ℝ) :
    coordExpect Finset.univ f = f := by
  ext x
  simp only [coordExpect, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero,
    Nat.cast_one, div_one]
  have hfilt : (Finset.univ.filter fun y : Fin r → Fin D =>
      ∀ i ∈ (Finset.univ : Finset (Fin r)), y i = x i) = {x} := by
    ext y
    simp [funext_iff]
  rw [hfilt, Finset.sum_singleton]

theorem coordExpect_empty {D r : ℕ} (f : (Fin r → Fin D) → ℝ) (x : Fin r → Fin D) :
    coordExpect ∅ f x = uniformExpect f := by
  simp [coordExpect, uniformExpect]

theorem coordExpect_add {D r : ℕ} (S : Finset (Fin r)) (f g : (Fin r → Fin D) → ℝ) :
    coordExpect S (fun x => f x + g x) = fun x => coordExpect S f x + coordExpect S g x := by
  ext x
  simp [coordExpect, Finset.sum_add_distrib, add_div]

theorem coordExpect_const_mul {D r : ℕ} (S : Finset (Fin r)) (c : ℝ)
    (f : (Fin r → Fin D) → ℝ) :
    coordExpect S (fun x => c * f x) = fun x => c * coordExpect S f x := by
  ext x
  simp [coordExpect, ← Finset.mul_sum, mul_div_assoc]

theorem coordExpect_sum {ι : Type*} {D r : ℕ} (S : Finset (Fin r)) (s : Finset ι)
    (f : ι → (Fin r → Fin D) → ℝ) :
    coordExpect S (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, coordExpect S (f i) x := by
  ext x
  simp only [coordExpect, Finset.sum_div]
  rw [Finset.sum_comm]

theorem coordExpect_comp {D r : ℕ} (hD : 0 < D) (S T : Finset (Fin r))
    (f : (Fin r → Fin D) → ℝ) :
    coordExpect S (coordExpect T f) = coordExpect (S ∩ T) f := by
  classical
  ext x
  have hpow : ∀ n : ℕ, ((D ^ n : ℕ) : ℝ) ≠ 0 := fun n =>
    (Nat.cast_pos.mpr (pow_pos hD n)).ne'
  simp only [coordExpect, ← Finset.sum_div, div_div]
  have hinner : ∀ z : Fin r → Fin D,
      (∑ y : Fin r → Fin D with ∀ i ∈ S, y i = x i,
        if ∀ i ∈ T, z i = y i then f z else 0) =
      if ∀ i ∈ S ∩ T, z i = x i then
        ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) * f z
      else 0 := by
    intro z
    rw [← Finset.sum_filter]
    by_cases hST : ∀ i ∈ S ∩ T, z i = x i
    · have hrhs : (if ∀ i ∈ S ∩ T, z i = x i then ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) * f z
          else 0) = ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) * f z := by split_ifs; rfl
      rw [hrhs]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      let e : {y : Fin r → Fin D // (∀ i ∈ S, y i = x i) ∧ (∀ i ∈ T, z i = y i)} ≃
          ({i : Fin r // i ∉ S ∪ T} → Fin D) :=
        { toFun := fun y i => y.1 i.1
          invFun := fun g =>
            ⟨fun i => if hS : i ∈ S then x i else if hT : i ∈ T then z i
              else g ⟨i, by simp [hS, hT]⟩,
              ⟨fun i hS => by simp [hS], fun i hT => by
                by_cases hS : i ∈ S
                · simp [hS, hST i (Finset.mem_inter.mpr ⟨hS, hT⟩)]
                · simp [hS, hT]⟩⟩
          left_inv := fun y => by
            ext i
            by_cases hS : i ∈ S
            · simp [hS, y.2.1 i hS]
            · by_cases hT : i ∈ T
              · simp [hS, hT, (y.2.2 i hT).symm]
              · simp [hS, hT]
          right_inv := fun g => by
            ext ⟨i, hi⟩
            have hS : i ∉ S := fun h => hi (Finset.mem_union_left T h)
            have hT : i ∉ T := fun h => hi (Finset.mem_union_right S h)
            simp [hS, hT] }
      have hcard : (Finset.univ.filter fun y : Fin r → Fin D =>
          (∀ i ∈ S, y i = x i) ∧ (∀ i ∈ T, z i = y i)).card = D ^ (r - (S ∪ T).card) := by
        rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_pi]
        simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_subtype]
        congr 1
        have hcompl : (Finset.univ.filter fun i : Fin r => i ∉ S ∪ T) = (S ∪ T)ᶜ := by
          ext i; simp
        rw [hcompl, Finset.card_compl, Fintype.card_fin]
      have hfilt : (Finset.univ.filter fun y : Fin r → Fin D => ∀ i ∈ S, y i = x i).filter
          (fun y => ∀ i ∈ T, z i = y i) =
          Finset.univ.filter (fun y => (∀ i ∈ S, y i = x i) ∧ (∀ i ∈ T, z i = y i)) := by
        ext y; simp
      rw [hfilt, hcard]
    · simp only [hST, ↓reduceIte]
      have hemp : (Finset.univ.filter fun y : Fin r → Fin D => ∀ i ∈ S, y i = x i).filter
          (fun y => ∀ i ∈ T, z i = y i) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hST fun i hi => (hy.2 i (Finset.mem_inter.mp hi).2).trans
          (hy.1 i (Finset.mem_inter.mp hi).1)
      simp [hemp]
  have hsum : (∑ y : Fin r → Fin D with ∀ i ∈ S, y i = x i,
        ∑ z : Fin r → Fin D with ∀ i ∈ T, z i = y i, f z) =
      ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) *
        ∑ z : Fin r → Fin D with ∀ i ∈ S ∩ T, z i = x i, f z := by
    calc
      (∑ y : Fin r → Fin D with ∀ i ∈ S, y i = x i,
          ∑ z : Fin r → Fin D with ∀ i ∈ T, z i = y i, f z)
          = ∑ y : Fin r → Fin D with ∀ i ∈ S, y i = x i,
              ∑ z : Fin r → Fin D, if ∀ i ∈ T, z i = y i then f z else 0 := by
            refine Finset.sum_congr rfl fun y _ => Finset.sum_filter ..
      _ = ∑ z : Fin r → Fin D, ∑ y : Fin r → Fin D with ∀ i ∈ S, y i = x i,
            if ∀ i ∈ T, z i = y i then f z else 0 :=
            Finset.sum_comm
      _ = ∑ z : Fin r → Fin D, if ∀ i ∈ S ∩ T, z i = x i then
            ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) * f z else 0 :=
            Finset.sum_congr rfl fun z _ => hinner z
      _ = ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) *
            ∑ z : Fin r → Fin D with ∀ i ∈ S ∩ T, z i = x i, f z := by
            rw [← Finset.sum_filter, ← Finset.mul_sum]
  rw [hsum]
  have hexp : r - (S ∪ T).card + (r - (S ∩ T).card) = (r - T.card) + (r - S.card) := by
    have h1 := Finset.card_union_add_card_inter S T
    have h2 : S.card ≤ r := by simpa [Fintype.card_fin] using Finset.card_le_univ S
    have h3 : T.card ≤ r := by simpa [Fintype.card_fin] using Finset.card_le_univ T
    have h4 : (S ∪ T).card ≤ r := by simpa [Fintype.card_fin] using Finset.card_le_univ (S ∪ T)
    have h5 : (S ∩ T).card ≤ r := by simpa [Fintype.card_fin] using Finset.card_le_univ (S ∩ T)
    omega
  have hcast : ((D ^ (r - T.card) : ℕ) : ℝ) * ((D ^ (r - S.card) : ℕ) : ℝ) =
      ((D ^ (r - (S ∪ T).card) : ℕ) : ℝ) * ((D ^ (r - (S ∩ T).card) : ℕ) : ℝ) := by
    norm_cast
    rw [← pow_add, ← pow_add, hexp]
  rw [hcast, mul_div_mul_left _ _ (hpow _)]

theorem coordExpect_selfAdjoint {D r : ℕ} (S : Finset (Fin r))
    (f g : (Fin r → Fin D) → ℝ) :
    uniformInner (coordExpect S f) g = uniformInner f (coordExpect S g) := by
  classical
  simp only [uniformInner, uniformExpect, coordExpect]
  congr 1
  simp only [div_mul_eq_mul_div, ← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    ∑ x : Fin r → Fin D, ∑ y with ∀ i ∈ S, y i = x i, f y * g x
        = ∑ x : Fin r → Fin D, ∑ y : Fin r → Fin D,
            if ∀ i ∈ S, y i = x i then f y * g x else 0 := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_filter ..
    _ = ∑ y : Fin r → Fin D, ∑ x : Fin r → Fin D,
            if ∀ i ∈ S, x i = y i then f y * g x else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
          have hiff : (∀ i ∈ S, y i = x i) ↔ (∀ i ∈ S, x i = y i) :=
            forall₂_congr fun _ _ => eq_comm
          simp [hiff]
    _ = ∑ y : Fin r → Fin D, ∑ x with ∀ i ∈ S, x i = y i, f y * g x := by
          refine Finset.sum_congr rfl fun y _ => (Finset.sum_filter ..).symm

/-- The Efron–Stein / ANOVA pure-`S` orthogonal component of `f : (Fin r → Fin D) → ℝ`. -/
noncomputable def anovaComponent {D r : ℕ} (S : Finset (Fin r)) (f : (Fin r → Fin D) → ℝ)
    (x : Fin r → Fin D) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * coordExpect T f x

theorem anovaComponent_add {D r : ℕ} (S : Finset (Fin r)) (f g : (Fin r → Fin D) → ℝ) :
    anovaComponent S (fun x => f x + g x) =
      fun x => anovaComponent S f x + anovaComponent S g x := by
  ext x
  simp [anovaComponent, coordExpect_add, mul_add, Finset.sum_add_distrib]

theorem anovaComponent_const_mul {D r : ℕ} (S : Finset (Fin r)) (c : ℝ)
    (f : (Fin r → Fin D) → ℝ) :
    anovaComponent S (fun x => c * f x) = fun x => c * anovaComponent S f x := by
  ext x
  simp [anovaComponent, coordExpect_const_mul, mul_left_comm, ← Finset.mul_sum]

theorem anovaComponent_sum {ι : Type*} {D r : ℕ} (S : Finset (Fin r)) (s : Finset ι)
    (f : ι → (Fin r → Fin D) → ℝ) :
    anovaComponent S (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, anovaComponent S (f i) x := by
  ext x
  simp only [anovaComponent, coordExpect_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Reconstruction: summing `anovaComponent S f` over all subsets `S` recovers `f`. -/
theorem sum_anovaComponent {D r : ℕ} (f : (Fin r → Fin D) → ℝ)
    (x : Fin r → Fin D) :
    ∑ S : Finset (Fin r), anovaComponent S f x = f x := by
  classical
  simp only [anovaComponent]
  calc
    ∑ S : Finset (Fin r), ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * coordExpect T f x
        = ∑ S : Finset (Fin r), ∑ T : Finset (Fin r),
            if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) * coordExpect T f x else 0 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [← Finset.sum_filter]
          congr 1; ext T; simp
    _ = ∑ T : Finset (Fin r), ∑ S : Finset (Fin r),
            if T ⊆ S then (-1 : ℝ) ^ (S.card - T.card) * coordExpect T f x else 0 :=
          Finset.sum_comm
    _ = ∑ T : Finset (Fin r),
          (∑ S with T ⊆ S, (-1 : ℝ) ^ (S.card - T.card)) * coordExpect T f x := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.sum_filter, Finset.sum_mul]
    _ = ∑ T : Finset (Fin r),
          (if T = Finset.univ then (1 : ℝ) else 0) * coordExpect T f x := by
          refine Finset.sum_congr rfl fun T _ => ?_
          congr 1
          by_cases hT : T = Finset.univ
          · subst hT
            have hfilt : (Finset.univ.filter fun S : Finset (Fin r) => Finset.univ ⊆ S) =
                {Finset.univ} := by
              ext S; simp [Finset.univ_subset_iff]
            rw [hfilt]
            simp
          · simp only [hT, ↓reduceIte]
            have hssub : T ⊂ Finset.univ :=
              Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, hT⟩
            have hpow : (Finset.univ : Finset (Fin r)).powerset.filter (fun S => T ⊆ S) =
                Finset.univ.filter (fun S => T ⊆ S) := by
              ext S; simp
            have hzero := sum_alternating_interval_eq_zero hssub
            rw [hpow] at hzero
            have hbij : ∑ S with T ⊆ S, (-1 : ℝ) ^ (S.card - T.card) =
                (-1 : ℝ) ^ ((Finset.univ : Finset (Fin r)).card - T.card) *
                  ∑ S with T ⊆ S, (-1 : ℝ) ^ ((Finset.univ : Finset (Fin r)).card - S.card) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun S hS => ?_
              have hcard_le : T.card ≤ S.card := Finset.card_le_card (Finset.mem_filter.mp hS).2
              have hS_le : S.card ≤ (Finset.univ : Finset (Fin r)).card :=
                Finset.card_le_univ S
              have hsum_exp : ((Finset.univ : Finset (Fin r)).card - T.card) +
                  ((Finset.univ : Finset (Fin r)).card - S.card) =
                  (S.card - T.card) + 2 * ((Finset.univ : Finset (Fin r)).card - S.card) := by
                omega
              rw [← pow_add, hsum_exp, pow_add, pow_mul]
              norm_num
            rw [hbij, hzero, mul_zero]
    _ = coordExpect Finset.univ f x := by simp
    _ = f x := by rw [coordExpect_univ]

/-- Action of `coordExpect T'` on `anovaComponent U f`: returns `anovaComponent U f` when
`U ⊆ T'` and `0` otherwise. -/
theorem coordExpect_anovaComponent {D r : ℕ} (hD : 0 < D) (T U : Finset (Fin r))
    (f : (Fin r → Fin D) → ℝ) :
    coordExpect T (anovaComponent U f) = if U ⊆ T then anovaComponent U f else 0 := by
  classical
  ext x
  have hlin : coordExpect T (anovaComponent U f) x =
      ∑ W ∈ U.powerset, (-1 : ℝ) ^ (U.card - W.card) * coordExpect T (coordExpect W f) x := by
    rw [show anovaComponent U f = fun y =>
        ∑ W ∈ U.powerset, (-1 : ℝ) ^ (U.card - W.card) * coordExpect W f y from rfl,
      coordExpect_sum]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [coordExpect_const_mul]
  rw [hlin]
  by_cases hUT : U ⊆ T
  · simp only [hUT, ↓reduceIte]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [coordExpect_comp hD, Finset.inter_eq_right.mpr ((Finset.mem_powerset.mp hW).trans hUT)]
  · simp only [hUT, ↓reduceIte, Pi.zero_apply]
    obtain ⟨t₀, ht₀U, ht₀T⟩ := Finset.not_subset.mp hUT
    rw [← Finset.sum_filter_add_sum_filter_not U.powerset (fun W => t₀ ∈ W)]
    have hbij : ∑ W ∈ U.powerset.filter (fun W => t₀ ∈ W),
        (-1 : ℝ) ^ (U.card - W.card) * coordExpect T (coordExpect W f) x =
        - ∑ W ∈ U.powerset.filter (fun W => t₀ ∉ W),
          (-1 : ℝ) ^ (U.card - W.card) * coordExpect T (coordExpect W f) x := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij (fun W _ => W.erase t₀) ?_ ?_ ?_ ?_
      · intro W hW
        simp only [Finset.mem_filter, Finset.mem_powerset] at hW ⊢
        exact ⟨(Finset.erase_subset t₀ W).trans hW.1, Finset.notMem_erase t₀ W⟩
      · intro a ha b hb h
        simp only [Finset.mem_filter] at ha hb
        rw [← Finset.insert_erase ha.2, ← Finset.insert_erase hb.2, h]
      · intro W hW
        simp only [Finset.mem_filter, Finset.mem_powerset] at hW
        refine ⟨insert t₀ W, ?_, Finset.erase_insert hW.2⟩
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset ht₀U hW.1, Finset.mem_insert_self t₀ W⟩
      · intro W hW
        simp only [Finset.mem_filter, Finset.mem_powerset] at hW
        rw [coordExpect_comp hD, coordExpect_comp hD]
        have hcap : T ∩ W.erase t₀ = T ∩ W := by
          ext t
          simp only [Finset.mem_inter, Finset.mem_erase]
          exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩,
            fun ⟨h1, h2⟩ => ⟨h1, fun ht => ht₀T (ht ▸ h1), h2⟩⟩
        rw [hcap, Finset.card_erase_of_mem hW.2]
        have hle : W.card ≤ U.card := Finset.card_le_card hW.1
        have hpos : 0 < W.card := Finset.card_pos.mpr ⟨t₀, hW.2⟩
        have hsub' : U.card - (W.card - 1) = (U.card - W.card) + 1 := by omega
        rw [hsub', pow_succ]
        ring
    linarith

/-- Mutual orthogonality of distinct ANOVA components. -/
theorem uniformInner_anovaComponent_eq_zero {D r : ℕ} (hD : 0 < D)
    {S₁ S₂ : Finset (Fin r)} (hne : S₁ ≠ S₂) (f g : (Fin r → Fin D) → ℝ) :
    uniformInner (anovaComponent S₁ f) (anovaComponent S₂ g) = 0 := by
  classical
  have hsymm : ∀ (A B : Finset (Fin r)) (u v : (Fin r → Fin D) → ℝ),
      (∃ i, i ∈ B ∧ i ∉ A) →
      uniformInner (anovaComponent A u) (anovaComponent B v) = 0 := by
    intro A B u v ⟨i₀, hi₀B, hi₀A⟩
    rw [show anovaComponent A u = fun x =>
        ∑ T₁ ∈ A.powerset, (-1 : ℝ) ^ (A.card - T₁.card) * coordExpect T₁ u x from rfl,
      uniformInner_sum_left]
    refine Finset.sum_eq_zero fun T₁ hT₁ => ?_
    rw [uniformInner_const_mul_left, coordExpect_selfAdjoint, coordExpect_anovaComponent hD]
    have hnsub : ¬ B ⊆ T₁ := fun h => hi₀A (Finset.mem_powerset.mp hT₁ (h hi₀B))
    simp [hnsub, uniformInner, uniformExpect]
  by_cases h1 : ∃ i, i ∈ S₂ ∧ i ∉ S₁
  · exact hsymm S₁ S₂ f g h1
  · have h2 : ∃ i, i ∈ S₁ ∧ i ∉ S₂ := by
      by_contra h
      push Not at h1 h
      exact hne (Finset.Subset.antisymm h h1)
    rw [uniformInner_comm]
    exact hsymm S₂ S₁ g f h2

/-- Parseval identity for the ANOVA decomposition. -/
theorem uniformL2Sq_eq_sum_anovaComponent {D r : ℕ} (hD : 0 < D)
    (f : (Fin r → Fin D) → ℝ) :
    uniformL2Sq f = ∑ S : Finset (Fin r), uniformL2Sq (anovaComponent S f) := by
  have hrecon : f = fun x => ∑ S : Finset (Fin r), anovaComponent S f x :=
    funext fun x => (sum_anovaComponent f x).symm
  conv_lhs => rw [uniformL2Sq, hrecon]
  rw [uniformInner_sum_left]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [uniformInner_sum_right, Finset.sum_eq_single S]
  · rfl
  · intro S' _ hne
    exact uniformInner_anovaComponent_eq_zero hD hne.symm f f
  · intro h; exact absurd (Finset.mem_univ S) h

/-! ### Orthonormal Fourier bases on `[D]^r` -/

/-- Predicate for a constant-`1` orthonormal basis on `Fin D` (`D > 0`) under the uniform
inner product. -/
@[expose] def IsOrthBasisOnFin {D : ℕ} (hD : 0 < D) (α : Fin D → Fin D → ℝ) : Prop :=
  (∀ y : Fin D, α ⟨0, hD⟩ y = 1) ∧
    (∀ i j : Fin D, (∑ y : Fin D, α i y * α j y) / (D : ℝ) = if i = j then 1 else 0)

/-- Tensor-product basis function `α_z(x) = ∏ i, α (z i) (x i)`. -/
@[expose] def tensorBasis {D r : ℕ} (α : Fin D → Fin D → ℝ) (z x : Fin r → Fin D) : ℝ :=
  ∏ i : Fin r, α (z i) (x i)

/-- Fourier coefficient `f̂(z) = ⟨f, α_z⟩`. -/
@[expose] noncomputable def fourierCoeff {D r : ℕ} (α : Fin D → Fin D → ℝ)
    (f : (Fin r → Fin D) → ℝ) (z : Fin r → Fin D) : ℝ :=
  uniformInner f (tensorBasis α z)

/-- Support of a multi-index `z : Fin r → Fin D`: coordinates where `z i ≠ 0`. -/
@[expose] def coeffSupport {D r : ℕ} (z : Fin r → Fin D) : Finset (Fin r) :=
  Finset.univ.filter fun i => (z i).1 ≠ 0

theorem mem_coeffSupport {D r : ℕ} {z : Fin r → Fin D} {i : Fin r} :
    i ∈ coeffSupport z ↔ (z i).1 ≠ 0 := by
  simp [coeffSupport]

/-- Tensor basis functions are orthonormal under `uniformInner`. -/
theorem uniformInner_tensorBasis {D r : ℕ} (hD : 0 < D) {α : Fin D → Fin D → ℝ}
    (hα : IsOrthBasisOnFin hD α) (z₁ z₂ : Fin r → Fin D) :
    uniformInner (tensorBasis α z₁) (tensorBasis α z₂) =
      @ite ℝ (z₁ = z₂) (Classical.propDecidable _) 1 0 := by
  classical
  simp only [uniformInner, uniformExpect, tensorBasis]
  have hprod : (∑ x : Fin r → Fin D, (∏ i, α (z₁ i) (x i)) * (∏ i, α (z₂ i) (x i))) /
      ((D ^ r : ℕ) : ℝ) =
      ∏ i : Fin r, ((∑ y : Fin D, α (z₁ i) y * α (z₂ i) y) / (D : ℝ)) := by
    simp only [← Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Fintype.prod_sum]
    congr 1
    push_cast
    rfl
  rw [hprod]
  simp only [hα.2]
  by_cases h : z₁ = z₂
  · subst h; simp
  · simp only [h, ↓reduceIte]
    have hex : ∃ i, z₁ i ≠ z₂ i := by
      by_contra hall; push Not at hall; exact h (funext hall)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Action of `coordExpect T` on a tensor basis vector. -/
theorem coordExpect_tensorBasis {D r : ℕ} (hD : 0 < D) {α : Fin D → Fin D → ℝ}
    (hα : IsOrthBasisOnFin hD α) (T : Finset (Fin r)) (z : Fin r → Fin D) :
    coordExpect T (tensorBasis α z) =
      if coeffSupport z ⊆ T then tensorBasis α z else 0 := by
  classical
  ext x
  simp only [coordExpect, tensorBasis]
  by_cases hsub : coeffSupport z ⊆ T
  · simp only [hsub, ↓reduceIte]
    have hconst : ∀ y : Fin r → Fin D, (∀ i ∈ T, y i = x i) →
        ∏ i, α (z i) (y i) = ∏ i, α (z i) (x i) := by
      intro y hy
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ T
      · rw [hy i hi]
      · have hz0 : z i = ⟨0, hD⟩ := by
          ext
          by_contra hne
          exact hi (hsub (mem_coeffSupport.mpr hne))
        rw [hz0, hα.1, hα.1]
    have hsum : (∑ y : Fin r → Fin D with ∀ i ∈ T, y i = x i, ∏ i, α (z i) (y i)) =
        ((D ^ (r - T.card) : ℕ) : ℝ) * ∏ i, α (z i) (x i) := by
      rw [Finset.sum_congr rfl fun y hy => hconst y (Finset.mem_filter.mp hy).2,
        Finset.sum_const, card_agree_eq, nsmul_eq_mul]
    rw [hsum, mul_div_cancel_left₀ _ (Nat.cast_pos.mpr (pow_pos hD _)).ne']
    rfl
  · simp only [hsub, ↓reduceIte, Pi.zero_apply]
    obtain ⟨i₀, hi₀_supp, hi₀_notT⟩ := Finset.not_subset.mp hsub
    have hzi₀ : z i₀ ≠ ⟨0, hD⟩ := fun h =>
      mem_coeffSupport.mp hi₀_supp (by simp [h])
    have hmean0 : ∑ y : Fin D, α (z i₀) y = 0 := by
      have h := hα.2 (z i₀) ⟨0, hD⟩
      simp only [hzi₀, ↓reduceIte, hα.1, mul_one] at h
      have hD0 : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
      exact (div_eq_zero_iff.mp h).resolve_right hD0
    have hsum0 : (∑ y : Fin r → Fin D with ∀ i ∈ T, y i = x i, ∏ i, α (z i) (y i)) = 0 := by
      let P := Finset.univ.filter fun y : Fin r → Fin D => ∀ i ∈ T, y i = x i
      let e : {y : Fin r → Fin D // ∀ i ∈ T, y i = x i} ≃
          Fin D × {g : Fin r → Fin D // (∀ i ∈ T, g i = x i) ∧ g i₀ = ⟨0, hD⟩} :=
        { toFun := fun y => (y.1 i₀, ⟨Function.update y.1 i₀ ⟨0, hD⟩,
            ⟨fun i hi => by
              have hne : i ≠ i₀ := fun h => hi₀_notT (h ▸ hi)
              simp [Function.update_of_ne hne, y.2 i hi],
             by simp⟩⟩)
          invFun := fun p => ⟨Function.update p.2.1 i₀ p.1, fun i hi => by
            have hne : i ≠ i₀ := fun h => hi₀_notT (h ▸ hi)
            simp [Function.update_of_ne hne, p.2.2.1 i hi]⟩
          left_inv := fun y => by ext i; by_cases h : i = i₀ <;> simp [h]
          right_inv := fun p => by
            ext
            · simp
            · rename_i i
              by_cases h : i = i₀
              · subst h; simp [p.2.2.2]
              · simp [h] }
      have hrewrite : (∑ y : Fin r → Fin D with ∀ i ∈ T, y i = x i, ∏ i, α (z i) (y i)) =
          ∑ p : Fin D × {g : Fin r → Fin D // (∀ i ∈ T, g i = x i) ∧ g i₀ = ⟨0, hD⟩},
            α (z i₀) p.1 * ∏ i ∈ Finset.univ.erase i₀, α (z i) (p.2.1 i) := by
        let eP : P ≃ {y : Fin r → Fin D // ∀ i ∈ T, y i = x i} :=
          Equiv.subtypeEquivRight fun y => by simp [P]
        have hcoe : (∑ y ∈ P, ∏ i, α (z i) (y i)) = ∑ y : P, ∏ i, α (z i) (y.1 i) :=
          (Finset.sum_coe_sort P (fun y => ∏ i, α (z i) (y i))).symm
        change (∑ y ∈ P, ∏ i, α (z i) (y i)) = _
        rw [hcoe]
        refine Fintype.sum_equiv (eP.trans e) _ _ fun y => ?_
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        simp [e, eP, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hrewrite, Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hmean0, zero_mul]
    rw [hsum0, zero_div]

/-- Action of `anovaComponent S` on a tensor basis vector. -/
theorem anovaComponent_tensorBasis {D r : ℕ} (hD : 0 < D) {α : Fin D → Fin D → ℝ}
    (hα : IsOrthBasisOnFin hD α) (S : Finset (Fin r)) (z : Fin r → Fin D) :
    anovaComponent S (tensorBasis α z) =
      if coeffSupport z = S then tensorBasis α z else 0 := by
  classical
  ext x
  simp only [anovaComponent, coordExpect_tensorBasis hD hα]
  by_cases heq : coeffSupport z = S
  · subst heq
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single (coeffSupport z)]
    · simp
    · intro T hT hne
      have hnsub : ¬ coeffSupport z ⊆ T := fun hsub =>
        hne (Finset.Subset.antisymm (Finset.mem_powerset.mp hT) hsub)
      simp [hnsub]
    · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h
  · simp only [heq, ↓reduceIte, Pi.zero_apply]
    by_cases hsub : coeffSupport z ⊆ S
    · have hlt : coeffSupport z ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
      let P := S.powerset.filter fun T => coeffSupport z ⊆ T
      have hrewrite : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
          (if coeffSupport z ⊆ T then tensorBasis α z else 0) x) =
          (∑ T ∈ P, (-1 : ℝ) ^ (S.card - T.card)) * tensorBasis α z x := by
        rw [Finset.sum_mul]
        have hstep : ∀ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
            (if coeffSupport z ⊆ T then tensorBasis α z else 0) x =
            if coeffSupport z ⊆ T then (-1 : ℝ) ^ (S.card - T.card) * tensorBasis α z x else 0 :=
          fun T _ => by split_ifs <;> simp
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
      rw [hrewrite, sum_alternating_interval_eq_zero hlt, zero_mul]
    · refine Finset.sum_eq_zero fun T hT => ?_
      have hnsub : ¬ coeffSupport z ⊆ T := fun h => hsub (h.trans (Finset.mem_powerset.mp hT))
      simp [hnsub]

/-- Every function `f : (Fin r → Fin D) → ℝ` expands in any constant-`1` orthonormal basis. -/
theorem fourier_expansion {D r : ℕ} (hD : 0 < D) {α : Fin D → Fin D → ℝ}
    (hα : IsOrthBasisOnFin hD α) (f : (Fin r → Fin D) → ℝ) (x : Fin r → Fin D) :
    f x = ∑ z : Fin r → Fin D, fourierCoeff α f z * tensorBasis α z x := by
  classical
  let V := (Fin r → Fin D) → ℝ
  let g : V := fun y => f y - ∑ z, fourierCoeff α f z * tensorBasis α z y
  have hinner_g : ∀ z, uniformInner g (tensorBasis α z) = 0 := by
    intro z
    have hsub : uniformInner g (tensorBasis α z) =
        uniformInner f (tensorBasis α z) -
          uniformInner (fun y => ∑ w, fourierCoeff α f w * tensorBasis α w y)
            (tensorBasis α z) := by
      simp only [g, uniformInner, sub_mul, uniformExpect_sub]
    rw [hsub, uniformInner_sum_left]
    simp only [uniformInner_const_mul_left, uniformInner_tensorBasis hD hα,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      fourierCoeff, sub_self]
  have hli : LinearIndependent ℝ (tensorBasis (r := r) α) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc z
    have h0 : uniformInner (fun y => ∑ w, c w * tensorBasis α w y) (tensorBasis α z) = 0 := by
      have hfun : (fun y => ∑ w, c w * tensorBasis α w y) = 0 := by
        ext y; simpa using congrFun hc y
      rw [hfun]
      simp [uniformInner, uniformExpect]
    rw [uniformInner_sum_left] at h0
    simpa [uniformInner_const_mul_left, uniformInner_tensorBasis hD hα] using h0
  have hspan : Submodule.span ℝ (Set.range (tensorBasis (r := r) α)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hg_mem : g ∈ Submodule.span ℝ (Set.range (tensorBasis (r := r) α)) :=
    hspan ▸ Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg_mem
  obtain ⟨c, hc⟩ := hg_mem
  have hgg : uniformL2Sq g = 0 := by
    rw [uniformL2Sq]
    have hfun : (c.sum fun z a => a • tensorBasis α z) =
        fun y => ∑ z ∈ c.support, c z * tensorBasis α z y := by
      ext y; simp [Finsupp.sum, smul_eq_mul]
    have hgc : g = fun y => ∑ z ∈ c.support, c z * tensorBasis α z y := hc.symm.trans hfun
    conv_lhs => arg 1; rw [hgc]
    rw [uniformInner_sum_left]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [uniformInner_const_mul_left, uniformInner_comm, hinner_g z, mul_zero]
  have hgx : g x = 0 := by
    have hsum0 : ∑ y, g y * g y = 0 := by
      simp only [uniformL2Sq, uniformInner, uniformExpect] at hgg
      exact (div_eq_zero_iff.mp hgg).resolve_right (Nat.cast_pos.mpr (pow_pos hD r)).ne'
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_self_nonneg (g y))).mp
      hsum0 x (Finset.mem_univ x)
    exact mul_self_eq_zero.mp hterm
  linarith [show g x = f x - ∑ z, fourierCoeff α f z * tensorBasis α z x from rfl]

/-- Parseval's identity in any constant-`1` orthonormal basis. -/
theorem parseval_fourier {D r : ℕ} (hD : 0 < D) {α : Fin D → Fin D → ℝ}
    (hα : IsOrthBasisOnFin hD α) (f g : (Fin r → Fin D) → ℝ) :
    uniformInner f g = ∑ z : Fin r → Fin D, fourierCoeff α f z * fourierCoeff α g z := by
  conv_lhs =>
    rw [show f = fun x => ∑ z, fourierCoeff α f z * tensorBasis α z x from
      funext (fourier_expansion hD hα f)]
  rw [uniformInner_sum_left]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [uniformInner_const_mul_left, uniformInner_comm, fourierCoeff]
  rfl

/-- Exact formula for `uniformL2Sq (anovaComponent S f)` in any constant-`1` orthonormal basis. -/
theorem uniformL2Sq_anovaComponent_eq_sum_fourierCoeff {D r : ℕ} (hD : 0 < D)
    {α : Fin D → Fin D → ℝ} (hα : IsOrthBasisOnFin hD α)
    (S : Finset (Fin r)) (f : (Fin r → Fin D) → ℝ) :
    uniformL2Sq (anovaComponent S f) =
      ∑ z : Fin r → Fin D with coeffSupport z = S, fourierCoeff α f z ^ 2 := by
  classical
  have hanova_f : anovaComponent S f =
      fun x => ∑ z with coeffSupport z = S, fourierCoeff α f z * tensorBasis α z x := by
    ext x
    conv_lhs =>
      rw [show f = fun y => ∑ z, fourierCoeff α f z * tensorBasis α z y from
        funext (fourier_expansion hD hα f)]
    rw [anovaComponent_sum]
    have hterm : ∀ z : Fin r → Fin D,
        anovaComponent S (fun y => fourierCoeff α f z * tensorBasis α z y) x =
          if coeffSupport z = S then fourierCoeff α f z * tensorBasis α z x else 0 := by
      intro z
      rw [anovaComponent_const_mul, anovaComponent_tensorBasis hD hα]
      split_ifs <;> simp
    simp only [hterm, ← Finset.sum_filter]
  rw [uniformL2Sq, hanova_f, uniformInner_sum_left]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [uniformInner_const_mul_left, uniformInner_sum_right, Finset.sum_eq_single z]
  · rw [uniformInner_const_mul_right, uniformInner_tensorBasis hD hα]
    simp [sq]
  · intro w _ hne
    rw [uniformInner_const_mul_right, uniformInner_tensorBasis hD hα]
    simp [hne.symm]
  · intro h; exact absurd hz h

/-! ### Low-degree influences, minor operations, and coordinate regrouping -/

/-- Basis-independent low-degree influence `Inf_i^{≤ d}(f)` of coordinate `i` on `f`. -/
noncomputable def lowDegInfluence {D r : ℕ} (d : ℕ) (i : Fin r) (f : (Fin r → Fin D) → ℝ) : ℝ :=
  ∑ S : Finset (Fin r) with i ∈ S ∧ S.card ≤ d, uniformL2Sq (anovaComponent S f)

/-- Low-degree influence of coordinate `i` on a vector-valued function `f : [D]^r → ℝ^ℓ`. -/
@[expose] noncomputable def lowDegVecInfluence {D r ℓ : ℕ} (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → Fin ℓ → ℝ) : ℝ :=
  ∑ j : Fin ℓ, lowDegInfluence d i (fun x => f x j)

theorem lowDegInfluence_nonneg {D r : ℕ} (d : ℕ) (i : Fin r) (f : (Fin r → Fin D) → ℝ) :
    0 ≤ lowDegInfluence d i f :=
  Finset.sum_nonneg fun _ _ => uniformL2Sq_nonneg _

theorem lowDegVecInfluence_nonneg {D r ℓ : ℕ} (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → Fin ℓ → ℝ) :
    0 ≤ lowDegVecInfluence d i f :=
  Finset.sum_nonneg fun _ _ => lowDegInfluence_nonneg _ _ _

/-- **Basis independence of low-degree influence**: for every constant-`1` orthonormal basis `α`,
`lowDegInfluence d i f = ∑_{z_i ≠ 0, |z| ≤ d} f̂(z)²`. -/
theorem lowDegInfluence_eq_sum_fourierCoeff {D r : ℕ} (hD : 0 < D)
    {α : Fin D → Fin D → ℝ} (hα : IsOrthBasisOnFin hD α)
    (d : ℕ) (i : Fin r) (f : (Fin r → Fin D) → ℝ) :
    lowDegInfluence d i f =
      ∑ z : Fin r → Fin D with (z i).1 ≠ 0 ∧ (coeffSupport z).card ≤ d,
        fourierCoeff α f z ^ 2 := by
  classical
  simp only [lowDegInfluence, uniformL2Sq_anovaComponent_eq_sum_fourierCoeff hD hα]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
  · intro ⟨S, z⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [hp.2]
    exact ⟨mem_coeffSupport.mp (hp.2 ▸ hp.1.1), hp.1.2⟩
  · intro ⟨S₁, z₁⟩ h₁ ⟨S₂, z₂⟩ h₂ (heq : z₁ = z₂)
    subst heq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Sigma.ext (h₁.2.symm.trans h₂.2) (heq_of_eq rfl)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨⟨coeffSupport z, z⟩, ?_, rfl⟩
    simp [mem_coeffSupport.mpr hz.1, hz.2]
  · intro _ _; rfl

theorem lowDegInfluence_le_uniformL2Sq {D r : ℕ} (hD : 0 < D) (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → ℝ) :
    lowDegInfluence d i f ≤ uniformL2Sq f := by
  rw [uniformL2Sq_eq_sum_anovaComponent hD f, lowDegInfluence]
  exact Finset.sum_le_univ_sum_of_nonneg fun _ => uniformL2Sq_nonneg _

theorem lowDegVecInfluence_le_uniformVecL2Sq {D r ℓ : ℕ} (hD : 0 < D) (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → Fin ℓ → ℝ) :
    lowDegVecInfluence d i f ≤ uniformVecL2Sq f :=
  Finset.sum_le_sum fun _ _ => lowDegInfluence_le_uniformL2Sq hD d i _

theorem sum_lowDegInfluence_le {D r : ℕ} (hD : 0 < D) (d : ℕ)
    (f : (Fin r → Fin D) → ℝ) :
    ∑ i : Fin r, lowDegInfluence d i f ≤ (d : ℝ) * uniformL2Sq f := by
  classical
  simp only [lowDegInfluence]
  calc
    ∑ i : Fin r, ∑ S with i ∈ S ∧ S.card ≤ d, uniformL2Sq (anovaComponent S f)
        = ∑ i : Fin r, ∑ S : Finset (Fin r),
            if i ∈ S ∧ S.card ≤ d then uniformL2Sq (anovaComponent S f) else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_filter ..
    _ = ∑ S : Finset (Fin r), ∑ i : Fin r,
            if i ∈ S ∧ S.card ≤ d then uniformL2Sq (anovaComponent S f) else 0 :=
          Finset.sum_comm
    _ = ∑ S : Finset (Fin r),
            (if S.card ≤ d then (S.card : ℝ) * uniformL2Sq (anovaComponent S f) else 0) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          by_cases hS : S.card ≤ d
          · simp only [hS, and_true, ↓reduceIte, ← Finset.sum_filter, Finset.sum_const,
              nsmul_eq_mul]
            congr 1
            have : (Finset.univ.filter fun i : Fin r => i ∈ S) = S := by ext i; simp
            rw [this]
          · simp [hS]
    _ ≤ ∑ S : Finset (Fin r), (d : ℝ) * uniformL2Sq (anovaComponent S f) := by
          refine Finset.sum_le_sum fun S _ => ?_
          split_ifs with hS
          · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hS) (uniformL2Sq_nonneg _)
          · exact mul_nonneg (Nat.cast_nonneg _) (uniformL2Sq_nonneg _)
    _ = (d : ℝ) * uniformL2Sq f := by
          rw [← Finset.mul_sum, uniformL2Sq_eq_sum_anovaComponent hD]

theorem sum_lowDegVecInfluence_le {D r ℓ : ℕ} (hD : 0 < D) (d : ℕ)
    (f : (Fin r → Fin D) → Fin ℓ → ℝ) :
    ∑ i : Fin r, lowDegVecInfluence d i f ≤ (d : ℝ) * uniformVecL2Sq f := by
  simp only [lowDegVecInfluence]
  rw [Finset.sum_comm]
  calc
    ∑ j : Fin ℓ, ∑ i : Fin r, lowDegInfluence d i (fun x => f x j)
        ≤ ∑ j : Fin ℓ, (d : ℝ) * uniformL2Sq (fun x => f x j) :=
          Finset.sum_le_sum fun _ _ => sum_lowDegInfluence_le hD d _
    _ = (d : ℝ) * uniformVecL2Sq f := by rw [← Finset.mul_sum]; rfl

/-- Coordinate minor of a vector `x : Fin s → Fin D` along `π : Fin r → Fin s`. -/
@[expose] def vecMinor {D r s : ℕ} (π : Fin r → Fin s) (x : Fin s → Fin D) : Fin r → Fin D :=
  fun i => x (π i)

/-- Function minor `f^π(x) = f(x^π)` along `π : Fin r → Fin s`. -/
@[expose] def funMinor {α : Type*} {D r s : ℕ} (π : Fin r → Fin s) (f : (Fin r → Fin D) → α) :
    (Fin s → Fin D) → α :=
  fun x => f (vecMinor π x)

/-- Bijective coordinate minor preserves the uniform expectation. -/
theorem uniformExpect_funMinor {D r : ℕ} (π : Equiv.Perm (Fin r))
    (f : (Fin r → Fin D) → ℝ) :
    uniformExpect (funMinor π f) = uniformExpect f := by
  simp only [uniformExpect, funMinor]
  congr 1
  exact Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl (Fin D))) _ _ fun x => rfl

/-- Bijective coordinate minor preserves the uniform inner product. -/
theorem uniformInner_funMinor {D r : ℕ} (π : Equiv.Perm (Fin r))
    (f g : (Fin r → Fin D) → ℝ) :
    uniformInner (funMinor π f) (funMinor π g) = uniformInner f g :=
  uniformExpect_funMinor π (fun x => f x * g x)

/-- Equivariance of `coordExpect` under bijective minors. -/
theorem coordExpect_funMinor {D r : ℕ} (π : Equiv.Perm (Fin r)) (S : Finset (Fin r))
    (f : (Fin r → Fin D) → ℝ) (x : Fin r → Fin D) :
    coordExpect S (funMinor π f) x = coordExpect (S.map π.symm.toEmbedding) f (vecMinor π x) := by
  classical
  simp only [coordExpect, funMinor, vecMinor, Finset.card_map]
  congr 1
  refine Finset.sum_bij (fun y _ => fun j => y (π j)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply] at hy ⊢
    rintro _ ⟨i, hi, rfl⟩
    simpa using hy i hi
  · intro y₁ _ y₂ _ heq
    ext i
    have := congrArg Fin.val (congrFun heq (π.symm i))
    simpa using this
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply] at hz
    refine ⟨fun i => z (π.symm i), ?_, by ext j; simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    simpa using hz (π.symm i) ⟨i, hi, rfl⟩
  · intro _ _; rfl

/-- Equivariance of `anovaComponent` under bijective minors. -/
theorem anovaComponent_funMinor {D r : ℕ} (π : Equiv.Perm (Fin r)) (S : Finset (Fin r))
    (f : (Fin r → Fin D) → ℝ) :
    anovaComponent S (funMinor π f) =
      funMinor π (anovaComponent (S.map π.symm.toEmbedding) f) := by
  classical
  ext x
  simp only [anovaComponent, funMinor, coordExpect_funMinor]
  refine Finset.sum_bij (fun T _ => T.map π.symm.toEmbedding) ?_ ?_ ?_ ?_
  · intro T hT
    exact Finset.mem_powerset.mpr (Finset.map_subset_map.mpr (Finset.mem_powerset.mp hT))
  · intro T₁ _ T₂ _ h
    exact Finset.map_injective π.symm.toEmbedding h
  · intro U hU
    refine ⟨U.map π.toEmbedding, ?_, ?_⟩
    · rw [Finset.mem_powerset] at hU ⊢
      intro i hi
      obtain ⟨j, hjU, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨i', hi'S, hji'⟩ := Finset.mem_map.mp (hU hjU)
      simpa [← hji'] using hi'S
    · ext j
      simp
  · intro T _
    simp [Finset.card_map]

/-- Low-degree influence under a bijective coordinate minor:
`Inf_i^{≤ d}(f^π) = Inf_{π⁻¹ i}^{≤ d}(f)`. -/
theorem lowDegInfluence_funMinor {D r : ℕ} (π : Equiv.Perm (Fin r)) (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → ℝ) :
    lowDegInfluence d i (funMinor π f) = lowDegInfluence d (π.symm i) f := by
  classical
  simp only [lowDegInfluence]
  refine Finset.sum_bij (fun S _ => S.map π.symm.toEmbedding) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact ⟨Finset.mem_map.mpr ⟨i, hS.1, rfl⟩, by simpa [Finset.card_map] using hS.2⟩
  · intro S₁ _ S₂ _ h; exact Finset.map_injective π.symm.toEmbedding h
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    refine ⟨U.map π.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_map]
      exact ⟨Finset.mem_map.mpr ⟨π.symm i, hU.1, by simp⟩, hU.2⟩
    · ext j; simp
  · intro S _
    rw [anovaComponent_funMinor, uniformL2Sq, uniformInner_funMinor]
    rfl

/-- Low-degree influence at `π i` under a bijective minor:
`Inf_{π i}^{≤ d}(f^π) = Inf_i^{≤ d}(f)`. -/
theorem lowDegInfluence_funMinor_apply {D r : ℕ} (π : Equiv.Perm (Fin r)) (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → ℝ) :
    lowDegInfluence d (π i) (funMinor π f) = lowDegInfluence d i f := by
  rw [lowDegInfluence_funMinor, Equiv.symm_apply_apply]

theorem lowDegVecInfluence_funMinor {D r ℓ : ℕ} (π : Equiv.Perm (Fin r)) (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → Fin ℓ → ℝ) :
    lowDegVecInfluence d i (funMinor π f) = lowDegVecInfluence d (π.symm i) f := by
  simp only [lowDegVecInfluence]
  refine Finset.sum_congr rfl fun j _ => lowDegInfluence_funMinor π d i (fun x => f x j)

theorem lowDegVecInfluence_funMinor_apply {D r ℓ : ℕ} (π : Equiv.Perm (Fin r)) (d : ℕ) (i : Fin r)
    (f : (Fin r → Fin D) → Fin ℓ → ℝ) :
    lowDegVecInfluence d (π i) (funMinor π f) = lowDegVecInfluence d i f := by
  rw [lowDegVecInfluence_funMinor, Equiv.symm_apply_apply]

/-- Convexity of low-degree influence: averaging functions over a nonempty finite index set
does not increase low-degree influence. -/
theorem lowDegInfluence_avg_le {ι : Type*} {D r : ℕ}
    (s : Finset ι) (hs : s.Nonempty) (d : ℕ) (i : Fin r)
    (f : ι → (Fin r → Fin D) → ℝ) :
    lowDegInfluence d i (fun x => (∑ a ∈ s, f a x) / (s.card : ℝ)) ≤
      (∑ a ∈ s, lowDegInfluence d i (f a)) / (s.card : ℝ) := by
  have hs_pos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
  have hterm : ∀ S : Finset (Fin r),
      uniformL2Sq (anovaComponent S (fun x => (∑ a ∈ s, f a x) / (s.card : ℝ))) ≤
        (∑ a ∈ s, uniformL2Sq (anovaComponent S (f a))) / (s.card : ℝ) := by
    intro S
    have hlin : anovaComponent S (fun x => (∑ a ∈ s, f a x) / (s.card : ℝ)) =
        fun x => (∑ a ∈ s, anovaComponent S (f a) x) / (s.card : ℝ) := by
      ext x
      simp only [div_eq_inv_mul, anovaComponent_const_mul, anovaComponent_sum]
    rw [hlin, uniformL2Sq, uniformInner, uniformExpect]
    have hcs : ∀ x, ((∑ a ∈ s, anovaComponent S (f a) x) / (s.card : ℝ)) ^ 2 ≤
        (∑ a ∈ s, anovaComponent S (f a) x ^ 2) / (s.card : ℝ) := by
      intro x
      have hsq := sq_sum_le_card_mul_sum_sq (s := s) (f := fun a => anovaComponent S (f a) x)
      rw [div_pow, div_le_div_iff₀ (pow_pos hs_pos 2) hs_pos]
      nlinarith
    have hstep1 : (∑ x : Fin r → Fin D, (∑ a ∈ s, anovaComponent S (f a) x ^ 2) / (s.card : ℝ)) /
        ((D ^ r : ℕ) : ℝ) =
        (∑ a ∈ s, uniformL2Sq (anovaComponent S (f a))) / (s.card : ℝ) := by
      simp only [uniformL2Sq, uniformInner, uniformExpect, sq, ← Finset.sum_div]
      rw [Finset.sum_comm, div_div, mul_comm (s.card : ℝ), ← div_div]
    calc
      (∑ x, ((∑ a ∈ s, anovaComponent S (f a) x) / (s.card : ℝ)) *
          ((∑ a ∈ s, anovaComponent S (f a) x) / (s.card : ℝ))) / ((D ^ r : ℕ) : ℝ)
          = (∑ x, ((∑ a ∈ s, anovaComponent S (f a) x) / (s.card : ℝ)) ^ 2) /
              ((D ^ r : ℕ) : ℝ) := by
            simp only [sq]
      _ ≤ (∑ x, (∑ a ∈ s, anovaComponent S (f a) x ^ 2) / (s.card : ℝ)) /
            ((D ^ r : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hcs x) (Nat.cast_nonneg _)
      _ = (∑ a ∈ s, uniformL2Sq (anovaComponent S (f a))) / (s.card : ℝ) := hstep1
  simp only [lowDegInfluence]
  rw [Finset.sum_div]
  have hrhs : ∑ a ∈ s, (∑ S with i ∈ S ∧ S.card ≤ d, uniformL2Sq (anovaComponent S (f a))) /
      (s.card : ℝ) =
      ∑ S with i ∈ S ∧ S.card ≤ d, (∑ a ∈ s, uniformL2Sq (anovaComponent S (f a))) /
        (s.card : ℝ) := by
    simp only [Finset.sum_div]
    exact Finset.sum_comm
  rw [hrhs]
  exact Finset.sum_le_sum fun S _ => hterm S

theorem lowDegVecInfluence_avg_le {ι : Type*} {D r ℓ : ℕ}
    (s : Finset ι) (hs : s.Nonempty) (d : ℕ) (i : Fin r)
    (f : ι → (Fin r → Fin D) → Fin ℓ → ℝ) :
    lowDegVecInfluence d i (fun x j => (∑ a ∈ s, f a x j) / (s.card : ℝ)) ≤
      (∑ a ∈ s, lowDegVecInfluence d i (f a)) / (s.card : ℝ) := by
  simp only [lowDegVecInfluence]
  rw [Finset.sum_div]
  have hrhs : ∑ a ∈ s, (∑ j : Fin ℓ, lowDegInfluence d i (fun x => f a x j)) / (s.card : ℝ) =
      ∑ j : Fin ℓ, (∑ a ∈ s, lowDegInfluence d i (fun x => f a x j)) / (s.card : ℝ) := by
    simp only [Finset.sum_div]
    exact Finset.sum_comm
  rw [hrhs]
  exact Finset.sum_le_sum fun j _ => lowDegInfluence_avg_le s hs d i (fun a x => f a x j)

/-! ### Coordinate regrouping (`2`-to-`1`) -/

/-- Canonical pairing equivalence `Fin r × Fin 2 ≃ Fin (2 * r)` mapping `(i, j)` to `2 * i + j`. -/
@[expose] def pairIndexEquiv (r : ℕ) : Fin r × Fin 2 ≃ Fin (2 * r) where
  toFun p := ⟨2 * p.1.1 + p.2.1, by omega⟩
  invFun t := (⟨t.1 / 2, by omega⟩, ⟨t.1 % 2, by omega⟩)
  left_inv p := by
    ext
    · dsimp; omega
    · dsimp; omega
  right_inv t := by
    ext
    dsimp; omega

/-- Regrouping a vector `x : Fin (2 * r) → Fin k` into `Fin r → Fin k × Fin k`. -/
@[expose] def regroup2 {k r : ℕ} (x : Fin (2 * r) → Fin k) : Fin r → Fin k × Fin k :=
  fun i => (x (pairIndexEquiv r (i, 0)), x (pairIndexEquiv r (i, 1)))

/-- Ungrouping a vector `y : Fin r → Fin k × Fin k` back to `Fin (2 * r) → Fin k`. -/
@[expose] def ungroup2 {k r : ℕ} (y : Fin r → Fin k × Fin k) : Fin (2 * r) → Fin k :=
  fun t =>
    let p := (pairIndexEquiv r).symm t
    if p.2 = 0 then (y p.1).1 else (y p.1).2

theorem regroup2_ungroup2 {k r : ℕ} (y : Fin r → Fin k × Fin k) :
    regroup2 (ungroup2 y) = y := by
  ext i <;> simp [regroup2, ungroup2]

private theorem fin2_eq_zero_or_one (c : Fin 2) : c = 0 ∨ c = 1 := by
  rcases c with ⟨v, hv⟩
  have : v = 0 ∨ v = 1 := by omega
  rcases this with rfl | rfl
  · left; rfl
  · right; rfl

theorem ungroup2_regroup2 {k r : ℕ} (x : Fin (2 * r) → Fin k) :
    ungroup2 (regroup2 x) = x := by
  ext t
  simp only [ungroup2, regroup2]
  rcases fin2_eq_zero_or_one ((pairIndexEquiv r).symm t).2 with h2 | h2
  · simp only [h2, ↓reduceIte]
    have hpair : (((pairIndexEquiv r).symm t).1, (0 : Fin 2)) = (pairIndexEquiv r).symm t :=
      Prod.ext rfl h2.symm
    rw [hpair, (pairIndexEquiv r).apply_symm_apply]
  · have hne : ((pairIndexEquiv r).symm t).2 ≠ 0 := by rw [h2]; decide
    simp only [hne, ↓reduceIte]
    have hpair : (((pairIndexEquiv r).symm t).1, (1 : Fin 2)) = (pairIndexEquiv r).symm t :=
      Prod.ext rfl h2.symm
    rw [hpair, (pairIndexEquiv r).apply_symm_apply]

/-- Regrouping a function `f : (Fin (2 * r) → Fin k) → α` to `(Fin r → Fin (k * k)) → α` via
`finProdFinEquiv`. -/
@[expose] def regroupFun2 {α : Type*} {k r : ℕ} (f : (Fin (2 * r) → Fin k) → α) :
    (Fin r → Fin (k * k)) → α :=
  fun y => f (ungroup2 fun i => finProdFinEquiv.symm (y i))

/-- Ungrouping a function `g : (Fin r → Fin (k * k)) → α` to `(Fin (2 * r) → Fin k) → α`. -/
@[expose] def ungroupFun2 {α : Type*} {k r : ℕ} (g : (Fin r → Fin (k * k)) → α) :
    (Fin (2 * r) → Fin k) → α :=
  fun x => g fun i => finProdFinEquiv (regroup2 x i)

theorem regroupFun2_ungroupFun2 {α : Type*} {k r : ℕ} (g : (Fin r → Fin (k * k)) → α) :
    regroupFun2 (ungroupFun2 g) = g := by
  ext y
  simp only [regroupFun2, ungroupFun2, regroup2_ungroup2, Equiv.apply_symm_apply]

/-- For `f : [k]^{2r} → ℝ`, `i ∈ [r]`, and `d : ℕ`,
`Inf_i^{≤ d}(regroupFun2 f) ≤ Inf_{2i}^{≤ 2d}(f) + Inf_{2i+1}^{≤ 2d}(f)`.
The degree bound `2 * d` on the right-hand side is sharp.
-/
theorem lowDegInfluence_regroupFun2_le {k r : ℕ} (hk : 0 < k) (d : ℕ) (i : Fin r)
    (f : (Fin (2 * r) → Fin k) → ℝ) :
    lowDegInfluence d i (regroupFun2 f) ≤
      lowDegInfluence (2 * d) (pairIndexEquiv r (i, 0)) f +
        lowDegInfluence (2 * d) (pairIndexEquiv r (i, 1)) f := by
  classical
  let e : (Fin (2 * r) → Fin k) ≃ (Fin r → Fin (k * k)) :=
    { toFun := fun x j => finProdFinEquiv (regroup2 x j)
      invFun := fun y => ungroup2 fun j => finProdFinEquiv.symm (y j)
      left_inv := fun x => by simp [ungroup2_regroup2]
      right_inv := fun y => by ext j; simp only [regroup2_ungroup2, Equiv.apply_symm_apply] }
  have hce : ∀ (g : (Fin (2 * r) → Fin k) → ℝ) (S : Finset (Fin r)) (x : Fin (2 * r) → Fin k),
      coordExpect S (regroupFun2 g) (e x) =
        coordExpect (S.biUnion fun j => {pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)})
          g x := by
    intro g S x
    set S' := S.biUnion fun j => {pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)}
    have hcardS' : S'.card = 2 * S.card := by
      have hdisj : (S : Set (Fin r)).PairwiseDisjoint
          fun j => ({pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)} :
            Finset (Fin (2 * r))) := by
        intro j₁ _ j₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro t ht₁ ht₂
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
        rcases ht₁ with rfl | rfl <;> rcases ht₂ with h | h <;>
          exact hne (congrArg Prod.fst ((pairIndexEquiv r).injective h))
      rw [Finset.card_biUnion hdisj]
      have h2 : ∀ j ∈ S,
          ({pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)} :
            Finset (Fin (2 * r))).card = 2 := by
        intro j _
        exact Finset.card_pair fun h =>
          Fin.zero_ne_one (congrArg Prod.snd ((pairIndexEquiv r).injective h))
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
    simp only [coordExpect, regroupFun2]
    rw [hcardS']
    have hpow : (k * k) ^ (r - S.card) = k ^ (2 * r - 2 * S.card) := by
      rw [← pow_two, ← pow_mul]
      congr 1; omega
    rw [hpow]
    congr 1
    refine Finset.sum_bij (fun y _ => e.symm y) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S', Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rintro t ⟨j, hjS, rfl | rfl⟩
      · have h := congrArg (fun p => (finProdFinEquiv.symm p).1) (hy j hjS)
        simpa [e, regroup2, ungroup2] using h
      · have h := congrArg (fun p => (finProdFinEquiv.symm p).2) (hy j hjS)
        simpa [e, regroup2, ungroup2] using h
    · intro y₁ _ y₂ _ h; exact e.symm.injective h
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S', Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton] at hz
      refine ⟨e z, ?_, e.symm_apply_apply z⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hjS
      have h0 := hz (pairIndexEquiv r (j, 0)) ⟨j, hjS, Or.inl rfl⟩
      have h1 := hz (pairIndexEquiv r (j, 1)) ⟨j, hjS, Or.inr rfl⟩
      simp [e, regroup2, h0, h1]
    · intro _ _; rfl
  have hpi : ∀ (S : Finset (Fin r)) (U : Finset (Fin (2 * r))),
      (let img : Finset (Fin r) := U.image (fun t => ((pairIndexEquiv r).symm t).1);
       anovaComponent S (regroupFun2 (anovaComponent U f)) =
         if img = S then regroupFun2 (anovaComponent U f) else 0) := by
    intro S U
    dsimp only
    set img : Finset (Fin r) := U.image (fun t => ((pairIndexEquiv r).symm t).1)
    have hce_U : ∀ (T : Finset (Fin r)),
        coordExpect T (regroupFun2 (anovaComponent U f)) =
          if img ⊆ T then regroupFun2 (anovaComponent U f) else 0 := by
      intro T
      ext y
      have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
      rw [hy, hce (anovaComponent U f) T (e.symm y)]
      set T' := T.biUnion fun j => {pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)}
      have hsub_iff : img ⊆ T ↔ U ⊆ T' := by
        constructor
        · intro h t ht
          have hmem : ((pairIndexEquiv r).symm t).1 ∈ T := h (Finset.mem_image_of_mem _ ht)
          simp only [T', Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
          refine ⟨((pairIndexEquiv r).symm t).1, hmem, ?_⟩
          rcases fin2_eq_zero_or_one ((pairIndexEquiv r).symm t).2 with h2 | h2
          · left
            have hpair : (((pairIndexEquiv r).symm t).1, (0 : Fin 2)) = (pairIndexEquiv r).symm t :=
              Prod.ext rfl h2.symm
            rw [hpair, (pairIndexEquiv r).apply_symm_apply]
          · right
            have hpair : (((pairIndexEquiv r).symm t).1, (1 : Fin 2)) = (pairIndexEquiv r).symm t :=
              Prod.ext rfl h2.symm
            rw [hpair, (pairIndexEquiv r).apply_symm_apply]
        · intro h j hj
          obtain ⟨t, htU, rfl⟩ := Finset.mem_image.mp hj
          have htT' := h htU
          simp only [T', Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at htT'
          obtain ⟨j', hj'T, htj'⟩ := htT'
          rcases htj' with rfl | rfl <;> simpa using hj'T
      rw [coordExpect_anovaComponent hk]
      by_cases h : img ⊆ T
      · simp only [h, ↓reduceIte, hsub_iff.mp h]
        rw [← hy]
        rfl
      · simp [h, mt hsub_iff.mpr h]
    ext y
    simp only [anovaComponent, hce_U]
    by_cases heq : img = S
    · subst heq
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single img]
      · simp
      · intro T hT hne
        have hnsub : ¬ img ⊆ T := fun h =>
          hne (Finset.Subset.antisymm (Finset.mem_powerset.mp hT) h)
        simp [hnsub]
      · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h
    · simp only [heq, ↓reduceIte, Pi.zero_apply]
      by_cases hsub : img ⊆ S
      · have hlt : img ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
        let P := S.powerset.filter fun T => img ⊆ T
        have hrewrite : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
            (if img ⊆ T then regroupFun2 (anovaComponent U f) else 0) y) =
            (∑ T ∈ P, (-1 : ℝ) ^ (S.card - T.card)) * regroupFun2 (anovaComponent U f) y := by
          rw [Finset.sum_mul]
          have hstep : ∀ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
              (if img ⊆ T then regroupFun2 (anovaComponent U f) else 0) y =
              if img ⊆ T then (-1 : ℝ) ^ (S.card - T.card) *
                regroupFun2 (anovaComponent U f) y else 0 := fun T _ => by split_ifs <;> simp
          rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
        rw [hrewrite, sum_alternating_interval_eq_zero hlt, zero_mul]
      · refine Finset.sum_eq_zero fun T hT => ?_
        have hnsub : ¬ img ⊆ T := fun h => hsub (h.trans (Finset.mem_powerset.mp hT))
        simp [hnsub]
  have hsq : ∀ S : Finset (Fin r),
      uniformL2Sq (anovaComponent S (regroupFun2 f)) =
        ∑ U : Finset (Fin (2 * r)) with U.image (fun t => ((pairIndexEquiv r).symm t).1) = S,
          uniformL2Sq (anovaComponent U f) := by
    intro S
    have hrf : regroupFun2 f = fun y => ∑ U, regroupFun2 (anovaComponent U f) y := by
      ext y
      exact (sum_anovaComponent f (e.symm y)).symm
    have hcomp : anovaComponent S (regroupFun2 f) =
        fun y => ∑ U with U.image (fun t => ((pairIndexEquiv r).symm t).1) = S,
          regroupFun2 (anovaComponent U f) y := by
      rw [hrf, anovaComponent_sum]
      ext y
      have hterm : ∀ U : Finset (Fin (2 * r)),
          anovaComponent S (regroupFun2 (anovaComponent U f)) y =
            if U.image (fun t => ((pairIndexEquiv r).symm t).1) = S then
              regroupFun2 (anovaComponent U f) y else 0 := fun U => by
        rw [hpi S U]; split_ifs <;> rfl
      simp only [hterm, ← Finset.sum_filter]
    have hinner_eq : ∀ g₁ g₂ : (Fin (2 * r) → Fin k) → ℝ,
        uniformInner (regroupFun2 g₁) (regroupFun2 g₂) = uniformInner g₁ g₂ := by
      intro g₁ g₂
      simp only [uniformInner, uniformExpect, regroupFun2]
      have hpow : (k * k) ^ r = k ^ (2 * r) := by rw [← pow_two, ← pow_mul]
      rw [hpow]
      congr 1
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
    rw [uniformL2Sq, hcomp, uniformInner_sum_left]
    refine Finset.sum_congr rfl fun U hU => ?_
    rw [uniformInner_sum_right, Finset.sum_eq_single U]
    · exact hinner_eq _ _
    · intro U' _ hne
      rw [hinner_eq]
      exact uniformInner_anovaComponent_eq_zero hk hne.symm f f
    · intro h; exact absurd hU h
  simp only [lowDegInfluence, hsq]
  rw [Finset.sum_sigma']
  let mapImg : Finset (Fin (2 * r)) → Finset (Fin r) :=
    fun U => U.image (fun t => ((pairIndexEquiv r).symm t).1)
  have hle_sum :
      ∑ p ∈ (Finset.univ.filter fun S : Finset (Fin r) => i ∈ S ∧ S.card ≤ d).sigma
          (fun S => Finset.univ.filter fun U : Finset (Fin (2 * r)) => mapImg U = S),
        uniformL2Sq (anovaComponent p.2 f) =
      ∑ U ∈ Finset.univ.filter
          (fun U : Finset (Fin (2 * r)) => i ∈ mapImg U ∧ (mapImg U).card ≤ d),
        uniformL2Sq (anovaComponent U f) := by
    refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
    · intro ⟨S, U⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [hp.2]; exact hp.1
    · intro ⟨S₁, U₁⟩ h₁ ⟨S₂, U₂⟩ h₂ (heq : U₁ = U₂)
      subst heq
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact Sigma.ext (h₁.2.symm.trans h₂.2) (heq_of_eq rfl)
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      refine ⟨⟨mapImg U, U⟩, ?_, rfl⟩
      simp [hU]
    · intro _ _; rfl
  rw [hle_sum]
  let A₀ := Finset.univ.filter fun U : Finset (Fin (2 * r)) =>
    pairIndexEquiv r (i, 0) ∈ U ∧ U.card ≤ 2 * d
  let A₁ := Finset.univ.filter fun U : Finset (Fin (2 * r)) =>
    pairIndexEquiv r (i, 1) ∈ U ∧ U.card ≤ 2 * d
  have hsub_union :
      (Finset.univ.filter fun U : Finset (Fin (2 * r)) => i ∈ mapImg U ∧ (mapImg U).card ≤ d) ⊆
        A₀ ∪ A₁ := by
    intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mapImg] at hU
    have hcard_le : U.card ≤ 2 * (U.image (fun t => ((pairIndexEquiv r).symm t).1)).card := by
      have hsubU : U ⊆ (U.image (fun t => ((pairIndexEquiv r).symm t).1)).biUnion
          fun j => {pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)} := by
        intro t ht
        simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
        refine ⟨((pairIndexEquiv r).symm t).1, Finset.mem_image_of_mem _ ht, ?_⟩
        rcases fin2_eq_zero_or_one ((pairIndexEquiv r).symm t).2 with h2 | h2
        · left
          have hpair : (((pairIndexEquiv r).symm t).1, (0 : Fin 2)) = (pairIndexEquiv r).symm t :=
            Prod.ext rfl h2.symm
          rw [hpair, (pairIndexEquiv r).apply_symm_apply]
        · right
          have hpair : (((pairIndexEquiv r).symm t).1, (1 : Fin 2)) = (pairIndexEquiv r).symm t :=
            Prod.ext rfl h2.symm
          rw [hpair, (pairIndexEquiv r).apply_symm_apply]
      calc
        U.card ≤ ((U.image (fun t => ((pairIndexEquiv r).symm t).1)).biUnion
            fun j => {pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)}).card :=
          Finset.card_le_card hsubU
        _ ≤ ∑ j ∈ U.image (fun t => ((pairIndexEquiv r).symm t).1),
            ({pairIndexEquiv r (j, 0), pairIndexEquiv r (j, 1)} :
              Finset (Fin (2 * r))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ U.image (fun t => ((pairIndexEquiv r).symm t).1), 2 :=
          Finset.sum_le_sum fun _ _ => Finset.card_le_two
        _ = 2 * (U.image (fun t => ((pairIndexEquiv r).symm t).1)).card := by
          simp [mul_comm]
    have hcard2d : U.card ≤ 2 * d := hcard_le.trans (Nat.mul_le_mul_left 2 hU.2)
    obtain ⟨t, htU, hti⟩ := Finset.mem_image.mp hU.1
    rw [Finset.mem_union]
    rcases fin2_eq_zero_or_one ((pairIndexEquiv r).symm t).2 with h2 | h2
    · left
      simp only [A₀, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hcard2d⟩
      have heq_t : pairIndexEquiv r (i, 0) = t := by
        have hpair : (i, (0 : Fin 2)) = (pairIndexEquiv r).symm t := Prod.ext hti.symm h2.symm
        rw [hpair, (pairIndexEquiv r).apply_symm_apply]
      rwa [heq_t]
    · right
      simp only [A₁, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hcard2d⟩
      have heq_t : pairIndexEquiv r (i, 1) = t := by
        have hpair : (i, (1 : Fin 2)) = (pairIndexEquiv r).symm t := Prod.ext hti.symm h2.symm
        rw [hpair, (pairIndexEquiv r).apply_symm_apply]
      rwa [heq_t]
  have hunion_le : ∑ U ∈ A₀ ∪ A₁, uniformL2Sq (anovaComponent U f) ≤
      (∑ U ∈ A₀, uniformL2Sq (anovaComponent U f)) +
        ∑ U ∈ A₁, uniformL2Sq (anovaComponent U f) := by
    have h := Finset.sum_union_inter (s₁ := A₀) (s₂ := A₁)
      (f := fun U => uniformL2Sq (anovaComponent U f))
    have hnn : 0 ≤ ∑ U ∈ A₀ ∩ A₁, uniformL2Sq (anovaComponent U f) :=
      Finset.sum_nonneg fun _ _ => uniformL2Sq_nonneg _
    linarith
  calc
    ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin (2 * r)) => i ∈ mapImg U ∧ (mapImg U).card ≤ d),
        uniformL2Sq (anovaComponent U f)
        ≤ ∑ U ∈ A₀ ∪ A₁, uniformL2Sq (anovaComponent U f) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun _ _ _ => uniformL2Sq_nonneg _
    _ ≤ (∑ U ∈ A₀, uniformL2Sq (anovaComponent U f)) +
          ∑ U ∈ A₁, uniformL2Sq (anovaComponent U f) := hunion_le

/-- Vector-valued coordinate regrouping bound with sharp degree `2 * d`. -/
theorem lowDegVecInfluence_regroupFun2_le {k r ℓ : ℕ} (hk : 0 < k) (d : ℕ) (i : Fin r)
    (f : (Fin (2 * r) → Fin k) → Fin ℓ → ℝ) :
    lowDegVecInfluence d i (regroupFun2 f) ≤
      lowDegVecInfluence (2 * d) (pairIndexEquiv r (i, 0)) f +
        lowDegVecInfluence (2 * d) (pairIndexEquiv r (i, 1)) f := by
  simp only [lowDegVecInfluence, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => lowDegInfluence_regroupFun2_le hk d i (fun x => f x j)

end CslibFrontier.Foundations.BooleanAnalysis
