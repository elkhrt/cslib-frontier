/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General-Alphabet Quantum Spectral Adversary Method

This module develops the nonnegative spectral adversary method in the quantum value-query model
(`Cslib.Quantum.ValueState`,
`Cslib.Quantum.valueOracle`, `Cslib.Quantum.runValue`) over arbitrary finite input and output
alphabets, proved under standard Lean axioms:

1. **Distinguisher matrices and spectral adversary bound**:
   - `CslibFrontier.Quantum.distinguisherMatrix` and `CslibFrontier.Quantum.maxDistinguisherNorm`:
     coordinate-disagreement matrices `D_i[x, y]` and `max_i ‖Γ ⊙ D_i‖`.
   - `CslibFrontier.Quantum.IsIndexedAdversary`, `CslibFrontier.Quantum.indexedSpectralAdversary`,
     and `CslibFrontier.Quantum.valueSpectralAdversary`: optimal spectral adversary ratio `SA(f)`
     for indexed input families and subsets `S ⊆ (ι → G)`.
2. **Domain transfers and distinguisher-cover reductions**:
   - `CslibFrontier.Quantum.indexedSpectralAdversary_le_of_embedding` and
     `CslibFrontier.Quantum.indexedSpectralAdversary_eq_of_equiv`: monotonicity under injective
     domain embeddings and invariance under equivalences.
   - `CslibFrontier.Quantum.indexedSpectralAdversary_div_le_of_cover`: native adversary reduction
     `SA(val₁, f₁) / c ≤ SA(val₂, f₂)` from `c`-point distinguisher covers.
3. **Špalek–Szegedy lower bound**:
   - `CslibFrontier.Quantum.one_sub_mul_opNorm_le_value`,
     `CslibFrontier.Quantum.one_sub_two_mul_sqrt_mul_indexedSpectralAdversary_le_two_mul`, and
     `CslibFrontier.Quantum.one_sub_two_mul_sqrt_mul_valueSpectralAdversary_le_two_mul`:
     `(1 - 2√(ε(1 - ε))) SA(f) ≤ 2 T` for any `T`-query unitary value-query algorithm.

## Main definitions

* `CslibFrontier.Quantum.distinguisherMatrix`, `CslibFrontier.Quantum.maxDistinguisherNorm`,
  `CslibFrontier.Quantum.IsIndexedAdversary`.
* `CslibFrontier.Quantum.indexedSpectralAdversary`, `CslibFrontier.Quantum.valueSpectralAdversary`.

## Main results

* `CslibFrontier.Quantum.opNorm_toEuclideanCLM_congr_equiv`,
  `CslibFrontier.Quantum.indexedSpectralAdversary_le_iff`.
* `CslibFrontier.Quantum.indexedSpectralAdversary_le_of_embedding`,
  `CslibFrontier.Quantum.indexedSpectralAdversary_eq_of_equiv`,
  `CslibFrontier.Quantum.indexedSpectralAdversary_div_le_of_cover`.
* `CslibFrontier.Quantum.one_sub_mul_opNorm_le_value`,
  `CslibFrontier.Quantum.one_sub_two_mul_sqrt_mul_indexedSpectralAdversary_le_two_mul`,
  `CslibFrontier.Quantum.one_sub_two_mul_sqrt_mul_valueSpectralAdversary_le_two_mul`.

## Tags

quantum query complexity, spectral adversary method, value query
-/

public section

open Finset Function Matrix Cslib.Quantum
open scoped Matrix RealInnerProductSpace Matrix.Norms.L2Operator

namespace CslibFrontier.Quantum

/-! ### 1. Bilinear and Matrix Equivalence Helpers -/

section Helpers

private theorem opNorm_toEuclideanCLM_mono_of_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A B : Matrix κ κ ℝ} (hA : ∀ x y, 0 ≤ A x y) (hAB : ∀ x y, A x y ≤ B x y) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
  refine opNorm_toEuclideanCLM_le_of_inner A (norm_nonneg _) fun u v hu hv ↦ ?_
  have habs := inner_toEuclideanCLM_le_absVec hA u v
  have hle : inner ℝ (absVec u) (toEuclideanCLM (𝕜 := ℝ) A (absVec v)) ≤
      inner ℝ (absVec u) (toEuclideanCLM (𝕜 := ℝ) B (absVec v)) := by
    simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, absVec_apply]
    refine sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hAB x y) (abs_nonneg _)) (abs_nonneg _)
  exact habs.trans (hle.trans ((le_abs_self _).trans
    (abs_inner_toEuclideanCLM_le_opNorm B (norm_absVec_le hu) (norm_absVec_le hv))))

private theorem opNorm_toEuclideanCLM_le_of_equiv {U V : Type*} [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V] (f : U ≃ V) {M : Matrix U U ℝ} {N : Matrix V V ℝ}
    (hMN : ∀ u₁ u₂, M u₁ u₂ = N (f u₁) (f u₂)) :
    ‖toEuclideanCLM (𝕜 := ℝ) M‖ ≤ ‖toEuclideanCLM (𝕜 := ℝ) N‖ := by
  refine opNorm_toEuclideanCLM_le_of_inner M (norm_nonneg _) fun u v hu hv ↦ ?_
  let u' : EuclideanSpace ℝ V := WithLp.toLp 2 fun y ↦ u.ofLp (f.symm y)
  let v' : EuclideanSpace ℝ V := WithLp.toLp 2 fun y ↦ v.ofLp (f.symm y)
  have hu' : ‖u'‖ ≤ 1 := by
    rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hu ⊢
    have hsum : (∑ y : V, u'.ofLp y ^ 2) = ∑ x : U, u.ofLp x ^ 2 :=
      f.symm.sum_comp (fun x : U ↦ u.ofLp x ^ 2)
    exact hsum.le.trans hu
  have hv' : ‖v'‖ ≤ 1 := by
    rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hv ⊢
    have hsum : (∑ y : V, v'.ofLp y ^ 2) = ∑ x : U, v.ofLp x ^ 2 :=
      f.symm.sum_comp (fun x : U ↦ v.ofLp x ^ 2)
    exact hsum.le.trans hv
  have heq : inner ℝ u (toEuclideanCLM (𝕜 := ℝ) M v) =
      inner ℝ u' (toEuclideanCLM (𝕜 := ℝ) N v') := by
    simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, u', v']
    rw [← f.sum_comp (fun y₁ : V ↦ ∑ y₂ : V, u.ofLp (f.symm y₁) * (N y₁ y₂ * v.ofLp (f.symm y₂)))]
    refine sum_congr rfl fun x₁ _ ↦ ?_
    rw [← f.sum_comp (fun y₂ : V ↦ u.ofLp (f.symm (f x₁)) * (N (f x₁) y₂ * v.ofLp (f.symm y₂)))]
    refine sum_congr rfl fun x₂ _ ↦ ?_
    simp only [Equiv.symm_apply_apply, hMN x₁ x₂]
  rw [heq]
  exact (le_abs_self _).trans (abs_inner_toEuclideanCLM_le_opNorm N hu' hv')

/-- Reindexing rows and columns of a finite real matrix by the same equivalence `e : X ≃ Y`
preserves its Euclidean `ℓ²` operator norm. -/
theorem opNorm_toEuclideanCLM_congr_equiv {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ≃ Y) {A : Matrix X X ℝ} {B : Matrix Y Y ℝ}
    (hAB : ∀ x₁ x₂, A x₁ x₂ = B (e x₁) (e x₂)) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ = ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
  refine le_antisymm (opNorm_toEuclideanCLM_le_of_equiv e hAB)
    (opNorm_toEuclideanCLM_le_of_equiv e.symm fun y₁ y₂ ↦ ?_)
  rw [hAB (e.symm y₁) (e.symm y₂), e.apply_symm_apply, e.apply_symm_apply]

private theorem opNorm_toEuclideanCLM_embed {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ↪ Y) (A : Matrix X X ℝ) :
    let B : Matrix Y Y ℝ := of fun y₁ y₂ ↦
      if h₁ : ∃ x₁, e x₁ = y₁ then
        if h₂ : ∃ x₂, e x₂ = y₂ then A h₁.choose h₂.choose else 0
      else 0
    ‖toEuclideanCLM (𝕜 := ℝ) B‖ = ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
  intro B
  have hB_apply : ∀ x₁ x₂ : X, B (e x₁) (e x₂) = A x₁ x₂ := fun x₁ x₂ ↦ by
    have h₁ : ∃ z₁, e z₁ = e x₁ := ⟨x₁, rfl⟩
    have h₂ : ∃ z₂, e z₂ = e x₂ := ⟨x₂, rfl⟩
    simp only [B, of_apply, h₁, h₂, ↓reduceDIte]
    rw [e.injective h₁.choose_spec, e.injective h₂.choose_spec]
  refine le_antisymm ?_ ?_
  · refine opNorm_toEuclideanCLM_le_of_inner B (norm_nonneg _) fun u v hu hv ↦ ?_
    let u' : EuclideanSpace ℝ X := WithLp.toLp 2 fun x ↦ u.ofLp (e x)
    let v' : EuclideanSpace ℝ X := WithLp.toLp 2 fun x ↦ v.ofLp (e x)
    have hu' : ‖u'‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hu ⊢
      have hmap : ∑ x : X, u.ofLp (e x) ^ 2 = ∑ y ∈ univ.map e, u.ofLp y ^ 2 :=
        (sum_map univ e (fun y ↦ u.ofLp y ^ 2)).symm
      exact (le_of_eq hmap).trans ((sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _).trans hu)
    have hv' : ‖v'‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hv ⊢
      have hmap : ∑ x : X, v.ofLp (e x) ^ 2 = ∑ y ∈ univ.map e, v.ofLp y ^ 2 :=
        (sum_map univ e (fun y ↦ v.ofLp y ^ 2)).symm
      exact (le_of_eq hmap).trans ((sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _).trans hv)
    have heq : inner ℝ u (toEuclideanCLM (𝕜 := ℝ) B v) =
        inner ℝ u' (toEuclideanCLM (𝕜 := ℝ) A v') := by
      simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum, u', v']
      have hrow : ∀ y₁ : Y, (∑ y₂ : Y, u.ofLp y₁ * (B y₁ y₂ * v.ofLp y₂)) =
          if h₁ : ∃ x₁, e x₁ = y₁ then
            ∑ x₂ : X, u.ofLp y₁ * (A h₁.choose x₂ * v.ofLp (e x₂))
          else 0 := fun y₁ ↦ by
        by_cases h₁ : ∃ x₁, e x₁ = y₁
        · simp only [h₁, ↓reduceDIte]
          trans ∑ y₂ ∈ univ.map e, u.ofLp y₁ * (B y₁ y₂ * v.ofLp y₂)
          · symm
            refine sum_subset (subset_univ _) fun y₂ _ hy₂ ↦ ?_
            have h₂ : ¬∃ x₂, e x₂ = y₂ := by simpa [mem_map] using hy₂
            simp [B, h₁, h₂]
          · rw [sum_map]
            refine sum_congr rfl fun x₂ _ ↦ ?_
            have hb : B y₁ (e x₂) = A h₁.choose x₂ := by
              conv_lhs => rw [← h₁.choose_spec]
              exact hB_apply h₁.choose x₂
            rw [hb]
        · simp [B, h₁]
      simp_rw [hrow]
      trans ∑ y₁ ∈ univ.map e,
        (if h₁ : ∃ x₁, e x₁ = y₁ then
          ∑ x₂ : X, u.ofLp y₁ * (A h₁.choose x₂ * v.ofLp (e x₂))
        else 0)
      · symm
        refine sum_subset (subset_univ _) fun y₁ _ hy₁ ↦ ?_
        have h₁ : ¬∃ x₁, e x₁ = y₁ := by simpa [mem_map] using hy₁
        simp [h₁]
      · rw [sum_map]
        refine sum_congr rfl fun x₁ _ ↦ ?_
        have h₁ : ∃ z₁, e z₁ = e x₁ := ⟨x₁, rfl⟩
        simp only [h₁, ↓reduceDIte, e.injective h₁.choose_spec]
    rw [heq]
    exact (le_abs_self _).trans (abs_inner_toEuclideanCLM_le_opNorm A hu' hv')
  · refine opNorm_toEuclideanCLM_le_of_inner A (norm_nonneg _) fun u v hu hv ↦ ?_
    let u' : EuclideanSpace ℝ Y :=
      WithLp.toLp 2 fun y ↦ if h : ∃ x, e x = y then u.ofLp h.choose else 0
    let v' : EuclideanSpace ℝ Y :=
      WithLp.toLp 2 fun y ↦ if h : ∃ x, e x = y then v.ofLp h.choose else 0
    have hu' : ‖u'‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hu ⊢
      have hsub : ∑ y : Y, u'.ofLp y ^ 2 = ∑ x : X, u.ofLp x ^ 2 := by
        trans ∑ y ∈ univ.map e, u'.ofLp y ^ 2
        · symm
          refine sum_subset (subset_univ _) fun y _ hy ↦ ?_
          have h : ¬∃ x, e x = y := by simpa [mem_map] using hy
          simp [u', h]
        · rw [sum_map]
          refine sum_congr rfl fun x _ ↦ ?_
          have h : ∃ z, e z = e x := ⟨x, rfl⟩
          simp only [u', h, ↓reduceDIte, e.injective h.choose_spec]
      exact hsub ▸ hu
    have hv' : ‖v'‖ ≤ 1 := by
      rw [EuclideanSpace.norm_le_one_iff_sum_sq_le_one] at hv ⊢
      have hsub : ∑ y : Y, v'.ofLp y ^ 2 = ∑ x : X, v.ofLp x ^ 2 := by
        trans ∑ y ∈ univ.map e, v'.ofLp y ^ 2
        · symm
          refine sum_subset (subset_univ _) fun y _ hy ↦ ?_
          have h : ¬∃ x, e x = y := by simpa [mem_map] using hy
          simp [v', h]
        · rw [sum_map]
          refine sum_congr rfl fun x _ ↦ ?_
          have h : ∃ z, e z = e x := ⟨x, rfl⟩
          simp only [v', h, ↓reduceDIte, e.injective h.choose_spec]
      exact hsub ▸ hv
    have heq : inner ℝ u (toEuclideanCLM (𝕜 := ℝ) A v) =
        inner ℝ u' (toEuclideanCLM (𝕜 := ℝ) B v') := by
      simp only [inner_toEuclideanCLM, dotProduct, mulVec, mul_sum]
      symm
      trans ∑ y₁ ∈ univ.map e,
        ∑ y₂ ∈ univ.map e, u'.ofLp y₁ * (B y₁ y₂ * v'.ofLp y₂)
      · trans ∑ y₁ ∈ univ.map e, ∑ y₂ : Y, u'.ofLp y₁ * (B y₁ y₂ * v'.ofLp y₂)
        · symm
          refine sum_subset (subset_univ _) fun y₁ _ hy₁ ↦ ?_
          have h₁ : ¬∃ x₁, e x₁ = y₁ := by simpa [mem_map] using hy₁
          simp [u', h₁]
        · refine sum_congr rfl fun y₁ _ ↦ ?_
          symm
          refine sum_subset (subset_univ _) fun y₂ _ hy₂ ↦ ?_
          have h₂ : ¬∃ x₂, e x₂ = y₂ := by simpa [mem_map] using hy₂
          simp [v', h₂]
      · simp only [sum_map]
        refine sum_congr rfl fun x₁ _ ↦ sum_congr rfl fun x₂ _ ↦ ?_
        have h₁ : ∃ z₁, e z₁ = e x₁ := ⟨x₁, rfl⟩
        have h₂ : ∃ z₂, e z₂ = e x₂ := ⟨x₂, rfl⟩
        simp only [u', v', h₁, h₂, ↓reduceDIte,
          e.injective h₁.choose_spec, e.injective h₂.choose_spec, hB_apply]
    rw [heq]
    exact (le_abs_self _).trans (abs_inner_toEuclideanCLM_le_opNorm B hu' hv')

private theorem sum_sq_mul_coord_eq {κ ι : Type*} [Fintype κ] [Fintype ι]
    (u : EuclideanSpace ℝ κ) (φ : κ → EuclideanSpace ℂ ι) :
    ∑ p : ι × Bool, ∑ x,
        (u.ofLp x * if p.2 then ((φ x).ofLp p.1).im else ((φ x).ofLp p.1).re) ^ 2 =
      ∑ x, (u.ofLp x * ‖φ x‖) ^ 2 := by
  rw [sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [Fintype.sum_prod_type, mul_pow, EuclideanSpace.norm_sq_eq, mul_sum]
  exact sum_congr rfl fun k _ ↦ by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte]
    ring

private theorem abs_sum_mul_re_inner_le {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (M : Matrix κ κ ℝ) (u v : EuclideanSpace ℝ κ) (φ ψ : κ → EuclideanSpace ℂ ι) :
    |∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))| ≤
      ‖toEuclideanCLM (𝕜 := ℝ) M‖ *
        √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) * √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) := by
  let coord (χ : κ → EuclideanSpace ℂ ι) (x : κ) (p : ι × Bool) : ℝ :=
    if p.2 then ((χ x).ofLp p.1).im else ((χ x).ofLp p.1).re
  have hre (x y : κ) : RCLike.re (inner ℂ (φ x) (ψ y)) =
      ∑ p : ι × Bool, coord φ x p * coord ψ y p := by
    rw [PiLp.inner_apply, map_sum, Fintype.sum_prod_type]
    exact sum_congr rfl fun k _ ↦ by
      simp only [RCLike.inner_apply', RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, coord]
      ring
  have hrewrite :
      (∑ x, ∑ y, M x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (ψ y))) =
      ∑ p : ι × Bool, ∑ x, ∑ y,
        (u.ofLp x * coord φ x p) * M x y * (v.ofLp y * coord ψ y p) := by
    simp only [hre, mul_sum]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  rw [hrewrite, l2_opNorm_toEuclideanCLM]
  calc
    |∑ p : ι × Bool, ∑ x, ∑ y,
          (u.ofLp x * coord φ x p) * M x y * (v.ofLp y * coord ψ y p)|
        ≤ ∑ p : ι × Bool, ‖M‖ * √(∑ x, (u.ofLp x * coord φ x p) ^ 2) *
            √(∑ y, (v.ofLp y * coord ψ y p) ^ 2) :=
          (abs_sum_le_sum_abs _ _).trans
            (sum_le_sum fun p _ ↦ abs_sum_mul_le_l2_opNorm M _ _)
    _ = ‖M‖ * ∑ p : ι × Bool,
          √(∑ x, (u.ofLp x * coord φ x p) ^ 2) *
            √(∑ y, (v.ofLp y * coord ψ y p) ^ 2) := by
          simp only [mul_assoc, ← mul_sum]
    _ ≤ ‖M‖ * (√(∑ p : ι × Bool, ∑ x, (u.ofLp x * coord φ x p) ^ 2) *
          √(∑ p : ι × Bool, ∑ y, (v.ofLp y * coord ψ y p) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le univ
            (fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)
            (fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)) (norm_nonneg _)
    _ = ‖M‖ * √(∑ x, (u.ofLp x * ‖φ x‖) ^ 2) *
          √(∑ y, (v.ofLp y * ‖ψ y‖) ^ 2) := by
          rw [sum_sq_mul_coord_eq u φ, sum_sq_mul_coord_eq v ψ, mul_assoc]

end Helpers

/-! ### 2. General-Alphabet Distinguisher Matrices and Spectral Adversary Bound -/

section SpectralAdversary

/-- **Distinguisher matrix** `D_i` for an indexed family of inputs `val : X → ι → G`:
entry `(x, y)` equals `1` if `val x i ≠ val y i` and `0` otherwise. -/
@[expose] def distinguisherMatrix {ι G X : Type*} [DecidableEq G] (val : X → ι → G) (i : ι) :
    Matrix X X ℝ :=
  of fun x y ↦ if val x i ≠ val y i then 1 else 0

/-- Coordinate evaluation of `distinguisherMatrix val i`. -/
theorem distinguisherMatrix_apply {ι G X : Type*} [DecidableEq G] (val : X → ι → G) (i : ι)
    (x y : X) :
    distinguisherMatrix val i x y = if val x i ≠ val y i then 1 else 0 :=
  rfl

/-- Diagonal entries of `distinguisherMatrix val i` vanish. -/
@[simp]
theorem distinguisherMatrix_self {ι G X : Type*} [DecidableEq G] (val : X → ι → G) (i : ι)
    (x : X) :
    distinguisherMatrix val i x x = 0 := by
  simp [distinguisherMatrix]

/-- `distinguisherMatrix val i` is symmetric. -/
theorem isSymm_distinguisherMatrix {ι G X : Type*} [DecidableEq G]
    (val : X → ι → G) (i : ι) :
    (distinguisherMatrix val i).IsSymm := by
  ext x y
  dsimp only [transpose_apply, distinguisherMatrix, of_apply]
  by_cases h : val x i = val y i
  · simp [h]
  · have h' : val y i ≠ val x i := Ne.symm h
    simp [h, h']

/-- Maximum coordinate-masked operator norm `max_{i ∈ ι} ‖Γ ⊙ D_i‖`
(`0` when `ι` is empty). -/
noncomputable def maxDistinguisherNorm {ι G X : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) (Γ : Matrix X X ℝ) : ℝ :=
  (((univ : Finset ι).sup fun i ↦
    ‖toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val i))‖₊ : NNReal) : ℝ)

/-- `maxDistinguisherNorm val Γ` is nonnegative. -/
theorem maxDistinguisherNorm_nonneg {ι G X : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) (Γ : Matrix X X ℝ) :
    0 ≤ maxDistinguisherNorm val Γ :=
  NNReal.coe_nonneg _

/-- The zero matrix has `maxDistinguisherNorm` equal to `0`. -/
@[simp]
theorem maxDistinguisherNorm_zero {ι G X : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) :
    maxDistinguisherNorm val (0 : Matrix X X ℝ) = 0 := by
  simp [maxDistinguisherNorm]

/-- For every query coordinate `i : ι`, `‖Γ ⊙ D_i‖ ≤ maxDistinguisherNorm val Γ`. -/
theorem opNorm_hadamard_distinguisher_le {ι G X : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) (Γ : Matrix X X ℝ) (i : ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val i))‖ ≤
      maxDistinguisherNorm val Γ :=
  NNReal.coe_le_coe.2 (Finset.le_sup (f := fun j ↦
    ‖toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val j))‖₊) (mem_univ i))

/-- Upper-bound characterization of `maxDistinguisherNorm val Γ ≤ K` for `0 ≤ K`. -/
theorem maxDistinguisherNorm_le_iff {ι G X : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] {val : X → ι → G} {Γ : Matrix X X ℝ}
    {K : ℝ} (hK : 0 ≤ K) :
    maxDistinguisherNorm val Γ ≤ K ↔
      ∀ i : ι,
        ‖toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val i))‖ ≤ K := by
  refine ⟨fun h i ↦ (opNorm_hadamard_distinguisher_le val Γ i).trans h, fun h ↦ ?_⟩
  rw [maxDistinguisherNorm, ← Real.coe_toNNReal K hK, NNReal.coe_le_coe, Finset.sup_le_iff]
  exact fun i _ ↦ (Real.le_toNNReal_iff_coe_le hK).2 (h i)

/-- Support condition for an adversary matrix `Γ` of `(val, f)`: every nonzero entry connects
distinct input strings with distinct target outputs. -/
@[expose] def IsIndexedAdversary {ι G X H : Type*} (val : X → ι → G) (f : X → H)
    (Γ : Matrix X X ℝ) : Prop :=
  ∀ x y, Γ x y ≠ 0 → val x ≠ val y ∧ f x ≠ f y

private theorem abs_entry_le_maxDistinguisherNorm {ι G X H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] {val : X → ι → G} {f : X → H} {Γ : Matrix X X ℝ}
    (hΓ : IsIndexedAdversary val f Γ) (x y : X) :
    |Γ x y| ≤ maxDistinguisherNorm val Γ := by
  by_cases h0 : Γ x y = 0
  · simp [h0, maxDistinguisherNorm_nonneg]
  · obtain ⟨hval, _⟩ := hΓ x y h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hval
    have hentry := abs_entry_le_norm_toEuclideanCLM
      (Γ.hadamard (distinguisherMatrix val i)) x y
    simpa only [hadamard_apply, distinguisherMatrix_apply, hi, ne_eq, not_false_eq_true,
      ↓reduceIte, mul_one] using hentry.trans (opNorm_hadamard_distinguisher_le val Γ i)

/-- If `maxDistinguisherNorm val Γ = 0` for an adversary matrix `Γ`, then `Γ = 0`. -/
theorem eq_zero_of_maxDistinguisherNorm_eq_zero {ι G X H : Type*} [Fintype ι]
    [DecidableEq G] [Fintype X] [DecidableEq X] {val : X → ι → G} {f : X → H}
    {Γ : Matrix X X ℝ} (hΓ : IsIndexedAdversary val f Γ)
    (h0 : maxDistinguisherNorm val Γ = 0) :
    Γ = 0 :=
  ext fun x y ↦ abs_nonpos_iff.1 ((abs_entry_le_maxDistinguisherNorm hΓ x y).trans_eq h0)

/-- For any adversary matrix `Γ` on `X`, `‖Γ‖ / maxDistinguisherNorm val Γ ≤ |X|`. -/
theorem norm_div_maxDistinguisherNorm_le_card {ι G X H : Type*} [Fintype ι]
    [DecidableEq G] [Fintype X] [DecidableEq X] {val : X → ι → G} {f : X → H}
    {Γ : Matrix X X ℝ} (hΓ : IsIndexedAdversary val f Γ) :
    ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDistinguisherNorm val Γ ≤
      (Fintype.card X : ℝ) := by
  rcases (maxDistinguisherNorm_nonneg val Γ).eq_or_lt with h0 | hpos
  · simp [← h0]
  · have hsum (g : X → ℝ) (hg : ∀ z, g z ≤ maxDistinguisherNorm val Γ) :
        ∑ z, g z ≤ (Fintype.card X : ℝ) * maxDistinguisherNorm val Γ :=
      (sum_le_sum fun z _ ↦ hg z).trans_eq (by simp [sum_const, card_univ, nsmul_eq_mul])
    refine (div_le_iff₀ hpos).2 ((opNorm_toEuclideanCLM_le_sqrt Γ (by positivity) (by positivity)
      (fun x ↦ hsum _ (abs_entry_le_maxDistinguisherNorm hΓ x))
      fun y ↦ hsum _ (abs_entry_le_maxDistinguisherNorm hΓ · y)).trans_eq
      (Real.sqrt_mul_self (by positivity)))

/-- **Nonnegative spectral adversary bound** `SA(f)` for an indexed input family
`val : X → ι → G` and target `f : X → H`: supremum of `‖Γ‖ / max_i ‖Γ ⊙ D_i‖` over symmetric
nonnegative adversary matrices `Γ`. -/
noncomputable def indexedSpectralAdversary {ι G X H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) (f : X → H) : ℝ :=
  sSup {r : ℝ | ∃ Γ : Matrix X X ℝ,
    Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ IsIndexedAdversary val f Γ ∧
      r = ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDistinguisherNorm val Γ}

private theorem bddAbove_indexedSpectralAdversary {ι G X H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) (f : X → H) :
    BddAbove {r : ℝ | ∃ Γ : Matrix X X ℝ,
      Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ IsIndexedAdversary val f Γ ∧
        r = ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDistinguisherNorm val Γ} :=
  ⟨Fintype.card X, fun _ ⟨_, _, _, hΓ, hr⟩ ↦
    hr ▸ norm_div_maxDistinguisherNorm_le_card hΓ⟩

/-- `indexedSpectralAdversary val f` is nonnegative. -/
theorem indexedSpectralAdversary_nonneg {ι G X H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] (val : X → ι → G) (f : X → H) :
    0 ≤ indexedSpectralAdversary val f :=
  Real.sSup_nonneg fun _ ⟨Γ, _, _, _, hr⟩ ↦
    hr ▸ div_nonneg (norm_nonneg _) (maxDistinguisherNorm_nonneg val Γ)

/-- Any symmetric nonnegative adversary matrix `Γ` yields a lower bound on
`indexedSpectralAdversary val f`. -/
theorem le_indexedSpectralAdversary {ι G X H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] {val : X → ι → G} {f : X → H} {Γ : Matrix X X ℝ}
    (hsym : Γ.IsSymm) (hnonneg : ∀ x y, 0 ≤ Γ x y) (hΓ : IsIndexedAdversary val f Γ) :
    ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ / maxDistinguisherNorm val Γ ≤
      indexedSpectralAdversary val f :=
  le_csSup (bddAbove_indexedSpectralAdversary val f) ⟨Γ, hsym, hnonneg, hΓ, rfl⟩

/-- Upper-bound characterization of `indexedSpectralAdversary val f ≤ K` for `0 ≤ K`. -/
theorem indexedSpectralAdversary_le_iff {ι G X H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] {val : X → ι → G} {f : X → H} {K : ℝ} (hK : 0 ≤ K) :
    indexedSpectralAdversary val f ≤ K ↔
      ∀ Γ : Matrix X X ℝ, Γ.IsSymm → (∀ x y, 0 ≤ Γ x y) →
        IsIndexedAdversary val f Γ →
          ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ K * maxDistinguisherNorm val Γ := by
  refine ⟨fun hle Γ hsym hnn hΓ ↦ ?_,
    fun h ↦ Real.sSup_le (fun _ ⟨Γ, hsym, hnn, hΓ, hr⟩ ↦ ?_) hK⟩
  · have hdiv := (le_indexedSpectralAdversary hsym hnn hΓ).trans hle
    rcases (maxDistinguisherNorm_nonneg val Γ).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero, eq_zero_of_maxDistinguisherNorm_eq_zero hΓ h0.symm,
        map_zero, norm_zero]
    · exact (div_le_iff₀ hpos).1 hdiv
  · rw [hr]
    rcases (maxDistinguisherNorm_nonneg val Γ).eq_or_lt with h0 | hpos
    · simp [← h0, hK]
    · exact (div_le_iff₀ hpos).2 (h Γ hsym hnn hΓ)

/-- Restricting an adversary problem to an embedded subfamily `e : X ↪ Y` cannot increase the
spectral adversary bound. -/
theorem indexedSpectralAdversary_le_of_embedding {ι G X Y H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {valX : X → ι → G} {fX : X → H} {valY : Y → ι → G} {fY : Y → H}
    (e : X ↪ Y) (hval : ∀ x, valY (e x) = valX x) (hf : ∀ x, fY (e x) = fX x) :
    indexedSpectralAdversary valX fX ≤ indexedSpectralAdversary valY fY := by
  rw [indexedSpectralAdversary_le_iff (indexedSpectralAdversary_nonneg valY fY)]
  intro Γ hsym hnn hΓ
  let ΓY : Matrix Y Y ℝ := of fun y₁ y₂ ↦
    if h₁ : ∃ x₁, e x₁ = y₁ then
      if h₂ : ∃ x₂, e x₂ = y₂ then Γ h₁.choose h₂.choose else 0
    else 0
  have hΓY_sym : ΓY.IsSymm := by
    ext y₁ y₂
    by_cases h₁ : ∃ x₁, e x₁ = y₁ <;> by_cases h₂ : ∃ x₂, e x₂ = y₂ <;>
      simp [ΓY, h₁, h₂, hsym.apply]
  have hΓY_nn : ∀ y₁ y₂, 0 ≤ ΓY y₁ y₂ := fun y₁ y₂ ↦ by
    by_cases h₁ : ∃ x₁, e x₁ = y₁ <;> by_cases h₂ : ∃ x₂, e x₂ = y₂ <;>
      simp [ΓY, h₁, h₂, hnn]
  have hΓY_adv : IsIndexedAdversary valY fY ΓY := fun y₁ y₂ hne ↦ by
    by_cases h₁ : ∃ x₁, e x₁ = y₁
    · by_cases h₂ : ∃ x₂, e x₂ = y₂
      · simp only [ΓY, of_apply, h₁, h₂, ↓reduceDIte] at hne
        obtain ⟨hv, hfx⟩ := hΓ h₁.choose h₂.choose hne
        rw [← h₁.choose_spec, ← h₂.choose_spec, hval, hval, hf, hf]
        exact ⟨hv, hfx⟩
      · simp [ΓY, h₁, h₂] at hne
    · simp [ΓY, h₁] at hne
  have hnorm_eq : ‖toEuclideanCLM (𝕜 := ℝ) ΓY‖ = ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ :=
    opNorm_toEuclideanCLM_embed e Γ
  have hmax_le : maxDistinguisherNorm valY ΓY ≤ maxDistinguisherNorm valX Γ := by
    rw [maxDistinguisherNorm_le_iff (maxDistinguisherNorm_nonneg valX Γ)]
    intro i
    have hhad_eq : ΓY.hadamard (distinguisherMatrix valY i) =
        (of fun y₁ y₂ ↦
          if h₁ : ∃ x₁, e x₁ = y₁ then
            if h₂ : ∃ x₂, e x₂ = y₂ then
              (Γ.hadamard (distinguisherMatrix valX i)) h₁.choose h₂.choose
            else 0
          else 0) := by
      ext y₁ y₂
      by_cases h₁ : ∃ x₁, e x₁ = y₁
      · by_cases h₂ : ∃ x₂, e x₂ = y₂
        · have hy₁ : valY y₁ = valX h₁.choose := by
            conv_lhs => rw [← h₁.choose_spec]
            exact hval h₁.choose
          have hy₂ : valY y₂ = valX h₂.choose := by
            conv_lhs => rw [← h₂.choose_spec]
            exact hval h₂.choose
          simp only [hadamard_apply, ΓY, of_apply, h₁, h₂, ↓reduceDIte,
            distinguisherMatrix_apply, hy₁, hy₂]
        · simp [ΓY, h₁, h₂]
      · simp [ΓY, h₁]
    rw [hhad_eq, opNorm_toEuclideanCLM_embed e (Γ.hadamard (distinguisherMatrix valX i))]
    exact opNorm_hadamard_distinguisher_le valX Γ i
  have hbound := ((indexedSpectralAdversary_le_iff (indexedSpectralAdversary_nonneg valY fY)).1
    le_rfl) ΓY hΓY_sym hΓY_nn hΓY_adv
  rw [hnorm_eq] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left hmax_le (indexedSpectralAdversary_nonneg valY fY))

/-- Reindexing an adversary problem along an equivalence `e : X ≃ Y` preserves
`indexedSpectralAdversary`. -/
theorem indexedSpectralAdversary_eq_of_equiv {ι G X Y H : Type*} [Fintype ι] [DecidableEq G]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {valX : X → ι → G} {fX : X → H} {valY : Y → ι → G} {fY : Y → H}
    (e : X ≃ Y) (hval : ∀ x, valY (e x) = valX x) (hf : ∀ x, fY (e x) = fX x) :
    indexedSpectralAdversary valX fX = indexedSpectralAdversary valY fY :=
  le_antisymm (indexedSpectralAdversary_le_of_embedding e.toEmbedding hval hf)
    (indexedSpectralAdversary_le_of_embedding e.symm.toEmbedding
      (fun y ↦ by simpa using (hval (e.symm y)).symm)
      (fun y ↦ by simpa using (hf (e.symm y)).symm))

/-- **Native spectral adversary reduction via distinguisher covers**: if `(val₁, f₁)` and
`(val₂, f₂)` share the parameter space `X` such that distinct `f₁`-answers imply distinct
`val₂` inputs and distinct `f₂`-answers, and every query coordinate `q : ι₂` is covered by a set
`V ⊆ ι₁` of size at most `c` (`1 ≤ c`) witnessing any disagreement at `q`, then
`indexedSpectralAdversary val₁ f₁ / c ≤ indexedSpectralAdversary val₂ f₂`. -/
theorem indexedSpectralAdversary_div_le_of_cover {ι₁ G₁ ι₂ G₂ X H₁ H₂ : Type*}
    [Fintype ι₁] [DecidableEq G₁] [Fintype ι₂] [DecidableEq G₂]
    [Fintype X] [DecidableEq X]
    {val₁ : X → ι₁ → G₁} {f₁ : X → H₁} {val₂ : X → ι₂ → G₂} {f₂ : X → H₂}
    (hadv : ∀ x y, val₁ x ≠ val₁ y → f₁ x ≠ f₁ y →
      val₂ x ≠ val₂ y ∧ f₂ x ≠ f₂ y)
    {c : ℕ} (hc : 1 ≤ c)
    (hcover : ∀ q : ι₂, ∃ V : Finset ι₁, V.card ≤ c ∧
      ∀ x y : X, f₁ x ≠ f₁ y → val₂ x q ≠ val₂ y q →
        ∃ p ∈ V, val₁ x p ≠ val₁ y p) :
    indexedSpectralAdversary val₁ f₁ / (c : ℝ) ≤ indexedSpectralAdversary val₂ f₂ := by
  have hc_pos : (0 : ℝ) < c := by positivity
  rw [div_le_iff₀ hc_pos,
    indexedSpectralAdversary_le_iff
      (mul_nonneg (indexedSpectralAdversary_nonneg val₂ f₂) hc_pos.le)]
  intro Γ hsym hnn hΓ₁
  have hΓ₂ : IsIndexedAdversary val₂ f₂ Γ := fun x y h0 ↦
    hadv x y (hΓ₁ x y h0).1 (hΓ₁ x y h0).2
  have hmax : maxDistinguisherNorm val₂ Γ ≤ (c : ℝ) * maxDistinguisherNorm val₁ Γ := by
    rw [maxDistinguisherNorm_le_iff (mul_nonneg hc_pos.le (maxDistinguisherNorm_nonneg val₁ Γ))]
    intro q
    obtain ⟨V, hVcard, hVq⟩ := hcover q
    have hentry_le : ∀ x y : X, (Γ.hadamard (distinguisherMatrix val₂ q)) x y ≤
        (∑ p ∈ V, Γ.hadamard (distinguisherMatrix val₁ p)) x y := fun x y ↦ by
      rw [Matrix.sum_apply, hadamard_apply, distinguisherMatrix_apply]
      by_cases h0 : Γ x y = 0
      · simp only [h0, zero_mul]
        exact sum_nonneg fun p _ ↦ by
          rw [hadamard_apply, h0, zero_mul]
      · split_ifs with hneq
        · obtain ⟨p, hpV, hpne⟩ := hVq x y (hΓ₁ x y h0).2 hneq
          rw [mul_one]
          have hsingle : (Γ.hadamard (distinguisherMatrix val₁ p)) x y ≤
              ∑ p' ∈ V, (Γ.hadamard (distinguisherMatrix val₁ p')) x y :=
            single_le_sum (f := fun p' ↦ (Γ.hadamard (distinguisherMatrix val₁ p')) x y)
              (fun p' _ ↦ by
                rw [hadamard_apply, distinguisherMatrix_apply]
                split_ifs <;> simp [hnn x y]) hpV
          refine (?_ : Γ x y ≤ (Γ.hadamard (distinguisherMatrix val₁ p)) x y).trans hsingle
          simp [hadamard_apply, distinguisherMatrix_apply, hpne]
        · rw [mul_zero]
          exact sum_nonneg fun p _ ↦ by
            rw [hadamard_apply, distinguisherMatrix_apply]
            split_ifs <;> simp [hnn x y]
    have hhad_nn : ∀ x y, 0 ≤ (Γ.hadamard (distinguisherMatrix val₂ q)) x y := fun x y ↦ by
      rw [hadamard_apply, distinguisherMatrix_apply]
      split_ifs <;> simp [hnn x y]
    calc
      ‖toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val₂ q))‖
          ≤ ‖toEuclideanCLM (𝕜 := ℝ)
              (∑ p ∈ V, Γ.hadamard (distinguisherMatrix val₁ p))‖ :=
            opNorm_toEuclideanCLM_mono_of_nonneg hhad_nn hentry_le
      _ = ‖∑ p ∈ V,
            toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val₁ p))‖ := by
            rw [map_sum]
      _ ≤ ∑ p ∈ V,
            ‖toEuclideanCLM (𝕜 := ℝ) (Γ.hadamard (distinguisherMatrix val₁ p))‖ :=
            norm_sum_le V _
      _ ≤ ∑ _p ∈ V, maxDistinguisherNorm val₁ Γ :=
            sum_le_sum fun p _ ↦ opNorm_hadamard_distinguisher_le val₁ Γ p
      _ = (V.card : ℝ) * maxDistinguisherNorm val₁ Γ := by
            simp [sum_const, nsmul_eq_mul]
      _ ≤ (c : ℝ) * maxDistinguisherNorm val₁ Γ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hVcard)
              (maxDistinguisherNorm_nonneg val₁ Γ)
  have hle₂ := ((indexedSpectralAdversary_le_iff (indexedSpectralAdversary_nonneg val₂ f₂)).1
    le_rfl) Γ hsym hnn hΓ₂
  calc
    ‖toEuclideanCLM (𝕜 := ℝ) Γ‖
        ≤ indexedSpectralAdversary val₂ f₂ * maxDistinguisherNorm val₂ Γ := hle₂
    _ ≤ indexedSpectralAdversary val₂ f₂ * ((c : ℝ) * maxDistinguisherNorm val₁ Γ) :=
          mul_le_mul_of_nonneg_left hmax (indexedSpectralAdversary_nonneg val₂ f₂)
    _ = indexedSpectralAdversary val₂ f₂ * (c : ℝ) * maxDistinguisherNorm val₁ Γ := by ring

/-- **Nonnegative spectral adversary bound** `SA(f)` for a partial function `f : S → H` defined on
a domain `S : Set (ι → G)` over finite alphabets. -/
noncomputable def valueSpectralAdversary {ι G H : Type*} [Fintype ι] [Finite G]
    (S : Set (ι → G)) (f : S → H) : ℝ := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  exact indexedSpectralAdversary Subtype.val f

/-- `valueSpectralAdversary S f` is nonnegative. -/
theorem valueSpectralAdversary_nonneg {ι G H : Type*} [Fintype ι] [Finite G]
    (S : Set (ι → G)) (f : S → H) :
    0 ≤ valueSpectralAdversary S f := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  exact indexedSpectralAdversary_nonneg Subtype.val f

/-- Any injectively parameterized subfamily of `S` gives a lower bound on
`valueSpectralAdversary S f`. -/
theorem indexedSpectralAdversary_le_valueSpectralAdversary {ι G X H : Type*} [Fintype ι]
    [DecidableEq G] [Finite G] [Fintype X] [DecidableEq X]
    {S : Set (ι → G)} {f : S → H} (e : X ↪ S) :
    indexedSpectralAdversary (fun x ↦ (e x).1) (fun x ↦ f (e x)) ≤
      valueSpectralAdversary S f := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  have hcongr : indexedSpectralAdversary (G := G) (X := S) Subtype.val f =
      valueSpectralAdversary S f := by
    unfold valueSpectralAdversary
    congr!
  rw [← hcongr]
  exact indexedSpectralAdversary_le_of_embedding e (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- A bijective parameterization `e : X ≃ S` identifies `indexedSpectralAdversary` with
`valueSpectralAdversary S f`. -/
theorem indexedSpectralAdversary_eq_valueSpectralAdversary {ι G X H : Type*} [Fintype ι]
    [DecidableEq G] [Finite G] [Fintype X] [DecidableEq X]
    {S : Set (ι → G)} {f : S → H} (e : X ≃ S) :
    indexedSpectralAdversary (fun x ↦ (e x).1) (fun x ↦ f (e x)) =
      valueSpectralAdversary S f := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  have hcongr : indexedSpectralAdversary (G := G) (X := S) Subtype.val f =
      valueSpectralAdversary S f := by
    unfold valueSpectralAdversary
    congr!
  rw [← hcongr]
  exact indexedSpectralAdversary_eq_of_equiv e (fun _ ↦ rfl) (fun _ ↦ rfl)

end SpectralAdversary

/-! ### 3. Špalek–Szegedy Lower Bound for Unitary Value-Query Algorithms -/

section QueryLowerBound

variable {ι G V W X H : Type*} [Fintype ι] [DecidableEq G] [Fintype V] [Fintype W]
  [Fintype X] [DecidableEq X]

private noncomputable def valAdvForm (Γ : Matrix X X ℝ) (u v : EuclideanSpace ℝ X)
    (φ : X → ValueState ι V W) : ℝ :=
  ∑ x, ∑ y, Γ x y * u.ofLp x * v.ofLp y * RCLike.re (inner ℂ (φ x) (φ y))

private theorem valAdvForm_step_sub_le (val : X → ι → G) (Γ : Matrix X X ℝ)
    (u v : EuclideanSpace ℝ X) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (step : G → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (t : ℕ) :
    |valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) t) -
        valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) (t + 1))| ≤
      2 * maxDistinguisherNorm val Γ := by
  let φ : X → ValueState ι V W := fun x ↦ runValue step U ψ₀ (val x) t
  let φ' : X → ValueState ι V W := fun x ↦ valueOracle step (val x) (φ x)
  let M (i : ι) := Γ.hadamard (distinguisherMatrix val i)
  have hslice_norm (w : EuclideanSpace ℝ X) (hw : ‖w‖ ≤ 1) :
      ∑ i : ι, ∑ x : X, (w.ofLp x * ‖querySlice i (φ x)‖) ^ 2 ≤ 1 := by
    rw [sum_comm]
    calc
      ∑ x : X, ∑ i : ι, (w.ofLp x * ‖querySlice i (φ x)‖) ^ 2
          = ∑ x : X, w.ofLp x ^ 2 * ∑ i : ι, ‖querySlice i (φ x)‖ ^ 2 :=
            sum_congr rfl fun x _ ↦ by simp only [mul_pow, ← mul_sum]
      _ = ∑ x : X, w.ofLp x ^ 2 := sum_congr rfl fun x _ ↦ by
            rw [sum_sq_norm_querySlice, norm_runValue, hψ₀, one_pow, mul_one]
      _ ≤ 1 := (EuclideanSpace.norm_le_one_iff_sum_sq_le_one w).1 hw
  have hdiff_eq : valAdvForm Γ u v φ -
      valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) (t + 1)) =
      (∑ i : ι, ∑ x, ∑ y, M i x y * u.ofLp x * v.ofLp y *
        RCLike.re (inner ℂ (querySlice i (φ x)) (querySlice i (φ y)))) -
      (∑ i : ι, ∑ x, ∑ y, M i x y * u.ofLp x * v.ofLp y *
        RCLike.re (inner ℂ (querySlice i (φ' x)) (querySlice i (φ' y)))) := by
    have hpair (x y : X) :
        RCLike.re (inner ℂ (φ x) (φ y)) -
          RCLike.re (inner ℂ (runValue step U ψ₀ (val x) (t + 1))
            (runValue step U ψ₀ (val y) (t + 1))) =
        ∑ i : ι, distinguisherMatrix val i x y *
          (RCLike.re (inner ℂ (querySlice i (φ x)) (querySlice i (φ y))) -
            RCLike.re (inner ℂ (querySlice i (φ' x)) (querySlice i (φ' y)))) := by
      change RCLike.re (inner ℂ (φ x) (φ y)) -
          RCLike.re (inner ℂ (U (t + 1) (φ' x)) (U (t + 1) (φ' y))) = _
      rw [(U (t + 1)).inner_map_map, ← map_sub,
        inner_eq_sum_inner_querySlice (φ x) (φ y),
        inner_eq_sum_inner_querySlice (φ' x) (φ' y),
        ← sum_sub_distrib, map_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [distinguisherMatrix_apply]
      by_cases hne : val x i ≠ val y i
      · simp [hne, map_sub]
      · push Not at hne
        simp only [hne, ne_eq, not_true_eq_false, ↓reduceIte, zero_mul]
        dsimp only [φ']
        rw [inner_querySlice_valueOracle_of_eq step hne (φ x) (φ y), sub_self, map_zero]
    simp only [valAdvForm, ← sum_sub_distrib, ← mul_sub, hpair, mul_sum]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp_rw [mul_sub, sum_sub_distrib]
    congr 1 <;>
      exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by
        dsimp only [M]; rw [hadamard_apply]; ring
  have hterm_le (χ : X → ValueState ι V W)
      (hχ : ∀ i x, ‖querySlice i (χ x)‖ = ‖querySlice i (φ x)‖) :
      |∑ i : ι, ∑ x, ∑ y, M i x y * u.ofLp x * v.ofLp y *
          RCLike.re (inner ℂ (querySlice i (χ x)) (querySlice i (χ y)))| ≤
        maxDistinguisherNorm val Γ := by
    calc
      |∑ i : ι, ∑ x, ∑ y, M i x y * u.ofLp x * v.ofLp y *
            RCLike.re (inner ℂ (querySlice i (χ x)) (querySlice i (χ y)))|
          ≤ ∑ i : ι, maxDistinguisherNorm val Γ *
              (√(∑ x, (u.ofLp x * ‖querySlice i (φ x)‖) ^ 2) *
                √(∑ y, (v.ofLp y * ‖querySlice i (φ y)‖) ^ 2)) :=
            (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun i _ ↦ by
              have hb := abs_sum_mul_re_inner_le (M i) u v
                (fun x ↦ querySlice i (χ x)) (fun y ↦ querySlice i (χ y))
              simp_rw [hχ i] at hb
              rw [mul_assoc] at hb
              exact hb.trans (mul_le_mul_of_nonneg_right
                (opNorm_hadamard_distinguisher_le val Γ i) (by positivity))
      _ = maxDistinguisherNorm val Γ * ∑ i : ι,
            √(∑ x, (u.ofLp x * ‖querySlice i (φ x)‖) ^ 2) *
              √(∑ y, (v.ofLp y * ‖querySlice i (φ y)‖) ^ 2) := (mul_sum _ _ _).symm
      _ ≤ maxDistinguisherNorm val Γ *
            (√(∑ i : ι, ∑ x, (u.ofLp x * ‖querySlice i (φ x)‖) ^ 2) *
              √(∑ i : ι, ∑ y, (v.ofLp y * ‖querySlice i (φ y)‖) ^ 2)) :=
            mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le univ
              (fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)
              (fun _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _)) (maxDistinguisherNorm_nonneg val Γ)
      _ ≤ maxDistinguisherNorm val Γ * (1 * 1) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.sqrt_le_one.2 (hslice_norm u hu))
                (Real.sqrt_le_one.2 (hslice_norm v hv)) (Real.sqrt_nonneg _) zero_le_one)
              (maxDistinguisherNorm_nonneg val Γ)
      _ = maxDistinguisherNorm val Γ := by ring
  rw [hdiff_eq]
  have h1 := hterm_le φ (fun _ _ ↦ rfl)
  have h2 := hterm_le φ' (fun i x ↦ norm_querySlice_valueOracle step (val x) (φ x) i)
  set s₁ := ∑ i : ι, ∑ x, ∑ y, M i x y * u.ofLp x * v.ofLp y *
    RCLike.re (inner ℂ (querySlice i (φ x)) (querySlice i (φ y)))
  set s₂ := ∑ i : ι, ∑ x, ∑ y, M i x y * u.ofLp x * v.ofLp y *
    RCLike.re (inner ℂ (querySlice i (φ' x)) (querySlice i (φ' y)))
  have habs_sub : |s₁ - s₂| ≤ |s₁| + |s₂| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le s₁ 0 s₂
  linarith

/-- **Nonnegative spectral adversary matrix inequality for unitary value-query algorithms**: if
`0 ≤ Γ` is an adversary matrix for `(val, f)` and after `T` value queries all `f`-distinguishable
pairs have overlap at most `δ`, then `(1 - δ) ‖Γ‖ ≤ 2 T · maxDistinguisherNorm val Γ`. -/
theorem one_sub_mul_opNorm_le_value {val : X → ι → G} {f : X → H} {Γ : Matrix X X ℝ}
    (hnonneg : ∀ x y, 0 ≤ Γ x y) (hΓ : IsIndexedAdversary val f Γ)
    (step : G → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) {δ : ℝ}
    (hδ : ∀ x y, f x ≠ f y →
      ‖inner ℂ (runValue step U ψ₀ (val x) T) (runValue step U ψ₀ (val y) T)‖ ≤ δ) :
    (1 - δ) * ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ ≤ 2 * T * maxDistinguisherNorm val Γ := by
  by_cases hzero : Γ = 0
  · simp [hzero]
  · have hδ0 : 0 ≤ δ := Classical.byContradiction fun hneg ↦ hzero <| ext fun x y ↦
      Classical.byContradiction fun hxy ↦
        hneg ((norm_nonneg _).trans (hδ x y (hΓ x y hxy).2))
    have hbound := opNorm_toEuclideanCLM_le_of_inner Γ
      (C := δ * ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ + 2 * T * maxDistinguisherNorm val Γ)
      (add_nonneg (mul_nonneg hδ0 (norm_nonneg _))
        (mul_nonneg (by positivity) (maxDistinguisherNorm_nonneg val Γ)))
      fun u v hu hv ↦ by
        have h0 : inner ℝ u (toEuclideanCLM (𝕜 := ℝ) Γ v) =
            valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) 0) := by
          have hinner : inner ℂ (U 0 ψ₀) (U 0 ψ₀) = (1 : ℂ) := by
            rw [LinearIsometry.inner_map_map, inner_self_eq_norm_sq_to_K, hψ₀]; norm_num
          rw [inner_toEuclideanCLM]
          simp only [valAdvForm, runValue, hinner, dotProduct, mulVec, mul_sum, RCLike.one_re]
          exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
        have htel : |inner ℝ u (toEuclideanCLM (𝕜 := ℝ) Γ v) -
            valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) T)| ≤
            2 * T * maxDistinguisherNorm val Γ := by
          rw [h0, (sum_range_sub' (fun t ↦
            valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) t)) T).symm]
          calc
            |∑ t ∈ range T, (valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) t) -
                valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) (t + 1)))|
                ≤ ∑ _t ∈ range T, 2 * maxDistinguisherNorm val Γ :=
                  (abs_sum_le_sum_abs _ _).trans <|
                    sum_le_sum fun t _ ↦ valAdvForm_step_sub_le val Γ u v hu hv step U hψ₀ t
            _ = 2 * T * maxDistinguisherNorm val Γ := by
                  simp only [sum_const, card_range, nsmul_eq_mul]; ring
        have hfin : |valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) T)| ≤
            δ * ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ := by
          calc
            |valAdvForm Γ u v (fun x ↦ runValue step U ψ₀ (val x) T)|
                ≤ ∑ x, ∑ y, Γ x y * |u.ofLp x| * |v.ofLp y| * δ :=
                  (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun x _ ↦
                    (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun y _ ↦ by
                      by_cases hxy : Γ x y = 0
                      · simp [hxy]
                      · simp only [abs_mul, abs_of_nonneg (hnonneg x y)]
                        exact mul_le_mul_of_nonneg_left
                          ((RCLike.abs_re_le_norm _).trans (hδ x y (hΓ x y hxy).2))
                          (mul_nonneg (mul_nonneg (hnonneg x y) (abs_nonneg _)) (abs_nonneg _))
            _ = δ * inner ℝ (absVec u) (toEuclideanCLM (𝕜 := ℝ) Γ (absVec v)) := by
                  rw [inner_toEuclideanCLM]
                  simp only [dotProduct, mulVec, mul_sum, absVec_apply]
                  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
            _ ≤ δ * ‖toEuclideanCLM (𝕜 := ℝ) Γ‖ :=
                  mul_le_mul_of_nonneg_left
                    ((le_abs_self _).trans (abs_inner_toEuclideanCLM_le_opNorm Γ
                      (norm_absVec_le hu) (norm_absVec_le hv))) hδ0
        linarith [(abs_le.1 htel).2, (abs_le.1 hfin).2]
    rw [sub_mul, one_mul]
    linarith

/-- **Špalek–Szegedy** (indexed form): if a `T`-query value-query algorithm
`(step, U, ψ₀)` with classical readout `out : ι × V × W → H` computes `f x` on `val x` with
error at most `ε` (`2 * ε ≤ 1`), then
`(1 - 2√(ε(1 - ε))) * indexedSpectralAdversary val f ≤ 2 * T`.
-/
theorem one_sub_two_mul_sqrt_mul_indexedSpectralAdversary_le_two_mul [DecidableEq H]
    (val : X → ι → G) (f : X → H)
    (step : G → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → H) {ε : ℝ} (hε : 2 * ε ≤ 1)
    (herr : ∀ x : X, 1 - ε ≤ measureProb (runValue step U ψ₀ (val x) T) {q | out q = f x}) :
    (1 - 2 * √(ε * (1 - ε))) * indexedSpectralAdversary val f ≤ 2 * T := by
  set c := 1 - 2 * √(ε * (1 - ε))
  rcases le_or_gt c 0 with hc0 | hcpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hc0 (indexedSpectralAdversary_nonneg val f)).trans
      (by positivity)
  · rw [← le_div_iff₀' hcpos]
    refine (indexedSpectralAdversary_le_iff (by positivity)).2 fun Γ _ hnn hΓ ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀' hcpos]
    refine one_sub_mul_opNorm_le_value hnn hΓ step U hψ₀ T fun x y hne ↦ ?_
    exact norm_inner_le_two_mul_sqrt_of_readout_ne
      (by rw [norm_runValue, hψ₀]) (by rw [norm_runValue, hψ₀])
      out hne (herr x) (herr y) hε

omit [DecidableEq G] [Fintype X] [DecidableEq X] in
/-- **Špalek–Szegedy** (domain-subset form): for any `S : Set (ι → G)`, target
`f : S → H`, and `T`-query value-query algorithm `(step, U, ψ₀)` outputting `f s` with
probability at least `1 - ε` (`2 * ε ≤ 1`) for every `s ∈ S`,
`(1 - 2√(ε(1 - ε))) * valueSpectralAdversary S f ≤ 2 * T`.
-/
theorem one_sub_two_mul_sqrt_mul_valueSpectralAdversary_le_two_mul [Finite G] [DecidableEq H]
    (S : Set (ι → G)) (f : S → H)
    (step : G → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → H) {ε : ℝ} (hε : 2 * ε ≤ 1)
    (herr : ∀ s : S, 1 - ε ≤ measureProb (runValue step U ψ₀ s.1 T) {q | out q = f s}) :
    (1 - 2 * √(ε * (1 - ε))) * valueSpectralAdversary S f ≤ 2 * T := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  have hcongr : valueSpectralAdversary S f =
      indexedSpectralAdversary (G := G) (X := S) Subtype.val f := by
    unfold valueSpectralAdversary
    congr!
  rw [hcongr]
  exact one_sub_two_mul_sqrt_mul_indexedSpectralAdversary_le_two_mul
    Subtype.val f step U hψ₀ T out hε herr

end QueryLowerBound

-- Private non-vacuity check on 1-bit identity function
private example :
    0 ≤ valueSpectralAdversary (Set.univ : Set (Unit → Bool)) (fun s ↦ s.1 ()) :=
  valueSpectralAdversary_nonneg _ _

end CslibFrontier.Quantum
