/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import CslibFrontier.Foundations.BooleanAnalysis.DiscreteProduct

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetric Markov Operators and Spectral Comparison on Product Spaces

This module formalizes symmetric Markov operators on finite state spaces, their spectral radius
bounds on the zero-mean subspace `1^⊥`, tensor-power Markov operators `T^{\otimes r}`, discrete
Bonami–Beckner noise stability `S_ρ(f)`, the spectral comparison inequality
`⟨f, T^{\otimes r} f⟩ ≥ 2 μ² - S_ρ(f)`, and the colourful `p = 1` Bonami–Beckner operator
`T_{-1/(k-1)}` under standard Lean axioms. For the colourful `p = 2` Guruswami–Sinop operator on
`[k]²`, see `CslibFrontier.Foundations.BooleanAnalysis.GuruswamiSinop`.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.IsSymmetricMarkovOperator`: symmetric, entrywise
  nonnegative, row-sum
  `1` matrix on a finite index type.
* `CslibFrontier.Foundations.BooleanAnalysis.HasMarkovSpectralRadiusBound`: `L²` operator-norm bound
  `≤ ρ` on `1^⊥`.
* `CslibFrontier.Foundations.BooleanAnalysis.IsColourfulMarkov`: colourfulness of a Markov operator
  on `[k]^p`.
* `CslibFrontier.Foundations.BooleanAnalysis.markovTensorPowApply`,
  `CslibFrontier.Foundations.BooleanAnalysis.markovTensorPowVecApply`: action of `T^{\otimes r}` on
  scalar and
  vector-valued functions.
* `CslibFrontier.Foundations.BooleanAnalysis.bonamiBeckner`,
  `CslibFrontier.Foundations.BooleanAnalysis.noiseStability`: the
  Bonami–Beckner operator `T_ρ` and discrete noise stability `S_ρ(f)`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.exists_eigenbasis_of_isSymmetricMarkov`: every
  symmetric Markov
  operator on `Fin D` (`D > 0`) with spectral radius bound `ρ ≥ 0` admits a constant-`1`
  orthonormal eigenbasis with non-zeroth eigenvalues bounded in magnitude by `ρ`.
* `CslibFrontier.Foundations.BooleanAnalysis.noiseStability_eq_sum_fourier`,
  `CslibFrontier.Foundations.BooleanAnalysis.noiseStability_eq_sum_anova`: exact Fourier and ANOVA
  formulas for
  discrete noise stability.
*
`CslibFrontier.Foundations.BooleanAnalysis.inner_markovTensorPow_ge_two_mul_sq_sub_noiseStability`,
  `CslibFrontier.Foundations.BooleanAnalysis.inner_markovTensorPow_ge_sq_sub_noiseStability`:
  spectral comparison
  inequality `⟨f, T^{\otimes r} f⟩ ≥ 2 μ² - S_ρ(f) ≥ μ² - S_ρ(f)`.
* `CslibFrontier.Foundations.BooleanAnalysis.bonamiBeckner_neg_inv_spec`: for `k ≥ 2`,
  `T_{-1/(k-1)}` is a
  colourful symmetric Markov operator with spectral radius `1 / (k - 1)`.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Foundations.BooleanAnalysis

/-! ### Symmetric Markov operators, spectral radius, and colourfulness -/

/-- A matrix `T` on a finite type `α` is a symmetric Markov operator if it is symmetric,
entrywise nonnegative, and has row sums equal to `1`. -/
@[expose] def IsSymmetricMarkovOperator {α : Type*} [Fintype α] (T : Matrix α α ℝ) : Prop :=
  T.IsSymm ∧ (∀ x y : α, 0 ≤ T x y) ∧ (∀ x : α, ∑ y : α, T x y = 1)

/-- Spectral radius bound `≤ ρ` on the zero-mean subspace `1^⊥`: for every `v` with `∑ x, v x = 0`,
`∑ x, (T *ᵥ v) x ^ 2 ≤ ρ ^ 2 * ∑ x, v x ^ 2`. -/
@[expose] def HasMarkovSpectralRadiusBound {α : Type*} [Fintype α] (T : Matrix α α ℝ) (ρ : ℝ) :
    Prop :=
  ∀ v : α → ℝ, (∑ x : α, v x = 0) →
    ∑ x : α, (T.mulVec v x) ^ 2 ≤ ρ ^ 2 * ∑ x : α, v x ^ 2

/-- Colourfulness of a Markov operator on `[k]^p` (`Fin p → Fin k`): every positive transition
connects tuples with disjoint colour sets. -/
@[expose] def IsColourfulMarkov {k p : ℕ} (T : Matrix (Fin p → Fin k) (Fin p → Fin k) ℝ) : Prop :=
  ∀ x y : Fin p → Fin k, 0 < T x y → ∀ i j : Fin p, x i ≠ y j

/-- Transport of `IsSymmetricMarkovOperator` along an equivalence of finite index types. -/
theorem IsSymmetricMarkovOperator.reindex {α β : Type*} [Fintype α] [Fintype β]
    {T : Matrix α α ℝ} (hT : IsSymmetricMarkovOperator T) (e : α ≃ β) :
    IsSymmetricMarkovOperator (Matrix.reindex e e T) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x y
    simpa [Matrix.reindex_apply, Matrix.transpose_apply] using
      congrFun (congrFun hT.1 (e.symm x)) (e.symm y)
  · intro x y
    simpa [Matrix.reindex_apply] using hT.2.1 (e.symm x) (e.symm y)
  · intro x
    simpa [Matrix.reindex_apply] using
      (Fintype.sum_equiv e.symm _ _ fun _ => rfl).trans (hT.2.2 (e.symm x))

/-- Transport of `HasMarkovSpectralRadiusBound` along an equivalence of finite index types. -/
theorem HasMarkovSpectralRadiusBound.reindex {α β : Type*} [Fintype α] [Fintype β]
    {T : Matrix α α ℝ} {ρ : ℝ} (hT : HasMarkovSpectralRadiusBound T ρ) (e : α ≃ β) :
    HasMarkovSpectralRadiusBound (Matrix.reindex e e T) ρ := by
  intro v hv
  have hv' : ∑ x : α, v (e x) = 0 := (Fintype.sum_equiv e _ _ fun _ => rfl).trans hv
  have hmul : ∀ x : β, (Matrix.reindex e e T).mulVec v x = T.mulVec (v ∘ e) (e.symm x) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply]
    exact Fintype.sum_equiv e.symm (fun i => T (e.symm x) (e.symm i) * v i)
      (fun x₁ => T (e.symm x) x₁ * v (e x₁)) (fun i => by simp)
  have h1 : ∑ x : β, ((Matrix.reindex e e T).mulVec v x) ^ 2 =
      ∑ x : α, (T.mulVec (v ∘ e) x) ^ 2 := by
    simp only [hmul]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  have h2 : ∑ x : β, v x ^ 2 = ∑ x : α, (v ∘ e) x ^ 2 :=
    (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  rw [h1, h2]
  exact hT (v ∘ e) hv'

/-- Action of the `r`-fold tensor power `T^{\otimes r}` on `f : (Fin r → Fin D) → ℝ`. -/
@[expose] noncomputable def markovTensorPowApply {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (r : ℕ)
    (f : (Fin r → Fin D) → ℝ) (x : Fin r → Fin D) : ℝ :=
  ∑ y : Fin r → Fin D, (∏ i : Fin r, T (x i) (y i)) * f y

/-- Action of `T^{\otimes r}` on vector-valued functions `f : (Fin r → Fin D) → Fin ℓ → ℝ`. -/
@[expose] noncomputable def markovTensorPowVecApply {D ℓ : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (r : ℕ) (f : (Fin r → Fin D) → Fin ℓ → ℝ) (x : Fin r → Fin D) (j : Fin ℓ) : ℝ :=
  markovTensorPowApply T r (fun y => f y j) x

/-- The Bonami–Beckner operator `T_ρ = ρ I_D + ((1 - ρ) / D) J_D` on `Fin D`. -/
@[expose] noncomputable def bonamiBeckner (D : ℕ) (ρ : ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun x y => (if x = y then ρ else 0) + (1 - ρ) / (D : ℝ)

/-- Discrete noise stability `S_ρ(f) = ⟨f, T_ρ^{\otimes r} f⟩`. -/
@[expose] noncomputable def noiseStability {D r : ℕ} (ρ : ℝ) (f : (Fin r → Fin D) → ℝ) : ℝ :=
  uniformInner f (markovTensorPowApply (bonamiBeckner D ρ) r f)

theorem markovTensorPowApply_add {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (r : ℕ)
    (f g : (Fin r → Fin D) → ℝ) :
    markovTensorPowApply T r (fun x => f x + g x) =
      fun x => markovTensorPowApply T r f x + markovTensorPowApply T r g x := by
  ext x
  simp [markovTensorPowApply, mul_add, Finset.sum_add_distrib]

theorem markovTensorPowApply_const_mul {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (r : ℕ)
    (c : ℝ) (f : (Fin r → Fin D) → ℝ) :
    markovTensorPowApply T r (fun x => c * f x) =
      fun x => c * markovTensorPowApply T r f x := by
  ext x
  simp [markovTensorPowApply, mul_left_comm, ← Finset.mul_sum]

theorem markovTensorPowApply_sum {ι : Type*} {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (r : ℕ)
    (s : Finset ι) (f : ι → (Fin r → Fin D) → ℝ) :
    markovTensorPowApply T r (fun x => ∑ i ∈ s, f i x) =
      fun x => ∑ i ∈ s, markovTensorPowApply T r (f i) x := by
  ext x
  simp only [markovTensorPowApply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem markovTensorPowApply_selfAdjoint {D : ℕ} {T : Matrix (Fin D) (Fin D) ℝ}
    (hT : T.IsSymm) (r : ℕ) (f g : (Fin r → Fin D) → ℝ) :
    uniformInner (markovTensorPowApply T r f) g =
      uniformInner f (markovTensorPowApply T r g) := by
  simp only [uniformInner, uniformExpect, markovTensorPowApply, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hsym : ∀ i, T (y i) (x i) = T (x i) (y i) := fun i => by
    have := congrFun (congrFun hT (x i)) (y i)
    simpa [Matrix.transpose_apply] using this
  simp only [hsym]
  ring

/-- Action of `T^{\otimes r}` on a product function `x ↦ ∏ i, h i (x i)`. -/
theorem markovTensorPowApply_prod {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (r : ℕ)
    (h : Fin r → Fin D → ℝ) (x : Fin r → Fin D) :
    markovTensorPowApply T r (fun y => ∏ i, h i (y i)) x =
      ∏ i, T.mulVec (h i) (x i) := by
  simp only [markovTensorPowApply, Matrix.mulVec, dotProduct, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

/-- `bonamiBeckner D 0` is a symmetric Markov operator for every `D > 0`. -/
theorem isSymmetricMarkovOperator_bonamiBeckner_zero {D : ℕ} (hD : 0 < D) :
    IsSymmetricMarkovOperator (bonamiBeckner D 0) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  refine ⟨?_, ?_, ?_⟩
  · ext x y
    simp [Matrix.transpose_apply, bonamiBeckner]
  · intro x y
    simp only [bonamiBeckner, Matrix.of_apply, sub_zero, ite_self, zero_add]
    positivity
  · intro x
    simp only [bonamiBeckner, Matrix.of_apply, sub_zero, ite_self, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hDpos.ne'

/-- `bonamiBeckner D ρ` is a symmetric Markov operator for `-1 / (D - 1) ≤ ρ ≤ 1` (`D ≥ 2`). -/
theorem isSymmetricMarkovOperator_bonamiBeckner {D : ℕ} (hD : 2 ≤ D) {ρ : ℝ}
    (hρ_lo : -1 / ((D : ℝ) - 1) ≤ ρ) (hρ_hi : ρ ≤ 1) :
    IsSymmetricMarkovOperator (bonamiBeckner D ρ) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hDm1 : (0 : ℝ) < (D : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  refine ⟨?_, ?_, ?_⟩
  · ext x y
    simp only [Matrix.transpose_apply, bonamiBeckner, Matrix.of_apply, eq_comm]
  · intro x y
    simp only [bonamiBeckner, Matrix.of_apply]
    split_ifs with h
    · have hmul : -1 ≤ ((D : ℝ) - 1) * ρ := by
        have := (div_le_iff₀ hDm1).mp hρ_lo
        linarith
      have hnum : 0 ≤ ((D : ℝ) - 1) * ρ + 1 := by linarith
      have h2 : ρ + (1 - ρ) / (D : ℝ) = (((D : ℝ) - 1) * ρ + 1) / (D : ℝ) := by
        field_simp [hDpos.ne']; ring
      rw [h2]
      exact div_nonneg hnum hDpos.le
    · rw [zero_add]
      exact div_nonneg (by linarith) hDpos.le
  · intro x
    simp only [bonamiBeckner, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hDpos.ne']
    ring

theorem bonamiBeckner_mulVec {D : ℕ} (ρ : ℝ) (v : Fin D → ℝ) (x : Fin D) :
    (bonamiBeckner D ρ).mulVec v x =
      ρ * v x + (1 - ρ) * ((∑ y : Fin D, v y) / (D : ℝ)) := by
  simp only [Matrix.mulVec, dotProduct, bonamiBeckner, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← Finset.mul_sum]
  ring

theorem bonamiBeckner_mulVec_one {D : ℕ} (hD : 0 < D) (ρ : ℝ) :
    (bonamiBeckner D ρ).mulVec (fun _ => 1) = fun _ => 1 := by
  ext x
  rw [bonamiBeckner_mulVec]
  have hD0 : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
  simp [hD0]

theorem bonamiBeckner_mulVec_of_sum_eq_zero {D : ℕ} (ρ : ℝ) {v : Fin D → ℝ}
    (hv : ∑ y : Fin D, v y = 0) :
    (bonamiBeckner D ρ).mulVec v = fun x => ρ * v x := by
  ext x
  rw [bonamiBeckner_mulVec, hv, zero_div, mul_zero, add_zero]

/-! ### Existence of a constant-`1` eigenbasis for any symmetric Markov operator -/

/-- Every symmetric Markov operator `T` on `Fin D` (`D > 0`) admits a constant-`1` orthonormal
eigenbasis whose non-zeroth eigenvalues satisfy `|λ j| ≤ ρ` whenever `T` has spectral radius bound
`ρ ≥ 0`. -/
theorem exists_eigenbasis_of_isSymmetricMarkov {D : ℕ} (hD : 0 < D)
    {T : Matrix (Fin D) (Fin D) ℝ} (hT : IsSymmetricMarkovOperator T) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hspec : HasMarkovSpectralRadiusBound T ρ) :
    ∃ (α : Fin D → Fin D → ℝ) (lam : Fin D → ℝ),
      IsOrthBasisOnFin hD α ∧
      lam ⟨0, hD⟩ = 1 ∧
      (∀ j : Fin D, j ≠ ⟨0, hD⟩ → |lam j| ≤ ρ) ∧
      (∀ j : Fin D, T.mulVec (α j) = fun x => lam j * α j x) := by
  let E := EuclideanSpace ℝ (Fin D)
  let u0 : E := WithLp.toLp 2 (fun _ : Fin D => (1 : ℝ))
  have hu0_ne : u0 ≠ 0 := by
    intro h
    have h0 := congrFun (congrArg WithLp.ofLp h) ⟨0, hD⟩
    simp [u0] at h0
  let W : Submodule ℝ E := (Submodule.span ℝ {u0})ᗮ
  have hmem_W : ∀ v : E, v ∈ W ↔ ∑ x : Fin D, v.ofLp x = 0 := by
    intro v
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hinner : @inner ℝ E _ u0 v = ∑ x : Fin D, v.ofLp x := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, u0]
    rw [hinner]
  let A : E →ₗ[ℝ] E :=
    { toFun := fun v => WithLp.toLp 2 (T.mulVec v.ofLp)
      map_add' := fun v w => by
        ext x
        exact congrFun (Matrix.mulVec_add T v.ofLp w.ofLp) x
      map_smul' := fun c v => by
        ext x
        exact congrFun (Matrix.mulVec_smul T c v.ofLp) x }
  have hA_symm : A.IsSymmetric := by
    intro v w
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    have hsym : ∀ x y, T y x = T x y := fun x y => by
      have := congrFun (congrFun hT.1 x) y
      simpa [Matrix.transpose_apply] using this
    simp only [star_trivial, A, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hsym x y]
    ring
  have hAu0 : A u0 = u0 := by
    ext x
    change (T.mulVec u0.ofLp) x = 1
    simp only [u0, Matrix.mulVec, dotProduct, mul_one]
    exact hT.2.2 x
  have hA_inv : ∀ v ∈ W, A v ∈ W := by
    intro v hv
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv ⊢
    rw [← hA_symm u0 v, hAu0, hv]
  let AW : W →ₗ[ℝ] W := A.restrict hA_inv
  have hAW_symm : AW.IsSymmetric := fun v w => hA_symm v.1 w.1
  have hfinW : Module.finrank ℝ W = D - 1 := by
    have hsum : Module.finrank ℝ (Submodule.span ℝ {u0}) + Module.finrank ℝ W =
        Module.finrank ℝ E := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {u0})
    have hspan1 : Module.finrank ℝ (Submodule.span ℝ {u0}) = 1 := finrank_span_singleton hu0_ne
    have hE : Module.finrank ℝ E = D := by simp [E]
    omega
  let b : OrthonormalBasis (Fin (D - 1)) ℝ W := hAW_symm.eigenvectorBasis hfinW
  let ev : Fin (D - 1) → ℝ := hAW_symm.eigenvalues hfinW
  let α : Fin D → Fin D → ℝ := fun j x =>
    if hj : j.1 = 0 then 1 else √(D : ℝ) * (b ⟨j.1 - 1, by omega⟩).1.ofLp x
  let lam : Fin D → ℝ := fun j =>
    if hj : j.1 = 0 then 1 else ev ⟨j.1 - 1, by omega⟩
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hα0 : ∀ y : Fin D, α ⟨0, hD⟩ y = 1 := fun y => by simp [α]
  have hlam0 : lam ⟨0, hD⟩ = 1 := by simp [lam]
  have heig : ∀ j : Fin D, T.mulVec (α j) = fun x => lam j * α j x := by
    intro j
    by_cases hj : j.1 = 0
    · ext x
      simp only [α, lam, hj, ↓reduceDIte, Matrix.mulVec, dotProduct, mul_one]
      exact hT.2.2 x
    · ext x
      have hα_eq : α j = fun y => √(D : ℝ) * (b ⟨j.1 - 1, by omega⟩).1.ofLp y := by
        ext y; simp [α, hj]
      have hlam_eq : lam j = ev ⟨j.1 - 1, by omega⟩ := by simp [lam, hj]
      rw [hα_eq, hlam_eq]
      have happly := hAW_symm.apply_eigenvectorBasis hfinW ⟨j.1 - 1, by omega⟩
      have hcoord := congrFun (congrArg (fun z : W => z.1.ofLp) happly) x
      have hmul : T.mulVec (fun y => √(D : ℝ) * (b ⟨j.1 - 1, by omega⟩).1.ofLp y) x =
          √(D : ℝ) * T.mulVec (b ⟨j.1 - 1, by omega⟩).1.ofLp x := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring
      rw [hmul]
      have hcoord' : T.mulVec (b ⟨j.1 - 1, by omega⟩).1.ofLp x =
          ev ⟨j.1 - 1, by omega⟩ * (b ⟨j.1 - 1, by omega⟩).1.ofLp x := by
        dsimp only [AW, A, b, ev] at hcoord
        exact hcoord
      rw [hcoord']
      ring
  have horth : ∀ i j : Fin D,
      (∑ y : Fin D, α i y * α j y) / (D : ℝ) = if i = j then 1 else 0 := by
    intro i j
    by_cases hi : i.1 = 0 <;> by_cases hj : j.1 = 0
    · have hij : i = j := Fin.ext (hi.trans hj.symm)
      simp only [α, hj, ↓reduceDIte, mul_one, hij, ↓reduceIte, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_self hDpos.ne']
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp only [α, hi, hj, ↓reduceDIte, one_mul, hij, ↓reduceIte, ← Finset.mul_sum]
      have hsum0 : ∑ y : Fin D, (b ⟨j.1 - 1, by omega⟩).1.ofLp y = 0 :=
        (hmem_W _).mp (b ⟨j.1 - 1, by omega⟩).2
      rw [hsum0, mul_zero, zero_div]
    · have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp only [α, hi, hj, ↓reduceDIte, mul_one, hij, ↓reduceIte, ← Finset.mul_sum]
      have hsum0 : ∑ y : Fin D, (b ⟨i.1 - 1, by omega⟩).1.ofLp y = 0 :=
        (hmem_W _).mp (b ⟨i.1 - 1, by omega⟩).2
      rw [hsum0, mul_zero, zero_div]
    · have hinner_b :
          ∑ y : Fin D, (b ⟨i.1 - 1, by omega⟩).1.ofLp y * (b ⟨j.1 - 1, by omega⟩).1.ofLp y =
          @inner ℝ W _ (b ⟨i.1 - 1, by omega⟩) (b ⟨j.1 - 1, by omega⟩) := by
        change _ = @inner ℝ E _ (b ⟨i.1 - 1, by omega⟩).1 (b ⟨j.1 - 1, by omega⟩).1
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial, dotProduct]
        refine Finset.sum_congr rfl fun y _ => mul_comm _ _
      have hsum_eq :
          ∑ y : Fin D, α i y * α j y =
          (D : ℝ) * @inner ℝ W _ (b ⟨i.1 - 1, by omega⟩) (b ⟨j.1 - 1, by omega⟩) := by
        simp only [α, hi, hj, ↓reduceDIte]
        rw [← hinner_b, Finset.mul_sum]
        have hsq : √(D : ℝ) * √(D : ℝ) = (D : ℝ) := Real.mul_self_sqrt hDpos.le
        refine Finset.sum_congr rfl fun y _ => ?_
        calc
          √(D : ℝ) * (b ⟨i.1 - 1, by omega⟩).1.ofLp y *
              (√(D : ℝ) * (b ⟨j.1 - 1, by omega⟩).1.ofLp y)
              = (√(D : ℝ) * √(D : ℝ)) *
                ((b ⟨i.1 - 1, by omega⟩).1.ofLp y * (b ⟨j.1 - 1, by omega⟩).1.ofLp y) := by ring
          _ = (D : ℝ) * ((b ⟨i.1 - 1, by omega⟩).1.ofLp y *
                (b ⟨j.1 - 1, by omega⟩).1.ofLp y) := by rw [hsq]
      rw [hsum_eq, mul_div_cancel_left₀ _ hDpos.ne', orthonormal_iff_ite.mp b.orthonormal]
      have hiff : (⟨i.1 - 1, by omega⟩ : Fin (D - 1)) = ⟨j.1 - 1, by omega⟩ ↔ i = j := by
        constructor
        · intro h
          have hval := congrArg Fin.val h
          dsimp only at hval
          exact Fin.ext (by omega)
        · intro h; subst h; rfl
      simp [hiff]
  have hlam_le : ∀ j : Fin D, j ≠ ⟨0, hD⟩ → |lam j| ≤ ρ := by
    intro j hj
    have hsum0 : ∑ x : Fin D, α j x = 0 := by
      have h := horth j ⟨0, hD⟩
      simp only [hj, ↓reduceIte, hα0, mul_one] at h
      exact (div_eq_zero_iff.mp h).resolve_right hDpos.ne'
    have hnorm : ∑ x : Fin D, α j x ^ 2 = (D : ℝ) := by
      have h := horth j j
      simp only [↓reduceIte, ← sq] at h
      exact (div_eq_one_iff_eq hDpos.ne').mp h
    have hle := hspec (α j) hsum0
    simp only [heig j, mul_pow, ← Finset.mul_sum, hnorm] at hle
    have hsq_le : lam j ^ 2 ≤ ρ ^ 2 := by nlinarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [sq_abs (lam j), sq_nonneg (lam j)]) hρ)
  exact ⟨α, lam, ⟨hα0, horth⟩, hlam0, hlam_le, heig⟩

/-- Exact Fourier formula for discrete noise stability in any constant-`1` orthonormal basis. -/
theorem noiseStability_eq_sum_fourier {D r : ℕ} (hD : 0 < D) {α : Fin D → Fin D → ℝ}
    (hα : IsOrthBasisOnFin hD α) (ρ : ℝ) (f : (Fin r → Fin D) → ℝ) :
    noiseStability ρ f =
      ∑ z : Fin r → Fin D, ρ ^ (coeffSupport z).card * fourierCoeff α f z ^ 2 := by
  have haction : ∀ z : Fin r → Fin D,
      markovTensorPowApply (bonamiBeckner D ρ) r (tensorBasis α z) =
        fun x => ρ ^ (coeffSupport z).card * tensorBasis α z x := by
    intro z
    ext x
    change markovTensorPowApply (bonamiBeckner D ρ) r (fun y => ∏ i, α (z i) (y i)) x = _
    rw [markovTensorPowApply_prod]
    have hmul : ∀ i : Fin r, (bonamiBeckner D ρ).mulVec (α (z i)) (x i) =
        (if (z i).1 ≠ 0 then ρ else 1) * α (z i) (x i) := by
      intro i
      by_cases hi : (z i).1 = 0
      · have hzi : z i = ⟨0, hD⟩ := Fin.ext hi
        simp only [ne_eq, hi, not_true_eq_false, ↓reduceIte, one_mul]
        rw [hzi]
        have h1 : α ⟨0, hD⟩ = fun _ => 1 := funext hα.1
        rw [h1, bonamiBeckner_mulVec_one hD]
      · simp only [ne_eq, hi, not_false_eq_true, ↓reduceIte]
        have hsum0 : ∑ y : Fin D, α (z i) y = 0 := by
          have h := hα.2 (z i) ⟨0, hD⟩
          have hne : z i ≠ ⟨0, hD⟩ := fun heq => hi (by simp [heq])
          simp only [hne, ↓reduceIte, hα.1, mul_one] at h
          exact (div_eq_zero_iff.mp h).resolve_right (Nat.cast_pos.mpr hD).ne'
        rw [bonamiBeckner_mulVec_of_sum_eq_zero ρ hsum0]
    simp only [hmul, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
    rfl
  rw [noiseStability]
  conv_lhs =>
    rw [show f = fun x => ∑ z, fourierCoeff α f z * tensorBasis α z x from
      funext (fourier_expansion hD hα f)]
  rw [markovTensorPowApply_sum]
  simp only [markovTensorPowApply_const_mul, haction, uniformInner_sum_left,
    uniformInner_sum_right]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single z]
  · rw [uniformInner_const_mul_left, uniformInner_const_mul_right,
      uniformInner_const_mul_right, uniformInner_tensorBasis hD hα]
    simp only [↓reduceIte]
    ring
  · intro w _ hne
    rw [uniformInner_const_mul_left, uniformInner_const_mul_right,
      uniformInner_const_mul_right, uniformInner_tensorBasis hD hα]
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ z) h

/-- Exact ANOVA formula for discrete noise stability: `S_ρ(f) = ∑_S ρ^|S| ‖f^{=S}‖₂²`. -/
theorem noiseStability_eq_sum_anova {D r : ℕ} (hD : 0 < D) (ρ : ℝ)
    (f : (Fin r → Fin D) → ℝ) :
    noiseStability ρ f = ∑ S : Finset (Fin r), ρ ^ S.card * uniformL2Sq (anovaComponent S f) := by
  classical
  have hspec0 : HasMarkovSpectralRadiusBound (bonamiBeckner D 0) 0 := by
    intro v hv
    simp [bonamiBeckner_mulVec_of_sum_eq_zero 0 hv]
  obtain ⟨α, _, hα, _, _, _⟩ :=
    exists_eigenbasis_of_isSymmetricMarkov hD (isSymmetricMarkovOperator_bonamiBeckner_zero hD)
      le_rfl hspec0
  rw [noiseStability_eq_sum_fourier hD hα]
  simp only [uniformL2Sq_anovaComponent_eq_sum_fourierCoeff hD hα, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_).symm
  · intro _ _; exact Finset.mem_univ _
  · intro ⟨S₁, z₁⟩ h₁ ⟨S₂, z₂⟩ h₂ (heq : z₁ = z₂)
    subst heq
    simp only [Finset.mem_sigma, Finset.mem_filter] at h₁ h₂
    exact Sigma.ext (h₁.2.2.symm.trans h₂.2.2) (heq_of_eq rfl)
  · intro z _
    refine ⟨⟨coeffSupport z, z⟩, ?_, rfl⟩
    simp
  · intro ⟨S, z⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    rw [hp.2.2]

/-- **Spectral Comparison Lemma** (sharp form):
for any symmetric Markov operator `T` on `Fin D` (`D > 0`) with spectral radius bound `ρ ≥ 0`
and any `f : (Fin r → Fin D) → ℝ`, `⟨f, T^{\otimes r} f⟩ ≥ 2 (E[f])² - S_ρ(f)`. -/
theorem inner_markovTensorPow_ge_two_mul_sq_sub_noiseStability {D r : ℕ} (hD : 0 < D)
    {T : Matrix (Fin D) (Fin D) ℝ} (hT : IsSymmetricMarkovOperator T) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hspec : HasMarkovSpectralRadiusBound T ρ) (f : (Fin r → Fin D) → ℝ) :
    2 * (uniformExpect f) ^ 2 - noiseStability ρ f ≤
      uniformInner f (markovTensorPowApply T r f) := by
  obtain ⟨α, lam, hα, hlam0, hlam_le, heig⟩ :=
    exists_eigenbasis_of_isSymmetricMarkov hD hT hρ0 hspec
  have haction : ∀ z : Fin r → Fin D,
      markovTensorPowApply T r (tensorBasis α z) =
        fun x => (∏ i : Fin r, lam (z i)) * tensorBasis α z x := by
    intro z
    ext x
    change markovTensorPowApply T r (fun y => ∏ i, α (z i) (y i)) x = _
    rw [markovTensorPowApply_prod]
    simp only [heig, Finset.prod_mul_distrib]
    rfl
  have hinner_T : uniformInner f (markovTensorPowApply T r f) =
      ∑ z : Fin r → Fin D, (∏ i : Fin r, lam (z i)) * fourierCoeff α f z ^ 2 := by
    conv_lhs =>
      rw [show f = fun x => ∑ z, fourierCoeff α f z * tensorBasis α z x from
        funext (fourier_expansion hD hα f)]
    rw [markovTensorPowApply_sum]
    simp only [markovTensorPowApply_const_mul, haction, uniformInner_sum_left,
      uniformInner_sum_right]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_eq_single z]
    · rw [uniformInner_const_mul_left, uniformInner_const_mul_right,
        uniformInner_const_mul_right, uniformInner_tensorBasis hD hα]
      simp only [↓reduceIte]
      ring
    · intro w _ hne
      rw [uniformInner_const_mul_left, uniformInner_const_mul_right,
        uniformInner_const_mul_right, uniformInner_tensorBasis hD hα]
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ z) h
  rw [hinner_T, noiseStability_eq_sum_fourier hD hα]
  let z0 : Fin r → Fin D := fun _ => ⟨0, hD⟩
  have hcoeff0 : fourierCoeff α f z0 = uniformExpect f := by
    simp only [fourierCoeff, uniformInner, tensorBasis, z0, hα.1, Finset.prod_const_one, mul_one]
  have hsupp0 : coeffSupport z0 = ∅ := by ext i; simp [coeffSupport, z0]
  have hterm_nn : ∀ z ∈ (Finset.univ : Finset (Fin r → Fin D)),
      0 ≤ ((∏ i : Fin r, lam (z i)) + ρ ^ (coeffSupport z).card) * fourierCoeff α f z ^ 2 := by
    intro z _
    refine mul_nonneg ?_ (sq_nonneg _)
    have habs : |∏ i : Fin r, lam (z i)| ≤ ρ ^ (coeffSupport z).card := by
      rw [Finset.abs_prod]
      calc
        ∏ i : Fin r, |lam (z i)|
            = ∏ i : Fin r, (if (z i).1 ≠ 0 then |lam (z i)| else 1) := by
              refine Finset.prod_congr rfl fun i _ => ?_
              by_cases hi : (z i).1 = 0
              · have hzi : z i = ⟨0, hD⟩ := Fin.ext hi
                simp [hzi, hlam0]
              · simp [hi]
        _ = ∏ i ∈ coeffSupport z, |lam (z i)| := by
              rw [Finset.prod_ite, Finset.prod_const_one, mul_one]; rfl
        _ ≤ ∏ _i ∈ coeffSupport z, ρ :=
              Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i hi =>
                hlam_le (z i) fun h => mem_coeffSupport.mp hi (by simp [h])
        _ = ρ ^ (coeffSupport z).card := Finset.prod_const ρ
    linarith [neg_abs_le (∏ i : Fin r, lam (z i))]
  have hsum_ge : 2 * (uniformExpect f) ^ 2 ≤
      ∑ z : Fin r → Fin D,
        ((∏ i : Fin r, lam (z i)) + ρ ^ (coeffSupport z).card) * fourierCoeff α f z ^ 2 := by
    calc
      2 * (uniformExpect f) ^ 2
          = ((∏ i : Fin r, lam (z0 i)) + ρ ^ (coeffSupport z0).card) *
              fourierCoeff α f z0 ^ 2 := by
            simp only [z0, hlam0, hsupp0, hcoeff0, Finset.prod_const_one, Finset.card_empty,
              pow_zero]
            ring
      _ ≤ ∑ z : Fin r → Fin D,
            ((∏ i : Fin r, lam (z i)) + ρ ^ (coeffSupport z).card) * fourierCoeff α f z ^ 2 :=
            Finset.single_le_sum (f := fun z =>
              ((∏ i : Fin r, lam (z i)) + ρ ^ (coeffSupport z).card) * fourierCoeff α f z ^ 2)
              hterm_nn (Finset.mem_univ z0)
  have hadd : ∑ z : Fin r → Fin D,
      ((∏ i : Fin r, lam (z i)) + ρ ^ (coeffSupport z).card) * fourierCoeff α f z ^ 2 =
      (∑ z : Fin r → Fin D, (∏ i : Fin r, lam (z i)) * fourierCoeff α f z ^ 2) +
        ∑ z : Fin r → Fin D, ρ ^ (coeffSupport z).card * fourierCoeff α f z ^ 2 := by
    simp [add_mul, Finset.sum_add_distrib]
  linarith

/-- Corollary matching the literal inequality `⟨f, T^{\otimes r} f⟩ ≥ μ² - S_ρ(f)`. -/
theorem inner_markovTensorPow_ge_sq_sub_noiseStability {D r : ℕ} (hD : 0 < D)
    {T : Matrix (Fin D) (Fin D) ℝ} (hT : IsSymmetricMarkovOperator T) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hspec : HasMarkovSpectralRadiusBound T ρ) (f : (Fin r → Fin D) → ℝ) :
    (uniformExpect f) ^ 2 - noiseStability ρ f ≤
      uniformInner f (markovTensorPowApply T r f) := by
  linarith [inner_markovTensorPow_ge_two_mul_sq_sub_noiseStability hD hT hρ0 hspec f,
    sq_nonneg (uniformExpect f)]

/-! ### Colourful `p = 1` Bonami–Beckner operator -/

/-- **Bonami–Beckner `p = 1` Colourful Operator**: for `k ≥ 2`, `T_{-1/(k-1)}` on `[k]` is a
colourful symmetric Markov operator with spectral radius `1 / (k - 1)` whose entries are
nonnegative integer multiples of `1 / (k - 1)`. -/
theorem bonamiBeckner_neg_inv_spec {k : ℕ} (hk : 2 ≤ k) :
    let T := bonamiBeckner k (-1 / ((k : ℝ) - 1))
    IsSymmetricMarkovOperator T ∧
      HasMarkovSpectralRadiusBound T (1 / ((k : ℝ) - 1)) ∧
      (∀ x y : Fin k, 0 < T x y → x ≠ y) ∧
      (∀ x y : Fin k, ∃ m : ℕ, T x y = (m : ℝ) * (1 / ((k : ℝ) - 1))) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hdiag : ∀ x : Fin k, bonamiBeckner k (-1 / ((k : ℝ) - 1)) x x = 0 := by
    intro x
    simp only [bonamiBeckner, Matrix.of_apply, ↓reduceIte]
    field_simp [hkpos.ne', hkm1.ne']
    ring
  have hoff : ∀ x y : Fin k, x ≠ y →
      bonamiBeckner k (-1 / ((k : ℝ) - 1)) x y = 1 / ((k : ℝ) - 1) := by
    intro x y hne
    simp only [bonamiBeckner, Matrix.of_apply, hne, ↓reduceIte, zero_add]
    field_simp [hkpos.ne', hkm1.ne']
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isSymmetricMarkovOperator_bonamiBeckner hk le_rfl (by
      have : -1 / ((k : ℝ) - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hkm1.le
      linarith)
  · intro v hv
    rw [bonamiBeckner_mulVec_of_sum_eq_zero _ hv]
    simp only [mul_pow, ← Finset.mul_sum]
    have hsq : (-1 / ((k : ℝ) - 1)) ^ 2 = (1 / ((k : ℝ) - 1)) ^ 2 := by ring
    rw [hsq]
  · intro x y hpos hxy
    subst hxy
    linarith [hdiag x]
  · intro x y
    by_cases h : x = y
    · subst h; exact ⟨0, by simp [hdiag x]⟩
    · exact ⟨1, by simp [hoff x y h]⟩

end CslibFrontier.Foundations.BooleanAnalysis
