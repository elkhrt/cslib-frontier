/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery
public import CslibFrontier.Foundations.Quantum.Measurement.Readout

import CslibFrontier.Foundations.Quantum.Measurement.Overlap
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Bounded-Error Quantum Value-Query Complexity

Defines the bounded-error quantum value-query complexity model over arbitrary finite query index
types `ι` and alphabets `α`, building directly on `Cslib.Quantum.ValueState`,
`Cslib.Quantum.runValue`, and `Cslib.Quantum.measureOut` under standard Lean axioms.

To support uniform complexity statements including degenerate empty-domain (`n = 0`) and
empty-alphabet (`k = 0`) boundary cases where `EuclideanSpace ℂ (ι × V × W)` would be
zero-dimensional, query algorithms operate on `Option ι` where `none` is an idle (no-op) slot and
`some i` queries `x i`. Whenever `Nonempty ι`, an explicit sector-splitting equivalence identifies
this model query-for-query (with identical query count `T` and identical error `ε`) with
`Cslib.Quantum.runValue` on `Cslib.Quantum.ValueState ι _ _`.

## Main definitions

* `CslibFrontier.Quantum.idleStep`: lifts a per-symbol unitary step on `α` to `Option α` by
  acting as the identity on `none`.
* `CslibFrontier.Quantum.swapStep`: canonical involutive value-oracle step on `Option α`
  swapping `none` and `some a`.
* `CslibFrontier.Quantum.QuantumValueAlg`: bundled pure unitary `T`-query quantum value-query
  algorithm with finite value/workspace registers, unit initial state, and classical readout.
* `CslibFrontier.Quantum.ComputesWithin`, `CslibFrontier.Quantum.ComputesTotal`: existence of
  a `T`-query algorithm computing a partial (promise) or total function within error `ε`.
* `CslibFrontier.Quantum.promiseQuantumQueryComplexity`,
  `CslibFrontier.Quantum.promiseBoundedQuantumQueryComplexity`,
  `CslibFrontier.Quantum.quantumQueryComplexity`,
  `CslibFrontier.Quantum.boundedQuantumQueryComplexity`: minimal query counts at error `ε` and at
  standard bounded error `1 / 3`.

## Main results

* `CslibFrontier.Quantum.orthonormalSwap`: explicit involutive unitary exchanging two mutually
  orthogonal orthonormal families in any complex Hilbert space.
* `CslibFrontier.Quantum.computesWithin_iff_exists_runValue`: exact `T`-query equivalence with
  `Cslib.Quantum.runValue` whenever `Nonempty ι`.
* `CslibFrontier.Quantum.QuantumValueAlg.toSwapStep`: any `T`-query algorithm with an arbitrary
  unitary oracle `step` is simulated identically in `2 * T` queries by the involutive `swapStep`
  oracle.
* `CslibFrontier.Quantum.promiseQuantumQueryComplexity_le_of_computesWithin`: upper-bounding
  quantum query complexity from an explicit `QuantumValueAlg` witness.
-/

public section

namespace CslibFrontier.Quantum

open Finset
open scoped BigOperators
/-! ### 1. Orthonormal subspace swap unitary and fiber helpers -/

section OrthonormalSwap

variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private noncomputable def orthonormalSwapRaw (u v : κ → E) (ψ : E) : E :=
  ψ + ∑ k : κ, inner ℂ (u k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (v k) ψ • (u k - v k)

private theorem orthonormalSwapRaw_add (u v : κ → E) (x y : E) :
    orthonormalSwapRaw u v (x + y) = orthonormalSwapRaw u v x + orthonormalSwapRaw u v y := by
  simp only [orthonormalSwapRaw, inner_add_right, add_smul, sum_add_distrib]
  abel

private theorem orthonormalSwapRaw_smul (u v : κ → E) (c : ℂ) (x : E) :
    orthonormalSwapRaw u v (c • x) = c • orthonormalSwapRaw u v x := by
  simp only [orthonormalSwapRaw, inner_smul_right, mul_smul, smul_add, ← smul_sum]

private theorem inner_orthonormalSwapRaw_u {u v : κ → E} (hu : Orthonormal ℂ u)
    (huv : ∀ i j, inner ℂ (u i) (v j) = 0) (j : κ) (ψ : E) :
    inner ℂ (u j) (orthonormalSwapRaw u v ψ) = inner ℂ (v j) ψ := by
  classical
  simp only [orthonormalSwapRaw, inner_add_right, inner_sum, inner_smul_right, inner_sub_right,
    orthonormal_iff_ite.mp hu, huv, zero_sub, sub_zero, mul_neg, mul_ite, mul_one, mul_zero,
    sum_neg_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  ring

private theorem inner_orthonormalSwapRaw_v {u v : κ → E} (hv : Orthonormal ℂ v)
    (huv : ∀ i j, inner ℂ (u i) (v j) = 0) (j : κ) (ψ : E) :
    inner ℂ (v j) (orthonormalSwapRaw u v ψ) = inner ℂ (u j) ψ := by
  classical
  have hvu : ∀ j k, inner ℂ (v j) (u k) = 0 := fun j k ↦ by
    rw [← inner_conj_symm, huv k j, map_zero]
  simp only [orthonormalSwapRaw, inner_add_right, inner_sum, inner_smul_right, inner_sub_right,
    orthonormal_iff_ite.mp hv, hvu, zero_sub, sub_zero, mul_neg, mul_ite, mul_one, mul_zero,
    sum_neg_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  ring

private theorem orthonormalSwapRaw_involutive {u v : κ → E} (hu : Orthonormal ℂ u)
    (hv : Orthonormal ℂ v) (huv : ∀ i j, inner ℂ (u i) (v j) = 0) (ψ : E) :
    orthonormalSwapRaw u v (orthonormalSwapRaw u v ψ) = ψ := by
  set φ := orthonormalSwapRaw u v ψ
  change φ + ∑ k : κ, inner ℂ (u k) φ • (v k - u k) + ∑ k : κ, inner ℂ (v k) φ • (u k - v k) = ψ
  simp only [φ, inner_orthonormalSwapRaw_u hu huv, inner_orthonormalSwapRaw_v hv huv]
  dsimp only [orthonormalSwapRaw]
  have hcancel :
      (∑ k : κ, inner ℂ (u k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (v k) ψ • (u k - v k)) +
        (∑ k : κ, inner ℂ (v k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (u k) ψ • (u k - v k)) = 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun k _ ↦ ?_
    module
  have hassoc :
      ψ + ∑ k : κ, inner ℂ (u k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (v k) ψ • (u k - v k) +
        ∑ k : κ, inner ℂ (v k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (u k) ψ • (u k - v k) =
      ψ + ((∑ k : κ, inner ℂ (u k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (v k) ψ • (u k - v k)) +
        (∑ k : κ, inner ℂ (v k) ψ • (v k - u k) + ∑ k : κ, inner ℂ (u k) ψ • (u k - v k))) := by
    abel
  rw [hassoc, hcancel, add_zero]

private theorem inner_orthonormalSwapRaw_symm (u v : κ → E) (φ ψ : E) :
    inner ℂ (orthonormalSwapRaw u v φ) ψ = inner ℂ φ (orthonormalSwapRaw u v ψ) := by
  simp only [orthonormalSwapRaw, inner_add_left, inner_add_right, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  have h1 : ∀ a : E, starRingEnd ℂ (inner ℂ a φ) = inner ℂ φ a := fun a ↦ inner_conj_symm φ a
  simp only [h1]
  rw [add_assoc, add_assoc]
  congr 1
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-- Explicit involutive linear isometry exchanging two mutually orthogonal orthonormal families
`u` and `v` (`u k ↦ v k`, `v k ↦ u k`) while fixing their joint orthogonal complement. -/
noncomputable def orthonormalSwap {u v : κ → E} (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (huv : ∀ i j, inner ℂ (u i) (v j) = 0) : E ≃ₗᵢ[ℂ] E where
  toFun := orthonormalSwapRaw u v
  invFun := orthonormalSwapRaw u v
  map_add' := orthonormalSwapRaw_add u v
  map_smul' := orthonormalSwapRaw_smul u v
  left_inv := orthonormalSwapRaw_involutive hu hv huv
  right_inv := orthonormalSwapRaw_involutive hu hv huv
  norm_map' ψ := by
    have hsq : ‖orthonormalSwapRaw u v ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ,
        inner_orthonormalSwapRaw_symm, orthonormalSwapRaw_involutive hu hv huv]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

@[simp]
theorem orthonormalSwap_u {u v : κ → E} (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (huv : ∀ i j, inner ℂ (u i) (v j) = 0) (j : κ) :
    orthonormalSwap hu hv huv (u j) = v j := by
  classical
  change orthonormalSwapRaw u v (u j) = v j
  have hvu : ∀ k, inner ℂ (v k) (u j) = 0 := fun k ↦ by
    rw [← inner_conj_symm, huv j k, map_zero]
  simp only [orthonormalSwapRaw, hvu, zero_smul, sum_const_zero, add_zero]
  rw [sum_eq_single j]
  · simp [hu.1 j]
  · intro k _ hkj
    simp [orthonormal_iff_ite.mp hu, hkj]
  · intro h; exact absurd (mem_univ j) h

@[simp]
theorem orthonormalSwap_symm {u v : κ → E} (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (huv : ∀ i j, inner ℂ (u i) (v j) = 0) :
    (orthonormalSwap hu hv huv).symm = orthonormalSwap hu hv huv := by
  rfl

end OrthonormalSwap

section FiberHelpers

/-- Reindexing linear isometric equivalence on `EuclideanSpace ℂ` along `e : P ≃ Q`. -/
@[expose] noncomputable def reindexSpace {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ Q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp]
theorem reindexSpace_apply {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q)
    (ψ : EuclideanSpace ℂ P) (q : Q) :
    (reindexSpace e ψ).ofLp q = ψ.ofLp (e.symm q) :=
  rfl

@[simp]
theorem reindexSpace_symm_apply {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q)
    (ψ : EuclideanSpace ℂ Q) (p : P) :
    ((reindexSpace e).symm ψ).ofLp p = ψ.ofLp (e p) := by
  simp [reindexSpace]

/-- Applies a family of linear isometries `F : A → (ℂ^B →ₗᵢ[ℂ] ℂ^B)` fiberwise on `A × B`. -/
noncomputable def fiberIsometry {A B : Type*} [Fintype A] [Fintype B]
    (F : A → (EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B)) :
    EuclideanSpace ℂ (A × B) →ₗᵢ[ℂ] EuclideanSpace ℂ (A × B) where
  toFun ψ := WithLp.toLp 2 fun p ↦ (F p.1 (WithLp.toLp 2 fun b ↦ ψ.ofLp (p.1, b))).ofLp p.2
  map_add' x y := by
    ext ⟨a, b⟩
    change (F a (WithLp.toLp 2 fun b' ↦ x.ofLp (a, b') + y.ofLp (a, b'))).ofLp b = _
    have hxy : (WithLp.toLp 2 fun b' ↦ x.ofLp (a, b') + y.ofLp (a, b')) =
        (WithLp.toLp 2 fun b' ↦ x.ofLp (a, b')) + (WithLp.toLp 2 fun b' ↦ y.ofLp (a, b')) := rfl
    rw [hxy, map_add]
    rfl
  map_smul' c x := by
    ext ⟨a, b⟩
    change (F a (WithLp.toLp 2 fun b' ↦ c * x.ofLp (a, b'))).ofLp b = _
    have hcx : (WithLp.toLp 2 fun b' ↦ c * x.ofLp (a, b')) =
        c • (WithLp.toLp 2 fun b' ↦ x.ofLp (a, b')) := rfl
    rw [hcx, map_smul]
    rfl
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun p : A × B ↦
        (F p.1 (WithLp.toLp 2 fun b ↦ ψ.ofLp (p.1, b))).ofLp p.2 :
          EuclideanSpace ℂ (A × B))‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ ↦ ?_
      have hFa := (F a).norm_map (WithLp.toLp 2 fun b ↦ ψ.ofLp (a, b))
      have hFa2 : ‖F a (WithLp.toLp 2 fun b ↦ ψ.ofLp (a, b))‖ ^ 2 =
          ‖(WithLp.toLp 2 fun b ↦ ψ.ofLp (a, b) : EuclideanSpace ℂ B)‖ ^ 2 := by rw [hFa]
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hFa2
      exact hFa2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

@[simp]
theorem fiberIsometry_apply {A B : Type*} [Fintype A] [Fintype B]
    (F : A → (EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B))
    (ψ : EuclideanSpace ℂ (A × B)) (a : A) (b : B) :
    (fiberIsometry F ψ).ofLp (a, b) =
      (F a (WithLp.toLp 2 fun b' ↦ ψ.ofLp (a, b'))).ofLp b := by
  rfl

/-- Applies a family of linear isometric equivalences fiberwise over a dependent `Sigma` type. -/
noncomputable def sigmaEquiv {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)]
    (F : ∀ a : A, EuclideanSpace ℂ (B a) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (B a)) :
    EuclideanSpace ℂ (Σ a : A, B a) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Σ a : A, B a) where
  toFun ψ := WithLp.toLp 2 fun p ↦ (F p.1 (WithLp.toLp 2 fun b ↦ ψ.ofLp ⟨p.1, b⟩)).ofLp p.2
  invFun ψ := WithLp.toLp 2 fun p ↦
    ((F p.1).symm (WithLp.toLp 2 fun b ↦ ψ.ofLp ⟨p.1, b⟩)).ofLp p.2
  map_add' x y := by
    ext ⟨a, b⟩
    have hxy : (WithLp.toLp 2 fun b' ↦ x.ofLp ⟨a, b'⟩ + y.ofLp ⟨a, b'⟩) =
        (WithLp.toLp 2 fun b' ↦ x.ofLp ⟨a, b'⟩) + (WithLp.toLp 2 fun b' ↦ y.ofLp ⟨a, b'⟩) := rfl
    change (F a (WithLp.toLp 2 fun b' ↦ x.ofLp ⟨a, b'⟩ + y.ofLp ⟨a, b'⟩)).ofLp b = _
    rw [hxy, map_add]
    rfl
  map_smul' c x := by
    ext ⟨a, b⟩
    have hcx : (WithLp.toLp 2 fun b' ↦ c * x.ofLp ⟨a, b'⟩) =
        c • (WithLp.toLp 2 fun b' ↦ x.ofLp ⟨a, b'⟩) := rfl
    change (F a (WithLp.toLp 2 fun b' ↦ c * x.ofLp ⟨a, b'⟩)).ofLp b = _
    rw [hcx, map_smul]
    rfl
  left_inv ψ := by
    ext ⟨a, b⟩
    change ((F a).symm (F a (WithLp.toLp 2 fun b' ↦ ψ.ofLp ⟨a, b'⟩))).ofLp b = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  right_inv ψ := by
    ext ⟨a, b⟩
    change (F a ((F a).symm (WithLp.toLp 2 fun b' ↦ ψ.ofLp ⟨a, b'⟩))).ofLp b = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun p : Σ a : A, B a ↦
        (F p.1 (WithLp.toLp 2 fun b ↦ ψ.ofLp ⟨p.1, b⟩)).ofLp p.2 :
          EuclideanSpace ℂ (Σ a : A, B a))‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_sigma, Fintype.sum_sigma]
      refine sum_congr rfl fun a _ ↦ ?_
      have hFa := (F a).norm_map (WithLp.toLp 2 fun b ↦ ψ.ofLp ⟨a, b⟩)
      have hFa2 : ‖F a (WithLp.toLp 2 fun b ↦ ψ.ofLp ⟨a, b⟩)‖ ^ 2 =
          ‖(WithLp.toLp 2 fun b ↦ ψ.ofLp ⟨a, b⟩ : EuclideanSpace ℂ (B a))‖ ^ 2 := by rw [hFa]
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hFa2
      exact hFa2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

@[simp]
theorem sigmaEquiv_apply {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)]
    (F : ∀ a : A, EuclideanSpace ℂ (B a) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (B a))
    (ψ : EuclideanSpace ℂ (Σ a : A, B a)) (a : A) (b : B a) :
    (sigmaEquiv F ψ).ofLp ⟨a, b⟩ =
      (F a (WithLp.toLp 2 fun b' ↦ ψ.ofLp ⟨a, b'⟩)).ofLp b := by
  rfl

/-- Direct sum of two linear isometric equivalences on `EuclideanSpace ℂ (V₁ ⊕ V₂)`. -/
noncomputable def sumEquiv {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (e₁ : EuclideanSpace ℂ V₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ V₁)
    (e₂ : EuclideanSpace ℂ V₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ V₂) :
    EuclideanSpace ℂ (V₁ ⊕ V₂) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (V₁ ⊕ V₂) where
  toFun ψ := WithLp.toLp 2 fun s ↦ match s with
    | Sum.inl v₁ => (e₁ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u))).ofLp v₁
    | Sum.inr v₂ => (e₂ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u))).ofLp v₂
  invFun ψ := WithLp.toLp 2 fun s ↦ match s with
    | Sum.inl v₁ => (e₁.symm (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u))).ofLp v₁
    | Sum.inr v₂ => (e₂.symm (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u))).ofLp v₂
  map_add' x y := by
    ext (v₁ | v₂)
    · have h : (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inl u) + y.ofLp (Sum.inl u)) =
          (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inl u)) +
            (WithLp.toLp 2 fun u ↦ y.ofLp (Sum.inl u)) := rfl
      change (e₁ (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inl u) + y.ofLp (Sum.inl u))).ofLp v₁ = _
      rw [h, map_add]; rfl
    · have h : (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inr u) + y.ofLp (Sum.inr u)) =
          (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inr u)) +
            (WithLp.toLp 2 fun u ↦ y.ofLp (Sum.inr u)) := rfl
      change (e₂ (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inr u) + y.ofLp (Sum.inr u))).ofLp v₂ = _
      rw [h, map_add]; rfl
  map_smul' c x := by
    ext (v₁ | v₂)
    · have h : (WithLp.toLp 2 fun u ↦ c * x.ofLp (Sum.inl u)) =
          c • (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inl u)) := rfl
      change (e₁ (WithLp.toLp 2 fun u ↦ c * x.ofLp (Sum.inl u))).ofLp v₁ = _
      rw [h, map_smul]; rfl
    · have h : (WithLp.toLp 2 fun u ↦ c * x.ofLp (Sum.inr u)) =
          c • (WithLp.toLp 2 fun u ↦ x.ofLp (Sum.inr u)) := rfl
      change (e₂ (WithLp.toLp 2 fun u ↦ c * x.ofLp (Sum.inr u))).ofLp v₂ = _
      rw [h, map_smul]; rfl
  left_inv ψ := by
    ext (v₁ | v₂)
    · change (e₁.symm (e₁ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u)))).ofLp v₁ = _
      rw [LinearIsometryEquiv.symm_apply_apply]
    · change (e₂.symm (e₂ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u)))).ofLp v₂ = _
      rw [LinearIsometryEquiv.symm_apply_apply]
  right_inv ψ := by
    ext (v₁ | v₂)
    · change (e₁ (e₁.symm (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u)))).ofLp v₁ = _
      rw [LinearIsometryEquiv.apply_symm_apply]
    · change (e₂ (e₂.symm (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u)))).ofLp v₂ = _
      rw [LinearIsometryEquiv.apply_symm_apply]
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 (fun s : V₁ ⊕ V₂ ↦ match s with
        | Sum.inl v₁ => (e₁ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u))).ofLp v₁
        | Sum.inr v₂ => (e₂ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u))).ofLp v₂) :
          EuclideanSpace ℂ (V₁ ⊕ V₂))‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_sum_type, Fintype.sum_sum_type]
      have h1 := e₁.norm_map (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u))
      have h2 := e₂.norm_map (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u))
      have h1' : ‖e₁ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u))‖ ^ 2 =
          ‖(WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u) : EuclideanSpace ℂ V₁)‖ ^ 2 := by rw [h1]
      have h2' : ‖e₂ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u))‖ ^ 2 =
          ‖(WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u) : EuclideanSpace ℂ V₂)‖ ^ 2 := by rw [h2]
      simp only [EuclideanSpace.norm_sq_eq] at h1' h2'
      linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

@[simp]
theorem sumEquiv_apply_inl {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (e₁ : EuclideanSpace ℂ V₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ V₁)
    (e₂ : EuclideanSpace ℂ V₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ V₂)
    (ψ : EuclideanSpace ℂ (V₁ ⊕ V₂)) (v₁ : V₁) :
    (sumEquiv e₁ e₂ ψ).ofLp (Sum.inl v₁) =
      (e₁ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inl u))).ofLp v₁ := by
  rfl

@[simp]
theorem sumEquiv_apply_inr {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (e₁ : EuclideanSpace ℂ V₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ V₁)
    (e₂ : EuclideanSpace ℂ V₂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ V₂)
    (ψ : EuclideanSpace ℂ (V₁ ⊕ V₂)) (v₂ : V₂) :
    (sumEquiv e₁ e₂ ψ).ofLp (Sum.inr v₂) =
      (e₂ (WithLp.toLp 2 fun u ↦ ψ.ofLp (Sum.inr u))).ofLp v₂ := by
  rfl

end FiberHelpers

/-! ### 2. Value-query algorithms and bounded-error quantum query complexity -/

/-- Lifts a per-symbol unitary step `step : α → (ℂ^V ≃ₗᵢ[ℂ] ℂ^V)` to `Option α` by acting as the
identity unitary on the idle symbol `none`. -/
@[expose] noncomputable def idleStep {α V : Type*} [Fintype V]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) :
    Option α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)
  | none => LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ V)
  | some a => step a

@[simp]
theorem idleStep_none {α V : Type*} [Fintype V]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) :
    idleStep step none = LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ V) :=
  rfl

@[simp]
theorem idleStep_some {α V : Type*} [Fintype V]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) (a : α) :
    idleStep step (some a) = step a :=
  rfl

/-- Canonical involutive permutation step on `Option α`, acting as identity on `none` and swapping
`none` with `some a` on `some a`. -/
@[expose] noncomputable def swapStep {α : Type*} [Fintype α] [DecidableEq α] :
    Option α → (EuclideanSpace ℂ (Option α) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Option α)) :=
  idleStep (Cslib.Quantum.permStep fun a : α ↦ Equiv.swap none (some a))

@[simp]
theorem swapStep_none {α : Type*} [Fintype α] [DecidableEq α] :
    swapStep (α := α) none = LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ (Option α)) :=
  rfl

@[simp]
theorem swapStep_some {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    swapStep (some a) = Cslib.Quantum.permStep (fun b : α ↦ Equiv.swap none (some b)) a :=
  rfl

/-- `swapStep o` is self-inverse for every `o : Option α`. -/
theorem swapStep_involutive {α : Type*} [Fintype α] [DecidableEq α] (o : Option α)
    (φ : EuclideanSpace ℂ (Option α)) :
    swapStep o (swapStep o φ) = φ := by
  cases o with
  | none => rfl
  | some a =>
    ext u
    simp [swapStep, idleStep, Cslib.Quantum.permStep_apply]

/-- Value oracle under `swapStep` is self-inverse. -/
theorem valueOracle_swapStep_involutive {ι α W : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Fintype W] (x : Option ι → Option α)
    (ψ : Cslib.Quantum.ValueState (Option ι) (Option α) W) :
    Cslib.Quantum.valueOracle swapStep x (Cslib.Quantum.valueOracle swapStep x ψ) = ψ := by
  ext ⟨oi, v, w⟩
  simp only [Cslib.Quantum.valueOracle_apply]
  have h := congrArg (fun u : EuclideanSpace ℂ (Option α) ↦ u.ofLp v)
    (swapStep_involutive (x oi) (WithLp.toLp 2 fun v' ↦ ψ.ofLp (oi, v', w)))
  simpa using h

/-- Addition law for `Cslib.Quantum.runValue` across two sequential stages `T + s`. -/
theorem runValue_add {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    {U U' : ℕ → Cslib.Quantum.ValueState ι V W →ₗᵢ[ℂ] Cslib.Quantum.ValueState ι V W} {T : ℕ}
    (h0 : U' 0 = LinearIsometry.id) (hsucc : ∀ r, U' (r + 1) = U (T + r + 1))
    (ψ₀ : Cslib.Quantum.ValueState ι V W) (x : ι → α) (s : ℕ) :
    Cslib.Quantum.runValue step U ψ₀ x (T + s) =
      Cslib.Quantum.runValue step U' (Cslib.Quantum.runValue step U ψ₀ x T) x s := by
  induction s with
  | zero => simp [Cslib.Quantum.runValue, h0]
  | succ s ih =>
    rw [Nat.add_succ, Cslib.Quantum.runValue, Cslib.Quantum.runValue, ← ih, hsucc s]

/-- Congruence of `Cslib.Quantum.runValue` when unitary schedules agree up to step `t`. -/
theorem runValue_congr {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    {U U' : ℕ → Cslib.Quantum.ValueState ι V W →ₗᵢ[ℂ] Cslib.Quantum.ValueState ι V W} {t : ℕ}
    (h : ∀ s ≤ t, U s = U' s) (ψ₀ : Cslib.Quantum.ValueState ι V W) (x : ι → α) :
    Cslib.Quantum.runValue step U ψ₀ x t = Cslib.Quantum.runValue step U' ψ₀ x t := by
  induction t with
  | zero => simp [Cslib.Quantum.runValue, h 0 (Nat.zero_le _)]
  | succ t ih =>
    simp only [Cslib.Quantum.runValue, ih fun s hs ↦ h s (Nat.le_succ_of_le hs),
      h (t + 1) (le_refl _)]

/-- A pure unitary quantum value-query algorithm over finite query index set `ι`, input alphabet
`α`, and output type `β`. -/
structure QuantumValueAlg (ι : Type*) [Fintype ι] (α β : Type*) where
  /-- Finite value register type. -/
  V : Type
  /-- Finite workspace register type. -/
  W : Type
  /-- Finiteness of `V`. -/
  instFintypeV : Fintype V
  /-- Finiteness of `W`. -/
  instFintypeW : Fintype W
  /-- Total number of oracle queries executed. -/
  queries : ℕ
  /-- Per-symbol unitary step on `ℂ^V`. -/
  step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)
  /-- Inter-query unitaries `U_0, ..., U_queries`. -/
  unitary : ℕ → Cslib.Quantum.ValueState (Option ι) V W →ₗᵢ[ℂ]
    Cslib.Quantum.ValueState (Option ι) V W
  /-- Initial unit-norm quantum state. -/
  init : Cslib.Quantum.ValueState (Option ι) V W
  /-- Proof that `init` has unit Euclidean norm. -/
  norm_init : ‖init‖ = 1
  /-- Classical readout decoding computational basis outcomes to `β`. -/
  readout : Option ι × V × W → β

attribute [instance] QuantumValueAlg.instFintypeV QuantumValueAlg.instFintypeW

namespace QuantumValueAlg

variable {ι α β γ : Type*} [Fintype ι]

/-- State of `A` after `t` oracle queries on input `x : ι → α`. -/
@[expose] noncomputable def stateAt (A : QuantumValueAlg ι α β) (x : ι → α) (t : ℕ) :
    Cslib.Quantum.ValueState (Option ι) A.V A.W :=
  Cslib.Quantum.runValue (idleStep A.step) A.unitary A.init (Option.map x) t

@[simp]
theorem stateAt_zero (A : QuantumValueAlg ι α β) (x : ι → α) :
    A.stateAt x 0 = A.unitary 0 A.init :=
  rfl

theorem stateAt_succ (A : QuantumValueAlg ι α β) (x : ι → α) (t : ℕ) :
    A.stateAt x (t + 1) =
      A.unitary (t + 1)
        (Cslib.Quantum.valueOracle (idleStep A.step) (Option.map x) (A.stateAt x t)) :=
  rfl

theorem stateAt_eq_runValue (A : QuantumValueAlg ι α β) (x : ι → α) (t : ℕ) :
    A.stateAt x t =
      Cslib.Quantum.runValue (idleStep A.step) A.unitary A.init (Option.map x) t :=
  rfl

/-- Final state of `A` after `A.queries` oracle queries on input `x : ι → α`. -/
@[expose] noncomputable def finalState (A : QuantumValueAlg ι α β) (x : ι → α) :
    Cslib.Quantum.ValueState (Option ι) A.V A.W :=
  A.stateAt x A.queries

theorem finalState_eq_stateAt (A : QuantumValueAlg ι α β) (x : ι → α) :
    A.finalState x = A.stateAt x A.queries :=
  rfl

/-- Every intermediate state of `A` has unit norm. -/
theorem norm_stateAt (A : QuantumValueAlg ι α β) (x : ι → α) (t : ℕ) :
    ‖A.stateAt x t‖ = 1 := by
  rw [stateAt, Cslib.Quantum.norm_runValue, A.norm_init]

/-- The final state of `A` has unit norm. -/
theorem norm_finalState (A : QuantumValueAlg ι α β) (x : ι → α) :
    ‖A.finalState x‖ = 1 :=
  A.norm_stateAt x A.queries

/-- Output probability mass function of `A` on input `x : ι → α`. -/
@[expose] noncomputable def outputPMF (A : QuantumValueAlg ι α β) (x : ι → α) : PMF β :=
  Cslib.Quantum.measureOut (A.finalState x) (A.norm_finalState x) A.readout

theorem outputPMF_eq_measureOut (A : QuantumValueAlg ι α β) (x : ι → α) :
    A.outputPMF x =
      Cslib.Quantum.measureOut (A.finalState x) (A.norm_finalState x) A.readout :=
  rfl

/-- Probability in `ℝ` that `A` outputs `b` on input `x`. -/
@[expose] noncomputable def acceptProb (A : QuantumValueAlg ι α β) (x : ι → α) (b : β) : ℝ :=
  (A.outputPMF x b).toReal

theorem acceptProb_eq_toReal (A : QuantumValueAlg ι α β) (x : ι → α) (b : β) :
    A.acceptProb x b = (A.outputPMF x b).toReal :=
  rfl

/-- `acceptProb` equals `Cslib.Quantum.measureProb` of the readout fiber over `b`. -/
theorem acceptProb_eq_measureProb (A : QuantumValueAlg ι α β) (x : ι → α) (b : β) :
    A.acceptProb x b =
      Cslib.Quantum.measureProb (A.finalState x)
        (by classical exact univ.filter fun q ↦ A.readout q = b) := by
  classical
  rw [acceptProb, outputPMF, Cslib.Quantum.measureOut_eq_ofReal_measureProb]
  exact ENNReal.toReal_ofReal (Cslib.Quantum.measureProb_nonneg _ _)

/-- `0 ≤ A.acceptProb x b`. -/
theorem acceptProb_nonneg (A : QuantumValueAlg ι α β) (x : ι → α) (b : β) :
    0 ≤ A.acceptProb x b :=
  ENNReal.toReal_nonneg

/-- `A.acceptProb x b ≤ 1`. -/
theorem acceptProb_le_one (A : QuantumValueAlg ι α β) (x : ι → α) (b : β) :
    A.acceptProb x b ≤ 1 := by
  rw [acceptProb_eq_measureProb]
  exact (Cslib.Quantum.measureProb_le_measureProb_univ _ _).trans_eq
    (by rw [Cslib.Quantum.measureProb_univ, A.norm_finalState, one_pow])

/-- Deterministic post-processing of the output of `A` without extra queries. -/
noncomputable def mapOutput (A : QuantumValueAlg ι α β) (g : β → γ) :
    QuantumValueAlg ι α γ where
  V := A.V
  W := A.W
  instFintypeV := A.instFintypeV
  instFintypeW := A.instFintypeW
  queries := A.queries
  step := A.step
  unitary := A.unitary
  init := A.init
  norm_init := A.norm_init
  readout := g ∘ A.readout

@[simp]
theorem queries_mapOutput (A : QuantumValueAlg ι α β) (g : β → γ) :
    (A.mapOutput g).queries = A.queries := by
  rfl

@[simp]
theorem outputPMF_mapOutput (A : QuantumValueAlg ι α β) (g : β → γ) (x : ι → α) :
    (A.mapOutput g).outputPMF x = (A.outputPMF x).map g := by
  simp only [outputPMF, mapOutput, finalState, stateAt, Cslib.Quantum.measureOut_map]
  rfl

/-- Pads `A` to `T'` queries (`A.queries ≤ T'`) by tagging the value register `A.V ⊕ A.V` so that
the `Sum.inr` sector ignores subsequent oracle queries. -/
noncomputable def padQueries (A : QuantumValueAlg ι α β) {T' : ℕ} (_hT : A.queries ≤ T') :
    QuantumValueAlg ι α β :=
  let liftU (f : Cslib.Quantum.ValueState (Option ι) A.V A.W →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W →ₗᵢ[ℂ]
        Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    let e : (Option ι × (A.V ⊕ A.V) × A.W) ≃ Bool × (Option ι × A.V × A.W) :=
      { toFun := fun ⟨oi, s, w⟩ ↦ match s with
          | Sum.inl v => (false, oi, v, w)
          | Sum.inr v => (true, oi, v, w)
        invFun := fun ⟨b, oi, v, w⟩ ↦ (oi, if b then Sum.inr v else Sum.inl v, w)
        left_inv := fun ⟨_, s, _⟩ ↦ by cases s <;> rfl
        right_inv := fun ⟨b, _, _, _⟩ ↦ by cases b <;> rfl }
    (reindexSpace e).symm.toLinearIsometry.comp
      ((fiberIsometry fun b : Bool ↦ if b then LinearIsometry.id else f).comp
        (reindexSpace e).toLinearIsometry)
  let flipSector : Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W ≃ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    reindexSpace
      { toFun := fun ⟨oi, s, w⟩ ↦ (oi, s.swap, w)
        invFun := fun ⟨oi, s, w⟩ ↦ (oi, s.swap, w)
        left_inv := fun ⟨_, s, _⟩ ↦ by simp
        right_inv := fun ⟨_, s, _⟩ ↦ by simp }
  let initEmb : Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    WithLp.toLp 2 fun ⟨oi, s, w⟩ ↦ match s with
      | Sum.inl v => A.init.ofLp (oi, v, w)
      | Sum.inr _ => 0
  have hnorm : ‖initEmb‖ = 1 := by
    have hsq : ‖initEmb‖ ^ 2 = ‖A.init‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [initEmb, Fintype.sum_prod_type, Fintype.sum_sum_type, norm_zero, sq, mul_zero,
        sum_const_zero, add_zero]
    rw [A.norm_init, one_pow] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [sq] using hsq)
  { V := A.V ⊕ A.V
    W := A.W
    instFintypeV := inferInstance
    instFintypeW := A.instFintypeW
    queries := T'
    step := fun a ↦ sumEquiv (A.step a) (LinearIsometryEquiv.refl ℂ _)
    unitary := fun s ↦
      if s < A.queries then liftU (A.unitary s)
      else if s = A.queries then
        if A.queries = T' then liftU (A.unitary s)
        else flipSector.toLinearIsometry.comp (liftU (A.unitary s))
      else LinearIsometry.id
    init := initEmb
    norm_init := hnorm
    readout := fun ⟨oi, s, w⟩ ↦ match s with
      | Sum.inl v => A.readout (oi, v, w)
      | Sum.inr v => A.readout (oi, v, w) }

@[simp]
theorem queries_padQueries (A : QuantumValueAlg ι α β) {T' : ℕ} (_hT : A.queries ≤ T') :
    (A.padQueries _hT).queries = T' := by
  rfl

/-- `padQueries` preserves `outputPMF` identically on every input `x`. -/
theorem outputPMF_padQueries (A : QuantumValueAlg ι α β) {T' : ℕ} (hT : A.queries ≤ T')
    (x : ι → α) :
    (A.padQueries hT).outputPMF x = A.outputPMF x := by
  let ePad : (Option ι × (A.V ⊕ A.V) × A.W) ≃ Bool × (Option ι × A.V × A.W) :=
    { toFun := fun ⟨oi, s, w⟩ ↦ match s with
        | Sum.inl v => (false, oi, v, w)
        | Sum.inr v => (true, oi, v, w)
      invFun := fun ⟨b, oi, v, w⟩ ↦ (oi, if b then Sum.inr v else Sum.inl v, w)
      left_inv := fun ⟨_, s, _⟩ ↦ by cases s <;> rfl
      right_inv := fun ⟨b, _, _, _⟩ ↦ by cases b <;> rfl }
  let liftU (f : Cslib.Quantum.ValueState (Option ι) A.V A.W →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W →ₗᵢ[ℂ]
        Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    (reindexSpace ePad).symm.toLinearIsometry.comp
      ((fiberIsometry fun b : Bool ↦ if b then LinearIsometry.id else f).comp
        (reindexSpace ePad).toLinearIsometry)
  let flipSector : Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W ≃ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    reindexSpace
      { toFun := fun ⟨oi, s, w⟩ ↦ (oi, s.swap, w)
        invFun := fun ⟨oi, s, w⟩ ↦ (oi, s.swap, w)
        left_inv := fun ⟨_, s, _⟩ ↦ by simp
        right_inv := fun ⟨_, s, _⟩ ↦ by simp }
  let stepPad (a : α) : EuclideanSpace ℂ (A.V ⊕ A.V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A.V ⊕ A.V) :=
    sumEquiv (A.step a) (LinearIsometryEquiv.refl ℂ _)
  let uPad (s : ℕ) : Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    if s < A.queries then liftU (A.unitary s)
    else if s = A.queries then
      if A.queries = T' then liftU (A.unitary s)
      else flipSector.toLinearIsometry.comp (liftU (A.unitary s))
    else LinearIsometry.id
  let embedInl (ψ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    WithLp.toLp 2 fun ⟨oi, s, w⟩ ↦ match s with
      | Sum.inl v => ψ.ofLp (oi, v, w)
      | Sum.inr _ => 0
  let embedInr (ψ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      Cslib.Quantum.ValueState (Option ι) (A.V ⊕ A.V) A.W :=
    WithLp.toLp 2 fun ⟨oi, s, w⟩ ↦ match s with
      | Sum.inl _ => 0
      | Sum.inr v => ψ.ofLp (oi, v, w)
  let outPad (p : Option ι × (A.V ⊕ A.V) × A.W) : β :=
    match p.2.1 with
    | Sum.inl v => A.readout (p.1, v, p.2.2)
    | Sum.inr v => A.readout (p.1, v, p.2.2)
  have hlift_inl (f : Cslib.Quantum.ValueState (Option ι) A.V A.W →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) A.V A.W)
      (ψ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      liftU f (embedInl ψ) = embedInl (f ψ) := by
    ext ⟨oi, v | v, w⟩
    · simp [liftU, ePad, embedInl]
    · have hz : (WithLp.toLp 2 fun _ : Option ι × A.V × A.W ↦ (0 : ℂ)) = 0 := rfl
      simp [liftU, ePad, embedInl, hz]
  have hflip_inl (ψ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      flipSector (embedInl ψ) = embedInr ψ := by
    ext ⟨oi, v | v, w⟩ <;> simp [flipSector, embedInl, embedInr]
  have horacle_inl (ψ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      Cslib.Quantum.valueOracle (idleStep stepPad) (Option.map x) (embedInl ψ) =
        embedInl (Cslib.Quantum.valueOracle (idleStep A.step) (Option.map x) ψ) := by
    ext ⟨oi, v | v, w⟩
    · cases oi <;> simp [embedInl, stepPad, Cslib.Quantum.valueOracle_apply]
    · cases oi with
      | none => simp [embedInl, stepPad, Cslib.Quantum.valueOracle_apply]
      | some i =>
        have hz : (WithLp.toLp 2 fun _ : A.V ↦ (0 : ℂ)) = 0 := rfl
        simp [embedInl, stepPad, Cslib.Quantum.valueOracle_apply, hz]
  have horacle_inr (ψ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
      Cslib.Quantum.valueOracle (idleStep stepPad) (Option.map x) (embedInr ψ) =
        embedInr ψ := by
    ext ⟨oi, v | v, w⟩
    · cases oi with
      | none => simp [embedInr, stepPad, Cslib.Quantum.valueOracle_apply]
      | some i =>
        have hz : (WithLp.toLp 2 fun _ : A.V ↦ (0 : ℂ)) = 0 := rfl
        simp [embedInr, stepPad, Cslib.Quantum.valueOracle_apply, hz]
    · cases oi <;> simp [embedInr, stepPad, Cslib.Quantum.valueOracle_apply]
  have hrun_eq : (A.padQueries hT).outputPMF x =
      Cslib.Quantum.measureOut
        (Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x) T')
        (by
          rw [Cslib.Quantum.norm_runValue]
          exact (A.padQueries hT).norm_init)
        outPad := by
    simp only [outputPMF, finalState, stateAt, padQueries]
    rfl
  rw [hrun_eq]
  by_cases hEq : A.queries = T'
  · have hstate : ∀ t ≤ A.queries,
        Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x) t =
          embedInl (A.stateAt x t) := by
      intro t ht
      induction t with
      | zero =>
        rw [Cslib.Quantum.runValue, A.stateAt_zero]
        by_cases h0 : 0 < A.queries
        · simp [uPad, h0, hlift_inl]
        · have h0eq : 0 = A.queries := by omega
          simp [uPad, h0eq, hEq, hlift_inl]
      | succ t ih =>
        rw [Cslib.Quantum.runValue, ih (Nat.le_of_succ_le ht), horacle_inl, A.stateAt_succ]
        by_cases hlt : t + 1 < A.queries
        · simp [uPad, hlt, hlift_inl]
        · have heqt : t + 1 = A.queries := by omega
          simp [uPad, heqt, hEq, hlift_inl]
    have hfin : Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x) T' =
        embedInl (A.finalState x) := by
      rw [← hEq, finalState_eq_stateAt]
      exact hstate A.queries (le_refl _)
    ext b
    classical
    rw [outputPMF, Cslib.Quantum.measureOut_eq_ofReal_measureProb,
      Cslib.Quantum.measureOut_eq_ofReal_measureProb]
    congr 1
    rw [hfin, Cslib.Quantum.measureProb, Cslib.Quantum.measureProb,
      Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun oi _ ↦ ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_sum_type]
    have hzero : ∑ v : A.V, ∑ w : A.W,
        (if outPad (oi, Sum.inr v, w) = b then
          ‖(embedInl (A.finalState x)).ofLp (oi, Sum.inr v, w)‖ ^ 2 else 0) = 0 := by
      refine sum_eq_zero fun v _ ↦ sum_eq_zero fun w _ ↦ ?_
      simp [embedInl]
    rw [hzero, add_zero]
  · have hltT : A.queries < T' := lt_of_le_of_ne hT hEq
    have hstate_lt : ∀ t < A.queries,
        Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x) t =
          embedInl (A.stateAt x t) := by
      intro t ht
      induction t with
      | zero =>
        rw [Cslib.Quantum.runValue, A.stateAt_zero]
        simp [uPad, ht, hlift_inl]
      | succ t ih =>
        rw [Cslib.Quantum.runValue, ih (Nat.lt_of_succ_lt ht), horacle_inl, A.stateAt_succ]
        simp [uPad, ht, hlift_inl]
    have hstate_eq :
        Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x) A.queries =
          embedInr (A.finalState x) := by
      cases hq : A.queries with
      | zero =>
        rw [Cslib.Quantum.runValue, finalState_eq_stateAt, hq, A.stateAt_zero]
        have h0ne : 0 ≠ T' := by omega
        simp [uPad, hq, h0ne, hlift_inl, hflip_inl]
      | succ q =>
        rw [Cslib.Quantum.runValue, hstate_lt q (by omega), horacle_inl,
          finalState_eq_stateAt, hq, A.stateAt_succ]
        have h2 : q + 1 = A.queries := hq.symm
        simp [uPad, h2, hEq, hlift_inl, hflip_inl]
    have hstate_gt : ∀ r,
        Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x)
          (A.queries + r) = embedInr (A.finalState x) := by
      intro r
      induction r with
      | zero => simpa using hstate_eq
      | succ r ih =>
        rw [Nat.add_succ, Cslib.Quantum.runValue, ih, horacle_inr]
        have h1 : ¬ A.queries + r + 1 < A.queries := by omega
        have h2 : ¬ A.queries + r + 1 = A.queries := by omega
        simp [uPad, h1, h2]
    have hfin : Cslib.Quantum.runValue (idleStep stepPad) uPad (embedInl A.init) (Option.map x) T' =
        embedInr (A.finalState x) := by
      rw [show T' = A.queries + (T' - A.queries) by omega]
      exact hstate_gt (T' - A.queries)
    ext b
    classical
    rw [outputPMF, Cslib.Quantum.measureOut_eq_ofReal_measureProb,
      Cslib.Quantum.measureOut_eq_ofReal_measureProb]
    congr 1
    rw [hfin, Cslib.Quantum.measureProb, Cslib.Quantum.measureProb,
      Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun oi _ ↦ ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_sum_type]
    have hzero : ∑ v : A.V, ∑ w : A.W,
        (if outPad (oi, Sum.inl v, w) = b then
          ‖(embedInr (A.finalState x)).ofLp (oi, Sum.inl v, w)‖ ^ 2 else 0) = 0 := by
      refine sum_eq_zero fun v _ ↦ sum_eq_zero fun w _ ↦ ?_
      simp [embedInr]
    rw [hzero, zero_add]

private noncomputable def swapUnitary {V₀ : Type} [Fintype V₀]
    (eα : α ≃ V₀) (A : QuantumValueAlg ι α β) (s : ℕ) :
    Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) :=
  let eMid : (Option ι × Option V₀ × (A.V × A.W)) ≃ ((Option ι × Option V₀ × A.W) × A.V) :=
    { toFun := fun ⟨oi, ok, v, w⟩ ↦ ((oi, ok, w), v)
      invFun := fun ⟨⟨oi, ok, w⟩, v⟩ ↦ (oi, ok, v, w)
      left_inv := fun ⟨_, _, _, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _, _⟩, _⟩ ↦ rfl }
  let applyStep : Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) :=
    (reindexSpace eMid).symm.toLinearIsometry.comp
      ((fiberIsometry fun p : Option ι × Option V₀ × A.W ↦
          (idleStep A.step (p.2.1.map eα.symm)).toLinearIsometry).comp
        (reindexSpace eMid).toLinearIsometry)
  let eLift : (Option ι × Option V₀ × (A.V × A.W)) ≃ (Option V₀ × (Option ι × A.V × A.W)) :=
    { toFun := fun ⟨oi, ok, v, w⟩ ↦ (ok, oi, v, w)
      invFun := fun ⟨ok, oi, v, w⟩ ↦ (oi, ok, v, w)
      left_inv := fun ⟨_, _, _, _⟩ ↦ rfl
      right_inv := fun ⟨_, _, _, _⟩ ↦ rfl }
  let liftU (t : ℕ) : Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) →ₗᵢ[ℂ]
      Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) :=
    (reindexSpace eLift).symm.toLinearIsometry.comp
      ((fiberIsometry fun _ : Option V₀ ↦ A.unitary t).comp
        (reindexSpace eLift).toLinearIsometry)
  if s = 0 then liftU 0
  else if s % 2 = 1 then applyStep
  else liftU (s / 2)

private noncomputable def swapEmbedNone (V₀ : Type) {V W : Type}
    (ψ : Cslib.Quantum.ValueState (Option ι) V W) :
    Cslib.Quantum.ValueState (Option ι) (Option V₀) (V × W) :=
  WithLp.toLp 2 fun ⟨oi, ok, v, w⟩ ↦ if ok = none then ψ.ofLp (oi, v, w) else 0

private def swapReadout (V₀ : Type) (A : QuantumValueAlg ι α β) :
    Option ι × Option V₀ × (A.V × A.W) → β :=
  fun ⟨oi, _, v, w⟩ ↦ A.readout (oi, v, w)

private theorem norm_swapEmbedNone_init {V₀ : Type} [Fintype V₀]
    (A : QuantumValueAlg ι α β) :
    ‖swapEmbedNone V₀ A.init‖ = 1 := by
  have hsq : ‖swapEmbedNone V₀ A.init‖ ^ 2 = ‖A.init‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun oi _ ↦ ?_
    rw [Fintype.sum_prod_type, Fintype.sum_option]
    have hsome : ∑ k : V₀, ∑ vw : A.V × A.W,
        ‖(swapEmbedNone V₀ A.init).ofLp (oi, some k, vw)‖ ^ 2 = 0 := by
      refine sum_eq_zero fun k _ ↦ sum_eq_zero fun vw _ ↦ ?_
      simp [swapEmbedNone]
    rw [hsome, add_zero, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ ?_
    simp [swapEmbedNone]
  rw [A.norm_init, one_pow] at hsq
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [sq] using hsq)

private theorem measureOut_swapUnitary {V₀ : Type} [Fintype V₀] [DecidableEq V₀]
    (eα : α ≃ V₀) (A : QuantumValueAlg ι α β) (x : ι → α) :
    Cslib.Quantum.measureOut
      (Cslib.Quantum.runValue swapStep (swapUnitary eα A) (swapEmbedNone V₀ A.init)
        (Option.map (fun i ↦ eα (x i))) (2 * A.queries))
      (by rw [Cslib.Quantum.norm_runValue, norm_swapEmbedNone_init])
      (swapReadout V₀ A) = A.outputPMF x := by
  have htwo : ∀ t : ℕ,
      Cslib.Quantum.runValue swapStep (swapUnitary eα A) (swapEmbedNone V₀ A.init)
        (Option.map (fun i ↦ eα (x i))) (2 * t) = swapEmbedNone V₀ (A.stateAt x t) := by
    intro t
    induction t with
    | zero =>
      ext ⟨oi, ok, v, w⟩
      by_cases hok : ok = none
      · subst hok
        simp [Cslib.Quantum.runValue, swapUnitary, swapEmbedNone, A.stateAt_zero]
      · have hz : (WithLp.toLp 2 fun _ : Option ι × A.V × A.W ↦ (0 : ℂ)) = 0 := rfl
        simp [Cslib.Quantum.runValue, swapUnitary, swapEmbedNone, hok, hz]
    | succ t ih =>
      have h2t : 2 * (t + 1) = (2 * t + 1) + 1 := by ring
      rw [h2t, Cslib.Quantum.runValue, Cslib.Quantum.runValue, ih]
      set ψ := A.stateAt x t
      have hmid : swapUnitary eα A (2 * t + 1)
          (Cslib.Quantum.valueOracle swapStep
            (Option.map (fun i ↦ eα (x i))) (swapEmbedNone V₀ ψ)) =
          WithLp.toLp 2 (fun ⟨oi, ok, v, w⟩ ↦
            if ok = Option.map (fun i ↦ eα (x i)) oi then
              (Cslib.Quantum.valueOracle (idleStep A.step) (Option.map x) ψ).ofLp (oi, v, w)
            else 0) := by
        have hodd1 : 2 * t + 1 ≠ 0 := by omega
        have hodd2 : (2 * t + 1) % 2 = 1 := by omega
        have hor1 : Cslib.Quantum.valueOracle swapStep (Option.map (fun i ↦ eα (x i)))
            (swapEmbedNone V₀ ψ) =
            WithLp.toLp 2 (fun ⟨oi, ok, v, w⟩ ↦
              if ok = Option.map (fun i ↦ eα (x i)) oi then ψ.ofLp (oi, v, w) else 0) := by
          ext ⟨oi, ok, v, w⟩
          cases oi with
          | none =>
            simp [Cslib.Quantum.valueOracle_apply, swapStep, idleStep, swapEmbedNone]
          | some i =>
            simp only [Option.map_some, Cslib.Quantum.valueOracle_apply, swapStep, idleStep_some,
              Cslib.Quantum.permStep_apply, Equiv.symm_swap, swapEmbedNone]
            by_cases hok : ok = some (eα (x i))
            · subst hok; simp
            · have hne : Equiv.swap none (some (eα (x i))) ok ≠ none := fun h ↦
                hok (by simpa using congrArg (Equiv.swap none (some (eα (x i)))) h)
              simp [hok, hne]
        rw [hor1]
        ext ⟨oi, ok, v, w⟩
        simp only [swapUnitary, hodd1, ↓reduceIte, hodd2, LinearIsometry.coe_comp,
          Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry, reindexSpace_symm_apply]
        by_cases hok : ok = Option.map (fun i ↦ eα (x i)) oi
        · subst hok
          have hmap_symm : (Option.map (fun i ↦ eα (x i)) oi).map eα.symm = Option.map x oi := by
            cases oi <;> simp
          simp [hmap_symm, Cslib.Quantum.valueOracle_apply]
        · have hz : (WithLp.toLp 2 fun _ : A.V ↦ (0 : ℂ)) = 0 := rfl
          simp [hok, hz]
      set φ := Cslib.Quantum.valueOracle (idleStep A.step) (Option.map x) ψ
      let midVec : Cslib.Quantum.ValueState (Option ι) (Option V₀) (A.V × A.W) :=
        WithLp.toLp 2 fun ⟨oi, ok, v, w⟩ ↦
          if ok = Option.map (fun i ↦ eα (x i)) oi then φ.ofLp (oi, v, w) else 0
      change _ = midVec at hmid
      rw [hmid]
      have hor2 : Cslib.Quantum.valueOracle swapStep (Option.map (fun i ↦ eα (x i))) midVec =
          swapEmbedNone V₀ φ := by
        ext ⟨oi, ok, v, w⟩
        cases oi with
        | none => simp [Cslib.Quantum.valueOracle_apply, swapStep, idleStep, midVec, swapEmbedNone]
        | some i =>
          simp only [Option.map_some, Cslib.Quantum.valueOracle_apply, swapStep, idleStep_some,
            Cslib.Quantum.permStep_apply, Equiv.symm_swap, midVec, swapEmbedNone]
          by_cases hok : ok = none
          · subst hok; simp
          · have hne : Equiv.swap none (some (eα (x i))) ok ≠ some (eα (x i)) := fun h ↦
              hok (by simpa using congrArg (Equiv.swap none (some (eα (x i)))) h)
            simp [hok, hne]
      rw [hor2]
      have hev2 : ¬ ((2 * t + 1) + 1) % 2 = 1 := by omega
      have hev3 : ((2 * t + 1) + 1) / 2 = t + 1 := by omega
      have hφ_eta : (WithLp.toLp 2 fun b' : Option ι × A.V × A.W ↦
          φ.ofLp (b'.1, b'.2.1, b'.2.2)) = φ := rfl
      ext ⟨oi, ok, v, w⟩
      by_cases hok : ok = none
      · subst hok
        simp [swapUnitary, hev2, hev3, A.stateAt_succ, swapEmbedNone, hφ_eta]
        rfl
      · have hz : (WithLp.toLp 2 fun _ : Option ι × A.V × A.W ↦ (0 : ℂ)) = 0 := rfl
        simp [swapUnitary, hev2, hev3, swapEmbedNone, hok, hz]
  ext b
  classical
  rw [outputPMF, Cslib.Quantum.measureOut_eq_ofReal_measureProb,
    Cslib.Quantum.measureOut_eq_ofReal_measureProb]
  congr 1
  rw [htwo A.queries, Cslib.Quantum.measureProb, Cslib.Quantum.measureProb,
    Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun oi _ ↦ ?_
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  have hsome : ∑ k : V₀, ∑ vw : A.V × A.W,
      (if swapReadout V₀ A (oi, some k, vw) = b then
        ‖(swapEmbedNone V₀ (A.stateAt x A.queries)).ofLp (oi, some k, vw)‖ ^ 2 else 0) = 0 := by
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun vw _ ↦ ?_
    simp [swapEmbedNone]
  rw [hsome, add_zero, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ ?_
  simp [swapEmbedNone, swapReadout, finalState]

/-- Explicit `swapStep` schedule extraction along any equivalence `eα : α ≃ V₀` onto a `Type`
register `V₀`. -/
theorem exists_swapStep_equiv {V₀ : Type} [Fintype V₀] [DecidableEq V₀] (eα : α ≃ V₀)
    (A : QuantumValueAlg ι α β) :
    ∃ (W' : Type) (_ : Fintype W')
      (U' : ℕ → Cslib.Quantum.ValueState (Option ι) (Option V₀) W' →ₗᵢ[ℂ]
        Cslib.Quantum.ValueState (Option ι) (Option V₀) W')
      (init' : Cslib.Quantum.ValueState (Option ι) (Option V₀) W')
      (hinit' : ‖init'‖ = 1)
      (out' : Option ι × Option V₀ × W' → β),
      ∀ x : ι → α,
        Cslib.Quantum.measureOut
          (Cslib.Quantum.runValue swapStep U' init'
            (Option.map (fun i ↦ eα (x i))) (2 * A.queries))
          (by rw [Cslib.Quantum.norm_runValue, hinit']) out' = A.outputPMF x :=
  ⟨A.V × A.W, inferInstance, swapUnitary eα A, swapEmbedNone V₀ A.init,
    norm_swapEmbedNone_init A, swapReadout V₀ A, measureOut_swapUnitary eα A⟩

/-- Explicit `swapStep` schedule extraction for `A` on `Option (Fin (Fintype.card α))`. -/
theorem exists_swapStep [Fintype α] (A : QuantumValueAlg ι α β) :
    ∃ (W' : Type) (_ : Fintype W')
      (U' : ℕ → Cslib.Quantum.ValueState (Option ι) (Option (Fin (Fintype.card α))) W' →ₗᵢ[ℂ]
        Cslib.Quantum.ValueState (Option ι) (Option (Fin (Fintype.card α))) W')
      (init' : Cslib.Quantum.ValueState (Option ι) (Option (Fin (Fintype.card α))) W')
      (hinit' : ‖init'‖ = 1)
      (out' : Option ι × Option (Fin (Fintype.card α)) × W' → β),
      ∀ x : ι → α,
        Cslib.Quantum.measureOut
          (Cslib.Quantum.runValue swapStep U' init'
            (Option.map (fun i ↦ Fintype.equivFin α (x i))) (2 * A.queries))
          (by rw [Cslib.Quantum.norm_runValue, hinit']) out' = A.outputPMF x :=
  A.exists_swapStep_equiv (Fintype.equivFin α)

/-- Converts any `T`-query `QuantumValueAlg` over a finite alphabet `α` into an equivalent
`(2 * T)`-query algorithm whose value register is `Option (Fin (Fintype.card α))` and whose oracle
step swaps `none` with `some (Fintype.equivFin α a)`. -/
noncomputable def toSwapStep [Fintype α] (A : QuantumValueAlg ι α β) :
    QuantumValueAlg ι α β where
  V := Option (Fin (Fintype.card α))
  W := A.V × A.W
  instFintypeV := inferInstance
  instFintypeW := inferInstance
  queries := 2 * A.queries
  step a := Cslib.Quantum.permStep (fun k ↦ Equiv.swap none (some k)) (Fintype.equivFin α a)
  unitary := swapUnitary (Fintype.equivFin α) A
  init := swapEmbedNone (Fin (Fintype.card α)) A.init
  norm_init := norm_swapEmbedNone_init A
  readout := swapReadout (Fin (Fintype.card α)) A

@[simp]
theorem queries_toSwapStep [Fintype α] (A : QuantumValueAlg ι α β) :
    A.toSwapStep.queries = 2 * A.queries := by
  rfl

/-- `toSwapStep` preserves `outputPMF` identically on every input `x`. -/
theorem outputPMF_toSwapStep [Fintype α] (A : QuantumValueAlg ι α β) (x : ι → α) :
    A.toSwapStep.outputPMF x = A.outputPMF x := by
  let Kα := Fin (Fintype.card α)
  let eα : α ≃ Kα := Fintype.equivFin α
  have hrun_eq : ∀ t : ℕ,
      Cslib.Quantum.runValue
        (idleStep fun a ↦ Cslib.Quantum.permStep (fun k : Kα ↦ Equiv.swap none (some k)) (eα a))
        (swapUnitary eα A) (swapEmbedNone Kα A.init) (Option.map x) t =
      Cslib.Quantum.runValue swapStep (swapUnitary eα A) (swapEmbedNone Kα A.init)
        (Option.map (fun i ↦ eα (x i))) t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Cslib.Quantum.runValue, Cslib.Quantum.runValue, ih]
      congr 1
      ext ⟨oi, ok, v, w⟩
      cases oi <;> simp [Cslib.Quantum.valueOracle_apply, swapStep]
  have hout : A.toSwapStep.outputPMF x =
      Cslib.Quantum.measureOut
        (Cslib.Quantum.runValue swapStep (swapUnitary eα A) (swapEmbedNone Kα A.init)
          (Option.map (fun i ↦ eα (x i))) (2 * A.queries))
        (by rw [Cslib.Quantum.norm_runValue, norm_swapEmbedNone_init])
        (swapReadout Kα A) := by
    simp only [outputPMF, finalState, stateAt, toSwapStep]
    congr 1
    exact hrun_eq (2 * A.queries)
  rw [hout]
  exact measureOut_swapUnitary eα A x

end QuantumValueAlg

/-! ### 3. Bounded-error complexity definitions and exact equivalence with `Cslib.Quantum` -/

section ComplexityDefs

variable {ι α β : Type*} [Fintype ι]

/-- `ComputesWithin P f T ε` holds if some `T`-query pure unitary quantum value-query algorithm
outputs `f x` with probability at least `1 - ε` on every input `x : ι → α` satisfying `P x`. -/
@[expose]
def ComputesWithin (P : (ι → α) → Prop) (f : (ι → α) → β) (T : ℕ) (ε : ℝ) : Prop :=
  ∃ A : QuantumValueAlg ι α β, A.queries = T ∧ ∀ x, P x → 1 - ε ≤ A.acceptProb x (f x)

/-- `ComputesTotal f T ε` holds if some `T`-query quantum value-query algorithm computes `f` on
every input `x : ι → α` with error probability at most `ε`. -/
@[expose]
def ComputesTotal (f : (ι → α) → β) (T : ℕ) (ε : ℝ) : Prop :=
  ComputesWithin (fun _ ↦ True) f T ε

/-- Query monotonicity: `T ≤ T'` preserves `ComputesWithin`. -/
theorem ComputesWithin.mono_queries {P : (ι → α) → Prop} {f : (ι → α) → β} {T T' : ℕ} {ε : ℝ}
    (h : ComputesWithin P f T ε) (hT : T ≤ T') : ComputesWithin P f T' ε := by
  obtain ⟨A, rfl, hA⟩ := h
  refine ⟨A.padQueries hT, rfl, fun x hx ↦ ?_⟩
  rw [QuantumValueAlg.acceptProb, A.outputPMF_padQueries]
  exact hA x hx

/-- Error monotonicity: `ε ≤ ε'` preserves `ComputesWithin`. -/
theorem ComputesWithin.mono_error {P : (ι → α) → Prop} {f : (ι → α) → β} {T : ℕ} {ε ε' : ℝ}
    (h : ComputesWithin P f T ε) (hε : ε ≤ ε') : ComputesWithin P f T ε' := by
  obtain ⟨A, hq, hA⟩ := h
  exact ⟨A, hq, fun x hx ↦ (by linarith : 1 - ε' ≤ 1 - ε).trans (hA x hx)⟩

/-- Promise antimonotonicity: restricting the promise domain preserves `ComputesWithin`. -/
theorem ComputesWithin.mono_promise {P P' : (ι → α) → Prop} {f : (ι → α) → β} {T : ℕ} {ε : ℝ}
    (h : ComputesWithin P' f T ε) (hP : ∀ x, P x → P' x) : ComputesWithin P f T ε := by
  obtain ⟨A, hq, hA⟩ := h
  exact ⟨A, hq, fun x hx ↦ hA x (hP x hx)⟩

/-- Whenever `Nonempty ι`, `ComputesWithin P f T ε` is equivalent at the exact same query count `T`
and error `ε` to the existence of a `Cslib.Quantum.runValue` algorithm on `ValueState ι V W`. -/
theorem computesWithin_iff_exists_runValue [Nonempty ι] (P : (ι → α) → Prop) (f : (ι → α) → β)
    (T : ℕ) (ε : ℝ) :
    ComputesWithin P f T ε ↔
      ∃ (V W : Type) (_ : Fintype V) (_ : Fintype W)
        (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
        (U : ℕ → Cslib.Quantum.ValueState ι V W →ₗᵢ[ℂ] Cslib.Quantum.ValueState ι V W)
        (ψ₀ : Cslib.Quantum.ValueState ι V W) (hψ₀ : ‖ψ₀‖ = 1) (out : ι × V × W → β),
        ∀ x, P x → 1 - ε ≤
          (Cslib.Quantum.measureOut (Cslib.Quantum.runValue step U ψ₀ x T)
            (by rw [Cslib.Quantum.norm_runValue, hψ₀]) out (f x)).toReal := by
  constructor
  · rintro ⟨A, rfl, hA⟩
    classical
    let i₀ : ι := Classical.arbitrary ι
    let Rest := {i : ι // i ≠ i₀} × A.V × A.W
    let eSplit : (ι × (A.V ⊕ A.V) × A.W) ≃ (Option ι × A.V × A.W) ⊕ Rest :=
      { toFun := fun ⟨i, s, w⟩ ↦ match s with
          | Sum.inl v => Sum.inl (some i, v, w)
          | Sum.inr v =>
            if h : i = i₀ then Sum.inl (none, v, w) else Sum.inr (⟨i, h⟩, v, w)
        invFun := fun u ↦ match u with
          | Sum.inl (some i, v, w) => (i, Sum.inl v, w)
          | Sum.inl (none, v, w) => (i₀, Sum.inr v, w)
          | Sum.inr (⟨i, _⟩, v, w) => (i, Sum.inr v, w)
        left_inv := fun ⟨i, s, w⟩ ↦ by
          cases s with
          | inl v => rfl
          | inr v =>
            by_cases hi : i = i₀ <;> simp [hi]
        right_inv := fun u ↦ by
          cases u with
          | inl p =>
            rcases p with ⟨oi, v, w⟩
            cases oi <;> simp
          | inr r =>
            rcases r with ⟨⟨i, hi⟩, v, w⟩
            simp [hi] }
    let liftOp (g : Cslib.Quantum.ValueState (Option ι) A.V A.W →ₗᵢ[ℂ]
        Cslib.Quantum.ValueState (Option ι) A.V A.W) :
        Cslib.Quantum.ValueState ι (A.V ⊕ A.V) A.W →ₗᵢ[ℂ]
          Cslib.Quantum.ValueState ι (A.V ⊕ A.V) A.W :=
      (reindexSpace eSplit).symm.toLinearIsometry.comp
        ((sumEquiv (g.toLinearIsometryEquiv rfl)
            (LinearIsometryEquiv.refl ℂ _)).toLinearIsometry.comp
          (reindexSpace eSplit).toLinearIsometry)
    let step' : α → (EuclideanSpace ℂ (A.V ⊕ A.V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A.V ⊕ A.V)) :=
      fun a ↦ sumEquiv (A.step a) (LinearIsometryEquiv.refl ℂ _)
    let ψ₀ : Cslib.Quantum.ValueState ι (A.V ⊕ A.V) A.W :=
      (reindexSpace eSplit).symm (WithLp.toLp 2 fun s ↦ match s with
        | Sum.inl p => A.init.ofLp p
        | Sum.inr _ => 0)
    have hψ₀ : ‖ψ₀‖ = 1 := by
      dsimp only [ψ₀]
      rw [LinearIsometryEquiv.norm_map]
      have hsq : ‖(WithLp.toLp 2 (fun s : (Option ι × A.V × A.W) ⊕ Rest ↦ match s with
          | Sum.inl p => A.init.ofLp p
          | Sum.inr _ => 0) : EuclideanSpace ℂ ((Option ι × A.V × A.W) ⊕ Rest))‖ ^ 2 =
          ‖A.init‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
        simp
      rw [A.norm_init, one_pow] at hsq
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [sq] using hsq)
    let embedState (φ : Cslib.Quantum.ValueState (Option ι) A.V A.W) :
        Cslib.Quantum.ValueState ι (A.V ⊕ A.V) A.W :=
      (reindexSpace eSplit).symm (WithLp.toLp 2 fun s ↦ match s with
        | Sum.inl p => φ.ofLp p
        | Sum.inr _ => 0)
    have hrun : ∀ x t, Cslib.Quantum.runValue step' (fun s ↦ liftOp (A.unitary s)) ψ₀ x t =
        embedState (A.stateAt x t) := by
      intro x t
      induction t with
      | zero =>
        ext q
        rw [Cslib.Quantum.runValue]
        simp only [liftOp, ψ₀, embedState, QuantumValueAlg.stateAt, Cslib.Quantum.runValue,
          LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
          LinearIsometryEquiv.apply_symm_apply, reindexSpace_symm_apply]
        cases eSplit q with
        | inl p =>
          simp [sumEquiv_apply_inl, LinearIsometry.toLinearIsometryEquiv_apply]
        | inr r =>
          have hz : (WithLp.toLp 2 fun _ : Rest ↦ (0 : ℂ)) = 0 := rfl
          simp [sumEquiv_apply_inr, hz]
      | succ t ih =>
        rw [Cslib.Quantum.runValue, ih]
        have hor : Cslib.Quantum.valueOracle step' x (embedState (A.stateAt x t)) =
            embedState (Cslib.Quantum.valueOracle (idleStep A.step) (Option.map x)
              (A.stateAt x t)) := by
          ext ⟨i, v | v, w⟩
          · simp [Cslib.Quantum.valueOracle_apply, step', embedState, eSplit]
          · by_cases hi : i = i₀
            · subst hi
              simp [Cslib.Quantum.valueOracle_apply, step', embedState, eSplit]
            · simp [Cslib.Quantum.valueOracle_apply, step', embedState, eSplit, hi]
        rw [hor]
        ext q
        simp only [liftOp, embedState, QuantumValueAlg.stateAt, Cslib.Quantum.runValue,
          LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
          LinearIsometryEquiv.apply_symm_apply, reindexSpace_symm_apply]
        cases eSplit q with
        | inl p =>
          simp [sumEquiv_apply_inl, LinearIsometry.toLinearIsometryEquiv_apply]
        | inr r =>
          have hz : (WithLp.toLp 2 fun _ : Rest ↦ (0 : ℂ)) = 0 := rfl
          simp [sumEquiv_apply_inr, hz]
    let pDefault : Option ι × A.V × A.W :=
      Classical.choice (by
        by_contra hemp
        rw [not_nonempty_iff] at hemp
        have h0 : A.init = 0 := Subsingleton.elim _ _
        have := A.norm_init
        rw [h0, norm_zero] at this
        exact zero_ne_one this)
    let out' : ι × (A.V ⊕ A.V) × A.W → β := fun q ↦
      match eSplit q with
      | Sum.inl p => A.readout p
      | Sum.inr _ => A.readout pDefault
    refine ⟨A.V ⊕ A.V, A.W, inferInstance, A.instFintypeW, step',
      fun s ↦ liftOp (A.unitary s), ψ₀, hψ₀, out', fun x hx ↦ ?_⟩
    suffices hpmf : Cslib.Quantum.measureOut
        (Cslib.Quantum.runValue step' (fun s ↦ liftOp (A.unitary s)) ψ₀ x A.queries)
        (by rw [Cslib.Quantum.norm_runValue, hψ₀]) out' = A.outputPMF x by
      rw [hpmf]; exact hA x hx
    ext b
    rw [QuantumValueAlg.outputPMF, Cslib.Quantum.measureOut_eq_ofReal_measureProb,
      Cslib.Quantum.measureOut_eq_ofReal_measureProb]
    congr 1
    simp only [hrun x A.queries, QuantumValueAlg.finalState, Cslib.Quantum.measureProb, sum_filter]
    rw [← eSplit.symm.sum_comp]
    simp only [Fintype.sum_sum_type]
    have hzero : ∑ r : Rest, (if out' (eSplit.symm (Sum.inr r)) = b then
        ‖(embedState (A.stateAt x A.queries)).ofLp (eSplit.symm (Sum.inr r))‖ ^ 2 else 0) = 0 := by
      refine sum_eq_zero fun r _ ↦ ?_
      simp [embedState]
    rw [hzero, add_zero]
    refine sum_congr rfl fun p _ ↦ ?_
    simp [out', embedState]
  · rintro ⟨V, W, hFV, hFW, step, U, ψ₀, hψ₀, out, hcomp⟩
    classical
    let eSome : Option ι × V × W ≃ (ι × V × W) ⊕ (V × W) :=
      { toFun := fun ⟨oi, v, w⟩ ↦ match oi with
          | some i => Sum.inl (i, v, w)
          | none => Sum.inr (v, w)
        invFun := fun s ↦ match s with
          | Sum.inl (i, v, w) => (some i, v, w)
          | Sum.inr (v, w) => (none, v, w)
        left_inv := fun ⟨oi, _, _⟩ ↦ by cases oi <;> rfl
        right_inv := fun s ↦ by cases s <;> rfl }
    let liftU (t : ℕ) : Cslib.Quantum.ValueState (Option ι) V W →ₗᵢ[ℂ]
        Cslib.Quantum.ValueState (Option ι) V W :=
      (reindexSpace eSome).symm.toLinearIsometry.comp
        ((sumEquiv ((U t).toLinearIsometryEquiv rfl)
            (LinearIsometryEquiv.refl ℂ _)).toLinearIsometry.comp
          (reindexSpace eSome).toLinearIsometry)
    let embedSome (φ : Cslib.Quantum.ValueState ι V W) :
        Cslib.Quantum.ValueState (Option ι) V W :=
      (reindexSpace eSome).symm (WithLp.toLp 2 fun s ↦ match s with
        | Sum.inl q => φ.ofLp q
        | Sum.inr _ => 0)
    have hnorm : ‖embedSome ψ₀‖ = 1 := by
      dsimp only [embedSome]
      rw [LinearIsometryEquiv.norm_map]
      have hsq : ‖(WithLp.toLp 2 (fun s : (ι × V × W) ⊕ (V × W) ↦ match s with
          | Sum.inl q => ψ₀.ofLp q
          | Sum.inr _ => 0) : EuclideanSpace ℂ ((ι × V × W) ⊕ (V × W)))‖ ^ 2 = ‖ψ₀‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
        simp
      rw [hψ₀, one_pow] at hsq
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [sq] using hsq)
    let i₀ : ι := Classical.arbitrary ι
    let A : QuantumValueAlg ι α β :=
      { V := V
        W := W
        instFintypeV := hFV
        instFintypeW := hFW
        queries := T
        step := step
        unitary := liftU
        init := embedSome ψ₀
        norm_init := hnorm
        readout := fun ⟨oi, v, w⟩ ↦ out (oi.getD i₀, v, w) }
    refine ⟨A, rfl, fun x hx ↦ ?_⟩
    have hrun : ∀ t,
        (A.stateAt x t : Cslib.Quantum.ValueState (Option ι) V W) =
          embedSome (Cslib.Quantum.runValue step U ψ₀ x t) := by
      intro t
      induction t with
      | zero =>
        ext ⟨oi, v, w⟩
        cases oi with
        | some i =>
          simp [A, QuantumValueAlg.stateAt, Cslib.Quantum.runValue, liftU, embedSome, eSome,
            LinearIsometry.toLinearIsometryEquiv_apply]
        | none =>
          have hz : (WithLp.toLp 2 fun _ : V × W ↦ (0 : ℂ)) = 0 := rfl
          simp [A, QuantumValueAlg.stateAt, Cslib.Quantum.runValue, liftU, embedSome, eSome, hz]
      | succ t ih =>
        rw [A.stateAt_succ]
        change liftU (t + 1)
          (Cslib.Quantum.valueOracle (idleStep step) (Option.map x) (A.stateAt x t)) = _
        rw [ih]
        have hor : Cslib.Quantum.valueOracle (idleStep step) (Option.map x)
            (embedSome (Cslib.Quantum.runValue step U ψ₀ x t)) =
            embedSome (Cslib.Quantum.valueOracle step x
              (Cslib.Quantum.runValue step U ψ₀ x t)) := by
          ext ⟨oi, v, w⟩
          cases oi <;> simp [Cslib.Quantum.valueOracle_apply, embedSome, eSome]
        rw [hor]
        ext ⟨oi, v, w⟩
        cases oi with
        | some i =>
          simp [liftU, embedSome, eSome, Cslib.Quantum.runValue,
            LinearIsometry.toLinearIsometryEquiv_apply]
        | none =>
          have hz : (WithLp.toLp 2 fun _ : V × W ↦ (0 : ℂ)) = 0 := rfl
          simp [liftU, embedSome, eSome, hz]
    suffices hpmf : A.outputPMF x =
        Cslib.Quantum.measureOut (Cslib.Quantum.runValue step U ψ₀ x T)
          (by rw [Cslib.Quantum.norm_runValue, hψ₀]) out by
      rw [QuantumValueAlg.acceptProb, hpmf]
      exact hcomp x hx
    ext b
    rw [QuantumValueAlg.outputPMF, Cslib.Quantum.measureOut_eq_ofReal_measureProb,
      Cslib.Quantum.measureOut_eq_ofReal_measureProb]
    congr 1
    rw [Cslib.Quantum.measureProb, Cslib.Quantum.measureProb,
      Finset.sum_filter, Finset.sum_filter]
    have hfinA : (A.finalState x : Cslib.Quantum.ValueState (Option ι) V W) =
        embedSome (Cslib.Quantum.runValue step U ψ₀ x T) := hrun T
    change (∑ y : Option ι × V × W,
        if out (y.1.getD i₀, y.2.1, y.2.2) = b then
          ‖(A.finalState x : Cslib.Quantum.ValueState (Option ι) V W).ofLp y‖ ^ 2 else 0) = _
    rw [hfinA, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_option]
    have hnone : ∑ vw : V × W, (if out ((none : Option ι).getD i₀, vw.1, vw.2) = b then
        ‖(embedSome (Cslib.Quantum.runValue step U ψ₀ x T)).ofLp (none, vw)‖ ^ 2 else 0) = 0 := by
      refine sum_eq_zero fun ⟨v, w⟩ _ ↦ ?_
      simp [embedSome, eSome]
    rw [hnone, zero_add]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ ?_
    simp [embedSome, eSome]

/-- Minimal number of quantum value queries required to compute `f` on promise domain `P` with
worst-case error probability at most `ε`. -/
noncomputable def promiseQuantumQueryComplexity (P : (ι → α) → Prop) (ε : ℝ)
    (f : (ι → α) → β) : ℕ :=
  sInf {T : ℕ | ComputesWithin P f T ε}

/-- Standard `1 / 3`-bounded-error quantum query complexity on promise domain `P`. -/
noncomputable def promiseBoundedQuantumQueryComplexity (P : (ι → α) → Prop)
    (f : (ι → α) → β) : ℕ :=
  promiseQuantumQueryComplexity P (1 / 3) f

/-- Minimal number of quantum value queries required to compute a total function `f` with worst-case
error probability at most `ε`. -/
noncomputable def quantumQueryComplexity (ε : ℝ) (f : (ι → α) → β) : ℕ :=
  promiseQuantumQueryComplexity (fun _ ↦ True) ε f

/-- Standard `1 / 3`-bounded-error quantum query complexity of a total function `f`. -/
noncomputable def boundedQuantumQueryComplexity (f : (ι → α) → β) : ℕ :=
  quantumQueryComplexity (1 / 3) f

/-- Characterization of `promiseBoundedQuantumQueryComplexity` at `ε = 1 / 3`. -/
theorem promiseBoundedQuantumQueryComplexity_eq (P : (ι → α) → Prop) (f : (ι → α) → β) :
    promiseBoundedQuantumQueryComplexity P f = promiseQuantumQueryComplexity P (1 / 3) f := by
  rfl

/-- Characterization of `quantumQueryComplexity` as promise complexity on `True`. -/
theorem quantumQueryComplexity_eq (ε : ℝ) (f : (ι → α) → β) :
    quantumQueryComplexity ε f = promiseQuantumQueryComplexity (fun _ ↦ True) ε f := by
  rfl

/-- Characterization of `boundedQuantumQueryComplexity` at `ε = 1 / 3`. -/
theorem boundedQuantumQueryComplexity_eq (f : (ι → α) → β) :
    boundedQuantumQueryComplexity f = quantumQueryComplexity (1 / 3) f := by
  rfl

/-- Congruence of `promiseQuantumQueryComplexity` under equivalence of `ComputesWithin`. -/
theorem promiseQuantumQueryComplexity_congr_iff {ι₂ α₂ β₂ : Type*} [Fintype ι₂]
    {P₁ : (ι → α) → Prop} {f₁ : (ι → α) → β} {ε₁ : ℝ}
    {P₂ : (ι₂ → α₂) → Prop} {f₂ : (ι₂ → α₂) → β₂} {ε₂ : ℝ}
    (h : ∀ T, ComputesWithin P₁ f₁ T ε₁ ↔ ComputesWithin P₂ f₂ T ε₂) :
    promiseQuantumQueryComplexity P₁ ε₁ f₁ = promiseQuantumQueryComplexity P₂ ε₂ f₂ := by
  simp only [promiseQuantumQueryComplexity, h]

/-- Any `T`-query algorithm witnessing `ComputesWithin P f T ε` upper-bounds
`promiseQuantumQueryComplexity P ε f ≤ T`. -/
theorem promiseQuantumQueryComplexity_le_of_computesWithin {P : (ι → α) → Prop}
    {f : (ι → α) → β} {T : ℕ} {ε : ℝ} (h : ComputesWithin P f T ε) :
    promiseQuantumQueryComplexity P ε f ≤ T :=
  Nat.sInf_le h

/-- Any `T`-query algorithm witnessing `ComputesTotal f T ε` upper-bounds
`quantumQueryComplexity ε f ≤ T`. -/
theorem quantumQueryComplexity_le_of_computesTotal {f : (ι → α) → β} {T : ℕ} {ε : ℝ}
    (h : ComputesTotal f T ε) :
    quantumQueryComplexity ε f ≤ T :=
  Nat.sInf_le h

/-- Any `T`-query algorithm witnessing `ComputesTotal f T (1 / 3)` upper-bounds
`boundedQuantumQueryComplexity f ≤ T`. -/
theorem boundedQuantumQueryComplexity_le_of_computesTotal {f : (ι → α) → β} {T : ℕ}
    (h : ComputesTotal f T (1 / 3)) :
    boundedQuantumQueryComplexity f ≤ T :=
  Nat.sInf_le h

/-- When `{T | ComputesWithin P f T ε}` is nonempty (which holds unconditionally for `0 ≤ ε`),
`promiseQuantumQueryComplexity P ε f` itself achieves `ComputesWithin`. -/
theorem computesWithin_promiseQuantumQueryComplexity {P : (ι → α) → Prop} {f : (ι → α) → β}
    {ε : ℝ} (hne : ∃ T, ComputesWithin P f T ε) :
    ComputesWithin P f (promiseQuantumQueryComplexity P ε f) ε := by
  unfold promiseQuantumQueryComplexity
  obtain ⟨T, hT⟩ := hne
  exact Nat.sInf_mem (s := {T | ComputesWithin P f T ε}) ⟨T, hT⟩

/-- Lower-bounding `promiseQuantumQueryComplexity P ε f` from a universal lower bound on every
achieving query count `T` (given achievability `hne`). -/
theorem le_promiseQuantumQueryComplexity_of_forall {P : (ι → α) → Prop} {f : (ι → α) → β}
    {ε : ℝ} {B : ℕ} (hne : ∃ T, ComputesWithin P f T ε)
    (hB : ∀ T, ComputesWithin P f T ε → B ≤ T) :
    B ≤ promiseQuantumQueryComplexity P ε f :=
  hB _ (computesWithin_promiseQuantumQueryComplexity hne)

end ComplexityDefs

end CslibFrontier.Quantum
