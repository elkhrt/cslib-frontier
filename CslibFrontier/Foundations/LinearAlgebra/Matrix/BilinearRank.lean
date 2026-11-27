/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bilinear Tensor Rank of Matrix Multiplication and Row-Wise Kronecker Products

Develops algebraic complexity primitives for matrix multiplication:
- Bilinear tensor rank `matrixMulRank` and total complexity `matrixMulCost` of `⟨n₁, n₂, n₃⟩`
  with exact `S₃` permutation invariance,
- Row-wise Kronecker (face-splitting) product `rowKronecker` and Hadamard factorization
  `(U₁ * V₁ᵀ) ⊙ (U₂ * V₂ᵀ) = (rowKronecker U₁ U₂) * (rowKronecker V₁ V₂)ᵀ`.
-/

public section

namespace Cslib.LinearAlgebra

open Matrix Finset

/-- A rank-`r` bilinear tensor decomposition of the `n₁ × n₂ × n₃` matrix multiplication tensor
`⟨n₁, n₂, n₃⟩` over a semiring `R`. -/
def IsMatrixMulDecomp (R : Type*) [Semiring R] (n₁ n₂ n₃ r : ℕ)
    (u : Fin r → Matrix (Fin n₁) (Fin n₂) R)
    (v : Fin r → Matrix (Fin n₂) (Fin n₃) R)
    (w : Fin r → Matrix (Fin n₃) (Fin n₁) R) : Prop :=
  ∀ (i₁ i₁' : Fin n₁) (i₂ i₂' : Fin n₂) (i₃ i₃' : Fin n₃),
    ∑ t : Fin r, u t i₁ i₂ * v t i₂' i₃ * w t i₃' i₁' =
      (if i₂ = i₂' then (1 : R) else 0) * (if i₃ = i₃' then 1 else 0) *
        (if i₁ = i₁' then 1 else 0)

/-- The bilinear tensor rank `R(⟨n₁, n₂, n₃⟩)` of `n₁ × n₂` by `n₂ × n₃` matrix
multiplication over `R`. -/
noncomputable def matrixMulRank (R : Type*) [Semiring R] (n₁ n₂ n₃ : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ u v w, IsMatrixMulDecomp R n₁ n₂ n₃ r u v w}

/-- Total bilinear complexity plus input/output matrix sizes. -/
noncomputable def matrixMulCost (R : Type*) [Semiring R] (n₁ n₂ n₃ : ℕ) : ℕ :=
  matrixMulRank R n₁ n₂ n₃ + n₁ * n₂ + n₂ * n₃ + n₁ * n₃

/-- Every bilinear decomposition evaluates `A * B` via `r` scalar multiplications. -/
theorem IsMatrixMulDecomp.mul_eq {R : Type*} [CommSemiring R] {n₁ n₂ n₃ r : ℕ}
    {u : Fin r → Matrix (Fin n₁) (Fin n₂) R}
    {v : Fin r → Matrix (Fin n₂) (Fin n₃) R}
    {w : Fin r → Matrix (Fin n₃) (Fin n₁) R}
    (h : IsMatrixMulDecomp R n₁ n₂ n₃ r u v w)
    (A : Matrix (Fin n₁) (Fin n₂) R) (B : Matrix (Fin n₂) (Fin n₃) R)
    (i₁ : Fin n₁) (i₃ : Fin n₃) :
    (A * B) i₁ i₃ =
      ∑ t : Fin r,
        (∑ i, ∑ j, u t i j * A i j) * (∑ j', ∑ k, v t j' k * B j' k) * w t i₃ i₁ := by
  have h1 :
      ∑ t : Fin r,
        (∑ i, ∑ j, u t i j * A i j) * (∑ j', ∑ k, v t j' k * B j' k) * w t i₃ i₁ =
      ∑ i, ∑ j, ∑ j', ∑ k,
        A i j * B j' k * (∑ t : Fin r, u t i j * v t j' k * w t i₃ i₁) := by
    have hstep : ∀ t : Fin r,
        (∑ i, ∑ j, u t i j * A i j) * (∑ j', ∑ k, v t j' k * B j' k) * w t i₃ i₁ =
        ∑ i, ∑ j, ∑ j', ∑ k, A i j * B j' k * (u t i j * v t j' k * w t i₃ i₁) := fun t => by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  rw [h1, Matrix.mul_apply]
  have h' : ∀ (i₁ i₁' : Fin n₁) (i₂ i₂' : Fin n₂) (i₃ i₃' : Fin n₃),
      ∑ t : Fin r, u t i₁ i₂ * v t i₂' i₃ * w t i₃' i₁' =
        (if i₂ = i₂' then (1 : R) else 0) * (if i₃ = i₃' then 1 else 0) *
          (if i₁ = i₁' then 1 else 0) := h
  simp_rw [h']
  symm
  calc
    ∑ i : Fin n₁, ∑ j : Fin n₂, ∑ j' : Fin n₂, ∑ k : Fin n₃,
        A i j * B j' k *
          ((if j = j' then (1 : R) else 0) * (if k = i₃ then 1 else 0) *
            (if i = i₁ then 1 else 0))
      = ∑ i : Fin n₁, if i = i₁ then
          ∑ j : Fin n₂, ∑ j' : Fin n₂, if j' = j then
            ∑ k : Fin n₃, if k = i₃ then A i j * B j' k else 0
          else 0
        else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i = i₁
          · subst hi
            simp only [↓reduceIte]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
            by_cases hj : j' = j
            · subst hj
              simp only [↓reduceIte]
              refine Finset.sum_congr rfl fun k _ => by split_ifs <;> simp_all
            · simp [Ne.symm hj, hj]
          · simp [hi]
    _ = ∑ j : Fin n₂, A i₁ j * B j i₃ := by
          simp [Finset.sum_ite_eq']

/-- Cyclic permutation `(u, v, w) ↦ (v, w, u)` preserves bilinear decompositions. -/
theorem IsMatrixMulDecomp.cyclic {R : Type*} [CommSemiring R] {n₁ n₂ n₃ r : ℕ}
    {u : Fin r → Matrix (Fin n₁) (Fin n₂) R}
    {v : Fin r → Matrix (Fin n₂) (Fin n₃) R}
    {w : Fin r → Matrix (Fin n₃) (Fin n₁) R}
    (h : IsMatrixMulDecomp R n₁ n₂ n₃ r u v w) :
    IsMatrixMulDecomp R n₂ n₃ n₁ r v w u := by
  intro i₂ i₂' i₃ i₃' i₁ i₁'
  calc ∑ t : Fin r, v t i₂ i₃ * w t i₃' i₁ * u t i₁' i₂'
      = ∑ t : Fin r, u t i₁' i₂' * v t i₂ i₃ * w t i₃' i₁ :=
        Finset.sum_congr rfl fun t _ => by ring
    _ = (if i₂' = i₂ then (1 : R) else 0) * (if i₃ = i₃' then 1 else 0) *
          (if i₁' = i₁ then 1 else 0) := h i₁' i₁ i₂' i₂ i₃ i₃'
    _ = (if i₃ = i₃' then (1 : R) else 0) * (if i₁ = i₁' then 1 else 0) *
          (if i₂ = i₂' then 1 else 0) := by split_ifs <;> simp_all

/-- Transposition `(u, v, w) ↦ (vᵀ, uᵀ, wᵀ)` preserves bilinear decompositions. -/
theorem IsMatrixMulDecomp.transpose {R : Type*} [CommSemiring R] {n₁ n₂ n₃ r : ℕ}
    {u : Fin r → Matrix (Fin n₁) (Fin n₂) R}
    {v : Fin r → Matrix (Fin n₂) (Fin n₃) R}
    {w : Fin r → Matrix (Fin n₃) (Fin n₁) R}
    (h : IsMatrixMulDecomp R n₁ n₂ n₃ r u v w) :
    IsMatrixMulDecomp R n₃ n₂ n₁ r
      (fun t => (v t)ᵀ) (fun t => (u t)ᵀ) (fun t => (w t)ᵀ) := by
  intro i₃ i₃' i₂ i₂' i₁ i₁'
  calc ∑ t : Fin r, (v t)ᵀ i₃ i₂ * (u t)ᵀ i₂' i₁ * (w t)ᵀ i₁' i₃'
      = ∑ t : Fin r, u t i₁ i₂' * v t i₂ i₃ * w t i₃' i₁' :=
        Finset.sum_congr rfl fun t _ => by simp [Matrix.transpose_apply]; ring
    _ = (if i₂' = i₂ then (1 : R) else 0) * (if i₃ = i₃' then 1 else 0) *
          (if i₁ = i₁' then 1 else 0) := h i₁ i₁' i₂' i₂ i₃ i₃'
    _ = (if i₂ = i₂' then (1 : R) else 0) * (if i₁ = i₁' then 1 else 0) *
          (if i₃ = i₃' then 1 else 0) := by split_ifs <;> simp_all

/-- Naive triple-loop decomposition of rank `n₁ * n₂ * n₃`. -/
theorem exists_isMatrixMulDecomp_naive (R : Type*) [Semiring R] (n₁ n₂ n₃ : ℕ) :
    ∃ u v w, IsMatrixMulDecomp R n₁ n₂ n₃ (n₁ * n₂ * n₃) u v w := by
  let e : Fin (n₁ * n₂ * n₃) ≃ Fin n₁ × Fin n₂ × Fin n₃ :=
    (finCongr (by simp [Fintype.card_prod, mul_assoc])).trans
      (Fintype.equivFin (Fin n₁ × Fin n₂ × Fin n₃)).symm
  let e' : Fin n₁ × Fin n₂ × Fin n₃ ≃ Fin (n₁ * n₂ * n₃) := e.symm
  refine ⟨fun t i j => if (e t).1 = i ∧ (e t).2.1 = j then 1 else 0,
    fun t j k => if (e t).2.1 = j ∧ (e t).2.2 = k then 1 else 0,
    fun t k i => if (e t).2.2 = k ∧ (e t).1 = i then 1 else 0, ?_⟩
  intro i₁ i₁' i₂ i₂' i₃ i₃'
  rw [← e'.sum_comp]
  simp only [e', Equiv.apply_symm_apply]
  have hterm : ∀ p : Fin n₁ × Fin n₂ × Fin n₃,
      (if p.1 = i₁ ∧ p.2.1 = i₂ then (1 : R) else 0) *
        (if p.2.1 = i₂' ∧ p.2.2 = i₃ then 1 else 0) *
        (if p.2.2 = i₃' ∧ p.1 = i₁' then 1 else 0) =
      if p = (i₁, i₂, i₃) then
        (if i₂ = i₂' then (1 : R) else 0) * (if i₃ = i₃' then 1 else 0) *
          (if i₁ = i₁' then 1 else 0)
      else 0 := by
    rintro ⟨a, b, c⟩
    by_cases h1 : a = i₁ <;> by_cases h2 : b = i₂ <;> by_cases h3 : c = i₃ <;>
      by_cases h1' : i₁ = i₁' <;> by_cases h2' : i₂ = i₂' <;> by_cases h3' : i₃ = i₃' <;>
      simp_all
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' Finset.univ (i₁, i₂, i₃)]
  simp

/-- `matrixMulRank` is invariant under cyclic permutation. -/
theorem matrixMulRank_cyclic (R : Type*) [CommSemiring R] (n₁ n₂ n₃ : ℕ) :
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₂ n₃ n₁ := by
  have hle : ∀ a b c : ℕ, matrixMulRank R b c a ≤ matrixMulRank R a b c := fun a b c => by
    unfold matrixMulRank
    refine le_csInf (⟨_, exists_isMatrixMulDecomp_naive R a b c⟩) ?_
    rintro r ⟨u, v, w, h⟩
    exact Nat.sInf_le ⟨v, w, u, h.cyclic⟩
  exact le_antisymm ((hle n₃ n₁ n₂).trans (hle n₂ n₃ n₁)) (hle n₁ n₂ n₃)

/-- `matrixMulRank` is invariant under reversing outer dimensions. -/
theorem matrixMulRank_transpose (R : Type*) [CommSemiring R] (n₁ n₂ n₃ : ℕ) :
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₃ n₂ n₁ := by
  have hle : ∀ a b c : ℕ, matrixMulRank R c b a ≤ matrixMulRank R a b c := fun a b c => by
    unfold matrixMulRank
    refine le_csInf (⟨_, exists_isMatrixMulDecomp_naive R a b c⟩) ?_
    rintro r ⟨u, v, w, h⟩
    exact Nat.sInf_le ⟨_, _, _, h.transpose⟩
  exact le_antisymm (hle n₃ n₂ n₁) (hle n₁ n₂ n₃)

/-- Exact `S₃` permutation invariance of `matrixMulRank`. -/
theorem matrixMulRank_perm (R : Type*) [CommSemiring R] (n₁ n₂ n₃ : ℕ) :
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₁ n₃ n₂ ∧
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₂ n₁ n₃ ∧
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₂ n₃ n₁ ∧
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₃ n₁ n₂ ∧
    matrixMulRank R n₁ n₂ n₃ = matrixMulRank R n₃ n₂ n₁ := by
  have hc1 := matrixMulRank_cyclic R n₁ n₂ n₃
  have hc2 := matrixMulRank_cyclic R n₂ n₃ n₁
  have ht1 := matrixMulRank_transpose R n₁ n₂ n₃
  have ht2 := matrixMulRank_transpose R n₂ n₃ n₁
  have ht3 := matrixMulRank_transpose R n₃ n₁ n₂
  exact ⟨by rw [hc1, ht2], by rw [hc1, hc2, ht3], hc1, by rw [hc1, hc2], ht1⟩

/-- Exact `S₃` permutation invariance of `matrixMulCost`. -/
theorem matrixMulCost_perm (R : Type*) [CommSemiring R] (n₁ n₂ n₃ : ℕ) :
    matrixMulCost R n₁ n₂ n₃ = matrixMulCost R n₁ n₃ n₂ ∧
    matrixMulCost R n₁ n₂ n₃ = matrixMulCost R n₂ n₁ n₃ ∧
    matrixMulCost R n₁ n₂ n₃ = matrixMulCost R n₂ n₃ n₁ ∧
    matrixMulCost R n₁ n₂ n₃ = matrixMulCost R n₃ n₁ n₂ ∧
    matrixMulCost R n₁ n₂ n₃ = matrixMulCost R n₃ n₂ n₁ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := matrixMulRank_perm R n₁ n₂ n₃
  simp only [matrixMulCost]
  refine ⟨by rw [h1]; ring, by rw [h2]; ring, by rw [h3]; ring, by rw [h4]; ring,
    by rw [h5]; ring⟩

/-- Row-wise Kronecker (face-splitting) product `A ⊘ B`. -/
def rowKronecker {m n₁ n₂ R : Type*} [Mul R]
    (A : Matrix m n₁ R) (B : Matrix m n₂ R) : Matrix m (n₁ × n₂) R :=
  Matrix.of fun i p => A i p.1 * B i p.2

@[simp]
theorem rowKronecker_apply {m n₁ n₂ R : Type*} [Mul R]
    (A : Matrix m n₁ R) (B : Matrix m n₂ R) (i : m) (p : n₁ × n₂) :
    rowKronecker A B i p = A i p.1 * B i p.2 := by
  rfl

/-- Hadamard factorization identity `(U₁ * V₁ᵀ) ⊙ (U₂ * V₂ᵀ) = (U₁ ⊘ U₂) * (V₁ ⊘ V₂)ᵀ`. -/
theorem rowKronecker_mul_transpose {m n k₁ k₂ R : Type*} [Fintype k₁] [Fintype k₂]
    [CommSemiring R] (U₁ : Matrix m k₁ R) (V₁ : Matrix n k₁ R)
    (U₂ : Matrix m k₂ R) (V₂ : Matrix n k₂ R) :
    (U₁ * V₁ᵀ) ⊙ (U₂ * V₂ᵀ) = rowKronecker U₁ U₂ * (rowKronecker V₁ V₂)ᵀ := by
  ext i j
  rw [Matrix.hadamard_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => by
    simp only [Matrix.transpose_apply, rowKronecker_apply]; ring

end Cslib.LinearAlgebra
