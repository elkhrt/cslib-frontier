/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Bilinear Tensor Rank and Asymptotic Exponents of Matrix Multiplication

This module defines bilinear tensor decompositions of `N × N` matrix multiplication
(`IsMatMulBilinearDecomp`, `HasMatMulRankLe`) and admissible asymptotic matrix multiplication
exponents `ω` (`IsMatrixMulExponent`), following Bürgisser–Clausen–Shokrollahi, *Algebraic
Complexity Theory*.

We prove:
1. Naive triple-loop matrix multiplication gives `HasMatMulRankLe R N (N ^ 3)` and hence
   `IsMatrixMulExponent R 3` over every commutative ring `R`.
2. Over any field `K`, every bilinear decomposition of `N × N` matrix multiplication has length
   `q ≥ N ^ 2`, so every admissible exponent satisfies `2 ≤ ω` (and no `ω < 2` is admissible).

## Main definitions

* `Cslib.Complexity.Algebraic.IsMatMulBilinearDecomp`: bilinear decomposition
  `A * B = ∑ t, (u t A * v t B) • w t`.
* `Cslib.Complexity.Algebraic.HasMatMulRankLe`: existence of a length-`q` bilinear decomposition.
* `Cslib.Complexity.Algebraic.IsMatrixMulExponent`: asymptotic exponent `ω` with bilinear rank
  `≤ C * N ^ (ω + ε)` for every `ε > 0`.

## Main results

* `Cslib.Complexity.Algebraic.hasMatMulRankLe_cube`,
  `Cslib.Complexity.Algebraic.isMatrixMulExponent_three`: `ω = 3` is admissible over any
  commutative ring.
* `Cslib.Complexity.Algebraic.sq_le_of_hasMatMulRankLe`,
  `Cslib.Complexity.Algebraic.two_le_of_isMatrixMulExponent`,
  `Cslib.Complexity.Algebraic.not_isMatrixMulExponent_of_lt_two`: `N ^ 2 ≤ q` and `2 ≤ ω` over any
  field.
-/

public section

namespace Cslib.Complexity.Algebraic

/-- A bilinear tensor decomposition of `N × N` matrix multiplication of length `q` over `R`:
`A * B = ∑ t, (u t A * v t B) • w t` for linear functionals `u t, v t` and output matrices `w t`. -/
@[expose] def IsMatMulBilinearDecomp (R : Type*) [CommRing R] (N q : ℕ)
    (u v : Fin q → Matrix (Fin N) (Fin N) R →ₗ[R] R)
    (w : Fin q → Matrix (Fin N) (Fin N) R) : Prop :=
  ∀ A B : Matrix (Fin N) (Fin N) R, A * B = ∑ t : Fin q, (u t A * v t B) • w t

/-- `N × N` matrix multiplication over `R` has bilinear rank at most `q`. -/
@[expose] def HasMatMulRankLe (R : Type*) [CommRing R] (N q : ℕ) : Prop :=
  ∃ (u v : Fin q → Matrix (Fin N) (Fin N) R →ₗ[R] R)
    (w : Fin q → Matrix (Fin N) (Fin N) R),
    IsMatMulBilinearDecomp R N q u v w

/-- Monotonicity of `HasMatMulRankLe` in the rank bound `q`. -/
theorem HasMatMulRankLe.mono {R : Type*} [CommRing R] {N q q' : ℕ}
    (h : HasMatMulRankLe R N q) (hle : q ≤ q') : HasMatMulRankLe R N q' := by
  obtain ⟨u, v, w, huv⟩ := h
  let u' : Fin q' → Matrix (Fin N) (Fin N) R →ₗ[R] R :=
    fun t ↦ if ht : t.1 < q then u ⟨t.1, ht⟩ else 0
  let v' : Fin q' → Matrix (Fin N) (Fin N) R →ₗ[R] R :=
    fun t ↦ if ht : t.1 < q then v ⟨t.1, ht⟩ else 0
  let w' : Fin q' → Matrix (Fin N) (Fin N) R :=
    fun t ↦ if ht : t.1 < q then w ⟨t.1, ht⟩ else 0
  refine ⟨u', v', w', fun A B ↦ ?_⟩
  rw [huv A B]
  let emb : Fin q ↪ Fin q' := Fin.castLEEmb hle
  have hmap : ∑ s : Fin q, (u s A * v s B) • w s =
      ∑ t ∈ Finset.univ.map emb, (u' t A * v' t B) • w' t := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp [emb, u', v', w']
  rw [hmap]
  refine Finset.sum_subset (Finset.subset_univ _) fun t _ ht ↦ ?_
  have hnot : ¬ t.1 < q := by
    intro hlt
    exact ht (Finset.mem_map.mpr ⟨⟨t.1, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  simp [u', v', w', hnot]

/-- Naive triple-loop matrix multiplication gives `HasMatMulRankLe R N (N ^ 3)` over any
commutative ring `R`. -/
theorem hasMatMulRankLe_cube (R : Type*) [CommRing R] (N : ℕ) :
    HasMatMulRankLe R N (N ^ 3) := by
  let eqv : Fin (N ^ 3) ≃ (Fin N × Fin N) × Fin N :=
    (Fintype.equivFinOfCardEq (by simp [pow_three, Nat.mul_assoc])).symm
  let u : Fin (N ^ 3) → Matrix (Fin N) (Fin N) R →ₗ[R] R := fun t ↦
    { toFun := fun A ↦ A (eqv t).1.1 (eqv t).1.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let v : Fin (N ^ 3) → Matrix (Fin N) (Fin N) R →ₗ[R] R := fun t ↦
    { toFun := fun B ↦ B (eqv t).1.2 (eqv t).2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let w : Fin (N ^ 3) → Matrix (Fin N) (Fin N) R := fun t ↦
    Matrix.of fun r c ↦ if r = (eqv t).1.1 ∧ c = (eqv t).2 then 1 else 0
  refine ⟨u, v, w, fun A B ↦ ?_⟩
  ext r c
  rw [Matrix.mul_apply, Matrix.sum_apply]
  have hconv : (∑ t : Fin (N ^ 3), ((u t A * v t B) • w t) r c) =
      ∑ p : (Fin N × Fin N) × Fin N,
        if r = p.1.1 ∧ c = p.2 then A p.1.1 p.1.2 * B p.1.2 p.2 else 0 := by
    refine Fintype.sum_equiv eqv _ _ fun t ↦ ?_
    simp [u, v, w]
    rfl
  rw [hconv, Fintype.sum_prod_type, Fintype.sum_prod_type]
  symm
  dsimp only
  rw [Finset.sum_eq_single r]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      simp [hc'.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ c))
  · intro r' _ hr'
    refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun c' _ ↦ ?_
    simp [hr'.symm]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ r))

/-- Over any field `K`, every bilinear decomposition of `N × N` matrix multiplication has length
`q ≥ N ^ 2`. -/
theorem sq_le_of_hasMatMulRankLe (K : Type*) [Field K] {N q : ℕ}
    (h : HasMatMulRankLe K N q) : N ^ 2 ≤ q := by
  obtain ⟨u, v, w, huv⟩ := h
  let eqv : Fin N × Fin N ≃ Fin (N ^ 2) :=
    Fintype.equivFinOfCardEq (by simp [sq])
  let φ : (Fin q → K) →ₗ[K] (Fin (N ^ 2) → K) :=
    { toFun := fun c idx ↦ (∑ t : Fin q, c t • w t) (eqv.symm idx).1 (eqv.symm idx).2
      map_add' := fun c₁ c₂ ↦ by
        funext idx
        simp [add_smul, Finset.sum_add_distrib, Matrix.add_apply]
      map_smul' := fun r c ↦ by
        funext idx
        simp [Matrix.sum_apply, Matrix.smul_apply, mul_assoc, Finset.mul_sum] }
  have hsurj : Function.Surjective φ := by
    intro y
    let B : Matrix (Fin N) (Fin N) K := Matrix.of fun i j ↦ y (eqv (i, j))
    refine ⟨fun t ↦ u t 1 * v t B, ?_⟩
    funext idx
    change (∑ t : Fin q, (u t 1 * v t B) • w t) (eqv.symm idx).1 (eqv.symm idx).2 = y idx
    rw [← huv 1 B, one_mul]
    simp [B]
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hle := LinearMap.finrank_range_le φ
  rwa [hrange, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hle

/-- A real number `ω` is an **admissible exponent of matrix multiplication** over `R` if for every
`ε > 0` there exists `C > 0` such that for all `N ≥ 1`, `N × N` matrix multiplication over `R` has
bilinear rank at most `q ≤ C * N ^ (ω + ε)`. -/
@[expose] def IsMatrixMulExponent (R : Type*) [CommRing R] (ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1 ≤ N → ∃ q : ℕ, (q : ℝ) ≤ C * (N : ℝ) ^ (ω + ε) ∧ HasMatMulRankLe R N q

/-- Monotonicity of `IsMatrixMulExponent`: if `ω` is an admissible exponent and `ω ≤ ω'`, then
`ω'` is also an admissible exponent. -/
theorem IsMatrixMulExponent.mono {R : Type*} [CommRing R] {ω ω' : ℝ}
    (hω : IsMatrixMulExponent R ω) (hle : ω ≤ ω') : IsMatrixMulExponent R ω' := by
  intro ε hε
  obtain ⟨C, hC, hN⟩ := hω ε hε
  refine ⟨C, hC, fun N hN1 ↦ ?_⟩
  obtain ⟨q, hq, hrk⟩ := hN N hN1
  refine ⟨q, hq.trans ?_, hrk⟩
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)) hC.le

/-- `ω = 3` is unconditionally an admissible matrix multiplication exponent over every
commutative ring `R`. -/
theorem isMatrixMulExponent_three (R : Type*) [CommRing R] : IsMatrixMulExponent R 3 := by
  intro ε hε
  refine ⟨1, zero_lt_one, fun N hN ↦ ⟨N ^ 3, ?_, hasMatMulRankLe_cube R N⟩⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ (3 : ℕ) := by norm_cast
    _ = (N : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast (N : ℝ) 3).symm
    _ ≤ 1 * (N : ℝ) ^ (3 + ε) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- Over any field `K`, every admissible matrix multiplication exponent satisfies `2 ≤ ω`. -/
theorem two_le_of_isMatrixMulExponent (K : Type*) [Field K] {ω : ℝ}
    (hω : IsMatrixMulExponent K ω) : 2 ≤ ω := by
  by_contra hlt
  push Not at hlt
  set ε : ℝ := (2 - ω) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hN⟩ := hω ε hε
  set δ : ℝ := 2 - (ω + ε)
  have hδ : 0 < δ := by dsimp [δ, ε]; linarith
  have hgt1 : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hgt1
  let N : ℕ := 2 ^ k
  have hN1 : 1 ≤ N := Nat.one_le_pow k 2 (by norm_num)
  obtain ⟨q, hq, hrk⟩ := hN N hN1
  have hsq : ((N ^ 2 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast sq_le_of_hasMatMulRankLe K hrk
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hpow_eq : ((2 : ℝ) ^ δ) ^ k = (N : ℝ) ^ δ := by
    have hNcast : (N : ℝ) = (2 : ℝ) ^ k := by simp [N]
    rw [hNcast, ← Real.rpow_natCast ((2 : ℝ) ^ δ) k, ← Real.rpow_mul (by norm_num),
      mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hC_lt : C * (N : ℝ) ^ (ω + ε) < ((N ^ 2 : ℕ) : ℝ) := by
    have hmul : C * (N : ℝ) ^ (ω + ε) < (N : ℝ) ^ δ * (N : ℝ) ^ (ω + ε) :=
      mul_lt_mul_of_pos_right (hk.trans_eq hpow_eq) (Real.rpow_pos_of_pos hNpos _)
    calc
      C * (N : ℝ) ^ (ω + ε) < (N : ℝ) ^ δ * (N : ℝ) ^ (ω + ε) := hmul
      _ = (N : ℝ) ^ (δ + (ω + ε)) := (Real.rpow_add hNpos δ (ω + ε)).symm
      _ = (N : ℝ) ^ (2 : ℝ) := by
        congr 1
        dsimp [δ]
        ring
      _ = (N : ℝ) ^ (2 : ℕ) := Real.rpow_natCast (N : ℝ) 2
      _ = ((N ^ 2 : ℕ) : ℝ) := by norm_cast
  linarith

/-- Sharpness of `IsMatrixMulExponent`: over any field `K`, no `ω < 2` is an admissible matrix
multiplication exponent. -/
theorem not_isMatrixMulExponent_of_lt_two (K : Type*) [Field K] {ω : ℝ} (h : ω < 2) :
    ¬ IsMatrixMulExponent K ω :=
  fun hω ↦ h.not_ge (two_le_of_isMatrixMulExponent K hω)

end Cslib.Complexity.Algebraic
