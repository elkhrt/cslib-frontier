/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Addition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Parity-Vector Spaces and Dual `𝔽₂`-Linear Transformations on the Boolean Cube

This module develops the `𝔽₂`-linear algebra of parity characters on finite Boolean cubes
`ι → Bool`, identifying subsets `S : Finset ι` with indicator vectors `parityVec S : ι → ZMod 2`,
defining parity spans `paritySpan` and parity dimensions `parityDim`, and constructing dual
(transpose) `𝔽₂`-linear transformations together with their action on Walsh–Fourier coefficients and
`𝔽₂`-polynomial degree.

## Main definitions

* `CslibFrontier.BooleanFunction.parityVec`, `CslibFrontier.BooleanFunction.parityVecEquiv`:
  identification of
  `Finset ι` with `ι → ZMod 2` sending symmetric difference to addition.
* `CslibFrontier.BooleanFunction.boolToZModVal`, `CslibFrontier.BooleanFunction.zmodToBoolVal`,
  `CslibFrontier.BooleanFunction.bitStringZModEquiv`: coordinatewise correspondence between `ι →
  Bool`
  and `ι → ZMod 2`.
* `CslibFrontier.BooleanFunction.applyF2Linear`, `CslibFrontier.BooleanFunction.transposeF2Linear`,
  `CslibFrontier.BooleanFunction.transposeF2Equiv`, `CslibFrontier.BooleanFunction.dualParitySet`,
  `CslibFrontier.BooleanFunction.applyF2Equiv`: Boolean action and dot-product adjoint of
  `𝔽₂`-linear
  maps.
* `CslibFrontier.BooleanFunction.paritySpan`, `CslibFrontier.BooleanFunction.parityDim`: `𝔽₂`-linear
  span and
  dimension of a family of character indices.

## Main results

* `CslibFrontier.BooleanFunction.fourierCoeff_comp_applyF2Linear`: Walsh–Fourier pullback formula
  along
  an arbitrary `𝔽₂`-linear map.
* `CslibFrontier.BooleanFunction.mem_lowDegree_comp_applyF2Linear`: pullback along an `𝔽₂`-linear
  map
  does not increase `𝔽₂`-polynomial degree.
* `CslibFrontier.BooleanFunction.exists_basis_subset_of_parityDim`: extraction of a linearly
  independent
  spanning subfamily of cardinality `parityDim`.
* `CslibFrontier.BooleanFunction.exists_linearEquiv_extending_finset`: extension of any linearly
  independent family of parities to an `𝔽₂`-linear automorphism of `ι → ZMod 2`.
-/

public section

namespace CslibFrontier.BooleanFunction

open Cslib Cslib.BitString Finset
open scoped BigOperators

variable {ι κ : Type*}

/-- Every element of `ZMod 2` is either `0` or `1`. -/
theorem ZMod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Characteristic vector in `ι → ZMod 2` of a character index `S : Finset ι`. -/
@[expose]
def parityVec [DecidableEq ι] (S : Finset ι) : ι → ZMod 2 :=
  fun i ↦ if i ∈ S then 1 else 0

/-- The empty character has zero parity vector. -/
@[simp]
theorem parityVec_empty [DecidableEq ι] : parityVec (∅ : Finset ι) = 0 := by
  ext i
  simp [parityVec]

/-- Coordinate evaluation of `parityVec S`. -/
theorem parityVec_apply [DecidableEq ι] (S : Finset ι) (i : ι) :
    parityVec S i = if i ∈ S then 1 else 0 :=
  rfl

/-- Coordinate evaluation of `parityVec S` at a member of `S`. -/
theorem parityVec_of_mem [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∈ S) :
    parityVec S i = 1 := by
  simp [parityVec, hi]

/-- Coordinate evaluation of `parityVec S` outside `S`. -/
theorem parityVec_of_notMem [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S) :
    parityVec S i = 0 := by
  simp [parityVec, hi]

/-- The singleton `{i}` maps to the standard basis vector `Pi.single i 1`. -/
theorem parityVec_singleton [DecidableEq ι] (i : ι) :
    parityVec ({i} : Finset ι) = Pi.single i 1 := by
  ext j
  simp [parityVec, Pi.single_apply, eq_comm]

/-- Standard-basis expansion of any vector `v : ι → ZMod 2` in singleton parities. -/
theorem sum_smul_parityVec_singleton [Fintype ι] [DecidableEq ι] (v : ι → ZMod 2) :
    ∑ i : ι, v i • parityVec ({i} : Finset ι) = v := by
  ext j; simp [parityVec]

/-- Mapping a character index along an injective embedding decomposes into singletons. -/
theorem parityVec_map [DecidableEq ι] (f : κ ↪ ι) (V : Finset κ) :
    parityVec (V.map f) = ∑ a ∈ V, parityVec ({f a} : Finset ι) := by
  classical
  ext i
  simp only [parityVec, Finset.sum_apply, mem_map, mem_singleton]
  by_cases hex : ∃ a ∈ V, f a = i
  · obtain ⟨a, ha, rfl⟩ := hex
    rw [ite_eq_left ⟨a, ha, rfl⟩]
    symm
    refine (sum_eq_single a (fun a' _ hne ↦ ite_eq_right fun h ↦ hne (f.injective h.symm))
      (fun hn ↦ (hn ha).elim)).trans (ite_eq_left rfl)
  · rw [ite_eq_right hex]
    exact (sum_eq_zero fun a ha ↦ ite_eq_right fun h ↦ hex ⟨a, ha, h.symm⟩).symm

/-- Symmetric difference of finite sets maps to addition in `ι → ZMod 2`. -/
@[simp]
theorem parityVec_symmDiff [DecidableEq ι] (S T : Finset ι) :
    parityVec (symmDiff S T) = parityVec S + parityVec T := by
  ext i
  simp only [parityVec, mem_symmDiff, Pi.add_apply]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
  · simp only [hS, hT, not_true_eq_false, and_false, or_self, ↓reduceIte]; decide
  · simp [hS, hT]
  · simp [hS, hT]
  · simp [hS, hT]

/-- Injective identification of `Finset ι` inside `ι → ZMod 2`. -/
theorem parityVec_injective [DecidableEq ι] : Function.Injective (parityVec (ι := ι)) := by
  intro S T h
  ext i
  have hi := congr_fun h i
  simp only [parityVec] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-- Equivalence between character indices `Finset ι` and vectors in `ι → ZMod 2`. -/
@[expose]
def parityVecEquiv [Fintype ι] [DecidableEq ι] : Finset ι ≃ (ι → ZMod 2) where
  toFun := parityVec
  invFun v := {i : ι | v i ≠ 0}
  left_inv S := by
    ext i
    simp [parityVec]
  right_inv v := by
    ext i
    simp only [parityVec, mem_filter, mem_univ, true_and]
    rcases ZMod2_eq_zero_or_one (v i) with h0 | h1
    · simp [h0]
    · simp [h1]

/-- Forward action of `parityVecEquiv` is `parityVec`. -/
@[simp]
theorem parityVecEquiv_apply [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    parityVecEquiv S = parityVec S := by
  rfl

/-- Inverse action of `parityVecEquiv` is the support filter `{i | v i ≠ 0}`. -/
@[simp]
theorem parityVecEquiv_symm_apply [Fintype ι] [DecidableEq ι] (v : ι → ZMod 2) :
    parityVecEquiv.symm v = {i : ι | v i ≠ 0} := by
  ext i
  simp [parityVecEquiv]

/-- `parityVec S = 0` iff `S = ∅`. -/
@[simp]
theorem parityVec_eq_zero_iff [DecidableEq ι] {S : Finset ι} :
    parityVec S = 0 ↔ S = ∅ := by
  rw [← parityVec_empty]
  exact parityVec_injective.eq_iff

/-- The zero vector corresponds to the empty set under `parityVecEquiv.symm`. -/
@[simp]
theorem parityVecEquiv_symm_zero [Fintype ι] [DecidableEq ι] :
    (parityVecEquiv (ι := ι)).symm 0 = ∅ := by
  apply parityVecEquiv.injective
  simp

/-- Addition in `ι → ZMod 2` corresponds to symmetric difference under `parityVecEquiv.symm`. -/
@[simp]
theorem parityVecEquiv_symm_add [Fintype ι] [DecidableEq ι] (u v : ι → ZMod 2) :
    parityVecEquiv.symm (u + v) = symmDiff (parityVecEquiv.symm u) (parityVecEquiv.symm v) := by
  apply parityVecEquiv.injective
  rw [Equiv.apply_symm_apply, parityVecEquiv_apply, parityVec_symmDiff, ← parityVecEquiv_apply,
    ← parityVecEquiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Convert a Boolean bit to `ZMod 2` (`false ↦ 0`, `true ↦ 1`). -/
@[expose]
def boolToZModVal (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- Convert a `ZMod 2` scalar to `Bool` (`0 ↦ false`, `1 ↦ true`). -/
@[expose]
def zmodToBoolVal (a : ZMod 2) : Bool :=
  a != 0

/-- `false` maps to `0 : ZMod 2`. -/
@[simp]
theorem boolToZModVal_false : boolToZModVal false = 0 := by rfl

/-- `true` maps to `1 : ZMod 2`. -/
@[simp]
theorem boolToZModVal_true : boolToZModVal true = 1 := by rfl

/-- `0 : ZMod 2` maps to `false`. -/
@[simp]
theorem zmodToBoolVal_zero : zmodToBoolVal 0 = false := by rfl

/-- `1 : ZMod 2` maps to `true`. -/
@[simp]
theorem zmodToBoolVal_one : zmodToBoolVal 1 = true := by rfl

/-- `zmodToBoolVal` is a left inverse to `boolToZModVal`. -/
@[simp]
theorem zmodToBoolVal_boolToZModVal (b : Bool) : zmodToBoolVal (boolToZModVal b) = b := by
  cases b <;> rfl

/-- `boolToZModVal` is a left inverse to `zmodToBoolVal`. -/
@[simp]
theorem boolToZModVal_zmodToBoolVal (a : ZMod 2) : boolToZModVal (zmodToBoolVal a) = a := by
  rcases ZMod2_eq_zero_or_one a with rfl | rfl <;> rfl

/-- Boolean `xor` maps to addition in `ZMod 2`. -/
@[simp]
theorem boolToZModVal_xor (a b : Bool) :
    boolToZModVal (a ^^ b) = boolToZModVal a + boolToZModVal b := by
  cases a <;> cases b <;> decide

/-- Addition in `ZMod 2` maps to Boolean `xor`. -/
@[simp]
theorem zmodToBoolVal_add (a b : ZMod 2) :
    zmodToBoolVal (a + b) = (zmodToBoolVal a ^^ zmodToBoolVal b) := by
  rcases ZMod2_eq_zero_or_one a with rfl | rfl <;>
    rcases ZMod2_eq_zero_or_one b with rfl | rfl <;> decide

/-- `boolToZModVal` agrees with `Cslib.BitString.bitVal (ZMod 2)`. -/
theorem boolToZModVal_eq_bitVal (b : Bool) : boolToZModVal b = bitVal (ZMod 2) b := by
  cases b <;> simp [bitVal]

/-- Coordinatewise equivalence between Boolean strings `ι → Bool` and `ι → ZMod 2`. -/
@[expose]
def bitStringZModEquiv : (ι → Bool) ≃ (ι → ZMod 2) where
  toFun x i := boolToZModVal (x i)
  invFun v i := zmodToBoolVal (v i)
  left_inv x := by ext i; simp
  right_inv v := by ext i; simp

/-- Coordinate evaluation of `bitStringZModEquiv`. -/
@[simp]
theorem bitStringZModEquiv_apply (x : ι → Bool) (i : ι) :
    bitStringZModEquiv x i = boolToZModVal (x i) := by
  rfl

/-- Coordinate evaluation of `bitStringZModEquiv.symm`. -/
@[simp]
theorem bitStringZModEquiv_symm_apply (v : ι → ZMod 2) (i : ι) :
    bitStringZModEquiv.symm v i = zmodToBoolVal (v i) := by
  rfl

/-- `parityOn S x` maps under `boolToZModVal` to the `𝔽₂` sum `∑ i ∈ S, xᵢ`. -/
theorem boolToZModVal_parityOn (S : Finset ι) (x : ι → Bool) :
    boolToZModVal (parityOn S x) = ∑ i ∈ S, boolToZModVal (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [parityOn_insert ha, boolToZModVal_xor, ih, sum_insert ha]

/-- `parityOn S x` equals the `𝔽₂` inner product `⟨parityVec S, x⟩`. -/
theorem boolToZModVal_parityOn_eq_dot [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : ι → Bool) :
    boolToZModVal (parityOn S x) = ∑ i : ι, parityVec S i * bitStringZModEquiv x i := by
  rw [boolToZModVal_parityOn]
  simp [parityVec]

/-- Action of an `𝔽₂`-linear map `A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)` on Boolean strings. -/
@[expose]
def applyF2Linear (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (y : κ → Bool) : ι → Bool :=
  bitStringZModEquiv.symm (A (bitStringZModEquiv y))

/-- Coordinate evaluation of `applyF2Linear`. -/
theorem applyF2Linear_apply (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (y : κ → Bool) (i : ι) :
    applyF2Linear A y i = zmodToBoolVal (A (bitStringZModEquiv y) i) := by
  rfl

/-- Composition law for `applyF2Linear`. -/
theorem applyF2Linear_comp {μ : Type*}
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
    (B : (μ → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (z : μ → Bool) :
    applyF2Linear A (applyF2Linear B z) = applyF2Linear (A.comp B) z := by
  simp [applyF2Linear]

/-- Identity law for `applyF2Linear`. -/
@[simp]
theorem applyF2Linear_id (x : ι → Bool) :
    applyF2Linear (LinearMap.id : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x = x := by
  simp [applyF2Linear]

/-- Dual (transpose) `𝔽₂`-linear map `(ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)` with respect to the
standard coordinate dot product. -/
@[expose]
def transposeF2Linear [Fintype ι] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) :
    (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2) where
  toFun w j := ∑ i : ι, w i * A (Pi.single j 1) i
  map_add' w₁ w₂ := by
    ext j
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c w := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, mul_sum]

/-- Coordinate evaluation of `transposeF2Linear`. -/
theorem transposeF2Linear_apply [Fintype ι] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (w : ι → ZMod 2) (j : κ) :
    transposeF2Linear A w j = ∑ i : ι, w i * A (Pi.single j 1) i := by
  rfl

/-- Dual action of an `𝔽₂`-linear map on character indices, satisfying
`χ_S(applyF2Linear A y) = χ_{dualParitySet A S}(y)`. -/
@[expose]
def dualParitySet [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (S : Finset ι) : Finset κ :=
  parityVecEquiv.symm (transposeF2Linear A (parityVec S))

/-- The dual of the empty character is empty. -/
@[simp]
theorem dualParitySet_empty [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) :
    dualParitySet A ∅ = ∅ := by
  simp [dualParitySet]

/-- Parity vector of `dualParitySet A S` equals `transposeF2Linear A (parityVec S)`. -/
@[simp]
theorem parityVec_dualParitySet [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (S : Finset ι) :
    parityVec (dualParitySet A S) = transposeF2Linear A (parityVec S) :=
  parityVecEquiv.apply_symm_apply _

/-- Dot-product adjointness for `transposeF2Linear`. -/
theorem dot_applyF2Linear [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (w : ι → ZMod 2) (v : κ → ZMod 2) :
    ∑ i : ι, w i * A v i = ∑ j : κ, transposeF2Linear A w j * v j := by
  have hv : v = ∑ j : κ, v j • Pi.single j (1 : ZMod 2) := by
    ext j'
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [transposeF2Linear, LinearMap.coe_mk, AddHom.coe_mk, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ ?_
  ring

/-- Double transpose is the identity. -/
@[simp]
theorem transposeF2Linear_transposeF2Linear [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) :
    transposeF2Linear (transposeF2Linear A) = A := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ j : κ, v j • Pi.single j (1 : ZMod 2) := by
    ext j'; simp [Pi.single_apply]
  rw [hv, map_sum, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, map_smul]
  congr 1
  ext i
  simp only [transposeF2Linear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_eq_single j (fun j' _ hne ↦ by simp [Pi.single_apply, hne]) (by simp)]
  simp only [Pi.single_eq_same, one_mul]
  rw [sum_eq_single i (fun i' _ hne ↦ by simp [hne]) (by simp)]
  simp

/-- Contravariance of `transposeF2Linear` under composition. -/
theorem transposeF2Linear_comp [Fintype ι] [Fintype κ] [DecidableEq κ]
    {μ : Type*} [DecidableEq μ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
    (B : (μ → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) :
    transposeF2Linear (A.comp B) = (transposeF2Linear B).comp (transposeF2Linear A) := by
  apply LinearMap.ext
  intro w
  ext m
  rw [LinearMap.comp_apply, transposeF2Linear_apply, LinearMap.comp_apply,
    dot_applyF2Linear A w (B (Pi.single m 1)), transposeF2Linear_apply]

/-- Transpose of an `𝔽₂`-linear equivalence `(κ → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)`. -/
@[expose]
def transposeF2Equiv [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : (κ → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    (ι → ZMod 2) ≃ₗ[ZMod 2] (κ → ZMod 2) :=
  LinearEquiv.ofLinearMap (transposeF2Linear B.toLinearMap) (transposeF2Linear B.symm.toLinearMap)
    (by
      rw [← transposeF2Linear_comp]
      apply LinearMap.ext; intro v; ext k
      simp [transposeF2Linear, Pi.single_apply])
    (by
      rw [← transposeF2Linear_comp]
      apply LinearMap.ext; intro w; ext i
      simp [transposeF2Linear, Pi.single_apply])

/-- Underlying linear map of `transposeF2Equiv B` is `transposeF2Linear B.toLinearMap`. -/
@[simp]
theorem transposeF2Equiv_toLinearMap [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : (κ → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    (transposeF2Equiv B).toLinearMap = transposeF2Linear B.toLinearMap := by
  rfl

/-- Inverse of `transposeF2Equiv B` is `transposeF2Equiv B.symm`. -/
@[simp]
theorem transposeF2Equiv_symm [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : (κ → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    (transposeF2Equiv B).symm = transposeF2Equiv B.symm := by
  ext w j
  rfl

/-- Parity commutes with `applyF2Linear` via `dualParitySet`. -/
theorem parityOn_applyF2Linear [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (S : Finset ι) (y : κ → Bool) :
    parityOn S (applyF2Linear A y) = parityOn (dualParitySet A S) y := by
  have hinj : Function.Injective boolToZModVal := fun a b h ↦ by
    simpa using congr_arg zmodToBoolVal h
  apply hinj
  rw [boolToZModVal_parityOn_eq_dot, boolToZModVal_parityOn_eq_dot]
  have h1 : bitStringZModEquiv (applyF2Linear A y) = A (bitStringZModEquiv y) :=
    bitStringZModEquiv.apply_symm_apply _
  have h2 : parityVec (dualParitySet A S) = transposeF2Linear A (parityVec S) :=
    parityVecEquiv.apply_symm_apply _
  rw [h1, h2]
  exact dot_applyF2Linear A (parityVec S) (bitStringZModEquiv y)

/-- Walsh characters pull back along `applyF2Linear` via `dualParitySet`. -/
theorem chi_applyF2Linear [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (S : Finset ι) (y : κ → Bool) :
    chi ℝ S (applyF2Linear A y) = chi ℝ (dualParitySet A S) y := by
  rw [chi_eq_signVal_parityOn, chi_eq_signVal_parityOn, parityOn_applyF2Linear]

/-- Fourier coefficients of a pullback `f ∘ applyF2Linear A` sum the fibers of
`dualParitySet A`. -/
theorem fourierCoeff_comp_applyF2Linear [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (f : (ι → Bool) → ℝ) (U : Finset κ) :
    fourierCoeff (fun y ↦ f (applyF2Linear A y)) U =
      ∑ S : Finset ι with dualParitySet A S = U, fourierCoeff f S := by
  have hexp : (fun y : κ → Bool ↦ f (applyF2Linear A y)) =
      fun y ↦ ∑ S : Finset ι, fourierCoeff f S * chi ℝ (dualParitySet A S) y := by
    ext y
    rw [← sum_fourierCoeff_mul_chi f (applyF2Linear A y)]
    simp_rw [chi_applyF2Linear]
  rw [hexp, fourierCoeff_sum_mul]
  simp_rw [fourierCoeff_chi, mul_ite, mul_one, mul_zero, sum_filter]

/-- `applyF2Linear` gives an equivalence of Boolean cubes for every `𝔽₂`-linear equivalence. -/
@[expose]
def applyF2Equiv (e : (κ → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) : (κ → Bool) ≃ (ι → Bool) :=
  bitStringZModEquiv.trans (e.toEquiv.trans bitStringZModEquiv.symm)

/-- Forward action of `applyF2Equiv` agrees with `applyF2Linear`. -/
theorem applyF2Equiv_apply (e : (κ → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (y : κ → Bool) :
    applyF2Equiv e y = applyF2Linear e.toLinearMap y := by
  rfl

/-- Pullback along any `𝔽₂`-linear map does not increase `𝔽₂`-degree. -/
theorem mem_lowDegree_comp_applyF2Linear [Finite κ]
    (A : (κ → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) {D : ℕ}
    {p : (ι → Bool) → ZMod 2} (hp : p ∈ lowDegree (ZMod 2) ι D) :
    (fun y ↦ p (applyF2Linear A y)) ∈ lowDegree (ZMod 2) κ D := by
  classical
  cases nonempty_fintype κ
  have hcoord : ∀ i : ι, (fun y : κ → Bool ↦ bitVal (ZMod 2) (applyF2Linear A y i)) ∈
      lowDegree (ZMod 2) κ 1 := by
    intro i
    have hfun : (fun y : κ → Bool ↦ bitVal (ZMod 2) (applyF2Linear A y i)) =
        ∑ j : κ, A (Pi.single j 1) i • (fun y : κ → Bool ↦ bitVal (ZMod 2) (y j)) := by
      ext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← boolToZModVal_eq_bitVal,
        applyF2Linear, bitStringZModEquiv_symm_apply, boolToZModVal_zmodToBoolVal]
      have hy : bitStringZModEquiv y =
          ∑ j : κ, bitStringZModEquiv y j • Pi.single j (1 : ZMod 2) := by
        ext j'
        simp [Pi.single_apply]
      conv_lhs => rw [hy, map_sum]
      simp [map_smul, Finset.sum_apply, smul_eq_mul, mul_comm]
    rw [hfun]
    exact sum_mem_lowDegree univ fun j _ ↦
      Submodule.smul_mem (lowDegree (ZMod 2) κ 1) (A (Pi.single j 1) i)
        (bitVal_mem_lowDegree (R := ZMod 2) j)
  have hmono : ∀ S : Finset ι, #S ≤ D →
      (fun y : κ → Bool ↦ monomial (ZMod 2) S (applyF2Linear A y)) ∈ lowDegree (ZMod 2) κ D := by
    intro S hS
    have hprod : (fun y : κ → Bool ↦ monomial (ZMod 2) S (applyF2Linear A y)) =
        ∏ i ∈ S, fun y : κ → Bool ↦ bitVal (ZMod 2) (applyF2Linear A y i) := by
      ext y
      rw [Finset.prod_apply, monomial_apply]
      by_cases hall : ∀ i ∈ S, applyF2Linear A y i = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hall)]
        symm
        exact prod_eq_one fun i hi ↦ by rw [hall i hi]; rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hall)]
        push Not at hall
        obtain ⟨i, hi, hne⟩ := hall
        have hfalse : applyF2Linear A y i = false := Bool.eq_false_iff.2 hne
        symm
        exact prod_eq_zero hi (by rw [hfalse]; rfl)
    rw [hprod]
    have hmono' : lowDegree (ZMod 2) κ #S ≤ lowDegree (ZMod 2) κ D := lowDegree_mono hS
    apply hmono'
    have hpm := prod_mem_lowDegree S fun i _ ↦ hcoord i
    rwa [mul_one] at hpm
  refine Submodule.span_induction ?_ (Submodule.zero_mem _)
    (fun _ _ _ _ hf hg ↦ Submodule.add_mem _ hf hg)
    (fun c _ _ hf ↦ Submodule.smul_mem _ c hf) hp
  rintro _ ⟨S, hS, rfl⟩
  exact hmono S hS

/-- The `𝔽₂`-linear subspace of `ι → ZMod 2` spanned by a collection of character indices. -/
@[expose]
def paritySpan [DecidableEq ι] (𝒮 : Set (Finset ι)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  Submodule.span (ZMod 2) (parityVec '' 𝒮)

/-- The `𝔽₂`-dimension of the span of a finite family of character indices. -/
@[expose]
noncomputable def parityDim [DecidableEq ι] (𝒮 : Finset (Finset ι)) : ℕ :=
  Module.finrank (ZMod 2) (paritySpan (𝒮 : Set (Finset ι)))

/-- The parity span of the empty family is trivial. -/
@[simp]
theorem paritySpan_empty [DecidableEq ι] : paritySpan (∅ : Set (Finset ι)) = ⊥ := by
  simp [paritySpan]

/-- The parity dimension of the empty family is `0`. -/
@[simp]
theorem parityDim_empty [DecidableEq ι] : parityDim (∅ : Finset (Finset ι)) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [parityDim, coe_empty, paritySpan_empty, finrank_bot]

/-- The parity dimension of `{∅}` is `0`. -/
@[simp]
theorem parityDim_singleton_empty [DecidableEq ι] :
    parityDim ({∅} : Finset (Finset ι)) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : paritySpan (({∅} : Finset (Finset ι)) : Set (Finset ι)) = ⊥ := by
    rw [paritySpan, Submodule.span_eq_bot]
    rintro _ ⟨S, hS, rfl⟩
    rw [show S = ∅ by simpa using hS, parityVec_empty]
  rw [parityDim, hbot, finrank_bot]

/-- Monotonicity of `paritySpan`. -/
@[gcongr]
theorem paritySpan_mono [DecidableEq ι] {𝒮 𝒯 : Set (Finset ι)} (h : 𝒮 ⊆ 𝒯) :
    paritySpan 𝒮 ≤ paritySpan 𝒯 :=
  Submodule.span_mono (Set.image_mono h)

/-- Monotonicity of `parityDim`. -/
@[gcongr]
theorem parityDim_mono [Finite ι] [DecidableEq ι] {𝒮 𝒯 : Finset (Finset ι)} (h : 𝒮 ⊆ 𝒯) :
    parityDim 𝒮 ≤ parityDim 𝒯 := by
  cases nonempty_fintype ι
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Submodule.finrank_mono (paritySpan_mono h)

/-- Every member of `𝒮` has its parity vector in `paritySpan 𝒮`. -/
theorem mem_paritySpan_of_mem [DecidableEq ι] {𝒮 : Set (Finset ι)} {S : Finset ι} (hS : S ∈ 𝒮) :
    parityVec S ∈ paritySpan 𝒮 :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Inserting `∅` leaves `paritySpan` unchanged. -/
theorem paritySpan_insert_empty [DecidableEq ι] (𝒮 : Set (Finset ι)) :
    paritySpan (insert ∅ 𝒮) = paritySpan 𝒮 := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨S, rfl | hS, rfl⟩
    · simp
    · exact mem_paritySpan_of_mem hS
  · exact paritySpan_mono (Set.subset_insert _ _)

/-- Removing `∅` leaves `paritySpan` unchanged. -/
theorem paritySpan_diff_singleton_empty [DecidableEq ι] (𝒮 : Set (Finset ι)) :
    paritySpan (𝒮 \ {∅}) = paritySpan 𝒮 := by
  apply le_antisymm (paritySpan_mono Set.sdiff_subset)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨S, hS, rfl⟩
  by_cases h0 : S = ∅
  · subst h0; simp
  · exact mem_paritySpan_of_mem ⟨hS, h0⟩

/-- `parityDim 𝒮 = 0` iff `𝒮 ⊆ {∅}`. -/
theorem parityDim_eq_zero_iff [Finite ι] [DecidableEq ι] {𝒮 : Finset (Finset ι)} :
    parityDim 𝒮 = 0 ↔ 𝒮 ⊆ {∅} := by
  cases nonempty_fintype ι
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [parityDim, Submodule.finrank_eq_zero, paritySpan, Submodule.span_eq_bot]
  constructor
  · intro h S hS
    rw [mem_singleton, ← parityVec_eq_zero_iff]
    exact h _ ⟨S, hS, rfl⟩
  · rintro h _ ⟨S, hS, rfl⟩
    rw [mem_singleton.1 (h hS), parityVec_empty]

/-- `parityDim 𝒮` never exceeds the ambient dimension `|ι|`. -/
theorem parityDim_le_card_type [Fintype ι] [DecidableEq ι] (𝒮 : Finset (Finset ι)) :
    parityDim 𝒮 ≤ Fintype.card ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Submodule.finrank_le _).trans_eq (Module.finrank_pi (ZMod 2))

/-- The full family `univ : Finset (Finset ι)` has parity span `⊤`. -/
@[simp]
theorem paritySpan_univ [Finite ι] [DecidableEq ι] :
    paritySpan (Set.univ : Set (Finset ι)) = ⊤ := by
  cases nonempty_fintype ι
  rw [eq_top_iff]
  intro v _
  exact Submodule.subset_span ⟨parityVecEquiv.symm v, Set.mem_univ _,
    parityVecEquiv.apply_symm_apply v⟩

/-- The full family `univ : Finset (Finset ι)` has parity dimension `|ι|`. -/
@[simp]
theorem parityDim_univ [Fintype ι] [DecidableEq ι] :
    parityDim (univ : Finset (Finset ι)) = Fintype.card ι := by
  rw [parityDim, coe_univ, paritySpan_univ, finrank_top, Module.finrank_pi]

/-- Linear equivalence invariance of `parityDim` when `L` maps generators of `𝒮` onto `𝒯`. -/
theorem parityDim_congr_equiv [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) {𝒮 : Finset (Finset ι)} {𝒯 : Finset (Finset κ)}
    (h : ∀ S : Finset ι, S ∈ 𝒮 ↔ S.map e.toEmbedding ∈ 𝒯) :
    parityDim 𝒮 = parityDim 𝒯 := by
  let L : (ι → ZMod 2) ≃ₗ[ZMod 2] (κ → ZMod 2) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm
  have hL : ∀ S : Finset ι, L (parityVec S) = parityVec (S.map e.toEmbedding) := by
    intro S; ext j; simp [L, parityVec]
  have hmap : Submodule.map L.toLinearMap (paritySpan (𝒮 : Set (Finset ι))) =
      paritySpan (𝒯 : Set (Finset κ)) := by
    rw [paritySpan, paritySpan, Submodule.map_span]
    congr 1; ext w; constructor
    · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
      exact ⟨S.map e.toEmbedding, (h S).1 hS, (hL S).symm⟩
    · rintro ⟨T, hT, rfl⟩
      let S : Finset ι := T.map e.symm.toEmbedding
      have hST : S.map e.toEmbedding = T := by ext j; simp [S]
      exact ⟨parityVec S, ⟨S, (h S).2 (hST.symm ▸ hT), rfl⟩, (hL S).trans (congrArg parityVec hST)⟩
  rw [parityDim, parityDim, ← hmap]
  exact (LinearEquiv.finrank_map_eq L _).symm

/-- `Module.finrank (ZMod 2) (paritySpan 𝒮)` equals `parityDim 𝒮`. -/
theorem finrank_paritySpan [DecidableEq ι] (𝒮 : Finset (Finset ι)) :
    Module.finrank (ZMod 2) (paritySpan (𝒮 : Set (Finset ι))) = parityDim 𝒮 := by
  rfl

/-- Elimination principle for membership in `paritySpan 𝒮`. -/
theorem paritySpan_le [DecidableEq ι] {𝒮 : Set (Finset ι)}
    {W : Submodule (ZMod 2) (ι → ZMod 2)} :
    paritySpan 𝒮 ≤ W ↔ ∀ S ∈ 𝒮, parityVec S ∈ W := by
  rw [paritySpan, Submodule.span_le, Set.image_subset_iff]; rfl

/-- A family `𝒮` has cardinality at most `2 ^ parityDim 𝒮`. -/
theorem card_le_two_pow_parityDim [Finite ι] [DecidableEq ι] (𝒮 : Finset (Finset ι)) :
    #𝒮 ≤ 2 ^ parityDim 𝒮 := by
  classical
  cases nonempty_fintype ι
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W := paritySpan (𝒮 : Set (Finset ι))
  have hinj : Function.Injective (fun S : 𝒮 ↦ (⟨parityVec S.1, mem_paritySpan_of_mem S.2⟩ : W)) :=
    fun a b h ↦ Subtype.ext (parityVec_injective (congr_arg Subtype.val h))
  have hcard : Fintype.card 𝒮 ≤ Fintype.card W := Fintype.card_le_of_injective _ hinj
  let b := Module.Basis.ofVectorSpace (ZMod 2) W
  have hW : Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, ZMod.card,
      ← Module.finrank_eq_card_basis b]
  rw [Fintype.card_coe, hW] at hcard
  exact hcard

/-- Every finite family `𝒮` of character indices contains a subset `ℬ ⊆ 𝒮` of cardinality
`parityDim 𝒮` whose characteristic vectors form a basis of `paritySpan 𝒮`. -/
theorem exists_basis_subset_of_parityDim [DecidableEq ι]
    (𝒮 : Finset (Finset ι)) :
    ∃ ℬ : Finset (Finset ι),
      ℬ ⊆ 𝒮 ∧
      #ℬ = parityDim 𝒮 ∧
      paritySpan (ℬ : Set (Finset ι)) = paritySpan (𝒮 : Set (Finset ι)) ∧
      LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I, hI_sub, hI_span, hI_li⟩ :=
    exists_linearIndependent (ZMod 2) (parityVec '' (𝒮 : Set (Finset ι)))
  let ℬ : Finset (Finset ι) := {S ∈ 𝒮 | parityVec S ∈ I}
  have hℬ_sub : ℬ ⊆ 𝒮 := filter_subset _ _
  have hℬ_img : parityVec '' (ℬ : Set (Finset ι)) = I := by
    ext v
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact (mem_filter.1 hS).2
    · intro hv
      obtain ⟨S, hS, rfl⟩ := hI_sub hv
      exact ⟨S, mem_filter.2 ⟨hS, hv⟩, rfl⟩
  have hspan : paritySpan (ℬ : Set (Finset ι)) = paritySpan (𝒮 : Set (Finset ι)) := by
    simp only [paritySpan, hℬ_img, hI_span]
  have hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1) := by
    let φ : ℬ → I := fun S ↦ ⟨parityVec S.1, (mem_filter.1 S.2).2⟩
    have hinj : Function.Injective φ :=
      fun a b h ↦ Subtype.ext (parityVec_injective (congr_arg Subtype.val h))
    exact hI_li.comp φ hinj
  have hcard : #ℬ = parityDim 𝒮 := by
    have hfr := Module.finrank_eq_card_basis (Module.Basis.span hli)
    have hrange : Set.range (fun S : ℬ ↦ parityVec S.1) = parityVec '' (ℬ : Set (Finset ι)) := by
      ext v; simp
    rw [hrange, Fintype.card_coe] at hfr
    change #ℬ = Module.finrank (ZMod 2) (paritySpan (𝒮 : Set (Finset ι)))
    rw [← hspan]
    exact hfr.symm
  exact ⟨ℬ, hℬ_sub, hcard, hspan, hli⟩

/-- `parityDim 𝒮` never exceeds `#𝒮`. -/
theorem parityDim_le_card [DecidableEq ι] (𝒮 : Finset (Finset ι)) :
    parityDim 𝒮 ≤ #𝒮 := by
  obtain ⟨ℬ, hsub, hcard, _, _⟩ := exists_basis_subset_of_parityDim 𝒮
  rw [← hcard]
  exact card_le_card hsub

/-- A linearly independent family `ℬ` with `paritySpan ℬ = paritySpan 𝒮` has `#ℬ = parityDim 𝒮`. -/
theorem parityDim_eq_card_of_basis [DecidableEq ι]
    {𝒮 ℬ : Finset (Finset ι)}
    (hspan : paritySpan (ℬ : Set (Finset ι)) = paritySpan (𝒮 : Set (Finset ι)))
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    parityDim 𝒮 = #ℬ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfr := Module.finrank_eq_card_basis (Module.Basis.span hli)
  have hrange : Set.range (fun S : ℬ ↦ parityVec S.1) = parityVec '' (ℬ : Set (Finset ι)) := by
    ext v; simp
  rw [hrange, Fintype.card_coe] at hfr
  change Module.finrank (ZMod 2) (paritySpan (𝒮 : Set (Finset ι))) = #ℬ
  rw [← hspan]
  exact hfr

/-- A linearly independent family of parities cannot contain `∅`. -/
theorem empty_notMem_of_linearIndependent [DecidableEq ι] {ℬ : Finset (Finset ι)}
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    ∅ ∉ ℬ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  have hne := hli.ne_zero ⟨∅, h0⟩
  simp at hne

/-- Any linearly independent family `ℬ` of character indices extends to an `𝔽₂`-linear automorphism
`B` of `ι → ZMod 2` sending singleton coordinates `{emb S}` to `S` and remaining singletons outside
`paritySpan ℬ`. -/
theorem exists_linearEquiv_extending_finset [Finite ι] [DecidableEq ι]
    {ℬ : Finset (Finset ι)}
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    ∃ (B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (emb : ℬ ↪ ι),
      (∀ S : ℬ, B (parityVec {emb S}) = parityVec S.1) ∧
      (∀ i : ι, i ∉ Set.range emb → B (parityVec {i}) ∉ paritySpan (ℬ : Set (Finset ι))) := by
  classical
  cases nonempty_fintype ι
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let s : Set (ι → ZMod 2) := parityVec '' (ℬ : Set (Finset ι))
  let e : ℬ ≃ s := Equiv.ofBijective
    (fun S : ℬ ↦ (⟨parityVec S.1, ⟨S.1, S.2, rfl⟩⟩ : s))
    ⟨fun a b h ↦ Subtype.ext (parityVec_injective (congr_arg Subtype.val h)),
     fun ⟨_, S, hS, hv⟩ ↦ ⟨⟨S, hS⟩, Subtype.ext hv⟩⟩
  have hs_li : LinearIndepOn (ZMod 2) id s := by
    change LinearIndependent (ZMod 2) (fun x : s ↦ x.1)
    refine (linearIndependent_equiv e).1 ?_
    exact hli
  let bExt := Module.Basis.extend hs_li
  have hcard : Fintype.card (hs_li.extend (Set.subset_univ s)) = Fintype.card ι := by
    have h1 := Module.finrank_eq_card_basis bExt
    rw [Module.finrank_pi (ZMod 2)] at h1
    exact h1.symm
  let idxEquiv : hs_li.extend (Set.subset_univ s) ≃ ι := Fintype.equivOfCardEq hcard
  let stdBasis : Module.Basis ι (ZMod 2) (ι → ZMod 2) := Pi.basisFun (ZMod 2) ι
  let bReindex : Module.Basis ι (ZMod 2) (ι → ZMod 2) := bExt.reindex idxEquiv
  let B : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) := stdBasis.equiv bReindex (Equiv.refl ι)
  have hsub : s ⊆ hs_li.extend (Set.subset_univ s) := hs_li.subset_extend (Set.subset_univ s)
  let emb : ℬ ↪ ι :=
    { toFun := fun S ↦ idxEquiv ⟨parityVec S.1, hsub ⟨S.1, S.2, rfl⟩⟩
      inj' := fun _ _ h ↦
        Subtype.ext (parityVec_injective (congr_arg Subtype.val (idxEquiv.injective h))) }
  refine ⟨B, emb, ?_, ?_⟩
  · intro S
    have hemb : emb S = idxEquiv ⟨parityVec S.1, hsub ⟨S.1, S.2, rfl⟩⟩ := rfl
    rw [parityVec_singleton]
    have hstd : Pi.single (emb S) (1 : ZMod 2) = stdBasis (emb S) := by simp [stdBasis]
    rw [hstd]
    simp [B, bReindex, bExt, hemb]
  · intro i hi hmem
    have hstd : parityVec ({i} : Finset ι) = stdBasis i := by
      rw [parityVec_singleton]; simp [stdBasis]
    let j0 : hs_li.extend (Set.subset_univ s) := idxEquiv.symm i
    have hBi : B (parityVec {i}) = j0.1 := by
      rw [hstd]
      simp [B, bReindex, bExt, j0]
    rw [hBi] at hmem
    have hnotins : j0.1 ∉ s := by
      rintro ⟨S, hS, heq⟩
      apply hi
      refine ⟨⟨S, hS⟩, ?_⟩
      have hsub_eq : (⟨parityVec S, hsub ⟨S, hS, rfl⟩⟩ : hs_li.extend (Set.subset_univ s)) = j0 :=
        Subtype.ext heq
      change idxEquiv ⟨parityVec S, hsub ⟨S, hS, rfl⟩⟩ = i
      rw [hsub_eq]
      exact idxEquiv.apply_symm_apply i
    have hspan_sub : paritySpan (ℬ : Set (Finset ι)) ≤
        Submodule.span (ZMod 2) (bExt '' (Set.univ \ {j0})) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨S, hS, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨parityVec S, hsub ⟨S, hS, rfl⟩⟩, ⟨Set.mem_univ _, ?_⟩, by simp [bExt]⟩
      intro heq
      apply hnotins
      have hv : j0.1 = parityVec S := congr_arg Subtype.val (Set.mem_singleton_iff.1 heq).symm
      rw [hv]
      exact ⟨S, hS, rfl⟩
    have hj0_not := (linearIndependent_iff_notMem_span.1 bExt.linearIndependent) j0
    apply hj0_not
    have hb0 : bExt j0 = j0.1 := by simp [bExt]
    rw [hb0]
    exact hspan_sub hmem

end CslibFrontier.BooleanFunction
