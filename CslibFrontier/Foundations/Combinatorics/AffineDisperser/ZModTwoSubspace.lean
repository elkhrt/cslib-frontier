/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-!
# Necessary and sufficient affine-subspace characterization of affine dispersers over `𝔽₂`

`Cslib.BitString.isAffineDisperser_of_forall_exists_ne` proves one direction of the subspace
characterization of `Cslib.BitString.IsAffineDisperser`: nonconstancy on every `d`-dimensional
`AffineSubspace Bool (BitString n)` implies `IsAffineDisperser f d`. Because `Bool` is not a
`Field`, the converse cannot extract a basis over `Bool`. Passing along the canonical coordinatewise
bijection `BitString n ≃ (Fin n → ZMod 2)` (`bitStringEquivZMod2`), `ZMod 2` is a field, yielding
the exact two-sided characterization `isAffineDisperser_iff_forall_affineSubspace_zmod2`:
`IsAffineDisperser f d` holds if and only if `f` is nonconstant on every nonempty `d`-dimensional
`AffineSubspace (ZMod 2) (Fin n → ZMod 2)` (for `d ≤ n`).

## Main definitions

* `Cslib.BitString.boolEquivZMod2`, `Cslib.BitString.bitStringEquivZMod2`: coordinatewise bijection
  between `BitString n` and `Fin n → ZMod 2`.

## Main results

* `Cslib.BitString.isAffineDisperser_iff_forall_affineSubspace_zmod2`: `f` is an affine disperser
  for dimension `d` iff `f` is nonconstant on every nonempty `d`-dimensional affine subspace of
  `Fin n → ZMod 2`.
-/

public section

namespace Cslib.BitString

open Finset Module

/-- Canonical bijection `Bool ≃ ZMod 2` sending `false ↦ 0` and `true ↦ 1`. -/
def boolEquivZMod2 : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> rfl
  right_inv z := by fin_cases z <;> rfl

/-- `boolEquivZMod2` sends exclusive-or (`+` on `Bool`) to addition in `ZMod 2`. -/
theorem boolEquivZMod2_add (a b : Bool) :
    boolEquivZMod2 (a + b) = boolEquivZMod2 a + boolEquivZMod2 b := by
  cases a <;> cases b <;> rfl

/-- Coordinatewise bijection between `BitString n` and `Fin n → ZMod 2`. -/
def bitStringEquivZMod2 (n : ℕ) : BitString n ≃ (Fin n → ZMod 2) :=
  Equiv.arrowCongr (Equiv.refl (Fin n)) boolEquivZMod2

@[simp]
theorem bitStringEquivZMod2_apply {n : ℕ} (x : BitString n) (i : Fin n) :
    bitStringEquivZMod2 n x i = boolEquivZMod2 (x i) := by
  rfl

@[simp]
theorem bitStringEquivZMod2_symm_apply {n : ℕ} (v : Fin n → ZMod 2) (i : Fin n) :
    (bitStringEquivZMod2 n).symm v i = boolEquivZMod2.symm (v i) := by
  rfl

theorem bitStringEquivZMod2_add {n : ℕ} (x y : BitString n) :
    bitStringEquivZMod2 n (x + y) = bitStringEquivZMod2 n x + bitStringEquivZMod2 n y :=
  funext fun i ↦ boolEquivZMod2_add (x i) (y i)

private theorem zmod2_vec_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = z
  fin_cases z <;> rfl

private theorem exists_injective_linearMap_submodule {n : ℕ} :
    ∀ (d : ℕ) (W : Submodule (ZMod 2) (Fin n → ZMod 2)),
      d ≤ finrank (ZMod 2) W →
      ∃ emb : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2),
        Function.Injective emb ∧ ∀ u : Fin d → ZMod 2, emb u ∈ W := by
  intro d
  induction d with
  | zero =>
    intro W _
    exact ⟨0, fun u v _ ↦ Subsingleton.elim u v, fun _ ↦ W.zero_mem⟩
  | succ d ih =>
    intro W hdim
    have hne : W ≠ ⊥ := fun h ↦ by rw [h, finrank_bot] at hdim; omega
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hexj : ∃ j : Fin n, v j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv0 (funext hall)
    obtain ⟨j, hvj⟩ := hexj
    have hvj1 : v j = 1 := by
      have hor : v j = 0 ∨ v j = 1 := by
        generalize v j = z
        fin_cases z <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact hor.resolve_left hvj
    let φ : W →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj j).comp W.subtype
    have hsurj : Function.Surjective φ := fun a ↦ ⟨a • ⟨v, hvW⟩, by simp [φ, hvj1]⟩
    have hrange : finrank (ZMod 2) (LinearMap.range φ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hker : d ≤ finrank (ZMod 2) (LinearMap.ker φ) := by omega
    let W' : Submodule (ZMod 2) (Fin n → ZMod 2) := (LinearMap.ker φ).map W.subtype
    have hdim' : d ≤ finrank (ZMod 2) W' := by
      rwa [(Submodule.equivMapOfInjective W.subtype Subtype.val_injective
        (LinearMap.ker φ)).finrank_eq] at hker
    obtain ⟨emb', hemb'_inj, hemb'_mem⟩ := ih W' hdim'
    have hW'mem : ∀ w ∈ W', w ∈ W ∧ w j = 0 := by
      rintro _ ⟨⟨w, hwW⟩, hwker, rfl⟩
      exact ⟨hwW, LinearMap.mem_ker.mp hwker⟩
    let initMap : (Fin (d + 1) → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
      { toFun := Fin.init
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let emb : (Fin (d + 1) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      emb'.comp initMap + LinearMap.toSpanSingleton (ZMod 2) (Fin n → ZMod 2) v ∘ₗ
        LinearMap.proj (Fin.last d)
    refine ⟨emb, fun u₁ u₂ hEq ↦ ?_, fun u ↦ W.add_mem (hW'mem _ (hemb'_mem _)).1
      (W.smul_mem (u (Fin.last d)) hvW)⟩
    have hj_eq : u₁ (Fin.last d) = u₂ (Fin.last d) := by
      have h := congrFun hEq j
      simpa [emb, initMap, (hW'mem _ (hemb'_mem _)).2, hvj1] using h
    have hinit_eq : Fin.init u₁ = Fin.init u₂ := by
      apply hemb'_inj
      have h : emb' (Fin.init u₁) + u₁ (Fin.last d) • v =
          emb' (Fin.init u₂) + u₂ (Fin.last d) • v := hEq
      rw [hj_eq] at h
      exact add_right_cancel h
    rw [← Fin.snoc_init_self u₁, ← Fin.snoc_init_self u₂, hinit_eq, hj_eq]

/-- **Two-sided affine-subspace characterization of `IsAffineDisperser`**: a Boolean function
`f : BitString n → Bool` is an affine disperser for dimension `d` if and only if on every nonempty
`d`-dimensional `AffineSubspace (ZMod 2) (Fin n → ZMod 2)` there exist two points where `f` takes
distinct values. -/
theorem isAffineDisperser_iff_forall_affineSubspace_zmod2 {n d : ℕ} (f : BitString n → Bool) :
    IsAffineDisperser f d ↔
      ∀ A : AffineSubspace (ZMod 2) (Fin n → ZMod 2),
        (A : Set (Fin n → ZMod 2)).Nonempty →
        finrank (ZMod 2) A.direction = d →
        ∃ u ∈ A, ∃ v ∈ A, f ((bitStringEquivZMod2 n).symm u) ≠
          f ((bitStringEquivZMod2 n).symm v) := by
  constructor
  · intro hf A ⟨c, hc⟩ hdim
    obtain ⟨emb, hemb_inj, hemb_mem⟩ :=
      exists_injective_linearMap_submodule d A.direction hdim.ge
    let g : BitString d → BitString n :=
      fun x ↦ (bitStringEquivZMod2 n).symm (emb (bitStringEquivZMod2 d x) + c)
    have hg_aff : IsAffine g := fun x y z ↦ by
      apply (bitStringEquivZMod2 n).injective
      simp only [g, bitStringEquivZMod2_add, Equiv.apply_symm_apply, map_add]
      funext i
      simp only [Pi.add_apply]
      have hc2 : c i + c i = 0 := congrFun (zmod2_vec_add_self c) i
      calc emb (bitStringEquivZMod2 d x) i + emb (bitStringEquivZMod2 d y) i +
              emb (bitStringEquivZMod2 d z) i + c i
          = emb (bitStringEquivZMod2 d x) i + emb (bitStringEquivZMod2 d y) i +
              emb (bitStringEquivZMod2 d z) i + c i + (c i + c i) := by rw [hc2, add_zero]
        _ = (emb (bitStringEquivZMod2 d x) i + c i) + (emb (bitStringEquivZMod2 d y) i + c i) +
              (emb (bitStringEquivZMod2 d z) i + c i) := by ring
    have hg_inj : Function.Injective g := fun x y hEq ↦
      (bitStringEquivZMod2 d).injective
        (hemb_inj (add_right_cancel ((bitStringEquivZMod2 n).symm.injective hEq)))
    obtain ⟨x, y, hne⟩ := hf g hg_aff hg_inj
    have hmemA : ∀ z : BitString d, emb (bitStringEquivZMod2 d z) + c ∈ A := fun z ↦ by
      simpa using AffineSubspace.vadd_mem_of_mem_direction (hemb_mem _) hc
    exact ⟨_, hmemA x, _, hmemA y, hne⟩
  · intro hall g hg_aff hg_inj
    let c : Fin n → ZMod 2 := bitStringEquivZMod2 n (g 0)
    have hlin_add : ∀ x y : BitString d,
        bitStringEquivZMod2 n (g (x + y)) + c =
          (bitStringEquivZMod2 n (g x) + c) + (bitStringEquivZMod2 n (g y) + c) := fun x y ↦ by
      have h0 := hg_aff x y 0
      rw [add_zero] at h0
      rw [h0, bitStringEquivZMod2_add, bitStringEquivZMod2_add]
      funext i
      simp only [Pi.add_apply]
      ring
    let L : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      { toFun := fun u ↦ bitStringEquivZMod2 n (g ((bitStringEquivZMod2 d).symm u)) + c
        map_add' := fun u v ↦ by
          have hsymm : (bitStringEquivZMod2 d).symm (u + v) =
              (bitStringEquivZMod2 d).symm u + (bitStringEquivZMod2 d).symm v :=
            (bitStringEquivZMod2 d).injective (by
              rw [bitStringEquivZMod2_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
                Equiv.apply_symm_apply])
          rw [hsymm, hlin_add]
        map_smul' := fun a u ↦ by
          have ha : a = 0 ∨ a = 1 := by fin_cases a <;> [exact Or.inl rfl; exact Or.inr rfl]
          rcases ha with rfl | rfl
          · have hsymm0 : (bitStringEquivZMod2 d).symm 0 = 0 := by
              funext j
              rw [bitStringEquivZMod2_symm_apply, Pi.zero_apply]
              rfl
            simp only [zero_smul, RingHom.id_apply, hsymm0]
            exact zmod2_vec_add_self c
          · simp }
    have hL_inj : Function.Injective L := fun u v hEq ↦
      (bitStringEquivZMod2 d).symm.injective
        (hg_inj ((bitStringEquivZMod2 n).injective (add_right_cancel hEq)))
    let A : AffineSubspace (ZMod 2) (Fin n → ZMod 2) := AffineSubspace.mk' c (LinearMap.range L)
    have hdim : finrank (ZMod 2) A.direction = d := by
      rw [AffineSubspace.direction_mk', LinearMap.finrank_range_of_inj hL_inj,
        Module.finrank_fin_fun]
    obtain ⟨u, huA, v, hvA, hne⟩ := hall A ⟨c, AffineSubspace.self_mem_mk' c _⟩ hdim
    obtain ⟨u₀, hu₀⟩ := AffineSubspace.mem_mk'.mp huA
    obtain ⟨v₀, hv₀⟩ := AffineSubspace.mem_mk'.mp hvA
    have hgu : (bitStringEquivZMod2 n).symm u = g ((bitStringEquivZMod2 d).symm u₀) := by
      apply (bitStringEquivZMod2 n).injective
      rw [Equiv.apply_symm_apply]
      dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hu₀
      calc u = (u -ᵥ c) + c := by simp [vsub_eq_sub]
        _ = (bitStringEquivZMod2 n (g ((bitStringEquivZMod2 d).symm u₀)) + c) + c := by rw [← hu₀]
        _ = bitStringEquivZMod2 n (g ((bitStringEquivZMod2 d).symm u₀)) := by
            rw [add_assoc, zmod2_vec_add_self, add_zero]
    have hgv : (bitStringEquivZMod2 n).symm v = g ((bitStringEquivZMod2 d).symm v₀) := by
      apply (bitStringEquivZMod2 n).injective
      rw [Equiv.apply_symm_apply]
      dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hv₀
      calc v = (v -ᵥ c) + c := by simp [vsub_eq_sub]
        _ = (bitStringEquivZMod2 n (g ((bitStringEquivZMod2 d).symm v₀)) + c) + c := by rw [← hv₀]
        _ = bitStringEquivZMod2 n (g ((bitStringEquivZMod2 d).symm v₀)) := by
            rw [add_assoc, zmod2_vec_add_self, add_zero]
    rw [hgu, hgv] at hne
    exact ⟨_, _, hne⟩

end Cslib.BitString
