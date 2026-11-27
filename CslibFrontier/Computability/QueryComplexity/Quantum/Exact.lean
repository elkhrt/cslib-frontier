/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.Data.BitString.Weight
public import CslibFrontier.Foundations.Quantum.Fourier
public import CslibFrontier.Foundations.Quantum.POVM
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact Quantum Query Complexity in the Modular-Addition Oracle Model

This module develops the exact quantum query complexity model for functions
`f : BitString n → X` into an arbitrary finite alphabet `X`, using the modular-addition
oracle `O_x |i, b, w⟩ = |i, b + x_i, w⟩` (`b : ZMod d`) built on
`Cslib.Quantum.valueOracle`, `Cslib.Quantum.addStep`, `Cslib.Quantum.runValue`, and
`Cslib.Quantum.POVM`.

It provides:
1. Unitary building blocks on `EuclideanSpace ℂ`: matrix-unitary conversion, the quantum
   Fourier transform `qftEquiv`, direct-sum unitary extension along embeddings, fiberwise
   unitary lifting, and basis-state preparation.
2. The flat quantum query model (`QuantumQueryAlgorithm`, `ExactQuantumComputableInMod`,
   `ExactQuantumComputableIn`, `exactQuantumQueryComplexity`) and the phase-kickback
   diagonalization of `modAddStep` by `qftEquiv`.
3. The amplitude-polynomial orthogonality lower-bound method under standard Lean axioms:
   exactness forces final states of differently valued inputs to be orthogonal; every
   final-state amplitude after `T` queries to any Boolean unitary value oracle has
   multilinear degree at most `T`; and Minsky–Papert symmetrization yields general
   root-counting lower bounds on the full cube and on affine subcubes.

## Main definitions

* `CslibFrontier.Quantum.modAddStep`, `CslibFrontier.Quantum.modAddOracle`: the
  modular-addition query step and oracle on `ZMod d`.
* `CslibFrontier.Quantum.QuantumQueryAlgorithm`: a `T`-query quantum algorithm with
  unit initial state, unitary sequence `U_0..., U_T`, and POVM measurement.
* `CslibFrontier.Quantum.ExactQuantumComputableIn`: existence of an exact `T`-query
  algorithm computing `f`.
* `CslibFrontier.Quantum.exactQuantumQueryComplexity`: the exact quantum query
  complexity `Q_E(f)`.

## Main results

* `CslibFrontier.Quantum.qft_modAddStep_qft_symm`: phase kickback for `modAddStep`.
* `CslibFrontier.Quantum.inner_finalState_eq_zero_of_ne`: exactness implies
  orthogonality of final states for inputs with distinct outputs.
* `CslibFrontier.Quantum.amplitude_mem_lowDegree_valueOracle`: amplitudes after `t`
  queries to any Boolean value oracle have multilinear degree at most `t`.
* `CslibFrontier.Quantum.card_le_of_exact_subcube_zero`,
  `CslibFrontier.Quantum.card_le_of_exact_subcube_top`,
  `CslibFrontier.Quantum.card_le_of_exact_weight_zero`,
  `CslibFrontier.Quantum.card_le_of_exact_weight_top`: root-counting lower bounds for
  exact quantum query complexity.
-/

public section

namespace CslibFrontier.Quantum

open Cslib Cslib.BitString Cslib.Quantum Finset Matrix Polynomial
open scoped ComplexOrder

/-! ### Unitary and Euclidean-space linear-isometry helpers -/

section UnitaryHelpers

/-- Convert a matrix in `unitaryGroup ι ℂ` into a unitary `LinearIsometryEquiv` on
`EuclideanSpace ℂ ι`. -/
noncomputable def unitaryEquivOfMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitaryGroup ι ℂ) : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun ψ := WithLp.toLp 2 ((U : Matrix ι ι ℂ) *ᵥ ψ.ofLp)
  invFun ψ := WithLp.toLp 2 ((U : Matrix ι ι ℂ)ᴴ *ᵥ ψ.ofLp)
  map_add' ψ φ := by ext i; simp [Matrix.mulVec_add]
  map_smul' c ψ := by ext i; simp [Matrix.mulVec_smul]
  left_inv ψ := by
    ext i
    have hU : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 :=
      (mem_unitaryGroup_iff').mp U.2
    simp [Matrix.mulVec_mulVec, hU]
  right_inv ψ := by
    ext i
    have hU : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 :=
      (mem_unitaryGroup_iff).mp U.2
    simp [Matrix.mulVec_mulVec, hU]
  norm_map' ψ :=
    Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self
      ((mem_unitaryGroup_iff').mp U.2) ψ

@[simp]
theorem unitaryEquivOfMatrix_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    (unitaryEquivOfMatrix U ψ).ofLp i = ((U : Matrix ι ι ℂ) *ᵥ ψ.ofLp) i := by
  unfold unitaryEquivOfMatrix; rfl

@[simp]
theorem unitaryEquivOfMatrix_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    ((unitaryEquivOfMatrix U).symm ψ).ofLp i = ((U : Matrix ι ι ℂ)ᴴ *ᵥ ψ.ofLp) i := by
  unfold unitaryEquivOfMatrix; rfl

/-- Unitary quantum Fourier transform on `EuclideanSpace ℂ (ZMod d)`. -/
noncomputable def qftEquiv (d : ℕ) [NeZero d] :
    EuclideanSpace ℂ (ZMod d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod d) :=
  unitaryEquivOfMatrix (qft d)

@[simp]
theorem qftEquiv_apply (d : ℕ) [NeZero d] (ψ : EuclideanSpace ℂ (ZMod d)) (j : ZMod d) :
    (qftEquiv d ψ).ofLp j =
      ∑ k : ZMod d, (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (j * k) * ψ.ofLp k := by
  simp only [qftEquiv, unitaryEquivOfMatrix_apply, Matrix.mulVec, dotProduct, qft_apply]

@[simp]
theorem qftEquiv_symm_apply (d : ℕ) [NeZero d] (ψ : EuclideanSpace ℂ (ZMod d)) (j : ZMod d) :
    ((qftEquiv d).symm ψ).ofLp j =
      ∑ k : ZMod d, (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (-(j * k)) * ψ.ofLp k := by
  simp only [qftEquiv, unitaryEquivOfMatrix_symm_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, qft_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
  refine sum_congr rfl fun k _ => ?_
  rw [← AddChar.map_neg_eq_conj, mul_comm k j]

/-- Direct-sum extension of a unitary `U` along an embedding `j : A ↪ P`, acting as `U` on
`Set.range j` and as the identity off `Set.range j`. -/
noncomputable def directSumUnitary {A P : Type*} [Fintype A] [Fintype P]
    (j : A ↪ P) (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ P := by
  classical
  let act (V : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A) (ψ : EuclideanSpace ℂ P) :
      EuclideanSpace ℂ P :=
    WithLp.toLp 2 fun p =>
      if hp : p ∈ Set.range j then
        (V (WithLp.toLp 2 fun a => ψ.ofLp (j a))).ofLp
          ((Equiv.ofInjective j j.injective).symm ⟨p, hp⟩)
      else ψ.ofLp p
  have hact_emb : ∀ V ψ a, (act V ψ).ofLp (j a) =
      (V (WithLp.toLp 2 fun a' => ψ.ofLp (j a'))).ofLp a := fun V ψ a => by
    have ha : j a ∈ Set.range j := Set.mem_range_self a
    simp only [act, ha, ↓reduceDIte]
    exact congrArg _ ((Equiv.ofInjective j j.injective).symm_apply_apply a)
  have hact_rest : ∀ V ψ p, p ∉ Set.range j → (act V ψ).ofLp p = ψ.ofLp p := fun V ψ p hp => by
    simp only [act, hp, ↓reduceDIte]
  have hact_inv : ∀ V ψ, act V.symm (act V ψ) = ψ := fun V ψ => by
    ext p
    by_cases hp : p ∈ Set.range j
    · obtain ⟨a, rfl⟩ := hp
      rw [hact_emb]
      have harg : (WithLp.toLp 2 fun a' => (act V ψ).ofLp (j a')) =
          V (WithLp.toLp 2 fun a' => ψ.ofLp (j a')) := by
        ext a'; exact hact_emb V ψ a'
      rw [harg, V.symm_apply_apply]
    · rw [hact_rest _ _ _ hp, hact_rest _ _ _ hp]
  have hnorm : ∀ ψ, ‖act U ψ‖ = ‖ψ‖ := fun ψ => by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ Set.range j),
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ Set.range j)]
    congr 1
    · rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
      · have hfilt : Finset.univ.filter (fun p : P => p ∈ Set.range j) = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨a, _⟩
          exact hA.false a
        rw [hfilt, Finset.sum_empty, Finset.sum_empty]
      · have hbij : ∀ (φ : EuclideanSpace ℂ P),
            ∑ p ∈ Finset.univ.filter (fun p => p ∈ Set.range j), ‖φ.ofLp p‖ ^ 2 =
              ∑ a : A, ‖φ.ofLp (j a)‖ ^ 2 := fun φ =>
          (Finset.sum_nbij' (fun a => j a)
            (fun p => if hp : p ∈ Set.range j then (Equiv.ofInjective j j.injective).symm ⟨p, hp⟩
              else a₀)
            (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Set.mem_range_self a⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun a _ => by
              simp only [Set.mem_range_self, ↓reduceDIte]
              exact (Equiv.ofInjective j j.injective).symm_apply_apply a)
            (fun p hp => by
              have hmem : p ∈ Set.range j := (Finset.mem_filter.mp hp).2
              simp only [hmem, ↓reduceDIte]
              exact congrArg Subtype.val
                ((Equiv.ofInjective j j.injective).apply_symm_apply ⟨p, hmem⟩))
            (fun _ _ => rfl)).symm
        rw [hbij (act U ψ), hbij ψ]
        simp_rw [hact_emb]
        have hsq := congrArg (· ^ 2) (U.norm_map (WithLp.toLp 2 fun a => ψ.ofLp (j a)))
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hsq
        exact hsq
    · refine sum_congr rfl fun p hp => ?_
      rw [hact_rest _ _ _ (Finset.mem_filter.mp hp).2]
  exact
    { toFun := act U
      invFun := act U.symm
      map_add' := fun ψ φ => by
        ext p
        by_cases hp : p ∈ Set.range j
        · obtain ⟨a, rfl⟩ := hp
          rw [PiLp.add_apply, hact_emb, hact_emb, hact_emb]
          have hadd : (WithLp.toLp 2 fun a' => (ψ + φ).ofLp (j a')) =
              (WithLp.toLp 2 fun a' => ψ.ofLp (j a')) +
                (WithLp.toLp 2 fun a' => φ.ofLp (j a')) := rfl
          rw [hadd, map_add, PiLp.add_apply]
        · rw [PiLp.add_apply, hact_rest _ _ _ hp, hact_rest _ _ _ hp, hact_rest _ _ _ hp,
            PiLp.add_apply]
      map_smul' := fun c ψ => by
        ext p
        by_cases hp : p ∈ Set.range j
        · obtain ⟨a, rfl⟩ := hp
          rw [PiLp.smul_apply, RingHom.id_apply, hact_emb, hact_emb]
          have hsmul : (WithLp.toLp 2 fun a' => (c • ψ).ofLp (j a')) =
              c • (WithLp.toLp 2 fun a' => ψ.ofLp (j a')) := rfl
          rw [hsmul, map_smul, PiLp.smul_apply]
        · rw [PiLp.smul_apply, RingHom.id_apply, hact_rest _ _ _ hp, hact_rest _ _ _ hp,
            PiLp.smul_apply]
      left_inv := hact_inv U
      right_inv := fun ψ => by simpa using hact_inv U.symm ψ
      norm_map' := hnorm }

theorem directSumUnitary_apply_emb {A P : Type*} [Fintype A] [Fintype P]
    (j : A ↪ P) (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ P) (a : A) :
    (directSumUnitary j U ψ).ofLp (j a) =
      (U (WithLp.toLp 2 fun a' => ψ.ofLp (j a'))).ofLp a := by
  classical
  unfold directSumUnitary
  have ha : j a ∈ Set.range j := Set.mem_range_self a
  simp only [LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, ha, ↓reduceDIte]
  exact congrArg _ ((Equiv.ofInjective j j.injective).symm_apply_apply a)

theorem directSumUnitary_apply_of_not_mem {A P : Type*} [Fintype A] [Fintype P]
    (j : A ↪ P) (U : EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (ψ : EuclideanSpace ℂ P) {p : P} (hp : p ∉ Set.range j) :
    (directSumUnitary j U ψ).ofLp p = ψ.ofLp p := by
  classical
  unfold directSumUnitary
  simp only [LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp, hp, ↓reduceDIte]

/-- Extend any `LinearIsometry` `L : ℂ^κ →ₗᵢ[ℂ] ℂ^ι` along an injection `j : κ ↪ ι` into a
unitary `U : ℂ^ι ≃ₗᵢ[ℂ] ℂ^ι` satisfying `U (ket (j k)) = L (ket k)`. -/
theorem exists_unitary_extension_of_linearIsometry {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] [DecidableEq ι] (j : κ ↪ ι)
    (L : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    ∃ U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι,
      ∀ k : κ, U (ket (j k)) = L (ket k) := by
  classical
  set v : ι → EuclideanSpace ℂ ι := fun p =>
    if h : p ∈ Set.range j then L (ket ((Equiv.ofInjective j j.injective).symm ⟨p, h⟩))
    else 0
  have hvj : ∀ k : κ, v (j k) = L (ket k) := fun k => by
    have hk : j k ∈ Set.range j := Set.mem_range_self k
    simp only [v, hk, ↓reduceDIte]
    congr 2
    exact (Equiv.ofInjective j j.injective).symm_apply_apply k
  have horth_k : Orthonormal ℂ (fun k : κ => L (ket k)) := by
    rw [orthonormal_iff_ite]
    intro k₁ k₂
    rw [L.inner_map_map, ket, ket, EuclideanSpace.inner_single_left, PiLp.single_apply]
    simp
  have horth : Orthonormal ℂ ((Set.range j).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
    obtain ⟨k₁, rfl⟩ := hp₁
    obtain ⟨k₂, rfl⟩ := hp₂
    simp only [Set.domRestrict_apply, hvj]
    rw [(orthonormal_iff_ite.mp horth_k) k₁ k₂]
    by_cases hk : k₁ = k₂
    · subst hk; simp
    · have hne : (⟨j k₁, Set.mem_range_self k₁⟩ : Set.range j) ≠
          ⟨j k₂, Set.mem_range_self k₂⟩ := fun h =>
        hk (j.injective (congrArg Subtype.val h))
      simp [hk, hne]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  let U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    (EuclideanSpace.basisFun ι ℂ).equiv b (Equiv.refl ι)
  refine ⟨U, fun k => ?_⟩
  have hket : ket (j k) = EuclideanSpace.basisFun ι ℂ (j k) := by
    ext p
    simp [ket, EuclideanSpace.basisFun_apply]
  rw [hket, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
  simpa [hvj] using hb (j k) (Set.mem_range_self k)

private noncomputable def unitScalarIsometry {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    EuclideanSpace ℂ Unit →ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun c := (c.ofLp ()) • v
  map_add' c₁ c₂ := by
    change (c₁.ofLp () + c₂.ofLp ()) • v = c₁.ofLp () • v + c₂.ofLp () • v
    exact add_smul _ _ _
  map_smul' r c := by
    change (r * c.ofLp ()) • v = r • (c.ofLp () • v)
    exact mul_smul _ _ _
  norm_map' c := by
    change ‖c.ofLp () • v‖ = ‖c‖
    rw [norm_smul, hv, mul_one]
    have hsq : ‖c‖ ^ 2 = ‖c.ofLp ()‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_unique]
    exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).symm

/-- Unitary mapping a fixed basis state `ket p₀` to an arbitrary unit state `v`. -/
noncomputable def prepareUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p₀ : ι) (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  (exists_unitary_extension_of_linearIsometry
    ⟨fun _ : Unit => p₀, fun _ _ _ => rfl⟩ (unitScalarIsometry v hv)).choose

theorem prepareUnitary_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p₀ : ι) (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    prepareUnitary p₀ v hv (ket p₀) = v := by
  let emb : Unit ↪ ι := ⟨fun _ : Unit => p₀, fun _ _ _ => rfl⟩
  have h :=
    (exists_unitary_extension_of_linearIsometry emb (unitScalarIsometry v hv)).choose_spec ()
  have hket : ket (emb ()) = ket p₀ := rfl
  have hrhs : unitScalarIsometry v hv (ket ()) = v := by
    change (ket () : EuclideanSpace ℂ Unit).ofLp () • v = v
    simp [ket]
  rw [hket, hrhs] at h
  exact h

/-- Fiberwise unitary lifting along an equivalence `e : P ≃ B × A`: applies `F b` on fiber `b`. -/
noncomputable def fiberUnitary {P B A : Type*} [Fintype P] [Fintype B] [Fintype A]
    (e : P ≃ B × A) (F : B → (EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ P where
  toFun ψ := WithLp.toLp 2 fun p =>
    (F (e p).1 (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a)))).ofLp (e p).2
  invFun ψ := WithLp.toLp 2 fun p =>
    ((F (e p).1).symm (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a)))).ofLp (e p).2
  map_add' ψ φ := by
    ext p
    have hadd : (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a)) +
          φ.ofLp (e.symm ((e p).1, a))) =
        (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a))) +
          (WithLp.toLp 2 fun a => φ.ofLp (e.symm ((e p).1, a))) := rfl
    change ((F (e p).1) (WithLp.toLp 2 fun a =>
        ψ.ofLp (e.symm ((e p).1, a)) + φ.ofLp (e.symm ((e p).1, a)))).ofLp (e p).2 = _
    rw [hadd, map_add]; rfl
  map_smul' c ψ := by
    ext p
    have hsmul : (WithLp.toLp 2 fun a => c * ψ.ofLp (e.symm ((e p).1, a))) =
        c • (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a))) := rfl
    change ((F (e p).1) (WithLp.toLp 2 fun a =>
        c * ψ.ofLp (e.symm ((e p).1, a)))).ofLp (e p).2 = _
    rw [hsmul, map_smul]; rfl
  left_inv ψ := by
    ext p
    have harg : (WithLp.toLp 2 fun a =>
        (F (e (e.symm ((e p).1, a))).1
          (WithLp.toLp 2 fun a' => ψ.ofLp (e.symm ((e (e.symm ((e p).1, a))).1, a')))).ofLp
          (e (e.symm ((e p).1, a))).2) =
        F (e p).1 (WithLp.toLp 2 fun a' => ψ.ofLp (e.symm ((e p).1, a'))) := by
      ext a; simp only [e.apply_symm_apply]
    simp only [WithLp.ofLp_toLp, harg, LinearIsometryEquiv.symm_apply_apply, e.symm_apply_apply]
  right_inv ψ := by
    ext p
    have harg : (WithLp.toLp 2 fun a =>
        ((F (e (e.symm ((e p).1, a))).1).symm
          (WithLp.toLp 2 fun a' => ψ.ofLp (e.symm ((e (e.symm ((e p).1, a))).1, a')))).ofLp
          (e (e.symm ((e p).1, a))).2) =
        (F (e p).1).symm (WithLp.toLp 2 fun a' => ψ.ofLp (e.symm ((e p).1, a'))) := by
      ext a; simp only [e.apply_symm_apply]
    simp only [WithLp.ofLp_toLp, harg, LinearIsometryEquiv.apply_symm_apply, e.symm_apply_apply]
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Equiv.sum_comp e.symm (fun p => ‖_‖ ^ 2), ← Equiv.sum_comp e.symm (fun p => ‖ψ.ofLp p‖ ^ 2),
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun b _ => ?_
    have hsq := congrArg (· ^ 2) ((F b).norm_map (WithLp.toLp 2 fun a => ψ.ofLp (e.symm (b, a))))
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hsq
    simpa [e.apply_symm_apply] using hsq

@[simp]
theorem fiberUnitary_apply {P B A : Type*} [Fintype P] [Fintype B] [Fintype A]
    (e : P ≃ B × A) (F : B → (EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A))
    (ψ : EuclideanSpace ℂ P) (p : P) :
    (fiberUnitary e F ψ).ofLp p =
      (F (e p).1 (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a)))).ofLp (e p).2 := by
  unfold fiberUnitary; rfl

@[simp]
theorem fiberUnitary_symm_apply {P B A : Type*} [Fintype P] [Fintype B] [Fintype A]
    (e : P ≃ B × A) (F : B → (EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ A))
    (ψ : EuclideanSpace ℂ P) (p : P) :
    ((fiberUnitary e F).symm ψ).ofLp p =
      ((F (e p).1).symm (WithLp.toLp 2 fun a => ψ.ofLp (e.symm ((e p).1, a)))).ofLp (e p).2 := by
  unfold fiberUnitary; rfl

/-- Equivalence permuting the basis of `EuclideanSpace ℂ` as a unitary. -/
noncomputable def permUnitary {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp]
theorem permUnitary_apply {ι : Type*} [Fintype ι] (e : Equiv.Perm ι)
    (ψ : EuclideanSpace ℂ ι) (p : ι) :
    (permUnitary e ψ).ofLp p = ψ.ofLp (e.symm p) := by
  unfold permUnitary; rfl

end UnitaryHelpers

/-! ### Modular-addition quantum query model and exact query complexity -/

section Model

/-- Per-bit modular-addition unitary step on `ZMod d`: `|b⟩ ↦ |b + x_i⟩`. -/
noncomputable def modAddStep (d : ℕ) [NeZero d] (bit : Bool) :
    EuclideanSpace ℂ (ZMod d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod d) :=
  addStep (if bit then (1 : ZMod d) else 0)

@[simp]
theorem modAddStep_apply (d : ℕ) [NeZero d] (bit : Bool)
    (φ : EuclideanSpace ℂ (ZMod d)) (b : ZMod d) :
    (modAddStep d bit φ).ofLp b = φ.ofLp (b - if bit then (1 : ZMod d) else 0) := by
  simp [modAddStep]

theorem modAddStep_ket (d : ℕ) [NeZero d] (bit : Bool) (b : ZMod d) :
    modAddStep d bit (ket b) = ket (b + if bit then (1 : ZMod d) else 0) :=
  addStep_ket _ _

/-- The modular-addition quantum query oracle `O_x |i, b, w⟩ = |i, b + x_i, w⟩` on
`ValueState (Fin n) (ZMod d) W`. -/
noncomputable def modAddOracle {n : ℕ} (d : ℕ) [NeZero d] {W : Type*} [Fintype W]
    (x : BitString n) :
    ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W :=
  valueOracle (modAddStep d) x

/-- Unfolding lemma for `runValue` with `modAddStep` at `t = 0`. -/
theorem runValue_modAddStep_zero {n d : ℕ} [NeZero d] {W : Type*} [Fintype W]
    (U : ℕ → ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W)
    (ψ₀ : ValueState (Fin n) (ZMod d) W) (x : BitString n) :
    runValue (modAddStep d) (fun s => (U s).toLinearIsometry) ψ₀ x 0 = U 0 ψ₀ := rfl

/-- Unfolding lemma for `runValue` with `modAddStep` at `t + 1`. -/
theorem runValue_modAddStep_succ {n d : ℕ} [NeZero d] {W : Type*} [Fintype W]
    (U : ℕ → ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W)
    (ψ₀ : ValueState (Fin n) (ZMod d) W) (x : BitString n) (t : ℕ) :
    runValue (modAddStep d) (fun s => (U s).toLinearIsometry) ψ₀ x (t + 1) =
      U (t + 1) (modAddOracle d x
        (runValue (modAddStep d) (fun s => (U s).toLinearIsometry) ψ₀ x t)) := by
  unfold modAddOracle; rfl

@[simp]
theorem modAddOracle_apply {n : ℕ} (d : ℕ) [NeZero d] {W : Type*} [Fintype W]
    (x : BitString n) (ψ : ValueState (Fin n) (ZMod d) W) (i : Fin n) (b : ZMod d) (w : W) :
    (modAddOracle d x ψ).ofLp (i, b, w) =
      ψ.ofLp (i, b - (if x i then (1 : ZMod d) else 0), w) := by
  simp [modAddOracle, modAddStep]

/-- Phase-kickback identity for `modAddStep`: conjugating by `qftEquiv d` diagonalizes
`modAddStep d bit` with eigenvalue `ZMod.stdAddChar (b * bit)`. -/
theorem qft_modAddStep_qft_symm (d : ℕ) [NeZero d] (bit : Bool)
    (φ : EuclideanSpace ℂ (ZMod d)) (b : ZMod d) :
    (qftEquiv d (modAddStep d bit ((qftEquiv d).symm φ))).ofLp b =
      (if bit then ZMod.stdAddChar b else 1) * φ.ofLp b := by
  have h1 : ∀ k : ZMod d,
      (modAddStep d bit ((qftEquiv d).symm φ)).ofLp k =
        ∑ r : ZMod d, (((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
          ZMod.stdAddChar (-((k - (if bit then (1 : ZMod d) else 0)) * r)) * φ.ofLp r := by
    intro k
    rw [modAddStep_apply, qftEquiv_symm_apply]
  rw [qftEquiv_apply]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hstep : ∀ r : ZMod d,
      (∑ k : ZMod d, (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (b * k) *
        ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
          ZMod.stdAddChar (-((k - (if bit then (1 : ZMod d) else 0)) * r)) * φ.ofLp r)) =
      (if b = r then (if bit then ZMod.stdAddChar b else 1) * φ.ofLp r else 0) := fun r => by
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have hterm : ∀ k : ZMod d,
        (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (b * k) *
          ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
            ZMod.stdAddChar (-((k - (if bit then (1 : ZMod d) else 0)) * r)) * φ.ofLp r) =
        ((d : ℂ)⁻¹ * ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * r) * φ.ofLp r) *
          ZMod.stdAddChar (k * (b - r)) := fun k => by
      have hsq := sqrt_inv_mul_sqrt_inv d
      have hadd : ZMod.stdAddChar (b * k) *
          ZMod.stdAddChar (-((k - (if bit then (1 : ZMod d) else 0)) * r)) =
          ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * r) *
            ZMod.stdAddChar (k * (b - r)) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1; ring
      calc
        (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (b * k) *
            ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) *
              ZMod.stdAddChar (-((k - (if bit then (1 : ZMod d) else 0)) * r)) * φ.ofLp r) =
          ((((Real.sqrt d)⁻¹ : ℝ) : ℂ) * (((Real.sqrt d)⁻¹ : ℝ) : ℂ)) *
            (ZMod.stdAddChar (b * k) *
              ZMod.stdAddChar (-((k - (if bit then (1 : ZMod d) else 0)) * r))) * φ.ofLp r := by
            ring
        _ = (d : ℂ)⁻¹ *
            (ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * r) *
              ZMod.stdAddChar (k * (b - r))) * φ.ofLp r := by rw [hsq, hadd]
        _ = _ := by ring
    simp_rw [hterm, ← Finset.mul_sum]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d), ZMod.card]
    by_cases hbr : b = r
    · subst hbr
      simp only [sub_self, ↓reduceIte]
      have hcancel : (d : ℂ)⁻¹ * ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * b) *
          φ.ofLp b * (d : ℂ) =
          ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * b) * φ.ofLp b := by
        calc
          (d : ℂ)⁻¹ * ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * b) *
              φ.ofLp b * (d : ℂ) =
            ((d : ℂ)⁻¹ * (d : ℂ)) *
              (ZMod.stdAddChar ((if bit then (1 : ZMod d) else 0) * b) * φ.ofLp b) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]
      rw [hcancel]
      cases bit <;> simp
    · have hne : b - r ≠ 0 := sub_ne_zero.mpr hbr
      simp [hbr, hne]
  simp_rw [hstep]
  rw [Finset.sum_ite_eq Finset.univ b]
  simp

/-- A `T`-query quantum query algorithm on `n`-bit strings with answer-register modulus `d`,
finite workspace `W`, and output alphabet `X`. -/
structure QuantumQueryAlgorithm (n d : ℕ) [NeZero d] (W X : Type*)
    [Fintype W] [DecidableEq W] [Fintype X] (T : ℕ) where
  /-- Initial quantum state `|ψ₀⟩`. -/
  init : ValueState (Fin n) (ZMod d) W
  /-- The initial state has unit norm. -/
  norm_init : ‖init‖ = 1
  /-- Sequence of input-independent unitaries `U_0, ..., U_T`. -/
  unitary : ℕ → ValueState (Fin n) (ZMod d) W ≃ₗᵢ[ℂ] ValueState (Fin n) (ZMod d) W
  /-- Final POVM measurement `{E_a}_{a ∈ X}`. -/
  povm : POVM X (Fin n × ZMod d × W)

namespace QuantumQueryAlgorithm

variable {n d T : ℕ} [NeZero d] {W X : Type*} [Fintype W] [DecidableEq W] [Fintype X]

/-- The final state `|ψ_x⟩ = U_T O_x U_{T-1} ... O_x U_0 |ψ₀⟩` after `T` queries. -/
@[expose]
noncomputable def finalState (A : QuantumQueryAlgorithm n d W X T) (x : BitString n) :
    ValueState (Fin n) (ZMod d) W :=
  runValue (modAddStep d) (fun t => (A.unitary t).toLinearIsometry) A.init x T

/-- The final state of a quantum query algorithm always has unit norm. -/
theorem norm_finalState (A : QuantumQueryAlgorithm n d W X T) (x : BitString n) :
    ‖A.finalState x‖ = 1 := by
  rw [finalState, norm_runValue, A.norm_init]

/-- The probability `⟨ψ_x | E_a | ψ_x⟩` of outputting `a` on input `x`. -/
@[expose]
noncomputable def prob (A : QuantumQueryAlgorithm n d W X T) (x : BitString n) (a : X) : ℝ :=
  A.povm.prob (A.finalState x) a

/-- `A` computes `f : BitString n → X` exactly if `A` outputs `f x` with probability `1` on
every input `x`. -/
@[expose]
def ComputesExactly (A : QuantumQueryAlgorithm n d W X T) (f : BitString n → X) : Prop :=
  ∀ x : BitString n, A.prob x (f x) = 1

end QuantumQueryAlgorithm

/-- `f : BitString n → X` is exactly computable in `T` quantum queries with modulus `d`. -/
@[expose]
def ExactQuantumComputableInMod {n : ℕ} (d : ℕ) [NeZero d] {X : Type*} [Fintype X]
    (f : BitString n → X) (T : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QuantumQueryAlgorithm n d W X T),
    A.ComputesExactly f

/-- `f : BitString n → X` is exactly computable in `T` quantum queries (for some positive
answer-register modulus `d` and finite workspace `W`). -/
@[expose]
def ExactQuantumComputableIn {n : ℕ} {X : Type*} [Fintype X]
    (f : BitString n → X) (T : ℕ) : Prop :=
  ∃ (d : ℕ) (_ : NeZero d), ExactQuantumComputableInMod d f T

/-- The exact quantum query complexity `Q_E(f)` of `f : BitString n → X`. -/
noncomputable def exactQuantumQueryComplexity {n : ℕ} {X : Type*} [Fintype X]
    (f : BitString n → X) : ℕ :=
  sInf {T : ℕ | ExactQuantumComputableIn f T}

theorem exactQuantumQueryComplexity_le {n : ℕ} {X : Type*} [Fintype X]
    {f : BitString n → X} {T : ℕ} (h : ExactQuantumComputableIn f T) :
    exactQuantumQueryComplexity f ≤ T :=
  Nat.sInf_le h

theorem le_exactQuantumQueryComplexity {n : ℕ} {X : Type*} [Fintype X]
    {f : BitString n → X} {k : ℕ}
    (hne : ∃ T, ExactQuantumComputableIn f T)
    (h : ∀ T, ExactQuantumComputableIn f T → k ≤ T) :
    k ≤ exactQuantumQueryComplexity f :=
  le_csInf hne h

end Model

/-! ### Amplitude-polynomial orthogonality lower-bound method -/

section LowerBounds

/-- For a positive semidefinite matrix `E`, `⟨ψ | E | ψ⟩ = 0` implies `E ψ = 0`. -/
private theorem mulVec_eq_zero_of_posSemidef_of_re_eq_zero {ι : Type*} [Fintype ι]
    {E : Matrix ι ι ℂ} (hE : E.PosSemidef) {v : ι → ℂ}
    (hv : (star v ⬝ᵥ (E *ᵥ v)).re = 0) : E *ᵥ v = 0 := by
  classical
  let U : Matrix ι ι ℂ := (hE.1.eigenvectorUnitary : Matrix ι ι ℂ)
  set lam : ι → ℝ := hE.1.eigenvalues
  have hlam : ∀ k, 0 ≤ lam k := hE.eigenvalues_nonneg
  have hEspec : E = U * diagonal (fun k => (lam k : ℂ)) * Uᴴ := by
    conv_lhs => rw [hE.1.spectral_theorem]
    simp [U, lam, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]
  set w : ι → ℂ := Uᴴ *ᵥ v
  have hquad : (star v ⬝ᵥ (E *ᵥ v)).re = ∑ k : ι, lam k * ‖w k‖ ^ 2 := by
    have h1 : star v ⬝ᵥ (E *ᵥ v) = star w ⬝ᵥ (diagonal (fun k => (lam k : ℂ)) *ᵥ w) := by
      have hEv : E *ᵥ v = U *ᵥ (diagonal (fun k => (lam k : ℂ)) *ᵥ w) := by
        rw [hEspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hstar : star v ᵥ* U = star w := by
        rw [show w = Uᴴ *ᵥ v from rfl, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [hEv, Matrix.dotProduct_mulVec, hstar]
    rw [h1, dotProduct, Complex.re_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec_diagonal, Pi.star_apply]
    have hconj : star (w k) * ((lam k : ℂ) * w k) = ((lam k * ‖w k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
    rw [hconj, Complex.ofReal_re]
  rw [hquad] at hv
  have hterm_zero : ∀ k : ι, lam k * ‖w k‖ ^ 2 = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hlam j) (sq_nonneg _)).mp hv k
      (mem_univ k)
  have hdw : diagonal (fun k => (lam k : ℂ)) *ᵥ w = 0 := by
    ext k
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply]
    rcases mul_eq_zero.mp (hterm_zero k) with hk | hk
    · simp [hk]
    · have : w k = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hk)
      simp [this]
  rw [hEspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, show Uᴴ *ᵥ v = w from rfl, hdw,
    Matrix.mulVec_zero]

/-- **Exactness implies orthogonality**: if a quantum query algorithm computes `f` exactly,
then final states for inputs with distinct outputs are orthogonal. -/
theorem inner_finalState_eq_zero_of_ne {n d T : ℕ} [NeZero d] {W X : Type*}
    [Fintype W] [DecidableEq W] [Fintype X]
    {A : QuantumQueryAlgorithm n d W X T} {f : BitString n → X}
    (hA : A.ComputesExactly f) {x y : BitString n} (hxy : f x ≠ f y) :
    @inner ℂ _ _ (A.finalState x) (A.finalState y) = 0 := by
  classical
  have hprob_sum : ∀ z a, a ≠ f z → A.prob z a = 0 := fun z a ha => by
    have hsum : ∑ b : X, A.prob z b = 1 := by
      have hs := A.povm.sum_prob (A.finalState z)
      rw [A.norm_finalState z, one_pow] at hs
      exact hs
    have hfz : A.prob z (f z) = 1 := hA z
    have hrest : ∑ b ∈ Finset.univ.erase (f z), A.prob z b = 0 := by
      have h1 := Finset.add_sum_erase Finset.univ (A.prob z) (Finset.mem_univ (f z))
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
      A.povm.prob_nonneg (A.finalState z) b).mp hrest a (Finset.mem_erase.mpr ⟨ha, mem_univ a⟩)
  have hEyx : A.povm.effect (f y) *ᵥ (A.finalState x).ofLp = 0 :=
    mulVec_eq_zero_of_posSemidef_of_re_eq_zero (A.povm.posSemidef (f y))
      (hprob_sum x (f y) hxy.symm)
  have hEyy : A.povm.effect (f y) *ᵥ (A.finalState y).ofLp = (A.finalState y).ofLp := by
    have hsum_vec : ∑ a : X, A.povm.effect a *ᵥ (A.finalState y).ofLp =
        (A.finalState y).ofLp := by
      rw [← Matrix.sum_mulVec, A.povm.sum_effect, Matrix.one_mulVec]
    have hsingle : ∑ a : X, A.povm.effect a *ᵥ (A.finalState y).ofLp =
        A.povm.effect (f y) *ᵥ (A.finalState y).ofLp :=
      Finset.sum_eq_single_of_mem (f y) (mem_univ _) fun a _ ha =>
        mulVec_eq_zero_of_posSemidef_of_re_eq_zero (A.povm.posSemidef a) (hprob_sum y a ha)
    exact hsingle.symm.trans hsum_vec
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, ← hEyy,
    Matrix.dotProduct_mulVec, ← (A.povm.posSemidef (f y)).isHermitian.eq, ← Matrix.star_mulVec,
    hEyx, star_zero, zero_dotProduct]

/-- **Amplitude degree bound for arbitrary Boolean value oracles**: after `t` queries to any
two-valued unitary value oracle on `BitString n`, every computational-basis amplitude of the
state has complex multilinear degree at most `t`. -/
theorem amplitude_mem_lowDegree_valueOracle {n : ℕ} {V W : Type*} [Fintype V] [Fintype W]
    (step : Bool → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState (Fin n) V W →ₗᵢ[ℂ] ValueState (Fin n) V W)
    (ψ₀ : ValueState (Fin n) V W) (t : ℕ) (p : Fin n × V × W) :
    (fun x : BitString n => (runValue step U ψ₀ x t).ofLp p) ∈ lowDegree ℂ (Fin n) t := by
  classical
  have hlin : ∀ (L : ValueState (Fin n) V W →ₗ[ℂ] ValueState (Fin n) V W)
      (ψ : ValueState (Fin n) V W) (q : Fin n × V × W),
      (L ψ).ofLp q = ∑ r, (L (EuclideanSpace.single r 1)).ofLp q * ψ.ofLp r := fun L ψ q => by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n × V × W) ℂ).sum_repr ψ]
    simp [map_sum, map_smul, mul_comm]
  induction t generalizing p with
  | zero => exact const_mem_lowDegree (R := ℂ) (ι := Fin n) 0 ((U 0 ψ₀).ofLp p)
  | succ t ih =>
    have hEq : (fun x : BitString n => (runValue step U ψ₀ x (t + 1)).ofLp p) =
        ∑ q : Fin n × V × W, fun x =>
          (U (t + 1) (EuclideanSpace.single q 1)).ofLp p *
            (valueOracle step x (runValue step U ψ₀ x t)).ofLp q := by
      funext x
      have h1 := hlin (U (t + 1)).toLinearMap (valueOracle step x (runValue step U ψ₀ x t)) p
      simp only [LinearIsometry.coe_toLinearMap] at h1
      simp only [runValue, Finset.sum_apply, h1]
    rw [hEq]
    refine sum_mem_lowDegree _ fun q _ => ?_
    rcases q with ⟨i, v, w⟩
    have hvo : (fun x : BitString n =>
          (valueOracle step x (runValue step U ψ₀ x t)).ofLp (i, v, w)) =
        ∑ v' : V,
          ((fun x => (step false (EuclideanSpace.single v' 1)).ofLp v * (1 - bitVal ℂ (x i)) +
            (step true (EuclideanSpace.single v' 1)).ofLp v * bitVal ℂ (x i)) *
            fun x => (runValue step U ψ₀ x t).ofLp (i, v', w)) := by
      funext x
      simp only [Finset.sum_apply, Pi.mul_apply, valueOracle_apply]
      have hlinV : ∀ (L : EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V)
          (φ : EuclideanSpace ℂ V),
          (L φ).ofLp v = ∑ v' : V, (L (EuclideanSpace.single v' 1)).ofLp v * φ.ofLp v' :=
        fun L φ => by
          conv_lhs => rw [← (EuclideanSpace.basisFun V ℂ).sum_repr φ]
          simp [map_sum, map_smul, mul_comm]
      have hsub := hlinV (step (x i)).toLinearEquiv.toLinearMap
        (WithLp.toLp 2 fun v' => (runValue step U ψ₀ x t).ofLp (i, v', w))
      simp only [LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv] at hsub
      rw [hsub]
      refine sum_congr rfl fun v' _ => ?_
      cases x i <;> simp [bitVal]
    have hmem : (fun x : BitString n =>
        (valueOracle step x (runValue step U ψ₀ x t)).ofLp (i, v, w)) ∈
        lowDegree ℂ (Fin n) (t + 1) := by
      rw [hvo]
      refine sum_mem_lowDegree _ fun v' _ => ?_
      have h1 : (fun x : BitString n =>
          (step false (EuclideanSpace.single v' 1)).ofLp v * (1 - bitVal ℂ (x i)) +
          (step true (EuclideanSpace.single v' 1)).ofLp v * bitVal ℂ (x i)) ∈
          lowDegree ℂ (Fin n) 1 := by
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem _ ((step false (EuclideanSpace.single v' 1)).ofLp v)
            (one_sub_mem_lowDegree (bitVal_mem_lowDegree (R := ℂ) i))
        · exact Submodule.smul_mem _ ((step true (EuclideanSpace.single v' 1)).ofLp v)
            (bitVal_mem_lowDegree (R := ℂ) i)
      have hprod := mul_mem_lowDegree h1 (ih (i, v', w))
      rwa [Nat.add_comm 1 t] at hprod
    exact Submodule.smul_mem _ ((U (t + 1) (EuclideanSpace.single (i, v, w) 1)).ofLp p) hmem

/-- **Inner-product degree bound**: fixing a reference input `y`, the overlap
`x ↦ ⟨ψ_y | ψ_x⟩` of an exact `T`-query algorithm has complex multilinear degree at most `T`. -/
theorem inner_finalState_mem_lowDegree {n d T : ℕ} [NeZero d] {W X : Type*}
    [Fintype W] [DecidableEq W] [Fintype X] (A : QuantumQueryAlgorithm n d W X T)
    (y : BitString n) :
    (fun x : BitString n => @inner ℂ _ _ (A.finalState y) (A.finalState x)) ∈
      lowDegree ℂ (Fin n) T := by
  have h : (fun x : BitString n => @inner ℂ _ _ (A.finalState y) (A.finalState x)) =
      ∑ p : Fin n × ZMod d × W,
        star ((A.finalState y).ofLp p) • fun x => (A.finalState x).ofLp p := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PiLp.inner_apply,
      RCLike.inner_apply, Complex.star_def]
    exact sum_congr rfl fun p _ => mul_comm _ _
  rw [h]
  refine sum_mem_lowDegree _ fun p _ => Submodule.smul_mem _ _ ?_
  exact amplitude_mem_lowDegree_valueOracle (modAddStep d)
    (fun t => (A.unitary t).toLinearIsometry) A.init T p

/-- A nonzero univariate polynomial over `ℂ` has degree at least the cardinality of any
finite set of distinct natural-number roots. -/
private theorem card_le_natDegree_of_eval_eq_zero {p : ℂ[X]} (hp : p ≠ 0)
    (R : Finset ℕ) (hR : ∀ k ∈ R, p.eval (k : ℂ) = 0) :
    R.card ≤ p.natDegree := by
  have hsub : (R.image (Nat.cast : ℕ → ℂ)).val ⊆ p.roots := by
    intro z hz
    rw [Finset.mem_val, Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    exact (Polynomial.mem_roots hp).mpr (hR k hk)
  have hcard : (R.image (Nat.cast : ℕ → ℂ)).card ≤ p.roots.card :=
    Multiset.card_le_card (Multiset.le_iff_subset (R.image _).nodup |>.mpr hsub)
  rw [Finset.card_image_of_injective R Nat.cast_injective] at hcard
  exact hcard.trans (Polynomial.card_roots' p)

/-- **Subcube root-counting lower bound at weight `0`**: for any affine-degree-1 map
`φ : BitString k → BitString n`, if every `z : BitString k` of weight `w ∈ R` (`R ⊆ {0, ..., k}`)
satisfies `f (φ z) ≠ f (φ 0^k)`, then `R.card ≤ T` for every exact `T`-query algorithm
computing `f`. -/
theorem card_le_of_exact_subcube_zero {k n T : ℕ} {X : Type*} [Fintype X]
    {f : BitString n → X} (h : ExactQuantumComputableIn f T)
    (φ : BitString k → BitString n)
    (hφ : ∀ i : Fin n, (fun z : BitString k => bitVal ℂ (φ z i)) ∈ lowDegree ℂ (Fin k) 1)
    (R : Finset ℕ) (hRle : ∀ w ∈ R, w ≤ k)
    (hRne : ∀ w ∈ R, ∀ z : BitString k, weight z = w →
      f (φ z) ≠ f (φ (fun _ => false))) :
    R.card ≤ T := by
  classical
  obtain ⟨d, hd, W, hW, hWdec, A, hA⟩ := h
  let g : BitString k → ℂ :=
    fun z => @inner ℂ _ _ (A.finalState (φ (fun _ => false))) (A.finalState (φ z))
  have hg : g ∈ lowDegree ℂ (Fin k) T :=
    comp_mem_lowDegree hφ (inner_finalState_mem_lowDegree A (φ (fun _ => false)))
  obtain ⟨q, hqdeg, hqval⟩ := exists_natDegree_le_eval_eq_layerAverage hg
  have hq0 : q.eval (0 : ℂ) = 1 := by
    have h0 := hqval 0 (Nat.zero_le _)
    have havg : layerAverage g 0 = 1 := by
      have hset : ({z : BitString k | weight z = 0} : Finset (BitString k)) =
          {fun _ => false} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hw; funext i; by_contra hzi
          have htrue : z i = true := by cases hz : z i <;> simp_all
          have hpos : 0 < weight z := Finset.card_pos.mpr ⟨i, by simp [htrue]⟩
          omega
        · rintro rfl; simp [weight]
      rw [layerAverage, hset, Finset.expect_singleton]
      simp only [g, inner_self_eq_norm_sq_to_K, A.norm_finalState]
      norm_num
    simpa [havg] using h0
  have hq_ne : q ≠ 0 := fun h0 => by simp [h0] at hq0
  have hroots : ∀ w ∈ R, q.eval (w : ℂ) = 0 := fun w hw => by
    rw [hqval w (by simpa using hRle w hw), layerAverage]
    refine Finset.expect_eq_zero fun z hz => ?_
    exact inner_finalState_eq_zero_of_ne hA (hRne w hw z (Finset.mem_filter.mp hz).2).symm
  exact (card_le_natDegree_of_eval_eq_zero hq_ne R hroots).trans hqdeg

/-- **Subcube root-counting lower bound at weight `k`**: for any affine-degree-1 map
`φ : BitString k → BitString n`, if every `z : BitString k` of weight `w ∈ R` (`R ⊆ {0, ..., k}`)
satisfies `f (φ z) ≠ f (φ 1^k)`, then `R.card ≤ T` for every exact `T`-query algorithm
computing `f`. -/
theorem card_le_of_exact_subcube_top {k n T : ℕ} {X : Type*} [Fintype X]
    {f : BitString n → X} (h : ExactQuantumComputableIn f T)
    (φ : BitString k → BitString n)
    (hφ : ∀ i : Fin n, (fun z : BitString k => bitVal ℂ (φ z i)) ∈ lowDegree ℂ (Fin k) 1)
    (R : Finset ℕ) (hRle : ∀ w ∈ R, w ≤ k)
    (hRne : ∀ w ∈ R, ∀ z : BitString k, weight z = w →
      f (φ z) ≠ f (φ (fun _ => true))) :
    R.card ≤ T := by
  classical
  obtain ⟨d, hd, W, hW, hWdec, A, hA⟩ := h
  let g : BitString k → ℂ :=
    fun z => @inner ℂ _ _ (A.finalState (φ (fun _ => true))) (A.finalState (φ z))
  have hg : g ∈ lowDegree ℂ (Fin k) T :=
    comp_mem_lowDegree hφ (inner_finalState_mem_lowDegree A (φ (fun _ => true)))
  obtain ⟨q, hqdeg, hqval⟩ := exists_natDegree_le_eval_eq_layerAverage hg
  have hqk : q.eval (k : ℂ) = 1 := by
    have hk := hqval k (by simp)
    have havg : layerAverage g k = 1 := by
      have hset : ({z : BitString k | weight z = k} : Finset (BitString k)) =
          {fun _ => true} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hw
          have hall : ({i : Fin k | z i = true} : Finset (Fin k)) = Finset.univ :=
            Finset.eq_univ_of_card _ (by simpa [weight] using hw)
          funext i
          have : i ∈ ({j : Fin k | z j = true} : Finset (Fin k)) := by rw [hall]; exact mem_univ i
          exact (Finset.mem_filter.mp this).2
        · rintro rfl; simp [weight]
      rw [layerAverage, hset, Finset.expect_singleton]
      simp only [g, inner_self_eq_norm_sq_to_K, A.norm_finalState]
      norm_num
    simpa [havg] using hk
  have hq_ne : q ≠ 0 := fun h0 => by simp [h0] at hqk
  have hroots : ∀ w ∈ R, q.eval (w : ℂ) = 0 := fun w hw => by
    rw [hqval w (by simpa using hRle w hw), layerAverage]
    refine Finset.expect_eq_zero fun z hz => ?_
    exact inner_finalState_eq_zero_of_ne hA (hRne w hw z (Finset.mem_filter.mp hz).2).symm
  exact (card_le_natDegree_of_eval_eq_zero hq_ne R hroots).trans hqdeg

/-- **Root-counting lower bound at weight `0`**: specialization of
`card_le_of_exact_subcube_zero` to the identity map. -/
theorem card_le_of_exact_weight_zero {n T : ℕ} {X : Type*} [Fintype X]
    {f : BitString n → X} (h : ExactQuantumComputableIn f T)
    (R : Finset ℕ) (hRle : ∀ k ∈ R, k ≤ n)
    (hRne : ∀ k ∈ R, ∀ x : BitString n, weight x = k → f x ≠ f (fun _ => false)) :
    R.card ≤ T :=
  card_le_of_exact_subcube_zero h id (fun i => bitVal_mem_lowDegree i) R hRle hRne

/-- **Root-counting lower bound at weight `n`**: specialization of
`card_le_of_exact_subcube_top` to the identity map. -/
theorem card_le_of_exact_weight_top {n T : ℕ} {X : Type*} [Fintype X]
    {f : BitString n → X} (h : ExactQuantumComputableIn f T)
    (R : Finset ℕ) (hRle : ∀ k ∈ R, k ≤ n)
    (hRne : ∀ k ∈ R, ∀ x : BitString n, weight x = k → f x ≠ f (fun _ => true)) :
    R.card ≤ T :=
  card_le_of_exact_subcube_top h id (fun i => bitVal_mem_lowDegree i) R hRle hRne

/-- Fixing coordinates outside an embedding `ι : Fin k ↪ Fin n` to constants is a degree-1
substitution map. -/
theorem bitVal_subcube_mem_lowDegree {k n : ℕ} (ι : Fin k ↪ Fin n) (base : BitString n)
    (i : Fin n) :
    (fun z : BitString k =>
      bitVal ℂ (if hi : i ∈ Set.range ι then
        z ((Equiv.ofInjective ι ι.injective).symm ⟨i, hi⟩)
      else base i)) ∈ lowDegree ℂ (Fin k) 1 := by
  by_cases hi : i ∈ Set.range ι
  · simp only [hi, ↓reduceDIte]
    exact bitVal_mem_lowDegree _
  · simp only [hi, ↓reduceDIte]
    exact const_mem_lowDegree 1 _

end LowerBounds

end CslibFrontier.Quantum
