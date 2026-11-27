/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order

import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Finite-Dimensional Quantum Channels, Choi–Kraus Representation, and Stinespring Dilation

Defines finite-dimensional quantum channels (completely positive trace-preserving linear maps on
complex matrix algebras), the Choi matrix, and proves Choi's PSD theorem, the Choi–Kraus
representation, and Stinespring's isometry and unitary dilation theorems strictly under standard
Lean axioms.

## Main definitions

* `CslibFrontier.Foundations.Quantum.QuantumChannel`: CPTP linear map on finite-dimensional
  complex matrix algebras.
* `CslibFrontier.Foundations.Quantum.choiMatrix`: the Choi matrix `J(Ψ)`.
* `CslibFrontier.Foundations.Quantum.stinespringEquiv`: coordinate permutation for Stinespring
  unitary dilation.

## Main results

* `CslibFrontier.Foundations.Quantum.QuantumChannel.choiMatrix_posSemidef`: Choi's theorem.
* `CslibFrontier.Foundations.Quantum.QuantumChannel.exists_kraus_repr`: Choi–Kraus representation.
* `CslibFrontier.Foundations.Quantum.QuantumChannel.exists_stinespring_isometry`: Stinespring
  isometry dilation.
* `CslibFrontier.Foundations.Quantum.QuantumChannel.exists_stinespring_unitary`: Stinespring
  unitary dilation.
-/

public section

namespace CslibFrontier.Foundations.Quantum

open Matrix Cslib.Quantum
open scoped ComplexOrder Kronecker MatrixOrder

/-- A quantum channel from `L(ℂ^ι)` to `L(ℂ^κ)` is a completely positive, trace-preserving
`ℂ`-linear map between finite-dimensional complex matrix algebras. -/
@[ext]
structure QuantumChannel (ι κ : Type*) [Fintype ι] [Fintype κ] where
  /-- The underlying `ℂ`-linear map `Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ`. -/
  toLinearMap : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ
  /-- Complete positivity: `(id_n ⊗ Ψ)` preserves positive semidefiniteness for every `n : ℕ`. -/
  completely_positive : ∀ (n : ℕ) (X : Matrix (Fin n × ι) (Fin n × ι) ℂ),
    X.PosSemidef →
    (Matrix.of fun (p q : Fin n × κ) ↦
      toLinearMap (Matrix.of fun a b ↦ X (p.1, a) (q.1, b)) p.2 q.2).PosSemidef
  /-- Trace preservation: `Tr(Ψ(X)) = Tr(X)` for all `X`. -/
  trace_preserving : ∀ X : Matrix ι ι ℂ, (toLinearMap X).trace = X.trace

instance {ι κ : Type*} [Fintype ι] [Fintype κ] :
    FunLike (QuantumChannel ι κ) (Matrix ι ι ℂ) (Matrix κ κ ℂ) where
  coe Ψ := Ψ.toLinearMap
  coe_injective _ _ h := QuantumChannel.ext (DFunLike.coe_injective h)

@[simp]
theorem QuantumChannel.toLinearMap_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ψ : QuantumChannel ι κ) (X : Matrix ι ι ℂ) :
    Ψ.toLinearMap X = Ψ X := rfl

theorem QuantumChannel.map_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ψ : QuantumChannel ι κ) (X Y : Matrix ι ι ℂ) : Ψ (X + Y) = Ψ X + Ψ Y :=
  Ψ.toLinearMap.map_add X Y

theorem QuantumChannel.map_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ψ : QuantumChannel ι κ) (c : ℂ) (X : Matrix ι ι ℂ) : Ψ (c • X) = c • Ψ X :=
  Ψ.toLinearMap.map_smul c X

theorem QuantumChannel.trace_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ψ : QuantumChannel ι κ) (X : Matrix ι ι ℂ) : (Ψ X).trace = X.trace :=
  Ψ.trace_preserving X

theorem QuantumChannel.posSemidef_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ψ : QuantumChannel ι κ) {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    (Ψ X).PosSemidef := by
  let X' : Matrix (Fin 1 × ι) (Fin 1 × ι) ℂ := Matrix.of fun p q ↦ X p.2 q.2
  have hX' : X'.PosSemidef := by
    have hXherm := hX.1
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hX ⊢
    refine ⟨?_, fun v ↦ ?_⟩
    · ext p q
      have := hXherm.apply p.2 q.2
      simpa [X', Matrix.conjTranspose_apply] using this
    · have := hX.2 (fun a ↦ v (0, a))
      simpa [X', dotProduct, Matrix.mulVec, Fintype.sum_prod_type] using this
  have hcp := Ψ.completely_positive 1 X' hX'
  have hcpherm := hcp.1
  have hXeq : (Matrix.of fun a b ↦ X' (0, a) (0, b)) = X := by ext a b; rfl
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hcp ⊢
  refine ⟨?_, fun v ↦ ?_⟩
  · ext a b
    have := hcpherm.apply (0, a) (0, b)
    simpa [hXeq, Matrix.conjTranspose_apply] using this
  · have := hcp.2 (fun p ↦ v p.2)
    simpa [hXeq, dotProduct, Matrix.mulVec, Fintype.sum_prod_type] using this

theorem QuantumChannel.isDensityMatrix_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ψ : QuantumChannel ι κ) {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (Ψ ρ) :=
  ⟨Ψ.posSemidef_map hρ.posSemidef, by rw [Ψ.trace_map, hρ.trace_eq_one]⟩

/-- The Choi matrix `J(Ψ) = ∑_{a,b} E_{ab} ⊗ Ψ(E_{ab})` of a linear map
`Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ` on `ι × κ`. -/
noncomputable def choiMatrix {ι κ : Type*} [DecidableEq ι]
    (Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.of fun p q ↦ Ψ (Matrix.single p.1 q.1 (1 : ℂ)) p.2 q.2

/-- **Choi's Theorem (PSD of Choi Matrix)**: The Choi matrix of a quantum channel is positive
semidefinite. -/
theorem QuantumChannel.choiMatrix_posSemidef {d m : ℕ} (Ψ : QuantumChannel (Fin d) (Fin m)) :
    (choiMatrix Ψ.toLinearMap).PosSemidef := by
  let Ω : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    Matrix.of fun p q ↦ if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0
  have hΩ : Ω.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v ↦ ?_⟩
    · ext p q
      simp only [Ω, Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq]
    · have hsum : star v ⬝ᵥ Ω *ᵥ v =
          star (∑ i : Fin d, v (i, i)) * (∑ i : Fin d, v (i, i)) := by
        simp only [dotProduct, Matrix.mulVec, Ω, Matrix.of_apply, Fintype.sum_prod_type]
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_eq_single i]
        · congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.sum_eq_single j]
          · simp
          · intro j' _ hj'; simp [Ne.symm hj']
          · intro hj; exact absurd (Finset.mem_univ j) hj
        · intro i' _ hi'
          have h0 : ∑ j : Fin d, ∑ j' : Fin d,
              (if i = i' ∧ j = j' then (1 : ℂ) else 0) * v (j, j') = 0 :=
            Finset.sum_eq_zero fun j _ ↦ Finset.sum_eq_zero fun j' _ ↦ by
              simp [Ne.symm hi']
          rw [h0, mul_zero]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hsum, Complex.star_def, mul_comm, Complex.mul_conj]
      exact_mod_cast Complex.normSq_nonneg _
  have hcp := Ψ.completely_positive d Ω hΩ
  have hEq : (Matrix.of fun (p q : Fin d × Fin m) ↦
      Ψ.toLinearMap (Matrix.of fun a b ↦ Ω (p.1, a) (q.1, b)) p.2 q.2) =
      choiMatrix Ψ.toLinearMap := by
    ext p q
    simp only [choiMatrix, Matrix.of_apply]
    have hmat : (Matrix.of fun a b ↦ Ω (p.1, a) (q.1, b)) = Matrix.single p.1 q.1 (1 : ℂ) := by
      ext a b
      simp [Ω, Matrix.single, eq_comm]
    rw [hmat]
  rw [← hEq]
  exact hcp

/-- **Choi–Kraus Representation**: Every quantum channel `Ψ : L(ℂ^d) → L(ℂ^m)` admits a Kraus
representation `Ψ(X) = ∑_{r : Fin d × Fin m} K_r X K_rᴴ` with `∑_r K_rᴴ K_r = 1`. -/
theorem QuantumChannel.exists_kraus_repr {d m : ℕ} (Ψ : QuantumChannel (Fin d) (Fin m)) :
    ∃ K : (Fin d × Fin m) → Matrix (Fin m) (Fin d) ℂ,
      (∀ X : Matrix (Fin d) (Fin d) ℂ, Ψ X = ∑ r, K r * X * (K r)ᴴ) ∧
      ∑ r, (K r)ᴴ * K r = 1 := by
  have hJ := Ψ.choiMatrix_posSemidef
  have hJherm := hJ.isHermitian
  let U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ := hJherm.eigenvectorUnitary
  let lam : (Fin d × Fin m) → ℝ := hJherm.eigenvalues
  have hlam : ∀ r, 0 ≤ lam r := hJ.eigenvalues_nonneg
  let K : (Fin d × Fin m) → Matrix (Fin m) (Fin d) ℂ := fun r ↦
    Matrix.of fun b a ↦ (Real.sqrt (lam r) : ℂ) * U (a, b) r
  have hspec_mat : choiMatrix Ψ.toLinearMap =
      U * Matrix.diagonal (fun r ↦ (lam r : ℂ)) * Uᴴ := by
    simpa [U, lam, Matrix.star_eq_conjTranspose, Function.comp_def] using hJherm.spectral_theorem
  have hJ_eq : ∀ a a' : Fin d, ∀ b b' : Fin m,
      Ψ (Matrix.single a a' (1 : ℂ)) b b' = ∑ r, K r b a * star (K r b' a') := by
    intro a a' b b'
    have hspec := congrFun (congrFun hspec_mat (a, b)) (a', b')
    change Ψ (Matrix.single a a' (1 : ℂ)) b b' =
      (U * Matrix.diagonal (fun r ↦ (lam r : ℂ)) * Uᴴ) (a, b) (a', b') at hspec
    rw [hspec, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, K, Matrix.of_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hsq : ((Real.sqrt (lam r) : ℂ) * star (Real.sqrt (lam r) : ℂ)) = (lam r : ℂ) := by
      simp only [Complex.star_def, Complex.conj_ofReal]
      exact_mod_cast Real.mul_self_sqrt (hlam r)
    calc U (a, b) r * (lam r : ℂ) * star (U (a', b') r)
        = ((Real.sqrt (lam r) : ℂ) * star (Real.sqrt (lam r) : ℂ)) * U (a, b) r *
            star (U (a', b') r) := by rw [hsq]; ring
      _ = (Real.sqrt (lam r) : ℂ) * U (a, b) r *
            star ((Real.sqrt (lam r) : ℂ) * U (a', b') r) := by rw [star_mul]; ring
  refine ⟨K, ?_, ?_⟩
  · intro X
    have hX : X = ∑ a : Fin d, ∑ a' : Fin d, X a a' • Matrix.single a a' (1 : ℂ) := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single, Matrix.of_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'; simp [hj']
        · intro hj; exact absurd (Finset.mem_univ j) hj
      · intro i' _ hi'
        refine Finset.sum_eq_zero fun j' _ ↦ ?_
        simp [hi']
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hmap : Ψ X = ∑ a : Fin d, ∑ a' : Fin d, X a a' • Ψ (Matrix.single a a' (1 : ℂ)) := by
      conv_lhs => rw [hX]
      simp only [← QuantumChannel.toLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun a' _ ↦
        Ψ.toLinearMap.map_smul _ _
    rw [hmap]
    ext b b'
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    have hterm : ∀ a a' : Fin d,
        X a a' * Ψ (Matrix.single a a' (1 : ℂ)) b b' =
          ∑ r, K r b a * X a a' * star (K r b' a') := by
      intro a a'
      rw [hJ_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ ↦ by ring
    have hinner_eq : ∀ a : Fin d,
        ∑ a' : Fin d, X a a' * Ψ (Matrix.single a a' (1 : ℂ)) b b' =
          ∑ a' : Fin d, ∑ r, K r b a * X a a' * star (K r b' a') :=
      fun a ↦ Finset.sum_congr rfl fun a' _ ↦ hterm a a'
    rw [Finset.sum_congr rfl fun a _ ↦ hinner_eq a]
    calc ∑ a : Fin d, ∑ a' : Fin d, ∑ r, K r b a * X a a' * star (K r b' a')
        = ∑ a : Fin d, ∑ r, ∑ a' : Fin d, K r b a * X a a' * star (K r b' a') :=
          Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
      _ = ∑ r, ∑ a : Fin d, ∑ a' : Fin d, K r b a * X a a' * star (K r b' a') :=
          Finset.sum_comm
      _ = ∑ r, ∑ a' : Fin d, ∑ a : Fin d, K r b a * X a a' * star (K r b' a') :=
          Finset.sum_congr rfl fun r _ ↦ Finset.sum_comm
      _ = ∑ r, ∑ a' : Fin d, (∑ a : Fin d, K r b a * X a a') * star (K r b' a') :=
          Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun a' _ ↦
            (Finset.sum_mul _ _ _).symm
  · ext a a'
    have htr := Ψ.trace_map (Matrix.single a' a (1 : ℂ))
    have htr_rhs : (Matrix.single a' a (1 : ℂ)).trace = (1 : Matrix (Fin d) (Fin d) ℂ) a a' := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.single, Matrix.of_apply, Matrix.one_apply]
      by_cases ha : a = a'
      · subst ha; simp
      · have h0 : ∑ x : Fin d, (if a' = x ∧ a = x then (1 : ℂ) else 0) = 0 :=
          Finset.sum_eq_zero fun x _ ↦ by
            by_cases h1 : a' = x
            · subst h1; simp [ha]
            · simp [h1]
        rw [h0]
        simp [ha]
    rw [htr_rhs] at htr
    rw [← htr]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    simp_rw [hJ_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- **Stinespring Isometry Dilation**: Every quantum channel `Ψ : L(ℂ^d) → L(ℂ^m)` admits an
isometry `V : ℂ^d → ℂ^m ⊗ ℂ^{d*m}` such that `Ψ(ω) = Tr_{ℂ^{d*m}}(V ω Vᴴ)`. -/
theorem QuantumChannel.exists_stinespring_isometry {d m : ℕ}
    (Ψ : QuantumChannel (Fin d) (Fin m)) :
    ∃ V : Matrix (Fin m × (Fin d × Fin m)) (Fin d) ℂ,
      Vᴴ * V = 1 ∧
      ∀ ω : Matrix (Fin d) (Fin d) ℂ,
        Ψ ω = partialTraceRight (densityConj V ω) := by
  obtain ⟨K, hK_map, hK_tp⟩ := Ψ.exists_kraus_repr
  let V : Matrix (Fin m × (Fin d × Fin m)) (Fin d) ℂ :=
    Matrix.of fun p a ↦ K p.2 p.1 a
  refine ⟨V, ?_, ?_⟩
  · ext a a'
    rw [← hK_tp]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, V, Matrix.of_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
  · intro ω
    rw [hK_map ω]
    ext b b'
    simp only [partialTraceRight_apply, densityConj_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, V, Matrix.of_apply]

/-- The permutation equivalence `(Fin m × (Fin d × Fin m)) ≃ (Fin d × (Fin m × Fin m))` used in
the unitary Stinespring dilation. -/
def stinespringEquiv (d m : ℕ) : (Fin m × (Fin d × Fin m)) ≃ (Fin d × (Fin m × Fin m)) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stinespring Unitary Dilation**: Every quantum channel `Ψ : L(ℂ^d) → L(ℂ^m)` (`m > 0`)
admits a unitary operator `U ∈ U(ℂ^m ⊗ ℂ^d ⊗ ℂ^m)` and a fixed pure state `|φ₀⟩ ∈ Sphere(ℂ^m ⊗ ℂ^m)`
such that `Ψ(ω) = Tr_{ℂ^d ⊗ ℂ^m}(U (ω ⊗ |φ₀⟩⟨φ₀|) Uᴴ)` for all `ω : Matrix (Fin d) (Fin d) ℂ`. -/
theorem QuantumChannel.exists_stinespring_unitary {d m : ℕ} (hm : 0 < m)
    (Ψ : QuantumChannel (Fin d) (Fin m)) :
    ∃ (U : Matrix.unitaryGroup (Fin m × (Fin d × Fin m)) ℂ)
      (φ₀ : EuclideanSpace ℂ (Fin m × Fin m)),
      ‖φ₀‖ = 1 ∧
      ∀ ω : Matrix (Fin d) (Fin d) ℂ,
        Ψ ω = partialTraceRight
          (densityConj (U : Matrix (Fin m × (Fin d × Fin m)) (Fin m × (Fin d × Fin m)) ℂ)
            (Matrix.reindex (stinespringEquiv d m).symm (stinespringEquiv d m).symm
              (ω ⊗ₖ pureState φ₀))) := by
  obtain ⟨V, hV_iso, hV_eq⟩ := Ψ.exists_stinespring_isometry
  let i₀ : Fin m := ⟨0, hm⟩
  let φ₀ : EuclideanSpace ℂ (Fin m × Fin m) := EuclideanSpace.single (i₀, i₀) 1
  have hφ₀ : ‖φ₀‖ = 1 := by simp [φ₀]
  let J : Matrix (Fin m × (Fin d × Fin m)) (Fin d) ℂ :=
    Matrix.of fun p a ↦ if p = (i₀, (a, i₀)) then (1 : ℂ) else 0
  have hJ_iso : Jᴴ * J = 1 := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, J, Matrix.of_apply, Matrix.one_apply]
    have h1 : ∀ p : Fin m × (Fin d × Fin m),
        star (if p = (i₀, (a, i₀)) then (1 : ℂ) else 0) *
          (if p = (i₀, (a', i₀)) then (1 : ℂ) else 0) =
        if p = (i₀, (a, i₀)) then (if a = a' then (1 : ℂ) else 0) else 0 := by
      intro p
      by_cases hp : p = (i₀, (a, i₀))
      · subst hp
        by_cases ha : a = a'
        · subst ha; simp
        · simp [ha, Prod.ext_iff]
      · simp [hp]
    simp_rw [h1]
    simp
  have hJ_eq : Jᴴ * J = Vᴴ * V := hJ_iso.trans hV_iso.symm
  obtain ⟨Umat, hUmat, hUJ⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq J V hJ_eq
  refine ⟨⟨Umat, hUmat⟩, φ₀, hφ₀, ?_⟩
  intro ω
  rw [hV_eq ω, ← hUJ]
  congr 1
  rw [densityConj_mul]
  congr 1
  ext p q
  simp only [densityConj_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, pureState_apply, φ₀, PiLp.single_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, J, Matrix.of_apply,
    Equiv.symm_symm]
  have hst : ∀ z : Fin m × (Fin d × Fin m),
      stinespringEquiv d m z = (z.2.1, (z.1, z.2.2)) := fun _ ↦ rfl
  simp only [hst]
  by_cases h : p.1 = i₀ ∧ p.2.2 = i₀ ∧ q.1 = i₀ ∧ q.2.2 = i₀
  · rcases h with ⟨hp1, hp2, hq1, hq2⟩
    have hsum : ∑ x : Fin d,
        (∑ a : Fin d, (if p = (i₀, (a, i₀)) then (1 : ℂ) else 0) * ω a x) *
          star (if q = (i₀, (x, i₀)) then (1 : ℂ) else 0) = ω p.2.1 q.2.1 := by
      rw [Finset.sum_eq_single q.2.1]
      · have hqeq : q = (i₀, (q.2.1, i₀)) := Prod.ext hq1 (Prod.ext rfl hq2)
        have hq1_if : (if q = (i₀, (q.2.1, i₀)) then (1 : ℂ) else 0) = 1 := by
          rw [← hqeq]; simp
        rw [hq1_if, star_one, mul_one]
        rw [Finset.sum_eq_single p.2.1]
        · have hpeq : p = (i₀, (p.2.1, i₀)) := Prod.ext hp1 (Prod.ext rfl hp2)
          have hp1_if : (if p = (i₀, (p.2.1, i₀)) then (1 : ℂ) else 0) = 1 := by
            rw [← hpeq]; simp
          rw [hp1_if, one_mul]
        · intro a _ ha
          have hne : p ≠ (i₀, (a, i₀)) := fun he ↦ ha (congrArg (fun z ↦ z.2.1) he).symm
          simp [hne]
        · intro hp'; exact absurd (Finset.mem_univ _) hp'
      · intro x _ hx
        have hne : q ≠ (i₀, (x, i₀)) := fun he ↦ hx (congrArg (fun z ↦ z.2.1) he).symm
        simp [hne]
      · intro hq'; exact absurd (Finset.mem_univ _) hq'
    rw [hsum, hp1, hp2, hq1, hq2]
    simp
  · have hsum : ∑ x : Fin d,
        (∑ a : Fin d, (if p = (i₀, (a, i₀)) then (1 : ℂ) else 0) * ω a x) *
          star (if q = (i₀, (x, i₀)) then (1 : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      by_cases hq : q = (i₀, (x, i₀))
      · have hq1 : q.1 = i₀ := congrArg Prod.fst hq
        have hq2 : q.2.2 = i₀ := congrArg (fun z ↦ z.2.2) hq
        have hp_not : ¬(p.1 = i₀ ∧ p.2.2 = i₀) := fun hp ↦ h ⟨hp.1, hp.2, hq1, hq2⟩
        have h0 : ∑ a : Fin d, (if p = (i₀, (a, i₀)) then (1 : ℂ) else 0) * ω a x = 0 :=
          Finset.sum_eq_zero fun a _ ↦ by
            have hne : p ≠ (i₀, (a, i₀)) := fun he ↦
              hp_not ⟨congrArg Prod.fst he, congrArg (fun z ↦ z.2.2) he⟩
            simp [hne]
        rw [h0, zero_mul]
      · simp [hq]
    rw [hsum]
    by_cases hp : (p.1, p.2.2) = (i₀, i₀)
    · have hq_ne : (q.1, q.2.2) ≠ (i₀, i₀) := fun hq ↦
        h ⟨congrArg Prod.fst hp, congrArg Prod.snd hp, congrArg Prod.fst hq, congrArg Prod.snd hq⟩
      simp [hq_ne]
    · simp [hp]

end CslibFrontier.Foundations.Quantum
