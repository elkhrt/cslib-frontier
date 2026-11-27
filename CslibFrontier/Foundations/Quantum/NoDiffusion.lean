/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Quantum.Bipartite
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Impossibility of Controlled State Reflection (No General Quantum Diffusion)

For a unit state `ψ` in an inner product space `E`, the Householder state reflection
`φ ↦ φ - (2 * ⟪ψ, φ⟫) • ψ` acts as `I - 2 |ψ⟩⟨ψ|`, inverting amplitudes orthogonal to the
hyperplane `(𝕜 ∙ ψ)ᗮ` while negating `ψ`. In quantum algorithms such as amplitude amplification,
this reflection is implemented using a state-preparation circuit for `ψ` and its inverse.

This module proves that when `1 < Module.rank 𝕜 E` (or `[Nontrivial ι]` in coordinates), no linear
operator can perform controlled state reflection given only a single copy of an unknown state `ψ`:

* **Isometric inner-product dichotomy**: if a complex linear isometry `U` maps `(ψ ⊗ ψ) ⊗ a₀` to
  `(ψ ⊗ stateReflection ℂ ψ ψ) ⊗ a₁` and `(φ ⊗ ψ) ⊗ a₀` to `(φ ⊗ stateReflection ℂ φ ψ) ⊗ a₂` for
  unit states `ψ, φ` and unit apparatus state `a₀`, then `ψ` and `φ` are orthogonal or collinear up
  to a unit phase.
* **No linear controlled state reflection**: when `1 < Module.rank 𝕜 E`, no `𝕜`-linear operator on
  `(E ⊗ E) ⊗ A` maps `(ψ ⊗ φ) ⊗ a₀` to `(ψ ⊗ stateReflection 𝕜 ψ φ) ⊗ a` with `a ≠ 0` for all unit
  states `ψ, φ`. In particular, no ancilla-free linear operator or matrix realizes controlled state
  reflection even up to nonzero scalar factors.
* **Exact rank-at-most-one characterization**: a `𝕜`-linear controlled state reflection operator on
  `E ⊗ E` exists if and only if `Module.rank 𝕜 E ≤ 1` (realized in rank `≤ 1` by `-id`).

## Main definitions

* `CslibFrontier.Foundations.Quantum.stateReflection`: the linear operator
  `φ ↦ φ - (2 * ⟪ψ, φ⟫_𝕜) • ψ`.
* `CslibFrontier.Foundations.Quantum.IsControlledStateReflection`: predicate that `D` maps
  `ψ ⊗ₜ φ` to `ψ ⊗ₜ stateReflection 𝕜 ψ φ` on all unit states `ψ, φ`.

## Main results

* `CslibFrontier.Foundations.Quantum.inner_eq_zero_or_exists_smul_of_stateReflection_apparatus`,
  `CslibFrontier.Foundations.Quantum.inner_eq_zero_or_exists_smul_of_stateReflection`: isometric
  inner-product dichotomy with and without an apparatus register.
* `CslibFrontier.Foundations.Quantum.not_exists_linearMap_stateReflection_apparatus`,
  `CslibFrontier.Foundations.Quantum.not_exists_linearMap_stateReflection_smul`,
  `CslibFrontier.Foundations.Quantum.not_exists_linearMap_stateReflection`: linear no-go theorems
  on tensor products when `1 < Module.rank 𝕜 E`.
* `CslibFrontier.Foundations.Quantum.exists_linearMap_stateReflection_iff_rank_le_one`: exact
  equivalence with `Module.rank 𝕜 E ≤ 1`.
* `CslibFrontier.Foundations.Quantum.not_exists_matrix_stateReflection`: coordinate matrix no-go
  theorem on `EuclideanSpace ℂ (ι × ι)` for `[Nontrivial ι]`.
-/

public section

open Matrix
open scoped TensorProduct InnerProductSpace

namespace CslibFrontier.Foundations.Quantum

universe u v

section Reflection

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Householder state reflection `φ ↦ φ - (2 * ⟪ψ, φ⟫_𝕜) • ψ` on an inner product space `E`. -/
noncomputable def stateReflection (ψ : E) : E →ₗ[𝕜] E where
  toFun φ := φ - (2 * ⟪ψ, φ⟫_𝕜) • ψ
  map_add' φ₁ φ₂ := by
    rw [inner_add_right, mul_add, add_smul]
    abel
  map_smul' c φ := by
    rw [inner_smul_right, RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring

variable {𝕜}

/-- Evaluation formula for `stateReflection`. -/
theorem stateReflection_apply (ψ φ : E) :
    stateReflection 𝕜 ψ φ = φ - (2 * ⟪ψ, φ⟫_𝕜) • ψ := by
  rfl

/-- A unit vector `ψ` is negated by `stateReflection 𝕜 ψ`. -/
theorem stateReflection_self {ψ : E} (hψ : ‖ψ‖ = 1) :
    stateReflection 𝕜 ψ ψ = -ψ := by
  rw [stateReflection_apply, inner_self_eq_one_of_norm_eq_one hψ, mul_one, two_smul]
  abel

/-- Any vector orthogonal to `ψ` is fixed by `stateReflection 𝕜 ψ`. -/
theorem stateReflection_of_inner_eq_zero {ψ φ : E} (h : ⟪ψ, φ⟫_𝕜 = 0) :
    stateReflection 𝕜 ψ φ = φ := by
  simp [stateReflection_apply, h]

/-- For a unit vector `ψ`, `stateReflection 𝕜 ψ` agrees with orthogonal reflection across
`(𝕜 ∙ ψ)ᗮ`. -/
theorem stateReflection_eq_orthReflection {ψ : E} (hψ : ‖ψ‖ = 1) (φ : E) :
    stateReflection 𝕜 ψ φ = (𝕜 ∙ ψ)ᗮ.reflection φ := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hψ,
    RCLike.ofReal_one, one_pow, div_one, stateReflection_apply, two_smul, two_mul, add_smul]
  abel

/-- For a unit vector `ψ`, `stateReflection 𝕜 ψ` preserves norms. -/
theorem norm_stateReflection {ψ : E} (hψ : ‖ψ‖ = 1) (φ : E) :
    ‖stateReflection 𝕜 ψ φ‖ = ‖φ‖ := by
  rw [stateReflection_eq_orthReflection hψ]
  exact (𝕜 ∙ ψ)ᗮ.reflection.norm_map φ

end Reflection

section ControlledReflection

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Predicate that `D : E ⊗[𝕜] E →ₗ[𝕜] E ⊗[𝕜] E` performs controlled state reflection
`ψ ⊗ₜ φ ↦ ψ ⊗ₜ stateReflection 𝕜 ψ φ` on all unit states `ψ, φ : E`. -/
def IsControlledStateReflection (D : E ⊗[𝕜] E →ₗ[𝕜] E ⊗[𝕜] E) : Prop :=
  ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 → D (ψ ⊗ₜ[𝕜] φ) = ψ ⊗ₜ[𝕜] stateReflection 𝕜 ψ φ

variable {𝕜}

private theorem exists_orthonormal_pair_of_one_lt_rank (h : 1 < Module.rank 𝕜 E) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_𝕜 = 0 := by
  obtain ⟨x, hx⟩ := rank_pos_iff_exists_ne_zero.mp (zero_lt_one.trans h)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_rank h hx
  have ho := InnerProductSpace.gramSchmidtNormed_orthonormal hxy
  exact ⟨_, _, ho.1 0, ho.1 1, ho.2 (by decide : (0 : Fin 2) ≠ 1)⟩

private theorem not_stateReflection_apparatus_core {A G : Type*}
    [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : E → E → A → G)
    (hT : ∀ x y a x' y' a', ⟪T x y a, T x' y' a'⟫_𝕜 = ⟪x, x'⟫_𝕜 * ⟪y, y'⟫_𝕜 * ⟪a, a'⟫_𝕜)
    (haddL : ∀ x x' y a, T (x + x') y a = T x y a + T x' y a)
    (hsmulL : ∀ (c : 𝕜) x y a, T (c • x) y a = c • T x y a)
    (hsmulR : ∀ (c : 𝕜) x y a, T x (c • y) a = c • T x y a)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_𝕜 = 0)
    (a₀ : A) (L : G →ₗ[𝕜] G)
    (hL : ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      ∃ a : A, a ≠ 0 ∧ L (T ψ φ a₀) = T ψ (stateReflection 𝕜 ψ φ) a) :
    False := by
  have hvu : ⟪v, u⟫_𝕜 = 0 := inner_eq_zero_symm.mp huv
  have huu : ⟪u, u⟫_𝕜 = 1 := inner_self_eq_one_of_norm_eq_one hu
  have hvv : ⟪v, v⟫_𝕜 = 1 := inner_self_eq_one_of_norm_eq_one hv
  set r : ℝ := (Real.sqrt 2)⁻¹
  set s : 𝕜 := (r : 𝕜) with hs_def
  have hconj : starRingEnd 𝕜 s = s := RCLike.conj_ofReal r
  have hss : s * s = (1 / 2 : 𝕜) := by
    have hr2 : r * r = 1 / 2 := by
      dsimp only [r]
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
      norm_num
    calc
      s * s = ((r * r : ℝ) : 𝕜) := (RCLike.ofReal_mul r r).symm
      _ = (1 / 2 : 𝕜) := by rw [hr2]; push_cast; rfl
  have hs0 : s ≠ 0 := by
    rw [hs_def]
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  set w : E := s • u + s • v
  have hw : ‖w‖ = 1 := by
    have hw2 : ⟪w, w⟫_𝕜 = 1 := by
      simp only [w, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        hconj, huu, hvv, huv, hvu]
      linear_combination 2 * hss
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hw2]
    simp
  have hwu : stateReflection 𝕜 w u = -v := by
    have hinner_wu : ⟪w, u⟫_𝕜 = s := by
      simp [w, inner_add_left, inner_smul_left, hconj, hu, hvu]
    have h2s : (2 * s) * s = 1 := by linear_combination 2 * hss
    rw [stateReflection_apply, hinner_wu]
    dsimp only [w]
    rw [smul_add, smul_smul, smul_smul, h2s, one_smul, one_smul]
    abel
  obtain ⟨au, -, hLu⟩ := hL u u hu hu
  obtain ⟨av, -, hLv⟩ := hL v u hv hu
  obtain ⟨aw, haw, hLw⟩ := hL w u hw hu
  rw [stateReflection_self hu] at hLu
  rw [stateReflection_of_inner_eq_zero hvu] at hLv
  rw [hwu] at hLw
  have hlin : L (T w u a₀) = s • T u (-u) au + s • T v u av := by
    calc
      L (T w u a₀) = L (s • T u u a₀ + s • T v u a₀) := by
        dsimp only [w]
        rw [haddL, hsmulL, hsmulL]
      _ = s • L (T u u a₀) + s • L (T v u a₀) := by rw [map_add, map_smul, map_smul]
      _ = s • T u (-u) au + s • T v u av := by rw [hLu, hLv]
  have hneg_u : T u (-u) au = -T u u au := by
    simpa using hsmulR (-1 : 𝕜) u u au
  have hneg_v : T w (-v) aw = -(s • T u v aw + s • T v v aw) := by
    calc
      T w (-v) aw = (-1 : 𝕜) • T w v aw := by simpa using hsmulR (-1 : 𝕜) w v aw
      _ = -(T w v aw) := neg_one_smul 𝕜 _
      _ = -(s • T u v aw + s • T v v aw) := by
        dsimp only [w]
        rw [haddL, hsmulL, hsmulL]
  rw [hlin, hneg_u, hneg_v] at hLw
  have key := congrArg (⟪T u v aw, ·⟫_𝕜) hLw
  simp only [inner_add_right, inner_neg_right, inner_smul_right, hT, huu, hvv, huv, hvu] at key
  have hmul : s * ⟪aw, aw⟫_𝕜 = 0 := by linear_combination key
  exact (mul_eq_zero.mp hmul).elim hs0 fun h => haw (inner_self_eq_zero.mp h)

/-- Apparatus-assisted impossibility of linear controlled state reflection when
`1 < Module.rank 𝕜 E`. -/
theorem not_exists_linearMap_stateReflection_apparatus {A : Type v}
    [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
    (h : 1 < Module.rank 𝕜 E) (a₀ : A) :
    ¬ ∃ D : (E ⊗[𝕜] E) ⊗[𝕜] A →ₗ[𝕜] (E ⊗[𝕜] E) ⊗[𝕜] A,
      ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 →
        ∃ a : A, a ≠ 0 ∧ D ((ψ ⊗ₜ[𝕜] φ) ⊗ₜ[𝕜] a₀) =
          (ψ ⊗ₜ[𝕜] stateReflection 𝕜 ψ φ) ⊗ₜ[𝕜] a := by
  rintro ⟨D, hD⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair_of_one_lt_rank h
  exact not_stateReflection_apparatus_core (𝕜 := 𝕜) (G := (E ⊗[𝕜] E) ⊗[𝕜] A)
    (fun x y a => (x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] a)
    (fun _ _ _ _ _ _ => by simp only [TensorProduct.inner_tmul])
    (fun _ _ _ _ => by rw [TensorProduct.add_tmul, TensorProduct.add_tmul])
    (fun _ _ _ _ => by rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul'])
    (fun _ _ _ _ => by rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul'])
    hu hv huv a₀ D hD

/-- Impossibility of linear controlled state reflection up to nonzero scalar factors when
`1 < Module.rank 𝕜 E`. -/
theorem not_exists_linearMap_stateReflection_smul (h : 1 < Module.rank 𝕜 E) :
    ¬ ∃ (D : E ⊗[𝕜] E →ₗ[𝕜] E ⊗[𝕜] E) (c : E → E → 𝕜),
      ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 →
        c ψ φ ≠ 0 ∧ D (ψ ⊗ₜ[𝕜] φ) = c ψ φ • (ψ ⊗ₜ[𝕜] stateReflection 𝕜 ψ φ) := by
  rintro ⟨D, c, hD⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair_of_one_lt_rank h
  exact not_stateReflection_apparatus_core (𝕜 := 𝕜) (A := 𝕜) (G := E ⊗[𝕜] E)
    (fun x y a => a • (x ⊗ₜ[𝕜] y))
    (fun _ _ _ _ _ _ => by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.inner_tmul,
        inner_smul_left, inner_smul_right, RCLike.inner_apply]
      ring)
    (fun _ _ _ _ => by rw [TensorProduct.add_tmul, smul_add])
    (fun _ _ _ _ => by rw [← TensorProduct.smul_tmul', smul_comm])
    (fun _ _ _ _ => by rw [TensorProduct.tmul_smul, smul_comm])
    hu hv huv (1 : 𝕜) D fun ψ φ hψ hφ =>
      ⟨c ψ φ, (hD ψ φ hψ hφ).1, by rw [one_smul, (hD ψ φ hψ hφ).2]⟩

/-- Ancilla-free impossibility of linear controlled state reflection when `1 < Module.rank 𝕜 E`. -/
theorem not_exists_linearMap_stateReflection (h : 1 < Module.rank 𝕜 E) :
    ¬ ∃ D : E ⊗[𝕜] E →ₗ[𝕜] E ⊗[𝕜] E, IsControlledStateReflection 𝕜 D := by
  rintro ⟨D, hD⟩
  exact not_exists_linearMap_stateReflection_smul h
    ⟨D, fun _ _ => 1, fun ψ φ hψ hφ => ⟨one_ne_zero, by rw [one_smul, hD ψ φ hψ hφ]⟩⟩

/-- When `Module.rank 𝕜 E ≤ 1`, `-LinearMap.id` is a controlled state reflection operator. -/
theorem isControlledStateReflection_neg_id_of_rank_le_one (h : Module.rank 𝕜 E ≤ 1) :
    IsControlledStateReflection 𝕜 (-LinearMap.id : E ⊗[𝕜] E →ₗ[𝕜] E ⊗[𝕜] E) := by
  intro ψ φ hψ _
  have hcol : φ = ⟪ψ, φ⟫_𝕜 • ψ := by
    by_contra hne
    set w : E := φ - ⟪ψ, φ⟫_𝕜 • ψ
    have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
    have horth : ⟪ψ, w⟫_𝕜 = 0 := by simp [w, inner_sub_right, inner_smul_right, hψ]
    have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    set v : E := ((‖w‖⁻¹ : ℝ) : 𝕜) • w
    have hv1 : ‖v‖ = 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hnw]
    have hψv : ⟪ψ, v⟫_𝕜 = 0 := by simp [v, inner_smul_right, horth]
    have hon : Orthonormal 𝕜 ![ψ, v] := by
      refine ⟨?_, ?_⟩
      · intro i; fin_cases i <;> assumption
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact hψv
        · exact inner_eq_zero_symm.mp hψv
        · exact absurd rfl hij
    have h2 : (2 : Cardinal) ≤ Module.rank 𝕜 E := by
      simpa using hon.linearIndependent.cardinal_lift_le_rank
    exact not_lt_of_ge h (lt_of_lt_of_le (by norm_num : (1 : Cardinal) < 2) h2)
  have hrefl : stateReflection 𝕜 ψ φ = -φ := by
    conv_lhs => rw [hcol]
    rw [map_smul, stateReflection_self hψ, smul_neg, ← hcol]
  rw [hrefl, TensorProduct.tmul_neg]
  rfl

/-- Exact rank characterization: a `𝕜`-linear controlled state reflection operator on `E ⊗[𝕜] E`
exists if and only if `Module.rank 𝕜 E ≤ 1`. -/
theorem exists_linearMap_stateReflection_iff_rank_le_one :
    (∃ D : E ⊗[𝕜] E →ₗ[𝕜] E ⊗[𝕜] E, IsControlledStateReflection 𝕜 D) ↔
      Module.rank 𝕜 E ≤ 1 := by
  constructor
  · intro hD
    by_contra hlt
    exact not_exists_linearMap_stateReflection (lt_of_not_ge hlt) hD
  · exact fun h => ⟨-LinearMap.id, isControlledStateReflection_neg_id_of_rank_le_one h⟩

end ControlledReflection

section DichotomyAndCoordinates

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem inner_eq_zero_or_exists_smul_core {A G : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (T : E → E → A → G)
    (hT : ∀ x y a x' y' a', ⟪T x y a, T x' y' a'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ * ⟪a, a'⟫_ℂ)
    (U : G →ₗᵢ[ℂ] G) {ψ φ : E} {a₀ a₁ a₂ : A}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (ha₀ : ‖a₀‖ = 1)
    (hUψ : U (T ψ ψ a₀) = T ψ (stateReflection ℂ ψ ψ) a₁)
    (hUφ : U (T φ ψ a₀) = T φ (stateReflection ℂ φ ψ) a₂) :
    ⟪ψ, φ⟫_ℂ = 0 ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := by
  have norm_app {x : E} {ax : A} (hx : ‖x‖ = 1)
      (hUx : U (T x ψ a₀) = T x (stateReflection ℂ x ψ) ax) :
      ‖ax‖ = 1 := by
    have hn := U.inner_map_map (T x ψ a₀) (T x ψ a₀)
    have hrx : ‖stateReflection ℂ x ψ‖ = 1 := by rw [norm_stateReflection hx, hψ]
    rw [hUx, hT, hT, inner_self_eq_one_of_norm_eq_one hx, inner_self_eq_one_of_norm_eq_one hψ,
      inner_self_eq_one_of_norm_eq_one ha₀, inner_self_eq_one_of_norm_eq_one hrx,
      one_mul, one_mul, mul_one] at hn
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hn]
    simp
  refine or_iff_not_imp_left.mpr fun h0 => ?_
  set c : ℂ := ⟪ψ, φ⟫_ℂ with hc_def
  have hc_conj : ⟪φ, ψ⟫_ℂ = starRingEnd ℂ c := by rw [hc_def, inner_conj_symm]
  have hinner := U.inner_map_map (T ψ ψ a₀) (T φ ψ a₀)
  rw [hUψ, hUφ, hT, hT, stateReflection_self hψ, stateReflection_apply] at hinner
  simp only [inner_self_eq_one_of_norm_eq_one ha₀,
    inner_neg_left, inner_sub_right, inner_smul_right,
    inner_self_eq_one_of_norm_eq_one hψ, mul_one, ← hc_def, hc_conj] at hinner
  have hcsq : starRingEnd ℂ c * c = (‖c‖ ^ 2 : ℂ) := RCLike.conj_mul c
  have hreal : (1 : ℂ) - 2 * starRingEnd ℂ c * c = ((1 - 2 * ‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, hcsq]; push_cast; ring
  have hsimp : c * (-1 - 2 * starRingEnd ℂ c * -c) * ⟪a₁, a₂⟫_ℂ =
      -(c * ((1 - 2 * ‖c‖ ^ 2 : ℝ) : ℂ) * ⟪a₁, a₂⟫_ℂ) := by rw [← hreal]; ring
  rw [hsimp] at hinner
  have hn := congrArg norm hinner
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr h0
  have hprod : |1 - 2 * ‖c‖ ^ 2| * ‖⟪a₁, a₂⟫_ℂ‖ = 1 :=
    mul_left_cancel₀ hc_pos.ne' (by linear_combination hn)
  have hc_le : ‖c‖ ≤ 1 := by simpa only [hc_def, hψ, hφ, mul_one] using norm_inner_le_norm ψ φ
  have ha_le : ‖⟪a₁, a₂⟫_ℂ‖ ≤ 1 := by
    simpa only [norm_app hψ hUψ, norm_app hφ hUφ, mul_one] using norm_inner_le_norm a₁ a₂
  have habs_ge : 1 ≤ |1 - 2 * ‖c‖ ^ 2| := by
    nlinarith [abs_nonneg (1 - 2 * ‖c‖ ^ 2), norm_nonneg ⟪a₁, a₂⟫_ℂ]
  have hc1 : ‖c‖ = 1 := by
    have hcsq_le : ‖c‖ ^ 2 ≤ 1 := by nlinarith
    rcases le_or_gt 0 (1 - 2 * ‖c‖ ^ 2) with hpos | hneg
    · rw [abs_of_nonneg hpos] at habs_ge
      nlinarith [sq_pos_of_pos hc_pos]
    · rw [abs_of_neg hneg] at habs_ge
      have hcsq1 : ‖c‖ ^ 2 = 1 := by linarith
      nlinarith
  have hcψ : ‖c • ψ‖ = 1 := by rw [norm_smul, hc1, hψ, one_mul]
  refine ⟨c, hc1, ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℂ) hcψ hφ).mp ?_).symm⟩
  rw [inner_smul_left, ← hc_def, RCLike.conj_mul, hc1]
  norm_num

/-- Isometric inner-product dichotomy for controlled state reflection with an apparatus register. -/
theorem inner_eq_zero_or_exists_smul_of_stateReflection_apparatus {A : Type v}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (U : (E ⊗[ℂ] E) ⊗[ℂ] A →ₗᵢ[ℂ] (E ⊗[ℂ] E) ⊗[ℂ] A)
    {ψ φ : E} {a₀ a₁ a₂ : A}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (ha₀ : ‖a₀‖ = 1)
    (hUψ : U ((ψ ⊗ₜ[ℂ] ψ) ⊗ₜ[ℂ] a₀) = (ψ ⊗ₜ[ℂ] stateReflection ℂ ψ ψ) ⊗ₜ[ℂ] a₁)
    (hUφ : U ((φ ⊗ₜ[ℂ] ψ) ⊗ₜ[ℂ] a₀) = (φ ⊗ₜ[ℂ] stateReflection ℂ φ ψ) ⊗ₜ[ℂ] a₂) :
    ⟪ψ, φ⟫_ℂ = 0 ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ :=
  inner_eq_zero_or_exists_smul_core (G := (E ⊗[ℂ] E) ⊗[ℂ] A)
    (fun x y a => (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] a)
    (fun _ _ _ _ _ _ => by simp only [TensorProduct.inner_tmul]) U hψ hφ ha₀ hUψ hUφ

/-- Ancilla-free isometric inner-product dichotomy for controlled state reflection. -/
theorem inner_eq_zero_or_exists_smul_of_stateReflection
    (U : E ⊗[ℂ] E →ₗᵢ[ℂ] E ⊗[ℂ] E) {ψ φ : E}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hUψ : U (ψ ⊗ₜ[ℂ] ψ) = ψ ⊗ₜ[ℂ] stateReflection ℂ ψ ψ)
    (hUφ : U (φ ⊗ₜ[ℂ] ψ) = φ ⊗ₜ[ℂ] stateReflection ℂ φ ψ) :
    ⟪ψ, φ⟫_ℂ = 0 ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ :=
  inner_eq_zero_or_exists_smul_core (A := ℂ) (G := E ⊗[ℂ] E)
    (fun x y a => a • (x ⊗ₜ[ℂ] y))
    (fun _ _ _ _ _ _ => by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.inner_tmul,
        inner_smul_left, inner_smul_right, RCLike.inner_apply]
      ring)
    U hψ hφ norm_one (a₁ := 1) (a₂ := 1)
    (by rw [one_smul, one_smul, hUψ]) (by rw [one_smul, one_smul, hUφ])

/-- Coordinate matrix impossibility of controlled state reflection on `ℂ^{ι × ι}` when `|ι| ≥ 2`. -/
theorem not_exists_matrix_stateReflection {ι : Type*} [Fintype ι] [Nontrivial ι] :
    ¬ ∃ U : Matrix (ι × ι) (ι × ι) ℂ,
      ∀ ψ φ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 → ‖φ‖ = 1 →
        U *ᵥ (Cslib.Quantum.prodState ψ φ).ofLp =
          (Cslib.Quantum.prodState ψ (stateReflection ℂ ψ φ)).ofLp := by
  classical
  rintro ⟨U, hU⟩
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  set u : EuclideanSpace ℂ ι := Cslib.Quantum.ket i
  set v : EuclideanSpace ℂ ι := Cslib.Quantum.ket j
  have hu : ‖u‖ = 1 := Cslib.Quantum.norm_ket i
  have hv : ‖v‖ = 1 := Cslib.Quantum.norm_ket j
  have huv : ⟪u, v⟫_ℂ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k = i
    · subst hki
      simp [u, v, Cslib.Quantum.ket_apply, hij]
    · simp [u, Cslib.Quantum.ket_apply, hki]
  exact not_stateReflection_apparatus_core (𝕜 := ℂ) (A := ℂ)
    (G := EuclideanSpace ℂ (ι × ι))
    (fun x y a => a • Cslib.Quantum.prodState x y)
    (fun _ _ _ _ _ _ => by
      rw [inner_smul_left, inner_smul_right, Cslib.Quantum.inner_prodState, RCLike.inner_apply]
      ring)
    (fun _ _ _ _ => by
      ext p
      simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply,
        Cslib.Quantum.prodState_apply, smul_eq_mul]
      ring)
    (fun _ _ _ _ => by
      ext p
      simp only [WithLp.ofLp_smul, Pi.smul_apply, Cslib.Quantum.prodState_apply, smul_eq_mul]
      ring)
    (fun _ _ _ _ => by
      ext p
      simp only [WithLp.ofLp_smul, Pi.smul_apply, Cslib.Quantum.prodState_apply, smul_eq_mul]
      ring)
    hu hv huv (1 : ℂ) (Matrix.toEuclideanLin U) fun ψ φ hψ hφ =>
      ⟨1, one_ne_zero, by
        rw [one_smul, one_smul]
        exact WithLp.ofLp_injective 2 (hU ψ φ hψ hφ)⟩

end DichotomyAndCoordinates

end CslibFrontier.Foundations.Quantum
