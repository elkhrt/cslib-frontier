/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Logics.Polymorphism.Minion
public import CslibFrontier.Computability.Complexity.BoundedWidth
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Data.Finsupp.Defs

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Basic

/-!
# The Quantum Minion, the SDP Minion, and Pseudo-Telepathy for Relational Structures

This module defines orthogonal subspace partitions
(`CslibFrontier.Computability.Complexity.OrthogonalPartition`),
the quantum minion (`CslibFrontier.Computability.Complexity.quantumMinion`), the
semidefinite-programming minion
(`CslibFrontier.Computability.Complexity.SdpPartition`,
`CslibFrontier.Computability.Complexity.sdpMinion`), and proves
strictly under standard Lean axioms:

  constructing a minion homomorphism from `quantumMinion ℂ H` to `sdpMinion` for every nontrivial
  finite-dimensional complex Hilbert space `H`.
  `CslibFrontier.Computability.Complexity.isPseudoTelepathicOver_iff_not_minionHomExists`, equating
  pseudo-telepathy of a finite relational structure `Y` over `H` with the non-existence of a
  minion homomorphism from `quantumMinion ℂ H` to `polMinion L Y`.

## Main definitions

- `CslibFrontier.Computability.Complexity.OrthogonalPartition`,
  `CslibFrontier.Computability.Complexity.quantumMinion`:
  `r`-tuples of pairwise orthogonal subspaces spanning `H` and the resulting quantum minion.
- `CslibFrontier.Computability.Complexity.sdpInner`,
  `CslibFrontier.Computability.Complexity.SdpPartition`,
  `CslibFrontier.Computability.Complexity.sdpMinion`: Finitely supported real dot product, pairwise
  orthogonal
  real vector partitions summing to `Finsupp.single 0 1`, and the SDP minion.
- `CslibFrontier.Computability.Complexity.RelConstraint`,
  `CslibFrontier.Computability.Complexity.QuantumHomStrategy`,
  `CslibFrontier.Computability.Complexity.IsPseudoTelepathicOver`,
  `CslibFrontier.Computability.Complexity.IsPseudoTelepathic`:
  Relational constraints, maximally entangled projective quantum homomorphism strategies, and
  pseudo-telepathy over `H` and over some positive-dimensional `ℂ^d`.

## Main results

- `CslibFrontier.Computability.Complexity.OrthogonalPartition.orthogonal_subspace_eq_iSup`,
  `CslibFrontier.Computability.Complexity.OrthogonalPartition.le_subspace_of_pairwise_isOrtho`,
  `CslibFrontier.Computability.Complexity.OrthogonalPartition.eq_of_subspace_le`:
  Orthogonal-complement and
  inclusion rigidity lemmas for orthogonal partitions.
- `CslibFrontier.Computability.Complexity.quantumMinion_to_sdpMinion`: Minion homomorphism from
  `quantumMinion ℂ H` to `sdpMinion` for every nontrivial finite-dimensional complex Hilbert
  space `H`.
- `CslibFrontier.Computability.Complexity.not_isPseudoTelepathicOver_of_minionHomExists`,
  `CslibFrontier.Computability.Complexity.isPseudoTelepathicOver_iff_not_minionHomExists`,
  `CslibFrontier.Computability.Complexity.isPseudoTelepathic_iff_exists_not_minionHomExists`:
  Quantum-minion
  characterization of pseudo-telepathy.
-/

public section

universe u v w w' uH

namespace CslibFrontier.Computability.Complexity

open CslibFrontier.Logics.Polymorphism
open scoped CslibFrontier.Logics.Polymorphism

/-! ### Orthogonal Subspace Partitions and the Quantum Minion -/

/-- An *orthogonal `r`-partition* over a `𝕜`-inner product space `H` is an `r`-tuple of pairwise
orthogonal subspaces of `H` whose supremum is `⊤`. -/
@[ext]
structure OrthogonalPartition (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (r : ℕ) : Type v where
  /-- Subspace assigned to outcome `i : Fin r`. -/
  subspace : Fin r → Submodule 𝕜 H
  /-- Distinct outcomes correspond to orthogonal subspaces. -/
  pairwise_orth : ∀ ⦃i j : Fin r⦄, i ≠ j → subspace i ⟂ subspace j
  /-- The component subspaces span the entire ambient space `H`. -/
  iSup_eq_top : (⨆ i, subspace i) = ⊤

namespace OrthogonalPartition

/-- The `r`-ary orthogonal partition placing `⊤` at index `i₀` and `⊥` at every other index. -/
def topSingle (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {r : ℕ} (i₀ : Fin r) : OrthogonalPartition 𝕜 H r where
  subspace i := if i = i₀ then ⊤ else ⊥
  pairwise_orth i j hij := by
    by_cases hi : i = i₀
    · have hj : j ≠ i₀ := fun h ↦ hij (hi.trans h.symm)
      simp [hi, hj]
    · simp [hi]
  iSup_eq_top := top_unique <| le_iSup_of_le i₀ (by simp)

/-- Component subspace of `OrthogonalPartition.topSingle`. -/
@[simp]
theorem topSingle_subspace (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {r : ℕ} (i₀ i : Fin r) :
    (topSingle 𝕜 H i₀).subspace i = if i = i₀ then ⊤ else ⊥ := by
  rfl

/-- Taking the minor of an orthogonal `ℓ`-partition `U` along `π : Fin ℓ → Fin ℓ'` groups the
subspaces over each fiber `π⁻¹({j})` by supremum. -/
def minor {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ℓ ℓ' : ℕ} (π : Fin ℓ → Fin ℓ') (U : OrthogonalPartition 𝕜 H ℓ) :
    OrthogonalPartition 𝕜 H ℓ' where
  subspace j := ⨆ (i : Fin ℓ) (_ : π i = j), U.subspace i
  pairwise_orth j₁ j₂ hjj := by
    simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro i₁ hi₁ i₂ hi₂
    exact U.pairwise_orth fun h ↦ hjj (by subst h; rw [← hi₁, ← hi₂])
  iSup_eq_top := top_unique <| by
    rw [← U.iSup_eq_top]
    refine iSup_le fun i ↦ ?_
    exact le_iSup_of_le (π i) (le_iSup_of_le i (le_iSup_of_le rfl le_rfl))

/-- Component subspace of a minor `U.minor π`. -/
@[simp]
theorem minor_subspace {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ℓ ℓ' : ℕ} (π : Fin ℓ → Fin ℓ') (U : OrthogonalPartition 𝕜 H ℓ)
    (j : Fin ℓ') :
    (U.minor π).subspace j = ⨆ (i : Fin ℓ) (_ : π i = j), U.subspace i := by
  rfl

/-- Taking the minor of an orthogonal partition along the identity map fixes it. -/
@[simp]
theorem minor_id {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ℓ : ℕ} (U : OrthogonalPartition 𝕜 H ℓ) :
    U.minor id = U := by
  refine OrthogonalPartition.ext (funext fun j ↦ ?_)
  rw [minor_subspace]
  refine le_antisymm ?_ (le_iSup_of_le j (le_iSup (fun _ : id j = j ↦ U.subspace j) rfl))
  exact iSup_le fun i ↦ iSup_le fun hi ↦ hi ▸ le_rfl

/-- Taking minors of orthogonal partitions respects composition of index maps. -/
@[simp]
theorem minor_comp {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ℓ ℓ' ℓ'' : ℕ} (π₁ : Fin ℓ → Fin ℓ') (π₂ : Fin ℓ' → Fin ℓ'')
    (U : OrthogonalPartition 𝕜 H ℓ) :
    (U.minor π₁).minor π₂ = U.minor (π₂ ∘ π₁) := by
  refine OrthogonalPartition.ext (funext fun k ↦ ?_)
  simp only [minor_subspace]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j ↦ iSup_le fun hj ↦ iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    refine le_iSup_of_le i (le_iSup (fun _ : (π₂ ∘ π₁) i = k ↦ U.subspace i) ?_)
    exact (congrArg π₂ hi).trans hj
  · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    refine le_iSup_of_le (π₁ i) (le_iSup_of_le hi ?_)
    exact le_iSup_of_le i (le_iSup (fun _ : π₁ i = π₁ i ↦ U.subspace i) rfl)

end OrthogonalPartition

/-- The *quantum minion* `quantumMinion 𝕜 H` over a `𝕜`-inner product space `H`, whose `r`-ary
operations (`0 < r`) are orthogonal `r`-partitions of `H`. -/
@[expose]
def quantumMinion (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] : Minion.{v} where
  Carrier r _ := OrthogonalPartition 𝕜 H r
  nonempty _ hr := ⟨OrthogonalPartition.topSingle 𝕜 H ⟨0, hr⟩⟩
  minor _ _ π U := OrthogonalPartition.minor π U
  minor_id _ U := OrthogonalPartition.minor_id U
  minor_comp _ _ _ π₁ π₂ U := OrthogonalPartition.minor_comp π₁ π₂ U

/-- Component subspace of a minor in `quantumMinion 𝕜 H`. -/
@[simp]
theorem quantumMinion_minor_subspace {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ')
    (U : (quantumMinion 𝕜 H).Carrier ℓ hℓ) (j : Fin ℓ') :
    ((quantumMinion 𝕜 H).minor hℓ hℓ' π U).subspace j =
      ⨆ (i : Fin ℓ) (_ : π i = j), U.subspace i := by
  rfl

namespace OrthogonalPartition

private theorem sup_iSup_ne_eq_top {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {r : ℕ} (U : OrthogonalPartition 𝕜 H r) (k : Fin r) :
    U.subspace k ⊔ (⨆ (j : Fin r) (_ : j ≠ k), U.subspace j) = ⊤ := by
  refine top_unique ?_
  rw [← U.iSup_eq_top]
  refine iSup_le fun j ↦ ?_
  by_cases hjk : j = k
  · subst hjk
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup_of_le j (le_iSup (fun _ : j ≠ k ↦ U.subspace j) hjk))

private theorem iSup_ne_le_orthogonal {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {r : ℕ} (U : OrthogonalPartition 𝕜 H r)
    (k : Fin r) :
    (⨆ (j : Fin r) (_ : j ≠ k), U.subspace j) ≤ (U.subspace k)ᗮ := by
  rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_iSup_left]
  intro j
  rw [Submodule.isOrtho_iSup_left]
  intro hjk
  exact U.pairwise_orth hjk

private theorem hasOrthogonalProjection_subspace {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {r : ℕ} (U : OrthogonalPartition 𝕜 H r)
    (k : Fin r) :
    (U.subspace k).HasOrthogonalProjection := by
  refine ⟨fun w ↦ ?_⟩
  have hw : w ∈ U.subspace k ⊔ (⨆ (j : Fin r) (_ : j ≠ k), U.subspace j) := by
    rw [sup_iSup_ne_eq_top U k]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  refine ⟨x, hx, ?_⟩
  simpa only [add_sub_cancel_left] using iSup_ne_le_orthogonal U k hy

/-- In an orthogonal partition `U : OrthogonalPartition 𝕜 H r`, the orthogonal complement of
`U.subspace k` equals the supremum of all other components `U.subspace j` (`j ≠ k`). -/
theorem orthogonal_subspace_eq_iSup {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {r : ℕ} (U : OrthogonalPartition 𝕜 H r)
    (k : Fin r) :
    (U.subspace k)ᗮ = ⨆ (j : Fin r) (_ : j ≠ k), U.subspace j := by
  refine le_antisymm ?_ (iSup_ne_le_orthogonal U k)
  have hsup : U.subspace k ⊔ (⨆ (j : Fin r) (_ : j ≠ k), U.subspace j) = ⊤ :=
    sup_iSup_ne_eq_top U k
  have hle : (⨆ (j : Fin r) (_ : j ≠ k), U.subspace j) ≤ (U.subspace k)ᗮ :=
    iSup_ne_le_orthogonal U k
  intro w hw
  have hw' : w ∈ U.subspace k ⊔ (⨆ (j : Fin r) (_ : j ≠ k), U.subspace j) := by
    rw [hsup]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw'
  have hx_orth : x ∈ (U.subspace k)ᗮ := by
    have : x = (x + y) - y := (add_sub_cancel_right x y).symm
    rw [this]
    exact (U.subspace k)ᗮ.sub_mem hw (hle hy)
  have hx_zero : x = 0 := by
    have : x ∈ U.subspace k ⊓ (U.subspace k)ᗮ := ⟨hx, hx_orth⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  simpa [hx_zero] using hy

/-- If a subspace `W` is orthogonal to `U.subspace j` for every `j ≠ k`, then
`W ≤ U.subspace k`. -/
theorem le_subspace_of_pairwise_isOrtho {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {r : ℕ} (U : OrthogonalPartition 𝕜 H r)
    {W : Submodule 𝕜 H} {k : Fin r} (hW : ∀ j : Fin r, j ≠ k → W ⟂ U.subspace j) :
    W ≤ U.subspace k := by
  have hW_orth : W ⟂ (U.subspace k)ᗮ := by
    rw [U.orthogonal_subspace_eq_iSup k, Submodule.isOrtho_iSup_right]
    intro j
    rw [Submodule.isOrtho_iSup_right]
    exact fun hjk ↦ hW j hjk
  have _ : (U.subspace k).HasOrthogonalProjection := U.hasOrthogonalProjection_subspace k
  have hsup : U.subspace k ⊔ (U.subspace k)ᗮ = ⊤ :=
    Submodule.sup_orthogonal_of_hasOrthogonalProjection
  intro w hw
  have hw' : w ∈ U.subspace k ⊔ (U.subspace k)ᗮ := by
    rw [hsup]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw'
  have hy_orth : y ∈ (U.subspace k)ᗮᗮ := by
    have : y = (x + y) - x := (add_sub_cancel_left x y).symm
    rw [this]
    exact (U.subspace k)ᗮᗮ.sub_mem (hW_orth.le hw) (Submodule.le_orthogonal_orthogonal _ hx)
  have hy_zero : y = 0 := by
    have : y ∈ (U.subspace k)ᗮ ⊓ (U.subspace k)ᗮᗮ := ⟨hy, hy_orth⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  simpa [hy_zero] using hx

/-- Two orthogonal `r`-partitions satisfying `A.subspace k ≤ B.subspace k` for every `k : Fin r`
are equal. -/
theorem eq_of_subspace_le {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {r : ℕ} {A B : OrthogonalPartition 𝕜 H r}
    (hAB : ∀ k : Fin r, A.subspace k ≤ B.subspace k) :
    A = B := by
  refine OrthogonalPartition.ext (funext fun k ↦ le_antisymm (hAB k) ?_)
  refine A.le_subspace_of_pairwise_isOrtho fun j hjk ↦ ?_
  exact (B.pairwise_orth hjk.symm).mono_right (hAB j)

end OrthogonalPartition

/-! ### The SDP Minion and Ciardo's Reduction `Q_H → M_SDP` -/

/-- Standard real dot product on finitely supported real sequences `ℕ →₀ ℝ`. -/
def sdpInner (x y : ℕ →₀ ℝ) : ℝ :=
  x.sum fun k a ↦ a * y k

@[simp]
theorem sdpInner_zero_left (y : ℕ →₀ ℝ) : sdpInner 0 y = 0 := by
  simp [sdpInner]

@[simp]
theorem sdpInner_zero_right (x : ℕ →₀ ℝ) : sdpInner x 0 = 0 := by
  simp [sdpInner]

theorem sdpInner_add_left (x₁ x₂ y : ℕ →₀ ℝ) :
    sdpInner (x₁ + x₂) y = sdpInner x₁ y + sdpInner x₂ y := by
  classical
  simp only [sdpInner]
  exact Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)

theorem sdpInner_add_right (x y₁ y₂ : ℕ →₀ ℝ) :
    sdpInner x (y₁ + y₂) = sdpInner x y₁ + sdpInner x y₂ := by
  simp only [sdpInner, Finsupp.sum, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem sdpInner_sum_left {ι : Type*} (s : Finset ι) (x : ι → (ℕ →₀ ℝ)) (y : ℕ →₀ ℝ) :
    sdpInner (∑ i ∈ s, x i) y = ∑ i ∈ s, sdpInner (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sdpInner_add_left, ih]

theorem sdpInner_sum_right {ι : Type*} (s : Finset ι) (x : ℕ →₀ ℝ) (y : ι → (ℕ →₀ ℝ)) :
    sdpInner x (∑ i ∈ s, y i) = ∑ i ∈ s, sdpInner x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sdpInner_add_right, ih]

theorem sdpInner_smul_left (c : ℝ) (x y : ℕ →₀ ℝ) :
    sdpInner (c • x) y = c * sdpInner x y := by
  classical
  simp only [sdpInner, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_subset Finsupp.support_smul fun k _ hk ↦ by
    simp [Finsupp.notMem_support_iff.mp hk]]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [mul_assoc]

theorem sdpInner_smul_right (c : ℝ) (x y : ℕ →₀ ℝ) :
    sdpInner x (c • y) = c * sdpInner x y := by
  simp only [sdpInner, Finsupp.sum, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

theorem sdpInner_single_single (a b : ℕ) (r s : ℝ) :
    sdpInner (Finsupp.single a r) (Finsupp.single b s) = if a = b then r * s else 0 := by
  by_cases h : a = b
  · subst h
    simp [sdpInner, Finsupp.sum_single_index]
  · simp [sdpInner, Finsupp.single_apply, h, Ne.symm h]

theorem sdpInner_comm (x y : ℕ →₀ ℝ) : sdpInner x y = sdpInner y x := by
  classical
  simp only [sdpInner, Finsupp.sum]
  have hL :
      (∑ k ∈ x.support, x k * y k) = ∑ k ∈ x.support ∪ y.support, x k * y k :=
    Finset.sum_subset Finset.subset_union_left fun k _ hk ↦ by
      simp [Finsupp.notMem_support_iff.mp hk]
  have hR :
      (∑ k ∈ y.support, y k * x k) = ∑ k ∈ x.support ∪ y.support, y k * x k :=
    Finset.sum_subset Finset.subset_union_right fun k _ hk ↦ by
      simp [Finsupp.notMem_support_iff.mp hk]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

theorem sdpInner_self_eq_zero_iff (x : ℕ →₀ ℝ) : sdpInner x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hall : ∀ k ∈ x.support, x k * x k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ mul_self_nonneg (x k)).mp h
    ext k
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hk
    exact mul_self_eq_zero.mp (hall k (Finsupp.mem_support_iff.mpr hk)) |> hk
  · rintro rfl
    exact sdpInner_zero_left 0

/-- An `r`-ary element of the *SDP minion* `sdpMinion`: an `r`-tuple of pairwise orthogonal
finitely supported real vectors summing to the unit vector `Finsupp.single 0 1`. -/
@[ext]
structure SdpPartition (r : ℕ) : Type where
  /-- Component vector assigned to outcome `i : Fin r`. -/
  vec : Fin r → (ℕ →₀ ℝ)
  /-- Distinct outcomes correspond to orthogonal vectors. -/
  pairwise_orth : ∀ ⦃i j : Fin r⦄, i ≠ j → sdpInner (vec i) (vec j) = 0
  /-- The component vectors sum to the shared unit vector `e₀`. -/
  sum_eq_single : (∑ i : Fin r, vec i) = Finsupp.single 0 1

namespace SdpPartition

/-- The `r`-ary SDP partition placing `Finsupp.single 0 1` at `i₀` and `0` elsewhere. -/
noncomputable def single {r : ℕ} (i₀ : Fin r) : SdpPartition r where
  vec i := if i = i₀ then Finsupp.single 0 1 else 0
  pairwise_orth i j hij := by
    by_cases hi : i = i₀
    · have hj : j ≠ i₀ := fun h ↦ hij (hi.trans h.symm)
      simp [hi, hj]
    · simp [hi]
  sum_eq_single := by simp

/-- Taking the minor of an SDP partition along `π : Fin ℓ → Fin ℓ'` sums component vectors
over each fiber `π⁻¹({j})`. -/
noncomputable def minor {ℓ ℓ' : ℕ} (π : Fin ℓ → Fin ℓ') (v : SdpPartition ℓ) : SdpPartition ℓ' where
  vec j := ∑ i ∈ Finset.univ.filter (fun i ↦ π i = j), v.vec i
  pairwise_orth j₁ j₂ hjj := by
    rw [sdpInner_sum_left]
    refine Finset.sum_eq_zero fun i₁ hi₁ ↦ ?_
    rw [sdpInner_sum_right]
    refine Finset.sum_eq_zero fun i₂ hi₂ ↦ ?_
    have h₁ : π i₁ = j₁ := (Finset.mem_filter.mp hi₁).2
    have h₂ : π i₂ = j₂ := (Finset.mem_filter.mp hi₂).2
    exact v.pairwise_orth fun h ↦ hjj (by subst h; rw [← h₁, ← h₂])
  sum_eq_single := by
    have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := π) (f := v.vec) (fun _ _ ↦ Finset.mem_univ _)
    simpa [v.sum_eq_single] using h

@[simp]
theorem minor_vec {ℓ ℓ' : ℕ} (π : Fin ℓ → Fin ℓ') (v : SdpPartition ℓ) (j : Fin ℓ') :
    (v.minor π).vec j = ∑ i ∈ Finset.univ.filter (fun i ↦ π i = j), v.vec i := by
  rfl

@[simp]
theorem minor_id {ℓ : ℕ} (v : SdpPartition ℓ) : v.minor id = v := by
  ext j k
  simp [Finset.sum_filter]

@[simp]
theorem minor_comp {ℓ ℓ' ℓ'' : ℕ} (π₁ : Fin ℓ → Fin ℓ') (π₂ : Fin ℓ' → Fin ℓ'')
    (v : SdpPartition ℓ) :
    (v.minor π₁).minor π₂ = v.minor (π₂ ∘ π₁) := by
  classical
  refine SdpPartition.ext (funext fun k ↦ ?_)
  simp only [minor_vec, Function.comp_apply]
  symm
  have hdisj : (Finset.univ.filter (fun j ↦ π₂ j = k) : Set (Fin ℓ')).PairwiseDisjoint
      (fun j ↦ Finset.univ.filter (fun i ↦ π₁ i = j)) := by
    intro j₁ _ j₂ _ hj
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
    exact hj (hi₁.symm.trans hi₂)
  rw [← Finset.sum_biUnion hdisj]
  congr 1
  ext i
  simp

end SdpPartition

/-- The *SDP minion* `sdpMinion`, whose `r`-ary operations (`0 < r`) are pairwise orthogonal
finitely supported real vector partitions summing to `Finsupp.single 0 1`. -/
@[expose]
noncomputable def sdpMinion : Minion.{0} where
  Carrier r _ := SdpPartition r
  nonempty _ hr := ⟨SdpPartition.single ⟨0, hr⟩⟩
  minor _ _ π v := SdpPartition.minor π v
  minor_id _ v := SdpPartition.minor_id v
  minor_comp _ _ _ π₁ π₂ v := SdpPartition.minor_comp π₁ π₂ v

@[simp]
theorem sdpMinion_minor_vec {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ')
    (v : sdpMinion.Carrier ℓ hℓ) (j : Fin ℓ') :
    (sdpMinion.minor hℓ hℓ' π v).vec j =
      ∑ i ∈ Finset.univ.filter (fun i ↦ π i = j), v.vec i := by
  rfl

private theorem starProjection_sum_of_pairwise_isOrtho {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {ι : Type*} (s : Finset ι)
    (U : ι → Submodule ℂ H) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → U i ⟂ U j) (w : H) :
    (⨆ i ∈ s, U i).starProjection w = ∑ i ∈ s, (U i).starProjection w := by
  classical
  let p : H := ∑ i ∈ s, (U i).starProjection w
  have hp_mem : p ∈ ⨆ i ∈ s, U i := by
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    exact le_iSup₂ (f := fun i (_ : i ∈ s) ↦ U i) i hi (Submodule.starProjection_apply_mem _ w)
  have hdiff_orth : w - p ∈ (⨆ i ∈ s, U i)ᗮ := by
    have hle : (⨆ i ∈ s, U i) ≤ (ℂ ∙ (w - p))ᗮ := by
      refine iSup₂_le fun j hj u hu ↦ ?_
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [inner_sub_left]
      have hsum_j : inner ℂ p u = inner ℂ w u := by
        simp only [p, sum_inner]
        rw [Finset.sum_eq_single j]
        · have hproj := Submodule.starProjection_inner_eq_zero (K := U j) w u hu
          rw [inner_sub_left] at hproj
          exact (sub_eq_zero.mp hproj).symm
        · intro i hi hij
          have hio : U i ⟂ U j := horth i hi j hj hij
          exact Submodule.isOrtho_iff_inner_eq.mp hio _ (Submodule.starProjection_apply_mem _ w)
            u hu
        · intro h; exact (h hj).elim
      rw [hsum_j, sub_self]
    rw [Submodule.mem_orthogonal]
    intro u hu
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hu)
  have h1 : (⨆ i ∈ s, U i).starProjection p = p :=
    Submodule.starProjection_eq_self_iff.mpr hp_mem
  have h2 : (⨆ i ∈ s, U i).starProjection (w - p) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := ⨆ i ∈ s, U i)).mpr hdiff_orth
  rw [map_sub, h1, sub_eq_zero] at h2
  exact h2

/-- `H` admits a minion homomorphism `quantumMinion ℂ H → sdpMinion`, sending each orthogonal
subspace partition `U` to the real coordinate vectors of `((U.subspace i).starProjection ψ)` for
a fixed unit vector `ψ : H`.
-/
theorem quantumMinion_to_sdpMinion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H] :
    MinionHomExists (quantumMinion ℂ H) sdpMinion := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : H)
  let ψ : H := (‖v₀‖⁻¹ : ℝ) • v₀
  have hψ_norm : ‖ψ‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v₀)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀)]
  have hψ_inner : inner ℂ ψ ψ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ_norm]
    simp
  let W : Submodule ℂ H := (ℂ ∙ ψ)ᗮ
  let bW := stdOrthonormalBasis ℂ W
  let coord : H →ₗ[ℝ] (ℕ →₀ ℝ) :=
    { toFun := fun x ↦
        Finsupp.single 0 (inner ℂ ψ x).re + Finsupp.single 1 (inner ℂ ψ x).im +
          ∑ k : Fin (Module.finrank ℂ W),
            (Finsupp.single (2 + 2 * k.1) (inner ℂ (bW k : H) x).re +
              Finsupp.single (2 + 2 * k.1 + 1) (inner ℂ (bW k : H) x).im)
      map_add' := fun x y ↦ by
        simp only [inner_add_right, Complex.add_re, Complex.add_im, Finsupp.single_add,
          Finset.sum_add_distrib]
        abel
      map_smul' := fun c x ↦ by
        have hsc : ∀ u : H, inner ℂ u (c • x) = (c : ℂ) * inner ℂ u x := fun u ↦ by
          rw [← Complex.coe_smul c x, inner_smul_right]
        simp only [hsc, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero, Finsupp.smul_single, smul_eq_mul, RingHom.id_apply,
          Finset.smul_sum, smul_add] }
  have hcoord_ψ : coord ψ = Finsupp.single 0 1 := by
    have hbW_orth : ∀ k : Fin (Module.finrank ℂ W), inner ℂ (bW k : H) ψ = 0 := fun k ↦ by
      have hk : (bW k : H) ∈ (ℂ ∙ ψ)ᗮ := (bW k).2
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp hk
    simp [coord, hbW_orth, hψ_norm]
  have hcoord_inner : ∀ x y : H, sdpInner (coord x) (coord y) = (inner ℂ x y).re := by
    intro x y
    have hre_im : ∀ z w : ℂ, z.re * w.re + z.im * w.im = (starRingEnd ℂ z * w).re := by
      intro z w
      simp [Complex.mul_re]
    have hpair : ∀ (a : ℕ) (z w : ℂ),
        sdpInner (Finsupp.single (2 * a) z.re + Finsupp.single (2 * a + 1) z.im)
          (Finsupp.single (2 * a) w.re + Finsupp.single (2 * a + 1) w.im) =
          (starRingEnd ℂ z * w).re := by
      intro a z w
      rw [sdpInner_add_left, sdpInner_add_right, sdpInner_add_right,
        sdpInner_single_single, sdpInner_single_single, sdpInner_single_single,
        sdpInner_single_single]
      have hne1 : 2 * a ≠ 2 * a + 1 := by omega
      have hne2 : 2 * a + 1 ≠ 2 * a := by omega
      simp only [hne1, hne2, ↓reduceIte, add_zero, zero_add]
      exact hre_im z w
    have hdisj_0 : ∀ (k : Fin (Module.finrank ℂ W)) (r₁ r₂ s₁ s₂ : ℝ),
        sdpInner (Finsupp.single 0 r₁ + Finsupp.single 1 r₂)
          (Finsupp.single (2 + 2 * k.1) s₁ + Finsupp.single (2 + 2 * k.1 + 1) s₂) = 0 := by
      intro k r₁ r₂ s₁ s₂
      rw [sdpInner_add_left, sdpInner_add_right, sdpInner_add_right,
        sdpInner_single_single, sdpInner_single_single, sdpInner_single_single,
        sdpInner_single_single]
      have h1 : (0 : ℕ) ≠ 2 + 2 * k.1 := by omega
      have h3 : (1 : ℕ) ≠ 2 + 2 * k.1 := by omega
      simp [h1, h3]
    have hdisj_kk : ∀ (k₁ k₂ : Fin (Module.finrank ℂ W)), k₁ ≠ k₂ →
        ∀ r₁ r₂ s₁ s₂ : ℝ,
        sdpInner (Finsupp.single (2 + 2 * k₁.1) r₁ + Finsupp.single (2 + 2 * k₁.1 + 1) r₂)
          (Finsupp.single (2 + 2 * k₂.1) s₁ + Finsupp.single (2 + 2 * k₂.1 + 1) s₂) = 0 := by
      intro k₁ k₂ hk r₁ r₂ s₁ s₂
      have hval : k₁.1 ≠ k₂.1 := fun h ↦ hk (Fin.ext h)
      rw [sdpInner_add_left, sdpInner_add_right, sdpInner_add_right,
        sdpInner_single_single, sdpInner_single_single, sdpInner_single_single,
        sdpInner_single_single]
      have h2 : 2 + 2 * k₁.1 ≠ 2 + 2 * k₂.1 + 1 := by omega
      have h3 : 2 + 2 * k₁.1 + 1 ≠ 2 + 2 * k₂.1 := by omega
      simp [h2, h3, hval]
    have hexpand :
        sdpInner (coord x) (coord y) =
          (inner ℂ x ψ * inner ℂ ψ y).re +
            ∑ k : Fin (Module.finrank ℂ W),
              (inner ℂ x (bW k : H) * inner ℂ (bW k : H) y).re := by
      let a₀ (u : H) : ℕ →₀ ℝ :=
        Finsupp.single 0 (inner ℂ ψ u).re + Finsupp.single 1 (inner ℂ ψ u).im
      let a₁ (u : H) : ℕ →₀ ℝ :=
        ∑ k : Fin (Module.finrank ℂ W),
          (Finsupp.single (2 + 2 * k.1) (inner ℂ (bW k : H) u).re +
            Finsupp.single (2 + 2 * k.1 + 1) (inner ℂ (bW k : H) u).im)
      change sdpInner (a₀ x + a₁ x) (a₀ y + a₁ y) = _
      rw [sdpInner_add_left, sdpInner_add_right (a₀ x), sdpInner_add_right (a₁ x)]
      have h00 : sdpInner (a₀ x) (a₀ y) = (inner ℂ x ψ * inner ℂ ψ y).re := by
        simpa [a₀, inner_conj_symm] using hpair 0 (inner ℂ ψ x) (inner ℂ ψ y)
      have h01 : sdpInner (a₀ x) (a₁ y) = 0 := by
        dsimp only [a₀, a₁]
        rw [sdpInner_sum_right]
        exact Finset.sum_eq_zero fun k _ ↦ hdisj_0 k _ _ _ _
      have h10 : sdpInner (a₁ x) (a₀ y) = 0 := by
        dsimp only [a₀, a₁]
        rw [sdpInner_comm, sdpInner_sum_right]
        exact Finset.sum_eq_zero fun k _ ↦ hdisj_0 k _ _ _ _
      have h11 :
          sdpInner (a₁ x) (a₁ y) =
            ∑ k : Fin (Module.finrank ℂ W),
              (inner ℂ x (bW k : H) * inner ℂ (bW k : H) y).re := by
        dsimp only [a₁]
        rw [sdpInner_sum_left]
        refine Finset.sum_congr rfl fun k₁ _ ↦ ?_
        rw [sdpInner_sum_right, Finset.sum_eq_single k₁]
        · have hstep := hpair (1 + k₁.1) (inner ℂ (bW k₁ : H) x) (inner ℂ (bW k₁ : H) y)
          have heq1 : 2 * (1 + k₁.1) = 2 + 2 * k₁.1 := by omega
          rw [heq1] at hstep
          simpa [inner_conj_symm] using hstep
        · intro k₂ _ hk
          exact hdisj_kk k₁ k₂ hk.symm _ _ _ _
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [h00, h01, h10, h11, add_zero, zero_add]
    rw [hexpand, ← Complex.re_sum, ← Complex.add_re]
    congr 1
    have hdecomp : ∀ u : H,
        u = inner ℂ ψ u • ψ + ∑ k : Fin (Module.finrank ℂ W), inner ℂ (bW k : H) u • (bW k : H) :=
      fun u ↦ by
        have hsum_proj : (ℂ ∙ ψ).starProjection u + W.starProjection u = u :=
          Submodule.starProjection_add_starProjection_orthogonal u
        have hproj_span : (ℂ ∙ ψ).starProjection u = inner ℂ ψ u • ψ := by
          rw [Submodule.starProjection_singleton, hψ_norm]
          simp
        have hproj_W :
            W.starProjection u =
              ∑ k : Fin (Module.finrank ℂ W), inner ℂ (bW k : H) u • (bW k : H) := by
          let uW : W := ⟨W.starProjection u, Submodule.starProjection_apply_mem W u⟩
          have hrepr : ∑ k : Fin (Module.finrank ℂ W), inner ℂ (bW k) uW • bW k = uW :=
            bW.sum_repr' uW
          have hval := congrArg Subtype.val hrepr
          simp only [Submodule.coe_sum, uW] at hval
          rw [← hval]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          change inner ℂ (bW k : H) (W.starProjection u) • (bW k : H) =
            inner ℂ (bW k : H) u • (bW k : H)
          congr 1
          have hsub_mem : u - W.starProjection u ∈ ℂ ∙ ψ := by
            have := Submodule.starProjection_add_starProjection_orthogonal (K := ℂ ∙ ψ) u
            have heq : u - W.starProjection u = (ℂ ∙ ψ).starProjection u :=
              sub_eq_of_eq_add this.symm
            rw [heq]
            exact Submodule.starProjection_apply_mem _ u
          have horth_k : inner ℂ (bW k : H) (u - W.starProjection u) = 0 := by
            rw [← inner_conj_symm, (Submodule.mem_orthogonal _ _).mp (bW k).2 _ hsub_mem, map_zero]
          rw [inner_sub_right] at horth_k
          exact (sub_eq_zero.mp horth_k).symm
        rw [← hproj_span, ← hproj_W, hsum_proj]
    conv_rhs => rw [hdecomp x]
    rw [inner_add_left, sum_inner]
    congr 1
    · rw [inner_smul_left, ← inner_conj_symm]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [inner_smul_left, ← inner_conj_symm]
  refine MinionHomExists.of_hom
    { toFun := fun {r} _ (U : OrthogonalPartition ℂ H r) ↦
        { vec := fun i ↦ coord ((U.subspace i).starProjection ψ)
          pairwise_orth := fun i j hij ↦ by
            rw [hcoord_inner]
            have horth := Submodule.isOrtho_iff_inner_eq.mp (U.pairwise_orth hij)
              _ (Submodule.starProjection_apply_mem _ ψ) _ (Submodule.starProjection_apply_mem _ ψ)
            rw [horth, Complex.zero_re]
          sum_eq_single := by
            rw [← map_sum]
            have hsum_top : ∑ i : Fin r, (U.subspace i).starProjection ψ = ψ := by
              have h := starProjection_sum_of_pairwise_isOrtho Finset.univ U.subspace
                (fun i _ j _ hij ↦ U.pairwise_orth hij) ψ
              have htop : (⨆ i ∈ (Finset.univ : Finset (Fin r)), U.subspace i) = ⊤ := by
                simpa using U.iSup_eq_top
              rw [htop, Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top] at h
              exact h.symm
            rw [hsum_top, hcoord_ψ] }
      map_minor' := fun {ℓ ℓ'} _ _ π (U : OrthogonalPartition ℂ H ℓ) ↦ by
        refine SdpPartition.ext (funext fun j ↦ ?_)
        dsimp only [quantumMinion, sdpMinion, OrthogonalPartition.minor, SdpPartition.minor]
        rw [← map_sum]
        congr 1
        have hfib : (⨆ (i : Fin ℓ) (_ : π i = j), U.subspace i) =
            ⨆ i ∈ Finset.univ.filter (fun i ↦ π i = j), U.subspace i := by
          refine le_antisymm ?_ ?_
          · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
            exact le_iSup₂ (f := fun i' (_ : i' ∈ Finset.univ.filter (fun i' ↦ π i' = j)) ↦
                U.subspace i') i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
            exact le_iSup₂ (f := fun i' (_ : π i' = j) ↦ U.subspace i') i
              (Finset.mem_filter.mp hi).2
        have hstar_eq : ∀ {K₁ K₂ : Submodule ℂ H}, K₁ = K₂ →
            K₁.starProjection ψ = K₂.starProjection ψ := by
          rintro K _ rfl
          rfl
        rw [hstar_eq hfib]
        exact starProjection_sum_of_pairwise_isOrtho _ U.subspace
          (fun i₁ _ i₂ _ h ↦ U.pairwise_orth h) ψ }


/-! ### Quantum Homomorphism Strategies and Pseudo-Telepathy -/

open FirstOrder Language Structure

/-! ### Quantum Homomorphism Strategies and Pseudo-Telepathy -/

/-- A relational constraint in an `L`-structure `X`: a relation symbol `symbol` of arity `arity`
together with a tuple in `X` satisfying `RelMap symbol tuple`. -/
structure RelConstraint (L : Language.{u, v}) (X : Type w) [L.Structure X] :
    Type (max v w) where
  /-- Arity of the relation symbol. -/
  arity : ℕ
  /-- Relation symbol appearing in the constraint. -/
  symbol : L.Relations arity
  /-- Tuple of elements of `X` satisfying the relation. -/
  tuple : Fin arity → X
  /-- Witness that `RelMap symbol tuple` holds in `X`. -/
  mem_rel : RelMap symbol tuple

/-- A projective quantum homomorphism strategy from `X` to `Y` over a finite-dimensional
complex Hilbert space `H` using the maximally entangled state. -/
structure QuantumHomStrategy (L : Language.{u, v}) (X : Type w) (Y : Type w')
    [L.Structure X] [L.Structure Y] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] where
  /-- Alice's measurement subspace for constraint `c` and output tuple `y`. -/
  aliceSubspace : (c : RelConstraint L X) → (Fin c.arity → Y) → Submodule ℂ H
  /-- Nonzero Alice subspaces occur only on valid tuples of the relation `c.symbol` in `Y`. -/
  alice_mem_rel : ∀ (c : RelConstraint L X) (y : Fin c.arity → Y),
    aliceSubspace c y ≠ ⊥ → RelMap c.symbol y
  /-- Alice's subspaces for distinct output tuples at constraint `c` are orthogonal. -/
  alice_orth : ∀ (c : RelConstraint L X) ⦃y₁ y₂ : Fin c.arity → Y⦄,
    y₁ ≠ y₂ → aliceSubspace c y₁ ⟂ aliceSubspace c y₂
  /-- Alice's measurement subspaces at constraint `c` span all of `H`. -/
  alice_complete : ∀ (c : RelConstraint L X), (⨆ y : Fin c.arity → Y, aliceSubspace c y) = ⊤
  /-- Bob's measurement subspace for input `x : X` and output `y : Y`. -/
  bobSubspace : X → Y → Submodule ℂ H
  /-- Bob's subspaces for distinct outputs at input `x` are orthogonal. -/
  bob_orth : ∀ (x : X) ⦃y₁ y₂ : Y⦄, y₁ ≠ y₂ → bobSubspace x y₁ ⟂ bobSubspace x y₂
  /-- Bob's measurement subspaces at input `x` span all of `H`. -/
  bob_complete : ∀ (x : X), (⨆ y : Y, bobSubspace x y) = ⊤
  /-- Consistency on the maximally entangled state: inconsistent outcomes are orthogonal. -/
  consistent : ∀ (c : RelConstraint L X) (y : Fin c.arity → Y) (i : Fin c.arity) (y' : Y),
    y i ≠ y' → aliceSubspace c y ⟂ bobSubspace (c.tuple i) y'

namespace QuantumHomStrategy

/-- If `y` does not satisfy `c.symbol` in `Y`, then `aliceSubspace c y = ⊥`. -/
theorem aliceSubspace_eq_bot_of_not_relMap {L : Language.{u, v}} {X : Type w} {Y : Type w'}
    [L.Structure X] [L.Structure Y] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (s : QuantumHomStrategy L X Y H)
    {c : RelConstraint L X} {y : Fin c.arity → Y} (hy : ¬ RelMap c.symbol y) :
    s.aliceSubspace c y = ⊥ :=
  not_ne_iff.mp fun hne ↦ hy (s.alice_mem_rel c y hne)

end QuantumHomStrategy

/-- An `L`-structure `Y` is *pseudo-telepathic over `H`* if some finite `L`-structure `X` admits a
quantum homomorphism strategy to `Y` over `H` while admitting no classical `L`-homomorphism
`X →[L] Y`. -/
def IsPseudoTelepathicOver (L : Language.{u, v}) (Y : Type w) [L.Structure Y]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] : Prop :=
  ∃ (X : Type) (_ : Finite X) (_ : L.Structure X),
    Nonempty (QuantumHomStrategy L X Y H) ∧ IsEmpty (X →[L] Y)

/-- Characterization of `IsPseudoTelepathicOver` as an existential witness over finite
`L`-structures. -/
theorem isPseudoTelepathicOver_iff {L : Language.{u, v}} {Y : Type w} [L.Structure Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] :
    IsPseudoTelepathicOver L Y H ↔
      ∃ (X : Type) (_ : Finite X) (_ : L.Structure X),
        Nonempty (QuantumHomStrategy L X Y H) ∧ IsEmpty (X →[L] Y) := by
  rfl

/-- An `L`-structure `Y` is *pseudo-telepathic* if it is pseudo-telepathic over `ℂ^d` for some
positive dimension `0 < d`. -/
def IsPseudoTelepathic (L : Language.{u, v}) (Y : Type w) [L.Structure Y] : Prop :=
  ∃ d : ℕ, 0 < d ∧ IsPseudoTelepathicOver L Y (EuclideanSpace ℂ (Fin d))

/-- Characterization of `IsPseudoTelepathic` via existence of a positive Hilbert-space dimension. -/
theorem isPseudoTelepathic_iff {L : Language.{u, v}} {Y : Type w} [L.Structure Y] :
    IsPseudoTelepathic L Y ↔
      ∃ d : ℕ, 0 < d ∧ IsPseudoTelepathicOver L Y (EuclideanSpace ℂ (Fin d)) := by
  rfl

/-! ### Characterization via the Quantum Minion -/

private def bobPartition {L : Language.{u, v}} {X : Type w} {Y : Type w'}
    [L.Structure X] [L.Structure Y] {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (s : QuantumHomStrategy L X Y H)
    {r₀ : ℕ} (eY : Fin r₀ ≃ Y) (x : X) : OrthogonalPartition ℂ H r₀ where
  subspace k := s.bobSubspace x (eY k)
  pairwise_orth _ _ h := s.bob_orth x (eY.injective.ne h)
  iSup_eq_top := by
    rw [eY.iSup_comp]
    exact s.bob_complete x

private def alicePartition {L : Language.{u, v}} {X : Type w} {Y : Type w'}
    [L.Structure X] [L.Structure Y] {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (s : QuantumHomStrategy L X Y H)
    (c : RelConstraint L X) {r : ℕ}
    (eR : Fin r ≃ { y : Fin c.arity → Y // RelMap c.symbol y }) :
    OrthogonalPartition ℂ H r where
  subspace k := s.aliceSubspace c (eR k).1
  pairwise_orth _ _ h := s.alice_orth c (fun heq ↦ h (eR.injective (Subtype.ext heq)))
  iSup_eq_top := top_unique <| by
    rw [← s.alice_complete c]
    refine iSup_le fun y ↦ ?_
    by_cases hy : RelMap c.symbol y
    · refine le_iSup_of_le (eR.symm ⟨y, hy⟩) ?_
      simp
    · rw [s.aliceSubspace_eq_bot_of_not_relMap hy]
      exact bot_le

private theorem alicePartition_minor_eq_bob {L : Language.{u, v}} {X : Type w} {Y : Type w'}
    [L.Structure X] [L.Structure Y] {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (s : QuantumHomStrategy L X Y H)
    (c : RelConstraint L X) {r₀ r : ℕ} (eY : Fin r₀ ≃ Y)
    (eR : Fin r ≃ { y : Fin c.arity → Y // RelMap c.symbol y }) (i : Fin c.arity) :
    (alicePartition s c eR).minor (fun k ↦ eY.symm ((eR k).1 i)) =
      bobPartition s eY (c.tuple i) := by
  refine OrthogonalPartition.eq_of_subspace_le fun m ↦ ?_
  rw [OrthogonalPartition.minor_subspace]
  refine iSup₂_le fun k hk ↦ ?_
  refine (bobPartition s eY (c.tuple i)).le_subspace_of_pairwise_isOrtho fun m' hm' ↦ ?_
  have hne : (eR k).1 i ≠ eY m' := by
    intro heq
    apply hm'
    rw [← hk, heq, eY.symm_apply_apply]
  exact s.consistent c (eR k).1 i (eY m') hne

/-- If there exists a minion homomorphism from the quantum minion over `H` into the polymorphism
minion of `Y`, then `Y` is not pseudo-telepathic over `H`. -/
theorem not_isPseudoTelepathicOver_of_minionHomExists {L : Language.{u, v}} {Y : Type w}
    [L.IsRelational] [IsEmpty (L.Relations 0)] [L.Structure Y] [Finite Y] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H]
    (hMinion : MinionHomExists (quantumMinion ℂ H) (polMinion L Y)) :
    ¬ IsPseudoTelepathicOver L Y H := by
  classical
  rintro ⟨X, _, _, ⟨s⟩, hEmpty⟩
  by_cases hY : IsEmpty Y
  · by_cases hX : IsEmpty X
    · refine hEmpty.false (homOfRel (fun x ↦ isEmptyElim x) fun {n} R x _ ↦ ?_)
      cases n with
      | zero => exact isEmptyElim R
      | succ k => exact isEmptyElim (x 0)
    · rw [not_isEmpty_iff] at hX
      obtain ⟨x₀⟩ := hX
      have htop : (⊤ : Submodule ℂ H) = ⊥ := by
        rw [← s.bob_complete x₀]
        exact iSup_eq_bot.mpr fun y ↦ isEmptyElim y
      obtain ⟨v, hv⟩ := exists_ne (0 : H)
      have hv_bot : v ∈ (⊥ : Submodule ℂ H) := by
        rw [← htop]
        trivial
      exact hv ((Submodule.mem_bot ℂ).mp hv_bot)
  · rw [not_isEmpty_iff] at hY
    let _ : Fintype Y := Fintype.ofFinite Y
    let r₀ : ℕ := Fintype.card Y
    have hr₀ : 0 < r₀ := Fintype.card_pos
    let eY : Fin r₀ ≃ Y := (Fintype.equivFin Y).symm
    rw [minionHomExists_iff] at hMinion
    obtain ⟨ξ⟩ := hMinion
    let f : X → Y := fun x ↦ ξ.toFun hr₀ (bobPartition s eY x) eY
    refine hEmpty.false (homOfRel f fun {n} R a ha ↦ ?_)
    cases n with
    | zero => exact isEmptyElim R
    | succ m =>
      let c : RelConstraint L X := ⟨m + 1, R, a, ha⟩
      let T := { y : Fin (m + 1) → Y // RelMap R y }
      have hT_nonempty : Nonempty T := by
        by_contra hT
        rw [not_nonempty_iff] at hT
        have htop : (⊤ : Submodule ℂ H) = ⊥ := by
          rw [← s.alice_complete c]
          refine iSup_eq_bot.mpr fun y ↦ s.aliceSubspace_eq_bot_of_not_relMap ?_
          exact fun hy ↦ hT.false ⟨y, hy⟩
        obtain ⟨v, hv⟩ := exists_ne (0 : H)
        have hv_bot : v ∈ (⊥ : Submodule ℂ H) := by
          rw [← htop]
          trivial
        exact hv ((Submodule.mem_bot ℂ).mp hv_bot)
      let r : ℕ := Fintype.card T
      have hr : 0 < r := Fintype.card_pos
      let eR : Fin r ≃ T := (Fintype.equivFin T).symm
      let A := alicePartition s c eR
      let _ := piStructure L (fun _ : Fin r ↦ Y)
      let φ : (Fin r → Y) →[L] Y := ξ.toFun hr A
      let col : Fin (m + 1) → Fin r → Y := fun i k ↦ (eR k).1 i
      have hcol_rel : RelMap R col := (pi_relMap R col).mpr fun k ↦ (eR k).2
      have hφ_rel : RelMap R (fun i ↦ φ (col i)) := φ.map_rel' R col hcol_rel
      have h_eq : f ∘ a = fun i ↦ φ (col i) := by
        ext i
        have hminor :
            (quantumMinion ℂ H).minor hr hr₀ (fun k ↦ eY.symm ((eR k).1 i)) A =
              bobPartition s eY (a i) :=
          alicePartition_minor_eq_bob s c eY eR i
        have hξ := ξ.map_minor hr hr₀ (fun k ↦ eY.symm ((eR k).1 i)) A
        change ξ.toFun hr₀ (bobPartition s eY (a i)) eY = φ (col i)
        rw [← hminor, hξ, polMinion_minor_apply]
        congr 1
        ext k
        exact eY.apply_symm_apply ((eR k).1 i)
      rw [h_eq]
      exact hφ_rel

private structure ConstraintIdx (L : Language.{u, v}) (Y : Type w) [L.Structure Y]
    (eRel : ∀ {n : ℕ} (R : L.Relations n),
      Σ r : ℕ, Fin r ≃ { y : Fin n → Y // RelMap R y })
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Type (max v uH) where
  arity : ℕ
  symbol : L.Relations arity
  nonempty_rel : 0 < (eRel symbol).1
  tuple : OrthogonalPartition ℂ H (eRel symbol).1

private noncomputable def minionHomOfIsEmpty {L : Language.{u, v}} {Y : Type w}
    [L.IsRelational] [IsEmpty (L.Relations 0)] [L.Structure Y] [IsEmpty Y]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    MinionHom (quantumMinion ℂ H) (polMinion L Y) where
  toFun {ℓ} hℓ _ :=
    let _ := piStructure L (fun _ : Fin ℓ ↦ Y)
    homOfRel (fun x : Fin ℓ → Y ↦ isEmptyElim (x ⟨0, hℓ⟩)) fun {n} R x _ ↦ by
      cases n with
      | zero => exact isEmptyElim R
      | succ k => exact isEmptyElim ((x 0) ⟨0, hℓ⟩)
  map_minor' _ hℓ' _ _ := Hom.ext fun x ↦ isEmptyElim (x ⟨0, hℓ'⟩)

private theorem finite_intersection_nonempty {L : Language.{u, v}} {Y : Type w}
    [L.IsRelational] [L.Structure Y] [Nonempty Y] {H : Type uH}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (hNotPT : ¬ IsPseudoTelepathicOver L Y H)
    {r₀ : ℕ} (eY : Fin r₀ ≃ Y)
    (eRel : ∀ {n : ℕ} (R : L.Relations n),
      Σ r : ℕ, Fin r ≃ { y : Fin n → Y // RelMap R y })
    (s : Finset (ConstraintIdx L Y eRel H)) :
    (⋂ idx ∈ s, { h : OrthogonalPartition ℂ H r₀ → Y |
      RelMap idx.symbol (fun i ↦ h (idx.tuple.minor
        (fun j ↦ eY.symm (((eRel idx.symbol).2 j).1 i)))) }).Nonempty := by
  classical
  let V := OrthogonalPartition ℂ H r₀
  let varTuple (idx : ConstraintIdx L Y eRel H) : Fin idx.arity → V :=
    fun i ↦ idx.tuple.minor (fun j ↦ eY.symm (((eRel idx.symbol).2 j).1 i))
  let S : Finset V := s.biUnion fun idx ↦ Finset.univ.image (varTuple idx)
  let X_sub := Fin S.card
  let eS : X_sub ≃ { v : V // v ∈ S } := (S.equivFin).symm
  let val : X_sub → V := fun x ↦ (eS x).1
  let strX : L.Structure X_sub :=
    { funMap := fun {_} fn ↦ isEmptyElim fn
      RelMap := fun {n} R t ↦
        ∃ (hn : 0 < (eRel R).1) (W : OrthogonalPartition ℂ H (eRel R).1),
          (⟨n, R, hn, W⟩ : ConstraintIdx L Y eRel H) ∈ s ∧
            (fun i ↦ val (t i)) =
              fun i ↦ W.minor (fun j ↦ eY.symm (((eRel R).2 j).1 i)) }
  have hmem_S : ∀ {idx : ConstraintIdx L Y eRel H} (hidx : idx ∈ s) (i : Fin idx.arity),
      varTuple idx i ∈ S := fun {idx} hidx i ↦
    Finset.mem_biUnion.mpr ⟨idx, hidx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  let strat : @QuantumHomStrategy L X_sub Y strX _ H _ _ _ :=
    { aliceSubspace := fun c y ↦
        if hy : RelMap c.symbol y then
          (Classical.choose (Classical.choose_spec c.mem_rel)).subspace
            ((eRel c.symbol).2.symm ⟨y, hy⟩)
        else ⊥
      alice_mem_rel := fun c y hne ↦ by
        by_contra hy
        simp only [hy, ↓reduceDIte] at hne
        exact hne rfl
      alice_orth := fun c y₁ y₂ hne ↦ by
        split_ifs with h₁ h₂
        · exact (Classical.choose (Classical.choose_spec c.mem_rel)).pairwise_orth
            fun heq ↦ hne (congr_arg Subtype.val ((eRel c.symbol).2.symm.injective heq))
        · exact Submodule.isOrtho_bot_right
        · exact Submodule.isOrtho_bot_left
        · exact Submodule.isOrtho_bot_left
      alice_complete := fun c ↦ top_unique <| by
        rw [← (Classical.choose (Classical.choose_spec c.mem_rel)).iSup_eq_top]
        refine iSup_le fun j ↦ ?_
        have hj : RelMap c.symbol ((eRel c.symbol).2 j).1 := ((eRel c.symbol).2 j).2
        refine le_iSup_of_le ((eRel c.symbol).2 j).1 ?_
        split_ifs
        simp
      bobSubspace := fun x y ↦ (val x).subspace (eY.symm y)
      bob_orth := fun x y₁ y₂ hne ↦ (val x).pairwise_orth (eY.symm.injective.ne hne)
      bob_complete := fun x ↦ by
        rw [eY.symm.iSup_comp]
        exact (val x).iSup_eq_top
      consistent := fun c y i y' hne ↦ by
        split_ifs with hy
        · have hspec := Classical.choose_spec (Classical.choose_spec c.mem_rel)
          have hval := congr_fun hspec.2 i
          rw [hval, OrthogonalPartition.minor_subspace, Submodule.isOrtho_iSup_right]
          intro k
          rw [Submodule.isOrtho_iSup_right]
          intro hk
          refine (Classical.choose (Classical.choose_spec c.mem_rel)).pairwise_orth fun heq ↦ ?_
          apply hne
          have hk' : ((eRel c.symbol).2 k).1 i = y' := eY.symm.injective hk
          have hyk : ((eRel c.symbol).2 ((eRel c.symbol).2.symm ⟨y, hy⟩)).1 i =
              ((eRel c.symbol).2 k).1 i := by
            rw [heq]
          simpa using hyk.trans hk'
        · exact Submodule.isOrtho_bot_left }
  have hNonEmptyHom : ¬ @IsEmpty (X_sub →[L] Y) := by
    intro hEmpty
    exact hNotPT ⟨X_sub, inferInstance, strX, ⟨strat⟩, hEmpty⟩
  rw [not_isEmpty_iff] at hNonEmptyHom
  obtain ⟨f⟩ := hNonEmptyHom
  let h : V → Y := fun v ↦ if hv : v ∈ S then f (eS.symm ⟨v, hv⟩) else Classical.arbitrary Y
  refine ⟨h, Set.mem_iInter.mpr fun idx ↦ Set.mem_iInter.mpr fun hidx ↦ ?_⟩
  let t : Fin idx.arity → X_sub := fun i ↦ eS.symm ⟨varTuple idx i, hmem_S hidx i⟩
  have ht_val : (fun i ↦ val (t i)) = varTuple idx := funext fun i ↦ by
    simp only [val, t, eS.apply_symm_apply]
  have ht_rel : @RelMap L X_sub strX idx.arity idx.symbol t :=
    ⟨idx.nonempty_rel, idx.tuple, hidx, ht_val⟩
  have hf_rel : RelMap idx.symbol (f ∘ t) := f.map_rel' idx.symbol t ht_rel
  have hf_eq : f ∘ t = fun i ↦ h (varTuple idx i) := funext fun i ↦ by
    change f (t i) = if hv : varTuple idx i ∈ S then f (eS.symm ⟨varTuple idx i, hv⟩) else _
    split_ifs with hv
    · rfl
    · exact absurd (hmem_S hidx i) hv
  change RelMap idx.symbol fun i ↦ h (varTuple idx i)
  rw [← hf_eq]
  exact hf_rel

/-- (with no `0`-ary relations) is pseudo-telepathic over a nontrivial finite-dimensional complex
Hilbert space `H` if and only if there is no minion homomorphism from `quantumMinion ℂ H` to
`polMinion L Y`.
-/
theorem isPseudoTelepathicOver_iff_not_minionHomExists {L : Language.{u, v}} {Y : Type w}
    [L.IsRelational] [IsEmpty (L.Relations 0)] [L.Structure Y] [Finite Y] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H] :
    IsPseudoTelepathicOver L Y H ↔
      ¬ MinionHomExists (quantumMinion ℂ H) (polMinion L Y) := by
  refine ⟨fun hPT hMinion ↦ not_isPseudoTelepathicOver_of_minionHomExists hMinion hPT, ?_⟩
  intro hNotMinion
  by_contra hNotPT
  apply hNotMinion
  by_cases hY : IsEmpty Y
  · exact MinionHomExists.of_hom (minionHomOfIsEmpty H)
  · rw [not_isEmpty_iff] at hY
    classical
    let _ : Fintype Y := Fintype.ofFinite Y
    let r₀ : ℕ := Fintype.card Y
    let eY : Fin r₀ ≃ Y := (Fintype.equivFin Y).symm
    let eRel : ∀ {n : ℕ} (R : L.Relations n),
        Σ r : ℕ, Fin r ≃ { y : Fin n → Y // RelMap R y } := fun R ↦
      ⟨Fintype.card { y : Fin _ → Y // RelMap R y }, (Fintype.equivFin _).symm⟩
    let _ : TopologicalSpace Y := ⊥
    have _ : DiscreteTopology Y := discreteTopology_bot Y
    let V := OrthogonalPartition ℂ H r₀
    let C : ConstraintIdx L Y eRel H → Set (V → Y) := fun idx ↦
      { h : V → Y | RelMap idx.symbol (fun i ↦ h (idx.tuple.minor
        (fun j ↦ eY.symm (((eRel idx.symbol).2 j).1 i)))) }
    have hC_closed : ∀ idx, IsClosed (C idx) := fun idx ↦ by
      let proj : (V → Y) → (Fin idx.arity → Y) := fun h i ↦
        h (idx.tuple.minor (fun j ↦ eY.symm (((eRel idx.symbol).2 j).1 i)))
      have hproj : Continuous proj :=
        continuous_pi fun i ↦ continuous_apply _
      exact (isClosed_discrete { y : Fin idx.arity → Y | RelMap idx.symbol y }).preimage hproj
    have hInter := CompactSpace.iInter_nonempty hC_closed
      (finite_intersection_nonempty hNotPT eY eRel)
    obtain ⟨h, hh⟩ := hInter
    have hHom : ∀ {r : ℕ} (hr : 0 < r) (W : OrthogonalPartition ℂ H r)
        {n : ℕ} (R : L.Relations n) (a : Fin n → Fin r → Y),
        @RelMap L (Fin r → Y) (piStructure L (fun _ ↦ Y)) n R a →
        RelMap R (fun i ↦ h (W.minor (eY.symm ∘ a i))) := by
      intro r hr W n R a ha
      have ha' := (pi_relMap R a).mp ha
      have hR : 0 < (eRel R).1 := by
        let y₀ : Fin n → Y := fun i ↦ a i ⟨0, hr⟩
        have hy₀ : RelMap R y₀ := ha' ⟨0, hr⟩
        exact Fintype.card_pos_iff.mpr ⟨⟨y₀, hy₀⟩⟩
      let σ : Fin r → Fin (eRel R).1 := fun k ↦ (eRel R).2.symm ⟨fun i ↦ a i k, ha' k⟩
      let idx : ConstraintIdx L Y eRel H := ⟨n, R, hR, W.minor σ⟩
      have hmem : h ∈ C idx := Set.mem_iInter.mp hh idx
      have hsub : ∀ i : Fin n,
          idx.tuple.minor (fun j ↦ eY.symm (((eRel R).2 j).1 i)) = W.minor (eY.symm ∘ a i) := by
        intro i
        rw [OrthogonalPartition.minor_comp]
        congr 1
        funext k
        dsimp only [Function.comp_apply, σ]
        simp
      simpa only [C, idx, Set.mem_ofPred_eq, hsub] using hmem
    let mkHom : ∀ {r : ℕ} (hr : 0 < r),
        OrthogonalPartition ℂ H r →
          @Hom L (Fin r → Y) Y (piStructure L (fun _ ↦ Y)) _ := fun {r} hr W ↦
      let _ := piStructure L (fun _ : Fin r ↦ Y)
      homOfRel (fun z ↦ h (W.minor (eY.symm ∘ z))) fun {n} R a ha ↦ hHom hr W R a ha
    refine MinionHomExists.of_hom
      { toFun := fun {r} hr W ↦ mkHom hr W
        map_minor' := fun hℓ hℓ' π W ↦ Hom.ext fun z ↦ by
          have hmc :
              OrthogonalPartition.minor (eY.symm ∘ z) (OrthogonalPartition.minor π W) =
                OrthogonalPartition.minor ((eY.symm ∘ z) ∘ π) W :=
            OrthogonalPartition.minor_comp π (eY.symm ∘ z) W
          have hL :
              mkHom hℓ' ((quantumMinion ℂ H).minor hℓ hℓ' π W) z =
                h (OrthogonalPartition.minor ((eY.symm ∘ z) ∘ π) W) := by
            change (mkHom hℓ' (OrthogonalPartition.minor π W)) z = _
            dsimp only [mkHom]
            rw [homOfRel_apply, hmc]
          have hR :
              ((polMinion L Y).minor hℓ hℓ' π (mkHom hℓ W)) z =
                h (OrthogonalPartition.minor (eY.symm ∘ fun i ↦ z (π i)) W) := by
            have hp : ((polMinion L Y).minor hℓ hℓ' π (mkHom hℓ W)) z =
                mkHom hℓ W (fun i ↦ z (π i)) :=
              polMinion_minor_apply hℓ hℓ' π (mkHom hℓ W) z
            rw [hp]
            dsimp only [mkHom]
            rw [homOfRel_apply]
          exact hL.trans hR.symm }

/-- An `L`-structure `Y` (with `[L.IsRelational]`, `[IsEmpty (L.Relations 0)]`, and `[Finite Y]`)
is pseudo-telepathic if and only if there exists `0 < d` such that no minion homomorphism exists
from `quantumMinion ℂ (EuclideanSpace ℂ (Fin d))` to `polMinion L Y`. -/
theorem isPseudoTelepathic_iff_exists_not_minionHomExists {L : Language.{u, v}} {Y : Type w}
    [L.IsRelational] [IsEmpty (L.Relations 0)] [L.Structure Y] [Finite Y] :
    IsPseudoTelepathic L Y ↔
      ∃ d : ℕ, 0 < d ∧
        ¬ MinionHomExists (quantumMinion ℂ (EuclideanSpace ℂ (Fin d))) (polMinion L Y) := by
  refine exists_congr fun d ↦ and_congr_right fun hd ↦ ?_
  have _ : Nontrivial (EuclideanSpace ℂ (Fin d)) := by
    refine ⟨⟨EuclideanSpace.single ⟨0, hd⟩ 1, 0, ?_⟩⟩
    intro h
    have := congr_fun (congr_arg WithLp.ofLp h) ⟨0, hd⟩
    simp at this
  exact isPseudoTelepathicOver_iff_not_minionHomExists

/-! ### Unmarked SDP Rounding and Majority Separations -/

private noncomputable def sdpTwoColoringVec {r : ℕ} (v : SdpPartition r) (x : Fin r → Bool) :
    ℕ →₀ ℝ :=
  ∑ i : Fin r, (if x i then (1 : ℝ) else -1) • v.vec i

private lemma sdpTwoColoringVec_neg {r : ℕ} (v : SdpPartition r) (x : Fin r → Bool) :
    sdpTwoColoringVec v (fun i ↦ !x i) = -sdpTwoColoringVec v x := by
  simp only [sdpTwoColoringVec, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : x i <;> simp [h]

private lemma sdpTwoColoringVec_ne_zero {r : ℕ} (v : SdpPartition r) (x : Fin r → Bool) :
    sdpTwoColoringVec v x ≠ 0 := by
  intro h0
  have hinner : sdpInner (sdpTwoColoringVec v x) (sdpTwoColoringVec v x) = 1 := by
    simp only [sdpTwoColoringVec, sdpInner_sum_left]
    have hdiag :
        (∑ i : Fin r, ∑ j : Fin r,
          sdpInner ((if x i then (1 : ℝ) else -1) • v.vec i)
            ((if x j then (1 : ℝ) else -1) • v.vec j)) =
          ∑ i : Fin r, sdpInner (v.vec i) (v.vec i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i]
      · rw [sdpInner_smul_left, sdpInner_smul_right]
        by_cases h : x i <;> simp [h]
      · intro j _ hji
        rw [sdpInner_smul_left, sdpInner_smul_right, v.pairwise_orth hji.symm, mul_zero, mul_zero]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hsum :
        ∑ i : Fin r, sdpInner (v.vec i) (v.vec i) =
          sdpInner (∑ i : Fin r, v.vec i) (∑ j : Fin r, v.vec j) := by
      rw [sdpInner_sum_left]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [sdpInner_sum_right, Finset.sum_eq_single i]
      · intro j _ hji
        exact v.pairwise_orth hji.symm
      · intro h; exact (h (Finset.mem_univ _)).elim
    simp_rw [sdpInner_sum_right]
    rw [hdiag, hsum, v.sum_eq_single, sdpInner_single_single]
    simp
  rw [h0, sdpInner_zero_left] at hinner
  norm_num at hinner

private lemma sdpTwoColoringVec_minor {ℓ ℓ' : ℕ} (π : Fin ℓ → Fin ℓ') (v : SdpPartition ℓ)
    (z : Fin ℓ' → Bool) :
    sdpTwoColoringVec (v.minor π) z = sdpTwoColoringVec v (z ∘ π) := by
  simp only [sdpTwoColoringVec, SdpPartition.minor_vec, Finset.smul_sum, Function.comp_apply]
  have hrew :
      (∑ j : Fin ℓ', ∑ i ∈ Finset.univ.filter (fun i ↦ π i = j),
          (if z j then (1 : ℝ) else -1) • v.vec i) =
        ∑ j : Fin ℓ', ∑ i ∈ Finset.univ.filter (fun i ↦ π i = j),
          (if z (π i) then (1 : ℝ) else -1) • v.vec i := by
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [hrew]
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := π) (f := fun i ↦ (if z (π i) then (1 : ℝ) else -1) • v.vec i)
    (fun _ _ ↦ Finset.mem_univ _)

/-- Unmarked explicit SDP rounding for graph $2$-coloring under standard Lean axioms: there exists
a minion homomorphism from `sdpMinion` into `polMinion twoColoringLang Bool`, mapping each SDP
partition `v` to the lexicographic first-nonzero-coordinate sign of
`∑ i, (if x i then 1 else -1) • v.vec i`. -/
theorem sdpMinion_to_polMinion_twoColoring :
    MinionHomExists sdpMinion (polMinion twoColoringLang Bool) := by
  classical
  let roundVec : (ℕ →₀ ℝ) → Bool := fun w ↦
    if h : w.support.Nonempty then decide (0 < w (w.support.min' h)) else false
  have hround_neg : ∀ w : ℕ →₀ ℝ, w ≠ 0 → roundVec (-w) = !roundVec w := by
    intro w hw
    have hsupp : (-w).support = w.support := Finsupp.support_neg w
    have hne : w.support.Nonempty := Finsupp.support_nonempty_iff.mpr hw
    have hne' : (-w).support.Nonempty := by rwa [hsupp]
    have hmin : (-w).support.min' hne' = w.support.min' hne := by
      simp [hsupp]
    have hnz : w (w.support.min' hne) ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.min'_mem w.support hne)
    simp only [roundVec, hne, hne', ↓reduceDIte, hmin, Finsupp.neg_apply]
    rcases lt_or_gt_of_ne hnz with hlt | hgt
    · have hpos : 0 < -w (w.support.min' hne) := neg_pos.mpr hlt
      have hnot : ¬ (0 < w (w.support.min' hne)) := not_lt_of_gt hlt
      simp [hpos, hnot]
    · have hnot : ¬ (0 < -w (w.support.min' hne)) := not_lt_of_gt (neg_lt_zero.mpr hgt)
      simp [hgt, hnot]
  let mkHom {r : ℕ} (v : SdpPartition r) : (Fin r → Bool) →[twoColoringLang] Bool :=
    let _ := piStructure twoColoringLang (fun _ : Fin r ↦ Bool)
    homOfRel (fun x ↦ roundVec (sdpTwoColoringVec v x)) fun {n} R a ha ↦ by
      cases R
      have ha' : ∀ k : Fin r, a 0 k ≠ a 1 k := fun k ↦
        (twoColoringLang_relMap_ne_iff _).mp
          ((pi_relMap (L := twoColoringLang) TwoColoringRel.ne a).mp ha k)
      have ha1 : a 1 = fun k ↦ !(a 0 k) := funext fun k ↦ by
        have hk := ha' k
        cases h0 : a 0 k <;> cases h1 : a 1 k <;> simp_all
      rw [twoColoringLang_relMap_ne_iff]
      change roundVec (sdpTwoColoringVec v (a 0)) ≠ roundVec (sdpTwoColoringVec v (a 1))
      rw [ha1, sdpTwoColoringVec_neg, hround_neg _ (sdpTwoColoringVec_ne_zero v (a 0))]
      cases roundVec (sdpTwoColoringVec v (a 0)) <;> decide
  have hmk : ∀ {r : ℕ} (v : SdpPartition r) (x : Fin r → Bool),
      mkHom v x = roundVec (sdpTwoColoringVec v x) := fun v x ↦ homOfRel_apply _ _ x
  refine MinionHomExists.of_hom
    { toFun := fun {r} _ (v : SdpPartition r) ↦ mkHom v
      map_minor' := fun {ℓ ℓ'} hℓ hℓ' π (v : SdpPartition ℓ) ↦ Hom.ext fun z ↦
        (hmk (v.minor π) z).trans <|
          (congrArg roundVec (sdpTwoColoringVec_minor π v z)).trans <|
            (hmk v (z ∘ π)).symm.trans (polMinion_minor_apply hℓ hℓ' π (mkHom v) z).symm }

/-- Unmarked proof under standard Lean axioms that graph $2$-coloring (`K₂`) is not
pseudo-telepathic, combining `quantumMinion_to_sdpMinion`, `sdpMinion_to_polMinion_twoColoring`,
and `isPseudoTelepathic_iff_exists_not_minionHomExists`. -/
theorem not_isPseudoTelepathic_twoColoring :
    ¬ IsPseudoTelepathic twoColoringLang Bool := by
  rw [isPseudoTelepathic_iff_exists_not_minionHomExists]
  rintro ⟨d, hd, hnot⟩
  have _ : Nontrivial (EuclideanSpace ℂ (Fin d)) := by
    refine ⟨⟨EuclideanSpace.single ⟨0, hd⟩ 1, 0, ?_⟩⟩
    intro h
    have := congr_fun (congr_arg WithLp.ofLp h) ⟨0, hd⟩
    simp at this
  exact hnot (quantumMinion_to_sdpMinion.trans sdpMinion_to_polMinion_twoColoring)

/-- Unmarked separation under standard Lean axioms: for every `n ≥ 2`, there is no minion
homomorphism from `polMinion twoColoringLang Bool` into `polMinion (linLang n) (ZMod n)`,
witnessed by the ternary majority polymorphism of `K₂`. -/
theorem not_minionHomExists_polMinion_twoColoring_lin {n : ℕ} (hn : 2 ≤ n) :
    ¬ MinionHomExists (polMinion twoColoringLang Bool) (polMinion (linLang n) (ZMod n)) := by
  intro hξ
  obtain ⟨ξ⟩ := minionHomExists_iff.mp hξ
  have h3 : (0 : ℕ) < 3 := by decide
  have h1 : (0 : ℕ) < 1 := by decide
  let majFun : (Fin 3 → Bool) → Bool := fun x ↦ (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 0)
  let _ := piStructure twoColoringLang (fun _ : Fin 3 ↦ Bool)
  let maj : (polMinion twoColoringLang Bool).Carrier 3 h3 :=
    homOfRel majFun fun {k} R a ha ↦ by
      cases R
      have ha' : ∀ i : Fin 3, a 0 i ≠ a 1 i := fun i ↦
        (twoColoringLang_relMap_ne_iff _).mp
          ((pi_relMap (L := twoColoringLang) TwoColoringRel.ne a).mp ha i)
      rw [twoColoringLang_relMap_ne_iff]
      have h0 := ha' 0
      have h1' := ha' 1
      have h2 := ha' 2
      change majFun (a 0) ≠ majFun (a 1)
      dsimp only [majFun]
      cases c0 : a 0 0 <;> cases c1 : a 0 1 <;> cases c2 : a 0 2 <;>
        cases d0 : a 1 0 <;> cases d1 : a 1 1 <;> cases d2 : a 1 2 <;> simp_all
  have hmaj_apply : ∀ y : Fin 3 → Bool, maj y = majFun y := fun y ↦ homOfRel_apply _ _ y
  -- For each `π : Fin 3 → Fin 2` with two equal entries, `maj.minor π` is a projection.
  have hmaj_001 :
      (polMinion twoColoringLang Bool).minor h3 (by decide : (0 : ℕ) < 2) ![0, 0, 1] maj =
        homProj twoColoringLang (fun _ : Fin 2 ↦ Bool) 0 := by
    apply Hom.ext
    intro x
    rw [homProj_apply]
    refine (polMinion_minor_apply h3 (by decide : (0 : ℕ) < 2) ![0, 0, 1] maj x).trans ?_
    rw [hmaj_apply]
    dsimp only [majFun]
    cases c0 : x 0 <;> cases c1 : x 1 <;> simp [c0, c1]
  have hmaj_010 :
      (polMinion twoColoringLang Bool).minor h3 (by decide : (0 : ℕ) < 2) ![0, 1, 0] maj =
        homProj twoColoringLang (fun _ : Fin 2 ↦ Bool) 0 := by
    apply Hom.ext
    intro x
    rw [homProj_apply]
    refine (polMinion_minor_apply h3 (by decide : (0 : ℕ) < 2) ![0, 1, 0] maj x).trans ?_
    rw [hmaj_apply]
    dsimp only [majFun]
    cases c0 : x 0 <;> cases c1 : x 1 <;> simp [c0, c1]
  have hmaj_100 :
      (polMinion twoColoringLang Bool).minor h3 (by decide : (0 : ℕ) < 2) ![1, 0, 0] maj =
        homProj twoColoringLang (fun _ : Fin 2 ↦ Bool) 0 := by
    apply Hom.ext
    intro x
    rw [homProj_apply]
    refine (polMinion_minor_apply h3 (by decide : (0 : ℕ) < 2) ![1, 0, 0] maj x).trans ?_
    rw [hmaj_apply]
    dsimp only [majFun]
    cases c0 : x 0 <;> cases c1 : x 1 <;> simp [c0, c1]
  let φ := ξ.toFun h3 maj
  -- Show `φ` is additive and `φ(1, 1, 1) = 1`, while each `φ(e_i) = 0` via the majority identities.
  have hφ_zero : φ 0 = 0 := by
    have := φ.map_rel' LinRel.zero (fun _ _ ↦ 0)
      ((pi_relMap (L := linLang n) LinRel.zero _).mpr fun _ ↦
        (linLang_relMap_zero_iff n _).mpr rfl)
    exact (linLang_relMap_zero_iff n _).mp this
  have hφ_neg : ∀ x : Fin 3 → ZMod n, φ (-x) = -φ x := by
    intro x
    let a : Fin 3 → Fin 3 → ZMod n := fun k j ↦ if k = 0 then x j else if k = 1 then 0 else -x j
    have ha : @RelMap (linLang n) (Fin 3 → ZMod n) (piStructure (linLang n) (fun _ ↦ ZMod n)) 3
        (LinRel.sumEq 0) a :=
      (pi_relMap (L := linLang n) (LinRel.sumEq 0) a).mpr fun j ↦ by
        rw [linLang_relMap_sumEq_iff]
        simp [a]
    have hrel := (linLang_relMap_sumEq_iff n 0 _).mp (φ.map_rel' (LinRel.sumEq 0) a ha)
    have h0 : a 0 = x := funext fun j ↦ by simp [a]
    have h1' : a 1 = 0 := funext fun j ↦ by simp [a]
    have h2 : a 2 = -x := funext fun j ↦ by simp [a]
    change φ (a 0) + φ (a 1) + φ (a 2) = 0 at hrel
    rw [h0, h1', h2, hφ_zero, add_zero] at hrel
    exact eq_neg_of_add_eq_zero_right hrel
  have hφ_add : ∀ x y : Fin 3 → ZMod n, φ (x + y) = φ x + φ y := by
    intro x y
    let a : Fin 3 → Fin 3 → ZMod n :=
      fun k j ↦ if k = 0 then x j else if k = 1 then y j else -(x j + y j)
    have ha : @RelMap (linLang n) (Fin 3 → ZMod n) (piStructure (linLang n) (fun _ ↦ ZMod n)) 3
        (LinRel.sumEq 0) a :=
      (pi_relMap (L := linLang n) (LinRel.sumEq 0) a).mpr fun j ↦ by
        rw [linLang_relMap_sumEq_iff]
        simp [a, add_assoc]
    have hrel := (linLang_relMap_sumEq_iff n 0 _).mp (φ.map_rel' (LinRel.sumEq 0) a ha)
    have h0 : a 0 = x := funext fun j ↦ by simp [a]
    have h1' : a 1 = y := funext fun j ↦ by simp [a]
    have h2 : a 2 = -(x + y) := funext fun j ↦ by simp [a]
    change φ (a 0) + φ (a 1) + φ (a 2) = 0 at hrel
    rw [h0, h1', h2, hφ_neg (x + y)] at hrel
    exact neg_inj.mp (eq_neg_of_add_eq_zero_right hrel)
  have hφ_one : φ (fun _ ↦ 1) = 1 := by
    let a : Fin 3 → Fin 3 → ZMod n := fun k _ ↦ if k = 0 then 1 else 0
    have ha : @RelMap (linLang n) (Fin 3 → ZMod n) (piStructure (linLang n) (fun _ ↦ ZMod n)) 3
        (LinRel.sumEq 1) a :=
      (pi_relMap (L := linLang n) (LinRel.sumEq 1) a).mpr fun _ ↦ by
        rw [linLang_relMap_sumEq_iff]
        simp [a]
    have hrel := (linLang_relMap_sumEq_iff n 1 _).mp (φ.map_rel' (LinRel.sumEq 1) a ha)
    have h0 : a 0 = fun _ ↦ 1 := funext fun _ ↦ by simp [a]
    have h1' : a 1 = 0 := funext fun _ ↦ by simp [a]
    have h2 : a 2 = 0 := funext fun _ ↦ by simp [a]
    change φ (a 0) + φ (a 1) + φ (a 2) = 1 at hrel
    rw [h0, h1', h2, hφ_zero, add_zero, add_zero] at hrel
    exact hrel
  -- Each two-equal-coordinate minor of `maj` is the first projection (a minor of the unary
  -- projection), forcing `φ` to vanish on every standard basis vector of `(ZMod n)^3`.
  have hbasis : ∀ (π : Fin 3 → Fin 2) (v : Fin 3 → ZMod n),
      (polMinion twoColoringLang Bool).minor h3 (by decide : (0 : ℕ) < 2) π maj =
        homProj twoColoringLang (fun _ : Fin 2 ↦ Bool) 0 →
      (fun i ↦ (![0, 1] : Fin 2 → ZMod n) (π i)) = v →
      (fun i ↦ (![0, 0] : Fin 2 → ZMod n) (π i)) = 0 →
      φ v = 0 := by
    intro π v hmaj hv1 hv0
    have hm := ξ.map_minor h3 (by decide : (0 : ℕ) < 2) π maj
    rw [hmaj] at hm
    have hproj_eq :
        homProj twoColoringLang (fun _ : Fin 2 ↦ Bool) 0 =
          (polMinion twoColoringLang Bool).minor h1 (by decide : (0 : ℕ) < 2) ![0]
            (homProj twoColoringLang (fun _ : Fin 1 ↦ Bool) 0) := by
      apply Hom.ext; intro x; simp
    have hm' := ξ.map_minor h1 (by decide : (0 : ℕ) < 2) ![0]
      (homProj twoColoringLang (fun _ : Fin 1 ↦ Bool) 0)
    rw [← hproj_eq] at hm'
    have hEq := hm.symm.trans hm'
    have h01 := congrArg (fun (g : (polMinion (linLang n) (ZMod n)).Carrier 2 (by decide)) ↦
      g ![0, 1]) hEq
    have h00 := congrArg (fun (g : (polMinion (linLang n) (ZMod n)).Carrier 2 (by decide)) ↦
      g ![0, 0]) hEq
    rw [polMinion_minor_apply, polMinion_minor_apply] at h01 h00
    have heq0 : (fun i : Fin 1 ↦ (![0, 1] : Fin 2 → ZMod n) ((![0] : Fin 1 → Fin 2) i)) =
        (fun i : Fin 1 ↦ (![0, 0] : Fin 2 → ZMod n) ((![0] : Fin 1 → Fin 2) i)) := by
      ext i; fin_cases i; rfl
    rw [heq0] at h01
    have hcombine := h01.trans h00.symm
    change φ (fun i ↦ (![0, 1] : Fin 2 → ZMod n) (π i)) =
        φ (fun i ↦ (![0, 0] : Fin 2 → ZMod n) (π i)) at hcombine
    rw [hv1, hv0, hφ_zero] at hcombine
    exact hcombine
  have he2 : φ ![0, 0, 1] = 0 :=
    hbasis ![0, 0, 1] ![0, 0, 1] hmaj_001
      (by ext i; fin_cases i <;> rfl) (by ext i; fin_cases i <;> rfl)
  have he1 : φ ![0, 1, 0] = 0 :=
    hbasis ![0, 1, 0] ![0, 1, 0] hmaj_010
      (by ext i; fin_cases i <;> rfl) (by ext i; fin_cases i <;> rfl)
  have he0 : φ ![1, 0, 0] = 0 :=
    hbasis ![1, 0, 0] ![1, 0, 0] hmaj_100
      (by ext i; fin_cases i <;> rfl) (by ext i; fin_cases i <;> rfl)
  have hsum_one : (![1, 0, 0] : Fin 3 → ZMod n) + ![0, 1, 0] + ![0, 0, 1] = fun _ ↦ 1 := by
    ext i
    fin_cases i <;> simp
  have hzero_eq_one : (0 : ZMod n) = 1 := by
    calc (0 : ZMod n) = φ ![1, 0, 0] + φ ![0, 1, 0] + φ ![0, 0, 1] := by rw [he0, he1, he2]; simp
      _ = φ ((![1, 0, 0] : Fin 3 → ZMod n) + ![0, 1, 0] + ![0, 0, 1]) := by
            rw [← hφ_add, ← hφ_add]
      _ = φ (fun _ ↦ 1) := by rw [hsum_one]
      _ = 1 := hφ_one
  have _ : Fact (1 < n) := ⟨Nat.lt_of_lt_of_le (by decide) hn⟩
  exact zero_ne_one hzero_eq_one

end CslibFrontier.Computability.Complexity
