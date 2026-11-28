/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Discrepancy
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiparty Cylinder Intersection Norms and NOF Communication Bounds

This module defines the cylinder intersection norm `mu`, the `±1` cylinder-product norm `muPM`,
and the approximate cylinder intersection norms `muAlpha` (`μ^α`) and `muInfty` (`μ^∞`) for
multiparty tensors in the number-on-the-forehead (NOF) communication model, and establishes
fundamental connections to deterministic, public-coin randomized, and nondeterministic NOF
communication complexity.

## Main definitions

* `Tensor`, `IsSignTensor`, `signTensor`, `CylInter`, `charTensor`: multiparty real/sign tensors
  and cylinder intersection indicator tensors.
* `mu`, `muPM`: exact cylinder intersection norm and `±1` cylinder-product norm.
* `muAlpha`, `muInfty`: approximate cylinder intersection norms for `α ≥ 1` and `α = ∞`.
* `NondetCover`: nondeterministic cylinder-intersection covers for sign tensors.

## Main results

* `det_partition_cylinderInter`, `logb_mu_le_det_ecomplexity`: deterministic NOF protocols partition
  the domain into `2^c` monochromatic cylinder intersections, giving `log₂ μ(f) ≤ c`.
* `muPM_bounds`: `2^{-k} μ(B) ≤ μ_{±1}(B) ≤ μ(B)` for `k`-party tensors.
* `publicCoin_decomposition_iff`, `logb_muAlpha_le_publicCoin_ecomplexity`: randomized NOF protocol
  decompositions and `log₂ μ^α(f) - log₂ α ≤ R^k_ε(f)`.
* `logb_muInfty_le_nondetCover`: `log₂(μ^∞(A) - 1) ≤ log₂ |C|` for nondeterministic covers `C`.
-/

public section

open scoped BigOperators ENNReal
open Cslib.BitString Cslib.Communication.NOF Cslib.Probability

namespace CslibFrontier.Computability.Communication.NOF

section Tensors

variable {ι : Type*} {X : ι → Type*}

/-- Real-valued multiparty tensor indexed by `∀ i, X i`. -/
abbrev Tensor (X : ι → Type*) : Type _ :=
  (∀ i, X i) → ℝ

/-- Total entry count `size(A) = ∏ i, |X i|` of a tensor. -/
@[expose] def tensorSize (X : ι → Type*) [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] : ℕ :=
  Fintype.card (∀ i, X i)

/-- The entry count of a tensor equals the cardinality of the product domain. -/
theorem tensorSize_eq_card [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] :
    tensorSize X = Fintype.card (∀ i, X i) := rfl

/-- The entry count of a tensor is the product of its side lengths. -/
theorem tensorSize_eq_prod [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] :
    tensorSize X = ∏ i : ι, Fintype.card (X i) := by
  simp [tensorSize]

/-- A tensor on nonempty finite domains has positive size. -/
theorem tensorSize_pos [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] :
    0 < tensorSize X :=
  Fintype.card_pos

/-- A sign tensor takes values in `{-1, +1}`. -/
@[expose] def IsSignTensor (A : Tensor X) : Prop :=
  ∀ x, A x = 1 ∨ A x = -1

/-- The `{-1, +1}` sign tensor associated to a Boolean function (`false ↦ 1`, `true ↦ -1`). -/
@[expose] def signTensor (f : (∀ i, X i) → Bool) : Tensor X :=
  fun x ↦ signVal (f x)

/-- Pointwise evaluation of a sign tensor. -/
theorem signTensor_apply (f : (∀ i, X i) → Bool) (x : ∀ i, X i) :
    signTensor f x = signVal (f x) := rfl

/-- Every Boolean function induces a sign tensor. -/
theorem isSignTensor_signTensor (f : (∀ i, X i) → Bool) : IsSignTensor (signTensor f) := by
  intro x
  cases h : f x
  · left; simp [signTensor, h]
  · right; simp [signTensor, h]

/-- Entries of a sign tensor square to `1`. -/
theorem IsSignTensor.sq_eq_one {A : Tensor X} (hA : IsSignTensor A) (x : ∀ i, X i) :
    A x ^ 2 = 1 := by
  rcases hA x with h | h <;> rw [h] <;> norm_num

/-- Entries of a sign tensor satisfy `A x * A x = 1`. -/
theorem IsSignTensor.mul_self {A : Tensor X} (hA : IsSignTensor A) (x : ∀ i, X i) :
    A x * A x = 1 := by
  rw [← sq]
  exact hA.sq_eq_one x

/-- Entries of a sign tensor have absolute value `1`. -/
theorem IsSignTensor.abs_eq_one {A : Tensor X} (hA : IsSignTensor A) (x : ∀ i, X i) :
    |A x| = 1 := by
  rcases hA x with h | h <;> rw [h] <;> norm_num

/-- Entrywise inner product `⟨A, B⟩ = ∑ x, A x * B x`. -/
@[expose] def tensorInner [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] (A B : Tensor X) : ℝ :=
  ∑ x : ∀ i, X i, A x * B x

/-- Sum expansion of the tensor inner product. -/
theorem tensorInner_eq_sum [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] (A B : Tensor X) :
    tensorInner A B = ∑ x : ∀ i, X i, A x * B x := rfl

/-- Entrywise Hadamard product `(A ∘ B)[x] = A x * B x`. -/
@[expose] def hadamardTensor (A B : Tensor X) : Tensor X :=
  fun x ↦ A x * B x

/-- Pointwise evaluation of the Hadamard product. -/
theorem hadamardTensor_apply (A B : Tensor X) (x : ∀ i, X i) :
    hadamardTensor A B x = A x * B x := rfl

/-- Entrywise `ℓ₁` norm `‖A‖₁ = ∑ x, |A x|`. -/
@[expose] def tensorL1 [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] (A : Tensor X) : ℝ :=
  ∑ x : ∀ i, X i, |A x|

/-- Sum expansion of the tensor `ℓ₁` norm. -/
theorem tensorL1_eq_sum [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] (A : Tensor X) :
    tensorL1 A = ∑ x : ∀ i, X i, |A x| := rfl

/-- Entrywise `ℓ_∞` norm `‖A‖_∞ = sup_x |A x|`. -/
noncomputable def tensorLInfty (A : Tensor X) : ℝ :=
  ⨆ x : ∀ i, X i, |A x|

/-- Characteristic `{0, 1}` tensor `χ(Z)` of a subset `Z`. -/
noncomputable def charTensor (Z : Set (∀ i, X i)) : Tensor X := by
  classical
  exact fun x ↦ if x ∈ Z then 1 else 0

/-- Characteristic tensor evaluates to `1` on members of `Z`. -/
theorem charTensor_of_mem {Z : Set (∀ i, X i)} {x : ∀ i, X i} (hx : x ∈ Z) :
    charTensor Z x = 1 := by
  classical
  simp [charTensor, hx]

/-- Characteristic tensor evaluates to `0` outside `Z`. -/
theorem charTensor_of_notMem {Z : Set (∀ i, X i)} {x : ∀ i, X i} (hx : x ∉ Z) :
    charTensor Z x = 0 := by
  classical
  simp [charTensor, hx]

/-- Characteristic tensor is always nonnegative. -/
theorem charTensor_nonneg (Z : Set (∀ i, X i)) (x : ∀ i, X i) : 0 ≤ charTensor Z x := by
  by_cases hx : x ∈ Z
  · rw [charTensor_of_mem hx]; norm_num
  · rw [charTensor_of_notMem hx]

@[simp]
theorem charTensor_univ (x : ∀ i, X i) : charTensor (Set.univ : Set (∀ i, X i)) x = 1 :=
  charTensor_of_mem (Set.mem_univ x)

@[simp]
theorem charTensor_empty (x : ∀ i, X i) : charTensor (∅ : Set (∀ i, X i)) x = 0 :=
  charTensor_of_notMem (Set.notMem_empty x)

/-- Characteristic tensor of an intersection is the pointwise product. -/
theorem charTensor_inter (Z₁ Z₂ : Set (∀ i, X i)) (x : ∀ i, X i) :
    charTensor (Z₁ ∩ Z₂) x = charTensor Z₁ x * charTensor Z₂ x := by
  by_cases h₁ : x ∈ Z₁ <;> by_cases h₂ : x ∈ Z₂
  · rw [charTensor_of_mem (Set.mem_inter h₁ h₂), charTensor_of_mem h₁, charTensor_of_mem h₂,
      mul_one]
  · rw [charTensor_of_notMem (fun h : x ∈ Z₁ ∩ Z₂ ↦ h₂ h.2), charTensor_of_mem h₁,
      charTensor_of_notMem h₂, mul_zero]
  · rw [charTensor_of_notMem (fun h : x ∈ Z₁ ∩ Z₂ ↦ h₁ h.1), charTensor_of_notMem h₁,
      charTensor_of_mem h₂, zero_mul]
  · rw [charTensor_of_notMem (fun h : x ∈ Z₁ ∩ Z₂ ↦ h₁ h.1), charTensor_of_notMem h₁,
      charTensor_of_notMem h₂, zero_mul]

/-- The tensor inner product is symmetric. -/
theorem tensorInner_comm [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] (A B : Tensor X) :
    tensorInner A B = tensorInner B A :=
  Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The `ℓ₁` norm of a tensor is nonnegative. -/
theorem tensorL1_nonneg [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] (A : Tensor X) :
    0 ≤ tensorL1 A :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Entrywise bound from the `ℓ_∞` norm on finite domains. -/
theorem abs_le_tensorLInfty [Finite ι] [∀ i, Finite (X i)] (A : Tensor X) (x : ∀ i, X i) :
    |A x| ≤ tensorLInfty A := by
  unfold tensorLInfty
  exact le_ciSup (Set.finite_range (fun y : ∀ i, X i ↦ |A y|)).bddAbove x

/-- Upper bound criterion for `tensorLInfty`. -/
theorem tensorLInfty_le_iff [Finite ι] [∀ i, Finite (X i)] (A : Tensor X) {c : ℝ} (hc : 0 ≤ c) :
    tensorLInfty A ≤ c ↔ ∀ x, |A x| ≤ c := by
  constructor
  · intro h x
    exact (abs_le_tensorLInfty A x).trans h
  · intro h
    unfold tensorLInfty
    rcases isEmpty_or_nonempty (∀ i, X i) with hempty | hne
    · rw [Real.iSup_of_isEmpty]; exact hc
    · exact ciSup_le h

/-- When `A` is a sign tensor and `A ∘ Q ≥ 0`, `⟨A, Q⟩ = ‖Q‖₁`. -/
theorem signTensor_inner_eq_l1_of_nonneg [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    {A Q : Tensor X} (hA : IsSignTensor A) (hAQ : ∀ x, 0 ≤ A x * Q x) :
    tensorInner A Q = tensorL1 Q := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have habs : |A x * Q x| = |Q x| := by rw [abs_mul, hA.abs_eq_one x, one_mul]
  rw [← habs, abs_of_nonneg (hAQ x)]

end Tensors

section CylinderIntersections

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

/-- Subtype of cylinder intersections on `∀ i, X i`. -/
abbrev CylInter (X : ι → Type*) : Type _ :=
  {Z : Set (∀ i, X i) // IsCylinderIntersection Z}

/-- The whole input space `Set.univ` is a cylinder intersection. -/
theorem isCylinderIntersection_univ :
    IsCylinderIntersection (Set.univ : Set (∀ i, X i)) :=
  isCylinderIntersection_iff.mpr ⟨fun _ _ ↦ true, cylinderIntersection_true.symm⟩

/-- On at least one player, the empty set is a cylinder intersection. -/
theorem isCylinderIntersection_empty [Nonempty ι] :
    IsCylinderIntersection (∅ : Set (∀ i, X i)) := by
  refine isCylinderIntersection_iff.mpr ⟨fun _ _ ↦ false, Set.ext fun x ↦ ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  simp only [Set.mem_empty_iff_false, mem_cylinderIntersection, Bool.false_eq_true, false_iff,
    not_forall]
  exact ⟨i₀, id⟩

/-- On at least two players, every singleton `{a}` is a cylinder intersection. -/
theorem isCylinderIntersection_singleton [Nontrivial ι] (a : ∀ i, X i) :
    IsCylinderIntersection ({a} : Set (∀ i, X i)) := by
  refine ⟨fun i ↦ {x | ∀ j, j ≠ i → x j = a j}, ?_, Set.ext fun x ↦ ?_⟩
  · intro i x y
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h j hj
    · simpa [Function.update_of_ne hj] using h j hj
    · rw [Function.update_of_ne hj]; exact h j hj
  · simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro rfl i j _; rfl
    · intro h
      funext j
      obtain ⟨i, hij⟩ := exists_ne j
      exact h i j hij.symm

/-- Cylinder intersections are closed under finite intersection. -/
theorem isCylinderIntersection_inter {Z₁ Z₂ : Set (∀ i, X i)}
    (h₁ : IsCylinderIntersection Z₁) (h₂ : IsCylinderIntersection Z₂) :
    IsCylinderIntersection (Z₁ ∩ Z₂) := by
  rcases isCylinderIntersection_iff.mp h₁ with ⟨φ₁, rfl⟩
  rcases isCylinderIntersection_iff.mp h₂ with ⟨φ₂, rfl⟩
  refine isCylinderIntersection_iff.mpr ⟨fun i v ↦ φ₁ i v && φ₂ i v, Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_inter_iff, mem_cylinderIntersection, Bool.and_eq_true, forall_and]

end CylinderIntersections

section CylinderNorm

variable {ι : Type*} {X : ι → Type*}

/-- **Cylinder intersection norm `μ(B)`**):
minimum `∑ |α_r|` over finite linear combinations `B = ∑ α_r χ(Z_r)` of cylinder intersection
characteristic tensors. -/
noncomputable def mu [DecidableEq ι] (B : Tensor X) : ℝ :=
  sInf {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
    (∀ r, IsCylinderIntersection (Z r)) ∧
    (∀ x, B x = ∑ r, α r * charTensor (Z r) x) ∧
    w = ∑ r, |α r|}

/-- A `±1`-valued cylinder product `∏_i f_i(view_i x)`. -/
def IsSignCylProd [Fintype ι] (F : Tensor X) : Prop :=
  ∃ f : ∀ i, View X i → Bool, ∀ x, F x = ∏ i : ι, signVal (f i (view i x))

/-- **`±1`-valued cylinder intersection norm `μ_{±1}(B)`**. -/
noncomputable def muPM [Fintype ι] (B : Tensor X) : ℝ :=
  sInf {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (F : Fin n → Tensor X),
    (∀ r, IsSignCylProd (F r)) ∧
    (∀ x, B x = ∑ r, α r * F r x) ∧
    w = ∑ r, |α r|}

private theorem bddBelow_mu_set [DecidableEq ι] (B : Tensor X) :
    BddBelow {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
      (∀ r, IsCylinderIntersection (Z r)) ∧
      (∀ x, B x = ∑ r, α r * charTensor (Z r) x) ∧
      w = ∑ r, |α r|} := by
  refine ⟨0, ?_⟩
  rintro w ⟨n, α, Z, _, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

private theorem bddBelow_muPM_set [Fintype ι] (B : Tensor X) :
    BddBelow {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (F : Fin n → Tensor X),
      (∀ r, IsSignCylProd (F r)) ∧
      (∀ x, B x = ∑ r, α r * F r x) ∧
      w = ∑ r, |α r|} := by
  refine ⟨0, ?_⟩
  rintro w ⟨n, α, F, _, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Any finite cylinder-intersection decomposition bounds `μ(B)` from above. -/
theorem mu_le_of_decomp [DecidableEq ι] {B : Tensor X} {n : ℕ} (α : Fin n → ℝ)
    (Z : Fin n → Set (∀ i, X i)) (hZ : ∀ r, IsCylinderIntersection (Z r))
    (hB : ∀ x, B x = ∑ r, α r * charTensor (Z r) x) :
    mu B ≤ ∑ r, |α r| :=
  csInf_le (bddBelow_mu_set B) ⟨n, α, Z, hZ, hB, rfl⟩

/-- Any finite `±1`-cylinder-product decomposition bounds `μ_{±1}(B)` from above. -/
theorem muPM_le_of_decomp [Fintype ι] {B : Tensor X} {n : ℕ} (α : Fin n → ℝ)
    (F : Fin n → Tensor X) (hF : ∀ r, IsSignCylProd (F r))
    (hB : ∀ x, B x = ∑ r, α r * F r x) :
    muPM B ≤ ∑ r, |α r| :=
  csInf_le (bddBelow_muPM_set B) ⟨n, α, F, hF, hB, rfl⟩

/-- The cylinder intersection norm is nonnegative. -/
theorem mu_nonneg [DecidableEq ι] (B : Tensor X) : 0 ≤ mu B := by
  unfold mu
  exact Real.sInf_nonneg fun _ ⟨_, _, _, _, _, hw⟩ ↦ hw ▸ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The `±1` cylinder intersection norm is nonnegative. -/
theorem muPM_nonneg [Fintype ι] (B : Tensor X) : 0 ≤ muPM B := by
  unfold muPM
  exact Real.sInf_nonneg fun _ ⟨_, _, _, _, _, hw⟩ ↦ hw ▸ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- On at least two players and finite domains, every tensor admits a finite cylinder-intersection
decomposition of weight `‖B‖₁`. -/
theorem exists_decomp_of_nontrivial [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    [Nontrivial ι] (B : Tensor X) :
    ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
      (∀ r, IsCylinderIntersection (Z r)) ∧
      (∀ x, B x = ∑ r, α r * charTensor (Z r) x) ∧
      ∑ r, |α r| = tensorL1 B := by
  let e : Fin (tensorSize X) ≃ (∀ i, X i) := (Fintype.equivFin (∀ i, X i)).symm
  refine ⟨tensorSize X, fun r ↦ B (e r), fun r ↦ {e r},
    fun r ↦ isCylinderIntersection_singleton (e r), fun x ↦ ?_, ?_⟩
  · rw [Finset.sum_eq_single (e.symm x)]
    · dsimp only
      rw [e.apply_symm_apply x, charTensor_of_mem (Set.mem_singleton x), mul_one]
    · intro r _ hr
      have hne : x ≠ e r := fun h ↦ hr ((e.symm_apply_eq.mpr h).symm)
      rw [charTensor_of_notMem (Set.notMem_singleton_iff.mpr hne), mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · unfold tensorL1
    exact e.sum_comp (fun x ↦ |B x|)

/-- `μ(B) ≤ ‖B‖₁` on at least two players. -/
theorem mu_le_tensorL1 [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [Nontrivial ι]
    (B : Tensor X) : mu B ≤ tensorL1 B := by
  obtain ⟨n, α, Z, hZ, hB, hw⟩ := exists_decomp_of_nontrivial B
  exact hw ▸ mu_le_of_decomp α Z hZ hB

/-- Lower bound criterion for `μ(B)`: if `B` admits some decomposition and every decomposition has
weight at least `c`, then `c ≤ μ(B)`. -/
theorem le_mu_of_forall_decomp [Finite ι] [DecidableEq ι] [∀ i, Finite (X i)] [Nontrivial ι]
    {B : Tensor X} {c : ℝ}
    (h : ∀ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
      (∀ r, IsCylinderIntersection (Z r)) →
      (∀ x, B x = ∑ r, α r * charTensor (Z r) x) → c ≤ ∑ r, |α r|) :
    c ≤ mu B := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun i ↦ Fintype.ofFinite (X i)
  obtain ⟨n₀, α₀, Z₀, hZ₀, hB₀, _⟩ := exists_decomp_of_nontrivial B
  refine le_csInf ⟨_, n₀, α₀, Z₀, hZ₀, hB₀, rfl⟩ ?_
  rintro w ⟨n, α, Z, hZ, hB, rfl⟩
  exact h n α Z hZ hB

/-- `μ` is subadditive (triangle inequality). -/
theorem mu_add_le [Finite ι] [DecidableEq ι] [∀ i, Finite (X i)] [Nontrivial ι]
    (A B : Tensor X) : mu (fun x ↦ A x + B x) ≤ mu A + mu B := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun i ↦ Fintype.ofFinite (X i)
  have hneA : {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
      (∀ r, IsCylinderIntersection (Z r)) ∧
      (∀ x, A x = ∑ r, α r * charTensor (Z r) x) ∧ w = ∑ r, |α r|}.Nonempty := by
    obtain ⟨n, α, Z, hZ, hA, _⟩ := exists_decomp_of_nontrivial A
    exact ⟨_, n, α, Z, hZ, hA, rfl⟩
  have hneB : {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
      (∀ r, IsCylinderIntersection (Z r)) ∧
      (∀ x, B x = ∑ r, α r * charTensor (Z r) x) ∧ w = ∑ r, |α r|}.Nonempty := by
    obtain ⟨n, α, Z, hZ, hB, _⟩ := exists_decomp_of_nontrivial B
    exact ⟨_, n, α, Z, hZ, hB, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨_, ⟨nA, αA, ZA, hZA, hA, rfl⟩, hwA⟩ := Real.lt_sInf_add_pos hneA (half_pos hε)
  obtain ⟨_, ⟨nB, αB, ZB, hZB, hB, rfl⟩, hwB⟩ := Real.lt_sInf_add_pos hneB (half_pos hε)
  have hcomb : mu (fun x ↦ A x + B x) ≤ ∑ r, |αA r| + ∑ r, |αB r| := by
    let α : Fin (nA + nB) → ℝ := Fin.append αA αB
    let Z : Fin (nA + nB) → Set (∀ i, X i) := Fin.append ZA ZB
    have hZ : ∀ r, IsCylinderIntersection (Z r) := by
      intro r
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
      · simpa [Z] using hZA i
      · simpa [Z] using hZB j
    have hsum : ∀ x, A x + B x = ∑ r : Fin (nA + nB), α r * charTensor (Z r) x := by
      intro x
      rw [Fin.sum_univ_add, hA x, hB x]
      congr 1 <;> refine Finset.sum_congr rfl fun r _ ↦ by simp [α, Z]
    have hwt : ∑ r : Fin (nA + nB), |α r| = ∑ r, |αA r| + ∑ r, |αB r| := by
      rw [Fin.sum_univ_add]
      congr 1 <;> refine Finset.sum_congr rfl fun r _ ↦ by simp [α]
    exact hwt ▸ mu_le_of_decomp α Z hZ hsum
  have hwA' : ∑ r, |αA r| < mu A + ε / 2 := hwA
  have hwB' : ∑ r, |αB r| < mu B + ε / 2 := hwB
  linarith

/-- `μ` is positively homogeneous: `μ(c · B) = |c| · μ(B)`. -/
theorem mu_smul [Finite ι] [DecidableEq ι] [∀ i, Finite (X i)] [Nontrivial ι]
    (c : ℝ) (B : Tensor X) : mu (fun x ↦ c * B x) = |c| * mu B := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun i ↦ Fintype.ofFinite (X i)
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, abs_zero]
    refine le_antisymm ?_ (mu_nonneg _)
    simpa using mu_le_of_decomp (B := fun _ : ∀ i, X i ↦ (0 : ℝ))
      (n := 0) Fin.elim0 Fin.elim0 (fun r ↦ r.elim0) (fun _ ↦ by simp)
  · have hpos : 0 < |c| := abs_pos.mpr hc
    have hle : ∀ (a : ℝ) (T : Tensor X), mu (fun x ↦ a * T x) ≤ |a| * mu T := by
      intro a T
      have hneT : {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
          (∀ r, IsCylinderIntersection (Z r)) ∧
          (∀ x, T x = ∑ r, α r * charTensor (Z r) x) ∧ w = ∑ r, |α r|}.Nonempty := by
        obtain ⟨n, α, Z, hZ, hT, _⟩ := exists_decomp_of_nontrivial T
        exact ⟨_, n, α, Z, hZ, hT, rfl⟩
      by_cases ha : a = 0
      · subst ha
        simp only [zero_mul, abs_zero]
        simpa using mu_le_of_decomp (B := fun _ : ∀ i, X i ↦ (0 : ℝ))
          (n := 0) Fin.elim0 Fin.elim0 (fun r ↦ r.elim0) (fun _ ↦ by simp)
      · have hapos : 0 < |a| := abs_pos.mpr ha
        refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        obtain ⟨_, ⟨n, α, Z, hZ, hT, rfl⟩, hw⟩ :=
          Real.lt_sInf_add_pos hneT (div_pos hε hapos)
        have hw' : ∑ r, |α r| < mu T + ε / |a| := hw
        have hstep : mu (fun x ↦ a * T x) ≤ |a| * ∑ r, |α r| := by
          have hwt : ∑ r, |a * α r| = |a| * ∑ r, |α r| := by
            simp_rw [abs_mul, ← Finset.mul_sum]
          refine hwt ▸ mu_le_of_decomp (fun r ↦ a * α r) Z hZ fun x ↦ ?_
          rw [hT x, Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ ↦ by ring
        have hmul : |a| * ∑ r, |α r| < |a| * (mu T + ε / |a|) :=
          mul_lt_mul_of_pos_left hw' hapos
        have hrhs : |a| * (mu T + ε / |a|) = |a| * mu T + ε := by
          field_simp [hapos.ne']
        linarith
    refine le_antisymm (hle c B) ?_
    have hback := hle c⁻¹ (fun x ↦ c * B x)
    have hsimp : (fun x ↦ c⁻¹ * (c * B x)) = B := by
      funext x; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [hsimp, abs_inv] at hback
    have := mul_le_mul_of_nonneg_left hback hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this

/-- `μ` of a finite sum is at most the sum of `μ` norms. -/
theorem mu_finset_sum_le [Finite ι] [DecidableEq ι] [∀ i, Finite (X i)] [Nontrivial ι]
    {κ : Type*} (s : Finset κ) (T : κ → Tensor X) :
    mu (fun x ↦ ∑ j ∈ s, T j x) ≤ ∑ j ∈ s, mu (T j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using mu_le_of_decomp (B := fun _ : ∀ i, X i ↦ (0 : ℝ))
      (n := 0) Fin.elim0 Fin.elim0 (fun r ↦ r.elim0) (fun _ ↦ by simp)
  | insert a t hat ih =>
    simp only [Finset.sum_insert hat]
    have htri := mu_add_le (T a) (fun x ↦ ∑ j ∈ t, T j x)
    linarith

/-- Every cylinder intersection indicator expands as a uniform average of `2^k` `±1`-cylinder
products. -/
theorem charTensor_eq_avg_signCylProd [Fintype ι] [DecidableEq ι] {Z : Set (∀ i, X i)}
    (hZ : IsCylinderIntersection Z) :
    ∃ (F : Finset ι → Tensor X), (∀ S, IsSignCylProd (F S)) ∧
      ∀ x, charTensor Z x = ∑ S : Finset ι, ((2 : ℝ) ^ Fintype.card ι)⁻¹ * F S x := by
  rcases isCylinderIntersection_iff.mp hZ with ⟨φ, rfl⟩
  refine ⟨fun S x ↦ ∏ i ∈ S, signVal (!φ i (view i x)), fun S ↦ ?_, fun x ↦ ?_⟩
  · refine ⟨fun i v ↦ if i ∈ S then !φ i v else false, fun x ↦ ?_⟩
    dsimp only
    have hfilt : Finset.univ.filter (fun i : ι ↦ i ∈ S) = S := by ext i; simp
    simp only [apply_ite signVal, signVal_false, ← Finset.prod_filter, hfilt]
  · have hfactor : ∀ i : ι,
        (if φ i (view i x) = true then (1 : ℝ) else 0) =
          (1 + signVal (!φ i (view i x))) / 2 := by
      intro i
      cases φ i (view i x) <;> norm_num
    have hprod : charTensor (cylinderIntersection φ) x =
        ∏ i : ι, (if φ i (view i x) = true then (1 : ℝ) else 0) := by
      by_cases hx : x ∈ cylinderIntersection φ
      · rw [charTensor_of_mem hx]
        symm
        exact Finset.prod_eq_one fun i _ ↦ ite_eq_left (mem_cylinderIntersection.mp hx i)
      · rw [charTensor_of_notMem hx]
        symm
        obtain ⟨i, hi⟩ := not_forall.mp (mem_cylinderIntersection.not.mp hx)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    rw [hprod]
    simp_rw [hfactor, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Finset.prod_one_add, Finset.sum_mul, inv_pow]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- Every `±1`-cylinder product expands as a signed sum of `2^k` `{0,1}`-cylinder intersections. -/
theorem signCylProd_eq_sum_charTensor [Fintype ι] [DecidableEq ι] {F : Tensor X}
    (hF : IsSignCylProd F) :
    ∃ (Z : (ι → Bool) → Set (∀ i, X i)) (s : (ι → Bool) → ℝ),
      (∀ b, IsCylinderIntersection (Z b)) ∧
      (∀ b, |s b| = 1) ∧
      ∀ x, F x = ∑ b : ι → Bool, s b * charTensor (Z b) x := by
  rcases hF with ⟨f, hf⟩
  refine ⟨fun b ↦ cylinderIntersection (fun i v ↦ f i v == b i),
    fun b ↦ ∏ i : ι, signVal (b i),
    fun b ↦ isCylinderIntersection_iff.mpr ⟨_, rfl⟩,
    fun b ↦ by rw [Finset.abs_prod]; exact Finset.prod_eq_one fun i _ ↦ abs_signVal (b i),
    fun x ↦ ?_⟩
  rw [hf x]
  let b₀ : ι → Bool := fun i ↦ f i (view i x)
  rw [Finset.sum_eq_single b₀]
  · have hmem : x ∈ cylinderIntersection (fun i v ↦ f i v == b₀ i) := by
      intro i; simp [b₀]
    rw [charTensor_of_mem hmem, mul_one]
  · intro b _ hb
    have hnot : x ∉ cylinderIntersection (fun i v ↦ f i v == b i) := by
      intro hm
      apply hb
      funext i
      have hi := mem_cylinderIntersection.mp hm i
      exact (beq_iff_eq.mp hi).symm
    rw [charTensor_of_notMem hnot, mul_zero]
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- **Norm Equivalence**:
`2^{-k} μ(B) ≤ μ_{±1}(B) ≤ μ(B)` for every tensor `B` on at least two players. -/
theorem muPM_bounds [Fintype ι] [DecidableEq ι] [∀ i, Finite (X i)] [Nontrivial ι]
    (B : Tensor X) :
    ((2 : ℝ) ^ Fintype.card ι)⁻¹ * mu B ≤ muPM B ∧ muPM B ≤ mu B := by
  let _ : ∀ i, Fintype (X i) := fun i ↦ Fintype.ofFinite (X i)
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
  have hne_mu : {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (Z : Fin n → Set (∀ i, X i)),
      (∀ r, IsCylinderIntersection (Z r)) ∧
      (∀ x, B x = ∑ r, α r * charTensor (Z r) x) ∧ w = ∑ r, |α r|}.Nonempty := by
    obtain ⟨n, α, Z, hZ, hB, _⟩ := exists_decomp_of_nontrivial B
    exact ⟨_, n, α, Z, hZ, hB, rfl⟩
  have hupper : muPM B ≤ mu B := by
    refine le_csInf hne_mu ?_
    rintro w ⟨n, α, Z, hZ, hB, rfl⟩
    choose F hF hZeq using fun r ↦ charTensor_eq_avg_signCylProd (hZ r)
    let e : Fin (n * 2 ^ Fintype.card ι) ≃ Fin n × Finset ι :=
      (Fintype.equivOfCardEq (by simp)).symm
    let α' : Fin (n * 2 ^ Fintype.card ι) → ℝ :=
      fun idx ↦ α (e idx).1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹
    let F' : Fin (n * 2 ^ Fintype.card ι) → Tensor X := fun idx ↦ F (e idx).1 (e idx).2
    have hB_eq : ∀ x, B x = ∑ idx : Fin (n * 2 ^ Fintype.card ι), α' idx * F' idx x := by
      intro x
      rw [hB x]
      calc ∑ r : Fin n, α r * charTensor (Z r) x
          = ∑ r : Fin n, ∑ S : Finset ι,
              (α r * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F r S x := by
            refine Finset.sum_congr rfl fun r _ ↦ ?_
            rw [hZeq r x, Finset.mul_sum]
            exact Finset.sum_congr rfl fun S _ ↦ by ring
        _ = ∑ p : Fin n × Finset ι, (α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F p.1 p.2 x :=
            (Fintype.sum_prod_type (fun p : Fin n × Finset ι ↦
              (α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F p.1 p.2 x)).symm
        _ = ∑ idx : Fin (n * 2 ^ Fintype.card ι), α' idx * F' idx x :=
            (e.sum_comp (fun p : Fin n × Finset ι ↦
              (α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F p.1 p.2 x)).symm
    have hle := muPM_le_of_decomp (B := B) α' F' (fun idx ↦ hF (e idx).1 (e idx).2) hB_eq
    refine hle.trans (le_of_eq ?_)
    calc ∑ idx : Fin (n * 2 ^ Fintype.card ι), |α' idx|
        = ∑ p : Fin n × Finset ι, |α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹| :=
          e.sum_comp (fun p : Fin n × Finset ι ↦ |α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹|)
      _ = ∑ r : Fin n, ∑ _S : Finset ι, |α r| * ((2 : ℝ) ^ Fintype.card ι)⁻¹ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
          rw [abs_mul, abs_of_pos (inv_pos.mpr h2k_pos)]
      _ = ∑ r : Fin n, |α r| := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
          push_cast
          field_simp [h2k_pos.ne']
  have hne_pm : {w : ℝ | ∃ (n : ℕ) (α : Fin n → ℝ) (F : Fin n → Tensor X),
      (∀ r, IsSignCylProd (F r)) ∧ (∀ x, B x = ∑ r, α r * F r x) ∧ w = ∑ r, |α r|}.Nonempty := by
    obtain ⟨n, α, Z, hZ, hB, _⟩ := exists_decomp_of_nontrivial B
    choose F hF hZeq using fun r ↦ charTensor_eq_avg_signCylProd (hZ r)
    let e : Fin (n * 2 ^ Fintype.card ι) ≃ Fin n × Finset ι :=
      (Fintype.equivOfCardEq (by simp)).symm
    refine ⟨_, n * 2 ^ Fintype.card ι,
      fun idx ↦ α (e idx).1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹,
      fun idx ↦ F (e idx).1 (e idx).2,
      fun idx ↦ hF (e idx).1 (e idx).2, fun x ↦ ?_, rfl⟩
    rw [hB x]
    calc ∑ r : Fin n, α r * charTensor (Z r) x
        = ∑ r : Fin n, ∑ S : Finset ι,
            (α r * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F r S x := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [hZeq r x, Finset.mul_sum]
          exact Finset.sum_congr rfl fun S _ ↦ by ring
      _ = ∑ p : Fin n × Finset ι, (α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F p.1 p.2 x :=
          (Fintype.sum_prod_type (fun p : Fin n × Finset ι ↦
            (α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F p.1 p.2 x)).symm
      _ = _ := (e.sum_comp (fun p : Fin n × Finset ι ↦
            (α p.1 * ((2 : ℝ) ^ Fintype.card ι)⁻¹) * F p.1 p.2 x)).symm
  have hlower : ((2 : ℝ) ^ Fintype.card ι)⁻¹ * mu B ≤ muPM B := by
    refine le_csInf hne_pm ?_
    rintro w ⟨n, α, F, hF, hB, rfl⟩
    choose Z s hZ hs hFeq using fun r ↦ signCylProd_eq_sum_charTensor (hF r)
    let e : Fin (n * 2 ^ Fintype.card ι) ≃ Fin n × (ι → Bool) :=
      (Fintype.equivOfCardEq (by simp)).symm
    have hmu : mu B ≤ (2 : ℝ) ^ Fintype.card ι * ∑ r, |α r| := by
      have hB_eq : ∀ x, B x = ∑ idx : Fin (n * 2 ^ Fintype.card ι),
          (α (e idx).1 * s (e idx).1 (e idx).2) * charTensor (Z (e idx).1 (e idx).2) x := by
        intro x
        rw [hB x]
        calc ∑ r : Fin n, α r * F r x
            = ∑ r : Fin n, ∑ b : ι → Bool, (α r * s r b) * charTensor (Z r b) x := by
              refine Finset.sum_congr rfl fun r _ ↦ ?_
              rw [hFeq r x, Finset.mul_sum]
              exact Finset.sum_congr rfl fun b _ ↦ by ring
          _ = ∑ p : Fin n × (ι → Bool), (α p.1 * s p.1 p.2) * charTensor (Z p.1 p.2) x :=
              (Fintype.sum_prod_type (fun p : Fin n × (ι → Bool) ↦
                (α p.1 * s p.1 p.2) * charTensor (Z p.1 p.2) x)).symm
          _ = _ := (e.sum_comp (fun p : Fin n × (ι → Bool) ↦
                (α p.1 * s p.1 p.2) * charTensor (Z p.1 p.2) x)).symm
      have hle := mu_le_of_decomp (B := B)
        (fun idx : Fin (n * 2 ^ Fintype.card ι) ↦ α (e idx).1 * s (e idx).1 (e idx).2)
        (fun idx ↦ Z (e idx).1 (e idx).2)
        (fun idx ↦ hZ (e idx).1 (e idx).2) hB_eq
      refine hle.trans (le_of_eq ?_)
      calc ∑ idx : Fin (n * 2 ^ Fintype.card ι), |α (e idx).1 * s (e idx).1 (e idx).2|
          = ∑ p : Fin n × (ι → Bool), |α p.1 * s p.1 p.2| :=
            e.sum_comp (fun p : Fin n × (ι → Bool) ↦ |α p.1 * s p.1 p.2|)
        _ = ∑ r : Fin n, ∑ _b : ι → Bool, |α r| := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
            rw [abs_mul, hs r b, mul_one]
        _ = (2 : ℝ) ^ Fintype.card ι * ∑ r : Fin n, |α r| := by
            simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← Finset.mul_sum]
    have hmul := mul_le_mul_of_nonneg_left hmu (inv_nonneg.mpr h2k_pos.le)
    rwa [← mul_assoc, inv_mul_cancel₀ h2k_pos.ne', one_mul] at hmul
  exact ⟨hlower, hupper⟩

end CylinderNorm

section DeterministicAndRandomizedBounds

variable {ι : Type*} {X : ι → Type*}

/-- **the decomposition fact**:
If a Boolean function `f` has deterministic NOF complexity `D^k(f) ≤ c`, then its sign tensor
decomposes as a sum of `2^c` signed cylinder intersections `∑_{r < 2^c} α_r χ(Z_r)` with
`α_r ∈ {-1, +1}`. -/
theorem det_partition_cylinderInter [DecidableEq ι] [Nonempty ι] {f : (∀ i, X i) → Bool} {c : ℕ}
    (h : Protocol.ecomplexityFun f ≤ c) :
    ∃ (Z : Fin (2 ^ c) → Set (∀ i, X i)) (α : Fin (2 ^ c) → ℝ),
      (∀ r, IsCylinderIntersection (Z r)) ∧
      (∀ r, α r = 1 ∨ α r = -1) ∧
      ∀ x, signTensor f x = ∑ r : Fin (2 ^ c), α r * charTensor (Z r) x := by
  classical
  obtain ⟨p, hrun, hdepth⟩ := Protocol.ecomplexityFun_le_iff.mp h
  have hlc : p.leafCount ≤ 2 ^ c :=
    p.leafCount_le_two_pow_depth.trans (Nat.pow_le_pow_right (by omega) hdepth)
  let Z : Fin (2 ^ c) → Set (∀ i, X i) := fun r ↦
    if hr : r.val < p.leafCount then {x | p.leaf x = ⟨r.val, hr⟩} else ∅
  let α : Fin (2 ^ c) → ℝ := fun r ↦
    if hr : r.val < p.leafCount then
      if hex : ∃ x, p.leaf x = ⟨r.val, hr⟩ then signVal (f hex.choose) else 1
    else 1
  refine ⟨Z, α, ?_, ?_, ?_⟩
  · intro r
    dsimp only [Z]
    split_ifs with hr
    · exact p.isCylinderIntersection_leaf ⟨r.val, hr⟩
    · exact isCylinderIntersection_empty
  · intro r
    dsimp only [α]
    split_ifs with hr hex
    · exact isSignTensor_signTensor f hex.choose
    · exact Or.inl rfl
    · exact Or.inl rfl
  · intro x
    let r₀ : Fin (2 ^ c) := ⟨(p.leaf x).val, lt_of_lt_of_le (p.leaf x).isLt hlc⟩
    rw [Finset.sum_eq_single r₀]
    · have hr₀ : r₀.val < p.leafCount := (p.leaf x).isLt
      have hex : ∃ y, p.leaf y = ⟨r₀.val, hr₀⟩ := ⟨x, rfl⟩
      have hmem : x ∈ Z r₀ := by
        dsimp only [Z]
        rw [dite_eq_left hr₀]
        exact Fin.ext rfl
      rw [charTensor_of_mem hmem, mul_one]
      dsimp only [α]
      rw [dite_eq_left hr₀, dite_eq_left hex]
      have hfeq : f hex.choose = f x := by
        rw [← hrun]
        exact p.run_eq_of_leaf_eq hex.choose_spec
      rw [hfeq]
      rfl
    · intro r _ hne
      have hnot : x ∉ Z r := by
        dsimp only [Z]
        split_ifs with hr
        · intro hmem
          apply hne
          exact Fin.ext (congrArg Fin.val hmem).symm
        · exact Set.notMem_empty x
      rw [charTensor_of_notMem hnot, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim

/-- **exponential form**:
If `D^k(f) ≤ c`, then `μ(A_f) ≤ 2^c`. -/
theorem mu_le_two_pow_of_ecomplexityFun_le [DecidableEq ι] [Nonempty ι]
    {f : (∀ i, X i) → Bool} {c : ℕ} (h : Protocol.ecomplexityFun f ≤ c) :
    mu (signTensor f) ≤ (2 : ℝ) ^ c := by
  obtain ⟨Z, α, hZ, hα, hsum⟩ := det_partition_cylinderInter h
  refine (mu_le_of_decomp α Z hZ hsum).trans (le_of_eq ?_)
  have hones : ∀ r : Fin (2 ^ c), |α r| = 1 := fun r ↦ by
    rcases hα r with hr | hr <;> rw [hr] <;> norm_num
  simp_rw [hones]
  simp

/-- **logarithmic form**:
`log₂(μ(A_f)) ≤ c` whenever `D^k(f) ≤ c`. -/
theorem logb_mu_le_det_ecomplexity [DecidableEq ι] [Nonempty ι] {f : (∀ i, X i) → Bool} {c : ℕ}
    (h : Protocol.ecomplexityFun f ≤ c) :
    Real.logb 2 (mu (signTensor f)) ≤ (c : ℝ) := by
  by_cases hpos : 0 < mu (signTensor f)
  · rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos, Real.rpow_natCast]
    exact mu_le_two_pow_of_ecomplexityFun_le h
  · have hzero : mu (signTensor f) = 0 := le_antisymm (not_lt.mp hpos) (mu_nonneg _)
    rw [hzero, Real.logb_zero]
    positivity

/-- **the decomposition fact**:
A sign tensor `A_f` has public-coin randomized NOF complexity `R^k_ε(f) ≤ c` if and only if
there exist a probability distribution `(p_1, …, p_ℓ)` and functions `g_1, …, g_ℓ` with
`D^k(g_r) ≤ c` such that `‖A_f - ∑_r p_r A_{g_r}‖_∞ ≤ 2ε`. -/
theorem publicCoin_decomposition_iff [Finite ι] [∀ i, Finite (X i)] {f : (∀ i, X i) → Bool}
    {ε : ℝ} {c : ℕ}
    (hε : 0 ≤ ε) :
    PublicCoin.ecomplexityFun ε f ≤ c ↔
      ∃ (l : ℕ) (p : Fin l → ℝ) (g : Fin l → (∀ i, X i) → Bool),
        (∀ r, 0 ≤ p r) ∧
        (∑ r, p r = 1) ∧
        (∀ r, Protocol.ecomplexityFun (g r) ≤ c) ∧
        tensorLInfty (fun x ↦ signTensor f x - ∑ r, p r * signTensor (g r) x) ≤ 2 * ε := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun i ↦ Fintype.ofFinite (X i)
  constructor
  · intro h
    obtain ⟨μ, hsol, hdepth⟩ := PublicCoin.ecomplexity_le_iff.mp h
    let ν : PMF ((∀ i, X i) → Bool) := μ.map Protocol.run
    let S : Finset ((∀ i, X i) → Bool) :=
      Finset.univ.filter fun g ↦ Protocol.ecomplexityFun g ≤ c
    have hsupp : ∀ g ∈ ν.support, g ∈ S := by
      intro g hg
      rw [PMF.mem_support_map_iff] at hg
      rcases hg with ⟨P, hP, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (Protocol.ecomplexityFun_le_depth rfl).trans
        ((PublicCoin.depth_le_depth hP).trans hdepth)
    let e : Fin S.card ≃ {g // g ∈ S} := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
    have hsum_toReal : ∑ g : (∀ i, X i) → Bool, (ν g).toReal = 1 := by
      have hsum_enn : ∑ g : (∀ i, X i) → Bool, ν g = 1 := by
        have h := PMF.tsum_coe ν
        rwa [tsum_fintype] at h
      rw [← ENNReal.toReal_sum (fun g _ ↦ PMF.apply_ne_top ν g), hsum_enn, ENNReal.toReal_one]
    have hsum1 : ∑ r : Fin S.card, (ν (e r).1).toReal = 1 := by
      calc ∑ r : Fin S.card, (ν (e r).1).toReal
          = ∑ g : {g // g ∈ S}, (ν g.1).toReal := e.sum_comp (fun g : {g // g ∈ S} ↦ (ν g.1).toReal)
        _ = ∑ g ∈ S, (ν g).toReal := Finset.sum_coe_sort S (fun g ↦ (ν g).toReal)
        _ = ∑ g : (∀ i, X i) → Bool, (ν g).toReal := by
            refine Finset.sum_subset (Finset.subset_univ S) fun g _ hgS ↦ ?_
            have h0 : ν g = 0 := by
              by_contra hne
              exact hgS (hsupp g ((PMF.mem_support_iff ν g).mpr hne))
            simp [h0]
        _ = 1 := hsum_toReal
    refine ⟨S.card, fun r ↦ (ν (e r).1).toReal, fun r ↦ (e r).1,
      fun _ ↦ ENNReal.toReal_nonneg, hsum1, fun r ↦ (Finset.mem_filter.mp (e r).2).2, ?_⟩
    rw [tensorLInfty_le_iff _ (by linarith)]
    intro x
    have herr_eq :
        ∑ r : Fin S.card, (ν (e r).1).toReal * (if (e r).1 x ≠ f x then (1 : ℝ) else 0) =
          μ.errorProb (fun x b ↦ f x = b) x := by
      have hsum_all :
          ∑ r : Fin S.card, (ν (e r).1).toReal * (if (e r).1 x ≠ f x then (1 : ℝ) else 0) =
            ∑ g : (∀ i, X i) → Bool,
              (ν g).toReal * (if g x ≠ f x then (1 : ℝ) else 0) := by
        calc ∑ r : Fin S.card, (ν (e r).1).toReal * (if (e r).1 x ≠ f x then (1 : ℝ) else 0)
            = ∑ g : {g // g ∈ S}, (ν g.1).toReal * (if g.1 x ≠ f x then (1 : ℝ) else 0) :=
              e.sum_comp (fun g : {g // g ∈ S} ↦
                (ν g.1).toReal * (if g.1 x ≠ f x then (1 : ℝ) else 0))
          _ = ∑ g ∈ S, (ν g).toReal * (if g x ≠ f x then (1 : ℝ) else 0) :=
              Finset.sum_coe_sort S (fun g ↦ (ν g).toReal * (if g x ≠ f x then (1 : ℝ) else 0))
          _ = ∑ g : (∀ i, X i) → Bool, (ν g).toReal * (if g x ≠ f x then (1 : ℝ) else 0) := by
              refine Finset.sum_subset (Finset.subset_univ S) fun g _ hgS ↦ ?_
              have h0 : ν g = 0 := by
                by_contra hne
                exact hgS (hsupp g ((PMF.mem_support_iff ν g).mpr hne))
              simp [h0]
      rw [hsum_all]
      change _ = (μ.toOuterMeasure {P | ¬ f x = P.run x}).toReal
      have hpre : {P : Protocol X Bool | ¬ f x = P.run x} =
          Protocol.run ⁻¹' {g : (∀ i, X i) → Bool | g x ≠ f x} := by
        ext P; simp [eq_comm]
      rw [hpre, ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype]
      rw [ENNReal.toReal_sum (fun g _ ↦ by
        simp only [Set.indicator_apply]
        split_ifs
        · exact PMF.apply_ne_top ν g
        · exact ENNReal.zero_ne_top)]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      change (ν g).toReal * (if g x ≠ f x then (1 : ℝ) else 0) =
        ({g : (∀ i, X i) → Bool | g x ≠ f x}.indicator (⇑ν) g).toReal
      by_cases hne : g x ≠ f x
      · simp [hne]
      · simp [hne]
    have hdiff : signTensor f x - ∑ r : Fin S.card, (ν (e r).1).toReal * signTensor (e r).1 x =
        ∑ r : Fin S.card, (ν (e r).1).toReal * (signVal (f x) - signVal ((e r).1 x)) := by
      calc signVal (f x) - ∑ r, (ν (e r).1).toReal * signVal ((e r).1 x)
          = (∑ r, (ν (e r).1).toReal) * signVal (f x) -
              ∑ r, (ν (e r).1).toReal * signVal ((e r).1 x) := by rw [hsum1, one_mul]
        _ = ∑ r, (ν (e r).1).toReal * (signVal (f x) - signVal ((e r).1 x)) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun r _ ↦ by ring
    rw [hdiff]
    calc |∑ r, (ν (e r).1).toReal * (signVal (f x) - signVal ((e r).1 x))|
        ≤ ∑ r, |(ν (e r).1).toReal * (signVal (f x) - signVal ((e r).1 x))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = 2 * ∑ r, (ν (e r).1).toReal * (if (e r).1 x ≠ f x then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          cases f x <;> cases (e r).1 x <;> simp <;> ring
      _ = 2 * μ.errorProb (fun x b ↦ f x = b) x := by rw [herr_eq]
      _ ≤ 2 * ε := by linarith [hsol x (Set.mem_univ x)]
  · rintro ⟨l, p, g, hp0, hp1, hg, hinf⟩
    choose P hPrun hPdepth using fun r ↦ Protocol.ecomplexityFun_le_iff.mp (hg r)
    have hsum_enn : ∑ r : Fin l, ENNReal.ofReal (p r) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ ↦ hp0 r), hp1, ENNReal.ofReal_one]
    let μ₀ : PMF (Fin l) := PMF.ofFintype (fun r ↦ ENNReal.ofReal (p r)) hsum_enn
    let μ : PublicCoin X Bool := μ₀.map P
    change PublicCoin.ecomplexity ε (fun x b ↦ f x = b) Set.univ ≤ c
    rw [PublicCoin.ecomplexity_le_iff]
    refine ⟨μ, ?_, ?_⟩
    · intro x _
      have herr_eq : μ.errorProb (fun x b ↦ f x = b) x =
          ∑ r : Fin l, p r * (if g r x ≠ f x then (1 : ℝ) else 0) := by
        change (μ.toOuterMeasure {Q | ¬ f x = Q.run x}).toReal = _
        rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype]
        rw [ENNReal.toReal_sum (fun r _ ↦ by
          simp only [Set.indicator_apply]
          split_ifs
          · exact PMF.apply_ne_top μ₀ r
          · exact ENNReal.zero_ne_top)]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        have hiff : (P r ∈ {Q : Protocol X Bool | ¬ f x = Q.run x}) ↔ g r x ≠ f x := by
          simp [hPrun r, eq_comm]
        by_cases hne : g r x ≠ f x
        · rw [Set.indicator_apply, ite_eq_left (Set.mem_preimage.mpr (hiff.mpr hne)),
            ite_eq_left hne, mul_one]
          exact ENNReal.toReal_ofReal (hp0 r)
        · have hnot : P r ∉ {Q : Protocol X Bool | ¬ f x = Q.run x} := fun hm ↦ hne (hiff.mp hm)
          rw [Set.indicator_apply, ite_eq_right (Set.mem_preimage.not.mpr hnot),
            ite_eq_right hne, mul_zero, ENNReal.toReal_zero]
      rw [herr_eq]
      have hx := (tensorLInfty_le_iff _ (by linarith)).mp hinf x
      have hkey : 2 * ∑ r : Fin l, p r * (if g r x ≠ f x then (1 : ℝ) else 0) =
          |signTensor f x - ∑ r : Fin l, p r * signTensor (g r) x| := by
        have hident : signTensor f x * (signTensor f x - ∑ r, p r * signTensor (g r) x) =
            2 * ∑ r, p r * (if g r x ≠ f x then (1 : ℝ) else 0) := by
          rw [mul_sub, show signTensor f x * signTensor f x = 1 from signVal_mul_self (f x)]
          conv_lhs => rw [← hp1]
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          cases hfx : f x <;> cases hgx : g r x <;> simp [signTensor, hfx, hgx] <;> ring
        have hnn : 0 ≤ 2 * ∑ r, p r * (if g r x ≠ f x then (1 : ℝ) else 0) :=
          mul_nonneg zero_le_two (Finset.sum_nonneg fun r _ ↦
            mul_nonneg (hp0 r) (by split_ifs <;> norm_num))
        rw [← abs_of_nonneg hnn, ← hident, abs_mul,
          show |signTensor f x| = 1 from abs_signVal (f x), one_mul]
      linarith
    · rw [PublicCoin.depth_le_iff]
      intro Q hQ
      rw [PMF.mem_support_map_iff] at hQ
      rcases hQ with ⟨r, _, rfl⟩
      exact_mod_cast hPdepth r

/-- **`α`-approximate cylinder intersection norm `μ^α(A)`**. -/
noncomputable def muAlpha [DecidableEq ι] (α : ℝ) (A : Tensor X) : ℝ :=
  sInf {w : ℝ | ∃ B : Tensor X, (∀ x, 1 ≤ A x * B x ∧ A x * B x ≤ α) ∧ w = mu B}

/-- **`∞`-approximate cylinder intersection norm `μ^∞(A)`**. -/
noncomputable def muInfty [DecidableEq ι] (A : Tensor X) : ℝ :=
  sInf {w : ℝ | ∃ B : Tensor X, (∀ x, 1 ≤ A x * B x) ∧ w = mu B}

private theorem bddBelow_muAlpha_set [DecidableEq ι] (α : ℝ) (A : Tensor X) :
    BddBelow {w : ℝ | ∃ B : Tensor X, (∀ x, 1 ≤ A x * B x ∧ A x * B x ≤ α) ∧ w = mu B} :=
  ⟨0, fun _ ⟨B, _, hw⟩ ↦ hw ▸ mu_nonneg B⟩

private theorem bddBelow_muInfty_set [DecidableEq ι] (A : Tensor X) :
    BddBelow {w : ℝ | ∃ B : Tensor X, (∀ x, 1 ≤ A x * B x) ∧ w = mu B} :=
  ⟨0, fun _ ⟨B, _, hw⟩ ↦ hw ▸ mu_nonneg B⟩

/-- `μ^α(A)` is nonnegative. -/
theorem muAlpha_nonneg [DecidableEq ι] (α : ℝ) (A : Tensor X) : 0 ≤ muAlpha α A :=
  Real.sInf_nonneg fun _ ⟨B, _, hw⟩ ↦ hw ▸ mu_nonneg B

/-- `μ^∞(A)` is nonnegative. -/
theorem muInfty_nonneg [DecidableEq ι] (A : Tensor X) : 0 ≤ muInfty A :=
  Real.sInf_nonneg fun _ ⟨B, _, hw⟩ ↦ hw ▸ mu_nonneg B

/-- Any `α`-approximating tensor `B` bounds `μ^α(A)` from above by `μ(B)`. -/
theorem muAlpha_le_mu [DecidableEq ι] {α : ℝ} {A B : Tensor X}
    (h : ∀ x, 1 ≤ A x * B x ∧ A x * B x ≤ α) : muAlpha α A ≤ mu B :=
  csInf_le (bddBelow_muAlpha_set α A) ⟨B, h, rfl⟩

/-- Any sign-agreeing tensor `B` with `1 ≤ A ∘ B` bounds `μ^∞(A)` from above by `μ(B)`. -/
theorem muInfty_le_mu [DecidableEq ι] {A B : Tensor X} (h : ∀ x, 1 ≤ A x * B x) :
    muInfty A ≤ mu B :=
  csInf_le (bddBelow_muInfty_set A) ⟨B, h, rfl⟩

/-- Lower bound criterion for `μ^α(A)` on a sign tensor `A` with `1 ≤ α`. -/
theorem le_muAlpha_of_forall [DecidableEq ι] {A : Tensor X} (hA : IsSignTensor A) {α c : ℝ}
    (hα : 1 ≤ α)
    (h : ∀ B : Tensor X, (∀ x, 1 ≤ A x * B x ∧ A x * B x ≤ α) → c ≤ mu B) :
    c ≤ muAlpha α A := by
  refine le_csInf
    ⟨mu A, A, fun x ↦ ⟨by rw [hA.mul_self x], by rw [hA.mul_self x]; exact hα⟩, rfl⟩ ?_
  rintro w ⟨B, hB, rfl⟩
  exact h B hB

/-- Lower bound criterion for `μ^∞(A)` on a sign tensor `A`. -/
theorem le_muInfty_of_forall [DecidableEq ι] {A : Tensor X} (hA : IsSignTensor A) {c : ℝ}
    (h : ∀ B : Tensor X, (∀ x, 1 ≤ A x * B x) → c ≤ mu B) :
    c ≤ muInfty A := by
  refine le_csInf ⟨mu A, A, fun x ↦ by rw [hA.mul_self x], rfl⟩ ?_
  rintro w ⟨B, hB, rfl⟩
  exact h B hB

/-- `μ^α(A)` is antitone in `α` for `1 ≤ β ≤ α`. -/
theorem muAlpha_antitone [DecidableEq ι] {A : Tensor X} (hA : IsSignTensor A) {β α : ℝ}
    (hβ : 1 ≤ β) (hβα : β ≤ α) : muAlpha α A ≤ muAlpha β A := by
  refine csInf_le_csInf (bddBelow_muAlpha_set α A) ?_ ?_
  · exact ⟨mu A, A, fun x ↦ ⟨by rw [hA.mul_self x], by rw [hA.mul_self x]; exact hβ⟩, rfl⟩
  · rintro w ⟨B, hB, rfl⟩
    exact ⟨B, fun x ↦ ⟨(hB x).1, (hB x).2.trans hβα⟩, rfl⟩

/-- `μ^∞(A) ≤ μ^α(A)` for every sign tensor `A` and `1 ≤ α`. -/
theorem muInfty_le_muAlpha [DecidableEq ι] {A : Tensor X} (hA : IsSignTensor A) {α : ℝ}
    (hα : 1 ≤ α) : muInfty A ≤ muAlpha α A := by
  refine csInf_le_csInf (bddBelow_muInfty_set A) ?_ ?_
  · exact ⟨mu A, A, fun x ↦ ⟨by rw [hA.mul_self x], by rw [hA.mul_self x]; exact hα⟩, rfl⟩
  · rintro w ⟨B, hB, rfl⟩
    exact ⟨B, fun x ↦ (hB x).1, rfl⟩

/-- **exponential form**:
For `0 ≤ ε < 1/2` and `α ≥ α_ε = 1 / (1 - 2ε)`, if `R^k_ε(f) ≤ c`, then
`μ^α(A_f) ≤ α_ε · 2^c`. -/
theorem muAlpha_le_of_publicCoin_ecomplexityFun_le [Finite ι] [DecidableEq ι] [∀ i, Finite (X i)]
    [Nontrivial ι] {f : (∀ i, X i) → Bool} {ε α : ℝ} {c : ℕ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hα : 1 / (1 - 2 * ε) ≤ α)
    (h : PublicCoin.ecomplexityFun ε f ≤ c) :
    muAlpha α (signTensor f) ≤ (1 / (1 - 2 * ε)) * (2 : ℝ) ^ c := by
  have hpos : 0 < 1 - 2 * ε := by linarith
  have hαε1 : 1 ≤ 1 / (1 - 2 * ε) := by rw [le_div_iff₀ hpos]; linarith
  obtain ⟨l, p, g, hp0, hp1, hg, hinf⟩ := (publicCoin_decomposition_iff hε0).mp h
  let B : Tensor X := fun x ↦ (1 / (1 - 2 * ε)) * ∑ r : Fin l, p r * signTensor (g r) x
  have hB : ∀ x, 1 ≤ signTensor f x * B x ∧ signTensor f x * B x ≤ 1 / (1 - 2 * ε) := by
    intro x
    have hx := (tensorLInfty_le_iff _ (by linarith)).mp hinf x
    have habs : |1 - signTensor f x * ∑ r, p r * signTensor (g r) x| ≤ 2 * ε := by
      have heq : 1 - signTensor f x * ∑ r, p r * signTensor (g r) x =
          signTensor f x * (signTensor f x - ∑ r, p r * signTensor (g r) x) := by
        rw [mul_sub, show signTensor f x * signTensor f x = 1 from signVal_mul_self (f x)]
      rw [heq, abs_mul, show |signTensor f x| = 1 from abs_signVal (f x), one_mul]
      exact hx
    have hlo : 1 - 2 * ε ≤ signTensor f x * ∑ r, p r * signTensor (g r) x := by
      linarith [(abs_le.mp habs).2]
    have hhi : signTensor f x * ∑ r, p r * signTensor (g r) x ≤ 1 := by
      calc signTensor f x * ∑ r, p r * signTensor (g r) x
          ≤ |signTensor f x * ∑ r, p r * signTensor (g r) x| := le_abs_self _
        _ = |∑ r, p r * signTensor (g r) x| := by
            rw [abs_mul, show |signTensor f x| = 1 from abs_signVal (f x), one_mul]
        _ ≤ ∑ r, |p r * signTensor (g r) x| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ r, p r := Finset.sum_congr rfl fun r _ ↦ by
            rw [abs_mul, abs_of_nonneg (hp0 r),
              show |signTensor (g r) x| = 1 from abs_signVal (g r x), mul_one]
        _ = 1 := hp1
    constructor
    · dsimp only [B]
      rw [← mul_assoc, mul_comm (signTensor f x), mul_assoc, one_div_mul_eq_div, le_div_iff₀ hpos]
      linarith
    · dsimp only [B]
      rw [← mul_assoc, mul_comm (signTensor f x), mul_assoc]
      calc (1 / (1 - 2 * ε)) * (signTensor f x * ∑ r, p r * signTensor (g r) x)
          ≤ (1 / (1 - 2 * ε)) * 1 := mul_le_mul_of_nonneg_left hhi (by positivity)
        _ = 1 / (1 - 2 * ε) := mul_one _
  calc muAlpha α (signTensor f)
      ≤ muAlpha (1 / (1 - 2 * ε)) (signTensor f) :=
        muAlpha_antitone (isSignTensor_signTensor f) hαε1 hα
    _ ≤ mu B := muAlpha_le_mu hB
    _ = (1 / (1 - 2 * ε)) * mu (fun x ↦ ∑ r, p r * signTensor (g r) x) := by
        rw [mu_smul, abs_of_pos (by positivity)]
    _ ≤ (1 / (1 - 2 * ε)) * ∑ r, mu (fun x ↦ p r * signTensor (g r) x) :=
        mul_le_mul_of_nonneg_left (mu_finset_sum_le Finset.univ _) (by positivity)
    _ = (1 / (1 - 2 * ε)) * ∑ r, p r * mu (signTensor (g r)) := by
        congr 1
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [mu_smul, abs_of_nonneg (hp0 r)]
    _ ≤ (1 / (1 - 2 * ε)) * ∑ r, p r * (2 : ℝ) ^ c := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ ↦ ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (mu_le_two_pow_of_ecomplexityFun_le (hg r)) (hp0 r)
    _ = (1 / (1 - 2 * ε)) * (2 : ℝ) ^ c := by
        rw [← Finset.sum_mul, hp1, one_mul]

/-- **logarithmic form**:
For `0 ≤ ε < 1/2`, `α_ε = 1 / (1 - 2ε)`, `α ≥ α_ε`, and `R^k_ε(f) ≤ c`,
`log₂(μ^α(A_f)) - log₂(α_ε) ≤ c`. -/
theorem logb_muAlpha_le_publicCoin_ecomplexity [Finite ι] [DecidableEq ι] [∀ i, Finite (X i)]
    [Nontrivial ι]
    {f : (∀ i, X i) → Bool} {ε α : ℝ} {c : ℕ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hα : 1 / (1 - 2 * ε) ≤ α)
    (h : PublicCoin.ecomplexityFun ε f ≤ c) :
    Real.logb 2 (muAlpha α (signTensor f)) - Real.logb 2 (1 / (1 - 2 * ε)) ≤ (c : ℝ) := by
  have hpos : 0 < 1 - 2 * ε := by linarith
  have hαε_pos : 0 < 1 / (1 - 2 * ε) := by positivity
  have hαε_ge : 1 ≤ 1 / (1 - 2 * ε) := by rw [le_div_iff₀ hpos]; linarith
  have hlog_nn : 0 ≤ Real.logb 2 (1 / (1 - 2 * ε)) :=
    Real.logb_nonneg (by norm_num) hαε_ge
  by_cases hmu_pos : 0 < muAlpha α (signTensor f)
  · have hbound := muAlpha_le_of_publicCoin_ecomplexityFun_le hε0 hε hα h
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hmu_pos hbound
    rw [Real.logb_mul hαε_pos.ne' (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
    linarith
  · have hzero : muAlpha α (signTensor f) = 0 :=
      le_antisymm (not_lt.mp hmu_pos) (muAlpha_nonneg _ _)
    rw [hzero, Real.logb_zero]
    linarith [Nat.cast_nonneg (α := ℝ) c]

/-- **Nondeterministic cylinder-intersection cover**:
a finite collection of cylinder intersections covering every `-1` entry of a sign tensor `A` and
disjoint from every `+1` entry of `A`. -/
structure NondetCover [DecidableEq ι] (A : Tensor X) where
  /-- Number of cylinder intersections in the cover. -/
  size : ℕ
  /-- The covering family of subsets. -/
  sets : Fin size → Set (∀ i, X i)
  /-- Every set in the family is a cylinder intersection. -/
  all_cyl : ∀ r, IsCylinderIntersection (sets r)
  /-- No `+1` entry of `A` lies in any set of the cover. -/
  sound : ∀ r x, x ∈ sets r → A x = -1
  /-- Every `-1` entry of `A` is covered by at least one set. -/
  complete : ∀ x, A x = -1 → ∃ r, x ∈ sets r

/-- **cover-size form**:
For any sign tensor `A` and nondeterministic cover `C`, `μ^∞(A) ≤ 2 |C| + 1`, i.e.,
`(μ^∞(A) - 1) / 2 ≤ |C|`. -/
theorem muInfty_le_of_nondetCover [DecidableEq ι] {A : Tensor X} (hA : IsSignTensor A)
    (C : NondetCover A) : (muInfty A - 1) / 2 ≤ (C.size : ℝ) := by
  let B : Tensor X := fun x ↦ 1 - 2 * ∑ r : Fin C.size, charTensor (C.sets r) x
  have hlo : ∀ x, 1 ≤ A x * B x := by
    intro x
    rcases hA x with hx1 | hxm1
    · have hsum0 : ∑ r : Fin C.size, charTensor (C.sets r) x = 0 := by
        refine Finset.sum_eq_zero fun r _ ↦ charTensor_of_notMem fun hmem ↦ ?_
        have := C.sound r x hmem
        linarith
      simp [B, hx1, hsum0]
    · obtain ⟨r₀, hr₀⟩ := C.complete x hxm1
      have hge1 : (1 : ℝ) ≤ ∑ r : Fin C.size, charTensor (C.sets r) x := by
        calc (1 : ℝ) = charTensor (C.sets r₀) x := (charTensor_of_mem hr₀).symm
          _ ≤ ∑ r : Fin C.size, charTensor (C.sets r) x :=
              Finset.single_le_sum (f := fun r : Fin C.size ↦ charTensor (C.sets r) x)
                (fun r _ ↦ charTensor_nonneg (C.sets r) x) (Finset.mem_univ r₀)
      dsimp only [B]
      rw [hxm1]
      linarith
  have hmuB : mu B ≤ 2 * (C.size : ℝ) + 1 := by
    let α : Fin (C.size + 1) → ℝ := Fin.cases 1 (fun _ ↦ -2)
    let Z : Fin (C.size + 1) → Set (∀ i, X i) := Fin.cases Set.univ C.sets
    have hZ : ∀ r, IsCylinderIntersection (Z r) := Fin.cases isCylinderIntersection_univ C.all_cyl
    have hsum : ∀ x, B x = ∑ r : Fin (C.size + 1), α r * charTensor (Z r) x := fun x ↦ by
      rw [Fin.sum_univ_succ]
      simp only [α, Z, Fin.cases_zero, Fin.cases_succ, charTensor_univ, mul_one, B]
      rw [← Finset.mul_sum]
      ring
    refine (mu_le_of_decomp α Z hZ hsum).trans (le_of_eq ?_)
    rw [Fin.sum_univ_succ]
    simp only [α, Fin.cases_zero, Fin.cases_succ, abs_one, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have := (muInfty_le_mu hlo).trans hmuB
  linarith

/-- **logarithmic form**):
`log₂((μ^∞(A) - 1) / 2) ≤ log₂ |C|` whenever `1 < μ^∞(A)`. -/
theorem logb_muInfty_le_nondetCover [DecidableEq ι] {A : Tensor X} (hA : IsSignTensor A)
    (C : NondetCover A) (hgt : 1 < muInfty A) :
    Real.logb 2 ((muInfty A - 1) / 2) ≤ Real.logb 2 (C.size : ℝ) :=
  Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by linarith)
    (muInfty_le_of_nondetCover hA C)

end DeterministicAndRandomizedBounds

end CslibFrontier.Computability.Communication.NOF
