/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.CylinderNormDuality
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiparty Contraction Product, Contraction Inequality, and Hadamard Tensors

This module defines the multiparty contraction product `contractionProduct` (`B •₁ B`), proves the
iterative Cauchy–Schwarz contraction inequality relating `μ*(B)` to `μ*(B •₁ B)` and
`𝔼[|B •₁ B|]`, defines multiparty Hadamard tensors, and derives lower bounds on `μ^∞` for Hadamard
matrices and Hadamard tensors together with a concrete Sylvester Hadamard witness.

## Main definitions

* `ContractionSpace`, `cubeVertex`, `contractionProduct`, `tensorExpectAbs`: domain and definition
  of the contraction product `B •₁ B` and its average absolute value.
* `IsHadamardTensor`, `sylvesterHadamard2`: multiparty Hadamard tensors and a `2`-point witness.

## Main results

* `contraction_inequality`: `(μ*(B) / size(B))^{2^r} ≤ μ*(B •₁ B) / size(B •₁ B) ≤ 𝔼[|B •₁ B|]`.
* `hadamard_matrix_muInfty_ge_sqrt`: `√N ≤ μ^∞(H)` for `N × N` Hadamard sign matrices.
* `hadamardTensor_muInfty_ge`: `(N / r)^{1 / 2^r} ≤ μ^∞(H)` for `(r + 1)`-party Hadamard tensors.
-/

public section

open scoped BigOperators
open Cslib.BitString Cslib.Communication.NOF

namespace CslibFrontier.Computability.Communication.NOF

section Contraction

variable {r : ℕ} {X : Fin (r + 1) → Type*}

/-- The `2r`-party domain `X₁ × X₁ × ⋯ × X_r × X_r` of the contraction product `B •₁ B`,
indexed by `Fin r × Bool`. -/
abbrev ContractionSpace (X : Fin (r + 1) → Type*) : Fin r × Bool → Type _ :=
  fun p ↦ X p.1.succ

/-- Vertex `(x₀, y₁^{ℓ₁}, …, y_r^{ℓ_r})` of the Boolean cube indexed by `z: ∀ p, X p.1.succ`
and `ℓ: Fin r → Bool`. -/
@[expose] def cubeVertex (x₀ : X 0) (z : ∀ p : Fin r × Bool, ContractionSpace X p)
    (ℓ : Fin r → Bool) : ∀ i : Fin (r + 1), X i :=
  Fin.cases x₀ (fun j ↦ z (j, ℓ j))

/-- **Contraction product `B •₁ B`**:
`(B •₁ B)[z] = 𝔼_{x₀} [∏_{ℓ: Fin r → Bool} B(x₀, z(·, ℓ ·))]`. -/
@[expose] noncomputable def contractionProduct [Fintype (X 0)] (B : Tensor X) :
    Tensor (ContractionSpace X) :=
  fun z ↦ (Fintype.card (X 0) : ℝ)⁻¹ * ∑ x₀ : X 0, ∏ ℓ : Fin r → Bool, B (cubeVertex x₀ z ℓ)

/-- Pointwise evaluation of the contraction product `B •₁ B`. -/
theorem contractionProduct_apply [Fintype (X 0)] (B : Tensor X)
    (z : ∀ p : Fin r × Bool, ContractionSpace X p) :
    contractionProduct B z =
      (Fintype.card (X 0) : ℝ)⁻¹ * ∑ x₀ : X 0, ∏ ℓ : Fin r → Bool, B (cubeVertex x₀ z ℓ) := rfl

/-- Uniform expectation of `|A|` over its finite domain. -/
@[expose] noncomputable def tensorExpectAbs {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
    [∀ i, Fintype (Y i)] (A : Tensor Y) : ℝ :=
  (tensorSize Y : ℝ)⁻¹ * tensorL1 A

/-- Characterization of `tensorExpectAbs` in terms of `tensorSize` and `tensorL1`. -/
theorem tensorExpectAbs_eq_inv_mul_l1 {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
    [∀ i, Fintype (Y i)] (A : Tensor Y) :
    tensorExpectAbs A = (tensorSize Y : ℝ)⁻¹ * tensorL1 A := rfl

/-- The size of `ContractionSpace X` equals `(∏ j: Fin r, |X j.succ|)^2`. -/
theorem tensorSize_contractionSpace [∀ i, Fintype (X i)] :
    tensorSize (ContractionSpace X) = (∏ j : Fin r, Fintype.card (X j.succ)) ^ 2 := by
  rw [tensorSize_eq_prod, Fintype.prod_prod_type]
  simp_rw [Fintype.prod_bool, ← sq, Finset.prod_pow]

/-- Partial cube vertex for stage `t ≤ r`: coordinates `j < t` branch via `ℓ: Fin t → Bool`,
while coordinates `j ≥ t` use the `false` copy `z (j, false)`. -/
private def stageVertex (t : ℕ) (x₀ : X 0) (z : ∀ p : Fin r × Bool, ContractionSpace X p)
    (ℓ : Fin t → Bool) : ∀ i : Fin (r + 1), X i :=
  Fin.cases x₀ (fun j ↦ if h : j.val < t then z (j, ℓ ⟨j.val, h⟩) else z (j, false))

private def boolInd (b : Bool) : ℝ :=
  if b then 1 else 0

private theorem boolInd_sq (b : Bool) : boolInd b ^ 2 = boolInd b := by
  cases b <;> norm_num [boolInd]

private theorem boolInd_le_one (b : Bool) : boolInd b ≤ 1 := by
  cases b <;> norm_num [boolInd]

/-- Stage `t` integrand in the `r`-step Cauchy–Schwarz proof of the contraction lemma. -/
private def stageIntegrand (B : Tensor X) (φ : ∀ i : Fin (r + 1), View X i → Bool) (t : ℕ)
    (x₀ : X 0) (z : ∀ p : Fin r × Bool, ContractionSpace X p) : ℝ :=
  ∏ ℓ : Fin t → Bool,
    B (stageVertex t x₀ z ℓ) *
    boolInd (φ 0 (view 0 (stageVertex t x₀ z ℓ))) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin r ↦ t ≤ j.val),
      boolInd (φ j.succ (view j.succ (stageVertex t x₀ z ℓ)))

/-- Finite Cauchy–Schwarz inequality for uniform averages:
`((|α|⁻¹ ∑ a, f a))^2 ≤ |α|⁻¹ ∑ a, (f a)^2`. -/
private theorem sq_avg_le_avg_sq {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ((Fintype.card α : ℝ)⁻¹ * ∑ a : α, f a) ^ 2 ≤
      (Fintype.card α : ℝ)⁻¹ * ∑ a : α, f a ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hcs : (∑ a : α, f a * (1 : ℝ)) ^ 2 ≤ (∑ a : α, f a ^ 2) * (∑ _a : α, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
  rw [mul_pow, inv_pow]
  calc ((Fintype.card α : ℝ) ^ 2)⁻¹ * (∑ a : α, f a) ^ 2
      ≤ ((Fintype.card α : ℝ) ^ 2)⁻¹ * ((∑ a : α, f a ^ 2) * (Fintype.card α : ℝ)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (Fintype.card α : ℝ)⁻¹ * ∑ a : α, f a ^ 2 := by
        field_simp [hcard.ne']

/-- Updating one coordinate in a `Pi` type preserves the uniform average. -/
private theorem avg_pi_eq_avg_update {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Y : κ → Type*} [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)] (k₀ : κ)
    (F : (∀ k, Y k) → ℝ) :
    ((Fintype.card (∀ k, Y k) : ℝ)⁻¹ * ∑ z : ∀ k, Y k, F z) =
      (Fintype.card (∀ k, Y k) : ℝ)⁻¹ *
        ∑ z : ∀ k, Y k, (Fintype.card (Y k₀) : ℝ)⁻¹ * ∑ a : Y k₀, F (Function.update z k₀ a) := by
  have hcard : (0 : ℝ) < Fintype.card (Y k₀) := by exact_mod_cast Fintype.card_pos (α := Y k₀)
  let e : ((∀ k, Y k) × Y k₀) ≃ ((∀ k, Y k) × Y k₀) :=
    { toFun := fun p ↦ (Function.update p.1 k₀ p.2, p.1 k₀)
      invFun := fun p ↦ (Function.update p.1 k₀ p.2, p.1 k₀)
      left_inv := fun ⟨z, a⟩ ↦ by
        ext k
        · by_cases hk : k = k₀
          · subst hk; simp
          · simp [Function.update_of_ne hk]
        · simp
      right_inv := fun ⟨z, a⟩ ↦ by
        ext k
        · by_cases hk : k = k₀
          · subst hk; simp
          · simp [Function.update_of_ne hk]
        · simp }
  have hsum_eq : ∑ z : ∀ k, Y k, ∑ a : Y k₀, F (Function.update z k₀ a) =
      (Fintype.card (Y k₀) : ℝ) * ∑ z : ∀ k, Y k, F z := by
    calc ∑ z : ∀ k, Y k, ∑ a : Y k₀, F (Function.update z k₀ a)
        = ∑ p : (∀ k, Y k) × Y k₀, F (e p).1 :=
          (Fintype.sum_prod_type (fun p : (∀ k, Y k) × Y k₀ ↦ F (e p).1)).symm
      _ = ∑ p : (∀ k, Y k) × Y k₀, F p.1 := e.sum_comp (fun p : (∀ k, Y k) × Y k₀ ↦ F p.1)
      _ = ∑ z : ∀ k, Y k, ∑ _a : Y k₀, F z := Fintype.sum_prod_type _
      _ = (Fintype.card (Y k₀) : ℝ) * ∑ z : ∀ k, Y k, F z := by
          simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Finset.mul_sum, hsum_eq]
  field_simp [hcard.ne']

/-- Simultaneous two-coordinate averaging identity. -/
private theorem avg_pi_eq_avg_update_two {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Y : κ → Type*} [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)] (k₀ k₁ : κ)
    (F : (∀ k, Y k) → ℝ) :
    ((Fintype.card (∀ k, Y k) : ℝ)⁻¹ * ∑ z : ∀ k, Y k, F z) =
      (Fintype.card (∀ k, Y k) : ℝ)⁻¹ *
        ∑ z : ∀ k, Y k, (Fintype.card (Y k₀) : ℝ)⁻¹ *
          ∑ a₀ : Y k₀, (Fintype.card (Y k₁) : ℝ)⁻¹ *
            ∑ a₁ : Y k₁, F (Function.update (Function.update z k₀ a₀) k₁ a₁) := by
  rw [avg_pi_eq_avg_update k₁ F]
  exact avg_pi_eq_avg_update k₀ (fun z ↦ (Fintype.card (Y k₁) : ℝ)⁻¹ *
    ∑ a₁ : Y k₁, F (Function.update z k₁ a₁))

/-- One step of the Cauchy–Schwarz contraction induction (`t → t + 1` for `t < r`). -/
private theorem stage_step [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (B : Tensor X) (φ : ∀ i : Fin (r + 1), View X i → Bool) {t : ℕ} (ht : t < r) :
    ((Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
      ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
        stageIntegrand B φ t x₀ z) ^ 2 ≤
    (Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
      ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
        stageIntegrand B φ (t + 1) x₀ z := by
  let j₀ : Fin r := ⟨t, ht⟩
  let S_t : Finset (Fin r) := Finset.univ.filter (fun j : Fin r ↦ t ≤ j.val)
  let S_succ : Finset (Fin r) := Finset.univ.filter (fun j : Fin r ↦ t + 1 ≤ j.val)
  have hS_split : S_t = insert j₀ S_succ := by
    ext j
    simp only [S_t, S_succ, j₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have hj₀_notMem : j₀ ∉ S_succ := by simp [S_succ, j₀]
  let F : X 0 → (∀ p : Fin r × Bool, ContractionSpace X p) → ℝ := fun x₀ z ↦
    ∏ ℓ : Fin t → Bool, boolInd (φ j₀.succ (view j₀.succ (stageVertex t x₀ z ℓ)))
  let G : X 0 → (∀ p : Fin r × Bool, ContractionSpace X p) → ℝ := fun x₀ z ↦
    ∏ ℓ : Fin t → Bool,
      B (stageVertex t x₀ z ℓ) *
      boolInd (φ 0 (view 0 (stageVertex t x₀ z ℓ))) *
      ∏ j ∈ S_succ, boolInd (φ j.succ (view j.succ (stageVertex t x₀ z ℓ)))
  have hdecomp : ∀ x₀ z, stageIntegrand B φ t x₀ z = F x₀ z * G x₀ z := by
    intro x₀ z
    dsimp only [stageIntegrand, F, G]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ℓ _ ↦ ?_
    change B (stageVertex t x₀ z ℓ) * boolInd (φ 0 (view 0 (stageVertex t x₀ z ℓ))) *
        ∏ j ∈ S_t, boolInd (φ j.succ (view j.succ (stageVertex t x₀ z ℓ))) = _
    rw [hS_split, Finset.prod_insert hj₀_notMem]
    ring
  have hF_indep : ∀ x₀ z a, F x₀ (Function.update z (j₀, false) a) = F x₀ z := by
    intro x₀ z a
    refine Finset.prod_congr rfl fun ℓ _ ↦ ?_
    congr 2
    funext ⟨i, hi⟩
    revert hi
    refine Fin.cases (fun _ ↦ rfl) (fun j hj ↦ ?_) i
    dsimp only [view, stageVertex]
    simp only [Fin.cases_succ]
    have hne_j : j ≠ j₀ := fun h ↦ hj (by subst h; rfl)
    have hne_pair : ∀ b : Bool, (j, b) ≠ (j₀, false) := fun b h ↦ hne_j (congrArg Prod.fst h)
    split_ifs <;> exact Function.update_of_ne (hne_pair _) _ _
  have hF_sq : ∀ x₀ z, (F x₀ z) ^ 2 ≤ 1 := by
    intro x₀ z
    have h01 : F x₀ z = 0 ∨ F x₀ z = 1 := by
      dsimp only [F]
      by_cases h : ∀ ℓ : Fin t → Bool, φ j₀.succ (view j₀.succ (stageVertex t x₀ z ℓ)) = true
      · right
        exact Finset.prod_eq_one fun ℓ _ ↦ by simp [boolInd, h ℓ]
      · push Not at h
        obtain ⟨ℓ, hℓ⟩ := h
        left
        exact Finset.prod_eq_zero (Finset.mem_univ ℓ) (by simp [boolInd, hℓ])
    rcases h01 with h | h <;> rw [h] <;> norm_num
  have hG_indep_true : ∀ x₀ z a, G x₀ (Function.update z (j₀, true) a) = G x₀ z := by
    intro x₀ z a
    have hvert : ∀ ℓ : Fin t → Bool,
        stageVertex t x₀ (Function.update z (j₀, true) a) ℓ = stageVertex t x₀ z ℓ := by
      intro ℓ
      funext i
      refine Fin.cases rfl (fun j ↦ ?_) i
      dsimp only [stageVertex]
      simp only [Fin.cases_succ]
      split_ifs with hj
      · have hne : (j, ℓ ⟨j.val, hj⟩) ≠ (j₀, true) := by
          intro h
          have hv : j.val = t := congrArg (fun p : Fin r × Bool ↦ p.1.val) h
          omega
        rw [Function.update_of_ne hne]
      · have hne : (j, false) ≠ (j₀, true) := by intro h; cases congrArg Prod.snd h
        rw [Function.update_of_ne hne]
    dsimp only [G]
    simp_rw [hvert]
  have havg_rewrite :
      (Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
        ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
          stageIntegrand B φ t x₀ z =
      (Fintype.card (X 0 × (∀ p : Fin r × Bool, ContractionSpace X p)) : ℝ)⁻¹ *
        ∑ p : X 0 × (∀ p : Fin r × Bool, ContractionSpace X p),
          F p.1 p.2 * ((Fintype.card (X j₀.succ) : ℝ)⁻¹ *
            ∑ a : X j₀.succ, G p.1 (Function.update p.2 (j₀, false) a)) := by
    have hcard_prod : (Fintype.card (X 0 × (∀ p : Fin r × Bool, ContractionSpace X p)) : ℝ) =
        (Fintype.card (X 0) : ℝ) * (tensorSize (ContractionSpace X) : ℝ) := by
      simp [tensorSize_eq_card]
    rw [hcard_prod, mul_inv, Fintype.sum_prod_type]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₀ _ ↦ ?_
    have hstep := avg_pi_eq_avg_update (Y := ContractionSpace X) (j₀, false)
      (fun z ↦ stageIntegrand B φ t x₀ z)
    change (tensorSize (ContractionSpace X) : ℝ)⁻¹ * ∑ z, stageIntegrand B φ t x₀ z =
      (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
        ∑ z, (Fintype.card (X j₀.succ) : ℝ)⁻¹ *
          ∑ a : X j₀.succ, stageIntegrand B φ t x₀ (Function.update z (j₀, false) a) at hstep
    rw [hstep]
    congr 1
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    simp_rw [hdecomp, hF_indep, ← Finset.mul_sum]
    ring
  rw [havg_rewrite]
  have hcs := sq_avg_le_avg_sq (α := X 0 × (∀ p : Fin r × Bool, ContractionSpace X p))
    (fun p ↦ F p.1 p.2 * ((Fintype.card (X j₀.succ) : ℝ)⁻¹ *
      ∑ a : X j₀.succ, G p.1 (Function.update p.2 (j₀, false) a)))
  refine hcs.trans ?_
  have hdrop :
      (Fintype.card (X 0 × (∀ p : Fin r × Bool, ContractionSpace X p)) : ℝ)⁻¹ *
        ∑ p : X 0 × (∀ p : Fin r × Bool, ContractionSpace X p),
          (F p.1 p.2 * ((Fintype.card (X j₀.succ) : ℝ)⁻¹ *
            ∑ a : X j₀.succ, G p.1 (Function.update p.2 (j₀, false) a))) ^ 2 ≤
      (Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
        ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
          ((Fintype.card (X j₀.succ) : ℝ)⁻¹ *
            ∑ a : X j₀.succ, G x₀ (Function.update z (j₀, false) a)) ^ 2 := by
    have hcard_prod : (Fintype.card (X 0 × (∀ p : Fin r × Bool, ContractionSpace X p)) : ℝ) =
        (Fintype.card (X 0) : ℝ) * (tensorSize (ContractionSpace X) : ℝ) := by
      simp [tensorSize_eq_card]
    rw [hcard_prod, mul_inv, Fintype.sum_prod_type]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x₀ _ ↦ Finset.sum_le_sum fun z _ ↦ ?_)
      (by positivity)
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (hF_sq x₀ z)
  refine hdrop.trans (le_of_eq ?_)
  rw [mul_assoc, mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x₀ _ ↦ ?_
  have hprod_split : ∀ z : ∀ p : Fin r × Bool, ContractionSpace X p,
      stageIntegrand B φ (t + 1) x₀ z =
        G x₀ (Function.update z (j₀, false) (z (j₀, false))) *
        G x₀ (Function.update z (j₀, false) (z (j₀, true))) := by
    intro z
    have hvert_b : ∀ (b : Bool) (ℓ : Fin t → Bool),
        stageVertex (t + 1) x₀ z (Fin.snoc (α := fun _ ↦ Bool) ℓ b) =
          stageVertex t x₀ (Function.update z (j₀, false) (z (j₀, b))) ℓ := by
      intro b ℓ
      funext i
      refine Fin.cases rfl (fun j ↦ ?_) i
      dsimp only [stageVertex]
      simp only [Fin.cases_succ]
      by_cases hlt : j.val < t
      · have hlt' : j.val < t + 1 := Nat.lt_succ_of_lt hlt
        rw [dite_eq_left hlt', dite_eq_left hlt]
        have hsnoc : Fin.snoc (α := fun _ ↦ Bool) ℓ b ⟨j.val, hlt'⟩ = ℓ ⟨j.val, hlt⟩ := by
          change Fin.snoc (α := fun _ ↦ Bool) ℓ b (Fin.castSucc ⟨j.val, hlt⟩) = ℓ ⟨j.val, hlt⟩
          exact Fin.snoc_castSucc (α := fun _ ↦ Bool) b ℓ ⟨j.val, hlt⟩
        rw [hsnoc]
        have hne : (j, ℓ ⟨j.val, hlt⟩) ≠ (j₀, false) := fun h ↦ by
          have hv : j.val = t := congrArg (fun p : Fin r × Bool ↦ p.1.val) h
          omega
        rw [Function.update_of_ne hne]
      · by_cases heq : j.val = t
        · have hlt' : j.val < t + 1 := by omega
          rw [dite_eq_left hlt', dite_eq_right hlt]
          have hlast : (⟨j.val, hlt'⟩ : Fin (t + 1)) = Fin.last t := Fin.ext heq
          rw [hlast, Fin.snoc_last (α := fun _ ↦ Bool)]
          have hjj₀ : j = j₀ := Fin.ext heq
          subst hjj₀
          simp
        · have hnot' : ¬ j.val < t + 1 := by omega
          rw [dite_eq_right hnot', dite_eq_right hlt]
          have hne : (j, false) ≠ (j₀, false) := fun h ↦
            heq (congrArg (fun p : Fin r × Bool ↦ p.1.val) h)
          rw [Function.update_of_ne hne]
    let eSnoc : ((Fin t → Bool) × Bool) ≃ (Fin (t + 1) → Bool) :=
      { toFun := fun p ↦ Fin.snoc (α := fun _ ↦ Bool) p.1 p.2
        invFun := fun ℓ ↦ (Fin.init ℓ, ℓ (Fin.last t))
        left_inv := fun ⟨ℓ, b⟩ ↦ by
          ext i
          · exact Fin.snoc_castSucc (α := fun _ ↦ Bool) b ℓ i
          · exact Fin.snoc_last (α := fun _ ↦ Bool) b ℓ
        right_inv := fun ℓ ↦ by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · exact Fin.snoc_last (α := fun _ ↦ Bool) _ _
          · intro j; exact Fin.snoc_castSucc (α := fun _ ↦ Bool) _ _ j }
    dsimp only [stageIntegrand]
    rw [← eSnoc.prod_comp, Fintype.prod_prod_type_right, Fintype.prod_bool]
    dsimp only [eSnoc, Equiv.coe_fn_mk, G]
    rw [mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun ℓ _ ↦ by rw [hvert_b false ℓ]
    · refine Finset.prod_congr rfl fun ℓ _ ↦ by rw [hvert_b true ℓ]
  have htwo := avg_pi_eq_avg_update_two (Y := ContractionSpace X)
    (j₀, false) (j₀, true) (fun z ↦ stageIntegrand B φ (t + 1) x₀ z)
  change (tensorSize (ContractionSpace X) : ℝ)⁻¹ * ∑ z, stageIntegrand B φ (t + 1) x₀ z = _ at htwo
  rw [htwo]
  congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hterm : ∀ (a₀ a₁ : X j₀.succ),
      stageIntegrand B φ (t + 1) x₀
        (Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁) =
      G x₀ (Function.update z (j₀, false) a₀) * G x₀ (Function.update z (j₀, false) a₁) := by
    intro a₀ a₁
    rw [hprod_split]
    have h1 : Function.update (Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁)
        (j₀, false)
        (Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁ (j₀, false)) =
        Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁ := by
      simp
    have h2 : Function.update (Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁)
        (j₀, false)
        (Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁ (j₀, true)) =
        Function.update (Function.update z (j₀, false) a₁) (j₀, true) a₁ := by
      have hval : Function.update (Function.update z (j₀, false) a₀) (j₀, true) a₁ (j₀, true) =
          a₁ := by simp
      rw [hval]
      funext p
      by_cases hp1 : p = (j₀, false)
      · subst hp1; simp
      · by_cases hp2 : p = (j₀, true)
        · subst hp2; simp
        · simp [Function.update_of_ne hp1, Function.update_of_ne hp2]
    rw [h1, h2, hG_indep_true, hG_indep_true]
  simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sq]
  ring

/-- Stage `0` uniform average equals `⟨B, χ(cylinderIntersection φ)⟩ / size(X)`. -/
private theorem stage_zero_eq [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (B : Tensor X) (φ : ∀ i : Fin (r + 1), View X i → Bool) :
    (Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
      ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
        stageIntegrand B φ 0 x₀ z =
    tensorInner B (charTensor (cylinderIntersection φ)) / (tensorSize X : ℝ) := by
  let e : (∀ p : Fin r × Bool, ContractionSpace X p) ≃
      ((∀ j : Fin r, X j.succ) × (∀ j : Fin r, X j.succ)) :=
    { toFun := fun z ↦ (fun j ↦ z (j, false), fun j ↦ z (j, true))
      invFun := fun p q ↦ if q.2 then p.2 q.1 else p.1 q.1
      left_inv := fun z ↦ by funext ⟨j, b⟩; cases b <;> rfl
      right_inv := fun ⟨y₀, y₁⟩ ↦ by ext j <;> rfl }
  let eX : (X 0 × (∀ j : Fin r, X j.succ)) ≃ (∀ i : Fin (r + 1), X i) :=
    { toFun := fun p ↦ Fin.cases p.1 p.2
      invFun := fun x ↦ (x 0, fun j ↦ x j.succ)
      left_inv := fun ⟨x₀, y⟩ ↦ by ext <;> rfl
      right_inv := fun x ↦ by funext i; refine Fin.cases rfl (fun _ ↦ rfl) i }
  have hstage0 : ∀ x₀ z, stageIntegrand B φ 0 x₀ z =
      B (eX (x₀, (e z).1)) * charTensor (cylinderIntersection φ) (eX (x₀, (e z).1)) := by
    intro x₀ z
    dsimp only [stageIntegrand]
    have huniq : (∏ ℓ : Fin 0 → Bool,
        B (stageVertex 0 x₀ z ℓ) *
        boolInd (φ 0 (view 0 (stageVertex 0 x₀ z ℓ))) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin r ↦ 0 ≤ j.val),
          boolInd (φ j.succ (view j.succ (stageVertex 0 x₀ z ℓ)))) =
        B (eX (x₀, (e z).1)) *
        boolInd (φ 0 (view 0 (eX (x₀, (e z).1)))) *
        ∏ j : Fin r, boolInd (φ j.succ (view j.succ (eX (x₀, (e z).1)))) := by
      rw [Fintype.prod_unique]
      have hv : ∀ ℓ : Fin 0 → Bool, stageVertex 0 x₀ z ℓ = eX (x₀, (e z).1) := fun ℓ ↦ by
        funext i
        refine Fin.cases rfl (fun j ↦ ?_) i
        simp [stageVertex, eX, e]
      have hfilt : Finset.univ.filter (fun j : Fin r ↦ 0 ≤ j.val) = Finset.univ := by
        ext j; simp
      rw [hv, hfilt]
    rw [huniq, mul_assoc]
    congr 1
    rw [← Fin.prod_univ_succ (fun i : Fin (r + 1) ↦ boolInd (φ i (view i (eX (x₀, (e z).1)))))]
    by_cases hmem : eX (x₀, (e z).1) ∈ cylinderIntersection φ
    · rw [charTensor_of_mem hmem]
      exact Finset.prod_eq_one fun i _ ↦ by
        simp [boolInd, mem_cylinderIntersection.mp hmem i]
    · rw [charTensor_of_notMem hmem]
      obtain ⟨i, hi⟩ := not_forall.mp (mem_cylinderIntersection.not.mp hmem)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [boolInd, hi])
  have hsum_z : ∀ x₀ : X 0,
      ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p, stageIntegrand B φ 0 x₀ z =
      (Fintype.card (∀ j : Fin r, X j.succ) : ℝ) *
        ∑ y : ∀ j : Fin r, X j.succ,
          B (eX (x₀, y)) * charTensor (cylinderIntersection φ) (eX (x₀, y)) := by
    intro x₀
    simp_rw [hstage0]
    rw [← e.symm.sum_comp]
    rw [Fintype.sum_prod_type]
    have hsimp : ∀ y₀ y₁ : ∀ j : Fin r, X j.succ, (e (e.symm (y₀, y₁))).1 = y₀ := fun y₀ y₁ ↦ by
      rw [e.apply_symm_apply]
    simp_rw [hsimp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  simp_rw [hsum_z, ← Finset.mul_sum]
  have hinner : ∑ x₀ : X 0, ∑ y : ∀ j : Fin r, X j.succ,
      B (eX (x₀, y)) * charTensor (cylinderIntersection φ) (eX (x₀, y)) =
      tensorInner B (charTensor (cylinderIntersection φ)) := by
    rw [← Fintype.sum_prod_type (fun p : X 0 × (∀ j : Fin r, X j.succ) ↦
      B (eX p) * charTensor (cylinderIntersection φ) (eX p))]
    exact eX.sum_comp (fun x ↦ B x * charTensor (cylinderIntersection φ) x)
  rw [hinner]
  have hcard_X : (tensorSize X : ℝ) =
      (Fintype.card (X 0) : ℝ) * (Fintype.card (∀ j : Fin r, X j.succ) : ℝ) := by
    have := Fintype.card_congr eX
    simp only [Fintype.card_prod] at this
    change ((Fintype.card (∀ i : Fin (r + 1), X i) : ℕ) : ℝ) = _
    rw [← this, Nat.cast_mul]
  have hcard_C : (tensorSize (ContractionSpace X) : ℝ) =
      (Fintype.card (∀ j : Fin r, X j.succ) : ℝ) *
      (Fintype.card (∀ j : Fin r, X j.succ) : ℝ) := by
    have := Fintype.card_congr e
    simp only [Fintype.card_prod] at this
    change ((Fintype.card (∀ p : Fin r × Bool, ContractionSpace X p) : ℕ) : ℝ) = _
    rw [this, Nat.cast_mul]
  have hpos0 : (0 : ℝ) < Fintype.card (X 0) := by exact_mod_cast Fintype.card_pos (α := X 0)
  have hposY : (0 : ℝ) < Fintype.card (∀ j : Fin r, X j.succ) := by
    exact_mod_cast Fintype.card_pos (α := ∀ j : Fin r, X j.succ)
  rw [hcard_X, hcard_C]
  field_simp [hpos0.ne', hposY.ne']

/-- Stage `r` uniform average equals `⟨B •₁ B, χ(W)⟩ / size(B •₁ B)` for a cylinder intersection
`W` on `ContractionSpace X`. -/
private theorem stage_final_eq [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (hr : 1 ≤ r)
    (B : Tensor X) (φ : ∀ i : Fin (r + 1), View X i → Bool) :
    ∃ W : Set (∀ p : Fin r × Bool, ContractionSpace X p),
      IsCylinderIntersection W ∧
      (Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
        ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
          stageIntegrand B φ r x₀ z =
      tensorInner (contractionProduct B) (charTensor W) /
        (tensorSize (ContractionSpace X) : ℝ) := by
  let x₀_arb : X 0 := Classical.arbitrary (X 0)
  let j₀ : Fin r := ⟨0, hr⟩
  let W : Set (∀ p : Fin r × Bool, ContractionSpace X p) :=
    {z | ∀ ℓ : Fin r → Bool, φ 0 (view 0 (cubeVertex x₀_arb z ℓ)) = true}
  have hview0_indep : ∀ (x₀ : X 0) (z : ∀ p : Fin r × Bool, ContractionSpace X p)
      (ℓ : Fin r → Bool),
      view 0 (cubeVertex x₀ z ℓ) = view 0 (cubeVertex x₀_arb z ℓ) := by
    intro x₀ z ℓ
    funext ⟨i, hi⟩
    revert hi
    refine Fin.cases (fun hi ↦ False.elim (hi rfl)) (fun _ _ ↦ rfl) i
  have hW_cyl : IsCylinderIntersection W := by
    let D : (Fin r × Bool) → Set (∀ p : Fin r × Bool, ContractionSpace X p) := fun p ↦
      if p = (j₀, true) then
        {z | ∀ ℓ : Fin r → Bool, ℓ j₀ = false → φ 0 (view 0 (cubeVertex x₀_arb z ℓ)) = true}
      else if p = (j₀, false) then
        {z | ∀ ℓ : Fin r → Bool, ℓ j₀ = true → φ 0 (view 0 (cubeVertex x₀_arb z ℓ)) = true}
      else Set.univ
    refine ⟨D, ?_, Set.ext fun z ↦ ?_⟩
    · intro p z a
      dsimp only [D]
      split_ifs with hp1 hp2
      · subst hp1
        simp only [Set.mem_ofPred_eq]
        refine forall_congr' fun ℓ ↦ imp_congr_right fun hℓ ↦ ?_
        have heq : view 0 (cubeVertex x₀_arb (Function.update z (j₀, true) a) ℓ) =
            view 0 (cubeVertex x₀_arb z ℓ) := by
          funext ⟨i, hi⟩
          revert hi
          refine Fin.cases (fun hi ↦ False.elim (hi rfl)) (fun j _ ↦ ?_) i
          dsimp only [view, cubeVertex]
          simp only [Fin.cases_succ]
          have hne : (j, ℓ j) ≠ (j₀, true) := by
            intro h
            have h1 : j = j₀ := congrArg Prod.fst h
            have h2 : ℓ j = true := congrArg Prod.snd h
            subst h1; rw [hℓ] at h2; cases h2
          rw [Function.update_of_ne hne]
        rw [heq]
      · subst hp2
        simp only [Set.mem_ofPred_eq]
        refine forall_congr' fun ℓ ↦ imp_congr_right fun hℓ ↦ ?_
        have heq : view 0 (cubeVertex x₀_arb (Function.update z (j₀, false) a) ℓ) =
            view 0 (cubeVertex x₀_arb z ℓ) := by
          funext ⟨i, hi⟩
          revert hi
          refine Fin.cases (fun hi ↦ False.elim (hi rfl)) (fun j _ ↦ ?_) i
          dsimp only [view, cubeVertex]
          simp only [Fin.cases_succ]
          have hne : (j, ℓ j) ≠ (j₀, false) := by
            intro h
            have h1 : j = j₀ := congrArg Prod.fst h
            have h2 : ℓ j = false := congrArg Prod.snd h
            subst h1; rw [hℓ] at h2; cases h2
          rw [Function.update_of_ne hne]
        rw [heq]
      · simp
    · simp only [W, Set.mem_ofPred_eq, Set.mem_iInter, D]
      constructor
      · intro h p
        split_ifs
        · exact fun ℓ _ ↦ h ℓ
        · exact fun ℓ _ ↦ h ℓ
        · exact Set.mem_univ z
      · intro h ℓ
        cases hℓ : ℓ j₀
        · have ht := h (j₀, true)
          simp only [↓reduceIte, Set.mem_ofPred_eq] at ht
          exact ht ℓ hℓ
        · have hf := h (j₀, false)
          simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, ↓reduceIte,
            Set.mem_ofPred_eq] at hf
          exact hf ℓ hℓ
  refine ⟨W, hW_cyl, ?_⟩
  have hstager : ∀ x₀ z, stageIntegrand B φ r x₀ z =
      (∏ ℓ : Fin r → Bool, B (cubeVertex x₀ z ℓ)) * charTensor W z := by
    intro x₀ z
    have hfilt : Finset.univ.filter (fun j : Fin r ↦ r ≤ j.val) = ∅ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_le]; exact j.isLt
    have hvert : ∀ ℓ : Fin r → Bool, stageVertex r x₀ z ℓ = cubeVertex x₀ z ℓ := by
      intro ℓ
      funext i
      refine Fin.cases rfl (fun j ↦ ?_) i
      simp [stageVertex, cubeVertex]
    dsimp only [stageIntegrand]
    simp_rw [hfilt, Finset.prod_empty, mul_one, hvert, hview0_indep]
    rw [Finset.prod_mul_distrib]
    congr 1
    by_cases hm : z ∈ W
    · rw [charTensor_of_mem hm]
      exact Finset.prod_eq_one fun ℓ _ ↦ by simp [boolInd, hm ℓ]
    · rw [charTensor_of_notMem hm]
      obtain ⟨ℓ, hℓ⟩ := not_forall.mp hm
      exact Finset.prod_eq_zero (Finset.mem_univ ℓ) (by simp [boolInd, hℓ])
  simp_rw [hstager]
  rw [Finset.sum_comm]
  simp only [tensorInner_eq_sum, contractionProduct_apply]
  rw [div_eq_inv_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [← Finset.sum_mul]
  ring

/-- **Contraction Inequality**: for any `(r + 1)`-tensor `B` on nonempty finite domains,
`(μ*(B) / size(B))^{2^r} ≤ μ*(B •₁ B) / size(B •₁ B) ≤ 𝔼[|B •₁ B|]`. -/
theorem contraction_inequality [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (B : Tensor X) :
    (muDual B / (tensorSize X : ℝ)) ^ (2 ^ r) ≤
      muDual (contractionProduct B) / (tensorSize (ContractionSpace X) : ℝ) ∧
    muDual (contractionProduct B) / (tensorSize (ContractionSpace X) : ℝ) ≤
      tensorExpectAbs (contractionProduct B) := by
  have hsecond : muDual (contractionProduct B) / (tensorSize (ContractionSpace X) : ℝ) ≤
      tensorExpectAbs (contractionProduct B) := by
    rw [tensorExpectAbs, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (muDual_le_tensorL1 (contractionProduct B)) (by positivity)
  refine ⟨?_, hsecond⟩
  obtain ⟨Z, hZ, hmax⟩ := exists_cylInter_eq_muDual B
  rcases isCylinderIntersection_iff.mp hZ with ⟨φ, rfl⟩
  rw [← hmax]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- Base case `r = 0` (`1` player): `cylinderIntersection φ` is either `∅` or `Set.univ`.
    simp only [pow_zero, pow_one]
    have hcard_C : (tensorSize (ContractionSpace X) : ℝ) = 1 := by
      simp [tensorSize_contractionSpace]
    have hcard_X : (tensorSize X : ℝ) = (Fintype.card (X 0) : ℝ) := by
      simp [tensorSize_eq_prod]
    by_cases hemp : cylinderIntersection φ = ∅
    · rw [hemp]
      have h0 : tensorInner B (charTensor (∅ : Set (∀ i : Fin 1, X i))) = 0 := by
        simp [tensorInner_eq_sum]
      rw [h0, abs_zero, zero_div]
      exact div_nonneg (muDual_nonneg _) (by positivity)
    · have huniv : cylinderIntersection φ = Set.univ := by
        obtain ⟨x₁, hx₁⟩ := Set.nonempty_iff_ne_empty.mpr hemp
        refine Set.eq_univ_of_forall fun x i ↦ ?_
        have hi0 : i = 0 := Fin.eq_zero i
        subst hi0
        have hv : view 0 x = view 0 x₁ := funext fun ⟨j, hj⟩ ↦
          False.elim (hj (Fin.eq_zero j))
        rw [hv]
        exact mem_cylinderIntersection.mp hx₁ 0
      rw [huniv, hcard_C, div_one]
      have hX_pos : (0 : ℝ) < tensorSize X := by exact_mod_cast tensorSize_pos (X := X)
      have hinner_eq : tensorInner B (charTensor (Set.univ : Set (∀ i : Fin 1, X i))) /
          (tensorSize X : ℝ) =
          tensorInner (contractionProduct B)
            (charTensor (Set.univ : Set (∀ p : Fin 0 × Bool, ContractionSpace X p))) := by
        rw [hcard_X, div_eq_inv_mul]
        simp only [tensorInner_eq_sum, contractionProduct_apply]
        conv_rhs => rw [Fintype.sum_unique]
        simp only [charTensor_univ, mul_one, Fintype.prod_unique]
        congr 1
        let e0 : X 0 ≃ (∀ i : Fin 1, X i) :=
          { toFun := fun a i ↦ Fin.cases a (fun j ↦ j.elim0) i
            invFun := fun x ↦ x 0
            left_inv := fun _ ↦ rfl
            right_inv := fun x ↦ by funext i; exact Fin.cases rfl (fun j ↦ j.elim0) i }
        have hsum := e0.sum_comp B
        rw [← hsum]
        rfl
      have habs_div : |tensorInner B (charTensor (Set.univ : Set (∀ i : Fin 1, X i)))| /
          (tensorSize X : ℝ) =
          |tensorInner B (charTensor (Set.univ : Set (∀ i : Fin 1, X i))) /
            (tensorSize X : ℝ)| := by
        rw [abs_div, abs_of_pos hX_pos]
      rw [habs_div, hinner_eq]
      exact abs_tensorInner_charTensor_le_muDual _ isCylinderIntersection_univ
  · -- General case `r ≥ 1`: `r`-step Cauchy–Schwarz induction.
    have hind : ∀ t : ℕ, 1 ≤ t → t ≤ r →
        |tensorInner B (charTensor (cylinderIntersection φ)) / (tensorSize X : ℝ)| ^ (2 ^ t) ≤
        (Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
          ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
            stageIntegrand B φ t x₀ z := by
      intro t ht1 htr
      induction t with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [pow_one, sq_abs, ← stage_zero_eq B φ]
          exact stage_step B φ (by omega)
        · have hprev := ih hk (Nat.le_of_succ_le htr)
          have hstep := stage_step B φ (Nat.lt_of_succ_le htr)
          rw [pow_succ, pow_mul]
          calc (|tensorInner B (charTensor (cylinderIntersection φ)) / (tensorSize X : ℝ)| ^
                  (2 ^ k)) ^ 2
              ≤ ((Fintype.card (X 0) : ℝ)⁻¹ * (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
                  ∑ x₀ : X 0, ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p,
                    stageIntegrand B φ k x₀ z) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hprev 2
            _ ≤ _ := hstep
    have hfinal := hind r hr le_rfl
    obtain ⟨W, hW_cyl, hW_eq⟩ := stage_final_eq hr B φ
    rw [hW_eq] at hfinal
    have hpos_X : (0 : ℝ) < tensorSize X := by exact_mod_cast tensorSize_pos (X := X)
    have hpos_C : (0 : ℝ) < tensorSize (ContractionSpace X) := by
      exact_mod_cast tensorSize_pos (X := ContractionSpace X)
    have habs_div : |tensorInner B (charTensor (cylinderIntersection φ))| / (tensorSize X : ℝ) =
        |tensorInner B (charTensor (cylinderIntersection φ)) / (tensorSize X : ℝ)| := by
      rw [abs_div, abs_of_pos hpos_X]
    rw [habs_div]
    calc |tensorInner B (charTensor (cylinderIntersection φ)) / (tensorSize X : ℝ)| ^ (2 ^ r)
        ≤ tensorInner (contractionProduct B) (charTensor W) /
            (tensorSize (ContractionSpace X) : ℝ) := hfinal
      _ ≤ |tensorInner (contractionProduct B) (charTensor W)| /
            (tensorSize (ContractionSpace X) : ℝ) :=
          div_le_div_of_nonneg_right (le_abs_self _) hpos_C.le
      _ ≤ muDual (contractionProduct B) / (tensorSize (ContractionSpace X) : ℝ) :=
          div_le_div_of_nonneg_right (abs_tensorInner_charTensor_le_muDual _ hW_cyl) hpos_C.le

/-- Corollary of the contraction lemma: `μ*(B)^{2^r} ≤ size(B)^{2^r} · 𝔼[|B •₁ B|]`. -/
theorem muDual_pow_le_size_mul_expectAbs [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (B : Tensor X) :
    muDual B ^ (2 ^ r) ≤
      (tensorSize X : ℝ) ^ (2 ^ r) * tensorExpectAbs (contractionProduct B) := by
  have hpos : (0 : ℝ) < (tensorSize X : ℝ) ^ (2 ^ r) := by
    have : (0 : ℝ) < tensorSize X := by exact_mod_cast tensorSize_pos (X := X)
    positivity
  have h1 := (contraction_inequality B).1.trans (contraction_inequality B).2
  rw [div_pow, div_le_iff₀ hpos] at h1
  rwa [mul_comm] at h1

end Contraction

section HadamardTensors

/-- **Hadamard `k`-tensor**:
a sign `(r + 1)`-tensor `H` such that `(H •₁ H)[z] = 0` whenever `z(j, false) ≠ z(j, true)` for
every `j: Fin r`. -/
def IsHadamardTensor {r : ℕ} {X : Fin (r + 1) → Type*} [Fintype (X 0)] (H : Tensor X) : Prop :=
  IsSignTensor H ∧
    ∀ z : ∀ p : Fin r × Bool, ContractionSpace X p,
      (∀ j : Fin r, z (j, false) ≠ z (j, true)) → contractionProduct H z = 0

/-- Every entry of `H •₁ H` for a sign tensor `H` has absolute value at most `1`. -/
theorem abs_contractionProduct_le_one {r : ℕ} {X : Fin (r + 1) → Type*}
    [Fintype (X 0)] [Nonempty (X 0)] {H : Tensor X} (hH : IsSignTensor H)
    (z : ∀ p : Fin r × Bool, ContractionSpace X p) :
    |contractionProduct H z| ≤ 1 := by
  have hpos : (0 : ℝ) < Fintype.card (X 0) := by exact_mod_cast Fintype.card_pos (α := X 0)
  unfold contractionProduct
  rw [abs_mul, abs_inv, abs_of_pos hpos]
  calc (Fintype.card (X 0) : ℝ)⁻¹ * |∑ x₀ : X 0, ∏ ℓ : Fin r → Bool, H (cubeVertex x₀ z ℓ)|
      ≤ (Fintype.card (X 0) : ℝ)⁻¹ *
          ∑ x₀ : X 0, |∏ ℓ : Fin r → Bool, H (cubeVertex x₀ z ℓ)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = (Fintype.card (X 0) : ℝ)⁻¹ * ∑ _x₀ : X 0, (1 : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl fun x₀ _ ↦ ?_
        rw [Finset.abs_prod]
        exact Finset.prod_eq_one fun ℓ _ ↦ hH.abs_eq_one _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hpos.ne']

/-- **Ford and Gál**:
If `H` is a Hadamard `(r + 1)`-tensor of side length `N` (`1 ≤ r`, `1 ≤ N`), then
`(N / r)^{1 / 2^r} ≤ μ^∞(H)`. -/
theorem hadamardTensor_muInfty_ge {r N : ℕ} (hr : 1 ≤ r) (hN : 1 ≤ N)
    {H : Tensor (fun _ : Fin (r + 1) ↦ Fin N)} (hH : IsHadamardTensor H) :
    ((N : ℝ) / (r : ℝ)) ^ ((2 ^ r : ℝ)⁻¹) ≤ muInfty H := by
  have _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have _ : Nontrivial (Fin (r + 1)) := ⟨⟨0, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  let X : Fin (r + 1) → Type := fun _ ↦ Fin N
 -- Step 1: Take `Q = H` in weak duality for `μ^∞`: `size(H) ≤ μ^∞(H) * μ*(H)`.
  have hHH : ∀ x, 0 ≤ H x * H x := fun x ↦ by rw [hH.1.mul_self x]; norm_num
  have hinner : tensorInner H H = (tensorSize X : ℝ) := by
    simp only [tensorInner_eq_sum, tensorSize_eq_card]
    calc ∑ x : ∀ i : Fin (r + 1), X i, H x * H x
        = ∑ _x : ∀ i : Fin (r + 1), X i, (1 : ℝ) :=
          Finset.sum_congr rfl fun x _ ↦ hH.1.mul_self x
      _ = (Fintype.card (∀ i : Fin (r + 1), X i) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hwd : (tensorSize X : ℝ) ≤ muInfty H * muDual H := by
    have := weak_duality_muInfty hH.1 hHH
    rwa [hinner] at this
 -- Step 2: Union bound `𝔼[|H •₁ H|] ≤ r / N`.
  let badSet : Finset (∀ p : Fin r × Bool, ContractionSpace X p) :=
    Finset.univ.filter fun z ↦ ∃ j : Fin r, z (j, false) = z (j, true)
  have hbad_card : (badSet.card : ℝ) ≤
      (r : ℝ) * ((tensorSize (ContractionSpace X) : ℝ) / (N : ℝ)) := by
    have hsub : badSet ⊆ Finset.univ.biUnion (fun j : Fin r ↦
        Finset.univ.filter fun z : ∀ p : Fin r × Bool, ContractionSpace X p ↦
          z (j, false) = z (j, true)) := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rcases hz.2 with ⟨j, hj⟩
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hj⟩⟩
    have hcard_j : ∀ j : Fin r,
        ((Finset.univ.filter fun z : ∀ p : Fin r × Bool, ContractionSpace X p ↦
          z (j, false) = z (j, true)).card : ℝ) * (N : ℝ) =
        (tensorSize (ContractionSpace X) : ℝ) := by
      intro j
      let S_j := Finset.univ.filter fun z : ∀ p : Fin r × Bool, ContractionSpace X p ↦
        z (j, false) = z (j, true)
      let e : ({z // z ∈ S_j} × Fin N) ≃ (∀ p : Fin r × Bool, ContractionSpace X p) :=
        { toFun := fun p ↦ Function.update p.1.1 (j, true) p.2
          invFun := fun z ↦
            (⟨Function.update z (j, true) (z (j, false)), by
              simp [S_j]⟩, z (j, true))
          left_inv := fun ⟨⟨z, hz⟩, a⟩ ↦ by
            have hzj : z (j, false) = z (j, true) := (Finset.mem_filter.mp hz).2
            ext p
            · by_cases hp : p = (j, true)
              · subst hp; simp [hzj]
              · simp [Function.update_of_ne hp]
            · simp
          right_inv := fun z ↦ by
            funext p
            by_cases hp : p = (j, true)
            · subst hp; simp
            · simp [Function.update_of_ne hp] }
      have hcard_eq := Fintype.card_congr e
      simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hcard_eq
      exact_mod_cast hcard_eq
    have hbi := Finset.card_le_card hsub |>.trans Finset.card_biUnion_le
    have hbiR : (badSet.card : ℝ) ≤ ∑ j : Fin r,
        ((Finset.univ.filter fun z : ∀ p : Fin r × Bool, ContractionSpace X p ↦
          z (j, false) = z (j, true)).card : ℝ) := by exact_mod_cast hbi
    refine hbiR.trans (le_of_eq ?_)
    have hterm : ∀ j : Fin r,
        ((Finset.univ.filter fun z : ∀ p : Fin r × Bool, ContractionSpace X p ↦
          z (j, false) = z (j, true)).card : ℝ) =
        (tensorSize (ContractionSpace X) : ℝ) / (N : ℝ) := fun j ↦ by
      rw [eq_div_iff hNpos.ne']
      exact hcard_j j
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexpect : tensorExpectAbs (contractionProduct H) ≤ (r : ℝ) / (N : ℝ) := by
    have hCpos : (0 : ℝ) < tensorSize (ContractionSpace X) := by
      exact_mod_cast tensorSize_pos (X := ContractionSpace X)
    simp only [tensorExpectAbs_eq_inv_mul_l1, tensorL1_eq_sum]
    have hsum_le : ∑ z : ∀ p : Fin r × Bool, ContractionSpace X p, |contractionProduct H z| ≤
        (badSet.card : ℝ) := by
      calc ∑ z, |contractionProduct H z|
          = ∑ z ∈ badSet, |contractionProduct H z| := by
            symm
            refine Finset.sum_subset (Finset.subset_univ badSet) fun z _ hz ↦ ?_
            have hne : ∀ j : Fin r, z (j, false) ≠ z (j, true) := by
              intro j heq
              exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, j, heq⟩)
            rw [hH.2 z hne, abs_zero]
        _ ≤ ∑ _z ∈ badSet, (1 : ℝ) :=
            Finset.sum_le_sum fun z _ ↦ abs_contractionProduct_le_one hH.1 z
        _ = (badSet.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    calc (tensorSize (ContractionSpace X) : ℝ)⁻¹ * ∑ z, |contractionProduct H z|
        ≤ (tensorSize (ContractionSpace X) : ℝ)⁻¹ * (badSet.card : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ ≤ (tensorSize (ContractionSpace X) : ℝ)⁻¹ *
            ((r : ℝ) * ((tensorSize (ContractionSpace X) : ℝ) / (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hbad_card (by positivity)
      _ = (r : ℝ) / (N : ℝ) := by field_simp [hCpos.ne', hNpos.ne']
 -- Step 3: Combine `(μ*(H)/size(H))^{2^r} ≤ r/N` with `size(H) ≤ μ^∞(H) * μ*(H)`.
  have hcontr := ((contraction_inequality H).1.trans (contraction_inequality H).2).trans hexpect
  have hXpos : (0 : ℝ) < tensorSize X := by exact_mod_cast tensorSize_pos (X := X)
  have hmu_pos : 0 < muInfty H := lt_of_lt_of_le zero_lt_one (one_le_muInfty hH.1)
  have hpow : (N : ℝ) / (r : ℝ) ≤ muInfty H ^ (2 ^ r) := by
    have h1 : (1 : ℝ) ≤ muInfty H * (muDual H / (tensorSize X : ℝ)) := by
      rw [mul_div_assoc', one_le_div hXpos]
      exact hwd
    have h1p : (1 : ℝ) ≤ (muInfty H * (muDual H / (tensorSize X : ℝ))) ^ (2 ^ r) := by
      simpa using pow_le_pow_left₀ zero_le_one h1 (2 ^ r)
    rw [mul_pow] at h1p
    have h2 : (1 : ℝ) ≤ muInfty H ^ (2 ^ r) * ((r : ℝ) / (N : ℝ)) :=
      h1p.trans (mul_le_mul_of_nonneg_left hcontr (by positivity))
    rw [div_le_iff₀ hrpos]
    have h3 := mul_le_mul_of_nonneg_right h2 hNpos.le
    have h4 : muInfty H ^ (2 ^ r) * ((r : ℝ) / (N : ℝ)) * (N : ℝ) =
        muInfty H ^ (2 ^ r) * (r : ℝ) := by field_simp [hNpos.ne']
    linarith
  have h2r_pos : (0 : ℝ) < (2 ^ r : ℝ) := by positivity
  calc ((N : ℝ) / (r : ℝ)) ^ ((2 ^ r : ℝ)⁻¹)
      ≤ (muInfty H ^ (2 ^ r)) ^ ((2 ^ r : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (muInfty H ^ ((2 ^ r : ℕ) : ℝ)) ^ ((2 ^ r : ℝ)⁻¹) := by
        rw [Real.rpow_natCast]
    _ = muInfty H := by
        rw [← Real.rpow_mul hmu_pos.le]
        push_cast
        rw [mul_inv_cancel₀ h2r_pos.ne', Real.rpow_one]

/-- **Warmup Hadamard Matrix Bound**:
For any `N × N` Hadamard matrix `H` (`r = 1`), `√N ≤ μ^∞(H)`. -/
theorem hadamard_matrix_muInfty_ge_sqrt {N : ℕ} (hN : 1 ≤ N)
    {H : Tensor (fun _ : Fin 2 ↦ Fin N)} (hH : IsHadamardTensor H) :
    Real.sqrt (N : ℝ) ≤ muInfty H := by
  have hfg := hadamardTensor_muInfty_ge (r := 1) (N := N) le_rfl hN hH
  simpa [Real.sqrt_eq_rpow] using hfg

/-- Concrete `2 × 2` Sylvester Hadamard matrix `H₂` (`1, 1; 1, -1`) as a non-vacuity witness for
`IsHadamardTensor` and `hadamard_matrix_muInfty_ge_sqrt`. -/
def sylvesterHadamard2 : Tensor (fun _ : Fin 2 ↦ Fin 2) :=
  fun x ↦ if x 0 = 1 ∧ x 1 = 1 then -1 else 1

/-- Non-vacuity witness: `sylvesterHadamard2` is a `2 × 2` Hadamard tensor. -/
theorem isHadamardTensor_sylvesterHadamard2 : IsHadamardTensor sylvesterHadamard2 := by
  refine ⟨fun x ↦ ?_, fun z hz ↦ ?_⟩
  · unfold sylvesterHadamard2
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have hne : z (0, false) ≠ z (0, true) := hz 0
    unfold contractionProduct
    have hsum : ∑ x₀ : Fin 2, ∏ ℓ : Fin 1 → Bool,
        sylvesterHadamard2 (cubeVertex x₀ z ℓ) = 0 := by
      rw [Fin.sum_univ_two]
      have hprod : ∀ x₀ : Fin 2,
          ∏ ℓ : Fin 1 → Bool, sylvesterHadamard2 (cubeVertex x₀ z ℓ) =
          sylvesterHadamard2 (Fin.cases x₀ (fun _ ↦ z (0, false))) *
          sylvesterHadamard2 (Fin.cases x₀ (fun _ ↦ z (0, true))) := by
        intro x₀
        let e1 : Bool ≃ (Fin 1 → Bool) :=
          { toFun := fun b _ ↦ b
            invFun := fun ℓ ↦ ℓ 0
            left_inv := fun _ ↦ rfl
            right_inv := fun ℓ ↦ funext fun i ↦ by rw [Fin.eq_zero i] }
        rw [← e1.prod_comp, Fintype.prod_bool, mul_comm]
        rfl
      have hval : ∀ u v : Fin 2,
          sylvesterHadamard2 (Fin.cases u (fun _ ↦ v)) = if u = 1 ∧ v = 1 then -1 else 1 :=
        fun _ _ ↦ rfl
      rw [hprod 0, hprod 1, hval, hval, hval, hval]
      generalize hz0 : z (0, false) = a
      generalize hz1 : z (0, true) = b
      rw [hz0, hz1] at hne
      fin_cases a <;> fin_cases b <;> simp_all
    rw [hsum, mul_zero]

end HadamardTensors

end CslibFrontier.Computability.Communication.NOF
