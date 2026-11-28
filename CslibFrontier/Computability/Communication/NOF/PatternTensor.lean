/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Contraction
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.DualPolynomial
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiparty Pattern Tensors and Approximate-Degree Lifting

This module defines `(r + 1)`-party pattern tensors `patternTensor` and `normalizedPatternTensor`,
establishes the uniform fiber law preserving `ℓ₁` norms and inner products, bounds the contraction
expectation and dual cylinder intersection norm of normalized pattern tensors built from functions
with vanishing low-degree Fourier coefficients, and proves general approximate-degree and
threshold-degree lifting theorems to the multiparty norms `muAlpha` and `muInfty`.

## Main definitions

* `PatternSpace`, `patternProj`, `patternTensor`, `normalizedPatternTensor`: domain, projection,
  and normalized multiparty pattern tensors.

## Main results

* `sum_comp_patternProj`, `tensorL1_normalizedPatternTensor`,
  `tensorInner_patternTensor_normalized`: uniform fiber law and norm/inner-product preservation.
* `patternTensor_contraction_expectAbs_le`, `patternTensor_muDual_rpow_le`: contraction expectation
  and dual-norm upper bounds `μ*(A) ≤ 2^{-d / 2^r}`.
* `muAlpha_patternTensor_ge_exp`, `logb_muAlpha_patternTensor_ge`, `muInfty_patternTensor_ge_exp`,
  `logb_muInfty_patternTensor_ge`: approximate-degree and threshold-degree lifting theorems for
  `μ^α` and `μ^∞`.
-/

public section

open scoped BigOperators
open Cslib Cslib.BitString Cslib.Communication.NOF

open CslibFrontier.Computability.QueryComplexity
namespace CslibFrontier.Computability.Communication.NOF

section PatternTensorDefs

/-- The `(r + 1)`-party domain of a `(k = r + 1, M, φ)` pattern tensor:
player `0` holds `x : Fin m → (Fin r → Fin M) → Bool`, and each player
`j.succ` (`j: Fin r`) holds a selector vector `y_j: Fin m → Fin M`. -/
@[expose] def PatternSpace (r m M : ℕ) (p : Fin (r + 1)) : Type :=
  Fin.cases (Fin m → (Fin r → Fin M) → Bool) (fun _ ↦ Fin m → Fin M) p

/-- Equivalence identifying `PatternSpace r m M 0` with `Fin m → (Fin r → Fin M) → Bool`. -/
@[expose] def patternPlayer0Equiv (r m M : ℕ) :
    PatternSpace r m M 0 ≃ (Fin m → (Fin r → Fin M) → Bool) :=
  Equiv.refl _

/-- Equivalence identifying `PatternSpace r m M j.succ` with `Fin m → Fin M`. -/
@[expose] def patternSuccEquiv (r m M : ℕ) (j : Fin r) :
    PatternSpace r m M j.succ ≃ (Fin m → Fin M) :=
  Equiv.refl _

/-- `Fintype` instance for each player's domain in `PatternSpace r m M`. -/
instance instFintypePatternSpace (r m M : ℕ) (p : Fin (r + 1)) :
    Fintype (PatternSpace r m M p) :=
  Fin.cases
    (inferInstance : Fintype (Fin m → (Fin r → Fin M) → Bool))
    (fun _ ↦ (inferInstance : Fintype (Fin m → Fin M))) p

/-- `Nonempty` instance for `PatternSpace r m M` when `M > 0`. -/
instance instNonemptyPatternSpace (r m M : ℕ) [NeZero M] (p : Fin (r + 1)) :
    Nonempty (PatternSpace r m M p) :=
  Fin.cases
    (inferInstance : Nonempty (Fin m → (Fin r → Fin M) → Bool))
    (fun _ ↦ (inferInstance : Nonempty (Fin m → Fin M))) p

/-- Selector `y_j[i] ∈ Fin M` extracted from player `j.succ`'s input in `PatternSpace`. -/
@[expose] def patternSelector {r m M : ℕ} (z : ∀ p : Fin (r + 1), PatternSpace r m M p)
    (j : Fin r) (i : Fin m) : Fin M :=
  patternSuccEquiv r m M j (z j.succ) i

/-- Evaluation of the pattern selector at player `j.succ` and block `i`. -/
theorem patternSelector_eq {r m M : ℕ} (z : ∀ p : Fin (r + 1), PatternSpace r m M p)
    (j : Fin r) (i : Fin m) :
    patternSelector z j i = patternSuccEquiv r m M j (z j.succ) i := rfl

/-- **Pattern projection** `patternProj z: BitString m`):
`(patternProj z) i = x^i[y_1[i], …, y_r[i]]`. -/
@[expose] def patternProj {r m M : ℕ} (z : ∀ p : Fin (r + 1), PatternSpace r m M p) : BitString m :=
  fun i ↦ patternPlayer0Equiv r m M (z 0) i (fun j ↦ patternSelector z j i)

/-- **Pattern tensor `A_{k, M, φ}`**):
`A_{k, M, φ}[x, y_1, …, y_{k-1}] = φ(patternProj (x, y))`. -/
@[expose] def patternTensor (r m M : ℕ) (φ : BitString m → ℝ) : Tensor (PatternSpace r m M) :=
  fun z ↦ φ (patternProj z)

/-- **Normalized pattern tensor** `(2^m / size(A)) · A_{k, M, φ}`. -/
noncomputable def normalizedPatternTensor (r m M : ℕ) (φ : BitString m → ℝ) :
    Tensor (PatternSpace r m M) :=
  fun z ↦ ((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) * φ (patternProj z)

/-- The size of `PatternSpace r m M` equals `2^{m M^r} · M^{m r}`. -/
theorem tensorSize_patternSpace (r m M : ℕ) :
    tensorSize (PatternSpace r m M) = 2 ^ (m * M ^ r) * M ^ (m * r) := by
  rw [tensorSize_eq_prod, Fin.prod_univ_succ]
  have h0 : Fintype.card (PatternSpace r m M 0) = 2 ^ (m * M ^ r) := by
    rw [Fintype.card_congr (patternPlayer0Equiv r m M)]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm]
  have hs : ∀ j : Fin r, Fintype.card (PatternSpace r m M j.succ) = M ^ m := fun j ↦ by
    rw [Fintype.card_congr (patternSuccEquiv r m M j)]
    simp [Fintype.card_fin]
  simp_rw [h0, hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- **Uniform Fiber Law**:
every `w: BitString m` appears as `patternProj z` an equal number of times, so
`∑ z, g (patternProj z) = (size(PatternSpace) / 2^m) * ∑ w, g w`. -/
theorem sum_comp_patternProj {r m M : ℕ} (hM : 0 < M) (g : BitString m → ℝ) :
    ∑ z : ∀ p : Fin (r + 1), PatternSpace r m M p, g (patternProj z) =
      ((tensorSize (PatternSpace r m M) : ℝ) / (2 : ℝ) ^ m) * ∑ w : BitString m, g w := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
 -- For any fixed selector tuple `y`, XORing the selected entry of `x 0` bijects fibers.
  let eSplit : (∀ p : Fin (r + 1), PatternSpace r m M p) ≃
      ((Fin m → (Fin r → Fin M) → Bool) × (Fin r → Fin m → Fin M)) :=
    { toFun := fun z ↦
        (patternPlayer0Equiv r m M (z 0), fun j ↦ patternSuccEquiv r m M j (z j.succ))
      invFun := fun p q ↦ Fin.cases p.1 (fun j ↦ p.2 j) q
      left_inv := fun z ↦ by
        funext q
        refine Fin.cases rfl (fun _ ↦ rfl) q
      right_inv := fun ⟨x, y⟩ ↦ by ext <;> rfl }
  have hfiber : ∀ (y : Fin r → Fin m → Fin M) (w : BitString m),
      ∑ x : Fin m → (Fin r → Fin M) → Bool,
        (if (fun i ↦ x i (fun j ↦ y j i)) = w then (1 : ℝ) else 0) =
      ((2 : ℝ) ^ (m * M ^ r)) / (2 : ℝ) ^ m := by
    intro y w
 -- Shifting `x i t` by `xor (w₁ i) (w₂ i)` at `t = fun j ↦ y j i` bijects all fibers.
    have heq_fiber : ∀ w₁ w₂ : BitString m,
        ∑ x : Fin m → (Fin r → Fin M) → Bool,
          (if (fun i ↦ x i (fun j ↦ y j i)) = w₁ then (1 : ℝ) else 0) =
        ∑ x : Fin m → (Fin r → Fin M) → Bool,
          (if (fun i ↦ x i (fun j ↦ y j i)) = w₂ then (1 : ℝ) else 0) := by
      intro w₁ w₂
      let eShift : (Fin m → (Fin r → Fin M) → Bool) ≃ (Fin m → (Fin r → Fin M) → Bool) :=
        { toFun := fun x i t ↦ if t = fun j ↦ y j i then xor (x i t) (xor (w₁ i) (w₂ i)) else x i t
          invFun := fun x i t ↦ if t = fun j ↦ y j i then xor (x i t) (xor (w₁ i) (w₂ i)) else x i t
          left_inv := fun x ↦ by
            funext i t
            dsimp only
            split_ifs
            · cases x i t <;> cases w₁ i <;> cases w₂ i <;> rfl
            · rfl
          right_inv := fun x ↦ by
            funext i t
            dsimp only
            split_ifs
            · cases x i t <;> cases w₁ i <;> cases w₂ i <;> rfl
            · rfl }
      rw [← eShift.sum_comp]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hiff : ((fun i ↦ (eShift x) i (fun j ↦ y j i)) = w₁) ↔
          ((fun i ↦ x i (fun j ↦ y j i)) = w₂) := by
        simp only [funext_iff, eShift, Equiv.coe_fn_mk]
        refine forall_congr' fun i ↦ ?_
        cases x i (fun j ↦ y j i) <;> cases w₁ i <;> cases w₂ i <;> simp
      by_cases h : (fun i ↦ x i (fun j ↦ y j i)) = w₂
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hm ↦ h (hiff.mp hm)), ite_eq_right h]
    have hsum_all : ∑ w' : BitString m,
        ∑ x : Fin m → (Fin r → Fin M) → Bool,
          (if (fun i ↦ x i (fun j ↦ y j i)) = w' then (1 : ℝ) else 0) =
        (2 : ℝ) ^ (m * M ^ r) := by
      rw [Finset.sum_comm]
      have hinner : ∀ x : Fin m → (Fin r → Fin M) → Bool,
          ∑ w' : BitString m, (if (fun i ↦ x i (fun j ↦ y j i)) = w' then (1 : ℝ) else 0) = 1 := by
        intro x
        rw [Finset.sum_ite_eq Finset.univ (fun i ↦ x i (fun j ↦ y j i))]
        simp
      simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring_nf
    have hconst : ∑ w' : BitString m,
        ∑ x : Fin m → (Fin r → Fin M) → Bool,
          (if (fun i ↦ x i (fun j ↦ y j i)) = w' then (1 : ℝ) else 0) =
        (2 : ℝ) ^ m * ∑ x : Fin m → (Fin r → Fin M) → Bool,
          (if (fun i ↦ x i (fun j ↦ y j i)) = w then (1 : ℝ) else 0) := by
      have hc : ∀ w' : BitString m,
          ∑ x : Fin m → (Fin r → Fin M) → Bool,
            (if (fun i ↦ x i (fun j ↦ y j i)) = w' then (1 : ℝ) else 0) =
          ∑ x : Fin m → (Fin r → Fin M) → Bool,
            (if (fun i ↦ x i (fun j ↦ y j i)) = w then (1 : ℝ) else 0) := fun w' ↦ heq_fiber w' w
      simp_rw [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [eq_div_iff h2m_pos.ne', mul_comm]
    linarith
  calc ∑ z : ∀ p : Fin (r + 1), PatternSpace r m M p, g (patternProj z)
      = ∑ p : (Fin m → (Fin r → Fin M) → Bool) × (Fin r → Fin m → Fin M),
          g (fun i ↦ p.1 i (fun j ↦ p.2 j i)) := by
        rw [← eSplit.symm.sum_comp]
        refine Finset.sum_congr rfl fun ⟨x, y⟩ _ ↦ rfl
    _ = ∑ y : Fin r → Fin m → Fin M, ∑ x : Fin m → (Fin r → Fin M) → Bool,
          g (fun i ↦ x i (fun j ↦ y j i)) := by
        rw [Fintype.sum_prod_type_right]
    _ = ∑ y : Fin r → Fin m → Fin M, ∑ w : BitString m,
          g w * ∑ x : Fin m → (Fin r → Fin M) → Bool,
            (if (fun i ↦ x i (fun j ↦ y j i)) = w then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        have hpart : ∀ x : Fin m → (Fin r → Fin M) → Bool,
            g (fun i ↦ x i (fun j ↦ y j i)) =
            ∑ w : BitString m, g w * (if (fun i ↦ x i (fun j ↦ y j i)) = w then 1 else 0) := by
          intro x
          rw [Finset.sum_eq_single (fun i ↦ x i (fun j ↦ y j i))]
          · simp
          · intro w _ hne; simp [Ne.symm hne]
          · intro h; exact (h (Finset.mem_univ _)).elim
        simp_rw [hpart]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ ↦ (Finset.mul_sum _ _ _).symm
    _ = ∑ _y : Fin r → Fin m → Fin M,
          (((2 : ℝ) ^ (m * M ^ r)) / (2 : ℝ) ^ m) * ∑ w : BitString m, g w := by
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        simp_rw [hfiber y, ← Finset.sum_mul, mul_comm]
    _ = ((tensorSize (PatternSpace r m M) : ℝ) / (2 : ℝ) ^ m) * ∑ w : BitString m, g w := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
          tensorSize_patternSpace]
        push_cast
        rw [← pow_mul]
        ring

/-- `‖normalizedPatternTensor r m M φ‖₁ = ‖φ‖₁`. -/
theorem tensorL1_normalizedPatternTensor {r m M : ℕ} (hM : 0 < M) (φ : BitString m → ℝ) :
    tensorL1 (normalizedPatternTensor r m M φ) = boolL1 φ := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have hpos_sz : (0 : ℝ) < tensorSize (PatternSpace r m M) := by
    exact_mod_cast tensorSize_pos (X := PatternSpace r m M)
  have hpos_2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [tensorL1_eq_sum, boolL1_eq_sum]; unfold normalizedPatternTensor
  have habs : ∀ z : ∀ p : Fin (r + 1), PatternSpace r m M p,
      |((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) * φ (patternProj z)| =
      ((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) * |φ (patternProj z)| := fun z ↦ by
    rw [abs_mul, abs_of_pos (div_pos hpos_2m hpos_sz)]
  simp_rw [habs, ← Finset.mul_sum, sum_comp_patternProj hM (fun w ↦ |φ w|)]
  field_simp [hpos_sz.ne', hpos_2m.ne']

/-- `⟨patternTensor r m M (signVal ∘ f), normalizedPatternTensor r m M φ⟩ = ⟨φ, f⟩`. -/
theorem tensorInner_patternTensor_normalized {r m M : ℕ} (hM : 0 < M)
    (f : BitString m → Bool) (φ : BitString m → ℝ) :
    tensorInner (patternTensor r m M (fun w ↦ signVal (f w)))
      (normalizedPatternTensor r m M φ) = boolInner φ f := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have hpos_sz : (0 : ℝ) < tensorSize (PatternSpace r m M) := by
    exact_mod_cast tensorSize_pos (X := PatternSpace r m M)
  have hpos_2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [tensorInner_eq_sum, boolInner_eq_sum]; unfold patternTensor normalizedPatternTensor
  have hterm : ∀ z : ∀ p : Fin (r + 1), PatternSpace r m M p,
      signVal (f (patternProj z)) *
        (((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) * φ (patternProj z)) =
      ((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) *
        (φ (patternProj z) * signVal (f (patternProj z))) := fun z ↦ by ring
  simp_rw [hterm, ← Finset.mul_sum,
    sum_comp_patternProj hM (fun w ↦ φ w * signVal (f w))]
  field_simp [hpos_sz.ne', hpos_2m.ne']

end PatternTensorDefs

section MainPatternLemma

/-- Elementary Stirling-type lower bound `2 * (g / e)^g ≤ g!` for all `1 ≤ g`, yielding
`m.choose g ≤ (1/2) * (e * m / d)^g` and the exact `2e` threshold constant. -/
theorem two_mul_div_exp_pow_le_factorial {g : ℕ} (hg : 1 ≤ g) :
    2 * ((g : ℝ) / Real.exp 1) ^ g ≤ (g.factorial : ℝ) := by
  induction g with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.reduceAdd, Nat.cast_one, pow_one, Nat.factorial_one]
      have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      rw [mul_one_div, div_le_one (Real.exp_pos 1)]
      exact he.le
    · have hprev := ih hk
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
 -- `((k + 1) / k)^k = (1 + 1/k)^k ≤ exp(1)`:
      have hstep : (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k ≤ Real.exp 1 := by
        have h1 : ((k + 1 : ℕ) : ℝ) / (k : ℝ) = 1 + (k : ℝ)⁻¹ := by
          push_cast; field_simp [hk_pos.ne']
        rw [h1]
        calc (1 + (k : ℝ)⁻¹) ^ k ≤ (Real.exp ((k : ℝ)⁻¹)) ^ k :=
              pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((k : ℝ)⁻¹)]) k
          _ = Real.exp ((k : ℝ) * (k : ℝ)⁻¹) := by rw [← Real.exp_nat_mul]
          _ = Real.exp 1 := by rw [mul_inv_cancel₀ hk_pos.ne']
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      have hident : 2 * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ k * (((k + 1 : ℕ) : ℝ) / Real.exp 1) =
          ((k + 1 : ℕ) : ℝ) * (2 * ((k : ℝ) / Real.exp 1) ^ k) *
            (((((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k) / Real.exp 1) := by
        rw [div_pow, div_pow, div_pow]
        field_simp [hk_pos.ne', hexp_pos.ne']
      rw [← mul_assoc, hident]
      have hratio : ((((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k) / Real.exp 1 ≤ 1 := by
        rw [div_le_one hexp_pos]; exact hstep
      calc ((k + 1 : ℕ) : ℝ) * (2 * ((k : ℝ) / Real.exp 1) ^ k) *
              (((((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k) / Real.exp 1)
          ≤ ((k + 1 : ℕ) : ℝ) * (2 * ((k : ℝ) / Real.exp 1) ^ k) * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = ((k + 1 : ℕ) : ℝ) * (2 * ((k : ℝ) / Real.exp 1) ^ k) := mul_one _
        _ ≤ ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left hprev (by positivity)

/-- Consequence of `two_mul_div_exp_pow_le_factorial`:
`m.choose g ≤ (1 / 2) * (e * m / d)^g` whenever `1 ≤ d ≤ g`. -/
private theorem choose_le_half_exp_pow {m g d : ℕ} (hd : 1 ≤ d) (hdg : d ≤ g) :
    (m.choose g : ℝ) ≤ (1 / 2 : ℝ) * (Real.exp 1 * (m : ℝ) / (d : ℝ)) ^ g := by
  have hg1 : 1 ≤ g := le_trans hd hdg
  have hg_pos : (0 : ℝ) < g := by exact_mod_cast hg1
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hfac_pos : (0 : ℝ) < g.factorial := by exact_mod_cast Nat.factorial_pos g
  have hdesc : (m.choose g : ℝ) * (g.factorial : ℝ) ≤ (m : ℝ) ^ g := by
    have hnat : m.choose g * g.factorial ≤ m ^ g := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow m g
    exact_mod_cast hnat
  have hstirl := two_mul_div_exp_pow_le_factorial hg1
  have hle_g : (m.choose g : ℝ) ≤ (1 / 2 : ℝ) * (Real.exp 1 * (m : ℝ) / (g : ℝ)) ^ g := by
    have h1 : (m.choose g : ℝ) * (2 * ((g : ℝ) / Real.exp 1) ^ g) ≤ (m : ℝ) ^ g :=
      (mul_le_mul_of_nonneg_left hstirl (by positivity)).trans hdesc
    have hpow_pos : (0 : ℝ) < 2 * ((g : ℝ) / Real.exp 1) ^ g := by positivity
    rw [← le_div_iff₀ hpow_pos] at h1
    refine h1.trans (le_of_eq ?_)
    rw [div_pow, div_pow, mul_pow]
    field_simp [hg_pos.ne', (Real.exp_pos 1).ne']
  refine hle_g.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine pow_le_pow_left₀ (by positivity) ?_ g
  exact div_le_div_of_nonneg_left (by positivity) hd_pos (by exact_mod_cast hdg)

/-- Monotonicity of finite real products with nonnegative factors. -/
private theorem prod_le_prod_nonneg {α : Type*} {s : Finset α} {f g : α → ℝ}
    (hf : ∀ a ∈ s, 0 ≤ f a) (hfg : ∀ a ∈ s, f a ≤ g a) :
    ∏ a ∈ s, f a ≤ ∏ a ∈ s, g a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hfg a (Finset.mem_insert_self a s)
    have hfs : ∀ x ∈ s, 0 ≤ f x := fun x hx ↦ hf x (Finset.mem_insert_of_mem hx)
    have hprod_nn : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg hfs
    exact mul_le_mul hga (ih hfs (fun x hx ↦ hfg x (Finset.mem_insert_of_mem hx)))
      hprod_nn (le_trans hfa hga)

/-- Single-block cube vanishing:
if `pt: (Fin r → Bool) → (Fin r → Fin M)` is injective and `S: Finset (Fin r → Bool)` is
nonempty, then `∑ b: (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal (b (pt ℓ)) = 0`. -/
private theorem sum_prod_signVal_eq_zero_of_injective {r M : ℕ}
    {pt : (Fin r → Bool) → (Fin r → Fin M)} (hinj : Function.Injective pt)
    {S : Finset (Fin r → Bool)} (hS : S.Nonempty) :
    ∑ b : (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal (b (pt ℓ)) = 0 := by
  obtain ⟨ℓ₀, hℓ₀⟩ := hS
  let u₀ := pt ℓ₀
  let flip : ((Fin r → Fin M) → Bool) ≃ ((Fin r → Fin M) → Bool) :=
    { toFun := fun b u ↦ if u = u₀ then !b u else b u
      invFun := fun b u ↦ if u = u₀ then !b u else b u
      left_inv := fun b ↦ by funext u; dsimp only; split_ifs <;> simp
      right_inv := fun b ↦ by funext u; dsimp only; split_ifs <;> simp }
  have hneg : ∀ b : (Fin r → Fin M) → Bool,
      ∏ ℓ ∈ S, signVal ((flip b) (pt ℓ)) = -(∏ ℓ ∈ S, signVal (b (pt ℓ))) := by
    intro b
    rw [← Finset.mul_prod_erase S _ hℓ₀, ← Finset.mul_prod_erase S _ hℓ₀]
    have h0 : signVal ((flip b) (pt ℓ₀)) = -signVal (b (pt ℓ₀)) := by
      simp [flip, u₀, signVal_not]
    have hrest : ∏ ℓ ∈ S.erase ℓ₀, signVal ((flip b) (pt ℓ)) =
        ∏ ℓ ∈ S.erase ℓ₀, signVal (b (pt ℓ)) := by
      refine Finset.prod_congr rfl fun ℓ hℓ ↦ ?_
      have hne : pt ℓ ≠ u₀ := fun h ↦ (Finset.mem_erase.mp hℓ).1 (hinj h)
      simp [flip, hne]
    rw [h0, hrest, neg_mul]
  have hsum_neg : ∑ b : (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal (b (pt ℓ)) =
      -(∑ b : (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal (b (pt ℓ))) := by
    calc ∑ b : (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal (b (pt ℓ))
        = ∑ b : (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal ((flip b) (pt ℓ)) :=
          (flip.sum_comp (fun b ↦ ∏ ℓ ∈ S, signVal (b (pt ℓ)))).symm
      _ = ∑ b : (Fin r → Fin M) → Bool, -(∏ ℓ ∈ S, signVal (b (pt ℓ))) :=
          Finset.sum_congr rfl fun b _ ↦ hneg b
      _ = -(∑ b : (Fin r → Fin M) → Bool, ∏ ℓ ∈ S, signVal (b (pt ℓ))) := by
          rw [Finset.sum_neg_distrib]
  linarith

/-- **Pattern-tensor contraction expectation bound**:
for `A = normalizedPatternTensor r m M φ` with `‖φ‖₁ = 1`, `φ̂(T) = 0` for all
`|T| < d` (`1 ≤ d`), `0 < M`, and `M ≥ 2 e r 2^{2^r} m / d`,
`𝔼[|A •₁ A|] ≤ 2^{-d} / size(A)^{2^r}`. -/
theorem patternTensor_contraction_expectAbs_le {r m M d : ℕ} (hd : 1 ≤ d) (hM : 0 < M)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) / (d : ℝ) ≤ (M : ℝ))
    {φ : BitString m → ℝ} (hL1 : boolL1 φ = 1)
    (hvanish : ∀ T : Finset (Fin m), T.card < d → BitString.fourierCoeff φ T = 0) :
    tensorExpectAbs (contractionProduct (normalizedPatternTensor r m M φ)) ≤
      ((2 : ℝ)⁻¹ ^ d) / (tensorSize (PatternSpace r m M) : ℝ) ^ (2 ^ r) := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let A := normalizedPatternTensor r m M φ
  let sz : ℝ := (tensorSize (PatternSpace r m M) : ℝ)
  have hsz_pos : 0 < sz := by
    dsimp only [sz]
    exact_mod_cast tensorSize_pos (X := PatternSpace r m M)
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
 -- Bound `c * |φ̂(T)| ≤ sz⁻¹` for every `T`:
  have hcoeff_le : ∀ T : Finset (Fin m),
      ((2 : ℝ) ^ m / sz) * |BitString.fourierCoeff φ T| ≤ sz⁻¹ := by
    intro T
    rw [BitString.fourierCoeff_eq_sum]
    simp only [Fintype.card_fin]
    have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [abs_div, abs_of_pos h2m_pos]
    have hsum_le : |∑ x : BitString m, φ x * chi ℝ T x| ≤ 1 := by
      calc |∑ x : BitString m, φ x * chi ℝ T x|
          ≤ ∑ x : BitString m, |φ x * chi ℝ T x| := Finset.abs_sum_le_sum_abs _ _
        _ = boolL1 φ := Finset.sum_congr rfl fun x _ ↦ by rw [abs_mul, abs_chi, mul_one]
        _ = 1 := hL1
    calc ((2 : ℝ) ^ m / sz) * (|∑ x : BitString m, φ x * chi ℝ T x| / (2 : ℝ) ^ m)
        = |∑ x : BitString m, φ x * chi ℝ T x| / sz := by field_simp [h2m_pos.ne', hsz_pos.ne']
      _ ≤ 1 / sz := div_le_div_of_nonneg_right hsum_le hsz_pos.le
      _ = sz⁻¹ := one_div sz
 -- Define degenerate block set for `z`:
  let degenSet : (∀ p : Fin r × Bool, ContractionSpace (PatternSpace r m M) p) → Finset (Fin m) :=
    fun z ↦ Finset.univ.filter fun i : Fin m ↦
      ∃ j : Fin r, patternSuccEquiv r m M j (z (j, false)) i =
        patternSuccEquiv r m M j (z (j, true)) i
 -- Step 1: Pointwise bound on `|contractionProduct A z|`:
  have hpoint : ∀ z : ∀ p : Fin r × Bool, ContractionSpace (PatternSpace r m M) p,
      |contractionProduct A z| ≤
        (sz ^ (2 ^ r))⁻¹ *
          if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0 := by
    intro z
    let pt : Fin m → (Fin r → Bool) → (Fin r → Fin M) :=
      fun i ℓ j ↦ patternSuccEquiv r m M j (z (j, ℓ j)) i
    have hA_expand : ∀ (x₀ : PatternSpace r m M 0) (ℓ : Fin r → Bool),
        A (cubeVertex x₀ z ℓ) =
          ∑ T : Finset (Fin m), (((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ T) *
            ∏ i ∈ T, signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)) := by
      intro x₀ ℓ
      dsimp only [A, normalizedPatternTensor]
      rw [← sum_fourierCoeff_mul_chi φ (patternProj (cubeVertex x₀ z ℓ)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      rw [chi_eq_prod_signVal, ← mul_assoc]
      congr 1
 -- Expand `contractionProduct A z` over tuples `T: (Fin r → Bool) → Finset (Fin m)`:
    have hcard0_pos : (0 : ℝ) < Fintype.card (PatternSpace r m M 0) := by
      exact_mod_cast Fintype.card_pos (α := PatternSpace r m M 0)
    have hcontr_eq : contractionProduct A z =
        ∑ T : (Fin r → Bool) → Finset (Fin m),
          (∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
          ((Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
            ∑ x₀ : PatternSpace r m M 0,
              ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))) := by
      rw [contractionProduct_apply]
      simp_rw [hA_expand, Fintype.prod_sum]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      have hterm : ∀ x₀ : PatternSpace r m M 0,
          ∏ ℓ : Fin r → Bool,
            (((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
              ∏ i ∈ T ℓ, signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)) =
          (∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
            ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
              signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)) := by
        intro x₀
        rw [Finset.prod_mul_distrib]
        congr 1
        have hswap : ∀ ℓ : Fin r → Bool,
            ∏ i ∈ T ℓ, signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)) =
            ∏ i : Fin m, if i ∈ T ℓ then signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)) else 1 :=
          fun ℓ ↦ by rw [← Finset.prod_filter]; congr 1; ext i; simp
        simp_rw [hswap]
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [← Finset.prod_filter]
      simp_rw [hterm, ← Finset.mul_sum]
      ring
 -- Factor the expectation over `x₀` across `i: Fin m`:
    have hfactor_x0 : ∀ T : (Fin r → Bool) → Finset (Fin m),
        (Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
          ∑ x₀ : PatternSpace r m M 0,
            ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
              signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)) =
        ∏ i : Fin m,
          ((Fintype.card ((Fin r → Fin M) → Bool) : ℝ)⁻¹ *
            ∑ b : (Fin r → Fin M) → Bool,
              ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ), signVal (b (pt i ℓ))) := by
      intro T
      rw [(patternPlayer0Equiv r m M).sum_comp (fun y ↦
        ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ), signVal (y i (pt i ℓ)))]
      rw [Fintype.card_congr (patternPlayer0Equiv r m M), Fintype.card_fun, Fintype.card_fin]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_pow, inv_pow]
      congr 1
      exact (Fintype.prod_sum (fun (i : Fin m) (b : (Fin r → Fin M) → Bool) ↦
        ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ), signVal (b (pt i ℓ)))).symm
 -- Define the surviving tuple set: `∀ ℓ, d ≤ (T ℓ).card ∧ T ℓ ⊆ degenSet z`.
    let goodTuples : Finset ((Fin r → Bool) → Finset (Fin m)) :=
      Finset.univ.filter fun T ↦ ∀ ℓ : Fin r → Bool, d ≤ (T ℓ).card ∧ T ℓ ⊆ degenSet z
    have hvanish_outside : ∀ T : (Fin r → Bool) → Finset (Fin m), T ∉ goodTuples →
        (∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
          ((Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
            ∑ x₀ : PatternSpace r m M 0,
              ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))) = 0 := by
      intro T hT
      simp only [goodTuples, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hT
      obtain ⟨ℓ₀, hℓ₀⟩ := hT
      by_cases hcard : d ≤ (T ℓ₀).card
      · have hnsub : ¬ T ℓ₀ ⊆ degenSet z := fun hs ↦ hℓ₀ ⟨hcard, hs⟩
        rw [Finset.not_subset] at hnsub
        obtain ⟨i₀, hi₀T, hi₀D⟩ := hnsub
        rw [hfactor_x0 T]
        suffices hzero : (Fintype.card ((Fin r → Fin M) → Bool) : ℝ)⁻¹ *
            ∑ b : (Fin r → Fin M) → Bool,
              ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i₀ ∈ T ℓ), signVal (b (pt i₀ ℓ)) = 0 by
          rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hzero, mul_zero]
        have hinj : Function.Injective (pt i₀) := by
          intro ℓ₁ ℓ₂ heq
          funext j
          have hj := congrFun heq j
          by_contra hne
          apply hi₀D
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, j, ?_⟩
          cases h1 : ℓ₁ j <;> cases h2 : ℓ₂ j
          · exact (hne (h1.trans h2.symm)).elim
          · dsimp only [pt] at hj; rw [h1, h2] at hj; exact hj
          · dsimp only [pt] at hj; rw [h1, h2] at hj; exact hj.symm
          · exact (hne (h1.trans h2.symm)).elim
        have hne_S : (Finset.univ.filter (fun ℓ : Fin r → Bool ↦ i₀ ∈ T ℓ)).Nonempty :=
          ⟨ℓ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ₀, hi₀T⟩⟩
        rw [sum_prod_signVal_eq_zero_of_injective hinj hne_S, mul_zero]
      · have h0 : BitString.fourierCoeff φ (T ℓ₀) = 0 := hvanish (T ℓ₀) (Nat.lt_of_not_ge hcard)
        rw [Finset.prod_eq_zero (Finset.mem_univ ℓ₀) (by rw [h0, mul_zero]), zero_mul]
    rw [hcontr_eq]
    have hrestrict : ∑ T : (Fin r → Bool) → Finset (Fin m),
        (∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
          ((Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
            ∑ x₀ : PatternSpace r m M 0,
              ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))) =
        ∑ T ∈ goodTuples,
          (∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
            ((Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
              ∑ x₀ : PatternSpace r m M 0,
                ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                  signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) fun T _ hT ↦ hvanish_outside T hT
    rw [hrestrict]
    have hterm_le : ∀ T ∈ goodTuples,
        |(∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)) *
          ((Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
            ∑ x₀ : PatternSpace r m M 0,
              ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ)))| ≤ (sz ^ (2 ^ r))⁻¹ := by
      intro T _
      rw [abs_mul, Finset.abs_prod]
      have h1 : ∏ ℓ : Fin r → Bool, |((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)| ≤
          (sz ^ (2 ^ r))⁻¹ := by
        calc ∏ ℓ : Fin r → Bool, |((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)|
            = ∏ ℓ : Fin r → Bool, ((2 : ℝ) ^ m / sz) * |BitString.fourierCoeff φ (T ℓ)| :=
              Finset.prod_congr rfl fun ℓ _ ↦ by
                rw [abs_mul, abs_of_pos (by positivity)]
          _ ≤ ∏ _ℓ : Fin r → Bool, sz⁻¹ :=
              prod_le_prod_nonneg (fun _ _ ↦ by positivity) (fun ℓ _ ↦ hcoeff_le (T ℓ))
          _ = (sz ^ (2 ^ r))⁻¹ := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
                Fintype.card_fin, inv_pow]
      have h2 : |(Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
          ∑ x₀ : PatternSpace r m M 0,
            ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
              signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))| ≤ 1 := by
        rw [abs_mul, abs_inv, abs_of_pos hcard0_pos]
        have hones : ∀ x₀ : PatternSpace r m M 0,
            |∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
              signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))| = 1 := fun x₀ ↦ by
          rw [Finset.abs_prod]
          refine Finset.prod_eq_one fun i _ ↦ ?_
          rw [Finset.abs_prod]
          exact Finset.prod_eq_one fun ℓ _ ↦ abs_signVal _
        calc (Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
              |∑ x₀ : PatternSpace r m M 0,
                ∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                  signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))|
            ≤ (Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
                ∑ x₀ : PatternSpace r m M 0,
                  |∏ i : Fin m, ∏ ℓ ∈ Finset.univ.filter (fun ℓ ↦ i ∈ T ℓ),
                    signVal (patternPlayer0Equiv r m M x₀ i (pt i ℓ))| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
          _ = (Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ *
                ∑ _x₀ : PatternSpace r m M 0, (1 : ℝ) := by
              simp_rw [hones]
          _ = 1 := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
                inv_mul_cancel₀ hcard0_pos.ne']
      calc (∏ ℓ, |((2 : ℝ) ^ m / sz) * BitString.fourierCoeff φ (T ℓ)|) *
            |(Fintype.card (PatternSpace r m M 0) : ℝ)⁻¹ * _|
          ≤ (sz ^ (2 ^ r))⁻¹ * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (sz ^ (2 ^ r))⁻¹ := mul_one _
    have hcard_good : (goodTuples.card : ℝ) ≤
        if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0 := by
      split_ifs with hdg
      · have hsub : goodTuples ⊆ Finset.univ.filter (fun T : (Fin r → Bool) → Finset (Fin m) ↦
            ∀ ℓ, T ℓ ⊆ degenSet z) := by
          intro T hT
          simp only [goodTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
          exact fun ℓ ↦ (hT ℓ).2
        have hcard_pow : (Finset.univ.filter (fun T : (Fin r → Bool) → Finset (Fin m) ↦
            ∀ ℓ, T ℓ ⊆ degenSet z)).card = (2 ^ (degenSet z).card) ^ (2 ^ r) := by
          let eT : {T : (Fin r → Bool) → Finset (Fin m) // ∀ ℓ, T ℓ ⊆ degenSet z} ≃
              ((Fin r → Bool) → {S : Finset (Fin m) // S ∈ (degenSet z).powerset}) :=
            { toFun := fun T ℓ ↦ ⟨T.1 ℓ, Finset.mem_powerset.mpr (T.2 ℓ)⟩
              invFun := fun f ↦ ⟨fun ℓ ↦ (f ℓ).1, fun ℓ ↦ Finset.mem_powerset.mp (f ℓ).2⟩
              left_inv := fun _ ↦ rfl
              right_inv := fun _ ↦ rfl }
          have h1 : (Finset.univ.filter (fun T : (Fin r → Bool) → Finset (Fin m) ↦
              ∀ ℓ, T ℓ ⊆ degenSet z)).card =
              Fintype.card {T : (Fin r → Bool) → Finset (Fin m) // ∀ ℓ, T ℓ ⊆ degenSet z} := by
            rw [Fintype.card_subtype]
          rw [h1, Fintype.card_congr eT, Fintype.card_fun, Fintype.card_coe, Finset.card_powerset,
            Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        have hnat : goodTuples.card ≤ (2 ^ (degenSet z).card) ^ (2 ^ r) :=
          (Finset.card_le_card hsub).trans (le_of_eq hcard_pow)
        have hreal : (goodTuples.card : ℝ) ≤ ((2 : ℝ) ^ (degenSet z).card) ^ (2 ^ r) := by
          exact_mod_cast hnat
        refine hreal.trans (le_of_eq ?_)
        rw [← pow_mul, ← pow_mul, mul_comm]
      · have hemp : goodTuples = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro T hT
          simp only [goodTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hT
          have h0 := hT (fun _ ↦ false)
          have hle := Finset.card_le_card h0.2
          omega
        simp [hemp]
    calc |∑ T ∈ goodTuples, _|
        ≤ ∑ T ∈ goodTuples, |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _T ∈ goodTuples, (sz ^ (2 ^ r))⁻¹ := Finset.sum_le_sum hterm_le
      _ = (sz ^ (2 ^ r))⁻¹ * (goodTuples.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ (sz ^ (2 ^ r))⁻¹ *
            if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0 :=
          mul_le_mul_of_nonneg_left hcard_good (by positivity)
 -- Step 2: Bound `Pr_z [S ⊆ degenSet z] ≤ (r / M)^|S|` for any `S: Finset (Fin m)`:
  let CType := ∀ p : Fin r × Bool, ContractionSpace (PatternSpace r m M) p
  have hC_pos : (0 : ℝ) < tensorSize (ContractionSpace (PatternSpace r m M)) := by
    exact_mod_cast tensorSize_pos (X := ContractionSpace (PatternSpace r m M))
  have hprob_subset : ∀ S : Finset (Fin m),
      (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
        ∑ z : CType, (if S ⊆ degenSet z then (1 : ℝ) else 0) ≤
      ((r : ℝ) / (M : ℝ)) ^ S.card := by
    intro S
 -- Swap coordinates `CType ≃ (Fin m → (Fin r × Bool → Fin M))`:
    let eSwap : CType ≃ (Fin m → (Fin r × Bool → Fin M)) :=
      { toFun := fun z i p ↦ patternSuccEquiv r m M p.1 (z p) i
        invFun := fun w p i ↦ w i p
        left_inv := fun z ↦ by funext ⟨j, b⟩; rfl
        right_inv := fun w ↦ rfl }
    have hsingle_prob :
        ((Fintype.card (Fin r × Bool → Fin M) : ℝ)⁻¹ *
          ∑ u : Fin r × Bool → Fin M,
            if ∃ j : Fin r, u (j, false) = u (j, true) then (1 : ℝ) else 0) ≤
        (r : ℝ) / (M : ℝ) := by
      let U := Fin r × Bool → Fin M
      have hU_pos : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos (α := U)
      let badU : Finset U := Finset.univ.filter fun u ↦ ∃ j : Fin r, u (j, false) = u (j, true)
      have hsub : badU ⊆ Finset.univ.biUnion (fun j : Fin r ↦
          Finset.univ.filter fun u : U ↦ u (j, false) = u (j, true)) := by
        intro u hu
        rcases (Finset.mem_filter.mp hu).2 with ⟨j, hj⟩
        exact Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hj⟩⟩
      have hcard_j : ∀ j : Fin r,
          ((Finset.univ.filter fun u : U ↦ u (j, false) = u (j, true)).card : ℝ) * (M : ℝ) =
          (Fintype.card U : ℝ) := by
        intro j
        let S_j := Finset.univ.filter fun u : U ↦ u (j, false) = u (j, true)
        let e : ({u // u ∈ S_j} × Fin M) ≃ U :=
          { toFun := fun p ↦ Function.update p.1.1 (j, true) p.2
            invFun := fun u ↦ (⟨Function.update u (j, true) (u (j, false)), by simp [S_j]⟩,
              u (j, true))
            left_inv := fun ⟨⟨u, hu⟩, a⟩ ↦ by
              have huj : u (j, false) = u (j, true) := (Finset.mem_filter.mp hu).2
              ext p
              · by_cases hp : p = (j, true)
                · subst hp; simp [huj]
                · simp [Function.update_of_ne hp]
              · simp
            right_inv := fun u ↦ by
              funext p
              by_cases hp : p = (j, true)
              · subst hp; simp
              · simp [Function.update_of_ne hp] }
        have hc := Fintype.card_congr e
        simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hc
        exact_mod_cast hc
      have hbi : (badU.card : ℝ) ≤ (r : ℝ) * ((Fintype.card U : ℝ) / (M : ℝ)) := by
        have h1 : (badU.card : ℝ) ≤ ∑ j : Fin r,
            ((Finset.univ.filter fun u : U ↦ u (j, false) = u (j, true)).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        refine h1.trans (le_of_eq ?_)
        have hterm : ∀ j : Fin r,
            ((Finset.univ.filter fun u : U ↦ u (j, false) = u (j, true)).card : ℝ) =
            (Fintype.card U : ℝ) / (M : ℝ) := fun j ↦ by
          rw [eq_div_iff hM_pos.ne']; exact hcard_j j
        simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsum_eq : ∑ u : U, (if ∃ j : Fin r, u (j, false) = u (j, true) then (1 : ℝ) else 0) =
          (badU.card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hsum_eq]
      calc (Fintype.card U : ℝ)⁻¹ * (badU.card : ℝ)
          ≤ (Fintype.card U : ℝ)⁻¹ * ((r : ℝ) * ((Fintype.card U : ℝ) / (M : ℝ))) :=
            mul_le_mul_of_nonneg_left hbi (by positivity)
        _ = (r : ℝ) / (M : ℝ) := by field_simp [hU_pos.ne', hM_pos.ne']
    have hprod_eq : (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
        ∑ z : CType, (if S ⊆ degenSet z then (1 : ℝ) else 0) =
        ∏ i : Fin m,
          if i ∈ S then
            (Fintype.card (Fin r × Bool → Fin M) : ℝ)⁻¹ *
              ∑ u : Fin r × Bool → Fin M,
                if ∃ j : Fin r, u (j, false) = u (j, true) then (1 : ℝ) else 0
          else 1 := by
      have hcard_swap : (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ) =
          ((Fintype.card (Fin r × Bool → Fin M) : ℝ)) ^ m := by
        have hc : Fintype.card CType = Fintype.card (Fin r × Bool → Fin M) ^ m := by
          rw [Fintype.card_congr eSwap, Fintype.card_fun, Fintype.card_fin]
        change ((Fintype.card CType : ℕ) : ℝ) = _
        rw [hc, Nat.cast_pow]
      have hsum_swap : ∑ z : CType, (if S ⊆ degenSet z then (1 : ℝ) else 0) =
          ∑ w : Fin m → (Fin r × Bool → Fin M),
            ∏ i : Fin m,
              if i ∈ S then
                (if ∃ j : Fin r, w i (j, false) = w i (j, true) then (1 : ℝ) else 0)
              else 1 := by
        rw [← eSwap.symm.sum_comp]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        have hiff : S ⊆ degenSet (eSwap.symm w) ↔
            ∀ i ∈ S, ∃ j : Fin r, w i (j, false) = w i (j, true) := by
          simp only [Finset.subset_iff, degenSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rfl
        by_cases hSsub : S ⊆ degenSet (eSwap.symm w)
        · rw [ite_eq_left hSsub]
          symm
          refine Finset.prod_eq_one fun i _ ↦ ?_
          by_cases hi : i ∈ S
          · rw [ite_eq_left hi, ite_eq_left (hiff.mp hSsub i hi)]
          · rw [ite_eq_right hi]
        · rw [ite_eq_right hSsub]
          have hnot := hiff.not.mp hSsub
          push Not at hnot
          obtain ⟨i₀, hi₀S, hi₀not⟩ := hnot
          symm
          exact Finset.prod_eq_zero (Finset.mem_univ i₀)
            (by rw [ite_eq_left hi₀S, ite_eq_right (fun ⟨j, hj⟩ ↦ hi₀not j hj)])
      rw [hcard_swap, hsum_swap, (Fintype.prod_sum (fun (i : Fin m) (u : Fin r × Bool → Fin M) ↦
        if i ∈ S then (if ∃ j : Fin r, u (j, false) = u (j, true) then (1 : ℝ) else 0)
        else 1)).symm]
      have hU_pos : (0 : ℝ) < Fintype.card (Fin r × Bool → Fin M) := by
        exact_mod_cast Fintype.card_pos (α := Fin r × Bool → Fin M)
      rw [← inv_pow, show ((Fintype.card (Fin r × Bool → Fin M) : ℝ)⁻¹) ^ m =
          ∏ _i : Fin m, (Fintype.card (Fin r × Bool → Fin M) : ℝ)⁻¹ by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi]
        congr 1
        exact Finset.sum_congr rfl fun u _ ↦ by rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        have hones : ∀ u : Fin r × Bool → Fin M,
            (if i ∈ S then
              (if ∃ j : Fin r, u (j, false) = u (j, true) then (1 : ℝ) else 0)
            else 1) = (1 : ℝ) := fun _ ↦ ite_eq_right hi
        simp_rw [hones, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          inv_mul_cancel₀ hU_pos.ne']
    rw [hprod_eq]
    calc ∏ i : Fin m, (if i ∈ S then
              (Fintype.card (Fin r × Bool → Fin M) : ℝ)⁻¹ *
                ∑ u : Fin r × Bool → Fin M,
                  if ∃ j : Fin r, u (j, false) = u (j, true) then (1 : ℝ) else 0
            else 1)
        ≤ ∏ i : Fin m, (if i ∈ S then (r : ℝ) / (M : ℝ) else 1) := by
          refine prod_le_prod_nonneg (fun i _ ↦ ?_) (fun i _ ↦ ?_)
          · split_ifs
            · exact mul_nonneg (by positivity)
                (Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num)
            · norm_num
          · split_ifs
            · exact hsingle_prob
            · exact le_rfl
      _ = ((r : ℝ) / (M : ℝ)) ^ S.card := by
          rw [← Finset.prod_filter]
          have hfilt : Finset.univ.filter (fun i : Fin m ↦ i ∈ S) = S := by ext i; simp
          rw [hfilt, Finset.prod_const]
 -- Step 3: Average `hpoint` over `z`, partition by `S = degenSet z`, and sum over `g = d.. m`.
  rw [tensorExpectAbs_eq_inv_mul_l1, tensorL1_eq_sum]
  have havg1 : (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
      ∑ z : CType, |contractionProduct A z| ≤
      (sz ^ (2 ^ r))⁻¹ *
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
          ((2 : ℝ) ^ (2 ^ r)) ^ S.card * ((r : ℝ) / (M : ℝ)) ^ S.card := by
    calc (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
          ∑ z : CType, |contractionProduct A z|
        ≤ (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
            ∑ z : CType, (sz ^ (2 ^ r))⁻¹ *
              (if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ ↦ hpoint z) (by positivity)
      _ = (sz ^ (2 ^ r))⁻¹ * ((tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
            ∑ z : CType,
              if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (sz ^ (2 ^ r))⁻¹ *
            ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
              ((2 : ℝ) ^ (2 ^ r)) ^ S.card * ((r : ℝ) / (M : ℝ)) ^ S.card := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hpart : ∀ z : CType,
              (if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0) ≤
              ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
                ((2 : ℝ) ^ (2 ^ r)) ^ S.card * (if S ⊆ degenSet z then (1 : ℝ) else 0) := by
            intro z
            split_ifs with hdg
            · have hmem : degenSet z ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdg⟩
              calc ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card
                  = ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card *
                      (if degenSet z ⊆ degenSet z then (1 : ℝ) else 0) := by simp
                _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
                      ((2 : ℝ) ^ (2 ^ r)) ^ S.card * (if S ⊆ degenSet z then (1 : ℝ) else 0) :=
                    Finset.single_le_sum
                      (f := fun S : Finset (Fin m) ↦
                        ((2 : ℝ) ^ (2 ^ r)) ^ S.card * (if S ⊆ degenSet z then (1 : ℝ) else 0))
                      (fun S _ ↦ mul_nonneg (by positivity) (by split_ifs <;> norm_num)) hmem
            · exact Finset.sum_nonneg fun _ _ ↦
                mul_nonneg (by positivity) (by split_ifs <;> norm_num)
          calc (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
                ∑ z : CType,
                  (if d ≤ (degenSet z).card then ((2 : ℝ) ^ (2 ^ r)) ^ (degenSet z).card else 0)
              ≤ (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
                  ∑ z : CType,
                    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
                      ((2 : ℝ) ^ (2 ^ r)) ^ S.card * (if S ⊆ degenSet z then (1 : ℝ) else 0) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ ↦ hpart z) (by positivity)
            _ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
                  ((2 : ℝ) ^ (2 ^ r)) ^ S.card *
                    ((tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
                      ∑ z : CType, if S ⊆ degenSet z then (1 : ℝ) else 0) := by
                rw [Finset.sum_comm, Finset.mul_sum]
                refine Finset.sum_congr rfl fun S _ ↦ ?_
                rw [← Finset.mul_sum]; ring
            _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
                  ((2 : ℝ) ^ (2 ^ r)) ^ S.card * ((r : ℝ) / (M : ℝ)) ^ S.card :=
                Finset.sum_le_sum fun S _ ↦
                  mul_le_mul_of_nonneg_left (hprob_subset S) (by positivity)
 -- Step 4: Group subsets `S` by cardinality `g ∈ Icc d m` and bound by the geometric series!
  have hsum_by_card :
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
        ((2 : ℝ) ^ (2 ^ r)) ^ S.card * ((r : ℝ) / (M : ℝ)) ^ S.card =
      ∑ g ∈ Finset.Icc d m,
        (m.choose g : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g := by
    have hmap : Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card) =
        (Finset.Icc d m).biUnion (fun g ↦ (Finset.univ : Finset (Fin m)).powersetCard g) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_Icc,
        Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact ⟨fun h ↦ ⟨S.card, ⟨h, by simpa using S.card_le_univ⟩, rfl⟩,
        fun ⟨g, ⟨hdg, _⟩, hcard⟩ ↦ hcard ▸ hdg⟩
    rw [hmap, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun g _ ↦ ?_
      have hterm : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard g,
          ((2 : ℝ) ^ (2 ^ r)) ^ S.card * ((r : ℝ) / (M : ℝ)) ^ S.card =
          (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g := fun S hS ↦ by
        rw [(Finset.mem_powersetCard.mp hS).2, ← mul_pow]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    · intro g₁ _ g₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro S h1 h2
      exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  have hgeom : ∑ g ∈ Finset.Icc d m,
      (m.choose g : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g ≤ (2 : ℝ)⁻¹ ^ d := by
    have hratio : Real.exp 1 * (m : ℝ) / (d : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ≤
        (2 : ℝ)⁻¹ := by
      have h1 : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) ≤ (d : ℝ) * (M : ℝ) := by
        rwa [div_le_iff₀ hd_pos, mul_comm (M : ℝ)] at hM_ge
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      rw [show Real.exp 1 * (m : ℝ) / (d : ℝ) * ((2 : ℝ) ^ (2 ^ r) * ((r : ℝ) / (M : ℝ))) =
          (Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ)) / ((d : ℝ) * (M : ℝ)) by
            field_simp [hd_pos.ne', hM_pos.ne']]
      rw [div_le_div_iff₀ (mul_pos hd_pos hM_pos) (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hterm : ∀ g ∈ Finset.Icc d m,
        (m.choose g : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g ≤
          (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ g := by
      intro g hg
      have hdg : d ≤ g := (Finset.mem_Icc.mp hg).1
      calc (m.choose g : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g
          ≤ ((1 / 2 : ℝ) * (Real.exp 1 * (m : ℝ) / (d : ℝ)) ^ g) *
              (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g :=
            mul_le_mul_of_nonneg_right (choose_le_half_exp_pow hd hdg) (by positivity)
        _ = (1 / 2 : ℝ) * (Real.exp 1 * (m : ℝ) / (d : ℝ) *
              (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ)))) ^ g := by
            rw [mul_assoc, ← mul_pow]
        _ ≤ (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ g :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio g) (by norm_num)
    calc ∑ g ∈ Finset.Icc d m,
          (m.choose g : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g
        ≤ ∑ g ∈ Finset.Icc d m, (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ g := Finset.sum_le_sum hterm
      _ ≤ (2 : ℝ)⁻¹ ^ d := by
 -- Elementary telescoping sum `∑_{g ∈ Icc d m} (1/2) * (1/2)^g ≤ (1/2)^d`:
          have htele : ∀ n : ℕ,
              ∑ g ∈ Finset.Icc d n, (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ g ≤ (2 : ℝ)⁻¹ ^ d := by
            intro n
            by_cases hdn : d ≤ n
            · have hrec : ∀ k : ℕ,
                  ∑ g ∈ Finset.Icc d (d + k), (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ g =
                  (2 : ℝ)⁻¹ ^ d - (2 : ℝ)⁻¹ ^ (d + k + 1) := by
                intro k
                induction k with
                | zero =>
                  simp only [add_zero, Finset.Icc_self, Finset.sum_singleton, pow_succ]
                  ring
                | succ k ih =>
                  have hIcc : Finset.Icc d (d + (k + 1)) =
                      insert (d + (k + 1)) (Finset.Icc d (d + k)) := by
                    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                  have hnot : d + (k + 1) ∉ Finset.Icc d (d + k) := by simp
                  rw [hIcc, Finset.sum_insert hnot, ih]
                  rw [show d + (k + 1) + 1 = (d + k + 1) + 1 by omega,
                    show d + (k + 1) = d + k + 1 by omega, pow_succ]
                  ring
              rw [show n = d + (n - d) by omega, hrec (n - d)]
              have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (d + (n - d) + 1) := by positivity
              linarith
            · have hemp : Finset.Icc d n = ∅ := Finset.Icc_eq_empty hdn
              rw [hemp, Finset.sum_empty]
              positivity
          exact htele m
  calc (tensorSize (ContractionSpace (PatternSpace r m M)) : ℝ)⁻¹ *
        ∑ z : CType, |contractionProduct A z|
      ≤ (sz ^ (2 ^ r))⁻¹ *
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) ↦ d ≤ S.card),
            ((2 : ℝ) ^ (2 ^ r)) ^ S.card * ((r : ℝ) / (M : ℝ)) ^ S.card := havg1
    _ = (sz ^ (2 ^ r))⁻¹ *
          ∑ g ∈ Finset.Icc d m,
            (m.choose g : ℝ) * (((2 : ℝ) ^ (2 ^ r)) * ((r : ℝ) / (M : ℝ))) ^ g := by
        rw [hsum_by_card]
    _ ≤ (sz ^ (2 ^ r))⁻¹ * (2 : ℝ)⁻¹ ^ d :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = ((2 : ℝ)⁻¹ ^ d) / sz ^ (2 ^ r) := by rw [div_eq_inv_mul]

/-- **dual-norm power form**:
`μ*(A)^{2^r} ≤ 2^{-d}` for the normalized pattern tensor `A = normalizedPatternTensor r m M φ`. -/
theorem patternTensor_muDual_pow_le {r m M d : ℕ} (hd : 1 ≤ d) (hM : 0 < M)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) / (d : ℝ) ≤ (M : ℝ))
    {φ : BitString m → ℝ} (hL1 : boolL1 φ = 1)
    (hvanish : ∀ T : Finset (Fin m), T.card < d → BitString.fourierCoeff φ T = 0) :
    muDual (normalizedPatternTensor r m M φ) ^ (2 ^ r) ≤ (2 : ℝ)⁻¹ ^ d := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have hsz_pos : (0 : ℝ) < (tensorSize (PatternSpace r m M) : ℝ) ^ (2 ^ r) := by
    have : (0 : ℝ) < tensorSize (PatternSpace r m M) := by
      exact_mod_cast tensorSize_pos (X := PatternSpace r m M)
    positivity
  have h1 := muDual_pow_le_size_mul_expectAbs (normalizedPatternTensor r m M φ)
  have h2 := patternTensor_contraction_expectAbs_le hd hM hM_ge hL1 hvanish
  calc muDual (normalizedPatternTensor r m M φ) ^ (2 ^ r)
      ≤ (tensorSize (PatternSpace r m M) : ℝ) ^ (2 ^ r) *
          (((2 : ℝ)⁻¹ ^ d) / (tensorSize (PatternSpace r m M) : ℝ) ^ (2 ^ r)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hsz_pos.le)
    _ = (2 : ℝ)⁻¹ ^ d := by field_simp [hsz_pos.ne']

/-- **real-exponent form**:
`μ*(A) ≤ 2^{-d / 2^r}` for the normalized pattern tensor `A`. -/
theorem patternTensor_muDual_rpow_le {r m M d : ℕ} (hd : 1 ≤ d) (hM : 0 < M)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) / (d : ℝ) ≤ (M : ℝ))
    {φ : BitString m → ℝ} (hL1 : boolL1 φ = 1)
    (hvanish : ∀ T : Finset (Fin m), T.card < d → BitString.fourierCoeff φ T = 0) :
    muDual (normalizedPatternTensor r m M φ) ≤ (2 : ℝ) ^ (-((d : ℝ) / (2 ^ r : ℝ))) := by
  have hpow := patternTensor_muDual_pow_le hd hM hM_ge hL1 hvanish
  have h2r_pos : (0 : ℝ) < (2 ^ r : ℝ) := by positivity
  have hnn : 0 ≤ muDual (normalizedPatternTensor r m M φ) := muDual_nonneg _
  have h1 := Real.rpow_le_rpow (by positivity) hpow (inv_nonneg.mpr h2r_pos.le)
  have hL : (muDual (normalizedPatternTensor r m M φ) ^ (2 ^ r)) ^ ((2 ^ r : ℝ)⁻¹) =
      muDual (normalizedPatternTensor r m M φ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    push_cast
    rw [mul_inv_cancel₀ h2r_pos.ne', Real.rpow_one]
  have hR : ((2 : ℝ)⁻¹ ^ d) ^ ((2 ^ r : ℝ)⁻¹) = (2 : ℝ) ^ (-((d : ℝ) / (2 ^ r : ℝ))) := by
    rw [inv_pow, ← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul, div_eq_mul_inv]
  rwa [hL, hR] at h1

end MainPatternLemma

section LiftingTheorem

/-- **exponential form**: for `k = r + 1 ≥ 2` (`1 ≤ r`), `1 ≤ α < α₀`, `d = deg_{α₀}(f) ≥ 1`, and
`M ≥ 2 e r 2^{2^r} m / d`,
`((α₀ - α) / (α₀ + 1)) * 2^{d / 2^r} ≤ μ^α(A_{k, M, f})`. -/
theorem muAlpha_patternTensor_ge_exp {r m M : ℕ} (hr : 1 ≤ r) (hM : 0 < M)
    {f : BitString m → Bool} {α α₀ : ℝ} (hα : 1 ≤ α) (hα₀ : α < α₀)
    (hd : 1 ≤ alphaApproxDeg α₀ f)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) /
      (alphaApproxDeg α₀ f : ℝ) ≤ (M : ℝ)) :
    ((α₀ - α) / (α₀ + 1)) * (2 : ℝ) ^ ((alphaApproxDeg α₀ f : ℝ) / (2 ^ r : ℝ)) ≤
      muAlpha α (patternTensor r m M (fun w ↦ signVal (f w))) := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have _ : Nontrivial (Fin (r + 1)) := ⟨⟨0, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  have hα₀1 : 1 ≤ α₀ := by linarith
  obtain ⟨q, hq_orth, hq_l1, hq_corr⟩ := exists_dual_polynomial_finite hα₀1 f
  let A := patternTensor r m M (fun w ↦ signVal (f w))
  let Q := normalizedPatternTensor r m M q
  have hA_sign : IsSignTensor A := fun z ↦ isSignTensor_signTensor (f ∘ patternProj) z
  have hL1_Q : tensorL1 Q = 1 := by rw [tensorL1_normalizedPatternTensor hM q, hq_l1]
  have hInner_Q : (α₀ - 1) / (α₀ + 1) ≤ tensorInner A Q := by
    rw [tensorInner_patternTensor_normalized hM f q]
    exact hq_corr
  have hnum : (α₀ - α) / (α₀ + 1) ≤ ((1 + α) * tensorInner A Q + (1 - α) * tensorL1 Q) / 2 := by
    rw [hL1_Q, mul_one]
    have hα₀_pos : 0 < α₀ + 1 := by linarith
    have h1 : (1 + α) * ((α₀ - 1) / (α₀ + 1)) ≤ (1 + α) * tensorInner A Q :=
      mul_le_mul_of_nonneg_left hInner_Q (by linarith)
    have hident : ((1 + α) * ((α₀ - 1) / (α₀ + 1)) + (1 - α)) / 2 = (α₀ - α) / (α₀ + 1) := by
      field_simp [hα₀_pos.ne']; ring
    linarith
  have hwd := weak_duality_muAlpha hA_sign hα Q
  have hmuQ := patternTensor_muDual_rpow_le hd hM hM_ge hq_l1 hq_orth
  have hcomb : (α₀ - α) / (α₀ + 1) ≤
      muAlpha α A * (2 : ℝ) ^ (-((alphaApproxDeg α₀ f : ℝ) / (2 ^ r : ℝ))) :=
    hnum.trans (hwd.trans (mul_le_mul_of_nonneg_left hmuQ (muAlpha_nonneg _ _)))
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((alphaApproxDeg α₀ f : ℝ) / (2 ^ r : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcomb hpow_pos.le
  refine hmul.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero,
    mul_one]

/-- **`log₂` form**):
`deg_{α₀}(f) / 2^{k-1} + log₂((α₀ - α) / (α₀ + 1)) ≤ log₂(μ^α(A_{k, M, f}))`. -/
theorem logb_muAlpha_patternTensor_ge {r m M : ℕ} (hr : 1 ≤ r) (hM : 0 < M)
    {f : BitString m → Bool} {α α₀ : ℝ} (hα : 1 ≤ α) (hα₀ : α < α₀)
    (hd : 1 ≤ alphaApproxDeg α₀ f)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) /
      (alphaApproxDeg α₀ f : ℝ) ≤ (M : ℝ)) :
    (alphaApproxDeg α₀ f : ℝ) / (2 ^ r : ℝ) + Real.logb 2 ((α₀ - α) / (α₀ + 1)) ≤
      Real.logb 2 (muAlpha α (patternTensor r m M (fun w ↦ signVal (f w)))) := by
  have hfrac_pos : 0 < (α₀ - α) / (α₀ + 1) := div_pos (by linarith) (by linarith)
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((alphaApproxDeg α₀ f : ℝ) / (2 ^ r : ℝ)) := by positivity
  have hexp := muAlpha_patternTensor_ge_exp hr hM hα hα₀ hd hM_ge
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (mul_pos hfrac_pos hpow_pos) hexp
  rw [Real.logb_mul hfrac_pos.ne' hpow_pos.ne',
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hlog
  linarith

/-- **exponential form**: for `k = r + 1 ≥ 2`, `d = deg_∞(f) ≥ 1`, and `M ≥ 2 e r 2^{2^r} m / d`,
`2^{d / 2^r} ≤ μ^∞(A_{k, M, f})`. -/
theorem muInfty_patternTensor_ge_exp {r m M : ℕ} (hr : 1 ≤ r) (hM : 0 < M)
    {f : BitString m → Bool} (hd : 1 ≤ inftyApproxDeg f)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) /
      (inftyApproxDeg f : ℝ) ≤ (M : ℝ)) :
    (2 : ℝ) ^ ((inftyApproxDeg f : ℝ) / (2 ^ r : ℝ)) ≤
      muInfty (patternTensor r m M (fun w ↦ signVal (f w))) := by
  have _ : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have _ : Nontrivial (Fin (r + 1)) := ⟨⟨0, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  obtain ⟨q, hq_orth, hq_l1, hq_sgn⟩ := exists_dual_polynomial_infty f
  let A := patternTensor r m M (fun w ↦ signVal (f w))
  let Q := normalizedPatternTensor r m M q
  have hA_sign : IsSignTensor A := fun z ↦ isSignTensor_signTensor (f ∘ patternProj) z
  have hAQ : ∀ z, 0 ≤ A z * Q z := fun z ↦ by
    dsimp only [A, Q, patternTensor, normalizedPatternTensor]
    have hpos : 0 ≤ (2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ) := by positivity
    have hmul : signVal (f (patternProj z)) *
        (((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) * q (patternProj z)) =
        ((2 : ℝ) ^ m / (tensorSize (PatternSpace r m M) : ℝ)) *
          (q (patternProj z) * signVal (f (patternProj z))) := by ring
    rw [hmul]
    exact mul_nonneg hpos (hq_sgn (patternProj z))
  have hInner_Q : tensorInner A Q = 1 := by
    rw [tensorInner_patternTensor_normalized hM f q]
    calc boolInner q f = boolL1 q := by
          rw [boolInner_eq_sum, boolL1_eq_sum]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          have habs : |q x * signVal (f x)| = |q x| := by rw [abs_mul, abs_signVal, mul_one]
          rw [← habs, abs_of_nonneg (hq_sgn x)]
      _ = 1 := hq_l1
  have hwd := weak_duality_muInfty hA_sign hAQ
  rw [hInner_Q] at hwd
  have hmuQ := patternTensor_muDual_rpow_le hd hM hM_ge hq_l1 hq_orth
  have hcomb : (1 : ℝ) ≤ muInfty A * (2 : ℝ) ^ (-((inftyApproxDeg f : ℝ) / (2 ^ r : ℝ))) :=
    hwd.trans (mul_le_mul_of_nonneg_left hmuQ (muInfty_nonneg _))
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((inftyApproxDeg f : ℝ) / (2 ^ r : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcomb hpow_pos.le
  rw [one_mul, mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
    Real.rpow_zero, mul_one] at hmul
  exact hmul

/-- **`log₂` form**):
`deg_∞(f) / 2^{k-1} ≤ log₂(μ^∞(A_{k, M, f}))`. -/
theorem logb_muInfty_patternTensor_ge {r m M : ℕ} (hr : 1 ≤ r) (hM : 0 < M)
    {f : BitString m → Bool} (hd : 1 ≤ inftyApproxDeg f)
    (hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) /
      (inftyApproxDeg f : ℝ) ≤ (M : ℝ)) :
    (inftyApproxDeg f : ℝ) / (2 ^ r : ℝ) ≤
      Real.logb 2 (muInfty (patternTensor r m M (fun w ↦ signVal (f w)))) := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((inftyApproxDeg f : ℝ) / (2 ^ r : ℝ)) := by positivity
  have hexp := muInfty_patternTensor_ge_exp hr hM hd hM_ge
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpow_pos hexp
  rwa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hlog

end LiftingTheorem

end CslibFrontier.Computability.Communication.NOF
