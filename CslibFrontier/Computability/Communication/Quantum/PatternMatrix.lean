/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Computability.Communication.Quantum.MatrixNorms

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Indexing Gadget and Sherstov's Pattern Matrix Spectral Norm

This module defines the $k$-bit indexing gadget $g_k$ and the $k$-pattern matrix
$\mathrm{PM}_k(\psi)$ of a real function $\psi : \{0, 1\}^n \to \mathbb{R}$, and proves
Sherstov's exact spectral-norm identity:

$$\|\mathrm{PM}_k(\psi)\| = \sqrt{2^{nk} (2k)^n} \max_{S \subseteq [n]} |\widehat{\psi}(S)|
k^{-|S|/2}.$$

The proof expands $\mathrm{PM}_k(\psi) = \sum_S \widehat{\psi}(S) \mathrm{PM}_k(\chi_S)$, verifies
by direct coordinatewise Fubini product that the Gram matrices
$P_S = c_S^{-1} \mathrm{PM}_k(\chi_S)^\top \mathrm{PM}_k(\chi_S)$ are nonzero pairwise orthogonal
symmetric idempotents, and reads off both the upper and lower spectral norm bounds directly.

## Main definitions

* `CslibFrontier.CommunicationComplexity.indexGadget`: the $k$-bit indexing gadget
  $g_k(x, (j, w)) = x_j \oplus w$.
* `CslibFrontier.CommunicationComplexity.patternMatrix`: the $k$-pattern matrix
  $\mathrm{PM}_k(\psi)$.

## Main results

* `CslibFrontier.CommunicationComplexity.patternMatrix_l1Norm`:
  $\|\mathrm{PM}_k(\psi)\|_1 = 2^{nk} k^n \|\psi\|_1$.
* `CslibFrontier.CommunicationComplexity.spectralNorm_patternMatrix`: Sherstov's exact spectral-norm
  identity for $\mathrm{PM}_k(\psi)$.
-/

public section

open scoped BigOperators Matrix.Norms.L2Operator
open Finset Matrix Cslib Cslib.BitString

namespace CslibFrontier.CommunicationComplexity

/-- The $k$-bit indexing gadget $g_k(x, (j, w)) = x_j \oplus w$. -/
def indexGadget (k : ℕ) (x : BitString k) (yw : Fin k × Bool) : Bool :=
  x yw.1 ^^ yw.2

lemma indexGadget_apply (k : ℕ) (x : BitString k) (yw : Fin k × Bool) :
    indexGadget k x yw = (x yw.1 ^^ yw.2) := by rfl

/-- The $k$-pattern matrix $\mathrm{PM}_k(\psi)$ of $\psi : \{0, 1\}^n \to \mathbb{R}$:
a $2^{nk} \times (2k)^n$ real matrix with entries $\psi(g_k(x^1, y_1), \dots, g_k(x^n, y_n))$. -/
noncomputable def patternMatrix {n k : ℕ} (ψ : BitString n → ℝ) :
    Matrix (Fin n → BitString k) (Fin n → Fin k × Bool) ℝ :=
  Matrix.of fun x yw => ψ (fun i => indexGadget k (x i) (yw i))

lemma patternMatrix_apply {n k : ℕ} (ψ : BitString n → ℝ)
    (x : Fin n → BitString k) (yw : Fin n → Fin k × Bool) :
    patternMatrix ψ x yw = ψ (fun i => indexGadget k (x i) (yw i)) := by rfl

lemma patternMatrix_smul {n k : ℕ} (c : ℝ) (ψ : BitString n → ℝ) :
    patternMatrix (k := k) (fun z => c * ψ z) = c • patternMatrix (k := k) ψ := by
  ext x yw; simp [patternMatrix]

lemma patternMatrix_add {n k : ℕ} (ψ₁ ψ₂ : BitString n → ℝ) :
    patternMatrix (k := k) (fun z => ψ₁ z + ψ₂ z) =
      patternMatrix (k := k) ψ₁ + patternMatrix (k := k) ψ₂ := by
  ext x yw; simp [patternMatrix]

/-- Every output string `z : BitString n` has exactly `2^{nk} * k^n` preimages under the
`n`-fold indexing gadget. -/
lemma card_indexGadget_fiber {n k : ℕ} (z : BitString n) :
    #({p : (Fin n → BitString k) × (Fin n → Fin k × Bool) |
      (fun i => indexGadget k (p.1 i) (p.2 i)) = z}) =
      2 ^ (n * k) * k ^ n := by
  -- For each coordinate `i`, there are `k * 2^k` pairs `(x_i, (j_i, w_i))` with `x_i j_i ^^ w_i = z
  -- i`.
  have h1 : ∀ b : Bool, #({p : BitString k × (Fin k × Bool) | indexGadget k p.1 p.2 = b}) =
      2 ^ k * k := by
    intro b
    let e : (BitString k × Fin k) ≃ {p : BitString k × (Fin k × Bool) // indexGadget k p.1 p.2 =
      b} :=
      { toFun := fun ⟨x, j⟩ => ⟨(x, (j, x j ^^ b)), by simp [indexGadget]⟩
        invFun := fun ⟨⟨x, j, _⟩, _⟩ => (x, j)
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨⟨x, j, w⟩, h⟩ => by
          apply Subtype.ext; simp only [Prod.mk.injEq, true_and]
          cases hx : x j <;> cases w <;> cases b <;> simp_all [indexGadget] }
    rw [← Fintype.card_subtype]
    have hcard := Fintype.card_congr e.symm
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
    exact hcard
  let eAll : {p : (Fin n → BitString k) × (Fin n → Fin k × Bool) //
        (fun i => indexGadget k (p.1 i) (p.2 i)) = z} ≃
      (∀ i : Fin n, {p : BitString k × (Fin k × Bool) // indexGadget k p.1 p.2 = z i}) :=
    { toFun := fun ⟨⟨x, yw⟩, h⟩ i => ⟨(x i, yw i), congr_fun h i⟩
      invFun := fun f => ⟨(fun i => (f i).1.1, fun i => (f i).1.2), funext fun i => (f i).2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card {p : (Fin n → BitString k) × (Fin n → Fin k × Bool) //
        (fun i => indexGadget k (p.1 i) (p.2 i)) = z} =
      ∏ i : Fin n, Fintype.card {p : BitString k × (Fin k × Bool) // indexGadget k p.1 p.2 =
        z i} := by
    rw [Fintype.card_congr eAll, Fintype.card_pi]
  have hprod : (∏ i : Fin n, Fintype.card {p : BitString k × (Fin k × Bool) //
        indexGadget k p.1 p.2 = z i}) = 2 ^ (n * k) * k ^ n := by
    have hterm : ∀ i : Fin n, Fintype.card {p : BitString k × (Fin k × Bool) //
        indexGadget k p.1 p.2 = z i} = 2 ^ k * k := fun i => by
      rw [Fintype.card_subtype]
      exact h1 (z i)
    simp_rw [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul]
    rw [mul_comm k n]
  rw [← Fintype.card_subtype]
  exact hcard.trans hprod

/-- The entrywise $\ell_1$ norm of `patternMatrix ψ` is `2^{nk} k^n * ∑ z, |ψ z|`. -/
lemma patternMatrix_l1Norm {n k : ℕ} (ψ : BitString n → ℝ) :
    matrixL1Norm (patternMatrix (k := k) ψ) =
      (2 : ℝ) ^ (n * k) * (k : ℝ) ^ n * ∑ z : BitString n, |ψ z| := by
  classical
  simp only [matrixL1Norm_eq_sum, patternMatrix, Matrix.of_apply]
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_fiberwise_of_maps_to (g :=
    fun p : (Fin n → BitString k) × (Fin n → Fin k × Bool) =>
      fun i => indexGadget k (p.1 i) (p.2 i)) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hconst : ∑ p ∈ Finset.univ.filter (fun p : (Fin n → BitString k) × (Fin n → Fin k × Bool) =>
      (fun i => indexGadget k (p.1 i) (p.2 i)) = z), |ψ (fun i => indexGadget k (p.1 i) (p.2 i))| =
      #({p : (Fin n → BitString k) × (Fin n → Fin k × Bool) |
        (fun i => indexGadget k (p.1 i) (p.2 i)) = z}) • |ψ z| := by
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2], Finset.sum_const]
  rw [hconst, card_indexGadget_fiber z, nsmul_eq_mul]
  push_cast; ring

private lemma inner_toEuclideanLin_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A B : Matrix α β ℝ) (v : EuclideanSpace ℝ β) :
    inner ℝ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin B v) =
      inner ℝ v (Matrix.toEuclideanLin (Aᵀ * B) v) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-- **Sherstov's Pattern Matrix Spectral Norm Identity**:
for every `n : ℕ`, `k ≥ 1`, and `ψ : BitString n → ℝ`,
`‖PM_k(ψ)‖ = √(2^{nk} (2k)^n) * max_S (|ψ̂(S)| * k^{-|S|/2})`.
-/
theorem spectralNorm_patternMatrix {n k : ℕ} (hk : 1 ≤ k) (ψ : BitString n → ℝ) :
    spectralNorm (patternMatrix (k := k) ψ) =
      Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) *
        (Finset.univ.sup' Finset.univ_nonempty fun S : Finset (Fin n) =>
          |fourierCoeff ψ S| * (k : ℝ) ^ (-(#S : ℝ) / 2)) := by
  classical
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let M : Finset (Fin n) → Matrix (Fin n → BitString k) (Fin n → Fin k × Bool) ℝ :=
    fun S => patternMatrix (k := k) (chi ℝ S)
  let c : Finset (Fin n) → ℝ :=
    fun S => (2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n * (k : ℝ) ^ (-(#S : ℝ))
  have hc_pos : ∀ S, 0 < c S := fun S => by
    simp only [c]; positivity
  -- Compute `(M S)ᵀ * M T` explicitly for all `S, T`.
  have hMTM : ∀ (S T : Finset (Fin n)) (y y' : Fin n → Fin k × Bool),
      ((M S)ᵀ * M T) y y' =
        if S = T ∧ ∀ i ∈ S, (y i).1 = (y' i).1 then
          ((2 : ℝ) ^ k) ^ n * ∏ i ∈ S, signVal ((y i).2 ^^ (y' i).2)
        else 0 := by
    intro S T y y'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, patternMatrix, Matrix.of_apply,
      chi_eq_prod_signVal]
    -- Factor `∑_{x : Fin n → BitString k} ∏ i, ...` into `∏ i, ∑_{u : BitString k} ...`!
    have hfac : ∀ x : Fin n → BitString k,
        (∏ i ∈ S, signVal (indexGadget k (x i) (y i))) *
        (∏ i ∈ T, signVal (indexGadget k (x i) (y' i))) =
          ∏ i : Fin n,
            ((if i ∈ S then signVal (indexGadget k (x i) (y i)) else 1) *
             (if i ∈ T then signVal (indexGadget k (x i) (y' i)) else 1)) := by
      intro x
      rw [Finset.prod_mul_distrib]
      congr 1 <;> rw [Finset.prod_ite_mem, Finset.univ_inter]
    simp_rw [hfac]
    rw [← Fintype.prod_sum (fun (i : Fin n) (u : BitString k) =>
      (if i ∈ S then signVal (indexGadget k u (y i)) else 1) *
      (if i ∈ T then signVal (indexGadget k u (y' i)) else 1))]
    -- Evaluate the 1-coordinate sum over `u : BitString k`!
    have h1d : ∀ i : Fin n,
        ∑ u : BitString k,
          (if i ∈ S then signVal (indexGadget k u (y i)) else 1) *
          (if i ∈ T then signVal (indexGadget k u (y' i)) else 1) =
        if i ∈ S ∧ i ∈ T then
          if (y i).1 = (y' i).1 then (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y' i).2) else 0
        else if i ∉ S ∧ i ∉ T then (2 : ℝ) ^ k else 0 := by
      intro i
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
      · simp only [hS, hT, and_self, ↓reduceIte]
        have hprod_u : ∀ u : BitString k,
            signVal (indexGadget k u (y i)) * signVal (indexGadget k u (y' i)) =
              signVal ((y i).2 ^^ (y' i).2) *
                (signVal (u (y i).1) * signVal (u (y' i).1)) := by
          intro u; simp only [indexGadget, signVal_xor]; ring
        simp_rw [hprod_u, ← Finset.mul_sum]
        by_cases hj : (y i).1 = (y' i).1
        · simp only [hj, ↓reduceIte, signVal_mul_self, Finset.sum_const, Finset.card_univ,
            Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one,
            Nat.cast_pow, Nat.cast_ofNat]
          ring
        · simp only [hj, ↓reduceIte, mul_eq_zero]
          right
          -- Pair `u` with `Function.update u (y i).1 (!(u (y i).1))`!
          have hpair : ∑ u : BitString k, signVal (u (y i).1) * signVal (u (y' i).1) =
              ∑ u : BitString k, -(signVal (u (y i).1) * signVal (u (y' i).1)) := by
            let f : BitString k ≃ BitString k :=
              { toFun := fun u => Function.update u (y i).1 (!(u (y i).1))
                invFun := fun u => Function.update u (y i).1 (!(u (y i).1))
                left_inv := fun u => by funext r; by_cases hr : r = (y i).1 <;> simp [hr]
                right_inv := fun u => by funext r; by_cases hr : r = (y i).1 <;> simp [hr] }
            refine Fintype.sum_equiv f _ _ fun u => ?_
            simp only [f, Equiv.coe_fn_mk, Function.update_self, Function.update_of_ne (Ne.symm hj),
              signVal_not]
            ring
          rw [Finset.sum_neg_distrib] at hpair
          linarith
      · simp only [hS, hT, ↓reduceIte, mul_one, and_false, not_true_eq_false, false_and]
        have hpair : ∑ u : BitString k, signVal (indexGadget k u (y i)) =
            ∑ u : BitString k, -(signVal (indexGadget k u (y i))) := by
          let f : BitString k ≃ BitString k :=
            { toFun := fun u => Function.update u (y i).1 (!(u (y i).1))
              invFun := fun u => Function.update u (y i).1 (!(u (y i).1))
              left_inv := fun u => by funext r; by_cases hr : r = (y i).1 <;> simp [hr]
              right_inv := fun u => by funext r; by_cases hr : r = (y i).1 <;> simp [hr] }
          refine Fintype.sum_equiv f _ _ fun u => ?_
          simp [f, indexGadget, signVal_xor, signVal_not]
        rw [Finset.sum_neg_distrib] at hpair; linarith
      · simp only [hS, hT, ↓reduceIte, one_mul, false_and, not_true_eq_false, and_false]
        have hpair : ∑ u : BitString k, signVal (indexGadget k u (y' i)) =
            ∑ u : BitString k, -(signVal (indexGadget k u (y' i))) := by
          let f : BitString k ≃ BitString k :=
            { toFun := fun u => Function.update u (y' i).1 (!(u (y' i).1))
              invFun := fun u => Function.update u (y' i).1 (!(u (y' i).1))
              left_inv := fun u => by funext r; by_cases hr : r = (y' i).1 <;> simp [hr]
              right_inv := fun u => by funext r; by_cases hr : r = (y' i).1 <;> simp [hr] }
          refine Fintype.sum_equiv f _ _ fun u => ?_
          simp [f, indexGadget, signVal_xor, signVal_not]
        rw [Finset.sum_neg_distrib] at hpair; linarith
      · simp [hS, hT]
    simp_rw [h1d]
    by_cases hST : S = T
    · subst hST
      simp only [and_self, true_and]
      by_cases hy : ∀ i ∈ S, (y i).1 = (y' i).1
      · simp only [eq_true hy, ↓reduceIte]
        have hsplit : (∏ i : Fin n, if i ∈ S then
              if (y i).1 = (y' i).1 then (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y' i).2) else 0
            else if i ∉ S then (2 : ℝ) ^ k else 0) =
            (∏ i ∈ S, ((2 : ℝ) ^ k * signVal ((y i).2 ^^ (y' i).2))) *
            (∏ i ∈ Finset.univ.filter (fun i => i ∉ S), (2 : ℝ) ^ k) := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
          congr 1
          · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
            exact Finset.prod_congr rfl fun i hi => by simp [hi, hy i hi]
          · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        have hcard_compl : (Finset.univ.filter fun i : Fin n => i ∉ S).card = n - #S := by
          rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        rw [hsplit, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, hcard_compl]
        rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (by simpa using Finset.card_le_univ S)]
      · simp only [hy, ↓reduceIte]
        push Not at hy
        obtain ⟨i₀, hi₀, hne⟩ := hy
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀, hne])
    · have hdiff : ∃ i : Fin n, (i ∈ S ∧ i ∉ T) ∨ (i ∉ S ∧ i ∈ T) := by
        by_contra hall; push Not at hall
        apply hST; ext i; specialize hall i; tauto
      obtain ⟨i₀, hi₀ | hi₀⟩ := hdiff
      · simp only [hST, false_and, ↓reduceIte]
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀.1, hi₀.2])
      · simp only [hST, false_and, ↓reduceIte]
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀.1, hi₀.2])
  -- Pairwise orthogonality `(M S)ᵀ * M T = 0` for `S ≠ T`, and idempotence of `P_S = (c S)⁻¹ • ((M
  -- S)ᵀ * M S)`.
  have hP_orth : ∀ S T : Finset (Fin n), S ≠ T → (M S)ᵀ * M T = 0 := by
    intro S T hST; ext y y'; rw [hMTM]; simp [hST]
  have hP_sq : ∀ S : Finset (Fin n), ((M S)ᵀ * M S) * ((M S)ᵀ * M S) = c S • ((M S)ᵀ * M S) := by
    intro S; ext y y''
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hMTM, true_and]
    -- Factor the sum over `y' : Fin n → Fin k × Bool` coordinatewise!
    have hfac : ∀ y' : Fin n → Fin k × Bool,
        (if ∀ i ∈ S, (y i).1 = (y' i).1 then
          ((2 : ℝ) ^ k) ^ n * ∏ i ∈ S, signVal ((y i).2 ^^ (y' i).2) else 0) *
        (if ∀ i ∈ S, (y' i).1 = (y'' i).1 then
          ((2 : ℝ) ^ k) ^ n * ∏ i ∈ S, signVal ((y' i).2 ^^ (y'' i).2) else 0) =
        ∏ i : Fin n,
          (if i ∈ S then
            if (y i).1 = (y' i).1 ∧ (y' i).1 = (y'' i).1 then
              (2 : ℝ) ^ k * (2 : ℝ) ^ k *
                signVal ((y i).2 ^^ (y' i).2) * signVal ((y' i).2 ^^ (y'' i).2)
            else 0
          else (2 : ℝ) ^ k * (2 : ℝ) ^ k) := by
      intro y'
      by_cases h1 : ∀ i ∈ S, (y i).1 = (y' i).1 <;> by_cases h2 : ∀ i ∈ S, (y' i).1 = (y'' i).1
      · simp only [eq_true h1, eq_true h2, ↓reduceIte]
        have hsplit : (∏ i : Fin n, if i ∈ S then
              if (y i).1 = (y' i).1 ∧ (y' i).1 = (y'' i).1 then
                (2 : ℝ) ^ k * (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y' i).2) *
                  signVal ((y' i).2 ^^ (y'' i).2) else 0
            else (2 : ℝ) ^ k * (2 : ℝ) ^ k) =
            (∏ i ∈ S, ((2 : ℝ) ^ k * (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y' i).2) *
              signVal ((y' i).2 ^^ (y'' i).2))) *
            (∏ i ∈ Finset.univ.filter (fun i => i ∉ S), ((2 : ℝ) ^ k * (2 : ℝ) ^ k)) := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
          congr 1
          · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
            exact Finset.prod_congr rfl fun i hi => by simp [hi, h1 i hi, h2 i hi]
          · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        rw [hsplit]
        have hcard_compl : (Finset.univ.filter fun i : Fin n => i ∉ S).card = n - #S := by
          rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        simp only [Finset.prod_mul_distrib, Finset.prod_const, hcard_compl]
        have hpow : (((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ #S) *
            (((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S)) =
            ((2 : ℝ) ^ k) ^ n * ((2 : ℝ) ^ k) ^ n := by
          have hle : #S ≤ n := by simpa using Finset.card_le_univ S
          calc (((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ #S) *
                (((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S))
              = (((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ (n - #S)) *
                (((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ (n - #S)) := by ring
            _ = ((2 : ℝ) ^ k) ^ n * ((2 : ℝ) ^ k) ^ n := by rw [← pow_add, Nat.add_sub_of_le hle]
        calc ((2 : ℝ) ^ k) ^ n * (∏ i ∈ S, signVal ((y i).2 ^^ (y' i).2)) *
              (((2 : ℝ) ^ k) ^ n * ∏ i ∈ S, signVal ((y' i).2 ^^ (y'' i).2))
            = (((2 : ℝ) ^ k) ^ n * ((2 : ℝ) ^ k) ^ n) *
              ((∏ i ∈ S, signVal ((y i).2 ^^ (y' i).2)) *
                ∏ i ∈ S, signVal ((y' i).2 ^^ (y'' i).2)) := by ring
          _ = ((((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ #S) *
                (((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S))) *
              ((∏ i ∈ S, signVal ((y i).2 ^^ (y' i).2)) *
                ∏ i ∈ S, signVal ((y' i).2 ^^ (y'' i).2)) := by rw [hpow]
          _ = ((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ #S *
                (∏ i ∈ S, signVal ((y i).2 ^^ (y' i).2)) *
                (∏ i ∈ S, signVal ((y' i).2 ^^ (y'' i).2)) *
                (((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S)) := by ring
      · simp only [h2, ↓reduceIte, mul_zero]; symm
        push Not at h2; obtain ⟨i₀, hi₀, hne⟩ := h2
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀, hne])
      · simp only [h1, ↓reduceIte, zero_mul]; symm
        push Not at h1; obtain ⟨i₀, hi₀, hne⟩ := h1
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀, hne])
      · simp only [h1, ↓reduceIte, zero_mul]; symm
        push Not at h1; obtain ⟨i₀, hi₀, hne⟩ := h1
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀, hne])
    simp_rw [hfac]
    rw [← Fintype.prod_sum (fun (i : Fin n) (jw : Fin k × Bool) =>
      if i ∈ S then
        if (y i).1 = jw.1 ∧ jw.1 = (y'' i).1 then
          (2 : ℝ) ^ k * (2 : ℝ) ^ k *
            signVal ((y i).2 ^^ jw.2) * signVal (jw.2 ^^ (y'' i).2)
        else 0
      else (2 : ℝ) ^ k * (2 : ℝ) ^ k)]
    have h1d : ∀ i : Fin n,
        ∑ jw : Fin k × Bool,
          (if i ∈ S then
            if (y i).1 = jw.1 ∧ jw.1 = (y'' i).1 then
              (2 : ℝ) ^ k * (2 : ℝ) ^ k * signVal ((y i).2 ^^ jw.2) * signVal (jw.2 ^^ (y'' i).2)
            else 0
          else (2 : ℝ) ^ k * (2 : ℝ) ^ k) =
        if i ∈ S then
          if (y i).1 = (y'' i).1 then
            (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y'' i).2)
          else 0
        else (2 * (k : ℝ)) * (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, ↓reduceIte]
        rw [Fintype.sum_prod_type]
        by_cases hj : (y i).1 = (y'' i).1
        · simp only [hj, ↓reduceIte]
          rw [Finset.sum_eq_single (y'' i).1]
          · simp only [and_self, ↓reduceIte, Fintype.sum_bool]
            have hsign : ∀ w : Bool, signVal ((y i).2 ^^ w) * signVal (w ^^ (y'' i).2) =
                signVal ((y i).2 ^^ (y'' i).2) := by
              intro w; cases (y i).2 <;> cases (y'' i).2 <;> cases w <;> norm_num
            simp only [mul_assoc, hsign]; ring
          · intro j _ hne; simp [hne]
          · simp
        · simp only [hj, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun w _ => ?_
          have : ¬ ((y i).1 = j ∧ j = (y'' i).1) := fun h => hj (h.1.trans h.2)
          simp [this]
      · simp only [hi, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
    simp_rw [h1d]
    by_cases hy : ∀ i ∈ S, (y i).1 = (y'' i).1
    · simp only [eq_true hy, ↓reduceIte]
      have hsplit : (∏ i : Fin n, if i ∈ S then
            if (y i).1 = (y'' i).1 then
              (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y'' i).2) else 0
          else (2 * (k : ℝ)) * (2 : ℝ) ^ k * (2 : ℝ) ^ k) =
          (∏ i ∈ S, ((2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k * signVal ((y i).2 ^^ (y'' i).2))) *
          (∏ i ∈ Finset.univ.filter (fun i => i ∉ S),
            ((2 * (k : ℝ)) * (2 : ℝ) ^ k * (2 : ℝ) ^ k)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
        congr 1
        · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          exact Finset.prod_congr rfl fun i hi => by simp [hi, hy i hi]
        · exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      rw [hsplit]
      have hcard_compl : (Finset.univ.filter fun i : Fin n => i ∉ S).card = n - #S := by
        rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, hcard_compl]
      have hle : #S ≤ n := by simpa using Finset.card_le_univ S
      have hscalar : ((2 : ℝ) ^ (k + 1)) ^ #S * ((2 : ℝ) ^ k) ^ #S *
          ((2 * (k : ℝ)) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S)) =
          c S * ((2 : ℝ) ^ k) ^ n := by
        simp only [c]
        have h2k : ((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ (n - #S) = ((2 : ℝ) ^ k) ^ n := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        have h2k2 : ((2 : ℝ) ^ (k + 1)) ^ #S = (2 : ℝ) ^ #S * ((2 : ℝ) ^ k) ^ #S := by
          rw [pow_succ, mul_pow, mul_comm]
        have h2n : (2 * (k : ℝ)) ^ (n - #S) * (2 : ℝ) ^ #S =
            (2 * (k : ℝ)) ^ n * (k : ℝ) ^ (-(#S : ℝ)) := by
          have hkpow : (k : ℝ) ^ (-(#S : ℝ)) = ((k : ℝ) ^ #S)⁻¹ := by
            rw [Real.rpow_neg hkpos.le, Real.rpow_natCast]
          rw [hkpow, mul_pow, mul_pow, mul_assoc, mul_comm ((k : ℝ) ^ (n - #S)),
            ← mul_assoc _ ((2 : ℝ) ^ #S), ← pow_add, Nat.sub_add_cancel hle, mul_assoc,
            show (k : ℝ) ^ n * ((k : ℝ) ^ #S)⁻¹ = (k : ℝ) ^ (n - #S) by
              rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hkpos.ne'), ← pow_add,
                Nat.sub_add_cancel hle]]
        have h2nk : ((2 : ℝ) ^ k) ^ n = (2 : ℝ) ^ (n * k) := by rw [← pow_mul, mul_comm]
        rw [h2k2]
        calc (2 : ℝ) ^ #S * ((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ #S *
              ((2 * (k : ℝ)) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S))
            = ((2 * (k : ℝ)) ^ (n - #S) * (2 : ℝ) ^ #S) *
              (((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ (n - #S)) *
              (((2 : ℝ) ^ k) ^ #S * ((2 : ℝ) ^ k) ^ (n - #S)) := by ring
          _ = (2 * (k : ℝ)) ^ n * (k : ℝ) ^ (-(#S : ℝ)) *
                (2 : ℝ) ^ (n * k) * ((2 : ℝ) ^ k) ^ n := by
              rw [h2n, h2k, h2nk]
          _ = (2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n *
                (k : ℝ) ^ (-(#S : ℝ)) * ((2 : ℝ) ^ k) ^ n := by
              ring
      calc ((2 : ℝ) ^ (k + 1)) ^ #S * ((2 : ℝ) ^ k) ^ #S *
            (∏ i ∈ S, signVal ((y i).2 ^^ (y'' i).2)) *
            ((2 : ℝ) ^ (n - #S) * (k : ℝ) ^ (n - #S) *
              ((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S))
          = ((2 : ℝ) ^ (k + 1)) ^ #S * ((2 : ℝ) ^ k) ^ #S *
            ((2 * (k : ℝ)) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S) * ((2 : ℝ) ^ k) ^ (n - #S)) *
            ∏ i ∈ S, signVal ((y i).2 ^^ (y'' i).2) := by rw [mul_pow]; ring
        _ = c S * (((2 : ℝ) ^ k) ^ n * ∏ i ∈ S, signVal ((y i).2 ^^ (y'' i).2)) := by
            rw [hscalar]; ring
    · simp only [hy, ↓reduceIte, mul_zero]
      push Not at hy; obtain ⟨i₀, hi₀, hne⟩ := hy
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀, hne])
  -- Define orthogonal symmetric idempotents `P S := (c S)⁻¹ • ((M S)ᵀ * M S)`.
  let P : Finset (Fin n) → Matrix (Fin n → Fin k × Bool) (Fin n → Fin k × Bool) ℝ :=
    fun S => (c S)⁻¹ • ((M S)ᵀ * M S)
  have hP_symm : ∀ S, (P S)ᵀ = P S := fun S => by
    simp [P, Matrix.transpose_smul, Matrix.transpose_mul]
  have hP_idem : ∀ S, P S * P S = P S := fun S => by
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, hP_sq, smul_smul]
    rw [inv_mul_cancel₀ (hc_pos S).ne', mul_one]
  have hMMT_orth : ∀ S T : Finset (Fin n), S ≠ T → M S * (M T)ᵀ = 0 := by
    intro S T hST
    have hdiff : ∃ i : Fin n, (i ∈ S ∧ i ∉ T) ∨ (i ∉ S ∧ i ∈ T) := by
      by_contra hall; push Not at hall
      apply hST; ext i; specialize hall i; tauto
    ext x x'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, M, patternMatrix,
      Matrix.of_apply, chi_eq_prod_signVal]
    have hfac : ∀ y : Fin n → Fin k × Bool,
        (∏ i ∈ S, signVal (indexGadget k (x i) (y i))) *
        (∏ i ∈ T, signVal (indexGadget k (x' i) (y i))) =
          ∏ i : Fin n,
            ((if i ∈ S then signVal (indexGadget k (x i) (y i)) else 1) *
             (if i ∈ T then signVal (indexGadget k (x' i) (y i)) else 1)) := by
      intro y
      rw [Finset.prod_mul_distrib]
      congr 1 <;> rw [Finset.prod_ite_mem, Finset.univ_inter]
    simp_rw [hfac]
    rw [← Fintype.prod_sum (fun (i : Fin n) (jw : Fin k × Bool) =>
      (if i ∈ S then signVal (indexGadget k (x i) jw) else 1) *
      (if i ∈ T then signVal (indexGadget k (x' i) jw) else 1))]
    obtain ⟨i₀, ⟨hiS, hiT⟩ | ⟨hiS, hiT⟩⟩ := hdiff
    · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      simp only [hiS, hiT, ↓reduceIte, mul_one, Fintype.sum_prod_type, Fintype.sum_bool,
        indexGadget, Bool.xor_true, Bool.xor_false, signVal_not]
      exact Finset.sum_eq_zero fun j _ => by ring
    · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      simp only [hiS, hiT, ↓reduceIte, one_mul, Fintype.sum_prod_type, Fintype.sum_bool,
        indexGadget, Bool.xor_true, Bool.xor_false, signVal_not]
      exact Finset.sum_eq_zero fun j _ => by ring
  have hP_disj : ∀ S T, S ≠ T → P S * P T = 0 := fun S T hST => by
    simp only [P, Matrix.smul_mul, Matrix.mul_smul]
    have h0 : ((M S)ᵀ * M S) * ((M T)ᵀ * M T) = 0 := by
      calc ((M S)ᵀ * M S) * ((M T)ᵀ * M T)
          = (M S)ᵀ * ((M S * (M T)ᵀ) * M T) := by simp [Matrix.mul_assoc]
        _ = 0 := by rw [hMMT_orth S T hST, Matrix.zero_mul, Matrix.mul_zero]
    simp [h0]
  -- Let `A := patternMatrix ψ = ∑ S, fourierCoeff ψ S • M S`.
  have hA_eq : patternMatrix (k := k) ψ = ∑ S : Finset (Fin n), fourierCoeff ψ S • M S := by
    ext x yw
    simp only [patternMatrix_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, M]
    exact (sum_fourierCoeff_mul_chi ψ _).symm
  have hATA : (patternMatrix (k := k) ψ)ᵀ * patternMatrix (k := k) ψ =
      ∑ S : Finset (Fin n), (fourierCoeff ψ S ^ 2 * c S) • P S := by
    rw [hA_eq, Matrix.transpose_sum, Matrix.sum_mul]
    simp_rw [Matrix.mul_sum, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_eq_single S]
    · simp only [P, smul_smul]
      congr 1; field_simp [(hc_pos S).ne']
    · intro T _ hTS; simp [hP_orth S T hTS.symm]
    · simp
  -- Spectral norm equals `√(sup_S (fourierCoeff ψ S ^ 2 * c S))`.
  set Bval := Finset.univ.sup' Finset.univ_nonempty fun S : Finset (Fin n) =>
    |fourierCoeff ψ S| * (k : ℝ) ^ (-(#S : ℝ) / 2)
  have hBval_nn : 0 ≤ Bval :=
    le_trans (by positivity) (Finset.le_sup' (fun S : Finset (Fin n) =>
      |fourierCoeff ψ S| * (k : ℝ) ^ (-(#S : ℝ) / 2)) (Finset.mem_univ ∅))
  have hbound_eq : ∀ S : Finset (Fin n),
      fourierCoeff ψ S ^ 2 * c S ≤
        ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval ^ 2 := by
    intro S
    have hle : |fourierCoeff ψ S| * (k : ℝ) ^ (-(#S : ℝ) / 2) ≤ Bval :=
      Finset.le_sup' (fun T : Finset (Fin n) =>
        |fourierCoeff ψ T| * (k : ℝ) ^ (-(#T : ℝ) / 2)) (Finset.mem_univ S)
    have hsq := pow_le_pow_left₀ (by positivity) hle 2
    have hksq : ((k : ℝ) ^ (-(#S : ℝ) / 2)) ^ 2 = (k : ℝ) ^ (-(#S : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]
      simp
    rw [mul_pow, sq_abs, hksq] at hsq
    simp only [c]
    have hpos : 0 ≤ (2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n := by positivity
    nlinarith
  -- Prove `‖patternMatrix ψ‖ ≤ √(...) * Bval` and `≥ √(...) * Bval`.
  have hupper : spectralNorm (patternMatrix (k := k) ψ) ≤
      Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval := by
    refine spectralNorm_le_of_mulVec_le (mul_nonneg (Real.sqrt_nonneg _) hBval_nn) fun v => ?_
    have hnorm_sq : ‖Matrix.toEuclideanLin (patternMatrix (k := k) ψ) v‖ ^ 2 ≤
        (Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖) ^ 2 := by
      have hlhs : ‖Matrix.toEuclideanLin (patternMatrix (k := k) ψ) v‖ ^ 2 =
          ∑ S : Finset (Fin n), (fourierCoeff ψ S ^ 2 * c S) *
            ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_toEuclideanLin_mul, hATA, map_sum,
          LinearMap.sum_apply, inner_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [map_smul, LinearMap.smul_apply, inner_smul_right]
        congr 1
        conv_lhs => rw [← hP_idem S, show P S * P S = (P S)ᵀ * P S by rw [hP_symm]]
        rw [← inner_toEuclideanLin_mul, real_inner_self_eq_norm_sq]
      have hsum_P : ∑ S : Finset (Fin n), ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        have hnn : 0 ≤ ‖v - ∑ S : Finset (Fin n), Matrix.toEuclideanLin (P S) v‖ ^ 2 := sq_nonneg _
        have hexp : ‖v - ∑ S : Finset (Fin n), Matrix.toEuclideanLin (P S) v‖ ^ 2 =
            ‖v‖ ^ 2 - ∑ S : Finset (Fin n), ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
            real_inner_self_eq_norm_sq, inner_sum, sum_inner, sum_inner]
          have hcross : ∑ S : Finset (Fin n),
              inner ℝ (Matrix.toEuclideanLin (P S) v)
                (∑ T : Finset (Fin n), Matrix.toEuclideanLin (P T) v) =
              ∑ S : Finset (Fin n), ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 := by
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [inner_sum, Finset.sum_eq_single S]
            · rw [real_inner_self_eq_norm_sq]
            · intro T _ hTS
              rw [inner_toEuclideanLin_mul, hP_symm S, hP_disj S T hTS.symm, map_zero,
                LinearMap.zero_apply, inner_zero_right]
            · simp
          have hPv : ∀ S : Finset (Fin n),
              inner ℝ v (Matrix.toEuclideanLin (P S) v) = ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 := by
            intro S
            conv_lhs => rw [← hP_idem S, show P S * P S = (P S)ᵀ * P S by rw [hP_symm]]
            rw [← inner_toEuclideanLin_mul, real_inner_self_eq_norm_sq]
          have hPv' : ∀ S : Finset (Fin n),
              inner ℝ (Matrix.toEuclideanLin (P S) v) v = ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 := by
            intro S; rw [real_inner_comm, hPv S]
          simp_rw [hPv, hPv', hcross]
          ring
        linarith
      rw [hlhs]
      calc ∑ S : Finset (Fin n), (fourierCoeff ψ S ^ 2 * c S) * ‖Matrix.toEuclideanLin (P S) v‖ ^ 2
          ≤ ∑ S : Finset (Fin n),
              (((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval ^ 2) *
                ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 :=
            Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (hbound_eq S) (sq_nonneg _)
        _ = (((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval ^ 2) *
              ∑ S : Finset (Fin n), ‖Matrix.toEuclideanLin (P S) v‖ ^ 2 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval ^ 2) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsum_P (by positivity)
        _ = (Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖) ^ 2 := by
            have hsq : Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) ^ 2 =
                (2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n := Real.sq_sqrt (by positivity)
            have h1 : (Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖) ^ 2 =
                Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) ^ 2 * Bval ^ 2 * ‖v‖ ^ 2 := by
              ring
            rw [h1, hsq]
    have hrhs : 0 ≤ Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖ := by positivity
    nlinarith [norm_nonneg (Matrix.toEuclideanLin (patternMatrix (k := k) ψ) v)]
  have hlower : Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval ≤
      spectralNorm (patternMatrix (k := k) ψ) := by
    obtain ⟨S₀, _, hS₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun S : Finset (Fin n) => |fourierCoeff ψ S| * (k : ℝ) ^ (-(#S : ℝ) / 2))
    let y₀ : Fin n → Fin k × Bool := fun _ => (⟨0, hk⟩, false)
    let v : EuclideanSpace ℝ (Fin n → Fin k × Bool) :=
      Matrix.toEuclideanLin (P S₀) (EuclideanSpace.single y₀ 1)
    have hv_norm_sq : ‖v‖ ^ 2 = (c S₀)⁻¹ * ((2 : ℝ) ^ k) ^ n := by
      have h1 : ‖v‖ ^ 2 = inner ℝ (EuclideanSpace.single y₀ 1)
          (Matrix.toEuclideanLin ((P S₀)ᵀ * P S₀) (EuclideanSpace.single y₀ 1)) := by
        rw [← real_inner_self_eq_norm_sq]
        exact inner_toEuclideanLin_mul (P S₀) (P S₀) (EuclideanSpace.single y₀ 1)
      rw [h1, hP_symm, hP_idem]
      have hdiag : inner ℝ (EuclideanSpace.single y₀ 1)
          (Matrix.toEuclideanLin (P S₀) (EuclideanSpace.single y₀ 1)) = P S₀ y₀ y₀ := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
          dotProduct, Pi.single_apply]
      rw [hdiag]
      simp [P, hMTM, y₀]
    have hv_pos : 0 < ‖v‖ := by
      have : 0 < ‖v‖ ^ 2 := by rw [hv_norm_sq]; positivity
      nlinarith [norm_nonneg v]
    have hAv_sq : ‖Matrix.toEuclideanLin (patternMatrix (k := k) ψ) v‖ ^ 2 =
        (fourierCoeff ψ S₀ ^ 2 * c S₀) * ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_toEuclideanLin_mul, hATA, map_sum,
        LinearMap.sum_apply, inner_sum, Finset.sum_eq_single S₀]
      · have hPv : Matrix.toEuclideanLin (P S₀) v = v := by
          simp only [v]
          have : Matrix.toEuclideanLin (P S₀) (Matrix.toEuclideanLin (P S₀)
              (EuclideanSpace.single y₀ 1)) =
              Matrix.toEuclideanLin (P S₀ * P S₀) (EuclideanSpace.single y₀ 1) := by
            change Matrix.toLpLin 2 2 (P S₀) (Matrix.toLpLin 2 2 (P S₀) _) = _
            rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
          rw [this, hP_idem]
        rw [map_smul, LinearMap.smul_apply, inner_smul_right, hPv, real_inner_self_eq_norm_sq]
      · intro T _ hTS
        have hTv : Matrix.toEuclideanLin (P T) v = 0 := by
          simp only [v]
          have : Matrix.toEuclideanLin (P T) (Matrix.toEuclideanLin (P S₀)
              (EuclideanSpace.single y₀ 1)) =
              Matrix.toEuclideanLin (P T * P S₀) (EuclideanSpace.single y₀ 1) := by
            change Matrix.toLpLin 2 2 (P T) (Matrix.toLpLin 2 2 (P S₀) _) = _
            rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
          rw [this, hP_disj T S₀ hTS, map_zero, LinearMap.zero_apply]
        rw [map_smul, LinearMap.smul_apply, inner_smul_right, hTv, inner_zero_right, mul_zero]
      · simp
    have hop := spectralNorm_mulVec_le (patternMatrix (k := k) ψ) v
    have hBval_sq : (Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval) ^ 2 =
        fourierCoeff ψ S₀ ^ 2 * c S₀ := by
      have hksq : ((k : ℝ) ^ (-(#S₀ : ℝ) / 2)) ^ 2 = (k : ℝ) ^ (-(#S₀ : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hkpos.le]
        simp
      have hsq : Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) ^ 2 =
          (2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n := Real.sq_sqrt (by positivity)
      dsimp only [Bval]
      rw [hS₀]
      have h1 : (Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) *
            (|fourierCoeff ψ S₀| * (k : ℝ) ^ (-(#S₀ : ℝ) / 2))) ^ 2 =
          Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) ^ 2 *
            |fourierCoeff ψ S₀| ^ 2 * ((k : ℝ) ^ (-(#S₀ : ℝ) / 2)) ^ 2 := by ring
      rw [h1, hsq, sq_abs, hksq]
      simp only [c]
      ring
    have hmul_sq : (Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖) ^ 2 ≤
        (spectralNorm (patternMatrix (k := k) ψ) * ‖v‖) ^ 2 := by
      rw [mul_pow, hBval_sq, ← hAv_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hop 2
    have hle_mul : Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖ ≤
        spectralNorm (patternMatrix (k := k) ψ) * ‖v‖ := by
      have ha : 0 ≤ Real.sqrt ((2 : ℝ) ^ (n * k) * (2 * (k : ℝ)) ^ n) * Bval * ‖v‖ := by positivity
      have hb : 0 ≤ spectralNorm (patternMatrix (k := k) ψ) * ‖v‖ :=
        mul_nonneg (spectralNorm_nonneg _) hv_pos.le
      nlinarith [ha, hb]
    exact le_of_mul_le_mul_right hle_mul hv_pos
  exact le_antisymm hupper hlower

end CslibFrontier.CommunicationComplexity
