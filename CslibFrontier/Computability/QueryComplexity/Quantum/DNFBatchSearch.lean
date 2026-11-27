/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.UnknownSearch
public import CslibFrontier.Logics.Propositional.DNF
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Benchmarks
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Dual
public import CslibFrontier.Computability.QueryComplexity.Quantum.QMA

import CslibFrontier.Computability.QueryComplexity.Quantum.Composition
import CslibFrontier.Computability.QueryComplexity.Quantum.Grover
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Grover-Based QMA Batch Verification of DNF Formulas

This module constructs the $O(k \sqrt{m})$-query QMA query protocol for batch verifying $m$
independent instances of an $s$-term, width-$k$ DNF formula $\varphi$ with witness length
$m \lceil \log_2 s \rceil$, perfect completeness, and soundness error at most $1/3$.

The prover sends one satisfied-term index per block ($m \lceil \log_2 s \rceil$ bits total); the
verifier runs `Cslib.Quantum.orSearch` to search for an unsatisfied claimed term among the $m$
blocks, evaluating each term's $k$-literal check with $2k$ controlled bit-oracle queries
(compute + uncompute).

## Main results

* `CslibFrontier.QueryComplexity.dnf_batch_qmaQueryProtocol`: constructive QMA query protocol for
  $\mathrm{AND}_m \circ \varphi^m$ with witness length `m * Nat.clog 2 s`, query complexity at most
  `16 * k * (Nat.sqrt m + 1)`, perfect completeness, and soundness error at most `1 / 3`.
-/

public section

open scoped BigOperators
open Finset Cslib Cslib.BitString Cslib.Quantum Cslib.Logic.PL

namespace CslibFrontier.QueryComplexity

private lemma hadCtrl_phaseOracle_bit {N : ℕ} {W : Type*} [Fintype W]
    (x : BitString N) (ψ : State N W) (p : Fin N × Bool × W) :
    (hadCtrl (phaseOracle x (hadCtrl ψ))).ofLp p =
      ψ.ofLp (p.1, p.2.1 ^^ x p.1, p.2.2) := by
  have h := hadCtrl_phaseOracle_hadCtrl_eq_permute x ψ
  rw [h, permute_apply]
  have hsymm : (bitFlip x).symm p = (p.1, p.2.1 ^^ x p.1, p.2.2) := by
    simp [bitFlip]
  rw [hsymm]

private def dnfSwapLitEquiv {m n w k : ℕ} [NeZero (m * n)] {WOr : Type*}
    (litAt : BitString w → Fin m → Fin k → Option (Fin n × Bool)) (r : Fin k) :
    Equiv.Perm (Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))) where
  toFun p :=
    let u := p.2.2.1
    let jOr := p.2.2.2.2.1
    let a := p.2.2.2.2.2.2
    match litAt u jOr r with
    | some (v, _) =>
      (p.1 + finProdFinEquiv (jOr, v), a r,
        (u, (p.2.2.2.1, jOr, p.2.2.2.2.2.1, Function.update a r p.2.1)))
    | none => p
  invFun p :=
    let u := p.2.2.1
    let jOr := p.2.2.2.2.1
    let a := p.2.2.2.2.2.2
    match litAt u jOr r with
    | some (v, _) =>
      (p.1 - finProdFinEquiv (jOr, v), a r,
        (u, (p.2.2.2.1, jOr, p.2.2.2.2.2.1, Function.update a r p.2.1)))
    | none => p
  left_inv := fun ⟨q, c, u, wor, jOr, cOr, a⟩ => by
    dsimp only; cases h : litAt u jOr r with
    | none => simp [h]
    | some vp => rcases vp with ⟨v, pol⟩; simp [h, add_sub_cancel_right, Function.update_idem]
  right_inv := fun ⟨q, c, u, wor, jOr, cOr, a⟩ => by
    dsimp only; cases h : litAt u jOr r with
    | none => simp [h]
    | some vp => rcases vp with ⟨v, pol⟩; simp [h, sub_add_cancel, Function.update_idem]

private noncomputable def dnfCondHad {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (litAt : BitString w → Fin m → Fin k → Option (Fin n × Bool)) (r : Fin k) :
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) ≃ₗᵢ[ℂ]
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) :=
  let Work' := WOr × Fin m × Bool × BitString k
  let toF (ψ : State (m * n) (BitString w × Work')) : State (m * n) (BitString w × Work') :=
    WithLp.toLp 2 fun p =>
      if (litAt p.2.2.1 p.2.2.2.2.1 r).isSome then (hadCtrl ψ).ofLp p else ψ.ofLp p
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]; norm_num
  have hinv : ∀ ψ, toF (toF ψ) = ψ := by
    intro ψ; ext ⟨q, c, u, wor, jOr, cOr, a⟩
    simp only [toF]
    split_ifs with h
    · simp only [hadCtrl_apply, h, ↓reduceIte]
      generalize (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = s at h2 ⊢
      cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] <;>
        first | linear_combination (2 * ψ.ofLp (q, false, u, wor, jOr, cOr, a)) * h2
              | linear_combination (2 * ψ.ofLp (q, true, u, wor, jOr, cOr, a)) * h2
    · rfl
  { toFun := toF
    invFun := toF
    map_add' := fun ψ₁ ψ₂ => by
      ext p; simp only [toF, PiLp.add_apply, map_add]; split_ifs <;> rfl
    map_smul' := fun c ψ => by
      ext p; simp only [toF, PiLp.smul_apply, map_smul, RingHom.id_apply]
      split_ifs <;> rfl
    left_inv := hinv
    right_inv := hinv
    norm_map' := fun ψ => by
      have hkey : ∀ a b : ℂ,
          ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a + -1 * b)‖ ^ 2 +
          ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a + 1 * b)‖ ^ 2 = ‖b‖ ^ 2 + ‖a‖ ^ 2 := by
        intro a b
        simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
          Real.sq_sqrt zero_le_two, neg_one_mul, one_mul, ← sub_eq_add_neg, Complex.sq_norm,
          Complex.normSq_add, Complex.normSq_sub]
        ring
      have hsq : ‖toF ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        conv_lhs => rw [Fintype.sum_prod_type]
        conv_rhs => rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun q _ => ?_
        conv_lhs => rw [Fintype.sum_prod_type, Fintype.sum_bool]
        conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_bool]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun uw _ => ?_
        simp only [toF, hadCtrl_apply]
        by_cases h : (litAt uw.1 uw.2.2.1 r).isSome = true
        · simp only [h, ↓reduceIte]; exact hkey _ _
        · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private lemma dnfCondHad_apply {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (litAt : BitString w → Fin m → Fin k → Option (Fin n × Bool)) (r : Fin k)
    (ψ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
    (p : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))) :
    (dnfCondHad litAt r ψ).ofLp p =
      if (litAt p.2.2.1 p.2.2.2.2.1 r).isSome then (hadCtrl ψ).ofLp p else ψ.ofLp p := rfl

private noncomputable def dnfEvalCheckPhase {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (checkAnc : BitString w → Fin m → BitString k → Bool) :
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) ≃ₗᵢ[ℂ]
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) :=
  let Work' := WOr × Fin m × Bool × BitString k
  let ph (p : Fin (m * n) × Bool × (BitString w × Work')) : ℂ :=
    if p.2.2.2.2.2.1 && checkAnc p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 then -1 else 1
  { toFun := fun ψ => WithLp.toLp 2 fun p => ph p * ψ.ofLp p
    invFun := fun ψ => WithLp.toLp 2 fun p => ph p * ψ.ofLp p
    map_add' := fun ψ₁ ψ₂ => by ext p; simp [mul_add]
    map_smul' := fun c ψ => by
      ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    left_inv := fun ψ => by
      ext p; simp only [← mul_assoc, ph]; split_ifs <;> simp
    right_inv := fun ψ => by
      ext p; simp only [← mul_assoc, ph]; split_ifs <;> simp
    norm_map' := fun ψ => by
      have hsq : ‖(WithLp.toLp 2 fun p => ph p * ψ.ofLp p :
            State (m * n) (BitString w × Work'))‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [PiLp.toLp_apply, norm_mul]; simp only [ph]; split_ifs <;> simp
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private lemma dnfEvalCheckPhase_apply {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (checkAnc : BitString w → Fin m → BitString k → Bool)
    (ψ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
    (p : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))) :
    (dnfEvalCheckPhase checkAnc ψ).ofLp p =
      (if p.2.2.2.2.2.1 && checkAnc p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 then -1 else 1) *
        ψ.ofLp p := rfl

private noncomputable def dnfLiftOr {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (V : State m WOr →ₗᵢ[ℂ] State m WOr) :
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) ≃ₗᵢ[ℂ]
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) :=
  let Work' := WOr × Fin m × Bool × BitString k
  let Ve : State m WOr ≃ₗᵢ[ℂ] State m WOr :=
    LinearIsometryEquiv.ofSurjective V (LinearMap.injective_iff_surjective.mp V.injective)
  let e : (Fin (m * n) × Bool × (BitString w × Work')) ≃
      (Fin (m * n) × Bool × BitString w × BitString k) × (Fin m × Bool × WOr) :=
    { toFun := fun p => ((p.1, p.2.1, p.2.2.1, p.2.2.2.2.2.2),
        (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1))
      invFun := fun q => (q.1.1, q.1.2.1, (q.1.2.2.1, (q.2.2.2, q.2.1, q.2.2.1, q.1.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let toF : State (m * n) (BitString w × Work') → State (m * n) (BitString w × Work') := fun ψ =>
    WithLp.toLp 2 fun p =>
      (Ve (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((e p).1, q)))).ofLp (e p).2
  let invF : State (m * n) (BitString w × Work') → State (m * n) (BitString w × Work') := fun ψ =>
    WithLp.toLp 2 fun p =>
      (Ve.symm (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((e p).1, q)))).ofLp (e p).2
  { toFun := toF
    invFun := invF
    map_add' := fun ψ₁ ψ₂ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (ψ₁ + ψ₂).ofLp (e.symm ((e p).1, q))) =
          (WithLp.toLp 2 fun q => ψ₁.ofLp (e.symm ((e p).1, q))) +
          (WithLp.toLp 2 fun q => ψ₂.ofLp (e.symm ((e p).1, q))) := rfl
      dsimp only [toF]; rw [h, map_add]; rfl
    map_smul' := fun c ψ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (c • ψ).ofLp (e.symm ((e p).1, q))) =
          c • (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((e p).1, q))) := rfl
      dsimp only [toF]; rw [h, map_smul]; rfl
    left_inv := fun ψ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (toF ψ).ofLp (e.symm ((e p).1, q))) =
          Ve (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((e p).1, q))) := by ext q; rfl
      simp only [invF, h, LinearIsometryEquiv.symm_apply_apply]; rfl
    right_inv := fun ψ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (invF ψ).ofLp (e.symm ((e p).1, q))) =
          Ve.symm (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((e p).1, q))) := by ext q; rfl
      simp only [toF, h, LinearIsometryEquiv.apply_symm_apply]; rfl
    norm_map' := fun ψ => by
      have hsq : ‖toF ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        dsimp only [toF]
        rw [Fintype.sum_equiv e
          (fun p => ‖(Ve (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((e p).1, q)))).ofLp
            (e p).2‖ ^ 2)
          (fun q => ‖(Ve (WithLp.toLp 2 fun s => ψ.ofLp (e.symm (q.1, s)))).ofLp q.2‖ ^ 2)
          (fun _ => rfl)]
        rw [Fintype.sum_equiv e (fun p => ‖ψ.ofLp p‖ ^ 2) (fun q => ‖ψ.ofLp (e.symm q)‖ ^ 2)
          (fun p => by simp)]
        conv_lhs => rw [Fintype.sum_prod_type]
        conv_rhs => rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun idx _ => ?_
        dsimp only
        rw [← EuclideanSpace.norm_sq_eq, Ve.norm_map, EuclideanSpace.norm_sq_eq]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private lemma dnfLiftOr_apply {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (V : State m WOr →ₗᵢ[ℂ] State m WOr)
    (ψ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
    (p : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))) :
    (dnfLiftOr V ψ).ofLp p =
      (V (WithLp.toLp 2 fun q =>
        ψ.ofLp (p.1, p.2.1, (p.2.2.1, (q.2.2, q.1, q.2.1, p.2.2.2.2.2.2))))).ofLp
        (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) := rfl

private noncomputable def dnfPrepOr {m : ℕ} {WOr : Type*} [Fintype WOr] [DecidableEq WOr]
    (initBasis : Fin m × Bool × WOr) (target : State m WOr) (htarget : ‖target‖ = 1) :
    State m WOr ≃ₗᵢ[ℂ] State m WOr :=
  let prepV : Submodule.span ℂ ({ket initBasis} : Set (State m WOr)) →ₗᵢ[ℂ] State m WOr :=
    { toFun := fun v => (inner ℂ (ket initBasis) v.1) • target
      map_add' := fun u v => by simp [inner_add_right, add_smul]
      map_smul' := fun c u => by simp [inner_smul_right, mul_smul]
      norm_map' := fun v => by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.2
        change ‖(inner ℂ (ket initBasis) v.1) • target‖ = ‖v.1‖
        rw [← hc, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_ket, RCLike.ofReal_one,
          one_pow, mul_one, norm_smul, norm_smul, htarget, norm_ket, mul_one] }
  LinearIsometryEquiv.ofSurjective prepV.extend
    (LinearMap.injective_iff_surjective.mp prepV.extend.injective)

private lemma dnfPrepOr_apply {m : ℕ} {WOr : Type*} [Fintype WOr] [DecidableEq WOr]
    (initBasis : Fin m × Bool × WOr) (target : State m WOr) (htarget : ‖target‖ = 1) :
    dnfPrepOr initBasis target htarget (ket initBasis) = target := by
  classical
  dsimp only [dnfPrepOr]
  change (LinearIsometry.extend _ (ket initBasis)) = target
  have hmem : ket initBasis ∈ Submodule.span ℂ ({ket initBasis} : Set (State m WOr)) :=
    Submodule.subset_span rfl
  have h1 := LinearIsometry.extend_apply
    ({ toFun := fun v : Submodule.span ℂ ({ket initBasis} : Set (State m WOr)) =>
          (inner ℂ (ket initBasis) v.1) • target
       map_add' := fun u v => by simp [inner_add_right, add_smul]
       map_smul' := fun c u => by simp [inner_smul_right, mul_smul]
       norm_map' := fun v => by
         obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.2
         change ‖(inner ℂ (ket initBasis) v.1) • target‖ = ‖v.1‖
         rw [← hc, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_ket, RCLike.ofReal_one,
           one_pow, mul_one, norm_smul, norm_smul, htarget, norm_ket, mul_one] } :
      Submodule.span ℂ ({ket initBasis} : Set (State m WOr)) →ₗᵢ[ℂ] State m WOr)
    ⟨ket initBasis, hmem⟩
  simp only [LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    inner_self_eq_norm_sq_to_K, norm_ket, one_pow, RCLike.ofReal_one, one_smul] at h1
  exact h1

private noncomputable def dnfEmbedFamily {m n w k : ℕ} {WOr : Type*}
    (p0 : Fin (m * n)) (F : BitString w → State m WOr) :
    State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)) :=
  WithLp.toLp 2 fun p =>
    if p.1 = p0 ∧ p.2.1 = false ∧ p.2.2.2.2.2.2 = (fun _ => false) then
      (F p.2.2.1).ofLp (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1)
    else 0

private lemma dnfLiftOr_embedFamily {m n w k : ℕ} {WOr : Type*} [Fintype WOr]
    (p0 : Fin (m * n)) (V : State m WOr →ₗᵢ[ℂ] State m WOr) (G : BitString w → State m WOr) :
    dnfLiftOr (m := m) (n := n) (w := w) (k := k) V (dnfEmbedFamily p0 G) =
      dnfEmbedFamily p0 (fun u => V (G u)) := by
  classical
  ext ⟨q, c, u, wor, jOr, cOr, a⟩
  simp only [dnfLiftOr_apply, dnfEmbedFamily]
  by_cases h : q = p0 ∧ c = false ∧ a = fun _ => false
  · simp only [h, and_self, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    have hzero : (WithLp.toLp 2 fun _ : Fin m × Bool × WOr => (0 : ℂ)) = 0 := rfl
    rw [hzero, map_zero]; rfl

private def dnfFlipAnc {m n w k : ℕ}
    (litAt : BitString w → Fin m → Fin k → Option (Fin n × Bool))
    (x : BitString (m * n)) (u : BitString w) (jOr : Fin m) (r : Fin k)
    (a : BitString k) : BitString k :=
  match litAt u jOr r with
  | some (v, _) => Function.update a r (a r ^^ x (finProdFinEquiv (jOr, v)))
  | none => a

private lemma dnfQueryBit_apply {m n w k : ℕ} [NeZero (m * n)] {WOr : Type*} [Fintype WOr]
    (litAt : BitString w → Fin m → Fin k → Option (Fin n × Bool))
    (p0 : Fin (m * n)) (hp0_zero : p0.1 = 0)
    (x : BitString (m * n)) (r : Fin k)
    (ξ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
    (hξ0 : ∀ p : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k)),
      (p.1 ≠ p0 ∨ p.2.1 ≠ false) → ξ.ofLp p = 0)
    (p : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))) :
    let stepPre := (permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).trans
      (dnfCondHad (m := m) (n := n) (WOr := WOr) litAt r)
    let stepPost := (dnfCondHad (m := m) (n := n) (WOr := WOr) litAt r).trans
      (permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).symm
    (stepPost (phaseOracle x (stepPre ξ))).ofLp p =
      if p.1 = p0 ∧ p.2.1 = false then
        ξ.ofLp (p0, false, (p.2.2.1, (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
          dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r p.2.2.2.2.2.2)))
      else 0 := by
  classical
  intro stepPre stepPost
  rcases p with ⟨q, c, u, wor, jOr, cOr, a⟩
  simp only [stepPost, stepPre, LinearIsometryEquiv.trans_apply]
  have hswapLit_symm : ∀ (ζ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
      (p' : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))),
      ((permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).symm ζ).ofLp p' =
        ζ.ofLp (dnfSwapLitEquiv (WOr := WOr) litAt r p') := fun ζ p' => by
    have h := congrArg (fun v => v.ofLp (dnfSwapLitEquiv (WOr := WOr) litAt r p'))
      ((permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).apply_symm_apply ζ)
    rw [permute_apply, Equiv.symm_apply_apply] at h; exact h
  have hcond_step : ∀ (p' : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k)))
      (ζ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k))),
      (dnfCondHad (WOr := WOr) litAt r (phaseOracle x (dnfCondHad (WOr := WOr) litAt r ζ))).ofLp
        p' =
        if (litAt p'.2.2.1 p'.2.2.2.2.1 r).isSome then
          ζ.ofLp (p'.1, p'.2.1 ^^ x p'.1, p'.2.2)
        else (if p'.2.1 && x p'.1 then -1 else 1) * ζ.ofLp p' := by
    intro ⟨q', c', u', wor', jOr', cOr', a'⟩ ζ
    simp only [dnfCondHad_apply]
    by_cases h : (litAt u' jOr' r).isSome = true
    · simp only [h, ↓reduceIte]
      have hagree : (hadCtrl (phaseOracle x (dnfCondHad (WOr := WOr) litAt r ζ))).ofLp
            (q', c', u', wor', jOr', cOr', a') =
          (hadCtrl (phaseOracle x (hadCtrl ζ))).ofLp (q', c', u', wor', jOr', cOr', a') := by
        simp only [hadCtrl_apply, phaseOracle_apply, dnfCondHad_apply, h, ↓reduceIte]
      rw [hagree, hadCtrl_phaseOracle_bit]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, phaseOracle_apply, dnfCondHad_apply]
  rw [hswapLit_symm]
  cases hlit : litAt u jOr r with
  | none =>
    have hsw : dnfSwapLitEquiv (WOr := WOr) litAt r (q, c, u, wor, jOr, cOr, a) =
        (q, c, u, wor, jOr, cOr, a) := by simp [dnfSwapLitEquiv, hlit]
    rw [hsw, hcond_step]
    simp only [hlit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, permute_apply]
    have hid : (dnfSwapLitEquiv (WOr := WOr) litAt r).symm (q, c, u, wor, jOr, cOr, a) =
        (q, c, u, wor, jOr, cOr, a) := by simp [dnfSwapLitEquiv, hlit]
    rw [hid]
    by_cases hqc : q = p0 ∧ c = false
    · rcases hqc with ⟨rfl, rfl⟩; simp [dnfFlipAnc, hlit]
    · have hor : q ≠ p0 ∨ c ≠ false := by by_contra h; push Not at h; exact hqc h
      simp only [hqc, ↓reduceIte, hξ0 (q, c, u, wor, jOr, cOr, a) hor, mul_zero]
  | some vp =>
    rcases vp with ⟨v, pol⟩
    have hsw : dnfSwapLitEquiv (WOr := WOr) litAt r (q, c, u, wor, jOr, cOr, a) =
        (q + finProdFinEquiv (jOr, v), a r, (u, (wor, jOr, cOr, Function.update a r c))) := by
      simp [dnfSwapLitEquiv, hlit]
    rw [hsw, hcond_step]
    simp only [hlit, Option.isSome_some, ↓reduceIte, permute_apply]
    have hback : (dnfSwapLitEquiv (WOr := WOr) litAt r).symm
        (q + finProdFinEquiv (jOr, v), a r ^^ x (q + finProdFinEquiv (jOr, v)),
          (u, (wor, jOr, cOr, Function.update a r c))) =
        (q, c, (u, (wor, jOr, cOr,
          Function.update a r (a r ^^ x (q + finProdFinEquiv (jOr, v)))))) := by
      simp [dnfSwapLitEquiv, hlit, add_sub_cancel_right, Function.update_idem]
    rw [hback]
    by_cases hqc : q = p0 ∧ c = false
    · rcases hqc with ⟨rfl, rfl⟩
      have hp0 : q + finProdFinEquiv (jOr, v) = finProdFinEquiv (jOr, v) := by
        ext; rw [Fin.val_add, hp0_zero, zero_add, Nat.mod_eq_of_lt (finProdFinEquiv (jOr, v)).2]
      simp [dnfFlipAnc, hlit, hp0]
    · have hor : q ≠ p0 ∨ c ≠ false := by by_contra h; push Not at h; exact hqc h
      simp only [hqc, ↓reduceIte,
        hξ0 (q, c, u, wor, jOr, cOr,
          Function.update a r (a r ^^ x (q + finProdFinEquiv (jOr, v)))) hor]

private noncomputable def dnfApplyQ {N : ℕ} {W : Type*} [Fintype W] {k : ℕ}
    (stepPre stepPost : Fin k → State N W ≃ₗᵢ[ℂ] State N W)
    (x : BitString N) : ℕ → State N W → State N W
  | 0, ζ => ζ
  | r + 1, ζ =>
    if hr : r < k then
      stepPost ⟨r, hr⟩ (phaseOracle x (stepPre ⟨r, hr⟩ (dnfApplyQ stepPre stepPost x r ζ)))
    else dnfApplyQ stepPre stepPost x r ζ

private lemma dnfApplyQ_zero {N : ℕ} {W : Type*} [Fintype W] {k : ℕ}
    (stepPre stepPost : Fin k → State N W ≃ₗᵢ[ℂ] State N W) (x : BitString N) (ζ : State N W) :
    dnfApplyQ stepPre stepPost x 0 ζ = ζ := rfl

private lemma dnfApplyQ_succ {N : ℕ} {W : Type*} [Fintype W] {k : ℕ}
    (stepPre stepPost : Fin k → State N W ≃ₗᵢ[ℂ] State N W) (x : BitString N) (r : ℕ)
    (ζ : State N W) :
    dnfApplyQ stepPre stepPost x (r + 1) ζ =
      if hr : r < k then
        stepPost ⟨r, hr⟩ (phaseOracle x (stepPre ⟨r, hr⟩ (dnfApplyQ stepPre stepPost x r ζ)))
      else dnfApplyQ stepPre stepPost x r ζ := rfl

private lemma dnfPrefixBits_apply {m n w k : ℕ} [NeZero (m * n)] {WOr : Type*} [Fintype WOr]
    (litAt : BitString w → Fin m → Fin k → Option (Fin n × Bool))
    (p0 : Fin (m * n)) (hp0_zero : p0.1 = 0)
    (x : BitString (m * n)) (t : ℕ) (ht : t ≤ k)
    (a₀ : BitString w → Fin m → BitString k) (F : BitString w → State m WOr)
    (ξ : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
    (hξ : ∀ p, ξ.ofLp p =
      if p.1 = p0 ∧ p.2.1 = false ∧ p.2.2.2.2.2.2 = a₀ p.2.2.1 p.2.2.2.2.1 then
        (F p.2.2.1).ofLp (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) else 0)
    (ξ' : State (m * n) (BitString w × (WOr × Fin m × Bool × BitString k)))
    (hξ' : dnfApplyQ
      (fun r => (permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).trans
        (dnfCondHad (WOr := WOr) litAt r))
      (fun r => (dnfCondHad (WOr := WOr) litAt r).trans
        (permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).symm) x t ξ = ξ') :
    ∀ p : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k)),
      ξ'.ofLp p =
        if p.1 = p0 ∧ p.2.1 = false ∧
            p.2.2.2.2.2.2 = (fun r : Fin k => if r.1 < t then
              dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r (a₀ p.2.2.1 p.2.2.2.2.1) r
            else a₀ p.2.2.1 p.2.2.2.2.1 r) then
          (F p.2.2.1).ofLp (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) else 0 := by
  classical
  induction t generalizing ξ' with
  | zero =>
    intro p
    rw [← hξ']; simp only [dnfApplyQ_zero, hξ]
    have : (fun r : Fin k => if r.1 < 0 then
        dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r (a₀ p.2.2.1 p.2.2.2.2.1) r
      else a₀ p.2.2.1 p.2.2.2.2.1 r) = a₀ p.2.2.1 p.2.2.2.2.1 := by funext r; simp
    rw [this]
  | succ t ih =>
    intro p
    have ht' : t < k := by omega
    let stepPre (r : Fin k) := (permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).trans
      (dnfCondHad (WOr := WOr) litAt r)
    let stepPost (r : Fin k) := (dnfCondHad (WOr := WOr) litAt r).trans
      (permute (dnfSwapLitEquiv (WOr := WOr) litAt r)).symm
    let ζ := dnfApplyQ stepPre stepPost x t ξ
    have hζ := ih (by omega) ζ rfl
    have hζ0 : ∀ q : Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k)),
        (q.1 ≠ p0 ∨ q.2.1 ≠ false) → ζ.ofLp q = 0 := by
      intro q hq; rw [hζ]; rcases hq with hq | hq <;> simp [hq]
    rw [← hξ']; simp only [dnfApplyQ_succ, ht', ↓reduceDIte]
    rw [dnfQueryBit_apply litAt p0 hp0_zero x ⟨t, ht'⟩ ζ hζ0 p]
    by_cases hqc : p.1 = p0 ∧ p.2.1 = false
    · simp only [hqc, ↓reduceIte, hζ, true_and]
      have hfl : (dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ p.2.2.2.2.2.2 =
          fun r : Fin k => if r.1 < t then
            dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r (a₀ p.2.2.1 p.2.2.2.2.1) r
          else a₀ p.2.2.1 p.2.2.2.2.1 r) ↔
          (p.2.2.2.2.2.2 = fun r : Fin k => if r.1 < t + 1 then
            dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r (a₀ p.2.2.1 p.2.2.2.2.1) r
          else a₀ p.2.2.1 p.2.2.2.2.1 r) := by
        constructor <;> intro heq <;> funext r
        · have hr := congr_fun heq r
          by_cases hrt : r.1 < t
          · have hne : r ≠ ⟨t, ht'⟩ := by simp [Fin.ext_iff]; omega
            simp only [dnfFlipAnc] at hr ⊢
            cases hlit : litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
            | none => simpa [hlit, hrt, show r.1 < t + 1 by omega] using hr
            | some vp =>
              rcases vp with ⟨v, pol⟩
              simpa [hlit, Function.update_of_ne hne, hrt, show r.1 < t + 1 by omega] using hr
          · by_cases hreq : r.1 = t
            · have hrt' : r = ⟨t, ht'⟩ := Fin.ext hreq
              subst hrt'
              simp only [dnfFlipAnc] at hr ⊢
              cases hlit : litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
              | none => simpa [hlit] using hr
              | some vp =>
                rcases vp with ⟨v, pol⟩
                simp only [hlit, Function.update_self, Nat.lt_irrefl, ↓reduceIte,
                  Nat.lt_succ_self] at hr ⊢
                have hxor := congrArg (· ^^ x (finProdFinEquiv (p.2.2.2.2.1, v))) hr
                simpa [Bool.xor_assoc] using hxor
            · have hne : r ≠ ⟨t, ht'⟩ := by simp [Fin.ext_iff]; omega
              have hgt : ¬ r.1 < t + 1 := by omega
              simp only [dnfFlipAnc] at hr ⊢
              cases hlit : litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
              | none => simpa [hlit, hrt, hgt] using hr
              | some vp =>
                rcases vp with ⟨v, pol⟩
                simpa [hlit, Function.update_of_ne hne, hrt, hgt] using hr
        · rw [heq]
          have houter : ∀ a : BitString k, dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ a r =
              match litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
              | some (v, _) =>
                Function.update a ⟨t, ht'⟩
                  (a ⟨t, ht'⟩ ^^ x (finProdFinEquiv (p.2.2.2.2.1, v))) r
              | none => a r := fun a => by
            dsimp only [dnfFlipAnc]
            cases litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ <;> rfl
          rw [houter]
          by_cases hrt : r.1 < t
          · have hne : r ≠ ⟨t, ht'⟩ := by simp [Fin.ext_iff]; omega
            have hlt1 : r.1 < t + 1 := by omega
            cases hlit : litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
            | none => simp only [hrt, hlt1, ↓reduceIte]
            | some vp =>
              rcases vp with ⟨v, pol⟩
              simp only [Function.update_of_ne hne, hrt, hlt1, ↓reduceIte]
          · by_cases hreq : r.1 = t
            · have hrt' : r = ⟨t, ht'⟩ := Fin.ext hreq
              subst hrt'
              cases hlit : litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
              | none => simp [dnfFlipAnc, hlit]
              | some vp =>
                rcases vp with ⟨v, pol⟩
                simp [dnfFlipAnc, hlit, Function.update_self]
            · have hne : r ≠ ⟨t, ht'⟩ := by simp [Fin.ext_iff]; omega
              have hgt : ¬ r.1 < t + 1 := by omega
              cases hlit : litAt p.2.2.1 p.2.2.2.2.1 ⟨t, ht'⟩ with
              | none => simp only [hrt, hgt, ↓reduceIte]
              | some vp =>
                rcases vp with ⟨v, pol⟩
                simp only [Function.update_of_ne hne, hrt, hgt, ↓reduceIte]
      by_cases hcond : p.2.2.2.2.2.2 = fun r : Fin k => if r.1 < t + 1 then
          dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r (a₀ p.2.2.1 p.2.2.2.2.1) r
        else a₀ p.2.2.1 p.2.2.2.2.1 r
      · simp only [hfl.mpr hcond, ↓reduceIte]
        simp only [hcond, ↓reduceIte]
      · simp only [mt hfl.mp hcond, ↓reduceIte]
        simp only [hcond, ↓reduceIte]
    · have hqc' : ¬ (p.1 = p0 ∧ p.2.1 = false ∧
          p.2.2.2.2.2.2 = fun r : Fin k => if r.1 < t + 1 then
            dnfFlipAnc litAt x p.2.2.1 p.2.2.2.2.1 r (a₀ p.2.2.1 p.2.2.2.2.1) r
          else a₀ p.2.2.1 p.2.2.2.2.1 r) := fun h => hqc ⟨h.1, h.2.1⟩
      simp only [hqc, hqc', ↓reduceIte]

private lemma dnfMeasureProb_embedFamily {m n w k : ℕ}
    (hm : 1 ≤ m) (p0 : Fin (m * n)) (badTerm : BitString w → Fin m → Bool)
    (TOr : ℕ) (ψ : EuclideanSpace ℂ (BitString w))
    (acc : Finset (Fin (m * n) × Bool ×
      (BitString w ×
        (((Unit × Fin (orRange m)) × QueryBasis m (Unit × Fin (orRange m))) ×
          Fin m × Bool × BitString k))))
    (hacc : ∀ p, p ∈ acc ↔ (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) ∉ orAccept m) :
    measureProb
      (dnfEmbedFamily (k := k)
        (WOr := (Unit × Fin (orRange m)) × QueryBasis m (Unit × Fin (orRange m))) p0
        (fun u =>
          ψ.ofLp u • Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr))
      acc =
      ∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2 *
        (1 - measureProb (Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr)
          (orAccept m)) := by
  classical
  let WOr := (Unit × Fin (orRange m)) × QueryBasis m (Unit × Fin (orRange m))
  rw [measureProb, show acc = Finset.univ.filter (fun p => p ∈ acc) by ext p; simp,
    Finset.sum_filter]
  simp only [hacc, dnfEmbedFamily]
  let e : (Fin (m * n) × Bool × (BitString w × (WOr × Fin m × Bool × BitString k))) ≃
      (Fin (m * n) × Bool × BitString k) × BitString w × (Fin m × Bool × WOr) :=
    { toFun := fun p => ((p.1, p.2.1, p.2.2.2.2.2.2), (p.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1,
        p.2.2.2.1)))
      invFun := fun q => (q.1.1, q.1.2.1, (q.2.1, (q.2.2.2.2, q.2.2.1, q.2.2.2.1, q.1.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.sum_equiv e
    (fun p => if (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) ∉ orAccept m then
        ‖if p.1 = p0 ∧ p.2.1 = false ∧ p.2.2.2.2.2.2 = (fun _ => false) then
          (ψ.ofLp p.2.2.1 • Cslib.Quantum.run (orSearch m) (orSearchInit m)
            (badTerm p.2.2.1) TOr).ofLp (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1)
        else 0‖ ^ 2
      else 0)
    (fun q => if q.2.2 ∉ orAccept m then
        ‖if q.1.1 = p0 ∧ q.1.2.1 = false ∧ q.1.2.2 = (fun _ => false) then
          (ψ.ofLp q.2.1 • Cslib.Quantum.run (orSearch m) (orSearchInit m)
            (badTerm q.2.1) TOr).ofLp q.2.2
        else 0‖ ^ 2
      else 0)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (p0, false, fun _ => false) (fun idx _ hidx => by
    refine Finset.sum_eq_zero fun uq _ => ?_
    have hnot : ¬ (idx.1 = p0 ∧ idx.2.1 = false ∧ idx.2.2 = fun _ => false) := fun h =>
      hidx (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
    simp [hnot]) (by simp)]
  simp only [true_and, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hnorm_run : ∑ q : Fin m × Bool × WOr,
      ‖(Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr).ofLp q‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, norm_run, norm_orSearchInit hm, one_pow]
  have hcompl := Finset.sum_filter_add_sum_filter_not Finset.univ (fun q => q ∈ orAccept m)
    (fun q => ‖(Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr).ofLp q‖ ^ 2)
  rw [hnorm_run] at hcompl
  have hmul : ∑ q : Fin m × Bool × WOr,
      (if q ∉ orAccept m then
        ‖(ψ.ofLp u • Cslib.Quantum.run (orSearch m) (orSearchInit m)
          (badTerm u) TOr).ofLp q‖ ^ 2
      else 0) =
      ‖ψ.ofLp u‖ ^ 2 * ∑ q : Fin m × Bool × WOr with q ∉ orAccept m,
        ‖(Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr).ofLp q‖ ^ 2 := by
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp [PiLp.smul_apply, mul_pow]
  rw [hmul]; congr 1
  change ∑ q ∈ Finset.univ.filter (fun q => ¬ q ∈ orAccept m), _ = _
  linarith [show measureProb (Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr)
    (orAccept m) = ∑ q ∈ Finset.univ.filter (fun q => q ∈ orAccept m),
      ‖(Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u) TOr).ofLp q‖ ^ 2 by
    simp [measureProb]]

/-- Constructive QMA query protocol for batch-verifying $m$ copies of a width-$k$, size-$\le s$
DNF formula $\varphi$ on `Fin n` ($m, n \ge 1$): witness length `m * Nat.clog 2 s`, query
complexity at most `16 * k * (Nat.sqrt m + 1)`, completeness error `0`, soundness error `1 / 3`. -/
theorem dnf_batch_qmaQueryProtocol {m n s k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (φ : DNF (Fin n)) (hlen : φ.length ≤ s) (hwidth : ∀ t ∈ φ, t.length ≤ k) :
    ∃ P : QMAQueryProtocol (m * n) (m * Nat.clog 2 s),
      P.Computes (blockComp (threshold m m) (fun x => φ.eval x)) 0 (1 / 3) ∧
      P.queries ≤ 16 * k * (Nat.sqrt m + 1) := by
  classical
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have : NeZero (m * n) := ⟨hmn.ne'⟩
  let p0 : Fin (m * n) := ⟨0, hmn⟩
  by_cases hφ0 : φ.length = 0
  · have hnil : φ = [] := List.eq_nil_of_length_eq_zero hφ0
    refine ⟨{
      Work := Unit
      queries := 0
      unitary := fun _ => LinearIsometryEquiv.refl ℂ _
      initWork := (p0, false, ())
      accept := ∅ }, ?_, Nat.zero_le _⟩
    constructor
    · intro x hx
      exfalso
      have hff : blockComp (threshold m m) (fun y => φ.eval y) x = false := by
        simp only [blockComp_apply, hnil, DNF.eval_nil, threshold_apply, decide_eq_false_iff_not,
          not_le]
        have hw0 : weight (fun _ : Fin m => false) = 0 := by simp [weight]
        rw [hw0]; omega
      rw [hff] at hx; exact Bool.false_ne_true hx
    · intro x _ ψ _; simp [QMAQueryProtocol.acceptProb_eq_measureProb, measureProb]
  have hφpos : 0 < φ.length := Nat.pos_of_ne_zero hφ0
  by_cases hk0 : k = 0
  · subst hk0
    have htrue : ∀ y : BitString n, φ.eval y = true := by
      intro y
      rw [DNF.eval_eq_true_iff]
      let t0 := φ[0]'hφpos
      have ht0_mem : t0 ∈ φ := List.getElem_mem hφpos
      have ht0_len : t0.length = 0 := Nat.le_zero.mp (hwidth t0 ht0_mem)
      refine ⟨t0, ht0_mem, ?_⟩
      rw [List.eq_nil_of_length_eq_zero ht0_len, Term.eval_nil]
    refine ⟨{
      Work := Unit
      queries := 0
      unitary := fun _ => LinearIsometryEquiv.refl ℂ _
      initWork := (p0, false, ())
      accept := Finset.univ }, ?_, by simp⟩
    constructor
    · intro x _
      refine ⟨ket (fun _ => false), norm_ket _, ?_⟩
      rw [QMAQueryProtocol.acceptProb_eq_measureProb, measureProb_univ,
        QMAQueryProtocol.runState_eq_run, Cslib.Quantum.run, LinearIsometry.norm_map,
        QMAQueryProtocol.norm_embedWitness, norm_ket]
      norm_num
    · intro x hx
      exfalso
      have hall : blockComp (threshold m m) (fun y => φ.eval y) x = true := by
        simp only [blockComp_apply, htrue, threshold_apply, decide_eq_true_eq]
        have : weight (fun _ : Fin m => true) = m := by simp [weight]
        rw [this]
      rw [hall] at hx; exact Bool.false_ne_true hx.symm
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  -- Main case: `1 ≤ m`, `1 ≤ n`, `1 ≤ k`, `1 ≤ φ.length ≤ s`.
  let b := Nat.clog 2 s
  let w := m * b
  have hpow_ge : φ.length ≤ 2 ^ b := hlen.trans (Nat.le_pow_clog (by norm_num) s)
  let termIdx (u : BitString w) (j : Fin m) : Fin φ.length :=
    let v := (decodeFin b (fun r => u (finProdFinEquiv (j, r)))).1
    if h : v < φ.length then ⟨v, h⟩ else ⟨0, hφpos⟩
  let badTerm (u : BitString w) (x : BitString (m * n)) (j : Fin m) : Bool :=
    !((φ[termIdx u j]).eval (fun r => x (finProdFinEquiv (j, r))))
  let litAt (u : BitString w) (j : Fin m) (r : Fin k) : Option (Fin n × Bool) :=
    let t := φ[termIdx u j]
    if h : r.1 < t.length then some (t[r.1]'h) else none
  let WOr := (Unit × Fin (orRange m)) × QueryBasis m (Unit × Fin (orRange m))
  let Work' := WOr × Fin m × Bool × BitString k
  let TOr := orRange m + orRange m
  let totalQ := 2 * k * TOr
  have htotalQ : totalQ = 16 * k * (Nat.sqrt m + 1) := by
    simp only [totalQ, TOr, orRange]; ring
  have hTOr_pos : 0 < TOr := by simp only [TOr, orRange]; omega
  -- Swap `(q_reg, ctrl)` with `(q_reg + finProdFinEquiv (jOr, v), a r)` when `litAt u jOr r =
  -- some`.
  let swapLitEquiv (r : Fin k) := dnfSwapLitEquiv (WOr := WOr) litAt r
  let swapLit (r : Fin k) :
      State (m * n) (BitString w × Work') ≃ₗᵢ[ℂ] State (m * n) (BitString w × Work') :=
    permute (swapLitEquiv r)
  have hswapLit_symm_apply : ∀ (r : Fin k) (ζ : State (m * n) (BitString w × Work'))
      (p : Fin (m * n) × Bool × (BitString w × Work')),
      ((swapLit r).symm ζ).ofLp p = ζ.ofLp (swapLitEquiv r p) := fun r ζ p => by
    have h := congrArg (fun v => v.ofLp (swapLitEquiv r p)) ((swapLit r).apply_symm_apply ζ)
    rw [show (swapLit r) ((swapLit r).symm ζ) = permute (swapLitEquiv r) ((swapLit r).symm ζ)
        from rfl,
      permute_apply, Equiv.symm_apply_apply] at h
    exact h
  let condHad (r : Fin k) := dnfCondHad (m := m) (n := n) (WOr := WOr) litAt r
  have hcondHad_apply := dnfCondHad_apply (m := m) (n := n) (WOr := WOr) litAt
  let checkAnc (u : BitString w) (jOr : Fin m) (a : BitString k) : Bool :=
    let t := φ[termIdx u jOr]
    !(decide (∀ r : Fin k, ∀ hr : r.1 < t.length, a r = (t[r.1]'hr).2))
  let evalCheckPhase := dnfEvalCheckPhase (m := m) (n := n) (WOr := WOr) checkAnc
  have hevalCheckPhase_apply := dnfEvalCheckPhase_apply (m := m) (n := n) (WOr := WOr) checkAnc
  let liftOr (V : State m WOr →ₗᵢ[ℂ] State m WOr) := dnfLiftOr (m := m) (n := n) (w := w) (k := k) V
  have hliftOr_apply := dnfLiftOr_apply (m := m) (n := n) (w := w) (k := k) (WOr := WOr)
  let j0 : Fin m := ⟨0, hm⟩
  let wor0 : WOr := (((), ⟨0, Nat.mul_pos (by decide) (Nat.succ_pos _)⟩),
    ⟨j0, false, ((), ⟨0, Nat.mul_pos (by decide) (Nat.succ_pos _)⟩)⟩)
  let initBasis : Fin m × Bool × WOr := (j0, false, wor0)
  let prepOr : State m WOr ≃ₗᵢ[ℂ] State m WOr :=
    dnfPrepOr initBasis (orSearchInit m) (norm_orSearchInit hm)
  have hprepOr : prepOr (ket initBasis) = orSearchInit m :=
    dnfPrepOr_apply initBasis (orSearchInit m) (norm_orSearchInit hm)
  let stepPre (r : Fin k) := (swapLit r).trans (condHad r)
  let stepPost (r : Fin k) := (condHad r).trans (swapLit r).symm
  let blockMid (s : ℕ) :
      State (m * n) (BitString w × Work') ≃ₗᵢ[ℂ] State (m * n) (BitString w × Work') :=
    if h1 : 1 ≤ s ∧ s < k then
      (stepPost ⟨s - 1, by omega⟩).trans (stepPre ⟨s, h1.2⟩)
    else if h2 : s = k then
      (stepPost ⟨k - 1, by omega⟩).trans (evalCheckPhase.trans (stepPre ⟨0, hkpos⟩))
    else if h3 : k < s ∧ s < 2 * k then
      (stepPost ⟨s - k - 1, by omega⟩).trans (stepPre ⟨s - k, by omega⟩)
    else
      LinearIsometryEquiv.refl ℂ _
  let fullU (t : ℕ) :
      State (m * n) (BitString w × Work') ≃ₗᵢ[ℂ] State (m * n) (BitString w × Work') :=
    if t = 0 then
      ((liftOr prepOr.toLinearIsometry).trans (liftOr (orSearch m 0))).trans (stepPre ⟨0, hkpos⟩)
    else if t < totalQ then
      let s := t % (2 * k)
      let j := t / (2 * k)
      if s = 0 then
        ((stepPost ⟨k - 1, by omega⟩).trans (liftOr (orSearch m j))).trans (stepPre ⟨0, hkpos⟩)
      else
        blockMid s
    else if t = totalQ then
      (stepPost ⟨k - 1, by omega⟩).trans (liftOr (orSearch m TOr))
    else
      LinearIsometryEquiv.refl ℂ _
  let P : QMAQueryProtocol (m * n) w :=
    { Work := Work'
      queries := totalQ
      unitary := fullU
      initWork := (p0, false, (wor0, j0, false, fun _ => false))
      accept := Finset.univ.filter fun p =>
        (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) ∉ orAccept m }
  refine ⟨P, ?_, by dsimp only [P]; rw [htotalQ]⟩
  let embedFamily : (BitString w → State m WOr) → State (m * n) (BitString w × Work') :=
    dnfEmbedFamily p0
  let flipAnc := dnfFlipAnc litAt
  let applyQ := dnfApplyQ stepPre stepPost
  have hprefix_bits := dnfPrefixBits_apply (WOr := WOr) litAt p0 rfl
  -- Prove the clean two-phase induction for any `ψ : EuclideanSpace ℂ (BitString w)`.
  have hcircuit : ∀ (x : BitString (m * n)) (ψ : EuclideanSpace ℂ (BitString w)),
      P.runState x ψ =
        embedFamily (fun u =>
          ψ.ofLp u • Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u x) TOr) := by
    intro x ψ
    let F (j : ℕ) (u : BitString w) : State m WOr :=
      ψ.ofLp u • Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u x) j
    -- Helper: `stepPost (k-1) (phaseOracle x (...))` after one `2*k`-query block starting from
    -- `stepPre 0 (embedFamily G)` at step `2 * k * j` equals `embedFamily (fun u => phaseOracle
    -- (badTerm u x) (G u))`!
    have hblock : ∀ (j : ℕ) (hj : j < TOr) (G : BitString w → State m WOr),
        Cslib.Quantum.run (fun s => (fullU s).toLinearIsometry) (P.embedWitness ψ) x (2 * k * j) =
          stepPre ⟨0, hkpos⟩ (embedFamily G) →
        stepPost ⟨k - 1, by omega⟩ (phaseOracle x
          (Cslib.Quantum.run (fun s => (fullU s).toLinearIsometry) (P.embedWitness ψ) x
            (2 * k * j + (2 * k - 1)))) =
          embedFamily (fun u => phaseOracle (badTerm u x) (G u)) := by
      intro j hj G hstart
      -- First half (`s < k`): state at `2 * k * j + s` is `stepPre s (applyQ x s (embedFamily G))`.
      have hhalf1 : ∀ (s : ℕ) (hs : s < k),
          Cslib.Quantum.run (fun t => (fullU t).toLinearIsometry) (P.embedWitness ψ) x
            (2 * k * j + s) = stepPre ⟨s, hs⟩ (applyQ x s (embedFamily G)) := by
        intro s; induction s with
        | zero => intro _; simpa [applyQ, dnfApplyQ_zero] using hstart
        | succ s ihs =>
          intro hs
          rw [show 2 * k * j + (s + 1) = (2 * k * j + s) + 1 by omega]
          simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
          rw [ihs (by omega), show 2 * k * j + s + 1 = 2 * k * j + (s + 1) by omega]
          have hlt : 2 * k * j + (s + 1) < totalQ := by
            have hmul : 2 * k * j + 2 * k ≤ totalQ := by
              calc 2 * k * j + 2 * k = 2 * k * (j + 1) := by ring
                _ ≤ 2 * k * TOr := Nat.mul_le_mul_left _ hj
            omega
          have hmod : (2 * k * j + (s + 1)) % (2 * k) = s + 1 := by
            rw [show 2 * k * j + (s + 1) = (s + 1) + (2 * k) * j by ring,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          have hmid : fullU (2 * k * j + (s + 1)) =
              (stepPost ⟨s, by omega⟩).trans (stepPre ⟨s + 1, hs⟩) := by
            have h1s : 1 ≤ s + 1 ∧ s + 1 < k := ⟨by omega, hs⟩
            simp only [fullU, show 2 * k * j + (s + 1) ≠ 0 by omega, hlt, ↓reduceIte, hmod,
              show s + 1 ≠ 0 by omega, blockMid, h1s, and_self, ↓reduceDIte,
              show s + 1 - 1 = s by omega]
          rw [hmid, LinearIsometryEquiv.trans_apply]
          simp only [applyQ, dnfApplyQ_succ, show s < k by omega, ↓reduceDIte]
      -- After `s = k - 1`, applying `phaseOracle x`, `stepPost (k-1)`, `evalCheckPhase` gives
      -- `evalCheckPhase (applyQ x k (embedFamily G))`.
      let midState := evalCheckPhase (applyQ x k (embedFamily G))
      have hmid_at : Cslib.Quantum.run (fun t => (fullU t).toLinearIsometry) (P.embedWitness ψ) x
          (2 * k * j + k) = stepPre ⟨0, hkpos⟩ midState := by
        rw [show 2 * k * j + k = (2 * k * j + (k - 1)) + 1 by omega]
        simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
        rw [hhalf1 (k - 1) (by omega), show 2 * k * j + (k - 1) + 1 = 2 * k * j + k by omega]
        have hlt : 2 * k * j + k < totalQ := by
          have hmul : 2 * k * j + 2 * k ≤ totalQ := by
            calc 2 * k * j + 2 * k = 2 * k * (j + 1) := by ring
              _ ≤ 2 * k * TOr := Nat.mul_le_mul_left _ hj
          omega
        have hmod : (2 * k * j + k) % (2 * k) = k := by
          rw [show 2 * k * j + k = k + (2 * k) * j by ring,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        have hstepk : fullU (2 * k * j + k) =
            (stepPost ⟨k - 1, by omega⟩).trans (evalCheckPhase.trans (stepPre ⟨0, hkpos⟩)) := by
          simp only [fullU, show 2 * k * j + k ≠ 0 by omega, hlt, ↓reduceIte, hmod, hkpos.ne',
            blockMid, show ¬ (1 ≤ k ∧ k < k) by omega, ↓reduceDIte, eq_self]
        rw [hstepk, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply]
        have hkeq : applyQ x k (embedFamily G) =
            stepPost ⟨k - 1, by omega⟩ (phaseOracle x (stepPre ⟨k - 1, by omega⟩
              (applyQ x (k - 1) (embedFamily G)))) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          simp only [applyQ, dnfApplyQ_succ, show k - 1 < k by omega, ↓reduceDIte]
        rw [← hkeq]
      -- Second half (`s < k`): state at `2 * k * j + k + s` is `stepPre s (applyQ x s midState)`.
      have hhalf2 : ∀ (s : ℕ) (hs : s < k),
          Cslib.Quantum.run (fun t => (fullU t).toLinearIsometry) (P.embedWitness ψ) x
            (2 * k * j + k + s) = stepPre ⟨s, hs⟩ (applyQ x s midState) := by
        intro s; induction s with
        | zero => intro _; simpa [applyQ, dnfApplyQ_zero] using hmid_at
        | succ s ihs =>
          intro hs
          rw [show 2 * k * j + k + (s + 1) = (2 * k * j + k + s) + 1 by omega]
          simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
          rw [ihs (by omega), show 2 * k * j + k + s + 1 = 2 * k * j + k + (s + 1) by omega]
          have hlt : 2 * k * j + k + (s + 1) < totalQ := by
            have hmul : 2 * k * j + 2 * k ≤ totalQ := by
              calc 2 * k * j + 2 * k = 2 * k * (j + 1) := by ring
                _ ≤ 2 * k * TOr := Nat.mul_le_mul_left _ hj
            omega
          have hmod : (2 * k * j + k + (s + 1)) % (2 * k) = k + (s + 1) := by
            rw [show 2 * k * j + k + (s + 1) = (k + (s + 1)) + (2 * k) * j by ring,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          have hstep : fullU (2 * k * j + k + (s + 1)) =
              (stepPost ⟨s, by omega⟩).trans (stepPre ⟨s + 1, hs⟩) := by
            have h3s : k < k + (s + 1) ∧ k + (s + 1) < 2 * k := ⟨by omega, by omega⟩
            simp only [fullU, show 2 * k * j + k + (s + 1) ≠ 0 by omega, hlt, ↓reduceIte, hmod,
              show k + (s + 1) ≠ 0 by omega, blockMid,
              show ¬ (1 ≤ k + (s + 1) ∧ k + (s + 1) < k) by omega,
              show k + (s + 1) ≠ k by omega, h3s, and_self, ↓reduceDIte,
              show k + (s + 1) - k = s + 1 by omega, show s + 1 - 1 = s by omega]
          rw [hstep, LinearIsometryEquiv.trans_apply]
          simp only [applyQ, dnfApplyQ_succ, show s < k by omega, ↓reduceDIte]
      rw [show 2 * k * j + (2 * k - 1) =
        2 * k * j + k + (k - 1) by omega, hhalf2 (k - 1) (by omega)]
      have hfinal : stepPost ⟨k - 1, by omega⟩ (phaseOracle x (stepPre ⟨k - 1, by omega⟩
          (applyQ x (k - 1) midState))) = applyQ x k midState := by
        conv_rhs => rw [show k = (k - 1) + 1 by omega]
        simp only [applyQ, dnfApplyQ_succ, show k - 1 < k by omega, ↓reduceDIte]
      rw [hfinal]
      -- Compute `applyQ x k midState` coordinatewise using `hprefix_bits` twice!
      let litBits (u : BitString w) (jOr : Fin m) : BitString k :=
        fun r => flipAnc x u jOr r (fun _ => false) r
      have h1 : ∀ p, (applyQ x k (embedFamily G)).ofLp p =
          if p.1 = p0 ∧ p.2.1 = false ∧ p.2.2.2.2.2.2 = litBits p.2.2.1 p.2.2.2.2.1 then
            (G p.2.2.1).ofLp (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1) else 0 := by
        intro p
        have h := hprefix_bits x k le_rfl (fun _ _ => fun _ => false) G (embedFamily G)
          (fun _ => rfl) (applyQ x k (embedFamily G)) rfl p
        simpa [litBits] using h
      have hmid_coord : ∀ p, midState.ofLp p =
          if p.1 = p0 ∧ p.2.1 = false ∧ p.2.2.2.2.2.2 = litBits p.2.2.1 p.2.2.2.2.1 then
            ((phaseOracle (badTerm p.2.2.1 x) (G p.2.2.1)).ofLp
              (p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.1)) else 0 := by
        intro ⟨q, c, u, wor, jOr, cOr, a⟩
        simp only [midState, evalCheckPhase, hevalCheckPhase_apply, h1]
        by_cases h : q = p0 ∧ c = false ∧ a = litBits u jOr
        · rcases h with ⟨rfl, rfl, rfl⟩
          simp only [and_self, ↓reduceIte, phaseOracle_apply]
          have hcheck : checkAnc u jOr (litBits u jOr) = badTerm u x jOr := by
            simp only [checkAnc, badTerm]
            congr 1
            rw [Bool.eq_iff_iff, decide_eq_true_iff, Term.eval_eq_true_iff]
            constructor
            · intro hall l hl
              obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hl
              have hlen_t : (φ[termIdx u jOr]).length ≤ k :=
                hwidth _ (List.getElem_mem _)
              have hlt_k : idx < k := lt_of_lt_of_le hidx hlen_t
              have h1 := hall ⟨idx, hlt_k⟩ hidx
              simp only [litBits, flipAnc, dnfFlipAnc, litAt, hidx, ↓reduceDIte,
                Function.update_self, Bool.false_xor] at h1
              exact h1
            · intro hall r hr
              have h1 := hall (φ[termIdx u jOr][r.1]'hr) (List.getElem_mem hr)
              simp only [litBits, flipAnc, dnfFlipAnc, litAt, hr, ↓reduceDIte,
                Function.update_self, Bool.false_xor]
              exact h1
          rw [hcheck]
        · simp only [h, ↓reduceIte, mul_zero]
      have h2 := hprefix_bits x k le_rfl litBits (fun u => phaseOracle (badTerm u x) (G u))
        midState hmid_coord (applyQ x k midState) rfl
      ext p
      rw [h2 p]
      simp only [embedFamily]
      have hdouble : (fun r : Fin k => if r.1 < k then
          flipAnc x p.2.2.1 p.2.2.2.2.1 r (litBits p.2.2.1 p.2.2.2.2.1) r
        else litBits p.2.2.1 p.2.2.2.2.1 r) = fun _ => false := by
        funext r
        simp only [r.2, ↓reduceIte, litBits, flipAnc, dnfFlipAnc]
        cases hlit : litAt p.2.2.1 p.2.2.2.2.1 r with
        | none => simp [hlit]
        | some vp => rcases vp with ⟨v, pol⟩; simp
      rw [hdouble]; rfl
    -- Induction on `j < TOr`: state at `2 * k * j` is `stepPre 0 (embedFamily (F j))`.
    have hstep_j : ∀ (j : ℕ) (hj : j < TOr),
        Cslib.Quantum.run (fun s => (fullU s).toLinearIsometry) (P.embedWitness ψ) x (2 * k * j) =
          stepPre ⟨0, hkpos⟩ (embedFamily (F j)) := by
      intro j; induction j with
      | zero =>
        intro _
        simp only [mul_zero, Cslib.Quantum.run, fullU, ↓reduceIte,
          LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.trans_apply]
        have hinit : P.embedWitness ψ =
            embedFamily (fun u => ψ.ofLp u • ket initBasis) := by
          ext ⟨q, c, u, wor, jOr, cOr, a⟩
          simp only [QMAQueryProtocol.embedWitness_apply, embedFamily, dnfEmbedFamily, P,
            PiLp.smul_apply, ket_apply, smul_eq_mul, initBasis]
          by_cases h1 : q = p0 ∧ c = false ∧ a = fun _ => false
          · rcases h1 with ⟨rfl, rfl, rfl⟩
            by_cases h2 : (wor, jOr, cOr) = (wor0, j0, false)
            · rcases Prod.mk.inj h2 with ⟨rfl, h2'⟩
              rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩
              simp
            · have hne1 : (p0, false, (wor, jOr, cOr, (fun _ : Fin k => false))) ≠
                  (p0, false, (wor0, j0, false, (fun _ : Fin k => false))) := by
                intro heq; apply h2
                rcases Prod.mk.inj heq with ⟨_, hA⟩; rcases Prod.mk.inj hA with ⟨_, hB⟩
                rcases Prod.mk.inj hB with ⟨hB1, hB2⟩; rcases Prod.mk.inj hB2 with ⟨hB2a, hB2b⟩
                rcases Prod.mk.inj hB2b with ⟨hB2c, _⟩
                exact Prod.ext hB1 (Prod.ext hB2a hB2c)
              have hne2 : (jOr, cOr, wor) ≠ (j0, false, wor0) := by
                intro heq; apply h2
                rcases Prod.mk.inj heq with ⟨rfl, hA⟩; rcases Prod.mk.inj hA with ⟨rfl, rfl⟩; rfl
              simp [hne1, hne2]
          · have hne1 : (q, c, (wor, jOr, cOr, a)) ≠
                (p0, false, (wor0, j0, false, (fun _ : Fin k => false))) := by
              intro heq; apply h1
              rcases Prod.mk.inj heq with ⟨rfl, hA⟩; rcases Prod.mk.inj hA with ⟨rfl, hB⟩
              rcases Prod.mk.inj hB with ⟨_, hC⟩; rcases Prod.mk.inj hC with ⟨_, hD⟩
              rcases Prod.mk.inj hD with ⟨_, hE⟩; exact ⟨rfl, rfl, hE⟩
            simp [h1, hne1]
        rw [hinit]
        refine congrArg (stepPre ⟨0, hkpos⟩) ?_
        dsimp only [liftOr, embedFamily]
        rw [dnfLiftOr_embedFamily, dnfLiftOr_embedFamily]
        refine congrArg (dnfEmbedFamily p0) (funext fun u => ?_)
        simp only [F, map_smul, LinearIsometryEquiv.coe_toLinearIsometry, hprepOr,
          Cslib.Quantum.run]
      | succ j ihj =>
        intro hj
        have h2kj : 2 * k * (j + 1) = (2 * k * j + (2 * k - 1)) + 1 := by
          calc 2 * k * (j + 1) = 2 * k * j + 2 * k := by ring
            _ = (2 * k * j + (2 * k - 1)) + 1 := by omega
        rw [h2kj]
        simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
        have hlt : 2 * k * (j + 1) < totalQ := Nat.mul_lt_mul_of_pos_left hj (by omega)
        have hmod : (2 * k * (j + 1)) % (2 * k) = 0 := Nat.mul_mod_right (2 * k) (j + 1)
        have hdiv : (2 * k * (j + 1)) / (2 * k) = j + 1 :=
          Nat.mul_div_cancel_left (j + 1) (by omega)
        have hstep : fullU (2 * k * (j + 1)) =
            ((stepPost ⟨k - 1, by omega⟩).trans (liftOr (orSearch m (j + 1)))).trans
              (stepPre ⟨0, hkpos⟩) := by
          simp only [fullU, show 2 * k * (j + 1) ≠ 0 by omega, hlt, ↓reduceIte, hmod, hdiv,
            eq_self]
        rw [← h2kj, hstep, LinearIsometryEquiv.trans_apply]
        refine congrArg (stepPre ⟨0, hkpos⟩) ?_
        rw [LinearIsometryEquiv.trans_apply, hblock j (by omega) (F j) (ihj (by omega))]
        dsimp only [liftOr, embedFamily]
        rw [dnfLiftOr_embedFamily]
        refine congrArg (dnfEmbedFamily p0) (funext fun u => ?_)
        simp only [F, map_smul, Cslib.Quantum.run]
    -- Final step at `t = totalQ = 2 * k * TOr`.
    rw [QMAQueryProtocol.runState_eq_run]
    change Cslib.Quantum.run (fun s => (fullU s).toLinearIsometry) (P.embedWitness ψ) x totalQ = _
    have hlast_eq : (2 * k * (TOr - 1) + (2 * k - 1)) + 1 = totalQ := by
      simp only [totalQ]
      calc (2 * k * (TOr - 1) + (2 * k - 1)) + 1 = 2 * k * (TOr - 1) + 2 * k := by omega
        _ = 2 * k * ((TOr - 1) + 1) := by ring
        _ = 2 * k * TOr := by rw [Nat.sub_add_cancel hTOr_pos]
    rw [← hlast_eq]
    simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [hlast_eq]
    have hstep_end : fullU totalQ =
        (stepPost ⟨k - 1, by omega⟩).trans (liftOr (orSearch m TOr)) := by
      simp only [fullU, show totalQ ≠ 0 by positivity, show ¬ (totalQ < totalQ) by omega,
        ↓reduceIte, eq_self]
    rw [hstep_end, LinearIsometryEquiv.trans_apply]
    rw [hblock (TOr - 1) (by omega) (F (TOr - 1)) (hstep_j (TOr - 1) (by omega))]
    dsimp only [liftOr, embedFamily]
    rw [dnfLiftOr_embedFamily]
    refine congrArg (dnfEmbedFamily p0) (funext fun u => ?_)
    dsimp only [F]; rw [map_smul, map_smul]
    congr 1
  -- Convert `P.acceptProb x ψ` to `∑ u, ‖ψ u‖^2 * (1 - measureProb (orSearch ...) (orAccept m))`!
  have hprob_eq : ∀ (x : BitString (m * n)) (ψ : EuclideanSpace ℂ (BitString w)),
      P.acceptProb x ψ =
        ∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2 *
          (1 - measureProb (Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u x) TOr)
            (orAccept m)) := by
    intro x ψ
    rw [QMAQueryProtocol.acceptProb_eq_measureProb, hcircuit x ψ]
    exact dnfMeasureProb_embedFamily hm p0 (fun u => badTerm u x) TOr ψ P.accept
      (fun p => by simp [P])
  -- Finally prove completeness (`ε₁ = 0`) and soundness (`ε₂ = 1 / 3`)!
  constructor
  · -- Completeness: every block `j` has a satisfied term `t_j ∈ φ`; encode its index!
    intro x hfx
    have hall_true : ∀ j : Fin m, φ.eval (fun r => x (finProdFinEquiv (j, r))) = true := by
      simp only [blockComp_apply, threshold_apply, decide_eq_true_eq] at hfx
      have hge := le_antisymm (by simpa [Fintype.card_fin] using weight_le (fun j : Fin m =>
        φ.eval (fun r => x (finProdFinEquiv (j, r))))) hfx
      intro j
      by_contra hfj
      have hlt : weight (fun j' : Fin m => φ.eval (fun r => x (finProdFinEquiv (j', r)))) < m := by
        have hsub : (Finset.univ.filter fun j' : Fin m =>
            φ.eval (fun r => x (finProdFinEquiv (j', r))) = true) ⊂ Finset.univ := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
          have hmem : j ∈ Finset.univ.filter (fun j' : Fin m =>
              φ.eval (fun r => x (finProdFinEquiv (j', r))) = true) :=
            heq.symm ▸ Finset.mem_univ j
          exact hfj (Finset.mem_filter.mp hmem).2
        have hlt' := Finset.card_lt_card hsub
        simpa [weight, Fintype.card_fin] using hlt'
      omega
    have hidx_ex : ∀ j : Fin m, ∃ idx : Fin φ.length,
        (φ[idx]).eval (fun r => x (finProdFinEquiv (j, r))) = true := by
      intro j
      obtain ⟨t, ht, hteval⟩ := (DNF.eval_eq_true_iff _ _).mp (hall_true j)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
      exact ⟨⟨i, hi⟩, hteval⟩
    let chosen (j : Fin m) : Fin φ.length := Classical.choose (hidx_ex j)
    let u₀ : BitString w := fun p =>
      let j := (finProdFinEquiv.symm p).1
      let r := (finProdFinEquiv.symm p).2
      encodeFin b ⟨(chosen j).1, lt_of_lt_of_le (chosen j).2 hpow_ge⟩ r
    refine ⟨ket u₀, norm_ket u₀, ?_⟩
    rw [hprob_eq x (ket u₀), Finset.sum_eq_single u₀]
    · have hbad0 : badTerm u₀ x = fun _ => false := by
        funext j
        have hdec : termIdx u₀ j = chosen j := by
          have hslice : (fun r : Fin b => u₀ (finProdFinEquiv (j, r))) =
              encodeFin b ⟨(chosen j).1, lt_of_lt_of_le (chosen j).2 hpow_ge⟩ := by
            funext r; simp only [u₀, Equiv.symm_apply_apply]
          have hval : (decodeFin b (fun r => u₀ (finProdFinEquiv (j, r)))).1 = (chosen j).1 := by
            rw [hslice, decodeFin_encodeFin]
          ext; simp [termIdx, hval, (chosen j).2]
        simp only [badTerm, hdec, Bool.not_eq_false']
        exact Classical.choose_spec (hidx_ex j)
      have hzero : measureProb (Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u₀ x) TOr)
          (orAccept m) = 0 := by
        rw [measureProb_run_orSearch hm, hbad0]
        have hw0 : weight (fun _ : Fin m => false) = 0 := by simp [weight]
        rw [hw0, searchAngle_zero]
        simp
      simp [ket_apply, hzero]
    · intro u _ hu; simp [ket_apply, hu]
    · simp
  · -- Soundness: if `f x = false`, some block `j₀` has `φ.eval (block_{j₀} x) = false`, so
    -- for EVERY `u`, `badTerm u x j₀ = true`, hence `orSearch` accepts with prob ≥ `2 / 3`!
    intro x hfx ψ hψ
    have hex_false : ∃ j₀ : Fin m, φ.eval (fun r => x (finProdFinEquiv (j₀, r))) = false := by
      by_contra hall; push Not at hall
      have htrue : blockComp (threshold m m) (fun y => φ.eval y) x = true := by
        simp only [blockComp_apply, threshold_apply, decide_eq_true_eq]
        have h1 : ∀ j : Fin m, φ.eval (fun r => x (finProdFinEquiv (j, r))) = true := fun j =>
          Bool.eq_true_of_not_eq_false (hall j)
        have hw : weight (fun j : Fin m => φ.eval (fun r => x (finProdFinEquiv (j, r)))) = m := by
          simp [weight, h1]
        rw [hw]
      rw [htrue] at hfx; exact Bool.false_ne_true hfx.symm
    obtain ⟨j₀, hj₀⟩ := hex_false
    rw [hprob_eq x ψ]
    have hnorm_sum : ∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
    calc ∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2 *
          (1 - measureProb (Cslib.Quantum.run (orSearch m) (orSearchInit m) (badTerm u x) TOr)
            (orAccept m))
        ≤ ∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2 * (1 / 3) := by
          refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hbad_j0 : badTerm u x j₀ = true := by
            simp only [badTerm, Bool.not_eq_true']
            by_contra hte
            have hte' : (φ[termIdx u j₀]).eval (fun r => x (finProdFinEquiv (j₀, r))) = true :=
              Bool.eq_true_of_not_eq_false hte
            have hfe : φ.eval (fun r => x (finProdFinEquiv (j₀, r))) = true :=
              (DNF.eval_eq_true_iff _ _).mpr ⟨_, List.getElem_mem _, hte'⟩
            rw [hfe] at hj₀; exact Bool.false_ne_true hj₀.symm
          have hspec := abs_measureProb_run_orSearch_sub_le hm (badTerm u x)
          have hor1 : threshold m 1 (badTerm u x) = true := by
            rw [threshold_one_right, decide_eq_true_eq]
            exact ⟨j₀, hbad_j0⟩
          rw [hor1, bitVal_true] at hspec
          linarith [(abs_le.mp hspec).1]
      _ = 1 / 3 := by rw [← Finset.sum_mul, hnorm_sum, one_mul]

end CslibFrontier.QueryComplexity
