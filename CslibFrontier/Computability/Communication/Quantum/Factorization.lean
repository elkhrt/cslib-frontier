/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Quantum.Protocol

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Schmidt Operator Factorization and Linial–Shraibman Lemma

This module proves the entanglement-independent Schmidt operator factorization for canonical
two-party quantum communication protocols (`exists_schmidt_operator_factorization`) and deduces
Linial and Shraibman's (`linial_shraibman_factorization`) with zero dependence on the
shared entanglement dimension.

## Main results

* `CslibFrontier.CommunicationComplexity.exists_schmidt_operator_factorization`: entanglement-
  independent
  Yao–Kremer–Schmidt factorization of a protocol's acceptance and rejection operators.
* `CslibFrontier.CommunicationComplexity.linial_shraibman_factorization`: real matrix factorization
  `A * B = P.acceptMatrix` with `‖A‖_F ≤ 2^c √|X|` and `‖B‖_F ≤ 2^c √|Y|`.
-/

public section

open scoped BigOperators ComplexOrder
open Finset Matrix Cslib

namespace CslibFrontier.CommunicationComplexity

section Factorization

variable {X Y : Type*} {w : ℕ}

/-- Core entanglement-independent factorization lemma for any `QuantumCommProtocol X Y w`:
produces Schmidt eigenvalues `p : P.EntA → ℝ` (with `∑ i, p i = 1`), Alice scalar coefficients
`R : X → (BitString P.comm × S) × (BitString P.comm × S) → ℂ` with `∑_t ‖R x t‖² ≤ 4^P.comm`,
and Bob witness matrices `Smat : Y → Bool → _ → Matrix (BitString w) (BitString w) ℂ` such that
`M_{x,y} = ∑_t R x t • Smat y true t`, `I - M_{x,y} = ∑_t R x t • Smat y false t`, and
`∑_{t, z} ‖(Smat y z t) *ᵥ v‖² ≤ 4^P.comm ‖v‖²` for every vector `v`! -/
theorem exists_schmidt_operator_factorization (P : QuantumCommProtocol X Y w) :
    ∃ (T : Type) (_ : Fintype T) (R : X → T → ℂ)
      (Smat : Y → Bool → T → Matrix (BitString w) (BitString w) ℂ),
      (∀ x, ∑ t : T, ‖R x t‖ ^ 2 ≤ (4 : ℝ) ^ P.comm) ∧
      (∀ y (v : EuclideanSpace ℂ (BitString w)),
        ∑ t : T, ∑ z : Bool, ‖(Smat y z t).toEuclideanLin v‖ ^ 2 ≤ (4 : ℝ) ^ P.comm * ‖v‖ ^ 2) ∧
      (∀ x y (u v : BitString w),
        inner ℂ (P.finalState x y (WithLp.toLp 2 fun a => if a = u then 1 else 0))
          (WithLp.toLp 2 fun p => if (p.1.2, p.2) ∈ P.accept then
            (P.finalState x y (WithLp.toLp 2 fun a => if a = v then 1 else 0)).ofLp p else 0) =
          ∑ t : T, R x t * Smat y true t u v) ∧
      (∀ x y (u v : BitString w),
        inner ℂ (P.finalState x y (WithLp.toLp 2 fun a => if a = u then 1 else 0))
          (WithLp.toLp 2 fun p => if (p.1.2, p.2) ∉ P.accept then
            (P.finalState x y (WithLp.toLp 2 fun a => if a = v then 1 else 0)).ofLp p else 0) =
          ∑ t : T, R x t * Smat y false t u v) ∧
      (P.comm = 0 → ∀ x₁ x₂ y u v,
        ∑ t : T, R x₁ t * Smat y true t u v = ∑ t : T, R x₂ t * Smat y true t u v) := by
  classical
  -- Schmidt decomposition of `P.entState` via `C * Cᴴ`.
  let C : Matrix P.EntA P.EntB ℂ := Matrix.of fun a b => P.entState.ofLp (a, b)
  let H : Matrix P.EntA P.EntA ℂ := C * Cᴴ
  have hH_psd : H.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose C
  have hH_herm : H.IsHermitian := hH_psd.isHermitian
  let eA := hH_herm.eigenvectorBasis
  let p := hH_herm.eigenvalues
  have hp_nonneg : ∀ i, 0 ≤ p i := hH_psd.eigenvalues_nonneg
  have hp_sum : ∑ i : P.EntA, p i = 1 := by
    have htr : H.trace = ∑ i : P.EntA, (p i : ℂ) := by
      let Q : Matrix P.EntA P.EntA ℂ := Matrix.of fun a i => (eA i).ofLp a
      have hQu : Qᴴ * Q = 1 := by
        ext i j; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
          Matrix.one_apply]
        have hi : inner ℂ (eA i) (eA j) = ∑ a, star ((eA i).ofLp a) * (eA j).ofLp a := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
        rw [← hi]
        by_cases hij : i = j
        · subst hij; simp [eA.orthonormal.1 i]
        · simp [hij, eA.orthonormal.2 hij]
      have hQu' : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQu
      rw [show H.trace = (Qᴴ * H * Q).trace by rw [Matrix.trace_mul_cycle, hQu', Matrix.one_mul]]
      simp only [Matrix.trace, Matrix.diag_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmul : (Qᴴ * H * Q) i i = dotProduct (star ⇑(eA i)) (H *ᵥ ⇑(eA i)) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply, dotProduct,
          Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [hmul, hH_herm.mulVec_eigenvectorBasis i]
      have h1 : dotProduct (star ⇑(eA i)) ((p i : ℝ) • ⇑(eA i)) = (p i : ℂ) := by
        have hnorm : inner ℂ (eA i) (eA i) = 1 := by
          rw [inner_self_eq_norm_sq_to_K, eA.orthonormal.1 i, RCLike.ofReal_one, one_pow]
        simp only [EuclideanSpace.inner_eq_star_dotProduct] at hnorm
        rw [dotProduct_smul, dotProduct_comm, hnorm, Complex.real_smul, mul_one]
      exact h1
    have htrC : H.trace.re = 1 := by
      have h1 : H.trace = ∑ a : P.EntA, ∑ b : P.EntB, ((‖P.entState.ofLp (a, b)‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Matrix.trace, Matrix.diag_apply, H, Matrix.mul_apply, Matrix.conjTranspose_apply,
          C, Matrix.of_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h1, Complex.re_sum]
      simp only [Complex.re_sum, Complex.ofReal_re]
      rw [← Fintype.sum_prod_type (f := fun ab : P.EntA × P.EntB => ‖P.entState.ofLp ab‖ ^ 2),
        ← EuclideanSpace.norm_sq_eq, P.norm_entState, one_pow]
    have hre := congrArg Complex.re htr
    rw [htrC, Complex.re_sum] at hre
    simpa using hre.symm
  let eB (i : P.EntA) : EuclideanSpace ℂ P.EntB :=
    if 0 < p i then (((Real.sqrt (p i))⁻¹ : ℝ) : ℂ) • WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) else 0
  have heB_orth : ∀ i j : P.EntA, 0 < p i → 0 < p j →
      inner ℂ (eB i) (eB j) = if i = j then 1 else 0 := by
    intro i j hi hj
    simp only [eB, hi, hj, ↓reduceIte, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have hdot : inner ℂ (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) : EuclideanSpace ℂ P.EntB)
        (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA j))) = (p j : ℂ) * inner ℂ (eA i) (eA j) := by
      have h1 : inner ℂ (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) : EuclideanSpace ℂ P.EntB)
          (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA j))) = dotProduct (star ⇑(eA i)) (H *ᵥ ⇑(eA j)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        change dotProduct (star (Cᴴ *ᵥ ⇑(eA i))) (Cᴴ *ᵥ ⇑(eA j)) = _
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
          Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]
      rw [h1, hH_herm.mulVec_eigenvectorBasis j]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_smul, Complex.real_smul]
      rw [dotProduct_comm]
    rw [hdot]
    by_cases hij : i = j
    · subst hij
      have h1 : inner ℂ (eA i) (eA i) = 1 := by simp [eA.orthonormal.1 i]
      rw [h1, mul_one, ← mul_assoc, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (le_of_lt hi), ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hi)]
      simp
    · simp [hij, eA.orthonormal.2 hij]
  have hschmidt : ∀ a b,
      P.entState.ofLp (a, b) =
        ∑ i : P.EntA, (Real.sqrt (p i) : ℂ) * (eA i).ofLp a * star ((eB i).ofLp b) := by
    intro a b
    have hterm : ∀ i : P.EntA,
        (Real.sqrt (p i) : ℂ) * (eA i).ofLp a * star ((eB i).ofLp b) =
          (eA i).ofLp a * (∑ a' : P.EntA, C a' b * star ((eA i).ofLp a')) := by
      intro i
      by_cases hi : 0 < p i
      · simp only [eB, hi, ↓reduceIte, PiLp.smul_apply, smul_eq_mul,
          Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_mul, Complex.star_def,
          Complex.conj_ofReal, map_sum]
        have hmul : (Real.sqrt (p i) : ℂ) * (((Real.sqrt (p i))⁻¹ : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hi),
            Complex.ofReal_one]
        calc (Real.sqrt (p i) : ℂ) * (eA i).ofLp a *
              ((∑ x : P.EntA, (starRingEnd ℂ) ((starRingEnd ℂ) (C x b) * (eA i).ofLp x)) *
                (((Real.sqrt (p i))⁻¹ : ℝ) : ℂ))
            = ((Real.sqrt (p i) : ℂ) * (((Real.sqrt (p i))⁻¹ : ℝ) : ℂ)) * (eA i).ofLp a *
                (∑ x : P.EntA, C x b * (starRingEnd ℂ) ((eA i).ofLp x)) := by
                have hsum : (∑ x : P.EntA,
                      (starRingEnd ℂ) ((starRingEnd ℂ) (C x b) * (eA i).ofLp x)) =
                    ∑ x : P.EntA, C x b * (starRingEnd ℂ) ((eA i).ofLp x) := by
                  refine Finset.sum_congr rfl fun x _ => by rw [map_mul, starRingEnd_self_apply]
                rw [hsum]; ring
          _ = (eA i).ofLp a * ∑ x : P.EntA, C x b * (starRingEnd ℂ) ((eA i).ofLp x) := by
                rw [hmul, one_mul]
      · have hpi0 : p i = 0 := le_antisymm (not_lt.mp hi) (hp_nonneg i)
        have hzero : ‖(WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) : EuclideanSpace ℂ P.EntB)‖ ^ 2 = 0 := by
          rw [← @inner_self_eq_norm_sq ℂ]
          have h1 : inner ℂ (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) : EuclideanSpace ℂ P.EntB)
              (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i))) = dotProduct (star ⇑(eA i)) (H *ᵥ ⇑(eA i)) := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
            change dotProduct (star (Cᴴ *ᵥ ⇑(eA i))) (Cᴴ *ᵥ ⇑(eA i)) = _
            rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
              Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]
          rw [h1, hH_herm.mulVec_eigenvectorBasis i]
          dsimp only [p] at hpi0
          rw [hpi0]; simp
        have hv0 : (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) : EuclideanSpace ℂ P.EntB) = 0 :=
          norm_eq_zero.mp (by
            nlinarith [norm_nonneg (WithLp.toLp 2 (Cᴴ *ᵥ ⇑(eA i)) : EuclideanSpace ℂ P.EntB)])
        have hcoord : (Cᴴ *ᵥ ⇑(eA i)) b = 0 := congrArg (fun v => v.ofLp b) hv0
        have hconj := congrArg star hcoord
        simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul,
          star_star, star_zero] at hconj
        have hsum0 : ∑ a' : P.EntA, C a' b * star ((eA i).ofLp a') = 0 := by
          rw [← hconj]; refine Finset.sum_congr rfl fun a' _ => mul_comm _ _
        rw [hpi0, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, zero_mul, hsum0, mul_zero]
    simp_rw [hterm]
    have hsum_comm :
        (∑ i : P.EntA, (eA i).ofLp a * (∑ a' : P.EntA, C a' b * star ((eA i).ofLp a'))) =
        ∑ a' : P.EntA, C a' b * ∑ i : P.EntA, (eA i).ofLp a * star ((eA i).ofLp a') := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_comm]
    have hproj : ∀ a', ∑ i : P.EntA, (eA i).ofLp a * star ((eA i).ofLp a') =
        if a' = a then 1 else 0 := by
      intro a'
      let Q : Matrix P.EntA P.EntA ℂ := Matrix.of fun x i => (eA i).ofLp x
      have hQu : Qᴴ * Q = 1 := by
        ext i j; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
          Matrix.one_apply]
        have hi : inner ℂ (eA i) (eA j) = ∑ x, star ((eA i).ofLp x) * (eA j).ofLp x := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
        rw [← hi]
        by_cases hij : i = j
        · subst hij; simp [eA.orthonormal.1 i]
        · simp [hij, eA.orthonormal.2 hij]
      have hQu' : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQu
      have hcell := congrFun (congrFun hQu' a) a'
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.one_apply,
        eq_comm] using hcell
    simp_rw [hproj]
    simp [C]
  -- Restrict to positive Schmidt indices `S := {i : P.EntA // 0 < p i}`.
  let S := {i : P.EntA // 0 < p i}
  let T := (BitString P.comm × S) × (BitString P.comm × S)
  let aVec (x : X) (s : BitString P.comm) (i : S) : EuclideanSpace ℂ P.HA :=
    opA P P.comm s x (WithLp.toLp 2 fun a => if a.1 = P.initA then (eA i.1).ofLp a.2 else 0)
  let bVec (y : Y) (s : BitString P.comm) (u : BitString w) (i : S) : EuclideanSpace ℂ (P.HB × Bool)
    :=
    P.finalBobU y (embedBool (if h0 : P.comm = 0 then false else s ⟨P.comm - 1, by omega⟩)
      (opB P P.comm s y (WithLp.toLp 2 fun b =>
        if b.1 = u ∧ b.2.1 = P.initB then star ((eB i.1).ofLp b.2.2) else 0)))
  let R : X → T → ℂ := fun x t =>
    (Real.sqrt (p t.1.2.1) : ℂ) * inner ℂ (aVec x t.1.1 t.1.2) (aVec x t.2.1 t.2.2)
  let Smat : Y → Bool → T → Matrix (BitString w) (BitString w) ℂ := fun y z t =>
    Matrix.of fun u v => (Real.sqrt (p t.2.2.1) : ℂ) *
      inner ℂ (bVec y t.1.1 u t.1.2)
        (WithLp.toLp 2 fun bm => if (bm ∈ P.accept) = z then (bVec y t.2.1 v t.2.2).ofLp bm else 0)
  -- Shared final-state decomposition + unified proof for both `z = true` and `z = false`.
  have hM_both : ∀ (z : Bool) (x : X) (y : Y) (u v : BitString w),
      inner ℂ (P.finalState x y (WithLp.toLp 2 fun a => if a = u then 1 else 0))
        (WithLp.toLp 2 fun p =>
          if ((p.1.2, p.2) ∈ P.accept) = z then
            (P.finalState x y (WithLp.toLp 2 fun a => if a = v then 1 else 0)).ofLp p
          else 0) =
        ∑ t : T, R x t * Smat y z t u v := by
    intro z x y u v
    have hfinal : ∀ u' : BitString w,
        P.finalState x y (WithLp.toLp 2 fun a => if a = u' then 1 else 0) =
        WithLp.toLp 2 fun q : P.Joint =>
          ∑ i : S, ∑ s : BitString P.comm,
            (Real.sqrt (p i.1) : ℂ) * (aVec x s i).ofLp q.1.1 * (bVec y s u' i).ofLp (q.1.2,
              q.2) := by
      intro u'
      let initI (i : P.EntA) : EuclideanSpace ℂ P.Joint :=
        WithLp.toLp 2 fun q : P.Joint =>
          if q.2 = false then
            (if q.1.1.1 = P.initA then (eA i).ofLp q.1.1.2 else 0) *
            (if q.1.2.1 = u' ∧ q.1.2.2.1 = P.initB then star ((eB i).ofLp q.1.2.2.2) else 0)
          else 0
      have hinit : P.initState (WithLp.toLp 2 fun a => if a = u' then 1 else 0) =
          ∑ i : P.EntA, (Real.sqrt (p i) : ℂ) • initI i := by
        ext ⟨⟨⟨wa, ea⟩, ⟨u'', wb, eb⟩⟩, m⟩
        simp only [P.initState_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
          smul_eq_mul, initI]
        by_cases hcond : wa = P.initA ∧ wb = P.initB ∧ m = false
        · rcases hcond with ⟨rfl, rfl, rfl⟩
          by_cases hu : u'' = u'
          · subst hu; simp [hschmidt ea eb, Finset.mul_sum, mul_assoc]
          · simp [hu]
        · have hzero : ∀ i : P.EntA,
              (Real.sqrt (p i) : ℂ) *
                (if m = false then (if wa = P.initA then (eA i).ofLp ea else 0) *
                  (if u'' = u' ∧ wb = P.initB then star ((eB i).ofLp eb) else 0) else 0) = 0 := by
            intro i
            by_cases hm : m = false
            · by_cases hwa : wa = P.initA
              · have hwb : wb ≠ P.initB := fun h => hcond ⟨hwa, h, hm⟩
                simp [hm, hwa, hwb]
              · simp [hm, hwa]
            · simp [hm]
          simp only [hcond, ↓reduceIte]
          exact (Finset.sum_eq_zero fun i _ => hzero i).symm
      rw [P.finalState_eq_liftBob_runSteps, hinit, P.runSteps_sum, P.liftBob_sum]
      ext q
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
      have hdrop : ∑ i : P.EntA, (P.liftBob (P.finalBobU y)
            (P.runSteps x y P.comm ((Real.sqrt (p i) : ℂ) • initI i))).ofLp q =
          ∑ i : S, (P.liftBob (P.finalBobU y)
            (P.runSteps x y P.comm ((Real.sqrt (p i.1) : ℂ) • initI i.1))).ofLp q := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : P.EntA => 0 < p i)]
        have h0 : ∑ i ∈ Finset.univ.filter (fun i : P.EntA => ¬ 0 < p i),
            (P.liftBob (P.finalBobU y)
              (P.runSteps x y P.comm ((Real.sqrt (p i) : ℂ) • initI i))).ofLp q = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hpi0 : p i = 0 := le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hp_nonneg i)
          rw [P.runSteps_smul, P.liftBob_smul, hpi0, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
          rfl
        rw [h0, add_zero]
        exact Finset.sum_subtype _ (fun _ => by simp) _
      rw [hdrop]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [P.runSteps_smul, P.liftBob_smul]
      let vA : EuclideanSpace ℂ P.HA :=
        WithLp.toLp 2 fun a => if a.1 = P.initA then (eA i.1).ofLp a.2 else 0
      let uB : EuclideanSpace ℂ P.HB :=
        WithLp.toLp 2 fun b =>
          if b.1 = u' ∧ b.2.1 = P.initB then star ((eB i.1).ofLp b.2.2) else 0
      have hyk := yao_kremer_finalState P x y vA uB
      have hinit_eq : initI i.1 = WithLp.toLp 2 fun p =>
          if p.2 = false then vA.ofLp p.1.1 * uB.ofLp p.1.2 else 0 := rfl
      rw [hinit_eq, hyk]
      simp [PiLp.smul_apply, Finset.mul_sum, aVec, bVec, vA, uB, mul_assoc]
    rw [hfinal u, hfinal v]
    have hlhs : inner ℂ (WithLp.toLp 2 fun q : P.Joint => ∑ i : S, ∑ s : BitString P.comm,
          (Real.sqrt (p i.1) : ℂ) * (aVec x s i).ofLp q.1.1 * (bVec y s u i).ofLp (q.1.2, q.2))
        (WithLp.toLp 2 fun q : P.Joint => if ((q.1.2, q.2) ∈ P.accept) = z then
          ∑ i : S, ∑ s : BitString P.comm, (Real.sqrt (p i.1) : ℂ) * (aVec x s i).ofLp q.1.1 *
            (bVec y s v i).ofLp (q.1.2, q.2) else 0) =
        ∑ a : P.HA, ∑ b : P.HB, ∑ m : Bool,
          star (∑ j : S, ∑ s' : BitString P.comm,
            (Real.sqrt (p j.1) : ℂ) * (aVec x s' j).ofLp a * (bVec y s' u j).ofLp (b, m)) *
          (if ((b, m) ∈ P.accept) = z then ∑ i : S, ∑ s : BitString P.comm,
            (Real.sqrt (p i.1) : ℂ) * (aVec x s i).ofLp a * (bVec y s v i).ofLp (b, m) else 0) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
      rw [@Fintype.sum_prod_type _ (P.HA × P.HB) Bool, @Fintype.sum_prod_type _ P.HA P.HB]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun m _ => mul_comm _ _
    have hswap : ∀ (a : P.HA) (bm : P.HB × Bool),
        star (∑ j : S, ∑ s' : BitString P.comm,
          (Real.sqrt (p j.1) : ℂ) * (aVec x s' j).ofLp a * (bVec y s' u j).ofLp bm) *
        (if (bm ∈ P.accept) = z then ∑ i : S, ∑ s : BitString P.comm,
          (Real.sqrt (p i.1) : ℂ) * (aVec x s i).ofLp a * (bVec y s v i).ofLp bm else 0) =
        ∑ j : S, ∑ s' : BitString P.comm, ∑ i : S, ∑ s : BitString P.comm,
          ((Real.sqrt (p j.1) : ℂ) * (star ((aVec x s' j).ofLp a) * (aVec x s i).ofLp a)) *
          ((Real.sqrt (p i.1) : ℂ) * (star ((bVec y s' u j).ofLp bm) *
            (if (bm ∈ P.accept) = z then (bVec y s v i).ofLp bm else 0))) := by
      intro a bm
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s' _ => ?_
      by_cases hbm : (bm ∈ P.accept) = z
      · simp only [hbm, ↓reduceIte, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal]; ring
      · simp [hbm]
    have hcomm4 : ∀ (f : P.HA → P.HB → Bool → S → BitString P.comm → S → BitString P.comm → ℂ),
        ∑ a : P.HA, ∑ b : P.HB, ∑ m : Bool, ∑ j : S, ∑ s' : BitString P.comm, ∑ i : S,
          ∑ s : BitString P.comm, f a b m j s' i s =
        ∑ j : S, ∑ s' : BitString P.comm, ∑ i : S, ∑ s : BitString P.comm,
          ∑ a : P.HA, ∑ b : P.HB, ∑ m : Bool, f a b m j s' i s := by
      intro f
      calc ∑ a, ∑ b, ∑ m, ∑ j, ∑ s', ∑ i, ∑ s, f a b m j s' i s
          = ∑ q : (P.HA × P.HB) × Bool, ∑ t : (S × BitString P.comm) × (S × BitString P.comm),
              f q.1.1 q.1.2 q.2 t.1.1 t.1.2 t.2.1 t.2.2 := by
            simp only [Fintype.sum_prod_type]
        _ = ∑ t : (S × BitString P.comm) × (S × BitString P.comm), ∑ q : (P.HA × P.HB) × Bool,
              f q.1.1 q.1.2 q.2 t.1.1 t.1.2 t.2.1 t.2.2 := Finset.sum_comm
        _ = ∑ j, ∑ s', ∑ i, ∑ s, ∑ a, ∑ b, ∑ m, f a b m j s' i s := by
            simp only [Fintype.sum_prod_type]
    have hsplit_sum : ∑ a : P.HA, ∑ b : P.HB, ∑ m : Bool,
        star (∑ j : S, ∑ s' : BitString P.comm,
          (Real.sqrt (p j.1) : ℂ) * (aVec x s' j).ofLp a * (bVec y s' u j).ofLp (b, m)) *
        (if ((b, m) ∈ P.accept) = z then ∑ i : S, ∑ s : BitString P.comm,
          (Real.sqrt (p i.1) : ℂ) * (aVec x s i).ofLp a * (bVec y s v i).ofLp (b, m) else 0) =
        ∑ j : S, ∑ s' : BitString P.comm, ∑ i : S, ∑ s : BitString P.comm,
          ((Real.sqrt (p j.1) : ℂ) * inner ℂ (aVec x s' j) (aVec x s i)) *
          ((Real.sqrt (p i.1) : ℂ) * inner ℂ (bVec y s' u j)
            (WithLp.toLp 2 fun bm => if (bm ∈ P.accept) =
              z then (bVec y s v i).ofLp bm else 0)) := by
      simp_rw [hswap]
      rw [hcomm4]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s' _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
      rw [@Fintype.sum_prod_type _ P.HB Bool, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hrhs : ∑ t : T, R x t * Smat y z t u v =
        ∑ j : S, ∑ s' : BitString P.comm, ∑ i : S, ∑ s : BitString P.comm,
          ((Real.sqrt (p j.1) : ℂ) * inner ℂ (aVec x s' j) (aVec x s i)) *
          ((Real.sqrt (p i.1) : ℂ) * inner ℂ (bVec y s' u j)
            (WithLp.toLp 2 fun bm => if (bm ∈ P.accept) =
              z then (bVec y s v i).ofLp bm else 0)) := by
      simp only [R, Smat, Matrix.of_apply]
      rw [@Fintype.sum_prod_type _ (BitString P.comm × S) (BitString P.comm × S)]
      conv_lhs =>
        rw [@Fintype.sum_prod_type _ (BitString P.comm) S]
        arg 2; ext s'; arg 2; ext j
        rw [@Fintype.sum_prod_type _ (BitString P.comm) S]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s' _ => Finset.sum_comm
    exact hlhs.trans (hsplit_sum.trans hrhs.symm)
  refine ⟨T, inferInstance, R, Smat, ?_, ?_, ?_, ?_, ?_⟩
  · -- Bound `∑ t, ‖R x t‖² ≤ 4^P.comm`.
    intro x
    let K : Matrix P.HA (BitString P.comm × S) ℂ :=
      Matrix.of fun a si => (Real.sqrt (p si.2.1) : ℂ) * (aVec x si.1 si.2).ofLp a
    let G : Matrix P.HA (BitString P.comm × S) ℂ :=
      Matrix.of fun a si => (aVec x si.1 si.2).ofLp a
    have hR_sum : ∑ t : T, ‖R x t‖ ^ 2 = ((K * Kᴴ) * (G * Gᴴ)).trace.re := by
      have hKG : ∀ (u v : BitString P.comm × S), (Kᴴ * G) u v = R x (u, v) := fun u v => by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, G, Matrix.of_apply, R,
          EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, Finset.mul_sum,
          star_mul, Complex.star_def, Complex.conj_ofReal]
        refine Finset.sum_congr rfl fun a _ => by ring
      have h1 : (∑ t : T, ((‖R x t‖ ^ 2 : ℝ) : ℂ)) = ((Kᴴ * G)ᴴ * (Kᴴ * G)).trace := by
        rw [Fintype.sum_prod_type, Matrix.trace, Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Matrix.diag_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Matrix.conjTranspose_apply, hKG u v, Complex.star_def, mul_comm, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      have h2 : ((Kᴴ * G)ᴴ * (Kᴴ * G)).trace = ((K * Kᴴ) * (G * Gᴴ)).trace := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
          Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      have hre := congrArg Complex.re (h1.trans h2)
      rw [Complex.re_sum] at hre
      simpa only [Complex.ofReal_re] using hre
    rw [hR_sum]
    have hKK_psd : (K * Kᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose K
    have hKK_herm : (K * Kᴴ).IsHermitian := hKK_psd.isHermitian
    have hKK_tr : (K * Kᴴ).trace.re ≤ (2 : ℝ) ^ P.comm := by
      have htr : (K * Kᴴ).trace = ∑ si : BitString P.comm × S,
          ((p si.2.1 * ‖aVec x si.1 si.2‖ ^ 2 : ℝ) : ℂ) := by
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, K,
          Matrix.of_apply]
        refine Finset.sum_congr rfl fun si _ => ?_
        have hsum : ∑ a : P.HA, star ((Real.sqrt (p si.2.1) : ℂ) * (aVec x si.1 si.2).ofLp a) *
            ((Real.sqrt (p si.2.1) : ℂ) * (aVec x si.1 si.2).ofLp a) =
            ((p si.2.1 * ‖aVec x si.1 si.2‖ ^ 2 : ℝ) : ℂ) := by
          rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [star_mul, Complex.star_def, Complex.conj_ofReal]
          have hsq : (Real.sqrt (p si.2.1) : ℂ) * (Real.sqrt (p si.2.1) : ℂ) = (p si.2.1 : ℂ) := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt si.2.2)]
          calc (starRingEnd ℂ) ((aVec x si.1 si.2).ofLp a) * (Real.sqrt (p si.2.1) : ℂ) *
                ((Real.sqrt (p si.2.1) : ℂ) * (aVec x si.1 si.2).ofLp a)
              = ((Real.sqrt (p si.2.1) : ℂ) * (Real.sqrt (p si.2.1) : ℂ)) *
                  ((aVec x si.1 si.2).ofLp a * (starRingEnd ℂ) ((aVec x si.1 si.2).ofLp a)) := by
                ring
            _ = (p si.2.1 : ℂ) * ((‖(aVec x si.1 si.2).ofLp a‖ ^ 2 : ℝ) : ℂ) := by
                rw [hsq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        exact hsum
      rw [htr, Complex.re_sum]
      simp only [Complex.ofReal_re, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      have hsum_p : ∑ i : S, p i.1 = 1 := by
        rw [← hp_sum]
        have hfilter : ∑ i : P.EntA, p i = ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), p i := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < p i)]
          have h0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i), p i = 0 :=
            Finset.sum_eq_zero fun i hi =>
              le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hp_nonneg i)
          linarith
        rw [hfilter]
        exact (Finset.sum_subtype _ (fun _ => by simp) p).symm
      calc ∑ i : S, ∑ s : BitString P.comm, p i.1 * ‖aVec x s i‖ ^ 2
          = ∑ i : S, p i.1 * ∑ s : BitString P.comm, ‖aVec x s i‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ i : S, p i.1 * ((2 : ℝ) ^ P.comm * 1) := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (le_of_lt i.2)
            have hnorm_e : ‖(WithLp.toLp 2 fun a : P.HA =>
                if a.1 = P.initA then (eA i.1).ofLp a.2 else 0 : EuclideanSpace ℂ P.HA)‖ ^ 2 =
                  1 := by
              simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
              rw [Finset.sum_eq_single P.initA (fun w _ hw => by simp [hw]) (by simp)]
              simp only [↓reduceIte]
              rw [← EuclideanSpace.norm_sq_eq, eA.orthonormal.1 i.1, one_pow]
            simpa [aVec, hnorm_e] using sum_norm_sq_opA_le P x
              (WithLp.toLp 2 fun a => if a.1 = P.initA then (eA i.1).ofLp a.2 else 0)
        _ = (2 : ℝ) ^ P.comm := by rw [mul_one, ← Finset.sum_mul, hsum_p, one_mul]
    -- Spectral bound on `Tr((K * Kᴴ) * (G * Gᴴ))` using `‖(G * Gᴴ) v‖` quadratic form `≤ 2^c ‖v‖²`.
    have hGG_quad : ∀ v : EuclideanSpace ℂ P.HA,
        (inner ℂ v ((G * Gᴴ).toEuclideanLin v)).re ≤ (2 : ℝ) ^ P.comm * ‖v‖ ^ 2 := by
      intro v
      have hquad : inner ℂ v ((G * Gᴴ).toEuclideanLin v) =
          ∑ si : BitString P.comm × S, ((‖inner ℂ (aVec x si.1 si.2) v‖ ^ 2 : ℝ) : ℂ) := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toLpLin_apply,
          Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, G, Matrix.of_apply,
          Pi.star_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun si _ => ?_
        have h1 : (∑ b : P.HA, ∑ a : P.HA,
            (aVec x si.1 si.2).ofLp b * star ((aVec x si.1 si.2).ofLp a) * v.ofLp a *
              star (v.ofLp b)) =
            (∑ b : P.HA, (aVec x si.1 si.2).ofLp b * star (v.ofLp b)) *
            (∑ a : P.HA, v.ofLp a * star ((aVec x si.1 si.2).ofLp a)) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
        rw [Finset.sum_comm, h1]
        have h2 : ∑ b : P.HA, (aVec x si.1 si.2).ofLp b * star (v.ofLp b) =
            star (∑ a : P.HA, v.ofLp a * star ((aVec x si.1 si.2).ofLp a)) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun a _ => by rw [star_mul, star_star, mul_comm]
        rw [h2, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rfl
      rw [hquad, Complex.re_sum]
      simp only [Complex.ofReal_re, Fintype.sum_prod_type]
      have hbessel : ∀ s : BitString P.comm,
          ∑ i : S, ‖inner ℂ (aVec x s i) v‖ ^ 2 ≤ ‖LinearMap.adjoint (opA P P.comm s x) v‖ ^ 2 := by
        intro s
        let η := LinearMap.adjoint (opA P P.comm s x) v
        let ηInit : EuclideanSpace ℂ P.EntA := WithLp.toLp 2 fun a => η.ofLp (P.initA, a)
        have hterm : ∀ i : S, inner ℂ (aVec x s i) v = inner ℂ (eA i.1) ηInit := by
          intro i
          rw [show aVec x s i = opA P P.comm s x _ from rfl, ← LinearMap.adjoint_inner_right]
          simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
            ηInit]
          rw [Finset.sum_eq_single P.initA (fun a _ ha => by simp [ha]) (by simp)]
          simp only [↓reduceIte, Pi.star_apply]; rfl
        simp_rw [hterm]
        have hsub : ∑ i : S, ‖inner ℂ (eA i.1) ηInit‖ ^ 2 ≤
            ∑ i : P.EntA, ‖inner ℂ (eA i) ηInit‖ ^ 2 := by
          have h1 : ∑ i : S, ‖inner ℂ (eA i.1) ηInit‖ ^ 2 =
              ∑ i ∈ Finset.univ.filter (fun i : P.EntA => 0 < p i),
                ‖inner ℂ (eA i) ηInit‖ ^ 2 := by
            symm; exact Finset.sum_subtype _ (fun _ => by simp) _
          rw [h1]
          exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
        have hparseval : ∑ i : P.EntA, ‖inner ℂ (eA i) ηInit‖ ^ 2 = ‖ηInit‖ ^ 2 :=
          eA.sum_sq_norm_inner_right ηInit
        have hsub2 : ‖ηInit‖ ^ 2 ≤ ‖η‖ ^ 2 := by
          simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, ηInit]
          exact Finset.single_le_sum (f := fun w => ∑ a : P.EntA, ‖η.ofLp (w, a)‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ P.initA)
        linarith
      calc ∑ s : BitString P.comm, ∑ i : S, ‖inner ℂ (aVec x s i) v‖ ^ 2
          ≤ ∑ s : BitString P.comm, ‖LinearMap.adjoint (opA P P.comm s x) v‖ ^ 2 :=
            Finset.sum_le_sum fun s _ => hbessel s
        _ ≤ (2 : ℝ) ^ P.comm * ‖v‖ ^ 2 := sum_norm_sq_adjoint_opA_le P x v
    let vK := hKK_herm.eigenvectorBasis
    let μK := hKK_herm.eigenvalues
    have htr_eig : ((K * Kᴴ) * (G * Gᴴ)).trace.re =
        ∑ k : P.HA, μK k * (inner ℂ (vK k) ((G * Gᴴ).toEuclideanLin (vK k))).re := by
      let Q : Matrix P.HA P.HA ℂ := Matrix.of fun a k => (vK k).ofLp a
      have hQu : Qᴴ * Q = 1 := by
        ext i j; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
          Matrix.one_apply]
        have hi : inner ℂ (vK i) (vK j) = ∑ a, star ((vK i).ofLp a) * (vK j).ofLp a := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
        rw [← hi]; by_cases hij : i = j
        · subst hij; simp [vK.orthonormal.1 i]
        · simp [hij, vK.orthonormal.2 hij]
      have hQu' : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQu
      have htr_eq : ((K * Kᴴ) * (G * Gᴴ)).trace = (Qᴴ * ((G * Gᴴ) * (K * Kᴴ)) * Q).trace := by
        rw [Matrix.trace_mul_comm (K * Kᴴ)]
        conv_rhs => rw [Matrix.trace_mul_cycle, hQu', Matrix.one_mul]
      rw [htr_eq, Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag_apply]
      have hmul : (Qᴴ * ((G * Gᴴ) * (K * Kᴴ)) * Q) k k =
          inner ℂ (vK k) (((G * Gᴴ) * (K * Kᴴ)).toEuclideanLin (vK k)) := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toLpLin_apply,
          Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => by ring
      have heig : ((G * Gᴴ) * (K * Kᴴ)).toEuclideanLin (vK k) =
          (μK k : ℂ) • (G * Gᴴ).toEuclideanLin (vK k) := by
        have h1 : ((G * Gᴴ) * (K * Kᴴ)).toEuclideanLin (vK k) =
            (G * Gᴴ).toEuclideanLin ((K * Kᴴ).toEuclideanLin (vK k)) := by
          change Matrix.toLpLin 2 2 _ _ = _; rw [Matrix.toLpLin_mul_same]; rfl
        have h2 : (K * Kᴴ).toEuclideanLin (vK k) = (μK k : ℂ) • vK k := by
          ext a; change ((K * Kᴴ) *ᵥ ⇑(vK k)) a = _; rw [hKK_herm.mulVec_eigenvectorBasis k]
          simp [μK, vK]
        rw [h1, h2, map_smul]
      rw [hmul, heig, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    have hsum_μ : ∑ k : P.HA, μK k = (K * Kᴴ).trace.re := by
      let Q : Matrix P.HA P.HA ℂ := Matrix.of fun a k => (vK k).ofLp a
      have hQu : Qᴴ * Q = 1 := by
        ext i j; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
          Matrix.one_apply]
        have hi : inner ℂ (vK i) (vK j) = ∑ a, star ((vK i).ofLp a) * (vK j).ofLp a := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
        rw [← hi]; by_cases hij : i = j
        · subst hij; simp [vK.orthonormal.1 i]
        · simp [hij, vK.orthonormal.2 hij]
      have hQu' : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQu
      have htr_eq : (K * Kᴴ).trace = (Qᴴ * (K * Kᴴ) * Q).trace := by
        conv_rhs => rw [Matrix.trace_mul_cycle, hQu', Matrix.one_mul]
      rw [htr_eq, Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag_apply]
      have hmul : (Qᴴ * (K * Kᴴ) * Q) k k = inner ℂ (vK k) ((K * Kᴴ).toEuclideanLin (vK k)) := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toLpLin_apply,
          Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, Q, Matrix.of_apply,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => by ring
      have h2 : (K * Kᴴ).toEuclideanLin (vK k) = (μK k : ℂ) • vK k := by
        ext a; change ((K * Kᴴ) *ᵥ ⇑(vK k)) a = _; rw [hKK_herm.mulVec_eigenvectorBasis k]
        simp [μK, vK]
      rw [hmul, h2, inner_smul_right, inner_self_eq_norm_sq_to_K, vK.orthonormal.1 k,
        RCLike.ofReal_one, one_pow, mul_one, Complex.ofReal_re]
    rw [htr_eig]
    calc ∑ k : P.HA, μK k * (inner ℂ (vK k) ((G * Gᴴ).toEuclideanLin (vK k))).re
        ≤ ∑ k : P.HA, μK k * (2 : ℝ) ^ P.comm := by
          refine Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left ?_ (hKK_psd.eigenvalues_nonneg k)
          have := hGG_quad (vK k); rwa [vK.orthonormal.1 k, one_pow, mul_one] at this
      _ = (∑ k : P.HA, μK k) * (2 : ℝ) ^ P.comm := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 : ℝ) ^ P.comm * (2 : ℝ) ^ P.comm :=
          mul_le_mul_of_nonneg_right (hsum_μ ▸ hKK_tr) (by positivity)
      _ = (4 : ℝ) ^ P.comm := by rw [← mul_pow]; norm_num
  · -- Bound `∑ t, ∑ z, ‖(Smat y z t) *ᵥ v‖² ≤ 4^P.comm * ‖v‖²`.
    intro y v
    let embedBVec (i : S) : EuclideanSpace ℂ P.HB :=
      WithLp.toLp 2 fun b => if b.2.1 = P.initB then v.ofLp b.1 * star ((eB i.1).ofLp b.2.2) else 0
    have hnorm_embedBVec : ∀ i : S, ‖embedBVec i‖ ^ 2 = ‖v‖ ^ 2 := by
      intro i
      simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, embedBVec]
      have h1 : ∀ u : BitString w,
          ∑ wb : P.WorkB, ∑ eb : P.EntB,
            ‖if wb = P.initB then v.ofLp u * star ((eB i.1).ofLp eb) else 0‖ ^ 2 =
              ‖v.ofLp u‖ ^ 2 := by
        intro u
        rw [Finset.sum_eq_single P.initB (fun wb _ hwb => by simp [hwb]) (by simp)]
        simp only [↓reduceIte, norm_mul, mul_pow, norm_star, ← Finset.mul_sum]
        have heBi : ∑ eb : P.EntB, ‖(eB i.1).ofLp eb‖ ^ 2 = 1 := by
          rw [← EuclideanSpace.norm_sq_eq, ← @inner_self_eq_norm_sq ℂ, heB_orth i.1 i.1 i.2 i.2]
          simp
        rw [heBi, mul_one]
      simp_rw [h1]
    have hlin_b : ∀ (s : BitString P.comm) (i : S) (z : Bool) (u : BitString w)
      (s' : BitString P.comm) (j : S),
        ((Smat y z ((s', j), (s, i))).toEuclideanLin v).ofLp u =
          (Real.sqrt (p i.1) : ℂ) * inner ℂ (bVec y s' u j)
            (WithLp.toLp 2 fun bm => if (bm ∈ P.accept) = z then
              (P.finalBobU y (embedBool (if h0 : P.comm =
                0 then false else s ⟨P.comm - 1, by omega⟩)
                (opB P P.comm s y (embedBVec i)))).ofLp bm else 0) := by
      intro s i z u s' j
      simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Smat, Matrix.of_apply]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      have hpull : ∀ v' : BitString w,
          inner ℂ (bVec y s' u j) (WithLp.toLp 2 fun bm =>
              if (bm ∈ P.accept) = z then (bVec y s v' i).ofLp bm else 0) * v.ofLp v' =
          inner ℂ (bVec y s' u j) (v.ofLp v' • WithLp.toLp 2 fun bm =>
              if (bm ∈ P.accept) = z then (bVec y s v' i).ofLp bm else 0) := by
        intro v'; rw [inner_smul_right, mul_comm]
      simp_rw [hpull]
      rw [← inner_sum]
      congr 2; ext bm
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
      by_cases hacc : (bm ∈ P.accept) = z
      · simp only [hacc, ↓reduceIte]
        have hsum_v : (P.finalBobU y (embedBool (if h0 : P.comm =
          0 then false else s ⟨P.comm - 1, by omega⟩)
            (opB P P.comm s y (embedBVec i)))).ofLp bm =
            ∑ v' : BitString w, v.ofLp v' * (bVec y s v' i).ofLp bm := by
          have heq : embedBVec i = ∑ v' : BitString w, v.ofLp v' •
              (WithLp.toLp 2 fun b : P.HB => if b.1 = v' ∧ b.2.1 = P.initB then
                star ((eB i.1).ofLp b.2.2) else 0) := by
            ext ⟨u', wb, eb⟩
            simp only [embedBVec, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
            rw [Finset.sum_eq_single u' (fun v' _ hv' => by simp [hv'.symm]) (by simp)]
            simp
          have hmap : ∀ (m : Bool) (ξs : BitString w → EuclideanSpace ℂ P.HB),
              embedBool m (∑ v' : BitString w, ξs v') =
                ∑ v' : BitString w, embedBool m (ξs v') := by
            intro m ξs; ext ⟨b', m'⟩
            by_cases hm : m' = m <;> simp [embedBool_apply, hm, Finset.sum_apply]
          have hsmul : ∀ (m : Bool) (c : ℂ) (ξ : EuclideanSpace ℂ P.HB),
              embedBool m (c • ξ) = c • embedBool m ξ := by
            intro m c ξ; ext ⟨b', m'⟩; simp [embedBool_apply]
          rw [heq, map_sum, hmap]
          simp_rw [map_smul, hsmul]
          rw [map_sum]
          simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
            bVec]
        rw [hsum_v]
        refine Finset.sum_congr rfl fun v' _ => ?_
        rw [PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply]
        simp only [hacc, ↓reduceIte]
      · simp only [hacc, ↓reduceIte]
        refine Finset.sum_eq_zero fun v' _ => ?_
        simp only [PiLp.smul_apply, smul_eq_mul, hacc, ↓reduceIte, mul_zero]
    -- Bound the sum over `(s', j)` and `u` for any fixed `ξ : EuclideanSpace ℂ (P.HB × Bool)`.
    have hinner_b : ∀ (ξ : EuclideanSpace ℂ (P.HB × Bool)),
        ∑ s' : BitString P.comm, ∑ j : S, ∑ u : BitString w,
          ‖inner ℂ (bVec y s' u j) ξ‖ ^ 2 ≤ (2 : ℝ) ^ P.comm * ‖ξ‖ ^ 2 := by
      intro ξ
      let ξ' := (P.finalBobU y).symm ξ
      have hterm : ∀ (s' : BitString P.comm) (j : S) (u : BitString w),
          inner ℂ (bVec y s' u j) ξ =
            inner ℂ (WithLp.toLp 2 fun b : P.HB => if b.1 = u ∧ b.2.1 = P.initB then
                star ((eB j.1).ofLp b.2.2) else 0)
              (LinearMap.adjoint (opB P P.comm s' y)
                (sliceBool (if h0 : P.comm = 0 then false else s' ⟨P.comm - 1, by omega⟩) ξ')) := by
        intro s' j u
        rw [show bVec y s' u j = P.finalBobU y _ from rfl, LinearIsometryEquiv.inner_map_eq_flip,
          inner_embedBool_sliceBool, ← LinearMap.adjoint_inner_right]
      simp_rw [hterm]
      have hbessel : ∀ (s' : BitString P.comm) (η : EuclideanSpace ℂ P.HB),
          ∑ j : S, ∑ u : BitString w,
            ‖inner ℂ (WithLp.toLp 2 fun b : P.HB => if b.1 = u ∧ b.2.1 = P.initB then
                star ((eB j.1).ofLp b.2.2) else 0) η‖ ^ 2 ≤ ‖η‖ ^ 2 := by
        intro s' η
        rw [Finset.sum_comm]
        have h1 : ∀ u : BitString w,
            ∑ j : S, ‖inner ℂ (WithLp.toLp 2 fun b : P.HB => if b.1 = u ∧ b.2.1 = P.initB then
                star ((eB j.1).ofLp b.2.2) else 0) η‖ ^ 2 ≤
              ∑ eb : P.EntB, ‖η.ofLp (u, P.initB, eb)‖ ^ 2 := by
          intro u
          let ηu : EuclideanSpace ℂ P.EntB := WithLp.toLp 2 fun eb => star (η.ofLp (u, P.initB, eb))
          have hi : ∀ j : S,
              ‖inner ℂ (WithLp.toLp 2 fun b : P.HB => if b.1 = u ∧ b.2.1 = P.initB then
                  star ((eB j.1).ofLp b.2.2) else 0) η‖ ^ 2 = ‖inner ℂ (eB j.1) ηu‖ ^ 2 := by
            intro j
            have hconj : inner ℂ (WithLp.toLp 2 fun b : P.HB => if b.1 = u ∧ b.2.1 = P.initB then
                  star ((eB j.1).ofLp b.2.2) else 0) η = star (inner ℂ (eB j.1) ηu) := by
              simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
                ηu]
              rw [Finset.sum_eq_single u (fun u' _ hu' => by simp [hu']) (by simp)]
              rw [Finset.sum_eq_single P.initB (fun wb _ hwb => by simp [hwb]) (by simp)]
              simp only [and_self, ↓reduceIte, Pi.star_apply, star_sum, star_mul, star_star]
              exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
            rw [hconj, norm_star]
          simp_rw [hi]
          -- `{eB j | j : S}` is orthonormal, so `∑ j : S, ‖⟨eB j, ηu⟩‖² ≤ ‖ηu‖²`!
          have horth_S : Orthonormal ℂ (fun j : S => eB j.1) := by
            rw [orthonormal_iff_ite]
            intro j₁ j₂
            have := heB_orth j₁.1 j₂.1 j₁.2 j₂.2
            by_cases h : j₁ = j₂
            · subst h; simpa using this
            · have hne : j₁.1 ≠ j₂.1 := fun h' => h (Subtype.ext h')
              simpa [h, hne] using this
          have hb := horth_S.sum_inner_products_le (s := Finset.univ) ηu
          simpa only [EuclideanSpace.norm_sq_eq, ηu, norm_star] using hb
        calc ∑ u : BitString w, ∑ j : S, _
            ≤ ∑ u : BitString w, ∑ eb : P.EntB, ‖η.ofLp (u, P.initB, eb)‖ ^ 2 :=
              Finset.sum_le_sum fun u _ => h1 u
          _ ≤ ∑ u : BitString w, ∑ wb : P.WorkB, ∑ eb : P.EntB, ‖η.ofLp (u, wb, eb)‖ ^ 2 :=
              Finset.sum_le_sum fun u _ => Finset.single_le_sum
                (f := fun wb => ∑ eb : P.EntB, ‖η.ofLp (u, wb, eb)‖ ^ 2)
                (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ P.initB)
          _ = ‖η‖ ^ 2 := by simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
      calc ∑ s' : BitString P.comm, ∑ j : S, ∑ u : BitString w, _
          ≤ ∑ s' : BitString P.comm,
              ‖LinearMap.adjoint (opB P P.comm s' y)
                (sliceBool (if h0 : P.comm =
                  0 then false else s' ⟨P.comm - 1, by omega⟩) ξ')‖ ^ 2 :=
            Finset.sum_le_sum fun s' _ => hbessel s' _
        _ ≤ ∑ s' : BitString P.comm,
              (‖LinearMap.adjoint (opB P P.comm s' y) (sliceBool false ξ')‖ ^ 2 +
               ‖LinearMap.adjoint (opB P P.comm s' y) (sliceBool true ξ')‖ ^ 2) := by
            refine Finset.sum_le_sum fun s' _ => ?_
            cases (if h0 : P.comm = 0 then false else s' ⟨P.comm - 1, by omega⟩) <;>
              linarith [sq_nonneg ‖LinearMap.adjoint (opB P P.comm s' y) (sliceBool false ξ')‖,
                sq_nonneg ‖LinearMap.adjoint (opB P P.comm s' y) (sliceBool true ξ')‖]
        _ = (∑ s' : BitString P.comm,
          ‖LinearMap.adjoint (opB P P.comm s' y) (sliceBool false ξ')‖ ^ 2) +
            (∑ s' : BitString P.comm,
              ‖LinearMap.adjoint (opB P P.comm s' y) (sliceBool true ξ')‖ ^ 2) :=
            Finset.sum_add_distrib
        _ ≤ (2 : ℝ) ^ P.comm * ‖sliceBool false ξ'‖ ^ 2 +
          (2 : ℝ) ^ P.comm * ‖sliceBool true ξ'‖ ^ 2 :=
            add_le_add (sum_norm_sq_adjoint_opB_le P y _) (sum_norm_sq_adjoint_opB_le P y _)
        _ = (2 : ℝ) ^ P.comm * ‖ξ'‖ ^ 2 := by rw [← mul_add, norm_sq_sliceBool_sum]
        _ = (2 : ℝ) ^ P.comm * ‖ξ‖ ^ 2 := by rw [(P.finalBobU y).symm.norm_map]
    -- Assemble the full sum over `t = ((s', j), (s, i))` and `z : Bool`.
    rw [Fintype.sum_prod_type]
    have hrearr : ∑ p1 : BitString P.comm × S, ∑ p2 : BitString P.comm × S, ∑ z : Bool,
        ‖(Smat y z (p1, p2)).toEuclideanLin v‖ ^ 2 =
        ∑ p2 : BitString P.comm × S, ∑ z : Bool, ∑ p1 : BitString P.comm × S,
          ‖(Smat y z (p1, p2)).toEuclideanLin v‖ ^ 2 := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hrearr]
    have hstep1 : ∀ (s : BitString P.comm) (i : S),
        ∑ z : Bool, ∑ p1 : BitString P.comm × S,
          ‖(Smat y z (p1, (s, i))).toEuclideanLin v‖ ^ 2 ≤
        (2 : ℝ) ^ P.comm * (p i.1 * ‖opB P P.comm s y (embedBVec i)‖ ^ 2) := by
      intro s i
      have hterm_z : ∀ z : Bool,
          ∑ p1 : BitString P.comm × S, ‖(Smat y z (p1, (s, i))).toEuclideanLin v‖ ^ 2 ≤
          p i.1 * ((2 : ℝ) ^ P.comm *
            ‖(WithLp.toLp 2 fun bm => if (bm ∈ P.accept) = z then
              (P.finalBobU y (embedBool (if h0 : P.comm =
                0 then false else s ⟨P.comm - 1, by omega⟩)
                (opB P P.comm s y (embedBVec i)))).ofLp bm else 0 :
                EuclideanSpace ℂ (P.HB × Bool))‖ ^ 2) := by
        intro z
        rw [Fintype.sum_prod_type]
        have h1 : ∀ s' j, ‖(Smat y z ((s', j), (s, i))).toEuclideanLin v‖ ^ 2 =
            p i.1 * ∑ u : BitString w,
              ‖inner ℂ (bVec y s' u j) (WithLp.toLp 2 fun bm => if (bm ∈ P.accept) = z then
                (P.finalBobU y (embedBool (if h0 : P.comm =
                  0 then false else s ⟨P.comm - 1, by omega⟩)
                  (opB P P.comm s y (embedBVec i)))).ofLp bm else 0)‖ ^ 2 := by
          intro s' j
          rw [EuclideanSpace.norm_sq_eq]
          simp_rw [hlin_b s i z _ s' j, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt i.2)]
          rw [Finset.mul_sum]
        simp_rw [h1, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (by simpa [Fintype.sum_prod_type] using hinner_b _)
          (le_of_lt i.2)
      calc ∑ z : Bool, ∑ p1 : BitString P.comm × S, ‖(Smat y z (p1, (s, i))).toEuclideanLin v‖ ^ 2
          ≤ ∑ z : Bool, p i.1 * ((2 : ℝ) ^ P.comm *
              ‖(WithLp.toLp 2 fun bm => if (bm ∈ P.accept) = z then
                (P.finalBobU y (embedBool (if h0 : P.comm =
                  0 then false else s ⟨P.comm - 1, by omega⟩)
                  (opB P P.comm s y (embedBVec i)))).ofLp bm else 0 :
                  EuclideanSpace ℂ (P.HB × Bool))‖ ^ 2) :=
            Finset.sum_le_sum fun z _ => hterm_z z
        _ = (2 : ℝ) ^ P.comm * (p i.1 *
              ∑ z : Bool, ‖(WithLp.toLp 2 fun bm => if (bm ∈ P.accept) = z then
                (P.finalBobU y (embedBool (if h0 : P.comm =
                  0 then false else s ⟨P.comm - 1, by omega⟩)
                  (opB P P.comm s y (embedBVec i)))).ofLp bm else 0 :
                  EuclideanSpace ℂ (P.HB × Bool))‖ ^ 2) := by
            simp only [Fintype.sum_bool]; ring
        _ = (2 : ℝ) ^ P.comm * (p i.1 * ‖opB P P.comm s y (embedBVec i)‖ ^ 2) := by
            congr 2
            simp only [Fintype.sum_bool, EuclideanSpace.norm_sq_eq]
            rw [← Finset.sum_add_distrib]
            trans ‖P.finalBobU y (embedBool (if h0 : P.comm =
              0 then false else s ⟨P.comm - 1, by omega⟩)
              (opB P P.comm s y (embedBVec i)))‖ ^ 2
            · rw [EuclideanSpace.norm_sq_eq]
              refine Finset.sum_congr rfl fun bm _ => ?_
              by_cases hbm : bm ∈ P.accept <;> simp [hbm]
            · rw [(P.finalBobU y).norm_map, norm_sq_embedBool, EuclideanSpace.norm_sq_eq]
    have hsum_p : ∑ i : S, p i.1 = 1 := by
      rw [← hp_sum]
      have hfilter : ∑ i : P.EntA, p i = ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), p i := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < p i)]
        have h0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i), p i = 0 :=
          Finset.sum_eq_zero fun i hi =>
            le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hp_nonneg i)
        linarith
      rw [hfilter]
      exact (Finset.sum_subtype _ (fun _ => by simp) p).symm
    calc ∑ p2 : BitString P.comm × S, ∑ z : Bool, ∑ p1 : BitString P.comm × S,
          ‖(Smat y z (p1, p2)).toEuclideanLin v‖ ^ 2
        ≤ ∑ p2 : BitString P.comm × S,
            (2 : ℝ) ^ P.comm * (p p2.2.1 * ‖opB P P.comm p2.1 y (embedBVec p2.2)‖ ^ 2) :=
          Finset.sum_le_sum fun ⟨s, i⟩ _ => hstep1 s i
      _ = (2 : ℝ) ^ P.comm * ∑ i : S, p i.1 * ∑ s : BitString P.comm,
            ‖opB P P.comm s y (embedBVec i)‖ ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by dsimp only; exact (Finset.mul_sum _ _ _).symm
      _ ≤ (2 : ℝ) ^ P.comm * ∑ i : S, p i.1 * ((2 : ℝ) ^ P.comm * ‖v‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left ?_ (le_of_lt i.2)) (by positivity)
          simpa [hnorm_embedBVec i] using sum_norm_sq_opB_le P y (embedBVec i)
      _ = (4 : ℝ) ^ P.comm * ‖v‖ ^ 2 := by
          rw [← Finset.sum_mul, hsum_p, one_mul, ← mul_assoc, ← mul_pow]; norm_num
  · -- Exact formula for `M_{x, y} u v` (`z = true`).
    intro x y u v
    simpa using hM_both true x y u v
  · -- Exact formula for `(I - M_{x, y}) u v` (`z = false`).
    intro x y u v
    simpa using hM_both false x y u v
  · -- When `P.comm = 0`, `opA P 0 s x = LinearMap.id`, so `R x t` is independent of `x`.
    intro hc0 x₁ x₂ y u v
    refine Finset.sum_congr rfl fun t _ => ?_
    have hR : R x₁ t = R x₂ t := by
      simp only [R, aVec, hc0, opA_zero]
    rw [hR]

/-- **Linial–Shraibman Factorization Lemma**:
for every witness-free (`w = 0`) `c`-qubit quantum communication protocol `P` (with unlimited
finite-dimensional shared entanglement) on `X × Y`, there exist real matrices `A, B` such that
`A * B = P.acceptMatrix`, `‖A‖_F ≤ 2^c √|X|`, and `‖B‖_F ≤ 2^c √|Y|`.
-/
theorem linial_shraibman_factorization [Fintype X] [Fintype Y]
    (P : QuantumCommProtocol X Y 0) :
    ∃ (Z : Type) (_ : Fintype Z) (A : Matrix X Z ℝ) (B : Matrix Z Y ℝ),
      A * B = P.acceptMatrix ∧
      frobeniusNorm A ≤ (2 : ℝ) ^ P.comm * Real.sqrt (Fintype.card X) ∧
      frobeniusNorm B ≤ (2 : ℝ) ^ P.comm * Real.sqrt (Fintype.card Y) := by
  classical
  obtain ⟨T, _, R, Smat, hR, hS, hM, _, _⟩ := exists_schmidt_operator_factorization P
  let u0 : BitString 0 := fun i => Fin.elim0 i
  let A : Matrix X (T × Bool) ℝ := Matrix.of fun x tb =>
    if tb.2 then -(R x tb.1).im else (R x tb.1).re
  let B : Matrix (T × Bool) Y ℝ := Matrix.of fun tb y =>
    if tb.2 then (Smat y true tb.1 u0 u0).im else (Smat y true tb.1 u0 u0).re
  refine ⟨T × Bool, inferInstance, A, B, ?_, ?_, ?_⟩
  · ext x y
    have h1 : (P.acceptMatrix x y : ℂ) = ∑ t : T, R x t * Smat y true t u0 u0 := by
      have hket : (WithLp.toLp 2 fun _ : BitString 0 => (1 : ℂ)) =
          (WithLp.toLp 2 fun a : BitString 0 => if a = u0 then (1 : ℂ) else 0) := by
        ext a; simp [show a = u0 from Subsingleton.elim a u0]
      have hM0 := hM x y u0 u0
      rw [← hket] at hM0
      rw [← hM0, P.acceptMatrix_apply, P.acceptProb_eq_sum_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
        Finset.sum_filter, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs
      · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp
    have hre := congrArg Complex.re h1
    simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re] at hre
    rw [hre]
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, A, B, Matrix.of_apply,
      ↓reduceIte, Bool.false_eq_true]
    refine Finset.sum_congr rfl fun t _ => by ring
  · -- `‖A‖_F² ≤ 4^c * |X|`.
    have hsq : frobeniusNorm A ^ 2 ≤ ((2 : ℝ) ^ P.comm * Real.sqrt (Fintype.card X)) ^ 2 := by
      rw [sq_frobeniusNorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), show ((2 : ℝ) ^ P.comm) ^ 2 =
        (4 : ℝ) ^ P.comm by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      calc ∑ x : X, ∑ tb : T × Bool, A x tb ^ 2
          = ∑ x : X, ∑ t : T, ‖R x t‖ ^ 2 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [Fintype.sum_prod_type, Fintype.sum_bool, A, Matrix.of_apply,
              ↓reduceIte, Bool.false_eq_true]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
        _ ≤ ∑ _x : X, (4 : ℝ) ^ P.comm := Finset.sum_le_sum fun x _ => hR x
        _ = (4 : ℝ) ^ P.comm * Fintype.card X := by simp [mul_comm]
    exact (sq_le_sq₀ (frobeniusNorm_nonneg A) (by positivity)).mp hsq
  · -- `‖B‖_F² ≤ 4^c * |Y|`.
    have hsq : frobeniusNorm B ^ 2 ≤ ((2 : ℝ) ^ P.comm * Real.sqrt (Fintype.card Y)) ^ 2 := by
      rw [sq_frobeniusNorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), show ((2 : ℝ) ^ P.comm) ^ 2 =
        (4 : ℝ) ^ P.comm by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      calc ∑ tb : T × Bool, ∑ y : Y, B tb y ^ 2
          = ∑ y : Y, ∑ t : T, ‖Smat y true t u0 u0‖ ^ 2 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => ?_
            simp only [Fintype.sum_prod_type, Fintype.sum_bool, B, Matrix.of_apply,
              ↓reduceIte, Bool.false_eq_true]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
        _ ≤ ∑ y : Y, (4 : ℝ) ^ P.comm := by
            refine Finset.sum_le_sum fun y _ => ?_
            let e0 : EuclideanSpace ℂ (BitString 0) := WithLp.toLp 2 fun _ => 1
            have he0 : ‖e0‖ ^ 2 = 1 := by simp [EuclideanSpace.norm_sq_eq, e0]
            have hSy := hS y e0
            rw [he0, mul_one] at hSy
            calc ∑ t : T, ‖Smat y true t u0 u0‖ ^ 2
                = ∑ t : T, ‖(Smat y true t).toEuclideanLin e0‖ ^ 2 := by
                  refine Finset.sum_congr rfl fun t _ => ?_
                  have hsing : (Finset.univ : Finset (BitString 0)) = {u0} := by
                    ext a; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
                    exact Subsingleton.elim a u0
                  rw [EuclideanSpace.norm_sq_eq, hsing, Finset.sum_singleton]
                  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, hsing,
                    Finset.sum_singleton, e0, mul_one]
              _ ≤ ∑ t : T, ∑ z : Bool, ‖(Smat y z t).toEuclideanLin e0‖ ^ 2 :=
                  Finset.sum_le_sum fun t _ => by
                    rw [Fintype.sum_bool]
                    linarith [sq_nonneg ‖(Smat y false t).toEuclideanLin e0‖]
              _ ≤ (4 : ℝ) ^ P.comm := hSy
        _ = (4 : ℝ) ^ P.comm * Fintype.card Y := by simp [mul_comm]
    exact (sq_le_sq₀ (frobeniusNorm_nonneg B) (by positivity)).mp hsq


end Factorization

end CslibFrontier.CommunicationComplexity
