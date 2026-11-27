/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact Single-Step Amplitude Amplification and Multi-Qudit QFT over `ZMod p`

This module develops two general quantum unitary primitives on finite-dimensional complex
Euclidean spaces:
1. Generalized diagonal phase reflections and Brassard–Høyer–Mosca–Tapp exact single-step
   amplitude amplification boosting any initial good probability `a ≥ 1 / 4` to exact unit
   probability `1` while preserving zero-amplitude coordinates.
2. Subspace orthogonality for `ZMod.stdAddChar` and the `n`-qudit and `1`-qudit discrete Quantum
   Fourier Transforms as `LinearIsometryEquiv` operators on `EuclideanSpace ℂ (Fin n → ZMod p)` and
   `EuclideanSpace ℂ (ZMod p)`, bridged directly to `Cslib.Quantum.qft`.

## Main definitions

* `CslibFrontier.Quantum.phaseReflection`: diagonal unitary multiplying coordinates satisfying `P`
  by `exp (φ * I)`.
* `CslibFrontier.Quantum.exactAmpOp`, `CslibFrontier.Quantum.exactAmpAngle`: single-step generalized
  amplitude amplification operator and exact angle `2 * arcsin (1 / (2 * √a))`.
* `CslibFrontier.Quantum.qftZMod`, `CslibFrontier.Quantum.qftZModOne`: `n`-qudit and `1`-qudit
  discrete Quantum Fourier Transform linear isometries over `ZMod p`.

## Main results

* `CslibFrontier.Quantum.exactAmpOp_bad_eq_zero`,
  `CslibFrontier.Quantum.exactAmpOp_good_prob_eq_one`,
  `CslibFrontier.Quantum.exactAmpOp_ofLp_eq_zero_of_eq_zero`: exact cancellation of bad amplitudes,
  unit measurement probability on `Good` for `a ≥ 1 / 4`, and preservation of zero amplitudes.
* `CslibFrontier.Quantum.sum_stdAddChar_dotProduct_submodule`: character orthogonality over any
  submodule `S ≤ (ι → ZMod p)`.
* `CslibFrontier.Quantum.qftZModOne_apply_eq_qft`,
  `CslibFrontier.Quantum.qftZModOne_symm_phaseVec`: agreement with `Cslib.Quantum.qft` and
  inverse-QFT basis recovery from Fourier phase states.
-/

public section

namespace CslibFrontier.Quantum

section ExactAmplification

/-- Generalized diagonal phase reflection on `EuclideanSpace ℂ W`, multiplying coordinates
satisfying `P` by `Complex.exp ((φ : ℂ) * Complex.I)`. -/
noncomputable def phaseReflection {W : Type*} [Fintype W] (P : W → Prop) [DecidablePred P]
    (φ : ℝ) : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W := by
  have hexp_inv : Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I) =
      1 := by
    rw [← Complex.exp_add]
    have h : (((-φ : ℝ) : ℂ) * Complex.I) + ((φ : ℂ) * Complex.I) = 0 := by push_cast; ring
    rw [h, Complex.exp_zero]
  have hexp_star : Complex.exp ((φ : ℂ) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
    have h : ((φ : ℂ) * Complex.I) + ((φ : ℂ) * -Complex.I) = 0 := by ring
    rw [h, Complex.exp_zero]
  let diag (θ : ℝ) : EuclideanSpace ℂ W →ₗ[ℂ] EuclideanSpace ℂ W :=
    { toFun := fun v ↦ WithLp.toLp 2
        (fun w ↦ (if P w then Complex.exp ((θ : ℂ) * Complex.I) else 1) * v.ofLp w)
      map_add' := fun _ _ ↦ by ext w; simp [mul_add]
      map_smul' := fun _ _ ↦ by
        ext w
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hleft : Function.LeftInverse (diag (-φ)) (diag φ) := fun v ↦ by
    ext w; simp only [diag, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hw : P w
    · simp only [hw, ↓reduceIte, ← mul_assoc, hexp_inv, one_mul]
    · simp [hw]
  have hright : Function.RightInverse (diag (-φ)) (diag φ) := fun v ↦ by
    ext w; simp only [diag, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hw : P w
    · simp only [hw, ↓reduceIte, ← mul_assoc]
      rw [mul_comm (Complex.exp ((φ : ℂ) * Complex.I)), hexp_inv, one_mul]
    · simp [hw]
  refine LinearEquiv.isometryOfInner (LinearEquiv.mk (diag φ) (diag (-φ)) hleft hright)
    fun u v ↦ ?_
  simp only [LinearEquiv.coe_mk, diag, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
    RCLike.inner_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  by_cases hw : P w
  · simp only [hw, ↓reduceIte, map_mul]
    calc (Complex.exp ((φ : ℂ) * Complex.I) * v.ofLp w) *
            ((starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) * (starRingEnd ℂ) (u.ofLp w))
        = (Complex.exp ((φ : ℂ) * Complex.I) *
            (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I))) *
            (v.ofLp w * (starRingEnd ℂ) (u.ofLp w)) := by ring
      _ = v.ofLp w * (starRingEnd ℂ) (u.ofLp w) := by rw [hexp_star, one_mul]
  · simp [hw]

theorem phaseReflection_apply {W : Type*} [Fintype W] (P : W → Prop) [DecidablePred P]
    (φ : ℝ) (v : EuclideanSpace ℂ W) (w : W) :
    (phaseReflection P φ v).ofLp w =
      (if P w then Complex.exp ((φ : ℂ) * Complex.I) else 1) * v.ofLp w := by
  rfl

/-- Single-step generalized amplitude amplification operator
`A ∘ S_{w₀}(φ) ∘ A⁻¹ ∘ S_Good(φ) ∘ A`. -/
noncomputable def exactAmpOp {W : Type*} [Fintype W] [DecidableEq W]
    (A : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W) (w₀ : W)
    (Good : W → Prop) [DecidablePred Good] (φ : ℝ) :
    EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W :=
  A.trans ((phaseReflection Good φ).trans
    (A.symm.trans ((phaseReflection (· = w₀) φ).trans A)))

theorem exactAmpOp_apply {W : Type*} [Fintype W] [DecidableEq W]
    (A : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W) (w₀ : W)
    (Good : W → Prop) [DecidablePred Good] (φ : ℝ) (v : EuclideanSpace ℂ W) :
    exactAmpOp A w₀ Good φ v =
      A (phaseReflection (· = w₀) φ (A.symm (phaseReflection Good φ (A v)))) := by
  rfl

/-- Exact single-step amplitude amplification phase angle `2 * arcsin (1 / (2 * √a))`. -/
noncomputable def exactAmpAngle (a : ℝ) : ℝ :=
  2 * Real.arcsin (1 / (2 * Real.sqrt a))

private lemma phaseReflection_singleton_eq {W : Type*} [Fintype W] [DecidableEq W]
    (w₀ : W) (φ : ℝ) (u : EuclideanSpace ℂ W) :
    phaseReflection (· = w₀) φ u =
      u + ((Complex.exp ((φ : ℂ) * Complex.I) - 1) *
        inner ℂ (EuclideanSpace.single w₀ 1) u) • EuclideanSpace.single w₀ 1 := by
  have hinner : inner ℂ (EuclideanSpace.single w₀ 1) u = u.ofLp w₀ := by
    simp [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.single]
  rw [hinner]
  ext w
  simp only [phaseReflection_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single, PiLp.ofLp_single, Pi.single_apply]
  by_cases hw : w = w₀
  · subst hw; simp only [↓reduceIte, mul_one]; ring
  · simp [hw]

/-- Generalized single-step amplitude amplification preserves zero-amplitude coordinates of
`A |w₀⟩`. -/
theorem exactAmpOp_ofLp_eq_zero_of_eq_zero {W : Type*} [Fintype W] [DecidableEq W]
    (A : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W) (w₀ : W)
    (Good : W → Prop) [DecidablePred Good] (φ : ℝ) {w : W}
    (h0 : (A (EuclideanSpace.single w₀ 1)).ofLp w = 0) :
    ((exactAmpOp A w₀ Good φ) (EuclideanSpace.single w₀ 1)).ofLp w = 0 := by
  rw [exactAmpOp_apply, phaseReflection_singleton_eq, map_add, map_smul,
    LinearIsometryEquiv.apply_symm_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    phaseReflection_apply, h0, mul_zero, mul_zero, add_zero]

private lemma exactAmp_phase_poly_eq_zero {a : ℝ} (ha : (1 / 4 : ℝ) ≤ a) :
    Complex.exp ((exactAmpAngle a : ℂ) * Complex.I) +
      (a : ℂ) * (Complex.exp ((exactAmpAngle a : ℂ) * Complex.I) - 1) ^ 2 = 0 := by
  set c : ℂ := Complex.exp ((exactAmpAngle a : ℂ) * Complex.I)
  have ha_pos : 0 < a := by linarith
  have hsqrt_ge : (1 / 2 : ℝ) ≤ Real.sqrt a := by
    have h14 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h14]; exact Real.sqrt_le_sqrt ha
  have h2sqrt_pos : 0 < 2 * Real.sqrt a := by linarith
  have harg_pos : 0 < 1 / (2 * Real.sqrt a) := by positivity
  have harg_le : 1 / (2 * Real.sqrt a) ≤ 1 := (div_le_one h2sqrt_pos).mpr (by linarith)
  set θ : ℝ := Real.arcsin (1 / (2 * Real.sqrt a))
  have hsinθ : Real.sin θ = 1 / (2 * Real.sqrt a) := Real.sin_arcsin (by linarith) harg_le
  have h4asin : 4 * a * Real.sin θ ^ 2 = 1 := by
    rw [hsinθ, div_pow, one_pow, mul_pow, Real.sq_sqrt ha_pos.le]
    field_simp [ha_pos.ne']; ring
  set z : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  set w : ℂ := Complex.exp (-((θ : ℂ) * Complex.I))
  have hzw : z * w = 1 := by
    dsimp only [z, w]; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcz : c = z * z := by
    dsimp only [c, z, exactAmpAngle]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hzsub : z - w = 2 * (Real.sin θ : ℂ) * Complex.I := by
    dsimp only [z, w]
    rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    push_cast; ring
  have hfactor : c + (a : ℂ) * (c - 1) ^ 2 = z * z * (1 + (a : ℂ) * (z - w) ^ 2) := by
    have hc1 : c - 1 = z * (z - w) := by rw [hcz, ← hzw]; ring
    rw [hc1, hcz]; ring
  rw [hfactor, hzsub]
  have h4c : 4 * (a : ℂ) * (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast h4asin
  have hvanish : 1 + (a : ℂ) * (2 * (Real.sin θ : ℂ) * Complex.I) ^ 2 = 0 := by
    calc 1 + (a : ℂ) * (2 * (Real.sin θ : ℂ) * Complex.I) ^ 2
        = 1 + 4 * (a : ℂ) * (Real.sin θ : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = 1 - 4 * (a : ℂ) * (Real.sin θ : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
      _ = 0 := by rw [h4c, sub_self]
  rw [hvanish, mul_zero]

private lemma exactAmpOp_bad_coeff {W : Type*} [Fintype W] [DecidableEq W]
    (A : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W) (w₀ : W)
    (Good : W → Prop) [DecidablePred Good] (φ : ℝ) {w : W} (hw : ¬ Good w) :
    ((exactAmpOp A w₀ Good φ) (EuclideanSpace.single w₀ 1)).ofLp w =
      (Complex.exp ((φ : ℂ) * Complex.I) +
        ((∑ u ∈ Finset.univ.filter Good,
            ‖(A (EuclideanSpace.single w₀ 1)).ofLp u‖ ^ 2 : ℝ) : ℂ) *
          (Complex.exp ((φ : ℂ) * Complex.I) - 1) ^ 2) *
        (A (EuclideanSpace.single w₀ 1)).ofLp w := by
  set ψ : EuclideanSpace ℂ W := A (EuclideanSpace.single w₀ 1)
  set a : ℝ := ∑ u ∈ Finset.univ.filter Good, ‖ψ.ofLp u‖ ^ 2
  set v : EuclideanSpace ℂ W := phaseReflection Good φ ψ
  set c : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  have hnorm_ψ : ∑ u : W, ‖ψ.ofLp u‖ ^ 2 = 1 := by
    have hsq := EuclideanSpace.norm_sq_eq ψ
    have h1 : ‖ψ‖ = 1 := by
      rw [show ψ = A (EuclideanSpace.single w₀ 1) from rfl, LinearIsometryEquiv.norm_map]
      simp [EuclideanSpace.single, PiLp.norm_single]
    rw [h1, one_pow] at hsq; exact hsq.symm
  have hbad_sum : ∑ u ∈ Finset.univ.filter (fun u ↦ ¬ Good u), ‖ψ.ofLp u‖ ^ 2 = 1 - a := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset W))
      (p := Good) (f := fun u ↦ ‖ψ.ofLp u‖ ^ 2)
    rw [hnorm_ψ] at hsplit; linarith
  have hinner_ψv : inner ℂ ψ v = (a : ℂ) * c + (1 - (a : ℂ)) := by
    rw [PiLp.inner_apply]
    have hterm (u : W) :
        inner ℂ (ψ.ofLp u) (v.ofLp u) =
          (if Good u then c else 1) * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.inner_apply, show v = phaseReflection Good φ ψ from rfl, phaseReflection_apply]
      have hmul : ψ.ofLp u * (starRingEnd ℂ) (ψ.ofLp u) = ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.conj_mul']; norm_cast
      calc ((if Good u then c else 1) * ψ.ofLp u) * (starRingEnd ℂ) (ψ.ofLp u)
          = (if Good u then c else 1) * (ψ.ofLp u * (starRingEnd ℂ) (ψ.ofLp u)) := by ring
        _ = (if Good u then c else 1) * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) := by rw [hmul]
    simp_rw [hterm]
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset W)) (p := Good)]
    have hgood : ∑ u ∈ Finset.univ.filter Good,
        (if Good u then c else 1) * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) = (a : ℂ) * c := by
      have hcongr :
          ∑ u ∈ Finset.univ.filter Good,
              (if Good u then c else 1) * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) =
            ∑ u ∈ Finset.univ.filter Good, c * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun u hu ↦ by simp [(Finset.mem_filter.mp hu).2]
      rw [hcongr, ← Finset.mul_sum, ← Complex.ofReal_sum, mul_comm]
    have hbad : ∑ u ∈ Finset.univ.filter (fun u ↦ ¬ Good u),
        (if Good u then c else 1) * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) = 1 - (a : ℂ) := by
      have hcongr :
          ∑ u ∈ Finset.univ.filter (fun u ↦ ¬ Good u),
              (if Good u then c else 1) * ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) =
            ∑ u ∈ Finset.univ.filter (fun u ↦ ¬ Good u), ((‖ψ.ofLp u‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun u hu ↦ by simp [(Finset.mem_filter.mp hu).2]
      rw [hcongr, ← Complex.ofReal_sum, hbad_sum]
      push_cast; rfl
    rw [hgood, hbad]
  have hstep : A (phaseReflection (· = w₀) φ (A.symm v)) =
      v + ((c - 1) * inner ℂ ψ v) • ψ := by
    rw [phaseReflection_singleton_eq, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply]
    have hinner_eq : inner ℂ (EuclideanSpace.single w₀ 1) (A.symm v) = inner ℂ ψ v := by
      calc inner ℂ (EuclideanSpace.single w₀ 1) (A.symm v)
          = inner ℂ (A (EuclideanSpace.single w₀ 1)) (A (A.symm v)) := (A.inner_map_map _ _).symm
        _ = inner ℂ ψ v := by rw [LinearIsometryEquiv.apply_symm_apply]
    rw [hinner_eq]
  rw [exactAmpOp_apply, show A (EuclideanSpace.single w₀ 1) = ψ from rfl,
    show phaseReflection Good φ ψ = v from rfl, hstep, hinner_ψv]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hvw : v.ofLp w = ψ.ofLp w := by
    rw [show v = phaseReflection Good φ ψ from rfl, phaseReflection_apply]; simp [hw]
  rw [hvw]; ring

/-- Exact single-step amplitude amplification annihilates every bad amplitude when `a ≥ 1 / 4`. -/
theorem exactAmpOp_bad_eq_zero {W : Type*} [Fintype W] [DecidableEq W]
    (A : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W) (w₀ : W)
    (Good : W → Prop) [DecidablePred Good]
    (ha : (1 / 4 : ℝ) ≤
      ∑ u ∈ Finset.univ.filter Good, ‖(A (EuclideanSpace.single w₀ 1)).ofLp u‖ ^ 2)
    {w : W} (hw : ¬ Good w) :
    ((exactAmpOp A w₀ Good
        (exactAmpAngle
          (∑ u ∈ Finset.univ.filter Good, ‖(A (EuclideanSpace.single w₀ 1)).ofLp u‖ ^ 2)))
      (EuclideanSpace.single w₀ 1)).ofLp w = 0 := by
  rw [exactAmpOp_bad_coeff A w₀ Good _ hw, exactAmp_phase_poly_eq_zero ha, zero_mul]

/-- Exact single-step amplitude amplification achieves unit success probability for `a ≥ 1 / 4`. -/
theorem exactAmpOp_good_prob_eq_one {W : Type*} [Fintype W] [DecidableEq W]
    (A : EuclideanSpace ℂ W ≃ₗᵢ[ℂ] EuclideanSpace ℂ W) (w₀ : W)
    (Good : W → Prop) [DecidablePred Good]
    (ha : (1 / 4 : ℝ) ≤
      ∑ u ∈ Finset.univ.filter Good, ‖(A (EuclideanSpace.single w₀ 1)).ofLp u‖ ^ 2) :
    ∑ w ∈ Finset.univ.filter Good,
      ‖((exactAmpOp A w₀ Good
          (exactAmpAngle
            (∑ u ∈ Finset.univ.filter Good, ‖(A (EuclideanSpace.single w₀ 1)).ofLp u‖ ^ 2)))
        (EuclideanSpace.single w₀ 1)).ofLp w‖ ^ 2 = 1 := by
  set φ : ℝ :=
    exactAmpAngle (∑ u ∈ Finset.univ.filter Good, ‖(A (EuclideanSpace.single w₀ 1)).ofLp u‖ ^ 2)
  set ψ' : EuclideanSpace ℂ W := exactAmpOp A w₀ Good φ (EuclideanSpace.single w₀ 1)
  have htot : ∑ w : W, ‖ψ'.ofLp w‖ ^ 2 = 1 := by
    have hsq := EuclideanSpace.norm_sq_eq ψ'
    have h1 : ‖ψ'‖ = 1 := by
      rw [show ψ' = exactAmpOp A w₀ Good φ (EuclideanSpace.single w₀ 1) from rfl,
        LinearIsometryEquiv.norm_map]
      simp [EuclideanSpace.single, PiLp.norm_single]
    rw [h1, one_pow] at hsq; exact hsq.symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset W))
    (p := Good) (f := fun w ↦ ‖ψ'.ofLp w‖ ^ 2)
  have hbad : ∑ w ∈ Finset.univ.filter (fun w ↦ ¬ Good w), ‖ψ'.ofLp w‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun w hw ↦ by
      rw [show ψ'.ofLp w = 0 from exactAmpOp_bad_eq_zero A w₀ Good ha (Finset.mem_filter.mp hw).2]
      simp
  rw [htot, hbad, add_zero] at hsplit
  exact hsplit

end ExactAmplification

section DiscreteQFT

private lemma stdAddChar_ne_one_of_ne_zero {p : ℕ} [NeZero p] {a : ZMod p} (ha : a ≠ 0) :
    (ZMod.stdAddChar a : ℂ) ≠ 1 := fun h1 ↦
  ha (ZMod.injective_stdAddChar (h1.trans (AddChar.map_zero_eq_one _).symm))

/-- Subspace character orthogonality for `ZMod.stdAddChar` over any submodule `S ≤ (ι → ZMod p)`. -/
theorem sum_stdAddChar_dotProduct_submodule {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (S : Submodule (ZMod p) (ι → ZMod p)) [Fintype S]
    (h : ι → ZMod p) [Decidable (∀ s ∈ S, h ⬝ᵥ s = 0)] :
    ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ) =
      if ∀ s ∈ S, h ⬝ᵥ s = 0 then (Fintype.card S : ℂ) else 0 := by
  split_ifs with hh
  · calc ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ)
        = ∑ _ : S, (1 : ℂ) := Finset.sum_congr rfl fun s _ ↦ by
            rw [hh s.1 s.2, AddChar.map_zero_eq_one]
      _ = (Fintype.card S : ℂ) := by simp
  · push Not at hh
    obtain ⟨s₀, hs₀, hdot⟩ := hh
    have hshift :
        (ZMod.stdAddChar (h ⬝ᵥ s₀) : ℂ) * ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ) =
          ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ) := by
      rw [Finset.mul_sum]
      calc ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s₀) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ s.1)
          = ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ (s + ⟨s₀, hs₀⟩).1) : ℂ) :=
            Finset.sum_congr rfl fun s _ ↦ by
              rw [← AddChar.map_add_eq_mul, Submodule.coe_add, dotProduct_add, add_comm]
        _ = ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ) :=
            Equiv.sum_comp (Equiv.addRight (⟨s₀, hs₀⟩ : S))
              fun s ↦ (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ)
    have hmul : ((ZMod.stdAddChar (h ⬝ᵥ s₀) : ℂ) - 1) *
        ∑ s : S, (ZMod.stdAddChar (h ⬝ᵥ s.1) : ℂ) = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (stdAddChar_ne_one_of_ne_zero hdot))

private lemma sum_stdAddChar_dotProduct_delta {p n : ℕ} [NeZero p] (g k : Fin n → ZMod p) :
    ∑ h : Fin n → ZMod p,
        (ZMod.stdAddChar (-(g ⬝ᵥ h)) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ k) =
      if k = g then ((p ^ n : ℕ) : ℂ) else 0 := by
  have hterm (h : Fin n → ZMod p) :
      (ZMod.stdAddChar (-(g ⬝ᵥ h)) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ k) =
        ZMod.stdAddChar ((k - g) ⬝ᵥ h) := by
    rw [← AddChar.map_add_eq_mul, sub_dotProduct, dotProduct_comm h k, sub_eq_add_neg, add_comm]
  simp_rw [hterm]
  by_cases hkg : k = g
  · subst hkg; simp [ZMod.card]
  · simp only [hkg, ↓reduceIte]
    have hex : ∃ i : Fin n, (k - g) i ≠ 0 := by
      by_contra hall; push Not at hall; exact hkg (sub_eq_zero.mp (funext hall))
    obtain ⟨i, hi⟩ := hex
    let e : Fin n → ZMod p := Pi.single i 1
    have hshift :
        (ZMod.stdAddChar ((k - g) ⬝ᵥ e) : ℂ) *
            ∑ h : Fin n → ZMod p, (ZMod.stdAddChar ((k - g) ⬝ᵥ h) : ℂ) =
          ∑ h : Fin n → ZMod p, (ZMod.stdAddChar ((k - g) ⬝ᵥ h) : ℂ) := by
      rw [Finset.mul_sum]
      calc _ = ∑ h : Fin n → ZMod p, (ZMod.stdAddChar ((k - g) ⬝ᵥ (h + e)) : ℂ) :=
            Finset.sum_congr rfl fun h _ ↦ by
              rw [← AddChar.map_add_eq_mul, dotProduct_add, add_comm]
        _ = _ := Equiv.sum_comp (Equiv.addRight e) fun h ↦ (ZMod.stdAddChar ((k - g) ⬝ᵥ h) : ℂ)
    have hmul : ((ZMod.stdAddChar ((k - g) ⬝ᵥ e) : ℂ) - 1) *
        ∑ h : Fin n → ZMod p, (ZMod.stdAddChar ((k - g) ⬝ᵥ h) : ℂ) = 0 := by
      linear_combination hshift
    have hdot : (k - g) ⬝ᵥ e = (k - g) i := by simp [e]
    rw [hdot] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (stdAddChar_ne_one_of_ne_zero hi))

/-- The `n`-qudit discrete Quantum Fourier Transform on `EuclideanSpace ℂ (Fin n → ZMod p)`. -/
noncomputable def qftZMod (p n : ℕ) [NeZero p] :
    EuclideanSpace ℂ (Fin n → ZMod p) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n → ZMod p) := by
  let scale : ℂ := ((Real.sqrt ((p ^ n : ℕ) : ℝ)) : ℂ)⁻¹
  have hscale_sq : scale * scale * (p : ℂ) ^ n = 1 := by
    have hp_pos : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_pos (NeZero.pos p) (n := n)
    have hr : (Real.sqrt ((p ^ n : ℕ) : ℝ))⁻¹ * (Real.sqrt ((p ^ n : ℕ) : ℝ))⁻¹ *
        ((p ^ n : ℕ) : ℝ) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hp_pos.le, inv_mul_cancel₀ hp_pos.ne']
    have hC : (((Real.sqrt ((p ^ n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt ((p ^ n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * ((p ^ n : ℕ) : ℂ) = 1 := by
      exact_mod_cast hr
    simpa [scale, Complex.ofReal_inv, Nat.cast_pow] using hC
  let fwd : EuclideanSpace ℂ (Fin n → ZMod p) →ₗ[ℂ] EuclideanSpace ℂ (Fin n → ZMod p) :=
    { toFun := fun v ↦ WithLp.toLp 2
        (fun g ↦ scale * ∑ h : Fin n → ZMod p, (ZMod.stdAddChar (g ⬝ᵥ h) : ℂ) * v.ofLp h)
      map_add' := fun _ _ ↦ by ext g; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun _ _ ↦ by
        ext g; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring }
  let bwd : EuclideanSpace ℂ (Fin n → ZMod p) →ₗ[ℂ] EuclideanSpace ℂ (Fin n → ZMod p) :=
    { toFun := fun v ↦ WithLp.toLp 2
        (fun g ↦ scale * ∑ h : Fin n → ZMod p, (ZMod.stdAddChar (-(g ⬝ᵥ h)) : ℂ) * v.ofLp h)
      map_add' := fun _ _ ↦ by ext g; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun _ _ ↦ by
        ext g; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring }
  have hleft : Function.LeftInverse bwd fwd := fun v ↦ by
    ext g; simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk]
    have hsum :
        (∑ h : Fin n → ZMod p, (ZMod.stdAddChar (-(g ⬝ᵥ h)) : ℂ) *
            (scale * ∑ k : Fin n → ZMod p, (ZMod.stdAddChar (h ⬝ᵥ k) : ℂ) * v.ofLp k)) =
          scale * ∑ k : Fin n → ZMod p,
            (∑ h : Fin n → ZMod p,
              (ZMod.stdAddChar (-(g ⬝ᵥ h)) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ k)) * v.ofLp k := by
      calc _ = ∑ h : Fin n → ZMod p, ∑ k : Fin n → ZMod p, scale *
            (((ZMod.stdAddChar (-(g ⬝ᵥ h)) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ k)) * v.ofLp k) :=
            Finset.sum_congr rfl fun _ _ ↦ by
              rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ = ∑ k : Fin n → ZMod p, ∑ h : Fin n → ZMod p, _ := Finset.sum_comm
        _ = _ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_mul, Finset.mul_sum]
    rw [hsum]; simp_rw [sum_stdAddChar_dotProduct_delta g]; simp [← mul_assoc, hscale_sq]
  have hright : Function.RightInverse bwd fwd := fun v ↦ by
    ext g; simp only [fwd, bwd, LinearMap.coe_mk, AddHom.coe_mk]
    have hsum :
        (∑ h : Fin n → ZMod p, (ZMod.stdAddChar (g ⬝ᵥ h) : ℂ) *
            (scale * ∑ k : Fin n → ZMod p, (ZMod.stdAddChar (-(h ⬝ᵥ k)) : ℂ) * v.ofLp k)) =
          scale * ∑ k : Fin n → ZMod p,
            (∑ h : Fin n → ZMod p,
              (ZMod.stdAddChar (-(k ⬝ᵥ h)) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ g)) * v.ofLp k := by
      calc _ = ∑ h : Fin n → ZMod p, ∑ k : Fin n → ZMod p, scale *
            (((ZMod.stdAddChar (-(k ⬝ᵥ h)) : ℂ) * ZMod.stdAddChar (h ⬝ᵥ g)) * v.ofLp k) :=
            Finset.sum_congr rfl fun h _ ↦ by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ ↦ ?_
              rw [dotProduct_comm g h, dotProduct_comm h k]; ring
        _ = ∑ k : Fin n → ZMod p, ∑ h : Fin n → ZMod p, _ := Finset.sum_comm
        _ = _ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_mul, Finset.mul_sum]
    rw [hsum]; simp_rw [fun k ↦ sum_stdAddChar_dotProduct_delta k g, eq_comm (a := g)]
    simp [← mul_assoc, hscale_sq]
  refine LinearEquiv.isometryOfInner (LinearEquiv.mk fwd bwd hleft hright) fun u v ↦ ?_
  simp only [LinearEquiv.coe_mk, fwd, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
    RCLike.inner_apply]
  have hscale_conj : (starRingEnd ℂ) scale = scale := by simp [scale]
  have hchar_conj (x : ZMod p) :
      (starRingEnd ℂ) (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  calc ∑ g : Fin n → ZMod p,
        (scale * ∑ k : Fin n → ZMod p, (ZMod.stdAddChar (g ⬝ᵥ k) : ℂ) * v.ofLp k) *
          (starRingEnd ℂ)
            (scale * ∑ j : Fin n → ZMod p, (ZMod.stdAddChar (g ⬝ᵥ j) : ℂ) * u.ofLp j)
      = ∑ g : Fin n → ZMod p, ∑ j : Fin n → ZMod p, ∑ k : Fin n → ZMod p,
          (scale * scale) *
            ((ZMod.stdAddChar (-(j ⬝ᵥ g)) : ℂ) * ZMod.stdAddChar (g ⬝ᵥ k)) *
            (v.ofLp k * (starRingEnd ℂ) (u.ofLp j)) :=
        Finset.sum_congr rfl fun g _ ↦ by
          rw [map_mul, hscale_conj, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_mul, hchar_conj, dotProduct_comm g j]; ring
    _ = ∑ j : Fin n → ZMod p, ∑ k : Fin n → ZMod p, (scale * scale) *
          (∑ g : Fin n → ZMod p, (ZMod.stdAddChar (-(j ⬝ᵥ g)) : ℂ) * ZMod.stdAddChar (g ⬝ᵥ k)) *
          (v.ofLp k * (starRingEnd ℂ) (u.ofLp j)) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ j : Fin n → ZMod p, v.ofLp j * (starRingEnd ℂ) (u.ofLp j) :=
        Finset.sum_congr rfl fun j _ ↦ by
          simp_rw [sum_stdAddChar_dotProduct_delta j]; simp [hscale_sq]

theorem qftZMod_apply (p n : ℕ) [NeZero p]
    (v : EuclideanSpace ℂ (Fin n → ZMod p)) (g : Fin n → ZMod p) :
    (qftZMod p n v).ofLp g =
      (Real.sqrt ((p ^ n : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ h : Fin n → ZMod p, (ZMod.stdAddChar (g ⬝ᵥ h) : ℂ) * v.ofLp h := by
  rfl

/-- The `1`-qudit discrete Quantum Fourier Transform as a linear isometry equivalence on
`EuclideanSpace ℂ (ZMod p)`. -/
noncomputable def qftZModOne (p : ℕ) [NeZero p] :
    EuclideanSpace ℂ (ZMod p) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod p) :=
  ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.funUnique (Fin 1) (ZMod p)).symm).trans
    (qftZMod p 1)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.funUnique (Fin 1) (ZMod p)))

theorem qftZModOne_apply (p : ℕ) [NeZero p] (v : EuclideanSpace ℂ (ZMod p)) (j : ZMod p) :
    (qftZModOne p v).ofLp j =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        ∑ k : ZMod p, (ZMod.stdAddChar (j * k) : ℂ) * v.ofLp k := by
  simp only [qftZModOne, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Equiv.symm_symm,
    qftZMod_apply, pow_one]
  congr 1
  refine (Equiv.sum_comp (Equiv.funUnique (Fin 1) (ZMod p)).symm
    fun h : Fin 1 → ZMod p ↦
      (ZMod.stdAddChar ((fun _ ↦ j) ⬝ᵥ h) : ℂ) * v.ofLp (h 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  simp [dotProduct]

open Matrix in
/-- Agreement of `qftZModOne p` with the unitary QFT matrix `Cslib.Quantum.qft p`. -/
theorem qftZModOne_apply_eq_qft (p : ℕ) [NeZero p]
    (v : EuclideanSpace ℂ (ZMod p)) (j : ZMod p) :
    (qftZModOne p v).ofLp j = ((Cslib.Quantum.qft p : Matrix (ZMod p) (ZMod p) ℂ) *ᵥ v.ofLp) j := by
  rw [qftZModOne_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Cslib.Quantum.qft_apply, Complex.ofReal_inv, mul_assoc]

/-- Inverse-QFT recovery of a computational basis state `|c⟩` from the Fourier phase state at
frequency `c`. -/
theorem qftZModOne_symm_phaseVec (p : ℕ) [NeZero p] (c : ZMod p) :
    (qftZModOne p).symm
        ((Real.sqrt (p : ℝ) : ℂ)⁻¹ •
          WithLp.toLp 2 (fun i : ZMod p ↦ (ZMod.stdAddChar (i * c) : ℂ))) =
      EuclideanSpace.single c 1 := by
  have hsingle : qftZModOne p (EuclideanSpace.single c 1) =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ •
        WithLp.toLp 2 (fun i : ZMod p ↦ (ZMod.stdAddChar (i * c) : ℂ)) := by
    ext i
    rw [qftZModOne_apply, Finset.sum_eq_single c]
    · simp [EuclideanSpace.single]
    · intro k _ hk; simp [EuclideanSpace.single, hk]
    · intro hnot; exact False.elim (hnot (Finset.mem_univ c))
  rw [← hsingle, LinearIsometryEquiv.symm_apply_apply]

end DiscreteQFT

end CslibFrontier.Quantum
