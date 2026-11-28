module

public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import CslibFrontier.Foundations.Quantum.DensityMatrix.FidelityTraceDistance
public import Mathlib.Data.Matrix.Basic

import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import CslibFrontier.Foundations.Quantum.DensityMatrix.TraceDistanceDataProcessing
import CslibFrontier.Foundations.Quantum.POVM.Density
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Small-Register Discard Lower Bound on Trace Distance

Proves that discarding a small register `F` of dimension `d = |F|` after applying an isometry
`W : ℂ^N → ℂ^{K × F}` preserves near-maximal trace distance from the maximally mixed state
`ρ₀ = I_N / N` whenever the alternative state `ρ₁` has small rank `s`:
`(1/2) ‖Tr_F(W ρ₁ W†) - Tr_F(W ρ₀ W†)‖_1 ≥ 1 - d^2 s / N`.

## Main results

* `CslibFrontier.Quantum.small_register_rank`: rank-based trace-distance lower bound under
  isometry + partial trace.
-/

public section

namespace CslibFrontier.Quantum

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

/-- Discarding a register `F` of dimension `d = |F|` after an isometry `W : ℂ^N → ℂ^{K × F}`
yields `(1/2) ‖τ₁ - τ₀‖_1 ≥ 1 - d^2 · rank(ρ₁) / N` against the maximally mixed state
`ρ₀ = I_N / N`. -/
theorem small_register_rank {N K F : Type*} [Fintype N] [DecidableEq N]
    [Fintype K] [DecidableEq K] [Fintype F]
    {ρ₁ : Matrix N N ℂ} (hρ₁ : Cslib.Quantum.IsDensityMatrix ρ₁)
    (W : Matrix (K × F) N ℂ) (hW : Wᴴ * W = 1) (hN : 0 < Fintype.card N) :
    let ρ₀ : Matrix N N ℂ := (((Fintype.card N : ℂ)⁻¹)) • (1 : Matrix N N ℂ)
    let τ₁ : Matrix K K ℂ := Cslib.Quantum.partialTraceRight (W * ρ₁ * Wᴴ)
    let τ₀ : Matrix K K ℂ := Cslib.Quantum.partialTraceRight (W * ρ₀ * Wᴴ)
    1 - ((Fintype.card F : ℝ) ^ 2 * (ρ₁.rank : ℝ)) / (Fintype.card N : ℝ) ≤
      Cslib.Quantum.traceDistance τ₁ τ₀ := by
  intro ρ₀ τ₁ τ₀
  classical
  have hNne : (Fintype.card N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hWρ₁_psd : (W * ρ₁ * Wᴴ).PosSemidef := by
    have := hρ₁.1.mul_mul_conjTranspose_same W; simpa [Matrix.mul_assoc] using this
  have hτ₁_psd : τ₁.PosSemidef := Cslib.Quantum.posSemidef_partialTraceRight hWρ₁_psd
  let hH := hτ₁_psd.isHermitian
  let ev := hH.eigenvalues
  let eb := hH.eigenvectorBasis
  let PA : Matrix K K ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i : K => ev i ≠ 0), Cslib.Quantum.pureState (eb i)
  have hmul_eb : ∀ i : K, τ₁ *ᵥ (eb i).ofLp = ((ev i : ℝ) : ℂ) • (eb i).ofLp :=
    fun i => hH.mulVec_eigenvectorBasis i
  have hsum1 : ∑ i : K, Cslib.Quantum.pureState (eb i) = 1 := by
    ext r s
    rw [Matrix.sum_apply]
    simp only [Cslib.Quantum.pureState_apply, eb]
    have hU : (hH.eigenvectorUnitary : Matrix K K ℂ) *
        (hH.eigenvectorUnitary : Matrix K K ℂ)ᴴ = 1 := by
      simpa only [star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
    have h := congrFun (congrFun hU r) s
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have h1m : 1 - PA =
      ∑ i ∈ Finset.univ.filter (fun i : K => ev i = 0), Cslib.Quantum.pureState (eb i) := by
    have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : K => ev i ≠ 0)
      (f := fun i : K => Cslib.Quantum.pureState (eb i))
    simp only [not_not] at hsp
    rw [hsum1] at hsp
    exact (eq_sub_of_add_eq' hsp).symm
  have hPA_proj : PA.PosSemidef ∧ (1 - PA).PosSemidef :=
    ⟨Matrix.posSemidef_sum _ fun _ _ => Cslib.Quantum.posSemidef_pureState _,
      by rw [h1m]; exact Matrix.posSemidef_sum _ fun _ _ => Cslib.Quantum.posSemidef_pureState _⟩
  have htr_PA_τ₁ : (PA * τ₁).trace = 1 := by
    have htr_1m : ((1 - PA) * τ₁).trace = 0 := by
      rw [h1m, Matrix.sum_mul, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hev0 : ev i = 0 := (Finset.mem_filter.mp hi).2
      rw [Matrix.trace]
      have hquad : ∀ r : K, (Cslib.Quantum.pureState (eb i) * τ₁) r r =
          (eb i).ofLp r * star ((τ₁ *ᵥ (eb i).ofLp) r) := by
        intro r; rw [Matrix.mul_apply]; simp only [Cslib.Quantum.pureState_apply]
        have hself : ∀ s : K, star ((eb i).ofLp s) * τ₁ s r =
          star ((eb i).ofLp s) * star (τ₁ r s) := by
          intro s; congr 1; exact (congrFun (congrFun hH.eq s) r).symm
        simp_rw [mul_assoc, hself, ← star_mul, ← Finset.mul_sum, ← star_sum]; rfl
      simp_rw [Matrix.diag_apply, hquad, hmul_eb i, hev0, Complex.ofReal_zero, zero_smul,
        Pi.zero_apply, star_zero, mul_zero, Finset.sum_const_zero]
    have htr1 : τ₁.trace = 1 := by
      rw [Cslib.Quantum.trace_partialTraceRight, Matrix.trace_mul_cycle, hW, Matrix.one_mul, hρ₁.2]
    have hsplit : (PA * τ₁).trace + ((1 - PA) * τ₁).trace = τ₁.trace := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    rw [htr_1m, add_zero, htr1] at hsplit
    exact hsplit
  have hPA_trace_le : (PA.trace).re ≤ (Fintype.card F : ℝ) * (ρ₁.rank : ℝ) := by
    have hPA_tr : (PA.trace).re = ((Finset.univ.filter fun i : K => ev i ≠ 0).card : ℝ) := by
      rw [Matrix.trace_sum, Complex.re_sum]
      have h1 : ∀ i : K, ((Cslib.Quantum.pureState (eb i)).trace).re = 1 := fun i => by
        rw [Cslib.Quantum.trace_pureState, eb.orthonormal.1 i]; norm_num
      simp [h1]
    rw [hPA_tr]
    have hcard_le_rank : (Finset.univ.filter fun i : K => ev i ≠ 0).card ≤ τ₁.rank := by
      have hsub : Submodule.span ℂ ((fun i : {i : K // ev i ≠ 0} => (eb i.1).ofLp) '' Set.univ) ≤
          LinearMap.range τ₁.mulVecLin := by
        rw [Submodule.span_le]
        rintro _ ⟨⟨i, hi⟩, _, rfl⟩
        refine ⟨((ev i : ℝ) : ℂ)⁻¹ • (eb i).ofLp, ?_⟩
        change τ₁ *ᵥ _ = _
        rw [Matrix.mulVec_smul, hmul_eb i, smul_smul,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hi), one_smul]
      have hli : LinearIndependent ℂ (fun i : {i : K // ev i ≠ 0} => (eb i.1).ofLp) := by
        have h := eb.orthonormal.linearIndependent.comp (Subtype.val : {i : K // ev i ≠ 0} → K)
          Subtype.val_injective
        exact (LinearMap.linearIndependent_iff (WithLp.linearEquiv 2 ℂ (K → ℂ)).toLinearMap
          (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℂ (K → ℂ)).injective)).mpr h
      have h1 := Submodule.finrank_mono hsub
      rw [Set.image_univ, finrank_span_eq_card hli, Fintype.card_subtype] at h1
      exact h1
    have hrank_le : τ₁.rank ≤ Fintype.card F * ρ₁.rank := by
      have hτ₁_sum : τ₁ = ∑ f : F,
          (Matrix.of fun k n => W (k, f) n) * ρ₁ * (Matrix.of fun k n => W (k, f) n)ᴴ := by
        ext k₁ k₂; rw [Matrix.sum_apply]
        simp only [τ₁, Cslib.Quantum.partialTraceRight_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
      have hrank_sum : ∀ (s : Finset F) (g : F → Matrix K K ℂ),
          (∑ f ∈ s, g f).rank ≤ ∑ f ∈ s, (g f).rank := by
        intro s g
        induction s using Finset.cons_induction with
        | empty => simp
        | cons f s _ ih =>
          rw [Finset.sum_cons, Finset.sum_cons]
          exact (Matrix.rank_add_le _ _).trans (Nat.add_le_add_left ih _)
      rw [hτ₁_sum]
      calc (∑ f : F, (Matrix.of fun k n => W (k, f) n) * ρ₁ *
              (Matrix.of fun k n => W (k, f) n)ᴴ).rank
          ≤ ∑ f : F, ((Matrix.of fun k n => W (k, f) n) * ρ₁ *
              (Matrix.of fun k n => W (k, f) n)ᴴ).rank := hrank_sum _ _
        _ ≤ ∑ _f : F, ρ₁.rank := Finset.sum_le_sum fun f _ =>
            (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
        _ = Fintype.card F * ρ₁.rank := by simp [Finset.sum_const]
    exact_mod_cast (hcard_le_rank.trans hrank_le)
  have htr_PA_τ₀ : (PA * τ₀).trace.re ≤
      ((Fintype.card F : ℝ) ^ 2 * (ρ₁.rank : ℝ)) / (Fintype.card N : ℝ) := by
    have hEq : (PA * τ₀).trace =
        ((Fintype.card N : ℂ)⁻¹) * ((PA ⊗ₖ (1 : Matrix F F ℂ)) * (W * Wᴴ)).trace := by
      have hτ₀_eq : τ₀ = ((Fintype.card N : ℂ)⁻¹) • Cslib.Quantum.partialTraceRight (W * Wᴴ) := by
        simp only [τ₀, ρ₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Cslib.Quantum.partialTraceRight_smul]
      rw [hτ₀_eq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      congr 1
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Cslib.Quantum.partialTraceRight_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Fintype.sum_prod_type]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f₁ _ => Finset.sum_congr rfl fun k₂ _ => ?_
      symm
      rw [Finset.sum_eq_single f₁]
      · simp
      · intro f₂ _ hf; simp [Ne.symm hf]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h1mWW_psd : (1 - W * Wᴴ).PosSemidef := by
      have hidem : (1 - W * Wᴴ)ᴴ * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
        have hH' : (1 - W * Wᴴ)ᴴ = 1 - W * Wᴴ := by
          simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
        rw [hH', Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
          Matrix.mul_one, Matrix.mul_assoc W Wᴴ, ← Matrix.mul_assoc Wᴴ W Wᴴ, hW, Matrix.one_mul Wᴴ,
          sub_self, sub_zero]
      rw [← hidem]; exact Matrix.posSemidef_conjTranspose_mul_self _
    have hP_psd : (PA ⊗ₖ (1 : Matrix F F ℂ)).PosSemidef :=
      hPA_proj.1.kronecker Matrix.PosSemidef.one
    have hle_tr : ((PA ⊗ₖ (1 : Matrix F F ℂ)) * (W * Wᴴ)).trace.re ≤
      (PA ⊗ₖ (1 : Matrix F F ℂ)).trace.re := by
      have hdiff_nn : 0 ≤ ((PA ⊗ₖ (1 : Matrix F F ℂ)) * (1 - W * Wᴴ)).trace.re :=
        (Complex.nonneg_iff.mp (hP_psd.trace_mul_nonneg h1mWW_psd)).1
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at hdiff_nn
      linarith
    have htr_kron : (PA ⊗ₖ (1 : Matrix F F ℂ)).trace = (Fintype.card F : ℂ) * PA.trace := by
      rw [Matrix.trace_kronecker, Matrix.trace_one, mul_comm]
    rw [hEq, Complex.mul_re]
    have hinv_re : ((Fintype.card N : ℂ)⁻¹).re = (Fintype.card N : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    have hinv_im : ((Fintype.card N : ℂ)⁻¹).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
    rw [hinv_re, hinv_im, zero_mul, sub_zero]
    calc (Fintype.card N : ℝ)⁻¹ * ((PA ⊗ₖ (1 : Matrix F F ℂ)) * (W * Wᴴ)).trace.re
        ≤ (Fintype.card N : ℝ)⁻¹ * (PA ⊗ₖ (1 : Matrix F F ℂ)).trace.re :=
          mul_le_mul_of_nonneg_left hle_tr (by positivity)
      _ = (Fintype.card N : ℝ)⁻¹ * ((Fintype.card F : ℝ) * PA.trace.re) := by
        rw [htr_kron, Complex.mul_re]; simp
      _ ≤ (Fintype.card N : ℝ)⁻¹ * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) * (ρ₁.rank : ℝ)))
        :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPA_trace_le (Nat.cast_nonneg _))
            (by positivity)
      _ = ((Fintype.card F : ℝ) ^ 2 * (ρ₁.rank : ℝ)) / (Fintype.card N : ℝ) := by ring
  let M_povm : Cslib.Quantum.POVM Bool K :=
    { effect := fun b => if b then PA else 1 - PA
      posSemidef := fun b => by cases b <;> simp [hPA_proj.1, hPA_proj.2]
      sum_effect := by rw [Fintype.sum_bool]; simp }
  have hgap' : |M_povm.densityProb τ₁ true - M_povm.densityProb τ₀ true| ≤
    Cslib.Quantum.traceDistance τ₁ τ₀ := by
    have hhalf := Cslib.Quantum.POVM.half_sum_abs_densityProb_sub_le_traceDistance M_povm τ₁ τ₀
    rw [Fintype.sum_bool] at hhalf
    have hsum1 : M_povm.densityProb τ₁ true + M_povm.densityProb τ₁ false = 1 := by
      have h := M_povm.sum_densityProb τ₁; rw [Fintype.sum_bool] at h
      have htr1 : τ₁.trace = 1 := by
        rw [Cslib.Quantum.trace_partialTraceRight, Matrix.trace_mul_cycle, hW, Matrix.one_mul,
          hρ₁.2]
      rw [htr1, Complex.one_re] at h; linarith
    have hsum0 : M_povm.densityProb τ₀ true + M_povm.densityProb τ₀ false = 1 := by
      have h := M_povm.sum_densityProb τ₀; rw [Fintype.sum_bool] at h
      have htr0 : τ₀.trace = 1 := by
        rw [Cslib.Quantum.trace_partialTraceRight, Matrix.trace_mul_cycle, hW, Matrix.one_mul]
        simp [ρ₀, Matrix.trace_one, hNne]
      rw [htr0, Complex.one_re] at h; linarith
    have heq_f : |M_povm.densityProb τ₁ false - M_povm.densityProb τ₀ false| =
        |M_povm.densityProb τ₁ true - M_povm.densityProb τ₀ true| := by
      rw [show M_povm.densityProb τ₁ false - M_povm.densityProb τ₀ false =
          -(M_povm.densityProb τ₁ true - M_povm.densityProb τ₀ true) by linarith, abs_neg]
    rw [heq_f] at hhalf; linarith
  have hp1 : M_povm.densityProb τ₁ true = 1 := by
    change (PA * τ₁).trace.re = 1; rw [htr_PA_τ₁, Complex.one_re]
  have hp0 : M_povm.densityProb τ₀ true = (PA * τ₀).trace.re := rfl
  rw [hp1, hp0] at hgap'
  linarith [le_abs_self (1 - (PA * τ₀).trace.re)]

end CslibFrontier.Quantum
