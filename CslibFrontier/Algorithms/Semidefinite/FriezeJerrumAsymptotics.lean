/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Probability.CDF
public import CslibFrontier.Algorithms.Semidefinite.FriezeJerrumSDP

import CslibFrontier.Foundations.Probability.Gaussian.CDF
import CslibFrontier.Foundations.Probability.Gaussian.Hermite
import CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion
import CslibFrontier.Foundations.Probability.Gaussian.Quantile
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import CslibFrontier.Foundations.Probability.Gaussian.WillinkBounds

/-!
# First-Order Asymptotics of the Frieze–Jerrum Collision Probability

This module derives the exact integral representation and sharp asymptotic behavior of the
first-order Taylor coefficient `c_1(ℓ)` of the Frieze–Jerrum correlated Gaussian collision
probability `N_ℓ(a)` under standard Lean axioms:

1. Exact formula `c_1(ℓ) = ℓ² (ℓ - 1) I_ℓ²` for all `ℓ ≥ 2`, where
   `I_ℓ = ∫ u, φ(u)² Φ(u)^(ℓ - 2) du` (`friezeJerrumFirstIntegral`).
2. Sharp asymptotic `I_ℓ ~ √(2 ln ℓ) / ℓ²`, yielding
   `c_1(ℓ) / (2 ln ℓ / ℓ) → 1` and `c_1(ℓ) / (2 ln ℓ / (ℓ - 1)) → 1` as `ℓ → ∞`.

## Main definitions

* `CslibFrontier.Algorithms.Semidefinite.friezeJerrumFirstIntegral`: the integral
  `I_ℓ = ∫ u, φ(u)² Φ(u)^(ℓ - 2) du`.

## Main results

* `CslibFrontier.Algorithms.Semidefinite.friezeJerrumTaylorCoeff_one_eq`:
  `c_1(ℓ) = ℓ² (ℓ - 1) I_ℓ²` for `ℓ ≥ 2`.
* `CslibFrontier.Algorithms.Semidefinite.tendsto_friezeJerrumFirstIntegral`:
  `ℓ² I_ℓ / √(2 ln ℓ) → 1` as `ℓ → ∞`.
* `CslibFrontier.Algorithms.Semidefinite.tendsto_friezeJerrumTaylorCoeff_one`:
  `c_1(ℓ) / (2 ln ℓ / ℓ) → 1` as `ℓ → ∞`.
* `CslibFrontier.Algorithms.Semidefinite.tendsto_friezeJerrumTaylorCoeff_one_div_pred`:
  `c_1(ℓ) / (2 ln ℓ / (ℓ - 1)) → 1` as `ℓ → ∞`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Finset BigOperators
open scoped NNReal

namespace CslibFrontier.Algorithms.Semidefinite

/-- The Frieze–Jerrum first-order integral `I_ℓ = ∫ u, φ(u)² Φ(u)^(ℓ - 2) du`. -/
@[expose] noncomputable def friezeJerrumFirstIntegral (ℓ : ℕ) : ℝ :=
  ∫ u : ℝ, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)

/-! ### Exact formula for `c_1(ℓ)` -/

private theorem integrable_gaussianPDFReal_sq_mul_cdf_pow (m : ℕ) :
    Integrable (fun u : ℝ => gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ m) := by
  refine Integrable.mono' ((integrable_gaussianPDFReal 0 1).const_mul (√(2 * π))⁻¹) ?_ ?_
  · exact ((continuous_gaussianPDFReal 0 1).pow 2 |>.mul
      ((continuous_cdf_gaussianReal 0 one_ne_zero).pow m)).aestronglyMeasurable
  · refine ae_of_all _ fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (pow_nonneg (cdf_nonneg _ _) _))]
    have hle1 : cdf (gaussianReal 0 1) u ^ m ≤ 1 :=
      pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _)
    have hpdf : gaussianPDFReal 0 1 u ≤ (√(2 * π))⁻¹ := by
      simpa only [NNReal.coe_one, mul_one] using gaussianPDFReal_le 0 1 u
    have hnn := gaussianPDFReal_nonneg 0 1 u
    nlinarith [mul_le_mul_of_nonneg_right hpdf hnn]

private theorem integrable_mul_gaussianPDFReal_mul_cdf_pow (m : ℕ) :
    Integrable (fun u : ℝ => u * gaussianPDFReal 0 1 u * cdf (gaussianReal 0 1) u ^ m) := by
  have hint_id : Integrable (fun u : ℝ => |u| * gaussianPDFReal 0 1 u) := by
    have h := (@integrable_eval_gaussianReal 0 1 (Polynomial.X : Polynomial ℝ)).norm
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, integrable_withDensity_iff
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
    refine h.congr (ae_of_all _ fun u => ?_)
    simp [gaussianPDF, Real.norm_eq_abs, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  refine Integrable.mono' hint_id ?_ ?_
  · exact ((continuous_id.mul (continuous_gaussianPDFReal 0 1)).mul
      ((continuous_cdf_gaussianReal 0 one_ne_zero).pow m)).aestronglyMeasurable
  · refine ae_of_all _ fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
      abs_of_nonneg (pow_nonneg (cdf_nonneg _ _) _)]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (gaussianPDFReal_nonneg _ _ _))
      (pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _))

/-- Integration by parts: `∫ u * φ(u) * Φ(u)^m du = m * ∫ φ(u)² * Φ(u)^(m - 1) du` for `m ≥ 1`. -/
private theorem integral_mul_pdf_cdf_pow {m : ℕ} (_hm : 1 ≤ m) :
    ∫ u : ℝ, u * gaussianPDFReal 0 1 u * cdf (gaussianReal 0 1) u ^ m =
      (m : ℝ) * ∫ u : ℝ, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (m - 1) := by
  let φ := gaussianPDFReal 0 1
  let Φ := cdf (gaussianReal 0 1)
  let F : ℝ → ℝ := fun u => -φ u * Φ u ^ m
  let f : ℝ → ℝ := fun u => u * φ u * Φ u ^ m - (m : ℝ) * (φ u ^ 2 * Φ u ^ (m - 1))
  have hderiv : ∀ u : ℝ, HasDerivAt F (f u) u := by
    intro u
    have hφ : HasDerivAt φ (-u * φ u) u := by
      simpa [φ] using hasDerivAt_gaussianPDFReal 0 1 u
    have hΦ : HasDerivAt (fun t => Φ t ^ m) ((m : ℝ) * Φ u ^ (m - 1) * φ u) u := by
      change HasDerivAt (fun t => (cdf (gaussianReal 0 1) : ℝ → ℝ) t ^ m) _ u
      exact (hasDerivAt_cdf_gaussianReal 0 one_ne_zero u).pow m
    have h1 := hφ.neg.mul hΦ
    convert h1 using 1
    dsimp only [f, Pi.neg_apply]
    ring
  have hf_int : Integrable f :=
    (integrable_mul_gaussianPDFReal_mul_cdf_pow m).sub
      ((integrable_gaussianPDFReal_sq_mul_cdf_pow (m - 1)).const_mul (m : ℝ))
  have hF_zero : Tendsto F atTop (nhds 0) ∧ Tendsto F atBot (nhds 0) := by
    have hφ_top : Tendsto φ atTop (nhds 0) := by
      have hsq : Tendsto (fun u : ℝ => -(u ^ 2 / 2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp
          ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num : (0 : ℝ) < 2))
      have hexp := Real.tendsto_exp_atBot.comp hsq
      simpa [φ, gaussianPDFReal_def, Function.comp_def, neg_div] using hexp.const_mul (√(2 * π))⁻¹
    have hφ_bot : Tendsto φ atBot (nhds 0) := by
      have hcomp := hφ_top.comp tendsto_neg_atBot_atTop
      refine hcomp.congr fun u => ?_
      simp [φ, gaussianPDFReal_def]
    have hbdd : ∀ (l : Filter ℝ), Tendsto φ l (nhds 0) → Tendsto F l (nhds 0) := fun l hl => by
      refine squeeze_zero_norm (fun u => ?_) (by simpa using hl.norm)
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg (cdf_nonneg _ _) _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _))
    exact ⟨hbdd atTop hφ_top, hbdd atBot hφ_bot⟩
  have h0 : ∫ u : ℝ, f u = 0 - 0 :=
    integral_of_hasDerivAt_of_tendsto hderiv hf_int hF_zero.2 hF_zero.1
  rw [sub_zero, integral_sub (integrable_mul_gaussianPDFReal_mul_cdf_pow m)
    ((integrable_gaussianPDFReal_sq_mul_cdf_pow (m - 1)).const_mul (m : ℝ)),
    integral_const_mul] at h0
  linarith

/-- Exact first-order Taylor coefficient `c_1(ℓ) = ℓ² (ℓ - 1) I_ℓ²` for all `ℓ ≥ 2`. -/
theorem friezeJerrumTaylorCoeff_one_eq {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    friezeJerrumTaylorCoeff ℓ 1 =
      (ℓ : ℝ) ^ 2 * ((ℓ : ℝ) - 1) * friezeJerrumFirstIntegral ℓ ^ 2 := by
  classical
  have hℓ0 : 0 < ℓ := by omega
  let γℓ : Measure (Fin ℓ → ℝ) := Measure.pi fun _ : Fin ℓ => gaussianReal 0 1
  let f : (Fin ℓ → ℝ) → ℝ := gaussianMaxIndicator ℓ ⟨0, hℓ0⟩
  let S := (Fintype.piFinset fun _ : Fin ℓ => Finset.range 2).filter
    (fun α : Fin ℓ → ℕ => ∑ i : Fin ℓ, α i = 1)
  have hS : S = Finset.univ.image (fun j : Fin ℓ => Pi.single j (1 : ℕ)) := by
    ext α
    simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hsum⟩
      have hex : ∃ j : Fin ℓ, α j ≠ 0 := by
        by_contra hall
        push Not at hall
        simp [hall] at hsum
      obtain ⟨j, hj⟩ := hex
      have hge1 : 1 ≤ α j := Nat.pos_of_ne_zero hj
      have hle1 : α j ≤ 1 :=
        hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hj1 : α j = 1 := le_antisymm hle1 hge1
      have hother : ∀ i : Fin ℓ, i ≠ j → α i = 0 := by
        intro i hi
        have hsum_er := Finset.add_sum_erase Finset.univ α (Finset.mem_univ j)
        rw [hj1, hsum] at hsum_er
        have h0 : ∑ x ∈ Finset.univ.erase j, α x = 0 := by omega
        exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
      refine ⟨j, ?_⟩
      ext i
      by_cases hij : i = j
      · subst hij; simp [hj1]
      · simp [hij, hother i hij]
    · rintro ⟨j, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hij : i = j <;> simp [hij]
      · simp [Pi.single_apply]
  have hinj : Function.Injective (fun j : Fin ℓ => (Pi.single j (1 : ℕ) : Fin ℓ → ℕ)) := by
    intro i j h
    have := congrFun h i
    by_contra hij
    simp [hij] at this
  have hsum_sq :
      ∑ α ∈ S, hermiteCoeff f α ^ 2 = ∑ j : Fin ℓ, hermiteCoeff f (Pi.single j 1) ^ 2 := by
    rw [hS, Finset.sum_image (fun i _ j _ h => hinj h)]
  have hcoeff_single :
      ∀ j : Fin ℓ, hermiteCoeff f (Pi.single j 1) = ∫ z : Fin ℓ → ℝ, f z * z j ∂γℓ := by
    intro j
    rw [hermiteCoeff_def]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    congr 1
    have hsingle : (Pi.single j (1 : ℕ) : Fin ℓ → ℕ) =
        fun i => if i ∈ ({j} : Finset (Fin ℓ)) then 1 else 0 := by
      ext i; simp [Pi.single_apply]
    rw [hsingle, multiHermite_indicator]
    simp
  have hc0 :
      hermiteCoeff f (Pi.single ⟨0, hℓ0⟩ 1) = ((ℓ : ℝ) - 1) * friezeJerrumFirstIntegral ℓ := by
    rw [hcoeff_single]
    let m : ℕ := ℓ - 1
    have hℓ_eq : ℓ = m + 1 := by omega
    let e : (Fin (m + 1) → ℝ) ≃ᵐ (Fin ℓ → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => ℝ) (finCongr hℓ_eq.symm)
    let eAll : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin ℓ → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.trans e
    have hmp : MeasurePreserving eAll
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) γℓ :=
      (measurePreserving_piCongrLeft (fun _ : Fin ℓ => gaussianReal 0 1)
        (finCongr hℓ_eq.symm)).comp
        (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0).symm
    rw [← hmp.integral_comp']
    have he_app : ∀ (q : ℝ × (Fin m → ℝ)) (d : Fin ℓ),
        eAll q d = ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm q)
          ((finCongr hℓ_eq.symm).symm d) := fun q d => by
      change e ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm q) d = _
      conv_lhs => rw [← (finCongr hℓ_eq.symm).apply_symm_apply d]
      exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (finCongr hℓ_eq.symm) _ _
    have he0 : ∀ q : ℝ × (Fin m → ℝ), eAll q ⟨0, hℓ0⟩ = q.1 := fun q => by
      rw [he_app]
      have hidx : (finCongr hℓ_eq.symm).symm ⟨0, hℓ0⟩ = 0 := by ext; simp
      rw [hidx, MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp [Fin.cons_zero]
    have hint_prod : Integrable (fun q : ℝ × (Fin m → ℝ) => f (eAll q) * eAll q ⟨0, hℓ0⟩)
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
      have hmeas : Measurable (fun q : ℝ × (Fin m → ℝ) => f (eAll q) * q.1) :=
        ((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).comp hmp.measurable).mul measurable_fst
      have hnorm : Integrable (fun q : ℝ × (Fin m → ℝ) => |q.1|)
          ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) :=
        ((@integrable_eval_gaussianReal 0 1 (Polynomial.X : Polynomial ℝ)).norm.congr
          (ae_of_all _ fun _ => by simp)).comp_fst _
      refine Integrable.mono' hnorm (by simpa [he0] using hmeas.aestronglyMeasurable)
        (ae_of_all _ fun q => ?_)
      rw [he0 q, Real.norm_eq_abs, abs_mul]
      have hf1 : |f (eAll q)| ≤ 1 := by
        simp only [f, gaussianMaxIndicator]; split_ifs <;> norm_num
      nlinarith [abs_nonneg q.1]
    rw [integral_prod _ hint_prod]
    have hinner : ∀ u : ℝ, ∫ z' : Fin m → ℝ, f (eAll (u, z')) * eAll (u, z') ⟨0, hℓ0⟩
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) =
        u * cdf (gaussianReal 0 1) u ^ m := by
      intro u
      have hpt : ∀ z' : Fin m → ℝ,
          f (eAll (u, z')) = ∏ j : Fin m, if z' j ≤ u then (1 : ℝ) else 0 := by
        intro z'
        have hsucc : ∀ j : Fin m, eAll (u, z') ⟨j.1 + 1, by omega⟩ = z' j := by
          intro j
          rw [he_app]
          have hidx : (finCongr hℓ_eq.symm).symm ⟨j.1 + 1, by omega⟩ = j.succ := by
            ext; simp [Fin.succ]
          rw [hidx, MeasurableEquiv.piFinSuccAbove_symm_apply]
          simp [Fin.cons_succ]
        simp only [f, gaussianMaxIndicator, he0 (u, z')]
        have hiff : (∀ d : Fin ℓ, eAll (u, z') d ≤ u) ↔ ∀ j : Fin m, z' j ≤ u := by
          constructor
          · intro h j; rw [← hsucc j]; exact h _
          · intro h d
            by_cases hd : d.1 = 0
            · have : d = ⟨0, hℓ0⟩ := Fin.ext hd; subst this; rw [he0 (u, z')]
            · let j : Fin m := ⟨d.1 - 1, by omega⟩
              have hd_eq : d = ⟨j.1 + 1, by omega⟩ := Fin.ext (by simp [j]; omega)
              rw [hd_eq, hsucc j]; exact h j
        rw [if_congr hiff rfl rfl]
        by_cases hall : ∀ j : Fin m, z' j ≤ u
        · simp [hall]
        · simp only [hall, ↓reduceIte]
          push Not at hall
          obtain ⟨j, hj⟩ := hall
          exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [not_le.mpr hj])).symm
      simp only [he0, hpt, integral_mul_const]
      rw [integral_fintype_prod_eq_prod (f := fun _ r => if r ≤ u then (1 : ℝ) else 0)]
      have h1 : ∫ r : ℝ, (if r ≤ u then (1 : ℝ) else 0) ∂(gaussianReal 0 1) =
          cdf (gaussianReal 0 1) u := by
        have hind : (fun r : ℝ => if r ≤ u then (1 : ℝ) else 0) =
            (Iic u).indicator (fun _ => (1 : ℝ)) := by
          ext r; simp [Set.indicator]
        rw [hind, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one, ← cdf_eq_real]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, h1, mul_comm]
    simp only [hinner]
    let ν := gaussianReal 0 1
    change ∫ u : ℝ, u * cdf ν u ^ m ∂(gaussianReal 0 1) = _
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have hrew : (fun u : ℝ => (gaussianPDF 0 1 u).toReal • (u * cdf ν u ^ m)) =
        fun u : ℝ => u * gaussianPDFReal 0 1 u * cdf ν u ^ m := by
      ext u
      simp only [gaussianPDF, smul_eq_mul, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
      ring
    rw [hrew, integral_mul_pdf_cdf_pow (by omega : 1 ≤ m)]
    have hm_cast : (m : ℝ) = (ℓ : ℝ) - 1 := by
      dsimp only [m]; rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]; simp
    have hm1 : m - 1 = ℓ - 2 := by omega
    rw [hm_cast, hm1]
    rfl
  have hc_other_eq : ∀ j₁ j₂ : Fin ℓ, j₁ ≠ ⟨0, hℓ0⟩ → j₂ ≠ ⟨0, hℓ0⟩ →
      hermiteCoeff f (Pi.single j₁ 1) = hermiteCoeff f (Pi.single j₂ 1) := by
    intro j₁ j₂ hj₁ hj₂
    rw [hcoeff_single j₁, hcoeff_single j₂]
    let σ : Equiv.Perm (Fin ℓ) := Equiv.swap j₁ j₂
    let e := MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => ℝ) σ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin ℓ => gaussianReal 0 1) σ
    rw [← hmp.integral_comp']
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have he_app : ∀ d : Fin ℓ, e z d = z (σ.symm d) := fun d => by
      conv_lhs => rw [← σ.apply_symm_apply d]
      exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) σ z _
    have hσ0 : σ.symm ⟨0, hℓ0⟩ = ⟨0, hℓ0⟩ := by
      simp [σ, Equiv.swap_apply_of_ne_of_ne hj₁.symm hj₂.symm]
    have hσj : σ.symm j₁ = j₂ := by simp [σ]
    change f (e z) * e z j₁ = f z * z j₂
    simp only [he_app, hσj, f, gaussianMaxIndicator, hσ0]
    congr 1
    exact if_congr ⟨fun h d => by simpa using h (σ d), fun h d => h _⟩ rfl rfl
  have hsum_zero : ∑ j : Fin ℓ, hermiteCoeff f (Pi.single j 1) = 0 := by
    simp only [hcoeff_single]
    rw [← integral_finsetSum _ fun j _ => ?_]
    · simp only [← Finset.mul_sum]
      have hsym_c : ∀ c : Fin ℓ,
          ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ c z * (∑ j : Fin ℓ, z j) ∂γℓ =
            ∫ z : Fin ℓ → ℝ, f z * (∑ j : Fin ℓ, z j) ∂γℓ := by
        intro c
        let σ := Equiv.swap c ⟨0, hℓ0⟩
        let ec := MeasurableEquiv.piCongrLeft (fun _ : Fin ℓ => ℝ) σ
        have hmp := measurePreserving_piCongrLeft (fun _ : Fin ℓ => gaussianReal 0 1) σ
        rw [← hmp.integral_comp']
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        have he_app : ∀ d : Fin ℓ, ec z d = z (σ.symm d) := fun d => by
          conv_lhs => rw [← σ.apply_symm_apply d]
          exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) σ z _
        change gaussianMaxIndicator ℓ c (ec z) * (∑ j : Fin ℓ, ec z j) =
          f z * (∑ j : Fin ℓ, z j)
        simp only [he_app, f, gaussianMaxIndicator]
        have hsum_perm : ∑ j : Fin ℓ, z (σ.symm j) = ∑ j : Fin ℓ, z j :=
          Equiv.sum_comp σ.symm z
        rw [hsum_perm]
        congr 1
        have h0 : σ.symm c = ⟨0, hℓ0⟩ := by simp [σ]
        rw [h0]
        exact if_congr ⟨fun h d => by simpa using h (σ d), fun h d => h _⟩ rfl rfl
      have htot : (ℓ : ℝ) * ∫ z : Fin ℓ → ℝ, f z * (∑ j : Fin ℓ, z j) ∂γℓ = 0 := by
        have hsum_c :
            ∑ c : Fin ℓ, ∫ z : Fin ℓ → ℝ, gaussianMaxIndicator ℓ c z * (∑ j : Fin ℓ, z j) ∂γℓ =
              (ℓ : ℝ) * ∫ z : Fin ℓ → ℝ, f z * (∑ j : Fin ℓ, z j) ∂γℓ := by
          simp [hsym_c]
        rw [← hsum_c, ← integral_finsetSum]
        · have hae :
              (fun z : Fin ℓ → ℝ => ∑ c : Fin ℓ, gaussianMaxIndicator ℓ c z * (∑ j : Fin ℓ, z j))
                =ᵐ[γℓ] fun z => ∑ j : Fin ℓ, z j := by
            filter_upwards [ae_pairwise_ne_pi_gaussianReal ℓ] with z hz
            rw [← Finset.sum_mul]
            let m := argmaxFin hℓ0 z
            rw [Finset.sum_eq_single m]
            · simp [gaussianMaxIndicator, m, argmaxFin_le hℓ0 z]
            · intro d _ hdm
              have hlt : z d < z m := lt_of_le_of_ne (argmaxFin_le hℓ0 z d) (hz d m hdm)
              have hnot : ¬ ∀ e, z e ≤ z d := fun h => not_lt_of_ge (h m) hlt
              simp [gaussianMaxIndicator, hnot]
            · intro h; exact absurd (Finset.mem_univ m) h
          rw [integral_congr_ae hae, integral_finsetSum]
          · refine Finset.sum_eq_zero fun j _ => ?_
            have hmp := measurePreserving_eval (fun _ : Fin ℓ => gaussianReal 0 1) j
            have hmap : ∫ z : Fin ℓ → ℝ, z j ∂γℓ = ∫ r : ℝ, r ∂(gaussianReal 0 1) := by
              rw [← hmp.map_eq]
              change ∫ z : Fin ℓ → ℝ, id (Function.eval j z) ∂γℓ =
                ∫ r : ℝ, id r ∂(Measure.map (Function.eval j) γℓ)
              exact (integral_map
                (measurable_pi_apply (X := fun _ : Fin ℓ => ℝ) j).aemeasurable
                aestronglyMeasurable_id).symm
            rw [hmap, integral_id_gaussianReal]
          · intro j _
            have hmp := measurePreserving_eval (fun _ : Fin ℓ => gaussianReal 0 1) j
            have hX : Integrable (fun r : ℝ => r) (gaussianReal 0 1) :=
              (@integrable_eval_gaussianReal 0 1 (Polynomial.X : Polynomial ℝ)).congr
                (ae_of_all _ fun _ => by simp)
            exact (hmp.integrable_comp hX.aestronglyMeasurable).mpr hX
        · intro c _
          have hint_sum : Integrable (fun z : Fin ℓ → ℝ => ∑ j : Fin ℓ, |z j|) γℓ :=
            integrable_finsetSum _ fun j _ => by
              have hmp := measurePreserving_eval (fun _ : Fin ℓ => gaussianReal 0 1) j
              have hX : Integrable (fun r : ℝ => |r|) (gaussianReal 0 1) :=
                (@integrable_eval_gaussianReal 0 1 (Polynomial.X : Polynomial ℝ)).norm.congr
                  (ae_of_all _ fun _ => by simp)
              exact (hmp.integrable_comp hX.aestronglyMeasurable).mpr hX
          refine Integrable.mono' hint_sum ?_ (ae_of_all _ fun z => ?_)
          · exact ((measurable_gaussianMaxIndicator ℓ c).mul
              (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)).aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_mul]
            have h1 : |gaussianMaxIndicator ℓ c z| ≤ 1 := by
              simp only [gaussianMaxIndicator]; split_ifs <;> norm_num
            calc |gaussianMaxIndicator ℓ c z| * |∑ j, z j|
                ≤ 1 * |∑ j, z j| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
              _ ≤ ∑ j, |z j| := by rw [one_mul]; exact Finset.abs_sum_le_sum_abs _ _
      have hℓ_ne : (ℓ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hℓ0).ne'
      exact (mul_eq_zero.mp htot).resolve_left hℓ_ne
    · have hmp := measurePreserving_eval (fun _ : Fin ℓ => gaussianReal 0 1) j
      have hX : Integrable (fun r : ℝ => |r|) (gaussianReal 0 1) :=
        (@integrable_eval_gaussianReal 0 1 (Polynomial.X : Polynomial ℝ)).norm.congr
          (ae_of_all _ fun _ => by simp)
      have hint_j : Integrable (fun z : Fin ℓ → ℝ => |z j|) γℓ :=
        (hmp.integrable_comp hX.aestronglyMeasurable).mpr hX
      refine Integrable.mono' hint_j
        ((measurable_gaussianMaxIndicator ℓ ⟨0, hℓ0⟩).mul
          (measurable_pi_apply j)).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |f z| ≤ 1 := by simp only [f, gaussianMaxIndicator]; split_ifs <;> norm_num
      nlinarith [abs_nonneg (z j)]
  have hc_other : ∀ j : Fin ℓ, j ≠ ⟨0, hℓ0⟩ →
      hermiteCoeff f (Pi.single j 1) = -friezeJerrumFirstIntegral ℓ := by
    intro j hj
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ⟨0, hℓ0⟩), hc0] at hsum_zero
    have hrest : ∑ i ∈ Finset.univ.erase ⟨0, hℓ0⟩, hermiteCoeff f (Pi.single i 1) =
        ((ℓ : ℝ) - 1) * hermiteCoeff f (Pi.single j 1) := by
      have h1 : ∀ i ∈ Finset.univ.erase ⟨0, hℓ0⟩,
          hermiteCoeff f (Pi.single i 1) = hermiteCoeff f (Pi.single j 1) :=
        fun i hi => hc_other_eq i j (Finset.mem_erase.mp hi).1 hj
      rw [Finset.sum_congr rfl h1, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
    rw [hrest] at hsum_zero
    have hℓm1 : (ℓ : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
      linarith
    have hmul :
        ((ℓ : ℝ) - 1) * (hermiteCoeff f (Pi.single j 1) + friezeJerrumFirstIntegral ℓ) = 0 := by
      linarith
    linarith [(mul_eq_zero.mp hmul).resolve_left hℓm1]
  simp only [friezeJerrumTaylorCoeff, hℓ0, ↓reduceDIte]
  rw [hsum_sq, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ⟨0, hℓ0⟩), hc0]
  have hrest_sq : ∑ j ∈ Finset.univ.erase ⟨0, hℓ0⟩, hermiteCoeff f (Pi.single j 1) ^ 2 =
      ((ℓ : ℝ) - 1) * friezeJerrumFirstIntegral ℓ ^ 2 := by
    have h1 : ∀ j ∈ Finset.univ.erase ⟨0, hℓ0⟩,
        hermiteCoeff f (Pi.single j 1) ^ 2 = friezeJerrumFirstIntegral ℓ ^ 2 := fun j hj => by
      rw [hc_other j (Finset.mem_erase.mp hj).1]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  rw [hrest_sq]
  ring

/-! ### Sharp asymptotic `I_ℓ ~ √(2 ln ℓ) / ℓ²` and `c_1(ℓ) ~ 2 ln ℓ / ℓ` -/

private theorem hasDerivAt_fjAntideriv (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (u : ℝ) :
    HasDerivAt (fun t => cdf (gaussianReal 0 1) t ^ (ℓ - 1) / ((ℓ : ℝ) - 1) -
        cdf (gaussianReal 0 1) t ^ ℓ / (ℓ : ℝ))
      ((1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) *
        gaussianPDFReal 0 1 u) u := by
  have hℓ_real : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by linarith
  have hℓm1 : (ℓ : ℝ) - 1 ≠ 0 := by linarith
  have hΦ := hasDerivAt_cdf_gaussianReal 0 one_ne_zero u
  have h1 := (hΦ.pow (ℓ - 1)).div_const ((ℓ : ℝ) - 1)
  have h2 := (hΦ.pow ℓ).div_const (ℓ : ℝ)
  have hsub := h1.sub h2
  have hc1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]; simp
  have hsub2 : ℓ - 1 - 1 = ℓ - 2 := by omega
  have hpow : cdf (gaussianReal 0 1) u ^ (ℓ - 1) =
      cdf (gaussianReal 0 1) u * cdf (gaussianReal 0 1) u ^ (ℓ - 2) := by
    conv_lhs => rw [show ℓ - 1 = (ℓ - 2) + 1 by omega, pow_succ']
  convert hsub using 1
  rw [hc1, hsub2, hpow]
  field_simp [hℓ0, hℓm1]

private theorem integrable_fjAntideriv_deriv (ℓ : ℕ) :
    Integrable (fun u : ℝ =>
      (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) *
        gaussianPDFReal 0 1 u) := by
  refine Integrable.mono' (integrable_gaussianPDFReal 0 1) ?_ (ae_of_all _ fun u => ?_)
  · exact (((continuous_const.sub (continuous_cdf_gaussianReal 0 one_ne_zero)).mul
      ((continuous_cdf_gaussianReal 0 one_ne_zero).pow (ℓ - 2))).mul
      (continuous_gaussianPDFReal 0 1)).aestronglyMeasurable
  · have h0 : 0 ≤ (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) :=
      mul_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) (pow_nonneg (cdf_nonneg _ _) _)
    have h1 : (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤ 1 := by
      calc (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
          ≤ 1 * 1 := mul_le_mul (by linarith [cdf_nonneg (gaussianReal 0 1) u])
            (pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _)) (pow_nonneg (cdf_nonneg _ _) _)
            zero_le_one
        _ = 1 := one_mul 1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (gaussianPDFReal_nonneg _ _ _))]
    exact mul_le_of_le_one_left (gaussianPDFReal_nonneg _ _ _) h1

private theorem fj_integral_Ioi_pdf (u : ℝ) :
    ∫ t in Ioi u, gaussianPDFReal 0 1 t = cdf (gaussianReal 0 1) (-u) := by
  have hneg := cdf_gaussianReal_neg (v := 1) one_ne_zero u
  rw [cdf_gaussianReal_eq_integral 0 one_ne_zero u] at hneg
  have htot := integral_gaussianPDFReal_eq_one 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  have hsp : (∫ t in Iic u, gaussianPDFReal 0 1 t) + (∫ t in Ioi u, gaussianPDFReal 0 1 t) =
      ∫ t, gaussianPDFReal 0 1 t := by
    rw [← setIntegral_union (disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2)
      measurableSet_Ioi (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn, Iic_union_Ioi, Measure.restrict_univ]
  linarith

private theorem fj_inv_sqrt_two_pi_le_one : (√(2 * π))⁻¹ ≤ 1 := by
  have hpi : (1 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.pi_gt_three]
  exact inv_le_one_of_one_le₀ hpi

private theorem fj_left_tail_le {ℓ : ℕ} {u₁ B : ℝ}
    (hB : cdf (gaussianReal 0 1) u₁ ^ (ℓ - 2) ≤ B) :
    ∫ u in Iic u₁, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤ B := by
  have hB_nn : 0 ≤ B := le_trans (pow_nonneg (cdf_nonneg _ _) _) hB
  calc ∫ u in Iic u₁, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
      ≤ ∫ u in Iic u₁, gaussianPDFReal 0 1 u * B := by
        refine setIntegral_mono_on
          (integrable_gaussianPDFReal_sq_mul_cdf_pow (ℓ - 2)).integrableOn
          ((integrable_gaussianPDFReal 0 1).mul_const B).integrableOn
          measurableSet_Iic fun u hu => ?_
        have hΦu : cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤ B :=
          (pow_le_pow_left₀ (cdf_nonneg _ _)
            ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone hu) _).trans hB
        have hφ1 : gaussianPDFReal 0 1 u ≤ 1 := by
          have := gaussianPDFReal_le 0 1 u
          simp only [NNReal.coe_one, mul_one] at this
          exact this.trans fj_inv_sqrt_two_pi_le_one
        have hsq : gaussianPDFReal 0 1 u ^ 2 ≤ gaussianPDFReal 0 1 u := by
          nlinarith [gaussianPDFReal_nonneg 0 1 u]
        calc gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
            ≤ gaussianPDFReal 0 1 u * cdf (gaussianReal 0 1) u ^ (ℓ - 2) :=
              mul_le_mul_of_nonneg_right hsq (pow_nonneg (cdf_nonneg _ _) _)
          _ ≤ gaussianPDFReal 0 1 u * B :=
              mul_le_mul_of_nonneg_left hΦu (gaussianPDFReal_nonneg 0 1 u)
    _ = (∫ u in Iic u₁, gaussianPDFReal 0 1 u) * B := integral_mul_const _ _
    _ ≤ 1 * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB_nn
        rw [← cdf_gaussianReal_eq_integral 0 one_ne_zero u₁]
        exact cdf_le_one _ _
    _ = B := one_mul _

private theorem fj_right_tail_le {ℓ : ℕ} {u₂ : ℝ} (hu2 : 1 ≤ u₂) :
    ∫ u in Ioi u₂, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤
      gaussianPDFReal 0 1 u₂ ^ 2 := by
  have hu2_pos : 0 < u₂ := lt_of_lt_of_le zero_lt_one hu2
  calc ∫ u in Ioi u₂, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
      ≤ ∫ u in Ioi u₂, gaussianPDFReal 0 1 u₂ * gaussianPDFReal 0 1 u := by
        refine setIntegral_mono_on
          (integrable_gaussianPDFReal_sq_mul_cdf_pow (ℓ - 2)).integrableOn
          ((integrable_gaussianPDFReal 0 1).const_mul _).integrableOn
          measurableSet_Ioi fun u hu => ?_
        have hφu : gaussianPDFReal 0 1 u ≤ gaussianPDFReal 0 1 u₂ := by
          rw [gaussianPDFReal_def]
          dsimp only
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          simp only [sub_zero, NNReal.coe_one, mul_one, neg_div, neg_le_neg_iff]
          exact div_le_div_of_nonneg_right (by nlinarith [hu.le]) (by norm_num)
        have hΦ1 : cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤ 1 :=
          pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _)
        calc gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
            ≤ gaussianPDFReal 0 1 u ^ 2 * 1 := mul_le_mul_of_nonneg_left hΦ1 (sq_nonneg _)
          _ = gaussianPDFReal 0 1 u * gaussianPDFReal 0 1 u := by ring
          _ ≤ gaussianPDFReal 0 1 u₂ * gaussianPDFReal 0 1 u :=
              mul_le_mul_of_nonneg_right hφu (gaussianPDFReal_nonneg 0 1 u)
    _ = gaussianPDFReal 0 1 u₂ * ∫ u in Ioi u₂, gaussianPDFReal 0 1 u := integral_const_mul _ _
    _ = gaussianPDFReal 0 1 u₂ * cdf (gaussianReal 0 1) (-u₂) := by rw [fj_integral_Ioi_pdf u₂]
    _ ≤ gaussianPDFReal 0 1 u₂ * (gaussianPDFReal 0 1 u₂ / u₂) :=
        mul_le_mul_of_nonneg_left (
          CslibFrontier.Foundations.Probability.Gaussian.millsRatio_upper hu2_pos)
          (gaussianPDFReal_nonneg 0 1 u₂)
    _ ≤ gaussianPDFReal 0 1 u₂ ^ 2 := by
        have hdiv : gaussianPDFReal 0 1 u₂ / u₂ ≤ gaussianPDFReal 0 1 u₂ :=
          div_le_self (gaussianPDFReal_nonneg 0 1 u₂) hu2
        nlinarith [gaussianPDFReal_nonneg 0 1 u₂]

private theorem fj_mid_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {u₁ u₂ : ℝ} (hu1 : 0 < u₁)
    (h12 : u₁ ≤ u₂) :
    let G := fun t => cdf (gaussianReal 0 1) t ^ (ℓ - 1) / ((ℓ : ℝ) - 1) -
      cdf (gaussianReal 0 1) t ^ ℓ / (ℓ : ℝ)
    u₁ * (G u₂ - G u₁) ≤
      ∫ u in Ioc u₁ u₂, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2) ∧
    ∫ u in Ioc u₁ u₂, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤
      (u₂ + 1 / u₁) * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) := by
  intro G
  have hℓ_real : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hℓm1_pos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  let gG : ℝ → ℝ := fun u =>
    (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) * gaussianPDFReal 0 1 u
  have hgG_int : Integrable gG := integrable_fjAntideriv_deriv ℓ
  have hG_top : Tendsto G atTop (nhds (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)))) := by
    have h1 := ((tendsto_cdf_atTop (gaussianReal 0 1)).pow (ℓ - 1)).div_const ((ℓ : ℝ) - 1)
    have h2 := ((tendsto_cdf_atTop (gaussianReal 0 1)).pow ℓ).div_const (ℓ : ℝ)
    have hval : (1 : ℝ) ^ (ℓ - 1) / ((ℓ : ℝ) - 1) - (1 : ℝ) ^ ℓ / (ℓ : ℝ) =
        1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
      simp only [one_pow]
      field_simp [hℓ_pos.ne', hℓm1_pos.ne']
      ring
    rw [← hval]
    exact h1.sub h2
  have hG_bot : Tendsto G atBot (nhds 0) := by
    have h1 := ((tendsto_cdf_atBot (gaussianReal 0 1)).pow (ℓ - 1)).div_const ((ℓ : ℝ) - 1)
    have h2 := ((tendsto_cdf_atBot (gaussianReal 0 1)).pow ℓ).div_const (ℓ : ℝ)
    simpa [zero_pow (by omega : ℓ - 1 ≠ 0), zero_pow (by omega : ℓ ≠ 0)] using h1.sub h2
  have hint_gG_all : ∫ u : ℝ, gG u = 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
    have := integral_of_hasDerivAt_of_tendsto (hasDerivAt_fjAntideriv ℓ hℓ) hgG_int hG_bot hG_top
    linarith
  have hint_gG_Ioc : ∫ u in Ioc u₁ u₂, gG u = G u₂ - G u₁ := by
    rw [← intervalIntegral.integral_of_le h12]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_fjAntideriv ℓ hℓ u) hgG_int.intervalIntegrable
  constructor
  · rw [← hint_gG_Ioc, ← integral_const_mul]
    refine setIntegral_mono_on (hgG_int.const_mul _).integrableOn
      (integrable_gaussianPDFReal_sq_mul_cdf_pow (ℓ - 2)).integrableOn measurableSet_Ioc
      fun u hu => ?_
    have hu_pos : 0 < u := lt_trans hu1 hu.1
    have h1m : 1 - cdf (gaussianReal 0 1) u = cdf (gaussianReal 0 1) (-u) := by
      have := cdf_gaussianReal_neg (v := 1) one_ne_zero u; linarith
    have hφ_ge : u * (1 - cdf (gaussianReal 0 1) u) ≤ gaussianPDFReal 0 1 u := by
      rw [h1m]
      have hm := CslibFrontier.Foundations.Probability.Gaussian.millsRatio_upper hu_pos
      linarith [(le_div_iff₀ hu_pos).mp hm]
    have hφ_ge2 : u₁ * (1 - cdf (gaussianReal 0 1) u) ≤ gaussianPDFReal 0 1 u :=
      (mul_le_mul_of_nonneg_right hu.1.le (sub_nonneg.mpr (cdf_le_one _ _))).trans hφ_ge
    have hstep := mul_le_mul_of_nonneg_right hφ_ge2
      (mul_nonneg (gaussianPDFReal_nonneg 0 1 u)
        (pow_nonneg (cdf_nonneg (gaussianReal 0 1) u) (ℓ - 2)))
    dsimp only [gG]; linarith
  · have hu2_pos : 0 < u₂ := lt_of_lt_of_le hu1 h12
    calc ∫ u in Ioc u₁ u₂, gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
        ≤ ∫ u in Ioc u₁ u₂, (u₂ + 1 / u₁) * gG u := by
          refine setIntegral_mono_on
            (integrable_gaussianPDFReal_sq_mul_cdf_pow (ℓ - 2)).integrableOn
            (hgG_int.const_mul _).integrableOn measurableSet_Ioc fun u hu => ?_
          have hu_pos : 0 < u := lt_trans hu1 hu.1
          have h1m : 1 - cdf (gaussianReal 0 1) u = cdf (gaussianReal 0 1) (-u) := by
            have := cdf_gaussianReal_neg (v := 1) one_ne_zero u; linarith
          have hφ_le : gaussianPDFReal 0 1 u ≤ (u + 1 / u) * (1 - cdf (gaussianReal 0 1) u) := by
            rw [h1m]
            have hden : 0 < u ^ 2 + 1 := by positivity
            have hmul := mul_le_mul_of_nonneg_right (
              CslibFrontier.Foundations.Probability.Gaussian.millsRatio_lower u)
              hden.le
            have hmul2 : gaussianPDFReal 0 1 u * u ≤ cdf (gaussianReal 0 1) (-u) * (u ^ 2 + 1) := by
              have hcancel : u / (u ^ 2 + 1) * gaussianPDFReal 0 1 u * (u ^ 2 + 1) =
                  gaussianPDFReal 0 1 u * u := by field_simp [hden.ne']
              linarith
            have hdiv := (le_div_iff₀ hu_pos).mpr hmul2
            calc gaussianPDFReal 0 1 u ≤ cdf (gaussianReal 0 1) (-u) * (u ^ 2 + 1) / u := hdiv
              _ = (u + 1 / u) * cdf (gaussianReal 0 1) (-u) := by field_simp [hu_pos.ne']
          have hu_bound : u + 1 / u ≤ u₂ + 1 / u₁ := by
            linarith [one_div_le_one_div_of_le hu1 hu.1.le, hu.2]
          have hφ_le2 : gaussianPDFReal 0 1 u ≤ (u₂ + 1 / u₁) * (1 - cdf (gaussianReal 0 1) u) :=
            hφ_le.trans (mul_le_mul_of_nonneg_right hu_bound (sub_nonneg.mpr (cdf_le_one _ _)))
          have hstep := mul_le_mul_of_nonneg_right hφ_le2
            (mul_nonneg (gaussianPDFReal_nonneg 0 1 u)
              (pow_nonneg (cdf_nonneg (gaussianReal 0 1) u) (ℓ - 2)))
          dsimp only [gG]; linarith
      _ = (u₂ + 1 / u₁) * ∫ u in Ioc u₁ u₂, gG u := integral_const_mul _ _
      _ ≤ (u₂ + 1 / u₁) * ∫ u : ℝ, gG u := by
          refine mul_le_mul_of_nonneg_left
            (setIntegral_le_integral hgG_int (ae_of_all _ fun u => ?_)) (by positivity)
          exact mul_nonneg (mul_nonneg (sub_nonneg.mpr (cdf_le_one _ _))
            (pow_nonneg (cdf_nonneg _ _) _)) (gaussianPDFReal_nonneg _ _ _)
      _ = (u₂ + 1 / u₁) * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) := by rw [hint_gG_all]

private theorem fj_antideriv_right_tail {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {u₂ : ℝ} (hu2 : 1 ≤ u₂) :
    1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) -
      (cdf (gaussianReal 0 1) u₂ ^ (ℓ - 1) / ((ℓ : ℝ) - 1) -
        cdf (gaussianReal 0 1) u₂ ^ ℓ / (ℓ : ℝ)) ≤
      gaussianPDFReal 0 1 u₂ ^ 2 := by
  have hℓ_real : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hℓm1_pos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hu2_pos : 0 < u₂ := lt_of_lt_of_le zero_lt_one hu2
  let G : ℝ → ℝ := fun t =>
    cdf (gaussianReal 0 1) t ^ (ℓ - 1) / ((ℓ : ℝ) - 1) - cdf (gaussianReal 0 1) t ^ ℓ / (ℓ : ℝ)
  let gG : ℝ → ℝ := fun u =>
    (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) * gaussianPDFReal 0 1 u
  have hgG_int : Integrable gG := integrable_fjAntideriv_deriv ℓ
  have hG_top : Tendsto G atTop (nhds (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)))) := by
    have h1 := ((tendsto_cdf_atTop (gaussianReal 0 1)).pow (ℓ - 1)).div_const ((ℓ : ℝ) - 1)
    have h2 := ((tendsto_cdf_atTop (gaussianReal 0 1)).pow ℓ).div_const (ℓ : ℝ)
    have hval : (1 : ℝ) ^ (ℓ - 1) / ((ℓ : ℝ) - 1) - (1 : ℝ) ^ ℓ / (ℓ : ℝ) =
        1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
      simp only [one_pow]
      field_simp [hℓ_pos.ne', hℓm1_pos.ne']
      ring
    rw [← hval]
    exact h1.sub h2
  have hG_bot : Tendsto G atBot (nhds 0) := by
    have h1 := ((tendsto_cdf_atBot (gaussianReal 0 1)).pow (ℓ - 1)).div_const ((ℓ : ℝ) - 1)
    have h2 := ((tendsto_cdf_atBot (gaussianReal 0 1)).pow ℓ).div_const (ℓ : ℝ)
    simpa [zero_pow (by omega : ℓ - 1 ≠ 0), zero_pow (by omega : ℓ ≠ 0)] using h1.sub h2
  have hG_Ioi : ∫ u in Ioi u₂, gG u = 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) - G u₂ := by
    have htot : ∫ u : ℝ, gG u = 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
      have := integral_of_hasDerivAt_of_tendsto (hasDerivAt_fjAntideriv ℓ hℓ) hgG_int hG_bot hG_top
      linarith
    have hsp : (∫ u in Iic u₂, gG u) + (∫ u in Ioi u₂, gG u) = ∫ u, gG u := by
      rw [← setIntegral_union (disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2)
        measurableSet_Ioi hgG_int.integrableOn hgG_int.integrableOn, Iic_union_Ioi,
        Measure.restrict_univ]
    have hIic : ∫ u in Iic u₂, gG u = G u₂ := by
      have := integral_Iic_of_hasDerivAt_of_tendsto' (a := u₂)
        (fun u _ => hasDerivAt_fjAntideriv ℓ hℓ u) (hgG_int.integrableOn (s := Iic u₂)) hG_bot
      simpa [sub_zero] using this
    linarith
  change 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) - G u₂ ≤ gaussianPDFReal 0 1 u₂ ^ 2
  rw [← hG_Ioi]
  calc ∫ u in Ioi u₂, gG u
      ≤ ∫ u in Ioi u₂, (1 - cdf (gaussianReal 0 1) u₂) * gaussianPDFReal 0 1 u := by
        refine setIntegral_mono_on hgG_int.integrableOn
          ((integrable_gaussianPDFReal 0 1).const_mul _).integrableOn
          measurableSet_Ioi fun u hu => ?_
        dsimp only [gG]
        have h1 : 1 - cdf (gaussianReal 0 1) u ≤ 1 - cdf (gaussianReal 0 1) u₂ :=
          sub_le_sub_left ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone hu.le) 1
        have h2 : (1 - cdf (gaussianReal 0 1) u) * cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤
            1 - cdf (gaussianReal 0 1) u₂ := by
          have hle1 : cdf (gaussianReal 0 1) u ^ (ℓ - 2) ≤ 1 :=
            pow_le_one₀ (cdf_nonneg (gaussianReal 0 1) u) (cdf_le_one (gaussianReal 0 1) u)
          have := mul_le_of_le_one_right (sub_nonneg.mpr (cdf_le_one (gaussianReal 0 1) u)) hle1
          linarith
        exact mul_le_mul_of_nonneg_right h2 (gaussianPDFReal_nonneg 0 1 u)
    _ = (1 - cdf (gaussianReal 0 1) u₂) * ∫ u in Ioi u₂, gaussianPDFReal 0 1 u :=
        integral_const_mul _ _
    _ = cdf (gaussianReal 0 1) (-u₂) * cdf (gaussianReal 0 1) (-u₂) := by
        rw [fj_integral_Ioi_pdf u₂]
        have hneg := cdf_gaussianReal_neg (v := 1) one_ne_zero u₂
        congr 1; linarith
    _ ≤ (gaussianPDFReal 0 1 u₂ / u₂) * (gaussianPDFReal 0 1 u₂ / u₂) :=
        mul_le_mul (CslibFrontier.Foundations.Probability.Gaussian.millsRatio_upper hu2_pos)
          (CslibFrontier.Foundations.Probability.Gaussian.millsRatio_upper hu2_pos) (cdf_nonneg _ _)
          (div_nonneg (gaussianPDFReal_nonneg _ _ _) hu2_pos.le)
    _ ≤ gaussianPDFReal 0 1 u₂ ^ 2 := by
        have hdiv : gaussianPDFReal 0 1 u₂ / u₂ ≤ gaussianPDFReal 0 1 u₂ :=
          div_le_self (gaussianPDFReal_nonneg 0 1 u₂) hu2
        nlinarith [gaussianPDFReal_nonneg 0 1 u₂,
          div_nonneg (gaussianPDFReal_nonneg 0 1 u₂) hu2_pos.le]

private theorem tendsto_nat_sub_div_self (c : ℝ) :
    Tendsto (fun ℓ : ℕ => ((ℓ : ℝ) - c) / (ℓ : ℝ)) atTop (nhds 1) := by
  have hinv : Tendsto (fun ℓ : ℕ => c / (ℓ : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsub : Tendsto (fun ℓ : ℕ => (1 : ℝ) - c / (ℓ : ℝ)) atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with ℓ hℓ
  have hℓ0 : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hℓ0]

private theorem fj_eventually_bounds {δ ε : ℝ} (hδ : 0 < δ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 4) :
    ∀ᶠ ℓ : ℕ in atTop,
      4 ≤ Real.log (ℓ : ℝ) ∧
      ((ℓ : ℝ) ^ (-(ε / 2))) ≤
        (√(2 * (1 - ε) * Real.log (ℓ : ℝ)) / (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1)) *
          (√(2 * π))⁻¹ ∧
      (ℓ : ℝ) ^ (ε / 3) ≤ ((ℓ : ℝ) - 2) * (ℓ : ℝ) ^ (-(1 - ε / 2)) ∧
      (ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3))) < δ / 8 ∧
      (ℓ : ℝ) ^ (-(2 * ε)) < δ / 8 ∧
      1 / √(2 * (1 - ε) * Real.log (ℓ : ℝ)) < δ / 8 ∧
      (ℓ : ℝ) / ((ℓ : ℝ) - 1) ≤ 1 + δ / 8 ∧
      4 ≤ ℓ := by
  have h1mε : 0 < 1 - ε := by linarith
  have hlog_top : Tendsto (fun ℓ : ℕ => Real.log (ℓ : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow_2eps : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ (-(2 * ε))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * ε)).comp tendsto_natCast_atTop_atTop
  have hexp_tail :
      Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) atTop (nhds 0) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (9 / ε)
    have hn_eps : (3 : ℝ) ≤ (ε / 3) * (n : ℝ) := by
      have := (div_lt_iff₀ hε_pos).mp hn; linarith
    refine squeeze_zero_norm' ?_ (by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
        tendsto_natCast_atTop_atTop).const_mul (n.factorial : ℝ))
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with ℓ hℓ
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
    have hℓ_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ht_pos : 0 < (ℓ : ℝ) ^ (ε / 3) := Real.rpow_pos_of_pos hℓ_pos _
    have hexp_le :
        Real.exp (-((ℓ : ℝ) ^ (ε / 3))) ≤ (n.factorial : ℝ) / ((ℓ : ℝ) ^ (ε / 3)) ^ n := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (pow_pos ht_pos n),
        one_mul]
      have hfac := Real.pow_div_factorial_le_exp ((ℓ : ℝ) ^ (ε / 3)) ht_pos.le n
      have hfn : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
      linarith [(div_le_iff₀ hfn).mp hfac]
    have hpow_ge : (ℓ : ℝ) ^ (3 : ℝ) ≤ ((ℓ : ℝ) ^ (ε / 3)) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ_pos.le]
      exact Real.rpow_le_rpow_of_exponent_le hℓ_ge1 hn_eps
    have h3 : (ℓ : ℝ) ^ (3 : ℝ) = (ℓ : ℝ) ^ 2 * (ℓ : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hinv : (ℓ : ℝ) ^ (-1 : ℝ) = 1 / (ℓ : ℝ) := by rw [Real.rpow_neg_one, one_div]
    calc (ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))
        ≤ (ℓ : ℝ) ^ 2 * ((n.factorial : ℝ) / ((ℓ : ℝ) ^ (ε / 3)) ^ n) :=
          mul_le_mul_of_nonneg_left hexp_le (sq_nonneg _)
      _ ≤ (ℓ : ℝ) ^ 2 * ((n.factorial : ℝ) / (ℓ : ℝ) ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
            (by positivity) hpow_ge) (sq_nonneg _)
      _ = (n.factorial : ℝ) * (ℓ : ℝ) ^ (-1 : ℝ) := by
          rw [h3, hinv]; field_simp [hℓ_pos.ne']
  have hev_log : ∀ᶠ ℓ : ℕ in atTop, 4 ≤ Real.log (ℓ : ℝ) :=
    hlog_top.eventually (Filter.eventually_ge_atTop 4)
  have hev_u1_small : ∀ᶠ ℓ : ℕ in atTop,
      ((ℓ : ℝ) ^ (-(ε / 2))) ≤
        (√(2 * (1 - ε) * Real.log (ℓ : ℝ)) / (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1)) *
          (√(2 * π))⁻¹ := by
    have hlo_ratio : Tendsto (fun ℓ : ℕ =>
        (ℓ : ℝ) ^ (-(ε / 2)) * (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1) /
          √(2 * (1 - ε) * Real.log (ℓ : ℝ))) atTop (nhds 0) := by
      have hlog_o := isLittleO_log_rpow_atTop (by linarith : 0 < ε / 4)
      have hlog_ev : ∀ᶠ ℓ : ℕ in atTop, Real.log (ℓ : ℝ) ≤ (ℓ : ℝ) ^ (ε / 4) := by
        filter_upwards [(hlog_o.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
          (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop (2 : ℕ)] with ℓ hℓ h2
        have hpos : 0 < (ℓ : ℝ) ^ (ε / 4) :=
          Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < ℓ)) _
        exact ((div_lt_one hpos).mp hℓ).le
      refine squeeze_zero_norm' ?_ (by
        simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < ε / 4)).comp
          tendsto_natCast_atTop_atTop).const_mul (3 : ℝ))
      filter_upwards [hev_log, hlog_ev, eventually_ge_atTop (2 : ℕ)] with ℓ hlog hle h2
      have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
      have hden_pos : 0 < 2 * (1 - ε) * Real.log (ℓ : ℝ) + 1 := by nlinarith
      have hsqrt_ge1 : (1 : ℝ) ≤ √(2 * (1 - ε) * Real.log (ℓ : ℝ)) := by
        rw [Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (ℓ : ℝ) ^ (-(ε / 2)) * (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1) /
              √(2 * (1 - ε) * Real.log (ℓ : ℝ))
          ≤ (ℓ : ℝ) ^ (-(ε / 2)) * (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1) / 1 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hsqrt_ge1
        _ ≤ (ℓ : ℝ) ^ (-(ε / 2)) * (3 * (ℓ : ℝ) ^ (ε / 4)) := by
            rw [div_one]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h1_le : (1 : ℝ) ≤ (ℓ : ℝ) ^ (ε / 4) :=
              Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ ℓ)) (by linarith)
            nlinarith
        _ = 3 * (ℓ : ℝ) ^ (-(ε / 4)) := by
            rw [mul_left_comm, ← Real.rpow_add hℓ_pos]; congr 2; ring
    filter_upwards [hlo_ratio.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (√(2 * π))⁻¹)),
      hev_log] with ℓ hlt hlog
    have hsqrt_pos : 0 < √(2 * (1 - ε) * Real.log (ℓ : ℝ)) := Real.sqrt_pos.mpr (by nlinarith)
    have hden_pos : 0 < 2 * (1 - ε) * Real.log (ℓ : ℝ) + 1 := by nlinarith
    have h1 := (div_lt_iff₀ hsqrt_pos).mp hlt
    calc (ℓ : ℝ) ^ (-(ε / 2))
        ≤ √(2 * (1 - ε) * Real.log (ℓ : ℝ)) * (√(2 * π))⁻¹ /
            (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1) := by
          rw [le_div_iff₀ hden_pos]; linarith
      _ = √(2 * (1 - ε) * Real.log (ℓ : ℝ)) / (2 * (1 - ε) * Real.log (ℓ : ℝ) + 1) *
            (√(2 * π))⁻¹ := by ring
  have hev_exp_cond : ∀ᶠ ℓ : ℕ in atTop,
      (ℓ : ℝ) ^ (ε / 3) ≤ ((ℓ : ℝ) - 2) * (ℓ : ℝ) ^ (-(1 - ε / 2)) := by
    filter_upwards [(tendsto_nat_sub_div_self 2).eventually
        (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      ((tendsto_rpow_atTop (by linarith : 0 < ε / 6)).comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop (2 : ℝ)),
      eventually_ge_atTop (3 : ℕ)] with ℓ hhalf hpow h3
    dsimp only [Function.comp_apply] at hpow
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
    have h1 : (ℓ : ℝ) / 2 ≤ (ℓ : ℝ) - 2 := by
      have := (lt_div_iff₀ hℓ_pos).mp hhalf; linarith
    have h3' : ((ℓ : ℝ) / 2) * (ℓ : ℝ) ^ (-(1 - ε / 2)) =
        ((ℓ : ℝ) ^ (ε / 6) / 2) * (ℓ : ℝ) ^ (ε / 3) := by
      have hsplit : (ℓ : ℝ) * (ℓ : ℝ) ^ (-(1 - ε / 2)) = (ℓ : ℝ) ^ (ε / 2) := by
        rw [← Real.rpow_one_add' hℓ_pos.le (by linarith : (1 : ℝ) + -(1 - ε / 2) ≠ 0)]
        congr 1; ring
      have hsplit2 : (ℓ : ℝ) ^ (ε / 2) = (ℓ : ℝ) ^ (ε / 6) * (ℓ : ℝ) ^ (ε / 3) := by
        rw [← Real.rpow_add hℓ_pos]; congr 1; ring
      linarith
    have h4 : (ℓ : ℝ) ^ (ε / 3) ≤ ((ℓ : ℝ) / 2) * (ℓ : ℝ) ^ (-(1 - ε / 2)) := by
      rw [h3']; nlinarith [Real.rpow_pos_of_pos hℓ_pos (ε / 3)]
    have h5 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hℓ_pos.le (-(1 - ε / 2)))
    linarith
  have hev_err1 : ∀ᶠ ℓ : ℕ in atTop,
      (ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3))) < δ / 8 :=
    hexp_tail.eventually (gt_mem_nhds (by positivity))
  have hev_err2 : ∀ᶠ ℓ : ℕ in atTop, (ℓ : ℝ) ^ (-(2 * ε)) < δ / 8 :=
    hpow_2eps.eventually (gt_mem_nhds (by positivity))
  have hev_err3a : ∀ᶠ ℓ : ℕ in atTop, 1 / √(2 * (1 - ε) * Real.log (ℓ : ℝ)) < δ / 8 :=
    (tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (hlog_top.const_mul_atTop (by linarith)))).eventually
      (gt_mem_nhds (by positivity))
  have hev_err3b : ∀ᶠ ℓ : ℕ in atTop, (ℓ : ℝ) / ((ℓ : ℝ) - 1) ≤ 1 + δ / 8 := by
    have hinv : Tendsto (fun ℓ : ℕ => 1 / ((ℓ : ℝ) - 1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hadd : Tendsto (fun ℓ : ℕ => (1 : ℝ) + 1 / ((ℓ : ℝ) - 1)) atTop (nhds 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hinv
    have h2 : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) / ((ℓ : ℝ) - 1)) atTop (nhds 1) := by
      refine hadd.congr' ?_
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with ℓ hℓ
      have hℓm1 : (ℓ : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
        linarith
      field_simp [hℓm1]; ring
    exact h2.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hev_log, hev_u1_small, hev_exp_cond, hev_err1, hev_err2, hev_err3a, hev_err3b,
    eventually_ge_atTop (4 : ℕ)] with ℓ h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

private theorem fj_firstIntegral_upper {ℓ : ℕ} {δ ε u₁ u₂ S : ℝ}
    (hℓ_pos : (0 : ℝ) < (ℓ : ℝ)) (hℓm1_pos : (0 : ℝ) < (ℓ : ℝ) - 1)
    (hS_pos : 0 < S) (hS_ge1 : 1 ≤ S) (hu1_pos : 0 < u₁)
    (hu2_eq : u₂ = √(1 + ε) * S) (hsqrt_hi : √(1 + ε) < 1 + δ / 4)
    (herr1 : (ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3))) < δ / 8)
    (herr2 : (ℓ : ℝ) ^ (-(2 * ε)) < δ / 8)
    (herr3a : 1 / u₁ < δ / 8) (herr3b : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ≤ 1 + δ / 8)
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1)
    (hI_le : friezeJerrumFirstIntegral ℓ ≤
      Real.exp (-((ℓ : ℝ) ^ (ε / 3))) + (u₂ + 1 / u₁) * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) +
        (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2)) :
    (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / S < 1 + δ := by
  have hmul : (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / S ≤
      ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / S +
      ((u₂ + 1 / u₁) / S) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1)) +
      ((ℓ : ℝ) ^ (-(2 * ε))) / S := by
    have hrew : (ℓ : ℝ) ^ 2 * (Real.exp (-((ℓ : ℝ) ^ (ε / 3))) +
        (u₂ + 1 / u₁) * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) +
        (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2)) / S =
        ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / S +
        ((u₂ + 1 / u₁) / S) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1)) +
        ((ℓ : ℝ) ^ (-(2 * ε))) / S := by
      field_simp [hℓ_pos.ne', hℓm1_pos.ne', hS_pos.ne']
    rw [← hrew]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hI_le (sq_nonneg _)) hS_pos.le
  have ht1 : ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / S < δ / 8 :=
    (div_le_self (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hS_ge1).trans_lt herr1
  have ht3 : ((ℓ : ℝ) ^ (-(2 * ε))) / S < δ / 8 :=
    (div_le_self (Real.rpow_nonneg hℓ_pos.le _) hS_ge1).trans_lt herr2
  have hmid_eq : (u₂ + 1 / u₁) / S = √(1 + ε) + (1 / u₁) / S := by
    rw [add_div, hu2_eq, mul_div_cancel_right₀ _ hS_pos.ne']
  have hinv_u1 : (1 / u₁) / S < δ / 8 :=
    (div_le_self (one_div_nonneg.mpr hu1_pos.le) hS_ge1).trans_lt herr3a
  have hmid_val : ((u₂ + 1 / u₁) / S) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1)) < 1 + 3 * δ / 4 := by
    rw [hmid_eq]
    have hmid_le : (√(1 + ε) + (1 / u₁) / S) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1)) ≤
        (1 + 3 * δ / 8) * (1 + δ / 8) :=
      mul_le_mul (by linarith) herr3b (div_nonneg hℓ_pos.le hℓm1_pos.le) (by linarith)
    nlinarith
  linarith

private theorem fj_firstIntegral_lower {ℓ : ℕ} {δ ε u₁ S : ℝ}
    (hℓ_pos : (0 : ℝ) < (ℓ : ℝ)) (hℓm1_pos : (0 : ℝ) < (ℓ : ℝ) - 1)
    (hℓm1_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) - 1)
    (hS_pos : 0 < S)
    (hu1_eq : u₁ = √(1 - ε) * S) (hsqrt_lo : 1 - δ / 4 < √(1 - ε))
    (herr1 : (ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3))) < δ / 8)
    (herr2 : (ℓ : ℝ) ^ (-(2 * ε)) < δ / 8)
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1)
    (hI_ge : u₁ * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) - (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2) -
        Real.exp (-((ℓ : ℝ) ^ (ε / 3))) / ((ℓ : ℝ) - 1)) ≤ friezeJerrumFirstIntegral ℓ) :
    1 - δ < (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / S := by
  have hmul : √(1 - ε) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) - (ℓ : ℝ) ^ (-(2 * ε)) -
      ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / ((ℓ : ℝ) - 1)) ≤
      (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / S := by
    have hrew : (ℓ : ℝ) ^ 2 * (u₁ * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) -
        (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2) -
        Real.exp (-((ℓ : ℝ) ^ (ε / 3))) / ((ℓ : ℝ) - 1))) / S =
        √(1 - ε) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) - (ℓ : ℝ) ^ (-(2 * ε)) -
        ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / ((ℓ : ℝ) - 1)) := by
      rw [hu1_eq]; field_simp [hℓ_pos.ne', hℓm1_pos.ne', hS_pos.ne']
    rw [← hrew]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hI_ge (sq_nonneg _)) hS_pos.le
  have hℓ_ratio : (1 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [one_le_div hℓm1_pos]; linarith
  have htail1 : ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / ((ℓ : ℝ) - 1) < δ / 8 :=
    (div_le_self (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hℓm1_ge1).trans_lt herr1
  have hbr : 1 - δ / 4 < (ℓ : ℝ) / ((ℓ : ℝ) - 1) - (ℓ : ℝ) ^ (-(2 * ε)) -
      ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / ((ℓ : ℝ) - 1) := by linarith
  have hprod_gt : (1 - δ / 4) * (1 - δ / 4) <
      √(1 - ε) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) - (ℓ : ℝ) ^ (-(2 * ε)) -
        ((ℓ : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) ^ (ε / 3)))) / ((ℓ : ℝ) - 1)) :=
    mul_lt_mul'' hsqrt_lo hbr (by linarith) (by linarith)
  nlinarith

/-- Sharp asymptotic: `ℓ² * I_ℓ / √(2 ln ℓ) → 1` as `ℓ → ∞`. -/
theorem tendsto_friezeJerrumFirstIntegral :
    Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / √(2 * Real.log (ℓ : ℝ)))
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro δ₀ hδ₀
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδ_le1 : δ ≤ 1 := min_le_right _ _
  have hδ_le0 : δ ≤ δ₀ := min_le_left _ _
  let ε : ℝ := min (1 / 4) (δ / 8)
  have hε_pos : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε_le : ε ≤ 1 / 4 := min_le_left _ _
  have hε_δ : ε ≤ δ / 8 := min_le_right _ _
  have hsqrt_hi : √(1 + ε) < 1 + δ / 4 :=
    (Real.sqrt_lt' (by linarith)).mpr (by nlinarith)
  have hsqrt_lo : 1 - δ / 4 < √(1 - ε) :=
    (Real.lt_sqrt (by linarith)).mpr (by nlinarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (fj_eventually_bounds hδ hε_pos hε_le)
  refine ⟨N, fun ℓ hℓN => ?_⟩
  obtain ⟨hlog4, hu1_small, hexp_cond, herr1, herr2, herr3a, herr3b, hℓ4⟩ := hN ℓ hℓN
  have hℓ2 : 2 ≤ ℓ := by omega
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓm1_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ4
    linarith
  have hℓm1_pos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  set L : ℝ := Real.log (ℓ : ℝ)
  set S : ℝ := √(2 * L)
  have hS_pos : 0 < S := Real.sqrt_pos.mpr (by linarith)
  have hS_ge1 : 1 ≤ S := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  set u₁ : ℝ := √(2 * (1 - ε) * L)
  set u₂ : ℝ := √(2 * (1 + ε) * L)
  have hu1_pos : 0 < u₁ := Real.sqrt_pos.mpr (by nlinarith)
  have hu2_ge1 : 1 ≤ u₂ := by rw [Real.le_sqrt (by norm_num) (by nlinarith)]; nlinarith
  have hu1_le_u2 : u₁ ≤ u₂ := Real.sqrt_le_sqrt (by nlinarith)
  have hu1_sq : u₁ ^ 2 = 2 * (1 - ε) * L := Real.sq_sqrt (by nlinarith)
  have hu2_sq : u₂ ^ 2 = 2 * (1 + ε) * L := Real.sq_sqrt (by nlinarith)
  have hu1_eq : u₁ = √(1 - ε) * S := by
    dsimp only [u₁, S]
    rw [show 2 * (1 - ε) * L = (1 - ε) * (2 * L) by ring, Real.sqrt_mul (by linarith)]
  have hu2_eq : u₂ = √(1 + ε) * S := by
    dsimp only [u₂, S]
    rw [show 2 * (1 + ε) * L = (1 + ε) * (2 * L) by ring, Real.sqrt_mul (by linarith)]
  have hφ_u1 : gaussianPDFReal 0 1 u₁ = (√(2 * π))⁻¹ * (ℓ : ℝ) ^ (-(1 - ε)) := by
    rw [gaussianPDFReal_def]; dsimp only
    rw [sub_zero, NNReal.coe_one, mul_one, mul_one,
      show -u₁ ^ 2 / 2 = -(1 - ε) * L by rw [hu1_sq]; ring,
      Real.rpow_def_of_pos hℓ_pos, mul_comm (-(1 - ε)) L]
  have hφ_u2_sq : gaussianPDFReal 0 1 u₂ ^ 2 ≤ (ℓ : ℝ) ^ (-(2 * ε)) / (ℓ : ℝ) ^ 2 := by
    have hφ_u2 : gaussianPDFReal 0 1 u₂ = (√(2 * π))⁻¹ * (ℓ : ℝ) ^ (-(1 + ε)) := by
      rw [gaussianPDFReal_def]; dsimp only
      rw [sub_zero, NNReal.coe_one, mul_one, mul_one,
        show -u₂ ^ 2 / 2 = -(1 + ε) * L by rw [hu2_sq]; ring,
        Real.rpow_def_of_pos hℓ_pos, mul_comm (-(1 + ε)) L]
    rw [hφ_u2, mul_pow]
    have hinv1 : ((√(2 * π))⁻¹) ^ 2 ≤ 1 := by
      have := fj_inv_sqrt_two_pi_le_one
      nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg (2 * π))]
    have hpow_eq : ((ℓ : ℝ) ^ (-(1 + ε))) ^ 2 = (ℓ : ℝ) ^ (-(2 * ε)) / (ℓ : ℝ) ^ 2 := by
      have hneg2 : (ℓ : ℝ) ^ (-2 : ℝ) = ((ℓ : ℝ) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hℓ_pos.le, Real.rpow_two]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ_pos.le,
        show (-(1 + ε)) * (2 : ℕ) = -(2 * ε) + (-2 : ℝ) by push_cast; ring,
        Real.rpow_add hℓ_pos, hneg2, div_eq_mul_inv]
    rw [hpow_eq]
    exact mul_le_of_le_one_left
      (div_nonneg (Real.rpow_nonneg hℓ_pos.le _) (sq_nonneg _)) hinv1
  have hΦ_u1_pow : cdf (gaussianReal 0 1) u₁ ^ (ℓ - 2) ≤ Real.exp (-((ℓ : ℝ) ^ (ε / 3))) := by
    have htail_ge : (ℓ : ℝ) ^ (-(1 - ε / 2)) ≤ cdf (gaussianReal 0 1) (-u₁) := by
      have hm := CslibFrontier.Foundations.Probability.Gaussian.millsRatio_lower u₁
      have h1 : (ℓ : ℝ) ^ (-(ε / 2)) * (ℓ : ℝ) ^ (-(1 - ε)) = (ℓ : ℝ) ^ (-(1 - ε / 2)) := by
        rw [← Real.rpow_add hℓ_pos]; congr 1; ring
      calc (ℓ : ℝ) ^ (-(1 - ε / 2))
          = (ℓ : ℝ) ^ (-(ε / 2)) * (ℓ : ℝ) ^ (-(1 - ε)) := h1.symm
        _ ≤ (u₁ / (u₁ ^ 2 + 1) * (√(2 * π))⁻¹) * (ℓ : ℝ) ^ (-(1 - ε)) :=
            mul_le_mul_of_nonneg_right (by simpa [u₁, hu1_sq] using hu1_small)
              (Real.rpow_nonneg hℓ_pos.le _)
        _ = u₁ / (u₁ ^ 2 + 1) * gaussianPDFReal 0 1 u₁ := by rw [hφ_u1]; ring
        _ ≤ cdf (gaussianReal 0 1) (-u₁) := hm
    have hΦ_le : cdf (gaussianReal 0 1) u₁ ≤ 1 - (ℓ : ℝ) ^ (-(1 - ε / 2)) := by
      have hneg := cdf_gaussianReal_neg (v := 1) one_ne_zero u₁; linarith
    have hΦ_le_exp : cdf (gaussianReal 0 1) u₁ ≤ Real.exp (-((ℓ : ℝ) ^ (-(1 - ε / 2)))) :=
      hΦ_le.trans (by linarith [Real.add_one_le_exp (-((ℓ : ℝ) ^ (-(1 - ε / 2))))])
    calc cdf (gaussianReal 0 1) u₁ ^ (ℓ - 2)
        ≤ (Real.exp (-((ℓ : ℝ) ^ (-(1 - ε / 2))))) ^ (ℓ - 2) :=
          pow_le_pow_left₀ (cdf_nonneg _ _) hΦ_le_exp _
      _ = Real.exp (-(((ℓ - 2 : ℕ) : ℝ) * (ℓ : ℝ) ^ (-(1 - ε / 2)))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-((ℓ : ℝ) ^ (ε / 3))) := by
          rw [Real.exp_le_exp, neg_le_neg_iff, Nat.cast_sub (by omega : 2 ≤ ℓ), Nat.cast_ofNat]
          exact hexp_cond
  let g : ℝ → ℝ := fun u => gaussianPDFReal 0 1 u ^ 2 * cdf (gaussianReal 0 1) u ^ (ℓ - 2)
  have hg_int : Integrable g := integrable_gaussianPDFReal_sq_mul_cdf_pow (ℓ - 2)
  have hsplit : friezeJerrumFirstIntegral ℓ =
      (∫ u in Iic u₁, g u) + (∫ u in Ioc u₁ u₂, g u) + (∫ u in Ioi u₂, g u) := by
    unfold friezeJerrumFirstIntegral
    have h12 : (∫ u in Iic u₁, g u) + (∫ u in Ioc u₁ u₂, g u) = ∫ u in Iic u₂, g u := by
      rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        hg_int.integrableOn hg_int.integrableOn, Iic_union_Ioc_eq_Iic hu1_le_u2]
    rw [h12, ← setIntegral_union (disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2)
      measurableSet_Ioi hg_int.integrableOn hg_int.integrableOn, Iic_union_Ioi,
      Measure.restrict_univ]
  have htail_left : ∫ u in Iic u₁, g u ≤ Real.exp (-((ℓ : ℝ) ^ (ε / 3))) :=
    fj_left_tail_le hΦ_u1_pow
  have htail_right : ∫ u in Ioi u₂, g u ≤ (ℓ : ℝ) ^ (-(2 * ε)) / (ℓ : ℝ) ^ 2 :=
    (fj_right_tail_le hu2_ge1).trans hφ_u2_sq
  obtain ⟨hmid_lo, hmid_hi⟩ := fj_mid_bounds hℓ2 hu1_pos hu1_le_u2
  let G : ℝ → ℝ := fun t =>
    cdf (gaussianReal 0 1) t ^ (ℓ - 1) / ((ℓ : ℝ) - 1) - cdf (gaussianReal 0 1) t ^ ℓ / (ℓ : ℝ)
  have hGu1 : G u₁ ≤ Real.exp (-((ℓ : ℝ) ^ (ε / 3))) / ((ℓ : ℝ) - 1) := by
    have h1 : G u₁ ≤ cdf (gaussianReal 0 1) u₁ ^ (ℓ - 1) / ((ℓ : ℝ) - 1) := by
      dsimp only [G]
      linarith [div_nonneg (pow_nonneg (cdf_nonneg (gaussianReal 0 1) u₁) ℓ) hℓ_pos.le]
    have h2 : cdf (gaussianReal 0 1) u₁ ^ (ℓ - 1) ≤ cdf (gaussianReal 0 1) u₁ ^ (ℓ - 2) := by
      rw [show ℓ - 1 = (ℓ - 2) + 1 by omega, pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg (cdf_nonneg _ _) _) (cdf_le_one _ _)
    exact h1.trans (div_le_div_of_nonneg_right (h2.trans hΦ_u1_pow) hℓm1_pos.le)
  have hGu2_tail :
      1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) - G u₂ ≤ (ℓ : ℝ) ^ (-(2 * ε)) / (ℓ : ℝ) ^ 2 :=
    (fj_antideriv_right_tail hℓ2 hu2_ge1).trans hφ_u2_sq
  have hI_le : friezeJerrumFirstIntegral ℓ ≤
      Real.exp (-((ℓ : ℝ) ^ (ε / 3))) + (u₂ + 1 / u₁) * (1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) +
        (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2) := by
    rw [hsplit]
    exact add_le_add (add_le_add htail_left hmid_hi) htail_right
  have hupper : (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / S < 1 + δ :=
    fj_firstIntegral_upper hℓ_pos hℓm1_pos hS_pos hS_ge1 hu1_pos hu2_eq hsqrt_hi herr1 herr2
      herr3a herr3b hδ hδ_le1 hI_le
  have hI_ge_G : u₁ * (G u₂ - G u₁) ≤ friezeJerrumFirstIntegral ℓ := by
    have h1 : 0 ≤ ∫ u in Iic u₁, g u :=
      setIntegral_nonneg measurableSet_Iic fun u _ =>
        mul_nonneg (sq_nonneg _) (pow_nonneg (cdf_nonneg _ _) _)
    have h2 : 0 ≤ ∫ u in Ioi u₂, g u :=
      setIntegral_nonneg measurableSet_Ioi fun u _ =>
        mul_nonneg (sq_nonneg _) (pow_nonneg (cdf_nonneg _ _) _)
    have h3 : (∫ u in Ioc u₁ u₂, g u) ≤ friezeJerrumFirstIntegral ℓ := by
      rw [hsplit]
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le h1 le_rfl) h2
    exact hmid_lo.trans h3
  have hG_ge : 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) - (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2) -
      Real.exp (-((ℓ : ℝ) ^ (ε / 3))) / ((ℓ : ℝ) - 1) ≤ G u₂ - G u₁ := by
    have h1 : 1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) - (ℓ : ℝ) ^ (-(2 * ε)) / ((ℓ : ℝ) ^ 2) ≤ G u₂ :=
      sub_le_comm.mp hGu2_tail
    exact sub_le_sub h1 hGu1
  have hlower : 1 - δ < (ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / S :=
    fj_firstIntegral_lower hℓ_pos hℓm1_pos hℓm1_ge1 hS_pos hu1_eq hsqrt_lo herr1 herr2
      hδ hδ_le1 ((mul_le_mul_of_nonneg_left hG_ge hu1_pos.le).trans hI_ge_G)
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Sharp asymptotic for `c_1(ℓ)`: `c_1(ℓ) / (2 ln ℓ / ℓ) → 1` as `ℓ → ∞`. -/
theorem tendsto_friezeJerrumTaylorCoeff_one :
    Tendsto (fun ℓ : ℕ => friezeJerrumTaylorCoeff ℓ 1 / (2 * Real.log (ℓ : ℝ) / (ℓ : ℝ)))
      atTop (nhds 1) := by
  have hsq : Tendsto (fun ℓ : ℕ =>
      ((ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / √(2 * Real.log (ℓ : ℝ))) ^ 2)
      atTop (nhds 1) := by simpa using tendsto_friezeJerrumFirstIntegral.pow 2
  have hprod : Tendsto (fun ℓ : ℕ =>
      ((ℓ : ℝ) ^ 2 * friezeJerrumFirstIntegral ℓ / √(2 * Real.log (ℓ : ℝ))) ^ 2 *
        (((ℓ : ℝ) - 1) / (ℓ : ℝ))) atTop (nhds 1) := by
    simpa using hsq.mul (tendsto_nat_sub_div_self 1)
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with ℓ hℓ
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hlog_pos : 0 < Real.log (ℓ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ℓ))
  rw [friezeJerrumTaylorCoeff_one_eq (by omega : 2 ≤ ℓ), div_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (ℓ : ℝ))]
  field_simp [hℓ_pos.ne', hlog_pos.ne']

/-- Equivalent asymptotic `c_1(ℓ) / (2 ln ℓ / (ℓ - 1)) → 1` as `ℓ → ∞`. -/
theorem tendsto_friezeJerrumTaylorCoeff_one_div_pred :
    Tendsto (fun ℓ : ℕ => friezeJerrumTaylorCoeff ℓ 1 / (2 * Real.log (ℓ : ℝ) / ((ℓ : ℝ) - 1)))
      atTop (nhds 1) := by
  have hmul : Tendsto (fun ℓ : ℕ =>
      (friezeJerrumTaylorCoeff ℓ 1 / (2 * Real.log (ℓ : ℝ) / (ℓ : ℝ))) *
        (((ℓ : ℝ) - 1) / (ℓ : ℝ))) atTop (nhds 1) := by
    simpa using tendsto_friezeJerrumTaylorCoeff_one.mul (tendsto_nat_sub_div_self 1)
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with ℓ hℓ
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓm1_pos : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    linarith
  have hlog_pos : 0 < Real.log (ℓ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ℓ))
  field_simp [hℓ_pos.ne', hℓm1_pos.ne', hlog_pos.ne']

end CslibFrontier.Algorithms.Semidefinite
