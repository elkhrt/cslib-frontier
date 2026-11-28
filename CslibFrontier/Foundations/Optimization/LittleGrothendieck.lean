module

public import Mathlib.Probability.ProductMeasure
public import CslibFrontier.Foundations.Optimization.GrothendieckInequality

import CslibFrontier.Foundations.Probability.Gaussian.Moments
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Independence.Integration

/-!
# The Little Grothendieck Constant

This module proves Grothendieck's exact evaluation of the little Grothendieck constant
$k_G = \frac{\pi}{2}$ over finite symmetric positive semidefinite real matrices under standard
Lean axioms, and deduces the lower bound $\frac{\pi}{2} \le K_G$ on the real Grothendieck constant.

## Main definitions

* `CslibFrontier.Grothendieck.littleGrothendieckConstant`: the little Grothendieck constant
  $k_G = \sup_{n \in \mathbb{N}} \sup_{A \in \mathbb{R}^{n \times n},\, A \succeq 0}
  \frac{\mathrm{SDP}(A)}{\mathrm{OPT}(A)}$.

## Main results

* `CslibFrontier.Grothendieck.sdpNorm_le_pi_div_two_mul_optNorm_of_posSemidef` and
  `CslibFrontier.Grothendieck.littleGrothendieckConstant_le_pi_div_two`: for every symmetric
  positive
  semidefinite matrix `A`, $\mathrm{SDP}(A) \le \frac{\pi}{2} \mathrm{OPT}(A)$, so
  $k_G \le \frac{\pi}{2}$.
* `CslibFrontier.Grothendieck.integral_gaussianReal_abs` and
  `CslibFrontier.Grothendieck.integral_pi_gaussianReal_abs_dotProduct`:
  $\mathbb{E}_{Z \sim \mathcal{N}(0, I_n)} |\langle u, Z \rangle| = \sqrt{2 / \pi}$ for every unit
  vector $u \in \mathbb{R}^n$.
* `CslibFrontier.Grothendieck.exists_gaussian_partition_unitVectors`: finite measurable
  cube-partition
  approximation of $z \mapsto z / \|z\|$ on $(\mathbb{R}^n, \gamma_n)$.
* `CslibFrontier.Grothendieck.pi_div_two_le_littleGrothendieckConstant`,
  `CslibFrontier.Grothendieck.littleGrothendieckConstant_eq_pi_div_two`, and
  `CslibFrontier.Grothendieck.pi_div_two_le_grothendieckConstant`: $k_G = \frac{\pi}{2} \le K_G$.
-/

public section

open scoped BigOperators ENNReal InnerProductSpace NNReal Real Topology
open MeasureTheory ProbabilityTheory

namespace CslibFrontier.Grothendieck

/-! ### Definition and Upper Bound $k_G \le \frac{\pi}{2}$ -/

private def littleGrothendieckRatioSet : Set ℝ :=
  {r : ℝ | ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosSemidef ∧ r = sdpNorm A / optNorm A}

private theorem littleGrothendieckRatioSet_nonempty : littleGrothendieckRatioSet.Nonempty := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := 1
  exact ⟨sdpNorm A / optNorm A, 1, A, Matrix.PosSemidef.one, rfl⟩

private theorem littleGrothendieckRatioSet_bddAbove : BddAbove littleGrothendieckRatioSet := by
  refine ⟨grothendieckConstant, ?_⟩
  rintro r ⟨n, A, _, rfl⟩
  exact div_le_grothendieckConstant A

/-- The little Grothendieck constant
$k_G = \sup_{n \in \mathbb{N}} \sup_{A \in \mathbb{R}^{n \times n},\, A \succeq 0}
\frac{\mathrm{SDP}(A)}{\mathrm{OPT}(A)}$. -/
noncomputable def littleGrothendieckConstant : ℝ :=
  sSup littleGrothendieckRatioSet

/-- $k_G \le K_G$. -/
theorem littleGrothendieckConstant_le_grothendieckConstant :
    littleGrothendieckConstant ≤ grothendieckConstant := by
  refine csSup_le littleGrothendieckRatioSet_nonempty ?_
  rintro r ⟨n, A, _, rfl⟩
  exact div_le_grothendieckConstant A

private theorem sum_posSemidef_inner_nonneg {μ ι : Type*} [Fintype μ] [Fintype ι]
    {A : Matrix μ μ ℝ} (hA : A.PosSemidef) (v : μ → EuclideanSpace ℝ ι) :
    0 ≤ ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ := by
  have hrew : (∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ) =
      ∑ r : ι, star (fun i ↦ v i r) ⬝ᵥ A.mulVec (fun j ↦ v j r) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, star_trivial,
      dotProduct, Matrix.mulVec]
    calc
      (∑ i : μ, ∑ j : μ, A i j * ∑ r : ι, v j r * v i r)
          = ∑ i : μ, ∑ r : ι, ∑ j : μ, A i j * (v j r * v i r) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have h1 : ∀ j : μ, A i j * ∑ r : ι, v j r * v i r =
                ∑ r : ι, A i j * (v j r * v i r) := fun j ↦ Finset.mul_sum _ _ _
            simp_rw [h1]
            exact Finset.sum_comm
      _ = ∑ r : ι, ∑ i : μ, ∑ j : μ, A i j * (v j r * v i r) := Finset.sum_comm
      _ = ∑ r : ι, ∑ i : μ, v i r * ∑ j : μ, A i j * v j r := by
            refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hrew]
  exact Finset.sum_nonneg fun r _ ↦ hA.dotProduct_mulVec_nonneg (fun i ↦ v i r)

/-- Little Grothendieck inequality (upper bound): for every symmetric positive semidefinite
matrix `A`, $\mathrm{SDP}(A) \le \frac{\pi}{2} \mathrm{OPT}(A)$. -/
theorem sdpNorm_le_pi_div_two_mul_optNorm_of_posSemidef {μ : Type*} [Fintype μ]
    {A : Matrix μ μ ℝ} (hA : A.PosSemidef) :
    sdpNorm A ≤ (Real.pi / 2) * optNorm A := by
  classical
  rw [sdpNorm_le_iff]
  intro u w hu hw
  have hsymm : 2 * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ ≤
      (∑ i, ∑ j, A i j * ⟪u i, u j⟫_ℝ) + (∑ i, ∑ j, A i j * ⟪w i, w j⟫_ℝ) := by
    have hdiff := sum_posSemidef_inner_nonneg hA (fun i ↦ u i - w i)
    have hexp : (∑ i, ∑ j, A i j * ⟪u i - w i, u j - w j⟫_ℝ) =
        (∑ i, ∑ j, A i j * ⟪u i, u j⟫_ℝ) + (∑ i, ∑ j, A i j * ⟪w i, w j⟫_ℝ) -
          2 * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ := by
      have hji : (∑ i, ∑ j, A i j * ⟪w i, u j⟫_ℝ) = ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        have hAij : A j i = A i j := by
          have := congrFun (congrFun hA.isHermitian j) i
          simpa [Matrix.conjTranspose_apply] using this.symm
        rw [hAij, real_inner_comm]
      calc
        (∑ i, ∑ j, A i j * ⟪u i - w i, u j - w j⟫_ℝ)
            = (∑ i, ∑ j, A i j * ⟪u i, u j⟫_ℝ) - (∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ) -
                (∑ i, ∑ j, A i j * ⟪w i, u j⟫_ℝ) + (∑ i, ∑ j, A i j * ⟪w i, w j⟫_ℝ) := by
              simp only [inner_sub_left, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
              ring
        _ = (∑ i, ∑ j, A i j * ⟪u i, u j⟫_ℝ) + (∑ i, ∑ j, A i j * ⟪w i, w j⟫_ℝ) -
              2 * ∑ i, ∑ j, A i j * ⟪u i, w j⟫_ℝ := by
              rw [hji]
              ring
    linarith
  have hdiag : ∀ (v : μ → EuclideanSpace ℝ (μ ⊕ μ)), (∀ i, ‖v i‖ = 1) →
      ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ≤ (Real.pi / 2) * optNorm A := by
    intro v hv
    let E := EuclideanSpace ℝ (μ ⊕ μ)
    let sgnV : E → μ → ℝ := fun g i ↦ if 0 < ⟪v i, g⟫_ℝ then 1 else -1
    have hint_pair : ∀ i j, Integrable (fun g : E ↦ A i j * sgnV g i * sgnV g j)
        (stdGaussian E) := by
      intro i j
      have hmeas : Measurable fun g : E ↦ A i j * sgnV g i * sgnV g j := by
        refine (measurable_const.mul ?_).mul ?_
        · exact Measurable.ite
            (isOpen_lt continuous_const (continuous_const.inner continuous_id')).measurableSet
            measurable_const measurable_const
        · exact Measurable.ite
            (isOpen_lt continuous_const (continuous_const.inner continuous_id')).measurableSet
            measurable_const measurable_const
      refine Integrable.of_bound hmeas.aestronglyMeasurable |A i j|
        (Filter.Eventually.of_forall fun g ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |sgnV g i| = 1 := by dsimp [sgnV]; split_ifs <;> norm_num
      have h2 : |sgnV g j| = 1 := by dsimp [sgnV]; split_ifs <;> norm_num
      rw [h1, h2, mul_one, mul_one]
    have hexp_eq : (∫ g : E, (∑ i, ∑ j, A i j * sgnV g i * sgnV g j) ∂stdGaussian E) =
        ∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin ⟪v i, v j⟫_ℝ) := by
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint_pair i j]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum _ fun j _ ↦ hint_pair i j]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hmul : (fun g : E ↦ A i j * sgnV g i * sgnV g j) =
          fun g : E ↦ A i j * (sgnV g i * sgnV g j) := funext fun _ ↦ mul_assoc _ _ _
      rw [hmul, integral_const_mul, integral_stdGaussian_sign_mul_sign (hv i) (hv j)]
    have hpt_le : ∀ g : E, ∑ i, ∑ j, A i j * sgnV g i * sgnV g j ≤ optNorm A := by
      intro g
      refine le_optNorm_of_signs A (fun i ↦ ?_) (fun j ↦ ?_) <;>
        (dsimp [sgnV]; split_ifs <;> simp)
    have hint_le : ∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin ⟪v i, v j⟫_ℝ) ≤ optNorm A := by
      rw [← hexp_eq]
      have hmono := integral_mono_ae
        (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint_pair i j)
        (integrable_const (optNorm A)) (Filter.Eventually.of_forall hpt_le)
      simpa using hmono
    have harcsin_ge : ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ≤
        ∑ i, ∑ j, A i j * Real.arcsin ⟪v i, v j⟫_ℝ := by
      have hhas_ij : ∀ i j,
          HasSum (fun k ↦ A i j * (arcsinSeriesCoeff k * ⟪v i, v j⟫_ℝ ^ (2 * k + 1)))
            (A i j * Real.arcsin ⟪v i, v j⟫_ℝ) := by
        intro i j
        have hij : |⟪v i, v j⟫_ℝ| ≤ 1 := by
          simpa [hv i, hv j] using abs_real_inner_le_norm (v i) (v j)
        exact (hasSum_arcsin hij).mul_left (A i j)
      have hhas_sum : HasSum
          (fun k ↦ ∑ i, ∑ j, A i j * (arcsinSeriesCoeff k * ⟪v i, v j⟫_ℝ ^ (2 * k + 1)))
          (∑ i, ∑ j, A i j * Real.arcsin ⟪v i, v j⟫_ℝ) :=
        hasSum_sum fun i _ ↦ hasSum_sum fun j _ ↦ hhas_ij i j
      have hseries : (∑ i, ∑ j, A i j * Real.arcsin ⟪v i, v j⟫_ℝ) =
          ∑' k : ℕ, arcsinSeriesCoeff k * ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ^ (2 * k + 1) := by
        rw [← hhas_sum.tsum_eq]
        refine tsum_congr fun k ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      have hsumm_all : Summable fun k : ℕ ↦
          arcsinSeriesCoeff k * ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ^ (2 * k + 1) := by
        refine hhas_sum.summable.congr fun k ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      have hterm_nn : ∀ k : ℕ,
          0 ≤ arcsinSeriesCoeff k * ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ^ (2 * k + 1) := by
        intro k
        refine mul_nonneg (arcsinSeriesCoeff_pos k).le ?_
        have hpow : ∀ i j, ⟪v i, v j⟫_ℝ ^ (2 * k + 1) =
            ⟪vecTensorPow (2 * k + 1) (v i), vecTensorPow (2 * k + 1) (v j)⟫_ℝ :=
          fun i j ↦ (inner_vecTensorPow (2 * k + 1) (v i) (v j)).symm
        simp_rw [hpow]
        exact sum_posSemidef_inner_nonneg hA (fun i ↦ vecTensorPow (2 * k + 1) (v i))
      have hk0 : arcsinSeriesCoeff 0 * ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ^ (2 * 0 + 1) ≤
          ∑' k : ℕ, arcsinSeriesCoeff k * ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ ^ (2 * k + 1) :=
        hsumm_all.le_tsum 0 fun k _ ↦ hterm_nn k
      rw [hseries]
      simpa using hk0
    have hfactor : (∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin ⟪v i, v j⟫_ℝ)) =
        (2 / Real.pi) * ∑ i, ∑ j, A i j * Real.arcsin ⟪v i, v j⟫_ℝ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hfactor] at hint_le
    have hinv : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp [Real.pi_ne_zero]
    calc
      ∑ i, ∑ j, A i j * ⟪v i, v j⟫_ℝ
          ≤ ∑ i, ∑ j, A i j * Real.arcsin ⟪v i, v j⟫_ℝ := harcsin_ge
      _ = (Real.pi / 2) * ((2 / Real.pi) * ∑ i, ∑ j, A i j * Real.arcsin ⟪v i, v j⟫_ℝ) := by
            rw [← mul_assoc, hinv, one_mul]
      _ ≤ (Real.pi / 2) * optNorm A :=
            mul_le_mul_of_nonneg_left hint_le (by positivity)
  linarith [hdiag u hu, hdiag w hw]

/-- $k_G \le \frac{\pi}{2}$. -/
theorem littleGrothendieckConstant_le_pi_div_two :
    littleGrothendieckConstant ≤ Real.pi / 2 := by
  refine csSup_le littleGrothendieckRatioSet_nonempty ?_
  rintro r ⟨n, A, hA, rfl⟩
  by_cases hAz : A = 0
  · subst hAz
    simp only [sdpNorm_zero, optNorm_zero, zero_div]
    positivity
  · rw [div_le_iff₀ ((optNorm_pos_iff A).mpr hAz)]
    exact sdpNorm_le_pi_div_two_mul_optNorm_of_posSemidef hA

/-! ### Gaussian Absolute Moments and Cube-Partition Lower Bound $\frac{\pi}{2} \le k_G$ -/

/-- Absolute first moment of the standard real Gaussian:
$\mathbb{E}_{X \sim \mathcal{N}(0, 1)}[|X|] = \sqrt{\frac{2}{\pi}}$. -/
theorem integral_gaussianReal_abs :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = Real.sqrt (2 / Real.pi) := by
  let fPos : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator fun x ↦ x
  let fNeg : ℝ → ℝ := fun x ↦ fPos (-x)
  have hint_id : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  have hint_pos : Integrable fPos (gaussianReal 0 1) := hint_id.indicator measurableSet_Ioi
  have hneg_map : (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1 :=
    gaussianReal_zero_map_neg 1
  have hint_neg : Integrable fNeg (gaussianReal 0 1) := by
    have h := hint_pos
    rw [← hneg_map] at h
    exact h.comp_measurable measurable_neg
  have hpt : (fun x : ℝ ↦ |x|) = fun x ↦ fPos x + fNeg x := by
    ext x
    dsimp [fPos, fNeg, Set.indicator]
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have h1 : ¬ (0 < x) := not_lt.mpr hx.le
      have h2 : 0 < -x := neg_pos.mpr hx
      simp [h1, h2, abs_of_neg hx]
    · simp
    · have h2 : ¬ (0 < -x) := not_lt.mpr (by linarith)
      simp [hx, h2, abs_of_pos hx]
  have hneg_int : ∫ x, fNeg x ∂gaussianReal 0 1 = ∫ x, fPos x ∂gaussianReal 0 1 := by
    have hmap := integral_map (μ := gaussianReal 0 1) (φ := fun x : ℝ ↦ -x)
      measurable_neg.aemeasurable (f := fPos) (by
        rw [hneg_map]
        exact hint_pos.aestronglyMeasurable)
    rw [hneg_map] at hmap
    exact hmap.symm
  have heven : ∫ x : ℝ, |x| ∂gaussianReal 0 1 = 2 * ∫ x, fPos x ∂gaussianReal 0 1 := by
    rw [hpt, integral_add hint_pos hint_neg, hneg_int]
    ring
  rw [heven, integral_gaussianReal_eq_integral_smul (hv := one_ne_zero)]
  have hpdf_ind : (fun x : ℝ ↦ gaussianPDFReal 0 1 x • fPos x) =
      (Set.Ioi (0 : ℝ)).indicator (fun x ↦ gaussianPDFReal 0 1 x * x) := by
    ext x
    dsimp [fPos, Set.indicator]
    split_ifs <;> simp
  rw [hpdf_ind, integral_indicator measurableSet_Ioi]
  -- Evaluate ∫ x in Ioi 0, gaussianPDFReal 0 1 x * x = (√(2π))⁻¹ via FTC
  let G : ℝ → ℝ := fun x ↦ -(Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))
  have hG_deriv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt G (gaussianPDFReal 0 1 x * x) x := by
    intro x _
    have hd1 : HasDerivAt (fun y : ℝ ↦ -(y ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1
      push_cast; ring
    have hd2 := (hd1.exp).const_mul (-(Real.sqrt (2 * Real.pi))⁻¹)
    convert hd2 using 1
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, neg_div]
    ring
  have hG_nonneg : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ gaussianPDFReal 0 1 x * x := by
    intro x hx
    exact mul_nonneg (gaussianPDFReal_nonneg 0 1 x) hx.le
  have hG_tendsto : Filter.Tendsto G Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ 2 / 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
    have h2 : Filter.Tendsto (fun x : ℝ ↦ Real.exp (-(x ^ 2 / 2))) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h1)
    simpa [G] using h2.const_mul (-(Real.sqrt (2 * Real.pi))⁻¹)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hG_deriv hG_nonneg hG_tendsto]
  dsimp [G]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
    Real.exp_zero, mul_one, sub_neg_eq_add, zero_add]
  have hsq : (2 * (Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = 2 / Real.pi := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp [Real.pi_ne_zero]
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- Rotational invariance of the Gaussian $\ell_1$ projection: for any unit vector
$u \in \mathbb{R}^n$,
$\mathbb{E}_{Z \sim \gamma_n}[|\langle u, Z \rangle|] = \sqrt{\frac{2}{\pi}}$. -/
theorem integral_pi_gaussianReal_abs_dotProduct {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    ∫ z : Fin n → ℝ, |∑ r : Fin n, u r * z r|
      ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  have hmap : (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map
      (fun z : Fin n → ℝ ↦ (fun r ↦ u r) ⬝ᵥ z) = gaussianReal 0 1 := by
    have h1 := pi_gaussianReal_map_dotProduct (ι := Fin n) (fun r ↦ u r)
    have hu_eq : WithLp.toLp 2 (fun r : Fin n ↦ u r) = u := rfl
    have hnn : ‖u‖₊ ^ 2 = (1 : ℝ≥0) := by
      ext
      push_cast
      rw [hu, one_pow]
    rwa [hu_eq, hnn] at h1
  have hcomp := integral_map
    (μ := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)
    (φ := fun z : Fin n → ℝ ↦ (fun r ↦ u r) ⬝ᵥ z) (by fun_prop)
    (f := fun x : ℝ ↦ |x|) (by fun_prop)
  rw [hmap] at hcomp
  have hrew : (fun z : Fin n → ℝ ↦ |∑ r : Fin n, u r * z r|) =
      fun z : Fin n → ℝ ↦ |(fun r ↦ u r) ⬝ᵥ z| := by
    ext z
    simp [dotProduct]
  rw [hrew, ← hcomp]
  exact integral_gaussianReal_abs

private theorem integral_pi_gaussianReal_euclideanNorm_ge {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) ≤
      ∫ z : Fin n → ℝ, Real.sqrt (∑ r : Fin n, (z r) ^ 2)
        ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  let γ := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hpoly : ∀ t : ℝ, 0 ≤ t → 1 + (t ^ 2 - 1) / 2 - (t ^ 2 - 1) ^ 2 / 2 ≤ t := by
    intro t ht
    have hfactor : 2 * t - 2 * (1 + (t ^ 2 - 1) / 2 - (t ^ 2 - 1) ^ 2 / 2) =
        t * (t - 1) ^ 2 * (t + 2) := by ring
    have hnn : 0 ≤ t * (t - 1) ^ 2 * (t + 2) := by positivity
    linarith
  have h_eval : ∀ r : Fin n, γ.map (fun z : Fin n → ℝ ↦ z r) = gaussianReal 0 1 := by
    intro r
    simpa using (measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 1) r).map_eq
  have hint_sq : ∀ r : Fin n, Integrable (fun z : Fin n → ℝ ↦ (z r) ^ 2) γ := by
    intro r
    have h1 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
      simpa using (memLp_id_gaussianReal 2).integrable_sq
    rw [← h_eval r] at h1
    exact h1.comp_measurable (measurable_pi_apply r)
  have hm2 : ∀ r : Fin n, ∫ z : Fin n → ℝ, (z r) ^ 2 ∂γ = 1 := by
    intro r
    have : (∫ z : Fin n → ℝ, (z r) ^ 2 ∂γ) = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 := by
      rw [← h_eval r, integral_map (measurable_pi_apply r).aemeasurable (by fun_prop)]
    rw [this, integral_sq_gaussianReal]
  have hint_pow4 : ∀ r : Fin n, Integrable (fun z : Fin n → ℝ ↦ (z r) ^ 4) γ := by
    intro r
    have h1 : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 1) := by
      have hm := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_rpow
        (by norm_num) (by norm_num)
      have hexp : ((4 : ℝ≥0) : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) := by norm_num
      refine hm.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      dsimp only [id_eq]
      rw [Real.norm_eq_abs, hexp, Real.rpow_natCast]
      calc
        |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
        _ = (x ^ 2) ^ 2 := by rw [sq_abs]
        _ = x ^ 4 := by ring
    rw [← h_eval r] at h1
    exact h1.comp_measurable (measurable_pi_apply r)
  have hm4 : ∀ r : Fin n, ∫ z : Fin n → ℝ, (z r) ^ 4 ∂γ = 3 := by
    intro r
    have : (∫ z : Fin n → ℝ, (z r) ^ 4 ∂γ) = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 := by
      rw [← h_eval r, integral_map (measurable_pi_apply r).aemeasurable (by fun_prop)]
    rw [this, integral_pow_four_gaussianReal]
  have hint_cross : ∀ r s : Fin n, Integrable (fun z : Fin n → ℝ ↦ (z r) ^ 2 * (z s) ^ 2) γ := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      simpa [← pow_add] using hint_pow4 r
    · have hindep : IndepFun (fun z : Fin n → ℝ ↦ (z r) ^ 2) (fun z : Fin n → ℝ ↦ (z s) ^ 2) γ := by
        have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ gaussianReal 0 1)
          (fun _ ↦ aemeasurable_id)
        exact (hi.indepFun hrs).comp (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2)
          (measurable_id.pow_const 2) (measurable_id.pow_const 2)
      exact hindep.integrable_mul (hint_sq r) (hint_sq s)
  have hm_cross : ∀ r s : Fin n, r ≠ s → ∫ z : Fin n → ℝ, (z r) ^ 2 * (z s) ^ 2 ∂γ = 1 := by
    intro r s hrs
    have hindep : IndepFun (fun z : Fin n → ℝ ↦ (z r) ^ 2) (fun z : Fin n → ℝ ↦ (z s) ^ 2) γ := by
      have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ gaussianReal 0 1)
        (fun _ ↦ aemeasurable_id)
      exact (hi.indepFun hrs).comp (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2)
        (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have hmul := hindep.integral_mul_eq_mul_integral (hint_sq r).aestronglyMeasurable
      (hint_sq s).aestronglyMeasurable
    simpa [hm2 r, hm2 s] using hmul
  let S : (Fin n → ℝ) → ℝ := fun z ↦ ∑ r : Fin n, (z r) ^ 2
  have hint_S : Integrable S γ := integrable_finsetSum _ fun r _ ↦ hint_sq r
  have hint_S2 : Integrable (fun z ↦ (S z) ^ 2) γ := by
    have hexp : (fun z ↦ (S z) ^ 2) = fun z ↦ ∑ r : Fin n, ∑ s : Fin n, (z r) ^ 2 * (z s) ^ 2 := by
      ext z
      dsimp [S]
      rw [sq, Finset.sum_mul_sum]
    rw [hexp]
    exact integrable_finsetSum _ fun r _ ↦ integrable_finsetSum _ fun s _ ↦ hint_cross r s
  have hES : ∫ z, S z ∂γ = (n : ℝ) := by
    dsimp [S]
    rw [integral_finsetSum _ fun r _ ↦ hint_sq r]
    simp [hm2]
  have hES2 : ∫ z, (S z) ^ 2 ∂γ = (n : ℝ) * ((n : ℝ) + 2) := by
    have hexp : (fun z ↦ (S z) ^ 2) = fun z ↦ ∑ r : Fin n, ∑ s : Fin n, (z r) ^ 2 * (z s) ^ 2 := by
      ext z
      dsimp [S]
      rw [sq, Finset.sum_mul_sum]
    rw [hexp, integral_finsetSum _ fun r _ ↦ integrable_finsetSum _ fun s _ ↦ hint_cross r s]
    have hinner_sum : ∀ r : Fin n,
        (∫ z, (∑ s : Fin n, (z r) ^ 2 * (z s) ^ 2) ∂γ) = (n : ℝ) + 2 := by
      intro r
      rw [integral_finsetSum _ fun s _ ↦ hint_cross r s]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      have hdiag : (∫ z, (z r) ^ 2 * (z r) ^ 2 ∂γ) = 3 := by
        simpa [show ∀ x : ℝ, x ^ 2 * x ^ 2 = x ^ 4 by intro x; ring] using hm4 r
      rw [hdiag]
      have hoff : ∀ s ∈ Finset.univ.erase r, (∫ z, (z r) ^ 2 * (z s) ^ 2 ∂γ) = 1 :=
        fun s hs ↦ hm_cross r s (Finset.ne_of_mem_erase hs).symm
      rw [Finset.sum_congr rfl hoff]
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub hn, Nat.cast_one]
      ring
    simp_rw [hinner_sum]
    simp; ring
  have hint_sqrtS : Integrable (fun z ↦ Real.sqrt (S z)) γ := by
    have hmeas : AEStronglyMeasurable (fun z ↦ Real.sqrt (S z)) γ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hint_S.aestronglyMeasurable
    refine Integrable.mono' (g := fun z ↦ 1 + S z) ((integrable_const 1).add hint_S) hmeas
      (Filter.Eventually.of_forall fun z ↦ ?_)
    have hSnn : 0 ≤ S z := Finset.sum_nonneg fun r _ ↦ sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hSnn, sq_nonneg (Real.sqrt (S z) - 1)]
  let lhs : (Fin n → ℝ) → ℝ := fun z ↦
    1 + (S z / (n : ℝ) - 1) / 2 - (S z / (n : ℝ) - 1) ^ 2 / 2
  have hint_lhs : Integrable lhs γ := by
    have hrew_lhs : lhs = fun z ↦
        (1 / 2 - 1 / 2) + ((1 / (2 * (n : ℝ)) + 1 / (n : ℝ)) * S z) -
          (1 / (2 * (n : ℝ) ^ 2)) * (S z) ^ 2 := by
      ext z
      dsimp [lhs]
      ring
    rw [hrew_lhs]
    exact ((integrable_const _).add (hint_S.const_mul _)).sub (hint_S2.const_mul _)
  have hpt : ∀ z, lhs z ≤ Real.sqrt (S z) / Real.sqrt (n : ℝ) := by
    intro z
    have hSnn : 0 ≤ S z := Finset.sum_nonneg fun r _ ↦ sq_nonneg _
    have htsq : (Real.sqrt (S z) / Real.sqrt (n : ℝ)) ^ 2 = S z / (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hSnn, Real.sq_sqrt hn_pos.le]
    simpa [lhs, htsq] using hpoly (Real.sqrt (S z) / Real.sqrt (n : ℝ)) (by positivity)
  have hint_ineq := integral_mono hint_lhs (hint_sqrtS.div_const _) hpt
  rw [integral_div] at hint_ineq
  have hElhs : ∫ z, lhs z ∂γ = 1 - (n : ℝ)⁻¹ := by
    have hrew_lhs : lhs = fun z ↦
        ((3 / (2 * (n : ℝ))) * S z) - ((1 / (2 * (n : ℝ) ^ 2)) * (S z) ^ 2) := by
      ext z
      dsimp [lhs]
      ring
    rw [hrew_lhs, integral_sub (hint_S.const_mul _) (hint_S2.const_mul _),
      integral_const_mul, integral_const_mul, hES, hES2]
    field_simp [hn_pos.ne']
    ring
  rw [hElhs] at hint_ineq
  exact (le_div_iff₀' hsqrt_pos).mp hint_ineq

private theorem gramPosSemidef {κ : Type*} [Finite κ] {n : ℕ}
    (v : κ → EuclideanSpace ℝ (Fin n)) :
    (Matrix.of fun p q ↦ ⟪v p, v q⟫_ℝ).PosSemidef := by
  cases nonempty_fintype κ
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext p q
    simp [Matrix.conjTranspose_apply, real_inner_comm]
  · intro x
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    have hsq : (∑ p : κ, x p * ∑ q : κ, (∑ r : Fin n, v q r * v p r) * x q) =
        ∑ r : Fin n, (∑ p : κ, x p * v p r) ^ 2 := by
      calc
        (∑ p : κ, x p * ∑ q : κ, (∑ r : Fin n, v q r * v p r) * x q)
            = ∑ p : κ, ∑ r : Fin n, (x p * v p r) * ∑ q : κ, x q * v q r := by
              refine Finset.sum_congr rfl fun p _ ↦ ?_
              rw [Finset.mul_sum]
              have h1 : ∀ q : κ, x p * ((∑ r : Fin n, v q r * v p r) * x q) =
                  ∑ r : Fin n, (x p * v p r) * (x q * v q r) := by
                intro q
                rw [Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun r _ ↦ by ring
              simp_rw [h1]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ ↦ by rw [← Finset.mul_sum]
        _ = ∑ r : Fin n, ∑ p : κ, (x p * v p r) * ∑ q : κ, x q * v q r :=
              Finset.sum_comm
        _ = ∑ r : Fin n, (∑ p : κ, x p * v p r) ^ 2 := by
              refine Finset.sum_congr rfl fun r _ ↦ by rw [← Finset.sum_mul, sq]
    rw [hsq]
    exact Finset.sum_nonneg fun r _ ↦ sq_nonneg _

/-- Finite measurable partition approximation of the normalized Gaussian vector field
$z \mapsto z / \|z\|$ on $(\mathbb{R}^n, \gamma_n)$: for every $n \ge 2$ and $\varepsilon > 0$,
there exist `M : ℕ`, a measurable partition `E : Fin M → Set (Fin n → ℝ)` covering every point of
`Fin n → ℝ` uniquely, and unit vectors `u : Fin M → EuclideanSpace ℝ (Fin n)` such that
$(1 - n^{-1})^2 - \varepsilon \le \sum_{r = 0}^{n - 1} (\sum_{p = 0}^{M - 1} u_{p, r}
\int_{E_p} z_r \, d\gamma_n)^2$. -/
theorem exists_gaussian_partition_unitVectors {n : ℕ} (hn2 : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (E : Fin M → Set (Fin n → ℝ)) (u : Fin M → EuclideanSpace ℝ (Fin n)),
      (∀ p, MeasurableSet (E p)) ∧
      (∀ z : Fin n → ℝ, ∃! p : Fin M, z ∈ E p) ∧
      (∀ p, ‖u p‖ = 1) ∧
      (1 - (n : ℝ)⁻¹) ^ 2 - ε ≤
        ∑ r : Fin n,
          (∑ p : Fin M, u p r *
            ∫ z in E p, z r ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)) ^ 2 := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
  let γ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  by_cases hε_big : (1 - (n : ℝ)⁻¹) ^ 2 - ε ≤ 0
  · let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn1⟩ 1
    refine ⟨1, fun _ ↦ Set.univ, fun _ ↦ e₀, fun _ ↦ MeasurableSet.univ, ?_,
      fun _ ↦ by simp [e₀], ?_⟩
    · intro z
      exact ⟨0, Set.mem_univ z, fun p _ ↦ Subsingleton.elim p 0⟩
    · exact hε_big.trans (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  push Not at hε_big
  let normFn : (Fin n → ℝ) → ℝ := fun z ↦ Real.sqrt (∑ r : Fin n, (z r) ^ 2)
  have hint_coord : ∀ r : Fin n, Integrable (fun z : Fin n → ℝ ↦ z r) γ := by
    intro r
    have h_eval : γ.map (fun z : Fin n → ℝ ↦ z r) = gaussianReal 0 1 := by
      simpa [γ] using (measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 1) r).map_eq
    have h1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
      memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
    rw [← h_eval] at h1
    exact h1.comp_measurable (measurable_pi_apply r)
  have hint_norm : Integrable normFn γ := by
    have hint_sq : ∀ r : Fin n, Integrable (fun z : Fin n → ℝ ↦ (z r) ^ 2) γ := by
      intro r
      have h_eval : γ.map (fun z : Fin n → ℝ ↦ z r) = gaussianReal 0 1 := by
        simpa [γ] using (measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 1) r).map_eq
      have h1 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by
        simpa using (memLp_id_gaussianReal 2).integrable_sq
      rw [← h_eval] at h1
      exact h1.comp_measurable (measurable_pi_apply r)
    have hint_S : Integrable (fun z : Fin n → ℝ ↦ ∑ r : Fin n, (z r) ^ 2) γ :=
      integrable_finsetSum _ fun r _ ↦ hint_sq r
    refine Integrable.mono' (g := fun z ↦ 1 + ∑ r : Fin n, (z r) ^ 2)
      ((integrable_const 1).add hint_S)
      (Real.continuous_sqrt.comp_aestronglyMeasurable hint_S.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z ↦ ?_)
    have hSnn : 0 ≤ ∑ r : Fin n, (z r) ^ 2 := Finset.sum_nonneg fun r _ ↦ sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hSnn, sq_nonneg (Real.sqrt (∑ r : Fin n, (z r) ^ 2) - 1)]
  let boxSet : ℕ → Set (Fin n → ℝ) := fun R ↦
    {z : Fin n → ℝ | ∀ r : Fin n, -(R : ℝ) ≤ z r ∧ z r < (R : ℝ)}
  have hbox_meas : ∀ R : ℕ, MeasurableSet (boxSet R) := by
    intro R
    have : boxSet R = ⋂ r : Fin n, (fun z : Fin n → ℝ ↦ z r) ⁻¹' Set.Ico (-(R : ℝ)) (R : ℝ) := by
      ext z
      simp [boxSet]
    rw [this]
    exact MeasurableSet.iInter fun r ↦ measurableSet_Ico.preimage (measurable_pi_apply r)
  have htend_R : Filter.Tendsto (fun R : ℕ ↦ ∫ z in boxSet (R + 1), normFn z ∂γ)
      Filter.atTop (𝓝 (∫ z, normFn z ∂γ)) := by
    have hdom : ∀ R : ℕ, ∀ᵐ z ∂γ, ‖(boxSet (R + 1)).indicator normFn z‖ ≤ normFn z := by
      intro R
      refine Filter.Eventually.of_forall fun z ↦ ?_
      by_cases hz : z ∈ boxSet (R + 1)
      · simp [hz, normFn, abs_of_nonneg (Real.sqrt_nonneg _)]
      · simp [hz, normFn, Real.sqrt_nonneg]
    have hpt : ∀ᵐ z ∂γ, Filter.Tendsto (fun R : ℕ ↦ (boxSet (R + 1)).indicator normFn z)
        Filter.atTop (𝓝 (normFn z)) := by
      refine Filter.Eventually.of_forall fun z ↦ ?_
      obtain ⟨R₀, hR₀⟩ := exists_nat_gt (∑ r : Fin n, |z r|)
      refine tendsto_nhds_of_eventually_eq (Filter.eventually_atTop.mpr ⟨R₀, fun R hR ↦ ?_⟩)
      have hmem : z ∈ boxSet (R + 1) := by
        intro r
        have hzr : |z r| ≤ ∑ s : Fin n, |z s| :=
          Finset.single_le_sum (fun s _ ↦ abs_nonneg (z s)) (Finset.mem_univ r)
        have hlt : |z r| < ((R + 1 : ℕ) : ℝ) := by
          have : (R₀ : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : R₀ ≤ R + 1)
          linarith
        exact ⟨by linarith [(abs_lt.mp hlt).1], (abs_lt.mp hlt).2⟩
      simp [hmem]
    have ht := tendsto_integral_of_dominated_convergence normFn
      (fun R ↦ hint_norm.aestronglyMeasurable.indicator (hbox_meas (R + 1)))
      hint_norm hdom hpt
    simpa [integral_indicator (hbox_meas _)] using ht
  have hbase_pos : 0 < 1 - (n : ℝ)⁻¹ := by
    have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hinv_le : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ two_pos hn2'
    linarith
  set η := min (Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) / 2)
    (Real.sqrt (n : ℝ) * ε / (4 * (1 - (n : ℝ)⁻¹)))
  have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
  have hEnorm_ge := integral_pi_gaussianReal_euclideanNorm_ge hn1
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp htend_R (η / 2) (half_pos hη_pos)
  set R : ℕ := R₀ + 1
  have hR_pos : 0 < (R : ℝ) := by positivity
  have hbox_ge : Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) - η / 2 ≤
      ∫ z in boxSet R, normFn z ∂γ := by
    have hdist := hR₀ R₀ le_rfl
    rw [Real.dist_eq] at hdist
    have := (abs_lt.mp hdist).1
    linarith [hEnorm_ge]
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (4 * Real.sqrt (n : ℝ) * (R : ℝ) / η)
  set L : ℕ := L₀ + 1
  have hL_pos : 0 < (L : ℝ) := by positivity
  have hmesh_small : 2 * Real.sqrt (n : ℝ) * ((R : ℝ) / (L : ℝ)) < η / 2 := by
    have hL_gt : 4 * Real.sqrt (n : ℝ) * (R : ℝ) / η < (L : ℝ) := by
      have : (L₀ : ℝ) < (L : ℝ) := by exact_mod_cast (Nat.lt_succ_self L₀)
      linarith
    rw [div_lt_iff₀ hη_pos] at hL_gt
    have h1 : 2 * Real.sqrt (n : ℝ) * (R : ℝ) < (η / 2) * (L : ℝ) := by linarith
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ hL_pos).mpr h1
  let ι := (Fin n → Fin (2 * L)) ⊕ Unit
  let cellIco : Fin (2 * L) → Set ℝ := fun s ↦
    Set.Ico (-(R : ℝ) + (s.1 : ℝ) * ((R : ℝ) / (L : ℝ)))
      (-(R : ℝ) + ((s.1 : ℝ) + 1) * ((R : ℝ) / (L : ℝ)))
  let partSet : ι → Set (Fin n → ℝ) := fun p ↦
    match p with
    | Sum.inl α => {z : Fin n → ℝ | ∀ r : Fin n, z r ∈ cellIco (α r)}
    | Sum.inr () => (boxSet R)ᶜ
  have hpart_meas : ∀ p : ι, MeasurableSet (partSet p) := by
    rintro (α | ⟨⟩)
    · have : partSet (Sum.inl α) =
          ⋂ r : Fin n, (fun z : Fin n → ℝ ↦ z r) ⁻¹' cellIco (α r) := by
        ext z; simp [partSet]
      rw [this]
      exact MeasurableSet.iInter fun r ↦ measurableSet_Ico.preimage (measurable_pi_apply r)
    · exact (hbox_meas R).compl
  have h1D_mem_range : ∀ (s : Fin (2 * L)) (x : ℝ),
      x ∈ cellIco s → -(R : ℝ) ≤ x ∧ x < (R : ℝ) := by
    intro s x hs
    dsimp [cellIco] at hs
    set h : ℝ := (R : ℝ) / (L : ℝ)
    have hh_pos : 0 < h := div_pos hR_pos hL_pos
    have hs_le : ((s.1 : ℝ) + 1) ≤ 2 * (L : ℝ) := by
      exact_mod_cast (by omega : s.1 + 1 ≤ 2 * L)
    have htop : -(R : ℝ) + ((s.1 : ℝ) + 1) * h ≤ (R : ℝ) := by
      have : 2 * (L : ℝ) * h = 2 * (R : ℝ) := by dsimp [h]; field_simp [hL_pos.ne']
      nlinarith [mul_le_mul_of_nonneg_right hs_le hh_pos.le]
    have hbot : -(R : ℝ) ≤ -(R : ℝ) + (s.1 : ℝ) * h := by
      have hnn : 0 ≤ (s.1 : ℝ) * h := by positivity
      linarith
    exact ⟨hbot.trans hs.1, hs.2.trans_le htop⟩
  have h1D_part : ∀ x : ℝ, -(R : ℝ) ≤ x ∧ x < (R : ℝ) → ∃! s : Fin (2 * L), x ∈ cellIco s := by
    intro x ⟨hx1, hx2⟩
    set h : ℝ := (R : ℝ) / (L : ℝ)
    have hh_pos : 0 < h := div_pos hR_pos hL_pos
    let k : ℕ := ⌊(x + (R : ℝ)) / h⌋₊
    have hk_nn : 0 ≤ (x + (R : ℝ)) / h := div_nonneg (by linarith) hh_pos.le
    have hk_lt : k < 2 * L := by
      have hlt : (x + (R : ℝ)) / h < (2 * L : ℕ) := by
        rw [div_lt_iff₀ hh_pos]
        dsimp [h]
        push_cast
        have : (2 * (L : ℝ)) * ((R : ℝ) / (L : ℝ)) = 2 * (R : ℝ) := by
          field_simp [hL_pos.ne']
        linarith
      exact (Nat.floor_lt hk_nn).mpr hlt
    refine ⟨⟨k, hk_lt⟩, ?_, ?_⟩
    · dsimp [cellIco]
      have hfl1 := Nat.floor_le hk_nn
      have hfl2 := Nat.lt_floor_add_one ((x + (R : ℝ)) / h)
      rw [le_div_iff₀ hh_pos] at hfl1
      rw [div_lt_iff₀ hh_pos] at hfl2
      exact ⟨by linarith, by linarith⟩
    · intro s hs
      dsimp [cellIco] at hs
      ext
      dsimp
      symm
      rw [Nat.floor_eq_iff hk_nn, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hpart_unique : ∀ z : Fin n → ℝ, ∃! p : ι, z ∈ partSet p := by
    intro z
    by_cases hz : z ∈ boxSet R
    · choose f hf_mem hf_uniq using fun r : Fin n ↦ h1D_part (z r) (hz r)
      refine ⟨Sum.inl f, hf_mem, ?_⟩
      rintro (α | ⟨⟩) hα
      · congr 1
        ext r
        exact congrArg Fin.val (hf_uniq r (α r) (hα r))
      · exact False.elim (hα hz)
    · refine ⟨Sum.inr (), hz, ?_⟩
      rintro (α | ⟨⟩) hα
      · exact False.elim (hz fun r ↦ h1D_mem_range (α r) (z r) (hα r))
      · rfl
  have hpart_disj : Pairwise fun p q : ι ↦ Disjoint (partSet p) (partSet q) := by
    intro p q hpq
    rw [Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨p₀, _, hu⟩ := hpart_unique z
    exact hpq ((hu p hzp).trans (hu q hzq).symm)
  have hpart_union_univ : (⋃ p ∈ (Finset.univ : Finset ι), partSet p) = Set.univ := by
    ext z
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨p, hp, _⟩ := hpart_unique z
    exact ⟨p, hp⟩
  have hbox_union : (⋃ α ∈ (Finset.univ : Finset (Fin n → Fin (2 * L))),
      partSet (Sum.inl α)) = boxSet R := by
    ext z
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · rintro ⟨α, hα⟩ r
      exact h1D_mem_range (α r) (z r) (hα r)
    · intro hz
      choose f hf_mem _ using fun r : Fin n ↦ h1D_part (z r) (hz r)
      exact ⟨f, hf_mem⟩
  let mVec : ι → EuclideanSpace ℝ (Fin n) := fun p ↦
    WithLp.toLp 2 fun r ↦ ∫ z in partSet p, z r ∂γ
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn1⟩ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  let uDir : ι → EuclideanSpace ℝ (Fin n) := fun p ↦
    if mVec p = 0 then e₀ else ‖mVec p‖⁻¹ • mVec p
  have huDir_norm : ∀ p : ι, ‖uDir p‖ = 1 := by
    intro p
    dsimp [uDir]
    split_ifs with hp
    · exact he₀
    · have hpos : 0 < ‖mVec p‖ := norm_pos_iff.mpr hp
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  have hmVec_eq : ∀ p : ι, mVec p = ‖mVec p‖ • uDir p := by
    intro p
    dsimp [uDir]
    split_ifs with hp
    · simp [hp]
    · have hpos : 0 < ‖mVec p‖ := norm_pos_iff.mpr hp
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  let b : Fin n → ℝ := fun r ↦ ∑ p : ι, ‖mVec p‖ * (uDir p r) ^ 2
  have hb_ge : (1 / (n : ℝ)) * (∑ p : ι, ‖mVec p‖) ^ 2 ≤ ∑ r : Fin n, (b r) ^ 2 := by
    have hsum_b : ∑ r : Fin n, b r = ∑ p : ι, ‖mVec p‖ := by
      dsimp [b]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← Finset.mul_sum]
      have hu2 : ∑ r : Fin n, (uDir p r) ^ 2 = 1 := by
        have := EuclideanSpace.norm_sq_eq (uDir p)
        rw [huDir_norm p, one_pow] at this
        simpa [Real.norm_eq_abs, sq_abs] using this.symm
      rw [hu2, mul_one]
    have hcs : (∑ r : Fin n, (1 : ℝ) * b r) ^ 2 ≤
        (∑ r : Fin n, (1 : ℝ) ^ 2) * ∑ r : Fin n, (b r) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ ↦ (1 : ℝ)) b
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hcs
    rw [hsum_b] at hcs
    rw [one_div, inv_mul_le_iff₀ hn_pos]
    exact hcs
  have hsum_mVec_ge : Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) - η ≤ ∑ p : ι, ‖mVec p‖ := by
    set h : ℝ := (R : ℝ) / (L : ℝ)
    have hh_pos : 0 < h := div_pos hR_pos hL_pos
    let corner : (Fin n → Fin (2 * L)) → EuclideanSpace ℝ (Fin n) := fun α ↦
      WithLp.toLp 2 fun r ↦ -(R : ℝ) + ((α r).1 : ℝ) * h
    have hcell_bound : ∀ α : Fin n → Fin (2 * L),
        ∫ z in partSet (Sum.inl α), normFn z ∂γ ≤
          ‖mVec (Sum.inl α)‖ + 2 * Real.sqrt (n : ℝ) * h * γ.real (partSet (Sum.inl α)) := by
      intro α
      set Eα := partSet (Sum.inl α)
      have hdiff_coord : ∀ z ∈ Eα, ∀ r : Fin n, |z r - corner α r| ≤ h := by
        intro z hz r
        have hzr := hz r
        dsimp [cellIco] at hzr
        dsimp [corner]
        rw [abs_le]
        exact ⟨by linarith [hzr.1, hh_pos], by linarith [hzr.2]⟩
      have hm_corner : ‖mVec (Sum.inl α) - (γ.real Eα) • corner α‖ ≤
          Real.sqrt (n : ℝ) * h * γ.real Eα := by
        have hsq : ‖mVec (Sum.inl α) - (γ.real Eα) • corner α‖ ^ 2 ≤
            (Real.sqrt (n : ℝ) * h * γ.real Eα) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          have hcoord_le : ∀ r : Fin n,
              ‖(mVec (Sum.inl α) - (γ.real Eα) • corner α) r‖ ^ 2 ≤ (h * γ.real Eα) ^ 2 := by
            intro r
            rw [Real.norm_eq_abs, sq_abs, sq_le_sq,
              abs_of_nonneg (mul_nonneg hh_pos.le measureReal_nonneg)]
            have hcoord_eq : (mVec (Sum.inl α) - (γ.real Eα) • corner α) r =
                ∫ z in Eα, (z r - corner α r) ∂γ := by
              change (∫ z in Eα, z r ∂γ) - γ.real Eα * corner α r = _
              rw [integral_sub (hint_coord r).integrableOn (integrableOn_const (by simp)),
                setIntegral_const, smul_eq_mul]
            rw [hcoord_eq]
            calc
              |∫ z in Eα, (z r - corner α r) ∂γ|
                  ≤ ∫ z in Eα, |z r - corner α r| ∂γ := by
                    simpa only [Real.norm_eq_abs] using
                      norm_integral_le_integral_norm (μ := γ.restrict Eα)
                        (fun z : Fin n → ℝ ↦ z r - corner α r)
              _ ≤ ∫ _z in Eα, h ∂γ := by
                    refine setIntegral_mono_on
                      (((hint_coord r).sub (integrable_const _)).norm.integrableOn)
                      (integrableOn_const (by simp)) (hpart_meas (Sum.inl α))
                      (fun z hz ↦ hdiff_coord z hz r)
              _ = h * γ.real Eα := by rw [setIntegral_const, smul_eq_mul, mul_comm]
          calc
            ∑ r : Fin n, ‖(mVec (Sum.inl α) - (γ.real Eα) • corner α) r‖ ^ 2
                ≤ ∑ _r : Fin n, (h * γ.real Eα) ^ 2 := Finset.sum_le_sum fun r _ ↦ hcoord_le r
            _ = (n : ℝ) * (h * γ.real Eα) ^ 2 := by simp
            _ = Real.sqrt (n : ℝ) ^ 2 * (h * γ.real Eα) ^ 2 := by rw [Real.sq_sqrt hn_pos.le]
            _ = (Real.sqrt (n : ℝ) * h * γ.real Eα) ^ 2 := by ring
        nlinarith [norm_nonneg (mVec (Sum.inl α) - (γ.real Eα) • corner α),
          show 0 ≤ Real.sqrt (n : ℝ) * h * γ.real Eα by positivity]
      have hnormFn_le : ∀ z ∈ Eα, normFn z ≤ ‖corner α‖ + Real.sqrt (n : ℝ) * h := by
        intro z hz
        let zVec : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
        have hz_eq : normFn z = ‖zVec‖ := by
          dsimp [normFn, zVec]
          rw [EuclideanSpace.norm_eq]
          simp [Real.norm_eq_abs, sq_abs]
        rw [hz_eq]
        have hdiff_vec : ‖zVec - corner α‖ ≤ Real.sqrt (n : ℝ) * h := by
          have hsq : ‖zVec - corner α‖ ^ 2 ≤ (Real.sqrt (n : ℝ) * h) ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
            calc
              ∑ r : Fin n, ‖(zVec - corner α) r‖ ^ 2
                  ≤ ∑ _r : Fin n, h ^ 2 := by
                    refine Finset.sum_le_sum fun r _ ↦ ?_
                    rw [Real.norm_eq_abs, sq_abs, sq_le_sq, abs_of_pos hh_pos]
                    exact hdiff_coord z hz r
              _ = (Real.sqrt (n : ℝ) * h) ^ 2 := by
                    simp [mul_pow, Real.sq_sqrt hn_pos.le]
          nlinarith [norm_nonneg (zVec - corner α),
            show 0 ≤ Real.sqrt (n : ℝ) * h by positivity]
        have htri : ‖zVec‖ ≤ ‖corner α‖ + ‖zVec - corner α‖ := by
          simpa using norm_add_le (corner α) (zVec - corner α)
        linarith
      have hint_Eα : ∫ z in Eα, normFn z ∂γ ≤
          (‖corner α‖ + Real.sqrt (n : ℝ) * h) * γ.real Eα := by
        calc
          ∫ z in Eα, normFn z ∂γ
              ≤ ∫ _z in Eα, (‖corner α‖ + Real.sqrt (n : ℝ) * h) ∂γ :=
                setIntegral_mono_on hint_norm.integrableOn (integrableOn_const (by simp))
                  (hpart_meas (Sum.inl α)) hnormFn_le
          _ = (‖corner α‖ + Real.sqrt (n : ℝ) * h) * γ.real Eα := by
                rw [setIntegral_const, smul_eq_mul, mul_comm]
      have hrev_tri : γ.real Eα * ‖corner α‖ ≤
          ‖mVec (Sum.inl α)‖ + ‖mVec (Sum.inl α) - (γ.real Eα) • corner α‖ := by
        have h1 : ‖(γ.real Eα) • corner α‖ ≤
            ‖mVec (Sum.inl α)‖ + ‖(γ.real Eα) • corner α - mVec (Sum.inl α)‖ := by
          simpa using norm_add_le (mVec (Sum.inl α)) ((γ.real Eα) • corner α - mVec (Sum.inl α))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, norm_sub_rev] at h1
        exact h1
      linarith
    have hbox_sum : ∫ z in boxSet R, normFn z ∂γ =
        ∑ α : Fin n → Fin (2 * L), ∫ z in partSet (Sum.inl α), normFn z ∂γ := by
      rw [← hbox_union]
      exact integral_biUnion_finset Finset.univ
        (fun α _ ↦ hpart_meas (Sum.inl α))
        (fun α _ β _ hαβ ↦ @hpart_disj (Sum.inl α) (Sum.inl β) (fun h ↦ hαβ (Sum.inl.inj h)))
        (fun α _ ↦ hint_norm.integrableOn)
    have hprob_sum : (∑ α : Fin n → Fin (2 * L), γ.real (partSet (Sum.inl α))) ≤ 1 := by
      have hunion_prob : (∑ α : Fin n → Fin (2 * L), γ.real (partSet (Sum.inl α))) =
          γ.real (boxSet R) := by
        have h1 : (∑ α : Fin n → Fin (2 * L), ∫ _z in partSet (Sum.inl α), (1 : ℝ) ∂γ) =
            ∫ _z in boxSet R, (1 : ℝ) ∂γ := by
          rw [← hbox_union]
          symm
          exact integral_biUnion_finset Finset.univ
            (fun α _ ↦ hpart_meas (Sum.inl α))
            (fun α _ β _ hαβ ↦ @hpart_disj (Sum.inl α) (Sum.inl β) (fun h ↦ hαβ (Sum.inl.inj h)))
            (fun _ _ ↦ integrableOn_const (by simp))
        simpa [setIntegral_const] using h1
      rw [hunion_prob]
      exact measureReal_le_one
    have hm_inl_le : (∑ α : Fin n → Fin (2 * L), ‖mVec (Sum.inl α)‖) ≤ ∑ p : ι, ‖mVec p‖ := by
      simp only [ι, Fintype.sum_sum_type, Fintype.sum_unique]
      linarith [norm_nonneg (mVec (Sum.inr ()))]
    have hsum_cells := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Fin (2 * L))))
      fun α _ ↦ hcell_bound α
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_cells
    have h2 : 2 * Real.sqrt (n : ℝ) * h *
        (∑ α : Fin n → Fin (2 * L), γ.real (partSet (Sum.inl α))) ≤
        2 * Real.sqrt (n : ℝ) * h :=
      mul_le_of_le_one_right (by positivity) hprob_sum
    linarith [hbox_ge, hbox_sum, hsum_cells, h2, hm_inl_le, hmesh_small]
  have hb_lower : (1 - (n : ℝ)⁻¹) ^ 2 - ε ≤ ∑ r : Fin n, (b r) ^ 2 := by
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hη_le1 : η ≤ Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) / 2 := min_le_left _ _
    have hη_le2 : η ≤ Real.sqrt (n : ℝ) * ε / (4 * (1 - (n : ℝ)⁻¹)) := min_le_right _ _
    have hdiv_ge : (1 - (n : ℝ)⁻¹) - η / Real.sqrt (n : ℝ) ≤
        (∑ p : ι, ‖mVec p‖) / Real.sqrt (n : ℝ) := by
      rw [le_div_iff₀ hsqrt_pos]
      have : ((1 - (n : ℝ)⁻¹) - η / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) =
          Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) - η := by
        field_simp [hsqrt_pos.ne']
      linarith [hsum_mVec_ge]
    have hlhs_nn : 0 ≤ (1 - (n : ℝ)⁻¹) - η / Real.sqrt (n : ℝ) := by
      have : η / Real.sqrt (n : ℝ) ≤ (1 - (n : ℝ)⁻¹) / 2 := by
        rw [div_le_iff₀ hsqrt_pos]
        have : ((1 - (n : ℝ)⁻¹) / 2) * Real.sqrt (n : ℝ) =
            Real.sqrt (n : ℝ) * (1 - (n : ℝ)⁻¹) / 2 := by ring
        linarith
      linarith
    have hsq_ge : ((1 - (n : ℝ)⁻¹) - η / Real.sqrt (n : ℝ)) ^ 2 ≤
        ((∑ p : ι, ‖mVec p‖) / Real.sqrt (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlhs_nn hdiv_ge 2
    have hsq_eq : ((∑ p : ι, ‖mVec p‖) / Real.sqrt (n : ℝ)) ^ 2 =
        (1 / (n : ℝ)) * (∑ p : ι, ‖mVec p‖) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hn_pos.le]
      ring
    have herr : 2 * (1 - (n : ℝ)⁻¹) * (η / Real.sqrt (n : ℝ)) ≤ ε := by
      have : η / Real.sqrt (n : ℝ) ≤ ε / (4 * (1 - (n : ℝ)⁻¹)) := by
        rw [div_le_iff₀ hsqrt_pos]
        have : (ε / (4 * (1 - (n : ℝ)⁻¹))) * Real.sqrt (n : ℝ) =
            Real.sqrt (n : ℝ) * ε / (4 * (1 - (n : ℝ)⁻¹)) := by ring
        linarith
      have hmul := mul_le_mul_of_nonneg_left this (show 0 ≤ 2 * (1 - (n : ℝ)⁻¹) by positivity)
      have haux : ∀ b : ℝ, b ≠ 0 → 2 * b * (ε / (4 * b)) = ε / 2 := fun b hb ↦ by
        field_simp [hb]
        ring
      have hsimp : 2 * (1 - (n : ℝ)⁻¹) * (ε / (4 * (1 - (n : ℝ)⁻¹))) = ε / 2 :=
        haux (1 - (n : ℝ)⁻¹) hbase_pos.ne'
      linarith
    have hexp_sq : (1 - (n : ℝ)⁻¹) ^ 2 - 2 * (1 - (n : ℝ)⁻¹) * (η / Real.sqrt (n : ℝ)) ≤
        ((1 - (n : ℝ)⁻¹) - η / Real.sqrt (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (η / Real.sqrt (n : ℝ))]
    linarith [hb_ge, hsq_ge, hsq_eq, herr, hexp_sq]
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k ↦ partSet (e.symm k), fun k ↦ uDir (e.symm k),
    fun k ↦ hpart_meas (e.symm k), ?_, fun k ↦ huDir_norm (e.symm k), ?_⟩
  · intro z
    obtain ⟨p, hp, hu⟩ := hpart_unique z
    refine ⟨e p, by simpa using hp, fun k hk ↦ ?_⟩
    calc
      k = e (e.symm k) := (e.apply_symm_apply k).symm
      _ = e p := congrArg e (hu (e.symm k) hk)
  · refine hb_lower.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    congr 1
    calc
      b r = ∑ p : ι, uDir p r * ∫ z in partSet p, z r ∂γ := by
        dsimp [b]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        have hmr : ∫ z in partSet p, z r ∂γ = ‖mVec p‖ * uDir p r := by
          have := congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v r) (hmVec_eq p)
          simpa [mVec] using this
        rw [hmr]
        ring
      _ = ∑ k : Fin (Fintype.card ι), uDir (e.symm k) r * ∫ z in partSet (e.symm k), z r ∂γ :=
        (Equiv.sum_comp e.symm fun p ↦ uDir p r * ∫ z in partSet p, z r ∂γ).symm

/-- Lower bound $\frac{\pi}{2} \le k_G$ via finite cube-partition discretization of the first
Gaussian Hermite projection $\Pi_1^{(n)}$. -/
theorem pi_div_two_le_littleGrothendieckConstant :
    Real.pi / 2 ≤ littleGrothendieckConstant := by
  classical
  suffices hseq : ∀ n : ℕ, 2 ≤ n →
      (Real.pi / 2) * (1 - (n : ℝ)⁻¹) ^ 2 ≤ littleGrothendieckConstant by
    have htend : Filter.Tendsto (fun n : ℕ ↦ (Real.pi / 2) * ((1 : ℝ) - ((n : ℝ) + 2)⁻¹) ^ 2)
        Filter.atTop (𝓝 ((Real.pi / 2) * ((1 : ℝ) - 0) ^ 2)) := by
      refine (tendsto_const_nhds (x := Real.pi / 2)).mul (Filter.Tendsto.pow ?_ 2)
      refine (tendsto_const_nhds (x := (1 : ℝ))).sub ?_
      exact tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    have hbound_n : ∀ n : ℕ,
        (Real.pi / 2) * ((1 : ℝ) - ((n : ℝ) + 2)⁻¹) ^ 2 ≤ littleGrothendieckConstant := by
      intro n
      simpa [Nat.cast_add] using hseq (n + 2) (by omega)
    simpa using le_of_tendsto htend (Filter.Eventually.of_forall hbound_n)
  intro n hn2
  let γ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  suffices happrox : ∀ ε : ℝ, 0 < ε →
      (Real.pi / 2) * ((1 - (n : ℝ)⁻¹) ^ 2 - ε) ≤ littleGrothendieckConstant by
    by_contra hlt
    push Not at hlt
    set δ := ((Real.pi / 2) * (1 - (n : ℝ)⁻¹) ^ 2 - littleGrothendieckConstant) / Real.pi
    have hδ : 0 < δ := div_pos (by linarith) Real.pi_pos
    have := happrox δ hδ
    have hcalc : (Real.pi / 2) * ((1 - (n : ℝ)⁻¹) ^ 2 - δ) =
        ((Real.pi / 2) * (1 - (n : ℝ)⁻¹) ^ 2 + littleGrothendieckConstant) / 2 := by
      dsimp [δ]
      field_simp [Real.pi_ne_zero]
      ring
    linarith
  intro ε hε
  have hkg_nn : 0 ≤ littleGrothendieckConstant := by
    let A₁ : Matrix (Fin 1) (Fin 1) ℝ := 1
    have h1 : 0 ≤ sdpNorm A₁ / optNorm A₁ := div_nonneg (sdpNorm_nonneg A₁) (optNorm_nonneg A₁)
    exact h1.trans (le_csSup littleGrothendieckRatioSet_bddAbove ⟨1, A₁, Matrix.PosSemidef.one,
      rfl⟩)
  by_cases hε_big : (1 - (n : ℝ)⁻¹) ^ 2 - ε ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hε_big).trans hkg_nn
  push Not at hε_big
  have hint_coord : ∀ r : Fin n, Integrable (fun z : Fin n → ℝ ↦ z r) γ := by
    intro r
    have h_eval : γ.map (fun z : Fin n → ℝ ↦ z r) = gaussianReal 0 1 := by
      simpa [γ] using (measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 1) r).map_eq
    have h1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
      memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
    rw [← h_eval] at h1
    exact h1.comp_measurable (measurable_pi_apply r)
  obtain ⟨M, E, uDir, hE_meas, hE_uniq, huDir_norm, hsum_ge⟩ :=
    exists_gaussian_partition_unitVectors (n := n) hn2 hε
  have hE_disj : Pairwise fun p q : Fin M ↦ Disjoint (E p) (E q) := by
    intro p q hpq
    rw [Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨p₀, _, hu⟩ := hE_uniq z
    exact hpq ((hu p hzp).trans (hu q hzq).symm)
  have hE_union : (⋃ p ∈ (Finset.univ : Finset (Fin M)), E p) = Set.univ := by
    ext z
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨p, hp, _⟩ := hE_uniq z
    exact ⟨p, hp⟩
  let mVec : Fin M → EuclideanSpace ℝ (Fin n) := fun p ↦
    WithLp.toLp 2 fun r ↦ ∫ z in E p, z r ∂γ
  let A : Matrix (Fin M) (Fin M) ℝ := Matrix.of fun p q ↦ ⟪mVec p, mVec q⟫_ℝ
  have hA_psd : A.PosSemidef := gramPosSemidef mVec
  have hvec_norm_le : ∀ s : Fin M → ℝ, (∀ p, |s p| ≤ 1) →
      ‖∑ p : Fin M, s p • mVec p‖ ≤ Real.sqrt (2 / Real.pi) := by
    intro s hs
    set V : EuclideanSpace ℝ (Fin n) := ∑ p : Fin M, s p • mVec p
    by_cases hVz : V = 0
    · rw [hVz, norm_zero]
      positivity
    · have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hVz
      let u : EuclideanSpace ℝ (Fin n) := ‖V‖⁻¹ • V
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hVpos), inv_mul_cancel₀ hVpos.ne']
      have hV_eq : ‖V‖ = ∑ p : Fin M, s p * ⟪u, mVec p⟫_ℝ := by
        have h1 : ⟪u, V⟫_ℝ = ‖V‖ := by
          dsimp [u]
          rw [inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
          field_simp [hVpos.ne']
        rw [← h1]
        dsimp [V]
        rw [inner_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [inner_smul_right]
      have hint_dot : Integrable (fun z : Fin n → ℝ ↦ ∑ r : Fin n, u r * z r) γ :=
        integrable_finsetSum _ fun r _ ↦ (hint_coord r).const_mul (u r)
      have hinner_p : ∀ p : Fin M, ⟪u, mVec p⟫_ℝ =
          ∫ z in E p, (∑ r : Fin n, u r * z r) ∂γ := by
        intro p
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
        dsimp [mVec]
        rw [integral_finsetSum _ fun r _ ↦ ((hint_coord r).const_mul (u r)).integrableOn]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [integral_const_mul, mul_comm]
      have hterm_le : ∀ p : Fin M,
          s p * ⟪u, mVec p⟫_ℝ ≤ ∫ z in E p, |∑ r : Fin n, u r * z r| ∂γ := by
        intro p
        calc
          s p * ⟪u, mVec p⟫_ℝ ≤ |s p * ⟪u, mVec p⟫_ℝ| := le_abs_self _
          _ = |s p| * |⟪u, mVec p⟫_ℝ| := abs_mul _ _
          _ ≤ 1 * |⟪u, mVec p⟫_ℝ| := by gcongr; exact hs p
          _ = |∫ z in E p, (∑ r : Fin n, u r * z r) ∂γ| := by rw [one_mul, hinner_p p]
          _ ≤ ∫ z in E p, |∑ r : Fin n, u r * z r| ∂γ := by
            simpa only [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (μ := γ.restrict (E p))
                (fun z : Fin n → ℝ ↦ ∑ r : Fin n, u r * z r)
      calc
        ‖V‖ = ∑ p : Fin M, s p * ⟪u, mVec p⟫_ℝ := hV_eq
        _ ≤ ∑ p : Fin M, ∫ z in E p, |∑ r : Fin n, u r * z r| ∂γ :=
          Finset.sum_le_sum fun p _ ↦ hterm_le p
        _ = ∫ z in (⋃ p ∈ (Finset.univ : Finset (Fin M)), E p), |∑ r : Fin n, u r * z r| ∂γ := by
          symm
          exact integral_biUnion_finset Finset.univ (fun p _ ↦ hE_meas p)
            (hE_disj.set_pairwise _) (fun p _ ↦ hint_dot.norm.integrableOn)
        _ = ∫ z, |∑ r : Fin n, u r * z r| ∂γ := by
          rw [hE_union, Measure.restrict_univ]
        _ = Real.sqrt (2 / Real.pi) := integral_pi_gaussianReal_abs_dotProduct u hu
  have hopt_le : optNorm A ≤ 2 / Real.pi := by
    rw [optNorm_le_iff]
    intro x y hx hy
    have hx1 : ∀ p, |x p| ≤ 1 := fun p ↦ by
      rcases hx p with h | h
      · rw [h]; norm_num
      · rw [Set.mem_singleton_iff.mp h]; norm_num
    have hy1 : ∀ q, |y q| ≤ 1 := fun q ↦ by
      rcases hy q with h | h
      · rw [h]; norm_num
      · rw [Set.mem_singleton_iff.mp h]; norm_num
    have hbilin : (∑ p : Fin M, ∑ q : Fin M, A p q * x p * y q) =
        ⟪∑ p : Fin M, x p • mVec p, ∑ q : Fin M, y q • mVec q⟫_ℝ := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [inner_smul_left, inner_smul_right, conj_trivial]
      dsimp [A]
      ring
    rw [hbilin]
    calc
      ⟪∑ p : Fin M, x p • mVec p, ∑ q : Fin M, y q • mVec q⟫_ℝ
          ≤ ‖∑ p : Fin M, x p • mVec p‖ * ‖∑ q : Fin M, y q • mVec q‖ :=
            (le_abs_self _).trans (abs_real_inner_le_norm _ _)
      _ ≤ Real.sqrt (2 / Real.pi) * Real.sqrt (2 / Real.pi) :=
            mul_le_mul (hvec_norm_le x hx1) (hvec_norm_le y hy1) (norm_nonneg _) (by positivity)
      _ = 2 / Real.pi := Real.mul_self_sqrt (by positivity)
  have hsdp_lower : (1 - (n : ℝ)⁻¹) ^ 2 - ε ≤ sdpNorm A := by
    refine hsum_ge.trans (le_trans ?_ (sum_inner_le_sdpNorm A huDir_norm huDir_norm))
    have hrew : (∑ p : Fin M, ∑ q : Fin M, A p q * ⟪uDir p, uDir q⟫_ℝ) =
        ∑ r : Fin n, ∑ s : Fin n, (∑ p : Fin M, uDir p r * mVec p s) ^ 2 := by
      simp only [A, Matrix.of_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      calc
        (∑ p : Fin M, ∑ q : Fin M, (∑ s : Fin n, mVec q s * mVec p s) *
            (∑ r : Fin n, uDir q r * uDir p r))
            = ∑ p : Fin M, ∑ r : Fin n, ∑ s : Fin n, ∑ q : Fin M,
                (uDir p r * mVec p s) * (uDir q r * mVec q s) := by
              refine Finset.sum_congr rfl fun p _ ↦ ?_
              have h1 : ∀ q : Fin M,
                  (∑ s : Fin n, mVec q s * mVec p s) * (∑ r : Fin n, uDir q r * uDir p r) =
                  ∑ r : Fin n, ∑ s : Fin n, (uDir p r * mVec p s) * (uDir q r * mVec q s) := by
                intro q
                rw [mul_comm, Finset.sum_mul_sum]
                refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring
              simp_rw [h1]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_comm
        _ = ∑ r : Fin n, ∑ s : Fin n, ∑ p : Fin M, ∑ q : Fin M,
              (uDir p r * mVec p s) * (uDir q r * mVec q s) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_comm
        _ = ∑ r : Fin n, ∑ s : Fin n, (∑ p : Fin M, uDir p r * mVec p s) ^ 2 := by
              refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
              rw [sq, Finset.sum_mul_sum]
    rw [hrew]
    refine Finset.sum_le_sum fun r _ ↦ ?_
    exact Finset.single_le_sum (f := fun s : Fin n ↦ (∑ p : Fin M, uDir p r * mVec p s) ^ 2)
      (fun s _ ↦ sq_nonneg _) (Finset.mem_univ r)
  have hsdp_pos : 0 < sdpNorm A := lt_of_lt_of_le hε_big hsdp_lower
  have hAne : A ≠ 0 := by
    intro hAz
    rw [hAz, sdpNorm_zero] at hsdp_pos
    exact lt_irrefl 0 hsdp_pos
  have hopt_pos : 0 < optNorm A := (optNorm_pos_iff A).mpr hAne
  have hratio_le : sdpNorm A / optNorm A ≤ littleGrothendieckConstant :=
    le_csSup littleGrothendieckRatioSet_bddAbove ⟨M, A, hA_psd, rfl⟩
  refine le_trans ?_ hratio_le
  rw [le_div_iff₀ hopt_pos]
  calc
    (Real.pi / 2) * ((1 - (n : ℝ)⁻¹) ^ 2 - ε) * optNorm A
        ≤ (Real.pi / 2) * ((1 - (n : ℝ)⁻¹) ^ 2 - ε) * (2 / Real.pi) :=
          mul_le_mul_of_nonneg_left hopt_le (by positivity)
    _ = (1 - (n : ℝ)⁻¹) ^ 2 - ε := by
          field_simp [Real.pi_ne_zero]
    _ ≤ sdpNorm A := hsdp_lower

/-- **Grothendieck's Little Theorem**: the little Grothendieck constant equals $\frac{\pi}{2}$. -/
theorem littleGrothendieckConstant_eq_pi_div_two :
    littleGrothendieckConstant = Real.pi / 2 :=
  le_antisymm littleGrothendieckConstant_le_pi_div_two pi_div_two_le_littleGrothendieckConstant

/-- The real Grothendieck constant satisfies $\frac{\pi}{2} \le K_G$. -/
theorem pi_div_two_le_grothendieckConstant :
    Real.pi / 2 ≤ grothendieckConstant :=
  pi_div_two_le_littleGrothendieckConstant.trans littleGrothendieckConstant_le_grothendieckConstant

end CslibFrontier.Grothendieck
