module
-- upstream: candidate

public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.MutualInformation
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.Entropy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Finset.Powerset
import Mathlib.GroupTheory.Perm.Fin

/-!
# Hellinger Cut-Paste Inequality and Jensen–Shannon Bound

This module establishes two fundamental inequalities relating Hellinger distance and information
theory for discrete probability distributions (`PMF`):

1. **Jensen–Shannon vs. squared Hellinger inequality**: For any two discrete distributions `p` and
   `q` on a finite type, the squared Hellinger distance `h²(p, q)` is at most the mutual information
   `I(W; Y)` (in bits) when `W ~ Unif(Bool)` and `Y | W` is drawn from `p` or `q`
.
2. **Jayram's Hellinger cut-paste inequality**: For any family of discrete distributions
   `{P b : b ∈ {0, 1}^m}` satisfying the cut-paste property on squared Hellinger distance,
   `h²(P 0, P 1) ≤ 4 * ∑ i, h²(P 0, P eᵢ)`
.

All proofs are self-contained under standard Lean axioms.

## Main definitions

* `CslibFrontier.Probability.Hellinger.jensenShannonBits`: the Jensen–Shannon divergence in bits
  between two finite distributions, defined as `I(W; Y)` for `W ~ Unif(Bool)`.
* `CslibFrontier.Probability.Hellinger.IsCutPaste`: the cut-paste property for a family of
  distributions indexed by `{0, 1}^m`.

## Main results

* `CslibFrontier.Probability.Hellinger.hellingerSq_le_jensenShannonBits`:
  `h²(p, q) ≤ jensenShannonBits p q`.
* `CslibFrontier.Probability.Hellinger.hellingerSq_le_four_mul_sum_basis`:
  Jayram's cut-paste inequality `h²(P 0, P 1) ≤ 4 * ∑ i, h²(P 0, P eᵢ)`.
-/

public section

namespace CslibFrontier.Probability.Hellinger

open Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal

variable {α : Type*}

/-! ### Jensen–Shannon divergence vs. squared Hellinger distance -/

/-- The Jensen–Shannon divergence (in bits) between two discrete distributions `p` and `q`,
defined as the mutual information `I(W; Y)` where `W ~ Unif(Bool)` and `Y` is drawn from `p`
when `W = false` and from `q` when `W = true`. -/
@[expose]
noncomputable def jensenShannonBits [Finite α] (p q : PMF α) : ℝ :=
  mutualInfo ((PMF.uniformOfFintype Bool).bind fun b => (if b then q else p).map (b, ·))

private lemma js_aux_nonneg_on_Icc_half (x₀ : ℝ) (hx₀_pos : 0 < x₀) (hx₀_le : x₀ ≤ 1 / 2)
    (hx₀_eq : 2 * Real.sqrt (x₀ * (1 - x₀)) = Real.log 2) :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      0 ≤ x * Real.log x + (1 - x) * Real.log (1 - x) +
        2 * Real.log 2 * Real.sqrt (x * (1 - x)) := by
  let h : ℝ → ℝ := fun x =>
    x * Real.log x + (1 - x) * Real.log (1 - x) + 2 * Real.log 2 * Real.sqrt (x * (1 - x))
  let g : ℝ → ℝ := fun x =>
    Real.log x - Real.log (1 - x) + Real.log 2 * ((1 - 2 * x) / Real.sqrt (x * (1 - x)))
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt h (g x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hprod : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    have hd1 : HasDerivAt (fun t => t * Real.log t) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).fun_mul (Real.hasDerivAt_log hx0)
      simpa [mul_inv_cancel₀ hx0, add_comm] using h
    have hd2 : HasDerivAt (fun t => (1 - t) * Real.log (1 - t)) (-Real.log (1 - x) - 1) x := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
      have hlog : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - x)⁻¹) x := by
        simpa [div_eq_mul_inv] using hsub.log hx1
      convert hsub.fun_mul hlog using 1
      field_simp [hx1]
      ring
    have hd3 : HasDerivAt (fun t => 2 * Real.log 2 * Real.sqrt (t * (1 - t)))
        (Real.log 2 * ((1 - 2 * x) / Real.sqrt (x * (1 - x)))) x := by
      have hp : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * x) x := by
        have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
        have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
          simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub hid
        convert hid.fun_mul hsub using 1
        ring
      have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (t * (1 - t)))
          (1 / (2 * Real.sqrt (x * (1 - x))) * (1 - 2 * x)) x :=
        (Real.hasDerivAt_sqrt hprod.ne').comp x hp
      convert hsq.const_mul (2 * Real.log 2) using 1
      field_simp [Real.sqrt_ne_zero'.mpr hprod]
    convert (hd1.fun_add hd2).fun_add hd3 using 1
    simp only [g]
    ring
  have hg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g ((2 * Real.sqrt (x * (1 - x)) - Real.log 2) /
        (2 * (x * (1 - x)) * Real.sqrt (x * (1 - x)))) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hprod : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    have hsq_ne : Real.sqrt (x * (1 - x)) ≠ 0 := Real.sqrt_ne_zero'.mpr hprod
    have h1 : HasDerivAt (fun t => Real.log t) x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun t => Real.log (1 - t)) (-(1 - x)⁻¹) x := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
      simpa [div_eq_mul_inv] using hsub.log hx1
    have h3 : HasDerivAt (fun t => (1 - 2 * t) / Real.sqrt (t * (1 - t)))
        (-1 / (2 * (x * (1 - x)) * Real.sqrt (x * (1 - x)))) x := by
      have hnum : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub ((hasDerivAt_id x).const_mul 2)
      have hp : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * x) x := by
        have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
        have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
          simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub hid
        convert hid.fun_mul hsub using 1
        ring
      have hden : HasDerivAt (fun t : ℝ => Real.sqrt (t * (1 - t)))
          (1 / (2 * Real.sqrt (x * (1 - x))) * (1 - 2 * x)) x :=
        (Real.hasDerivAt_sqrt hprod.ne').comp x hp
      convert hnum.fun_div hden hsq_ne using 1
      have hsq2 : Real.sqrt (x * (1 - x)) ^ 2 = x * (1 - x) := Real.sq_sqrt hprod.le
      field_simp [hsq_ne]
      nlinarith [hsq2]
    convert (h1.fun_sub h2).fun_add (h3.const_mul (Real.log 2)) using 1
    have hsq2 : Real.sqrt (x * (1 - x)) ^ 2 = x * (1 - x) := Real.sq_sqrt hprod.le
    field_simp [hx0, hx1, hsq_ne]
    nlinarith [hsq2]
  have hprod_mono : StrictMonoOn (fun t : ℝ => t * (1 - t)) (Set.Icc 0 (1 / 2)) := by
    intro a ha b hb hab
    dsimp only
    nlinarith [ha.1, ha.2, hb.1, hb.2]
  have hcont_h : ContinuousOn h (Set.Icc 0 (1 / 2)) := by
    refine (((Real.continuous_mul_log.continuousOn).add
      ((Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).continuousOn)).add ?_)
    exact (continuous_const.mul
      (Real.continuous_sqrt.comp
        (continuous_id.mul (continuous_const.sub continuous_id)))).continuousOn
  have h_right : ∀ x ∈ Set.Icc x₀ (1 / 2), 0 ≤ h x := by
    have hg_mono : MonotoneOn g (Set.Icc x₀ (1 / 2)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc x₀ (1 / 2))
      · refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
        · exact Real.continuousOn_log.mono fun t ht => by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
        · exact (Real.continuousOn_log.comp (continuous_const.sub continuous_id).continuousOn
            (fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.2]))
        · refine ContinuousOn.mul continuousOn_const (ContinuousOn.div
            (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
            (Real.continuous_sqrt.comp
              (continuous_id.mul (continuous_const.sub continuous_id))).continuousOn ?_)
          intro t ht
          exact Real.sqrt_ne_zero'.mpr (mul_pos (by linarith [ht.1]) (by linarith [ht.2]))
      · intro x hx
        rw [interior_Icc] at hx
        exact (hg_deriv x ⟨by linarith [hx.1],
          by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        rw [(hg_deriv x hx').deriv]
        have hlt : x₀ * (1 - x₀) < x * (1 - x) :=
          hprod_mono ⟨hx₀_pos.le, hx₀_le⟩ ⟨by linarith [hx.1], hx.2.le⟩ hx.1
        have hsq : Real.sqrt (x₀ * (1 - x₀)) ≤ Real.sqrt (x * (1 - x)) := Real.sqrt_le_sqrt hlt.le
        have hpos : 0 < 2 * (x * (1 - x)) * Real.sqrt (x * (1 - x)) := by
          have hp : 0 < x * (1 - x) := mul_pos hx'.1 (by linarith [hx'.2])
          positivity
        exact div_nonneg (by linarith) hpos.le
    have hh_anti : AntitoneOn h (Set.Icc x₀ (1 / 2)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc x₀ (1 / 2))
      · exact hcont_h.mono (Set.Icc_subset_Icc hx₀_pos.le le_rfl)
      · intro x hx
        rw [interior_Icc] at hx
        exact (hderiv x ⟨by linarith [hx.1],
          by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        rw [(hderiv x hx').deriv]
        have hle : g x ≤ g (1 / 2) := hg_mono ⟨hx.1.le, hx.2.le⟩ ⟨hx₀_le, le_rfl⟩ hx.2.le
        have hg_half : g (1 / 2) = 0 := by norm_num [g]
        linarith
    intro x hx
    have hh_half : h (1 / 2) = 0 := by
      simp only [h]
      have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      have hsq : Real.sqrt ((1 / 2 : ℝ) * (1 / 2)) = 1 / 2 := by
        rw [← sq, Real.sqrt_sq (by norm_num)]
      rw [h12, hsq, Real.log_div one_ne_zero two_ne_zero, Real.log_one]
      ring
    linarith [hh_anti hx ⟨hx₀_le, le_rfl⟩ hx.2]
  have h_left : ∀ x ∈ Set.Icc (0 : ℝ) x₀, 0 ≤ h x := by
    have hconc : ConcaveOn ℝ (Set.Icc 0 x₀) h := by
      apply concaveOn_of_deriv2_nonpos (convex_Icc 0 x₀)
      · exact hcont_h.mono (Set.Icc_subset_Icc le_rfl hx₀_le)
      · intro x hx
        rw [interior_Icc] at hx
        exact (hderiv x ⟨hx.1, by linarith [hx.2]⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
        have hdeq : deriv h =ᶠ[nhds x] g := by
          filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with t ht
          exact (hderiv t ht).deriv
        exact (hdeq.hasDerivAt_iff.mpr (hg_deriv x hx')).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
        have hdeq : deriv h =ᶠ[nhds x] g := by
          filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with t ht
          exact (hderiv t ht).deriv
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
        rw [hdeq.deriv_eq, (hg_deriv x hx').deriv]
        have hlt : x * (1 - x) < x₀ * (1 - x₀) :=
          hprod_mono ⟨hx.1.le, by linarith [hx.2]⟩ ⟨hx₀_pos.le, hx₀_le⟩ hx.2
        have hsq : Real.sqrt (x * (1 - x)) ≤ Real.sqrt (x₀ * (1 - x₀)) := Real.sqrt_le_sqrt hlt.le
        have hpos : 0 < 2 * (x * (1 - x)) * Real.sqrt (x * (1 - x)) := by
          have hp : 0 < x * (1 - x) := mul_pos hx'.1 (by linarith [hx'.2])
          positivity
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    have hh0 : h 0 = 0 := by simp [h]
    have hhx₀ : 0 ≤ h x₀ := h_right x₀ ⟨le_rfl, hx₀_le⟩
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, hh0]
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
    have ht1 : 0 ≤ 1 - x / x₀ := by
      have : x / x₀ ≤ 1 := (div_le_one hx₀_pos).mpr hx.2
      linarith
    have ht2 : 0 ≤ x / x₀ := div_nonneg hx.1 hx₀_pos.le
    have hcomb := hconc.2 (Set.left_mem_Icc.mpr hx₀_pos.le) (Set.right_mem_Icc.mpr hx₀_pos.le)
      ht1 ht2 (by ring)
    have harg : (1 - x / x₀) • (0 : ℝ) + (x / x₀) • x₀ = x := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      exact div_mul_cancel₀ x hx₀_pos.ne'
    rw [harg, smul_eq_mul, smul_eq_mul, hh0, mul_zero, zero_add] at hcomb
    exact le_trans (mul_nonneg ht2 hhx₀) hcomb
  intro x hx
  rcases le_total x x₀ with hle | hge
  · exact h_left x ⟨hx.1, hle⟩
  · exact h_right x ⟨hge, hx.2⟩

private lemma log_two_mul_sqrt_sub_sq_le_js_term {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.log 2 * (Real.sqrt u - Real.sqrt v) ^ 2 ≤
      u * Real.log (2 * u / (u + v)) + v * Real.log (2 * v / (u + v)) := by
  by_cases huv : u + v = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    simp [hu0, hv0]
  have huv_pos : 0 < u + v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm huv)
  let x := u / (u + v)
  have hx0 : 0 ≤ x := div_nonneg hu huv_pos.le
  have hx1 : x ≤ 1 := (div_le_one huv_pos).mpr (by linarith)
  have h1x : 1 - x = v / (u + v) := by
    simp only [x]
    field_simp [huv_pos.ne']
    ring
  have h_exists_x₀ : ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1 / 2 ∧
      2 * Real.sqrt (x₀ * (1 - x₀)) = Real.log 2 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_lt : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 3
      norm_num [Finset.sum_range_succ] at h
      linarith
    let c := (Real.log 2 / 2) ^ 2
    have hc_pos : 0 < c := by positivity
    have hc_lt : c < 1 / 4 := by
      dsimp only [c]
      nlinarith [hlog2_pos, hlog2_lt]
    let x₀ := (1 - Real.sqrt (1 - 4 * c)) / 2
    have hsq_pos : 0 < Real.sqrt (1 - 4 * c) := Real.sqrt_pos.mpr (by linarith)
    have hsq_lt : Real.sqrt (1 - 4 * c) < 1 := by
      rw [Real.sqrt_lt' one_pos]
      linarith
    refine ⟨x₀, by dsimp only [x₀]; linarith, by dsimp only [x₀]; linarith, ?_⟩
    have hprod : x₀ * (1 - x₀) = c := by
      have hsq2 : Real.sqrt (1 - 4 * c) ^ 2 = 1 - 4 * c := Real.sq_sqrt (by linarith)
      simp only [x₀]
      nlinarith [hsq2]
    rw [hprod, Real.sqrt_sq (by positivity)]
    ring
  obtain ⟨x₀, hx₀_pos, hx₀_le, hx₀_eq⟩ := h_exists_x₀
  have hmain : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ t * Real.log t + (1 - t) * Real.log (1 - t) +
        2 * Real.log 2 * Real.sqrt (t * (1 - t)) := by
    intro t ht
    rcases le_total t (1 / 2) with hle | hge
    · exact js_aux_nonneg_on_Icc_half x₀ hx₀_pos hx₀_le hx₀_eq t ⟨ht.1, hle⟩
    · have h := js_aux_nonneg_on_Icc_half x₀ hx₀_pos hx₀_le hx₀_eq (1 - t)
        ⟨by linarith [ht.2], by linarith⟩
      have hsub : 1 - (1 - t) = t := by ring
      rw [hsub, mul_comm (1 - t) t] at h
      linarith
  have hunit := hmain x ⟨hx0, hx1⟩
  have hlog_eq :
      u * Real.log (2 * u / (u + v)) + v * Real.log (2 * v / (u + v)) -
        Real.log 2 * (Real.sqrt u - Real.sqrt v) ^ 2 =
      (u + v) * (x * Real.log x + (1 - x) * Real.log (1 - x) +
        2 * Real.log 2 * Real.sqrt (x * (1 - x))) := by
    have hsqrt_uv : (Real.sqrt u - Real.sqrt v) ^ 2 = u + v - 2 * Real.sqrt (u * v) := by
      rw [Real.sqrt_mul hu]
      nlinarith [Real.mul_self_sqrt hu, Real.mul_self_sqrt hv]
    have hsqrt_x : Real.sqrt (x * (1 - x)) = Real.sqrt (u * v) / (u + v) := by
      rw [h1x]
      have : u / (u + v) * (v / (u + v)) = u * v / (u + v) ^ 2 := by
        rw [div_mul_div_comm, sq]
      rw [this, Real.sqrt_div (mul_nonneg hu hv), Real.sqrt_sq huv_pos.le]
    have htx : u * Real.log (2 * u / (u + v)) =
        (u + v) * (x * Real.log 2 + x * Real.log x) := by
      by_cases hu0 : u = 0
      · simp [hu0, x]
      have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hx_pos : 0 < x := div_pos hu_pos huv_pos
      have h2x : 2 * u / (u + v) = 2 * x := by simp only [x]; ring
      rw [h2x, Real.log_mul two_ne_zero hx_pos.ne']
      simp only [x]
      field_simp [huv_pos.ne']
    have htv : v * Real.log (2 * v / (u + v)) =
        (u + v) * ((1 - x) * Real.log 2 + (1 - x) * Real.log (1 - x)) := by
      by_cases hv0 : v = 0
      · simp [hv0, h1x]
      have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
      have h1x_pos : 0 < 1 - x := by rw [h1x]; exact div_pos hv_pos huv_pos
      have h2v : 2 * v / (u + v) = 2 * (1 - x) := by rw [h1x]; ring
      rw [h2v, Real.log_mul two_ne_zero h1x_pos.ne']
      rw [h1x]
      field_simp [huv_pos.ne']
    rw [htx, htv, hsqrt_uv, hsqrt_x]
    field_simp [huv_pos.ne']
    ring
  linarith [mul_nonneg huv_pos.le hunit]

/-- **Jensen–Shannon vs. squared Hellinger inequality**
: for any two distributions `p` and `q` on a finite type,
`h²(p, q) ≤ jensenShannonBits p q`.
-/
theorem hellingerSq_le_jensenShannonBits [Finite α] (p q : PMF α) :
    hellingerSq p q ≤ jensenShannonBits p q := by
  classical
  let _ := Fintype.ofFinite α
  let joint : PMF (Bool × α) :=
    (PMF.uniformOfFintype Bool).bind fun b => (if b then q else p).map (b, ·)
  let m : PMF α := joint.map Prod.snd
  have hm_apply (a : α) : (m a).toReal = ((p a).toReal + (q a).toReal) / 2 := by
    have h1 : m = (PMF.uniformOfFintype Bool).bind (fun b => if b then q else p) := by
      simp only [m, joint, PMF.map_bind, PMF.map_comp]
      exact congrArg (PMF.uniformOfFintype Bool).bind
        (funext fun b => by exact PMF.map_id (if b then q else p))
    rw [h1, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ↓reduceIte,
      Bool.false_eq_true]
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
    ring
  have hjs_eq : jensenShannonBits p q =
      (∑ a : α, ((p a).toReal * Real.log (2 * (p a).toReal / ((p a).toReal + (q a).toReal)) +
        (q a).toReal * Real.log (2 * (q a).toReal / ((p a).toReal + (q a).toReal)))) /
        (2 * Real.log 2) := by
    have hjs_def : jensenShannonBits p q = entropy m - (entropy p + entropy q) / 2 := by
      change mutualInfo joint = _
      rw [mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy,
        conditionalEntropy_bind_pair (PMF.uniformOfFintype Bool) (fun b => if b then q else p),
        Fintype.sum_bool]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ↓reduceIte,
        Bool.false_eq_true, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      change entropy m - _ = _
      ring
    rw [hjs_def, entropy_eq_sum, entropy_eq_sum, entropy_eq_sum]
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlog2]
    rw [← Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib,
      show ∑ a : α, (Real.negMulLog (m a).toReal * 2 -
        (Real.negMulLog (p a).toReal + Real.negMulLog (q a).toReal)) =
        ∑ a : α, ((p a).toReal * Real.log (2 * (p a).toReal / ((p a).toReal + (q a).toReal)) +
          (q a).toReal * Real.log (2 * (q a).toReal / ((p a).toReal + (q a).toReal))) by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hm_apply a]
        simp only [Real.negMulLog]
        have hp0 : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
        have hq0 : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
        by_cases hpa : (p a).toReal = 0
        · by_cases hqa : (q a).toReal = 0
          · simp [hpa, hqa]
          · have hqpos : 0 < (q a).toReal := lt_of_le_of_ne hq0 (Ne.symm hqa)
            simp only [hpa, zero_add, zero_mul, neg_zero,
              mul_div_cancel_right₀ _ hqpos.ne', Real.log_div hqpos.ne' two_ne_zero]
            ring
        · by_cases hqa : (q a).toReal = 0
          · have hppos : 0 < (p a).toReal := lt_of_le_of_ne hp0 (Ne.symm hpa)
            simp only [hqa, add_zero, zero_mul, neg_zero,
              mul_div_cancel_right₀ _ hppos.ne', Real.log_div hppos.ne' two_ne_zero]
            ring
          · have hppos : 0 < (p a).toReal := lt_of_le_of_ne hp0 (Ne.symm hpa)
            have hqpos : 0 < (q a).toReal := lt_of_le_of_ne hq0 (Ne.symm hqa)
            have hpq : 0 < (p a).toReal + (q a).toReal := add_pos hppos hqpos
            rw [Real.log_div (mul_pos two_pos hppos).ne' hpq.ne',
              Real.log_div (mul_pos two_pos hqpos).ne' hpq.ne',
              Real.log_div hpq.ne' two_ne_zero,
              Real.log_mul two_ne_zero hppos.ne',
              Real.log_mul two_ne_zero hqpos.ne']
            ring]
  rw [hjs_eq, hellingerSq_eq_sum]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_div_iff₀ two_pos (by positivity)]
  have hsum :
      Real.log 2 * ∑ a : α, (Real.sqrt (p a).toReal - Real.sqrt (q a).toReal) ^ 2 ≤
        ∑ a : α, ((p a).toReal * Real.log (2 * (p a).toReal / ((p a).toReal + (q a).toReal)) +
          (q a).toReal * Real.log (2 * (q a).toReal / ((p a).toReal + (q a).toReal))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ =>
      log_two_mul_sqrt_sub_sq_le_js_term ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  linarith

/-! ### Jayram's Hellinger cut-paste inequality -/

/-- A family of distributions `{P b : b ∈ {0, 1}^m}` satisfies the **cut-paste property** for
squared Hellinger distance if `h²(P a, P b) = h²(P c, P d)` whenever `{a i, b i} = {c i, d i}`
as multisets for every coordinate `i`. -/
@[expose]
def IsCutPaste {m : ℕ} (P : (Fin m → Bool) → PMF α) : Prop :=
  ∀ a b c d : Fin m → Bool,
    (∀ i : Fin m, ({a i, b i} : Multiset Bool) = {c i, d i}) →
      hellingerSq (P a) (P b) = hellingerSq (P c) (P d)

/-- Indicator vector of a finite subset `S ⊆ Fin m`. -/
private def indicatorVec {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool :=
  fun i => decide (i ∈ S)

private lemma isCutPaste_disjoint_union {m : ℕ} {P : (Fin m → Bool) → PMF α}
    (hP : IsCutPaste P) {S T : Finset (Fin m)} (hdisj : Disjoint S T) :
    hellingerSq (P (indicatorVec S)) (P (indicatorVec T)) =
      hellingerSq (P (fun _ => false)) (P (indicatorVec (S ∪ T))) := by
  refine hP _ _ _ _ fun i => ?_
  simp only [indicatorVec, Finset.mem_union]
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.mp hdisj hS
    simp only [hS, hT, decide_true, decide_false, true_or]
    exact Multiset.pair_comm true false
  · by_cases hT : i ∈ T
    · simp [hS, hT]
    · simp [hS, hT]

private lemma sum_norm_sub_sq_le {M : ℕ} [Fintype α] (w : Fin M → EuclideanSpace ℝ α) :
    ∑ a : Fin M, ∑ b : Fin M, ‖w a - w b‖ ^ 2 ≤ 2 * (M : ℝ) * ∑ a : Fin M, ‖w a‖ ^ 2 := by
  have hexp (a b : Fin M) :
      ‖w a - w b‖ ^ 2 = ‖w a‖ ^ 2 - 2 * @inner ℝ _ _ (w a) (w b) + ‖w b‖ ^ 2 := by
    rw [norm_sub_sq_real]
  have hinner : 0 ≤ ∑ a : Fin M, ∑ b : Fin M, @inner ℝ _ _ (w a) (w b) := by
    have hnorm : ‖∑ a : Fin M, w a‖ ^ 2 = ∑ a : Fin M, ∑ b : Fin M, @inner ℝ _ _ (w a) (w b) := by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      exact Finset.sum_congr rfl fun a _ => inner_sum _ _ _
    rw [← hnorm]
    exact sq_nonneg _
  have hsum :
      ∑ a : Fin M, ∑ b : Fin M, ‖w a - w b‖ ^ 2 =
        2 * (M : ℝ) * (∑ a : Fin M, ‖w a‖ ^ 2) -
          2 * ∑ a : Fin M, ∑ b : Fin M, @inner ℝ _ _ (w a) (w b) := by
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  linarith

private lemma prod_two_pow_div_sub_one_le_four (L : ℕ) :
    ∏ k ∈ Finset.Icc 1 L, ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) ≤ 4 := by
  have hinv (L : ℕ) (hL : 1 ≤ L) :
      (1 / 2 : ℝ) + (2 : ℝ)⁻¹ ^ L ≤ ∏ k ∈ Finset.Icc 2 L, (1 - (2 : ℝ)⁻¹ ^ k) := by
    induction L with
    | zero => omega
    | succ n ih =>
      by_cases hn : n = 0
      · subst hn
        norm_num
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hIcc : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.prod_insert (by simp)]
      have hih := ih hn1
      have hfac_nonneg : 0 ≤ 1 - (2 : ℝ)⁻¹ ^ (n + 1) := by
        have : (2 : ℝ)⁻¹ ^ (n + 1) ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
        linarith
      have hmul : ((1 / 2 : ℝ) + (2 : ℝ)⁻¹ ^ n) * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ≤
          (1 - (2 : ℝ)⁻¹ ^ (n + 1)) * ∏ k ∈ Finset.Icc 2 n, (1 - (2 : ℝ)⁻¹ ^ k) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hih hfac_nonneg
      refine le_trans ?_ hmul
      have hpow : (2 : ℝ)⁻¹ ^ n = 2 * (2 : ℝ)⁻¹ ^ (n + 1) := by rw [pow_succ]; ring
      have hsq : (2 : ℝ)⁻¹ ^ (n + 1) ≤ (1 / 4 : ℝ) := by
        calc (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ ^ 2 :=
              pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
          _ = 1 / 4 := by norm_num
      have hpos : 0 ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
      rw [hpow]
      nlinarith
  by_cases hL : L = 0
  · subst hL; norm_num
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero hL
  have hIcc : Finset.Icc 1 L = insert 1 (Finset.Icc 2 L) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.prod_insert (by simp)]
  have hterm (k : ℕ) (hk : 1 ≤ k) :
      (2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1) = (1 - (2 : ℝ)⁻¹ ^ k)⁻¹ := by
    have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hsub : (2 : ℝ) ^ k - 1 ≠ 0 := by
      have : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
      linarith
    rw [inv_pow]
    field_simp [h2, hsub]
  have hprod_eq :
      ∏ k ∈ Finset.Icc 2 L, ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) =
        (∏ k ∈ Finset.Icc 2 L, (1 - (2 : ℝ)⁻¹ ^ k))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k hk => hterm k (by linarith [(Finset.mem_Icc.mp hk).1])
  rw [hterm 1 le_rfl, hprod_eq]
  have hge : (1 / 2 : ℝ) ≤ ∏ k ∈ Finset.Icc 2 L, (1 - (2 : ℝ)⁻¹ ^ k) := by
    have := hinv L hL1
    have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ L := by positivity
    linarith
  have hinv_le : (∏ k ∈ Finset.Icc 2 L, (1 - (2 : ℝ)⁻¹ ^ k))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    linarith
  norm_num
  linarith

private lemma perm_sum_block {n r : ℕ} (hr : r ≤ n) (B : Equiv.Perm (Fin n) → Finset (Fin n))
    (hcard : ∀ π, (B π).card = r)
    (hequiv : ∀ (σ π : Equiv.Perm (Fin n)), B (σ * π) = (B π).map σ.toEmbedding)
    (f : Finset (Fin n) → ℝ) :
    ((n.choose r : ℝ) / (Nat.factorial n : ℝ)) * ∑ π : Equiv.Perm (Fin n), f (B π) =
      ∑ S ∈ Finset.powersetCard r (Finset.univ : Finset (Fin n)), f S := by
  classical
  let Pset := Finset.powersetCard r (Finset.univ : Finset (Fin n))
  have hmem : ∀ π, B π ∈ Pset :=
    fun π => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard π⟩
  have hfib_eq : ∀ S₁ ∈ Pset, ∀ S₂ ∈ Pset,
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) => B π = S₁).card =
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) => B π = S₂).card := by
    intro S₁ hS₁ S₂ hS₂
    have hc1 : S₁.card = r := (Finset.mem_powersetCard.mp hS₁).2
    have hc2 : S₂.card = r := (Finset.mem_powersetCard.mp hS₂).2
    have hcard_eq : Fintype.card S₁ = Fintype.card S₂ := by simp [hc1, hc2]
    let eS : S₁ ≃ S₂ := Fintype.equivOfCardEq hcard_eq
    let σ : Equiv.Perm (Fin n) := Equiv.extendSubtype eS
    have hσ_map : S₁.map σ.toEmbedding = S₂ := by
      ext x
      simp only [Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have := Equiv.extendSubtype_apply_of_mem eS y hy
        exact (this ▸ (eS ⟨y, hy⟩).2)
      · intro hx
        refine ⟨(eS.symm ⟨x, hx⟩).1, (eS.symm ⟨x, hx⟩).2, ?_⟩
        have := Equiv.extendSubtype_apply_of_mem eS (eS.symm ⟨x, hx⟩).1 (eS.symm ⟨x, hx⟩).2
        simpa using this
    refine Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      rw [hequiv, hπ, hσ_map]
    · intro π₁ _ π₂ _ h
      exact mul_left_cancel h
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      refine ⟨σ⁻¹ * π, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : B (σ * (σ⁻¹ * π)) = S₂ := by simpa using hπ
      rw [hequiv] at h1
      have h2 := congrArg (fun S => S.map σ⁻¹.toEmbedding) h1
      have h3 : ((B (σ⁻¹ * π)).map σ.toEmbedding).map σ⁻¹.toEmbedding = B (σ⁻¹ * π) := by
        ext x; simp [Equiv.Perm.inv_def]
      have h4 : S₂.map σ⁻¹.toEmbedding = S₁ := by
        rw [← hσ_map]
        ext x; simp [Equiv.Perm.inv_def]
      rw [h3, h4] at h2
      exact h2
  have hPset_ne : Pset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 : Pset.card = 0 := by rw [hemp]; rfl
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h0
    exact Nat.choose_ne_zero hr h0
  obtain ⟨S₀, hS₀⟩ := hPset_ne
  let c := (Finset.univ.filter fun π : Equiv.Perm (Fin n) => B π = S₀).card
  have hsum_eq (g : Finset (Fin n) → ℝ) :
      ∑ π : Equiv.Perm (Fin n), g (B π) = (c : ℝ) * ∑ S ∈ Pset, g S := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun π _ => hmem π), Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.sum_congr rfl fun π hπ => by rw [(Finset.mem_filter.mp hπ).2],
      Finset.sum_const, nsmul_eq_mul, hfib_eq S hS S₀ hS₀]
  have hconst := hsum_eq (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Finset.card_powersetCard, nsmul_eq_mul, mul_one, Pset] at hconst
  have hfact_ne : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hc_eq : (c : ℝ) * (n.choose r : ℝ) = (Nat.factorial n : ℝ) := by
    simpa [mul_comm] using hconst.symm
  rw [hsum_eq f]
  have hch_ne : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  have hc_val : (c : ℝ) = (Nat.factorial n : ℝ) / (n.choose r : ℝ) := by
    field_simp [hch_ne]
    linarith
  rw [hc_val]
  field_simp [hfact_ne, hch_ne]
  rfl

private lemma hellingerSq_pow_two_step [Finite α] {L j : ℕ} (hj : j < L)
    {P : (Fin (2 ^ L) → Bool) → PMF α} (hP : IsCutPaste P) :
    let m : ℕ := 2 ^ L
    let r : ℕ := 2 ^ j
    let M : ℕ := 2 ^ (L - j)
    let A := fun t =>
      (∑ S ∈ Finset.powersetCard t (Finset.univ : Finset (Fin m)),
        hellingerSq (P (fun _ => false)) (P (indicatorVec S))) / (m.choose t : ℝ)
    A (2 * r) ≤ (2 * (M : ℝ) / ((M : ℝ) - 1)) * A r := by
  intro m r M A
  classical
  let _ := Fintype.ofFinite α
  have hM_ge2 : 2 ≤ M := by
    have : 1 ≤ L - j := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (L - j) := Nat.pow_le_pow_right (by norm_num) this
  have hr_mul_M : M * r = m := by
    change 2 ^ (L - j) * 2 ^ j = 2 ^ L
    rw [← pow_add, Nat.sub_add_cancel hj.le]
  have hr_le : r ≤ m := by
    calc r = 1 * r := (one_mul r).symm
      _ ≤ M * r := Nat.mul_le_mul_right r (by omega)
      _ = m := hr_mul_M
  have h2r_le : 2 * r ≤ m := by
    calc 2 * r ≤ M * r := Nat.mul_le_mul_right r hM_ge2
      _ = m := hr_mul_M
  let block : Fin M → Equiv.Perm (Fin m) → Finset (Fin m) := fun a π =>
    (Finset.univ : Finset (Fin r)).map
      ⟨fun t => π ⟨a.1 * r + t.1, by
        have ha : a.1 + 1 ≤ M := a.2
        have : a.1 * r + t.1 < (a.1 + 1) * r := by rw [add_mul, one_mul]; omega
        calc a.1 * r + t.1 < (a.1 + 1) * r := this
          _ ≤ M * r := Nat.mul_le_mul_right r ha
          _ = m := hr_mul_M⟩,
      fun t₁ t₂ h => by
        have h' := Fin.mk.inj (π.injective h)
        ext; omega⟩
  have hblock_card (a : Fin M) (π : Equiv.Perm (Fin m)) : (block a π).card = r := by
    simp [block]
  have hblock_disj {a b : Fin M} (hab : a ≠ b) (π : Equiv.Perm (Fin m)) :
      Disjoint (block a π) (block b π) := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    simp only [block, Finset.mem_map, Finset.mem_univ, true_and] at hxa hxb
    obtain ⟨t₁, rfl⟩ := hxa
    obtain ⟨t₂, h2⟩ := hxb
    have h3 := Fin.mk.inj (π.injective h2)
    have hdiv : a.1 = b.1 := by
      have : (a.1 * r + t₁.1) / r = (b.1 * r + t₂.1) / r := congrArg (· / r) h3.symm
      have hrpos : 0 < r := by positivity
      rw [mul_comm a.1 r, mul_comm b.1 r, Nat.mul_add_div hrpos, Nat.mul_add_div hrpos,
        Nat.div_eq_of_lt t₁.2, Nat.div_eq_of_lt t₂.2] at this
      simpa using this
    exact hab (Fin.ext hdiv)
  have hblock_equiv (a : Fin M) (σ π : Equiv.Perm (Fin m)) :
      block a (σ * π) = (block a π).map σ.toEmbedding := by
    simp only [block, Finset.map_map]
    congr 1
  have hunion_equiv (a b : Fin M) (σ π : Equiv.Perm (Fin m)) :
      block a (σ * π) ∪ block b (σ * π) = (block a π ∪ block b π).map σ.toEmbedding := by
    rw [hblock_equiv, hblock_equiv, Finset.map_union]
  let u : Finset (Fin m) → EuclideanSpace ℝ α := fun S =>
    WithLp.toLp 2 fun x =>
      Real.sqrt ((P (indicatorVec S) x).toReal) - Real.sqrt ((P (fun _ => false) x).toReal)
  have hu_norm_sq (S : Finset (Fin m)) :
      ‖u S‖ ^ 2 = 2 * hellingerSq (P (fun _ => false)) (P (indicatorVec S)) := by
    rw [EuclideanSpace.real_norm_sq_eq, hellingerSq_eq_sum]
    have : ∑ x : α, (u S x) ^ 2 =
        ∑ x : α, (Real.sqrt ((P (fun _ => false) x).toReal) -
          Real.sqrt ((P (indicatorVec S) x).toReal)) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by simp only [u]; ring
    rw [this]
    ring
  have hu_sub_norm_sq {S T : Finset (Fin m)} (hdisj : Disjoint S T) :
      ‖u S - u T‖ ^ 2 = 2 * hellingerSq (P (fun _ => false)) (P (indicatorVec (S ∪ T))) := by
    rw [EuclideanSpace.real_norm_sq_eq, ← isCutPaste_disjoint_union hP hdisj, hellingerSq_eq_sum]
    have : ∑ x : α, ((u S - u T) x) ^ 2 =
        ∑ x : α, (Real.sqrt ((P (indicatorVec S) x).toReal) -
          Real.sqrt ((P (indicatorVec T) x).toReal)) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by simp only [PiLp.sub_apply, u]; ring
    rw [this]
    ring
  have hperm_ineq (π : Equiv.Perm (Fin m)) :
      ∑ a : Fin M, ∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≠ a),
        hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) ≤
      2 * (M : ℝ) * ∑ a : Fin M,
        hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) := by
    have hvec := sum_norm_sub_sq_le (fun a : Fin M => u (block a π))
    have hlhs : ∑ a : Fin M, ∑ b : Fin M, ‖u (block a π) - u (block b π)‖ ^ 2 =
        2 * ∑ a : Fin M, ∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≠ a),
          hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => b ≠ a)]
      have hdiag : ∑ b ∈ Finset.univ.filter (fun b : Fin M => ¬b ≠ a),
          ‖u (block a π) - u (block b π)‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun b hb => by
          have : b = a := not_not.mp (Finset.mem_filter.mp hb).2
          simp [this]
      rw [hdiag, add_zero]
      exact Finset.sum_congr rfl fun b hb =>
        hu_sub_norm_sq (hblock_disj (Finset.mem_filter.mp hb).2.symm π)
    have hrhs : 2 * (M : ℝ) * ∑ a : Fin M, ‖u (block a π)‖ ^ 2 =
        4 * (M : ℝ) * ∑ a : Fin M,
          hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) := by
      simp_rw [hu_norm_sq, ← Finset.mul_sum]
      ring
    linarith
  have hsum_perm :
      ∑ a : Fin M, ∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≠ a),
        ∑ π : Equiv.Perm (Fin m),
          hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) ≤
      2 * (M : ℝ) * ∑ a : Fin M, ∑ π : Equiv.Perm (Fin m),
        hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) := by
    calc _ = ∑ π : Equiv.Perm (Fin m),
            ∑ a : Fin M, ∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≠ a),
              hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ ≤ ∑ π : Equiv.Perm (Fin m),
            2 * (M : ℝ) * ∑ a : Fin M,
              hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) :=
          Finset.sum_le_sum fun π _ => hperm_ineq π
      _ = 2 * (M : ℝ) * ∑ a : Fin M, ∑ π : Equiv.Perm (Fin m),
            hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
  have hfact_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hch_r_pos : (0 : ℝ) < (m.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hr_le
  have hch_2r_pos : (0 : ℝ) < (m.choose (2 * r) : ℝ) := by exact_mod_cast Nat.choose_pos h2r_le
  have hlhs_eval (a : Fin M) (b : Fin M) (hab : b ≠ a) :
      ∑ π : Equiv.Perm (Fin m),
        hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) =
      (Nat.factorial m : ℝ) * A (2 * r) := by
    have h := perm_sum_block h2r_le (fun π => block a π ∪ block b π)
      (fun π => by
        rw [Finset.card_union_of_disjoint (hblock_disj hab.symm π), hblock_card, hblock_card]
        ring)
      (hunion_equiv a b)
      (fun S => hellingerSq (P (fun _ => false)) (P (indicatorVec S)))
    simp only [A]
    have h1 : (m.choose (2 * r) : ℝ) ≠ 0 := hch_2r_pos.ne'
    have h2 : (Nat.factorial m : ℝ) ≠ 0 := hfact_pos.ne'
    rw [← h]
    field_simp [h1, h2]
  have hrhs_eval (a : Fin M) :
      ∑ π : Equiv.Perm (Fin m),
        hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) =
      (Nat.factorial m : ℝ) * A r := by
    have h := perm_sum_block hr_le (block a) (hblock_card a) (hblock_equiv a)
      (fun S => hellingerSq (P (fun _ => false)) (P (indicatorVec S)))
    simp only [A]
    have h1 : (m.choose r : ℝ) ≠ 0 := hch_r_pos.ne'
    have h2 : (Nat.factorial m : ℝ) ≠ 0 := hfact_pos.ne'
    rw [← h]
    field_simp [h1, h2]
  have hsum_lhs :
      ∑ a : Fin M, ∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≠ a),
        ∑ π : Equiv.Perm (Fin m),
          hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) =
      (M : ℝ) * ((M : ℝ) - 1) * (Nat.factorial m : ℝ) * A (2 * r) := by
    have hinner (a : Fin M) :
        ∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≠ a),
          ∑ π : Equiv.Perm (Fin m),
            hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π ∪ block b π))) =
        ((M : ℝ) - 1) * ((Nat.factorial m : ℝ) * A (2 * r)) := by
      have hcard_f : (Finset.univ.filter (fun b : Fin M => b ≠ a)).card = M - 1 := by
        rw [show Finset.univ.filter (fun b : Fin M => b ≠ a) = Finset.univ.erase a by
          ext b; simp [Finset.mem_erase]]
        simp
      rw [Finset.sum_congr rfl fun b hb => hlhs_eval a b (Finset.mem_filter.mp hb).2,
        Finset.sum_const, hcard_f, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one]
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum_rhs :
      2 * (M : ℝ) * ∑ a : Fin M, ∑ π : Equiv.Perm (Fin m),
        hellingerSq (P (fun _ => false)) (P (indicatorVec (block a π))) =
      2 * (M : ℝ) * (M : ℝ) * (Nat.factorial m : ℝ) * A r := by
    simp_rw [hrhs_eval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum_lhs, hsum_rhs] at hsum_perm
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hMm1_pos : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge2
    linarith
  have hfac_M : 0 < (M : ℝ) * ((M : ℝ) - 1) * (Nat.factorial m : ℝ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hMm1_pos]
  nlinarith

private lemma hellingerSq_le_four_mul_sum_basis_pow_two [Finite α] (L : ℕ)
    (P : (Fin (2 ^ L) → Bool) → PMF α) (hP : IsCutPaste P) :
    hellingerSq (P (fun _ => false)) (P (fun _ => true)) ≤
      4 * ∑ i : Fin (2 ^ L),
        hellingerSq (P (fun _ => false)) (P (fun j => decide (j = i))) := by
  classical
  let _ := Fintype.ofFinite α
  let m := 2 ^ L
  let A : ℕ → ℝ := fun t =>
    (∑ S ∈ Finset.powersetCard t (Finset.univ : Finset (Fin m)),
      hellingerSq (P (fun _ => false)) (P (indicatorVec S))) / (m.choose t : ℝ)
  have hA_nonneg (t : ℕ) : 0 ≤ A t :=
    div_nonneg (Finset.sum_nonneg fun _ _ => hellingerSq_nonneg _ _) (Nat.cast_nonneg _)
  have hstep : ∀ j ≤ L,
      A (2 ^ j) ≤ (∏ k ∈ Finset.Icc (L - j +
        1) L, (2 * (2 ^ k : ℝ) / ((2 ^ k : ℝ) - 1))) * A 1 := by
    intro j hj
    induction j with
    | zero =>
      simp only [pow_zero, Nat.sub_zero]
      have hIcc : Finset.Icc (L + 1) L = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hIcc, Finset.prod_empty, one_mul]
    | succ j ih =>
      have hjl : j < L := by omega
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
      have h1 := hellingerSq_pow_two_step hjl hP
      dsimp only at h1
      rw [Nat.cast_pow, Nat.cast_ofNat] at h1
      rw [hpow]
      have hM_nonneg : 0 ≤ 2 * (2 ^ (L - j) : ℝ) / ((2 ^ (L - j) : ℝ) - 1) := by
        have : (2 : ℝ) ≤ (2 : ℝ) ^ (L - j) := by
          calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
            _ ≤ (2 : ℝ) ^ (L - j) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact div_nonneg (by positivity) (by linarith)
      have h2 := le_trans h1 (mul_le_mul_of_nonneg_left (ih (by omega)) hM_nonneg)
      have hIcc : Finset.Icc (L - (j + 1) + 1) L = insert (L - j) (Finset.Icc (L - j + 1) L) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.prod_insert (by simp), mul_assoc]
      exact h2
  have htop := hstep L le_rfl
  rw [Nat.sub_self, zero_add] at htop
  have hprod_split :
      ∏ k ∈ Finset.Icc 1 L, (2 * (2 ^ k : ℝ) / ((2 ^ k : ℝ) - 1)) =
        (2 : ℝ) ^ L * ∏ k ∈ Finset.Icc 1 L, ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) := by
    have hmul : ∀ k ∈ Finset.Icc 1 L,
        2 * (2 ^ k : ℝ) / ((2 ^ k : ℝ) - 1) = (2 : ℝ) * ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) :=
      fun k _ => by ring
    rw [Finset.prod_congr rfl hmul, Finset.prod_mul_distrib, Finset.prod_const,
      Nat.card_Icc, Nat.add_sub_cancel]
  have hAm : A m = hellingerSq (P (fun _ => false)) (P (fun _ => true)) := by
    have hpu : Finset.powersetCard m (Finset.univ : Finset (Fin m)) = {Finset.univ} := by
      have hcard_u : (Finset.univ : Finset (Fin m)).card = m := by simp
      simpa [hcard_u] using Finset.powersetCard_self (Finset.univ : Finset (Fin m))
    dsimp only [A]
    rw [hpu, Finset.sum_singleton, Nat.choose_self, Nat.cast_one, div_one]
    congr 2
    ext i
    simp [indicatorVec]
  have hA1 : (2 : ℝ) ^ L * A 1 =
      ∑ i : Fin m, hellingerSq (P (fun _ => false)) (P (fun j => decide (j = i))) := by
    simp only [A, m, Nat.choose_one_right, Finset.powersetCard_one, Finset.sum_map,
      Function.Embedding.coeFn_mk]
    have h2L : ((2 ^ L : ℕ) : ℝ) ≠ 0 := by positivity
    have hcast : ((2 ^ L : ℕ) : ℝ) = (2 : ℝ) ^ L := by push_cast; rfl
    rw [hcast, mul_div_cancel₀ _ (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp only [indicatorVec, Finset.mem_singleton]
  have hmul_comm :
      (2 : ℝ) ^ L * (∏ k ∈ Finset.Icc 1 L, ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1))) * A 1 =
        (∏ k ∈ Finset.Icc 1 L, ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1))) * ((2 : ℝ) ^ L * A 1) := by
    ring
  rw [hAm, hprod_split, hmul_comm, hA1] at htop
  calc hellingerSq (P (fun _ => false)) (P (fun _ => true))
      ≤ (∏ k ∈ Finset.Icc 1 L, ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1))) *
          ∑ i : Fin m, hellingerSq (P (fun _ => false)) (P (fun j => decide (j = i))) := htop
    _ ≤ 4 * ∑ i : Fin m, hellingerSq (P (fun _ => false)) (P (fun j => decide (j = i))) := by
        exact mul_le_mul_of_nonneg_right (prod_two_pow_div_sub_one_le_four L)
          (Finset.sum_nonneg fun _ _ => hellingerSq_nonneg _ _)

/-- Braverman et al., ): for any family of discrete distributions
`{P b : b ∈ {0, 1}^m}` satisfying the cut-paste property,
`h²(P 0, P 1) ≤ 4 * ∑ i, h²(P 0, P eᵢ)`.
-/
theorem hellingerSq_le_four_mul_sum_basis {m : ℕ} [Finite α]
    (P : (Fin m → Bool) → PMF α) (hP : IsCutPaste P) :
    hellingerSq (P (fun _ => false)) (P (fun _ => true)) ≤
      4 * ∑ i : Fin m, hellingerSq (P (fun _ => false)) (P (fun j => decide (j = i))) := by
  classical
  by_cases hm : m = 0
  · subst hm
    have hzero : (fun _ : Fin 0 => false) = (fun _ : Fin 0 => true) := funext fun i => i.elim0
    rw [hzero, hellingerSq_self]
    simp
  let L := Nat.clog 2 m
  have hm_le : m ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) m
  let P' : (Fin (2 ^ L) → Bool) → PMF α := fun b =>
    P (fun i => b ⟨i.1, lt_of_lt_of_le i.2 hm_le⟩)
  have hP' : IsCutPaste P' := by
    intro a b c d habcd
    exact hP _ _ _ _ fun i => habcd ⟨i.1, lt_of_lt_of_le i.2 hm_le⟩
  have hmain := hellingerSq_le_four_mul_sum_basis_pow_two L P' hP'
  have h01 : P' (fun _ => false) = P (fun _ => false) ∧ P' (fun _ => true) = P (fun _ => true) :=
    ⟨rfl, rfl⟩
  rw [h01.1, h01.2] at hmain
  refine hmain.trans_eq ?_
  congr 1
  let emb : Fin m ↪ Fin (2 ^ L) := ⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 hm_le⟩,
    fun i j h => Fin.ext (Fin.mk.inj h)⟩
  refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.map emb)) fun j _ hj => ?_).symm.trans
    (by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsingle : P' (fun u => decide (u = emb i)) = P (fun k => decide (k = i)) := by
        dsimp only [P']
        exact congrArg P (funext fun k => by
          change decide (emb k = emb i) = decide (k = i)
          simp [emb.injective.eq_iff])
      rw [hsingle])
  have hsingle0 : P' (fun u => decide (u = j)) = P (fun _ => false) := by
    dsimp only [P']
    refine congrArg P (funext fun k => ?_)
    have hne : (⟨k.1, lt_of_lt_of_le k.2 hm_le⟩ : Fin (2 ^ L)) ≠ j := by
      intro heq
      apply hj
      rw [Finset.mem_map]
      exact ⟨k, Finset.mem_univ k, heq⟩
    simp [hne]
  rw [hsingle0, hellingerSq_self]

private example : hellingerSq (PMF.pure true) (PMF.pure false) ≤
    jensenShannonBits (PMF.pure true) (PMF.pure false) :=
  hellingerSq_le_jensenShannonBits _ _

end CslibFrontier.Probability.Hellinger
