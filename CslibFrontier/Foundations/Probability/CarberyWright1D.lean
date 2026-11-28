module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import CslibFrontier.Foundations.Probability.Reasonable
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-Dimensional Log-Concave and Gaussian Carbery–Wright Anti-Concentration

This module proves the one-dimensional Carbery–Wright anti-concentration inequality for univariate
polynomials of degree at most `d ≥ 1` under any continuous strictly positive log-concave
probability density on a compact interval `[a, b]` (with explicit universal constant `32 * exp 6`),
together with its one-dimensional standard Gaussian corollary.

## Main results

* `CslibFrontier.Probability.carbery_wright_1d_compact`:
  for any continuous strictly positive log-concave probability density `w` on `[a, b]`,
  `deg q ≤ d` (`1 ≤ d`), and `ε > 0`,
  `∫_{Icc a b} 1_{|q| ≤ ε} w ≤ (32 * exp 6) * d * (ε / √(∫_{Icc a b} q^2 w))^(1/d)`.
* `CslibFrontier.Probability.carbery_wright_1d_gaussian`:
  the one-dimensional standard Gaussian anti-concentration corollary.
-/

public section

open MeasureTheory ProbabilityTheory Polynomial Real Set Filter Topology
open scoped BigOperators NNReal

namespace CslibFrontier.Probability

/-! ### Elementary combinatorial and analytic helpers -/

private theorem nat_pow_div_factorial_le_exp (d : ℕ) :
    (d : ℝ) ^ d / (d.factorial : ℝ) ≤ rexp (d : ℝ) := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (d : ℝ)) (Nat.cast_nonneg d) (d + 1)
  have hmem : d ∈ Finset.range (d + 1) := Finset.mem_range.2 (Nat.lt_succ_self d)
  have hsingle := Finset.single_le_sum (f := fun k => (d : ℝ) ^ k / (k.factorial : ℝ))
    (fun k _ => by positivity) hmem
  exact hsingle.trans hsum

private theorem add_two_pow_div_factorial_le_exp_three_pow {d : ℕ} (hd : 1 ≤ d) :
    ((d + 2 : ℝ) ^ d) / (d.factorial : ℝ) ≤ (rexp 3) ^ d := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 (by omega)
  have h1 : ((d + 2 : ℝ) / (d : ℝ)) ^ d ≤ rexp 2 := by
    have hstep : (d + 2 : ℝ) / (d : ℝ) ≤ rexp (2 / (d : ℝ)) := by
      have heq : (d + 2 : ℝ) / (d : ℝ) = 2 / (d : ℝ) + 1 := by field_simp [hd_pos.ne']; ring
      rw [heq]; exact Real.add_one_le_exp _
    calc ((d + 2 : ℝ) / (d : ℝ)) ^ d
        ≤ (rexp (2 / (d : ℝ))) ^ d := pow_le_pow_left₀ (by positivity) hstep d
      _ = rexp ((d : ℝ) * (2 / (d : ℝ))) := (Real.exp_nat_mul _ d).symm
      _ = rexp 2 := by congr 1; field_simp [hd_pos.ne']
  have h2 := nat_pow_div_factorial_le_exp d
  have hprod : ((d + 2 : ℝ) ^ d) / (d.factorial : ℝ) =
      ((d + 2 : ℝ) / (d : ℝ)) ^ d * ((d : ℝ) ^ d / (d.factorial : ℝ)) := by
    rw [div_pow]; field_simp [hd_pos.ne']
  rw [hprod]
  calc ((d + 2 : ℝ) / (d : ℝ)) ^ d * ((d : ℝ) ^ d / (d.factorial : ℝ))
      ≤ rexp 2 * rexp (d : ℝ) := mul_le_mul h1 h2 (by positivity) (Real.exp_nonneg _)
    _ = rexp (2 + (d : ℝ)) := (Real.exp_add 2 (d : ℝ)).symm
    _ ≤ rexp ((d : ℝ) * 3) := Real.exp_le_exp.2 (by
          have : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.2 hd
          linarith)
    _ = (rexp 3) ^ d := Real.exp_nat_mul 3 d

private theorem prod_abs_sub_fin_eq_factorial (d : ℕ) (j : Fin (d + 1)) :
    ∏ i ∈ Finset.univ.erase j, |(j.1 : ℝ) - (i.1 : ℝ)| =
      (j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ) := by
  have hsplit : (Finset.univ.erase j : Finset (Fin (d + 1))) =
      (Finset.univ.filter fun i : Fin (d + 1) => i.1 < j.1) ∪
      (Finset.univ.filter fun i : Fin (d + 1) => j.1 < i.1) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
      true_and, ne_eq, Fin.ext_iff]
    omega
  have hdisj : Disjoint (Finset.univ.filter fun i : Fin (d + 1) => i.1 < j.1)
      (Finset.univ.filter fun i : Fin (d + 1) => j.1 < i.1) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2; omega
  rw [hsplit, Finset.prod_union hdisj]
  congr 1
  · -- Left product: `i.1 < j.1`, `j.1 - i.1` runs over `1, ..., j.1`
    have hbij : ∏ i ∈ Finset.univ.filter (fun i : Fin (d + 1) => i.1 < j.1),
          |(j.1 : ℝ) - (i.1 : ℝ)| =
        ∏ k ∈ Finset.range j.1, ((k + 1 : ℕ) : ℝ) := by
      refine Finset.prod_nbij'
        (fun i => j.1 - 1 - i.1)
        (fun k => ⟨j.1 - 1 - k, by omega⟩) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.2 (by omega)
      · intro k hk
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        ext; dsimp only; omega
      · intro k hk
        rw [Finset.mem_range] at hk
        dsimp only; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [abs_of_pos (sub_pos.2 (Nat.cast_lt.2 hi))]
        have : (j.1 - 1 - i.1 + 1 : ℕ) = j.1 - i.1 := by omega
        rw [this, Nat.cast_sub hi.le]
    rw [hbij]
    have hfac : ∀ m : ℕ, ∏ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring
    exact hfac j.1
  · -- Right product: `j.1 < i.1`, `i.1 - j.1` runs over `1, ..., d - j.1`
    have hbij : ∏ i ∈ Finset.univ.filter (fun i : Fin (d + 1) => j.1 < i.1),
          |(j.1 : ℝ) - (i.1 : ℝ)| =
        ∏ k ∈ Finset.range (d - j.1), ((k + 1 : ℕ) : ℝ) := by
      refine Finset.prod_nbij'
        (fun i => i.1 - j.1 - 1)
        (fun k => ⟨min (j.1 + k + 1) d, by omega⟩) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.2 (by omega)
      · intro k hk
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [min_eq_left (by omega)]; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        ext; dsimp only; rw [min_eq_left (by omega)]; omega
      · intro k hk
        rw [Finset.mem_range] at hk
        dsimp only; rw [min_eq_left (by omega)]; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [abs_sub_comm, abs_of_pos (sub_pos.2 (Nat.cast_lt.2 hi))]
        have : (i.1 - j.1 - 1 + 1 : ℕ) = i.1 - j.1 := by omega
        rw [this, Nat.cast_sub hi.le]
    rw [hbij]
    have hfac : ∀ m : ℕ, ∏ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring
    exact hfac (d - j.1)

private theorem sum_inv_factorial_mul_factorial (d : ℕ) :
    ∑ j : Fin (d + 1), ((j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ))⁻¹ =
      (2 : ℝ) ^ d / (d.factorial : ℝ) := by
  have hchoose : ∑ j : Fin (d + 1), (d.choose j.1 : ℝ) = (2 : ℝ) ^ d := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (d.choose k : ℝ)) (d + 1)]
    exact_mod_cast Nat.sum_range_choose d
  have hterm : ∀ j : Fin (d + 1),
      ((j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ))⁻¹ =
        (d.choose j.1 : ℝ) / (d.factorial : ℝ) := fun j => by
    have hle : j.1 ≤ d := Nat.lt_succ_iff.1 j.2
    have hmul : (d.choose j.1 : ℝ) * ((j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ)) =
        (d.factorial : ℝ) := by
      rw [← mul_assoc]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
    have h1 : (j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ) ≠ 0 := by positivity
    have h2 : (d.factorial : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff h2, inv_mul_eq_iff_eq_mul₀ h1, mul_comm]
    exact hmul.symm
  simp_rw [hterm, ← Finset.sum_div, hchoose]

private theorem integral_Ioi_pow_mul_exp_neg (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ k * rexp (-u) = (k.factorial : ℝ) := by
  have hG := Real.Gamma_eq_integral (s := (k + 1 : ℝ)) (by positivity)
  have hfac := Real.Gamma_nat_eq_factorial k
  rw [hG] at hfac
  have heq : EqOn (fun u : ℝ => rexp (-u) * u ^ ((k + 1 : ℝ) - 1))
      (fun u : ℝ => u ^ k * rexp (-u)) (Ioi (0 : ℝ)) := fun u hu => by
    simp only [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, hfac]

private theorem integrableOn_Ioi_pow_mul_exp_neg (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * rexp (-u)) (Ioi (0 : ℝ)) volume := by
  have hG := Real.GammaIntegral_convergent (s := (k + 1 : ℝ)) (by positivity)
  refine hG.congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast, mul_comm]

private theorem integrable_abs_pow_mul_exp_neg_abs (k : ℕ) :
    Integrable (fun s : ℝ => |s| ^ k * rexp (-|s|)) volume := by
  have hi_pos : IntegrableOn (fun s : ℝ => |s| ^ k * rexp (-|s|)) (Ioi (0 : ℝ)) volume :=
    (integrableOn_Ioi_pow_mul_exp_neg k).congr_fun (fun s hs => by
      rw [abs_of_pos hs]) measurableSet_Ioi
  have hi_neg : IntegrableOn (fun s : ℝ => |s| ^ k * rexp (-|s|)) (Iic (0 : ℝ)) volume := by
    have hcomp : IntegrableOn (fun s : ℝ => |-s| ^ k * rexp (-|-s|)) (Ici (0 : ℝ)) volume := by
      have h1 : IntegrableOn (fun s : ℝ => |s| ^ k * rexp (-|s|)) (Ici (0 : ℝ)) volume :=
        (integrableOn_Ioi_pow_mul_exp_neg k).congr_set_ae Ioi_ae_eq_Ici.symm |>.congr_fun
          (fun s hs => by rw [abs_of_nonneg hs]) measurableSet_Ici
      exact h1.congr_fun (fun s _ => by simp) measurableSet_Ici
    have hpre : (fun x : ℝ => -x) ⁻¹' Ici (0 : ℝ) = Iic (0 : ℝ) := by ext x; simp
    rw [← hpre]
    simpa [abs_neg] using hcomp.comp_neg
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi]; exact hi_neg.union hi_pos

private theorem integral_abs_pow_mul_exp_neg_abs (k : ℕ) :
    ∫ s : ℝ, |s| ^ k * rexp (-|s|) = 2 * (k.factorial : ℝ) := by
  have hint := integrable_abs_pow_mul_exp_neg_abs k
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint, Set.compl_Iic]
  have h1 : ∫ s in Ioi (0 : ℝ), |s| ^ k * rexp (-|s|) = (k.factorial : ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => by rw [abs_of_pos hs]),
      integral_Ioi_pow_mul_exp_neg k]
  have h2 : ∫ s in Iic (0 : ℝ), |s| ^ k * rexp (-|s|) = (k.factorial : ℝ) := by
    have hcomp := integral_comp_neg_Iic (0 : ℝ) (fun s : ℝ => |s| ^ k * rexp (-|s|))
    simp only [abs_neg, neg_zero] at hcomp
    rw [hcomp, h1]
  linarith

private theorem Icc_disjoint_Ioc_self {a b c : ℝ} : Disjoint (Icc a b) (Ioc b c) :=
  Set.disjoint_left.2 fun _ h1 h2 => not_lt_of_ge h1.2 h2.1

private theorem integral_comp_add_left_Icc (f : ℝ → ℝ) (c a b : ℝ) :
    ∫ x in Icc a b, f (c + x) = ∫ x in Icc (c + a) (c + b), f x := by
  rcases le_total a b with hab | hba
  · rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_of_le (by linarith : c + a ≤ c + b),
      intervalIntegral.integral_comp_add_left]
  · rcases hba.eq_or_lt with rfl | hlt
    · simp
    · rw [Set.Icc_eq_empty_of_lt hlt,
        Set.Icc_eq_empty_of_lt (by linarith : c + b < c + a)]; simp

private theorem integral_comp_mul_left_Icc (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ∫ x in Icc a b, f (c * x) = c⁻¹ * ∫ x in Icc (c * a) (c * b), f x := by
  rcases le_total a b with hab | hba
  · rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hc.le),
      intervalIntegral.integral_comp_mul_left f hc.ne', smul_eq_mul]
  · rcases hba.eq_or_lt with rfl | hlt
    · simp
    · rw [Set.Icc_eq_empty_of_lt hlt,
        Set.Icc_eq_empty_of_lt (mul_lt_mul_of_pos_left hlt hc)]; simp

private theorem integral_comp_neg_Icc (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in Icc a b, f (-x) = ∫ x in Icc (-b) (-a), f x := by
  rcases le_total a b with hab | hba
  · rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_of_le (neg_le_neg hab),
      intervalIntegral.integral_comp_neg]
  · rcases hba.eq_or_lt with rfl | hlt
    · simp
    · rw [Set.Icc_eq_empty_of_lt hlt, Set.Icc_eq_empty_of_lt (neg_lt_neg hlt)]; simp

/-! ### 1D log-concave decay and quantile-node Lagrange bound -/

/-- Log-concave tail decay on `[a, b]` around a mode `0 ∈ [a, b]`:
if `w` is continuous, positive, log-concave on `[a, b]` with `∫_{Icc a b} w = 1` and
`∀ u ∈ Icc a b, w u ≤ w 0`, then there exists `L > 0` with `1 / 2 ≤ w 0 * L ≤ exp 1`,
`w` antitone on `[0, b]` and monotone on `[a, 0]`, and `w u ≤
  w 0 * exp (1 - |u| / L)` on `[a, b]`. -/
private theorem logConcave_mode_bounds {a b : ℝ} (hab : a < b) (ha0 : a ≤ 0) (hb0 : 0 ≤ b)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Icc a b)) (hw_pos : ∀ u ∈ Icc a b, 0 < w u)
    (hw_lc : ConcaveOn ℝ (Icc a b) (fun u => Real.log (w u)))
    (hw_max : ∀ u ∈ Icc a b, w u ≤ w 0) (hw_int : ∫ u in Icc a b, w u = 1) :
    (AntitoneOn w (Icc 0 b)) ∧ (MonotoneOn w (Icc a 0)) ∧
    ∃ L > 0, 1 / 2 ≤ w 0 * L ∧ w 0 * L ≤ rexp 1 ∧
      ∀ u ∈ Icc a b, w u ≤ w 0 * rexp (1 - |u| / L) := by
  set M := w 0
  have hM_pos : 0 < M := hw_pos 0 ⟨ha0, hb0⟩
  have hanti : AntitoneOn w (Icc 0 b) := by
    intro x hx y hy hxy
    rcases hxy.eq_or_lt with rfl | hlt
    · exact le_rfl
    have hy_pos : 0 < y := lt_of_le_of_lt hx.1 hlt
    have hα : 0 ≤ x / y := div_nonneg hx.1 hy_pos.le
    have hβ : 0 ≤ 1 - x / y := sub_nonneg.2 ((div_le_one hy_pos).2 hlt.le)
    have hconc := hw_lc.2 ⟨ha0, hb0⟩ ⟨ha0.trans hy.1, hy.2⟩ hβ hα (by ring)
    have hpt : (1 - x / y) • (0 : ℝ) + (x / y) • y = x := by
      simp [smul_eq_mul]; field_simp [hy_pos.ne']
    rw [hpt] at hconc
    have hlog_le : Real.log (w y) ≤ Real.log (w 0) :=
      Real.log_le_log (hw_pos y ⟨ha0.trans hy.1, hy.2⟩) (hw_max y ⟨ha0.trans hy.1, hy.2⟩)
    have hlog_xy : Real.log (w y) ≤ Real.log (w x) := by
      simp only [smul_eq_mul] at hconc; nlinarith
    exact (Real.log_le_log_iff (hw_pos y ⟨ha0.trans hy.1, hy.2⟩)
      (hw_pos x ⟨ha0.trans hx.1, hx.2⟩)).1 hlog_xy
  have hmono : MonotoneOn w (Icc a 0) := by
    intro x hx y hy hxy
    rcases hxy.eq_or_lt with rfl | hlt
    · exact le_rfl
    have hx_neg : x < 0 := lt_of_lt_of_le hlt hy.2
    have hα : 0 ≤ y / x := div_nonneg_of_nonpos hy.2 hx_neg.le
    have hβ : 0 ≤ 1 - y / x := sub_nonneg.2 (by rw [div_le_one_of_neg hx_neg]; linarith)
    have hconc := hw_lc.2 ⟨ha0, hb0⟩ ⟨hx.1, hx.2.trans hb0⟩ hβ hα (by ring)
    have hpt : (1 - y / x) • (0 : ℝ) + (y / x) • x = y := by
      simp [smul_eq_mul]; field_simp [hx_neg.ne]
    rw [hpt] at hconc
    have hlog_le : Real.log (w x) ≤ Real.log (w 0) :=
      Real.log_le_log (hw_pos x ⟨hx.1, hx.2.trans hb0⟩) (hw_max x ⟨hx.1, hx.2.trans hb0⟩)
    have hlog_xy : Real.log (w x) ≤ Real.log (w y) := by
      simp only [smul_eq_mul] at hconc; nlinarith
    exact (Real.log_le_log_iff (hw_pos x ⟨hx.1, hx.2.trans hb0⟩)
      (hw_pos y ⟨hy.1, hy.2.trans hb0⟩)).1 hlog_xy
  refine ⟨hanti, hmono, ?_⟩
  -- Right scale `t₁` and left scale `t₂`
  set S₁ : Set ℝ := {u ∈ Icc 0 b | M * rexp (-1) ≤ w u}
  set S₂ : Set ℝ := {u ∈ Icc 0 (-a) | M * rexp (-1) ≤ w (-u)}
  have h0S₁ : (0 : ℝ) ∈ S₁ := ⟨⟨le_rfl, hb0⟩, by
    have : rexp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    nlinarith⟩
  have h0S₂ : (0 : ℝ) ∈ S₂ := ⟨⟨le_rfl, by linarith⟩, by
    have : rexp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    simpa using mul_le_of_le_one_right hM_pos.le this⟩
  have hS₁_closed : IsClosed S₁ := by
    have hcont1 : ContinuousOn w (Icc 0 b) := hw_cont.mono (fun u hu => ⟨ha0.trans hu.1, hu.2⟩)
    exact (hcont1.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
  have hS₂_closed : IsClosed S₂ := by
    have hcont2 : ContinuousOn (fun u => w (-u)) (Icc 0 (-a)) :=
      hw_cont.comp continuousOn_neg fun u hu => ⟨by linarith [hu.2], by linarith [hu.1, hb0]⟩
    exact (hcont2.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
  set t₁ := sSup S₁
  set t₂ := sSup S₂
  have ht₁_mem : t₁ ∈ S₁ := hS₁_closed.csSup_mem ⟨0, h0S₁⟩ ⟨b, fun _ hu => hu.1.2⟩
  have ht₂_mem : t₂ ∈ S₂ := hS₂_closed.csSup_mem ⟨0, h0S₂⟩ ⟨-a, fun _ hu => hu.1.2⟩
  have ht₁_ge0 : 0 ≤ t₁ := ht₁_mem.1.1
  have ht₁_leb : t₁ ≤ b := ht₁_mem.1.2
  have ht₂_ge0 : 0 ≤ t₂ := ht₂_mem.1.1
  have ht₂_lea : t₂ ≤ -a := ht₂_mem.1.2
  -- If `b > 0` then `t₁ > 0`; if `a < 0` then `t₂ > 0`
  have ht₁_pos_of : 0 < b → 0 < t₁ := fun hbpos => by
    have hlt : M * rexp (-1) < w 0 := by
      have : rexp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
      nlinarith
    have hcw : ContinuousWithinAt w (Icc 0 b) 0 :=
      (hw_cont.mono (Set.Icc_subset_Icc ha0 le_rfl)) 0 ⟨le_rfl, hb0⟩
    have hev := hcw.eventually (Ioi_mem_nhds hlt)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    set u₀ := min b (δ / 2)
    have hu₀_pos : 0 < u₀ := lt_min hbpos (by positivity)
    have hu₀_mem : u₀ ∈ S₁ := by
      refine ⟨⟨hu₀_pos.le, min_le_left _ _⟩, (hball ?_ ⟨hu₀_pos.le, min_le_left _ _⟩).le⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos hu₀_pos]
      exact (min_le_right _ _).trans_lt (by linarith)
    exact lt_of_lt_of_le hu₀_pos (le_csSup ⟨b, fun _ hu => hu.1.2⟩ hu₀_mem)
  have ht₂_pos_of : a < 0 → 0 < t₂ := fun haneg => by
    have hlt : M * rexp (-1) < w (-0) := by
      have : rexp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
      simp only [neg_zero]; nlinarith
    have hcont2 : ContinuousOn (fun u => w (-u)) (Icc 0 (-a)) :=
      hw_cont.comp continuousOn_neg fun u hu => ⟨by linarith [hu.2], by linarith [hu.1, hb0]⟩
    have hev := (hcont2 0 ⟨le_rfl, by linarith⟩).eventually (Ioi_mem_nhds hlt)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    set u₀ := min (-a) (δ / 2)
    have hu₀_pos : 0 < u₀ := lt_min (by linarith) (by positivity)
    have hu₀_mem : u₀ ∈ S₂ := by
      refine ⟨⟨hu₀_pos.le, min_le_left _ _⟩, (hball ?_ ⟨hu₀_pos.le, min_le_left _ _⟩).le⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos hu₀_pos]
      exact (min_le_right _ _).trans_lt (by linarith)
    exact lt_of_lt_of_le hu₀_pos (le_csSup ⟨-a, fun _ hu => hu.1.2⟩ hu₀_mem)
  -- Exponential decay past `t₁` and past `t₂`
  have hdecay₁ : ∀ u ∈ Ioc t₁ b, 0 < t₁ ∧ w u ≤ M * rexp (-u / t₁) := by
    intro u hu
    have hbpos : 0 < b := lt_of_le_of_lt ht₁_ge0 (lt_of_lt_of_le hu.1 hu.2)
    have ht₁_pos : 0 < t₁ := ht₁_pos_of hbpos
    have hwt₁_eq : w t₁ = M * rexp (-1) := by
      refine le_antisymm ?_ ht₁_mem.2
      by_contra hgt; push Not at hgt
      have hcw : ContinuousWithinAt w (Icc 0 b) t₁ :=
        (hw_cont.mono (Set.Icc_subset_Icc ha0 le_rfl)) t₁ ht₁_mem.1
      obtain ⟨δ, hδ, hball⟩ :=
        Metric.eventually_nhds_iff.1
          (eventually_nhdsWithin_iff.1 (hcw.eventually (Ioi_mem_nhds hgt)))
      set u' := min b (t₁ + δ / 2)
      have hu'_gt : t₁ < u' := lt_min (lt_of_lt_of_le hu.1 hu.2) (by linarith)
      have hu'_mem : u' ∈ S₁ := by
        refine ⟨⟨ht₁_ge0.trans hu'_gt.le, min_le_left _ _⟩,
          (hball ?_ ⟨ht₁_ge0.trans hu'_gt.le, min_le_left _ _⟩).le⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 hu'_gt)]
        linarith [min_le_right b (t₁ + δ / 2)]
      exact hu'_gt.not_ge (le_csSup ⟨b, fun _ hx => hx.1.2⟩ hu'_mem)
    have hu_pos : 0 < u := lt_trans ht₁_pos hu.1
    have hα : 0 ≤ t₁ / u := div_nonneg ht₁_pos.le hu_pos.le
    have hβ : 0 ≤ 1 - t₁ / u := sub_nonneg.2 ((div_le_one hu_pos).2 hu.1.le)
    have hconc := hw_lc.2 ⟨ha0, hb0⟩ ⟨ha0.trans hu_pos.le, hu.2⟩ hβ hα (by ring)
    have hpt : (1 - t₁ / u) • (0 : ℝ) + (t₁ / u) • u = t₁ := by
      simp [smul_eq_mul]; field_simp [hu_pos.ne']
    dsimp only at hconc
    rw [hpt, hwt₁_eq, Real.log_mul hM_pos.ne' (Real.exp_ne_zero _), Real.log_exp] at hconc
    simp only [smul_eq_mul] at hconc
    have hlog_u : Real.log (w u) ≤ Real.log M - u / t₁ := by
      have hstep : -1 ≥ (t₁ / u) * (Real.log (w u) - Real.log M) := by linarith
      have hdiv : Real.log (w u) - Real.log M ≤ -(u / t₁) := by
        have hmul := mul_le_mul_of_nonneg_left hstep (div_nonneg hu_pos.le ht₁_pos.le)
        have hcancel : u / t₁ * (t₁ / u) = 1 := by field_simp [hu_pos.ne', ht₁_pos.ne']
        rw [← mul_assoc, hcancel, one_mul] at hmul
        linarith
      linarith
    refine ⟨ht₁_pos, ?_⟩
    rw [← Real.exp_log (hw_pos u ⟨ha0.trans hu_pos.le, hu.2⟩),
      ← Real.exp_log hM_pos, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [show -u / t₁ = -(u / t₁) by ring])
  have hdecay₂ : ∀ u ∈ Ioc t₂ (-a), 0 < t₂ ∧ w (-u) ≤ M * rexp (-u / t₂) := by
    intro u hu
    have haneg : a < 0 := by linarith [ht₂_ge0, hu.1, hu.2]
    have ht₂_pos : 0 < t₂ := ht₂_pos_of haneg
    have hwt₂_eq : w (-t₂) = M * rexp (-1) := by
      refine le_antisymm ?_ ht₂_mem.2
      by_contra hgt; push Not at hgt
      have hcont2 : ContinuousOn (fun x => w (-x)) (Icc 0 (-a)) :=
        hw_cont.comp continuousOn_neg fun x hx => ⟨by linarith [hx.2], by linarith [hx.1, hb0]⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
        (eventually_nhdsWithin_iff.1 ((hcont2 t₂ ht₂_mem.1).eventually (Ioi_mem_nhds hgt)))
      set u' := min (-a) (t₂ + δ / 2)
      have hu'_gt : t₂ < u' := lt_min (lt_of_lt_of_le hu.1 hu.2) (by linarith)
      have hu'_mem : u' ∈ S₂ := by
        refine ⟨⟨ht₂_ge0.trans hu'_gt.le, min_le_left _ _⟩,
          (hball ?_ ⟨ht₂_ge0.trans hu'_gt.le, min_le_left _ _⟩).le⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 hu'_gt)]
        linarith [min_le_right (-a) (t₂ + δ / 2)]
      exact hu'_gt.not_ge (le_csSup ⟨-a, fun _ hx => hx.1.2⟩ hu'_mem)
    have hu_pos : 0 < u := lt_trans ht₂_pos hu.1
    have hα : 0 ≤ t₂ / u := div_nonneg ht₂_pos.le hu_pos.le
    have hβ : 0 ≤ 1 - t₂ / u := sub_nonneg.2 ((div_le_one hu_pos).2 hu.1.le)
    have hconc := hw_lc.2 (x := 0) ⟨ha0, hb0⟩ (y := -u)
      ⟨by linarith [hu.2], by linarith [hu_pos, hb0]⟩ hβ hα (by ring)
    have hpt : (1 - t₂ / u) • (0 : ℝ) + (t₂ / u) • (-u) = -t₂ := by
      simp [smul_eq_mul]; field_simp [hu_pos.ne']
    dsimp only at hconc
    rw [hpt, hwt₂_eq, Real.log_mul hM_pos.ne' (Real.exp_ne_zero _), Real.log_exp] at hconc
    simp only [smul_eq_mul] at hconc
    have hlog_u : Real.log (w (-u)) ≤ Real.log M - u / t₂ := by
      have hstep : -1 ≥ (t₂ / u) * (Real.log (w (-u)) - Real.log M) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hstep (div_nonneg hu_pos.le ht₂_pos.le)
      have hcancel : u / t₂ * (t₂ / u) = 1 := by field_simp [hu_pos.ne', ht₂_pos.ne']
      rw [← mul_assoc, hcancel, one_mul] at hmul
      linarith
    refine ⟨ht₂_pos, ?_⟩
    rw [← Real.exp_log (hw_pos (-u) ⟨by linarith [hu.2], by linarith [hu_pos, hb0]⟩),
      ← Real.exp_log hM_pos, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [show -u / t₂ = -(u / t₂) by ring])
  set L := t₁ + t₂
  have hL_pos : 0 < L := by
    rcases lt_or_eq_of_le hb0 with hbpos | rfl
    · exact add_pos_of_pos_of_nonneg (ht₁_pos_of hbpos) ht₂_ge0
    · exact add_pos_of_nonneg_of_pos ht₁_ge0 (ht₂_pos_of hab)
  have hw_intOn : IntegrableOn w (Icc a b) volume := hw_cont.integrableOn_Icc
  -- Upper bound `M * L ≤ exp 1`
  have hML_le : M * L ≤ rexp 1 := by
    have hsub : Icc (-t₂) t₁ ⊆ Icc a b := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hlow : ∀ u ∈ Icc (-t₂) t₁, M * rexp (-1) ≤ w u := fun u hu => by
      rcases le_total 0 u with hu0 | hu0
      · exact ht₁_mem.2.trans (hanti ⟨hu0, hu.2.trans ht₁_leb⟩ ht₁_mem.1 hu.2)
      · exact ht₂_mem.2.trans (hmono ⟨by linarith [ht₂_lea], by linarith [ht₂_ge0]⟩
          ⟨by linarith [hu.1, ht₂_lea], hu0⟩ hu.1)
    have hmono_int : ∫ u in Icc (-t₂) t₁, M * rexp (-1) ≤ ∫ u in Icc (-t₂) t₁, w u :=
      setIntegral_mono_on (integrableOn_const (by simp)) (hw_intOn.mono_set hsub)
        measurableSet_Icc hlow
    have hsub_int : ∫ u in Icc (-t₂) t₁, w u ≤ ∫ u in Icc a b, w u :=
      setIntegral_mono_set hw_intOn
        (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => (hw_pos u hu).le)
        (Eventually.of_forall hsub)
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul,
      show t₁ - -t₂ = L by unfold L; ring] at hmono_int
    rw [hw_int] at hsub_int
    have hle : M * rexp (-1) * L ≤ 1 := by linarith
    have hmul : M * L * (rexp (-1) * rexp 1) ≤ rexp 1 := by
      linarith [mul_le_mul_of_nonneg_right hle (Real.exp_nonneg 1)]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
    exact hmul
  -- Lower bound `1 / 2 ≤ M * L`
  have hML_ge : 1 / 2 ≤ M * L := by
    have hint_right : ∫ u in Icc 0 b, w u ≤ 2 * M * t₁ := by
      rcases eq_or_lt_of_le hb0 with rfl | hbpos
      · simp only [Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
          integral_zero_measure]
        positivity
      have ht₁_pos : 0 < t₁ := ht₁_pos_of hbpos
      have hsplit : Icc 0 b = Icc 0 t₁ ∪ Ioc t₁ b :=
        (Set.Icc_union_Ioc_eq_Icc ht₁_ge0 ht₁_leb).symm
      rw [hsplit, setIntegral_union Icc_disjoint_Ioc_self measurableSet_Ioc
        (hw_intOn.mono_set fun u hu => ⟨ha0.trans hu.1, hu.2.trans ht₁_leb⟩)
        (hw_intOn.mono_set fun u hu => ⟨ha0.trans (ht₁_ge0.trans hu.1.le), hu.2⟩)]
      have h1 : ∫ u in Icc 0 t₁, w u ≤ M * t₁ := by
        have hm := setIntegral_mono_on
          (hw_intOn.mono_set (Set.Icc_subset_Icc ha0 ht₁_leb))
          (integrableOn_const (C := M) (by simp)) measurableSet_Icc
          (fun u hu => hw_max u ⟨ha0.trans hu.1, hu.2.trans ht₁_leb⟩)
        rwa [setIntegral_const, Real.volume_real_Icc_of_le ht₁_ge0, sub_zero, smul_eq_mul,
          mul_comm] at hm
      have h2 : ∫ u in Ioc t₁ b, w u ≤ M * t₁ := by
        have hexp_int : IntegrableOn (fun u : ℝ => M * rexp (-u / t₁)) (Ioi t₁) volume := by
          have h0 : IntegrableOn (fun v : ℝ => rexp (-v)) (Ioi (0 : ℝ)) volume := by
            simpa using integrableOn_Ioi_pow_mul_exp_neg 0
          have hcomp :=
            ((h0.integrable_indicator measurableSet_Ioi).comp_mul_left'
              (inv_pos.2 ht₁_pos).ne').const_mul M
          refine hcomp.integrableOn.congr_fun (fun u hu => ?_) measurableSet_Ioi
          have hpos : t₁⁻¹ * u ∈ Ioi (0 : ℝ) := mul_pos (inv_pos.2 ht₁_pos) (lt_trans ht₁_pos hu)
          dsimp only
          rw [Set.indicator_of_mem hpos]
          congr 2; ring
        have hm := setIntegral_mono_on
          (hw_intOn.mono_set
            (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc (ha0.trans ht₁_ge0) le_rfl)))
          (hexp_int.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc
          (fun u hu => (hdecay₁ u hu).2)
        have htail : ∫ u in Ioc t₁ b, M * rexp (-u / t₁) ≤ ∫ u in Ioi t₁, M * rexp (-u / t₁) :=
          setIntegral_mono_set hexp_int
            (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => by positivity)
            (Eventually.of_forall Set.Ioc_subset_Ioi_self)
        have hval : ∫ u in Ioi t₁, M * rexp (-u / t₁) = M * t₁ * rexp (-1) := by
          rw [integral_const_mul]
          have hsub : ∫ u in Ioi t₁, rexp (-u / t₁) =
              t₁ * ∫ v in Ioi (1 : ℝ), rexp (-v) := by
            have heq : (fun u : ℝ => rexp (-u / t₁)) = fun u => rexp (-(t₁⁻¹ * u)) :=
              funext fun u => by congr 1; ring
            rw [heq,
              MeasureTheory.integral_comp_mul_left_Ioi (fun v => rexp (-v)) t₁ (inv_pos.2 ht₁_pos)]
            simp [ht₁_pos.ne']
          rw [hsub]
          have hIoi1 : ∫ v in Ioi (1 : ℝ), rexp (-v) = rexp (-1) := integral_exp_neg_Ioi (c := 1)
          rw [hIoi1]; ring
        have he1 : rexp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
        nlinarith [hm, htail, hval, mul_pos hM_pos ht₁_pos]
      linarith
    have hint_left : ∫ u in Icc a 0, w u ≤ 2 * M * t₂ := by
      rcases eq_or_lt_of_le ha0 with rfl | haneg
      · simp only [Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
          integral_zero_measure]
        positivity
      have ht₂_pos : 0 < t₂ := ht₂_pos_of haneg
      have hneg_eq : ∫ u in Icc a 0, w u = ∫ u in Icc 0 (-a), w (-u) := by
        rw [integral_comp_neg_Icc]; simp
      rw [hneg_eq]
      have hw2_int : IntegrableOn (fun u => w (-u)) (Icc 0 (-a)) volume := by
        have hcont2 : ContinuousOn (fun u => w (-u)) (Icc 0 (-a)) :=
          hw_cont.comp continuousOn_neg fun u hu => ⟨by linarith [hu.2], by linarith [hu.1, hb0]⟩
        exact hcont2.integrableOn_Icc
      have hsplit : Icc 0 (-a) = Icc 0 t₂ ∪ Ioc t₂ (-a) :=
        (Set.Icc_union_Ioc_eq_Icc ht₂_ge0 ht₂_lea).symm
      rw [hsplit, setIntegral_union Icc_disjoint_Ioc_self measurableSet_Ioc
        (hw2_int.mono_set fun u hu => ⟨hu.1, hu.2.trans ht₂_lea⟩)
        (hw2_int.mono_set fun u hu => ⟨ht₂_ge0.trans hu.1.le, hu.2⟩)]
      have h1 : ∫ u in Icc 0 t₂, w (-u) ≤ M * t₂ := by
        have hm := setIntegral_mono_on
          (hw2_int.mono_set (Set.Icc_subset_Icc le_rfl ht₂_lea))
          (integrableOn_const (C := M) (by simp)) measurableSet_Icc
          (fun u hu => hw_max (-u) ⟨by linarith [hu.2, ht₂_lea], by linarith [hu.1, hb0]⟩)
        rwa [setIntegral_const, Real.volume_real_Icc_of_le ht₂_ge0, sub_zero, smul_eq_mul,
          mul_comm] at hm
      have h2 : ∫ u in Ioc t₂ (-a), w (-u) ≤ M * t₂ := by
        have hexp_int : IntegrableOn (fun u : ℝ => M * rexp (-u / t₂)) (Ioi t₂) volume := by
          have h0 : IntegrableOn (fun v : ℝ => rexp (-v)) (Ioi (0 : ℝ)) volume := by
            simpa using integrableOn_Ioi_pow_mul_exp_neg 0
          have hcomp :=
            ((h0.integrable_indicator measurableSet_Ioi).comp_mul_left'
              (inv_pos.2 ht₂_pos).ne').const_mul M
          refine hcomp.integrableOn.congr_fun (fun u hu => ?_) measurableSet_Ioi
          have hpos : t₂⁻¹ * u ∈ Ioi (0 : ℝ) := mul_pos (inv_pos.2 ht₂_pos) (lt_trans ht₂_pos hu)
          dsimp only
          rw [Set.indicator_of_mem hpos]
          congr 2; ring
        have hm := setIntegral_mono_on
          (hw2_int.mono_set
            (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc ht₂_ge0 le_rfl)))
          (hexp_int.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc
          (fun u hu => (hdecay₂ u hu).2)
        have htail : ∫ u in Ioc t₂ (-a), M * rexp (-u / t₂) ≤ ∫ u in Ioi t₂, M * rexp (-u / t₂) :=
          setIntegral_mono_set hexp_int
            (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => by positivity)
            (Eventually.of_forall Set.Ioc_subset_Ioi_self)
        have hval : ∫ u in Ioi t₂, M * rexp (-u / t₂) = M * t₂ * rexp (-1) := by
          rw [integral_const_mul]
          have hsub : ∫ u in Ioi t₂, rexp (-u / t₂) =
              t₂ * ∫ v in Ioi (1 : ℝ), rexp (-v) := by
            have heq : (fun u : ℝ => rexp (-u / t₂)) = fun u => rexp (-(t₂⁻¹ * u)) :=
              funext fun u => by congr 1; ring
            rw [heq,
              MeasureTheory.integral_comp_mul_left_Ioi (fun v => rexp (-v)) t₂ (inv_pos.2 ht₂_pos)]
            simp [ht₂_pos.ne']
          rw [hsub, integral_exp_neg_Ioi (c := 1)]; ring
        have he1 : rexp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
        nlinarith [hm, htail, hval, mul_pos hM_pos ht₂_pos]
      linarith
    have hsplit : Icc a b = Icc a 0 ∪ Ioc 0 b := (Set.Icc_union_Ioc_eq_Icc ha0 hb0).symm
    have htot : ∫ u in Icc a b, w u = (∫ u in Icc a 0, w u) + (∫ u in Icc 0 b, w u) := by
      rw [hsplit, setIntegral_union Icc_disjoint_Ioc_self measurableSet_Ioc
        (hw_intOn.mono_set fun u hu => ⟨hu.1, hu.2.trans hb0⟩)
        (hw_intOn.mono_set fun u hu => ⟨ha0.trans hu.1.le, hu.2⟩),
        ← integral_Icc_eq_integral_Ioc]
    rw [hw_int] at htot
    unfold L; linarith
  refine ⟨L, hL_pos, hML_ge, hML_le, fun u hu => ?_⟩
  rcases le_total 0 u with hu0 | hu0
  · rw [abs_of_nonneg hu0]
    rcases le_or_gt u t₁ with hut | hut
    · have hexp1 : 1 ≤ rexp (1 - u / L) := Real.one_le_exp (by
        rw [sub_nonneg, div_le_one hL_pos]; linarith)
      exact (hw_max u hu).trans (le_mul_of_one_le_right hM_pos.le hexp1)
    · obtain ⟨ht₁_pos, hdec⟩ := hdecay₁ u ⟨hut, hu.2⟩
      refine hdec.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM_pos.le)
      have : u / L ≤ u / t₁ := div_le_div_of_nonneg_left hu0 ht₁_pos (by unfold L; linarith)
      have hneg : -u / t₁ = -(u / t₁) := by ring
      linarith
  · rw [abs_of_nonpos hu0]
    rcases le_or_gt (-u) t₂ with hut | hut
    · have hexp1 : 1 ≤ rexp (1 - -u / L) := Real.one_le_exp (by
        rw [sub_nonneg, div_le_one hL_pos]; linarith)
      exact (hw_max u hu).trans (le_mul_of_one_le_right hM_pos.le hexp1)
    · obtain ⟨ht₂_pos, hdec⟩ := hdecay₂ (-u) ⟨hut, by linarith [hu.1]⟩
      rw [neg_neg] at hdec
      refine hdec.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM_pos.le)
      have : -u / L ≤ -u / t₂ :=
        div_le_div_of_nonneg_left (by linarith) ht₂_pos (by unfold L; linarith)
      have hneg : u / t₂ = -(-u / t₂) := by ring
      linarith

/-- Core normalized 1D Carbery–Wright lemma when the mode is at `0` and scale `L = 1` with the
right half carrying at least `p / 2` of the sublevel mass. -/
private theorem carbery_wright_1d_normalized {A B : ℝ} (hA : A ≤ 0) (hB : 0 < B)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Icc A B)) (hw_pos : ∀ s ∈ Icc A B, 0 < w s)
    (hw_anti : AntitoneOn w (Icc 0 B))
    (hw_int : ∫ s in Icc A B, w s = 1)
    (hM_lo : 1 / 2 ≤ w 0) (hM_hi : w 0 ≤ rexp 1)
    (hw_decay : ∀ s ∈ Icc A B, w s ≤ w 0 * rexp (1 - |s|))
    {q : ℝ[X]} {d : ℕ} (hd : 1 ≤ d) (hdeg : q.natDegree ≤ d)
    {ε : ℝ} (hε : 0 < ε)
    {p : ℝ} (hp_pos : 0 < p)
    (hpR : p / 2 ≤ ∫ s in Icc 0 B, if |q.eval s| ≤ ε then w s else 0) :
    ∫ s in Icc A B, q.eval s ^ 2 * w s ≤
      ε ^ 2 * (32 * rexp 6 * (d : ℝ) / p) ^ (2 * d) := by
  set M := w 0
  have hM_pos : 0 < M := by linarith
  set E : Set ℝ := {s | |q.eval s| ≤ ε}
  have hE_closed : IsClosed E :=
    isClosed_le (q.continuous.abs) continuous_const
  set fE : ℝ → ℝ := fun s => if |q.eval s| ≤ ε then w s else 0
  have hfE_int : IntegrableOn fE (Icc 0 B) volume := by
    have hw0B : IntegrableOn w (Icc 0 B) volume :=
      hw_cont.integrableOn_Icc.mono_set fun s hs => ⟨hA.trans hs.1, hs.2⟩
    refine hw0B.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
    · exact (hw_cont.mono (Set.Icc_subset_Icc hA le_rfl)).aestronglyMeasurable
        measurableSet_Icc |>.indicator hE_closed.measurableSet |>.congr
          (ae_of_all _ fun s => by simp [fE, E, Set.indicator_apply])
    · simp only [fE, Real.norm_eq_abs]
      split_ifs
      · exact le_of_eq (abs_of_pos (hw_pos s ⟨hA.trans hs.1, hs.2⟩))
      · rw [abs_zero]; exact (hw_pos s ⟨hA.trans hs.1, hs.2⟩).le
  set pR : ℝ := ∫ s in Icc 0 B, fE s
  have hpR_pos : 0 < pR := lt_of_lt_of_le (by positivity) hpR
  have hpR_le1 : pR ≤ 1 := by
    calc pR ≤ ∫ s in Icc 0 B, w s :=
          setIntegral_mono_on hfE_int
            (hw_cont.integrableOn_Icc.mono_set fun s hs => ⟨hA.trans hs.1, hs.2⟩)
            measurableSet_Icc fun s hs => by
              simp only [fE]; split_ifs <;> [exact le_rfl; exact (hw_pos s ⟨hA.trans hs.1,
                hs.2⟩).le]
      _ ≤ ∫ s in Icc A B, w s :=
          setIntegral_mono_set hw_cont.integrableOn_Icc
            (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => (hw_pos s hs).le)
            (Eventually.of_forall fun s hs => ⟨hA.trans hs.1, hs.2⟩)
      _ = 1 := hw_int
  -- Define cumulative sublevel mass `F(x) = ∫_{0..x} fE` on `[0, B]`
  set F : ℝ → ℝ := fun x => ∫ s in Icc 0 x, fE s
  have hF_mono : MonotoneOn F (Icc 0 B) := fun x hx y hy hxy =>
    setIntegral_mono_set (hfE_int.mono_set fun s hs => ⟨hs.1, hs.2.trans hy.2⟩)
      (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => by
        simp only [fE]; split_ifs <;> [exact (hw_pos s ⟨hA.trans hs.1,
          hs.2.trans hy.2⟩).le; exact le_rfl])
      (Eventually.of_forall fun s hs => ⟨hs.1, hs.2.trans hxy⟩)
  have hF_diff_le : ∀ x ∈ Icc 0 B, ∀ y ∈ Icc 0 B, x ≤ y →
      F y - F x ≤ w x * (y - x) := fun x hx y hy hxy => by
    have hsplit : Icc 0 y = Icc 0 x ∪ Ioc x y := (Set.Icc_union_Ioc_eq_Icc hx.1 hxy).symm
    have hsub : F y - F x = ∫ s in Ioc x y, fE s := by
      unfold F
      rw [hsplit, setIntegral_union Icc_disjoint_Ioc_self measurableSet_Ioc
        (hfE_int.mono_set fun s hs => ⟨hs.1, hs.2.trans hx.2⟩)
        (hfE_int.mono_set fun s hs => ⟨hx.1.trans hs.1.le, hs.2.trans hy.2⟩)]
      ring
    rw [hsub]
    have hm := setIntegral_mono_on
      (hfE_int.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 hy.2)))
      (integrableOn_const (C := w x) (by simp)) measurableSet_Ioc fun s hs => by
        have hws : w s ≤ w x := hw_anti hx ⟨hx.1.trans hs.1.le, hs.2.trans hy.2⟩ hs.1.le
        simp only [fE]; split_ifs
        · exact hws
        · exact (hw_pos x ⟨hA.trans hx.1, hx.2⟩).le
    rwa [setIntegral_const, Real.volume_real_Ioc_of_le hxy, smul_eq_mul, mul_comm] at hm
  have hF_cont : ContinuousOn F (Icc 0 B) := by
    refine Metric.continuousOn_iff.2 fun x hx η hη => ?_
    refine ⟨η / (M + 1), by positivity, fun y hy hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    rcases le_total x y with hxy | hyx
    · have h1 : 0 ≤ F y - F x := sub_nonneg.2 (hF_mono hx hy hxy)
      have h2 := hF_diff_le x hx y hy hxy
      have hwx : w x ≤ M := hw_anti ⟨le_rfl, hB.le⟩ hx hx.1
      rw [abs_of_nonneg h1]
      have hlt : y - x < η / (M + 1) := by
        rwa [abs_of_nonneg (sub_nonneg.2 hxy)] at hdist
      calc F y - F x ≤ w x * (y - x) := h2
        _ ≤ M * (y - x) := mul_le_mul_of_nonneg_right hwx (sub_nonneg.2 hxy)
        _ ≤ (M + 1) * (y - x) := mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.2 hxy)
        _ < (M + 1) * (η / (M + 1)) := mul_lt_mul_of_pos_left hlt (by linarith)
        _ = η := by field_simp [(by linarith : M + 1 ≠ 0)]
    · have h1 : 0 ≤ F x - F y := sub_nonneg.2 (hF_mono hy hx hyx)
      have h2 := hF_diff_le y hy x hx hyx
      have hwy : w y ≤ M := hw_anti ⟨le_rfl, hB.le⟩ hy hy.1
      rw [abs_sub_comm, abs_of_nonneg h1]
      have hlt : x - y < η / (M + 1) := by
        rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hyx)] at hdist
      calc F x - F y ≤ w y * (x - y) := h2
        _ ≤ M * (x - y) := mul_le_mul_of_nonneg_right hwy (sub_nonneg.2 hyx)
        _ ≤ (M + 1) * (x - y) := mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.2 hyx)
        _ < (M + 1) * (η / (M + 1)) := mul_lt_mul_of_pos_left hlt (by linarith)
        _ = η := by field_simp [(by linarith : M + 1 ≠ 0)]
  -- Pick `d + 1` quantile nodes `x j ∈ E ∩ [0, B]` with `F (x j) = (j + 1) / (d + 2) * pR`
  have hnodes : ∃ x : Fin (d + 1) → ℝ,
      (∀ j, x j ∈ Icc 0 B) ∧ (∀ j, |q.eval (x j)| ≤ ε) ∧
      (∀ j, F (x j) = ((j.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR) := by
    have hex : ∀ j : Fin (d + 1), ∃ t ∈ Icc 0 B,
        |q.eval t| ≤ ε ∧ F t = ((j.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR := by
      intro j
      set c := ((j.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR
      have hc_pos : 0 < c := by positivity
      have hc_lt : c < pR := by
        have hfrac : ((j.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) < 1 := by
          rw [div_lt_one (by positivity)]; exact_mod_cast (by omega : j.1 + 1 < d + 2)
        nlinarith
      set T : Set ℝ := {t ∈ Icc 0 B | c ≤ F t}
      have hBT : B ∈ T := ⟨⟨hB.le, le_rfl⟩, hc_lt.le⟩
      have hT_closed : IsClosed T := hF_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      set t₀ := sInf T
      have ht₀_mem : t₀ ∈ T := hT_closed.csInf_mem ⟨B, hBT⟩ ⟨0, fun _ hu => hu.1.1⟩
      have ht₀_pos : 0 < t₀ := by
        rcases eq_or_lt_of_le ht₀_mem.1.1 with h0 | hpos
        · exfalso
          have hF0 : F 0 = 0 := by unfold F; simp
          linarith [ht₀_mem.2, h0 ▸ hF0]
        · exact hpos
      have hFt₀_eq : F t₀ = c := by
        refine le_antisymm ?_ ht₀_mem.2
        by_contra hgt; push Not at hgt
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
          (eventually_nhdsWithin_iff.1 ((hF_cont t₀ ht₀_mem.1).eventually (Ioi_mem_nhds hgt)))
        set t' := max 0 (t₀ - δ / 2)
        have ht'_lt : t' < t₀ := max_lt ht₀_pos (by linarith)
        have ht'_mem : t' ∈ T := by
          refine ⟨⟨le_max_left _ _, ht'_lt.le.trans ht₀_mem.1.2⟩,
            (hball ?_ ⟨le_max_left _ _, ht'_lt.le.trans ht₀_mem.1.2⟩).le⟩
          rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 ht'_lt)]
          linarith [le_max_right (0 : ℝ) (t₀ - δ / 2)]
        exact ht'_lt.not_ge (csInf_le ⟨0, fun _ hu => hu.1.1⟩ ht'_mem)
      have ht₀_E : |q.eval t₀| ≤ ε := by
        by_contra hnotE
        have hopen : IsOpen Eᶜ := hE_closed.isOpen_compl
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t₀ hnotE
        set t' := max 0 (t₀ - δ / 2)
        have ht'_lt : t' < t₀ := max_lt ht₀_pos (by linarith)
        have hzero : ∫ s in Ioc t' t₀, fE s = 0 := by
          refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
          have hmem : s ∈ Metric.ball t₀ δ := by
            rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs.2)]
            linarith [hs.1, le_max_right (0 : ℝ) (t₀ - δ / 2)]
          have hnot : ¬ |q.eval s| ≤ ε := hball hmem
          simp [fE, hnot]
        have hsplit : Icc 0 t₀ = Icc 0 t' ∪ Ioc t' t₀ :=
          (Set.Icc_union_Ioc_eq_Icc (le_max_left _ _) ht'_lt.le).symm
        have hFt' : F t' = F t₀ := by
          have hadd : F t₀ = F t' + ∫ s in Ioc t' t₀, fE s := by
            unfold F
            rw [hsplit, setIntegral_union Icc_disjoint_Ioc_self measurableSet_Ioc
              (hfE_int.mono_set fun s hs => ⟨hs.1, hs.2.trans (ht'_lt.le.trans ht₀_mem.1.2)⟩)
              (hfE_int.mono_set fun s hs => ⟨(le_max_left _ _).trans hs.1.le,
                hs.2.trans ht₀_mem.1.2⟩)]
          linarith
        have ht'_T : t' ∈ T :=
          ⟨⟨le_max_left _ _, ht'_lt.le.trans ht₀_mem.1.2⟩, by linarith [ht₀_mem.2]⟩
        exact ht'_lt.not_ge (csInf_le ⟨0, fun _ hu => hu.1.1⟩ ht'_T)
      exact ⟨t₀, ht₀_mem.1, ht₀_E, hFt₀_eq⟩
    exact ⟨fun j => (hex j).choose, fun j => (hex j).choose_spec.1,
      fun j => (hex j).choose_spec.2.1, fun j => (hex j).choose_spec.2.2⟩
  obtain ⟨x, hx_mem, hx_E, hx_F⟩ := hnodes
  have hx_strict : StrictMono x := by
    intro i j hij
    by_contra hge; push Not at hge
    have hF_le := hF_mono (hx_mem j) (hx_mem i) hge
    rw [hx_F j, hx_F i] at hF_le
    have hlt : ((i.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR <
        ((j.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR :=
      mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (by exact_mod_cast (by omega : i.1 +
        1 < j.1 + 1))
        (by positivity)) hpR_pos
    linarith
  -- Key pairwise spacing: for `i < j`, `x j - x i ≥ (j - i) / (d + 2) * (pR / w (x i))`
  have hgap : ∀ i j : Fin (d + 1), i.1 < j.1 →
      ((j.1 - i.1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR ≤ w (x i) * (x j - x i) := fun i j hij => by
    have h1 := hF_diff_le (x i) (hx_mem i) (x j) (hx_mem j) (hx_strict hij).le
    rw [hx_F j, hx_F i] at h1
    have hsub : ((j.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR -
        ((i.1 + 1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR =
        ((j.1 - i.1 : ℕ) : ℝ) / ((d + 2 : ℕ) : ℝ) * pR := by
      have : ((j.1 - i.1 : ℕ) : ℝ) = (j.1 : ℝ) - (i.1 : ℝ) := Nat.cast_sub hij.le
      rw [this]; push_cast; ring
    linarith
  -- Pointwise Lagrange bound on `|q.eval s|` for EVERY `s ∈ ℝ`
  have hq_pt : ∀ s : ℝ, |q.eval s| ≤ ε * (8 * rexp 5 * max 1 |s| / p) ^ d := by
    intro s
    set r := max 1 |s|
    have hr1 : 1 ≤ r := le_max_left _ _
    have hr_abs : |s| ≤ r := le_max_right _ _
    have hq_eq : q = Lagrange.interpolate (Finset.univ : Finset (Fin (d + 1))) x
        (fun j => q.eval (x j)) := by
      refine Lagrange.eq_interpolate (hx_strict.injective.injOn) ?_
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Polynomial.degree_le_natDegree.trans (Nat.cast_le.2 hdeg)).trans_lt
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self d))
    have heval : q.eval s = ∑ j : Fin (d + 1),
        q.eval (x j) * ∏ i ∈ Finset.univ.erase j, ((s - x i) / (x j - x i)) := by
      conv_lhs => rw [hq_eq, Lagrange.interpolate_eq_sum]
      rw [← Polynomial.coe_evalRingHom, map_sum]
      simp only [Polynomial.coe_evalRingHom]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_div_distrib, div_mul_eq_mul_div, mul_div_assoc]
    -- Bound each factor `|(s - x i) / (x j - x i)|`
    have hfac : ∀ j : Fin (d + 1), ∀ i ∈ Finset.univ.erase j,
        |(s - x i) / (x j - x i)| ≤
          (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) / |(j.1 : ℝ) - (i.1 : ℝ)| := by
      intro j i hi
      have hij : i ≠ j := (Finset.mem_erase.1 hi).1
      have hMpR : 1 / 2 ≤ M / pR := by
        rw [le_div_iff₀ hpR_pos]; linarith
      have hw_mul : ∀ u ∈ Icc 0 B, (1 + u) * w u ≤ M * rexp 1 := fun u hu => by
        have hdec := hw_decay u ⟨hA.trans hu.1, hu.2⟩
        rw [abs_of_nonneg hu.1] at hdec
        have h1u : 1 + u ≤ rexp u := by linarith [Real.add_one_le_exp u]
        calc (1 + u) * w u ≤ (1 + u) * (M * rexp (1 - u)) :=
              mul_le_mul_of_nonneg_left hdec (by linarith [hu.1])
          _ ≤ rexp u * (M * rexp (1 - u)) :=
              mul_le_mul_of_nonneg_right h1u (by positivity)
          _ = M * (rexp u * rexp (1 - u)) := by ring
          _ = M * rexp 1 := by rw [← Real.exp_add]; congr 2; ring
      have hsxi : |s - x i| ≤ r * (1 + x i) := by
        calc |s - x i| ≤ |s| + |x i| := abs_sub _ _
          _ = |s| + x i := by rw [abs_of_nonneg (hx_mem i).1]
          _ ≤ r + r * x i := by nlinarith [(hx_mem i).1]
          _ = r * (1 + x i) := by ring
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
      · -- Case `i < j`
        have hg := hgap i j hlt
        have hdiff_pos : 0 < x j - x i := sub_pos.2 (hx_strict hlt)
        have hji_pos : 0 < (j.1 : ℝ) - (i.1 : ℝ) := sub_pos.2 (Nat.cast_lt.2 hlt)
        have hcast : ((j.1 - i.1 : ℕ) : ℝ) = (j.1 : ℝ) - (i.1 : ℝ) := Nat.cast_sub hlt.le
        rw [hcast] at hg
        rw [abs_div, abs_of_pos hdiff_pos, abs_of_pos hji_pos, div_le_div_iff₀ hdiff_pos hji_pos]
        have hwi_pos : 0 < w (x i) := hw_pos (x i) ⟨hA.trans (hx_mem i).1, (hx_mem i).2⟩
        have h1 : |s - x i| * w (x i) ≤ r * (M * rexp 1) :=
          (mul_le_mul_of_nonneg_right hsxi hwi_pos.le).trans
            (by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (hw_mul (x i) (hx_mem i)) (by positivity))
        have hstep : |s - x i| * ((j.1 : ℝ) - (i.1 : ℝ)) * w (x i) ≤
            (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) * (w (x i) * (x j - x i)) := by
          calc
            |s - x i| * ((j.1 : ℝ) - (i.1 : ℝ)) * w (x i)
                = (|s - x i| * w (x i)) * ((j.1 : ℝ) - (i.1 : ℝ)) := by ring
            _ ≤ (r * (M * rexp 1)) * ((j.1 : ℝ) - (i.1 : ℝ)) :=
                  mul_le_mul_of_nonneg_right h1 hji_pos.le
            _ ≤ (2 * rexp 1 * r * M) * ((j.1 : ℝ) - (i.1 : ℝ)) := by
                  have hpos : 0 ≤ r * M * rexp 1 * ((j.1 : ℝ) - (i.1 : ℝ)) := by positivity
                  linarith
            _ = (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) *
                  (((j.1 : ℝ) - (i.1 : ℝ)) / ((d + 2 : ℕ) : ℝ) * pR) := by
                  field_simp [hpR_pos.ne', (by positivity : ((d + 2 : ℕ) : ℝ) ≠ 0)]
            _ ≤ (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) * (w (x i) * (x j - x i)) :=
                  mul_le_mul_of_nonneg_left hg (by positivity)
        have : w (x i) * (|s - x i| * ((j.1 : ℝ) - (i.1 : ℝ))) ≤
            w (x i) * (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR) * (x j - x i)) := by
          linarith
        exact le_of_mul_le_mul_left this hwi_pos
      · -- Case `j < i`
        have hg := hgap j i hgt
        have hdiff_pos : 0 < x i - x j := sub_pos.2 (hx_strict hgt)
        have hij_pos : 0 < (i.1 : ℝ) - (j.1 : ℝ) := sub_pos.2 (Nat.cast_lt.2 hgt)
        have hcast : ((i.1 - j.1 : ℕ) : ℝ) = (i.1 : ℝ) - (j.1 : ℝ) := Nat.cast_sub hgt.le
        rw [hcast] at hg
        rw [abs_div, abs_sub_comm (x j), abs_of_pos hdiff_pos, abs_sub_comm (j.1 : ℝ),
          abs_of_pos hij_pos]
        rcases le_or_gt ((1 + x i) / 2) (x i - x j) with hwide | hnarrow
        · -- Subcase A: `x i - x j ≥ (1 + x i) / 2`, so `|s - x i| / (x i - x j) ≤ 2 * r`
          have h2r : |s - x i| / (x i - x j) ≤ 2 * r := by
            rw [div_le_iff₀ hdiff_pos]
            nlinarith [hsxi, hr1]
          refine h2r.trans ?_
          rw [le_div_iff₀ hij_pos]
          have hbound_k : (i.1 : ℝ) - (j.1 : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by
            have : i.1 ≤ d := Nat.lt_succ_iff.1 i.2
            have : (i.1 : ℝ) ≤ (d : ℝ) := Nat.cast_le.2 this
            push_cast; linarith [Nat.cast_nonneg (α := ℝ) j.1]
          have he2 : (2 : ℝ) ≤ rexp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          calc
            2 * r * ((i.1 : ℝ) - (j.1 : ℝ))
                ≤ 2 * r * ((d + 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hbound_k (by positivity)
            _ ≤ 2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR) := by
                  have h1 : 1 ≤ rexp 1 * (M / pR) := by nlinarith
                  have h2 : 0 ≤ 2 * r * ((d + 2 : ℕ) : ℝ) := by positivity
                  nlinarith
        · -- Subcase B: `1 + x i < 2 * (1 + x j)`
          have h12 : 1 + x i ≤ 2 * (1 + x j) := by linarith
          have hsxj : |s - x i| ≤ 2 * r * (1 + x j) := hsxi.trans (by nlinarith)
          have hwj_pos : 0 < w (x j) := hw_pos (x j) ⟨hA.trans (hx_mem j).1, (hx_mem j).2⟩
          have h1 : |s - x i| * w (x j) ≤ 2 * r * (M * rexp 1) :=
            (mul_le_mul_of_nonneg_right hsxj hwj_pos.le).trans
              (by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left (hw_mul (x j) (hx_mem j)) (by positivity))
          rw [div_le_div_iff₀ hdiff_pos hij_pos]
          have hstep : |s - x i| * ((i.1 : ℝ) - (j.1 : ℝ)) * w (x j) ≤
              (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) * (w (x j) * (x i - x j)) := by
            calc
              |s - x i| * ((i.1 : ℝ) - (j.1 : ℝ)) * w (x j)
                  = (|s - x i| * w (x j)) * ((i.1 : ℝ) - (j.1 : ℝ)) := by ring
              _ ≤ (2 * r * (M * rexp 1)) * ((i.1 : ℝ) - (j.1 : ℝ)) :=
                    mul_le_mul_of_nonneg_right h1 hij_pos.le
              _ = (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) *
                    (((i.1 : ℝ) - (j.1 : ℝ)) / ((d + 2 : ℕ) : ℝ) * pR) := by
                    field_simp [hpR_pos.ne', (by positivity : ((d + 2 : ℕ) : ℝ) ≠ 0)]
              _ ≤ (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)) * (w (x j) * (x i - x j)) :=
                    mul_le_mul_of_nonneg_left hg (by positivity)
          have : w (x j) * (|s - x i| * ((i.1 : ℝ) - (j.1 : ℝ))) ≤
              w (x j) * (2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR) * (x i - x j)) := by
            linarith
          exact le_of_mul_le_mul_left this hwj_pos
    rw [heval]
    set K := 2 * rexp 1 * r * ((d + 2 : ℕ) : ℝ) * (M / pR)
    have hK_nn : 0 ≤ K := by positivity
    calc
      |∑ j : Fin (d + 1), q.eval (x j) * ∏ i ∈ Finset.univ.erase j, ((s - x i) / (x j - x i))|
          ≤ ∑ j : Fin (d + 1),
              |q.eval (x j)| * ∏ i ∈ Finset.univ.erase j, |(s - x i) / (x j - x i)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul, Finset.abs_prod]
      _ ≤ ∑ j : Fin (d + 1),
            ε * (K ^ d * ((j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ))⁻¹) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine mul_le_mul (hx_E j) ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hε.le
            calc
              ∏ i ∈ Finset.univ.erase j, |(s - x i) / (x j - x i)|
                  ≤ ∏ i ∈ Finset.univ.erase j, (K / |(j.1 : ℝ) - (i.1 : ℝ)|) := by
                    gcongr with i hi
                    exact hfac j i hi
              _ = (∏ _i ∈ Finset.univ.erase j, K) /
                    (∏ i ∈ Finset.univ.erase j, |(j.1 : ℝ) - (i.1 : ℝ)|) :=
                    Finset.prod_div_distrib _ _
              _ = K ^ d * ((j.1.factorial : ℝ) * ((d - j.1).factorial : ℝ))⁻¹ := by
                    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
                      Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
                      prod_abs_sub_fin_eq_factorial, div_eq_mul_inv]
      _ = ε * K ^ d * ((2 : ℝ) ^ d / (d.factorial : ℝ)) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, sum_inv_factorial_mul_factorial, mul_assoc]
      _ ≤ ε * (8 * rexp 5 * r / p) ^ d := by
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            have hMp : M / pR ≤ 2 * rexp 1 / p := by
              rw [div_le_div_iff₀ hpR_pos hp_pos]
              have : M * p ≤ rexp 1 * (2 * pR) := by nlinarith
              linarith
            have hK_rew : K ^ d * (2 ^ d / (d.factorial : ℝ)) =
                (2 * rexp 1 * r * (M / pR) * 2) ^ d * (((d : ℝ) + 2) ^ d / (d.factorial : ℝ)) := by
              have h1 : K * 2 = (2 * rexp 1 * r * (M / pR) * 2) * ((d : ℝ) + 2) := by
                unfold K; push_cast; ring
              calc K ^ d * (2 ^ d / (d.factorial : ℝ))
                  = (K * 2) ^ d / (d.factorial : ℝ) := by rw [← mul_div_assoc, ← mul_pow]
                _ = ((2 * rexp 1 * r * (M / pR) * 2) * ((d : ℝ) + 2)) ^ d / (d.factorial : ℝ) := by
                      rw [h1]
                _ = (2 * rexp 1 * r * (M / pR) * 2) ^ d *
                      (((d : ℝ) + 2) ^ d / (d.factorial : ℝ)) := by
                      rw [mul_pow, mul_div_assoc]
            have hfac_le := add_two_pow_div_factorial_le_exp_three_pow hd
            rw [hK_rew]
            calc
              (2 * rexp 1 * r * (M / pR) * 2) ^ d * (((d : ℝ) + 2) ^ d / (d.factorial : ℝ))
                  ≤ (2 * rexp 1 * r * (2 * rexp 1 / p) * 2) ^ d * (rexp 3) ^ d :=
                    mul_le_mul (pow_le_pow_left₀ (by positivity) (by
                      have h1 : 0 ≤ 2 * rexp 1 * r := by positivity
                      nlinarith) d) hfac_le (by positivity) (by positivity)
              _ = (8 * rexp 5 * r / p) ^ d := by
                    rw [← mul_pow]; congr 1
                    have he5 : rexp 1 * rexp 1 * rexp 3 = rexp 5 := by
                      rw [← Real.exp_add, ← Real.exp_add]; norm_num
                    have heq : 2 * rexp 1 * r * (2 * rexp 1 / p) * 2 * rexp 3 =
                        8 * (rexp 1 * rexp 1 * rexp 3) * r / p := by ring
                    rw [heq, he5]
  -- Square and integrate `q.eval s ^ 2 * w s` over `Icc A B`
  have hmom_bound : ∫ s in Icc A B, (max 1 |s|) ^ (2 * d) * w s ≤
    (4 * rexp 1 * (d : ℝ)) ^ (2 * d) := by
    have hpt_max : ∀ s ∈ Icc A B, (max 1 |s|) ^ (2 * d) * w s ≤ w s + |s| ^ (2 * d) * w s :=
      fun s hs => by
        have h1 : (max 1 |s|) ^ (2 * d) ≤ 1 + |s| ^ (2 * d) := by
          rcases le_total 1 |s| with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (abs_nonneg s) (2 * d)]
        nlinarith [hw_pos s hs]
    have hi_lhs : IntegrableOn (fun s => (max 1 |s|) ^ (2 * d) * w s) (Icc A B) volume :=
      (((continuous_const.max continuous_abs).pow
        (2 * d)).continuousOn.mul hw_cont).integrableOn_Icc
    have hi_abs : IntegrableOn (fun s => |s| ^ (2 * d) * w s) (Icc A B) volume :=
      ((continuous_abs.pow (2 * d)).continuousOn.mul hw_cont).integrableOn_Icc
    have h1 := setIntegral_mono_on hi_lhs (hw_cont.integrableOn_Icc.add hi_abs) measurableSet_Icc
      hpt_max
    simp only [Pi.add_apply] at h1
    rw [integral_add hw_cont.integrableOn_Icc hi_abs, hw_int] at h1
    have h2 : ∫ s in Icc A B, |s| ^ (2 * d) * w s ≤ 2 * rexp 2 * ((2 * d).factorial : ℝ) := by
      have hi_dom :
          Integrable (fun s : ℝ => M * rexp 1 * (|s| ^ (2 * d) * rexp (-|s|))) volume :=
        (integrable_abs_pow_mul_exp_neg_abs (2 * d)).const_mul (M * rexp 1)
      calc
        ∫ s in Icc A B, |s| ^ (2 * d) * w s
            ≤ ∫ s in Icc A B, M * rexp 1 * (|s| ^ (2 * d) * rexp (-|s|)) := by
              refine setIntegral_mono_on hi_abs hi_dom.integrableOn measurableSet_Icc fun s hs => ?_
              have hdec := hw_decay s hs
              rw [sub_eq_add_neg, Real.exp_add] at hdec
              calc |s| ^ (2 * d) * w s ≤ |s| ^ (2 * d) * (M * (rexp 1 * rexp (-|s|))) :=
                    mul_le_mul_of_nonneg_left hdec (pow_nonneg (abs_nonneg s) _)
                _ = M * rexp 1 * (|s| ^ (2 * d) * rexp (-|s|)) := by ring
        _ ≤ ∫ s : ℝ, M * rexp 1 * (|s| ^ (2 * d) * rexp (-|s|)) :=
              setIntegral_le_integral hi_dom (ae_of_all _ fun _ => by positivity)
        _ = M * rexp 1 * (2 * ((2 * d).factorial : ℝ)) := by
              rw [integral_const_mul, integral_abs_pow_mul_exp_neg_abs]
        _ ≤ rexp 1 * rexp 1 * (2 * ((2 * d).factorial : ℝ)) := by gcongr
        _ = 2 * rexp 2 * ((2 * d).factorial : ℝ) := by
              rw [← Real.exp_add]; norm_num; ring
    have hfac_le : ((2 * d).factorial : ℝ) ≤ (2 * (d : ℝ)) ^ (2 * d) := by
      exact_mod_cast Nat.factorial_le_pow (2 * d)
    have h1_le : (1 : ℝ) ≤ (2 * (d : ℝ)) ^ (2 * d) :=
      one_le_pow₀ (by have : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd; linarith)
    have he_ineq : 1 + 2 * rexp 2 ≤ (2 * rexp 1) ^ (2 * d) := by
      have hsq : 1 + 2 * rexp 2 ≤ (2 * rexp 1) ^ 2 := by
        have he2 : rexp 2 = rexp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
        have he1 : (2 : ℝ) ≤ rexp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        rw [he2]; nlinarith
      have hbase : (1 : ℝ) ≤ 2 * rexp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact hsq.trans (pow_le_pow_right₀ hbase (by omega))
    calc
      ∫ s in Icc A B, (max 1 |s|) ^ (2 * d) * w s
          ≤ 1 + 2 * rexp 2 * ((2 * d).factorial : ℝ) := by linarith
      _ ≤ (1 + 2 * rexp 2) * (2 * (d : ℝ)) ^ (2 * d) := by
            have := mul_le_mul_of_nonneg_left hfac_le (by positivity : 0 ≤ 2 * rexp 2)
            linarith
      _ ≤ (2 * rexp 1) ^ (2 * d) * (2 * (d : ℝ)) ^ (2 * d) :=
            mul_le_mul_of_nonneg_right he_ineq (by positivity)
      _ = (4 * rexp 1 * (d : ℝ)) ^ (2 * d) := by rw [← mul_pow]; congr 1; ring
  have hi_q : IntegrableOn (fun s => q.eval s ^ 2 * w s) (Icc A B) volume :=
    ((q.continuous.pow 2).continuousOn.mul hw_cont).integrableOn_Icc
  have hi_max : IntegrableOn (fun s => (max 1 |s|) ^ (2 * d) * w s) (Icc A B) volume :=
    (((continuous_const.max continuous_abs).pow (2 * d)).continuousOn.mul hw_cont).integrableOn_Icc
  have hsq_pt : ∀ s ∈ Icc A B, q.eval s ^ 2 * w s ≤
      (ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d)) * ((max 1 |s|) ^ (2 * d) * w s) := fun s hs => by
    have hq2 : q.eval s ^ 2 ≤ ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d) * (max 1 |s|) ^ (2 * d) := by
      rw [← sq_abs (q.eval s)]
      calc |q.eval s| ^ 2 ≤ (ε * (8 * rexp 5 * max 1 |s| / p) ^ d) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hq_pt s) 2
        _ = ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d) * (max 1 |s|) ^ (2 * d) := by
            rw [mul_pow, ← pow_mul, mul_comm d 2, mul_div_right_comm, mul_pow]; ring
    calc q.eval s ^ 2 * w s
        ≤ (ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d) * (max 1 |s|) ^ (2 * d)) * w s :=
          mul_le_mul_of_nonneg_right hq2 (hw_pos s hs).le
      _ = (ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d)) * ((max 1 |s|) ^ (2 * d) * w s) := by ring
  calc
    ∫ s in Icc A B, q.eval s ^ 2 * w s
        ≤ ∫ s in Icc A B, (ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d)) * ((max 1 |s|) ^ (2 * d) * w s) :=
          setIntegral_mono_on hi_q (hi_max.const_mul _) measurableSet_Icc hsq_pt
    _ = ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d) * ∫ s in Icc A B, (max 1 |s|) ^ (2 * d) * w s :=
          integral_const_mul _ _
    _ ≤ ε ^ 2 * (8 * rexp 5 / p) ^ (2 * d) * (4 * rexp 1 * (d : ℝ)) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hmom_bound (by positivity)
    _ = ε ^ 2 * (32 * rexp 6 * (d : ℝ) / p) ^ (2 * d) := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          have he6 : rexp 5 * rexp 1 = rexp 6 := by rw [← Real.exp_add]; norm_num
          rw [div_mul_eq_mul_div]; congr 1
          calc 8 * rexp 5 * (4 * rexp 1 * (d : ℝ)) = 32 * (rexp 5 * rexp 1) * (d : ℝ) := by ring
            _ = 32 * rexp 6 * (d : ℝ) := by rw [he6]

/-- **One-Dimensional Compact Log-Concave Carbery–Wright Inequality**:
for any continuous strictly positive log-concave probability density `w` on `[a, b]` (`a < b`),
any univariate polynomial `q` of degree at most `d` (`1 ≤ d`), and any `ε > 0`, if
`V = ∫_{Icc a b} q(t)^2 w(t) dt > 0`, then
`∫_{Icc a b} 1_{|q(t)| ≤ ε} w(t) dt ≤ (32 * exp 6) * d * (ε / √V)^(1/d)`. -/
theorem carbery_wright_1d_compact {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Icc a b)) (hw_pos : ∀ t ∈ Icc a b, 0 < w t)
    (hw_lc : ConcaveOn ℝ (Icc a b) (fun t => Real.log (w t)))
    (hw_int : ∫ t in Icc a b, w t = 1)
    {q : ℝ[X]} {d : ℕ} (hd : 1 ≤ d) (hdeg : q.natDegree ≤ d)
    {ε : ℝ} (hε : 0 < ε)
    (hV_pos : 0 < ∫ t in Icc a b, q.eval t ^ 2 * w t) :
    (∫ t in Icc a b, if |q.eval t| ≤ ε then w t else 0) ≤
      (32 * rexp 6) * (d : ℝ) * (ε / √(∫ t in Icc a b, q.eval t ^ 2 * w t)) ^ (1 / (d : ℝ)) := by
  set V := ∫ t in Icc a b, q.eval t ^ 2 * w t
  set p := ∫ t in Icc a b, if |q.eval t| ≤ ε then w t else 0
  rcases le_or_gt p 0 with hp0 | hp_pos
  · exact hp0.trans (by positivity)
  -- Translate mode `m ∈ [a, b]` to `0`
  obtain ⟨m, hm_mem, hm_max⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab.le) hw_cont
  set a₁ := a - m
  set b₁ := b - m
  have hab₁ : a₁ < b₁ := by unfold a₁ b₁; linarith
  have ha₁0 : a₁ ≤ 0 := by unfold a₁; linarith [hm_mem.1]
  have hb₁0 : 0 ≤ b₁ := by unfold b₁; linarith [hm_mem.2]
  set w₁ : ℝ → ℝ := fun u => w (m + u)
  have hw₁_cont : ContinuousOn w₁ (Icc a₁ b₁) :=
    hw_cont.comp (continuousOn_const.add continuousOn_id) fun u hu =>
      ⟨by unfold a₁ at hu; linarith [hu.1], by unfold b₁ at hu; linarith [hu.2]⟩
  have hw₁_pos : ∀ u ∈ Icc a₁ b₁, 0 < w₁ u := fun u hu =>
    hw_pos (m + u) ⟨by unfold a₁ at hu; linarith [hu.1], by unfold b₁ at hu; linarith [hu.2]⟩
  have hw₁_lc : ConcaveOn ℝ (Icc a₁ b₁) (fun u => Real.log (w₁ u)) := by
    refine ⟨convex_Icc a₁ b₁, fun x hx y hy α β hα hβ hαβ => ?_⟩
    have hx' : m + x ∈ Icc a b :=
      ⟨by unfold a₁ at hx; linarith [hx.1], by unfold b₁ at hx; linarith [hx.2]⟩
    have hy' : m + y ∈ Icc a b :=
      ⟨by unfold a₁ at hy; linarith [hy.1], by unfold b₁ at hy; linarith [hy.2]⟩
    have hpt : m + (α • x + β • y) = α • (m + x) + β • (m + y) := by
      simp only [smul_eq_mul]; linear_combination -m * hαβ
    simpa only [w₁, hpt] using hw_lc.2 hx' hy' hα hβ hαβ
  have hw₁_max : ∀ u ∈ Icc a₁ b₁, w₁ u ≤ w₁ 0 := fun u hu => by
    simpa [w₁] using hm_max ⟨by unfold a₁ at hu; linarith [hu.1],
      by unfold b₁ at hu; linarith [hu.2]⟩
  have hw₁_int : ∫ u in Icc a₁ b₁, w₁ u = 1 := by
    rw [← hw_int]; unfold w₁ a₁ b₁
    simpa [sub_eq_add_neg] using integral_comp_add_left_Icc w m (a - m) (b - m)
  obtain ⟨hanti₁, hmono₁, L, hL_pos, hML_lo, hML_hi, hdecay₁⟩ :=
    logConcave_mode_bounds hab₁ ha₁0 hb₁0 hw₁_cont hw₁_pos hw₁_lc hw₁_max hw₁_int
  -- Rescale by `L` so `A = a₁ / L ≤ 0 ≤ b₁ / L = B`
  set A := a₁ / L
  set B := b₁ / L
  have hA0 : A ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha₁0 hL_pos.le
  have hB0 : 0 ≤ B := div_nonneg hb₁0 hL_pos.le
  set w₂ : ℝ → ℝ := fun s => L * w₁ (L * s)
  set q₂ : ℝ[X] := q.comp (C m + C L * X)
  have hq₂_eval : ∀ s : ℝ, q₂.eval s = q.eval (m + L * s) := fun s => by
    simp [q₂, Polynomial.eval_comp]
  have hq₂_deg : q₂.natDegree ≤ d := by
    have hlin : (C m + C L * X : ℝ[X]).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    exact (Polynomial.natDegree_comp_le).trans (by nlinarith)
  have hw₂_cont : ContinuousOn w₂ (Icc A B) :=
    continuousOn_const.mul (hw₁_cont.comp (continuousOn_const.mul continuousOn_id) fun s hs =>
      ⟨(div_le_iff₀ hL_pos).1 hs.1 |>.trans_eq (mul_comm _ _),
        (le_div_iff₀ hL_pos).1 hs.2 |>.trans_eq' (mul_comm _ _)⟩)
  have hw₂_pos : ∀ s ∈ Icc A B, 0 < w₂ s := fun s hs =>
    mul_pos hL_pos (hw₁_pos (L * s)
      ⟨(div_le_iff₀ hL_pos).1 hs.1 |>.trans_eq (mul_comm _ _),
        (le_div_iff₀ hL_pos).1 hs.2 |>.trans_eq' (mul_comm _ _)⟩)
  have hw₂_int : ∫ s in Icc A B, w₂ s = 1 := by
    rw [← hw₁_int]
    have h := integral_comp_mul_left_Icc w₁ hL_pos A B
    rw [mul_div_cancel₀ _ hL_pos.ne', mul_div_cancel₀ _ hL_pos.ne'] at h
    unfold w₂
    rw [integral_const_mul, h, mul_inv_cancel_left₀ hL_pos.ne']
  have hscale_any : ∀ g : ℝ → ℝ, ∫ s in Icc A B, g (m + L * s) * w₂ s =
      ∫ t in Icc a b, g t * w t := fun g => by
    have h1 := integral_comp_mul_left_Icc (fun u => g (m + u) * w₁ u) hL_pos A B
    rw [mul_div_cancel₀ _ hL_pos.ne', mul_div_cancel₀ _ hL_pos.ne'] at h1
    have h2 : ∫ s in Icc A B, g (m + L * s) * w₂ s =
        ∫ u in Icc a₁ b₁, g (m + u) * w₁ u := by
      have heq : (fun s => g (m + L * s) * w₂ s) = fun s => L * (g (m + L * s) * w₁ (L * s)) :=
        funext fun s => by unfold w₂; ring
      rw [heq, integral_const_mul, h1, mul_inv_cancel_left₀ hL_pos.ne']
    rw [h2]
    simpa [a₁, b₁, w₁, sub_eq_add_neg] using
      integral_comp_add_left_Icc (fun t => g t * w t) m (a - m) (b - m)
  have hV_eq : ∫ s in Icc A B, q₂.eval s ^ 2 * w₂ s = V := by
    simp_rw [hq₂_eval]; exact hscale_any (fun t => q.eval t ^ 2)
  have hp_eq : ∫ s in Icc A B, (if |q₂.eval s| ≤ ε then w₂ s else 0) = p := by
    have hrew : ∀ s, (if |q₂.eval s| ≤ ε then w₂ s else 0) =
        (if |q.eval (m + L * s)| ≤ ε then (1 : ℝ) else 0) * w₂ s := fun s => by
      rw [hq₂_eval]; split_ifs <;> ring
    have hrew' : ∀ t, (if |q.eval t| ≤ ε then w t else 0) =
        (if |q.eval t| ≤ ε then (1 : ℝ) else 0) * w t := fun t => by split_ifs <;> ring
    simp_rw [hrew]
    rw [hscale_any (fun t => if |q.eval t| ≤ ε then 1 else 0)]
    simp_rw [← hrew']
    rfl
  -- Split `p` into `[A, 0]` and `[0, B]`, and reduce to `carbery_wright_1d_normalized`
  have hV_bound : V ≤ ε ^ 2 * (32 * rexp 6 * (d : ℝ) / p) ^ (2 * d) := by
    have hfE_int : IntegrableOn (fun s => if |q₂.eval s| ≤
      ε then w₂ s else 0) (Icc A B) volume := by
      refine hw₂_cont.integrableOn_Icc.mono' ?_
        (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
      · exact ((hw₂_cont.aestronglyMeasurable measurableSet_Icc).indicator
          (isClosed_le q₂.continuous.abs continuous_const :
            IsClosed {s : ℝ | |q₂.eval s| ≤ ε}).measurableSet).congr
            (ae_of_all _ fun s => by simp [Set.indicator_apply])
      · simp only [Real.norm_eq_abs]; split_ifs
        · exact le_of_eq (abs_of_pos (hw₂_pos s hs))
        · rw [abs_zero]; exact (hw₂_pos s hs).le
    have hsplit : Icc A B = Icc A 0 ∪ Ioc 0 B := (Set.Icc_union_Ioc_eq_Icc hA0 hB0).symm
    have hp_sum : p = (∫ s in Icc A 0, if |q₂.eval s| ≤ ε then w₂ s else 0) +
        (∫ s in Icc 0 B, if |q₂.eval s| ≤ ε then w₂ s else 0) := by
      rw [← hp_eq, hsplit, setIntegral_union Icc_disjoint_Ioc_self measurableSet_Ioc
        (hfE_int.mono_set fun s hs => ⟨hs.1, hs.2.trans hB0⟩)
        (hfE_int.mono_set fun s hs => ⟨hA0.trans hs.1.le, hs.2⟩),
        ← integral_Icc_eq_integral_Ioc]
    have hM₂_eq : w₂ 0 = w₁ 0 * L := by unfold w₂; simp [mul_comm]
    have hdecay₂ : ∀ s ∈ Icc A B, w₂ s ≤ w₂ 0 * rexp (1 - |s|) := fun s hs => by
      have h1 := hdecay₁ (L * s)
        ⟨(div_le_iff₀ hL_pos).1 hs.1 |>.trans_eq (mul_comm _ _),
          (le_div_iff₀ hL_pos).1 hs.2 |>.trans_eq' (mul_comm _ _)⟩
      rw [abs_mul, abs_of_pos hL_pos, mul_div_cancel_left₀ _ hL_pos.ne'] at h1
      calc w₂ s = L * w₁ (L * s) := rfl
        _ ≤ L * (w₁ 0 * rexp (1 - |s|)) := mul_le_mul_of_nonneg_left h1 hL_pos.le
        _ = w₂ 0 * rexp (1 - |s|) := by unfold w₂; simp; ring
    rcases le_total (∫ s in Icc A 0, if |q₂.eval s| ≤ ε then w₂ s else 0)
        (∫ s in Icc 0 B, if |q₂.eval s| ≤ ε then w₂ s else 0) with hR | hL
    · have hpR : p / 2 ≤ ∫ s in Icc 0 B, if |q₂.eval s| ≤ ε then w₂ s else 0 := by linarith
      have hB_pos : 0 < B := by
        rcases eq_or_lt_of_le hB0 with h0 | hpos
        · exfalso; rw [← h0] at hpR; simp at hpR; linarith
        · exact hpos
      have hanti₂ : AntitoneOn w₂ (Icc 0 B) := fun x hx y hy hxy =>
        mul_le_mul_of_nonneg_left (hanti₁
          ⟨mul_nonneg hL_pos.le hx.1, (le_div_iff₀ hL_pos).1 hx.2 |>.trans_eq' (mul_comm _ _)⟩
          ⟨mul_nonneg hL_pos.le hy.1, (le_div_iff₀ hL_pos).1 hy.2 |>.trans_eq' (mul_comm _ _)⟩
          (mul_le_mul_of_nonneg_left hxy hL_pos.le)) hL_pos.le
      rw [← hV_eq]
      exact carbery_wright_1d_normalized hA0 hB_pos hw₂_cont hw₂_pos hanti₂ hw₂_int
        (by rw [hM₂_eq]; exact hML_lo) (by rw [hM₂_eq]; exact hML_hi) hdecay₂ hd hq₂_deg hε
        hp_pos hpR
    · -- Reflect `s ↦ -s`
      have hpL : p / 2 ≤ ∫ s in Icc A 0, if |q₂.eval s| ≤ ε then w₂ s else 0 := by linarith
      have hA_neg : A < 0 := by
        rcases eq_or_lt_of_le hA0 with h0 | hneg
        · exfalso; rw [h0] at hpL; simp at hpL; linarith
        · exact hneg
      set w₃ : ℝ → ℝ := fun s => w₂ (-s)
      set q₃ : ℝ[X] := q₂.comp (-X)
      have hq₃_eval : ∀ s, q₃.eval s = q₂.eval (-s) := fun s => by simp [q₃]
      have hq₃_deg : q₃.natDegree ≤ d :=
        Polynomial.natDegree_comp_le.trans (by simp [hq₂_deg])
      have hw₃_cont : ContinuousOn w₃ (Icc (-B) (-A)) :=
        hw₂_cont.comp continuousOn_neg fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hw₃_pos : ∀ s ∈ Icc (-B) (-A), 0 < w₃ s := fun s hs =>
        hw₂_pos (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hanti₃ : AntitoneOn w₃ (Icc 0 (-A)) := fun x hx y hy hxy =>
        mul_le_mul_of_nonneg_left (hmono₁
          ⟨by have := (div_le_iff₀ hL_pos).1 (show A ≤ -y by linarith [hy.2]); nlinarith,
            by nlinarith [hy.1]⟩
          ⟨by have := (div_le_iff₀ hL_pos).1 (show A ≤ -x by linarith [hx.2]); nlinarith,
            by nlinarith [hx.1]⟩
          (by nlinarith)) hL_pos.le
      have hw₃_int : ∫ s in Icc (-B) (-A), w₃ s = 1 := by
        rw [← hw₂_int]; simpa [w₃] using integral_comp_neg_Icc w₂ (-B) (-A)
      have hdecay₃ : ∀ s ∈ Icc (-B) (-A), w₃ s ≤ w₃ 0 * rexp (1 - |s|) := fun s hs => by
        simpa [w₃, abs_neg] using hdecay₂ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hpR₃ : p / 2 ≤ ∫ s in Icc 0 (-A), if |q₃.eval s| ≤ ε then w₃ s else 0 := by
        have hcomp := integral_comp_neg_Icc
          (fun s => if |q₂.eval s| ≤ ε then w₂ s else 0) 0 (-A)
        simp only [neg_zero, neg_neg] at hcomp
        simp_rw [hq₃_eval, w₃]; linarith
      have hV₃ : ∫ s in Icc (-B) (-A), q₃.eval s ^ 2 * w₃ s = V := by
        rw [← hV_eq]
        simp_rw [hq₃_eval, w₃]
        simpa using integral_comp_neg_Icc (fun s => q₂.eval s ^ 2 * w₂ s) (-B) (-A)
      rw [← hV₃]
      exact carbery_wright_1d_normalized (by linarith) (by linarith) hw₃_cont hw₃_pos hanti₃
        hw₃_int (by simp only [w₃, neg_zero, hM₂_eq]; exact hML_lo)
        (by simp only [w₃, neg_zero, hM₂_eq]; exact hML_hi)
        hdecay₃ hd hq₃_deg hε hp_pos hpR₃
  -- Take `(2 * d)`-th root of `V ≤ ε^2 * (32 * exp 6 * d / p)^(2 * d)`
  have hsqrt : √V ≤ ε * (32 * rexp 6 * (d : ℝ) / p) ^ d := by
    have hrew : ε ^ 2 * (32 * rexp 6 * (d : ℝ) / p) ^ (2 * d) =
        (ε * (32 * rexp 6 * (d : ℝ) / p) ^ d) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm d 2]
    rw [hrew] at hV_bound
    exact (Real.sqrt_le_sqrt hV_bound).trans_eq (Real.sqrt_sq (by positivity))
  have hdiv : (ε / √V)⁻¹ ≤ (32 * rexp 6 * (d : ℝ) / p) ^ d := by
    rw [inv_div, div_le_iff₀ hε]
    linarith [mul_comm ε ((32 * rexp 6 * (d : ℝ) / p) ^ d)]
  have hpow : p ^ d ≤ ((32 * rexp 6) * (d : ℝ)) ^ d * (ε / √V) := by
    have h1 : √V / ε ≤ (32 * rexp 6 * (d : ℝ)) ^ d / p ^ d := by
      rwa [inv_div, div_pow] at hdiv
    rw [div_le_div_iff₀ hε (pow_pos hp_pos d)] at h1
    rw [← mul_div_assoc, le_div_iff₀ (Real.sqrt_pos.2 hV_pos)]
    linarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 (by omega)
  have hrpow := Real.rpow_le_rpow (pow_nonneg hp_pos.le d) hpow (by positivity : 0 ≤ 1 / (d : ℝ))
  rw [← Real.rpow_natCast p d, ← Real.rpow_mul hp_pos.le,
    mul_one_div_cancel hd_pos.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast ((32 * rexp 6) * (d : ℝ)) d,
    ← Real.rpow_mul (by positivity), mul_one_div_cancel hd_pos.ne', Real.rpow_one] at hrpow
  exact hrpow

/-- **One-Dimensional Standard Gaussian Carbery–Wright Inequality**:
for any univariate polynomial `q` of degree at most `d` (`1 ≤ d`), `ε > 0`, and
`V = ∫ x, q(x)^2 ∂gaussianReal 0 1 > 0`,
`(gaussianReal 0 1).real {x | |q.eval x| ≤ ε} ≤ (32 * exp 6) * d * (ε / √V)^(1/d)`. -/
theorem carbery_wright_1d_gaussian {q : ℝ[X]} {d : ℕ} (hd : 1 ≤ d) (hdeg : q.natDegree ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hV_pos : 0 < ∫ x, q.eval x ^ 2 ∂gaussianReal 0 1) :
    (gaussianReal 0 1).real {x | |q.eval x| ≤ ε} ≤
      (32 * rexp 6) * (d : ℝ) *
        (ε / √(∫ x, q.eval x ^ 2 ∂gaussianReal 0 1)) ^ (1 / (d : ℝ)) := by
  set φ := gaussianPDFReal 0 1
  have hφ_pos : ∀ x, 0 < φ x := fun x => gaussianPDFReal_pos 0 1 x one_ne_zero
  have hφ_cont : Continuous φ := continuous_gaussianPDFReal 0 1
  have hφ_lc : ConcaveOn ℝ Set.univ (fun x => Real.log (φ x)) := by
    have heq : (fun x => Real.log (φ x)) = fun x => -Real.log √(2 * π) - x ^ 2 / 2 :=
      funext fun x => by
        simp only [φ, gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
        rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
        ring
    rw [heq]
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hsq : (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
      have h1 : a * b * (x - y) ^ 2 ≥ 0 := by positivity
      have h2 : a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2 =
          a * (1 - a) * x ^ 2 + b * (1 - b) * y ^ 2 - 2 * a * b * x * y := by ring
      have h3 : 1 - a = b := by linarith
      have h4 : 1 - b = a := by linarith
      rw [h3, h4] at h2
      nlinarith
    linarith [show a * (-Real.log √(2 * π)) + b * (-Real.log √(2 * π)) =
      -Real.log √(2 * π) by linear_combination -Real.log √(2 * π) * hab]
  have hq2_int : Integrable (fun x => q.eval x ^ 2 * φ x) volume := by
    have hp : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k * φ x) volume := fun k => by
      have hall := integrable_abs_pow_mul_exp_neg_abs k
      refine (hall.const_mul ((√(2 * π))⁻¹ * rexp (1 / 2))).mono'
        ((continuous_pow k).mul hφ_cont).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (hφ_pos x)]
      have hφ_le : φ x ≤ (√(2 * π))⁻¹ * rexp (1 / 2) * rexp (-|x|) := by
        simp only [φ, gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
        rw [mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      calc |x| ^ k * φ x ≤ |x| ^ k * ((√(2 * π))⁻¹ * rexp (1 / 2) * rexp (-|x|)) :=
            mul_le_mul_of_nonneg_left hφ_le (by positivity)
        _ = (√(2 * π))⁻¹ * rexp (1 / 2) * (|x| ^ k * rexp (-|x|)) := by ring
    simp_rw [Polynomial.eval_eq_sum_range]
    have : ∀ x : ℝ, (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * x ^ i) ^ 2 * φ x =
        ∑ i ∈ Finset.range (q.natDegree + 1), ∑ j ∈ Finset.range (q.natDegree + 1),
          (q.coeff i * q.coeff j) * (x ^ (i + j) * φ x) := fun x => by
      rw [sq, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
    simp_rw [this]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hp (i + j)).const_mul _
  have hE_int : Integrable (fun x => if |q.eval x| ≤ ε then φ x else 0) volume := by
    have hφ_int : Integrable φ volume := integrable_gaussianPDFReal 0 1
    refine hφ_int.mono' ?_ (ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs]; split_ifs
      · exact le_of_eq (abs_of_pos (hφ_pos x))
      · rw [abs_zero]; exact (hφ_pos x).le)
    exact (hφ_cont.aestronglyMeasurable.indicator
      (isClosed_le q.continuous.abs continuous_const :
        IsClosed {x : ℝ | |q.eval x| ≤ ε}).measurableSet).congr
        (ae_of_all _ fun x => by simp [Set.indicator_apply])
  have hφ_int1 : ∫ x : ℝ, φ x = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have hV_eq : ∫ x, q.eval x ^ 2 ∂gaussianReal 0 1 = ∫ x, q.eval x ^ 2 * φ x := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    refine integral_congr_ae (ae_of_all _ fun x => by simp [φ, smul_eq_mul, mul_comm])
  have hp_eq : (gaussianReal 0 1).real {x | |q.eval x| ≤ ε} =
      ∫ x, if |q.eval x| ≤ ε then φ x else 0 := by
    have hmeas : MeasurableSet {x : ℝ | |q.eval x| ≤ ε} :=
      (isClosed_le q.continuous.abs continuous_const).measurableSet
    rw [← integral_indicator_one hmeas, integral_gaussianReal_eq_integral_smul one_ne_zero]
    refine integral_congr_ae (ae_of_all _ fun x => by
      simp [φ, Set.indicator_apply, smul_eq_mul])
  -- Pass to limit `R → ∞` over `Icc (-R) R`
  have hlim_Z : Tendsto (fun R : ℝ => ∫ x in Icc (-R) R, φ x) atTop (𝓝 1) := by
    rw [← hφ_int1]
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun R x => (Icc (-R) R).indicator φ x) (f := φ) (bound := φ)
      (Eventually.of_forall fun R => hφ_cont.aestronglyMeasurable.indicator measurableSet_Icc)
      (Eventually.of_forall fun R => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; by_cases hx : x ∈ Icc (-R) R <;>
          simp [hx, abs_of_pos (hφ_pos x), (hφ_pos x).le])
      (integrable_gaussianPDFReal 0 1)
      (ae_of_all _ fun x => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop |x|] with R hR
        rw [Set.indicator_of_mem (abs_le.1 hR)]))
    exact ht.congr fun R => integral_indicator measurableSet_Icc
  have hlim_V : Tendsto (fun R : ℝ => ∫ x in Icc (-R) R, q.eval x ^ 2 * φ x) atTop
      (𝓝 (∫ x, q.eval x ^ 2 * φ x)) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun R x => (Icc (-R) R).indicator (fun x => q.eval x ^ 2 * φ x) x)
      (f := fun x => q.eval x ^ 2 * φ x) (bound := fun x => q.eval x ^ 2 * φ x)
      (Eventually.of_forall fun R => hq2_int.aestronglyMeasurable.indicator measurableSet_Icc)
      (Eventually.of_forall fun R => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; by_cases hx : x ∈ Icc (-R) R <;>
          simp [hx, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hφ_pos x).le),
            mul_nonneg (sq_nonneg _) (hφ_pos x).le])
      hq2_int
      (ae_of_all _ fun x => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop |x|] with R hR
        rw [Set.indicator_of_mem (abs_le.1 hR)]))
    exact ht.congr fun R => integral_indicator measurableSet_Icc
  have hlim_p : Tendsto (fun R : ℝ => ∫ x in Icc (-R) R, if |q.eval x| ≤ ε then φ x else 0) atTop
      (𝓝 (∫ x, if |q.eval x| ≤ ε then φ x else 0)) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun R x => (Icc (-R) R).indicator (fun x => if |q.eval x| ≤ ε then φ x else 0) x)
      (f := fun x => if |q.eval x| ≤ ε then φ x else 0) (bound := φ)
      (Eventually.of_forall fun R => hE_int.aestronglyMeasurable.indicator measurableSet_Icc)
      (Eventually.of_forall fun R => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; by_cases hx : x ∈ Icc (-R) R
        · rw [Set.indicator_of_mem hx]; split_ifs
          · exact le_of_eq (abs_of_pos (hφ_pos x))
          · rw [abs_zero]; exact (hφ_pos x).le
        · rw [Set.indicator_of_notMem hx, abs_zero]; exact (hφ_pos x).le)
      (integrable_gaussianPDFReal 0 1)
      (ae_of_all _ fun x => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop |x|] with R hR
        rw [Set.indicator_of_mem (abs_le.1 hR)]))
    exact ht.congr fun R => integral_indicator measurableSet_Icc
  rw [hp_eq, hV_eq]
  rw [hV_eq] at hV_pos
  have hlim_lhs : Tendsto
      (fun R : ℝ => (∫ x in Icc (-R) R, if |q.eval x| ≤ ε then φ x else 0) /
        (∫ x in Icc (-R) R, φ x)) atTop
      (𝓝 (∫ x, if |q.eval x| ≤ ε then φ x else 0)) := by
    have h := (hlim_p.div hlim_Z one_ne_zero).congr
      (f₂ := fun R : ℝ => (∫ x in Icc (-R) R, if |q.eval x| ≤ ε then φ x else 0) /
        (∫ x in Icc (-R) R, φ x)) (fun _ => rfl)
    rwa [div_one] at h
  have hlim_rhs : Tendsto
      (fun R : ℝ => (32 * rexp 6) * (d : ℝ) *
        (ε / √((∫ x in Icc (-R) R, q.eval x ^ 2 * φ x) / (∫ x in Icc (-R) R, φ x))) ^
          (1 / (d : ℝ))) atTop
      (𝓝 ((32 * rexp 6) * (d : ℝ) * (ε / √(∫ x, q.eval x ^ 2 * φ x)) ^ (1 / (d : ℝ)))) := by
    have hVdiv : Tendsto (fun R : ℝ => (∫ x in Icc (-R) R, q.eval x ^ 2 * φ x) /
        (∫ x in Icc (-R) R, φ x)) atTop (𝓝 (∫ x, q.eval x ^ 2 * φ x)) := by
      have h := (hlim_V.div hlim_Z one_ne_zero).congr
        (f₂ := fun R : ℝ => (∫ x in Icc (-R) R, q.eval x ^ 2 * φ x) / (∫ x in Icc (-R) R, φ x))
        (fun _ => rfl)
      rwa [div_one] at h
    have hrat := (tendsto_const_nhds (x := ε)).div (hVdiv.sqrt) (Real.sqrt_pos.2 hV_pos).ne'
    have hrpow := hrat.rpow_const (p :=
      1 / (d : ℝ)) (Or.inl (div_pos hε (Real.sqrt_pos.2 hV_pos)).ne')
    exact tendsto_const_nhds.mul hrpow
  refine le_of_tendsto_of_tendsto hlim_lhs hlim_rhs ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlim_Z.eventually (Ioi_mem_nhds zero_lt_one),
    hlim_V.eventually (Ioi_mem_nhds hV_pos)] with R hR hZ_pos hVR_pos
  set Z := ∫ x in Icc (-R) R, φ x
  set wR : ℝ → ℝ := fun x => φ x / Z
  have hwR_int : ∫ x in Icc (-R) R, wR x = 1 := by
    simp only [wR, integral_div]; exact div_self hZ_pos.ne'
  have hwR_lc : ConcaveOn ℝ (Icc (-R) R) (fun x => Real.log (wR x)) := by
    refine ⟨convex_Icc (-R) R, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [wR, Real.log_div (hφ_pos _).ne' hZ_pos.ne', smul_eq_mul]
    have h := hφ_lc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h
    linarith [show a * Real.log Z + b * Real.log Z = Real.log Z by
      linear_combination Real.log Z * hab]
  have hcw := carbery_wright_1d_compact (a := -R) (b := R) (by linarith)
    (hφ_cont.continuousOn.div_const Z) (fun x _ => div_pos (hφ_pos x) hZ_pos) hwR_lc hwR_int
    hd hdeg hε (by
      have heq : ∫ x in Icc (-R) R, q.eval x ^ 2 * wR x =
          (∫ x in Icc (-R) R, q.eval x ^ 2 * φ x) / Z := by
        simp only [wR, ← mul_div_assoc, integral_div]
      rw [heq]; exact div_pos hVR_pos hZ_pos)
  have h1 : (∫ x in Icc (-R) R, if |q.eval x| ≤ ε then wR x else 0) =
      (∫ x in Icc (-R) R, if |q.eval x| ≤ ε then φ x else 0) / Z := by
    have : (fun x => if |q.eval x| ≤ ε then wR x else 0) =
        fun x => (if |q.eval x| ≤ ε then φ x else 0) / Z := funext fun x => by
      simp only [wR]; split_ifs <;> simp
    rw [this, integral_div]
  have h2 : ∫ x in Icc (-R) R, q.eval x ^ 2 * wR x =
      (∫ x in Icc (-R) R, q.eval x ^ 2 * φ x) / Z := by
    simp only [wR, ← mul_div_assoc, integral_div]
  rwa [h1, h2] at hcw

end CslibFrontier.Probability
