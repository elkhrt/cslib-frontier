/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.BooleanAnalysis.KhintchineKahane
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeMoments
import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.Holder
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Lagrange

/-!
# Multilinear and Exponential-Constant Discrete Bohnenblust–Hille Inequalities

Multilinear Bohnenblust–Hille inequality on hypercube sign tensors and exponential-in-degree
discrete Bohnenblust–Hille inequality for low-degree real-valued Boolean functions
`f ∈ Cslib.BitString.lowDegree ℝ ι d`:

* `CslibFrontier.BooleanAnalysis.bhExponent`: the exponent `2k / (k + 1)`.
* `CslibFrontier.BooleanAnalysis.sum_abs_rpow_le_of_le`: discrete `ℓ_p` norm monotonicity.
* `CslibFrontier.BooleanAnalysis.bh_multilinear_rpow_le`: multilinear Bohnenblust–Hille inequality
  with constant `(√2) ^ (k - 1)`.
* `CslibFrontier.BooleanAnalysis.norm_levelPart_le`: homogeneous level projection bound
  `‖levelPart l f‖ ≤ (2 e) ^ d * ‖f‖`.
* `CslibFrontier.BooleanAnalysis.sum_powersetCard_rpow_fourierCoeff_le_exp`: homogeneous level-`k`
  Fourier `ℓ_{2k/(k+1)}` bound via random `k`-coloring decoupling.
* `CslibFrontier.BooleanAnalysis.sum_rpow_fourierCoeff_le_exp`: bounded-degree discrete
  Bohnenblust–Hille inequality with constant `(4 e ^ 2 √2) ^ d`.
-/

public section

open scoped BigOperators
open Cslib.BitString

namespace CslibFrontier.BooleanAnalysis

/-! ### 1. Bohnenblust–Hille exponent and finite `ℓ_p` norm inequalities -/

/-- The `k`-th Bohnenblust–Hille exponent `2k / (k + 1)`. -/
@[expose] noncomputable def bhExponent (k : ℕ) : ℝ :=
  (2 * (k : ℝ)) / ((k : ℝ) + 1)

/-- Positivity of `bhExponent k` for `k ≥ 1`. -/
theorem bhExponent_pos {k : ℕ} (hk : 1 ≤ k) : 0 < bhExponent k := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold bhExponent; positivity

/-- For `k ≥ 1`, the Bohnenblust–Hille exponent satisfies `1 ≤ bhExponent k`. -/
theorem one_le_bhExponent {k : ℕ} (hk : 1 ≤ k) : 1 ≤ bhExponent k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold bhExponent; rw [one_le_div (by positivity)]; linarith

/-- For every `k : ℕ`, `bhExponent k < 2`. -/
theorem bhExponent_lt_two (k : ℕ) : bhExponent k < 2 := by
  unfold bhExponent; rw [div_lt_iff₀ (by positivity)]; linarith

/-- Monotonicity of `bhExponent` with respect to the degree parameter `k`. -/
theorem bhExponent_mono {l d : ℕ} (hld : l ≤ d) : bhExponent l ≤ bhExponent d := by
  have hreal : (l : ℝ) ≤ d := by exact_mod_cast hld
  unfold bhExponent; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- Discrete `ℓ_p` norm monotonicity: for `0 < p ≤ q`, the `ℓ_q` sum norm is bounded above by the
`ℓ_p` sum norm. -/
theorem sum_abs_rpow_le_of_le {α : Type*} (s : Finset α) (f : α → ℝ) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    (∑ x ∈ s, |f x| ^ q) ^ (1 / q) ≤ (∑ x ∈ s, |f x| ^ p) ^ (1 / p) := by
  have hq : 0 < q := hp.trans_le hpq
  set S : ℝ := ∑ x ∈ s, |f x| ^ p
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  rcases eq_or_lt_of_le hS_nn with hS0 | hS_pos
  · have hzero : ∀ x ∈ s, |f x| ^ q = 0 := fun x hx ↦ by
      have hpx : |f x| ^ p = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)).mp
          hS0.symm x hx
      have hfx : |f x| = 0 := (Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp hpx
      rw [hfx, Real.zero_rpow hq.ne']
    rw [Finset.sum_eq_zero hzero, ← hS0, Real.zero_rpow (one_div_ne_zero hq.ne'),
      Real.zero_rpow (one_div_ne_zero hp.ne')]
  · have hqp1 : 1 ≤ q / p := (one_le_div hp).mpr hpq
    have hterm : ∀ x ∈ s, |f x| ^ q / S ^ (q / p) ≤ |f x| ^ p / S := fun x hx ↦ by
      set u : ℝ := |f x| ^ p / S
      have hu0 : 0 ≤ u := div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hS_pos.le
      have hu1 : u ≤ 1 := (div_le_one hS_pos).mpr
        (Finset.single_le_sum (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hx)
      have hurpow : u ^ (q / p) ≤ u := by
        rcases eq_or_lt_of_le hu0 with hu_zero | hu_pos
        · rw [← hu_zero, Real.zero_rpow (by positivity)]
        · exact (Real.rpow_le_rpow_of_exponent_ge hu_pos hu1 hqp1).trans_eq (Real.rpow_one u)
      have hrew : u ^ (q / p) = |f x| ^ q / S ^ (q / p) := by
        dsimp [u]
        rw [Real.div_rpow (Real.rpow_nonneg (abs_nonneg _) _) hS_pos.le,
          ← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hp.ne']
      rwa [← hrew]
    have hsum_div : (∑ x ∈ s, |f x| ^ q) / S ^ (q / p) ≤ 1 := by
      rw [Finset.sum_div]
      exact (Finset.sum_le_sum hterm).trans_eq (by rw [← Finset.sum_div, div_self hS_pos.ne'])
    have hsum_le : ∑ x ∈ s, |f x| ^ q ≤ S ^ (q / p) :=
      (div_le_one (Real.rpow_pos_of_pos hS_pos _)).mp hsum_div
    have hpow := Real.rpow_le_rpow
      (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hsum_le
      (one_div_nonneg.mpr hq.le)
    refine hpow.trans_eq ?_
    rw [← Real.rpow_mul hS_pos.le]
    congr 1
    field_simp [hq.ne']

/-! ### 2. Minkowski's inequality and multilinear Bohnenblust–Hille inequality -/

private theorem minkowski_sum_rpow_le {α β : Type*} (U : Finset α) (V : Finset β)
    (w : α → β → ℝ) (hw : ∀ u ∈ U, ∀ v ∈ V, 0 ≤ w u v) {r : ℝ} (hr : 1 ≤ r) :
    (∑ v ∈ V, (∑ u ∈ U, w u v) ^ r) ^ (1 / r) ≤
      ∑ u ∈ U, (∑ v ∈ V, w u v ^ r) ^ (1 / r) := by
  rcases eq_or_lt_of_le hr with rfl | hr_gt
  · simp only [Real.rpow_one, div_one]
    rw [Finset.sum_comm]
  · have hr0 : 0 < r := zero_lt_one.trans hr_gt
    let g : β → ℝ := fun v ↦ ∑ u ∈ U, w u v
    have hg_nn : ∀ v ∈ V, 0 ≤ g v := fun v hv ↦ Finset.sum_nonneg fun u hu ↦ hw u hu v hv
    set S : ℝ := ∑ v ∈ V, g v ^ r
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun v hv ↦ Real.rpow_nonneg (hg_nn v hv) _
    rcases eq_or_lt_of_le hS_nn with hS0 | hS_pos
    · rw [← hS0, Real.zero_rpow (one_div_ne_zero hr0.ne')]
      exact Finset.sum_nonneg fun u hu ↦
        Real.rpow_nonneg (Finset.sum_nonneg fun v hv ↦ Real.rpow_nonneg (hw u hu v hv) _) _
    · let q : ℝ := r / (r - 1)
      have hr1 : 0 < r - 1 := sub_pos.mpr hr_gt
      have hq0 : 0 < q := div_pos hr0 hr1
      have hpq : r.HolderConjugate q :=
        ⟨by dsimp [q]; field_simp [hr0.ne', hr1.ne']; ring, hr0, hq0⟩
      have hS_expand : S = ∑ u ∈ U, ∑ v ∈ V, w u v * g v ^ (r - 1) := by
        calc
          S = ∑ v ∈ V, g v * g v ^ (r - 1) := Finset.sum_congr rfl fun v hv ↦ by
            conv_lhs => rw [show r = 1 + (r - 1) by ring]
            rw [Real.rpow_add' (hg_nn v hv) (by linarith), Real.rpow_one]
          _ = ∑ v ∈ V, ∑ u ∈ U, w u v * g v ^ (r - 1) :=
            Finset.sum_congr rfl fun v _ ↦ Finset.sum_mul U (fun u ↦ w u v) _
          _ = ∑ u ∈ U, ∑ v ∈ V, w u v * g v ^ (r - 1) := Finset.sum_comm
      have hholder : ∀ u ∈ U,
          ∑ v ∈ V, w u v * g v ^ (r - 1) ≤
            (∑ v ∈ V, w u v ^ r) ^ (1 / r) * S ^ (1 / q) := fun u hu ↦ by
        have hh := Real.inner_le_Lp_mul_Lq_of_nonneg V
          (f := w u) (g := fun v ↦ g v ^ (r - 1)) hpq
          (fun v hv ↦ hw u hu v hv) (fun v hv ↦ Real.rpow_nonneg (hg_nn v hv) (r - 1))
        refine hh.trans_eq ?_
        refine congrArg (_ * ·) (congrArg (· ^ (1 / q)) ?_)
        refine Finset.sum_congr rfl fun v hv ↦ ?_
        rw [← Real.rpow_mul (hg_nn v hv)]
        congr 1
        dsimp [q]
        field_simp [hr1.ne']
      have hbound : S ≤ (∑ u ∈ U, (∑ v ∈ V, w u v ^ r) ^ (1 / r)) * S ^ (1 / q) := by
        conv_lhs => rw [hS_expand]
        exact (Finset.sum_le_sum hholder).trans_eq (Finset.sum_mul _ _ _).symm
      have hS_split : S = S ^ (1 / r) * S ^ (1 / q) := by
        rw [← Real.rpow_add hS_pos, hpq.one_div_add_one_div, one_div_one, Real.rpow_one]
      have hSq_pos : 0 < S ^ (1 / q) := Real.rpow_pos_of_pos hS_pos _
      exact le_of_mul_le_mul_right (hS_split ▸ hbound) hSq_pos

private theorem sqrt_sum_sq_le_sqrt_two_mul_expect_abs {n : ℕ} (b : Fin n → ℝ) :
    Real.sqrt (∑ j : Fin n, b j ^ 2) ≤
      Real.sqrt 2 * (𝔼 y : Fin n → Bool, |∑ j : Fin n, b j * signVal (y j)|) := by
  have hkk := Cslib.BitString.expect_norm_sum_sq_le_two_mul_sq (V := ℝ) b
  have hl2 := Cslib.BitString.lpNorm_two_sum_mul_signVal b
  rw [Cslib.lpNorm_two] at hl2
  have hsq : ∑ j : Fin n, b j ^ 2 = 𝔼 y : Fin n → Bool, (∑ j : Fin n, b j * signVal (y j)) ^ 2 := by
    have h1 := congrArg (· ^ 2) hl2
    rw [Real.sq_sqrt (Finset.univ.expect_nonneg fun _ _ ↦ sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h1
    exact h1.symm
  have hcomm : ∀ y : Fin n → Bool,
      ‖∑ j : Fin n, signVal (y j) • b j‖ = |∑ j : Fin n, b j * signVal (y j)| := fun y ↦ by
    rw [Real.norm_eq_abs]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by simp [smul_eq_mul, mul_comm]
  simp_rw [hcomm, sq_abs] at hkk
  rw [← hsq] at hkk
  have hsqrt := Real.sqrt_le_sqrt hkk
  rwa [Real.sqrt_mul zero_le_two,
    Real.sqrt_sq (Finset.univ.expect_nonneg fun _ _ ↦ abs_nonneg _)] at hsqrt

private def finConsArrowEquiv (k : ℕ) (α : Type*) : (Fin (k + 1) → α) ≃ α × (Fin k → α) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp

private theorem multilinear_l2_le_expect_abs :
    ∀ (k n : ℕ) (a : (Fin k → Fin n) → ℝ),
      Real.sqrt (∑ i : Fin k → Fin n, a i ^ 2) ≤
        (Real.sqrt 2) ^ k *
          (𝔼 x : Fin k → Fin n → Bool,
            |∑ i : Fin k → Fin n, a i * ∏ r : Fin k, signVal (x r (i r))|)
  | 0, n, a => by
      have hsum : (∑ i : Fin 0 → Fin n, a i ^ 2) = a Fin.elim0 ^ 2 := by
        rw [Fintype.sum_unique]
        exact congrArg (· ^ 2) (congrArg a (Subsingleton.elim _ _))
      have hlin : ∀ x : Fin 0 → Fin n → Bool,
          (∑ i : Fin 0 → Fin n, a i * ∏ r : Fin 0, signVal (x r (i r))) = a Fin.elim0 := fun x ↦ by
        rw [Fintype.sum_unique]
        simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
        exact congrArg a (Subsingleton.elim _ _)
      simp_rw [hsum, hlin, Real.sqrt_sq_eq_abs, pow_zero, one_mul, Fintype.expect_const]
      exact le_rfl
  | k + 1, n, a => by
      let b : (Fin k → Fin n → Bool) → Fin n → ℝ := fun x' j ↦
        ∑ i' : Fin k → Fin n, a (Fin.cons j i') * ∏ r : Fin k, signVal (x' r (i' r))
      have hsplit_a :
          (∑ i : Fin (k + 1) → Fin n, a i ^ 2) =
            ∑ j : Fin n, ∑ i' : Fin k → Fin n, a (Fin.cons j i') ^ 2 := by
        rw [Fintype.sum_equiv (finConsArrowEquiv k (Fin n))
          (fun i ↦ a i ^ 2) (fun p ↦ a (Fin.cons p.1 p.2) ^ 2)
          (fun i ↦ by simp [finConsArrowEquiv, Fin.cons_self_tail]), Fintype.sum_prod_type]
      have hstep_j : ∀ j : Fin n,
          Real.sqrt (∑ i' : Fin k → Fin n, a (Fin.cons j i') ^ 2) ≤
            (Real.sqrt 2) ^ k * (𝔼 x' : Fin k → Fin n → Bool, |b x' j|) :=
        fun j ↦ multilinear_l2_le_expect_abs k n (fun i' ↦ a (Fin.cons j i'))
      have hmink :
          Real.sqrt (∑ j : Fin n, (𝔼 x' : Fin k → Fin n → Bool, |b x' j|) ^ 2) ≤
            𝔼 x' : Fin k → Fin n → Bool, Real.sqrt (∑ j : Fin n, b x' j ^ 2) := by
        let Ncard : ℝ := (Fintype.card (Fin k → Fin n → Bool) : ℝ)
        have hN_pos : 0 < Ncard := by dsimp [Ncard]; positivity
        simp_rw [Finset.expect_eq_sum_div_card, Finset.card_univ]
        have hm := minkowski_sum_rpow_le (Finset.univ : Finset (Fin k → Fin n → Bool))
          (Finset.univ : Finset (Fin n)) (fun x' j ↦ |b x' j| / Ncard)
          (fun _ _ _ _ ↦ by positivity) one_le_two
        refine (Real.sqrt_eq_rpow _).trans_le ((le_of_eq ?_).trans (hm.trans_eq ?_))
        · congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.sum_div, Real.rpow_two]
        · rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun x' _ ↦ ?_
          have hdiv :
              ∑ j : Fin n, (|b x' j| / Ncard) ^ (2 : ℝ) =
                (∑ j : Fin n, b x' j ^ 2) / Ncard ^ 2 := by
            simp_rw [Real.rpow_two, div_pow, sq_abs]
            rw [← Finset.sum_div]
          rw [hdiv, Real.div_rpow (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _),
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq hN_pos.le]
      have hexp_eq :
          (𝔼 x' : Fin k → Fin n → Bool,
              𝔼 y : Fin n → Bool, |∑ j : Fin n, b x' j * signVal (y j)|) =
            𝔼 x : Fin (k + 1) → Fin n → Bool,
              |∑ i : Fin (k + 1) → Fin n, a i * ∏ r : Fin (k + 1), signVal (x r (i r))| := by
        rw [← Fintype.expect_prod_type (fun p : (Fin k → Fin n → Bool) × (Fin n → Bool) ↦
            |∑ j : Fin n, b p.1 j * signVal (p.2 j)|)]
        exact Fintype.expect_equiv
          ((Equiv.prodComm (Fin k → Fin n → Bool) (Fin n → Bool)).trans
            (finConsArrowEquiv k (Fin n → Bool)).symm)
          (fun p : (Fin k → Fin n → Bool) × (Fin n → Bool) ↦
            |∑ j : Fin n, b p.1 j * signVal (p.2 j)|)
          (fun x : Fin (k + 1) → Fin n → Bool ↦
            |∑ i : Fin (k + 1) → Fin n, a i * ∏ r : Fin (k + 1), signVal (x r (i r))|)
          (fun p ↦ by
            let x : Fin (k + 1) → Fin n → Bool :=
              Fin.cons (α := fun _ ↦ Fin n → Bool) p.2 p.1
            change |∑ j : Fin n, b p.1 j * signVal (p.2 j)| =
              |∑ i : Fin (k + 1) → Fin n, a i * ∏ r : Fin (k + 1), signVal (x r (i r))|
            congr 1
            rw [Fintype.sum_equiv (finConsArrowEquiv k (Fin n))
              (fun i ↦ a i * ∏ r : Fin (k + 1), signVal (x r (i r)))
              (fun q ↦ a (Fin.cons q.1 q.2) *
                (signVal (p.2 q.1) * ∏ r : Fin k, signVal (p.1 r (q.2 r))))
              (fun i ↦ by
                simp only [finConsArrowEquiv, Equiv.coe_fn_mk, Fin.cons_self_tail, x]
                rw [Fin.prod_univ_succ (n := k)]
                rfl), Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            dsimp [b]
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i' _ ↦ by ring)
      calc
        Real.sqrt (∑ i : Fin (k + 1) → Fin n, a i ^ 2)
            = Real.sqrt (∑ j : Fin n,
                (Real.sqrt (∑ i' : Fin k → Fin n, a (Fin.cons j i') ^ 2)) ^ 2) := by
              rw [hsplit_a]
              congr 1
              exact Finset.sum_congr rfl fun j _ ↦
                (Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).symm
        _ ≤ Real.sqrt (∑ j : Fin n,
              ((Real.sqrt 2) ^ k * (𝔼 x' : Fin k → Fin n → Bool, |b x' j|)) ^ 2) := by
              refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ ↦ ?_)
              exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hstep_j j) 2
        _ = (Real.sqrt 2) ^ k *
              Real.sqrt (∑ j : Fin n, (𝔼 x' : Fin k → Fin n → Bool, |b x' j|) ^ 2) := by
              simp_rw [mul_pow]
              rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        _ ≤ (Real.sqrt 2) ^ k *
              (𝔼 x' : Fin k → Fin n → Bool, Real.sqrt (∑ j : Fin n, b x' j ^ 2)) :=
              mul_le_mul_of_nonneg_left hmink (by positivity)
        _ ≤ (Real.sqrt 2) ^ k *
              (𝔼 x' : Fin k → Fin n → Bool,
                Real.sqrt 2 * (𝔼 y : Fin n → Bool, |∑ j : Fin n, b x' j * signVal (y j)|)) := by
              refine mul_le_mul_of_nonneg_left
                (Finset.expect_le_expect fun x' _ ↦ sqrt_sum_sq_le_sqrt_two_mul_expect_abs _)
                (by positivity)
        _ = (Real.sqrt 2) ^ (k + 1) *
              (𝔼 x : Fin (k + 1) → Fin n → Bool,
                |∑ i : Fin (k + 1) → Fin n, a i * ∏ r : Fin (k + 1), signVal (x r (i r))|) := by
              rw [← Finset.mul_expect, ← hexp_eq, pow_succ, mul_assoc]

private theorem expect_abs_le_rpow_expect_rpow {α : Type*} [Fintype α] [Nonempty α]
    (g : α → ℝ) {p : ℝ} (hp1 : 1 ≤ p) :
    (𝔼 x : α, |g x|) ^ p ≤ 𝔼 x : α, |g x| ^ p := by
  rcases eq_or_lt_of_le hp1 with rfl | hp_gt
  · simp
  · have hp0 : 0 < p := zero_lt_one.trans hp_gt
    have hsub := Fintype.expect_rpow_le_rpow_expect (f := fun x ↦ |g x| ^ p)
      (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (one_div_pos.mpr hp0)
      (by rw [one_div]; exact inv_lt_one_of_one_lt₀ hp_gt)
    have hsimp : (fun x : α ↦ (|g x| ^ p) ^ (1 / p)) = fun x ↦ |g x| := funext fun x ↦ by
      rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
    rw [hsimp] at hsub
    have hpow := Real.rpow_le_rpow (Finset.univ.expect_nonneg fun _ _ ↦ abs_nonneg _) hsub hp0.le
    rwa [← Real.rpow_mul (Finset.univ.expect_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
      one_div_mul_cancel hp0.ne', Real.rpow_one] at hpow

private theorem bh_multilinear_rpow_le_succ :
    ∀ (m n : ℕ) (c : (Fin (m + 1) → Fin n) → ℝ) {M : ℝ},
      0 ≤ M →
      (∀ x : Fin (m + 1) → Fin n → Bool,
        |∑ i : Fin (m + 1) → Fin n, c i * ∏ r : Fin (m + 1), signVal (x r (i r))| ≤ M) →
      (∑ i : Fin (m + 1) → Fin n, |c i| ^ bhExponent (m + 1)) ^ (1 / bhExponent (m + 1)) ≤
        (Real.sqrt 2) ^ m * M
  | 0, n, c, M, _, hbound => by
      have hexp1 : bhExponent 1 = 1 := by unfold bhExponent; norm_num
      rw [hexp1]
      simp only [pow_zero, one_mul, div_one, Real.rpow_one]
      let x₀ : Fin 1 → Fin n → Bool := fun _ j ↦ decide (c (fun _ ↦ j) < 0)
      have hterm : ∀ i : Fin 1 → Fin n,
          c i * (∏ r : Fin 1, signVal (x₀ r (i r))) = |c i| := fun i ↦ by
        have hi : i = fun _ ↦ i 0 := funext fun r ↦ congrArg i (Subsingleton.elim r 0)
        rw [Fin.prod_univ_one]
        dsimp [x₀]
        rw [← hi]
        by_cases hlt : c i < 0
        · simp [hlt, abs_of_neg hlt]
        · simp [hlt, abs_of_nonneg (not_lt.mp hlt)]
      have hsum_eq : ∑ i : Fin 1 → Fin n, |c i| =
          ∑ i : Fin 1 → Fin n, c i * ∏ r : Fin 1, signVal (x₀ r (i r)) :=
        (Finset.sum_congr rfl fun i _ ↦ hterm i).symm
      rw [hsum_eq]
      exact (le_abs_self _).trans (hbound x₀)
  | m + 1, n, c, M, hM, hbound => by
      let k := m + 1
      have hk1 : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le m)
      set pk : ℝ := bhExponent k
      set pk1 : ℝ := bhExponent (k + 1)
      have hpk1 : 1 ≤ pk := one_le_bhExponent hk1
      have hpk0 : 0 < pk := zero_lt_one.trans_le hpk1
      have hpk_lt2 : pk < 2 := bhExponent_lt_two k
      have hpk1_pos : 0 < pk1 := bhExponent_pos (Nat.succ_le_succ (Nat.zero_le k))
      let d : Fin n → (Fin k → Fin n) → ℝ := fun j i' ↦ c (Fin.cons j i')
      have hcons_bound : ∀ (y : Fin n → Bool) (x' : Fin k → Fin n → Bool),
          |∑ j : Fin n, ∑ i' : Fin k → Fin n,
            d j i' * (signVal (y j) * ∏ r : Fin k, signVal (x' r (i' r)))| ≤ M := fun y x' ↦ by
        let x : Fin (k + 1) → Fin n → Bool := Fin.cons (α := fun _ ↦ Fin n → Bool) y x'
        have heq : (∑ j : Fin n, ∑ i' : Fin k → Fin n,
              d j i' * (signVal (y j) * ∏ r : Fin k, signVal (x' r (i' r)))) =
            ∑ i : Fin (k + 1) → Fin n,
              c i * ∏ r : Fin (k + 1), signVal (x r (i r)) := by
          rw [← Fintype.sum_prod_type (fun p : Fin n × (Fin k → Fin n) ↦
            d p.1 p.2 * (signVal (y p.1) * ∏ r : Fin k, signVal (x' r (p.2 r))))]
          exact Fintype.sum_equiv (finConsArrowEquiv k (Fin n)).symm
            (fun p : Fin n × (Fin k → Fin n) ↦
              d p.1 p.2 * (signVal (y p.1) * ∏ r : Fin k, signVal (x' r (p.2 r))))
            (fun i : Fin (k + 1) → Fin n ↦
              c i * ∏ r : Fin (k + 1), signVal (x r (i r)))
            (fun p ↦ by
              dsimp [finConsArrowEquiv, d, x]
              rw [Fin.prod_univ_succ (n := k)]
              rfl)
        rw [heq]
        exact hbound x
      let u : Fin n → ℝ := fun j ↦ Real.sqrt (∑ i' : Fin k → Fin n, d j i' ^ 2)
      have hu_nn : ∀ j : Fin n, 0 ≤ u j := fun _ ↦ Real.sqrt_nonneg _
      have hA : ∑ j : Fin n, u j ≤ (Real.sqrt 2) ^ k * M := by
        let L : (Fin k → Fin n → Bool) → Fin n → ℝ := fun x' j ↦
          ∑ i' : Fin k → Fin n, d j i' * ∏ r : Fin k, signVal (x' r (i' r))
        have hsum_L : ∀ x' : Fin k → Fin n → Bool, ∑ j : Fin n, |L x' j| ≤ M := fun x' ↦ by
          let y : Fin n → Bool := fun j ↦ decide (L x' j < 0)
          have hy_align : ∀ j : Fin n, signVal (y j) * L x' j = |L x' j| := fun j ↦ by
            dsimp [y]
            by_cases hlt : L x' j < 0
            · simp [hlt, abs_of_neg hlt]
            · simp [hlt, abs_of_nonneg (not_lt.mp hlt)]
          have hrew : ∑ j : Fin n, |L x' j| =
              ∑ j : Fin n, ∑ i' : Fin k → Fin n,
                d j i' * (signVal (y j) * ∏ r : Fin k, signVal (x' r (i' r))) := by
            simp_rw [← hy_align]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            dsimp [L]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i' _ ↦ by ring
          rw [hrew]
          exact le_trans (le_abs_self _) (hcons_bound y x')
        calc
          ∑ j : Fin n, u j
              ≤ ∑ j : Fin n, (Real.sqrt 2) ^ k * (𝔼 x' : Fin k → Fin n → Bool, |L x' j|) :=
                Finset.sum_le_sum fun j _ ↦ multilinear_l2_le_expect_abs k n (d j)
          _ = (Real.sqrt 2) ^ k * ∑ j : Fin n, 𝔼 x' : Fin k → Fin n → Bool, |L x' j| := by
                rw [← Finset.mul_sum]
          _ = (Real.sqrt 2) ^ k * (𝔼 x' : Fin k → Fin n → Bool, ∑ j : Fin n, |L x' j|) := by
                congr 1
                simp_rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div]
                rw [Finset.sum_comm]
          _ ≤ (Real.sqrt 2) ^ k * M := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact (Finset.expect_le_expect fun x' _ ↦ hsum_L x').trans_eq
                  (Fintype.expect_const M)
      let v : Fin n → ℝ := fun j ↦ (∑ i' : Fin k → Fin n, |d j i'| ^ pk) ^ (1 / pk)
      have hv_nn : ∀ j : Fin n, 0 ≤ v j := fun _ ↦
        Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _
      have hB : Real.sqrt (∑ j : Fin n, v j ^ 2) ≤ (Real.sqrt 2) ^ k * M := by
        have hv_sq : ∀ j : Fin n,
            v j ^ 2 = (∑ i' : Fin k → Fin n, |d j i'| ^ pk) ^ (2 / pk) := fun j ↦ by
          dsimp [v]
          rw [← Real.rpow_two, ← Real.rpow_mul
            (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _), one_div_mul_eq_div]
        have hr_ge1 : 1 ≤ 2 / pk := (one_le_div hpk0).mpr hpk_lt2.le
        have hmink := minkowski_sum_rpow_le (Finset.univ : Finset (Fin k → Fin n))
          (Finset.univ : Finset (Fin n)) (fun i' j ↦ |d j i'| ^ pk)
          (fun _ _ _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hr_ge1
        have hmink_lhs :
            (∑ j : Fin n, (∑ i' : Fin k → Fin n, |d j i'| ^ pk) ^ (2 / pk)) ^ (1 / (2 / pk)) =
              (Real.sqrt (∑ j : Fin n, v j ^ 2)) ^ pk := by
          simp_rw [← hv_sq]
          rw [one_div_div, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), one_div_mul_eq_div]
        have hmink_rhs :
            (∑ i' : Fin k → Fin n, (∑ j : Fin n, (|d j i'| ^ pk) ^ (2 / pk)) ^ (1 / (2 / pk))) =
              ∑ i' : Fin k → Fin n, (Real.sqrt (∑ j : Fin n, d j i' ^ 2)) ^ pk := by
          refine Finset.sum_congr rfl fun i' _ ↦ ?_
          have h1 : ∀ j : Fin n, (|d j i'| ^ pk) ^ (2 / pk) = d j i' ^ 2 := fun j ↦ by
            rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hpk0.ne', Real.rpow_two, sq_abs]
          simp_rw [h1]
          rw [one_div_div, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), one_div_mul_eq_div]
        rw [hmink_lhs, hmink_rhs] at hmink
        have hih_y : ∀ y : Fin n → Bool,
            ∑ i' : Fin k → Fin n, |∑ j : Fin n, d j i' * signVal (y j)| ^ pk ≤
              ((Real.sqrt 2) ^ m * M) ^ pk := fun y ↦ by
          have hy := bh_multilinear_rpow_le_succ m n
            (fun i' ↦ ∑ j : Fin n, d j i' * signVal (y j)) hM fun x' ↦ by
            have heq : (∑ i' : Fin k → Fin n,
                  (∑ j : Fin n, d j i' * signVal (y j)) *
                    ∏ r : Fin k, signVal (x' r (i' r))) =
                ∑ j : Fin n, ∑ i' : Fin k → Fin n,
                  d j i' * (signVal (y j) * ∏ r : Fin k, signVal (x' r (i' r))) := by
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i' _ ↦ by ring
            rw [heq]
            exact hcons_bound y x'
          have hpow := Real.rpow_le_rpow
            (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _)
            hy hpk0.le
          rwa [← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
            one_div_mul_cancel hpk0.ne', Real.rpow_one] at hpow
        have hsum_kh :
            ∑ i' : Fin k → Fin n, (Real.sqrt (∑ j : Fin n, d j i' ^ 2)) ^ pk ≤
              ((Real.sqrt 2) ^ k * M) ^ pk := by
          have hpt : ∀ i' : Fin k → Fin n,
              (Real.sqrt (∑ j : Fin n, d j i' ^ 2)) ^ pk ≤
                (Real.sqrt 2) ^ pk *
                  (𝔼 y : Fin n → Bool, |∑ j : Fin n, d j i' * signVal (y j)| ^ pk) := fun i' ↦ by
            have h1 := Real.rpow_le_rpow (Real.sqrt_nonneg _)
              (sqrt_sum_sq_le_sqrt_two_mul_expect_abs fun j ↦ d j i') hpk0.le
            rw [Real.mul_rpow (Real.sqrt_nonneg 2)
              (Finset.univ.expect_nonneg fun _ _ ↦ abs_nonneg _)] at h1
            exact h1.trans (mul_le_mul_of_nonneg_left
              (expect_abs_le_rpow_expect_rpow _ hpk1) (by positivity))
          calc
            ∑ i' : Fin k → Fin n, (Real.sqrt (∑ j : Fin n, d j i' ^ 2)) ^ pk
                ≤ ∑ i' : Fin k → Fin n, (Real.sqrt 2) ^ pk *
                    (𝔼 y : Fin n → Bool, |∑ j : Fin n, d j i' * signVal (y j)| ^ pk) :=
                  Finset.sum_le_sum fun i' _ ↦ hpt i'
            _ = (Real.sqrt 2) ^ pk *
                  (𝔼 y : Fin n → Bool,
                    ∑ i' : Fin k → Fin n, |∑ j : Fin n, d j i' * signVal (y j)| ^ pk) := by
                  rw [← Finset.mul_sum]
                  congr 1
                  simp_rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div]
                  rw [Finset.sum_comm]
            _ ≤ (Real.sqrt 2) ^ pk * ((Real.sqrt 2) ^ m * M) ^ pk := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact (Finset.expect_le_expect fun y _ ↦ hih_y y).trans_eq
                    (Fintype.expect_const _)
            _ = ((Real.sqrt 2) ^ k * M) ^ pk := by
                  rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_assoc, ← pow_succ']
        have hcomb := hmink.trans hsum_kh
        have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hcomb
          (one_div_nonneg.mpr hpk0.le)
        rwa [← Real.rpow_mul (Real.sqrt_nonneg _), mul_one_div_cancel hpk0.ne', Real.rpow_one,
          ← Real.rpow_mul (by positivity), mul_one_div_cancel hpk0.ne', Real.rpow_one] at hroot
      have hk2_pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
      have hconj_in : ((k : ℝ) + 2).HolderConjugate (((k : ℝ) + 2) / ((k : ℝ) + 1)) :=
        ⟨by field_simp [hk2_pos.ne', hk1_pos.ne']; ring, hk2_pos, by positivity⟩
      have hconj_out : (((k : ℝ) + 2) / 2).HolderConjugate (((k : ℝ) + 2) / (k : ℝ)) :=
        ⟨by field_simp [hk2_pos.ne', hk_pos.ne']; ring, by positivity, by positivity⟩
      have hinner : ∀ j : Fin n,
          ∑ i' : Fin k → Fin n, |d j i'| ^ pk1 ≤
            u j ^ (2 / ((k : ℝ) + 2)) * (v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)) := fun j ↦ by
        have hsplit_exp : ∀ i' : Fin k → Fin n,
            |d j i'| ^ pk1 =
              (|d j i'| ^ (2 / ((k : ℝ) + 2))) *
                (|d j i'| ^ (pk * (((k : ℝ) + 1) / ((k : ℝ) + 2)))) := fun i' ↦ by
          have hexp : 2 / ((k : ℝ) + 2) + pk * (((k : ℝ) + 1) / ((k : ℝ) + 2)) = pk1 := by
            dsimp [pk, pk1, bhExponent]
            push_cast
            field_simp [hk2_pos.ne', hk1_pos.ne']
            ring
          rw [← Real.rpow_add' (abs_nonneg _) (by rw [hexp]; exact hpk1_pos.ne'), hexp]
        simp_rw [hsplit_exp]
        have hh := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
          (f := fun i' ↦ |d j i'| ^ (2 / ((k : ℝ) + 2)))
          (g := fun i' ↦ |d j i'| ^ (pk * (((k : ℝ) + 1) / ((k : ℝ) + 2))))
          hconj_in
          (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
          (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
        refine hh.trans_eq (congrArg₂ (· * ·) ?_ ?_)
        · have h1 : ∀ i' : Fin k → Fin n,
              (|d j i'| ^ (2 / ((k : ℝ) + 2))) ^ ((k : ℝ) + 2) = d j i' ^ 2 := fun i' ↦ by
            rw [← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ _ hk2_pos.ne', Real.rpow_two,
              sq_abs]
          simp_rw [h1]
          dsimp only [u]
          rw [Real.sqrt_eq_rpow,
            ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
          congr 1
          ring
        · have h2 : ∀ i' : Fin k → Fin n,
              (|d j i'| ^ (pk * (((k : ℝ) + 1) / ((k : ℝ) + 2)))) ^
                (((k : ℝ) + 2) / ((k : ℝ) + 1)) = |d j i'| ^ pk := fun i' ↦ by
            rw [← Real.rpow_mul (abs_nonneg _)]
            congr 1
            field_simp [hk2_pos.ne', hk1_pos.ne']
          simp_rw [h2]
          dsimp only [v]
          rw [← Real.rpow_two, ← Real.rpow_mul (Real.rpow_nonneg
            (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _),
            ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
          congr 1
          dsimp [pk, bhExponent]
          field_simp [hk2_pos.ne', hk1_pos.ne', hk_pos.ne']
      have houter :
          ∑ j : Fin n, u j ^ (2 / ((k : ℝ) + 2)) * (v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)) ≤
            (∑ j : Fin n, u j) ^ (2 / ((k : ℝ) + 2)) *
              (∑ j : Fin n, v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)) := by
        have hh := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
          (f := fun j ↦ u j ^ (2 / ((k : ℝ) + 2)))
          (g := fun j ↦ (v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)))
          hconj_out
          (fun j _ ↦ Real.rpow_nonneg (hu_nn j) _)
          (fun _ _ ↦ Real.rpow_nonneg (sq_nonneg _) _)
        refine hh.trans_eq (congrArg₂ (· * ·) ?_ ?_)
        · rw [one_div_div]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← Real.rpow_mul (hu_nn j), div_mul_div_cancel₀ hk2_pos.ne', div_self two_ne_zero,
            Real.rpow_one]
        · rw [one_div_div]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← Real.rpow_mul (sq_nonneg _), div_mul_div_cancel₀ hk2_pos.ne', div_self hk_pos.ne',
            Real.rpow_one]
      have hsum_c :
          ∑ i : Fin (k + 1) → Fin n, |c i| ^ pk1 =
            ∑ j : Fin n, ∑ i' : Fin k → Fin n, |d j i'| ^ pk1 := by
        rw [Fintype.sum_equiv (finConsArrowEquiv k (Fin n))
          (fun i ↦ |c i| ^ pk1) (fun p ↦ |d p.1 p.2| ^ pk1)
          (fun i ↦ by simp [finConsArrowEquiv, d, Fin.cons_self_tail]), Fintype.sum_prod_type]
      have htotal :
          ∑ i : Fin (k + 1) → Fin n, |c i| ^ pk1 ≤ ((Real.sqrt 2) ^ k * M) ^ pk1 := by
        have h1 : (∑ j : Fin n, u j) ^ (2 / ((k : ℝ) + 2)) ≤
            ((Real.sqrt 2) ^ k * M) ^ (2 / ((k : ℝ) + 2)) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun j _ ↦ hu_nn j) hA (by positivity)
        have h2 : (∑ j : Fin n, v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)) ≤
            ((Real.sqrt 2) ^ k * M) ^ (2 * (k : ℝ) / ((k : ℝ) + 2)) := by
          have hsq_B : ∑ j : Fin n, v j ^ 2 ≤ ((Real.sqrt 2) ^ k * M) ^ 2 := by
            have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hB 2
            rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at hp
          exact (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hsq_B
            (by positivity)).trans_eq (by
              rw [← Real.rpow_two ((Real.sqrt 2) ^ k * M),
                ← Real.rpow_mul (by positivity), mul_div_assoc])
        calc
          ∑ i : Fin (k + 1) → Fin n, |c i| ^ pk1
              = ∑ j : Fin n, ∑ i' : Fin k → Fin n, |d j i'| ^ pk1 := hsum_c
          _ ≤ ∑ j : Fin n, u j ^ (2 / ((k : ℝ) + 2)) * (v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)) :=
                Finset.sum_le_sum fun j _ ↦ hinner j
          _ ≤ (∑ j : Fin n, u j) ^ (2 / ((k : ℝ) + 2)) *
                (∑ j : Fin n, v j ^ 2) ^ ((k : ℝ) / ((k : ℝ) + 2)) := houter
          _ ≤ ((Real.sqrt 2) ^ k * M) ^ (2 / ((k : ℝ) + 2)) *
                ((Real.sqrt 2) ^ k * M) ^ (2 * (k : ℝ) / ((k : ℝ) + 2)) :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = ((Real.sqrt 2) ^ k * M) ^ pk1 := by
                have hexp : 2 / ((k : ℝ) + 2) + 2 * (k : ℝ) / ((k : ℝ) + 2) = pk1 := by
                  dsimp [pk1, bhExponent]
                  push_cast
                  field_simp [hk2_pos.ne']
                  ring
                rw [← Real.rpow_add' (by positivity) (by rw [hexp]; exact hpk1_pos.ne'), hexp]
      have hroot := Real.rpow_le_rpow
        (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) htotal
        (one_div_nonneg.mpr hpk1_pos.le)
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hpk1_pos.ne', Real.rpow_one] at hroot
      exact hroot

/-- **Multilinear Bohnenblust–Hille inequality** on `{±1}` hypercubes: for every `k ≥ 1`, `n : ℕ`,
and tensor `c : (Fin k → Fin n) → ℝ` whose multilinear sign form is bounded in magnitude by `M ≥ 0`,
`(∑ i, |c i| ^ (2k / (k + 1))) ^ ((k + 1) / (2k)) ≤ (√2) ^ (k - 1) * M`. -/
theorem bh_multilinear_rpow_le {k n : ℕ} (hk : 1 ≤ k) (c : (Fin k → Fin n) → ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hbound : ∀ x : Fin k → Fin n → Bool,
      |∑ i : Fin k → Fin n, c i * ∏ r : Fin k, signVal (x r (i r))| ≤ M) :
    (∑ i : Fin k → Fin n, |c i| ^ bhExponent k) ^ (1 / bhExponent k) ≤
      (Real.sqrt 2) ^ (k - 1) * M := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa only [Nat.add_sub_cancel] using bh_multilinear_rpow_le_succ m n c hM hbound

/-! ### 3. Level projection bound via Lagrange interpolation of `noiseOp` -/

private theorem pow_div_factorial_le_exp_nat (k l : ℕ) :
    ((k : ℝ) ^ l) / (l.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
  have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg k) (l + 1)
  have hmem : l ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_self l)
  exact (Finset.single_le_sum (fun m _ ↦ by positivity) hmem).trans hsum

private theorem abs_coeff_prod_X_sub_C_le (t : Finset ℕ) (v : ℕ → ℝ)
    (hv : ∀ m ∈ t, |v m| ≤ 1) :
    ∀ l : ℕ, |(∏ m ∈ t, (Polynomial.X - Polynomial.C (v m))).coeff l| ≤ (2 : ℝ) ^ t.card := by
  induction t using Finset.induction_on with
  | empty =>
      intro l
      rw [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
      split_ifs <;> norm_num
  | @insert a s ha ih =>
      intro l
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      set Q : Polynomial ℝ := ∏ m ∈ s, (Polynomial.X - Polynomial.C (v m))
      have hQ : ∀ r : ℕ, |Q.coeff r| ≤ (2 : ℝ) ^ s.card :=
        ih (fun m hm ↦ hv m (Finset.mem_insert_of_mem hm))
      have hva : |v a| ≤ 1 := hv a (Finset.mem_insert_self a s)
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      cases l with
      | zero =>
          rw [mul_comm Polynomial.X Q, Polynomial.coeff_mul_X_zero, zero_sub, abs_neg,
            abs_mul]
          calc
            |v a| * |Q.coeff 0| ≤ 1 * (2 : ℝ) ^ s.card :=
              mul_le_mul hva (hQ 0) (abs_nonneg _) zero_le_one
            _ ≤ 2 * (2 : ℝ) ^ s.card := by linarith [pow_pos (zero_lt_two' ℝ) s.card]
      | succ r =>
          rw [mul_comm Polynomial.X Q, Polynomial.coeff_mul_X]
          calc
            |Q.coeff r - v a * Q.coeff (r + 1)|
                ≤ |Q.coeff r| + |v a * Q.coeff (r + 1)| := abs_sub _ _
            _ = |Q.coeff r| + |v a| * |Q.coeff (r + 1)| := by rw [abs_mul]
            _ ≤ (2 : ℝ) ^ s.card + 1 * (2 : ℝ) ^ s.card :=
                add_le_add (hQ r) (mul_le_mul hva (hQ (r + 1)) (abs_nonneg _) zero_le_one)
            _ = 2 * (2 : ℝ) ^ s.card := by ring

private theorem prod_abs_sub_range_self :
    ∀ n : ℕ, (∏ m ∈ Finset.range n, |(n : ℝ) - (m : ℝ)|) = (n.factorial : ℝ)
  | 0 => by simp
  | n + 1 => by
      have hshift :
          (∏ m ∈ Finset.range (n + 1), |((n + 1 : ℕ) : ℝ) - (m : ℝ)|) =
            ((n + 1 : ℕ) : ℝ) * ∏ m ∈ Finset.range n, |(n : ℝ) - (m : ℝ)| := by
        rw [Finset.prod_range_succ']
        simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
        rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun m _ ↦ ?_
        congr 1
        ring
      rw [hshift, prod_abs_sub_range_self n, Nat.factorial_succ, Nat.cast_mul]

private theorem prod_abs_sub_erase_range :
    ∀ (d j : ℕ), j ≤ d →
      (∏ m ∈ (Finset.range (d + 1)).erase j, |(j : ℝ) - (m : ℝ)|) =
        (j.factorial : ℝ) * ((d - j).factorial : ℝ)
  | 0, j, hj => by
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      simp
  | d + 1, j, hj => by
      rcases eq_or_lt_of_le hj with rfl | hlt
      · have herase : (Finset.range (d + 2)).erase (d + 1) = Finset.range (d + 1) := by
          rw [Finset.range_add_one, Finset.erase_insert (Finset.notMem_range_self)]
        rw [herase, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
        exact prod_abs_sub_range_self (d + 1)
      · have hjd : j ≤ d := Nat.lt_succ_iff.mp hlt
        have hne : j ≠ d + 1 := ne_of_lt hlt
        have herase :
            (Finset.range (d + 2)).erase j =
              insert (d + 1) ((Finset.range (d + 1)).erase j) := by
          rw [Finset.range_add_one, Finset.erase_insert_of_ne hne.symm]
        have hnotMem : d + 1 ∉ (Finset.range (d + 1)).erase j :=
          fun h ↦ Finset.notMem_range_self (Finset.mem_of_mem_erase h)
        have habs : |(j : ℝ) - ((d + 1 : ℕ) : ℝ)| = ((d + 1 - j : ℕ) : ℝ) := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj)),
            Nat.cast_sub hj]
        rw [herase, Finset.prod_insert hnotMem, prod_abs_sub_erase_range d j hjd, habs,
          Nat.succ_sub hjd, Nat.factorial_succ, Nat.cast_mul]
        ring

private theorem abs_noiseOp_le_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 1) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    |noiseOp ρ f x| ≤ ‖f‖ := by
  have hbound : ∀ y : ι → Bool, |f y| ≤ ‖f‖ := fun y ↦ by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm f y
  have hhi : noiseOp ρ f x ≤ ‖f‖ := by
    have hnn := noiseOp_nonneg hρ0 hρ1 (g := fun y ↦ ‖f‖ - f y)
      (fun y ↦ sub_nonneg.mpr ((le_abs_self _).trans (hbound y))) x
    rw [noiseOp_sub, noiseOp_const] at hnn
    linarith
  have hlo : -‖f‖ ≤ noiseOp ρ f x := by
    have hnn := noiseOp_nonneg hρ0 hρ1 (g := fun y ↦ f y + ‖f‖)
      (fun y ↦ by linarith [neg_abs_le (f y), hbound y]) x
    rw [noiseOp_add, noiseOp_const] at hnn
    linarith
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- **Homogeneous level projection bound**: for every finite index type `ι`, degree `d ≥ 1`,
`f ∈ lowDegree ℝ ι d`, and level `l : ℕ`, `‖levelPart l f‖ ≤ (2 e) ^ d * ‖f‖`. -/
theorem norm_levelPart_le {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (hd : 1 ≤ d)
    {f : (ι → Bool) → ℝ} (hf : f ∈ lowDegree ℝ ι d) (l : ℕ) :
    ‖levelPart l f‖ ≤ (2 * Real.exp 1) ^ d * ‖f‖ := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdeg := mem_lowDegree_iff_fourierCoeff_eq_zero.mp hf
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg f))).mpr fun x ↦ ?_
  rw [Real.norm_eq_abs]
  by_cases hld : l ≤ d
  · let s : Finset ℕ := Finset.range (d + 1)
    let v : ℕ → ℝ := fun j ↦ -1 + 2 * (j : ℝ) / (d : ℝ)
    have hvs : Set.InjOn v s := fun i _ j _ hij ↦ by
      dsimp [v] at hij
      have h1 : 2 * (i : ℝ) / (d : ℝ) = 2 * (j : ℝ) / (d : ℝ) := by linarith
      have h2 : (i : ℝ) = (j : ℝ) := by
        have := (div_left_inj₀ (ne_of_gt hd_pos)).mp h1
        linarith
      exact Nat.cast_injective h2
    have hv_mem : ∀ j ∈ s, v j ∈ Set.Icc (-1 : ℝ) 1 := fun j hj ↦ by
      have hjd : (j : ℝ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      dsimp [v]
      refine ⟨by linarith [div_nonneg (by positivity : (0 : ℝ) ≤ 2 * j) hd_pos.le], ?_⟩
      have hdiv : 2 * (j : ℝ) / (d : ℝ) ≤ 2 := (div_le_iff₀ hd_pos).mpr (by linarith)
      linarith
    let P : Polynomial ℝ :=
      ∑ m ∈ s, Polynomial.C (levelPart m f x) * Polynomial.X ^ m
    have hP_deg : P.degree < s.card := by
      have hcard : s.card = d + 1 := Finset.card_range (d + 1)
      rw [hcard, Nat.cast_withBot]
      refine (Polynomial.degree_sum_le s _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe (d + 1))]
      intro m hm
      exact (Polynomial.degree_C_mul_X_pow_le m _).trans_lt
        (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hm))
    have hP_coeff : P.coeff l = levelPart l f x := by
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single l]
      · simp
      · intro m _ hml
        simp [Ne.symm hml]
      · intro hl_not
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hld)) hl_not
    have hP_eval : ∀ ρ : ℝ, P.eval ρ = noiseOp ρ f x := fun ρ ↦ by
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, levelPart_eq_sum_ite, Finset.sum_mul]
      rw [Finset.sum_comm, noiseOp_eq_sum]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      by_cases hTd : T.card ≤ d
      · rw [Finset.sum_eq_single T.card]
        · simp [mul_left_comm, mul_comm]
        · intro m _ hm
          simp [Ne.symm hm]
        · intro hnot
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hTd)) hnot
      · rw [Finset.sum_eq_zero]
        · rw [hdeg T (not_le.mp hTd)]
          ring
        · intro m hm
          have hne : T.card ≠ m :=
            ne_of_gt ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)).trans_lt (not_le.mp hTd))
          simp [hne]
    have hinterp : P = Lagrange.interpolate s v (fun j ↦ P.eval (v j)) :=
      Lagrange.eq_interpolate hvs hP_deg
    have hbasis_coeff : ∀ j ∈ s,
        |(Lagrange.basis s v j).coeff l| ≤
          ((d : ℝ) ^ d / (d.factorial : ℝ)) * (d.choose j : ℝ) := fun j hj ↦ by
      have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hcard_erase : (s.erase j).card = d := by
        rw [Finset.card_erase_of_mem hj, Finset.card_range, Nat.add_sub_cancel]
      have hbasis_eq :
          Lagrange.basis s v j =
            Polynomial.C (∏ m ∈ s.erase j, (v j - v m)⁻¹) *
              ∏ m ∈ s.erase j, (Polynomial.X - Polynomial.C (v m)) := by
        simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, map_prod]
      rw [hbasis_eq, Polynomial.coeff_C_mul, abs_mul, Finset.abs_prod]
      have hprod_inv :
          (∏ m ∈ s.erase j, |(v j - v m)⁻¹|) =
            (((2 / (d : ℝ)) ^ d) * ((j.factorial : ℝ) * ((d - j).factorial : ℝ)))⁻¹ := by
        simp_rw [abs_inv]
        rw [Finset.prod_inv_distrib]
        congr 1
        have hdiff : ∀ m ∈ s.erase j,
            |v j - v m| = (2 / (d : ℝ)) * |(j : ℝ) - (m : ℝ)| := fun m _ ↦ by
          have heq : v j - v m = (2 / (d : ℝ)) * ((j : ℝ) - (m : ℝ)) := by
            dsimp [v]
            ring
          rw [heq, abs_mul, abs_of_pos (by positivity)]
        rw [Finset.prod_congr rfl hdiff, Finset.prod_mul_distrib, Finset.prod_const, hcard_erase,
          prod_abs_sub_erase_range d j hjd]
      have hpoly_le := abs_coeff_prod_X_sub_C_le (s.erase j) v
        (fun m hm ↦ abs_le.mpr (hv_mem m (Finset.mem_of_mem_erase hm))) l
      rw [hcard_erase] at hpoly_le
      have hchoose_id :
          (((2 / (d : ℝ)) ^ d) * ((j.factorial : ℝ) * ((d - j).factorial : ℝ)))⁻¹ * (2 : ℝ) ^ d =
            ((d : ℝ) ^ d / (d.factorial : ℝ)) * (d.choose j : ℝ) := by
        have hch : (d.choose j : ℝ) * ((j.factorial : ℝ) * ((d - j).factorial : ℝ)) =
            (d.factorial : ℝ) := by
          rw [← mul_assoc]
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjd
        have h1 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        have h2 : ((d - j).factorial : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (d - j))
        have h3 : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
        rw [div_pow]
        field_simp [hd_pos.ne', h1, h2, h3]
        linarith [congrArg ((d : ℝ) ^ d * (2 : ℝ) ^ d * ·) hch.symm]
      rw [hprod_inv]
      exact (mul_le_mul_of_nonneg_left hpoly_le (by positivity)).trans_eq hchoose_id
    calc
      |levelPart l f x|
          = |(Lagrange.interpolate s v (fun j ↦ P.eval (v j))).coeff l| := by
              rw [← hP_coeff]
              conv_lhs => rw [hinterp]
      _ = |∑ j ∈ s, P.eval (v j) * (Lagrange.basis s v j).coeff l| := by
              simp [Lagrange.interpolate_apply, Polynomial.coeff_C_mul]
      _ ≤ ∑ j ∈ s, |P.eval (v j) * (Lagrange.basis s v j).coeff l| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, ‖f‖ * (((d : ℝ) ^ d / (d.factorial : ℝ)) * (d.choose j : ℝ)) := by
              refine Finset.sum_le_sum fun j hj ↦ ?_
              rw [abs_mul, hP_eval (v j)]
              exact mul_le_mul
                (abs_noiseOp_le_norm (hv_mem j hj).1 (hv_mem j hj).2 f x)
                (hbasis_coeff j hj) (abs_nonneg _) (norm_nonneg f)
      _ = ‖f‖ * (((d : ℝ) ^ d / (d.factorial : ℝ)) * ∑ j ∈ s, (d.choose j : ℝ)) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = ((2 : ℝ) ^ d * ((d : ℝ) ^ d / (d.factorial : ℝ))) * ‖f‖ := by
              have hsum_ch : (∑ j ∈ s, (d.choose j : ℝ)) = (2 : ℝ) ^ d := by
                exact_mod_cast Nat.sum_range_choose d
              rw [hsum_ch]
              ring
      _ ≤ ((2 : ℝ) ^ d * (Real.exp 1) ^ d) * ‖f‖ := by
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg f)
              rw [← Real.exp_nat_mul, mul_one]
              exact pow_div_factorial_le_exp_nat d d
      _ = (2 * Real.exp 1) ^ d * ‖f‖ := by rw [← mul_pow]
  · have hzero : levelPart l f x = 0 := by
      rw [levelPart_eq_sum_ite]
      refine Finset.sum_eq_zero fun T _ ↦ ?_
      split_ifs with hcard
      · rw [hdeg T (hcard ▸ not_le.mp hld), zero_mul]
      · rw [zero_mul]
    rw [hzero, abs_zero]
    exact mul_nonneg (by positivity) (norm_nonneg f)

/-! ### 4. Random `k`-coloring decoupling and Boolean Bohnenblust–Hille inequality -/

private theorem coloring_avg_walsh_eq {n k : ℕ} (φ : Fin n → Fin k)
    (S : Finset (Fin n)) (hS : S.card = k) :
    ((2 : ℝ) ^ k)⁻¹ *
      ∑ ε : Fin k → Bool,
        (∏ r : Fin k, signVal (ε r)) * (∏ j ∈ S, signVal (ε (φ j))) =
      if Set.InjOn φ (S : Set (Fin n)) then 1 else 0 := by
  classical
  have hprod_S : ∀ ε : Fin k → Bool,
      ∏ j ∈ S, signVal (ε (φ j)) =
        ∏ r : Fin k, (signVal (ε r)) ^ (S.filter (fun j ↦ φ j = r)).card := fun ε ↦ by
    rw [← Finset.prod_fiberwise_of_maps_to (g := φ) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2]
  have hterm : ∀ ε : Fin k → Bool,
      (∏ r : Fin k, signVal (ε r)) * (∏ j ∈ S, signVal (ε (φ j))) =
        ∏ r : Fin k, (signVal (ε r)) ^ ((S.filter (fun j ↦ φ j = r)).card + 1) := fun ε ↦ by
    rw [hprod_S ε, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun r _ ↦ (pow_succ' _ _).symm
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (r : Fin k) (b : Bool) ↦
    (signVal b) ^ ((S.filter (fun j ↦ φ j = r)).card + 1))]
  split_ifs with hinj
  · have himg : S.image φ = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [Finset.card_image_of_injOn hinj, hS, Fintype.card_fin]
    have hcard_one : ∀ r : Fin k, (S.filter (fun j ↦ φ j = r)).card = 1 := fun r ↦ by
      have hr : r ∈ S.image φ := himg ▸ Finset.mem_univ r
      obtain ⟨j₀, hj₀S, hj₀φ⟩ := Finset.mem_image.mp hr
      have hfilt : S.filter (fun j ↦ φ j = r) = {j₀} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun ⟨hjS, hjφ⟩ ↦ hinj hjS hj₀S (hjφ.trans hj₀φ.symm),
          fun h ↦ h ▸ ⟨hj₀S, hj₀φ⟩⟩
      rw [hfilt, Finset.card_singleton]
    have hprod_two :
        ∏ r : Fin k, ∑ b : Bool, (signVal b) ^ ((S.filter (fun j ↦ φ j = r)).card + 1) =
          (2 : ℝ) ^ k := by
      calc
        ∏ r : Fin k, ∑ b : Bool, (signVal b) ^ ((S.filter (fun j ↦ φ j = r)).card + 1)
            = ∏ _r : Fin k, (2 : ℝ) := by
              refine Finset.prod_congr rfl fun r _ ↦ ?_
              rw [hcard_one r, Fintype.sum_bool, signVal_false, signVal_true]
              norm_num
        _ = (2 : ℝ) ^ k := by simp
    rw [hprod_two, inv_mul_cancel₀ (by positivity)]
  · have hlt : (S.image φ).card < Fintype.card (Fin k) := by
      rw [Fintype.card_fin]
      exact (lt_of_le_of_ne Finset.card_image_le
        (fun heq ↦ hinj (Finset.injOn_of_card_image_eq heq))).trans_eq hS
    have hne : S.image φ ≠ Finset.univ := fun h ↦ by
      rw [h, Finset.card_univ] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Fin k, r₀ ∉ S.image φ := by
      by_contra hall
      push Not at hall
      exact hne (Finset.eq_univ_iff_forall.mpr hall)
    have hcard_zero : (S.filter (fun j ↦ φ j = r₀)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj hφ
      exact hr₀ (Finset.mem_image.mpr ⟨j, hj, hφ⟩)
    have hzero :
        ∏ r : Fin k, ∑ b : Bool, (signVal b) ^ ((S.filter (fun j ↦ φ j = r)).card + 1) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ r₀) ?_
      rw [hcard_zero, Fintype.sum_bool, signVal_false, signVal_true]
      norm_num
    rw [hzero, mul_zero]

private theorem sum_coloring_decoupled_bij {n k : ℕ} (φ : Fin n → Fin k)
    (h : (Fin k → Fin n) → ℝ) (h' : Finset (Fin n) → ℝ)
    (hmatch : ∀ i : Fin k → Fin n, (∀ r : Fin k, φ (i r) = r) →
      h i = h' (Finset.univ.image i)) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin k → Fin n ↦ ∀ r : Fin k, φ (i r) = r), h i =
      ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card), h' S := by
  refine Finset.sum_bij (fun i _ ↦ Finset.univ.image i) ?_ ?_ ?_ ?_
  · intro i hi
    have hφ : ∀ r : Fin k, φ (i r) = r := (Finset.mem_filter.mp hi).2
    have hi_inj : Function.Injective i := fun r₁ r₂ heq ↦ by
      have h1 := hφ r₁
      have h2 := hφ r₂
      rw [heq] at h1
      exact h1.symm.trans h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injective _ hi_inj, Finset.card_univ, Fintype.card_fin]
    · refine Finset.card_image_of_injOn fun a ha b hb hab ↦ ?_
      obtain ⟨r₁, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
      obtain ⟨r₂, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
      have hr : r₁ = r₂ := (hφ r₁).symm.trans (hab.trans (hφ r₂))
      rw [hr]
  · intro i₁ hi₁ i₂ hi₂ heq
    have hφ₁ : ∀ r : Fin k, φ (i₁ r) = r := (Finset.mem_filter.mp hi₁).2
    have hφ₂ : ∀ r : Fin k, φ (i₂ r) = r := (Finset.mem_filter.mp hi₂).2
    funext r
    have hmem : i₁ r ∈ Finset.univ.image i₂ := heq ▸ Finset.mem_image_of_mem i₁ (Finset.mem_univ r)
    obtain ⟨r', -, hr'⟩ := Finset.mem_image.mp hmem
    have hrr' : r' = r := (hφ₂ r').symm.trans (by rw [hr', hφ₁ r])
    rw [← hr', hrr']
  · intro S hS
    have hS_card : S.card = k := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
    have hS_img : (S.image φ).card = S.card := (Finset.mem_filter.mp hS).2
    have himg : S.image φ = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [hS_img, hS_card, Fintype.card_fin]
    have hex : ∀ r : Fin k, ∃ j ∈ S, φ j = r := fun r ↦
      Finset.mem_image.mp (himg ▸ Finset.mem_univ r)
    let i : Fin k → Fin n := fun r ↦ Classical.choose (hex r)
    have hiS : ∀ r : Fin k, i r ∈ S := fun r ↦ (Classical.choose_spec (hex r)).1
    have hiφ : ∀ r : Fin k, φ (i r) = r := fun r ↦ (Classical.choose_spec (hex r)).2
    have hi_inj : Function.Injective i := fun r₁ r₂ heq ↦ by
      have h1 := hiφ r₁
      have h2 := hiφ r₂
      rw [heq] at h1
      exact h1.symm.trans h2
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiφ⟩, ?_⟩
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro j hj
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hj
      exact hiS r
    · rw [Finset.card_image_of_injective _ hi_inj, Finset.card_univ, Fintype.card_fin, hS_card]
  · intro i hi
    exact hmatch i (Finset.mem_filter.mp hi).2

private theorem sum_injOn_rpow_le_of_coloring {n k : ℕ} (hk : 1 ≤ k)
    (f : (Fin n → Bool) → ℝ) (φ : Fin n → Fin k) :
    ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
        |fourierCoeff f S| ^ bhExponent k ≤
      ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ bhExponent k := by
  let p : ℝ := bhExponent k
  have hp0 : 0 < p := bhExponent_pos hk
  let c : (Fin k → Fin n) → ℝ := fun i ↦
    if ∀ r : Fin k, φ (i r) = r then fourierCoeff f (Finset.univ.image i) else 0
  have hbound : ∀ x : Fin k → Fin n → Bool,
      |∑ i : Fin k → Fin n, c i * ∏ r : Fin k, signVal (x r (i r))| ≤ ‖levelPart k f‖ := by
    intro x
    let z : (Fin k → Bool) → (Fin n → Bool) := fun ε j ↦ xor (ε (φ j)) (x (φ j) j)
    have hsum_c :
        ∑ i : Fin k → Fin n, c i * ∏ r : Fin k, signVal (x r (i r)) =
          ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
            (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
            fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j) := by
      have hfilt :
          ∑ i : Fin k → Fin n, c i * ∏ r : Fin k, signVal (x r (i r)) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin k → Fin n ↦ ∀ r : Fin k, φ (i r) = r),
              fourierCoeff f (Finset.univ.image i) * ∏ r : Fin k, signVal (x r (i r)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        dsimp [c]
        split_ifs <;> simp
      rw [hfilt]
      refine sum_coloring_decoupled_bij φ _ _ fun i hi ↦ ?_
      have hi_inj : Function.Injective i := fun r₁ r₂ heq ↦ by
        have h1 := hi r₁
        have h2 := hi r₂
        rw [heq] at h1
        exact h1.symm.trans h2
      congr 1
      rw [Finset.prod_image (fun r₁ _ r₂ _ heq ↦ hi_inj heq)]
      exact Finset.prod_congr rfl fun r _ ↦ by rw [hi r]
    have havg :
        ((2 : ℝ) ^ k)⁻¹ *
          ∑ ε : Fin k → Bool,
            (∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε) =
          ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
            (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
            fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j) := by
      classical
      have hexpand : ∀ ε : Fin k → Bool,
          (∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε) =
            ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              (fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j)) *
                ((∏ r : Fin k, signVal (ε r)) * ∏ j ∈ S, signVal (ε (φ j))) := fun ε ↦ by
        have hlev : levelPart k f (z ε) =
            ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              fourierCoeff f S * chi ℝ S (z ε) := by
          rw [levelPart_eq_sum_ite]
          simp_rw [ite_mul, zero_mul, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ ↦ rfl
          ext S
          simp
        rw [hlev, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        have hwalsh : chi ℝ S (z ε) =
            (∏ j ∈ S, signVal (ε (φ j))) * (∏ j ∈ S, signVal (x (φ j) j)) := by
          rw [chi_eq_prod_signVal, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun j _ ↦ signVal_xor _ _
        rw [hwalsh]
        ring
      simp_rw [hexpand]
      rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      have hS_card : S.card = k := (Finset.mem_powersetCard.mp hS).2
      rw [← Finset.mul_sum]
      calc
        ((2 : ℝ) ^ k)⁻¹ *
            ((fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j)) *
              ∑ ε : Fin k → Bool, (∏ r : Fin k, signVal (ε r)) * ∏ j ∈ S, signVal (ε (φ j)))
            = (fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j)) *
                (((2 : ℝ) ^ k)⁻¹ *
                  ∑ ε : Fin k → Bool,
                    (∏ r : Fin k, signVal (ε r)) * ∏ j ∈ S, signVal (ε (φ j))) := by ring
        _ = (fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j)) *
              (if Set.InjOn φ (S : Set (Fin n)) then 1 else 0) := by
            rw [coloring_avg_walsh_eq φ S hS_card]
        _ = if (S.image φ).card = S.card then
              fourierCoeff f S * ∏ j ∈ S, signVal (x (φ j) j) else 0 := by
            simp only [Finset.card_image_iff]
            split_ifs <;> ring
    rw [hsum_c, ← havg, abs_mul, abs_of_nonneg (by positivity)]
    have htri :
        |∑ ε : Fin k → Bool, (∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε)| ≤
          ∑ ε : Fin k → Bool, |(∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε)| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm_le : ∀ ε : Fin k → Bool,
        |(∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε)| ≤ ‖levelPart k f‖ := fun ε ↦ by
      rw [abs_mul, Finset.abs_prod]
      have hprod1 : (∏ r : Fin k, |signVal (ε r)|) = 1 :=
        Finset.prod_eq_one fun r _ ↦ abs_signVal (ε r)
      rw [hprod1, one_mul]
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (levelPart k f) (z ε)
    have hsum_le :
        ∑ ε : Fin k → Bool, |(∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε)| ≤
          (2 : ℝ) ^ k * ‖levelPart k f‖ := by
      calc
        ∑ ε : Fin k → Bool, |(∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε)|
            ≤ ∑ _ε : Fin k → Bool, ‖levelPart k f‖ := Finset.sum_le_sum fun ε _ ↦ hterm_le ε
        _ = (2 : ℝ) ^ k * ‖levelPart k f‖ := by simp [Fintype.card_bool, Fintype.card_fin]
    calc
      ((2 : ℝ) ^ k)⁻¹ *
          |∑ ε : Fin k → Bool, (∏ r : Fin k, signVal (ε r)) * levelPart k f (z ε)|
          ≤ ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k * ‖levelPart k f‖) :=
            mul_le_mul_of_nonneg_left (htri.trans hsum_le) (by positivity)
      _ = ‖levelPart k f‖ := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hbh := bh_multilinear_rpow_le hk c (norm_nonneg (levelPart k f)) hbound
  have hsum_abs_eq :
      ∑ i : Fin k → Fin n, |c i| ^ p =
        ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
          |fourierCoeff f S| ^ p := by
    have hfilt :
        ∑ i : Fin k → Fin n, |c i| ^ p =
          ∑ i ∈ Finset.univ.filter (fun i : Fin k → Fin n ↦ ∀ r : Fin k, φ (i r) = r),
            |fourierCoeff f (Finset.univ.image i)| ^ p := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp [c]
      split_ifs
      · rfl
      · simp [Real.zero_rpow hp0.ne']
    rw [hfilt]
    exact sum_coloring_decoupled_bij φ _ _ fun _ _ ↦ rfl
  rw [← hsum_abs_eq]
  have hsum_nn : 0 ≤ ∑ i : Fin k → Fin n, |c i| ^ p :=
    Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hsum_nn _) hbh hp0.le
  rwa [← Real.rpow_mul hsum_nn, one_div_mul_cancel hp0.ne', Real.rpow_one] at hpow

private theorem card_filter_injOn_coloring {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) :
    ((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun φ ↦ (S.image φ).card = S.card)).card = k.factorial * k ^ (n - k) := by
  let e : {φ : Fin n → Fin k // (S.image φ).card = S.card} ≃
      (S ≃ Fin k) × ({j : Fin n // j ∉ S} → Fin k) :=
    { toFun := fun ⟨φ, hφ⟩ ↦
        (Equiv.ofBijective (fun s : S ↦ φ s.1)
          ((Fintype.bijective_iff_injective_and_card _).2
            ⟨fun s₁ s₂ heq ↦ Subtype.ext ((Finset.card_image_iff.mp hφ) s₁.2 s₂.2 heq), by
              rw [Fintype.card_coe, hS, Fintype.card_fin]⟩),
          fun j ↦ φ j.1)
      invFun := fun ⟨e₁, g⟩ ↦
        ⟨fun j ↦ if h : j ∈ S then e₁ ⟨j, h⟩ else g ⟨j, h⟩, by
          refine Finset.card_image_of_injOn fun a ha b hb hab ↦ ?_
          simp only [Finset.mem_coe.mp ha, Finset.mem_coe.mp hb, ↓reduceDIte] at hab
          exact congrArg Subtype.val (e₁.injective hab)⟩
      left_inv := fun ⟨φ, _⟩ ↦ by
        ext j
        by_cases hj : j ∈ S <;> simp [hj]
      right_inv := fun ⟨_, _⟩ ↦ by
        ext x
        · simp
        · simp [x.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  have hS_equiv : Fintype.card (S ≃ Fin k) = k.factorial := by
    have hcard : Fintype.card S = Fintype.card (Fin k) := by
      rw [Fintype.card_coe, hS, Fintype.card_fin]
    let eqS : S ≃ Fin k := Fintype.equivOfCardEq hcard
    rw [Fintype.card_congr (Equiv.equivCongr eqS (Equiv.refl (Fin k))), Fintype.card_perm,
      Fintype.card_fin]
  have hcompl_card : Fintype.card {j : Fin n // j ∉ S} = n - k := by
    have hfilt : (Finset.univ.filter (fun j : Fin n ↦ j ∉ S)) = Sᶜ := by ext j; simp
    rw [Fintype.card_subtype, hfilt, Finset.card_compl, Fintype.card_fin, hS]
  rw [hS_equiv, hcompl_card, Fintype.card_fin]

private theorem sum_powersetCard_rpow_fourierCoeff_le_factorial_exp_fin {n k : ℕ} (hk : 1 ≤ k)
    (f : (Fin n → Bool) → ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        |fourierCoeff f S| ^ bhExponent k ≤
      ((k : ℝ) ^ k / (k.factorial : ℝ)) *
        ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ bhExponent k := by
  let p : ℝ := bhExponent k
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have havg :
      ∑ φ : Fin n → Fin k,
        ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
            (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
          |fourierCoeff f S| ^ p ≤
        ((k : ℝ) ^ n) * ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ p := by
    calc
      ∑ φ : Fin n → Fin k,
          ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
              (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
            |fourierCoeff f S| ^ p
          ≤ ∑ _φ : Fin n → Fin k, ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ p :=
            Finset.sum_le_sum fun φ _ ↦ sum_injOn_rpow_le_of_coloring hk f φ
      _ = ((k : ℝ) ^ n) * ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ p := by
            simp [Fintype.card_fin]
  have hswap :
      ∑ φ : Fin n → Fin k,
        ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard k).filter
            (fun S : Finset (Fin n) ↦ (S.image φ).card = S.card),
          |fourierCoeff f S| ^ p =
        ((k.factorial : ℝ) * (k : ℝ) ^ (n - k)) *
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, |fourierCoeff f S| ^ p := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS ↦ ?_
    have hS_card : S.card = k := (Finset.mem_powersetCard.mp hS).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_filter_injOn_coloring S hS_card, Nat.cast_mul, Nat.cast_pow]
  rw [hswap] at havg
  by_cases hkn : k ≤ n
  · have hkn_pow : (k : ℝ) ^ n = (k : ℝ) ^ k * (k : ℝ) ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) * (k : ℝ) ^ (n - k) := by positivity
    rw [hkn_pow] at havg
    have hdiv := (le_div_iff₀' hfac_pos).2 havg
    refine hdiv.trans_eq ?_
    have hnk_ne : (k : ℝ) ^ (n - k) ≠ 0 := by positivity
    have hfac_ne : (k.factorial : ℝ) ≠ 0 := by positivity
    dsimp only [p]
    field_simp [hnk_ne, hfac_ne]
  · have hempty : (Finset.univ : Finset (Fin n)).powersetCard k = ∅ := by
      rw [Finset.powersetCard_eq_empty]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    rw [hempty, Finset.sum_empty]
    positivity

private theorem norm_comp_equiv {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (e : ι₁ ≃ ι₂) (f : (ι₂ → Bool) → ℝ) :
    ‖fun y : ι₁ → Bool ↦ f (fun j ↦ y (e.symm j))‖ = ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 fun y ↦ ?_
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm f (fun j ↦ y (e.symm j))
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun x ↦ ?_
    have h := norm_le_pi_norm (fun y : ι₁ → Bool ↦ f (fun j ↦ y (e.symm j))) (fun i ↦ x (e i))
    have hcomp : (fun j ↦ x (e (e.symm j))) = x := by ext j; simp
    simpa only [hcomp, Real.norm_eq_abs] using h

private theorem levelPart_eq_sum_powersetCard {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (q : (α → Bool) → ℝ) (z : α → Bool) :
    levelPart k q z =
      ∑ T ∈ (Finset.univ : Finset α).powersetCard k, fourierCoeff q T * chi ℝ T z := by
  rw [levelPart_eq_sum_ite]
  simp_rw [ite_mul, zero_mul, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext T
  simp

/-- **Decoupled homogeneous level-`k` Bohnenblust–Hille inequality**: for any finite index type
`ι`, `k ≥ 1`, and `f : (ι → Bool) → ℝ`,
`∑_{|S| = k} |fourierCoeff f S| ^ (2k / (k + 1)) ≤`
`(k ^ k / k!) * ((√2) ^ (k - 1) * ‖levelPart k f‖) ^ (2k / (k + 1))`. -/
theorem sum_powersetCard_rpow_fourierCoeff_le_factorial_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (hk : 1 ≤ k) (f : (ι → Bool) → ℝ) :
    ∑ S ∈ (Finset.univ : Finset ι).powersetCard k,
        |fourierCoeff f S| ^ bhExponent k ≤
      ((k : ℝ) ^ k / (k.factorial : ℝ)) *
        ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ bhExponent k := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let g : (Fin (Fintype.card ι) → Bool) → ℝ := fun y ↦ f (fun j ↦ y (e.symm j))
  have hfin := sum_powersetCard_rpow_fourierCoeff_le_factorial_exp_fin hk g
  have hbij : ∀ (h : Finset ι → ℝ) (h' : Finset (Fin (Fintype.card ι)) → ℝ),
      (∀ T, h' T = h (T.map e.toEmbedding)) →
      ∑ T ∈ (Finset.univ : Finset (Fin (Fintype.card ι))).powersetCard k, h' T =
        ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, h S := fun h h' hcomp ↦
    Finset.sum_bij (fun T _ ↦ T.map e.toEmbedding)
      (fun _ hT ↦ Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
        simpa using (Finset.mem_powersetCard.mp hT).2⟩)
      (fun _ _ _ _ heq ↦ Finset.map_injective e.toEmbedding heq)
      (fun S hS ↦ ⟨S.map e.symm.toEmbedding,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
          simpa using (Finset.mem_powersetCard.mp hS).2⟩, by ext i; simp⟩)
      (fun T _ ↦ hcomp T)
  have hcoeff : ∀ T : Finset (Fin (Fintype.card ι)),
      fourierCoeff g T = fourierCoeff f (T.map e.toEmbedding) :=
    fun T ↦ fourierCoeff_comp_arrowCongr e f T
  have hsum_eq := hbij (fun S ↦ |fourierCoeff f S| ^ bhExponent k)
    (fun T ↦ |fourierCoeff g T| ^ bhExponent k) (fun T ↦ by rw [hcoeff])
  have hproj_eq :
      (fun y : Fin (Fintype.card ι) → Bool ↦ levelPart k f (fun j ↦ y (e.symm j))) =
        levelPart k g := by
    funext y
    rw [levelPart_eq_sum_powersetCard, levelPart_eq_sum_powersetCard]
    refine (hbij _ _ fun T ↦ ?_).symm
    rw [hcoeff, chi_eq_prod_signVal, chi_eq_prod_signVal, Finset.prod_map]
    exact congrArg (fourierCoeff f (T.map e.toEmbedding) * ·)
      (Finset.prod_congr rfl fun j _ ↦ by simp)
  have hnorm_eq : ‖levelPart k g‖ = ‖levelPart k f‖ := by
    rw [← hproj_eq, norm_comp_equiv e]
  rwa [hsum_eq, hnorm_eq] at hfin

/-- **Exponential-constant homogeneous level-`k` Bohnenblust–Hille inequality**: for any finite
index type `ι`, `k ≥ 1`, and `f : (ι → Bool) → ℝ`,
`(∑_{|S| = k} |fourierCoeff f S| ^ (2k / (k + 1))) ^ ((k + 1) / (2k)) ≤`
`(e √2) ^ k * ‖levelPart k f‖`. -/
theorem sum_powersetCard_rpow_fourierCoeff_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (hk : 1 ≤ k) (f : (ι → Bool) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset ι).powersetCard k,
        |fourierCoeff f S| ^ bhExponent k) ^ (1 / bhExponent k) ≤
      (Real.exp 1 * Real.sqrt 2) ^ k * ‖levelPart k f‖ := by
  set p : ℝ := bhExponent k
  have hp1 : 1 ≤ p := one_le_bhExponent hk
  have hp0 : 0 < p := zero_lt_one.trans_le hp1
  have hsum_nn : 0 ≤ ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, |fourierCoeff f S| ^ p :=
    Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hbase := sum_powersetCard_rpow_fourierCoeff_le_factorial_exp hk f
  have hfac_le : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
    exact pow_div_factorial_le_exp_nat k k
  have hstep :
      ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, |fourierCoeff f S| ^ p ≤
        (Real.exp 1) ^ k * ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ p :=
    hbase.trans (mul_le_mul_of_nonneg_right hfac_le (Real.rpow_nonneg (by positivity) _))
  have hpow := Real.rpow_le_rpow hsum_nn hstep (one_div_nonneg.mpr hp0.le)
  have hexp1 : 1 ≤ (Real.exp 1) ^ k := one_le_pow₀ (Real.one_le_exp zero_le_one)
  have hexp_rpow : ((Real.exp 1) ^ k) ^ (1 / p) ≤ (Real.exp 1) ^ k :=
    (Real.rpow_le_rpow_of_exponent_le hexp1 (div_le_one_of_le₀ hp1 hp0.le)).trans_eq
      (Real.rpow_one _)
  have hsqrt_le : (Real.sqrt 2) ^ (k - 1) ≤ (Real.sqrt 2) ^ k :=
    pow_le_pow_right₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num))
      (Nat.sub_le k 1)
  calc
    (∑ S ∈ (Finset.univ : Finset ι).powersetCard k, |fourierCoeff f S| ^ p) ^ (1 / p)
        ≤ ((Real.exp 1) ^ k * ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ p) ^ (1 / p) := hpow
    _ = ((Real.exp 1) ^ k) ^ (1 / p) *
          (((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) ^ p) ^ (1 / p) :=
          Real.mul_rpow (by positivity) (Real.rpow_nonneg (by positivity) _)
    _ = ((Real.exp 1) ^ k) ^ (1 / p) * ((Real.sqrt 2) ^ (k - 1) * ‖levelPart k f‖) := by
          rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hp0.ne', Real.rpow_one]
    _ ≤ (Real.exp 1) ^ k * ((Real.sqrt 2) ^ k * ‖levelPart k f‖) :=
          mul_le_mul hexp_rpow (mul_le_mul_of_nonneg_right hsqrt_le (norm_nonneg _))
            (by positivity) (by positivity)
    _ = (Real.exp 1 * Real.sqrt 2) ^ k * ‖levelPart k f‖ := by rw [mul_pow, mul_assoc]

/-- **Exponential-constant discrete Bohnenblust–Hille polynomial inequality**: for any finite
index type `ι`, degree `d ≥ 1`, and `f ∈ lowDegree ℝ ι d`,
`(∑ S, |fourierCoeff f S| ^ (2d / (d + 1))) ^ ((d + 1) / (2d)) ≤ (4 e ^ 2 √2) ^ d * ‖f‖`. -/
theorem sum_rpow_fourierCoeff_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (hd : 1 ≤ d) {f : (ι → Bool) → ℝ} (hf : f ∈ lowDegree ℝ ι d) :
    (∑ S : Finset ι, |fourierCoeff f S| ^ bhExponent d) ^ (1 / bhExponent d) ≤
      (4 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖ := by
  set p : ℝ := bhExponent d
  have hp1 : 1 ≤ p := one_le_bhExponent hd
  have hp0 : 0 < p := zero_lt_one.trans_le hp1
  have hdeg := mem_lowDegree_iff_fourierCoeff_eq_zero.mp hf
  have hdeg_split :
      (∑ S : Finset ι, |fourierCoeff f S| ^ p) =
        ∑ l ∈ Finset.range (d + 1),
          ∑ S ∈ (Finset.univ : Finset ι).powersetCard l, |fourierCoeff f S| ^ p := by
    have hfilt :
        (∑ S : Finset ι, |fourierCoeff f S| ^ p) =
          ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d), |fourierCoeff f S| ^ p := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun S _ hnot ↦ ?_
      rw [hdeg S (lt_of_not_ge fun hle ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hle⟩)),
        abs_zero, Real.zero_rpow hp0.ne']
    rw [hfilt, ← Finset.sum_fiberwise_of_maps_to (g := fun S : Finset ι ↦ S.card)
      (fun S hS ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2))]
    refine Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.symm ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hl), h⟩⟩
  let a : ℕ → ℝ := fun l ↦
    (∑ S ∈ (Finset.univ : Finset ι).powersetCard l, |fourierCoeff f S| ^ p) ^ (1 / p)
  have ha_pow (l : ℕ) :
      ∑ S ∈ (Finset.univ : Finset ι).powersetCard l, |fourierCoeff f S| ^ p = a l ^ p := by
    dsimp [a]
    rw [← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) p),
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hsum_levels :
      (∑ S : Finset ι, |fourierCoeff f S| ^ p) ^ (1 / p) ≤ ∑ l ∈ Finset.range (d + 1), a l := by
    rw [hdeg_split]
    simp_rw [ha_pow]
    have ha_nn (l : ℕ) : 0 ≤ a l := Real.rpow_nonneg
      (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) p) _
    have hmono := sum_abs_rpow_le_of_le (Finset.range (d + 1)) a zero_lt_one hp1
    simp_rw [abs_of_nonneg (ha_nn _), Real.rpow_one, div_one] at hmono
    simpa only [Real.rpow_one] using hmono
  have hbase_ge_one : 1 ≤ Real.exp 1 * Real.sqrt 2 := by
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hs2 : 1 ≤ Real.sqrt 2 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  have hexp2_eq : 2 * Real.exp 2 * Real.sqrt 2 = (Real.exp 1 * Real.sqrt 2) * (2 * Real.exp 1) := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; ring
  have hterm (l : ℕ) (hl : l ∈ Finset.range (d + 1)) :
      a l ≤ (2 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖ := by
    have hld : l ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rcases Nat.eq_zero_or_pos l with rfl | hl_pos
    · have ha0 : a 0 = |fourierCoeff f ∅| := by
        dsimp [a]
        rw [Finset.powersetCard_zero, Finset.sum_singleton,
          ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
      have h0_le : |fourierCoeff f ∅| ≤ ‖f‖ :=
        (abs_fourierCoeff_le_expect_abs f ∅).trans ((Finset.expect_le_expect fun x _ ↦ by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm f x).trans_eq (Fintype.expect_const _))
      have hge1 : 1 ≤ (2 * Real.exp 2 * Real.sqrt 2) ^ d := by
        refine one_le_pow₀ ?_
        rw [hexp2_eq]; nlinarith [Real.one_le_exp (zero_le_one' ℝ)]
      rw [ha0]
      exact h0_le.trans (le_mul_of_one_le_left (norm_nonneg f) hge1)
    · have hpl_pos : 0 < bhExponent l := bhExponent_pos hl_pos
      calc
        a l ≤ (∑ S ∈ (Finset.univ : Finset ι).powersetCard l,
              |fourierCoeff f S| ^ bhExponent l) ^ (1 / bhExponent l) :=
            sum_abs_rpow_le_of_le ((Finset.univ : Finset ι).powersetCard l) (fourierCoeff f)
              hpl_pos (bhExponent_mono hld)
        _ ≤ (Real.exp 1 * Real.sqrt 2) ^ l * ‖levelPart l f‖ :=
            sum_powersetCard_rpow_fourierCoeff_le_exp hl_pos f
        _ ≤ (Real.exp 1 * Real.sqrt 2) ^ d * ((2 * Real.exp 1) ^ d * ‖f‖) :=
            mul_le_mul (pow_le_pow_right₀ hbase_ge_one hld) (norm_levelPart_le hd hf l)
              (norm_nonneg _) (by positivity)
        _ = (2 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖ := by
            rw [← mul_assoc, ← mul_pow, ← hexp2_eq]
  have hd_succ_le : (d + 1 : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast (show d + 1 ≤ 2 ^ d from Nat.lt_two_pow_self)
  calc
    (∑ S : Finset ι, |fourierCoeff f S| ^ p) ^ (1 / p)
        ≤ ∑ l ∈ Finset.range (d + 1), a l := hsum_levels
    _ ≤ ∑ _l ∈ Finset.range (d + 1), (2 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖ :=
        Finset.sum_le_sum hterm
    _ = ((d + 1 : ℕ) : ℝ) * ((2 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ d * ((2 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖) := by
        rw [Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_right hd_succ_le (by positivity)
    _ = (4 * Real.exp 2 * Real.sqrt 2) ^ d * ‖f‖ := by
        rw [← mul_assoc, ← mul_pow]; congr 2; ring

-- Non-vacuity witness on two-variable degree-1 Boolean functions.
example :
    let f : (Fin 2 → Bool) → ℝ := fun x ↦ signVal (x 0)
    f ∈ lowDegree ℝ (Fin 2) 1 ∧
      (∑ S : Finset (Fin 2), |fourierCoeff f S| ^ bhExponent 1) ^ (1 / bhExponent 1) ≤
        (4 * Real.exp 2 * Real.sqrt 2) ^ 1 * ‖f‖ := by
  intro f
  have hf : f ∈ lowDegree ℝ (Fin 2) 1 := by
    have hchi : f = chi ℝ ({0} : Finset (Fin 2)) := funext fun x ↦ (chi_singleton _ _).symm
    rw [hchi]
    simpa using chi_mem_lowDegree (F := ℝ) ({0} : Finset (Fin 2))
  exact ⟨hf, sum_rpow_fourierCoeff_le_exp le_rfl hf⟩

end CslibFrontier.BooleanAnalysis

end
