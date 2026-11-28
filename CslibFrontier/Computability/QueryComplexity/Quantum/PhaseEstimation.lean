module

public import CslibFrontier.Computability.QueryComplexity.Quantum.UnknownSearch
public import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum

/-!
# Grover Phase Estimation and Fejér-Kernel Concentration

This module constructs Grover phase estimation (`groverQPE`) on top of controlled random Grover
search (`Cslib.Quantum.randomGrover`) by applying the inverse quantum Fourier transform on the
`Fin M` iteration-count clock register after `M - 1` oracle queries.

## Main definitions

* `CslibFrontier.Computability.QueryComplexity.Quantum.groverQPE`: `M - 1`-query quantum phase
  estimation algorithm applying the inverse quantum Fourier transform to the clock register of
  `randomGrover N M`.
* `CslibFrontier.Computability.QueryComplexity.Quantum.fejerSum`: geometric Fejér-kernel sum
  `∑_{j < M} exp(2 i j (φ - π y / M))`.
* `CslibFrontier.Computability.QueryComplexity.Quantum.goodClock`: set of clock outcomes `y : Fin M`
  whose implied weight estimate `N sin²(π y / M)` lies within
  `2 (d π / M) √(t (N - t)) + N (d π / M)²` of the Hamming weight `t`.

## Main results

* `CslibFrontier.Computability.QueryComplexity.Quantum.clockProb_groverQPE`: exact Fejér-kernel
  formula `(‖fejerSum M θ y‖² + ‖fejerSum M (-θ) y‖²) / (2 M²)` for measuring clock outcome `y`,
  valid uniformly for all Hamming weights `0 ≤ weight x ≤ N`.
* `CslibFrontier.Computability.QueryComplexity.Quantum.norm_fejerSum_mul_abs_sin_le_one`: pointwise
  geometric-series bound `‖fejerSum M φ y‖ * |sin(φ - π y / M)| ≤ 1`.
* `CslibFrontier.Computability.QueryComplexity.Quantum.groverQPE_good_prob_ge`: for every `d ≥ 3`,
  `groverQPE N M` outputs a clock value in `goodClock N M d (weight x)` with probability at least
  `1 - 1 / (2 (d - 2))`.
-/

public section

open Cslib Cslib.BitString Cslib.Quantum Finset Real

namespace CslibFrontier.Computability.QueryComplexity.Quantum

/-- Discrete Parseval identity for the inverse discrete Fourier transform on `Fin M`. -/
private theorem dft_parseval {M : ℕ} (hM : 0 < M) (a : Fin M → ℂ) :
    ∑ y : Fin M,
      ‖(((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
        ∑ j : Fin M,
          Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) * a j‖ ^ 2 =
      ∑ j : Fin M, ‖a j‖ ^ 2 := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hscale :
      ∀ y : Fin M,
        ‖(((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
          ∑ j : Fin M,
            Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) * a j‖ ^ 2 =
        (M : ℝ)⁻¹ *
          ‖∑ j : Fin M,
            Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) * a j‖ ^ 2 := by
    intro y
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hMpos.le]
  simp_rw [hscale, ← mul_sum]
  rw [inv_mul_eq_iff_eq_mul₀ hMpos.ne']
  apply Complex.ofReal_injective
  have hnormC : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp_rw [hnormC]
  let ω : Fin M → Fin M → ℂ := fun j y =>
    Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I)
  have hLHS :
      ∑ y : Fin M, (∑ j : Fin M, ω j y * a j) * starRingEnd ℂ (∑ k : Fin M, ω k y * a k) =
        ∑ j : Fin M, ∑ k : Fin M,
          a j * starRingEnd ℂ (a k) * ∑ y : Fin M, ω j y * starRingEnd ℂ (ω k y) := by
    trans ∑ y : Fin M, ∑ j : Fin M, ∑ k : Fin M,
        a j * starRingEnd ℂ (a k) * (ω j y * starRingEnd ℂ (ω k y))
    · refine sum_congr rfl fun y _ => ?_
      rw [map_sum, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      rw [map_mul]
      ring
    · rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
  rw [hLHS]
  have horth : ∀ j k : Fin M,
      ∑ y : Fin M, ω j y * starRingEnd ℂ (ω k y) = if j = k then (M : ℂ) else 0 := by
    intro j k
    let r : ℂ := Complex.exp ((2 * Real.pi * (((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) / M) * Complex.I)
    have hterm : ∀ y : Fin M, ω j y * starRingEnd ℂ (ω k y) = r ^ y.1 := by
      intro y
      simp only [ω, r, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, map_div₀,
        Complex.conj_ofReal, map_ofNat, map_natCast, ← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      have hMne' : (M : ℂ) ≠ 0 := hMne
      push_cast
      field_simp [hMne']
      ring
    simp_rw [hterm]
    by_cases hjk : j = k
    · subst hjk
      have hr1 : r = 1 := by simp [r]
      simp [hr1]
    · have hrM : r ^ M = 1 := by
        rw [← Complex.exp_nat_mul]
        have harg :
            (M : ℂ) * (2 * Real.pi * (((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) / M * Complex.I) =
              (((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) * (2 * Real.pi * Complex.I) := by
          field_simp [hMne]
        rw [harg, ← Int.cast_sub]
        exact Complex.exp_int_mul_two_pi_mul_I ((k.1 : ℤ) - (j.1 : ℤ))
      have hr1 : r ≠ 1 := by
        intro hr
        rw [Complex.exp_eq_one_iff] at hr
        obtain ⟨n, hn⟩ := hr
        have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have h1 : (((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) / M = (n : ℂ) := by
          apply mul_right_cancel₀ h2pi
          have hrew :
              2 * (Real.pi : ℂ) * (((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) / (M : ℂ) * Complex.I =
                ((((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) / M) * (2 * Real.pi * Complex.I) := by
            ring
          linear_combination hn - hrew
        have h2 : (((k.1 : ℤ) - (j.1 : ℤ)) : ℂ) = (n : ℂ) * (M : ℂ) := by
          rwa [div_eq_iff hMne] at h1
        have h3 : (k.1 : ℤ) - (j.1 : ℤ) = n * (M : ℤ) := by exact_mod_cast h2
        have hlt1 : -(M : ℤ) < (k.1 : ℤ) - (j.1 : ℤ) := by omega
        have hlt2 : (k.1 : ℤ) - (j.1 : ℤ) < (M : ℤ) := by omega
        have hne0 : (k.1 : ℤ) - (j.1 : ℤ) ≠ 0 := fun h0 => hjk (Fin.ext (by omega))
        rcases eq_or_ne n 0 with rfl | hn0
        · omega
        · have hMposZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
          have habs : (M : ℤ) ≤ |(k.1 : ℤ) - (j.1 : ℤ)| := by
            rw [h3, abs_mul, abs_of_pos hMposZ]
            have h1n : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
            nlinarith
          have hltabs : |(k.1 : ℤ) - (j.1 : ℤ)| < (M : ℤ) := abs_lt.2 ⟨hlt1, hlt2⟩
          omega
      rw [Fin.sum_univ_eq_sum_range (fun y => r ^ y), geom_sum_eq hr1, hrM, sub_self, zero_div]
      simp [hjk]
  simp_rw [horth]
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The inverse quantum Fourier transform acting on the `Fin M` clock register of
`State N (Unit × Fin M)`. -/
private noncomputable def qftInv {N : ℕ} (M : ℕ) (hM : 0 < M) :
    State N (Unit × Fin M) →ₗᵢ[ℂ] State N (Unit × Fin M) where
  toFun ψ := WithLp.toLp 2 fun (i, b, u, y) =>
    (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
      ∑ j : Fin M,
        Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) *
          ψ.ofLp (i, b, u, j)
  map_add' ψ φ := by
    ext ⟨i, b, u, y⟩
    simp only [PiLp.add_apply, ← mul_add, ← sum_add_distrib]
  map_smul' r ψ := by
    ext ⟨i, b, u, y⟩
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  norm_map' ψ := by
    have hsq :
        ‖(WithLp.toLp 2 fun (i, b, u, y) =>
          (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
            ∑ j : Fin M,
              Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) *
                ψ.ofLp (i, b, u, j) : State N (Unit × Fin M))‖ ^ 2 = ‖ψ‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine sum_congr rfl fun b _ => ?_
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine sum_congr rfl fun u _ => dft_parseval hM (fun j => ψ.ofLp (i, b, u, j))
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Grover phase estimation (`groverQPE N M hM`): runs `randomGrover N M` for `M - 1` queries
and applies the inverse quantum Fourier transform on the `Fin M` clock register at the final
step. -/
public noncomputable def groverQPE (N M : ℕ) (hM : 0 < M) :
    ℕ → State N (Unit × Fin M) →ₗᵢ[ℂ] State N (Unit × Fin M) :=
  fun s =>
    if s = M - 1 then (qftInv M hM).comp (randomGrover N M (M - 1))
    else randomGrover N M s

/-- After `M - 1` queries, `groverQPE` equals `qftInv M hM` applied to `randomGrover N M`. -/
private theorem run_groverQPE (N M : ℕ) (hM : 0 < M) (x : BitString N) :
    run (groverQPE N M hM) (randomGroverInit N M) x (M - 1) =
      qftInv M hM (run (randomGrover N M) (randomGroverInit N M) x (M - 1)) := by
  by_cases hM1 : M = 1
  · subst hM1
    simp only [Nat.sub_self, run, groverQPE, ↓reduceIte, LinearIsometry.coe_comp,
      Function.comp_apply]
  · have hpos : 0 < M - 1 := by omega
    have hsucc : M - 1 = (M - 2) + 1 := by omega
    conv_lhs => rw [hsucc]
    conv_rhs => rw [hsucc]
    rw [run, run, run_congr (U' := randomGrover N M)
      (fun s hs => by simp [groverQPE, show s ≠ M - 1 by omega])]
    simp [groverQPE, ← hsucc]

/-- The Fejér-kernel geometric sum `∑_{j < M} exp(2 i j (φ - π y / M))`. -/
@[expose] public noncomputable def fejerSum (M : ℕ) (φ : ℝ) (y : Fin M) : ℂ :=
  ∑ j : Fin M, Complex.exp ((2 * (j.1 : ℝ) * (φ - Real.pi * (y.1 : ℝ) / M)) * Complex.I)

/-- Exact clock probability of Grover phase estimation: for every `N > 0`, `M > 0`, input `x`,
and clock outcome `y : Fin M`, the probability of measuring `y` is
`(‖fejerSum M θ y‖^2 + ‖fejerSum M (-θ) y‖^2) / (2 M^2)` where `θ = searchAngle N (weight x)`. -/
public theorem clockProb_groverQPE {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (x : BitString N)
    (y : Fin M) :
    measureProb (run (groverQPE N M hM) (randomGroverInit N M) x (M - 1))
        (univ.filter fun p => p.2.2.2 = y) =
      (1 / (2 * (M : ℝ) ^ 2)) *
        (‖fejerSum M (searchAngle N (weight x)) y‖ ^ 2 +
          ‖fejerSum M (-searchAngle N (weight x)) y‖ ^ 2) := by
  classical
  rw [run_groverQPE]
  set ψ := run (randomGrover N M) (randomGroverInit N M) x (M - 1)
  set t := weight x
  set θ := searchAngle N t
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hinv_sq : (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) = ((M : ℝ)⁻¹ : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hMpos.le, Complex.ofReal_inv]
  have hamp_true : ∀ i : Fin N, (qftInv M hM ψ).ofLp (i, true, (), y) = 0 := fun i => by
    simp only [qftInv, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
    rw [sum_eq_zero (fun j _ => by rw [run_randomGrover_ctrl hN (by omega) x i ((), j), mul_zero]),
      mul_zero]
  let A : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * fejerSum M θ y
  let B : ℂ := Complex.exp (-(θ : ℂ) * Complex.I) * fejerSum M (-θ) y
  have hsum_sin :
      (∑ j : Fin M,
        Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) *
          (Real.sin ((2 * (j.1 : ℝ) + 1) * θ) : ℂ)) = (A - B) / (2 * Complex.I) := by
    rw [eq_div_iff (by simp [Complex.I_ne_zero]), sum_mul]
    simp only [A, B, fejerSum, mul_sub, mul_sum]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_sin, Complex.sin]
    have halg : ∀ u e1 e2 : ℂ,
        u * ((e2 - e1) * Complex.I / 2) * (2 * Complex.I) = u * e1 - u * e2 := fun u e1 e2 => by
      calc u * ((e2 - e1) * Complex.I / 2) * (2 * Complex.I)
          = u * (e2 - e1) * (Complex.I * Complex.I) := by ring
        _ = u * e1 - u * e2 := by rw [Complex.I_mul_I]; ring
    rw [halg]
    simp only [← Complex.exp_add]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  have hsum_cos :
      (∑ j : Fin M,
        Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) *
          (Real.cos ((2 * (j.1 : ℝ) + 1) * θ) : ℂ)) = (A + B) / 2 := by
    rw [eq_div_iff (two_ne_zero : (2 : ℂ) ≠ 0), sum_mul]
    simp only [A, B, fejerSum, mul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_cos, Complex.cos]
    have halg : ∀ u e1 e2 : ℂ, u * ((e1 + e2) / 2) * 2 = u * e1 + u * e2 :=
      fun u e1 e2 => by ring
    rw [halg]
    simp only [← Complex.exp_add]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  have hamp_false : ∀ i : Fin N,
      (qftInv M hM ψ).ofLp (i, false, (), y) =
        if x i then ((M : ℝ)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * ((A - B) / (2 * Complex.I))
        else ((M : ℝ)⁻¹ : ℂ) * (((Real.sqrt (N - t))⁻¹ : ℝ) : ℂ) * ((A + B) / 2) := by
    intro i
    simp only [qftInv, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
    have hslice_val : ∀ j : Fin M,
        ψ.ofLp (i, false, (), j) =
          (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
            (if x i then ((Real.sin ((2 * (j.1 : ℝ) + 1) * θ) / Real.sqrt t : ℝ) : ℂ)
             else ((Real.cos ((2 * (j.1 : ℝ) + 1) * θ) / Real.sqrt (N - t) : ℝ) : ℂ)) := by
      intro j
      have hs := congrArg (fun φ => φ.ofLp (i, false, ()))
        (slice_run_randomGrover hN (m := M) (T := M - 1) (by omega) x j)
      cases hxi : x i <;>
        simpa only [slice_apply, PiLp.smul_apply, flipCtrl_apply, smul_eq_mul, Bool.not_false,
          run_grover_of_weight hN, groverControl_mk, hxi, Bool.false_eq_true, ↓reduceIte] using hs
    simp_rw [hslice_val]
    by_cases hxi : x i
    · simp only [hxi, ↓reduceIte]
      trans (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
            ∑ j : Fin M,
              Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) *
                (Real.sin ((2 * (j.1 : ℝ) + 1) * θ) : ℂ)
      · rw [mul_sum, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [div_eq_mul_inv, Complex.ofReal_mul]
        ring
      · rw [hinv_sq, hsum_sin]
    · simp only [hxi, Bool.false_eq_true, ↓reduceIte]
      trans (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (N - t))⁻¹ : ℝ) : ℂ) *
            ∑ j : Fin M,
              Complex.exp (-(2 * Real.pi * ((j.1 : ℝ) * (y.1 : ℝ) / M)) * Complex.I) *
                (Real.cos ((2 * (j.1 : ℝ) + 1) * θ) : ℂ)
      · rw [mul_sum, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [div_eq_mul_inv, Complex.ofReal_mul]
        ring
      · rw [hinv_sq, hsum_cos]
  have hmeas :
      measureProb (qftInv M hM ψ) (univ.filter fun p => p.2.2.2 = y) =
        ∑ i : Fin N, ‖(qftInv M hM ψ).ofLp (i, false, (), y)‖ ^ 2 := by
    rw [measureProb, sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_prod_type, Fintype.univ_unit,
      sum_singleton, Fintype.sum_prod_type, Fintype.univ_unit, sum_singleton]
    simp [hamp_true]
  rw [hmeas]
  simp_rw [hamp_false]
  have hsplit :
      (∑ i : Fin N,
        ‖if x i then ((M : ℝ)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * ((A - B) / (2 * Complex.I))
         else ((M : ℝ)⁻¹ : ℂ) * (((Real.sqrt (N - t))⁻¹ : ℝ) : ℂ) * ((A + B) / 2)‖ ^ 2) =
      (t : ℝ) * ((M : ℝ) ^ 2)⁻¹ * ((t : ℝ)⁻¹ * (‖A - B‖ ^ 2 / 4)) +
      ((N - t : ℕ) : ℝ) * ((M : ℝ) ^ 2)⁻¹ * (((N : ℝ) - t)⁻¹ * (‖A + B‖ ^ 2 / 4)) := by
    have hterm_ite : ∀ i : Fin N,
        ‖if x i then ((M : ℝ)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * ((A - B) / (2 * Complex.I))
         else ((M : ℝ)⁻¹ : ℂ) * (((Real.sqrt (N - t))⁻¹ : ℝ) : ℂ) * ((A + B) / 2)‖ ^ 2 =
        if x i then ((M : ℝ) ^ 2)⁻¹ * ((t : ℝ)⁻¹ * (‖A - B‖ ^ 2 / 4))
        else ((M : ℝ) ^ 2)⁻¹ * (((N : ℝ) - t)⁻¹ * (‖A + B‖ ^ 2 / 4)) := by
      intro i
      have htN : (0 : ℝ) ≤ (N : ℝ) - t :=
        sub_nonneg.2 (Nat.cast_le.2 (weight_le_length x))
      split_ifs
      · simp only [norm_mul, norm_div, mul_pow, div_pow, Complex.norm_real, Real.norm_eq_abs,
          sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg t), Complex.norm_I, mul_one,
          Complex.norm_ofNat]
        norm_num
        ring
      · simp only [norm_mul, norm_div, mul_pow, div_pow, Complex.norm_real, Real.norm_eq_abs,
          sq_abs, inv_pow, Real.sq_sqrt htN, Complex.norm_ofNat]
        norm_num
        ring
    simp_rw [hterm_ite]
    rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hcardT : #(univ.filter fun i : Fin N => x i = true) = t := rfl
    have hcardF : #(univ.filter fun i : Fin N => ¬x i = true) = N - t := by
      simpa [Fintype.card_fin] using card_filter_eq_false_eq_card_sub_weight x
    rw [hcardT, hcardF]
    ring
  rw [hsplit]
  have hnormA : ‖A‖ ^ 2 = ‖fejerSum M θ y‖ ^ 2 := by
    simp only [A, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnormB : ‖B‖ ^ 2 = ‖fejerSum M (-θ) y‖ ^ 2 := by
    simp only [B, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hpar : ‖A - B‖ ^ 2 + ‖A + B‖ ^ 2 = 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_add]
    ring
  have ht_le : t ≤ N := weight_le_length x
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · have hθ0 : θ = 0 := by simp [θ, ht0, searchAngle_zero]
    have hAB : A = B := by simp [A, B, hθ0]
    have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    simp only [ht0, Nat.sub_zero, Nat.cast_zero, zero_mul, zero_add, sub_zero]
    rw [hAB]
    have h2B : ‖B + B‖ ^ 2 = 4 * ‖B‖ ^ 2 := by
      rw [show B + B = (2 : ℂ) * B by ring, norm_mul, mul_pow, Complex.norm_ofNat]
      norm_num
    rw [h2B, hnormB, hθ0, neg_zero]
    field_simp [hMne, hNpos]
    ring
  · rcases lt_or_eq_of_le ht_le with htlt | htN
    · have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 htpos.ne'
      have hNtR : (N : ℝ) - t ≠ 0 := sub_ne_zero.2 (by exact_mod_cast htlt.ne')
      rw [Nat.cast_sub ht_le]
      have h1 : (t : ℝ) * ((M : ℝ) ^ 2)⁻¹ * ((t : ℝ)⁻¹ * (‖A - B‖ ^ 2 / 4)) =
          ((M : ℝ) ^ 2)⁻¹ * (‖A - B‖ ^ 2 / 4) := by field_simp [htR]
      have h2 : ((N : ℝ) - t) * ((M : ℝ) ^ 2)⁻¹ * (((N : ℝ) - t)⁻¹ * (‖A + B‖ ^ 2 / 4)) =
          ((M : ℝ) ^ 2)⁻¹ * (‖A + B‖ ^ 2 / 4) := by field_simp [hNtR]
      rw [h1, h2, ← mul_add, ← add_div, hpar, hnormA, hnormB]
      ring
    · have hθpi : θ = Real.pi / 2 := by simp [θ, htN, searchAngle_self hN]
      have hfejer_eq : fejerSum M θ y = fejerSum M (-θ) y := by
        simp only [fejerSum, hθpi]
        refine sum_congr rfl fun j _ => ?_
        have harg :
            (2 * ((j.1 : ℝ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) -
              Real.pi * ((y.1 : ℝ) : ℂ) / M)) * Complex.I =
              (2 * ((j.1 : ℝ) : ℂ) * (((-(Real.pi / 2) : ℝ) : ℂ) -
                Real.pi * ((y.1 : ℝ) : ℂ) / M)) *
                Complex.I + ((j.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          push_cast; ring
        rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have hAB : B = -A := by
        dsimp only [A, B]
        rw [← hfejer_eq, hθpi]
        have h1 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by simp
        have h2 : Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
          rw [show -((Real.pi / 2 : ℝ) : ℂ) * Complex.I =
            -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) by ring,
            Complex.exp_neg, h1, Complex.inv_I]
        rw [h1, h2]
        ring
      have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      simp only [htN, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      rw [hAB, sub_neg_eq_add]
      have h2A : ‖A + A‖ ^ 2 = 4 * ‖A‖ ^ 2 := by
        rw [show A + A = (2 : ℂ) * A by ring, norm_mul, mul_pow, Complex.norm_ofNat]
        norm_num
      rw [h2A, hnormA, hfejer_eq]
      field_simp [hMne, hNpos]
      ring

/-- Pointwise geometric-sum bound `‖fejerSum M φ y‖ * |sin (φ - π y / M)| ≤ 1`. -/
public theorem norm_fejerSum_mul_abs_sin_le_one (M : ℕ) (φ : ℝ) (y : Fin M) :
    ‖fejerSum M φ y‖ * |Real.sin (φ - Real.pi * (y.1 : ℝ) / M)| ≤ 1 := by
  set δ := φ - Real.pi * (y.1 : ℝ) / M
  set r : ℂ := Complex.exp ((2 * δ : ℝ) * Complex.I)
  have hfejer : fejerSum M φ y = ∑ j ∈ range M, r ^ j := by
    rw [fejerSum, Fin.sum_univ_eq_sum_range
      (fun j => Complex.exp
        ((2 * ((j : ℝ) : ℂ) * ((φ : ℂ) - Real.pi * ((y.1 : ℝ) : ℂ) / M)) * Complex.I))]
    refine sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [δ]
    push_cast
    ring
  rw [hfejer]
  by_cases hr1 : r = 1
  · rw [Complex.exp_eq_one_iff] at hr1
    obtain ⟨k, hk⟩ := hr1
    have hδC : (δ : ℂ) = (k : ℂ) * (Real.pi : ℂ) := by
      apply mul_right_cancel₀ (show (2 * Complex.I : ℂ) ≠ 0 by simp [Complex.I_ne_zero])
      have h1 : ((2 * δ : ℝ) : ℂ) * Complex.I = (δ : ℂ) * (2 * Complex.I) := by push_cast; ring
      have h2 : (k : ℂ) * (2 * Real.pi * Complex.I) =
          (k : ℂ) * (Real.pi : ℂ) * (2 * Complex.I) := by ring
      linear_combination -h1 + hk + h2
    have hδ : δ = (k : ℝ) * Real.pi := by exact_mod_cast hδC
    rw [hδ, Real.sin_int_mul_pi, abs_zero, mul_zero]
    exact zero_le_one
  · rw [geom_sum_eq hr1]
    have hnorm_sub : ‖r - 1‖ = 2 * |Real.sin δ| := by
      have hfac : r - 1 = Complex.exp ((δ : ℂ) * Complex.I) *
          (2 * Complex.I * (Real.sin δ : ℂ)) := by
        rw [Complex.ofReal_sin, Complex.sin]
        have halg : ∀ u e1 e2 : ℂ,
            u * (2 * Complex.I * ((e2 - e1) * Complex.I / 2)) = u * e1 - u * e2 := fun u e1 e2 => by
          calc u * (2 * Complex.I * ((e2 - e1) * Complex.I / 2))
              = u * (e2 - e1) * (Complex.I * Complex.I) := by ring
            _ = u * e1 - u * e2 := by rw [Complex.I_mul_I]; ring
        rw [halg, ← Complex.exp_add, ← Complex.exp_add]
        simp only [r]
        congr 1
        · congr 1; push_cast; ring
        · have hzero : (δ : ℂ) * Complex.I + -(δ : ℂ) * Complex.I = 0 := by ring
          rw [hzero, Complex.exp_zero]
      rw [hfac, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hsin_pos : 0 < |Real.sin δ| := by
      have : 0 < ‖r - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hr1)
      linarith
    rw [norm_div, hnorm_sub]
    have hnum : ‖r ^ M - 1‖ ≤ 2 := by
      calc ‖r ^ M - 1‖ ≤ ‖r ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by
          rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, norm_one]
        _ = 2 := by norm_num
    have hcancel : ‖r ^ M - 1‖ / (2 * |Real.sin δ|) * |Real.sin δ| = ‖r ^ M - 1‖ / 2 := by
      field_simp [hsin_pos.ne']
    rw [hcancel]
    linarith

/-- Telescoping inverse-square bound: for `2 ≤ a`, `∑ k ∈ Ico a b, (k : ℝ)⁻² ≤ (a - 1)⁻¹`. -/
private theorem sum_inv_sq_Ico_le {a b : ℕ} (ha : 2 ≤ a) :
    ∑ k ∈ Ico a b, ((k : ℝ) ^ 2)⁻¹ ≤ ((a - 1 : ℕ) : ℝ)⁻¹ := by
  rcases le_or_gt b a with hba | hab
  · rw [Ico_eq_empty_of_le hba, sum_empty]
    positivity
  · calc ∑ k ∈ Ico a b, ((k : ℝ) ^ 2)⁻¹
        ≤ ∑ k ∈ Ico a b, ((((k - 1 : ℕ) : ℝ))⁻¹ - ((k : ℝ))⁻¹) := by
          refine sum_le_sum fun k hk => ?_
          have hk2 : 2 ≤ k := le_trans ha (mem_Ico.1 hk).1
          have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
          have hkm1 : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
          have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          rw [inv_eq_one_div, inv_sub_inv hkm1.ne' hkpos.ne',
            div_le_div_iff₀ (by positivity) (by positivity), hcast]
          nlinarith
      _ = (((a - 1 : ℕ) : ℝ))⁻¹ - (((b - 1 : ℕ) : ℝ))⁻¹ := by
          have hstep : ∀ n, a ≤ n →
              ∑ k ∈ Ico a n, ((((k - 1 : ℕ) : ℝ))⁻¹ - ((k : ℝ))⁻¹) =
                (((a - 1 : ℕ) : ℝ))⁻¹ - (((n - 1 : ℕ) : ℝ))⁻¹ := by
            intro n hn
            induction n, hn using Nat.le_induction with
            | base => simp
            | succ m hm ih =>
              rw [sum_Ico_succ_top hm, ih]
              simp only [Nat.add_sub_cancel]
              ring
          exact hstep b (le_of_lt hab)
      _ ≤ ((a - 1 : ℕ) : ℝ)⁻¹ := by
          have : (0 : ℝ) ≤ (((b - 1 : ℕ) : ℝ))⁻¹ := by positivity
          linarith

/-- Periodicity of `|sin|` modulo integer multiples of `π`. -/
private theorem abs_sin_add_int_mul_pi (x : ℝ) (k : ℤ) :
    |Real.sin (x + (k : ℝ) * Real.pi)| = |Real.sin x| := by
  have hs0 : Real.sin ((k : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi k
  have hc1 : |Real.cos ((k : ℝ) * Real.pi)| = 1 := by
    have hsq : Real.cos ((k : ℝ) * Real.pi) ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi), hs0]
    have habs : |Real.cos ((k : ℝ) * Real.pi)| ^ 2 = 1 ^ 2 := by rw [sq_abs, hsq, one_pow]
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp habs
  rw [Real.sin_add, hs0, mul_zero, add_zero, abs_mul, hc1, mul_one]

/-- Clock outcomes `y : Fin M` whose phase `π y / M` is at least `d π / M` away from `φ (mod π)`. -/
private noncomputable def badClock (M : ℕ) (φ : ℝ) (d : ℕ) : Finset (Fin M) :=
  @Finset.filter (Fin M)
    (fun y => ∀ k : ℤ, (d : ℝ) * Real.pi / M ≤ |φ - Real.pi * (y.1 : ℝ) / M - k * Real.pi|)
    (fun _ => Classical.propDecidable _) univ

/-- Fejér-kernel tail bound: for `M > 0` and `d ≥ 3`,
`∑_{y ∈ badClock M φ d} ‖fejerSum M φ y‖^2 / M^2 ≤ 1 / (2 (d - 2))`. -/
private theorem sum_norm_sq_fejerSum_bad_le {M d : ℕ} (hM : 0 < M) (hd : 3 ≤ d) (φ : ℝ) :
    ∑ y ∈ badClock M φ d, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2 ≤
      1 / (2 * ((d - 2 : ℕ) : ℝ)) := by
  classical
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  set m₀ : ℤ := ⌊(M : ℝ) * φ / Real.pi⌋
  set α : ℝ := (M : ℝ) * φ / Real.pi - (m₀ : ℝ)
  have hα0 : 0 ≤ α := Int.fract_nonneg _
  have hα1 : α < 1 := Int.fract_lt_one _
  let rVal (y : Fin M) : ℕ := ((m₀ - (y.1 : ℤ)) % (M : ℤ)).toNat
  have hrVal_lt : ∀ y : Fin M, rVal y < M := fun y => by
    have h1 : 0 ≤ (m₀ - (y.1 : ℤ)) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
    have h2 : (m₀ - (y.1 : ℤ)) % (M : ℤ) < (M : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hM)
    exact (Int.toNat_lt h1).2 h2
  let rIdx (y : Fin M) : Fin M := ⟨rVal y, hrVal_lt y⟩
  have hrIdx_inj : Function.Injective rIdx := fun y₁ y₂ h => by
    have hv : rVal y₁ = rVal y₂ := congrArg Fin.val h
    have hmod : (m₀ - (y₁.1 : ℤ)) % (M : ℤ) = (m₀ - (y₂.1 : ℤ)) % (M : ℤ) := by
      have h1 : 0 ≤ (m₀ - (y₁.1 : ℤ)) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
      have h2 : 0 ≤ (m₀ - (y₂.1 : ℤ)) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
      exact (Int.toNat_of_nonneg h1).symm.trans
        ((congrArg Nat.cast hv).trans (Int.toNat_of_nonneg h2))
    have hdvd : (M : ℤ) ∣ (y₂.1 : ℤ) - (y₁.1 : ℤ) := by
      have := Int.emod_eq_emod_iff_emod_sub_eq_zero.1 hmod
      have hsub : m₀ - (y₁.1 : ℤ) - (m₀ - (y₂.1 : ℤ)) = (y₂.1 : ℤ) - (y₁.1 : ℤ) := by ring
      rw [hsub] at this
      exact Int.dvd_of_emod_eq_zero this
    have hlt1 : -(M : ℤ) < (y₂.1 : ℤ) - (y₁.1 : ℤ) := by omega
    have hlt2 : (y₂.1 : ℤ) - (y₁.1 : ℤ) < (M : ℤ) := by omega
    obtain ⟨c, hc⟩ := hdvd
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Fin.ext (by omega)
    · have habs : (M : ℤ) ≤ |(y₂.1 : ℤ) - (y₁.1 : ℤ)| := by
        rw [hc, abs_mul, abs_of_pos (by exact_mod_cast hM)]
        have : (1 : ℤ) ≤ |c| := Int.one_le_abs hc0
        nlinarith
      have hltabs : |(y₂.1 : ℤ) - (y₁.1 : ℤ)| < (M : ℤ) := abs_lt.2 ⟨hlt1, hlt2⟩
      omega
  have hpoint : ∀ y ∈ badClock M φ d,
      d - 1 ≤ min (rVal y) (M - 1 - rVal y) ∧
        ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2 ≤
          1 / (4 * ((min (rVal y) (M - 1 - rVal y) : ℕ) : ℝ) ^ 2) := by
    intro y hy
    have hbad := (mem_filter.1 hy).2
    let r := rVal y
    have hrM : r < M := hrVal_lt y
    let k₀ : ℤ := (m₀ - (y.1 : ℤ)) / (M : ℤ)
    have hdiv : (m₀ - (y.1 : ℤ) : ℤ) = (r : ℤ) + k₀ * (M : ℤ) := by
      have h1 : 0 ≤ (m₀ - (y.1 : ℤ)) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
      have h2 := Int.emod_add_mul_ediv (m₀ - (y.1 : ℤ)) (M : ℤ)
      have hr_eq : ((r : ℕ) : ℤ) = (m₀ - (y.1 : ℤ)) % (M : ℤ) := Int.toNat_of_nonneg h1
      linarith
    have hδ_eq : ∀ k : ℤ,
        φ - Real.pi * (y.1 : ℝ) / M - (k : ℝ) * Real.pi =
          (((r : ℝ) + α) - ((k - k₀ : ℤ) : ℝ) * (M : ℝ)) * (Real.pi / M) := by
      intro k
      have hdivR : (m₀ : ℝ) - (y.1 : ℝ) = (r : ℝ) + (k₀ : ℝ) * (M : ℝ) := by
        exact_mod_cast hdiv
      have hφ : φ = ((m₀ : ℝ) + α) * (Real.pi / M) := by
        simp only [α]
        field_simp [hMne, Real.pi_ne_zero]
        ring
      rw [hφ]
      push_cast
      have : ((m₀ : ℝ) + α) * (Real.pi / M) - Real.pi * (y.1 : ℝ) / M - (k : ℝ) * Real.pi =
          (((m₀ : ℝ) - (y.1 : ℝ)) + α - (k : ℝ) * (M : ℝ)) * (Real.pi / M) := by
        field_simp [hMne]
        ring
      rw [this, hdivR]
      ring
    have hlo : (d : ℝ) ≤ (r : ℝ) + α := by
      have hb := hbad k₀
      rw [hδ_eq k₀, sub_self, Int.cast_zero, zero_mul, sub_zero, abs_mul,
        abs_of_pos (div_pos Real.pi_pos hMpos), abs_of_nonneg (by positivity)] at hb
      have hpiM : 0 < Real.pi / M := div_pos Real.pi_pos hMpos
      have : (d : ℝ) * (Real.pi / M) ≤ ((r : ℝ) + α) * (Real.pi / M) := by
        simpa [mul_div_assoc] using hb
      exact le_of_mul_le_mul_right this hpiM
    have hhi : (d : ℝ) ≤ (M : ℝ) - ((r : ℝ) + α) := by
      have hb := hbad (k₀ + 1)
      have hsub1 : (k₀ + 1 - k₀ : ℤ) = 1 := by ring
      rw [hδ_eq (k₀ + 1), hsub1, Int.cast_one, one_mul, abs_mul,
        abs_of_pos (div_pos Real.pi_pos hMpos)] at hb
      have hneg : (r : ℝ) + α - (M : ℝ) ≤ 0 := by
        have hr1 : (r : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hrM
        linarith
      rw [abs_of_nonpos hneg] at hb
      have hpiM : 0 < Real.pi / M := div_pos Real.pi_pos hMpos
      have : (d : ℝ) * (Real.pi / M) ≤ ((M : ℝ) - ((r : ℝ) + α)) * (Real.pi / M) := by
        have : -(((r : ℝ) + α) - (M : ℝ)) = (M : ℝ) - ((r : ℝ) + α) := by ring
        rw [← this]
        simpa [mul_div_assoc] using hb
      exact le_of_mul_le_mul_right this hpiM
    have hr_ge : d ≤ r := by
      by_contra hlt
      have : (r : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast (show r + 1 ≤ d by omega)
      linarith
    have hMr_ge : d - 1 ≤ M - 1 - r := by
      have : (r : ℝ) + (d : ℝ) ≤ (M : ℝ) := by linarith
      have : r + d ≤ M := by exact_mod_cast this
      omega
    have hq_ge : d - 1 ≤ min r (M - 1 - r) := le_min (by omega) hMr_ge
    refine ⟨hq_ge, ?_⟩
    set q : ℕ := min r (M - 1 - r)
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hsin_ge : 2 * (q : ℝ) / M ≤ |Real.sin (φ - Real.pi * (y.1 : ℝ) / M)| := by
      by_cases hhalf : (r : ℝ) + α ≤ (M : ℝ) / 2
      · let u := ((r : ℝ) + α) * (Real.pi / M)
        have hu0 : 0 ≤ u := by positivity
        have hupi : u ≤ Real.pi / 2 := by
          have : u ≤ ((M : ℝ) / 2) * (Real.pi / M) :=
            mul_le_mul_of_nonneg_right hhalf (by positivity)
          calc u ≤ ((M : ℝ) / 2) * (Real.pi / M) := this
            _ = Real.pi / 2 := by field_simp [hMne]
        have hsin_eq : |Real.sin (φ - Real.pi * (y.1 : ℝ) / M)| = Real.sin u := by
          have h1 := hδ_eq k₀
          rw [sub_self, Int.cast_zero, zero_mul, sub_zero] at h1
          have h2 : φ - Real.pi * (y.1 : ℝ) / M = u + (k₀ : ℝ) * Real.pi := by linarith
          rw [h2, abs_sin_add_int_mul_pi,
            abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith [Real.pi_pos]))]
        rw [hsin_eq]
        have hJ := Real.mul_le_sin hu0 hupi
        have hqu : (q : ℝ) * (Real.pi / M) ≤ u := by
          have hqr : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast min_le_left r (M - 1 - r)
          have : (q : ℝ) ≤ (r : ℝ) + α := by linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
        calc 2 * (q : ℝ) / M = 2 / Real.pi * ((q : ℝ) * (Real.pi / M)) := by
              field_simp [Real.pi_ne_zero, hMne]
          _ ≤ 2 / Real.pi * u := mul_le_mul_of_nonneg_left hqu (by positivity)
          _ ≤ Real.sin u := hJ
      · push Not at hhalf
        let u := ((M : ℝ) - ((r : ℝ) + α)) * (Real.pi / M)
        have hu0 : 0 ≤ u := by
          have hr1 : (r : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hrM
          have : 0 ≤ (M : ℝ) - ((r : ℝ) + α) := by linarith
          positivity
        have hupi : u ≤ Real.pi / 2 := by
          have : (M : ℝ) - ((r : ℝ) + α) ≤ (M : ℝ) / 2 := by linarith
          calc u ≤ ((M : ℝ) / 2) * (Real.pi / M) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = Real.pi / 2 := by field_simp [hMne]
        have hsin_eq : |Real.sin (φ - Real.pi * (y.1 : ℝ) / M)| = Real.sin u := by
          have h1 := hδ_eq (k₀ + 1)
          have hsub1 : (k₀ + 1 - k₀ : ℤ) = 1 := by ring
          rw [hsub1, Int.cast_one, one_mul] at h1
          have h2 : φ - Real.pi * (y.1 : ℝ) / M = -u + ((k₀ + 1 : ℤ) : ℝ) * Real.pi := by
            dsimp only [u]
            linear_combination h1
          rw [h2, abs_sin_add_int_mul_pi, Real.sin_neg, abs_neg,
            abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith [Real.pi_pos]))]
        rw [hsin_eq]
        have hJ := Real.mul_le_sin hu0 hupi
        have hqu : (q : ℝ) * (Real.pi / M) ≤ u := by
          have hqMr : (q : ℝ) ≤ ((M - 1 - r : ℕ) : ℝ) := by
            exact_mod_cast min_le_right r (M - 1 - r)
          have hcast : ((M - 1 - r : ℕ) : ℝ) = (M : ℝ) - 1 - (r : ℝ) := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
          rw [hcast] at hqMr
          have : (q : ℝ) ≤ (M : ℝ) - ((r : ℝ) + α) := by linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
        calc 2 * (q : ℝ) / M = 2 / Real.pi * ((q : ℝ) * (Real.pi / M)) := by
              field_simp [Real.pi_ne_zero, hMne]
          _ ≤ 2 / Real.pi * u := mul_le_mul_of_nonneg_left hqu (by positivity)
          _ ≤ Real.sin u := hJ
    have hmul1 := norm_fejerSum_mul_abs_sin_le_one M φ y
    have hmul2 : ‖fejerSum M φ y‖ * (2 * (q : ℝ) / M) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hsin_ge (norm_nonneg _)).trans hmul1
    have hnorm_le : ‖fejerSum M φ y‖ / M ≤ 1 / (2 * (q : ℝ)) := by
      rw [div_le_div_iff₀ hMpos (by positivity)]
      have hmul3 := mul_le_mul_of_nonneg_right hmul2 hMpos.le
      have hcancel : ‖fejerSum M φ y‖ * (2 * (q : ℝ) / M) * M =
          ‖fejerSum M φ y‖ * (2 * (q : ℝ)) := by field_simp [hMne]
      linarith
    have hsq := pow_le_pow_left₀ (by positivity) hnorm_le 2
    simpa only [div_pow, one_pow, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq
  let B₁ := (badClock M φ d).filter fun y => rVal y ≤ M - 1 - rVal y
  let B₂ := (badClock M φ d).filter fun y => ¬ (rVal y ≤ M - 1 - rVal y)
  have hsplit_sum :
      ∑ y ∈ badClock M φ d, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2 =
        (∑ y ∈ B₁, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2) +
          (∑ y ∈ B₂, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2) :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit_sum]
  have hB₁ : ∑ y ∈ B₁, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2 ≤
      1 / (4 * ((d - 2 : ℕ) : ℝ)) := by
    calc ∑ y ∈ B₁, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2
        ≤ ∑ y ∈ B₁, 1 / (4 * ((rVal y : ℝ) ^ 2)) := by
          refine sum_le_sum fun y hy => ?_
          have hmem := (mem_filter.1 hy).1
          have hle := (mem_filter.1 hy).2
          have hp := (hpoint y hmem).2
          rwa [min_eq_left hle] at hp
      _ = (1 / 4 : ℝ) * ∑ y ∈ B₁, ((rVal y : ℝ) ^ 2)⁻¹ := by
          rw [mul_sum]; refine sum_congr rfl fun y _ => by ring
      _ ≤ (1 / 4 : ℝ) * ∑ k ∈ Ico (d - 1) M, ((k : ℝ) ^ 2)⁻¹ := by
          gcongr
          have himg_eq : ∑ y ∈ B₁, ((rVal y : ℝ) ^ 2)⁻¹ =
              ∑ k ∈ B₁.image rVal, ((k : ℝ) ^ 2)⁻¹ :=
            (sum_image (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹)
              fun y₁ _ y₂ _ h => hrIdx_inj (Fin.ext h)).symm
          rw [himg_eq]
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro k hk
          obtain ⟨y, hy, rfl⟩ := mem_image.1 hk
          have hmem := (mem_filter.1 hy).1
          have hle := (mem_filter.1 hy).2
          have hq := (hpoint y hmem).1
          rw [min_eq_left hle] at hq
          exact mem_Ico.2 ⟨hq, hrVal_lt y⟩
      _ ≤ (1 / 4 : ℝ) * ((d - 2 : ℕ) : ℝ)⁻¹ := by
          gcongr
          have := sum_inv_sq_Ico_le (a := d - 1) (b := M) (by omega)
          rwa [show d - 1 - 1 = d - 2 by omega] at this
      _ = 1 / (4 * ((d - 2 : ℕ) : ℝ)) := by ring
  have hB₂ : ∑ y ∈ B₂, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2 ≤
      1 / (4 * ((d - 2 : ℕ) : ℝ)) := by
    calc ∑ y ∈ B₂, ‖fejerSum M φ y‖ ^ 2 / (M : ℝ) ^ 2
        ≤ ∑ y ∈ B₂, 1 / (4 * (((M - 1 - rVal y : ℕ) : ℝ) ^ 2)) := by
          refine sum_le_sum fun y hy => ?_
          have hmem := (mem_filter.1 hy).1
          have hgt := (mem_filter.1 hy).2
          have hp := (hpoint y hmem).2
          rwa [min_eq_right (by omega)] at hp
      _ = (1 / 4 : ℝ) * ∑ y ∈ B₂, (((M - 1 - rVal y : ℕ) : ℝ) ^ 2)⁻¹ := by
          rw [mul_sum]; refine sum_congr rfl fun y _ => by ring
      _ ≤ (1 / 4 : ℝ) * ∑ k ∈ Ico (d - 1) M, ((k : ℝ) ^ 2)⁻¹ := by
          gcongr
          have himg_eq : ∑ y ∈ B₂, (((M - 1 - rVal y : ℕ) : ℝ) ^ 2)⁻¹ =
              ∑ k ∈ B₂.image (fun y => M - 1 - rVal y), ((k : ℝ) ^ 2)⁻¹ :=
            (sum_image (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) fun y₁ _ y₂ _ h => by
              change M - 1 - rVal y₁ = M - 1 - rVal y₂ at h
              have h1 : rVal y₁ < M := hrVal_lt y₁
              have h2 : rVal y₂ < M := hrVal_lt y₂
              have hr : rVal y₁ = rVal y₂ := by omega
              exact hrIdx_inj (Fin.ext hr)).symm
          rw [himg_eq]
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro k hk
          obtain ⟨y, hy, rfl⟩ := mem_image.1 hk
          have hmem := (mem_filter.1 hy).1
          have hgt := (mem_filter.1 hy).2
          have hq := (hpoint y hmem).1
          rw [min_eq_right (by omega)] at hq
          exact mem_Ico.2 ⟨hq, by omega⟩
      _ ≤ (1 / 4 : ℝ) * ((d - 2 : ℕ) : ℝ)⁻¹ := by
          gcongr
          have := sum_inv_sq_Ico_le (a := d - 1) (b := M) (by omega)
          rwa [show d - 1 - 1 = d - 2 by omega] at this
      _ = 1 / (4 * ((d - 2 : ℕ) : ℝ)) := by ring
  have hhalf_sum : (1 : ℝ) / (4 * ((d - 2 : ℕ) : ℝ)) + 1 / (4 * ((d - 2 : ℕ) : ℝ)) =
      1 / (2 * ((d - 2 : ℕ) : ℝ)) := by
    simp only [one_div, mul_inv]
    ring
  linarith

/-- Trigonometric error bound: if `|sin (π y / M - θ)| ≤ η` or `|sin (π y / M + θ)| ≤ η`, then
`|N * sin²(π y / M) - t| ≤ 2 * η * √(t * (N - t)) + N * η^2`. -/
private theorem abs_estimate_sub_weight_le {N M t : ℕ} {η : ℝ} (hN : 0 < N) (ht : t ≤ N)
    (hη : 0 ≤ η) (y : Fin M)
    (hsin : |Real.sin (Real.pi * (y.1 : ℝ) / M - searchAngle N t)| ≤ η ∨
      |Real.sin (Real.pi * (y.1 : ℝ) / M + searchAngle N t)| ≤ η) :
    |(N : ℝ) * Real.sin (Real.pi * (y.1 : ℝ) / M) ^ 2 - (t : ℝ)| ≤
      2 * η * Real.sqrt ((t : ℝ) * ((N : ℝ) - t)) + (N : ℝ) * η ^ 2 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set θ := searchAngle N t
  set α := Real.pi * (y.1 : ℝ) / M
  have hsin_sq_θ : Real.sin θ ^ 2 = (t : ℝ) / N := by
    rw [sin_searchAngle ht, Real.sq_sqrt (div_nonneg (Nat.cast_nonneg t) hNpos.le)]
  have hsin_2θ : Real.sin (2 * θ) = 2 * Real.sqrt ((t : ℝ) * ((N : ℝ) - t)) / N := by
    rw [Real.sin_two_mul, sin_searchAngle ht, cos_searchAngle]
    have h1 : 1 - (t : ℝ) / N = ((N : ℝ) - t) / N := by field_simp [hNpos.ne']
    rw [h1, Real.sqrt_div' _ hNpos.le, Real.sqrt_div' _ hNpos.le]
    have h2 : 2 * (Real.sqrt t / Real.sqrt N) * (Real.sqrt ((N : ℝ) - t) / Real.sqrt N) =
        2 * (Real.sqrt t * Real.sqrt ((N : ℝ) - t)) / (Real.sqrt N * Real.sqrt N) := by ring
    rw [h2, ← Real.sqrt_mul (Nat.cast_nonneg t), Real.mul_self_sqrt hNpos.le]
  have hdiff : Real.sin α ^ 2 - Real.sin θ ^ 2 = Real.sin (α - θ) * Real.sin (α + θ) := by
    rw [Real.sin_sub, Real.sin_add]
    have h1 := Real.sin_sq_add_cos_sq α
    have h2 := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hprod : |Real.sin (α - θ) * Real.sin (α + θ)| ≤ η * (Real.sin (2 * θ) + η) := by
    rw [abs_mul]
    rcases hsin with h1 | h2
    · have hother : |Real.sin (α + θ)| ≤ Real.sin (2 * θ) + η := by
        have hadd : α + θ = (α - θ) + 2 * θ := by ring
        rw [hadd, Real.sin_add]
        calc |Real.sin (α - θ) * Real.cos (2 * θ) + Real.cos (α - θ) * Real.sin (2 * θ)|
            ≤ |Real.sin (α - θ) * Real.cos (2 * θ)| + |Real.cos (α - θ) * Real.sin (2 * θ)| :=
              abs_add_le _ _
          _ = |Real.sin (α - θ)| * |Real.cos (2 * θ)| +
            |Real.cos (α - θ)| * |Real.sin (2 * θ)| := by
              rw [abs_mul, abs_mul]
          _ ≤ η * 1 + 1 * Real.sin (2 * θ) := by
              have hsin2_nn : 0 ≤ Real.sin (2 * θ) := by
                rw [hsin_2θ]; positivity
              rw [abs_of_nonneg hsin2_nn]
              gcongr
              · exact Real.abs_cos_le_one _
              · exact Real.abs_cos_le_one _
          _ = Real.sin (2 * θ) + η := by ring
      have hsin2_nn : 0 ≤ Real.sin (2 * θ) := by rw [hsin_2θ]; positivity
      exact mul_le_mul h1 hother (abs_nonneg _) (by linarith)
    · have hother : |Real.sin (α - θ)| ≤ Real.sin (2 * θ) + η := by
        have hsub : α - θ = (α + θ) - 2 * θ := by ring
        rw [hsub, Real.sin_sub]
        calc |Real.sin (α + θ) * Real.cos (2 * θ) - Real.cos (α + θ) * Real.sin (2 * θ)|
            ≤ |Real.sin (α + θ) * Real.cos (2 * θ)| + |Real.cos (α + θ) * Real.sin (2 * θ)| :=
              abs_sub _ _
          _ = |Real.sin (α + θ)| * |Real.cos (2 * θ)| +
            |Real.cos (α + θ)| * |Real.sin (2 * θ)| := by
              rw [abs_mul, abs_mul]
          _ ≤ η * 1 + 1 * Real.sin (2 * θ) := by
              have hsin2_nn : 0 ≤ Real.sin (2 * θ) := by rw [hsin_2θ]; positivity
              rw [abs_of_nonneg hsin2_nn]
              gcongr
              · exact Real.abs_cos_le_one _
              · exact Real.abs_cos_le_one _
          _ = Real.sin (2 * θ) + η := by ring
      have hsin2_nn : 0 ≤ Real.sin (2 * θ) := by rw [hsin_2θ]; positivity
      rw [mul_comm]
      exact mul_le_mul h2 hother (abs_nonneg _) (by linarith)
  have hmain : |(N : ℝ) * Real.sin α ^ 2 - (t : ℝ)| =
      (N : ℝ) * |Real.sin α ^ 2 - Real.sin θ ^ 2| := by
    rw [hsin_sq_θ, show (N : ℝ) * Real.sin α ^ 2 - (t : ℝ) =
      (N : ℝ) * (Real.sin α ^ 2 - (t : ℝ) / N) by field_simp [hNpos.ne'],
      abs_mul, abs_of_pos hNpos]
  rw [hmain, hdiff]
  calc (N : ℝ) * |Real.sin (α - θ) * Real.sin (α + θ)|
      ≤ (N : ℝ) * (η * (Real.sin (2 * θ) + η)) := by gcongr
    _ = 2 * η * Real.sqrt ((t : ℝ) * ((N : ℝ) - t)) + (N : ℝ) * η ^ 2 := by
        rw [hsin_2θ]
        field_simp [hNpos.ne']

/-- Good clock outcomes for `groverQPE N M` at weight `t` and accuracy parameter `d`. -/
@[expose] public noncomputable def goodClock (N M d t : ℕ) : Finset (Fin M) :=
  @Finset.filter (Fin M)
    (fun y => |(N : ℝ) * Real.sin (Real.pi * (y.1 : ℝ) / M) ^ 2 - (t : ℝ)| ≤
      2 * ((d : ℝ) * Real.pi / M) * Real.sqrt ((t : ℝ) * ((N : ℝ) - t)) +
        (N : ℝ) * ((d : ℝ) * Real.pi / M) ^ 2)
    (fun _ => Classical.propDecidable _) univ

/-- Grover phase-estimation concentration: for `N > 0`, `M > 0`, `d ≥ 3`, and any input `x`,
`groverQPE N M` measures a clock outcome in `goodClock N M d (weight x)` with probability at least
`1 - 1 / (2 (d - 2))`. -/
public theorem groverQPE_good_prob_ge {N M d : ℕ} (hN : 0 < N) (hM : 0 < M) (hd : 3 ≤ d)
    (x : BitString N) :
    1 - 1 / (2 * ((d - 2 : ℕ) : ℝ)) ≤
      measureProb (run (groverQPE N M hM) (randomGroverInit N M) x (M - 1))
        (univ.filter fun p => p.2.2.2 ∈ goodClock N M d (weight x)) := by
  classical
  set ψ := run (groverQPE N M hM) (randomGroverInit N M) x (M - 1)
  set θ := searchAngle N (weight x)
  have hnorm : ‖ψ‖ = 1 := by
    rw [norm_run, norm_randomGroverInit hN hM]
  have htot : measureProb ψ univ = 1 := by
    rw [measureProb_univ, hnorm, one_pow]
  let Sgood : Finset (Fin N × Bool × Unit × Fin M) :=
    univ.filter fun p => p.2.2.2 ∈ goodClock N M d (weight x)
  let Sbad : Finset (Fin N × Bool × Unit × Fin M) :=
    univ.filter fun p => p.2.2.2 ∉ goodClock N M d (weight x)
  have hpart : measureProb ψ Sgood + measureProb ψ Sbad = 1 := by
    rw [← htot, measureProb, measureProb, measureProb, sum_filter_add_sum_filter_not]
  have hsub_bad : ∀ y : Fin M, y ∉ goodClock N M d (weight x) →
      y ∈ badClock M θ d ∧ y ∈ badClock M (-θ) d := by
    intro y hy
    have hη : 0 ≤ (d : ℝ) * Real.pi / M := by positivity
    have hnot : ¬(|Real.sin (Real.pi * (y.1 : ℝ) / M - θ)| ≤ (d : ℝ) * Real.pi / M ∨
        |Real.sin (Real.pi * (y.1 : ℝ) / M + θ)| ≤ (d : ℝ) * Real.pi / M) := fun h =>
      hy (mem_filter.2 ⟨mem_univ y, abs_estimate_sub_weight_le hN (weight_le_length x) hη y h⟩)
    rw [not_or] at hnot
    constructor
    · refine mem_filter.2 ⟨mem_univ y, fun k => ?_⟩
      by_contra hlt
      push Not at hlt
      apply hnot.1
      have h1 : |Real.sin (Real.pi * (y.1 : ℝ) / M - θ)| =
          |Real.sin ((θ - Real.pi * (y.1 : ℝ) / M) - (k : ℝ) * Real.pi)| := by
        rw [show Real.pi * (y.1 : ℝ) / M - θ = -(θ - Real.pi * (y.1 : ℝ) / M) by ring,
          Real.sin_neg, abs_neg,
          show (θ - Real.pi * (y.1 : ℝ) / M) - (k : ℝ) * Real.pi =
            (θ - Real.pi * (y.1 : ℝ) / M) + ((-k : ℤ) : ℝ) * Real.pi by push_cast; ring,
          abs_sin_add_int_mul_pi]
      rw [h1]
      exact (Real.abs_sin_le_abs).trans hlt.le
    · refine mem_filter.2 ⟨mem_univ y, fun k => ?_⟩
      by_contra hlt
      push Not at hlt
      apply hnot.2
      have h1 : |Real.sin (Real.pi * (y.1 : ℝ) / M + θ)| =
          |Real.sin ((-θ - Real.pi * (y.1 : ℝ) / M) - (k : ℝ) * Real.pi)| := by
        rw [show Real.pi * (y.1 : ℝ) / M + θ = -(-θ - Real.pi * (y.1 : ℝ) / M) by ring,
          Real.sin_neg, abs_neg,
          show (-θ - Real.pi * (y.1 : ℝ) / M) - (k : ℝ) * Real.pi =
            (-θ - Real.pi * (y.1 : ℝ) / M) + ((-k : ℤ) : ℝ) * Real.pi by push_cast; ring,
          abs_sin_add_int_mul_pi]
      rw [h1]
      exact (Real.abs_sin_le_abs).trans hlt.le
  have hbad_eq :
      measureProb ψ Sbad =
        ∑ y ∈ univ.filter (fun y : Fin M => y ∉ goodClock N M d (weight x)),
          measureProb ψ (univ.filter fun p => p.2.2.2 = y) := by
    rw [measureProb, ← sum_fiberwise_of_maps_to (g :=
      fun p : Fin N × Bool × Unit × Fin M => p.2.2.2)
      (t := univ.filter fun y : Fin M => y ∉ goodClock N M d (weight x))
      (fun p hp => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2⟩)]
    refine sum_congr rfl fun y hy => ?_
    rw [measureProb]
    refine sum_congr (Finset.ext fun p => ?_) fun _ _ => rfl
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨_, hpy⟩ => hpy, fun hpy => ⟨hpy.symm ▸ (mem_filter.1 hy).2, hpy⟩⟩
  have hbad_le : measureProb ψ Sbad ≤ 1 / (2 * ((d - 2 : ℕ) : ℝ)) := by
    rw [hbad_eq]
    dsimp only [ψ]
    simp_rw [clockProb_groverQPE hN hM x]
    rw [show searchAngle N (weight x) = θ from rfl]
    have hsplit :
        (∑ y ∈ univ.filter (fun y : Fin M => y ∉ goodClock N M d (weight x)),
          (1 / (2 * (M : ℝ) ^ 2)) *
            (‖fejerSum M θ y‖ ^ 2 + ‖fejerSum M (-θ) y‖ ^ 2)) =
        (1 / 2 : ℝ) *
          (∑ y ∈ univ.filter (fun y : Fin M => y ∉ goodClock N M d (weight x)),
            ‖fejerSum M θ y‖ ^ 2 / (M : ℝ) ^ 2) +
        (1 / 2 : ℝ) *
          (∑ y ∈ univ.filter (fun y : Fin M => y ∉ goodClock N M d (weight x)),
            ‖fejerSum M (-θ) y‖ ^ 2 / (M : ℝ) ^ 2) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun y _ => by ring
    rw [hsplit]
    have h1 :
        ∑ y ∈ univ.filter (fun y : Fin M => y ∉ goodClock N M d (weight x)),
          ‖fejerSum M θ y‖ ^ 2 / (M : ℝ) ^ 2 ≤ 1 / (2 * ((d - 2 : ℕ) : ℝ)) :=
      (sum_le_sum_of_subset_of_nonneg
        (fun y hy => (hsub_bad y (mem_filter.1 hy).2).1)
        (fun _ _ _ => by positivity)).trans (sum_norm_sq_fejerSum_bad_le hM hd θ)
    have h2 :
        ∑ y ∈ univ.filter (fun y : Fin M => y ∉ goodClock N M d (weight x)),
          ‖fejerSum M (-θ) y‖ ^ 2 / (M : ℝ) ^ 2 ≤ 1 / (2 * ((d - 2 : ℕ) : ℝ)) :=
      (sum_le_sum_of_subset_of_nonneg
        (fun y hy => (hsub_bad y (mem_filter.1 hy).2).2)
        (fun _ _ _ => by positivity)).trans (sum_norm_sq_fejerSum_bad_le hM hd (-θ))
    linarith
  linarith

end CslibFrontier.Computability.QueryComplexity.Quantum
