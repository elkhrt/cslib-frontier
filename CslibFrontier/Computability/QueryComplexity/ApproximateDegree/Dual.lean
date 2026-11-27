/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.Data.BitString.Threshold

import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Approximate Degree Duality, Amplification, and Block Composition

This module develops the dual characterization of sign-valued approximate degree and one-sided
approximate degree on the Boolean cube, constant-error amplification, one-sidedness of
$\mathrm{AND}_m$, and block composition $f \circ g^m$.

## Main definitions

* `CslibFrontier.QueryComplexity.l1Norm`: unnormalized $\ell_1$ norm $\sum_x |\varphi(x)|$.
* `CslibFrontier.QueryComplexity.innerSum`: unnormalized inner product $\sum_x \varphi(x) \psi(x)$.
* `CslibFrontier.QueryComplexity.PureHighDegree`: orthogonality to all real functions of degree at
  most $d$.
* `CslibFrontier.QueryComplexity.signApproxDegree`: $\pm 1$ approximate degree
  $\widetilde{\deg}_\varepsilon(f)$.
* `CslibFrontier.QueryComplexity.IsOneSidedApprox`: one-sided $\varepsilon$-approximation predicate.
* `CslibFrontier.QueryComplexity.oneSidedApproxDegree`: one-sided approximate degree
  $\widetilde{\deg}_\varepsilon^{-}(f)$.
* `CslibFrontier.QueryComplexity.blockComp`: block composition $f \circ g^m$ on `BitString (m * n)`.
* `CslibFrontier.QueryComplexity.signBool`: sign bit of a real number (`decide (t < 0)`).

## Main results

* `CslibFrontier.QueryComplexity.signApproxDegree_eq_approxDegree`: relation to `{0, 1}` approximate
  degree via $\widetilde{\deg}_\varepsilon(f) = \mathrm{adeg}_{\varepsilon/2}(f)$.
* `CslibFrontier.QueryComplexity.lt_signApproxDegree_iff`: LP duality characterization of
  $\widetilde{\deg}_\varepsilon(f) > d$.
* `CslibFrontier.QueryComplexity.lt_oneSidedApproxDegree_iff`: LP duality characterization of
  $\widetilde{\deg}_\varepsilon^{-}(f) > d$.
* `CslibFrontier.QueryComplexity.signApproxDegree_one_third_le_of_large_error`: constant-error
  amplification $\widetilde{\deg}_{1/3}(f) \le 3^{19} \widetilde{\deg}_{99/100}(f)$.
* `CslibFrontier.QueryComplexity.oneSidedApproxDegree_and_eq_signApproxDegree`: one-sidedness is
  without loss of generality for $\mathrm{AND}_m$.
-/

public section

open scoped NNReal BigOperators
open Finset Matrix Cslib Cslib.BitString Cslib.QueryComplexity

namespace CslibFrontier.QueryComplexity

/-! ### Inner product, $\ell_1$ norm, and pure high degree -/

/-- Unnormalized $\ell_1$ norm on the Boolean cube. -/
def l1Norm {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, |φ x|

/-- Unnormalized inner product on the Boolean cube. -/
def innerSum {ι : Type*} [Fintype ι] [DecidableEq ι] (φ ψ : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, φ x * ψ x

/-- A real function on the Boolean cube has pure high degree strictly greater than `d` when it is
orthogonal to every real function of degree at most `d`. -/
def PureHighDegree {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → Bool) → ℝ) (d : ℕ) : Prop :=
  ∀ p ∈ lowDegree ℝ ι d, innerSum φ p = 0

lemma l1Norm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → Bool) → ℝ) :
    l1Norm φ = ∑ x, |φ x| := by rfl

@[simp]
lemma l1Norm_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    l1Norm (fun _ : ι → Bool => (0 : ℝ)) = 0 := by
  simp [l1Norm]

@[simp]
lemma l1Norm_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → Bool) → ℝ) :
    l1Norm (fun x => -φ x) = l1Norm φ := by
  simp [l1Norm]

lemma l1Norm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → Bool) → ℝ) :
    0 ≤ l1Norm φ := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1Norm_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) (φ : (ι → Bool) → ℝ) :
    l1Norm (fun x => c * φ x) = |c| * l1Norm φ := by
  simp only [l1Norm, abs_mul, Finset.mul_sum]

lemma innerSum_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (φ ψ : (ι → Bool) → ℝ) :
    innerSum φ ψ = ∑ x, φ x * ψ x := by rfl

@[simp]
lemma innerSum_zero_left {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : (ι → Bool) → ℝ) :
    innerSum (fun _ => (0 : ℝ)) ψ = 0 := by
  simp [innerSum]

@[simp]
lemma innerSum_zero_right {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → Bool) → ℝ) :
    innerSum φ (fun _ => (0 : ℝ)) = 0 := by
  simp [innerSum]

lemma innerSum_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (φ ψ : (ι → Bool) → ℝ) :
    innerSum φ ψ = innerSum ψ φ := by
  simp only [innerSum, mul_comm]

lemma innerSum_smul_left {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ)
    (φ ψ : (ι → Bool) → ℝ) :
    innerSum (fun x => c * φ x) ψ = c * innerSum φ ψ := by
  simp only [innerSum, mul_assoc, Finset.mul_sum]

lemma innerSum_eq_two_pow_mul_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ ψ : (ι → Bool) → ℝ) :
    innerSum φ ψ = (2 : ℝ) ^ Fintype.card ι * 𝔼 x, φ x * ψ x := by
  rw [innerSum, expect_eq_sum_div_card]
  have hcard : (Fintype.card (ι → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card ι := by
    simp
  rw [Finset.card_univ, hcard]
  have hpos : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  field_simp [hpos]

lemma innerSum_chi_eq_two_pow_mul_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → Bool) → ℝ) (S : Finset ι) :
    innerSum φ (chi ℝ S) = (2 : ℝ) ^ Fintype.card ι * fourierCoeff φ S :=
  innerSum_eq_two_pow_mul_expect φ (chi ℝ S)

lemma pureHighDegree_iff_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → Bool) → ℝ) (d : ℕ) :
    PureHighDegree φ d ↔ ∀ S : Finset ι, #S ≤ d → fourierCoeff φ S = 0 := by
  constructor
  · intro h S hS
    have h0 := h (chi ℝ S) (lowDegree_mono hS (chi_mem_lowDegree S))
    rw [innerSum_chi_eq_two_pow_mul_fourierCoeff] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by positivity)
  · intro h p hp
    have hlow := (mem_lowDegree_iff_fourierCoeff_eq_zero (f := p)).mp hp
    have hexp : innerSum φ p = ∑ x, φ x * (∑ S, fourierCoeff p S * chi ℝ S x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sum_fourierCoeff_mul_chi]
    rw [hexp]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun S _ => ?_
    by_cases hS : #S ≤ d
    · have h1 : ∑ x, φ x * (fourierCoeff p S * chi ℝ S x) =
          fourierCoeff p S * innerSum φ (chi ℝ S) := by
        rw [innerSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [h1, innerSum_chi_eq_two_pow_mul_fourierCoeff, h S hS, mul_zero, mul_zero]
    · have h0 : fourierCoeff p S = 0 := hlow S (Nat.lt_of_not_ge hS)
      simp [h0]

lemma pureHighDegree_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {φ : (ι → Bool) → ℝ} {d : ℕ}
    (h : PureHighDegree φ d) (c : ℝ) : PureHighDegree (fun x => c * φ x) d := by
  intro p hp
  rw [innerSum_smul_left, h p hp, mul_zero]

lemma abs_innerSum_le_l1Norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → Bool) → ℝ) (f : (ι → Bool) → Bool) :
    |innerSum φ (fun x => signVal (f x))| ≤ l1Norm φ := by
  rw [innerSum_eq_sum]
  calc |∑ x, φ x * signVal (f x)|
      ≤ ∑ x, |φ x * signVal (f x)| := Finset.abs_sum_le_sum_abs _ _
    _ = l1Norm φ := by simp [l1Norm, abs_mul]

lemma pureHighDegree_sum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : (ι → Bool) → ℝ} {d : ℕ} (h : PureHighDegree φ d) : ∑ x, φ x = 0 := by
  have h1 := h (fun _ => (1 : ℝ)) (const_mem_lowDegree d 1)
  simpa [innerSum] using h1

lemma pureHighDegree_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : (ι → Bool) → ℝ} {d₁ d₂ : ℕ}
    (h : PureHighDegree φ d₂) (hd : d₁ ≤ d₂) : PureHighDegree φ d₁ := by
  exact fun p hp => h p (lowDegree_mono hd hp)

/-! ### Sign approximate degree and one-sided approximate degree -/

/-- Sign-valued $\varepsilon$-approximate degree $\widetilde{\deg}_\varepsilon(f)$: the minimum
degree of a real polynomial $p$ with $|p(x) - \mathrm{signVal}(f(x))| \le \varepsilon$ on the
Boolean cube. -/
noncomputable def signApproxDegree {n : ℕ} (ε : ℝ) (f : BooleanFunction n) : ℕ :=
  sInf {d | ∃ p ∈ lowDegree ℝ (Fin n) d, ∀ x, |p x - signVal (f x)| ≤ ε}

/-- One-sided $\varepsilon$-approximation: $p(x) \le -1 + \varepsilon$ whenever $f(x) = -1$
(`true`), and $|p(x) - 1| \le \varepsilon$ whenever $f(x) = +1$ (`false`). -/
def IsOneSidedApprox {n : ℕ} (ε : ℝ) (f : BooleanFunction n) (p : BitString n → ℝ) : Prop :=
  (∀ x, f x = true → p x ≤ -1 + ε) ∧ (∀ x, f x = false → |p x - 1| ≤ ε)

/-- One-sided $\varepsilon$-approximate degree $\widetilde{\deg}_\varepsilon^{-}(f)$. -/
noncomputable def oneSidedApproxDegree {n : ℕ} (ε : ℝ) (f : BooleanFunction n) : ℕ :=
  sInf {d | ∃ p ∈ lowDegree ℝ (Fin n) d, IsOneSidedApprox ε f p}

lemma signApproxDegree_le_of_mem_lowDegree {n d : ℕ} {ε : ℝ} {f : BooleanFunction n}
    {p : BitString n → ℝ} (hp : p ∈ lowDegree ℝ (Fin n) d)
    (h : ∀ x, |p x - signVal (f x)| ≤ ε) : signApproxDegree ε f ≤ d := by
  exact Nat.sInf_le ⟨p, hp, h⟩

lemma exists_mem_lowDegree_signApproxDegree {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (f : BooleanFunction n) :
    ∃ p ∈ lowDegree ℝ (Fin n) (signApproxDegree ε f), ∀ x, |p x - signVal (f x)| ≤ ε := by
  have hmem : (fun x => signVal (f x)) ∈ lowDegree ℝ (Fin n) n := by
    simpa [Fintype.card_fin] using mem_lowDegree_self (fun x => signVal (f x))
  have hne : {d | ∃ p ∈ lowDegree ℝ (Fin n) d, ∀ x, |p x - signVal (f x)| ≤ ε}.Nonempty :=
    ⟨n, fun x => signVal (f x), hmem, fun x => by simpa using hε⟩
  exact Nat.sInf_mem hne

lemma signApproxDegree_eq_approxDegree {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    signApproxDegree ε f = approxDegree (Real.toNNReal (ε / 2)) f := by
  have hcoe : ((Real.toNNReal (ε / 2) : ℝ≥0) : ℝ) = ε / 2 :=
    Real.coe_toNNReal (ε / 2) (by positivity)
  refine le_antisymm ?_ ?_
  · obtain ⟨p, hp, hpf⟩ :=
      exists_mem_lowDegree_approxDegree (ε := Real.toNNReal (ε / 2)) (f := f)
    refine signApproxDegree_le_of_mem_lowDegree
      (p := fun x => 1 - 2 * p x)
      (Submodule.sub_mem _ (const_mem_lowDegree _ 1) (Submodule.smul_mem _ (2 : ℝ) hp))
      (fun x => ?_)
    have hx := hpf x
    rw [hcoe] at hx
    rw [signVal_eq_one_sub_two_mul_bitVal]
    have hrew : 1 - 2 * p x - (1 - 2 * bitVal ℝ (f x)) = (-2) * (p x - bitVal ℝ (f x)) := by ring
    rw [hrew, abs_mul]
    norm_num
    linarith
  · obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_signApproxDegree hε f
    refine approxDegree_le_of_mem_lowDegree
      (p := fun x => (1 - p x) / 2)
      (by
        have h1 : (fun x => (1 - p x) / 2) = (2⁻¹ : ℝ) • (1 - p) := by
          ext x; simp [div_eq_inv_mul]
        rw [h1]
        exact Submodule.smul_mem _ _ (one_sub_mem_lowDegree hp))
      (fun x => ?_)
    have hx := hpf x
    have hbit : bitVal ℝ (f x) = (1 - signVal (f x)) / 2 := by
      rw [signVal_eq_one_sub_two_mul_bitVal]; ring
    rw [hbit, hcoe]
    have hrew : (1 - p x) / 2 - (1 - signVal (f x)) / 2 = -(1 / 2) * (p x - signVal (f x)) := by
      ring
    rw [hrew, abs_mul]
    norm_num
    linarith

lemma signApproxDegree_antitone {n : ℕ} {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (f : BooleanFunction n) : signApproxDegree δ f ≤ signApproxDegree ε f := by
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_signApproxDegree hε f
  exact signApproxDegree_le_of_mem_lowDegree hp fun x => (hpf x).trans hεδ

lemma signApproxDegree_not {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    signApproxDegree ε (fun x => !f x) = signApproxDegree ε f := by
  rw [signApproxDegree_eq_approxDegree hε, signApproxDegree_eq_approxDegree hε, approxDegree_not]

lemma signApproxDegree_comp_not {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    signApproxDegree ε (fun x => f (fun i => !x i)) = signApproxDegree ε f := by
  have key (g : BooleanFunction n) :
      signApproxDegree ε (fun x => g (fun i => !x i)) ≤ signApproxDegree ε g := by
    obtain ⟨p, hp, hpg⟩ := exists_mem_lowDegree_signApproxDegree hε g
    exact signApproxDegree_le_of_mem_lowDegree (comp_not_mem_lowDegree hp) fun x => hpg _
  refine le_antisymm (key f) ?_
  have := key (fun x => f (fun i => !x i))
  simpa only [Bool.not_not] using this

lemma oneSidedApproxDegree_le_of_mem_lowDegree {n d : ℕ} {ε : ℝ} {f : BooleanFunction n}
    {p : BitString n → ℝ} (hp : p ∈ lowDegree ℝ (Fin n) d) (h : IsOneSidedApprox ε f p) :
    oneSidedApproxDegree ε f ≤ d := by
  exact Nat.sInf_le ⟨p, hp, h⟩

lemma exists_mem_lowDegree_oneSidedApproxDegree {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (f : BooleanFunction n) :
    ∃ p ∈ lowDegree ℝ (Fin n) (oneSidedApproxDegree ε f), IsOneSidedApprox ε f p := by
  have hmem : (fun x => signVal (f x)) ∈ lowDegree ℝ (Fin n) n := by
    simpa [Fintype.card_fin] using mem_lowDegree_self (fun x => signVal (f x))
  have hne : {d | ∃ p ∈ lowDegree ℝ (Fin n) d, IsOneSidedApprox ε f p}.Nonempty := by
    refine ⟨n, fun x => signVal (f x), hmem, ⟨?_, ?_⟩⟩
    · intro x hx; dsimp only; rw [hx, signVal_true]; linarith
    · intro x hx; dsimp only; rw [hx, signVal_false]; simpa using hε
  exact Nat.sInf_mem hne

lemma oneSidedApproxDegree_le_signApproxDegree {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (f : BooleanFunction n) : oneSidedApproxDegree ε f ≤ signApproxDegree ε f := by
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_signApproxDegree hε f
  refine oneSidedApproxDegree_le_of_mem_lowDegree hp ⟨?_, ?_⟩
  · intro x hx
    have := (abs_le.mp (hpf x)).2
    rw [hx, signVal_true] at this
    linarith
  · intro x hx
    have := hpf x
    rw [hx, signVal_false] at this
    exact this

lemma oneSidedApproxDegree_antitone {n : ℕ} {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (f : BooleanFunction n) : oneSidedApproxDegree δ f ≤ oneSidedApproxDegree ε f := by
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_oneSidedApproxDegree hε f
  refine oneSidedApproxDegree_le_of_mem_lowDegree hp ⟨?_, ?_⟩
  · intro x hx; exact (hpf.1 x hx).trans (by linarith)
  · intro x hx; exact (hpf.2 x hx).trans hεδ

lemma oneSidedApproxDegree_le_card {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    oneSidedApproxDegree ε f ≤ n :=
  (oneSidedApproxDegree_le_signApproxDegree hε f).trans <| by
    rw [signApproxDegree_eq_approxDegree hε]; exact approxDegree_le_card

lemma signApproxDegree_le_card {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    signApproxDegree ε f ≤ n := by
  rw [signApproxDegree_eq_approxDegree hε]; exact approxDegree_le_card

/-! ### LP duality for approximate degree and one-sided approximate degree -/

private lemma dual_weak_two_sided {n d : ℕ} {ε : ℝ} {f : BooleanFunction n}
    {p ψ : BitString n → ℝ} (hp : p ∈ lowDegree ℝ (Fin n) d)
    (hpf : ∀ x, |p x - signVal (f x)| ≤ ε)
    (hphd : PureHighDegree ψ d) (hnorm : l1Norm ψ = 1)
    (hcorr : ε < innerSum ψ (fun x => signVal (f x))) : False := by
  have h0 : innerSum ψ p = 0 := hphd p hp
  have hbound : innerSum ψ (fun x => signVal (f x)) - innerSum ψ p ≤ ε * l1Norm ψ := by
    have hdiff : innerSum ψ (fun x => signVal (f x)) - innerSum ψ p =
        ∑ x, ψ x * (signVal (f x) - p x) := by
      simp only [innerSum, ← Finset.sum_sub_distrib, mul_sub]
    rw [hdiff, l1Norm, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc ψ x * (signVal (f x) - p x)
        ≤ |ψ x * (signVal (f x) - p x)| := le_abs_self _
      _ = |ψ x| * |p x - signVal (f x)| := by rw [abs_mul, abs_sub_comm]
      _ ≤ |ψ x| * ε := mul_le_mul_of_nonneg_left (hpf x) (abs_nonneg _)
      _ = ε * |ψ x| := mul_comm _ _
  rw [h0, sub_zero, hnorm, mul_one] at hbound
  linarith

private lemma dual_weak_one_sided {n d : ℕ} {ε : ℝ} {f : BooleanFunction n}
    {p ψ : BitString n → ℝ} (hp : p ∈ lowDegree ℝ (Fin n) d)
    (hpf : IsOneSidedApprox ε f p)
    (hphd : PureHighDegree ψ d) (hnorm : l1Norm ψ = 1)
    (hcorr : ε < innerSum ψ (fun x => signVal (f x)))
    (hone : ∀ x, f x = true → ψ x ≤ 0) : False := by
  have h0 : innerSum ψ p = 0 := hphd p hp
  have hbound : innerSum ψ (fun x => signVal (f x)) - innerSum ψ p ≤ ε * l1Norm ψ := by
    have hdiff : innerSum ψ (fun x => signVal (f x)) - innerSum ψ p =
        ∑ x, ψ x * (signVal (f x) - p x) := by
      simp only [innerSum, ← Finset.sum_sub_distrib, mul_sub]
    rw [hdiff, l1Norm, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    cases hfx : f x
    · have hx := hpf.2 x hfx
      rw [signVal_false]
      calc ψ x * (1 - p x)
          ≤ |ψ x * (1 - p x)| := le_abs_self _
        _ = |ψ x| * |p x - 1| := by rw [abs_mul, abs_sub_comm]
        _ ≤ |ψ x| * ε := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
        _ = ε * |ψ x| := mul_comm _ _
    · have hψ : ψ x ≤ 0 := hone x hfx
      have hp1 : p x ≤ -1 + ε := hpf.1 x hfx
      rw [signVal_true, abs_of_nonpos hψ]
      nlinarith
  rw [h0, sub_zero, hnorm, mul_one] at hbound
  linarith

/-- **Dual characterization of approximate degree**: for any `ε ≥ 0`, `d < signApproxDegree ε f`
if and only if there exists a dual polynomial `ψ` of pure high degree `> d` with `‖ψ‖₁ = 1` and
`⟨ψ, f⟩ > ε`. -/
theorem lt_signApproxDegree_iff {n d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    d < signApproxDegree ε f ↔
      ∃ ψ : BitString n → ℝ,
        PureHighDegree ψ d ∧ l1Norm ψ = 1 ∧ ε < innerSum ψ (fun x => signVal (f x)) := by
  constructor
  · intro hlt
    let SIdx := {S : Finset (Fin n) // #S ≤ d}
    let A : Matrix (BitString n ⊕ BitString n) (SIdx ⊕ Unit) ℝ :=
      Matrix.of fun r c => match r, c with
        | .inl x, .inl S => chi ℝ S.1 x
        | .inl _, .inr _ => -1
        | .inr x, .inl S => -chi ℝ S.1 x
        | .inr _, .inr _ => -1
    let b : BitString n ⊕ BitString n → ℝ := fun r => match r with
      | .inl x => signVal (f x)
      | .inr x => -signVal (f x)
    let cObj : SIdx ⊕ Unit → ℝ := fun c => match c with
      | .inl _ => 0
      | .inr _ => -1
    have hP : ∃ z, A *ᵥ z ≤ b := by
      refine ⟨fun c => match c with | .inl _ => 0 | .inr _ => 1, ?_⟩
      rintro (x | x) <;>
        simp [A, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] <;>
        cases f x <;> norm_num
    have checkFeas : ∀ z, A *ᵥ z ≤ b → z (.inr ()) ≤ ε → False := by
      intro z hz hzε
      let p : BitString n → ℝ := fun x => ∑ S : SIdx, chi ℝ S.1 x * z (.inl S)
      have hp : p ∈ lowDegree ℝ (Fin n) d := by
        have hp_eq : p = ∑ S : SIdx, z (.inl S) • chi ℝ S.1 := by
          ext x; simp [p, Finset.sum_apply, mul_comm]
        rw [hp_eq]
        exact Submodule.sum_mem _ fun S _ =>
          Submodule.smul_mem _ _ (lowDegree_mono S.2 (chi_mem_lowDegree S.1))
      have hpf : ∀ x, |p x - signVal (f x)| ≤ ε := by
        intro x
        have h1 : (A *ᵥ z) (.inl x) ≤ b (.inl x) := hz (.inl x)
        have h2 : (A *ᵥ z) (.inr x) ≤ b (.inr x) := hz (.inr x)
        simp only [A, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
          neg_mul, one_mul, Finset.sum_neg_distrib, Matrix.of_apply] at h1 h2
        dsimp only [p]
        rw [abs_le]
        constructor <;> linarith
      exact (signApproxDegree_le_of_mem_lowDegree hp hpf).not_gt hlt
    have hbdd : BddAbove ((cObj ⬝ᵥ ·) '' {z | A *ᵥ z ≤ b}) := by
      refine ⟨-ε, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      dsimp only
      have hval : cObj ⬝ᵥ z = -z (.inr ()) := by
        simp [cObj, dotProduct, Fintype.sum_sum_type]
      rw [hval]
      by_contra hnot
      push Not at hnot
      exact checkFeas z hz (by linarith)
    obtain ⟨z, y, hz, hy, hyA, hzy⟩ := Matrix.exists_dual_eq_of_bddAbove A b cObj hP hbdd
    have hεopt : ε < z (.inr ()) := by
      by_contra hnot; push Not at hnot; exact checkFeas z hz hnot
    let ψ₀ : BitString n → ℝ := fun x => y (.inr x) - y (.inl x)
    have hψ_phd : PureHighDegree ψ₀ d := by
      rw [pureHighDegree_iff_fourierCoeff]
      intro S hS
      have hcol := congr_fun hyA (.inl ⟨S, hS⟩)
      simp only [Matrix.vecMul, dotProduct, cObj, A, Matrix.of_apply, Fintype.sum_sum_type,
        mul_neg] at hcol
      rw [fourierCoeff_eq_sum]
      have hsum : ∑ x, ψ₀ x * chi ℝ S x = 0 := by
        have : ∑ x, ψ₀ x * chi ℝ S x =
            -(∑ x, y (.inl x) * chi ℝ S x + ∑ x, -(y (.inr x) * chi ℝ S x)) := by
          simp only [ψ₀, sub_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
          ring
        rw [this, hcol, neg_zero]
      rw [hsum, zero_div]
    have hψ_sum : ∑ x, (y (.inl x) + y (.inr x)) = 1 := by
      have hcol := congr_fun hyA (.inr ())
      simp only [Matrix.vecMul, dotProduct, cObj, A, Matrix.of_apply, Fintype.sum_sum_type,
        mul_neg, mul_one, Finset.sum_neg_distrib] at hcol
      rw [Finset.sum_add_distrib]
      linarith
    have hψ_corr : innerSum ψ₀ (fun x => signVal (f x)) = z (.inr ()) := by
      have hobj : y ⬝ᵥ b = -innerSum ψ₀ (fun x => signVal (f x)) := by
        simp only [dotProduct, b, Fintype.sum_sum_type, innerSum, ψ₀, sub_mul,
          Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
        ring
      have hcval : cObj ⬝ᵥ z = -z (.inr ()) := by
        simp [cObj, dotProduct, Fintype.sum_sum_type]
      linarith [hzy]
    have hψ_l1_le : l1Norm ψ₀ ≤ 1 := by
      rw [← hψ_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 : 0 ≤ y (.inl x) := hy (.inl x)
      have h2 : 0 ≤ y (.inr x) := hy (.inr x)
      rw [abs_le]
      constructor <;> linarith
    have hψ_l1_pos : 0 < l1Norm ψ₀ := by
      have hle := abs_innerSum_le_l1Norm ψ₀ f
      have hgt : ε < innerSum ψ₀ (fun x => signVal (f x)) := hψ_corr ▸ hεopt
      have hpos : 0 < innerSum ψ₀ (fun x => signVal (f x)) := lt_of_le_of_lt hε hgt
      exact lt_of_lt_of_le hpos ((le_abs_self _).trans hle)
    refine ⟨fun x => (l1Norm ψ₀)⁻¹ * ψ₀ x, pureHighDegree_smul hψ_phd _, ?_, ?_⟩
    · rw [l1Norm_smul, abs_of_pos (inv_pos.mpr hψ_l1_pos), inv_mul_cancel₀ hψ_l1_pos.ne']
    · rw [innerSum_smul_left, hψ_corr]
      have h1 : 1 ≤ (l1Norm ψ₀)⁻¹ := one_le_inv₀ hψ_l1_pos |>.mpr hψ_l1_le
      have h2 : z (.inr ()) ≤ (l1Norm ψ₀)⁻¹ * z (.inr ()) :=
        le_mul_of_one_le_left (hε.trans hεopt.le) h1
      linarith
  · rintro ⟨ψ, hphd, hnorm, hcorr⟩
    by_contra hnot
    push Not at hnot
    obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_signApproxDegree hε f
    exact dual_weak_two_sided (lowDegree_mono hnot hp) hpf hphd hnorm hcorr

/-- **Dual characterization of one-sided approximate degree**: for any `ε ≥ 0`,
`d < oneSidedApproxDegree ε f` if and only if there exists a dual polynomial `ψ` of pure high
degree `> d` with `‖ψ‖₁ = 1`, `⟨ψ, f⟩ > ε`, and `ψ(x) ≤ 0` whenever `f(x) = -1` (`true`). -/
theorem lt_oneSidedApproxDegree_iff {n d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    d < oneSidedApproxDegree ε f ↔
      ∃ ψ : BitString n → ℝ,
        PureHighDegree ψ d ∧ l1Norm ψ = 1 ∧ ε < innerSum ψ (fun x => signVal (f x)) ∧
          ∀ x, f x = true → ψ x ≤ 0 := by
  constructor
  · intro hlt
    let SIdx := {S : Finset (Fin n) // #S ≤ d}
    let FalseIdx := {x : BitString n // f x = false}
    let A : Matrix (BitString n ⊕ FalseIdx) (SIdx ⊕ Unit) ℝ :=
      Matrix.of fun r c => match r, c with
        | .inl x, .inl S => chi ℝ S.1 x
        | .inl _, .inr _ => -1
        | .inr x, .inl S => -chi ℝ S.1 x.1
        | .inr _, .inr _ => -1
    let b : BitString n ⊕ FalseIdx → ℝ := fun r => match r with
      | .inl x => signVal (f x)
      | .inr _ => -1
    let cObj : SIdx ⊕ Unit → ℝ := fun c => match c with
      | .inl _ => 0
      | .inr _ => -1
    have hP : ∃ z, A *ᵥ z ≤ b := by
      refine ⟨fun c => match c with | .inl _ => 0 | .inr _ => 1, ?_⟩
      rintro (x | x)
      · simp [A, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
        cases f x <;> norm_num
      · simp [A, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have checkFeas : ∀ z, A *ᵥ z ≤ b → z (.inr ()) ≤ ε → False := by
      intro z hz hzε
      let p : BitString n → ℝ := fun x => ∑ S : SIdx, chi ℝ S.1 x * z (.inl S)
      have hp : p ∈ lowDegree ℝ (Fin n) d := by
        have hp_eq : p = ∑ S : SIdx, z (.inl S) • chi ℝ S.1 := by
          ext x; simp [p, Finset.sum_apply, mul_comm]
        rw [hp_eq]
        exact Submodule.sum_mem _ fun S _ =>
          Submodule.smul_mem _ _ (lowDegree_mono S.2 (chi_mem_lowDegree S.1))
      have hpf : IsOneSidedApprox ε f p := by
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · have h1 : (A *ᵥ z) (.inl x) ≤ b (.inl x) := hz (.inl x)
          simp only [A, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
            neg_mul, one_mul, Matrix.of_apply, hx, signVal_true] at h1
          dsimp only [p]
          linarith
        · have h1 : (A *ᵥ z) (.inl x) ≤ b (.inl x) := hz (.inl x)
          have h2 : (A *ᵥ z) (.inr ⟨x, hx⟩) ≤ b (.inr ⟨x, hx⟩) := hz (.inr ⟨x, hx⟩)
          simp only [A, b, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
            neg_mul, one_mul, Finset.sum_neg_distrib, Matrix.of_apply, hx, signVal_false] at h1 h2
          dsimp only [p]
          rw [abs_le]
          constructor <;> linarith
      exact (oneSidedApproxDegree_le_of_mem_lowDegree hp hpf).not_gt hlt
    have hbdd : BddAbove ((cObj ⬝ᵥ ·) '' {z | A *ᵥ z ≤ b}) := by
      refine ⟨-ε, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      dsimp only
      have hval : cObj ⬝ᵥ z = -z (.inr ()) := by
        simp [cObj, dotProduct, Fintype.sum_sum_type]
      rw [hval]
      by_contra hnot
      push Not at hnot
      exact checkFeas z hz (by linarith)
    obtain ⟨z, y, hz, hy, hyA, hzy⟩ := Matrix.exists_dual_eq_of_bddAbove A b cObj hP hbdd
    have hεopt : ε < z (.inr ()) := by
      by_contra hnot; push Not at hnot; exact checkFeas z hz hnot
    let v : BitString n → ℝ := fun x => if hx : f x = false then y (.inr ⟨x, hx⟩) else 0
    let ψ₀ : BitString n → ℝ := fun x => v x - y (.inl x)
    have hv_sum : ∀ g : BitString n → ℝ,
        ∑ x : FalseIdx, y (.inr x) * g x.1 = ∑ x, v x * g x := by
      intro g
      rw [show (∑ x, v x * g x) = ∑ x ∈ Finset.univ.filter fun x => f x = false, v x * g x by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : f x = false <;> simp [v, hx]]
      refine Finset.sum_bij (fun (x : FalseIdx) _ => x.1)
        (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun x hx => ⟨⟨x, (Finset.mem_filter.mp hx).2⟩, Finset.mem_univ _, rfl⟩)
        (fun x _ => by simp [v, x.2])
    have hψ_phd : PureHighDegree ψ₀ d := by
      rw [pureHighDegree_iff_fourierCoeff]
      intro S hS
      have hcol := congr_fun hyA (.inl ⟨S, hS⟩)
      simp only [Matrix.vecMul, dotProduct, cObj, A, Matrix.of_apply, Fintype.sum_sum_type,
        mul_neg] at hcol
      rw [Finset.sum_neg_distrib, hv_sum (chi ℝ S)] at hcol
      rw [fourierCoeff_eq_sum]
      have hsum : ∑ x, ψ₀ x * chi ℝ S x = 0 := by
        have : ∑ x, ψ₀ x * chi ℝ S x =
          -(∑ x, y (.inl x) * chi ℝ S x + -(∑ x, v x * chi ℝ S x)) := by
          simp only [ψ₀, sub_mul, Finset.sum_sub_distrib]
          ring
        rw [this, hcol, neg_zero]
      rw [hsum, zero_div]
    have hψ_sum : ∑ x, (y (.inl x) + v x) = 1 := by
      have hcol := congr_fun hyA (.inr ())
      simp only [Matrix.vecMul, dotProduct, cObj, A, Matrix.of_apply, Fintype.sum_sum_type,
        mul_neg, mul_one, Finset.sum_neg_distrib] at hcol
      have hv1 : ∑ x : FalseIdx, y (.inr x) = ∑ x, v x := by
        simpa using hv_sum (fun _ => 1)
      rw [Finset.sum_add_distrib, ← hv1]
      linarith
    have hψ_corr : innerSum ψ₀ (fun x => signVal (f x)) = z (.inr ()) := by
      have hv_sign : ∑ x : FalseIdx, y (.inr x) * (-1) =
          -(∑ x, v x * signVal (f x)) := by
        have := hv_sum (fun x => signVal (f x))
        rw [← this, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [x.2, signVal_false]; ring
      have hobj : y ⬝ᵥ b = -innerSum ψ₀ (fun x => signVal (f x)) := by
        simp only [dotProduct, b, Fintype.sum_sum_type, innerSum, ψ₀, sub_mul,
          Finset.sum_sub_distrib, hv_sign]
        ring
      have hcval : cObj ⬝ᵥ z = -z (.inr ()) := by
        simp [cObj, dotProduct, Fintype.sum_sum_type]
      linarith [hzy]
    have hψ_l1_le : l1Norm ψ₀ ≤ 1 := by
      rw [← hψ_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 : 0 ≤ y (.inl x) := hy (.inl x)
      have h2 : 0 ≤ v x := by
        by_cases hx : f x = false
        · simp only [v, hx, ↓reduceDIte]
          exact hy (.inr ⟨x, hx⟩)
        · simp [v, hx]
      rw [abs_le]
      constructor <;> linarith
    have hψ_l1_pos : 0 < l1Norm ψ₀ := by
      have hle := abs_innerSum_le_l1Norm ψ₀ f
      have hgt : ε < innerSum ψ₀ (fun x => signVal (f x)) := hψ_corr ▸ hεopt
      have hpos : 0 < innerSum ψ₀ (fun x => signVal (f x)) := lt_of_le_of_lt hε hgt
      exact lt_of_lt_of_le hpos ((le_abs_self _).trans hle)
    have hψ_one : ∀ x, f x = true → ψ₀ x ≤ 0 := by
      intro x hx
      have h1 : 0 ≤ y (.inl x) := hy (.inl x)
      simp only [ψ₀, v, hx, Bool.true_eq_false, ↓reduceDIte, zero_sub]
      linarith
    refine ⟨fun x => (l1Norm ψ₀)⁻¹ * ψ₀ x, pureHighDegree_smul hψ_phd _, ?_, ?_, ?_⟩
    · rw [l1Norm_smul, abs_of_pos (inv_pos.mpr hψ_l1_pos), inv_mul_cancel₀ hψ_l1_pos.ne']
    · rw [innerSum_smul_left, hψ_corr]
      have h1 : 1 ≤ (l1Norm ψ₀)⁻¹ := one_le_inv₀ hψ_l1_pos |>.mpr hψ_l1_le
      have h2 : z (.inr ()) ≤ (l1Norm ψ₀)⁻¹ * z (.inr ()) :=
        le_mul_of_one_le_left (hε.trans hεopt.le) h1
      linarith
    · intro x hx
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hψ_l1_pos.le) (hψ_one x hx)
  · rintro ⟨ψ, hphd, hnorm, hcorr, hone⟩
    by_contra hnot
    push Not at hnot
    obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_oneSidedApproxDegree hε f
    exact dual_weak_one_sided (lowDegree_mono hnot hp) hpf hphd hnorm hcorr hone

/-! ### Constant-error amplification -/

private noncomputable def ampStep (t : ℝ) : ℝ := (3 / 2 : ℝ) * t - (1 / 2 : ℝ) * t ^ 3

private lemma ampStep_neg (t : ℝ) : ampStep (-t) = -ampStep t := by
  simp only [ampStep]; ring

private lemma ampStep_mem_Icc {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ampStep t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have : ampStep t = t * (3 / 2 - (1 / 2) * t ^ 2) := by simp only [ampStep]; ring
    rw [this]
    exact mul_nonneg ht0 (by nlinarith)
  · have : 1 - ampStep t = (1 / 2) * (t - 1) ^ 2 * (t + 2) := by simp only [ampStep]; ring
    nlinarith [sq_nonneg (t - 1)]

private lemma ampStep_mono {t₁ t₂ : ℝ} (h10 : 0 ≤ t₁) (h21 : t₂ ≤ 1) (h : t₁ ≤ t₂) :
    ampStep t₁ ≤ ampStep t₂ := by
  have : ampStep t₂ - ampStep t₁ = (1 / 2) * (t₂ - t₁) * (3 - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)) := by
    simp only [ampStep]; ring
  have hsq : t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 ≤ 3 := by nlinarith
  nlinarith

private lemma ampStep_ge_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (11 / 8 : ℝ) * t ≤ ampStep t := by
  have : ampStep t - (11 / 8) * t = t * (1 / 8 - (1 / 2) * t ^ 2) := by simp only [ampStep]; ring
  nlinarith [sq_nonneg (t - 1 / 2)]

private lemma ampStep_ge_two_thirds {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    (2 / 3 : ℝ) ≤ ampStep t := by
  have h1 : ampStep (1 / 2) ≤ ampStep t := ampStep_mono (by norm_num) ht1 ht0
  have h2 : (2 / 3 : ℝ) ≤ ampStep (1 / 2) := by norm_num [ampStep]
  linarith

private lemma ampStep_iter_mem_Icc (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ampStep^[k] t ∈ Set.Icc (0 : ℝ) 1 := by
  induction k generalizing t with
  | zero => exact ⟨ht0, ht1⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have h := ampStep_mem_Icc ht0 ht1
    exact ih h.1 h.2

private lemma ampStep_iter_neg (k : ℕ) (t : ℝ) : ampStep^[k] (-t) = -ampStep^[k] t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ampStep_neg, ih]

private lemma ampStep_iter_ge (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min (1 / 2) ((11 / 8 : ℝ) ^ k * t) ≤ ampStep^[k] t := by
  induction k generalizing t with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    exact min_le_right _ _
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hmem := ampStep_mem_Icc ht0 ht1
    by_cases hhalf : t ≤ 1 / 2
    · have hstep := ampStep_ge_mul ht0 hhalf
      have hih := ih hmem.1 hmem.2
      have hmul : (11 / 8 : ℝ) ^ (k + 1) * t ≤ (11 / 8 : ℝ) ^ k * ampStep t := by
        rw [pow_succ, mul_assoc]
        exact mul_le_mul_of_nonneg_left hstep (by positivity)
      exact (min_le_min_left _ hmul).trans hih
    · push Not at hhalf
      have h1 : (1 / 2 : ℝ) ≤ ampStep t := (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans
        (ampStep_ge_two_thirds hhalf.le ht1)
      have hmono : ∀ m : ℕ, ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 1 → (1 / 2 : ℝ) ≤ ampStep^[m] u := by
        intro m
        induction m with
        | zero => intro u hu _; exact hu
        | succ m ihm =>
          intro u hu1 hu2
          rw [Function.iterate_succ_apply]
          have hm := ampStep_mem_Icc (by linarith) hu2
          exact ihm _ ((by norm_num : (1 / 2 : ℝ) ≤ 2 / 3).trans
            (ampStep_ge_two_thirds hu1 hu2)) hm.2
      exact (min_le_left _ _).trans (hmono k (ampStep t) h1 hmem.2)

private lemma ampStep_iter_mem_lowDegree {n d : ℕ} (k : ℕ) {p : BitString n → ℝ}
    (hp : p ∈ lowDegree ℝ (Fin n) d) :
    (fun x => ampStep^[k] (p x)) ∈ lowDegree ℝ (Fin n) (3 ^ k * d) := by
  induction k generalizing p d with
  | zero => simpa using hp
  | succ k ih =>
    have h1 : (fun x => ampStep (p x)) ∈ lowDegree ℝ (Fin n) (3 * d) := by
      have heq : (fun x => ampStep (p x)) =
          (3 / 2 : ℝ) • p - (1 / 2 : ℝ) • (p ^ 3) := by
        ext x; simp [ampStep]
      rw [heq]
      refine Submodule.sub_mem _
        (Submodule.smul_mem _ _ (lowDegree_mono (by omega) hp))
        (Submodule.smul_mem _ _ ?_)
      simpa [mul_comm] using pow_mem_lowDegree hp 3
    have h2 := ih h1
    have hdeg : 3 ^ k * (3 * d) = 3 ^ (k + 1) * d := by ring
    rw [hdeg] at h2
    convert h2 using 1
    ext x
    exact Function.iterate_succ_apply ampStep k (p x)

/-- **Constant-error amplification**: reducing sign-approximation error from `99 / 100` to `1 / 3`
increases the degree by at most a constant factor `3 ^ 19`. -/
theorem signApproxDegree_one_third_le_of_large_error {n : ℕ} (f : BooleanFunction n) :
    signApproxDegree (1 / 3) f ≤ 3 ^ 19 * signApproxDegree (99 / 100) f := by
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_signApproxDegree (by norm_num : (0 : ℝ) ≤ 99 / 100) f
  let q : BitString n → ℝ := fun x => (1 / 2 : ℝ) * p x
  have hq : q ∈ lowDegree ℝ (Fin n) (signApproxDegree (99 / 100) f) :=
    Submodule.smul_mem _ _ hp
  refine signApproxDegree_le_of_mem_lowDegree (ampStep_iter_mem_lowDegree 19 hq) fun x => ?_
  have hpx := abs_le.mp (hpf x)
  set s : ℝ := signVal (f x)
  have hs_sq : s * s = 1 := signVal_mul_self (f x)
  have hsq_mem : s * q x ∈ Set.Icc (1 / 200 : ℝ) 1 := by
    cases hfx : f x <;> simp only [s, q, hfx, signVal_false, signVal_true] at hpx ⊢ <;>
      constructor <;> linarith
  have h18 : (1 / 2 : ℝ) ≤ ampStep^[18] (s * q x) := by
    have h := ampStep_iter_ge 18 (by linarith [hsq_mem.1]) hsq_mem.2
    have hpow : (1 / 2 : ℝ) ≤ (11 / 8 : ℝ) ^ 18 * (1 / 200) := by norm_num
    have hmul : (1 / 2 : ℝ) ≤ (11 / 8 : ℝ) ^ 18 * (s * q x) :=
      hpow.trans (mul_le_mul_of_nonneg_left hsq_mem.1 (by positivity))
    exact (le_min le_rfl hmul).trans h
  have h18_le : ampStep^[18] (s * q x) ≤ 1 :=
    (ampStep_iter_mem_Icc 18 (by linarith [hsq_mem.1]) hsq_mem.2).2
  have h19_lo : (2 / 3 : ℝ) ≤ ampStep^[19] (s * q x) := by
    rw [show (19 : ℕ) = 18 + 1 from rfl, Function.iterate_succ_apply']
    exact ampStep_ge_two_thirds h18 h18_le
  have h19_hi : ampStep^[19] (s * q x) ≤ 1 :=
    (ampStep_iter_mem_Icc 19 (by linarith [hsq_mem.1]) hsq_mem.2).2
  have hsign_pull : ampStep^[19] (s * q x) = s * ampStep^[19] (q x) := by
    cases hfx : f x <;> simp [s, hfx, ampStep_iter_neg]
  rw [hsign_pull] at h19_lo h19_hi
  have hrew : ampStep^[19] (q x) - s = s * (s * ampStep^[19] (q x) - 1) := by
    have hmul : s * (s * ampStep^[19] (q x) - 1) = (s * s) * ampStep^[19] (q x) - s := by ring
    rw [hmul, hs_sq, one_mul]
  rw [hrew, abs_mul, abs_signVal, one_mul, abs_le]
  constructor <;> linarith

/-! ### Small-error approximate degree of $\mathrm{AND}_m$ -/

/-- One-sidedness is without loss of generality for $\mathrm{AND}_m$:
$\widetilde{\deg}_\gamma^{-}(\mathrm{AND}_m) = \widetilde{\deg}_\gamma(\mathrm{AND}_m)$
for all $\gamma \ge 0$. -/
theorem oneSidedApproxDegree_and_eq_signApproxDegree {m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) :
    oneSidedApproxDegree γ (threshold m m) = signApproxDegree γ (threshold m m) := by
  refine le_antisymm (oneSidedApproxDegree_le_signApproxDegree hγ _) ?_
  by_contra hlt
  push Not at hlt
  set d := oneSidedApproxDegree γ (threshold m m)
  have hd : d < signApproxDegree γ (threshold m m) := hlt
  obtain ⟨ψ, hphd, hnorm, hcorr⟩ := (lt_signApproxDegree_iff hγ _).mp hd
  have hone : ∀ x : BitString m, threshold m m x = true → ψ x ≤ 0 := by
    intro x hx
    have hsum0 : ∑ y : BitString m, ψ y = 0 := pureHighDegree_sum_eq_zero hphd
    have huniq : ∀ y : BitString m, y ≠ x → threshold m m y = false := by
      intro y hy
      rw [threshold_apply] at hx ⊢
      have hxall : ∀ i : Fin m, x i = true := by
        have hcard : #{i : Fin m | x i = true} = m :=
          le_antisymm ((Finset.card_le_univ _).trans_eq (Fintype.card_fin m))
            (decide_eq_true_eq.mp hx)
        have hfull := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin m).symm)
        intro i
        have := Finset.ext_iff.mp hfull i
        simpa using this
      have hyall : ¬ ∀ i : Fin m, y i = true := fun hall =>
        hy (funext fun i => (hall i).trans (hxall i).symm)
      rw [decide_eq_false_iff_not]
      intro hmy
      have hcard : #{i : Fin m | y i = true} = m :=
        le_antisymm ((Finset.card_le_univ _).trans_eq (Fintype.card_fin m)) hmy
      have hfull := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin m).symm)
      exact hyall fun i => by simpa using Finset.ext_iff.mp hfull i
    have hcorr_eq : innerSum ψ (fun y => signVal (threshold m m y)) = -2 * ψ x := by
      have hsplit : innerSum ψ (fun y => signVal (threshold m m y)) + ∑ y, ψ y =
          ∑ y, ψ y * (signVal (threshold m m y) + 1) := by
        simp only [innerSum,
          ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun y _ => by ring
      have hzero : ∑ y, ψ y * (signVal (threshold m m y) + 1) =
          ∑ y ∈ Finset.univ.erase x, ψ y * 2 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx, signVal_true]
        simp only [neg_add_cancel, mul_zero, zero_add]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [huniq y (Finset.ne_of_mem_erase hy), signVal_false]; norm_num
      have hsum_erase : ∑ y ∈ Finset.univ.erase x, ψ y = -ψ x := by
        have := Finset.add_sum_erase Finset.univ ψ (Finset.mem_univ x)
        linarith
      rw [hsum0, add_zero] at hsplit
      rw [hsplit, hzero, ← Finset.sum_mul, hsum_erase]; ring
    linarith
  have hd_lt : d < oneSidedApproxDegree γ (threshold m m) :=
    (lt_oneSidedApproxDegree_iff hγ _).mpr ⟨ψ, hphd, hnorm, hcorr, hone⟩
  exact lt_irrefl d hd_lt

lemma signApproxDegree_and_eq_or {m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) :
    signApproxDegree γ (threshold m m) = signApproxDegree γ (threshold m 1) := by
  have heq : threshold m m = fun x => !threshold m 1 (fun i => !x i) := by
    funext x
    rw [threshold_apply, threshold_apply]
    have hw : weight (fun i : Fin m => !x i) = m - weight x := by
      simpa [Fintype.card_fin] using weight_not x
    have hle : weight x ≤ m := by
      simpa [Fintype.card_fin] using weight_le x
    rw [hw]
    cases h : decide (m ≤ weight x) <;> simp at h ⊢ <;> omega
  rw [heq, signApproxDegree_not hγ, signApproxDegree_comp_not hγ]


/-! ### Block composition and the two-level AND–OR tree -/

/-- Block composition $(f \circ g^m)(x_1, \dots, x_m) = f(g(x_1), \dots, g(x_m))$ on
`BitString (m * n)`. -/
def blockComp {m n : ℕ} (f : BooleanFunction m) (g : BooleanFunction n) :
    BooleanFunction (m * n) :=
  fun x => f fun i => g fun j => x (finProdFinEquiv (i, j))

lemma blockComp_apply {m n : ℕ} (f : BooleanFunction m) (g : BooleanFunction n)
    (x : BitString (m * n)) :
    blockComp f g x = f fun i => g fun j => x (finProdFinEquiv (i, j)) := by rfl

/-- Boolean sign of a real number under the `true ↔ -1`, `false ↔ +1` convention:
`signBool t = true` iff `t < 0`. -/
noncomputable def signBool (t : ℝ) : Bool := decide (t < 0)

lemma signBool_eq_decide (t : ℝ) : signBool t = decide (t < 0) := by rfl

@[simp]
lemma signBool_of_neg {t : ℝ} (ht : t < 0) : signBool t = true := by
  simp [signBool, ht]

@[simp]
lemma signBool_of_nonneg {t : ℝ} (ht : 0 ≤ t) : signBool t = false := by
  simp [signBool, not_lt.mpr ht]

lemma mul_signVal_signBool (t : ℝ) : |t| * signVal (signBool t) = t := by
  unfold signBool
  by_cases ht : t < 0
  · simp [ht, abs_of_neg ht]
  · push Not at ht
    simp [not_lt.mpr ht, abs_of_nonneg ht]

lemma sum_abs_eq_half_of_pureHighDegree {n d : ℕ} {φ : BitString n → ℝ}
    (hphd : PureHighDegree φ d) (hnorm : l1Norm φ = 1) (b : Bool) :
    ∑ x with signBool (φ x) = b, |φ x| = 1 / 2 := by
  have hsum : ∑ x : BitString n, φ x = 0 := pureHighDegree_sum_eq_zero hphd
  have hpart : ∀ g : BitString n → ℝ,
      ∑ x, g x = (∑ x with signBool (φ x) = false, g x) +
        (∑ x with signBool (φ x) = true, g x) := by
    intro g
    have := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x => signBool (φ x) = false) (f := g)
    have hnot : Finset.univ.filter (fun x => ¬ signBool (φ x) = false) =
        Finset.univ.filter (fun x => signBool (φ x) = true) := by
      ext x; simp
    rw [hnot] at this
    exact this.symm
  have h1 := hpart φ
  have h2 := hpart (fun x => |φ x|)
  rw [hsum] at h1
  rw [← l1Norm_eq_sum, hnorm] at h2
  have hfalse : ∑ x with signBool (φ x) = false, φ x =
      ∑ x with signBool (φ x) = false, |φ x| := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hsb := (Finset.mem_filter.mp hx).2
    have hnn : 0 ≤ φ x := by
      simp only [signBool, decide_eq_false_iff_not, not_lt] at hsb; exact hsb
    exact (abs_of_nonneg hnn).symm
  have htrue : ∑ x with signBool (φ x) = true, φ x =
      -(∑ x with signBool (φ x) = true, |φ x|) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hsb := (Finset.mem_filter.mp hx).2
    have hneg : φ x < 0 := by simp only [signBool, decide_eq_true_eq] at hsb; exact hsb
    rw [abs_of_neg hneg, neg_neg]
  rw [hfalse, htrue] at h1
  cases b <;> linarith

end CslibFrontier.QueryComplexity
