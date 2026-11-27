/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Choose
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.ExpectPi
import Mathlib.Algebra.CharP.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetric Boolean Polynomials, Modular Equidistribution, and Local Correlation

This module develops reusable Boolean-analytic results on symmetric low-degree polynomials over
commutative rings and finite fields, modular equidistribution of Hamming weight on the Boolean
cube, exponential-sum correlation bounds against modular phase characters, and the Fourier
characterization of subcube local correlation.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.IsWeightSymmetric`: invariance of a function
  `(ι → Bool) → α` under preserving Hamming weight `Cslib.BitString.weight`.
* `CslibFrontier.Foundations.BooleanAnalysis.modPhase`: the modular unit-circle character
  `x ↦ exp(i φ · weight x)` on `ι → Bool`.
* `CslibFrontier.Foundations.BooleanAnalysis.modExpSum`: the signed modular exponential sum
  `𝔼 x, (-1) ^ (p x).val * modPhase φ x` for `p : (ι → Bool) → ZMod 2`.
* `CslibFrontier.Foundations.BooleanAnalysis.modCorrelation`: the modular correlation norm
  `‖modExpSum φ p‖`.
* `CslibFrontier.Foundations.BooleanAnalysis.localCorrelation`: the subcube local correlation
  variance `𝔼 x, (𝔼 y, F (S.piecewise y x) - 𝔼 z, F z) ^ 2` of `F : (ι → Bool) → ℝ` with respect
  to `S`.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.eq_zero_of_mem_lowDegree_of_forall_weight_le`: a
  degree-`d` polynomial function on `ι → Bool` vanishing on the Hamming ball of radius `d` is
  identically zero.
* `CslibFrontier.Foundations.BooleanAnalysis.IsWeightSymmetric.exists_sum_choose`: every
  weight-symmetric function in `Cslib.BitString.lowDegree R ι d` is an `R`-linear combination of
  binomial-weight functions `x ↦ (weight x).choose r` for `r ≤ d`.
* `CslibFrontier.Foundations.BooleanAnalysis.choose_mod_pow_prime_eq`: Lucas periodicity of
  binomial coefficients `w.choose r mod p` with period `p ^ δ` whenever `r < p ^ δ`.
* `CslibFrontier.Foundations.BooleanAnalysis.IsWeightSymmetric.eq_of_weight_modEq_prime_pow`:
  Bhatnagar–Gopalan–Lipton weight periodicity modulo `p ^ δ` for symmetric degree-`d` Boolean
  polynomials in characteristic `p` when `d < p ^ δ`.
* `CslibFrontier.Foundations.BooleanAnalysis.abs_expect_weight_mod_sub_inv_le`: uniform
  Hamming-weight residue equidistribution
  `|ℙ[weight x ≡ k (mod m)] - 1 / m| ≤ ((m - 1) / m) * |cos(π / m)| ^ |ι|`.
* `CslibFrontier.Foundations.BooleanAnalysis.modCorrelation_symmetric_le`: correlation bound
  `modCorrelation (2π k / m) s ≤ 2 m d * cos(π / (2 m d)) ^ |ι|` for symmetric degree-`d`
  polynomials over `ZMod 2` against odd-modulus characters.
* `CslibFrontier.Foundations.BooleanAnalysis.localCorrelation_eq_sum_fourierCoeff_sq`: Parseval
  identity equating `localCorrelation S F` to the Fourier mass on nonempty character sets disjoint
  from `S`.
-/

public section

namespace CslibFrontier.Foundations.BooleanAnalysis

open Cslib.BitString Finset
open scoped BigOperators

/-! ### Weight symmetry and binomial basis for low-degree Boolean polynomials -/

section WeightSymmetric

variable {ι : Type*} [Fintype ι]

/-- A function on a finite Boolean cube `ι → Bool` is *weight-symmetric* if its value depends only
on the Hamming weight `Cslib.BitString.weight x`. -/
def IsWeightSymmetric {α : Type*} (f : (ι → Bool) → α) : Prop :=
  ∀ ⦃x y : ι → Bool⦄, weight x = weight y → f x = f y

/-- Characterization of `IsWeightSymmetric` via equality on equal-weight inputs. -/
theorem isWeightSymmetric_iff {α : Type*} {f : (ι → Bool) → α} :
    IsWeightSymmetric f ↔ ∀ x y : ι → Bool, weight x = weight y → f x = f y := by
  rfl

/-- Constant functions are weight-symmetric. -/
theorem isWeightSymmetric_const {α : Type*} (c : α) :
    IsWeightSymmetric (fun _ : ι → Bool ↦ c) := by
  intro _ _ _
  rfl

/-- On `Cslib.BooleanFunction n`, `IsWeightSymmetric` coincides with
`Cslib.BooleanFunction.IsSymmetric`. -/
theorem isWeightSymmetric_iff_booleanFunction_isSymmetric {n : ℕ}
    {f : Cslib.BooleanFunction n} :
    IsWeightSymmetric f ↔ f.IsSymmetric := by
  rfl

/-- Weight-symmetric functions are closed under pointwise addition. -/
theorem IsWeightSymmetric.add {M : Type*} [Add M] {f g : (ι → Bool) → M}
    (hf : IsWeightSymmetric f) (hg : IsWeightSymmetric g) :
    IsWeightSymmetric (f + g) := by
  intro _ _ h
  exact congrArg₂ (· + ·) (hf h) (hg h)

/-- Weight-symmetric functions are closed under pointwise subtraction. -/
theorem IsWeightSymmetric.sub {G : Type*} [Sub G] {f g : (ι → Bool) → G}
    (hf : IsWeightSymmetric f) (hg : IsWeightSymmetric g) :
    IsWeightSymmetric (f - g) := by
  intro _ _ h
  exact congrArg₂ (· - ·) (hf h) (hg h)

/-- Weight-symmetric functions are closed under scalar multiplication. -/
theorem IsWeightSymmetric.smul {R M : Type*} [SMul R M] {f : (ι → Bool) → M} (c : R)
    (hf : IsWeightSymmetric f) :
    IsWeightSymmetric (c • f) := by
  intro _ _ h
  exact congrArg (c • ·) (hf h)

private lemma exists_weight_eq (w : ℕ) (hw : w ≤ Fintype.card ι) :
    ∃ x : ι → Bool, weight x = w := by
  classical
  have hpos : 0 < #{x : ι → Bool | weight x = w} := by
    rw [card_filter_weight_eq]
    exact Nat.choose_pos hw
  obtain ⟨x, hx⟩ := card_pos.mp hpos
  exact ⟨x, (mem_filter.mp hx).2⟩

/-- Every weight-symmetric function on `ι → Bool` factors through `Cslib.BitString.weight`. -/
theorem IsWeightSymmetric.exists_eq_comp_weight {α : Type*} [Nonempty α] {f : (ι → Bool) → α}
    (hf : IsWeightSymmetric f) :
    ∃ g : ℕ → α, ∀ x : ι → Bool, f x = g (weight x) := by
  classical
  refine ⟨fun w ↦
    if hw : w ≤ Fintype.card ι then f (exists_weight_eq w hw).choose else Classical.arbitrary α,
    fun x ↦ ?_⟩
  have hx : weight x ≤ Fintype.card ι := weight_le x
  dsimp only
  rw [dite_eq_left hx]
  exact hf (exists_weight_eq (weight x) hx).choose_spec.symm

/-- **Hamming-ball uniqueness for low-degree Boolean polynomials**: any function in
`Cslib.BitString.lowDegree R ι d` that vanishes on all inputs of Hamming weight at most `d` is
identically zero. -/
theorem eq_zero_of_mem_lowDegree_of_forall_weight_le {R : Type*} [CommRing R] {d : ℕ}
    {f : (ι → Bool) → R} (hf : f ∈ lowDegree R ι d)
    (h0 : ∀ x : ι → Bool, weight x ≤ d → f x = 0) :
    f = 0 := by
  classical
  let B : Finset (Finset ι) := univ.filter fun S : Finset ι ↦ #S ≤ d
  have hmem : f ∈ Submodule.span R (monomial R '' (B : Set (Finset ι))) := by
    rw [lowDegree] at hf
    refine Submodule.span_mono ?_ hf
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨S, mem_coe.mpr (mem_filter.mpr ⟨mem_univ S, hS⟩), rfl⟩
  rw [Fintype.mem_span_image_iff_exists_fun] at hmem
  obtain ⟨c, hcf⟩ := hmem
  have hc_zero : ∀ m : ℕ, ∀ S : (B : Set (Finset ι)), #S.1 = m → c S = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro S hSm
      have hSd : #S.1 ≤ d := (mem_filter.mp (mem_coe.mp S.2)).2
      let xS : ι → Bool := fun i ↦ decide (i ∈ S.1)
      have hwxS : weight xS = #S.1 := by
        simp only [weight, xS, decide_eq_true_eq, filter_mem_eq_inter, univ_inter]
      have hfxS : f xS = 0 := h0 xS (hwxS ▸ hSd)
      have heval : (∑ T : (B : Set (Finset ι)), c T • monomial R T.1) xS = c S := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [sum_eq_single S]
        · rw [monomial_apply, ite_eq_left (fun i hi ↦ decide_eq_true hi), mul_one]
        · intro T _ hne
          rw [monomial_apply]
          by_cases hsub : ∀ i ∈ T.1, xS i = true
          · have hTS : T.1 ⊆ S.1 := fun i hi ↦ of_decide_eq_true (hsub i hi)
            have hne_val : T.1 ≠ S.1 := fun h ↦ hne (Subtype.ext h)
            have hlt : #T.1 < m :=
              hSm ▸ card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne_val⟩)
            rw [ih #T.1 hlt T rfl, zero_mul]
          · rw [ite_eq_right hsub, mul_zero]
        · intro habs
          exact absurd (mem_univ S) habs
      rw [hcf] at heval
      exact heval.symm.trans hfxS
  rw [← hcf]
  exact sum_eq_zero fun S _ ↦ by rw [hc_zero #S.1 S rfl, zero_smul]

private def triangularCoeffs {R : Type*} [CommRing R] (g : ℕ → R) : ℕ → R
  | 0 => g 0
  | m + 1 =>
    have : ∀ r : Fin (m + 1), r.1 < m + 1 := fun r ↦ r.2
    g (m + 1) - ∑ r : Fin (m + 1), triangularCoeffs g r.1 * ((m + 1).choose r.1 : R)
termination_by m => m

private lemma sum_triangularCoeffs_choose {R : Type*} [CommRing R] (g : ℕ → R) (m : ℕ) :
    ∑ r ∈ range (m + 1), triangularCoeffs g r * (m.choose r : R) = g m := by
  cases m with
  | zero =>
    simp [triangularCoeffs]
  | succ m =>
    rw [sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
    have hdef : triangularCoeffs g (m + 1) =
        g (m + 1) - ∑ r ∈ range (m + 1), triangularCoeffs g r * ((m + 1).choose r : R) := by
      conv_lhs => unfold triangularCoeffs
      rw [Fin.sum_univ_eq_sum_range (fun r ↦ triangularCoeffs g r * ((m + 1).choose r : R))
        (m + 1)]
    rw [hdef]
    ring

/-- **Binomial basis theorem for symmetric Boolean polynomials**: every weight-symmetric function
in `Cslib.BitString.lowDegree R ι d` is an `R`-linear combination of `x ↦ (weight x).choose r`
for `0 ≤ r ≤ d`. -/
theorem IsWeightSymmetric.exists_sum_choose {R : Type*} [CommRing R] {d : ℕ}
    {f : (ι → Bool) → R} (hf_deg : f ∈ lowDegree R ι d) (hf_sym : IsWeightSymmetric f) :
    ∃ a : ℕ → R, ∀ x : ι → Bool,
      f x = ∑ r ∈ range (d + 1), a r * ((weight x).choose r : R) := by
  classical
  obtain ⟨g, hg⟩ := hf_sym.exists_eq_comp_weight
  let a := triangularCoeffs g
  let f' : (ι → Bool) → R := fun x ↦ ∑ r ∈ range (d + 1), a r * ((weight x).choose r : R)
  have hf'_deg : f' ∈ lowDegree R ι d := by
    have hfun : f' = ∑ r ∈ range (d + 1),
        a r • fun x : ι → Bool ↦ ∑ S ∈ (univ : Finset ι).powersetCard r, monomial R S x := by
      funext x
      simp only [f', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine sum_congr rfl fun r _ ↦ congrArg (a r * ·) ?_
      have hchoose := sum_powersetCard_monomial (R := R) (univ : Finset ι) r x
      simpa only [mem_univ, true_and, weight] using hchoose.symm
    rw [hfun]
    refine Submodule.sum_mem _ fun r hr ↦ Submodule.smul_mem _ (a r) ?_
    exact lowDegree_mono (Nat.lt_succ_iff.mp (mem_range.mp hr))
      (sum_powersetCard_monomial_mem_lowDegree (univ : Finset ι) r)
  have hdiff : f - f' = 0 := by
    refine eq_zero_of_mem_lowDegree_of_forall_weight_le (Submodule.sub_mem _ hf_deg hf'_deg) ?_
    intro x hx
    simp only [Pi.sub_apply, f', hg x]
    have hsplit : range (d + 1) = range (weight x + 1) ∪ Ico (weight x + 1) (d + 1) := by
      ext r
      simp only [mem_range, mem_union, mem_Ico]
      omega
    rw [hsplit, sum_union (disjoint_left.mpr fun r hr1 hr2 ↦ by
      simp only [mem_range, mem_Ico] at hr1 hr2; omega)]
    have htail : ∑ r ∈ Ico (weight x + 1) (d + 1), a r * ((weight x).choose r : R) = 0 := by
      refine sum_eq_zero fun r hr ↦ ?_
      have hgt : weight x < r := by
        have := (mem_Ico.mp hr).1
        omega
      rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, mul_zero]
    rw [htail, add_zero, sum_triangularCoeffs_choose g (weight x)]
    exact sub_self _
  refine ⟨a, fun x ↦ sub_eq_zero.mp (congrFun hdiff x)⟩

/-- **Lucas weight periodicity of binomial coefficients**: for a prime `p` and `r < p ^ δ`, the
binomial coefficient `w.choose r mod p` depends only on `w mod (p ^ δ)`. -/
theorem choose_mod_pow_prime_eq {p δ r : ℕ} (hp : p.Prime) (hr : r < p ^ δ) (w : ℕ) :
    (w % p ^ δ).choose r ≡ w.choose r [MOD p] := by
  induction δ generalizing r w with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hr
    subst hr
    simp [Nat.ModEq]
  | succ δ ih =>
    have : Fact p.Prime := ⟨hp⟩
    rw [pow_succ'] at hr ⊢
    have h1 : ((w % (p * p ^ δ)).choose r : ℤ) ≡
        ((w % (p * p ^ δ) % p).choose (r % p) *
          (w % (p * p ^ δ) / p).choose (r / p) : ℕ) [ZMOD p] := by
      simpa only [Nat.cast_mul] using
        Choose.choose_modEq_choose_mod_mul_choose_div (n := w % (p * p ^ δ)) (k := r) (p := p)
    have h2 : (w.choose r : ℤ) ≡
        ((w % p).choose (r % p) * (w / p).choose (r / p) : ℕ) [ZMOD p] := by
      simpa only [Nat.cast_mul] using
        Choose.choose_modEq_choose_mod_mul_choose_div (n := w) (k := r) (p := p)
    have hmod : w % (p * p ^ δ) % p = w % p := Nat.mod_mul_right_mod w p (p ^ δ)
    have hdiv : w % (p * p ^ δ) / p = w / p % p ^ δ := Nat.mod_mul_right_div_self w p (p ^ δ)
    have hrdiv : r / p < p ^ δ := Nat.div_lt_of_lt_mul hr
    have hih : ((w / p % p ^ δ).choose (r / p) : ℤ) ≡
        ((w / p).choose (r / p) : ℤ) [ZMOD p] :=
      Int.natCast_modEq_iff.mpr (ih hrdiv (w / p))
    rw [hmod, hdiv] at h1
    refine Int.natCast_modEq_iff.mp ?_
    refine h1.trans (Int.ModEq.trans ?_ h2.symm)
    simpa only [Nat.cast_mul] using Int.ModEq.mul_left ((w % p).choose (r % p) : ℤ) hih

/-- **Bhatnagar–Gopalan–Lipton weight periodicity**: over a commutative ring `R` of prime
characteristic `p`, any weight-symmetric function in `Cslib.BitString.lowDegree R ι d` with
`d < p ^ δ` depends only on `weight x mod (p ^ δ)`. -/
theorem IsWeightSymmetric.eq_of_weight_modEq_prime_pow {R : Type*} [CommRing R] {p : ℕ}
    [CharP R p] (hp : p.Prime) {d δ : ℕ} (hd : d < p ^ δ) {f : (ι → Bool) → R}
    (hf_deg : f ∈ lowDegree R ι d) (hf_sym : IsWeightSymmetric f) {x y : ι → Bool}
    (hw : weight x ≡ weight y [MOD p ^ δ]) :
    f x = f y := by
  obtain ⟨a, ha⟩ := hf_sym.exists_sum_choose hf_deg
  rw [ha x, ha y]
  refine sum_congr rfl fun r hr ↦ congrArg (a r * ·) ?_
  have hrd : r < p ^ δ := (Nat.lt_succ_iff.mp (mem_range.mp hr)).trans_lt hd
  have hxy : (weight x).choose r ≡ (weight y).choose r [MOD p] := by
    have hx := choose_mod_pow_prime_eq hp hrd (weight x)
    have hy := choose_mod_pow_prime_eq hp hrd (weight y)
    refine hx.symm.trans ?_
    rw [hw]
    exact hy
  wlog hle : (weight x).choose r ≤ (weight y).choose r generalizing x y
  · exact (this hw.symm hxy.symm (Nat.le_of_not_le hle)).symm
  have hdvd : p ∣ (weight y).choose r - (weight x).choose r :=
    (Nat.modEq_iff_dvd' hle).mp hxy
  have hsub : (((weight y).choose r - (weight x).choose r : ℕ) : R) = 0 :=
    (CharP.cast_eq_zero_iff R p _).mpr hdvd
  rw [Nat.cast_sub hle] at hsub
  exact (sub_eq_zero.mp hsub).symm

end WeightSymmetric

/-! ### Modular Hamming-weight equidistribution and exponential-sum correlation -/

section ModularCorrelation

variable {ι : Type*} [Fintype ι]

/-- The modular unit-circle character `x ↦ exp(i φ · weight x)` on `ι → Bool`. -/
noncomputable def modPhase (φ : ℝ) (x : ι → Bool) : ℂ :=
  Complex.exp ((φ : ℂ) * Complex.I * (weight x : ℂ))

/-- Evaluating `modPhase` at `φ = 0` gives `1`. -/
@[simp]
theorem modPhase_zero (x : ι → Bool) : modPhase 0 x = 1 := by
  simp [modPhase]

/-- Every value of `modPhase` lies on the complex unit circle (`‖modPhase φ x‖ = 1`). -/
@[simp]
theorem norm_modPhase (φ : ℝ) (x : ι → Bool) : ‖modPhase φ x‖ = 1 := by
  unfold modPhase
  have h : (φ : ℂ) * Complex.I * (weight x : ℂ) = ((φ * weight x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Explicit exponential formula `modPhase φ x = exp(i φ · weight x)`. -/
theorem modPhase_eq_exp (φ : ℝ) (x : ι → Bool) :
    modPhase φ x = Complex.exp ((φ : ℂ) * Complex.I * (weight x : ℂ)) := by
  rfl

/-- `modPhase` equals `(exp(i φ)) ^ weight x`. -/
theorem modPhase_eq_pow (φ : ℝ) (x : ι → Bool) :
    modPhase φ x = Complex.exp ((φ : ℂ) * Complex.I) ^ weight x := by
  unfold modPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

variable [DecidableEq ι]

/-- Signed modular exponential sum `𝔼 x, (-1) ^ (p x).val * modPhase φ x` of a Boolean function
`p : (ι → Bool) → ZMod 2`. -/
noncomputable def modExpSum (φ : ℝ) (p : (ι → Bool) → ZMod 2) : ℂ :=
  𝔼 x : ι → Bool, ((-1 : ℂ) ^ (p x).val) * modPhase φ x

/-- Uniform-expectation formula for `modExpSum`. -/
theorem modExpSum_eq_expect (φ : ℝ) (p : (ι → Bool) → ZMod 2) :
    modExpSum φ p = 𝔼 x : ι → Bool, ((-1 : ℂ) ^ (p x).val) * modPhase φ x := by
  rfl

/-- Correlation norm `‖modExpSum φ p‖` of `p : (ι → Bool) → ZMod 2` with `modPhase φ`. -/
noncomputable def modCorrelation (φ : ℝ) (p : (ι → Bool) → ZMod 2) : ℝ :=
  ‖modExpSum φ p‖

/-- Norm characterization `modCorrelation φ p = ‖modExpSum φ p‖`. -/
theorem modCorrelation_eq_norm (φ : ℝ) (p : (ι → Bool) → ZMod 2) :
    modCorrelation φ p = ‖modExpSum φ p‖ := by
  rfl

/-- `modCorrelation` is nonnegative. -/
theorem modCorrelation_nonneg (φ : ℝ) (p : (ι → Bool) → ZMod 2) :
    0 ≤ modCorrelation φ p := by
  exact norm_nonneg _

/-- `modCorrelation` is at most `1`. -/
theorem modCorrelation_le_one (φ : ℝ) (p : (ι → Bool) → ZMod 2) :
    modCorrelation φ p ≤ 1 := by
  unfold modCorrelation modExpSum
  rw [expect_eq_sum_div_card, norm_div, norm_natCast, card_univ]
  have hcard : (0 : ℝ) < (Fintype.card (ι → Bool) : ℝ) := by positivity
  rw [div_le_one hcard]
  refine (norm_sum_le _ _).trans_eq ?_
  calc
    ∑ x : ι → Bool, ‖((-1 : ℂ) ^ (p x).val) * modPhase φ x‖
        = ∑ _x : ι → Bool, (1 : ℝ) := by
          refine sum_congr rfl fun x _ ↦ ?_
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_modPhase]
    _ = Fintype.card (ι → Bool) := by simp

private lemma expect_pow_weight {R : Type*} [Semifield R] [CharZero R] (z : R) :
    (𝔼 x : ι → Bool, z ^ weight x) = ((1 + z) / 2) ^ Fintype.card ι := by
  classical
  have hprod : ∀ x : ι → Bool, z ^ weight x = ∏ i : ι, z ^ (x i).toNat := by
    intro x
    rw [weight_eq_sum_toNat, prod_pow_eq_pow_sum]
  simp_rw [hprod]
  rw [← Fintype.prod_expect (fun _ : ι ↦ fun b : Bool ↦ z ^ b.toNat)]
  have hcoord : ∀ _i : ι, (𝔼 b : Bool, z ^ b.toNat) = (1 + z) / 2 := fun _ ↦ by
    rw [Fintype.expect_bool]
    simp
  rw [prod_congr rfl fun i _ ↦ hcoord i, prod_const, card_univ]

private lemma norm_one_add_exp_div_two (θ : ℝ) :
    ‖(1 + Complex.exp ((θ : ℂ) * Complex.I)) / 2‖ = |Real.cos (θ / 2)| := by
  have hexp : 1 + Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp ((-((θ / 2 : ℝ)) : ℂ) * Complex.I) +
          Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have h1 : ((θ / 2 : ℝ) : ℂ) * Complex.I + (-((θ / 2 : ℝ)) : ℂ) * Complex.I = 0 := by
      push_cast; ring
    have h2 : ((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I =
        (θ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, h2, Complex.exp_zero]
  have hcos : (Complex.exp ((-((θ / 2 : ℝ)) : ℂ) * Complex.I) +
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) / 2 = (Real.cos (θ / 2) : ℂ) := by
    rw [add_comm, Complex.ofReal_cos, Complex.cos]
  have hdiv : (1 + Complex.exp ((θ : ℂ) * Complex.I)) / 2 =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * (Real.cos (θ / 2) : ℂ) := by
    rw [hexp, mul_div_assoc, hcos]
  rw [hdiv, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

private lemma abs_cos_pi_mul_le {m j : ℕ} (hm : 2 ≤ m) (hj1 : 1 ≤ j) (hj2 : j < m) :
    |Real.cos (Real.pi * j / m)| ≤ Real.cos (Real.pi / m) := by
  have hm_pos : (0 : ℝ) < m := by positivity
  by_cases hle : 2 * j ≤ m
  · have h0 : 0 ≤ Real.pi / m := by positivity
    have h1 : Real.pi / m ≤ Real.pi * j / m := by
      rw [div_le_div_iff_of_pos_right hm_pos]
      have hj_real : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      nlinarith [Real.pi_pos]
    have h2 : Real.pi * j / m ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hm_pos two_pos]
      have hle_real : (2 : ℝ) * j ≤ m := by exact_mod_cast hle
      nlinarith [Real.pi_pos]
    have hcos_nonneg : 0 ≤ Real.cos (Real.pi * j / m) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
    rw [abs_of_nonneg hcos_nonneg]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) h1
  · push Not at hle
    let j' : ℕ := m - j
    have hj'1 : 1 ≤ j' := by omega
    have h2j' : 2 * j' ≤ m := by omega
    have hrel : Real.pi * j / m = Real.pi - Real.pi * j' / m := by
      have hj_eq : (j : ℝ) = (m : ℝ) - (j' : ℝ) := by
        have : j + j' = m := by omega
        exact eq_sub_of_add_eq (by exact_mod_cast this)
      rw [hj_eq]
      field_simp
    rw [hrel, Real.cos_pi_sub, abs_neg]
    have h0 : 0 ≤ Real.pi / m := by positivity
    have h1 : Real.pi / m ≤ Real.pi * j' / m := by
      rw [div_le_div_iff_of_pos_right hm_pos]
      have hj'_real : (1 : ℝ) ≤ j' := by exact_mod_cast hj'1
      nlinarith [Real.pi_pos]
    have h2 : Real.pi * j' / m ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hm_pos two_pos]
      have hle_real : (2 : ℝ) * j' ≤ m := by exact_mod_cast h2j'
      nlinarith [Real.pi_pos]
    have hcos_nonneg : 0 ≤ Real.cos (Real.pi * j' / m) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
    rw [abs_of_nonneg hcos_nonneg]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) h1

private lemma sum_roots_of_unity_indicator {m : ℕ} (hm : 1 ≤ m) (d : ℤ) :
    (∑ j ∈ range m, Complex.exp ((2 * Real.pi * j * d / m : ℝ) * Complex.I)) =
      if (m : ℤ) ∣ d then (m : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp ((2 * Real.pi * d / m : ℝ) * Complex.I)
  have hpow : ∀ j : ℕ, Complex.exp ((2 * Real.pi * j * d / m : ℝ) * Complex.I) = ζ ^ j := by
    intro j
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hpow]
  by_cases hdvd : (m : ℤ) ∣ d
  · obtain ⟨q, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      dsimp only [ζ]
      have hm_ne : (m : ℝ) ≠ 0 := by positivity
      have hreal : 2 * Real.pi * (((m : ℤ) * q : ℤ) : ℝ) / m = (q : ℝ) * (2 * Real.pi) := by
        push_cast
        field_simp [hm_ne]
      rw [hreal]
      have hexp : (((q : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
          (q : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [hexp]
      exact Complex.exp_int_mul_two_pi_mul_I q
    rw [ite_eq_left ⟨q, rfl⟩]
    simp [hζ1]
  · rw [ite_eq_right hdvd]
    have hζ_ne : ζ ≠ 1 := by
      intro h1
      dsimp only [ζ] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨q, hq⟩ := h1
      have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      have h2pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * Real.pi ≠ 0)
      have hI_ne : Complex.I ≠ 0 := Complex.I_ne_zero
      have heq : (d : ℂ) = (m : ℂ) * (q : ℂ) := by
        have hq' : (2 * Real.pi : ℂ) * (d : ℂ) / (m : ℂ) * Complex.I =
            (q : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
          simpa [mul_assoc] using hq
        have hq'' : (2 * Real.pi : ℂ) * (d : ℂ) / (m : ℂ) = (q : ℂ) * (2 * Real.pi : ℂ) :=
          mul_right_cancel₀ hI_ne (by linear_combination hq')
        have hq''' : (2 * Real.pi : ℂ) * (d : ℂ) = (q : ℂ) * (2 * Real.pi : ℂ) * (m : ℂ) :=
          (div_eq_iff hm_ne).mp hq''
        exact mul_left_cancel₀ h2pi_ne (by linear_combination hq''')
      have heqZ : d = (m : ℤ) * q := by exact_mod_cast heq
      exact hdvd ⟨q, heqZ⟩
    have hζm : ζ ^ m = 1 := by
      dsimp only [ζ]
      rw [← Complex.exp_nat_mul]
      have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      have hexp : (m : ℂ) * (((2 * Real.pi * d / m : ℝ) : ℂ) * Complex.I) =
          (d : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp [hm_ne]
      rw [hexp]
      exact Complex.exp_int_mul_two_pi_mul_I d
    have hgeom := geom_sum_mul ζ m
    rw [hζm, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hζ_ne)

/-- **Modular Hamming-weight equidistribution**: for any `m ≥ 2` and residue `k`, the uniform
probability that `weight x ≡ k (mod m)` differs from `1 / m` by at most
`((m - 1) / m) * cos(π / m) ^ |ι|`. -/
theorem abs_expect_weight_mod_sub_inv_le {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    |(𝔼 x : ι → Bool, if weight x % m = k % m then (1 : ℝ) else 0) - (m : ℝ)⁻¹| ≤
      ((m - 1 : ℝ) / m) * Real.cos (Real.pi / m) ^ Fintype.card ι := by
  have hm1 : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < m := by positivity
  let p : ℝ := 𝔼 x : ι → Bool, if weight x % m = k % m then (1 : ℝ) else 0
  have hind : ∀ x : ι → Bool,
      ((if weight x % m = k % m then (1 : ℝ) else 0) : ℂ) =
        (m : ℂ)⁻¹ * ∑ j ∈ range m,
          Complex.exp
            ((2 * Real.pi * j * (((weight x : ℤ) - (k : ℤ) : ℤ) : ℝ) / m : ℝ) * Complex.I) := by
    intro x
    rw [sum_roots_of_unity_indicator hm1 ((weight x : ℤ) - (k : ℤ))]
    have hdvd_iff : ((m : ℤ) ∣ (weight x : ℤ) - (k : ℤ)) ↔ weight x % m = k % m := by
      rw [← Int.modEq_iff_dvd, eq_comm]
      exact Int.natCast_modEq_iff
    by_cases hmod : weight x % m = k % m
    · rw [ite_eq_left hmod, ite_eq_left (hdvd_iff.mpr hmod),
        inv_mul_cancel₀ (by exact_mod_cast hm_pos.ne'), Complex.ofReal_one]
    · rw [ite_eq_right hmod, ite_eq_right (mt hdvd_iff.mp hmod), mul_zero]
  have hp_complex : ((p - (m : ℝ)⁻¹ : ℝ) : ℂ) =
      (m : ℂ)⁻¹ * ∑ j ∈ Ico 1 m,
        Complex.exp ((-2 * Real.pi * j * k / m : ℝ) * Complex.I) *
          ((1 + Complex.exp ((2 * Real.pi * j / m : ℝ) * Complex.I)) / 2) ^ Fintype.card ι := by
    have hp_cast : (p : ℂ) = 𝔼 x : ι → Bool,
        ((if weight x % m = k % m then (1 : ℝ) else 0) : ℂ) := by
      dsimp only [p]
      rw [expect_eq_sum_div_card, expect_eq_sum_div_card]
      push_cast
      congr 1
      refine sum_congr rfl fun x _ ↦ ?_
      split_ifs <;> simp
    rw [Complex.ofReal_sub, hp_cast]
    simp_rw [hind]
    rw [← mul_expect, expect_sum_comm]
    have hsplit_range : range m = {0} ∪ Ico 1 m := by
      ext j
      simp only [mem_range, mem_union, mem_singleton, mem_Ico]
      omega
    rw [hsplit_range, sum_union (by simp), sum_singleton]
    have h0 : (𝔼 x : ι → Bool,
        Complex.exp ((2 * Real.pi * (0 : ℕ) * (((weight x : ℤ) - (k : ℤ) : ℤ) : ℝ) / m : ℝ) *
          Complex.I)) = 1 := by
      simp
    rw [h0, mul_add, mul_one, Complex.ofReal_inv, Complex.ofReal_natCast, add_sub_cancel_left]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    have hfactor : ∀ x : ι → Bool,
        Complex.exp ((2 * Real.pi * j * (((weight x : ℤ) - (k : ℤ) : ℤ) : ℝ) / m : ℝ) *
            Complex.I) =
          Complex.exp ((-2 * Real.pi * j * k / m : ℝ) * Complex.I) *
            Complex.exp ((2 * Real.pi * j / m : ℝ) * Complex.I) ^ weight x := by
      intro x
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hfactor]
    rw [← mul_expect, expect_pow_weight]
  have hnorm := congrArg (‖·‖) hp_complex
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_inv, Complex.norm_natCast] at hnorm
  rw [hnorm]
  calc
    (m : ℝ)⁻¹ * ‖∑ j ∈ Ico 1 m,
        Complex.exp ((-2 * Real.pi * j * k / m : ℝ) * Complex.I) *
          ((1 + Complex.exp ((2 * Real.pi * j / m : ℝ) * Complex.I)) / 2) ^ Fintype.card ι‖
        ≤ (m : ℝ)⁻¹ * ∑ j ∈ Ico 1 m,
            ‖Complex.exp ((-2 * Real.pi * j * k / m : ℝ) * Complex.I) *
              ((1 + Complex.exp ((2 * Real.pi * j / m : ℝ) * Complex.I)) / 2) ^
                Fintype.card ι‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ (m : ℝ)⁻¹ * ∑ _j ∈ Ico 1 m, Real.cos (Real.pi / m) ^ Fintype.card ι := by
          gcongr with j hj
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow,
            norm_one_add_exp_div_two]
          have hhalf : 2 * Real.pi * j / m / 2 = Real.pi * j / m := by ring
          rw [hhalf]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_cos_pi_mul_le hm (mem_Ico.mp hj).1 (mem_Ico.mp hj).2) _
    _ = ((m - 1 : ℝ) / m) * Real.cos (Real.pi / m) ^ Fintype.card ι := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hm1, Nat.cast_one]
          ring

/-- Convenience corollary `|ℙ[weight x ≡ k (mod m)] - 1 / m| ≤ cos(π / m) ^ |ι|` for `m ≥ 2`. -/
theorem abs_expect_weight_mod_sub_inv_le_cos_pow {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    |(𝔼 x : ι → Bool, if weight x % m = k % m then (1 : ℝ) else 0) - (m : ℝ)⁻¹| ≤
      Real.cos (Real.pi / m) ^ Fintype.card ι := by
  have hcos : 0 ≤ Real.cos (Real.pi / m) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have h0 : 0 ≤ Real.pi / m := div_nonneg Real.pi_pos.le (Nat.cast_nonneg m)
      linarith [Real.pi_pos]
    · rw [div_le_div_iff₀ (by positivity) two_pos]
      have hm_real : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [Real.pi_pos]
  refine (abs_expect_weight_mod_sub_inv_le hm k).trans ?_
  have hfrac : (m - 1 : ℝ) / m ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  exact mul_le_of_le_one_left (pow_nonneg hcos _) hfrac

/-- Strict equidistribution inequality `|ℙ[weight x ≡ k (mod m)] - 1 / m| < cos(π / m) ^ |ι|` for
`m ≥ 3`. -/
theorem abs_expect_weight_mod_sub_inv_lt_cos_pow {m : ℕ} (hm : 3 ≤ m) (k : ℕ) :
    |(𝔼 x : ι → Bool, if weight x % m = k % m then (1 : ℝ) else 0) - (m : ℝ)⁻¹| <
      Real.cos (Real.pi / m) ^ Fintype.card ι := by
  have hcos_pos : 0 < Real.cos (Real.pi / m) := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have h0 : 0 < Real.pi / m := div_pos Real.pi_pos (by positivity)
      linarith [Real.pi_pos]
    · rw [div_lt_div_iff₀ (by positivity) two_pos]
      have hm_real : (3 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [Real.pi_pos]
  refine (abs_expect_weight_mod_sub_inv_le (by omega) k).trans_lt ?_
  have hfrac : (m - 1 : ℝ) / m < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  exact mul_lt_of_lt_one_left (pow_pos hcos_pos _) hfrac

/-- **Correlation bound for symmetric polynomials against modular phase characters**: for any odd
`m ≥ 3`, `1 ≤ k < m`, `d ≥ 1`, and weight-symmetric `s ∈ Cslib.BitString.lowDegree (ZMod 2) ι d`,
`modCorrelation (2π k / m) s ≤ 2 m d * cos(π / (2 m d)) ^ |ι|`. -/
theorem modCorrelation_symmetric_le {m k d : ℕ} (hm_odd : Odd m) (hk1 : 1 ≤ k) (hkm : k < m)
    (hd : 1 ≤ d) {s : (ι → Bool) → ZMod 2} (hs_deg : s ∈ lowDegree (ZMod 2) ι d)
    (hs_sym : IsWeightSymmetric s) :
    modCorrelation (2 * Real.pi * k / m) s ≤
      2 * m * d * Real.cos (Real.pi / (2 * m * d)) ^ Fintype.card ι := by
  have hm3 : 3 ≤ m := by
    rcases hm_odd with ⟨q, rfl⟩
    omega
  let δ : ℕ := Nat.log 2 d + 1
  let Q : ℕ := 2 ^ δ
  have hd_lt_Q : d < Q := Nat.lt_pow_succ_log_self (by decide) d
  have hQ_pos : 1 ≤ Q := Nat.one_le_pow δ 2 (by decide)
  have hQ_le_2d : Q ≤ 2 * d := by
    dsimp only [Q, δ]
    rw [pow_succ']
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  -- Step 1: By Lucas weight periodicity, `s x` depends only on `weight x % Q`.
  have hperiod : ∀ x y : ι → Bool, weight x % Q = weight y % Q → s x = s y := fun x y hmod ↦
    hs_sym.eq_of_weight_modEq_prime_pow Nat.prime_two hd_lt_Q hs_deg hmod
  -- Choose canonical sign representative `c i : ℂ` for each residue `i < Q`.
  classical
  let c : ℕ → ℂ := fun i ↦
    if hex : ∃ x : ι → Bool, weight x % Q = i then (-1 : ℂ) ^ (s hex.choose).val else 1
  have hc_norm : ∀ i : ℕ, ‖c i‖ = 1 := by
    intro i
    dsimp only [c]
    split_ifs with hex
    · rw [norm_pow, norm_neg, norm_one, one_pow]
    · exact norm_one
  have hs_eq_sum : ∀ x : ι → Bool,
      ((-1 : ℂ) ^ (s x).val) * modPhase (2 * Real.pi * k / m) x =
        ∑ i ∈ range Q, c i *
          (if weight x % Q = i then modPhase (2 * Real.pi * k / m) x else 0) := by
    intro x
    have hi_mem : weight x % Q ∈ range Q := mem_range.mpr (Nat.mod_lt _ hQ_pos)
    rw [sum_eq_single (weight x % Q)]
    · rw [ite_eq_left rfl]
      have hex : ∃ y : ι → Bool, weight y % Q = weight x % Q := ⟨x, rfl⟩
      have hci : c (weight x % Q) = (-1 : ℂ) ^ (s x).val := by
        dsimp only [c]
        rw [dite_eq_left hex, hperiod hex.choose x hex.choose_spec]
      rw [hci]
    · intro b _ hb
      rw [ite_eq_right (Ne.symm hb), mul_zero]
    · intro hnot
      exact absurd hi_mem hnot
  -- Step 2: Bound each residue slice mod `Q` by decomposing into `m` residue classes mod `m * Q`.
  let φ : ℝ := 2 * Real.pi * k / m
  have hslice_bound : ∀ i ∈ range Q,
      ‖𝔼 x : ι → Bool, if weight x % Q = i then modPhase φ x else (0 : ℂ)‖ ≤
        (m : ℝ) * Real.cos (Real.pi / (m * Q)) ^ Fintype.card ι := by
    intro i hi
    have hiQ : i < Q := mem_range.mp hi
    have hmQ2 : 2 ≤ m * Q := by nlinarith
    -- Partition `weight x % Q = i` into `weight x % (m * Q) = i + j * Q` for `j ∈ range m`.
    have hpart : ∀ x : ι → Bool,
        (if weight x % Q = i then modPhase φ x else (0 : ℂ)) =
          ∑ j ∈ range m,
            Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
              ((if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) : ℂ) := by
      intro x
      by_cases hxQ : weight x % Q = i
      · rw [ite_eq_left hxQ]
        let j₀ : ℕ := weight x / Q % m
        have hj₀_mem : j₀ ∈ range m := mem_range.mpr (Nat.mod_lt _ (by omega))
        have hx_mQ : weight x % (m * Q) = i + j₀ * Q := by
          have hdivmod := Nat.mod_add_div (weight x) (m * Q)
          have hdivQ := Nat.mod_add_div (weight x) Q
          have hrem : weight x % (m * Q) < m * Q := Nat.mod_lt _ (by positivity)
          have hq : weight x % (m * Q) % Q = i := by
            rw [Nat.mod_mul_left_mod, hxQ]
          have hd : weight x % (m * Q) / Q = j₀ := by
            dsimp only [j₀]
            rw [mul_comm m Q, Nat.mod_mul_right_div_self]
          have hrecon := Nat.mod_add_div (weight x % (m * Q)) Q
          rw [hq, hd, mul_comm Q j₀] at hrecon
          exact hrecon.symm
        rw [sum_eq_single j₀]
        · simp only [hx_mQ, ↓reduceIte, Complex.ofReal_one, mul_one]
          unfold modPhase
          -- Both phases equal `exp(2π i * weight x * k / m)` since `weight x ≡ i + j₀ * Q (mod m)`.
          obtain ⟨q, hq⟩ : m * Q ∣ weight x - weight x % (m * Q) :=
            Nat.dvd_sub_mod (weight x)
          have hw_eq : weight x = i + j₀ * Q + m * Q * q := by
            have hle : weight x % (m * Q) ≤ weight x := Nat.mod_le _ _
            omega
          have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
          have hexp_diff :
              ((φ : ℂ) * Complex.I * (weight x : ℂ)) =
                ((2 * Real.pi * (i + j₀ * Q : ℕ) * k / m : ℝ) * Complex.I) +
                  ((Q * q * k : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
            dsimp only [φ]
            rw [hw_eq]
            push_cast
            field_simp [hm_ne]
          rw [hexp_diff, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
        · intro j _ hj
          have hne : weight x % (m * Q) ≠ i + j * Q := by
            rw [hx_mQ]
            intro heq
            apply hj
            have hmul : j * Q = j₀ * Q := by omega
            exact Nat.eq_of_mul_eq_mul_right hQ_pos hmul
          simp [hne]
        · intro hnot
          exact absurd hj₀_mem hnot
      · rw [ite_eq_right hxQ]
        symm
        refine sum_eq_zero fun j _ ↦ ?_
        have hne : weight x % (m * Q) ≠ i + j * Q := by
          intro heq
          apply hxQ
          have hq : weight x % (m * Q) % Q = weight x % Q := Nat.mod_mul_left_mod (weight x) m Q
          rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiQ] at hq
          exact hq.symm
        simp [hne]
    simp_rw [hpart]
    rw [expect_sum_comm]
    have hexp_pull :
        (∑ j ∈ range m, 𝔼 x : ι → Bool,
            Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
              ((if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) : ℂ)) =
          ∑ j ∈ range m,
            Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
              (((𝔼 x : ι → Bool,
                  if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) -
                ((m * Q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
      -- Because `∑ j ∈ range m, exp(2π i (i + j Q) k / m) = 0` (`gcd(m, Q) = 1` and `1 ≤ k < m`).
      have hcoprime : Nat.Coprime m Q :=
        hm_odd.coprime_two_right.pow_right δ
      have hnot_dvd : ¬ (m : ℤ) ∣ ((Q * k : ℕ) : ℤ) := by
        intro hdvd
        have hdvd_nat : m ∣ Q * k := Int.natCast_dvd_natCast.mp hdvd
        have hmk : m ∣ k := hcoprime.dvd_of_dvd_mul_left hdvd_nat
        exact Nat.not_lt.mpr (Nat.le_of_dvd (by omega) hmk) hkm
      have hzero_sum :
          ∑ j ∈ range m,
            Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) = 0 := by
        have hfactor_i : ∀ j : ℕ,
            Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) =
              Complex.exp ((2 * Real.pi * i * k / m : ℝ) * Complex.I) *
                Complex.exp ((2 * Real.pi * j * ((Q * k : ℕ) : ℤ) / m : ℝ) * Complex.I) := by
          intro j
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        simp_rw [hfactor_i]
        rw [← mul_sum, sum_roots_of_unity_indicator (by omega) ((Q * k : ℕ) : ℤ),
          ite_eq_right hnot_dvd, mul_zero]
      calc
        ∑ j ∈ range m, 𝔼 x : ι → Bool,
            Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
              ((if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) : ℂ)
            = ∑ j ∈ range m,
                Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
                  ((𝔼 x : ι → Bool,
                      if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0 : ℝ) : ℂ) := by
              refine sum_congr rfl fun j _ ↦ ?_
              rw [← mul_expect]
              congr 1
              rw [expect_eq_sum_div_card, expect_eq_sum_div_card]
              push_cast
              congr 1
              refine sum_congr rfl fun x _ ↦ ?_
              split_ifs <;> simp
        _ = (∑ j ∈ range m,
              Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
                (((𝔼 x : ι → Bool,
                    if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) -
                  ((m * Q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) +
            ((m * Q : ℕ) : ℂ)⁻¹ *
              ∑ j ∈ range m,
                Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) := by
              rw [mul_sum, ← sum_add_distrib]
              refine sum_congr rfl fun j _ ↦ ?_
              push_cast
              ring
        _ = _ := by rw [hzero_sum, mul_zero, add_zero]
    rw [hexp_pull]
    calc
      ‖∑ j ∈ range m,
          Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
            (((𝔼 x : ι → Bool,
                if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) -
              ((m * Q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)‖
          ≤ ∑ j ∈ range m,
              ‖Complex.exp ((2 * Real.pi * (i + j * Q : ℕ) * k / m : ℝ) * Complex.I) *
                (((𝔼 x : ι → Bool,
                    if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) -
                  ((m * Q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range m, Real.cos (Real.pi / (m * Q)) ^ Fintype.card ι := by
            refine sum_le_sum fun j hj ↦ ?_
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
              Real.norm_eq_abs]
            have hij_lt : i + j * Q < m * Q := by
              have hj_lt : j < m := mem_range.mp hj
              have hj_le : j + 1 ≤ m := hj_lt
              calc
                i + j * Q < Q + j * Q := Nat.add_lt_add_right hiQ _
                _ = (j + 1) * Q := by ring
                _ ≤ m * Q := Nat.mul_le_mul_right Q hj_le
            have hmod_self : (i + j * Q) % (m * Q) = i + j * Q := Nat.mod_eq_of_lt hij_lt
            have heq_prob :
                (𝔼 x : ι → Bool, if weight x % (m * Q) = i + j * Q then (1 : ℝ) else 0) =
                  𝔼 x : ι → Bool,
                    if weight x % (m * Q) = (i + j * Q) % (m * Q) then (1 : ℝ) else 0 := by
              simp_rw [hmod_self]
            rw [heq_prob]
            simpa only [Nat.cast_mul] using
              abs_expect_weight_mod_sub_inv_le_cos_pow (ι := ι) hmQ2 (i + j * Q)
      _ = (m : ℝ) * Real.cos (Real.pi / (m * Q)) ^ Fintype.card ι := by
            rw [sum_const, card_range, nsmul_eq_mul]
  -- Step 3: Sum over the `Q ≤ 2 * d` residue slices and apply cosine monotonicity.
  unfold modCorrelation modExpSum
  simp_rw [hs_eq_sum, expect_sum_comm, ← mul_expect]
  dsimp only [φ] at hslice_bound
  calc
    ‖∑ i ∈ range Q, c i * 𝔼 x : ι → Bool,
        if weight x % Q = i then modPhase (2 * Real.pi * k / m) x else 0‖
        ≤ ∑ i ∈ range Q, ‖c i * 𝔼 x : ι → Bool,
            if weight x % Q = i then modPhase (2 * Real.pi * k / m) x else 0‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _i ∈ range Q, (m : ℝ) * Real.cos (Real.pi / (m * Q)) ^ Fintype.card ι := by
          refine sum_le_sum fun i hi ↦ ?_
          rw [norm_mul, hc_norm i, one_mul]
          exact hslice_bound i hi
    _ = (m * Q : ℝ) * Real.cos (Real.pi / (m * Q)) ^ Fintype.card ι := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
    _ ≤ 2 * m * d * Real.cos (Real.pi / (2 * m * d)) ^ Fintype.card ι := by
          have hmQ_le : (m * Q : ℝ) ≤ 2 * m * d := by
            have : m * Q ≤ m * (2 * d) := Nat.mul_le_mul_left m hQ_le_2d
            have : (m : ℝ) * (Q : ℝ) ≤ (m : ℝ) * (2 * (d : ℝ)) := by exact_mod_cast this
            linarith
          have hcos_nonneg : 0 ≤ Real.cos (Real.pi / (m * Q)) := by
            refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
            · have h0 : 0 ≤ Real.pi / ((m : ℝ) * Q) :=
                div_nonneg Real.pi_pos.le (by positivity)
              linarith [Real.pi_pos]
            · rw [div_le_div_iff₀ (by positivity) two_pos]
              have hmQ_real : (3 : ℝ) ≤ (m : ℝ) * (Q : ℝ) := by
                have : 3 ≤ m * Q := by nlinarith
                exact_mod_cast this
              nlinarith [Real.pi_pos]
          have hcos_mono : Real.cos (Real.pi / (m * Q)) ≤ Real.cos (Real.pi / (2 * m * d)) := by
            refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
            · have hmQ_real : (3 : ℝ) ≤ (m : ℝ) * (Q : ℝ) := by
                have : 3 ≤ m * Q := by nlinarith
                exact_mod_cast this
              rw [div_le_iff₀ (by positivity)]
              nlinarith [Real.pi_pos]
            · exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hmQ_le
          exact mul_le_mul hmQ_le (pow_le_pow_left₀ hcos_nonneg hcos_mono _)
            (pow_nonneg hcos_nonneg _) (by positivity)

end ModularCorrelation

/-! ### Subcube local correlation and its Fourier Parseval identity -/

section LocalCorrelation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mean squared deviation of the subcube conditional expectation `𝔼_{y}[F(S.piecewise y x)]`
from the global expectation `𝔼[F]`.
-/
noncomputable def localCorrelation (S : Finset ι) (F : (ι → Bool) → ℝ) : ℝ :=
  𝔼 x : ι → Bool, ((𝔼 y : ι → Bool, F (S.piecewise y x)) - 𝔼 z : ι → Bool, F z) ^ 2

/-- Expectation-of-squared-deviation formula for `localCorrelation`. -/
theorem localCorrelation_eq_expect (S : Finset ι) (F : (ι → Bool) → ℝ) :
    localCorrelation S F =
      𝔼 x : ι → Bool, ((𝔼 y : ι → Bool, F (S.piecewise y x)) - 𝔼 z : ι → Bool, F z) ^ 2 := by
  rfl

/-- Local correlation is nonnegative. -/
theorem localCorrelation_nonneg (S : Finset ι) (F : (ι → Bool) → ℝ) :
    0 ≤ localCorrelation S F := by
  exact expect_nonneg fun _ _ ↦ sq_nonneg _

/-- When `S = univ`, every subcube average equals `𝔼[F]`, so `localCorrelation univ F = 0`. -/
@[simp]
theorem localCorrelation_univ (F : (ι → Bool) → ℝ) :
    localCorrelation univ F = 0 := by
  unfold localCorrelation
  have hpw : ∀ x y : ι → Bool, (univ : Finset ι).piecewise y x = y := fun x y ↦ by
    funext i
    simp [Finset.piecewise]
  simp_rw [hpw, sub_self, zero_pow (by decide : 2 ≠ 0), expect_const_zero]

private lemma expect_piecewise_chi (S T : Finset ι) (x : ι → Bool) :
    (𝔼 y : ι → Bool, chi ℝ T (S.piecewise y x)) = if Disjoint T S then chi ℝ T x else 0 := by
  have hsplit : ∀ y : ι → Bool,
      chi ℝ T (S.piecewise y x) = chi ℝ (T ∩ S) y * chi ℝ (T \ S) x := by
    intro y
    rw [chi_eq_prod_signVal, chi_eq_prod_signVal, chi_eq_prod_signVal,
      ← prod_inter_mul_prod_sdiff T S]
    congr 1
    · refine prod_congr rfl fun i hi ↦ ?_
      rw [Finset.piecewise_eq_of_mem _ _ _ (mem_inter.mp hi).2]
    · refine prod_congr rfl fun i hi ↦ ?_
      rw [Finset.piecewise_eq_of_notMem _ _ _ (mem_sdiff.mp hi).2]
  simp_rw [hsplit]
  rw [← expect_mul, expect_chi]
  by_cases hdisj : Disjoint T S
  · have hempty : T ∩ S = ∅ := disjoint_iff_inter_eq_empty.mp hdisj
    have hsdiff : T \ S = T := sdiff_eq_self_of_disjoint hdisj
    rw [ite_eq_left hempty, ite_eq_left hdisj, hsdiff, one_mul]
  · have hne : T ∩ S ≠ ∅ := mt disjoint_iff_inter_eq_empty.mpr hdisj
    rw [ite_eq_right hne, ite_eq_right hdisj, zero_mul]

/-- **Fourier Parseval identity for local correlation**: `localCorrelation S F` equals the sum of
squared Fourier coefficients `fourierCoeff F T ^ 2` over all nonempty `T` disjoint from `S`. -/
theorem localCorrelation_eq_sum_fourierCoeff_sq (S : Finset ι) (F : (ι → Bool) → ℝ) :
    localCorrelation S F =
      ∑ T : Finset ι with T ≠ ∅ ∧ Disjoint T S, fourierCoeff F T ^ 2 := by
  let G : (ι → Bool) → ℝ := fun x ↦ (𝔼 y : ι → Bool, F (S.piecewise y x)) - 𝔼 z : ι → Bool, F z
  have hG_fourier : ∀ x : ι → Bool,
      G x = ∑ T : Finset ι,
        (if T ≠ ∅ ∧ Disjoint T S then fourierCoeff F T else 0) * chi ℝ T x := by
    intro x
    dsimp only [G]
    have hF_exp : ∀ w : ι → Bool, F w = ∑ T : Finset ι, fourierCoeff F T * chi ℝ T w :=
      fun w ↦ (sum_fourierCoeff_mul_chi F w).symm
    conv_lhs =>
      lhs
      arg 2
      ext y
      rw [hF_exp (S.piecewise y x)]
    rw [expect_sum_comm]
    simp_rw [← mul_expect, expect_piecewise_chi, ← fourierCoeff_empty F]
    have hsplit_empty : (univ : Finset (Finset ι)) = {∅} ∪ univ.erase ∅ := by
      ext T
      simp
    rw [hsplit_empty, sum_union (by simp), sum_singleton]
    simp only [disjoint_empty_left, ↓reduceIte, chi_empty, mul_one, add_sub_cancel_left]
    rw [sum_union (by simp), sum_singleton]
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_mul, zero_add]
    refine sum_congr rfl fun T hT ↦ ?_
    have hTne : T ≠ ∅ := ne_of_mem_erase hT
    by_cases hdisj : Disjoint T S
    · simp [hTne, hdisj]
    · simp [hTne, hdisj]
  have hcoeff : ∀ T : Finset ι,
      fourierCoeff G T = if T ≠ ∅ ∧ Disjoint T S then fourierCoeff F T else 0 := by
    intro T
    have hG_eq : G = fun x ↦ ∑ U : Finset ι,
        (if U ≠ ∅ ∧ Disjoint U S then fourierCoeff F U else 0) * chi ℝ U x :=
      funext hG_fourier
    rw [hG_eq, fourierCoeff_sum_mul_chi]
  unfold localCorrelation
  change (𝔼 x : ι → Bool, G x ^ 2) = _
  rw [expect_sq_eq_sum_fourierCoeff_sq, sum_filter]
  refine sum_congr rfl fun T _ ↦ ?_
  rw [hcoeff T]
  split_ifs <;> simp

/-- Enlarging `S` can only decrease `localCorrelation S F`. -/
theorem localCorrelation_anti {S₁ S₂ : Finset ι} (hS : S₁ ⊆ S₂) (F : (ι → Bool) → ℝ) :
    localCorrelation S₂ F ≤ localCorrelation S₁ F := by
  rw [localCorrelation_eq_sum_fourierCoeff_sq, localCorrelation_eq_sum_fourierCoeff_sq]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ sq_nonneg _)
  intro T hT
  rw [mem_filter] at hT ⊢
  exact ⟨hT.1, hT.2.1, hT.2.2.mono_right hS⟩

/-- For any Boolean sign function `x ↦ signVal (f x)`, `localCorrelation S` is at most `1`. -/
theorem localCorrelation_signVal_le_one (S : Finset ι) (f : (ι → Bool) → Bool) :
    localCorrelation S (fun x ↦ signVal (f x)) ≤ 1 := by
  rw [localCorrelation_eq_sum_fourierCoeff_sq]
  exact sum_fourierCoeff_sq_signVal_le_one f _

-- Non-degenerate sanity check on `Fin 3` and odd modulus `m = 3`.
example : modCorrelation (2 * Real.pi * 1 / 3) (fun _ : Fin 3 → Bool ↦ (0 : ZMod 2)) ≤
    2 * (3 : ℝ) * 1 * Real.cos (Real.pi / (2 * 3 * 1)) ^ Fintype.card (Fin 3) := by
  simpa using modCorrelation_symmetric_le (ι := Fin 3) (m := 3) (k := 1) (d := 1) ⟨1, by ring⟩
    (by omega) (by omega) (by omega) (const_mem_lowDegree 1 0) (isWeightSymmetric_const 0)

end LocalCorrelation

end CslibFrontier.Foundations.BooleanAnalysis
