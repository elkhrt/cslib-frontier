/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import Cslib.Probability.PMF
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import CslibFrontier.Foundations.Data.BitString.ZModSpace
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Shearer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Entropic Chang Inequality, Basis Bounds, and Dimension Bounds

For a subset `A` of the Boolean cube `ι → Bool` with density `α = |A| / 2 ^ |ι|` and indicator
function `1_A`, subadditivity of Shannon entropy yields sharp upper bounds on Fourier weights over
arbitrary `𝔽₂`-bases, a dimension bound on the span of large Fourier characters (Chang's lemma),
weight-`k` averaging bounds, and a refined inequality for highly biased coordinates.

## Main definitions

* `Cslib.BitString.zmodSupport`: support subset `{i : ι | v i ≠ 0}` of a vector `v : ι → ZMod 2`.
* `Cslib.BitString.finsetIndicatorZMod`: indicator vector in `ι → ZMod 2` of a `Finset ι`.
* `Cslib.BitString.largeFourierChars`: set `{v : ι → ZMod 2 | ρ * α < |f̂(S_v)|}` of characters
  with large Fourier coefficient relative to `α`.

## Main results

* `Cslib.BitString.hasSum_binEntropy_taylor`: Taylor series expansion of
  `Real.log 2 - Real.binEntropy ((1 + x) / 2)` for `|x| ≤ 1`.
* `Cslib.BitString.binEntropy_one_add_div_two_le`: quadratic upper bound
  `Real.binEntropy ((1 + x) / 2) ≤ Real.log 2 - x ^ 2 / 2` for `|x| ≤ 1`.
* `Cslib.BitString.binEntropy_le_mul_one_sub_log`,
  `Cslib.BitString.binEntropy_one_add_div_two_le_biased`: upper bounds tight near the boundary.
* `Cslib.BitString.sum_fourierCoeff_sq_basis_le`,
  `Cslib.BitString.sum_fourierCoeff_sq_linearIndependent_le`: Chang's inequality over any
  `ZMod 2`-basis or finite linearly independent family of characters.
* `Cslib.BitString.finrank_span_largeFourierChars_lt`,
  `Cslib.BitString.finrank_span_largeFourierChars_le`: Chang's dimension bound on the
  `𝔽₂`-subspace spanned by characters with `|f̂(S)| > ρ α`.
* `Cslib.BitString.exists_weight_k_basis_iff`: exact characterization of Hamming weights `k`
  for which `𝔽₂^n` admits a basis of weight-`k` vectors.
* `Cslib.BitString.levelWeight_indicator_le_of_odd`,
  `Cslib.BitString.levelWeight_indicator_le_of_even`,
  `Cslib.BitString.levelWeight_indicator_le_two_mul_pow_div_factorial`: level-`k` Fourier weight
  bounds via permutation averaging over linearly independent weight-`k` families.
* `Cslib.BitString.log_card_le_sum_biased_margin`,
  `Cslib.BitString.log_card_le_sum_biased_margin_basis`: biased entropic bound
  `log |A| ≤ ∑ δ_i (1 - log δ_i)` with `δ_i = (1 - |f̂(S_i)| / α) / 2`.
-/

public section

open Finset Real Cslib Cslib.Probability.PMF
open scoped BigOperators Topology

namespace Cslib.BitString

/-! ### Analytic binary entropy bounds -/

section EntropyBounds

open Filter

private theorem sum_range_pow_div_mul_eq (x : ℝ) (N : ℕ) :
    ∑ m ∈ range N, x ^ (m + 2) / ((m + 2 : ℝ) * (m + 1)) =
      x + (x - 1) * (∑ m ∈ range N, x ^ (m + 1) / (m + 1 : ℝ)) -
        x ^ (N + 1) / (N + 1 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp [h1, h2]
    ring

private theorem hasSum_pow_div_mul_add_one {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ ↦ x ^ (m + 2) / ((m + 2 : ℝ) * (m + 1)))
      (x + (1 - x) * log (1 - x)) := by
  have hlog := hasSum_pow_div_log_of_abs_lt_one hx
  have hsum : Summable (fun m : ℕ ↦ x ^ (m + 2) / ((m + 2 : ℝ) * (m + 1))) := by
    refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg x) hx) fun m ↦ ?_
    have hpos : (0 : ℝ) < (m + 2 : ℝ) * (m + 1) := by positivity
    have hden : (1 : ℝ) ≤ (m + 2 : ℝ) * (m + 1) := by nlinarith
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
    calc |x| ^ (m + 2) / ((m + 2 : ℝ) * (m + 1))
        ≤ |x| ^ (m + 2) / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one hden
      _ = |x| ^ m * |x| ^ 2 := by rw [div_one, pow_add]
      _ ≤ |x| ^ m * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (abs_nonneg x) hx.le) (by positivity)
      _ = |x| ^ m := mul_one _
  rw [hsum.hasSum_iff_tendsto_nat]
  simp_rw [sum_range_pow_div_mul_eq]
  have htail : Tendsto (fun N : ℕ ↦ x ^ (N + 1) / (N + 1 : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N ↦ ?_)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg x) hx).comp (tendsto_add_atTop_nat 1))
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
    exact div_le_self (by positivity) (by linarith : (1 : ℝ) ≤ (N : ℝ) + 1)
  have ht := ((tendsto_const_nhds (x := x)).add
    ((tendsto_const_nhds (x := x - 1)).mul hlog.tendsto_sum_nat)).sub htail
  have hlim_eq : x + (x - 1) * -log (1 - x) - 0 = x + (1 - x) * log (1 - x) := by ring
  simpa only [hlim_eq] using ht

private theorem log_two_sub_binEntropy_eq {x : ℝ} (hx : |x| < 1) :
    log 2 - binEntropy ((1 + x) / 2) =
      ((1 + x) * log (1 + x) + (1 - x) * log (1 - x)) / 2 := by
  have h1px : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have h1mx : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have hsub : 1 - (1 + x) / 2 = (1 - x) / 2 := by ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, hsub, negMulLog, negMulLog,
    log_div h1px.ne' two_ne_zero, log_div h1mx.ne' two_ne_zero]
  ring

private theorem hasSum_binEntropy_taylor_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ ↦ x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1)))
      (log 2 - binEntropy ((1 + x) / 2)) := by
  have hpos := hasSum_pow_div_mul_add_one hx
  have hneg := hasSum_pow_div_mul_add_one (x := -x) (by rwa [abs_neg])
  have havg := (hpos.add hneg).div_const 2
  set term : ℕ → ℝ := fun m ↦
    (x ^ (m + 2) / ((m + 2 : ℝ) * (m + 1)) + (-x) ^ (m + 2) / ((m + 2 : ℝ) * (m + 1))) / 2
  have htarget :
      (x + (1 - x) * log (1 - x) + (-x + (1 - -x) * log (1 - -x))) / 2 =
        log 2 - binEntropy ((1 + x) / 2) := by
    rw [log_two_sub_binEntropy_eq hx]
    ring_nf
  rw [htarget] at havg
  have hcomp : term ∘ (2 * ·) =
      fun k : ℕ ↦ x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1)) := by
    funext k
    dsimp only [term, Function.comp_apply]
    have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
    rw [hev.neg_pow]
    push_cast
    ring
  rw [← hcomp, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · exact havg
  · intro m hm
    rw [Set.mem_range] at hm
    have hodd : Odd (m + 2) := by
      rcases Nat.even_or_odd m with ⟨k, rfl⟩ | hodd
      · exact absurd ⟨k, by omega⟩ hm
      · obtain ⟨k, rfl⟩ := hodd
        exact ⟨k + 1, by omega⟩
    dsimp only [term]
    rw [hodd.neg_pow]
    ring

private theorem summable_inv_two_mul_add_two_mul :
    Summable (fun k : ℕ ↦ (1 : ℝ) / ((2 * k + 2 : ℝ) * (2 * k + 1))) := by
  refine summable_of_sum_range_le (c := 1) (fun k ↦ by positivity) fun N ↦ ?_
  have hle : ∀ k : ℕ, (1 : ℝ) / ((2 * k + 2 : ℝ) * (2 * k + 1)) ≤
      1 / (k + 1 : ℝ) - 1 / (k + 2 : ℝ) := fun k ↦ by
    have h1 : (0 : ℝ) < k + 1 := by positivity
    have h2 : (0 : ℝ) < k + 2 := by positivity
    have h3 : (0 : ℝ) < 2 * k + 1 := by positivity
    have h4 : (0 : ℝ) < 2 * k + 2 := by positivity
    rw [div_sub_div _ _ h1.ne' h2.ne', one_mul, mul_one,
      show (k : ℝ) + 2 - (k + 1) = 1 by ring]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc ∑ k ∈ range N, (1 : ℝ) / ((2 * k + 2 : ℝ) * (2 * k + 1))
      ≤ ∑ k ∈ range N, (1 / (k + 1 : ℝ) - 1 / (k + 2 : ℝ)) := sum_le_sum fun k _ ↦ hle k
    _ = 1 - 1 / (N + 1 : ℝ) := by
        induction N with
        | zero => simp
        | succ N ih =>
          rw [sum_range_succ, ih]
          push_cast
          ring
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ 1 / (N + 1 : ℝ) := by positivity
        linarith

private theorem hasSum_inv_two_mul_add_two_mul :
    HasSum (fun k : ℕ ↦ (1 : ℝ) / ((2 * k + 2 : ℝ) * (2 * k + 1))) (log 2) := by
  set c : ℕ → ℝ := fun k ↦ (1 : ℝ) / ((2 * k + 2 : ℝ) * (2 * k + 1))
  have hc_sum : Summable c := summable_inv_two_mul_add_two_mul
  have hge : log 2 ≤ ∑' k, c k := by
    have hlim : Tendsto (fun x : ℝ ↦ log 2 - binEntropy ((1 + x) / 2)) (𝓝[<] 1) (𝓝 (log 2)) := by
      have hcont : Continuous (fun x : ℝ ↦ log 2 - binEntropy ((1 + x) / 2)) :=
        continuous_const.sub (binEntropy_continuous.comp (by fun_prop))
      have hval : log 2 - binEntropy ((1 + (1 : ℝ)) / 2) = log 2 := by norm_num
      have ht := (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      rwa [hval] at ht
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have habs : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
    have hhas := hasSum_binEntropy_taylor_of_abs_lt_one habs
    rw [← hhas.tsum_eq]
    refine hhas.summable.tsum_le_tsum (fun k ↦ ?_) hc_sum
    have hpow : x ^ (2 * k + 2) ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
    exact div_le_div_of_nonneg_right hpow (by positivity)
  have hle : ∑' k, c k ≤ log 2 := by
    refine hc_sum.tsum_le_of_sum_range_le fun N ↦ ?_
    have hlim : Tendsto
        (fun x : ℝ ↦ ∑ k ∈ range N, x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1)))
        (𝓝[<] 1) (𝓝 (∑ k ∈ range N, c k)) := by
      have hcont : Continuous
          (fun x : ℝ ↦ ∑ k ∈ range N, x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1))) := by
        fun_prop
      have hval :
          (∑ k ∈ range N, (1 : ℝ) ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1))) =
            ∑ k ∈ range N, c k := by
        simp [c]
      have ht := (hcont.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      rwa [hval] at ht
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have habs : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
    have hhas := hasSum_binEntropy_taylor_of_abs_lt_one habs
    have hpart : ∑ k ∈ range N, x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1)) ≤
        log 2 - binEntropy ((1 + x) / 2) := by
      rw [← hhas.tsum_eq]
      exact hhas.summable.sum_le_tsum (range N) fun k _ ↦ by
        have : 0 ≤ x ^ (2 * k + 2) := pow_nonneg hx.1.le _
        positivity
    have hbent : 0 ≤ binEntropy ((1 + x) / 2) :=
      binEntropy_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  have heq : ∑' k, c k = log 2 := le_antisymm hle hge
  exact heq ▸ hc_sum.hasSum

/-- **Taylor series expansion of binary entropy around `1 / 2`**: for `|x| ≤ 1`,
`Real.log 2 - Real.binEntropy ((1 + x) / 2) = ∑' k, x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 1))`.
-/
theorem hasSum_binEntropy_taylor {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ ↦ x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1)))
      (log 2 - binEntropy ((1 + x) / 2)) := by
  rcases hx.eq_or_lt with h1 | hlt
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl
    · simpa using hasSum_inv_two_mul_add_two_mul
    · have hpow : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 2) = 1 := fun k ↦
        Even.neg_one_pow ⟨k + 1, by ring⟩
      simpa [hpow] using hasSum_inv_two_mul_add_two_mul
  · exact hasSum_binEntropy_taylor_of_abs_lt_one hlt

/-- **Quadratic upper bound on binary entropy**: for `|x| ≤ 1`,
`Real.binEntropy ((1 + x) / 2) ≤ Real.log 2 - x ^ 2 / 2`. -/
theorem binEntropy_one_add_div_two_le {x : ℝ} (hx : |x| ≤ 1) :
    binEntropy ((1 + x) / 2) ≤ log 2 - x ^ 2 / 2 := by
  have hhas := hasSum_binEntropy_taylor hx
  have hnonneg : ∀ k : ℕ, 0 ≤ x ^ (2 * k + 2) / ((2 * k + 2 : ℝ) * (2 * k + 1)) := fun k ↦ by
    have hsq : x ^ (2 * k + 2) = (x ^ (k + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
    rw [hsq]
    positivity
  have h0 : x ^ 2 / 2 ≤ log 2 - binEntropy ((1 + x) / 2) := by
    have hle := hhas.summable.le_tsum 0 fun k _ ↦ hnonneg k
    rw [hhas.tsum_eq] at hle
    simpa using hle
  linarith

/-- **Biased upper bound on binary entropy**: for `p ≤ 1`,
`Real.binEntropy p ≤ p * (1 - Real.log p)`. -/
theorem binEntropy_le_mul_one_sub_log {p : ℝ} (hp1 : p ≤ 1) :
    binEntropy p ≤ p * (1 - log p) := by
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp
  have hq : 0 < 1 - p := sub_pos.mpr hp1'
  have hlog : log (1 - p)⁻¹ ≤ (1 - p)⁻¹ - 1 := log_le_sub_one_of_pos (inv_pos.mpr hq)
  have hmul := mul_le_mul_of_nonneg_left hlog hq.le
  rw [mul_sub, mul_inv_cancel₀ hq.ne', mul_one, sub_sub_cancel, log_inv, mul_neg] at hmul
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
  linarith

/-- **Symmetric biased upper bound on binary entropy**: for any `x : ℝ`,
`Real.binEntropy ((1 + x) / 2) ≤ ((1 - |x|) / 2) * (1 - Real.log ((1 - |x|) / 2))`. -/
theorem binEntropy_one_add_div_two_le_biased (x : ℝ) :
    binEntropy ((1 + x) / 2) ≤
      ((1 - |x|) / 2) * (1 - log ((1 - |x|) / 2)) := by
  have hsym : binEntropy ((1 + x) / 2) = binEntropy ((1 - |x|) / 2) := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, ← binEntropy_one_sub]
      ring_nf
    · rw [abs_of_nonpos h]
      ring_nf
  rw [hsym]
  exact binEntropy_le_mul_one_sub_log (by linarith [abs_nonneg x])

private theorem log_two_mul_entropy_bool_eq_binEntropy (q : PMF Bool) :
    log 2 * entropy q = binEntropy (q false).toReal := by
  rw [entropy_eq_sum, mul_div_cancel₀ _ (log_pos one_lt_two).ne', Fintype.sum_bool]
  have hsum : (q true).toReal + (q false).toReal = 1 := by
    simpa only [Fintype.sum_bool] using sum_toReal q
  have htrue : (q true).toReal = 1 - (q false).toReal := by linarith
  rw [htrue, binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm]

end EntropyBounds

/-! ### Support bridge between `ι → ZMod 2` and `Finset ι` -/

section SupportBridge

variable {ι : Type*}

/-- The support subset `{i : ι | v i ≠ 0}` of a binary vector `v : ι → ZMod 2`. -/
def zmodSupport [Fintype ι] (v : ι → ZMod 2) : Finset ι :=
  univ.filter fun i ↦ v i ≠ 0

/-- Membership characterization of `zmodSupport`. -/
@[simp] theorem mem_zmodSupport [Fintype ι] {v : ι → ZMod 2} {i : ι} :
    i ∈ zmodSupport v ↔ v i ≠ 0 := by
  simp [zmodSupport]

/-- The support of the zero vector is empty. -/
@[simp] theorem zmodSupport_zero [Fintype ι] : zmodSupport (0 : ι → ZMod 2) = ∅ := by
  ext i
  simp

/-- The support of a standard basis vector `Pi.single i 1` is `{i}`. -/
@[simp] theorem zmodSupport_single [Fintype ι] [DecidableEq ι] (i : ι) :
    zmodSupport (Pi.single i (1 : ZMod 2)) = {i} := by
  ext j
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

private theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

/-- `zmodSupport` is injective on `ι → ZMod 2`. -/
theorem zmodSupport_injective [Fintype ι] : Function.Injective (zmodSupport (ι := ι)) := by
  intro u v huv
  funext i
  by_cases hu : u i = 0
  · have hi : i ∉ zmodSupport u := by simp [hu]
    rw [huv] at hi
    have hv : v i = 0 := by simpa using hi
    rw [hu, hv]
  · have hi : i ∈ zmodSupport u := by simp [hu]
    rw [huv] at hi
    have hv : v i ≠ 0 := by simpa using hi
    rw [zmod_two_eq_one_of_ne_zero hu, zmod_two_eq_one_of_ne_zero hv]

/-- Indicator vector in `ι → ZMod 2` of a finite subset `S : Finset ι`. -/
def finsetIndicatorZMod [DecidableEq ι] (S : Finset ι) : ι → ZMod 2 :=
  fun i ↦ if i ∈ S then 1 else 0

/-- `finsetIndicatorZMod S` takes value `1` on elements of `S`. -/
@[simp] theorem finsetIndicatorZMod_of_mem [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∈ S) :
    finsetIndicatorZMod S i = 1 := by
  simp [finsetIndicatorZMod, hi]

/-- `finsetIndicatorZMod S` takes value `0` outside `S`. -/
@[simp] theorem finsetIndicatorZMod_of_notMem [DecidableEq ι] {S : Finset ι} {i : ι}
    (hi : i ∉ S) : finsetIndicatorZMod S i = 0 := by
  simp [finsetIndicatorZMod, hi]

/-- `zmodSupport` is a left inverse to `finsetIndicatorZMod`. -/
@[simp] theorem zmodSupport_finsetIndicatorZMod [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    zmodSupport (finsetIndicatorZMod S) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

/-- Under `bitEquiv.symm : Bool ≃+* ZMod 2`, parity on `zmodSupport v` is the dot product with `v`.
-/
theorem bitEquiv_symm_parityOn_zmodSupport [Fintype ι] (v : ι → ZMod 2) (x : ι → Bool) :
    bitEquiv.symm (parityOn (zmodSupport v) x) = v ⬝ᵥ toZModSpace ι x := by
  rw [parityOn_eq_sum, map_sum]
  simp only [dotProduct, toZModSpace_apply]
  rw [zmodSupport, sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases hv : v i = 0
  · simp [hv]
  · simp [zmod_two_eq_one_of_ne_zero hv]

/-- Evaluating parities along any `ZMod 2`-basis of `ι → ZMod 2` is injective on `ι → Bool`. -/
theorem parityOn_basis_injective [Fintype ι] {κ : Type*}
    (B : Module.Basis κ (ZMod 2) (ι → ZMod 2)) :
    Function.Injective (fun (x : ι → Bool) (j : κ) ↦ parityOn (zmodSupport (B j)) x) := by
  classical
  intro x y hxy
  apply (toZModSpace ι).injective
  rw [← sub_eq_zero]
  set d : ι → ZMod 2 := toZModSpace ι x - toZModSpace ι y
  have hd : ∀ j : κ, B j ⬝ᵥ d = 0 := fun j ↦ by
    have hj := congrArg bitEquiv.symm (congrFun hxy j)
    rw [bitEquiv_symm_parityOn_zmodSupport, bitEquiv_symm_parityOn_zmodSupport] at hj
    rw [dotProduct_sub, hj, sub_self]
  funext i
  have hrepr : Pi.single i (1 : ZMod 2) =
      ∑ j ∈ (B.repr (Pi.single i 1)).support, B.repr (Pi.single i 1) j • B j := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (B.linearCombination_repr (Pi.single i (1 : ZMod 2))).symm
  have hdot : Pi.single i (1 : ZMod 2) ⬝ᵥ d = 0 := by
    rw [hrepr, sum_dotProduct]
    refine sum_eq_zero fun j _ ↦ ?_
    rw [smul_dotProduct, hd j, smul_zero]
  simpa [single_dotProduct] using hdot

end SupportBridge

/-! ### Entropic Chang inequality and basis/dimension bounds -/

section ChangCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem fourierCoeff_indicator_eq_sum (A : Finset (ι → Bool)) (S : Finset ι) :
    fourierCoeff ((A : Set (ι → Bool)).indicator 1) S =
      (∑ x ∈ A, chi ℝ S x) / 2 ^ Fintype.card ι := by
  rw [fourierCoeff_eq_sum]
  congr 1
  rw [← sum_subset (subset_univ A)]
  · refine sum_congr rfl fun x hx ↦ ?_
    simp [Set.indicator_of_mem (mem_coe.mpr hx)]
  · intro x _ hx
    simp [Set.indicator_of_notMem (show x ∉ (A : Set (ι → Bool)) from hx)]

private theorem abs_fourierCoeff_indicator_div_le_one {A : Finset (ι → Bool)} (hA : A.Nonempty)
    {α : ℝ} (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) (S : Finset ι) :
    |fourierCoeff ((A : Set (ι → Bool)).indicator 1) S / α| ≤ 1 := by
  have h2pos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hαpos : 0 < α := by
    have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
    nlinarith
  rw [abs_div, abs_of_pos hαpos, div_le_one hαpos, fourierCoeff_indicator_eq_sum, abs_div,
    abs_of_pos h2pos, div_le_iff₀ h2pos]
  have hsum : |∑ x ∈ A, chi ℝ S x| ≤ (#A : ℝ) := by
    calc |∑ x ∈ A, chi ℝ S x|
        ≤ ∑ x ∈ A, |chi ℝ S x| := abs_sum_le_sum_abs _ _
      _ = (#A : ℝ) := by simp
  linarith

private theorem map_parityOn_uniformOfFinset_false {A : Finset (ι → Bool)} (hA : A.Nonempty)
    {α : ℝ} (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) (S : Finset ι) :
    ((uniformOfFinset A hA).map (parityOn S) false).toReal =
      (1 + fourierCoeff ((A : Set (ι → Bool)).indicator 1) S / α) / 2 := by
  have hcard_ne : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.card_pos.ne'
  have h2pos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hαpos : 0 < α := by
    have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
    nlinarith
  have hmap : ((uniformOfFinset A hA).map (parityOn S) false).toReal =
      (#(A.filter fun x ↦ parityOn S x = false) : ℝ) / (#A : ℝ) := by
    rw [_root_.PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun x _ ↦ by
      split_ifs
      · exact _root_.PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top)]
    refine (sum_congr rfl fun x _ ↦ ?_).trans (by
      rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, div_eq_mul_inv])
    by_cases hxA : x ∈ A <;> by_cases hp : parityOn S x = false
    · simp [hxA, hp, uniformOfFinset_apply]
    · simp [hxA, hp]
    · simp [hxA, hp, uniformOfFinset_apply]
    · simp [hxA, hp]
  have hchi : ∀ x : ι → Bool,
      (if parityOn S x = false then (1 : ℝ) else 0) = (1 + chi ℝ S x) / 2 := fun x ↦ by
    rw [chi_eq_signVal_parityOn]
    cases parityOn S x <;> norm_num
  have hcount : (#(A.filter fun x ↦ parityOn S x = false) : ℝ) =
      ((#A : ℝ) + ∑ x ∈ A, chi ℝ S x) / 2 := by
    rw [card_filter, Nat.cast_sum]
    simp_rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hchi, ← sum_div, sum_add_distrib,
      sum_const, nsmul_eq_mul, mul_one]
  rw [hmap, hcount, fourierCoeff_indicator_eq_sum]
  rw [hα] at hcard_ne ⊢
  field_simp [h2pos.ne', hαpos.ne']

/-- **Entropic subadditivity bound for separating parity families**: if `x ↦ (parityOn (S j) x)_j`
is injective on a nonempty subset `A ⊆ (ι → Bool)` with `|A| = 2 ^ |ι| * α`, then
`log |A| ≤ ∑ j, binEntropy ((1 + f̂(S j) / α) / 2)`. -/
theorem log_card_le_sum_binEntropy_of_injOn {A : Finset (ι → Bool)} (hA : A.Nonempty) {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hinj : Set.InjOn (fun (x : ι → Bool) (j : κ) ↦ parityOn (S j) x) (A : Set (ι → Bool))) :
    log (#A : ℝ) ≤
      ∑ j : κ,
        binEntropy ((1 + fourierCoeff ((A : Set (ι → Bool)).indicator 1) (S j) / α) / 2) := by
  let P : _root_.PMF (ι → Bool) := uniformOfFinset A hA
  let T : (ι → Bool) → (κ → Bool) := fun x j ↦ parityOn (S j) x
  have hsupp : P.support = (A : Set (ι → Bool)) := by
    ext x
    exact mem_support_uniformOfFinset_iff hA x
  have hinj' : Set.InjOn T P.support := hsupp.symm ▸ hinj
  have hent_eq : entropy (P.map T) = logb 2 (#A : ℝ) := by
    rw [entropy_map_of_injOn P hinj', entropy_uniformOfFinset A hA]
  have hsub := entropy_le_sum_entropy_map_eval (P.map T)
  rw [hent_eq] at hsub
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have hmul := mul_le_mul_of_nonneg_left hsub hlog2.le
  rw [logb, mul_div_cancel₀ _ hlog2.ne', mul_sum] at hmul
  refine hmul.trans_eq (sum_congr rfl fun j _ ↦ ?_)
  have hcomp : (P.map T).map (fun y : κ → Bool ↦ y j) = P.map (parityOn (S j)) := by
    rw [_root_.PMF.map_comp]
    rfl
  rw [hcomp, log_two_mul_entropy_bool_eq_binEntropy, map_parityOn_uniformOfFinset_false hA hα (S j)]

/-- **Chang's inequality over any `ZMod 2`-basis**: for `A ⊆ (ι → Bool)` with `|A| = 2 ^ |ι| * α`
and any basis `B` of `ι → ZMod 2`, `∑ j, f̂(S_{B j}) ^ 2 ≤ 2 * α ^ 2 * log α⁻¹`. -/
theorem sum_fourierCoeff_sq_basis_le {A : Finset (ι → Bool)} {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {κ : Type*} [Fintype κ]
    (B : Module.Basis κ (ZMod 2) (ι → ZMod 2)) :
    ∑ j : κ, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B j)) ^ 2 ≤
      2 * α ^ 2 * log α⁻¹ := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hα0 : α = 0 := by
      simp only [card_empty, Nat.cast_zero] at hα
      exact (mul_eq_zero.mp hα.symm).resolve_left (by positivity)
    subst hα0
    have hfc0 : ∀ S,
        fourierCoeff (((∅ : Finset (ι → Bool)) : Set (ι → Bool)).indicator 1) S = 0 := fun S ↦ by
      rw [fourierCoeff_indicator_eq_sum]
      simp
    simp_rw [hfc0]
    simp
  have hαpos : 0 < α := by
    have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
    nlinarith [show (0 : ℝ) < 2 ^ Fintype.card ι by positivity]
  have hcard_eq : Fintype.card κ = Fintype.card ι := by
    have h1 := Module.finrank_eq_card_basis B
    have h2 : Module.finrank (ZMod 2) (ι → ZMod 2) = Fintype.card ι :=
      Module.finrank_fintype_fun_eq_card (ZMod 2)
    omega
  have hent := log_card_le_sum_binEntropy_of_injOn hA hα (fun j ↦ zmodSupport (B j))
    (parityOn_basis_injective B).injOn
  have hbound :
      ∑ j : κ, binEntropy ((1 + fourierCoeff ((A : Set (ι → Bool)).indicator 1)
          (zmodSupport (B j)) / α) / 2) ≤
        ∑ j : κ, (log 2 - (fourierCoeff ((A : Set (ι → Bool)).indicator 1)
          (zmodSupport (B j)) / α) ^ 2 / 2) :=
    sum_le_sum fun j _ ↦
      binEntropy_one_add_div_two_le (abs_fourierCoeff_indicator_div_le_one hA hα _)
  have hcomb := hent.trans hbound
  rw [hα, log_mul (by positivity) hαpos.ne', log_pow, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul, hcard_eq, ← sum_div] at hcomb
  have hstep : ∑ j : κ, (fourierCoeff ((A : Set (ι → Bool)).indicator 1)
      (zmodSupport (B j)) / α) ^ 2 ≤ 2 * log α⁻¹ := by
    rw [log_inv]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hstep (sq_nonneg α)
  rw [sum_mul] at hmul
  calc ∑ j : κ, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B j)) ^ 2
      = ∑ j : κ, (fourierCoeff ((A : Set (ι → Bool)).indicator 1)
          (zmodSupport (B j)) / α) ^ 2 * α ^ 2 := by
        refine sum_congr rfl fun j _ ↦ ?_
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hαpos.ne')]
    _ ≤ 2 * log α⁻¹ * α ^ 2 := hmul
    _ = 2 * α ^ 2 * log α⁻¹ := by ring

/-- **Chang's inequality over any finite linearly independent family**: for `A ⊆ (ι → Bool)` with
`|A| = 2 ^ |ι| * α` and linearly independent `v : κ → (ι → ZMod 2)`,
`∑ j, f̂(S_{v j}) ^ 2 ≤ 2 * α ^ 2 * log α⁻¹`. -/
theorem sum_fourierCoeff_sq_linearIndependent_le {A : Finset (ι → Bool)} {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {κ : Type*} [Fintype κ]
    {v : κ → (ι → ZMod 2)} (hv : LinearIndependent (ZMod 2) v) :
    ∑ j : κ, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (v j)) ^ 2 ≤
      2 * α ^ 2 * log α⁻¹ := by
  classical
  have hvon : LinearIndepOn (ZMod 2) id (Set.range v) := hv.linearIndepOn_id
  let s : Set (ι → ZMod 2) := hvon.extend (Set.subset_univ (Set.range v))
  let _ : Fintype s := Fintype.ofFinite s
  let B : Module.Basis s (ZMod 2) (ι → ZMod 2) := Module.Basis.extend hvon
  have hsub : Set.range v ⊆ s := hvon.subset_extend (Set.subset_univ (Set.range v))
  let emb : κ ↪ s :=
    ⟨fun j ↦ ⟨v j, hsub ⟨j, rfl⟩⟩, fun j₁ j₂ h ↦ hv.injective (congrArg Subtype.val h)⟩
  have hB : ∀ j : κ, B (emb j) = v j := fun j ↦ Module.Basis.extend_apply_self hvon _
  calc ∑ j : κ, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (v j)) ^ 2
      = ∑ j : κ, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B (emb j))) ^ 2 :=
        sum_congr rfl fun j _ ↦ by rw [hB j]
    _ = ∑ x ∈ univ.map emb,
          fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B x)) ^ 2 := by
        rw [sum_map]
    _ ≤ ∑ x : s, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B x)) ^ 2 :=
        sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    _ ≤ 2 * α ^ 2 * log α⁻¹ := sum_fourierCoeff_sq_basis_le hα B

/-- The set `{v : ι → ZMod 2 | ρ * α < |f̂(S_v)|}` of large Fourier characters of `1_A`. -/
def largeFourierChars (A : Finset (ι → Bool)) (α ρ : ℝ) : Set (ι → ZMod 2) :=
  {v : ι → ZMod 2 | ρ * α < |fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport v)|}

/-- Membership characterization of `largeFourierChars`. -/
@[simp] theorem mem_largeFourierChars {A : Finset (ι → Bool)} {α ρ : ℝ} {v : ι → ZMod 2} :
    v ∈ largeFourierChars A α ρ ↔
      ρ * α < |fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport v)| :=
  Iff.rfl

private theorem finrank_span_largeFourierChars_lt_of_pos {A : Finset (ι → Bool)} (hA : A.Nonempty)
    {α ρ : ℝ} (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) (hρ : 0 < ρ)
    (hpos : 0 < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (largeFourierChars A α ρ))) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (largeFourierChars A α ρ)) : ℝ) <
      2 * ρ⁻¹ ^ 2 * log α⁻¹ := by
  classical
  have hαpos : 0 < α := by
    have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
    nlinarith [show (0 : ℝ) < 2 ^ Fintype.card ι by positivity]
  obtain ⟨s, hsR, hspan, hli⟩ := exists_linearIndependent (ZMod 2) (largeFourierChars A α ρ)
  let _ : Fintype s := Fintype.ofFinite s
  have hcard_eq :
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (largeFourierChars A α ρ)) =
        Fintype.card s := by
    have hrange : Set.range (Subtype.val : s → ι → ZMod 2) = s := by
      ext x
      simp
    have hfin := finrank_span_eq_card hli
    rw [hrange] at hfin
    rw [← hspan, hfin]
  have hsne : (univ : Finset s).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (hcard_eq ▸ hpos)
  have hlt : ∑ _u : s, (ρ * α) ^ 2 <
      ∑ u : s, fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport u.1) ^ 2 := by
    refine sum_lt_sum_of_nonempty hsne fun u _ ↦ ?_
    have hu : ρ * α < |fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport u.1)| :=
      hsR u.2
    calc (ρ * α) ^ 2
        < |fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport u.1)| ^ 2 :=
          pow_lt_pow_left₀ hu (by positivity) two_ne_zero
      _ = fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport u.1) ^ 2 := sq_abs _
  have hchang := sum_fourierCoeff_sq_linearIndependent_le hα hli
  have hcomb : (Fintype.card s : ℝ) * (ρ * α) ^ 2 < 2 * α ^ 2 * log α⁻¹ := by
    have hconst : ∑ _u : s, (ρ * α) ^ 2 = (Fintype.card s : ℝ) * (ρ * α) ^ 2 := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    linarith
  rw [hcard_eq]
  have hρα : 0 < (ρ * α) ^ 2 := by positivity
  rw [← lt_div_iff₀ hρα] at hcomb
  refine hcomb.trans_eq ?_
  field_simp [hρ.ne', hαpos.ne']

/-- **Chang's dimension bound (strict form)**: for a nonempty proper subset `A ⊆ (ι → Bool)` with
`|A| = 2 ^ |ι| * α` and `ρ > 0`, the large Fourier characters span an `𝔽₂`-subspace of dimension
strictly less than `2 * ρ⁻¹ ^ 2 * log α⁻¹`. -/
theorem finrank_span_largeFourierChars_lt {A : Finset (ι → Bool)}
    (hA : A.Nonempty) (hAne : A ≠ univ)
    {α ρ : ℝ} (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) (hρ : 0 < ρ) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (largeFourierChars A α ρ)) : ℝ) <
      2 * ρ⁻¹ ^ 2 * log α⁻¹ := by
  rcases Nat.eq_zero_or_pos
      (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (largeFourierChars A α ρ))) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    have hαpos : 0 < α := by
      have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
      nlinarith [show (0 : ℝ) < 2 ^ Fintype.card ι by positivity]
    have hlt_card : #A < 2 ^ Fintype.card ι := by
      have hss : A ⊂ univ := ssubset_univ_iff.mpr hAne
      simpa only [card_univ, Fintype.card_fun, Fintype.card_bool] using card_lt_card hss
    have hαlt1 : α < 1 := by
      have hcast : (#A : ℝ) < 2 ^ Fintype.card ι := by exact_mod_cast hlt_card
      nlinarith [show (0 : ℝ) < 2 ^ Fintype.card ι by positivity]
    have hlog : 0 < log α⁻¹ := log_pos ((one_lt_inv₀ hαpos).mpr hαlt1)
    positivity
  · exact finrank_span_largeFourierChars_lt_of_pos hA hα hρ hpos

/-- **Chang's dimension bound (non-strict form)**: for any subset `A ⊆ (ι → Bool)` with
`|A| = 2 ^ |ι| * α` and `ρ > 0`, the large Fourier characters span an `𝔽₂`-subspace of dimension
at most `2 * ρ⁻¹ ^ 2 * log α⁻¹`. -/
theorem finrank_span_largeFourierChars_le {A : Finset (ι → Bool)} {α ρ : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) (hρ : 0 < ρ) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (largeFourierChars A α ρ)) : ℝ) ≤
      2 * ρ⁻¹ ^ 2 * log α⁻¹ := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hα0 : α = 0 := by
      simp only [card_empty, Nat.cast_zero] at hα
      exact (mul_eq_zero.mp hα.symm).resolve_left (by positivity)
    subst hα0
    have hR : largeFourierChars (∅ : Finset (ι → Bool)) 0 ρ = ∅ := by
      ext v
      simp [largeFourierChars, fourierCoeff_const]
    rw [hR, Submodule.span_empty, finrank_bot]
    simp
  by_cases hAne : A = univ
  · subst hAne
    have hα1 : α = 1 := by
      have hcard : (#(univ : Finset (ι → Bool)) : ℝ) = 2 ^ Fintype.card ι := by
        simp [Fintype.card_bool]
      have h2ne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
      exact mul_left_cancel₀ h2ne (by linarith)
    subst hα1
    have hsub : largeFourierChars (univ : Finset (ι → Bool)) 1 ρ ⊆ {0} := by
      intro v hv
      simp only [Set.mem_singleton_iff]
      by_contra hv0
      have hSne : zmodSupport v ≠ ∅ := fun h ↦ hv0 (zmodSupport_injective (h.trans
        zmodSupport_zero.symm))
      have hind : ((univ : Finset (ι → Bool)) : Set (ι → Bool)).indicator (1 : (ι → Bool) → ℝ) =
          fun _ ↦ 1 := by
        funext x; simp
      have hfc : fourierCoeff (((univ : Finset (ι → Bool)) : Set (ι → Bool)).indicator 1)
          (zmodSupport v) = 0 := by
        rw [hind, fourierCoeff_const]
        simp [hSne]
      simp only [mem_largeFourierChars, hfc, abs_zero, mul_one] at hv
      linarith
    have hspan : Submodule.span (ZMod 2) (largeFourierChars (univ : Finset (ι → Bool)) 1 ρ) = ⊥ :=
      le_bot_iff.mp ((Submodule.span_mono hsub).trans (by simp))
    rw [hspan, finrank_bot]
    simp
  · exact (finrank_span_largeFourierChars_lt hA hAne hα hρ).le

/-- **Biased entropic bound for any `ZMod 2`-basis**: for a nonempty subset `A ⊆ (ι → Bool)` with
`|A| = 2 ^ |ι| * α` and any basis `B` of `ι → ZMod 2`, `log |A| ≤ ∑ j, δ_j * (1 - log δ_j)` where
`δ_j = (1 - |f̂(S_{B j})| / α) / 2`. -/
theorem log_card_le_sum_biased_margin_basis {A : Finset (ι → Bool)} (hA : A.Nonempty) {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {κ : Type*} [Fintype κ]
    (B : Module.Basis κ (ZMod 2) (ι → ZMod 2)) :
    log (#A : ℝ) ≤
      ∑ j : κ,
        ((1 - |fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B j))| / α) / 2) *
          (1 - log ((1 - |fourierCoeff ((A : Set (ι → Bool)).indicator 1)
            (zmodSupport (B j))| / α) / 2)) := by
  have hαpos : 0 < α := by
    have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
    nlinarith [show (0 : ℝ) < 2 ^ Fintype.card ι by positivity]
  refine (log_card_le_sum_binEntropy_of_injOn hA hα (fun j ↦ zmodSupport (B j))
    (parityOn_basis_injective B).injOn).trans (sum_le_sum fun j _ ↦ ?_)
  have h := binEntropy_one_add_div_two_le_biased
    (fourierCoeff ((A : Set (ι → Bool)).indicator 1) (zmodSupport (B j)) / α)
  rwa [abs_div, abs_of_pos hαpos] at h

/-- **Biased entropic bound on single coordinates**: for a nonempty subset `A ⊆ (ι → Bool)` with
`|A| = 2 ^ |ι| * α`, `log |A| ≤ ∑ i, δ_i * (1 - log δ_i)` where
`δ_i = (1 - |f̂({i})| / α) / 2`. -/
theorem log_card_le_sum_biased_margin {A : Finset (ι → Bool)} (hA : A.Nonempty) {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) :
    log (#A : ℝ) ≤
      ∑ i : ι,
        ((1 - |fourierCoeff ((A : Set (ι → Bool)).indicator 1) {i}| / α) / 2) *
          (1 - log ((1 - |fourierCoeff ((A : Set (ι → Bool)).indicator 1) {i}| / α) / 2)) := by
  simpa only [Pi.basisFun_apply, zmodSupport_single] using
    log_card_le_sum_biased_margin_basis hA hα (Pi.basisFun (ZMod 2) ι)

end ChangCore

/-! ### Weight-`k` bases and permutation averaging bounds -/

section WeightKLinear

variable {ι : Type*} [Fintype ι]

private theorem sum_zmod_eq_card_zmodSupport (v : ι → ZMod 2) :
    ∑ i : ι, v i = (#(zmodSupport v) : ZMod 2) := by
  have hsum : ∑ i : ι, v i = ∑ _i ∈ zmodSupport v, (1 : ZMod 2) := by
    rw [← sum_subset (subset_univ (zmodSupport v))]
    · refine sum_congr rfl fun i hi ↦ ?_
      have hne : v i ≠ 0 := mem_zmodSupport.mp hi
      generalize hvi : v i = a at hne ⊢
      fin_cases a
      · exact absurd rfl hne
      · rfl
    · intro i _ hi
      by_contra hne
      exact hi (mem_zmodSupport.mpr hne)
  rw [hsum, sum_const, nsmul_eq_mul, mul_one]

private theorem card_filter_fin_lt {n m : ℕ} (hm : m ≤ n) :
    #(univ.filter fun i : Fin n ↦ i.val < m) = m := by
  let emb : Fin m ↪ Fin n :=
    ⟨fun t ↦ ⟨t.val, lt_of_lt_of_le t.isLt hm⟩,
      fun _ _ hab ↦ Fin.ext (congrArg (Fin.val (n := n)) hab)⟩
  have hbij : (univ.filter fun i : Fin n ↦ i.val < m) = univ.map emb := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_map]
    exact ⟨fun hi ↦ ⟨⟨i.val, hi⟩, Fin.ext rfl⟩, fun ⟨t, ht⟩ ↦ ht ▸ t.isLt⟩
  rw [hbij, card_map, card_univ, Fintype.card_fin]

private theorem no_weight_k_basis_of_even [Nonempty ι] {k : ℕ} (hk : Even k) :
    ¬ ∃ B : Module.Basis (Fin (Fintype.card ι)) (ZMod 2) (ι → ZMod 2),
        ∀ j, #(zmodSupport (B j)) = k := by
  classical
  rintro ⟨B, hB⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let L : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v ↦ ∑ i : ι, v i
      map_add' := fun u v ↦ sum_add_distrib
      map_smul' := fun c v ↦ by simp [mul_sum] }
  have hLB : ∀ j, L (B j) = 0 := fun j ↦ by
    change ∑ i : ι, B j i = 0
    rw [sum_zmod_eq_card_zmodSupport, hB j]
    obtain ⟨m, rfl⟩ := hk
    push_cast
    rw [← two_mul]
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  have hrepr := (B.linearCombination_repr (Pi.single i₀ (1 : ZMod 2))).symm
  have hzero : L (Pi.single i₀ (1 : ZMod 2)) = 0 := by
    rw [hrepr, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact sum_eq_zero fun j _ ↦ by rw [map_smul, hLB j, smul_zero]
  have hone : L (Pi.single i₀ (1 : ZMod 2)) = 1 := by
    change ∑ i : ι, Pi.single i₀ (1 : ZMod 2) i = 1
    simp
  rw [hone] at hzero
  exact one_ne_zero hzero

private theorem no_weight_k_basis_of_eq_card (hn : 2 ≤ Fintype.card ι) :
    ¬ ∃ B : Module.Basis (Fin (Fintype.card ι)) (ZMod 2) (ι → ZMod 2),
        ∀ j, #(zmodSupport (B j)) = Fintype.card ι := by
  rintro ⟨B, hB⟩
  let j0 : Fin (Fintype.card ι) := ⟨0, by omega⟩
  let j1 : Fin (Fintype.card ι) := ⟨1, by omega⟩
  have heq : B j0 = B j1 := zmodSupport_injective <| by
    rw [eq_univ_of_card _ (hB j0), eq_univ_of_card _ (hB j1)]
  have hne : j0 ≠ j1 := by simp [j0, j1]
  exact hne (B.injective heq)

private theorem exists_weight_k_basis_fin_of_odd_lt {n k : ℕ} (hk : Odd k) (hkn : k < n) :
    ∃ B : Module.Basis (Fin n) (ZMod 2) (Fin n → ZMod 2),
      ∀ j, #(zmodSupport (B j)) = k := by
  have hk1 : 1 ≤ k := by obtain ⟨m, rfl⟩ := hk; omega
  let _ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let v : Fin n → (Fin n → ZMod 2) := fun j i ↦
    if j.val < k + 1 then
      if i.val < k + 1 ∧ i ≠ j then 1 else 0
    else
      if i.val < k - 1 ∨ i = j then 1 else 0
  have hv_card : ∀ j : Fin n, #(zmodSupport (v j)) = k := fun j ↦ by
    by_cases hj : j.val < k + 1
    · have hset : zmodSupport (v j) = (univ.filter fun i : Fin n ↦ i.val < k + 1).erase j := by
        ext i
        simp only [mem_zmodSupport, mem_erase, mem_filter, mem_univ, true_and, v, hj, ↓reduceIte]
        by_cases h : i.val < k + 1 ∧ i ≠ j
        · simp [h]
        · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, false_iff, not_and]
          exact fun hne hlt ↦ h ⟨hlt, hne⟩
      rw [hset, card_erase_of_mem (mem_filter.mpr ⟨mem_univ j, hj⟩),
        card_filter_fin_lt (by omega : k + 1 ≤ n)]
      omega
    · have hset : zmodSupport (v j) =
          insert j (univ.filter fun i : Fin n ↦ i.val < k - 1) := by
        ext i
        simp only [mem_zmodSupport, mem_insert, mem_filter, mem_univ, true_and, v, hj, ↓reduceIte]
        by_cases h : i.val < k - 1 ∨ i = j
        · rcases h with h1 | rfl
          · simp [h1]
          · simp
        · push Not at h
          simp [h.1, h.2]
      have hnotmem : j ∉ (univ.filter fun i : Fin n ↦ i.val < k - 1) := by
        simp only [mem_filter, mem_univ, true_and]
        omega
      rw [hset, card_insert_of_notMem hnotmem, card_filter_fin_lt (by omega : k - 1 ≤ n)]
      omega
  have hv_li : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hhi : ∀ j : Fin n, ¬ j.val < k + 1 → c j = 0 := fun j hj ↦ by
      have hcoord := congrFun hc j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      have hterm : ∀ m : Fin n, c m * v m j = if m = j then c j else 0 := fun m ↦ by
        dsimp only [v]
        by_cases hm : m.val < k + 1
        · have hne : m ≠ j := fun h ↦ hj (h ▸ hm)
          simp [hm, hj, hne]
        · have hlt : ¬ j.val < k - 1 := by omega
          by_cases hmj : m = j
          · subst hmj; simp [hm]
          · simp [hm, hlt, Ne.symm hmj, hmj]
      simpa [hterm] using hcoord
    let T : Finset (Fin n) := univ.filter fun j ↦ j.val < k + 1
    let s : ZMod 2 := ∑ j ∈ T, c j
    have hlo : ∀ i ∈ T, c i = s := fun i hi ↦ by
      have hi' : i.val < k + 1 := (mem_filter.mp hi).2
      have hcoord := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      have hsumT : ∑ j ∈ T, c j * v j i = 0 := by
        rw [← hcoord]
        refine sum_subset (subset_univ T) fun j _ hj ↦ ?_
        have hj' : ¬ j.val < k + 1 := by simpa [T] using hj
        rw [hhi j hj', zero_mul]
      have hterm : ∀ j ∈ T, c j * v j i = if j = i then 0 else c j := fun j hj ↦ by
        have hj' : j.val < k + 1 := (mem_filter.mp hj).2
        dsimp only [v]
        by_cases hji : j = i
        · subst hji; simp [hi']
        · simp [hj', hi', Ne.symm hji, hji]
      rw [sum_congr rfl hterm] at hsumT
      have herase : ∑ j ∈ T, (if j = i then 0 else c j) = ∑ j ∈ T.erase i, c j := by
        rw [← add_sum_erase T (fun j ↦ if j = i then 0 else c j) hi]
        simp only [↓reduceIte, zero_add]
        exact sum_congr rfl fun j hj ↦ by simp [(mem_erase.mp hj).1]
      rw [herase] at hsumT
      have hadd := add_sum_erase T c hi
      rw [hsumT, add_zero] at hadd
      exact hadd
    have hTcard : #T = k + 1 := card_filter_fin_lt (by omega : k + 1 ≤ n)
    have hs0 : s = 0 := by
      have hss : s = (#T : ZMod 2) * s := by
        calc s = ∑ j ∈ T, c j := rfl
          _ = ∑ _j ∈ T, s := sum_congr rfl hlo
          _ = (#T : ZMod 2) * s := by rw [sum_const, nsmul_eq_mul]
      rw [hTcard] at hss
      obtain ⟨m, rfl⟩ := hk
      have hev : ((2 * m + 1 + 1 : ℕ) : ZMod 2) = 0 := by
        have h2 : (2 : ZMod 2) = 0 := by decide
        push_cast
        rw [show (2 : ZMod 2) * m + 1 + 1 = 2 * (m + 1) by ring, h2, zero_mul]
      rw [hev, zero_mul] at hss
      exact hss
    intro j
    by_cases hj : j.val < k + 1
    · have hjT : j ∈ T := mem_filter.mpr ⟨mem_univ j, hj⟩
      rw [hlo j hjT, hs0]
    · exact hhi j hj
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hv_li (by simp), ?_⟩
  intro j
  simpa only [coe_basisOfLinearIndependentOfCardEqFinrank] using hv_card j

private theorem exists_weight_k_basis_of_odd {k : ℕ} (hk : Odd k)
    (hkn : k < Fintype.card ι ∨ (k = 1 ∧ Fintype.card ι = 1)) :
    ∃ B : Module.Basis (Fin (Fintype.card ι)) (ZMod 2) (ι → ZMod 2),
      ∀ j, #(zmodSupport (B j)) = k := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let L : (Fin (Fintype.card ι) → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e
  have hcardL : ∀ w : Fin (Fintype.card ι) → ZMod 2,
      #(zmodSupport (L w)) = #(zmodSupport w) := fun w ↦ by
    have hmap : zmodSupport (L w) = (zmodSupport w).map e.symm.toEmbedding := by
      ext i
      simp only [mem_zmodSupport, mem_map, Equiv.coe_toEmbedding]
      refine ⟨fun hi ↦ ⟨e i, hi, e.symm_apply_apply i⟩, fun ⟨a, ha, hai⟩ ↦ ?_⟩
      have heq : e i = a := by rw [← hai, e.apply_symm_apply]
      simpa [L, heq] using ha
    rw [hmap, card_map]
  rcases hkn with hlt | ⟨rfl, h1⟩
  · obtain ⟨B₀, hB₀⟩ := exists_weight_k_basis_fin_of_odd_lt hk hlt
    refine ⟨B₀.map L, fun j ↦ ?_⟩
    rw [Module.Basis.map_apply, hcardL, hB₀ j]
  · refine ⟨(Pi.basisFun (ZMod 2) (Fin (Fintype.card ι))).map L, fun j ↦ ?_⟩
    rw [Module.Basis.map_apply, hcardL, Pi.basisFun_apply, zmodSupport_single, card_singleton]

/-- **Exact characterization of weight-`k` bases of `ι → ZMod 2`**: for nonempty finite `ι`,
there exists a `ZMod 2`-basis consisting solely of Hamming weight-`k` vectors if and only if
`k` is odd and either `k < |ι|` or `k = |ι| = 1`. -/
theorem exists_weight_k_basis_iff [Nonempty ι] (k : ℕ) :
    (∃ B : Module.Basis (Fin (Fintype.card ι)) (ZMod 2) (ι → ZMod 2),
      ∀ j, #(zmodSupport (B j)) = k) ↔
      Odd k ∧ (k < Fintype.card ι ∨ (k = 1 ∧ Fintype.card ι = 1)) := by
  refine ⟨?_, fun ⟨hk, hkn⟩ ↦ exists_weight_k_basis_of_odd hk hkn⟩
  rintro ⟨B, hB⟩
  have hkodd : Odd k := by
    rcases Nat.even_or_odd k with hev | hodd
    · exact absurd ⟨B, hB⟩ (no_weight_k_basis_of_even hev)
    · exact hodd
  refine ⟨hkodd, ?_⟩
  have hkle : k ≤ Fintype.card ι := by
    have h0 : Fin (Fintype.card ι) := ⟨0, Fintype.card_pos⟩
    rw [← hB h0]
    exact card_le_univ _
  rcases hkle.eq_or_lt with rfl | hlt
  · right
    have hle1 : Fintype.card ι ≤ 1 := by
      by_contra h2
      exact no_weight_k_basis_of_eq_card (by omega) ⟨B, hB⟩
    have hpos := Fintype.card_pos (α := ι)
    omega
  · exact Or.inl hlt

private theorem exists_weight_k_linearIndependent_even {k : ℕ} (hk2 : 2 ≤ k)
    (hkn : k < Fintype.card ι) :
    ∃ v : Fin (Fintype.card ι - 1) → (ι → ZMod 2),
      LinearIndependent (ZMod 2) v ∧ ∀ j, #(zmodSupport (v j)) = k := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let L : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e
  let w : Fin (n - 1) → (Fin n → ZMod 2) := fun j i ↦
    if j.val < k then
      if i.val < k + 1 ∧ i.val ≠ j.val then 1 else 0
    else
      if i.val < k - 1 ∨ i.val = j.val + 1 then 1 else 0
  have hw_card : ∀ j : Fin (n - 1), #(zmodSupport (w j)) = k := fun j ↦ by
    by_cases hj : j.val < k
    · let j' : Fin n := ⟨j.val, by omega⟩
      have hset : zmodSupport (w j) = (univ.filter fun i : Fin n ↦ i.val < k + 1).erase j' := by
        ext i
        simp only [mem_zmodSupport, mem_erase, mem_filter, mem_univ, true_and, w, hj, ↓reduceIte]
        have hne : i ≠ j' ↔ i.val ≠ j.val := by simp [Fin.ext_iff, j']
        by_cases h : i.val < k + 1 ∧ i.val ≠ j.val
        · simp [h, hne.mpr h.2]
        · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, false_iff, not_and]
          intro hne' hlt
          exact h ⟨hlt, hne.mp hne'⟩
      rw [hset, card_erase_of_mem (mem_filter.mpr ⟨mem_univ j', by simp only [j']; omega⟩),
        card_filter_fin_lt (by omega : k + 1 ≤ n)]
      omega
    · let m : Fin n := ⟨j.val + 1, by omega⟩
      have hset : zmodSupport (w j) =
          insert m (univ.filter fun i : Fin n ↦ i.val < k - 1) := by
        ext i
        simp only [mem_zmodSupport, mem_insert, mem_filter, mem_univ, true_and, w, hj, ↓reduceIte]
        have heq : i = m ↔ i.val = j.val + 1 := by simp [Fin.ext_iff, m]
        by_cases h : i.val < k - 1 ∨ i.val = j.val + 1
        · rcases h with h1 | h2
          · simp [h1]
          · simp [heq.mpr h2, m]
        · push Not at h
          rw [heq]
          simp [h.1, h.2]
      have hnotmem : m ∉ (univ.filter fun i : Fin n ↦ i.val < k - 1) := by
        simp only [mem_filter, mem_univ, true_and, m]
        omega
      rw [hset, card_insert_of_notMem hnotmem, card_filter_fin_lt (by omega : k - 1 ≤ n)]
      omega
  have hw_li : LinearIndependent (ZMod 2) w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hhi : ∀ j : Fin (n - 1), ¬ j.val < k → c j = 0 := fun j hj ↦ by
      let m : Fin n := ⟨j.val + 1, by omega⟩
      have hcoord := congrFun hc m
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      have hterm : ∀ r : Fin (n - 1), c r * w r m = if r = j then c j else 0 := fun r ↦ by
        dsimp only [w]
        by_cases hr : r.val < k
        · have hne : r ≠ j := fun h ↦ hj (h ▸ hr)
          have hm : ¬ m.val < k + 1 := by simp only [m]; omega
          simp [hr, hm, hne]
        · have hm1 : ¬ m.val < k - 1 := by simp only [m]; omega
          by_cases hrj : r = j
          · subst hrj; simp [hr, m]
          · have hneq : m.val ≠ r.val + 1 := by
              simp only [m]
              intro heq
              exact hrj (Fin.ext (by omega))
            simp [hr, hm1, hneq, hrj]
      simpa [hterm] using hcoord
    let T : Finset (Fin (n - 1)) := univ.filter fun j ↦ j.val < k
    have hs0 : ∑ j ∈ T, c j = 0 := by
      let mk : Fin n := ⟨k, hkn⟩
      have hcoord := congrFun hc mk
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      have hsumT : ∑ j ∈ T, c j * w j mk = 0 := by
        rw [← hcoord]
        refine sum_subset (subset_univ T) fun j _ hj ↦ ?_
        have hj' : ¬ j.val < k := by simpa [T] using hj
        rw [hhi j hj', zero_mul]
      rw [← hsumT]
      refine sum_congr rfl fun j hj ↦ ?_
      have hj' : j.val < k := (mem_filter.mp hj).2
      have hlt : mk.val < k + 1 := by simp only [mk]; omega
      have hne : mk.val ≠ j.val := by simp only [mk]; omega
      dsimp only [w]
      simp [hj', hlt, hne]
    intro j
    by_cases hj : j.val < k
    · let mj : Fin n := ⟨j.val, by omega⟩
      have hcoord := congrFun hc mj
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      have hsumT : ∑ r ∈ T, c r * w r mj = 0 := by
        rw [← hcoord]
        refine sum_subset (subset_univ T) fun r _ hr ↦ ?_
        have hr' : ¬ r.val < k := by simpa [T] using hr
        rw [hhi r hr', zero_mul]
      have hterm : ∀ r ∈ T, c r * w r mj = if r = j then 0 else c r := fun r hr ↦ by
        have hr' : r.val < k := (mem_filter.mp hr).2
        have hlt : mj.val < k + 1 := by simp only [mj]; omega
        dsimp only [w]
        by_cases hrj : r = j
        · subst hrj; simp [hr', mj]
        · have hne : mj.val ≠ r.val := fun h ↦ hrj (Fin.ext h.symm)
          simp [hr', hlt, hne, hrj]
      rw [sum_congr rfl hterm] at hsumT
      have hjT : j ∈ T := mem_filter.mpr ⟨mem_univ j, hj⟩
      have hadd := add_sum_erase T c hjT
      have herase : ∑ r ∈ T, (if r = j then 0 else c r) = ∑ r ∈ T.erase j, c r := by
        rw [← add_sum_erase T (fun r ↦ if r = j then 0 else c r) hjT]
        simp only [↓reduceIte, zero_add]
        refine sum_congr rfl fun r hr ↦ ?_
        have hrne : r ≠ j := (mem_erase.mp hr).1
        simp [hrne]
      rw [herase] at hsumT
      rw [hsumT, add_zero] at hadd
      rw [hadd, hs0]
    · exact hhi j hj
  refine ⟨fun j ↦ L (w j), hw_li.map' L.toLinearMap L.ker, fun j ↦ ?_⟩
  have hmap : zmodSupport (L (w j)) = (zmodSupport (w j)).map e.symm.toEmbedding := by
    ext i
    simp only [mem_zmodSupport, mem_map, Equiv.coe_toEmbedding]
    refine ⟨fun hi ↦ ⟨e i, hi, e.symm_apply_apply i⟩, fun ⟨a, ha, hai⟩ ↦ ?_⟩
    have heq : e i = a := by rw [← hai, e.apply_symm_apply]
    simpa [L, heq] using ha
  rw [hmap, card_map, hw_card j]

private theorem exists_perm_map_eq {κ : Type*} [Finite κ] {S T : Finset κ} (hcard : #S = #T) :
    ∃ τ : Equiv.Perm κ, S.map τ.toEmbedding = T := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcompl : #(Sᶜ : Finset κ) = #(Tᶜ : Finset κ) := by
    rw [card_compl, card_compl, hcard]
  obtain ⟨e₁⟩ := Fintype.truncEquivOfCardEq (α := S) (β := T)
    (by rw [Fintype.card_coe, Fintype.card_coe, hcard])
  obtain ⟨e₂⟩ := Fintype.truncEquivOfCardEq (α := (Sᶜ : Finset κ)) (β := (Tᶜ : Finset κ))
    (by rw [Fintype.card_coe, Fintype.card_coe, hcompl])
  let τ : Equiv.Perm κ :=
    { toFun := fun i ↦ if hi : i ∈ S then (e₁ ⟨i, hi⟩).1 else (e₂ ⟨i, mem_compl.mpr hi⟩).1
      invFun := fun j ↦
        if hj : j ∈ T then (e₁.symm ⟨j, hj⟩).1 else (e₂.symm ⟨j, mem_compl.mpr hj⟩).1
      left_inv := fun i ↦ by
        dsimp only
        by_cases hi : i ∈ S
        · simp only [hi, ↓reduceDIte, (e₁ ⟨i, hi⟩).2]
          exact congrArg Subtype.val (e₁.symm_apply_apply ⟨i, hi⟩)
        · have hnotT : (e₂ ⟨i, mem_compl.mpr hi⟩).1 ∉ T :=
            mem_compl.mp (e₂ ⟨i, mem_compl.mpr hi⟩).2
          simp only [hi, ↓reduceDIte, hnotT]
          exact congrArg Subtype.val (e₂.symm_apply_apply ⟨i, mem_compl.mpr hi⟩)
      right_inv := fun j ↦ by
        dsimp only
        by_cases hj : j ∈ T
        · simp only [hj, ↓reduceDIte, (e₁.symm ⟨j, hj⟩).2]
          exact congrArg Subtype.val (e₁.apply_symm_apply ⟨j, hj⟩)
        · have hnotS : (e₂.symm ⟨j, mem_compl.mpr hj⟩).1 ∉ S :=
            mem_compl.mp (e₂.symm ⟨j, mem_compl.mpr hj⟩).2
          simp only [hj, ↓reduceDIte, hnotS]
          exact congrArg Subtype.val (e₂.apply_symm_apply ⟨j, mem_compl.mpr hj⟩) }
  refine ⟨τ, ?_⟩
  ext j
  simp only [mem_map, Equiv.coe_toEmbedding]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    simp only [τ, Equiv.coe_fn_mk, hi, ↓reduceDIte]
    exact (e₁ ⟨i, hi⟩).2
  · intro hj
    refine ⟨(e₁.symm ⟨j, hj⟩).1, (e₁.symm ⟨j, hj⟩).2, ?_⟩
    simp only [τ, Equiv.coe_fn_mk, (e₁.symm ⟨j, hj⟩).2, ↓reduceDIte]
    exact congrArg Subtype.val (e₁.apply_symm_apply ⟨j, hj⟩)

end WeightKLinear

section WeightKAveraging

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem choose_mul_sum_perm_eq_factorial_mul_sum {S : Finset ι} {k : ℕ} (hS : #S = k)
    (g : Finset ι → ℝ) :
    ((Fintype.card ι).choose k : ℝ) * ∑ σ : Equiv.Perm ι, g (S.map σ.toEmbedding) =
      ((Fintype.card ι).factorial : ℝ) * ∑ T : Finset ι with #T = k, g T := by
  classical
  let K : Finset (Finset ι) := univ.filter fun T ↦ #T = k
  have hKcard : #K = (Fintype.card ι).choose k := by
    have hpow : K = (univ : Finset ι).powersetCard k := by
      ext T
      simp [K, mem_powersetCard]
    rw [hpow, card_powersetCard, card_univ]
  let fiber (T : Finset ι) : Finset (Equiv.Perm ι) :=
    univ.filter fun σ ↦ S.map σ.toEmbedding = T
  have hfib_eq : ∀ T ∈ K, #(fiber T) = #(fiber S) := fun T hT ↦ by
    have hTcard : #T = k := (mem_filter.mp hT).2
    obtain ⟨τ, hτ⟩ := exists_perm_map_eq (hS.trans hTcard.symm)
    refine card_bij (fun σ _ ↦ τ⁻¹ * σ) ?_ ?_ ?_
    · intro σ hσ
      have hσ' : S.map σ.toEmbedding = T := (mem_filter.mp hσ).2
      simp only [fiber, mem_filter, mem_univ, true_and]
      ext i
      simp only [mem_map, Equiv.coe_toEmbedding, Equiv.Perm.coe_mul, Function.comp_apply]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hmemT : σ a ∈ T := by rw [← hσ']; exact mem_map_of_mem _ ha
        rw [← hτ] at hmemT
        obtain ⟨b, hb, hba⟩ := mem_map.mp hmemT
        have : τ⁻¹ (σ a) = b := by
          apply τ.injective
          simpa using hba.symm
        exact this ▸ hb
      · intro hi
        have hmemT : τ i ∈ T := by rw [← hτ]; exact mem_map_of_mem _ hi
        rw [← hσ'] at hmemT
        obtain ⟨a, ha, hai⟩ := mem_map.mp hmemT
        refine ⟨a, ha, ?_⟩
        apply τ.injective
        simpa using hai
    · intro σ₁ _ σ₂ _ h
      exact mul_left_cancel h
    · intro σ hσ
      have hσ' : S.map σ.toEmbedding = S := (mem_filter.mp hσ).2
      refine ⟨τ * σ, ?_, by simp⟩
      simp only [fiber, mem_filter, mem_univ, true_and]
      ext j
      simp only [mem_map, Equiv.coe_toEmbedding, Equiv.Perm.coe_mul, Function.comp_apply]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hmemS : σ a ∈ S := by rw [← hσ']; exact mem_map_of_mem _ ha
        rw [← hτ]
        exact mem_map_of_mem _ hmemS
      · intro hj
        rw [← hτ] at hj
        obtain ⟨b, hb, rfl⟩ := mem_map.mp hj
        rw [← hσ'] at hb
        obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
        exact ⟨a, ha, rfl⟩
  have hsum_perm : ∑ σ : Equiv.Perm ι, g (S.map σ.toEmbedding) =
      (#(fiber S) : ℝ) * ∑ T ∈ K, g T := by
    rw [← sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm ι ↦ S.map σ.toEmbedding) (t := K)
      (fun σ _ ↦ by simp [K, hS])]
    rw [mul_sum]
    refine sum_congr rfl fun T hT ↦ ?_
    have hcongr : ∑ σ ∈ fiber T, g (S.map σ.toEmbedding) = ∑ _σ ∈ fiber T, g T :=
      sum_congr rfl fun σ hσ ↦ by rw [(mem_filter.mp hσ).2]
    change ∑ σ ∈ fiber T, g (S.map σ.toEmbedding) = (#(fiber S) : ℝ) * g T
    rw [hcongr, sum_const, nsmul_eq_mul, hfib_eq T hT]
  have hcount : (#K : ℝ) * (#(fiber S) : ℝ) = ((Fintype.card ι).factorial : ℝ) := by
    have hnat : #K * #(fiber S) = Fintype.card (Equiv.Perm ι) := by
      calc #K * #(fiber S)
          = ∑ _T ∈ K, #(fiber S) := by rw [sum_const, smul_eq_mul]
        _ = ∑ T ∈ K, #(fiber T) := sum_congr rfl fun T hT ↦ (hfib_eq T hT).symm
        _ = #(univ : Finset (Equiv.Perm ι)) :=
            (card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm ι ↦ S.map σ.toEmbedding)
              (s := univ) (t := K) fun σ _ ↦ by simp [K, hS]).symm
        _ = Fintype.card (Equiv.Perm ι) := card_univ
    rw [Fintype.card_perm] at hnat
    exact_mod_cast hnat
  rw [hsum_perm, ← hKcard, ← mul_assoc, hcount]

private theorem levelWeight_le_of_linearIndependent_weight {A : Finset (ι → Bool)} {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {m k : ℕ} (hm : 0 < m)
    {v : Fin m → (ι → ZMod 2)} (hv : LinearIndependent (ZMod 2) v)
    (hcard : ∀ j, #(zmodSupport (v j)) = k) :
    levelWeight k ((A : Set (ι → Bool)).indicator 1) ≤
      (2 / (m : ℝ)) * ((Fintype.card ι).choose k : ℝ) * α ^ 2 * log α⁻¹ := by
  let f : (ι → Bool) → ℝ := (A : Set (ι → Bool)).indicator 1
  have hperm_bound : ∀ σ : Equiv.Perm ι,
      ∑ j : Fin m, fourierCoeff f ((zmodSupport (v j)).map σ.toEmbedding) ^ 2 ≤
        2 * α ^ 2 * log α⁻¹ := fun σ ↦ by
    let L : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
      LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) σ.symm
    have hvσ : LinearIndependent (ZMod 2) (fun j : Fin m ↦ L (v j)) :=
      hv.map' L.toLinearMap L.ker
    have hsupp : ∀ j : Fin m,
        zmodSupport (L (v j)) = (zmodSupport (v j)).map σ.toEmbedding := fun j ↦ by
      ext i
      simp only [mem_zmodSupport, mem_map, Equiv.coe_toEmbedding]
      refine ⟨fun hi ↦ ⟨σ.symm i, hi, σ.apply_symm_apply i⟩, fun ⟨a, ha, hai⟩ ↦ ?_⟩
      have heq : σ.symm i = a := by rw [← hai, σ.symm_apply_apply]
      simpa [L, heq] using ha
    simpa only [hsupp] using sum_fourierCoeff_sq_linearIndependent_le hα hvσ
  have hsum_all :
      ∑ σ : Equiv.Perm ι, ∑ j : Fin m, fourierCoeff f ((zmodSupport (v j)).map σ.toEmbedding) ^ 2
        ≤ ((Fintype.card ι).factorial : ℝ) * (2 * α ^ 2 * log α⁻¹) := by
    calc ∑ σ : Equiv.Perm ι,
            ∑ j : Fin m, fourierCoeff f ((zmodSupport (v j)).map σ.toEmbedding) ^ 2
        ≤ ∑ _σ : Equiv.Perm ι, (2 * α ^ 2 * log α⁻¹) := sum_le_sum fun σ _ ↦ hperm_bound σ
      _ = ((Fintype.card ι).factorial : ℝ) * (2 * α ^ 2 * log α⁻¹) := by
          rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_perm]
  have hchoose_nn : (0 : ℝ) ≤ ((Fintype.card ι).choose k : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum_all hchoose_nn
  rw [sum_comm, mul_sum] at hmul
  have hlhs :
      ∑ j : Fin m, ((Fintype.card ι).choose k : ℝ) *
          ∑ σ : Equiv.Perm ι, fourierCoeff f ((zmodSupport (v j)).map σ.toEmbedding) ^ 2 =
        (m : ℝ) * ((Fintype.card ι).factorial : ℝ) * levelWeight k f := by
    have hterm : ∀ j : Fin m,
        ((Fintype.card ι).choose k : ℝ) *
            ∑ σ : Equiv.Perm ι, fourierCoeff f ((zmodSupport (v j)).map σ.toEmbedding) ^ 2 =
          ((Fintype.card ι).factorial : ℝ) * levelWeight k f := fun j ↦
      choose_mul_sum_perm_eq_factorial_mul_sum (hcard j) (fun T ↦ fourierCoeff f T ^ 2)
    simp_rw [hterm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  rw [hlhs] at hmul
  have hfac_pos : (0 : ℝ) < ((Fintype.card ι).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hcancel : (m : ℝ) * levelWeight k f ≤
      ((Fintype.card ι).choose k : ℝ) * (2 * α ^ 2 * log α⁻¹) := by
    have h1 : ((Fintype.card ι).factorial : ℝ) * ((m : ℝ) * levelWeight k f) ≤
        ((Fintype.card ι).factorial : ℝ) *
          (((Fintype.card ι).choose k : ℝ) * (2 * α ^ 2 * log α⁻¹)) := by
      linarith
    exact le_of_mul_le_mul_left h1 hfac_pos
  have hdiv := (le_div_iff₀ hm_pos).mpr (by linarith : levelWeight k f * (m : ℝ) ≤
    ((Fintype.card ι).choose k : ℝ) * (2 * α ^ 2 * log α⁻¹))
  refine hdiv.trans_eq ?_
  ring

/-- **Level-`k` averaging bound for odd `k`**: when `k` is odd and either `k < |ι|` or
`k = |ι| = 1`, `levelWeight k (1_A) ≤ (2 / |ι|) * choose |ι| k * α ^ 2 * log α⁻¹`. -/
theorem levelWeight_indicator_le_of_odd {A : Finset (ι → Bool)} {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {k : ℕ} (hk : Odd k)
    (hkn : k < Fintype.card ι ∨ (k = 1 ∧ Fintype.card ι = 1)) :
    levelWeight k ((A : Set (ι → Bool)).indicator 1) ≤
      (2 / (Fintype.card ι : ℝ)) * ((Fintype.card ι).choose k : ℝ) * α ^ 2 * log α⁻¹ := by
  have hn : 0 < Fintype.card ι := by rcases hkn with h | ⟨_, h⟩ <;> omega
  obtain ⟨B, hB⟩ := exists_weight_k_basis_of_odd (ι := ι) hk hkn
  exact levelWeight_le_of_linearIndependent_weight hα hn B.linearIndependent hB

/-- **Level-`k` averaging bound for `2 ≤ k < |ι|`**: averaging over `(|ι| - 1)`-element linearly
independent weight-`k` families gives
`levelWeight k (1_A) ≤ (2 / (|ι| - 1)) * choose |ι| k * α ^ 2 * log α⁻¹`. -/
theorem levelWeight_indicator_le_of_even {A : Finset (ι → Bool)} {α : ℝ}
    (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k < Fintype.card ι) :
    levelWeight k ((A : Set (ι → Bool)).indicator 1) ≤
      (2 / ((Fintype.card ι : ℝ) - 1)) * ((Fintype.card ι).choose k : ℝ) * α ^ 2 * log α⁻¹ := by
  obtain ⟨v, hv, hcard⟩ := exists_weight_k_linearIndependent_even (ι := ι) hk2 hkn
  have hm : 0 < Fintype.card ι - 1 := by omega
  have h := levelWeight_le_of_linearIndependent_weight hα hm hv hcard
  rwa [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one] at h

private theorem factorial_le_pow_pred {n : ℕ} (hn : 1 ≤ n) : n.factorial ≤ n ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · calc (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
        _ ≤ (m + 1) * m ^ (m - 1) := Nat.mul_le_mul_left _ (ih hm)
        _ ≤ (m + 1) * (m + 1) ^ (m - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ m) _)
        _ = (m + 1) ^ m := by
            rw [← pow_succ', show m - 1 + 1 = m by omega]

private theorem descFactorial_le_pow (n k : ℕ) : n.descFactorial k ≤ n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le n k) ih

/-- **Unconditional level-`k` averaging bound**: for nonempty finite `ι` and every `k ≥ 1`,
`levelWeight k (1_A) ≤ (2 * |ι| ^ (k - 1) / k!) * α ^ 2 * log α⁻¹`. -/
theorem levelWeight_indicator_le_two_mul_pow_div_factorial [Nonempty ι] {A : Finset (ι → Bool)}
    {α : ℝ} (hα : (#A : ℝ) = 2 ^ Fintype.card ι * α) {k : ℕ} (hk : 1 ≤ k) :
    levelWeight k ((A : Set (ι → Bool)).indicator 1) ≤
      (2 * (Fintype.card ι : ℝ) ^ (k - 1) / (k.factorial : ℝ)) * α ^ 2 * log α⁻¹ := by
  set n := Fintype.card ι
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hlog_nn : 0 ≤ α ^ 2 * log α⁻¹ := by
    rcases A.eq_empty_or_nonempty with rfl | hA
    · have hα0 : α = 0 := by
        simp only [card_empty, Nat.cast_zero] at hα
        exact (mul_eq_zero.mp hα.symm).resolve_left (by positivity)
      subst hα0; simp
    · have hαpos : 0 < α := by
        have hcard : (0 : ℝ) < #A := Nat.cast_pos.mpr hA.card_pos
        nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
      have hαle1 : α ≤ 1 := by
        have hle : (#A : ℝ) ≤ 2 ^ n := by
          have : #A ≤ Fintype.card (ι → Bool) := card_le_univ A
          simpa [Fintype.card_fun, Fintype.card_bool] using
            (Nat.cast_le (α := ℝ)).mpr this
        nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
      have hlog : 0 ≤ log α⁻¹ := log_nonneg ((one_le_inv₀ hαpos).mpr hαle1)
      positivity
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  rcases lt_trichotomy k n with hlt | rfl | hgt
  · rcases Nat.even_or_odd k with hev | hodd
    · have hk2 : 2 ≤ k := by obtain ⟨m, rfl⟩ := hev; omega
      refine (levelWeight_indicator_le_of_even hα hk2 hlt).trans ?_
      have hcoeff : (2 / ((n : ℝ) - 1)) * (n.choose k : ℝ) ≤
          2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ) := by
        have hn2 : (0 : ℝ) < (n : ℝ) - 1 := by
          have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
          linarith
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hn2 hfac_pos]
        have hnat : n.choose k * k.factorial ≤ (n - 1) * n ^ (k - 1) := by
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          have hdesc1 : n.descFactorial k = n * (n - 1).descFactorial (k - 1) := by
            obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
            obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            rw [hn', hk', Nat.succ_descFactorial_succ]
            simp
          have hdesc2 : (n - 1).descFactorial (k - 1) =
              (n - 1) * (n - 2).descFactorial (k - 2) := by
            have hn2' : n - 1 ≠ 0 := by omega
            have hk2' : k - 1 ≠ 0 := by omega
            obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn2'
            obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk2'
            have hn2eq : n - 2 = n' := by omega
            have hk2eq : k - 2 = k' := by omega
            rw [hn', hk', hn2eq, hk2eq, Nat.succ_descFactorial_succ]
          rw [hdesc1, hdesc2]
          calc n * ((n - 1) * (n - 2).descFactorial (k - 2))
              = (n - 1) * (n * (n - 2).descFactorial (k - 2)) := by ring
            _ ≤ (n - 1) * (n * (n - 2) ^ (k - 2)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (descFactorial_le_pow _ _))
            _ ≤ (n - 1) * (n * n ^ (k - 2)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
                  (Nat.pow_le_pow_left (Nat.sub_le n 2) _))
            _ = (n - 1) * n ^ (k - 1) := by
                rw [← pow_succ', show k - 2 + 1 = k - 1 by omega]
        have hcast : (n.choose k : ℝ) * (k.factorial : ℝ) ≤
            ((n : ℝ) - 1) * (n : ℝ) ^ (k - 1) := by
          have h' : ((n.choose k * k.factorial : ℕ) : ℝ) ≤ (((n - 1) * n ^ (k - 1) : ℕ) : ℝ) :=
            Nat.cast_le.mpr hnat
          simpa [Nat.cast_sub hn1] using h'
        linarith
      calc (2 / ((n : ℝ) - 1)) * (n.choose k : ℝ) * α ^ 2 * log α⁻¹
          = ((2 / ((n : ℝ) - 1)) * (n.choose k : ℝ)) * (α ^ 2 * log α⁻¹) := by ring
        _ ≤ (2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ)) * (α ^ 2 * log α⁻¹) :=
            mul_le_mul_of_nonneg_right hcoeff hlog_nn
        _ = 2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ) * α ^ 2 * log α⁻¹ := by ring
    · refine (levelWeight_indicator_le_of_odd hα hodd (Or.inl hlt)).trans ?_
      have hcoeff : (2 / (n : ℝ)) * (n.choose k : ℝ) ≤
          2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ) := by
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hn_pos hfac_pos]
        have hnat : n.choose k * k.factorial ≤ n * n ^ (k - 1) := by
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          have hdesc1 : n.descFactorial k = n * (n - 1).descFactorial (k - 1) := by
            obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
            obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            rw [hn', hk', Nat.succ_descFactorial_succ]
            simp
          rw [hdesc1]
          calc n * (n - 1).descFactorial (k - 1)
              ≤ n * (n - 1) ^ (k - 1) := Nat.mul_le_mul_left _ (descFactorial_le_pow _ _)
            _ ≤ n * n ^ (k - 1) :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le n 1) _)
        have hcast : (n.choose k : ℝ) * (k.factorial : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          exact_mod_cast hnat
        linarith
      calc (2 / (n : ℝ)) * (n.choose k : ℝ) * α ^ 2 * log α⁻¹
          = ((2 / (n : ℝ)) * (n.choose k : ℝ)) * (α ^ 2 * log α⁻¹) := by ring
        _ ≤ (2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ)) * (α ^ 2 * log α⁻¹) :=
            mul_le_mul_of_nonneg_right hcoeff hlog_nn
        _ = 2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ) * α ^ 2 * log α⁻¹ := by ring
  · have htop : levelWeight n ((A : Set (ι → Bool)).indicator 1) ≤ 2 * α ^ 2 * log α⁻¹ := by
      let v : Fin 1 → (ι → ZMod 2) := fun _ ↦ finsetIndicatorZMod univ
      have hv_ne : finsetIndicatorZMod (univ : Finset ι) ≠ 0 := by
        obtain ⟨i₀⟩ := ‹Nonempty ι›
        intro h
        have hi := congrFun h i₀
        simp at hi
      have hv : LinearIndependent (ZMod 2) v := by
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        fin_cases i
        simp only [Fin.sum_univ_one, v] at hc
        exact (smul_eq_zero.mp hc).resolve_right hv_ne
      simpa [n, Nat.choose_self] using
        levelWeight_le_of_linearIndependent_weight hα (m := 1) (k := n)
          one_pos hv (fun _ ↦ by simp [v, n])
    refine htop.trans ?_
    have h1le : (1 : ℝ) ≤ (n : ℝ) ^ (n - 1) / (n.factorial : ℝ) := by
      rw [one_le_div hfac_pos]
      exact_mod_cast factorial_le_pow_pred hn1
    have hcoeff : (2 : ℝ) ≤ 2 * (n : ℝ) ^ (n - 1) / (n.factorial : ℝ) := by
      rw [mul_div_assoc]
      linarith
    calc 2 * α ^ 2 * log α⁻¹
        = 2 * (α ^ 2 * log α⁻¹) := by ring
      _ ≤ (2 * (n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) * (α ^ 2 * log α⁻¹) :=
          mul_le_mul_of_nonneg_right hcoeff hlog_nn
      _ = 2 * (n : ℝ) ^ (n - 1) / (n.factorial : ℝ) * α ^ 2 * log α⁻¹ := by ring
  · rw [levelWeight_eq_zero_of_card_lt hgt]
    have hcoeff_nn : (0 : ℝ) ≤ 2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ) := by positivity
    calc (0 : ℝ) ≤ (2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ)) * (α ^ 2 * log α⁻¹) :=
          mul_nonneg hcoeff_nn hlog_nn
      _ = 2 * (n : ℝ) ^ (k - 1) / (k.factorial : ℝ) * α ^ 2 * log α⁻¹ := by ring

end WeightKAveraging

end Cslib.BitString
