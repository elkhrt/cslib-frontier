module

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree
public import CslibFrontier.Computability.QueryComplexity.Randomized
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximate Degree Amplification and Randomized Query Complexity Bounds

Given a real polynomial `p` of degree at most `d` approximating a Boolean function
`f : {0, 1}ⁿ → {0, 1}` pointwise within error `ε₀ < 1 / 2`, composing the affine rescaling
`u(x) = (p(x) + ε₀) / (1 + 2 ε₀) ∈ [0, 1]` with the univariate degree-`(2m + 1)` majority
polynomial `M_{2m+1}(u) = ∑_{j = m + 1}^{2m + 1} C(2m + 1, j) uʲ (1 - u)^{2m + 1 - j}` yields an
approximating polynomial of degree at most `(2m + 1) d` with pointwise error bounded by
`(1 / 2) · (1 - ((1 - 2 ε₀) / (1 + 2 ε₀))²)ᵐ`.

This module establishes:

* `CslibFrontier.QueryComplexity.majorityPolyEval`: univariate degree-`(2m + 1)` majority
  polynomial and its symmetry and concentration bounds on `[0, 1]`.
* `CslibFrontier.QueryComplexity.approxDegree_le_odd_mul_approxDegree`: general `(2m + 1)`-fold
  error reduction for approximate degree from any `ε₀ < 1 / 2` to `ε`.
* `CslibFrontier.QueryComplexity.approxDegree_le_mul_approxDegree_third_mul_log`: logarithmic
  error amplification `adeg_ε(f) ≤ 56 · adeg_{1/3}(f) · log(1 / ε)` for `0 < ε < 1 / 2`.
* `CslibFrontier.QueryComplexity.approxDegree_third_le_mul_approxDegree_fortyFourHundredths`:
  constant-factor amplification `adeg_{1/3}(f) ≤ 441 · adeg_{11/25}(f)`.
* `CslibFrontier.QueryComplexity.approxDegree_le_randomizedComplexity`: randomized decision tree
  lower bound `adeg_ε(f) ≤ R^{dt}_ε(f)`.
-/

public section

open scoped BigOperators NNReal
open Finset

namespace CslibFrontier.QueryComplexity

/-- Evaluation of the degree-`(2m + 1)` majority polynomial
`M_{2m+1}(u) = ∑_{j = m + 1}^{2m + 1} C(2m + 1, j) uʲ (1 - u)^{2m + 1 - j}`. -/
def majorityPolyEval (m : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    ((2 * m + 1).choose (m + 1 + k) : ℝ) * u ^ (m + 1 + k) * (1 - u) ^ (m - k)

/-- Nonnegativity of `majorityPolyEval m u` on `[0, 1]`. -/
theorem majorityPolyEval_nonneg (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ majorityPolyEval m u := by
  refine Finset.sum_nonneg fun k _ ↦ ?_
  have h1u : 0 ≤ 1 - u := by linarith
  positivity

/-- Symmetry identity `M_{2m+1}(1 - u) = 1 - M_{2m+1}(u)`. -/
theorem majorityPolyEval_one_sub (m : ℕ) (u : ℝ) :
    majorityPolyEval m (1 - u) = 1 - majorityPolyEval m u := by
  have hbinom : ∑ j ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose j : ℝ) * u ^ j * (1 - u) ^ (2 * m + 1 - j) = 1 := by
    have h := add_pow u (1 - u) (2 * m + 1)
    rw [add_sub_cancel, one_pow] at h
    simpa only [show 2 * m + 1 + 1 = 2 * m + 2 by omega, mul_comm, mul_left_comm, mul_assoc]
      using h.symm
  have hsplit : (2 * m + 2) = (m + 1) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add] at hbinom
  have hright : (∑ k ∈ Finset.range (m + 1),
      ((2 * m + 1).choose (m + 1 + k) : ℝ) * u ^ (m + 1 + k) *
        (1 - u) ^ (2 * m + 1 - (m + 1 + k))) = majorityPolyEval m u := by
    unfold majorityPolyEval
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show 2 * m + 1 - (m + 1 + k) = m - k by omega]
  have hleft : (∑ j ∈ Finset.range (m + 1),
      ((2 * m + 1).choose j : ℝ) * u ^ j * (1 - u) ^ (2 * m + 1 - j)) =
        majorityPolyEval m (1 - u) := by
    unfold majorityPolyEval
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hj : m + 1 - 1 - k = m - k := by omega
    rw [hj, sub_sub_cancel, show 2 * m + 1 - (m - k) = m + 1 + k by omega]
    have hch : (2 * m + 1).choose (m - k) = (2 * m + 1).choose (m + 1 + k) := by
      rw [← Nat.choose_symm (by omega : m - k ≤ 2 * m + 1),
        show 2 * m + 1 - (m - k) = m + 1 + k by omega]
    rw [hch]
    ring
  linarith

private theorem sum_choose_upper_half (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), ((2 * m + 1).choose (m + 1 + k) : ℝ)) = 4 ^ m := by
  have htot : (∑ j ∈ Finset.range (2 * m + 2), (2 * m + 1).choose j) = 2 ^ (2 * m + 1) := by
    simpa [show 2 * m + 1 + 1 = 2 * m + 2 by omega] using Nat.sum_range_choose (2 * m + 1)
  have hsplit : (2 * m + 2) = (m + 1) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add] at htot
  have hsym : (∑ j ∈ Finset.range (m + 1), (2 * m + 1).choose j) =
      ∑ k ∈ Finset.range (m + 1), (2 * m + 1).choose (m + 1 + k) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show m + 1 - 1 - k = m - k by omega,
      ← Nat.choose_symm (by omega : m - k ≤ 2 * m + 1),
      show 2 * m + 1 - (m - k) = m + 1 + k by omega]
  rw [hsym, ← two_mul, pow_succ', show (2 : ℕ) ^ (2 * m) = 4 ^ m by
    rw [pow_mul]; norm_num] at htot
  have hhalf : (∑ k ∈ Finset.range (m + 1), (2 * m + 1).choose (m + 1 + k)) = 4 ^ m :=
    Nat.eq_of_mul_eq_mul_left Nat.two_pos htot
  exact_mod_cast hhalf

/-- Concentration of the degree-`(2m + 1)` majority polynomial: for `0 ≤ γ` and
`u ∈ [0, (1 - γ) / 2]`, `M_{2m+1}(u) ≤ (1 / 2) · (1 - γ²)ᵐ`. -/
theorem majorityPolyEval_le_half_mul_one_sub_sq_pow (m : ℕ) {γ u : ℝ}
    (hγ0 : 0 ≤ γ) (hu0 : 0 ≤ u) (huγ : u ≤ (1 - γ) / 2) :
    majorityPolyEval m u ≤ (1 / 2 : ℝ) * (1 - γ ^ 2) ^ m := by
  have hu_half : u ≤ 1 / 2 := by linarith
  have h1u : u ≤ 1 - u := by linarith
  have h1u0 : 0 ≤ 1 - u := by linarith
  have hterm : ∀ k ∈ Finset.range (m + 1),
      u ^ (m + 1 + k) * (1 - u) ^ (m - k) ≤ u * (u * (1 - u)) ^ m := by
    intro k hk
    have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hexp : u ^ (m + 1 + k) * (1 - u) ^ (m - k) =
        u * (u ^ 2) ^ k * (u * (1 - u)) ^ (m - k) := by
      rw [mul_pow, ← pow_mul]
      have h1 : m + 1 + k = 1 + 2 * k + (m - k) := by omega
      rw [h1, pow_add, pow_add, pow_one]
      ring
    rw [hexp]
    have hsq : u ^ 2 ≤ u * (1 - u) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left h1u hu0
    have hpow : (u ^ 2) ^ k ≤ (u * (1 - u)) ^ k :=
      pow_le_pow_left₀ (sq_nonneg u) hsq k
    calc u * (u ^ 2) ^ k * (u * (1 - u)) ^ (m - k)
        ≤ u * (u * (1 - u)) ^ k * (u * (1 - u)) ^ (m - k) := by gcongr
      _ = u * (u * (1 - u)) ^ m := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkle]
  have hsum : majorityPolyEval m u ≤ 4 ^ m * (u * (u * (1 - u)) ^ m) := by
    unfold majorityPolyEval
    calc ∑ k ∈ Finset.range (m + 1),
          ((2 * m + 1).choose (m + 1 + k) : ℝ) * u ^ (m + 1 + k) * (1 - u) ^ (m - k)
        ≤ ∑ k ∈ Finset.range (m + 1),
          ((2 * m + 1).choose (m + 1 + k) : ℝ) * (u * (u * (1 - u)) ^ m) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hterm k hk) (Nat.cast_nonneg _)
      _ = (∑ k ∈ Finset.range (m + 1), ((2 * m + 1).choose (m + 1 + k) : ℝ)) *
            (u * (u * (1 - u)) ^ m) := (Finset.sum_mul _ _ _).symm
      _ = 4 ^ m * (u * (u * (1 - u)) ^ m) := by rw [sum_choose_upper_half]
  have h4u : 4 * (u * (1 - u)) ≤ 1 - γ ^ 2 := by
    have hη : γ ≤ 1 - 2 * u := by linarith
    have hsq : γ ^ 2 ≤ (1 - 2 * u) ^ 2 := pow_le_pow_left₀ hγ0 hη 2
    linarith [show 4 * (u * (1 - u)) = 1 - (1 - 2 * u) ^ 2 by ring]
  calc majorityPolyEval m u
      ≤ 4 ^ m * (u * (u * (1 - u)) ^ m) := hsum
    _ = u * (4 * (u * (1 - u))) ^ m := by
        rw [mul_comm (4 ^ m), mul_assoc, ← mul_pow, mul_comm (u * (1 - u)) 4]
    _ ≤ (1 / 2 : ℝ) * (1 - γ ^ 2) ^ m := by
        exact mul_le_mul hu_half (pow_le_pow_left₀ (by positivity) h4u m)
          (by positivity) (by norm_num)

/-- Composing `majorityPolyEval m` with a cube function in `lowDegree ℝ ι d` yields a function in
`lowDegree ℝ ι ((2 * m + 1) * d)`. -/
theorem majorityPolyEval_comp_mem_lowDegree {ι : Type*} {d : ℕ} {u : (ι → Bool) → ℝ}
    (hu : u ∈ Cslib.BitString.lowDegree ℝ ι d) (m : ℕ) :
    (fun x ↦ majorityPolyEval m (u x)) ∈ Cslib.BitString.lowDegree ℝ ι ((2 * m + 1) * d) := by
  have heq : (fun x ↦ majorityPolyEval m (u x)) =
      ∑ k ∈ Finset.range (m + 1),
        ((2 * m + 1).choose (m + 1 + k) : ℝ) • (u ^ (m + 1 + k) * (1 - u) ^ (m - k)) := by
    funext x
    simp [majorityPolyEval, smul_eq_mul, mul_assoc]
  rw [heq]
  refine Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ ?_
  have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : u ^ (m + 1 + k) ∈ Cslib.BitString.lowDegree ℝ ι ((m + 1 + k) * d) :=
    Cslib.BitString.pow_mem_lowDegree hu _
  have h2 : (1 - u) ^ (m - k) ∈ Cslib.BitString.lowDegree ℝ ι ((m - k) * d) :=
    Cslib.BitString.pow_mem_lowDegree (Cslib.BitString.one_sub_mem_lowDegree hu) _
  have hdeg : (m + 1 + k) * d + (m - k) * d ≤ (2 * m + 1) * d := by
    rw [← Nat.add_mul, show m + 1 + k + (m - k) = 2 * m + 1 by omega]
  exact Cslib.BitString.lowDegree_mono hdeg (Cslib.BitString.mul_mem_lowDegree h1 h2)

/-- General majority amplification for approximate degree: if `ε₀ < 1 / 2` and
`(1 / 2) · (1 - ((1 - 2 ε₀) / (1 + 2 ε₀))²)ᵐ ≤ ε`, then
`adeg_ε(f) ≤ (2m + 1) · adeg_{ε₀}(f)`. -/
theorem approxDegree_le_odd_mul_approxDegree {n : ℕ} (f : Cslib.BooleanFunction n)
    {ε₀ ε : ℝ≥0} (hε₀ : (ε₀ : ℝ) < 1 / 2) (m : ℕ)
    (hm : (1 / 2 : ℝ) * (1 - ((1 - 2 * (ε₀ : ℝ)) / (1 + 2 * (ε₀ : ℝ))) ^ 2) ^ m ≤ ε) :
    Cslib.QueryComplexity.approxDegree ε f ≤
      (2 * m + 1) * Cslib.QueryComplexity.approxDegree ε₀ f := by
  obtain ⟨p, hp, hpf⟩ := Cslib.QueryComplexity.exists_mem_lowDegree_approxDegree
    (ε := ε₀) (f := f)
  have hε₀_nn : (0 : ℝ) ≤ ε₀ := ε₀.2
  have hden : 0 < 1 + 2 * (ε₀ : ℝ) := by linarith
  set γ : ℝ := (1 - 2 * (ε₀ : ℝ)) / (1 + 2 * (ε₀ : ℝ))
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) hden.le
  set u : Cslib.BitString n → ℝ := fun x ↦ (1 + 2 * (ε₀ : ℝ))⁻¹ * (p x + (ε₀ : ℝ))
  have hu : u ∈ Cslib.BitString.lowDegree ℝ (Fin n) (Cslib.QueryComplexity.approxDegree ε₀ f) := by
    have hu_eq : u = (1 + 2 * (ε₀ : ℝ))⁻¹ • (p + fun _ ↦ (ε₀ : ℝ)) := by
      funext x; simp [u]
    rw [hu_eq]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hp
      (Cslib.BitString.const_mem_lowDegree _ _))
  refine Cslib.QueryComplexity.approxDegree_le_of_mem_lowDegree
    (majorityPolyEval_comp_mem_lowDegree hu m) fun x ↦ ?_
  have hx := abs_le.mp (hpf x)
  cases hfx : f x
  · simp only [hfx, Cslib.BitString.bitVal_false, sub_zero] at hx ⊢
    have hu0 : 0 ≤ u x := mul_nonneg (inv_nonneg.mpr hden.le) (by linarith [hx.1])
    have huγ : u x ≤ (1 - γ) / 2 := by
      have hid : (1 - γ) / 2 = (1 + 2 * (ε₀ : ℝ))⁻¹ * (2 * (ε₀ : ℝ)) := by
        simp only [γ]; field_simp; ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left (by linarith [hx.2]) (inv_nonneg.mpr hden.le)
    have hnn := majorityPolyEval_nonneg m hu0 (by linarith)
    have hle := majorityPolyEval_le_half_mul_one_sub_sq_pow m hγ0 hu0 huγ
    rw [abs_of_nonneg hnn]
    exact hle.trans hm
  · simp only [hfx, Cslib.BitString.bitVal_true] at hx ⊢
    have h1u0 : 0 ≤ 1 - u x := by
      have hid : 1 - u x = (1 + 2 * (ε₀ : ℝ))⁻¹ * (1 + (ε₀ : ℝ) - p x) := by
        simp only [u]; field_simp; ring
      rw [hid]
      exact mul_nonneg (inv_nonneg.mpr hden.le) (by linarith [hx.2])
    have h1uγ : 1 - u x ≤ (1 - γ) / 2 := by
      have hid1 : 1 - u x = (1 + 2 * (ε₀ : ℝ))⁻¹ * (1 + (ε₀ : ℝ) - p x) := by
        simp only [u]; field_simp; ring
      have hid2 : (1 - γ) / 2 = (1 + 2 * (ε₀ : ℝ))⁻¹ * (2 * (ε₀ : ℝ)) := by
        simp only [γ]; field_simp; ring
      rw [hid1, hid2]
      exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) (inv_nonneg.mpr hden.le)
    have hsym : majorityPolyEval m (u x) - 1 = -majorityPolyEval m (1 - u x) := by
      linarith [majorityPolyEval_one_sub m (u x)]
    have hnn := majorityPolyEval_nonneg m h1u0 (by linarith)
    have hle := majorityPolyEval_le_half_mul_one_sub_sq_pow m hγ0 h1u0 h1uγ
    rw [hsym, abs_neg, abs_of_nonneg hnn]
    exact hle.trans hm

/-- Logarithmic error reduction for approximate degree: for every Boolean function
`f : {0, 1}ⁿ → {0, 1}` and every `0 < ε < 1 / 2`,
`adeg_ε(f) ≤ 56 · adeg_{1/3}(f) · log(1 / ε)`. -/
theorem approxDegree_le_mul_approxDegree_third_mul_log {n : ℕ} (f : Cslib.BooleanFunction n)
    {ε : ℝ≥0} (hε0 : 0 < (ε : ℝ)) (hε2 : (ε : ℝ) < 1 / 2) :
    (Cslib.QueryComplexity.approxDegree ε f : ℝ) ≤
      56 * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) * Real.log (1 / (ε : ℝ)) := by
  have h2lt : (2 : ℝ) < 1 / (ε : ℝ) := (lt_div_iff₀ hε0).mpr (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hexp : Real.exp (1 / 2) ≤ 2 := by
      have h1 : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
        linarith [Real.add_one_le_exp (-1 / 2)]
      have h2 := Real.exp_neg (1 / 2 : ℝ)
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] at h1
      rw [h2] at h1
      have h3 := (le_inv_comm₀ (by norm_num : (0 : ℝ) < 1 / 2) (Real.exp_pos _)).mp h1
      linarith
    calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
      _ ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) hexp
  have hlog_half : (1 / 2 : ℝ) < Real.log (1 / (ε : ℝ)) :=
    hlog2.trans_lt (Real.log_lt_log (by norm_num) h2lt)
  set m : ℕ := ⌈25 * Real.log (1 / (ε : ℝ))⌉₊
  have hm_ge : 25 * Real.log (1 / (ε : ℝ)) ≤ m := Nat.le_ceil _
  have hm_le : (m : ℝ) ≤ 25 * Real.log (1 / (ε : ℝ)) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hpow : (1 / 2 : ℝ) * (1 - ((1 - 2 * ((1 / 3 : ℝ≥0) : ℝ)) /
      (1 + 2 * ((1 / 3 : ℝ≥0) : ℝ))) ^ 2) ^ m ≤ ε := by
    have hbase : 1 - ((1 - 2 * ((1 / 3 : ℝ≥0) : ℝ)) /
        (1 + 2 * ((1 / 3 : ℝ≥0) : ℝ))) ^ 2 = (24 / 25 : ℝ) := by
      norm_num
    rw [hbase]
    have h24 : (24 / 25 : ℝ) ≤ Real.exp (-1 / 25) := by
      linarith [Real.add_one_le_exp (-1 / 25)]
    calc (1 / 2 : ℝ) * (24 / 25 : ℝ) ^ m
        ≤ 1 * (Real.exp (-1 / 25)) ^ m := by
          exact mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) h24 m)
            (by positivity) zero_le_one
      _ = Real.exp (-(m : ℝ) / 25) := by
          rw [one_mul, ← Real.exp_nat_mul]
          congr 1; ring
      _ ≤ Real.exp (-Real.log (1 / (ε : ℝ))) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = (ε : ℝ) := by
          rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hdeg := approxDegree_le_odd_mul_approxDegree f (ε₀ := 1 / 3) (ε := ε)
    (by norm_num) m hpow
  have hdegR : (Cslib.QueryComplexity.approxDegree ε f : ℝ) ≤
      (2 * (m : ℝ) + 1) * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) := by
    exact_mod_cast hdeg
  have h2m1 : 2 * (m : ℝ) + 1 ≤ 56 * Real.log (1 / (ε : ℝ)) := by linarith
  calc (Cslib.QueryComplexity.approxDegree ε f : ℝ)
      ≤ (2 * (m : ℝ) + 1) * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) := hdegR
    _ ≤ (56 * Real.log (1 / (ε : ℝ))) * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) :=
        mul_le_mul_of_nonneg_right h2m1 (Nat.cast_nonneg _)
    _ = 56 * (Cslib.QueryComplexity.approxDegree (1 / 3) f : ℝ) * Real.log (1 / (ε : ℝ)) := by
        ring

/-- Constant-factor amplification from error `11 / 25` (`0.44`) to standard error `1 / 3`:
`adeg_{1/3}(f) ≤ 441 · adeg_{11/25}(f)`. -/
theorem approxDegree_third_le_mul_approxDegree_fortyFourHundredths {n : ℕ}
    (f : Cslib.BooleanFunction n) :
    Cslib.QueryComplexity.approxDegree (1 / 3) f ≤
      441 * Cslib.QueryComplexity.approxDegree (11 / 25) f := by
  have hpow : (1 / 2 : ℝ) * (1 - ((1 - 2 * ((11 / 25 : ℝ≥0) : ℝ)) /
      (1 + 2 * ((11 / 25 : ℝ≥0) : ℝ))) ^ 2) ^ 220 ≤ ((1 / 3 : ℝ≥0) : ℝ) := by
    have hbase : 1 - ((1 - 2 * ((11 / 25 : ℝ≥0) : ℝ)) /
        (1 + 2 * ((11 / 25 : ℝ≥0) : ℝ))) ^ 2 = (2200 / 2209 : ℝ) := by
      norm_num
    rw [hbase]
    have hstep : (2200 / 2209 : ℝ) ≤ Real.exp (-9 / 2209) := by
      linarith [Real.add_one_le_exp (-9 / 2209)]
    have hexp : Real.exp (-1980 / 2209) ≤ 2 / 3 := by
      have hpos : (3 / 2 : ℝ) ≤ Real.exp (1980 / 2209) := by
        linarith [Real.add_one_le_exp (1980 / 2209)]
      rw [show (-1980 / 2209 : ℝ) = -(1980 / 2209 : ℝ) by ring, Real.exp_neg]
      exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by simpa using hpos)
    calc (1 / 2 : ℝ) * (2200 / 2209 : ℝ) ^ 220
        ≤ (1 / 2 : ℝ) * (Real.exp (-9 / 2209)) ^ 220 := by gcongr
      _ = (1 / 2 : ℝ) * Real.exp (-1980 / 2209) := by
          rw [← Real.exp_nat_mul]; congr 2; norm_num
      _ ≤ (1 / 2 : ℝ) * (2 / 3 : ℝ) := by gcongr
      _ = ((1 / 3 : ℝ≥0) : ℝ) := by norm_num
  simpa using approxDegree_le_odd_mul_approxDegree f (ε₀ := 11 / 25) (ε := 1 / 3)
    (by norm_num) 220 hpow

/-- Approximate degree is bounded above by randomized decision tree query complexity:
`adeg_ε(f) ≤ R^{dt}_ε(f)`. -/
theorem approxDegree_le_randomizedComplexity {n : ℕ} (ε : ℝ≥0) (f : Cslib.BooleanFunction n) :
    Cslib.QueryComplexity.approxDegree ε f ≤
      Cslib.QueryComplexity.randomizedComplexity ε f := by
  obtain ⟨μ, hμ, hd⟩ :=
    Cslib.QueryComplexity.exists_computes_depth_eq_randomizedComplexity (ε := ε) f
  let p : (Fin n → Bool) → ℝ :=
    ∑ t ∈ μ.weights.support, μ.weights t • fun x ↦ Cslib.BitString.bitVal ℝ (t.eval x)
  have hp_deg : p ∈ Cslib.BitString.lowDegree ℝ (Fin n)
      (Cslib.QueryComplexity.randomizedComplexity ε f) := by
    refine Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ _ ?_
    exact Cslib.BitString.lowDegree_mono
      ((Cslib.RandomizedDecisionTree.depth_le_depth ht).trans hd.le)
      (Cslib.DecisionTree.comp_eval_mem_lowDegree (Cslib.BitString.bitVal ℝ) t)
  refine Cslib.QueryComplexity.approxDegree_le_of_mem_lowDegree hp_deg fun x ↦ ?_
  have hsub : p x - Cslib.BitString.bitVal ℝ (f x) =
      ∑ t ∈ μ.weights.support,
        μ.weights t * (Cslib.BitString.bitVal ℝ (t.eval x) -
          Cslib.BitString.bitVal ℝ (f x)) := by
    have htot : ∑ t ∈ μ.weights.support, μ.weights t = 1 := μ.total
    have h1 : Cslib.BitString.bitVal ℝ (f x) =
        ∑ t ∈ μ.weights.support, μ.weights t * Cslib.BitString.bitVal ℝ (f x) := by
      rw [← Finset.sum_mul, htot, one_mul]
    simp only [p, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rhs; rw [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ ↦ (mul_sub _ _ _).symm
  rw [hsub]
  calc |∑ t ∈ μ.weights.support,
          μ.weights t * (Cslib.BitString.bitVal ℝ (t.eval x) -
            Cslib.BitString.bitVal ℝ (f x))|
      ≤ ∑ t ∈ μ.weights.support,
          |μ.weights t * (Cslib.BitString.bitVal ℝ (t.eval x) -
            Cslib.BitString.bitVal ℝ (f x))| := Finset.abs_sum_le_sum_abs _ _
    _ = μ.errorProb f x := by
        rw [Cslib.RandomizedDecisionTree.errorProb_eq_sum, Finsupp.sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (μ.weights_nonneg t)]
        congr 1
        cases t.eval x <;> cases f x <;> simp [Cslib.BitString.bitVal]
    _ ≤ ε := hμ x

end CslibFrontier.QueryComplexity
