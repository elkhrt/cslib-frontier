/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import CslibFrontier.Foundations.Probability.AzumaPi
import CslibFrontier.Foundations.Probability.BernsteinPi
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Dimension-Free Empirical `ℓ_∞` Concentration and Uniform Hoeffding Bounds

Greedy mass-bounded block partitioning, Canonne's dimension-free empirical `ℓ_∞`
concentration inequality for discrete distributions over arbitrary finite alphabets, and
finite-family uniform Hoeffding confidence bounds:

1. **Empirical frequencies and discrete `PMF` expectations**: `empiricalFreq`, range and
   normalization lemmas, empirical expectation identity `sum_empiricalFreq_mul`, and finite-alphabet
   `PMF.toMeasure` integration `integral_pmf_toMeasure`.
2. **Greedy mass-bounded block partition**: `exists_greedy_mass_partition` covers any light subset
   `S` (`∀ x ∈ S, 0 ≤ p x ∧ p x ≤ η / 4`) by pairwise disjoint nonempty blocks of mass at most
   `η / 2` whose count satisfies `(L.length : ℝ) ≤ 4 * (∑ x ∈ S, p x) / η + 1`.
3. **Dimension-free empirical `ℓ_∞` concentration**: subset-mass
   Bernstein tail bound `measureReal_abs_sum_empiricalFreq_sub_ge_le_of_pmf` and alphabet-free
   sample complexity `(20 / (min η 1) ^ 2) * Real.log (400 / δ) ≤ N` (and
   `(200 / (min η 1) ^ 2) * Real.log (1 / δ) ≤ N` for `δ ≤ 1 / 2`) guaranteeing
   `∀ x, |empiricalFreq X ω x - (q x).toReal| ≤ η` with probability at least `1 - δ`.
4. **Uniform Hoeffding confidence bound**: `uniform_hoeffding_confidence` bounds simultaneous
   deviations of `N` i.i.d. empirical averages across a nonempty finite family `f : Y → α → ℝ`
   taking values in `[0, c_bar]`.

## Main definitions

* `CslibFrontier.Probability.empiricalFreq`: empirical frequency
  `N⁻¹ ∑_{k=0}^{N-1} 1_{X_k(ω) = x}`.

## Main results

* `CslibFrontier.Probability.sum_finset_empiricalFreq`,
  `CslibFrontier.Probability.sum_empiricalFreq`,
  `CslibFrontier.Probability.sum_empiricalFreq_mul`,
  `CslibFrontier.Probability.integral_pmf_toMeasure`: empirical frequency summation and finite
  `PMF` expectation identities.
* `CslibFrontier.Probability.exists_greedy_mass_partition`: greedy mass-bounded partition of light
  elements.
* `CslibFrontier.Probability.measureReal_abs_sum_empiricalFreq_sub_ge_le_of_pmf`,
  `CslibFrontier.Probability.measureReal_exists_lt_abs_empiricalFreq_sub_le_of_pmf`,
  `CslibFrontier.Probability.measureReal_forall_abs_empiricalFreq_sub_le_of_pmf`,
  `CslibFrontier.Probability.measureReal_forall_abs_empiricalFreq_sub_le_of_pmf_half`: Canonne's
  dimension-free empirical `ℓ_∞` concentration inequality.
* `CslibFrontier.Probability.uniform_hoeffding_confidence`: finite-family uniform Hoeffding
  confidence bound.

## Tags

empirical distribution, concentration inequality, Bernstein inequality, Hoeffding inequality,
discrete distribution learning
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace CslibFrontier.Probability

/-! ### 1. Empirical frequencies and discrete `PMF` expectations -/

section EmpiricalFreq

/-- Empirical frequency `N⁻¹ ∑_{k=0}^{N-1} 1_{X_k(ω) = x}` of outcome `x : α` in an `N`-sample
trajectory `X · ω`. -/
noncomputable def empiricalFreq {N : ℕ} {Ω α : Type*} [DecidableEq α]
    (X : Fin N → Ω → α) (ω : Ω) (x : α) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k : Fin N, if X k ω = x then 1 else 0

/-- Empirical frequencies are nonnegative. -/
theorem empiricalFreq_nonneg {N : ℕ} {Ω α : Type*} [DecidableEq α]
    (X : Fin N → Ω → α) (ω : Ω) (x : α) :
    0 ≤ empiricalFreq X ω x := by
  unfold empiricalFreq
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num)

/-- Empirical frequencies are at most `1`. -/
theorem empiricalFreq_le_one {N : ℕ} {Ω α : Type*} [DecidableEq α]
    (X : Fin N → Ω → α) (ω : Ω) (x : α) :
    empiricalFreq X ω x ≤ 1 := by
  unfold empiricalFreq
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hle : (∑ k : Fin N, if X k ω = x then (1 : ℝ) else 0) ≤ N := by
      calc
        (∑ k : Fin N, if X k ω = x then (1 : ℝ) else 0)
            ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦ by split_ifs <;> norm_num
        _ = N := by simp
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    exact (inv_mul_le_iff₀ hN_pos).mpr (by simpa using hle)

/-- The empirical mass of a finite subset `A : Finset α` equals the sample average of `1_{· ∈ A}`.
-/
theorem sum_finset_empiricalFreq {N : ℕ} {Ω α : Type*} [DecidableEq α]
    (X : Fin N → Ω → α) (ω : Ω) (A : Finset α) :
    ∑ x ∈ A, empiricalFreq X ω x = (N : ℝ)⁻¹ * ∑ k : Fin N, if X k ω ∈ A then 1 else 0 := by
  unfold empiricalFreq
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : X k ω ∈ A
  · rw [Finset.sum_eq_single (X k ω)]
    · simp [hk]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hnot
      exact (hnot hk).elim
  · simp only [hk, ↓reduceIte]
    exact Finset.sum_eq_zero fun x hx ↦ by simp [show X k ω ≠ x from fun h ↦ hk (h ▸ hx)]

/-- When `1 ≤ N`, the empirical frequencies over a finite alphabet sum to `1`. -/
theorem sum_empiricalFreq {N : ℕ} (hN : 1 ≤ N) {Ω α : Type*} [Fintype α] [DecidableEq α]
    (X : Fin N → Ω → α) (ω : Ω) :
    ∑ x : α, empiricalFreq X ω x = 1 := by
  rw [sum_finset_empiricalFreq]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [hN0]

/-- Expectation of `f : α → ℝ` against `empiricalFreq X ω` equals the sample average of `f`. -/
theorem sum_empiricalFreq_mul {N : ℕ} {Ω α : Type*} [Fintype α] [DecidableEq α]
    (X : Fin N → Ω → α) (ω : Ω) (f : α → ℝ) :
    ∑ x : α, empiricalFreq X ω x * f x = (N : ℝ)⁻¹ * ∑ k : Fin N, f (X k ω) := by
  unfold empiricalFreq
  calc
    ∑ x : α, ((N : ℝ)⁻¹ * ∑ k : Fin N, if X k ω = x then (1 : ℝ) else 0) * f x
        = ∑ x : α, (N : ℝ)⁻¹ * ∑ k : Fin N, (if X k ω = x then (1 : ℝ) else 0) * f x :=
          Finset.sum_congr rfl fun x _ ↦ by rw [mul_assoc, Finset.sum_mul]
    _ = (N : ℝ)⁻¹ * ∑ k : Fin N, ∑ x : α, (if X k ω = x then (1 : ℝ) else 0) * f x := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (N : ℝ)⁻¹ * ∑ k : Fin N, f (X k ω) := by
          congr 1
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_eq_single (X k ω)]
          · simp
          · intro x _ hx
            simp [Ne.symm hx]
          · intro hnot
            exact (hnot (Finset.mem_univ _)).elim

private lemma integrable_pmf_toMeasure {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (q : PMF α) (f : α → ℝ) :
    Integrable f q.toMeasure := by
  cases nonempty_fintype α
  have hf_meas : Measurable f := fun s _ ↦ (f ⁻¹' s).toFinite.measurableSet
  exact Integrable.of_bound hf_meas.aestronglyMeasurable (∑ y : α, |f y|)
    (Eventually.of_forall fun x ↦
      (Real.norm_eq_abs (f x)).trans_le
        (Finset.single_le_sum (fun y _ ↦ abs_nonneg (f y)) (Finset.mem_univ x)))

/-- Bochner integral of `f : α → ℝ` under `q.toMeasure` on a finite discrete measurable space. -/
theorem integral_pmf_toMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (q : PMF α) (f : α → ℝ) :
    ∫ x, f x ∂q.toMeasure = ∑ x : α, (q x).toReal * f x := by
  rw [integral_fintype (integrable_pmf_toMeasure q f)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [measureReal_def, q.toMeasure_apply_singleton x (measurableSet_singleton x), smul_eq_mul]

end EmpiricalFreq

/-! ### 2. Greedy mass-bounded block partition -/

section GreedyPartition

/-- **Greedy mass-bounded block partition.** Any finite set `S` of light elements
(`∀ x ∈ S, 0 ≤ p x ∧ p x ≤ η / 4`, `0 < η`) admits a pairwise disjoint list `L` of nonempty
subsets covering `S` such that every block has mass at most `η / 2`, every non-terminal block has
mass strictly greater than `η / 4`, and `(L.length : ℝ) ≤ 4 * (∑ x ∈ S, p x) / η + 1`. -/
theorem exists_greedy_mass_partition {α : Type*} [DecidableEq α] (p : α → ℝ)
    {η : ℝ} (hη : 0 < η) (S : Finset α) (hS : ∀ x ∈ S, 0 ≤ p x ∧ p x ≤ η / 4) :
    ∃ L : List (Finset α),
      L.Pairwise Disjoint ∧
      (∀ B ∈ L, B ⊆ S ∧ B.Nonempty ∧ ∑ x ∈ B, p x ≤ η / 2) ∧
      (∀ x ∈ S, ∃ B ∈ L, x ∈ B) ∧
      (∑ B ∈ L.toFinset, ∑ x ∈ B, p x = ∑ x ∈ S, p x) ∧
      (∀ i : ℕ, (hi : i + 1 < L.length) → η / 4 < ∑ x ∈ L[i], p x) ∧
      (L.length : ℝ) ≤ 4 * (∑ x ∈ S, p x) / η + 1 := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS_ne
    · refine ⟨[], List.Pairwise.nil, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
    · classical
      let cand : Finset (Finset α) :=
        S.powerset.filter (fun B ↦ B.Nonempty ∧ ∑ x ∈ B, p x ≤ η / 2)
      have hcand_ne : cand.Nonempty := by
        obtain ⟨x₀, hx₀⟩ := hS_ne
        refine ⟨{x₀}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (Finset.singleton_subset_iff.mpr hx₀), Finset.singleton_nonempty x₀, ?_⟩⟩
        rw [Finset.sum_singleton]
        linarith [(hS x₀ hx₀).2]
      obtain ⟨B, hB_cand, hB_max⟩ := Finset.exists_max_image cand Finset.card hcand_ne
      rw [Finset.mem_filter, Finset.mem_powerset] at hB_cand
      rcases hB_cand with ⟨hB_sub, hB_ne, hB_sum⟩
      let S' : Finset α := S \ B
      have hS'_card : S'.card < n := hn ▸ Finset.card_lt_card (Finset.sdiff_ssubset hB_sub hB_ne)
      have hS'_prop : ∀ x ∈ S', 0 ≤ p x ∧ p x ≤ η / 4 :=
        fun x hx ↦ hS x (Finset.sdiff_subset hx)
      obtain ⟨L', hL'_disj, hL'_mem, hL'_cov, hL'_sum, hL'_heavy, hL'_len⟩ :=
        ih S'.card hS'_card S' hS'_prop rfl
      have hB_heavy : L' ≠ [] → η / 4 < ∑ x ∈ B, p x := by
        intro hL'_ne
        have hpos : 0 < L'.length := List.length_pos_iff.mpr hL'_ne
        have hhead_mem : L'[0] ∈ L' := List.getElem_mem hpos
        obtain ⟨y, hy0⟩ := (hL'_mem (L'[0]) hhead_mem).2.1
        have hy := (hL'_mem (L'[0]) hhead_mem).1 hy0
        rw [Finset.mem_sdiff] at hy
        rcases hy with ⟨hyS, hyB⟩
        have hnot_cand : insert y B ∉ cand := by
          intro hmem
          have hcard := hB_max (insert y B) hmem
          rw [Finset.card_insert_of_notMem hyB] at hcard
          omega
        have hgt : η / 2 < ∑ x ∈ insert y B, p x := by
          by_contra hle
          exact hnot_cand (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (Finset.insert_subset_iff.mpr ⟨hyS, hB_sub⟩),
            Finset.insert_nonempty y B, not_lt.mp hle⟩)
        rw [Finset.sum_insert hyB] at hgt
        linarith [(hS y hyS).2]
      refine ⟨B :: L', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun C hC ↦ Disjoint.mono_right (hL'_mem C hC).1 disjoint_sdiff_self_right,
          hL'_disj⟩
      · intro C hC
        rcases List.mem_cons.mp hC with rfl | hC'
        · exact ⟨hB_sub, hB_ne, hB_sum⟩
        · rcases hL'_mem C hC' with ⟨hC_sub, hC_ne, hC_sum⟩
          exact ⟨hC_sub.trans Finset.sdiff_subset, hC_ne, hC_sum⟩
      · intro x hx
        by_cases hxB : x ∈ B
        · exact ⟨B, List.mem_cons_self, hxB⟩
        · obtain ⟨C, hC, hxC⟩ := hL'_cov x (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
          exact ⟨C, List.mem_cons_of_mem B hC, hxC⟩
      · have hB_not_mem : B ∉ L' := fun hBL' ↦ by
          have hdisj : Disjoint B B :=
            Disjoint.mono_right (hL'_mem B hBL').1 disjoint_sdiff_self_right
          obtain ⟨x, hx⟩ := hB_ne
          exact Finset.disjoint_left.mp hdisj hx hx
        rw [List.toFinset_cons, Finset.sum_insert (List.mem_toFinset.not.mpr hB_not_mem),
          hL'_sum, add_comm, Finset.sum_sdiff hB_sub]
      · intro i hi
        cases i with
        | zero => exact hB_heavy (List.length_pos_iff.mp (Nat.succ_lt_succ_iff.mp hi))
        | succ j => exact hL'_heavy j (Nat.succ_lt_succ_iff.mp hi)
      · rcases eq_or_ne L' [] with rfl | hL'_ne
        · have hS_nn : 0 ≤ ∑ x ∈ S, p x := Finset.sum_nonneg fun x hx ↦ (hS x hx).1
          have hdiv_nn : 0 ≤ 4 * (∑ x ∈ S, p x) / η := by positivity
          simp only [List.length_cons, List.length_nil, zero_add, Nat.cast_one]
          linarith
        · have h1_lt : 1 < 4 * (∑ x ∈ B, p x) / η :=
            (one_lt_div hη).mpr (by linarith [hB_heavy hL'_ne])
          have hsum_eq : ∑ x ∈ S, p x = (∑ x ∈ S', p x) + ∑ x ∈ B, p x :=
            (Finset.sum_sdiff hB_sub).symm
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          rw [hsum_eq, mul_add, add_div]
          linarith

end GreedyPartition

/-! ### 3. Dimension-free empirical `ℓ_∞` concentration -/

section EmpiricalLInf

private lemma sum_pmf_toReal_eq_one {α : Type*} [Fintype α] (q : PMF α) :
    ∑ x : α, (q x).toReal = 1 := by
  have hsum : ∑ x : α, q x = 1 := by simpa [tsum_fintype] using q.tsum_coe
  rw [← ENNReal.toReal_sum (fun x _ ↦ q.apply_ne_top x), hsum, ENNReal.toReal_one]

private lemma pmf_toReal_le_one {α : Type*} [Finite α] (q : PMF α) (x : α) :
    (q x).toReal ≤ 1 := by
  cases nonempty_fintype α
  rw [← sum_pmf_toReal_eq_one q]
  exact Finset.single_le_sum (fun y _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ x)

/-- **Subset empirical-mass Bernstein tail bound.** For `N ≥ 1` mutually independent samples
drawn from `q : PMF α` on a finite discrete measurable space and any subset `A : Finset α`, the
empirical mass `∑ x ∈ A, empiricalFreq X ω x` deviates from `∑ x ∈ A, (q x).toReal` by at least
`t ≥ 0` with probability at most
`2 * exp (-N * t ^ 2 / (2 * ((∑ x ∈ A, (q x).toReal) + (2 / 3) * t)))`. -/
theorem measureReal_abs_sum_empiricalFreq_sub_ge_le_of_pmf {N : ℕ} {Ω α : Type*}
    [MeasurableSpace Ω] [Finite α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} {X : Fin N → Ω → α}
    (hN : 1 ≤ N) (h_indep : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ)
    (q : PMF α) (h_law : ∀ i, μ.map (X i) = q.toMeasure)
    (A : Finset α) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ x ∈ A, empiricalFreq X ω x - ∑ x ∈ A, (q x).toReal|} ≤
      2 * Real.exp (-(N : ℝ) * t ^ 2 / (2 * ((∑ x ∈ A, (q x).toReal) + (2 / 3) * t))) := by
  cases nonempty_fintype α
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp only [sq, mul_zero, zero_div, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    let ν : Fin N → Measure α := fun _ ↦ q.toMeasure
    have hmap_pi : μ.map (fun ω i ↦ X i ω) = Measure.pi ν :=
      (h_indep.map_fun_eq_pi_map hX).trans (by simp_rw [h_law]; rfl)
    set m : ℝ := ∑ x ∈ A, (q x).toReal
    have hm0 : 0 ≤ m := Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
    have hm1 : m ≤ 1 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        fun _ _ _ ↦ ENNReal.toReal_nonneg).trans_eq (sum_pmf_toReal_eq_one q)
    let φ : α → ℝ := fun x ↦ if x ∈ A then 1 else 0
    have hφ_meas : Measurable φ := fun s _ ↦ (φ ⁻¹' s).toFinite.measurableSet
    have hφ_sq : ∀ x : α, (φ x) ^ 2 = φ x := fun x ↦ by
      dsimp only [φ]
      split_ifs <;> norm_num
    have hint_φ : ∑ x : α, (q x).toReal * φ x = m := by
      simp [φ, m, Finset.sum_ite_mem]
    have hq_sum : ∑ x : α, (q x).toReal = 1 := sum_pmf_toReal_eq_one q
    have hvar_base : ∫ z, (φ z - m) ^ 2 ∂q.toMeasure ≤ m := by
      rw [integral_pmf_toMeasure]
      have hpt : ∀ x : α, (q x).toReal * (φ x - m) ^ 2 =
          (q x).toReal * φ x - 2 * m * ((q x).toReal * φ x) + m ^ 2 * (q x).toReal := fun x ↦ by
        calc
          (q x).toReal * (φ x - m) ^ 2
              = (q x).toReal * (φ x ^ 2 - 2 * m * φ x + m ^ 2) := by ring
          _ = (q x).toReal * φ x - 2 * m * ((q x).toReal * φ x) + m ^ 2 * (q x).toReal := by
              rw [hφ_sq x]; ring
      simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hint_φ, hq_sum]
      nlinarith [sq_nonneg m]
    let Ypos : Fin N → (Fin N → α) → ℝ := fun i v ↦ φ (v i) - m
    let Yneg : Fin N → (Fin N → α) → ℝ := fun i v ↦ m - φ (v i)
    have hYpos_meas : ∀ i : Fin N, Measurable (Ypos i) :=
      fun i ↦ (hφ_meas.comp (measurable_pi_apply i)).sub measurable_const
    have hYneg_meas : ∀ i : Fin N, Measurable (Yneg i) :=
      fun i ↦ measurable_const.sub (hφ_meas.comp (measurable_pi_apply i))
    have hbern_pos := measure_sum_ge_le_bernstein_pi (μ := ν) (Y := Ypos)
      (b := 1) (ε := (N : ℝ) * t) (s2 := fun _ : Fin N ↦ m)
      zero_le_one (fun _ ↦ hm0) (by positivity) hYpos_meas
      (fun i j hij v z ↦ by simp [Ypos, Function.update_of_ne hij.ne])
      (fun i v ↦ integrable_pmf_toMeasure q _)
      (fun i v ↦ integrable_pmf_toMeasure q _)
      (fun i v ↦ by
        simp only [Ypos, Function.update_self, ν]
        rw [integral_pmf_toMeasure]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hint_φ, hq_sum, one_mul, sub_self])
      (fun i v ↦ by
        dsimp only [Ypos, φ]
        split_ifs <;> linarith)
      (fun i v ↦ by simpa only [Ypos, Function.update_self, ν] using hvar_base)
    have hbern_neg := measure_sum_ge_le_bernstein_pi (μ := ν) (Y := Yneg)
      (b := 1) (ε := (N : ℝ) * t) (s2 := fun _ : Fin N ↦ m)
      zero_le_one (fun _ ↦ hm0) (by positivity) hYneg_meas
      (fun i j hij v z ↦ by simp [Yneg, Function.update_of_ne hij.ne])
      (fun i v ↦ integrable_pmf_toMeasure q _)
      (fun i v ↦ integrable_pmf_toMeasure q _)
      (fun i v ↦ by
        simp only [Yneg, Function.update_self, ν]
        rw [integral_pmf_toMeasure]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hint_φ, hq_sum, one_mul, sub_self])
      (fun i v ↦ by
        dsimp only [Yneg, φ]
        split_ifs <;> linarith)
      (fun i v ↦ by
        simp only [Yneg, Function.update_self, ν]
        simpa only [sub_sq_comm m] using hvar_base)
    have hexp_le :
        Real.exp (-((N : ℝ) * t) ^ 2 / (2 * ((∑ _ : Fin N, m) + 1 * ((N : ℝ) * t) / 3))) ≤
          Real.exp (-(N : ℝ) * t ^ 2 / (2 * (m + (2 / 3) * t))) := by
      refine Real.exp_le_exp.mpr ?_
      have hsum_m : (∑ _ : Fin N, m) = (N : ℝ) * m := by simp [nsmul_eq_mul]
      rw [hsum_m,
        show -((N : ℝ) * t) ^ 2 / (2 * ((N : ℝ) * m + 1 * ((N : ℝ) * t) / 3)) =
          -((N : ℝ) * t ^ 2 / (2 * (m + t / 3))) by field_simp [hN_pos.ne'],
        show -(N : ℝ) * t ^ 2 / (2 * (m + (2 / 3) * t)) =
          -((N : ℝ) * t ^ 2 / (2 * (m + (2 / 3) * t))) by ring]
      exact neg_le_neg (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
    let Epos : Set (Fin N → α) := {v | (N : ℝ) * t ≤ ∑ i : Fin N, Ypos i v}
    let Eneg : Set (Fin N → α) := {v | (N : ℝ) * t ≤ ∑ i : Fin N, Yneg i v}
    have hE_meas : MeasurableSet (Epos ∪ Eneg) :=
      (measurableSet_le measurable_const
        (Finset.measurable_sum Finset.univ fun i _ ↦ hYpos_meas i)).union
      (measurableSet_le measurable_const
        (Finset.measurable_sum Finset.univ fun i _ ↦ hYneg_meas i))
    have hsub :
        {ω | t ≤ |∑ x ∈ A, empiricalFreq X ω x - m|} ⊆
          (fun ω i ↦ X i ω) ⁻¹' (Epos ∪ Eneg) := fun ω hω ↦ by
      rw [Set.mem_ofPred_eq, sum_finset_empiricalFreq] at hω
      have hmul : (N : ℝ) * t ≤ |(∑ k : Fin N, φ (X k ω)) - (N : ℝ) * m| := by
        have h1 := mul_le_mul_of_nonneg_left hω hN_pos.le
        have h2 : |(∑ k : Fin N, φ (X k ω)) - (N : ℝ) * m| =
            (N : ℝ) * |((N : ℝ)⁻¹ * ∑ k : Fin N, φ (X k ω)) - m| := by
          calc
            |(∑ k : Fin N, φ (X k ω)) - (N : ℝ) * m|
                = |(N : ℝ) * (((N : ℝ)⁻¹ * ∑ k : Fin N, φ (X k ω)) - m)| :=
                  congrArg abs (by field_simp [hN_pos.ne'])
            _ = (N : ℝ) * |((N : ℝ)⁻¹ * ∑ k : Fin N, φ (X k ω)) - m| := by
                  rw [abs_mul, abs_of_pos hN_pos]
        rwa [← h2] at h1
      have hpos_sum : (∑ i : Fin N, Ypos i (fun k ↦ X k ω)) =
          (∑ k : Fin N, φ (X k ω)) - (N : ℝ) * m := by
        simp [Ypos, Finset.sum_sub_distrib, nsmul_eq_mul]
      have hneg_sum : (∑ i : Fin N, Yneg i (fun k ↦ X k ω)) =
          -((∑ k : Fin N, φ (X k ω)) - (N : ℝ) * m) := by
        simp [Yneg, Finset.sum_sub_distrib, nsmul_eq_mul]
      rcases le_abs.mp hmul with h1 | h2
      · exact Or.inl (by dsimp only [Epos]; rw [Set.mem_ofPred_eq, hpos_sum]; exact h1)
      · exact Or.inr (by dsimp only [Eneg]; rw [Set.mem_ofPred_eq, hneg_sum]; exact h2)
    have hpre : μ.real ((fun ω i ↦ X i ω) ⁻¹' (Epos ∪ Eneg)) =
        (Measure.pi ν).real (Epos ∪ Eneg) := by
      rw [measureReal_def, measureReal_def, ← hmap_pi,
        Measure.map_apply_of_aemeasurable (.of_eval hX) hE_meas]
    calc
      μ.real {ω | t ≤ |∑ x ∈ A, empiricalFreq X ω x - m|}
          ≤ μ.real ((fun ω i ↦ X i ω) ⁻¹' (Epos ∪ Eneg)) := measureReal_mono hsub
      _ = (Measure.pi ν).real (Epos ∪ Eneg) := hpre
      _ ≤ (Measure.pi ν).real Epos + (Measure.pi ν).real Eneg := measureReal_union_le Epos Eneg
      _ ≤ Real.exp (-(N : ℝ) * t ^ 2 / (2 * (m + (2 / 3) * t))) +
            Real.exp (-(N : ℝ) * t ^ 2 / (2 * (m + (2 / 3) * t))) :=
          add_le_add (hbern_pos.trans hexp_le) (hbern_neg.trans hexp_le)
      _ = 2 * Real.exp (-(N : ℝ) * t ^ 2 / (2 * (m + (2 / 3) * t))) := by ring

private lemma forall_abs_empiricalFreq_sub_le_of_blocks {N : ℕ} {Ω α : Type*}
    [Fintype α] [DecidableEq α] {X : Fin N → Ω → α} {p : α → ℝ}
    (hp_nn : ∀ x, 0 ≤ p x) {η : ℝ} (hη : 0 < η)
    {L : List (Finset α)}
    (hL_mem : ∀ B ∈ L,
      B ⊆ Finset.univ.filter (fun x ↦ p x ≤ η / 4) ∧ B.Nonempty ∧ ∑ x ∈ B, p x ≤ η / 2)
    (hL_cov : ∀ x ∈ Finset.univ.filter (fun x ↦ p x ≤ η / 4), ∃ B ∈ L, x ∈ B)
    {ω : Ω}
    (hH : ∀ x ∈ Finset.univ.filter (fun x ↦ η / 4 < p x), |empiricalFreq X ω x - p x| < η)
    (hL : ∀ B ∈ L, |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x| < η / 2) :
    ∀ x : α, |empiricalFreq X ω x - p x| ≤ η := by
  intro x
  by_cases hxH : x ∈ Finset.univ.filter (fun y ↦ η / 4 < p y)
  · exact (hH x hxH).le
  · have hxS : x ∈ Finset.univ.filter (fun y ↦ p y ≤ η / 4) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ x, not_lt.mp fun h ↦ hxH (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)⟩
    obtain ⟨B, hBL, hxB⟩ := hL_cov x hxS
    rcases hL_mem B hBL with ⟨_, _, hB_mass⟩
    have hupper : empiricalFreq X ω x - p x ≤ η := by
      have hle_sum : empiricalFreq X ω x ≤ ∑ y ∈ B, empiricalFreq X ω y :=
        Finset.single_le_sum (fun y _ ↦ empiricalFreq_nonneg X ω y) hxB
      have hpx_nn : 0 ≤ p x := hp_nn x
      linarith [(abs_lt.mp (hL B hBL)).2]
    have hlower : -(empiricalFreq X ω x - p x) ≤ η := by
      have hpx_le : p x ≤ η / 4 := (Finset.mem_filter.mp hxS).2
      have hfreq_nn : 0 ≤ empiricalFreq X ω x := empiricalFreq_nonneg X ω x
      linarith
    exact abs_le.mpr ⟨by linarith, hupper⟩

private lemma log_400_div_ge_one {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ Real.log (400 / δ) := by
  have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h1_le_div : 1 ≤ 1 / δ := one_le_one_div hδ0 hδ1
  have h400 : Real.exp 1 ≤ 400 / δ := by
    rw [show (400 : ℝ) / δ = 400 * (1 / δ) by ring]
    nlinarith
  exact (Real.le_log_iff_exp_le (div_pos (by norm_num) hδ0)).mpr h400

private lemma two_mul_exp_heavy_le {N : ℕ} {α : Type*} [Finite α] (q : PMF α)
    {η δ : ℝ} (hη : 0 < η) (hδ0 : 0 < δ)
    (hlog1 : 1 ≤ Real.log (400 / δ))
    (hNeta : 20 * Real.log (400 / δ) ≤ (N : ℝ) * η ^ 2)
    {x : α} (hx : η / 4 < (q x).toReal) :
    2 * Real.exp (-(N : ℝ) * η ^ 2 / (2 * ((q x).toReal + (2 / 3) * η))) ≤
      (1 / 2) * δ * (q x).toReal := by
  set px : ℝ := (q x).toReal
  have hpx_pos : 0 < px := by linarith
  have hpx_le_one : px ≤ 1 := pmf_toReal_le_one q x
  have hNeta_pos : 0 < (N : ℝ) * η ^ 2 := by linarith
  have hNeta_20 : 20 ≤ (N : ℝ) * η ^ 2 := by linarith
  have hdenom_pos : 0 < 2 * (px + (2 / 3) * η) := by positivity
  have hdenom_le : 2 * (px + (2 / 3) * η) ≤ (15 / 2) * px := by linarith
  let z : ℝ := (N : ℝ) * η ^ 2 / (15 * px)
  have hz_pos : 0 < z := by positivity
  have hexp_le : -(N : ℝ) * η ^ 2 / (2 * (px + (2 / 3) * η)) ≤ -z + -z := by
    have hdiv_le : (N : ℝ) * η ^ 2 / ((15 / 2) * px) ≤
        (N : ℝ) * η ^ 2 / (2 * (px + (2 / 3) * η)) := by gcongr
    rw [show -(N : ℝ) * η ^ 2 = -((N : ℝ) * η ^ 2) by ring,
      show -z + -z = -((N : ℝ) * η ^ 2) / ((15 / 2) * px) by dsimp only [z]; ring,
      neg_div, neg_div]
    exact neg_le_neg hdiv_le
  have hlog_le_z : Real.log (400 / δ) ≤ z := by
    have h1 : Real.log (400 / δ) ≤ (N : ℝ) * η ^ 2 / 15 := by linarith
    have h2 : (N : ℝ) * η ^ 2 / 15 ≤ (N : ℝ) * η ^ 2 / (15 * px) := by
      gcongr
      nlinarith
    exact h1.trans h2
  have hexp_first : Real.exp (-z) ≤ δ / 400 := by
    have h400_pos : (0 : ℝ) < 400 / δ := div_pos (by norm_num) hδ0
    calc
      Real.exp (-z) ≤ Real.exp (-Real.log (400 / δ)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlog_le_z)
      _ = δ / 400 := by rw [Real.exp_neg, Real.exp_log h400_pos, inv_div]
  have hexp_second : Real.exp (-z) ≤ (3 / 4) * px := by
    have hadd : z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
    have hinv : Real.exp (-z) ≤ z⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hz_pos hadd
    have hz_inv : z⁻¹ ≤ (3 / 4) * px := by
      have hz_inv_eq : z⁻¹ = 15 * px / ((N : ℝ) * η ^ 2) := by
        dsimp only [z]
        field_simp
      rw [hz_inv_eq, div_le_iff₀ hNeta_pos]
      nlinarith
    exact hinv.trans hz_inv
  calc
    2 * Real.exp (-(N : ℝ) * η ^ 2 / (2 * (px + (2 / 3) * η)))
        ≤ 2 * Real.exp (-z + -z) := by gcongr
    _ = 2 * (Real.exp (-z) * Real.exp (-z)) := by rw [Real.exp_add]
    _ ≤ 2 * ((δ / 400) * ((3 / 4) * px)) := by gcongr
    _ ≤ (1 / 2) * δ * px := by
        have hdp : 0 ≤ δ * px := mul_nonneg hδ0.le hpx_pos.le
        nlinarith

private lemma two_mul_exp_light_le {N : ℕ} {η δ m : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ0 : 0 < δ) (hm0 : 0 ≤ m) (hm_le : m ≤ η / 2)
    (hNeta : 20 * Real.log (400 / δ) ≤ (N : ℝ) * η ^ 2)
    (hNeta_20 : 20 ≤ (N : ℝ) * η ^ 2) :
    2 * Real.exp (-(N : ℝ) * (η / 2) ^ 2 / (2 * (m + (2 / 3) * (η / 2)))) ≤ η * (δ / 200) := by
  have hdenom_pos : 0 < 2 * (m + (2 / 3) * (η / 2)) := by positivity
  have hdenom_le : 2 * (m + (2 / 3) * (η / 2)) ≤ (5 / 3) * η := by linarith
  have hexp_le : -(N : ℝ) * (η / 2) ^ 2 / (2 * (m + (2 / 3) * (η / 2))) ≤
      -(1 / 20) * (N : ℝ) * η + -(1 / 10) * (N : ℝ) * η := by
    have hdiv_le : (N : ℝ) * (η / 2) ^ 2 / ((5 / 3) * η) ≤
        (N : ℝ) * (η / 2) ^ 2 / (2 * (m + (2 / 3) * (η / 2))) := by gcongr
    rw [show -(N : ℝ) * (η / 2) ^ 2 = -((N : ℝ) * (η / 2) ^ 2) by ring,
      show -(1 / 20) * (N : ℝ) * η + -(1 / 10) * (N : ℝ) * η =
        -((N : ℝ) * (η / 2) ^ 2) / ((5 / 3) * η) by field_simp [hη.ne']; ring,
      neg_div, neg_div]
    exact neg_le_neg hdiv_le
  have hexp_eta : Real.exp (-(1 / 20) * (N : ℝ) * η) ≤ η := by
    have hinv_le : η⁻¹ ≤ (1 / 20) * (N : ℝ) * η := by
      rw [inv_le_iff_one_le_mul₀' hη]
      nlinarith
    have hadd : η⁻¹ ≤ Real.exp (η⁻¹) := by linarith [Real.add_one_le_exp (η⁻¹)]
    have hexp_ge : η⁻¹ ≤ Real.exp ((1 / 20) * (N : ℝ) * η) :=
      hadd.trans (Real.exp_le_exp.mpr hinv_le)
    rw [show -(1 / 20) * (N : ℝ) * η = -((1 / 20) * (N : ℝ) * η) by ring, Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀' (Real.exp_pos _)).mpr
      ((inv_le_iff_one_le_mul₀ hη).mp hexp_ge)
  have hexp_delta : Real.exp (-(1 / 10) * (N : ℝ) * η) ≤ δ / 400 := by
    have hN_nn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have heta_sq_le : η ^ 2 ≤ η := by nlinarith
    have hlog_le : Real.log (400 / δ) ≤ (1 / 10) * (N : ℝ) * η := by
      have h1 : Real.log (400 / δ) ≤ (1 / 10) * ((N : ℝ) * η ^ 2) := by linarith
      have h2 : (1 / 10) * ((N : ℝ) * η ^ 2) ≤ (1 / 10) * ((N : ℝ) * η) := by gcongr
      linarith [h2]
    have h400_pos : (0 : ℝ) < 400 / δ := div_pos (by norm_num) hδ0
    calc
      Real.exp (-(1 / 10) * (N : ℝ) * η) ≤ Real.exp (-Real.log (400 / δ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = δ / 400 := by rw [Real.exp_neg, Real.exp_log h400_pos, inv_div]
  calc
    2 * Real.exp (-(N : ℝ) * (η / 2) ^ 2 / (2 * (m + (2 / 3) * (η / 2))))
        ≤ 2 * Real.exp (-(1 / 20) * (N : ℝ) * η + -(1 / 10) * (N : ℝ) * η) := by gcongr
    _ = 2 * (Real.exp (-(1 / 20) * (N : ℝ) * η) * Real.exp (-(1 / 10) * (N : ℝ) * η)) := by
        rw [Real.exp_add]
    _ ≤ 2 * (η * (δ / 400)) := by gcongr
    _ = η * (δ / 200) := by ring

/-- **Canonne (failure-probability form).** For `N` mutually independent
samples `X : Fin N → Ω → α` drawn from `q : PMF α` on a finite discrete measurable space, if
`(20 / (min η 1) ^ 2) * Real.log (400 / δ) ≤ N`, then the probability that some outcome has
empirical frequency error exceeding `η` is at most `δ`.
-/
theorem measureReal_exists_lt_abs_empiricalFreq_sub_le_of_pmf {N : ℕ} {Ω α : Type*}
    [MeasurableSpace Ω] [Finite α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} {X : Fin N → Ω → α}
    (h_indep : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ)
    (q : PMF α) (h_law : ∀ i, μ.map (X i) = q.toMeasure)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hN : (20 / (min η 1) ^ 2) * Real.log (400 / δ) ≤ N) :
    μ.real {ω | ∃ x, η < |empiricalFreq X ω x - (q x).toReal|} ≤ δ := by
  let _ : Fintype α := Fintype.ofFinite α
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  by_cases hδ1 : 1 < δ
  · exact measureReal_le_one.trans hδ1.le
  · have hδ_le : δ ≤ 1 := not_lt.mp hδ1
    by_cases hη1 : 1 < η
    · have hempty : {ω | ∃ x, η < |empiricalFreq X ω x - (q x).toReal|} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
        intro x
        have h1 : |empiricalFreq X ω x - (q x).toReal| ≤ 1 :=
          abs_sub_le_iff.mpr
            ⟨by linarith [empiricalFreq_le_one X ω x, @ENNReal.toReal_nonneg (q x)],
             by linarith [empiricalFreq_nonneg X ω x, pmf_toReal_le_one q x]⟩
        linarith
      rw [hempty, measureReal_empty]
      exact hδ.le
    · have hη_le : η ≤ 1 := not_lt.mp hη1
      rw [min_eq_left hη_le] at hN
      have hlog1 : 1 ≤ Real.log (400 / δ) := log_400_div_ge_one hδ hδ_le
      have hNeta : 20 * Real.log (400 / δ) ≤ (N : ℝ) * η ^ 2 := by
        rw [← div_le_iff₀ (sq_pos_of_pos hη)]
        simpa [div_mul_eq_mul_div] using hN
      have hNeta_20 : 20 ≤ (N : ℝ) * η ^ 2 := by linarith
      have hN1 : 1 ≤ N := by
        by_contra hN0
        have hN_zero : N = 0 := by omega
        rw [hN_zero, Nat.cast_zero, zero_mul] at hNeta_20
        linarith
      let p : α → ℝ := fun x ↦ (q x).toReal
      let H : Finset α := Finset.univ.filter (fun x ↦ η / 4 < p x)
      let S : Finset α := Finset.univ.filter (fun x ↦ p x ≤ η / 4)
      have hS_prop : ∀ x ∈ S, 0 ≤ p x ∧ p x ≤ η / 4 :=
        fun x hx ↦ ⟨ENNReal.toReal_nonneg, (Finset.mem_filter.mp hx).2⟩
      obtain ⟨L, _, hL_mem, hL_cov, _, _, hL_len⟩ := exists_greedy_mass_partition p hη S hS_prop
      have hsub : {ω | ∃ x, η < |empiricalFreq X ω x - p x|} ⊆
          (⋃ x ∈ H, {ω | η ≤ |empiricalFreq X ω x - p x|}) ∪
          (⋃ B ∈ L.toFinset, {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|}) := by
        intro ω hω
        by_contra hnot
        simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_toFinset,
          not_or, not_exists, not_le] at hnot
        obtain ⟨x, hx⟩ := hω
        have hle := forall_abs_empiricalFreq_sub_le_of_blocks (fun _ ↦ ENNReal.toReal_nonneg)
          hη hL_mem hL_cov hnot.1 hnot.2 x
        linarith
      have hH_bound : ∑ x ∈ H, μ.real {ω | η ≤ |empiricalFreq X ω x - p x|} ≤ (1 / 2) * δ := by
        have hterm : ∀ x ∈ H, μ.real {ω | η ≤ |empiricalFreq X ω x - p x|} ≤ (1 / 2) * δ * p x :=
          fun x hxH ↦ by
            have hbern :=
              measureReal_abs_sum_empiricalFreq_sub_ge_le_of_pmf hN1 h_indep hX q h_law {x} hη.le
            simp only [Finset.sum_singleton] at hbern
            exact hbern.trans
              (two_mul_exp_heavy_le q hη hδ hlog1 hNeta (Finset.mem_filter.mp hxH).2)
        have hH_mass : ∑ x ∈ H, p x ≤ ∑ x : α, p x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
            fun _ _ _ ↦ ENNReal.toReal_nonneg
        calc
          ∑ x ∈ H, μ.real {ω | η ≤ |empiricalFreq X ω x - p x|}
              ≤ ∑ x ∈ H, (1 / 2) * δ * p x := Finset.sum_le_sum hterm
          _ = (1 / 2) * δ * ∑ x ∈ H, p x := by rw [← Finset.mul_sum]
          _ ≤ (1 / 2) * δ * ∑ x : α, p x := mul_le_mul_of_nonneg_left hH_mass (by positivity)
          _ = (1 / 2) * δ := by rw [sum_pmf_toReal_eq_one q, mul_one]
      have hL_bound : ∑ B ∈ L.toFinset,
          μ.real {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|} ≤
          (1 / 2) * δ := by
        have hterm : ∀ B ∈ L.toFinset,
            μ.real {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|} ≤
            η * (δ / 200) := by
          intro B hBL
          have hB_prop := hL_mem B (List.mem_toFinset.mp hBL)
          have hbern := measureReal_abs_sum_empiricalFreq_sub_ge_le_of_pmf hN1 h_indep hX q h_law B
            (half_pos hη).le
          exact hbern.trans (two_mul_exp_light_le hη hη_le hδ
            (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg) hB_prop.2.2 hNeta hNeta_20)
        have hS_mass : ∑ x ∈ S, p x ≤ 1 :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun _ _ _ ↦ ENNReal.toReal_nonneg).trans_eq (sum_pmf_toReal_eq_one q)
        have hL_len_le : (L.length : ℝ) ≤ 5 / η := by
          have h4 : (4 * ∑ x ∈ S, p x) / η ≤ 4 / η :=
            div_le_div_of_nonneg_right (by linarith) hη.le
          have h2 : 1 ≤ 1 / η := (one_le_div hη).mpr hη_le
          have h45 : 4 / η + 1 / η = 5 / η := by ring
          linarith
        calc
          ∑ B ∈ L.toFinset, μ.real {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|}
              ≤ ∑ _B ∈ L.toFinset, η * (δ / 200) := Finset.sum_le_sum hterm
          _ = (L.toFinset.card : ℝ) * (η * (δ / 200)) := by simp [nsmul_eq_mul]
          _ ≤ (L.length : ℝ) * (η * (δ / 200)) := by
              gcongr
              exact_mod_cast List.toFinset_card_le L
          _ ≤ (5 / η) * (η * (δ / 200)) := by gcongr
          _ ≤ (1 / 2) * δ := by
              have heq : (5 / η) * (η * (δ / 200)) = (1 / 40) * δ := by
                field_simp [hη.ne']
                ring
              linarith
      calc
        μ.real {ω | ∃ x, η < |empiricalFreq X ω x - p x|}
            ≤ μ.real ((⋃ x ∈ H, {ω | η ≤ |empiricalFreq X ω x - p x|}) ∪
                (⋃ B ∈ L.toFinset,
                  {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|})) :=
              measureReal_mono hsub
        _ ≤ μ.real (⋃ x ∈ H, {ω | η ≤ |empiricalFreq X ω x - p x|}) +
              μ.real (⋃ B ∈ L.toFinset,
                {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|}) :=
            measureReal_union_le _ _
        _ ≤ (∑ x ∈ H, μ.real {ω | η ≤ |empiricalFreq X ω x - p x|}) +
              (∑ B ∈ L.toFinset,
                μ.real {ω | η / 2 ≤ |∑ x ∈ B, empiricalFreq X ω x - ∑ x ∈ B, p x|}) :=
            add_le_add (measureReal_biUnion_finset_le H _)
              (measureReal_biUnion_finset_le L.toFinset _)
        _ ≤ (1 / 2) * δ + (1 / 2) * δ := add_le_add hH_bound hL_bound
        _ = δ := by ring

/-- **Canonne (high-probability confidence form).** For `N` mutually independent
samples drawn from `q : PMF α` with `(20 / (min η 1) ^ 2) * Real.log (400 / δ) ≤ N`, the empirical
frequencies satisfy `∀ x, |empiricalFreq X ω x - (q x).toReal| ≤ η` with probability at least
`1 - δ`.
-/
theorem measureReal_forall_abs_empiricalFreq_sub_le_of_pmf {N : ℕ} {Ω α : Type*}
    [MeasurableSpace Ω] [Finite α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} {X : Fin N → Ω → α}
    (h_indep : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ)
    (q : PMF α) (h_law : ∀ i, μ.map (X i) = q.toMeasure)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hN : (20 / (min η 1) ^ 2) * Real.log (400 / δ) ≤ N) :
    1 - δ ≤ μ.real {ω | ∀ x, |empiricalFreq X ω x - (q x).toReal| ≤ η} := by
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let G : Set Ω := {ω | ∀ x, |empiricalFreq X ω x - (q x).toReal| ≤ η}
  have huniv : (1 : ℝ) ≤ μ.real G + μ.real Gᶜ := by
    rw [← probReal_univ (μ := μ), ← Set.union_compl_self G]
    exact measureReal_union_le G Gᶜ
  have hcompl : Gᶜ = {ω | ∃ x, η < |empiricalFreq X ω x - (q x).toReal|} := by
    ext ω
    simp only [G, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le]
  have htail := measureReal_exists_lt_abs_empiricalFreq_sub_le_of_pmf h_indep hX q h_law hη hδ hN
  rw [← hcompl] at htail
  linarith

/-- **Single-logarithm specialization of Canonne for `δ ≤ 1 / 2`.** When
`0 < δ ≤ 1 / 2`, the sample complexity `(200 / (min η 1) ^ 2) * Real.log (1 / δ) ≤ N` suffices for
`∀ x, |empiricalFreq X ω x - (q x).toReal| ≤ η` with probability at least `1 - δ`.
-/
theorem measureReal_forall_abs_empiricalFreq_sub_le_of_pmf_half {N : ℕ} {Ω α : Type*}
    [MeasurableSpace Ω] [Finite α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} {X : Fin N → Ω → α}
    (h_indep : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ)
    (q : PMF α) (h_law : ∀ i, μ.map (X i) = q.toMeasure)
    {η δ : ℝ} (hη : 0 < η) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hN : (200 / (min η 1) ^ 2) * Real.log (1 / δ) ≤ N) :
    1 - δ ≤ μ.real {ω | ∀ x, |empiricalFreq X ω x - (q x).toReal| ≤ η} := by
  have h2_le : (2 : ℝ) ≤ 1 / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  have hlog2 : Real.log 2 ≤ Real.log (1 / δ) := Real.log_le_log zero_lt_two h2_le
  have hlog400 : Real.log 400 ≤ 9 * Real.log 2 := by
    have h400_le : (400 : ℝ) ≤ (2 : ℝ) ^ 9 := by norm_num
    calc
      Real.log 400 ≤ Real.log ((2 : ℝ) ^ 9) := Real.log_le_log (by norm_num) h400_le
      _ = 9 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num
  have hlog_bound : Real.log (400 / δ) ≤ 10 * Real.log (1 / δ) := by
    rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (one_div_pos.mpr hδ0).ne']
    linarith
  have hcoeff_nn : 0 ≤ 20 / (min η 1) ^ 2 := by positivity
  have hN' : (20 / (min η 1) ^ 2) * Real.log (400 / δ) ≤ N := by
    calc
      (20 / (min η 1) ^ 2) * Real.log (400 / δ)
          ≤ (20 / (min η 1) ^ 2) * (10 * Real.log (1 / δ)) :=
            mul_le_mul_of_nonneg_left hlog_bound hcoeff_nn
      _ = (200 / (min η 1) ^ 2) * Real.log (1 / δ) := by ring
      _ ≤ N := hN
  exact measureReal_forall_abs_empiricalFreq_sub_le_of_pmf h_indep hX q h_law hη hδ0 hN'

end EmpiricalLInf

/-! ### 4. Finite-family uniform Hoeffding confidence bound -/

section UniformHoeffding

/-- **Uniform Hoeffding confidence bound.** Let `X : Fin N → Ω → α` (`N ≥ 1`) be mutually
independent identically distributed random variables and let `f : Y → α → ℝ` be a nonempty finite
family of measurable observables taking values in `[0, c_bar]`. Then for every `δ ∈ (0, 1]`, all
empirical averages simultaneously lie within
`c_bar * √(log (2 * Fintype.card Y / δ) / (2 * N))` of their expectations with probability at
least `1 - δ`. -/
theorem uniform_hoeffding_confidence {N : ℕ} [NeZero N] {Ω α Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype Y] [Nonempty Y]
    {μ : Measure Ω} {X : Fin N → Ω → α}
    (h_indep : iIndepFun X μ)
    (h_ident : ∀ k : Fin N, IdentDistrib (X k) (X 0) μ μ)
    {f : Y → α → ℝ} (hf_meas : ∀ y : Y, Measurable (f y))
    {c_bar : ℝ} (hf_mem : ∀ (y : Y) (x : α), f y x ∈ Set.Icc 0 c_bar)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ μ.real {ω | ∀ y : Y,
      |((N : ℝ)⁻¹ * ∑ k : Fin N, f y (X k ω)) - ∫ ω', f y (X 0 ω') ∂μ| ≤
        c_bar * Real.sqrt (Real.log (2 * (Fintype.card Y : ℝ) / δ) / (2 * (N : ℝ)))} := by
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hneΩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have huniv := probReal_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr h, measureReal_empty] at huniv
    norm_num at huniv
  obtain ⟨ω₀⟩ := hneΩ
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hc_nn : 0 ≤ c_bar := (hf_mem y₀ (X 0 ω₀)).1.trans (hf_mem y₀ (X 0 ω₀)).2
  have hX : ∀ k : Fin N, AEMeasurable (X k) μ := fun k ↦ (h_ident k).aemeasurable_fst
  let ν : Fin N → Measure α := fun k ↦ μ.map (X k)
  have hν_prob : ∀ k : Fin N, IsProbabilityMeasure (ν k) :=
    fun k ↦ (Measure.isProbabilityMeasure_map_iff (hX k)).mpr hprob
  have hmap_pi : μ.map (fun ω k ↦ X k ω) = Measure.pi ν := h_indep.map_fun_eq_pi_map hX
  let m : Y → ℝ := fun y ↦ ∫ ω', f y (X 0 ω') ∂μ
  let cNN : ℝ≥0 := ⟨c_bar, hc_nn⟩
  have hcNN_coe : (cNN : ℝ) = c_bar := rfl
  let C_par : ℝ≥0 := ∑ _ : Fin N, (cNN / 2) ^ 2
  have hcard_pos : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ge1 : (1 : ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos
  let δ' : ℝ := δ / (2 * (Fintype.card Y : ℝ))
  have hδ'_pos : 0 < δ' := by
    dsimp only [δ']
    positivity
  have hδ'_le1 : δ' ≤ 1 := by
    dsimp only [δ']
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hdiv_eq : 1 / δ' = 2 * (Fintype.card Y : ℝ) / δ := by
    dsimp only [δ']
    field_simp [hcard_pos.ne', hδ0.ne']
  have hlog_nn : 0 ≤ Real.log (2 * (Fintype.card Y : ℝ) / δ) :=
    Real.log_nonneg ((one_le_div hδ0).mpr (by linarith))
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set r : ℝ := c_bar * Real.sqrt (Real.log (2 * (Fintype.card Y : ℝ) / δ) / (2 * (N : ℝ)))
  have hthresh : Real.sqrt (2 * (C_par : ℝ) * Real.log (1 / δ')) = (N : ℝ) * r := by
    have hC_par : (C_par : ℝ) = (N : ℝ) * (c_bar / 2) ^ 2 := by
      dsimp only [C_par]
      push_cast
      simp [hcNN_coe, nsmul_eq_mul]
    have hr_nn : 0 ≤ (N : ℝ) * r := by
      dsimp only [r]
      positivity
    refine (sq_eq_sq₀ (Real.sqrt_nonneg _) hr_nn).mp ?_
    rw [hC_par, hdiv_eq, Real.sq_sqrt (by positivity)]
    dsimp only [r]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [hN_pos.ne']
  let Zpos : Y → Fin N → (Fin N → α) → ℝ := fun y k v ↦ f y (v k) - m y
  let Zneg : Y → Fin N → (Fin N → α) → ℝ := fun y k v ↦ m y - f y (v k)
  have hZpos_meas : ∀ (y : Y) (k : Fin N), Measurable (Zpos y k) :=
    fun y k ↦ ((hf_meas y).comp (measurable_pi_apply k)).sub measurable_const
  have hZneg_meas : ∀ (y : Y) (k : Fin N), Measurable (Zneg y k) :=
    fun y k ↦ measurable_const.sub ((hf_meas y).comp (measurable_pi_apply k))
  have htail_y : ∀ y : Y,
      (Measure.pi ν).real
        ({v | (N : ℝ) * r < ∑ k : Fin N, Zpos y k v} ∪
         {v | (N : ℝ) * r < ∑ k : Fin N, Zneg y k v}) ≤ 2 * δ' := fun y ↦ by
    have : IsProbabilityMeasure (μ.map (X 0)) := hν_prob 0
    have hint_fy : Integrable (f y) (μ.map (X 0)) :=
      Integrable.of_mem_Icc 0 c_bar (hf_meas y).aemeasurable (Eventually.of_forall (hf_mem y))
    have hmean_fy : ∫ z, f y z ∂(μ.map (X 0)) = m y :=
      integral_map (hX 0) (hf_meas y).aestronglyMeasurable
    have hsub_pos := hasSubgaussianMGF_sum_pi (μ := ν) (Y := Zpos y) (c := fun _ ↦ cNN)
      (hZpos_meas y)
      (fun k j hkj v z ↦ by simp [Zpos, Function.update_of_ne hkj.ne])
      (fun k v ↦ by
        simp only [Zpos, Function.update_self, ν]
        rw [(h_ident k).map_eq, integral_sub hint_fy (integrable_const (m y)), hmean_fy,
          integral_const, probReal_univ, one_smul, sub_self])
      (fun k v ↦ ⟨-m y, fun z ↦ by
        simp only [Zpos, Function.update_self, hcNN_coe, Set.mem_Icc]
        exact ⟨by linarith [(hf_mem y z).1], by linarith [(hf_mem y z).2]⟩⟩)
    have hsub_neg := hasSubgaussianMGF_sum_pi (μ := ν) (Y := Zneg y) (c := fun _ ↦ cNN)
      (hZneg_meas y)
      (fun k j hkj v z ↦ by simp [Zneg, Function.update_of_ne hkj.ne])
      (fun k v ↦ by
        simp only [Zneg, Function.update_self, ν]
        rw [(h_ident k).map_eq, integral_sub (integrable_const (m y)) hint_fy, hmean_fy,
          integral_const, probReal_univ, one_smul, sub_self])
      (fun k v ↦ ⟨m y - c_bar, fun z ↦ by
        simp only [Zneg, Function.update_self, hcNN_coe, Set.mem_Icc]
        exact ⟨by linarith [(hf_mem y z).2], by linarith [(hf_mem y z).1]⟩⟩)
    have hp := hsub_pos.measure_sqrt_lt_le hδ'_pos hδ'_le1
    have hn := hsub_neg.measure_sqrt_lt_le hδ'_pos hδ'_le1
    rw [hthresh] at hp hn
    exact (measureReal_union_le _ _).trans (by linarith)
  let Bad_pi : Set (Fin N → α) :=
    ⋃ y ∈ (Finset.univ : Finset Y),
      ({v | (N : ℝ) * r < ∑ k : Fin N, Zpos y k v} ∪
       {v | (N : ℝ) * r < ∑ k : Fin N, Zneg y k v})
  have hBad_meas : MeasurableSet Bad_pi :=
    Finset.measurableSet_biUnion Finset.univ fun y _ ↦
      (measurableSet_lt measurable_const
        (Finset.measurable_sum Finset.univ fun k _ ↦ hZpos_meas y k)).union
      (measurableSet_lt measurable_const
        (Finset.measurable_sum Finset.univ fun k _ ↦ hZneg_meas y k))
  let Good : Set Ω :=
    {ω | ∀ y : Y, |((N : ℝ)⁻¹ * ∑ k : Fin N, f y (X k ω)) - m y| ≤ r}
  have hcompl_sub : Goodᶜ ⊆ (fun ω k ↦ X k ω) ⁻¹' Bad_pi := fun ω hω ↦ by
    simp only [Good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨y, hy⟩ := hω
    have hmul : (N : ℝ) * r < |(∑ k : Fin N, f y (X k ω)) - (N : ℝ) * m y| := by
      have h1 := mul_lt_mul_of_pos_left hy hN_pos
      have h2 : |(∑ k : Fin N, f y (X k ω)) - (N : ℝ) * m y| =
          (N : ℝ) * |((N : ℝ)⁻¹ * ∑ k : Fin N, f y (X k ω)) - m y| := by
        calc
          |(∑ k : Fin N, f y (X k ω)) - (N : ℝ) * m y|
              = |(N : ℝ) * (((N : ℝ)⁻¹ * ∑ k : Fin N, f y (X k ω)) - m y)| :=
                congrArg abs (by field_simp [hN_pos.ne'])
          _ = (N : ℝ) * |((N : ℝ)⁻¹ * ∑ k : Fin N, f y (X k ω)) - m y| := by
                rw [abs_mul, abs_of_pos hN_pos]
      rwa [← h2] at h1
    have hpos_eq : (∑ k : Fin N, Zpos y k (fun j ↦ X j ω)) =
        (∑ k : Fin N, f y (X k ω)) - (N : ℝ) * m y := by
      simp [Zpos, Finset.sum_sub_distrib, nsmul_eq_mul]
    have hneg_eq : (∑ k : Fin N, Zneg y k (fun j ↦ X j ω)) =
        -((∑ k : Fin N, f y (X k ω)) - (N : ℝ) * m y) := by
      simp [Zneg, Finset.sum_sub_distrib, nsmul_eq_mul]
    rw [Set.mem_preimage]
    refine Set.mem_iUnion₂.mpr ⟨y, Finset.mem_univ y, ?_⟩
    rcases lt_abs.mp hmul with h1 | h2
    · exact Or.inl (by rw [Set.mem_ofPred_eq, hpos_eq]; exact h1)
    · exact Or.inr (by rw [Set.mem_ofPred_eq, hneg_eq]; exact h2)
  have hBad_prob : μ.real Goodᶜ ≤ δ := by
    calc
      μ.real Goodᶜ ≤ μ.real ((fun ω k ↦ X k ω) ⁻¹' Bad_pi) := measureReal_mono hcompl_sub
      _ = (Measure.pi ν).real Bad_pi := by
          rw [measureReal_def, measureReal_def, ← hmap_pi,
            Measure.map_apply_of_aemeasurable (.of_eval hX) hBad_meas]
      _ ≤ ∑ y ∈ (Finset.univ : Finset Y),
            (Measure.pi ν).real
              ({v | (N : ℝ) * r < ∑ k : Fin N, Zpos y k v} ∪
               {v | (N : ℝ) * r < ∑ k : Fin N, Zneg y k v}) :=
          measureReal_biUnion_finset_le Finset.univ _
      _ ≤ ∑ _y ∈ (Finset.univ : Finset Y), 2 * δ' := Finset.sum_le_sum fun y _ ↦ htail_y y
      _ = (Fintype.card Y : ℝ) * (2 * δ') := by simp [nsmul_eq_mul]
      _ = δ := by
          dsimp only [δ']
          field_simp [hcard_pos.ne']
  have huniv : (1 : ℝ) ≤ μ.real Good + μ.real Goodᶜ := by
    rw [← probReal_univ (μ := μ), ← Set.union_compl_self Good]
    exact measureReal_union_le Good Goodᶜ
  linarith

end UniformHoeffding

/-! ### 5. Non-vacuity and sharpness witnesses -/

section Witnesses

private noncomputable def uniformPMF (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ : α ↦ (Fintype.card α : ℝ≥0∞)⁻¹) (by
    simp [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel])

private lemma uniformPMF_toReal (α : Type*) [Fintype α] [Nonempty α] (x : α) :
    (uniformPMF α x).toReal = (Fintype.card α : ℝ)⁻¹ := by
  simp [uniformPMF]

private lemma pi_uniformPMF_law (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] (N : ℕ) (i : Fin N) :
    (Measure.pi fun _ : Fin N ↦ (uniformPMF α).toMeasure).map
      (fun (ω : Fin N → α) ↦ ω i) = (uniformPMF α).toMeasure :=
  (measurePreserving_eval (fun _ : Fin N ↦ (uniformPMF α).toMeasure) i).map_eq

-- Non-vacuity witness on `Bool` (`N = 3600` i.i.d. fair coin flips) and sharpness (`N = 1`).
example :
    (∃ (μ : Measure (Fin 3600 → Bool)) (_ : IsProbabilityMeasure μ)
      (X : Fin 3600 → (Fin 3600 → Bool) → Bool) (q : PMF Bool),
      iIndepFun X μ ∧ (∀ i, μ.map (X i) = q.toMeasure) ∧
      (∀ b : Bool, (q b).toReal = 1 / 2) ∧
      1 - (1 / 4 : ℝ) ≤ μ.real {ω | ∀ b : Bool, |empiricalFreq X ω b - 1 / 2| ≤ 1 / 4}) ∧
    (∃ (μ : Measure (Fin 1 → Bool)) (_ : IsProbabilityMeasure μ)
      (X : Fin 1 → (Fin 1 → Bool) → Bool) (q : PMF Bool),
      iIndepFun X μ ∧ (∀ i, μ.map (X i) = q.toMeasure) ∧
      μ.real {ω | ∀ b : Bool, |empiricalFreq X ω b - (q b).toReal| ≤ 1 / 4} = 0) := by
  refine ⟨?_, ?_⟩
  · let q : PMF Bool := uniformPMF Bool
    let μ : Measure (Fin 3600 → Bool) := Measure.pi fun _ : Fin 3600 ↦ q.toMeasure
    let X : Fin 3600 → (Fin 3600 → Bool) → Bool := fun i ω ↦ ω i
    have hq_val : ∀ b : Bool, (q b).toReal = 1 / 2 := fun b ↦ by
      rw [uniformPMF_toReal]
      norm_num
    have hindep : iIndepFun X μ := iIndepFun_pi fun _ ↦ aemeasurable_id
    have hX : ∀ i : Fin 3600, AEMeasurable (X i) μ := fun i ↦ (measurable_pi_apply i).aemeasurable
    have hlog : Real.log (400 / (1 / 4 : ℝ)) ≤ 11 := by
      have h2exp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h1600 : (400 / (1 / 4 : ℝ)) ≤ Real.exp 11 := by
        have hpow : (2 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) h2exp 11
        rw [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] at hpow
        linarith
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr h1600
    have hN :
        (20 / (min (1 / 4 : ℝ) 1) ^ 2) * Real.log (400 / (1 / 4 : ℝ)) ≤ ((3600 : ℕ) : ℝ) := by
      rw [min_eq_left (by norm_num)]
      linarith
    have hconc := measureReal_forall_abs_empiricalFreq_sub_le_of_pmf hindep hX q
      (pi_uniformPMF_law Bool 3600) (by norm_num) (by norm_num) hN
    refine ⟨μ, inferInstance, X, q, hindep, pi_uniformPMF_law Bool 3600, hq_val, ?_⟩
    simpa only [hq_val] using hconc
  · let q : PMF Bool := uniformPMF Bool
    let μ : Measure (Fin 1 → Bool) := Measure.pi fun _ : Fin 1 ↦ q.toMeasure
    let X : Fin 1 → (Fin 1 → Bool) → Bool := fun i ω ↦ ω i
    have hindep : iIndepFun X μ := iIndepFun_pi fun _ ↦ aemeasurable_id
    have hempty : {ω : Fin 1 → Bool |
        ∀ b : Bool, |empiricalFreq X ω b - (q b).toReal| ≤ 1 / 4} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
      refine ⟨ω 0, ?_⟩
      unfold empiricalFreq
      rw [uniformPMF_toReal, Fin.sum_univ_one]
      simp [X]
      norm_num
    refine ⟨μ, inferInstance, X, q, hindep, pi_uniformPMF_law Bool 1, ?_⟩
    rw [hempty, measureReal_empty]

end Witnesses

end CslibFrontier.Probability

end
