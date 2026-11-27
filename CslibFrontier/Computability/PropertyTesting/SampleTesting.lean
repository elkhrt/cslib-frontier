/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/
module

-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Probability.PMF
public import CslibFrontier.Probability.IID
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ZMod.Basic

import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Composite Sample Testing, Bayes-Optimal Mixture Distinguishers, and Random Dual-Code Weights

General sample-complexity primitives for distinguishing a reference probability mass function `P₀`
from a family `F` of alternative distributions given `T` independent samples `iid D T`:

1. **Randomized sample testers and Bayes optimality of the maximum-likelihood distinguisher**:
   `SampleTester`, `acceptProb`, `rejectProb`, `TestsFamily`, and `mleDistinguisher` against the
   uniform mixture over a finite nonempty subfamily `S` of alternatives, achieving minimum sum of
   false-positive and average false-negative error among all randomized `T`-sample testers
   (`mleDistinguisher_error_le`, `testsFamily_not_of_mle_acceptProb_gt`).
2. **Consistent-support elimination upper bound**: for any finite family of nonempty support
   events `H` each having `P₀`-mass at most `1 - ε`, the deterministic consistent-hypothesis tester
   `consistentSupportTester` accepts every distribution supported on some `E ∈ H` with probability
   `1` and rejects `P₀` with probability at least `1 - |H| (1 - ε)^T`
   (`consistentSupportTester_spec`).
3. **Random `𝔽₂ⁿ` dual-code weight anti-concentration and affine-hyperplane testing lower bound**:
   for `T` i.i.d. uniform vectors `v : Fin T → Fin n → ZMod 2`, the number `dualWeightCount k v` of
   Hamming-weight-`k` vectors orthogonal to every sample has exact mean `n.choose k / 2^T`
   (`expect_dualWeightCount`), exact second moment bounded by `μ + μ²`
   (`secondMoment_dualWeightCount_le`), and Paley–Zygmund lower tail `Pr[W ≥ 1] ≥ μ / (1 + μ)`
   (`prob_dualWeightCount_pos_ge`), forcing any sample tester distinguishing the uniform
   distribution on `𝔽₂ⁿ` from uniform distributions on weight-`k` parity hyperplanes (`1 ≤ k < n`)
   with error parameter `δ < 1 / 6` to use strictly more than `Nat.clog 2 (n.choose k)` samples
   (`parityHyperplane_sample_lower_bound`).
-/

public section

open Cslib.Probability.PMF
open scoped BigOperators ENNReal

namespace CslibFrontier.Computability.PropertyTesting

/-! ### 1. Randomized Sample Testers and Bayes-Optimal Mixture Distinguishing -/

section BayesMixture

/-- A randomized `T`-sample tester over alphabet `α`, mapping a `T`-sample tuple to a distribution
over `Bool` (`true` for alternative, `false` for null). -/
abbrev SampleTester (α : Type*) (T : ℕ) : Type _ :=
  (Fin T → α) → PMF Bool

/-- Probability that tester `A` accepts (`true`) on `T` i.i.d. samples drawn from `D`. -/
noncomputable def acceptProb {α : Type*} {T : ℕ} (A : SampleTester α T) (D : PMF α) : ℝ :=
  (((iid D T).bind A) true).toReal

/-- Probability that tester `A` rejects (`false`) on `T` i.i.d. samples drawn from `D`. -/
noncomputable def rejectProb {α : Type*} {T : ℕ} (A : SampleTester α T) (D : PMF α) : ℝ :=
  (((iid D T).bind A) false).toReal

/-- Finite-sum formula for `acceptProb`. -/
theorem acceptProb_eq_sum {α : Type*} [Fintype α] {T : ℕ} (A : SampleTester α T) (D : PMF α) :
    acceptProb A D = ∑ x : Fin T → α, (iid D T x).toReal * (A x true).toReal := by
  rw [acceptProb, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun x _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ x) (PMF.apply_ne_top _ _)]
  exact Finset.sum_congr rfl fun _ _ ↦ ENNReal.toReal_mul

/-- Finite-sum formula for `rejectProb`. -/
theorem rejectProb_eq_sum {α : Type*} [Fintype α] {T : ℕ} (A : SampleTester α T) (D : PMF α) :
    rejectProb A D = ∑ x : Fin T → α, (iid D T x).toReal * (A x false).toReal := by
  rw [rejectProb, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun x _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ x) (PMF.apply_ne_top _ _)]
  exact Finset.sum_congr rfl fun _ _ ↦ ENNReal.toReal_mul

private lemma pmf_bool_add_toReal (q : PMF Bool) : (q true).toReal + (q false).toReal = 1 := by
  have hsum : ∑ b : Bool, (q b).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun b _ ↦ PMF.apply_ne_top _ b, ← tsum_fintype (L := .unconditional _),
      PMF.tsum_coe, ENNReal.toReal_one]
  rwa [Fintype.sum_bool] at hsum

/-- For every tester `A` and distribution `D`, `acceptProb A D + rejectProb A D = 1`. -/
theorem acceptProb_add_rejectProb {α : Type*} {T : ℕ} (A : SampleTester α T) (D : PMF α) :
    acceptProb A D + rejectProb A D = 1 :=
  pmf_bool_add_toReal ((iid D T).bind A)

/-- A `T`-sample tester `A` distinguishes null distribution `P₀` from alternative family `F` with
error budget `δ` if it rejects `P₀` and accepts every `D ∈ F` with probability at least `1 - δ`. -/
def TestsFamily {α : Type*} {T : ℕ} (A : SampleTester α T) (P₀ : PMF α) (F : Set (PMF α))
    (δ : ℝ) : Prop :=
  1 - δ ≤ rejectProb A P₀ ∧ ∀ D ∈ F, 1 - δ ≤ acceptProb A D

private lemma iid_zero_eq_pure {α : Type*} (D : PMF α) :
    iid D 0 = PMF.pure Fin.elim0 := by
  ext x
  have hx : x = Fin.elim0 := funext fun i ↦ Fin.elim0 i
  subst hx
  simp [iid_apply]

private lemma iid_succ_eq_bind {α : Type*} (M : ℕ) (D : PMF α) :
    iid D (M + 1) = D.bind fun hd ↦ (iid D M).map (Fin.cons hd) := by
  classical
  ext x
  rw [iid_apply, Fin.prod_univ_succ, PMF.bind_apply, tsum_eq_single (x 0)]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single (Fin.tail x)]
    · have hcons : Fin.cons (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
      simp [hcons, iid_apply, Fin.tail]
    · intro tl htl
      split_ifs with h
      · exact (htl (funext fun j ↦ (congrFun h j.succ).symm)).elim
      · rfl
  · intro hd hhd
    suffices ((iid D M).map (Fin.cons hd)) x = 0 by simp [this]
    rw [PMF.map_apply, tsum_eq_zero_iff]
    intro tl
    split_ifs with h
    · exact (hhd (congrFun h 0).symm).elim
    · rfl

private lemma map_castLE_iid {α : Type*} {T₀ T : ℕ} (hT : T₀ ≤ T) (D : PMF α) :
    (iid D T).map (fun x : Fin T → α ↦ fun j : Fin T₀ ↦ x (Fin.castLE hT j)) = iid D T₀ := by
  induction T₀ generalizing T with
  | zero =>
    have hconst : (fun x : Fin T → α ↦ fun j : Fin 0 ↦ x (Fin.castLE hT j)) =
        Function.const (Fin T → α) Fin.elim0 := funext fun _ ↦ funext fun i ↦ Fin.elim0 i
    rw [hconst, PMF.map_const, iid_zero_eq_pure D]
  | succ M ih =>
    rcases T with _ | T
    · omega
    · have hT' : M ≤ T := Nat.le_of_succ_le_succ hT
      rw [iid_succ_eq_bind T D, iid_succ_eq_bind M D, PMF.map_bind]
      congr 1; funext hd; rw [PMF.map_comp]
      have hcomp : ((fun x : Fin (T + 1) → α ↦ fun j : Fin (M + 1) ↦ x (Fin.castLE hT j)) ∘
          Fin.cons hd) = Fin.cons hd ∘ fun tl : Fin T → α ↦ fun j : Fin M ↦ tl (Fin.castLE hT' j) :=
        funext fun _ ↦ funext fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j
      rw [hcomp, ← PMF.map_comp, ih hT']

/-- Sample-size monotonicity: any `(T₀, δ)`-tester extends to `T ≥ T₀` samples by prefix
restriction. -/
theorem exists_testsFamily_of_le {α : Type*} {T₀ T : ℕ} (hT : T₀ ≤ T) {P₀ : PMF α}
    {F : Set (PMF α)} {δ : ℝ} {A₀ : SampleTester α T₀} (hA₀ : TestsFamily A₀ P₀ F δ) :
    ∃ A : SampleTester α T, TestsFamily A P₀ F δ := by
  let proj : (Fin T → α) → (Fin T₀ → α) := fun x j ↦ x (Fin.castLE hT j)
  refine ⟨fun x ↦ A₀ (proj x), ?_, fun D hD ↦ ?_⟩
  · have heq : rejectProb (fun x ↦ A₀ (proj x)) P₀ = rejectProb A₀ P₀ := by
      simp only [rejectProb, ← map_castLE_iid hT P₀, PMF.bind_map, Function.comp_def, proj]
    exact heq ▸ hA₀.1
  · have heq : acceptProb (fun x ↦ A₀ (proj x)) D = acceptProb A₀ D := by
      simp only [acceptProb, ← map_castLE_iid hT D, PMF.bind_map, Function.comp_def, proj]
    exact heq ▸ hA₀.2 D hD

/-- Average `T`-sample likelihood of `x` under a finite index set `S` of alternative distributions
`Q : ι → PMF α`. -/
noncomputable def mixtureLikelihood {α ι : Type*} (S : Finset ι) (Q : ι → PMF α) (T : ℕ)
    (x : Fin T → α) : ℝ :=
  (∑ i ∈ S, (iid (Q i) T x).toReal) / (S.card : ℝ)

/-- Maximum-likelihood distinguisher between null `P₀` and the uniform mixture over `{Q i : i ∈ S}`,
accepting iff `P₀^T(x) ≤ mixtureLikelihood S Q T x`. -/
noncomputable def mleDistinguisher {α ι : Type*} (P₀ : PMF α) (S : Finset ι) (Q : ι → PMF α)
    (T : ℕ) : SampleTester α T :=
  fun x ↦ PMF.pure (decide ((iid P₀ T x).toReal ≤ mixtureLikelihood S Q T x))

/-- **Bayes optimality of `mleDistinguisher`**: for any nonempty finite alternative family
`{Q i : i ∈ S}` and any randomized `T`-sample tester `A`, the sum of false-positive rate under `P₀`
and uniform-average false-negative rate over `S` is minimized by `mleDistinguisher P₀ S Q T`. -/
theorem mleDistinguisher_error_le {α ι : Type*} [Finite α] (P₀ : PMF α) {S : Finset ι}
    (hS : S.Nonempty) (Q : ι → PMF α) {T : ℕ} (A : SampleTester α T) :
    acceptProb (mleDistinguisher P₀ S Q T) P₀ +
        (∑ i ∈ S, rejectProb (mleDistinguisher P₀ S Q T) (Q i)) / (S.card : ℝ) ≤
      acceptProb A P₀ + (∑ i ∈ S, rejectProb A (Q i)) / (S.card : ℝ) := by
  cases nonempty_fintype α
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hrisk : ∀ B : SampleTester α T,
      acceptProb B P₀ + (∑ i ∈ S, rejectProb B (Q i)) / (S.card : ℝ) =
        ∑ x : Fin T → α,
          ((iid P₀ T x).toReal * (B x true).toReal +
            mixtureLikelihood S Q T x * (B x false).toReal) := fun B ↦ by
    simp_rw [acceptProb_eq_sum, rejectProb_eq_sum]
    rw [Finset.sum_comm (s := S), Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp_rw [← Finset.sum_mul, mul_div_right_comm, mixtureLikelihood]
  rw [hrisk, hrisk]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  set p₀ : ℝ := (iid P₀ T x).toReal
  set p₁ : ℝ := mixtureLikelihood S Q T x
  set a : ℝ := (A x true).toReal
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  have hbf : (A x false).toReal = 1 - a := by linarith [pmf_bool_add_toReal (A x)]
  have ha_le : a ≤ 1 := by linarith [show 0 ≤ (A x false).toReal from ENNReal.toReal_nonneg]
  rw [hbf]
  by_cases hcmp : p₀ ≤ p₁
  · have hcmp' : (iid P₀ T x).toReal ≤ mixtureLikelihood S Q T x := hcmp
    have hmle_t : (mleDistinguisher P₀ S Q T x true).toReal = 1 := by
      rw [mleDistinguisher, decide_eq_true hcmp', PMF.pure_apply_self, ENNReal.toReal_one]
    have hmle_f : (mleDistinguisher P₀ S Q T x false).toReal = 0 := by
      rw [mleDistinguisher, decide_eq_true hcmp', PMF.pure_apply_of_ne _ _ (by decide),
        ENNReal.toReal_zero]
    change p₀ * (mleDistinguisher P₀ S Q T x true).toReal +
        p₁ * (mleDistinguisher P₀ S Q T x false).toReal ≤ p₀ * a + p₁ * (1 - a)
    rw [hmle_t, hmle_f]
    nlinarith
  · have hcmp' : ¬(iid P₀ T x).toReal ≤ mixtureLikelihood S Q T x := hcmp
    have hmle_t : (mleDistinguisher P₀ S Q T x true).toReal = 0 := by
      rw [mleDistinguisher, decide_eq_false hcmp', PMF.pure_apply_of_ne _ _ (by decide),
        ENNReal.toReal_zero]
    have hmle_f : (mleDistinguisher P₀ S Q T x false).toReal = 1 := by
      rw [mleDistinguisher, decide_eq_false hcmp', PMF.pure_apply_self, ENNReal.toReal_one]
    change p₀ * (mleDistinguisher P₀ S Q T x true).toReal +
        p₁ * (mleDistinguisher P₀ S Q T x false).toReal ≤ p₀ * a + p₁ * (1 - a)
    rw [hmle_t, hmle_f]
    nlinarith

/-- Symmetric-prior corollary: if `acceptProb (mleDistinguisher P₀ S Q T) P₀ > 2 * δ` for a
nonempty finite subfamily `{Q i : i ∈ S} ⊆ F`, then no randomized `T`-sample tester can satisfy
`TestsFamily A P₀ F δ`. -/
theorem testsFamily_not_of_mle_acceptProb_gt {α ι : Type*} [Finite α] {P₀ : PMF α} {S : Finset ι}
    (hS : S.Nonempty) {Q : ι → PMF α} {F : Set (PMF α)} (hQF : ∀ i ∈ S, Q i ∈ F) {T : ℕ} {δ : ℝ}
    (hmle : 2 * δ < acceptProb (mleDistinguisher P₀ S Q T) P₀) :
    ¬ ∃ A : SampleTester α T, TestsFamily A P₀ F δ := by
  rintro ⟨A, hU, hF⟩
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hA_fp : acceptProb A P₀ ≤ δ := by linarith [acceptProb_add_rejectProb A P₀]
  have hA_fn : (∑ i ∈ S, rejectProb A (Q i)) / (S.card : ℝ) ≤ δ := by
    rw [div_le_iff₀ hcard_pos]
    calc
      ∑ i ∈ S, rejectProb A (Q i) ≤ ∑ _i ∈ S, δ := Finset.sum_le_sum fun i hi ↦ by
        linarith [hF (Q i) (hQF i hi), acceptProb_add_rejectProb A (Q i)]
      _ = δ * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hbayes := mleDistinguisher_error_le P₀ hS Q A
  have hfn_nn : 0 ≤ (∑ i ∈ S, rejectProb (mleDistinguisher P₀ S Q T) (Q i)) / (S.card : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ ↦ ENNReal.toReal_nonneg) hcard_pos.le
  linarith

end BayesMixture

/-! ### 2. Finite-Class Consistent-Support Elimination Tester -/

section ConsistentSupport

private lemma sum_iid_pred_pow {β : Type*} [Fintype β] (D : PMF β) (T : ℕ) (P : β → Prop)
    [DecidablePred P] :
    (∑ v : Fin T → β, if ∀ j : Fin T, P (v j) then (iid D T v).toReal else 0) =
      (∑ u : β, if P u then (D u).toReal else 0) ^ T := by
  have hrhs : (∑ u : β, if P u then (D u).toReal else 0) ^ T =
      ∏ _j : Fin T, ∑ u : β, (if P u then (D u).toReal else 0) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hrhs, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  by_cases hv : ∀ j : Fin T, P (v j)
  · rw [ite_eq_left_iff.mpr fun h ↦ (h hv).elim, iid_apply, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun j _ ↦ (ite_eq_left_iff.mpr fun h ↦ (h (hv j)).elim).symm
  · rw [ite_eq_right_iff.mpr fun h ↦ (hv h).elim]
    push Not at hv
    rcases hv with ⟨j₀, hj₀⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])).symm

/-- Deterministic consistent-support tester for a finite hypothesis family `H : Finset (Finset α)`:
accepts a sample `x : Fin T → α` iff every observed coordinate lies inside a single `E ∈ H`. -/
noncomputable def consistentSupportTester {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (T : ℕ) : SampleTester α T :=
  fun x ↦ PMF.pure (decide (∃ E ∈ H, ∀ j : Fin T, x j ∈ E))

/-- **Consistent-support elimination guarantee**: if every hypothesis `E ∈ H` has `P₀`-mass at most
`1 - ε`, then `consistentSupportTester H T` achieves completeness `1` on every distribution `D`
whose support lies in some `E ∈ H`, and rejects `P₀` with probability at least
`1 - |H| (1 - ε)^T`. -/
theorem consistentSupportTester_spec {α : Type*} [Finite α] [DecidableEq α] (P₀ : PMF α)
    (H : Finset (Finset α)) {ε : ℝ} (hmass : ∀ E ∈ H, (∑ a ∈ E, (P₀ a).toReal) ≤ 1 - ε) (T : ℕ) :
    1 - (H.card : ℝ) * (1 - ε) ^ T ≤ rejectProb (consistentSupportTester H T) P₀ ∧
      ∀ D : PMF α, (∃ E ∈ H, ∀ a ∈ D.support, a ∈ E) →
        acceptProb (consistentSupportTester H T) D = 1 := by
  cases nonempty_fintype α
  refine ⟨?_, ?_⟩
  · have hsingle : ∀ E ∈ H,
        (∑ x : Fin T → α, if ∀ j : Fin T, x j ∈ E then (iid P₀ T x).toReal else 0) =
          (∑ a ∈ E, (P₀ a).toReal) ^ T := fun E _ ↦ by
      rw [sum_iid_pred_pow P₀ T (fun a ↦ a ∈ E), ← Finset.sum_filter]
      congr 2
      ext a
      simp
    have hfp : acceptProb (consistentSupportTester H T) P₀ ≤ (H.card : ℝ) * (1 - ε) ^ T := by
      rw [acceptProb_eq_sum]
      calc
        ∑ x : Fin T → α, (iid P₀ T x).toReal * (consistentSupportTester H T x true).toReal
          ≤ ∑ x : Fin T → α, ∑ E ∈ H, if ∀ j, x j ∈ E then (iid P₀ T x).toReal else 0 := by
              refine Finset.sum_le_sum fun x _ ↦ ?_
              by_cases hex : ∃ E ∈ H, ∀ j, x j ∈ E
              · rcases hex with ⟨E₀, hE₀, hxE₀⟩
                have htrue : (consistentSupportTester H T x true).toReal = 1 := by
                  simp [consistentSupportTester, show ∃ E ∈ H, ∀ j, x j ∈ E from ⟨E₀, hE₀, hxE₀⟩]
                rw [htrue, mul_one]
                let g : Finset α → ℝ := fun E ↦ if ∀ j, x j ∈ E then (iid P₀ T x).toReal else 0
                have hle0 : (iid P₀ T x).toReal ≤ g E₀ := by simp [g, hxE₀]
                refine hle0.trans (Finset.single_le_sum (f := g) (fun E _ ↦ ?_) hE₀)
                dsimp only [g]
                split_ifs <;> positivity
              · have hfalse : (consistentSupportTester H T x true).toReal = 0 := by
                  simp [consistentSupportTester, hex]
                rw [hfalse, mul_zero]
                exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
        _ = ∑ E ∈ H, (∑ a ∈ E, (P₀ a).toReal) ^ T := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl hsingle
        _ ≤ ∑ _E ∈ H, (1 - ε) ^ T := Finset.sum_le_sum fun E hE ↦
              pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg) (hmass E hE) T
        _ = (H.card : ℝ) * (1 - ε) ^ T := by rw [Finset.sum_const, nsmul_eq_mul]
    linarith [acceptProb_add_rejectProb (consistentSupportTester H T) P₀]
  · rintro D ⟨E₀, hE₀, hsupp⟩
    have hrej : rejectProb (consistentSupportTester H T) D = 0 := by
      rw [rejectProb_eq_sum]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      by_cases hall : ∀ j : Fin T, x j ∈ D.support
      · have hex : ∃ E ∈ H, ∀ j, x j ∈ E := ⟨E₀, hE₀, fun j ↦ hsupp (x j) (hall j)⟩
        have h0 : (consistentSupportTester H T x false).toReal = 0 := by
          simp [consistentSupportTester, hex]
        rw [h0, mul_zero]
      · push Not at hall
        rcases hall with ⟨j₀, hj₀⟩
        have hzero : iid D T x = 0 := by
          rw [iid_apply]
          exact Finset.prod_eq_zero (Finset.mem_univ j₀)
            ((PMF.mem_support_iff D (x j₀)).not_left.mp hj₀)
        simp [hzero]
    linarith [acceptProb_add_rejectProb (consistentSupportTester H T) D]

end ConsistentSupport

/-! ### 3. Random `𝔽₂ⁿ` Dual-Code Weights and Parity-Hyperplane Testing Lower Bound -/

section RandomDualCode

/-- The finite set of Hamming-weight-`k` vectors in `𝔽₂ⁿ = Fin n → ZMod 2`. -/
def f2WeightShell (n k : ℕ) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun y ↦ hammingNorm y = k

private lemma zmod2_eq_one_of_ne_zero {z : ZMod 2} (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b :=
  ⟨fun h ↦ by fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide),
   fun h ↦ by subst h; fin_cases a <;> decide⟩

/-- Cardinality `|f2WeightShell n k| = n.choose k`. -/
@[simp]
theorem card_f2WeightShell (n k : ℕ) : (f2WeightShell n k).card = n.choose k := by
  let e : (Fin n → ZMod 2) ≃ Finset (Fin n) :=
    { toFun := fun y ↦ Finset.univ.filter fun i ↦ y i ≠ 0
      invFun := fun S i ↦ if i ∈ S then 1 else 0
      left_inv := fun y ↦ funext fun i ↦ by
        by_cases h0 : y i = 0
        · simp [h0]
        · simp [zmod2_eq_one_of_ne_zero h0]
      right_inv := fun S ↦ by ext i; simp }
  have hpow : ((Finset.univ : Finset (Fin n)).powersetCard k).card = n.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [f2WeightShell, ← hpow]
  refine Finset.card_bij (fun y _ ↦ e y)
    (fun y hy ↦ Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hy).2⟩)
    (fun _ _ _ _ h ↦ e.injective h)
    (fun S hS ↦ ⟨e.symm S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have heq : hammingNorm (e.symm S) = (e (e.symm S)).card := rfl
      rw [heq, e.apply_symm_apply S]
      exact (Finset.mem_powersetCard.mp hS).2⟩, e.apply_symm_apply S⟩)

/-- Number of Hamming-weight-`k` vectors in `𝔽₂ⁿ` orthogonal to all `T` sample vectors `v`. -/
def dualWeightCount {n T : ℕ} (k : ℕ) (v : Fin T → Fin n → ZMod 2) : ℕ :=
  ((f2WeightShell n k).filter fun y ↦ ∀ j : Fin T, dotProduct (v j) y = 0).card

private lemma card_dotProduct_eq_zero {n : ℕ} {y : Fin n → ZMod 2} (hy : y ≠ 0) :
    ((Finset.univ : Finset (Fin n → ZMod 2)).filter fun u ↦ dotProduct u y = 0).card * 2 =
      2 ^ n := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := Function.ne_iff.mp hy
  have hyi₀ : y i₀ = 1 := zmod2_eq_one_of_ne_zero hi₀
  let S₀ := (Finset.univ : Finset (Fin n → ZMod 2)).filter fun u ↦ dotProduct u y = 0
  let S₁ := (Finset.univ : Finset (Fin n → ZMod 2)).filter fun u ↦ dotProduct u y ≠ 0
  let flip : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun u ↦ Function.update u i₀ (u i₀ + 1)
  have hflip : ∀ u : Fin n → ZMod 2, dotProduct (flip u) y = dotProduct u y + 1 := fun u ↦ by
    simp only [dotProduct, flip]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
      ← Finset.add_sum_erase _ (fun i ↦ u i * y i) (Finset.mem_univ i₀)]
    have hrest : ∑ i ∈ Finset.univ.erase i₀, Function.update u i₀ (u i₀ + 1) i * y i =
        ∑ i ∈ Finset.univ.erase i₀, u i * y i :=
      Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest, Function.update_self, hyi₀]
    ring
  have hinv : ∀ u : Fin n → ZMod 2, flip (flip u) = u := fun u ↦ by
    ext i
    by_cases hi : i = i₀
    · subst hi
      simp only [flip, Function.update_self, add_assoc]
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h11, add_zero]
    · simp [flip, hi]
  have hbij : S₀.card = S₁.card := Finset.card_bij
    (fun u _ ↦ flip u)
    (fun u hu ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hflip, (Finset.mem_filter.mp hu).2, zero_add]; decide⟩)
    (fun u₁ _ u₂ _ h12 ↦ by
      have h2 := congrArg flip h12
      rwa [hinv, hinv] at h2)
    (fun u hu ↦ ⟨flip u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hflip, zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hu).2]; decide⟩, hinv u⟩)
  have htot : S₀.card + S₁.card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_pi]
    simp
  change S₀.card * 2 = 2 ^ n
  omega

private lemma card_dotProduct_pair_eq_zero {n : ℕ} {x y : Fin n → ZMod 2}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    ((Finset.univ : Finset (Fin n → ZMod 2)).filter
      fun u ↦ dotProduct u x = 0 ∧ dotProduct u y = 0).card * 4 = 2 ^ n := by
  have hsum_ne : x + y ≠ 0 := fun h ↦ hxy <| funext fun i ↦
    (zmod2_add_eq_zero_iff (x i) (y i)).mp (congrFun h i)
  let A := (Finset.univ : Finset (Fin n → ZMod 2)).filter fun u ↦ dotProduct u x = 0
  let B := (Finset.univ : Finset (Fin n → ZMod 2)).filter fun u ↦ dotProduct u y = 0
  let C := (Finset.univ : Finset (Fin n → ZMod 2)).filter fun u ↦ dotProduct u (x + y) = 0
  let AB := (Finset.univ : Finset (Fin n → ZMod 2)).filter
    fun u ↦ dotProduct u x = 0 ∧ dotProduct u y = 0
  let A'B' := (Finset.univ : Finset (Fin n → ZMod 2)).filter
    fun u ↦ dotProduct u x ≠ 0 ∧ dotProduct u y ≠ 0
  have hC : C = AB ∪ A'B' := by
    ext u
    simp only [C, AB, A'B', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      dotProduct_add, zmod2_add_eq_zero_iff]
    by_cases h1 : dotProduct u x = 0 <;> by_cases h2 : dotProduct u y = 0
    · simp [h1, h2]
    · simp [h1, zmod2_eq_one_of_ne_zero h2]
    · simp [zmod2_eq_one_of_ne_zero h1, h2]
    · simp [zmod2_eq_one_of_ne_zero h1, zmod2_eq_one_of_ne_zero h2]
  have hdisj : Disjoint AB A'B' := Finset.disjoint_left.mpr fun _ h1 h2 ↦
    (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
  have hCcard : C.card = AB.card + A'B'.card := by rw [hC, Finset.card_union_of_disjoint hdisj]
  have hAuB : (A ∪ B).card + A'B'.card = 2 ^ n := by
    have hdisj2 : Disjoint (A ∪ B) A'B' := Finset.disjoint_left.mpr fun u h1 h2 ↦ by
      rcases Finset.mem_union.mp h1 with hA | hB
      · exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp hA).2
      · exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp hB).2
    have hunion : (A ∪ B) ∪ A'B' = Finset.univ := by
      ext u
      simp only [A, B, A'B', Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      tauto
    rw [← Finset.card_union_of_disjoint hdisj2, hunion, Finset.card_univ, Fintype.card_pi]
    simp
  have hinc : (A ∪ B).card + AB.card = A.card + B.card := by
    have hinter : A ∩ B = AB := by ext u; simp [A, B, AB]
    rw [← hinter, Finset.card_union_add_card_inter]
  have hA : A.card * 2 = 2 ^ n := card_dotProduct_eq_zero hx
  have hB : B.card * 2 = 2 ^ n := card_dotProduct_eq_zero hy
  have hC2 : C.card * 2 = 2 ^ n := card_dotProduct_eq_zero hsum_ne
  change AB.card * 4 = 2 ^ n
  omega

private lemma toReal_uniform_f2 (n : ℕ) (u : Fin n → ZMod 2) :
    (uniformOfFintype (Fin n → ZMod 2) u).toReal = (2 : ℝ)⁻¹ ^ n := by
  rw [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_pi]
  simp [inv_pow]

/-- Exact first moment of the weight-`k` random dual-code count: for `1 ≤ k`,
`𝔼[dualWeightCount k v] = n.choose k / 2^T`. -/
theorem expect_dualWeightCount {n k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    let U := uniformOfFintype (Fin n → ZMod 2)
    (∑ v : Fin T → Fin n → ZMod 2, (iid U T v).toReal * (dualWeightCount k v : ℝ)) =
      (n.choose k : ℝ) / (2 : ℝ) ^ T := by
  intro U
  have hsingle : ∀ y ∈ f2WeightShell n k,
      (∑ v : Fin T → Fin n → ZMod 2,
        if ∀ j, dotProduct (v j) y = 0 then (iid U T v).toReal else 0) = ((2 : ℝ)⁻¹) ^ T := by
    intro y hy
    have hy_ne : y ≠ 0 := by
      intro h0
      have hw := (Finset.mem_filter.mp hy).2
      rw [h0, hammingNorm_zero] at hw
      omega
    rw [sum_iid_pred_pow U T (fun u ↦ dotProduct u y = 0)]
    congr 1
    have h1 : (∑ u : Fin n → ZMod 2, if dotProduct u y = 0 then (U u).toReal else 0) =
        (((Finset.univ.filter fun u ↦ dotProduct u y = 0).card : ℝ)) * (2 : ℝ)⁻¹ ^ n := by
      dsimp only [U]
      simp_rw [toReal_uniform_f2]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Finset.univ.filter fun u ↦ dotProduct u y = 0).card : ℝ)) * 2 = (2 : ℝ) ^ n :=
      by exact_mod_cast card_dotProduct_eq_zero hy_ne
    rw [h1, inv_pow]
    field_simp
    linarith
  calc
    (∑ v : Fin T → Fin n → ZMod 2, (iid U T v).toReal * (dualWeightCount k v : ℝ))
      = ∑ y ∈ f2WeightShell n k, ∑ v : Fin T → Fin n → ZMod 2,
          if ∀ j, dotProduct (v j) y = 0 then (iid U T v).toReal else 0 := by
          simp_rw [dualWeightCount, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
          split_ifs <;> simp
    _ = ∑ _y ∈ f2WeightShell n k, ((2 : ℝ)⁻¹) ^ T := Finset.sum_congr rfl hsingle
    _ = (n.choose k : ℝ) / (2 : ℝ) ^ T := by
          rw [Finset.sum_const, card_f2WeightShell, nsmul_eq_mul, inv_pow, div_eq_mul_inv]

/-- Second moment upper bound `𝔼[(dualWeightCount k v)²] ≤ μ + μ²` where
`μ = n.choose k / 2^T`, proved via pairwise independence of distinct nonzero orthogonality
constraints over `𝔽₂ⁿ`. -/
theorem secondMoment_dualWeightCount_le {n k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    let U := uniformOfFintype (Fin n → ZMod 2)
    let μ : ℝ := (n.choose k : ℝ) / (2 : ℝ) ^ T
    (∑ v : Fin T → Fin n → ZMod 2, (iid U T v).toReal * (dualWeightCount k v : ℝ) ^ 2) ≤
      μ + μ ^ 2 := by
  intro U μ
  have hne : ∀ y ∈ f2WeightShell n k, y ≠ 0 := fun y hy h0 ↦ by
    have hw := (Finset.mem_filter.mp hy).2
    rw [h0, hammingNorm_zero] at hw
    omega
  have hpair : ∀ x ∈ f2WeightShell n k, ∀ y ∈ f2WeightShell n k,
      (∑ v : Fin T → Fin n → ZMod 2,
        if (∀ j, dotProduct (v j) x = 0) ∧ (∀ j, dotProduct (v j) y = 0)
        then (iid U T v).toReal else 0) ≤
        if x = y then ((2 : ℝ)⁻¹) ^ T else ((4 : ℝ)⁻¹) ^ T := by
    intro x hx y hy
    have hmerge : ∀ v : Fin T → Fin n → ZMod 2,
        ((∀ j, dotProduct (v j) x = 0) ∧ (∀ j, dotProduct (v j) y = 0)) ↔
          ∀ j, dotProduct (v j) x = 0 ∧ dotProduct (v j) y = 0 := fun _ ↦ forall_and.symm
    simp_rw [hmerge]
    rw [sum_iid_pred_pow U T (fun u ↦ dotProduct u x = 0 ∧ dotProduct u y = 0)]
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte, and_self]
      refine le_of_eq (congrArg (· ^ T) ?_)
      have hcard :
          (((Finset.univ.filter fun u ↦ dotProduct u x = 0).card : ℝ)) * 2 = (2 : ℝ) ^ n :=
        by exact_mod_cast card_dotProduct_eq_zero (hne x hx)
      dsimp only [U]
      simp_rw [toReal_uniform_f2]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, inv_pow]
      field_simp
      linarith
    · simp only [hxy, ↓reduceIte]
      refine le_of_eq (congrArg (· ^ T) ?_)
      have hcard : (((Finset.univ.filter
          fun u ↦ dotProduct u x = 0 ∧ dotProduct u y = 0).card : ℝ)) * 4 = (2 : ℝ) ^ n :=
        by exact_mod_cast card_dotProduct_pair_eq_zero (hne x hx) (hne y hy) hxy
      dsimp only [U]
      simp_rw [toReal_uniform_f2]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, inv_pow]
      field_simp
      linarith
  have hexpand :
      (∑ v : Fin T → Fin n → ZMod 2, (iid U T v).toReal * (dualWeightCount k v : ℝ) ^ 2) =
        ∑ x ∈ f2WeightShell n k, ∑ y ∈ f2WeightShell n k, ∑ v : Fin T → Fin n → ZMod 2,
          if (∀ j, dotProduct (v j) x = 0) ∧ (∀ j, dotProduct (v j) y = 0)
          then (iid U T v).toReal else 0 := by
    calc
      (∑ v : Fin T → Fin n → ZMod 2, (iid U T v).toReal * (dualWeightCount k v : ℝ) ^ 2)
        = ∑ v, ∑ x ∈ f2WeightShell n k, ∑ y ∈ f2WeightShell n k,
            if (∀ j, dotProduct (v j) x = 0) ∧ (∀ j, dotProduct (v j) y = 0)
            then (iid U T v).toReal else 0 := Finset.sum_congr rfl fun v _ ↦ by
            simp_rw [dualWeightCount, Finset.card_filter, Nat.cast_sum, sq, Finset.sum_mul,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
            by_cases hx : ∀ j, dotProduct (v j) x = 0 <;>
              by_cases hy : ∀ j, dotProduct (v j) y = 0 <;> simp [hx, hy]
      _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  rw [hexpand]
  calc
    ∑ x ∈ f2WeightShell n k, ∑ y ∈ f2WeightShell n k, _
      ≤ ∑ x ∈ f2WeightShell n k, ∑ y ∈ f2WeightShell n k,
          (if x = y then ((2 : ℝ)⁻¹) ^ T else ((4 : ℝ)⁻¹) ^ T) :=
        Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦ hpair x hx y hy
    _ ≤ ∑ x ∈ f2WeightShell n k, ∑ y ∈ f2WeightShell n k,
          ((if x = y then ((2 : ℝ)⁻¹) ^ T else 0) + ((4 : ℝ)⁻¹) ^ T) :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦ by
          by_cases hxy : x = y
          · simp only [hxy, ↓reduceIte, le_add_iff_nonneg_right]; positivity
          · simp only [hxy, ↓reduceIte, zero_add, le_refl]
    _ = μ + μ ^ 2 := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, card_f2WeightShell,
          nsmul_eq_mul]
        have hdiag : ∀ x ∈ f2WeightShell n k,
            (if x ∈ f2WeightShell n k then ((2 : ℝ)⁻¹) ^ T else 0) = ((2 : ℝ)⁻¹) ^ T :=
          fun x hx ↦ by simp [hx]
        rw [Finset.sum_congr rfl hdiag, Finset.sum_const, card_f2WeightShell, nsmul_eq_mul]
        dsimp only [μ]
        have h4 : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
          rw [← pow_right_comm, show (2 : ℝ) ^ 2 = 4 by norm_num]
        rw [inv_pow, inv_pow, div_pow, h4]
        ring

/-- **Paley–Zygmund anti-concentration for random `𝔽₂ⁿ` dual-code weights**: for `1 ≤ k ≤ n`,
`Pr[dualWeightCount k v ≥ 1] ≥ μ / (1 + μ)` where `μ = n.choose k / 2^T`. -/
theorem prob_dualWeightCount_pos_ge {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (T : ℕ) :
    let U := uniformOfFintype (Fin n → ZMod 2)
    let μ : ℝ := (n.choose k : ℝ) / (2 : ℝ) ^ T
    μ / (1 + μ) ≤
      ∑ v : Fin T → Fin n → ZMod 2, if 1 ≤ dualWeightCount k v then (iid U T v).toReal else 0 := by
  intro U μ
  have hμ_pos : 0 < μ := div_pos (Nat.cast_pos.mpr (Nat.choose_pos hkn)) (by positivity)
  set P : ℝ := ∑ v : Fin T → Fin n → ZMod 2,
    if 1 ≤ dualWeightCount k v then (iid U T v).toReal else 0
  set M₂ : ℝ := ∑ v : Fin T → Fin n → ZMod 2, (iid U T v).toReal * (dualWeightCount k v : ℝ) ^ 2
  let a : (Fin T → Fin n → ZMod 2) → ℝ :=
    fun v ↦ Real.sqrt (iid U T v).toReal * (dualWeightCount k v : ℝ)
  let b : (Fin T → Fin n → ZMod 2) → ℝ :=
    fun v ↦ if 1 ≤ dualWeightCount k v then Real.sqrt (iid U T v).toReal else 0
  have hab : ∑ v, a v * b v = μ := by
    dsimp only [μ]
    rw [← expect_dualWeightCount (n := n) hk T]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    dsimp only [a, b]
    by_cases hw : 1 ≤ dualWeightCount k v
    · simp only [hw, ↓reduceIte]
      rw [mul_right_comm, Real.mul_self_sqrt ENNReal.toReal_nonneg]
    · have hw0 : dualWeightCount k v = 0 := by omega
      simp [hw0]
  have ha2 : ∑ v, a v ^ 2 = M₂ := Finset.sum_congr rfl fun v _ ↦ by
    dsimp only [a]; rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hb2 : ∑ v, b v ^ 2 = P := Finset.sum_congr rfl fun v _ ↦ by
    dsimp only [b]
    by_cases hw : 1 ≤ dualWeightCount k v
    · simp only [hw, ↓reduceIte, Real.sq_sqrt ENNReal.toReal_nonneg]
    · simp [hw]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [hab, ha2, hb2] at hcs
  have hM₂ : M₂ ≤ μ * (1 + μ) := by
    linarith [secondMoment_dualWeightCount_le (n := n) (k := k) hk T]
  have hP_nn : 0 ≤ P := Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
  have hmul : μ ^ 2 ≤ μ * (1 + μ) * P := hcs.trans (mul_le_mul_of_nonneg_right hM₂ hP_nn)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Uniform probability mass function on the linear hyperplane `{u ∈ 𝔽₂ⁿ : u · y = 0}` for a
nonzero parity vector `y`. -/
noncomputable def parityHyperplanePMF {n : ℕ} (y : Fin n → ZMod 2) : PMF (Fin n → ZMod 2) :=
  (uniformOfFintype (Fin n → ZMod 2)).filter {u | dotProduct u y = 0}
    ⟨0, by simp, mem_support_uniformOfFintype (0 : Fin n → ZMod 2)⟩

/-- Family of uniform distributions on weight-`k` linear hyperplanes `{u ∈ 𝔽₂ⁿ : u · y = 0}`
(`hammingNorm y = k`). -/
def parityHyperplaneFamily (n k : ℕ) : Set (PMF (Fin n → ZMod 2)) :=
  {D | ∃ y ∈ f2WeightShell n k, D = parityHyperplanePMF y}

private lemma toReal_iid_parityHyperplanePMF {n T : ℕ} {y : Fin n → ZMod 2} (hy : y ≠ 0)
    (v : Fin T → Fin n → ZMod 2) :
    (iid (parityHyperplanePMF y) T v).toReal =
      if ∀ j : Fin T, dotProduct (v j) y = 0 then
        (2 : ℝ) ^ T * (iid (uniformOfFintype (Fin n → ZMod 2)) T v).toReal
      else 0 := by
  let U := uniformOfFintype (Fin n → ZMod 2)
  have hpt : ∀ u : Fin n → ZMod 2,
      (parityHyperplanePMF y u).toReal = if dotProduct u y = 0 then 2 * (U u).toReal else 0 := by
    intro u
    rw [parityHyperplanePMF, PMF.filter_apply]
    have hmass : (∑' w : Fin n → ZMod 2, ({w | dotProduct w y = 0} : Set _).indicator U w) =
        (2 : ℝ≥0∞)⁻¹ := by
      rw [tsum_fintype]
      have hind : ∑ w : Fin n → ZMod 2, ({w | dotProduct w y = 0} : Set _).indicator U w =
          ((Finset.univ.filter fun w ↦ dotProduct w y = 0).card : ℝ≥0∞) *
            ((Fintype.card (Fin n → ZMod 2) : ℕ) : ℝ≥0∞)⁻¹ := by
        have hsum_eq : (∑ w : Fin n → ZMod 2, ({w | dotProduct w y = 0} : Set _).indicator U w) =
            ∑ w ∈ Finset.univ.filter (fun w ↦ dotProduct w y = 0), U w := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun w _ ↦ by
            by_cases hw : dotProduct w y = 0 <;> simp [Set.indicator, hw]
        rw [hsum_eq]
        simp [U, uniformOfFintype_apply]
      rw [hind]
      have hcard_nat : Fintype.card (Fin n → ZMod 2) =
          (Finset.univ.filter fun w ↦ dotProduct w y = 0).card * 2 := by
        rw [card_dotProduct_eq_zero hy, Fintype.card_pi]
        simp
      have hc_ne : ((Finset.univ.filter fun w ↦ dotProduct w y = 0).card : ℝ≥0∞) ≠ 0 := by
        have hpos : 0 < (Finset.univ.filter fun w ↦ dotProduct w y = 0).card :=
          Finset.card_pos.mpr ⟨0, by simp⟩
        exact Nat.cast_ne_zero.mpr hpos.ne'
      rw [hcard_nat, Nat.cast_mul, Nat.cast_ofNat,
        ENNReal.mul_inv (Or.inl hc_ne) (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
        ENNReal.mul_inv_cancel hc_ne (ENNReal.natCast_ne_top _), one_mul]
    rw [hmass, inv_inv]
    by_cases hu : dotProduct u y = 0
    · have hmem : u ∈ {w | dotProduct w y = 0} := hu
      rw [ite_eq_left_iff.mpr fun h ↦ (h hu).elim, Set.indicator_of_mem hmem, ENNReal.toReal_mul,
        ENNReal.toReal_ofNat, mul_comm]
    · have hmem : u ∉ {w | dotProduct w y = 0} := hu
      rw [ite_eq_right_iff.mpr fun h ↦ (hu h).elim, Set.indicator_of_notMem hmem, zero_mul,
        ENNReal.toReal_zero]
  rw [iid_apply, iid_apply, ENNReal.toReal_prod, ENNReal.toReal_prod]
  simp_rw [hpt]
  by_cases hall : ∀ j : Fin T, dotProduct (v j) y = 0
  · rw [ite_eq_left_iff.mpr fun h ↦ (h hall).elim]
    calc
      ∏ j : Fin T, (if dotProduct (v j) y = 0 then 2 * (U (v j)).toReal else 0)
        = ∏ j : Fin T, (2 * (U (v j)).toReal) :=
            Finset.prod_congr rfl fun j _ ↦ ite_eq_left_iff.mpr fun h ↦ (h (hall j)).elim
      _ = (2 : ℝ) ^ T * ∏ j : Fin T, (U (v j)).toReal := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [ite_eq_right_iff.mpr fun h ↦ (hall h).elim]
    push Not at hall
    rcases hall with ⟨j₀, hj₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])

/-- **Sample-complexity lower bound for testing parity-hyperplane truncation over `𝔽₂ⁿ`**: for any
`1 ≤ k < n` and error budget `δ < 1 / 6`, every randomized `T`-sample tester distinguishing the
uniform distribution on `𝔽₂ⁿ` from `parityHyperplaneFamily n k` satisfies
`Nat.clog 2 (n.choose k) < T` (and hence `Real.logb 2 (n.choose k) < T`). -/
theorem parityHyperplane_sample_lower_bound {n k T : ℕ} (hk : 1 ≤ k) (hkn : k < n) {δ : ℝ}
    (hδ : δ < 1 / 6) {A : SampleTester (Fin n → ZMod 2) T}
    (hA : TestsFamily A (uniformOfFintype (Fin n → ZMod 2)) (parityHyperplaneFamily n k) δ) :
    Nat.clog 2 (n.choose k) < T := by
  by_contra hnot
  set T₀ : ℕ := Nat.clog 2 (n.choose k)
  obtain ⟨B, hB⟩ := exists_testsFamily_of_le (not_lt.mp hnot) hA
  set U := uniformOfFintype (Fin n → ZMod 2)
  set S := f2WeightShell n k
  have hchoose_ge : 2 ≤ n.choose k := by
    have hsplit : n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := by
      rcases n with _ | n'
      · omega
      · rcases k with _ | k'
        · omega
        · simpa using Nat.choose_succ_succ n' k'
    have hp1 : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
    have hp2 : 0 < (n - 1).choose k := Nat.choose_pos (by omega)
    omega
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by rw [card_f2WeightShell]; omega)
  have hT₀_pos : 1 ≤ T₀ := Nat.clog_pos one_lt_two (by omega)
  have hpow_ge : n.choose k ≤ 2 ^ T₀ := Nat.le_pow_clog one_lt_two (n.choose k)
  have hpow_lt : 2 ^ (T₀ - 1) < n.choose k :=
    (Nat.clog_le_iff_le_pow one_lt_two).not.mp (by omega : ¬ T₀ ≤ T₀ - 1) |> not_le.mp
  set μ : ℝ := (n.choose k : ℝ) / (2 : ℝ) ^ T₀
  have hμ_le_one : μ ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hpow_ge)
  have hμ_gt_half : 1 / 2 < μ := by
    rw [div_lt_div_iff₀ zero_lt_two (by positivity)]
    have hlt_real : ((2 ^ (T₀ - 1) : ℕ) : ℝ) < (n.choose k : ℝ) := Nat.cast_lt.mpr hpow_lt
    have hpow_split : (2 : ℝ) ^ T₀ = 2 * ((2 ^ (T₀ - 1) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_succ', Nat.sub_add_cancel hT₀_pos]
    linarith
  have hmle_ge :
      (∑ v : Fin T₀ → Fin n → ZMod 2, if 1 ≤ dualWeightCount k v then (iid U T₀ v).toReal else 0) ≤
        acceptProb (mleDistinguisher U S parityHyperplanePMF T₀) U := by
    rw [acceptProb_eq_sum]
    refine Finset.sum_le_sum fun v _ ↦ ?_
    by_cases hw : 1 ≤ dualWeightCount k v
    · have hcmp : (iid U T₀ v).toReal ≤ mixtureLikelihood S parityHyperplanePMF T₀ v := by
        rw [mixtureLikelihood, card_f2WeightShell]
        have hsum_eq : ∑ y ∈ S, (iid (parityHyperplanePMF y) T₀ v).toReal =
            (dualWeightCount k v : ℝ) * (2 : ℝ) ^ T₀ * (iid U T₀ v).toReal := by
          have hterm : ∀ y ∈ S, (iid (parityHyperplanePMF y) T₀ v).toReal =
              if ∀ j, dotProduct (v j) y = 0 then (2 : ℝ) ^ T₀ * (iid U T₀ v).toReal else 0 := by
            intro y hy
            refine toReal_iid_parityHyperplanePMF (fun h0 ↦ ?_) v
            have hnorm := (Finset.mem_filter.mp hy).2
            rw [h0, hammingNorm_zero] at hnorm
            omega
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
            ← mul_assoc]
          rfl
        rw [hsum_eq, le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
        have h1 : (1 : ℝ) ≤ (dualWeightCount k v : ℝ) := by exact_mod_cast hw
        have h2 : (n.choose k : ℝ) ≤ (dualWeightCount k v : ℝ) * (2 : ℝ) ^ T₀ := by
          calc
            (n.choose k : ℝ) ≤ 1 * (2 : ℝ) ^ T₀ := by rw [one_mul]; exact_mod_cast hpow_ge
            _ ≤ (dualWeightCount k v : ℝ) * (2 : ℝ) ^ T₀ :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
        nlinarith [show 0 ≤ (iid U T₀ v).toReal from ENNReal.toReal_nonneg]
      have hmle1 : (mleDistinguisher U S parityHyperplanePMF T₀ v true).toReal = 1 := by
        rw [mleDistinguisher]
        simp only [decide_eq_true hcmp, PMF.pure_apply_self, ENNReal.toReal_one]
      simp [hw, hmle1]
    · simp only [hw, ↓reduceIte]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hpz := prob_dualWeightCount_pos_ge hk hkn.le T₀
  have hthird : (1 / 3 : ℝ) < μ / (1 + μ) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hmle_gt : 2 * δ < acceptProb (mleDistinguisher U S parityHyperplanePMF T₀) U := by
    linarith
  exact testsFamily_not_of_mle_acceptProb_gt (F := parityHyperplaneFamily n k) hS_ne
    (fun y hy ↦ ⟨y, hy, rfl⟩) hmle_gt ⟨B, hB⟩

end RandomDualCode

end CslibFrontier.Computability.PropertyTesting
