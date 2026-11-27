module

public import CslibFrontier.Foundations.BooleanAnalysis.AffinePullback
public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
import CslibFrontier.Foundations.Combinatorics.BinomialTail
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Product Restrictions, Level Thinning, and Random-Index Parity Bounds

This module develops product random restrictions `Res(s)` on Boolean functions, exact Fourier
first and second moment formulas, cumulative low-degree mass level thinning, multi-round
composition, subset survival probabilities, and random-index parity correlation bounds without
flip-noise domination.

## Main definitions

* `CslibFrontier.Foundations.BooleanAnalysis.prodRestrictWeight`: product restriction law `Res(s)`
  on `ι → Option Bool`.
* `CslibFrontier.Foundations.BooleanAnalysis.restrictFun`: restricted Boolean function `f ↾ ρ`.
* `CslibFrontier.Foundations.BooleanAnalysis.aliveSet`: alive coordinate set `{i | ρ i = none}`.
* `CslibFrontier.Foundations.BooleanAnalysis.compRestrict`: sequential composition of two
  restrictions.

## Main results

* `CslibFrontier.Foundations.BooleanAnalysis.sum_filter_exists_eq_none_prodRestrictWeight`: survival
  probability `1 - (1 - s)^{|V|}` that at least one coordinate of `V` remains alive.
* `CslibFrontier.Foundations.BooleanAnalysis.prodRestrict_comp_two`: composition of two independent
  restriction rounds yields a single product restriction at rate `s₁ * s₂`.
* `CslibFrontier.Foundations.BooleanAnalysis.expect_fourierCoeff_restrict`,
  `CslibFrontier.Foundations.BooleanAnalysis.expect_fourierCoeff_restrict_sq`,
  `CslibFrontier.Foundations.BooleanAnalysis.expect_lowDegreeMass_restrict`, and
  `CslibFrontier.Foundations.BooleanAnalysis.expect_abs_fourierCoeff_restrict_le`: Fourier moments
  and level thinning under `Res(s)`.
* `CslibFrontier.Foundations.BooleanAnalysis.expect_abs_fourierCoeff_random_index_le` and
  `CslibFrontier.Foundations.BooleanAnalysis.expect_abs_fourierCoeff_binomial_chernoff_le`:
  random-index parity correlation bounds without flip-noise domination.
-/

public section

namespace CslibFrontier.Foundations.BooleanAnalysis

open Cslib.BitString Finset
open scoped BigOperators

section Restriction

/-- Product restriction weight on `ρ : ι → Option Bool` keeping each coordinate alive (`none`)
with probability `s` and setting it to an unbiased fixed bit (`some false` or `some true`)
with probability `(1 - s) / 2` each. -/
noncomputable def prodRestrictWeight {ι : Type*} [Fintype ι] (s : ℝ) (ρ : ι → Option Bool) : ℝ :=
  ∏ i : ι, match ρ i with
    | none => s
    | some _ => (1 - s) / 2

/-- Apply a restriction `ρ : ι → Option Bool` to a Boolean function `f : (ι → Bool) → ℝ`. -/
def restrictFun {ι : Type*} (f : (ι → Bool) → ℝ) (ρ : ι → Option Bool) (x : ι → Bool) : ℝ :=
  f fun i => (ρ i).getD (x i)

/-- Alive coordinate set `{i | ρ i = none}` of a restriction `ρ`. -/
def aliveSet {ι : Type*} [Fintype ι] (ρ : ι → Option Bool) : Finset ι :=
  Finset.univ.filter fun i => ρ i = none

/-- Composition of two restrictions: `ρ₁` applied first, then `ρ₂` on coordinates still alive. -/
def compRestrict {ι : Type*} (ρ₁ ρ₂ : ι → Option Bool) : ι → Option Bool :=
  fun i => match ρ₁ i with
    | none => ρ₂ i
    | some b => some b

/-- Restricting by the trivial all-alive restriction leaves `f` unchanged. -/
@[simp]
theorem restrictFun_const_none {ι : Type*} (f : (ι → Bool) → ℝ) :
    restrictFun f (fun _ => none) = f := by
  funext x; simp [restrictFun]

/-- The alive set of the trivial all-alive restriction is `Finset.univ`. -/
@[simp]
theorem aliveSet_const_none {ι : Type*} [Fintype ι] :
    aliveSet (fun _ : ι => (none : Option Bool)) = Finset.univ := by
  ext i; simp [aliveSet]

/-- Left identity of `compRestrict` at the all-alive restriction. -/
@[simp]
theorem compRestrict_const_none_left {ι : Type*} (ρ : ι → Option Bool) :
    compRestrict (fun _ => none) ρ = ρ := by
  funext i; simp [compRestrict]

/-- Composition law `restrictFun (restrictFun f ρ₁) ρ₂ = restrictFun f (compRestrict ρ₁ ρ₂)`. -/
theorem restrictFun_comp {ι : Type*} (f : (ι → Bool) → ℝ) (ρ₁ ρ₂ : ι → Option Bool) :
    restrictFun (restrictFun f ρ₁) ρ₂ = restrictFun f (compRestrict ρ₁ ρ₂) := by
  funext x
  simp only [restrictFun, compRestrict]
  congr 1
  funext i
  cases ρ₁ i <;> rfl

/-- Product restriction weights are nonnegative for `s ∈ [0, 1]`. -/
theorem prodRestrictWeight_nonneg {ι : Type*} [Fintype ι] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ρ : ι → Option Bool) :
    0 ≤ prodRestrictWeight s ρ := by
  refine Finset.prod_nonneg fun i _ => ?_
  cases ρ i <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product restriction weights sum to `1`. -/
theorem sum_prodRestrictWeight (s : ℝ) :
    ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ = 1 := by
  let g : ι → Option Bool → ℝ := fun _ o =>
    match o with | none => s | some _ => (1 - s) / 2
  have hpt : ∀ ρ : ι → Option Bool, prodRestrictWeight s ρ = ∏ i : ι, g i (ρ i) := fun _ => rfl
  rw [Finset.sum_congr rfl fun ρ _ => hpt ρ, ← Fintype.prod_sum g]
  refine Finset.prod_eq_one fun _ _ => ?_
  dsimp only [g]
  have hsum : (∑ o : Option Bool, match o with | none => s | some _ => (1 - s) / 2) =
      s + (1 - s) / 2 + (1 - s) / 2 := by
    simp only [Fintype.sum_option, Fintype.sum_bool]
    ring
  rw [hsum]
  ring

/-- For any subset `V : Finset ι`, the probability under `Res(s)` that at least one coordinate in
`V` remains alive (`none`) equals `1 - (1 - s) ^ V.card`. -/
theorem sum_filter_exists_eq_none_prodRestrictWeight (s : ℝ) (V : Finset ι) :
    ∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => ∃ v ∈ V, ρ v = none),
      prodRestrictWeight s ρ = 1 - (1 - s) ^ V.card := by
  have hcompl :
      (∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => ∃ v ∈ V, ρ v = none),
          prodRestrictWeight s ρ) +
      (∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => ∀ v ∈ V, ρ v ≠ none),
          prodRestrictWeight s ρ) = 1 := by
    have htot := sum_prodRestrictWeight (ι := ι) s
    rw [← htot, ← Finset.sum_union]
    · congr 1
      ext ρ
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : ∃ v ∈ V, ρ v = none
      · exact iff_true_intro (Or.inl h)
      · push Not at h
        exact iff_true_intro (Or.inr h)
    · rw [Finset.disjoint_left]
      intro ρ h1 h2
      obtain ⟨v, hv, hnone⟩ := (Finset.mem_filter.mp h1).2
      exact (Finset.mem_filter.mp h2).2 v hv hnone
  have hdead :
      ∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => ∀ v ∈ V, ρ v ≠ none),
          prodRestrictWeight s ρ = (1 - s) ^ V.card := by
    rw [Finset.sum_filter]
    let g : ι → Option Bool → ℝ := fun v o =>
      if v ∈ V then (match o with | none => 0 | some _ => (1 - s) / 2)
      else (match o with | none => s | some _ => (1 - s) / 2)
    have hpt : ∀ ρ : ι → Option Bool,
        (if ∀ v ∈ V, ρ v ≠ none then prodRestrictWeight s ρ else 0) =
        ∏ v : ι, g v (ρ v) := by
      intro ρ
      split_ifs with hall
      · simp only [prodRestrictWeight, g]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : v ∈ V
        · cases hρ : ρ v with
          | none => exact False.elim (hall v hv hρ)
          | some _ => simp [hv]
        · simp [hv]
      · push Not at hall
        obtain ⟨v, hv, hnone⟩ := hall
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [g, hv, hnone])
    rw [Finset.sum_congr rfl fun ρ _ => hpt ρ, ← Fintype.prod_sum g]
    have hfac : (∏ v : ι, ∑ o : Option Bool, g v o) =
        ∏ v : ι, if v ∈ V then 1 - s else 1 := by
      refine Finset.prod_congr rfl fun v _ => ?_
      dsimp only [g]
      by_cases hv : v ∈ V <;> simp only [hv, ↓reduceIte, Fintype.sum_option, Fintype.sum_bool] <;>
        ring
    rw [hfac, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  linarith

/-- **Composition of independent restriction rounds**: pushing forward two independent product
restrictions with survival rates `s₁` and `s₂` via `compRestrict` yields
`prodRestrictWeight (s₁ * s₂)`. -/
theorem prodRestrict_comp_two (s₁ s₂ : ℝ) (ρ : ι → Option Bool) :
    ∑ ρ₁ : ι → Option Bool, ∑ ρ₂ : ι → Option Bool,
      (if compRestrict ρ₁ ρ₂ = ρ then prodRestrictWeight s₁ ρ₁ * prodRestrictWeight s₂ ρ₂ else 0) =
    prodRestrictWeight (s₁ * s₂) ρ := by
  let g : ι → Option Bool × Option Bool → ℝ := fun i q =>
    if (match q.1 with | none => q.2 | some b => some b) = ρ i then
      (match q.1 with | none => s₁ | some _ => (1 - s₁) / 2) *
      (match q.2 with | none => s₂ | some _ => (1 - s₂) / 2)
    else 0
  have hrew :
      ∀ (ρ₁ ρ₂ : ι → Option Bool),
        (if compRestrict ρ₁ ρ₂ = ρ then prodRestrictWeight s₁ ρ₁ * prodRestrictWeight s₂ ρ₂
          else 0) =
        ∏ i : ι, g i (ρ₁ i, ρ₂ i) := by
    intro ρ₁ ρ₂
    split_ifs with h
    · have hpt : ∀ i : ι, (match ρ₁ i with | none => ρ₂ i | some b => some b) = ρ i :=
        fun i => congrFun h i
      simp only [g, hpt, ↓reduceIte, prodRestrictWeight, Finset.prod_mul_distrib]
    · have hex : ∃ i : ι, (match ρ₁ i with | none => ρ₂ i | some b => some b) ≠ ρ i := by
        by_contra hall
        push Not at hall
        exact h (funext hall)
      obtain ⟨i, hi⟩ := hex
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hi])
  simp_rw [hrew]
  have hpair :
      (∑ ρ₁ : ι → Option Bool, ∑ ρ₂ : ι → Option Bool, ∏ i : ι, g i (ρ₁ i, ρ₂ i)) =
      ∑ p : ι → Option Bool × Option Bool, ∏ i : ι, g i (p i) := by
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun _ => rfl
  rw [hpair, ← Fintype.prod_sum g, prodRestrictWeight]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only [g]
  cases ρ i with
  | none =>
    simp [Fintype.sum_prod_type, Fintype.sum_option]
  | some b =>
    cases b <;>
      simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, Option.some.injEq,
        reduceCtorEq, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] <;>
      ring

/-- Exact Fourier coefficient of a restricted function `restrictFun f ρ`. -/
theorem fourierCoeff_restrictFun (f : (ι → Bool) → ℝ) (ρ : ι → Option Bool) (S : Finset ι) :
    fourierCoeff (restrictFun f ρ) S =
      if S ⊆ aliveSet ρ then
        ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U ∩ aliveSet ρ = S),
          fourierCoeff f U * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
      else 0 := by
  have hexp : restrictFun f ρ = fun x =>
      ∑ U : Finset ι,
        (fourierCoeff f U * ∏ i ∈ U \ aliveSet ρ, signVal ((ρ i).getD false)) *
          chi ℝ (U ∩ aliveSet ρ) x := by
    funext x
    simp only [restrictFun]
    rw [← sum_fourierCoeff_mul_chi f]
    refine Finset.sum_congr rfl fun U _ => ?_
    have hsplit : chi ℝ U (fun i => (ρ i).getD (x i)) =
        (∏ i ∈ U \ aliveSet ρ, signVal ((ρ i).getD false)) * chi ℝ (U ∩ aliveSet ρ) x := by
      simp only [chi_eq_prod_signVal]
      conv_lhs => rw [← Finset.sdiff_union_inter U (aliveSet ρ)]
      rw [Finset.prod_union (Finset.disjoint_sdiff_inter U (aliveSet ρ))]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hdead : ρ i ≠ none := fun h =>
          (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        cases hρ : ρ i with
        | none => exact False.elim (hdead hρ)
        | some b => simp
      · refine Finset.prod_congr rfl fun i hi => ?_
        have halive : ρ i = none := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
        simp [halive]
    rw [hsplit]
    ring
  rw [hexp, fourierCoeff_sum_mul]
  have hchi : ∀ U : Finset ι,
      fourierCoeff (chi ℝ (U ∩ aliveSet ρ)) S = if U ∩ aliveSet ρ = S then 1 else 0 :=
    fun U => fourierCoeff_chi _ _
  simp_rw [hchi]
  by_cases hS : S ⊆ aliveSet ρ
  · simp only [hS, ↓reduceIte, Finset.sum_filter]
    refine Finset.sum_congr rfl fun U _ => ?_
    by_cases hU : U ∩ aliveSet ρ = S
    · simp only [hU, ↓reduceIte, mul_one]
      have hsdiff : U \ aliveSet ρ = U \ S := by
        rw [← hU]
        ext i; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      rw [hsdiff]
    · simp [hU]
  · simp only [hS, ↓reduceIte]
    refine Finset.sum_eq_zero fun U _ => ?_
    have hne : U ∩ aliveSet ρ ≠ S := fun h => hS (h ▸ Finset.inter_subset_right)
    simp [hne]

/-- **First moment of restricted Fourier coefficients** (`lem:restrict-level-thinning` (i)):
`E_{ρ ~ Res(s)}[widehat{p ↾ ρ}(S)] = s^{|S|} p̂(S)`. -/
theorem expect_fourierCoeff_restrict (s : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * fourierCoeff (restrictFun f ρ) S =
      s ^ S.card * fourierCoeff f S := by
  simp_rw [fourierCoeff_restrictFun]
  have hswap :
      ∑ ρ : ι → Option Bool,
        prodRestrictWeight s ρ *
          (if S ⊆ aliveSet ρ then
            ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U ∩ aliveSet ρ = S),
              fourierCoeff f U * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
          else 0) =
      ∑ U : Finset ι,
        fourierCoeff f U *
          ∑ ρ : ι → Option Bool,
            if S ⊆ aliveSet ρ ∧ U ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
            else 0 := by
    have h1 : ∀ ρ : ι → Option Bool,
        prodRestrictWeight s ρ *
          (if S ⊆ aliveSet ρ then
            ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U ∩ aliveSet ρ = S),
              fourierCoeff f U * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
          else 0) =
        ∑ U : Finset ι,
          fourierCoeff f U *
            (if S ⊆ aliveSet ρ ∧ U ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
            else 0) := by
      intro ρ
      by_cases hS : S ⊆ aliveSet ρ
      · simp only [hS, ↓reduceIte, true_and, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun U _ => ?_
        split_ifs <;> ring
      · simp [hS]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun U _ => by rw [Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ U : Finset ι,
      (∑ ρ : ι → Option Bool,
        if S ⊆ aliveSet ρ ∧ U ∩ aliveSet ρ = S then
          prodRestrictWeight s ρ * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
        else 0) =
      if U = S then s ^ S.card else 0 := by
    intro U
    have hcond : ∀ ρ : ι → Option Bool,
        (S ⊆ aliveSet ρ ∧ U ∩ aliveSet ρ = S) ↔
          (S ⊆ U ∧ ∀ i : ι, (i ∈ S → ρ i = none) ∧ (i ∈ U \ S → ρ i ≠ none)) := by
      intro ρ
      constructor
      · rintro ⟨hS, hU⟩
        refine ⟨hU ▸ Finset.inter_subset_left, fun i => ⟨fun hi =>
          (Finset.mem_filter.mp (hS hi)).2, fun hi hnone => ?_⟩⟩
        have hmem : i ∈ U ∩ aliveSet ρ :=
          Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi).1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
        rw [hU] at hmem
        exact (Finset.mem_sdiff.mp hi).2 hmem
      · rintro ⟨hSU, hall⟩
        refine ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hall i).1 hi⟩, ?_⟩
        ext i
        simp only [Finset.mem_inter, aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hiU, hnone⟩
          by_contra hiS
          exact (hall i).2 (Finset.mem_sdiff.mpr ⟨hiU, hiS⟩) hnone
        · intro hiS
          exact ⟨hSU hiS, (hall i).1 hiS⟩
    by_cases hSU : S ⊆ U
    · have hprod :
          (∑ ρ : ι → Option Bool,
            if S ⊆ aliveSet ρ ∧ U ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
            else 0) =
          ∏ i : ι,
            if i ∈ S then s
            else if i ∈ U \ S then
              ((1 - s) / 2) * signVal false + ((1 - s) / 2) * signVal true
            else 1 := by
        let g : ι → Option Bool → ℝ := fun i o =>
          if i ∈ S then (if o = none then s else 0)
          else if i ∈ U \ S then
            (match o with | none => 0 | some b => ((1 - s) / 2) * signVal b)
          else (match o with | none => s | some _ => (1 - s) / 2)
        have hpt : ∀ ρ : ι → Option Bool,
            (if S ⊆ aliveSet ρ ∧ U ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
            else 0) =
            ∏ i : ι, g i (ρ i) := by
          intro ρ
          split_ifs with hc
          · have hall := ((hcond ρ).mp hc).2
            simp only [prodRestrictWeight, g]
            have hfac : (∏ i ∈ U \ S, signVal ((ρ i).getD false)) =
                ∏ i : ι, if i ∈ U \ S then signVal ((ρ i).getD false) else 1 := by
              rw [Finset.prod_ite_mem, Finset.univ_inter]
            rw [hfac, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun i _ => ?_
            by_cases hiS : i ∈ S
            · have hnone := (hall i).1 hiS
              have hnot : i ∉ U \ S := fun h => (Finset.mem_sdiff.mp h).2 hiS
              simp [hiS, hnot, hnone]
            · by_cases hiUS : i ∈ U \ S
              · have hdead := (hall i).2 hiUS
                cases hρ : ρ i with
                | none => exact False.elim (hdead hρ)
                | some b => simp [hiS, hiUS]
              · simp [hiS, hiUS]
          · have hall : ¬ ∀ i : ι, (i ∈ S → ρ i = none) ∧ (i ∈ U \ S → ρ i ≠ none) :=
              fun h => hc ((hcond ρ).mpr ⟨hSU, h⟩)
            obtain ⟨i, hi⟩ := Classical.not_forall.mp hall
            symm
            refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
            dsimp only [g]
            rcases not_and_or.mp hi with h1 | h2
            · obtain ⟨hiS, hne⟩ := Classical.not_imp.mp h1
              simp [hiS, hne]
            · obtain ⟨hiUS, hnone⟩ := Classical.not_imp.mp h2
              have hnotS : i ∉ S := (Finset.mem_sdiff.mp hiUS).2
              simp [hnotS, hiUS, not_not.mp hnone]
        rw [Finset.sum_congr rfl fun ρ _ => hpt ρ, ← Fintype.prod_sum g]
        refine Finset.prod_congr rfl fun i _ => ?_
        dsimp only [g]
        by_cases hiS : i ∈ S
        · simp [hiS]
        · by_cases hiUS : i ∈ U \ S
          · simp [hiS, hiUS, Fintype.sum_option]
          · simp only [hiS, hiUS, ↓reduceIte, Fintype.sum_option, Fintype.sum_bool]
            ring
      rw [hprod]
      by_cases hUS : U = S
      · subst hUS
        simp only [↓reduceIte]
        have h1 : (∏ i : ι,
            if i ∈ U then s
            else if i ∈ U \ U then
              ((1 - s) / 2) * signVal false + ((1 - s) / 2) * signVal true
            else 1) = ∏ i : ι, if i ∈ U then s else 1 := by
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hi : i ∈ U <;> simp [hi]
        rw [h1, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      · simp only [hUS, ↓reduceIte]
        have hne : (U \ S).Nonempty :=
          Finset.sdiff_nonempty.mpr fun h => hUS (Finset.Subset.antisymm h hSU)
        obtain ⟨i, hi⟩ := hne
        have hnotS : i ∉ S := (Finset.mem_sdiff.mp hi).2
        have hcancel : ((1 - s) / 2) * signVal false + ((1 - s) / 2) * signVal true = 0 := by
          simp [signVal]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp only [hnotS, hi, ↓reduceIte, hcancel]
    · have hne : U ≠ S := fun h => hSU (h ▸ subset_rfl)
      simp only [hne, ↓reduceIte]
      refine Finset.sum_eq_zero fun ρ _ => ?_
      split_ifs with hc
      · exact False.elim (hSU ((hcond ρ).mp hc).1)
      · rfl
  simp_rw [hinner]
  rw [Finset.sum_eq_single S]
  · simp [mul_comm]
  · intro U _ hne; simp [hne]
  · intro h; exact False.elim (h (Finset.mem_univ _))

/-- Product-restriction sign cancellation: the cross-term between distinct subsets `U₁ ≠ U₂`
containing `S` vanishes in expectation over `ρ ~ Res(s)`. -/
private theorem expect_restrict_cross_term (s : ℝ) (S U₁ U₂ : Finset ι)
    (hSU₁ : S ⊆ U₁) (hSU₂ : S ⊆ U₂) :
    (∑ ρ : ι → Option Bool,
      if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
        prodRestrictWeight s ρ *
          (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
          (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
      else 0) =
    if U₁ = U₂ then s ^ S.card * (1 - s) ^ (U₁ \ S).card else 0 := by
  have hcond : ∀ ρ : ι → Option Bool,
      (S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S) ↔
        ∀ i : ι, (i ∈ S → ρ i = none) ∧ (i ∈ (U₁ \ S) ∪ (U₂ \ S) → ρ i ≠ none) := by
    intro ρ
    constructor
    · rintro ⟨hS, hU₁, hU₂⟩ i
      refine ⟨fun hi => (Finset.mem_filter.mp (hS hi)).2, fun hi hnone => ?_⟩
      rcases Finset.mem_union.mp hi with hi1 | hi2
      · have hmem : i ∈ U₁ ∩ aliveSet ρ :=
          Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi1).1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
        rw [hU₁] at hmem; exact (Finset.mem_sdiff.mp hi1).2 hmem
      · have hmem : i ∈ U₂ ∩ aliveSet ρ :=
          Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi2).1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
        rw [hU₂] at hmem; exact (Finset.mem_sdiff.mp hi2).2 hmem
    · intro hall
      refine ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hall i).1 hi⟩, ?_, ?_⟩
      · ext i
        simp only [Finset.mem_inter, aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨hiU, hnone⟩ => by_contra fun hiS =>
          (hall i).2 (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hiU, hiS⟩)) hnone,
          fun hiS => ⟨hSU₁ hiS, (hall i).1 hiS⟩⟩
      · ext i
        simp only [Finset.mem_inter, aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨hiU, hnone⟩ => by_contra fun hiS =>
          (hall i).2 (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hiU, hiS⟩)) hnone,
          fun hiS => ⟨hSU₂ hiS, (hall i).1 hiS⟩⟩
  have hprod :
      (∑ ρ : ι → Option Bool,
        if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
          prodRestrictWeight s ρ *
            (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
            (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
        else 0) =
      ∏ i : ι,
        if i ∈ S then s
        else if i ∈ (U₁ \ S) ∩ (U₂ \ S) then 1 - s
        else if i ∈ (U₁ \ S) ∪ (U₂ \ S) then
          ((1 - s) / 2) * signVal false + ((1 - s) / 2) * signVal true
        else 1 := by
    let g : ι → Option Bool → ℝ := fun i o =>
      if i ∈ S then (if o = none then s else 0)
      else if i ∈ (U₁ \ S) ∩ (U₂ \ S) then
        (match o with | none => 0 | some _ => (1 - s) / 2)
      else if i ∈ (U₁ \ S) ∪ (U₂ \ S) then
        (match o with | none => 0 | some b => ((1 - s) / 2) * signVal b)
      else (match o with | none => s | some _ => (1 - s) / 2)
    have hpt : ∀ ρ : ι → Option Bool,
        (if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
          prodRestrictWeight s ρ *
            (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
            (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
        else 0) =
        ∏ i : ι, g i (ρ i) := by
      intro ρ
      split_ifs with hc
      · have hall := (hcond ρ).mp hc
        simp only [prodRestrictWeight, g]
        have hf1 : (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) =
            ∏ i : ι, if i ∈ U₁ \ S then signVal ((ρ i).getD false) else 1 := by
          rw [Finset.prod_ite_mem, Finset.univ_inter]
        have hf2 : (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false)) =
            ∏ i : ι, if i ∈ U₂ \ S then signVal ((ρ i).getD false) else 1 := by
          rw [Finset.prod_ite_mem, Finset.univ_inter]
        rw [hf1, hf2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hiS : i ∈ S
        · have hnone := (hall i).1 hiS
          have hn1 : i ∉ U₁ \ S := fun h => (Finset.mem_sdiff.mp h).2 hiS
          have hn2 : i ∉ U₂ \ S := fun h => (Finset.mem_sdiff.mp h).2 hiS
          simp [hiS, hn1, hn2, hnone]
        · by_cases h1 : i ∈ U₁ \ S <;> by_cases h2 : i ∈ U₂ \ S
          · have hdead := (hall i).2 (Finset.mem_union_left _ h1)
            cases hρ : ρ i with
            | none => exact False.elim (hdead hρ)
            | some b =>
              have hsq : signVal b * signVal b = 1 := by cases b <;> norm_num [signVal]
              simp only [hiS, Finset.mem_inter, h1, h2, and_self, ↓reduceIte, Option.getD_some]
              linarith [mul_assoc ((1 - s) / 2) (signVal b) (signVal b),
                show ((1 - s) / 2) * signVal b * signVal b = (1 - s) / 2 by
                  rw [mul_assoc, hsq, mul_one]]
          · have hdead := (hall i).2 (Finset.mem_union_left _ h1)
            cases hρ : ρ i with
            | none => exact False.elim (hdead hρ)
            | some b => simp [hiS, h1, h2]
          · have hdead := (hall i).2 (Finset.mem_union_right _ h2)
            cases hρ : ρ i with
            | none => exact False.elim (hdead hρ)
            | some b => simp [hiS, h1, h2]
          · simp [hiS, h1, h2]
      · have hall : ¬ ∀ i : ι, (i ∈ S → ρ i = none) ∧ (i ∈ (U₁ \ S) ∪ (U₂ \ S) → ρ i ≠ none) :=
          mt (hcond ρ).mpr hc
        obtain ⟨i, hi⟩ := Classical.not_forall.mp hall
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        dsimp only [g]
        rcases not_and_or.mp hi with h1 | h2
        · obtain ⟨hiS, hne⟩ := Classical.not_imp.mp h1
          simp [hiS, hne]
        · obtain ⟨hiU, hnone_nn⟩ := Classical.not_imp.mp h2
          have hnone : ρ i = none := not_not.mp hnone_nn
          have hnotS : i ∉ S := by
            rcases Finset.mem_union.mp hiU with h | h <;> exact (Finset.mem_sdiff.mp h).2
          by_cases hint : i ∈ (U₁ \ S) ∩ (U₂ \ S)
          · simp [hnotS, hint, hnone]
          · simp [hnotS, hint, hiU, hnone]
    rw [Finset.sum_congr rfl fun ρ _ => hpt ρ, ← Fintype.prod_sum g]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [g]
    by_cases hiS : i ∈ S
    · simp [hiS]
    · by_cases hint : i ∈ (U₁ \ S) ∩ (U₂ \ S)
      · simp only [hiS, hint, ↓reduceIte, Fintype.sum_option, Fintype.sum_bool]
        ring
      · by_cases hunion : i ∈ (U₁ \ S) ∪ (U₂ \ S)
        · simp [hiS, hint, hunion, Fintype.sum_option]
        · simp only [hiS, hint, hunion, ↓reduceIte, Fintype.sum_option, Fintype.sum_bool]
          ring
  rw [hprod]
  by_cases hU : U₁ = U₂
  · subst hU
    simp only [↓reduceIte]
    have hcollapse :
        (∏ i : ι,
          if i ∈ S then s
          else if i ∈ (U₁ \ S) ∩ (U₁ \ S) then 1 - s
          else if i ∈ (U₁ \ S) ∪ (U₁ \ S) then
            ((1 - s) / 2) * signVal false + ((1 - s) / 2) * signVal true
          else 1) =
        ∏ i : ι, if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hiS : i ∈ S
      · simp [hiS]
      · by_cases hiU : i ∈ U₁ \ S <;> simp [hiS, hiU]
    rw [hcollapse]
    have hdisj : Disjoint S (U₁ \ S) := Finset.disjoint_sdiff
    have h1 : (∏ i : ι, if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1) =
        ∏ i ∈ S ∪ (U₁ \ S), if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1 := by
      symm
      refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
      have hn1 : i ∉ S := fun h => hi (Finset.mem_union_left _ h)
      have hn2 : i ∉ U₁ \ S := fun h => hi (Finset.mem_union_right _ h)
      simp [hn1, hn2]
    rw [h1, Finset.prod_union hdisj]
    have hp1 : (∏ i ∈ S, if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1) = s ^ S.card := by
      have hc1 : (∏ i ∈ S, if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1) = ∏ _i ∈ S, s :=
        Finset.prod_congr rfl fun i hi => by simp [hi]
      rw [hc1, Finset.prod_const]
    have hp2 : (∏ i ∈ U₁ \ S, if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1) =
        (1 - s) ^ (U₁ \ S).card := by
      have hc2 : (∏ i ∈ U₁ \ S, if i ∈ S then s else if i ∈ U₁ \ S then 1 - s else 1) =
          ∏ _i ∈ U₁ \ S, (1 - s) :=
        Finset.prod_congr rfl fun i hi => by simp [Finset.disjoint_right.mp hdisj hi, hi]
      rw [hc2, Finset.prod_const]
    rw [hp1, hp2]
  · simp only [hU, ↓reduceIte]
    have hdiff : ∃ i : ι, i ∈ (U₁ \ S) ∪ (U₂ \ S) ∧ i ∉ (U₁ \ S) ∩ (U₂ \ S) := by
      by_contra hall
      push Not at hall
      apply hU
      ext i
      by_cases hiS : i ∈ S
      · exact ⟨fun _ => hSU₂ hiS, fun _ => hSU₁ hiS⟩
      · constructor
        · intro hi1
          have hm : i ∈ U₁ \ S := Finset.mem_sdiff.mpr ⟨hi1, hiS⟩
          have hmem := hall i (Finset.mem_union_left _ hm)
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hmem).2).1
        · intro hi2
          have hm : i ∈ U₂ \ S := Finset.mem_sdiff.mpr ⟨hi2, hiS⟩
          have hmem := hall i (Finset.mem_union_right _ hm)
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hmem).1).1
    obtain ⟨i, hunion, hnotint⟩ := hdiff
    have hnotS : i ∉ S := by
      rcases Finset.mem_union.mp hunion with h | h <;> exact (Finset.mem_sdiff.mp h).2
    have hcancel : ((1 - s) / 2) * signVal false + ((1 - s) / 2) * signVal true = 0 := by
      simp [signVal]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [hnotS, hnotint, hunion, ↓reduceIte, hcancel]

/-- **Second moment of restricted Fourier coefficients** (`lem:restrict-level-thinning` (ii)):
`E_{ρ ~ Res(s)}[widehat{p ↾ ρ}(S)²] = s^{|S|} ∑_{T ⊆ Sᶜ} (1 - s)^{|T|} p̂(S ∪ T)²`. -/
theorem expect_fourierCoeff_restrict_sq (s : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * fourierCoeff (restrictFun f ρ) S ^ 2 =
      s ^ S.card * ∑ T ∈ Sᶜ.powerset, (1 - s) ^ T.card * fourierCoeff f (S ∪ T) ^ 2 := by
  simp_rw [fourierCoeff_restrictFun]
  have hsq : ∀ ρ : ι → Option Bool,
      prodRestrictWeight s ρ *
        (if S ⊆ aliveSet ρ then
          ∑ U ∈ Finset.univ.filter (fun U : Finset ι => U ∩ aliveSet ρ = S),
            fourierCoeff f U * ∏ i ∈ U \ S, signVal ((ρ i).getD false)
        else 0) ^ 2 =
      ∑ U₁ : Finset ι, ∑ U₂ : Finset ι,
        fourierCoeff f U₁ * fourierCoeff f U₂ *
          (if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
            prodRestrictWeight s ρ *
              (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
              (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
          else 0) := by
    intro ρ
    by_cases hS : S ⊆ aliveSet ρ
    · simp only [hS, ↓reduceIte, true_and, sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun U₁ _ => Finset.sum_congr rfl fun U₂ _ => ?_
      by_cases h1 : U₁ ∩ aliveSet ρ = S <;> by_cases h2 : U₂ ∩ aliveSet ρ = S <;>
        simp only [h1, h2, and_self, and_false, false_and, ↓reduceIte] <;> ring
    · simp [hS]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  have hswap :
      (∑ U₁ : Finset ι, ∑ ρ : ι → Option Bool, ∑ U₂ : Finset ι,
        fourierCoeff f U₁ * fourierCoeff f U₂ *
          (if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
            prodRestrictWeight s ρ *
              (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
              (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
          else 0)) =
      ∑ U₁ : Finset ι, ∑ U₂ : Finset ι,
        fourierCoeff f U₁ * fourierCoeff f U₂ *
          ∑ ρ : ι → Option Bool,
            if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ *
                (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
                (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
            else 0 := by
    refine Finset.sum_congr rfl fun U₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun U₂ _ => by rw [Finset.mul_sum]
  rw [hswap]
  have heval :
      (∑ U₁ : Finset ι, ∑ U₂ : Finset ι,
        fourierCoeff f U₁ * fourierCoeff f U₂ *
          ∑ ρ : ι → Option Bool,
            if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ *
                (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
                (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
            else 0) =
      ∑ U ∈ Finset.univ.filter (fun U : Finset ι => S ⊆ U),
        fourierCoeff f U ^ 2 * (s ^ S.card * (1 - s) ^ (U \ S).card) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun U₁ _ => ?_
    by_cases hSU₁ : S ⊆ U₁
    · simp only [hSU₁, ↓reduceIte]
      rw [Finset.sum_eq_single U₁]
      · rw [expect_restrict_cross_term s S U₁ U₁ hSU₁ hSU₁]
        simp [sq]
      · intro U₂ _ hne
        by_cases hSU₂ : S ⊆ U₂
        · rw [expect_restrict_cross_term s S U₁ U₂ hSU₁ hSU₂]
          simp [hne.symm]
        · have h0 :
              (∑ ρ : ι → Option Bool,
                if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
                  prodRestrictWeight s ρ *
                    (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
                    (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
                else 0) = 0 := by
            refine Finset.sum_eq_zero fun ρ _ => ?_
            have hnot : ¬ (U₂ ∩ aliveSet ρ = S) := fun h => hSU₂ (h ▸ Finset.inter_subset_left)
            simp [hnot]
          simp [h0]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    · simp only [hSU₁, ↓reduceIte]
      refine Finset.sum_eq_zero fun U₂ _ => ?_
      have h0 :
          (∑ ρ : ι → Option Bool,
            if S ⊆ aliveSet ρ ∧ U₁ ∩ aliveSet ρ = S ∧ U₂ ∩ aliveSet ρ = S then
              prodRestrictWeight s ρ *
                (∏ i ∈ U₁ \ S, signVal ((ρ i).getD false)) *
                (∏ i ∈ U₂ \ S, signVal ((ρ i).getD false))
            else 0) = 0 := by
        refine Finset.sum_eq_zero fun ρ _ => ?_
        have hnot : ¬ (U₁ ∩ aliveSet ρ = S) := fun h => hSU₁ (h ▸ Finset.inter_subset_left)
        simp [hnot]
      simp [h0]
  rw [heval, Finset.mul_sum]
  refine Finset.sum_bij (fun U _ => U \ S)
    (fun U hU => Finset.mem_powerset.mpr (fun i hi =>
      Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2))
    (fun U₁ hU₁ U₂ hU₂ h => by
      have h1 : S ⊆ U₁ := (Finset.mem_filter.mp hU₁).2
      have h2 : S ⊆ U₂ := (Finset.mem_filter.mp hU₂).2
      rw [← Finset.union_sdiff_of_subset h1, h, Finset.union_sdiff_of_subset h2])
    (fun T hT => ⟨S ∪ T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩, by
      have hdisj : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro i hiS hiT
        exact (Finset.mem_compl.mp (Finset.mem_powerset.mp hT hiT)) hiS
      exact Finset.union_sdiff_cancel_left hdisj⟩)
    (fun U hU => by
      have hSU : S ⊆ U := (Finset.mem_filter.mp hU).2
      rw [Finset.union_sdiff_of_subset hSU]
      ring)

/-- Upper bound corollary of the second moment (`lem:restrict-level-thinning` (ii)): for
`s ∈ [0, 1]`, `E_ρ[widehat{p ↾ ρ}(S)²] ≤ s^{|S|} ∑_{U ⊇ S} p̂(U)²`. -/
theorem expect_fourierCoeff_restrict_sq_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (f : (ι → Bool) → ℝ) (S : Finset ι) :
    ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * fourierCoeff (restrictFun f ρ) S ^ 2 ≤
      s ^ S.card * ∑ U ∈ Finset.univ.filter (fun U : Finset ι => S ⊆ U), fourierCoeff f U ^ 2 := by
  rw [expect_fourierCoeff_restrict_sq]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs0 _)
  have h1 :
      ∑ T ∈ Sᶜ.powerset, (1 - s) ^ T.card * fourierCoeff f (S ∪ T) ^ 2 ≤
      ∑ T ∈ Sᶜ.powerset, fourierCoeff f (S ∪ T) ^ 2 := by
    refine Finset.sum_le_sum fun T _ => ?_
    have hpow : (1 - s) ^ T.card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith [sq_nonneg (fourierCoeff f (S ∪ T))]
  refine h1.trans_eq ?_
  refine Finset.sum_bij (fun T _ => S ∪ T)
    (fun _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩)
    (fun T₁ hT₁ T₂ hT₂ h => by
      have hd1 : Disjoint S T₁ := Finset.disjoint_left.mpr fun i hiS hiT =>
        (Finset.mem_compl.mp (Finset.mem_powerset.mp hT₁ hiT)) hiS
      have hd2 : Disjoint S T₂ := Finset.disjoint_left.mpr fun i hiS hiT =>
        (Finset.mem_compl.mp (Finset.mem_powerset.mp hT₂ hiT)) hiS
      rw [← Finset.union_sdiff_cancel_left hd1, h, Finset.union_sdiff_cancel_left hd2])
    (fun U hU => ⟨U \ S, Finset.mem_powerset.mpr (fun i hi =>
        Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2),
      Finset.union_sdiff_of_subset (Finset.mem_filter.mp hU).2⟩)
    (fun _ _ => rfl)

/-- **Expected low-degree mass after product restriction** (`lem:restrict-level-thinning`):
`E_{ρ ~ Res(s)}[mass_{≤ k}(p ↾ ρ)] = ∑_U P[Bin(|U|, s) ≤ k] * p̂(U)² ≤ E[p²]`. -/
theorem expect_lowDegreeMass_restrict {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (f : (ι → Bool) → ℝ) (k : ℕ) :
    (∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * lowDegreeMass k (restrictFun f ρ) =
      ∑ U : Finset ι,
        (∑ j ∈ (Finset.range (U.card + 1)).filter (fun j => j ≤ k),
          (U.card.choose j : ℝ) * s ^ j * (1 - s) ^ (U.card - j)) *
          fourierCoeff f U ^ 2) ∧
    (∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * lowDegreeMass k (restrictFun f ρ) ≤
      𝔼 x, f x ^ 2) := by
  have heq :
      ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * lowDegreeMass k (restrictFun f ρ) =
      ∑ U : Finset ι,
        (∑ j ∈ (Finset.range (U.card + 1)).filter (fun j => j ≤ k),
          (U.card.choose j : ℝ) * s ^ j * (1 - s) ^ (U.card - j)) *
          fourierCoeff f U ^ 2 := by
    simp_rw [mul_lowDegreeMass]
    rw [Finset.sum_comm]
    have hstep1 :
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ k),
          ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * fourierCoeff (restrictFun f ρ) S ^ 2 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ k),
          ∑ U ∈ Finset.univ.filter (fun U : Finset ι => S ⊆ U),
            s ^ S.card * (1 - s) ^ (U.card - S.card) * fourierCoeff f U ^ 2 := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [expect_fourierCoeff_restrict_sq, Finset.mul_sum]
      refine Finset.sum_bij (fun T _ => S ∪ T)
        (fun _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩)
        (fun T₁ hT₁ T₂ hT₂ h => by
          have hd1 : Disjoint S T₁ := Finset.disjoint_left.mpr fun i hiS hiT =>
            (Finset.mem_compl.mp (Finset.mem_powerset.mp hT₁ hiT)) hiS
          have hd2 : Disjoint S T₂ := Finset.disjoint_left.mpr fun i hiS hiT =>
            (Finset.mem_compl.mp (Finset.mem_powerset.mp hT₂ hiT)) hiS
          rw [← Finset.union_sdiff_cancel_left hd1, h, Finset.union_sdiff_cancel_left hd2])
        (fun U hU => ⟨U \ S, Finset.mem_powerset.mpr (fun i hi =>
            Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2),
          Finset.union_sdiff_of_subset (Finset.mem_filter.mp hU).2⟩)
        (fun T hT => by
          have hd : Disjoint S T := Finset.disjoint_left.mpr fun i hiS hiT =>
            (Finset.mem_compl.mp (Finset.mem_powerset.mp hT hiT)) hiS
          rw [Finset.card_union_of_disjoint hd, Nat.add_sub_cancel_left]
          ring)
    rw [hstep1]
    have hite : ∀ S : Finset ι,
        (if S.card ≤ k then
          ∑ U : Finset ι,
            if S ⊆ U then s ^ S.card * (1 - s) ^ (U.card - S.card) * fourierCoeff f U ^ 2 else 0
        else 0) =
        ∑ U : Finset ι,
          if S.card ≤ k then
            if S ⊆ U then s ^ S.card * (1 - s) ^ (U.card - S.card) * fourierCoeff f U ^ 2 else 0
          else 0 := fun S => by split_ifs <;> simp
    have hlhs :
        (∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ k),
          ∑ U ∈ Finset.univ.filter (fun U : Finset ι => S ⊆ U),
            s ^ S.card * (1 - s) ^ (U.card - S.card) * fourierCoeff f U ^ 2) =
        ∑ U : Finset ι, ∑ S : Finset ι,
          if S.card ≤ k then
            if S ⊆ U then s ^ S.card * (1 - s) ^ (U.card - S.card) * fourierCoeff f U ^ 2 else 0
          else 0 := by
      simp_rw [Finset.sum_filter, hite]
      rw [Finset.sum_comm]
    rw [hlhs]
    refine Finset.sum_congr rfl fun U _ => ?_
    have hU_sub :
        (∑ S : Finset ι,
          if S.card ≤ k then
            if S ⊆ U then s ^ S.card * (1 - s) ^ (U.card - S.card) * fourierCoeff f U ^ 2 else 0
          else 0) =
        (∑ S ∈ U.powerset.filter (fun S => S.card ≤ k),
          s ^ S.card * (1 - s) ^ (U.card - S.card)) * fourierCoeff f U ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_filter]
      rw [← Finset.sum_subset (Finset.subset_univ (U.powerset))]
      · refine Finset.sum_congr rfl fun S hS => ?_
        have h1 : S ⊆ U := Finset.mem_powerset.mp hS
        by_cases h2 : S.card ≤ k <;> simp [h1, h2]
      · intro S _ hnot
        have hnot' : ¬ (S ⊆ U) := fun h => hnot (Finset.mem_powerset.mpr h)
        simp [hnot']
    rw [hU_sub]
    congr 1
    have hbycard :
        ∑ S ∈ U.powerset.filter (fun S => S.card ≤ k),
          s ^ S.card * (1 - s) ^ (U.card - S.card) =
        ∑ j ∈ (Finset.range (U.card + 1)).filter (fun j => j ≤ k),
          ∑ S ∈ U.powersetCard j, s ^ j * (1 - s) ^ (U.card - j) := by
      have hbi : U.powerset.filter (fun S => S.card ≤ k) =
          ((Finset.range (U.card + 1)).filter (fun j => j ≤ k)).biUnion
            (fun j => U.powersetCard j) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_powersetCard]
        exact ⟨fun ⟨hSU, hSk⟩ => ⟨S.card, ⟨Nat.lt_succ_of_le (Finset.card_le_card hSU), hSk⟩,
          hSU, rfl⟩, fun ⟨_, ⟨_, hSk⟩, hSU, hcard⟩ => ⟨hSU, hcard ▸ hSk⟩⟩
      have hdisj : Set.PairwiseDisjoint
          ↑((Finset.range (U.card + 1)).filter (fun j => j ≤ k))
          (fun j => U.powersetCard j) := by
        intro j₁ _ j₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro S h1 h2
        exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
      rw [hbi, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S hS => ?_
      have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
      simp [hcard]
    rw [hbycard]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    ring
  refine ⟨heq, ?_⟩
  rw [heq, expect_sq_eq_sum_fourierCoeff_sq]
  refine Finset.sum_le_sum fun U _ => ?_
  have hprob_le :
      ∑ j ∈ (Finset.range (U.card + 1)).filter (fun j => j ≤ k),
        (U.card.choose j : ℝ) * s ^ j * (1 - s) ^ (U.card - j) ≤ 1 := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun j : ℕ => (U.card.choose j : ℝ) * s ^ j * (1 - s) ^ (U.card - j))
      (Finset.filter_subset (fun j : ℕ => j ≤ k) (Finset.range (U.card + 1)))
      (fun j _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))
        (pow_nonneg (sub_nonneg.mpr hs1) _))
    exact hsub.trans_eq (Cslib.sum_choose_mul_pow_eq_one U.card s)
  nlinarith [sq_nonneg (fourierCoeff f U)]

/-- Expected absolute parity correlation bound after product restriction:
`E_ρ[|⟨p ↾ ρ, χ_S⟩|] ≤ s^{|S| / 2} ‖p‖₂`. -/
theorem expect_abs_fourierCoeff_restrict_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (f : (ι → Bool) → ℝ) (S : Finset ι) :
    ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * |fourierCoeff (restrictFun f ρ) S| ≤
      s ^ ((S.card : ℝ) / 2) * Real.sqrt (𝔼 x, f x ^ 2) := by
  have hcs :
      (∑ ρ : ι → Option Bool,
        prodRestrictWeight s ρ * |fourierCoeff (restrictFun f ρ) S|) ^ 2 ≤
      (∑ ρ : ι → Option Bool, prodRestrictWeight s ρ) *
        (∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * fourierCoeff (restrictFun f ρ) S ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι → Option Bool))
      (fun ρ => Real.sqrt (prodRestrictWeight s ρ))
      (fun ρ => Real.sqrt (prodRestrictWeight s ρ) * |fourierCoeff (restrictFun f ρ) S|)
    have h1 : ∀ ρ : ι → Option Bool,
        Real.sqrt (prodRestrictWeight s ρ) *
          (Real.sqrt (prodRestrictWeight s ρ) * |fourierCoeff (restrictFun f ρ) S|) =
        prodRestrictWeight s ρ * |fourierCoeff (restrictFun f ρ) S| := fun ρ => by
      rw [← mul_assoc, Real.mul_self_sqrt (prodRestrictWeight_nonneg hs0 hs1 ρ)]
    have h2 : ∀ ρ : ι → Option Bool,
        Real.sqrt (prodRestrictWeight s ρ) ^ 2 = prodRestrictWeight s ρ := fun ρ =>
      Real.sq_sqrt (prodRestrictWeight_nonneg hs0 hs1 ρ)
    have h3 : ∀ ρ : ι → Option Bool,
        (Real.sqrt (prodRestrictWeight s ρ) * |fourierCoeff (restrictFun f ρ) S|) ^ 2 =
        prodRestrictWeight s ρ * fourierCoeff (restrictFun f ρ) S ^ 2 := fun ρ => by
      rw [mul_pow, Real.sq_sqrt (prodRestrictWeight_nonneg hs0 hs1 ρ), sq_abs]
    simpa only [h1, h2, h3] using h
  rw [sum_prodRestrictWeight, one_mul] at hcs
  have hsec := expect_fourierCoeff_restrict_sq_le hs0 hs1 f S
  have hparseval :
      ∑ U ∈ Finset.univ.filter (fun U : Finset ι => S ⊆ U), fourierCoeff f U ^ 2 ≤
        𝔼 x, f x ^ 2 := by
    rw [expect_sq_eq_sum_fourierCoeff_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hbound :
      (∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * |fourierCoeff (restrictFun f ρ) S|) ^ 2 ≤
        s ^ S.card * (𝔼 x, f x ^ 2) :=
    hcs.trans (hsec.trans (mul_le_mul_of_nonneg_left hparseval (pow_nonneg hs0 _)))
  have hexp_nonneg : 0 ≤ 𝔼 x, f x ^ 2 := by
    rw [expect_sq_eq_sum_fourierCoeff_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrhs_sq :
      (s ^ ((S.card : ℝ) / 2) * Real.sqrt (𝔼 x, f x ^ 2)) ^ 2 = s ^ S.card * (𝔼 x, f x ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hexp_nonneg, ← Real.rpow_natCast (s ^ ((S.card : ℝ) / 2)) 2,
      ← Real.rpow_mul hs0, ← Real.rpow_natCast s S.card]
    congr 2
    push_cast
    ring
  have hrhs_nonneg : 0 ≤ s ^ ((S.card : ℝ) / 2) * Real.sqrt (𝔼 x, f x ^ 2) :=
    mul_nonneg (Real.rpow_nonneg hs0 _) (Real.sqrt_nonneg _)
  have hsqrt := Real.le_sqrt_of_sq_le (hbound.trans_eq hrhs_sq.symm)
  rwa [Real.sqrt_sq hrhs_nonneg] at hsqrt

/-- **Random-index parity correlation bound** (`lem:rand-index-parity`): if `totalDegree p ≤ d₀`,
then for any `ρ`-measurable subset `U(ρ)`,
`E_ρ[|⟨p ↾ ρ, χ_{U(ρ)}⟩|] ≤ ‖p‖₂ * P_ρ[|U(ρ)| ≤ d₀]^{1/2}`. -/
theorem expect_abs_fourierCoeff_random_index_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {p : (ι → Bool) → ℝ} {d₀ : ℕ} (hp : totalDegree p ≤ d₀)
    (U : (ι → Option Bool) → Finset ι) :
    ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * |fourierCoeff (restrictFun p ρ) (U ρ)| ≤
      Real.sqrt (𝔼 x, p x ^ 2) *
        Real.sqrt (∑ ρ ∈ Finset.univ.filter (fun ρ => (U ρ).card ≤ d₀),
          prodRestrictWeight s ρ) := by
  have hdeg : ∀ ρ : ι → Option Bool, totalDegree (restrictFun p ρ) ≤ d₀ := by
    intro ρ
    rw [totalDegree_le_iff_fourierCoeff_eq_zero]
    intro S hS
    rw [fourierCoeff_restrictFun]
    split_ifs with hsub
    · refine Finset.sum_eq_zero fun V hV => ?_
      have hVS : V ∩ aliveSet ρ = S := (Finset.mem_filter.mp hV).2
      have hSV : S.card ≤ V.card := by
        rw [← hVS]
        exact Finset.card_le_card Finset.inter_subset_left
      have hVd : d₀ < V.card := lt_of_lt_of_le hS hSV
      have hp0 := (totalDegree_le_iff_fourierCoeff_eq_zero.mp hp) V hVd
      simp [hp0]
    · rfl
  have hpoint : ∀ ρ : ι → Option Bool,
      |fourierCoeff (restrictFun p ρ) (U ρ)| ≤
        (if (U ρ).card ≤ d₀ then 1 else 0) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ)) := by
    intro ρ
    by_cases hle : (U ρ).card ≤ d₀
    · simp only [hle, ↓reduceIte, one_mul]
      have hsq : fourierCoeff (restrictFun p ρ) (U ρ) ^ 2 ≤ lowDegreeMass d₀ (restrictFun p ρ) :=
        fourierCoeff_sq_le_lowDegreeMass hle (restrictFun p ρ)
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq_eq_abs] at this
    · have hgt : d₀ < (U ρ).card := Nat.lt_of_not_ge hle
      have h0 : fourierCoeff (restrictFun p ρ) (U ρ) = 0 :=
        (totalDegree_le_iff_fourierCoeff_eq_zero.mp (hdeg ρ)) (U ρ) hgt
      simp [hle, h0]
  have h1 :
      ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * |fourierCoeff (restrictFun p ρ) (U ρ)| ≤
      ∑ ρ : ι → Option Bool,
        (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) *
          (Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0)) := by
    refine Finset.sum_le_sum fun ρ _ => ?_
    have hw := prodRestrictWeight_nonneg hs0 hs1 ρ
    have hpt := hpoint ρ
    have hmul :
        (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) *
          (Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0)) =
        prodRestrictWeight s ρ *
          ((if (U ρ).card ≤ d₀ then 1 else 0) *
            Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) := by
      calc
        (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) *
            (Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0))
            = (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (prodRestrictWeight s ρ)) *
                ((if (U ρ).card ≤ d₀ then 1 else 0) *
                  Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) := by ring
        _ = prodRestrictWeight s ρ *
              ((if (U ρ).card ≤ d₀ then 1 else 0) *
                Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) := by rw [Real.mul_self_sqrt hw]
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hpt hw
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι → Option Bool))
    (fun ρ => Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ)))
    (fun ρ => Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0))
  have hsq1 :
      ∑ ρ : ι → Option Bool,
        (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) ^ 2 =
      ∑ ρ : ι → Option Bool, prodRestrictWeight s ρ * lowDegreeMass d₀ (restrictFun p ρ) := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hmass_nonneg : 0 ≤ lowDegreeMass d₀ (restrictFun p ρ) :=
      lowDegreeMass_nonneg d₀ (restrictFun p ρ)
    rw [mul_pow, Real.sq_sqrt (prodRestrictWeight_nonneg hs0 hs1 ρ), Real.sq_sqrt hmass_nonneg]
  have hsq2 :
      ∑ ρ : ι → Option Bool,
        (Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0)) ^ 2 =
      ∑ ρ ∈ Finset.univ.filter (fun ρ => (U ρ).card ≤ d₀), prodRestrictWeight s ρ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_pow, Real.sq_sqrt (prodRestrictWeight_nonneg hs0 hs1 ρ)]
    split_ifs <;> ring
  rw [hsq1, hsq2] at hcs
  have hmass_le := (expect_lowDegreeMass_restrict hs0 hs1 p d₀).2
  have hprob_nonneg :
      0 ≤ ∑ ρ ∈ Finset.univ.filter (fun ρ => (U ρ).card ≤ d₀), prodRestrictWeight s ρ :=
    Finset.sum_nonneg fun ρ _ => prodRestrictWeight_nonneg hs0 hs1 ρ
  have hexp_nonneg : 0 ≤ 𝔼 x, p x ^ 2 := by
    rw [expect_sq_eq_sum_fourierCoeff_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod_le :
      (∑ ρ : ι → Option Bool,
        (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) *
          (Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0))) ^ 2 ≤
      (𝔼 x, p x ^ 2) *
        (∑ ρ ∈ Finset.univ.filter (fun ρ => (U ρ).card ≤ d₀), prodRestrictWeight s ρ) :=
    hcs.trans (mul_le_mul_of_nonneg_right hmass_le hprob_nonneg)
  have hsqrt :
      ∑ ρ : ι → Option Bool,
        (Real.sqrt (prodRestrictWeight s ρ) * Real.sqrt (lowDegreeMass d₀ (restrictFun p ρ))) *
          (Real.sqrt (prodRestrictWeight s ρ) * (if (U ρ).card ≤ d₀ then 1 else 0)) ≤
      Real.sqrt (𝔼 x, p x ^ 2) *
        Real.sqrt (∑ ρ ∈ Finset.univ.filter (fun ρ => (U ρ).card ≤ d₀),
          prodRestrictWeight s ρ) := by
    rw [← Real.sqrt_mul hexp_nonneg]
    exact Real.le_sqrt_of_sq_le hprod_le
  exact h1.trans hsqrt

/-- **Binomial-Chernoff specialization of the random-index parity bound**: when
`U(ρ) = T ∩ Alive(ρ)` for a fixed parity support `T` of size `t_*` with `d₀ ≤ t_* * s`,
`E_ρ[|⟨p ↾ ρ, χ_{T ∩ Alive(ρ)}⟩|] ≤ ‖p‖₂ * exp (-(t_* * s - d₀)² / t_*)`. -/
theorem expect_abs_fourierCoeff_binomial_chernoff_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {p : (ι → Bool) → ℝ} {d₀ : ℕ} (hp : totalDegree p ≤ d₀) (T : Finset ι)
    (hd : (d₀ : ℝ) ≤ (T.card : ℝ) * s) :
    ∑ ρ : ι → Option Bool,
        prodRestrictWeight s ρ * |fourierCoeff (restrictFun p ρ) (T ∩ aliveSet ρ)| ≤
      Real.sqrt (𝔼 x, p x ^ 2) *
        Real.exp (-((T.card : ℝ) * s - (d₀ : ℝ)) ^ 2 / (T.card : ℝ)) := by
  have hbase := expect_abs_fourierCoeff_random_index_le hs0 hs1 hp (fun ρ => T ∩ aliveSet ρ)
  have hbin :
      ∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => (T ∩ aliveSet ρ).card ≤ d₀),
        prodRestrictWeight s ρ =
      ∑ j ∈ (Finset.range (T.card + 1)).filter (fun j => j ≤ d₀),
        (T.card.choose j : ℝ) * s ^ j * (1 - s) ^ (T.card - j) := by
    have hfactor : ∀ S : Finset ι, S ⊆ T →
        (∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => T ∩ aliveSet ρ = S),
          prodRestrictWeight s ρ) = s ^ S.card * (1 - s) ^ (T.card - S.card) := by
      intro S hST
      let g : ι → Option Bool → ℝ := fun i o =>
        if i ∈ S then (if o = none then s else 0)
        else if i ∈ T \ S then (match o with | none => 0 | some _ => (1 - s) / 2)
        else (match o with | none => s | some _ => (1 - s) / 2)
      have hpt : ∀ ρ : ι → Option Bool,
          (if T ∩ aliveSet ρ = S then prodRestrictWeight s ρ else 0) =
          ∏ i : ι, g i (ρ i) := by
        intro ρ
        split_ifs with hEq
        · simp only [prodRestrictWeight, g]
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hiS : i ∈ S
          · have halive : ρ i = none := by
              rw [← hEq] at hiS
              exact (Finset.mem_filter.mp (Finset.mem_inter.mp hiS).2).2
            simp [hiS, halive]
          · by_cases hiTS : i ∈ T \ S
            · have hdead : ρ i ≠ none := fun hnone => by
                have hmem : i ∈ T ∩ aliveSet ρ :=
                  Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hiTS).1,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
                rw [hEq] at hmem
                exact hiS hmem
              cases hρ : ρ i with
              | none => exact False.elim (hdead hρ)
              | some b => simp [hiS, hiTS]
            · simp [hiS, hiTS]
        · have hex : ∃ i : ι, (i ∈ S ∧ ρ i ≠ none) ∨ (i ∈ T \ S ∧ ρ i = none) := by
            by_contra hall
            push Not at hall
            apply hEq
            ext i
            simp only [Finset.mem_inter, aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hiT, hnone⟩
              by_contra hiS
              exact (hall i).2 (Finset.mem_sdiff.mpr ⟨hiT, hiS⟩) hnone
            · intro hiS
              exact ⟨hST hiS, (hall i).1 hiS⟩
          obtain ⟨i, hi⟩ := hex
          symm
          refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
          dsimp only [g]
          rcases hi with ⟨hiS, hne⟩ | ⟨hiTS, hnone⟩
          · simp [hiS, hne]
          · have hnotS : i ∉ S := (Finset.mem_sdiff.mp hiTS).2
            simp [hnotS, hiTS, hnone]
      rw [Finset.sum_filter, Finset.sum_congr rfl fun ρ _ => hpt ρ, ← Fintype.prod_sum g]
      have hprod :
          (∏ i : ι, ∑ o : Option Bool, g i o) =
          ∏ i : ι, if i ∈ S then s else if i ∈ T \ S then 1 - s else 1 := by
        refine Finset.prod_congr rfl fun i _ => ?_
        dsimp only [g]
        by_cases hiS : i ∈ S
        · simp [hiS]
        · by_cases hiTS : i ∈ T \ S
          · simp only [hiS, hiTS, ↓reduceIte, Fintype.sum_option, Fintype.sum_bool]; ring
          · simp only [hiS, hiTS, ↓reduceIte, Fintype.sum_option, Fintype.sum_bool]; ring
      rw [hprod]
      have hdisj : Disjoint S (T \ S) := Finset.disjoint_sdiff
      have h1 : (∏ i : ι, if i ∈ S then s else if i ∈ T \ S then 1 - s else 1) =
          ∏ i ∈ S ∪ (T \ S), if i ∈ S then s else if i ∈ T \ S then 1 - s else 1 := by
        symm
        refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
        have hn1 : i ∉ S := fun h => hi (Finset.mem_union_left _ h)
        have hn2 : i ∉ T \ S := fun h => hi (Finset.mem_union_right _ h)
        simp [hn1, hn2]
      rw [h1, Finset.prod_union hdisj]
      have hp1 : (∏ i ∈ S, if i ∈ S then s else if i ∈ T \ S then 1 - s else 1) = s ^ S.card := by
        have hc1 : (∏ i ∈ S, if i ∈ S then s else if i ∈ T \ S then 1 - s else 1) = ∏ _i ∈ S, s :=
          Finset.prod_congr rfl fun i hi => by simp [hi]
        rw [hc1, Finset.prod_const]
      have hp2 : (∏ i ∈ T \ S, if i ∈ S then s else if i ∈ T \ S then 1 - s else 1) =
          (1 - s) ^ (T.card - S.card) := by
        have hc2 : (∏ i ∈ T \ S, if i ∈ S then s else if i ∈ T \ S then 1 - s else 1) =
            ∏ _i ∈ T \ S, (1 - s) :=
          Finset.prod_congr rfl fun i hi => by simp [Finset.disjoint_right.mp hdisj hi, hi]
        rw [hc2, Finset.prod_const, Finset.card_sdiff_of_subset hST]
      rw [hp1, hp2]
    have hsplit :
        ∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => (T ∩ aliveSet ρ).card ≤ d₀),
          prodRestrictWeight s ρ =
        ∑ S ∈ T.powerset.filter (fun S => S.card ≤ d₀),
          ∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => T ∩ aliveSet ρ = S),
            prodRestrictWeight s ρ := by
      have hbi : Finset.univ.filter (fun ρ : ι → Option Bool => (T ∩ aliveSet ρ).card ≤ d₀) =
          (T.powerset.filter (fun S => S.card ≤ d₀)).biUnion
            (fun S => Finset.univ.filter (fun ρ : ι → Option Bool => T ∩ aliveSet ρ = S)) := by
        ext ρ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_powerset]
        exact ⟨fun h => ⟨T ∩ aliveSet ρ, ⟨Finset.inter_subset_left, h⟩, rfl⟩,
          fun ⟨S, ⟨_, hS⟩, hEq⟩ => hEq ▸ hS⟩
      have hdisj : Set.PairwiseDisjoint
          ↑(T.powerset.filter (fun S => S.card ≤ d₀))
          (fun S => Finset.univ.filter (fun ρ : ι → Option Bool => T ∩ aliveSet ρ = S)) := by
        intro S₁ _ S₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro ρ h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [hbi, Finset.sum_biUnion hdisj]
    rw [hsplit]
    have hsum_pow :
        ∑ S ∈ T.powerset.filter (fun S => S.card ≤ d₀),
          ∑ ρ ∈ Finset.univ.filter (fun ρ : ι → Option Bool => T ∩ aliveSet ρ = S),
            prodRestrictWeight s ρ =
        ∑ S ∈ T.powerset.filter (fun S => S.card ≤ d₀),
          s ^ S.card * (1 - s) ^ (T.card - S.card) :=
      Finset.sum_congr rfl fun S hS =>
        hfactor S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
    rw [hsum_pow]
    have hbycard :
        ∑ S ∈ T.powerset.filter (fun S => S.card ≤ d₀),
          s ^ S.card * (1 - s) ^ (T.card - S.card) =
        ∑ j ∈ (Finset.range (T.card + 1)).filter (fun j => j ≤ d₀),
          ∑ S ∈ T.powersetCard j, s ^ j * (1 - s) ^ (T.card - j) := by
      have hbi : T.powerset.filter (fun S => S.card ≤ d₀) =
          ((Finset.range (T.card + 1)).filter (fun j => j ≤ d₀)).biUnion
            (fun j => T.powersetCard j) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_powersetCard]
        exact ⟨fun ⟨hST, hSd⟩ => ⟨S.card, ⟨Nat.lt_succ_of_le (Finset.card_le_card hST), hSd⟩,
          hST, rfl⟩, fun ⟨_, ⟨_, hSd⟩, hST, hc⟩ => ⟨hST, hc ▸ hSd⟩⟩
      have hdisj : Set.PairwiseDisjoint
          ↑((Finset.range (T.card + 1)).filter (fun j => j ≤ d₀))
          (fun j => T.powersetCard j) := by
        intro j₁ _ j₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro S h1 h2
        exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
      rw [hbi, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S hS => ?_
      have hc : S.card = j := (Finset.mem_powersetCard.mp hS).2
      simp [hc]
    rw [hbycard]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    ring
  have hchernoff :
      ∑ j ∈ (Finset.range (T.card + 1)).filter (fun j => j ≤ d₀),
        (T.card.choose j : ℝ) * s ^ j * (1 - s) ^ (T.card - j) ≤
      Real.exp (-2 * ((T.card : ℝ) * s - (d₀ : ℝ)) ^ 2 / (T.card : ℝ)) := by
    have hsub :
        (Finset.range (T.card + 1)).filter (fun j => j ≤ d₀) ⊆
          (Finset.range (T.card + 1)).filter
            (fun j => ((T.card : ℝ) * s - (d₀ : ℝ)) ≤ (T.card : ℝ) * s - (j : ℝ)) := by
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      have hj' : (j : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast hj.2
      linarith
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun j : ℕ => (T.card.choose j : ℝ) * s ^ j * (1 - s) ^ (T.card - j)) hsub
      (fun j _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))
        (pow_nonneg (sub_nonneg.mpr hs1) _))
    exact h1.trans (Cslib.sum_filter_le_mul_sub_choose_mul_pow_le T.card hs0 hs1
      (by linarith : 0 ≤ (T.card : ℝ) * s - (d₀ : ℝ)))
  have hsqrt_exp :
      Real.sqrt (Real.exp (-2 * ((T.card : ℝ) * s - (d₀ : ℝ)) ^ 2 / (T.card : ℝ))) =
        Real.exp (-((T.card : ℝ) * s - (d₀ : ℝ)) ^ 2 / (T.card : ℝ)) := by
    rw [← Real.exp_half]
    congr 1
    ring
  rw [hbin] at hbase
  calc
    ∑ ρ : ι → Option Bool,
        prodRestrictWeight s ρ * |fourierCoeff (restrictFun p ρ) (T ∩ aliveSet ρ)|
        ≤ Real.sqrt (𝔼 x, p x ^ 2) *
            Real.sqrt (∑ j ∈ (Finset.range (T.card + 1)).filter (fun j => j ≤ d₀),
              (T.card.choose j : ℝ) * s ^ j * (1 - s) ^ (T.card - j)) := hbase
    _ ≤ Real.sqrt (𝔼 x, p x ^ 2) *
          Real.sqrt (Real.exp (-2 * ((T.card : ℝ) * s - (d₀ : ℝ)) ^ 2 / (T.card : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hchernoff) (Real.sqrt_nonneg _)
    _ = Real.sqrt (𝔼 x, p x ^ 2) *
          Real.exp (-((T.card : ℝ) * s - (d₀ : ℝ)) ^ 2 / (T.card : ℝ)) := by rw [hsqrt_exp]

end Restriction

private theorem productRestriction_sanity :
    ∑ ρ : Fin 2 → Option Bool, prodRestrictWeight (1 / 2) ρ = 1 :=
  sum_prodRestrictWeight (1 / 2)

end CslibFrontier.Foundations.BooleanAnalysis
