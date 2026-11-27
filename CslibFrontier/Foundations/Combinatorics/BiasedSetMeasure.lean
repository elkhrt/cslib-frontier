/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sups
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Biased Subset Distributions, Positive Correlation, and Janson's Inequality

This module develops `p`-biased random subset distributions on finite ground sets, satisfying set
systems, extraction of pairwise disjoint sets via random colorings, positive correlation of
decreasing events, and Janson's exponential lower-tail inequality.

Given a finite ground set `X` and bias `p ∈ [0, 1]`, the `p`-biased distribution assigns mass
`p ^ |R| * (1 - p) ^ (|X| - |R|)` to each subset `R ⊆ X`. A set system `F` is `(α, β)`-satisfying
when an `α`-biased random subset contains at least one member of `F` with probability strictly
greater than `1 - β`.

## Main definitions

* `CslibFrontier.biasedWeight`, `CslibFrontier.biasedEventProb`, `CslibFrontier.biasedExpect`:
  probability mass, event probability, and expectation under the `p`-biased subset distribution on a
  finite set.
* `CslibFrontier.satProb`, `CslibFrontier.IsSatisfying`: satisfaction probability and
  `(α, β)`-satisfying set systems.

## Main results

* `CslibFrontier.satProb_eq_setBernoulli_real`: equivalence of `satProb` with
  `ProbabilityTheory.setBernoulli`.
* `CslibFrontier.biasedExpect_union_sdiff`: two-stage union sampling identity for `W ∪ W'` with
  `W` `p`-biased on `X` and `W'` `q`-biased on `X \ W`.
* `CslibFrontier.exists_pairwise_disjoint_of_isSatisfying`: every `(1 / r, 1 / r)`-satisfying
  nonempty-set family contains `r` pairwise disjoint sets.
* `CslibFrontier.fkg_lower_events`: positive correlation of decreasing events under `p`-biased
  product measures.
* `CslibFrontier.janson_subset_bound`, `CslibFrontier.janson_inequality`: exponential upper bounds
  on the probability that a `p`-biased random subset avoids a family of subsets.
-/

public section

namespace CslibFrontier

open Finset
open scoped FinsetFamily

/-! ### Biased subset distributions and satisfying set systems -/

/-- Probability mass `p ^ |R| * (1 - p) ^ (|X| - |R|)` of `R ⊆ X` under the `p`-biased subset
distribution on `X`. -/
public def biasedWeight {α : Type*} (X : Finset α) (p : ℝ) (R : Finset α) : ℝ :=
  p ^ R.card * (1 - p) ^ (X.card - R.card)

/-- Probability of an event `E : Finset α → Prop` under a `p`-biased random subset of `X`. -/
public noncomputable def biasedEventProb {α : Type*}
    (X : Finset α) (p : ℝ) (E : Finset α → Prop) : ℝ := by
  classical
  exact ∑ R ∈ X.powerset with E R, biasedWeight X p R

/-- Expectation of `f : Finset α → ℝ` under a `p`-biased random subset of `X`. -/
public noncomputable def biasedExpect {α : Type*}
    (X : Finset α) (p : ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ R ∈ X.powerset, biasedWeight X p R * f R

private noncomputable def eventInd {α : Type*} (E : Finset α → Prop) (R : Finset α) : ℝ := by
  classical
  exact if E R then 1 else 0

private lemma eventInd_of_pos {α : Type*} {E : Finset α → Prop} {R : Finset α} (h : E R) :
    eventInd E R = 1 := by
  classical
  simp [eventInd, h]

private lemma eventInd_of_neg {α : Type*} {E : Finset α → Prop} {R : Finset α} (h : ¬ E R) :
    eventInd E R = 0 := by
  classical
  simp [eventInd, h]

private lemma eventInd_congr {α : Type*} {E₁ E₂ : Finset α → Prop} {R₁ R₂ : Finset α}
    (h : E₁ R₁ ↔ E₂ R₂) : eventInd E₁ R₁ = eventInd E₂ R₂ := by
  classical
  by_cases h1 : E₁ R₁
  · simp [eventInd, h1, h.1 h1]
  · simp [eventInd, h1, mt h.2 h1]

private lemma eventInd_mono {α : Type*} {E₁ E₂ : Finset α → Prop} {R₁ R₂ : Finset α}
    (h : E₁ R₁ → E₂ R₂) : eventInd E₁ R₁ ≤ eventInd E₂ R₂ := by
  classical
  by_cases h1 : E₁ R₁
  · simp [eventInd, h1, h h1]
  · by_cases h2 : E₂ R₂ <;> simp [eventInd, h1, h2]

/-- Probability that a `p`-biased random subset of `⋃_{S ∈ F} S` contains at least one member of
`F`. -/
public noncomputable def satProb {α : Type*} [DecidableEq α]
    (p : ℝ) (F : Finset (Finset α)) : ℝ :=
  biasedEventProb (F.biUnion id) p fun R ↦ ∃ S ∈ F, S ⊆ R

/-- A set system `F` is `(α, β)`-satisfying when an `α`-biased random subset contains some member
of `F` with probability strictly greater than `1 - β`. -/
public def IsSatisfying {α : Type*} [DecidableEq α]
    (α_prob β_err : ℝ) (F : Finset (Finset α)) : Prop :=
  1 - β_err < satProb α_prob F

/-- Characterization of `IsSatisfying`. -/
public theorem isSatisfying_iff {α : Type*} [DecidableEq α]
    {α_prob β_err : ℝ} {F : Finset (Finset α)} :
    IsSatisfying α_prob β_err F ↔ 1 - β_err < satProb α_prob F :=
  Iff.rfl

/-- Explicit polynomial formula for `biasedWeight X p R`. -/
public theorem biasedWeight_eq_mul_pow {α : Type*} (X : Finset α) (p : ℝ) (R : Finset α) :
    biasedWeight X p R = p ^ R.card * (1 - p) ^ (X.card - R.card) := by
  rfl

/-- Explicit finite-sum formula for `biasedExpect X p f`. -/
public theorem biasedExpect_eq_sum {α : Type*}
    (X : Finset α) (p : ℝ) (f : Finset α → ℝ) :
    biasedExpect X p f = ∑ R ∈ X.powerset, biasedWeight X p R * f R := by
  rfl

/-- Explicit filtered-sum formula for `biasedEventProb X p E` when `DecidablePred E` is given. -/
public theorem biasedEventProb_eq_sum_filter {α : Type*}
    (X : Finset α) (p : ℝ) (E : Finset α → Prop) [DecidablePred E] :
    biasedEventProb X p E = ∑ R ∈ X.powerset with E R, biasedWeight X p R := by
  unfold biasedEventProb
  congr 1
  ext R
  simp

/-- The empty set system has satisfaction probability `0`. -/
@[simp]
public theorem satProb_empty {α : Type*} [DecidableEq α] (p : ℝ) :
    satProb p (∅ : Finset (Finset α)) = 0 := by
  simp [satProb, biasedEventProb]

/-- The singleton empty-set system `{∅}` has satisfaction probability `1`. -/
@[simp]
public theorem satProb_singleton_empty {α : Type*} [DecidableEq α] (p : ℝ) :
    satProb p ({∅} : Finset (Finset α)) = 1 := by
  simp [satProb, biasedEventProb, biasedWeight]

/-- Unfolding `satProb` as an event probability over `F.biUnion id`. -/
public theorem satProb_eq_biasedEventProb_biUnion {α : Type*} [DecidableEq α]
    (p : ℝ) (F : Finset (Finset α)) :
    satProb p F = biasedEventProb (F.biUnion id) p (fun R ↦ ∃ S ∈ F, S ⊆ R) := by
  rfl

/-- `biasedWeight` is nonnegative when `0 ≤ p ≤ 1`. -/
public theorem biasedWeight_nonneg {α : Type*} {X : Finset α} {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (R : Finset α) :
    0 ≤ biasedWeight X p R := by
  have h1 : 0 ≤ 1 - p := sub_nonneg.2 hp₁
  exact mul_nonneg (pow_nonneg hp₀ _) (pow_nonneg h1 _)

/-- `biasedWeight` is strictly positive when `0 < p < 1`. -/
public theorem biasedWeight_pos {α : Type*} {X : Finset α} {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) (R : Finset α) :
    0 < biasedWeight X p R := by
  have h1 : 0 < 1 - p := sub_pos.2 hp₁
  exact mul_pos (pow_pos hp₀ _) (pow_pos h1 _)

/-- `biasedWeight` at `insert a X` (`a ∉ X`) for `R ⊆ X` not containing `a`. -/
public theorem biasedWeight_insert_notMem {α : Type*} [DecidableEq α]
    {X : Finset α} {a : α} (ha : a ∉ X) (p : ℝ) {R : Finset α} (hR : R ⊆ X) :
    biasedWeight (insert a X) p R = (1 - p) * biasedWeight X p R := by
  have hcard : R.card ≤ X.card := card_le_card hR
  have hsub : (insert a X).card - R.card = (X.card - R.card) + 1 := by
    rw [card_insert_of_notMem ha]
    omega
  unfold biasedWeight
  rw [hsub, pow_succ]
  ring

/-- `biasedWeight` at `insert a X` (`a ∉ X`) for `insert a R` (`R ⊆ X`). -/
public theorem biasedWeight_insert_mem {α : Type*} [DecidableEq α]
    {X : Finset α} {a : α} (ha : a ∉ X) (p : ℝ) {R : Finset α} (hR : R ⊆ X) :
    biasedWeight (insert a X) p (insert a R) = p * biasedWeight X p R := by
  have haR : a ∉ R := fun h ↦ ha (hR h)
  have hsub : (insert a X).card - (insert a R).card = X.card - R.card := by
    rw [card_insert_of_notMem ha, card_insert_of_notMem haR]
    omega
  unfold biasedWeight
  rw [hsub, card_insert_of_notMem haR, pow_succ]
  ring

/-- Sum over `(insert a X).powerset` split according to membership of `a ∉ X`. -/
public theorem sum_powerset_insert {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {X : Finset α} {a : α} (ha : a ∉ X) (f : Finset α → β) :
    ∑ R ∈ (insert a X).powerset, f R =
      ∑ R ∈ X.powerset, f R + ∑ R ∈ X.powerset, f (insert a R) := by
  rw [powerset_insert, sum_union, sum_image]
  · intro R₁ hR₁ R₂ hR₂ heq
    have ha₁ : a ∉ R₁ := fun h ↦ ha (mem_powerset.1 hR₁ h)
    have ha₂ : a ∉ R₂ := fun h ↦ ha (mem_powerset.1 hR₂ h)
    rw [← erase_insert ha₁, ← erase_insert ha₂, heq]
  · rw [disjoint_left]
    intro R hR₁ hR₂
    obtain ⟨T, -, rfl⟩ := mem_image.1 hR₂
    exact ha (mem_powerset.1 hR₁ (mem_insert_self a T))

/-- Decomposition of `biasedExpect (insert a X) p f` for `a ∉ X`. -/
public theorem biasedExpect_insert {α : Type*} [DecidableEq α]
    {X : Finset α} {a : α} (ha : a ∉ X) (p : ℝ) (f : Finset α → ℝ) :
    biasedExpect (insert a X) p f =
      (1 - p) * biasedExpect X p f + p * biasedExpect X p (fun R ↦ f (insert a R)) := by
  simp only [biasedExpect, sum_powerset_insert ha, mul_sum]
  congr 1
  · refine sum_congr rfl fun R hR ↦ ?_
    rw [biasedWeight_insert_notMem ha p (mem_powerset.1 hR)]
    ring
  · refine sum_congr rfl fun R hR ↦ ?_
    rw [biasedWeight_insert_mem ha p (mem_powerset.1 hR)]
    ring

/-- Total mass of `biasedWeight X p` over `X.powerset` equals `1`. -/
@[simp]
public theorem sum_biasedWeight_powerset {α : Type*} (X : Finset α) (p : ℝ) :
    ∑ R ∈ X.powerset, biasedWeight X p R = 1 := by
  classical
  have h : biasedExpect X p (fun _ ↦ 1) = 1 := by
    induction X using Finset.induction with
    | empty => simp [biasedExpect, biasedWeight]
    | insert a X ha ih =>
      rw [biasedExpect_insert ha, ih]
      ring
  simpa [biasedExpect] using h

private lemma biasedEventProb_eq_biasedExpect_ind {α : Type*}
    (X : Finset α) (p : ℝ) (E : Finset α → Prop) :
    biasedEventProb X p E = biasedExpect X p (eventInd E) := by
  classical
  simp [biasedEventProb, biasedExpect, eventInd, sum_filter]

/-- Complement rule `Pr[E] + Pr[¬ E] = 1` under `biasedEventProb X p`. -/
public theorem biasedEventProb_add_compl {α : Type*}
    (X : Finset α) (p : ℝ) (E : Finset α → Prop) :
    biasedEventProb X p E + biasedEventProb X p (fun R ↦ ¬ E R) = 1 := by
  rw [biasedEventProb_eq_biasedExpect_ind, biasedEventProb_eq_biasedExpect_ind]
  simp only [biasedExpect, ← sum_add_distrib]
  refine (sum_congr rfl fun R _ ↦ ?_).trans (sum_biasedWeight_powerset X p)
  by_cases hE : E R
  · rw [eventInd_of_pos hE, eventInd_of_neg (not_not.2 hE)]
    ring
  · rw [eventInd_of_neg hE, eventInd_of_pos hE]
    ring

/-- Monotonicity of `biasedEventProb` in the event `E` when `0 ≤ p ≤ 1`. -/
public theorem biasedEventProb_mono {α : Type*} {X : Finset α} {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {E₁ E₂ : Finset α → Prop}
    (hE : ∀ R, R ⊆ X → E₁ R → E₂ R) :
    biasedEventProb X p E₁ ≤ biasedEventProb X p E₂ := by
  classical
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun R _ _ ↦ biasedWeight_nonneg hp₀ hp₁ R)
  intro R hR
  simp only [mem_filter, mem_powerset] at hR ⊢
  exact ⟨hR.1, hE R hR.1 hR.2⟩

/-- Markov's inequality for nonnegative observables under `biasedExpect X p`. -/
public theorem biasedEventProb_ge_le_div {α : Type*} {X : Finset α} {p t : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ht : 0 < t) {f : Finset α → ℝ}
    (hf : ∀ R, R ⊆ X → 0 ≤ f R) :
    biasedEventProb X p (fun R ↦ t ≤ f R) ≤ biasedExpect X p f / t := by
  classical
  rw [le_div_iff₀ ht, biasedEventProb, sum_mul, biasedExpect]
  calc ∑ R ∈ X.powerset with t ≤ f R, biasedWeight X p R * t
      ≤ ∑ R ∈ X.powerset with t ≤ f R, biasedWeight X p R * f R := by
        refine sum_le_sum fun R hR ↦ ?_
        exact mul_le_mul_of_nonneg_left (mem_filter.1 hR).2 (biasedWeight_nonneg hp₀ hp₁ R)
    _ ≤ ∑ R ∈ X.powerset, biasedWeight X p R * f R := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun R hRX _ ↦ ?_
        exact mul_nonneg (biasedWeight_nonneg hp₀ hp₁ R) (hf R (mem_powerset.1 hRX))

/-- Exact probability `p ^ |S|` of containing a subset `S ⊆ X`. -/
public theorem biasedEventProb_subset_eq {α : Type*}
    {X S : Finset α} (hSX : S ⊆ X) (p : ℝ) :
    biasedEventProb X p (fun R ↦ S ⊆ R) = p ^ S.card := by
  classical
  induction X using Finset.induction generalizing S with
  | empty =>
    rw [subset_empty.1 hSX]
    simp [biasedEventProb, biasedWeight]
  | insert a X ha ih =>
    rw [biasedEventProb_eq_biasedExpect_ind, biasedExpect_insert ha]
    by_cases haS : a ∈ S
    · have hS' : S.erase a ⊆ X := by
        intro x hx
        rcases mem_insert.1 (hSX (mem_of_mem_erase hx)) with rfl | hxX
        · exact absurd rfl (ne_of_mem_erase hx)
        · exact hxX
      have hleft : biasedExpect X p (eventInd fun R ↦ S ⊆ R) = 0 := by
        refine sum_eq_zero fun R hR ↦ ?_
        have hnot : ¬ S ⊆ R := fun hsub ↦ ha (mem_powerset.1 hR (hsub haS))
        rw [eventInd_of_neg hnot, mul_zero]
      have hright : biasedExpect X p (fun R ↦ eventInd (fun T ↦ S ⊆ T) (insert a R)) =
          biasedEventProb X p (fun R ↦ S.erase a ⊆ R) := by
        rw [biasedEventProb_eq_biasedExpect_ind]
        refine sum_congr rfl fun R _ ↦ congrArg (biasedWeight X p R * ·) ?_
        have hiff : S ⊆ insert a R ↔ S.erase a ⊆ R := by
          constructor
          · intro hsub x hx
            rcases mem_insert.1 (hsub (mem_of_mem_erase hx)) with rfl | hxR
            · exact absurd rfl (ne_of_mem_erase hx)
            · exact hxR
          · intro hsub x hx
            by_cases hxa : x = a
            · exact hxa ▸ mem_insert_self a R
            · exact mem_insert_of_mem (hsub (mem_erase.2 ⟨hxa, hx⟩))
        exact eventInd_congr hiff
      rw [hleft, hright, ih hS', mul_zero, zero_add, ← pow_succ', card_erase_add_one haS]
    · have hSX' : S ⊆ X := by
        intro x hx
        rcases mem_insert.1 (hSX hx) with rfl | hxX
        · exact absurd hx haS
        · exact hxX
      have hright : biasedExpect X p (fun R ↦ eventInd (fun T ↦ S ⊆ T) (insert a R)) =
          biasedEventProb X p (fun R ↦ S ⊆ R) := by
        rw [biasedEventProb_eq_biasedExpect_ind]
        refine sum_congr rfl fun R _ ↦ congrArg (biasedWeight X p R * ·) ?_
        have hiff : S ⊆ insert a R ↔ S ⊆ R := by
          refine ⟨fun hsub x hx ↦ ?_, fun hsub ↦ hsub.trans (subset_insert a R)⟩
          rcases mem_insert.1 (hsub hx) with rfl | hxR
          · exact absurd hx haS
          · exact hxR
        exact eventInd_congr hiff
      rw [← biasedEventProb_eq_biasedExpect_ind, hright, ih hSX']
      ring

/-- Ground-set invariance: for any finite ground set `X` containing every member of `F`, the
probability that a `p`-biased random subset of `X` contains a member of `F` equals `satProb p F`. -/
public theorem biasedEventProb_exists_subset_eq_satProb {α : Type*} [DecidableEq α]
    {X : Finset α} {F : Finset (Finset α)} (hFX : ∀ S ∈ F, S ⊆ X) (p : ℝ) :
    biasedEventProb X p (fun R ↦ ∃ S ∈ F, S ⊆ R) = satProb p F := by
  let U := F.biUnion id
  have hsub : U ⊆ X := biUnion_subset.2 hFX
  have hX : X = U ∪ (X \ U) := (union_sdiff_of_subset hsub).symm
  have hdisj : Disjoint U (X \ U) := disjoint_sdiff_self_right
  rw [hX]
  change biasedEventProb (U ∪ (X \ U)) p (fun R ↦ ∃ S ∈ F, S ⊆ R) =
    biasedEventProb U p (fun R ↦ ∃ S ∈ F, S ⊆ R)
  generalize X \ U = D at hdisj ⊢
  induction D using Finset.induction with
  | empty => simp
  | insert a D ha ih =>
    have haU : a ∉ U := disjoint_right.1 hdisj (mem_insert_self a D)
    have hdisj' : Disjoint U D := hdisj.mono_right (subset_insert a D)
    have haUD : a ∉ U ∪ D := notMem_union.2 ⟨haU, ha⟩
    rw [union_insert, biasedEventProb_eq_biasedExpect_ind, biasedExpect_insert haUD]
    have heq : biasedExpect (U ∪ D) p
        (fun R ↦ eventInd (fun T ↦ ∃ S ∈ F, S ⊆ T) (insert a R)) =
          biasedEventProb (U ∪ D) p (fun R ↦ ∃ S ∈ F, S ⊆ R) := by
      rw [biasedEventProb_eq_biasedExpect_ind]
      refine sum_congr rfl fun R _ ↦ congrArg (biasedWeight (U ∪ D) p R * ·) ?_
      have hiff : (∃ S ∈ F, S ⊆ insert a R) ↔ ∃ S ∈ F, S ⊆ R := by
        refine exists_congr fun S ↦ and_congr_right fun hSF ↦ ?_
        have haS : a ∉ S := fun h ↦ haU (subset_biUnion_of_mem id hSF h)
        refine ⟨fun hsub x hx ↦ ?_, fun hsub ↦ hsub.trans (subset_insert a R)⟩
        rcases mem_insert.1 (hsub hx) with rfl | hxR
        · exact absurd hx haS
        · exact hxR
      exact eventInd_congr hiff
    rw [← biasedEventProb_eq_biasedExpect_ind, heq, ih hdisj']
    ring

/-- Equivalence of `satProb` with `ProbabilityTheory.setBernoulli` on countable ground types. -/
public theorem satProb_eq_setBernoulli_real {α : Type*} [DecidableEq α] [Countable α]
    {X : Finset α} {F : Finset (Finset α)} (hFX : ∀ S ∈ F, S ⊆ X) (p : unitInterval) :
    satProb (p : ℝ) F =
      (ProbabilityTheory.setBernoulli (X : Set α) p).real
        {R : Set α | ∃ S ∈ F, (S : Set α) ⊆ R} := by
  classical
  rw [← biasedEventProb_exists_subset_eq_satProb hFX]
  let A : Finset (Finset α) := X.powerset.filter fun R ↦ ∃ S ∈ F, S ⊆ R
  have hset : {s : Set α | s ∈ {R : Set α | ∃ S ∈ F, (S : Set α) ⊆ R} ∧ s ⊆ (X : Set α)} =
      ⋃ R ∈ A, ({(R : Set α)} : Set (Set α)) := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff, A, mem_filter,
      mem_powerset]
    constructor
    · rintro ⟨hS, hRX⟩
      have hfin : R.Finite := X.finite_toSet.subset hRX
      refine ⟨hfin.toFinset, ⟨?_, ?_⟩, (Set.Finite.coe_toFinset hfin).symm⟩
      · intro x hx
        exact mem_coe.1 (hRX ((Set.Finite.mem_toFinset hfin).1 hx))
      · obtain ⟨S, hSF, hSR⟩ := hS
        exact ⟨S, hSF, fun x hx ↦ (Set.Finite.mem_toFinset hfin).2 (hSR hx)⟩
    · rintro ⟨T, ⟨hTX, S, hSF, hST⟩, rfl⟩
      exact ⟨⟨S, hSF, coe_subset.2 hST⟩, coe_subset.2 hTX⟩
  rw [MeasureTheory.measureReal_def, ProbabilityTheory.setBernoulli_apply_eq_apply_subsets,
    ← MeasureTheory.measureReal_def, hset,
    MeasureTheory.measureReal_biUnion_finset
      (fun R₁ _ R₂ _ hne ↦ Set.disjoint_singleton.2 fun h ↦ hne (coe_injective h))
      (by simp)]
  simp only [biasedEventProb, A]
  refine sum_congr rfl fun R hR ↦ ?_
  have hRX : R ⊆ X := mem_powerset.1 (mem_filter.1 hR).1
  have hRX' : (R : Set α) ⊆ (X : Set α) := coe_subset.2 hRX
  rw [ProbabilityTheory.setBernoulli_real_singleton p hRX' X.finite_toSet]
  simp only [biasedWeight, Set.ncard_coe_finset, ← coe_sdiff, card_sdiff_of_subset hRX]

/-- Two-stage sampling identity: sampling `W` `p`-biased from `X` and `W'` `q`-biased from `X \ W`
distributes `W ∪ W'` as a `(p + (1 - p) * q)`-biased random subset of `X`. -/
public theorem biasedExpect_union_sdiff {α : Type*} [DecidableEq α]
    (X : Finset α) (p q : ℝ) (f : Finset α → ℝ) :
    biasedExpect X p (fun W ↦ biasedExpect (X \ W) q (fun W' ↦ f (W ∪ W'))) =
      biasedExpect X (p + (1 - p) * q) f := by
  induction X using Finset.induction generalizing f with
  | empty =>
    simp [biasedExpect, biasedWeight]
  | insert a X ha ih =>
    rw [biasedExpect_insert ha, biasedExpect_insert ha]
    have hnotMem : biasedExpect X p
        (fun W ↦ biasedExpect (insert a X \ W) q (fun W' ↦ f (W ∪ W'))) =
        (1 - q) * biasedExpect X (p + (1 - p) * q) f +
          q * biasedExpect X (p + (1 - p) * q) (fun R ↦ f (insert a R)) := by
      let g₁ : Finset α → ℝ := fun W ↦ biasedExpect (X \ W) q (fun W' ↦ f (W ∪ W'))
      let g₂ : Finset α → ℝ := fun W ↦ biasedExpect (X \ W) q (fun W' ↦ f (insert a (W ∪ W')))
      have hcongr : ∀ W ∈ X.powerset,
          biasedExpect (insert a X \ W) q (fun W' ↦ f (W ∪ W')) =
            (1 - q) * g₁ W + q * g₂ W := by
        intro W hW
        have haW : a ∉ W := fun h ↦ ha (mem_powerset.1 hW h)
        have hsdiff : insert a X \ W = insert a (X \ W) := insert_sdiff_of_notMem X haW
        have haXW : a ∉ X \ W := fun h ↦ ha (sdiff_subset h)
        rw [hsdiff, biasedExpect_insert haXW]
        simp only [union_insert, g₁, g₂]
      calc biasedExpect X p (fun W ↦ biasedExpect (insert a X \ W) q (fun W' ↦ f (W ∪ W')))
          = ∑ W ∈ X.powerset, biasedWeight X p W * ((1 - q) * g₁ W + q * g₂ W) := by
            refine sum_congr rfl fun W hW ↦ congrArg (biasedWeight X p W * ·) (hcongr W hW)
        _ = (1 - q) * biasedExpect X p g₁ + q * biasedExpect X p g₂ := by
            change ∑ W ∈ X.powerset, biasedWeight X p W * ((1 - q) * g₁ W + q * g₂ W) =
              (1 - q) * (∑ W ∈ X.powerset, biasedWeight X p W * g₁ W) +
                q * (∑ W ∈ X.powerset, biasedWeight X p W * g₂ W)
            simp only [mul_add, sum_add_distrib, mul_sum]
            congr 1 <;> refine sum_congr rfl fun W _ ↦ by ring
        _ = (1 - q) * biasedExpect X (p + (1 - p) * q) f +
              q * biasedExpect X (p + (1 - p) * q) (fun R ↦ f (insert a R)) := by
            simp only [g₁, g₂, ih f, ih (fun R ↦ f (insert a R))]
    have hMem : biasedExpect X p
        (fun W ↦ biasedExpect (insert a X \ insert a W) q (fun W' ↦ f (insert a W ∪ W'))) =
        biasedExpect X (p + (1 - p) * q) (fun R ↦ f (insert a R)) := by
      have hcongr : ∀ W ∈ X.powerset,
          biasedExpect (insert a X \ insert a W) q (fun W' ↦ f (insert a W ∪ W')) =
            biasedExpect (X \ W) q (fun W' ↦ f (insert a (W ∪ W'))) := by
        intro W hW
        have haW : a ∉ W := fun h ↦ ha (mem_powerset.1 hW h)
        have hsdiff : insert a X \ insert a W = X \ W := by
          ext x
          simp only [mem_sdiff, mem_insert]
          constructor
          · rintro ⟨rfl | hxX, hxW⟩
            · exact absurd (Or.inl rfl) hxW
            · exact ⟨hxX, fun h ↦ hxW (Or.inr h)⟩
          · rintro ⟨hxX, hxW⟩
            exact ⟨Or.inr hxX, fun h ↦ h.elim (fun hxa ↦ ha (hxa ▸ hxX)) hxW⟩
        rw [hsdiff]
        simp only [insert_union]
      calc biasedExpect X p
              (fun W ↦ biasedExpect (insert a X \ insert a W) q (fun W' ↦ f (insert a W ∪ W')))
          = biasedExpect X p
              (fun W ↦ biasedExpect (X \ W) q (fun W' ↦ f (insert a (W ∪ W')))) := by
            refine sum_congr rfl fun W hW ↦ congrArg (biasedWeight X p W * ·) (hcongr W hW)
        _ = biasedExpect X (p + (1 - p) * q) (fun R ↦ f (insert a R)) :=
            ih (fun R ↦ f (insert a R))
    rw [hnotMem, hMem]
    ring

/-- Event form of the two-stage union sampling law. -/
public theorem biasedEventProb_union_sdiff {α : Type*} [DecidableEq α]
    (X : Finset α) (p q : ℝ) (E : Finset α → Prop) :
    biasedExpect X p (fun W ↦ biasedEventProb (X \ W) q (fun W' ↦ E (W ∪ W'))) =
      biasedEventProb X (p + (1 - p) * q) E := by
  simp_rw [biasedEventProb_eq_biasedExpect_ind]
  exact biasedExpect_union_sdiff X p q (eventInd E)

/-- Monotonicity of `satProb p F` with respect to `p ∈ [0, 1]`. -/
public theorem satProb_mono_prob {α : Type*} [DecidableEq α]
    {p q : ℝ} (hp₀ : 0 ≤ p) (hpq : p ≤ q) (hq₁ : q ≤ 1) (F : Finset (Finset α)) :
    satProb p F ≤ satProb q F := by
  by_cases hp1 : p = 1
  · have hq : q = 1 := le_antisymm hq₁ (hp1 ▸ hpq)
    rw [hp1, hq]
  have hp1lt : p < 1 := lt_of_le_of_ne (hpq.trans hq₁) hp1
  let r : ℝ := (q - p) / (1 - p)
  have hr₀ : 0 ≤ r := div_nonneg (sub_nonneg.2 hpq) (sub_nonneg.2 hp1lt.le)
  have hr₁ : r ≤ 1 := (div_le_one (sub_pos.2 hp1lt)).2 (by linarith)
  have hqr : q = p + (1 - p) * r := by
    simp only [r]
    field_simp [sub_ne_zero.2 (ne_of_lt hp1lt).symm]
    ring
  let U := F.biUnion id
  let E : Finset α → Prop := fun R ↦ ∃ S ∈ F, S ⊆ R
  calc satProb p F
      = biasedExpect U p (eventInd E) := biasedEventProb_eq_biasedExpect_ind U p E
    _ ≤ biasedExpect U p (fun W ↦ biasedExpect (U \ W) r (fun W' ↦ eventInd E (W ∪ W'))) := by
        refine sum_le_sum fun W _ ↦ mul_le_mul_of_nonneg_left ?_
          (biasedWeight_nonneg hp₀ hp1lt.le W)
        calc eventInd E W
            = ∑ W' ∈ (U \ W).powerset, biasedWeight (U \ W) r W' * eventInd E W := by
              rw [← sum_mul, sum_biasedWeight_powerset, one_mul]
          _ ≤ biasedExpect (U \ W) r (fun W' ↦ eventInd E (W ∪ W')) := by
              refine sum_le_sum fun W' _ ↦ mul_le_mul_of_nonneg_left ?_
                (biasedWeight_nonneg hr₀ hr₁ W')
              exact eventInd_mono fun ⟨S, hSF, hSW⟩ ↦ ⟨S, hSF, hSW.trans subset_union_left⟩
    _ = biasedExpect U (p + (1 - p) * r) (eventInd E) :=
        biasedExpect_union_sdiff U p r (eventInd E)
    _ = satProb q F := by
        rw [← hqr, ← biasedEventProb_eq_biasedExpect_ind]
        rfl

/-- Monotonicity of `IsSatisfying` when increasing the bias `α` in `[0, 1]` and error `β`. -/
public theorem IsSatisfying.mono {α : Type*} [DecidableEq α]
    {α₁ α₂ β₁ β₂ : ℝ} {F : Finset (Finset α)}
    (h : IsSatisfying α₁ β₁ F) (hα₀ : 0 ≤ α₁) (hα : α₁ ≤ α₂) (hα₁ : α₂ ≤ 1) (hβ : β₁ ≤ β₂) :
    IsSatisfying α₂ β₂ F := by
  have hsat := satProb_mono_prob hα₀ hα hα₁ F
  unfold IsSatisfying at h ⊢
  linarith

/-- Any nonempty set system has positive satisfaction probability when `0 < p ≤ 1`. -/
public theorem satProb_pos_of_nonempty {α : Type*} [DecidableEq α]
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) {F : Finset (Finset α)} (hF : F.Nonempty) :
    0 < satProb p F := by
  obtain ⟨S₀, hS₀⟩ := hF
  have h1 : biasedEventProb (F.biUnion id) p (fun R ↦ S₀ ⊆ R) = p ^ S₀.card :=
    biasedEventProb_subset_eq (subset_biUnion_of_mem id hS₀) p
  have h2 : biasedEventProb (F.biUnion id) p (fun R ↦ S₀ ⊆ R) ≤ satProb p F :=
    biasedEventProb_mono hp₀.le hp₁ fun _ _ hS₀R ↦ ⟨S₀, hS₀, hS₀R⟩
  exact lt_of_lt_of_le (h1 ▸ pow_pos hp₀ S₀.card) h2

/-! ### Pairwise disjoint sets from satisfying set systems -/

private def colorClass {α : Type*} (U : Finset α) {r : ℕ}
    (c : ↥U → Fin r) (i : Fin r) : Finset α :=
  (U.attach.filter fun x ↦ c x = i).map ⟨Subtype.val, Subtype.val_injective⟩

private lemma mem_colorClass_iff {α : Type*} {U : Finset α} {r : ℕ}
    {c : ↥U → Fin r} {i : Fin r} {a : α} :
    a ∈ colorClass U c i ↔ ∃ ha : a ∈ U, c ⟨a, ha⟩ = i := by
  simp only [colorClass, mem_map, mem_filter, mem_attach, true_and, Function.Embedding.coeFn_mk,
    Subtype.exists]
  exact ⟨fun ⟨b, hbU, hci, hba⟩ ↦ ⟨hba ▸ hbU, hba ▸ hci⟩, fun ⟨haU, hci⟩ ↦ ⟨a, haU, hci, rfl⟩⟩

/-- Every `(1 / r, 1 / r)`-satisfying set system (`r ≥ 1`) not containing `∅` contains `r`
pairwise disjoint sets. -/
public theorem exists_pairwise_disjoint_of_isSatisfying {α : Type*} [DecidableEq α]
    {r : ℕ} (hr : 1 ≤ r) {F : Finset (Finset α)}
    (hsat : IsSatisfying (1 / (r : ℝ)) (1 / (r : ℝ)) F) (hempty : ∅ ∉ F) :
    ∃ D ⊆ F, D.card = r ∧ (D : Set (Finset α)).Pairwise Disjoint := by
  classical
  have hsat' := isSatisfying_iff.1 hsat
  rcases eq_or_lt_of_le hr with rfl | hr2
  · simp only [Nat.cast_one, div_one, sub_self] at hsat'
    have hne : F.Nonempty := by
      by_contra hnot
      rw [not_nonempty_iff_eq_empty] at hnot
      subst hnot
      simp at hsat'
    obtain ⟨S₀, hS₀⟩ := hne
    exact ⟨{S₀}, singleton_subset_iff.2 hS₀, card_singleton S₀, by simp⟩
  let U := F.biUnion id
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.2 (by omega)
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hfiber_card : ∀ (i : Fin r) (R : Finset α), R ⊆ U →
      ((univ : Finset (↥U → Fin r)).filter fun c ↦ colorClass U c i = R).card =
        (r - 1) ^ (U.card - R.card) := by
    intro i R hRU
    let V : Finset ↥U := U.attach.filter fun x : ↥U ↦ (x : α) ∉ R
    have hVcard : V.card = U.card - R.card := by
      have hpart :
          (U.attach.filter fun x : ↥U ↦ (x : α) ∈ R).card + V.card = U.attach.card :=
        card_filter_add_card_filter_not (fun x : ↥U ↦ (x : α) ∈ R)
      have hinR : (U.attach.filter fun x : ↥U ↦ (x : α) ∈ R).card = R.card := by
        rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩]
        congr 1
        ext a
        simp only [mem_map, mem_filter, mem_attach, true_and, Function.Embedding.coeFn_mk,
          Subtype.exists]
        exact ⟨fun ⟨b, _, hbR, hba⟩ ↦ hba ▸ hbR, fun haR ↦ ⟨a, hRU haR, haR, rfl⟩⟩
      rw [card_attach, hinR] at hpart
      omega
    let BadColor := {j : Fin r // j ≠ i}
    have hBadCard : Fintype.card BadColor = r - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    let toFun : (↥V → BadColor) → (↥U → Fin r) := fun g x ↦
      if hx : x ∈ V then (g ⟨x, hx⟩).1 else i
    have hmem : ∀ g : ↥V → BadColor, colorClass U (toFun g) i = R := by
      intro g
      ext a
      rw [mem_colorClass_iff]
      constructor
      · rintro ⟨haU, hcol⟩
        by_contra haR
        have hxV : (⟨a, haU⟩ : ↥U) ∈ V := mem_filter.2 ⟨mem_attach _ _, haR⟩
        have hcol' : (g ⟨⟨a, haU⟩, hxV⟩).1 = i := by simpa [toFun, hxV] using hcol
        exact (g ⟨⟨a, haU⟩, hxV⟩).2 hcol'
      · intro haR
        have haU : a ∈ U := hRU haR
        have hxV : (⟨a, haU⟩ : ↥U) ∉ V := by simp [V, haR]
        refine ⟨haU, ?_⟩
        simp [toFun, hxV]
    have hinj : Function.Injective toFun := by
      intro g₁ g₂ heq
      funext ⟨x, hxV⟩
      apply Subtype.ext
      have h := congrFun heq x
      simpa [toFun, hxV] using h
    have hsurj : ((univ : Finset (↥U → Fin r)).filter fun c ↦ colorClass U c i = R) =
        (univ : Finset (↥V → BadColor)).image toFun := by
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_image]
      refine ⟨fun hc ↦ ?_, ?_⟩
      · have hne_i : ∀ x : ↥V, c x.1 ≠ i := by
          rintro ⟨x, hxV⟩ hci
          have hxR : (x : α) ∈ colorClass U c i := mem_colorClass_iff.2 ⟨x.2, hci⟩
          rw [hc] at hxR
          exact (mem_filter.1 hxV).2 hxR
        refine ⟨fun x ↦ ⟨c x.1, hne_i x⟩, ?_⟩
        funext x
        by_cases hxV : x ∈ V
        · simp [toFun, hxV]
        · have hxR : (x : α) ∈ R := by
            simp only [V, mem_filter, mem_attach, true_and, not_not] at hxV
            exact hxV
          rw [← hc, mem_colorClass_iff] at hxR
          obtain ⟨hxU', hc_eq⟩ := hxR
          have hx_sub : (⟨(x : α), hxU'⟩ : ↥U) = x := Subtype.ext rfl
          rw [hx_sub] at hc_eq
          simp [toFun, hxV, hc_eq]
      · rintro ⟨g, rfl⟩
        exact hmem g
    rw [hsurj, card_image_of_injective _ hinj, card_univ, Fintype.card_fun, hBadCard,
      Fintype.card_coe, hVcard]
  have hbad_count : ∀ i : Fin r,
      (((univ : Finset (↥U → Fin r)).filter fun c ↦ ¬ ∃ S ∈ F, S ⊆ colorClass U c i).card : ℝ) <
        (1 / (r : ℝ)) * (r : ℝ) ^ U.card := by
    intro i
    have hpart :
        ((univ : Finset (↥U → Fin r)).filter fun c ↦ ¬ ∃ S ∈ F, S ⊆ colorClass U c i).card =
          ∑ R ∈ U.powerset with ¬ ∃ S ∈ F, S ⊆ R,
            ((univ : Finset (↥U → Fin r)).filter fun c ↦ colorClass U c i = R).card := by
      rw [← card_biUnion]
      · congr 1
        ext c
        simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_powerset]
        refine ⟨fun hc ↦ ⟨colorClass U c i, ⟨?_, hc⟩, rfl⟩, ?_⟩
        · intro a ha
          exact (mem_colorClass_iff.1 ha).1
        · rintro ⟨R, ⟨-, hR⟩, rfl⟩
          exact hR
      · intro R₁ _ R₂ _ hne
        exact disjoint_left.2 fun c hc₁ hc₂ ↦
          hne ((mem_filter.1 hc₁).2.symm.trans (mem_filter.1 hc₂).2)
    rw [hpart, Nat.cast_sum]
    have hcompl := biasedEventProb_add_compl U (1 / (r : ℝ)) (fun R ↦ ∃ S ∈ F, S ⊆ R)
    have hlt : biasedEventProb U (1 / (r : ℝ)) (fun R ↦ ¬ ∃ S ∈ F, S ⊆ R) < 1 / (r : ℝ) := by
      rw [satProb_eq_biasedEventProb_biUnion] at hsat'
      linarith
    have hident : (∑ R ∈ U.powerset with ¬ ∃ S ∈ F, S ⊆ R,
        (((univ : Finset (↥U → Fin r)).filter fun c ↦ colorClass U c i = R).card : ℝ)) =
        biasedEventProb U (1 / (r : ℝ)) (fun R ↦ ¬ ∃ S ∈ F, S ⊆ R) * (r : ℝ) ^ U.card := by
      rw [biasedEventProb_eq_sum_filter, sum_mul]
      refine sum_congr rfl fun R hR ↦ ?_
      have hRU : R ⊆ U := mem_powerset.1 (mem_filter.1 hR).1
      have hcard : R.card ≤ U.card := card_le_card hRU
      rw [hfiber_card i R hRU, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      have hrsplit : (r : ℝ) ^ U.card = (r : ℝ) ^ R.card * (r : ℝ) ^ (U.card - R.card) := by
        rw [← pow_add, Nat.add_sub_of_le hcard]
      rw [hrsplit, biasedWeight_eq_mul_pow]
      have h1 : (1 / (r : ℝ)) ^ R.card * (r : ℝ) ^ R.card = 1 := by
        rw [← mul_pow, one_div_mul_cancel hrpos.ne', one_pow]
      have h2 : (1 - 1 / (r : ℝ)) ^ (U.card - R.card) * (r : ℝ) ^ (U.card - R.card) =
          ((r : ℝ) - 1) ^ (U.card - R.card) := by
        rw [← mul_pow]
        congr 1
        field_simp [hrpos.ne']
      calc ((r : ℝ) - 1) ^ (U.card - R.card)
          = 1 * ((r : ℝ) - 1) ^ (U.card - R.card) := (one_mul _).symm
        _ = ((1 / (r : ℝ)) ^ R.card * (r : ℝ) ^ R.card) *
              ((1 - 1 / (r : ℝ)) ^ (U.card - R.card) * (r : ℝ) ^ (U.card - R.card)) := by
            rw [h1, h2]
        _ = (1 / (r : ℝ)) ^ R.card * (1 - 1 / (r : ℝ)) ^ (U.card - R.card) *
              ((r : ℝ) ^ R.card * (r : ℝ) ^ (U.card - R.card)) := by ring
    rw [hident]
    exact mul_lt_mul_of_pos_right hlt (pow_pos hrpos _)
  have hgood_exists : ∃ c : ↥U → Fin r, ∀ i : Fin r, ∃ S ∈ F, S ⊆ colorClass U c i := by
    by_contra hnot
    have hall : ∀ c : ↥U → Fin r, ∃ i : Fin r, ¬ ∃ S ∈ F, S ⊆ colorClass U c i := by
      simpa only [not_exists, not_forall] using hnot
    have hcov : (univ : Finset (↥U → Fin r)) ⊆
        univ.biUnion fun i : Fin r ↦
          (univ : Finset (↥U → Fin r)).filter fun c ↦ ¬ ∃ S ∈ F, S ⊆ colorClass U c i := by
      intro c _
      obtain ⟨i, hi⟩ := hall c
      exact mem_biUnion.2 ⟨i, mem_univ i, mem_filter.2 ⟨mem_univ c, hi⟩⟩
    have hle : ((univ : Finset (↥U → Fin r)).card : ℝ) ≤
        ∑ i : Fin r,
          (((univ : Finset (↥U →
            Fin r)).filter fun c ↦ ¬ ∃ S ∈ F, S ⊆ colorClass U c i).card : ℝ) := by
      exact_mod_cast (card_le_card hcov).trans card_biUnion_le
    have hlt_sum : (∑ i : Fin r,
        (((univ : Finset (↥U →
          Fin r)).filter fun c ↦ ¬ ∃ S ∈ F, S ⊆ colorClass U c i).card : ℝ)) <
        ∑ _i : Fin r, (1 / (r : ℝ)) * (r : ℝ) ^ U.card :=
      sum_lt_sum_of_nonempty univ_nonempty fun i _ ↦ hbad_count i
    have htot : ((univ : Finset (↥U → Fin r)).card : ℝ) = (r : ℝ) ^ U.card := by
      rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt_sum
    have hr_cancel : (r : ℝ) * (1 / (r : ℝ) * (r : ℝ) ^ U.card) = (r : ℝ) ^ U.card := by
      field_simp [hrpos.ne']
    linarith
  obtain ⟨c, hc⟩ := hgood_exists
  choose S hSF hScol using hc
  have hdisj : Pairwise fun i j ↦ Disjoint (S i) (S j) := by
    intro i j hij
    refine disjoint_left.2 fun a ha₁ ha₂ ↦ ?_
    obtain ⟨_, hci⟩ := mem_colorClass_iff.1 (hScol i ha₁)
    obtain ⟨_, hcj⟩ := mem_colorClass_iff.1 (hScol j ha₂)
    exact hij (hci.symm.trans hcj)
  have hinj : Function.Injective S := by
    intro i j hij
    by_contra hne
    have hd : Disjoint (S i) (S j) := hdisj hne
    rw [hij] at hd
    have hSj : S j = ∅ := disjoint_self.1 hd
    exact hempty (hSj ▸ hSF j)
  refine ⟨univ.image S, image_subset_iff.2 fun i _ ↦ hSF i, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro A hA B hB hAB
    obtain ⟨i, -, rfl⟩ := mem_image.1 hA
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB
    exact hdisj fun hij ↦ hAB (congrArg S hij)

/-! ### Positive correlation and Janson's exponential tail inequality -/

private lemma biasedWeight_mul_eq_inter_mul_union {α : Type*} [DecidableEq α]
    {X R₁ R₂ : Finset α} (h₁ : R₁ ⊆ X) (h₂ : R₂ ⊆ X) (p : ℝ) :
    biasedWeight X p R₁ * biasedWeight X p R₂ =
      biasedWeight X p (R₁ ∩ R₂) * biasedWeight X p (R₁ ∪ R₂) := by
  have hcard : R₁.card + R₂.card = (R₁ ∩ R₂).card + (R₁ ∪ R₂).card :=
    (card_inter_add_card_union R₁ R₂).symm
  have hc1 : R₁.card ≤ X.card := card_le_card h₁
  have hc2 : R₂.card ≤ X.card := card_le_card h₂
  have hci : (R₁ ∩ R₂).card ≤ X.card := card_le_card (inter_subset_left.trans h₁)
  have hcu : (R₁ ∪ R₂).card ≤ X.card := card_le_card (union_subset h₁ h₂)
  have hsub : (X.card - R₁.card) + (X.card - R₂.card) =
      (X.card - (R₁ ∩ R₂).card) + (X.card - (R₁ ∪ R₂).card) := by omega
  simp only [biasedWeight_eq_mul_pow]
  calc (p ^ R₁.card * (1 - p) ^ (X.card - R₁.card)) *
          (p ^ R₂.card * (1 - p) ^ (X.card - R₂.card))
      = (p ^ R₁.card * p ^ R₂.card) *
          ((1 - p) ^ (X.card - R₁.card) * (1 - p) ^ (X.card - R₂.card)) := by ring
    _ = p ^ (R₁.card + R₂.card) *
          (1 - p) ^ ((X.card - R₁.card) + (X.card - R₂.card)) := by
        rw [← pow_add, ← pow_add]
    _ = p ^ ((R₁ ∩ R₂).card + (R₁ ∪ R₂).card) *
          (1 - p) ^ ((X.card - (R₁ ∩ R₂).card) + (X.card - (R₁ ∪ R₂).card)) := by
        rw [hcard, hsub]
    _ = (p ^ (R₁ ∩ R₂).card * (1 - p) ^ (X.card - (R₁ ∩ R₂).card)) *
          (p ^ (R₁ ∪ R₂).card * (1 - p) ^ (X.card - (R₁ ∪ R₂).card)) := by
        rw [pow_add, pow_add]
        ring

/-- Positive correlation (FKG inequality) for two decreasing events on `X.powerset` under
`biasedEventProb X p`. -/
public theorem fkg_lower_events {α : Type*}
    (X : Finset α) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {E₁ E₂ : Finset α → Prop}
    (hE₁ : ∀ ⦃R₁ R₂⦄, R₁ ⊆ R₂ → R₂ ⊆ X → E₁ R₂ → E₁ R₁)
    (hE₂ : ∀ ⦃R₁ R₂⦄, R₁ ⊆ R₂ → R₂ ⊆ X → E₂ R₂ → E₂ R₁) :
    biasedEventProb X p E₁ * biasedEventProb X p E₂ ≤
      biasedEventProb X p (fun R ↦ E₁ R ∧ E₂ R) := by
  classical
  rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
  let 𝒜 := X.powerset.filter E₁
  let ℬ := X.powerset.filter E₂
  let w : Finset α → ℝ := biasedWeight X p
  have hw : 0 ≤ w := fun R ↦ biasedWeight_nonneg hp₀ hp₁ R
  have h4 := X.four_functions_theorem hw hw hw hw
    (fun s hs t ht ↦ (biasedWeight_mul_eq_inter_mul_union hs ht p).le)
    (filter_subset E₁ X.powerset) (filter_subset E₂ X.powerset)
  have hinfs : 𝒜 ⊼ ℬ ⊆ X.powerset.filter (fun R ↦ E₁ R ∧ E₂ R) := by
    intro R hR
    obtain ⟨s, hs, t, ht, rfl⟩ := mem_infs.1 hR
    obtain ⟨hsX, hsE⟩ := mem_filter.1 hs
    obtain ⟨htX, htE⟩ := mem_filter.1 ht
    have hsX' : s ⊆ X := mem_powerset.1 hsX
    have htX' : t ⊆ X := mem_powerset.1 htX
    exact mem_filter.2 ⟨mem_powerset.2 (inter_subset_left.trans hsX'),
      hE₁ inter_subset_left hsX' hsE, hE₂ inter_subset_right htX' htE⟩
  have hsups : 𝒜 ⊻ ℬ ⊆ X.powerset := by
    intro R hR
    obtain ⟨s, hs, t, ht, rfl⟩ := mem_sups.1 hR
    exact mem_powerset.2
      (union_subset (mem_powerset.1 (mem_filter.1 hs).1) (mem_powerset.1 (mem_filter.1 ht).1))
  have hle₁ : ∑ R ∈ 𝒜 ⊼ ℬ, w R ≤ ∑ R ∈ X.powerset with E₁ R ∧ E₂ R, w R :=
    sum_le_sum_of_subset_of_nonneg hinfs fun R _ _ ↦ hw R
  have hle₂ : ∑ R ∈ 𝒜 ⊻ ℬ, w R ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg hsups fun R _ _ ↦ hw R).trans_eq
      (sum_biasedWeight_powerset X p)
  calc (∑ R ∈ 𝒜, w R) * ∑ R ∈ ℬ, w R
      ≤ (∑ R ∈ 𝒜 ⊼ ℬ, w R) * ∑ R ∈ 𝒜 ⊻ ℬ, w R := h4
    _ ≤ (∑ R ∈ X.powerset with E₁ R ∧ E₂ R, w R) * 1 :=
        mul_le_mul hle₁ hle₂ (sum_nonneg fun R _ ↦ hw R)
          (sum_nonneg fun R _ ↦ hw R)
    _ = ∑ R ∈ X.powerset with E₁ R ∧ E₂ R, w R := mul_one _

private lemma biasedEventProb_subset_and_eq {α : Type*} [DecidableEq α]
    {X A : Finset α} (hAX : A ⊆ X) (p : ℝ) (P : Finset α → Prop) :
    biasedEventProb X p (fun R ↦ A ⊆ R ∧ P R) =
      p ^ A.card * biasedEventProb (X \ A) p (fun R' ↦ P (A ∪ R')) := by
  classical
  rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter, mul_sum]
  symm
  refine sum_nbij (fun R' ↦ A ∪ R') ?_ ?_ ?_ ?_
  · intro R' hR'
    obtain ⟨hR'pow, hPR'⟩ := mem_filter.1 hR'
    have hR'sub : R' ⊆ X \ A := mem_powerset.1 hR'pow
    exact mem_filter.2 ⟨mem_powerset.2 (union_subset hAX (hR'sub.trans sdiff_subset)),
      subset_union_left, hPR'⟩
  · intro R₁ hR₁ R₂ hR₂ heq
    have hd₁ : Disjoint A R₁ :=
      disjoint_of_subset_right (mem_powerset.1 (mem_filter.1 hR₁).1) disjoint_sdiff_self_right
    have hd₂ : Disjoint A R₂ :=
      disjoint_of_subset_right (mem_powerset.1 (mem_filter.1 hR₂).1) disjoint_sdiff_self_right
    have h := congrArg (· \ A) heq
    simpa [union_sdiff_cancel_left hd₁, union_sdiff_cancel_left hd₂] using h
  · intro R hR
    obtain ⟨hRpow, hAR, hPR⟩ := mem_filter.1 hR
    have hRX : R ⊆ X := mem_powerset.1 hRpow
    have hR'sub : R \ A ⊆ X \ A := sdiff_subset_sdiff hRX Subset.rfl
    have hun : A ∪ (R \ A) = R := union_sdiff_of_subset hAR
    exact ⟨R \ A, mem_filter.2 ⟨mem_powerset.2 hR'sub, hun.symm ▸ hPR⟩, hun⟩
  · intro R' hR'
    have hR'sub : R' ⊆ X \ A := mem_powerset.1 (mem_filter.1 hR').1
    have hd : Disjoint A R' := disjoint_of_subset_right hR'sub disjoint_sdiff_self_right
    have hcard_u : (A ∪ R').card = A.card + R'.card := card_union_of_disjoint hd
    have hcard_sdiff : (X \ A).card = X.card - A.card := card_sdiff_of_subset hAX
    have hAX_le : A.card ≤ X.card := card_le_card hAX
    have hR'_le : R'.card ≤ (X \ A).card := card_le_card hR'sub
    have hsub : X.card - (A ∪ R').card = (X \ A).card - R'.card := by omega
    rw [biasedWeight_eq_mul_pow, biasedWeight_eq_mul_pow, hsub, hcard_u, pow_add]
    ring

/-- Independence from unused ground elements: if `Q` is invariant under removing `A ⊆ X`, then
`biasedEventProb (X \ A) p Q = biasedEventProb X p Q`. -/
public theorem biasedEventProb_sdiff_eq_of_indep {α : Type*} [DecidableEq α]
    {X A : Finset α} (hAX : A ⊆ X) (p : ℝ) {Q : Finset α → Prop}
    (hQ : ∀ R, R ⊆ X → (Q R ↔ Q (R \ A))) :
    biasedEventProb (X \ A) p Q = biasedEventProb X p Q := by
  classical
  rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
  have h1 : (∑ R₂ ∈ (X \ A).powerset with Q R₂, biasedWeight (X \ A) p R₂) =
      (∑ R₁ ∈ A.powerset, biasedWeight A p R₁) *
        (∑ R₂ ∈ (X \ A).powerset with Q R₂, biasedWeight (X \ A) p R₂) := by
    rw [sum_biasedWeight_powerset, one_mul]
  rw [h1, sum_mul_sum, ← sum_product']
  refine sum_nbij (fun q : Finset α × Finset α ↦ q.1 ∪ q.2) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hR₁, hR₂⟩ := mem_product.1 hq
    have hR₁A : q.1 ⊆ A := mem_powerset.1 hR₁
    obtain ⟨hR₂pow, hQR₂⟩ := mem_filter.1 hR₂
    have hR₂X : q.2 ⊆ X \ A := mem_powerset.1 hR₂pow
    have hunX : q.1 ∪ q.2 ⊆ X := union_subset (hR₁A.trans hAX) (hR₂X.trans sdiff_subset)
    have hd : Disjoint q.2 A := disjoint_of_subset_left hR₂X sdiff_disjoint
    have hsdiff : (q.1 ∪ q.2) \ A = q.2 := by
      rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 hR₁A, empty_union,
        hd.sdiff_eq_left]
    exact mem_filter.2 ⟨mem_powerset.2 hunX, (hQ _ hunX).2 (hsdiff.symm ▸ hQR₂)⟩
  · intro q₁ hq₁ q₂ hq₂ heq
    dsimp only at heq
    have h₁A : q₁.1 ⊆ A := mem_powerset.1 (mem_product.1 hq₁).1
    have h₂A : q₂.1 ⊆ A := mem_powerset.1 (mem_product.1 hq₂).1
    have h₁B : q₁.2 ⊆ X \ A := mem_powerset.1 (mem_filter.1 (mem_product.1 hq₁).2).1
    have h₂B : q₂.2 ⊆ X \ A := mem_powerset.1 (mem_filter.1 (mem_product.1 hq₂).2).1
    have hd₁ : Disjoint q₁.2 A := disjoint_of_subset_left h₁B sdiff_disjoint
    have hd₂ : Disjoint q₂.2 A := disjoint_of_subset_left h₂B sdiff_disjoint
    have hsnd : q₁.2 = q₂.2 := by
      ext x
      have h : x ∈ q₁.1 ∪ q₁.2 ↔ x ∈ q₂.1 ∪ q₂.2 := by rw [heq]
      simp only [mem_union] at h
      exact ⟨fun hx ↦ h.1 (Or.inr hx) |>.resolve_left fun hx1 ↦
        disjoint_left.1 hd₁ hx (h₂A hx1),
        fun hx ↦ h.2 (Or.inr hx) |>.resolve_left fun hx1 ↦
        disjoint_left.1 hd₂ hx (h₁A hx1)⟩
    have hfst : q₁.1 = q₂.1 := by
      ext x
      have h : x ∈ q₁.1 ∪ q₁.2 ↔ x ∈ q₂.1 ∪ q₂.2 := by rw [heq]
      simp only [mem_union] at h
      exact ⟨fun hx ↦ h.1 (Or.inl hx) |>.resolve_right fun hx2 ↦
        disjoint_left.1 hd₂ hx2 (h₁A hx),
        fun hx ↦ h.2 (Or.inl hx) |>.resolve_right fun hx2 ↦
        disjoint_left.1 hd₁ hx2 (h₂A hx)⟩
    exact Prod.ext hfst hsnd
  · intro R hR
    obtain ⟨hRpow, hQR⟩ := mem_filter.1 hR
    have hRX : R ⊆ X := mem_powerset.1 hRpow
    refine ⟨(R ∩ A, R \ A), mem_product.2 ⟨mem_powerset.2 inter_subset_right,
      mem_filter.2 ⟨mem_powerset.2 (sdiff_subset_sdiff hRX Subset.rfl), (hQ R hRX).1 hQR⟩⟩, ?_⟩
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  · intro q hq
    have h₁A : q.1 ⊆ A := mem_powerset.1 (mem_product.1 hq).1
    have h₂B : q.2 ⊆ X \ A := mem_powerset.1 (mem_filter.1 (mem_product.1 hq).2).1
    have hd : Disjoint q.1 q.2 :=
      disjoint_left.2 fun x hx₁ hx₂ ↦ (mem_sdiff.1 (h₂B hx₂)).2 (h₁A hx₁)
    have hcu : (q.1 ∪ q.2).card = q.1.card + q.2.card := card_union_of_disjoint hd
    have hcA : A.card ≤ X.card := card_le_card hAX
    have hc1 : q.1.card ≤ A.card := card_le_card h₁A
    have hc2 : q.2.card ≤ (X \ A).card := card_le_card h₂B
    have hcs : (X \ A).card = X.card - A.card := card_sdiff_of_subset hAX
    have hsub : (A.card - q.1.card) + ((X \ A).card - q.2.card) = X.card - (q.1 ∪ q.2).card := by
      omega
    simp only [biasedWeight_eq_mul_pow, hcu]
    calc (p ^ q.1.card * (1 - p) ^ (A.card - q.1.card)) *
            (p ^ q.2.card * (1 - p) ^ ((X \ A).card - q.2.card))
        = (p ^ q.1.card * p ^ q.2.card) *
            ((1 - p) ^ (A.card - q.1.card) * (1 - p) ^ ((X \ A).card - q.2.card)) := by ring
      _ = p ^ (q.1.card + q.2.card) * (1 - p) ^ (X.card - (q.1.card + q.2.card)) := by
          rw [← pow_add, ← pow_add, hsub, hcu]

private lemma biasedEventProb_forall_not_ge_one_sub_sum {α ι : Type*}
    (Y : Finset α) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (J : Finset ι) (C : ι → Finset α → Prop) :
    1 - ∑ j ∈ J, biasedEventProb Y p (C j) ≤
      biasedEventProb Y p (fun R ↦ ∀ j ∈ J, ¬ C j R) := by
  classical
  induction J using Finset.induction with
  | empty =>
    rw [sum_empty, sub_zero, biasedEventProb_eq_sum_filter]
    have hfilt : (Y.powerset.filter fun R ↦ ∀ j ∈ (∅ : Finset ι), ¬ C j R) = Y.powerset := by
      ext R
      simp
    rw [hfilt, sum_biasedWeight_powerset]
  | insert j₀ K hj₀ ih =>
    rw [sum_insert hj₀]
    let EK : Finset α → Prop := fun R ↦ ∀ j ∈ K, ¬ C j R
    have hsplit : biasedEventProb Y p EK =
        biasedEventProb Y p (fun R ↦ C j₀ R ∧ EK R) +
          biasedEventProb Y p (fun R ↦ ¬ C j₀ R ∧ EK R) := by
      rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter,
        biasedEventProb_eq_sum_filter]
      have h1 : (Y.powerset.filter fun R ↦ C j₀ R ∧ EK R) =
          (Y.powerset.filter EK).filter (C j₀) := by
        ext R; simp only [mem_filter]; tauto
      have h2 : (Y.powerset.filter fun R ↦ ¬ C j₀ R ∧ EK R) =
          (Y.powerset.filter EK).filter (fun R ↦ ¬ C j₀ R) := by
        ext R; simp only [mem_filter]; tauto
      rw [h1, h2, sum_filter_add_sum_filter_not]
    have hle_j₀ : biasedEventProb Y p (fun R ↦ C j₀ R ∧ EK R) ≤ biasedEventProb Y p (C j₀) :=
      biasedEventProb_mono hp₀ hp₁ fun _ _ h ↦ h.1
    have heq_ins : biasedEventProb Y p (fun R ↦ ∀ j ∈ insert j₀ K, ¬ C j R) =
        biasedEventProb Y p (fun R ↦ ¬ C j₀ R ∧ EK R) := by
      rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
      congr 1
      ext R
      simp [EK]
    linarith

/-- Exponential upper bound on `Pr[∀ i ∈ I, ¬ S_i ⊆ R]` for any finite index subset `I` and family
`S : ι → Finset α` of subsets of `X` under `biasedEventProb X p`. -/
public theorem janson_subset_bound {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (X : Finset α) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (S : ι → Finset α) (hSX : ∀ i, S i ⊆ X) (I : Finset ι) :
    biasedEventProb X p (fun R ↦ ∀ i ∈ I, ¬ S i ⊆ R) ≤
      Real.exp (- ((∑ i ∈ I, p ^ (S i).card) -
        (1 / 2 : ℝ) * ∑ i ∈ I, ∑ j ∈ I with i ≠ j ∧ ¬ Disjoint (S i) (S j),
          p ^ (S i ∪ S j).card)) := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [sum_empty, mul_zero, sub_zero, neg_zero, Real.exp_zero]
    have h1 := biasedEventProb_add_compl X p (fun R ↦ ∀ i ∈ (∅ : Finset ι), ¬ S i ⊆ R)
    have h2 : 0 ≤ biasedEventProb X p (fun R ↦ ¬ ∀ i ∈ (∅ : Finset ι), ¬ S i ⊆ R) := by
      rw [biasedEventProb_eq_sum_filter]
      exact sum_nonneg fun R _ ↦ biasedWeight_nonneg hp₀ hp₁ R
    linarith
  | insert i₀ J hi₀ ih =>
    let EJ : Finset α → Prop := fun R ↦ ∀ j ∈ J, ¬ S j ⊆ R
    let J₁ := J.filter fun j ↦ ¬ Disjoint (S i₀) (S j)
    let J₂ := J.filter fun j ↦ Disjoint (S i₀) (S j)
    let δ : ℝ := p ^ (S i₀).card - ∑ j ∈ J₁, p ^ (S i₀ ∪ S j).card
    have hEJ_nonneg : 0 ≤ biasedEventProb X p EJ := by
      rw [biasedEventProb_eq_sum_filter]
      exact sum_nonneg fun R _ ↦ biasedWeight_nonneg hp₀ hp₁ R
    have hstep_lb : δ * biasedEventProb X p EJ ≤
        biasedEventProb X p (fun R ↦ S i₀ ⊆ R ∧ EJ R) := by
      by_cases hδ : δ ≤ 0
      · have hle0 : δ * biasedEventProb X p EJ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hδ hEJ_nonneg
        have hge0 : 0 ≤ biasedEventProb X p (fun R ↦ S i₀ ⊆ R ∧ EJ R) := by
          rw [biasedEventProb_eq_sum_filter]
          exact sum_nonneg fun R _ ↦ biasedWeight_nonneg hp₀ hp₁ R
        exact hle0.trans hge0
      · push Not at hδ
        rw [biasedEventProb_subset_and_eq (hSX i₀) p EJ]
        let E₁ : Finset α → Prop := fun R' ↦ ∀ j ∈ J₁, ¬ S j ⊆ S i₀ ∪ R'
        let E₂ : Finset α → Prop := fun R' ↦ ∀ j ∈ J₂, ¬ S j ⊆ R'
        have hiff_cond : ∀ R' ∈ (X \ S i₀).powerset,
            (EJ (S i₀ ∪ R') ↔ E₁ R' ∧ E₂ R') := by
          intro R' _
          simp only [EJ, E₁, E₂, J₁, J₂, mem_filter]
          constructor
          · intro h
            refine ⟨fun j hj ↦ h j hj.1, fun j hj hsub ↦ h j hj.1 (hsub.trans subset_union_right)⟩
          · rintro ⟨h₁, h₂⟩ j hj hsub
            by_cases hd : Disjoint (S i₀) (S j)
            · refine h₂ j ⟨hj, hd⟩ (fun x hx ↦ ?_)
              rcases mem_union.1 (hsub hx) with hxi₀ | hxR'
              · exact absurd hx (disjoint_left.1 hd hxi₀)
              · exact hxR'
            · exact h₁ j ⟨hj, hd⟩ hsub
        have hcongr_cond : biasedEventProb (X \ S i₀) p (fun R' ↦ EJ (S i₀ ∪ R')) =
            biasedEventProb (X \ S i₀) p (fun R' ↦ E₁ R' ∧ E₂ R') := by
          rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
          congr 1
          ext R'
          simp only [mem_filter]
          exact and_congr_right fun hR' ↦ hiff_cond R' hR'
        rw [hcongr_cond]
        have hfkg : biasedEventProb (X \ S i₀) p E₁ * biasedEventProb (X \ S i₀) p E₂ ≤
            biasedEventProb (X \ S i₀) p (fun R' ↦ E₁ R' ∧ E₂ R') := by
          refine fkg_lower_events (X \ S i₀) hp₀ hp₁ ?_ ?_
          · intro R₁ R₂ hsub _ h₂ j hj hSj
            exact h₂ j hj
              (hSj.trans (union_subset subset_union_left (hsub.trans subset_union_right)))
          · intro R₁ R₂ hsub _ h₂ j hj hSj
            exact h₂ j hj (hSj.trans hsub)
        have hE₂_eq : biasedEventProb (X \ S i₀) p E₂ = biasedEventProb X p E₂ := by
          refine biasedEventProb_sdiff_eq_of_indep (hSX i₀) p fun R _ ↦ ?_
          simp only [E₂, J₂, mem_filter]
          refine forall₂_congr fun j hj ↦ not_congr ?_
          constructor
          · intro hsub x hx
            exact mem_sdiff.2 ⟨hsub hx, fun hxi₀ ↦ disjoint_left.1 hj.2 hxi₀ hx⟩
          · intro hsub
            exact hsub.trans sdiff_subset
        have hE₂_ge : biasedEventProb X p EJ ≤ biasedEventProb (X \ S i₀) p E₂ := by
          rw [hE₂_eq]
          exact biasedEventProb_mono hp₀ hp₁ fun R _ h j hj ↦ h j (mem_filter.1 hj).1
        have hE₁_lb : δ ≤ p ^ (S i₀).card * biasedEventProb (X \ S i₀) p E₁ := by
          have hub := biasedEventProb_forall_not_ge_one_sub_sum (X \ S i₀) hp₀ hp₁ J₁
            (fun j R' ↦ S j ⊆ S i₀ ∪ R')
          have hprob_j : ∀ j ∈ J₁,
              p ^ (S i₀).card * biasedEventProb (X \ S i₀) p (fun R' ↦ S j ⊆ S i₀ ∪ R') =
                p ^ (S i₀ ∪ S j).card := by
            intro j hj
            have hcongr_j : biasedEventProb (X \ S i₀) p (fun R' ↦ S j ⊆ S i₀ ∪ R') =
                biasedEventProb (X \ S i₀) p (fun R' ↦ S j \ S i₀ ⊆ R') := by
              rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter]
              congr 1
              ext R'
              simp only [mem_filter]
              refine and_congr_right fun hR' ↦ ?_
              have hdisj : Disjoint (S i₀) R' :=
                disjoint_of_subset_right (mem_powerset.1 hR') disjoint_sdiff_self_right
              constructor
              · intro hsub x hx
                obtain ⟨hxj, hxi₀⟩ := mem_sdiff.1 hx
                rcases mem_union.1 (hsub hxj) with h1 | h2
                · exact absurd h1 hxi₀
                · exact h2
              · intro hsub x hx
                by_cases hxi₀ : x ∈ S i₀
                · exact mem_union_left R' hxi₀
                · exact mem_union_right (S i₀) (hsub (mem_sdiff.2 ⟨hx, hxi₀⟩))
            rw [hcongr_j, biasedEventProb_subset_eq
              (sdiff_subset_sdiff (hSX _) Subset.rfl) p, ← pow_add]
            congr 1
            have hd : Disjoint (S i₀) (S j \ S i₀) := disjoint_sdiff_self_right
            have hun : S i₀ ∪ (S j \ S i₀) = S i₀ ∪ S j := union_sdiff_self_eq_union
            rw [← card_union_of_disjoint hd, hun]
          have hmul := mul_le_mul_of_nonneg_left hub (pow_nonneg hp₀ (S i₀).card)
          rw [mul_sub, mul_one, mul_sum, sum_congr rfl hprob_j] at hmul
          exact hmul
        calc δ * biasedEventProb X p EJ
            ≤ (p ^ (S i₀).card * biasedEventProb (X \ S i₀) p E₁) *
                biasedEventProb (X \ S i₀) p E₂ :=
              mul_le_mul hE₁_lb hE₂_ge hEJ_nonneg (hδ.le.trans hE₁_lb)
          _ = p ^ (S i₀).card *
                (biasedEventProb (X \ S i₀) p E₁ * biasedEventProb (X \ S i₀) p E₂) := by ring
          _ ≤ p ^ (S i₀).card *
                biasedEventProb (X \ S i₀) p (fun R' ↦ E₁ R' ∧ E₂ R') :=
              mul_le_mul_of_nonneg_left hfkg (pow_nonneg hp₀ _)
    have hsplit : biasedEventProb X p EJ =
        biasedEventProb X p (fun R ↦ S i₀ ⊆ R ∧ EJ R) +
          biasedEventProb X p (fun R ↦ ∀ i ∈ insert i₀ J, ¬ S i ⊆ R) := by
      rw [biasedEventProb_eq_sum_filter, biasedEventProb_eq_sum_filter,
        biasedEventProb_eq_sum_filter]
      have h1 : (X.powerset.filter fun R ↦ S i₀ ⊆ R ∧ EJ R) =
          (X.powerset.filter EJ).filter (fun R ↦ S i₀ ⊆ R) := by
        ext R; simp only [mem_filter]; tauto
      have h2 : (X.powerset.filter fun R ↦ ∀ i ∈ insert i₀ J, ¬ S i ⊆ R) =
          (X.powerset.filter EJ).filter (fun R ↦ ¬ S i₀ ⊆ R) := by
        ext R; simp only [mem_filter, forall_mem_insert, EJ]; tauto
      rw [h1, h2, sum_filter_add_sum_filter_not]
    have h1sub : biasedEventProb X p (fun R ↦ ∀ i ∈ insert i₀ J, ¬ S i ⊆ R) ≤
        (1 - δ) * biasedEventProb X p EJ := by
      linarith
    have hexp_δ : 1 - δ ≤ Real.exp (-δ) := by
      linarith [Real.add_one_le_exp (-δ)]
    have hsum_ident :
        (∑ i ∈ insert i₀ J, p ^ (S i).card) -
            (1 / 2 : ℝ) * ∑ i ∈ insert i₀ J,
              ∑ j ∈ insert i₀ J with i ≠ j ∧ ¬ Disjoint (S i) (S j),
                p ^ (S i ∪ S j).card =
          δ + ((∑ i ∈ J, p ^ (S i).card) -
            (1 / 2 : ℝ) * ∑ i ∈ J, ∑ j ∈ J with i ≠ j ∧ ¬ Disjoint (S i) (S j),
              p ^ (S i ∪ S j).card) := by
      rw [sum_insert hi₀, sum_insert hi₀]
      have hrow0 :
          (∑ j ∈ insert i₀ J with i₀ ≠ j ∧ ¬ Disjoint (S i₀) (S j), p ^ (S i₀ ∪ S j).card) =
            ∑ j ∈ J₁, p ^ (S i₀ ∪ S j).card := by
        rw [filter_insert]
        simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
        refine sum_congr ?_ fun _ _ ↦ rfl
        ext j
        simp only [J₁, mem_filter]
        exact ⟨fun ⟨hj, _, hd⟩ ↦ ⟨hj, hd⟩,
          fun ⟨hj, hd⟩ ↦ ⟨hj, fun heq ↦ hi₀ (heq ▸ hj), hd⟩⟩
      have hrowsJ :
          (∑ i ∈ J, ∑ j ∈ insert i₀ J with i ≠ j ∧ ¬ Disjoint (S i) (S j),
              p ^ (S i ∪ S j).card) =
            (∑ j ∈ J₁, p ^ (S i₀ ∪ S j).card) +
              ∑ i ∈ J, ∑ j ∈ J with i ≠ j ∧ ¬ Disjoint (S i) (S j),
                p ^ (S i ∪ S j).card := by
        have hper_i : ∀ i ∈ J,
            (∑ j ∈ insert i₀ J with i ≠ j ∧ ¬ Disjoint (S i) (S j), p ^ (S i ∪ S j).card) =
              (if ¬ Disjoint (S i₀) (S i) then p ^ (S i₀ ∪ S i).card else 0) +
                ∑ j ∈ J with i ≠ j ∧ ¬ Disjoint (S i) (S j), p ^ (S i ∪ S j).card := by
          intro i hi
          have hne : i ≠ i₀ := fun heq ↦ hi₀ (heq ▸ hi)
          rw [filter_insert]
          by_cases hd : Disjoint (S i₀) (S i)
          · have hcond : ¬ (i ≠ i₀ ∧ ¬ Disjoint (S i) (S i₀)) := fun h ↦ h.2 hd.symm
            simp only [hcond, ↓reduceIte, hd, not_true_eq_false, zero_add]
          · have hcond : i ≠ i₀ ∧ ¬ Disjoint (S i) (S i₀) := ⟨hne, fun h ↦ hd h.symm⟩
            rw [ite_eq_left hcond, ite_eq_left hd,
              sum_insert (fun h ↦ hi₀ (mem_filter.1 h).1), union_comm]
        rw [sum_congr rfl hper_i, sum_add_distrib, ← sum_filter]
      rw [hrow0, hrowsJ]
      simp only [δ]
      ring
    calc biasedEventProb X p (fun R ↦ ∀ i ∈ insert i₀ J, ¬ S i ⊆ R)
        ≤ (1 - δ) * biasedEventProb X p EJ := h1sub
      _ ≤ Real.exp (-δ) * biasedEventProb X p EJ :=
          mul_le_mul_of_nonneg_right hexp_δ hEJ_nonneg
      _ ≤ Real.exp (-δ) *
            Real.exp (- ((∑ i ∈ J, p ^ (S i).card) -
              (1 / 2 : ℝ) * ∑ i ∈ J, ∑ j ∈ J with i ≠ j ∧ ¬ Disjoint (S i) (S j),
                p ^ (S i ∪ S j).card)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (- ((∑ i ∈ insert i₀ J, p ^ (S i).card) -
            (1 / 2 : ℝ) * ∑ i ∈ insert i₀ J,
              ∑ j ∈ insert i₀ J with i ≠ j ∧ ¬ Disjoint (S i) (S j),
                p ^ (S i ∪ S j).card)) := by
          rw [← Real.exp_add, hsum_ident]
          ring_nf

/-- **Janson's inequality** for `p`-biased random subsets: for `S : ι → Finset α` with `S i ⊆ X`,
let `μ = ∑ i, p ^ |S i|` and `Δ = ∑_{i, j : S i ∩ S j ≠ ∅} p ^ |S i ∪ S j|` (including diagonal
pairs `(i, i)` when `S i ≠ ∅`). If `0 < μ ≤ Δ`, then
`Pr[∀ i, ¬ S i ⊆ R] ≤ exp(- μ ^ 2 / (2 * Δ))`. -/
public theorem janson_inequality {α ι : Type*} [DecidableEq α] [Fintype ι]
    (X : Finset α) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (S : ι → Finset α) (hSX : ∀ i, S i ⊆ X) :
    let μ : ℝ := ∑ i : ι, p ^ (S i).card
    let Δ : ℝ := ∑ i : ι, ∑ j ∈ (univ : Finset ι) with ¬ Disjoint (S i) (S j),
      p ^ (S i ∪ S j).card
    0 < μ → μ ≤ Δ →
      biasedEventProb X p (fun R ↦ ∀ i : ι, ¬ S i ⊆ R) ≤ Real.exp (- (μ ^ 2 / (2 * Δ))) := by
  classical
  intro μ Δ hμ_pos hμΔ
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le hμ_pos hμΔ
  let q : ℝ := μ / Δ
  have hq₀ : 0 ≤ q := div_nonneg hμ_pos.le hΔ_pos.le
  have hq₁ : q ≤ 1 := (div_le_one hΔ_pos).2 hμΔ
  let f : Finset ι → ℝ := fun I ↦
    (∑ i ∈ I, p ^ (S i).card) -
      (1 / 2 : ℝ) * ∑ i ∈ I, ∑ j ∈ I with i ≠ j ∧ ¬ Disjoint (S i) (S j),
        p ^ (S i ∪ S j).card
  let Δ_off : ℝ := ∑ i : ι, ∑ j ∈ (univ : Finset ι) with i ≠ j ∧ ¬ Disjoint (S i) (S j),
    p ^ (S i ∪ S j).card
  have hΔ_off_le : Δ_off ≤ Δ := by
    refine sum_le_sum fun i _ ↦ sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      exact mem_filter.2 ⟨mem_univ j, (mem_filter.1 hj).2.2⟩
    · intro j _ _
      exact pow_nonneg hp₀ _
  have hexpect_lin : biasedExpect (univ : Finset ι) q (fun I ↦ ∑ i ∈ I, p ^ (S i).card) =
      q * μ := by
    rw [biasedExpect_eq_sum]
    calc ∑ I ∈ (univ : Finset ι).powerset, biasedWeight univ q I * ∑ i ∈ I, p ^ (S i).card
        = ∑ I ∈ (univ : Finset ι).powerset,
            ∑ i : ι, (if i ∈ I then biasedWeight univ q I * p ^ (S i).card else 0) := by
          refine sum_congr rfl fun I _ ↦ ?_
          rw [mul_sum, ← sum_filter, filter_mem_eq_inter, univ_inter]
      _ = ∑ i : ι,
            (∑ I ∈ (univ : Finset ι).powerset with i ∈ I, biasedWeight univ q I) *
              p ^ (S i).card := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ ↦ ?_
          rw [sum_mul, ← sum_filter]
      _ = ∑ i : ι, q * p ^ (S i).card := by
          refine sum_congr rfl fun i _ ↦ ?_
          have hprob_i :
              (∑ I ∈ (univ : Finset ι).powerset with i ∈ I, biasedWeight univ q I) = q := by
            have h1 := biasedEventProb_subset_eq (subset_univ ({i} : Finset ι)) q
            rw [biasedEventProb_eq_sum_filter, card_singleton, pow_one] at h1
            simpa only [singleton_subset_iff] using h1
          rw [hprob_i]
      _ = q * μ := (mul_sum _ _ _).symm
  have hexpect_quad :
      biasedExpect (univ : Finset ι) q
          (fun I ↦ ∑ i ∈ I, ∑ j ∈ I with i ≠ j ∧ ¬ Disjoint (S i) (S j),
            p ^ (S i ∪ S j).card) =
        q ^ 2 * Δ_off := by
    rw [biasedExpect_eq_sum]
    let Pairs := (univ ×ˢ (univ : Finset ι)).filter fun x : ι × ι ↦
      x.1 ≠ x.2 ∧ ¬ Disjoint (S x.1) (S x.2)
    have hinner : ∀ I : Finset ι,
        (∑ i ∈ I, ∑ j ∈ I with i ≠ j ∧ ¬ Disjoint (S i) (S j), p ^ (S i ∪ S j).card) =
          ∑ x ∈ Pairs, if x.1 ∈ I ∧ x.2 ∈ I then p ^ (S x.1 ∪ S x.2).card else 0 := by
      intro I
      rw [← sum_filter]
      have hfilt : (Pairs.filter fun x ↦ x.1 ∈ I ∧ x.2 ∈ I) =
          (I ×ˢ I).filter fun x ↦ x.1 ≠ x.2 ∧ ¬ Disjoint (S x.1) (S x.2) := by
        ext ⟨i, j⟩
        simp only [Pairs, mem_filter, mem_product, mem_univ, true_and]
        tauto
      rw [hfilt, sum_filter]
      simpa only [sum_filter] using
        (sum_product' I I fun i j ↦
          if i ≠ j ∧ ¬ Disjoint (S i) (S j) then p ^ (S i ∪ S j).card else 0).symm
    calc ∑ I ∈ (univ : Finset ι).powerset,
            biasedWeight univ q I *
              ∑ i ∈ I, ∑ j ∈ I with i ≠ j ∧ ¬ Disjoint (S i) (S j), p ^ (S i ∪ S j).card
        = ∑ I ∈ (univ : Finset ι).powerset,
            ∑ x ∈ Pairs,
              if x.1 ∈ I ∧ x.2 ∈ I then
                biasedWeight univ q I * p ^ (S x.1 ∪ S x.2).card
              else 0 := by
          refine sum_congr rfl fun I _ ↦ ?_
          rw [hinner I, mul_sum]
          exact sum_congr rfl fun x _ ↦ by split_ifs <;> ring
      _ = ∑ x ∈ Pairs,
            (∑ I ∈ (univ : Finset ι).powerset with x.1 ∈ I ∧ x.2 ∈ I, biasedWeight univ q I) *
              p ^ (S x.1 ∪ S x.2).card := by
          rw [sum_comm]
          refine sum_congr rfl fun x _ ↦ ?_
          rw [sum_mul, ← sum_filter]
      _ = ∑ x ∈ Pairs, q ^ 2 * p ^ (S x.1 ∪ S x.2).card := by
          refine sum_congr rfl fun x hx ↦ ?_
          have hne : x.1 ≠ x.2 := (mem_filter.1 hx).2.1
          have hprob_ij :
              (∑ I ∈ (univ : Finset ι).powerset with x.1 ∈ I ∧ x.2 ∈ I,
                biasedWeight univ q I) = q ^ 2 := by
            have h1 := biasedEventProb_subset_eq (subset_univ ({x.1, x.2} : Finset ι)) q
            rw [biasedEventProb_eq_sum_filter, card_pair hne] at h1
            convert h1 using 2
            ext I
            simp [insert_subset_iff]
          rw [hprob_ij]
      _ = q ^ 2 * ∑ x ∈ Pairs, p ^ (S x.1 ∪ S x.2).card := (mul_sum _ _ _).symm
      _ = q ^ 2 * Δ_off := by
          congr 1
          simp only [Pairs, Δ_off, sum_filter]
          rw [← sum_product']
  have hexpect_f : biasedExpect (univ : Finset ι) q f = q * μ - (1 / 2 : ℝ) * (q ^ 2 * Δ_off) := by
    rw [biasedExpect_eq_sum] at hexpect_lin hexpect_quad ⊢
    calc ∑ I ∈ (univ : Finset ι).powerset, biasedWeight univ q I * f I
        = (∑ I ∈ (univ : Finset ι).powerset,
              biasedWeight univ q I * ∑ i ∈ I, p ^ (S i).card) -
            (1 / 2 : ℝ) * ∑ I ∈ (univ : Finset ι).powerset,
              biasedWeight univ q I *
                ∑ i ∈ I, ∑ j ∈ I with i ≠ j ∧ ¬ Disjoint (S i) (S j),
                  p ^ (S i ∪ S j).card := by
          simp only [f, mul_sub, sum_sub_distrib]
          congr 1
          rw [mul_sum]
          exact sum_congr rfl fun I _ ↦ by ring
      _ = q * μ - (1 / 2 : ℝ) * (q ^ 2 * Δ_off) := by rw [hexpect_lin, hexpect_quad]
  obtain ⟨I₀, -, hI₀_max⟩ := (univ : Finset ι).powerset.exists_max_image f
    ⟨∅, mem_powerset.2 (empty_subset _)⟩
  have hf_ge : μ ^ 2 / (2 * Δ) ≤ f I₀ := by
    have hle_max : biasedExpect (univ : Finset ι) q f ≤ f I₀ := by
      rw [biasedExpect_eq_sum]
      calc ∑ I ∈ (univ : Finset ι).powerset, biasedWeight univ q I * f I
          ≤ ∑ I ∈ (univ : Finset ι).powerset, biasedWeight univ q I * f I₀ :=
            sum_le_sum fun I hI ↦ mul_le_mul_of_nonneg_left (hI₀_max I hI)
              (biasedWeight_nonneg hq₀ hq₁ I)
        _ = (∑ I ∈ (univ : Finset ι).powerset, biasedWeight univ q I) * f I₀ :=
            (sum_mul _ _ _).symm
        _ = f I₀ := by rw [sum_biasedWeight_powerset, one_mul]
    have hquad_le : q ^ 2 * Δ_off ≤ q ^ 2 * Δ :=
      mul_le_mul_of_nonneg_left hΔ_off_le (sq_nonneg q)
    have hval : q * μ - (1 / 2 : ℝ) * (q ^ 2 * Δ) = μ ^ 2 / (2 * Δ) := by
      simp only [q]
      field_simp [hΔ_pos.ne']
      ring
    linarith
  calc biasedEventProb X p (fun R ↦ ∀ i : ι, ¬ S i ⊆ R)
      ≤ biasedEventProb X p (fun R ↦ ∀ i ∈ I₀, ¬ S i ⊆ R) :=
        biasedEventProb_mono hp₀ hp₁ fun R _ h i _ ↦ h i
    _ ≤ Real.exp (- f I₀) := janson_subset_bound X hp₀ hp₁ S hSX I₀
    _ ≤ Real.exp (- (μ ^ 2 / (2 * Δ))) := Real.exp_le_exp.2 (neg_le_neg hf_ge)

end CslibFrontier
