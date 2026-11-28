/-
Copyright (c) 2026 Formal Papers / CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers contributors
-/
module

-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.Basic

public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Absorbing Finite Markov Chains, Bellman Operators, and Harmonic Guess Verification

Let `P : Cslib.Probability.MarkovChain S` be a homogeneous discrete-time Markov chain on a finite
state space `S`, and let `T : Set S` be a target subset of states. This module develops the
discrete theory of absorbing Bellman operators for weighted reachability and stochastic shortest
path (SSP) objectives on `Cslib.Probability.MarkovChain`:

* `minPosProb P`: smallest positive transition probability (`0 < minPosProb P ≤ 1`).
* `levelIndex P T s` and `numLevels P T`: shortest-path BFS level partition to `ellZero P T`.
* `expectStep`, `subStep`, `survivalSet`, `affineBellman`, `reachBellman`, `sspBellman`:
  Bellman operators, level-refined `k * t` interval contraction
    (`affineBellman_ivi_interval_bound`),
  and Banach fixed-point existence, uniqueness, comparison, and global convergence
  (`affineBellmanVal`, `reachVal`, `sspVal`, `tendsto_iterate_affineBellman`).
* `reduceChain P s` and `hitBeforeProb P T s`: harmonic linear interpolation on reduced Markov
  chains (`affineBellmanVal_insert_eq`), exact one-step Bellman guess verification
  (`gt_iff_affineBellman_insert_gt`, `lt_iff_affineBellman_insert_lt`), and `δ_min ^ |S|`
  encompassing bounds (`affineBellman_encompassing_lower`, `affineBellman_encompassing_upper`).
-/

public section

noncomputable section

open Filter
open scoped ENNReal NNReal Topology

namespace CslibFrontier.Probability.MarkovChain

section ReachabilityAndLevels

variable {S : Type*}

/-- A subset `T : Set S` is **absorbing** for `P : Cslib.Probability.MarkovChain S` if every state
`s ∈ T` transitions deterministically to itself (`P s = PMF.pure s`). -/
def IsAbsorbingSet (P : Cslib.Probability.MarkovChain S) (T : Set S) : Prop :=
  ∀ s ∈ T, P s = PMF.pure s

/-- State `s` **reaches** `T` in `P` if there is a finite path of positive-probability transitions
from `s` to some `t ∈ T`. -/
def ReachesSet (P : Cslib.Probability.MarkovChain S) (T : Set S) (s : S) : Prop :=
  ∃ t ∈ T, Relation.ReflTransGen (fun a b ↦ P a b ≠ 0) s t

/-- Every state in `S` reaches `T` along positive-probability transitions of `P`. -/
def AllReachSet (P : Cslib.Probability.MarkovChain S) (T : Set S) : Prop :=
  ∀ s : S, ReachesSet P T s

/-- Every state in `T` reaches `T` in zero steps. -/
theorem reachesSet_of_mem {P : Cslib.Probability.MarkovChain S} {T : Set S} {s : S}
    (hs : s ∈ T) : ReachesSet P T s :=
  ⟨s, hs, Relation.ReflTransGen.refl⟩

/-- If `P s s' ≠ 0` and `s'` reaches `T`, then `s` reaches `T`. -/
theorem reachesSet_of_step {P : Cslib.Probability.MarkovChain S} {T : Set S} {s s' : S}
    (hstep : P s s' ≠ 0) (hs' : ReachesSet P T s') : ReachesSet P T s := by
  rcases hs' with ⟨t, ht, hpath⟩
  exact ⟨t, ht, Relation.ReflTransGen.head hstep hpath⟩

/-- Level-`0` base set `ellZero P T` consisting of `T` together with all states that cannot reach
`T` along positive-probability transitions. -/
def ellZero (P : Cslib.Probability.MarkovChain S) (T : Set S) : Set S :=
  {s : S | s ∈ T ∨ ¬ ReachesSet P T s}

/-- When `AllReachSet P T` holds, `ellZero P T` coincides with `T`. -/
theorem ellZero_eq_of_allReachSet {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) : ellZero P T = T := by
  ext s
  simp [ellZero, hreach s]

/-- The **reduced Markov chain** obtained from `P` by making state `s` absorbing (`PMF.pure s`)
while keeping all other transition rows unchanged. -/
def reduceChain (P : Cslib.Probability.MarkovChain S) (s : S)
    : Cslib.Probability.MarkovChain S where
  step x := @ite _ (x = s) (Classical.propDecidable _) (PMF.pure s) (P x)

@[simp]
theorem reduceChain_self (P : Cslib.Probability.MarkovChain S) (s : S) :
    reduceChain P s s = PMF.pure s := by
  simp [reduceChain]

@[simp]
theorem reduceChain_of_ne (P : Cslib.Probability.MarkovChain S) {s x : S} (hx : x ≠ s) :
    reduceChain P s x = P x := by
  simp [reduceChain, hx]

theorem AllReachSet.insert_reduceChain {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (s : S) :
    AllReachSet (reduceChain P s) (insert s T) := by
  intro x
  rcases hreach x with ⟨t, ht, hpath⟩
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact reachesSet_of_mem (Set.mem_insert_of_mem s ht)
  | @head a b hab _ ih =>
    by_cases has : a = s
    · subst has
      exact reachesSet_of_mem (Set.mem_insert a T)
    · refine reachesSet_of_step ?_ ih
      simpa [reduceChain_of_ne P has] using hab

/-- `ReachInSteps P B k s` holds if `s` can reach `B` in at most `k` positive-probability steps. -/
def ReachInSteps (P : Cslib.Probability.MarkovChain S) (B : Set S) : ℕ → S → Prop
  | 0, s => s ∈ B
  | k + 1, s => ReachInSteps P B k s ∨ ∃ s', P s s' ≠ 0 ∧ ReachInSteps P B k s'

private theorem reachInSteps_mono {P : Cslib.Probability.MarkovChain S} {B : Set S}
    {j k : ℕ} (hjk : j ≤ k) {s : S} (hs : ReachInSteps P B j s) : ReachInSteps P B k s := by
  induction k, hjk using Nat.le_induction with
  | base => exact hs
  | succ _ _ ih => exact Or.inl ih

section FiniteLevels

variable [Fintype S]

/-- Smallest positive transition probability `δ_min(P)` of a finite Markov chain `P` (`1` when `S`
is empty). -/
def minPosProb (P : Cslib.Probability.MarkovChain S) : ℝ := by
  classical
  exact if h : ((Finset.univ ×ˢ Finset.univ).filter fun p : S × S ↦ P p.1 p.2 ≠ 0).Nonempty then
    (((Finset.univ ×ˢ Finset.univ).filter fun p : S × S ↦ P p.1 p.2 ≠ 0).image
      fun p : S × S ↦ (P p.1 p.2).toReal).min' (h.image _)
  else 1

theorem minPosProb_pos (P : Cslib.Probability.MarkovChain S) : 0 < minPosProb P := by
  classical
  unfold minPosProb
  split_ifs with h
  · have hy := Finset.min'_mem
      (((Finset.univ ×ˢ Finset.univ).filter fun p : S × S ↦ P p.1 p.2 ≠ 0).image
        fun p : S × S ↦ (P p.1 p.2).toReal) (h.image _)
    rcases Finset.mem_image.mp hy with ⟨p, hp, hp_eq⟩
    rw [← hp_eq]
    exact ENNReal.toReal_pos (Finset.mem_filter.mp hp).2 ((P p.1).apply_ne_top p.2)
  · exact zero_lt_one

theorem minPosProb_le_one (P : Cslib.Probability.MarkovChain S) : minPosProb P ≤ 1 := by
  classical
  unfold minPosProb
  split_ifs with h
  · rcases h with ⟨p, hp⟩
    exact (Finset.min'_le _ ((P p.1 p.2).toReal)
      (Finset.mem_image_of_mem (fun q : S × S ↦ (P q.1 q.2).toReal) hp)).trans
      (ENNReal.toReal_mono ENNReal.one_ne_top ((P p.1).coe_le_one p.2))
  · exact le_rfl

theorem minPosProb_le_toReal {P : Cslib.Probability.MarkovChain S} {s s' : S}
    (h : P s s' ≠ 0) : minPosProb P ≤ (P s s').toReal := by
  classical
  have hmem : (s, s') ∈ (Finset.univ ×ˢ Finset.univ).filter fun p : S × S ↦ P p.1 p.2 ≠ 0 := by
    simp [h]
  unfold minPosProb
  rw [dite_eq_left ⟨(s, s'), hmem⟩]
  exact Finset.min'_le _ ((P s s').toReal)
    (Finset.mem_image_of_mem (fun q : S × S ↦ (P q.1 q.2).toReal) hmem)

private theorem reachInSteps_card_of_reachesSet {P : Cslib.Probability.MarkovChain S} {B : Set S}
    {s : S} (h : ∃ b ∈ B, Relation.ReflTransGen (fun x y ↦ P x y ≠ 0) s b) :
    ReachInSteps P B (Fintype.card S) s := by
  classical
  let layer : ℕ → Finset S := fun k ↦ Finset.univ.filter (ReachInSteps P B k)
  have hmono : ∀ k, layer k ⊆ layer (k + 1) := fun k x hx ↦ by
    simp only [layer, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact Or.inl hx
  have hstab : ∃ k ≤ Fintype.card S, layer k = layer (k + 1) := by
    by_contra! hgrow
    have hcard : ∀ k ≤ Fintype.card S + 1, k ≤ (layer k).card := by
      intro k hk
      induction k with
      | zero => exact Nat.zero_le _
      | succ m ih =>
        have hlt := Finset.card_lt_card
          (ssubset_iff_subset_ne.mpr ⟨hmono m, hgrow m (by omega)⟩)
        have := ih (by omega); omega
    have := hcard (Fintype.card S + 1) le_rfl
    have := Finset.card_le_univ (layer (Fintype.card S + 1))
    omega
  rcases hstab with ⟨k₀, hk₀, heq⟩
  have hclosed : ∀ x y, P x y ≠ 0 → ReachInSteps P B k₀ y → ReachInSteps P B k₀ x := by
    intro x y hxy hy
    have hmem : x ∈ layer (k₀ + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, Or.inr ⟨y, hxy, hy⟩⟩
    rw [← heq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  rcases h with ⟨b, hb, hpath⟩
  have hk₀_s : ReachInSteps P B k₀ s := by
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact reachInSteps_mono (Nat.zero_le k₀) hb
    | @head x y hxy _ ih => exact hclosed x y hxy ih
  exact reachInSteps_mono hk₀ hk₀_s

omit [Fintype S] in
private theorem exists_reachInSteps_ellZero [Finite S] (P : Cslib.Probability.MarkovChain S)
    (T : Set S) (s : S) : ∃ k, ReachInSteps P (ellZero P T) k s := by
  cases nonempty_fintype S
  by_cases h : ReachesSet P T s
  · rcases h with ⟨t, ht, hpath⟩
    exact ⟨Fintype.card S, reachInSteps_card_of_reachesSet ⟨t, Or.inl ht, hpath⟩⟩
  · exact ⟨0, Or.inr h⟩

/-- Shortest-path BFS level index `levelIndex P T s`. -/
def levelIndex (P : Cslib.Probability.MarkovChain S) (T : Set S) (s : S) : ℕ := by
  classical
  exact Nat.find (exists_reachInSteps_ellZero P T s)

/-- Maximum shortest-path level `numLevels P T`. -/
def numLevels (P : Cslib.Probability.MarkovChain S) (T : Set S) : ℕ :=
  Finset.univ.sup (levelIndex P T)

theorem levelIndex_eq_zero_iff_of_allReachSet {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (s : S) :
    levelIndex P T s = 0 ↔ s ∈ T := by
  classical
  unfold levelIndex
  rw [Nat.find_eq_zero, ReachInSteps, ellZero_eq_of_allReachSet hreach]

theorem levelIndex_le_numLevels (P : Cslib.Probability.MarkovChain S) (T : Set S) (s : S) :
    levelIndex P T s ≤ numLevels P T :=
  Finset.le_sup (f := levelIndex P T) (Finset.mem_univ s)

theorem levelIndex_le_card (P : Cslib.Probability.MarkovChain S) (T : Set S) (s : S) :
    levelIndex P T s ≤ Fintype.card S := by
  classical
  unfold levelIndex
  refine Nat.find_min' _ ?_
  by_cases h : ReachesSet P T s
  · rcases h with ⟨t, ht, hpath⟩
    exact reachInSteps_card_of_reachesSet ⟨t, Or.inl ht, hpath⟩
  · exact reachInSteps_mono (Nat.zero_le _) (Or.inr h)

theorem levelIndex_step_pred {P : Cslib.Probability.MarkovChain S} {T : Set S} {s : S} {i : ℕ}
    (hi : levelIndex P T s = i + 1) :
    ∃ s' : S, P s s' ≠ 0 ∧ levelIndex P T s' = i := by
  classical
  have hspec : ReachInSteps P (ellZero P T) (i + 1) s := by
    unfold levelIndex at hi; exact hi ▸ Nat.find_spec (exists_reachInSteps_ellZero P T s)
  have hnot : ¬ ReachInSteps P (ellZero P T) i s := by
    unfold levelIndex at hi
    exact Nat.find_min (exists_reachInSteps_ellZero P T s) (by omega)
  rcases hspec with h_i | ⟨s', hstep, hs'⟩
  · exact absurd h_i hnot
  · refine ⟨s', hstep, le_antisymm ?_ ?_⟩
    · unfold levelIndex; exact Nat.find_min' _ hs'
    · by_contra! hlt
      have hs'_i1 : ReachInSteps P (ellZero P T) (i - 1) s' := by
        refine reachInSteps_mono (by omega : levelIndex P T s' ≤ i - 1) ?_
        unfold levelIndex; exact Nat.find_spec (exists_reachInSteps_ellZero P T s')
      have hs_i : ReachInSteps P (ellZero P T) i s := by
        rw [show i = (i - 1) + 1 by omega]
        exact Or.inr ⟨s', hstep, hs'_i1⟩
      exact hnot hs_i

end FiniteLevels

end ReachabilityAndLevels

section BellmanAndGuessing

variable {S : Type*} [Fintype S]

/-- One-step expectation `(expectStep P v) s = ∑ s', (P s s').toReal * v s'`. -/
def expectStep (P : Cslib.Probability.MarkovChain S) (v : S → ℝ) (s : S) : ℝ :=
  ∑ s' : S, (P s s').toReal * v s'

theorem sum_toReal_apply (P : Cslib.Probability.MarkovChain S) (s : S) :
    ∑ s' : S, (P s s').toReal = 1 := by
  have hsum : ∑ s' : S, P s s' = 1 := by rw [← (P s).tsum_coe, tsum_fintype]
  rw [← ENNReal.toReal_sum (fun s' _ ↦ (P s).apply_ne_top s'), hsum, ENNReal.toReal_one]

@[simp]
theorem expectStep_const (P : Cslib.Probability.MarkovChain S) (c : ℝ) (s : S) :
    expectStep P (fun _ ↦ c) s = c := by
  simp [expectStep, ← Finset.sum_mul, sum_toReal_apply]

theorem expectStep_add (P : Cslib.Probability.MarkovChain S) (u v : S → ℝ) (s : S) :
    expectStep P (u + v) s = expectStep P u s + expectStep P v s := by
  simp only [expectStep, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem expectStep_sub (P : Cslib.Probability.MarkovChain S) (u v : S → ℝ) (s : S) :
    expectStep P (u - v) s = expectStep P u s - expectStep P v s := by
  simp only [expectStep, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem expectStep_smul (P : Cslib.Probability.MarkovChain S) (c : ℝ) (v : S → ℝ) (s : S) :
    expectStep P (fun x ↦ c * v x) s = c * expectStep P v s := by
  simp only [expectStep, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by ring

@[gcongr]
theorem expectStep_mono {P : Cslib.Probability.MarkovChain S} {u v : S → ℝ}
    (h : ∀ s', u s' ≤ v s') (s : S) :
    expectStep P u s ≤ expectStep P v s :=
  Finset.sum_le_sum fun s' _ ↦ mul_le_mul_of_nonneg_left (h s') ENNReal.toReal_nonneg

theorem abs_expectStep_le_norm (P : Cslib.Probability.MarkovChain S) (v : S → ℝ) (s : S) :
    |expectStep P v s| ≤ ‖v‖ := by
  calc |∑ s' : S, (P s s').toReal * v s'|
      ≤ ∑ s' : S, (P s s').toReal * |v s'| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun s' _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ s' : S, (P s s').toReal * ‖v‖ :=
        Finset.sum_le_sum fun s' _ ↦
          mul_le_mul_of_nonneg_left (norm_le_pi_norm v s') ENNReal.toReal_nonneg
    _ = ‖v‖ := by rw [← Finset.sum_mul, sum_toReal_apply, one_mul]

/-- Substochastic step operator `subStep P T`. -/
def subStep (P : Cslib.Probability.MarkovChain S) (T : Set S) (v : S → ℝ) (s : S) : ℝ :=
  @ite _ (s ∈ T) (Classical.propDecidable _) 0 (expectStep P v s)

/-- Finite-horizon target-avoidance probability `survivalSet P T t s`. -/
def survivalSet (P : Cslib.Probability.MarkovChain S) (T : Set S) (t : ℕ) : S → ℝ :=
  (subStep P T)^[t] fun s ↦ @ite _ (s ∈ T) (Classical.propDecidable _) 0 1

private theorem subStep_iterate_mono {P : Cslib.Probability.MarkovChain S} {T : Set S} (n : ℕ)
    {u v : S → ℝ} (h : ∀ s, u s ≤ v s) :
    ∀ s, (subStep P T)^[n] u s ≤ (subStep P T)^[n] v s := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro s; rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases hs : s ∈ T <;> simp [subStep, hs, expectStep_mono ih s]

private theorem subStep_iterate_smul (P : Cslib.Probability.MarkovChain S) (T : Set S) (n : ℕ)
    (c : ℝ) (v : S → ℝ) :
    (subStep P T)^[n] (fun s ↦ c * v s) = fun s ↦ c * (subStep P T)^[n] v s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    ext s; by_cases hs : s ∈ T <;> simp [subStep, hs, expectStep_smul]

theorem survivalSet_le_one (P : Cslib.Probability.MarkovChain S) (T : Set S) :
    ∀ (t : ℕ) (s : S), survivalSet P T t s ≤ 1
  | 0, s => by by_cases hs : s ∈ T <;> simp [survivalSet, hs]
  | t + 1, s => by
    rw [survivalSet, Function.iterate_succ_apply']
    by_cases hs : s ∈ T
    · simp [subStep, hs]
    · simp only [subStep, ite_eq_right hs]
      exact (expectStep_mono (survivalSet_le_one P T t) s).trans_eq (expectStep_const P 1 s)

private theorem survivalSet_of_mem (P : Cslib.Probability.MarkovChain S) {T : Set S} {x : S}
    (hx : x ∈ T) : ∀ n : ℕ, survivalSet P T n x = 0
  | 0 => by simp [survivalSet, hx]
  | n + 1 => by simp [survivalSet, Function.iterate_succ_apply', subStep, hx]

theorem survivalSet_antitone (P : Cslib.Probability.MarkovChain S) (T : Set S) (s : S) :
    Antitone fun t ↦ survivalSet P T t s :=
  antitone_nat_of_succ_le fun t ↦ by
    have h10 : ∀ x, survivalSet P T 1 x ≤ survivalSet P T 0 x := fun x ↦ by
      by_cases hx : x ∈ T
      · simp [survivalSet_of_mem P hx]
      · simp only [survivalSet, Function.iterate_one, Function.iterate_zero_apply, subStep,
          ite_eq_right hx]
        exact (expectStep_mono (survivalSet_le_one P T 0) x).trans_eq (expectStep_const P 1 x)
    simpa [survivalSet, ← Function.iterate_add_apply, Nat.add_comm] using
      subStep_iterate_mono t h10 s

theorem survivalSet_le_one_sub_pow_levelIndex {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) :
    ∀ {i : ℕ} {s : S}, levelIndex P T s = i →
      survivalSet P T i s ≤ 1 - (minPosProb P) ^ i
  | 0, s, hi => by
    have hsT : s ∈ T := (levelIndex_eq_zero_iff_of_allReachSet hreach s).mp hi
    simp [survivalSet, hsT]
  | i + 1, s, hi => by
    have hsT : s ∉ T := fun hmem ↦ by
      have := (levelIndex_eq_zero_iff_of_allReachSet hreach s).mpr hmem; omega
    obtain ⟨sStar, hstep, hsStar_lvl⟩ := levelIndex_step_pred hi
    rw [survivalSet, Function.iterate_succ_apply']
    simp only [subStep, ite_eq_right hsT]
    change expectStep P (survivalSet P T i) s ≤ 1 - (minPosProb P) ^ (i + 1)
    have hih := survivalSet_le_one_sub_pow_levelIndex hreach hsStar_lvl
    have hp_ge := minPosProb_le_toReal hstep
    classical
    rw [expectStep, ← Finset.add_sum_erase _ _ (Finset.mem_univ sStar)]
    have hrest : ∑ x ∈ Finset.univ.erase sStar, (P s x).toReal * survivalSet P T i x ≤
        (1 - (P s sStar).toReal) * 1 := by
      calc ∑ x ∈ Finset.univ.erase sStar, (P s x).toReal * survivalSet P T i x
          ≤ ∑ x ∈ Finset.univ.erase sStar, (P s x).toReal * 1 :=
            Finset.sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left (survivalSet_le_one P T i x) ENNReal.toReal_nonneg
        _ = (1 - (P s sStar).toReal) * 1 := by
            have := Finset.add_sum_erase Finset.univ (fun x ↦ (P s x).toReal)
              (Finset.mem_univ sStar)
            rw [sum_toReal_apply] at this; rw [← Finset.sum_mul]; linarith
    have hstar := mul_le_mul_of_nonneg_left hih (ENNReal.toReal_nonneg (a := P s sStar))
    have hpos : 0 ≤ (minPosProb P) ^ i := pow_nonneg (minPosProb_pos P).le i
    rw [pow_succ']
    nlinarith

/-- Unified **affine Bellman operator** on `Cslib.Probability.MarkovChain S`. -/
def affineBellman (P : Cslib.Probability.MarkovChain S) (T : Set S) (term stepCost : S → ℝ)
    (v : S → ℝ) (s : S) : ℝ :=
  @ite _ (s ∈ T) (Classical.propDecidable _) (term s) (stepCost s + expectStep P v s)

/-- Weighted reachability Bellman operator. -/
def reachBellman (P : Cslib.Probability.MarkovChain S) (T : Set S) (w : S → ℝ) :
    (S → ℝ) → (S → ℝ) :=
  affineBellman P T w 0

/-- Stochastic shortest path Bellman operator. -/
def sspBellman (P : Cslib.Probability.MarkovChain S) (T : Set S) (w : S → ℝ) :
    (S → ℝ) → (S → ℝ) :=
  affineBellman P T w w

@[gcongr]
theorem affineBellman_mono {P : Cslib.Probability.MarkovChain S} {T : Set S}
    {term stepCost u v : S → ℝ} (h : ∀ s', u s' ≤ v s') (s : S) :
    affineBellman P T term stepCost u s ≤ affineBellman P T term stepCost v s := by
  by_cases hs : s ∈ T <;> simp [affineBellman, hs, expectStep_mono h s]

theorem affineBellman_iterate_sub (P : Cslib.Probability.MarkovChain S) (T : Set S)
    (term stepCost : S → ℝ) :
    ∀ (n : ℕ) (u v : S → ℝ),
      (affineBellman P T term stepCost)^[n + 1] u -
        (affineBellman P T term stepCost)^[n + 1] v =
        (subStep P T)^[n + 1] (u - v)
  | 0, u, v => by ext s; by_cases hs : s ∈ T <;> simp [affineBellman, subStep, hs, expectStep_sub]
  | n + 1, u, v => by
    ext s
    rw [Pi.sub_apply, Function.iterate_succ_apply' (n := n + 1),
      Function.iterate_succ_apply' (n := n + 1), Function.iterate_succ_apply' (n := n + 1)]
    have ih := affineBellman_iterate_sub P T term stepCost n u v
    by_cases hs : s ∈ T
    · simp [affineBellman, subStep, hs]
    · simp only [affineBellman, subStep, ite_eq_right hs]
      rw [add_sub_add_left_eq_sub, ← expectStep_sub, ih]

private theorem abs_subStep_iterate_le (P : Cslib.Probability.MarkovChain S) (T : Set S) :
    ∀ (n : ℕ) (v : S → ℝ) (s : S),
      |(subStep P T)^[n] v s| ≤ (subStep P T)^[n] (fun x ↦ |v x|) s
  | 0, _, _ => le_rfl
  | n + 1, v, s => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases hs : s ∈ T
    · simp [subStep, hs]
    · simp only [subStep, ite_eq_right hs, expectStep]
      calc |∑ s' : S, (P s s').toReal * (subStep P T)^[n] v s'|
          ≤ ∑ s' : S, (P s s').toReal * |(subStep P T)^[n] v s'| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun s' _ ↦ ?_)
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        _ ≤ _ := Finset.sum_le_sum fun s' _ ↦
            mul_le_mul_of_nonneg_left (abs_subStep_iterate_le P T n v s') ENNReal.toReal_nonneg

theorem affineBellman_ivi_interval_bound {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost l₀ u₀ : S → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hT_eq : ∀ s ∈ T, u₀ s = l₀ s) (hbound : ∀ s ∉ T, |u₀ s - l₀ s| ≤ C)
    {t : ℕ} (ht : 1 ≤ t) {i : ℕ} {s : S} (hi : levelIndex P T s = i) :
    |(affineBellman P T term stepCost)^[numLevels P T * t] u₀ s -
      (affineBellman P T term stepCost)^[numLevels P T * t] l₀ s| ≤
      (1 - (minPosProb P) ^ i) * (1 - (minPosProb P) ^ numLevels P T) ^ (t - 1) * C := by
  set k := numLevels P T
  set δ := minPosProb P
  have hδ0 : 0 ≤ δ := (minPosProb_pos P).le
  have hδ1 : δ ≤ 1 := minPosProb_le_one P
  by_cases hk0 : k = 0
  · have hi0 : i = 0 := by have := levelIndex_le_numLevels P T s; omega
    subst hi0
    have hsT : s ∈ T := (levelIndex_eq_zero_iff_of_allReachSet hreach s).mp hi
    simp [hk0, hT_eq s hsT]
  · have hkt_pos : 1 ≤ k * t := Nat.mul_pos (Nat.pos_of_ne_zero hk0) ht
    have hdiff := affineBellman_iterate_sub P T term stepCost (k * t - 1) u₀ l₀
    rw [show k * t - 1 + 1 = k * t by omega] at hdiff
    have habs0 : ∀ x, |(u₀ - l₀) x| ≤ C * survivalSet P T 0 x := fun x ↦ by
      by_cases hx : x ∈ T <;> simp [survivalSet, hx, hT_eq x, hbound x]
    have hk_all : ∀ x, survivalSet P T k x ≤ 1 - δ ^ k := fun x ↦ by
      have hx_le := levelIndex_le_numLevels P T x
      have h1 := (survivalSet_antitone P T x hx_le).trans
        (survivalSet_le_one_sub_pow_levelIndex hreach (s := x) rfl)
      linarith [pow_le_pow_of_le_one hδ0 hδ1 hx_le]
    have hgeom : ∀ m : ℕ, ∀ x, survivalSet P T (k * m) x ≤ (1 - δ ^ k) ^ m := fun m ↦ by
      induction m with
      | zero => exact fun x ↦ by simpa using survivalSet_le_one P T 0 x
      | succ m ih =>
        intro x; rw [Nat.mul_succ]
        have hm_le : ∀ y, survivalSet P T k y ≤ (1 - δ ^ k) * survivalSet P T 0 y := fun y ↦ by
          by_cases hy : y ∈ T
          · simp [survivalSet_of_mem P hy]
          · simpa [survivalSet, hy] using hk_all y
        have hiter := subStep_iterate_mono (P := P) (T := T) (k * m) hm_le x
        rw [subStep_iterate_smul] at hiter
        have hadd : survivalSet P T (k * m + k) x ≤ (1 - δ ^ k) * survivalSet P T (k * m) x := by
          simpa [survivalSet, Function.iterate_add_apply] using hiter
        exact hadd.trans ((mul_le_mul_of_nonneg_left (ih x)
          (sub_nonneg.mpr (pow_le_one₀ hδ0 hδ1))).trans_eq (pow_succ' _ _).symm)
    have hbase : ∀ x, survivalSet P T (k * (t - 1)) x ≤
        (1 - δ ^ k) ^ (t - 1) * survivalSet P T 0 x := fun x ↦ by
      by_cases hx : x ∈ T
      · simp [survivalSet_of_mem P hx]
      · simpa [survivalSet, hx] using hgeom (t - 1) x
    have hiter := subStep_iterate_mono (P := P) (T := T) k hbase s
    rw [subStep_iterate_smul] at hiter
    have hkt : k + k * (t - 1) = k * t := by
      rw [Nat.add_comm, ← Nat.mul_succ]
      exact congrArg (k * ·) (Nat.sub_add_cancel ht)
    have hsurv_kt : survivalSet P T (k * t) s ≤ (1 - δ ^ k) ^ (t - 1) * survivalSet P T k s := by
      simpa [survivalSet, ← Function.iterate_add_apply, hkt] using hiter
    have hik : i ≤ k := hi ▸ levelIndex_le_numLevels P T s
    have hsi : survivalSet P T k s ≤ 1 - δ ^ i :=
      (survivalSet_antitone P T s hik).trans (survivalSet_le_one_sub_pow_levelIndex hreach hi)
    have hpow_nn : 0 ≤ (1 - δ ^ k) ^ (t - 1) := pow_nonneg (sub_nonneg.mpr (pow_le_one₀ hδ0 hδ1)) _
    calc |(affineBellman P T term stepCost)^[k * t] u₀ s -
            (affineBellman P T term stepCost)^[k * t] l₀ s|
        = |(subStep P T)^[k * t] (u₀ - l₀) s| := congrArg (fun f : S → ℝ ↦ |f s|) hdiff
      _ ≤ (subStep P T)^[k * t] (fun x ↦ |(u₀ - l₀) x|) s :=
          abs_subStep_iterate_le P T (k * t) (u₀ - l₀) s
      _ ≤ C * survivalSet P T (k * t) s := by
          have := subStep_iterate_mono (P := P) (T := T) (k * t) habs0 s
          rwa [subStep_iterate_smul] at this
      _ ≤ C * ((1 - δ ^ k) ^ (t - 1) * (1 - δ ^ i)) :=
          mul_le_mul_of_nonneg_left (hsurv_kt.trans (mul_le_mul_of_nonneg_left hsi hpow_nn)) hC
      _ = (1 - δ ^ i) * (1 - δ ^ k) ^ (t - 1) * C := by ring

theorem contractingWith_affineBellman_iterate {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) :
    ContractingWith
      ⟨1 - (minPosProb P) ^ Fintype.card S,
        sub_nonneg.mpr (pow_le_one₀ (minPosProb_pos P).le (minPosProb_le_one P))⟩
      ((affineBellman P T term stepCost)^[Fintype.card S + 1]) := by
  set δ := minPosProb P
  set N := Fintype.card S
  have hδ0 : 0 < δ := minPosProb_pos P
  have hδ1 : δ ≤ 1 := minPosProb_le_one P
  refine ⟨?_, lipschitzWith_iff_dist_le_mul.mpr fun u v ↦ ?_⟩
  · change 1 - δ ^ N < 1
    linarith [pow_pos hδ0 N]
  · rw [dist_eq_norm, dist_eq_norm]
    change ‖(affineBellman P T term stepCost)^[N + 1] u -
        (affineBellman P T term stepCost)^[N + 1] v‖ ≤ (1 - δ ^ N) * ‖u - v‖
    rw [pi_norm_le_iff_of_nonneg
      (mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hδ0.le hδ1)) (norm_nonneg _))]
    intro s
    rw [Pi.sub_apply, Real.norm_eq_abs,
      show (affineBellman P T term stepCost)^[N + 1] u s -
          (affineBellman P T term stepCost)^[N + 1] v s =
        (subStep P T)^[N + 1] (u - v) s from
        congrFun (affineBellman_iterate_sub P T term stepCost N u v) s]
    have hstep1 : ∀ x, |subStep P T (u - v) x| ≤ ‖u - v‖ * survivalSet P T 0 x := fun x ↦ by
      by_cases hx : x ∈ T
      · simp [subStep, survivalSet, hx]
      · simp [subStep, survivalSet, hx, abs_expectStep_le_norm]
    have hiter : |(subStep P T)^[N + 1] (u - v) s| ≤ ‖u - v‖ * survivalSet P T N s := by
      rw [Function.iterate_succ_apply]
      exact (abs_subStep_iterate_le P T N _ s).trans
        ((subStep_iterate_mono N hstep1 s).trans_eq (by rw [subStep_iterate_smul]; rfl))
    have hi_le : levelIndex P T s ≤ N := levelIndex_le_card P T s
    have hsurv : survivalSet P T N s ≤ 1 - δ ^ N := by
      have h1 := (survivalSet_antitone P T s hi_le).trans
        (survivalSet_le_one_sub_pow_levelIndex hreach (s := s) rfl)
      have hpow : δ ^ N ≤ δ ^ levelIndex P T s := pow_le_pow_of_le_one hδ0.le hδ1 hi_le
      linarith
    exact hiter.trans (by nlinarith [norm_nonneg (u - v)])

/-- Unique Bellman fixed-point value vector `affineBellmanVal`. -/
def affineBellmanVal (P : Cslib.Probability.MarkovChain S) (T : Set S) (term stepCost : S → ℝ) :
    S → ℝ := by
  classical
  exact if h : AllReachSet P T then
    (contractingWith_affineBellman_iterate h term stepCost).fixedPoint
      ((affineBellman P T term stepCost)^[Fintype.card S + 1])
  else 0

/-- Weighted reachability value vector `reachVal P T w`. -/
def reachVal (P : Cslib.Probability.MarkovChain S) (T : Set S) (w : S → ℝ) : S → ℝ :=
  affineBellmanVal P T w 0

/-- Stochastic shortest path value vector `sspVal P T w`. -/
def sspVal (P : Cslib.Probability.MarkovChain S) (T : Set S) (w : S → ℝ) : S → ℝ :=
  affineBellmanVal P T w w

theorem affineBellmanVal_isFixedPt {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) :
    Function.IsFixedPt (affineBellman P T term stepCost)
      (affineBellmanVal P T term stepCost) := by
  classical
  simp only [affineBellmanVal, hreach, ↓reduceDIte]
  exact (contractingWith_affineBellman_iterate hreach term stepCost).isFixedPt_fixedPoint_iterate

theorem affineBellman_fixedPt_unique {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) {term stepCost v : S → ℝ}
    (hv : affineBellman P T term stepCost v = v) :
    v = affineBellmanVal P T term stepCost := by
  classical
  simp only [affineBellmanVal, hreach, ↓reduceDIte]
  exact (contractingWith_affineBellman_iterate hreach term stepCost).fixedPoint_unique
    (Function.IsFixedPt.iterate hv (Fintype.card S + 1))

theorem tendsto_iterate_affineBellman {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost v₀ : S → ℝ) :
    Tendsto (fun n ↦ (affineBellman P T term stepCost)^[n] v₀) atTop
      (𝓝 (affineBellmanVal P T term stepCost)) := by
  set f := affineBellman P T term stepCost
  set vStar := affineBellmanVal P T term stepCost
  set N := Fintype.card S + 1
  have hsub : ∀ r < N, Tendsto (fun q ↦ f^[N * q + r] v₀) atTop (𝓝 vStar) := fun r _ ↦ by
    have h1 : (fun q ↦ f^[N * q + r] v₀) = fun q ↦ (f^[N])^[q] (f^[r] v₀) := by
      ext q; rw [Function.iterate_add_apply, Function.iterate_mul]
    rw [h1]
    classical
    simp only [vStar, affineBellmanVal, hreach, ↓reduceDIte]
    exact (contractingWith_affineBellman_iterate hreach term stepCost).tendsto_iterate_fixedPoint _
  rw [Metric.tendsto_atTop]
  intro ε hε
  choose M hM using fun r : Fin N ↦ (Metric.tendsto_atTop.mp (hsub r.1 r.2)) ε hε
  refine ⟨(Finset.univ.sup M + 1) * N, fun n hn ↦ ?_⟩
  have hN_pos : 0 < N := Nat.succ_pos _
  let r : Fin N := ⟨n % N, Nat.mod_lt n hN_pos⟩
  have hq : M r ≤ n / N := by
    have hmul : (Finset.univ.sup M + 1) * N ≤ (n / N + 1) * N := by
      have := Nat.div_add_mod n N; have := Nat.mod_lt n hN_pos; nlinarith
    exact (Finset.le_sup (Finset.mem_univ r)).trans
      (by have := Nat.le_of_mul_le_mul_right hmul hN_pos; omega)
  have hdiv : N * (n / N) + r.1 = n := Nat.div_add_mod n N
  simpa [r, hdiv] using hM r (n / N) hq

/-- Probability `hitBeforeProb P T s x` of hitting `s` before `T` starting from `x`. -/
def hitBeforeProb (P : Cslib.Probability.MarkovChain S) (T : Set S) (s : S) : S → ℝ :=
  reachVal (reduceChain P s) (insert s T) fun x ↦ @ite _ (x = s) (Classical.propDecidable _) 1 0

private theorem hitBeforeProb_bounds {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (s x : S) :
    0 ≤ hitBeforeProb P T s x ∧ hitBeforeProb P T s x ≤ 1 := by
  have hQ := hreach.insert_reduceChain s
  let w1 := fun z ↦ @ite _ (z = s) (Classical.propDecidable _) (1 : ℝ) 0
  have ht0 := (tendsto_pi_nhds.mp (tendsto_iterate_affineBellman hQ w1 0 0)) x
  have ht1 := (tendsto_pi_nhds.mp (tendsto_iterate_affineBellman hQ w1 0 (fun _ ↦ 1))) x
  have h0 : ∀ n y, 0 ≤ (affineBellman (reduceChain P s) (insert s T) w1 0)^[n] 0 y := fun n ↦ by
    induction n with
    | zero => exact fun _ ↦ le_rfl
    | succ k ih =>
      intro y; rw [Function.iterate_succ_apply']
      by_cases hy : y ∈ insert s T
      · by_cases hys : y = s <;> simp [affineBellman, hy, w1, hys]
      · simpa [affineBellman, hy] using expectStep_mono ih y
  have h1 : ∀ n y, (affineBellman (reduceChain P s) (insert s T) w1 0)^[n] (fun _ ↦ 1) y ≤ 1 :=
    fun n ↦ by
      induction n with
      | zero => exact fun _ ↦ le_rfl
      | succ k ih =>
        intro y; rw [Function.iterate_succ_apply']
        by_cases hy : y ∈ insert s T
        · by_cases hys : y = s <;> simp [affineBellman, hy, w1, hys]
        · simp only [affineBellman, ite_eq_right hy, Pi.zero_apply, zero_add]
          exact (expectStep_mono ih y).trans_eq (expectStep_const _ 1 y)
  exact ⟨ge_of_tendsto ht0 (Eventually.of_forall fun n ↦ h0 n x),
    le_of_tendsto ht1 (Eventually.of_forall fun n ↦ h1 n x)⟩

theorem affineBellmanVal_insert_eq {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) {s : S} (hs : s ∉ T) (γ : ℝ) (x : S) :
    affineBellmanVal (reduceChain P s) (insert s T)
        (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost x =
      affineBellmanVal P T term stepCost x +
        (γ - affineBellmanVal P T term stepCost s) * hitBeforeProb P T s x := by
  set v := affineBellmanVal P T term stepCost
  set p := hitBeforeProb P T s
  set g : S → ℝ := fun y ↦ v y + (γ - v s) * p y
  have hQ_reach : AllReachSet (reduceChain P s) (insert s T) := hreach.insert_reduceChain s
  have hv_fix := affineBellmanVal_isFixedPt hreach term stepCost
  have hp_fix := affineBellmanVal_isFixedPt hQ_reach
    (fun z ↦ @ite _ (z = s) (Classical.propDecidable _) (1 : ℝ) 0) 0
  suffices hg : g = affineBellmanVal (reduceChain P s) (insert s T)
      (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost from
    (congrFun hg x).symm
  refine affineBellman_fixedPt_unique hQ_reach (funext fun y ↦ ?_)
  by_cases hys : y = s
  · subst hys
    have hp_self : p y = 1 := by
      have := congrFun hp_fix y; simpa [p, hitBeforeProb, reachVal, affineBellman] using this.symm
    simp [affineBellman, g, hp_self]
  · by_cases hyT : y ∈ T
    · have hy_ins : y ∈ insert s T := Set.mem_insert_of_mem s hyT
      have hp_T : p y = 0 := by
        have := congrFun hp_fix y
        simpa [p, hitBeforeProb, reachVal, affineBellman, hy_ins, hys] using this.symm
      have hv_T : v y = term y := by
        have := congrFun hv_fix y; simpa [v, affineBellman, hyT] using this.symm
      simp [affineBellman, g, hy_ins, hys, hp_T, hv_T]
    · have hy_nins : y ∉ insert s T := fun h ↦ h.elim hys hyT
      have hexp_eq : ∀ f : S → ℝ, expectStep (reduceChain P s) f y = expectStep P f y :=
        fun f ↦ by simp [expectStep, reduceChain_of_ne P hys]
      have hv_step : v y = stepCost y + expectStep P v y := by
        have := congrFun hv_fix y; simpa [v, affineBellman, hyT] using this.symm
      have hp_step : p y = expectStep P p y := by
        have := congrFun hp_fix y
        simpa [p, hitBeforeProb, reachVal, affineBellman, hy_nins, hexp_eq] using this.symm
      simp only [affineBellman, ite_eq_right hy_nins, hexp_eq]
      change stepCost y + expectStep P (v + fun z ↦ (γ - v s) * p z) y = v y + (γ - v s) * p y
      rw [expectStep_add, expectStep_smul, ← hp_step]
      linarith

private theorem pow_card_le_one_sub_returnProb {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) {s : S} (hs : s ∉ T) :
    (minPosProb P) ^ Fintype.card S ≤ 1 - expectStep P (hitBeforeProb P T s) s := by
  classical
  set p := hitBeforeProb P T s
  set δ := minPosProb P
  have hQ_reach : AllReachSet (reduceChain P s) (insert s T) := hreach.insert_reduceChain s
  have hp_fix := affineBellmanVal_isFixedPt hQ_reach
    (fun z ↦ @ite _ (z = s) (Classical.propDecidable _) (1 : ℝ) 0) 0
  have hp_lt_lvl : ∀ j : ℕ, j < levelIndex P T s →
      ∀ y : S, levelIndex P T y = j → δ ^ j ≤ 1 - p y := by
    intro j
    induction j with
    | zero =>
      intro _ y hy0
      have hyT : y ∈ T := (levelIndex_eq_zero_iff_of_allReachSet hreach y).mp hy0
      have hys : y ≠ s := fun h ↦ hs (h ▸ hyT)
      have hp0 : p y = 0 := by
        have := congrFun hp_fix y
        simpa [p, hitBeforeProb, reachVal, affineBellman, Set.mem_insert_of_mem s hyT, hys] using
          this.symm
      simp [hp0]
    | succ m ih =>
      intro hm_lt y hym
      have hys : y ≠ s := fun h ↦ by rw [h] at hym; omega
      have hyT : y ∉ T := fun hyT ↦ by
        have := (levelIndex_eq_zero_iff_of_allReachSet hreach y).mpr hyT; omega
      have hy_nins : y ∉ insert s T := fun h ↦ h.elim hys hyT
      obtain ⟨yStar, hstep, hyStar_lvl⟩ := levelIndex_step_pred hym
      have hih_star : δ ^ m ≤ 1 - p yStar := ih (by omega) yStar hyStar_lvl
      have hp_eq : p y = expectStep P p y := by
        have := congrFun hp_fix y
        simpa [p, hitBeforeProb, reachVal, affineBellman, hy_nins, expectStep,
          reduceChain_of_ne P hys] using this.symm
      have h1sub : 1 - p y = expectStep P (fun z ↦ 1 - p z) y := by
        have hsub : expectStep P (fun z ↦ 1 - p z) y =
            expectStep P (fun _ ↦ 1) y - expectStep P p y :=
          expectStep_sub P (fun _ ↦ 1) p y
        rw [expectStep_const, ← hp_eq] at hsub
        exact hsub.symm
      rw [h1sub, expectStep, ← Finset.add_sum_erase _ _ (Finset.mem_univ yStar)]
      have hrest_nn : 0 ≤ ∑ z ∈ Finset.univ.erase yStar, (P y z).toReal * (1 - p z) :=
        Finset.sum_nonneg fun z _ ↦
          mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hitBeforeProb_bounds hreach s z).2)
      have hstar_ge : δ ^ (m + 1) ≤ (P y yStar).toReal * (1 - p yStar) := by
        rw [pow_succ']
        exact mul_le_mul (minPosProb_le_toReal hstep) hih_star
          (pow_nonneg (minPosProb_pos P).le m) ENNReal.toReal_nonneg
      linarith
  have hs_pos : 1 ≤ levelIndex P T s := by
    by_contra! h0
    exact hs ((levelIndex_eq_zero_iff_of_allReachSet hreach s).mp (by omega))
  obtain ⟨sStar, hstep, hsStar_lvl⟩ :=
    levelIndex_step_pred (P := P) (T := T) (s := s) (i := levelIndex P T s - 1) (by omega)
  have hstar_bound := hp_lt_lvl (levelIndex P T s - 1) (by omega) sStar hsStar_lvl
  have h1sub : 1 - expectStep P p s = expectStep P (fun z ↦ 1 - p z) s := by
    have hsub : expectStep P (fun z ↦ 1 - p z) s =
        expectStep P (fun _ ↦ 1) s - expectStep P p s :=
      expectStep_sub P (fun _ ↦ 1) p s
    rw [expectStep_const] at hsub
    exact hsub.symm
  have hret_ge : δ ^ levelIndex P T s ≤ 1 - expectStep P p s := by
    rw [h1sub, expectStep, ← Finset.add_sum_erase _ _ (Finset.mem_univ sStar)]
    have hrest_nn : 0 ≤ ∑ z ∈ Finset.univ.erase sStar, (P s z).toReal * (1 - p z) :=
      Finset.sum_nonneg fun z _ ↦
        mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hitBeforeProb_bounds hreach s z).2)
    have hstar_ge : δ ^ levelIndex P T s ≤ (P s sStar).toReal * (1 - p sStar) := by
      rw [show levelIndex P T s = (levelIndex P T s - 1) + 1 by omega, pow_succ']
      exact mul_le_mul (minPosProb_le_toReal hstep) hstar_bound
        (pow_nonneg (minPosProb_pos P).le _) ENNReal.toReal_nonneg
    linarith
  exact (pow_le_pow_of_le_one (minPosProb_pos P).le (minPosProb_le_one P)
    (levelIndex_le_card P T s)).trans hret_ge

private theorem affineBellman_insert_sub_eq {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) {s : S} (hs : s ∉ T) (γ : ℝ) :
    affineBellman P T term stepCost
        (affineBellmanVal (reduceChain P s) (insert s T)
          (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost) s - γ =
      (affineBellmanVal P T term stepCost s - γ) *
        (1 - expectStep P (hitBeforeProb P T s) s) := by
  simp only [affineBellman, ite_eq_right hs]
  have hfun : affineBellmanVal (reduceChain P s) (insert s T)
      (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost =
      affineBellmanVal P T term stepCost +
        fun x ↦ (γ - affineBellmanVal P T term stepCost s) * hitBeforeProb P T s x :=
    funext (affineBellmanVal_insert_eq hreach term stepCost hs γ)
  rw [hfun, expectStep_add, expectStep_smul]
  have hv_step := congrFun (affineBellmanVal_isFixedPt hreach term stepCost) s
  simp only [affineBellman, ite_eq_right hs] at hv_step
  linarith

theorem gt_iff_affineBellman_insert_gt {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) (s : S) (γ : ℝ) :
    affineBellman P T term stepCost
        (affineBellmanVal (reduceChain P s) (insert s T)
          (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost) s > γ ↔
      affineBellmanVal P T term stepCost s > γ := by
  by_cases hs : s ∈ T
  · have hv := congrFun (affineBellmanVal_isFixedPt hreach term stepCost) s
    simp only [affineBellman, ite_eq_left hs] at hv ⊢
    rw [hv]
  · have hpos : 0 < 1 - expectStep P (hitBeforeProb P T s) s :=
      (pow_pos (minPosProb_pos P) (Fintype.card S)).trans_le
        (pow_card_le_one_sub_returnProb hreach hs)
    have hid := affineBellman_insert_sub_eq hreach term stepCost hs γ
    constructor <;> intro h
    · exact sub_pos.mp (pos_of_mul_pos_left (by linarith) hpos.le)
    · linarith [mul_pos (sub_pos.mpr h) hpos]

theorem lt_iff_affineBellman_insert_lt {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) (s : S) (γ : ℝ) :
    affineBellman P T term stepCost
        (affineBellmanVal (reduceChain P s) (insert s T)
          (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost) s < γ ↔
      affineBellmanVal P T term stepCost s < γ := by
  by_cases hs : s ∈ T
  · have hv := congrFun (affineBellmanVal_isFixedPt hreach term stepCost) s
    simp only [affineBellman, ite_eq_left hs] at hv ⊢
    rw [hv]
  · have hpos : 0 < 1 - expectStep P (hitBeforeProb P T s) s :=
      (pow_pos (minPosProb_pos P) (Fintype.card S)).trans_le
        (pow_card_le_one_sub_returnProb hreach hs)
    have hid := affineBellman_insert_sub_eq hreach term stepCost hs γ
    constructor <;> intro h
    · by_contra! hge; linarith [mul_nonneg (sub_nonneg.mpr hge) hpos.le]
    · linarith [mul_neg_of_neg_of_pos (sub_neg.mpr h) hpos]

theorem affineBellman_encompassing_lower {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) (s : S) (γ : ℝ) {f : S → ℝ}
    (hf : ∀ x, f x ≤ affineBellmanVal (reduceChain P s) (insert s T)
      (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost x)
    {ε : ℝ} (hε : 0 < ε)
    (hgt : affineBellman P T term stepCost f s + (minPosProb P) ^ Fintype.card S * ε > γ) :
    affineBellmanVal P T term stepCost s > γ - ε := by
  have hmono := affineBellman_mono (P := P) (T := T) (term := term) (stepCost := stepCost) hf s
  by_cases hs : s ∈ T
  · have hv := congrFun (affineBellmanVal_isFixedPt hreach term stepCost) s
    simp only [affineBellman, ite_eq_left hs] at hv hgt
    rw [← hv]
    nlinarith [pow_le_one₀ (minPosProb_pos P).le (minPosProb_le_one P) (n := Fintype.card S)]
  · have hret := pow_card_le_one_sub_returnProb hreach hs
    have hid := affineBellman_insert_sub_eq hreach term stepCost hs γ
    have hpow_pos : 0 < (minPosProb P) ^ Fintype.card S := pow_pos (minPosProb_pos P) _
    by_cases hval : γ ≤ affineBellmanVal P T term stepCost s
    · linarith
    · push Not at hval
      have h1 := mul_le_mul_of_nonneg_left hret (by linarith : 0 ≤
        γ - affineBellmanVal P T term stepCost s)
      nlinarith

theorem affineBellman_encompassing_upper {P : Cslib.Probability.MarkovChain S} {T : Set S}
    (hreach : AllReachSet P T) (term stepCost : S → ℝ) (s : S) (γ : ℝ) {u : S → ℝ}
    (hu : ∀ x, affineBellmanVal (reduceChain P s) (insert s T)
      (fun y ↦ @ite _ (y = s) (Classical.propDecidable _) γ (term y)) stepCost x ≤ u x)
    {ε : ℝ} (hε : 0 < ε)
    (hlt : affineBellman P T term stepCost u s - (minPosProb P) ^ Fintype.card S * ε < γ) :
    affineBellmanVal P T term stepCost s < γ + ε := by
  have hmono := affineBellman_mono (P := P) (T := T) (term := term) (stepCost := stepCost) hu s
  by_cases hs : s ∈ T
  · have hv := congrFun (affineBellmanVal_isFixedPt hreach term stepCost) s
    simp only [affineBellman, ite_eq_left hs] at hv hlt
    rw [← hv]
    nlinarith [pow_le_one₀ (minPosProb_pos P).le (minPosProb_le_one P) (n := Fintype.card S)]
  · have hret := pow_card_le_one_sub_returnProb hreach hs
    have hid := affineBellman_insert_sub_eq hreach term stepCost hs γ
    have hpow_pos : 0 < (minPosProb P) ^ Fintype.card S := pow_pos (minPosProb_pos P) _
    by_cases hval : affineBellmanVal P T term stepCost s ≤ γ
    · linarith
    · push Not at hval
      have h1 := mul_le_mul_of_nonneg_left hret (by linarith : 0 ≤
        affineBellmanVal P T term stepCost s - γ)
      nlinarith

end BellmanAndGuessing

end CslibFrontier.Probability.MarkovChain
