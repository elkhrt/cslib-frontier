/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Simplex.Dantzig
public import CslibFrontier.Algorithms.Lean.Simplex.LinearProgram
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Equivalence of Finite Absorbing MDP Policy Iteration and the Simplex Method

This module formalizes finite absorbing Markov Decision Processes (MDPs) over a linearly ordered
field and proves the classical correspondence between proper positional policies and basic feasible
dictionaries of the primal occupation-measure Linear Program, using the simplex dictionaries and
Bland / Dantzig pivoting rules of
`CslibFrontier.Algorithms.Lean.Simplex`.

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.FiniteMDP`: a finite absorbing MDP with designated sink states.
* `Cslib.Algorithms.Lean.Simplex.FiniteMDP.IsProper`: proper positional policy criterion.
* `Cslib.Algorithms.Lean.Simplex.FiniteMDP.val`,
  `Cslib.Algorithms.Lean.Simplex.FiniteMDP.appeal`,
  `Cslib.Algorithms.Lean.Simplex.FiniteMDP.Switchable`,
  `Cslib.Algorithms.Lean.Simplex.FiniteMDP.IsLocallyOptimal`: policy evaluation and improvement.
* `Cslib.Algorithms.Lean.Simplex.mdpMatrix`, `Cslib.Algorithms.Lean.Simplex.mdpRhs`,
  `Cslib.Algorithms.Lean.Simplex.mdpObj`: primal occupation-measure LP `(J - P)ᵀ x = e`, `x ≥ 0`,
  `max cᵀ x`.
* `Cslib.Algorithms.Lean.Simplex.policyDictionary`: simplex dictionary for a proper policy `π`.

## Main results

* `Cslib.Algorithms.Lean.Simplex.policyDictionary_feasible`: `policyDictionary M π` is feasible
  (with every basic `rhs ≥ 1`).
* `Cslib.Algorithms.Lean.Simplex.policyDictionary_represents`: `policyDictionary M π` represents
  the primal occupation-measure LP.
* `Cslib.Algorithms.Lean.Simplex.policyDictionary_pivot_spec`: single-state policy switching is
  the unique minimum-ratio pivot of `policyDictionary M π` and yields
  `policyDictionary M (Function.update π s a)`.
* `Cslib.Algorithms.Lean.Simplex.blandStep_policyDictionary`: Bland's rule on
  `policyDictionary M π` chooses the smallest improving `(s, a)` and pivots to the updated policy.
* `Cslib.Algorithms.Lean.Simplex.dantzigStep_policyDictionary`: Dantzig's rule on
  `policyDictionary M π` chooses the `(s, a)` maximizing `appeal π s a - val π s` and pivots to
  the updated policy.
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

open Matrix

universe u v w

/-! ### Finite Absorbing Markov Decision Processes -/

/-- A finite Markov Decision Process with state space `S`, available action sets `A s`,
designated terminal sink states `sinks`, transition probabilities `prob`, and immediate rewards
`reward`. Sink states have zero outgoing probabilities and zero rewards. -/
@[ext]
structure FiniteMDP (S : Type u) (A : S → Type v) (K : Type w)
    [Fintype S] [Semiring K] [PartialOrder K] where
  /-- Designated terminal (sink) states with no outgoing transitions or rewards. -/
  sinks : Finset S
  /-- Transition probability `prob s a s'` of reaching `s'` from `s` under action `a`. -/
  prob : (s : S) → A s → S → K
  /-- Immediate reward `reward s a` obtained by taking action `a` at state `s`. -/
  reward : (s : S) → A s → K
  /-- Every transition probability is nonnegative. -/
  prob_nonneg : ∀ s a s', 0 ≤ prob s a s'
  /-- At every non-sink state, transition probabilities sum to `1`. -/
  prob_sum : ∀ s, s ∉ sinks → ∀ a, ∑ s', prob s a s' = 1
  /-- Sink states have no outgoing transitions. -/
  prob_sink : ∀ s, s ∈ sinks → ∀ a s', prob s a s' = 0
  /-- Sink states yield zero immediate reward. -/
  reward_sink : ∀ s, s ∈ sinks → ∀ a, reward s a = 0

namespace FiniteMDP

/-- A deterministic positional policy selects an action at every state. -/
abbrev Policy (S : Type u) (A : S → Type v) : Type (max u v) := (s : S) → A s

section Basic

variable {S : Type u} {A : S → Type v} {K : Type w}
  [Fintype S] [Semiring K] [PartialOrder K]

/-- The sub-stochastic transition matrix `P_π` induced by policy `π`, with zero rows on sinks. -/
def transitionMatrix (M : FiniteMDP S A K) (π : Policy S A) : Matrix S S K :=
  Matrix.of fun s s' ↦ M.prob s (π s) s'

/-- The immediate reward vector `r_π` induced by policy `π`, vanishing on sinks. -/
def rewardVec (M : FiniteMDP S A K) (π : Policy S A) : S → K :=
  fun s ↦ M.reward s (π s)

@[simp]
theorem transitionMatrix_apply (M : FiniteMDP S A K) (π : Policy S A) (s s' : S) :
    M.transitionMatrix π s s' = M.prob s (π s) s' := by rfl

@[simp]
theorem rewardVec_apply (M : FiniteMDP S A K) (π : Policy S A) (s : S) :
    M.rewardVec π s = M.reward s (π s) := by rfl

theorem transitionMatrix_nonneg (M : FiniteMDP S A K) (π : Policy S A) (s s' : S) :
    0 ≤ M.transitionMatrix π s s' :=
  M.prob_nonneg s (π s) s'

theorem transitionMatrix_sink (M : FiniteMDP S A K) (π : Policy S A) {s : S} (hs : s ∈ M.sinks)
    (s' : S) : M.transitionMatrix π s s' = 0 :=
  M.prob_sink s hs (π s) s'

/-- A policy `π` is **proper** if some finite power of its transition matrix has every row sum
strictly less than `1`. -/
def IsProper [DecidableEq S] (M : FiniteMDP S A K) (π : Policy S A) : Prop :=
  ∃ m : ℕ, ∀ s : S, ∑ s' : S, (M.transitionMatrix π ^ m) s s' < 1

end Basic

section OrderedField

variable {S : Type u} {A : S → Type v} {K : Type w}
  [Fintype S] [DecidableEq S] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem transitionMatrix_pow_nonneg (M : FiniteMDP S A K) (π : Policy S A) :
    ∀ (t : ℕ) (s s' : S), 0 ≤ (M.transitionMatrix π ^ t) s s'
  | 0, s, s' => by
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | t + 1, s, s' => by
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun u _ ↦
      mul_nonneg (M.transitionMatrix_nonneg π s u) (transitionMatrix_pow_nonneg M π t u s')

namespace IsProper

theorem mulVec_eq_zero_imp {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π)
    {v : S → K} (hv : (1 - M.transitionMatrix π) *ᵥ v = 0) : v = 0 := by
  obtain ⟨m, hm⟩ := hπ
  have hP : M.transitionMatrix π *ᵥ v = v := by
    have : v - M.transitionMatrix π *ᵥ v = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hv
    exact (sub_eq_zero.mp this).symm
  have hPm : ∀ t : ℕ, (M.transitionMatrix π ^ t) *ᵥ v = v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hP]
  by_contra hvne
  have hne : (Finset.univ : Finset S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hvne
    ext s
    exact absurd (Finset.mem_univ s) (h ▸ Finset.notMem_empty s)
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_max_image Finset.univ (fun s ↦ |v s|) hne
  have hpos : 0 < |v s₀| := by
    have : ∃ s, v s ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hvne (funext hall)
    obtain ⟨s, hs⟩ := this
    exact lt_of_lt_of_le (abs_pos.mpr hs) (hs₀ s (Finset.mem_univ s))
  have hle : |v s₀| ≤ (∑ s' : S, (M.transitionMatrix π ^ m) s₀ s') * |v s₀| := by
    calc |v s₀| = |((M.transitionMatrix π ^ m) *ᵥ v) s₀| := by rw [hPm m]
      _ = |∑ s' : S, (M.transitionMatrix π ^ m) s₀ s' * v s'| := rfl
      _ ≤ ∑ s' : S, |(M.transitionMatrix π ^ m) s₀ s' * v s'| := Finset.abs_sum_le_sum_abs ..
      _ = ∑ s' : S, (M.transitionMatrix π ^ m) s₀ s' * |v s'| := by
          refine Finset.sum_congr rfl fun s' _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (M.transitionMatrix_pow_nonneg π m s₀ s')]
      _ ≤ ∑ s' : S, (M.transitionMatrix π ^ m) s₀ s' * |v s₀| := by
          refine Finset.sum_le_sum fun s' _ ↦
            mul_le_mul_of_nonneg_left (hs₀ s' (Finset.mem_univ s'))
              (M.transitionMatrix_pow_nonneg π m s₀ s')
      _ = (∑ s' : S, (M.transitionMatrix π ^ m) s₀ s') * |v s₀| := (Finset.sum_mul ..).symm
  have hlt : (∑ s' : S, (M.transitionMatrix π ^ m) s₀ s') * |v s₀| < 1 * |v s₀| :=
    mul_lt_mul_of_pos_right (hm s₀) hpos
  linarith

theorem isUnit_one_sub {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π) :
    IsUnit (1 - M.transitionMatrix π) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hvne (hπ.mulVec_eq_zero_imp hv)

theorem mul_inv_one_sub {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π) :
    (1 - M.transitionMatrix π) * (1 - M.transitionMatrix π)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hπ.isUnit_one_sub)

theorem inv_one_sub_mul {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π) :
    (1 - M.transitionMatrix π)⁻¹ * (1 - M.transitionMatrix π) = 1 :=
  Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hπ.isUnit_one_sub)

theorem nonneg_of_one_sub_mulVec_nonneg {M : FiniteMDP S A K} {π : Policy S A}
    (hπ : M.IsProper π) {v : S → K} (hv : ∀ s, 0 ≤ ((1 - M.transitionMatrix π) *ᵥ v) s) :
    ∀ s, 0 ≤ v s := by
  obtain ⟨m, hm⟩ := hπ
  have hstep : ∀ s, 0 ≤ v s - (M.transitionMatrix π *ᵥ v) s := fun s ↦ by
    simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hv s
  have hiter : ∀ t : ℕ, ∀ s, (M.transitionMatrix π ^ t *ᵥ v) s ≤ v s := by
    intro t
    induction t with
    | zero => intro s; simp
    | succ t ih =>
      intro s
      have h1 : (M.transitionMatrix π ^ (t + 1) *ᵥ v) s =
          ∑ u, M.transitionMatrix π s u * (M.transitionMatrix π ^ t *ᵥ v) u := by
        rw [pow_succ', ← Matrix.mulVec_mulVec]; rfl
      rw [h1]
      have h2 : ∑ u, M.transitionMatrix π s u * (M.transitionMatrix π ^ t *ᵥ v) u ≤
          ∑ u, M.transitionMatrix π s u * v u :=
        Finset.sum_le_sum fun u _ ↦
          mul_le_mul_of_nonneg_left (ih u) (M.transitionMatrix_nonneg π s u)
      have h3 : (M.transitionMatrix π *ᵥ v) s = ∑ u, M.transitionMatrix π s u * v u := rfl
      linarith [hstep s]
  by_contra hneg
  push Not at hneg
  obtain ⟨s₁, hs₁⟩ := hneg
  have hne : (Finset.univ : Finset S).Nonempty := ⟨s₁, Finset.mem_univ s₁⟩
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image Finset.univ v hne
  have hv0 : v s₀ < 0 := lt_of_le_of_lt (hs₀ s₁ (Finset.mem_univ s₁)) hs₁
  have hge : (∑ s' : S, (M.transitionMatrix π ^ m) s₀ s') * v s₀ ≤
      (M.transitionMatrix π ^ m *ᵥ v) s₀ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun s' _ ↦
      mul_le_mul_of_nonneg_left (hs₀ s' (Finset.mem_univ s'))
        (M.transitionMatrix_pow_nonneg π m s₀ s')
  have hle : (M.transitionMatrix π ^ m *ᵥ v) s₀ ≤ v s₀ := hiter m s₀
  have hlt : v s₀ < (∑ s' : S, (M.transitionMatrix π ^ m) s₀ s') * v s₀ := by
    have := mul_lt_mul_of_neg_right (hm s₀) hv0
    simpa using this
  linarith

theorem inv_one_sub_nonneg {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π)
    (s s' : S) : 0 ≤ (1 - M.transitionMatrix π)⁻¹ s s' := by
  let v : S → K := fun u ↦ (1 - M.transitionMatrix π)⁻¹ u s'
  have hv : ∀ u, 0 ≤ ((1 - M.transitionMatrix π) *ᵥ v) u := by
    intro u
    have hmul : ((1 - M.transitionMatrix π) *ᵥ v) u =
        ((1 - M.transitionMatrix π) * (1 - M.transitionMatrix π)⁻¹) u s' := rfl
    rw [hmul, hπ.mul_inv_one_sub, Matrix.one_apply]
    split_ifs <;> norm_num
  exact hπ.nonneg_of_one_sub_mulVec_nonneg hv s

theorem one_le_inv_one_sub_diag {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π)
    (s : S) : 1 ≤ (1 - M.transitionMatrix π)⁻¹ s s := by
  have heq := congr_fun (congr_fun hπ.mul_inv_one_sub s) s
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.one_apply_eq] at heq
  have hnonneg : 0 ≤ (M.transitionMatrix π * (1 - M.transitionMatrix π)⁻¹) s s := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun u _ ↦
      mul_nonneg (M.transitionMatrix_nonneg π s u) (hπ.inv_one_sub_nonneg u s)
  linarith

theorem inv_one_sub_sink {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π)
    {s : S} (hs : s ∈ M.sinks) (s' : S) :
    (1 - M.transitionMatrix π)⁻¹ s s' = if s = s' then 1 else 0 := by
  have heq := congr_fun (congr_fun hπ.mul_inv_one_sub s) s'
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.one_apply] at heq
  have hzero : (M.transitionMatrix π * (1 - M.transitionMatrix π)⁻¹) s s' = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun u _ ↦ by rw [M.transitionMatrix_sink π hs, zero_mul]
  linarith

end IsProper

/-- Total-reward value vector of policy `π`: `val π = (1 - P_π)⁻¹ *ᵥ r_π`. -/
noncomputable def val (M : FiniteMDP S A K) (π : Policy S A) : S → K :=
  (1 - M.transitionMatrix π)⁻¹ *ᵥ M.rewardVec π

/-- Action appeal of taking action `a` at state `s` under policy `π`:
`appeal π s a = r(s, a) + ∑ s', p(s' | s, a) * val π s'`. -/
noncomputable def appeal (M : FiniteMDP S A K) (π : Policy S A) (s : S) (a : A s) : K :=
  M.reward s a + ∑ s' : S, M.prob s a s' * M.val π s'

/-- A state `s` is switchable under `π` if it is non-sink and admits an action with strictly
greater appeal than `val π s`. -/
def Switchable (M : FiniteMDP S A K) (π : Policy S A) (s : S) : Prop :=
  s ∉ M.sinks ∧ ∃ a : A s, M.val π s < M.appeal π s a

/-- A policy `π` is locally optimal if no state is switchable. -/
def IsLocallyOptimal (M : FiniteMDP S A K) (π : Policy S A) : Prop :=
  ∀ s : S, ¬M.Switchable π s

omit [IsStrictOrderedRing K] in
theorem appeal_eq (M : FiniteMDP S A K) (π : Policy S A) (s : S) (a : A s) :
    M.appeal π s a = M.reward s a + ∑ s' : S, M.prob s a s' * M.val π s' := by rfl

omit [IsStrictOrderedRing K] in
theorem switchable_iff (M : FiniteMDP S A K) (π : Policy S A) (s : S) :
    M.Switchable π s ↔ s ∉ M.sinks ∧ ∃ a : A s, M.val π s < M.appeal π s a :=
  Iff.rfl

omit [IsStrictOrderedRing K] in
theorem isLocallyOptimal_iff (M : FiniteMDP S A K) (π : Policy S A) :
    M.IsLocallyOptimal π ↔ ∀ s : S, ¬M.Switchable π s :=
  Iff.rfl

theorem IsProper.val_eq_bellman {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π)
    (s : S) : M.val π s = M.reward s (π s) + ∑ s' : S, M.prob s (π s) s' * M.val π s' := by
  have hmul : (1 - M.transitionMatrix π) *ᵥ M.val π = M.rewardVec π := by
    rw [val, Matrix.mulVec_mulVec, hπ.mul_inv_one_sub, Matrix.one_mulVec]
  have hs := congr_fun hmul s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hs
  have hsum : (M.transitionMatrix π *ᵥ M.val π) s =
      ∑ s' : S, M.prob s (π s) s' * M.val π s' := rfl
  rw [hsum, rewardVec_apply] at hs
  linarith

theorem IsProper.val_sink {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π) {s : S}
    (hs : s ∈ M.sinks) : M.val π s = 0 := by
  rw [hπ.val_eq_bellman s, M.reward_sink s hs]
  simp [M.prob_sink s hs]

theorem IsProper.appeal_self {M : FiniteMDP S A K} {π : Policy S A} (hπ : M.IsProper π) (s : S) :
    M.appeal π s (π s) = M.val π s :=
  (hπ.val_eq_bellman s).symm

end OrderedField

end FiniteMDP

/-! ### Simplex Dictionary Uniqueness and Primal MDP LP Equivalence -/

section Uniqueness

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- A dictionary is normalized if all entries outside its basic/nonbasic index ranges are zero. -/
def DictionaryNormalized (D : Dictionary ι K) : Prop :=
  (∀ i, i ∉ D.basis → D.rhs i = 0) ∧
    (∀ i j, (i ∉ D.basis ∨ j ∈ D.basis) → D.coeff i j = 0) ∧
    (∀ j, j ∈ D.basis → D.objCoeff j = 0)

omit [Fintype ι] in
theorem dictionaryNormalized_pivot (D : Dictionary ι K) (r s : ι) :
    DictionaryNormalized (D.pivot r s) := by
  refine ⟨fun i hi ↦ ?_, fun i j hij ↦ ?_, fun j hj ↦ ?_⟩
  · rw [Dictionary.mem_pivot_basis] at hi
    push Not at hi
    simp only [Dictionary.pivot]
    split_ifs <;> simp_all
  · rcases hij with hi | hj
    · rw [Dictionary.mem_pivot_basis] at hi
      push Not at hi
      simp only [Dictionary.pivot]
      split_ifs <;> simp_all
    · rw [Dictionary.mem_pivot_basis] at hj
      simp only [Dictionary.pivot]
      split_ifs; simp_all
  · rw [Dictionary.mem_pivot_basis] at hj
    simp only [Dictionary.pivot]
    split_ifs; simp_all

/-- Two normalized dictionaries with the same basis representing the same LP are identical. -/
theorem dictionary_eq_of_represents {m : Type*} [Fintype m]
    {D₁ D₂ : Dictionary ι K} {A : Matrix m ι K} {b : m → K} {c : ι → K}
    (hB : D₁.basis = D₂.basis) (h₁ : D₁.Represents A b c) (h₂ : D₂.Represents A b c)
    (hn₁ : DictionaryNormalized D₁) (hn₂ : DictionaryNormalized D₂) : D₁ = D₂ := by
  have heq : D₁.Equivalent D₂ :=
    ⟨fun x ↦ (h₁.isSolution_iff x).trans (h₂.isSolution_iff x).symm,
     fun x hx ↦ (h₁.value_eq x ((h₁.isSolution_iff x).mp hx)).trans
       (h₂.value_eq x ((h₁.isSolution_iff x).mp hx)).symm⟩
  have hsol : D₁.basicSolution = D₂.basicSolution :=
    (D₂.eq_basicSolution_of_isSolution ((heq.isSolution_iff _).mp D₁.isSolution_basicSolution)
      (fun j hj ↦ D₁.basicSolution_of_notMem (hB ▸ hj)))
  have hrhs : D₁.rhs = D₂.rhs := by
    ext i
    by_cases hi : i ∈ D₁.basis
    · have h1 := D₁.basicSolution_of_mem hi
      have h2 := D₂.basicSolution_of_mem (hB ▸ hi)
      rw [hsol] at h1
      exact h1.symm.trans h2
    · rw [hn₁.1 i hi, hn₂.1 i (hB ▸ hi)]
  have hobjConst : D₁.objConst = D₂.objConst := by
    rw [← D₁.value_basicSolution, ← D₂.value_basicSolution, ← hsol]
    exact heq.value_eq _ D₁.isSolution_basicSolution
  have hray_sol : ∀ j, j ∉ D₁.basis → D₂.IsSolution (D₁.basicSolution + (1 : K) • D₁.ray j) :=
    fun j hj ↦ (heq.isSolution_iff _).mp
      (D₁.isSolution_add_smul_ray hj D₁.isSolution_basicSolution 1)
  have hcoeff : D₁.coeff = D₂.coeff := by
    ext i j
    by_cases hij : i ∉ D₁.basis ∨ j ∈ D₁.basis
    · rw [hn₁.2.1 i j hij, hn₂.2.1 i j (hB ▸ hij)]
    · push Not at hij
      obtain ⟨hi, hj⟩ := hij
      have hrow := hray_sol j hj i (hB ▸ hi)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul,
        D₁.basicSolution_of_mem hi, D₁.ray_of_mem hi hj] at hrow
      have hsum : ∑ k ∈ D₂.basisᶜ, D₂.coeff i k * (D₁.basicSolution k + D₁.ray j k) =
          D₂.coeff i j := by
        rw [Finset.sum_eq_single j]
        · rw [D₁.basicSolution_of_notMem hj, D₁.ray_self, zero_add, mul_one]
        · intro k hk hkj
          have hk1 : k ∉ D₁.basis := hB ▸ Finset.mem_compl.mp hk
          rw [D₁.basicSolution_of_notMem hk1, D₁.ray_of_notMem hk1 hkj, add_zero, mul_zero]
        · intro hmem
          exact absurd (Finset.mem_compl.mpr (hB ▸ hj)) hmem
      rw [hsum, ← hrhs] at hrow
      exact add_left_cancel hrow
  have hobjCoeff : D₁.objCoeff = D₂.objCoeff := by
    ext j
    by_cases hj : j ∈ D₁.basis
    · rw [hn₁.2.2 j hj, hn₂.2.2 j (hB ▸ hj)]
    · have hval := heq.value_eq _ (D₁.isSolution_add_smul_ray hj D₁.isSolution_basicSolution 1)
      rw [D₁.value_add_smul_ray hj, D₁.value_basicSolution, one_mul] at hval
      have hval2 : D₂.value (D₁.basicSolution + (1 : K) • D₁.ray j) =
          D₂.objConst + D₂.objCoeff j := by
        rw [Dictionary.value]
        congr 1
        rw [Finset.sum_eq_single j]
        · simp [D₁.basicSolution_of_notMem hj, D₁.ray_self]
        · intro k hk hkj
          have hk1 : k ∉ D₁.basis := hB ▸ Finset.mem_compl.mp hk
          simp [D₁.basicSolution_of_notMem hk1, D₁.ray_of_notMem hk1 hkj]
        · intro hmem
          exact absurd (Finset.mem_compl.mpr (hB ▸ hj)) hmem
      rw [hval2, hobjConst] at hval
      exact add_left_cancel hval
  ext
  · rw [hB]
  · rw [hrhs]
  · rw [hcoeff]
  · exact hobjConst
  · rw [hobjCoeff]

end Uniqueness

section MdpLP

variable {S : Type u} {A : S → Type v} {K : Type w}
  [Fintype S] [DecidableEq S] [∀ s, DecidableEq (A s)]
  [Field K] [LinearOrder K]

/-- The subtype of non-sink states of a finite MDP `M`. -/
abbrev NonSink (M : FiniteMDP S A K) : Type u := { s : S // s ∉ M.sinks }

/-- The state-action variables `Σ s : NonSink M, A s` of the primal MDP linear program. -/
abbrev ActionVar (M : FiniteMDP S A K) : Type (max u v) := Σ s : NonSink M, A s.1

/-- The constraint matrix `(J - P)ᵀ` of the primal occupation-measure LP of `M`. -/
def mdpMatrix (M : FiniteMDP S A K) : Matrix (NonSink M) (ActionVar M) K :=
  Matrix.of fun u x ↦ (if u = x.1 then 1 else 0) - M.prob x.1.1 x.2 u.1

/-- The all-ones right-hand side `e` of the primal occupation-measure LP. -/
def mdpRhs (M : FiniteMDP S A K) : NonSink M → K := fun _ ↦ 1

/-- The reward objective vector `c` of the primal occupation-measure LP. -/
def mdpObj (M : FiniteMDP S A K) : ActionVar M → K := fun x ↦ M.reward x.1.1 x.2

/-- The basis of `ActionVar M` corresponding to positional policy `π`. -/
def policyBasis (M : FiniteMDP S A K) (π : FiniteMDP.Policy S A) : Finset (ActionVar M) :=
  Finset.univ.image fun s : NonSink M ↦ ⟨s, π s.1⟩

@[simp]
theorem mem_policyBasis_iff {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A} {x : ActionVar M} :
    x ∈ policyBasis M π ↔ x.2 = π x.1.1 := by
  simp only [policyBasis, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, rfl⟩; rfl
  · intro h
    refine ⟨x.1, ?_⟩
    cases x
    simp_all

/-- The simplex dictionary corresponding to a proper positional policy `π`. -/
noncomputable def policyDictionary (M : FiniteMDP S A K) (π : FiniteMDP.Policy S A) :
    Dictionary (ActionVar M) K where
  basis := policyBasis M π
  rhs x :=
    if x.2 = π x.1.1 then ∑ v : NonSink M, (1 - M.transitionMatrix π)⁻¹ v.1 x.1.1 else 0
  coeff x y :=
    if x.2 = π x.1.1 ∧ y.2 ≠ π y.1.1 then
      (∑ w : NonSink M, (1 - M.transitionMatrix π)⁻¹ w.1 x.1.1 * M.prob y.1.1 y.2 w.1) -
        (1 - M.transitionMatrix π)⁻¹ y.1.1 x.1.1
    else 0
  objConst := ∑ s : NonSink M, M.val π s.1
  objCoeff y := if y.2 = π y.1.1 then 0 else M.appeal π y.1.1 y.2 - M.val π y.1.1

@[simp]
theorem policyDictionary_basis (M : FiniteMDP S A K) (π : FiniteMDP.Policy S A) :
    (policyDictionary M π).basis = policyBasis M π := by
  dsimp only [policyDictionary]

@[simp]
theorem policyDictionary_objConst (M : FiniteMDP S A K) (π : FiniteMDP.Policy S A) :
    (policyDictionary M π).objConst = ∑ s : NonSink M, M.val π s.1 := by
  dsimp only [policyDictionary]

@[simp]
theorem policyDictionary_rhs_of_notMem {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    {x : ActionVar M} (hx : x ∉ policyBasis M π) :
    (policyDictionary M π).rhs x = 0 := by
  dsimp only [policyDictionary]
  exact ite_eq_right (mt mem_policyBasis_iff.mpr hx)

@[simp]
theorem policyDictionary_objCoeff_of_mem {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    {y : ActionVar M} (hy : y ∈ policyBasis M π) :
    (policyDictionary M π).objCoeff y = 0 := by
  dsimp only [policyDictionary]
  exact ite_eq_left (mem_policyBasis_iff.mp hy)

@[simp]
theorem policyDictionary_objCoeff_of_notMem {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    {y : ActionVar M} (hy : y ∉ policyBasis M π) :
    (policyDictionary M π).objCoeff y = M.appeal π y.1.1 y.2 - M.val π y.1.1 := by
  dsimp only [policyDictionary]
  exact ite_eq_right (mt mem_policyBasis_iff.mpr hy)

theorem policyDictionary_normalized (M : FiniteMDP S A K) (π : FiniteMDP.Policy S A) :
    DictionaryNormalized (policyDictionary M π) := by
  refine ⟨fun i hi ↦ ?_, fun i j hij ↦ ?_, fun j hj ↦ ?_⟩
  · dsimp only [policyDictionary]
    exact ite_eq_right (mt mem_policyBasis_iff.mpr hi)
  · rcases hij with hi | hj
    · have hi' : i.2 ≠ π i.1.1 := mt mem_policyBasis_iff.mpr hi
      simp [policyDictionary, hi']
    · have hj' : j.2 = π j.1.1 := mem_policyBasis_iff.mp hj
      simp [policyDictionary, hj']
  · simp [policyDictionary, mem_policyBasis_iff.mp hj]

section OrderedMdpLP

variable [IsStrictOrderedRing K]

omit [∀ s, DecidableEq (A s)] [IsStrictOrderedRing K] in
private theorem sum_nonSink_eq_sum (M : FiniteMDP S A K) (f : S → K)
    (hf : ∀ s ∈ M.sinks, f s = 0) :
    ∑ w : NonSink M, f w.1 = ∑ w : S, f w := by
  have hsub : ∑ w : NonSink M, f w.1 = ∑ w ∈ Finset.univ.filter (· ∉ M.sinks), f w :=
    (Finset.sum_subtype (Finset.univ.filter (· ∉ M.sinks)) (p := (· ∉ M.sinks)) (by simp) f).symm
  rw [hsub]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun w _ hw ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
  exact hf w hw

omit [∀ s, DecidableEq (A s)] in
private theorem sum_nonSink_one_sub_mul_inv {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    (hπ : M.IsProper π) (u v : NonSink M) :
    ∑ w : NonSink M, (1 - M.transitionMatrix π) u.1 w.1 *
        (1 - M.transitionMatrix π)⁻¹ w.1 v.1 = if u = v then 1 else 0 := by
  have h := congr_fun (congr_fun hπ.mul_inv_one_sub u.1) v.1
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  have hsub : (if u = v then (1 : K) else 0) = if u.1 = v.1 then 1 else 0 := by
    simp [Subtype.ext_iff]
  rw [hsub, ← h]
  exact sum_nonSink_eq_sum M
    (fun w ↦ (1 - M.transitionMatrix π) u.1 w * (1 - M.transitionMatrix π)⁻¹ w v.1)
    fun w hw ↦ by
      have hne : w ≠ v.1 := fun heq ↦ v.2 (heq ▸ hw)
      rw [hπ.inv_one_sub_sink hw v.1, ite_eq_right hne, mul_zero]

omit [∀ s, DecidableEq (A s)] in
private theorem sum_nonSink_inv_mul_one_sub {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    (hπ : M.IsProper π) (u v : NonSink M) :
    ∑ w : NonSink M, (1 - M.transitionMatrix π)⁻¹ u.1 w.1 *
        (1 - M.transitionMatrix π) w.1 v.1 = if u = v then 1 else 0 := by
  have h := congr_fun (congr_fun hπ.inv_one_sub_mul u.1) v.1
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  have hsub : (if u = v then (1 : K) else 0) = if u.1 = v.1 then 1 else 0 := by
    simp [Subtype.ext_iff]
  rw [hsub, ← h]
  exact sum_nonSink_eq_sum M
    (fun w ↦ (1 - M.transitionMatrix π)⁻¹ u.1 w * (1 - M.transitionMatrix π) w v.1)
    fun w hw ↦ by
      have hne : w ≠ v.1 := fun heq ↦ v.2 (heq ▸ hw)
      simp only [Matrix.sub_apply, Matrix.one_apply, FiniteMDP.transitionMatrix_sink M π hw,
        sub_zero, ite_eq_right hne, mul_zero]

/-- Every basic variable of `policyDictionary M π` has `rhs ≥ 1 > 0`. -/
theorem one_le_policyDictionary_rhs {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    (hπ : M.IsProper π) {x : ActionVar M} (hx : x ∈ (policyDictionary M π).basis) :
    1 ≤ (policyDictionary M π).rhs x := by
  have hx' : x.2 = π x.1.1 := mem_policyBasis_iff.mp hx
  simp only [policyDictionary, hx', ↓reduceIte]
  calc (1 : K) ≤ (1 - M.transitionMatrix π)⁻¹ x.1.1 x.1.1 := hπ.one_le_inv_one_sub_diag x.1.1
    _ ≤ ∑ v : NonSink M, (1 - M.transitionMatrix π)⁻¹ v.1 x.1.1 :=
        Finset.single_le_sum (fun v _ ↦ hπ.inv_one_sub_nonneg v.1 x.1.1) (Finset.mem_univ x.1)

theorem policyDictionary_feasible {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    (hπ : M.IsProper π) : (policyDictionary M π).Feasible :=
  fun _ hx ↦ le_trans zero_le_one (one_le_policyDictionary_rhs hπ hx)

section FiniteActions

variable [∀ s, Fintype (A s)]

omit [IsStrictOrderedRing K] in
private theorem sum_actionVar_split (M : FiniteMDP S A K) (π : FiniteMDP.Policy S A)
    (f : ActionVar M → K) :
    ∑ x : ActionVar M, f x =
      (∑ s : NonSink M, f ⟨s, π s.1⟩) + ∑ y ∈ (policyBasis M π)ᶜ, f y := by
  rw [← Finset.sum_add_sum_compl (policyBasis M π) f]
  congr 1
  rw [policyBasis, Finset.sum_image]
  intro s _ t _ hst
  exact congr_arg Sigma.fst hst

/-- **`policyDictionary M π` represents the primal MDP linear program** `(J - P)ᵀ x = e`,
`max cᵀ x`. -/
theorem policyDictionary_represents {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    (hπ : M.IsProper π) :
    (policyDictionary M π).Represents (mdpMatrix M) (mdpRhs M) (mdpObj M) := by
  set Q := (1 - M.transitionMatrix π)⁻¹
  constructor
  · intro x
    constructor
    · intro hx
      ext u
      have hrow : ∀ s : NonSink M,
          x ⟨s, π s.1⟩ =
            (∑ v : NonSink M, Q v.1 s.1) +
            ∑ y ∈ (policyBasis M π)ᶜ,
              ((∑ w : NonSink M, Q w.1 s.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 s.1) * x y := by
        intro s
        have hs := hx ⟨s, π s.1⟩ (mem_policyBasis_iff.mpr rfl)
        simp only [policyDictionary, ↓reduceIte] at hs
        dsimp only [Q]
        rw [hs]
        congr 1
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        have hy' : y.2 ≠ π y.1.1 := mt mem_policyBasis_iff.mpr (Finset.mem_compl.mp hy)
        simp only [hy', ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      have hmul : (mdpMatrix M *ᵥ x) u =
          (∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 * x ⟨s, π s.1⟩) +
          ∑ y ∈ (policyBasis M π)ᶜ, mdpMatrix M u y * x y := by
        change ∑ y : ActionVar M, mdpMatrix M u y * x y = _
        rw [sum_actionVar_split]
        congr 1
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        simp only [mdpMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
          FiniteMDP.transitionMatrix_apply]
        have heq : (u = s) ↔ (s.1 = u.1) := by rw [Subtype.ext_iff]; exact eq_comm
        simp [heq]
      rw [hmul]
      simp_rw [hrow]
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have hterm1 : ∑ s : NonSink M, ∑ v : NonSink M,
          (1 - M.transitionMatrix π) s.1 u.1 * (Q v.1 s.1) = 1 := by
        rw [Finset.sum_comm]
        have hinner : ∀ v : NonSink M,
            ∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 * Q v.1 s.1 =
              if v = u then 1 else 0 := fun v ↦ by
          simpa [mul_comm] using sum_nonSink_inv_mul_one_sub hπ v u
        simp_rw [hinner]
        simp
      have hterm2 : ∀ y ∈ (policyBasis M π)ᶜ,
          (∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 *
            (((∑ w : NonSink M, Q w.1 s.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 s.1) * x y)) +
          mdpMatrix M u y * x y = 0 := by
        intro y _
        have hA : ∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 *
            ((∑ w : NonSink M, Q w.1 s.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 s.1) =
            M.prob y.1.1 y.2 u.1 - (if u = y.1 then 1 else 0) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          have h1 : ∑ s : NonSink M, ∑ w : NonSink M,
              (1 - M.transitionMatrix π) s.1 u.1 * (Q w.1 s.1 * M.prob y.1.1 y.2 w.1) =
              M.prob y.1.1 y.2 u.1 := by
            rw [Finset.sum_comm]
            have h1' : ∀ w : NonSink M, ∑ s : NonSink M,
                (1 - M.transitionMatrix π) s.1 u.1 * (Q w.1 s.1 * M.prob y.1.1 y.2 w.1) =
                (if w = u then 1 else 0) * M.prob y.1.1 y.2 w.1 := fun w ↦ by
              have := sum_nonSink_inv_mul_one_sub hπ w u
              calc ∑ s : NonSink M,
                    (1 - M.transitionMatrix π) s.1 u.1 * (Q w.1 s.1 * M.prob y.1.1 y.2 w.1)
                  = (∑ s : NonSink M, Q w.1 s.1 * (1 - M.transitionMatrix π) s.1 u.1) *
                      M.prob y.1.1 y.2 w.1 := by
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun s _ ↦ by ring
                _ = (if w = u then 1 else 0) * M.prob y.1.1 y.2 w.1 := by rw [this]
            simp_rw [h1']
            simp
          have h2 : ∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 * Q y.1.1 s.1 =
              if u = y.1 then 1 else 0 := by
            have := sum_nonSink_inv_mul_one_sub hπ y.1 u
            simpa [mul_comm, eq_comm] using this
          rw [h1, h2]
        have hfactor : ∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 *
            (((∑ w : NonSink M, Q w.1 s.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 s.1) * x y) =
            (∑ s : NonSink M, (1 - M.transitionMatrix π) s.1 u.1 *
              ((∑ w : NonSink M, Q w.1 s.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 s.1)) * x y := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ ↦ by ring
        rw [hfactor, hA]
        simp only [mdpMatrix, Matrix.of_apply]
        ring
      have hswap : (∑ s : NonSink M, ∑ y ∈ (policyBasis M π)ᶜ,
            (1 - M.transitionMatrix π) s.1 u.1 *
              (((∑ w : NonSink M, Q w.1 s.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 s.1) * x y)) +
          ∑ y ∈ (policyBasis M π)ᶜ, mdpMatrix M u y * x y = 0 := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero hterm2
      rw [hterm1, add_assoc, hswap, add_zero]
      rfl
    · intro hAx i hi
      have hi' : i.2 = π i.1.1 := mem_policyBasis_iff.mp hi
      have hsum_eq : ∑ u : NonSink M, Q u.1 i.1.1 * (mdpMatrix M *ᵥ x) u =
          ∑ u : NonSink M, Q u.1 i.1.1 * mdpRhs M u := by rw [hAx]
      have hLHS : ∑ u : NonSink M, Q u.1 i.1.1 * (mdpMatrix M *ᵥ x) u =
          x i - ∑ y ∈ (policyBasis M π)ᶜ,
            ((∑ w : NonSink M, Q w.1 i.1.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 i.1.1) * x y := by
        have h1 : ∑ u : NonSink M, Q u.1 i.1.1 * (mdpMatrix M *ᵥ x) u =
            ∑ y : ActionVar M, (∑ u : NonSink M, Q u.1 i.1.1 * mdpMatrix M u y) * x y := by
          simp_rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ ↦ by ring
        rw [h1, sum_actionVar_split M π]
        have hbas : ∑ s : NonSink M,
            (∑ u : NonSink M, Q u.1 i.1.1 * mdpMatrix M u ⟨s, π s.1⟩) * x ⟨s, π s.1⟩ = x i := by
          have hcoef : ∀ s : NonSink M,
              ∑ u : NonSink M, Q u.1 i.1.1 * mdpMatrix M u ⟨s, π s.1⟩ =
                if s = i.1 then 1 else 0 := fun s ↦ by
            have := sum_nonSink_one_sub_mul_inv hπ s i.1
            have hstep : ∀ u : NonSink M, Q u.1 i.1.1 * mdpMatrix M u ⟨s, π s.1⟩ =
                (1 - M.transitionMatrix π) s.1 u.1 * Q u.1 i.1.1 := fun u ↦ by
              simp only [mdpMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
                FiniteMDP.transitionMatrix_apply]
              have heq : (u = s) ↔ (s.1 = u.1) := by rw [Subtype.ext_iff]; exact eq_comm
              simp only [heq]
              ring
            simp_rw [hstep]
            exact this
          simp_rw [hcoef]
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          cases i with
          | mk s a =>
            dsimp only at hi'
            subst hi'
            rfl
        have hnonbas : ∀ y ∈ (policyBasis M π)ᶜ,
            ∑ u : NonSink M, Q u.1 i.1.1 * mdpMatrix M u y =
              -(∑ w : NonSink M, Q w.1 i.1.1 * M.prob y.1.1 y.2 w.1 - Q y.1.1 i.1.1) := by
          intro y _
          simp only [mdpMatrix, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
          have hfirst : ∑ u : NonSink M, Q u.1 i.1.1 * (if u = y.1 then 1 else 0) =
              Q y.1.1 i.1.1 := by simp
          rw [hfirst]
          ring
        rw [hbas]
        have hneg : ∑ y ∈ (policyBasis M π)ᶜ,
            (∑ u : NonSink M, Q u.1 i.1.1 * mdpMatrix M u y) * x y =
            -(∑ y ∈ (policyBasis M π)ᶜ,
              ((∑ w : NonSink M, Q w.1 i.1.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 i.1.1) * x y) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun y hy ↦ ?_
          rw [hnonbas y hy]
          ring
        rw [hneg]
        ring
      rw [hLHS] at hsum_eq
      have hRHS : ∑ u : NonSink M, Q u.1 i.1.1 * mdpRhs M u =
          ∑ v : NonSink M, Q v.1 i.1.1 := by simp [mdpRhs]
      rw [hRHS] at hsum_eq
      simp only [policyDictionary, hi', true_and, ↓reduceIte]
      have hcongr : ∑ y ∈ (policyBasis M π)ᶜ,
          (if y.2 ≠ π y.1.1 then
            (∑ w : NonSink M, Q w.1 i.1.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 i.1.1
           else 0) * x y =
          ∑ y ∈ (policyBasis M π)ᶜ,
            ((∑ w : NonSink M, Q w.1 i.1.1 * M.prob y.1.1 y.2 w.1) - Q y.1.1 i.1.1) * x y := by
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        have hy' : y.2 ≠ π y.1.1 := mt mem_policyBasis_iff.mpr (Finset.mem_compl.mp hy)
        simp [hy']
      dsimp only [Q] at hcongr hsum_eq
      rw [hcongr]
      linarith
  · intro x hAx
    have hval_dot : ∑ u : NonSink M, M.val π u.1 * (mdpMatrix M *ᵥ x) u =
        ∑ u : NonSink M, M.val π u.1 * mdpRhs M u := by rw [hAx]
    have hRHS : ∑ u : NonSink M, M.val π u.1 * mdpRhs M u = ∑ u : NonSink M, M.val π u.1 := by
      simp [mdpRhs]
    have hLHS : ∑ u : NonSink M, M.val π u.1 * (mdpMatrix M *ᵥ x) u =
        ∑ y : ActionVar M, (M.val π y.1.1 - ∑ u : S, M.prob y.1.1 y.2 u * M.val π u) * x y := by
      simp_rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      congr 1
      simp only [mdpMatrix, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
      have h1 : ∑ u : NonSink M, M.val π u.1 * (if u = y.1 then 1 else 0) = M.val π y.1.1 := by
        simp
      have h2 : ∑ u : NonSink M, M.val π u.1 * M.prob y.1.1 y.2 u.1 =
          ∑ u : S, M.prob y.1.1 y.2 u * M.val π u := by
        simp_rw [mul_comm (M.val π _) (M.prob _ _ _)]
        exact sum_nonSink_eq_sum M (fun u ↦ M.prob y.1.1 y.2 u * M.val π u)
          fun u hu ↦ by rw [hπ.val_sink hu, mul_zero]
      rw [h1, h2]
    rw [hLHS, hRHS] at hval_dot
    rw [Dictionary.value, policyDictionary]
    dsimp only
    have hsplit : mdpObj M ⬝ᵥ x =
        (∑ u : NonSink M, M.val π u.1) +
        ∑ y : ActionVar M, (M.appeal π y.1.1 y.2 - M.val π y.1.1) * x y := by
      rw [← hval_dot]
      change (∑ y : ActionVar M, M.reward y.1.1 y.2 * x y) = _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [FiniteMDP.appeal_eq]
      ring
    rw [hsplit, sum_actionVar_split M π (fun y ↦ (M.appeal π y.1.1 y.2 - M.val π y.1.1) * x y)]
    have hzero : ∑ s : NonSink M, (M.appeal π s.1 (π s.1) - M.val π s.1) * x ⟨s, π s.1⟩ = 0 :=
      Finset.sum_eq_zero fun s _ ↦ by rw [hπ.appeal_self s.1, sub_self, zero_mul]
    rw [hzero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    have hy' : y.2 ≠ π y.1.1 := mt mem_policyBasis_iff.mpr (Finset.mem_compl.mp hy)
    simp [hy']

omit [∀ s, Fintype (A s)] in
/-- **Unique leaving variable and exact pivot equivalence**: switching a single non-sink state `s`
from `π s` to `a` (`a ≠ π s`) produces a strictly negative pivot entry at `⟨s, π s⟩`, makes
`⟨s, π s⟩` the unique minimum-ratio leaving variable, and yields
`policyDictionary M (Function.update π s a)`. -/
theorem policyDictionary_pivot_spec [∀ s, Finite (A s)]
    {M : FiniteMDP S A K} {π : FiniteMDP.Policy S A}
    (hπ : M.IsProper π) (s : NonSink M) (a : A s.1) (ha : a ≠ π s.1)
    (hπ' : M.IsProper (Function.update π s.1 a)) :
    let D := policyDictionary M π
    let r : ActionVar M := ⟨s, π s.1⟩
    let c : ActionVar M := ⟨s, a⟩
    D.coeff r c < 0 ∧
      (∀ i ∈ D.basis, i ≠ r → D.coeff i c < 0 → D.ratio c r < D.ratio c i) ∧
      D.pivot r c = policyDictionary M (Function.update π s.1 a) := by
  let _ : ∀ t, Fintype (A t) := fun t ↦ Fintype.ofFinite (A t)
  set π' := Function.update π s.1 a
  set D := policyDictionary M π
  set D' := policyDictionary M π'
  set r : ActionVar M := ⟨s, π s.1⟩
  set c : ActionVar M := ⟨s, a⟩
  have hr : r ∈ D.basis := mem_policyBasis_iff.mpr rfl
  have hc : c ∉ D.basis := mt mem_policyBasis_iff.mp ha
  have hrep : D.Represents (mdpMatrix M) (mdpRhs M) (mdpObj M) := policyDictionary_represents hπ
  have hrep' : D'.Represents (mdpMatrix M) (mdpRhs M) (mdpObj M) :=
    policyDictionary_represents hπ'
  have hsol' : D.IsSolution D'.basicSolution :=
    (hrep.isSolution_iff _).mpr hrep'.mulVec_basicSolution
  have hc_mem' : c ∈ D'.basis := by
    dsimp only [D', policyDictionary]
    exact mem_policyBasis_iff.mpr (by simp [π', c])
  set t : K := D'.basicSolution c
  have ht_pos : 0 < t := by
    rw [show t = D'.rhs c from D'.basicSolution_of_mem hc_mem']
    exact lt_of_lt_of_le zero_lt_one (one_le_policyDictionary_rhs hπ' hc_mem')
  have hray_eq : D'.basicSolution = D.basicSolution + t • D.ray c := by
    have hsol_ray : D.IsSolution (D.basicSolution + t • D.ray c) :=
      D.isSolution_add_smul_ray hc D.isSolution_basicSolution t
    ext i
    by_cases hi : i ∈ D.basis
    · rw [hsol' i hi, hsol_ray i hi]
      congr 1
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj_not : j ∉ D.basis := Finset.mem_compl.mp hj
      by_cases hjc : j = c
      · subst hjc
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, D.basicSolution_of_notMem hc,
          D.ray_self, mul_one, zero_add, t]
      · have hj_not' : j ∉ D'.basis := by
          intro hmem
          have hj_eq : j.2 = π' j.1.1 := mem_policyBasis_iff.mp hmem
          by_cases hjs : j.1 = s
          · apply hjc
            cases j with
            | mk u b =>
              dsimp only at hjs hj_eq
              subst hjs
              simp only [π', Function.update_self] at hj_eq
              subst hj_eq
              rfl
          · apply hj_not
            dsimp only [D, policyDictionary]
            rw [mem_policyBasis_iff, hj_eq]
            simp [π', Subtype.ext_iff.not.mp hjs]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, D'.basicSolution_of_notMem hj_not',
          D.basicSolution_of_notMem hj_not, D.ray_of_notMem hj_not hjc, mul_zero, add_zero]
    · by_cases hic : i = c
      · subst hic
        simp [D.basicSolution_of_notMem hc, D.ray_self, t]
      · have hi_not' : i ∉ D'.basis := by
          intro hmem
          have hi_eq : i.2 = π' i.1.1 := mem_policyBasis_iff.mp hmem
          by_cases his : i.1 = s
          · apply hic
            cases i with
            | mk u b =>
              dsimp only at his hi_eq
              subst his
              simp only [π', Function.update_self] at hi_eq
              subst hi_eq
              rfl
          · apply hi
            dsimp only [D, policyDictionary]
            rw [mem_policyBasis_iff, hi_eq]
            simp [π', Subtype.ext_iff.not.mp his]
        simp [D'.basicSolution_of_notMem hi_not', D.basicSolution_of_notMem hi,
          D.ray_of_notMem hi hic]
  have hr_not' : r ∉ D'.basis := by
    intro hmem
    have := mem_policyBasis_iff.mp hmem
    simp [r, π'] at this
    exact ha this.symm
  have hrow_r : D.rhs r + t * D.coeff r c = 0 := by
    have := congr_fun hray_eq r
    rw [D'.basicSolution_of_notMem hr_not', Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      D.basicSolution_of_mem hr, D.ray_of_mem hr hc] at this
    exact this.symm
  have hrhs_r_pos : 0 < D.rhs r :=
    lt_of_lt_of_le zero_lt_one (one_le_policyDictionary_rhs hπ hr)
  have hcoeff_neg : D.coeff r c < 0 := by nlinarith
  have hratio_r : D.ratio c r = t := by
    rw [Dictionary.ratio, div_eq_iff (neg_pos.mpr hcoeff_neg).ne']
    linarith
  have hmin : ∀ i ∈ D.basis, i ≠ r → D.coeff i c < 0 → D.ratio c r < D.ratio c i := by
    intro i hi hir hneg
    have hi' : i ∈ D'.basis := by
      have hi_eq : i.2 = π i.1.1 := mem_policyBasis_iff.mp hi
      have his : i.1 ≠ s := by
        intro hEq
        apply hir
        cases i with
        | mk u b =>
          dsimp only at hEq hi_eq
          subst hEq
          subst hi_eq
          rfl
      dsimp only [D', policyDictionary]
      rw [mem_policyBasis_iff, hi_eq]
      simp [π', Subtype.ext_iff.not.mp his]
    have hrow_i : 0 < D.rhs i + t * D.coeff i c := by
      have := congr_fun hray_eq i
      rw [D'.basicSolution_of_mem hi', Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        D.basicSolution_of_mem hi, D.ray_of_mem hi hc] at this
      have hi_pos : 0 < D'.rhs i :=
        lt_of_lt_of_le zero_lt_one (one_le_policyDictionary_rhs hπ' hi')
      linarith
    rw [hratio_r, Dictionary.ratio, lt_div_iff₀ (neg_pos.mpr hneg)]
    linarith
  have hbasis_eq : (D.pivot r c).basis = D'.basis := by
    ext x
    dsimp only [D, D', policyDictionary]
    rw [Dictionary.mem_pivot_basis, mem_policyBasis_iff, mem_policyBasis_iff]
    cases x with
    | mk u b =>
      dsimp only [r, c, π']
      by_cases hus : u = s
      · subst hus
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Function.update_self]
        constructor
        · rintro (rfl | ⟨hEq, hne⟩)
          · rfl
          · exact absurd (show (⟨u, b⟩ : ActionVar M) = ⟨u, π u.1⟩ by rw [hEq]) hne
        · rintro rfl; exact .inl rfl
      · have hus' : u.1 ≠ s.1 := Subtype.ext_iff.not.mp hus
        simp only [Sigma.mk.injEq, hus, false_and, false_or, ne_eq, not_false_eq_true, and_true,
          Function.update_of_ne hus']
  have hpivot_eq : D.pivot r c = D' :=
    dictionary_eq_of_represents hbasis_eq
      (hrep.of_equivalent (D.equivalent_pivot hr hc hcoeff_neg.ne))
      hrep' (dictionaryNormalized_pivot D r c) (policyDictionary_normalized M π')
  exact ⟨hcoeff_neg, hmin, hpivot_eq⟩

section StepEquivalence

/-- **Bland's pivoting rule on `policyDictionary M π`**: `blandStep` stops at `.optimal` iff `π`
is locally optimal, and otherwise pivots on the smallest improving `(s, a)` to produce
`policyDictionary M (Function.update π s a)`. -/
theorem blandStep_policyDictionary {M : FiniteMDP S A K}
    {π : FiniteMDP.Policy S A} (hπ : M.IsProper π) [LinearOrder (ActionVar M)]
    (hnext : ∀ (s : NonSink M) (a : A s.1), M.IsProper (Function.update π s.1 a)) :
    let D := policyDictionary M π
    (D.blandStep = .optimal ↔ M.IsLocallyOptimal π) ∧
      ∀ (s : NonSink M) (a : A s.1),
        (D.blandStep = .pivot ⟨s, π s.1⟩ ⟨s, a⟩ ↔
          M.val π s.1 < M.appeal π s.1 a ∧
          ∀ (t : NonSink M) (b : A t.1),
            M.val π t.1 < M.appeal π t.1 b → (⟨s, a⟩ : ActionVar M) ≤ ⟨t, b⟩) ∧
        (D.blandStep = .pivot ⟨s, π s.1⟩ ⟨s, a⟩ →
          D.pivot ⟨s, π s.1⟩ ⟨s, a⟩ = policyDictionary M (Function.update π s.1 a)) := by
  set D := policyDictionary M π
  have hobj : ∀ y : ActionVar M, y ∉ D.basis →
      D.objCoeff y = M.appeal π y.1.1 y.2 - M.val π y.1.1 := by
    intro y hy
    dsimp only [D, policyDictionary]
    exact ite_eq_right (mt mem_policyBasis_iff.mpr hy)
  constructor
  · rw [D.blandStep_eq_optimal_iff, D.blandEntering_eq_none_iff, FiniteMDP.isLocallyOptimal_iff]
    constructor
    · intro h s
      rw [FiniteMDP.switchable_iff]
      rintro ⟨hs_ns, a, ha⟩
      have hne : a ≠ π s := by
        intro heq; subst heq; rw [hπ.appeal_self] at ha; exact lt_irrefl _ ha
      have hmem : (⟨⟨s, hs_ns⟩, a⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp hne
      have := h _ hmem
      rw [hobj _ hmem] at this
      linarith
    · intro h y hy
      rw [hobj y hy]
      by_contra hlt
      push Not at hlt
      exact h y.1.1 ((FiniteMDP.switchable_iff M π y.1.1).mpr ⟨y.1.2, y.2, by linarith⟩)
  · intro s a
    constructor
    · constructor
      · intro hpiv
        obtain ⟨hent, _⟩ := D.blandStep_eq_pivot_iff.mp hpiv
        obtain ⟨hc, hpos, hmin⟩ := D.blandEntering_eq_some_iff.mp hent
        rw [hobj _ hc] at hpos
        refine ⟨by linarith, fun t b htb ↦ ?_⟩
        have htb_ne : b ≠ π t.1 := by
          intro heq; subst heq; rw [hπ.appeal_self] at htb; exact lt_irrefl _ htb
        have htb_mem : (⟨t, b⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp htb_ne
        exact hmin _ htb_mem (by rw [hobj _ htb_mem]; linarith)
      · rintro ⟨himp, hmin⟩
        have ha : a ≠ π s.1 := by
          intro heq; subst heq; rw [hπ.appeal_self] at himp; exact lt_irrefl _ himp
        have hc : (⟨s, a⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp ha
        have hent : D.blandEntering = some ⟨s, a⟩ := by
          rw [D.blandEntering_eq_some_iff]
          refine ⟨hc, by rw [hobj _ hc]; linarith, fun y hy hpos ↦ ?_⟩
          rw [hobj y hy] at hpos
          exact hmin y.1 y.2 (by linarith)
        obtain ⟨hneg, hrat, _⟩ := policyDictionary_pivot_spec hπ s a ha (hnext s a)
        have hleav : D.blandLeaving ⟨s, a⟩ = some ⟨s, π s.1⟩ := by
          rw [D.blandLeaving_eq_some_iff]
          refine ⟨mem_policyBasis_iff.mpr rfl, hneg, ?_, ?_⟩
          · intro i hi hci
            by_cases hir : i = ⟨s, π s.1⟩
            · subst hir; exact le_rfl
            · exact (hrat i hi hir hci).le
          · intro i hi hci heq
            by_cases hir : i = ⟨s, π s.1⟩
            · subst hir; exact le_rfl
            · exact absurd heq (hrat i hi hir hci).ne'
        exact D.blandStep_eq_pivot_iff.mpr ⟨hent, hleav⟩
    · intro hpiv
      obtain ⟨hent, _⟩ := D.blandStep_eq_pivot_iff.mp hpiv
      obtain ⟨hc, _, _⟩ := D.blandEntering_eq_some_iff.mp hent
      have ha : a ≠ π s.1 := by
        dsimp only [D, policyDictionary] at hc
        exact fun heq ↦ hc (mem_policyBasis_iff.mpr heq)
      exact (policyDictionary_pivot_spec hπ s a ha (hnext s a)).2.2

/-- **Dantzig's pivoting rule on `policyDictionary M π`**: `dantzigStep` stops at `.optimal` iff
`π` is locally optimal, and otherwise pivots on the improving `(s, a)` maximizing
`appeal π s a - val π s` (smallest in case of ties) to produce
`policyDictionary M (Function.update π s a)`. -/
theorem dantzigStep_policyDictionary {M : FiniteMDP S A K}
    {π : FiniteMDP.Policy S A} (hπ : M.IsProper π) [LinearOrder (ActionVar M)]
    (hnext : ∀ (s : NonSink M) (a : A s.1), M.IsProper (Function.update π s.1 a)) :
    let D := policyDictionary M π
    (D.dantzigStep = .optimal ↔ M.IsLocallyOptimal π) ∧
      ∀ (s : NonSink M) (a : A s.1),
        (D.dantzigStep = .pivot ⟨s, π s.1⟩ ⟨s, a⟩ ↔
          M.val π s.1 < M.appeal π s.1 a ∧
          (∀ (t : NonSink M) (b : A t.1),
            M.appeal π t.1 b - M.val π t.1 ≤ M.appeal π s.1 a - M.val π s.1) ∧
          (∀ (t : NonSink M) (b : A t.1),
            M.appeal π t.1 b - M.val π t.1 = M.appeal π s.1 a - M.val π s.1 →
              (⟨s, a⟩ : ActionVar M) ≤ ⟨t, b⟩)) ∧
        (D.dantzigStep = .pivot ⟨s, π s.1⟩ ⟨s, a⟩ →
          D.pivot ⟨s, π s.1⟩ ⟨s, a⟩ = policyDictionary M (Function.update π s.1 a)) := by
  set D := policyDictionary M π
  have hobj : ∀ y : ActionVar M, y ∉ D.basis →
      D.objCoeff y = M.appeal π y.1.1 y.2 - M.val π y.1.1 := by
    intro y hy
    dsimp only [D, policyDictionary]
    exact ite_eq_right (mt mem_policyBasis_iff.mpr hy)
  constructor
  · rw [D.dantzigStep_eq_optimal_iff, D.dantzigEntering_eq_none_iff, FiniteMDP.isLocallyOptimal_iff]
    constructor
    · intro h s
      rw [FiniteMDP.switchable_iff]
      rintro ⟨hs_ns, a, ha⟩
      have hne : a ≠ π s := by
        intro heq; subst heq; rw [hπ.appeal_self] at ha; exact lt_irrefl _ ha
      have hmem : (⟨⟨s, hs_ns⟩, a⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp hne
      have := h _ hmem
      rw [hobj _ hmem] at this
      linarith
    · intro h y hy
      rw [hobj y hy]
      by_contra hlt
      push Not at hlt
      exact h y.1.1 ((FiniteMDP.switchable_iff M π y.1.1).mpr ⟨y.1.2, y.2, by linarith⟩)
  · intro s a
    constructor
    · constructor
      · intro hpiv
        obtain ⟨hent, _⟩ := D.dantzigStep_eq_pivot_iff.mp hpiv
        obtain ⟨hc, hpos, hmax, htie⟩ := D.dantzigEntering_eq_some_iff.mp hent
        rw [hobj _ hc] at hpos
        refine ⟨by linarith, fun t b ↦ ?_, fun t b heq ↦ ?_⟩
        · by_cases htb : b = π t.1
          · subst htb; rw [hπ.appeal_self, sub_self]; linarith
          · have hmem : (⟨t, b⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp htb
            have := hmax _ hmem
            rwa [hobj _ hmem, hobj _ hc] at this
        · have htb : b ≠ π t.1 := by
            intro hEq; subst hEq; rw [hπ.appeal_self, sub_self] at heq; linarith
          have hmem : (⟨t, b⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp htb
          exact htie _ hmem (by rw [hobj _ hmem, hobj _ hc, heq])
      · rintro ⟨himp, hmax, htie⟩
        have ha : a ≠ π s.1 := by
          intro heq; subst heq; rw [hπ.appeal_self] at himp; exact lt_irrefl _ himp
        have hc : (⟨s, a⟩ : ActionVar M) ∉ D.basis := mt mem_policyBasis_iff.mp ha
        have hent : D.dantzigEntering = some ⟨s, a⟩ := by
          rw [D.dantzigEntering_eq_some_iff]
          refine ⟨hc, by rw [hobj _ hc]; linarith,
            fun y hy ↦ by rw [hobj y hy, hobj _ hc]; exact hmax y.1 y.2,
            fun y hy heq ↦ htie y.1 y.2 (by rwa [hobj y hy, hobj _ hc] at heq)⟩
        obtain ⟨hneg, hrat, _⟩ := policyDictionary_pivot_spec hπ s a ha (hnext s a)
        have hleav : D.blandLeaving ⟨s, a⟩ = some ⟨s, π s.1⟩ := by
          rw [D.blandLeaving_eq_some_iff]
          refine ⟨mem_policyBasis_iff.mpr rfl, hneg, ?_, ?_⟩
          · intro i hi hci
            by_cases hir : i = ⟨s, π s.1⟩
            · subst hir; exact le_rfl
            · exact (hrat i hi hir hci).le
          · intro i hi hci heq
            by_cases hir : i = ⟨s, π s.1⟩
            · subst hir; exact le_rfl
            · exact absurd heq (hrat i hi hir hci).ne'
        exact D.dantzigStep_eq_pivot_iff.mpr ⟨hent, hleav⟩
    · intro hpiv
      obtain ⟨hent, _⟩ := D.dantzigStep_eq_pivot_iff.mp hpiv
      obtain ⟨hc, _, _, _⟩ := D.dantzigEntering_eq_some_iff.mp hent
      have ha : a ≠ π s.1 := by
        dsimp only [D, policyDictionary] at hc
        exact fun heq ↦ hc (mem_policyBasis_iff.mpr heq)
      exact (policyDictionary_pivot_spec hπ s a ha (hnext s a)).2.2

end StepEquivalence

end FiniteActions

end OrderedMdpLP

end MdpLP

end Cslib.Algorithms.Lean.Simplex
