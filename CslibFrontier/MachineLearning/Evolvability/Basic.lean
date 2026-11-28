/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module

public import Cslib.Foundations.Data.BitString
public import Cslib.MachineLearning.PACLearning.Defs
public import Cslib.Probability.PMF
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Languages.Probabilistic.QueriesWith
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.MachineLearning.StatisticalQuery.Basic
public import CslibFrontier.MachineLearning.StatisticalQuery.Parity
public import CslibFrontier.MachineLearning.StatisticalQuery.Simulation
import CslibFrontier.Probability.PMF
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evolvability, Statistical Queries, and Boolean Conjunction Landscapes

Evolvability models local search over a representation space `R` guided only by aggregate
correlation feedback `StatisticalQuery.corr D f (eval r)` between candidate hypotheses and an
unknown target concept `f : X → Bool` under an input distribution `D : PMF X`. At each generation,
candidates in a bounded local neighborhood are partitioned into beneficial mutations (`v(r') ≥ v(r)
+ t`) and neutral mutations (`v(r) - t ≤ v(r') < v(r) + t`).

This module develops the general connection between bounded-neighborhood evolutionary trajectories
and statistical-query learning over finite input spaces, derives the representation-independent
exponential lower bound for evolving Boolean parity functions under the uniform distribution, and
establishes the exact correlation formula and bounded-degree local neighborhood properties for
monotone Boolean conjunctions.

## Main definitions

* `CslibFrontier.MachineLearning.Evolvability.corrQuery`: statistical query whose expectation equals
  `StatisticalQuery.corr D f r`.
* `CslibFrontier.MachineLearning.Evolvability.beneficialSet`,
  `CslibFrontier.MachineLearning.Evolvability.neutralSet`: beneficial and neutral mutation sets in a
  candidate neighborhood.
* `CslibFrontier.MachineLearning.Evolvability.detEvolve`,
  `CslibFrontier.MachineLearning.Evolvability.evolveSQ`: deterministic `g`-generation evolutionary
  trajectory and its simulation in `StatisticalQuery.Algorithm`.
* `CslibFrontier.MachineLearning.Evolvability.monotoneConjunction`,
  `CslibFrontier.MachineLearning.Evolvability.BoundedConjunction`,
  `CslibFrontier.MachineLearning.Evolvability.monotoneNeighborhood`: monotone Boolean conjunctions
  and their `(+1 / -1 / swap)` bounded-support neighborhood.

## Main results

* `CslibFrontier.MachineLearning.Evolvability.corr_mem_Icc`,
  `CslibFrontier.MachineLearning.Evolvability.corr_eq_one_iff`: correlation bounds in `[-1, 1]` and
  characterization of unit correlation on `D.support`.
* `CslibFrontier.MachineLearning.Evolvability.isQueryBounded_evolveSQ`,
  `CslibFrontier.MachineLearning.Evolvability.evolveSQ_learnsStateless`,
  `CslibFrontier.MachineLearning.Evolvability.evolveSQ_isPACLearnerFor`: simulation of
  `g`-generation bounded-neighborhood evolution using at most `g * (p + 1)` statistical queries, and
  resulting statistical-query and PAC learnability transfers.
* `CslibFrontier.MachineLearning.Evolvability.parity_evolvability_sq_lower_bound`: universal
  exponential lower bound `2^n ≤ (g * (p + 1)) / τ^2 + 1 / (1 - ε)^2` for evolving `n`-bit parities
  under the uniform distribution.
* `CslibFrontier.MachineLearning.Evolvability.corr_uniformOfFintype_monotoneConjunction`,
  `CslibFrontier.MachineLearning.Evolvability.card_monotoneNeighborhood_le`: closed-form uniform
  correlation and polynomial `(n + 1)^2` neighborhood bound for monotone conjunctions.
-/

public section

namespace CslibFrontier.MachineLearning.Evolvability

open Finset
open scoped BigOperators ENNReal NNReal

section GeneralDomain

/-- Statistical query evaluating agreement sign `signVal y * signVal (r x)` for hypothesis `r`. -/
def corrQuery {X : Type} (r : X → Bool) : Cslib.MachineLearning.StatisticalQuery.Query X where
  toFun x y := Cslib.BitString.signVal y * Cslib.BitString.signVal (r x)
  abs_le_one' x y := by
    rw [abs_mul, Cslib.BitString.abs_signVal, Cslib.BitString.abs_signVal, mul_one]

/-- Expectation of `corrQuery r` equals `StatisticalQuery.corr D c r`. -/
theorem expect_corrQuery_eq_corr {X : Type} [Fintype X] (D : PMF X) (c r : X → Bool) :
    Cslib.MachineLearning.StatisticalQuery.expect D c (corrQuery r) =
      Cslib.MachineLearning.StatisticalQuery.corr D c r := by rfl

/-- Correlation between Boolean functions lies in `[-1, 1]`. -/
theorem corr_mem_Icc {X : Type} [Fintype X] (D : PMF X) (f r : X → Bool) :
    Cslib.MachineLearning.StatisticalQuery.corr D f r ∈ Set.Icc (-1) 1 := by
  rw [Cslib.MachineLearning.StatisticalQuery.corr_eq_one_sub_two_mul_disagreement]
  have h0 : 0 ≤ Cslib.MachineLearning.StatisticalQuery.disagreement D f r := by
    refine sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg ?_
    split_ifs <;> norm_num
  have h1 : Cslib.MachineLearning.StatisticalQuery.disagreement D f r ≤ 1 := by
    calc Cslib.MachineLearning.StatisticalQuery.disagreement D f r
        ≤ ∑ x, (D x).toReal * 1 := by
          refine sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          split_ifs <;> norm_num
      _ = 1 := by simp only [mul_one, Cslib.Probability.PMF.sum_toReal]
  exact ⟨by linarith, by linarith⟩

/-- Correlation equals `1` if and only if `r` agrees with `f` throughout `D.support`. -/
theorem corr_eq_one_iff {X : Type} [Fintype X] (D : PMF X) (f r : X → Bool) :
    Cslib.MachineLearning.StatisticalQuery.corr D f r = 1 ↔ ∀ x ∈ D.support, r x = f x := by
  rw [Cslib.MachineLearning.StatisticalQuery.corr_eq_one_sub_two_mul_disagreement]
  rw [show (1 - 2 * Cslib.MachineLearning.StatisticalQuery.disagreement D f r = 1) ↔
      Cslib.MachineLearning.StatisticalQuery.disagreement D f r = 0 by
    constructor <;> intro h <;> linarith]
  unfold Cslib.MachineLearning.StatisticalQuery.disagreement
  rw [sum_eq_zero_iff_of_nonneg (fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (by split_ifs <;> norm_num))]
  constructor
  · intro h x hx
    have hx0 := h x (mem_univ x)
    have hDpos : 0 < (D x).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff D x).mp hx) (D.apply_ne_top x)
    by_contra hne
    have hne' : f x ≠ r x := fun heq ↦ hne heq.symm
    simp only [hne', ↓reduceIte, mul_one] at hx0
    linarith
  · intro h x _
    by_cases hx : x ∈ D.support
    · simp only [h x hx, ↓reduceIte, mul_zero]
    · have hDx : D x = 0 := not_not.mp ((PMF.mem_support_iff D x).not.mp hx)
      simp only [hDx, ENNReal.toReal_zero, zero_mul]

/-- Beneficial mutation candidates `{r' ∈ N | v r + t ≤ v r'}`. -/
noncomputable def beneficialSet {R : Type*} (N : Finset R) (v : R → ℝ)
    (t : ℝ) (r : R) : Finset R :=
  by classical exact N.filter fun r' ↦ v r + t ≤ v r'

/-- Neutral mutation candidates `{r' ∈ N | v r - t ≤ v r'} \ beneficialSet N v t r`. -/
noncomputable def neutralSet {R : Type*} [DecidableEq R] (N : Finset R) (v : R → ℝ)
    (t : ℝ) (r : R) : Finset R :=
  (by classical exact N.filter fun r' ↦ v r - t ≤ v r') \ beneficialSet N v t r

/-- Membership in `beneficialSet`. -/
theorem mem_beneficialSet_iff {R : Type*} {N : Finset R} {v : R → ℝ}
    {t : ℝ} {r r' : R} :
    r' ∈ beneficialSet N v t r ↔ r' ∈ N ∧ v r + t ≤ v r' := by
  classical
  simp only [beneficialSet, mem_filter]

/-- Membership in `neutralSet`. -/
theorem mem_neutralSet_iff {R : Type*} [DecidableEq R] {N : Finset R} {v : R → ℝ}
    {t : ℝ} {r r' : R} :
    r' ∈ neutralSet N v t r ↔ r' ∈ N ∧ v r - t ≤ v r' ∧ v r' < v r + t := by
  simp only [neutralSet, mem_sdiff, mem_beneficialSet_iff, not_and, not_le]
  have hlow_iff : r' ∈ (by classical exact N.filter fun q ↦ v r - t ≤ v q) ↔
      r' ∈ N ∧ v r - t ≤ v r' := by
    classical
    simp only [mem_filter]
  rw [hlow_iff]
  exact ⟨fun ⟨⟨hN, hlow⟩, hhigh⟩ ↦ ⟨hN, hlow, hhigh hN⟩,
    fun ⟨hN, hlow, hhigh⟩ ↦ ⟨⟨hN, hlow⟩, fun _ ↦ hhigh⟩⟩

/-- `beneficialSet` and `neutralSet` are disjoint. -/
theorem disjoint_beneficialSet_neutralSet {R : Type*} [DecidableEq R] (N : Finset R)
    (v : R → ℝ) (t : ℝ) (r : R) :
    Disjoint (beneficialSet N v t r) (neutralSet N v t r) :=
  disjoint_sdiff_self_right

/-- Beneficial-first, neutral-second deterministic candidate selector on evaluated neighborhoods. -/
noncomputable def selectCandidate {R : Type} (t vCurr : ℝ)
    (candidates : List (R × ℝ)) : Option R := by
  classical
  exact match candidates.find? (fun p ↦ decide (vCurr + t ≤ p.2)) with
  | some (r', _) => some r'
  | none =>
      match candidates.find? (fun p ↦ decide (vCurr - t ≤ p.2)) with
      | some (r', _) => some r'
      | none => none

/-- Deterministic `g`-generation evolutionary trajectory under neighborhood `neigh`, valuation `v`,
and threshold `t`. -/
noncomputable def detEvolve {R : Type} (neigh : R → List R) (v : R → ℝ) (t : ℝ) :
    ℕ → R → R
  | 0, r => r
  | g + 1, r =>
      match selectCandidate t (v r) ((neigh r).map fun r' ↦ (r', v r')) with
      | some r' => detEvolve neigh v t g r'
      | none => r

/-- Queries `corrQuery (eval r')` across every candidate in `L`. -/
def queryCandidates {X R : Type} (eval : R → X → Bool) :
    List R → Cslib.OracleComp (Cslib.MachineLearning.StatisticalQuery.spec X) (List (R × ℝ))
  | [] => pure []
  | r' :: rs =>
      Cslib.OracleComp.query (corrQuery (eval r')) >>= fun val ↦
        (fun rest ↦ (r', val) :: rest) <$> queryCandidates eval rs

/-- `queryCandidates eval L` makes at most `L.length` oracle calls. -/
theorem isQueryBounded_queryCandidates {X R : Type} (eval : R → X → Bool) (L : List R) :
    (queryCandidates eval L).IsQueryBounded L.length := by
  induction L with
  | nil =>
    unfold queryCandidates
    exact Cslib.OracleComp.IsCostBounded.pure [] 0
  | cons r' rs ih =>
    unfold queryCandidates
    simpa only [List.length_cons] using
      Cslib.OracleComp.IsCostBounded.liftBind (corrQuery (eval r'))
        (fun val ↦ (fun rest ↦ (r', val) :: rest) <$> queryCandidates eval rs)
        rs.length fun _ ↦ (Cslib.OracleComp.isCostBounded_map_iff _ _ _).mpr ih

private theorem interpret_queryCandidates_bind {X R α : Type}
    (eval : R → X → Bool)
    (answer : Cslib.MachineLearning.StatisticalQuery.Query X → ℝ)
    (L : List R)
    (k : List (R × ℝ) → Cslib.OracleComp (Cslib.MachineLearning.StatisticalQuery.spec X) α) :
    Cslib.OracleComp.interpret (m := Id) answer (queryCandidates eval L >>= k) =
      Cslib.OracleComp.interpret (m := Id) answer
        (k (L.map fun r' ↦ (r', answer (corrQuery (eval r'))))) := by
  induction L generalizing k with
  | nil => rfl
  | cons r' rs ih =>
    simp only [queryCandidates, ← bind_pure_comp, bind_assoc,
      Cslib.OracleComp.interpret_id_query_bind, List.map_cons]
    exact ih (fun rest ↦ k ((r', answer (corrQuery (eval r'))) :: rest))

/-- Statistical-query algorithm simulating `g` generations of `detEvolve`. -/
noncomputable def evolveSQ {X R : Type} (eval : R → X → Bool)
    (neigh : R → List R) (t : ℝ) :
    ℕ → R → Cslib.OracleComp (Cslib.MachineLearning.StatisticalQuery.spec X) (X → Bool)
  | 0, r => pure (eval r)
  | g + 1, r =>
      Cslib.OracleComp.query (corrQuery (eval r)) >>= fun vCurr ↦
        queryCandidates eval (neigh r) >>= fun candVals ↦
          match selectCandidate t vCurr candVals with
          | some r' => evolveSQ eval neigh t g r'
          | none => pure (eval r)

/-- When neighborhoods have size at most `p`, `evolveSQ` makes at most `g * (p + 1)` queries. -/
theorem isQueryBounded_evolveSQ {X R : Type} (eval : R → X → Bool)
    {neigh : R → List R} {p : ℕ} (hneigh : ∀ r, (neigh r).length ≤ p)
    (t : ℝ) (g : ℕ) (r₀ : R) :
    (evolveSQ eval neigh t g r₀).IsQueryBounded (g * (p + 1)) := by
  induction g generalizing r₀ with
  | zero =>
    unfold evolveSQ
    simpa only [Nat.zero_mul] using Cslib.OracleComp.IsCostBounded.pure (eval r₀) 0
  | succ g ih =>
    unfold evolveSQ
    have hcand : (queryCandidates eval (neigh r₀)).IsQueryBounded p :=
      (isQueryBounded_queryCandidates eval (neigh r₀)).mono (hneigh r₀)
    have hstep : ∀ vCurr : ℝ,
        (queryCandidates eval (neigh r₀) >>= fun candVals ↦
          match selectCandidate t vCurr candVals with
          | some r' => evolveSQ eval neigh t g r'
          | none => pure (eval r₀)).IsQueryBounded (p + g * (p + 1)) := fun vCurr ↦
      Cslib.OracleComp.IsCostBounded.bind hcand fun candVals ↦ by
        cases selectCandidate t vCurr candVals with
        | none => exact Cslib.OracleComp.IsCostBounded.pure (eval r₀) (g * (p + 1))
        | some r' => exact ih r'
    have htotal := Cslib.OracleComp.IsCostBounded.liftBind (corrQuery (eval r₀))
      (fun vCurr ↦ queryCandidates eval (neigh r₀) >>= fun candVals ↦
        match selectCandidate t vCurr candVals with
        | some r' => evolveSQ eval neigh t g r'
        | none => pure (eval r₀))
      (p + g * (p + 1)) hstep
    have heq : p + g * (p + 1) + 1 = (g + 1) * (p + 1) := by ring
    simpa only [heq] using htotal

/-- Running `evolveSQ` against `answer` evaluates `detEvolve` under
`r ↦ answer (corrQuery (eval r))`. -/
theorem run_evolveSQ_eq_detEvolve {X R : Type} (eval : R → X → Bool)
    (neigh : R → List R) (t : ℝ)
    (answer : Cslib.MachineLearning.StatisticalQuery.Query X → ℝ)
    (g : ℕ) (r₀ : R) :
    Cslib.MachineLearning.StatisticalQuery.run (evolveSQ eval neigh t g r₀) answer =
      eval (detEvolve neigh (fun r ↦ answer (corrQuery (eval r))) t g r₀) := by
  induction g generalizing r₀ with
  | zero =>
    unfold Cslib.MachineLearning.StatisticalQuery.run evolveSQ detEvolve
    rfl
  | succ g ih =>
    unfold Cslib.MachineLearning.StatisticalQuery.run evolveSQ detEvolve
    rw [Cslib.OracleComp.interpret_id_query_bind, interpret_queryCandidates_bind]
    cases selectCandidate t (answer (corrQuery (eval r₀)))
      (List.map (fun r' ↦ (r', answer (corrQuery (eval r')))) (neigh r₀)) with
    | none => rfl
    | some r' => exact ih r'

/-- Bounded-neighborhood evolutionary convergence against `τ`-accurate valuations implies
`StatisticalQuery.LearnsStateless` with error `ε / 2`. -/
theorem evolveSQ_learnsStateless {X : Type} [Fintype X] {R : Type} (eval : R → X → Bool)
    (neigh : R → List R) (t : ℝ) (g : ℕ) (r₀ : R) (D : PMF X)
    (C : Cslib.MachineLearning.PACLearning.ConceptClass X Bool) {τ ε : ℝ}
    (hevolve : ∀ f ∈ C, ∀ v : R → ℝ,
      (∀ r, |v r - Cslib.MachineLearning.StatisticalQuery.corr D f (eval r)| ≤ τ) →
      1 - ε ≤ Cslib.MachineLearning.StatisticalQuery.corr D f
        (eval (detEvolve neigh v t g r₀))) :
    Cslib.MachineLearning.StatisticalQuery.LearnsStateless
      (evolveSQ eval neigh t g r₀) D C τ (ε / 2) := by
  intro c hc answer hanswer
  rw [run_evolveSQ_eq_detEvolve]
  have hv : ∀ r,
      |answer (corrQuery (eval r)) -
        Cslib.MachineLearning.StatisticalQuery.corr D c (eval r)| ≤ τ := fun r ↦ by
    rw [← expect_corrQuery_eq_corr]
    exact hanswer (corrQuery (eval r))
  have hcorr := hevolve c hc (fun r ↦ answer (corrQuery (eval r))) hv
  rw [Cslib.MachineLearning.StatisticalQuery.corr_eq_one_sub_two_mul_disagreement] at hcorr
  linarith

/-- Adaptive statistical-query learning via `evolveSQ` yields a PAC learner from
`(g * (p + 1)) * m` examples. -/
theorem evolveSQ_isPACLearnerFor {X : Type} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {R : Type} (eval : R → X → Bool)
    {neigh : R → List R} {p : ℕ} (hneigh : ∀ r, (neigh r).length ≤ p)
    (t : ℝ) (g : ℕ) (r₀ : R) (D : PMF X)
    (C : Cslib.MachineLearning.PACLearning.ConceptClass X Bool)
    {τ : ℝ} (hτ : 0 ≤ τ) {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hlearns : Cslib.MachineLearning.StatisticalQuery.Learns
      (evolveSQ eval neigh t g r₀) D C τ ε.val)
    {m : ℕ} (hm : (g * (p + 1) : ℕ) * (2 * Real.exp (-(m * τ ^ 2) / 2)) ≤ δ.val) :
    Cslib.MachineLearning.PACLearning.IsPACLearnerFor ((g * (p + 1)) * m) ε δ C
      (Cslib.MachineLearning.StatisticalQuery.realizable D C) :=
  hlearns.isPACLearnerFor (isQueryBounded_evolveSQ eval hneigh t g r₀) hτ hm

end GeneralDomain

section BooleanCube

/-- Representation-independent exponential lower bound for evolving all `n`-bit parity functions
under the uniform distribution: any `g`-generation trajectory with neighborhood size `≤ p` reaching
correlation `≥ 1 - ε` (`0 ≤ ε < 1`) under tolerance `τ > 0` satisfies
`2^n ≤ (g * (p + 1)) / τ^2 + 1 / (1 - ε)^2`. -/
theorem parity_evolvability_sq_lower_bound {n : ℕ} {R : Type}
    (eval : R → Cslib.BooleanFunction n)
    {neigh : R → List R} {p : ℕ} (hneigh : ∀ r, (neigh r).length ≤ p)
    (t : ℝ) (g : ℕ) (r₀ : R) {τ ε : ℝ} (hτ : 0 < τ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hevolve : ∀ S : Finset (Fin n), ∀ v : R → ℝ,
      (∀ r, |v r - Cslib.MachineLearning.StatisticalQuery.corr
        (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n))
        (Cslib.parityOn S) (eval r)| ≤ τ) →
      1 - ε ≤ Cslib.MachineLearning.StatisticalQuery.corr
        (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n))
        (Cslib.parityOn S) (eval (detEvolve neigh v t g r₀))) :
    (2 : ℝ) ^ n ≤ (g * (p + 1) : ℕ) / τ ^ 2 + 1 / (1 - ε) ^ 2 := by
  let C : Cslib.MachineLearning.PACLearning.ConceptClass (Cslib.BitString n) Bool :=
    Set.range (@Cslib.parityOn (Fin n))
  have hstateless : Cslib.MachineLearning.StatisticalQuery.LearnsStateless
      (evolveSQ eval neigh t g r₀)
      (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n)) C τ (ε / 2) := by
    refine evolveSQ_learnsStateless eval neigh t g r₀ _ C ?_
    rintro _ ⟨S, rfl⟩ v hv
    exact hevolve S v hv
  have hbound := hstateless.two_pow_card_le_of_parityOn_mem
    (isQueryBounded_evolveSQ eval hneigh t g r₀)
    (fun S ↦ ⟨S, rfl⟩) hτ (by linarith) (by linarith)
  simpa only [Fintype.card_fin, show 1 - 2 * (ε / 2) = 1 - ε by ring] using hbound

/-- Monotone Boolean conjunction on `n` bits with variable support `S ⊆ Fin n`. -/
def monotoneConjunction {n : ℕ} (S : Finset (Fin n)) : Cslib.BooleanFunction n :=
  fun x ↦ decide (∀ i ∈ S, x i = true)

/-- `monotoneConjunction S x = true` iff all coordinates in `S` equal `true`. -/
theorem monotoneConjunction_eq_true_iff {n : ℕ} {S : Finset (Fin n)} {x : Cslib.BitString n} :
    monotoneConjunction S x = true ↔ ∀ i ∈ S, x i = true := by
  simp only [monotoneConjunction, decide_eq_true_eq]

private def monotoneConjunctionTrueEquiv {n : ℕ} (S : Finset (Fin n)) :
    {x : Cslib.BitString n // monotoneConjunction S x = true} ≃ (↥(Sᶜ) → Bool) where
  toFun x j := x.1 j.1
  invFun g :=
    ⟨fun i ↦ if hi : i ∈ S then true else g ⟨i, mem_compl.mpr hi⟩, by
      rw [monotoneConjunction_eq_true_iff]
      intro i hi
      simp only [hi, ↓reduceDIte]⟩
  left_inv x := by
    ext i
    have hx := monotoneConjunction_eq_true_iff.mp x.2
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceDIte, hx i hi]
    · simp only [hi, ↓reduceDIte]
  right_inv g := by
    funext ⟨i, hi⟩
    have hiS : i ∉ S := mem_compl.mp hi
    simp only [hiS, ↓reduceDIte]

/-- Number of satisfying assignments of `monotoneConjunction S` in `BitString n`. -/
theorem card_filter_monotoneConjunction_eq_true {n : ℕ} (S : Finset (Fin n)) :
    #{x : Cslib.BitString n | monotoneConjunction S x = true} = 2 ^ (n - S.card) := by
  calc #{x : Cslib.BitString n | monotoneConjunction S x = true}
      = Fintype.card {x : Cslib.BitString n // monotoneConjunction S x = true} := by
        rw [Fintype.card_subtype]
    _ = Fintype.card (↥(Sᶜ) → Bool) := Fintype.card_congr (monotoneConjunctionTrueEquiv S)
    _ = 2 ^ Sᶜ.card := by simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ = 2 ^ (n - S.card) := by rw [card_compl, Fintype.card_fin]

private theorem sum_uniform_bitVal_monotoneConjunction {n : ℕ} (S : Finset (Fin n)) :
    ∑ x : Cslib.BitString n,
      (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n) x).toReal *
        Cslib.BitString.bitVal ℝ (monotoneConjunction S x) = (2⁻¹ : ℝ) ^ S.card := by
  have hcard : Fintype.card (Cslib.BitString n) = 2 ^ n := by
    change Fintype.card (Fin n → Bool) = 2 ^ n
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hmass : ∀ x : Cslib.BitString n,
      (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n) x).toReal =
        ((2 : ℝ) ^ n)⁻¹ := fun x ↦ by
    rw [Cslib.Probability.PMF.uniformOfFintype_apply, hcard, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat]
  simp only [hmass, ← mul_sum]
  have hsum : ∑ x : Cslib.BitString n, Cslib.BitString.bitVal ℝ (monotoneConjunction S x) =
      (2 : ℝ) ^ (n - S.card) := by
    have hboole : ∀ x : Cslib.BitString n,
        Cslib.BitString.bitVal ℝ (monotoneConjunction S x) =
          if monotoneConjunction S x = true then (1 : ℝ) else 0 := fun x ↦ by
      cases monotoneConjunction S x <;> rfl
    simp only [hboole, sum_boole, card_filter_monotoneConjunction_eq_true, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hsum]
  have hle : S.card ≤ n := by simpa only [Fintype.card_fin] using S.card_le_univ
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - S.card) * (2 : ℝ) ^ S.card := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow, mul_inv, mul_comm (((2 : ℝ) ^ (n - S.card))⁻¹), mul_assoc,
    inv_mul_cancel₀ (by positivity), mul_one, inv_pow]

/-- Exact closed-form correlation between `monotoneConjunction T` and `monotoneConjunction S` under
the uniform distribution on `BitString n`. -/
theorem corr_uniformOfFintype_monotoneConjunction {n : ℕ} (T S : Finset (Fin n)) :
    Cslib.MachineLearning.StatisticalQuery.corr
      (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n))
      (monotoneConjunction T) (monotoneConjunction S) =
      1 - 2 * (2⁻¹ : ℝ) ^ T.card - 2 * (2⁻¹ : ℝ) ^ S.card + 4 * (2⁻¹ : ℝ) ^ (T ∪ S).card := by
  have hand : ∀ x : Cslib.BitString n,
      (monotoneConjunction T x && monotoneConjunction S x) = monotoneConjunction (T ∪ S) x := by
    intro x
    rw [Bool.eq_iff_iff, Bool.and_eq_true, monotoneConjunction_eq_true_iff,
      monotoneConjunction_eq_true_iff, monotoneConjunction_eq_true_iff]
    exact ⟨fun ⟨hT, hS⟩ i hi ↦ (mem_union.mp hi).elim (hT i) (hS i),
      fun h ↦ ⟨fun i hi ↦ h i (mem_union_left S hi), fun i hi ↦ h i (mem_union_right T hi)⟩⟩
  have hdis : Cslib.MachineLearning.StatisticalQuery.disagreement
      (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n))
      (monotoneConjunction T) (monotoneConjunction S) =
      (2⁻¹ : ℝ) ^ T.card + (2⁻¹ : ℝ) ^ S.card - 2 * (2⁻¹ : ℝ) ^ (T ∪ S).card := by
    unfold Cslib.MachineLearning.StatisticalQuery.disagreement
    have hterm : ∀ x : Cslib.BitString n,
        (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n) x).toReal *
            (if monotoneConjunction T x = monotoneConjunction S x then 0 else 1) =
          (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n) x).toReal *
            Cslib.BitString.bitVal ℝ (monotoneConjunction T x) +
          (Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n) x).toReal *
            Cslib.BitString.bitVal ℝ (monotoneConjunction S x) -
          2 * ((Cslib.Probability.PMF.uniformOfFintype (Cslib.BitString n) x).toReal *
            Cslib.BitString.bitVal ℝ (monotoneConjunction (T ∪ S) x)) := fun x ↦ by
      have h0 : (if monotoneConjunction T x = monotoneConjunction S x then (0 : ℝ) else 1) =
          Cslib.BitString.bitVal ℝ (monotoneConjunction T x) +
          Cslib.BitString.bitVal ℝ (monotoneConjunction S x) -
          2 * Cslib.BitString.bitVal ℝ (monotoneConjunction T x && monotoneConjunction S x) := by
        cases monotoneConjunction T x <;> cases monotoneConjunction S x <;>
          norm_num [Cslib.BitString.bitVal]
      rw [h0, hand x]
      ring
    simp only [hterm, sum_sub_distrib, sum_add_distrib, ← mul_sum,
      sum_uniform_bitVal_monotoneConjunction]
  rw [Cslib.MachineLearning.StatisticalQuery.corr_eq_one_sub_two_mul_disagreement, hdis]
  ring

/-- Conjunction support sets `S ⊆ Fin n` of cardinality at most `q`. -/
@[ext]
structure BoundedConjunction (n q : ℕ) where
  /-- Included variable indices. -/
  support : Finset (Fin n)
  /-- Upper bound on support size. -/
  card_le : support.card ≤ q

instance instDecidableEqBoundedConjunction (n q : ℕ) : DecidableEq (BoundedConjunction n q) :=
  fun a b ↦ decidable_of_iff (a.support = b.support) BoundedConjunction.ext_iff.symm

instance instFintypeBoundedConjunction (n q : ℕ) : Fintype (BoundedConjunction n q) :=
  Fintype.ofEquiv {S : Finset (Fin n) // S.card ≤ q}
    { toFun := fun s ↦ ⟨s.1, s.2⟩
      invFun := fun r ↦ ⟨r.support, r.card_le⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Symmetric-difference radius-`2` local mutation neighborhood on `BoundedConjunction n q`. -/
def monotoneNeighborhood {n q : ℕ} (r : BoundedConjunction n q) :
    Finset (BoundedConjunction n q) :=
  univ.filter fun r' ↦ (symmDiff r.support r'.support).card ≤ 2

/-- Every `monotoneNeighborhood r` has size at most `(n + 1) ^ 2`. -/
theorem card_monotoneNeighborhood_le {n q : ℕ} (r : BoundedConjunction n q) :
    (monotoneNeighborhood r).card ≤ (n + 1) ^ 2 := by
  let smallSets : Finset (Finset (Fin n)) :=
    powersetCard 0 univ ∪ powersetCard 1 univ ∪ powersetCard 2 univ
  have hinj : Set.InjOn (fun r' : BoundedConjunction n q ↦ symmDiff r.support r'.support)
      (monotoneNeighborhood r) := by
    intro a _ b _ hab
    ext1
    have key := congrArg (symmDiff r.support) hab
    simpa only [symmDiff_symmDiff_cancel_left] using key
  have hmaps : (monotoneNeighborhood r).image
      (fun r' : BoundedConjunction n q ↦ symmDiff r.support r'.support) ⊆ smallSets := by
    intro Δ hΔ
    rcases mem_image.mp hΔ with ⟨r', hr', rfl⟩
    simp only [monotoneNeighborhood, mem_filter, mem_univ, true_and] at hr'
    have hcases : (symmDiff r.support r'.support).card = 0 ∨
        (symmDiff r.support r'.support).card = 1 ∨
        (symmDiff r.support r'.support).card = 2 := by omega
    simp only [smallSets, mem_union, mem_powersetCard_univ]
    exact hcases.elim (fun h0 ↦ Or.inl (Or.inl h0))
      (fun h12 ↦ h12.elim (fun h1 ↦ Or.inl (Or.inr h1)) Or.inr)
  have hcard1 : (monotoneNeighborhood r).card ≤ smallSets.card := by
    rw [← card_image_of_injOn hinj]
    exact card_le_card hmaps
  have hcard2 : smallSets.card ≤ n.choose 0 + n.choose 1 + n.choose 2 := by
    calc smallSets.card
        ≤ (powersetCard 0 (univ : Finset (Fin n)) ∪ powersetCard 1 univ).card +
            (powersetCard 2 (univ : Finset (Fin n))).card := card_union_le _ _
      _ ≤ (powersetCard 0 (univ : Finset (Fin n))).card +
            (powersetCard 1 (univ : Finset (Fin n))).card +
            (powersetCard 2 (univ : Finset (Fin n))).card := by
          linarith [card_union_le (powersetCard 0 (univ : Finset (Fin n))) (powersetCard 1 univ)]
      _ = n.choose 0 + n.choose 1 + n.choose 2 := by
          simp only [card_powersetCard, card_univ, Fintype.card_fin]
  have hchoose2 : n.choose 2 ≤ n * n := by
    rw [Nat.choose_two_right]
    refine Nat.div_le_of_le_mul ?_
    calc n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      _ ≤ 2 * (n * n) := by omega
  have h01 : n.choose 0 = 1 ∧ n.choose 1 = n := ⟨Nat.choose_zero_right n, Nat.choose_one_right n⟩
  nlinarith [hcard1, hcard2, hchoose2, h01.1, h01.2]

end BooleanCube

end CslibFrontier.MachineLearning.Evolvability
