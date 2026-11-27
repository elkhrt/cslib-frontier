/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Computability.RandomizedCost
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Foundations.Quantum.DensityMatrix.MaxInformation
import CslibFrontier.Foundations.Data.ENat.IInf
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-Way Classical and Quantum Communication Complexity and Message Compression

This module defines two-party one-way communication complexity models for partial functions
`f : X → Y → Option Z`:

* **Classical one-way protocols**: deterministic (`DetOneWay`) and public-coin (`PublicCoinOneWay`)
  protocols, with worst-case error, distributional error under `μ : PMF (X × Y)`, and worst-case-`y`
  distributional error under `μ_X : PMF X`, yielding `R¹_ε(f)`, `R^{1,μ}_ε(f)`, `R^{1,μ_X}_ε(f)`.
* **Classical one-way Yao minimax principle**: `R¹_ε(f) = sup_μ R^{1,μ}_ε(f)` via
  `Cslib.RandomizedCost`.
* **Quantum one-way protocols**: unassisted (`QuantumOneWay`) and entanglement-assisted
  (`EntangledQuantumOneWay`) protocols, yielding `Q¹_ε(f)`, `Q^{1,μ}_ε(f)`, `Q^{1,μ_X}_ε(f)`
  and `Q^{1,*}_ε(f)`, `Q^{1,μ,*}_ε(f)`, `Q^{1,μ_X,*}_ε(f)`.
* **JRS message compression (rejection sampling)**: given a classical channel `cond : X → PMF C`
  dominated by `2^k • σ`, a public-coin one-way protocol sending `k + ⌈log₂ max(1, ln(1/η))⌉`
  bits simulates `cond x` within total variation distance `η` for every `x`, proving the
  Jain–Radhakrishnan–Sen message-compression theorem `T_η(X : C) ≤ I_max(X : C) + O(log log (1/η))`.

All results are proved from first principles under standard Lean axioms.

## Main definitions

* `CslibFrontier.Communication.DetOneWay`, `CslibFrontier.Communication.PublicCoinOneWay`: classical
  deterministic and public-coin one-way protocols.
* `CslibFrontier.Communication.classicalOneWayComplexity`,
  `CslibFrontier.Communication.classicalOneWayDistComplexity`,
  `CslibFrontier.Communication.classicalOneWayWorstYComplexity`: `R¹_ε`, `R^{1,μ}_ε`, `R^{1,μ_X}_ε`.
* `CslibFrontier.Communication.QuantumOneWay`, `CslibFrontier.Communication.EntangledQuantumOneWay`:
  quantum one-way protocols without and with shared entanglement.
* `CslibFrontier.Communication.quantumOneWayComplexity`,
  `CslibFrontier.Communication.quantumOneWayDistComplexity`,
  `CslibFrontier.Communication.quantumOneWayWorstYComplexity`,
  `CslibFrontier.Communication.entangledQuantumOneWayComplexity`,
  `CslibFrontier.Communication.entangledQuantumOneWayDistComplexity`,
  `CslibFrontier.Communication.entangledQuantumOneWayWorstYComplexity`.

## Main results

* `CslibFrontier.Communication.classicalOneWayComplexity_eq_iSup_distComplexity`: Yao's minimax
  principle for classical one-way communication complexity.
* `CslibFrontier.Communication.jrs_rejection_sampling_simulation`: pointwise rejection-sampling
  one-way simulation of a classical channel within total variation distance `η`.
* `CslibFrontier.Communication.jrs_message_compression`: Jain–Radhakrishnan–Sen message compression
  bound `T_η(X : C) ≤ I_max(X : C) + O(log log (1/η))`.
* `CslibFrontier.Communication.EntangledQuantumOneWay.maxInformation_le`: `I_max(X : D B) ≤ 2 a`
  for any `a`-qubit entanglement-assisted protocol.
-/

public section

namespace CslibFrontier.Communication

open Matrix Finset Cslib Cslib.Quantum Cslib.Probability
open scoped MatrixOrder ComplexOrder Kronecker ENNReal Cslib.Probability.PMF

/-! ### Partial-function relation and classical one-way protocols -/

section Classical

variable {X Y Z : Type*}

/-- Relation corresponding to a partial function `f : X → Y → Option Z`: inputs with `f x y = none`
impose no constraint (error is `0`), matching the partial-function convention. -/
def partialRel (f : X → Y → Option Z) (x : X) (y : Y) (z : Z) : Prop :=
  ∀ z₀ : Z, f x y = some z₀ → z = z₀

/-- A deterministic one-way communication protocol where Alice sends `msgBits` bits to Bob. -/
structure DetOneWay (X Y Z : Type*) where
  /-- Number of bits sent by Alice. -/
  msgBits : ℕ
  /-- Alice's deterministic encoder. -/
  alice : X → BitString msgBits
  /-- Bob's deterministic decoder. -/
  bob : Y → BitString msgBits → Z

/-- Deterministic one-way protocols as a `Cslib.RandomizedCost` model on `X × Y`. -/
def DetOneWay.randomizedCost (X Y Z : Type*) : RandomizedCost (DetOneWay X Y Z) (X × Y) Z where
  eval p q := p.bob q.2 (p.alice q.1)
  cost p := p.msgBits

/-- A classical public-coin one-way protocol is a distribution over deterministic one-way
protocols. -/
abbrev PublicCoinOneWay (X Y Z : Type*) : Type _ :=
  PMF (DetOneWay X Y Z)

/-- Worst-case communication cost `CC(P)` (maximum message length in support) of a public-coin
one-way protocol. -/
@[expose] noncomputable def PublicCoinOneWay.commCost (P : PublicCoinOneWay X Y Z) : ℕ∞ :=
  PMF.maxCost DetOneWay.msgBits P

/-- Pointwise error probability `err_{x,y}(P, f)` of a public-coin one-way protocol. -/
@[expose] noncomputable def PublicCoinOneWay.pointError (P : PublicCoinOneWay X Y Z)
    (f : X → Y → Option Z) (x : X) (y : Y) : ℝ :=
  (DetOneWay.randomizedCost X Y Z).errorProb P (fun q z ↦ partialRel f q.1 q.2 z) (x, y)

/-- Output distribution of a public-coin one-way protocol on `(x, y)`. -/
@[expose] noncomputable def PublicCoinOneWay.outputPMF (P : PublicCoinOneWay X Y Z) (x : X) (y : Y)
  :
    PMF Z :=
  P.map fun p ↦ p.bob y (p.alice x)

/-- Distributional error `err(P, f, μ) = E_{(x,y) ← μ}[err_{x,y}(P, f)]`. -/
@[expose] noncomputable def PublicCoinOneWay.distError [Fintype X] [Fintype Y]
    (P : PublicCoinOneWay X Y Z) (f : X → Y → Option Z) (μ : PMF (X × Y)) : ℝ :=
  ∑ q : X × Y, (μ q).toReal * P.pointError f q.1 q.2

/-- Classical public-coin one-way communication complexity `R¹_ε(f)`. -/
@[expose] noncomputable def classicalOneWayComplexity (ε : ℝ) (f : X → Y → Option Z) : ℕ∞ :=
  (DetOneWay.randomizedCost X Y Z).ecomplexity ε (fun q z ↦ partialRel f q.1 q.2 z) Set.univ

/-- Distributional classical one-way communication complexity `R^{1,μ}_ε(f)`. -/
@[expose] noncomputable def classicalOneWayDistComplexity [Fintype X] [Fintype Y]
    (ε : ℝ) (f : X → Y → Option Z) (μ : PMF (X × Y)) : ℕ∞ :=
  ⨅ P : {P : PublicCoinOneWay X Y Z // P.distError f μ ≤ ε}, P.1.commCost

/-- Worst-case-`y` distributional classical one-way communication complexity `R^{1,μ_X}_ε(f)`. -/
@[expose] noncomputable def classicalOneWayWorstYComplexity [Fintype X]
    (ε : ℝ) (f : X → Y → Option Z) (μX : PMF X) : ℕ∞ :=
  ⨅ P : {P : PublicCoinOneWay X Y Z // ∀ y : Y,
    ∑ x : X, (μX x).toReal * P.pointError f x y ≤ ε}, P.1.commCost

@[simp]
theorem PublicCoinOneWay.commCost_pure (p : DetOneWay X Y Z) :
    PublicCoinOneWay.commCost (PMF.pure p) = (p.msgBits : ℕ∞) := by
  simp [PublicCoinOneWay.commCost, PMF.maxCost, PMF.support_pure]

@[simp]
theorem PublicCoinOneWay.outputPMF_pure (p : DetOneWay X Y Z) (x : X) (y : Y) :
    PublicCoinOneWay.outputPMF (PMF.pure p) x y = PMF.pure (p.bob y (p.alice x)) := by
  simp [PublicCoinOneWay.outputPMF]

theorem PublicCoinOneWay.pointError_le_one (P : PublicCoinOneWay X Y Z)
    (f : X → Y → Option Z) (x : X) (y : Y) :
    P.pointError f x y ≤ 1 := by
  exact RandomizedCost.errorProb_le_one

theorem PublicCoinOneWay.distError_product [Fintype X] [Fintype Y]
    (P : PublicCoinOneWay X Y Z) (f : X → Y → Option Z) (μX : PMF X) (μY : PMF Y) :
    P.distError f (μX.bind fun x ↦ μY.map fun y ↦ (x, y)) =
      ∑ y : Y, (μY y).toReal * ∑ x : X, (μX x).toReal * P.pointError f x y := by
  simp only [PublicCoinOneWay.distError, Fintype.sum_prod_type,
    Cslib.Probability.PMF.bind_map_prodMk_apply, ENNReal.toReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

theorem PublicCoinOneWay.distError_filter_split [Fintype X] [Fintype Y]
    (P : PublicCoinOneWay X Y Z) (f : X → Y → Option Z) (μ : PMF (X × Y))
    (p : X × Y → Prop) [DecidablePred p] :
    P.distError f μ =
      (∑ q ∈ Finset.univ.filter p, (μ q).toReal * P.pointError f q.1 q.2) +
      (∑ q ∈ Finset.univ.filter (fun q ↦ ¬ p q), (μ q).toReal * P.pointError f q.1 q.2) := by
  unfold PublicCoinOneWay.distError
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem PublicCoinOneWay.pointError_eq_one_sub_outputPMF
    (P : PublicCoinOneWay X Y Z) (f : X → Y → Option Z) (x : X) (y : Y) :
    P.pointError f x y =
      match f x y with
      | none => 0
      | some z₀ => 1 - (P.outputPMF x y z₀).toReal := by
  classical
  cases h : f x y with
  | none =>
    simp only [pointError, RandomizedCost.errorProb, DetOneWay.randomizedCost, PMF.errorProb,
      partialRel, h]
    have hempty : {p : DetOneWay X Y Z | ¬ ∀ z₀, (none : Option Z) = some z₀ →
        p.bob y (p.alice x) = z₀} = ∅ := by
      ext p; simp
    rw [hempty, MeasureTheory.measure_empty, ENNReal.toReal_zero]
  | some z₀ =>
    simp only [pointError, RandomizedCost.errorProb, DetOneWay.randomizedCost, PMF.errorProb,
      partialRel, h]
    have hset : {p : DetOneWay X Y Z | ¬ ∀ z₁, some z₀ = some z₁ →
        p.bob y (p.alice x) = z₁} = {p | p.bob y (p.alice x) ≠ z₀} := by
      ext p; simp
    rw [hset]
    have hcomp : (P.toOuterMeasure {p | p.bob y (p.alice x) ≠ z₀}).toReal =
        1 - (P.toOuterMeasure {p | p.bob y (p.alice x) = z₀}).toReal := by
      have hsum : (P.toOuterMeasure {p | p.bob y (p.alice x) ≠ z₀}) +
          (P.toOuterMeasure {p | p.bob y (p.alice x) = z₀}) = 1 := by
        simp only [PMF.toOuterMeasure_apply]
        rw [← tsum_add]
        have hpt (p : DetOneWay X Y Z) :
            Set.indicator {p | p.bob y (p.alice x) ≠ z₀} (fun a ↦ P a) p +
              Set.indicator {p | p.bob y (p.alice x) = z₀} (fun a ↦ P a) p = P p := by
          by_cases hp : p.bob y (p.alice x) = z₀ <;> simp [hp]
        simp_rw [hpt]
        exact P.tsum_coe
      have hne1 : P.toOuterMeasure {p | p.bob y (p.alice x) ≠ z₀} ≠ ⊤ :=
        PMF.toOuterMeasure_ne_top _ _
      have hne2 : P.toOuterMeasure {p | p.bob y (p.alice x) = z₀} ≠ ⊤ :=
        PMF.toOuterMeasure_ne_top _ _
      have hr := congrArg ENNReal.toReal hsum
      rw [ENNReal.toReal_add hne1 hne2, ENNReal.toReal_one] at hr
      linarith
    rw [hcomp]
    congr 1
    rw [outputPMF, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl

/-- Construct a `PublicCoinOneWay` protocol from arbitrary finite public randomness `pub : PMF R`,
randomized encoder `alice : R → X → PMF (BitString k)`, and randomized decoder
`bob : R → Y → BitString k → PMF Z`, preserving the exact output distribution and cost `≤ k`. -/
noncomputable def PublicCoinOneWay.ofPublicPrivate [Fintype X] [Fintype Y]
    {R : Type*} (k : ℕ) (pub : PMF R)
    (alice : R → X → PMF (BitString k)) (bob : R → Y → BitString k → PMF Z)
    [Finite Z] : PublicCoinOneWay X Y Z :=
  pub.bind fun r ↦
    (PMF.pi (alice r)).bind fun a ↦
      (PMF.pi (fun y : Y ↦ PMF.pi (bob r y))).map fun b ↦
        ⟨k, a, b⟩

theorem PublicCoinOneWay.commCost_ofPublicPrivate_le [Fintype X] [Fintype Y]
    {R : Type*} [Finite Z] (k : ℕ) (pub : PMF R)
    (alice : R → X → PMF (BitString k)) (bob : R → Y → BitString k → PMF Z) :
    (PublicCoinOneWay.ofPublicPrivate k pub alice bob).commCost ≤ (k : ℕ∞) := by
  refine PMF.maxCost_le_iff.mpr fun p hp ↦ ?_
  rw [ofPublicPrivate, PMF.mem_support_bind_iff] at hp
  obtain ⟨r, -, hp⟩ := hp
  rw [PMF.mem_support_bind_iff] at hp
  obtain ⟨a, -, hp⟩ := hp
  rw [PMF.mem_support_map_iff] at hp
  obtain ⟨b, -, rfl⟩ := hp
  exact le_rfl

theorem PublicCoinOneWay.outputPMF_ofPublicPrivate [Fintype X] [Fintype Y]
    {R : Type*} [Finite Z] (k : ℕ) (pub : PMF R)
    (alice : R → X → PMF (BitString k)) (bob : R → Y → BitString k → PMF Z)
    (x : X) (y : Y) :
    (PublicCoinOneWay.ofPublicPrivate k pub alice bob).outputPMF x y =
      pub.bind fun r ↦ (alice r x).bind fun m ↦ bob r y m := by
  classical
  simp only [outputPMF, ofPublicPrivate, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine congrArg (pub.bind ·) (funext fun r ↦ ?_)
  have hbob (a : X → BitString k) :
      (PMF.pi (fun y' : Y ↦ PMF.pi (bob r y'))).map (fun b ↦ b y (a x)) = bob r y (a x) := by
    have h1 : (fun b : ∀ y' : Y, BitString k → Z ↦ b y (a x)) =
        (fun f : BitString k → Z ↦ f (a x)) ∘ (fun b ↦ b y) := rfl
    rw [h1, ← PMF.map_comp, PMF.pi_map_eval, PMF.pi_map_eval]
  simp_rw [hbob]
  have halice :
      (PMF.pi (alice r)).bind (fun a ↦ bob r y (a x)) =
        ((PMF.pi (alice r)).map (fun a ↦ a x)).bind (fun m ↦ bob r y m) := by
    rw [PMF.bind_map]; rfl
  rw [halice, PMF.pi_map_eval]

/-- Distributional complexity over public-coin protocols equals deterministic distributional
complexity (coin-fixing). -/
theorem classicalOneWayDistComplexity_eq_det [Fintype X] [Fintype Y]
    (ε : ℝ) (f : X → Y → Option Z) (μ : PMF (X × Y)) :
    classicalOneWayDistComplexity ε f μ =
      (DetOneWay.randomizedCost X Y Z).distributionalComplexity ε
        (fun q z ↦ partialRel f q.1 q.2 z) μ := by
  classical
  apply le_antisymm
  · refine ENat.le_iInf_subtype_natCast_iff.mpr fun p hp ↦ ?_
    have hpure : PublicCoinOneWay.distError (PMF.pure p) f μ ≤ ε := by
      have hpt (q : X × Y) :
          PublicCoinOneWay.pointError (PMF.pure p) f q.1 q.2 =
            if partialRel f q.1 q.2 (p.bob q.2 (p.alice q.1)) then 0 else 1 := by
        unfold PublicCoinOneWay.pointError
        have h := (DetOneWay.randomizedCost X Y Z).errorProb_pure p
          (fun r z ↦ partialRel f r.1 r.2 z) q
        rw [h]
        by_cases hq : partialRel f q.1 q.2 (p.bob q.2 (p.alice q.1)) <;>
          simp [hq, DetOneWay.randomizedCost]
      have hdist : PublicCoinOneWay.distError (PMF.pure p) f μ =
          (DetOneWay.randomizedCost X Y Z).distributionalError p μ
            (fun r z ↦ partialRel f r.1 r.2 z) := by
        simp only [PublicCoinOneWay.distError, RandomizedCost.distributionalError, PMF.errorProb,
          hpt, PMF.toOuterMeasure_apply_fintype, Set.indicator, Set.mem_ofPred_eq,
          DetOneWay.randomizedCost]
        rw [ENNReal.toReal_sum (fun _ _ ↦ by split_ifs <;> simp [PMF.apply_ne_top])]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        by_cases hq : partialRel f q.1 q.2 (p.bob q.2 (p.alice q.1)) <;> simp [hq]
      rwa [hdist]
    have hcost : PublicCoinOneWay.commCost (PMF.pure p) = (p.msgBits : ℕ∞) := by
      simp [PublicCoinOneWay.commCost, PMF.maxCost, PMF.support_pure]
    exact (iInf_le (fun P : {P : PublicCoinOneWay X Y Z // P.distError f μ ≤ ε} ↦ P.1.commCost)
      ⟨PMF.pure p, hpure⟩).trans (by rw [hcost]; rfl)
  · refine ENat.le_iInf_subtype_iff.mpr fun P hP ↦ ?_
    have havg : ∃ p ∈ P.support,
        (DetOneWay.randomizedCost X Y Z).distributionalError p μ
          (fun q z ↦ partialRel f q.1 q.2 z) ≤ ε := by
      by_contra hall
      push Not at hall
      have hP_summ : Summable fun p : DetOneWay X Y Z ↦ (P p).toReal :=
        Cslib.Probability.PMF.summable_toReal P
      have hP_tsum : ∑' p : DetOneWay X Y Z, (P p).toReal = 1 :=
        Cslib.Probability.PMF.tsum_toReal P
      have hgt : ε < P.distError f μ := by
        have hswap : P.distError f μ =
            ∑' p : DetOneWay X Y Z, (P p).toReal *
              (DetOneWay.randomizedCost X Y Z).distributionalError p μ
                (fun q z ↦ partialRel f q.1 q.2 z) := by
          simp only [PublicCoinOneWay.distError, PublicCoinOneWay.pointError,
            RandomizedCost.errorProb, RandomizedCost.distributionalError, PMF.errorProb,
            PMF.toOuterMeasure_apply, Set.indicator_apply, Set.mem_ofPred_eq,
            DetOneWay.randomizedCost]
          have hterm (q : X × Y) :
              (μ q).toReal * (∑' p : DetOneWay X Y Z,
                if ¬ partialRel f q.1 q.2 (p.bob q.2 (p.alice q.1)) then P p else 0).toReal =
              ∑' p : DetOneWay X Y Z, (P p).toReal *
                (if ¬ partialRel f q.1 q.2 (p.bob q.2 (p.alice q.1)) then (μ q).toReal else 0) := by
            rw [ENNReal.tsum_toReal_eq (fun p ↦ by
              split_ifs <;> simp [PMF.apply_ne_top]), ← tsum_mul_left]
            refine tsum_congr fun p ↦ ?_
            split_ifs <;> simp [mul_comm]
          simp_rw [hterm]
          rw [← Summable.tsum_finsetSum (fun q _ ↦
            Summable.of_nonneg_of_le (fun p ↦ by split_ifs <;> positivity)
              (fun p ↦ by
                by_cases hp : partialRel f q.1 q.2 (p.bob q.2 (p.alice q.1))
                · simp only [hp, not_true_eq_false, ite_false, mul_zero]; positivity
                · simp [hp])
              (hP_summ.mul_right (μ q).toReal))]
          refine tsum_congr fun p ↦ ?_
          rw [ENNReal.tsum_toReal_eq (fun q ↦ by split_ifs <;> simp [PMF.apply_ne_top]),
            tsum_fintype, ← Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          split_ifs <;> simp
        rw [hswap]
        obtain ⟨p₀, hp₀⟩ := P.support_nonempty
        have hpos : 0 < (P p₀).toReal :=
          ENNReal.toReal_pos hp₀ (P.apply_ne_top p₀)
        have h1 : ∑' p : DetOneWay X Y Z, (P p).toReal * ε = ε := by
          rw [tsum_mul_right, hP_tsum, one_mul]
        have hle_pt (p : DetOneWay X Y Z) :
            (P p).toReal * ε ≤ (P p).toReal *
              (DetOneWay.randomizedCost X Y Z).distributionalError p μ
                (fun q z ↦ partialRel f q.1 q.2 z) := by
          by_cases hp : p ∈ P.support
          · exact mul_le_mul_of_nonneg_left (hall p hp).le ENNReal.toReal_nonneg
          · simp [(P.apply_eq_zero_iff p).mpr hp]
        have hlt_pt : (P p₀).toReal * ε < (P p₀).toReal *
            (DetOneWay.randomizedCost X Y Z).distributionalError p₀ μ
              (fun q z ↦ partialRel f q.1 q.2 z) :=
          mul_lt_mul_of_pos_left (hall p₀ hp₀) hpos
        have hsum1 : Summable (fun p : DetOneWay X Y Z ↦ (P p).toReal * ε) :=
          hP_summ.mul_right ε
        have hsum2 : Summable (fun p : DetOneWay X Y Z ↦ (P p).toReal *
            (DetOneWay.randomizedCost X Y Z).distributionalError p μ
              (fun q z ↦ partialRel f q.1 q.2 z)) :=
          Summable.of_nonneg_of_le
            (fun p ↦ mul_nonneg ENNReal.toReal_nonneg (by
              unfold RandomizedCost.distributionalError PMF.errorProb
              exact ENNReal.toReal_nonneg))
            (fun p ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg (by
              unfold RandomizedCost.distributionalError PMF.errorProb
              exact Cslib.Probability.PMF.toOuterMeasure_toReal_le_one _ _))
            hP_summ
        rw [← h1]
        exact hsum1.tsum_lt_tsum hle_pt hlt_pt hsum2
      linarith
    obtain ⟨p, hp, herr⟩ := havg
    exact (RandomizedCost.distributionalComplexity_le_cost herr).trans (PMF.le_maxCost hp)

/-- (classical part): Yao's minimax principle for classical one-way communication complexity
of partial functions: `R¹_ε(f) = sup_μ R^{1,μ}_ε(f)`.
-/
theorem classicalOneWayComplexity_eq_iSup_distComplexity [Fintype X] [Fintype Y] [Nonempty Z]
    (ε : ℝ) (f : X → Y → Option Z) :
    classicalOneWayComplexity ε f =
      ⨆ μ : PMF (X × Y), classicalOneWayDistComplexity ε f μ := by
  have h0 : ∃ p : DetOneWay X Y Z, (DetOneWay.randomizedCost X Y Z).cost p = 0 :=
    ⟨⟨0, fun _ _ ↦ false, fun _ _ ↦ Classical.arbitrary Z⟩, rfl⟩
  rw [classicalOneWayComplexity,
    (DetOneWay.randomizedCost X Y Z).ecomplexity_eq_iSup_distributionalComplexity h0]
  simp only [Set.mem_univ, implies_true, iSup_pos]
  refine iSup_congr fun μ ↦ (classicalOneWayDistComplexity_eq_det ε f μ).symm

end Classical

/-! ### Quantum one-way protocols (unassisted and entanglement-assisted) -/

section Quantum

variable {X Y Z : Type*}

/-- An unassisted quantum one-way communication protocol sending `msgQubits` qubits from Alice to
Bob. -/
structure QuantumOneWay (X Y Z : Type*) [Fintype Z] where
  /-- Number of qubits transmitted from Alice to Bob. -/
  msgQubits : ℕ
  /-- Alice's state preparation map. -/
  alice : X → Matrix (BitString msgQubits) (BitString msgQubits) ℂ
  /-- Every prepared state is a valid density matrix. -/
  alice_density : ∀ x, IsDensityMatrix (alice x)
  /-- Bob's measurement POVM conditioned on his input `y`. -/
  bob : Y → POVM Z (BitString msgQubits)

/-- Output distribution of an unassisted quantum one-way protocol on `(x, y)`. -/
@[expose] noncomputable def QuantumOneWay.outputPMF [Fintype Z] (P : QuantumOneWay X Y Z) (x : X)
  (y : Y) :
    PMF Z :=
  (P.bob y).measureDensity (P.alice x) (P.alice_density x)

/-- Pointwise error probability `err_{x,y}(P, f)` of an unassisted quantum one-way protocol. -/
@[expose] noncomputable def QuantumOneWay.pointError [Fintype Z] (P : QuantumOneWay X Y Z)
    (f : X → Y → Option Z) (x : X) (y : Y) : ℝ :=
  match f x y with
  | none => 0
  | some z => 1 - (P.outputPMF x y z).toReal

/-- Distributional error `err(P, f, μ)` of an unassisted quantum one-way protocol. -/
@[expose] noncomputable def QuantumOneWay.distError [Fintype X] [Fintype Y] [Fintype Z]
    (P : QuantumOneWay X Y Z) (f : X → Y → Option Z) (μ : PMF (X × Y)) : ℝ :=
  ∑ q : X × Y, (μ q).toReal * P.pointError f q.1 q.2

/-- Unassisted quantum one-way worst-case communication complexity `Q¹_ε(f)`. -/
@[expose] noncomputable def quantumOneWayComplexity [Fintype Z] (ε : ℝ) (f : X → Y →
  Option Z) : ℕ∞ :=
  ⨅ P : {P : QuantumOneWay X Y Z // ∀ x y, P.pointError f x y ≤ ε}, (P.1.msgQubits : ℕ∞)

/-- Unassisted quantum one-way distributional communication complexity `Q^{1,μ}_ε(f)`. -/
@[expose] noncomputable def quantumOneWayDistComplexity [Fintype X] [Fintype Y] [Fintype Z]
    (ε : ℝ) (f : X → Y → Option Z) (μ : PMF (X × Y)) : ℕ∞ :=
  ⨅ P : {P : QuantumOneWay X Y Z // P.distError f μ ≤ ε}, (P.1.msgQubits : ℕ∞)

/-- Unassisted quantum one-way worst-case-`y` distributional complexity `Q^{1,μ_X}_ε(f)`. -/
@[expose] noncomputable def quantumOneWayWorstYComplexity [Fintype X] [Fintype Z]
    (ε : ℝ) (f : X → Y → Option Z) (μX : PMF X) : ℕ∞ :=
  ⨅ P : {P : QuantumOneWay X Y Z // ∀ y : Y,
    ∑ x : X, (μX x).toReal * P.pointError f x y ≤ ε}, (P.1.msgQubits : ℕ∞)

@[simp]
theorem QuantumOneWay.pointError_none [Fintype Z] (P : QuantumOneWay X Y Z)
    {f : X → Y → Option Z} {x : X} {y : Y} (h : f x y = none) :
    P.pointError f x y = 0 := by
  simp [QuantumOneWay.pointError, h]

theorem QuantumOneWay.pointError_some [Fintype Z] (P : QuantumOneWay X Y Z)
    {f : X → Y → Option Z} {x : X} {y : Y} {z : Z} (h : f x y = some z) :
    P.pointError f x y = 1 - (P.bob y).densityProb (P.alice x) z := by
  simp only [QuantumOneWay.pointError, QuantumOneWay.outputPMF, h, POVM.measureDensity_apply,
    ENNReal.toReal_ofReal ((P.bob y).densityProb_nonneg (P.alice_density x).posSemidef z)]

theorem QuantumOneWay.pointError_nonneg [Fintype Z] (P : QuantumOneWay X Y Z)
    (f : X → Y → Option Z) (x : X) (y : Y) :
    0 ≤ P.pointError f x y := by
  cases hf : f x y with
  | none => rw [P.pointError_none hf]
  | some z =>
    rw [P.pointError_some hf]
    have hle1 : (P.bob y).densityProb (P.alice x) z ≤ 1 := by
      calc (P.bob y).densityProb (P.alice x) z
          ≤ ∑ z' : Z, (P.bob y).densityProb (P.alice x) z' :=
            Finset.single_le_sum (fun z' _ ↦
              (P.bob y).densityProb_nonneg (P.alice_density x).posSemidef z') (mem_univ z)
        _ = 1 := by rw [(P.bob y).sum_densityProb, (P.alice_density x).trace_eq_one, Complex.one_re]
    linarith

theorem QuantumOneWay.outputPMF_apply_toReal [Fintype Z] (P : QuantumOneWay X Y Z)
    (x : X) (y : Y) (z : Z) :
    (P.outputPMF x y z).toReal = (P.bob y).densityProb (P.alice x) z := by
  simp only [QuantumOneWay.outputPMF, POVM.measureDensity_apply,
    ENNReal.toReal_ofReal ((P.bob y).densityProb_nonneg (P.alice_density x).posSemidef z)]

theorem QuantumOneWay.outputPMF_eq_of_alice_eq [Fintype Z] (P : QuantumOneWay X Y Z)
    {x₁ x₂ : X} (hx : P.alice x₁ = P.alice x₂) (y : Y) :
    P.outputPMF x₁ y = P.outputPMF x₂ y := by
  ext z
  simp [QuantumOneWay.outputPMF, POVM.measureDensity_apply, POVM.densityProb, hx]

theorem QuantumOneWay.distError_product [Fintype X] [Fintype Y] [Fintype Z]
    (P : QuantumOneWay X Y Z) (f : X → Y → Option Z) (μX : PMF X) (μY : PMF Y) :
    P.distError f (μX.bind fun x ↦ μY.map fun y ↦ (x, y)) =
      ∑ y : Y, (μY y).toReal * ∑ x : X, (μX x).toReal * P.pointError f x y := by
  simp only [QuantumOneWay.distError, Fintype.sum_prod_type,
    Cslib.Probability.PMF.bind_map_prodMk_apply, ENNReal.toReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

theorem exists_quantumOneWay_of_distComplexity_le [Fintype X] [Fintype Y] [Fintype Z]
    {ε : ℝ} {f : X → Y → Option Z} {μ : PMF (X × Y)} {a : ℕ}
    (h : quantumOneWayDistComplexity ε f μ ≤ (a : ℕ∞)) :
    ∃ P : QuantumOneWay X Y Z, P.distError f μ ≤ ε ∧ P.msgQubits ≤ a := by
  by_contra hno
  push Not at hno
  have hge : ((a + 1 : ℕ) : ℕ∞) ≤ quantumOneWayDistComplexity ε f μ :=
    le_iInf fun P ↦ Nat.cast_le.mpr (Nat.succ_le_of_lt (hno P.1 P.2))
  have hlt : (a + 1 : ℕ) ≤ a := Nat.cast_le.mp (hge.trans h)
  omega

theorem exists_quantumOneWay_of_worstYComplexity_le [Fintype X] [Fintype Z]
    {ε : ℝ} {f : X → Y → Option Z} {μX : PMF X} {a : ℕ}
    (h : quantumOneWayWorstYComplexity ε f μX ≤ (a : ℕ∞)) :
    ∃ P : QuantumOneWay X Y Z,
      (∀ y : Y, ∑ x : X, (μX x).toReal * P.pointError f x y ≤ ε) ∧ P.msgQubits ≤ a := by
  by_contra hno
  push Not at hno
  have hge : ((a + 1 : ℕ) : ℕ∞) ≤ quantumOneWayWorstYComplexity ε f μX :=
    le_iInf fun P ↦ Nat.cast_le.mpr (Nat.succ_le_of_lt (hno P.1 P.2))
  have hlt : (a + 1 : ℕ) ≤ a := Nat.cast_le.mp (hge.trans h)
  omega

/-- An entanglement-assisted quantum one-way protocol sending `msgQubits` qubits from Alice to Bob,
using an arbitrary finite-dimensional shared pure state `|ψ_AB⟩` and local isometries `V_x`. -/
structure EntangledQuantumOneWay (X Y Z : Type*) [Fintype Z] where
  /-- Number of qubits transmitted from Alice to Bob. -/
  msgQubits : ℕ
  /-- Dimension of Alice's share of the entanglement register `A`. -/
  aliceAncDim : ℕ
  /-- Dimension of Alice's discarded local register `A'`. -/
  aliceOutDim : ℕ
  /-- Dimension of Bob's share of the entanglement register `B`. -/
  bobAncDim : ℕ
  /-- Alice's initial register is nonempty. -/
  aliceAncPos : 0 < aliceAncDim
  /-- Alice's discarded register is nonempty. -/
  aliceOutPos : 0 < aliceOutDim
  /-- Bob's entanglement register is nonempty. -/
  bobAncPos : 0 < bobAncDim
  /-- Shared pure entangled state `|ψ_AB⟩`. -/
  sharedState : EuclideanSpace ℂ (Fin aliceAncDim × Fin bobAncDim)
  /-- The shared state is normalized. -/
  sharedState_norm : ‖sharedState‖ = 1
  /-- Alice's input-dependent encoding isometry `V_x : H_A → H_{A'} ⊗ H_D`. -/
  aliceOp : X → Matrix (Fin aliceOutDim × BitString msgQubits) (Fin aliceAncDim) ℂ
  /-- Isometry condition `V_xᴴ V_x = 1`. -/
  aliceOp_isometry : ∀ x, (aliceOp x)ᴴ * aliceOp x = 1
  /-- Bob's measurement POVM on `H_D ⊗ H_B` conditioned on `y`. -/
  bob : Y → POVM Z (BitString msgQubits × Fin bobAncDim)

/-- Bob's reduced quantum state on `Q = D B` given Alice's input `x`. -/
noncomputable def EntangledQuantumOneWay.bobState [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (x : X) :
    Matrix (BitString P.msgQubits × Fin P.bobAncDim) (BitString P.msgQubits × Fin P.bobAncDim) ℂ :=
  let e := Equiv.prodAssoc (Fin P.aliceOutDim) (BitString P.msgQubits) (Fin P.bobAncDim)
  partialTraceLeft (reindex e e (densityConj (P.aliceOp x ⊗ₖ (1 : Matrix (Fin P.bobAncDim)
    (Fin P.bobAncDim) ℂ)) (pureState P.sharedState)))

theorem EntangledQuantumOneWay.bobState_isDensityMatrix [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (x : X) :
    IsDensityMatrix (P.bobState x) := by
  let e := Equiv.prodAssoc (Fin P.aliceOutDim) (BitString P.msgQubits) (Fin P.bobAncDim)
  have h1 : IsDensityMatrix (densityConj (P.aliceOp x ⊗ₖ (1 : Matrix (Fin P.bobAncDim)
      (Fin P.bobAncDim) ℂ)) (pureState P.sharedState)) :=
    (isDensityMatrix_pureState P.sharedState_norm).densityConj_kronecker (P.aliceOp_isometry x)
  have h2 : IsDensityMatrix (reindex e e (densityConj (P.aliceOp x ⊗ₖ (1 : Matrix (Fin P.bobAncDim)
      (Fin P.bobAncDim) ℂ)) (pureState P.sharedState))) := by
    refine ⟨h1.posSemidef.submatrix e.symm, ?_⟩
    simpa only [trace, diag_apply, reindex_apply, submatrix_apply] using
      (e.symm.sum_comp _).trans h1.trace_eq_one
  exact h2.partialTraceLeft

/-- No-signalling marginal property: Bob's `B`-marginal of `P.bobState x` is independent of `x`. -/
theorem EntangledQuantumOneWay.partialTraceLeft_bobState [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (x : X) :
    partialTraceLeft (P.bobState x) = partialTraceLeft (pureState P.sharedState) := by
  have hns := partialTraceLeft_densityConj_kronecker (P.aliceOp_isometry x)
    (pureState P.sharedState)
  rw [← hns]
  ext b₁ b₂
  simp only [bobState, partialTraceLeft_apply, reindex_apply, submatrix_apply,
    Equiv.prodAssoc_symm_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Max-information bound for entanglement-assisted protocols: `I_max(X : D B)_ρ ≤ 2 * a`. -/
theorem EntangledQuantumOneWay.maxInformation_le [Finite X] [DecidableEq X] [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (pX : PMF X) :
    CslibFrontier.Quantum.maxInformation (CslibFrontier.Quantum.cqState pX P.bobState) ≤
      ((2 * (P.msgQubits : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  -- Reorder `X × (D × B)` to `X × (B × D)` to apply !
  let swapDB : BitString P.msgQubits × Fin P.bobAncDim ≃ Fin P.bobAncDim × BitString P.msgQubits :=
    Equiv.prodComm _ _
  let ρBD : X → Matrix (Fin P.bobAncDim × BitString P.msgQubits)
      (Fin P.bobAncDim × BitString P.msgQubits) ℂ :=
    fun x ↦ reindex swapDB swapDB (P.bobState x)
  have hρBD : ∀ x, IsDensityMatrix (ρBD x) := fun x ↦ by
    refine ⟨(P.bobState_isDensityMatrix x).posSemidef.submatrix swapDB.symm, ?_⟩
    simpa only [ρBD, trace, diag_apply, reindex_apply, submatrix_apply] using
      (swapDB.symm.sum_comp _).trans (P.bobState_isDensityMatrix x).trace_eq_one
  have hcq_BD : IsDensityMatrix (CslibFrontier.Quantum.cqState pX ρBD) :=
    CslibFrontier.Quantum.isDensityMatrix_cqState pX hρBD
  have hprod : partialTraceRight (reindex (Equiv.prodAssoc X (Fin P.bobAncDim)
        (BitString P.msgQubits)).symm (Equiv.prodAssoc X (Fin P.bobAncDim)
        (BitString P.msgQubits)).symm (CslibFrontier.Quantum.cqState pX ρBD)) =
      partialTraceRight (CslibFrontier.Quantum.cqState pX ρBD) ⊗ₖ
        partialTraceLeft (partialTraceRight (reindex (Equiv.prodAssoc X (Fin P.bobAncDim)
          (BitString P.msgQubits)).symm (Equiv.prodAssoc X (Fin P.bobAncDim)
          (BitString P.msgQubits)).symm (CslibFrontier.Quantum.cqState pX ρBD))) := by
    have hpt (x : X) : partialTraceRight (ρBD x) = partialTraceLeft (pureState P.sharedState) := by
      rw [← P.partialTraceLeft_bobState x]
      ext b₁ b₂
      simp [ρBD, swapDB, partialTraceRight_apply, partialTraceLeft_apply]
    ext ⟨x₁, b₁⟩ ⟨x₂, b₂⟩
    have hR : partialTraceRight (CslibFrontier.Quantum.cqState pX ρBD) x₁ x₂ =
        if x₁ = x₂ then ((pX x₁).toReal : ℂ) else 0 := by
      rw [CslibFrontier.Quantum.partialTraceRight_cqState pX hρBD]
      by_cases hx : x₁ = x₂ <;> simp [hx]
    rw [kroneckerMap_apply, hR]
    simp only [partialTraceRight_apply, reindex_apply, submatrix_apply,
      Equiv.symm_symm, Equiv.prodAssoc_apply, CslibFrontier.Quantum.cqState_apply,
      partialTraceLeft_apply, ite_true]
    have hB : ∑ x : X, ∑ d : BitString P.msgQubits,
        ((pX x).toReal : ℂ) * ρBD x (b₁, d) (b₂, d) =
        partialTraceLeft (pureState P.sharedState) b₁ b₂ := by
      simp only [← Finset.mul_sum]
      have hinner (x : X) : ∑ d : BitString P.msgQubits, ρBD x (b₁, d) (b₂, d) =
          partialTraceLeft (pureState P.sharedState) b₁ b₂ := by
        simpa [partialTraceRight_apply] using congrFun (congrFun (hpt x) b₁) b₂
      simp_rw [hinner, ← Finset.sum_mul]
      have h1 : (∑ x : X, ((pX x).toReal : ℂ)) = 1 := by
        exact_mod_cast Cslib.Probability.PMF.sum_toReal pX
      rw [h1, one_mul]
    rw [hB]
    by_cases hx : x₁ = x₂
    · subst hx
      simp only [ite_true, ← Finset.mul_sum]
      have hinner : ∑ d : BitString P.msgQubits, ρBD x₁ (b₁, d) (b₂, d) =
          partialTraceLeft (pureState P.sharedState) b₁ b₂ := by
        simpa [partialTraceRight_apply] using congrFun (congrFun (hpt x₁) b₁) b₂
      rw [hinner]
    · simp [hx]
  have : Nonempty (Fin P.bobAncDim) := ⟨⟨0, P.bobAncPos⟩⟩
  have hbound :=
    CslibFrontier.Quantum.maxInformation_le_two_mul_logb_of_product_marginal hcq_BD hprod
  have hlog : 2 * Real.logb 2 (Fintype.card (BitString P.msgQubits) : ℝ) =
      2 * (P.msgQubits : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [hlog] at hbound
  -- Transfer the bound back from `X × (B × D)` to `X × (D × B)` via `swapDB` without unfolding
  -- `maxInformation`.
  have hcq_DB : IsDensityMatrix (CslibFrontier.Quantum.cqState pX P.bobState) :=
    CslibFrontier.Quantum.isDensityMatrix_cqState pX P.bobState_isDensityMatrix
  have hle_eps : ∀ ε : ℝ, 0 < ε →
      CslibFrontier.Quantum.maxInformation (CslibFrontier.Quantum.cqState pX P.bobState) ≤
        ((2 * (P.msgQubits : ℝ) + ε : ℝ) : WithTop ℝ) := by
    intro ε hε
    obtain ⟨σ, hσ, hc⟩ :=
      CslibFrontier.Quantum.exists_le_of_maxInformation_le hcq_BD.posSemidef hbound hε
    let σ' := reindex swapDB.symm swapDB.symm σ
    have hσ' : IsDensityMatrix σ' := by
      refine ⟨hσ.posSemidef.submatrix swapDB, ?_⟩
      simpa only [σ', trace, diag_apply, reindex_apply, submatrix_apply, Equiv.symm_symm] using
        (swapDB.sum_comp _).trans hσ.trace_eq_one
    have hle' : CslibFrontier.Quantum.cqState pX P.bobState ≤
        (2 : ℝ) ^ (2 * (P.msgQubits : ℝ) + ε) •
          (partialTraceRight (CslibFrontier.Quantum.cqState pX P.bobState) ⊗ₖ σ') := by
      let E : X × (BitString P.msgQubits × Fin P.bobAncDim) ≃
          X × (Fin P.bobAncDim × BitString P.msgQubits) :=
        Equiv.prodCongr (Equiv.refl X) swapDB
      have hsub := (Matrix.le_iff.mp hc).submatrix E
      rw [Matrix.le_iff]
      convert hsub using 1
      ext ⟨x₁, d₁, b₁⟩ ⟨x₂, d₂, b₂⟩
      rw [CslibFrontier.Quantum.partialTraceRight_cqState pX P.bobState_isDensityMatrix,
        CslibFrontier.Quantum.partialTraceRight_cqState pX hρBD]
      simp [E, σ', ρBD, swapDB, CslibFrontier.Quantum.cqState_apply, reindex_apply, submatrix_apply,
        kroneckerMap_apply]
    exact CslibFrontier.Quantum.maxInformation_le_of_le hcq_DB hσ' hle'
  cases hval :
      CslibFrontier.Quantum.maxInformation (CslibFrontier.Quantum.cqState pX P.bobState) with
  | top =>
    have := hle_eps 1 one_pos
    rw [hval] at this
    exact absurd this (not_le_of_gt (WithTop.coe_lt_top _))
  | coe v =>
    rw [WithTop.coe_le_coe]
    by_contra hlt
    push Not at hlt
    have hε : 0 < (v - 2 * (P.msgQubits : ℝ)) / 2 := by linarith
    have h1 := hle_eps _ hε
    rw [hval, WithTop.coe_le_coe] at h1
    linarith

/-- Output distribution of an entanglement-assisted quantum one-way protocol on `(x, y)`. -/
@[expose] noncomputable def EntangledQuantumOneWay.outputPMF [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (x : X) (y : Y) : PMF Z :=
  (P.bob y).measureDensity (P.bobState x) (P.bobState_isDensityMatrix x)

/-- Pointwise error probability of an entanglement-assisted quantum one-way protocol. -/
@[expose] noncomputable def EntangledQuantumOneWay.pointError [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (f : X → Y → Option Z) (x : X) (y : Y) : ℝ :=
  match f x y with
  | none => 0
  | some z => 1 - (P.outputPMF x y z).toReal

/-- Distributional error of an entanglement-assisted quantum one-way protocol. -/
@[expose] noncomputable def EntangledQuantumOneWay.distError [Fintype X] [Fintype Y] [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (f : X → Y → Option Z) (μ : PMF (X × Y)) : ℝ :=
  ∑ q : X × Y, (μ q).toReal * P.pointError f q.1 q.2

/-- Entanglement-assisted quantum one-way worst-case complexity `Q^{1,*}_ε(f)`. -/
@[expose] noncomputable def entangledQuantumOneWayComplexity [Fintype Z]
    (ε : ℝ) (f : X → Y → Option Z) : ℕ∞ :=
  ⨅ P : {P : EntangledQuantumOneWay X Y Z // ∀ x y, P.pointError f x y ≤ ε},
    (P.1.msgQubits : ℕ∞)

/-- Entanglement-assisted quantum one-way distributional complexity `Q^{1,μ,*}_ε(f)`. -/
@[expose] noncomputable def entangledQuantumOneWayDistComplexity [Fintype X] [Fintype Y] [Fintype Z]
    (ε : ℝ) (f : X → Y → Option Z) (μ : PMF (X × Y)) : ℕ∞ :=
  ⨅ P : {P : EntangledQuantumOneWay X Y Z // P.distError f μ ≤ ε}, (P.1.msgQubits : ℕ∞)

/-- Entanglement-assisted quantum one-way worst-case-`y` distributional complexity
`Q^{1,μ_X,*}_ε(f)`. -/
@[expose] noncomputable def entangledQuantumOneWayWorstYComplexity [Fintype X] [Fintype Z]
    (ε : ℝ) (f : X → Y → Option Z) (μX : PMF X) : ℕ∞ :=
  ⨅ P : {P : EntangledQuantumOneWay X Y Z // ∀ y : Y,
    ∑ x : X, (μX x).toReal * P.pointError f x y ≤ ε}, (P.1.msgQubits : ℕ∞)

@[simp]
theorem EntangledQuantumOneWay.pointError_none [Fintype Z] (P : EntangledQuantumOneWay X Y Z)
    {f : X → Y → Option Z} {x : X} {y : Y} (h : f x y = none) :
    P.pointError f x y = 0 := by
  simp [EntangledQuantumOneWay.pointError, h]

theorem EntangledQuantumOneWay.pointError_some [Fintype Z] (P : EntangledQuantumOneWay X Y Z)
    {f : X → Y → Option Z} {x : X} {y : Y} {z : Z} (h : f x y = some z) :
    P.pointError f x y = 1 - (P.bob y).densityProb (P.bobState x) z := by
  simp only [EntangledQuantumOneWay.pointError, EntangledQuantumOneWay.outputPMF, h,
    POVM.measureDensity_apply, ENNReal.toReal_ofReal
      ((P.bob y).densityProb_nonneg (P.bobState_isDensityMatrix x).posSemidef z)]

theorem EntangledQuantumOneWay.distError_product [Fintype X] [Fintype Y] [Fintype Z]
    (P : EntangledQuantumOneWay X Y Z) (f : X → Y → Option Z) (μX : PMF X) (μY : PMF Y) :
    P.distError f (μX.bind fun x ↦ μY.map fun y ↦ (x, y)) =
      ∑ y : Y, (μY y).toReal * ∑ x : X, (μX x).toReal * P.pointError f x y := by
  simp only [EntangledQuantumOneWay.distError, Fintype.sum_prod_type,
    Cslib.Probability.PMF.bind_map_prodMk_apply, ENNReal.toReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

theorem exists_entangledQuantumOneWay_of_distComplexity_le [Fintype X] [Fintype Y] [Fintype Z]
    {ε : ℝ} {f : X → Y → Option Z} {μ : PMF (X × Y)} {a : ℕ}
    (h : entangledQuantumOneWayDistComplexity ε f μ ≤ (a : ℕ∞)) :
    ∃ P : EntangledQuantumOneWay X Y Z, P.distError f μ ≤ ε ∧ P.msgQubits ≤ a := by
  by_contra hno
  push Not at hno
  have hge : ((a + 1 : ℕ) : ℕ∞) ≤ entangledQuantumOneWayDistComplexity ε f μ :=
    le_iInf fun P ↦ Nat.cast_le.mpr (Nat.succ_le_of_lt (hno P.1 P.2))
  have hlt : (a + 1 : ℕ) ≤ a := Nat.cast_le.mp (hge.trans h)
  omega

theorem exists_entangledQuantumOneWay_of_worstYComplexity_le [Fintype X] [Fintype Z]
    {ε : ℝ} {f : X → Y → Option Z} {μX : PMF X} {a : ℕ}
    (h : entangledQuantumOneWayWorstYComplexity ε f μX ≤ (a : ℕ∞)) :
    ∃ P : EntangledQuantumOneWay X Y Z,
      (∀ y : Y, ∑ x : X, (μX x).toReal * P.pointError f x y ≤ ε) ∧ P.msgQubits ≤ a := by
  by_contra hno
  push Not at hno
  have hge : ((a + 1 : ℕ) : ℕ∞) ≤ entangledQuantumOneWayWorstYComplexity ε f μX :=
    le_iInf fun P ↦ Nat.cast_le.mpr (Nat.succ_le_of_lt (hno P.1 P.2))
  have hlt : (a + 1 : ℕ) ≤ a := Nat.cast_le.mp (hge.trans h)
  omega

end Quantum

/-! ### JRS Message Compression via Rejection Sampling -/

section MessageCompression

variable {X C : Type*}

/-- Boolean coin with `true` probability `p ∈ [0, 1]`. -/
private noncomputable def bernoulliPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b : Bool ↦ if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) (by
    rw [Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1), add_sub_cancel, ENNReal.ofReal_one])

/-- `N`-trial sequential rejection sampler on `R = Fin N → C`: Alice accepts coordinate `i` with
probability `α (r i)` independently and sends the first accepted index (`none` if none accept). -/
private noncomputable def rejectionAliceAux [Fintype C] (α : C → ℝ)
    (hα0 : ∀ y, 0 ≤ α y) (hα1 : ∀ y, α y ≤ 1) :
    ∀ (N : ℕ), (Fin N → C) → PMF (Option (Fin N))
  | 0, _ => PMF.pure none
  | N + 1, r =>
    (bernoulliPMF (α (r 0)) (hα0 (r 0)) (hα1 (r 0))).bind fun b ↦
      if b then PMF.pure (some 0)
      else (rejectionAliceAux α hα0 hα1 N (Fin.tail r)).map (Option.map Fin.succ)

/-- Exact law of the first accepted sample in `N` independent rejection-sampling trials:
`Pr[accepted ∧ output = y] = (1 - (1 - q)^N) * cond(y)`. -/
private theorem rejection_accept_prob [Fintype C] (σ : PMF C) (cond : PMF C) {q : ℝ}
    (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1) (α : C → ℝ) (hα0 : ∀ y, 0 ≤ α y) (hα1 : ∀ y, α y ≤ 1)
    (hmatch : ∀ y, (σ y).toReal * α y = q * (cond y).toReal) :
    ∀ (N : ℕ),
      (∀ y : C,
        (((PMF.pi (fun _ : Fin N ↦ σ)).bind fun r ↦
          (rejectionAliceAux α hα0 hα1 N r).map fun o ↦ o.map r) (some y)).toReal =
          (1 - (1 - q) ^ N) * (cond y).toReal) ∧
      (((PMF.pi (fun _ : Fin N ↦ σ)).bind fun r ↦
        (rejectionAliceAux α hα0 hα1 N r).map fun o ↦ o.map r) none).toReal =
        (1 - q) ^ N := by
  intro N
  classical
  induction N with
  | zero =>
    constructor
    · intro y
      simp [rejectionAliceAux, PMF.bind_const]
    · simp [rejectionAliceAux, PMF.bind_const]
  | succ N ih =>
    have hsum_alpha : ∑ y : C, (σ y).toReal * α y = q := by
      simp_rw [hmatch, ← Finset.mul_sum, Cslib.Probability.PMF.sum_toReal, mul_one]
    have hsplit :
        ((PMF.pi (fun _ : Fin (N + 1) ↦ σ)).bind fun r ↦
          (rejectionAliceAux α hα0 hα1 (N + 1) r).map fun o ↦ o.map r) =
        σ.bind fun c0 ↦
          (bernoulliPMF (α c0) (hα0 c0) (hα1 c0)).bind fun b ↦
            if b then PMF.pure (some c0)
            else ((PMF.pi (fun _ : Fin N ↦ σ)).bind fun r' ↦
              (rejectionAliceAux α hα0 hα1 N r').map fun o ↦ o.map r') := by
      rw [PMF.pi_fin_succ, PMF.bind_bind]
      refine congrArg (σ.bind ·) (funext fun c0 ↦ ?_)
      rw [PMF.bind_map]
      simp only [Function.comp_def, rejectionAliceAux, Fin.cons_zero, Fin.tail_cons, PMF.map_bind]
      have hcomm :
          ((PMF.pi fun _ : Fin N ↦ σ).bind fun r' ↦
            (bernoulliPMF (α c0) (hα0 c0) (hα1 c0)).bind fun b ↦
              (if b then PMF.pure (some (0 : Fin (N + 1)))
                else (rejectionAliceAux α hα0 hα1 N r').map (Option.map Fin.succ)).map
                fun o ↦ o.map (Fin.cons c0 r')) =
          (bernoulliPMF (α c0) (hα0 c0) (hα1 c0)).bind fun b ↦
            (PMF.pi fun _ : Fin N ↦ σ).bind fun r' ↦
              (if b then PMF.pure (some (0 : Fin (N + 1)))
                else (rejectionAliceAux α hα0 hα1 N r').map (Option.map Fin.succ)).map
                fun o ↦ o.map (Fin.cons c0 r') := by
        rw [PMF.bind_comm]
      rw [hcomm]
      refine congrArg (PMF.bind _) (funext fun b ↦ ?_)
      cases b
      · simp only [Bool.false_eq_true, ite_false, PMF.map_comp, Function.comp_def]
        refine congrArg (PMF.bind _) (funext fun r' ↦ ?_)
        refine congrArg (PMF.map · _) (funext fun o ↦ ?_)
        cases o <;> rfl
      · simp only [ite_true, PMF.pure_map, Option.map_some, Fin.cons_zero, PMF.bind_const]
    let tailPMF : PMF (Option C) :=
      (PMF.pi fun _ : Fin N ↦ σ).bind fun r' ↦
        (rejectionAliceAux α hα0 hα1 N r').map fun o ↦ o.map r'
    have hsplit' :
        ((PMF.pi (fun _ : Fin (N + 1) ↦ σ)).bind fun r ↦
          (rejectionAliceAux α hα0 hα1 (N + 1) r).map fun o ↦ o.map r) =
        σ.bind fun c0 ↦
          (bernoulliPMF (α c0) (hα0 c0) (hα1 c0)).bind fun b ↦
            if b then PMF.pure (some c0) else tailPMF := hsplit
    have hnone_step :
        (((PMF.pi (fun _ : Fin (N + 1) ↦ σ)).bind fun r ↦
          (rejectionAliceAux α hα0 hα1 (N + 1) r).map fun o ↦ o.map r) none).toReal =
          (1 - q) ^ (N + 1) := by
      rw [hsplit']
      simp only [PMF.bind_apply, tsum_fintype, Fintype.sum_bool, bernoulliPMF, PMF.ofFintype_apply,
        ite_true, Bool.false_eq_true, ite_false, PMF.pure_apply, reduceCtorEq, mul_zero, zero_add]
      rw [ENNReal.toReal_sum (fun c0 _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top tailPMF _)))]
      simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr (hα1 _)),
        show (tailPMF none).toReal = (1 - q) ^ N from ih.2]
      have hfactor : ∑ c0 : C, (σ c0).toReal * ((1 - α c0) * (1 - q) ^ N) =
          (∑ c0 : C, (σ c0).toReal - ∑ c0 : C, (σ c0).toReal * α c0) * (1 - q) ^ N := by
        rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c0 _ ↦ by ring
      rw [hfactor, Cslib.Probability.PMF.sum_toReal, hsum_alpha, pow_succ']
    refine ⟨fun y ↦ ?_, hnone_step⟩
    rw [hsplit']
    simp only [PMF.bind_apply, tsum_fintype, Fintype.sum_bool, bernoulliPMF, PMF.ofFintype_apply,
      ite_true, Bool.false_eq_true, ite_false, PMF.pure_apply]
    rw [ENNReal.toReal_sum (fun c0 _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by by_cases h : some y = some c0 <;> simp [h]),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top tailPMF _)⟩))]
    have hsplit_sum :
        ∑ c0 : C, (σ c0 * (ENNReal.ofReal (α c0) * (if some y = some c0 then 1 else 0) +
          ENNReal.ofReal (1 - α c0) * tailPMF (some y))).toReal =
        (∑ c0 : C, (σ c0).toReal * α c0 * (if c0 = y then 1 else 0)) +
          (∑ c0 : C, (σ c0).toReal * (1 - α c0)) * ((1 - (1 - q) ^ N) * (cond y).toReal) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c0 _ ↦ ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by by_cases h : some y = some c0 <;> simp [h]))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top tailPMF _)),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hα0 c0),
        ENNReal.toReal_ofReal (sub_nonneg.mpr (hα1 c0)),
        show (tailPMF (some y)).toReal = (1 - (1 - q) ^ N) * (cond y).toReal from ih.1 y]
      by_cases h : c0 = y
      · subst h; simp; ring
      · simp [h, Ne.symm h]; ring
    have hfirst : ∑ c0 : C, (σ c0).toReal * α c0 * (if c0 = y then (1 : ℝ) else 0) =
        q * (cond y).toReal := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true, hmatch y]
    have hsec : ∑ c0 : C, (σ c0).toReal * (1 - α c0) = 1 - q := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Cslib.Probability.PMF.sum_toReal,
        hsum_alpha]
    refine (Finset.sum_congr rfl fun c0 _ ↦ ?_).trans (hsplit_sum.trans ?_)
    · by_cases h : some y = some c0 <;> simp [h]
    · rw [hfirst, hsec, pow_succ']; ring

/-- Explicit bit-overhead helper `⌈log₂ max(1, ln(1/η))⌉` for JRS message compression. -/
@[expose] noncomputable def jrsExtraBits (η : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 1 (Real.log (1 / η))))

/-- Helper bound: `2^(jrsExtraBits η) ≥ ln(1/η)` for all `η > 0`. -/
theorem log_inv_le_two_pow_jrsExtraBits {η : ℝ} (_hη : 0 < η) :
    Real.log (1 / η) ≤ (2 : ℝ) ^ (jrsExtraBits η) := by
  have hmax_pos : (0 : ℝ) < max 1 (Real.log (1 / η)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : Real.log (1 / η) ≤ max 1 (Real.log (1 / η)) := le_max_right _ _
  have h2 : max 1 (Real.log (1 / η)) = (2 : ℝ) ^ (Real.logb 2 (max 1 (Real.log (1 / η)))) :=
    (Real.rpow_logb (by norm_num) (by norm_num) hmax_pos).symm
  have h3 : (2 : ℝ) ^ (Real.logb 2 (max 1 (Real.log (1 / η)))) ≤
      (2 : ℝ) ^ (jrsExtraBits η : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have h4 : (2 : ℝ) ^ (jrsExtraBits η : ℝ) = (2 : ℝ) ^ (jrsExtraBits η) := Real.rpow_natCast 2 _
  linarith

/-- **JRS Rejection-Sampling Message Compression** (pointwise form):
Given a classical channel `cond : X → PMF C`, a reference distribution `σ : PMF C`, and `k : ℕ`
with `cond x y ≤ 2^k * σ y` for all `x ∈ S` and `y : C`, there exists a public-coin randomized
one-way simulation (public coin `R = Fin (2^(k + m)) → C` drawn from `σ^⊗N`, message length
`k + m` bits where `m = jrsExtraBits η`, and deterministic Bob decoder `r (bitStringToFin msg)`)
whose simulated output distribution `sim x` satisfies `dist (cond x) (sim x) ≤ η` for every
`x ∈ S`. -/
theorem jrs_rejection_sampling_simulation [Fintype C]
    (cond : X → PMF C) (σ : PMF C) (S : Set X) (k : ℕ) {η : ℝ} (hη : 0 < η)
    (hdom : ∀ x ∈ S, ∀ y : C, (cond x y).toReal ≤ (2 : ℝ) ^ k * (σ y).toReal) :
    let m := jrsExtraBits η
    let N := 2 ^ (k + m)
    ∃ (alice : (Fin N → C) → X → PMF (BitString (k + m)))
      (dec : (Fin N → C) → BitString (k + m) → C),
      ∀ x ∈ S,
        dist (cond x)
          ((PMF.pi (fun _ : Fin N ↦ σ)).bind fun r ↦ (alice r x).map (dec r)) ≤ η := by
  classical
  intro m N
  let eBit : BitString (k + m) ≃ Fin N :=
    (Fintype.equivFinOfCardEq (by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])).trans (Equiv.refl _)
  let q : ℝ := ((2 : ℝ) ^ k)⁻¹
  have hq_pos : 0 < q := inv_pos.mpr (by positivity)
  have hq_le1 : q ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  -- Define acceptance probabilities `α x y` (defaulting to `0` for `x ∉ S`).
  let α (x : X) (y : C) : ℝ :=
    if hx : x ∈ S then
      if (σ y).toReal = 0 then 0 else q * (cond x y).toReal / (σ y).toReal
    else 0
  have hα0 (x : X) (y : C) : 0 ≤ α x y := by
    dsimp only [α]
    split_ifs <;> positivity
  have hα1 (x : X) (y : C) : α x y ≤ 1 := by
    dsimp only [α]
    split_ifs with hx hσ0
    · norm_num
    · have hσpos : 0 < (σ y).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hσ0)
      rw [div_le_one hσpos]
      have hd := hdom x hx y
      have hmul : q * (cond x y).toReal ≤ q * ((2 : ℝ) ^ k * (σ y).toReal) :=
        mul_le_mul_of_nonneg_left hd hq_pos.le
      rwa [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul] at hmul
    · norm_num
  -- Fallback index `0 : Fin N`.
  have hNpos : 0 < N := by positivity
  let idx0 : Fin N := ⟨0, hNpos⟩
  let alice : (Fin N → C) → X → PMF (BitString (k + m)) := fun r x ↦
    (rejectionAliceAux (α x) (hα0 x) (hα1 x) N r).map fun o ↦ eBit.symm (o.getD idx0)
  let dec : (Fin N → C) → BitString (k + m) → C := fun r b ↦ r (eBit b)
  refine ⟨alice, dec, fun x hx ↦ ?_⟩
  have hmatch (y : C) : (σ y).toReal * α x y = q * (cond x y).toReal := by
    dsimp only [α]
    simp only [hx, dite_true]
    by_cases hσ0 : (σ y).toReal = 0
    · simp only [hσ0, ite_true, mul_zero]
      have hd := hdom x hx y
      rw [hσ0, mul_zero] at hd
      have hcy : (cond x y).toReal = 0 := le_antisymm hd ENNReal.toReal_nonneg
      rw [hcy, mul_zero]
    · simp only [hσ0, ite_false, mul_div_cancel₀ _ hσ0]
  have hlaw := rejection_accept_prob σ (cond x) hq_pos.le hq_le1 (α x) (hα0 x) (hα1 x) hmatch N
  -- Compare simulated PMF `sim` with `cond x` using `hlaw`.
  let sim : PMF C := (PMF.pi (fun _ : Fin N ↦ σ)).bind fun r ↦ (alice r x).map (dec r)
  let raw : PMF (Option C) := (PMF.pi (fun _ : Fin N ↦ σ)).bind fun r ↦
    (rejectionAliceAux (α x) (hα0 x) (hα1 x) N r).map fun o ↦ o.map r
  -- On every `y : C`, `(sim y).toReal ≥ (raw (some y)).toReal = (1 - (1 - q)^N) * (cond x
  -- y).toReal`.
  have hsim_ge (y : C) : (1 - (1 - q) ^ N) * (cond x y).toReal ≤ (sim y).toReal := by
    rw [← hlaw.1 y]
    -- `sim` is obtained from `raw'` by replacing `none` with `r idx0`, so `P[sim = y] ≥ P[raw =
    -- some y]`.
    have hmap : ∀ r : Fin N → C,
        ((alice r x).map (dec r) y) ≥
          ((rejectionAliceAux (α x) (hα0 x) (hα1 x) N r).map fun o ↦ o.map r) (some y) := by
      intro r
      simp only [alice, dec, PMF.map_comp, Function.comp_def, Equiv.apply_symm_apply, PMF.map_apply]
      refine tsum_le_tsum fun o ↦ ?_
      cases o with
      | none => simp
      | some i => simp [Option.getD]
    have hbind : raw (some y) ≤ sim y := by
      simp only [raw, sim, PMF.bind_apply]
      exact tsum_le_tsum fun r ↦ mul_le_mul_right (hmap r) _
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) hbind
  -- Use `dist_eq_sum_filter_lt`: `dist (cond x) sim = ∑_{cond x y > sim y} ((cond x y) - (sim y))`.
  rw [Cslib.Probability.PMF.dist_eq_sum_filter_lt]
  calc
    ∑ y ∈ Finset.univ.filter (fun y : C ↦ (sim y).toReal < (cond x y).toReal),
        ((cond x y).toReal - (sim y).toReal)
        ≤ ∑ y ∈ Finset.univ.filter (fun y : C ↦ (sim y).toReal < (cond x y).toReal),
            ((1 - q) ^ N * (cond x y).toReal) := by
      refine Finset.sum_le_sum fun y _ ↦ ?_
      linarith [hsim_ge y]
    _ ≤ ∑ y : C, (1 - q) ^ N * (cond x y).toReal :=
      Finset.sum_le_univ_sum_of_nonneg fun y ↦
        mul_nonneg (pow_nonneg (sub_nonneg.mpr hq_le1) N) ENNReal.toReal_nonneg
    _ = (1 - q) ^ N := by
      rw [← Finset.mul_sum, Cslib.Probability.PMF.sum_toReal, mul_one]
    _ ≤ Real.exp (-q * (N : ℝ)) := by
      have h1 : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
      calc
        (1 - q) ^ N ≤ (Real.exp (-q)) ^ N :=
          pow_le_pow_left₀ (sub_nonneg.mpr hq_le1) h1 N
        _ = Real.exp ((N : ℝ) * (-q)) := (Real.exp_nat_mul (-q) N).symm
        _ = Real.exp (-q * (N : ℝ)) := by ring_nf
    _ ≤ η := by
      have hqN : Real.log (1 / η) ≤ q * (N : ℝ) := by
        have hN_eq : q * (N : ℝ) = (2 : ℝ) ^ m := by
          dsimp only [q, N]
          rw [pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
            ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
        rw [hN_eq]
        exact log_inv_le_two_pow_jrsExtraBits hη
      calc
        Real.exp (-q * (N : ℝ)) ≤ Real.exp (-Real.log (1 / η)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (Real.log η) := by rw [one_div, Real.log_inv, neg_neg]
        _ = η := Real.exp_log hη

end MessageCompression

end CslibFrontier.Communication
