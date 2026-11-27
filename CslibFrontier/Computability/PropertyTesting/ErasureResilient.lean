/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module

-- upstream: candidate

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Computability.PropertyTesting.Monotonicity.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.Monotone
public import CslibFrontier.Init

import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonadaptive Query Complexity, Yao's Minimax Principle, and Erasure-Resilient Property Testing

Reusable query-complexity and property-testing foundations on `Cslib.Probability.PMF`:

1. **Deterministic and randomized nonadaptive query algorithms**:
   `DetNonadaptiveAlg`, `RandNonadaptiveAlg`, worst-case query bounds `HasQueryBound`, output
   probabilities `probOut`, and answer-view distributions `viewPMF`.
2. **Conditioning bound and Yao's minimax indistinguishability lemma**:
   `dist_filter_le_one_div_sub_one` (bounding `dist (P.filter E hE) P ≤ 1 / (a - 1)` when
   `P(E) ≥ 1 - 1 / a`) and `yao_nonadaptive_lower_bound` (proving that `δ < 1 / 3` view
   indistinguishability rules out two-sided `2 / 3`-confidence nonadaptive testers).
3. **Erasure-resilient and tolerant Boolean property testing**:
   partially erased Boolean functions `(ι → Bool) → Option Bool`, completions `IsCompletion`,
   erasure filling `fillErasures`, erased fractions `erasedFraction`, relative property distance
   `relDistToSet`, and the Dixit–Raskhodnikova–Thakurta–Varma erasure-filling reduction
   `isErasureResilientTester_liftFillAlg` converting any `(α, ε)`-tolerant tester into an
   `α`-erasure-resilient `ε`-tester with identical query complexity.
-/

@[expose] public section

open scoped BigOperators ENNReal Cslib.Probability.PMF

namespace CslibFrontier.PropertyTesting

/-! ### 1. Deterministic and Randomized Nonadaptive Query Algorithms -/

/-- A deterministic nonadaptive query algorithm making `numQueries` parallel oracle queries in
advance and computing an output via `decide`. -/
structure DetNonadaptiveAlg (X Val Out : Type*) where
  /-- Number of parallel oracle queries issued by the algorithm. -/
  numQueries : ℕ
  /-- Indexed family of domain points queried before inspecting any answers. -/
  query : Fin numQueries → X
  /-- Decision function mapping oracle answer tuples to outputs. -/
  decide : (Fin numQueries → Val) → Out

/-- Answer tuple observed by `D` on input `f : X → Val`. -/
def DetNonadaptiveAlg.view {X Val Out : Type*} (D : DetNonadaptiveAlg X Val Out) (f : X → Val) :
    Fin D.numQueries → Val :=
  fun i ↦ f (D.query i)

/-- Output produced by `D` on input `f : X → Val`. -/
def DetNonadaptiveAlg.run {X Val Out : Type*} (D : DetNonadaptiveAlg X Val Out) (f : X → Val) :
    Out :=
  D.decide (D.view f)

/-- Answer-view distribution of `D` under an input prior `μ : PMF (X → Val)`. -/
noncomputable def DetNonadaptiveAlg.viewPMF {X Val Out : Type*}
    (D : DetNonadaptiveAlg X Val Out) (μ : PMF (X → Val)) : PMF (Fin D.numQueries → Val) :=
  μ.map D.view

/-- Randomized nonadaptive query algorithm modeled as a `PMF` over deterministic nonadaptive
algorithms. -/
abbrev RandNonadaptiveAlg (X Val Out : Type*) := PMF (DetNonadaptiveAlg X Val Out)

/-- Worst-case query complexity bound `q` across the support of `A`. -/
def RandNonadaptiveAlg.HasQueryBound {X Val Out : Type*} (A : RandNonadaptiveAlg X Val Out)
    (q : ℕ) : Prop :=
  ∀ D ∈ A.support, D.numQueries ≤ q

theorem RandNonadaptiveAlg.HasQueryBound.mono {X Val Out : Type*}
    {A : RandNonadaptiveAlg X Val Out} {q q' : ℕ} (hA : A.HasQueryBound q) (hqq' : q ≤ q') :
    A.HasQueryBound q' :=
  fun D hD ↦ (hA D hD).trans hqq'

/-- Probability that `A` on input `f : X → Val` outputs a value satisfying `P`. -/
noncomputable def RandNonadaptiveAlg.probOut {X Val Out : Type*}
    (A : RandNonadaptiveAlg X Val Out) (f : X → Val) (P : Out → Prop) : ℝ :=
  (A.toOuterMeasure {D | P (D.run f)}).toReal

theorem RandNonadaptiveAlg.probOut_not {X Val Out : Type*} (A : RandNonadaptiveAlg X Val Out)
    (f : X → Val) (P : Out → Prop) :
    A.probOut f (fun y ↦ ¬ P y) = 1 - A.probOut f P := by
  let s : Set (DetNonadaptiveAlg X Val Out) := {D | P (D.run f)}
  have hreal := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl A s
  change (A.toOuterMeasure sᶜ).toReal = 1 - (A.toOuterMeasure s).toReal
  linarith

/-! ### 2. Conditioning Bound and Yao's Minimax Indistinguishability Lemma -/

private lemma summable_pmf_mul_of_bdd {α : Type*} (μ : PMF α) {h : α → ℝ} {C : ℝ}
    (h0 : ∀ a, 0 ≤ h a) (hC : ∀ a, h a ≤ C) : Summable fun a ↦ (μ a).toReal * h a :=
  Summable.of_nonneg_of_le (fun a ↦ mul_nonneg ENNReal.toReal_nonneg (h0 a))
    (fun a ↦ (mul_le_mul_of_nonneg_left (hC a) ENNReal.toReal_nonneg).trans_eq (mul_comm _ _))
    ((Cslib.Probability.PMF.summable_toReal μ).mul_left C)

/-- Mixture (`PMF.bind`) convexity of statistical distance over an arbitrary prior `μ : PMF α`. -/
theorem dist_bind_le_of_support {α Ω : Type*} [Fintype Ω] (μ : PMF α) (F G : α → PMF Ω)
    {δ : ℝ} (hFG : ∀ a ∈ μ.support, dist (F a) (G a) ≤ δ) :
    dist (μ.bind F) (μ.bind G) ≤ δ := by
  have hle1 : ∀ (R : PMF Ω) (ω : Ω), (R ω).toReal ≤ 1 := fun R ω ↦
    ENNReal.toReal_mono ENNReal.one_ne_top (R.coe_le_one ω)
  have hterm : ∀ ω : Ω, Summable fun a ↦ (μ a).toReal * |(F a ω).toReal - (G a ω).toReal| :=
    fun ω ↦ summable_pmf_mul_of_bdd μ (C := 2) (fun _ ↦ abs_nonneg _) fun a ↦ by
      rw [abs_le]
      exact ⟨by linarith [ENNReal.toReal_nonneg (a := F a ω), hle1 (G a) ω],
        by linarith [ENNReal.toReal_nonneg (a := G a ω), hle1 (F a) ω]⟩
  have hH (H : α → PMF Ω) (ω : Ω) : Summable fun a ↦ (μ a).toReal * (H a ω).toReal :=
    summable_pmf_mul_of_bdd μ (fun _ ↦ ENNReal.toReal_nonneg) fun a ↦ hle1 (H a) ω
  have hpt : ∀ ω : Ω, |(μ.bind F ω).toReal - (μ.bind G ω).toReal| ≤
      ∑' a, (μ a).toReal * |(F a ω).toReal - (G a ω).toReal| := fun ω ↦ by
    rw [Cslib.Probability.PMF.bind_apply_toReal_tsum μ F ω,
      Cslib.Probability.PMF.bind_apply_toReal_tsum μ G ω, ← (hH F ω).tsum_sub (hH G ω)]
    have hsub : (fun a ↦ (μ a).toReal * (F a ω).toReal - (μ a).toReal * (G a ω).toReal) =
        fun a ↦ (μ a).toReal * ((F a ω).toReal - (G a ω).toReal) := funext fun _ ↦ by ring
    rw [hsub]
    have hnorm := norm_tsum_le_tsum_norm
      (f := fun a ↦ (μ a).toReal * ((F a ω).toReal - (G a ω).toReal))
      (by simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using hterm ω)
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using hnorm
  have hbind : dist (μ.bind F) (μ.bind G) ≤ ∑' a, (μ a).toReal * dist (F a) (G a) := by
    rw [Cslib.Probability.PMF.dist_eq]
    calc
      (∑ ω : Ω, |(μ.bind F ω).toReal - (μ.bind G ω).toReal|) / 2
        ≤ (∑ ω : Ω, ∑' a, (μ a).toReal * |(F a ω).toReal - (G a ω).toReal|) / 2 :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ ↦ hpt ω) zero_le_two
      _ = (∑' a, ∑ ω : Ω, (μ a).toReal * |(F a ω).toReal - (G a ω).toReal|) / 2 := by
          rw [← Summable.tsum_finsetSum fun ω _ ↦ hterm ω]
      _ = ∑' a, (μ a).toReal * dist (F a) (G a) := by
          rw [div_eq_mul_inv, ← tsum_mul_right]
          refine tsum_congr fun a ↦ ?_
          rw [← Finset.mul_sum, Cslib.Probability.PMF.dist_eq]
          ring
  have hsum_μ := Cslib.Probability.PMF.summable_toReal μ
  have hsum_tv := summable_pmf_mul_of_bdd μ (fun _ ↦ dist_nonneg)
    fun a ↦ Cslib.Probability.PMF.dist_le_one (F a) (G a)
  refine hbind.trans ((hsum_tv.tsum_le_tsum (fun a ↦ ?_) (hsum_μ.mul_right δ)).trans_eq
    (by rw [tsum_mul_right, Cslib.Probability.PMF.tsum_toReal μ, one_mul]))
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (hFG a ha) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

/-- Conditioning statistical-distance bound: if `1 < a` and `P(E) ≥ 1 - 1 / a`, then `E` meets
`P.support` and `dist (P.filter E hE) P ≤ 1 / (a - 1)`. -/
theorem dist_filter_le_one_div_sub_one {Ω : Type*} [Fintype Ω] (P : PMF Ω) (E : Set Ω)
    {a : ℝ} (ha : 1 < a) (hprob : 1 - 1 / a ≤ (P.toOuterMeasure E).toReal) :
    ∃ hE, dist (P.filter E hE) P ≤ 1 / (a - 1) := by
  have h1a : 1 / a < 1 := (div_lt_one (by linarith)).mpr ha
  have hE : ∃ ω ∈ E, ω ∈ P.support :=
    (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff P E).mp (by linarith)
  refine ⟨hE, ?_⟩
  rw [dist_comm, Cslib.Probability.PMF.dist_filter]
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl P E
  have hdiv : 1 / a ≤ 1 / (a - 1) := one_div_le_one_div_of_le (sub_pos.mpr ha) (by linarith)
  linarith

/-- **Yao's minimax indistinguishability lower bound for nonadaptive testers**: if `δ < 1 / 3` and
every `q`-query deterministic tester has `μYes`-view and `μNo`-view within statistical distance `δ`,
then no `q`-query randomized nonadaptive tester distinguishes `μYes.support` from `μNo.support` with
two-sided confidence `2 / 3`. -/
theorem yao_nonadaptive_lower_bound {X Val : Type*} [Fintype Val]
    {μYes μNo : PMF (X → Val)} {q : ℕ} {δ : ℝ} (hδ : δ < 1 / 3)
    (hview : ∀ D : DetNonadaptiveAlg X Val Bool,
      D.numQueries ≤ q → dist (D.viewPMF μYes) (D.viewPMF μNo) ≤ δ) :
    ¬ ∃ A : RandNonadaptiveAlg X Val Bool,
      A.HasQueryBound q ∧
        (∀ f ∈ μYes.support, 2 / 3 ≤ A.probOut f (· = true)) ∧
        (∀ f ∈ μNo.support, 2 / 3 ≤ A.probOut f (· = false)) := by
  rintro ⟨A, hAq, hYes, hNo⟩
  let acc (μ : PMF (X → Val)) : PMF Bool := μ.bind fun f ↦ A.map fun D ↦ D.run f
  have hprob_true : ∀ f : X → Val, ((A.map fun D ↦ D.run f) true).toReal =
      A.probOut f (· = true) := fun f ↦ by
    rw [RandNonadaptiveAlg.probOut, ← PMF.toOuterMeasure_apply_singleton,
      PMF.toOuterMeasure_map_apply]
    rfl
  have hacc_eq : ∀ μ : PMF (X → Val),
      acc μ = A.bind fun D ↦ (D.viewPMF μ).map D.decide := fun μ ↦ by
    calc
      acc μ = μ.bind fun f ↦ A.bind fun D ↦ PMF.pure (D.run f) := rfl
      _ = A.bind fun D ↦ μ.bind fun f ↦ PMF.pure (D.run f) := PMF.bind_comm μ A _
      _ = A.bind fun D ↦ (D.viewPMF μ).map D.decide := congrArg (A.bind ·) (funext fun D ↦ by
        rw [DetNonadaptiveAlg.viewPMF, PMF.map_comp]; rfl)
  have htv_le : dist (acc μYes) (acc μNo) ≤ δ := by
    rw [hacc_eq μYes, hacc_eq μNo]
    exact dist_bind_le_of_support A _ _ fun D hD ↦
      (Cslib.Probability.PMF.dist_map_le (D.viewPMF μYes) (D.viewPMF μNo) D.decide).trans
        (hview D (hAq D hD))
  have hYes_ge : 2 / 3 ≤ (acc μYes true).toReal := by
    have henn : ENNReal.ofReal (2 / 3) ≤ acc μYes true := by
      calc
        ENNReal.ofReal (2 / 3) = ∑' f, μYes f * ENNReal.ofReal (2 / 3) := by
          rw [ENNReal.tsum_mul_right, μYes.tsum_coe, one_mul]
        _ ≤ ∑' f, μYes f * (A.map fun D ↦ D.run f) true :=
          tsum_le_tsum fun f ↦ by
            by_cases hf : f ∈ μYes.support
            · refine mul_le_mul_right ?_ _
              rw [← ENNReal.ofReal_toReal ((A.map fun D ↦ D.run f).apply_ne_top true),
                hprob_true f]
              exact ENNReal.ofReal_le_ofReal (hYes f hf)
            · rw [PMF.mem_support_iff, not_not] at hf; rw [hf, zero_mul, zero_mul]
        _ = acc μYes true := (PMF.bind_apply _ _ _).symm
    simpa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / 3)] using
      ENNReal.toReal_mono ((acc μYes).apply_ne_top true) henn
  have hNo_le : (acc μNo true).toReal ≤ 1 / 3 := by
    have henn : acc μNo true ≤ ENNReal.ofReal (1 / 3) := by
      calc
        acc μNo true = ∑' f, μNo f * (A.map fun D ↦ D.run f) true := PMF.bind_apply _ _ _
        _ ≤ ∑' f, μNo f * ENNReal.ofReal (1 / 3) :=
          tsum_le_tsum fun f ↦ by
            by_cases hf : f ∈ μNo.support
            · refine mul_le_mul_right ?_ _
              rw [← ENNReal.ofReal_toReal ((A.map fun D ↦ D.run f).apply_ne_top true),
                hprob_true f]
              have hfalse : A.probOut f (· = false) = A.probOut f (fun b ↦ ¬ b = true) := by
                congr 1; ext b; cases b <;> simp
              exact ENNReal.ofReal_le_ofReal
                (by linarith [hNo f hf, hfalse, A.probOut_not f (· = true)])
            · rw [PMF.mem_support_iff, not_not] at hf; rw [hf, zero_mul, zero_mul]
        _ = ENNReal.ofReal (1 / 3) := by rw [ENNReal.tsum_mul_right, μNo.tsum_coe, one_mul]
    simpa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / 3)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top henn
  have hcoord : |(acc μYes true).toReal - (acc μNo true).toReal| ≤ dist (acc μYes) (acc μNo) := by
    simpa [PMF.toOuterMeasure_apply_singleton] using
      Cslib.Probability.PMF.abs_toOuterMeasure_toReal_sub_le_dist (acc μYes) (acc μNo) {true}
  have h13 : (1 / 3 : ℝ) ≤ |(acc μYes true).toReal - (acc μNo true).toReal| :=
    (by linarith : (1 / 3 : ℝ) ≤ (acc μYes true).toReal - (acc μNo true).toReal).trans
      (le_abs_self _)
  linarith

/-! ### 3. Erasure-Resilient and Tolerant Boolean Property Testing -/

section ErasureResilient

/-- Normalized Hamming distance between Boolean functions `f, g : (ι → Bool) → Bool`. -/
noncomputable def relHammingDist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → Bool) → Bool) : ℝ :=
  (hammingDist f g : ℝ) / (2 ^ Fintype.card ι : ℝ)

/-- Minimum relative Hamming distance from `f` to a property `P : Set ((ι → Bool) → Bool)`. -/
noncomputable def relDistToSet {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool)
    (P : Set ((ι → Bool) → Bool)) : ℝ :=
  sInf (relHammingDist f '' P)

theorem relDistToSet_le_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → Bool) → Bool}
    {P : Set ((ι → Bool) → Bool)} (hg : g ∈ P) : relDistToSet f P ≤ relHammingDist f g :=
  csInf_le ⟨0, by rintro _ ⟨h, -, rfl⟩; unfold relHammingDist; positivity⟩ ⟨g, hg, rfl⟩

/-- Agreement between `relDistToSet f {g | Monotone g}` and `Cslib.BitString.relDistMonotone f`. -/
theorem relDistToSet_monotone_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) :
    relDistToSet f {g | Monotone g} = Cslib.BitString.relDistMonotone f := by
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg, hfg⟩ := Cslib.BitString.exists_monotone_hammingDist_eq_distMonotone f
    rw [Cslib.BitString.relDistMonotone_eq, ← hfg]
    exact relDistToSet_le_of_mem hg
  · rw [relDistToSet]
    refine le_csInf ⟨_, ⟨fun _ ↦ false, monotone_const, rfl⟩⟩ ?_
    rintro _ ⟨g, hg, rfl⟩
    exact (Cslib.BitString.le_relDistMonotone_iff.mp le_rfl) g hg

/-- A total Boolean function `g` is a completion of a partially erased function `f` if `g` agrees
with `f` at every non-erased input. -/
def IsCompletion {ι : Type*} (f : (ι → Bool) → Option Bool) (g : (ι → Bool) → Bool) : Prop :=
  ∀ x b, f x = some b → g x = b

/-- Canonical completion replacing every `none` with `defaultBit`. -/
def fillErasures {ι : Type*} (defaultBit : Bool) (f : (ι → Bool) → Option Bool) (x : ι → Bool) :
    Bool :=
  (f x).getD defaultBit

theorem isCompletion_fillErasures {ι : Type*} (defaultBit : Bool)
    (f : (ι → Bool) → Option Bool) : IsCompletion f (fillErasures defaultBit f) :=
  fun _ _ hx ↦ by simp [fillErasures, hx]

/-- Fraction of hypercube inputs on which `f` is erased (`none`). -/
noncomputable def erasedFraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Option Bool) : ℝ :=
  ((Finset.univ.filter fun x ↦ f x = none).card : ℝ) / (2 ^ Fintype.card ι : ℝ)

/-- `f` admits a completion in property `P`. -/
def HasCompletionIn {ι : Type*} (P : Set ((ι → Bool) → Bool))
    (f : (ι → Bool) → Option Bool) : Prop :=
  ∃ g ∈ P, IsCompletion f g

/-- Every completion of `f` is `ε`-far from property `P`. -/
def IsFarEveryCompletion {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ)
    (P : Set ((ι → Bool) → Bool)) (f : (ι → Bool) → Option Bool) : Prop :=
  ∀ g, IsCompletion f g → ε ≤ relDistToSet g P

theorem relHammingDist_fillErasures_le {ι : Type*} [Fintype ι] [DecidableEq ι] (defaultBit : Bool)
    {f : (ι → Bool) → Option Bool} {g : (ι → Bool) → Bool} (hg : IsCompletion f g) :
    relHammingDist (fillErasures defaultBit f) g ≤ erasedFraction f := by
  unfold relHammingDist erasedFraction
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [hammingDist]
  exact_mod_cast Finset.card_le_card fun x hx ↦ by
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ x, ?_⟩
    cases hfx : f x with
    | none => rfl
    | some b => exact False.elim (hx.2 (by simp [fillErasures, hfx, hg x b hfx]))

/-- Two-sided `2 / 3`-confidence nonadaptive `α`-erasure-resilient `ε`-tester for `P`. -/
def IsErasureResilientTester {ι : Type*} [Fintype ι] [DecidableEq ι] (α ε : ℝ)
    (P : Set ((ι → Bool) → Bool))
    (A : RandNonadaptiveAlg (ι → Bool) (Option Bool) Bool) : Prop :=
  (∀ f, erasedFraction f ≤ α → HasCompletionIn P f → 2 / 3 ≤ A.probOut f (· = true)) ∧
    (∀ f, erasedFraction f ≤ α → IsFarEveryCompletion ε P f → 2 / 3 ≤ A.probOut f (· = false))

/-- Two-sided `2 / 3`-confidence nonadaptive `(α, ε)`-tolerant tester for `P`. -/
def IsTolerantTester {ι : Type*} [Fintype ι] [DecidableEq ι] (α ε : ℝ)
    (P : Set ((ι → Bool) → Bool))
    (A : RandNonadaptiveAlg (ι → Bool) Bool Bool) : Prop :=
  (∀ g, relDistToSet g P ≤ α → 2 / 3 ≤ A.probOut g (· = true)) ∧
    (∀ g, ε ≤ relDistToSet g P → 2 / 3 ≤ A.probOut g (· = false))

/-- Lifts a deterministic nonadaptive query algorithm on total Boolean inputs to partially erased
inputs by filling queried `none` values with `defaultBit`. -/
def liftFillDetAlg {ι Out : Type*} (defaultBit : Bool)
    (D : DetNonadaptiveAlg (ι → Bool) Bool Out) :
    DetNonadaptiveAlg (ι → Bool) (Option Bool) Out :=
  ⟨D.numQueries, D.query, fun ans ↦ D.decide fun i ↦ (ans i).getD defaultBit⟩

/-- Lifts a randomized nonadaptive query algorithm on total Boolean inputs to partially erased
inputs by filling queried erasures with `defaultBit`. -/
noncomputable def liftFillAlg {ι Out : Type*} (defaultBit : Bool)
    (A : RandNonadaptiveAlg (ι → Bool) Bool Out) :
    RandNonadaptiveAlg (ι → Bool) (Option Bool) Out :=
  A.map (liftFillDetAlg defaultBit)

theorem hasQueryBound_liftFillAlg {ι Out : Type*} (defaultBit : Bool)
    {A : RandNonadaptiveAlg (ι → Bool) Bool Out} {q : ℕ} (hA : A.HasQueryBound q) :
    (liftFillAlg defaultBit A).HasQueryBound q := by
  intro D hD
  rcases (PMF.mem_support_map_iff _ _ _).mp hD with ⟨D₀, hD₀, rfl⟩
  exact hA D₀ hD₀

/-- **Dixit–Raskhodnikova–Thakurta–Varma Erasure-Filling Reduction**: filling queried erasures with
`defaultBit` converts any nonadaptive `(α, ε)`-tolerant tester for `P` into a nonadaptive
`α`-erasure-resilient `ε`-tester for `P` with identical query complexity. -/
theorem isErasureResilientTester_liftFillAlg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (defaultBit : Bool) {α ε : ℝ} {P : Set ((ι → Bool) → Bool)}
    {A : RandNonadaptiveAlg (ι → Bool) Bool Bool}
    (hA : IsTolerantTester α ε P A) :
    IsErasureResilientTester α ε P (liftFillAlg defaultBit A) := by
  have hprob : ∀ (f : (ι → Bool) → Option Bool) (Q : Bool → Prop),
      (liftFillAlg defaultBit A).probOut f Q = A.probOut (fillErasures defaultBit f) Q :=
    fun f Q ↦ by
      rw [RandNonadaptiveAlg.probOut, RandNonadaptiveAlg.probOut, liftFillAlg,
        PMF.toOuterMeasure_map_apply]
      rfl
  refine ⟨fun f hα ⟨g, hgP, hfg⟩ ↦ ?_, fun f _ hf ↦ ?_⟩ <;> rw [hprob]
  · exact hA.1 _ ((relDistToSet_le_of_mem hgP).trans
      ((relHammingDist_fillErasures_le defaultBit hfg).trans hα))
  · exact hA.2 _ (hf _ (isCompletion_fillErasures defaultBit f))

end ErasureResilient

end CslibFrontier.PropertyTesting
