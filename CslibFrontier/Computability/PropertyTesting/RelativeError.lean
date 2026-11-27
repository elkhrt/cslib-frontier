module

public import Cslib.Probability.PMF
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.ThresholdCounting
public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Probability.IID
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relative-Error Property Testing of Boolean Functions

General framework for relative-error property testing of Boolean functions over `{0, 1}^n` with
`SAMP` (uniform positive samples) and `MQ` (membership queries) oracle access, including
adaptive-to-non-adaptive simulation, tester padding, Yao's distributional distinguishing lemma,
and the violating 4-tuple obstruction for linear threshold functions (halfspaces).

## Main definitions

* `CslibFrontier.Computability.PropertyTesting.RelativeError.relDist`, `relDistToClass`:
  relative-error distance `|f⁻¹(1) △ g⁻¹(1)| / |f⁻¹(1)|` and distance to a Boolean function class.
* `CslibFrontier.Computability.PropertyTesting.RelativeError.DetNonAdaptiveTester`,
  `DetAdaptiveTester`, `IsRelativeErrorTester`, `IsAdaptiveRelativeErrorTester`: deterministic
  and randomized relative-error testers with `SAMP` and `MQ` access.
* `CslibFrontier.Computability.PropertyTesting.RelativeError.IsGoodFourTuple`,
  `IsViolatingFourTuple`: 4-tuple obstructions for halfspaces.

## Main results

* `DetAdaptiveTester.eval_toNonAdaptive`, `IsAdaptiveRelativeErrorTester.toNonAdaptive`:
  simulating a `q`-query adaptive tester by a `(2 ^ q - 1)`-query non-adaptive tester.
* `yao_relative_error_distinguishing_bound`: Yao's minimax principle for relative-error testers.
* `not_isViolatingFourTuple_of_isLTF`, `card_disjoint_violating_le_hammingDist`: halfspaces have
  no violating 4-tuples, yielding additive Hamming distance lower bounds from disjoint packings.
-/

public section

namespace CslibFrontier.Computability.PropertyTesting.RelativeError

open Finset
open scoped BigOperators ENNReal

/-- The set of satisfying assignments `f⁻¹(1)` of a Boolean function on `Fin n → Bool`. -/
def satisfyingSet {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  univ.filter fun x => f x = true

theorem mem_satisfyingSet {n : ℕ} {f : (Fin n → Bool) → Bool} {x : Fin n → Bool} :
    x ∈ satisfyingSet f ↔ f x = true := by
  simp [satisfyingSet]

/-- Relative-error distance `reldist(f, g) = |f⁻¹(1) △ g⁻¹(1)| / |f⁻¹(1)|` between Boolean
functions on `{0, 1}^n` (`0` when `f⁻¹(1) = ∅`). -/
noncomputable def relDist {n : ℕ} (f g : (Fin n → Bool) → Bool) : ℝ :=
  (hammingDist f g : ℝ) / ((satisfyingSet f).card : ℝ)

theorem relDist_nonneg {n : ℕ} (f g : (Fin n → Bool) → Bool) : 0 ≤ relDist f g := by
  unfold relDist; positivity

@[simp]
theorem relDist_self {n : ℕ} (f : (Fin n → Bool) → Bool) : relDist f f = 0 := by
  simp [relDist]

/-- Relative distance from `f` to a class `C` of Boolean functions: `min_{g ∈ C} reldist(f, g)`. -/
noncomputable def relDistToClass {n : ℕ} (f : (Fin n → Bool) → Bool)
    (C : ((Fin n → Bool) → Bool) → Prop) : ℝ :=
  sInf (relDist f '' {g | C g})

theorem relDistToClass_le {n : ℕ} {f g : (Fin n → Bool) → Bool}
    {C : ((Fin n → Bool) → Bool) → Prop} (hg : C g) :
    relDistToClass f C ≤ relDist f g := by
  refine csInf_le ⟨0, ?_⟩ ⟨g, hg, rfl⟩
  rintro _ ⟨h, -, rfl⟩
  exact relDist_nonneg f h

theorem exists_relDist_eq_relDistToClass {n : ℕ} (f : (Fin n → Bool) → Bool)
    {C : ((Fin n → Bool) → Bool) → Prop} (hC : ∃ g, C g) :
    ∃ g, C g ∧ relDist f g = relDistToClass f C := by
  classical
  let S : Finset ((Fin n → Bool) → Bool) := univ.filter C
  have hS : S.Nonempty := let ⟨g, hg⟩ := hC; ⟨g, mem_filter.2 ⟨mem_univ g, hg⟩⟩
  obtain ⟨g, hg, hmin⟩ := exists_min_image S (relDist f) hS
  have hCg : C g := (mem_filter.1 hg).2
  refine ⟨g, hCg, le_antisymm ?_ (relDistToClass_le hCg)⟩
  exact le_csInf (let ⟨h, hh⟩ := hC; ⟨relDist f h, h, hh, rfl⟩)
    (by rintro _ ⟨h, hh, rfl⟩; exact hmin h (mem_filter.2 ⟨mem_univ h, hh⟩))

theorem le_relDistToClass_iff {n : ℕ} {f : (Fin n → Bool) → Bool}
    {C : ((Fin n → Bool) → Bool) → Prop} (hC : ∃ g, C g) {ε : ℝ} :
    ε ≤ relDistToClass f C ↔ ∀ g, C g → ε ≤ relDist f g := by
  refine ⟨fun h g hg => h.trans (relDistToClass_le hg), fun h => ?_⟩
  obtain ⟨g, hg, hmin⟩ := exists_relDist_eq_relDistToClass f hC
  exact hmin ▸ h g hg

theorem relDistToClass_eq_zero_of_mem {n : ℕ} {f : (Fin n → Bool) → Bool}
    {C : ((Fin n → Bool) → Bool) → Prop} (hf : C f) :
    relDistToClass f C = 0 := by
  refine le_antisymm ((relDistToClass_le hf).trans_eq (relDist_self f)) ?_
  exact (le_relDistToClass_iff ⟨f, hf⟩).2 fun g _ => relDist_nonneg f g

/-- Composing with coordinatewise XOR preserves relative-error distance. -/
theorem relDist_comp_xor {n : ℕ} (f g : (Fin n → Bool) → Bool) (z : Fin n → Bool) :
    relDist (fun x => f (fun i => xor (x i) (z i))) (fun x => g (fun i => xor (x i) (z i))) =
      relDist f g := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun x i => xor (x i) (z i)
      invFun := fun x i => xor (x i) (z i)
      left_inv := fun x => by funext i; simp
      right_inv := fun x => by funext i; simp }
  unfold relDist
  have hham : hammingDist (fun x : Fin n → Bool => f (fun i => xor (x i) (z i)))
      (fun x : Fin n → Bool => g (fun i => xor (x i) (z i))) = hammingDist f g := by
    simp only [hammingDist]
    exact Finset.card_bij (fun x _ => e x) (fun x hx => by simpa [e] using hx)
      (fun _ _ _ _ h => e.injective h)
      (fun y hy => ⟨e.symm y, by simpa [e] using hy, e.apply_symm_apply y⟩)
  have hsat : (satisfyingSet (fun x : Fin n → Bool => f (fun i => xor (x i) (z i)))).card =
      (satisfyingSet f).card :=
    Finset.card_bij (fun x _ => e x) (fun x hx => by simpa [e, mem_satisfyingSet] using hx)
      (fun _ _ _ _ h => e.injective h)
      (fun y hy => ⟨e.symm y, by simpa [e, mem_satisfyingSet] using hy, e.apply_symm_apply y⟩)
  rw [hham, hsat]

/-- A deterministic `s`-sample, `q`-query non-adaptive relative-error tester on `{0, 1}^n`. -/
@[ext]
structure DetNonAdaptiveTester (n s q : ℕ) where
  /-- Non-adaptive membership query maps chosen from the `s` positive samples. -/
  query : Fin q → (Fin s → Fin n → Bool) → (Fin n → Bool)
  /-- Final Boolean verdict given samples and query answers. -/
  decide : (Fin s → Fin n → Bool) → (Fin q → Bool) → Bool

instance (n s q : ℕ) : Fintype (DetNonAdaptiveTester n s q) :=
  Fintype.ofEquiv
    ((Fin q → (Fin s → Fin n → Bool) → (Fin n → Bool)) ×
      ((Fin s → Fin n → Bool) → (Fin q → Bool) → Bool))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun A => (A.query, A.decide)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }

/-- Evaluate a deterministic non-adaptive tester on `f` and samples `u`. -/
def DetNonAdaptiveTester.eval {n s q : ℕ} (A : DetNonAdaptiveTester n s q)
    (f : (Fin n → Bool) → Bool) (u : Fin s → Fin n → Bool) : Bool :=
  A.decide u (fun i => f (A.query i u))

/-- The `s`-sample uniform positive-example distribution `SAMP(f)^s`. -/
noncomputable def sampleDist {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : (satisfyingSet f).Nonempty) (s : ℕ) : PMF (Fin s → Fin n → Bool) :=
  Cslib.Probability.PMF.iid (Cslib.Probability.PMF.uniformOfFinset (satisfyingSet f) hf) s

/-- Acceptance probability of a deterministic non-adaptive tester on `f`. -/
noncomputable def DetNonAdaptiveTester.acceptProb {n s q : ℕ} (A : DetNonAdaptiveTester n s q)
    (f : (Fin n → Bool) → Bool) (hf : (satisfyingSet f).Nonempty) : ℝ :=
  ((sampleDist f hf s).map (A.eval f) true).toReal

/-- Acceptance probability of a randomized non-adaptive tester `T` on `f`. -/
noncomputable def nonAdaptiveAcceptProb {n s q : ℕ} (T : PMF (DetNonAdaptiveTester n s q))
    (f : (Fin n → Bool) → Bool) (hf : (satisfyingSet f).Nonempty) : ℝ :=
  (T.bind (fun A => (sampleDist f hf s).map (A.eval f)) true).toReal

/-- Average acceptance probability of a deterministic non-adaptive tester on a distribution `μ`. -/
noncomputable def distAcceptProb {n s q : ℕ} (μ : PMF ((Fin n → Bool) → Bool))
    (A : DetNonAdaptiveTester n s q) : ℝ :=
  ∑ f : (Fin n → Bool) → Bool, (μ f).toReal *
    if hf : (satisfyingSet f).Nonempty then A.acceptProb f hf else 0

/-- Randomized relative-error `ε`-tester for class `C` with success probability `p`. -/
structure IsRelativeErrorTester {n s q : ℕ} (T : PMF (DetNonAdaptiveTester n s q))
    (C : ((Fin n → Bool) → Bool) → Prop) (ε p : ℝ) : Prop where
  /-- Completeness: accepts every nonempty `f ∈ C` with probability at least `p`. -/
  accept : ∀ f (hf : (satisfyingSet f).Nonempty), C f → p ≤ nonAdaptiveAcceptProb T f hf
  /-- Soundness: accepts every nonempty `ε`-far `f` with probability at most `1 - p`. -/
  reject : ∀ f (hf : (satisfyingSet f).Nonempty),
    ε ≤ relDistToClass f C → nonAdaptiveAcceptProb T f hf ≤ 1 - p

/-- A deterministic `s`-sample, `q`-query adaptive relative-error tester on `{0, 1}^n`. -/
@[ext]
structure DetAdaptiveTester (n s q : ℕ) where
  /-- Adaptive decision tree of depth at most `q` selected from the `s` positive samples. -/
  tree : (Fin s → Fin n → Bool) → Cslib.DecisionTree (Fin n → Bool) Bool
  /-- Depth bound ensuring at most `q` adaptive membership queries. -/
  depth_le : ∀ u, (tree u).depth ≤ q

/-- Evaluate a deterministic adaptive tester on `f` and samples `u`. -/
def DetAdaptiveTester.eval {n s q : ℕ} (A : DetAdaptiveTester n s q)
    (f : (Fin n → Bool) → Bool) (u : Fin s → Fin n → Bool) : Bool :=
  (A.tree u).eval f

/-- Acceptance probability of a randomized adaptive tester `T` on `f`. -/
noncomputable def adaptiveAcceptProb {n s q : ℕ} (T : PMF (DetAdaptiveTester n s q))
    (f : (Fin n → Bool) → Bool) (hf : (satisfyingSet f).Nonempty) : ℝ :=
  (T.bind (fun A => (sampleDist f hf s).map (A.eval f)) true).toReal

/-- Randomized adaptive relative-error `ε`-tester for class `C` with success probability `p`. -/
structure IsAdaptiveRelativeErrorTester {n s q : ℕ} (T : PMF (DetAdaptiveTester n s q))
    (C : ((Fin n → Bool) → Bool) → Prop) (ε p : ℝ) : Prop where
  /-- Completeness: accepts every nonempty `f ∈ C` with probability at least `p`. -/
  accept : ∀ f (hf : (satisfyingSet f).Nonempty), C f → p ≤ adaptiveAcceptProb T f hf
  /-- Soundness: accepts every nonempty `ε`-far `f` with probability at most `1 - p`. -/
  reject : ∀ f (hf : (satisfyingSet f).Nonempty),
    ε ≤ relDistToClass f C → adaptiveAcceptProb T f hf ≤ 1 - p

private def treeQueries {n : ℕ} :
    Cslib.DecisionTree (Fin n → Bool) Bool → (d : ℕ) → Fin (2 ^ d - 1) → (Fin n → Bool)
  | _, 0, i => Fin.elim0 i
  | .leaf _, _ + 1, _ => fun _ => false
  | .node x t₀ t₁, d + 1, i =>
      if h0 : i.val = 0 then x
      else if h1 : i.val - 1 < 2 ^ d - 1 then
        treeQueries t₀ d ⟨i.val - 1, h1⟩
      else
        treeQueries t₁ d ⟨i.val - 2 ^ d, by
          have := i.isLt
          have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
          have hd : 1 ≤ 2 ^ d := Nat.one_le_two_pow
          omega⟩

private def treeEvalFromAnswers {n : ℕ} :
    Cslib.DecisionTree (Fin n → Bool) Bool → (d : ℕ) → (Fin (2 ^ d - 1) → Bool) → Bool
  | .leaf b, _, _ => b
  | .node _ _ _, 0, _ => false
  | .node _ t₀ t₁, d + 1, ans =>
      have hd : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      cond (ans ⟨0, by omega⟩)
        (treeEvalFromAnswers t₁ d fun j => ans ⟨j.val + 2 ^ d, by omega⟩)
        (treeEvalFromAnswers t₀ d fun j => ans ⟨j.val + 1, by omega⟩)

private theorem treeEvalFromAnswers_correct {n : ℕ}
    (t : Cslib.DecisionTree (Fin n → Bool) Bool) (d : ℕ) (hd : t.depth ≤ d)
    (f : (Fin n → Bool) → Bool) :
    treeEvalFromAnswers t d (fun i => f (treeQueries t d i)) = t.eval f := by
  induction t generalizing d with
  | leaf b => cases d <;> rfl
  | node x t₀ t₁ ih₀ ih₁ =>
      cases d with
      | zero => simp [Cslib.DecisionTree.depth_node] at hd
      | succ d =>
          simp only [Cslib.DecisionTree.depth_node] at hd
          have h0 : t₀.depth ≤ d := le_trans (le_max_left _ _) (Nat.le_of_succ_le_succ hd)
          have h1 : t₁.depth ≤ d := le_trans (le_max_right _ _) (Nat.le_of_succ_le_succ hd)
          simp only [treeEvalFromAnswers, Cslib.DecisionTree.eval_node]
          have hroot : treeQueries (.node x t₀ t₁) (d + 1) ⟨0, by
              have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
              have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
              omega⟩ = x := by simp [treeQueries]
          rw [hroot]
          cases f x with
          | false =>
              simp only [Bool.cond_false]
              have hleft : (fun j : Fin (2 ^ d - 1) =>
                  f (treeQueries (.node x t₀ t₁) (d + 1) ⟨j.val + 1, by
                    have := j.isLt
                    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
                    have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
                    omega⟩)) = fun j => f (treeQueries t₀ d j) := by
                funext j
                have hne : j.val + 1 ≠ 0 := by omega
                have hlt : j.val + 1 - 1 < 2 ^ d - 1 := by simp
                simp [treeQueries]
              rw [hleft, ih₀ d h0]
          | true =>
              simp only [Bool.cond_true]
              have hright : (fun j : Fin (2 ^ d - 1) =>
                  f (treeQueries (.node x t₀ t₁) (d + 1) ⟨j.val + 2 ^ d, by
                    have := j.isLt
                    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
                    have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
                    omega⟩)) = fun j => f (treeQueries t₁ d j) := by
                funext j
                have hne : j.val + 2 ^ d ≠ 0 := by
                  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow; omega
                have hnlt : ¬ (j.val + 2 ^ d - 1 < 2 ^ d - 1) := by
                  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow; omega
                simp [treeQueries, hnlt]
              rw [hright, ih₁ d h1]

/-- Simulate a `q`-query adaptive tester by a `(2 ^ q - 1)`-query non-adaptive tester. -/
def DetAdaptiveTester.toNonAdaptive {n s q : ℕ} (A : DetAdaptiveTester n s q) :
    DetNonAdaptiveTester n s (2 ^ q - 1) where
  query i u := treeQueries (A.tree u) q i
  decide u ans := treeEvalFromAnswers (A.tree u) q ans

theorem DetAdaptiveTester.eval_toNonAdaptive {n s q : ℕ} (A : DetAdaptiveTester n s q)
    (f : (Fin n → Bool) → Bool) (u : Fin s → Fin n → Bool) :
    A.toNonAdaptive.eval f u = A.eval f u :=
  treeEvalFromAnswers_correct (A.tree u) q (A.depth_le u) f

theorem IsAdaptiveRelativeErrorTester.toNonAdaptive {n s q : ℕ}
    {T : PMF (DetAdaptiveTester n s q)} {C : ((Fin n → Bool) → Bool) → Prop} {ε p : ℝ}
    (hT : IsAdaptiveRelativeErrorTester T C ε p) :
    IsRelativeErrorTester (T.map DetAdaptiveTester.toNonAdaptive) C ε p where
  accept f hf hCf := by
    have heq : nonAdaptiveAcceptProb (T.map DetAdaptiveTester.toNonAdaptive) f hf =
        adaptiveAcceptProb T f hf := by
      simp only [nonAdaptiveAcceptProb, adaptiveAcceptProb, PMF.bind_map, Function.comp_def]
      refine congrArg (fun p : PMF Bool => (p true).toReal) ?_
      refine congrArg (T.bind ·) (funext fun A => ?_)
      congr 1; funext u
      exact A.eval_toNonAdaptive f u
    rw [heq]; exact hT.accept f hf hCf
  reject f hf hfar := by
    have heq : nonAdaptiveAcceptProb (T.map DetAdaptiveTester.toNonAdaptive) f hf =
        adaptiveAcceptProb T f hf := by
      simp only [nonAdaptiveAcceptProb, adaptiveAcceptProb, PMF.bind_map, Function.comp_def]
      refine congrArg (fun p : PMF Bool => (p true).toReal) ?_
      refine congrArg (T.bind ·) (funext fun A => ?_)
      congr 1; funext u
      exact A.eval_toNonAdaptive f u
    rw [heq]; exact hT.reject f hf hfar

/-- Yao's distributional principle for relative-error testers: if `T` is a relative-error
`ε`-tester for `C` with success probability `p ≥ 1/2`, `μ_yes` is supported on nonempty functions
in `C`, and `μ_no` is supported on nonempty functions assigning probability at least `α` to
`ε`-far functions, then some deterministic tester achieves distinguishing advantage at least
`p - (1 - α * p)`. -/
theorem yao_relative_error_distinguishing_bound {n s q : ℕ}
    {T : PMF (DetNonAdaptiveTester n s q)} {C : ((Fin n → Bool) → Bool) → Prop} {ε p α : ℝ}
    (hT : IsRelativeErrorTester T C ε p) (hp : 1 / 2 ≤ p)
    {μ_yes μ_no : PMF ((Fin n → Bool) → Bool)}
    (hyes_supp : ∀ f ∈ μ_yes.support, (satisfyingSet f).Nonempty ∧ C f)
    (hno_supp : ∀ f ∈ μ_no.support, (satisfyingSet f).Nonempty)
    (hno_far : α ≤ (μ_no.toOuterMeasure {g | ε ≤ relDistToClass g C}).toReal) :
    ∃ A : DetNonAdaptiveTester n s q,
      p - (1 - α * p) ≤ distAcceptProb μ_yes A - distAcceptProb μ_no A := by
  classical
  have havg : ∀ μ : PMF ((Fin n → Bool) → Bool),
      ∑ A, (T A).toReal * distAcceptProb μ A =
        ∑ f, (μ f).toReal *
          (if hf : (satisfyingSet f).Nonempty then nonAdaptiveAcceptProb T f hf else 0) := by
    intro μ
    simp only [distAcceptProb, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · have hbind : nonAdaptiveAcceptProb T f hf = ∑ A, (T A).toReal * A.acceptProb f hf := by
        unfold nonAdaptiveAcceptProb DetNonAdaptiveTester.acceptProb
        rw [Cslib.Probability.PMF.bind_apply_toReal]
      rw [hbind, mul_sum]; refine sum_congr rfl fun _ _ => by ring
    · simp
  have hyes_ge : p ≤ ∑ A, (T A).toReal * distAcceptProb μ_yes A := by
    rw [havg]
    calc p = ∑ f, (μ_yes f).toReal * p := by
            rw [← sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
      _ ≤ ∑ f, (μ_yes f).toReal *
            (if hf : (satisfyingSet f).Nonempty then nonAdaptiveAcceptProb T f hf else 0) := by
            refine sum_le_sum fun f _ => ?_
            by_cases hm : f ∈ μ_yes.support
            · rcases hyes_supp f hm with ⟨hf, hCf⟩
              simp only [hf, ↓reduceDIte]
              exact mul_le_mul_of_nonneg_left (hT.accept f hf hCf) ENNReal.toReal_nonneg
            · have h0 : (μ_yes f).toReal = 0 := by
                rw [(μ_yes.apply_eq_zero_iff f).2 hm, ENNReal.toReal_zero]
              simp [h0]
  have hno_le : ∑ A, (T A).toReal * distAcceptProb μ_no A ≤ 1 - α * p := by
    rw [havg]
    let Far : Set ((Fin n → Bool) → Bool) := {g | ε ≤ relDistToClass g C}
    calc ∑ f, (μ_no f).toReal *
            (if hf : (satisfyingSet f).Nonempty then nonAdaptiveAcceptProb T f hf else 0)
        ≤ ∑ f, (μ_no f).toReal * (if f ∈ Far then 1 - p else 1) := by
          refine sum_le_sum fun f _ => ?_
          by_cases hm : f ∈ μ_no.support
          · have hf := hno_supp f hm
            simp only [hf, ↓reduceDIte]
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            split_ifs with hfar
            · exact hT.reject f hf hfar
            · exact Cslib.Probability.PMF.toReal_apply_le_one _ _
          · have h0 : (μ_no f).toReal = 0 := by
              rw [(μ_no.apply_eq_zero_iff f).2 hm, ENNReal.toReal_zero]
            simp [h0]
      _ = (μ_no.toOuterMeasure Far).toReal * (1 - p) +
        (1 - (μ_no.toOuterMeasure Far).toReal) * 1 := by
          have hcompl : (μ_no.toOuterMeasure Farᶜ).toReal =
            1 - (μ_no.toOuterMeasure Far).toReal := by
            linarith [Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ_no Far]
          rw [← hcompl, Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
            Cslib.Probability.PMF.toOuterMeasure_apply_toReal, sum_mul, sum_mul, ← sum_add_distrib]
          refine sum_congr rfl fun f _ => ?_
          by_cases hf : f ∈ Far
          · have hnot : f ∉ Farᶜ := fun h => h hf
            simp [hf, hnot]
          · have hmem : f ∈ Farᶜ := hf
            simp [hf, hmem]
      _ = 1 - (μ_no.toOuterMeasure Far).toReal * p := by ring
      _ ≤ 1 - α * p := by nlinarith
  have hdiff : p - (1 - α * p) ≤
      ∑ A, (T A).toReal * (distAcceptProb μ_yes A - distAcceptProb μ_no A) := by
    simp_rw [mul_sub, sum_sub_distrib]; linarith
  by_contra hall
  push Not at hall
  have hlt : ∑ A, (T A).toReal * (distAcceptProb μ_yes A - distAcceptProb μ_no A) <
      p - (1 - α * p) := by
    calc ∑ A, (T A).toReal * (distAcceptProb μ_yes A - distAcceptProb μ_no A)
        < ∑ A, (T A).toReal * (p - (1 - α * p)) := by
          refine sum_lt_sum
            (fun A _ => mul_le_mul_of_nonneg_left (hall A).le ENNReal.toReal_nonneg) ?_
          obtain ⟨A₀, hA₀⟩ := T.support_nonempty
          have hpos : 0 < (T A₀).toReal :=
            ENNReal.toReal_pos ((PMF.mem_support_iff T A₀).1 hA₀) (PMF.apply_ne_top T A₀)
          exact ⟨A₀, mem_univ A₀, mul_lt_mul_of_pos_left (hall A₀) hpos⟩
      _ = p - (1 - α * p) := by rw [← sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
  linarith

/-- A good 4-tuple of points in `{0, 1}^n` supported on pairwise disjoint sets `J₁, J₂, J₃, J₄`
of size `r / 2`. -/
def IsGoodFourTuple {n : ℕ} (r : ℕ) (w : Fin 4 → Fin n → Bool) : Prop :=
  ∃ J₁ J₂ J₃ J₄ : Finset (Fin n),
    J₁.card = r / 2 ∧ J₂.card = r / 2 ∧ J₃.card = r / 2 ∧ J₄.card = r / 2 ∧
    Disjoint J₁ J₂ ∧ Disjoint J₁ J₃ ∧ Disjoint J₁ J₄ ∧
    Disjoint J₂ J₃ ∧ Disjoint J₂ J₄ ∧ Disjoint J₃ J₄ ∧
    (∀ j, w 0 j = decide (j ∈ J₁ ∪ J₃)) ∧
    (∀ j, w 1 j = decide (j ∈ J₁ ∪ J₄)) ∧
    (∀ j, w 2 j = decide (j ∈ J₂ ∪ J₃)) ∧
    (∀ j, w 3 j = decide (j ∈ J₂ ∪ J₄))

/-- A good 4-tuple `w` is violating for `h` if `h(w 0) = h(w 3) ≠ h(w 1) = h(w 2)`. -/
def IsViolatingFourTuple {n : ℕ} (r : ℕ) (h : (Fin n → Bool) → Bool)
    (w : Fin 4 → Fin n → Bool) : Prop :=
  IsGoodFourTuple r w ∧ h (w 0) = h (w 3) ∧ h (w 1) = h (w 2) ∧ h (w 0) ≠ h (w 1)

/-- No linear threshold function (halfspace) has a violating 4-tuple. -/
theorem not_isViolatingFourTuple_of_isLTF {n r : ℕ} {h : (Fin n → Bool) → Bool}
    (hh : Cslib.Circuits.Boolean.WeightedThreshold.IsLTF h) {w : Fin 4 → Fin n → Bool} :
    ¬ IsViolatingFourTuple r h w := by
  rintro ⟨⟨J₁, J₂, J₃, J₄, -, -, -, -, h12, h13, h14, h23, h24, h34, h0, h1, h2, h3⟩,
    h03, h12e, h01⟩
  rcases hh with ⟨a, θ, ha⟩
  have hcoord : ∀ j : Fin n, ((w 0 j).toNat : ℝ) + ((w 3 j).toNat : ℝ) =
      ((w 1 j).toNat : ℝ) + ((w 2 j).toNat : ℝ) := by
    intro j; rw [h0 j, h1 j, h2 j, h3 j]
    by_cases hj1 : j ∈ J₁
    · simp [hj1, Finset.disjoint_left.1 h12 hj1, Finset.disjoint_left.1 h13 hj1,
        Finset.disjoint_left.1 h14 hj1]
    · by_cases hj2 : j ∈ J₂
      · simp [hj1, hj2, Finset.disjoint_left.1 h23 hj2, Finset.disjoint_left.1 h24 hj2]
      · by_cases hj3 : j ∈ J₃
        · simp [hj1, hj2, hj3, Finset.disjoint_left.1 h34 hj3]
        · by_cases hj4 : j ∈ J₄ <;> simp [hj1, hj2, hj3, hj4]
  have hsum : (∑ j : Fin n, a j * ((w 0 j).toNat : ℝ)) +
        (∑ j : Fin n, a j * ((w 3 j).toNat : ℝ)) =
      (∑ j : Fin n, a j * ((w 1 j).toNat : ℝ)) +
        (∑ j : Fin n, a j * ((w 2 j).toNat : ℝ)) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => by rw [← mul_add, ← mul_add, hcoord j]
  have hval (i : Fin 4) :
      h (w i) = decide (θ ≤ ∑ j : Fin n, a j * ((w i j).toNat : ℝ)) := ha (w i)
  cases hv0 : h (w 0)
  · have hv3 : h (w 3) = false := h03.symm.trans hv0
    have hv1 : h (w 1) = true := by
      cases h1' : h (w 1) with
      | false => exact absurd (hv0.trans h1'.symm) h01
      | true => rfl
    have hv2 : h (w 2) = true := h12e.symm.trans hv1
    rw [hval] at hv0 hv1 hv2 hv3
    have : ∑ j : Fin n, a j * ((w 0 j).toNat : ℝ) < θ := by simpa using hv0
    have : ∑ j : Fin n, a j * ((w 3 j).toNat : ℝ) < θ := by simpa using hv3
    have : θ ≤ ∑ j : Fin n, a j * ((w 1 j).toNat : ℝ) := by simpa using hv1
    have : θ ≤ ∑ j : Fin n, a j * ((w 2 j).toNat : ℝ) := by simpa using hv2
    linarith
  · have hv3 : h (w 3) = true := h03.symm.trans hv0
    have hv1 : h (w 1) = false := by
      cases h1' : h (w 1) with
      | false => rfl
      | true => exact absurd (hv0.trans h1'.symm) h01
    have hv2 : h (w 2) = false := h12e.symm.trans hv1
    rw [hval] at hv0 hv1 hv2 hv3
    have : θ ≤ ∑ j : Fin n, a j * ((w 0 j).toNat : ℝ) := by simpa using hv0
    have : θ ≤ ∑ j : Fin n, a j * ((w 3 j).toNat : ℝ) := by simpa using hv3
    have : ∑ j : Fin n, a j * ((w 1 j).toNat : ℝ) < θ := by simpa using hv1
    have : ∑ j : Fin n, a j * ((w 2 j).toNat : ℝ) < θ := by simpa using hv2
    linarith

/-- Any family of pairwise disjoint violating 4-tuples for `g` lower-bounds `hammingDist g h`
for every halfspace `h`. -/
theorem card_disjoint_violating_le_hammingDist {n r : ℕ} {g h : (Fin n → Bool) → Bool}
    (hh : Cslib.Circuits.Boolean.WeightedThreshold.IsLTF h)
    (H : Finset (Fin 4 → Fin n → Bool))
    (hdisj : ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → Disjoint (univ.image w) (univ.image w'))
    (hviol : ∀ w ∈ H, IsViolatingFourTuple r g w) :
    H.card ≤ hammingDist g h := by
  classical
  have hex : ∀ w ∈ H, ∃ i : Fin 4, g (w i) ≠ h (w i) := by
    intro w hw; by_contra hall; push Not at hall
    have hv := hviol w hw
    exact not_isViolatingFourTuple_of_isLTF hh
      ⟨hv.1, by rw [← hall 0, ← hall 3]; exact hv.2.1,
       by rw [← hall 1, ← hall 2]; exact hv.2.2.1, by rw [← hall 0, ← hall 1]; exact hv.2.2.2⟩
  let f : (Fin 4 → Fin n → Bool) → (Fin n → Bool) := fun w =>
    if hw : w ∈ H then w (hex w hw).choose else fun _ => false
  refine Finset.card_le_card_of_injOn f (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)
  · simp only [Finset.mem_coe] at hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, f, hw, ↓reduceDIte]
    exact (hex w hw).choose_spec
  · by_contra hne
    simp only [Finset.mem_coe] at hw₁ hw₂
    have hd := hdisj w₁ hw₁ w₂ hw₂ hne
    have hm1 : f w₁ ∈ univ.image w₁ := by
      simp only [f, hw₁, ↓reduceDIte]; exact mem_image_of_mem w₁ (mem_univ _)
    have hm2 : f w₂ ∈ univ.image w₂ := by
      simp only [f, hw₂, ↓reduceDIte]; exact mem_image_of_mem w₂ (mem_univ _)
    rw [hfeq] at hm1
    exact Finset.disjoint_left.1 hd hm1 hm2

end CslibFrontier.Computability.PropertyTesting.RelativeError
