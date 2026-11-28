module

public import CslibFrontier.Computability.DecisionTree.Cost
public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalCost
public import CslibFrontier.Computability.QueryComplexity.Randomized.ZeroError
public import CslibFrontier.Computability.QueryComplexity.Yao
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Product
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Computability.QueryComplexity.YaoExpected
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Product.Resample
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Query Elimination and Influence Lower Bounds on Query Complexity

This module develops general-alphabet deterministic query trees, coordinate influence under
independent product distributions, and query-elimination lower bounds on distributional,
bounded-error randomized, and zero-error randomized query complexity.

Given a function `f : (ι → α) → β` over a finite coordinate index type `ι` and a finite input
alphabet `α`, together with independent coordinate distributions `μ : ι → PMF α`, the influence
of coordinate `i` on `f` is `Pr[f(X) ≠ f(X^i)]`, where `X` is drawn from the independent product
`PMF.pi μ` and `X^i` resamples coordinate `i` independently from `μ i`. Eliminating the root
query `i` of a deterministic query tree by substituting an independent draw `Y_i ~ μ i` (and
pruning any subsequent queries to `i`) reduces worst-case query depth by one and expected query
count by at least one while increasing distributional error by at most the influence of `i`.

Iterating this single-step elimination proves:
- a worst-case distributional query complexity lower bound in terms of the maximum coordinate
  influence and the complement of the maximum output probability;
- an expected-query distributional lower bound for arbitrary deterministic query trees;
- a smoothed distributional lower bound via any close approximating function `g`;
- Markov truncation relating bounded-error and zero-error randomized query complexity; and
- the variance-over-influence lower bound on zero-error randomized query complexity for Boolean
  functions under independent biased product distributions.

## Main definitions

- `CslibFrontier.QueryComplexity.QueryTree`: deterministic adaptive query trees over arbitrary
  input alphabets `α` and output types `β`.
- `CslibFrontier.QueryComplexity.distributionalComplexity`: minimum worst-case depth of a
  deterministic query tree with bounded distributional error under an input distribution.
- `CslibFrontier.QueryComplexity.coordInfluence`,
  `CslibFrontier.QueryComplexity.maxCoordInfluence`: coordinate and maximum coordinate influence
  under an independent product distribution.
- `CslibFrontier.QueryComplexity.maxOutputProb`: maximum probability of any single output value.
- `CslibFrontier.QueryComplexity.elimFirst`: single-step root query elimination.
- `CslibFrontier.QueryComplexity.boolVariance`: variance of a `{-1, +1}`-valued Boolean function
  under a discrete input distribution.

## Main results

- `CslibFrontier.QueryComplexity.exists_query_elimination_step`: deterministic one-step query
  elimination reducing worst-case depth by one with error increase at most `maxCoordInfluence`.
- `CslibFrontier.QueryComplexity.one_sub_maxOutputProb_le_distributionalError_add_expectedCost`:
  expected-query influence lower bound for arbitrary deterministic query trees.
- `CslibFrontier.QueryComplexity.distributionalComplexity_ge_div_maxCoordInfluence`:
  distributional query complexity lower bound via maximum coordinate influence.
- `CslibFrontier.QueryComplexity.smoothed_div_coord`: smoothed distributional influence lower
  bound via any close approximating function.
- `CslibFrontier.QueryComplexity.mul_randomizedComplexity_le_zeroErrorComplexity`: Markov
  truncation bound `ε * R_ε(f) ≤ R_0(f)`.
- `CslibFrontier.QueryComplexity.randomizedComplexity_ge_div_maxCoordInfluence`: bounded-error
  randomized query complexity lower bound via Yao's minimax principle.
- `CslibFrontier.QueryComplexity.zeroErrorComplexity_ge_variance_div`: variance-over-influence
  lower bound on zero-error randomized query complexity for Boolean functions.
-/

public section

namespace CslibFrontier.QueryComplexity

open scoped BigOperators ENNReal NNReal unitInterval
open Cslib Cslib.Probability

/-! ### General-alphabet deterministic query trees -/

/-- A deterministic adaptive query tree querying coordinates in `ι` with input alphabet `α` and
producing outputs in `β`. -/
inductive QueryTree (ι : Type*) (α : Type*) (β : Type*) : Type _ where
  /-- Output `val` without querying any further coordinates. -/
  | leaf (val : β) : QueryTree ι α β
  /-- Query coordinate `idx` and branch on its value in `α`. -/
  | node (idx : ι) (branch : α → QueryTree ι α β) : QueryTree ι α β

namespace QueryTree

section Core

variable {ι α β : Type*}

/-- Output produced by query tree `t` on input `x`. -/
def eval : QueryTree ι α β → (ι → α) → β
  | leaf b, _ => b
  | node i branch, x => (branch (x i)).eval x

/-- Number of queries executed by `t` on input `x`. -/
def cost : QueryTree ι α β → (ι → α) → ℕ
  | leaf _, _ => 0
  | node i branch, x => (branch (x i)).cost x + 1

/-- Worst-case structural depth of `t` in `ℕ∞`. -/
noncomputable def edepth : QueryTree ι α β → ℕ∞
  | leaf _ => 0
  | node _ branch => (⨆ a, (branch a).edepth) + 1

@[simp] theorem eval_leaf (b : β) (x : ι → α) : (leaf b : QueryTree ι α β).eval x = b := by
  rfl

@[simp] theorem eval_node (i : ι) (branch : α → QueryTree ι α β) (x : ι → α) :
    (node i branch).eval x = (branch (x i)).eval x := by
  rfl

@[simp] theorem cost_leaf (b : β) (x : ι → α) : (leaf b : QueryTree ι α β).cost x = 0 := by
  rfl

@[simp] theorem cost_node (i : ι) (branch : α → QueryTree ι α β) (x : ι → α) :
    (node i branch).cost x = (branch (x i)).cost x + 1 := by
  rfl

@[simp] theorem edepth_leaf (b : β) : (leaf b : QueryTree ι α β).edepth = 0 := by
  rfl

@[simp] theorem edepth_node (i : ι) (branch : α → QueryTree ι α β) :
    (node i branch).edepth = (⨆ a, (branch a).edepth) + 1 := by
  rfl

/-- A query tree has zero depth iff it is a leaf. -/
theorem edepth_eq_zero_iff (t : QueryTree ι α β) : t.edepth = 0 ↔ ∃ b, t = leaf b := by
  cases t with
  | leaf b => exact ⟨fun _ ↦ ⟨b, rfl⟩, fun _ ↦ rfl⟩
  | node i branch => simp [edepth_node]

/-- Depth bound characterization for an internal node. -/
theorem edepth_node_le_succ_iff (i : ι) (branch : α → QueryTree ι α β) (k : ℕ) :
    (node i branch).edepth ≤ (k + 1 : ℕ) ↔ ∀ a, (branch a).edepth ≤ (k : ℕ) := by
  rw [edepth_node, Nat.cast_add, Nat.cast_one]
  constructor
  · intro h a
    have hsup : (⨆ b, (branch b).edepth) ≤ (k : ℕ∞) :=
      (ENat.add_le_add_iff_right (k := 1) (by simp)).mp h
    exact (le_iSup (fun b ↦ (branch b).edepth) a).trans hsup
  · intro h
    exact add_le_add (iSup_le h) le_rfl

/-- Executed query count on any input is bounded by structural depth. -/
theorem cost_le_edepth (t : QueryTree ι α β) (x : ι → α) : (t.cost x : ℕ∞) ≤ t.edepth := by
  induction t with
  | leaf b => simp
  | node i branch ih =>
    simp only [cost_node, edepth_node, Nat.cast_add, Nat.cast_one]
    exact add_le_add ((ih (x i)).trans (le_iSup (fun a ↦ (branch a).edepth) (x i))) le_rfl

/-- Every query tree over a finite alphabet has finite structural depth. -/
theorem edepth_ne_top [Finite α] (t : QueryTree ι α β) : t.edepth ≠ ⊤ := by
  induction t with
  | leaf b => simp
  | node i branch ih =>
    let _ := Fintype.ofFinite α
    rw [edepth_node]
    set M : ℕ := Finset.univ.sup fun a : α ↦ (branch a).edepth.toNat
    have hsup : (⨆ a : α, (branch a).edepth) ≤ (M : ℕ∞) := by
      refine iSup_le fun a ↦ ?_
      rw [← ENat.natCast_toNat (ih a)]
      exact Nat.cast_le.mpr
        (Finset.le_sup (f := fun b : α ↦ (branch b).edepth.toNat) (Finset.mem_univ a))
    have hlt : (⨆ a : α, (branch a).edepth) + 1 < ⊤ :=
      (add_le_add hsup le_rfl).trans_lt
        (by rw [← Nat.cast_one, ← Nat.cast_add]; exact ENat.natCast_lt_top _)
    exact hlt.ne

/-- Worst-case structural depth of a query tree in `ℕ` (matching `edepth` on finite alphabets
via `coe_depth`). -/
noncomputable def depth (t : QueryTree ι α β) : ℕ :=
  t.edepth.toNat

/-- Casting `depth` to `ℕ∞` recovers `edepth`. -/
@[simp] theorem coe_depth [Finite α] (t : QueryTree ι α β) : (t.depth : ℕ∞) = t.edepth :=
  ENat.natCast_toNat (edepth_ne_top t)

@[simp] theorem depth_leaf (b : β) : (leaf b : QueryTree ι α β).depth = 0 := by
  simp [depth]

/-- Every branch of an internal node has strictly smaller depth than the node. -/
theorem depth_branch_lt [Finite α] (i : ι) (branch : α → QueryTree ι α β) (a : α) :
    (branch a).depth < (node i branch).depth := by
  have hle : (branch a).edepth + 1 ≤ (node i branch).edepth := by
    rw [edepth_node]
    exact add_le_add (le_iSup (fun b ↦ (branch b).edepth) a) le_rfl
  rw [← coe_depth (branch a), ← coe_depth (node i branch)] at hle
  have : (branch a).depth + 1 ≤ (node i branch).depth := by exact_mod_cast hle
  omega

/-- A query tree over a finite alphabet has depth zero iff it is a leaf. -/
theorem depth_eq_zero_iff [Finite α] (t : QueryTree ι α β) : t.depth = 0 ↔ ∃ b, t = leaf b := by
  rw [← edepth_eq_zero_iff, ← coe_depth t, Nat.cast_eq_zero]

/-- Depth bound characterization for an internal node over a finite alphabet. -/
theorem depth_node_le_succ_iff [Finite α] (i : ι) (branch : α → QueryTree ι α β) (k : ℕ) :
    (node i branch).depth ≤ k + 1 ↔ ∀ a, (branch a).depth ≤ k := by
  have h := edepth_node_le_succ_iff i branch k
  simp only [← coe_depth, Nat.cast_le] at h
  exact h

/-- Executed query count on any input is bounded by finite depth. -/
theorem cost_le_depth [Finite α] (t : QueryTree ι α β) (x : ι → α) : t.cost x ≤ t.depth := by
  have h := cost_le_edepth t x
  rw [← coe_depth t] at h
  exact_mod_cast h

/-- Deterministic query trees as a `Cslib.RandomizedCost` model. -/
noncomputable def randomizedCost (ι α β : Type*) :
    RandomizedCost (QueryTree ι α β) (ι → α) β :=
  ⟨eval, depth⟩

end Core

section RestrictAndQueryAll

variable {ι α β : Type*} [DecidableEq ι]

/-- Fix coordinate `i` to value `y`, removing all queries to `i`. -/
def restrictCoord (i : ι) (y : α) : QueryTree ι α β → QueryTree ι α β
  | leaf b => leaf b
  | node j branch =>
    if j = i then restrictCoord i y (branch y)
    else node j fun a ↦ restrictCoord i y (branch a)

@[simp] theorem restrictCoord_leaf (i : ι) (y : α) (b : β) :
    (leaf b : QueryTree ι α β).restrictCoord i y = leaf b := by
  rfl

/-- Evaluating `restrictCoord i y t` on `x` equals evaluating `t` on `Function.update x i y`. -/
theorem eval_restrictCoord (i : ι) (y : α) (t : QueryTree ι α β) (x : ι → α) :
    (t.restrictCoord i y).eval x = t.eval (Function.update x i y) := by
  induction t with
  | leaf b => rfl
  | node j branch ih =>
    by_cases hji : j = i
    · subst hji
      simp only [restrictCoord, ↓reduceIte, eval_node, Function.update_self]
      exact ih y
    · simp only [restrictCoord, hji, ↓reduceIte, eval_node, Function.update_of_ne hji]
      exact ih (x j)

/-- Restricting coordinate `i` to `y` never increases executed query count on the updated input. -/
theorem cost_restrictCoord_le (i : ι) (y : α) (t : QueryTree ι α β) (x : ι → α) :
    (t.restrictCoord i y).cost x ≤ t.cost (Function.update x i y) := by
  induction t with
  | leaf b => simp [restrictCoord]
  | node j branch ih =>
    by_cases hji : j = i
    · subst hji
      simp only [restrictCoord, ↓reduceIte, cost_node, Function.update_self]
      exact (ih y).trans (Nat.le_succ _)
    · simp only [restrictCoord, hji, ↓reduceIte, cost_node, Function.update_of_ne hji]
      exact Nat.add_le_add_right (ih (x j)) 1

/-- Restricting coordinate `i` to `y` never increases structural depth. -/
theorem edepth_restrictCoord_le (i : ι) (y : α) (t : QueryTree ι α β) :
    (t.restrictCoord i y).edepth ≤ t.edepth := by
  induction t with
  | leaf b => simp [restrictCoord]
  | node j branch ih =>
    by_cases hji : j = i
    · subst hji
      simp only [restrictCoord, ↓reduceIte, edepth_node]
      exact (ih y).trans ((le_iSup (fun a ↦ (branch a).edepth) y).trans le_self_add)
    · simp only [restrictCoord, hji, ↓reduceIte, edepth_node]
      exact add_le_add (iSup_mono fun a ↦ ih a) le_rfl

/-- Restricting coordinate `i` to `y` never increases finite depth. -/
theorem depth_restrictCoord_le [Finite α] (i : ι) (y : α) (t : QueryTree ι α β) :
    (t.restrictCoord i y).depth ≤ t.depth := by
  have h := edepth_restrictCoord_le i y t
  simp only [← coe_depth, Nat.cast_le] at h
  exact h

/-- Query every coordinate in `l` starting from default assignment `a` and output `f`. -/
def queryAll : List ι → ((ι → α) → β) → (ι → α) → QueryTree ι α β
  | [], f, a => leaf (f a)
  | i :: l, f, a => node i fun v ↦ queryAll l f (Function.update a i v)

/-- Evaluating `queryAll l f a` on `x` returns `f` on the assignment matching `x` on `l`. -/
theorem eval_queryAll (l : List ι) (f : (ι → α) → β) (a x : ι → α) :
    (queryAll l f a).eval x = f (fun j ↦ if j ∈ l then x j else a j) := by
  induction l generalizing a with
  | nil => simp [queryAll]
  | cons i l ih =>
    simp only [queryAll, eval_node, ih]
    congr 1
    funext j
    by_cases hjl : j ∈ l
    · simp [hjl]
    · by_cases hji : j = i
      · subst hji; simp
      · simp [hjl, hji]

/-- Structural depth of `queryAll l f a` is at most `l.length`. -/
theorem edepth_queryAll_le (l : List ι) (f : (ι → α) → β) (a : ι → α) :
    (queryAll l f a).edepth ≤ (l.length : ℕ∞) := by
  induction l generalizing a with
  | nil => simp [queryAll]
  | cons i l ih =>
    simp only [queryAll, List.length_cons]
    exact (edepth_node_le_succ_iff i _ l.length).mpr fun v ↦ ih (Function.update a i v)

omit [DecidableEq ι] in
/-- Every function on finitely many coordinates over a nonempty alphabet has an exact query tree
of depth at most `Fintype.card ι`. -/
theorem exists_exact [Fintype ι] [Nonempty α] (f : (ι → α) → β) :
    ∃ t : QueryTree ι α β, (∀ x, t.eval x = f x) ∧ t.edepth ≤ (Fintype.card ι : ℕ∞) := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty α›
  refine ⟨queryAll Finset.univ.toList f (fun _ ↦ a₀), fun x ↦ ?_, ?_⟩
  · simp [eval_queryAll]
  · simpa using edepth_queryAll_le Finset.univ.toList f (fun _ ↦ a₀)

end RestrictAndQueryAll

section ErrorAndCost

variable {ι α β : Type*}

/-- Distributional error of `t` for computing `f` under input distribution `ν`. -/
noncomputable def distributionalError (t : QueryTree ι α β) (ν : PMF (ι → α))
    (f : (ι → α) → β) : ℝ :=
  PMF.errorProb (fun x (t : QueryTree ι α β) ↦ t.eval x = f x) ν t

/-- Agreement with `Cslib.RandomizedCost.distributionalError`. -/
theorem distributionalError_eq_randomizedCost (t : QueryTree ι α β)
    (ν : PMF (ι → α)) (f : (ι → α) → β) :
    t.distributionalError ν f =
      (QueryTree.randomizedCost ι α β).distributionalError t ν (fun x z ↦ z = f x) := by
  rfl

/-- Outer-measure expression for distributional error. -/
theorem distributionalError_eq_toOuterMeasure (t : QueryTree ι α β) (ν : PMF (ι → α))
    (f : (ι → α) → β) :
    t.distributionalError ν f = (ν.toOuterMeasure {x | t.eval x ≠ f x}).toReal := by
  rfl

theorem distributionalError_nonneg (t : QueryTree ι α β) (ν : PMF (ι → α))
    (f : (ι → α) → β) : 0 ≤ t.distributionalError ν f :=
  PMF.errorProb_nonneg

theorem distributionalError_le_one (t : QueryTree ι α β) (ν : PMF (ι → α))
    (f : (ι → α) → β) : t.distributionalError ν f ≤ 1 :=
  PMF.errorProb_le_one

/-- An exact query tree has zero distributional error under every input distribution. -/
theorem distributionalError_eq_zero_of_exact {t : QueryTree ι α β} {f : (ι → α) → β}
    (ht : ∀ x, t.eval x = f x) (ν : PMF (ι → α)) : t.distributionalError ν f = 0 := by
  rw [distributionalError_eq_toOuterMeasure]
  have hemp : {x : ι → α | t.eval x ≠ f x} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
    hx (ht x)
  simp [hemp]

/-- The error of a constant leaf `leaf b` is `1 - Pr[f(X) = b]`. -/
theorem distributionalError_leaf (b : β) (ν : PMF (ι → α)) (f : (ι → α) → β) :
    (leaf b : QueryTree ι α β).distributionalError ν f =
      1 - (ν.toOuterMeasure {x | f x = b}).toReal := by
  rw [distributionalError_eq_toOuterMeasure]
  have hcompl : {x : ι → α | (leaf b : QueryTree ι α β).eval x ≠ f x} =
      ({x : ι → α | f x = b})ᶜ := by
    ext x
    simp [eq_comm]
  rw [hcompl]
  have hsum := PMF.toOuterMeasure_toReal_add_compl ν {x : ι → α | f x = b}
  linarith

/-- Expected number of queries executed by `t` on an input drawn from `ν`. -/
noncomputable def distributionalExpectedCost (t : QueryTree ι α β) (ν : PMF (ι → α)) : ℝ :=
  ∑' x, (ν x).toReal * (t.cost x : ℝ)

@[simp] theorem distributionalExpectedCost_leaf (b : β) (ν : PMF (ι → α)) :
    (leaf b : QueryTree ι α β).distributionalExpectedCost ν = 0 := by
  simp [distributionalExpectedCost]

/-- Finite-sum form of expected query count. -/
theorem distributionalExpectedCost_eq_sum [Fintype (ι → α)]
    (t : QueryTree ι α β) (ν : PMF (ι → α)) :
    t.distributionalExpectedCost ν = ∑ x, (ν x).toReal * (t.cost x : ℝ) :=
  tsum_fintype _

end ErrorAndCost

section BoolBridge

variable {ι β : Type*}

/-- Convert a Boolean-alphabet `QueryTree ι Bool β` to a `Cslib.DecisionTree ι β`. -/
def toDecisionTree : QueryTree ι Bool β → DecisionTree ι β
  | leaf b => DecisionTree.leaf b
  | node i branch => DecisionTree.node i (branch false).toDecisionTree (branch true).toDecisionTree

/-- Convert a `Cslib.DecisionTree ι β` to a Boolean-alphabet `QueryTree ι Bool β`. -/
def ofDecisionTree : DecisionTree ι β → QueryTree ι Bool β
  | DecisionTree.leaf b => leaf b
  | DecisionTree.node i t₀ t₁ => node i fun b ↦ cond b (ofDecisionTree t₁) (ofDecisionTree t₀)

@[simp] theorem toDecisionTree_ofDecisionTree (t : DecisionTree ι β) :
    (ofDecisionTree t).toDecisionTree = t := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => simp [ofDecisionTree, toDecisionTree, ih₀, ih₁]

@[simp] theorem eval_toDecisionTree (t : QueryTree ι Bool β) (x : ι → Bool) :
    t.toDecisionTree.eval x = t.eval x := by
  induction t with
  | leaf b => rfl
  | node i branch ih =>
    simp only [toDecisionTree, DecisionTree.eval_node, eval_node]
    cases hx : x i <;> simp [ih]

@[simp] theorem eval_ofDecisionTree (t : DecisionTree ι β) (x : ι → Bool) :
    (ofDecisionTree t).eval x = t.eval x := by
  rw [← eval_toDecisionTree, toDecisionTree_ofDecisionTree]

@[simp] theorem cost_toDecisionTree (t : QueryTree ι Bool β) (x : ι → Bool) :
    t.toDecisionTree.cost x = t.cost x := by
  induction t with
  | leaf b => rfl
  | node i branch ih =>
    simp only [toDecisionTree, DecisionTree.cost_node, cost_node]
    cases hx : x i <;> simp [ih]

@[simp] theorem depth_toDecisionTree (t : QueryTree ι Bool β) :
    t.toDecisionTree.depth = t.depth := by
  induction t with
  | leaf b => simp [toDecisionTree]
  | node i branch ih =>
    have hsup : (⨆ a : Bool, (branch a).edepth) =
        ((max (branch false).depth (branch true).depth : ℕ) : ℕ∞) := by
      apply le_antisymm
      · refine iSup_le fun b ↦ ?_
        rw [← coe_depth]
        cases b
        · exact Nat.cast_le.mpr (le_max_left _ _)
        · exact Nat.cast_le.mpr (le_max_right _ _)
      · rcases le_total (branch false).depth (branch true).depth with h | h
        · rw [max_eq_right h, coe_depth]
          exact le_iSup (fun b ↦ (branch b).edepth) true
        · rw [max_eq_left h, coe_depth]
          exact le_iSup (fun b ↦ (branch b).edepth) false
    have h : ((node i branch).depth : ℕ∞) =
        ((max (branch false).depth (branch true).depth + 1 : ℕ) : ℕ∞) := by
      rw [coe_depth, edepth_node, hsup, Nat.cast_add, Nat.cast_one]
    have hnat : (node i branch).depth = max (branch false).depth (branch true).depth + 1 := by
      exact_mod_cast h
    simp [toDecisionTree, ih, hnat]

@[simp] theorem depth_ofDecisionTree (t : DecisionTree ι β) :
    (ofDecisionTree t).depth = t.depth := by
  rw [← depth_toDecisionTree, toDecisionTree_ofDecisionTree]

/-- Agreement with `Cslib.DecisionTree.distributionalError` under `PMF.toStdSimplex`. -/
theorem distributionalError_toDecisionTree [Fintype ι] [DecidableEq ι] (t : QueryTree ι Bool β)
    (ν : PMF (ι → Bool)) (f : (ι → Bool) → β) :
    t.toDecisionTree.distributionalError (PMF.toStdSimplex ν) f =
      t.distributionalError ν f := by
  rw [DecisionTree.distributionalError, distributionalError_eq_toOuterMeasure]
  have h := PMF.toOuterMeasure_toReal_ofStdSimplex_setOf (PMF.toStdSimplex ν)
    (fun x ↦ t.toDecisionTree.eval x ≠ f x)
  rw [PMF.ofStdSimplex_toStdSimplex] at h
  simp only [not_not] at h
  simpa only [eval_toDecisionTree] using h.symm

/-- Agreement with `Cslib.DecisionTree.distributionalCost` under `PMF.toStdSimplex`. -/
theorem distributionalExpectedCost_toDecisionTree [Fintype ι] [DecidableEq ι]
    (t : QueryTree ι Bool β) (ν : PMF (ι → Bool)) :
    t.toDecisionTree.distributionalCost (PMF.toStdSimplex ν) =
      t.distributionalExpectedCost ν := by
  rw [DecisionTree.distributionalCost_eq_sum, distributionalExpectedCost_eq_sum,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [PMF.weights_toStdSimplex, cost_toDecisionTree]

end BoolBridge

end QueryTree

/-! ### Distributional query complexity, influence, and maximum output probability -/

section DistributionalComplexity

variable {ι α β : Type*}

/-- Minimum worst-case depth of a deterministic query tree whose error under `ν` is at most `ε`.
-/
noncomputable def distributionalComplexity (ε : ℝ) (ν : PMF (ι → α))
    (f : (ι → α) → β) : ℕ :=
  ((QueryTree.randomizedCost ι α β).distributionalComplexity ε (fun x z ↦ z = f x) ν).toNat

variable [Finite α]

private theorem randomizedCost_distributionalComplexity_le_card [Fintype ι] {ε : ℝ} (hε : 0 ≤ ε)
    (ν : PMF (ι → α)) (f : (ι → α) → β) :
    (QueryTree.randomizedCost ι α β).distributionalComplexity ε (fun x z ↦ z = f x) ν ≤
      (Fintype.card ι : ℕ∞) := by
  classical
  obtain ⟨x₀, _⟩ := ν.support_nonempty
  have hne : Nonempty α ∨ IsEmpty ι := by
    by_cases hi : Nonempty ι
    · exact Or.inl ⟨x₀ hi.some⟩
    · exact Or.inr (not_nonempty_iff.mp hi)
  rcases hne with hα | hι
  · obtain ⟨t, hteval, htdepth⟩ := QueryTree.exists_exact f
    have herr : (QueryTree.randomizedCost ι α β).distributionalError t ν (fun x z ↦ z = f x) ≤
        ε := by
      rw [← QueryTree.distributionalError_eq_randomizedCost,
        QueryTree.distributionalError_eq_zero_of_exact hteval ν]
      exact hε
    refine (RandomizedCost.distributionalComplexity_le_cost herr).trans ?_
    simpa [QueryTree.randomizedCost] using htdepth
  · have hconst : ∀ x : ι → α, (QueryTree.leaf (f x₀) : QueryTree ι α β).eval x = f x := by
      intro x; rw [QueryTree.eval_leaf]; congr 1; funext i; exact isEmptyElim i
    have herr : (QueryTree.randomizedCost ι α β).distributionalError
        (QueryTree.leaf (f x₀)) ν (fun x z ↦ z = f x) ≤ ε := by
      rw [← QueryTree.distributionalError_eq_randomizedCost,
        QueryTree.distributionalError_eq_zero_of_exact hconst ν]
      exact hε
    refine (RandomizedCost.distributionalComplexity_le_cost herr).trans ?_
    simp [QueryTree.randomizedCost]

private theorem coe_distributionalComplexity [Finite ι] {ε : ℝ} (hε : 0 ≤ ε) (ν : PMF (ι → α))
    (f : (ι → α) → β) :
    (distributionalComplexity ε ν f : ℕ∞) =
      (QueryTree.randomizedCost ι α β).distributionalComplexity ε (fun x z ↦ z = f x) ν := by
  let _ := Fintype.ofFinite ι
  exact ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    (randomizedCost_distributionalComplexity_le_card hε ν f))

/-- Any query tree with error at most `ε` upper-bounds `distributionalComplexity`. -/
theorem distributionalComplexity_le_depth [Finite ι] {t : QueryTree ι α β} {ε : ℝ}
    {ν : PMF (ι → α)} {f : (ι → α) → β} (ht : t.distributionalError ν f ≤ ε) :
    distributionalComplexity ε ν f ≤ t.depth := by
  have hε : 0 ≤ ε := (t.distributionalError_nonneg ν f).trans ht
  have h := RandomizedCost.distributionalComplexity_le_cost
    (C := QueryTree.randomizedCost ι α β) (R := fun x z ↦ z = f x) (ν := ν) (m := t) ht
  rw [← coe_distributionalComplexity hε ν f] at h
  exact_mod_cast h

/-- Attainment of `distributionalComplexity` for `0 ≤ ε`. -/
theorem exists_distributionalError_le_depth_eq_distributionalComplexity [Finite ι] {ε : ℝ}
    (hε : 0 ≤ ε) (ν : PMF (ι → α)) (f : (ι → α) → β) :
    ∃ t : QueryTree ι α β,
      t.distributionalError ν f ≤ ε ∧ t.depth = distributionalComplexity ε ν f := by
  have h := RandomizedCost.distributionalComplexity_le_iff
    (C := QueryTree.randomizedCost ι α β) (R := fun x z ↦ z = f x) (ν := ν) (ε := ε)
    (k := distributionalComplexity ε ν f)
  rw [← coe_distributionalComplexity hε ν f, Nat.cast_le] at h
  obtain ⟨t, herr, hle⟩ := h.mp le_rfl
  exact ⟨t, herr, le_antisymm hle (distributionalComplexity_le_depth herr)⟩

/-- Agreement with `Cslib.QueryComplexity.distributionalComplexity` on Boolean inputs. -/
theorem distributionalComplexity_eq_cslib [Fintype ι] [DecidableEq ι] (ε : ℝ≥0)
    (ν : PMF (ι → Bool)) (f : (ι → Bool) → β) :
    distributionalComplexity (ε : ℝ) ν f =
      Cslib.QueryComplexity.distributionalComplexity ε (PMF.toStdSimplex ν) f := by
  apply le_antisymm
  · obtain ⟨t, ht, hd⟩ :=
      Cslib.QueryComplexity.exists_distributionalError_le_depth_eq_distributionalComplexity
        (ε := ε) (PMF.toStdSimplex ν) f
    have ht' : (QueryTree.ofDecisionTree t).distributionalError ν f ≤ (ε : ℝ) := by
      have hbr := QueryTree.distributionalError_toDecisionTree (QueryTree.ofDecisionTree t) ν f
      rw [QueryTree.toDecisionTree_ofDecisionTree] at hbr
      rwa [← hbr]
    exact (distributionalComplexity_le_depth ht').trans_eq (by simp [hd])
  · obtain ⟨t, ht, hd⟩ :=
      exists_distributionalError_le_depth_eq_distributionalComplexity ε.coe_nonneg ν f
    have ht' : t.toDecisionTree.distributionalError (PMF.toStdSimplex ν) f ≤ (ε : ℝ) := by
      rwa [QueryTree.distributionalError_toDecisionTree]
    exact (Cslib.QueryComplexity.distributionalComplexity_le_depth ht').trans_eq (by simp [hd])

end DistributionalComplexity

section InfluenceAndMaxOutput

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Finite α]

/-- Joint law of `(X, X^i)` where `X ~ PMF.pi μ` and coordinate `i` is resampled from `μ i`. -/
noncomputable def resamplePair (μ : ι → PMF α) (i : ι) : PMF ((ι → α) × (ι → α)) :=
  (PMF.pi μ).bind fun x ↦ (μ i).map fun y ↦ (x, Function.update x i y)

/-- Influence of coordinate `i` on `f` under independent coordinate distributions `μ`. -/
noncomputable def coordInfluence (μ : ι → PMF α) (f : (ι → α) → β) (i : ι) : ℝ :=
  ((resamplePair μ i).toOuterMeasure {p | f p.1 ≠ f p.2}).toReal

/-- Maximum coordinate influence `max_i coordInfluence μ f i`. -/
noncomputable def maxCoordInfluence (μ : ι → PMF α) (f : (ι → α) → β) : ℝ :=
  ⨆ i : ι, coordInfluence μ f i

theorem coordInfluence_nonneg (μ : ι → PMF α) (f : (ι → α) → β) (i : ι) :
    0 ≤ coordInfluence μ f i :=
  ENNReal.toReal_nonneg

theorem coordInfluence_le_maxCoordInfluence (μ : ι → PMF α) (f : (ι → α) → β) (i : ι) :
    coordInfluence μ f i ≤ maxCoordInfluence μ f :=
  le_ciSup (Set.finite_range _).bddAbove i

theorem maxCoordInfluence_nonneg (μ : ι → PMF α) (f : (ι → α) → β) :
    0 ≤ maxCoordInfluence μ f := by
  by_cases h : Nonempty ι
  · exact (coordInfluence_nonneg μ f h.some).trans
      (coordInfluence_le_maxCoordInfluence μ f h.some)
  · have : IsEmpty ι := not_nonempty_iff.mp h
    simp [maxCoordInfluence]

private theorem coordInfluence_eq_bind_swap (μ : ι → PMF α) (f : (ι → α) → β) (i : ι) :
    coordInfluence μ f i =
      (((μ i).bind fun y ↦ (PMF.pi μ).map fun x ↦ (x, Function.update x i y)).toOuterMeasure
        {p | f p.2 ≠ f p.1}).toReal := by
  classical
  let _ := Fintype.ofFinite α
  rw [coordInfluence, resamplePair, PMF.toOuterMeasure_bind_toReal, PMF.toOuterMeasure_bind_toReal]
  have hL (x : ι → α) :
      (((μ i).map fun y ↦ (x, Function.update x i y)).toOuterMeasure {p | f p.1 ≠ f p.2}).toReal =
        ∑ y : α, (μ i y).toReal * if f x ≠ f (Function.update x i y) then (1 : ℝ) else 0 := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_toReal]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases h : f x ≠ f (Function.update x i y) <;> simp [h]
  have hR (y : α) :
      (((PMF.pi μ).map fun x ↦ (x, Function.update x i y)).toOuterMeasure
          {p | f p.2 ≠ f p.1}).toReal =
        ∑ x : ι → α, (PMF.pi μ x).toReal *
          if f (Function.update x i y) ≠ f x then (1 : ℝ) else 0 := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_toReal]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : f (Function.update x i y) ≠ f x <;> simp [h]
  simp_rw [hL, hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h : f x = f (Function.update x i y)
  · simp [h]
  · have h' : f (Function.update x i y) ≠ f x := Ne.symm h
    simp only [ne_eq, h, not_false_eq_true, ↓reduceIte, h']
    ring

end InfluenceAndMaxOutput

/-- Maximum probability of any single output value `max_z Pr_{X ~ ν}[f(X) = z]`. -/
noncomputable def maxOutputProb {X β : Type*} (ν : PMF X) (f : X → β) : ℝ :=
  ⨆ z : β, (ν.toOuterMeasure {x | f x = z}).toReal

theorem prob_eq_le_maxOutputProb {X β : Type*} (ν : PMF X) (f : X → β) (z : β) :
    (ν.toOuterMeasure {x | f x = z}).toReal ≤ maxOutputProb ν f :=
  le_ciSup
    (⟨1, by rintro _ ⟨w, rfl⟩; exact PMF.toOuterMeasure_toReal_le_one _ _⟩ :
      BddAbove (Set.range fun w : β ↦ (ν.toOuterMeasure {x | f x = w}).toReal)) z

theorem maxOutputProb_bool {X : Type*} (ν : PMF X) (f : X → Bool) :
    maxOutputProb ν f =
      max (ν.toOuterMeasure {x | f x = false}).toReal
        (ν.toOuterMeasure {x | f x = true}).toReal := by
  apply le_antisymm
  · refine ciSup_le fun b ↦ ?_
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (prob_eq_le_maxOutputProb ν f false) (prob_eq_le_maxOutputProb ν f true)

/-! ### Query elimination and distributional / randomized lower bounds -/

section ElimFirst

variable {ι α β : Type*} [DecidableEq ι]

/-- Eliminate the root query `i` by fixing its answer to `y` and pruning subsequent queries to `i`.
-/
def elimFirst (i : ι) (branch : α → QueryTree ι α β) (y : α) : QueryTree ι α β :=
  (branch y).restrictCoord i y

theorem eval_elimFirst (i : ι) (branch : α → QueryTree ι α β) (y : α) (x : ι → α) :
    (elimFirst i branch y).eval x = (QueryTree.node i branch).eval (Function.update x i y) := by
  rw [elimFirst, QueryTree.eval_restrictCoord, QueryTree.eval_node, Function.update_self]

theorem cost_elimFirst_add_one_le (i : ι) (branch : α → QueryTree ι α β) (y : α) (x : ι → α) :
    (elimFirst i branch y).cost x + 1 ≤ (QueryTree.node i branch).cost (Function.update x i y) := by
  rw [elimFirst, QueryTree.cost_node, Function.update_self]
  exact Nat.add_le_add_right (QueryTree.cost_restrictCoord_le i y (branch y) x) 1

theorem depth_elimFirst_le [Finite α] {i : ι} {branch : α → QueryTree ι α β} {k : ℕ}
    (hk : (QueryTree.node i branch).depth ≤ k + 1) (y : α) :
    (elimFirst i branch y).depth ≤ k :=
  (QueryTree.depth_restrictCoord_le i y (branch y)).trans
    ((QueryTree.depth_node_le_succ_iff i branch k).mp hk y)

end ElimFirst

section QueryElimination

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Finite α]

private theorem bind_pi_update_self (μ : ι → PMF α) (i : ι) :
    (μ i).bind (fun y ↦ (PMF.pi μ).map fun x ↦ Function.update x i y) = PMF.pi μ := by
  have h := PMF.bind_pi_function_update (p := μ) i (μ i) PMF.pure
  simpa only [PMF.map, Function.comp_def, Function.update_eq_self, PMF.bind_pure] using h

/-- Averaging the error of `elimFirst i branch y` over `y ~ μ i` adds at most
`coordInfluence μ f i` to the distributional error of `node i branch`. -/
theorem average_distributionalError_elimFirst_le (μ : ι → PMF α) (f : (ι → α) → β)
    (i : ι) (branch : α → QueryTree ι α β) :
    (∑' y, (μ i y).toReal * (elimFirst i branch y).distributionalError (PMF.pi μ) f) ≤
      (QueryTree.node i branch).distributionalError (PMF.pi μ) f + coordInfluence μ f i := by
  let _ := Fintype.ofFinite α
  set t := QueryTree.node i branch
  set Q : PMF ((ι → α) × (ι → α)) :=
    (μ i).bind fun y ↦ (PMF.pi μ).map fun x ↦ (x, Function.update x i y)
  have havg : (∑' y, (μ i y).toReal * (elimFirst i branch y).distributionalError (PMF.pi μ) f) =
      (Q.toOuterMeasure {p | t.eval p.2 ≠ f p.1}).toReal := by
    rw [tsum_fintype, PMF.toOuterMeasure_bind_toReal]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    congr 1
    rw [QueryTree.distributionalError_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_elimFirst, t]
  have hsub : {p : (ι → α) × (ι → α) | t.eval p.2 ≠ f p.1} ⊆
      {p | t.eval p.2 ≠ f p.2} ∪ {p | f p.2 ≠ f p.1} := by
    intro p hp
    by_cases h : t.eval p.2 = f p.2
    · exact Or.inr fun heq ↦ hp (h.trans heq)
    · exact Or.inl h
  have hunion : (Q.toOuterMeasure {p | t.eval p.2 ≠ f p.1}).toReal ≤
      (Q.toOuterMeasure {p | t.eval p.2 ≠ f p.2}).toReal +
        (Q.toOuterMeasure {p | f p.2 ≠ f p.1}).toReal :=
    ENNReal.toReal_le_add
      ((MeasureTheory.measure_mono (μ := Q.toOuterMeasure) hsub).trans
        (MeasureTheory.measure_union_le _ _))
      (PMF.toOuterMeasure_ne_top _ _) (PMF.toOuterMeasure_ne_top _ _)
  have hmar : Q.map Prod.snd = PMF.pi μ := by
    simp only [Q, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact bind_pi_update_self μ i
  have hfirst : (Q.toOuterMeasure {p | t.eval p.2 ≠ f p.2}).toReal =
      t.distributionalError (PMF.pi μ) f := by
    rw [QueryTree.distributionalError_eq_toOuterMeasure, ← hmar, PMF.toOuterMeasure_map_apply]
    rfl
  rw [havg, ← hfirst, coordInfluence_eq_bind_swap μ f i]
  exact hunion

/-- Deterministic one-step query elimination: reduces worst-case depth from `k + 1` to `k` while
increasing distributional error under `PMF.pi μ` by at most `maxCoordInfluence μ f`. -/
theorem exists_query_elimination_step (μ : ι → PMF α) (f : (ι → α) → β)
    (t : QueryTree ι α β) {k : ℕ} (hk : t.depth ≤ k + 1) :
    ∃ t' : QueryTree ι α β, t'.depth ≤ k ∧
      t'.distributionalError (PMF.pi μ) f ≤
        t.distributionalError (PMF.pi μ) f + maxCoordInfluence μ f := by
  cases t with
  | leaf b =>
    refine ⟨QueryTree.leaf b, by simp, ?_⟩
    linarith [maxCoordInfluence_nonneg μ f]
  | node i branch =>
    let _ := Fintype.ofFinite α
    set err : α → ℝ := fun y ↦ (elimFirst i branch y).distributionalError (PMF.pi μ) f
    have herr_nonneg : ∀ z, 0 ≤ err z := fun z ↦ QueryTree.distributionalError_nonneg _ _ _
    obtain ⟨y, _, hy⟩ := PMF.exists_mem_support_le_tsum_mul (μ i) (fun y ↦ ENNReal.ofReal (err y))
    have hyreal : err y ≤ ∑' z, (μ i z).toReal * err z := by
      have hne : ∀ z, μ i z * ENNReal.ofReal (err z) ≠ ⊤ := fun z ↦
        ENNReal.mul_ne_top (PMF.apply_ne_top _ z) ENNReal.ofReal_ne_top
      have htsum_ne : (∑' z, μ i z * ENNReal.ofReal (err z)) ≠ ⊤ := by
        rw [tsum_fintype]
        exact ENNReal.sum_ne_top.mpr fun z _ ↦ hne z
      have hle := ENNReal.toReal_mono htsum_ne hy
      rw [ENNReal.toReal_ofReal (herr_nonneg y), ENNReal.tsum_toReal_eq hne] at hle
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (herr_nonneg _)] using hle
    refine ⟨elimFirst i branch y, depth_elimFirst_le hk y, ?_⟩
    calc err y ≤ ∑' z, (μ i z).toReal * err z := hyreal
      _ ≤ (QueryTree.node i branch).distributionalError (PMF.pi μ) f + coordInfluence μ f i :=
          average_distributionalError_elimFirst_le μ f i branch
      _ ≤ (QueryTree.node i branch).distributionalError (PMF.pi μ) f + maxCoordInfluence μ f :=
          add_le_add le_rfl (coordInfluence_le_maxCoordInfluence μ f i)

private theorem average_expectedCost_elimFirst_add_one_le (μ : ι → PMF α)
    (i : ι) (branch : α → QueryTree ι α β) :
    (∑' y, (μ i y).toReal * (elimFirst i branch y).distributionalExpectedCost (PMF.pi μ)) + 1 ≤
      (QueryTree.node i branch).distributionalExpectedCost (PMF.pi μ) := by
  let _ := Fintype.ofFinite α
  set t := QueryTree.node i branch
  rw [tsum_fintype, QueryTree.distributionalExpectedCost_eq_sum]
  rw [PMF.sum_pi_mul_update μ i (fun x ↦ (t.cost x : ℝ))]
  have h1 : (1 : ℝ) = ∑ y : α, (μ i y).toReal * 1 := by simp only [mul_one, PMF.sum_toReal]
  calc (∑ y : α, (μ i y).toReal * (elimFirst i branch y).distributionalExpectedCost (PMF.pi μ)) + 1
      = ∑ y : α, (μ i y).toReal *
          ((elimFirst i branch y).distributionalExpectedCost (PMF.pi μ) + 1) := by
          conv_lhs => rw [h1]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun y _ ↦ by ring
    _ ≤ ∑ y : α, (μ i y).toReal *
          ∑ x : ι → α, (PMF.pi μ x).toReal * (t.cost (Function.update x i y) : ℝ) := by
          refine Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rw [QueryTree.distributionalExpectedCost_eq_sum]
          have hx1 : (1 : ℝ) = ∑ x : ι → α, (PMF.pi μ x).toReal * 1 := by
            simp only [mul_one, PMF.sum_toReal]
          conv_lhs => rw [hx1]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun x _ ↦ ?_
          rw [← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          exact_mod_cast cost_elimFirst_add_one_le i branch y x
    _ = ∑ x : ι → α, (PMF.pi μ x).toReal *
          ∑ y : α, (μ i y).toReal * (t.cost (Function.update x i y) : ℝ) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ ↦
            Finset.sum_congr rfl fun y _ ↦ mul_left_comm _ _ _

/-- Expected-query influence lower bound for arbitrary deterministic query trees. -/
theorem one_sub_maxOutputProb_le_distributionalError_add_expectedCost
    (μ : ι → PMF α) (f : (ι → α) → β) (t : QueryTree ι α β) :
    1 - maxOutputProb (PMF.pi μ) f ≤
      t.distributionalError (PMF.pi μ) f +
        t.distributionalExpectedCost (PMF.pi μ) * maxCoordInfluence μ f := by
  let _ := Fintype.ofFinite α
  suffices ∀ d (t : QueryTree ι α β), t.depth ≤ d →
      1 - maxOutputProb (PMF.pi μ) f ≤
        t.distributionalError (PMF.pi μ) f +
          t.distributionalExpectedCost (PMF.pi μ) * maxCoordInfluence μ f from
    this t.depth t le_rfl
  intro d
  induction d with
  | zero =>
    intro t ht
    obtain ⟨b, rfl⟩ := (QueryTree.depth_eq_zero_iff t).mp (Nat.le_zero.mp ht)
    rw [QueryTree.distributionalError_leaf, QueryTree.distributionalExpectedCost_leaf, zero_mul,
      add_zero]
    linarith [prob_eq_le_maxOutputProb (PMF.pi μ) f b]
  | succ d ih =>
    intro t ht
    cases t with
    | leaf b =>
      rw [QueryTree.distributionalError_leaf, QueryTree.distributionalExpectedCost_leaf, zero_mul,
        add_zero]
      linarith [prob_eq_le_maxOutputProb (PMF.pi μ) f b]
    | node i branch =>
      have hpt (y : α) := ih (elimFirst i branch y) (depth_elimFirst_le ht y)
      have havg_bound :
          1 - maxOutputProb (PMF.pi μ) f ≤
            (∑' y, (μ i y).toReal * (elimFirst i branch y).distributionalError (PMF.pi μ) f) +
              (∑' y, (μ i y).toReal *
                (elimFirst i branch y).distributionalExpectedCost (PMF.pi μ)) *
                maxCoordInfluence μ f := by
        simp only [tsum_fintype]
        calc 1 - maxOutputProb (PMF.pi μ) f
            = ∑ y : α, (μ i y).toReal * (1 - maxOutputProb (PMF.pi μ) f) := by
              rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
          _ ≤ ∑ y : α, (μ i y).toReal *
                ((elimFirst i branch y).distributionalError (PMF.pi μ) f +
                  (elimFirst i branch y).distributionalExpectedCost (PMF.pi μ) *
                    maxCoordInfluence μ f) :=
              Finset.sum_le_sum fun y _ ↦
                mul_le_mul_of_nonneg_left (hpt y) ENNReal.toReal_nonneg
          _ = _ := by
              simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
      have herr := (average_distributionalError_elimFirst_le μ f i branch).trans
        (add_le_add le_rfl (coordInfluence_le_maxCoordInfluence μ f i))
      have hcost := average_expectedCost_elimFirst_add_one_le μ i branch
      have hinf := maxCoordInfluence_nonneg μ f
      nlinarith

/-- Multiplicative distributional influence lower bound for independent coordinate distributions.
-/
theorem one_sub_maxOutputProb_sub_le_distributionalComplexity_mul_maxCoordInfluence
    (μ : ι → PMF α) (f : (ι → α) → β) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - maxOutputProb (PMF.pi μ) f - ε ≤
      (distributionalComplexity ε (PMF.pi μ) f : ℝ) * maxCoordInfluence μ f := by
  let _ := Fintype.ofFinite α
  obtain ⟨t, ht_err, ht_depth⟩ :=
    exists_distributionalError_le_depth_eq_distributionalComplexity hε (PMF.pi μ) f
  have h1 := one_sub_maxOutputProb_le_distributionalError_add_expectedCost μ f t
  have h2 : t.distributionalExpectedCost (PMF.pi μ) ≤ t.depth := by
    rw [QueryTree.distributionalExpectedCost_eq_sum]
    exact PMF.sum_mul_le _ _ _ fun x ↦ Nat.cast_le.mpr (t.cost_le_depth x)
  have hinf := maxCoordInfluence_nonneg μ f
  rw [← ht_depth]
  nlinarith

/-- Distributional query complexity lower bound via maximum coordinate influence. -/
theorem distributionalComplexity_ge_div_maxCoordInfluence
    (μ : ι → PMF α) (f : (ι → α) → β) {ε : ℝ} (hε : 0 ≤ ε)
    (hinf : 0 < maxCoordInfluence μ f) :
    (1 - maxOutputProb (PMF.pi μ) f - ε) / maxCoordInfluence μ f ≤
      (distributionalComplexity ε (PMF.pi μ) f : ℝ) :=
  (div_le_iff₀ hinf).mpr
    (one_sub_maxOutputProb_sub_le_distributionalComplexity_mul_maxCoordInfluence μ f hε)

/-- Smoothed distributional influence lower bound via any `δ`-close approximating function `g`. -/
theorem smoothed_div_coord (μ : ι → PMF α) (f g : (ι → α) → β) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hfg : ((PMF.pi μ).toOuterMeasure {x | f x ≠ g x}).toReal ≤ δ)
    (hinf : 0 < maxCoordInfluence μ g) :
    (1 - maxOutputProb (PMF.pi μ) g - ε - δ) / maxCoordInfluence μ g ≤
        (distributionalComplexity (ε + δ) (PMF.pi μ) g : ℝ) ∧
      (distributionalComplexity (ε + δ) (PMF.pi μ) g : ℝ) ≤
        (distributionalComplexity ε (PMF.pi μ) f : ℝ) := by
  refine ⟨?_, Nat.cast_le.mpr ?_⟩
  · have h := distributionalComplexity_ge_div_maxCoordInfluence μ g (add_nonneg hε hδ) hinf
    simpa only [sub_add_eq_sub_sub] using h
  · obtain ⟨t, ht_err, ht_depth⟩ :=
      exists_distributionalError_le_depth_eq_distributionalComplexity hε (PMF.pi μ) f
    have hsub : {x : ι → α | t.eval x ≠ g x} ⊆ {x | t.eval x ≠ f x} ∪ {x | f x ≠ g x} := by
      intro x hx
      by_cases h : t.eval x = f x
      · exact Or.inr fun heq ↦ hx (h.trans heq)
      · exact Or.inl h
    have htri : t.distributionalError (PMF.pi μ) g ≤
        t.distributionalError (PMF.pi μ) f +
          ((PMF.pi μ).toOuterMeasure {x | f x ≠ g x}).toReal :=
      ENNReal.toReal_le_add
        ((MeasureTheory.measure_mono (μ := (PMF.pi μ).toOuterMeasure) hsub).trans
          (MeasureTheory.measure_union_le _ _))
        (PMF.toOuterMeasure_ne_top _ _) (PMF.toOuterMeasure_ne_top _ _)
    exact (distributionalComplexity_le_depth (htri.trans (add_le_add ht_err hfg))).trans_eq
      ht_depth

end QueryElimination

/-! ### Boolean variance, Markov truncation, and randomized lower bounds -/

section BooleanApplications

/-- Expected value of `signVal ∘ f` under a discrete distribution `ν` on `ι → Bool`. -/
noncomputable def boolMean {ι : Type*} (ν : PMF (ι → Bool)) (f : (ι → Bool) → Bool) : ℝ :=
  ∑' x, (ν x).toReal * BitString.signVal (f x)

/-- Variance of `signVal ∘ f` (`{-1, +1}`-valued) under a discrete distribution `ν`. -/
noncomputable def boolVariance {ι : Type*} (ν : PMF (ι → Bool)) (f : (ι → Bool) → Bool) : ℝ :=
  ∑' x, (ν x).toReal * (BitString.signVal (f x) - boolMean ν f) ^ 2

private theorem prob_bool_false_add_true {ι : Type*} (ν : PMF (ι → Bool))
    (f : (ι → Bool) → Bool) :
    (ν.toOuterMeasure {x | f x = false}).toReal +
      (ν.toOuterMeasure {x | f x = true}).toReal = 1 := by
  have hcompl : {x : ι → Bool | f x = true} = ({x : ι → Bool | f x = false})ᶜ := by
    ext x; cases f x <;> simp
  simpa only [hcompl] using
    PMF.toOuterMeasure_toReal_add_compl ν {x : ι → Bool | f x = false}

/-- `boolVariance ν f = 4 * Pr[f(X) = false] * Pr[f(X) = true]`. -/
theorem boolVariance_eq_four_mul {ι : Type*} [Finite ι] (ν : PMF (ι → Bool))
    (f : (ι → Bool) → Bool) :
    boolVariance ν f =
      4 * (ν.toOuterMeasure {x | f x = false}).toReal *
        (ν.toOuterMeasure {x | f x = true}).toReal := by
  let _ := Fintype.ofFinite (ι → Bool)
  have hsum := prob_bool_false_add_true ν f
  have hmean : boolMean ν f =
      (ν.toOuterMeasure {x | f x = false}).toReal -
        (ν.toOuterMeasure {x | f x = true}).toReal := by
    rw [boolMean, tsum_fintype, PMF.toOuterMeasure_apply_toReal, PMF.toOuterMeasure_apply_toReal,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [Set.mem_ofPred_eq]
    rcases Bool.eq_false_or_eq_true (f x) with hx | hx <;> simp [hx, BitString.signVal]
  have hvar : boolVariance ν f = 1 - (boolMean ν f) ^ 2 := by
    rw [boolVariance, tsum_fintype]
    have hsplit : ∀ x, (ν x).toReal * (BitString.signVal (f x) - boolMean ν f) ^ 2 =
        (ν x).toReal - 2 * boolMean ν f * ((ν x).toReal * BitString.signVal (f x)) +
          (boolMean ν f) ^ 2 * (ν x).toReal := by
      intro x
      have hsq : BitString.signVal (f x) ^ 2 = 1 := by cases f x <;> simp [BitString.signVal]
      linear_combination (ν x).toReal * hsq
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      PMF.sum_toReal]
    have hmean_sum : ∑ x : ι → Bool, (ν x).toReal * BitString.signVal (f x) = boolMean ν f :=
      (tsum_fintype _).symm
    rw [hmean_sum]
    ring
  rw [hvar, hmean]
  nlinarith [hsum]

/-- Truncate a Boolean decision tree at depth `d`, replacing deeper nodes with `default`. -/
def truncate {ι β : Type*} (d : ℕ) (default : β) : DecisionTree ι β → DecisionTree ι β
  | DecisionTree.leaf b => DecisionTree.leaf b
  | DecisionTree.node i t₀ t₁ =>
    match d with
    | 0 => DecisionTree.leaf default
    | d + 1 => DecisionTree.node i (truncate d default t₀) (truncate d default t₁)

private theorem depth_truncate_le {ι β : Type*} (d : ℕ) (default : β) (t : DecisionTree ι β) :
    (truncate d default t).depth ≤ d := by
  induction t generalizing d with
  | leaf b => simp [truncate]
  | node i t₀ t₁ ih₀ ih₁ =>
    cases d with
    | zero => simp [truncate]
    | succ d =>
      simp only [truncate, DecisionTree.depth_node]
      exact Nat.add_le_add_right (max_le (ih₀ d) (ih₁ d)) 1

private theorem eval_truncate_of_cost_le {ι β : Type*} (d : ℕ) (default : β)
    (t : DecisionTree ι β) {x : ι → Bool} (hx : t.cost x ≤ d) :
    (truncate d default t).eval x = t.eval x := by
  induction t generalizing d with
  | leaf b => simp [truncate]
  | node i t₀ t₁ ih₀ ih₁ =>
    cases d with
    | zero => simp [DecisionTree.cost_node] at hx
    | succ d =>
      simp only [truncate, DecisionTree.eval_node]
      simp only [DecisionTree.cost_node] at hx
      cases hxi : x i
      · simp only [hxi, Bool.cond_false] at hx ⊢
        exact ih₀ d (by omega)
      · simp only [hxi, Bool.cond_true] at hx ⊢
        exact ih₁ d (by omega)

/-- Markov truncation: for every `ε > 0`, `ε * R_ε(f) ≤ R_0(f)`. -/
theorem mul_randomizedComplexity_le_zeroErrorComplexity {ι β : Type*} [Finite ι]
    (f : (ι → Bool) → β) {ε : ℝ≥0} (hε : 0 < (ε : ℝ)) :
    (ε : ℝ) * (Cslib.QueryComplexity.randomizedComplexity ε f : ℝ) ≤
      Cslib.QueryComplexity.zeroErrorComplexity f := by
  classical
  refine Cslib.QueryComplexity.le_zeroErrorComplexity fun μ c hμ hc ↦ ?_
  have hc0 : 0 ≤ c :=
    RandomizedDecisionTree.expectedCost_nonneg.trans (hc fun _ ↦ false)
  set d : ℕ := Nat.floor (c / (ε : ℝ))
  set b₀ : β := f fun _ ↦ false
  set μ' : RandomizedDecisionTree ι β := μ.mapTree (truncate d b₀)
  have hdepth : μ'.depth ≤ d := by
    rw [RandomizedDecisionTree.depth_le_iff]
    intro u hu
    obtain ⟨t, _, rfl⟩ := RandomizedDecisionTree.exists_of_mem_support_mapTree hu
    exact depth_truncate_le d b₀ t
  have hcomp : μ'.Computes (ε : ℝ) f := by
    intro x
    have hmarkov : μ'.errorProb f x * ((d + 1 : ℕ) : ℝ) ≤ μ.expectedCost x := by
      rw [RandomizedDecisionTree.errorProb_eq_sum, RandomizedDecisionTree.expectedCost_eq_sum,
        show μ' = Convexity.StdSimplex.map (truncate d b₀) μ from rfl,
        Convexity.StdSimplex.weights_map,
        Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _,
        Finsupp.sum, Finsupp.sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun t ht ↦ ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (μ.weights_nonneg t)
      have htf : t.Computes f := RandomizedDecisionTree.computes_zero_iff.mp hμ t ht
      by_cases heq : (truncate d b₀ t).eval x = f x
      · simp [heq]
      · simp only [heq, ↓reduceIte, one_mul]
        have hgt : d < t.cost x := by
          by_contra hle
          exact heq ((eval_truncate_of_cost_le d b₀ t (not_lt.mp hle)).trans (htf x))
        exact_mod_cast Nat.succ_le_of_lt hgt
    have hdpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
    have hfloor : c / (ε : ℝ) < ((d + 1 : ℕ) : ℝ) := by
      push_cast [d]
      exact Nat.lt_floor_add_one (c / (ε : ℝ))
    have hc_le : c ≤ (ε : ℝ) * ((d + 1 : ℕ) : ℝ) := by
      have := (div_lt_iff₀ hε).mp hfloor
      linarith
    exact le_of_mul_le_mul_right (hmarkov.trans ((hc x).trans hc_le)) hdpos
  have hr : (Cslib.QueryComplexity.randomizedComplexity ε f : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Cslib.QueryComplexity.randomizedComplexity_le_depth hcomp).trans hdepth
  have hd_le : (d : ℝ) ≤ c / (ε : ℝ) := Nat.floor_le (div_nonneg hc0 hε.le)
  have hmul := mul_le_mul_of_nonneg_left (hr.trans hd_le) hε.le
  rwa [mul_div_cancel₀ _ hε.ne'] at hmul

/-- Bounded-error randomized query complexity lower bound via maximum coordinate influence. -/
theorem randomizedComplexity_ge_div_maxCoordInfluence {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → PMF Bool) (f : (ι → Bool) → β) (ε : ℝ≥0)
    (hinf : 0 < maxCoordInfluence μ f) :
    (1 - maxOutputProb (PMF.pi μ) f - (ε : ℝ)) / maxCoordInfluence μ f ≤
      (Cslib.QueryComplexity.randomizedComplexity ε f : ℝ) := by
  have h1 := distributionalComplexity_ge_div_maxCoordInfluence μ f ε.coe_nonneg hinf
  have h2 : distributionalComplexity (ε : ℝ) (PMF.pi μ) f ≤
      Cslib.QueryComplexity.randomizedComplexity ε f := by
    rw [distributionalComplexity_eq_cslib]
    exact Cslib.QueryComplexity.distributionalComplexity_le_randomizedComplexity ε
      (PMF.toStdSimplex (PMF.pi μ)) f
  exact h1.trans (Nat.cast_le.mpr h2)

/-- Zero-error randomized query complexity lower bound for Boolean functions under independent
biased coordinate distributions: `Var[f] / (4 * maxCoordInfluence μ f) ≤ R_0(f)`. -/
theorem zeroErrorComplexity_ge_variance_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → I) (f : (ι → Bool) → Bool)
    (hinf : 0 < maxCoordInfluence (fun i ↦ PMF.coin (p i)) f) :
    boolVariance (PMF.pi fun i ↦ PMF.coin (p i)) f /
        (4 * maxCoordInfluence (fun i ↦ PMF.coin (p i)) f) ≤
      Cslib.QueryComplexity.zeroErrorComplexity f := by
  set μ : ι → PMF Bool := fun i ↦ PMF.coin (p i)
  set P : PMF (ι → Bool) := PMF.pi μ
  obtain ⟨t, ht_comp, ht_cost⟩ :=
    Cslib.QueryComplexity.exists_computes_distributionalCost_eq (PMF.toStdSimplex P) f
  have hcost_le : t.distributionalCost (PMF.toStdSimplex P) ≤
      Cslib.QueryComplexity.zeroErrorComplexity f :=
    ht_cost.trans_le
      (Cslib.QueryComplexity.distributionalExpectedComplexity_le_zeroErrorComplexity _ f)
  have hq_err : (QueryTree.ofDecisionTree t).distributionalError P f = 0 :=
    QueryTree.distributionalError_eq_zero_of_exact
      (fun x ↦ by rw [QueryTree.eval_ofDecisionTree]; exact ht_comp x) P
  have hq_cost : (QueryTree.ofDecisionTree t).distributionalExpectedCost P =
      t.distributionalCost (PMF.toStdSimplex P) := by
    have h := QueryTree.distributionalExpectedCost_toDecisionTree (QueryTree.ofDecisionTree t) P
    rw [QueryTree.toDecisionTree_ofDecisionTree] at h
    exact h.symm
  have helim := one_sub_maxOutputProb_le_distributionalError_add_expectedCost μ f
    (QueryTree.ofDecisionTree t)
  rw [hq_err, zero_add, hq_cost] at helim
  have hvar : (1 / 4 : ℝ) * boolVariance P f ≤ 1 - maxOutputProb P f := by
    rw [boolVariance_eq_four_mul, maxOutputProb_bool]
    have hsum := prob_bool_false_add_true P f
    have hp₀ : 0 ≤ (P.toOuterMeasure {x | f x = false}).toReal := ENNReal.toReal_nonneg
    have hp₁ : 0 ≤ (P.toOuterMeasure {x | f x = true}).toReal := ENNReal.toReal_nonneg
    rcases le_total (P.toOuterMeasure {x | f x = false}).toReal
        (P.toOuterMeasure {x | f x = true}).toReal with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end BooleanApplications

end CslibFrontier.QueryComplexity
