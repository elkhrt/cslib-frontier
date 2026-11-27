/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Cost
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# General-Alphabet Decision Trees, Randomized Query Models, and Promise Relational Adversaries

This module develops deterministic, randomized, and nonadaptive query algorithms over arbitrary
query index types `I`, answer alphabets `A`, and output types `O`, connects the Boolean-alphabet
case `A = Bool` to `Cslib.DecisionTree`, and proves Aaronson's classical relational adversary lower
bound for promise functions.

## Main definitions

* `CslibFrontier.QueryComplexity.DTree`: deterministic adaptive decision trees querying oracles
  `I → A` and returning outputs in `O`, with `eval`, `cost`, `depth`, `bind`, `queriedSet`,
  `queryList`, and `equivCslib : DTree I Bool O ≃ Cslib.DecisionTree I O`.
* `CslibFrontier.QueryComplexity.RandDTree`: finite-support randomized decision trees with
  `ofDTree`, `expectedCost`, `HasQueryBoundOn`, `errorProb`, and `successProb`.
* `CslibFrontier.QueryComplexity.NonadaptiveAlg`: deterministic nonadaptive (parallel) query
  algorithms with `eval`, `queryCount`, and `toDTree`.
* `CslibFrontier.QueryComplexity.relRowWeight`, `CslibFrontier.QueryComplexity.relTotalWeight`,
  `CslibFrontier.QueryComplexity.relDisagreeWeight`, `CslibFrontier.QueryComplexity.relRatio`:
  row weight, total weight, coordinate disagreement weight, and adversary ratio for a relational
  adversary matrix on a finite promise family.

## Main results

* `CslibFrontier.QueryComplexity.DTree.eval_equivCslib`,
  `CslibFrontier.QueryComplexity.DTree.cost_equivCslib`,
  `CslibFrontier.QueryComplexity.DTree.depth_equivCslib`,
  `CslibFrontier.QueryComplexity.DTree.queries_equivCslib`: exact agreement with
  `Cslib.DecisionTree` for Boolean oracles.
* `CslibFrontier.QueryComplexity.DTree.exists_mem_queriedSet_inter_of_eval_ne`: mutual query
  separation for deterministic decision trees producing distinct outputs.
* `CslibFrontier.QueryComplexity.DTree.relAdversary_sum_cost_ge`,
  `CslibFrontier.QueryComplexity.relAdversary_cslib_sum_cost_ge`: deterministic relational
  adversary lower bound for general-alphabet `DTree` and Boolean `Cslib.DecisionTree`.
* `CslibFrontier.QueryComplexity.RandDTree.relAdversary_expectedCost_ge`,
  `CslibFrontier.QueryComplexity.RandDTree.exists_relAdversary_expectedCost_ge`,
  `CslibFrontier.QueryComplexity.RandDTree.relAdversary_queryBound_ge`: Aaronson's randomized
  relational adversary lower bound for promise functions.
-/

public section

namespace CslibFrontier.QueryComplexity

section DTree

variable {I A O O' : Type*}

/-- Deterministic adaptive decision tree querying an oracle `I → A` and returning an output in
`O`. -/
inductive DTree (I A O : Type*) where
  /-- Leaf returning a final output value without further oracle queries. -/
  | leaf (out : O) : DTree I A O
  /-- Internal node querying index `idx` and branching on the oracle answer in `A`. -/
  | node (idx : I) (branch : A → DTree I A O) : DTree I A O

namespace DTree

/-- Default decision tree returning `default` immediately when `O` is inhabited. -/
instance instInhabited [Inhabited O] : Inhabited (DTree I A O) :=
  ⟨.leaf default⟩

/-- Evaluates a deterministic decision tree `T` on an input oracle `x : I → A`. -/
def eval : DTree I A O → (I → A) → O
  | .leaf o, _ => o
  | .node i k, x => (k (x i)).eval x

@[simp]
theorem eval_leaf (o : O) (x : I → A) : (leaf o : DTree I A O).eval x = o := by
  rfl

@[simp]
theorem eval_node (i : I) (k : A → DTree I A O) (x : I → A) :
    (node i k).eval x = (k (x i)).eval x := by
  rfl

/-- Number of oracle queries executed along the path followed by `T` on oracle `x`. -/
def cost : DTree I A O → (I → A) → ℕ
  | .leaf _, _ => 0
  | .node i k, x => 1 + (k (x i)).cost x

@[simp]
theorem cost_leaf (o : O) (x : I → A) : (leaf o : DTree I A O).cost x = 0 := by
  rfl

@[simp]
theorem cost_node (i : I) (k : A → DTree I A O) (x : I → A) :
    (node i k).cost x = 1 + (k (x i)).cost x := by
  rfl

/-- Worst-case structural depth of a decision tree over a finite answer alphabet `A`. -/
def depth [Fintype A] : DTree I A O → ℕ
  | .leaf _ => 0
  | .node _ k => 1 + Finset.univ.sup fun a ↦ (k a).depth

@[simp]
theorem depth_leaf [Fintype A] (o : O) : (leaf o : DTree I A O).depth = 0 := by
  rfl

@[simp]
theorem depth_node [Fintype A] (i : I) (k : A → DTree I A O) :
    (node i k).depth = 1 + Finset.univ.sup fun a ↦ (k a).depth := by
  rfl

/-- The path query cost of `T` on any input is at most `T.depth`. -/
theorem cost_le_depth [Fintype A] (T : DTree I A O) (x : I → A) :
    T.cost x ≤ T.depth := by
  induction T with
  | leaf _ => simp
  | node i k ih =>
    rw [cost_node, depth_node]
    exact Nat.add_le_add_left
      ((ih (x i)).trans (Finset.le_sup (f := fun a ↦ (k a).depth) (Finset.mem_univ (x i)))) 1

/-- Sequential (monadic) composition of deterministic decision trees. -/
def bind : DTree I A O → (O → DTree I A O') → DTree I A O'
  | .leaf o, k => k o
  | .node i br, k => .node i fun a ↦ (br a).bind k

@[simp]
theorem bind_leaf (o : O) (k : O → DTree I A O') :
    (leaf o : DTree I A O).bind k = k o := by
  rfl

@[simp]
theorem bind_node (i : I) (br : A → DTree I A O) (k : O → DTree I A O') :
    (node i br).bind k = .node i fun a ↦ (br a).bind k := by
  rfl

@[simp]
theorem eval_bind (T : DTree I A O) (k : O → DTree I A O') (x : I → A) :
    (T.bind k).eval x = (k (T.eval x)).eval x := by
  induction T with
  | leaf _ => rfl
  | node i _ ih => exact ih (x i)

@[simp]
theorem cost_bind (T : DTree I A O) (k : O → DTree I A O') (x : I → A) :
    (T.bind k).cost x = T.cost x + (k (T.eval x)).cost x := by
  induction T with
  | leaf _ => simp
  | node i _ ih => simp only [bind_node, cost_node, eval_node, ih (x i), Nat.add_assoc]

/-- Finite set of query indices visited by `T` along the path followed on oracle `x`. -/
def queriedSet [DecidableEq I] : DTree I A O → (I → A) → Finset I
  | .leaf _, _ => ∅
  | .node i k, x => insert i ((k (x i)).queriedSet x)

@[simp]
theorem queriedSet_leaf [DecidableEq I] (o : O) (x : I → A) :
    (leaf o : DTree I A O).queriedSet x = ∅ := by
  rfl

@[simp]
theorem queriedSet_node [DecidableEq I] (i : I) (k : A → DTree I A O) (x : I → A) :
    (node i k).queriedSet x = insert i ((k (x i)).queriedSet x) := by
  rfl

/-- The number of distinct queried indices is at most the path query cost. -/
theorem card_queriedSet_le_cost [DecidableEq I] (T : DTree I A O) (x : I → A) :
    (T.queriedSet x).card ≤ T.cost x := by
  induction T with
  | leaf _ => simp
  | node i k ih =>
    rw [queriedSet_node, cost_node]
    have hcard := Finset.card_insert_le i ((k (x i)).queriedSet x)
    have hsub := ih (x i)
    omega

/-- Mutual query separation: if `T.eval x ≠ T.eval y`, some index queried on both `x` and `y`
separates `x` and `y`. -/
theorem exists_mem_queriedSet_inter_of_eval_ne [DecidableEq I] (T : DTree I A O)
    {x y : I → A} (hne : T.eval x ≠ T.eval y) :
    ∃ i ∈ T.queriedSet x ∩ T.queriedSet y, x i ≠ y i := by
  induction T with
  | leaf _ => exact False.elim (hne rfl)
  | node i k ih =>
    by_cases hi : x i = y i
    · rw [eval_node, eval_node, ← hi] at hne
      obtain ⟨j, hj, hxy⟩ := ih (x i) hne
      rw [Finset.mem_inter] at hj
      refine ⟨j, Finset.mem_inter.mpr ⟨?_, ?_⟩, hxy⟩
      · rw [queriedSet_node]; exact Finset.mem_insert_of_mem hj.1
      · rw [queriedSet_node, ← hi]; exact Finset.mem_insert_of_mem hj.2
    · exact ⟨i, Finset.mem_inter.mpr
        ⟨Finset.mem_insert_self i _, Finset.mem_insert_self i _⟩, hi⟩

/-- Converts a Boolean-alphabet `DTree I Bool O` to `Cslib.DecisionTree I O`. -/
def toCslib : DTree I Bool O → Cslib.DecisionTree I O
  | .leaf o => .leaf o
  | .node i k => .node i (k false).toCslib (k true).toCslib

/-- Converts a `Cslib.DecisionTree I O` to `DTree I Bool O`. -/
def ofCslib : Cslib.DecisionTree I O → DTree I Bool O
  | .leaf o => .leaf o
  | .node i t₀ t₁ => .node i fun b ↦ cond b (ofCslib t₁) (ofCslib t₀)

/-- Canonical equivalence `DTree I Bool O ≃ Cslib.DecisionTree I O`. -/
def equivCslib : DTree I Bool O ≃ Cslib.DecisionTree I O where
  toFun := toCslib
  invFun := ofCslib
  left_inv T := by
    induction T with
    | leaf _ => rfl
    | node _ _ ih =>
      simp only [toCslib, ofCslib]
      congr 1; ext b; cases b <;> simp [ih]
  right_inv t := by
    induction t with
    | leaf _ => rfl
    | node _ _ _ ih₀ ih₁ => simp [ofCslib, toCslib, ih₀, ih₁]

@[simp]
theorem eval_equivCslib (T : DTree I Bool O) (x : I → Bool) :
    (equivCslib T).eval x = T.eval x := by
  induction T with
  | leaf _ => rfl
  | node i k ih =>
    change (Cslib.DecisionTree.node i (equivCslib (k false)) (equivCslib (k true))).eval x =
      (k (x i)).eval x
    rw [Cslib.DecisionTree.eval_node]
    cases h : x i <;> simp [ih]

@[simp]
theorem cost_equivCslib (T : DTree I Bool O) (x : I → Bool) :
    (equivCslib T).cost x = T.cost x := by
  induction T with
  | leaf _ => rfl
  | node i k ih =>
    change (Cslib.DecisionTree.node i (equivCslib (k false)) (equivCslib (k true))).cost x =
      1 + (k (x i)).cost x
    rw [Cslib.DecisionTree.cost_node]
    cases h : x i <;> simp [ih, Nat.add_comm]

@[simp]
theorem depth_equivCslib (T : DTree I Bool O) :
    (equivCslib T).depth = T.depth := by
  induction T with
  | leaf _ => rfl
  | node i k ih =>
    change (Cslib.DecisionTree.node i (equivCslib (k false)) (equivCslib (k true))).depth =
      1 + Finset.univ.sup fun b : Bool ↦ (k b).depth
    rw [Cslib.DecisionTree.depth_node, ih false, ih true]
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv]
    simp [Nat.add_comm]

@[simp]
theorem queries_equivCslib [DecidableEq I] (T : DTree I Bool O) (x : I → Bool) :
    (equivCslib T).queries x = T.queriedSet x := by
  induction T with
  | leaf _ => rfl
  | node i k ih =>
    change (Cslib.DecisionTree.node i (equivCslib (k false)) (equivCslib (k true))).queries x =
      insert i ((k (x i)).queriedSet x)
    rw [Cslib.DecisionTree.queries_node]
    cases h : x i <;> simp [ih]

end DTree

end DTree

section RandAndNonadaptive

/-- Finite-support randomized decision tree represented as a probability distribution over finitely
many deterministic decision trees. -/
@[ext]
structure RandDTree (I A O : Type*) where
  /-- Number of random seeds in the support. -/
  numSeeds : ℕ
  /-- Probability weight of each seed. -/
  weights : Fin numSeeds → ℝ
  /-- Non-negativity of all seed weights. -/
  weights_nonneg : ∀ s, 0 ≤ weights s
  /-- Normalization of the seed weights. -/
  sum_weights : ∑ s, weights s = 1
  /-- Deterministic decision tree executed for each seed. -/
  tree : Fin numSeeds → DTree I A O

namespace RandDTree

variable {I A O : Type*}

/-- Embeds a deterministic decision tree as a single-seed randomized decision tree. -/
def ofDTree (T : DTree I A O) : RandDTree I A O where
  numSeeds := 1
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  sum_weights := by simp
  tree := fun _ ↦ T

/-- Expected query cost of `R` on oracle `x`. -/
def expectedCost (R : RandDTree I A O) (x : I → A) : ℝ :=
  ∑ s, R.weights s * ((R.tree s).cost x : ℝ)

/-- Every seed tree of `R` makes at most `q` queries on every input satisfying `P`. -/
def HasQueryBoundOn (R : RandDTree I A O) (P : (I → A) → Prop) (q : ℕ) : Prop :=
  ∀ s x, P x → (R.tree s).cost x ≤ q

/-- A uniform seed query bound `q` on `P` bounds the expected cost on `P` by `q`. -/
theorem expectedCost_le_of_hasQueryBoundOn {R : RandDTree I A O} {P : (I → A) → Prop} {q : ℕ}
    (h : R.HasQueryBoundOn P q) {x : I → A} (hx : P x) :
    R.expectedCost x ≤ (q : ℝ) := by
  calc
    R.expectedCost x = ∑ s, R.weights s * ((R.tree s).cost x : ℝ) := rfl
    _ ≤ ∑ s, R.weights s * (q : ℝ) :=
      Finset.sum_le_sum fun s _ ↦
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (h s x hx)) (R.weights_nonneg s)
    _ = (∑ s, R.weights s) * (q : ℝ) := (Finset.sum_mul _ _ _).symm
    _ = (q : ℝ) := by rw [R.sum_weights, one_mul]

/-- Error probability `Pr_s[(R.tree s).eval x ≠ out]`. -/
noncomputable def errorProb (R : RandDTree I A O) (x : I → A) (out : O) : ℝ := by
  classical exact ∑ s, R.weights s * if (R.tree s).eval x = out then 0 else 1

theorem errorProb_eq_sum_ite [DecidableEq O] (R : RandDTree I A O) (x : I → A) (out : O) :
    R.errorProb x out = ∑ s, R.weights s * if (R.tree s).eval x = out then 0 else 1 := by
  classical
  unfold errorProb
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  split_ifs <;> rfl

/-- Success probability `Pr_s[(R.tree s).eval x = out]`. -/
noncomputable def successProb (R : RandDTree I A O) (x : I → A) (out : O) : ℝ := by
  classical exact ∑ s, R.weights s * if (R.tree s).eval x = out then 1 else 0

theorem errorProb_ofDTree_eq_zero {T : DTree I A O} {x : I → A} {out : O} (h : T.eval x = out) :
    (ofDTree T).errorProb x out = 0 := by
  classical
  simp [errorProb_eq_sum_ite, ofDTree, h]

end RandDTree

variable {I A O : Type*}

/-- Sequentially queries the indices of `l` and passes the collected answers to `k`. -/
def DTree.queryList [DecidableEq I] :
    (l : List I) → ((∀ i, i ∈ l → A) → O) → DTree I A O
  | [], k => .leaf (k fun _ h ↦ False.elim (List.not_mem_nil h))
  | i :: tl, k =>
    .node i fun a ↦
      DTree.queryList tl fun f ↦
        k fun j hj ↦
          if hji : j = i then a else f j ((List.mem_cons.mp hj).resolve_left hji)

@[simp]
theorem DTree.eval_queryList [DecidableEq I] (l : List I) (k : (∀ i, i ∈ l → A) → O)
    (x : I → A) : (DTree.queryList l k).eval x = k (fun i _ ↦ x i) := by
  induction l with
  | nil =>
    simp only [queryList, eval_leaf]
    congr 1; funext i hi; exact False.elim (List.not_mem_nil hi)
  | cons i tl ih =>
    simp only [queryList, eval_node, ih]
    congr 1; funext j hj; split_ifs with hji
    · rw [hji]
    · rfl

@[simp]
theorem DTree.cost_queryList [DecidableEq I] (l : List I) (k : (∀ i, i ∈ l → A) → O)
    (x : I → A) : (DTree.queryList l k).cost x = l.length := by
  induction l with
  | nil => simp [queryList]
  | cons i tl ih => simp [queryList, ih, Nat.add_comm]

/-- Deterministic nonadaptive (parallel) query algorithm. -/
@[ext]
structure NonadaptiveAlg (I A O : Type*) where
  /-- Fixed finite set of indices queried in parallel. -/
  querySet : Finset I
  /-- Decision function on oracle answers restricted to `querySet`. -/
  decide : (querySet → A) → O

namespace NonadaptiveAlg

/-- Evaluates a nonadaptive query algorithm `alg` on `x`. -/
def eval (alg : NonadaptiveAlg I A O) (x : I → A) : O :=
  alg.decide fun i ↦ x i.1

/-- Number of parallel queries issued by `alg`. -/
def queryCount (alg : NonadaptiveAlg I A O) : ℕ :=
  alg.querySet.card

/-- Compiles `alg` into an adaptive deterministic decision tree of cost `alg.querySet.card`. -/
noncomputable def toDTree [DecidableEq I] (alg : NonadaptiveAlg I A O) : DTree I A O :=
  DTree.queryList alg.querySet.toList fun f ↦
    alg.decide fun i ↦ f i.1 (Finset.mem_toList.mpr i.2)

@[simp]
theorem eval_toDTree [DecidableEq I] (alg : NonadaptiveAlg I A O) (x : I → A) :
    alg.toDTree.eval x = alg.eval x := by
  simp [toDTree, eval]

@[simp]
theorem cost_toDTree [DecidableEq I] (alg : NonadaptiveAlg I A O) (x : I → A) :
    alg.toDTree.cost x = alg.querySet.card := by
  simp [toDTree]

end NonadaptiveAlg

end RandAndNonadaptive

section PromiseRelationalAdversary

variable {I A O ι : Type*}

/-- Row weight `W_y = ∑ z, R y z` of a relational adversary matrix `R`. -/
def relRowWeight [Fintype ι] (R : ι → ι → ℝ) (y : ι) : ℝ :=
  ∑ z, R y z

theorem relRowWeight_nonneg [Fintype ι] {R : ι → ι → ℝ} (hnonneg : ∀ y z, 0 ≤ R y z) (y : ι) :
    0 ≤ relRowWeight R y :=
  Finset.sum_nonneg fun z _ ↦ hnonneg y z

/-- Total weight `∑ y, relRowWeight R y` of a relational adversary matrix `R`. -/
def relTotalWeight [Fintype ι] (R : ι → ι → ℝ) : ℝ :=
  ∑ y, relRowWeight R y

/-- Coordinate disagreement weight `∑_{z : F y i ≠ F z i} R y z`. -/
noncomputable def relDisagreeWeight [Fintype ι] (F : ι → (I → A)) (R : ι → ι → ℝ) (y : ι)
    (i : I) : ℝ := by
  classical exact ∑ z, if F y i ≠ F z i then R y z else 0

theorem relDisagreeWeight_eq_sum_ite [Fintype ι] [DecidableEq A] (F : ι → (I → A))
    (R : ι → ι → ℝ) (y : ι) (i : I) :
    relDisagreeWeight F R y i = ∑ z, if F y i ≠ F z i then R y z else 0 := by
  classical
  unfold relDisagreeWeight
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  split_ifs <;> rfl

theorem le_relDisagreeWeight_of_ne [Fintype ι] {F : ι → (I → A)} {R : ι → ι → ℝ}
    (hnonneg : ∀ y z, 0 ≤ R y z) {y z : ι} {i : I} (hne : F y i ≠ F z i) :
    R y z ≤ relDisagreeWeight F R y i := by
  classical
  rw [relDisagreeWeight_eq_sum_ite]
  have hle := Finset.single_le_sum
    (f := fun w ↦ if F y i ≠ F w i then R y w else 0)
    (fun w _ ↦ by split_ifs; exacts [hnonneg y w, le_rfl]) (Finset.mem_univ z)
  simpa [hne] using hle

/-- Relational adversary ratio `relRowWeight R y / relDisagreeWeight F R y i`. -/
noncomputable def relRatio [Fintype ι] (F : ι → (I → A)) (R : ι → ι → ℝ) (y : ι) (i : I) : ℝ :=
  relRowWeight R y / relDisagreeWeight F R y i

/-- Deterministic classical relational adversary lower bound for promise functions. -/
theorem DTree.relAdversary_sum_cost_ge [Fintype ι]
    (T : DTree I A O) (F : ι → (I → A)) (P : ι → O) (R : ι → ι → ℝ) {v : ℝ}
    (hnonneg : ∀ y z, 0 ≤ R y z) (hsymm : ∀ y z, R y z = R z y)
    (hzero : ∀ y z, P y = P z → R y z = 0) (hv : 0 < v)
    (hcond : ∀ y z i, 0 < R y z → F y i ≠ F z i →
      v ≤ max (relRatio F R y i) (relRatio F R z i)) :
    v * (relTotalWeight R - 2 * ∑ y,
        by classical exact if T.eval (F y) = P y then 0 else relRowWeight R y) ≤
      2 * ∑ y, relRowWeight R y * (T.cost (F y) : ℝ) := by
  classical
  let succ : ι → ℝ := fun y ↦ if T.eval (F y) = P y then 1 else 0
  let good (y : ι) : Finset I :=
    (T.queriedSet (F y)).filter fun i ↦ v * relDisagreeWeight F R y i ≤ relRowWeight R y
  let dis (y z : ι) (i : I) : ℝ := if F y i ≠ F z i then R y z else 0
  have hdis_nonneg (y z : ι) (i : I) : 0 ≤ dis y z i := by
    by_cases h : F y i = F z i <;> simp [dis, h, hnonneg y z]
  have hsum_dis (y : ι) (i : I) : ∑ z, dis y z i = relDisagreeWeight F R y i :=
    (relDisagreeWeight_eq_sum_ite F R y i).symm
  have h1 :
      relTotalWeight R -
          2 * ∑ y, (if T.eval (F y) = P y then 0 else relRowWeight R y) ≤
        ∑ y, ∑ z, succ y * succ z * R y z := by
    have hpt :
        ∑ y, ∑ z, (succ y + succ z - 1) * R y z ≤ ∑ y, ∑ z, succ y * succ z * R y z := by
      refine Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun z _ ↦
        mul_le_mul_of_nonneg_right ?_ (hnonneg y z)
      have hy : succ y ≤ 1 := by dsimp [succ]; split_ifs <;> norm_num
      have hz : succ z ≤ 1 := by dsimp [succ]; split_ifs <;> norm_num
      nlinarith
    have hsymm_sum :
        ∑ y, ∑ z, (1 - succ z) * R y z = ∑ y, ∑ z, (1 - succ y) * R y z := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun y _ ↦ by rw [hsymm y z]
    have hsub :
        ∑ y, ∑ z, (succ y + succ z - 1) * R y z =
          ∑ y, ∑ z, R y z - ∑ y, ∑ z, (1 - succ y) * R y z - ∑ y, ∑ z, (1 - succ z) * R y z := by
      simp_rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    have herr :
        ∑ y, ∑ z, (1 - succ y) * R y z =
          ∑ y, (if T.eval (F y) = P y then 0 else relRowWeight R y) := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [← Finset.mul_sum]; change (1 - succ y) * relRowWeight R y = _
      dsimp [succ]; split_ifs <;> ring
    have htot : ∑ y, ∑ z, R y z = relTotalWeight R := rfl
    linarith
  have hpair (y z : ι) :
      succ y * succ z * R y z ≤
        (∑ i ∈ good y, dis y z i) + (∑ i ∈ good z, dis z y i) := by
    have hrhs_nonneg : 0 ≤ (∑ i ∈ good y, dis y z i) + (∑ i ∈ good z, dis z y i) :=
      add_nonneg (Finset.sum_nonneg fun i _ ↦ hdis_nonneg y z i)
        (Finset.sum_nonneg fun i _ ↦ hdis_nonneg z y i)
    by_cases hR : 0 < R y z
    · by_cases hy : T.eval (F y) = P y
      · by_cases hz : T.eval (F z) = P z
        · have hne_eval : T.eval (F y) ≠ T.eval (F z) := fun heq ↦ by
            linarith [hzero y z (by rw [← hy, ← hz, heq])]
          obtain ⟨i, hi, hFi⟩ := T.exists_mem_queriedSet_inter_of_eval_ne hne_eval
          rw [Finset.mem_inter] at hi
          have hlhs : succ y * succ z * R y z = R y z := by simp [succ, hy, hz]
          rw [hlhs]
          rcases le_max_iff.mp (hcond y z i hR hFi) with hvy | hvz
          · have hDpos : 0 < relDisagreeWeight F R y i :=
              lt_of_lt_of_le hR (le_relDisagreeWeight_of_ne hnonneg hFi)
            have hgood : i ∈ good y :=
              Finset.mem_filter.mpr ⟨hi.1, (le_div_iff₀ hDpos).mp hvy⟩
            have hsingle : R y z ≤ ∑ j ∈ good y, dis y z j := by
              simpa [dis, hFi] using Finset.single_le_sum (fun j _ ↦ hdis_nonneg y z j) hgood
            exact hsingle.trans
              (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hdis_nonneg z y j))
          · have hRzy : 0 < R z y := by rwa [hsymm z y]
            have hDpos : 0 < relDisagreeWeight F R z i :=
              lt_of_lt_of_le hRzy (le_relDisagreeWeight_of_ne hnonneg hFi.symm)
            have hgood : i ∈ good z :=
              Finset.mem_filter.mpr ⟨hi.2, (le_div_iff₀ hDpos).mp hvz⟩
            have hsingle : R y z ≤ ∑ j ∈ good z, dis z y j := by
              rw [hsymm y z]
              simpa [dis, hFi.symm] using
                Finset.single_le_sum (fun j _ ↦ hdis_nonneg z y j) hgood
            exact hsingle.trans
              (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ hdis_nonneg y z j))
        · have : succ y * succ z * R y z = 0 := by simp [succ, hz]
          linarith
      · have : succ y * succ z * R y z = 0 := by simp [succ, hy]
        linarith
    · rw [le_antisymm (not_lt.mp hR) (hnonneg y z), mul_zero]; exact hrhs_nonneg
  have hsum :
      ∑ y, ∑ z, succ y * succ z * R y z ≤ 2 * ∑ y, ∑ i ∈ good y, relDisagreeWeight F R y i := by
    have hstep1 :
        ∑ y, ∑ z, succ y * succ z * R y z ≤
          (∑ y, ∑ z, ∑ i ∈ good y, dis y z i) + ∑ y, ∑ z, ∑ i ∈ good z, dis z y i := by
      simp_rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun z _ ↦ hpair y z
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun y z ↦ ∑ i ∈ good z, dis z y i)] at hstep1
    have hinner (y : ι) :
        ∑ z, ∑ i ∈ good y, dis y z i = ∑ i ∈ good y, relDisagreeWeight F R y i := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ ↦ hsum_dis y i
    simp_rw [hinner] at hstep1
    linarith
  have hrow (y : ι) :
      v * ∑ i ∈ good y, relDisagreeWeight F R y i ≤ relRowWeight R y * (T.cost (F y) : ℝ) := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ good y, v * relDisagreeWeight F R y i
        ≤ ∑ _i ∈ good y, relRowWeight R y :=
          Finset.sum_le_sum fun _ hi ↦ (Finset.mem_filter.mp hi).2
      _ = ((good y).card : ℝ) * relRowWeight R y := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T.cost (F y) : ℝ) * relRowWeight R y :=
          mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr ((Finset.card_filter_le _ _).trans (T.card_queriedSet_le_cost (F y))))
            (relRowWeight_nonneg hnonneg y)
      _ = relRowWeight R y * (T.cost (F y) : ℝ) := mul_comm _ _
  calc
    v * (relTotalWeight R - 2 * ∑ y, (if T.eval (F y) = P y then 0 else relRowWeight R y))
      ≤ v * ∑ y, ∑ z, succ y * succ z * R y z := mul_le_mul_of_nonneg_left h1 hv.le
    _ ≤ v * (2 * ∑ y, ∑ i ∈ good y, relDisagreeWeight F R y i) :=
        mul_le_mul_of_nonneg_left hsum hv.le
    _ = 2 * ∑ y, v * ∑ i ∈ good y, relDisagreeWeight F R y i := by
        simp_rw [← Finset.mul_sum]; ring
    _ ≤ 2 * ∑ y, relRowWeight R y * (T.cost (F y) : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ ↦ hrow y) (by norm_num)

/-- Direct specialization of the deterministic promise relational adversary lower bound to Boolean
`Cslib.DecisionTree`. -/
theorem relAdversary_cslib_sum_cost_ge [Fintype ι]
    (t : Cslib.DecisionTree I O) (F : ι → (I → Bool)) (P : ι → O) (R : ι → ι → ℝ) {v : ℝ}
    (hnonneg : ∀ y z, 0 ≤ R y z) (hsymm : ∀ y z, R y z = R z y)
    (hzero : ∀ y z, P y = P z → R y z = 0) (hv : 0 < v)
    (hcond : ∀ y z i, 0 < R y z → F y i ≠ F z i →
      v ≤ max (relRatio F R y i) (relRatio F R z i)) :
    v * (relTotalWeight R - 2 * ∑ y,
        by classical exact if t.eval (F y) = P y then 0 else relRowWeight R y) ≤
      2 * ∑ y, relRowWeight R y * (t.cost (F y) : ℝ) := by
  have h := (DTree.equivCslib.symm t).relAdversary_sum_cost_ge F P R hnonneg hsymm hzero hv hcond
  have heval (y : ι) : (DTree.equivCslib.symm t).eval (F y) = t.eval (F y) := by
    rw [← DTree.eval_equivCslib, Equiv.apply_symm_apply]
  have hcost (y : ι) : (DTree.equivCslib.symm t).cost (F y) = t.cost (F y) := by
    rw [← DTree.cost_equivCslib, Equiv.apply_symm_apply]
  have hite :
      (∑ y, by classical exact if (DTree.equivCslib.symm t).eval (F y) = P y then 0
          else relRowWeight R y) =
        ∑ y, by classical exact if t.eval (F y) = P y then 0 else relRowWeight R y :=
    Finset.sum_congr rfl fun y _ ↦ by classical simp [heval y]
  rw [hite] at h
  simpa only [hcost] using h

/-- Aaronson's randomized classical relational adversary lower bound (average expected-cost
form). -/
theorem RandDTree.relAdversary_expectedCost_ge [Fintype ι]
    (Alg : RandDTree I A O) (F : ι → (I → A)) (P : ι → O) (R : ι → ι → ℝ) {v ε : ℝ}
    (hnonneg : ∀ y z, 0 ≤ R y z) (hsymm : ∀ y z, R y z = R z y)
    (hzero : ∀ y z, P y = P z → R y z = 0) (hv : 0 < v)
    (hcond : ∀ y z i, 0 < R y z → F y i ≠ F z i →
      v ≤ max (relRatio F R y i) (relRatio F R z i))
    (hε : ∀ y, Alg.errorProb (F y) (P y) ≤ ε) :
    ((1 - 2 * ε) / 2) * v * relTotalWeight R ≤
      ∑ y, relRowWeight R y * Alg.expectedCost (F y) := by
  classical
  have hsum :
      ∑ s : Fin Alg.numSeeds, Alg.weights s * (v * (relTotalWeight R - 2 * ∑ y,
          (if (Alg.tree s).eval (F y) = P y then 0 else relRowWeight R y))) ≤
        ∑ s : Fin Alg.numSeeds,
          Alg.weights s * (2 * ∑ y, relRowWeight R y * ((Alg.tree s).cost (F y) : ℝ)) :=
    Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
      ((Alg.tree s).relAdversary_sum_cost_ge F P R hnonneg hsymm hzero hv hcond)
      (Alg.weights_nonneg s)
  have hrhs :
      ∑ s, Alg.weights s * (2 * ∑ y, relRowWeight R y * ((Alg.tree s).cost (F y) : ℝ)) =
        2 * ∑ y, relRowWeight R y * Alg.expectedCost (F y) := by
    simp only [RandDTree.expectedCost, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hlhs_eq :
      ∑ s, Alg.weights s * (v * (relTotalWeight R - 2 * ∑ y,
          (if (Alg.tree s).eval (F y) = P y then 0 else relRowWeight R y))) =
        v * (relTotalWeight R - 2 * ∑ y, relRowWeight R y * Alg.errorProb (F y) (P y)) := by
    have hterm (s : Fin Alg.numSeeds) :
        Alg.weights s * (v * (relTotalWeight R - 2 * ∑ y,
            (if (Alg.tree s).eval (F y) = P y then 0 else relRowWeight R y))) =
          v * (Alg.weights s * relTotalWeight R -
            2 * ∑ y, relRowWeight R y * (Alg.weights s *
              if (Alg.tree s).eval (F y) = P y then 0 else 1)) := by
      have hinner :
          Alg.weights s * ∑ y,
              (if (Alg.tree s).eval (F y) = P y then 0 else relRowWeight R y) =
            ∑ y, relRowWeight R y * (Alg.weights s *
              if (Alg.tree s).eval (F y) = P y then 0 else 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ ↦ ?_
        split_ifs <;> ring
      calc
        Alg.weights s * (v * (relTotalWeight R - 2 * ∑ y,
            (if (Alg.tree s).eval (F y) = P y then 0 else relRowWeight R y)))
          = v * (Alg.weights s * relTotalWeight R) -
              v * (2 * (Alg.weights s * ∑ y,
                (if (Alg.tree s).eval (F y) = P y then 0 else relRowWeight R y))) := by ring
        _ = v * (Alg.weights s * relTotalWeight R -
              2 * ∑ y, relRowWeight R y * (Alg.weights s *
                if (Alg.tree s).eval (F y) = P y then 0 else 1)) := by rw [hinner]; ring
    simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Alg.sum_weights, one_mul, ← Finset.mul_sum]
    have hcomm :
        ∑ s, ∑ y, relRowWeight R y * (Alg.weights s *
            if (Alg.tree s).eval (F y) = P y then 0 else 1) =
          ∑ y, relRowWeight R y * Alg.errorProb (F y) (P y) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [← Finset.mul_sum, Alg.errorProb_eq_sum_ite]
    rw [hcomm]
  have herr_le :
      ∑ y, relRowWeight R y * Alg.errorProb (F y) (P y) ≤ ε * relTotalWeight R := by
    calc
      ∑ y, relRowWeight R y * Alg.errorProb (F y) (P y)
        ≤ ∑ y, relRowWeight R y * ε :=
          Finset.sum_le_sum fun y _ ↦
            mul_le_mul_of_nonneg_left (hε y) (relRowWeight_nonneg hnonneg y)
      _ = (∑ y, relRowWeight R y) * ε := (Finset.sum_mul _ _ _).symm
      _ = ε * relTotalWeight R := mul_comm _ _
  rw [hlhs_eq, hrhs] at hsum
  have hstep :
      v * (relTotalWeight R - 2 * (ε * relTotalWeight R)) ≤
        v * (relTotalWeight R - 2 * ∑ y, relRowWeight R y * Alg.errorProb (F y) (P y)) :=
    mul_le_mul_of_nonneg_left (by linarith) hv.le
  linarith

/-- Worst-case expected-cost form of Aaronson's randomized relational adversary lower bound. -/
theorem RandDTree.exists_relAdversary_expectedCost_ge [Fintype ι]
    (Alg : RandDTree I A O) (F : ι → (I → A)) (P : ι → O) (R : ι → ι → ℝ) {v ε : ℝ}
    (hnonneg : ∀ y z, 0 ≤ R y z) (hsymm : ∀ y z, R y z = R z y)
    (hzero : ∀ y z, P y = P z → R y z = 0) (hv : 0 < v)
    (hcond : ∀ y z i, 0 < R y z → F y i ≠ F z i →
      v ≤ max (relRatio F R y i) (relRatio F R z i))
    (htot : 0 < relTotalWeight R) (hε : ∀ y, Alg.errorProb (F y) (P y) ≤ ε) :
    ∃ y, ((1 - 2 * ε) / 2) * v ≤ Alg.expectedCost (F y) := by
  by_contra! hlt
  have hex : ∃ y₀, 0 < relRowWeight R y₀ := by
    by_contra! hle
    linarith [show relTotalWeight R ≤ 0 from Finset.sum_nonpos fun y _ ↦ hle y]
  obtain ⟨y₀, hy₀⟩ := hex
  have hsum_lt :
      ∑ y, relRowWeight R y * Alg.expectedCost (F y) <
        ∑ y, relRowWeight R y * (((1 - 2 * ε) / 2) * v) :=
    Finset.sum_lt_sum
      (fun y _ ↦ mul_le_mul_of_nonneg_left (hlt y).le (relRowWeight_nonneg hnonneg y))
      ⟨y₀, Finset.mem_univ y₀, mul_lt_mul_of_pos_left (hlt y₀) hy₀⟩
  have hge := Alg.relAdversary_expectedCost_ge F P R hnonneg hsymm hzero hv hcond hε
  rw [← Finset.sum_mul] at hsum_lt
  change ∑ y, relRowWeight R y * Alg.expectedCost (F y) <
    relTotalWeight R * (((1 - 2 * ε) / 2) * v) at hsum_lt
  linarith

/-- Worst-case query-bound form of Aaronson's randomized relational adversary lower bound. -/
theorem RandDTree.relAdversary_queryBound_ge [Fintype ι]
    (Alg : RandDTree I A O) (F : ι → (I → A)) (P : ι → O) (R : ι → ι → ℝ) {v ε : ℝ} {q : ℕ}
    (hnonneg : ∀ y z, 0 ≤ R y z) (hsymm : ∀ y z, R y z = R z y)
    (hzero : ∀ y z, P y = P z → R y z = 0) (hv : 0 < v)
    (hcond : ∀ y z i, 0 < R y z → F y i ≠ F z i →
      v ≤ max (relRatio F R y i) (relRatio F R z i))
    (htot : 0 < relTotalWeight R) (hε : ∀ y, Alg.errorProb (F y) (P y) ≤ ε)
    (hq : Alg.HasQueryBoundOn (fun x ↦ ∃ y, x = F y) q) :
    ((1 - 2 * ε) / 2) * v ≤ (q : ℝ) := by
  obtain ⟨y, hy⟩ :=
    Alg.exists_relAdversary_expectedCost_ge F P R hnonneg hsymm hzero hv hcond htot hε
  exact hy.trans (Alg.expectedCost_le_of_hasQueryBoundOn hq ⟨y, rfl⟩)

end PromiseRelationalAdversary

end CslibFrontier.QueryComplexity
