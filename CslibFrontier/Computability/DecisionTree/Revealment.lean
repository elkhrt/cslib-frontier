module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Computability.DecisionTree.Cost
public import CslibFrontier.Computability.QueryComplexity.Randomized
public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalCost
public import CslibFrontier.Computability.QueryComplexity.Randomized.ZeroError
public import CslibFrontier.Computability.QueryComplexity.YaoExpected
public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.BooleanAnalysis.MargulisRusso
public import CslibFrontier.Foundations.BooleanAnalysis.TransitiveSymmetric
public import CslibFrontier.Foundations.BooleanAnalysis.Variance
public import CslibFrontier.Foundations.Data.BitString.Graph
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import CslibFrontier.Foundations.Data.BitString.Flip
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Sym.Card
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Revealment, Coordinate Influence Inequalities, and Monotone Query-Complexity Lower Bounds

For functions on finite product probability spaces into pseudo-metric spaces, the variation
`𝔼_{x, y}[d(f x, f y)]` is bounded above by the sum over coordinates `i` of the revealment
`δ_i(T) = Pr_x[i ∈ T.queries x]` of any deterministic or zero-error randomized decision tree
computing `f` multiplied by the coordinate influence `Inf_i(f)`. A two-function generalization
bounds the absolute covariation `|𝔼_{x, y}[d(f x, g y)] - 𝔼_x[d(f x, g x)]|` by the
revealment-weighted sum of coordinate influences of `g`, yielding expected query-complexity lower
bounds for functions that approximate `g` in expectation.

Specializing to `p`-biased Boolean functions on `ι → Bool` connects revealment on
`Cslib.DecisionTree` and `Cslib.RandomizedDecisionTree` to distributional expected query complexity
and zero-error randomized query complexity:

* The `p`-biased variance satisfies `Var_p(f) ≤ ∑_i δ_i(T) Inf_i(f)`, so the distributional
  expected query complexity satisfies `Var_p(f) / Inf_max(f) ≤ Δ_p(f) ≤ R_0(f)`, and whenever
  `Δ_p(f) ≤ d`, some set of at most `d` coordinates has total influence at least `Var_p(f)`.
* For every monotone Boolean function, pairing unqueried coordinates along a loop-pruned tree with
  the second-moment identity for centered query sums proves `Inf_p(f) ≤ 2 √(p (1 - p) Δ_p(f))`.
* Every nonconstant monotone Boolean function has a unique critical probability `p ∈ (0, 1)` where
  its `{-1, 1}` expectation vanishes (`Var_p(f) = 1`). Combining transitive symmetry with the
  revealment and monotone total-influence bounds proves `|ι|^{2/3} / (4 p (1 - p))^{1/3} ≤ R_0(f)`
  for nonconstant monotone transitive Boolean functions and
  `(v - 1)^{4/3} / (16 p (1 - p))^{1/3} ≤ R_0(f_P)` for nontrivial monotone `v`-vertex graph
  properties.

## Main definitions

* `CslibFrontier.DecisionTree.Semimetric`: symmetric nonnegative distance vanishing on the diagonal.
* `CslibFrontier.DecisionTree.ProdDecisionTree`, `CslibFrontier.DecisionTree.ProdRDT`:
  deterministic and zero-error randomized decision trees over finite product domains.
* `CslibFrontier.DecisionTree.revealment`, `CslibFrontier.DecisionTree.revealmentRDT`,
  `CslibFrontier.DecisionTree.variation`, `CslibFrontier.DecisionTree.covariation`,
  `CslibFrontier.DecisionTree.prodInfluence`: product-space revealment, variation, covariation,
  and coordinate influence.
* `CslibFrontier.DecisionTree.boolVariance`, `CslibFrontier.DecisionTree.boolInfluence`,
  `CslibFrontier.DecisionTree.revealmentBool`, `CslibFrontier.DecisionTree.minExpectedQueriesBool`,
  `CslibFrontier.DecisionTree.IsCriticalProb`, `CslibFrontier.DecisionTree.graphPropertyFn`:
  `p`-biased Boolean variance, coordinate influence, revealment, distributional query complexity,
  critical probability, and encoding of `v`-vertex graph properties.

## Main results

* `CslibFrontier.DecisionTree.prodExpect_hybridSum`: exact expectation identity along the hybrid
  coupling trajectory of a repetition-free product decision tree.
* `CslibFrontier.DecisionTree.variation_le_sum_revealment_mul_prodInfluence`,
  `CslibFrontier.DecisionTree.variation_le_sum_revealmentRDT_mul_prodInfluence`,
  `CslibFrontier.DecisionTree.abs_covariation_le_sum_revealmentRDT_mul_prodInfluence`:
  one-function and two-function revealment-influence inequalities on pseudo-metric spaces.
* `CslibFrontier.DecisionTree.boolVariance_le_sum_revealmentBool_mul_boolInfluence`,
  `CslibFrontier.DecisionTree.boolVariance_div_boolMaxInfluence_le_minExpectedQueriesBool`,
  `CslibFrontier.DecisionTree.exists_card_le_and_boolVariance_le_sum_boolInfluence`:
  `p`-biased Boolean revealment inequalities and query-complexity lower bounds.
* `CslibFrontier.DecisionTree.boolTotalInfluence_le_two_mul_sqrt_expectedQueriesBool`,
  `CslibFrontier.DecisionTree.exists_unique_criticalProb`: monotone total-influence bound and
  existence and uniqueness of critical probability.
* `CslibFrontier.DecisionTree.card_rpow_div_le_minExpectedQueriesBool_of_isPretransitive`,
  `CslibFrontier.DecisionTree.graphProperty_rpow_le_minExpectedQueriesBool`: polynomial randomized
  query-complexity lower bounds for monotone transitive functions and monotone graph properties.
-/

public section

namespace CslibFrontier.DecisionTree

open Finset
open scoped BigOperators

/-! ### Symmetric nonnegative distance functions -/

/-- A symmetric nonnegative distance function vanishing on the diagonal, without requiring
definiteness or the triangle inequality. -/
@[ext]
structure Semimetric (Z : Type*) where
  /-- Pairwise distance `Z → Z → ℝ`. -/
  dist : Z → Z → ℝ
  /-- Nonnegativity of pairwise distances. -/
  dist_nonneg : ∀ x y : Z, 0 ≤ dist x y
  /-- Zero distance on identical points. -/
  dist_self : ∀ x : Z, dist x x = 0
  /-- Symmetry of pairwise distances. -/
  dist_comm : ∀ x y : Z, dist x y = dist y x

namespace Semimetric

/-- Canonical `Semimetric` induced by a `PseudoMetricSpace`. -/
def ofPseudoMetricSpace (Z : Type*) [PseudoMetricSpace Z] : Semimetric Z where
  dist := Dist.dist
  dist_nonneg _ _ := _root_.dist_nonneg
  dist_self := _root_.dist_self
  dist_comm := _root_.dist_comm

@[simp]
theorem ofPseudoMetricSpace_dist (Z : Type*) [PseudoMetricSpace Z] (x y : Z) :
    (ofPseudoMetricSpace Z).dist x y = Dist.dist x y := by rfl

/-- Scaled discrete metric on `Bool` matching distance in `{-1, 1} ⊂ ℝ`: `0` on equal bits and `2`
on distinct bits. -/
def discreteBool : Semimetric Bool where
  dist b b' := if b = b' then 0 else 2
  dist_nonneg b b' := by split_ifs <;> norm_num
  dist_self b := by simp
  dist_comm b b' := by
    by_cases h : b = b'
    · simp [h]
    · simp [h, Ne.symm h]

@[simp]
theorem discreteBool_dist (b b' : Bool) :
    discreteBool.dist b b' = if b = b' then 0 else 2 := by rfl

end Semimetric

/-! ### Finite product probability spaces -/

section ProductProb

variable {ι : Type*} {X : ι → Type*}

/-- Product weight `∏ i, μ_i(x_i)` of a point `x` in a finite product probability space. -/
def prodWeight [Fintype ι] (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (x : ∀ i : ι, X i) : ℝ :=
  ∏ i, (μ i).weights (x i)

/-- Expectation `∑_x (∏_i μ_i(x_i)) h(x)` over a finite product probability space. -/
def prodExpect [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (h : (∀ i : ι, X i) → ℝ) : ℝ :=
  ∑ x : ∀ i : ι, X i, prodWeight μ x * h x

/-- Coordinate simplex weights sum to `1` over a finite type. -/
theorem sum_simplex_weights {α : Type*} [Fintype α] (s : Convexity.StdSimplex ℝ α) :
    ∑ a : α, s.weights a = 1 := by
  have h := s.total
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h

/-- Product weights are nonnegative. -/
theorem prodWeight_nonneg [Fintype ι] (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i))
    (x : ∀ i : ι, X i) : 0 ≤ prodWeight μ x :=
  prod_nonneg fun i _ => (μ i).nonneg (x i)

/-- Product weights sum to `1`. -/
theorem sum_prodWeight [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) :
    ∑ x : ∀ i : ι, X i, prodWeight μ x = 1 := by
  unfold prodWeight
  rw [← Fintype.prod_sum (fun i (a : X i) => (μ i).weights a)]
  exact prod_eq_one fun i _ => sum_simplex_weights (μ i)

/-- Product distribution packaged as a `Convexity.StdSimplex`. -/
noncomputable def prodSimplex [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) : Convexity.StdSimplex ℝ (∀ i : ι, X i) where
  weights := Finsupp.equivFunOnFinite.symm (prodWeight μ)
  nonneg x := by simpa using prodWeight_nonneg μ x
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa using sum_prodWeight μ

/-- Product expectation agrees with the `StdSimplex` weighted sum of `prodSimplex μ`. -/
theorem prodExpect_eq_simplex_sum [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (h : (∀ i : ι, X i) → ℝ) :
    prodExpect μ h = (prodSimplex μ).weights.sum fun x w => w * h x := by
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp [prodExpect, prodSimplex]

/-- Constant functions have expectation equal to the constant. -/
theorem prodExpect_const [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (c : ℝ) :
    prodExpect μ (fun _ => c) = c := by
  simp only [prodExpect, ← sum_mul, sum_prodWeight, one_mul]

@[simp]
theorem prodExpect_zero [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) :
    prodExpect μ (fun _ => 0) = 0 :=
  prodExpect_const μ 0

theorem prodExpect_add [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f g : (∀ i : ι, X i) → ℝ) :
    prodExpect μ (fun x => f x + g x) = prodExpect μ f + prodExpect μ g := by
  simp only [prodExpect, mul_add, sum_add_distrib]

theorem prodExpect_sub [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f g : (∀ i : ι, X i) → ℝ) :
    prodExpect μ (fun x => f x - g x) = prodExpect μ f - prodExpect μ g := by
  simp only [prodExpect, mul_sub, sum_sub_distrib]

theorem prodExpect_const_mul [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (c : ℝ) (f : (∀ i : ι, X i) → ℝ) :
    prodExpect μ (fun x => c * f x) = c * prodExpect μ f := by
  simp only [prodExpect, mul_sum, mul_left_comm]

theorem prodExpect_sum [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] {α : Type*} (s : Finset α)
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f : α → (∀ i : ι, X i) → ℝ) :
    prodExpect μ (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, prodExpect μ (f a) := by
  simp only [prodExpect, mul_sum]
  exact sum_comm

@[gcongr]
theorem prodExpect_mono [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) {f g : (∀ i : ι, X i) → ℝ}
    (hfg : ∀ x, f x ≤ g x) : prodExpect μ f ≤ prodExpect μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (prodWeight_nonneg μ x)

theorem prodExpect_nonneg [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) {f : (∀ i : ι, X i) → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ prodExpect μ f :=
  sum_nonneg fun x _ => mul_nonneg (prodWeight_nonneg μ x) (hf x)

theorem abs_prodExpect_le [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f : (∀ i : ι, X i) → ℝ) :
    |prodExpect μ f| ≤ prodExpect μ (fun x => |f x|) := by
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  refine sum_congr rfl fun x _ => ?_
  rw [abs_mul, abs_of_nonneg (prodWeight_nonneg μ x)]

/-- Resampling a single coordinate `i` independently from `μ i` preserves `prodExpect μ`. -/
theorem prodExpect_update [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (h : (∀ j : ι, X j) → ℝ) :
    ∑ a : X i, (μ i).weights a * prodExpect μ (fun x => h (Function.update x i a)) =
      prodExpect μ h := by
  classical
  let e := Equiv.piSplitAt i X
  have hw (x : ∀ j, X j) :
      prodWeight μ x = (μ i).weights (x i) * ∏ j : {j // j ≠ i}, (μ j).weights (x j) :=
    Fintype.prod_eq_mul_prod_subtype_ne (fun j => (μ j).weights (x j)) i
  have hupd_eq (a : X i) (x : ∀ j, X j) :
      Function.update x i a = e.symm (a, fun j : {j // j ≠ i} => x j) := by
    funext j
    by_cases hji : j = i
    · subst hji; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hji]
  have hsum_rest (a : X i) :
      prodExpect μ (fun x => h (Function.update x i a)) =
        ∑ y : ∀ j : {j // j ≠ i}, X j,
          (∏ j : {j // j ≠ i}, (μ j).weights (y j)) * h (e.symm (a, y)) := by
    unfold prodExpect
    rw [← e.symm.sum_comp]
    simp_rw [hw]
    have hfst (z : X i × (∀ j : {j // j ≠ i}, X j)) : e.symm z i = z.1 := by
      simp [e, Equiv.piSplitAt]
    have hsnd (z : X i × (∀ j : {j // j ≠ i}, X j)) (j : {j // j ≠ i}) : e.symm z j = z.2 j := by
      simp [e, Equiv.piSplitAt, j.property]
    simp_rw [hupd_eq, hfst, hsnd]
    rw [Fintype.sum_prod_type]
    dsimp only
    simp_rw [mul_assoc, ← mul_sum]
    rw [← sum_mul, sum_simplex_weights, one_mul]
  simp_rw [hsum_rest, mul_sum]
  rw [← Fintype.sum_prod_type (fun z : X i × (∀ j : {j // j ≠ i}, X j) =>
    (μ i).weights z.1 * ((∏ j : {j // j ≠ i}, (μ j).weights (z.2 j)) * h (e.symm z)))]
  symm
  unfold prodExpect
  rw [← e.symm.sum_comp]
  refine sum_congr rfl fun z _ => ?_
  rw [hw]
  have hfst : e.symm z i = z.1 := by simp [e, Equiv.piSplitAt]
  have hsnd : ∀ j : {j // j ≠ i}, e.symm z j = z.2 j := fun j => by
    simp [e, Equiv.piSplitAt, j.property]
  simp_rw [hfst, hsnd]
  ring

theorem prodExpect_comm [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (h : (∀ i : ι, X i) → (∀ i : ι, X i) → ℝ) :
    prodExpect μ (fun x => prodExpect μ (fun y => h x y)) =
      prodExpect μ (fun y => prodExpect μ (fun x => h x y)) := by
  simp only [prodExpect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem prodExpect_prodExpect_update_left [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι)
    (h : (∀ j : ι, X j) → (∀ j : ι, X j) → ℝ) :
    ∑ a : X i, (μ i).weights a *
        prodExpect μ (fun x => prodExpect μ (fun y => h (Function.update x i a) y)) =
      prodExpect μ (fun x => prodExpect μ (fun y => h x y)) :=
  prodExpect_update μ i (fun x => prodExpect μ (fun y => h x y))

theorem prodExpect_prodExpect_update_right [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι)
    (h : (∀ j : ι, X j) → (∀ j : ι, X j) → ℝ) :
    ∑ b : X i, (μ i).weights b *
        prodExpect μ (fun x => prodExpect μ (fun y => h x (Function.update y i b))) =
      prodExpect μ (fun x => prodExpect μ (fun y => h x y)) := by
  rw [prodExpect_comm μ h]
  have h1 := prodExpect_update μ i (fun y => prodExpect μ (fun x => h x y))
  rw [← h1]
  refine sum_congr rfl fun b _ => ?_
  rw [prodExpect_comm]

/-- Single-coordinate Bernoulli distribution on `Bool` with `Pr[true] = p` and
`Pr[false] = 1 - p`. -/
noncomputable def bernoulliCoordSimplex {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Convexity.StdSimplex ℝ Bool :=
  Convexity.StdSimplex.duple true false hp0 (sub_nonneg.mpr hp1) (add_sub_cancel p 1)

@[simp]
theorem bernoulliCoordSimplex_weights_true {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliCoordSimplex hp0 hp1).weights true = p := by
  simp [bernoulliCoordSimplex]

@[simp]
theorem bernoulliCoordSimplex_weights_false {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliCoordSimplex hp0 hp1).weights false = 1 - p := by
  simp [bernoulliCoordSimplex]

/-- `p`-biased product distribution on `ι → Bool` as a coordinate family of simplices. -/
noncomputable def bernoulliCoordFamily (ι : Type*) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ _ : ι, Convexity.StdSimplex ℝ Bool :=
  fun _ => bernoulliCoordSimplex hp0 hp1

@[simp]
theorem bernoulliCoordFamily_apply (ι : Type*) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) :
    bernoulliCoordFamily ι hp0 hp1 i = bernoulliCoordSimplex hp0 hp1 := by rfl

theorem prodWeight_bernoulliCoordFamily [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) :
    prodWeight (bernoulliCoordFamily ι hp0 hp1) x = Cslib.BitString.bernoulliWeight p x := by
  refine prod_congr rfl fun i _ => ?_
  cases x i <;> simp [bernoulliCoordFamily]

theorem prodExpect_bernoulliCoordFamily [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : (ι → Bool) → ℝ) :
    prodExpect (bernoulliCoordFamily ι hp0 hp1) h = Cslib.BitString.bernoulliAverage p h := by
  unfold prodExpect Cslib.BitString.bernoulliAverage
  refine sum_congr rfl fun x _ => ?_
  rw [prodWeight_bernoulliCoordFamily]

/-- `p`-biased product distribution on `ι → Bool` packaged as a `Convexity.StdSimplex`. -/
noncomputable def bernoulliProductSimplex [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Convexity.StdSimplex ℝ (ι → Bool) :=
  prodSimplex (bernoulliCoordFamily ι hp0 hp1)

theorem bernoulliProductSimplex_eq_prodSimplex [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliProductSimplex hp0 hp1 : Convexity.StdSimplex ℝ (ι → Bool)) =
      prodSimplex (bernoulliCoordFamily ι hp0 hp1) := by rfl

end ProductProb

/-! ### Deterministic and zero-error randomized decision trees over product domains -/

/-- Deterministic decision tree over a product domain `∀ i : ι, X i` with outputs in `Z`. -/
inductive ProdDecisionTree {ι : Type*} (X : ι → Type*) (Z : Type*) where
  /-- Leaf outputting `z : Z`. -/
  | leaf (z : Z)
  /-- Internal query node reading coordinate `i : ι` and branching on `X i`. -/
  | node (i : ι) (children : X i → ProdDecisionTree X Z)

namespace ProdDecisionTree

variable {ι : Type*} {X : ι → Type*} {Z W : Type*}

/-- Evaluate a product decision tree on an input `x`. -/
@[expose]
def eval : ProdDecisionTree X Z → (∀ i : ι, X i) → Z
  | leaf z, _ => z
  | node i c, x => (c (x i)).eval x

@[simp]
theorem eval_leaf (z : Z) (x : ∀ i : ι, X i) : (leaf z : ProdDecisionTree X Z).eval x = z := rfl

@[simp]
theorem eval_node (i : ι) (c : X i → ProdDecisionTree X Z) (x : ∀ j : ι, X j) :
    (node i c).eval x = (c (x i)).eval x := rfl

/-- A product decision tree computes `f` if it evaluates to `f x` on every input `x`. -/
@[expose]
def Computes (T : ProdDecisionTree X Z) (f : (∀ i : ι, X i) → Z) : Prop :=
  ∀ x, T.eval x = f x

/-- Relabel the leaves of a product decision tree by `φ : Z → W`. -/
@[expose]
def map (φ : Z → W) : ProdDecisionTree X Z → ProdDecisionTree X W
  | leaf z => leaf (φ z)
  | node i c => node i fun a => (c a).map φ

@[simp]
theorem eval_map (φ : Z → W) (T : ProdDecisionTree X Z) (x : ∀ i : ι, X i) :
    (T.map φ).eval x = φ (T.eval x) := by
  induction T with
  | leaf _ => rfl
  | node i _ ih => exact ih (x i)

/-- Number of queries executed along the root-to-leaf path on input `x`. -/
@[expose]
def cost : ProdDecisionTree X Z → (∀ i : ι, X i) → ℕ
  | leaf _, _ => 0
  | node i c, x => (c (x i)).cost x + 1

@[simp]
theorem cost_leaf (z : Z) (x : ∀ i : ι, X i) : (leaf z : ProdDecisionTree X Z).cost x = 0 := rfl

@[simp]
theorem cost_node (i : ι) (c : X i → ProdDecisionTree X Z) (x : ∀ j : ι, X j) :
    (node i c).cost x = (c (x i)).cost x + 1 := rfl

/-- Maximum structural root-to-leaf path length of a product decision tree. -/
@[expose]
def depth [∀ i, Fintype (X i)] : ProdDecisionTree X Z → ℕ
  | leaf _ => 0
  | node i c => Finset.univ.sup (fun a : X i => (c a).depth) + 1

@[simp]
theorem depth_leaf [∀ i, Fintype (X i)] (z : Z) :
    (leaf z : ProdDecisionTree X Z).depth = 0 := rfl

@[simp]
theorem depth_node [∀ i, Fintype (X i)] (i : ι) (c : X i → ProdDecisionTree X Z) :
    (node i c).depth = Finset.univ.sup (fun a : X i => (c a).depth) + 1 := rfl

/-- Coordinates queried along the execution path of `T` on input `x`. -/
@[expose]
def queries [DecidableEq ι] : ProdDecisionTree X Z → (∀ i : ι, X i) → Finset ι
  | leaf _, _ => ∅
  | node i c, x => insert i ((c (x i)).queries x)

@[simp]
theorem queries_leaf [DecidableEq ι] (z : Z) (x : ∀ i : ι, X i) :
    (leaf z : ProdDecisionTree X Z).queries x = ∅ := rfl

@[simp]
theorem queries_node [DecidableEq ι] (i : ι) (c : X i → ProdDecisionTree X Z) (x : ∀ j : ι, X j) :
    (node i c).queries x = insert i ((c (x i)).queries x) := rfl

@[simp]
theorem queries_map [DecidableEq ι] (φ : Z → W) (T : ProdDecisionTree X Z) (x : ∀ i : ι, X i) :
    (T.map φ).queries x = T.queries x := by
  induction T with
  | leaf _ => rfl
  | node _ _ ih => simp [map, ih]

theorem card_queries_le_cost [DecidableEq ι] (T : ProdDecisionTree X Z) (x : ∀ i : ι, X i) :
    (T.queries x).card ≤ T.cost x := by
  induction T with
  | leaf _ => simp
  | node i _ ih =>
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (ih (x i)) 1)

/-- All coordinates appearing at internal nodes along any structural branch of `T`. -/
@[expose]
def allQueries [DecidableEq ι] [∀ i, Fintype (X i)] : ProdDecisionTree X Z → Finset ι
  | leaf _ => ∅
  | node i c => insert i (Finset.univ.biUnion fun a : X i => (c a).allQueries)

@[simp]
theorem allQueries_leaf [DecidableEq ι] [∀ i, Fintype (X i)] (z : Z) :
    (leaf z : ProdDecisionTree X Z).allQueries = ∅ := rfl

@[simp]
theorem allQueries_node [DecidableEq ι] [∀ i, Fintype (X i)]
    (i : ι) (c : X i → ProdDecisionTree X Z) :
    (node i c).allQueries = insert i (Finset.univ.biUnion fun a : X i => (c a).allQueries) := rfl

theorem queries_subset_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    (T : ProdDecisionTree X Z) (x : ∀ i : ι, X i) : T.queries x ⊆ T.allQueries := by
  induction T with
  | leaf _ => exact Finset.empty_subset _
  | node i c ih =>
    refine Finset.insert_subset_insert i ?_
    exact (ih (x i)).trans (Finset.subset_biUnion_of_mem (fun a => (c a).allQueries)
      (Finset.mem_univ (x i)))

/-- Predicate stating that no coordinate is queried more than once along any root-to-leaf path. -/
@[expose]
def NoRepeat [DecidableEq ι] [∀ i, Fintype (X i)] : ProdDecisionTree X Z → Prop
  | leaf _ => True
  | node i c => ∀ a : X i, (c a).NoRepeat ∧ i ∉ (c a).allQueries

theorem noRepeat_node_iff [DecidableEq ι] [∀ i, Fintype (X i)]
    (i : ι) (c : X i → ProdDecisionTree X Z) :
    (node i c).NoRepeat ↔ ∀ a : X i, (c a).NoRepeat ∧ i ∉ (c a).allQueries := Iff.rfl

theorem card_queries_eq_cost_of_noRepeat [DecidableEq ι] [∀ i, Fintype (X i)]
    {T : ProdDecisionTree X Z} (hT : T.NoRepeat) (x : ∀ i : ι, X i) :
    (T.queries x).card = T.cost x := by
  induction T with
  | leaf _ => simp
  | node i c ih =>
    have hi : i ∉ (c (x i)).queries x := fun h =>
      (hT (x i)).2 (queries_subset_allQueries (c (x i)) x h)
    rw [queries_node, Finset.card_insert_of_notMem hi, cost_node, ih (x i) (hT (x i)).1]

theorem eval_eq_of_eq_on_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    (T : ProdDecisionTree X Z) {x y : ∀ i : ι, X i}
    (h : ∀ j ∈ T.allQueries, x j = y j) : T.eval x = T.eval y := by
  induction T with
  | leaf _ => rfl
  | node i c ih =>
    have hi : x i = y i := h i (Finset.mem_insert_self i _)
    rw [eval_node, eval_node, hi]
    exact ih (y i) fun j hj =>
      h j (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨y i, Finset.mem_univ _, hj⟩))

theorem eval_eq_of_forall_mem_queries [DecidableEq ι]
    (T : ProdDecisionTree X Z) {x y : ∀ i : ι, X i}
    (h : ∀ j ∈ T.queries x, y j = x j) : T.eval y = T.eval x := by
  induction T with
  | leaf _ => rfl
  | node i _ ih =>
    have hi : y i = x i := h i (Finset.mem_insert_self i _)
    rw [eval_node, eval_node, hi]
    exact ih (x i) fun j hj => h j (Finset.mem_insert_of_mem hj)

theorem queries_eq_of_forall_mem_queries [DecidableEq ι]
    (T : ProdDecisionTree X Z) {x y : ∀ i : ι, X i}
    (h : ∀ j ∈ T.queries x, y j = x j) : T.queries y = T.queries x := by
  induction T with
  | leaf _ => rfl
  | node i _ ih =>
    have hi : y i = x i := h i (Finset.mem_insert_self i _)
    rw [queries_node, queries_node, hi, ih (x i) fun j hj => h j (Finset.mem_insert_of_mem hj)]

theorem eval_update_of_notMem_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    {T : ProdDecisionTree X Z} {i : ι} (hi : i ∉ T.allQueries)
    (x : ∀ j : ι, X j) (a : X i) : T.eval (Function.update x i a) = T.eval x :=
  eval_eq_of_eq_on_allQueries T fun j hj =>
    Function.update_of_ne (by rintro rfl; exact hi hj) a x

theorem queries_update_of_notMem_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    {T : ProdDecisionTree X Z} {i : ι} (hi : i ∉ T.allQueries)
    (x : ∀ j : ι, X j) (a : X i) : T.queries (Function.update x i a) = T.queries x :=
  queries_eq_of_forall_mem_queries T fun j hj =>
    Function.update_of_ne (by rintro rfl; exact hi (queries_subset_allQueries T x hj)) a x

/-- Remove repeated queries along every path by recording observed answers in `ρ`. -/
@[expose]
def prune [DecidableEq ι] :
    ProdDecisionTree X Z → (∀ i : ι, Option (X i)) → ProdDecisionTree X Z
  | leaf z, _ => leaf z
  | node i c, ρ =>
    match ρ i with
    | some a => (c a).prune ρ
    | none => node i fun a => (c a).prune (Function.update ρ i (some a))

private def fixedCoords [Fintype ι] (ρ : ∀ i : ι, Option (X i)) : Finset ι :=
  Finset.univ.filter fun i => (ρ i).isSome

private theorem mem_fixedCoords [Fintype ι] {ρ : ∀ i : ι, Option (X i)} {i : ι} :
    i ∈ fixedCoords ρ ↔ (ρ i).isSome := by
  simp [fixedCoords]

theorem notMem_allQueries_prune_of_isSome [DecidableEq ι] [∀ i, Fintype (X i)]
    (T : ProdDecisionTree X Z) (ρ : ∀ i : ι, Option (X i)) {i : ι} (hi : (ρ i).isSome) :
    i ∉ (T.prune ρ).allQueries := by
  induction T generalizing ρ with
  | leaf _ => simp [prune]
  | node j c ih =>
    cases hρj : ρ j with
    | some a => simpa [prune, hρj] using ih a ρ hi
    | none =>
      have hne : i ≠ j := by intro h; subst h; simp [hρj] at hi
      simp only [prune, hρj, allQueries_node, Finset.mem_insert, Finset.mem_biUnion,
        Finset.mem_univ, true_and, not_or, not_exists]
      refine ⟨hne, fun a => ih a (Function.update ρ j (some a)) ?_⟩
      simpa [Function.update_of_ne hne] using hi

theorem noRepeat_prune [DecidableEq ι] [∀ i, Fintype (X i)]
    (T : ProdDecisionTree X Z) (ρ : ∀ i : ι, Option (X i)) : (T.prune ρ).NoRepeat := by
  induction T generalizing ρ with
  | leaf _ => trivial
  | node i c ih =>
    cases hρi : ρ i with
    | some a => simpa [prune, hρi] using ih a ρ
    | none =>
      simp only [prune, hρi, noRepeat_node_iff]
      intro a
      exact ⟨ih a _, notMem_allQueries_prune_of_isSome (c a) _ (by simp)⟩

theorem eval_prune_of_agrees [DecidableEq ι] (T : ProdDecisionTree X Z)
    (ρ : ∀ i : ι, Option (X i)) {x : ∀ i : ι, X i}
    (hx : ∀ i a, ρ i = some a → x i = a) : (T.prune ρ).eval x = T.eval x := by
  induction T generalizing ρ with
  | leaf _ => rfl
  | node i c ih =>
    cases hρi : ρ i with
    | some a =>
      have hxi : x i = a := hx i a hρi
      simp only [prune, hρi, eval_node, hxi]
      exact ih a ρ hx
    | none =>
      simp only [prune, hρi, eval_node]
      refine ih (x i) (Function.update ρ i (some (x i))) fun j b hj => ?_
      by_cases hji : j = i
      · subst hji; simp only [Function.update_self, Option.some.injEq] at hj; exact hj
      · exact hx j b (by rwa [Function.update_of_ne hji] at hj)

private theorem queries_prune_union_fixed [DecidableEq ι] [Fintype ι] (T : ProdDecisionTree X Z)
    (ρ : ∀ i : ι, Option (X i)) {x : ∀ i : ι, X i}
    (hx : ∀ i a, ρ i = some a → x i = a) :
    (T.prune ρ).queries x ∪ fixedCoords ρ = T.queries x ∪ fixedCoords ρ := by
  induction T generalizing ρ with
  | leaf _ => simp [prune]
  | node i c ih =>
    cases hρi : ρ i with
    | some a =>
      have hxi : x i = a := hx i a hρi
      have hi_mem : i ∈ fixedCoords ρ := mem_fixedCoords.mpr (by simp [hρi])
      simp only [prune, hρi, queries_node, hxi]
      rw [ih a ρ hx]
      ext j
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · intro h
        rcases h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · intro h
        rcases h with (rfl | h) | h
        · exact Or.inr hi_mem
        · exact Or.inl h
        · exact Or.inr h
    | none =>
      have hfixed : fixedCoords (Function.update ρ i (some (x i))) =
          insert i (fixedCoords ρ) := by
        ext j
        by_cases hji : j = i
        · subst hji; simp [mem_fixedCoords]
        · simp [mem_fixedCoords, hji]
      have hx' : ∀ j b, Function.update ρ i (some (x i)) j = some b → x j = b := by
        intro j b hj
        by_cases hji : j = i
        · subst hji; simp only [Function.update_self, Option.some.injEq] at hj; exact hj
        · exact hx j b (by rwa [Function.update_of_ne hji] at hj)
      have hrec := ih (x i) (Function.update ρ i (some (x i))) hx'
      rw [hfixed] at hrec
      simp only [prune, hρi, queries_node]
      rw [Finset.insert_union, ← Finset.union_insert, hrec, Finset.union_insert,
        ← Finset.insert_union]

theorem eval_prune_empty [DecidableEq ι] (T : ProdDecisionTree X Z) (x : ∀ i : ι, X i) :
    (T.prune (fun _ => none)).eval x = T.eval x :=
  eval_prune_of_agrees T _ fun _ _ h => by simp at h

theorem queries_prune_empty [DecidableEq ι] [Finite ι]
    (T : ProdDecisionTree X Z) (x : ∀ i : ι, X i) :
    (T.prune (fun _ => none)).queries x = T.queries x := by
  let _ := Fintype.ofFinite ι
  have h := queries_prune_union_fixed T (fun _ => none) (x := x) (fun _ _ h => by simp at h)
  have h0 : fixedCoords (X := X) (fun _ => none) = ∅ := by
    ext i; simp [mem_fixedCoords]
  simpa [h0] using h

/-- Convert a `Cslib.DecisionTree ι Z` into a Boolean-domain `ProdDecisionTree`. -/
@[expose]
def ofCslib : Cslib.DecisionTree ι Z → ProdDecisionTree (fun _ : ι => Bool) Z
  | .leaf z => leaf z
  | .node i t₀ t₁ => node i fun b => cond b (ofCslib t₁) (ofCslib t₀)

/-- Convert a Boolean-domain `ProdDecisionTree` into a `Cslib.DecisionTree ι Z`. -/
@[expose]
def toCslib : ProdDecisionTree (fun _ : ι => Bool) Z → Cslib.DecisionTree ι Z
  | leaf z => .leaf z
  | node i c => .node i (toCslib (c false)) (toCslib (c true))

@[simp]
theorem ofCslib_toCslib (T : ProdDecisionTree (fun _ : ι => Bool) Z) :
    ofCslib (toCslib T) = T := by
  induction T with
  | leaf _ => rfl
  | node i c ih =>
    simp only [toCslib, ofCslib]
    congr 1
    funext b
    cases b <;> simpa using ih _

@[simp]
theorem eval_ofCslib (t : Cslib.DecisionTree ι Z) (x : ι → Bool) :
    (ofCslib t).eval x = t.eval x := by
  induction t with
  | leaf _ => rfl
  | node i _ _ ih₀ ih₁ => cases h : x i <;> simp [ofCslib, h, ih₀, ih₁]

@[simp]
theorem eval_toCslib (T : ProdDecisionTree (fun _ : ι => Bool) Z) (x : ι → Bool) :
    (toCslib T).eval x = T.eval x := by
  induction T with
  | leaf _ => rfl
  | node i _ ih => cases h : x i <;> simp [toCslib, h, ih]

@[simp]
theorem queries_ofCslib [DecidableEq ι] (t : Cslib.DecisionTree ι Z) (x : ι → Bool) :
    (ofCslib t).queries x = t.queries x := by
  induction t with
  | leaf _ => rfl
  | node i _ _ ih₀ ih₁ => cases h : x i <;> simp [ofCslib, h, ih₀, ih₁]

@[simp]
theorem queries_toCslib [DecidableEq ι] (T : ProdDecisionTree (fun _ : ι => Bool) Z)
    (x : ι → Bool) : (toCslib T).queries x = T.queries x := by
  induction T with
  | leaf _ => rfl
  | node i _ ih => cases h : x i <;> simp [toCslib, h, ih]

@[simp]
theorem cost_ofCslib (t : Cslib.DecisionTree ι Z) (x : ι → Bool) :
    (ofCslib t).cost x = t.cost x := by
  induction t with
  | leaf _ => rfl
  | node i _ _ ih₀ ih₁ => cases h : x i <;> simp [ofCslib, h, ih₀, ih₁]

end ProdDecisionTree

/-- Zero-error randomized decision tree over a product domain: a finitely supported probability
distribution over deterministic product decision trees. -/
abbrev ProdRDT {ι : Type*} (X : ι → Type*) (Z : Type*) : Type _ :=
  Convexity.StdSimplex ℝ (ProdDecisionTree X Z)

namespace ProdRDT

/-- A randomized product decision tree computes `f` with zero error when every tree in its support
computes `f`. -/
@[expose]
def Computes {ι : Type*} {X : ι → Type*} {Z : Type*}
    (𝒯 : ProdRDT X Z) (f : (∀ i : ι, X i) → Z) : Prop :=
  ∀ T ∈ 𝒯.weights.support, T.Computes f

end ProdRDT

/-! ### Revealment, variation, covariation, and coordinate influences -/

section ProductMeasures

variable {ι : Type*} {X : ι → Type*} {Z : Type*}

/-- Revealment `δ_i(T) = Pr_{x ← μ}[i ∈ T.queries x]` of coordinate `i` for a deterministic
product decision tree `T`. -/
def revealment [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (T : ProdDecisionTree X Z) : ℝ :=
  prodExpect μ fun x => if i ∈ T.queries x then 1 else 0

/-- Revealment `δ_i(𝒯)` of coordinate `i` for a randomized product decision tree `𝒯`. -/
noncomputable def revealmentRDT [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (𝒯 : ProdRDT X Z) : ℝ :=
  𝒯.weights.sum fun T w => w * revealment μ i T

/-- Expected number of distinct coordinates queried by `T`: `Δ(T) = ∑_i δ_i(T)`. -/
def expectedQueries [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (T : ProdDecisionTree X Z) : ℝ :=
  ∑ i : ι, revealment μ i T

/-- Expected number of distinct coordinates queried by `𝒯`: `Δ(𝒯) = ∑_i δ_i(𝒯)`. -/
noncomputable def expectedQueriesRDT [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (𝒯 : ProdRDT X Z) : ℝ :=
  ∑ i : ι, revealmentRDT μ i 𝒯

theorem revealment_eq_prodExpect [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (T : ProdDecisionTree X Z) :
    revealment μ i T = prodExpect μ fun x => if i ∈ T.queries x then 1 else 0 := by rfl

theorem expectedQueries_eq_sum [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (T : ProdDecisionTree X Z) :
    expectedQueries μ T = ∑ i : ι, revealment μ i T := by rfl

theorem sum_revealmentRDT_eq_expectedQueriesRDT [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (𝒯 : ProdRDT X Z) :
    ∑ i : ι, revealmentRDT μ i 𝒯 = expectedQueriesRDT μ 𝒯 := by rfl

theorem revealment_nonneg [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (T : ProdDecisionTree X Z) :
    0 ≤ revealment μ i T :=
  prodExpect_nonneg μ fun _ => by split_ifs <;> norm_num

theorem revealment_le_one [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (T : ProdDecisionTree X Z) :
    revealment μ i T ≤ 1 := by
  calc revealment μ i T ≤ prodExpect μ (fun _ => 1) :=
        prodExpect_mono μ fun _ => by split_ifs <;> norm_num
    _ = 1 := prodExpect_const μ 1

theorem revealmentRDT_nonneg [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (𝒯 : ProdRDT X Z) :
    0 ≤ revealmentRDT μ i 𝒯 :=
  Finset.sum_nonneg fun T _ => mul_nonneg (𝒯.nonneg T) (revealment_nonneg μ i T)

theorem expectedQueriesRDT_nonneg [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (𝒯 : ProdRDT X Z) :
    0 ≤ expectedQueriesRDT μ 𝒯 :=
  Finset.sum_nonneg fun i _ => revealmentRDT_nonneg μ i 𝒯

theorem expectedQueries_eq_expect_card [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (T : ProdDecisionTree X Z) :
    expectedQueries μ T = prodExpect μ fun x => ((T.queries x).card : ℝ) := by
  simp only [expectedQueries, revealment, ← prodExpect_sum]
  refine congrArg (prodExpect μ) (funext fun x => ?_)
  simp

theorem sum_revealmentRDT_mul [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (𝒯 : ProdRDT X Z) (g : ι → ℝ) :
    ∑ i : ι, revealmentRDT μ i 𝒯 * g i =
      𝒯.weights.sum fun T w => w * ∑ i : ι, revealment μ i T * g i := by
  simp only [revealmentRDT, Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem revealment_prune_empty [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (T : ProdDecisionTree X Z) :
    revealment μ i (T.prune fun _ => none) = revealment μ i T := by
  simp only [revealment, ProdDecisionTree.queries_prune_empty]

@[simp]
theorem revealment_leaf [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι) (z : Z) :
    revealment μ i (ProdDecisionTree.leaf z : ProdDecisionTree X Z) = 0 := by
  simp [revealment, prodExpect]

theorem revealment_node_self [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (i : ι)
    (c : X i → ProdDecisionTree X Z) :
    revealment μ i (ProdDecisionTree.node i c) = 1 := by
  simp [revealment, prodExpect_const]

theorem revealment_eq_zero_of_notMem_allQueries [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) {i : ι} {T : ProdDecisionTree X Z}
    (hi : i ∉ T.allQueries) : revealment μ i T = 0 := by
  have hzero : (fun x => if i ∈ T.queries x then (1 : ℝ) else 0) = fun _ => 0 :=
    funext fun x => ite_eq_right fun h =>
      (hi (ProdDecisionTree.queries_subset_allQueries T x h)).elim
  rw [revealment, hzero, prodExpect_const]

theorem revealment_node_ne [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) {i j : ι} (hji : j ≠ i)
    (c : X i → ProdDecisionTree X Z) (hc : ∀ a, i ∉ (c a).allQueries) :
    revealment μ j (ProdDecisionTree.node i c) =
      ∑ a : X i, (μ i).weights a * revealment μ j (c a) := by
  rw [revealment, ← prodExpect_update μ i]
  refine sum_congr rfl fun a _ => congrArg ((μ i).weights a * ·) ?_
  refine congrArg (prodExpect μ) (funext fun x => ?_)
  simp only [ProdDecisionTree.queries_node, Function.update_self, Finset.mem_insert, hji,
    false_or]
  rw [ProdDecisionTree.queries_update_of_notMem_allQueries (hc a)]

/-- Variation `𝔼_{x, y ← μ}[ρ(f x, f y)]` of `f` on a finite product probability space. -/
def variation [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (f : (∀ i : ι, X i) → Z) : ℝ :=
  prodExpect μ fun x => prodExpect μ fun y => ρ.dist (f x) (f y)

theorem variation_eq_prodExpect [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z) (f : (∀ i : ι, X i) → Z) :
    variation μ ρ f = prodExpect μ fun x => prodExpect μ fun y => ρ.dist (f x) (f y) := by rfl

/-- Covariation `𝔼_{x, y ← μ}[ρ(f x, g y)] - 𝔼_{x ← μ}[ρ(f x, g x)]`. -/
def covariation [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (f g : (∀ i : ι, X i) → Z) : ℝ :=
  (prodExpect μ fun x => prodExpect μ fun y => ρ.dist (f x) (g y)) -
    prodExpect μ fun x => ρ.dist (f x) (g x)

theorem covariation_eq_prodExpect [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z) (f g : (∀ i : ι, X i) → Z) :
    covariation μ ρ f g =
      (prodExpect μ fun x => prodExpect μ fun y => ρ.dist (f x) (g y)) -
        prodExpect μ fun x => ρ.dist (f x) (g x) := by rfl

/-- Coordinate influence `𝔼_{x, a ← μ_i}[ρ(f x, f (update x i a))]` of coordinate `i`. -/
def prodInfluence [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (i : ι) (f : (∀ j : ι, X j) → Z) : ℝ :=
  prodExpect μ fun x => ∑ a : X i, (μ i).weights a * ρ.dist (f x) (f (Function.update x i a))

theorem prodInfluence_eq_prodExpect [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (i : ι) (f : (∀ j : ι, X j) → Z) :
    prodInfluence μ ρ i f =
      prodExpect μ fun x =>
        ∑ a : X i, (μ i).weights a * ρ.dist (f x) (f (Function.update x i a)) := by rfl

/-- Total coordinate influence `∑_i Inf_i(f)`. -/
def totalProdInfluence [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (f : (∀ j : ι, X j) → Z) : ℝ :=
  ∑ i : ι, prodInfluence μ ρ i f

/-- Maximum coordinate influence `max_i Inf_i(f)` (and `0` on an empty coordinate index type). -/
noncomputable def maxProdInfluence [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (f : (∀ j : ι, X j) → Z) : ℝ :=
  Finset.univ.fold max 0 (fun i => prodInfluence μ ρ i f)

private theorem le_fold_max_of_mem {α : Type*} (s : Finset α) (g : α → ℝ)
    {a : α} (ha : a ∈ s) : g a ≤ s.fold max 0 g := by
  classical
  induction s using Finset.induction with
  | empty => exact (Finset.notMem_empty a ha).elim
  | insert b t hb ih =>
    rw [Finset.fold_insert hb]
    rcases Finset.mem_insert.mp ha with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

theorem prodInfluence_nonneg [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (i : ι) (f : (∀ j : ι, X j) → Z) : 0 ≤ prodInfluence μ ρ i f :=
  prodExpect_nonneg μ fun _ =>
    sum_nonneg fun a _ => mul_nonneg ((μ i).nonneg a) (ρ.dist_nonneg _ _)

theorem prodInfluence_le_maxProdInfluence [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (i : ι) (f : (∀ j : ι, X j) → Z) :
    prodInfluence μ ρ i f ≤ maxProdInfluence μ ρ f :=
  le_fold_max_of_mem Finset.univ (fun j => prodInfluence μ ρ j f) (Finset.mem_univ i)

theorem maxProdInfluence_nonneg [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (f : (∀ j : ι, X j) → Z) : 0 ≤ maxProdInfluence μ ρ f := by
  unfold maxProdInfluence
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.fold_insert hj]
    exact le_max_of_le_right ih

theorem maxProdInfluence_eq_fold [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    (f : (∀ j : ι, X j) → Z) :
    maxProdInfluence μ ρ f = Finset.univ.fold max 0 (fun i => prodInfluence μ ρ i f) := by rfl

end ProductMeasures

/-! ### Hybrid coupling and product-space revealment inequalities -/

section Hybrid

variable {ι : Type*} {X : ι → Type*} {Z : Type*}

/-- Initial hybrid point agreeing with `x` on the coordinates queried by `T` on `x` and with `y`
on all remaining coordinates. -/
@[expose]
def hybridU0 [DecidableEq ι] :
    ProdDecisionTree X Z → (∀ i : ι, X i) → (∀ i : ι, X i) → (∀ i : ι, X i)
  | .leaf _, _, y => y
  | .node i c, x, y => Function.update (hybridU0 (c (x i)) x y) i (x i)

@[simp]
theorem hybridU0_leaf [DecidableEq ι] (z : Z) (x y : ∀ i : ι, X i) :
    hybridU0 (.leaf z : ProdDecisionTree X Z) x y = y := rfl

@[simp]
theorem hybridU0_node [DecidableEq ι] (i : ι) (c : X i → ProdDecisionTree X Z)
    (x y : ∀ j : ι, X j) :
    hybridU0 (.node i c) x y = Function.update (hybridU0 (c (x i)) x y) i (x i) := rfl

theorem hybridU0_update_left_of_notMem_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    {T : ProdDecisionTree X Z} {i : ι} (hi : i ∉ T.allQueries)
    (x y : ∀ j : ι, X j) (a : X i) :
    hybridU0 T (Function.update x i a) y = hybridU0 T x y := by
  induction T with
  | leaf _ => rfl
  | node j c ih =>
    have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j _)
    have hic : i ∉ (c (x j)).allQueries := fun h =>
      hi (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x j, Finset.mem_univ _, h⟩))
    simp only [hybridU0_node, Function.update_of_ne hji]
    rw [ih (x j) hic]

theorem hybridU0_update_right_of_notMem_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    {T : ProdDecisionTree X Z} {i : ι} (hi : i ∉ T.allQueries)
    (x y : ∀ j : ι, X j) (b : X i) :
    hybridU0 T x (Function.update y i b) = Function.update (hybridU0 T x y) i b := by
  induction T with
  | leaf _ => rfl
  | node j c ih =>
    have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j _)
    have hic : i ∉ (c (x j)).allQueries := fun h =>
      hi (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x j, Finset.mem_univ _, h⟩))
    rw [hybridU0_node, hybridU0_node, ih (x j) hic, Function.update_comm hji.symm]

theorem hybridU0_agrees_queries [DecidableEq ι] (T : ProdDecisionTree X Z)
    (x y : ∀ i : ι, X i) {j : ι} (hj : j ∈ T.queries x) : hybridU0 T x y j = x j := by
  induction T with
  | leaf _ => simp at hj
  | node i _ ih =>
    simp only [ProdDecisionTree.queries_node, Finset.mem_insert] at hj
    rw [hybridU0_node]
    rcases hj with rfl | hj
    · simp
    · by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]; exact ih (x i) hj

theorem eval_hybridU0 [DecidableEq ι] (T : ProdDecisionTree X Z) (x y : ∀ i : ι, X i) :
    T.eval (hybridU0 T x y) = T.eval x :=
  ProdDecisionTree.eval_eq_of_forall_mem_queries T fun _ hj => hybridU0_agrees_queries T x y hj

/-- For a repetition-free tree `T`, `hybridU0 T x y` has marginal distribution `μ` under
independent draws `x, y ← μ`. -/
theorem prodExpect_hybridU0 [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) {T : ProdDecisionTree X Z} (hT : T.NoRepeat)
    (h : (∀ i : ι, X i) → ℝ) :
    prodExpect μ (fun x => prodExpect μ fun y => h (hybridU0 T x y)) = prodExpect μ h := by
  induction T generalizing h with
  | leaf _ =>
    simp only [hybridU0_leaf, prodExpect_const]
  | node i c ih =>
    rw [← prodExpect_prodExpect_update_left μ i]
    have hstep (a : X i) :
        prodExpect μ (fun x => prodExpect μ fun y =>
          h (hybridU0 (.node i c) (Function.update x i a) y)) =
        prodExpect μ fun z => h (Function.update z i a) := by
      have hcongr :
          (fun x => prodExpect μ fun y =>
            h (hybridU0 (.node i c) (Function.update x i a) y)) =
          (fun x => prodExpect μ fun y =>
            h (Function.update (hybridU0 (c a) x y) i a)) := by
        funext x
        refine congrArg (prodExpect μ) (funext fun y => ?_)
        simp only [hybridU0_node, Function.update_self]
        rw [hybridU0_update_left_of_notMem_allQueries (hT a).2]
      rw [hcongr]
      exact ih a (hT a).1 (fun z => h (Function.update z i a))
    simp_rw [hstep]
    exact prodExpect_update μ i h

/-- Sum of step distances of `g` along the hybrid coupling path of `T` on `(x, y)`. -/
@[expose]
def hybridSum [DecidableEq ι] (ρ : Semimetric Z) (g : (∀ i : ι, X i) → Z) :
    ProdDecisionTree X Z → (∀ i : ι, X i) → (∀ i : ι, X i) → ℝ
  | .leaf _, _, _ => 0
  | .node i c, x, y =>
      ρ.dist (g (hybridU0 (.node i c) x y)) (g (hybridU0 (c (x i)) x y)) +
        hybridSum ρ g (c (x i)) x y

@[simp]
theorem hybridSum_leaf [DecidableEq ι] (ρ : Semimetric Z) (g : (∀ i : ι, X i) → Z)
    (z : Z) (x y : ∀ i : ι, X i) : hybridSum ρ g (.leaf z) x y = 0 := rfl

@[simp]
theorem hybridSum_node [DecidableEq ι] (ρ : Semimetric Z) (g : (∀ i : ι, X i) → Z)
    (i : ι) (c : X i → ProdDecisionTree X Z) (x y : ∀ j : ι, X j) :
    hybridSum ρ g (.node i c) x y =
      ρ.dist (g (hybridU0 (.node i c) x y)) (g (hybridU0 (c (x i)) x y)) +
        hybridSum ρ g (c (x i)) x y := rfl

private theorem hybridSum_update_of_notMem_allQueries [DecidableEq ι] [∀ i, Fintype (X i)]
    (ρ : Semimetric Z) (g : (∀ i : ι, X i) → Z) {T : ProdDecisionTree X Z} {i : ι}
    (hi : i ∉ T.allQueries) (x y : ∀ j : ι, X j) (a b : X i) :
    hybridSum ρ g T (Function.update x i a) (Function.update y i b) =
      hybridSum ρ (fun z => g (Function.update z i b)) T x y := by
  induction T with
  | leaf _ => rfl
  | node j c ih =>
    have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j _)
    have hic : i ∉ (c (x j)).allQueries := fun h =>
      hi (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x j, Finset.mem_univ _, h⟩))
    simp only [hybridSum_node, Function.update_of_ne hji]
    rw [hybridU0_update_left_of_notMem_allQueries hi,
      hybridU0_update_right_of_notMem_allQueries hi,
      hybridU0_update_left_of_notMem_allQueries hic,
      hybridU0_update_right_of_notMem_allQueries hic, ih (x j) hic]

private theorem sum_prodInfluence_update_eq [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z)
    {i j : ι} (hji : j ≠ i) (g : (∀ k : ι, X k) → Z) :
    ∑ b : X i, (μ i).weights b * prodInfluence μ ρ j (fun z => g (Function.update z i b)) =
      prodInfluence μ ρ j g := by
  have hcomm (z : ∀ k : ι, X k) (b : X i) (c : X j) :
      Function.update (Function.update z j c) i b = Function.update (Function.update z i b) j c :=
    Function.update_comm hji _ _ _
  simp only [prodInfluence_eq_prodExpect]
  simp_rw [hcomm]
  exact prodExpect_update μ i fun z => ∑ c : X j, (μ j).weights c *
    ρ.dist (g z) (g (Function.update z j c))

/-- Exact expectation identity along the hybrid trajectory: for every repetition-free decision
tree `T`, `𝔼_{x, y}[hybridSum ρ g T x y] = ∑ j, δ_j(T) · Inf_j(g)`. -/
theorem prodExpect_hybridSum [Fintype ι] [∀ i, Fintype (X i)] [DecidableEq ι]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (ρ : Semimetric Z) (g : (∀ i : ι, X i) → Z)
    {T : ProdDecisionTree X Z} (hT : T.NoRepeat) :
    prodExpect μ (fun x => prodExpect μ fun y => hybridSum ρ g T x y) =
      ∑ j : ι, revealment μ j T * prodInfluence μ ρ j g := by
  induction T generalizing g with
  | leaf _ =>
    simp [hybridSum_leaf]
  | node i c ih =>
    simp only [hybridSum_node, prodExpect_add]
    have hterm1 :
        prodExpect μ (fun x => prodExpect μ fun y =>
          ρ.dist (g (hybridU0 (.node i c) x y)) (g (hybridU0 (c (x i)) x y))) =
        revealment μ i (.node i c) * prodInfluence μ ρ i g := by
      rw [revealment_node_self, one_mul, ← prodExpect_prodExpect_update_left μ i]
      have hinner (a : X i) :
          prodExpect μ (fun x => prodExpect μ fun y =>
            ρ.dist (g (hybridU0 (.node i c) (Function.update x i a) y))
              (g (hybridU0 (c (Function.update x i a i)) (Function.update x i a) y))) =
          ∑ b : X i, (μ i).weights b *
            prodExpect μ (fun z =>
              ρ.dist (g (Function.update z i a)) (g (Function.update z i b))) := by
        rw [← prodExpect_prodExpect_update_right μ i]
        refine sum_congr rfl fun b _ => congrArg ((μ i).weights b * ·) ?_
        have hcongr :
            (fun x => prodExpect μ fun y =>
              ρ.dist (g (hybridU0 (.node i c) (Function.update x i a) (Function.update y i b)))
                (g (hybridU0 (c (Function.update x i a i)) (Function.update x i a)
                  (Function.update y i b)))) =
            (fun x => prodExpect μ fun y =>
              ρ.dist (g (Function.update (hybridU0 (c a) x y) i a))
                (g (Function.update (hybridU0 (c a) x y) i b))) := by
          funext x
          refine congrArg (prodExpect μ) (funext fun y => ?_)
          simp only [hybridU0_node, Function.update_self]
          rw [hybridU0_update_left_of_notMem_allQueries (hT a).2,
            hybridU0_update_right_of_notMem_allQueries (hT a).2, Function.update_idem]
        rw [hcongr]
        exact prodExpect_hybridU0 μ (hT a).1
          (fun z => ρ.dist (g (Function.update z i a)) (g (Function.update z i b)))
      simp_rw [hinner]
      have hswap :
          ∑ a : X i, (μ i).weights a * ∑ b : X i, (μ i).weights b *
              prodExpect μ (fun z =>
                ρ.dist (g (Function.update z i a)) (g (Function.update z i b))) =
          ∑ b : X i, (μ i).weights b * prodExpect μ (fun z =>
              ∑ a : X i, (μ i).weights a *
                ρ.dist (g (Function.update z i b)) (g (Function.update z i a))) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun b _ => ?_
        rw [prodExpect_sum]
        simp_rw [prodExpect_const_mul, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        simp_rw [ρ.dist_comm]
        ring
      rw [hswap, prodInfluence_eq_prodExpect]
      simpa only [Function.update_idem] using prodExpect_update μ i fun z =>
        ∑ a : X i, (μ i).weights a * ρ.dist (g z) (g (Function.update z i a))
    have hterm2 :
        prodExpect μ (fun x => prodExpect μ fun y => hybridSum ρ g (c (x i)) x y) =
        ∑ j ∈ Finset.univ.erase i, revealment μ j (.node i c) * prodInfluence μ ρ j g := by
      rw [← prodExpect_prodExpect_update_left μ i]
      have hinner (a : X i) :
          prodExpect μ (fun x => prodExpect μ fun y =>
            hybridSum ρ g (c (Function.update x i a i)) (Function.update x i a) y) =
          ∑ b : X i, (μ i).weights b *
            ∑ j : ι, revealment μ j (c a) *
              prodInfluence μ ρ j (fun z => g (Function.update z i b)) := by
        rw [← prodExpect_prodExpect_update_right μ i]
        refine sum_congr rfl fun b _ => congrArg ((μ i).weights b * ·) ?_
        simp only [Function.update_self]
        have hcongr :
            (fun x => prodExpect μ fun y =>
              hybridSum ρ g (c a) (Function.update x i a) (Function.update y i b)) =
            (fun x => prodExpect μ fun y =>
              hybridSum ρ (fun z => g (Function.update z i b)) (c a) x y) := by
          funext x
          exact congrArg (prodExpect μ) (funext fun y =>
            hybridSum_update_of_notMem_allQueries ρ g (hT a).2 x y a b)
        rw [hcongr]
        exact ih a (fun z => g (Function.update z i b)) (hT a).1
      simp_rw [hinner]
      have hfact :
          ∑ a : X i, (μ i).weights a * ∑ b : X i, (μ i).weights b *
              ∑ j : ι, revealment μ j (c a) *
                prodInfluence μ ρ j (fun z => g (Function.update z i b)) =
          ∑ j : ι, (∑ a : X i, (μ i).weights a * revealment μ j (c a)) *
              (∑ b : X i, (μ i).weights b *
                prodInfluence μ ρ j (fun z => g (Function.update z i b))) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine (sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
        rw [sum_comm]
        refine sum_congr rfl fun _ _ => ?_
        refine sum_congr rfl fun _ _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun _ _ => by ring
      rw [hfact, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hi0 : (∑ a : X i, (μ i).weights a * revealment μ i (c a)) = 0 := by
        refine sum_eq_zero fun a _ => ?_
        rw [revealment_eq_zero_of_notMem_allQueries μ (hT a).2, mul_zero]
      rw [hi0, zero_mul, zero_add]
      refine sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [revealment_node_ne μ hji c (fun a => (hT a).2),
        sum_prodInfluence_update_eq μ ρ hji g]
    rw [hterm1, hterm2,
      Finset.add_sum_erase Finset.univ
        (fun j => revealment μ j (.node i c) * prodInfluence μ ρ j g) (Finset.mem_univ i)]

theorem dist_hybridU0_le_hybridSum [DecidableEq ι] [PseudoMetricSpace Z]
    (g : (∀ i : ι, X i) → Z) (T : ProdDecisionTree X Z) (x y : ∀ i : ι, X i) :
    dist (g (hybridU0 T x y)) (g y) ≤
      hybridSum (Semimetric.ofPseudoMetricSpace Z) g T x y := by
  induction T with
  | leaf _ => simp [hybridU0_leaf, hybridSum_leaf]
  | node i c ih =>
    rw [hybridSum_node, Semimetric.ofPseudoMetricSpace_dist]
    exact (dist_triangle _ (g (hybridU0 (c (x i)) x y)) _).trans
      (add_le_add le_rfl (ih (x i)))

end Hybrid

section ProductInequalities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type*} [∀ i, Fintype (X i)]

/-- For any function from a finite product probability space into a pseudo-metric space and any
deterministic decision tree `T` computing `f`, variation is at most the revealment-weighted sum of
coordinate influences. -/
theorem variation_le_sum_revealment_mul_prodInfluence {Z : Type*} [PseudoMetricSpace Z]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f : (∀ i : ι, X i) → Z)
    (T : ProdDecisionTree X Z) (hT : T.Computes f) :
    variation μ (Semimetric.ofPseudoMetricSpace Z) f ≤
      ∑ i : ι, revealment μ i T * prodInfluence μ (Semimetric.ofPseudoMetricSpace Z) i f := by
  let P := T.prune (fun _ => none)
  have hP_no : P.NoRepeat := ProdDecisionTree.noRepeat_prune T _
  have hP_comp : P.Computes f := fun x => (ProdDecisionTree.eval_prune_empty T x).trans (hT x)
  have hP_rev : ∀ i, revealment μ i P = revealment μ i T := fun i => revealment_prune_empty μ i T
  simp_rw [← hP_rev, ← prodExpect_hybridSum μ (Semimetric.ofPseudoMetricSpace Z) f hP_no]
  have hvar :
      variation μ (Semimetric.ofPseudoMetricSpace Z) f =
        prodExpect μ (fun x => prodExpect μ fun y => dist (f (hybridU0 P x y)) (f y)) := by
    rw [variation_eq_prodExpect]
    refine congrArg (prodExpect μ) (funext fun x => congrArg (prodExpect μ) (funext fun y => ?_))
    rw [← hP_comp x, ← hP_comp (hybridU0 P x y), eval_hybridU0]
    exact Semimetric.ofPseudoMetricSpace_dist Z _ _
  rw [hvar]
  exact prodExpect_mono μ fun x => prodExpect_mono μ fun y => dist_hybridU0_le_hybridSum f P x y

/-- Zero-error randomized decision tree version of the product-space revealment inequality. -/
theorem variation_le_sum_revealmentRDT_mul_prodInfluence {Z : Type*} [PseudoMetricSpace Z]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f : (∀ i : ι, X i) → Z)
    (𝒯 : ProdRDT X Z) (h𝒯 : 𝒯.Computes f) :
    variation μ (Semimetric.ofPseudoMetricSpace Z) f ≤
      ∑ i : ι, revealmentRDT μ i 𝒯 * prodInfluence μ (Semimetric.ofPseudoMetricSpace Z) i f := by
  rw [sum_revealmentRDT_mul]
  calc variation μ (Semimetric.ofPseudoMetricSpace Z) f
      = 𝒯.weights.sum fun _ w => w * variation μ (Semimetric.ofPseudoMetricSpace Z) f := by
        rw [← Finsupp.sum_mul, 𝒯.total, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun T hT =>
        mul_le_mul_of_nonneg_left
          (variation_le_sum_revealment_mul_prodInfluence μ f T (h𝒯 T hT)) (𝒯.nonneg T)

/-- Two-function revealment inequality on a pseudo-metric space: for any zero-error randomized
decision tree `𝒯` computing `f` and any function `g`, `|CoVr[f, g]|` is at most the
`𝒯`-revealment-weighted sum of coordinate influences of `g`. -/
theorem abs_covariation_le_sum_revealmentRDT_mul_prodInfluence {Z : Type*} [PseudoMetricSpace Z]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f g : (∀ i : ι, X i) → Z)
    (𝒯 : ProdRDT X Z) (h𝒯 : 𝒯.Computes f) :
    |covariation μ (Semimetric.ofPseudoMetricSpace Z) f g| ≤
      ∑ i : ι, revealmentRDT μ i 𝒯 * prodInfluence μ (Semimetric.ofPseudoMetricSpace Z) i g := by
  have hddt (T : ProdDecisionTree X Z) (hT : T.Computes f) :
      |covariation μ (Semimetric.ofPseudoMetricSpace Z) f g| ≤
        ∑ i : ι, revealment μ i T * prodInfluence μ (Semimetric.ofPseudoMetricSpace Z) i g := by
    let P := T.prune (fun _ => none)
    have hP_no : P.NoRepeat := ProdDecisionTree.noRepeat_prune T _
    have hP_comp : P.Computes f := fun x => (ProdDecisionTree.eval_prune_empty T x).trans (hT x)
    have hP_rev : ∀ i, revealment μ i P = revealment μ i T := fun i => revealment_prune_empty μ i T
    simp_rw [← hP_rev, ← prodExpect_hybridSum μ (Semimetric.ofPseudoMetricSpace Z) g hP_no]
    have hcov :
        covariation μ (Semimetric.ofPseudoMetricSpace Z) f g =
          prodExpect μ (fun x => prodExpect μ fun y =>
            dist (f (hybridU0 P x y)) (g y) - dist (f (hybridU0 P x y)) (g (hybridU0 P x y))) := by
      rw [covariation_eq_prodExpect]
      simp only [Semimetric.ofPseudoMetricSpace_dist]
      rw [← prodExpect_hybridU0 μ hP_no (fun z => dist (f z) (g z))]
      simp_rw [← prodExpect_sub]
      refine congrArg (prodExpect μ) (funext fun x => congrArg (prodExpect μ) (funext fun y => ?_))
      have hfx : f (hybridU0 P x y) = f x := by
        rw [← hP_comp x, ← hP_comp (hybridU0 P x y), eval_hybridU0]
      rw [hfx]
    rw [hcov]
    calc |prodExpect μ fun x => prodExpect μ fun y =>
            dist (f (hybridU0 P x y)) (g y) - dist (f (hybridU0 P x y)) (g (hybridU0 P x y))|
        ≤ prodExpect μ fun x => |prodExpect μ fun y =>
            dist (f (hybridU0 P x y)) (g y) - dist (f (hybridU0 P x y)) (g (hybridU0 P x y))| :=
          abs_prodExpect_le μ _
      _ ≤ prodExpect μ fun x => prodExpect μ fun y =>
            |dist (f (hybridU0 P x y)) (g y) - dist (f (hybridU0 P x y)) (g (hybridU0 P x y))| :=
          prodExpect_mono μ fun x => abs_prodExpect_le μ _
      _ ≤ prodExpect μ fun x => prodExpect μ fun y => dist (g (hybridU0 P x y)) (g y) :=
          prodExpect_mono μ fun x => prodExpect_mono μ fun y => by
            rw [dist_comm (f (hybridU0 P x y)) (g y),
              dist_comm (f (hybridU0 P x y)) (g (hybridU0 P x y)), abs_sub_comm]
            exact abs_dist_sub_le (g (hybridU0 P x y)) (g y) (f (hybridU0 P x y))
      _ ≤ prodExpect μ fun x => prodExpect μ fun y =>
            hybridSum (Semimetric.ofPseudoMetricSpace Z) g P x y :=
          prodExpect_mono μ fun x => prodExpect_mono μ fun y => dist_hybridU0_le_hybridSum g P x y
  rw [sum_revealmentRDT_mul]
  calc |covariation μ (Semimetric.ofPseudoMetricSpace Z) f g|
      = 𝒯.weights.sum fun _ w => w * |covariation μ (Semimetric.ofPseudoMetricSpace Z) f g| := by
        rw [← Finsupp.sum_mul, 𝒯.total, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun T hT =>
        mul_le_mul_of_nonneg_left (hddt T (h𝒯 T hT)) (𝒯.nonneg T)

private theorem covariation_ge_variation_sub_two_mul {Z : Type*} [PseudoMetricSpace Z]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f g : (∀ i : ι, X i) → Z) :
    variation μ (Semimetric.ofPseudoMetricSpace Z) g -
        2 * prodExpect μ (fun x => dist (f x) (g x)) ≤
      covariation μ (Semimetric.ofPseudoMetricSpace Z) f g := by
  rw [variation_eq_prodExpect, covariation_eq_prodExpect]
  have h1 :
      prodExpect μ (fun x => prodExpect μ fun y => dist (g x) (g y)) ≤
        prodExpect μ (fun x => prodExpect μ fun y => dist (g x) (f x) + dist (f x) (g y)) :=
    prodExpect_mono μ fun x => prodExpect_mono μ fun y => dist_triangle (g x) (f x) (g y)
  have h2 :
      prodExpect μ (fun x => prodExpect μ fun y => dist (g x) (f x) + dist (f x) (g y)) =
        prodExpect μ (fun x => dist (f x) (g x)) +
          prodExpect μ (fun x => prodExpect μ fun y => dist (f x) (g y)) := by
    simp_rw [prodExpect_add, prodExpect_const, dist_comm (g _) (f _)]
  simp only [Semimetric.ofPseudoMetricSpace_dist]
  linarith

/-- Expected query-complexity lower bound for any randomized decision tree computing an
`ε`-approximation `f` to `g` in expected distance. -/
theorem expectedQueriesRDT_ge_of_approx {Z : Type*} [PseudoMetricSpace Z]
    (μ : ∀ i : ι, Convexity.StdSimplex ℝ (X i)) (f g : (∀ i : ι, X i) → Z)
    (𝒯 : ProdRDT X Z) (h𝒯 : 𝒯.Computes f) {ε : ℝ}
    (hε : prodExpect μ (fun x => dist (f x) (g x)) ≤ ε) :
    (variation μ (Semimetric.ofPseudoMetricSpace Z) g - 2 * ε) /
        maxProdInfluence μ (Semimetric.ofPseudoMetricSpace Z) g ≤
      expectedQueriesRDT μ 𝒯 := by
  have hle :
      variation μ (Semimetric.ofPseudoMetricSpace Z) g - 2 * ε ≤
        maxProdInfluence μ (Semimetric.ofPseudoMetricSpace Z) g * expectedQueriesRDT μ 𝒯 := by
    calc variation μ (Semimetric.ofPseudoMetricSpace Z) g - 2 * ε
        ≤ variation μ (Semimetric.ofPseudoMetricSpace Z) g -
            2 * prodExpect μ (fun x => dist (f x) (g x)) := by linarith
      _ ≤ covariation μ (Semimetric.ofPseudoMetricSpace Z) f g :=
          covariation_ge_variation_sub_two_mul μ f g
      _ ≤ |covariation μ (Semimetric.ofPseudoMetricSpace Z) f g| := le_abs_self _
      _ ≤ ∑ i : ι, revealmentRDT μ i 𝒯 *
            prodInfluence μ (Semimetric.ofPseudoMetricSpace Z) i g :=
          abs_covariation_le_sum_revealmentRDT_mul_prodInfluence μ f g 𝒯 h𝒯
      _ ≤ ∑ i : ι, revealmentRDT μ i 𝒯 *
            maxProdInfluence μ (Semimetric.ofPseudoMetricSpace Z) g :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (prodInfluence_le_maxProdInfluence μ _ i g) (revealmentRDT_nonneg μ i 𝒯)
      _ = maxProdInfluence μ (Semimetric.ofPseudoMetricSpace Z) g * expectedQueriesRDT μ 𝒯 := by
          rw [← sum_mul, mul_comm, sum_revealmentRDT_eq_expectedQueriesRDT]
  by_cases hm : maxProdInfluence μ (Semimetric.ofPseudoMetricSpace Z) g = 0
  · rw [hm, div_zero]
    exact expectedQueriesRDT_nonneg μ 𝒯
  · have hm_pos : 0 < maxProdInfluence μ (Semimetric.ofPseudoMetricSpace Z) g :=
      lt_of_le_of_ne (maxProdInfluence_nonneg μ _ g) (Ne.symm hm)
    rw [div_le_iff₀ hm_pos]
    linarith

end ProductInequalities

/-! ### `p`-biased Boolean revealment, monotone total influence, and randomized query bounds -/

section BooleanRevealment

variable {ι : Type*}

/-- Order-preserving `{-1, 1}` encoding of `Bool`: `false ↦ -1` and `true ↦ 1`. -/
@[expose]
def boolVal (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem boolVal_false : boolVal false = -1 := rfl
@[simp] theorem boolVal_true : boolVal true = 1 := rfl

theorem boolVal_sq (b : Bool) : boolVal b ^ 2 = 1 := by cases b <;> norm_num

theorem boolVal_eq_neg_signVal (b : Bool) : boolVal b = -Cslib.BitString.signVal b := by
  cases b <;> simp [boolVal]

theorem abs_boolVal_sub (b b' : Bool) :
    |boolVal b - boolVal b'| = Semimetric.discreteBool.dist b b' := by
  cases b <;> cases b' <;> norm_num [boolVal, Semimetric.discreteBool_dist]

variable [Fintype ι] [DecidableEq ι]

/-- `p`-biased variance `1 - (𝔼_p[boolVal ∘ f])²` of a Boolean function `f : (ι → Bool) → Bool`. -/
def boolVariance (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  1 - (Cslib.BitString.bernoulliAverage p fun x => boolVal (f x)) ^ 2

theorem boolVariance_eq_variation {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) :
    boolVariance p f =
      variation (bernoulliCoordFamily ι hp0 hp1) Semimetric.discreteBool f := by
  have hdist (b b' : Bool) :
      Semimetric.discreteBool.dist b b' = (boolVal b - boolVal b') ^ 2 / 2 := by
    cases b <;> cases b' <;> norm_num [boolVal, Semimetric.discreteBool_dist]
  simp only [variation_eq_prodExpect, hdist]
  have hexp (x : ι → Bool) :
      prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun y => (boolVal (f x) - boolVal (f y)) ^ 2 / 2)
        = (1 : ℝ) - boolVal (f x) *
            prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun y => boolVal (f y)) := by
    have hpt : (fun y => (boolVal (f x) - boolVal (f y)) ^ 2 / 2) =
        fun y => (1 : ℝ) - boolVal (f x) * boolVal (f y) := by
      funext y
      have hx2 := boolVal_sq (f x)
      have hy2 := boolVal_sq (f y)
      nlinarith
    rw [hpt, prodExpect_sub, prodExpect_const, prodExpect_const_mul]
  simp only [hexp, prodExpect_sub, prodExpect_const]
  have hmul :
      prodExpect (bernoulliCoordFamily ι hp0 hp1)
        (fun x => boolVal (f x) *
          prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun y => boolVal (f y))) =
        (prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun x => boolVal (f x))) ^ 2 := by
    have h := prodExpect_const_mul (bernoulliCoordFamily ι hp0 hp1)
      (prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun y => boolVal (f y)))
      (fun x => boolVal (f x))
    simpa [mul_comm, sq] using h
  rw [hmul, prodExpect_bernoulliCoordFamily, boolVariance]

theorem boolVariance_one_half (f : (ι → Bool) → Bool) :
    boolVariance (1 / 2) f =
      𝔼 x, (Cslib.BitString.signVal (f x) - 𝔼 y, Cslib.BitString.signVal (f y)) ^ 2 := by
  rw [Cslib.BitString.expect_sub_expect_sq_signVal, boolVariance,
    Cslib.BitString.bernoulliAverage_one_half]
  simp only [boolVal_eq_neg_signVal, Finset.expect_neg_distrib, neg_sq]

/-- `p`-biased coordinate influence `2 · Pr_{x, a ← μ_p}[f x ≠ f (update x i a)]` of coordinate `i`
on `f : (ι → Bool) → Bool`. -/
def boolInfluence (p : ℝ) (i : ι) (f : (ι → Bool) → Bool) : ℝ :=
  Cslib.BitString.bernoulliAverage p fun x =>
    (1 - p) * (if f x = f (Function.update x i false) then 0 else 2) +
      p * (if f x = f (Function.update x i true) then 0 else 2)

theorem boolInfluence_eq_prodInfluence {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) (f : (ι → Bool) → Bool) :
    boolInfluence p i f =
      prodInfluence (bernoulliCoordFamily ι hp0 hp1) Semimetric.discreteBool i f := by
  rw [boolInfluence, prodInfluence_eq_prodExpect, prodExpect_bernoulliCoordFamily]
  refine congrArg (Cslib.BitString.bernoulliAverage p) (funext fun x => ?_)
  rw [Fintype.sum_bool]
  simp only [bernoulliCoordFamily_apply, bernoulliCoordSimplex_weights_true,
    bernoulliCoordSimplex_weights_false, Semimetric.discreteBool_dist]
  ring

theorem boolInfluence_eq_four_mul_prob_flip (p : ℝ) (i : ι) (f : (ι → Bool) → Bool) :
    boolInfluence p i f =
      4 * p * (1 - p) * Cslib.BitString.bernoulliAverage p fun x =>
        if f (Function.update x i true) ≠ f (Function.update x i false) then 1 else 0 := by
  rw [boolInfluence, ← Cslib.BitString.bernoulliAverage_const_mul]
  have h1 := Cslib.BitString.sum_update_false_add_update_true i fun x =>
    Cslib.BitString.bernoulliWeight p x *
      ((1 - p) * (if f x = f (Function.update x i false) then (0 : ℝ) else 2) +
        p * (if f x = f (Function.update x i true) then 0 else 2))
  have h2 := Cslib.BitString.sum_update_false_add_update_true i fun x =>
    Cslib.BitString.bernoulliWeight p x *
      (4 * p * (1 - p) *
        if f (Function.update x i true) ≠ f (Function.update x i false) then (1 : ℝ) else 0)
  have hw (x : ι → Bool) :
      (1 - p) * Cslib.BitString.bernoulliWeight p (Function.update x i true) =
        p * Cslib.BitString.bernoulliWeight p (Function.update x i false) := by
    have hR (b : Bool) :
        ∏ j ∈ univ.erase i, (if Function.update x i b j = true then p else 1 - p) =
          ∏ j ∈ univ.erase i, (if x j = true then p else 1 - p) :=
      prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [Cslib.BitString.bernoulliWeight, Cslib.BitString.bernoulliWeight,
      ← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase univ _ (mem_univ i), hR, hR]
    simp only [Function.update_self, ite_true, Bool.false_eq_true, ite_false]
    ring
  have h3 :
      ∑ x : ι → Bool,
        (Cslib.BitString.bernoulliWeight p (Function.update x i false) *
            ((1 - p) * (if f (Function.update x i false) =
                f (Function.update (Function.update x i false) i false) then (0 : ℝ) else 2) +
              p * (if f (Function.update x i false) =
                f (Function.update (Function.update x i false) i true) then 0 else 2)) +
          Cslib.BitString.bernoulliWeight p (Function.update x i true) *
            ((1 - p) * (if f (Function.update x i true) =
                f (Function.update (Function.update x i true) i false) then (0 : ℝ) else 2) +
              p * (if f (Function.update x i true) =
                f (Function.update (Function.update x i true) i true) then 0 else 2))) =
      ∑ x : ι → Bool,
        (Cslib.BitString.bernoulliWeight p (Function.update x i false) *
            (4 * p * (1 - p) *
              if f (Function.update (Function.update x i false) i true) ≠
                f (Function.update (Function.update x i false) i false) then (1 : ℝ) else 0) +
          Cslib.BitString.bernoulliWeight p (Function.update x i true) *
            (4 * p * (1 - p) *
              if f (Function.update (Function.update x i true) i true) ≠
                f (Function.update (Function.update x i true) i false) then 1 else 0)) := by
    refine sum_congr rfl fun x _ => ?_
    simp only [Function.update_idem, ↓reduceIte, mul_zero, zero_add, add_zero]
    by_cases h : f (Function.update x i true) = f (Function.update x i false)
    · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, mul_zero, add_zero]
    · have h' : f (Function.update x i false) ≠ f (Function.update x i true) := Ne.symm h
      simp only [h, h', ne_eq, not_false_eq_true, ↓reduceIte, mul_one]
      have hwx := hw x
      linear_combination (2 - 4 * p) * hwx
  beta_reduce at h1 h2
  simp only [Cslib.BitString.bernoulliAverage]
  linarith

theorem boolInfluence_one_half (i : ι) (f : (ι → Bool) → Bool) :
    boolInfluence (1 / 2) i f =
      Cslib.BitString.influence i (fun x => Cslib.BitString.signVal (f x)) := by
  rw [boolInfluence_eq_four_mul_prob_flip, Cslib.BitString.influence_signVal,
    Cslib.BitString.bernoulliAverage_one_half]
  norm_num only
  rw [one_mul]
  refine Finset.expect_congr rfl fun x _ => ?_
  have hiff := Cslib.BitString.apply_update_false_eq_apply_update_true_iff f i x
  by_cases h : f (Function.update x i false) = f (Function.update x i true)
  · simp [h, hiff.mp h]
  · simp [Ne.symm h, mt hiff.mpr h]

/-- Total `p`-biased Boolean influence `∑_i Inf_i(f)`. -/
def boolTotalInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i : ι, boolInfluence p i f

/-- Maximum `p`-biased Boolean coordinate influence `max_i Inf_i(f)`. -/
noncomputable def boolMaxInfluence (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  Finset.univ.fold max 0 (fun i => boolInfluence p i f)

theorem boolInfluence_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι)
    (f : (ι → Bool) → Bool) : 0 ≤ boolInfluence p i f := by
  rw [boolInfluence_eq_prodInfluence hp0 hp1]
  exact prodInfluence_nonneg _ _ _ _

theorem boolInfluence_le_boolMaxInfluence (p : ℝ) (i : ι) (f : (ι → Bool) → Bool) :
    boolInfluence p i f ≤ boolMaxInfluence p f :=
  le_fold_max_of_mem Finset.univ (fun j => boolInfluence p j f) (Finset.mem_univ i)

theorem boolMaxInfluence_eq_maxProdInfluence {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) :
    boolMaxInfluence p f =
      maxProdInfluence (bernoulliCoordFamily ι hp0 hp1) Semimetric.discreteBool f := by
  simp only [boolMaxInfluence, maxProdInfluence_eq_fold, boolInfluence_eq_prodInfluence hp0 hp1]

/-- Revealment `Pr_{x ← μ_p}[i ∈ T.queries x]` of coordinate `i` for a `Cslib.DecisionTree`. -/
def revealmentBool (p : ℝ) (i : ι) {β : Type*} (T : Cslib.DecisionTree ι β) : ℝ :=
  Cslib.BitString.bernoulliAverage p fun x => if i ∈ T.queries x then 1 else 0

/-- Revealment of coordinate `i` for a `Cslib.RandomizedDecisionTree` under `μ_p`. -/
noncomputable def revealmentBoolRDT (p : ℝ) (i : ι) {β : Type*}
    (𝒯 : Cslib.RandomizedDecisionTree ι β) : ℝ :=
  𝒯.weights.sum fun T w => w * revealmentBool p i T

/-- Expected number of distinct coordinates queried by `T` under `μ_p`. -/
def expectedQueriesBool (p : ℝ) {β : Type*} (T : Cslib.DecisionTree ι β) : ℝ :=
  ∑ i : ι, revealmentBool p i T

/-- Minimum distributional expected query cost over all deterministic trees computing `f` under
the `p`-biased product distribution. -/
noncomputable def minExpectedQueriesBool {β : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → β) : ℝ :=
  Cslib.QueryComplexity.distributionalExpectedComplexity (bernoulliProductSimplex hp0 hp1) f

theorem revealmentBool_eq_revealment {β : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) (T : Cslib.DecisionTree ι β) :
    revealmentBool p i T =
      revealment (bernoulliCoordFamily ι hp0 hp1) i (ProdDecisionTree.ofCslib T) := by
  rw [revealmentBool, revealment_eq_prodExpect, prodExpect_bernoulliCoordFamily]
  simp only [ProdDecisionTree.queries_ofCslib]

theorem expectedQueriesBool_eq_expectedQueries {β : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : Cslib.DecisionTree ι β) :
    expectedQueriesBool p T =
      expectedQueries (bernoulliCoordFamily ι hp0 hp1) (ProdDecisionTree.ofCslib T) := by
  simp only [expectedQueriesBool, expectedQueries_eq_sum, revealmentBool_eq_revealment hp0 hp1]

theorem expectedQueriesBool_le_distributionalCost {β : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : Cslib.DecisionTree ι β) :
    expectedQueriesBool p T ≤ T.distributionalCost (bernoulliProductSimplex hp0 hp1) := by
  rw [expectedQueriesBool_eq_expectedQueries hp0 hp1, expectedQueries_eq_expect_card,
    Cslib.DecisionTree.distributionalCost_eq_sum, bernoulliProductSimplex_eq_prodSimplex,
    ← prodExpect_eq_simplex_sum]
  exact prodExpect_mono _ fun x => by
    rw [ProdDecisionTree.queries_ofCslib]
    exact Nat.cast_le.mpr (T.card_queries_le_cost x)

theorem expectedQueriesBool_eq_distributionalCost_of_noRepeat {β : Type*} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T : Cslib.DecisionTree ι β}
    (hT : (ProdDecisionTree.ofCslib T).NoRepeat) :
    expectedQueriesBool p T = T.distributionalCost (bernoulliProductSimplex hp0 hp1) := by
  rw [expectedQueriesBool_eq_expectedQueries hp0 hp1, expectedQueries_eq_expect_card,
    Cslib.DecisionTree.distributionalCost_eq_sum, bernoulliProductSimplex_eq_prodSimplex,
    ← prodExpect_eq_simplex_sum]
  refine congrArg (prodExpect _) (funext fun x => ?_)
  rw [ProdDecisionTree.card_queries_eq_cost_of_noRepeat hT x, ProdDecisionTree.cost_ofCslib]

theorem minExpectedQueriesBool_le_zeroErrorComplexity {β : Type*} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → β) :
    minExpectedQueriesBool hp0 hp1 f ≤ Cslib.QueryComplexity.zeroErrorComplexity f :=
  Cslib.QueryComplexity.distributionalExpectedComplexity_le_zeroErrorComplexity
    (bernoulliProductSimplex hp0 hp1) f

theorem minExpectedQueriesBool_le_expectedQueriesBool {β : Type*} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : (ι → Bool) → β} {T : Cslib.DecisionTree ι β}
    (hT : T.Computes f) : minExpectedQueriesBool hp0 hp1 f ≤ expectedQueriesBool p T := by
  let P := (ProdDecisionTree.ofCslib T).prune (fun _ => none)
  let T' := ProdDecisionTree.toCslib P
  have hT'_comp : T'.Computes f := fun x => by
    rw [ProdDecisionTree.eval_toCslib, ProdDecisionTree.eval_prune_empty,
      ProdDecisionTree.eval_ofCslib, hT x]
  have hno : (ProdDecisionTree.ofCslib T').NoRepeat := by
    rw [ProdDecisionTree.ofCslib_toCslib]
    exact ProdDecisionTree.noRepeat_prune _ _
  have hT'_eq : expectedQueriesBool p T' = expectedQueriesBool p T := by
    simp only [expectedQueriesBool, revealmentBool_eq_revealment hp0 hp1]
    refine sum_congr rfl fun i _ => ?_
    have hq : ∀ x, (ProdDecisionTree.ofCslib T').queries x =
        (ProdDecisionTree.ofCslib T).queries x := fun x => by
      rw [ProdDecisionTree.queries_ofCslib, ProdDecisionTree.queries_toCslib,
        ProdDecisionTree.queries_prune_empty]
    simp only [revealment_eq_prodExpect, hq]
  rw [← hT'_eq, expectedQueriesBool_eq_distributionalCost_of_noRepeat hp0 hp1 hno]
  exact Cslib.QueryComplexity.distributionalExpectedComplexity_le hT'_comp le_rfl

theorem exists_computes_expectedQueriesBool_eq {β : Type*} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → β) :
    ∃ T : Cslib.DecisionTree ι β,
      T.Computes f ∧ (ProdDecisionTree.ofCslib T).NoRepeat ∧
        expectedQueriesBool p T = minExpectedQueriesBool hp0 hp1 f := by
  obtain ⟨T₀, hT₀, hcost⟩ := Cslib.QueryComplexity.exists_computes_distributionalCost_eq
    (bernoulliProductSimplex hp0 hp1) f
  let P := (ProdDecisionTree.ofCslib T₀).prune (fun _ => none)
  let T := ProdDecisionTree.toCslib P
  have hT_comp : T.Computes f := fun x => by
    rw [ProdDecisionTree.eval_toCslib, ProdDecisionTree.eval_prune_empty,
      ProdDecisionTree.eval_ofCslib, hT₀ x]
  have hno : (ProdDecisionTree.ofCslib T).NoRepeat := by
    rw [ProdDecisionTree.ofCslib_toCslib]
    exact ProdDecisionTree.noRepeat_prune _ _
  have hle : expectedQueriesBool p T ≤ minExpectedQueriesBool hp0 hp1 f := by
    calc expectedQueriesBool p T
        = expectedQueriesBool p T₀ := by
          simp only [expectedQueriesBool, revealmentBool_eq_revealment hp0 hp1,
            revealment_eq_prodExpect]
          refine sum_congr rfl fun i _ => congrArg (prodExpect _) (funext fun x => ?_)
          rw [ProdDecisionTree.queries_ofCslib, ProdDecisionTree.queries_toCslib,
            ProdDecisionTree.queries_prune_empty, ProdDecisionTree.queries_ofCslib]
      _ ≤ T₀.distributionalCost (bernoulliProductSimplex hp0 hp1) :=
          expectedQueriesBool_le_distributionalCost hp0 hp1 T₀
      _ = minExpectedQueriesBool hp0 hp1 f := hcost
  exact ⟨T, hT_comp, hno,
    le_antisymm hle (minExpectedQueriesBool_le_expectedQueriesBool hp0 hp1 hT_comp)⟩

/-- For any Boolean function `f : (ι → Bool) → Bool` under `μ_p` (`p ∈ [0, 1]`) and any
deterministic decision tree `T` computing `f`, `Var_p(f) ≤ ∑_i δ_i(T) · Inf_i(f)`. -/
theorem boolVariance_le_sum_revealmentBool_mul_boolInfluence {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (T : Cslib.DecisionTree ι Bool) (hT : T.Computes f) :
    boolVariance p f ≤ ∑ i : ι, revealmentBool p i T * boolInfluence p i f := by
  let μ := bernoulliCoordFamily ι hp0 hp1
  let fR : (ι → Bool) → ℝ := fun x => boolVal (f x)
  let TR : ProdDecisionTree (fun _ : ι => Bool) ℝ := (ProdDecisionTree.ofCslib T).map boolVal
  have hTR : TR.Computes fR := fun x => by
    simp [TR, fR, ProdDecisionTree.eval_map, ProdDecisionTree.eval_ofCslib, hT x]
  have hvar : boolVariance p f = variation μ (Semimetric.ofPseudoMetricSpace ℝ) fR := by
    rw [boolVariance_eq_variation hp0 hp1, variation_eq_prodExpect, variation_eq_prodExpect]
    refine congrArg (prodExpect μ) (funext fun x => congrArg (prodExpect μ) (funext fun y => ?_))
    simpa [fR, Semimetric.ofPseudoMetricSpace_dist, Real.dist_eq] using
      (abs_boolVal_sub (f x) (f y)).symm
  have hrev (i : ι) : revealmentBool p i T = revealment μ i TR := by
    rw [revealmentBool_eq_revealment hp0 hp1, revealment_eq_prodExpect, revealment_eq_prodExpect]
    simp [TR, μ]
  have hinf (i : ι) :
      boolInfluence p i f = prodInfluence μ (Semimetric.ofPseudoMetricSpace ℝ) i fR := by
    rw [boolInfluence_eq_prodInfluence hp0 hp1, prodInfluence_eq_prodExpect,
      prodInfluence_eq_prodExpect]
    refine congrArg (prodExpect μ) (funext fun x => sum_congr rfl fun b _ => ?_)
    refine congrArg ((μ i).weights b * ·) ?_
    simpa only [fR, Semimetric.ofPseudoMetricSpace_dist, Real.dist_eq] using
      (abs_boolVal_sub (f x) (f (Function.update x i b))).symm
  rw [hvar]
  simp_rw [hrev, hinf]
  exact variation_le_sum_revealment_mul_prodInfluence μ fR TR hTR

/-- Zero-error randomized decision tree revealment inequality for `p`-biased Boolean functions. -/
theorem boolVariance_le_sum_revealmentBoolRDT_mul_boolInfluence {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (𝒯 : Cslib.RandomizedDecisionTree ι Bool) (h𝒯 : 𝒯.Computes 0 f) :
    boolVariance p f ≤ ∑ i : ι, revealmentBoolRDT p i 𝒯 * boolInfluence p i f := by
  have hsupp := Cslib.RandomizedDecisionTree.computes_zero_iff.mp h𝒯
  have hsum :
      ∑ i : ι, revealmentBoolRDT p i 𝒯 * boolInfluence p i f =
        𝒯.weights.sum fun T w => w * ∑ i : ι, revealmentBool p i T * boolInfluence p i f := by
    simp only [revealmentBoolRDT, Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [hsum]
  calc boolVariance p f
      = 𝒯.weights.sum fun _ w => w * boolVariance p f := by
        rw [← Finsupp.sum_mul, 𝒯.total, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun T hT =>
        mul_le_mul_of_nonneg_left
          (boolVariance_le_sum_revealmentBool_mul_boolInfluence hp0 hp1 f T (hsupp T hT))
          (𝒯.nonneg T)

/-- Multiplicative lower bound on distributional expected query complexity in terms of `p`-biased
variance and maximum coordinate influence: `Var_p(f) ≤ Inf_max(f) · Δ_p(f)`. -/
theorem boolVariance_le_boolMaxInfluence_mul_minExpectedQueriesBool {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) :
    boolVariance p f ≤ boolMaxInfluence p f * minExpectedQueriesBool hp0 hp1 f := by
  obtain ⟨T, hT, _, hΔ⟩ := exists_computes_expectedQueriesBool_eq hp0 hp1 f
  calc boolVariance p f
      ≤ ∑ i : ι, revealmentBool p i T * boolInfluence p i f :=
        boolVariance_le_sum_revealmentBool_mul_boolInfluence hp0 hp1 f T hT
    _ ≤ ∑ i : ι, revealmentBool p i T * boolMaxInfluence p f :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (boolInfluence_le_boolMaxInfluence p i f)
          (by rw [revealmentBool_eq_revealment hp0 hp1]; exact revealment_nonneg _ _ _)
    _ = boolMaxInfluence p f * expectedQueriesBool p T := by
        rw [← sum_mul, mul_comm, expectedQueriesBool]
    _ = boolMaxInfluence p f * minExpectedQueriesBool hp0 hp1 f := by rw [hΔ]

/-- Ratio lower bound on distributional expected query complexity:
`Var_p(f) / Inf_max(f) ≤ Δ_p(f)`. -/
theorem boolVariance_div_boolMaxInfluence_le_minExpectedQueriesBool {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) :
    boolVariance p f / boolMaxInfluence p f ≤ minExpectedQueriesBool hp0 hp1 f := by
  have hmul := boolVariance_le_boolMaxInfluence_mul_minExpectedQueriesBool hp0 hp1 f
  have hmax_nn : 0 ≤ boolMaxInfluence p f := by
    rw [boolMaxInfluence_eq_maxProdInfluence hp0 hp1]
    exact maxProdInfluence_nonneg _ _ _
  by_cases hm : boolMaxInfluence p f = 0
  · rw [hm, div_zero]
    obtain ⟨T, _, _, hΔ⟩ := exists_computes_expectedQueriesBool_eq hp0 hp1 f
    rw [← hΔ]
    exact sum_nonneg fun i _ => by
      rw [revealmentBool_eq_revealment hp0 hp1]; exact revealment_nonneg _ _ _
  · have hm_pos : 0 < boolMaxInfluence p f := lt_of_le_of_ne hmax_nn (Ne.symm hm)
    rwa [div_le_iff₀ hm_pos, mul_comm]

/-- Whenever `Δ_p(f) ≤ d`, there exists a set `S` of at most `d` coordinates whose `p`-biased
influences sum to at least `Var_p(f)`. -/
theorem exists_card_le_and_boolVariance_le_sum_boolInfluence {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) {d : ℕ} (hd : minExpectedQueriesBool hp0 hp1 f ≤ (d : ℝ)) :
    ∃ S : Finset ι, S.card ≤ d ∧ boolVariance p f ≤ ∑ i ∈ S, boolInfluence p i f := by
  obtain ⟨T, hT, _, hΔ⟩ := exists_computes_expectedQueriesBool_eq hp0 hp1 f
  have hw_nn (i : ι) : 0 ≤ revealmentBool p i T := by
    rw [revealmentBool_eq_revealment hp0 hp1]; exact revealment_nonneg _ _ _
  have hw_le1 (i : ι) : revealmentBool p i T ≤ 1 := by
    rw [revealmentBool_eq_revealment hp0 hp1]; exact revealment_le_one _ _ _
  have hw_sum : ∑ i : ι, revealmentBool p i T ≤ (d : ℝ) := by
    rw [← expectedQueriesBool, hΔ]
    exact hd
  have ha_nn (i : ι) : 0 ≤ boolInfluence p i f := boolInfluence_nonneg hp0 hp1 i f
  have hmain := boolVariance_le_sum_revealmentBool_mul_boolInfluence hp0 hp1 f T hT
  by_cases hcard : Fintype.card ι ≤ d
  · refine ⟨Finset.univ, by simpa using hcard, hmain.trans ?_⟩
    exact sum_le_sum fun i _ => mul_le_of_le_one_left (ha_nn i) (hw_le1 i)
  · have hd_le : d ≤ Fintype.card ι := le_of_not_ge hcard
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · refine ⟨∅, le_rfl, ?_⟩
      simp only [sum_empty]
      have hall0 : ∀ i : ι, revealmentBool p i T = 0 := fun i => by
        have hsum0 : ∑ j : ι, revealmentBool p j T = 0 :=
          le_antisymm (by simpa using hw_sum) (sum_nonneg fun j _ => hw_nn j)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw_nn j)).mp hsum0 i (mem_univ i)
      refine hmain.trans_eq ?_
      simp [hall0]
    · have hne : (Finset.univ.powersetCard d : Finset (Finset ι)).Nonempty :=
        Finset.powersetCard_nonempty.mpr (by simpa using hd_le)
      obtain ⟨S, hS_mem, hS_max⟩ :=
        Finset.exists_max_image (Finset.univ.powersetCard d)
          (fun U => ∑ i ∈ U, boolInfluence p i f) hne
      have hScard : S.card = d := (Finset.mem_powersetCard.mp hS_mem).2
      have hS_ne : S.Nonempty := Finset.card_pos.mp (hScard.symm ▸ hd_pos)
      obtain ⟨i₀, hi₀, hi₀_min⟩ :=
        Finset.exists_min_image S (fun i => boolInfluence p i f) hS_ne
      have hout : ∀ j ∉ S, boolInfluence p j f ≤ boolInfluence p i₀ f := by
        intro j hj
        let S' := insert j (S.erase i₀)
        have hS'_mem : S' ∈ Finset.univ.powersetCard d := by
          rw [Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ _, ?_⟩
          have hj_not : j ∉ S.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
          rw [Finset.card_insert_of_notMem hj_not, Finset.card_erase_of_mem hi₀]
          omega
        have hle := hS_max S' hS'_mem
        have hsum_S' :
            (∑ k ∈ S', boolInfluence p k f) =
              (∑ k ∈ S, boolInfluence p k f) - boolInfluence p i₀ f + boolInfluence p j f := by
          have hj_not : j ∉ S.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
          rw [Finset.sum_insert hj_not, Finset.sum_erase_eq_sub hi₀]
          ring
        linarith
      refine ⟨S, hScard.le, hmain.trans ?_⟩
      have hsplit :
          (∑ i : ι, revealmentBool p i T * boolInfluence p i f) -
              (∑ i ∈ S, boolInfluence p i f) =
            (∑ j ∈ Finset.univ \ S, revealmentBool p j T * boolInfluence p j f) -
              (∑ i ∈ S, (1 - revealmentBool p i T) * boolInfluence p i f) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ S)]
        have hsub :
            (∑ i ∈ S, revealmentBool p i T * boolInfluence p i f) -
                (∑ i ∈ S, boolInfluence p i f) =
              -(∑ i ∈ S, (1 - revealmentBool p i T) * boolInfluence p i f) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
          exact sum_congr rfl fun _ _ => by ring
        linarith
      have h1 :
          ∑ j ∈ Finset.univ \ S, revealmentBool p j T * boolInfluence p j f ≤
            (∑ j ∈ Finset.univ \ S, revealmentBool p j T) * boolInfluence p i₀ f := by
        rw [Finset.sum_mul]
        exact sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (hout j (Finset.mem_sdiff.mp hj).2) (hw_nn j)
      have h2 :
          (∑ i ∈ S, (1 - revealmentBool p i T)) * boolInfluence p i₀ f ≤
            ∑ i ∈ S, (1 - revealmentBool p i T) * boolInfluence p i f := by
        rw [Finset.sum_mul]
        exact sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hi₀_min i hi) (sub_nonneg.mpr (hw_le1 i))
      have h3 :
          (∑ j ∈ Finset.univ \ S, revealmentBool p j T) -
              (∑ i ∈ S, (1 - revealmentBool p i T)) =
            (∑ i : ι, revealmentBool p i T) - (d : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hScard,
          ← Finset.sum_sdiff (Finset.subset_univ S)]
        ring
      have h4 :
          ((∑ j ∈ Finset.univ \ S, revealmentBool p j T) -
              (∑ i ∈ S, (1 - revealmentBool p i T))) * boolInfluence p i₀ f ≤ 0 := by
        rw [h3]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hw_sum) (ha_nn i₀)
      linarith

end BooleanRevealment

/-! ### Monotone total-influence bound, critical probability, and query-complexity lower bounds -/

section MonotoneBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def centeredSum {β : Type*} (p : ℝ) (T : ProdDecisionTree (fun _ : ι => Bool) β)
    (x : ι → Bool) : ℝ :=
  ∑ i ∈ T.queries x, (boolVal (x i) - (2 * p - 1))

private theorem bernoulliAverage_centered_coord (p : ℝ) (i : ι) :
    Cslib.BitString.bernoulliAverage p (fun x : ι → Bool => boolVal (x i) - (2 * p - 1)) = 0 := by
  have h : (fun x : ι → Bool => boolVal (x i) - (2 * p - 1)) =
      fun x => 2 * (if x i then (1 : ℝ) else 0) - 2 * p := by
    funext x; cases x i <;> norm_num [boolVal] <;> ring
  rw [h, Cslib.BitString.bernoulliAverage_sub, Cslib.BitString.bernoulliAverage_const_mul,
    Cslib.BitString.bernoulliAverage_coordinate, Cslib.BitString.bernoulliAverage_const]
  ring

private theorem bernoulliAverage_centered_coord_sq (p : ℝ) (i : ι) :
    Cslib.BitString.bernoulliAverage p
        (fun x : ι → Bool => (boolVal (x i) - (2 * p - 1)) ^ 2) =
      4 * p * (1 - p) := by
  have h : (fun x : ι → Bool => (boolVal (x i) - (2 * p - 1)) ^ 2) =
      fun x => (4 - 8 * p) * (if x i then (1 : ℝ) else 0) + 4 * p ^ 2 := by
    funext x; cases x i <;> norm_num [boolVal] <;> ring
  rw [h, Cslib.BitString.bernoulliAverage_add, Cslib.BitString.bernoulliAverage_const_mul,
    Cslib.BitString.bernoulliAverage_coordinate, Cslib.BitString.bernoulliAverage_const]
  ring

private theorem prodExpect_centeredSum_eq_zero {β : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T : ProdDecisionTree (fun _ : ι => Bool) β} (hT : T.NoRepeat) :
    prodExpect (bernoulliCoordFamily ι hp0 hp1) (centeredSum p T) = 0 := by
  induction T with
  | leaf z =>
    have h0 : centeredSum p (.leaf z : ProdDecisionTree (fun _ : ι => Bool) β) = fun _ => 0 :=
      funext fun x => by simp [centeredSum]
    rw [h0, prodExpect_zero]
  | node i c ih =>
    have hsplit : centeredSum p (.node i c) =
        fun x => (boolVal (x i) - (2 * p - 1)) + centeredSum p (c (x i)) x := by
      funext x
      have hi : i ∉ (c (x i)).queries x := fun h =>
        (hT (x i)).2 (ProdDecisionTree.queries_subset_allQueries (c (x i)) x h)
      simp [centeredSum, ProdDecisionTree.queries_node, Finset.sum_insert hi]
    rw [hsplit, prodExpect_add]
    have h1 : prodExpect (bernoulliCoordFamily ι hp0 hp1)
        (fun x => boolVal (x i) - (2 * p - 1)) = 0 := by
      rw [prodExpect_bernoulliCoordFamily]
      exact bernoulliAverage_centered_coord p i
    have h2 : prodExpect (bernoulliCoordFamily ι hp0 hp1)
        (fun x => centeredSum p (c (x i)) x) = 0 := by
      rw [← prodExpect_update (bernoulliCoordFamily ι hp0 hp1) i]
      refine sum_eq_zero fun a _ => ?_
      have hcongr : (fun x => centeredSum p (c (Function.update x i a i)) (Function.update x i a)) =
          centeredSum p (c a) := by
        funext x
        simp only [Function.update_self, centeredSum,
          ProdDecisionTree.queries_update_of_notMem_allQueries (hT a).2]
        refine sum_congr rfl fun j hj => ?_
        have hji : j ≠ i := fun h =>
          (hT a).2 (h ▸ ProdDecisionTree.queries_subset_allQueries (c a) x hj)
        simp [Function.update_of_ne hji]
      rw [hcongr, ih a (hT a).1, mul_zero]
    rw [h1, h2, add_zero]

private theorem prodExpect_centeredSum_sq {β : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T : ProdDecisionTree (fun _ : ι => Bool) β} (hT : T.NoRepeat) :
    prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun x => centeredSum p T x ^ 2) =
      4 * p * (1 - p) * expectedQueries (bernoulliCoordFamily ι hp0 hp1) T := by
  induction T with
  | leaf _ =>
    simp [centeredSum, expectedQueries_eq_sum, revealment]
  | node i c ih =>
    have hsplit (x : ι → Bool) :
        centeredSum p (.node i c) x ^ 2 =
          (boolVal (x i) - (2 * p - 1)) ^ 2 +
            2 * (boolVal (x i) - (2 * p - 1)) * centeredSum p (c (x i)) x +
            centeredSum p (c (x i)) x ^ 2 := by
      have hi : i ∉ (c (x i)).queries x := fun h =>
        (hT (x i)).2 (ProdDecisionTree.queries_subset_allQueries (c (x i)) x h)
      have hs : centeredSum p (.node i c) x =
          (boolVal (x i) - (2 * p - 1)) + centeredSum p (c (x i)) x := by
        simp [centeredSum, ProdDecisionTree.queries_node, Finset.sum_insert hi]
      rw [hs]; ring
    simp_rw [hsplit, prodExpect_add]
    have h1 : prodExpect (bernoulliCoordFamily ι hp0 hp1)
        (fun x => (boolVal (x i) - (2 * p - 1)) ^ 2) = 4 * p * (1 - p) := by
      rw [prodExpect_bernoulliCoordFamily]
      exact bernoulliAverage_centered_coord_sq p i
    have hcross : prodExpect (bernoulliCoordFamily ι hp0 hp1)
        (fun x => 2 * (boolVal (x i) - (2 * p - 1)) * centeredSum p (c (x i)) x) = 0 := by
      rw [← prodExpect_update (bernoulliCoordFamily ι hp0 hp1) i]
      refine sum_eq_zero fun a _ => ?_
      have hcongr :
          (fun x => 2 * (boolVal (Function.update x i a i) - (2 * p - 1)) *
              centeredSum p (c (Function.update x i a i)) (Function.update x i a)) =
            fun x => (2 * (boolVal a - (2 * p - 1))) * centeredSum p (c a) x := by
        funext x
        simp only [Function.update_self, centeredSum,
          ProdDecisionTree.queries_update_of_notMem_allQueries (hT a).2]
        refine congrArg (2 * (boolVal a - (2 * p - 1)) * ·) (sum_congr rfl fun j hj => ?_)
        have hji : j ≠ i := fun h =>
          (hT a).2 (h ▸ ProdDecisionTree.queries_subset_allQueries (c a) x hj)
        simp [Function.update_of_ne hji]
      rw [hcongr, prodExpect_const_mul, prodExpect_centeredSum_eq_zero hp0 hp1 (hT a).1,
        mul_zero, mul_zero]
    have hrec : prodExpect (bernoulliCoordFamily ι hp0 hp1)
        (fun x => centeredSum p (c (x i)) x ^ 2) =
        ∑ a : Bool, (bernoulliCoordFamily ι hp0 hp1 i).weights a *
          (4 * p * (1 - p) * expectedQueries (bernoulliCoordFamily ι hp0 hp1) (c a)) := by
      rw [← prodExpect_update (bernoulliCoordFamily ι hp0 hp1) i]
      refine sum_congr rfl fun a _ => congrArg _ ?_
      have hcongr :
          (fun x => centeredSum p (c (Function.update x i a i)) (Function.update x i a) ^ 2) =
            fun x => centeredSum p (c a) x ^ 2 := by
        funext x
        simp only [Function.update_self, centeredSum,
          ProdDecisionTree.queries_update_of_notMem_allQueries (hT a).2]
        congr 1
        refine sum_congr rfl fun j hj => ?_
        have hji : j ≠ i := fun h =>
          (hT a).2 (h ▸ ProdDecisionTree.queries_subset_allQueries (c a) x hj)
        simp [Function.update_of_ne hji]
      rw [hcongr, ih a (hT a).1]
    have hexp_split :
        expectedQueries (bernoulliCoordFamily ι hp0 hp1) (.node i c) =
          1 + ∑ a : Bool, (bernoulliCoordFamily ι hp0 hp1 i).weights a *
            expectedQueries (bernoulliCoordFamily ι hp0 hp1) (c a) := by
      rw [expectedQueries_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        revealment_node_self]
      congr 1
      have hne : ∀ j ∈ Finset.univ.erase i,
          revealment (bernoulliCoordFamily ι hp0 hp1) j (.node i c) =
            ∑ a : Bool, (bernoulliCoordFamily ι hp0 hp1 i).weights a *
              revealment (bernoulliCoordFamily ι hp0 hp1) j (c a) := fun j hj =>
        revealment_node_ne (bernoulliCoordFamily ι hp0 hp1) (Finset.ne_of_mem_erase hj) c
          (fun a => (hT a).2)
      rw [Finset.sum_congr rfl hne, Finset.sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      rw [expectedQueries_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        revealment_eq_zero_of_notMem_allQueries _ (hT a).2, zero_add]
    rw [h1, hcross, add_zero, hrec, hexp_split, mul_add, mul_one, Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun _ _ => by ring

private theorem prodExpect_eval_mul_unqueried_eq_zero {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T : ProdDecisionTree (fun _ : ι => Bool) Bool} (hT : T.NoRepeat) (j : ι) :
    prodExpect (bernoulliCoordFamily ι hp0 hp1)
      (fun x => if j ∈ T.queries x then 0 else boolVal (T.eval x) * (boolVal (x j) - (2 * p - 1))) =
      0 := by
  induction T with
  | leaf _ =>
    simp only [ProdDecisionTree.queries_leaf, Finset.notMem_empty, ↓reduceIte,
      ProdDecisionTree.eval_leaf, prodExpect_const_mul, prodExpect_bernoulliCoordFamily,
      bernoulliAverage_centered_coord, mul_zero]
  | node i c ih =>
    by_cases hji : j = i
    · subst hji
      simp [ProdDecisionTree.queries_node]
    · rw [← prodExpect_update (bernoulliCoordFamily ι hp0 hp1) i]
      refine sum_eq_zero fun a _ => ?_
      have hcongr :
          (fun x => if j ∈ (ProdDecisionTree.node i c).queries (Function.update x i a) then (0 : ℝ)
              else boolVal ((ProdDecisionTree.node i c).eval (Function.update x i a)) *
                (boolVal (Function.update x i a j) - (2 * p - 1))) =
            fun x => if j ∈ (c a).queries x then 0 else
              boolVal ((c a).eval x) * (boolVal (x j) - (2 * p - 1)) := by
        funext x
        simp only [ProdDecisionTree.queries_node, ProdDecisionTree.eval_node, Function.update_self,
          Finset.mem_insert, hji, false_or, Function.update_of_ne hji,
          ProdDecisionTree.queries_update_of_notMem_allQueries (hT a).2,
          ProdDecisionTree.eval_update_of_notMem_allQueries (hT a).2]
      rw [hcongr, ih a (hT a).1, mul_zero]

private theorem boolInfluence_eq_expect_mul_centered_of_monotone (p : ℝ) (i : ι)
    {f : (ι → Bool) → Bool} (hf : Monotone f) :
    boolInfluence p i f =
      Cslib.BitString.bernoulliAverage p
        (fun x => boolVal (f x) * (boolVal (x i) - (2 * p - 1))) := by
  have h1 :
      (fun x => boolVal (f x) * (boolVal (x i) - (2 * p - 1))) =
        fun x => Cslib.BitString.signVal (f x) * (Cslib.BitString.signVal (x i) - (1 - 2 * p)) := by
    funext x
    rw [boolVal_eq_neg_signVal, boolVal_eq_neg_signVal]
    ring
  rw [h1, Cslib.BitString.bernoulliAverage_mul_signVal_sub, boolInfluence_eq_four_mul_prob_flip]
  congr 1
  refine congrArg (Cslib.BitString.bernoulliAverage p) (funext fun x => ?_)
  have hle : f (Function.update x i false) ≤ f (Function.update x i true) :=
    hf fun j => by
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
  rw [Cslib.BitString.derivative]
  revert hle
  cases f (Function.update x i false) <;> cases f (Function.update x i true) <;>
    simp [Cslib.BitString.signVal]

private theorem prodExpect_sq_le_prodExpect_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : (ι → Bool) → ℝ) :
    (prodExpect (bernoulliCoordFamily ι hp0 hp1) h) ^ 2 ≤
      prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun x => h x ^ 2) := by
  let μ := bernoulliCoordFamily ι hp0 hp1
  let m := prodExpect μ h
  have hnn : 0 ≤ prodExpect μ (fun x => (h x - m) ^ 2) := prodExpect_nonneg μ fun _ => sq_nonneg _
  have hexp :
      prodExpect μ (fun x => (h x - m) ^ 2) =
        prodExpect μ (fun x => h x ^ 2) - m ^ 2 := by
    have hpt : (fun x => (h x - m) ^ 2) =
        fun x => h x ^ 2 + (-(2 * m) * h x + m ^ 2) := by funext _; ring
    rw [hpt, prodExpect_add, prodExpect_add, prodExpect_const_mul, prodExpect_const]
    dsimp [m]; ring
  linarith

/-- For any monotone Boolean function `f` under `μ_p` (`p ∈ [0, 1]`) and any deterministic decision
tree `T` computing `f`, total `p`-biased influence satisfies
`Inf_p(f) ≤ 2 √(p (1 - p) Δ_p(T))`. -/
theorem boolTotalInfluence_le_two_mul_sqrt_expectedQueriesBool {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : (ι → Bool) → Bool} (hf : Monotone f)
    {T : Cslib.DecisionTree ι Bool} (hT : T.Computes f) :
    boolTotalInfluence p f ≤ 2 * √(p * (1 - p) * expectedQueriesBool p T) := by
  let P := (ProdDecisionTree.ofCslib T).prune (fun _ => none)
  have hP_no : P.NoRepeat := ProdDecisionTree.noRepeat_prune _ _
  have hP_comp : P.Computes f := fun x => by
    rw [ProdDecisionTree.eval_prune_empty, ProdDecisionTree.eval_ofCslib, hT x]
  have hP_exp : expectedQueries (bernoulliCoordFamily ι hp0 hp1) P = expectedQueriesBool p T := by
    rw [expectedQueriesBool_eq_expectedQueries hp0 hp1]
    simp only [P, expectedQueries_eq_sum, revealment_prune_empty]
  have htot :
      boolTotalInfluence p f =
        prodExpect (bernoulliCoordFamily ι hp0 hp1) (fun x => boolVal (f x) * centeredSum p P x)
          := by
    unfold boolTotalInfluence
    simp_rw [boolInfluence_eq_expect_mul_centered_of_monotone p _ hf,
      ← prodExpect_bernoulliCoordFamily hp0 hp1]
    rw [← prodExpect_sum]
    have hdiff :
        (fun x => ∑ i : ι, boolVal (f x) * (boolVal (x i) - (2 * p - 1))) =
          fun x => boolVal (f x) * centeredSum p P x +
            ∑ j : ι, if j ∈ P.queries x then (0 : ℝ) else
              boolVal (P.eval x) * (boolVal (x j) - (2 * p - 1)) := by
      funext x
      have hq_sum :
          boolVal (f x) * centeredSum p P x =
            ∑ j : ι, if j ∈ P.queries x then
              boolVal (f x) * (boolVal (x j) - (2 * p - 1)) else 0 := by
        rw [centeredSum, Finset.mul_sum, ← Finset.sum_filter]
        congr 1; ext j; simp
      rw [hq_sum, ← Finset.sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ P.queries x <;> simp [hj, hP_comp x]
    rw [hdiff, prodExpect_add, prodExpect_sum]
    have h0 :
        ∑ j : ι, prodExpect (bernoulliCoordFamily ι hp0 hp1)
            (fun x => if j ∈ P.queries x then 0 else
              boolVal (P.eval x) * (boolVal (x j) - (2 * p - 1))) = 0 :=
      sum_eq_zero fun j _ => prodExpect_eval_mul_unqueried_eq_zero hp0 hp1 hP_no j
    rw [h0, add_zero]
  have hcs := prodExpect_sq_le_prodExpect_sq hp0 hp1 (fun x => boolVal (f x) * centeredSum p P x)
  rw [← htot] at hcs
  have hsq :
      (fun x => (boolVal (f x) * centeredSum p P x) ^ 2) =
        fun x => centeredSum p P x ^ 2 := by
    funext x; rw [mul_pow, boolVal_sq, one_mul]
  rw [hsq, prodExpect_centeredSum_sq hp0 hp1 hP_no, hP_exp] at hcs
  have h4 : 4 * p * (1 - p) * expectedQueriesBool p T =
      (2 * √(p * (1 - p) * expectedQueriesBool p T)) ^ 2 := by
    have hnn : 0 ≤ p * (1 - p) * expectedQueriesBool p T := by
      refine mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) ?_
      rw [expectedQueriesBool_eq_expectedQueries hp0 hp1, expectedQueries_eq_sum]
      exact sum_nonneg fun _ _ => revealment_nonneg _ _ _
    rw [mul_pow, Real.sq_sqrt hnn]
    ring
  rw [h4] at hcs
  have hrhs_nn : 0 ≤ 2 * √(p * (1 - p) * expectedQueriesBool p T) := by positivity
  exact le_of_sq_le_sq hcs hrhs_nn

/-- Distributional expected query-complexity form of the monotone total-influence bound:
`Inf_p(f) ≤ 2 √(p (1 - p) Δ_p(f))`. -/
theorem boolTotalInfluence_le_two_mul_sqrt_minExpectedQueriesBool {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : (ι → Bool) → Bool} (hf : Monotone f) :
    boolTotalInfluence p f ≤ 2 * √(p * (1 - p) * minExpectedQueriesBool hp0 hp1 f) := by
  obtain ⟨T, hT, _, hΔ⟩ := exists_computes_expectedQueriesBool_eq hp0 hp1 f
  rw [← hΔ]
  exact boolTotalInfluence_le_two_mul_sqrt_expectedQueriesBool hp0 hp1 hf hT

/-- `p` is the critical probability of a Boolean function `f` when `p ∈ (0, 1)` and its `{-1, 1}`
expectation under `μ_p` vanishes (equivalently `Var_p(f) = 1`). -/
structure IsCriticalProb (p : ℝ) (f : (ι → Bool) → Bool) : Prop where
  /-- Positivity `0 < p`. -/
  pos : 0 < p
  /-- Upper bound `p < 1`. -/
  lt_one : p < 1
  /-- Vanishing `p`-biased expectation in `{-1, 1}`. -/
  expect_zero : Cslib.BitString.bernoulliAverage p (fun x => boolVal (f x)) = 0

theorem IsCriticalProb.boolVariance_eq_one {p : ℝ} {f : (ι → Bool) → Bool}
    (hp : IsCriticalProb p f) : boolVariance p f = 1 := by
  rw [boolVariance, hp.expect_zero]
  norm_num

/-- Every nonconstant monotone Boolean function has a unique critical probability `p ∈ (0, 1)`. -/
theorem exists_unique_criticalProb {f : (ι → Bool) → Bool} (hf : Monotone f)
    (hnc : ∃ x y : ι → Bool, f x ≠ f y) :
    ∃! p : ℝ, IsCriticalProb p f := by
  have hfalse : f (fun _ => false) = false := by
    by_contra h
    have htrue : f (fun _ => false) = true := by cases hf0 : f (fun _ => false) <;> simp_all
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : f x = true := le_antisymm (Bool.le_true _) (htrue ▸ hf (fun _ => Bool.false_le _))
    have hy : f y = true := le_antisymm (Bool.le_true _) (htrue ▸ hf (fun _ => Bool.false_le _))
    exact hxy (hx.trans hy.symm)
  have htrue : f (fun _ => true) = true := by
    by_contra h
    have hf1 : f (fun _ => true) = false := by cases hf1 : f (fun _ => true) <;> simp_all
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : f x = false := le_antisymm (hf (fun _ => Bool.le_true _) |>.trans_eq hf1)
      (Bool.false_le _)
    have hy : f y = false := le_antisymm (hf (fun _ => Bool.le_true _) |>.trans_eq hf1)
      (Bool.false_le _)
    exact hxy (hx.trans hy.symm)
  let g : ℝ → ℝ :=
    fun q => Cslib.BitString.bernoulliAverage q fun x => Cslib.BitString.bitVal ℝ (f x)
  have hstrict : StrictMonoOn g (Set.Icc 0 1) :=
    Cslib.BitString.strictMonoOn_bernoulliAverage_bitVal_of_monotone hf hnc
  have hcont_sum : ∀ (s : Finset (ι → Bool)) (h : (ι → Bool) → ℝ → ℝ),
      (∀ a ∈ s, Continuous (h a)) → Continuous (fun q => ∑ a ∈ s, h a q) := by
    intro s h hs
    induction s using Finset.induction with
    | empty => simpa using continuous_const
    | insert a t ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (hs a (Finset.mem_insert_self a t)).add
        (ih fun b hb => hs b (Finset.mem_insert_of_mem hb))
  have hcont_prod : ∀ (s : Finset ι) (h : ι → ℝ → ℝ),
      (∀ a ∈ s, Continuous (h a)) → Continuous (fun q => ∏ a ∈ s, h a q) := by
    intro s h hs
    induction s using Finset.induction with
    | empty => simpa using continuous_const
    | insert a t ha ih =>
      simp_rw [Finset.prod_insert ha]
      exact (hs a (Finset.mem_insert_self a t)).mul
        (ih fun b hb => hs b (Finset.mem_insert_of_mem hb))
  have hcont : Continuous g := by
    refine hcont_sum Finset.univ _ fun x _ => (hcont_prod Finset.univ _ fun i _ => ?_).mul
      continuous_const
    by_cases hxi : x i = true
    · simpa [hxi] using continuous_id'
    · simpa [hxi] using continuous_sub_left (1 : ℝ)
  have hg0 : g 0 = 0 := by
    simp [g, Cslib.BitString.bernoulliAverage_zero, hfalse]
  have hg1 : g 1 = 1 := by
    have h := Cslib.BitString.bernoulliAverage_one_sub (ι :=
      ι) 0 (fun x => Cslib.BitString.bitVal ℝ (f x))
    rw [sub_zero, Cslib.BitString.bernoulliAverage_zero] at h
    have hall : (fun _ : ι => !false) = fun _ => true := rfl
    simpa [g, hall, htrue] using h
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc (g 0) (g 1) := by rw [hg0, hg1]; norm_num
  obtain ⟨p, hpIcc, hgp⟩ :=
    intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hcont.continuousOn hmem
  have hp0 : 0 < p := lt_of_le_of_ne hpIcc.1 (by rintro rfl; linarith)
  have hp1 : p < 1 := lt_of_le_of_ne hpIcc.2 (by rintro rfl; linarith)
  have hboolVal (q : ℝ) :
      Cslib.BitString.bernoulliAverage q (fun x => boolVal (f x)) = 2 * g q - 1 := by
    have hpt : (fun x => boolVal (f x)) = fun x => 2 * Cslib.BitString.bitVal ℝ (f x) - 1 := by
      funext x; cases f x <;> norm_num [boolVal]
    rw [hpt, Cslib.BitString.bernoulliAverage_sub, Cslib.BitString.bernoulliAverage_const_mul,
      Cslib.BitString.bernoulliAverage_const]
  refine ⟨p, ⟨hp0, hp1, by rw [hboolVal, hgp]; ring⟩, fun q hq => ?_⟩
  have hgq : g q = 1 / 2 := by
    have := hq.expect_zero; rw [hboolVal] at this; linarith
  exact hstrict.injOn ⟨hq.pos.le, hq.lt_one.le⟩ hpIcc (hgq.trans hgp.symm)

/-- Coordinate influences of a transitive Boolean function are equal across all coordinates under
every `p`-biased product distribution. -/
theorem boolInfluence_eq_of_isPretransitive (p : ℝ) (f : (ι → Bool) → Bool)
    [htrans : MulAction.IsPretransitive (Cslib.BitString.aut f) ι] (i j : ι) :
    boolInfluence p i f = boolInfluence p j f := by
  obtain ⟨π, rfl, hπ⟩ := (Cslib.BitString.isPretransitive_aut_iff.mp htrans) i j
  rw [boolInfluence_eq_four_mul_prob_flip, boolInfluence_eq_four_mul_prob_flip]
  congr 1
  rw [← Cslib.BitString.bernoulliAverage_reindex π.symm p]
  refine congrArg (Cslib.BitString.bernoulliAverage p) (funext fun x => ?_)
  have hupd (b : Bool) :
      Function.update (fun k => x (π.symm.symm k)) i b =
        fun k => Function.update x (π i) b (π k) := by
    funext k
    simp only [Equiv.symm_symm]
    by_cases hki : k = i
    · subst hki; simp
    · have hk' : π k ≠ π i := fun h => hki (π.injective h)
      simp [Function.update_of_ne hki, Function.update_of_ne hk']
  rw [hupd true, hupd false, hπ (Function.update x (π i) true),
    hπ (Function.update x (π i) false)]

/-- Distributional and zero-error randomized query-complexity lower bound for any nonconstant
monotone transitive Boolean function `f : (ι → Bool) → Bool` at its critical probability `p`:
`|ι|^{2/3} / (4 p (1 - p))^{1/3} ≤ Δ_p(f) ≤ R_0(f)`. -/
theorem card_rpow_div_le_minExpectedQueriesBool_of_isPretransitive {p : ℝ}
    {f : (ι → Bool) → Bool} (hf : Monotone f) (hnc : ∃ x y : ι → Bool, f x ≠ f y)
    [MulAction.IsPretransitive (Cslib.BitString.aut f) ι] (hp : IsCriticalProb p f) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / (4 * p * (1 - p)) ^ ((1 : ℝ) / 3) ≤
        minExpectedQueriesBool hp.pos.le hp.lt_one.le f ∧
      minExpectedQueriesBool hp.pos.le hp.lt_one.le f ≤
        Cslib.QueryComplexity.zeroErrorComplexity f := by
  have hp_pos : 0 < p := hp.pos
  have hp0 : 0 ≤ p := hp.pos.le
  have hp1 : p ≤ 1 := hp.lt_one.le
  have hq : 0 < 1 - p := sub_pos.mpr hp.lt_one
  have h4pq : 0 < 4 * p * (1 - p) := by positivity
  refine ⟨?_, minExpectedQueriesBool_le_zeroErrorComplexity hp0 hp1 f⟩
  have hne_ι : Nonempty ι := by
    obtain ⟨x, y, hxy⟩ := hnc
    by_contra hemp
    exact hxy (congrArg f (funext fun i => (hemp ⟨i⟩).elim))
  obtain ⟨i₀⟩ := hne_ι
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) :=
    Nat.cast_pos.mpr (@Fintype.card_pos ι _ ⟨i₀⟩)
  have htot_eq : boolTotalInfluence p f = (Fintype.card ι : ℝ) * boolInfluence p i₀ f := by
    rw [boolTotalInfluence,
      Finset.sum_congr rfl fun j _ => boolInfluence_eq_of_isPretransitive p f j i₀]
    simp
  have hmax_eq : boolMaxInfluence p f = boolInfluence p i₀ f := by
    refine le_antisymm ?_ (boolInfluence_le_boolMaxInfluence p i₀ f)
    unfold boolMaxInfluence
    have hle : ∀ s : Finset ι, s.fold max 0 (fun j => boolInfluence p j f) ≤
      boolInfluence p i₀ f := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using boolInfluence_nonneg hp0 hp1 i₀ f
      | insert j t hj ih =>
        rw [Finset.fold_insert hj, boolInfluence_eq_of_isPretransitive p f j i₀]
        exact max_le le_rfl ih
    exact hle Finset.univ
  set Δ := minExpectedQueriesBool hp0 hp1 f
  have hΔ_nn : 0 ≤ Δ := by
    obtain ⟨T, _, _, hΔ⟩ := exists_computes_expectedQueriesBool_eq hp0 hp1 f
    dsimp only [Δ]
    rw [← hΔ]
    exact sum_nonneg fun i _ => by
      rw [revealmentBool_eq_revealment hp0 hp1]; exact revealment_nonneg _ _ _
  have h1 : 1 ≤ boolInfluence p i₀ f * Δ := by
    have hc := boolVariance_le_boolMaxInfluence_mul_minExpectedQueriesBool hp0 hp1 f
    rwa [hp.boolVariance_eq_one, hmax_eq] at hc
  have h2 : (Fintype.card ι : ℝ) ≤ boolTotalInfluence p f * Δ := by
    rw [htot_eq, mul_assoc]
    calc (Fintype.card ι : ℝ) = (Fintype.card ι : ℝ) * 1 := (mul_one _).symm
      _ ≤ (Fintype.card ι : ℝ) * (boolInfluence p i₀ f * Δ) :=
          mul_le_mul_of_nonneg_left h1 hn_pos.le
  have hos := boolTotalInfluence_le_two_mul_sqrt_minExpectedQueriesBool hp0 hp1 hf
  have h3 : (Fintype.card ι : ℝ) ≤ 2 * √(p * (1 - p) * Δ) * Δ :=
    h2.trans (mul_le_mul_of_nonneg_right hos hΔ_nn)
  have hsq : (Fintype.card ι : ℝ) ^ 2 ≤ (4 * p * (1 - p)) * Δ ^ 3 := by
    have hsq' : (Fintype.card ι : ℝ) ^ 2 ≤ (2 * √(p * (1 - p) * Δ) * Δ) ^ 2 :=
      pow_le_pow_left₀ hn_pos.le h3 2
    have hmul_nn : 0 ≤ p * (1 - p) * Δ := by positivity
    calc (Fintype.card ι : ℝ) ^ 2
        ≤ (2 * √(p * (1 - p) * Δ) * Δ) ^ 2 := hsq'
      _ = 4 * (√(p * (1 - p) * Δ)) ^ 2 * Δ ^ 2 := by ring
      _ = 4 * (p * (1 - p) * Δ) * Δ ^ 2 := by rw [Real.sq_sqrt hmul_nn]
      _ = (4 * p * (1 - p)) * Δ ^ 3 := by ring
  have hrpow :
      ((Fintype.card ι : ℝ) ^ 2) ^ ((1 : ℝ) / 3) ≤ ((4 * p * (1 - p)) * Δ ^ 3) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (sq_nonneg _) hsq (by norm_num)
  have hL : ((Fintype.card ι : ℝ) ^ 2) ^ ((1 : ℝ) / 3) =
      (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hR : ((4 * p * (1 - p)) * Δ ^ 3) ^ ((1 : ℝ) / 3) =
      (4 * p * (1 - p)) ^ ((1 : ℝ) / 3) * Δ := by
    rw [Real.mul_rpow h4pq.le (pow_nonneg hΔ_nn 3), ← Real.rpow_natCast Δ 3,
      ← Real.rpow_mul hΔ_nn]
    norm_num
  rw [hL, hR] at hrpow
  have hdenom_pos : 0 < (4 * p * (1 - p)) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos h4pq _
  rwa [div_le_iff₀ hdenom_pos, mul_comm]

/-- Boolean function on `edgeCount v` edge indicators encoding a `v`-vertex undirected graph
property `P : SimpleGraph (Fin v) → Prop`. -/
noncomputable def graphPropertyFn {v : ℕ} (P : SimpleGraph (Fin v) → Prop) :
    Cslib.BooleanFunction (Cslib.BitString.Graph.edgeCount v) :=
  fun x => @decide (P (Cslib.BitString.Graph.graph x)) (Classical.propDecidable _)

@[simp]
theorem graphPropertyFn_apply {v : ℕ} (P : SimpleGraph (Fin v) → Prop)
    (x : Fin (Cslib.BitString.Graph.edgeCount v) → Bool) :
    (graphPropertyFn P x = true) ↔ P (Cslib.BitString.Graph.graph x) := by
  simp [graphPropertyFn]

/-- Invariance of a `v`-vertex simple-graph predicate under graph isomorphisms. -/
@[expose]
def IsGraphProperty {v : ℕ} (P : SimpleGraph (Fin v) → Prop) : Prop :=
  ∀ (G H : SimpleGraph (Fin v)), Nonempty (G ≃g H) → (P G ↔ P H)

/-- Every isomorphism-invariant `v`-vertex graph property induces a transitive Boolean function on
`edgeCount v` edge variables. -/
theorem isPretransitive_aut_graphPropertyFn {v : ℕ} {P : SimpleGraph (Fin v) → Prop}
    (hP : IsGraphProperty P) :
    MulAction.IsPretransitive (Cslib.BitString.aut (graphPropertyFn P))
      (Fin (Cslib.BitString.Graph.edgeCount v)) := by
  classical
  rw [Cslib.BitString.isPretransitive_aut_iff]
  intro i j
  let e₁ := (Cslib.BitString.Graph.edgeEquiv v).symm i
  let e₂ := (Cslib.BitString.Graph.edgeEquiv v).symm j
  obtain ⟨u₁, w₁, hu₁⟩ : ∃ a b, s(a, b) = e₁.1 := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₁.1
  obtain ⟨u₂, w₂, hu₂⟩ : ∃ a b, s(a, b) = e₂.1 := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₂.1
  have hne₁ : u₁ ≠ w₁ := by
    intro h; subst h; exact e₁.2 (hu₁ ▸ by simp)
  have hne₂ : u₂ ≠ w₂ := by
    intro h; subst h; exact e₂.2 (hu₂ ▸ by simp)
  let S₁ : Finset (Fin v) := {u₁, w₁}
  let S₂ : Finset (Fin v) := {u₂, w₂}
  have hcardS₁ : S₁.card = 2 := Finset.card_pair hne₁
  have hcardS₂ : S₂.card = 2 := Finset.card_pair hne₂
  have hcardC : Fintype.card {a : Fin v // a ∉ S₁} = Fintype.card {a : Fin v // a ∉ S₂} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hcardS₁, hcardS₂]
  obtain ⟨eC⟩ := Fintype.card_eq.mp hcardC
  let eS : {a : Fin v // a ∈ S₁} ≃ {a : Fin v // a ∈ S₂} :=
    { toFun := fun a =>
        if a.1 = u₁ then ⟨u₂, by simp [S₂]⟩ else ⟨w₂, by simp [S₂]⟩
      invFun := fun b =>
        if b.1 = u₂ then ⟨u₁, by simp [S₁]⟩ else ⟨w₁, by simp [S₁]⟩
      left_inv := fun ⟨a, ha⟩ => by
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · simp
        · have ha_eq : a = w₁ := Finset.mem_singleton.mp ha'
          subst ha_eq
          simp [hne₁.symm, hne₂.symm]
      right_inv := fun ⟨b, hb⟩ => by
        rcases Finset.mem_insert.mp hb with rfl | hb'
        · simp
        · have hb_eq : b = w₂ := Finset.mem_singleton.mp hb'
          subst hb_eq
          simp [hne₂.symm, hne₁.symm] }
  let τ : Equiv.Perm (Fin v) := eS.subtypeCongr eC
  have hτ_u : τ u₁ = u₂ := by
    simp [τ, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos, eS, S₁]
  have hτ_w : τ w₁ = w₂ := by
    have hw₁ : w₁ ∈ S₁ := by simp [S₁]
    simp [τ, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos, hw₁, eS, hne₁.symm]
  let πEdge : Equiv.Perm (Cslib.BitString.Graph.Edge v) :=
    { toFun := fun e => ⟨Sym2.map τ e.1, by
        intro hd
        obtain ⟨a, b, hab_eq⟩ : ∃ a b, s(a, b) = e.1 := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e.1
        apply e.2
        rw [← hab_eq] at hd ⊢
        change s(τ a, τ b).IsDiag at hd
        simpa [τ.injective.eq_iff] using hd⟩
      invFun := fun e => ⟨Sym2.map τ.symm e.1, by
        intro hd
        obtain ⟨a, b, hab_eq⟩ : ∃ a b, s(a, b) = e.1 := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e.1
        apply e.2
        rw [← hab_eq] at hd ⊢
        change s(τ.symm a, τ.symm b).IsDiag at hd
        simpa [τ.symm.injective.eq_iff] using hd⟩
      left_inv := fun e => by ext1; simp [Sym2.map_map]
      right_inv := fun e => by ext1; simp [Sym2.map_map] }
  let π : Equiv.Perm (Fin (Cslib.BitString.Graph.edgeCount v)) :=
    (Cslib.BitString.Graph.edgeEquiv v).symm.trans
      (πEdge.trans (Cslib.BitString.Graph.edgeEquiv v))
  refine ⟨π, ?_, ?_⟩
  · have hmap : πEdge e₁ = e₂ := by
      ext1
      change Sym2.map τ e₁.1 = e₂.1
      rw [← hu₁, ← hu₂]
      change s(τ u₁, τ w₁) = s(u₂, w₂)
      rw [hτ_u, hτ_w]
    simp [π, e₁, e₂, hmap]
  · intro x
    have hiso : Nonempty (Cslib.BitString.Graph.graph (fun k => x (π k)) ≃g
        Cslib.BitString.Graph.graph x) := by
      refine ⟨{
        toEquiv := τ
        map_rel_iff' := fun {a b} => by
          by_cases hab : a = b
          · subst hab; simp
          · have hτab : τ a ≠ τ b := fun h => hab (τ.injective h)
            rw [Cslib.BitString.Graph.graph_adj hab, Cslib.BitString.Graph.graph_adj hτab]
            have hπ_edge :
                π (Cslib.BitString.Graph.edgeEquiv v (Cslib.BitString.Graph.edge hab)) =
                  Cslib.BitString.Graph.edgeEquiv v (Cslib.BitString.Graph.edge hτab) := by
              simp [π, πEdge, Cslib.BitString.Graph.edge]
            rw [hπ_edge] }⟩
    have hiff := hP _ _ hiso
    exact Bool.eq_iff_iff.mpr (by simpa [graphPropertyFn_apply] using hiff)

/-- Distributional and zero-error randomized query-complexity lower bound for any nontrivial
monotone `v`-vertex graph property `P` at its critical probability `p ∈ (0, 1)`:
`((v : ℝ) - 1)^{4/3} / (16 p (1 - p))^{1/3} ≤ Δ_p(f_P) ≤ R_0(f_P)`. -/
theorem graphProperty_rpow_le_minExpectedQueriesBool {v : ℕ} {p : ℝ}
    {P : SimpleGraph (Fin v) → Prop} (hP : IsGraphProperty P)
    (hmono : Monotone (graphPropertyFn P))
    (hnc : ∃ x y, graphPropertyFn P x ≠ graphPropertyFn P y)
    (hp : IsCriticalProb p (graphPropertyFn P)) :
    ((v : ℝ) - 1) ^ ((4 : ℝ) / 3) / (16 * p * (1 - p)) ^ ((1 : ℝ) / 3) ≤
        minExpectedQueriesBool hp.pos.le hp.lt_one.le (graphPropertyFn P) ∧
      minExpectedQueriesBool hp.pos.le hp.lt_one.le (graphPropertyFn P) ≤
        Cslib.QueryComplexity.zeroErrorComplexity (graphPropertyFn P) := by
  let _ := isPretransitive_aut_graphPropertyFn hP
  obtain ⟨hlow, hup⟩ := card_rpow_div_le_minExpectedQueriesBool_of_isPretransitive hmono hnc hp
  refine ⟨le_trans ?_ hlow, hup⟩
  have hv2 : 2 ≤ v := by
    by_contra hlt
    have hv1 : v ≤ 1 := by omega
    have hcard0 : Cslib.BitString.Graph.edgeCount v = 0 := by
      rw [Cslib.BitString.Graph.edgeCount_eq_choose]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv1 with rfl | rfl <;> rfl
    obtain ⟨x, y, hxy⟩ := hnc
    have hsub : Subsingleton (Fin (Cslib.BitString.Graph.edgeCount v) → Bool) := by
      rw [hcard0]; infer_instance
    exact hxy (congrArg _ (Subsingleton.elim x y))
  have hv1_nn : (0 : ℝ) ≤ (v : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast (show 1 ≤ v by omega)
    linarith
  have h4pq : 0 < 4 * p * (1 - p) := by
    have := hp.pos; have := sub_pos.mpr hp.lt_one; positivity
  have hcard_ge : ((v : ℝ) - 1) ^ 2 / 2 ≤
      (Fintype.card (Fin (Cslib.BitString.Graph.edgeCount v)) : ℝ) := by
    rw [Fintype.card_fin, Cslib.BitString.Graph.edgeCount_eq_choose, Nat.choose_two_right]
    have hcast : (↑(v * (v - 1) / 2) : ℝ) = (v : ℝ) * ((v : ℝ) - 1) / 2 := by
      obtain ⟨m, hm⟩ := Nat.even_mul_pred_self v |>.two_dvd
      have hdiv : v * (v - 1) / 2 = m := by omega
      have hmR : (2 : ℝ) * (m : ℝ) = (v : ℝ) * ((v : ℝ) - 1) := by
        have : ((v * (v - 1) : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) := congrArg Nat.cast hm
        rwa [Nat.cast_mul, Nat.cast_sub (show 1 ≤ v by omega), Nat.cast_one, Nat.cast_mul,
          Nat.cast_ofNat, eq_comm] at this
      rw [hdiv]
      linarith
    rw [hcast]
    nlinarith
  have hrpow :
      (((v : ℝ) - 1) ^ 2 / 2) ^ ((2 : ℝ) / 3) ≤
        (Fintype.card (Fin (Cslib.BitString.Graph.edgeCount v)) : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hcard_ge (by norm_num)
  have hnum :
      (((v : ℝ) - 1) ^ 2 / 2) ^ ((2 : ℝ) / 3) =
        ((v : ℝ) - 1) ^ ((4 : ℝ) / 3) / (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.div_rpow (sq_nonneg _) (by norm_num), ← Real.rpow_natCast ((v : ℝ) - 1) 2,
      ← Real.rpow_mul hv1_nn]
    norm_num
    congr 1
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hden :
      (4 : ℝ) ^ ((1 : ℝ) / 3) * (4 * p * (1 - p)) ^ ((1 : ℝ) / 3) =
        (16 * p * (1 - p)) ^ ((1 : ℝ) / 3) := by
    rw [← Real.mul_rpow (by norm_num) h4pq.le]
    ring_nf
  rw [hnum] at hrpow
  calc ((v : ℝ) - 1) ^ ((4 : ℝ) / 3) / (16 * p * (1 - p)) ^ ((1 : ℝ) / 3)
      = (((v : ℝ) - 1) ^ ((4 : ℝ) / 3) / (4 : ℝ) ^ ((1 : ℝ) / 3)) /
          (4 * p * (1 - p)) ^ ((1 : ℝ) / 3) := by
        rw [div_div, hden]
    _ ≤ (Fintype.card (Fin (Cslib.BitString.Graph.edgeCount v)) : ℝ) ^ ((2 : ℝ) / 3) /
          (4 * p * (1 - p)) ^ ((1 : ℝ) / 3) :=
        div_le_div_of_nonneg_right hrpow (Real.rpow_nonneg h4pq.le _)

end MonotoneBounds

end CslibFrontier.DecisionTree
