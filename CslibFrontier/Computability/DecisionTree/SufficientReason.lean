/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Event
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Partial Evaluations and Sufficient Reasons for Decision Trees

Extends Boolean decision trees (`Cslib.DecisionTree`) to partial assignments
(`Cslib.BitString.PartialAssignment`) and defines `δ`-sufficient reasons (probabilistic local
explanations) for binary classifications over finite coordinate types:

* Given a partial assignment `y : PartialAssignment ι`, `completions y` is the finite set of
  complete inputs `x : ι → Bool` consistent with `y`, of cardinality `2 ^ #{i | y i = none}`.
* `DecisionTree.evalProb T y` evaluates the fraction of completions of `y` on which `T` outputs
  `true`, and `evalProb_eq_completionPMF` equates this combinatorial ratio with the probability
  under the product distribution `completionPMF y` that samples undefined coordinates
  independently and uniformly at random.
* `DecisionTree.IsSufficientReason T x δ S` states that at least a fraction `δ` of complete inputs
  agreeing with `x` on `S : Finset ι` satisfy `T.eval z = T.eval x`.
* `DecisionTree.queriesSet` and `DecisionTree.bind` provide structural variable-support tracking,
  leaf-substitution composition, and the read-once node splitting identity
  `evalProb_node_of_not_mem`.

## Main definitions

* `Cslib.DecisionTree.Consistent`, `Cslib.DecisionTree.completions`: consistency and completion
  sets for partial Boolean assignments.
* `Cslib.DecisionTree.evalProb`, `Cslib.DecisionTree.completionPMF`: extended evaluation on partial
  inputs and its independent product `PMF`.
* `Cslib.DecisionTree.IsSufficientReason`, `Cslib.DecisionTree.restrictToSet`: `δ`-sufficient
  reasons for an input `x` under a decision tree `T`.
* `Cslib.DecisionTree.queriesSet`, `Cslib.DecisionTree.bind`: structural variable set and monadic
  leaf substitution.

## Main results

* `Cslib.DecisionTree.card_completions_eq_two_pow`: `|(completions y)| = 2 ^ #{i | y i = none}`.
* `Cslib.DecisionTree.evalProb_eq_completionPMF`: counting vs. product-measure equivalence for
  partial evaluations.
* `Cslib.DecisionTree.isSufficientReason_iff_evalProb`,
  `Cslib.DecisionTree.isSufficientReason_iff_completionPMF`: equivalences between `δ`-sufficient
  reasons and partial-input completion probabilities.
* `Cslib.DecisionTree.evalProb_node_of_not_mem`: exact branching formula for `evalProb` when a
  queried variable does not reappear in either child subtree.
-/

public section

namespace Cslib.DecisionTree

open Cslib.BitString Cslib.Probability

section Structural

variable {ι β γ : Type*}

/-- Leaf substitution (monadic bind) for decision trees: replace each leaf `b` by `g b`. -/
@[expose] def bind : DecisionTree ι β → (β → DecisionTree ι γ) → DecisionTree ι γ
  | .leaf b, g => g b
  | .node i t₀ t₁, g => .node i (t₀.bind g) (t₁.bind g)

/-- Evaluating `t.bind g` on `x` evaluates `g (t.eval x)` on `x`. -/
@[simp] theorem eval_bind (t : DecisionTree ι β) (g : β → DecisionTree ι γ)
    (x : ι → Bool) :
    (t.bind g).eval x = (g (t.eval x)).eval x := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => cases h : x i <;> simp [bind, h, ih₀, ih₁]

/-- Set of all variables appearing at any internal node of a decision tree. -/
@[expose] def queriesSet [DecidableEq ι] : DecisionTree ι β → Finset ι
  | .leaf _ => ∅
  | .node i t₀ t₁ => insert i (t₀.queriesSet ∪ t₁.queriesSet)

/-- Evaluating a decision tree depends only on the coordinates in `queriesSet`. -/
theorem eval_eq_of_eq_on_queriesSet [DecidableEq ι] (t : DecisionTree ι β)
    {x x' : ι → Bool} (h : ∀ i ∈ t.queriesSet, x i = x' i) :
    t.eval x = t.eval x' := by
  induction t with
  | leaf _ => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [eval_node]
    have hi : x i = x' i := h i (by simp [queriesSet])
    rw [hi]
    cases x' i
    · simp only [Bool.cond_false]
      exact ih₀ fun j hj => h j (by simp [queriesSet, hj])
    · simp only [Bool.cond_true]
      exact ih₁ fun j hj => h j (by simp [queriesSet, hj])

/-- Variables queried along any execution path belong to `queriesSet`. -/
theorem queries_subset_queriesSet [DecidableEq ι] (t : DecisionTree ι β) (x : ι → Bool) :
    t.queries x ⊆ t.queriesSet := by
  induction t with
  | leaf _ => simp
  | node i t₀ t₁ ih₀ ih₁ =>
    intro j hj
    simp only [queries_node, queriesSet, Finset.mem_insert, Finset.mem_union] at hj ⊢
    rcases hj with rfl | hj'
    · exact Or.inl rfl
    · cases hx : x i
      · rw [hx, Bool.cond_false] at hj'
        exact Or.inr (Or.inl (ih₀ hj'))
      · rw [hx, Bool.cond_true] at hj'
        exact Or.inr (Or.inr (ih₁ hj'))

/-- `queriesSet` of a leaf substitution `t.bind g` is contained in `t.queriesSet` together with
the `queriesSet` of `g false` and `g true`. -/
theorem queriesSet_bind_subset [DecidableEq ι] (t : DecisionTree ι Bool)
    (g : Bool → DecisionTree ι β) :
    (t.bind g).queriesSet ⊆ t.queriesSet ∪ (g false).queriesSet ∪ (g true).queriesSet := by
  induction t with
  | leaf b =>
    cases b <;> intro j hj <;> simp only [bind, queriesSet, Finset.mem_union] at hj ⊢ <;> tauto
  | node i t₀ t₁ ih₀ ih₁ =>
    intro j hj
    simp only [bind, queriesSet, Finset.mem_insert, Finset.mem_union] at hj ⊢
    rcases hj with rfl | h₀ | h₁
    · left; left; left; rfl
    · have := ih₀ h₀; simp only [Finset.mem_union] at this; tauto
    · have := ih₁ h₁; simp only [Finset.mem_union] at this; tauto

end Structural

section PartialEvaluation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A complete assignment `x : ι → Bool` is consistent with a partial assignment
`y : PartialAssignment ι` when `x` agrees with `y` at every defined coordinate. -/
@[expose] def Consistent (x : ι → Bool) (y : PartialAssignment ι) : Prop :=
  ∀ i : ι, ∀ b : Bool, y i = some b → x i = b

instance instDecidableConsistent (x : ι → Bool) (y : PartialAssignment ι) :
    Decidable (Consistent x y) := by
  unfold Consistent
  infer_instance

/-- The finite set of complete Boolean assignments consistent with `y`. -/
@[expose] def completions (y : PartialAssignment ι) : Finset (ι → Bool) :=
  Finset.univ.filter fun x => Consistent x y

/-- Every partial assignment has at least one completion. -/
theorem completions_nonempty (y : PartialAssignment ι) : (completions y).Nonempty := by
  refine ⟨fun i => (y i).getD false, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i b hb => ?_⟩⟩
  simp [hb]

/-- Every partial assignment has a positive number of completions. -/
theorem card_completions_pos (y : PartialAssignment ι) : 0 < (completions y).card :=
  Finset.card_pos.2 (completions_nonempty y)

/-- The number of completions of `y` equals `2 ^ #{i | y i = none}`. -/
theorem card_completions_eq_two_pow (y : PartialAssignment ι) :
    (completions y).card = 2 ^ (Finset.univ.filter fun i : ι => y i = none).card := by
  let freeSet := Finset.univ.filter fun i : ι => y i = none
  let φ : (↥freeSet → Bool) → ι → Bool := fun f i =>
    if h : y i = none then f ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩⟩
    else (y i).getD false
  have hmem : ∀ f, φ f ∈ completions y := fun f => by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i b hb => ?_⟩
    simp [φ, hb]
  have hinj : Function.Injective φ := fun f g hfg => by
    funext ⟨i, hi⟩
    have hnone : y i = none := (Finset.mem_filter.1 hi).2
    have := congrFun hfg i
    simpa [φ, hnone] using this
  have hsurj : ∀ x ∈ completions y, ∃ f, φ f = x := fun x hx => by
    have hcons := (Finset.mem_filter.1 hx).2
    refine ⟨fun ⟨i, _⟩ => x i, funext fun i => ?_⟩
    dsimp only [φ]
    split_ifs with h
    · rfl
    · cases hy : y i with
      | none => exact absurd hy h
      | some b =>
        simp only [Option.getD_some]
        exact (hcons i b hy).symm
  have hcard : Finset.univ.image φ = completions y := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨f, hf⟩ => hf ▸ hmem f, hsurj x⟩
  rw [← hcard, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe]

/-- Extended evaluation `T.evalProb y` of a Boolean decision tree `T` on a partial assignment `y`:
the fraction of completions of `y` on which `T` evaluates to `true`. -/
@[expose] noncomputable def evalProb (T : DecisionTree ι Bool) (y : PartialAssignment ι) : ℝ :=
  (((completions y).filter fun x => T.eval x = true).card : ℝ) / ((completions y).card : ℝ)

/-- `0 ≤ T.evalProb y`. -/
theorem evalProb_nonneg (T : DecisionTree ι Bool) (y : PartialAssignment ι) :
    0 ≤ T.evalProb y := by
  unfold evalProb
  positivity

/-- `T.evalProb y ≤ 1`. -/
theorem evalProb_le_one (T : DecisionTree ι Bool) (y : PartialAssignment ι) :
    T.evalProb y ≤ 1 := by
  unfold evalProb
  have hpos : (0 : ℝ) < (completions y).card := Nat.cast_pos.2 (card_completions_pos y)
  rw [div_le_one hpos]
  exact_mod_cast Finset.card_filter_le (completions y) _

/-- Evaluating a constant leaf `.leaf b` on any partial assignment gives `1` if `b` and `0`
otherwise. -/
theorem evalProb_leaf (b : Bool) (y : PartialAssignment ι) :
    (leaf b : DecisionTree ι Bool).evalProb y = if b then 1 else 0 := by
  unfold evalProb
  have hpos : (0 : ℝ) < (completions y).card := Nat.cast_pos.2 (card_completions_pos y)
  cases b
  · simp
  · simp [div_self hpos.ne']

/-- Evaluating on a complete assignment `x` (viewed as `fun i => some (x i)`) agrees with
`T.eval x`. -/
theorem evalProb_some (T : DecisionTree ι Bool) (x : ι → Bool) :
    T.evalProb (fun i => some (x i)) = if T.eval x = true then 1 else 0 := by
  have hcomp : completions (fun i => some (x i)) = {x} := by
    ext z
    simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Consistent, Option.some.injEq]
    exact ⟨fun h => funext fun i => h i (x i) rfl, fun h i b hb => hb ▸ congrFun h i⟩
  unfold evalProb
  rw [hcomp]
  cases h : T.eval x <;> simp [Finset.filter_singleton, h]

/-- Coordinate `PMF` for a partial assignment entry: point mass at `b` when fixed to `some b`, and
uniform over `Bool` when `none`. -/
@[expose] noncomputable def coordPMF : Option Bool → PMF Bool
  | some b => PMF.pure b
  | none => PMF.uniformOfFintype Bool

/-- Product `PMF` over `ι → Bool` sampling undefined coordinates of `y` independently and
uniformly at random. -/
@[expose] noncomputable def completionPMF (y : PartialAssignment ι) : PMF (ι → Bool) :=
  PMF.pi fun i => coordPMF (y i)

/-- `completionPMF y` is uniform over `completions y` and zero outside `completions y`. -/
theorem completionPMF_apply (y : PartialAssignment ι) (x : ι → Bool) :
    completionPMF y x =
      if Consistent x y then (((completions y).card : ENNReal)⁻¹) else 0 := by
  classical
  have hprod : completionPMF y x = ∏ i : ι, coordPMF (y i) (x i) :=
    PMF.pi_apply (fun i => coordPMF (y i)) x
  rw [hprod]
  by_cases hx : Consistent x y
  · rw [ite_eq_left hx, card_completions_eq_two_pow]
    have hsplit : ∏ i : ι, coordPMF (y i) (x i) =
        (∏ i ∈ Finset.univ.filter (fun i : ι => y i = none), (2 : ENNReal)⁻¹) *
        (∏ i ∈ Finset.univ.filter (fun i : ι => ¬(y i = none)), (1 : ENNReal)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => y i = none)]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hnone : y i = none := (Finset.mem_filter.1 hi).2
        simp [coordPMF, hnone]
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hne : y i ≠ none := (Finset.mem_filter.1 hi).2
        cases hy : y i with
        | none => exact absurd hy hne
        | some b =>
          have hxb : x i = b := hx i b hy
          simp [coordPMF, hxb]
    rw [hsplit, Finset.prod_const_one, mul_one, Finset.prod_const, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.inv_pow]
  · rw [ite_eq_right hx]
    simp only [Consistent, not_forall] at hx
    obtain ⟨i, b, hy, hxb⟩ := hx
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [coordPMF, hy, hxb]

/-- `T.evalProb y` equals the probability under `completionPMF y` that `T.eval x = true`. -/
theorem evalProb_eq_completionPMF (T : DecisionTree ι Bool) (y : PartialAssignment ι) :
    T.evalProb y = ((completionPMF y).toOuterMeasure {x | T.eval x = true}).toReal := by
  classical
  rw [PMF.toOuterMeasure_toReal_eq_sum_ite]
  simp_rw [mul_ite, mul_one, mul_zero]
  have hsum : ∑ x : ι → Bool,
        (if x ∈ {z | T.eval z = true} then (completionPMF y x).toReal else 0) =
      ∑ x ∈ (completions y).filter (fun z => T.eval z = true),
        (((completions y).card : ℝ)⁻¹) := by
    rw [← Finset.sum_filter]
    trans ∑ x ∈ Finset.univ.filter (fun x : ι → Bool => T.eval x = true),
        (if Consistent x y then (((completions y).card : ℝ)⁻¹) else 0)
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [completionPMF_apply]
      by_cases hx : Consistent x y <;> simp [hx]
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x; simp [completions, and_comm]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
  rfl

private theorem evalProb_update_of_not_mem (t : DecisionTree ι Bool)
    (y : PartialAssignment ι) {i : ι} (hi : i ∉ t.queriesSet) (b : Bool) (hyi : y i = none) :
    t.evalProb (Function.update y i (some b)) = t.evalProb y := by
  let y' := Function.update y i (some b)
  let flip (x : ι → Bool) : ι → Bool := Function.update x i (!x i)
  have hflip_inv : ∀ x, flip (flip x) = x := fun x => by
    funext j
    by_cases hj : j = i
    · subst hj; simp [flip]
    · simp [flip, hj]
  have hflip_eval : ∀ x, t.eval (flip x) = t.eval x := fun x =>
    eval_eq_of_eq_on_queriesSet t fun j hj => by
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      simp [flip, hne]
  have hcomp_eq : completions y' = (completions y).filter fun x => x i = b := by
    ext x
    simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨fun j c hj => ?_, h i b (by simp [y'])⟩
      by_cases hji : j = i
      · subst hji; simp [hyi] at hj
      · exact h j c (by simp [y', hji, hj])
    · rintro ⟨h, hxi⟩ j c hj
      by_cases hji : j = i
      · subst hji
        simp only [y', Function.update_self, Option.some.injEq] at hj
        exact hj ▸ hxi
      · simp only [y', Function.update_of_ne hji] at hj
        exact h j c hj
  have hcard_half : (completions y).card = 2 * (completions y').card := by
    rw [card_completions_eq_two_pow, card_completions_eq_two_pow]
    have hset : (Finset.univ.filter fun j : ι => y' j = none) =
        (Finset.univ.filter fun j : ι => y j = none).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, y']
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    have hmem : i ∈ Finset.univ.filter fun j : ι => y j = none :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hyi⟩
    rw [hset, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ (Finset.univ.filter fun j : ι => y j = none).card :=
      Finset.card_pos.2 ⟨i, hmem⟩
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  have hgood_half : ((completions y).filter fun x => t.eval x = true).card =
      2 * ((completions y').filter fun x => t.eval x = true).card := by
    have hpart : ((completions y).filter fun x => t.eval x = true) =
        ((completions y).filter fun x => t.eval x = true ∧ x i = b) ∪
        ((completions y).filter fun x => t.eval x = true ∧ x i = !b) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨hx, ht⟩; cases hxb : x i <;> cases b <;> simp_all
      · rintro (⟨hx, ht, _⟩ | ⟨hx, ht, _⟩) <;> exact ⟨hx, ht⟩
    have hdisj : Disjoint ((completions y).filter fun x => t.eval x = true ∧ x i = b)
        ((completions y).filter fun x => t.eval x = true ∧ x i = !b) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have hb1 := (Finset.mem_filter.1 h1).2.2
      have hb2 := (Finset.mem_filter.1 h2).2.2
      rw [hb1] at hb2; cases b <;> simp at hb2
    have hbij : ((completions y).filter fun x => t.eval x = true ∧ x i = !b).card =
        ((completions y).filter fun x => t.eval x = true ∧ x i = b).card := by
      refine Finset.card_bij (fun x _ => flip x) (fun x hx => ?_)
        (fun x₁ _ x₂ _ h => by have := congrArg flip h; simpa [hflip_inv] using this)
        (fun x hx => ⟨flip x, ?_, hflip_inv x⟩)
      · obtain ⟨hx, ht, hxi⟩ := Finset.mem_filter.1 hx
        refine Finset.mem_filter.2 ⟨?_, by rwa [hflip_eval], by simp [flip, hxi]⟩
        simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        intro j c hj
        by_cases hji : j = i
        · subst hji; simp [hyi] at hj
        · simpa [flip, hji] using hx j c hj
      · obtain ⟨hx, ht, hxi⟩ := Finset.mem_filter.1 hx
        refine Finset.mem_filter.2 ⟨?_, by rwa [hflip_eval], by simp [flip, hxi]⟩
        simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        intro j c hj
        by_cases hji : j = i
        · subst hji; simp [hyi] at hj
        · simpa [flip, hji] using hx j c hj
    have heq1 : ((completions y).filter fun x => t.eval x = true ∧ x i = b) =
        ((completions y').filter fun x => t.eval x = true) := by
      rw [hcomp_eq]; ext x; simp only [Finset.mem_filter]; tauto
    rw [hpart, Finset.card_union_of_disjoint hdisj, hbij, heq1, two_mul]
  unfold evalProb
  dsimp only [y'] at hgood_half hcard_half
  rw [hgood_half, hcard_half, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- Read-once branching identity for `evalProb`: if `i` is not queried in `t₀` or `t₁`, then
`(node i t₀ t₁).evalProb y` equals `t₀.evalProb y` when `y i = some false`, `t₁.evalProb y` when
`y i = some true`, and their average `(t₀.evalProb y + t₁.evalProb y) / 2` when `y i = none`. -/
theorem evalProb_node_of_not_mem {i : ι} {t₀ t₁ : DecisionTree ι Bool}
    (h₀ : i ∉ t₀.queriesSet) (h₁ : i ∉ t₁.queriesSet) (y : PartialAssignment ι) :
    (node i t₀ t₁).evalProb y =
      match y i with
      | some false => t₀.evalProb y
      | some true => t₁.evalProb y
      | none => (t₀.evalProb y + t₁.evalProb y) / 2 := by
  cases hy : y i with
  | some b =>
    cases b
    · have heq : ((completions y).filter fun x => (node i t₀ t₁).eval x = true) =
          ((completions y).filter fun x => t₀.eval x = true) := by
        ext x
        simp only [Finset.mem_filter, completions, Finset.mem_univ, true_and]
        refine and_congr_right fun hx => ?_
        simp [hx i false hy]
      unfold evalProb; rw [heq]
    · have heq : ((completions y).filter fun x => (node i t₀ t₁).eval x = true) =
          ((completions y).filter fun x => t₁.eval x = true) := by
        ext x
        simp only [Finset.mem_filter, completions, Finset.mem_univ, true_and]
        refine and_congr_right fun hx => ?_
        simp [hx i true hy]
      unfold evalProb; rw [heq]
  | none =>
    let y₀ := Function.update y i (some false)
    let y₁ := Function.update y i (some true)
    have hcomp0 : completions y₀ = (completions y).filter fun x => x i = false := by
      ext x
      simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨fun j c hj => ?_, h i false (by simp [y₀])⟩
        by_cases hji : j = i
        · subst hji; simp [hy] at hj
        · exact h j c (by simp [y₀, hji, hj])
      · rintro ⟨h, hxi⟩ j c hj
        by_cases hji : j = i
        · subst hji; simp only [y₀, Function.update_self, Option.some.injEq] at hj; exact hj ▸ hxi
        · simp only [y₀, Function.update_of_ne hji] at hj; exact h j c hj
    have hcomp1 : completions y₁ = (completions y).filter fun x => x i = true := by
      ext x
      simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨fun j c hj => ?_, h i true (by simp [y₁])⟩
        by_cases hji : j = i
        · subst hji; simp [hy] at hj
        · exact h j c (by simp [y₁, hji, hj])
      · rintro ⟨h, hxi⟩ j c hj
        by_cases hji : j = i
        · subst hji; simp only [y₁, Function.update_self, Option.some.injEq] at hj; exact hj ▸ hxi
        · simp only [y₁, Function.update_of_ne hji] at hj; exact h j c hj
    have hcard0 : (completions y).card = 2 * (completions y₀).card := by
      rw [card_completions_eq_two_pow, card_completions_eq_two_pow]
      have hset : (Finset.univ.filter fun j : ι => y₀ j = none) =
          (Finset.univ.filter fun j : ι => y j = none).erase i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, y₀]
        by_cases hji : j = i <;> [subst hji; skip] <;> simp [*]
      have hmem : i ∈ Finset.univ.filter fun j : ι => y j = none :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
      rw [hset, Finset.card_erase_of_mem hmem]
      have hpos : 1 ≤ (Finset.univ.filter fun j : ι => y j = none).card :=
        Finset.card_pos.2 ⟨i, hmem⟩
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    have hcard1 : (completions y).card = 2 * (completions y₁).card := by
      rw [card_completions_eq_two_pow, card_completions_eq_two_pow]
      have hset : (Finset.univ.filter fun j : ι => y₁ j = none) =
          (Finset.univ.filter fun j : ι => y j = none).erase i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, y₁]
        by_cases hji : j = i <;> [subst hji; skip] <;> simp [*]
      have hmem : i ∈ Finset.univ.filter fun j : ι => y j = none :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
      rw [hset, Finset.card_erase_of_mem hmem]
      have hpos : 1 ≤ (Finset.univ.filter fun j : ι => y j = none).card :=
        Finset.card_pos.2 ⟨i, hmem⟩
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    have hsplit_good : ((completions y).filter fun x => (node i t₀ t₁).eval x = true).card =
        ((completions y₀).filter fun x => t₀.eval x = true).card +
        ((completions y₁).filter fun x => t₁.eval x = true).card := by
      have hpart : ((completions y).filter fun x => (node i t₀ t₁).eval x = true) =
          ((completions y₀).filter fun x => t₀.eval x = true) ∪
          ((completions y₁).filter fun x => t₁.eval x = true) := by
        rw [hcomp0, hcomp1]
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, eval_node]
        cases hxi : x i <;> simp [hxi]
      have hdisj : Disjoint ((completions y₀).filter fun x => t₀.eval x = true)
          ((completions y₁).filter fun x => t₁.eval x = true) := by
        rw [hcomp0, hcomp1, Finset.disjoint_left]
        intro x h1 h2
        have hb0 := (Finset.mem_filter.1 (Finset.mem_filter.1 h1).1).2
        have hb1 := (Finset.mem_filter.1 (Finset.mem_filter.1 h2).1).2
        rw [hb0] at hb1; cases hb1
      rw [hpart, Finset.card_union_of_disjoint hdisj]
    have hev0 : t₀.evalProb y₀ = t₀.evalProb y := evalProb_update_of_not_mem t₀ y h₀ false hy
    have hev1 : t₁.evalProb y₁ = t₁.evalProb y := evalProb_update_of_not_mem t₁ y h₁ true hy
    rw [← hev0, ← hev1]
    unfold evalProb
    have hc0 : ((completions y₀).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (card_completions_pos y₀).ne'
    have hc1_eq : (completions y₁).card = (completions y₀).card := by omega
    rw [hsplit_good, hcard0, hc1_eq]
    push_cast
    field_simp [hc0]

/-! ### `δ`-Sufficient reasons -/

/-- A subset `S : Finset ι` of coordinates is a `δ`-sufficient reason for an input `x : ι → Bool`
under a decision tree `T` when at least a fraction `δ` of complete assignments agreeing with `x`
on `S` produce the same classification `T.eval z = T.eval x`. -/
@[expose] def IsSufficientReason (T : DecisionTree ι Bool) (x : ι → Bool) (δ : ℝ)
    (S : Finset ι) : Prop :=
  δ ≤ (((Finset.univ.filter fun z : ι → Bool =>
          (∀ i ∈ S, z i = x i) ∧ T.eval z = T.eval x).card : ℝ) /
        ((Finset.univ.filter fun z : ι → Bool => ∀ i ∈ S, z i = x i).card : ℝ))

/-- The partial assignment fixing coordinates in `S` to `x` and leaving coordinates outside `S`
undefined (`none`). -/
@[expose] def restrictToSet (x : ι → Bool) (S : Finset ι) : PartialAssignment ι :=
  fun i => if i ∈ S then some (x i) else none

/-- Completions of `restrictToSet x S` are the complete assignments agreeing with `x` on `S`. -/
theorem completions_restrictToSet (x : ι → Bool) (S : Finset ι) :
    completions (restrictToSet x S) =
      Finset.univ.filter fun z : ι → Bool => ∀ i ∈ S, z i = x i := by
  ext z
  rw [completions, Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Consistent, restrictToSet]
  constructor
  · intro h i hi; exact h i (x i) (ite_eq_left hi)
  · intro h i b hb
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi] at hb; cases hb; exact h i hi
    · rw [ite_eq_right hi] at hb; cases hb

/-- When `T.eval x = true`, `S` is a `δ`-sufficient reason for `x` under `T` iff
`δ ≤ T.evalProb (restrictToSet x S)`. -/
theorem isSufficientReason_iff_evalProb {T : DecisionTree ι Bool} {x : ι → Bool}
    (hx : T.eval x = true) {δ : ℝ} {S : Finset ι} :
    T.IsSufficientReason x δ S ↔ δ ≤ T.evalProb (restrictToSet x S) := by
  unfold IsSufficientReason evalProb
  rw [completions_restrictToSet, Finset.filter_filter, hx]

/-- Probabilistic characterization of `δ`-sufficient reasons via `completionPMF`. -/
theorem isSufficientReason_iff_completionPMF {T : DecisionTree ι Bool} {x : ι → Bool}
    (hx : T.eval x = true) {δ : ℝ} {S : Finset ι} :
    T.IsSufficientReason x δ S ↔
      δ ≤ ((completionPMF (restrictToSet x S)).toOuterMeasure {z | T.eval z = true}).toReal := by
  rw [isSufficientReason_iff_evalProb hx, evalProb_eq_completionPMF]

/-- The full coordinate set `Finset.univ` is always a `1`-sufficient reason for any input `x`. -/
theorem isSufficientReason_univ (T : DecisionTree ι Bool) (x : ι → Bool) :
    T.IsSufficientReason x 1 Finset.univ := by
  have heq : (Finset.univ.filter fun z : ι → Bool => ∀ i ∈ (Finset.univ : Finset ι), z i = x i) =
      {x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => funext fun i => h i trivial, fun h i _ => congrFun h i⟩
  have hnum : (Finset.univ.filter fun z : ι → Bool =>
      (∀ i ∈ (Finset.univ : Finset ι), z i = x i) ∧ T.eval z = T.eval x) = {x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨h, _⟩ => funext fun i => h i trivial,
      fun h => ⟨fun i _ => congrFun h i, by rw [h]⟩⟩
  unfold IsSufficientReason
  rw [heq, hnum]
  simp

end PartialEvaluation

end Cslib.DecisionTree
