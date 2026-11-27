/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Composition
public import CslibFrontier.Computability.DecisionTree.Dual
public import CslibFrontier.Computability.DecisionTree.Leaves
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ehrenfeucht–Haussler Decision Tree Rank, Leaf Size, and Weighted Complexity

For a binary decision tree `t : Cslib.DecisionTree ι β`, the Ehrenfeucht–Haussler (Strahler) rank
`t.rank` measures branching complexity, `t.leafCount` counts structural leaves, and
`t.weightedDepth w` measures worst-case root-to-leaf query cost under weights `w : ι → ℕ`. This
module develops constructive tree reduction (eliminating repeated queries along every root-to-leaf
path without increasing depth, leaf count, rank, or weighted depth), subtree-context monotonicity,
leaf-grafting rank laws, and the induced Boolean function measures `sizeComplexity`,
`rankComplexity`, and `weightedComplexity`, culminating in the Ehrenfeucht–Haussler rank-size
sandwich
`rankComplexity f ≤ log₂(sizeComplexity f) ≤ rankComplexity f * log₂(e * n / rankComplexity f)`.

## Main definitions

* `Cslib.DecisionTree.IsReduced`, `Cslib.DecisionTree.reduce`: read-once-per-path predicate and
  constructive reduction of `Cslib.DecisionTree ι β`.
* `Cslib.DecisionTree.leafCountVal`: count of structural leaves carrying a given output label.
* `Cslib.DecisionTree.IsComplete`, `Cslib.DecisionTree.AllLeavesDepthGE`,
  `Cslib.DecisionTree.HasLeafVal`, `Cslib.DecisionTree.AllSubtreesBivalent`: structural tree
  predicates.
* `Cslib.DecisionTree.Context`, `Cslib.DecisionTree.Context.plug`: one-hole tree contexts.
* `Cslib.DecisionTree.graftBool`, `Cslib.DecisionTree.completeQueryList`: Boolean leaf grafting and
  complete sequential query prefix trees.
* `Cslib.DecisionTree.sizeComplexity`, `Cslib.DecisionTree.rankComplexity`,
  `Cslib.DecisionTree.weightedComplexity`: minimum leaf count, minimum Strahler rank, and minimum
  weighted depth of decision trees computing `f : (ι → Bool) → β`.

## Main results

* `Cslib.DecisionTree.weightedDepth_update_succ_le`: incrementing one variable's weight by `1`
  increases the weighted depth of a reduced tree by at most `1`.
* `Cslib.DecisionTree.leafCount_le_sum_choose_of_isReduced`: leaf count of a reduced tree over `ι`
  is bounded by `∑ k ∈ range (t.rank + 1), (Fintype.card ι).choose k`.
* `Cslib.DecisionTree.rank_graftBool_le`, `Cslib.DecisionTree.rank_graftBool_eq_of_isComplete`,
  `Cslib.DecisionTree.le_rank_graftBool_of_allSubtreesBivalent`,
  `Cslib.DecisionTree.rank_graftBool_eq_of_isComplete_of_ne`: exact and inequality laws for
  grafting trees onto Boolean leaves.
* `Cslib.DecisionTree.rankComplexity_le_logb_sizeComplexity`,
  `Cslib.DecisionTree.logb_sizeComplexity_le_rankComplexity_mul_logb`: the Ehrenfeucht–Haussler
  rank-size inequalities.
-/

public section

open scoped BigOperators
open Cslib Cslib.BitString

namespace Cslib.DecisionTree

section TreeStructure

variable {ι β : Type*}

/-- Rank of a decision tree vanishes if and only if the tree is a single leaf. -/
theorem rank_eq_zero_iff {t : DecisionTree ι β} :
    t.rank = 0 ↔ ∃ b : β, t = .leaf b := by
  cases t with
  | leaf b => simp
  | node _ l r =>
    refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ by cases h⟩
    rw [rank_node] at h
    split_ifs at h with heq
    have h1 : l.rank = 0 := Nat.eq_zero_of_le_zero ((le_max_left _ _).trans h.le)
    have h2 : r.rank = 0 := Nat.eq_zero_of_le_zero ((le_max_right _ _).trans h.le)
    exact absurd (h1.trans h2.symm) heq

/-- At any internal node, `1 + min left.rank right.rank ≤ (node i left right).rank`. -/
theorem one_add_min_rank_le_rank_node (i : ι) (left right : DecisionTree ι β) :
    1 + min left.rank right.rank ≤ (DecisionTree.node i left right).rank := by
  rw [rank_node]
  split_ifs <;> omega

/-- Number of structural leaves of `t` carrying a specific output value `b₀`. -/
def leafCountVal [DecidableEq β] : DecisionTree ι β → β → ℕ
  | .leaf b, b₀ => if b = b₀ then 1 else 0
  | .node _ left right, b₀ => leafCountVal left b₀ + leafCountVal right b₀

/-- `leafCountVal` on a leaf is `1` on matching label and `0` otherwise. -/
@[simp] theorem leafCountVal_leaf [DecidableEq β] (b b₀ : β) :
    leafCountVal (.leaf b : DecisionTree ι β) b₀ = if b = b₀ then 1 else 0 := by rfl

/-- `leafCountVal` on an internal node sums the left and right child counts. -/
@[simp] theorem leafCountVal_node [DecidableEq β] (i : ι) (left right : DecisionTree ι β)
    (b₀ : β) :
    leafCountVal (.node i left right) b₀ = leafCountVal left b₀ + leafCountVal right b₀ := by rfl

/-- For Boolean-output trees, `false`-leaves and `true`-leaves partition `t.leafCount`. -/
theorem leafCountVal_false_add_true (t : DecisionTree ι Bool) :
    leafCountVal t false + leafCountVal t true = t.leafCount := by
  induction t with
  | leaf b => cases b <;> rfl
  | node _ _ _ ihl ihr =>
    simp only [leafCountVal_node, leafCount]
    omega

/-- If `S` is a finite set of inputs evaluating to `b₀` with pairwise distinct root-to-leaf paths
in `t`, then `S.card ≤ leafCountVal t b₀`. -/
theorem card_le_leafCountVal_of_injOn_path [DecidableEq β] (t : DecisionTree ι β)
    (S : Finset (ι → Bool)) (b₀ : β) (heval : ∀ x ∈ S, t.eval x = b₀)
    (hinj : Set.InjOn t.path (S : Set (ι → Bool))) :
    S.card ≤ leafCountVal t b₀ := by
  classical
  induction t generalizing S with
  | leaf b =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    · have hsub : S ⊆ {x₀} := fun y hy ↦ Finset.mem_singleton.mpr (hinj hy hx₀ rfl)
      have hcard : S.card ≤ 1 := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton x₀)
      have hb : b = b₀ := heval x₀ hx₀
      simp [hb, hcard]
  | node i left right ihl ihr =>
    let S₀ := S.filter fun x ↦ x i = false
    let S₁ := S.filter fun x ↦ x i = true
    have hcard : S.card = S₀.card + S₁.card := by
      have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun x ↦ x i = false)
      have hS₁ : (S.filter fun x ↦ ¬x i = false) = S₁ := by
        ext x
        simp [S₁]
      rw [hS₁] at h
      exact h.symm
    have hl : S₀.card ≤ leafCountVal left b₀ := by
      refine ihl S₀ (fun x hx ↦ ?_) (fun x hx y hy hp ↦ ?_)
      · obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
        have he := heval x hxS
        rwa [eval_node, hxi, Bool.cond_false] at he
      · obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
        obtain ⟨hyS, hyi⟩ := Finset.mem_filter.mp hy
        apply hinj hxS hyS
        simp [path, hxi, hyi, hp]
    have hr : S₁.card ≤ leafCountVal right b₀ := by
      refine ihr S₁ (fun x hx ↦ ?_) (fun x hx y hy hp ↦ ?_)
      · obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
        have he := heval x hxS
        rwa [eval_node, hxi, Bool.cond_true] at he
      · obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
        obtain ⟨hyS, hyi⟩ := Finset.mem_filter.mp hy
        apply hinj hxS hyS
        simp [path, hxi, hyi, hp]
    rw [hcard, leafCountVal_node]
    omega

/-- Auxiliary predicate asserting `t` queries no variable in `seen` and no variable twice along any
root-to-leaf path. -/
@[expose] def IsReducedAux : Set ι → DecisionTree ι β → Prop
  | _, .leaf _ => True
  | seen, .node i left right =>
    i ∉ seen ∧ IsReducedAux (insert i seen) left ∧ IsReducedAux (insert i seen) right

/-- A binary decision tree is reduced if no variable is queried more than once along any
root-to-leaf path. -/
@[expose] def IsReduced (t : DecisionTree ι β) : Prop :=
  IsReducedAux ∅ t

private lemma isReducedAux_antitone {s₁ s₂ : Set ι} {t : DecisionTree ι β}
    (hs : s₁ ⊆ s₂) (ht : IsReducedAux s₂ t) : IsReducedAux s₁ t := by
  induction t generalizing s₁ s₂ with
  | leaf _ => trivial
  | node _ _ _ ihl ihr =>
    exact ⟨fun h ↦ ht.1 (hs h), ihl (Set.insert_subset_insert hs) ht.2.1,
      ihr (Set.insert_subset_insert hs) ht.2.2⟩

/-- Auxiliary constructive reduction of `t` under partial assignment `ρ`. -/
def reduceAux [DecidableEq ι] (ρ : PartialAssignment ι) :
    DecisionTree ι β → DecisionTree ι β
  | .leaf b => .leaf b
  | .node i left right =>
    match ρ i with
    | some false => reduceAux ρ left
    | some true => reduceAux ρ right
    | none => .node i (reduceAux (Function.update ρ i (some false)) left)
        (reduceAux (Function.update ρ i (some true)) right)

/-- Constructively eliminates repeated variable queries along every root-to-leaf path of `t`. -/
def reduce [DecidableEq ι] (t : DecisionTree ι β) : DecisionTree ι β :=
  reduceAux PartialAssignment.empty t

private lemma isReducedAux_reduceAux [DecidableEq ι] (t : DecisionTree ι β)
    (ρ : PartialAssignment ι) : IsReducedAux {i | (ρ i).isSome} (reduceAux ρ t) := by
  induction t generalizing ρ with
  | leaf _ => trivial
  | node i left right ihl ihr =>
    simp only [reduceAux]
    cases hρ : ρ i with
    | some b =>
      cases b
      · exact ihl ρ
      · exact ihr ρ
    | none =>
      refine ⟨by simp [hρ], ?_, ?_⟩
      · refine isReducedAux_antitone ?_ (ihl (Function.update ρ i (some false)))
        intro j hj
        rcases eq_or_ne j i with rfl | hne <;> simp_all
      · refine isReducedAux_antitone ?_ (ihr (Function.update ρ i (some true)))
        intro j hj
        rcases eq_or_ne j i with rfl | hne <;> simp_all

/-- Reducing any decision tree produces a reduced decision tree. -/
theorem isReduced_reduce [DecidableEq ι] (t : DecisionTree ι β) : IsReduced (reduce t) :=
  isReducedAux_antitone (Set.empty_subset _) (isReducedAux_reduceAux t PartialAssignment.empty)

private lemma eval_reduceAux [DecidableEq ι] (t : DecisionTree ι β) (ρ : PartialAssignment ι)
    (x : ι → Bool) (hx : ρ.Agrees x) : (reduceAux ρ t).eval x = t.eval x := by
  induction t generalizing ρ with
  | leaf _ => rfl
  | node i left right ihl ihr =>
    simp only [reduceAux, eval_node]
    cases hρ : ρ i with
    | some b =>
      have hxi : x i = b := by
        have hfill := PartialAssignment.agrees_iff_fill_eq.mp hx
        rw [← hfill, PartialAssignment.fill_of_eq_some hρ]
      rw [hxi]
      cases b
      · exact ihl ρ hx
      · exact ihr ρ hx
    | none =>
      cases hxi : x i
      · simp only [eval_node, hxi, Bool.cond_false]
        refine ihl (Function.update ρ i (some false)) ?_
        rw [PartialAssignment.agrees_iff_fill_eq, PartialAssignment.fill_update,
          PartialAssignment.agrees_iff_fill_eq.mp hx]
        ext j
        rcases eq_or_ne j i with rfl | hne <;> simp [*]
      · simp only [eval_node, hxi, Bool.cond_true]
        refine ihr (Function.update ρ i (some true)) ?_
        rw [PartialAssignment.agrees_iff_fill_eq, PartialAssignment.fill_update,
          PartialAssignment.agrees_iff_fill_eq.mp hx]
        ext j
        rcases eq_or_ne j i with rfl | hne <;> simp [*]

/-- Tree reduction preserves evaluation at every input `x`. -/
@[simp] theorem eval_reduce [DecidableEq ι] (t : DecisionTree ι β) (x : ι → Bool) :
    (reduce t).eval x = t.eval x :=
  eval_reduceAux t PartialAssignment.empty x (PartialAssignment.agrees_empty x)

private lemma reduceAux_measure_le [DecidableEq ι] {m : DecisionTree ι β → ℕ}
    (hnode : ∀ i (l r : DecisionTree ι β), m l ≤ m (.node i l r) ∧ m r ≤ m (.node i l r))
    (hmono : ∀ i (l₁ r₁ l₂ r₂ : DecisionTree ι β),
      m l₁ ≤ m l₂ → m r₁ ≤ m r₂ → m (.node i l₁ r₁) ≤ m (.node i l₂ r₂))
    (t : DecisionTree ι β) (ρ : PartialAssignment ι) : m (reduceAux ρ t) ≤ m t := by
  induction t generalizing ρ with
  | leaf _ => exact le_rfl
  | node i l r ihl ihr =>
    simp only [reduceAux]
    cases ρ i with
    | some b =>
      cases b
      · exact (ihl ρ).trans (hnode i l r).1
      · exact (ihr ρ).trans (hnode i l r).2
    | none =>
      exact hmono i _ _ l r (ihl _) (ihr _)

/-- Tree reduction does not increase worst-case depth. -/
theorem depth_reduce_le [DecidableEq ι] (t : DecisionTree ι β) :
    (reduce t).depth ≤ t.depth :=
  reduceAux_measure_le (fun _ _ _ ↦ by simp only [depth_node]; omega)
    (fun _ _ _ _ _ _ _ ↦ by simp only [depth_node]; omega)
    t PartialAssignment.empty

/-- Tree reduction does not increase the number of structural leaves. -/
theorem leafCount_reduce_le [DecidableEq ι] (t : DecisionTree ι β) :
    (reduce t).leafCount ≤ t.leafCount :=
  reduceAux_measure_le (fun _ _ _ ↦ by simp only [leafCount]; omega)
    (fun _ _ _ _ _ _ _ ↦ by simp only [leafCount]; omega)
    t PartialAssignment.empty

/-- Tree reduction does not increase Ehrenfeucht–Haussler rank. -/
theorem rank_reduce_le [DecidableEq ι] (t : DecisionTree ι β) :
    (reduce t).rank ≤ t.rank :=
  reduceAux_measure_le
    (fun i l r ↦ ⟨rank_left_le_rank_node i l r, rank_right_le_rank_node i l r⟩)
    (fun _ _ _ _ _ hl hr ↦ rank_node_le_rank_node hl hr)
    t PartialAssignment.empty

/-- Tree reduction does not increase weighted depth for any weight function `w`. -/
theorem weightedDepth_reduce_le [DecidableEq ι] (t : DecisionTree ι β) (w : ι → ℕ) :
    (reduce t).weightedDepth w ≤ t.weightedDepth w :=
  reduceAux_measure_le (m := fun q ↦ q.weightedDepth w)
    (fun _ _ _ ↦ by simp only [weightedDepth_node]; omega)
    (fun _ _ _ _ _ _ _ ↦ by simp only [weightedDepth_node]; omega)
    t PartialAssignment.empty

private lemma weightedDepth_eq_of_mem_seen [DecidableEq ι] {seen : Set ι}
    {t : DecisionTree ι β} (ht : IsReducedAux seen t) {i : ι} (hi : i ∈ seen)
    (w : ι → ℕ) (v : ℕ) :
    t.weightedDepth (Function.update w i v) = t.weightedDepth w := by
  induction t generalizing seen with
  | leaf _ => rfl
  | node j l r ihl ihr =>
    obtain ⟨hj, hfl, hfr⟩ := ht
    simp only [weightedDepth_node, Function.update_of_ne (fun h : j = i ↦ hj (h ▸ hi))]
    rw [ihl hfl (Set.mem_insert_of_mem j hi), ihr hfr (Set.mem_insert_of_mem j hi)]

private lemma weightedDepth_update_succ_le_aux [DecidableEq ι] {seen : Set ι}
    {t : DecisionTree ι β} (ht : IsReducedAux seen t) (w : ι → ℕ) (i : ι) :
    t.weightedDepth (Function.update w i (w i + 1)) ≤ t.weightedDepth w + 1 := by
  induction t generalizing seen with
  | leaf _ => simp
  | node j l r ihl ihr =>
    obtain ⟨_, hfl, hfr⟩ := ht
    rcases eq_or_ne j i with rfl | hne
    · simp only [weightedDepth_node, Function.update_self]
      rw [weightedDepth_eq_of_mem_seen hfl (Set.mem_insert j seen),
        weightedDepth_eq_of_mem_seen hfr (Set.mem_insert j seen)]
      omega
    · simp only [weightedDepth_node, Function.update_of_ne hne]
      have h1 := ihl hfl
      have h2 := ihr hfr
      omega

/-- Incrementing a single variable's weight by `1` increases the weighted depth of a reduced
decision tree by at most `1`. -/
theorem weightedDepth_update_succ_le [DecidableEq ι] {t : DecisionTree ι β}
    (ht : IsReduced t) (w : ι → ℕ) (i : ι) :
    t.weightedDepth (Function.update w i (w i + 1)) ≤ t.weightedDepth w + 1 :=
  weightedDepth_update_succ_le_aux ht w i

private lemma depth_le_of_isReducedAux {seen : Set ι} {t : DecisionTree ι β} {m : ℕ}
    (ht : IsReducedAux seen t) (hm : ∀ s : Finset ι, Disjoint (s : Set ι) seen → s.card ≤ m) :
    t.depth ≤ m := by
  classical
  induction t generalizing seen m with
  | leaf _ => simp
  | node i l r ihl ihr =>
    obtain ⟨hi, hfl, hfr⟩ := ht
    cases m with
    | zero =>
      have hc := hm {i} (by simp [hi])
      simp at hc
    | succ m =>
      have hm' : ∀ s : Finset ι, Disjoint (s : Set ι) (insert i seen) → s.card ≤ m := fun s hs ↦ by
        have hni : i ∉ s := fun his ↦ Set.disjoint_left.mp hs his (Set.mem_insert i seen)
        have hcard := hm (insert i s) (by
          rw [Finset.coe_insert, Set.disjoint_insert_left]
          exact ⟨hi, hs.mono_right (Set.subset_insert i seen)⟩)
        rw [Finset.card_insert_of_notMem hni] at hcard
        omega
      have hl := ihl hfl hm'
      have hr := ihr hfr hm'
      rw [depth_node]
      omega

/-- Every reduced decision tree over `ι` has depth at most `Fintype.card ι`. -/
theorem depth_le_card_of_isReduced [Fintype ι] {t : DecisionTree ι β} (ht : IsReduced t) :
    t.depth ≤ Fintype.card ι :=
  depth_le_of_isReducedAux ht fun s _ ↦ s.card_le_univ

/-- For any reduced decision tree over `ι`, the number of structural leaves is at most
`∑ k ∈ Finset.range (t.rank + 1), (Fintype.card ι).choose k`. -/
theorem leafCount_le_sum_choose_of_isReduced [Fintype ι] {t : DecisionTree ι β}
    (ht : IsReduced t) :
    t.leafCount ≤ ∑ k ∈ Finset.range (t.rank + 1), (Fintype.card ι).choose k :=
  t.leafCount_le_sum_choose_of_rank_le le_rfl (depth_le_card_of_isReduced ht)

private lemma exists_path_all_vars_of_isReducedAux [Fintype ι] [DecidableEq ι]
    {seen : Finset ι} {t : DecisionTree ι β}
    (ht : IsReducedAux (seen : Set ι) t)
    (hd : Fintype.card ι - seen.card ≤ t.depth) (w : ι → ℕ) :
    (∑ i ∈ Finset.univ \ seen, w i) ≤ t.weightedDepth w := by
  induction t generalizing seen with
  | leaf _ =>
    have hcard : seen.card = Fintype.card ι := by
      have hle := seen.card_le_univ
      simp only [depth_leaf] at hd
      omega
    have heq : seen = Finset.univ := Finset.eq_univ_of_card seen hcard
    simp [heq]
  | node i l r ihl ihr =>
    obtain ⟨hi_not, hfl, hfr⟩ := ht
    have hi_fin : i ∉ seen := by simpa using hi_not
    have hins_coe : ((insert i seen : Finset ι) : Set ι) = insert i (seen : Set ι) := by simp
    rw [← hins_coe] at hfl hfr
    have hcard_ins : (insert i seen).card = seen.card + 1 := Finset.card_insert_of_notMem hi_fin
    have hcard_le : seen.card + 1 ≤ Fintype.card ι :=
      hcard_ins ▸ (insert i seen).card_le_univ
    rw [depth_node] at hd
    have hsdiff : Finset.univ \ seen = insert i (Finset.univ \ insert i seen) := by
      ext j
      rcases eq_or_ne j i with rfl | hne <;> simp [*]
    have hi_not_sdiff : i ∉ Finset.univ \ insert i seen := by simp
    rw [hsdiff, Finset.sum_insert hi_not_sdiff, weightedDepth_node]
    rcases le_total l.depth r.depth with hlr | hrl
    · have ihr' := ihr hfr (by omega)
      omega
    · have ihl' := ihl hfl (by omega)
      omega

/-- If a reduced decision tree over `ι` has maximal depth `Fintype.card ι`, then its weighted depth
is at least `∑ i, w i`. -/
theorem sum_le_weightedDepth_of_isReduced_of_card_le_depth [Fintype ι]
    {t : DecisionTree ι β} (ht : IsReduced t) (hd : Fintype.card ι ≤ t.depth) (w : ι → ℕ) :
    (∑ i : ι, w i) ≤ t.weightedDepth w := by
  classical
  have ht' : IsReducedAux ((∅ : Finset ι) : Set ι) t := by
    rw [Finset.coe_empty]
    exact ht
  simpa using exists_path_all_vars_of_isReducedAux ht' (by simpa using hd) w

end TreeStructure

section ContextsAndGrafting

variable {ι β γ : Type*}

/-- A binary decision tree is complete if both subtrees at every internal node are complete and
have equal depth. -/
@[expose] def IsComplete : DecisionTree ι β → Prop
  | .leaf _ => True
  | .node _ left right => IsComplete left ∧ IsComplete right ∧ left.depth = right.depth

/-- For a complete binary decision tree, the Strahler rank equals the depth. -/
theorem IsComplete.rank_eq_depth {t : DecisionTree ι β} (ht : IsComplete t) :
    t.rank = t.depth := by
  induction t with
  | leaf _ => rfl
  | node _ l r ihl ihr =>
    obtain ⟨hcl, hcr, hdeq⟩ := ht
    rw [rank_node, depth_node, ihl hcl, ihr hcr, hdeq, ite_eq_left rfl, max_self]

/-- Predicate asserting that every structural leaf of `t` lies at depth at least `r`. -/
@[expose] def AllLeavesDepthGE : ℕ → DecisionTree ι β → Prop
  | 0, _ => True
  | _ + 1, .leaf _ => False
  | r + 1, .node _ left right => AllLeavesDepthGE r left ∧ AllLeavesDepthGE r right

/-- If every structural leaf of `t` lies at depth at least `r`, then `r ≤ t.rank`. -/
theorem le_rank_of_allLeavesDepthGE {r : ℕ} {t : DecisionTree ι β}
    (h : AllLeavesDepthGE r t) : r ≤ t.rank := by
  induction r generalizing t with
  | zero => exact Nat.zero_le _
  | succ r ih =>
    cases t with
    | leaf _ => exact False.elim h
    | node i left right =>
      have hl := ih h.1
      have hr := ih h.2
      have hmin := one_add_min_rank_le_rank_node i left right
      omega

/-- Predicate asserting that `t` contains at least one structural leaf labeled `b₀`. -/
@[expose] def HasLeafVal (b₀ : β) : DecisionTree ι β → Prop
  | .leaf b => b = b₀
  | .node _ left right => HasLeafVal b₀ left ∨ HasLeafVal b₀ right

/-- A leaf labeled `b` satisfies `HasLeafVal b₀` iff `b = b₀`. -/
@[simp] theorem hasLeafVal_leaf (b₀ b : β) :
    HasLeafVal b₀ (.leaf b : DecisionTree ι β) ↔ b = b₀ := Iff.rfl

/-- An internal node satisfies `HasLeafVal b₀` iff its left or right child does. -/
@[simp] theorem hasLeafVal_node (b₀ : β) (i : ι) (left right : DecisionTree ι β) :
    HasLeafVal b₀ (.node i left right) ↔ HasLeafVal b₀ left ∨ HasLeafVal b₀ right := Iff.rfl

/-- Predicate on Boolean-output decision trees asserting that every non-leaf subtree contains both
a `false`-leaf and a `true`-leaf. -/
@[expose] def AllSubtreesBivalent : DecisionTree ι Bool → Prop
  | .leaf _ => True
  | .node i left right =>
    HasLeafVal false (.node i left right) ∧ HasLeafVal true (.node i left right) ∧
      AllSubtreesBivalent left ∧ AllSubtreesBivalent right

/-- One-hole context in a binary decision tree `DecisionTree ι β` for subtree replacement. -/
inductive Context (ι β : Type*) where
  /-- Empty context representing the hole itself. -/
  | hole : Context ι β
  /-- Hole located inside the `false` branch of an internal query node. -/
  | left (i : ι) (ctx : Context ι β) (rightTree : DecisionTree ι β) : Context ι β
  /-- Hole located inside the `true` branch of an internal query node. -/
  | right (i : ι) (leftTree : DecisionTree ι β) (ctx : Context ι β) : Context ι β

/-- Plugs a subtree `t` into the hole of a context `c`. -/
@[expose] def Context.plug : Context ι β → DecisionTree ι β → DecisionTree ι β
  | .hole, t => t
  | .left i ctx r, t => .node i (ctx.plug t) r
  | .right i l ctx, t => .node i l (ctx.plug t)

/-- Replacing a subtree inside any context `c` by a tree of at least as large rank does not
decrease the rank of the resulting tree. -/
theorem Context.rank_plug_mono {t₁ t₂ : DecisionTree ι β} (c : Context ι β)
    (h : t₁.rank ≤ t₂.rank) : (c.plug t₁).rank ≤ (c.plug t₂).rank := by
  induction c with
  | hole => exact h
  | left _ _ r ih => exact rank_node_le_rank_node ih le_rfl
  | right _ l _ ih => exact rank_node_le_rank_node le_rfl ih

/-- Rank of `t.map f` equals `t.rank`. -/
@[simp] theorem rank_map (f : β → γ) (t : DecisionTree ι β) : (t.map f).rank = t.rank := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr => simp [DecisionTree.map, rank_node, ihl, ihr]

/-- Leaf count of `t.map f` equals `t.leafCount`. -/
@[simp] theorem leafCount_map (f : β → γ) (t : DecisionTree ι β) :
    (t.map f).leafCount = t.leafCount := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr => simp [DecisionTree.map, leafCount, ihl, ihr]

/-- Weighted depth of `t.map f` equals `t.weightedDepth w`. -/
@[simp] theorem weightedDepth_map (f : β → γ) (t : DecisionTree ι β) (w : ι → ℕ) :
    (t.map f).weightedDepth w = t.weightedDepth w := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr => simp [DecisionTree.map, weightedDepth_node, ihl, ihr]

/-- Rank of `t.dual` equals `t.rank`. -/
@[simp] theorem rank_dual (t : DecisionTree ι Bool) : t.dual.rank = t.rank := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr =>
    simp only [dual_node, rank_node, ihl, ihr]
    split_ifs <;> omega

/-- Leaf count of `t.dual` equals `t.leafCount`. -/
@[simp] theorem leafCount_dual (t : DecisionTree ι Bool) :
    t.dual.leafCount = t.leafCount := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr =>
    simp only [dual_node, leafCount, ihl, ihr]
    omega

/-- Weighted depth of `t.dual` equals `t.weightedDepth w`. -/
@[simp] theorem weightedDepth_dual (t : DecisionTree ι Bool) (w : ι → ℕ) :
    t.dual.weightedDepth w = t.weightedDepth w := by
  induction t with
  | leaf _ => rfl
  | node _ _ _ ihl ihr =>
    simp only [dual_node, weightedDepth_node, ihl, ihr, max_comm]

/-- Grafts `t₀` onto every `false`-leaf of `t` and `t₁` onto every `true`-leaf of `t`. -/
def graftBool (t t₀ t₁ : DecisionTree ι Bool) : DecisionTree ι Bool :=
  t.bind fun b ↦ cond b t₁ t₀

/-- Evaluating `graftBool t t₀ t₁` branches to `t₁` when `t` evaluates to `true` and `t₀` when
`false`. -/
@[simp] theorem eval_graftBool (t t₀ t₁ : DecisionTree ι Bool) (x : ι → Bool) :
    (graftBool t t₀ t₁).eval x = cond (t.eval x) (t₁.eval x) (t₀.eval x) := by
  rw [graftBool, eval_bind]
  cases t.eval x <;> rfl

/-- Attaching `t₀` to `false`-leaves and `t₁` to `true`-leaves of `t` yields rank at most
`t.rank + max t₀.rank t₁.rank`. -/
theorem rank_graftBool_le (t t₀ t₁ : DecisionTree ι Bool) :
    (graftBool t t₀ t₁).rank ≤ t.rank + max t₀.rank t₁.rank := by
  induction t with
  | leaf b => cases b <;> simp [graftBool]
  | node _ _ _ ihl ihr =>
    simp only [graftBool, node_bind, rank_node] at ihl ihr ⊢
    split_ifs <;> omega

/-- If `t` is a complete binary tree and `t₀.rank = t₁.rank`, grafting `t₀` and `t₁` onto `t`
yields rank `t.rank + t₀.rank`. -/
theorem rank_graftBool_eq_of_isComplete {t t₀ t₁ : DecisionTree ι Bool}
    (ht : IsComplete t) (hr : t₀.rank = t₁.rank) :
    (graftBool t t₀ t₁).rank = t.rank + t₀.rank := by
  induction t with
  | leaf b => cases b <;> simp [graftBool, hr]
  | node _ l r ihl ihr =>
    obtain ⟨hcl, hcr, hdeq⟩ := ht
    have heq : l.rank = r.rank := by rw [hcl.rank_eq_depth, hcr.rank_eq_depth, hdeq]
    simp only [graftBool, node_bind, rank_node] at ihl ihr ⊢
    rw [ihl hcl, ihr hcr, heq, ite_eq_left rfl, ite_eq_left rfl]
    omega

private lemma depth_eq_zero_iff_leaf {t : DecisionTree ι β} :
    t.depth = 0 ↔ ∃ b : β, t = .leaf b := by
  cases t <;> simp

private lemma one_le_rank_iff_one_le_depth {t : DecisionTree ι β} :
    1 ≤ t.rank ↔ 1 ≤ t.depth := by
  constructor <;> intro h
  · by_contra hd
    obtain ⟨b, rfl⟩ := depth_eq_zero_iff_leaf.mp (by omega : t.depth = 0)
    simp at h
  · by_contra hr
    obtain ⟨b, rfl⟩ := rank_eq_zero_iff.mp (by omega : t.rank = 0)
    simp at h

/-- If `t` has depth at least `1` and every non-leaf subtree of `t` has both a `false`-leaf and a
`true`-leaf, then `(graftBool t t₀ t₁).rank ≥ t.rank + max t₀.rank t₁.rank - 1`. -/
theorem le_rank_graftBool_of_allSubtreesBivalent {t t₀ t₁ : DecisionTree ι Bool}
    (hd : 1 ≤ t.depth) (hbiv : AllSubtreesBivalent t) :
    t.rank + max t₀.rank t₁.rank - 1 ≤ (graftBool t t₀ t₁).rank := by
  induction t with
  | leaf _ => simp at hd
  | node i l r ihl ihr =>
    obtain ⟨hhas0, hhas1, hbiv0, hbiv1⟩ := hbiv
    rcases eq_or_ne l.rank 0 with hr0 | hr0
    · obtain ⟨b0, hb0⟩ := rank_eq_zero_iff.mp hr0
      rcases eq_or_ne r.rank 0 with hr1 | hr1
      · obtain ⟨b1, hb1⟩ := rank_eq_zero_iff.mp hr1
        subst hb0 hb1
        simp only [HasLeafVal] at hhas0 hhas1
        simp only [graftBool, node_bind, leaf_bind, rank_node, rank_leaf]
        rcases hhas0 with rfl | rfl <;> rcases hhas1 with h1 | h1
        · cases h1
        · subst h1
          by_cases heq : t₀.rank = t₁.rank <;> simp [heq]
        · subst h1
          by_cases heq : t₁.rank = t₀.rank <;> simp [heq, max_comm]
        · cases h1
      · have ih1 := ihr (one_le_rank_iff_one_le_depth.mp (by omega)) hbiv1
        have hnr : (DecisionTree.node i l r).rank = r.rank := by
          simp [rank_node, hr0, hr1.symm]
        rw [hnr]
        exact ih1.trans (rank_right_le_rank_node i _ _)
    · rcases eq_or_ne r.rank 0 with hr1 | hr1
      · have ih0 := ihl (one_le_rank_iff_one_le_depth.mp (by omega)) hbiv0
        have hnr : (DecisionTree.node i l r).rank = l.rank := by
          simp [rank_node, hr1, hr0]
        rw [hnr]
        exact ih0.trans (rank_left_le_rank_node i _ _)
      · have ih0 := ihl (one_le_rank_iff_one_le_depth.mp (by omega)) hbiv0
        have ih1 := ihr (one_le_rank_iff_one_le_depth.mp (by omega)) hbiv1
        simp only [graftBool, node_bind, rank_node] at ih0 ih1 ⊢
        split_ifs <;> omega

/-- If `t` is a complete binary tree of depth at least `1`, every non-leaf subtree of `t` has both
a `false`-leaf and a `true`-leaf, and `t₀.rank ≠ t₁.rank`, then
`(graftBool t t₀ t₁).rank = t.rank + max t₀.rank t₁.rank - 1`. -/
theorem rank_graftBool_eq_of_isComplete_of_ne {t t₀ t₁ : DecisionTree ι Bool}
    (hd : 1 ≤ t.depth) (hbiv : AllSubtreesBivalent t) (hc : IsComplete t)
    (hne : t₀.rank ≠ t₁.rank) :
    (graftBool t t₀ t₁).rank = t.rank + max t₀.rank t₁.rank - 1 := by
  induction t with
  | leaf _ => simp at hd
  | node _ l r ihl ihr =>
    obtain ⟨hhas0, hhas1, hbiv0, hbiv1⟩ := hbiv
    obtain ⟨hc0, hc1, hdeq⟩ := hc
    rcases eq_or_ne l.depth 0 with hd0 | hd0
    · obtain ⟨b0, rfl⟩ := depth_eq_zero_iff_leaf.mp hd0
      obtain ⟨b1, rfl⟩ := depth_eq_zero_iff_leaf.mp (hdeq.symm.trans hd0)
      simp only [HasLeafVal] at hhas0 hhas1
      simp only [graftBool, node_bind, leaf_bind, rank_node, rank_leaf]
      rcases hhas0 with rfl | rfl <;> rcases hhas1 with h1 | h1
      · cases h1
      · subst h1
        simp [hne]
      · subst h1
        simp [hne.symm, max_comm]
      · cases h1
    · have hd0' : 1 ≤ l.depth := by omega
      have ih0 := ihl hd0' hbiv0 hc0
      have ih1 := ihr (by omega) hbiv1 hc1
      have hreq : l.rank = r.rank := by rw [hc0.rank_eq_depth, hc1.rank_eq_depth, hdeq]
      have hrpos : 1 ≤ l.rank := one_le_rank_iff_one_le_depth.mpr hd0'
      simp only [graftBool, node_bind, rank_node] at ih0 ih1 ⊢
      rw [ih0, ih1, hreq, ite_eq_left rfl, ite_eq_left rfl]
      omega

/-- Complete binary query prefix tree querying `vars` sequentially while recording queried values in
`acc`, then invoking `cont acc` at the leaves. -/
def completeQueryList [DecidableEq ι] (vars : List ι)
    (cont : (ι → Bool) → DecisionTree ι β) (acc : ι → Bool) : DecisionTree ι β :=
  graft vars cont acc

/-- Evaluating `completeQueryList vars cont acc` at `x` evaluates `cont` on the input updating
`acc` by `x` on `vars`. -/
@[simp] theorem eval_completeQueryList [DecidableEq ι] (vars : List ι)
    (cont : (ι → Bool) → DecisionTree ι β) (acc x : ι → Bool) :
    (completeQueryList vars cont acc).eval x =
      (cont fun i ↦ if i ∈ vars then x i else acc i).eval x :=
  eval_graft vars cont acc x

private lemma rank_completeQueryList_le_add [DecidableEq ι] (vars : List ι)
    (cont : (ι → Bool) → DecisionTree ι β) (acc : ι → Bool) {R : ℕ}
    (hub : ∀ acc', (cont acc').rank ≤ R) :
    (completeQueryList vars cont acc).rank ≤ R + vars.length := by
  induction vars generalizing acc with
  | nil => simpa [completeQueryList, graft_nil] using hub acc
  | cons i rest ih =>
    simp only [completeQueryList, graft_cons, rank_node, List.length_cons] at ih ⊢
    have hf := ih (Function.update acc i false)
    have ht := ih (Function.update acc i true)
    split_ifs <;> omega

/-- Heterogeneous complete-tree rank bound: if `vars` is nonempty, every continuation tree has rank
at most `R` (`1 ≤ R`), and at least one branch reaches a leaf of rank `0`, then
`(completeQueryList vars cont acc).rank ≤ R + vars.length - 1`. -/
theorem rank_completeQueryList_le_of_exists_rank_zero [DecidableEq ι]
    {vars : List ι} (hlen : 1 ≤ vars.length) {R : ℕ} (hR : 1 ≤ R)
    {cont : (ι → Bool) → DecisionTree ι β} (hub : ∀ acc', (cont acc').rank ≤ R)
    (acc : ι → Bool)
    (hzero : ∃ x₀ : ι → Bool, (cont (fun i ↦ if i ∈ vars then x₀ i else acc i)).rank = 0) :
    (completeQueryList vars cont acc).rank ≤ R + vars.length - 1 := by
  induction vars generalizing acc with
  | nil => simp at hlen
  | cons j rest ih =>
    obtain ⟨x₀, hx₀⟩ := hzero
    cases rest with
    | nil =>
      have h_eq : (fun i ↦ if i ∈ [j] then x₀ i else acc i) = Function.update acc j (x₀ j) := by
        ext k
        rcases eq_or_ne k j with rfl | hne <;> simp [*]
      rw [h_eq] at hx₀
      rw [completeQueryList, graft_cons, graft_nil, graft_nil, rank_node, List.length_singleton]
      have hf := hub (Function.update acc j false)
      have ht := hub (Function.update acc j true)
      cases hxj : x₀ j <;> rw [hxj] at hx₀ <;> (split_ifs <;> omega)
    | cons j₂ rest₂ =>
      have h_eq : (fun i ↦ if i ∈ j :: j₂ :: rest₂ then x₀ i else acc i) =
          (fun i ↦ if i ∈ j₂ :: rest₂ then x₀ i else Function.update acc j (x₀ j) i) := by
        ext k
        rcases eq_or_ne k j with rfl | hne <;> simp [*]
      rw [h_eq] at hx₀
      have hz := ih (by simp) (Function.update acc j (x₀ j)) ⟨x₀, hx₀⟩
      have ho := rank_completeQueryList_le_add (j₂ :: rest₂) cont (Function.update acc j (!x₀ j))
        hub
      rw [completeQueryList, graft_cons, rank_node]
      simp only [completeQueryList, List.length_cons] at hz ho ⊢
      cases hxj : x₀ j <;> rw [hxj] at hz ho
      · simp only [Bool.not_false] at ho
        split_ifs <;> omega
      · simp only [Bool.not_true] at ho
        split_ifs <;> omega

end ContextsAndGrafting

section FunctionMeasures

variable {ι β : Type*}

/-- Decision tree leaf-size complexity `DTSize(f)`: minimum leaf count of a decision tree computing
`f`. -/
noncomputable def sizeComplexity (f : (ι → Bool) → β) : ℕ :=
  sInf {k : ℕ | ∃ t : DecisionTree ι β, t.Computes f ∧ t.leafCount = k}

/-- Decision tree rank complexity `Rank(f)`: minimum Ehrenfeucht–Haussler rank of a decision tree
computing `f`. -/
noncomputable def rankComplexity (f : (ι → Bool) → β) : ℕ :=
  sInf {k : ℕ | ∃ t : DecisionTree ι β, t.Computes f ∧ t.rank = k}

/-- Weighted decision tree depth complexity `Depth_w(f, w)` with query weights `w : ι → ℕ`. -/
noncomputable def weightedComplexity (f : (ι → Bool) → β) (w : ι → ℕ) : ℕ :=
  sInf {k : ℕ | ∃ t : DecisionTree ι β, t.Computes f ∧ t.weightedDepth w = k}

/-- Any decision tree computing `f` bounds `sizeComplexity f` by its leaf count. -/
theorem sizeComplexity_le_leafCount {f : (ι → Bool) → β} {t : DecisionTree ι β}
    (ht : t.Computes f) : sizeComplexity f ≤ t.leafCount :=
  Nat.sInf_le ⟨t, ht, rfl⟩

/-- Any decision tree computing `f` bounds `rankComplexity f` by its rank. -/
theorem rankComplexity_le_rank {f : (ι → Bool) → β} {t : DecisionTree ι β}
    (ht : t.Computes f) : rankComplexity f ≤ t.rank :=
  Nat.sInf_le ⟨t, ht, rfl⟩

/-- Any decision tree computing `f` bounds `weightedComplexity f w` by its weighted depth. -/
theorem weightedComplexity_le_weightedDepth {f : (ι → Bool) → β} {t : DecisionTree ι β}
    (ht : t.Computes f) (w : ι → ℕ) : weightedComplexity f w ≤ t.weightedDepth w :=
  Nat.sInf_le ⟨t, ht, rfl⟩

section FiniteVars

variable [Finite ι]

private lemma exists_isReduced_opt {m : DecisionTree ι β → ℕ}
    (hred : ∀ [DecidableEq ι] (t : DecisionTree ι β), m (reduce t) ≤ m t)
    (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, IsReduced t ∧ t.Computes f ∧
      m t = sInf {k : ℕ | ∃ q : DecisionTree ι β, q.Computes f ∧ m q = k} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨t₀, ht₀, _⟩ := exists_computes f
  obtain ⟨t, ht, hm⟩ :=
    Nat.sInf_mem (s := {k : ℕ | ∃ q : DecisionTree ι β, q.Computes f ∧ m q = k})
      ⟨m t₀, t₀, ht₀, rfl⟩
  have hrc : (reduce t).Computes f := fun x ↦ (eval_reduce t x).trans (ht x)
  exact ⟨reduce t, isReduced_reduce t, hrc,
    le_antisymm ((hred t).trans_eq hm) (Nat.sInf_le ⟨reduce t, hrc, rfl⟩)⟩

/-- Attainment of `DecisionTree.complexity f` by a reduced decision tree. -/
theorem exists_isReduced_computes_complexity (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, IsReduced t ∧ t.Computes f ∧
      t.depth = complexity f := by
  classical
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  have hrc : (reduce t).Computes f := fun x ↦ (eval_reduce t x).trans (ht x)
  exact ⟨reduce t, isReduced_reduce t, hrc,
    le_antisymm ((depth_reduce_le t).trans_eq hd) (complexity_le_depth hrc)⟩

/-- Attainment of `sizeComplexity f` by a reduced decision tree. -/
theorem exists_isReduced_computes_sizeComplexity (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, IsReduced t ∧ t.Computes f ∧ t.leafCount = sizeComplexity f :=
  exists_isReduced_opt leafCount_reduce_le f

/-- Attainment of `rankComplexity f` by a reduced decision tree. -/
theorem exists_isReduced_computes_rankComplexity (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, IsReduced t ∧ t.Computes f ∧ t.rank = rankComplexity f :=
  exists_isReduced_opt rank_reduce_le f

/-- Attainment of `weightedComplexity f w` by a reduced decision tree. -/
theorem exists_isReduced_computes_weightedComplexity (f : (ι → Bool) → β) (w : ι → ℕ) :
    ∃ t : DecisionTree ι β, IsReduced t ∧ t.Computes f ∧
      t.weightedDepth w = weightedComplexity f w :=
  exists_isReduced_opt (fun t ↦ weightedDepth_reduce_le t w) f

/-- `rankComplexity f = 0` if and only if `f` is constant (on nonempty `ι → Bool`). -/
theorem rankComplexity_eq_zero_iff_isConst {f : (ι → Bool) → β} :
    rankComplexity f = 0 ↔ Function.IsConst f := by
  refine ⟨fun h0 x y ↦ ?_, fun hconst ↦ ?_⟩
  · obtain ⟨t, _, hc, hr⟩ := exists_isReduced_computes_rankComplexity f
    obtain ⟨b, rfl⟩ := rank_eq_zero_iff.mp (hr.trans h0)
    exact (hc x).symm.trans (hc y)
  · refine Nat.eq_zero_of_le_zero ?_
    exact rankComplexity_le_rank (t := .leaf (f (fun _ ↦ false))) fun x ↦ (hconst x _).symm

/-- Every function on `ι → Bool` has decision tree leaf-size complexity at least `1`. -/
theorem one_le_sizeComplexity (f : (ι → Bool) → β) : 1 ≤ sizeComplexity f := by
  obtain ⟨t, _, _, hs⟩ := exists_isReduced_computes_sizeComplexity f
  rw [← hs]
  exact t.leafCount_pos

/-- Decision tree rank is bounded above by decision tree depth complexity. -/
theorem rankComplexity_le_complexity (f : (ι → Bool) → β) :
    rankComplexity f ≤ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact (rankComplexity_le_rank ht).trans (t.rank_le_depth.trans_eq hd)

/-- Decision tree leaf-size complexity is at most `2 ^ complexity f`. -/
theorem sizeComplexity_le_two_pow_complexity (f : (ι → Bool) → β) :
    sizeComplexity f ≤ 2 ^ complexity f := by
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  rw [← hd]
  exact (sizeComplexity_le_leafCount ht).trans t.leafCount_le_two_pow_depth

/-- With constant weight `c`, `weightedComplexity f (fun _ ↦ c) = complexity f * c`. -/
theorem weightedComplexity_const (f : (ι → Bool) → β) (c : ℕ) :
    weightedComplexity f (fun _ ↦ c) = complexity f * c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
    exact (weightedComplexity_le_weightedDepth ht _).trans_eq
      ((t.weightedDepth_const c).trans (by rw [hd]))
  · obtain ⟨t, _, ht, hw⟩ := exists_isReduced_computes_weightedComplexity f (fun _ ↦ c)
    rw [← hw, t.weightedDepth_const]
    exact Nat.mul_le_mul_right c (complexity_le_depth ht)

/-- Monotonicity of `weightedComplexity` in the variable weights. -/
theorem weightedComplexity_mono (f : (ι → Bool) → β) {w₁ w₂ : ι → ℕ} (hw : ∀ i, w₁ i ≤ w₂ i) :
    weightedComplexity f w₁ ≤ weightedComplexity f w₂ := by
  obtain ⟨t, _, hc, hw₂⟩ := exists_isReduced_computes_weightedComplexity f w₂
  exact (weightedComplexity_le_weightedDepth hc w₁).trans ((t.weightedDepth_mono hw).trans_eq hw₂)

/-- Incrementing one variable's query weight by `1` increases `weightedComplexity f` by at most
`1`. -/
theorem weightedComplexity_update_succ_le [DecidableEq ι] (f : (ι → Bool) → β) (w : ι → ℕ)
    (i : ι) :
    weightedComplexity f (Function.update w i (w i + 1)) ≤ weightedComplexity f w + 1 := by
  obtain ⟨t, hred, hc, hw⟩ := exists_isReduced_computes_weightedComplexity f w
  rw [← hw]
  exact (weightedComplexity_le_weightedDepth hc _).trans (weightedDepth_update_succ_le hred w i)

end FiniteVars

section InvarianceAndRestrictions

/-- Complement invariance of decision tree rank. -/
@[simp] theorem rankComplexity_not [Finite ι] (f : (ι → Bool) → Bool) :
    rankComplexity (fun x ↦ !f x) = rankComplexity f := by
  have hle : ∀ g : (ι → Bool) → Bool, rankComplexity (fun x ↦ !g x) ≤ rankComplexity g :=
    fun g ↦ by
      obtain ⟨t, _, hc, hr⟩ := exists_isReduced_computes_rankComplexity g
      refine (rankComplexity_le_rank (t := t.map (!·)) fun x ↦ ?_).trans_eq
        ((rank_map (!·) t).trans hr)
      simp [eval_map, hc x]
  exact le_antisymm (hle f) (by simpa using hle fun x ↦ !f x)

/-- Complement invariance of decision tree leaf-size complexity. -/
@[simp] theorem sizeComplexity_not [Finite ι] (f : (ι → Bool) → Bool) :
    sizeComplexity (fun x ↦ !f x) = sizeComplexity f := by
  have hle : ∀ g : (ι → Bool) → Bool, sizeComplexity (fun x ↦ !g x) ≤ sizeComplexity g :=
    fun g ↦ by
      obtain ⟨t, _, hc, hs⟩ := exists_isReduced_computes_sizeComplexity g
      refine (sizeComplexity_le_leafCount (t := t.map (!·)) fun x ↦ ?_).trans_eq
        ((leafCount_map (!·) t).trans hs)
      simp [eval_map, hc x]
  exact le_antisymm (hle f) (by simpa using hle fun x ↦ !f x)

/-- Complement invariance of weighted decision tree complexity. -/
@[simp] theorem weightedComplexity_not [Finite ι] (f : (ι → Bool) → Bool) (w : ι → ℕ) :
    weightedComplexity (fun x ↦ !f x) w = weightedComplexity f w := by
  have hle : ∀ g : (ι → Bool) → Bool,
      weightedComplexity (fun x ↦ !g x) w ≤ weightedComplexity g w := fun g ↦ by
    obtain ⟨t, _, hc, hw⟩ := exists_isReduced_computes_weightedComplexity g w
    refine (weightedComplexity_le_weightedDepth (t := t.map (!·)) (fun x ↦ ?_) w).trans_eq
      ((weightedDepth_map (!·) t w).trans hw)
    simp [eval_map, hc x]
  exact le_antisymm (hle f) (by simpa using hle fun x ↦ !f x)

/-- Dual invariance of decision tree rank. -/
theorem rankComplexity_dual [Finite ι] (f : (ι → Bool) → Bool) :
    rankComplexity (fun x ↦ !f fun i ↦ !x i) = rankComplexity f := by
  have hle : ∀ g : (ι → Bool) → Bool,
      rankComplexity (fun x ↦ !g fun i ↦ !x i) ≤ rankComplexity g := fun g ↦ by
    obtain ⟨t, _, hc, hr⟩ := exists_isReduced_computes_rankComplexity g
    exact (rankComplexity_le_rank hc.dual).trans_eq ((rank_dual t).trans hr)
  exact le_antisymm (hle f) (by simpa using hle fun x ↦ !f fun i ↦ !x i)

/-- Dual invariance of decision tree leaf-size complexity. -/
theorem sizeComplexity_dual [Finite ι] (f : (ι → Bool) → Bool) :
    sizeComplexity (fun x ↦ !f fun i ↦ !x i) = sizeComplexity f := by
  have hle : ∀ g : (ι → Bool) → Bool,
      sizeComplexity (fun x ↦ !g fun i ↦ !x i) ≤ sizeComplexity g := fun g ↦ by
    obtain ⟨t, _, hc, hs⟩ := exists_isReduced_computes_sizeComplexity g
    exact (sizeComplexity_le_leafCount hc.dual).trans_eq ((leafCount_dual t).trans hs)
  exact le_antisymm (hle f) (by simpa using hle fun x ↦ !f fun i ↦ !x i)

/-- Dual invariance of weighted decision tree complexity. -/
theorem weightedComplexity_dual [Finite ι] (f : (ι → Bool) → Bool) (w : ι → ℕ) :
    weightedComplexity (fun x ↦ !f fun i ↦ !x i) w = weightedComplexity f w := by
  have hle : ∀ g : (ι → Bool) → Bool,
      weightedComplexity (fun x ↦ !g fun i ↦ !x i) w ≤ weightedComplexity g w := fun g ↦ by
    obtain ⟨t, _, hc, hw⟩ := exists_isReduced_computes_weightedComplexity g w
    exact (weightedComplexity_le_weightedDepth hc.dual w).trans_eq
      ((weightedDepth_dual t w).trans hw)
  exact le_antisymm (hle f) (by simpa using hle fun x ↦ !f fun i ↦ !x i)

private lemma rankComplexity_comp_equiv_le {α₁ α₂ : Type*} [Finite α₁] (σ : α₁ ≃ α₂)
    (g : (α₁ → Bool) → β) :
    rankComplexity (fun y : α₂ → Bool ↦ g (y ∘ σ)) ≤ rankComplexity g := by
  obtain ⟨t, _, hc, hr⟩ := exists_isReduced_computes_rankComplexity g
  refine (rankComplexity_le_rank (t := t.mapQueries σ) fun y ↦ ?_).trans_eq
    ((rank_mapQueries σ t).trans hr)
  rw [eval_mapQueries, hc]

/-- Coordinate-bijection invariance of decision tree rank. -/
theorem rankComplexity_comp_equiv {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] (e : ι₁ ≃ ι₂)
    (f : (ι₁ → Bool) → β) :
    rankComplexity (fun y : ι₂ → Bool ↦ f (y ∘ e)) = rankComplexity f :=
  le_antisymm (rankComplexity_comp_equiv_le e f)
    (by simpa [Function.comp_def] using rankComplexity_comp_equiv_le e.symm fun y ↦ f (y ∘ e))

private lemma sizeComplexity_comp_equiv_le {α₁ α₂ : Type*} [Finite α₁] (σ : α₁ ≃ α₂)
    (g : (α₁ → Bool) → β) :
    sizeComplexity (fun y : α₂ → Bool ↦ g (y ∘ σ)) ≤ sizeComplexity g := by
  obtain ⟨t, _, hc, hs⟩ := exists_isReduced_computes_sizeComplexity g
  refine (sizeComplexity_le_leafCount (t := t.mapQueries σ) fun y ↦ ?_).trans_eq
    ((leafCount_mapQueries σ t).trans hs)
  rw [eval_mapQueries, hc]

/-- Coordinate-bijection invariance of decision tree leaf-size complexity. -/
theorem sizeComplexity_comp_equiv {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] (e : ι₁ ≃ ι₂)
    (f : (ι₁ → Bool) → β) :
    sizeComplexity (fun y : ι₂ → Bool ↦ f (y ∘ e)) = sizeComplexity f :=
  le_antisymm (sizeComplexity_comp_equiv_le e f)
    (by simpa [Function.comp_def] using sizeComplexity_comp_equiv_le e.symm fun y ↦ f (y ∘ e))

private lemma complexity_comp_equiv_le {α₁ α₂ : Type*} [Finite α₁] [Finite α₂] (σ : α₁ ≃ α₂)
    (g : (α₁ → Bool) → β) :
    complexity (fun y : α₂ → Bool ↦ g (y ∘ σ)) ≤ complexity g := by
  obtain ⟨t, hc, hd⟩ := exists_computes_depth_eq_complexity g
  refine (complexity_le_depth (t := t.mapQueries σ) fun y ↦ ?_).trans_eq
    ((depth_mapQueries σ t).trans hd)
  rw [eval_mapQueries, hc]

/-- Coordinate-bijection invariance of decision tree depth complexity. -/
theorem complexity_comp_equiv {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] (e : ι₁ ≃ ι₂)
    (f : (ι₁ → Bool) → β) :
    complexity (fun y : ι₂ → Bool ↦ f (y ∘ e)) = complexity f :=
  le_antisymm (complexity_comp_equiv_le e f)
    (by simpa [Function.comp_def] using complexity_comp_equiv_le e.symm fun y ↦ f (y ∘ e))

/-- Coordinate-bijection transport of weighted decision tree complexity. -/
theorem weightedComplexity_comp_equiv {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] (e : ι₁ ≃ ι₂)
    (f : (ι₁ → Bool) → β) (w : ι₂ → ℕ) :
    weightedComplexity (fun y : ι₂ → Bool ↦ f (y ∘ e)) w = weightedComplexity f (w ∘ e) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨t, _, hc, hw⟩ := exists_isReduced_computes_weightedComplexity f (w ∘ e)
    refine (weightedComplexity_le_weightedDepth (t := t.mapQueries e) (fun y ↦ ?_) w).trans_eq
      ((weightedDepth_mapQueries e t w).trans hw)
    rw [eval_mapQueries, hc]
  · obtain ⟨t, _, hc, hw⟩ :=
      exists_isReduced_computes_weightedComplexity (fun y : ι₂ → Bool ↦ f (y ∘ e)) w
    refine (weightedComplexity_le_weightedDepth (t := t.mapQueries e.symm) (fun x ↦ ?_)
      (w ∘ e)).trans_eq ?_
    · rw [eval_mapQueries, hc]
      change f ((x ∘ e.symm) ∘ e) = f x
      congr 1
      ext i
      simp
    · rw [weightedDepth_mapQueries]
      have hw_eq : (w ∘ e) ∘ e.symm = w := funext fun j ↦ by simp
      rw [hw_eq, hw]

/-- Extends an assignment `y : {i : ι // ρ i = none} → Bool` on the free coordinates of a partial
assignment `ρ` to a full input `ι → Bool` agreeing with `ρ`. -/
def extendFree {ι : Type*} (ρ : PartialAssignment ι)
    (y : {i : ι // ρ i = none} → Bool) (i : ι) : Bool :=
  match h : ρ i with
  | some b => b
  | none => y ⟨i, h⟩

/-- At a coordinate fixed by `ρ` to `b`, `extendFree ρ y i = b`. -/
@[simp] theorem extendFree_of_eq_some {ι : Type*} {ρ : PartialAssignment ι}
    (y : {i : ι // ρ i = none} → Bool) {i : ι} {b : Bool} (h : ρ i = some b) :
    extendFree ρ y i = b := by
  unfold extendFree
  split
  · next b' hb' => exact Option.some.inj (hb'.symm.trans h)
  · next hb' => cases hb'.symm.trans h

/-- At a free coordinate `h : ρ i = none`, `extendFree ρ y i = y ⟨i, h⟩`. -/
@[simp] theorem extendFree_of_eq_none {ι : Type*} {ρ : PartialAssignment ι}
    (y : {i : ι // ρ i = none} → Bool) {i : ι} (h : ρ i = none) :
    extendFree ρ y i = y ⟨i, h⟩ := by
  unfold extendFree
  split
  · next b' hb' => cases hb'.symm.trans h
  · rfl

private def restrictTreeToSubtype {ι β : Type*} (ρ : PartialAssignment ι) :
    DecisionTree ι β → DecisionTree {i : ι // ρ i = none} β
  | .leaf b => .leaf b
  | .node i left right =>
    match h : ρ i with
    | some false => restrictTreeToSubtype ρ left
    | some true => restrictTreeToSubtype ρ right
    | none => .node ⟨i, h⟩ (restrictTreeToSubtype ρ left) (restrictTreeToSubtype ρ right)

private lemma eval_restrictTreeToSubtype {ι β : Type*} (ρ : PartialAssignment ι)
    (t : DecisionTree ι β) (y : {i : ι // ρ i = none} → Bool) :
    (restrictTreeToSubtype ρ t).eval y = t.eval (extendFree ρ y) := by
  induction t with
  | leaf _ => rfl
  | node i l r ihl ihr =>
    simp only [restrictTreeToSubtype, eval_node]
    split
    · next h => rw [extendFree_of_eq_some y h, Bool.cond_false, ihl]
    · next h => rw [extendFree_of_eq_some y h, Bool.cond_true, ihr]
    · next h =>
      simp only [eval_node, extendFree_of_eq_none y h]
      cases y ⟨i, h⟩ <;> simp [ihl, ihr]

private lemma rank_restrictTreeToSubtype_le {ι β : Type*} (ρ : PartialAssignment ι)
    (t : DecisionTree ι β) : (restrictTreeToSubtype ρ t).rank ≤ t.rank := by
  induction t with
  | leaf _ => simp [restrictTreeToSubtype]
  | node i l r ihl ihr =>
    simp only [restrictTreeToSubtype]
    split
    · exact ihl.trans (rank_left_le_rank_node i l r)
    · exact ihr.trans (rank_right_le_rank_node i l r)
    · rw [rank_node, rank_node]
      split_ifs <;> omega

/-- Restricting `f : (ι → Bool) → β` to the free coordinates `{i : ι // ρ i = none}` of a partial
assignment `ρ` does not increase `rankComplexity`. -/
theorem rankComplexity_restrictToFree_le [Finite ι] (f : (ι → Bool) → β)
    (ρ : PartialAssignment ι) :
    rankComplexity (fun y : {i : ι // ρ i = none} → Bool ↦ f (extendFree ρ y)) ≤
      rankComplexity f := by
  obtain ⟨t, _, hc, hr⟩ := exists_isReduced_computes_rankComplexity f
  refine (rankComplexity_le_rank (t := restrictTreeToSubtype ρ t) fun y ↦ ?_).trans
    ((rank_restrictTreeToSubtype_le ρ t).trans_eq hr)
  rw [eval_restrictTreeToSubtype, hc]

/-- Restricting `f : (ι → Bool) → β` via `ρ.fill` on the full hypercube does not increase
`rankComplexity`. -/
theorem rankComplexity_comp_fill_le [Finite ι] (f : (ι → Bool) → β)
    (ρ : PartialAssignment ι) : rankComplexity (f ∘ ρ.fill) ≤ rankComplexity f := by
  obtain ⟨t, _, hc, hr⟩ := exists_isReduced_computes_rankComplexity f
  let proj : {i : ι // ρ i = none} → ι := Subtype.val
  have hcomp : ((restrictTreeToSubtype ρ t).mapQueries proj).Computes (f ∘ ρ.fill) := fun x ↦ by
    rw [eval_mapQueries, eval_restrictTreeToSubtype, hc]
    dsimp only [Function.comp_apply]
    congr 1
    ext i
    cases h : ρ i with
    | some b => rw [extendFree_of_eq_some _ h, PartialAssignment.fill_of_eq_some h]
    | none => rw [extendFree_of_eq_none _ h, PartialAssignment.fill_of_eq_none h]; rfl
  exact (rankComplexity_le_rank hcomp).trans
    ((rank_mapQueries proj _).trans_le ((rank_restrictTreeToSubtype_le ρ t).trans_eq hr))

end InvarianceAndRestrictions

section RankSizeSandwich

/-- Binomial partial sum upper bound: for `1 ≤ r ≤ n`,
`∑ k ∈ range (r + 1), (n.choose k : ℝ) ≤ (e * n / r) ^ r`. -/
theorem sum_choose_le_exp_mul_div_pow {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∑ k ∈ Finset.range (r + 1), (n.choose k : ℝ)) ≤ (Real.exp 1 * (n : ℝ) / (r : ℝ)) ^ r := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (hr.trans hrn)
  set x : ℝ := (r : ℝ) / (n : ℝ)
  have hx_pos : 0 < x := div_pos hr_pos hn_pos
  have hx_le_one : x ≤ 1 := (div_le_one hn_pos).mpr (Nat.cast_le.mpr hrn)
  have hsum1 : (∑ k ∈ Finset.range (r + 1), (n.choose k : ℝ)) * x ^ r ≤
      ∑ k ∈ Finset.range (r + 1), (n.choose k : ℝ) * x ^ k := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hx_pos.le hx_le_one (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      (Nat.cast_nonneg _)
  have hsum2 : ∑ k ∈ Finset.range (r + 1), (n.choose k : ℝ) * x ^ k ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hrn 1))
      fun _ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx_pos.le _)
  have hbinom : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k = (1 + x) ^ n := by
    have hb := add_pow x (1 : ℝ) n
    rw [add_comm x 1] at hb
    rw [hb]
    exact Finset.sum_congr rfl fun k _ ↦ by simp [mul_comm]
  have hexp : (1 + x) ^ n ≤ Real.exp r :=
    calc
      (1 + x) ^ n ≤ (Real.exp x) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) n
      _ = Real.exp (n * x) := (Real.exp_nat_mul x n).symm
      _ = Real.exp r := congrArg Real.exp (mul_div_cancel₀ (r : ℝ) hn_pos.ne')
  have hdiv : (∑ k ∈ Finset.range (r + 1), (n.choose k : ℝ)) ≤ Real.exp r / x ^ r :=
    (le_div_iff₀ (pow_pos hx_pos r)).mpr ((hsum1.trans hsum2).trans (hbinom.trans_le hexp))
  refine hdiv.trans_eq ?_
  rw [show Real.exp (r : ℝ) = (Real.exp 1) ^ r by rw [← Real.exp_nat_mul, mul_one], ← div_pow]
  congr 1
  dsimp [x]
  rw [div_div_eq_mul_div]

/-- Tree-level rank-size-depth logarithmic chain:
`(t.rank : ℝ) ≤ log₂(t.leafCount) ∧ log₂(t.leafCount) ≤ t.depth`. -/
theorem rank_le_logb_leafCount_le_depth {ι β : Type*} (t : DecisionTree ι β) :
    (t.rank : ℝ) ≤ Real.logb 2 (t.leafCount : ℝ) ∧
      Real.logb 2 (t.leafCount : ℝ) ≤ (t.depth : ℝ) := by
  have hpos : (0 : ℝ) < (t.leafCount : ℝ) := Nat.cast_pos.mpr t.leafCount_pos
  refine ⟨?_, ?_⟩
  · rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
    exact_mod_cast t.two_pow_rank_le_leafCount
  · rw [Real.logb_le_iff_le_rpow (by norm_num) hpos, Real.rpow_natCast]
    exact_mod_cast t.leafCount_le_two_pow_depth

/-- Lower half of the Ehrenfeucht–Haussler rank-size inequality:
`rankComplexity f ≤ log₂(sizeComplexity f)`. -/
theorem rankComplexity_le_logb_sizeComplexity {ι β : Type*} [Finite ι] (f : (ι → Bool) → β) :
    (rankComplexity f : ℝ) ≤ Real.logb 2 (sizeComplexity f : ℝ) := by
  obtain ⟨t, _, hc, hs⟩ := exists_isReduced_computes_sizeComplexity f
  exact (Nat.cast_le.mpr (rankComplexity_le_rank hc)).trans
    ((rank_le_logb_leafCount_le_depth t).1.trans_eq (by rw [hs]))

/-- Upper half of the Ehrenfeucht–Haussler rank-size inequality: for every nonconstant function
`f : (ι → Bool) → β` over a finite index set `ι`,
`log₂(sizeComplexity f) ≤ rankComplexity f * log₂(e * card ι / rankComplexity f)`. -/
theorem logb_sizeComplexity_le_rankComplexity_mul_logb {ι β : Type*} [Fintype ι]
    {f : (ι → Bool) → β} (hf : ¬ Function.IsConst f) :
    Real.logb 2 (sizeComplexity f : ℝ) ≤
      (rankComplexity f : ℝ) *
        Real.logb 2 (Real.exp 1 * (Fintype.card ι : ℝ) / (rankComplexity f : ℝ)) := by
  obtain ⟨t, hred, hc, hr⟩ := exists_isReduced_computes_rankComplexity f
  have hr_pos : 1 ≤ rankComplexity f := by
    by_contra h0
    exact hf (rankComplexity_eq_zero_iff_isConst.mp (by omega))
  have hrn : rankComplexity f ≤ Fintype.card ι :=
    (rankComplexity_le_complexity f).trans (complexity_le_card f)
  have hsize_le : (sizeComplexity f : ℝ) ≤
      (Real.exp 1 * (Fintype.card ι : ℝ) / (rankComplexity f : ℝ)) ^ rankComplexity f := by
    calc
      (sizeComplexity f : ℝ) ≤ (t.leafCount : ℝ) :=
        Nat.cast_le.mpr (sizeComplexity_le_leafCount hc)
      _ ≤ (∑ k ∈ Finset.range (t.rank + 1), (Fintype.card ι).choose k : ℕ) := by
        exact_mod_cast leafCount_le_sum_choose_of_isReduced hred
      _ = ∑ k ∈ Finset.range (rankComplexity f + 1), ((Fintype.card ι).choose k : ℝ) := by
        rw [hr]
        push_cast
        rfl
      _ ≤ (Real.exp 1 * (Fintype.card ι : ℝ) / (rankComplexity f : ℝ)) ^ rankComplexity f :=
        sum_choose_le_exp_mul_div_pow hr_pos hrn
  have hs_pos : (0 : ℝ) < (sizeComplexity f : ℝ) := Nat.cast_pos.mpr (one_le_sizeComplexity f)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hs_pos hsize_le
  rwa [Real.logb_pow] at hlog

end RankSizeSandwich

end FunctionMeasures

end Cslib.DecisionTree
