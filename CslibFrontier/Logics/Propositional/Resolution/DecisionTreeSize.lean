/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.Resolution.TreeLike

/-!
# Exact Equivalence Between Tree-Like Resolution Size and Falsifying Decision-Tree Size

For any unsatisfiable CNF formula `φ : CNF V` over an arbitrary variable type `V` with decidable
equality, the minimum size of a tree-like resolution refutation of `φ` equals the minimum size of
a decision tree finding a falsified clause of `φ`. The equality holds identically in both standard
size
conventions:
* **Leaf-count convention**: minimum `d.toDecisionTree.leafCount` over `d : φ.Derivation` equals
  minimum `t.leafCount` over `t` satisfying `t.FindsFalsifiedClause φ`.
* **Total-node-count convention**: minimum `d.size` over `d : φ.Derivation` equals minimum
  `t.leafCount + t.nodeCount` over `t` satisfying `t.FindsFalsifiedClause φ`.

Consequently, any falsifying decision tree for `φ` of depth at most `d` yields a tree-like
resolution refutation with at most `2 ^ d` leaves (`≤ 2 * 2 ^ d - 1` nodes), and—when every clause
of `φ` has width at most `k`—a general resolution refutation of width at most `k + d + 1`.

## Main definitions

* `Cslib.Logic.PL.CNF.minTreeLikeRefutationLeaves`,
  `Cslib.Logic.PL.CNF.minFalsifyingTreeLeaves`: minimum leaf counts of tree-like resolution
  refutations and falsifying decision trees.
* `Cslib.Logic.PL.CNF.minTreeLikeRefutationSize`,
  `Cslib.Logic.PL.CNF.minFalsifyingTreeNodes`: minimum total node counts of tree-like resolution
  refutations and falsifying decision trees.

## Main results

* `Cslib.Logic.PL.CNF.exists_findsFalsifiedClause_of_not_satisfiable`: every unsatisfiable CNF
  formula admits a falsifying decision tree of depth at most `φ.vars.length`.
* `Cslib.Logic.PL.CNF.minTreeLikeRefutationLeaves_eq`: exact leaf-size equality between tree-like
  resolution refutations and falsifying decision trees.
* `Cslib.Logic.PL.CNF.minTreeLikeRefutationSize_eq`: exact total-node-size equality between
  tree-like resolution refutations and falsifying decision trees.
* `Cslib.Logic.PL.CNF.exists_derivation_of_depth_le`,
  `Cslib.Logic.PL.CNF.refutableInWidth_of_findsFalsifiedClause_depth_le`: depth-to-size and
  depth-to-width bounds for resolution refutations.
-/

public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*}

/-- Every unsatisfiable CNF formula `φ : CNF V` admits a falsifying decision tree of depth at most
`φ.vars.length` (even when the ambient variable type `V` is infinite). -/
theorem exists_findsFalsifiedClause_of_not_satisfiable {φ : CNF V}
    (hunsat : ¬ φ.Satisfiable) :
    ∃ t : DecisionTree V (Clause V),
      t.FindsFalsifiedClause φ ∧ t.depth ≤ φ.vars.length := by
  classical
  let pickClause : (V → Bool) → Clause V := fun b =>
    (φ.find? fun c => !c.eval b).getD []
  refine ⟨DecisionTree.queryAll pickClause φ.vars (fun _ => false), fun σ => ?_,
    DecisionTree.depth_queryAll_le _ _ _⟩
  rw [DecisionTree.eval_queryAll]
  let b : V → Bool := fun j => if j ∈ φ.vars then σ j else false
  have hb_false : φ.eval b = false :=
    Bool.eq_false_iff.mpr fun hsat => hunsat ⟨b, hsat⟩
  obtain ⟨c₀, hc₀_mem, hc₀_false⟩ : ∃ c ∈ φ, c.eval b = false := by
    by_contra hall
    push Not at hall
    have htrue : φ.eval b = true :=
      (eval_eq_true_iff b φ).mpr fun c hc => Bool.eq_true_of_not_eq_false (hall c hc)
    exact Bool.false_ne_true (hb_false.symm.trans htrue)
  have hsome : (φ.find? fun c => !c.eval b).isSome := by
    rw [List.find?_isSome]
    exact ⟨c₀, hc₀_mem, by simp [hc₀_false]⟩
  obtain ⟨c, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hpick : pickClause b = c := by simp [pickClause, hfind]
  rw [hpick]
  have hc_mem : c ∈ φ := List.mem_of_find?_eq_some hfind
  have hc_b : c.eval b = false := by simpa using List.find?_some hfind
  refine ⟨hc_mem, ?_⟩
  have hcongr : c.eval σ = c.eval b := by
    rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
    refine exists_congr fun l => and_congr_right fun hl => ?_
    have hl_var : l.1 ∈ φ.vars :=
      List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc_mem, hl⟩, rfl⟩
    simp [b, hl_var]
  exact hcongr.trans hc_b

variable [DecidableEq V]

/-- Minimum number of leaves among all tree-like resolution refutations of `φ`. -/
noncomputable def minTreeLikeRefutationLeaves (φ : CNF V) : ℕ :=
  sInf {s : ℕ | ∃ d : φ.Derivation [], d.toDecisionTree.leafCount = s}

/-- Minimum number of leaves among all falsifying decision trees for `φ`. -/
noncomputable def minFalsifyingTreeLeaves (φ : CNF V) : ℕ :=
  sInf {s : ℕ | ∃ t : DecisionTree V (Clause V), t.FindsFalsifiedClause φ ∧ t.leafCount = s}

/-- Minimum number of nodes (`Derivation.size`) among all tree-like resolution refutations of
`φ`. -/
noncomputable def minTreeLikeRefutationSize (φ : CNF V) : ℕ :=
  sInf {s : ℕ | ∃ d : φ.Derivation [], d.size = s}

/-- Minimum total node count (`leafCount + nodeCount`) among all falsifying decision trees for
`φ`. -/
noncomputable def minFalsifyingTreeNodes (φ : CNF V) : ℕ :=
  sInf {s : ℕ | ∃ t : DecisionTree V (Clause V),
    t.FindsFalsifiedClause φ ∧ t.leafCount + t.nodeCount = s}

/-- **Tree-like resolution leaf size equals DPLL leaf size**: for any unsatisfiable formula `φ`,
the minimum leaf count of a tree-like resolution refutation equals the minimum leaf count of a
falsifying decision tree. -/
theorem minTreeLikeRefutationLeaves_eq {φ : CNF V} (hunsat : ¬ φ.Satisfiable) :
    minTreeLikeRefutationLeaves φ = minFalsifyingTreeLeaves φ := by
  obtain ⟨t₀, ht₀, _⟩ := exists_findsFalsifiedClause_of_not_satisfiable hunsat
  obtain ⟨d₀, _⟩ := ht₀.exists_derivation_leafCount_le
  have hdt_ne : {s : ℕ | ∃ t : DecisionTree V (Clause V),
      t.FindsFalsifiedClause φ ∧ t.leafCount = s}.Nonempty := ⟨t₀.leafCount, t₀, ht₀, rfl⟩
  have hres_ne : {s : ℕ | ∃ d : φ.Derivation [], d.toDecisionTree.leafCount = s}.Nonempty :=
    ⟨d₀.toDecisionTree.leafCount, d₀, rfl⟩
  apply le_antisymm
  · obtain ⟨t, ht, htle⟩ := Nat.sInf_mem hdt_ne
    obtain ⟨d, hdle⟩ := ht.exists_derivation_leafCount_le
    calc minTreeLikeRefutationLeaves φ ≤ d.toDecisionTree.leafCount := Nat.sInf_le ⟨d, rfl⟩
      _ ≤ t.leafCount := hdle
      _ = minFalsifyingTreeLeaves φ := htle
  · obtain ⟨d, hd⟩ := Nat.sInf_mem hres_ne
    calc minFalsifyingTreeLeaves φ ≤ d.toDecisionTree.leafCount :=
          Nat.sInf_le ⟨d.toDecisionTree, d.findsFalsifiedClause_toDecisionTree, rfl⟩
      _ = minTreeLikeRefutationLeaves φ := hd

/-- **Tree-like resolution node size equals DPLL total node size**: for any unsatisfiable formula
`φ`, the minimum node count `d.size` of a tree-like resolution refutation equals the minimum total
node count `t.leafCount + t.nodeCount` of a falsifying decision tree. -/
theorem minTreeLikeRefutationSize_eq {φ : CNF V} (hunsat : ¬ φ.Satisfiable) :
    minTreeLikeRefutationSize φ = minFalsifyingTreeNodes φ := by
  obtain ⟨t₀, ht₀, _⟩ := exists_findsFalsifiedClause_of_not_satisfiable hunsat
  obtain ⟨d₀, _⟩ := ht₀.exists_derivation
  have hdt_ne : {s : ℕ | ∃ t : DecisionTree V (Clause V),
      t.FindsFalsifiedClause φ ∧ t.leafCount + t.nodeCount = s}.Nonempty :=
    ⟨t₀.leafCount + t₀.nodeCount, t₀, ht₀, rfl⟩
  have hres_ne : {s : ℕ | ∃ d : φ.Derivation [], d.size = s}.Nonempty := ⟨d₀.size, d₀, rfl⟩
  apply le_antisymm
  · obtain ⟨t, ht, htle⟩ := Nat.sInf_mem hdt_ne
    obtain ⟨d, hd⟩ := ht.exists_derivation
    have ht_nodes : t.leafCount + t.nodeCount = 2 * t.leafCount - 1 := by
      have := t.leafCount_eq_nodeCount_add_one
      omega
    calc minTreeLikeRefutationSize φ ≤ d.size := Nat.sInf_le ⟨d, rfl⟩
      _ ≤ 2 * t.leafCount - 1 := by omega
      _ = t.leafCount + t.nodeCount := ht_nodes.symm
      _ = minFalsifyingTreeNodes φ := htle
  · obtain ⟨d, hd⟩ := Nat.sInf_mem hres_ne
    have hd_nodes : d.toDecisionTree.leafCount + d.toDecisionTree.nodeCount = d.size := by
      have h1 := d.two_mul_leafCount_toDecisionTree
      have h2 := d.toDecisionTree.leafCount_eq_nodeCount_add_one
      omega
    calc minFalsifyingTreeNodes φ
        ≤ d.toDecisionTree.leafCount + d.toDecisionTree.nodeCount :=
          Nat.sInf_le ⟨d.toDecisionTree, d.findsFalsifiedClause_toDecisionTree, rfl⟩
      _ = d.size := hd_nodes
      _ = minTreeLikeRefutationSize φ := hd

/-- A falsifying decision tree for `φ` of depth at most `d` yields a tree-like resolution
refutation of `φ` with at most `2 ^ d` leaves and at most `2 * 2 ^ d - 1` nodes. -/
theorem exists_derivation_of_depth_le {φ : CNF V} {t : DecisionTree V (Clause V)}
    (ht : t.FindsFalsifiedClause φ) {d : ℕ} (hd : t.depth ≤ d) :
    ∃ der : φ.Derivation [],
      der.toDecisionTree.leafCount ≤ 2 ^ d ∧ der.size ≤ 2 * 2 ^ d - 1 := by
  obtain ⟨der, hsize⟩ := ht.exists_derivation
  have hleaves : t.leafCount ≤ 2 ^ d :=
    t.leafCount_le_two_pow_depth.trans (Nat.pow_le_pow_right two_pos hd)
  have htwo := der.two_mul_leafCount_toDecisionTree
  refine ⟨der, ?_, ?_⟩ <;> omega

/-- If every clause of `φ` has width at most `k` and `φ` admits a falsifying decision tree of depth
at most `d`, then `φ` is refutable in resolution width at most `k + (d + 1)`. -/
theorem refutableInWidth_of_findsFalsifiedClause_depth_le {φ : CNF V} {k d : ℕ}
    (hk : ∀ c ∈ φ, c.width ≤ k) {t : DecisionTree V (Clause V)} (ht : t.FindsFalsifiedClause φ)
    (hd : t.depth ≤ d) :
    φ.RefutableInWidth (k + (d + 1)) := by
  obtain ⟨der, _, hsize⟩ := exists_derivation_of_depth_le ht hd
  refine RefutableInWidth.of_derivation hk der rfl ?_
  rw [pow_succ']
  omega

end Cslib.Logic.PL.CNF
