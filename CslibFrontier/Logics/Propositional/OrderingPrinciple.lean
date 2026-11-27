/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import CslibFrontier.Algorithms.Lean.DPLL.SearchTree
public import CslibFrontier.Logics.Propositional.CNF
public import CslibFrontier.Logics.Propositional.Resolution.ProverDelayer
public import CslibFrontier.Logics.Propositional.Resolution.TreeLike
public import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

/-!
# The Propositional Ordering Principle and Tree-Like Resolution / DPLL Lower Bounds

The **Ordering Principle** `OP_n` asserts in propositional conjunctive normal form that a binary
relation `P_{i, j}` (`i ≠ j` in `Fin n`) on an `n`-element set is transitive and asymmetric (hence
a strict partial order) while possessing no minimal element. Introduced by Krishnamurthy and
shown to have polynomial-size general resolution refutations by Stålmarck, `OP_n` requires
exponentially large tree-like resolution refutations and DPLL search trees.

## Main definitions

* `CslibFrontier.Logics.Propositional.PartialAssignExtends`: domain-extension preorder on partial
  Boolean assignments `V → Option Bool`.
* `CslibFrontier.Logics.Propositional.OrderingVar`: off-diagonal variable `P_{i, j}` (`row col :
  Fin n`, `row_ne_col : row ≠ col`) of the `n`-element Ordering Principle.
* `CslibFrontier.Logics.Propositional.orderedColVars`: ordered list of the `n - 1` variables in
  column `j` sorted by increasing row index.
* `CslibFrontier.Logics.Propositional.transitivityClause`,
  `CslibFrontier.Logics.Propositional.antisymmetryClause`,
  `CslibFrontier.Logics.Propositional.nonMinimalityClause`,
  `CslibFrontier.Logics.Propositional.orderingPrinciple`: the clause families and full Ordering
  Principle CNF formula `OP_n = A_n ++ B_n ++ D_n`.

## Main results

* `CslibFrontier.Logics.Propositional.pow_pot_le_leafCount_of_state_delayer`,
  `CslibFrontier.Logics.Propositional.pow_pot_le_size_of_state_delayer`,
  `CslibFrontier.Logics.Propositional.pow_pot_le_dpll_leafCount_of_state_delayer`: symmetric
  state-space Prover–Delayer lower bounds for tree-like resolution derivations and DPLL trees.
* `CslibFrontier.Logics.Propositional.not_satisfiable_orderingPrinciple`,
  `CslibFrontier.Logics.Propositional.satisfiable_orderingPrinciple_iff`: `OP_n` is satisfiable iff
  `n = 0`.
* `CslibFrontier.Logics.Propositional.two_pow_le_leafCount_orderingPrinciple`,
  `CslibFrontier.Logics.Propositional.two_pow_le_size_orderingPrinciple`,
  `CslibFrontier.Logics.Propositional.two_pow_le_dpll_leafCount_relabel_orderingPrinciple`,
  `CslibFrontier.Logics.Propositional.two_pow_le_leafCount_searchTree_orderingPrinciple`: every
  tree-like resolution refutation and DPLL search tree of `OP_n` (`n ≥ 2`) has at least
  `2 ^ ((n - 1) / 2)` leaves and nodes.
-/

public section

namespace CslibFrontier.Logics.Propositional

open Cslib.Logic.PL

section StateDelayer

variable {V : Type*}

/-- Domain-extension relation on partial Boolean assignments `V → Option Bool`. -/
def PartialAssignExtends (ρ ρ' : V → Option Bool) : Prop :=
  ∀ v b, ρ v = some b → ρ' v = some b

theorem partialAssignExtends_iff {ρ ρ' : V → Option Bool} :
    PartialAssignExtends ρ ρ' ↔ ∀ v b, ρ v = some b → ρ' v = some b :=
  Iff.rfl

@[simp]
theorem partialAssignExtends_refl (ρ : V → Option Bool) : PartialAssignExtends ρ ρ :=
  fun _ _ h ↦ h

theorem PartialAssignExtends.trans {ρ₁ ρ₂ ρ₃ : V → Option Bool}
    (h₁₂ : PartialAssignExtends ρ₁ ρ₂) (h₂₃ : PartialAssignExtends ρ₂ ρ₃) :
    PartialAssignExtends ρ₁ ρ₃ :=
  fun v b hv ↦ h₂₃ v b (h₁₂ v b hv)

theorem falsifiedBy_of_extends {ρ ρ' : V → Option Bool} (hext : PartialAssignExtends ρ ρ')
    {c : Clause V} (hfals : Clause.FalsifiedBy ρ c) : Clause.FalsifiedBy ρ' c :=
  fun l hl ↦ hext l.1 (!l.2) (hfals l hl)

private theorem one_le_decisionTree_leafCount {α : Type*} :
    ∀ t : Cslib.DecisionTree V α, 1 ≤ t.leafCount
  | .leaf _ => le_rfl
  | .node _ t₀ _ => (one_le_decisionTree_leafCount t₀).trans (Nat.le_add_right _ _)

/-- **State-Space Prover–Delayer Leaf Lower Bound** for tree-like resolution derivations. -/
theorem pow_pot_le_leafCount_of_state_delayer [DecidableEq V] {S : Type*} (φ : CNF V)
    (eval : S → V → Option Bool) (pot : S → ℕ) (inv : S → Prop)
    (hno : ∀ s, inv s → ∀ c ∈ φ, ¬ Clause.FalsifiedBy (eval s) c)
    (hsplit : ∀ s, inv s → ∀ v : V, eval s v = none → 0 < pot s →
      ∃ s₀ s₁, inv s₀ ∧ inv s₁ ∧
        PartialAssignExtends (eval s) (eval s₀) ∧
        PartialAssignExtends (eval s) (eval s₁) ∧
        eval s₀ v = some false ∧ eval s₁ v = some true ∧
        pot s - 1 ≤ pot s₀ ∧ pot s - 1 ≤ pot s₁)
    {c : Clause V} (d : φ.Derivation c) :
    ∀ {s : S}, inv s → Clause.FalsifiedBy (eval s) c →
      2 ^ pot s ≤ d.toDecisionTree.leafCount := by
  induction d with
  | mem hc =>
    intro s hs hfals
    exact False.elim (hno s hs _ hc hfals)
  | @resolvent c₁ c₂ v d₁ d₂ _ _ ih₁ ih₂ =>
    intro s hs hfals
    simp only [CNF.Derivation.toDecisionTree, Cslib.DecisionTree.leafCount]
    by_cases hpot : pot s = 0
    · rw [hpot, Nat.pow_zero]
      exact (one_le_decisionTree_leafCount d₁.toDecisionTree).trans (Nat.le_add_right _ _)
    · have hpos : 0 < pot s := Nat.pos_of_ne_zero hpot
      cases hv : eval s v with
      | none =>
        obtain ⟨s₀, s₁, hs₀, hs₁, hext₀, hext₁, hv₀, hv₁, hpot₀, hpot₁⟩ :=
          hsplit s hs v hv hpos
        have hleft : 2 ^ pot s₀ ≤ d₁.toDecisionTree.leafCount :=
          ih₁ hs₀ ((falsifiedBy_of_extends hext₀ hfals).left_of_resolvent hv₀)
        have hright : 2 ^ pot s₁ ≤ d₂.toDecisionTree.leafCount :=
          ih₂ hs₁ ((falsifiedBy_of_extends hext₁ hfals).right_of_resolvent hv₁)
        have hpow₀ : 2 ^ (pot s - 1) ≤ d₁.toDecisionTree.leafCount :=
          (Nat.pow_le_pow_right (by decide) hpot₀).trans hleft
        have hpow₁ : 2 ^ (pot s - 1) ≤ d₂.toDecisionTree.leafCount :=
          (Nat.pow_le_pow_right (by decide) hpot₁).trans hright
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpot
        rw [hk, Nat.succ_sub_one] at hpow₀ hpow₁
        rw [hk, Nat.pow_succ, Nat.mul_two]
        exact Nat.add_le_add hpow₀ hpow₁
      | some b =>
        cases b
        · exact (ih₁ hs (hfals.left_of_resolvent hv)).trans (Nat.le_add_right _ _)
        · exact (ih₂ hs (hfals.right_of_resolvent hv)).trans (Nat.le_add_left _ _)

/-- **State-Space Prover–Delayer Node Lower Bound** for tree-like resolution refutations. -/
theorem pow_pot_le_size_of_state_delayer [DecidableEq V] {S : Type*} (φ : CNF V)
    (eval : S → V → Option Bool) (pot : S → ℕ) (inv : S → Prop)
    (hno : ∀ s, inv s → ∀ c ∈ φ, ¬ Clause.FalsifiedBy (eval s) c)
    (hsplit : ∀ s, inv s → ∀ v : V, eval s v = none → 0 < pot s →
      ∃ s₀ s₁, inv s₀ ∧ inv s₁ ∧
        PartialAssignExtends (eval s) (eval s₀) ∧
        PartialAssignExtends (eval s) (eval s₁) ∧
        eval s₀ v = some false ∧ eval s₁ v = some true ∧
        pot s - 1 ≤ pot s₀ ∧ pot s - 1 ≤ pot s₁)
    {s₀ : S} (hs₀ : inv s₀) (d : φ.Derivation []) :
    2 ^ pot s₀ ≤ d.size :=
  (pow_pot_le_leafCount_of_state_delayer φ eval pot inv hno hsplit d hs₀
    (Clause.falsifiedBy_nil _)).trans d.leafCount_toDecisionTree_le_size

/-- **State-Space Prover–Delayer DPLL Search-Tree Lower Bound**. -/
theorem pow_pot_le_dpll_leafCount_of_state_delayer {S : Type*} (φ : CNF V)
    (eval : S → V → Option Bool) (pot : S → ℕ) (inv : S → Prop)
    (hno : ∀ s, inv s → ∀ c ∈ φ, ¬ Clause.FalsifiedBy (eval s) c)
    (hsplit : ∀ s, inv s → ∀ v : V, eval s v = none → 0 < pot s →
      ∃ s₀ s₁, inv s₀ ∧ inv s₁ ∧
        PartialAssignExtends (eval s) (eval s₀) ∧
        PartialAssignExtends (eval s) (eval s₁) ∧
        eval s₀ v = some false ∧ eval s₁ v = some true ∧
        pot s - 1 ≤ pot s₀ ∧ pot s - 1 ≤ pot s₁)
    {s₀ : S} (hs₀ : inv s₀) {t : Cslib.DecisionTree V (Clause V)}
    (ht : t.FindsFalsifiedClause φ) :
    2 ^ pot s₀ ≤ t.leafCount := by
  classical
  obtain ⟨d, hd⟩ := ht.exists_derivation_leafCount_le
  exact (pow_pot_le_leafCount_of_state_delayer φ eval pot inv hno hsplit d hs₀
    (Clause.falsifiedBy_nil _)).trans hd

end StateDelayer

section OrderingVariables

/-- Propositional variable `P_{i, j}` (`row ≠ col` in `Fin n`) of the `n`-element Ordering
Principle. -/
@[ext]
structure OrderingVar (n : ℕ) where
  /-- Row element `i : Fin n`. -/
  row : Fin n
  /-- Column element `j : Fin n`. -/
  col : Fin n
  /-- Off-diagonal condition `row ≠ col`. -/
  row_ne_col : row ≠ col
  deriving DecidableEq

namespace OrderingVar

variable {n : ℕ}

def equivOffDiag (n : ℕ) : OrderingVar n ≃ { p : Fin n × Fin n // p.1 ≠ p.2 } where
  toFun v := ⟨(v.row, v.col), v.row_ne_col⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv v := by cases v; rfl
  right_inv p := by rcases p with ⟨⟨_, _⟩, _⟩; rfl

instance instFintype (n : ℕ) : Fintype (OrderingVar n) :=
  Fintype.ofEquiv { p : Fin n × Fin n // p.1 ≠ p.2 } (equivOffDiag n).symm

@[expose]
def rowRank (v : OrderingVar n) : ℕ :=
  if v.row.val < v.col.val then v.row.val else v.row.val - 1

theorem rowRank_lt (v : OrderingVar n) : v.rowRank < n - 1 := by
  have hne : v.row.val ≠ v.col.val := fun h ↦ v.row_ne_col (Fin.ext h)
  have hr := v.row.isLt
  have hc := v.col.isLt
  unfold rowRank
  split_ifs with hlt <;> omega

theorem row_val_of_rowRank (v : OrderingVar n) :
    v.row.val = if v.rowRank < v.col.val then v.rowRank else v.rowRank + 1 := by
  have hne : v.row.val ≠ v.col.val := fun h ↦ v.row_ne_col (Fin.ext h)
  unfold rowRank
  split_ifs <;> omega

@[expose]
def colMajorIdx (v : OrderingVar n) : ℕ :=
  v.col.val * (n - 1) + v.rowRank

theorem colMajorIdx_lt (v : OrderingVar n) : v.colMajorIdx < n * (n - 1) := by
  have hr := v.rowRank_lt
  have hc := v.col.isLt
  calc v.col.val * (n - 1) + v.rowRank
      < v.col.val * (n - 1) + (n - 1) := Nat.add_lt_add_left hr _
    _ = (v.col.val + 1) * (n - 1) := by rw [Nat.succ_mul]
    _ ≤ n * (n - 1) := Nat.mul_le_mul_right _ hc

theorem colMajorIdx_injective (n : ℕ) : Function.Injective (colMajorIdx (n := n)) := by
  intro u v huv
  have hu := u.rowRank_lt
  have hv := v.rowRank_lt
  have hcol : u.col.val = v.col.val := by
    unfold colMajorIdx at huv
    rcases lt_trichotomy u.col.val v.col.val with hc | hc | hc
    · have hle : (u.col.val + 1) * (n - 1) ≤ v.col.val * (n - 1) :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.succ_mul] at hle
      omega
    · exact hc
    · have hle : (v.col.val + 1) * (n - 1) ≤ u.col.val * (n - 1) :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.succ_mul] at hle
      omega
  have hrank : u.rowRank = v.rowRank := by
    unfold colMajorIdx at huv
    rw [hcol] at huv
    exact Nat.add_left_cancel huv
  ext
  · rw [u.row_val_of_rowRank, v.row_val_of_rowRank, hcol, hrank]
  · exact hcol

end OrderingVar

@[expose]
def orderingVarEquivFin (n : ℕ) : OrderingVar n ≃ Fin (n * (n - 1)) where
  toFun v := ⟨v.colMajorIdx, v.colMajorIdx_lt⟩
  invFun k :=
    let j : ℕ := k.val / (n - 1)
    let r : ℕ := k.val % (n - 1)
    let i : ℕ := if r < j then r else r + 1
    have hn : 1 < n := by
      have hk := k.isLt
      rcases n with _ | _ | m
      · simp at hk
      · simp at hk
      · omega
    have hj : j < n := by
      have hk : k.val < (n - 1) * n := by simp [Nat.mul_comm]
      exact Nat.div_lt_of_lt_mul hk
    have hr : r < n - 1 := Nat.mod_lt _ (by omega)
    have hi : i < n := by dsimp [i]; split_ifs <;> omega
    have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
      intro h
      have hv : i = j := congrArg Fin.val h
      dsimp [i] at hv
      split_ifs at hv <;> omega
    ⟨⟨i, hi⟩, ⟨j, hj⟩, hne⟩
  left_inv v := by
    have hr := v.rowRank_lt
    have hpos : 0 < n - 1 := by omega
    have hdiv : v.colMajorIdx / (n - 1) = v.col.val := by
      unfold OrderingVar.colMajorIdx
      rw [Nat.mul_comm v.col.val (n - 1), Nat.mul_add_div hpos,
        Nat.div_eq_zero_iff.mpr (Or.inr hr), Nat.add_zero]
    have hmod : v.colMajorIdx % (n - 1) = v.rowRank := by
      unfold OrderingVar.colMajorIdx
      rw [Nat.mul_comm v.col.val (n - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    ext
    · dsimp
      rw [hdiv, hmod, ← v.row_val_of_rowRank]
    · dsimp
      exact hdiv
  right_inv k := by
    ext
    have hk := k.isLt
    have hpos : 0 < n - 1 := by
      rcases n with _ | _ | m
      · simp at hk
      · simp at hk
      · omega
    dsimp [OrderingVar.colMajorIdx, OrderingVar.rowRank]
    have hrr :
        (if (if k.val % (n - 1) < k.val / (n - 1) then k.val % (n - 1)
             else k.val % (n - 1) + 1) < k.val / (n - 1)
         then if k.val % (n - 1) < k.val / (n - 1) then k.val % (n - 1)
              else k.val % (n - 1) + 1
         else (if k.val % (n - 1) < k.val / (n - 1) then k.val % (n - 1)
               else k.val % (n - 1) + 1) - 1) = k.val % (n - 1) := by
      split_ifs <;> omega
    rw [hrr, Nat.mul_comm, Nat.div_add_mod]

@[simp]
theorem card_orderingVar (n : ℕ) : Fintype.card (OrderingVar n) = n * (n - 1) := by
  rw [Fintype.card_congr (orderingVarEquivFin n), Fintype.card_fin]

end OrderingVariables

section OrderingFormula

@[expose]
def orderedColVars (n : ℕ) (j : Fin n) : List (OrderingVar n) :=
  (List.finRange n).filterMap fun i ↦ if h : i ≠ j then some ⟨i, j, h⟩ else none

@[simp]
theorem mem_orderedColVars {n : ℕ} {j : Fin n} {v : OrderingVar n} :
    v ∈ orderedColVars n j ↔ v.col = j := by
  simp only [orderedColVars, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hne : i ≠ j
    · rw [dite_eq_left hne] at hi
      exact (Option.some.inj hi) ▸ rfl
    · rw [dite_eq_right hne] at hi
      cases hi
  · intro hj
    have hne : v.row ≠ j := hj ▸ v.row_ne_col
    refine ⟨v.row, ?_⟩
    rw [dite_eq_left hne]
    exact congrArg some (OrderingVar.ext rfl hj.symm)

@[expose]
def transitivityClause {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Clause (OrderingVar n) :=
  [(⟨i, j, hij⟩, false), (⟨j, k, hjk⟩, false), (⟨i, k, hik⟩, true)]

@[expose]
def antisymmetryClause {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Clause (OrderingVar n) :=
  [(⟨i, j, hij⟩, false), (⟨j, i, hij.symm⟩, false)]

@[expose]
def nonMinimalityClause {n : ℕ} (j : Fin n) : Clause (OrderingVar n) :=
  (orderedColVars n j).map (·, true)

def transitivityCNF (n : ℕ) : CNF (OrderingVar n) :=
  (List.finRange n).flatMap fun i ↦
    (List.finRange n).flatMap fun j ↦
      (List.finRange n).filterMap fun k ↦
        if hij : i ≠ j then
          if hjk : j ≠ k then
            if hik : i ≠ k then
              some (transitivityClause i j k hij hjk hik)
            else none
          else none
        else none

def antisymmetryCNF (n : ℕ) : CNF (OrderingVar n) :=
  (List.finRange n).flatMap fun i ↦
    (List.finRange n).filterMap fun j ↦
      if hij : i ≠ j then some (antisymmetryClause i j hij) else none

def nonMinimalityCNF (n : ℕ) : CNF (OrderingVar n) :=
  (List.finRange n).map nonMinimalityClause

def orderingPrinciple (n : ℕ) : CNF (OrderingVar n) :=
  transitivityCNF n ++ antisymmetryCNF n ++ nonMinimalityCNF n

theorem mem_transitivityCNF {n : ℕ} {c : Clause (OrderingVar n)} :
    c ∈ transitivityCNF n ↔
      ∃ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
        c = transitivityClause i j k hij hjk hik := by
  simp only [transitivityCNF, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨i, j, k, h⟩
    by_cases hij : i ≠ j
    · rw [dite_eq_left hij] at h
      by_cases hjk : j ≠ k
      · rw [dite_eq_left hjk] at h
        by_cases hik : i ≠ k
        · rw [dite_eq_left hik] at h
          exact ⟨i, j, k, hij, hjk, hik, (Option.some.inj h).symm⟩
        · rw [dite_eq_right hik] at h; cases h
      · rw [dite_eq_right hjk] at h; cases h
    · rw [dite_eq_right hij] at h; cases h
  · rintro ⟨i, j, k, hij, hjk, hik, rfl⟩
    refine ⟨i, j, k, ?_⟩
    rw [dite_eq_left hij, dite_eq_left hjk, dite_eq_left hik]

theorem mem_antisymmetryCNF {n : ℕ} {c : Clause (OrderingVar n)} :
    c ∈ antisymmetryCNF n ↔
      ∃ (i j : Fin n) (hij : i ≠ j), c = antisymmetryClause i j hij := by
  simp only [antisymmetryCNF, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨i, j, h⟩
    by_cases hij : i ≠ j
    · rw [dite_eq_left hij] at h
      exact ⟨i, j, hij, (Option.some.inj h).symm⟩
    · rw [dite_eq_right hij] at h; cases h
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨i, j, ?_⟩
    rw [dite_eq_left hij]

theorem mem_nonMinimalityCNF {n : ℕ} {c : Clause (OrderingVar n)} :
    c ∈ nonMinimalityCNF n ↔ ∃ j : Fin n, c = nonMinimalityClause j := by
  simp only [nonMinimalityCNF, List.mem_map, List.mem_finRange, true_and]
  exact ⟨fun ⟨j, h⟩ ↦ ⟨j, h.symm⟩, fun ⟨j, h⟩ ↦ ⟨j, h.symm⟩⟩

theorem mem_orderingPrinciple {n : ℕ} {c : Clause (OrderingVar n)} :
    c ∈ orderingPrinciple n ↔
      c ∈ transitivityCNF n ∨ c ∈ antisymmetryCNF n ∨ c ∈ nonMinimalityCNF n := by
  unfold orderingPrinciple
  simp only [List.mem_append, or_assoc]

@[simp]
theorem eval_transitivityClause {n : ℕ} (σ : OrderingVar n → Bool) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (transitivityClause i j k hij hjk hik).eval σ = true ↔
      (σ ⟨i, j, hij⟩ = true ∧ σ ⟨j, k, hjk⟩ = true → σ ⟨i, k, hik⟩ = true) := by
  simp only [transitivityClause, Clause.eval_cons, Clause.eval_nil, Bool.or_false, Literal.eval_mk]
  cases σ ⟨i, j, hij⟩ <;> cases σ ⟨j, k, hjk⟩ <;> cases σ ⟨i, k, hik⟩ <;> simp

@[simp]
theorem eval_antisymmetryClause {n : ℕ} (σ : OrderingVar n → Bool) (i j : Fin n) (hij : i ≠ j) :
    (antisymmetryClause i j hij).eval σ = true ↔
      ¬ (σ ⟨i, j, hij⟩ = true ∧ σ ⟨j, i, hij.symm⟩ = true) := by
  simp only [antisymmetryClause, Clause.eval_cons, Clause.eval_nil, Bool.or_false, Literal.eval_mk]
  cases σ ⟨i, j, hij⟩ <;> cases σ ⟨j, i, hij.symm⟩ <;> simp

@[simp]
theorem mem_nonMinimalityClause {n : ℕ} {j : Fin n} {l : Literal (OrderingVar n)} :
    l ∈ nonMinimalityClause j ↔ l.1.col = j ∧ l.2 = true := by
  simp only [nonMinimalityClause, List.mem_map, mem_orderedColVars]
  constructor
  · rintro ⟨v, rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hcol, hpol⟩
    rcases l with ⟨v, b⟩
    subst hpol
    exact ⟨v, hcol, rfl⟩

@[simp]
theorem eval_nonMinimalityClause {n : ℕ} (σ : OrderingVar n → Bool) (j : Fin n) :
    (nonMinimalityClause j).eval σ = true ↔ ∃ (i : Fin n) (hij : i ≠ j), σ ⟨i, j, hij⟩ = true := by
  rw [Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨⟨v, b⟩, hmem, hσ⟩
    obtain ⟨hcol, rfl⟩ := mem_nonMinimalityClause.mp hmem
    have hv : (⟨v.row, j, hcol ▸ v.row_ne_col⟩ : OrderingVar n) = v :=
      OrderingVar.ext rfl hcol.symm
    exact ⟨v.row, hcol ▸ v.row_ne_col, by rwa [hv]⟩
  · rintro ⟨i, hij, hσ⟩
    exact ⟨(⟨i, j, hij⟩, true), mem_nonMinimalityClause.mpr ⟨rfl, rfl⟩, hσ⟩

/-- **Unsatisfiability of the Ordering Principle** for `n > 0`. -/
theorem not_satisfiable_orderingPrinciple {n : ℕ} (hn : 0 < n) :
    ¬ (orderingPrinciple n).Satisfiable := by
  rintro ⟨σ, hσ⟩
  rw [CNF.eval_eq_true_iff] at hσ
  let rel : Fin n → Fin n → Prop := fun i j ↦ ∃ hij : i ≠ j, σ ⟨i, j, hij⟩ = true
  have hasym : ∀ {i j : Fin n}, rel i j → ¬ rel j i := by
    rintro i j ⟨hij, h₁⟩ ⟨_, h₂⟩
    have hb := hσ _ (mem_orderingPrinciple.mpr
      (Or.inr (Or.inl (mem_antisymmetryCNF.mpr ⟨i, j, hij, rfl⟩))))
    exact (eval_antisymmetryClause σ i j hij).mp hb ⟨h₁, h₂⟩
  have htrans : ∀ {i j k : Fin n}, rel i j → rel j k → rel i k := by
    rintro i j k ⟨hij, h₁⟩ ⟨hjk, h₂⟩
    have hik : i ≠ k := by
      rintro rfl
      exact hasym ⟨hij, h₁⟩ ⟨hjk, h₂⟩
    have ha := hσ _ (mem_orderingPrinciple.mpr
      (Or.inl (mem_transitivityCNF.mpr ⟨i, j, k, hij, hjk, hik, rfl⟩)))
    exact ⟨hik, (eval_transitivityClause σ i j k hij hjk hik).mp ha ⟨h₁, h₂⟩⟩
  have hstep : ∀ (m : ℕ) (j : Fin n), ∃ i : Fin n, rel i j ∧
      (Finset.univ.filter (fun x ↦ rel x i)).card + m ≤
        (Finset.univ.filter (fun x ↦ rel x j)).card := by
    intro m
    induction m with
    | zero =>
      intro j
      have hd := hσ _ (mem_orderingPrinciple.mpr
        (Or.inr (Or.inr (mem_nonMinimalityCNF.mpr ⟨j, rfl⟩))))
      obtain ⟨i, hij, hrel⟩ := (eval_nonMinimalityClause σ j).mp hd
      have hsub : Finset.univ.filter (fun x ↦ rel x i) ⊂
          Finset.univ.filter (fun x ↦ rel x j) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hrel⟩, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rintro ⟨hii, _⟩
          exact hii rfl
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact htrans hx ⟨hij, hrel⟩
      have hlt := Finset.card_lt_card hsub
      exact ⟨i, ⟨hij, hrel⟩, by omega⟩
    | succ m ih =>
      intro j
      obtain ⟨i₁, hrel₁, hcard₁⟩ := ih j
      obtain ⟨i₀, hrel₀, hcard₀⟩ := ih i₁
      have hle : (Finset.univ.filter (fun x ↦ rel x i₀)).card <
          (Finset.univ.filter (fun x ↦ rel x i₁)).card := by
        have hsub : Finset.univ.filter (fun x ↦ rel x i₀) ⊂
            Finset.univ.filter (fun x ↦ rel x i₁) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel₀⟩, ?_⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rintro ⟨hii, _⟩
            exact hii rfl
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact htrans hx hrel₀
        exact Finset.card_lt_card hsub
      exact ⟨i₀, htrans hrel₀ hrel₁, by omega⟩
  obtain ⟨i, _, hcard⟩ := hstep (n + 1) ⟨0, hn⟩
  have hmax : (Finset.univ.filter (fun x ↦ rel x ⟨0, hn⟩)).card ≤ n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  omega

@[simp]
theorem satisfiable_orderingPrinciple_iff {n : ℕ} :
    (orderingPrinciple n).Satisfiable ↔ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨fun v ↦ Fin.elim0 v.row, rfl⟩⟩
  · exact ⟨fun h ↦ False.elim (not_satisfiable_orderingPrinciple hn h), fun h ↦ by omega⟩

end OrderingFormula

section TreeLikeLowerBound

private def chainAssign {n : ℕ} (L : List (Fin n)) (v : OrderingVar n) : Option Bool :=
  if v.row ∈ L ∧ v.col ∈ L then some (decide (L.idxOf v.row < L.idxOf v.col)) else none

private theorem chainAssign_eq_none_iff {n : ℕ} {L : List (Fin n)} {v : OrderingVar n} :
    chainAssign L v = none ↔ ¬ (v.row ∈ L ∧ v.col ∈ L) := by
  simp [chainAssign]

private theorem chainAssign_of_mem {n : ℕ} {L : List (Fin n)} {v : OrderingVar n}
    (hr : v.row ∈ L) (hc : v.col ∈ L) :
    chainAssign L v = some (decide (L.idxOf v.row < L.idxOf v.col)) := by
  simp [chainAssign, hr, hc]

private theorem idxOf_lt_idxOf_cons {α : Type*} [BEq α] [LawfulBEq α] {x a b : α} {L : List α}
    (ha : a ≠ x) (hb : b ≠ x) :
    (x :: L).idxOf a < (x :: L).idxOf b ↔ L.idxOf a < L.idxOf b := by
  rw [List.idxOf_cons_ne L ha.symm, List.idxOf_cons_ne L hb.symm]
  omega

private theorem idxOf_lt_idxOf_append {α : Type*} [BEq α] [LawfulBEq α] {a b : α}
    {L R : List α} (ha : a ∈ L) (hb : b ∈ L) :
    (L ++ R).idxOf a < (L ++ R).idxOf b ↔ L.idxOf a < L.idxOf b := by
  rw [List.idxOf_append_of_mem ha, List.idxOf_append_of_mem hb]

private theorem extends_chainAssign_cons {n : ℕ} {L : List (Fin n)} {x : Fin n} (hx : x ∉ L) :
    PartialAssignExtends (chainAssign L) (chainAssign (x :: L)) := by
  intro v b hv
  by_cases hmem : v.row ∈ L ∧ v.col ∈ L
  · rw [chainAssign_of_mem hmem.1 hmem.2, Option.some.injEq] at hv
    have hr : v.row ≠ x := fun h ↦ hx (h ▸ hmem.1)
    have hc : v.col ≠ x := fun h ↦ hx (h ▸ hmem.2)
    rw [chainAssign_of_mem (List.mem_cons_of_mem x hmem.1) (List.mem_cons_of_mem x hmem.2),
      Option.some.injEq, ← hv]
    simp [idxOf_lt_idxOf_cons hr hc]
  · simp [chainAssign, hmem] at hv

private theorem extends_chainAssign_append {n : ℕ} {L R : List (Fin n)} :
    PartialAssignExtends (chainAssign L) (chainAssign (L ++ R)) := by
  intro v b hv
  by_cases hmem : v.row ∈ L ∧ v.col ∈ L
  · rw [chainAssign_of_mem hmem.1 hmem.2, Option.some.injEq] at hv
    rw [chainAssign_of_mem (List.mem_append_left R hmem.1) (List.mem_append_left R hmem.2),
      Option.some.injEq, ← hv]
    simp [idxOf_lt_idxOf_append hmem.1 hmem.2]
  · simp [chainAssign, hmem] at hv

private theorem chainAssign_no_falsify {n : ℕ} (hn : 2 ≤ n) {L : List (Fin n)}
    (hnd : L.Nodup) (hlen : L.length ≤ n - 1) :
    ∀ c ∈ orderingPrinciple n, ¬ Clause.FalsifiedBy (chainAssign L) c := by
  intro c hc hfals
  rcases mem_orderingPrinciple.mp hc with hA | hB | hD
  · obtain ⟨i, j, k, hij, hjk, hik, rfl⟩ := mem_transitivityCNF.mp hA
    have h₁ := hfals (⟨i, j, hij⟩, false) (by simp [transitivityClause])
    have h₂ := hfals (⟨j, k, hjk⟩, false) (by simp [transitivityClause])
    have h₃ := hfals (⟨i, k, hik⟩, true) (by simp [transitivityClause])
    by_cases hijL : i ∈ L ∧ j ∈ L
    · by_cases hjkL : j ∈ L ∧ k ∈ L
      · rw [chainAssign_of_mem hijL.1 hijL.2] at h₁
        rw [chainAssign_of_mem hjkL.1 hjkL.2] at h₂
        rw [chainAssign_of_mem hijL.1 hjkL.2] at h₃
        simp only [Bool.not_false, Bool.not_true, Option.some.injEq, decide_eq_true_eq,
          decide_eq_false_iff_not] at h₁ h₂ h₃
        exact h₃ (Nat.lt_trans h₁ h₂)
      · simp [chainAssign, hjkL] at h₂
    · simp [chainAssign, hijL] at h₁
  · obtain ⟨i, j, hij, rfl⟩ := mem_antisymmetryCNF.mp hB
    have h₁ := hfals (⟨i, j, hij⟩, false) (by simp [antisymmetryClause])
    have h₂ := hfals (⟨j, i, hij.symm⟩, false) (by simp [antisymmetryClause])
    by_cases hijL : i ∈ L ∧ j ∈ L
    · rw [chainAssign_of_mem hijL.1 hijL.2] at h₁
      rw [chainAssign_of_mem hijL.2 hijL.1] at h₂
      simp only [Bool.not_false, Option.some.injEq, decide_eq_true_eq] at h₁ h₂
      omega
    · simp [chainAssign, hijL] at h₁
  · obtain ⟨j, rfl⟩ := mem_nonMinimalityCNF.mp hD
    have hex : ∃ u : Fin n, u ∉ L := by
      by_contra! hall
      have hcard : n ≤ L.length := by
        have hsub : Finset.univ ⊆ L.toFinset := fun u _ ↦ List.mem_toFinset.mpr (hall u)
        have := Finset.card_le_card hsub
        rwa [Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hnd] at this
      omega
    obtain ⟨u, hu⟩ := hex
    by_cases huj : u = j
    · subst huj
      obtain ⟨i, hij⟩ : ∃ i : Fin n, i ≠ u := by
        by_cases h0 : (⟨0, by omega⟩ : Fin n) = u
        · refine ⟨⟨1, by omega⟩, fun h1 ↦ ?_⟩
          have : (0 : ℕ) = 1 := congrArg Fin.val (h0.trans h1.symm)
          omega
        · exact ⟨⟨0, by omega⟩, h0⟩
      have hf := hfals (⟨i, u, hij⟩, true) (mem_nonMinimalityClause.mpr ⟨rfl, rfl⟩)
      simp [chainAssign, hu] at hf
    · have hf := hfals (⟨u, j, huj⟩, true) (mem_nonMinimalityClause.mpr ⟨rfl, rfl⟩)
      simp [chainAssign, hu] at hf

private theorem chainAssign_split {n : ℕ} :
    ∀ (L : List (Fin n)), L.Nodup ∧ L.length ≤ n - 1 →
      ∀ v : OrderingVar n, chainAssign L v = none → 0 < (n - 1 - L.length) / 2 →
      ∃ L₀ L₁ : List (Fin n),
        (L₀.Nodup ∧ L₀.length ≤ n - 1) ∧
        (L₁.Nodup ∧ L₁.length ≤ n - 1) ∧
        PartialAssignExtends (chainAssign L) (chainAssign L₀) ∧
        PartialAssignExtends (chainAssign L) (chainAssign L₁) ∧
        chainAssign L₀ v = some false ∧
        chainAssign L₁ v = some true ∧
        (n - 1 - L.length) / 2 - 1 ≤ (n - 1 - L₀.length) / 2 ∧
        (n - 1 - L.length) / 2 - 1 ≤ (n - 1 - L₁.length) / 2 := by
  rintro L ⟨hnd, hlen⟩ v hnone hpos
  have hroom : L.length + 2 ≤ n - 1 := by omega
  have hnotboth := chainAssign_eq_none_iff.mp hnone
  by_cases hr : v.row ∈ L
  · have hc : v.col ∉ L := fun hc ↦ hnotboth ⟨hr, hc⟩
    refine ⟨v.col :: L, L ++ [v.col], ?_, ?_,
      extends_chainAssign_cons hc, extends_chainAssign_append, ?_, ?_, ?_, ?_⟩
    · exact ⟨List.nodup_cons.mpr ⟨hc, hnd⟩, by simp; omega⟩
    · exact ⟨hnd.append (List.nodup_singleton _) (by simp [hc]), by simp; omega⟩
    · have hne : v.row ≠ v.col := v.row_ne_col
      rw [chainAssign_of_mem (List.mem_cons_of_mem _ hr) List.mem_cons_self]
      simp [List.idxOf_cons_self, List.idxOf_cons_ne L hne.symm]
    · rw [chainAssign_of_mem (List.mem_append_left _ hr) (by simp)]
      rw [List.idxOf_append_of_mem hr, List.idxOf_append_of_notMem hc, List.idxOf_cons_self]
      simp [List.idxOf_lt_length_iff.mpr hr]
    · simp; omega
    · simp; omega
  · by_cases hc : v.col ∈ L
    · refine ⟨L ++ [v.row], v.row :: L, ?_, ?_,
        extends_chainAssign_append, extends_chainAssign_cons hr, ?_, ?_, ?_, ?_⟩
      · exact ⟨hnd.append (List.nodup_singleton _) (by simp [hr]), by simp; omega⟩
      · exact ⟨List.nodup_cons.mpr ⟨hr, hnd⟩, by simp; omega⟩
      · rw [chainAssign_of_mem (by simp) (List.mem_append_left _ hc)]
        rw [List.idxOf_append_of_notMem hr, List.idxOf_append_of_mem hc, List.idxOf_cons_self]
        have hlt := List.idxOf_lt_length_iff.mpr hc
        simp; omega
      · have hne : v.col ≠ v.row := v.row_ne_col.symm
        rw [chainAssign_of_mem List.mem_cons_self (List.mem_cons_of_mem _ hc)]
        simp [List.idxOf_cons_self, List.idxOf_cons_ne L hne.symm]
      · simp; omega
      · simp; omega
    · have hne : v.row ≠ v.col := v.row_ne_col
      have hnd₀ : (L ++ [v.col, v.row]).Nodup := by
        refine hnd.append (by simp [hne.symm]) fun x hxL hxR ↦ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
        rcases hxR with rfl | rfl <;> [exact hc hxL; exact hr hxL]
      have hnd₁ : (L ++ [v.row, v.col]).Nodup := by
        refine hnd.append (by simp [hne]) fun x hxL hxR ↦ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR
        rcases hxR with rfl | rfl <;> [exact hr hxL; exact hc hxL]
      refine ⟨L ++ [v.col, v.row], L ++ [v.row, v.col],
        ⟨hnd₀, by simp; omega⟩, ⟨hnd₁, by simp; omega⟩,
        extends_chainAssign_append, extends_chainAssign_append, ?_, ?_, ?_, ?_⟩
      · rw [chainAssign_of_mem (by simp) (by simp)]
        rw [List.idxOf_append_of_notMem hr, List.idxOf_append_of_notMem hc,
          List.idxOf_cons_self, List.idxOf_cons_ne _ hne.symm, List.idxOf_cons_self]
        simp
      · rw [chainAssign_of_mem (by simp) (by simp)]
        rw [List.idxOf_append_of_notMem hr, List.idxOf_append_of_notMem hc,
          List.idxOf_cons_self, List.idxOf_cons_ne _ hne, List.idxOf_cons_self]
        simp
      · simp; omega
      · simp; omega

/-- **Exponential Tree-Like Resolution Leaf Lower Bound for `OP_n`**. -/
theorem two_pow_le_leafCount_orderingPrinciple {n : ℕ} (hn : 2 ≤ n)
    (d : (orderingPrinciple n).Derivation []) :
    2 ^ ((n - 1) / 2) ≤ d.toDecisionTree.leafCount := by
  have h := pow_pot_le_leafCount_of_state_delayer (orderingPrinciple n)
    (S := List (Fin n)) chainAssign (fun L ↦ (n - 1 - L.length) / 2)
    (fun L ↦ L.Nodup ∧ L.length ≤ n - 1)
    (fun _ hL ↦ chainAssign_no_falsify hn hL.1 hL.2)
    chainAssign_split d (s := []) ⟨List.nodup_nil, Nat.zero_le _⟩ (Clause.falsifiedBy_nil _)
  simpa using h

/-- **Exponential Tree-Like Resolution Size Lower Bound for `OP_n`**. -/
theorem two_pow_le_size_orderingPrinciple {n : ℕ} (hn : 2 ≤ n)
    (d : (orderingPrinciple n).Derivation []) :
    2 ^ ((n - 1) / 2) ≤ d.size :=
  (two_pow_le_leafCount_orderingPrinciple hn d).trans d.leafCount_toDecisionTree_le_size

/-- **Relabeled Ordering Principle Tree-Like Resolution Lower Bound**. -/
theorem two_pow_le_leafCount_relabel_orderingPrinciple {n : ℕ} {W : Type*} [DecidableEq W]
    (hn : 2 ≤ n) {f : OrderingVar n → W} (hf : Function.Injective f)
    (d : ((orderingPrinciple n).relabel f).Derivation []) :
    2 ^ ((n - 1) / 2) ≤ d.toDecisionTree.leafCount := by
  obtain ⟨d', hs⟩ := CNF.Derivation.exists_size_eq_of_relabel hf d
  have h₁ := d.two_mul_leafCount_toDecisionTree
  have h₂ := d'.two_mul_leafCount_toDecisionTree
  have hle := two_pow_le_leafCount_orderingPrinciple hn d'
  omega

/-- **Relabeled Ordering Principle DPLL Search-Tree Lower Bound**. -/
theorem two_pow_le_dpll_leafCount_relabel_orderingPrinciple {n : ℕ} {W : Type*}
    (hn : 2 ≤ n) {f : OrderingVar n → W} (hf : Function.Injective f)
    {t : Cslib.DecisionTree W (Clause W)}
    (ht : t.FindsFalsifiedClause ((orderingPrinciple n).relabel f)) :
    2 ^ ((n - 1) / 2) ≤ t.leafCount := by
  classical
  obtain ⟨d, hd⟩ := ht.exists_derivation_leafCount_le
  exact (two_pow_le_leafCount_relabel_orderingPrinciple hn hf d).trans hd

/-- **DPLL Trail Search-Tree Exponential Lower Bound on `OP_n`**: for `n ≥ 2` and any injective
variable numbering `f : OrderingVar n → ℕ`, `Cslib.Algorithms.Lean.DPLL.searchTree` explores at
least `2 ^ ((n - 1) / 2)` leaves on `(orderingPrinciple n).relabel f`. -/
theorem two_pow_le_leafCount_searchTree_orderingPrinciple {n : ℕ} (hn : 2 ≤ n)
    {f : OrderingVar n → ℕ} (hf : Function.Injective f) :
    2 ^ ((n - 1) / 2) ≤
      (Cslib.Algorithms.Lean.DPLL.searchTree ((orderingPrinciple n).relabel f)
        (Cslib.Algorithms.Lean.DPLL.depth ((orderingPrinciple n).relabel f)) []).leafCount :=
  two_pow_le_dpll_leafCount_relabel_orderingPrinciple hn hf
    (Cslib.Algorithms.Lean.DPLL.findsFalsifiedClause_searchTree
      (by
        rw [CNF.satisfiable_relabel hf]
        exact not_satisfiable_orderingPrinciple (by omega)))

end TreeLikeLowerBound

end CslibFrontier.Logics.Propositional
