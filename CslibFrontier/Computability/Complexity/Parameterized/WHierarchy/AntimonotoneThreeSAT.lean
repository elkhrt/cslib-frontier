/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.WeftCertificate
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# `WA3NS` (Weighted Antimonotone 3-Normalized Satisfiability) is `W[3]`-Complete

An *antimonotone `3`-normalized* Boolean formula (`WA3NSFormula`) is a conjunction of subformulas in
disjunctive normal form (DNF) whose literals are all negative (`¬x_v`). Identifying a truth
assignment with the finite set `A ⊆ var(F)` of variables assigned `true`, `A` satisfies `F` when
every DNF in `F` contains at least one conjunctive clause disjoint from `A`. The *Weighted
Antimonotone `3`-Normalized Satisfiability* problem (`WA3NS`) asks whether `F` admits a satisfying
assignment `A ⊆ var(F)` of exact Hamming weight `|A| = k`, parameterized by `k`.

This module establishes the `W[3]` case of the Downey–Fellows Antimonotone Collapse Theorem on
multi-tape Turing machines:
1. `WA3NS` FPT-reduces to `WCS 3 4` via a 4-layer unbounded fan-in circuit (input negations, inner
   conjunctions, DNF disjunctions, and outer conjunction) of weft at most `3` and depth at most `4`,
   placing `WA3NS` in `W[3]`.
2. For every fixed depth `d`, `WCS 3 d` FPT-reduces to `WA3NS` by encoding single-selection across
   `1 + K` blocks via intra-block pairwise negative clauses `(¬y_u ∨ ¬y_w)` combined with total
   weight `1 + K`, enforcing bracket consistency via `(¬y_P ∨ ¬y_Q)`, and translating weft-`3`
   certificate checks through two levels of certificate/refutation duality into purely negative
   DNFs `(¬y_{cl₃}) ∨ ⋁_{e₁, cl₁} (⋀_{P : refutes(cl₁, P)} ¬y_P)`.

All results are proved unconditionally under standard Lean axioms.

## Main definitions

- `CslibFrontier.ParameterizedComplexity.WA3NSFormula`, `WA3NSInstance`, `WA3NS`: antimonotone
  `3`-normalized formulas and weighted satisfiability.
- `CslibFrontier.ParameterizedComplexity.AntimonotoneCNFFormula`, `toWA3NSFormula`: antimonotone CNF
  formulas and their canonical embedding into `WA3NSFormula`.

## Main results

- `CslibFrontier.ParameterizedComplexity.WA3NSFormula.Satisfies.anti_mono`: downward closure.
- `CslibFrontier.ParameterizedComplexity.WA3NS_mem_W`: `WA3NS ∈ W[3]`.
- `CslibFrontier.ParameterizedComplexity.fptReducible_WCS_WA3NS`: `WCS 3 d ≤_FPT WA3NS` for fixed
  `d`.
- `CslibFrontier.ParameterizedComplexity.WA3NS_wHard` & `W_three_eq_FPT_iff`: `W[3]`-completeness.

## Tags

parameterized complexity, W[3]-completeness, antimonotone collapse, 3-normalized formula, DNF
-/

public section

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.Unbounded
open Cslib.Complexity Cslib.Complexity.WCS.ToClique Turing.MultiTapeTM

namespace CslibFrontier.ParameterizedComplexity

private theorem mem_zipIdx_iff {α : Type*} {l : List α} {a : α} {i : ℕ} :
    (a, i) ∈ l.zipIdx ↔ ∃ h : i < l.length, l[i] = a := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zipIdx, List.getElem_zipIdx, zero_add, Prod.mk.injEq]
  exact ⟨fun ⟨j, hj, h1, h2⟩ => ⟨h2 ▸ hj, h2 ▸ h1⟩, fun ⟨hi, h1⟩ => ⟨i, hi, h1, rfl⟩⟩

/-! ### Antimonotone `3`-normalized and CNF formulas -/

/-- Antimonotone `3`-normalized Boolean formula: a non-empty variable set `headVar :: tailVars` and
a conjunction `dnfs` of antimonotone DNF subformulas, where each DNF is a list of conjunctive
clauses and each conjunctive clause is a list of negated variables `v` (`¬x_v`). -/
@[ext]
structure WA3NSFormula where
  /-- Base variable identifier ensuring `varSet` is non-empty. -/
  headVar : ℕ
  /-- Additional declared variable identifiers. -/
  tailVars : List ℕ
  /-- Conjunction of antimonotone DNFs (`⋀_r ⋁_j ⋀_{v ∈ M_{r,j}} ¬x_v`). -/
  dnfs : List (List (List ℕ))
  deriving DecidableEq

/-- Canonical binary encoding of `WA3NSFormula`. -/
enc_structure encWA3NSFormula : WA3NSFormula where
  headVar : encNat, tailVars : (encList encNat),
  dnfs : (encList (encList (encList encNat)))

namespace WA3NSFormula

/-- Deduplicated non-empty list of declared variables of `F`. -/
@[expose] def distinctVars (F : WA3NSFormula) : List ℕ :=
  selectDistinct (F.headVar :: F.tailVars) (List.replicate (F.tailVars.length + 1) true)

/-- Finite variable set `var(F)`. -/
@[expose] def varSet (F : WA3NSFormula) : Finset ℕ :=
  F.distinctVars.toFinset

/-- `distinctVars` has no duplicates. -/
theorem nodup_distinctVars (F : WA3NSFormula) : F.distinctVars.Nodup :=
  nodup_selectDistinct _ _

/-- Membership in `distinctVars`. -/
theorem mem_distinctVars {F : WA3NSFormula} {v : ℕ} :
    v ∈ F.distinctVars ↔ v = F.headVar ∨ v ∈ F.tailVars := by
  unfold distinctVars
  have hlen : (F.headVar :: F.tailVars).length = F.tailVars.length + 1 := rfl
  rw [← hlen, mem_selectDistinct_replicate, List.mem_cons]

/-- Membership in `varSet`. -/
theorem mem_varSet {F : WA3NSFormula} {v : ℕ} :
    v ∈ F.varSet ↔ v ∈ F.distinctVars :=
  List.mem_toFinset

/-- `F.headVar` belongs to `F.varSet`. -/
theorem headVar_mem_varSet (F : WA3NSFormula) : F.headVar ∈ F.varSet :=
  mem_varSet.2 (mem_distinctVars.2 (Or.inl rfl))

/-- `F.varSet` is always non-empty. -/
theorem varSet_nonempty (F : WA3NSFormula) : F.varSet.Nonempty :=
  ⟨F.headVar, F.headVar_mem_varSet⟩

/-- DNF subformulas of `F` with conjunctive-clause variables restricted to `F.distinctVars`. -/
@[expose] def cleanDNFs (F : WA3NSFormula) : List (List (List ℕ)) :=
  F.dnfs.map fun D => D.map fun M => M.filter (· ∈ F.distinctVars)

/-- When all variables in `F.dnfs` belong to `F.distinctVars`, `F.cleanDNFs = F.dnfs`. -/
theorem cleanDNFs_eq_dnfs {F : WA3NSFormula}
    (h : ∀ D ∈ F.dnfs, ∀ M ∈ D, ∀ v ∈ M, v ∈ F.distinctVars) :
    F.cleanDNFs = F.dnfs := by
  rw [cleanDNFs]
  conv_rhs => rw [← List.map_id F.dnfs]
  refine List.map_congr_left fun D hD => ?_
  conv_rhs => rw [id, ← List.map_id D]
  exact List.map_congr_left fun M hM =>
    List.filter_eq_self.2 fun v hv => decide_eq_true (h D hD M hM v hv)

/-- Assignment `A : Finset ℕ` (the set of `true` variables) satisfies `F` when `A ⊆ var(F)` and
every DNF in `F.cleanDNFs` has at least one conjunctive clause disjoint from `A`. -/
@[expose] def Satisfies (F : WA3NSFormula) (A : Finset ℕ) : Prop :=
  A ⊆ F.varSet ∧ ∀ D ∈ F.cleanDNFs, ∃ M ∈ D, ∀ v ∈ M, v ∉ A

/-- Characterization of `F.Satisfies A`. -/
theorem satisfies_iff {F : WA3NSFormula} {A : Finset ℕ} :
    F.Satisfies A ↔ A ⊆ F.varSet ∧ ∀ D ∈ F.cleanDNFs, ∃ M ∈ D, ∀ v ∈ M, v ∉ A :=
  Iff.rfl

/-- Computable Boolean indicator `f_F(A)` deciding `F.Satisfies A` for `A ⊆ F.varSet`. -/
@[expose] def indicator (F : WA3NSFormula) (A : Finset ℕ) : Bool :=
  decide (A ⊆ F.varSet) && F.cleanDNFs.all fun D => D.any fun M => M.all fun v => decide (v ∉ A)

/-- `F.indicator A = true` iff `F.Satisfies A`. -/
theorem indicator_eq_true_iff (F : WA3NSFormula) (A : Finset ℕ) :
    F.indicator A = true ↔ F.Satisfies A := by
  simp [indicator, Satisfies, List.all_eq_true, List.any_eq_true]

/-- `A` is an inclusion-maximal satisfying assignment of `F`. -/
@[expose] def IsMaximalSatisfying (F : WA3NSFormula) (A : Finset ℕ) : Prop :=
  Maximal F.Satisfies A

/-- Characterization of `F.IsMaximalSatisfying A`. -/
theorem isMaximalSatisfying_iff {F : WA3NSFormula} {A : Finset ℕ} :
    F.IsMaximalSatisfying A ↔ Maximal F.Satisfies A :=
  Iff.rfl

/-- Satisfying assignments of an antimonotone formula are downward-closed under `⊆`. -/
theorem Satisfies.anti_mono {F : WA3NSFormula} {A A' : Finset ℕ}
    (hA : F.Satisfies A) (hsub : A' ⊆ A) : F.Satisfies A' :=
  ⟨hsub.trans hA.1, fun D hD =>
    let ⟨M, hM, hdisj⟩ := hA.2 D hD
    ⟨M, hM, fun v hv hmem => hdisj v hv (hsub hmem)⟩⟩

/-- Polynomial-time computability of `distinctVars`. -/
@[fun_prop]
theorem computableInPolyTime_distinctVars :
    ComputableInPolyTime distinctVars encWA3NSFormula (encList encNat) := by
  open scoped WA3NSFormula in
  unfold distinctVars
  fun_prop

/-- Polynomial-time computability of `cleanDNFs`. -/
@[fun_prop]
theorem computableInPolyTime_cleanDNFs :
    ComputableInPolyTime cleanDNFs encWA3NSFormula (encList (encList (encList encNat))) := by
  open scoped WA3NSFormula in
  unfold cleanDNFs
  fun_prop

end WA3NSFormula

/-- Parameterized `WA3NS` instance `(formula, k)`. -/
@[ext]
structure WA3NSInstance where
  /-- Input antimonotone `3`-normalized formula. -/
  formula : WA3NSFormula
  /-- Target Hamming weight (and parameter). -/
  k : ℕ
  deriving DecidableEq

/-- Canonical binary encoding of `WA3NSInstance`. -/
enc_structure encWA3NSInstance : WA3NSInstance where
  formula : encWA3NSFormula, k : encNat

/-- **Weighted Antimonotone `3`-Normalized Satisfiability (`WA3NS`)**: instances `(F, k)` admitting
a satisfying assignment `A ⊆ var(F)` of exact Hamming weight `|A| = k`. -/
@[expose] def WA3NS : Set WA3NSInstance :=
  {x | ∃ A : Finset ℕ, x.formula.Satisfies A ∧ A.card = x.k}

/-- Membership in `WA3NS`. -/
theorem mem_WA3NS {x : WA3NSInstance} :
    x ∈ WA3NS ↔ ∃ A : Finset ℕ, x.formula.Satisfies A ∧ A.card = x.k :=
  Iff.rfl

/-- By downward closure of antimonotone formulas, `WA3NS` is equivalent to asking for a satisfying
assignment of Hamming weight *at least* `k`. -/
theorem mem_WA3NS_iff_card_ge {x : WA3NSInstance} :
    x ∈ WA3NS ↔ ∃ A : Finset ℕ, x.formula.Satisfies A ∧ x.k ≤ A.card := by
  refine ⟨fun ⟨A, hA, hcard⟩ => ⟨A, hA, hcard.ge⟩, fun ⟨A, hA, hge⟩ => ?_⟩
  obtain ⟨A', hA'sub, hcard'⟩ := Finset.exists_subset_card_eq hge
  exact ⟨A', hA.anti_mono hA'sub, hcard'⟩

/-- Antimonotone CNF formula: a non-empty variable set `headVar :: tailVars` and a conjunction of
disjunctive clauses of negative literals (`⋀_i ⋁_{v ∈ C_i} ¬x_v`). -/
@[ext]
structure AntimonotoneCNFFormula where
  /-- Base variable identifier ensuring `varSet` is non-empty. -/
  headVar : ℕ
  /-- Additional declared variable identifiers. -/
  tailVars : List ℕ
  /-- Conjunctive list of disjunctive negative-literal clauses. -/
  clauses : List (List ℕ)
  deriving DecidableEq

/-- Canonical binary encoding of `AntimonotoneCNFFormula`. -/
enc_structure encAntimonotoneCNFFormula : AntimonotoneCNFFormula where
  headVar : encNat, tailVars : (encList encNat), clauses : (encList (encList encNat))

namespace AntimonotoneCNFFormula

/-- Deduplicated non-empty list of declared variables of `F`. -/
@[expose] def distinctVars (F : AntimonotoneCNFFormula) : List ℕ :=
  selectDistinct (F.headVar :: F.tailVars) (List.replicate (F.tailVars.length + 1) true)

/-- Finite variable set `var(F)`. -/
@[expose] def varSet (F : AntimonotoneCNFFormula) : Finset ℕ :=
  F.distinctVars.toFinset

/-- Membership in `F.varSet`. -/
theorem mem_varSet {F : AntimonotoneCNFFormula} {v : ℕ} :
    v ∈ F.varSet ↔ v ∈ F.distinctVars :=
  List.mem_toFinset

/-- Clauses restricted to declared variables in `F.distinctVars`. -/
@[expose] def cleanClauses (F : AntimonotoneCNFFormula) : List (List ℕ) :=
  F.clauses.map fun C => C.filter (· ∈ F.distinctVars)

/-- Membership in `F.cleanClauses`. -/
theorem mem_cleanClauses_iff {F : AntimonotoneCNFFormula} {C : List ℕ} :
    C ∈ F.cleanClauses ↔ ∃ r ∈ F.clauses, r.filter (· ∈ F.distinctVars) = C :=
  List.mem_map

/-- When all variables in `F.clauses` belong to `F.distinctVars`, `F.cleanClauses = F.clauses`. -/
theorem cleanClauses_eq_clauses {F : AntimonotoneCNFFormula}
    (h : ∀ C ∈ F.clauses, ∀ v ∈ C, v ∈ F.distinctVars) :
    F.cleanClauses = F.clauses := by
  rw [cleanClauses]; conv_rhs => rw [← List.map_id F.clauses]
  exact List.map_congr_left fun C hC =>
    List.filter_eq_self.2 fun v hv => decide_eq_true (h C hC v hv)

/-- Assignment `A : Finset ℕ` satisfies the antimonotone CNF `F` when `A ⊆ var(F)` and every clause
contains at least one variable outside `A`. -/
@[expose] def Satisfies (F : AntimonotoneCNFFormula) (A : Finset ℕ) : Prop :=
  A ⊆ F.varSet ∧ ∀ C ∈ F.cleanClauses, ∃ v ∈ C, v ∉ A

/-- Characterization of `F.Satisfies A`. -/
theorem satisfies_iff {F : AntimonotoneCNFFormula} {A : Finset ℕ} :
    F.Satisfies A ↔ A ⊆ F.varSet ∧ ∀ C ∈ F.cleanClauses, ∃ v ∈ C, v ∉ A :=
  Iff.rfl

/-- `A` is an inclusion-maximal satisfying assignment of `F`. -/
@[expose] def IsMaximalSatisfying (F : AntimonotoneCNFFormula) (A : Finset ℕ) : Prop :=
  Maximal F.Satisfies A

/-- Characterization of `F.IsMaximalSatisfying A`. -/
theorem isMaximalSatisfying_iff {F : AntimonotoneCNFFormula} {A : Finset ℕ} :
    F.IsMaximalSatisfying A ↔ Maximal F.Satisfies A :=
  Iff.rfl

/-- Polynomial-time computability of `distinctVars`. -/
@[fun_prop]
theorem computableInPolyTime_distinctVars :
    ComputableInPolyTime distinctVars encAntimonotoneCNFFormula (encList encNat) := by
  open scoped AntimonotoneCNFFormula in
  unfold distinctVars
  fun_prop

/-- Polynomial-time computability of `cleanClauses`. -/
@[fun_prop]
theorem computableInPolyTime_cleanClauses :
    ComputableInPolyTime cleanClauses encAntimonotoneCNFFormula (encList (encList encNat)) := by
  open scoped AntimonotoneCNFFormula in
  unfold cleanClauses
  fun_prop

/-- Canonical embedding of an antimonotone CNF formula into an antimonotone `3`-normalized formula
by viewing each declared negative literal `¬x_v` as a unary conjunctive clause `[v]`. -/
@[expose] def toWA3NSFormula (F : AntimonotoneCNFFormula) : WA3NSFormula where
  headVar := F.headVar
  tailVars := F.tailVars
  dnfs := F.cleanClauses.map fun C => C.map fun v => [v]

/-- Embedding an antimonotone CNF into `WA3NSFormula` preserves variable sets. -/
theorem toWA3NSFormula_varSet (F : AntimonotoneCNFFormula) :
    F.toWA3NSFormula.varSet = F.varSet := by rfl

/-- Embedding an antimonotone CNF into `WA3NSFormula` preserves satisfying assignments. -/
theorem satisfies_toWA3NSFormula_iff (F : AntimonotoneCNFFormula) (A : Finset ℕ) :
    F.toWA3NSFormula.Satisfies A ↔ F.Satisfies A := by
  have hd : F.toWA3NSFormula.distinctVars = F.distinctVars := rfl
  have hclean : F.toWA3NSFormula.cleanDNFs = F.toWA3NSFormula.dnfs :=
    WA3NSFormula.cleanDNFs_eq_dnfs fun D hD M hM v hv => by
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hM
      rw [List.mem_singleton.1 hv, hd]
      obtain ⟨_, -, rfl⟩ := mem_cleanClauses_iff.1 hC
      exact of_decide_eq_true (List.mem_filter.1 hu).2
  rw [WA3NSFormula.satisfies_iff, satisfies_iff, toWA3NSFormula_varSet, hclean]
  refine and_congr_right fun _ => ⟨fun h C hC => ?_, fun h D hD => ?_⟩
  · obtain ⟨M, hM, hdisj⟩ := h (C.map ([·])) (List.mem_map.2 ⟨C, hC, rfl⟩)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hM
    exact ⟨v, hv, hdisj v (List.mem_singleton_self v)⟩
  · obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
    obtain ⟨v, hv, hvA⟩ := h C hC
    exact ⟨[v], List.mem_map.2 ⟨v, hv, rfl⟩, fun u hu => List.mem_singleton.1 hu ▸ hvA⟩

/-- Embedding an antimonotone CNF into `WA3NSFormula` preserves maximal satisfying assignments. -/
theorem isMaximalSatisfying_toWA3NSFormula_iff (F : AntimonotoneCNFFormula) (A : Finset ℕ) :
    F.toWA3NSFormula.IsMaximalSatisfying A ↔ F.IsMaximalSatisfying A := by
  simp only [WA3NSFormula.IsMaximalSatisfying, IsMaximalSatisfying, Maximal,
    satisfies_toWA3NSFormula_iff]

/-- `toWA3NSFormula` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toWA3NSFormula :
    ComputableInPolyTime toWA3NSFormula encAntimonotoneCNFFormula encWA3NSFormula := by
  open scoped AntimonotoneCNFFormula WA3NSFormula in
  unfold toWA3NSFormula
  fun_prop

end AntimonotoneCNFFormula

/-! ### `WA3NS ∈ W[3]` (`WA3NS ≤_FPT WCS 3 4`) -/

namespace WA3NSToCircuit

/-- Conjunctive clauses of `F` paired with their DNF index `r < F.cleanDNFs.length` and translated
to negated-input wire lists in `[n, 2 * n)`. -/
def indexedClauses (F : WA3NSFormula) : List (ℕ × List ℕ) :=
  let V := F.distinctVars
  let n := V.length
  F.cleanDNFs.zipIdx.flatMap fun p =>
    p.1.map fun M => (p.2, M.map fun v => n + V.idxOf v)

/-- Wire indices in gate stage 2 belonging to the `r`-th DNF of `F`. -/
def dnfWires (n : ℕ) (IC : List (ℕ × List ℕ)) (r : ℕ) : List ℕ :=
  (IC.zipIdx.filter fun q => decide (q.1.1 = r)).map fun q => n + n + q.2

/-- 4-layer gate list for `WA3NSFormula`: input negations, conjunctive clauses, DNF disjunctions,
and top-level conjunction. -/
def circuitGates (n numDNFs : ℕ) (IC : List (ℕ × List ℕ)) : List (Op × List ℕ) :=
  let m := IC.length
  (List.range n).map (fun i => (.not, [i])) ++
    IC.map (fun p => (.and p.2.length, p.2)) ++
    (List.range numDNFs).map (fun r =>
      let W := dnfWires n IC r
      (.or W.length, W)) ++
    [(.and numDNFs, (List.range numDNFs).map (n + n + m + ·))]

/-- Circuit code for `F : WA3NSFormula`. -/
def circuitCode (F : WA3NSFormula) : List (Op × List ℕ) × List ℕ :=
  let n := F.distinctVars.length
  let numDNFs := F.cleanDNFs.length
  let IC := indexedClauses F
  (circuitGates n numDNFs IC, [n + n + IC.length + numDNFs])

/-- Every wire in `indexedClauses F` lies strictly below `2 * F.distinctVars.length`. -/
theorem lt_of_mem_indexedClauses {F : WA3NSFormula} {p : ℕ × List ℕ}
    (hp : p ∈ indexedClauses F) {w : ℕ} (hw : w ∈ p.2) :
    w < F.distinctVars.length + F.distinctVars.length := by
  simp only [indexedClauses, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨⟨D, r⟩, hDr, M, hM, rfl⟩ := hp
  obtain ⟨hD_lt, hD_eq⟩ := mem_zipIdx_iff.1 hDr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  have hD_mem : D ∈ F.cleanDNFs := hD_eq ▸ List.getElem_mem hD_lt
  simp only [WA3NSFormula.cleanDNFs, List.mem_map] at hD_mem
  obtain ⟨rawD, -, rfl⟩ := hD_mem
  simp only [List.mem_map] at hM
  obtain ⟨rawM, -, rfl⟩ := hM
  have hvin : v ∈ F.distinctVars := of_decide_eq_true (List.mem_filter.1 hv).2
  have hidx : F.distinctVars.idxOf v < F.distinctVars.length := List.idxOf_lt_length_iff.2 hvin
  omega

/-- Every wire in `dnfWires n IC r` lies strictly below `n + n + IC.length`. -/
theorem lt_of_mem_dnfWires {n : ℕ} {IC : List (ℕ × List ℕ)} {r w : ℕ}
    (hw : w ∈ dnfWires n IC r) : w < n + n + IC.length := by
  obtain ⟨⟨p, j⟩, hfilt, rfl⟩ := List.mem_map.1 hw
  obtain ⟨hj, _⟩ := mem_zipIdx_iff.1 (List.mem_filter.1 hfilt).1
  omega

/-- `circuitGates n numDNFs IC` is a well-formed gate list from `n` inputs. -/
theorem isCodeFrom_circuitGates {n numDNFs : ℕ} {IC : List (ℕ × List ℕ)}
    (hIC : ∀ p ∈ IC, ∀ w ∈ p.2, w < n + n) :
    Program.IsCodeFrom signature n 0 (circuitGates n numDNFs IC) := by
  rw [circuitGates, Program.isCodeFrom_append, Program.isCodeFrom_append, Program.isCodeFrom_append]
  refine ⟨⟨⟨Program.isCodeFrom_of_forall
        (List.forall_mem_map.2 fun i hi => ⟨rfl, fun _ hx => by simp_all⟩),
      Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun p hp => ⟨by simp, fun w hw => ?_⟩)⟩,
      Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun r _ => ⟨by simp, fun w hw => ?_⟩)⟩,
    Program.isCodeFrom_of_forall (List.forall_mem_singleton.2 ⟨by simp,
      List.forall_mem_map.2 fun j hj => ?_⟩)⟩
  · have := hIC p hp w hw; simp only [List.length_map, List.length_range]; omega
  · have := lt_of_mem_dnfWires hw
    simp only [List.length_append, List.length_map, List.length_range]; omega
  · simp only [List.mem_range, List.length_append, List.length_map, List.length_range] at hj ⊢
    omega

/-- `circuitCode F` decodes to a valid 1-output circuit. -/
theorem isSome_ofCode_circuitCode (F : WA3NSFormula) :
    (Circuit.ofCode (σ := signature) F.distinctVars.length 1 (circuitCode F)).isSome = true := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_circuitGates fun p hp w hw => lt_of_mem_indexedClauses hp hw, rfl, ?_⟩
  simp only [circuitCode, circuitGates, List.mem_singleton, forall_eq, List.length_append,
    List.length_map, List.length_range, List.length_singleton]
  omega

/-- The 4-layer circuit of `F : WA3NSFormula`. -/
def toCircuit (F : WA3NSFormula) : Σ n, Circuit signature n 1 :=
  ⟨F.distinctVars.length,
    (Circuit.ofCode (σ := signature) F.distinctVars.length 1 (circuitCode F)).get
      (isSome_ofCode_circuitCode F)⟩

/-- Code of `toCircuit F`. -/
theorem code_toCircuit (F : WA3NSFormula) : (toCircuit F).2.code = circuitCode F :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-- Number of inputs of `toCircuit F`. -/
theorem toCircuit_fst (F : WA3NSFormula) : (toCircuit F).1 = F.distinctVars.length := by rfl

private theorem le_of_mem_evalCode_circuitGates (cost : Op → ℕ) {n numDNFs : ℕ}
    {IC : List (ℕ × List ℕ)} (hIC : ∀ p ∈ IC, ∀ w ∈ p.2, w < n + n) {c₁ c₂ c₃ c₄ : ℕ}
    (h₁ : cost Op.not ≤ c₁)
    (h₂ : ∀ p ∈ IC, cost (Op.and p.2.length) ≤ c₂)
    (h₃ : ∀ r ∈ List.range numDNFs, cost (Op.or (dnfWires n IC r).length) ≤ c₃)
    (h₄ : cost (Op.and numDNFs) ≤ c₄) :
    ∀ v ∈ evalCode (depthInterpretation (σ := signature) cost) 0 (List.replicate n 0)
      (circuitGates n numDNFs IC), v ≤ 0 + c₁ + c₂ + c₃ + c₄ := by
  rw [circuitGates, evalCode_append, evalCode_append, evalCode_append]
  refine le_of_mem_evalCode_depth_layer _ _ _
    (List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_))
    (le_of_mem_evalCode_depth_layer _ _ _
      (List.forall_mem_map.2 fun r _ w hw => ?_)
      (le_of_mem_evalCode_depth_layer _ _ _
        (List.forall_mem_map.2 fun p hp w hw => ?_)
        (le_of_mem_evalCode_depth_layer _ _ _
          (List.forall_mem_map.2 fun j hj _ hi => by simp_all)
          (fun _ hv => (List.eq_of_mem_replicate hv).le)
          (by simp [h₁]))
        (List.forall_mem_map.2 h₂))
      (List.forall_mem_map.2 h₃))
    (by simp [h₄])
  · simp only [List.mem_range, length_evalCode, List.length_replicate,
      List.length_map, List.length_range] at hj ⊢
    omega
  · have := lt_of_mem_dnfWires hw
    simp only [length_evalCode, List.length_replicate, List.length_map, List.length_range]
    omega
  · have := hIC p hp w hw
    simp only [length_evalCode, List.length_replicate, List.length_map, List.length_range]
    omega

/-- `toCircuit F` has weft at most `3`. -/
theorem weft_toCircuit_le (F : WA3NSFormula) : (toCircuit F).2.weft ≤ 3 := by
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  simpa using le_of_mem_evalCode_circuitGates (largeGateCost signature)
    (fun p hp w hw => lt_of_mem_indexedClauses hp hw)
    (c₁ := 0) (c₂ := 1) (c₃ := 1) (c₄ := 1)
    (by decide) (fun _ _ => largeGateCost_le_one _) (fun _ _ => largeGateCost_le_one _)
    (largeGateCost_le_one _) v (code_toCircuit F ▸ hv)

/-- `toCircuit F` has depth at most `4`. -/
theorem depth_toCircuit_le (F : WA3NSFormula) : (toCircuit F).2.depth ≤ 4 := by
  rw [← Circuit.depthWith_one]
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  simpa using le_of_mem_evalCode_circuitGates 1
    (fun p hp w hw => lt_of_mem_indexedClauses hp hw)
    le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl v (code_toCircuit F ▸ hv)

/-- Evaluating `circuitGates` across all 4 layers. -/
theorem evalCode_circuitGates {n numDNFs : ℕ} {IC : List (ℕ × List ℕ)}
    (hIC : ∀ p ∈ IC, ∀ w ∈ p.2, w < n + n) (x : List Bool) (hx : x.length = n) :
    (evalCode interpretation false x (circuitGates n numDNFs IC)).getD
        (n + n + IC.length + numDNFs) false =
      decide (∀ r < numDNFs, ∃ p ∈ IC, p.1 = r ∧
        ∀ w ∈ p.2, (x ++ x.map (!·)).getD w false = true) := by
  subst hx
  rw [circuitGates, evalCode_append, evalCode_append, evalCode_append]
  have h1 : evalCode interpretation false x
      ((List.range x.length).map fun i => (Op.not, [i])) = x ++ x.map (!·) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.length_map, List.length_range] at h₁
      simp [List.getElem?_eq_getElem h₁]
    · exact List.forall_mem_map.2 fun j hj _ hi => by simp_all
  set lits := x ++ x.map (!·)
  have hlits_len : lits.length = x.length + x.length := by simp [lits]
  have h2 : evalCode interpretation false lits
      (IC.map fun p => (Op.and p.2.length, p.2)) =
      lits ++ IC.map fun p => decide (∀ w ∈ p.2, lits.getD w false = true) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun p hp => ?_
      simp only [Function.comp_apply, interpretation_and]
      rw [decide_eq_decide]
      constructor
      · intro ha w hw
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
        simpa [List.getElem?_eq_getElem hi] using ha ⟨i, hi⟩
      · intro hall a
        simpa [List.getElem?_eq_getElem a.isLt] using hall p.2[a.val] (List.getElem_mem a.isLt)
    · refine List.forall_mem_map.2 fun p hp w hw => ?_
      rw [hlits_len]; exact hIC p hp w hw
  set l2 := lits ++ IC.map fun p => decide (∀ w ∈ p.2, lits.getD w false = true)
  have hl2_len : l2.length = x.length + x.length + IC.length := by simp [l2, hlits_len, add_assoc]
  have h3 : evalCode interpretation false l2
      ((List.range numDNFs).map fun r =>
        (Op.or (dnfWires x.length IC r).length, dnfWires x.length IC r)) =
      l2 ++ (List.range numDNFs).map fun r =>
        decide (∃ p ∈ IC, p.1 = r ∧ ∀ w ∈ p.2, lits.getD w false = true) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun r _ => ?_
      simp only [Function.comp_apply, interpretation_or]
      rw [decide_eq_decide]
      constructor
      · rintro ⟨a, ha⟩
        have hw_mem : (dnfWires x.length IC r)[a.val] ∈ dnfWires x.length IC r :=
          List.getElem_mem a.isLt
        have hval : l2.getD (dnfWires x.length IC r)[a.val] false = true := by
          simpa [List.getElem?_eq_getElem a.isLt] using ha
        obtain ⟨⟨p, j⟩, hfilt, hweq⟩ := List.mem_map.1 hw_mem
        obtain ⟨hzip, hpr⟩ := List.mem_filter.1 hfilt
        obtain ⟨hj, hICj⟩ := mem_zipIdx_iff.1 hzip
        rw [decide_eq_true_eq] at hpr
        rw [← hweq, show x.length + x.length + j = lits.length + j by rw [hlits_len],
          List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
          decide_eq_true_eq, hICj] at hval
        exact ⟨p, hICj ▸ List.getElem_mem hj, hpr, hval⟩
      · rintro ⟨p, hp, hpr, hall⟩
        obtain ⟨j, hj, hICj⟩ := List.getElem_of_mem hp
        have hw_mem : x.length + x.length + j ∈ dnfWires x.length IC r :=
          List.mem_map.2 ⟨(p, j), List.mem_filter.2
            ⟨mem_zipIdx_iff.2 ⟨hj, hICj⟩, decide_eq_true hpr⟩, rfl⟩
        obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw_mem
        refine ⟨⟨i, hi⟩, ?_⟩
        simp only [List.getElem?_eq_getElem hi, Option.elim_some, hwi]
        rw [show x.length + x.length + j = lits.length + j by rw [hlits_len],
          List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map, hICj,
          decide_eq_true_eq]
        exact hall
    · refine List.forall_mem_map.2 fun r _ w hw => ?_
      rw [hl2_len]; exact lt_of_mem_dnfWires hw
  set l3 := l2 ++ (List.range numDNFs).map fun r =>
    decide (∃ p ∈ IC, p.1 = r ∧ ∀ w ∈ p.2, lits.getD w false = true)
  have hl3_len : l3.length = x.length + x.length + IC.length + numDNFs := by
    simp [l3, hl2_len, Nat.add_assoc]
  rw [h1, h2, h3, evalCode_layer]
  · rw [← hl3_len, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [List.map_singleton, List.getD_cons_zero, interpretation_and]
    rw [decide_eq_decide, Fin.forall_iff]
    refine forall_congr' fun r => forall_congr' fun hr => ?_
    dsimp only
    have hr' : r < ((List.range numDNFs).map (x.length + x.length + IC.length + ·)).length := by
      simp [hr]
    rw [List.getElem?_eq_getElem hr']
    simp only [Option.elim_some, List.getElem_map, List.getElem_range]
    rw [show x.length + x.length + IC.length + r = l2.length + r by rw [hl2_len],
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map, List.getElem_range,
      decide_eq_true_eq]
  · refine List.forall_mem_singleton.2 (List.forall_mem_map.2 fun r hr => ?_)
    simp only [List.mem_range, hl3_len] at hr ⊢
    omega

private def varSetOfBits (F : WA3NSFormula) (x : BitString (toCircuit F).1) : Finset ℕ :=
  (Finset.univ.filter fun i => x i = true).map
    ⟨fun i => F.distinctVars[i.val]'(i.isLt.trans_eq (toCircuit_fst F)),
      fun _ _ h => Fin.ext ((List.Nodup.getElem_inj_iff F.nodup_distinctVars).1 h)⟩

private theorem mem_varSetOfBits {F : WA3NSFormula} {x : BitString (toCircuit F).1} {v : ℕ} :
    v ∈ varSetOfBits F x ↔ ∃ h : v ∈ F.distinctVars,
      x ⟨F.distinctVars.idxOf v, List.idxOf_lt_length_iff.2 h⟩ = true := by
  simp only [varSetOfBits, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, fun ⟨hv, hx⟩ => ⟨_, hx, List.getElem_idxOf _⟩⟩
  rintro ⟨i, hi, rfl⟩
  refine ⟨List.getElem_mem _, ?_⟩
  convert hi using 2
  exact Fin.ext (F.nodup_distinctVars.idxOf_getElem _ _)

/-- `toCircuit F` has a weight-`k` satisfying input if and only if `(F, k) ∈ WA3NS`. -/
theorem toCircuit_satisfiableWithWeight_iff (F : WA3NSFormula) (k : ℕ) :
    (toCircuit F).2.SatisfiableWithWeight interpretation k ↔ (⟨F, k⟩ : WA3NSInstance) ∈ WA3NS := by
  have hout : ((toCircuit F).2.outputs 0).toNat =
      F.distinctVars.length + F.distinctVars.length + (indexedClauses F).length +
        F.cleanDNFs.length :=
    congrArg (fun c => c.2.headD 0) (code_toCircuit F)
  have heval : ∀ x : BitString (toCircuit F).1,
      (toCircuit F).2.eval interpretation x 0 = true ↔ F.Satisfies (varSetOfBits F x) := by
    intro x
    rw [Circuit.eval_eq_getD _ _ false, hout, code_toCircuit]
    dsimp only [circuitCode]
    rw [evalCode_circuitGates (fun p hp w hw => lt_of_mem_indexedClauses hp hw) _
        (List.length_ofFn.trans (toCircuit_fst F)),
      decide_eq_true_eq]
    have hsub : varSetOfBits F x ⊆ F.varSet := fun v hv =>
      WA3NSFormula.mem_varSet.2 (mem_varSetOfBits.1 hv).1
    simp only [WA3NSFormula.Satisfies, hsub, true_and]
    have hneg_val : ∀ (v : ℕ) (hv : v ∈ F.distinctVars),
        ((List.ofFn x ++ (List.ofFn x).map (!·)).getD
          (F.distinctVars.length + F.distinctVars.idxOf v) false = true) ↔
          v ∉ varSetOfBits F x := by
      intro v hv
      have hidx : F.distinctVars.idxOf v < F.distinctVars.length := List.idxOf_lt_length_iff.2 hv
      have hlen : (List.ofFn x).length = F.distinctVars.length :=
        List.length_ofFn.trans (toCircuit_fst F)
      rw [← hlen, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by rw [List.length_map, hlen]; exact hidx), List.getElem_map,
        List.getElem_ofFn, Bool.not_eq_true', mem_varSetOfBits]
      exact ⟨fun h ⟨_, ht⟩ => Bool.false_ne_true (h.symm.trans ht),
        fun h => Bool.eq_false_iff.2 fun ht => h ⟨hv, ht⟩⟩
    have hvin_of : ∀ {r} (hr : r < F.cleanDNFs.length) {M}, M ∈ F.cleanDNFs[r] →
        ∀ {v}, v ∈ M → v ∈ F.distinctVars := by
      intro r hr M hM v hv
      obtain ⟨rawD, -, hrawD⟩ := List.mem_map.1 (List.getElem_mem hr : F.cleanDNFs[r] ∈ F.cleanDNFs)
      rw [← hrawD] at hM
      obtain ⟨rawM, -, rfl⟩ := List.mem_map.1 hM
      exact of_decide_eq_true (List.mem_filter.1 hv).2
    constructor
    · intro h D hD
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hD
      obtain ⟨p, hp, hpr, hall⟩ := h r hr
      simp only [indexedClauses, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨⟨D', r'⟩, hD'r', M, hM, rfl⟩ := hp
      obtain ⟨hD'_lt, hD'_eq⟩ := mem_zipIdx_iff.1 hD'r'
      dsimp only at hpr hM; subst hpr; rw [← hD'_eq] at hM
      exact ⟨M, hM, fun v hv =>
        (hneg_val v (hvin_of hr hM hv)).1 (hall _ (List.mem_map.2 ⟨v, hv, rfl⟩))⟩
    · intro h r hr
      obtain ⟨M, hM, hdisj⟩ := h F.cleanDNFs[r] (List.getElem_mem hr)
      refine ⟨(r, M.map fun v => F.distinctVars.length + F.distinctVars.idxOf v), ?_, rfl, ?_⟩
      · simp only [indexedClauses, List.mem_flatMap, List.mem_map]
        exact ⟨(F.cleanDNFs[r], r), mem_zipIdx_iff.2 ⟨hr, rfl⟩, M, hM, rfl⟩
      · intro w hw
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
        exact (hneg_val v (hvin_of hr hM hv)).2 (hdisj v hv)
  simp only [Circuit.SatisfiableWithWeight, heval, mem_WA3NS]
  refine ⟨fun ⟨x, hk, hx⟩ => ⟨varSetOfBits F x, hx, (Finset.card_map _).trans hk⟩, ?_⟩
  rintro ⟨A, hA, hk⟩
  let x : BitString (toCircuit F).1 := fun i =>
    decide (F.distinctVars[i.val]'(i.isLt.trans_eq (toCircuit_fst F)) ∈ A)
  have hvA : varSetOfBits F x = A := Finset.ext fun v => by
    simp only [mem_varSetOfBits, x, decide_eq_true_eq, List.getElem_idxOf, exists_prop]
    exact ⟨And.right, fun hv => ⟨WA3NSFormula.mem_varSet.1 (hA.1 hv), hv⟩⟩
  exact ⟨x, (Finset.card_map _).symm.trans ((congrArg Finset.card hvA).trans hk), hvA.symm ▸ hA⟩

/-- `indexedClauses` is polynomial-time (with indices and wires in unary). -/
theorem computableInPolyTime_indexedClauses :
    ComputableInPolyTime indexedClauses encWA3NSFormula
      (encList (encPair encUnary (encList encUnary))) := by
  have hV := WA3NSFormula.computableInPolyTime_distinctVars
  have hD := WA3NSFormula.computableInPolyTime_cleanDNFs
  unfold indexedClauses; polytime

/-- `dnfWires` is polynomial-time. -/
theorem computableInPolyTime_dnfWires {γ : Type} {encIn : γ ↪ List Bool}
    {nf rf : γ → ℕ} {IC : γ → List (ℕ × List ℕ)}
    (hn : ComputableInPolyTime nf encIn encUnary)
    (hIC : ComputableInPolyTime IC encIn (encList (encPair encUnary (encList encUnary))))
    (hr : ComputableInPolyTime rf encIn encUnary) :
    ComputableInPolyTime (fun a => dnfWires (nf a) (IC a) (rf a)) encIn (encList encUnary) := by
  unfold dnfWires; polytime

/-- `circuitCode` is polynomial-time. -/
theorem computableInPolyTime_circuitCode :
    ComputableInPolyTime circuitCode encWA3NSFormula (Circuit.encCode encOp) := by
  have hV := WA3NSFormula.computableInPolyTime_distinctVars
  have hD := WA3NSFormula.computableInPolyTime_cleanDNFs
  have hIC := computableInPolyTime_indexedClauses
  have hb := ComputableInPolyTime.unary_to_binary
  have hn : ComputableInPolyTime (fun F : WA3NSFormula => F.distinctVars.length)
      encWA3NSFormula encUnary := by fun_prop
  have hm : ComputableInPolyTime (fun F : WA3NSFormula => (indexedClauses F).length)
      encWA3NSFormula encUnary := by fun_prop
  have hP : ComputableInPolyTime (fun F : WA3NSFormula => F.cleanDNFs.length)
      encWA3NSFormula encUnary := by fun_prop
  have hnot : ComputableInPolyTime
      (fun F : WA3NSFormula => (List.range F.distinctVars.length).map
        fun i => ((Op.not, [i]) : Op × List ℕ))
      encWA3NSFormula (encList (Circuit.encGate encOp)) := by fun_prop
  have hand1 : ComputableInPolyTime
      (fun F : WA3NSFormula => (indexedClauses F).map fun p =>
        ((Op.and p.2.length, p.2) : Op × List ℕ))
      encWA3NSFormula (encList (Circuit.encGate encOp)) := by
    refine hIC.mapWithInput ?_
    have hp2 : ComputableInPolyTime (fun p : WA3NSFormula × (ℕ × List ℕ) => p.2.2)
        (encPair encWA3NSFormula (encPair encUnary (encList encUnary))) (encList encUnary) :=
      (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
    exact (computableInPolyTime_and.comp ((ComputableInPolyTime.length_list _).comp hp2)).prod
      (((ComputableInPolyTime.map hb).comp hp2).of_enc_eq fun _ => by simp)
  have hor : ComputableInPolyTime
      (fun F : WA3NSFormula => (List.range F.cleanDNFs.length).map fun r =>
        let W := dnfWires F.distinctVars.length (indexedClauses F) r
        ((Op.or W.length, W) : Op × List ℕ))
      encWA3NSFormula (encList (Circuit.encGate encOp)) := by
    refine (ComputableInPolyTime.range.comp hP).mapWithInput ?_
    have hW := computableInPolyTime_dnfWires (hn.comp (ComputableInPolyTime.fst _ _))
      (hIC.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _)
    exact (computableInPolyTime_or.comp ((ComputableInPolyTime.length_list _).comp hW)).prod
      (((ComputableInPolyTime.map hb).comp hW).of_enc_eq fun _ => by simp)
  have hand2 : ComputableInPolyTime
      (fun F : WA3NSFormula => [((Op.and F.cleanDNFs.length,
        (List.range F.cleanDNFs.length).map
          (F.distinctVars.length + F.distinctVars.length + (indexedClauses F).length + ·)) :
        Op × List ℕ)])
      encWA3NSFormula (encList (Circuit.encGate encOp)) :=
    .cons' ((computableInPolyTime_and.comp hP).prod
      ((ComputableInPolyTime.range.comp hP).mapWithInput (hb.comp
        (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_add' (hn.comp (ComputableInPolyTime.fst _ _))
            (hn.comp (ComputableInPolyTime.fst _ _)))
          (hm.comp (ComputableInPolyTime.fst _ _))) (ComputableInPolyTime.snd _ _))))) (.const [])
  unfold circuitCode circuitGates
  exact (((hnot.listAppend' hand1).listAppend' hor).listAppend' hand2).prod
    (.cons' (hb.comp (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hn hn) hm) hP)) (.const []))

/-- Map a `WA3NSInstance` to `WCSInstance 3 4`. -/
def toWCS (x : WA3NSInstance) : WCSInstance 3 4 :=
  ⟨⟨toCircuit x.formula, weft_toCircuit_le x.formula, depth_toCircuit_le x.formula⟩, x.k⟩

/-- `toWCS` is polynomial-time. -/
theorem computableInPolyTime_toWCS :
    ComputableInPolyTime toWCS encWA3NSInstance (encWCS 3 4) := by
  open scoped WA3NSInstance in
  have hc := computableInPolyTime_circuitCode
  have hV := WA3NSFormula.computableInPolyTime_distinctVars
  refine (by fun_prop : ComputableInPolyTime
      (fun x : WA3NSInstance => ((x.formula.distinctVars.length, circuitCode x.formula), x.k))
      encWA3NSInstance (encPair (encPair encUnary (Circuit.encCode encOp)) encNat)).of_enc_eq
    fun ⟨F, k⟩ => ?_
  simp only [toWCS, encWCS_apply, encPair_apply, encWeftCircuit_apply, Circuit.encCircuit_apply,
    code_toCircuit]; rfl

end WA3NSToCircuit

/-- **`WA3NS` FPT-reduces to `WCS 3 4`**. -/
theorem fptReducible_WA3NS_WCS :
    FPTReducible encWA3NSInstance (encWCS 3 4) (·.k) WCSInstance.weight WA3NS (WCS 3 4) :=
  FPTReducible.of_computableInPolyTime WA3NSToCircuit.computableInPolyTime_toWCS (h := id)
    (fun _ => le_rfl) fun x =>
      (WA3NSToCircuit.toCircuit_satisfiableWithWeight_iff x.formula x.k).symm

/-- **`WA3NS` belongs to `W[3]`**. -/
theorem WA3NS_mem_W : WA3NS ∈ W 3 encWA3NSInstance (·.k) :=
  ⟨4, fptReducible_WA3NS_WCS⟩

/-! ### `W[3]`-Hardness of `WA3NS` (`WCS 3 d ≤_FPT WA3NS`) -/

namespace WCSToWA3NS

/-- Bracket variable block `{N_certs + j | B[j].map fst = C}`. -/
def bracketVars (N_certs : ℕ) (B : List (List (ℕ × ℕ))) (C : List ℕ) : List ℕ :=
  (B.zipIdx.filter fun p => decide (p.1.map Prod.fst = C)).map fun p => N_certs + p.2

/-- Pairwise negative 2-clauses `(¬x_u ∨ ¬x_w)` (`[[u], [w]]`) enforcing `|A ∩ S| ≤ 1`. -/
def atMostOneDNFs (S : List ℕ) : List (List (List ℕ)) :=
  S.flatMap fun u => S.flatMap fun w => if decide (u < w) then [[[u], [w]]] else []

/-- Cross-block negative 2-clauses `(¬x_{P₁} ∨ ¬x_{P₂})` forbidding incompatible brackets. -/
def consistencyDNFs (N_certs : ℕ) (B : List (List (ℕ × ℕ))) : List (List (List ℕ)) :=
  B.zipIdx.flatMap fun p₁ =>
    B.zipIdx.flatMap fun p₂ =>
      if !decide (p₁.1.map Prod.fst = p₂.1.map Prod.fst) && !consistent p₁.1 p₂.1 then
        [[[N_certs + p₁.2], [N_certs + p₂.2]]]
      else []

/-- Antimonotone DNFs encoding two-level certificate/refutation checks for weft-`3` certificates
`C₃ = certsSucc 2 d n gates o true`. -/
def checkDNFs (d n kk : ℕ) (gates : List (Op × List ℕ))
    (C₃ : List (List (ℕ × Bool))) (B : List (List (ℕ × ℕ))) : List (List (List ℕ)) :=
  let N_certs := C₃.length
  C₃.zipIdx.flatMap fun p =>
    (p.1.flatMap (WeftOne.claimChecks n gates)).flatMap fun e₂ =>
      (certsSucc 1 d n gates e₂.1 (!e₂.2)).map fun cl₂ =>
        [p.2] :: ((cl₂.flatMap (WeftOne.claimChecks n gates)).flatMap fun e₁ =>
          (certsOne d n gates e₁.1 (!e₁.2)).map fun cl₁ =>
            (B.zipIdx.filter fun q => refutes n kk gates cl₁ q.1).map fun q => N_certs + q.2)

/-- Raw DNF list of the `WCS 3 d → WA3NS` reduction. -/
def rawDNFsOf (d n : ℕ) (gates : List (Op × List ℕ)) (o k : ℕ) : List (List (List ℕ)) :=
  let kk := min (n + 1) k
  let C₃ := certsSucc 2 d n gates o true
  let B := brackets d n kk
  let IL := indexLists d kk
  let N_certs := C₃.length
  atMostOneDNFs (List.range N_certs) ++
    (IL.flatMap fun C => atMostOneDNFs (bracketVars N_certs B C)) ++
    consistencyDNFs N_certs B ++
    checkDNFs d n kk gates C₃ B

/-- Antimonotone `3`-normalized formula of a weft-`3`, depth-`d` gate list. -/
def formula (d n : ℕ) (gates : List (Op × List ℕ)) (o k : ℕ) : WA3NSFormula :=
  let kk := min (n + 1) k
  let C₃ := certsSucc 2 d n gates o true
  let B := brackets d n kk
  { headVar := 0
    tailVars := List.range (C₃.length + B.length)
    dnfs := rawDNFsOf d n gates o k }

/-- Map a `WCSInstance 3 d` to a `WA3NSInstance`. -/
def toWA3NS {d : ℕ} (x : WCSInstance 3 d) : WA3NSInstance :=
  ⟨formula d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
    (x.circuit.toCircuit.2.outputs 0).toNat x.weight,
    size d x.circuit.toCircuit.1 x.weight⟩

private theorem brackets_pos (d n kk : ℕ) : 0 < (brackets d n kk).length :=
  List.length_pos_of_mem (mem_brackets.2 ⟨Nat.zero_le _, by simp⟩ : ([] : List _) ∈ _)

private theorem mem_distinctVars_formula_iff (d n : ℕ) (gates : List (Op × List ℕ))
    (o k v : ℕ) :
    v ∈ (formula d n gates o k).distinctVars ↔
      v < (certsSucc 2 d n gates o true).length + (brackets d n (min (n + 1) k)).length := by
  have hpos := brackets_pos d n (min (n + 1) k)
  rw [WA3NSFormula.mem_distinctVars]; simp only [formula, List.mem_range]; omega

private theorem mem_bracketVars_iff {N_certs : ℕ} {B : List (List (ℕ × ℕ))} {C : List ℕ} {v : ℕ} :
    v ∈ bracketVars N_certs B C ↔
      ∃ (j : ℕ) (hj : j < B.length), B[j].map Prod.fst = C ∧ v = N_certs + j := by
  simp only [bracketVars, List.mem_map, List.mem_filter, Prod.exists, mem_zipIdx_iff,
    decide_eq_true_eq]
  exact ⟨fun ⟨P, j, ⟨⟨hj, hP⟩, hC⟩, hv⟩ => ⟨j, hj, hP.symm ▸ hC, hv.symm⟩,
    fun ⟨j, hj, hC, hv⟩ => ⟨B[j], j, ⟨⟨hj, rfl⟩, hC⟩, hv.symm⟩⟩

private theorem rawDNFsOf_lt {d n : ℕ} {gates : List (Op × List ℕ)} {o k : ℕ}
    {D : List (List ℕ)} (hD : D ∈ rawDNFsOf d n gates o k) {M : List ℕ} (hM : M ∈ D)
    {v : ℕ} (hv : v ∈ M) :
    v < (certsSucc 2 d n gates o true).length + (brackets d n (min (n + 1) k)).length := by
  have hamo : ∀ {S : List ℕ} (hS : ∀ u ∈ S,
      u < (certsSucc 2 d n gates o true).length + (brackets d n (min (n + 1) k)).length)
      {D' : List (List ℕ)}, D' ∈ atMostOneDNFs S → ∀ M' ∈ D', ∀ u ∈ M',
      u < (certsSucc 2 d n gates o true).length + (brackets d n (min (n + 1) k)).length := by
    intro S hS D' hD' M' hM' u hu
    simp only [atMostOneDNFs, List.mem_flatMap] at hD'
    obtain ⟨a, ha, b, hb, hite⟩ := hD'
    split_ifs at hite; swap; · cases hite
    simp only [List.mem_singleton] at hite; subst hite
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM'
    rcases hM' with rfl | rfl <;> (rw [List.mem_singleton] at hu; subst hu; exact hS _ ‹_›)
  simp only [rawDNFsOf, List.mem_append, List.mem_flatMap] at hD
  rcases hD with ((hcert | ⟨C, -, hbr⟩) | hcons) | hchk
  · exact hamo (fun u hu => by have := List.mem_range.1 hu; omega) hcert M hM v hv
  · exact hamo (fun u hu => by obtain ⟨j, hj, -, rfl⟩ := mem_bracketVars_iff.1 hu; omega)
      hbr M hM v hv
  · simp only [consistencyDNFs, List.mem_flatMap] at hcons
    obtain ⟨⟨P₁, j₁⟩, hp₁, ⟨P₂, j₂⟩, hp₂, hite⟩ := hcons
    obtain ⟨hj₁, _⟩ := mem_zipIdx_iff.1 hp₁; obtain ⟨hj₂, _⟩ := mem_zipIdx_iff.1 hp₂
    split_ifs at hite; swap; · cases hite
    simp only [List.mem_singleton] at hite; subst hite
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl <;> (rw [List.mem_singleton] at hv; subst hv; omega)
  · simp only [checkDNFs, List.mem_flatMap, List.mem_map] at hchk
    obtain ⟨⟨cl₃, ic⟩, hic, e₂, -, cl₂, -, rfl⟩ := hchk
    obtain ⟨hic_lt, _⟩ := mem_zipIdx_iff.1 hic
    rcases List.mem_cons.1 hM with rfl | hM'
    · rw [List.mem_singleton] at hv; subst hv; omega
    · simp only [List.mem_flatMap, List.mem_map] at hM'
      obtain ⟨e₁, -, cl₁, -, rfl⟩ := hM'
      simp only [List.mem_map, List.mem_filter, Prod.exists, mem_zipIdx_iff] at hv
      obtain ⟨P, j, ⟨⟨hj, _⟩, _⟩, rfl⟩ := hv; omega

private theorem cleanDNFs_formula_eq (d n : ℕ) (gates : List (Op × List ℕ)) (o k : ℕ) :
    (formula d n gates o k).cleanDNFs = rawDNFsOf d n gates o k :=
  WA3NSFormula.cleanDNFs_eq_dnfs fun _ hD _ hM v hv =>
    (mem_distinctVars_formula_iff d n gates o k v).2 (rawDNFsOf_lt hD hM hv)

private theorem atMostOneDNFs_iff {S : List ℕ} {A : Finset ℕ} :
    (∀ D ∈ atMostOneDNFs S, ∃ M ∈ D, ∀ v ∈ M, v ∉ A) ↔ (A ∩ S.toFinset).card ≤ 1 := by
  constructor
  · intro h
    have hlt_false : ∀ {a b}, a ∈ A → a ∈ S → b ∈ A → b ∈ S → a < b → False := by
      intro a b haA haS hbA hbS hlt
      obtain ⟨M, hM, hdisj⟩ := h [[a], [b]]
        (List.mem_flatMap.2 ⟨a, haS, List.mem_flatMap.2 ⟨b, hbS, by simp [hlt]⟩⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
      rcases hM with rfl | rfl
      · exact hdisj a (List.mem_singleton_self a) haA
      · exact hdisj b (List.mem_singleton_self b) hbA
    rw [Finset.card_le_one]; intro u hu w hw
    rw [Finset.mem_inter, List.mem_toFinset] at hu hw
    by_contra hne
    exact (lt_or_gt_of_ne hne).elim (hlt_false hu.1 hu.2 hw.1 hw.2) (hlt_false hw.1 hw.2 hu.1 hu.2)
  · intro hcard D hD
    simp only [atMostOneDNFs, List.mem_flatMap] at hD
    obtain ⟨u, hu, w, hw, hite⟩ := hD
    split_ifs at hite with hlt; swap; · cases hite
    simp only [List.mem_singleton] at hite; subst hite
    by_cases huA : u ∈ A
    · refine ⟨[w], List.mem_cons_of_mem _ (List.mem_singleton_self _), fun v hv hvA => ?_⟩
      rw [List.mem_singleton.1 hv] at hvA
      have heq := Finset.card_le_one.1 hcard _ (Finset.mem_inter.2 ⟨huA, List.mem_toFinset.2 hu⟩)
        _ (Finset.mem_inter.2 ⟨hvA, List.mem_toFinset.2 hw⟩)
      rw [decide_eq_true_eq] at hlt; omega
    · exact ⟨[u], List.mem_cons_self, fun v hv => List.mem_singleton.1 hv ▸ huA⟩

private theorem map_fst_map_pair (u : ℕ → ℕ) (C : List ℕ) :
    (C.map fun j => (j, u j)).map Prod.fst = C := List.map_map.trans (List.map_id C)

private theorem eq_map_pair_of_map_fst {u : ℕ → ℕ} {P : List (ℕ × ℕ)} {C : List ℕ}
    (hC : P.map Prod.fst = C) (hu : ∀ p ∈ P, p.2 = u p.1) : P = C.map fun j => (j, u j) := by
  subst hC
  induction P with
  | nil => rfl
  | cons p P ih =>
    obtain ⟨a, b⟩ := p
    have hb : b = u a := hu (a, b) List.mem_cons_self; subst hb
    exact congrArg ((a, u a) :: ·) (ih fun q hq => hu q (List.mem_cons_of_mem _ hq))

/-- **Completeness of `toWA3NS`.** A weight-`k` satisfying input of a circuit of weft at most `3`
and depth at most `d` yields a weight-`(size d n k)` satisfying assignment of `formula`. -/
theorem mem_WA3NS_of_eval {d n : ℕ} (c : Circuit signature n 1) (hw : c.weft ≤ 3)
    (hd : c.depth ≤ d) {k : ℕ} (x : BitString n) (hk : BitString.weight x = k)
    (hx : c.eval interpretation x 0 = true) :
    (⟨formula d n c.code.1 (c.outputs 0).toNat k, size d n k⟩ : WA3NSInstance) ∈ WA3NS := by
  classical
  have hkn : k ≤ n := hk ▸ BitString.weight_le_length x
  have hkk : min (n + 1) k = k := min_eq_right (by omega)
  obtain ⟨u, hu, hun, rfl⟩ := exists_eq_selectedBits x hk
  have ho_wft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) c.code.1).getD (c.outputs 0).toNat 0 ≤ 3 := by
    simpa only [Circuit.getD_evalCode_depthInterpretation] using c.weft_le_iff.1 hw 0
  have ho_dp : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) c.code.1).getD (c.outputs 0).toNat 0 ≤ d := by
    simpa only [Circuit.getD_evalCode_depthInterpretation] using
      (c.wireDepthsWith_outputs_le_depthWith 1 0).trans (c.depthWith_one.trans_le hd)
  set gates := c.code.1
  set o := (c.outputs 0).toNat
  have ho_lt : o < n + gates.length := c.toNat_outputs_lt 0
  rw [c.eval_eq_getD interpretation false] at hx
  obtain ⟨cl₃, hcl₃, hchecks₃⟩ :=
    (eval_eq_iff_exists_certsSucc (t := 2) c.isCodeFrom_code List.length_ofFn ho_lt ho_wft ho_dp
      true).1 hx
  set C₃ := certsSucc 2 d n gates o true
  set B := brackets d n k
  set IL := indexLists d k
  set N_certs := C₃.length
  obtain ⟨ic, hic_lt, hic_eq⟩ := List.getElem_of_mem hcl₃
  let trueBr : List ℕ → List (ℕ × ℕ) := fun C => C.map fun j => (j, u j)
  have htrueBr_mem : ∀ C ∈ IL, trueBr C ∈ B := by
    intro C hC
    obtain ⟨hlen, hlt⟩ := mem_indexLists.1 hC
    refine mem_brackets.2 ⟨by simpa [trueBr] using hlen, fun p hp => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact ⟨hlt j hj, hun j (hlt j hj)⟩
  let ib : List ℕ → ℕ := fun C => B.idxOf (trueBr C)
  have hib_lt : ∀ C ∈ IL, ib C < B.length := fun C hC =>
    List.idxOf_lt_length_iff.2 (htrueBr_mem C hC)
  have hib_get : ∀ C (hC : C ∈ IL), B[ib C]'(hib_lt C hC) = trueBr C := fun C _ =>
    List.getElem_idxOf _
  let T : Finset ℕ := insert ic (IL.toFinset.image fun C => N_certs + ib C)
  have hC₃_eq : (certsSucc 2 d n gates o true).length = N_certs := rfl
  have hB_eq : (brackets d n k).length = B.length := rfl
  rw [mem_WA3NS]
  refine ⟨T, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    rw [WA3NSFormula.mem_varSet, mem_distinctVars_formula_iff, hkk, hC₃_eq, hB_eq]
    simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv
    rcases hv with rfl | ⟨C, hC, rfl⟩
    · exact Nat.lt_add_right _ hic_lt
    · have := hib_lt C hC; omega
  · rw [cleanDNFs_formula_eq]
    intro D hD
    simp only [rawDNFsOf, hkk, List.mem_append, List.mem_flatMap] at hD
    rcases hD with ((hcert | ⟨C, hC, hbr⟩) | hcons) | hchk
    · refine atMostOneDNFs_iff.2 ?_ D hcert
      have huniq : ∀ v ∈ T ∩ (List.range N_certs).toFinset, v = ic := by
        intro v hv
        rw [Finset.mem_inter, List.mem_toFinset, List.mem_range] at hv
        simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv
        rcases hv.1 with rfl | ⟨_, _, rfl⟩
        · rfl
        · omega
      exact Finset.card_le_one.2 fun v₁ h₁ v₂ h₂ => (huniq v₁ h₁).trans (huniq v₂ h₂).symm
    · refine atMostOneDNFs_iff.2 ?_ D hbr
      have huniq : ∀ v ∈ T ∩ (bracketVars N_certs B C).toFinset, v = N_certs + ib C := by
        intro v hv
        rw [Finset.mem_inter, List.mem_toFinset, mem_bracketVars_iff] at hv
        obtain ⟨j, hj, hCj, rfl⟩ := hv.2
        simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv
        rcases hv.1 with h | ⟨C', hC', h⟩
        · have : ic < N_certs := hic_lt; omega
        · have hj_eq : ib C' = j := Nat.add_left_cancel h
          have hB_eq' : B[j]'hj = trueBr C' := by rw [← hib_get C' hC']; simp only [hj_eq]
          have hC_eq : C' = C := by
            simpa only [trueBr, map_fst_map_pair, hCj] using
              (congrArg (List.map Prod.fst) hB_eq').symm
          subst hC_eq; omega
      exact Finset.card_le_one.2 fun v₁ h₁ v₂ h₂ => (huniq v₁ h₁).trans (huniq v₂ h₂).symm
    · simp only [consistencyDNFs, List.mem_flatMap] at hcons
      obtain ⟨⟨P₁, j₁⟩, hp₁, ⟨P₂, j₂⟩, hp₂, hite⟩ := hcons
      obtain ⟨hj₁, rfl⟩ := mem_zipIdx_iff.1 hp₁; obtain ⟨hj₂, rfl⟩ := mem_zipIdx_iff.1 hp₂
      split_ifs at hite with hbad; swap; · cases hite
      simp only [List.mem_singleton] at hite; subst hite
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hbad
      by_cases h1 : N_certs + j₁ ∈ T
      · refine ⟨[N_certs + j₂], List.mem_cons_of_mem _ (List.mem_singleton_self _),
          fun v hv h2 => ?_⟩
        rw [List.mem_singleton.1 hv] at h2
        simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at h1 h2
        rcases h1 with h1 | ⟨C₁, hC₁, h1⟩
        · have : ic < N_certs := hic_lt; omega
        rcases h2 with h2 | ⟨C₂', hC₂', h2⟩
        · have : ic < N_certs := hic_lt; omega
        have hj₁_eq : ib C₁ = j₁ := Nat.add_left_cancel h1
        have hj₂_eq : ib C₂' = j₂ := Nat.add_left_cancel h2
        have heq₁ : B[j₁] = trueBr C₁ := by rw [← hib_get C₁ hC₁]; simp only [hj₁_eq]
        have heq₂ : B[j₂] = trueBr C₂' := by rw [← hib_get C₂' hC₂']; simp only [hj₂_eq]
        have hcons_true : consistent (trueBr C₁) (trueBr C₂') = true := by
          rw [consistent_iff]; intro p hp q hq
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
          have ha_lt := (mem_indexLists.1 hC₁).2 a ha; have hb_lt := (mem_indexLists.1 hC₂').2 b hb
          exact (pairOk_iff _ _).2 ⟨(hu.injOn.eq_iff ha_lt hb_lt).symm,
            (hu.lt_iff_lt (Set.mem_Iio.2 ha_lt) (Set.mem_Iio.2 hb_lt)).symm⟩
        rw [heq₁, heq₂, hcons_true] at hbad; exact absurd hbad.2 (by decide)
      · exact ⟨[N_certs + j₁], List.mem_cons_self, fun v hv => List.mem_singleton.1 hv ▸ h1⟩
    · simp only [checkDNFs, List.mem_flatMap, List.mem_map] at hchk
      obtain ⟨⟨cl₃', jc⟩, hjc, e₂, he₂, cl₂, hcl₂, rfl⟩ := hchk
      obtain ⟨hjc_lt, rfl⟩ := mem_zipIdx_iff.1 hjc
      by_cases hjc_eq : ic = jc
      · subst hjc_eq
        have hic_eq' : (certsSucc 2 d n gates o true)[ic] = cl₃ := hic_eq
        rw [hic_eq'] at he₂
        have he₂' : e₂ ∈ cl₃.flatMap (WeftOne.claimChecks n gates) := List.mem_flatMap.2 he₂
        obtain ⟨he₂_lt, he₂_wft, he₂_dp⟩ :=
          check_bounds_of_mem_certsSucc c.isCodeFrom_code hcl₃ he₂'
        have he₂_val := hchecks₃ e₂ he₂'
        obtain ⟨e₁, he₁, he₁_fail⟩ :=
          (eval_eq_iff_forall_certsSucc_not (t := 1) c.isCodeFrom_code List.length_ofFn
            he₂_lt he₂_wft he₂_dp e₂.2).1 he₂_val cl₂ hcl₂
        obtain ⟨he₁_lt, he₁_wft, he₁_dp⟩ :=
          check_bounds_of_mem_certsSucc c.isCodeFrom_code hcl₂ he₁
        obtain ⟨cl₁, hcl₁, hchecks₁⟩ :=
          (eval_eq_iff_exists_certsOne c.isCodeFrom_code List.length_ofFn
            he₁_lt he₁_wft he₁_dp (!e₁.2)).1 he₁_fail
        have hnoref := (checks_selectedBits_iff_forall_not_refutes c.isCodeFrom_code hu hcl₁).1
          hchecks₁
        let M := (B.zipIdx.filter fun q => refutes n k gates cl₁ q.1).map fun q => N_certs + q.2
        refine ⟨M, List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨e₁, he₁,
          List.mem_map.2 ⟨cl₁, hcl₁, rfl⟩⟩), fun v hv hvT => ?_⟩
        simp only [M, List.mem_map, List.mem_filter, Prod.exists, mem_zipIdx_iff] at hv
        obtain ⟨P, j, ⟨⟨hj, rfl⟩, href_true⟩, rfl⟩ := hv
        simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hvT
        rcases hvT with h | ⟨C, hC, h⟩
        · have : ic < N_certs := hic_lt; omega
        · have hj_eq : ib C = j := Nat.add_left_cancel h
          have hPeq : B[j] = trueBr C := by rw [← hib_get C hC]; simp only [hj_eq]
          rw [hPeq, hnoref C hC] at href_true
          exact Bool.false_ne_true href_true
      · refine ⟨[jc], List.mem_cons_self, fun v hv hvT => ?_⟩
        rw [List.mem_singleton.1 hv] at hvT
        simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hvT
        rcases hvT with rfl | ⟨_, _, h⟩
        · exact hjc_eq rfl
        · have : jc < N_certs := hjc_lt; omega
  · have hnotMem : ic ∉ IL.toFinset.image fun C => N_certs + ib C := by
      simp only [Finset.mem_image, List.mem_toFinset, not_exists, not_and]
      intro C _ h; have : ic < N_certs := hic_lt; omega
    have hinj : Set.InjOn (fun C => N_certs + ib C) (IL.toFinset : Set (List ℕ)) := by
      intro C₁ h₁ C₂' h₂ h
      rw [Finset.mem_coe, List.mem_toFinset] at h₁ h₂
      have hib_eq : ib C₁ = ib C₂' := Nat.add_left_cancel h
      have hbr_eq : trueBr C₁ = trueBr C₂' := by
        rw [← hib_get C₁ h₁, ← hib_get C₂' h₂]; simp only [hib_eq]
      simpa only [trueBr, map_fst_map_pair] using congrArg (List.map Prod.fst) hbr_eq
    rw [Finset.card_insert_of_notMem hnotMem, Finset.card_image_of_injOn hinj,
      List.toFinset_card_of_nodup (nodup_indexLists d k), size, hkk, add_comm]

/-- **Soundness of `toWA3NS`.** A weight-`(size d n k)` satisfying assignment of `formula` yields a
weight-`k` satisfying input of `c`. -/
theorem satisfiableWithWeight_of_mem_WA3NS {d n : ℕ} (c : Circuit signature n 1) {k : ℕ}
    (h : (⟨formula d n c.code.1 (c.outputs 0).toNat k, size d n k⟩ : WA3NSInstance) ∈ WA3NS) :
    c.SatisfiableWithWeight interpretation k := by
  classical
  set kk := min (n + 1) k with hkk_def
  set gates := c.code.1
  set o := (c.outputs 0).toNat
  set C₃ := certsSucc 2 d n gates o true
  set B := brackets d n kk
  set IL := indexLists d kk
  set N_certs := C₃.length
  obtain ⟨A, ⟨hAV, hAsat⟩, hAcard⟩ := mem_WA3NS.1 h
  rw [cleanDNFs_formula_eq] at hAsat
  rw [size, ← hkk_def] at hAcard
  -- At-most-one per block + total weight `IL.length + 1` forces exact single-selection per block
  let Scert : Finset ℕ := A ∩ (List.range N_certs).toFinset
  let Sbr : List ℕ → Finset ℕ := fun C => A ∩ (bracketVars N_certs B C).toFinset
  have hScert_le : Scert.card ≤ 1 := atMostOneDNFs_iff.1 fun D hD =>
    hAsat D (by simp only [rawDNFsOf, ← hkk_def,
      List.mem_append]; exact Or.inl (Or.inl (Or.inl hD)))
  have hSbr_le : ∀ C ∈ IL, (Sbr C).card ≤ 1 := fun C hC =>
    atMostOneDNFs_iff.1 fun D hD => hAsat D (by
      simp only [rawDNFsOf, ← hkk_def, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inr ⟨C, hC, hD⟩)))
  have hpw : (IL.toFinset : Set (List ℕ)).PairwiseDisjoint Sbr := by
    intro C₁ _ C₂ _ hne; change Disjoint (Sbr C₁) (Sbr C₂); rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [Sbr, Finset.mem_inter, List.mem_toFinset, mem_bracketVars_iff] at hv₁ hv₂
    obtain ⟨j₁, hj₁, hC₁, rfl⟩ := hv₁.2; obtain ⟨j₂, hj₂, hC₂, hv_eq⟩ := hv₂.2
    have hj_eq : j₁ = j₂ := by dsimp only [N_certs] at *; omega
    subst hj_eq; exact hne (hC₁.symm.trans hC₂)
  have hdisj_cert : Disjoint Scert (IL.toFinset.biUnion Sbr) := by
    rw [Finset.disjoint_left]; intro v hv₁ hv₂
    simp only [Scert, Finset.mem_inter, List.mem_toFinset, List.mem_range] at hv₁
    simp only [Finset.mem_biUnion, Sbr, Finset.mem_inter, List.mem_toFinset,
      mem_bracketVars_iff] at hv₂
    obtain ⟨C, -, -, ⟨j, -, -, rfl⟩⟩ := hv₂; dsimp only [N_certs] at *; omega
  have hA_eq_union : A = Scert ∪ IL.toFinset.biUnion Sbr := by
    ext v
    simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, Scert, Sbr,
      Finset.mem_inter, List.mem_range, mem_bracketVars_iff]
    refine ⟨fun hvA => ?_, fun h => h.elim And.left fun ⟨_, _, h⟩ => h.1⟩
    have hv_lt : v < N_certs + B.length :=
      (mem_distinctVars_formula_iff d n gates o k v).1 (WA3NSFormula.mem_varSet.1 (hAV hvA))
    rcases Nat.lt_or_ge v N_certs with hlt | hge
    · exact Or.inl ⟨hvA, hlt⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
      have hj : j < B.length := by dsimp only [N_certs] at *; omega
      obtain ⟨hlen, hlt_pair⟩ := mem_brackets.1 (List.getElem_mem hj)
      have hCj : B[j].map Prod.fst ∈ IL := mem_indexLists.2
        ⟨by simpa using hlen, fun idx hidx =>
          let ⟨p, hp, h⟩ := List.mem_map.1 hidx; h ▸ (hlt_pair p hp).1⟩
      exact Or.inr ⟨B[j].map Prod.fst, hCj, hvA, j, hj, rfl, rfl⟩
  have hAcard_sum : A.card = Scert.card + ∑ C ∈ IL.toFinset, (Sbr C).card := by
    conv_lhs => rw [hA_eq_union]
    rw [Finset.card_union_of_disjoint hdisj_cert, Finset.card_biUnion hpw]
  have hIL_card : (IL.toFinset).card = IL.length :=
    List.toFinset_card_of_nodup (nodup_indexLists d kk)
  have hsum_le : ∑ C ∈ IL.toFinset, (Sbr C).card ≤ IL.length :=
    (Finset.sum_le_sum fun C hC => hSbr_le C (List.mem_toFinset.1 hC)).trans_eq (by
      rw [Finset.sum_const, smul_eq_mul, mul_one, hIL_card])
  have hAcard' : A.card = IL.length + 1 := hAcard
  have hScert_one : Scert.card = 1 := by omega
  have hSbr_one : ∀ C ∈ IL, (Sbr C).card = 1 := by
    intro C hC; by_contra hne1
    have hsum_lt : ∑ C' ∈ IL.toFinset, (Sbr C').card < IL.length :=
      (Finset.sum_lt_sum (fun C' hC' => hSbr_le C' (List.mem_toFinset.1 hC'))
        ⟨C, List.mem_toFinset.2 hC, by have := hSbr_le C hC; omega⟩).trans_eq (by
          rw [Finset.sum_const, smul_eq_mul, mul_one, hIL_card])
    omega
  obtain ⟨ic, hic_eq⟩ := Finset.card_eq_one.1 hScert_one
  have hic_mem : ic ∈ Scert := hic_eq ▸ Finset.mem_singleton_self ic
  have hic_A : ic ∈ A := (Finset.mem_inter.1 hic_mem).1
  have hic_lt : ic < N_certs :=
    List.mem_range.1 (List.mem_toFinset.1 (Finset.mem_inter.1 hic_mem).2)
  have hbr_sel : ∀ C ∈ IL, ∃ j, ∃ hj : j < B.length,
      B[j].map Prod.fst = C ∧ Sbr C = {N_certs + j} ∧ N_certs + j ∈ A := by
    intro C hC
    obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.1 (hSbr_one C hC)
    have hv_mem : v ∈ Sbr C := hv_eq ▸ Finset.mem_singleton_self v
    obtain ⟨j, hj, hC_eq, rfl⟩ :=
      mem_bracketVars_iff.1 (List.mem_toFinset.1 (Finset.mem_inter.1 hv_mem).2)
    exact ⟨j, hj, hC_eq, hv_eq, (Finset.mem_inter.1 hv_mem).1⟩
  choose! jb hjb_lt hjb_fst hjb_eq hjb_A using hbr_sel
  -- Consistency between selected brackets
  have hcons_sel : ∀ (C₁ : List ℕ) (hC₁ : C₁ ∈ IL) (C₂' : List ℕ) (hC₂' : C₂' ∈ IL), C₁ ≠ C₂' →
      consistent (B[jb C₁]'(hjb_lt C₁ hC₁)) (B[jb C₂']'(hjb_lt C₂' hC₂')) = true := by
    intro C₁ hC₁ C₂' hC₂' hne
    by_contra hnc
    simp only [Bool.not_eq_true] at hnc
    have hD : [[N_certs + jb C₁], [N_certs + jb C₂']] ∈ rawDNFsOf d n gates o k := by
      simp only [rawDNFsOf, ← hkk_def, List.mem_append]
      refine Or.inl (Or.inr ?_)
      simp only [consistencyDNFs, List.mem_flatMap]
      refine ⟨(B[jb C₁]'(hjb_lt C₁ hC₁), jb C₁), mem_zipIdx_iff.2 ⟨hjb_lt C₁ hC₁, rfl⟩,
        (B[jb C₂']'(hjb_lt C₂' hC₂'), jb C₂'), mem_zipIdx_iff.2 ⟨hjb_lt C₂' hC₂', rfl⟩, ?_⟩
      simp only [hjb_fst C₁ hC₁, hjb_fst C₂' hC₂', hne, decide_false, Bool.not_false, hnc,
        Bool.and_self, ↓reduceIte, List.mem_singleton]
      rfl
    obtain ⟨M, hM, hdisj⟩ := hAsat _ hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · exact hdisj _ (List.mem_singleton_self _) (hjb_A C₁ hC₁)
    · exact hdisj _ (List.mem_singleton_self _) (hjb_A C₂' hC₂')
  have hjIL_of : ∀ {j}, j < kk → [j] ∈ IL := fun hj =>
    mem_indexLists.2 ⟨by simp [Nat.one_le_two_pow], by simpa using hj⟩
  have hsing : ∀ (j : ℕ), ∀ (hj : j < kk), ∃ s,
      B[jb [j]]'(hjb_lt [j] (hjIL_of hj)) = [(j, s)] ∧ s < n := by
    intro j hj
    obtain ⟨⟨j', s⟩, hP, hj'⟩ := List.map_eq_singleton_iff.1 (hjb_fst [j] (hjIL_of hj))
    rw [show j' = j from hj'] at hP
    have hBmem : B[jb [j]]'(hjb_lt [j] (hjIL_of hj)) ∈ B := List.getElem_mem _
    exact ⟨s, hP, ((mem_brackets.1 hBmem).2 (j, s) (hP ▸ List.mem_singleton_self _)).2⟩
  choose! u hu_eq hun using hsing
  have hpairs : ∀ C (hC : C ∈ IL) p, p ∈ B[jb C]'(hjb_lt C hC) → p.1 < kk ∧ p.2 = u p.1 := by
    intro C hC p hp
    have hp1 : p.1 < kk := ((mem_brackets.1 (List.getElem_mem _)).2 p hp).1
    refine ⟨hp1, ?_⟩
    by_cases hCeq : C = [p.1]
    · subst hCeq; rw [hu_eq p.1 hp1, List.mem_singleton] at hp; exact congrArg Prod.snd hp
    · have hok := consistent_iff.1 (hcons_sel C hC [p.1] (hjIL_of hp1) hCeq) p hp (p.1, u p.1)
        (by rw [hu_eq p.1 hp1]; exact List.mem_singleton_self _)
      exact ((pairOk_iff _ _).1 hok).1.1 rfl
  have hmono : StrictMonoOn u (Set.Iio kk) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    have hcons := hcons_sel [i] (hjIL_of hi) [j] (hjIL_of hj) (by simp; omega)
    have hok := consistent_iff.1 hcons (i, u i)
      (by rw [hu_eq i hi]; exact List.mem_singleton_self _) (j, u j)
      (by rw [hu_eq j hj]; exact List.mem_singleton_self _)
    exact ((pairOk_iff _ _).1 hok).2.1 hij
  have hkk_eq : kk = k := by
    have := (weight_selectedBits hmono hun).symm.trans_le (BitString.weight_le_length _); omega
  have hB_true : ∀ C (hC : C ∈ IL), B[jb C]'(hjb_lt C hC) = C.map fun j => (j, u j) :=
    fun C hC => eq_map_pair_of_map_fst (hjb_fst C hC) fun p hp => (hpairs C hC p hp).2
  set cl₃ := C₃[ic]
  have hcl₃_mem : cl₃ ∈ C₃ := List.getElem_mem hic_lt
  refine ⟨selectedBits n kk u, hkk_eq ▸ weight_selectedBits hmono hun, ?_⟩
  rw [c.eval_eq_getD interpretation false]
  refine eval_eq_of_kleeneEval_override c.isCodeFrom_code (kleeneEval_of_mem_certsSucc hcl₃_mem)
    List.length_ofFn ?_
  intro e₂ he₂
  obtain ⟨he₂_lt, he₂_wft, he₂_dp⟩ := check_bounds_of_mem_certsSucc c.isCodeFrom_code hcl₃_mem he₂
  rw [eval_eq_iff_forall_certsSucc_not (t := 1) c.isCodeFrom_code List.length_ofFn
    he₂_lt he₂_wft he₂_dp]
  intro cl₂ hcl₂
  let D := [ic] :: ((cl₂.flatMap (WeftOne.claimChecks n gates)).flatMap fun e₁ =>
    (certsOne d n gates e₁.1 (!e₁.2)).map fun cl₁ =>
      (B.zipIdx.filter fun q => refutes n kk gates cl₁ q.1).map fun q => N_certs + q.2)
  have hD_mem : D ∈ rawDNFsOf d n gates o k := by
    simp only [rawDNFsOf, ← hkk_def, List.mem_append]; refine Or.inr ?_
    simp only [checkDNFs, List.mem_flatMap, List.mem_map]
    exact ⟨(cl₃, ic), mem_zipIdx_iff.2 ⟨hic_lt, rfl⟩, e₂, List.mem_flatMap.1 he₂, cl₂, hcl₂, rfl⟩
  obtain ⟨M, hM, hdisj⟩ := hAsat D hD_mem
  rcases List.mem_cons.1 hM with rfl | hM'
  · exact absurd hic_A (hdisj ic (List.mem_singleton_self ic))
  · simp only [List.mem_flatMap, List.mem_map] at hM'
    obtain ⟨e₁, he₁, cl₁, hcl₁, rfl⟩ := hM'
    have he₁' : e₁ ∈ cl₂.flatMap (WeftOne.claimChecks n gates) := List.mem_flatMap.2 he₁
    obtain ⟨he₁_lt, he₁_wft, he₁_dp⟩ := check_bounds_of_mem_certsSucc c.isCodeFrom_code hcl₂ he₁'
    refine ⟨e₁, he₁', (eval_eq_iff_exists_certsOne c.isCodeFrom_code List.length_ofFn
      he₁_lt he₁_wft he₁_dp (!e₁.2)).2 ⟨cl₁, hcl₁, ?_⟩⟩
    rw [checks_selectedBits_iff_forall_not_refutes c.isCodeFrom_code hmono hcl₁]
    intro C hC; by_contra href_ne; simp only [Bool.not_eq_false] at href_ne
    have hvM : N_certs + jb C ∈
        (B.zipIdx.filter fun q => refutes n kk gates cl₁ q.1).map (fun q => N_certs + q.2) :=
      List.mem_map.2 ⟨(B[jb C]'(hjb_lt C hC), jb C), List.mem_filter.2
        ⟨mem_zipIdx_iff.2 ⟨hjb_lt C hC, rfl⟩, by rwa [hB_true C hC]⟩, rfl⟩
    exact hdisj _ hvM (hjb_A C hC)

/-- **Correctness of `toWA3NS`.** -/
theorem toWA3NS_mem_WA3NS_iff {d : ℕ} (x : WCSInstance 3 d) :
    toWA3NS x ∈ WA3NS ↔ x ∈ WCS 3 d := by
  obtain ⟨⟨⟨n, c⟩, hw, hd⟩, k⟩ := x
  rw [mem_WCS]
  exact ⟨satisfiableWithWeight_of_mem_WA3NS c,
    fun ⟨y, hy, hc⟩ => mem_WA3NS_of_eval c hw hd y hy hc⟩

/-! ### Polynomial-time computability of `toWA3NS` -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

private theorem computableInPolyTime_unaryList_to_natList {f : γ → List ℕ}
    (hf : ComputableInPolyTime f encIn (encList encUnary)) :
    ComputableInPolyTime f encIn (encList encNat) :=
  ((ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hf).of_enc_eq fun _ =>
    by simp

private theorem computableInPolyTime_unaryList3_to_natList3 {f : γ → List (List (List ℕ))}
    (hf : ComputableInPolyTime f encIn (encList (encList (encList encUnary)))) :
    ComputableInPolyTime f encIn (encList (encList (encList encNat))) :=
  ((ComputableInPolyTime.map (ComputableInPolyTime.map
    (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary))).comp hf).of_enc_eq fun a => by
    dsimp only [Function.comp_apply]; induction f a with | nil => rfl | cons D Ds ih => simp [ih]

private theorem computableInPolyTime_bracketVars
    {nc : γ → ℕ} {B : γ → List (List (ℕ × ℕ))} {C : γ → List ℕ}
    (hnc : ComputableInPolyTime nc encIn encUnary)
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary))))
    (hC : ComputableInPolyTime C encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => bracketVars (nc a) (B a) (C a)) encIn (encList encUnary) := by
  unfold bracketVars; polytime

private theorem computableInPolyTime_atMostOneDNFs {S : γ → List ℕ}
    (hS : ComputableInPolyTime S encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => atMostOneDNFs (S a)) encIn
      (encList (encList (encList encUnary))) := by
  unfold atMostOneDNFs
  refine hS.flatMapWithInput ((hS.comp (ComputableInPolyTime.fst _ _)).flatMapWithInput ?_)
  exact ComputableInPolyTime.ite' (by polytime) (.cons' (.cons' (.cons' (by fun_prop) (.const []))
    (.cons' (.cons' (by fun_prop) (.const [])) (.const []))) (.const [])) (.const [])

attribute [local fun_prop] computableInPolyTime_consistent in
private theorem computableInPolyTime_consistencyDNFs
    {nc : γ → ℕ} {B : γ → List (List (ℕ × ℕ))} (hnc : ComputableInPolyTime nc encIn encUnary)
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary)))) :
    ComputableInPolyTime (fun a => consistencyDNFs (nc a) (B a)) encIn
      (encList (encList (encList encUnary))) := by
  unfold consistencyDNFs; have hBz := (ComputableInPolyTime.zipIdx _).comp hB
  refine hBz.flatMapWithInput ((hBz.comp (ComputableInPolyTime.fst _ _)).flatMapWithInput ?_)
  exact ComputableInPolyTime.ite' (by polytime) (.cons' (.cons' (.cons' (by fun_prop) (.const []))
    (.cons' (.cons' (by fun_prop) (.const [])) (.const []))) (.const [])) (.const [])

attribute [local fun_prop] computableInPolyTime_refutes_poly in
private theorem computableInPolyTime_checkDNFs (d : ℕ)
    {n kk : γ → ℕ} {gates : γ → List (Op × List ℕ)}
    {C₃ : γ → List (List (ℕ × Bool))} {B : γ → List (List (ℕ × ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (hC₃ : ComputableInPolyTime C₃ encIn (encList (encList (encPair encUnary encBool))))
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary)))) :
    ComputableInPolyTime (fun a => checkDNFs d (n a) (kk a) (gates a) (C₃ a) (B a))
      encIn (encList (encList (encList encUnary))) := by
  unfold checkDNFs; refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
  refine ComputableInPolyTime.flatMapWithInput (WeftOne.computableInPolyTime_checks
    (hn.comp (by fun_prop)) (hg.comp (by fun_prop)) (by fun_prop)) ?_
  refine ComputableInPolyTime.mapWithInput (computableInPolyTime_certsSucc 1 d
    (hn.comp (by fun_prop)) (hg.comp (by fun_prop))
    ((ComputableInPolyTime.fst encNat encBool).comp (ComputableInPolyTime.snd _ _))
    (by polytime)) ?_
  refine ComputableInPolyTime.cons' (.cons' (by fun_prop) (.const [])) ?_
  refine ComputableInPolyTime.flatMapWithInput (WeftOne.computableInPolyTime_checks
    (hn.comp (by fun_prop)) (hg.comp (by fun_prop)) (by fun_prop)) ?_
  refine ComputableInPolyTime.mapWithInput (computableInPolyTime_certsOne d
    (hn.comp (by fun_prop)) (hg.comp (by fun_prop))
    ((ComputableInPolyTime.fst encNat encBool).comp (ComputableInPolyTime.snd _ _))
    (by polytime)) ?_
  polytime

private theorem computableInPolyTime_rawDNFsOf_aux
    {nc : γ → ℕ} {IL : γ → List (List ℕ)} {B : γ → List (List (ℕ × ℕ))}
    {cons chk : γ → List (List (List ℕ))}
    (hnc : ComputableInPolyTime nc encIn encUnary)
    (hIL : ComputableInPolyTime IL encIn (encList (encList encUnary)))
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary))))
    (hcons : ComputableInPolyTime cons encIn (encList (encList (encList encUnary))))
    (hchk : ComputableInPolyTime chk encIn (encList (encList (encList encUnary)))) :
    ComputableInPolyTime (fun a => atMostOneDNFs (List.range (nc a)) ++
      ((IL a).flatMap fun C => atMostOneDNFs (bracketVars (nc a) (B a) C)) ++
      cons a ++ chk a) encIn (encList (encList (encList encNat))) :=
  computableInPolyTime_unaryList3_to_natList3
    ((((computableInPolyTime_atMostOneDNFs (ComputableInPolyTime.range.comp hnc)).listAppend'
      (hIL.flatMapWithInput (computableInPolyTime_atMostOneDNFs
        (computableInPolyTime_bracketVars (hnc.comp (ComputableInPolyTime.fst _ _))
          (hB.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))))).listAppend'
      hcons).listAppend' hchk)

private theorem computableInPolyTime_rawDNFsOf (d : ℕ)
    {n o k : γ → ℕ} {gates : γ → List (Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (ho : ComputableInPolyTime o encIn encNat)
    (hk : ComputableInPolyTime k encIn encNat) :
    ComputableInPolyTime (fun a => rawDNFsOf d (n a) (gates a) (o a) (k a)) encIn
      (encList (encList (encList encNat))) := by
  have hkk : ComputableInPolyTime (fun a => min (n a + 1) (k a)) encIn encUnary := by fun_prop
  have hC₃ := computableInPolyTime_certsSucc 2 d hn hg ho (ComputableInPolyTime.const true)
  have hB := computableInPolyTime_brackets_poly d hn hkk
  have hIL := computableInPolyTime_indexLists_poly d hkk
  have hnc : ComputableInPolyTime (fun a => (certsSucc 2 d (n a) (gates a) (o a) true).length)
      encIn encUnary := (ComputableInPolyTime.length_list _).comp hC₃
  unfold rawDNFsOf
  exact computableInPolyTime_rawDNFsOf_aux hnc hIL hB
    (computableInPolyTime_consistencyDNFs hnc hB)
    (computableInPolyTime_checkDNFs d hn hkk hg hC₃ hB)

/-- `toWA3NS` is polynomial-time for every fixed depth `d`. -/
theorem computableInPolyTime_toWA3NS (d : ℕ) :
    ComputableInPolyTime (toWA3NS (d := d)) (encWCS 3 d) encWA3NSInstance := by
  open scoped WA3NSInstance WA3NSFormula in
  have hwc := encWCS_circuit_polyTime (t := 3) (d := d) .id'
  have hn := WeftCircuit.computableInPolyTime_numInputs hwc
  have hg := WeftCircuit.computableInPolyTime_gates hwc
  have houts := WeftCircuit.computableInPolyTime_outputs hwc
  have hk := encWCS_weight_polyTime (t := 3) (d := d) .id'
  have ho : ComputableInPolyTime (fun x : WCSInstance 3 d => x.circuit.toCircuit.2.code.2.getD 0 0)
      (encWCS 3 d) encNat := by fun_prop
  have hkk : ComputableInPolyTime
      (fun x : WCSInstance 3 d => min (x.circuit.toCircuit.1 + 1) x.weight)
      (encWCS 3 d) encUnary := by fun_prop
  have hC₃ := computableInPolyTime_certsSucc 2 d hn hg ho (ComputableInPolyTime.const true)
  have hB := computableInPolyTime_brackets_poly d hn hkk
  have htail : ComputableInPolyTime (fun x : WCSInstance 3 d =>
      List.range ((certsSucc 2 d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
        (x.circuit.toCircuit.2.code.2.getD 0 0) true).length +
        (brackets d x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)).length))
      (encWCS 3 d) (encList encNat) :=
    computableInPolyTime_unaryList_to_natList (ComputableInPolyTime.range.comp
      (ComputableInPolyTime.unary_add' ((ComputableInPolyTime.length_list _).comp hC₃)
        ((ComputableInPolyTime.length_list _).comp hB)))
  have hraw := computableInPolyTime_rawDNFsOf d hn hg ho hk
  have hsize : ComputableInPolyTime (fun x : WCSInstance 3 d =>
      size d x.circuit.toCircuit.1 x.weight) (encWCS 3 d) encNat := by
    unfold size; exact ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add'
      ((ComputableInPolyTime.length_list _).comp (computableInPolyTime_indexLists_poly d hkk))
      (.const 1))
  have hmk : ∀ (f2 : WCSInstance 3 d → List ℕ) (f3 : WCSInstance 3 d → List (List (List ℕ)))
      (fk : WCSInstance 3 d → ℕ), ComputableInPolyTime f2 (encWCS 3 d) (encList encNat) →
      ComputableInPolyTime f3 (encWCS 3 d) (encList (encList (encList encNat))) →
      ComputableInPolyTime fk (encWCS 3 d) encNat →
      ComputableInPolyTime (fun x => WA3NSInstance.mk ⟨0, f2 x, f3 x⟩ (fk x))
        (encWCS 3 d) encWA3NSInstance := by intros; fun_prop
  have heq : (toWA3NS (d := d)) = fun x : WCSInstance 3 d =>
      ⟨formula d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
        (x.circuit.toCircuit.2.code.2.getD 0 0) x.weight,
        size d x.circuit.toCircuit.1 x.weight⟩ := by funext x; simp [toWA3NS, Circuit.code]
  rw [heq]; exact hmk _ _ _ htail hraw hsize

end PolyTime

end WCSToWA3NS

/-- **Downey–Fellows Antimonotone Collapse for `W[3]`.** For every fixed depth `d`, `WCS 3 d`
FPT-reduces to `WA3NS` with parameter bound `k' ≤ (k + 1) ^ 2 ^ (d + 1) + 1`. -/
theorem fptReducible_WCS_WA3NS (d : ℕ) :
    FPTReducible (encWCS 3 d) encWA3NSInstance WCSInstance.weight (·.k) (WCS 3 d) WA3NS :=
  FPTReducible.of_computableInPolyTime (WCSToWA3NS.computableInPolyTime_toWA3NS d)
    (h := fun k => (k + 1) ^ 2 ^ (d + 1) + 1) (fun _ => size_le d _ _)
    fun x => (WCSToWA3NS.toWA3NS_mem_WA3NS_iff x).symm

/-- **`WA3NS` is `W[3]`-hard**. -/
theorem WA3NS_wHard : WHard 3 encWA3NSInstance (·.k) WA3NS :=
  wHard_iff.2 fptReducible_WCS_WA3NS

/-- **`W[3] = FPT` if and only if `WA3NS ∈ FPT`**. -/
theorem W_three_eq_FPT_iff :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 3 enc κ = FPT enc κ) ↔
      WA3NS ∈ FPT encWA3NSInstance (·.k) :=
  ⟨fun h => h _ _ ▸ WA3NS_mem_W,
    fun h _ _ _ => Set.Subset.antisymm (WA3NS_wHard.subset_FPT h) (FPT_subset_W 3)⟩

section Witnesses

private theorem wa3ns_nondegenerate_example :
    ∃ F : WA3NSFormula,
      (⟨F, 2⟩ : WA3NSInstance) ∈ WA3NS ∧ (⟨F, 3⟩ : WA3NSInstance) ∉ WA3NS := by
  -- ((¬x₁ ∧ ¬x₂ ∧ ¬x₄) ∨ (¬x₃ ∧ ¬x₄)) ∧ ((¬x₁ ∧ ¬x₃) ∨ (¬x₂ ∧ ¬x₅) ∨ (¬x₁ ∧ ¬x₄ ∧ ¬x₅))
  let F : WA3NSFormula :=
    ⟨1, [2, 3, 4, 5], [[[1, 2, 4], [3, 4]], [[1, 3], [2, 5], [1, 4, 5]]]⟩
  refine ⟨F, ?_, ?_⟩
  · refine ⟨{2, 5}, ?_, by decide⟩
    rw [← WA3NSFormula.indicator_eq_true_iff]
    decide
  · rintro ⟨A, hA, hcard⟩
    have hfalse : ∀ S ∈ F.varSet.powersetCard 3, F.indicator S = false := by decide
    have hmem : A ∈ F.varSet.powersetCard 3 := Finset.mem_powersetCard.2 ⟨hA.1, hcard⟩
    have htrue : F.indicator A = true := (WA3NSFormula.indicator_eq_true_iff F A).2 hA
    rw [hfalse A hmem] at htrue; exact Bool.false_ne_true htrue
end Witnesses
end CslibFrontier.ParameterizedComplexity
