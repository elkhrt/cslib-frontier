/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.EUThreeSAT
public import CslibFrontier.Logics.Propositional.CNF.ThreeOccurrence
import CslibFrontier.Computability.Complexity.NatCodec
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ThreeOccurrence.PolyTime
import Mathlib.Tactic.FinCases

/-!
# Bounded-Occurrence `(2/3, B2)`-SAT (`TwoClauseThreeSAT`) and `NP`-Completeness

This module formalizes bounded-occurrence 3-SAT in which every clause has `2` or `3` literals (or
at most `3` literals) on pairwise distinct variables and every occurring variable appears in
exactly `2` clauses positively and `2` clauses negatively (`TwoClauseThreeSAT`,
`AtMostThreeTwoClauseSAT`), and proves `NP`-completeness of both problems under
`Cslib.Complexity.encCNF` using standard Lean axioms.

Starting from an exact-3 distinct-variable formula `φ` (`EUThreeSAT`), the reduction first doubles
`φ` to `ψ = φ ++ φ` so every occurring variable appears at least twice, applies Tovey/Papadimitriou
occurrence splitting (`CNF.toThreeOccurrence`) so each split copy `x` appears in distinct-variable
clauses of length `2` or `3` with `2` occurrences of its clause polarity `b` and `1` occurrence of
the opposite polarity `!b`, and attaches a 7-clause padding gadget over 5 fresh auxiliary variables
supplying the single missing occurrence of `(x, !b)` while giving each auxiliary variable exactly
`2` positive and `2` negative occurrences.

## Main definitions

- `CslibFrontier.Complexity.litClauseCount`: number of clauses in `φ` containing literal `(v, b)`.
- `CslibFrontier.Complexity.IsAtMostThreeTwoClause`: distinct-variable width-`≤ 3` CNF formulas in
  which every occurring variable appears in `2` clauses positively and `2` clauses negatively.
- `CslibFrontier.Complexity.IsTwoClauseThree`: strengthens `IsAtMostThreeTwoClause` by requiring
  every clause to have length `2` or `3`.
- `CslibFrontier.Complexity.TwoClauseThreeSAT`, `CslibFrontier.Complexity.AtMostThreeTwoClauseSAT`:
  corresponding decision languages over `CNF ℕ`.
- `CslibFrontier.Complexity.twoOccPaddingGadget`: the 7-clause ternary padding gadget adding one
  occurrence of `(x, b)` and balanced `(2, 2)` occurrences on 5 fresh auxiliary variables.
- `CslibFrontier.Complexity.toTwoClauseThreeSAT`: polynomial-time many-one reduction from
  `EUThreeSAT` to `TwoClauseThreeSAT` (and `AtMostThreeTwoClauseSAT`).

## Main results

- `CslibFrontier.Complexity.twoClauseThreeSAT_mem_NP`,
  `CslibFrontier.Complexity.atMostThreeTwoClauseSAT_mem_NP`: `NP`-membership of both languages.
- `CslibFrontier.Complexity.mem_twoClauseThreeSAT_toTwoClauseThreeSAT_iff`,
  `CslibFrontier.Complexity.mem_atMostThreeTwoClauseSAT_toTwoClauseThreeSAT_iff`: total correctness
  of `toTwoClauseThreeSAT`.
- `CslibFrontier.Complexity.computableInPolyTime_toTwoClauseThreeSAT`: `toTwoClauseThreeSAT` runs in
  polynomial time under `encCNF`.
- `CslibFrontier.Complexity.twoClauseThreeSAT_npHard`,
  `CslibFrontier.Complexity.twoClauseThreeSAT_npComplete`,
  `CslibFrontier.Complexity.atMostThreeTwoClauseSAT_npHard`,
  `CslibFrontier.Complexity.atMostThreeTwoClauseSAT_npComplete`: `NP`-completeness of both
  languages.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Balanced `(2, 2)`-occurrence 3-SAT predicates and languages -/

/-- Number of clauses in `φ : CNF V` containing the signed literal `(v, b)`. -/
@[expose] def litClauseCount {V : Type*} [DecidableEq V] (φ : CNF V) (v : V) (b : Bool) : ℕ :=
  φ.countP fun c ↦ decide ((v, b) ∈ c)

/-- Invariance of `litClauseCount` under injective variable relabeling. -/
theorem litClauseCount_relabel {U V : Type*} [DecidableEq U] [DecidableEq V] {f : U → V}
    (hf : Function.Injective f) (φ : CNF U) (u : U) (b : Bool) :
    litClauseCount (φ.relabel f) (f u) b = litClauseCount φ u b := by
  simp only [litClauseCount, CNF.relabel, List.countP_map]
  refine List.countP_congr fun c _ ↦ ?_
  simp only [Function.comp_apply, decide_eq_true_eq, Clause.relabel, List.mem_map]
  exact ⟨fun ⟨⟨u', b'⟩, hmem, heq⟩ ↦ by
    obtain ⟨hfu, hb⟩ := Prod.mk.inj heq
    exact hb ▸ hf hfu ▸ hmem, fun hmem ↦ ⟨(u, b), hmem, rfl⟩⟩

/-- Predicate asserting that every clause of `φ` has at most `3` literals with pairwise distinct
variables, and every variable occurring in `φ` appears in `2` clauses positively and `2` clauses
negatively. -/
def IsAtMostThreeTwoClause {V : Type*} [DecidableEq V] (φ : CNF V) : Prop :=
  (∀ c ∈ φ, c.length ≤ 3 ∧ (c.map Prod.fst).Nodup) ∧
    ∀ v ∈ φ.vars, ∀ b : Bool, litClauseCount φ v b = 2

/-- Standard `(2/3, B2)`-SAT predicate: every clause of `φ` has `2` or `3` literals on pairwise
distinct variables, and every variable occurring in `φ` appears in `2` clauses positively and `2`
clauses negatively. -/
@[expose] def IsTwoClauseThree {V : Type*} [DecidableEq V] (φ : CNF V) : Prop :=
  (∀ c ∈ φ, 2 ≤ c.length ∧ c.length ≤ 3 ∧ (c.map Prod.fst).Nodup) ∧
    ∀ v ∈ φ.vars, ∀ b : Bool, litClauseCount φ v b = 2

/-- Every `IsTwoClauseThree` formula satisfies `IsAtMostThreeTwoClause`. -/
theorem IsTwoClauseThree.isAtMostThreeTwoClause {V : Type*} [DecidableEq V] {φ : CNF V}
    (h : IsTwoClauseThree φ) : IsAtMostThreeTwoClause φ :=
  ⟨fun c hc ↦ (h.1 c hc).2, h.2⟩

/-- Injectively relabeling variables preserves `IsTwoClauseThree`. -/
theorem IsTwoClauseThree.relabel {U V : Type*} [DecidableEq U] [DecidableEq V] {f : U → V}
    (hf : Function.Injective f) {φ : CNF U} (h : IsTwoClauseThree φ) :
    IsTwoClauseThree (φ.relabel f) := by
  refine ⟨fun c hc ↦ ?_, fun v hv b ↦ ?_⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨h2, h3, hnd⟩ := h.1 d hd
    refine ⟨by simpa [Clause.relabel] using h2, by simpa [Clause.relabel] using h3, ?_⟩
    have hmap : (d.relabel f).map Prod.fst = (d.map Prod.fst).map f := by
      simp [Clause.relabel, List.map_map, Function.comp_def]
    exact hmap ▸ hnd.map hf
  · rw [CNF.vars_relabel] at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    rw [litClauseCount_relabel hf]
    exact h.2 u hu b

/-- The `(2/3, B2)`-SAT language: satisfiable CNF formulas over `ℕ` with `2` or `3` distinct
variables per clause and `2` positive plus `2` negative clause occurrences per occurring
variable. -/
@[expose] def TwoClauseThreeSAT : Set (CNF ℕ) :=
  {φ | IsTwoClauseThree φ ∧ φ.Satisfiable}

/-- The width-`≤ 3` balanced `(2, 2)`-occurrence SAT language: satisfiable CNF formulas over `ℕ`
with at most `3` distinct variables per clause and `2` positive plus `2` negative clause
occurrences per occurring variable. -/
def AtMostThreeTwoClauseSAT : Set (CNF ℕ) :=
  {φ | IsAtMostThreeTwoClause φ ∧ φ.Satisfiable}

/-- Every member of `TwoClauseThreeSAT` lies in `AtMostThreeTwoClauseSAT`. -/
theorem twoClauseThreeSAT_subset_atMostThreeTwoClauseSAT :
    TwoClauseThreeSAT ⊆ AtMostThreeTwoClauseSAT :=
  fun _ ⟨hs, hsat⟩ ↦ ⟨hs.isAtMostThreeTwoClause, hsat⟩

/-! ### Executable syntax checks and `NP`-membership -/

private def nodupVarsBool (c : Clause ℕ) : Bool :=
  let vs := c.map Prod.fst
  vs.zipIdx.all fun e ↦ decide (vs.idxOf e.1 = e.2)

private theorem nodupVarsBool_iff (c : Clause ℕ) :
    nodupVarsBool c = true ↔ (c.map Prod.fst).Nodup := by
  simp only [nodupVarsBool, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun h ↦ List.nodup_iff_injective_get.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ ?_,
    fun hnd e he ↦ ?_⟩
  · simp only [List.get_eq_getElem] at hij
    have hi' : (c.map Prod.fst).idxOf (c.map Prod.fst)[i] = i :=
      h ((c.map Prod.fst)[i], i) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))
    have hj' : (c.map Prod.fst).idxOf (c.map Prod.fst)[j] = j :=
      h ((c.map Prod.fst)[j], j) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hj))
    exact Fin.ext ((hij ▸ hi').symm.trans hj')
  · obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
    rw [← heq]
    exact hnd.idxOf_getElem e.2 hlt

private def atMostThreeTwoClauseCheck (φ : CNF ℕ) : Bool :=
  (φ.all fun c ↦ decide (c.length ≤ 3) && nodupVarsBool c) &&
    φ.vars.all fun v ↦
      decide ((φ.countP fun c ↦ c.any fun l ↦ decide (l = (v, false))) = 2) &&
      decide ((φ.countP fun c ↦ c.any fun l ↦ decide (l = (v, true))) = 2)

private def twoClauseThreeCheck (φ : CNF ℕ) : Bool :=
  (φ.all fun c ↦ decide (2 ≤ c.length) && decide (c.length ≤ 3) && nodupVarsBool c) &&
    φ.vars.all fun v ↦
      decide ((φ.countP fun c ↦ c.any fun l ↦ decide (l = (v, false))) = 2) &&
      decide ((φ.countP fun c ↦ c.any fun l ↦ decide (l = (v, true))) = 2)

private theorem countP_any_eq_litClauseCount (φ : CNF ℕ) (v : ℕ) (b : Bool) :
    (φ.countP fun c ↦ c.any fun l ↦ decide (l = (v, b))) = litClauseCount φ v b :=
  List.countP_congr fun c _ ↦ by simp

private theorem atMostThreeTwoClauseCheck_iff (φ : CNF ℕ) :
    atMostThreeTwoClauseCheck φ = true ↔ IsAtMostThreeTwoClause φ := by
  simp only [atMostThreeTwoClauseCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    nodupVarsBool_iff, countP_any_eq_litClauseCount, IsAtMostThreeTwoClause, Bool.forall_bool]

private theorem twoClauseThreeCheck_iff (φ : CNF ℕ) :
    twoClauseThreeCheck φ = true ↔ IsTwoClauseThree φ := by
  simp only [twoClauseThreeCheck, Bool.and_eq_true, and_assoc, List.all_eq_true, decide_eq_true_eq,
    nodupVarsBool_iff, countP_any_eq_litClauseCount, IsTwoClauseThree, Bool.forall_bool]

private theorem computableInPolyTime_atMostThreeTwoClauseCheck :
    ComputableInPolyTime atMostThreeTwoClauseCheck encCNF encBool := by
  have hnd : ComputableInPolyTime nodupVarsBool (encList (encPair encNat encBool)) encBool := by
    unfold nodupVarsBool; fun_prop
  unfold atMostThreeTwoClauseCheck encCNF
  fun_prop

private theorem computableInPolyTime_twoClauseThreeCheck :
    ComputableInPolyTime twoClauseThreeCheck encCNF encBool := by
  have hnd : ComputableInPolyTime nodupVarsBool (encList (encPair encNat encBool)) encBool := by
    unfold nodupVarsBool; fun_prop
  unfold twoClauseThreeCheck encCNF
  fun_prop

/-- `AtMostThreeTwoClauseSAT` belongs to `NP encCNF`. -/
theorem atMostThreeTwoClauseSAT_mem_NP : AtMostThreeTwoClauseSAT ∈ NP encCNF := by
  let ver : CNF ℕ × List Bool → Bool := fun x ↦ atMostThreeTwoClauseCheck x.1 && SAT.verifier x
  have hset : AtMostThreeTwoClauseSAT = {φ | atMostThreeTwoClauseCheck φ = true ∧ φ ∈ SAT} :=
    Set.ext fun φ ↦ by
      simp only [AtMostThreeTwoClauseSAT, Set.mem_ofPred_eq, atMostThreeTwoClauseCheck_iff, mem_SAT]
  have hpoly : ComputableInPolyTime ver (encPair encCNF encBits) encBool :=
    ComputableInPolyTime.bool_and'
      (computableInPolyTime_atMostThreeTwoClauseCheck.comp (ComputableInPolyTime.fst _ _))
      SAT.computableInPolyTime_verifier
  exact ⟨Polynomial.X, ver, hpoly, hset ▸ SAT.isVerifier.guard⟩

/-- `TwoClauseThreeSAT` belongs to `NP encCNF`. -/
theorem twoClauseThreeSAT_mem_NP : TwoClauseThreeSAT ∈ NP encCNF := by
  let ver : CNF ℕ × List Bool → Bool := fun x ↦ twoClauseThreeCheck x.1 && SAT.verifier x
  have hset : TwoClauseThreeSAT = {φ | twoClauseThreeCheck φ = true ∧ φ ∈ SAT} :=
    Set.ext fun φ ↦ by
      simp only [TwoClauseThreeSAT, Set.mem_ofPred_eq, twoClauseThreeCheck_iff, mem_SAT]
  have hpoly : ComputableInPolyTime ver (encPair encCNF encBits) encBool :=
    ComputableInPolyTime.bool_and'
      (computableInPolyTime_twoClauseThreeCheck.comp (ComputableInPolyTime.fst _ _))
      SAT.computableInPolyTime_verifier
  exact ⟨Polynomial.X, ver, hpoly, hset ▸ SAT.isVerifier.guard⟩

/-! ### The 7-clause `(2, 2)`-occurrence padding gadget -/

/-- The 7-clause ternary padding gadget for a split variable `x : W` and missing polarity `b`:
using variables `(x, 0)` for `x` and `(x, 1), …, (x, 5)` for the 5 fresh auxiliary variables
`y₁, …, y₅`, it contributes `1` occurrence of `((x, 0), b)`, `0` occurrences of `((x, 0), !b)`,
and `2` positive plus `2` negative occurrences of each `y₁, …, y₅`, and is always satisfied by
setting `y₁ = ⋯ = y₅ = true`. -/
def twoOccPaddingGadget {W : Type*} (x : W) (b : Bool) : CNF (W × ℕ) :=
  let x₀ := (x, 0)
  let y₁ := (x, 1)
  let y₂ := (x, 2)
  let y₃ := (x, 3)
  let y₄ := (x, 4)
  let y₅ := (x, 5)
  [ [(x₀, b), (y₁, true), (y₂, false)],
    [(y₁, true), (y₃, true), (y₄, false)],
    [(y₁, false), (y₃, true), (y₄, false)],
    [(y₁, false), (y₄, true), (y₅, false)],
    [(y₂, true), (y₄, true), (y₅, false)],
    [(y₂, true), (y₃, false), (y₅, true)],
    [(y₂, false), (y₃, false), (y₅, true)] ]

private def modelGadget (b : Bool) : CNF (Fin 6) :=
  [ [(0, b), (1, true), (2, false)],
    [(1, true), (3, true), (4, false)],
    [(1, false), (3, true), (4, false)],
    [(1, false), (4, true), (5, false)],
    [(2, true), (4, true), (5, false)],
    [(2, true), (3, false), (5, true)],
    [(2, false), (3, false), (5, true)] ]

private theorem twoOccPaddingGadget_eq_relabel {W : Type*} (x : W) (b : Bool) :
    twoOccPaddingGadget x b = (modelGadget b).relabel fun i : Fin 6 ↦ (x, i.1) :=
  rfl

private theorem modelGadget_clauses (b : Bool) :
    ∀ c ∈ modelGadget b, c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  cases b <;> decide

private theorem modelGadget_count_zero (b pol : Bool) :
    litClauseCount (modelGadget b) 0 pol = if pol = b then 1 else 0 := by
  cases b <;> cases pol <;> decide

private theorem modelGadget_count_succ (b : Bool) (a : Fin 5) (pol : Bool) :
    litClauseCount (modelGadget b) a.succ pol = 2 := by
  cases b <;> fin_cases a <;> cases pol <;> decide

private theorem modelGadget_eval_true (b x₀ : Bool) :
    (modelGadget b).eval (fun i : Fin 6 ↦ if i = 0 then x₀ else true) = true := by
  cases b <;> cases x₀ <;> decide

private theorem twoOccPaddingGadget_clauses {W : Type*} (x : W) (b : Bool) {c : Clause (W × ℕ)}
    (hc : c ∈ twoOccPaddingGadget x b) : 2 ≤ c.length ∧ c.length ≤ 3 ∧ (c.map Prod.fst).Nodup := by
  rw [twoOccPaddingGadget_eq_relabel] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hlen, hnd⟩ := modelGadget_clauses b d hd
  have hinj : Function.Injective (fun i : Fin 6 ↦ (x, i.1)) :=
    fun _ _ h ↦ Fin.ext (Prod.mk.inj h).2
  have hmap : (d.relabel fun i : Fin 6 ↦ (x, i.1)).map Prod.fst =
      (d.map Prod.fst).map fun i : Fin 6 ↦ (x, i.1) := by
    simp [Clause.relabel, List.map_map, Function.comp_def]
  exact ⟨by simp [Clause.relabel, hlen], by simp [Clause.relabel, hlen], hmap ▸ hnd.map hinj⟩

private theorem litClauseCount_twoOccPaddingGadget {W : Type*} [DecidableEq W] (x y : W)
    (k : ℕ) (b pol : Bool) :
    litClauseCount (twoOccPaddingGadget x b) (y, k) pol =
      if y = x then
        if k = 0 then (if pol = b then 1 else 0)
        else if k < 6 then 2 else 0
      else 0 := by
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    by_cases hk6 : k < 6
    · have hinj : Function.Injective (fun i : Fin 6 ↦ (y, i.1)) :=
        fun _ _ h ↦ Fin.ext (Prod.mk.inj h).2
      have harg : (y, k) = (fun i : Fin 6 ↦ (y, i.1)) ⟨k, hk6⟩ := rfl
      rw [twoOccPaddingGadget_eq_relabel, harg, litClauseCount_relabel hinj]
      rcases k with _ | k'
      · simp [modelGadget_count_zero]
      · have hk5 : k' < 5 := by omega
        simp only [Nat.succ_ne_zero, ↓reduceIte, hk6]
        exact modelGadget_count_succ b ⟨k', hk5⟩ pol
    · simp only [show k ≠ 0 by omega, hk6, ↓reduceIte, litClauseCount, List.countP_eq_zero,
        decide_eq_true_eq]
      intro c hc hl
      rw [twoOccPaddingGadget_eq_relabel] at hc
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
      obtain ⟨⟨i, _⟩, -, heq⟩ := List.mem_map.mp hl
      exact hk6 ((Prod.mk.inj (Prod.mk.inj heq).1).2 ▸ i.2)
  · simp only [hyx, ↓reduceIte, litClauseCount, List.countP_eq_zero, decide_eq_true_eq]
    intro c hc hl
    rw [twoOccPaddingGadget_eq_relabel] at hc
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
    obtain ⟨⟨i, _⟩, -, heq⟩ := List.mem_map.mp hl
    exact hyx (Prod.mk.inj (Prod.mk.inj heq).1).1.symm

private theorem eval_twoOccPaddingGadget_of_aux_true {W : Type*} (x : W) (b : Bool)
    (τ : W × ℕ → Bool) (haux : ∀ k, 1 ≤ k → k < 6 → τ (x, k) = true) :
    (twoOccPaddingGadget x b).eval τ = true := by
  rw [twoOccPaddingGadget_eq_relabel, CNF.eval_relabel]
  have hfun : (τ ∘ fun i : Fin 6 ↦ (x, i.1)) =
      fun i : Fin 6 ↦ if i = 0 then τ (x, 0) else true := by
    funext i
    fin_cases i
    · rfl
    all_goals exact haux _ (by decide) (by decide)
  rw [hfun]
  exact modelGadget_eval_true b (τ (x, 0))

/-! ### Occurrence-splitting + padding reduction from `EUThreeSAT` -/

private lemma countP_flatMap_eq_sum {α β : Type*} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).countP p = (l.map fun a ↦ (f a).countP p).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.countP_append, ih]

private lemma nodup_implicationPath {V : Type*} {first : V} :
    ∀ {cur : V} {rest : List V}, (cur :: rest).Nodup → first ∉ rest →
      (rest = [] → cur ≠ first) →
      ∀ c ∈ CNF.implicationPath first cur rest, (c.map Prod.fst).Nodup
  | cur, [], _, _, hne, _, hc => by
    obtain rfl := List.mem_singleton.mp hc
    simp [hne]
  | cur, next :: rest, hnd, hfirst, _, c, hc => by
    rw [List.nodup_cons] at hnd
    have hfirst_ne_next : next ≠ first := fun h ↦ hfirst (h ▸ List.mem_cons_self)
    have hfirst_rest : first ∉ rest := fun h ↦ hfirst (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp hc with rfl | hc
    · have hcn : cur ≠ next := fun h ↦ hnd.1 (h ▸ List.mem_cons_self)
      simp [hcn]
    · exact nodup_implicationPath hnd.2 hfirst_rest (fun _ ↦ hfirst_ne_next) c hc

private lemma nodup_implicationCycle {V : Type*} {vs : List V} (hnd : vs.Nodup)
    (hlen : 2 ≤ vs.length) {c : Clause V} (hc : c ∈ CNF.implicationCycle vs) :
    (c.map Prod.fst).Nodup := by
  rcases vs with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · simp at hlen
  · simp at hlen
  · have hf : first ∉ second :: rest := (List.nodup_cons.mp hnd).1
    exact nodup_implicationPath hnd hf (by simp) c hc

private lemma litClauseCount_implicationPath {V : Type*} [DecidableEq V] (first : V) :
    ∀ (cur : V) (rest : List V) (v : V) (b : Bool),
      litClauseCount (CNF.implicationPath first cur rest) v b =
        (if b = false then (if cur = v then 1 else 0) + rest.count v
         else (if first = v then 1 else 0) + rest.count v)
  | cur, [], v, false => by simp [CNF.implicationPath, litClauseCount, eq_comm]
  | cur, [], v, true => by simp [CNF.implicationPath, litClauseCount, eq_comm]
  | cur, next :: rest, v, false => by
    rw [CNF.implicationPath, litClauseCount, List.countP_cons]
    change litClauseCount (CNF.implicationPath first next rest) v false +
      (if decide ((v, false) ∈ [(cur, false), (next, true)]) then 1 else 0) = _
    rw [litClauseCount_implicationPath first next rest v false]
    simp only [List.count_cons, beq_iff_eq, ↓reduceIte]
    have hhd : decide ((v, false) ∈ [(cur, false), (next, true)]) = decide (v = cur) := by
      by_cases h : v = cur <;> simp [h]
    rw [hhd]
    by_cases hc : cur = v <;> by_cases hn : next = v <;> simp [hc, hn, eq_comm] <;> omega
  | cur, next :: rest, v, true => by
    rw [CNF.implicationPath, litClauseCount, List.countP_cons]
    change litClauseCount (CNF.implicationPath first next rest) v true +
      (if decide ((v, true) ∈ [(cur, false), (next, true)]) then 1 else 0) = _
    rw [litClauseCount_implicationPath first next rest v true]
    simp only [List.count_cons, beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
    have hhd : decide ((v, true) ∈ [(cur, false), (next, true)]) = decide (v = next) := by
      by_cases h : v = next <;> simp [h]
    rw [hhd]
    by_cases hf : first = v <;> by_cases hn : next = v
    · simp [hf, hn]; omega
    · simp [hf, hn, Ne.symm hn]
    · simp [hf, hn]
    · simp [hf, hn, Ne.symm hn]

private lemma litClauseCount_implicationCycle {V : Type*} [DecidableEq V] {vs : List V}
    (hnd : vs.Nodup) (v : V) (b : Bool) :
    litClauseCount (CNF.implicationCycle vs) v b = if v ∈ vs then 1 else 0 := by
  rcases vs with _ | ⟨first, rest⟩
  · simp [CNF.implicationCycle, litClauseCount]
  · rw [CNF.implicationCycle, litClauseCount_implicationPath]
    rw [List.nodup_cons] at hnd
    have hcnt : rest.count v = if v ∈ rest then 1 else 0 := by
      by_cases hvr : v ∈ rest
      · simp [hvr, Nat.le_antisymm ((List.nodup_iff_count_le_one.mp hnd.2) v)
          (List.count_pos_iff.mpr hvr)]
      · simp [hvr, List.count_eq_zero.mpr hvr]
    by_cases hfv : v = first
    · subst hfv
      cases b <;> simp [hcnt, hnd.1]
    · have hfv' : first ≠ v := Ne.symm hfv
      cases b <;> by_cases hvr : v ∈ rest <;> simp [hcnt, hfv, hfv', hvr]

private def rawTwoClauseThree (φ : CNF ℕ) : CNF ((ℕ × ℕ × ℕ) × ℕ) :=
  let ψ : CNF ℕ := φ ++ φ
  let base : CNF ((ℕ × ℕ × ℕ) × ℕ) := ψ.toThreeOccurrence.relabel fun x ↦ (x, 0)
  let pads : CNF ((ℕ × ℕ × ℕ) × ℕ) :=
    ψ.occurrenceClauses.flatten.flatMap fun l ↦ twoOccPaddingGadget l.1 (!l.2)
  base ++ pads

private theorem isTwoClauseThree_rawTwoClauseThree {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) :
    IsTwoClauseThree (rawTwoClauseThree φ) := by
  set ψ : CNF ℕ := φ ++ φ
  have hψ : ψ.IsExactThreeDistinct := fun c hc ↦
    (List.mem_append.mp hc).elim (hφ c) (hφ c)
  have hcopies_nd (v : ℕ) : (ψ.occurrenceCopies v).Nodup :=
    (CNF.nodup_vars_occurrenceClauses ψ).filter _
  have hcopies_len {v : ℕ} (hv : v ∈ ψ.distinctVars) : 2 ≤ (ψ.occurrenceCopies v).length := by
    rw [CNF.length_occurrenceCopies]
    have hvψ : v ∈ ψ.vars := (CNF.mem_distinctVars (φ := ψ) (v := v)).mp hv
    have hvars : ψ.vars = φ.vars ++ φ.vars := by
      simp [ψ, CNF.vars, List.flatten_append, List.map_append]
    rw [hvars, List.mem_append, or_self] at hvψ
    have hpos : 1 ≤ φ.vars.count v := List.count_pos_iff.mpr hvψ
    rw [hvars, List.count_append]
    omega
  have hinj0 : Function.Injective (fun x : ℕ × ℕ × ℕ ↦ (x, (0 : ℕ))) :=
    fun _ _ h ↦ (Prod.mk.inj h).1
  -- Part 1: Every clause has length in {2, 3} and distinct variables
  refine ⟨fun c hc ↦ ?_, fun u hu pol ↦ ?_⟩
  · rcases List.mem_append.mp hc with hcBase | hcPad
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hcBase
      have hmap : (d.relabel fun x : ℕ × ℕ × ℕ ↦ (x, 0)).map Prod.fst =
          (d.map Prod.fst).map fun x ↦ (x, 0) := by
        simp [Clause.relabel, List.map_map, Function.comp_def]
      rcases List.mem_append.mp hd with hdOcc | hdCyc
      · obtain ⟨⟨e, idx⟩, he, rfl⟩ := List.mem_map.mp hdOcc
        have he3 := hψ e (List.fst_mem_of_mem_zipIdx he)
        have hlen : (e.zipIdx.map fun l ↦ ((l.1.1, idx, l.2), l.1.2)).length = 3 := by
          simp [he3.1]
        have hnd : ((e.zipIdx.map fun l ↦ ((l.1.1, idx, l.2), l.1.2)).map Prod.fst).Nodup := by
          apply List.Nodup.of_map (f := fun x : ℕ × ℕ × ℕ ↦ x.2.2)
          have hrange : (((e.zipIdx.map fun l ↦ ((l.1.1, idx, l.2), l.1.2)).map Prod.fst).map
              fun x : ℕ × ℕ × ℕ ↦ x.2.2) = List.range e.length :=
            List.ext_getElem (by simp) fun i h1 _ ↦ by simp
          rw [hrange]
          exact List.nodup_range
        exact ⟨by simp [Clause.relabel, he3.1], by simp [Clause.relabel, he3.1],
          hmap ▸ hnd.map hinj0⟩
      · obtain ⟨v, hv, hdCyc⟩ := List.mem_flatMap.mp hdCyc
        have hlen := CNF.length_of_mem_implicationCycle _ hdCyc
        have hnd := nodup_implicationCycle (hcopies_nd v) (hcopies_len hv) hdCyc
        exact ⟨by simp [Clause.relabel, hlen], by simp [Clause.relabel, hlen],
          hmap ▸ hnd.map hinj0⟩
    · obtain ⟨l, -, hcPad⟩ := List.mem_flatMap.mp hcPad
      exact twoOccPaddingGadget_clauses l.1 (!l.2) hcPad
  -- Part 2: Every occurring variable `(x, k)` appears in exactly 2 clauses of each polarity
  · rcases u with ⟨x, k⟩
    have hvars_flat : ∀ {α : Type} (χ : CNF α), CNF.vars χ = χ.flatten.map Prod.fst := by
      intro α χ
      induction χ with
      | nil => rfl
      | cons c cs ih =>
        rw [List.flatten_cons, List.map_append, ← ih]
        simp [CNF.vars]
    have hx_occ : x ∈ ψ.occurrenceClauses.vars ∧ k < 6 := by
      have hvars_app : (rawTwoClauseThree φ).vars =
          CNF.vars (ψ.toThreeOccurrence.relabel fun x ↦ (x, 0)) ++
          CNF.vars (ψ.occurrenceClauses.flatten.flatMap
            fun l ↦ twoOccPaddingGadget l.1 (!l.2)) := by
        rw [hvars_flat, hvars_flat, hvars_flat]
        simp only [rawTwoClauseThree, ψ, List.flatten_append, List.map_append]
      rw [hvars_app, List.mem_append] at hu
      rcases hu with huB | huP
      · rw [CNF.vars_relabel] at huB
        obtain ⟨x', hx', heq⟩ := List.mem_map.mp huB
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        have hcnt : 0 < ψ.toThreeOccurrence.vars.count x' := List.count_pos_iff.mpr hx'
        rw [CNF.count_vars_toThreeOccurrence] at hcnt
        exact ⟨List.count_pos_iff.mp (by omega), by omega⟩
      · rw [hvars_flat, List.mem_map] at huP
        obtain ⟨⟨⟨x', k'⟩, _⟩, hl, heq⟩ := huP
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [List.mem_flatten] at hl
        obtain ⟨c, hc, hlc⟩ := hl
        obtain ⟨l₀, hl₀, hc⟩ := List.mem_flatMap.mp hc
        rw [twoOccPaddingGadget_eq_relabel] at hc
        obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
        obtain ⟨⟨i, _⟩, -, heq'⟩ := List.mem_map.mp hlc
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq').1
        exact ⟨hvars_flat ψ.occurrenceClauses ▸ List.mem_map_of_mem hl₀, i.2⟩
    obtain ⟨hx_mem, hk6⟩ := hx_occ
    -- Extract the unique literal `(x, b₀) ∈ ψ.occurrenceClauses.flatten`
    have hvars_def : ψ.occurrenceClauses.vars = ψ.occurrenceClauses.flatten.map Prod.fst :=
      hvars_flat ψ.occurrenceClauses
    obtain ⟨⟨x', b₀⟩, hlb₀, hxeq⟩ := List.mem_map.mp (hvars_def ▸ hx_mem)
    dsimp only at hxeq
    subst hxeq
    have hnd_occ := CNF.nodup_vars_occurrenceClauses ψ
    have huniq_lit : ∀ l ∈ ψ.occurrenceClauses.flatten, l.1 = x' → l = (x', b₀) := by
      intro ⟨y, b'⟩ hly hy
      dsimp only at hy
      subst hy
      have hnd_flat : (ψ.occurrenceClauses.flatten.map Prod.fst).Nodup := hvars_def ▸ hnd_occ
      obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem hly
      obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem hlb₀
      have hinj_get := List.nodup_iff_injective_getElem.mp hnd_flat
      have hlen_m : (ψ.occurrenceClauses.flatten.map Prod.fst).length =
          ψ.occurrenceClauses.flatten.length := List.length_map _
      have hij : (⟨i, hlen_m ▸ hi⟩ : Fin (ψ.occurrenceClauses.flatten.map Prod.fst).length) =
          ⟨j, hlen_m ▸ hj⟩ := by
        apply hinj_get
        simp only [List.getElem_map, hi_eq, hj_eq]
      have hval : i = j := congrArg Fin.val hij
      subst hval
      exact hi_eq.symm.trans hj_eq
    -- Split `litClauseCount` across `base` and `pads`
    have hsplit : litClauseCount (rawTwoClauseThree φ) (x', k) pol =
        litClauseCount (ψ.toThreeOccurrence.relabel fun z ↦ (z, 0)) (x', k) pol +
        litClauseCount (ψ.occurrenceClauses.flatten.flatMap fun l ↦
          twoOccPaddingGadget l.1 (!l.2)) (x', k) pol := by
      simp [rawTwoClauseThree, ψ, litClauseCount, List.countP_append]
    rw [hsplit]
    -- Count in `pads`
    have hpads : litClauseCount (ψ.occurrenceClauses.flatten.flatMap fun l ↦
        twoOccPaddingGadget l.1 (!l.2)) (x', k) pol =
        if k = 0 then (if pol = !b₀ then 1 else 0) else 2 := by
      have hsum_eq : litClauseCount (ψ.occurrenceClauses.flatten.flatMap fun l ↦
          twoOccPaddingGadget l.1 (!l.2)) (x', k) pol =
          (ψ.occurrenceClauses.flatten.map fun l ↦
            litClauseCount (twoOccPaddingGadget l.1 (!l.2)) (x', k) pol).sum :=
        countP_flatMap_eq_sum _ _ _
      rw [hsum_eq]
      have hsum := List.sum_map_eq_nsmul_single (x', b₀)
        (l := ψ.occurrenceClauses.flatten)
        (f := fun l : Literal (ℕ × ℕ × ℕ) ↦
          litClauseCount (twoOccPaddingGadget l.1 (!l.2)) (x', k) pol)
        fun l hne hl ↦ by
          have hfx : x' ≠ l.1 := fun h ↦ hne (huniq_lit l hl h.symm)
          simp [litClauseCount_twoOccPaddingGadget, hfx]
      have hnd_f : ψ.occurrenceClauses.flatten.Nodup := (hvars_def ▸ hnd_occ).of_map Prod.fst
      have hcnt1 : ψ.occurrenceClauses.flatten.count (x', b₀) = 1 :=
        Nat.le_antisymm ((List.nodup_iff_count_le_one.mp hnd_f) (x', b₀))
          (List.count_pos_iff.mpr hlb₀)
      rw [hsum, hcnt1, one_smul, litClauseCount_twoOccPaddingGadget]
      simp [hk6]
    rw [hpads]
    rcases k with _ | k'
    · -- `k = 0`: count in `base` = count in `occurrenceClauses` + count in `implicationCycles`
      rw [litClauseCount_relabel hinj0]
      have hbase_split : litClauseCount ψ.toThreeOccurrence x' pol =
          litClauseCount ψ.occurrenceClauses x' pol +
          litClauseCount (ψ.distinctVars.flatMap fun v ↦
            CNF.implicationCycle (ψ.occurrenceCopies v)) x' pol := by
        simp [CNF.toThreeOccurrence, litClauseCount, List.countP_append]
      have hocc_cnt : litClauseCount ψ.occurrenceClauses x' pol =
          if pol = b₀ then 1 else 0 := by
        obtain ⟨c₀, hc₀, hlc₀⟩ := List.mem_flatten.mp hlb₀
        by_cases hpb : pol = b₀
        · subst hpb
          simp only [↓reduceIte]
          have hge : 1 ≤ litClauseCount ψ.occurrenceClauses x' pol := by
            obtain ⟨l₁, l₂, hdecomp⟩ := List.append_of_mem hc₀
            rw [litClauseCount, hdecomp, List.countP_append, List.countP_cons]
            simp only [decide_eq_true_eq, hlc₀, ↓reduceIte]
            omega
          have hle : litClauseCount ψ.occurrenceClauses x' pol ≤
              ψ.occurrenceClauses.vars.count x' := by
            clear hge hlc₀ hc₀ huniq_lit hlb₀ hx_mem
            induction ψ.occurrenceClauses with
            | nil => simp [litClauseCount, CNF.vars]
            | cons c cs ih =>
              have hvc : CNF.vars (c :: cs) = c.map Prod.fst ++ CNF.vars cs := by
                simp [CNF.vars]
              rw [hvc, List.count_append]
              simp only [litClauseCount, List.countP_cons, decide_eq_true_eq] at ih ⊢
              by_cases hm : (x', pol) ∈ c
              · have hcpos : 1 ≤ (c.map Prod.fst).count x' :=
                  List.count_pos_iff.mpr (List.mem_map_of_mem hm)
                simp only [hm, ↓reduceIte]
                omega
              · simp only [hm, ↓reduceIte]
                omega
          have h1 := (List.nodup_iff_count_le_one.mp hnd_occ) x'
          omega
        · simp only [hpb, ↓reduceIte, litClauseCount, List.countP_eq_zero, decide_eq_true_eq]
          intro c hc hmem
          have heq := huniq_lit (x', pol) (List.mem_flatten.mpr ⟨c, hc, hmem⟩) rfl
          exact hpb (Prod.mk.inj heq).2
      have hcyc_cnt : litClauseCount (ψ.distinctVars.flatMap fun v ↦
          CNF.implicationCycle (ψ.occurrenceCopies v)) x' pol = 1 := by
        simp only [litClauseCount, countP_flatMap_eq_sum]
        change (ψ.distinctVars.map fun v ↦
          litClauseCount (CNF.implicationCycle (ψ.occurrenceCopies v)) x' pol).sum = 1
        have hsum := List.sum_map_eq_nsmul_single x'.1 (l := ψ.distinctVars)
          (f := fun v ↦ litClauseCount (CNF.implicationCycle (ψ.occurrenceCopies v)) x' pol)
          fun v hne _ ↦ by
            rw [litClauseCount_implicationCycle (hcopies_nd v)]
            simp [CNF.occurrenceCopies, Ne.symm hne]
        have hx1_mem : x'.1 ∈ ψ.distinctVars := by
          rw [CNF.mem_distinctVars, ← CNF.map_fst_vars_occurrenceClauses]
          exact List.mem_map_of_mem hx_mem
        have hcnt1 : ψ.distinctVars.count x'.1 = 1 :=
          Nat.le_antisymm
            ((List.nodup_iff_count_le_one.mp (CNF.nodup_distinctVars ψ)) x'.1)
            (List.count_pos_iff.mpr hx1_mem)
        rw [hsum, hcnt1, one_smul, litClauseCount_implicationCycle (hcopies_nd x'.1)]
        simp [CNF.occurrenceCopies, hx_mem]
      rw [hbase_split, hocc_cnt, hcyc_cnt]
      cases pol <;> cases b₀ <;> simp
    · -- `k = k' + 1 > 0`: never appears in `base`, appears twice in `pads`
      have hbase0 : litClauseCount (ψ.toThreeOccurrence.relabel fun z ↦ (z, 0))
          (x', k' + 1) pol = 0 := by
        simp only [litClauseCount, List.countP_eq_zero, decide_eq_true_eq]
        intro c hc hmem
        obtain ⟨d, -, rfl⟩ := List.mem_map.mp hc
        obtain ⟨⟨z, _⟩, -, heq⟩ := List.mem_map.mp hmem
        exact Nat.succ_ne_zero k' (Prod.mk.inj (Prod.mk.inj heq).1).2.symm
      simp [hbase0]

private theorem satisfiable_rawTwoClauseThree_iff (φ : CNF ℕ) :
    (rawTwoClauseThree φ).Satisfiable ↔ φ.Satisfiable := by
  have hdup : (φ ++ φ).Satisfiable ↔ φ.Satisfiable :=
    ⟨fun ⟨σ, hσ⟩ ↦ ⟨σ, by simp only [CNF.eval_append, Bool.and_eq_true] at hσ; exact hσ.1⟩,
      fun ⟨σ, hσ⟩ ↦ ⟨σ, by simp [CNF.eval_append, hσ]⟩⟩
  rw [← hdup, ← CNF.satisfiable_toThreeOccurrence (φ ++ φ)]
  constructor
  · rintro ⟨τ, hτ⟩
    rw [rawTwoClauseThree, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel] at hτ
    exact ⟨fun x ↦ τ (x, 0), hτ.1⟩
  · rintro ⟨τ₀, hτ₀⟩
    refine ⟨fun u ↦ if u.2 = 0 then τ₀ u.1 else true, ?_⟩
    rw [rawTwoClauseThree, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel]
    refine ⟨hτ₀, (CNF.eval_flatMap_eq_true_iff _ _ _).mpr fun l _ ↦
      eval_twoOccPaddingGadget_of_aux_true l.1 (!l.2) _ fun k hk _ ↦
        by simp [show k ≠ 0 by omega]⟩

private def twoClauseCodec : NatCodec ((ℕ × ℕ × ℕ) × ℕ) :=
  (NatCodec.nat.pair (NatCodec.nat.pair .nat)).pair .nat

private def numberTwoClauseVar (u : (ℕ × ℕ × ℕ) × ℕ) : ℕ :=
  twoClauseCodec u

private theorem numberTwoClauseVar_injective : Function.Injective numberTwoClauseVar :=
  twoClauseCodec.injective

private abbrev encSplitPadVar : (ℕ × ℕ × ℕ) × ℕ ↪ List Bool :=
  encPair (encPair encNat (encPair encUnary encUnary)) encUnary

@[fun_prop]
private theorem computableInPolyTime_numberTwoClauseVar :
    ComputableInPolyTime numberTwoClauseVar encSplitPadVar encNat := by
  unfold numberTwoClauseVar twoClauseCodec encSplitPadVar
  fun_prop

/-- Total polynomial-time reduction from `EUThreeSAT` to `TwoClauseThreeSAT` (and
`AtMostThreeTwoClauseSAT`): checks `EUThreeSAT.syntaxCheck`, doubles the formula, splits variable
occurrences onto binary implication cycles, attaches the 7-clause `(2, 2)` padding gadget to every
missing polarity, and numbers variables injectively in binary; rejects malformed inputs with
`[[]]`. -/
def toTwoClauseThreeSAT (φ : CNF ℕ) : CNF ℕ :=
  if EUThreeSAT.syntaxCheck φ then (rawTwoClauseThree φ).relabel numberTwoClauseVar else [[]]

/-- Total correctness of `toTwoClauseThreeSAT` into `TwoClauseThreeSAT`. -/
theorem mem_twoClauseThreeSAT_toTwoClauseThreeSAT_iff (φ : CNF ℕ) :
    toTwoClauseThreeSAT φ ∈ TwoClauseThreeSAT ↔ φ ∈ EUThreeSAT := by
  unfold toTwoClauseThreeSAT
  split_ifs with hs
  · have hφ : φ.IsExactThreeDistinct := (EUThreeSAT.syntaxCheck_iff φ).mp hs
    have hsat :=
      (CNF.satisfiable_relabel numberTwoClauseVar_injective (rawTwoClauseThree φ)).trans
        (satisfiable_rawTwoClauseThree_iff φ)
    exact ⟨fun ⟨_, h⟩ ↦ ⟨hφ, hsat.mp h⟩,
      fun ⟨_, h⟩ ↦ ⟨(isTwoClauseThree_rawTwoClauseThree hφ).relabel numberTwoClauseVar_injective,
        hsat.mpr h⟩⟩
  · have hns : ¬ φ.IsExactThreeDistinct := fun h ↦ hs ((EUThreeSAT.syntaxCheck_iff φ).mpr h)
    refine iff_of_false (fun ⟨_, σ, hσ⟩ ↦ ?_) fun ⟨h, _⟩ ↦ hns h
    simp [CNF.eval, Clause.eval] at hσ

/-- Total correctness of `toTwoClauseThreeSAT` into `AtMostThreeTwoClauseSAT`. -/
theorem mem_atMostThreeTwoClauseSAT_toTwoClauseThreeSAT_iff (φ : CNF ℕ) :
    toTwoClauseThreeSAT φ ∈ AtMostThreeTwoClauseSAT ↔ φ ∈ EUThreeSAT := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ twoClauseThreeSAT_subset_atMostThreeTwoClauseSAT
      ((mem_twoClauseThreeSAT_toTwoClauseThreeSAT_iff φ).mpr h)⟩
  unfold toTwoClauseThreeSAT at h
  split_ifs at h with hs
  · have hφ : φ.IsExactThreeDistinct := (EUThreeSAT.syntaxCheck_iff φ).mp hs
    have hsat :=
      (CNF.satisfiable_relabel numberTwoClauseVar_injective (rawTwoClauseThree φ)).trans
        (satisfiable_rawTwoClauseThree_iff φ)
    exact ⟨hφ, hsat.mp h.2⟩
  · obtain ⟨_, σ, hσ⟩ := h
    simp [CNF.eval, Clause.eval] at hσ

/-- `toTwoClauseThreeSAT` runs in polynomial time under `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_toTwoClauseThreeSAT :
    ComputableInPolyTime toTwoClauseThreeSAT encCNF encCNF := by
  let encSplit : ℕ × ℕ × ℕ ↪ List Bool := encPair encNat (encPair encUnary encUnary)
  have hgad : ComputableInPolyTime
      (fun l : Literal (ℕ × ℕ × ℕ) ↦ twoOccPaddingGadget l.1 (!l.2))
      (encPair encSplit encBool) (encCNFOver encSplitPadVar) := by
    have hlit (k : ℕ) (pol : Bool) : ComputableInPolyTime
        (fun l : Literal (ℕ × ℕ × ℕ) ↦ ((l.1, k), pol))
        (encPair encSplit encBool) (encPair encSplitPadVar encBool) := by
      unfold encSplitPadVar; fun_prop
    have hlit0 : ComputableInPolyTime
        (fun l : Literal (ℕ × ℕ × ℕ) ↦ ((l.1, (0 : ℕ)), !l.2))
        (encPair encSplit encBool) (encPair encSplitPadVar encBool) := by
      unfold encSplitPadVar; fun_prop
    have hcl3 {f g h : Literal (ℕ × ℕ × ℕ) → Literal ((ℕ × ℕ × ℕ) × ℕ)}
        (hf : ComputableInPolyTime f (encPair encSplit encBool) (encPair encSplitPadVar encBool))
        (hg : ComputableInPolyTime g (encPair encSplit encBool) (encPair encSplitPadVar encBool))
        (hh : ComputableInPolyTime h (encPair encSplit encBool) (encPair encSplitPadVar encBool)) :
        ComputableInPolyTime (fun l ↦ [f l, g l, h l]) (encPair encSplit encBool)
          (encList (encPair encSplitPadVar encBool)) :=
      .cons' hf (.cons' hg (.cons' hh (.const [])))
    exact .cons' (hcl3 hlit0 (hlit 1 true) (hlit 2 false))
      (.cons' (hcl3 (hlit 1 true) (hlit 3 true) (hlit 4 false))
      (.cons' (hcl3 (hlit 1 false) (hlit 3 true) (hlit 4 false))
      (.cons' (hcl3 (hlit 1 false) (hlit 4 true) (hlit 5 false))
      (.cons' (hcl3 (hlit 2 true) (hlit 4 true) (hlit 5 false))
      (.cons' (hcl3 (hlit 2 true) (hlit 3 false) (hlit 5 true))
      (.cons' (hcl3 (hlit 2 false) (hlit 3 false) (hlit 5 true))
      (.const [])))))))
  have hraw : ComputableInPolyTime rawTwoClauseThree encCNF (encCNFOver encSplitPadVar) := by
    have hdup : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ ++ φ) encCNF (encCNFOver encNat) :=
      (ComputableInPolyTime.listAppend (encList (encPair encNat encBool))).comp (.prod .id' .id')
    have hbase : ComputableInPolyTime
        (fun φ : CNF ℕ ↦ (φ ++ φ).toThreeOccurrence.relabel fun x ↦ (x, (0 : ℕ)))
        encCNF (encCNFOver encSplitPadVar) := by
      have hpad0 : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ (x, (0 : ℕ)))
          encSplit encSplitPadVar :=
        ComputableInPolyTime.prod .id' (.const 0)
      have hrel := CNF.computableInPolyTime_relabel hpad0
      exact hrel.comp ((CNF.computableInPolyTime_toThreeOccurrence encNat).comp hdup)
    have hpads : ComputableInPolyTime
        (fun φ : CNF ℕ ↦ (φ ++ φ).occurrenceClauses.flatten.flatMap fun l ↦
          twoOccPaddingGadget l.1 (!l.2))
        encCNF (encCNFOver encSplitPadVar) := by
      have hocc := (CNF.computableInPolyTime_occurrenceClauses encNat).comp hdup
      have hfl := (ComputableInPolyTime.flatten (encPair encSplit encBool)).comp hocc
      exact ComputableInPolyTime.flatMapWithInput hfl
        (hgad.comp (ComputableInPolyTime.snd _ _))
    exact (ComputableInPolyTime.listAppend (encList (encPair encSplitPadVar encBool))).comp
      (.prod hbase hpads)
  have hrelRaw : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (rawTwoClauseThree φ).relabel numberTwoClauseVar) encCNF encCNF :=
    (CNF.computableInPolyTime_relabel computableInPolyTime_numberTwoClauseVar).comp hraw
  exact EUThreeSAT.computableInPolyTime_syntaxCheck.ite hrelRaw (.const [[]])

/-- `EUThreeSAT` polynomial-time many-one reduces to `TwoClauseThreeSAT`. -/
theorem polyTimeReducible_EUThreeSAT_twoClauseThreeSAT :
    PolyTimeReducible encCNF encCNF EUThreeSAT TwoClauseThreeSAT :=
  ⟨toTwoClauseThreeSAT, computableInPolyTime_toTwoClauseThreeSAT,
    fun φ ↦ (mem_twoClauseThreeSAT_toTwoClauseThreeSAT_iff φ).symm⟩

/-- `EUThreeSAT` polynomial-time many-one reduces to `AtMostThreeTwoClauseSAT`. -/
theorem polyTimeReducible_EUThreeSAT_atMostThreeTwoClauseSAT :
    PolyTimeReducible encCNF encCNF EUThreeSAT AtMostThreeTwoClauseSAT :=
  ⟨toTwoClauseThreeSAT, computableInPolyTime_toTwoClauseThreeSAT,
    fun φ ↦ (mem_atMostThreeTwoClauseSAT_toTwoClauseThreeSAT_iff φ).symm⟩

/-- `TwoClauseThreeSAT` is unconditionally `NP`-hard. -/
theorem twoClauseThreeSAT_npHard : NPHard encCNF TwoClauseThreeSAT :=
  EUThreeSAT_npHard.trans polyTimeReducible_EUThreeSAT_twoClauseThreeSAT

/-- **`TwoClauseThreeSAT` (`(2/3, B2)`-SAT) is `NP`-complete.** -/
theorem twoClauseThreeSAT_npComplete : NPComplete encCNF TwoClauseThreeSAT :=
  ⟨twoClauseThreeSAT_mem_NP, twoClauseThreeSAT_npHard⟩

/-- `AtMostThreeTwoClauseSAT` is unconditionally `NP`-hard. -/
theorem atMostThreeTwoClauseSAT_npHard : NPHard encCNF AtMostThreeTwoClauseSAT :=
  EUThreeSAT_npHard.trans polyTimeReducible_EUThreeSAT_atMostThreeTwoClauseSAT

/-- **`AtMostThreeTwoClauseSAT` is `NP`-complete.** -/
theorem atMostThreeTwoClauseSAT_npComplete : NPComplete encCNF AtMostThreeTwoClauseSAT :=
  ⟨atMostThreeTwoClauseSAT_mem_NP, atMostThreeTwoClauseSAT_npHard⟩

/-! ### Internal non-vacuity check -/

/-- Explicit satisfiable 3-variable, 4-clause member and unsatisfiable 2-variable, 4-clause
non-member satisfying `IsTwoClauseThree`. -/
private theorem twoClauseThreeSAT_nontrivial :
    let φSat : CNF ℕ :=
      [ [(0, true), (1, true), (2, true)],
        [(0, true), (1, false), (2, false)],
        [(0, false), (1, true), (2, false)],
        [(0, false), (1, false), (2, true)] ]
    let φUnsat : CNF ℕ :=
      [ [(0, true), (1, true)],
        [(0, true), (1, false)],
        [(0, false), (1, true)],
        [(0, false), (1, false)] ]
    φSat ∈ TwoClauseThreeSAT ∧ IsTwoClauseThree φUnsat ∧ φUnsat ∉ TwoClauseThreeSAT := by
  refine ⟨⟨(twoClauseThreeCheck_iff _).mp (by decide), fun _ ↦ true, by decide⟩,
    (twoClauseThreeCheck_iff _).mp (by decide), fun ⟨_, σ, hσ⟩ ↦ ?_⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [CNF.eval, Clause.eval, Literal.eval, h0, h1] at hσ

end CslibFrontier.Complexity
