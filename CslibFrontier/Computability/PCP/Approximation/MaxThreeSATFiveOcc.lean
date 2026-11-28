/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Logics.Propositional.CNF.UnsatVal
import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.PCP.Approximation.MaxThreeSAT
import CslibFrontier.Computability.PCP.Encoded.Amplification.Arithmetic
import CslibFrontier.Computability.PCP.Encoded.Constraints
import CslibFrontier.Computability.PCP.Encoded.DegreeReduction
import CslibFrontier.Logics.Propositional.CNF.Compact.Relabel
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Gap NP-Hardness of Exact 5-Occurrence 3-SAT

This module proves under standard Lean axioms that there is an explicit universal constant
`ε₀ ∈ (0, 1)` for which it is `NP`-hard (under deterministic polynomial-time many-one reductions
on multi-tape Turing machines) to distinguish satisfiable 3-CNF formulas from 3-CNF formulas in
which every assignment satisfies at most a `1 - ε₀` fraction of the clauses, even when every
clause consists of `3` literals on pairwise distinct variables and every occurring variable appears
`5` times (`E3SAT-5`,).

Starting from Dinur's `MAX-2CSP` hardness theorem (`Cslib.Complexity.GapTwoCSP_npHard`), the
reduction composes four polynomial-time gap-preserving stages:
1. Expander degree reduction (`Cslib.PCP.Encoded.Graph.degreeReduce`) with the uniform arithmetic
   expander family (`Cslib.RotationMap.arithmeticExpander`), bounding every vertex degree.
2. Encoding binary constraint tables as `2 k`-CNF clauses and splitting to width `3`
   (`Cslib.PCP.Encoded.Graph.toCNF`, `Cslib.Complexity.toThreeSAT`) with bounded occurrences `Δ₀`.
3. Clause doubling (`φ ++ φ`) and Papadimitriou–Yannakakis occurrence splitting
   (`Cslib.Complexity.toThreeSATThree`) into ternary clauses and binary implication cycles.
4. Replacing each binary clause by a `13`-clause exact-`3`-distinct octahedron gadget on `7` fresh
   variables so every occurring variable appears `5` times while retaining `1 / 13` of the gap.

## Main definitions

* `Cslib.Complexity.IsExactThreeSATFiveOcc`: predicate asserting that every clause of a CNF
  formula has `3` literals on pairwise distinct variables and every occurring variable has `5`
  literal occurrences.
* `Cslib.Complexity.GapExactThreeSATFiveOcc`: the gap promise problem of `MAX-E3SAT-5` with
  perfect completeness `1` and soundness `s` on nonempty `E3SAT-5` instances.
* `Cslib.Complexity.feigeFiveOccGap`: explicit positive soundness-gap constant `ε₀ ∈ (0, 1)`
  for `MAX-E3SAT-5`.

## Main results

* `Cslib.Complexity.gapExactThreeSATFiveOcc_npHard`: `GapExactThreeSATFiveOcc` with soundness
  `1 - feigeFiveOccGap` is `NP`-hard under deterministic polynomial-time reductions.
* `Cslib.Complexity.exists_gapExactThreeSATFiveOcc_npHard`: existential form of Feige's
  `E3SAT-5` gap `NP`-hardness theorem (`∃ ε₀ ∈ (0, 1), NPHard...`).
* `Cslib.Complexity.gapExactThreeSATFiveOcc_notMem_PromiseP`: unless `P = NP`, no
  polynomial-time algorithm solves `GapExactThreeSATFiveOcc (1 - feigeFiveOccGap)`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM Finset
open Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.HadamardTester

section Defs

variable {V : Type*}

/-- A CNF formula `φ` is an **exact 5-occurrence 3-SAT (`E3SAT-5`) formula** when every clause
has `3` literals on pairwise distinct variables (`CNF.IsExactThreeDistinct`) and every variable
occurring in `φ` has `5` literal occurrences in total. -/
def IsExactThreeSATFiveOcc [DecidableEq V] (φ : CNF V) : Prop :=
  φ.IsExactThreeDistinct ∧ ∀ v ∈ φ.vars, φ.vars.count v = 5

/-- Characterization of `IsExactThreeSATFiveOcc` in terms of `CNF.IsExactThreeDistinct` and exact
count `5` on occurring variables. -/
theorem isExactThreeSATFiveOcc_iff [DecidableEq V] {φ : CNF V} :
    IsExactThreeSATFiveOcc φ ↔ φ.IsExactThreeDistinct ∧ ∀ v ∈ φ.vars, φ.vars.count v = 5 :=
  Iff.rfl

/-- Computable decidability of `IsExactThreeSATFiveOcc` over a decidable variable type. -/
instance instDecidableIsExactThreeSATFiveOcc [DecidableEq V] (φ : CNF V) :
    Decidable (IsExactThreeSATFiveOcc φ) :=
  inferInstanceAs (Decidable (φ.IsExactThreeDistinct ∧ ∀ v ∈ φ.vars, φ.vars.count v = 5))

/-- The empty CNF formula vacuously satisfies `IsExactThreeSATFiveOcc`. -/
@[simp]
theorem isExactThreeSATFiveOcc_nil [DecidableEq V] :
    IsExactThreeSATFiveOcc ([] : CNF V) :=
  ⟨fun _ hc ↦ False.elim (List.not_mem_nil hc), fun _ hv ↦ False.elim (List.not_mem_nil hv)⟩

end Defs

/-- The gap promise problem of **`MAX-E3SAT-5`** with perfect completeness `1` and soundness `s`:
instances are nonempty `E3SAT-5` formulas over `ℕ`, yes-instances are satisfiable (`unsatVal = 0`),
and no-instances have satisfaction ratio `1 - φ.unsatVal ≤ s`. -/
noncomputable def GapExactThreeSATFiveOcc (s : ℝ) : PromiseProblem (CNF ℕ) :=
  (PromiseProblem.gapMax (fun φ ↦ 1 - φ.unsatVal) (fun _ ↦ 1) (fun _ ↦ s)).restrict
    {φ | IsExactThreeSATFiveOcc φ ∧ 0 < φ.length}

/-- Yes-instances of `GapExactThreeSATFiveOcc` are nonempty satisfiable `E3SAT-5` formulas. -/
theorem mem_yes_GapExactThreeSATFiveOcc {s : ℝ} {φ : CNF ℕ} :
    φ ∈ (GapExactThreeSATFiveOcc s).yes ↔
      φ.Satisfiable ∧ IsExactThreeSATFiveOcc φ ∧ 0 < φ.length := by
  simp only [GapExactThreeSATFiveOcc, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, ← CNF.unsatVal_eq_zero_iff]
  have h0 := φ.unsatVal_nonneg
  exact ⟨fun ⟨h, h5⟩ ↦ ⟨by linarith, h5⟩, fun ⟨h, h5⟩ ↦ ⟨by linarith, h5⟩⟩

/-- For `s < 1`, no-instances of `GapExactThreeSATFiveOcc` are nonempty `E3SAT-5` formulas in
which every assignment falsifies at least a `1 - s` fraction of the clauses. -/
theorem mem_no_GapExactThreeSATFiveOcc {s : ℝ} (hs : s < 1) {φ : CNF ℕ} :
    φ ∈ (GapExactThreeSATFiveOcc s).no ↔
      1 - s ≤ φ.unsatVal ∧ IsExactThreeSATFiveOcc φ ∧ 0 < φ.length := by
  simp only [GapExactThreeSATFiveOcc, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ (1 : ℝ)) (s := fun _ ↦ s) hs,
    Set.mem_ofPred_eq]
  exact ⟨fun ⟨h, h5⟩ ↦ ⟨by linarith, h5⟩, fun ⟨h, h5⟩ ↦ ⟨by linarith, h5⟩⟩

/-! ### Stage 0: Concrete nonempty satisfiable `E3SAT-5` fallback formula -/

private def baseFiveOccCNF : CNF ℕ :=
  [ [(0, true), (1, true), (2, true)], [(0, true), (1, true), (3, true)],
    [(0, true), (2, true), (4, true)], [(0, true), (3, true), (5, true)],
    [(0, true), (4, true), (5, true)], [(1, true), (2, true), (5, true)],
    [(1, true), (3, true), (4, true)], [(1, true), (4, true), (5, true)],
    [(2, true), (3, true), (4, true)], [(2, true), (3, true), (5, true)] ]

private theorem isExactThreeSATFiveOcc_baseFiveOccCNF :
    IsExactThreeSATFiveOcc baseFiveOccCNF := by decide

private theorem satisfiable_baseFiveOccCNF : baseFiveOccCNF.Satisfiable :=
  ⟨fun _ ↦ true, by decide⟩

private theorem length_baseFiveOccCNF_pos : 0 < baseFiveOccCNF.length := by decide

/-! ### Stage 1: Polymorphic expander degree reduction of `GapTwoCSP` -/

private noncomputable def degreeReduceTwoCSP {α D : Type} [DecidableEq α]
    (fallback : α → α → Bool) (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (g : Graph (α → α → Bool)) : Graph (α → α → Bool) :=
  (g.degreeReduce fallback rotate labels).mapConstraints (Graph.degreeReduceEval id)

private theorem isPolyTime_degreeReduceTwoCSP {α D : Type} [Fintype α] [DecidableEq α]
    {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool}
    (fallback : α → α → Bool) (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (hrot : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding)) :
    ComputableInPolyTime (degreeReduceTwoCSP fallback rotate labels)
      (Graph.encoding encConstraintTable) (Graph.encoding encConstraintTable) := by
  have hdeg := Graph.isPolyTime_degreeReduce (enc := encConstraintTable)
    (labelEncoding := labelEncoding) fallback labels rotate hrot
  have htab := Graph.isPolyTime_tabulateConstraints (alphabet := alphabet)
    (Graph.isPolyTime_degreeReduceEval (eval := id) (Graph.isPolyTime_constraintTableEval alphabet))
  exact htab.comp hdeg

private theorem countP_product_fst_le {α β : Type*} (l₁ : List α) (l₂ : List β)
    (hl₁ : l₁.Nodup) (p : α → Bool) (hp : ∀ x ∈ l₁, ∀ y ∈ l₁, p x → p y → x = y) :
    (l₁.product l₂).countP (fun q ↦ p q.1) ≤ l₂.length := by
  induction l₁ with
  | nil => simp [List.product]
  | cons a rest ih =>
    rw [List.nodup_cons] at hl₁
    simp only [List.product, List.flatMap_cons, List.countP_append]
    by_cases ha : p a
    · have hrest : (rest.flatMap fun x ↦ l₂.map (x, ·)).countP (fun q ↦ p q.1) = 0 :=
        List.countP_eq_zero.2 fun q hq hpq ↦ by
          obtain ⟨x, hx, hqm⟩ := List.mem_flatMap.1 hq
          obtain ⟨_, _, rfl⟩ := List.mem_map.1 hqm
          exact hl₁.1 (hp x (List.mem_cons_of_mem a hx) a List.mem_cons_self hpq ha ▸ hx)
      rw [hrest, add_zero, List.countP_map]; exact List.countP_le_length
    · have hhead : (l₂.map (a, ·)).countP (fun q ↦ p q.1) = 0 :=
        List.countP_eq_zero.2 fun q hq ↦ by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hq; simpa using ha
      rw [hhead, zero_add]
      exact ih hl₁.2 fun x hx y hy ↦ hp x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)

private theorem countP_src_degreeReduceTwoCSP_le {α D : Type} [DecidableEq α] [Fintype D]
    (fallback : α → α → Bool) (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (hlen : labels.length = Fintype.card D) (g : Graph (α → α → Bool)) (u : ℕ) :
    ((degreeReduceTwoCSP fallback rotate labels g).edges.countP fun e ↦ decide (e.src = u)) ≤
      1 + Fintype.card D := by
  simp only [degreeReduceTwoCSP, Graph.mapConstraints, Graph.degreeReduce, List.map_map,
    List.countP_map, Function.comp_def, Graph.src_degreeReduceEdge, Graph.degreeReduceDarts]
  refine (countP_product_fst_le g.halfEdges (none :: labels.map some) g.nodup_halfEdges
    (fun q ↦ decide (Graph.halfEdgeNumber q = u)) ?_).trans_eq ?_
  · intro x _ y _ hx hy
    exact Graph.halfEdgeNumber_injective
      ((of_decide_eq_true hx).trans (of_decide_eq_true hy).symm)
  · simp [hlen, Nat.add_comm]

private theorem countP_dst_degreeReduceTwoCSP_le {α D : Type} [DecidableEq α] [Fintype D]
    (fallback : α → α → Bool) (family : (n : ℕ) → Cslib.RotationMap (Fin n) D)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    (g : Graph (α → α → Bool)) (u : ℕ) :
    ((degreeReduceTwoCSP fallback rotate labels g).edges.countP fun e ↦ decide (e.dst = u)) ≤
      1 + Fintype.card D := by
  classical
  set h := g.degreeReduce fallback rotate labels
  have hcnt : ((degreeReduceTwoCSP fallback rotate labels g).edges.countP fun e ↦
        decide (e.dst = u)) =
      (Finset.univ.filter fun i : Fin h.edges.length ↦ h.edges[i.val].dst = u).card := by
    have key (l : List (Edge (Option (Bool × (α → α → Bool))))) :
        (l.countP fun e ↦ decide (e.dst = u)) =
          (Finset.univ.filter fun i : Fin l.length ↦ l[i.val].dst = u).card := by
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.countP_cons, ih]
        change _ = (Finset.univ.filter fun i : Fin (l.length + 1) ↦ (a :: l)[i.val].dst = u).card
        rw [Fin.card_filter_univ_succ']
        simp [add_comm]
    simp only [degreeReduceTwoCSP, Graph.mapConstraints, h, List.countP_map, Function.comp_def]
    exact key h.edges
  rw [hcnt]
  let enum := g.degreeReduceEnumeration fallback rotate labels hlabels hmem
  let H := ((g.toGraph id).degreeReduce (g.cloudFamily id fallback family)).graph
  have htoG := Graph.toGraph_degreeReduce g id fallback family rotate hrotate labels hlabels hmem
  have hdst_eq (i : Fin h.edges.length) :
      h.edges[i.val].dst =
        Graph.halfEdgeNumber ((H.rot (enum.equiv i)).1.1.val, (H.rot (enum.equiv i)).1.2) := by
    have h1 := congrFun (congrArg ConstraintGraph.dst htoG) i
    dsimp only [ConstraintGraph.comap, ConstraintGraph.map,
      RegularConstraintGraph.toConstraintGraph, Function.comp_apply] at h1
    rw [Cslib.RotationMap.neighbor_def] at h1
    exact h1
  let eRot : ((Fin g.edges.length × Bool) × (Unit ⊕ D)) ≃
      ((Fin g.edges.length × Bool) × (Unit ⊕ D)) :=
    Equiv.ofBijective H.rot H.rot_involutive.bijective
  have hcard1 : (Finset.univ.filter fun i : Fin h.edges.length ↦ h.edges[i.val].dst = u).card =
      (Finset.univ.filter fun p : (Fin g.edges.length × Bool) × (Unit ⊕ D) ↦
        Graph.halfEdgeNumber ((H.rot p).1.1.val, (H.rot p).1.2) = u).card := by
    rw [← Finset.card_map enum.equiv.toEmbedding]
    refine congrArg Finset.card (Finset.ext fun p ↦ ?_)
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    exact ⟨fun ⟨i, hi, heq⟩ ↦ heq ▸ (hdst_eq i ▸ hi),
      fun hp ↦ ⟨enum.equiv.symm p, by simpa [hdst_eq] using hp, enum.equiv.apply_symm_apply p⟩⟩
  have hcard2 : (Finset.univ.filter fun p : (Fin g.edges.length × Bool) × (Unit ⊕ D) ↦
        Graph.halfEdgeNumber ((H.rot p).1.1.val, (H.rot p).1.2) = u).card =
      (Finset.univ.filter fun q : (Fin g.edges.length × Bool) × (Unit ⊕ D) ↦
        Graph.halfEdgeNumber (q.1.1.val, q.1.2) = u).card := by
    rw [← Finset.card_map eRot.toEmbedding]
    refine congrArg Finset.card (Finset.ext fun q ↦ ?_)
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    exact ⟨fun ⟨p, hp, heq⟩ ↦ by simpa [show H.rot p = q from heq] using hp, fun hq ↦
      ⟨eRot.symm q, by simpa [show H.rot (eRot.symm q) = q from eRot.apply_symm_apply q] using hq,
        eRot.apply_symm_apply q⟩⟩
  rw [hcard1, hcard2]
  by_cases hex : ∃ v : Fin g.edges.length × Bool, Graph.halfEdgeNumber (v.1.val, v.2) = u
  · obtain ⟨v₀, hv₀⟩ := hex
    have hsub : (Finset.univ.filter fun q : (Fin g.edges.length × Bool) × (Unit ⊕ D) ↦
        Graph.halfEdgeNumber (q.1.1.val, q.1.2) = u) ⊆
        ({v₀} : Finset _) ×ˢ (Finset.univ : Finset (Unit ⊕ D)) := fun q hq ↦ by
      have hqv : q.1 = v₀ := Graph.halfEdgeNumber_fin_injective g.edges.length
        ((Finset.mem_filter.1 hq).2.trans hv₀.symm)
      exact Finset.mem_product.2 ⟨Finset.mem_singleton.2 hqv, Finset.mem_univ _⟩
    exact (Finset.card_le_card hsub).trans_eq (by simp [Nat.add_comm])
  · push Not at hex
    have hemp : (Finset.univ.filter fun q : (Fin g.edges.length × Bool) × (Unit ⊕ D) ↦
        Graph.halfEdgeNumber (q.1.1.val, q.1.2) = u) = ∅ := by ext q; simp [hex q.1]
    rw [hemp, Finset.card_empty]; exact Nat.zero_le _

/-! ### Stage 2: Exact-width-`3` CNF conversion with bounded variable occurrences -/

private noncomputable def toBoundedWidthThreeCNF {α D : Type} [DecidableEq α] {k : ℕ}
    (e : α ≃ (Fin k → Bool)) (pairs : List (α × α))
    (fallback : α → α → Bool) (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (g : Graph (α → α → Bool)) : CNF ℕ :=
  toThreeSAT (Graph.toCNF e pairs (degreeReduceTwoCSP fallback rotate labels g))

private theorem isPolyTime_toBoundedWidthThreeCNF {α D : Type} [Fintype α] [DecidableEq α]
    {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool} {k : ℕ}
    (e : α ≃ (Fin k → Bool)) (pairs : List (α × α))
    (fallback : α → α → Bool) (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (hrot : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding)) :
    ComputableInPolyTime (toBoundedWidthThreeCNF e pairs fallback rotate labels)
      (Graph.encoding encConstraintTable) encCNF :=
  computableInPolyTime_toThreeSAT.comp
    ((Graph.isPolyTime_toCNF e pairs).comp
      (isPolyTime_degreeReduceTwoCSP (alphabet := alphabet) fallback rotate labels hrot))

private theorem length_eq_three_of_mem_splitAux {W : Type*} (fresh : ℕ → W) (j : ℕ)
    (carry : Literal W) (rest : Clause W) (hrest : 2 ≤ rest.length) :
    ∀ d ∈ Clause.splitAux fresh j carry rest, d.length = 3 := by
  fun_induction Clause.splitAux fresh j carry rest with
  | case1 j carry b c d rest' ih =>
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact ih (by simp) e he
  | case2 j carry rest' hnot =>
    intro e he
    obtain rfl := List.mem_singleton.1 he
    match rest', hrest, hnot with
    | [_, _], _, _ => rfl
    | _ :: _ :: _ :: _, _, hnot => exact absurd rfl (hnot _ _ _ _)

private theorem length_eq_three_of_mem_toBoundedWidthThreeCNF {α D : Type} [DecidableEq α]
    {k : ℕ} (hk : 2 ≤ k) (e : α ≃ (Fin k → Bool)) (pairs : List (α × α))
    (fallback : α → α → Bool) (rotate : ℕ × (ℕ × D) → ℕ × D) (labels : List D)
    (g : Graph (α → α → Bool)) :
    ∀ c ∈ toBoundedWidthThreeCNF e pairs fallback rotate labels g, c.length = 3 := by
  intro c hc
  simp only [toBoundedWidthThreeCNF, toThreeSAT, CNF.relabel, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  rw [Clause.length_relabel]
  simp only [CNF.to3CNF, List.mem_flatMap] at hd
  obtain ⟨⟨orig, idx⟩, hx, hd⟩ := hd
  have horig : orig ∈ Graph.toCNF e pairs (degreeReduceTwoCSP fallback rotate labels g) :=
    List.fst_mem_of_mem_zipIdx hx
  have hlen : orig.length = 2 * k := Graph.length_of_mem_toCNF e pairs horig
  dsimp only at hd
  cases hrel : orig.relabel (Sum.inl (β := ℕ × ℕ)) with
  | nil =>
    have h0 := congrArg List.length hrel; simp [Clause.length_relabel, hlen] at h0; omega
  | cons carry rest =>
    have hrest : 2 ≤ rest.length := by
      have h1 := congrArg List.length hrel; simp [Clause.length_relabel, hlen] at h1; omega
    rw [hrel, Clause.split3] at hd
    exact length_eq_three_of_mem_splitAux _ 0 carry rest hrest d hd

private theorem count_vars_excludeClause_le {α : Type} {k : ℕ} (e : α ≃ (Fin k → Bool))
    (u v : ℕ) (p : α × α) (x : ℕ) :
    ((Graph.excludeClause e u v p).map Prod.fst).count x ≤
      (if u = x.unpair.1 then 1 else 0) + (if v = x.unpair.1 then 1 else 0) := by
  simp only [Graph.excludeClause, List.map_append, List.map_map, Function.comp_def,
    List.count_append]
  have half (w : ℕ) :
      ((List.finRange k).map fun i : Fin k ↦ Nat.pair w i.val).count x ≤
        if w = x.unpair.1 then 1 else 0 := by
    have hnodup : ((List.finRange k).map fun i : Fin k ↦ Nat.pair w i.val).Nodup := by
      refine (List.nodup_finRange k).map fun i j hij ↦ Fin.ext ?_
      have h1 := congrArg Nat.unpair hij
      simpa [Nat.unpair_pair] using h1
    split_ifs with hw
    · exact List.nodup_iff_count_le_one.1 hnodup x
    · refine Nat.le_zero.2 (List.count_eq_zero.2 fun hmem ↦ hw ?_)
      obtain ⟨i, _, hi⟩ := List.mem_map.1 hmem
      have h1 := congrArg (Prod.fst ∘ Nat.unpair) hi
      simpa [Nat.unpair_pair] using h1
  exact Nat.add_le_add (half u) (half v)

private theorem vars_flatMap {α V : Type*} (l : List α) (f : α → CNF V) :
    CNF.vars (l.flatMap f) = l.flatMap fun a ↦ (f a).vars := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, CNF.vars, List.flatten_append, List.map_append]
    exact congrArg ((f a).vars ++ ·) ih

private theorem cnf_vars_append {V : Type*} (φ₁ φ₂ : CNF V) :
    (φ₁ ++ φ₂).vars = φ₁.vars ++ φ₂.vars := by
  simp [CNF.vars, List.flatten_append, List.map_append]

private theorem sum_map_count_vars {V : Type*} [DecidableEq V] (ψ : CNF V) (v : V) :
    (ψ.map fun c ↦ (c.map Prod.fst).count v).sum = ψ.vars.count v := by
  induction ψ with
  | nil => rfl
  | cons c rest ih => simp [CNF.vars, List.map_append, List.count_append, ih]

private theorem sum_zipIdx_single {α : Type*} (l : List α) (f : α × ℕ → ℕ) (i₀ : ℕ)
    (hzero : ∀ p ∈ l.zipIdx, p.2 ≠ i₀ → f p = 0) :
    (l.zipIdx.map f).sum = if h : i₀ < l.length then f (l[i₀], i₀) else 0 := by
  have go (xs : List α) (k : ℕ) (hz : ∀ p ∈ xs.zipIdx k, p.2 ≠ i₀ → f p = 0) :
      ((xs.zipIdx k).map f).sum =
        if h : k ≤ i₀ ∧ i₀ - k < xs.length then f (xs[i₀ - k]'h.2, i₀) else 0 := by
    induction xs generalizing k with
    | nil => simp
    | cons a rest ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
      rw [ih (k + 1) (fun p hp ↦ hz p (List.mem_cons_of_mem _ hp))]
      by_cases hk : k = i₀
      · subst hk; simp [show ¬(k + 1 ≤ k) by omega]
      · rw [hz (a, k) List.mem_cons_self hk, zero_add]
        split_ifs with h1 h2
        · have hidx : i₀ - k = (i₀ - (k + 1)) + 1 := by omega
          simp [hidx]
        · omega
        · omega
        · rfl
  simpa using go l 0 hzero

private theorem count_vars_toCNF_le {α : Type} {k : ℕ} (e : α ≃ (Fin k → Bool))
    (pairs : List (α × α)) (h : Graph (α → α → Bool)) (x : ℕ) :
    (Graph.toCNF e pairs h).vars.count x ≤
      pairs.length *
        ((h.edges.countP fun d ↦ decide (d.src = x.unpair.1)) +
          (h.edges.countP fun d ↦ decide (d.dst = x.unpair.1))) := by
  rw [Graph.toCNF, vars_flatMap, List.count_flatMap]
  have hvars_map {β : Type} (l : List β) (g : β → Clause ℕ) :
      CNF.vars (l.map g) = l.flatMap fun a ↦ (g a).map Prod.fst := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [← ih]; simp [CNF.vars, List.map_append]
  have hedge (d : Edge (α → α → Bool)) :
      (Graph.edgeCNF e pairs d).vars.count x ≤
        pairs.length *
          ((if d.src = x.unpair.1 then 1 else 0) + (if d.dst = x.unpair.1 then 1 else 0)) := by
    rw [Graph.edgeCNF, hvars_map, List.count_flatMap]
    refine (List.sum_le_length_nsmul _
      ((if d.src = x.unpair.1 then 1 else 0) + (if d.dst = x.unpair.1 then 1 else 0))
      fun n hn ↦ ?_).trans ?_
    · obtain ⟨p, _, rfl⟩ := List.mem_map.1 hn
      exact count_vars_excludeClause_le e d.src d.dst p x
    · simp only [smul_eq_mul, List.length_map]
      exact Nat.mul_le_mul_right _ (List.length_filter_le _ _)
  have hsum : (h.edges.map fun d ↦ (Graph.edgeCNF e pairs d).vars.count x).sum ≤
      (h.edges.map fun d ↦ pairs.length *
        ((if d.src = x.unpair.1 then 1 else 0) + (if d.dst = x.unpair.1 then 1 else 0))).sum :=
    List.sum_le_sum fun d _ ↦ hedge d
  refine hsum.trans ?_
  rw [List.sum_map_mul_left]
  refine Nat.mul_le_mul_left _ ?_
  induction h.edges with
  | nil => simp
  | cons d rest ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    have hs : (if decide (d.src = x.unpair.1) = true then 1 else 0) =
        if d.src = x.unpair.1 then 1 else 0 := by simp
    have hd : (if decide (d.dst = x.unpair.1) = true then 1 else 0) =
        if d.dst = x.unpair.1 then 1 else 0 := by simp
    omega

private theorem count_vars_splitAux_of_ne {W : Type*} [BEq W] [LawfulBEq W] (fresh : ℕ → W)
    (j : ℕ) (carry : Literal W) (rest : Clause W) (w : W) (hfresh : ∀ k, j ≤ k → fresh k ≠ w) :
    (Clause.splitAux fresh j carry rest).vars.count w =
      (if carry.1 == w then 1 else 0) + (rest.map Prod.fst).count w := by
  fun_induction Clause.splitAux fresh j carry rest with
  | case1 j carry b c d rest' ih =>
    have hj : fresh j ≠ w := hfresh j le_rfl
    simp only [CNF.vars, List.flatten_cons, List.map_append, List.count_append]
    have nih := ih fun k hk ↦ hfresh k (by omega)
    simp only [CNF.vars] at nih
    rw [nih]
    simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, beq_iff_eq, hj,
      ↓reduceIte]
    split_ifs <;> omega
  | case2 j carry rest' _ =>
    simp [CNF.vars, List.count_cons, beq_iff_eq, Nat.add_comm]

private theorem count_vars_splitAux_fresh_le {W : Type*} [BEq W] [LawfulBEq W] (fresh : ℕ → W)
    (hinj : Function.Injective fresh) (k₀ j : ℕ) (carry : Literal W) (rest : Clause W)
    (hrest : ∀ l ∈ rest, ∀ k, l.1 ≠ fresh k) (hcarry : ∀ k, j ≤ k → carry.1 ≠ fresh k) :
    (Clause.splitAux fresh j carry rest).vars.count (fresh k₀) ≤ 2 := by
  fun_induction Clause.splitAux fresh j carry rest with
  | case1 j carry b c d rest' ih =>
    simp only [CNF.vars, List.flatten_cons, List.map_append, List.count_append]
    have h0 : (rest'.map Prod.fst).count (fresh k₀) = 0 :=
      List.count_eq_zero.2 fun hw ↦
        let ⟨l, hl, he⟩ := List.mem_map.1 hw
        hrest l (List.mem_cons_of_mem b (List.mem_cons_of_mem c (List.mem_cons_of_mem d hl))) k₀ he
    have hb0 : b.1 ≠ fresh k₀ := hrest b List.mem_cons_self k₀
    have hc0' : c.1 ≠ fresh k₀ := hrest c (by simp) k₀
    have hd0' : d.1 ≠ fresh k₀ := hrest d (by simp) k₀
    by_cases hk : k₀ < j
    · have htail := count_vars_splitAux_of_ne fresh (j + 1) (fresh j, false)
        (c :: d :: rest') (fresh k₀) (fun k _ ↦ hinj.ne (by omega))
      simp only [CNF.vars] at htail
      rw [htail]
      have hj0 : fresh j ≠ fresh k₀ := hinj.ne (by omega)
      simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, beq_iff_eq,
        hb0, hc0', hd0', hj0, h0, ↓reduceIte]
      split_ifs <;> omega
    · rcases eq_or_lt_of_le (Nat.not_lt.1 hk) with hjk | hgt
      · subst j
        have htail := count_vars_splitAux_of_ne fresh (k₀ + 1) (fresh k₀, false)
          (c :: d :: rest') (fresh k₀) (fun k _ ↦ hinj.ne (by omega))
        simp only [CNF.vars] at htail
        rw [htail]
        have hc0 : carry.1 ≠ fresh k₀ := hcarry k₀ le_rfl
        simp [hc0, hb0, hc0', hd0', h0]
      · have hj0 : fresh j ≠ fresh k₀ := hinj.ne (by omega)
        have hhead : ([carry, b, (fresh j, true)].map Prod.fst).count (fresh k₀) = 0 := by
          simp [hcarry k₀ (by omega), hb0, hj0]
        rw [hhead, zero_add]
        simpa only [CNF.vars] using ih (fun l hl k ↦ hrest l (List.mem_cons_of_mem b hl) k)
          (fun k _ ↦ hinj.ne (by omega))
  | case2 j carry rest' _ =>
    have h0 : (rest'.map Prod.fst).count (fresh k₀) = 0 :=
      List.count_eq_zero.2 fun hw ↦ let ⟨l, hl, he⟩ := List.mem_map.1 hw; hrest l hl k₀ he
    simp only [CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons,
      List.count_cons, beq_iff_eq, h0]
    split_ifs <;> omega

private def maxOccStage2 (cardα cardD : ℕ) : ℕ :=
  2 * cardα ^ 2 * (1 + cardD)

private theorem two_le_maxOccStage2 {cardα cardD : ℕ} (hα : 0 < cardα) :
    2 ≤ maxOccStage2 cardα cardD := by
  have h3 : 1 ≤ cardα ^ 2 * (1 + cardD) :=
    Nat.mul_pos (Nat.pow_pos hα) (Nat.le_add_right 1 cardD)
  simpa [maxOccStage2, Nat.mul_assoc] using Nat.mul_le_mul_left 2 h3

private theorem count_vars_to3CNF_le {Δ₀ : ℕ} (hΔ₀ : 2 ≤ Δ₀) {φ : CNF ℕ}
    (hφ : ∀ x, φ.vars.count x ≤ Δ₀) (y : ℕ ⊕ (ℕ × ℕ)) :
    φ.to3CNF.vars.count y ≤ Δ₀ := by
  rw [CNF.to3CNF, vars_flatMap, List.count_flatMap]
  cases y with
  | inl x =>
    have hclause (p : Clause ℕ × ℕ) :
        (Clause.split3 (fun j ↦ Sum.inr (p.2, j)) 0 (p.1.relabel Sum.inl)).vars.count
          (Sum.inl x) = (p.1.map Prod.fst).count x := by
      cases hp : p.1 with
      | nil => simp [Clause.split3, Clause.relabel, CNF.vars]
      | cons hd tl =>
        simp only [Clause.relabel, List.map_cons, Clause.split3]
        have hs := count_vars_splitAux_of_ne (fun j ↦ Sum.inr (p.2, j)) 0
          (Prod.map Sum.inl id hd) (tl.map (Prod.map Sum.inl id)) (Sum.inl x)
          (fun _ _ ↦ Sum.inr_ne_inl)
        rw [hs]
        have hmap : ((tl.map (Prod.map (Sum.inl (β := ℕ × ℕ)) id)).map Prod.fst).count
            (Sum.inl x) = (tl.map Prod.fst).count x := by
          rw [show (tl.map (Prod.map (Sum.inl (β := ℕ × ℕ)) id)).map Prod.fst =
            (tl.map Prod.fst).map (Sum.inl (β := ℕ × ℕ)) by simp [List.map_map]]
          exact List.count_map_of_injective _ _ (Sum.inl_injective (α := ℕ) (β := ℕ × ℕ)) x
        rw [hmap]
        simp [Prod.map, List.count_cons, beq_iff_eq, Nat.add_comm]
    simp_rw [Function.comp_def, hclause]
    have hzip : (φ.zipIdx.map fun p ↦ (p.1.map Prod.fst).count x) =
        φ.map fun c ↦ (c.map Prod.fst).count x := by
      conv_rhs => rw [← List.zipIdx_map_fst 0 φ, List.map_map]
      rfl
    rw [hzip, sum_map_count_vars]
    exact hφ x
  | inr ik =>
    rcases ik with ⟨i₀, k₀⟩
    have hzero (p : Clause ℕ × ℕ) (hne : p.2 ≠ i₀) :
        (Clause.split3 (fun j ↦ Sum.inr (p.2, j)) 0 (p.1.relabel Sum.inl)).vars.count
          (Sum.inr (i₀, k₀)) = 0 := by
      cases hp : p.1 with
      | nil => simp [Clause.split3, Clause.relabel, CNF.vars]
      | cons hd tl =>
        simp only [Clause.relabel, List.map_cons, Clause.split3]
        have hs := count_vars_splitAux_of_ne (fun j ↦ Sum.inr (p.2, j)) 0
          (Prod.map Sum.inl id hd) (tl.map (Prod.map Sum.inl id)) (Sum.inr (i₀, k₀))
          (fun k _ h ↦ hne (Prod.mk.inj (Sum.inr.inj h)).1)
        rw [hs]
        simp [Prod.map, Function.comp_def, List.count_eq_zero]
    have hbound (p : Clause ℕ × ℕ) :
        (Clause.split3 (fun j ↦ Sum.inr (p.2, j)) 0 (p.1.relabel Sum.inl)).vars.count
          (Sum.inr (p.2, k₀)) ≤ 2 := by
      cases hp : p.1 with
      | nil => simp [Clause.split3, Clause.relabel, CNF.vars]
      | cons hd tl =>
        simp only [Clause.relabel, List.map_cons, Clause.split3]
        refine count_vars_splitAux_fresh_le (fun j ↦ Sum.inr (p.2, j))
          (fun a b h ↦ (Prod.mk.inj (Sum.inr.inj h)).2) k₀ 0
          (Prod.map (Sum.inl (β := ℕ × ℕ)) id hd)
          (tl.map (Prod.map (Sum.inl (β := ℕ × ℕ)) id)) ?_
          (fun _ _ ↦ Sum.inl_ne_inr)
        intro l hl _
        obtain ⟨l₀, _, rfl⟩ := List.mem_map.1 hl
        exact Sum.inl_ne_inr
    simp only [Function.comp_def]
    rw [sum_zipIdx_single φ _ i₀ (fun p _ hne ↦ hzero p hne)]
    split_ifs with hmem
    · exact (hbound (φ[i₀], i₀)).trans hΔ₀
    · exact Nat.zero_le _

private theorem count_vars_toBoundedWidthThreeCNF_le {α D : Type} [Fintype α] [DecidableEq α]
    [Fintype D] {k : ℕ} (e : α ≃ (Fin k → Bool))
    (pairs : List (α × α)) (hlen_pairs : pairs.length = Fintype.card α ^ 2)
    (fallback : α → α → Bool) (family : (n : ℕ) → Cslib.RotationMap (Fin n) D)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    (hlen_labels : labels.length = Fintype.card D) (g : Graph (α → α → Bool)) (v : ℕ) :
    (toBoundedWidthThreeCNF e pairs fallback rotate labels g).vars.count v ≤
      maxOccStage2 (Fintype.card α) (Fintype.card D) := by
  classical
  have : Nonempty α := ⟨e.symm fun _ ↦ false⟩
  refine CNF.count_vars_relabel_le_of_injOn _ _ splitVarToNat_injective.injOn
    (count_vars_to3CNF_le (two_le_maxOccStage2 Fintype.card_pos) fun x ↦ ?_) v
  refine (count_vars_toCNF_le e pairs (degreeReduceTwoCSP fallback rotate labels g) x).trans ?_
  have hs := countP_src_degreeReduceTwoCSP_le fallback rotate labels hlen_labels g x.unpair.1
  have hd := countP_dst_degreeReduceTwoCSP_le fallback family rotate hrotate labels hlabels hmem
    g x.unpair.1
  calc pairs.length *
        (((degreeReduceTwoCSP fallback rotate labels g).edges.countP fun d ↦
            decide (d.src = x.unpair.1)) +
          ((degreeReduceTwoCSP fallback rotate labels g).edges.countP fun d ↦
            decide (d.dst = x.unpair.1)))
      ≤ Fintype.card α ^ 2 * ((1 + Fintype.card D) + (1 + Fintype.card D)) := by
        rw [hlen_pairs]; exact Nat.mul_le_mul_left _ (Nat.add_le_add hs hd)
    _ = maxOccStage2 (Fintype.card α) (Fintype.card D) := by
        dsimp only [maxOccStage2]; ring

/-! ### Stage 3: Clause doubling and `toThreeSATThree` occurrence splitting -/

private theorem nodup_vars_of_mem_implicationPath {W : Type*} (first current : W) (rest : List W)
    (hnd : (current :: rest).Nodup) (hne : rest = [] → current ≠ first)
    (hfirst : ∀ x ∈ rest, x ≠ first) :
    ∀ c ∈ CNF.implicationPath first current rest, (c.map Prod.fst).Nodup := by
  fun_induction CNF.implicationPath first current rest with
  | case1 cur => intro c hc; obtain rfl := List.mem_singleton.1 hc; simp [hne rfl]
  | case2 cur nxt rst ih =>
    rw [List.nodup_cons] at hnd
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · simp [show cur ≠ nxt from fun h ↦ hnd.1 (h ▸ List.mem_cons_self)]
    · exact ih hnd.2 (fun _ ↦ hfirst nxt List.mem_cons_self)
        (fun x hx ↦ hfirst x (List.mem_cons_of_mem _ hx)) c hc

private theorem nodup_vars_of_mem_implicationCycle {W : Type*} {vs : List W}
    (hnd : vs.Nodup) (hlen : 2 ≤ vs.length) :
    ∀ c ∈ CNF.implicationCycle vs, (c.map Prod.fst).Nodup := by
  match vs, hlen with
  | first :: next :: rest, _ =>
    rw [List.nodup_cons] at hnd
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · simp [show first ≠ next from fun h ↦ hnd.1 (h ▸ List.mem_cons_self)]
    · exact nodup_vars_of_mem_implicationPath first next rest hnd.2
        (fun _ h ↦ hnd.1 (h ▸ List.mem_cons_self))
        (fun x hx h ↦ hnd.1 (h ▸ List.mem_cons_of_mem _ hx)) c hc

private theorem isExactThreeDistinct_occurrenceClauses {V : Type*} {φ : CNF V}
    (h3 : ∀ c ∈ φ, c.length = 3) :
    φ.occurrenceClauses.IsExactThreeDistinct := by
  have hsub (ψ : CNF (V × ℕ × ℕ)) (hψ : ψ.vars.Nodup) : ∀ c ∈ ψ, (c.map Prod.fst).Nodup := by
    induction ψ with
    | nil => simp
    | cons c rest ih =>
      simp only [CNF.vars, List.flatten_cons, List.map_append, List.nodup_append] at hψ
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hψ.1
      · exact ih hψ.2.1 d hd
  intro c hc
  refine ⟨?_, hsub _ (CNF.nodup_vars_occurrenceClauses φ) c hc⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  simpa using h3 d.1 (List.fst_mem_of_mem_zipIdx hd)

private theorem countP_clause_any_le_countP_vars {W : Type*} (Φ : CNF W) (p : W → Bool) :
    (Φ.countP fun c ↦ c.any fun l ↦ p l.1) ≤ Φ.vars.countP p := by
  induction Φ with
  | nil => simp [CNF.vars]
  | cons c rest ih =>
    simp only [List.countP_cons]
    have hvars : CNF.vars (c :: rest) = c.map Prod.fst ++ CNF.vars rest := by
      simp [CNF.vars, List.flatten_cons, List.map_append]
    rw [hvars, List.countP_append]
    have hc : (if (c.any fun l ↦ p l.1) = true then 1 else 0) ≤ (c.map Prod.fst).countP p := by
      by_cases h : (c.any fun l ↦ p l.1) = true
      · simp only [h, ↓reduceIte]
        obtain ⟨l, hl, hpl⟩ := List.any_eq_true.1 h
        exact List.countP_pos_iff.2 ⟨l.1, List.mem_map_of_mem hl, hpl⟩
      · simp [h]
    omega

private theorem countP_le_sum_map {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ)
    (h : ∀ x ∈ l, p x = true → 1 ≤ f x) :
    l.countP p ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    have ihr := ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    cases ha : p a
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · have := h a List.mem_cons_self ha; simp only [↓reduceIte]; omega

private theorem countUnsat_le_mul_countUnsat_toThreeOccurrence {φ : CNF ℕ} {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hocc : ∀ v, φ.vars.count v ≤ Δ) (τ : ℕ × ℕ × ℕ → Bool) :
    ∃ σ : ℕ → Bool, φ.countUnsat σ ≤ Δ * φ.toThreeOccurrence.countUnsat τ := by
  let σ : ℕ → Bool := fun v ↦ τ ((φ.occurrenceCopies v).headD (v, 0, 0))
  refine ⟨σ, ?_⟩
  let φ_ter : CNF (ℕ × ℕ × ℕ) := φ.occurrenceClauses
  let φ_bin : CNF (ℕ × ℕ × ℕ) :=
    φ.distinctVars.flatMap fun v ↦ CNF.implicationCycle (φ.occurrenceCopies v)
  have hsplit : φ.toThreeOccurrence.countUnsat τ = φ_ter.countUnsat τ + φ_bin.countUnsat τ := by
    simp [CNF.toThreeOccurrence, φ_ter, φ_bin, CNF.countUnsat, List.countP_append]
  have hter_eq : φ.countUnsat σ = φ_ter.countUnsat (σ ∘ Prod.fst) := by
    conv_lhs => rw [← CNF.relabel_occurrenceClauses φ, CNF.countUnsat_relabel]
  let P : ℕ × ℕ × ℕ → Bool := fun x ↦ decide (τ x ≠ σ x.1)
  have hdiff : φ_ter.countUnsat (σ ∘ Prod.fst) ≤
      φ_ter.countUnsat τ + (φ_ter.countP fun c ↦ c.any fun l ↦ P l.1) := by
    simp only [CNF.countUnsat]
    induction φ_ter with
    | nil => simp
    | cons c rest ih =>
      simp only [List.countP_cons]
      cases hc : c.eval τ
      · cases c.eval (σ ∘ Prod.fst) <;> cases c.any (fun l ↦ P l.1) <;> simp <;> omega
      · cases hs : c.eval (σ ∘ Prod.fst)
        · have hany : (c.any fun l ↦ P l.1) = true := by
            obtain ⟨l, hl, hlt⟩ := (Clause.eval_eq_true_iff τ c).1 hc
            refine List.any_eq_true.2 ⟨l, hl, decide_eq_true fun heq ↦ ?_⟩
            have htr := (Clause.eval_eq_true_iff (σ ∘ Prod.fst) c).2 ⟨l, hl, heq.symm.trans hlt⟩
            simp [hs] at htr
          simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, hany, ↓reduceIte]; omega
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; omega
  let badPred : ℕ → Bool := fun v ↦ !(CNF.implicationCycle (φ.occurrenceCopies v)).eval τ
  have hP_imp (x : ℕ × ℕ × ℕ) (hx : x ∈ φ_ter.vars) (hPx : P x = true) :
      badPred x.1 = true := by
    have hmem_c : x ∈ φ.occurrenceCopies x.1 := by
      simpa [CNF.occurrenceCopies, φ_ter] using hx
    have hhead_mem : (φ.occurrenceCopies x.1).headD (x.1, 0, 0) ∈ φ.occurrenceCopies x.1 := by
      cases hls : φ.occurrenceCopies x.1 with
      | nil => exact absurd hls (List.ne_nil_of_mem hmem_c)
      | cons a rest => simp
    simp only [badPred, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, CNF.eval_implicationCycle]
    exact fun hall ↦ of_decide_eq_true hPx (hall x hmem_c _ hhead_mem)
  have hcountP_le : φ_ter.vars.countP P ≤ φ.vars.countP badPred := by
    have hmono {α : Type} (xs : List α) (p q : α → Bool)
        (hpq : ∀ x ∈ xs, p x = true → q x = true) : xs.countP p ≤ xs.countP q := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.countP_cons]
        have ihr := ih fun x hx ↦ hpq x (List.mem_cons_of_mem _ hx)
        cases ha : p a
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihr.trans (Nat.le_add_right _ _)
        · simp [hpq a List.mem_cons_self ha]; omega
    have h2 : φ_ter.vars.countP (fun x : ℕ × ℕ × ℕ ↦ badPred x.1) = φ.vars.countP badPred := by
      conv_rhs => rw [← CNF.map_fst_vars_occurrenceClauses φ, List.countP_map]
      rfl
    exact (hmono φ_ter.vars P (fun x : ℕ × ℕ × ℕ ↦ badPred x.1) hP_imp).trans_eq h2
  have hbad_vars : φ.vars.countP badPred ≤ Δ * (φ.distinctVars.countP badPred) := by
    let m := φ.vars.filter badPred
    let b := φ.distinctVars.filter badPred
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
    change m.length ≤ Δ * b.length
    have hcnt_filt (l : List ℕ) (v : ℕ) : (l.filter badPred).count v ≤ l.count v := by
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.filter_cons]; split_ifs <;> simp [List.count_cons] <;> omega
    have hlen_m : m.length ≤ m.dedup.length * Δ := by
      rw [← List.sum_map_count_dedup_eq_length]
      refine (List.sum_le_length_nsmul _ Δ fun n hn ↦ ?_).trans_eq (by simp [smul_eq_mul])
      obtain ⟨v, _, rfl⟩ := List.mem_map.1 hn
      exact (hcnt_filt φ.vars v).trans (hocc v)
    have hsub_fin : m.dedup.toFinset ⊆ b.toFinset := fun v hv ↦ by
      obtain ⟨hvm, hvb⟩ := List.mem_filter.1 (List.mem_dedup.1 (List.mem_toFinset.1 hv))
      exact List.mem_toFinset.2 (List.mem_filter.2 ⟨CNF.mem_distinctVars.2 hvm, hvb⟩)
    have hb_nd : b.Nodup := (CNF.nodup_distinctVars φ).filter _
    have hdedup_le : m.dedup.length ≤ b.length := by
      rw [← List.toFinset_card_of_nodup (List.nodup_dedup m),
        ← List.toFinset_card_of_nodup hb_nd]
      exact Finset.card_le_card hsub_fin
    exact hlen_m.trans ((Nat.mul_le_mul_right Δ hdedup_le).trans_eq (Nat.mul_comm _ _))
  have hbin_ge : φ.distinctVars.countP badPred ≤ φ_bin.countUnsat τ := by
    simp only [φ_bin, CNF.countUnsat, List.countP_flatMap]
    refine countP_le_sum_map _ _ _ fun v _ hv ↦ ?_
    simp only [badPred, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      CNF.eval_eq_true_iff, not_forall] at hv
    obtain ⟨c, hc, hce⟩ := hv
    exact List.countP_pos_iff.2 ⟨c, hc, by simpa using hce⟩
  have hany_le := (countP_clause_any_le_countP_vars φ_ter P).trans
    (hcountP_le.trans (hbad_vars.trans (Nat.mul_le_mul_left Δ hbin_ge)))
  rw [hter_eq, hsplit, Nat.mul_add]
  have hter_mul : φ_ter.countUnsat τ ≤ Δ * φ_ter.countUnsat τ := Nat.le_mul_of_pos_left _ hΔ
  omega

/-! ### Stage 4: The `13`-clause exact-`3`-distinct octahedron gadget -/

/-- Expand a binary clause `(l₁ ∨ l₂)` at clause index `i` into `13` exact-`3`-distinct clauses
using `7` fresh variables `8 * i + 1, …, 8 * i + 7` so that `l₁` and `l₂` each appear twice and
each of the `7` fresh variables appears `5` times. -/
private def binaryGadget13 (l₁ l₂ : Literal ℕ) (i : ℕ) : CNF ℕ :=
  let a := (8 * l₁.1, l₁.2); let b := (8 * l₂.1, l₂.2); let z := 8 * i + 1
  let w₁ := 8 * i + 2; let w₂ := 8 * i + 3; let w₃ := 8 * i + 4
  let w₄ := 8 * i + 5; let w₅ := 8 * i + 6; let w₆ := 8 * i + 7
  [ [a, b, (z, true)], [a, b, (z, false)],
    [(z, true), (w₁, true), (w₂, true)], [(z, true), (w₃, true), (w₄, true)],
    [(z, true), (w₅, true), (w₆, true)],
    [(w₁, true), (w₃, true), (w₅, true)], [(w₁, true), (w₃, true), (w₆, true)],
    [(w₁, true), (w₄, true), (w₅, true)], [(w₁, true), (w₄, true), (w₆, true)],
    [(w₂, true), (w₃, true), (w₅, true)], [(w₂, true), (w₃, true), (w₆, true)],
    [(w₂, true), (w₄, true), (w₅, true)], [(w₂, true), (w₄, true), (w₆, true)] ]

private def expandClauseFiveOcc (p : Clause ℕ × ℕ) : CNF ℕ :=
  if p.1.length == 2 then
    binaryGadget13 (p.1.headD (0, true)) (p.1.tail.headD (0, true)) p.2
  else
    [p.1.relabel (8 * ·)]

private def expandFiveOcc (ψ : CNF ℕ) : CNF ℕ :=
  ψ.zipIdx.flatMap expandClauseFiveOcc

private theorem isPolyTime_mul8 :
    ComputableInPolyTime (fun v : ℕ ↦ 8 * v) encNat encNat :=
  ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 8) ComputableInPolyTime.id'

private theorem isPolyTime_expandClauseFiveOcc :
    ComputableInPolyTime expandClauseFiveOcc
      (encPair (encClause encNat) encUnary) encCNF := by
  have hc := ComputableInPolyTime.fst (encClause encNat) encUnary
  have hi_bin := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.snd (encClause encNat) encUnary)
  have h8i := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 8) hi_bin
  have hfresh (r : ℕ) := ComputableInPolyTime.binary_add' h8i (ComputableInPolyTime.const r)
  have hl1 := ComputableInPolyTime.listHeadDWithInput hc (ComputableInPolyTime.const (0, true))
  have hl2 := ComputableInPolyTime.listHeadDWithInput
    ((ComputableInPolyTime.listTail (encPair encNat encBool)).comp hc)
    (ComputableInPolyTime.const (0, true))
  have ha := (isPolyTime_mul8.comp hl1.fst').prod hl1.snd'
  have hb := (isPolyTime_mul8.comp hl2.fst').prod hl2.snd'
  have hpos (r : ℕ) := (hfresh r).prod (ComputableInPolyTime.const (encOut := encBool) true)
  have hneg1 := (hfresh 1).prod (ComputableInPolyTime.const (encOut := encBool) false)
  have hcl3 {f₁ f₂ f₃ : Clause ℕ × ℕ → Literal ℕ}
      (h₁ : ComputableInPolyTime f₁ (encPair (encClause encNat) encUnary) (encPair encNat encBool))
      (h₂ : ComputableInPolyTime f₂ (encPair (encClause encNat) encUnary) (encPair encNat encBool))
      (h₃ : ComputableInPolyTime f₃ (encPair (encClause encNat) encUnary)
        (encPair encNat encBool)) :
      ComputableInPolyTime (fun p ↦ [f₁ p, f₂ p, f₃ p])
        (encPair (encClause encNat) encUnary) (encClause encNat) :=
    h₁.cons' (h₂.cons' (h₃.cons' (ComputableInPolyTime.const (encOut := encClause encNat) [])))
  have hgad : ComputableInPolyTime
      (fun p : Clause ℕ × ℕ ↦
        binaryGadget13 (p.1.headD (0, true)) (p.1.tail.headD (0, true)) p.2)
      (encPair (encClause encNat) encUnary) encCNF := by
    unfold binaryGadget13
    exact (hcl3 ha hb (hpos 1)).cons' <| (hcl3 ha hb hneg1).cons' <|
      (hcl3 (hpos 1) (hpos 2) (hpos 3)).cons' <| (hcl3 (hpos 1) (hpos 4) (hpos 5)).cons' <|
      (hcl3 (hpos 1) (hpos 6) (hpos 7)).cons' <| (hcl3 (hpos 2) (hpos 4) (hpos 6)).cons' <|
      (hcl3 (hpos 2) (hpos 4) (hpos 7)).cons' <| (hcl3 (hpos 2) (hpos 5) (hpos 6)).cons' <|
      (hcl3 (hpos 2) (hpos 5) (hpos 7)).cons' <| (hcl3 (hpos 3) (hpos 4) (hpos 6)).cons' <|
      (hcl3 (hpos 3) (hpos 4) (hpos 7)).cons' <| (hcl3 (hpos 3) (hpos 5) (hpos 6)).cons' <|
      (hcl3 (hpos 3) (hpos 5) (hpos 7)).cons' (ComputableInPolyTime.const (encOut := encCNF) [])
  have hrel := ((Clause.computableInPolyTime_relabel isPolyTime_mul8).comp hc).cons'
    (ComputableInPolyTime.const (encOut := encCNF) [])
  have hcond := ComputableInPolyTime.unary_beq (Clause.computableInPolyTime_length hc)
    (ComputableInPolyTime.const (encOut := encUnary) 2)
  exact hcond.ite hgad hrel

private theorem isPolyTime_expandFiveOcc :
    ComputableInPolyTime expandFiveOcc encCNF encCNF := by
  unfold expandFiveOcc
  exact ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.zipIdx (encClause encNat))
    (isPolyTime_expandClauseFiveOcc.comp (ComputableInPolyTime.snd _ _))

private theorem isExactThreeDistinct_binaryGadget13 {l₁ l₂ : Literal ℕ} (hne : l₁.1 ≠ l₂.1)
    (i : ℕ) : (binaryGadget13 l₁ l₂ i).IsExactThreeDistinct := by
  intro c hc
  simp only [binaryGadget13, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Clause.isExactThreeDistinct_iff.2 ⟨_, _, _, rfl, by omega, by omega, by omega⟩

private theorem count_vars_binaryGadget13_mul8 (l₁ l₂ : Literal ℕ) (i v : ℕ) :
    (binaryGadget13 l₁ l₂ i).vars.count (8 * v) =
      2 * ([l₁, l₂].map Prod.fst).count v := by
  simp only [binaryGadget13, CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_cons, List.map_nil, List.map_append, List.count_cons, List.count_nil,
    List.count_append, beq_iff_eq]
  have hne (r : ℕ) (hr1 : 1 ≤ r) (hr7 : r ≤ 7) : 8 * i + r ≠ 8 * v := by omega
  simp only [hne 1 (by omega) (by omega), hne 2 (by omega) (by omega),
    hne 3 (by omega) (by omega), hne 4 (by omega) (by omega),
    hne 5 (by omega) (by omega), hne 6 (by omega) (by omega),
    hne 7 (by omega) (by omega), ↓reduceIte, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  split_ifs <;> omega

private theorem count_vars_binaryGadget13_rem (l₁ l₂ : Literal ℕ) (i w : ℕ)
    (hw : w % 8 ≠ 0) :
    (binaryGadget13 l₁ l₂ i).vars.count w = if w / 8 = i then 5 else 0 := by
  simp only [binaryGadget13, CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_cons, List.map_nil, List.map_append, List.count_cons, List.count_nil,
    List.count_append, beq_iff_eq]
  have ha : 8 * l₁.1 ≠ w := by omega
  have hb : 8 * l₂.1 ≠ w := by omega
  simp only [ha, hb, ↓reduceIte]
  by_cases hi : w / 8 = i
  · simp only [hi, ↓reduceIte]
    have hrem : w % 8 = 1 ∨ w % 8 = 2 ∨ w % 8 = 3 ∨ w % 8 = 4 ∨
        w % 8 = 5 ∨ w % 8 = 6 ∨ w % 8 = 7 := by omega
    rcases hrem with hr | hr | hr | hr | hr | hr | hr <;>
      · have hw_eq : w = 8 * i + (w % 8) := by omega
        rw [hw_eq, hr]; simp
  · have hne_r (r : ℕ) (hr : r < 8) : 8 * i + r ≠ w := by omega
    simp only [hi, hne_r 1 (by decide), hne_r 2 (by decide), hne_r 3 (by decide),
      hne_r 4 (by decide), hne_r 5 (by decide), hne_r 6 (by decide), hne_r 7 (by decide),
      ↓reduceIte]

private theorem isExactThreeDistinct_expandFiveOcc {ψ : CNF ℕ}
    (hψ : ∀ c ∈ ψ, c.IsExactThreeDistinct ∨ (c.length = 2 ∧ (c.map Prod.fst).Nodup)) :
    (expandFiveOcc ψ).IsExactThreeDistinct := by
  intro d hd
  simp only [expandFiveOcc, List.mem_flatMap] at hd
  obtain ⟨⟨c, i⟩, hci, hd⟩ := hd
  have hc := List.fst_mem_of_mem_zipIdx hci
  rcases hψ c hc with hc3 | ⟨hc2, hcnd⟩
  · have h2f : (c.length == 2) = false := by simp [hc3.length_eq]
    simp only [expandClauseFiveOcc, h2f, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hd
    subst hd
    exact hc3.relabel_of_injOn fun x _ y _ hxy ↦ by omega
  · match c, hc2 with
    | [l₁, l₂], _ =>
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, List.nodup_nil, and_true] at hcnd
      simp only [expandClauseFiveOcc, List.length_cons, List.length_nil, beq_self_eq_true,
        ↓reduceIte, List.headD_cons, List.tail_cons] at hd
      exact isExactThreeDistinct_binaryGadget13 (fun h ↦ hcnd.1 h) i d hd

private theorem count_vars_expandFiveOcc_eq_zero_or_five {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length = 3) (w : ℕ) :
    (expandFiveOcc (toThreeSATThree φ)).vars.count w = 0 ∨
      (expandFiveOcc (toThreeSATThree φ)).vars.count w = 5 := by
  have hw_le : ∀ c ∈ φ, c.length ≤ 3 := fun c hc ↦ (h3 c hc).le
  set ψ := toThreeSATThree φ
  have hψ_def : ψ = φ.toThreeOccurrence.relabel ThreeSATThree.numberCopy := by
    simp +contextual [ψ, toThreeSATThree, hw_le]
  let ψ_ter : CNF ℕ := φ.occurrenceClauses.relabel ThreeSATThree.numberCopy
  let ψ_bin : CNF ℕ := CNF.relabel ThreeSATThree.numberCopy
    (φ.distinctVars.flatMap fun v ↦ CNF.implicationCycle (φ.occurrenceCopies v))
  have hψ_split : ψ = ψ_ter ++ ψ_bin := by
    simp [hψ_def, CNF.toThreeOccurrence, ψ_ter, ψ_bin, CNF.relabel]
  have hter_len : ∀ c ∈ ψ_ter, c.length = 3 := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [Clause.length_relabel]
    exact (isExactThreeDistinct_occurrenceClauses h3 d hd).length_eq
  have hbin_len : ∀ c ∈ ψ_bin, c.length = 2 := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [Clause.length_relabel]
    obtain ⟨v, _, hd⟩ := List.mem_flatMap.1 hd
    exact CNF.length_of_mem_implicationCycle _ hd
  have hψ_len : ∀ c ∈ ψ, c.length = 3 ∨ c.length = 2 := by
    intro c hc
    rw [hψ_split, List.mem_append] at hc
    exact hc.imp (hter_len c) (hbin_len c)
  rw [expandFiveOcc, vars_flatMap, List.count_flatMap]
  simp only [Function.comp_def]
  by_cases hrem : w % 8 = 0
  · obtain ⟨v, rfl⟩ : ∃ v, w = 8 * v := ⟨w / 8, by omega⟩
    have hstep (p : Clause ℕ × ℕ) (hp : p ∈ ψ.zipIdx) :
        (expandClauseFiveOcc p).vars.count (8 * v) =
          (if p.1.length == 2 then 2 else 1) * (p.1.map Prod.fst).count v := by
      rcases hψ_len p.1 (List.fst_mem_of_mem_zipIdx hp) with h3p | h2p
      · have h2f : (p.1.length == 2) = false := by simp [h3p]
        simp only [expandClauseFiveOcc, h2f, Bool.false_eq_true, ↓reduceIte,
          one_mul, CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil, Clause.relabel,
          List.map_map, Function.comp_def, Prod.map_fst]
        rw [show List.map (fun x : Literal ℕ ↦ 8 * x.1) p.1 = (p.1.map Prod.fst).map (8 * ·) by
          simp [List.map_map]]
        exact List.count_map_of_injective (p.1.map Prod.fst) (8 * ·)
          (fun a b (h : 8 * a = 8 * b) ↦ by omega) v
      · match hp1 : p.1, h2p with
        | [l₁, l₂], _ =>
          rw [expandClauseFiveOcc, hp1]
          simp only [List.length_cons, List.length_nil, beq_self_eq_true,
            ↓reduceIte, List.headD_cons, List.tail_cons]
          exact count_vars_binaryGadget13_mul8 l₁ l₂ p.2 v
    have hmap_eq : (ψ.zipIdx.map fun p ↦ (expandClauseFiveOcc p).vars.count (8 * v)) =
        ψ.map fun c ↦ (if c.length == 2 then 2 else 1) * (c.map Prod.fst).count v := by
      rw [List.map_congr_left fun p hp ↦ hstep p hp]
      conv_rhs => rw [← List.zipIdx_map_fst 0 ψ, List.map_map]
      rfl
    rw [hmap_eq, hψ_split, List.map_append, List.sum_append]
    have hsum_ter : (ψ_ter.map fun c ↦
        (if c.length == 2 then 2 else 1) * (c.map Prod.fst).count v).sum =
        ψ_ter.vars.count v := by
      have hc : (ψ_ter.map fun c ↦ (if c.length == 2 then 2 else 1) * (c.map Prod.fst).count v) =
          ψ_ter.map fun c ↦ (c.map Prod.fst).count v :=
        List.map_congr_left fun c hc ↦ by simp [hter_len c hc]
      rw [hc, sum_map_count_vars]
    have hsum_bin : (ψ_bin.map fun c ↦
        (if c.length == 2 then 2 else 1) * (c.map Prod.fst).count v).sum =
        2 * ψ_bin.vars.count v := by
      have hc : (ψ_bin.map fun c ↦ (if c.length == 2 then 2 else 1) * (c.map Prod.fst).count v) =
          ψ_bin.map fun c ↦ 2 * (c.map Prod.fst).count v :=
        List.map_congr_left fun c hc ↦ by simp [hbin_len c hc]
      rw [hc, List.sum_map_mul_left, sum_map_count_vars]
    rw [hsum_ter, hsum_bin]
    by_cases hv : ∃ x, ThreeSATThree.numberCopy x = v
    · obtain ⟨x, rfl⟩ := hv
      have hcnt_ter : ψ_ter.vars.count (ThreeSATThree.numberCopy x) =
          φ.occurrenceClauses.vars.count x := by
        simp only [ψ_ter, CNF.vars_relabel]
        exact List.count_map_of_injective _ _ ThreeSATThree.numberCopy_injective x
      have hcnt_all : ψ.vars.count (ThreeSATThree.numberCopy x) =
          3 * φ.occurrenceClauses.vars.count x := by
        rw [hψ_def, CNF.vars_relabel,
          List.count_map_of_injective _ _ ThreeSATThree.numberCopy_injective x,
          CNF.count_vars_toThreeOccurrence]
      have hcnt_split : ψ.vars.count (ThreeSATThree.numberCopy x) =
          ψ_ter.vars.count (ThreeSATThree.numberCopy x) +
            ψ_bin.vars.count (ThreeSATThree.numberCopy x) := by
        rw [hψ_split, cnf_vars_append, List.count_append]
      have hle1 := List.nodup_iff_count_le_one.1 (CNF.nodup_vars_occurrenceClauses φ) x
      rcases Nat.eq_zero_or_pos (φ.occurrenceClauses.vars.count x) with h0 | hpos
      · left; omega
      · right; omega
    · push Not at hv
      have hnot_ter : v ∉ ψ_ter.vars := by
        simp only [ψ_ter, CNF.vars_relabel, List.mem_map, not_exists, not_and]
        intro x _; exact hv x
      have hnot_bin : v ∉ ψ_bin.vars := by
        simp only [ψ_bin, CNF.vars_relabel, List.mem_map, not_exists, not_and]
        intro x _; exact hv x
      left; simp [List.count_eq_zero.2 hnot_ter, List.count_eq_zero.2 hnot_bin]
  · set i₀ := w / 8
    have hzero (p : Clause ℕ × ℕ) (hp : p ∈ ψ.zipIdx) (hne : p.2 ≠ i₀) :
        (expandClauseFiveOcc p).vars.count w = 0 := by
      rcases hψ_len p.1 (List.fst_mem_of_mem_zipIdx hp) with h3p | h2p
      · have h2f : (p.1.length == 2) = false := by simp [h3p]
        simp only [expandClauseFiveOcc, h2f, Bool.false_eq_true, ↓reduceIte,
          CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil, Clause.relabel,
          List.map_map, Function.comp_def, Prod.map_fst, List.count_eq_zero, List.mem_map,
          not_exists, not_and]
        intro l _ heq; omega
      · match hp1 : p.1, h2p with
        | [l₁, l₂], _ =>
          rw [expandClauseFiveOcc, hp1]
          simp only [List.length_cons, List.length_nil, beq_self_eq_true,
            ↓reduceIte, List.headD_cons, List.tail_cons]
          rw [count_vars_binaryGadget13_rem l₁ l₂ p.2 w hrem]
          have hw_ne : w / 8 ≠ p.2 := hne.symm
          simp only [hw_ne, ↓reduceIte]
    rw [sum_zipIdx_single ψ _ i₀ hzero]
    split_ifs with hlt
    · rcases hψ_len ψ[i₀] (List.getElem_mem hlt) with h3p | h2p
      · left
        have h2f : (ψ[i₀].length == 2) = false := by simp [h3p]
        simp only [expandClauseFiveOcc, h2f, Bool.false_eq_true, ↓reduceIte,
          CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil, Clause.relabel,
          List.map_map, Function.comp_def, Prod.map_fst, List.count_eq_zero, List.mem_map,
          not_exists, not_and]
        intro l _ heq; omega
      · right
        match ψ[i₀], h2p with
        | [l₁, l₂], _ =>
          dsimp only [expandClauseFiveOcc]
          simp only [List.length_cons, List.length_nil, beq_self_eq_true,
            ↓reduceIte, List.headD_cons, List.tail_cons]
          rw [count_vars_binaryGadget13_rem l₁ l₂ i₀ w hrem]
          have hw_eq : w / 8 = i₀ := rfl
          simp only [hw_eq, ↓reduceIte]
    · left; rfl

private theorem satisfiable_expandFiveOcc {ψ : CNF ℕ} (hψ : ψ.Satisfiable) :
    (expandFiveOcc ψ).Satisfiable := by
  obtain ⟨σ, hσ⟩ := hψ
  let τ : ℕ → Bool := fun n ↦ if n % 8 == 0 then σ (n / 8) else true
  have hτ_mul (v : ℕ) : τ (8 * v) = σ v := by
    have hm : ((8 * v) % 8 == 0) = true := by rw [beq_iff_eq]; omega
    have hd : (8 * v) / 8 = v := by omega
    dsimp only [τ]; rw [hm]; simp [hd]
  have hτ_rem (i r : ℕ) (hr1 : 1 ≤ r) (hr7 : r ≤ 7) : Literal.eval τ (8 * i + r, true) = true := by
    have hm : ((8 * i + r) % 8 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    simp only [Literal.eval]; dsimp only [τ]; rw [hm]; simp
  refine ⟨τ, (CNF.eval_flatMap_eq_true_iff _ _ _).2 fun ⟨c, i⟩ hci ↦ ?_⟩
  have hc : c.eval σ = true :=
    (CNF.eval_eq_true_iff σ ψ).1 hσ c (List.fst_mem_of_mem_zipIdx hci)
  by_cases h2 : c.length == 2
  · have hlen2 : c.length = 2 := beq_iff_eq.1 h2
    match c, hlen2 with
    | [l₁, l₂], _ =>
      simp only [expandClauseFiveOcc, List.length_cons, List.length_nil, beq_self_eq_true,
        ↓reduceIte, List.headD_cons, List.tail_cons, binaryGadget13]
      simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false] at hc
      have hl1 : Literal.eval τ (8 * l₁.1, l₁.2) = Literal.eval σ l₁ := by
        simp [Literal.eval, hτ_mul]
      have hl2 : Literal.eval τ (8 * l₂.1, l₂.2) = Literal.eval σ l₂ := by
        simp [Literal.eval, hτ_mul]
      simp only [CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil, hl1, hl2,
        hτ_rem i 1 (by omega) (by omega), hτ_rem i 2 (by omega) (by omega),
        hτ_rem i 3 (by omega) (by omega), hτ_rem i 4 (by omega) (by omega),
        hτ_rem i 5 (by omega) (by omega), hτ_rem i 6 (by omega) (by omega),
        hτ_rem i 7 (by omega) (by omega)]
      rcases Bool.or_eq_true_iff.1 hc with h | h <;> simp [h]
  · simp only [expandClauseFiveOcc, h2, Bool.false_eq_true, ↓reduceIte, CNF.eval_cons,
      CNF.eval_nil, Bool.and_true, Clause.eval_relabel]
    have hcomp : τ ∘ (8 * ·) = σ := funext hτ_mul
    rwa [hcomp]

private theorem countUnsat_le_expandFiveOcc (ψ : CNF ℕ) (τ : ℕ → Bool) :
    ψ.countUnsat (fun v ↦ τ (8 * v)) ≤ (expandFiveOcc ψ).countUnsat τ := by
  have hzip : ψ.countUnsat (fun v ↦ τ (8 * v)) =
      ψ.zipIdx.countP fun p ↦ !p.1.eval (fun v ↦ τ (8 * v)) := by
    conv_lhs => rw [CNF.countUnsat, ← List.zipIdx_map_fst 0 ψ, List.countP_map]
    rfl
  rw [hzip, expandFiveOcc, CNF.countUnsat, List.countP_flatMap]
  refine countP_le_sum_map _ _ _ fun ⟨c, i⟩ _ hc ↦ ?_
  dsimp only [Function.comp_def, expandClauseFiveOcc] at hc ⊢
  by_cases h2 : c.length == 2
  · have hlen2 : c.length = 2 := beq_iff_eq.1 h2
    match c, hlen2 with
    | [l₁, l₂], _ =>
      simp only [List.length_cons, List.length_nil, beq_self_eq_true,
        ↓reduceIte, List.headD_cons, List.tail_cons]
      simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.not_eq_true',
        Bool.or_eq_false_iff] at hc
      have ha : Literal.eval τ (8 * l₁.1, l₁.2) = false := by simpa [Literal.eval] using hc.1
      have hb : Literal.eval τ (8 * l₂.1, l₂.2) = false := by simpa [Literal.eval] using hc.2
      cases hz : τ (8 * i + 1)
      · refine List.countP_pos_iff.2 ⟨[(8 * l₁.1, l₁.2), (8 * l₂.1, l₂.2), (8 * i + 1, true)],
          by simp [binaryGadget13], ?_⟩
        simp only [Clause.eval_cons, Clause.eval_nil, ha, hb, Bool.false_or, Bool.or_false]
        simp [Literal.eval, hz]
      · refine List.countP_pos_iff.2 ⟨[(8 * l₁.1, l₁.2), (8 * l₂.1, l₂.2), (8 * i + 1, false)],
          by simp [binaryGadget13], ?_⟩
        simp only [Clause.eval_cons, Clause.eval_nil, ha, hb, Bool.false_or, Bool.or_false]
        simp [Literal.eval, hz]
  · have hc' : Clause.eval (τ ∘ (8 * ·)) c = false := by simpa [Function.comp_def] using hc
    simp [h2, Clause.eval_relabel, hc']

private theorem length_expandFiveOcc_le (ψ : CNF ℕ) :
    (expandFiveOcc ψ).length ≤ 13 * ψ.length := by
  rw [expandFiveOcc, List.length_flatMap]
  refine (List.sum_le_length_nsmul (ψ.zipIdx.map fun p ↦ (expandClauseFiveOcc p).length) 13
    ?_).trans_eq (by simp [smul_eq_mul, Nat.mul_comm])
  intro n hn
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hn
  dsimp only [expandClauseFiveOcc]
  split_ifs <;> simp [binaryGadget13]

private theorem length_expandFiveOcc_pos {ψ : CNF ℕ} (hpos : 0 < ψ.length) :
    0 < (expandFiveOcc ψ).length := by
  cases ψ with
  | nil => simp at hpos
  | cons c rest =>
    simp only [expandFiveOcc, List.zipIdx_cons, List.flatMap_cons, List.length_append]
    have hc : 0 < (expandClauseFiveOcc (c, 0)).length := by
      unfold expandClauseFiveOcc
      split_ifs <;> simp [binaryGadget13]
    omega

/-! ### Complete polynomial-time reduction and explicit soundness gap -/

private def finishToFiveOcc (φ : CNF ℕ) : CNF ℕ :=
  if φ.isEmpty then baseFiveOccCNF else expandFiveOcc (toThreeSATThree (φ ++ φ))

private theorem isPolyTime_finishToFiveOcc :
    ComputableInPolyTime finishToFiveOcc encCNF encCNF := by
  unfold finishToFiveOcc
  have hempty := ComputableInPolyTime.listIsEmpty' (encClause encNat)
  have hdbl := (ComputableInPolyTime.listAppend (encClause encNat)).comp
    (ComputableInPolyTime.id'.prod ComputableInPolyTime.id')
  have hmain := isPolyTime_expandFiveOcc.comp (computableInPolyTime_toThreeSATThree.comp hdbl)
  exact hempty.ite
    (ComputableInPolyTime.const (encIn := encCNF) (encOut := encCNF) baseFiveOccCNF) hmain

private theorem isExactThreeSATFiveOcc_reduce {φ : CNF ℕ} (hne : φ ≠ [])
    (h3 : ∀ c ∈ φ, c.length = 3) :
    IsExactThreeSATFiveOcc (expandFiveOcc (toThreeSATThree (φ ++ φ))) ∧
      0 < (expandFiveOcc (toThreeSATThree (φ ++ φ))).length := by
  set φ_dbl := φ ++ φ
  have h3_dbl : ∀ c ∈ φ_dbl, c.length = 3 := fun c hc ↦ by
    rcases List.mem_append.1 hc with hc | hc <;> exact h3 c hc
  have hw_dbl : ∀ c ∈ φ_dbl, c.length ≤ 3 := fun c hc ↦ (h3_dbl c hc).le
  have hψ_eq : toThreeSATThree φ_dbl =
      φ_dbl.toThreeOccurrence.relabel ThreeSATThree.numberCopy := by
    simp +contextual [toThreeSATThree, hw_dbl]
  have hclauses : ∀ c ∈ toThreeSATThree φ_dbl,
      c.IsExactThreeDistinct ∨ (c.length = 2 ∧ (c.map Prod.fst).Nodup) := by
    rw [hψ_eq]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rcases List.mem_append.1 hd with hd_ter | hd_bin
    · left
      exact (isExactThreeDistinct_occurrenceClauses h3_dbl d hd_ter).relabel_of_injOn
        fun x _ y _ hxy ↦ ThreeSATThree.numberCopy_injective hxy
    · right
      obtain ⟨v, hv, hd_cyc⟩ := List.mem_flatMap.1 hd_bin
      have hv_mem : v ∈ φ.vars := by
        have h1 := CNF.mem_distinctVars.1 hv
        rwa [cnf_vars_append, List.mem_append, or_self] at h1
      have hv_cnt : 2 ≤ (φ_dbl.occurrenceCopies v).length := by
        rw [CNF.length_occurrenceCopies, cnf_vars_append, List.count_append]
        have := List.count_pos_iff.2 hv_mem
        omega
      have hv_nd : (φ_dbl.occurrenceCopies v).Nodup :=
        (CNF.nodup_vars_occurrenceClauses φ_dbl).filter _
      refine ⟨by rw [Clause.length_relabel, CNF.length_of_mem_implicationCycle _ hd_cyc], ?_⟩
      simpa [Clause.relabel, List.map_map, Function.comp_def] using
        (nodup_vars_of_mem_implicationCycle hv_nd hv_cnt d hd_cyc).map
          ThreeSATThree.numberCopy_injective
  refine ⟨⟨isExactThreeDistinct_expandFiveOcc hclauses, fun w hw ↦ ?_⟩, ?_⟩
  · rcases count_vars_expandFiveOcc_eq_zero_or_five h3_dbl w with h0 | h5
    · exact absurd hw (List.count_eq_zero.1 h0)
    · exact h5
  · apply length_expandFiveOcc_pos
    rw [length_toThreeSATThree φ_dbl hw_dbl]
    have hpos : 0 < φ.length := List.length_pos_iff.2 hne
    simp only [φ_dbl, List.length_append]
    omega

private noncomputable def degRedRetention (cardD : ℕ) (μ : ℝ) : ℝ :=
  min 1 ((1 - μ) * cardD) / (2 * (1 + cardD))

private noncomputable def twoCSPToFiveOccGap (cardα cardD k : ℕ) (μ ε : ℝ) : ℝ :=
  ε * degRedRetention cardD μ /
    (cardα ^ 2 * max 1 (2 * k - 2) : ℕ) /
    (8 * maxOccStage2 cardα cardD : ℕ) / 13

private theorem twoCSPToFiveOccGap_pos {cardα cardD k : ℕ} {μ ε : ℝ}
    (hα : 0 < cardα) (hD : 0 < cardD) (hμ : μ < 1) (hε : 0 < ε) :
    0 < twoCSPToFiveOccGap cardα cardD k μ ε := by
  have h1m : 0 < 1 - μ := sub_pos.2 hμ
  have hDr : 0 < (cardD : ℝ) := Nat.cast_pos.2 hD
  have hdeg : 0 < degRedRetention cardD μ := by unfold degRedRetention; positivity
  have hmax : 0 < maxOccStage2 cardα cardD :=
    lt_of_lt_of_le (by decide : 0 < 2) (two_le_maxOccStage2 hα)
  have hcnf_den : 0 < cardα ^ 2 * max 1 (2 * k - 2) :=
    Nat.mul_pos (Nat.pow_pos hα) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  unfold twoCSPToFiveOccGap; positivity

private theorem twoCSPToFiveOccGap_lt_one {cardα cardD k : ℕ} {μ ε : ℝ}
    (hα : 0 < cardα) (hD : 0 < cardD) (hμ : μ < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    twoCSPToFiveOccGap cardα cardD k μ ε < 1 := by
  have h1m : 0 < 1 - μ := sub_pos.2 hμ
  have hDr : 0 < (cardD : ℝ) := Nat.cast_pos.2 hD
  have hdeg_pos : 0 < degRedRetention cardD μ := by unfold degRedRetention; positivity
  have hdeg_le : degRedRetention cardD μ ≤ 1 := by
    unfold degRedRetention
    exact (div_le_one (by positivity)).2
      ((min_le_left _ _).trans (by linarith [Nat.cast_nonneg (α := ℝ) cardD]))
  have hd1 : (1 : ℝ) ≤ (cardα ^ 2 * max 1 (2 * k - 2) : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos hα) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hd2 : (1 : ℝ) ≤ (8 * maxOccStage2 cardα cardD : ℕ) := by
    exact_mod_cast le_trans (by decide : 1 ≤ 16) (Nat.mul_le_mul_left 8 (two_le_maxOccStage2 hα))
  unfold twoCSPToFiveOccGap
  have hs1 : ε * degRedRetention cardD μ ≤ ε := mul_le_of_le_one_right hε0.le hdeg_le
  have hs2 := (div_le_self (by positivity) hd1).trans hs1
  have hs3 := (div_le_self (by positivity) hd2).trans hs2
  exact ((div_le_self (by positivity) (by norm_num)).trans hs3).trans_lt hε1

private theorem unsatVal_stage2_ge {α D : Type} [Fintype α] [DecidableEq α]
    [Fintype D] {k : ℕ} (e : α ≃ (Fin k → Bool))
    (pairs : List (α × α)) (hpairs : ∀ p, p ∈ pairs)
    (hlen_pairs : pairs.length = Fintype.card α ^ 2)
    (fallback : α → α → Bool) (family : (n : ℕ) → Cslib.RotationMap (Fin n) D)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (labels : List D) (hlabels : labels.Nodup) (hmem : ∀ d, d ∈ labels)
    {μ : ℝ} (hgap : ∀ n, (family n).spectralExpansion ≤ μ)
    (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal * degRedRetention (Fintype.card D) μ /
      (Fintype.card α ^ 2 * max 1 (2 * k - 2) : ℕ) ≤
        (toBoundedWidthThreeCNF e pairs fallback rotate labels g).unsatVal := by
  classical
  have : Nonempty α := ⟨e.symm fun _ ↦ false⟩
  have hdeg := Graph.le_unsatVal_degreeReduce g id fallback family rotate hrotate
    labels hlabels hmem μ hgap
  have hmap : ((degreeReduceTwoCSP fallback rotate labels g).toGraph id).unsatVal =
      ((g.degreeReduce fallback rotate labels).toGraph (Graph.degreeReduceEval id)).unsatVal :=
    Graph.unsatVal_mapConstraints _ _ _
  rw [← hmap] at hdeg
  have hdeg' : (g.toGraph id).unsatVal * degRedRetention (Fintype.card D) μ ≤
      ((degreeReduceTwoCSP fallback rotate labels g).toGraph id).unsatVal := by
    unfold degRedRetention; rwa [mul_comm] at hdeg
  have hcnf := Graph.div_le_unsatVal_toThreeSAT_toCNF e pairs hpairs
    (degreeReduceTwoCSP fallback rotate labels g)
  rw [hlen_pairs] at hcnf
  exact (div_le_div_of_nonneg_right hdeg' (by positivity)).trans hcnf

private theorem unsatVal_stage34_ge {Δ₀ : ℕ} (hΔ₀ : 2 ≤ Δ₀) {φ : CNF ℕ} (hne : φ ≠ [])
    (h3 : ∀ c ∈ φ, c.length = 3) (hocc : ∀ v, φ.vars.count v ≤ Δ₀) :
    φ.unsatVal / (8 * Δ₀ : ℕ) / 13 ≤
      (expandFiveOcc (toThreeSATThree (φ ++ φ))).unsatVal := by
  set φ_dbl := φ ++ φ
  set Δ := 2 * Δ₀
  have hΔ : 1 ≤ Δ := by omega
  have hocc_dbl (v : ℕ) : φ_dbl.vars.count v ≤ Δ := by
    rw [cnf_vars_append, List.count_append]; have := hocc v; omega
  have h3_dbl : ∀ c ∈ φ_dbl, c.length = 3 := fun c hc ↦ by
    rcases List.mem_append.1 hc with hc | hc <;> exact h3 c hc
  have hw_dbl : ∀ c ∈ φ_dbl, c.length ≤ 3 := fun c hc ↦ (h3_dbl c hc).le
  have hvars_len : φ_dbl.vars.length = 3 * φ_dbl.length := by
    rw [CNF.length_vars, List.map_congr_left fun c hc ↦ h3_dbl c hc, List.map_const',
      List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  set ψ := toThreeSATThree φ_dbl
  have hψ_len : ψ.length = 4 * φ_dbl.length := by
    rw [length_toThreeSATThree φ_dbl hw_dbl, hvars_len]; omega
  have hφ_pos : 0 < φ.length := List.length_pos_iff.2 hne
  have hφ_dbl_len : φ_dbl.length = 2 * φ.length := by simp [φ_dbl, Nat.two_mul]
  have hψ_pos : 0 < ψ.length := by omega
  have hexp_pos : 0 < (expandFiveOcc ψ).length := length_expandFiveOcc_pos hψ_pos
  rw [CNF.le_unsatVal_iff]
  intro τ
  have hψ_eq : ψ = φ_dbl.toThreeOccurrence.relabel ThreeSATThree.numberCopy := by
    simp +contextual [ψ, toThreeSATThree, hw_dbl]
  obtain ⟨σ, hσ⟩ := countUnsat_le_mul_countUnsat_toThreeOccurrence hΔ hocc_dbl
    ((fun v ↦ τ (8 * v)) ∘ ThreeSATThree.numberCopy)
  have hσ_dbl : φ_dbl.countUnsat σ = 2 * φ.countUnsat σ := by
    simp [φ_dbl, CNF.countUnsat, List.countP_append, Nat.two_mul]
  have hψ_cnt : φ_dbl.toThreeOccurrence.countUnsat
      ((fun v ↦ τ (8 * v)) ∘ ThreeSATThree.numberCopy) =
      ψ.countUnsat (fun v ↦ τ (8 * v)) := by rw [hψ_eq, CNF.countUnsat_relabel]
  have hexp_cnt := countUnsat_le_expandFiveOcc ψ τ
  have hchain : 2 * φ.countUnsat σ ≤ Δ * (expandFiveOcc ψ).countUnsat τ := by
    calc 2 * φ.countUnsat σ = φ_dbl.countUnsat σ := hσ_dbl.symm
      _ ≤ Δ * ψ.countUnsat (fun v ↦ τ (8 * v)) := by rwa [hψ_cnt] at hσ
      _ ≤ Δ * (expandFiveOcc ψ).countUnsat τ := Nat.mul_le_mul_left Δ hexp_cnt
  have hval_φ : φ.unsatVal ≤ (φ.countUnsat σ : ℝ) / φ.length := φ.unsatVal_le σ
  have hexp_len_le : ((expandFiveOcc ψ).length : ℝ) ≤ 13 * (8 * (φ.length : ℝ)) := by
    have h1 := length_expandFiveOcc_le ψ
    rw [hψ_len, hφ_dbl_len] at h1
    exact_mod_cast (by omega : (expandFiveOcc ψ).length ≤ 13 * (8 * φ.length))
  have hchain_real : 2 * (φ.countUnsat σ : ℝ) ≤ (Δ : ℝ) * (expandFiveOcc ψ).countUnsat τ := by
    exact_mod_cast hchain
  calc φ.unsatVal / (8 * Δ₀ : ℕ) / 13
      ≤ ((φ.countUnsat σ : ℝ) / φ.length) / (8 * Δ₀ : ℕ) / 13 := by gcongr
    _ = (2 * (φ.countUnsat σ : ℝ)) / ((Δ : ℝ) * (13 * (8 * (φ.length : ℝ)))) := by
        dsimp only [Δ]; push_cast; ring
    _ ≤ ((Δ : ℝ) * (expandFiveOcc ψ).countUnsat τ) /
          ((Δ : ℝ) * (13 * (8 * (φ.length : ℝ)))) := by gcongr
    _ = ((expandFiveOcc ψ).countUnsat τ : ℝ) / (13 * (8 * (φ.length : ℝ))) :=
        mul_div_mul_left _ _ (by exact_mod_cast (by omega : Δ ≠ 0))
    _ ≤ ((expandFiveOcc ψ).countUnsat τ : ℝ) / (expandFiveOcc ψ).length :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hexp_pos) hexp_len_le

private theorem polyTimeReducible_GapTwoCSP_GapExactThreeSATFiveOcc
    {α D : Type} [Fintype α] [Fintype D] [Nonempty D]
    {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool}
    {k : ℕ} (hk : 2 ≤ k) (e : α ≃ (Fin k → Bool))
    (family : (n : ℕ) → Cslib.RotationMap (Fin n) D)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (hrot : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    {μ : ℝ} (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1)
    {s : ℝ} (hs : s < 1) :
    PromiseProblem.PolyTimeReducible (Graph.encoding encConstraintTable) encCNF
      (GapTwoCSP α s)
      (GapExactThreeSATFiveOcc
        (1 - twoCSPToFiveOccGap (Fintype.card α) (Fintype.card D) k μ (1 - s))) := by
  classical
  have : Nonempty α := ⟨e.symm fun _ ↦ false⟩
  let fallback : α → α → Bool := fun _ _ ↦ true
  let labels : List D := (Finset.univ : Finset D).toList
  have hlabels_nd : labels.Nodup := Finset.nodup_toList _
  have hlabels_mem : ∀ d, d ∈ labels := fun d ↦ Finset.mem_toList.2 (Finset.mem_univ d)
  have hlabels_len : labels.length = Fintype.card D := by simp [labels]
  let pairs : List (α × α) := (Finset.univ : Finset (α × α)).toList
  have hpairs_mem : ∀ p, p ∈ pairs := fun p ↦ Finset.mem_toList.2 (Finset.mem_univ p)
  have hpairs_len : pairs.length = Fintype.card α ^ 2 := by simp [pairs, Fintype.card_prod, sq]
  let toPhi := toBoundedWidthThreeCNF e pairs fallback rotate labels
  have hpoly : ComputableInPolyTime (finishToFiveOcc ∘ toPhi)
      (Graph.encoding encConstraintTable) encCNF :=
    isPolyTime_finishToFiveOcc.comp
      (isPolyTime_toBoundedWidthThreeCNF (alphabet := alphabet) e pairs fallback rotate labels hrot)
  refine ⟨finishToFiveOcc ∘ toPhi, hpoly, fun g hg ↦ ?_, fun g hg ↦ ?_⟩
  · have hg_sat : ((degreeReduceTwoCSP fallback rotate labels g).toGraph id).Satisfiable := by
      have hmap_sat : ((degreeReduceTwoCSP fallback rotate labels g).toGraph id).Satisfiable ↔
          ((g.degreeReduce fallback rotate labels).toGraph
            (Graph.degreeReduceEval id)).Satisfiable :=
        Graph.satisfiable_mapConstraints_iff _ _ _
      rw [hmap_sat, Graph.satisfiable_degreeReduce_iff g id fallback family rotate hrotate
        labels hlabels_nd hlabels_mem]
      exact (g.toGraph id).satisfiable_degreeReduce _ (mem_yes_GapTwoCSP.1 hg)
    have hφ_sat : (toPhi g).Satisfiable :=
      ((mem_ThreeSAT_toThreeSAT_iff _).2 (Graph.satisfiable_toCNF e pairs hg_sat)).2
    rw [mem_yes_GapExactThreeSATFiveOcc]
    simp only [Function.comp_apply, finishToFiveOcc]
    by_cases hempty : (toPhi g).isEmpty = true
    · simp only [hempty, ↓reduceIte]
      exact ⟨satisfiable_baseFiveOccCNF, isExactThreeSATFiveOcc_baseFiveOccCNF,
        length_baseFiveOccCNF_pos⟩
    · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
      have hne : toPhi g ≠ [] := fun hnil ↦ by simp [hnil] at hempty
      have h3 := length_eq_three_of_mem_toBoundedWidthThreeCNF hk e pairs fallback rotate labels g
      have hdbl_sat : (toPhi g ++ toPhi g).Satisfiable := by
        obtain ⟨σ, hσ⟩ := hφ_sat; exact ⟨σ, by simp [CNF.eval_append, hσ]⟩
      have hψ_sat : (toThreeSATThree (toPhi g ++ toPhi g)).Satisfiable :=
        ((mem_ThreeSATThree_toThreeSATThree_iff _).2
          ⟨fun c hc ↦ by rcases List.mem_append.1 hc with hc | hc <;> exact (h3 c hc).le,
            hdbl_sat⟩).2.2
      have h5 := isExactThreeSATFiveOcc_reduce hne h3
      exact ⟨satisfiable_expandFiveOcc hψ_sat, h5.1, h5.2⟩
  · have hg_no : 1 - s ≤ (g.toGraph id).unsatVal := (mem_no_GapTwoCSP hs).1 hg
    have h1s : 0 < 1 - s := sub_pos.2 hs
    have hdeg_pos : 0 < degRedRetention (Fintype.card D) μ := by
      have h1m : 0 < 1 - μ := sub_pos.2 hμ
      have hDr : 0 < (Fintype.card D : ℝ) := Nat.cast_pos.2 Fintype.card_pos
      unfold degRedRetention; positivity
    have hden_pos : 0 < Fintype.card α ^ 2 * max 1 (2 * k - 2) :=
      Nat.mul_pos (Nat.pow_pos Fintype.card_pos) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    have hφ_val : (1 - s) * degRedRetention (Fintype.card D) μ /
        (Fintype.card α ^ 2 * max 1 (2 * k - 2) : ℕ) ≤ (toPhi g).unsatVal :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg_no hdeg_pos.le)
        (by positivity)).trans
        (unsatVal_stage2_ge e pairs hpairs_mem hpairs_len fallback family rotate hrotate
          labels hlabels_nd hlabels_mem hgap g)
    have hne : toPhi g ≠ [] := List.ne_nil_of_length_pos
      (CNF.length_pos_of_unsatVal_pos (lt_of_lt_of_le (by positivity) hφ_val))
    have hempty : (toPhi g).isEmpty = false := List.isEmpty_eq_false_iff.2 hne
    have hgap_pos := twoCSPToFiveOccGap_pos (k := k)
      (Fintype.card_pos (α := α)) (Fintype.card_pos (α := D)) hμ h1s
    rw [mem_no_GapExactThreeSATFiveOcc (by linarith), sub_sub_cancel]
    simp only [Function.comp_apply, finishToFiveOcc, hempty, Bool.false_eq_true, ↓reduceIte]
    have h3 := length_eq_three_of_mem_toBoundedWidthThreeCNF hk e pairs fallback rotate labels g
    have h5 := isExactThreeSATFiveOcc_reduce hne h3
    refine ⟨?_, h5.1, h5.2⟩
    unfold twoCSPToFiveOccGap
    exact (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hφ_val (by positivity)) (by positivity)).trans
      (unsatVal_stage34_ge (two_le_maxOccStage2 Fintype.card_pos) hne h3
        (count_vars_toBoundedWidthThreeCNF_le e pairs hpairs_len fallback family rotate hrotate
          labels hlabels_nd hlabels_mem hlabels_len g))

private abbrev ExpLabel : Type :=
  Cslib.RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257

private theorem nonempty_expLabel : Nonempty ExpLabel :=
  ⟨Sum.inl (⟨0, by positivity⟩, ((0, 0), (0, 0)))⟩

/-- Explicit positive soundness-gap constant `ε₀ ∈ (0, 1)` for `MAX-E3SAT-5` obtained by composing
Dinur's `MAX-2CSP` gap (`2 ^ (-61)`) with expander degree reduction, `3`-CNF clause splitting,
occurrence splitting, and the `13`-clause exact-`3`-distinct octahedron gadget. -/
@[irreducible] noncomputable def feigeFiveOccGap : ℝ :=
  twoCSPToFiveOccGap (Fintype.card (Bool × (Fin 6 → Bool))) (Fintype.card ExpLabel) 7
    (1 - 9 / (400 * (257 : ℝ) ^ 16)) (1 - (1 - 1 / 2 ^ 61))

/-- The soundness-gap constant `feigeFiveOccGap` is strictly positive. -/
theorem feigeFiveOccGap_pos : 0 < feigeFiveOccGap := by
  unfold feigeFiveOccGap
  have := nonempty_expLabel
  exact twoCSPToFiveOccGap_pos Fintype.card_pos Fintype.card_pos (by norm_num) (by norm_num)

/-- The soundness-gap constant `feigeFiveOccGap` is strictly less than `1`. -/
theorem feigeFiveOccGap_lt_one : feigeFiveOccGap < 1 := by
  unfold feigeFiveOccGap
  have := nonempty_expLabel
  exact twoCSPToFiveOccGap_lt_one Fintype.card_pos Fintype.card_pos
    (by norm_num) (by norm_num) (by norm_num)

/-- **Feige's 5-Occurrence Exact-3-SAT Gap NP-Hardness Theorem**
: distinguishing satisfiable nonempty `E3SAT-5` formulas
from nonempty `E3SAT-5` formulas in which every assignment satisfies at most a
`1 - feigeFiveOccGap` fraction of the clauses is `NP`-hard under deterministic polynomial-time
many-one reductions.
-/
theorem gapExactThreeSATFiveOcc_npHard :
    PromiseProblem.NPHard encCNF (GapExactThreeSATFiveOcc (1 - feigeFiveOccGap)) := by
  unfold feigeFiveOccGap
  have := nonempty_expLabel
  have hrot := Cslib.RotationMap.polytime_arithmeticExpanderRotate (encFinite ExpLabel)
  have hred := polyTimeReducible_GapTwoCSP_GapExactThreeSATFiveOcc
    (alphabet := encPair encBool (encPi encBool)) (labelEncoding := encFinite ExpLabel)
    (s := 1 - 1 / 2 ^ 61) (by decide : 2 ≤ 7) (Fin.consEquiv fun _ : Fin 7 ↦ Bool)
    Cslib.RotationMap.arithmeticExpander Cslib.RotationMap.arithmeticExpanderRotate
    Cslib.RotationMap.arithmeticExpanderRotate_eq hrot
    (fun n ↦ by convert Cslib.RotationMap.spectralExpansion_arithmeticExpander_le n using 2)
    (by norm_num) (by norm_num)
  exact fun _ enc A hA ↦ (GapTwoCSP_npHard enc A hA).trans hred

/-- Existential form of Feige's 5-occurrence `3`-SAT gap `NP`-hardness theorem
: there exists a universal constant `ε₀ ∈ (0, 1)` such that
`GapExactThreeSATFiveOcc (1 - ε₀)` is `NP`-hard.
-/
theorem exists_gapExactThreeSATFiveOcc_npHard :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      PromiseProblem.NPHard encCNF (GapExactThreeSATFiveOcc (1 - ε₀)) :=
  ⟨feigeFiveOccGap, feigeFiveOccGap_pos, feigeFiveOccGap_lt_one, gapExactThreeSATFiveOcc_npHard⟩

/-- Unless `P = NP`, no polynomial-time algorithm solves the gap problem
`GapExactThreeSATFiveOcc (1 - feigeFiveOccGap)`. -/
theorem gapExactThreeSATFiveOcc_notMem_PromiseP {β : Type} {enc : β ↪ List Bool}
    (h : P enc ≠ NP enc) :
    GapExactThreeSATFiveOcc (1 - feigeFiveOccGap) ∉ PromiseP encCNF :=
  gapExactThreeSATFiveOcc_npHard.notMem_PromiseP h

-- Internal non-vacuity sanity check: `GapExactThreeSATFiveOcc` has concrete yes-instances.
example : baseFiveOccCNF ∈ (GapExactThreeSATFiveOcc (1 - feigeFiveOccGap)).yes :=
  mem_yes_GapExactThreeSATFiveOcc.2
    ⟨satisfiable_baseFiveOccCNF, isExactThreeSATFiveOcc_baseFiveOccCNF, length_baseFiveOccCNF_pos⟩

end Cslib.Complexity
