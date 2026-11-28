/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Randomized
public import CslibFrontier.Computability.Complexity.Classes.QMA.MA
public import CslibFrontier.Computability.PCP.Approximation.Hastad.Hardness

import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded-Degree CSP Promise Problems and Two-Sided Randomized Promise Reductions

This module introduces variable-degree, exact-arity, and simple-hypergraph predicates on CSPs and
CNF formulas, the corresponding bounded-degree gap promise problems, and two-sided bounded-error
randomized polynomial-time promise reductions (`PromiseBPReducibleWithError`,
`PromiseBPReducible`) together with their complexity-class closure and collapse theorems
(`PromiseBPP`, `NP ⊆ BPP`, `NP ⊆ BQP`) and degree-preserving four-clause compilation from
`Max-E3-LIN-2` to `Max-E3-SAT`, under standard Lean axioms.

## Main definitions

* `CslibFrontier.Complexity.cspVarDegree`,
  `CslibFrontier.Complexity.CSPHasDegreeAtMost`,
  `CslibFrontier.Complexity.CSPIsExactK`,
  `CslibFrontier.Complexity.CSPIsSimpleHypergraph`: variable degree, bounded degree,
  exact-$k$ distinct-variable scopes, and simple-hypergraph structure on `CSP Rel V`.
* `CslibFrontier.Complexity.cnfVarDegree`,
  `CslibFrontier.Complexity.CNFHasDegreeAtMost`: variable degree and bounded degree on
  `CNF V`.
* `CslibFrontier.Complexity.GapBoundedDegreeCSP`,
  `CslibFrontier.Complexity.GapSimpleBoundedDegreeCSP`,
  `CslibFrontier.Complexity.GapBoundedDegreeExactKLinAbelian`,
  `CslibFrontier.Complexity.GapBoundedDegreeExactKLinBool`,
  `CslibFrontier.Complexity.GapSimpleBoundedDegreeExactKLinBool`,
  `CslibFrontier.Complexity.GapBoundedDegreeExactThreeSAT`: bounded-degree gap promise
  problems.
* `CslibFrontier.Complexity.PromiseBPReducibleWithError`,
  `CslibFrontier.Complexity.PromiseBPReducible`: two-sided bounded-error randomized
  polynomial-time promise reductions.

## Main results

* `CslibFrontier.Complexity.PromiseBPReducible.mem_PromiseBPP`: `PromiseBPP` is closed
  under `PromiseBPReducible`.
* `CslibFrontier.Complexity.NP_subset_BPP_of_nphard_promiseBPReducible`,
  `CslibFrontier.Complexity.NP_subset_BQP_of_nphard_promiseBPReducible`: conditional
  complexity collapses `NP ⊆ BPP` and `NP ⊆ BQP` from randomized reductions of NP-hard promise
  problems.
* `CslibFrontier.Complexity.NP_subset_coRP_of_nphard_rpReducible`: one-sided conditional
  collapse `NP ⊆ coRP` from `RPReducible`.
* `CslibFrontier.Complexity.polyTimeReducible_gapBoundedDegreeExact3Lin_3SAT`:
  deterministic polynomial-time reduction from degree-`D'` `Max-E3-LIN-2` to degree-`(4 * D')`
  `Max-E3-SAT` via the four-clause parity gadget.

## Tags

CSP, bounded degree, promise problems, randomized reductions, BPP, BQP, coRP, Max-E3-SAT
-/

public section

namespace CslibFrontier.Complexity

open Finset Cslib Cslib.Logic.PL Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Variable degree, hypergraph simplicity, and bounded-degree gap promise problems -/

/-- Number of constraints in `F : CSP Rel V` whose scope contains variable `v`. -/
@[expose] def cspVarDegree {Rel V : Type*} [DecidableEq V] (F : CSP Rel V) (v : V) : ℕ :=
  F.countP fun c ↦ decide (v ∈ c.scope)

/-- Every variable appears in at most `D` constraints of `F`. -/
@[expose] def CSPHasDegreeAtMost {Rel V : Type*} [DecidableEq V] (D : ℕ) (F : CSP Rel V) : Prop :=
  ∀ v : V, cspVarDegree F v ≤ D

/-- Every constraint in `F` has exact arity `k` on `k` distinct variables. -/
@[expose] def CSPIsExactK {Rel V : Type*} (k : ℕ) (F : CSP Rel V) : Prop :=
  ∀ c ∈ F, c.scope.length = k ∧ c.scope.Nodup

/-- `F` has no duplicate constraint variable sets (a simple hypergraph when combined with
`CSPIsExactK k F`). -/
@[expose] def CSPIsSimpleHypergraph {Rel V : Type*} [DecidableEq V] (F : CSP Rel V) : Prop :=
  (F.map fun c ↦ c.scope.toFinset).Nodup

/-- Number of clauses in `φ : CNF V` in which variable `v` occurs. -/
@[expose] def cnfVarDegree {V : Type*} [DecidableEq V] (φ : CNF V) (v : V) : ℕ :=
  φ.countP fun cl ↦ cl.any fun lit ↦ decide (lit.1 = v)

/-- Every variable appears in at most `D` clauses of `φ : CNF V`. -/
@[expose] def CNFHasDegreeAtMost {V : Type*} [DecidableEq V] (D : ℕ) (φ : CNF V) : Prop :=
  ∀ v : V, cnfVarDegree φ v ≤ D

theorem CSPHasDegreeAtMost.mono {Rel V : Type*} [DecidableEq V] {D₁ D₂ : ℕ} (h : D₁ ≤ D₂)
    {F : CSP Rel V} (hF : CSPHasDegreeAtMost D₁ F) : CSPHasDegreeAtMost D₂ F :=
  fun v ↦ (hF v).trans h

theorem CNFHasDegreeAtMost.mono {V : Type*} [DecidableEq V] {D₁ D₂ : ℕ} (h : D₁ ≤ D₂)
    {φ : CNF V} (hφ : CNFHasDegreeAtMost D₁ φ) : CNFHasDegreeAtMost D₂ φ :=
  fun v ↦ (hφ v).trans h

/-- Gap promise problem for exact-$k$ Max-CSPs of variable degree at most `D`. -/
@[expose] noncomputable def GapBoundedDegreeCSP {Rel Dom : Type} (sem : Rel → List Dom → Bool)
    (k D : ℕ) (c s : ℝ) : PromiseProblem (CSP Rel ℕ) :=
  (PromiseProblem.gapMax (fun F ↦ 1 - F.unsatVal sem) (fun _ ↦ c) (fun _ ↦ s)).restrict
    {F | CSPIsExactK k F ∧ CSPHasDegreeAtMost D F}

/-- Gap promise problem for exact-$k$ Max-CSPs of variable degree at most `D` on simple
$k$-uniform hypergraphs. -/
@[expose] noncomputable def GapSimpleBoundedDegreeCSP {Rel Dom : Type} (sem : Rel → List Dom → Bool)
    (k D : ℕ) (c s : ℝ) : PromiseProblem (CSP Rel ℕ) :=
  (PromiseProblem.gapMax (fun F ↦ 1 - F.unsatVal sem) (fun _ ↦ c) (fun _ ↦ s)).restrict
    {F | CSPIsExactK k F ∧ CSPHasDegreeAtMost D F ∧ CSPIsSimpleHypergraph F}

/-- Bounded-degree `Max-Ek-LIN-Γ` gap promise problem over a finite Abelian group `Γ`. -/
noncomputable abbrev GapBoundedDegreeExactKLinAbelian (Γ : Type) [AddCommGroup Γ] [DecidableEq Γ]
    (k D : ℕ) (c s : ℝ) : PromiseProblem (CSP Γ ℕ) :=
  GapBoundedDegreeCSP (fun b vals ↦ decide (vals.sum = b)) k D c s

/-- Bounded-degree Boolean `Max-Ek-LIN-2` (`Max-Ek-XORSAT`) gap promise problem. -/
noncomputable abbrev GapBoundedDegreeExactKLinBool (k D : ℕ) (c s : ℝ) :
    PromiseProblem (CSP Bool ℕ) :=
  GapBoundedDegreeCSP CSP.paritySem k D c s

/-- Bounded-degree Boolean `Max-Ek-LIN-2` gap promise problem on simple $k$-uniform hypergraphs. -/
noncomputable abbrev GapSimpleBoundedDegreeExactKLinBool (k D : ℕ) (c s : ℝ) :
    PromiseProblem (CSP Bool ℕ) :=
  GapSimpleBoundedDegreeCSP CSP.paritySem k D c s

/-- Bounded-degree `Max-E3-SAT` gap promise problem on 3-CNF formulas with three distinct
variables per clause and variable degree at most `D`. -/
@[expose] noncomputable def GapBoundedDegreeExactThreeSAT (D : ℕ) (c s : ℝ) :
    PromiseProblem (CNF ℕ) :=
  (PromiseProblem.gapMax (fun φ ↦ 1 - φ.unsatVal) (fun _ ↦ c) (fun _ ↦ s)).restrict
    {φ | φ.IsExactThreeDistinct ∧ CNFHasDegreeAtMost D φ}

theorem mem_yes_GapBoundedDegreeCSP {Rel Dom : Type} {sem : Rel → List Dom → Bool}
    {k D : ℕ} {c s : ℝ} {F : CSP Rel ℕ} :
    F ∈ (GapBoundedDegreeCSP sem k D c s).yes ↔
      (CSPIsExactK k F ∧ CSPHasDegreeAtMost D F) ∧ c ≤ 1 - F.unsatVal sem := by
  simp only [GapBoundedDegreeCSP, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

theorem mem_no_GapBoundedDegreeCSP {Rel Dom : Type} {sem : Rel → List Dom → Bool}
    {k D : ℕ} {c s : ℝ} (hsc : s < c) {F : CSP Rel ℕ} :
    F ∈ (GapBoundedDegreeCSP sem k D c s).no ↔
      (CSPIsExactK k F ∧ CSPHasDegreeAtMost D F) ∧ 1 - F.unsatVal sem ≤ s := by
  simp only [GapBoundedDegreeCSP, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ c) (s := fun _ ↦ s) hsc,
    Set.mem_ofPred_eq, and_comm]

theorem mem_yes_GapSimpleBoundedDegreeCSP {Rel Dom : Type} {sem : Rel → List Dom → Bool}
    {k D : ℕ} {c s : ℝ} {F : CSP Rel ℕ} :
    F ∈ (GapSimpleBoundedDegreeCSP sem k D c s).yes ↔
      (CSPIsExactK k F ∧ CSPHasDegreeAtMost D F ∧ CSPIsSimpleHypergraph F) ∧
        c ≤ 1 - F.unsatVal sem := by
  simp only [GapSimpleBoundedDegreeCSP, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

theorem mem_no_GapSimpleBoundedDegreeCSP {Rel Dom : Type} {sem : Rel → List Dom → Bool}
    {k D : ℕ} {c s : ℝ} (hsc : s < c) {F : CSP Rel ℕ} :
    F ∈ (GapSimpleBoundedDegreeCSP sem k D c s).no ↔
      (CSPIsExactK k F ∧ CSPHasDegreeAtMost D F ∧ CSPIsSimpleHypergraph F) ∧
        1 - F.unsatVal sem ≤ s := by
  simp only [GapSimpleBoundedDegreeCSP, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ c) (s := fun _ ↦ s) hsc,
    Set.mem_ofPred_eq, and_comm]

theorem mem_yes_GapBoundedDegreeExactThreeSAT {D : ℕ} {c s : ℝ} {φ : CNF ℕ} :
    φ ∈ (GapBoundedDegreeExactThreeSAT D c s).yes ↔
      (φ.IsExactThreeDistinct ∧ CNFHasDegreeAtMost D φ) ∧ c ≤ 1 - φ.unsatVal := by
  simp only [GapBoundedDegreeExactThreeSAT, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

theorem mem_no_GapBoundedDegreeExactThreeSAT {D : ℕ} {c s : ℝ} (hsc : s < c) {φ : CNF ℕ} :
    φ ∈ (GapBoundedDegreeExactThreeSAT D c s).no ↔
      (φ.IsExactThreeDistinct ∧ CNFHasDegreeAtMost D φ) ∧ 1 - φ.unsatVal ≤ s := by
  simp only [GapBoundedDegreeExactThreeSAT, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ ↦ c) (s := fun _ ↦ s) hsc,
    Set.mem_ofPred_eq, and_comm]

/-! ### Two-sided bounded-error promise reductions and `BPP` / `BQP` / `coRP` collapses -/

/-- A **randomized polynomial-time many-one reduction with two-sided error** between promise
problems `X` and `Y` with completeness probability `p_yes` and soundness probability `p_no`. -/
@[expose] def PromiseBPReducibleWithError {α β : Type} (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (p_yes p_no : ℝ) (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
    (∀ a ∈ X.yes, p_yes ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal) ∧
    (∀ a ∈ X.no, p_no ≤ ((ProbComp.eval (R a)).toOuterMeasure Y.no).toReal)

/-- Standard two-sided bounded-error randomized polynomial-time promise reduction with success
threshold `2 / 3` on both yes- and no-instances. -/
abbrev PromiseBPReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (X : PromiseProblem α) (Y : PromiseProblem β) : Prop :=
  PromiseBPReducibleWithError encA encB (2 / 3) (2 / 3) X Y

theorem PromiseBPReducibleWithError.mono {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {p₁ q₁ p₂ q₂ : ℝ} {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseBPReducibleWithError encA encB p₁ q₁ X Y) (hp : p₂ ≤ p₁) (hq : q₂ ≤ q₁) :
    PromiseBPReducibleWithError encA encB p₂ q₂ X Y := by
  obtain ⟨R, hR, hyes, hno⟩ := h
  exact ⟨R, hR, fun a ha ↦ hp.trans (hyes a ha), fun a ha ↦ hq.trans (hno a ha)⟩

/-- Every one-sided `RPReducibleWithError` reduction with uniform soundness `s` lifts to a
`PromiseBPReducibleWithError` reduction with completeness `1` and soundness `s`. -/
theorem promiseBPReducibleWithError_of_rpReducibleWithError {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {s : ℝ}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseProblem.RPReducibleWithError encA encB (fun _ ↦ s) X Y) :
    PromiseBPReducibleWithError encA encB 1 s X Y := by
  rw [PromiseProblem.rpReducibleWithError_iff_toOuterMeasure_eq_one] at h
  obtain ⟨R, hR, hyes, hno⟩ := h
  exact ⟨R, hR, fun a ha ↦ (hyes a ha).ge, hno⟩

/-- Precomposing a `PromiseBPReducibleWithError` reduction with a deterministic polynomial-time
promise reduction preserves its error thresholds. -/
theorem PromiseBPReducibleWithError.of_polyTimeReducible_left {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {p_yes p_no : ℝ} {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    (hXY : PromiseProblem.PolyTimeReducible encA encB X Y)
    (hYZ : PromiseBPReducibleWithError encB encC p_yes p_no Y Z) :
    PromiseBPReducibleWithError encA encC p_yes p_no X Z := by
  obtain ⟨f, hf, fyes, fno⟩ := hXY
  obtain ⟨R, hR, ryes, rno⟩ := hYZ
  exact ⟨fun a ↦ R (f a), hR.preprocess hf,
    fun a ha ↦ ryes (f a) (fyes ha), fun a ha ↦ rno (f a) (fno ha)⟩

/-- Postcomposing a `PromiseBPReducibleWithError` reduction with a deterministic polynomial-time
promise reduction preserves its error thresholds. -/
theorem PromiseBPReducibleWithError.trans_polyTimeReducible {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {p_yes p_no : ℝ} {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    (hXY : PromiseBPReducibleWithError encA encB p_yes p_no X Y)
    (hYZ : PromiseProblem.PolyTimeReducible encB encC Y Z) :
    PromiseBPReducibleWithError encA encC p_yes p_no X Z := by
  obtain ⟨R, hR, hyes, hno⟩ := hXY
  obtain ⟨g, hg, gyes, gno⟩ := hYZ
  refine ⟨fun a ↦ g <$> R a, hR.map_with (hg.comp (.snd encA encB)),
    fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · simp only [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact (hyes a ha).trans
      (PMF.toOuterMeasure_toReal_mono (ProbComp.eval (R a)) gyes.subset_preimage)
  · simp only [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    exact (hno a ha).trans
      (PMF.toOuterMeasure_toReal_mono (ProbComp.eval (R a)) gno.subset_preimage)

/-- Enlarging the target promise preserves `PromiseBPReducibleWithError`. -/
theorem PromiseBPReducibleWithError.of_subset {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {p_yes p_no : ℝ}
    {X : PromiseProblem α} {Y Y' : PromiseProblem β}
    (h : PromiseBPReducibleWithError encA encB p_yes p_no X Y)
    (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    PromiseBPReducibleWithError encA encB p_yes p_no X Y' := by
  obtain ⟨R, hR, ryes, rno⟩ := h
  exact ⟨R, hR,
    fun a ha ↦ (ryes a ha).trans (PMF.toOuterMeasure_toReal_mono _ hyes),
    fun a ha ↦ (rno a ha).trans (PMF.toOuterMeasure_toReal_mono _ hno)⟩

private def maj3Bool (b₁ b₂ b₃ : Bool) : Bool :=
  (b₁ && b₂) || (b₁ && b₃) || (b₂ && b₃)

private def repeatMaj3 {α : Type} (T : α → ProbComp Bool) (a : α) : ProbComp Bool :=
  T a >>= fun b₁ ↦
    T a >>= fun b₂ ↦
      (fun b₃ ↦ maj3Bool b₁ b₂ b₃) <$> T a

private theorem isPPTOn_repeatMaj3 {α : Type} {encA : α ↪ List Bool} {T : α → ProbComp Bool}
    (hT : IsPPTOn encA encBool T) :
    IsPPTOn encA encBool (repeatMaj3 T) := by
  unfold repeatMaj3
  have hfin : ComputableInPolyTime
      (fun q : (Bool × Bool) × Bool ↦ maj3Bool q.1.1 q.1.2 q.2)
      (encPair (encPair encBool encBool) encBool) encBool :=
    ComputableInPolyTime.of_finite _
  let enc1 := encPair encA encBool
  let enc2 := encPair enc1 encBool
  have hcb : ComputableInPolyTime
      (fun r : ((α × Bool) × Bool) × Bool ↦ maj3Bool r.1.1.2 r.1.2 r.2)
      (encPair enc2 encBool) encBool := by
    have hp12 : ComputableInPolyTime (fun r : ((α × Bool) × Bool) × Bool ↦ (r.1.1.2, r.1.2))
        (encPair enc2 encBool) (encPair encBool encBool) :=
      (((ComputableInPolyTime.snd encA encBool).comp
        (.fst enc1 encBool)).comp (.fst enc2 encBool)).prod
        ((ComputableInPolyTime.snd enc1 encBool).comp (.fst enc2 encBool))
    exact hfin.comp (hp12.prod (.snd enc2 encBool))
  have hstep2 : IsPPTOn enc2 encBool
      (fun p : (α × Bool) × Bool ↦ (fun b₃ ↦ maj3Bool p.1.2 p.2 b₃) <$> T p.1.1) :=
    ((hT.preprocess (.fst encA encBool)).preprocess (.fst enc1 encBool)).map_with hcb
  have hstep1 : IsPPTOn enc1 encBool
      (fun p : α × Bool ↦ T p.1 >>= fun b₂ ↦ (fun b₃ ↦ maj3Bool p.2 b₂ b₃) <$> T p.1) :=
    (hT.preprocess (.fst encA encBool)).bind_with hstep2
  exact hT.bind_with hstep1

private theorem probability_repeatMaj3 {α : Type} (T : α → ProbComp Bool) (a : α) :
    Pr[repeatMaj3 T a] = Pr[T a] ^ 2 * (3 - 2 * Pr[T a]) := by
  have h0 : (ProbComp.eval (T a) false).toReal = 1 - Pr[T a] := by
    have hsum : (ProbComp.eval (T a) true).toReal + (ProbComp.eval (T a) false).toReal = 1 := by
      have h := (ProbComp.eval (T a)).tsum_coe
      rw [tsum_fintype, Fintype.sum_bool] at h
      have h' := congrArg ENNReal.toReal h
      rwa [ENNReal.toReal_add ((ProbComp.eval (T a)).apply_ne_top _)
        ((ProbComp.eval (T a)).apply_ne_top _), ENNReal.toReal_one] at h'
    change (ProbComp.eval (T a) false).toReal = 1 - (ProbComp.eval (T a) true).toReal
    linarith
  unfold repeatMaj3
  simp only [ProbComp.probability_bind, Fintype.sum_bool, ProbComp.eval_map, PMF.map_apply]
  change _ = (ProbComp.eval (T a) true).toReal ^ 2 * (3 - 2 * (ProbComp.eval (T a) true).toReal)
  simp only [maj3Bool, tsum_fintype, Fintype.sum_bool]
  norm_num
  simp only [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), h0]
  ring

private theorem maj3_poly_mono :
    MonotoneOn (fun p : ℝ ↦ p ^ 2 * (3 - 2 * p)) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hu : 0 ≤ x := hx.1
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hv : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  have hid : y ^ 2 * (3 - 2 * y) - x ^ 2 * (3 - 2 * x) =
      (y - x) * (6 * x * (1 - y) + 3 * (1 - y) * (y - x) + 3 * x * (y - x) + (y - x) ^ 2) := by
    ring
  have hnonneg :
      0 ≤ (y - x) * (6 * x * (1 - y) + 3 * (1 - y) * (y - x) + 3 * x * (y - x) + (y - x) ^ 2) := by
    positivity
  linarith

private theorem probability_sampleList_ge_of_errorExponentAt_true' {β : Type}
    {enc : β ↪ List Bool} {q p : Polynomial ℕ} {V : β × List Bool → Bool} {b : β}
    (h : ErrorExponentAt enc q p V b true) :
    1 - 1 / (2 : ℝ) ^ q.eval (enc b).length ≤
      Pr[(fun w ↦ V (b, w)) <$> BitString.sampleList (p.eval (enc b).length)] := by
  have hcast : (2 : ℝ) ^ q.eval (enc b).length *
      ((2 : ℝ) ^ p.eval (enc b).length - acceptCount V b (p.eval (enc b).length)) ≤
      2 ^ p.eval (enc b).length := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_sub acceptCount_le_two_pow] using
      Nat.cast_le (α := ℝ).mpr (errorExponentAt_true_iff.1 h)
  rw [probability_sampleList_verifier, sub_le_iff_le_add, ← sub_le_iff_le_add',
    one_sub_div (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **`PromiseBPP` is closed under `PromiseBPReducible`**: if `X` reduces to `Y` by a two-sided
bounded-error randomized polynomial-time reduction and `Y ∈ PromiseBPP encB`, then
`X ∈ PromiseBPP encA`. -/
theorem PromiseBPReducible.mem_PromiseBPP {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseBPReducible encA encB X Y) (hY : Y ∈ PromiseBPP encB) :
    X ∈ PromiseBPP encA := by
  obtain ⟨R, hR, hyesR, hnoR⟩ := hXY
  obtain ⟨p, V, hV, hYV⟩ := mem_PromiseBPP_iff_forall_solvesWithErrorExponent.1 hY 5
  let M (b : β) : ProbComp Bool :=
    (fun w ↦ V (b, w)) <$> BitString.sampleList (p.eval (encB b).length)
  have hMyes (b : β) (hb : b ∈ Y.yes) : 31 / 32 ≤ Pr[M b] := by
    have h := probability_sampleList_ge_of_errorExponentAt_true' ((hYV b).1 hb)
    rw [Polynomial.eval_ofNat] at h
    linarith
  have hMno (b : β) (hb : b ∈ Y.no) : Pr[M b] ≤ 1 / 32 := by
    have h := Nat.cast_le (α := ℝ).mpr (errorExponentAt_false_iff.1 ((hYV b).2 hb))
    simp only [Polynomial.eval_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    rw [probability_sampleList_verifier, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  let T (a : α) : ProbComp Bool := R a >>= M
  have hT : IsPPTOn encA encBool T :=
    hR.bind (IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
      (ComputableInPolyTime.encoding_length encB)) hV)
  refine mem_PromiseBPP_iff_exists_isPPTOn.mpr
    ⟨repeatMaj3 T, isPPTOn_repeatMaj3 hT, fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · have hT_yes : 31 / 48 ≤ Pr[T a] := by
      have h := PMF.toOuterMeasure_bind_ge_mul (ProbComp.eval (R a)) (fun y ↦ ProbComp.eval (M y))
        Y.yes {true} (by norm_num : (0 : ℝ) ≤ 31 / 32) (hyesR a ha)
        fun y _ hy ↦ by simpa only [PMF.toOuterMeasure_apply_singleton] using hMyes y hy
      rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at h
      linarith
    have hT_le1 : Pr[T a] ≤ 1 := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using
        PMF.toOuterMeasure_toReal_le_one (ProbComp.eval (T a)) {true}
    rw [probability_repeatMaj3]
    calc
      (2 / 3 : ℝ) ≤ (31 / 48 : ℝ) ^ 2 * (3 - 2 * (31 / 48 : ℝ)) := by norm_num
      _ ≤ Pr[T a] ^ 2 * (3 - 2 * Pr[T a]) :=
        maj3_poly_mono ⟨by norm_num, by norm_num⟩ ⟨by linarith, hT_le1⟩ hT_yes
  · have hT_no : Pr[T a] ≤ 35 / 96 := by
      have hfail := PMF.toOuterMeasure_bind_failure_toReal_le
        (ProbComp.eval (R a)) (fun y ↦ ProbComp.eval (M y)) Y.no {true}
        (by norm_num : (0 : ℝ) ≤ 1 / 32) fun y _ hy ↦ by
          simpa only [PMF.toOuterMeasure_apply_singleton] using hMno y hy
      rw [← ProbComp.eval_bind, PMF.toOuterMeasure_apply_singleton] at hfail
      change Pr[T a] ≤ _ at hfail
      linarith [PMF.toOuterMeasure_toReal_add_compl (ProbComp.eval (R a)) Y.no, hnoR a ha]
    have hT_nonneg : 0 ≤ Pr[T a] := ENNReal.toReal_nonneg
    have hmaj_le : Pr[repeatMaj3 T a] ≤ 1 / 3 := by
      rw [probability_repeatMaj3]
      calc
        Pr[T a] ^ 2 * (3 - 2 * Pr[T a]) ≤
            (35 / 96 : ℝ) ^ 2 * (3 - 2 * (35 / 96 : ℝ)) :=
          maj3_poly_mono ⟨hT_nonneg, by linarith⟩ ⟨by norm_num, by norm_num⟩ hT_no
        _ ≤ 1 / 3 := by norm_num
    rw [ProbComp.probability_not]
    linarith

/-- If an NP-hard promise problem `X` reduces to `Y` via `PromiseBPReducible` and
`Y ∈ PromiseBPP encB`, then `NP encA ⊆ BPP encA`. -/
theorem NP_subset_BPP_of_nphard_promiseBPReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : PromiseProblem.NPHard encA X) (hXY : PromiseBPReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) :
    NP encA ⊆ BPP encA := by
  intro A hA
  exact ofSet_mem_PromiseBPP.mp ((hX encA A hA).mem_PromiseBPP (hXY.mem_PromiseBPP hY))

/-- If an NP-hard promise problem `X` reduces to `Y` via `PromiseBPReducible` and
`Y ∈ PromiseBPP encB` (in particular, if `Y ∈ PromiseP encB`), then `NP encA ⊆ BQP encA` too. -/
theorem NP_subset_BQP_of_nphard_promiseBPReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : PromiseProblem.NPHard encA X) (hXY : PromiseBPReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) :
    NP encA ⊆ BQP encA :=
  (NP_subset_BPP_of_nphard_promiseBPReducible hX hXY hY).trans BPP_subset_BQP

/-- If an NP-hard promise problem `X` reduces to `Y` via one-sided `RPReducible` and
`Y ∈ PromiseCoRP encB` (in particular, if `Y ∈ PromiseP encB`), then `NP encA ⊆ coRP encA`. -/
theorem NP_subset_coRP_of_nphard_rpReducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : PromiseProblem.NPHard encA X) (hXY : PromiseProblem.RPReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) :
    NP encA ⊆ coRP encA :=
  PromiseProblem.NP_subset_coRP_of_forall_rpReducible
    (fun A hA ↦ (hX encA A hA).trans_rpReducible hXY) hY

/-! ### Degree-multiplying four-clause compilation from `Max-E3-LIN-2` to `Max-E3-SAT` -/

private theorem countP_toCNFBounded_le_four_mul {c : Constraint Bool ℕ} (hc : c.scope.length = 3)
    (v : ℕ) :
    ((Constraint.toCNFBounded 3 CSP.paritySem c).countP fun cl ↦
      cl.any fun lit ↦ decide (lit.1 = v)) ≤
      4 * (if v ∈ c.scope then 1 else 0) := by
  by_cases hv : v ∈ c.scope
  · rw [ite_eq_left hv, Nat.mul_one]
    have hlen4 : (Constraint.toCNFBounded 3 CSP.paritySem c).length = 4 := by
      have h := CSP.length_toCNFBounded_parity (F := [c]) fun e he ↦ by
        rcases List.mem_singleton.mp he with rfl
        exact hc
      simpa [CSP.toCNFBounded] using h
    exact List.countP_le_length.trans hlen4.le
  · rw [ite_eq_right hv, Nat.mul_zero, Nat.le_zero]
    refine List.countP_eq_zero.mpr fun cl hcl ↦ ?_
    simp only [Bool.not_eq_true, List.any_eq_false, decide_eq_true_eq]
    intro lit hlit hlitv
    subst hlitv
    have hmem : lit.1 ∈ (Constraint.toCNFBounded 3 CSP.paritySem c).vars := by
      simp only [CNF.vars, List.mem_map, List.mem_flatten]
      exact ⟨lit, ⟨cl, hcl, hlit⟩, rfl⟩
    exact hv (Constraint.mem_vars_toCNFBounded hmem)

/-- Under the four-clause parity gadget `CSP.toCNFBounded 3 CSP.paritySem`, each variable's clause
degree in the compiled 3-CNF formula is at most `4` times its constraint degree in `F`. -/
theorem cnfVarDegree_toCNFBounded_parity_le {F : CSP Bool ℕ} (hF : CSPIsExactK 3 F) (v : ℕ) :
    cnfVarDegree (F.toCNFBounded 3 CSP.paritySem) v ≤ 4 * cspVarDegree F v := by
  induction F with
  | nil => simp [cnfVarDegree, cspVarDegree, CSP.toCNFBounded]
  | cons c F ih =>
    have hc : c.scope.length = 3 := (hF c List.mem_cons_self).1
    have hrest : CSPIsExactK 3 F := fun e he ↦ hF e (List.mem_cons_of_mem c he)
    simp only [cnfVarDegree, CSP.toCNFBounded, List.flatMap_cons, List.countP_append,
      cspVarDegree, List.countP_cons]
    have hhead := countP_toCNFBounded_le_four_mul hc v
    have htail := ih hrest
    simp only [cnfVarDegree, cspVarDegree, CSP.toCNFBounded] at htail
    by_cases hv : v ∈ c.scope
    · rw [ite_eq_left hv] at hhead
      simp only [hv, decide_true, ↓reduceIte]
      omega
    · rw [ite_eq_right hv] at hhead
      simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Deterministic polynomial-time reduction from `GapBoundedDegreeExactKLinBool 3 (D / 4) c s` to
`GapBoundedDegreeExactThreeSAT D ((3 + c) / 4) ((3 + s) / 4)`. -/
theorem polyTimeReducible_gapBoundedDegreeExact3Lin_3SAT (D : ℕ) {c s : ℝ} (hsc : s < c) :
    PromiseProblem.PolyTimeReducible (encCSP encBool encNat) encCNF
      (GapBoundedDegreeExactKLinBool 3 (D / 4) c s)
      (GapBoundedDegreeExactThreeSAT D ((3 + c) / 4) ((3 + s) / 4)) := by
  refine ⟨CSP.toCNFBounded 3 CSP.paritySem,
    CSP.computableInPolyTime_toCNFBounded_of_finite encBool encNat 3 CSP.paritySem,
    fun F hF ↦ ?_, fun F hF ↦ ?_⟩
  · rw [mem_yes_GapBoundedDegreeCSP] at hF
    rw [mem_yes_GapBoundedDegreeExactThreeSAT,
      CSP.unsatVal_toCNFBounded_parity fun e he ↦ (hF.1.1 e he).1]
    refine ⟨⟨CSP.isExactThreeDistinct_toCNFBounded_parity hF.1.1, fun v ↦ ?_⟩, by linarith⟩
    exact (cnfVarDegree_toCNFBounded_parity_le hF.1.1 v).trans
      ((Nat.mul_le_mul_left 4 (hF.1.2 v)).trans (Nat.mul_div_le D 4))
  · rw [mem_no_GapBoundedDegreeCSP hsc] at hF
    rw [mem_no_GapBoundedDegreeExactThreeSAT (by linarith),
      CSP.unsatVal_toCNFBounded_parity fun e he ↦ (hF.1.1 e he).1]
    refine ⟨⟨CSP.isExactThreeDistinct_toCNFBounded_parity hF.1.1, fun v ↦ ?_⟩, by linarith⟩
    exact (cnfVarDegree_toCNFBounded_parity_le hF.1.1 v).trans
      ((Nat.mul_le_mul_left 4 (hF.1.2 v)).trans (Nat.mul_div_le D 4))

end CslibFrontier.Complexity
