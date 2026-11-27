/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi

import Mathlib.Data.List.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Left-Regular `p`-to-`1` Label Cover and Unique Games

This module defines executable left-regular bipartite `p`-to-`1` Label Cover instances, their
polynomial-time binary encodings, satisfaction values, the gap promise problem
`GapPToOneLabelCover`, and the left-regular bipartite Unique Games Conjecture
`LeftRegularUniqueGamesConjecture`.

## Main definitions

* `CslibFrontier.Computability.Complexity.Problems.LabelCoverEdge`,
  `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance`: executable bipartite
  `p`-to-`1`
  Label Cover instances.
* `CslibFrontier.Computability.Complexity.Problems.encLabelCoverEdge`,
  `CslibFrontier.Computability.Complexity.Problems.encLabelCoverInstance`: polynomial-time
  encodings.
* `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.IsPToOne`,
  `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.IsLeftRegular`: structural
  promises.
* `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.assignmentValue`,
  `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.instanceValue`: satisfaction
  values.
* `CslibFrontier.Computability.Complexity.Problems.GapPToOneLabelCover`: the `(c, s)`-gap promise
  problem.
* `CslibFrontier.Computability.Complexity.Problems.LeftRegularUniqueGamesConjecture`: the
  left-regular
  bipartite Unique Games Conjecture (`Prop`).

## Main results

* `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.assignmentValue_nonneg`,
  `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.assignmentValue_le_one`,
  `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.instanceValue_le_one`: basic
  value bounds.
* `CslibFrontier.Computability.Complexity.Problems.LabelCoverInstance.edges_length_eq_mul`:
  left-regular
  edge count identity `edges.length = numLeft * deg`.
* `CslibFrontier.Computability.Complexity.Problems.GapPToOneLabelCover_mono`: monotonicity in `(c,
  s)`.
* `CslibFrontier.Computability.Complexity.Problems.LeftRegularUniqueGamesConjecture_iff`: explicit
  equivalence
  characterization (non-`@[simp]`).
-/

public section

open Cslib.Complexity Turing.MultiTapeTM

namespace CslibFrontier.Computability.Complexity.Problems

/-! ### Executable `p`-to-`1` Label Cover instances and encodings -/

/-- A directed bipartite edge `(left, right)` carrying a projection `proj : Fin (p * r) → Fin r`
from right labels to left labels. -/
@[ext]
structure LabelCoverEdge (p r : ℕ) where
  /-- The left vertex index. -/
  left : ℕ
  /-- The right vertex index. -/
  right : ℕ
  /-- The projection constraint `Fin (p * r) → Fin r`. -/
  proj : Fin (p * r) → Fin r
  deriving DecidableEq

/-- An executable bipartite `p`-to-`1` Label Cover instance with `numLeft` left vertices,
`numRight` right vertices, and an ordered list of edges (allowing parallel edges). -/
@[ext]
structure LabelCoverInstance (p r : ℕ) where
  /-- Number of left vertices (`0 .. numLeft - 1`). -/
  numLeft : ℕ
  /-- Number of right vertices (`0 .. numRight - 1`). -/
  numRight : ℕ
  /-- Ordered list of bipartite projection edges. -/
  edges : List (LabelCoverEdge p r)
  deriving DecidableEq

/-- Polynomial-time encoding of a `LabelCoverEdge p r` via unary endpoints and a finite table for
the projection `Fin (p * r) → Fin r`. -/
noncomputable def encLabelCoverEdge (p r : ℕ) : LabelCoverEdge p r ↪ List Bool where
  toFun e := encPair encUnary (encPair encUnary (encPi (encFinEnum (Fin r))))
    (e.left, e.right, e.proj)
  inj' := by
    intro e₁ e₂ h
    have h' := (encPair encUnary (encPair encUnary (encPi (encFinEnum (Fin r))))).injective h
    exact LabelCoverEdge.ext (congrArg Prod.fst h') (congrArg (fun q => q.2.1) h')
      (congrArg (fun q => q.2.2) h')

/-- Polynomial-time encoding of a `LabelCoverInstance p r` via unary vertex counts and a framed
list of encoded edges. -/
noncomputable def encLabelCoverInstance (p r : ℕ) : LabelCoverInstance p r ↪ List Bool where
  toFun G := encPair encUnary (encPair encUnary (encList (encLabelCoverEdge p r)))
    (G.numLeft, G.numRight, G.edges)
  inj' := by
    intro G₁ G₂ h
    have h' := (encPair encUnary (encPair encUnary (encList (encLabelCoverEdge p r)))).injective h
    exact LabelCoverInstance.ext (congrArg Prod.fst h') (congrArg (fun q => q.2.1) h')
      (congrArg (fun q => q.2.2) h')

private theorem isPolyTime_edge_toTuple (p r : ℕ) :
    ComputableInPolyTime (fun e : LabelCoverEdge p r => (e.left, e.right, e.proj))
      (encLabelCoverEdge p r) (encPair encUnary (encPair encUnary (encPi (encFinEnum (Fin r))))) :=
  .of_eq fun _ => rfl

private theorem isPolyTime_inst_toTuple (p r : ℕ) :
    ComputableInPolyTime (fun G : LabelCoverInstance p r => (G.numLeft, G.numRight, G.edges))
      (encLabelCoverInstance p r)
      (encPair encUnary (encPair encUnary (encList (encLabelCoverEdge p r)))) :=
  .of_eq fun _ => rfl

@[fun_prop]
theorem isPolyTime_edge_left {Input : Type} {encIn : Input ↪ List Bool} {p r : ℕ}
    {f : Input → LabelCoverEdge p r}
    (hf : ComputableInPolyTime f encIn (encLabelCoverEdge p r)) :
    ComputableInPolyTime (fun x => (f x).left) encIn encUnary :=
  (isPolyTime_edge_toTuple p r).fst'.comp hf

@[fun_prop]
theorem isPolyTime_edge_right {Input : Type} {encIn : Input ↪ List Bool} {p r : ℕ}
    {f : Input → LabelCoverEdge p r}
    (hf : ComputableInPolyTime f encIn (encLabelCoverEdge p r)) :
    ComputableInPolyTime (fun x => (f x).right) encIn encUnary :=
  (isPolyTime_edge_toTuple p r).snd'.fst'.comp hf

@[fun_prop]
theorem isPolyTime_edge_proj {Input : Type} {encIn : Input ↪ List Bool} {p r : ℕ}
    {f : Input → LabelCoverEdge p r}
    (hf : ComputableInPolyTime f encIn (encLabelCoverEdge p r)) :
    ComputableInPolyTime (fun x => (f x).proj) encIn (encPi (encFinEnum (Fin r))) :=
  (isPolyTime_edge_toTuple p r).snd'.snd'.comp hf

@[fun_prop]
theorem isPolyTime_inst_numLeft {Input : Type} {encIn : Input ↪ List Bool} {p r : ℕ}
    {f : Input → LabelCoverInstance p r}
    (hf : ComputableInPolyTime f encIn (encLabelCoverInstance p r)) :
    ComputableInPolyTime (fun x => (f x).numLeft) encIn encUnary :=
  (isPolyTime_inst_toTuple p r).fst'.comp hf

@[fun_prop]
theorem isPolyTime_inst_numRight {Input : Type} {encIn : Input ↪ List Bool} {p r : ℕ}
    {f : Input → LabelCoverInstance p r}
    (hf : ComputableInPolyTime f encIn (encLabelCoverInstance p r)) :
    ComputableInPolyTime (fun x => (f x).numRight) encIn encUnary :=
  (isPolyTime_inst_toTuple p r).snd'.fst'.comp hf

@[fun_prop]
theorem isPolyTime_inst_edges {Input : Type} {encIn : Input ↪ List Bool} {p r : ℕ}
    {f : Input → LabelCoverInstance p r}
    (hf : ComputableInPolyTime f encIn (encLabelCoverInstance p r)) :
    ComputableInPolyTime (fun x => (f x).edges) encIn (encList (encLabelCoverEdge p r)) :=
  (isPolyTime_inst_toTuple p r).snd'.snd'.comp hf

/-! ### Structural properties and satisfaction value -/

namespace LabelCoverInstance

/-- Every edge constraint of `G` is a `p`-to-`1` function `Fin (p * r) → Fin r`. -/
@[expose] def IsPToOne {p r : ℕ} (G : LabelCoverInstance p r) : Prop :=
  ∀ e ∈ G.edges, ∀ j : Fin r, (Finset.univ.filter fun i : Fin (p * r) => e.proj i = j).card = p

/-- `G` is a nonempty well-formed left-regular bipartite instance: `numLeft > 0`, `numRight > 0`,
all edge endpoints are in bounds, and every left vertex has the same positive degree `d > 0`. -/
@[expose] def IsLeftRegular {p r : ℕ} (G : LabelCoverInstance p r) : Prop :=
  0 < G.numLeft ∧ 0 < G.numRight ∧
    (∀ e ∈ G.edges, e.left < G.numLeft ∧ e.right < G.numRight) ∧
    ∃ d : ℕ, 0 < d ∧ ∀ u : Fin G.numLeft,
      (G.edges.filter fun e => decide (e.left = u.1)).length = d

/-- Boolean satisfaction check of a single edge `(left, right, proj)` by `(σL, σR)`. -/
@[expose] def edgeSatisfied {p r : ℕ} (σL : ℕ → Fin r) (σR : ℕ → Fin (p * r))
    (e : LabelCoverEdge p r) : Bool :=
  decide (e.proj (σR e.right) = σL e.left)

/-- Fraction of edges of `G` satisfied by a labelling `(σL, σR)` (`0` if `G.edges = []`). -/
@[expose] noncomputable def assignmentValue {p r : ℕ} (G : LabelCoverInstance p r)
    (σL : ℕ → Fin r) (σR : ℕ → Fin (p * r)) : ℝ :=
  ((G.edges.countP (edgeSatisfied σL σR) : ℕ) : ℝ) / (G.edges.length : ℝ)

/-- Maximum satisfaction value of `G` over all labellings `(σL, σR)`. -/
noncomputable def instanceValue {p r : ℕ} (G : LabelCoverInstance p r) : ℝ :=
  ⨆ (σL : ℕ → Fin r), ⨆ (σR : ℕ → Fin (p * r)), G.assignmentValue σL σR

theorem assignmentValue_nonneg {p r : ℕ} (G : LabelCoverInstance p r)
    (σL : ℕ → Fin r) (σR : ℕ → Fin (p * r)) :
    0 ≤ G.assignmentValue σL σR := by
  unfold assignmentValue
  positivity

theorem assignmentValue_le_one {p r : ℕ} (G : LabelCoverInstance p r)
    (σL : ℕ → Fin r) (σR : ℕ → Fin (p * r)) :
    G.assignmentValue σL σR ≤ 1 := by
  unfold assignmentValue
  by_cases h : G.edges.length = 0
  · simp [h]
  · have hpos : (0 : ℝ) < (G.edges.length : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
    rw [div_le_one hpos]
    exact_mod_cast List.countP_le_length

theorem bddAbove_assignmentValue_right {p r : ℕ} (G : LabelCoverInstance p r) (σL : ℕ → Fin r) :
    BddAbove (Set.range fun σR : ℕ → Fin (p * r) => G.assignmentValue σL σR) :=
  ⟨1, fun _ ⟨_, h⟩ => h ▸ G.assignmentValue_le_one _ _⟩

theorem bddAbove_assignmentValue_left {p r : ℕ} (G : LabelCoverInstance p r) :
    BddAbove (Set.range fun σL : ℕ → Fin r =>
      ⨆ (σR : ℕ → Fin (p * r)), G.assignmentValue σL σR) := by
  refine ⟨1, fun _ ⟨σL, h⟩ => h ▸ ?_⟩
  by_cases hne : Nonempty (ℕ → Fin (p * r))
  · exact ciSup_le fun σR => G.assignmentValue_le_one σL σR
  · have : IsEmpty (ℕ → Fin (p * r)) := not_nonempty_iff.mp hne
    dsimp only
    rw [Real.iSup_of_isEmpty]
    norm_num

theorem assignmentValue_le_instanceValue {p r : ℕ} (G : LabelCoverInstance p r)
    (σL : ℕ → Fin r) (σR : ℕ → Fin (p * r)) :
    G.assignmentValue σL σR ≤ G.instanceValue := by
  unfold instanceValue
  exact (le_ciSup (G.bddAbove_assignmentValue_right σL) σR).trans
    (le_ciSup G.bddAbove_assignmentValue_left σL)

theorem instanceValue_le_one {p r : ℕ} (G : LabelCoverInstance p r) :
    G.instanceValue ≤ 1 := by
  unfold instanceValue
  by_cases hL : Nonempty (ℕ → Fin r)
  · refine ciSup_le fun σL => ?_
    by_cases hR : Nonempty (ℕ → Fin (p * r))
    · exact ciSup_le fun σR => G.assignmentValue_le_one σL σR
    · have : IsEmpty (ℕ → Fin (p * r)) := not_nonempty_iff.mp hR
      rw [Real.iSup_of_isEmpty]
      norm_num
  · have : IsEmpty (ℕ → Fin r) := not_nonempty_iff.mp hL
    rw [Real.iSup_of_isEmpty]
    norm_num

theorem instanceValue_le_iff {p r : ℕ} (hr : 0 < r) (hp : 0 < p)
    (G : LabelCoverInstance p r) {s : ℝ} :
    G.instanceValue ≤ s ↔ ∀ σL σR, G.assignmentValue σL σR ≤ s := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have : Nonempty (Fin (p * r)) := ⟨⟨0, Nat.mul_pos hp hr⟩⟩
  constructor
  · intro h σL σR
    exact (G.assignmentValue_le_instanceValue σL σR).trans h
  · intro h
    exact ciSup_le fun σL => ciSup_le fun σR => h σL σR

/-- If `G` is left-regular with degree `d`, then `G.edges.length = G.numLeft * d`. -/
theorem edges_length_eq_mul {p r : ℕ} {G : LabelCoverInstance p r} {d : ℕ}
    (hbounds : ∀ e ∈ G.edges, e.left < G.numLeft)
    (hdeg : ∀ u : Fin G.numLeft, (G.edges.filter fun e => decide (e.left = u.1)).length = d) :
    G.edges.length = G.numLeft * d := by
  have hsum : ∀ es : List (LabelCoverEdge p r), (∀ e ∈ es, e.left < G.numLeft) →
      ∑ u : Fin G.numLeft, (es.filter fun e => decide (e.left = u.1)).length = es.length := by
    intro es
    induction es with
    | nil => intro _; simp
    | cons e es ih =>
      intro hb
      simp only [List.filter_cons, List.length_cons]
      have hb' : ∀ e' ∈ es, e'.left < G.numLeft := fun e' he' =>
        hb e' (List.mem_cons_of_mem e he')
      have he_lt : e.left < G.numLeft := hb e List.mem_cons_self
      have hsplit : ∀ u : Fin G.numLeft,
          (if decide (e.left = u.1) = true then e :: es.filter (fun e' => decide (e'.left = u.1))
            else es.filter (fun e' => decide (e'.left = u.1))).length =
          (if u = ⟨e.left, he_lt⟩ then 1 else 0) +
            (es.filter fun e' => decide (e'.left = u.1)).length := by
        intro u
        by_cases hu : u = ⟨e.left, he_lt⟩
        · subst hu; simp; omega
        · have hne : e.left ≠ u.1 := fun h => hu (Fin.ext h.symm)
          simp [hne, hu]
      simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [ih hb']
      omega
  calc
    G.edges.length = ∑ u : Fin G.numLeft, (G.edges.filter fun e => decide (e.left = u.1)).length :=
      (hsum G.edges hbounds).symm
    _ = ∑ _u : Fin G.numLeft, d := Finset.sum_congr rfl fun u _ => hdeg u
    _ = G.numLeft * d := by simp

theorem edges_pos_of_isLeftRegular {p r : ℕ} {G : LabelCoverInstance p r} (h : G.IsLeftRegular) :
    0 < G.edges.length := by
  obtain ⟨hL, _, hbounds, d, hd, hdeg⟩ := h
  rw [edges_length_eq_mul (fun e he => (hbounds e he).1) hdeg]
  exact Nat.mul_pos hL hd

end LabelCoverInstance

/-! ### Gap `p`-to-`1` Label Cover and Left-Regular Unique Games Conjecture -/

/-- The `(c, s)`-gap promise problem for left-regular `p`-to-`1` Label Cover with right-label
domain size `p * r` and left-label domain size `r`. -/
@[expose] noncomputable def GapPToOneLabelCover (p r : ℕ) (c s : ℝ) :
    PromiseProblem (LabelCoverInstance p r) :=
  (PromiseProblem.gapMax LabelCoverInstance.instanceValue (fun _ => c) (fun _ => s)).restrict
    {G | G.IsPToOne ∧ G.IsLeftRegular}

/-- Monotonicity of `GapPToOneLabelCover` under weakening the gap thresholds. -/
theorem GapPToOneLabelCover_mono {p r : ℕ} {c c' s s' : ℝ}
    (hc : c' ≤ c) (hs : s ≤ s') (hsc : s' < c') :
    (GapPToOneLabelCover p r c s).yes ⊆ (GapPToOneLabelCover p r c' s').yes ∧
      (GapPToOneLabelCover p r c s).no ⊆ (GapPToOneLabelCover p r c' s').no :=
  ⟨fun _ ⟨h, hr⟩ => ⟨hc.trans h, hr⟩,
   fun _ ⟨⟨h, _⟩, hr⟩ => ⟨⟨h.trans hs, hsc⟩, hr⟩⟩

/-- **Left-Regular Bipartite Unique Games Conjecture**:
for every `ε, δ > 0` with `δ < 1 - ε`, there exists a domain size `r ≥ 1` such that
`(1 - ε, δ)`-approximating left-regular `1`-to-`1` Label Cover is NP-hard.
Stated strictly as a `Prop` hypothesis (not an axiom).
-/
def LeftRegularUniqueGamesConjecture : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 - ε →
    ∃ r : ℕ, 0 < r ∧
      PromiseProblem.NPHard (encLabelCoverInstance 1 r) (GapPToOneLabelCover 1 r (1 - ε) δ)

/-- Equivalence characterization of `LeftRegularUniqueGamesConjecture` (non-`@[simp]`). -/
theorem LeftRegularUniqueGamesConjecture_iff :
    LeftRegularUniqueGamesConjecture ↔
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 - ε →
        ∃ r : ℕ, 0 < r ∧
          PromiseProblem.NPHard (encLabelCoverInstance 1 r)
            (GapPToOneLabelCover 1 r (1 - ε) δ) :=
  Iff.rfl

/-- Unconditional positive/negative carrier witness for `GapPToOneLabelCover` (`p = 2, r = 1`,
`numLeft = 1`, `numRight = 1`, single `2`-to-`1` edge): value is `1`, so it is a `yes`-instance
of `(1, 1/2)` and outside the `no` set. -/
private theorem witness_twoToOne_trivial_yes :
    let G : LabelCoverInstance 2 1 := ⟨1, 1, [⟨0, 0, fun _ => 0⟩]⟩
    G.IsPToOne ∧ G.IsLeftRegular ∧ G.instanceValue = 1 := by
  let G : LabelCoverInstance 2 1 := ⟨1, 1, [⟨0, 0, fun _ => 0⟩]⟩
  have hp : G.IsPToOne := by
    intro e he j
    simp only [G, List.mem_singleton] at he
    subst he
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    simp
  have hreg : G.IsLeftRegular := by
    refine ⟨by simp [G], by simp [G], ?_, 1, by omega, ?_⟩
    · intro e he; simp only [G, List.mem_singleton] at he; subst he; simp [G]
    · intro u
      have hu : u = 0 := Fin.ext (by have := u.2; dsimp only [G] at this ⊢; omega)
      subst hu
      simp [G]
  have hval : G.instanceValue = 1 := by
    refine le_antisymm G.instanceValue_le_one ?_
    have h1 : G.assignmentValue (fun _ => 0) (fun _ => 0) = 1 := by
      simp [G, LabelCoverInstance.assignmentValue, LabelCoverInstance.edgeSatisfied]
    rw [← h1]
    exact G.assignmentValue_le_instanceValue _ _
  exact ⟨hp, hreg, hval⟩

/-- Unconditional negative witness: a `1`-to-`1` left-regular instance with `numLeft = 1`,
`numRight = 1`, `r = 2`, where two parallel edges (`id` and `swap`) cannot both be satisfied,
so `instanceValue ≤ 1 / 2`. -/
private theorem witness_oneToOne_strictly_unsat :
    let swap : Fin (1 * 2) → Fin 2 := fun i => ⟨1 - i.1, by omega⟩
    let id1 : Fin (1 * 2) → Fin 2 := fun i => ⟨i.1, by omega⟩
    let G : LabelCoverInstance 1 2 := ⟨1, 1, [⟨0, 0, id1⟩, ⟨0, 0, swap⟩]⟩
    G.IsPToOne ∧ G.IsLeftRegular ∧ G.instanceValue ≤ 1 / 2 := by
  let swap : Fin (1 * 2) → Fin 2 := fun i => ⟨1 - i.1, by omega⟩
  let id1 : Fin (1 * 2) → Fin 2 := fun i => ⟨i.1, by omega⟩
  let G : LabelCoverInstance 1 2 := ⟨1, 1, [⟨0, 0, id1⟩, ⟨0, 0, swap⟩]⟩
  have hp : G.IsPToOne := by
    intro e he j
    simp only [G, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have : (Finset.univ.filter fun i : Fin (1 * 2) => id1 i = j) = {⟨j.1, by omega⟩} := by
        ext i; simp [id1, Fin.ext_iff]
      simp [this]
    · have : (Finset.univ.filter fun i : Fin (1 * 2) => swap i = j) = {⟨1 - j.1, by omega⟩} := by
        ext i
        simp only [swap, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff]
        omega
      simp [this]
  have hreg : G.IsLeftRegular := by
    refine ⟨by simp [G], by simp [G], ?_, 2, by omega, ?_⟩
    · intro e he
      simp only [G, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [G]
    · intro u
      have hu : u = 0 := Fin.ext (by have := u.2; dsimp only [G] at this ⊢; omega)
      subst hu
      simp [G]
  have hval : G.instanceValue ≤ 1 / 2 := by
    rw [G.instanceValue_le_iff (by omega) (by omega)]
    intro σL σR
    simp only [G, LabelCoverInstance.assignmentValue, LabelCoverInstance.edgeSatisfied,
      List.countP_cons, List.countP_nil, List.length_cons, List.length_nil]
    have hnot : ¬ (id1 (σR 0) = σL 0 ∧ swap (σR 0) = σL 0) := by
      rintro ⟨h1, h2⟩
      have := congrArg Fin.val (h1.trans h2.symm)
      simp only [id1, swap] at this
      omega
    by_cases h1 : id1 (σR 0) = σL 0 <;> by_cases h2 : swap (σR 0) = σL 0
    · exact absurd ⟨h1, h2⟩ hnot
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  exact ⟨hp, hreg, hval⟩

end CslibFrontier.Computability.Complexity.Problems
