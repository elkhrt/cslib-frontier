/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Defs

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quota-Parameterized Proportionality Problems in Approval-Based Multiwinner Voting

This module defines the quota-parameterized approval-based multiwinner voting decision problems
`α`-JR, `α`-EJR, and `α`-EJR+ (both committee verification and committee existence) over concrete
Turing-machine encodings (`encEncodedElection` and `encEncodedElectionCommittee`), and proves their
fundamental membership bounds in `P`, `NP`, and `coNP`.

## Main definitions

* `CslibFrontier.Complexity.ApprovalVoting.ApprovalElection`: approval-based multiwinner election.
* `CslibFrontier.Complexity.ApprovalVoting.EncodedElection`,
  `CslibFrontier.Complexity.ApprovalVoting.encEncodedElection`: matrix-encoded election instances.
* `CslibFrontier.Complexity.ApprovalVoting.EncodedElectionCommittee`,
  `CslibFrontier.Complexity.ApprovalVoting.encEncodedElectionCommittee`: encoded `(I, W)` pairs.
* `CslibFrontier.Complexity.ApprovalVoting.AlphaJRVerify`,
  `CslibFrontier.Complexity.ApprovalVoting.AlphaEJRVerify`,
  `CslibFrontier.Complexity.ApprovalVoting.AlphaEJRPlusVerify`: verification problems.
* `CslibFrontier.Complexity.ApprovalVoting.AlphaJRProblem`,
  `CslibFrontier.Complexity.ApprovalVoting.AlphaEJRProblem`,
  `CslibFrontier.Complexity.ApprovalVoting.AlphaEJRPlusProblem`: existence problems.

## Main results

* `CslibFrontier.Complexity.ApprovalVoting.alphaJRVerify_mem_P`: `AlphaJRVerify α ∈ P`.
* `CslibFrontier.Complexity.ApprovalVoting.alphaEJRPlusVerify_mem_P`: `AlphaEJRPlusVerify α ∈ P`.
* `CslibFrontier.Complexity.ApprovalVoting.alphaJRProblem_mem_NP`: `AlphaJRProblem α ∈ NP`.
* `CslibFrontier.Complexity.ApprovalVoting.alphaEJRPlusProblem_mem_NP`:
  `AlphaEJRPlusProblem α ∈ NP`.
* `CslibFrontier.Complexity.ApprovalVoting.alphaEJRVerify_mem_coNP`: `AlphaEJRVerify α ∈ coNP`.
-/

public section

namespace CslibFrontier.Complexity.ApprovalVoting

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity
open scoped BigOperators

/-! ### Core approval-voting definitions -/

/-- An approval-based multiwinner election instance over finite voter set `V` and candidate set
`C`, with target committee size `1 ≤ size ≤ |C|` and nonempty electorate. -/
@[ext]
structure ApprovalElection (V C : Type*) [Fintype V] [Fintype C] where
  /-- Approval ballot `A_v ⊆ C` of each voter `v`. -/
  approvals : V → Finset C
  /-- Target committee size `k`. -/
  size : ℕ
  /-- The electorate `V` is nonempty. -/
  voters_nonempty : Nonempty V
  /-- Committee size is positive. -/
  size_pos : 0 < size
  /-- Committee size does not exceed the number of candidates. -/
  size_le : size ≤ Fintype.card C

/-- Common approved candidates `⋂_{v ∈ S} A_v` of a voter group `S`. -/
def ApprovalElection.commonApprovals {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (E : ApprovalElection V C) (S : Finset V) : Finset C :=
  Finset.univ.filter fun c ↦ ∀ v ∈ S, c ∈ E.approvals v

theorem ApprovalElection.mem_commonApprovals_iff {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : ApprovalElection V C) {S : Finset V} {c : C} :
    c ∈ E.commonApprovals S ↔ ∀ v ∈ S, c ∈ E.approvals v := by
  simp [commonApprovals]

/-- A voter group `S` is `(α, ℓ)`-cohesive if `1 ≤ ℓ ≤ k`, `|S| ≥ α ℓ n / k`, and
`|⋂_{v ∈ S} A_v| ≥ ℓ`. -/
def ApprovalElection.IsAlphaCohesive {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (E : ApprovalElection V C) (α : ℝ) (ℓ : ℕ) (S : Finset V) : Prop :=
  1 ≤ ℓ ∧ ℓ ≤ E.size ∧
    α * (ℓ : ℝ) * ((Fintype.card V : ℝ) / (E.size : ℝ)) ≤ (S.card : ℝ) ∧
    ℓ ≤ (E.commonApprovals S).card

/-- A committee `W` satisfies `α`-JR if every `(α, 1)`-cohesive group has a voter approving at
least one member of `W`. -/
def ApprovalElection.SatisfiesAlphaJR {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (E : ApprovalElection V C) (α : ℝ) (W : Finset C) : Prop :=
  ∀ S : Finset V, E.IsAlphaCohesive α 1 S → ∃ v ∈ S, 1 ≤ (E.approvals v ∩ W).card

/-- A committee `W` satisfies `α`-EJR if every `(α, ℓ)`-cohesive group has a voter approving at
least `ℓ` members of `W`. -/
def ApprovalElection.SatisfiesAlphaEJR {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (E : ApprovalElection V C) (α : ℝ) (W : Finset C) : Prop :=
  ∀ ℓ : ℕ, ∀ S : Finset V, E.IsAlphaCohesive α ℓ S → ∃ v ∈ S, ℓ ≤ (E.approvals v ∩ W).card

/-- A committee `W` satisfies `α`-EJR+ if no `c ∈ C \ W`, `ℓ ∈ [k]`, and `S ⊆ N` with
`|S| ≥ α ℓ n / k` and `c ∈ ⋂_{v ∈ S} A_v` satisfy `|A_v ∩ W| < ℓ` for all `v ∈ S`. -/
def ApprovalElection.SatisfiesAlphaEJRPlus {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (E : ApprovalElection V C) (α : ℝ) (W : Finset C) : Prop :=
  ¬∃ (c : C) (S : Finset V) (ℓ : ℕ),
    c ∉ W ∧ 1 ≤ ℓ ∧ ℓ ≤ E.size ∧
      α * (ℓ : ℝ) * ((Fintype.card V : ℝ) / (E.size : ℝ)) ≤ (S.card : ℝ) ∧
      c ∈ E.commonApprovals S ∧ ∀ v ∈ S, (E.approvals v ∩ W).card < ℓ

theorem ApprovalElection.SatisfiesAlphaJR.mono {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] {E : ApprovalElection V C} {α β : ℝ} {W : Finset C}
    (h : E.SatisfiesAlphaJR α W) (hαβ : α ≤ β) : E.SatisfiesAlphaJR β W := by
  intro S hcoh
  apply h S
  refine ⟨hcoh.1, hcoh.2.1, le_trans ?_ hcoh.2.2.1, hcoh.2.2.2⟩
  have hnn : 0 ≤ ((1 : ℕ) : ℝ) * ((Fintype.card V : ℝ) / (E.size : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_right hαβ hnn
  linarith

theorem ApprovalElection.SatisfiesAlphaEJR.mono {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] {E : ApprovalElection V C} {α β : ℝ} {W : Finset C}
    (h : E.SatisfiesAlphaEJR α W) (hαβ : α ≤ β) : E.SatisfiesAlphaEJR β W := by
  intro ℓ S hcoh
  apply h ℓ S
  refine ⟨hcoh.1, hcoh.2.1, le_trans ?_ hcoh.2.2.1, hcoh.2.2.2⟩
  have hnn : 0 ≤ (ℓ : ℝ) * ((Fintype.card V : ℝ) / (E.size : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_right hαβ hnn
  linarith

theorem ApprovalElection.SatisfiesAlphaEJRPlus.mono {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] {E : ApprovalElection V C} {α β : ℝ} {W : Finset C}
    (h : E.SatisfiesAlphaEJRPlus α W) (hαβ : α ≤ β) : E.SatisfiesAlphaEJRPlus β W := by
  rintro ⟨c, S, ℓ, hcW, hℓ1, hℓk, hScard, hcS, hSlt⟩
  apply h
  refine ⟨c, S, ℓ, hcW, hℓ1, hℓk, le_trans ?_ hScard, hcS, hSlt⟩
  have hnn : 0 ≤ (ℓ : ℝ) * ((Fintype.card V : ℝ) / (E.size : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_right hαβ hnn
  linarith

theorem ApprovalElection.not_satisfiesAlphaJR_zero {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : ApprovalElection V C) (W : Finset C) :
    ¬E.SatisfiesAlphaJR 0 W := by
  intro h
  have hcoh : E.IsAlphaCohesive 0 1 ∅ := by
    refine ⟨le_rfl, E.size_pos, by simp, ?_⟩
    have hEq : E.commonApprovals ∅ = Finset.univ := by ext c; simp [commonApprovals]
    rw [hEq, Finset.card_univ]
    exact le_trans E.size_pos E.size_le
  obtain ⟨v, hv, _⟩ := h ∅ hcoh
  exact Finset.notMem_empty v hv

theorem ApprovalElection.not_satisfiesAlphaEJR_zero {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : ApprovalElection V C) (W : Finset C) :
    ¬E.SatisfiesAlphaEJR 0 W := by
  intro h
  exact E.not_satisfiesAlphaJR_zero W fun S hcoh ↦ h 1 S hcoh

theorem ApprovalElection.not_satisfiesAlphaEJRPlus_zero_of_lt {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : ApprovalElection V C) {W : Finset C} (hlt : W.card < Fintype.card C) :
    ¬E.SatisfiesAlphaEJRPlus 0 W := by
  intro h
  obtain ⟨c, _, hcW⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  apply h
  refine ⟨c, ∅, 1, hcW, le_rfl, E.size_pos, by simp, ?_, fun v hv ↦ (Finset.notMem_empty v hv).elim⟩
  simp [commonApprovals]

theorem ApprovalElection.satisfiesAlphaEJRPlus_univ {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq C] (E : ApprovalElection V C) (α : ℝ) :
    E.SatisfiesAlphaEJRPlus α Finset.univ := by
  rintro ⟨c, _, _, hcW, _⟩
  exact hcW (Finset.mem_univ c)

/-! ### Matrix encodings and decision problems -/

/-- Matrix-encoded approval-election instance: unary candidate count `m`, list of `n` voter
approval bit-vectors of length `m`, and binary committee size `k`. -/
@[ext]
structure EncodedElection where
  /-- Number of candidates `m`. -/
  numCandidates : ℕ
  /-- Approval bit-vectors for the `n` voters. -/
  ballots : List (List Bool)
  /-- Target committee size `k`. -/
  k : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Structure encoding of `EncodedElection`: unary `numCandidates`, framed list of `encBits`
ballots, and binary `k`. -/
enc_structure encEncodedElection : EncodedElection where
  numCandidates : encUnary,
  ballots : (encList encBits),
  k : encNat

/-- Well-formedness of an `EncodedElection`. -/
def EncodedElection.WellFormed (x : EncodedElection) : Prop :=
  0 < x.ballots.length ∧ 0 < x.k ∧ x.k ≤ x.numCandidates ∧
    ∀ b ∈ x.ballots, b.length = x.numCandidates

/-- Computable well-formedness check for `EncodedElection`. -/
def EncodedElection.wellFormedBool (x : EncodedElection) : Bool :=
  decide (0 < x.ballots.length) && decide (0 < x.k) && decide (x.k ≤ x.numCandidates) &&
    x.ballots.all (fun b ↦ decide (b.length = x.numCandidates))

theorem EncodedElection.wellFormedBool_eq_true_iff (x : EncodedElection) :
    x.wellFormedBool = true ↔ x.WellFormed := by
  simp [wellFormedBool, WellFormed, Bool.and_eq_true, List.all_eq_true, and_assoc]

/-- Interpret a well-formed `EncodedElection` as an `ApprovalElection`. -/
def EncodedElection.toElection (x : EncodedElection) (hx : x.WellFormed) :
    ApprovalElection (Fin x.ballots.length) (Fin x.numCandidates) where
  approvals v := Finset.univ.filter fun c ↦ (x.ballots.getD v.val []).getD c.val false = true
  size := x.k
  voters_nonempty := ⟨⟨0, hx.1⟩⟩
  size_pos := hx.2.1
  size_le := by simpa using hx.2.2.1

/-- Matrix-encoded `(I, W)` pair for committee-verification problems. -/
@[ext]
structure EncodedElectionCommittee where
  /-- The underlying approval election instance `I`. -/
  election : EncodedElection
  /-- Candidate bit-mask of length `m` specifying `W ⊆ C`. -/
  committee : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- Structure encoding of `EncodedElectionCommittee`: framed `encEncodedElection` followed by
`encBits` committee mask. -/
enc_structure encEncodedElectionCommittee : EncodedElectionCommittee where
  election : encEncodedElection,
  committee : encBits

/-- Well-formedness of an `(I, W)` pair. -/
def EncodedElectionCommittee.WellFormed (x : EncodedElectionCommittee) : Prop :=
  x.election.WellFormed ∧ x.committee.length = x.election.numCandidates ∧
    x.committee.count true = x.election.k

/-- Computable well-formedness check for `EncodedElectionCommittee`. -/
def EncodedElectionCommittee.wellFormedBool (x : EncodedElectionCommittee) : Bool :=
  x.election.wellFormedBool && decide (x.committee.length = x.election.numCandidates) &&
    decide (x.committee.count true = x.election.k)

theorem EncodedElectionCommittee.wellFormedBool_eq_true_iff (x : EncodedElectionCommittee) :
    x.wellFormedBool = true ↔ x.WellFormed := by
  simp [wellFormedBool, WellFormed, EncodedElection.wellFormedBool_eq_true_iff,
    Bool.and_eq_true, and_assoc]

/-- Interpret `x.committee` as a `Finset (Fin x.election.numCandidates)`. -/
def EncodedElectionCommittee.toCommittee (x : EncodedElectionCommittee) :
    Finset (Fin x.election.numCandidates) :=
  Finset.univ.filter fun c ↦ x.committee.getD c.val false = true

theorem EncodedElectionCommittee.card_toCommittee (x : EncodedElectionCommittee)
    (hx : x.WellFormed) : x.toCommittee.card = x.election.k := by
  have h1 : ∀ (l : List Bool) (n : ℕ), l.length = n →
      (Finset.univ.filter (fun c : Fin n ↦ l.getD c.val false = true)).card =
        l.count true := by
    intro l
    induction l with
    | nil => rintro _ rfl; simp
    | cons b bs ih =>
      rintro _ rfl
      rw [List.count_cons, Finset.card_filter]
      change (∑ i : Fin (bs.length + 1), if (b :: bs).getD i.val false = true then 1 else 0) = _
      rw [Fin.sum_univ_succ, ← Finset.card_filter]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ,
        ih bs.length rfl]
      cases b <;> simp [Nat.add_comm]
  rw [toCommittee, h1 x.committee x.election.numCandidates hx.2.1, hx.2.2]

/-- Decision problem: given `I`, does there exist a size-`k` committee satisfying `α`-JR? -/
def AlphaJRProblem (α : ℚ) : Set EncodedElection :=
  {x | ∃ hx : x.WellFormed, ∃ W : Finset (Fin x.numCandidates),
    W.card = x.k ∧ (x.toElection hx).SatisfiesAlphaJR (α : ℝ) W}

/-- Decision problem: given `I`, does there exist a size-`k` committee satisfying `α`-EJR? -/
def AlphaEJRProblem (α : ℚ) : Set EncodedElection :=
  {x | ∃ hx : x.WellFormed, ∃ W : Finset (Fin x.numCandidates),
    W.card = x.k ∧ (x.toElection hx).SatisfiesAlphaEJR (α : ℝ) W}

/-- Decision problem: given `I`, does there exist a size-`k` committee satisfying `α`-EJR+? -/
def AlphaEJRPlusProblem (α : ℚ) : Set EncodedElection :=
  {x | ∃ hx : x.WellFormed, ∃ W : Finset (Fin x.numCandidates),
    W.card = x.k ∧ (x.toElection hx).SatisfiesAlphaEJRPlus (α : ℝ) W}

/-- Decision problem: given `(I, W)`, does `W` satisfy `α`-JR? -/
def AlphaJRVerify (α : ℚ) : Set EncodedElectionCommittee :=
  {x | ∃ hx : x.WellFormed, (x.election.toElection hx.1).SatisfiesAlphaJR (α : ℝ) x.toCommittee}

/-- Decision problem: given `(I, W)`, does `W` satisfy `α`-EJR? -/
def AlphaEJRVerify (α : ℚ) : Set EncodedElectionCommittee :=
  {x | ∃ hx : x.WellFormed, (x.election.toElection hx.1).SatisfiesAlphaEJR (α : ℝ) x.toCommittee}

/-- Decision problem: given `(I, W)`, does `W` satisfy `α`-EJR+? -/
def AlphaEJRPlusVerify (α : ℚ) : Set EncodedElectionCommittee :=
  {x | ∃ hx : x.WellFormed,
    (x.election.toElection hx.1).SatisfiesAlphaEJRPlus (α : ℝ) x.toCommittee}

/-! ### Private list/Finset and polynomial-time helpers -/

private theorem card_filter_fin_eq_countP_range (n : ℕ) (p : ℕ → Bool) :
    (Finset.univ.filter (fun i : Fin n ↦ p i.val = true)).card = (List.range n).countP p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton, ← ih,
      Finset.card_filter, Fin.sum_univ_castSucc, ← Finset.card_filter]
    simp only [Fin.val_castSucc, Fin.val_last]

private theorem card_filter_fin_eq_countP_range_iff {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (q : ℕ → Bool) (hq : ∀ v : Fin n, P v ↔ q v.val = true) :
    (Finset.univ.filter P).card = (List.range n).countP q := by
  rw [← card_filter_fin_eq_countP_range]
  congr 1; ext v; simp [hq v]

private theorem list_countP_eq_range {α : Type*} (l : List α) (d : α) (q : α → Bool) :
    l.countP q = (List.range l.length).countP (fun i ↦ q (l.getD i d)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_cons,
      List.countP_map]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    rw [ih]

private theorem foldl_max_mem_or_init {α : Type*} [LinearOrder α] (l : List α) (init : α) :
    l.foldl max init = init ∨ l.foldl max init ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    rcases ih (max init a) with h | h
    · rw [h]
      rcases max_choice init a with hm | hm
      · exact Or.inl hm
      · exact Or.inr (by rw [hm]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem a h)

private theorem foldl_max_ge_init {α : Type*} [LinearOrder α] (l : List α) (init : α) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left init a) (ih (max init a))

private theorem foldl_max_le_iff {α : Type*} [LinearOrder α] (l : List α) (init b : α) :
    l.foldl max init ≤ b ↔ init ≤ b ∧ ∀ x ∈ l, x ≤ b := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem le_foldl_max_of_mem {α : Type*} [LinearOrder α] {l : List α} {init a : α}
    (ha : a ∈ l) : a ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => cases ha
  | cons x t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ht
    · exact le_trans (le_max_right init a) (foldl_max_ge_init t (max init a))
    · exact ih ht

private theorem card_inter_toCommittee_eq (x : EncodedElectionCommittee) (hx : x.WellFormed)
    (v : Fin x.election.ballots.length) :
    ((x.election.toElection hx.1).approvals v ∩ x.toCommittee).card =
      (List.range x.election.numCandidates).countP
        (fun c ↦ (x.election.ballots.getD v.val []).getD c false &&
          x.committee.getD c false) := by
  rw [← card_filter_fin_eq_countP_range]
  congr 1; ext c
  simp [EncodedElection.toElection, EncodedElectionCommittee.toCommittee, Bool.and_eq_true]

theorem computableInPolyTime_wellFormedElection :
    ComputableInPolyTime EncodedElection.wellFormedBool encEncodedElection encBool := by
  have heq : EncodedElection.wellFormedBool = fun x ↦
      decide (0 < x.ballots.length) && decide (0 < x.k) && decide (x.k ≤ x.numCandidates) &&
        x.ballots.all (fun b ↦ decide (b.length = x.numCandidates)) := rfl
  rw [heq]
  have hk_bin : ComputableInPolyTime (fun x : EncodedElection ↦ x.k)
      encEncodedElection encNat := by fun_prop
  have hm_bin : ComputableInPolyTime (fun x : EncodedElection ↦ x.numCandidates)
      encEncodedElection encNat := unary_to_binary.comp (by fun_prop)
  have h1 : ComputableInPolyTime (fun x : EncodedElection ↦ decide (0 < x.ballots.length))
      encEncodedElection encBool := by fun_prop
  have h2 : ComputableInPolyTime (fun x : EncodedElection ↦ decide (0 < x.k))
      encEncodedElection encBool := binary_lt' (const 0) hk_bin
  have h3 : ComputableInPolyTime (fun x : EncodedElection ↦ decide (x.k ≤ x.numCandidates))
      encEncodedElection encBool := binary_le' hk_bin hm_bin
  have h4 : ComputableInPolyTime
      (fun x : EncodedElection ↦ x.ballots.all (fun b ↦ decide (b.length = x.numCandidates)))
      encEncodedElection encBool := by
    refine allWith (encP := encUnary) (encA := encBits)
      (test := fun p : ℕ × List Bool ↦ decide (p.2.length = p.1)) ?_ (by fun_prop) (by fun_prop)
    exact decide_eq' (length_bits.comp (snd _ _)) (fst _ _)
  exact bool_and' (bool_and' (bool_and' h1 h2) h3) h4

theorem computableInPolyTime_wellFormedCommittee :
    ComputableInPolyTime EncodedElectionCommittee.wellFormedBool
      encEncodedElectionCommittee encBool := by
  have heq : EncodedElectionCommittee.wellFormedBool = fun x ↦
      x.election.wellFormedBool && decide (x.committee.length = x.election.numCandidates) &&
        decide (x.committee.count true = x.election.k) := rfl
  rw [heq]
  have h1 : ComputableInPolyTime (fun x : EncodedElectionCommittee ↦ x.election.wellFormedBool)
      encEncodedElectionCommittee encBool :=
    computableInPolyTime_wellFormedElection.comp (by fun_prop)
  have h2 : ComputableInPolyTime
      (fun x : EncodedElectionCommittee ↦ decide (x.committee.length = x.election.numCandidates))
      encEncodedElectionCommittee encBool := by fun_prop
  have h3 : ComputableInPolyTime
      (fun x : EncodedElectionCommittee ↦ decide (x.committee.count true = x.election.k))
      encEncodedElectionCommittee encBool := by
    have hcnt : ComputableInPolyTime (fun x : EncodedElectionCommittee ↦ x.committee.count true)
        encEncodedElectionCommittee encUnary := by
      have hcp := countPWith (encA := encBool) (encL := encBits) (encP := encBool)
        (test := fun p : Bool × Bool ↦ p.2 == p.1) (by fun_prop) (const true)
        (encEncodedElectionCommittee_committee_polyTime id')
      exact hcp.of_enc_eq fun x ↦ by simp [List.count_eq_countP]
    exact decide_eq' (unary_to_binary.comp hcnt) (by fun_prop)
  exact bool_and' (bool_and' h1 h2) h3

/-! ### Polynomial-time verification of `α`-JR and `α`-EJR+ -/

/-- Executable `O(nm)` computation of the maximum uncovered support `s_max` for `α`-JR. -/
def computeMaxUncoveredJR (x : EncodedElectionCommittee) : ℕ :=
  let m := x.election.numCandidates
  let uncovered : List (List Bool) :=
    x.election.ballots.filter fun b ↦
      !(List.range m).any fun c ↦ b.getD c false && x.committee.getD c false
  ((List.range m).map fun c ↦
    if x.committee.getD c false then 0
    else uncovered.countP fun b ↦ b.getD c false).foldl max 0

/-- Executable polynomial-time computation of `α_JR^W(I)`. -/
def computeAlphaJR (x : EncodedElectionCommittee) : ℚ :=
  let k := min x.election.numCandidates x.election.k
  (computeMaxUncoveredJR x : ℚ) * ((k : ℚ) / (x.election.ballots.length : ℚ))

theorem computableInPolyTime_computeMaxUncoveredJR :
    ComputableInPolyTime computeMaxUncoveredJR encEncodedElectionCommittee encUnary := by
  have hM := encEncodedElection_numCandidates_polyTime
    (encEncodedElectionCommittee_election_polyTime id')
  have hB := encEncodedElection_ballots_polyTime (encEncodedElectionCommittee_election_polyTime id')
  have hW := encEncodedElectionCommittee_committee_polyTime id'
  have hunc : ComputableInPolyTime
      (fun x : EncodedElectionCommittee ↦
        x.election.ballots.filter fun b ↦
          !(List.range x.election.numCandidates).any
            fun c ↦ b.getD c false && x.committee.getD c false)
      encEncodedElectionCommittee (encList encBits) := by
    refine filterWithInput hB ?_
    refine bool_not.comp (anyWithInput (range.comp (hM.comp (fst _ _))) ?_)
    exact bool_and' (bitsGetDWithInput ((snd _ _).comp (fst _ _)) (snd _ _) false)
      (bitsGetDWithInput (hW.comp ((fst _ _).comp (fst _ _))) (snd _ _) false)
  have hlist : ComputableInPolyTime
      (fun x : EncodedElectionCommittee ↦
        (List.range x.election.numCandidates).map fun c ↦
          if x.committee.getD c false then 0
          else (x.election.ballots.filter fun b ↦
            !(List.range x.election.numCandidates).any
              fun j ↦ b.getD j false && x.committee.getD j false).countP
            fun b ↦ b.getD c false)
      encEncodedElectionCommittee (encList encUnary) := by
    refine mapWithInput (range.comp hM) ?_
    refine ite' (bitsGetDWithInput (hW.comp (fst _ _)) (snd _ _) false) (const 0) ?_
    refine countPWithInput (hunc.comp (fst _ _)) ?_
    exact bitsGetDWithInput (snd _ _) ((snd _ _).comp (fst _ _)) false
  exact foldl' (encA := encUnary) (encB := encUnary) (encL := encList encUnary)
    (step := max) hlist (const 0) unary_max (B := fun x ↦ x.election.ballots.length)
    ((length_list encBits).comp hB).polyBounded fun x i _ ↦ by
      simp only [encUnary_apply, List.length_replicate]
      rw [foldl_max_le_iff]
      refine ⟨Nat.zero_le _, fun s hs ↦ ?_⟩
      rcases List.mem_map.mp (List.mem_of_mem_take hs) with ⟨_, _, rfl⟩
      split_ifs
      · exact Nat.zero_le _
      · exact List.countP_le_length.trans (List.length_filter_le _ _)

theorem computableInPolyTime_computeAlphaJR :
    ComputableInPolyTime computeAlphaJR encEncodedElectionCommittee encRat := by
  unfold computeAlphaJR
  have hmax : ComputableInPolyTime (fun x ↦ (computeMaxUncoveredJR x : ℚ))
      encEncodedElectionCommittee encRat :=
    rat_natCast.comp (unary_to_binary.comp computableInPolyTime_computeMaxUncoveredJR)
  have hk : ComputableInPolyTime (fun x : EncodedElectionCommittee ↦
      ((min x.election.numCandidates x.election.k : ℕ) : ℚ))
      encEncodedElectionCommittee encRat :=
    rat_natCast.comp (unary_to_binary.comp (binary_min_unary' (by fun_prop) (by fun_prop)))
  have hn : ComputableInPolyTime (fun x : EncodedElectionCommittee ↦
      (x.election.ballots.length : ℚ)) encEncodedElectionCommittee encRat :=
    rat_natCast.comp (unary_to_binary.comp (by fun_prop))
  exact rat_mul' hmax (rat_div' hk hn)

private theorem satisfiesAlphaJR_iff_computeAlphaJR_lt (x : EncodedElectionCommittee)
    (hx : x.WellFormed) {α : ℚ} (hα : 0 < α) :
    (x.election.toElection hx.1).SatisfiesAlphaJR (α : ℝ) x.toCommittee ↔ computeAlphaJR x < α := by
  let E := x.election.toElection hx.1
  let W := x.toCommittee
  have hk : min x.election.numCandidates x.election.k = x.election.k := Nat.min_eq_right hx.1.2.2.1
  have hn_pos : (0 : ℝ) < (x.election.ballots.length : ℝ) := Nat.cast_pos.mpr hx.1.1
  have hk_pos : (0 : ℝ) < (x.election.k : ℝ) := Nat.cast_pos.mpr hx.1.2.1
  have hkn : (0 : ℝ) < (x.election.k : ℝ) / (x.election.ballots.length : ℝ) := div_pos hk_pos hn_pos
  have hcnt_eq : ∀ c : Fin x.election.numCandidates,
      (x.election.ballots.filter fun b ↦
        !(List.range x.election.numCandidates).any
          fun j ↦ b.getD j false && x.committee.getD j false).countP
        (fun b ↦ b.getD c.val false) =
      (Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        E.approvals v ∩ W = ∅ ∧ c ∈ E.approvals v).card := by
    intro c
    rw [List.countP_filter, list_countP_eq_range _ []]
    symm
    refine card_filter_fin_eq_countP_range_iff _ _ fun v ↦ ?_
    have hcov : (!(List.range x.election.numCandidates).any
        fun j ↦ (x.election.ballots.getD v.val []).getD j false && x.committee.getD j false) =
        decide (E.approvals v ∩ W = ∅) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq, not_and, Finset.eq_empty_iff_forall_notMem]
      constructor
      · intro h j hj
        rcases Finset.mem_inter.mp hj with ⟨hA, hW⟩
        exact h j.val j.isLt (by simpa [E, EncodedElection.toElection] using hA)
          (by simpa [W, EncodedElectionCommittee.toCommittee] using hW)
      · intro h j hj hA hW
        exact h ⟨j, hj⟩ (Finset.mem_inter.mpr
          ⟨by simpa [E, EncodedElection.toElection] using hA,
            by simpa [W, EncodedElectionCommittee.toCommittee] using hW⟩)
    simp only [Bool.and_eq_true, hcov, decide_eq_true_eq]
    have hmemA : c ∈ E.approvals v ↔ (x.election.ballots.getD v.val []).getD c.val false = true :=
      by simp [E, EncodedElection.toElection]
    rw [hmemA]; tauto
  have hval : (computeAlphaJR x : ℝ) =
      (computeMaxUncoveredJR x : ℝ) * ((x.election.k : ℝ) / (x.election.ballots.length : ℝ)) := by
    unfold computeAlphaJR; rw [hk]; push_cast; rfl
  rw [show computeAlphaJR x < α ↔ (computeAlphaJR x : ℝ) < (α : ℝ) by exact_mod_cast Iff.rfl, hval]
  constructor
  · intro hsat
    have hlt_all : ∀ c : Fin x.election.numCandidates, c ∉ W →
        ((Finset.univ.filter fun v : Fin x.election.ballots.length ↦
          E.approvals v ∩ W = ∅ ∧ c ∈ E.approvals v).card : ℝ) <
          (α : ℝ) * ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) := by
      intro c hcW
      by_contra hge; push Not at hge
      let S := Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        E.approvals v ∩ W = ∅ ∧ c ∈ E.approvals v
      have hcoh : E.IsAlphaCohesive (α : ℝ) 1 S := by
        refine ⟨le_rfl, hx.1.2.1, ?_, ?_⟩
        · have hEs : E.size = x.election.k := rfl
          rw [hEs, Fintype.card_fin, Nat.cast_one, mul_one]; exact hge
        · refine Finset.card_pos.mpr ⟨c, ?_⟩
          rw [E.mem_commonApprovals_iff]
          exact fun v hv ↦ (Finset.mem_filter.mp hv).2.2
      obtain ⟨v, hv, hcov⟩ := hsat S hcoh
      rw [(Finset.mem_filter.mp hv).2.1, Finset.card_empty] at hcov; omega
    have hmax_lt : (computeMaxUncoveredJR x : ℝ) <
        (α : ℝ) * ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) := by
      rcases foldl_max_mem_or_init _ 0 with h0 | hm
      · change computeMaxUncoveredJR x = 0 at h0
        rw [h0, Nat.cast_zero]
        exact mul_pos (by exact_mod_cast hα) (div_pos hn_pos hk_pos)
      · rcases List.mem_map.mp hm with ⟨c, hc, hEq⟩
        have hcm : c < x.election.numCandidates := List.mem_range.mp hc
        change _ = computeMaxUncoveredJR x at hEq
        rw [← hEq]
        split_ifs with hcw
        · rw [Nat.cast_zero]; exact mul_pos (by exact_mod_cast hα) (div_pos hn_pos hk_pos)
        · rw [hcnt_eq ⟨c, hcm⟩]
          exact hlt_all ⟨c, hcm⟩ (fun h' ↦ hcw (Finset.mem_filter.mp h').2)
    have := mul_lt_mul_of_pos_right hmax_lt hkn
    have hcancel : (α : ℝ) * ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) *
        ((x.election.k : ℝ) / (x.election.ballots.length : ℝ)) = (α : ℝ) := by
      have hn0 : (x.election.ballots.length : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hk0 : (x.election.k : ℝ) ≠ 0 := ne_of_gt hk_pos
      field_simp [hn0, hk0]
    linarith
  · intro hlt S hcoh
    by_contra hno; push Not at hno
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcoh.2.2.2)
    have hS_sub : S ⊆ Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        E.approvals v ∩ W = ∅ ∧ c ∈ E.approvals v := fun v hv ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.card_eq_zero.mp (Nat.lt_one_iff.mp (hno v hv)),
        (E.mem_commonApprovals_iff.mp hc) v hv⟩
    by_cases hcW : c ∈ W
    · have hαpos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
      have hSne : S.Nonempty := Finset.card_pos.mp (by
        have hpos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le
          (by simpa [E, EncodedElection.toElection, Fintype.card_fin] using
            mul_pos (mul_pos hαpos (by norm_num : (0 : ℝ) < 1)) (div_pos hn_pos hk_pos))
          hcoh.2.2.1
        exact_mod_cast hpos)
      obtain ⟨v, hv⟩ := hSne
      have h1 : c ∈ E.approvals v ∩ W := Finset.mem_inter.mpr
        ⟨(E.mem_commonApprovals_iff.mp hc) v hv, hcW⟩
      have hcard := Finset.card_pos.mpr ⟨c, h1⟩
      have hlt_v := hno v hv
      dsimp only [E, W] at hcard; omega
    · have hcw : x.committee.getD c.val false = false := by
        cases h : x.committee.getD c.val false
        · rfl
        · exact (hcW (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).elim
      have hmem : (x.election.ballots.filter fun b ↦
          !(List.range x.election.numCandidates).any
            fun j ↦ b.getD j false && x.committee.getD j false).countP
          (fun b ↦ b.getD c.val false) ∈
          (List.range x.election.numCandidates).map fun j ↦
            if x.committee.getD j false then 0
            else (x.election.ballots.filter fun b ↦
              !(List.range x.election.numCandidates).any
                fun i ↦ b.getD i false && x.committee.getD i false).countP
              fun b ↦ b.getD j false := by
        refine List.mem_map.mpr ⟨c.val, List.mem_range.mpr c.isLt, ?_⟩
        rw [hcw]; rfl
      have hle_max : S.card ≤ computeMaxUncoveredJR x := by
        have h1 := le_foldl_max_of_mem (init := 0) hmem
        rw [hcnt_eq c] at h1
        exact (Finset.card_le_card hS_sub).trans h1
      have hle_r : (S.card : ℝ) ≤ (computeMaxUncoveredJR x : ℝ) := by exact_mod_cast hle_max
      have hmul := mul_le_mul_of_nonneg_right (le_trans hcoh.2.2.1 hle_r) (le_of_lt hkn)
      have hcancel : (α : ℝ) * (1 : ℝ) *
          ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) *
          ((x.election.k : ℝ) / (x.election.ballots.length : ℝ)) = (α : ℝ) := by
        have hn0 : (x.election.ballots.length : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hk0 : (x.election.k : ℝ) ≠ 0 := ne_of_gt hk_pos
        field_simp [hn0, hk0]
      rw [Nat.cast_one] at hmul
      simp only [EncodedElection.toElection, Fintype.card_fin] at hmul
      linarith

/-- For every rational `α`, `AlphaJRVerify α ∈ P`. -/
theorem alphaJRVerify_mem_P (α : ℚ) :
    AlphaJRVerify α ∈ P encEncodedElectionCommittee := by
  by_cases hα : 0 < α
  · refine ⟨fun x ↦ x.wellFormedBool && decide (computeAlphaJR x < α), ?_, fun x ↦ ?_⟩
    · exact bool_and' computableInPolyTime_wellFormedCommittee
        (rat_lt' computableInPolyTime_computeAlphaJR (const α))
    · simp only [AlphaJRVerify, Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq,
        EncodedElectionCommittee.wellFormedBool_eq_true_iff]
      exact ⟨fun ⟨hx, hs⟩ ↦ ⟨hx, (satisfiesAlphaJR_iff_computeAlphaJR_lt x hx hα).mp hs⟩,
        fun ⟨hx, hlt⟩ ↦ ⟨hx, (satisfiesAlphaJR_iff_computeAlphaJR_lt x hx hα).mpr hlt⟩⟩
  · refine ⟨fun _ ↦ false, const false, fun x ↦ ?_⟩
    simp only [AlphaJRVerify, Set.mem_ofPred_eq, Bool.false_eq_true, iff_false, not_exists]
    intro hx hsat
    exact (x.election.toElection hx.1).not_satisfiesAlphaJR_zero x.toCommittee
      (hsat.mono (by exact_mod_cast not_lt.mp hα))

/-- Executable `O(mnk)` computation of `α_EJR+^W(I)`. -/
def computeAlphaEJRPlus (x : EncodedElectionCommittee) : ℚ :=
  let m := x.election.numCandidates
  let n := x.election.ballots.length
  let k := min m x.election.k
  let voterSats : List (List Bool × ℕ) :=
    x.election.ballots.map fun b ↦
      (b, (List.range m).countP fun j ↦ b.getD j false && x.committee.getD j false)
  let vals : List ℚ :=
    (List.range m).flatMap fun c ↦
      if x.committee.getD c false then []
      else (List.range k).map fun j ↦
        let ℓ : ℕ := j + 1
        let cnt := voterSats.countP fun p ↦ p.1.getD c false && decide (p.2 < ℓ)
        (cnt : ℚ) * ((k : ℚ) / ((ℓ : ℚ) * (n : ℚ)))
  vals.foldl max 0

theorem computableInPolyTime_computeAlphaEJRPlus :
    ComputableInPolyTime computeAlphaEJRPlus encEncodedElectionCommittee encRat := by
  have hM := encEncodedElection_numCandidates_polyTime
    (encEncodedElectionCommittee_election_polyTime id')
  have hB := encEncodedElection_ballots_polyTime (encEncodedElectionCommittee_election_polyTime id')
  have hW := encEncodedElectionCommittee_committee_polyTime id'
  have hK := encEncodedElection_k_polyTime (encEncodedElectionCommittee_election_polyTime id')
  have hpair_enc : ComputableInPolyTime
      (fun x : EncodedElectionCommittee ↦
        x.election.ballots.map fun b ↦
          (b, (List.range x.election.numCandidates).countP
            fun j ↦ b.getD j false && x.committee.getD j false))
      encEncodedElectionCommittee (encList (encPair encBits encUnary)) := by
    refine mapWithInput hB ?_
    refine ComputableInPolyTime.pair (enc₁ := encBits) (enc₂ := encUnary) (snd _ _) ?_
    refine countPWithInput (range.comp (hM.comp (fst _ _))) ?_
    exact bool_and' (bitsGetDWithInput ((snd _ _).comp (fst _ _)) (snd _ _) false)
      (bitsGetDWithInput (hW.comp ((fst _ _).comp (fst _ _))) (snd _ _) false)
  have hk_u := binary_min_unary' hM hK
  have hvals : ComputableInPolyTime
      (fun x : EncodedElectionCommittee ↦
        (List.range x.election.numCandidates).flatMap fun c ↦
          if x.committee.getD c false then []
          else (List.range (min x.election.numCandidates x.election.k)).map fun j ↦
            let ℓ : ℕ := j + 1
            let cnt := (x.election.ballots.map fun b ↦
              (b, (List.range x.election.numCandidates).countP
                fun i ↦ b.getD i false && x.committee.getD i false)).countP
              fun p ↦ p.1.getD c false && decide (p.2 < ℓ)
            (cnt : ℚ) * (((min x.election.numCandidates x.election.k : ℕ) : ℚ) /
              ((ℓ : ℚ) * (x.election.ballots.length : ℚ))))
      encEncodedElectionCommittee (encList encRat) := by
    refine flatMapWithInput (range.comp hM) ?_
    refine ite' (bitsGetDWithInput (hW.comp (fst _ _)) (snd _ _) false) (const []) ?_
    refine mapWithInput (range.comp (hk_u.comp (fst _ _))) ?_
    have hcnt : ComputableInPolyTime
        (fun p : (EncodedElectionCommittee × ℕ) × ℕ ↦
          ((p.1.1.election.ballots.map fun b ↦
            (b, (List.range p.1.1.election.numCandidates).countP
              fun i ↦ b.getD i false && p.1.1.committee.getD i false)).countP
            (fun q ↦ q.1.getD p.1.2 false && decide (q.2 < p.2 + 1)) : ℚ))
        (encPair (encPair encEncodedElectionCommittee encUnary) encUnary) encRat := by
      refine rat_natCast.comp (unary_to_binary.comp ?_)
      refine countPWithInput (hpair_enc.comp ((fst _ _).comp (fst _ _))) ?_
      exact bool_and'
        (bitsGetDWithInput ((fst _ _).comp (snd _ _)) ((snd _ _).comp ((fst _ _).comp (fst _ _)))
          false)
        (unary_lt' ((snd _ _).comp (snd _ _)) (unary_add' ((snd _ _).comp (fst _ _)) (const 1)))
    have hk_q : ComputableInPolyTime
        (fun p : (EncodedElectionCommittee × ℕ) × ℕ ↦
          ((min p.1.1.election.numCandidates p.1.1.election.k : ℕ) : ℚ))
        (encPair (encPair encEncodedElectionCommittee encUnary) encUnary) encRat :=
      rat_natCast.comp (unary_to_binary.comp (hk_u.comp ((fst _ _).comp (fst _ _))))
    have hℓ_q : ComputableInPolyTime
        (fun p : (EncodedElectionCommittee × ℕ) × ℕ ↦ ((p.2 + 1 : ℕ) : ℚ))
        (encPair (encPair encEncodedElectionCommittee encUnary) encUnary) encRat :=
      rat_natCast.comp (unary_to_binary.comp (unary_add' (snd _ _) (const 1)))
    have hn_q : ComputableInPolyTime
        (fun p : (EncodedElectionCommittee × ℕ) × ℕ ↦ (p.1.1.election.ballots.length : ℚ))
        (encPair (encPair encEncodedElectionCommittee encUnary) encUnary) encRat :=
      rat_natCast.comp (unary_to_binary.comp
        (((length_list encBits).comp hB).comp ((fst _ _).comp (fst _ _))))
    exact rat_mul' hcnt (rat_div' hk_q (rat_mul' hℓ_q hn_q))
  have hstep : ComputableInPolyTime (fun p : ℚ × ℚ ↦ max p.1 p.2) (encPair encRat encRat) encRat :=
    (ite' (rat_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _)).of_enc_eq fun p ↦ by
      congr 1; simp [max_def]
  exact foldl' (encA := encRat) (encB := encRat) (encL := encList encRat)
    (step := max) hvals (const 0) hstep
    (B := fun x ↦ (encRat 0).length + (encList encRat
      ((List.range x.election.numCandidates).flatMap fun c ↦
        if x.committee.getD c false then []
        else (List.range (min x.election.numCandidates x.election.k)).map fun j ↦
          let ℓ : ℕ := j + 1
          let cnt := (x.election.ballots.map fun b ↦
            (b, (List.range x.election.numCandidates).countP
              fun i ↦ b.getD i false && x.committee.getD i false)).countP
            fun p ↦ p.1.getD c false && decide (p.2 < ℓ)
          (cnt : ℚ) * (((min x.election.numCandidates x.election.k : ℕ) : ℚ) /
            ((ℓ : ℚ) * (x.election.ballots.length : ℚ))))).length)
    (PolyBounded.add (.const _) hvals.polyBounded_length) fun x i _ ↦ by
      rcases foldl_max_mem_or_init _ (0 : ℚ) with h0 | hmem
      · rw [h0]; omega
      · have hlen := length_le_encList_of_mem encRat (List.mem_of_mem_take hmem); omega

private theorem satisfiesAlphaEJRPlus_iff_computeAlphaEJRPlus_lt (x : EncodedElectionCommittee)
    (hx : x.WellFormed) {α : ℚ} (hα : 0 < α) :
    (x.election.toElection hx.1).SatisfiesAlphaEJRPlus (α : ℝ) x.toCommittee ↔
      computeAlphaEJRPlus x < α := by
  let E := x.election.toElection hx.1
  let W := x.toCommittee
  have hk : min x.election.numCandidates x.election.k = x.election.k := Nat.min_eq_right hx.1.2.2.1
  have hn_pos : (0 : ℝ) < (x.election.ballots.length : ℝ) := Nat.cast_pos.mpr hx.1.1
  have hk_pos : (0 : ℝ) < (x.election.k : ℝ) := Nat.cast_pos.mpr hx.1.2.1
  have hcnt_eq : ∀ (c : Fin x.election.numCandidates) (ℓ : ℕ),
      (x.election.ballots.map fun b ↦
        (b, (List.range x.election.numCandidates).countP
          fun j ↦ b.getD j false && x.committee.getD j false)).countP
        (fun p ↦ p.1.getD c.val false && decide (p.2 < ℓ)) =
      (Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ).card := by
    intro c ℓ
    rw [List.countP_map, list_countP_eq_range _ []]
    symm
    refine card_filter_fin_eq_countP_range_iff _ _ fun v ↦ ?_
    simp only [Function.comp_def, Bool.and_eq_true, decide_eq_true_eq]
    rw [card_inter_toCommittee_eq x hx v]
    simp [E, EncodedElection.toElection]
  rw [show computeAlphaEJRPlus x < α ↔ (computeAlphaEJRPlus x : ℝ) < (α : ℝ) by
    exact_mod_cast Iff.rfl]
  constructor
  · intro hsat
    have hlt_all : ∀ (c : Fin x.election.numCandidates) (ℓ : ℕ),
        c ∉ W → 1 ≤ ℓ → ℓ ≤ x.election.k →
        ((Finset.univ.filter fun v : Fin x.election.ballots.length ↦
          c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ).card : ℝ) *
          ((x.election.k : ℝ) / ((ℓ : ℝ) * (x.election.ballots.length : ℝ))) < (α : ℝ) := by
      intro c ℓ hcW hℓ1 hℓk
      have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ1
      have hden_pos : (0 : ℝ) < (ℓ : ℝ) * (x.election.ballots.length : ℝ) := mul_pos hℓ_pos hn_pos
      by_contra hge; push Not at hge
      apply hsat
      refine ⟨c, Finset.univ.filter (fun v ↦ c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ),
        ℓ, hcW, hℓ1, hℓk, ?_, ?_, fun v hv ↦ (Finset.mem_filter.mp hv).2.2⟩
      · have hmul := mul_le_mul_of_nonneg_right hge
          (le_of_lt (div_pos hden_pos hk_pos))
        have hcancel : ((Finset.univ.filter fun v : Fin x.election.ballots.length ↦
            c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ).card : ℝ) *
            ((x.election.k : ℝ) / ((ℓ : ℝ) * (x.election.ballots.length : ℝ))) *
            (((ℓ : ℝ) * (x.election.ballots.length : ℝ)) / (x.election.k : ℝ)) =
            ((Finset.univ.filter fun v : Fin x.election.ballots.length ↦
              c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ).card : ℝ) := by
          have hk0 : (x.election.k : ℝ) ≠ 0 := ne_of_gt hk_pos
          have hd0 : (ℓ : ℝ) * (x.election.ballots.length : ℝ) ≠ 0 := ne_of_gt hden_pos
          field_simp [hk0, hd0]
        have hcancel2 : (α : ℝ) * (((ℓ : ℝ) * (x.election.ballots.length : ℝ)) / (x.election.k : ℝ))
            = (α : ℝ) * (ℓ : ℝ) * ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) := by ring
        have hEs : E.size = x.election.k := rfl
        rw [hEs, Fintype.card_fin]
        linarith
      · rw [E.mem_commonApprovals_iff]
        exact fun v hv ↦ (Finset.mem_filter.mp hv).2.1
    unfold computeAlphaEJRPlus
    rcases foldl_max_mem_or_init _ (0 : ℚ) with h0 | hm
    · rw [h0, Rat.cast_zero]; exact_mod_cast hα
    · rcases List.mem_flatMap.mp hm with ⟨c, hc, hqc⟩
      have hcm : c < x.election.numCandidates := List.mem_range.mp hc
      split_ifs at hqc with hcw
      · cases hqc
      · rcases List.mem_map.mp hqc with ⟨j, hj, hEq⟩
        have hjlt : j < x.election.k := by rw [← hk]; exact List.mem_range.mp hj
        rw [← hEq]; dsimp only
        rw [hk, hcnt_eq ⟨c, hcm⟩ (j + 1)]
        have h := hlt_all ⟨c, hcm⟩ (j + 1)
          (fun h' ↦ hcw (Finset.mem_filter.mp h').2) (by omega) (by omega)
        push_cast; simpa [Nat.cast_add, Nat.cast_one] using h
  · rintro hlt ⟨c, S, ℓ, hcW, hℓ1, hℓk, hScard, hcS, hSlt⟩
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ1
    have hcw : x.committee.getD c.val false = false := by
      cases h : x.committee.getD c.val false
      · rfl
      · exact (hcW (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).elim
    have hS_sub : S ⊆ Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ := fun v hv ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (E.mem_commonApprovals_iff.mp hcS) v hv, hSlt v hv⟩
    have hℓlt : ℓ - 1 < x.election.k := by
      have : ℓ ≤ x.election.k := hℓk
      omega
    have hmem : ((((x.election.ballots.map fun b ↦
        (b, (List.range x.election.numCandidates).countP
          fun j ↦ b.getD j false && x.committee.getD j false)).countP
        fun p ↦ p.1.getD c.val false && decide (p.2 < ℓ)) : ℚ) *
        ((x.election.k : ℚ) / ((ℓ : ℚ) * (x.election.ballots.length : ℚ)))) ∈
        (List.range x.election.numCandidates).flatMap fun c' ↦
          if x.committee.getD c' false then []
          else (List.range (min x.election.numCandidates x.election.k)).map fun j ↦
            (((x.election.ballots.map fun b ↦
              (b, (List.range x.election.numCandidates).countP
                fun i ↦ b.getD i false && x.committee.getD i false)).countP
              fun p ↦ p.1.getD c' false && decide (p.2 < j + 1)) : ℚ) *
              (((min x.election.numCandidates x.election.k : ℕ) : ℚ) /
                (((j + 1 : ℕ) : ℚ) * (x.election.ballots.length : ℚ))) := by
      refine List.mem_flatMap.mpr ⟨c.val, List.mem_range.mpr c.isLt, ?_⟩
      rw [hcw, ite_eq_right Bool.false_ne_true]
      refine List.mem_map.mpr ⟨ℓ - 1, List.mem_range.mpr (by rw [hk]; exact hℓlt), ?_⟩
      have hsucc : ℓ - 1 + 1 = ℓ := by omega
      rw [hk, hsucc]
    have hle_q : (((x.election.ballots.map fun b ↦
        (b, (List.range x.election.numCandidates).countP
          fun j ↦ b.getD j false && x.committee.getD j false)).countP
        fun p ↦ p.1.getD c.val false && decide (p.2 < ℓ)) : ℚ) *
        ((x.election.k : ℚ) / ((ℓ : ℚ) * (x.election.ballots.length : ℚ))) ≤
        computeAlphaEJRPlus x := le_foldl_max_of_mem (init := (0 : ℚ)) hmem
    have hle_r : ((Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ).card : ℝ) *
        ((x.election.k : ℝ) / ((ℓ : ℝ) * (x.election.ballots.length : ℝ))) ≤
        (computeAlphaEJRPlus x : ℝ) := by
      rw [← hcnt_eq c ℓ]
      have hq := (Rat.cast_le (K := ℝ)).mpr hle_q
      push_cast at hq; exact hq
    have hScard_le : (S.card : ℝ) ≤ ((Finset.univ.filter fun v : Fin x.election.ballots.length ↦
        c ∈ E.approvals v ∧ (E.approvals v ∩ W).card < ℓ).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hS_sub
    have hpos_f : (0 : ℝ) < (x.election.k : ℝ) / ((ℓ : ℝ) * (x.election.ballots.length : ℝ)) :=
      div_pos hk_pos (mul_pos hℓ_pos hn_pos)
    have hmul := mul_le_mul_of_nonneg_right (le_trans hScard hScard_le) (le_of_lt hpos_f)
    have hcancel : (α : ℝ) * (ℓ : ℝ) * ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) *
        ((x.election.k : ℝ) / ((ℓ : ℝ) * (x.election.ballots.length : ℝ))) = (α : ℝ) := by
      have hn0 : (x.election.ballots.length : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hk0 : (x.election.k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hℓ0 : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos
      field_simp [hn0, hk0, hℓ0]
    simp only [EncodedElection.toElection, Fintype.card_fin] at hmul
    linarith

/-- For every rational `α`, `AlphaEJRPlusVerify α ∈ P`. -/
theorem alphaEJRPlusVerify_mem_P (α : ℚ) :
    AlphaEJRPlusVerify α ∈ P encEncodedElectionCommittee := by
  by_cases hα : 0 < α
  · refine ⟨fun x ↦ x.wellFormedBool && decide (computeAlphaEJRPlus x < α), ?_, fun x ↦ ?_⟩
    · exact bool_and' computableInPolyTime_wellFormedCommittee
        (rat_lt' computableInPolyTime_computeAlphaEJRPlus (const α))
    · simp only [AlphaEJRPlusVerify, Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq,
        EncodedElectionCommittee.wellFormedBool_eq_true_iff]
      exact ⟨fun ⟨hx, hs⟩ ↦ ⟨hx, (satisfiesAlphaEJRPlus_iff_computeAlphaEJRPlus_lt x hx hα).mp hs⟩,
        fun ⟨hx, hlt⟩ ↦ ⟨hx, (satisfiesAlphaEJRPlus_iff_computeAlphaEJRPlus_lt x hx hα).mpr hlt⟩⟩
  · refine ⟨fun x ↦ x.wellFormedBool && decide (x.election.k = x.election.numCandidates), ?_,
      fun x ↦ ?_⟩
    · exact bool_and' computableInPolyTime_wellFormedCommittee
        (decide_eq' (by fun_prop) (unary_to_binary.comp (by fun_prop)))
    · simp only [AlphaEJRPlusVerify, Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq,
        EncodedElectionCommittee.wellFormedBool_eq_true_iff]
      refine ⟨fun ⟨hx, hs⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hkm⟩ ↦ ⟨hx, ?_⟩⟩
      · by_contra hne
        have hlt : x.toCommittee.card < Fintype.card (Fin x.election.numCandidates) := by
          rw [x.card_toCommittee hx, Fintype.card_fin]; have := hx.1.2.2.1; omega
        exact (x.election.toElection hx.1).not_satisfiesAlphaEJRPlus_zero_of_lt hlt
          (hs.mono (by exact_mod_cast not_lt.mp hα))
      · have hW : x.toCommittee = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [x.card_toCommittee hx, Fintype.card_fin, hkm])
        rw [hW]
        exact (x.election.toElection hx.1).satisfiesAlphaEJRPlus_univ (α : ℝ)

/-! ### NP membership of `AlphaJRProblem` and `AlphaEJRPlusProblem` -/

private theorem count_true_ofFn_fin {n : ℕ} (W : Finset (Fin n)) :
    (List.ofFn fun c : Fin n ↦ decide (c ∈ W)).count true = W.card := by
  have h1 : ∀ l : List Bool,
      l.count true = (List.range l.length).countP fun j ↦ l.getD j false := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.count_cons, List.countP_cons,
        List.countP_map]
      simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ, ih]
      cases a <;> simp [Nat.add_comm]
  rw [h1, List.length_ofFn, ← card_filter_fin_eq_countP_range]
  congr 1; ext c; simp [List.getD_eq_getElem?_getD]

private theorem toCommittee_ofFn_fin {x : EncodedElection} (W : Finset (Fin x.numCandidates)) :
    (⟨x, List.ofFn fun c : Fin x.numCandidates ↦ decide (c ∈ W)⟩ :
      EncodedElectionCommittee).toCommittee = W := by
  ext c
  simp [EncodedElectionCommittee.toCommittee, List.getD_eq_getElem?_getD]

private theorem length_encEncodedElection_ge_numCandidates (x : EncodedElection) :
    x.numCandidates ≤ (encEncodedElection x).length := by
  simpa [encUnary_apply] using encEncodedElection_numCandidates_length_le x

private theorem length_encEncodedElection_ge_ballots (x : EncodedElection) :
    x.ballots.length ≤ (encEncodedElection x).length := by
  have h1 := length_le_length_encList encBits x.ballots
  have h2 := encEncodedElection_ballots_length_le x
  omega

/-- `AlphaJRProblem α ∈ NP` for every rational `α`. -/
theorem alphaJRProblem_mem_NP (α : ℚ) :
    AlphaJRProblem α ∈ NP encEncodedElection := by
  by_cases hα : 0 < α
  · let V : EncodedElection × List Bool → Bool := fun p ↦
      let y : EncodedElectionCommittee := ⟨p.1, p.2.take p.1.numCandidates⟩
      y.wellFormedBool && decide (computeAlphaJR y < α)
    refine mem_NP.mpr ⟨Polynomial.X, V, ?_, ?_⟩
    · have htake := bitsTakeWithInput (snd encEncodedElection encBits)
        (encEncodedElection_numCandidates_polyTime (fst encEncodedElection encBits))
      have hy := encEncodedElectionCommittee_mk_polyTime (fst encEncodedElection encBits) htake
      exact bool_and' (computableInPolyTime_wellFormedCommittee.comp hy)
        (rat_lt' (computableInPolyTime_computeAlphaJR.comp hy) (const α))
    · refine IsVerifier.of_padding (fun x w _ hV ↦ ?_) (fun x hx ↦ ?_)
      · dsimp only [V] at hV
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          EncodedElectionCommittee.wellFormedBool_eq_true_iff] at hV
        exact ⟨hV.1.1, (⟨x, w.take x.numCandidates⟩ : EncodedElectionCommittee).toCommittee,
          EncodedElectionCommittee.card_toCommittee _ hV.1,
          (satisfiesAlphaJR_iff_computeAlphaJR_lt _ hV.1 hα).mpr hV.2⟩
      · rcases hx with ⟨hwf, W, hWcard, hsat⟩
        let u : List Bool := List.ofFn fun c : Fin x.numCandidates ↦ decide (c ∈ W)
        refine ⟨u, ?_, fun pad ↦ ?_⟩
        · simpa [u] using length_encEncodedElection_ge_numCandidates x
        · have htake : (u ++ List.replicate pad false).take x.numCandidates = u := by
            rw [List.take_append_of_le_length (by simp [u]), List.take_of_length_le (by simp [u])]
          dsimp only [V]; rw [htake]
          have hywf : (⟨x, u⟩ : EncodedElectionCommittee).WellFormed :=
            ⟨hwf, by simp [u], by rw [count_true_ofFn_fin, hWcard]⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            EncodedElectionCommittee.wellFormedBool_eq_true_iff]
          exact ⟨hywf, (satisfiesAlphaJR_iff_computeAlphaJR_lt ⟨x, u⟩ hywf hα).mp
            (by rwa [toCommittee_ofFn_fin])⟩
  · refine mem_NP.mpr ⟨Polynomial.X, fun _ ↦ false, const false, ?_⟩
    refine IsVerifier.of_padding (fun _ _ _ h ↦ by cases h) (fun x hx ↦ ?_)
    rcases hx with ⟨hwf, W, _, hsat⟩
    exact ((x.toElection hwf).not_satisfiesAlphaJR_zero W
      (hsat.mono (by exact_mod_cast not_lt.mp hα))).elim

/-- `AlphaEJRPlusProblem α ∈ NP` for every rational `α`. -/
theorem alphaEJRPlusProblem_mem_NP (α : ℚ) :
    AlphaEJRPlusProblem α ∈ NP encEncodedElection := by
  by_cases hα : 0 < α
  · let V : EncodedElection × List Bool → Bool := fun p ↦
      let y : EncodedElectionCommittee := ⟨p.1, p.2.take p.1.numCandidates⟩
      y.wellFormedBool && decide (computeAlphaEJRPlus y < α)
    refine mem_NP.mpr ⟨Polynomial.X, V, ?_, ?_⟩
    · have htake := bitsTakeWithInput (snd encEncodedElection encBits)
        (encEncodedElection_numCandidates_polyTime (fst encEncodedElection encBits))
      have hy := encEncodedElectionCommittee_mk_polyTime (fst encEncodedElection encBits) htake
      exact bool_and' (computableInPolyTime_wellFormedCommittee.comp hy)
        (rat_lt' (computableInPolyTime_computeAlphaEJRPlus.comp hy) (const α))
    · refine IsVerifier.of_padding (fun x w _ hV ↦ ?_) (fun x hx ↦ ?_)
      · dsimp only [V] at hV
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          EncodedElectionCommittee.wellFormedBool_eq_true_iff] at hV
        exact ⟨hV.1.1, (⟨x, w.take x.numCandidates⟩ : EncodedElectionCommittee).toCommittee,
          EncodedElectionCommittee.card_toCommittee _ hV.1,
          (satisfiesAlphaEJRPlus_iff_computeAlphaEJRPlus_lt _ hV.1 hα).mpr hV.2⟩
      · rcases hx with ⟨hwf, W, hWcard, hsat⟩
        let u : List Bool := List.ofFn fun c : Fin x.numCandidates ↦ decide (c ∈ W)
        refine ⟨u, ?_, fun pad ↦ ?_⟩
        · simpa [u] using length_encEncodedElection_ge_numCandidates x
        · have htake : (u ++ List.replicate pad false).take x.numCandidates = u := by
            rw [List.take_append_of_le_length (by simp [u]), List.take_of_length_le (by simp [u])]
          dsimp only [V]; rw [htake]
          have hywf : (⟨x, u⟩ : EncodedElectionCommittee).WellFormed :=
            ⟨hwf, by simp [u], by rw [count_true_ofFn_fin, hWcard]⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            EncodedElectionCommittee.wellFormedBool_eq_true_iff]
          exact ⟨hywf, (satisfiesAlphaEJRPlus_iff_computeAlphaEJRPlus_lt ⟨x, u⟩ hywf hα).mp
            (by rwa [toCommittee_ofFn_fin])⟩
  · refine mem_NP.mpr ⟨Polynomial.X,
      fun p ↦ p.1.wellFormedBool && decide (p.1.k = p.1.numCandidates), ?_, ?_⟩
    · exact bool_and' (computableInPolyTime_wellFormedElection.comp (fst _ _))
        (decide_eq' (encEncodedElection_k_polyTime (fst _ _))
          (unary_to_binary.comp (encEncodedElection_numCandidates_polyTime (fst _ _))))
    · refine IsVerifier.of_padding (fun x _ _ hV ↦ ?_) (fun x hx ↦ ?_)
      · simp only [Bool.and_eq_true, decide_eq_true_eq,
          EncodedElection.wellFormedBool_eq_true_iff] at hV
        exact ⟨hV.1, Finset.univ, by simp [hV.2], (x.toElection hV.1).satisfiesAlphaEJRPlus_univ _⟩
      · rcases hx with ⟨hwf, W, hWcard, hsat⟩
        refine ⟨[], by simp, fun _ ↦ ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          EncodedElection.wellFormedBool_eq_true_iff]
        refine ⟨hwf, ?_⟩
        by_contra hne
        have hlt : W.card < Fintype.card (Fin x.numCandidates) := by
          rw [hWcard, Fintype.card_fin]; have := hwf.2.2.1; omega
        exact (x.toElection hwf).not_satisfiesAlphaEJRPlus_zero_of_lt hlt
          (hsat.mono (by exact_mod_cast not_lt.mp hα))

/-! ### coNP membership of `AlphaEJRVerify` -/

/-- Executable polynomial-time verifier for `(AlphaEJRVerify α)ᶜ` (`α > 0`). -/
def ejrViolationVerifier (α : ℚ) (p : EncodedElectionCommittee × List Bool) : Bool :=
  let x := p.1
  let w := p.2
  let a := α.num.toNat
  let b := α.den
  let m := x.election.numCandidates
  let n := x.election.ballots.length
  let k := min m x.election.k
  let S := w.take n
  let sCard := (List.range n).countP fun v ↦ S.getD v false
  if !x.wellFormedBool then true
  else
    (List.range k).any fun j ↦
      let ℓ : ℕ := j + 1
      let commonCard := (List.range m).countP fun c ↦
        (List.range n).all fun v ↦
          !(S.getD v false) || (x.election.ballots.getD v []).getD c false
      let allUnder := (List.range n).all fun v ↦
        !(S.getD v false) ||
          decide ((List.range m).countP (fun c ↦
            (x.election.ballots.getD v []).getD c false && x.committee.getD c false) < ℓ)
      decide (a * (ℓ * n) ≤ sCard * (b * k)) && decide (ℓ ≤ commonCard) && allUnder

private theorem computableInPolyTime_ejrViolationVerifier (α : ℚ) :
    ComputableInPolyTime (ejrViolationVerifier α)
      (encPair encEncodedElectionCommittee encBits) encBool := by
  unfold ejrViolationVerifier
  set a := α.num.toNat
  set b := α.den
  let encP := encPair encEncodedElectionCommittee encBits
  have hX : ComputableInPolyTime (fun p : EncodedElectionCommittee × List Bool ↦ p.1)
      encP encEncodedElectionCommittee := fst _ _
  have hW_in : ComputableInPolyTime (fun p : EncodedElectionCommittee × List Bool ↦ p.2)
      encP encBits := snd _ _
  have hE := encEncodedElectionCommittee_election_polyTime hX
  have hM := encEncodedElection_numCandidates_polyTime hE
  have hB := encEncodedElection_ballots_polyTime hE
  have hN := (length_list encBits).comp hB
  have hK := binary_min_unary' hM (encEncodedElection_k_polyTime hE)
  have hComm := encEncodedElectionCommittee_committee_polyTime hX
  have hS := bitsTakeWithInput hW_in hN
  have hSCard : ComputableInPolyTime
      (fun p : EncodedElectionCommittee × List Bool ↦
        (List.range p.1.election.ballots.length).countP
          fun v ↦ (p.2.take p.1.election.ballots.length).getD v false) encP encUnary :=
    countPWithInput (range.comp hN) (bitsGetDWithInput (hS.comp (fst _ _)) (snd _ _) false)
  refine ite' (bool_not.comp (computableInPolyTime_wellFormedCommittee.comp hX)) (const true) ?_
  refine anyWithInput (range.comp hK) ?_
  let encPJ := encPair encP encUnary
  have hP1 : ComputableInPolyTime (fun q : (EncodedElectionCommittee × List Bool) × ℕ ↦ q.1)
      encPJ encP := fst _ _
  have hL : ComputableInPolyTime (fun q : (EncodedElectionCommittee × List Bool) × ℕ ↦ q.2 + 1)
      encPJ encUnary := unary_add' (snd _ _) (const 1)
  have hCommCard : ComputableInPolyTime
      (fun q : (EncodedElectionCommittee × List Bool) × ℕ ↦
        (List.range q.1.1.election.numCandidates).countP fun c ↦
          (List.range q.1.1.election.ballots.length).all fun v ↦
            !((q.1.2.take q.1.1.election.ballots.length).getD v false) ||
              (q.1.1.election.ballots.getD v []).getD c false) encPJ encUnary := by
    refine countPWithInput (range.comp (hM.comp hP1)) ?_
    refine allWith (encP := encPair encPJ encUnary) (encA := encUnary)
      (test := fun r : (((EncodedElectionCommittee × List Bool) × ℕ) × ℕ) × ℕ ↦
        !((r.1.1.1.2.take r.1.1.1.1.election.ballots.length).getD r.2 false) ||
          (r.1.1.1.1.election.ballots.getD r.2 []).getD r.1.2 false) ?_ id'
      (range.comp ((hN.comp hP1).comp (fst _ _)))
    exact bool_or'
      (bool_not.comp (bitsGetDWithInput
        (((hS.comp hP1).comp (fst encPJ encUnary)).comp (fst _ _)) (snd _ _) false))
      (bitsGetDWithInput
        (listGetDWithInput (((hB.comp hP1).comp (fst encPJ encUnary)).comp (fst _ _))
          (snd _ _) [])
        ((snd encPJ encUnary).comp (fst _ _)) false)
  have hAllUnder : ComputableInPolyTime
      (fun q : (EncodedElectionCommittee × List Bool) × ℕ ↦
        (List.range q.1.1.election.ballots.length).all fun v ↦
          !((q.1.2.take q.1.1.election.ballots.length).getD v false) ||
            decide ((List.range q.1.1.election.numCandidates).countP (fun c ↦
              (q.1.1.election.ballots.getD v []).getD c false && q.1.1.committee.getD c false) <
              q.2 + 1)) encPJ encBool := by
    refine allWith (encP := encPJ) (encA := encUnary)
      (test := fun r : ((EncodedElectionCommittee × List Bool) × ℕ) × ℕ ↦
        !((r.1.1.2.take r.1.1.1.election.ballots.length).getD r.2 false) ||
          decide ((List.range r.1.1.1.election.numCandidates).countP (fun c ↦
            (r.1.1.1.election.ballots.getD r.2 []).getD c false &&
              r.1.1.1.committee.getD c false) < r.1.2 + 1)) ?_ id' (range.comp (hN.comp hP1))
    have hns := bool_not.comp (bitsGetDWithInput ((hS.comp hP1).comp (fst _ _)) (snd _ _) false)
    have hcnt : ComputableInPolyTime
        (fun r : ((EncodedElectionCommittee × List Bool) × ℕ) × ℕ ↦
          (List.range r.1.1.1.election.numCandidates).countP fun c ↦
            (r.1.1.1.election.ballots.getD r.2 []).getD c false &&
              r.1.1.1.committee.getD c false)
        (encPair encPJ encUnary) encUnary := by
      refine countPWithInput (range.comp ((hM.comp hP1).comp (fst _ _))) ?_
      exact bool_and'
        (bitsGetDWithInput
          (listGetDWithInput (((hB.comp hP1).comp (fst encPJ encUnary)).comp (fst _ _))
            ((snd encPJ encUnary).comp (fst _ _)) []) (snd _ _) false)
        (bitsGetDWithInput
          (((hComm.comp hP1).comp (fst encPJ encUnary)).comp (fst _ _)) (snd _ _) false)
    exact bool_or' hns (unary_lt' hcnt (hL.comp (fst _ _)))
  have hSize := binary_le'
    (binary_mul' (const a) (unary_to_binary.comp (unary_mul' hL (hN.comp hP1))))
    (binary_mul' (unary_to_binary.comp (hSCard.comp hP1))
      (binary_mul' (const b) (unary_to_binary.comp (hK.comp hP1))))
  exact bool_and' (bool_and' hSize (unary_le' hL hCommCard)) hAllUnder

/-- `AlphaEJRVerify α ∈ coNP` for every rational `α`. -/
theorem alphaEJRVerify_mem_coNP (α : ℚ) :
    AlphaEJRVerify α ∈ coNP encEncodedElectionCommittee := by
  rw [mem_coNP]
  by_cases hα : 0 < α
  · refine mem_NP.mpr ⟨Polynomial.X, ejrViolationVerifier α,
      computableInPolyTime_ejrViolationVerifier α, ?_⟩
    have ha_pos : (0 : ℤ) < α.num := Rat.num_pos.mpr hα
    have hb_pos : 0 < α.den := α.den_pos
    have hαeq : (α : ℝ) = (α.num.toNat : ℝ) / (α.den : ℝ) := by
      have hnum : (α.num.toNat : ℤ) = α.num := Int.toNat_of_nonneg (le_of_lt ha_pos)
      have hq : α = (α.num.toNat : ℚ) / (α.den : ℚ) := by
        calc α = (α.num : ℚ) / (α.den : ℚ) := (Rat.num_div_den α).symm
          _ = (α.num.toNat : ℚ) / (α.den : ℚ) := by rw [← hnum]; rfl
      have hr : (α : ℝ) = ((α.num.toNat : ℚ) / (α.den : ℚ) : ℝ) := by exact_mod_cast hq
      simpa using hr
    refine IsVerifier.of_padding (fun x w _ hV ↦ ?_) (fun x hx ↦ ?_)
    · dsimp only [ejrViolationVerifier] at hV
      by_cases hwf : x.WellFormed
      · have hwb : x.wellFormedBool = true :=
          (EncodedElectionCommittee.wellFormedBool_eq_true_iff x).mpr hwf
        simp only [hwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.any_eq_true,
          List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hV
        rcases hV with ⟨j, hj, ⟨hsize, hcomm⟩, hall⟩
        rintro ⟨_, hsat⟩
        let E := x.election.toElection hwf.1
        have hk_min : min x.election.numCandidates x.election.k = x.election.k :=
          Nat.min_eq_right hwf.1.2.2.1
        rw [hk_min] at hj hsize
        let S : Finset (Fin x.election.ballots.length) :=
          Finset.univ.filter fun v ↦ (w.take x.election.ballots.length).getD v.val false = true
        have hScard : S.card = (List.range x.election.ballots.length).countP
            fun v ↦ (w.take x.election.ballots.length).getD v false := by
          dsimp only [S]
          exact card_filter_fin_eq_countP_range_iff _ _ fun _ ↦ Iff.rfl
        have hcoh : E.IsAlphaCohesive (α : ℝ) (j + 1) S := by
          refine ⟨by omega, by simpa [E, EncodedElection.toElection] using hj, ?_, ?_⟩
          · simp only [E, EncodedElection.toElection, Fintype.card_fin]
            rw [hScard, hαeq]
            have hbk : (0 : ℝ) < (α.den : ℝ) * (x.election.k : ℝ) :=
              mul_pos (Nat.cast_pos.mpr hb_pos) (Nat.cast_pos.mpr hwf.1.2.1)
            have hr : ((α.num.toNat * ((j + 1) * x.election.ballots.length) : ℕ) : ℝ) ≤
                (((List.range x.election.ballots.length).countP
                  (fun v ↦ (w.take x.election.ballots.length).getD v false) *
                  (α.den * x.election.k) : ℕ) : ℝ) := by exact_mod_cast hsize
            push_cast at hr
            have hdiv := (div_le_iff₀ hbk).mpr hr
            have hEq : (α.num.toNat : ℝ) / (α.den : ℝ) * ((j : ℝ) + 1) *
                ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) =
                (α.num.toNat : ℝ) * (((j : ℝ) + 1) * (x.election.ballots.length : ℝ)) /
                  ((α.den : ℝ) * (x.election.k : ℝ)) := by
              have hbr : (α.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hb_pos)
              have hkr : (x.election.k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hwf.1.2.1)
              field_simp [hbr, hkr]
            push_cast; linarith
          · have hsub : Finset.univ.filter (fun c : Fin x.election.numCandidates ↦
                (List.range x.election.ballots.length).all (fun v ↦
                  !((w.take x.election.ballots.length).getD v false) ||
                    (x.election.ballots.getD v []).getD c.val false) = true) ⊆
                E.commonApprovals S := by
              intro c hc
              have hc' := List.all_eq_true.mp (Finset.mem_filter.mp hc).2
              rw [E.mem_commonApprovals_iff]
              intro v hv
              have hSv : (w.take x.election.ballots.length).getD v.val false = true :=
                (Finset.mem_filter.mp hv).2
              have hvv := hc' v.val (List.mem_range.mpr v.isLt)
              rw [Bool.or_eq_true, Bool.not_eq_true', hSv] at hvv
              rcases hvv with hf | ht
              · cases hf
              · simpa [E, EncodedElection.toElection] using ht
            have hcard_eq := card_filter_fin_eq_countP_range x.election.numCandidates
              (fun c ↦ (List.range x.election.ballots.length).all fun v ↦
                !((w.take x.election.ballots.length).getD v false) ||
                  (x.election.ballots.getD v []).getD c false)
            exact le_trans hcomm (hcard_eq ▸ Finset.card_le_card hsub)
        obtain ⟨v, hv, hge⟩ := hsat (j + 1) S hcoh
        have hSv : (w.take x.election.ballots.length).getD v.val false = true :=
          (Finset.mem_filter.mp hv).2
        have hvv := hall v.val v.isLt
        rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, hSv] at hvv
        rcases hvv with hf | hlt
        · cases hf
        · rw [← card_inter_toCommittee_eq x hwf v] at hlt; omega
      · exact fun hmem ↦ hwf hmem.1
    · by_cases hwf : x.WellFormed
      · have hnot : ¬(x.election.toElection hwf.1).SatisfiesAlphaEJR (α : ℝ) x.toCommittee :=
          fun hs ↦ hx ⟨hwf, hs⟩
        unfold ApprovalElection.SatisfiesAlphaEJR at hnot
        push Not at hnot
        rcases hnot with ⟨ℓ, S, hcoh, hbad⟩
        let E := x.election.toElection hwf.1
        let u : List Bool := List.ofFn fun v : Fin x.election.ballots.length ↦ decide (v ∈ S)
        refine ⟨u, ?_, fun pad ↦ ?_⟩
        · simp only [Polynomial.eval_X, u, List.length_ofFn]
          have h1 := length_encEncodedElection_ge_ballots x.election
          have h2 := encEncodedElectionCommittee_election_length_le x
          omega
        · have htake : (u ++ List.replicate pad false).take x.election.ballots.length = u := by
            rw [List.take_append_of_le_length (by simp [u]), List.take_of_length_le (by simp [u])]
          dsimp only [ejrViolationVerifier]; rw [htake]
          have hwb : x.wellFormedBool = true :=
            (EncodedElectionCommittee.wellFormedBool_eq_true_iff x).mpr hwf
          have hk_min : min x.election.numCandidates x.election.k = x.election.k :=
            Nat.min_eq_right hwf.1.2.2.1
          have hget_u : ∀ v : Fin x.election.ballots.length,
              u.getD v.val false = decide (v ∈ S) := fun v ↦ by
            simp [u, List.getD_eq_getElem?_getD]
          simp only [hwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.any_eq_true,
            List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, hk_min]
          have hℓ1 : 1 ≤ ℓ := hcoh.1
          have hℓk : ℓ ≤ x.election.k := hcoh.2.1
          refine ⟨ℓ - 1, by omega, ⟨?_, ?_⟩, ?_⟩
          · have hsucc : ℓ - 1 + 1 = ℓ := by omega
            rw [hsucc]
            have hSc : (List.range x.election.ballots.length).countP (fun v ↦ u.getD v false) =
                S.card := by
              rw [← card_filter_fin_eq_countP_range]
              congr 1; ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, hget_u v, decide_eq_true_eq]
            rw [hSc]
            have hScard_r := hcoh.2.2.1
            simp only [EncodedElection.toElection, Fintype.card_fin] at hScard_r
            rw [hαeq] at hScard_r
            have hbk : (0 : ℝ) < (α.den : ℝ) * (x.election.k : ℝ) :=
              mul_pos (Nat.cast_pos.mpr hb_pos) (Nat.cast_pos.mpr hwf.1.2.1)
            have hmul := mul_le_mul_of_nonneg_right hScard_r (le_of_lt hbk)
            have hcancel : (α.num.toNat : ℝ) / (α.den : ℝ) * (ℓ : ℝ) *
                ((x.election.ballots.length : ℝ) / (x.election.k : ℝ)) *
                ((α.den : ℝ) * (x.election.k : ℝ)) =
                (α.num.toNat : ℝ) * ((ℓ : ℝ) * (x.election.ballots.length : ℝ)) := by
              have hbr : (α.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hb_pos)
              have hkr : (x.election.k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hwf.1.2.1)
              field_simp [hbr, hkr]
            have hr : (α.num.toNat : ℝ) * ((ℓ : ℝ) * (x.election.ballots.length : ℝ)) ≤
                (S.card : ℝ) * ((α.den : ℝ) * (x.election.k : ℝ)) := by linarith
            exact_mod_cast hr
          · have hsucc : ℓ - 1 + 1 = ℓ := by omega
            rw [hsucc]
            have hcard_eq : (List.range x.election.numCandidates).countP (fun c ↦
                (List.range x.election.ballots.length).all fun v ↦
                  !(u.getD v false) || (x.election.ballots.getD v []).getD c false) =
                (E.commonApprovals S).card := by
              symm
              have hEq : E.commonApprovals S = Finset.univ.filter fun c ↦ c ∈ E.commonApprovals S :=
                by ext c; simp
              rw [hEq]
              refine card_filter_fin_eq_countP_range_iff _ _ fun c ↦ ?_
              rw [E.mem_commonApprovals_iff, List.all_eq_true]
              constructor
              · intro hc v hv
                have hvlt : v < x.election.ballots.length := List.mem_range.mp hv
                rw [hget_u ⟨v, hvlt⟩, Bool.or_eq_true, Bool.not_eq_true']
                by_cases hvs : (⟨v, hvlt⟩ : Fin x.election.ballots.length) ∈ S
                · exact Or.inr (Finset.mem_filter.mp (hc _ hvs)).2
                · exact Or.inl (by simp [hvs])
              · intro hc v hvs
                have hv := hc v.val (List.mem_range.mpr v.isLt)
                rw [hget_u v, Bool.or_eq_true, Bool.not_eq_true'] at hv
                rcases hv with hf | ht
                · simp [hvs] at hf
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
            rw [hcard_eq]; exact hcoh.2.2.2
          · intro v hvlt
            have hsucc : ℓ - 1 + 1 = ℓ := by omega
            rw [hsucc, hget_u ⟨v, hvlt⟩, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
            by_cases hvs : (⟨v, hvlt⟩ : Fin x.election.ballots.length) ∈ S
            · exact Or.inr ((card_inter_toCommittee_eq x hwf ⟨v, hvlt⟩).symm ▸ hbad _ hvs)
            · exact Or.inl (by simp [hvs])
      · refine ⟨[], by simp, fun _ ↦ ?_⟩
        have hwb : x.wellFormedBool = false := by
          cases h : x.wellFormedBool
          · rfl
          · exact (hwf ((EncodedElectionCommittee.wellFormedBool_eq_true_iff x).mp h)).elim
        simp [ejrViolationVerifier, hwb]
  · refine mem_NP.mpr ⟨Polynomial.X, fun _ ↦ true, const true, ?_⟩
    refine IsVerifier.of_padding (fun x _ _ _ ↦ ?_) (fun _ _ ↦ ⟨[], by simp, fun _ ↦ rfl⟩)
    rintro ⟨hwf, hsat⟩
    exact (x.election.toElection hwf.1).not_satisfiesAlphaEJR_zero x.toCommittee
      (hsat.mono (by exact_mod_cast not_lt.mp hα))

end CslibFrontier.Complexity.ApprovalVoting
