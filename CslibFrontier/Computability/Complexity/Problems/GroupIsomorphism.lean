/-
Copyright (c) 2026 FormalPapers / CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers / CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Mathlib.Algebra.Group.Defs

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Group Isomorphism and Automorphism Counting on Cayley Tables

This module formalizes finite groups given by Cayley multiplication tables, their bitstring
encodings and polynomial-time group-axiom verification, the decision problem
`GroupIsomorphism ∈ NP`, and the counting functions `GroupIsomorphismCount` and
`GroupAutomorphismCount` together with the parsimonious and `#P`-Turing reductions from
automorphism counting to isomorphism counting, proved under standard Lean axioms.

## Main definitions

* `CslibFrontier.Complexity.CayleyTable`, `CslibFrontier.Complexity.encCayleyTable`,
  `CslibFrontier.Complexity.CayleyGroup`, `CslibFrontier.Complexity.encCayleyGroup`,
  `CslibFrontier.Complexity.CayleyGroupPair`, `CslibFrontier.Complexity.encCayleyGroupPair`:
  Cayley-table finite group carriers and encodings.
* `CslibFrontier.Complexity.GroupIsomorphism`: the group isomorphism decision language.
* `CslibFrontier.Complexity.GroupIsomorphismCount`,
  `CslibFrontier.Complexity.GroupAutomorphismCount`: isomorphism and automorphism counting problems.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_isGroupBool`: verifying the group axioms on a
  Cayley table is in `P`.
* `CslibFrontier.Complexity.groupIsomorphism_mem_NP`: `GroupIsomorphism ∈ NP encCayleyGroupPair`.
* `CslibFrontier.Complexity.parsimoniousReducible_groupAutomorphismCount`:
  `ParsimoniousReducible encCayleyGroup encCayleyGroupPair` from `GroupAutomorphismCount` to
  `GroupIsomorphismCount`.
* `CslibFrontier.Complexity.countingTuringReducible_groupAutomorphismCount`:
  `CountingTuringReducible encCayleyGroup encCayleyGroupPair` from `GroupAutomorphismCount` to
  `GroupIsomorphismCount`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private lemma list_getD_eq_getElem {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

private lemma length_encList_le {α : Type} (encA : α ↪ List Bool) (l : List α) {B : ℕ}
    (hB : ∀ x ∈ l, (encA x).length ≤ B) :
    (encList encA l).length ≤ l.length * (2 * B + 2) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := hB a List.mem_cons_self
    have has := ih fun x hx ↦ hB x (List.mem_cons_of_mem a hx)
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    nlinarith

/-- Raw Cayley multiplication table on `{0, …, order - 1}` with `0` denoting the identity candidate.
-/
@[ext]
structure CayleyTable where
  /-- Declared order `n` of the carrier `{0, …, n - 1}`. -/
  order : ℕ
  /-- `n × n` multiplication table of indices in `{0, …, n - 1}`. -/
  table : List (List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- Framed pair encoding `(order, table)` of a `CayleyTable`. -/
def encCayleyTable : CayleyTable ↪ List Bool where
  toFun T := encPair encNat (encList (encList encNat)) (T.order, T.table)
  inj' T₁ T₂ h := by
    have hp := (encPair encNat (encList (encList encNat))).injective h
    exact CayleyTable.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)

/-- Table lookup `(T.table.getD i []).getD j 0`. -/
@[expose]
def CayleyTable.mulOp (T : CayleyTable) (i j : ℕ) : ℕ :=
  (T.table.getD i []).getD j 0

/-- Polynomial-time Boolean validator checking that `T` defines a group on `{0, …, T.order - 1}`
with identity `0`. -/
def CayleyTable.isGroupBool (T : CayleyTable) : Bool :=
  let n := T.table.length
  decide (0 < n) && (T.order == n) &&
    (T.table.all fun row ↦ (row.length == n) && row.all fun e ↦ decide (e < n)) &&
    ((List.range n).all fun i ↦ (T.mulOp 0 i == i) && (T.mulOp i 0 == i)) &&
    ((List.range n).all fun i ↦
      (List.range n).any fun j ↦ (T.mulOp i j == 0) && (T.mulOp j i == 0)) &&
    ((List.range n).all fun i ↦
      (List.range n).all fun j ↦
        (List.range n).all fun k ↦
          T.mulOp (T.mulOp i j) k == T.mulOp i (T.mulOp j k))

private lemma computableInPolyTime_range_nat {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun x ↦ List.range (n x)) encIn (encList encNat) := by
  have hmap : ComputableInPolyTime (fun l : List ℕ ↦ l.map id)
      (encList encUnary) (encList encNat) :=
    ComputableInPolyTime.map unary_to_binary
  exact (hmap.comp (range.comp hn)).of_enc_eq fun _ ↦ by simp

private lemma computableInPolyTime_mulOp {γ : Type} {encIn : γ ↪ List Bool}
    {T : γ → CayleyTable} {i j : γ → ℕ}
    (hT : ComputableInPolyTime T encIn encCayleyTable)
    (hi : ComputableInPolyTime i encIn encNat)
    (hj : ComputableInPolyTime j encIn encNat) :
    ComputableInPolyTime (fun x ↦ (T x).mulOp (i x) (j x)) encIn encNat := by
  have htbl : ComputableInPolyTime CayleyTable.table encCayleyTable (encList (encList encNat)) :=
    ((id' (encIn := encCayleyTable)).of_enc_eq
      (encD := encPair encNat (encList (encList encNat)))
      fun _ ↦ rfl).snd'
  have hrow : ComputableInPolyTime (fun x ↦ (T x).table.getD (i x) []) encIn (encList encNat) :=
    listGetD_binary ([] : List ℕ) (htbl.comp hT) hi
  exact listGetD_binary 0 hrow hj

/-- `CayleyTable.isGroupBool` is computable in polynomial time. -/
theorem computableInPolyTime_isGroupBool :
    ComputableInPolyTime CayleyTable.isGroupBool encCayleyTable encBool := by
  have hpair : ComputableInPolyTime (fun T : CayleyTable ↦ (T.order, T.table))
      encCayleyTable (encPair encNat (encList (encList encNat))) :=
    id'.of_enc_eq fun _ ↦ rfl
  have hord := hpair.fst'
  have htbl := hpair.snd'
  have hn_u := (length_list (encList encNat)).comp htbl
  have hn_b := unary_to_binary.comp hn_u
  have hrng := computableInPolyTime_range_nat hn_u
  have h1 := binary_lt' (const 0) hn_b
  have h2 := hord.beq hn_b
  have h3 : ComputableInPolyTime
      (fun T : CayleyTable ↦
        T.table.all fun row ↦ (row.length == T.table.length) &&
          row.all fun e ↦ decide (e < T.table.length))
      encCayleyTable encBool := by
    let ERow := encPair encCayleyTable (encList encNat)
    refine allWithInput htbl ?_
    have hall_e : ComputableInPolyTime
        (fun q : CayleyTable × List ℕ ↦ q.2.all fun e ↦ decide (e < q.1.table.length))
        ERow encBool := by
      refine allWithInput (snd encCayleyTable (encList encNat)) ?_
      exact (binary_lt' (snd ERow encNat) (hn_b.comp (fst ERow encNat).fst')).of_enc_eq fun _ ↦ rfl
    exact (bool_and.comp
      ((unary_beq ((length_list encNat).comp (snd encCayleyTable (encList encNat)))
          (hn_u.comp (fst encCayleyTable (encList encNat)))).prod
        hall_e)).of_enc_eq fun _ ↦ rfl
  let E1 := encPair encCayleyTable encNat
  let E2 := encPair E1 encNat
  have h4 : ComputableInPolyTime
      (fun T : CayleyTable ↦
        (List.range T.table.length).all fun i ↦ (T.mulOp 0 i == i) && (T.mulOp i 0 == i))
      encCayleyTable encBool := by
    refine allWithInput hrng ?_
    exact (bool_and.comp
      (((computableInPolyTime_mulOp (fst encCayleyTable encNat) (const 0)
          (snd encCayleyTable encNat)).beq (snd encCayleyTable encNat)).prod
        ((computableInPolyTime_mulOp (fst encCayleyTable encNat)
          (snd encCayleyTable encNat) (const 0)).beq (snd encCayleyTable encNat)))).of_enc_eq
      fun _ ↦ rfl
  have h5 : ComputableInPolyTime
      (fun T : CayleyTable ↦
        (List.range T.table.length).all fun i ↦
          (List.range T.table.length).any fun j ↦ (T.mulOp i j == 0) && (T.mulOp j i == 0))
      encCayleyTable encBool := by
    refine allWithInput hrng ?_
    refine anyWithInput (hrng.comp (fst encCayleyTable encNat)) ?_
    exact (bool_and.comp
      (((computableInPolyTime_mulOp (fst E1 encNat).fst' (fst E1 encNat).snd'
          (snd E1 encNat)).beq (const 0)).prod
        ((computableInPolyTime_mulOp (fst E1 encNat).fst' (snd E1 encNat)
          (fst E1 encNat).snd').beq (const 0)))).of_enc_eq fun _ ↦ rfl
  have h6 : ComputableInPolyTime
      (fun T : CayleyTable ↦
        (List.range T.table.length).all fun i ↦
          (List.range T.table.length).all fun j ↦
            (List.range T.table.length).all fun k ↦
              T.mulOp (T.mulOp i j) k == T.mulOp i (T.mulOp j k))
      encCayleyTable encBool := by
    refine allWithInput hrng ?_
    refine allWithInput (hrng.comp (fst encCayleyTable encNat)) ?_
    refine allWithInput (hrng.comp (fst E1 encNat).fst') ?_
    have hT0 := (fst E2 encNat).fst'.fst'
    have hi0 := (fst E2 encNat).fst'.snd'
    have hj0 := (fst E2 encNat).snd'
    have hk0 := snd E2 encNat
    exact ((computableInPolyTime_mulOp hT0 (computableInPolyTime_mulOp hT0 hi0 hj0) hk0).beq
      (computableInPolyTime_mulOp hT0 hi0 (computableInPolyTime_mulOp hT0 hj0 hk0))).of_enc_eq
      fun _ ↦ rfl
  unfold CayleyTable.isGroupBool
  exact (bool_and.comp ((bool_and.comp ((bool_and.comp ((bool_and.comp ((bool_and.comp
    (h1.prod h2)).prod h3)).prod h4)).prod h5)).prod h6)).of_enc_eq fun _ ↦ rfl

private lemma isGroupBool_props {T : CayleyTable} (h : T.isGroupBool = true) :
    0 < T.table.length ∧
    T.order = T.table.length ∧
    (∀ i < T.table.length, ∀ j < T.table.length, T.mulOp i j < T.table.length) ∧
    (∀ i < T.table.length, T.mulOp 0 i = i ∧ T.mulOp i 0 = i) ∧
    (∀ i < T.table.length, ∃ j < T.table.length, T.mulOp i j = 0 ∧ T.mulOp j i = 0) ∧
    (∀ i < T.table.length, ∀ j < T.table.length, ∀ k < T.table.length,
      T.mulOp (T.mulOp i j) k = T.mulOp i (T.mulOp j k)) := by
  unfold CayleyTable.isGroupBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range] at h
  rcases h with ⟨⟨⟨⟨⟨hpos, hord⟩, hrows⟩, hid⟩, hinv⟩, hassoc⟩
  refine ⟨hpos, hord, ?_, hid, hinv, hassoc⟩
  intro i hi j hj
  have hrow_mem : T.table[i] ∈ T.table := List.getElem_mem hi
  have ⟨hlen_r, hall_r⟩ := hrows T.table[i] hrow_mem
  have hj' : j < T.table[i].length := hlen_r.symm ▸ hj
  have he_mem : T.table[i][j] ∈ T.table[i] := List.getElem_mem hj'
  have hget : T.mulOp i j = T.table[i][j] := by
    unfold CayleyTable.mulOp
    rw [list_getD_eq_getElem _ _ hi, list_getD_eq_getElem _ _ hj']
  rw [hget]
  exact hall_r _ he_mem

/-- A verified finite group given by a `CayleyTable`. -/
abbrev CayleyGroup : Type :=
  { T : CayleyTable // T.isGroupBool = true }

/-- Order `n ≥ 1` of a `CayleyGroup`. -/
@[expose]
def CayleyGroup.order (G : CayleyGroup) : ℕ :=
  G.1.order

/-- Bitstring encoding of `CayleyGroup`. -/
def encCayleyGroup : CayleyGroup ↪ List Bool :=
  (Function.Embedding.subtype _).trans encCayleyTable

/-- Underlying group carrier `Fin G.order` of `G : CayleyGroup`. -/
@[expose]
def CayleyGroup.Elem (G : CayleyGroup) : Type :=
  Fin G.order

instance (G : CayleyGroup) : Fintype G.Elem :=
  Fin.fintype G.order

instance (G : CayleyGroup) : Finite G.Elem :=
  Finite.of_fintype G.Elem

instance (G : CayleyGroup) : DecidableEq G.Elem :=
  inferInstanceAs (DecidableEq (Fin G.order))

instance (G : CayleyGroup) : CoeOut G.Elem ℕ :=
  ⟨Fin.val⟩

private lemma cayleyGroup_mulOp_lt (G : CayleyGroup) {i j : ℕ} (hi : i < G.order)
    (hj : j < G.order) : G.1.mulOp i j < G.order := by
  have ⟨_, hord, hclosed, _, _, _⟩ := isGroupBool_props G.2
  have hi' : i < G.1.table.length := by unfold CayleyGroup.order at hi; omega
  have hj' : j < G.1.table.length := by unfold CayleyGroup.order at hj; omega
  have hlt := hclosed i hi' j hj'
  unfold CayleyGroup.order
  omega

/-- Two-sided inverse lookup in `G.1.table` on `{0, …, G.order - 1}`. -/
def CayleyGroup.invFn (G : CayleyGroup) (i : ℕ) : ℕ :=
  ((List.range G.1.table.length).find? fun j ↦
    (G.1.mulOp i j == 0) && (G.1.mulOp j i == 0)).getD 0

private lemma cayleyGroup_invFn_spec (G : CayleyGroup) {i : ℕ} (hi : i < G.order) :
    G.invFn i < G.order ∧ G.1.mulOp (G.invFn i) i = 0 := by
  have ⟨_, hord, _, _, hinv, _⟩ := isGroupBool_props G.2
  obtain ⟨j, hj, hij, hji⟩ := hinv i (by unfold CayleyGroup.order at hi; omega)
  have hsome : ∃ k, ((List.range G.1.table.length).find? fun k ↦
      (G.1.mulOp i k == 0) && (G.1.mulOp k i == 0)) = some k :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨j, List.mem_range.mpr hj,
      by simp [hij, hji]⟩)
  obtain ⟨k, hk⟩ := hsome
  have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hk)
  have hp := List.find?_some hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  unfold CayleyGroup.invFn
  rw [hk, Option.getD_some]
  refine ⟨?_, hp.2⟩
  unfold CayleyGroup.order
  omega

instance (G : CayleyGroup) : Group G.Elem where
  one := ⟨0, by
    have ⟨hpos, hord, _, _, _, _⟩ := isGroupBool_props G.2
    unfold CayleyGroup.order; omega⟩
  mul a b := ⟨G.1.mulOp a.1 b.1, by exact cayleyGroup_mulOp_lt G a.2 b.2⟩
  inv a := ⟨G.invFn a.1, by exact (cayleyGroup_invFn_spec G a.2).1⟩
  mul_assoc a b c := by
    have ⟨_, hord, _, _, _, hassoc⟩ := isGroupBool_props G.2
    exact Fin.ext (hassoc a.1 (by unfold CayleyGroup.order at *; omega)
      b.1 (by unfold CayleyGroup.order at *; omega)
      c.1 (by unfold CayleyGroup.order at *; omega))
  one_mul a := by
    have ⟨_, hord, _, hid, _, _⟩ := isGroupBool_props G.2
    exact Fin.ext (hid a.1 (by unfold CayleyGroup.order at *; omega)).1
  mul_one a := by
    have ⟨_, hord, _, hid, _, _⟩ := isGroupBool_props G.2
    exact Fin.ext (hid a.1 (by unfold CayleyGroup.order at *; omega)).2
  inv_mul_cancel a := by exact Fin.ext (cayleyGroup_invFn_spec G a.2).2

/-- Pair `(first, second)` of `CayleyGroup`s. -/
@[ext]
structure CayleyGroupPair where
  /-- First input group `G`. -/
  first : CayleyGroup
  /-- Second input group `H`. -/
  second : CayleyGroup

/-- Bitstring encoding of `CayleyGroupPair`. -/
def encCayleyGroupPair : CayleyGroupPair ↪ List Bool where
  toFun P := encPair encCayleyGroup encCayleyGroup (P.first, P.second)
  inj' P₁ P₂ h := by
    have hp := (encPair encCayleyGroup encCayleyGroup).injective h
    exact CayleyGroupPair.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)

/-- Polynomial-time verifier checking whether `σ : List ℕ` encodes a group isomorphism
`P.first.Elem ≃* P.second.Elem`. -/
def isIsoPermCheck (p : CayleyGroupPair × List ℕ) : Bool :=
  let G := p.1.first
  let H := p.1.second
  let σ := p.2
  (G.order == H.order) &&
    (σ.length == H.order) &&
    decide σ.Nodup &&
    (σ.all fun y ↦ decide (y < H.order)) &&
    ((List.range G.order).all fun i ↦
      (List.range G.order).all fun j ↦
        σ.getD (G.1.mulOp i j) 0 == H.1.mulOp (σ.getD i 0) (σ.getD j 0))

private lemma computableInPolyTime_isIsoPermCheck :
    ComputableInPolyTime isIsoPermCheck (encPair encCayleyGroupPair (encList encNat)) encBool := by
  let EIn := encPair encCayleyGroupPair (encList encNat)
  let E1 := encPair EIn encNat
  have hP := fst encCayleyGroupPair (encList encNat)
  have hσ := snd encCayleyGroupPair (encList encNat)
  have hpairP : ComputableInPolyTime (fun P : CayleyGroupPair ↦ (P.first.1, P.second.1))
      encCayleyGroupPair (encPair encCayleyTable encCayleyTable) :=
    id'.of_enc_eq fun _ ↦ rfl
  have hTG := hpairP.fst'.comp hP
  have hTH := hpairP.snd'.comp hP
  have hordG_u : ComputableInPolyTime (fun x : CayleyGroupPair × List ℕ ↦ x.1.first.order)
      EIn encUnary := by
    have htbl := ((id' (encIn := encCayleyTable)).of_enc_eq
      (encD := encPair encNat (encList (encList encNat))) fun _ ↦ rfl).snd'.comp hTG
    exact ((length_list (encList encNat)).comp htbl).of_enc_eq fun x ↦ by
      simp [CayleyGroup.order, (isGroupBool_props x.1.first.2).2.1]
  have hordH_u : ComputableInPolyTime (fun x : CayleyGroupPair × List ℕ ↦ x.1.second.order)
      EIn encUnary := by
    have htbl := ((id' (encIn := encCayleyTable)).of_enc_eq
      (encD := encPair encNat (encList (encList encNat))) fun _ ↦ rfl).snd'.comp hTH
    exact ((length_list (encList encNat)).comp htbl).of_enc_eq fun x ↦ by
      simp [CayleyGroup.order, (isGroupBool_props x.1.second.2).2.1]
  have hordH_b := unary_to_binary.comp hordH_u
  have h1 := unary_beq hordG_u hordH_u
  have h2 := unary_beq ((length_list encNat).comp hσ) hordH_u
  have h3 := decide_nodup hσ
  have h4 : ComputableInPolyTime
      (fun x : CayleyGroupPair × List ℕ ↦ x.2.all fun y ↦ decide (y < x.1.second.order))
      EIn encBool := by
    refine allWithInput hσ ?_
    exact (binary_lt' (snd EIn encNat) (hordH_b.comp (fst EIn encNat))).of_enc_eq fun _ ↦ rfl
  have hrngG := computableInPolyTime_range_nat hordG_u
  have h5 : ComputableInPolyTime
      (fun x : CayleyGroupPair × List ℕ ↦
        (List.range x.1.first.order).all fun i ↦
          (List.range x.1.first.order).all fun j ↦
            x.2.getD (x.1.first.1.mulOp i j) 0 ==
              x.1.second.1.mulOp (x.2.getD i 0) (x.2.getD j 0))
      EIn encBool := by
    refine allWithInput hrngG ?_
    refine allWithInput (hrngG.comp (fst EIn encNat)) ?_
    have hx := (fst E1 encNat).fst'
    have hi := (fst E1 encNat).snd'
    have hj := snd E1 encNat
    have hmulG := computableInPolyTime_mulOp (hTG.comp hx) hi hj
    have hσij : ComputableInPolyTime _ _ encNat := listGetD_binary 0 (hσ.comp hx) hmulG
    have hσi : ComputableInPolyTime _ _ encNat := listGetD_binary 0 (hσ.comp hx) hi
    have hσj : ComputableInPolyTime _ _ encNat := listGetD_binary 0 (hσ.comp hx) hj
    exact (hσij.beq (computableInPolyTime_mulOp (hTH.comp hx) hσi hσj)).of_enc_eq fun _ ↦ rfl
  unfold isIsoPermCheck
  exact (bool_and.comp ((bool_and.comp ((bool_and.comp ((bool_and.comp
    (h1.prod h2)).prod h3)).prod h4)).prod h5)).of_enc_eq fun _ ↦ rfl

/-- The **Group Isomorphism** decision language on pairs of `CayleyGroup`s. -/
def GroupIsomorphism : Set CayleyGroupPair :=
  { P | Nonempty (P.first.Elem ≃* P.second.Elem) }

/-- `GroupIsomorphism ∈ NP encCayleyGroupPair`. -/
theorem groupIsomorphism_mem_NP : GroupIsomorphism ∈ NP encCayleyGroupPair := by
  refine mem_NP_of_check (p := 4 * (Polynomial.X + 1) ^ 2) (Decoder.list Decoder.nat)
    computableInPolyTime_isIsoPermCheck
    (fun P σ hcheck ↦ ?_)
    (fun P ⟨φ⟩ ↦ ?_)
  · unfold isIsoPermCheck at hcheck
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hcheck
    rcases hcheck with ⟨⟨⟨⟨hord_eq, hlen⟩, hnd⟩, hlt⟩, hhom⟩
    let f : P.first.Elem → P.second.Elem := fun i ↦
      have hi : i.1 < σ.length := by omega
      ⟨σ[i.1]'hi, hlt _ (List.getElem_mem hi)⟩
    have hinj : Function.Injective f := fun i j hij ↦
      Fin.ext ((hnd.getElem_inj_iff).mp (congrArg Fin.val hij))
    have hc1 : Fintype.card P.first.Elem = P.first.order :=
      (Fintype.card_congr (Equiv.refl (Fin P.first.order))).trans (Fintype.card_fin P.first.order)
    have hc2 : Fintype.card P.second.Elem = P.second.order :=
      (Fintype.card_congr (Equiv.refl (Fin P.second.order))).trans
        (Fintype.card_fin P.second.order)
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [hc1, hc2, hord_eq]⟩
    refine ⟨MulEquiv.ofBijective
      ({ toFun := f
         map_mul' := fun a b ↦ ?_ } : P.first.Elem →ₙ* P.second.Elem) hbij⟩
    apply Fin.ext
    have hm := hhom a.1 a.2 b.1 b.2
    have hab : P.first.1.mulOp a.1 b.1 < σ.length := by
      have hlt_ab : P.first.1.mulOp a.1 b.1 < P.first.order :=
        cayleyGroup_mulOp_lt P.first a.2 b.2
      omega
    have ha_lt : a.1 < σ.length := by have := a.2; omega
    have hb_lt : b.1 < σ.length := by have := b.2; omega
    rw [list_getD_eq_getElem _ _ hab, list_getD_eq_getElem _ _ ha_lt,
      list_getD_eq_getElem _ _ hb_lt] at hm
    exact hm
  · have hc1 : Fintype.card P.first.Elem = P.first.order :=
      (Fintype.card_congr (Equiv.refl (Fin P.first.order))).trans (Fintype.card_fin P.first.order)
    have hc2 : Fintype.card P.second.Elem = P.second.order :=
      (Fintype.card_congr (Equiv.refl (Fin P.second.order))).trans
        (Fintype.card_fin P.second.order)
    have hord_eq : P.first.order = P.second.order := by
      have h := Fintype.card_congr φ.toEquiv
      rwa [hc1, hc2] at h
    have hfn_ex : ∃ fn : Fin P.first.order → ℕ,
        ∀ i : Fin P.first.order, fn i = (φ (⟨i.1, i.2⟩ : P.first.Elem)).1 :=
      ⟨fun i ↦ (φ i).1, fun _ ↦ rfl⟩
    obtain ⟨fn, hfn_app⟩ := hfn_ex
    let σ : List ℕ := List.ofFn fn
    refine ⟨σ, ?_, ?_⟩
    · unfold isIsoPermCheck
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨hord_eq, by simp [σ, hord_eq]⟩, ?_⟩, ?_⟩, ?_⟩
      · dsimp only [σ]
        rw [List.nodup_ofFn]
        intro i j hij
        rw [hfn_app, hfn_app] at hij
        have heq : (⟨i.1, i.2⟩ : P.first.Elem) = ⟨j.1, j.2⟩ := φ.injective (Fin.ext hij)
        exact Fin.ext (congrArg Fin.val heq)
      · intro y hy
        dsimp only [σ] at hy
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        rw [hfn_app]
        exact (φ (⟨i.1, i.2⟩ : P.first.Elem)).2
      · intro i hi j hj
        let fi : P.first.Elem := ⟨i, hi⟩
        let fj : P.first.Elem := ⟨j, hj⟩
        have h1 : σ.getD (P.first.1.mulOp i j) 0 = (φ (fi * fj)).1 := by
          have hij_lt : P.first.1.mulOp i j < P.first.order := (fi * fj).2
          dsimp only [σ]
          rw [list_getD_eq_getElem _ _ (by simp [hij_lt]), List.getElem_ofFn, hfn_app]
          rfl
        have h2 : σ.getD i 0 = (φ fi).1 := by
          dsimp only [σ]
          rw [list_getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn, hfn_app]
        have h3 : σ.getD j 0 = (φ fj).1 := by
          dsimp only [σ]
          rw [list_getD_eq_getElem _ _ (by simp [hj]), List.getElem_ofFn, hfn_app]
        rw [h1, h2, h3, map_mul]
        rfl
    · have hn_le : P.second.order ≤ (encCayleyGroupPair P).length := by
        have ⟨_, ho, _, _, _, _⟩ := isGroupBool_props P.second.2
        have hlen_tbl : P.second.1.table.length ≤
            (encList (encList encNat) P.second.1.table).length :=
          SizedListEncoding.length_le (encA := encList encNat)
            (encL := encList (encList encNat)) P.second.1.table
        have hlen_P : (encList (encList encNat) P.second.1.table).length ≤
            (encCayleyGroupPair P).length := by
          change (encList (encList encNat) P.second.1.table).length ≤
            (encPair encCayleyGroup encCayleyGroup (P.first, P.second)).length
          have h1 : (encList (encList encNat) P.second.1.table).length ≤
              (encCayleyGroup P.second).length := by
            change _ ≤ (encPair encNat (encList (encList encNat))
              (P.second.1.order, P.second.1.table)).length
            rw [length_encPair]
            dsimp only
            omega
          rw [length_encPair]
          dsimp only
          omega
        unfold CayleyGroup.order
        omega
      have helem : ∀ y ∈ σ, (encNat y).length ≤ P.second.order := by
        intro y hy
        dsimp only [σ] at hy
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        rw [hfn_app]
        simp only [encNat_apply, Nat.size_eq_bits_len]
        exact (Nat.size_le_self _).trans (Nat.le_of_lt (φ (⟨i.1, i.2⟩ : P.first.Elem)).2)
      have hσ_len := length_encList_le encNat σ helem
      dsimp only [σ] at hσ_len ⊢
      simp only [List.length_ofFn, hord_eq, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one] at hσ_len ⊢
      nlinarith

/-- Number of group isomorphisms `P.first.Elem ≃* P.second.Elem`. -/
noncomputable def GroupIsomorphismCount (P : CayleyGroupPair) : ℕ :=
  Nat.card (P.first.Elem ≃* P.second.Elem)

/-- Number of group automorphisms `MulAut G.Elem`. -/
noncomputable def GroupAutomorphismCount (G : CayleyGroup) : ℕ :=
  Nat.card (MulAut G.Elem)

/-- `GroupAutomorphismCount` is parsimoniously reducible to `GroupIsomorphismCount` via
`G ↦ (G, G)`. -/
theorem parsimoniousReducible_groupAutomorphismCount :
    ParsimoniousReducible encCayleyGroup encCayleyGroupPair
      GroupAutomorphismCount GroupIsomorphismCount := by
  have hid := id' (encIn := encCayleyGroup)
  refine ⟨fun G ↦ CayleyGroupPair.mk G G, (hid.prod hid).of_enc_eq fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- `GroupAutomorphismCount` is `#P`-Turing reducible to `GroupIsomorphismCount`. -/
theorem countingTuringReducible_groupAutomorphismCount :
    CountingTuringReducible encCayleyGroup encCayleyGroupPair
      GroupAutomorphismCount GroupIsomorphismCount := by
  have hord_u : ComputableInPolyTime CayleyGroup.order encCayleyGroup encUnary := by
    have htbl : ComputableInPolyTime (fun G : CayleyGroup ↦ G.1.table)
        encCayleyGroup (encList (encList encNat)) :=
      ((id' (encIn := encCayleyGroup)).of_enc_eq
        (encD := encPair encNat (encList (encList encNat))) fun _ ↦ rfl).snd'
    exact ((length_list (encList encNat)).comp htbl).of_enc_eq fun G ↦ by
      simp [CayleyGroup.order, (isGroupBool_props G.2).2.1]
  have hmk : ComputableInPolyTime (fun G : CayleyGroup ↦ [CayleyGroupPair.mk G G])
      encCayleyGroup (encList encCayleyGroupPair) := by
    have hid := id' (encIn := encCayleyGroup)
    have hpair : ComputableInPolyTime (fun G : CayleyGroup ↦ CayleyGroupPair.mk G G)
        encCayleyGroup encCayleyGroupPair :=
      (hid.prod hid).of_enc_eq fun _ ↦ rfl
    have hc_nil : ComputableInPolyTime (fun _ : CayleyGroup ↦ ([] : List CayleyGroupPair))
        encCayleyGroup (encList encCayleyGroupPair) := const []
    exact ((cons encCayleyGroupPair).comp (hpair.prod hc_nil)).of_enc_eq fun _ ↦ rfl
  refine PolyTimeOracleProgram.of_batchNatBits
    (queries := fun G ↦ [CayleyGroupPair.mk G G])
    (bound := fun G ↦ G.order * G.order + 1)
    (combine := fun p ↦ p.2.headD 0)
    hmk
    (unary_add' (unary_mul' hord_u hord_u) (const 1))
    ((headD 0).comp (snd _ _))
    (fun G P hP ↦ ?_)
    (fun _ ↦ rfl)
  rw [List.mem_singleton.mp hP]
  change (Nat.card (MulAut G.Elem)).size ≤ G.order * G.order + 1
  classical
  have hcard_le : Nat.card (MulAut G.Elem) ≤ G.order ^ G.order := by
    let emb : MulAut G.Elem → (G.Elem → G.Elem) := fun ψ ↦ ψ
    have hinj : Function.Injective emb := fun ψ₁ ψ₂ h ↦ MulEquiv.ext (congrFun h)
    have hc : Fintype.card G.Elem = G.order :=
      (Fintype.card_congr (Equiv.refl (Fin G.order))).trans (Fintype.card_fin G.order)
    rw [Nat.card_eq_fintype_card]
    simpa [Fintype.card_pi, hc] using Fintype.card_le_of_injective emb hinj
  have h1 := Nat.size_le_size hcard_le
  have h2 := Nat.size_pow_le G.order G.order
  have h3 := Nat.size_le_self G.order
  have h4 : G.order * G.order.size ≤ G.order * G.order := Nat.mul_le_mul_left _ h3
  omega

end CslibFrontier.Complexity
