/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction

import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Restricted Exact Cover by 3-Sets (`RX3C`) and NP-Completeness

This module defines **Restricted Exact Cover by 3-Sets**
— exact cover by 3-element subsets on a universe of size `3q` where every element occurs in
exactly 3 sets — and proves `RX3C_npComplete` via a self-contained polynomial-time reduction
from `Cslib.Complexity.PositiveOneInExactThreeSATThree`.
-/

public section

namespace Cslib.Complexity

open Finset Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Definition of `RX3C` and Membership in `NP` -/

/-- An instance `(numElements, sets)` of **Restricted Exact Cover by 3-Sets** (`RX3C`),
representing a universe `X = {0, ..., numElements - 1}` and a list `sets` of triples `(a, b, c)`. -/
@[ext]
structure RX3CInstance where
  /-- Size `|X|` of the universe `{0, ..., numElements - 1}`. -/
  numElements : ℕ
  /-- Collection `C` of 3-element subsets represented as ordered triples `(a, b, c)`. -/
  sets : List (ℕ × (ℕ × ℕ))
  deriving DecidableEq

/-- Binary encoding of a list of triples `(a, b, c)`. -/
abbrev encTripleList : List (ℕ × (ℕ × ℕ)) ↪ List Bool :=
  encList (encPair encNat (encPair encNat encNat))

/-- Binary encoding of `RX3CInstance`. -/
enc_structure encRX3C : RX3CInstance where
  numElements : encNat,
  sets : encTripleList

attribute [fun_prop] encRX3C_numElements_polyTime encRX3C_sets_polyTime encRX3C_mk_polyTime

/-- The 3-element finset corresponding to a triple `(a, b, c)`. -/
@[expose]
def tripleFinset (s : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  {s.1, s.2.1, s.2.2}

/-- Whether `x` is one of the entries of a triple `(a, b, c)`. -/
@[expose]
def memTriple (x : ℕ) (s : ℕ × (ℕ × ℕ)) : Bool :=
  decide (x = s.1) || decide (x = s.2.1) || decide (x = s.2.2)

theorem memTriple_eq_true_iff (x : ℕ) (s : ℕ × (ℕ × ℕ)) :
    memTriple x s = true ↔ x ∈ tripleFinset s := by
  simp [memTriple, tripleFinset, or_assoc]

/-- Number of sets in `sets` containing `x`. -/
@[expose]
def occCount (sets : List (ℕ × (ℕ × ℕ))) (x : ℕ) : ℕ :=
  sets.countP (memTriple x)

/-- Syntactic validity predicate for `RX3C`: `|X| = 3q`, `|C| = |X|`, each triple
consists of 3 distinct elements of `X`, all sets are distinct as 3-element subsets, and every
element of `X` appears in exactly 3 sets.
-/
@[expose]
def IsValidRX3C (x : RX3CInstance) : Prop :=
  x.numElements % 3 = 0 ∧
  x.sets.length = x.numElements ∧
  (∀ s ∈ x.sets, s.1 < x.numElements ∧ s.2.1 < x.numElements ∧ s.2.2 < x.numElements ∧
    s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2) ∧
  (∀ t < x.numElements, occCount x.sets t = 3) ∧
  x.sets.Pairwise (fun s₁ s₂ ↦ tripleFinset s₁ ≠ tripleFinset s₂)

/-- **Restricted Exact Cover by 3-Sets** (`RX3C`, Gonzalez): valid `RX3C` instances
admitting a subcollection `C' ⊆ C` covering every element of `X` exactly once.
-/
@[expose]
def RX3C : Set RX3CInstance :=
  {x | IsValidRX3C x ∧
    ∃ C' : Finset (Fin x.sets.length),
      ∀ t < x.numElements, (C'.filter fun i ↦ t ∈ tripleFinset (x.sets[i.1]'i.2)).card = 1}

/-- Executable syntax guard for `IsValidRX3C`. -/
@[expose]
def isValidRX3CBool (x : RX3CInstance) : Bool :=
  let m := x.sets.length
  decide (x.numElements = m) &&
  decide (m % 3 = 0) &&
  (x.sets.all fun s ↦
    decide (s.1 < m) && decide (s.2.1 < m) && decide (s.2.2 < m) &&
    !decide (s.1 = s.2.1) && !decide (s.1 = s.2.2) && !decide (s.2.1 = s.2.2)) &&
  ((List.range m).all fun t ↦ decide (occCount x.sets t = 3)) &&
  ((List.range m).all fun i ↦ (List.range m).all fun j ↦
    if i < j then
      let s₁ := x.sets.getD i (0, 0, 0)
      let s₂ := x.sets.getD j (0, 0, 0)
      !(memTriple s₁.1 s₂ && memTriple s₁.2.1 s₂ && memTriple s₁.2.2 s₂)
    else true)

private theorem distinct_tripleFinset_iff_not_mem (s₁ s₂ : ℕ × (ℕ × ℕ))
    (h1 : s₁.1 ≠ s₁.2.1 ∧ s₁.1 ≠ s₁.2.2 ∧ s₁.2.1 ≠ s₁.2.2)
    (h2 : s₂.1 ≠ s₂.2.1 ∧ s₂.1 ≠ s₂.2.2 ∧ s₂.2.1 ≠ s₂.2.2) :
    tripleFinset s₁ ≠ tripleFinset s₂ ↔
      ¬ (memTriple s₁.1 s₂ = true ∧ memTriple s₁.2.1 s₂ = true ∧ memTriple s₁.2.2 s₂ = true) := by
  have hc1 : (tripleFinset s₁).card = 3 := by
    unfold tripleFinset
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h1.2.2]
    · simp [h1.1, h1.2.1]
  have hc2 : (tripleFinset s₂).card = 3 := by
    unfold tripleFinset
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h2.2.2]
    · simp [h2.1, h2.2.1]
  simp only [memTriple_eq_true_iff]
  constructor
  · intro hne ⟨ha, hb, hc⟩
    apply hne
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hc1, hc2])
    intro z hz
    simp only [tripleFinset, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · intro hnot hEq
    apply hnot
    rw [← hEq]
    exact ⟨by simp [tripleFinset], by simp [tripleFinset], by simp [tripleFinset]⟩

theorem isValidRX3CBool_eq_true_iff (x : RX3CInstance) :
    isValidRX3CBool x = true ↔ IsValidRX3C x := by
  unfold isValidRX3CBool IsValidRX3C
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨hnm, hmod⟩, hsets⟩, hocc⟩, hpair⟩
    refine ⟨by omega, hnm.symm, ?_, ?_, ?_⟩
    · intro s hs
      have h := hsets s hs
      exact ⟨by omega, by omega, by omega, h.1.1.2, h.1.2, h.2⟩
    · intro t ht
      exact hocc t (by omega)
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hp := hpair i hi j hj
      simp only [hij, ↓reduceIte] at hp
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hp
      have h1 := hsets _ (List.getElem_mem hi)
      have h2 := hsets _ (List.getElem_mem hj)
      refine (distinct_tripleFinset_iff_not_mem _ _ ⟨h1.1.1.2, h1.1.2, h1.2⟩
        ⟨h2.1.1.2, h2.1.2, h2.2⟩).mpr ?_
      intro ⟨a, b, c⟩
      simp [a, b, c] at hp
  · rintro ⟨hmod, hlen, hsets, hocc, hpair⟩
    refine ⟨⟨⟨⟨hlen.symm, by omega⟩, fun s hs ↦ ?_⟩, fun t ht ↦ hocc t (by omega)⟩, ?_⟩
    · have h := hsets s hs
      exact ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, h.2.2.2.1⟩, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩
    · intro i hi j hj
      split_ifs with hij
      · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
        have hne : tripleFinset x.sets[i] ≠ tripleFinset x.sets[j] :=
          (List.pairwise_iff_getElem.mp hpair) i j hi hj hij
        have h1 := hsets _ (List.getElem_mem hi)
        have h2 := hsets _ (List.getElem_mem hj)
        have hnot := (distinct_tripleFinset_iff_not_mem _ _ ⟨h1.2.2.2.1, h1.2.2.2.2.1,
          h1.2.2.2.2.2⟩ ⟨h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2⟩).mp hne
        by_contra hbad
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hbad
        exact hnot ⟨hbad.1.1, hbad.1.2, hbad.2⟩
      · rfl

section PolyTimeRX3C

attribute [local irreducible] encRX3C encCNF encNat encUnary

private theorem computableInPolyTime_isValidRX3CBool :
    ComputableInPolyTime isValidRX3CBool encRX3C encBool := by
  have hN : ComputableInPolyTime RX3CInstance.numElements encRX3C encNat :=
    encRX3C_numElements_polyTime id'
  have hS : ComputableInPolyTime RX3CInstance.sets encRX3C
      (encList (encPair encNat (encPair encNat encNat))) :=
    encRX3C_sets_polyTime id'
  have hm_u : ComputableInPolyTime (fun x : RX3CInstance ↦ x.sets.length) encRX3C encUnary :=
    (length_list _).comp hS
  have hm_b : ComputableInPolyTime (fun x : RX3CInstance ↦ x.sets.length) encRX3C encNat :=
    unary_to_binary.comp hm_u
  have h1 : ComputableInPolyTime (fun x : RX3CInstance ↦ decide (x.numElements = x.sets.length))
      encRX3C encBool := hN.decide_eq' hm_b
  have h2 : ComputableInPolyTime (fun x : RX3CInstance ↦ decide (x.sets.length % 3 = 0))
      encRX3C encBool := (unary_mod' hm_u (const 3)).decide_eq' (const 0)
  have h3 : ComputableInPolyTime
      (fun x : RX3CInstance ↦ x.sets.all fun s ↦
        decide (s.1 < x.sets.length) && decide (s.2.1 < x.sets.length) &&
        decide (s.2.2 < x.sets.length) && !decide (s.1 = s.2.1) && !decide (s.1 = s.2.2) &&
        !decide (s.2.1 = s.2.2)) encRX3C encBool := by
    refine allWithInput hS ?_
    have hmb' : ComputableInPolyTime
        (fun p : RX3CInstance × (ℕ × (ℕ × ℕ)) ↦ p.1.sets.length)
        (encPair encRX3C (encPair encNat (encPair encNat encNat))) encNat :=
      hm_b.comp (fst _ _)
    have hs1 : ComputableInPolyTime (fun p : RX3CInstance × (ℕ × (ℕ × ℕ)) ↦ p.2.1)
        (encPair encRX3C (encPair encNat (encPair encNat encNat))) encNat := by fun_prop
    have hs2 : ComputableInPolyTime (fun p : RX3CInstance × (ℕ × (ℕ × ℕ)) ↦ p.2.2.1)
        (encPair encRX3C (encPair encNat (encPair encNat encNat))) encNat := by fun_prop
    have hs3 : ComputableInPolyTime (fun p : RX3CInstance × (ℕ × (ℕ × ℕ)) ↦ p.2.2.2)
        (encPair encRX3C (encPair encNat (encPair encNat encNat))) encNat := by fun_prop
    exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
      (binary_lt' hs1 hmb') (binary_lt' hs2 hmb')) (binary_lt' hs3 hmb'))
      (bool_not.comp (hs1.decide_eq' hs2)))
      (bool_not.comp (hs1.decide_eq' hs3)))
      (bool_not.comp (hs2.decide_eq' hs3))
  have hrange : ComputableInPolyTime (fun x : RX3CInstance ↦ List.range x.sets.length)
      encRX3C (encList encUnary) := ComputableInPolyTime.range.comp hm_u
  have h4 : ComputableInPolyTime
      (fun x : RX3CInstance ↦ (List.range x.sets.length).all fun t ↦ decide (occCount x.sets t = 3))
      encRX3C encBool := by
    refine allWithInput hrange ?_
    have hocc : ComputableInPolyTime
        (fun p : RX3CInstance × ℕ ↦ occCount p.1.sets p.2)
        (encPair encRX3C encUnary) encUnary := by
      unfold occCount memTriple
      refine countPWithInput (hS.comp (fst _ _)) ?_
      have hx : ComputableInPolyTime
          (fun q : (RX3CInstance × ℕ) × (ℕ × (ℕ × ℕ)) ↦ q.1.2)
          (encPair (encPair encRX3C encUnary) (encPair encNat (encPair encNat encNat)))
          encNat := unary_to_binary.comp (by fun_prop)
      have ha : ComputableInPolyTime
          (fun q : (RX3CInstance × ℕ) × (ℕ × (ℕ × ℕ)) ↦ q.2.1)
          (encPair (encPair encRX3C encUnary) (encPair encNat (encPair encNat encNat)))
          encNat := by fun_prop
      have hb : ComputableInPolyTime
          (fun q : (RX3CInstance × ℕ) × (ℕ × (ℕ × ℕ)) ↦ q.2.2.1)
          (encPair (encPair encRX3C encUnary) (encPair encNat (encPair encNat encNat)))
          encNat := by fun_prop
      have hc : ComputableInPolyTime
          (fun q : (RX3CInstance × ℕ) × (ℕ × (ℕ × ℕ)) ↦ q.2.2.2)
          (encPair (encPair encRX3C encUnary) (encPair encNat (encPair encNat encNat)))
          encNat := by fun_prop
      exact bool_or' (bool_or' (hx.decide_eq' ha) (hx.decide_eq' hb)) (hx.decide_eq' hc)
    exact hocc.decide_eq' (const 3)
  have h5 : ComputableInPolyTime
      (fun x : RX3CInstance ↦ (List.range x.sets.length).all fun i ↦
        (List.range x.sets.length).all fun j ↦
          if i < j then
            let s₁ := x.sets.getD i (0, 0, 0)
            let s₂ := x.sets.getD j (0, 0, 0)
            !(memTriple s₁.1 s₂ && memTriple s₁.2.1 s₂ && memTriple s₁.2.2 s₂)
          else true) encRX3C encBool := by
    refine allWithInput hrange ?_
    refine allWithInput (hrange.comp (fst _ _)) ?_
    let encQ := encPair (encPair encRX3C encUnary) encUnary
    have hi : ComputableInPolyTime (fun q : (RX3CInstance × ℕ) × ℕ ↦ q.1.2) encQ encUnary := by
      fun_prop
    have hj : ComputableInPolyTime (fun q : (RX3CInstance × ℕ) × ℕ ↦ q.2) encQ encUnary := by
      fun_prop
    have hSq : ComputableInPolyTime (fun q : (RX3CInstance × ℕ) × ℕ ↦ q.1.1.sets) encQ
        (encList (encPair encNat (encPair encNat encNat))) := hS.comp ((fst _ _).comp (fst _ _))
    have hs1 : ComputableInPolyTime
        (fun q : (RX3CInstance × ℕ) × ℕ ↦ q.1.1.sets.getD q.1.2 (0, 0, 0))
        encQ (encPair encNat (encPair encNat encNat)) := listGetDWithInput hSq hi (0, 0, 0)
    have hs2 : ComputableInPolyTime
        (fun q : (RX3CInstance × ℕ) × ℕ ↦ q.1.1.sets.getD q.2 (0, 0, 0))
        encQ (encPair encNat (encPair encNat encNat)) := listGetDWithInput hSq hj (0, 0, 0)
    have hmt : ∀ (f : (RX3CInstance × ℕ) × ℕ → ℕ),
        ComputableInPolyTime f encQ encNat →
        ComputableInPolyTime (fun q ↦ memTriple (f q) (q.1.1.sets.getD q.2 (0, 0, 0)))
          encQ encBool := fun f hf ↦ by
      unfold memTriple
      exact bool_or' (bool_or' (hf.decide_eq' ((fst _ _).comp hs2))
        (hf.decide_eq' ((fst _ _).comp ((snd _ _).comp hs2))))
        (hf.decide_eq' ((snd _ _).comp ((snd _ _).comp hs2)))
    have hcond : ComputableInPolyTime
        (fun q : (RX3CInstance × ℕ) × ℕ ↦
          !(memTriple (q.1.1.sets.getD q.1.2 (0, 0, 0)).1 (q.1.1.sets.getD q.2 (0, 0, 0)) &&
            memTriple (q.1.1.sets.getD q.1.2 (0, 0, 0)).2.1 (q.1.1.sets.getD q.2 (0, 0, 0)) &&
            memTriple (q.1.1.sets.getD q.1.2 (0, 0, 0)).2.2 (q.1.1.sets.getD q.2 (0, 0, 0))))
        encQ encBool :=
      bool_not.comp (bool_and' (bool_and'
        (hmt _ ((fst _ _).comp hs1)) (hmt _ ((fst _ _).comp ((snd _ _).comp hs1))))
        (hmt _ ((snd _ _).comp ((snd _ _).comp hs1))))
    exact ((unary_lt' hi hj).ite hcond (const true)).of_enc_eq fun _ ↦ by congr 1; simp
  unfold isValidRX3CBool
  exact (bool_and' (bool_and' (bool_and' (bool_and' h1 h2) h3) h4) h5).of_enc_eq
    fun _ ↦ by congr 1

theorem RX3C_mem_NP : RX3C ∈ NP encRX3C := by
  let check : RX3CInstance × List Bool → Bool := fun p ↦
    let x := p.1
    let w := p.2
    let m := x.sets.length
    isValidRX3CBool x &&
    (List.range m).all fun t ↦
      decide (((List.range m).countP fun i ↦
        w.getD i false && memTriple t (x.sets.getD i (0, 0, 0))) = 1)
  have hcheck : ComputableInPolyTime check (encPair encRX3C encBits) encBool := by
    have hX : ComputableInPolyTime (fun p : RX3CInstance × List Bool ↦ p.1)
        (encPair encRX3C encBits) encRX3C := fst _ _
    have hS : ComputableInPolyTime (fun p : RX3CInstance × List Bool ↦ p.1.sets)
        (encPair encRX3C encBits) (encList (encPair encNat (encPair encNat encNat))) :=
      (encRX3C_sets_polyTime id').comp hX
    have hm : ComputableInPolyTime (fun p : RX3CInstance × List Bool ↦ p.1.sets.length)
        (encPair encRX3C encBits) encUnary := (length_list _).comp hS
    have hrange : ComputableInPolyTime
        (fun p : RX3CInstance × List Bool ↦ List.range p.1.sets.length)
        (encPair encRX3C encBits) (encList encUnary) := ComputableInPolyTime.range.comp hm
    have hvalid := computableInPolyTime_isValidRX3CBool.comp hX
    have hcov : ComputableInPolyTime
        (fun p : RX3CInstance × List Bool ↦
          (List.range p.1.sets.length).all fun t ↦
            decide (((List.range p.1.sets.length).countP fun i ↦
              p.2.getD i false && memTriple t (p.1.sets.getD i (0, 0, 0))) = 1))
        (encPair encRX3C encBits) encBool := by
      refine allWithInput hrange ?_
      have hcnt : ComputableInPolyTime
          (fun q : (RX3CInstance × List Bool) × ℕ ↦
            (List.range q.1.1.sets.length).countP fun i ↦
              q.1.2.getD i false && memTriple q.2 (q.1.1.sets.getD i (0, 0, 0)))
          (encPair (encPair encRX3C encBits) encUnary) encUnary := by
        refine countPWithInput (hrange.comp (fst _ _)) ?_
        let encR := encPair (encPair (encPair encRX3C encBits) encUnary) encUnary
        have hbit : ComputableInPolyTime
            (fun r : ((RX3CInstance × List Bool) × ℕ) × ℕ ↦ r.1.1.2.getD r.2 false)
            encR encBool :=
          listGetDWithInput (bitsToList.comp ((snd encRX3C encBits).comp
            ((fst _ _).comp (fst _ _)))) (snd _ _) false
        have hset : ComputableInPolyTime
            (fun r : ((RX3CInstance × List Bool) × ℕ) × ℕ ↦ r.1.1.1.sets.getD r.2 (0, 0, 0))
            encR (encPair encNat (encPair encNat encNat)) :=
          listGetDWithInput (hS.comp ((fst _ _).comp (fst _ _))) (snd _ _) (0, 0, 0)
        have ht : ComputableInPolyTime
            (fun r : ((RX3CInstance × List Bool) × ℕ) × ℕ ↦ r.1.2) encR encNat :=
          unary_to_binary.comp (by fun_prop)
        have hmem : ComputableInPolyTime
            (fun r : ((RX3CInstance × List Bool) × ℕ) × ℕ ↦
              memTriple r.1.2 (r.1.1.1.sets.getD r.2 (0, 0, 0))) encR encBool := by
          unfold memTriple
          exact bool_or' (bool_or' (ht.decide_eq' ((fst _ _).comp hset))
            (ht.decide_eq' ((fst _ _).comp ((snd _ _).comp hset))))
            (ht.decide_eq' ((snd _ _).comp ((snd _ _).comp hset)))
        exact bool_and' hbit hmem
      exact hcnt.decide_eq' (const 1)
    unfold check
    exact bool_and' hvalid hcov
  refine mem_NP.mpr ⟨Polynomial.X, check, hcheck, fun x ↦ ?_⟩
  simp only [Polynomial.eval_X, check, Bool.and_eq_true, isValidRX3CBool_eq_true_iff,
    List.all_eq_true, List.mem_range, decide_eq_true_eq, RX3C, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hvalid, C', hC'⟩
    have hm_le : x.sets.length ≤ (encRX3C x).length := by
      have h1 : x.sets.length ≤ (encList (encPair encNat (encPair encNat encNat)) x.sets).length :=
        length_le_length_encList _ _
      have h2 : (encList (encPair encNat (encPair encNat encNat)) x.sets).length ≤
          (encRX3C x).length := by enc_len [encRX3C_apply, encRX3CFields, encTripleList]
      omega
    let w0 : List Bool := (List.range x.sets.length).map fun i ↦
      if hi : i < x.sets.length then decide ((⟨i, hi⟩ : Fin x.sets.length) ∈ C') else false
    let pad := (encRX3C x).length - x.sets.length
    refine ⟨w0 ++ List.replicate pad false,
      by simp only [w0, pad, List.length_append, List.length_map, List.length_range,
        List.length_replicate]; omega,
      hvalid, fun t ht ↦ ?_⟩
    have htN : t < x.numElements := by rw [← hvalid.2.1]; exact ht
    have hcount : ((List.range x.sets.length).countP fun i ↦
        (w0 ++ List.replicate pad false).getD i false && memTriple t (x.sets.getD i (0, 0, 0))) =
        (C'.filter fun i : Fin x.sets.length ↦ t ∈ tripleFinset (x.sets[i.1]'i.2)).card := by
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      refine Finset.card_bij (fun i hi ↦ ⟨i, List.mem_range.mp (List.mem_filter.mp
        (List.mem_toFinset.mp hi)).1⟩) ?_ (fun _ _ _ _ h ↦ congrArg Fin.val h) ?_
      · intro i hi
        have hf := List.mem_filter.mp (List.mem_toFinset.mp hi)
        have hilt : i < x.sets.length := List.mem_range.mp hf.1
        have hget : (w0 ++ List.replicate pad false).getD i false =
            decide ((⟨i, hilt⟩ : Fin x.sets.length) ∈ C') := by
          have hiw : i < w0.length := by simp [w0, hilt]
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
            List.getElem_append_left hiw]
          simp [w0, hilt]
        simp only [Bool.and_eq_true, hget, decide_eq_true_eq,
          List.getD_eq_getElem _ _ hilt, memTriple_eq_true_iff] at hf
        exact Finset.mem_filter.mpr hf.2
      · intro j hj
        have hjf := Finset.mem_filter.mp hj
        refine ⟨j.1, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr j.2, ?_⟩),
          rfl⟩
        have hget : (w0 ++ List.replicate pad false).getD j.1 false =
            decide (j ∈ C') := by
          have hjw : j.1 < w0.length := by simp [w0, j.2]
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
            List.getElem_append_left hjw]
          simp [w0, j.2]
        rw [hget, List.getD_eq_getElem _ _ j.2]
        simp [hjf.1, memTriple_eq_true_iff, hjf.2]
    rw [hcount, hC' t htN]
  · rintro ⟨w, _, hvalid, hcov⟩
    refine ⟨hvalid, Finset.univ.filter fun i : Fin x.sets.length ↦ w.getD i.1 false = true, ?_⟩
    intro t ht
    have htm : t < x.sets.length := by rw [hvalid.2.1]; exact ht
    have hcount : ((Finset.univ.filter fun i : Fin x.sets.length ↦ w.getD i.1 false = true).filter
        fun i ↦ t ∈ tripleFinset (x.sets[i.1]'i.2)).card =
        ((List.range x.sets.length).countP fun i ↦
          w.getD i false && memTriple t (x.sets.getD i (0, 0, 0))) := by
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      symm
      refine Finset.card_bij (fun i hi ↦ ⟨i, List.mem_range.mp (List.mem_filter.mp
        (List.mem_toFinset.mp hi)).1⟩) ?_ (fun _ _ _ _ h ↦ congrArg Fin.val h) ?_
      · intro i hi
        have hf := List.mem_filter.mp (List.mem_toFinset.mp hi)
        have hilt : i < x.sets.length := List.mem_range.mp hf.1
        simp only [Bool.and_eq_true, List.getD_eq_getElem _ _ hilt, memTriple_eq_true_iff] at hf
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.2.1⟩, hf.2.2⟩
      · intro j hj
        have hjf := Finset.mem_filter.mp hj
        have hjw := (Finset.mem_filter.mp hjf.1).2
        refine ⟨j.1, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr j.2, ?_⟩),
          rfl⟩
        rw [hjw, List.getD_eq_getElem _ _ j.2]
        simp [memTriple_eq_true_iff, hjf.2]
    rw [hcount, hcov t htm]

end PolyTimeRX3C

/-! ### 2. Polynomial-Time Reduction `PositiveOneInExactThreeSATThree → RX3C` -/

section RX3CReduction

/-- Clause indices `j < φ.length` in which variable `v` appears. -/
@[expose]
def clauseIndices (φ : CNF ℕ) (v : ℕ) : List ℕ :=
  (List.range φ.length).filter fun j ↦ ((φ.getD j []).map Prod.fst).contains v

/-- Number of dummy elements allocated to variable `v` (`9` if `v` appears in 3 clauses,
`6` otherwise). -/
@[expose]
def varDummyCount (φ : CNF ℕ) (v : ℕ) : ℕ :=
  if (clauseIndices φ v).length = 3 then 9 else 6

/-- Starting dummy element index for the `i`-th distinct variable of `φ`. -/
@[expose]
def varDummyBase (φ : CNF ℕ) (V : List ℕ) (i : ℕ) : ℕ :=
  3 * φ.length + ((V.take i).map (varDummyCount φ)).sum

/-- Sets generated by the gadget for variable `v` with dummy base `b` (`deg(v) ∈ {1, 2, 3}`). -/
@[expose]
def varGadgetSets (φ : CNF ℕ) (v b : ℕ) : List (ℕ × (ℕ × ℕ)) :=
  let cs := clauseIndices φ v
  let j₁ := cs.getD 0 0
  let j₂ := cs.getD 1 0
  let j₃ := cs.getD 2 0
  if cs.length = 1 then
    [(3 * j₁ + 0, b + 0, b + 3), (3 * j₁ + 1, b + 1, b + 4), (3 * j₁ + 2, b + 2, b + 5),
     (b + 0, b + 1, b + 2), (b + 3, b + 4, b + 5), (b + 0, b + 1, b + 5), (b + 2, b + 3, b + 4)]
  else if cs.length = 2 then
    [(3 * j₁ + 0, 3 * j₂ + 0, b + 0), (3 * j₁ + 1, 3 * j₂ + 1, b + 1),
     (3 * j₁ + 2, 3 * j₂ + 2, b + 2),
     (b + 0, b + 1, b + 2), (b + 3, b + 4, b + 5), (b + 0, b + 3, b + 4),
     (b + 1, b + 4, b + 5), (b + 2, b + 5, b + 3)]
  else
    [(3 * j₁ + 0, 3 * j₂ + 0, b + 0), (3 * j₁ + 1, 3 * j₂ + 1, b + 1),
     (3 * j₁ + 2, 3 * j₂ + 2, b + 2),
     (3 * j₃ + 0, b + 3, b + 6), (3 * j₃ + 1, b + 4, b + 7), (3 * j₃ + 2, b + 5, b + 8),
     (b + 0, b + 3, b + 6), (b + 1, b + 4, b + 7), (b + 2, b + 5, b + 8),
     (b + 0, b + 4, b + 8), (b + 1, b + 5, b + 6), (b + 2, b + 3, b + 7)]

/-- Fixed NO-instance of `RX3C` (`IsValidRX3C` fails since `numElements = 1`). -/
@[expose]
def rx3cNoInst : RX3CInstance := ⟨1, []⟩

/-- Fixed YES-instance of `RX3C` (empty universe and empty collection). -/
@[expose]
def rx3cYesInst : RX3CInstance := ⟨0, []⟩

/-- Polynomial-time reduction from `PositiveOneInExactThreeSATThree` to `RX3C`. -/
@[expose]
def toRX3C (φ : CNF ℕ) : RX3CInstance :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    let V := φ.distinctVars
    let numEl := 3 * φ.length + (V.map (varDummyCount φ)).sum
    let sets := (List.range V.length).flatMap fun i ↦
      varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)
    ⟨numEl, sets⟩
  else rx3cNoInst

theorem rx3cNoInst_not_mem : rx3cNoInst ∉ RX3C := by
  intro ⟨hvalid, _⟩
  have := hvalid.1
  simp [rx3cNoInst] at this

private theorem varDummyBase_succ (φ : CNF ℕ) (V : List ℕ) (i : ℕ) (hi : i < V.length) :
    varDummyBase φ V (i + 1) = varDummyBase φ V i + varDummyCount φ (V[i]'hi) := by
  unfold varDummyBase
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]
  omega

private theorem varDummyBase_mono (φ : CNF ℕ) (V : List ℕ) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ V.length) :
    varDummyBase φ V i ≤ varDummyBase φ V j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    by_cases h : i ≤ k
    · exact (ih h (by omega)).trans (by rw [varDummyBase_succ φ V k (by omega)]; omega)
    · have : i = k + 1 := by omega
      subst this; exact le_rfl

theorem varDummyBase_add_le (φ : CNF ℕ) (V : List ℕ) {i j : ℕ} (hij : i < j)
    (hj : j ≤ V.length) :
    varDummyBase φ V i + varDummyCount φ (V[i]'(by omega)) ≤ varDummyBase φ V j := by
  rw [← varDummyBase_succ φ V i (by omega)]
  exact varDummyBase_mono φ V (by omega) hj

theorem varDummyBase_end (φ : CNF ℕ) (V : List ℕ) :
    varDummyBase φ V V.length = 3 * φ.length + (V.map (varDummyCount φ)).sum := by
  simp [varDummyBase]

theorem clauseIndices_length_eq_count (φ : CNF ℕ)
    (hex : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) (v : ℕ) :
    (clauseIndices φ v).length = φ.vars.count v := by
  unfold clauseIndices CNF.vars
  have h1 : ((List.range φ.length).filter fun j ↦ ((φ.getD j []).map Prod.fst).contains v).length =
      (List.range φ.length).countP fun j ↦ ((φ.getD j []).map Prod.fst).contains v := by
    rw [List.countP_eq_length_filter]
  rw [h1]
  have h2 : (φ.flatten.map Prod.fst).count v =
      (φ.map fun c ↦ (c.map Prod.fst).count v).sum := by
    clear h1 hex
    induction φ with
    | nil => simp
    | cons c cs ih =>
      simp only [List.flatten_cons, List.map_append, List.count_append, List.map_cons,
        List.sum_cons, ih]
  rw [h2]
  have h3 : ∀ j (hj : j < φ.length), (φ[j].map Prod.fst).count v =
      if ((φ.getD j []).map Prod.fst).contains v then 1 else 0 := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    have hnd := (hex _ (List.getElem_mem hj)).2
    by_cases hm : v ∈ φ[j].map Prod.fst
    · simp [List.Nodup.count hnd, hm]
    · simp [hm, List.count_eq_zero.mpr hm]
  have hmap : φ.map (fun c ↦ (c.map Prod.fst).count v) =
      (List.range φ.length).map fun j ↦
        if ((φ.getD j []).map Prod.fst).contains v then 1 else 0 := by
    refine List.ext_getElem (by simp) fun j hj1 hj2 ↦ ?_
    simp only [List.length_map, List.length_range] at hj1 hj2
    simp only [List.getElem_map, List.getElem_range]
    exact h3 j hj1
  rw [hmap]
  clear h1 h2 h3 hmap hex
  induction (List.range φ.length) with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
    cases ((φ.getD a []).map Prod.fst).contains v <;> simp [Nat.add_comm]

theorem mem_clauseIndices_iff (φ : CNF ℕ) (v j : ℕ) :
    j ∈ clauseIndices φ v ↔ j < φ.length ∧ v ∈ (φ.getD j []).map Prod.fst := by
  simp [clauseIndices]

private theorem nodup_clauseIndices (φ : CNF ℕ) (v : ℕ) : (clauseIndices φ v).Nodup :=
  List.nodup_range.filter _

theorem clauseIndices_length_pos_of_mem_distinctVars (φ : CNF ℕ)
    (hex : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup)
    {v : ℕ} (hv : v ∈ φ.distinctVars) :
    1 ≤ (clauseIndices φ v).length := by
  rw [clauseIndices_length_eq_count φ hex v]
  have hv' : v ∈ φ.vars := CNF.mem_distinctVars.mp hv
  exact Nat.pos_of_ne_zero (mt List.count_eq_zero.mp (not_not.mpr hv'))

theorem varGadgetSets_length (φ : CNF ℕ) (v b : ℕ)
    (h1 : 1 ≤ (clauseIndices φ v).length) (h3 : (clauseIndices φ v).length ≤ 3) :
    (varGadgetSets φ v b).length = (clauseIndices φ v).length + varDummyCount φ v := by
  unfold varGadgetSets varDummyCount
  have hc : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hc with h | h | h <;> simp [h]

private theorem sum_length_clauseIndices_eq (φ : CNF ℕ)
    (hex : ∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) :
    (φ.distinctVars.map fun v ↦ (clauseIndices φ v).length).sum = 3 * φ.length := by
  have h1 : (φ.distinctVars.map fun v ↦ (clauseIndices φ v).length).sum =
      (φ.distinctVars.map fun v ↦ φ.vars.count v).sum := by
    congr 1; exact List.map_congr_left fun v _ ↦ clauseIndices_length_eq_count φ hex v
  rw [h1]
  have hsum : (φ.distinctVars.map fun v ↦ φ.vars.count v).sum = φ.vars.length := by
    have hnd : φ.distinctVars.Nodup := CNF.nodup_distinctVars φ
    have hmem : ∀ v, v ∈ φ.vars ↔ v ∈ φ.distinctVars := fun v ↦ CNF.mem_distinctVars.symm
    have hperm : ∀ (l : List ℕ) (d : List ℕ), d.Nodup → (∀ x ∈ l, x ∈ d) →
        (d.map fun x ↦ l.count x).sum = l.length := by
      intro l d hd hsub
      induction d generalizing l with
      | nil =>
        cases l with
        | nil => simp
        | cons a _ => exact (List.not_mem_nil (hsub a List.mem_cons_self)).elim
      | cons a ds ih =>
        rw [List.nodup_cons] at hd
        simp only [List.map_cons, List.sum_cons]
        have hpart : l.length = l.count a + (l.filter fun x ↦ x != a).length := by
          rw [← List.countP_eq_length_filter, List.count_eq_countP]
          have hfn : (fun x : ℕ ↦ x != a) = (fun x ↦ !(x == a)) := rfl
          rw [hfn]
          exact @List.length_eq_countP_add_countP _ (fun x ↦ x == a) l
        have hfilt : ∀ x ∈ ds, (l.filter fun y ↦ y != a).count x = l.count x := by
          intro x hx
          have hxa : x ≠ a := fun h ↦ hd.1 (h ▸ hx)
          rw [List.count_eq_countP, List.count_eq_countP, List.countP_filter]
          congr 1; funext y
          by_cases hya : y = a <;> by_cases hyx : y = x <;> simp_all [_root_.bne]
        have hsub' : ∀ x ∈ l.filter (fun y ↦ y != a), x ∈ ds := by
          intro x hx
          have hxf := List.mem_filter.mp hx
          have hxa : x ≠ a := by simpa [_root_.bne] using hxf.2
          exact (List.mem_cons.mp (hsub x hxf.1)).resolve_left hxa
        have hih := ih (l.filter fun y ↦ y != a) hd.2 hsub'
        have hmap_eq : ds.map (fun x ↦ l.count x) =
            ds.map (fun x ↦ (l.filter fun y ↦ y != a).count x) :=
          List.map_congr_left fun x hx ↦ (hfilt x hx).symm
        rw [hmap_eq, hih, ← hpart]
    exact hperm φ.vars φ.distinctVars hnd (fun v hv ↦ CNF.mem_distinctVars.mpr hv)
  rw [hsum]
  unfold CNF.vars
  have hlen : (φ.flatten.map Prod.fst).length = 3 * φ.length := by
    clear h1 hsum
    induction φ with
    | nil => simp
    | cons c cs ih =>
      simp only [List.flatten_cons, List.map_append, List.length_append, List.length_cons]
      rw [List.length_map, (hex c List.mem_cons_self).1,
        ih (fun d hd ↦ hex d (List.mem_cons_of_mem c hd))]
      omega
  exact hlen

theorem varDummyBase_ge (φ : CNF ℕ) (V : List ℕ) (i : ℕ) :
    3 * φ.length ≤ varDummyBase φ V i := by
  unfold varDummyBase; omega

theorem clauseIndices_getD_lt (φ : CNF ℕ) (v i : ℕ)
    (hi : i < (clauseIndices φ v).length) :
    (clauseIndices φ v).getD i 0 < φ.length := by
  rw [List.getD_eq_getElem _ _ hi]
  exact ((mem_clauseIndices_iff φ v _).mp (List.getElem_mem hi)).1

theorem clauseIndices_getD_ne (φ : CNF ℕ) (v i j : ℕ)
    (hi : i < (clauseIndices φ v).length) (hj : j < (clauseIndices φ v).length) (hij : i ≠ j) :
    (clauseIndices φ v).getD i 0 ≠ (clauseIndices φ v).getD j 0 := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact (List.Nodup.getElem_inj_iff (nodup_clauseIndices φ v)).not.mpr hij

private theorem occCount_nil (t : ℕ) : occCount [] t = 0 := rfl

private theorem occCount_cons (a b c : ℕ) (l : List (ℕ × (ℕ × ℕ))) (t : ℕ) :
    occCount ((a, b, c) :: l) t = (if t = a ∨ t = b ∨ t = c then 1 else 0) + occCount l t := by
  unfold occCount memTriple
  rw [List.countP_cons]
  by_cases h : t = a ∨ t = b ∨ t = c
  · rcases h with rfl | rfl | rfl <;> simp [Nat.add_comm]
  · push Not at h; simp [h.1, h.2.1, h.2.2]

private theorem occCount_cons_fst_lt {a b c t : ℕ} {l : List (ℕ × (ℕ × ℕ))} (ha : a < t) :
    occCount ((a, b, c) :: l) t = (if t = b ∨ t = c then 1 else 0) + occCount l t := by
  rw [occCount_cons]; simp [show t ≠ a by omega]

private theorem occCount_cons_fst_snd_lt {a b c t : ℕ} {l : List (ℕ × (ℕ × ℕ))}
    (ha : a < t) (hb : b < t) :
    occCount ((a, b, c) :: l) t = (if t = c then 1 else 0) + occCount l t := by
  rw [occCount_cons]; simp [show t ≠ a by omega, show t ≠ b by omega]

private theorem occCount_cons_snd_thd_gt {a b c t : ℕ} {l : List (ℕ × (ℕ × ℕ))}
    (hb : t < b) (hc : t < c) :
    occCount ((a, b, c) :: l) t = (if t = a then 1 else 0) + occCount l t := by
  rw [occCount_cons]; simp [show t ≠ b by omega, show t ≠ c by omega]

private theorem occCount_cons_thd_gt {a b c t : ℕ} {l : List (ℕ × (ℕ × ℕ))} (hc : t < c) :
    occCount ((a, b, c) :: l) t = (if t = a ∨ t = b then 1 else 0) + occCount l t := by
  rw [occCount_cons]; simp [show t ≠ c by omega]

private theorem occCount_cons_all_gt {a b c t : ℕ} {l : List (ℕ × (ℕ × ℕ))}
    (ha : t < a) (hb : t < b) (hc : t < c) :
    occCount ((a, b, c) :: l) t = occCount l t := by
  rw [occCount_cons]; simp [show t ≠ a by omega, show t ≠ b by omega, show t ≠ c by omega]

private theorem occCount_flatMap {α : Type*} (l : List α) (f : α → List (ℕ × (ℕ × ℕ))) (t : ℕ) :
    occCount (l.flatMap f) t = (l.map fun x ↦ occCount (f x) t).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [occCount, List.flatMap_cons, List.countP_append, List.map_cons, List.sum_cons, ← ih]
    rfl

/-- Count of occurrences of a dummy element `t ∈ [b, b + varDummyCount φ v)` inside
`varGadgetSets`. -/
private theorem occCount_varGadgetSets_dummy (φ : CNF ℕ) (v b t : ℕ)
    (hb : 3 * φ.length ≤ b) (h1 : 1 ≤ (clauseIndices φ v).length)
    (h3 : (clauseIndices φ v).length ≤ 3) (hge : b ≤ t) (hlt : t < b + varDummyCount φ v) :
    occCount (varGadgetSets φ v b) t = 3 := by
  unfold varGadgetSets
  unfold varDummyCount at hlt
  have hcases : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hcases with h | h | h
  · simp only [h, ↓reduceIte, show (1 : ℕ) ≠ 3 by omega] at hlt ⊢
    have hj1 : (clauseIndices φ v).getD 0 0 < φ.length := clauseIndices_getD_lt φ v 0 (by omega)
    rw [occCount_cons_fst_lt (by omega), occCount_cons_fst_lt (by omega),
      occCount_cons_fst_lt (by omega), occCount_cons, occCount_cons, occCount_cons,
      occCount_cons, occCount_nil]
    have ht : t = b ∨ t = b + 1 ∨ t = b + 2 ∨ t = b + 3 ∨ t = b + 4 ∨ t = b + 5 := by omega
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [h, ↓reduceIte, show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ 3 by omega] at hlt ⊢
    have hj1 : (clauseIndices φ v).getD 0 0 < φ.length := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 : (clauseIndices φ v).getD 1 0 < φ.length := clauseIndices_getD_lt φ v 1 (by omega)
    rw [occCount_cons_fst_snd_lt (by omega) (by omega),
      occCount_cons_fst_snd_lt (by omega) (by omega),
      occCount_cons_fst_snd_lt (by omega) (by omega),
      occCount_cons, occCount_cons, occCount_cons, occCount_cons, occCount_cons, occCount_nil]
    have ht : t = b ∨ t = b + 1 ∨ t = b + 2 ∨ t = b + 3 ∨ t = b + 4 ∨ t = b + 5 := by omega
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [h, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega] at hlt ⊢
    have hj1 : (clauseIndices φ v).getD 0 0 < φ.length := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 : (clauseIndices φ v).getD 1 0 < φ.length := clauseIndices_getD_lt φ v 1 (by omega)
    have hj3 : (clauseIndices φ v).getD 2 0 < φ.length := clauseIndices_getD_lt φ v 2 (by omega)
    rw [occCount_cons_fst_snd_lt (by omega) (by omega),
      occCount_cons_fst_snd_lt (by omega) (by omega),
      occCount_cons_fst_snd_lt (by omega) (by omega),
      occCount_cons_fst_lt (by omega), occCount_cons_fst_lt (by omega),
      occCount_cons_fst_lt (by omega),
      occCount_cons, occCount_cons, occCount_cons, occCount_cons, occCount_cons, occCount_cons,
      occCount_nil]
    have ht : t = b ∨ t = b + 1 ∨ t = b + 2 ∨ t = b + 3 ∨ t = b + 4 ∨ t = b + 5 ∨
        t = b + 6 ∨ t = b + 7 ∨ t = b + 8 := by omega
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Count of occurrences of a clause element `3 * j + r` inside `varGadgetSets`. -/
private theorem occCount_varGadgetSets_clause (φ : CNF ℕ) (v b j r : ℕ)
    (hb : 3 * φ.length ≤ b) (h1 : 1 ≤ (clauseIndices φ v).length)
    (h3 : (clauseIndices φ v).length ≤ 3) (hj : j < φ.length) (hr : r < 3) :
    occCount (varGadgetSets φ v b) (3 * j + r) = if j ∈ clauseIndices φ v then 1 else 0 := by
  unfold varGadgetSets
  have hcases : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hcases with h | h | h
  · simp only [h, ↓reduceIte]
    have hmem : j ∈ clauseIndices φ v ↔ j = (clauseIndices φ v).getD 0 0 := by
      rcases hl : clauseIndices φ v with _ | ⟨x, _ | _⟩ <;> simp_all
    simp only [hmem]
    rw [occCount_cons_snd_thd_gt (by omega) (by omega),
      occCount_cons_snd_thd_gt (by omega) (by omega),
      occCount_cons_snd_thd_gt (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega), occCount_nil]
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr_cases with rfl | rfl | rfl <;> split_ifs <;> omega
  · simp only [h, ↓reduceIte, show (2 : ℕ) ≠ 1 by omega]
    have hne01 : (clauseIndices φ v).getD 0 0 ≠ (clauseIndices φ v).getD 1 0 :=
      clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    have hmem : j ∈ clauseIndices φ v ↔
        j = (clauseIndices φ v).getD 0 0 ∨ j = (clauseIndices φ v).getD 1 0 := by
      rcases hl : clauseIndices φ v with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp_all
    simp only [hmem]
    rw [occCount_cons_thd_gt (by omega), occCount_cons_thd_gt (by omega),
      occCount_cons_thd_gt (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega), occCount_nil]
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr_cases with rfl | rfl | rfl <;> split_ifs <;> omega
  · simp only [h, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega]
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    have hne02 := clauseIndices_getD_ne φ v 0 2 (by omega) (by omega) (by omega)
    have hne12 := clauseIndices_getD_ne φ v 1 2 (by omega) (by omega) (by omega)
    have hmem : j ∈ clauseIndices φ v ↔
        j = (clauseIndices φ v).getD 0 0 ∨ j = (clauseIndices φ v).getD 1 0 ∨
          j = (clauseIndices φ v).getD 2 0 := by
      rcases hl : clauseIndices φ v with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
    simp only [hmem]
    rw [occCount_cons_thd_gt (by omega), occCount_cons_thd_gt (by omega),
      occCount_cons_thd_gt (by omega),
      occCount_cons_snd_thd_gt (by omega) (by omega),
      occCount_cons_snd_thd_gt (by omega) (by omega),
      occCount_cons_snd_thd_gt (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega),
      occCount_cons_all_gt (by omega) (by omega) (by omega), occCount_nil]
    have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr_cases with rfl | rfl | rfl <;> split_ifs <;> omega

theorem varGadgetSets_mem_bounds (φ : CNF ℕ) (v b numEl : ℕ)
    (hb : 3 * φ.length ≤ b) (hbn : b + varDummyCount φ v ≤ numEl)
    (h1 : 1 ≤ (clauseIndices φ v).length) (h3 : (clauseIndices φ v).length ≤ 3)
    {s : ℕ × (ℕ × ℕ)} (hs : s ∈ varGadgetSets φ v b) :
    (s.1 < numEl ∧ s.2.1 < numEl ∧ s.2.2 < numEl ∧
      s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2) ∧
    (s.1 < 3 * φ.length ∨ (b ≤ s.1 ∧ s.1 < b + varDummyCount φ v)) ∧
    (s.2.1 < 3 * φ.length ∨ (b ≤ s.2.1 ∧ s.2.1 < b + varDummyCount φ v)) ∧
    (b ≤ s.2.2 ∧ s.2.2 < b + varDummyCount φ v) := by
  unfold varGadgetSets at hs
  unfold varDummyCount at hbn ⊢
  have hcases : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hcases with h | h | h
  · simp only [h, ↓reduceIte, show (1 : ℕ) ≠ 3 by omega] at hs hbn ⊢
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only; refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        by omega, by omega, by omega⟩)
  · simp only [h, ↓reduceIte, show (2 : ℕ) ≠ 1 by omega, show (2 : ℕ) ≠ 3 by omega] at hs hbn ⊢
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only; refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        by omega, by omega, by omega⟩)
  · simp only [h, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega] at hs hbn ⊢
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    have hj3 := clauseIndices_getD_lt φ v 2 (by omega)
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only; refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        by omega, by omega, by omega⟩)

private theorem occCount_varGadgetSets_outside (φ : CNF ℕ) (v b t : ℕ)
    (hb : 3 * φ.length ≤ b) (h1 : 1 ≤ (clauseIndices φ v).length)
    (h3 : (clauseIndices φ v).length ≤ 3) (ht1 : 3 * φ.length ≤ t)
    (ht2 : t < b ∨ b + varDummyCount φ v ≤ t) :
    occCount (varGadgetSets φ v b) t = 0 := by
  unfold occCount
  rw [List.countP_eq_zero]
  intro s hs
  have hbnd := varGadgetSets_mem_bounds φ v b (b + varDummyCount φ v) hb le_rfl h1 h3 hs
  simp only [memTriple, Bool.or_eq_true, decide_eq_true_eq, not_or]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

private theorem tripleFinset_ne_of_sep {s₁ s₂ : ℕ × (ℕ × ℕ)}
    (h : (s₁.1 ≠ s₂.1 ∧ s₁.1 ≠ s₂.2.1 ∧ s₁.1 ≠ s₂.2.2) ∨
         (s₁.2.1 ≠ s₂.1 ∧ s₁.2.1 ≠ s₂.2.1 ∧ s₁.2.1 ≠ s₂.2.2) ∨
         (s₁.2.2 ≠ s₂.1 ∧ s₁.2.2 ≠ s₂.2.1 ∧ s₁.2.2 ≠ s₂.2.2)) :
    tripleFinset s₁ ≠ tripleFinset s₂ := fun hEq ↦ by
  rcases h with h | h | h
  · have hm : s₁.1 ∈ tripleFinset s₁ := by simp [tripleFinset]
    rw [hEq] at hm; simp [tripleFinset] at hm; omega
  · have hm : s₁.2.1 ∈ tripleFinset s₁ := by simp [tripleFinset]
    rw [hEq] at hm; simp [tripleFinset] at hm; omega
  · have hm : s₁.2.2 ∈ tripleFinset s₁ := by simp [tripleFinset]
    rw [hEq] at hm; simp [tripleFinset] at hm; omega

private theorem varGadgetSets_pairwise (φ : CNF ℕ) (v b : ℕ)
    (hb : 3 * φ.length ≤ b) (h1 : 1 ≤ (clauseIndices φ v).length)
    (h3 : (clauseIndices φ v).length ≤ 3) :
    (varGadgetSets φ v b).Pairwise (fun s₁ s₂ ↦ tripleFinset s₁ ≠ tripleFinset s₂) := by
  unfold varGadgetSets
  have hcases : (clauseIndices φ v).length = 1 ∨ (clauseIndices φ v).length = 2 ∨
      (clauseIndices φ v).length = 3 := by omega
  rcases hcases with h | h | h
  · simp only [h, ↓reduceIte]
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, false_implies, forall_const, and_true]
    repeat (first
      | refine ⟨?_, ?_⟩
      | exact tripleFinset_ne_of_sep (Or.inl ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩)
      | exact tripleFinset_ne_of_sep (Or.inr (Or.inr ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩)))
  · simp only [h, ↓reduceIte, show (2 : ℕ) ≠ 1 by omega]
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, false_implies, forall_const, and_true]
    repeat (first
      | refine ⟨?_, ?_⟩
      | exact tripleFinset_ne_of_sep (Or.inl ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩)
      | exact tripleFinset_ne_of_sep (Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩))
      | exact tripleFinset_ne_of_sep (Or.inr (Or.inr ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩)))
  · simp only [h, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega]
    have hj1 := clauseIndices_getD_lt φ v 0 (by omega)
    have hj2 := clauseIndices_getD_lt φ v 1 (by omega)
    have hj3 := clauseIndices_getD_lt φ v 2 (by omega)
    have hne01 := clauseIndices_getD_ne φ v 0 1 (by omega) (by omega) (by omega)
    have hne02 := clauseIndices_getD_ne φ v 0 2 (by omega) (by omega) (by omega)
    have hne12 := clauseIndices_getD_ne φ v 1 2 (by omega) (by omega) (by omega)
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, false_implies, forall_const, and_true]
    repeat (first
      | refine ⟨?_, ?_⟩
      | exact tripleFinset_ne_of_sep (Or.inl ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩)
      | exact tripleFinset_ne_of_sep (Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega⟩)))

theorem varDummyBase_find (φ : CNF ℕ) (V : List ℕ) {t : ℕ}
    (hge : 3 * φ.length ≤ t) (hlt : t < varDummyBase φ V V.length) :
    ∃ i, ∃ hi : i < V.length, varDummyBase φ V i ≤ t ∧
      t < varDummyBase φ V i + varDummyCount φ (V[i]'hi) := by
  suffices ∀ n (hn : n ≤ V.length), t < varDummyBase φ V n →
      ∃ i, ∃ hi : i < n, varDummyBase φ V i ≤ t ∧
        t < varDummyBase φ V i + varDummyCount φ (V[i]'(by omega)) by
    obtain ⟨i, hi, h1, h2⟩ := this V.length le_rfl hlt
    exact ⟨i, hi, h1, h2⟩
  intro n
  induction n with
  | zero =>
    intro _ hlt0; unfold varDummyBase at hlt0; simp at hlt0; omega
  | succ k ih =>
    intro hk hltS
    rw [varDummyBase_succ φ V k (by omega)] at hltS
    by_cases h : t < varDummyBase φ V k
    · obtain ⟨i, hi, h1, h2⟩ := ih (by omega) h
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨k, Nat.lt_succ_self k, by omega, hltS⟩

theorem sum_varDummyCount_eq (φ : CNF ℕ) (l : List ℕ) :
    (l.map (varDummyCount φ)).sum =
      6 * l.length + 3 * (l.countP fun v ↦ decide ((clauseIndices φ v).length = 3)) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.countP_cons, varDummyCount,
      decide_eq_true_eq, ih]
    split_ifs <;> omega

theorem toRX3C_isValidRX3C (φ : CNF ℕ)
    (hsyn : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) :
    IsValidRX3C (toRX3C φ) := by
  obtain ⟨hex, hpos, hcnt⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hsyn
  unfold toRX3C
  simp only [hsyn, ↓reduceIte]
  set V := φ.distinctVars
  set numEl := 3 * φ.length + (V.map (varDummyCount φ)).sum
  set sets := (List.range V.length).flatMap fun i ↦
    varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)
  have hv_deg : ∀ i (hi : i < V.length),
      1 ≤ (clauseIndices φ (V[i]'hi)).length ∧ (clauseIndices φ (V[i]'hi)).length ≤ 3 := by
    intro i hi
    refine ⟨clauseIndices_length_pos_of_mem_distinctVars φ hex (List.getElem_mem hi), ?_⟩
    rw [clauseIndices_length_eq_count φ hex]; exact hcnt _
  have hmod : numEl % 3 = 0 := by
    change (3 * φ.length + (V.map (varDummyCount φ)).sum) % 3 = 0
    rw [sum_varDummyCount_eq]; omega
  have hlen : sets.length = numEl := by
    have h1 : sets.length = ((List.range V.length).map fun i ↦
        (varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)).length).sum := by
      simp [sets, List.length_flatMap]
    have h2 : ((List.range V.length).map fun i ↦
        (varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)).length) =
        V.map fun v ↦ (clauseIndices φ v).length + varDummyCount φ v := by
      refine List.ext_getElem (by simp) fun i hi1 hi2 ↦ ?_
      simp only [List.length_map, List.length_range] at hi1 hi2
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi1]
      exact varGadgetSets_length φ (V[i]'hi1) (varDummyBase φ V i)
        (hv_deg i hi1).1 (hv_deg i hi1).2
    rw [h1, h2]
    have hsplit : ∀ l : List ℕ,
        (l.map fun v ↦ (clauseIndices φ v).length + varDummyCount φ v).sum =
        (l.map fun v ↦ (clauseIndices φ v).length).sum + (l.map (varDummyCount φ)).sum := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => simp [ih]; omega
    rw [hsplit, sum_length_clauseIndices_eq φ hex]
  have hbounds : ∀ s ∈ sets, s.1 < numEl ∧ s.2.1 < numEl ∧ s.2.2 < numEl ∧
      s.1 ≠ s.2.1 ∧ s.1 ≠ s.2.2 ∧ s.2.1 ≠ s.2.2 := by
    intro s hs
    obtain ⟨i, hi, hsi⟩ := List.mem_flatMap.mp hs
    have hilt : i < V.length := List.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ hilt] at hsi
    have hbn : varDummyBase φ V i + varDummyCount φ (V[i]'hilt) ≤ numEl := by
      dsimp only [numEl]; rw [← varDummyBase_end φ V]; exact varDummyBase_add_le φ V hilt le_rfl
    exact (varGadgetSets_mem_bounds φ (V[i]'hilt) (varDummyBase φ V i) numEl
      (varDummyBase_ge φ V i) hbn (hv_deg i hilt).1 (hv_deg i hilt).2 hsi).1
  have hocc : ∀ t < numEl, occCount sets t = 3 := by
    intro t ht
    rw [occCount_flatMap]
    by_cases hcl : t < 3 * φ.length
    · let j := t / 3
      let r := t % 3
      have hj : j < φ.length := by omega
      have hr : r < 3 := by omega
      have ht_eq : t = 3 * j + r := by omega
      have hmap : ((List.range V.length).map fun i ↦
          occCount (varGadgetSets φ (V.getD i 0) (varDummyBase φ V i)) t) =
          V.map fun v ↦ if j ∈ clauseIndices φ v then 1 else 0 := by
        refine List.ext_getElem (by simp) fun i hi1 hi2 ↦ ?_
        simp only [List.length_map, List.length_range] at hi1 hi2
        simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi1]
        rw [ht_eq]
        exact occCount_varGadgetSets_clause φ (V[i]'hi1) (varDummyBase φ V i) j r
          (varDummyBase_ge φ V i) (hv_deg i hi1).1 (hv_deg i hi1).2 hj hr
      rw [hmap]
      -- Sum over `v ∈ V` of `if j ∈ clauseIndices φ v then 1 else 0` = `(φ[j].map Prod.fst).length
      -- = 3`:
      have hcount_eq : (V.map fun v ↦ if j ∈ clauseIndices φ v then 1 else 0).sum =
          (V.filter fun v ↦ decide (j ∈ clauseIndices φ v)).length := by
        clear hmap ht_eq hbounds hlen hmod
        induction V with
        | nil => simp
        | cons a as ih =>
          simp only [List.map_cons, List.sum_cons, List.filter_cons, decide_eq_true_eq, ih]
          split_ifs
          · simp only [List.length_cons]; omega
          · omega
      rw [hcount_eq]
      have hnd_V : V.Nodup := CNF.nodup_distinctVars φ
      have hnd_c : (φ[j].map Prod.fst).Nodup := (hex _ (List.getElem_mem hj)).2
      have htoF : (V.filter fun v ↦ decide (j ∈ clauseIndices φ v)).toFinset =
          (φ[j].map Prod.fst).toFinset := by
        ext v
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_clauseIndices_iff,
          List.getD_eq_getElem _ _ hj, hj, true_and]
        refine ⟨And.right, fun hv ↦ ⟨CNF.mem_distinctVars.mpr ?_, hv⟩⟩
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl⟩, rfl⟩
      have hc_eq : (V.filter fun v ↦ decide (j ∈ clauseIndices φ v)).length =
          (φ[j].map Prod.fst).length := by
        rw [← List.toFinset_card_of_nodup (hnd_V.filter _), htoF,
          List.toFinset_card_of_nodup hnd_c]
      rw [hc_eq, List.length_map, (hex _ (List.getElem_mem hj)).1]
    · have hge : 3 * φ.length ≤ t := by omega
      have hlt_end : t < varDummyBase φ V V.length := by rw [varDummyBase_end]; exact ht
      obtain ⟨i₀, hi₀, ht_ge, ht_lt⟩ := varDummyBase_find φ V hge hlt_end
      have hsum_single : ∀ l : List ℕ, ∀ x, x ∈ l → l.Nodup →
          (∀ y ∈ l, y ≠ x → occCount (varGadgetSets φ (V.getD y 0) (varDummyBase φ V y)) t = 0) →
          (l.map fun y ↦ occCount (varGadgetSets φ (V.getD y 0) (varDummyBase φ V y)) t).sum =
            occCount (varGadgetSets φ (V.getD x 0) (varDummyBase φ V x)) t := by
        intro l x hx hnd hz
        induction l with
        | nil => cases hx
        | cons a as ih =>
          rw [List.nodup_cons] at hnd
          simp only [List.map_cons, List.sum_cons]
          rcases List.mem_cons.mp hx with rfl | hx'
          · have h0 : (as.map fun y ↦
                occCount (varGadgetSets φ (V.getD y 0) (varDummyBase φ V y)) t).sum = 0 := by
              rw [List.sum_eq_zero_iff]
              intro k hk
              obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hk
              exact hz y (List.mem_cons_of_mem _ hy) (fun h ↦ hnd.1 (h ▸ hy))
            omega
          · have h0 := hz a List.mem_cons_self (fun h ↦ hnd.1 (h ▸ hx'))
            rw [h0, zero_add]
            exact ih hx' hnd.2 (fun y hy hne ↦ hz y (List.mem_cons_of_mem _ hy) hne)
      rw [hsum_single (List.range V.length) i₀ (List.mem_range.mpr hi₀) List.nodup_range]
      · rw [List.getD_eq_getElem _ _ hi₀]
        exact occCount_varGadgetSets_dummy φ (V[i₀]'hi₀) (varDummyBase φ V i₀) t
          (varDummyBase_ge φ V i₀) (hv_deg i₀ hi₀).1 (hv_deg i₀ hi₀).2 ht_ge ht_lt
      · intro y hy hyne
        have hylt : y < V.length := List.mem_range.mp hy
        rw [List.getD_eq_getElem _ _ hylt]
        refine occCount_varGadgetSets_outside φ (V[y]'hylt) (varDummyBase φ V y) t
          (varDummyBase_ge φ V y) (hv_deg y hylt).1 (hv_deg y hylt).2 hge ?_
        rcases Nat.lt_or_gt_of_ne hyne with hlt' | hgt'
        · right; exact (varDummyBase_add_le φ V hlt' (by omega)).trans ht_ge
        · left; exact ht_lt.trans_le (varDummyBase_add_le φ V hgt' (by omega))
  have hpair : sets.Pairwise (fun s₁ s₂ ↦ tripleFinset s₁ ≠ tripleFinset s₂) := by
    rw [List.pairwise_flatMap]
    refine ⟨?_, ?_⟩
    · intro i hi
      have hilt : i < V.length := List.mem_range.mp hi
      rw [List.getD_eq_getElem _ _ hilt]
      exact varGadgetSets_pairwise φ (V[i]'hilt) (varDummyBase φ V i)
        (varDummyBase_ge φ V i) (hv_deg i hilt).1 (hv_deg i hilt).2
    · refine List.pairwise_iff_getElem.mpr fun a b ha hb hab ↦ ?_
      simp only [List.length_range] at ha hb
      simp only [List.getElem_range, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
      intro s₁ hs₁ s₂ hs₂
      have h1 := varGadgetSets_mem_bounds φ (V[a]'ha) (varDummyBase φ V a) numEl
        (varDummyBase_ge φ V a)
          (by dsimp only [numEl]; rw [← varDummyBase_end]; exact varDummyBase_add_le φ V ha le_rfl)
        (hv_deg a ha).1 (hv_deg a ha).2 hs₁
      have h2 := varGadgetSets_mem_bounds φ (V[b]'hb) (varDummyBase φ V b) numEl
        (varDummyBase_ge φ V b)
          (by dsimp only [numEl]; rw [← varDummyBase_end]; exact varDummyBase_add_le φ V hb le_rfl)
        (hv_deg b hb).1 (hv_deg b hb).2 hs₂
      have hsep := varDummyBase_add_le φ V hab (by omega)
      have hbase_a := varDummyBase_ge φ V a
      exact tripleFinset_ne_of_sep (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
  exact ⟨hmod, hlen, hbounds, hocc, hpair⟩

end RX3CReduction

end Cslib.Complexity
