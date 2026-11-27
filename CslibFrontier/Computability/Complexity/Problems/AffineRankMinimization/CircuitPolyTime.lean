/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.CircuitCompilation
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Hardness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Polynomial-Time Certificate for Arithmetic-Circuit Compilation

Polynomial-time certificate showing that `compileCircuitConstraints` is computable in
polynomial time under unary gate encodings and binary rational constraint encodings.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

attribute [local irreducible] encRat encIntBin encNat encUnary

private theorem sumElimSnd' {γ α β δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool}
    {f : γ × α → δ} {g : γ × β → δ}
    (hf : ComputableInPolyTime f (encPair eg ea) ed)
    (hg : ComputableInPolyTime g (encPair eg eb) ed) :
    ComputableInPolyTime
      (fun p : γ × (α ⊕ β) ↦ p.2.elim (fun a ↦ f (p.1, a)) (fun b ↦ g (p.1, b)))
      (encPair eg (encSum ea eb)) ed :=
  sumElimSnd (left := fun x a ↦ f (x, a)) (right := fun x b ↦ g (x, b)) hf hg

private theorem singleEntryRows_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) × ℚ ↦
      singleEntryRows p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2)
      (encPair (encPair encUnary encUnary) (encPair (encPair encUnary encUnary) encRat))
      (encList (encList encRat)) := by
  let encP := encPair (encPair encUnary encUnary) (encPair (encPair encUnary encUnary) encRat)
  let encPI := encPair encP encUnary
  let encPIJ := encPair encPI encUnary
  have hcell : ComputableInPolyTime
      (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × ℚ) × ℕ) × ℕ ↦
        if s.1.2 = s.1.1.2.1.1 ∧ s.2 = s.1.1.2.1.2 then s.1.1.2.2 else 0)
      encPIJ encRat := by
    have hi := (snd encP encUnary).comp (fst encPI encUnary)
    have hj := snd encPI encUnary
    have hp := (fst encP encUnary).comp (fst encPI encUnary)
    have hr := (fst encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hc := (snd encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hv := (snd _ _).comp ((snd _ _).comp hp)
    have hcond := bool_and' (unary_beq hi hr) (unary_beq hj hc)
    exact (hcond.ite' hv (const 0)).of_enc_eq fun s ↦ by
      congr 1; by_cases h1 : s.1.2 = s.1.1.2.1.1 <;> by_cases h2 : s.2 =
        s.1.1.2.1.2 <;> simp [h1, h2]
  have hrow := mapWith hcell id'
    (range.comp ((snd encUnary encUnary).comp ((fst _ _).comp (fst encP encUnary))))
  exact mapWith hrow id' (range.comp ((fst encUnary encUnary).comp (fst _ _)))

private theorem indicator_polyTime {γ : Type} {enc : γ ↪ List Bool} {a b c d : γ → ℕ}
    (ha : ComputableInPolyTime a enc encUnary) (hb : ComputableInPolyTime b enc encUnary)
    (hc : ComputableInPolyTime c enc encUnary) (hd : ComputableInPolyTime d enc encUnary) :
    ComputableInPolyTime (fun s ↦ if a s = b s ∧ c s = d s then (1 : ℚ) else 0) enc encRat :=
  ((bool_and' (unary_beq ha hb) (unary_beq hc hd)).ite'
    (const (α := γ) (1 : ℚ)) (const (α := γ) (0 : ℚ))).of_enc_eq fun s ↦ by
      congr 1; by_cases h1 : a s = b s <;> by_cases h2 : c s = d s <;> simp [h1, h2]

private theorem diffEntryRows_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) ↦
      diffEntryRows p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary encUnary)
        (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))
      (encList (encList encRat)) := by
  let encP := encPair (encPair encUnary encUnary)
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
  let encPI := encPair encP encUnary
  let encPIJ := encPair encPI encUnary
  have hcell : ComputableInPolyTime
      (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        (if s.1.2 = s.1.1.2.1.1 ∧ s.2 = s.1.1.2.1.2 then (1 : ℚ) else 0) -
        (if s.1.2 = s.1.1.2.2.1 ∧ s.2 = s.1.1.2.2.2 then (1 : ℚ) else 0))
      encPIJ encRat := by
    have hi : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.2)
        encPIJ encUnary := (snd encP encUnary).comp (fst encPI encUnary)
    have hj : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.2)
        encPIJ encUnary := snd encPI encUnary
    have hp := (fst encP encUnary).comp (fst encPI encUnary)
    have hr1 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.1.1) encPIJ encUnary :=
      (fst encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hc1 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.1.2) encPIJ encUnary :=
      (snd encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hr2 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.2.1) encPIJ encUnary :=
      (fst encUnary encUnary).comp ((snd _ _).comp ((snd _ _).comp hp))
    have hc2 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.2.2) encPIJ encUnary :=
      (snd encUnary encUnary).comp ((snd _ _).comp ((snd _ _).comp hp))
    exact rat_sub' (indicator_polyTime hi hr1 hj hc1) (indicator_polyTime hi hr2 hj hc2)
  have hrow := mapWith hcell id'
    (range.comp ((snd encUnary encUnary).comp ((fst _ _).comp (fst encP encUnary))))
  exact mapWith hrow id' (range.comp ((fst encUnary encUnary).comp (fst _ _)))

private theorem addEntryRows_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) ↦
      addEntryRows p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1.1 p.2.2.1.2 p.2.2.2.1 p.2.2.2.2)
      (encPair (encPair encUnary encUnary)
        (encPair (encPair encUnary encUnary)
          (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))))
      (encList (encList encRat)) := by
  let encP := encPair (encPair encUnary encUnary)
    (encPair (encPair encUnary encUnary)
      (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))
  let encPI := encPair encP encUnary
  let encPIJ := encPair encPI encUnary
  have hcell : ComputableInPolyTime
      (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        (if s.1.2 = s.1.1.2.1.1 ∧ s.2 = s.1.1.2.1.2 then (1 : ℚ) else 0) -
        (if s.1.2 = s.1.1.2.2.1.1 ∧ s.2 = s.1.1.2.2.1.2 then (1 : ℚ) else 0) -
        (if s.1.2 = s.1.1.2.2.2.1 ∧ s.2 = s.1.1.2.2.2.2 then (1 : ℚ) else 0))
      encPIJ encRat := by
    have hi : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.2)
        encPIJ encUnary := (snd encP encUnary).comp (fst encPI encUnary)
    have hj : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.2)
        encPIJ encUnary := snd encPI encUnary
    have hp := (fst encP encUnary).comp (fst encPI encUnary)
    have hrz : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.1.2.1.1)
        encPIJ encUnary := (fst encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hcz : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.1.2.1.2)
        encPIJ encUnary := (snd encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hrx : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.1.2.2.1.1)
        encPIJ encUnary :=
      (fst encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
    have hcx : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.1.2.2.1.2)
        encPIJ encUnary :=
      (snd encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
    have hry : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.1.2.2.2.1)
        encPIJ encUnary :=
      (fst encUnary encUnary).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
    have hcy : ComputableInPolyTime
        (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.1.2.2.2.2)
        encPIJ encUnary :=
      (snd encUnary encUnary).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
    exact rat_sub' (rat_sub' (indicator_polyTime hi hrz hj hcz) (indicator_polyTime hi hrx hj hcx))
      (indicator_polyTime hi hry hj hcy)
  have hrow := mapWith hcell id'
    (range.comp ((snd encUnary encUnary).comp ((fst _ _).comp (fst encP encUnary))))
  exact mapWith hrow id' (range.comp ((fst encUnary encUnary).comp (fst _ _)))

private theorem negEntryRows_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) ↦
      negEntryRows p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary encUnary)
        (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))
      (encList (encList encRat)) := by
  let encP := encPair (encPair encUnary encUnary)
    (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
  let encPI := encPair encP encUnary
  let encPIJ := encPair encPI encUnary
  have hcell : ComputableInPolyTime
      (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        (if s.1.2 = s.1.1.2.1.1 ∧ s.2 = s.1.1.2.1.2 then (1 : ℚ) else 0) +
        (if s.1.2 = s.1.1.2.2.1 ∧ s.2 = s.1.1.2.2.2 then (1 : ℚ) else 0))
      encPIJ encRat := by
    have hi : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.1.2)
        encPIJ encUnary := (snd encP encUnary).comp (fst encPI encUnary)
    have hj : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦ s.2)
        encPIJ encUnary := snd encPI encUnary
    have hp := (fst encP encUnary).comp (fst encPI encUnary)
    have hr1 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.1.1) encPIJ encUnary :=
      (fst encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hc1 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.1.2) encPIJ encUnary :=
      (snd encUnary encUnary).comp ((fst _ _).comp ((snd _ _).comp hp))
    have hr2 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.2.1) encPIJ encUnary :=
      (fst encUnary encUnary).comp ((snd _ _).comp ((snd _ _).comp hp))
    have hc2 : ComputableInPolyTime (fun s : (((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ ↦
        s.1.1.2.2.2) encPIJ encUnary :=
      (snd encUnary encUnary).comp ((snd _ _).comp ((snd _ _).comp hp))
    exact rat_add' (indicator_polyTime hi hr1 hj hc1) (indicator_polyTime hi hr2 hj hc2)
  have hrow := mapWith hcell id'
    (range.comp ((snd encUnary encUnary).comp ((fst _ _).comp (fst encP encUnary))))
  exact mapWith hrow id' (range.comp ((fst encUnary encUnary).comp (fst _ _)))

attribute [local irreducible] singleEntryRows diffEntryRows addEntryRows negEntryRows
  encPair encList

private theorem gaugeConstraints_polyTime :
    ComputableInPolyTime gaugeConstraints encUnary encARMConstraints := by
  let encC := encPair (encList (encList encRat)) encRat
  have mkG (r c : ℕ) (v : ℚ) : ComputableInPolyTime
      (fun d : ℕ ↦ (singleEntryRows d d r c 1, v)) encUnary encC :=
    (singleEntryRows_polyTime.comp
      (((id' (encIn := encUnary)).prod id').prod
        (((const r).prod (const c)).prod (const 1)))).prod (const v)
  have g8 : ComputableInPolyTime (fun d ↦ [(singleEntryRows d d 2 2 1, (1 : ℚ))])
      encUnary encARMConstraints :=
    (cons encC).comp ((mkG 2 2 1).prod (const (α := ℕ) []))
  have g7 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 2 1 1, (0 : ℚ)) :: [(singleEntryRows d d 2 2 1, (1 : ℚ))])
      encUnary encARMConstraints := (cons encC).comp ((mkG 2 1 0).prod g8)
  have g6 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 2 0 1, (0 : ℚ)) :: (singleEntryRows d d 2 1 1, 0) ::
      [(singleEntryRows d d 2 2 1, 1)]) encUnary encARMConstraints :=
    (cons encC).comp ((mkG 2 0 0).prod g7)
  have g5 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 1 2 1, (0 : ℚ)) :: (singleEntryRows d d 2 0 1, 0) ::
      (singleEntryRows d d 2 1 1, 0) :: [(singleEntryRows d d 2 2 1, 1)])
      encUnary encARMConstraints := (cons encC).comp ((mkG 1 2 0).prod g6)
  have g4 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 1 1 1, (1 : ℚ)) :: (singleEntryRows d d 1 2 1, 0) ::
      (singleEntryRows d d 2 0 1, 0) :: (singleEntryRows d d 2 1 1, 0) ::
      [(singleEntryRows d d 2 2 1, 1)]) encUnary encARMConstraints :=
    (cons encC).comp ((mkG 1 1 1).prod g5)
  have g3 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 1 0 1, (0 : ℚ)) :: (singleEntryRows d d 1 1 1, 1) ::
      (singleEntryRows d d 1 2 1, 0) :: (singleEntryRows d d 2 0 1, 0) ::
      (singleEntryRows d d 2 1 1, 0) :: [(singleEntryRows d d 2 2 1, 1)])
      encUnary encARMConstraints := (cons encC).comp ((mkG 1 0 0).prod g4)
  have g2 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 0 2 1, (0 : ℚ)) :: (singleEntryRows d d 1 0 1, 0) ::
      (singleEntryRows d d 1 1 1, 1) :: (singleEntryRows d d 1 2 1, 0) ::
      (singleEntryRows d d 2 0 1, 0) :: (singleEntryRows d d 2 1 1, 0) ::
      [(singleEntryRows d d 2 2 1, 1)]) encUnary encARMConstraints :=
    (cons encC).comp ((mkG 0 2 0).prod g3)
  have g1 : ComputableInPolyTime (fun d ↦
      (singleEntryRows d d 0 1 1, (0 : ℚ)) :: (singleEntryRows d d 0 2 1, 0) ::
      (singleEntryRows d d 1 0 1, 0) :: (singleEntryRows d d 1 1 1, 1) ::
      (singleEntryRows d d 1 2 1, 0) :: (singleEntryRows d d 2 0 1, 0) ::
      (singleEntryRows d d 2 1 1, 0) :: [(singleEntryRows d d 2 2 1, 1)])
      encUnary encARMConstraints := (cons encC).comp ((mkG 0 1 0).prod g2)
  exact (cons encC).comp ((mkG 0 0 1).prod g1)

private theorem mulGateConstraints_polyTime :
    ComputableInPolyTime
      (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
        let d := circuitDim s.1.1.1 s.1.1.2
        let r1 := 3 + s.1.1.1 + s.1.1.2 + 2 * s.1.2
        let r2 := 3 + s.1.1.1 + s.1.1.2 + 2 * s.1.2 + 1
        [ (singleEntryRows d d r1 r1 1, (1 : ℚ)),
          (singleEntryRows d d 0 r1 1, 0), (singleEntryRows d d 0 r2 1, 0),
          (singleEntryRows d d 1 r1 1, 0), (singleEntryRows d d 1 r2 1, 0),
          (singleEntryRows d d r1 0 1, 0), (singleEntryRows d d r1 1 1, 0),
          (singleEntryRows d d r2 0 1, 0), (singleEntryRows d d r2 1 1, 0),
          (diffEntryRows d d r1 r2 (3 + s.1.1.1 + s.2.1) (3 + s.1.1.1 + s.2.1), 0),
          (diffEntryRows d d r2 r1 (3 + s.1.1.1 + s.2.2) (3 + s.1.1.1 + s.2.2), 0),
          (diffEntryRows d d r2 r2 (3 + s.1.1.1 + s.1.2) (3 + s.1.1.1 + s.1.2), 0) ])
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encUnary))
      encARMConstraints := by
  let encB := encPair (encPair encUnary encUnary) encUnary
  let encIn := encPair encB (encPair encUnary encUnary)
  let encC := encPair (encList (encList encRat)) encRat
  have hNb : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.1.1) encIn encUnary :=
    (fst _ _).comp ((fst _ _).comp (fst encB (encPair encUnary encUnary)))
  have hSb : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.1.2) encIn encUnary :=
    (snd _ _).comp ((fst _ _).comp (fst encB (encPair encUnary encUnary)))
  have hkb : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.1.2) encIn encUnary :=
    (snd _ _).comp (fst encB (encPair encUnary encUnary))
  have hl : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.2.1) encIn encUnary :=
    (fst _ _).comp (snd encB (encPair encUnary encUnary))
  have hr : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦ s.2.2) encIn encUnary :=
    (snd _ _).comp (snd encB (encPair encUnary encUnary))
  have hdb : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
      circuitDim s.1.1.1 s.1.1.2) encIn encUnary :=
    unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod
      (unary_mul.comp ((const 3).prod hSb)))
  have hr1 : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
      3 + s.1.1.1 + s.1.1.2 + 2 * s.1.2) encIn encUnary :=
    unary_add.comp ((unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hSb)).prod
      (unary_mul.comp ((const 2).prod hkb)))
  have hr2 : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
      3 + s.1.1.1 + s.1.1.2 + 2 * s.1.2 + 1) encIn encUnary :=
    unary_add.comp (hr1.prod (const 1))
  have hgk : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
      3 + s.1.1.1 + s.1.2) encIn encUnary :=
    unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hkb)
  have hgl : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
      3 + s.1.1.1 + s.2.1) encIn encUnary :=
    unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hl)
  have hgr : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
      3 + s.1.1.1 + s.2.2) encIn encUnary :=
    unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hr)
  have mkS (a b : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → ℕ) (v : ℚ)
      (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary) :
      ComputableInPolyTime (fun s ↦
        (singleEntryRows (circuitDim s.1.1.1 s.1.1.2) (circuitDim s.1.1.1 s.1.1.2)
          (a s) (b s) 1, v)) encIn encC :=
    (singleEntryRows_polyTime.comp ((hdb.prod hdb).prod ((ha.prod hb).prod (const 1)))).prod
      (const v)
  have mkD (a b c d' : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → ℕ)
      (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
      (hc : ComputableInPolyTime c encIn encUnary) (hd' : ComputableInPolyTime d' encIn encUnary) :
      ComputableInPolyTime (fun s ↦
        (diffEntryRows (circuitDim s.1.1.1 s.1.1.2) (circuitDim s.1.1.1 s.1.1.2)
          (a s) (b s) (c s) (d' s), (0 : ℚ))) encIn encC :=
    (diffEntryRows_polyTime.comp ((hdb.prod hdb).prod ((ha.prod hb).prod (hc.prod hd')))).prod
      (const 0)
  have m11 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkD _ _ _ _ hr2 hr2 hgk hgk).prod (const []))
  have m10 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkD _ _ _ _ hr2 hr1 hgr hgr).prod m11)
  have m9 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkD _ _ _ _ hr1 hr2 hgl hgl).prod m10)
  have m8 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 hr2 (const 1)).prod m9)
  have m7 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 hr2 (const 0)).prod m8)
  have m6 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 hr1 (const 1)).prod m7)
  have m5 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 hr1 (const 0)).prod m6)
  have m4 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 (const 1) hr2).prod m5)
  have m3 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 (const 1) hr1).prod m4)
  have m2 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 (const 0) hr2).prod m3)
  have m1 : ComputableInPolyTime _ encIn encARMConstraints :=
    (cons encC).comp ((mkS _ _ 0 (const 0) hr1).prod m2)
  exact (cons encC).comp ((mkS _ _ 1 hr1 hr1).prod m1)

/-- Polynomial-time certificate for `compileCircuitConstraints`. -/
theorem compileCircuitConstraints_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × List ArithGate × ℕ ↦ compileCircuitConstraints p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encList encArithGateUnary) encUnary)) encARMConstraints := by
  let encC := encPair (encList (encList encRat)) encRat
  let encIn := encPair encUnary (encPair (encList encArithGateUnary) encUnary)
  have hN := fst encUnary (encPair (encList encArithGateUnary) encUnary)
  have hgs := (fst _ _).comp (snd encUnary (encPair (encList encArithGateUnary) encUnary))
  have hout := (snd _ _).comp (snd encUnary (encPair (encList encArithGateUnary) encUnary))
  have hS := (length_list encArithGateUnary).comp hgs
  have hd : ComputableInPolyTime (fun p : ℕ × List ArithGate × ℕ ↦ circuitDim p.1 p.2.1.length)
      encIn encUnary :=
    unary_add.comp ((unary_add.comp ((const 3).prod hN)).prod
      (unary_mul.comp ((const 3).prod hS)))
  have hgauge : ComputableInPolyTime
      (fun p : ℕ × List ArithGate × ℕ ↦ gaugeConstraints (circuitDim p.1 p.2.1.length))
      encIn encARMConstraints :=
    gaugeConstraints_polyTime.comp hd
  have houtC : ComputableInPolyTime
      (fun p : ℕ × List ArithGate × ℕ ↦
        [(singleEntryRows (circuitDim p.1 p.2.1.length) (circuitDim p.1 p.2.1.length)
          (3 + p.1 + p.2.2) (3 + p.1 + p.2.2) 1, (0 : ℚ))])
      encIn encARMConstraints := by
    have hpos := unary_add.comp ((unary_add.comp ((const 3).prod hN)).prod hout)
    have h1 : ComputableInPolyTime (fun p : ℕ × List ArithGate × ℕ ↦
        (singleEntryRows (circuitDim p.1 p.2.1.length) (circuitDim p.1 p.2.1.length)
          (3 + p.1 + p.2.2) (3 + p.1 + p.2.2) 1, (0 : ℚ))) encIn encC :=
      (singleEntryRows_polyTime.comp
        ((hd.prod hd).prod ((hpos.prod hpos).prod (const (encOut := encRat) 1)))).prod
        (const (encOut := encRat) (0 : ℚ))
    exact (cons encC).comp (h1.prod (const []))
  let encPar := encPair encUnary encUnary
  let encGP := encPair encPar (encPair encArithGateUnary encUnary)
  have hgateC : ComputableInPolyTime
      (fun q : (ℕ × ℕ) × (ArithGate × ℕ) ↦ gateConstraints q.1.1 q.1.2 q.2.2 q.2.1)
      encGP encARMConstraints := by
    have hkp := (snd _ _).comp (snd encPar (encPair encArithGateUnary encUnary))
    have hgp := (fst _ _).comp (snd encPar (encPair encArithGateUnary encUnary))
    have hBase : ComputableInPolyTime (fun q : (ℕ × ℕ) × (ArithGate × ℕ) ↦ (q.1, q.2.2))
        encGP (encPair encPar encUnary) := (fst _ _).prod hkp
    have hGateSum : ComputableInPolyTime
        (fun s : ((ℕ × ℕ) × ℕ) × (ℕ ⊕ ℚ ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) ↦
          gateConstraints s.1.1.1 s.1.1.2 s.1.2
            (s.2.elim ArithGate.input (Sum.elim ArithGate.const
              (Sum.elim (fun p ↦ ArithGate.add p.1 p.2)
                (Sum.elim (fun p ↦ ArithGate.mul p.1 p.2) ArithGate.neg)))))
        (encPair (encPair encPar encUnary)
          (encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
            (encSum (encPair encUnary encUnary) encUnary))))) encARMConstraints := by
      let encB := encPair encPar encUnary
      have hInp : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × ℕ ↦
          let d := circuitDim s.1.1.1 s.1.1.2
          [(diffEntryRows d d (3 + s.1.1.1 + s.1.2) (3 + s.1.1.1 + s.1.2)
            (3 + s.2) (3 + s.2), (0 : ℚ))])
          (encPair encB encUnary) encARMConstraints := by
        have hNb := (fst _ _).comp ((fst _ _).comp (fst encB encUnary))
        have hSb := (snd _ _).comp ((fst _ _).comp (fst encB encUnary))
        have hkb := (snd _ _).comp (fst encB encUnary)
        have hidx := snd encB encUnary
        have hdb := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod
          (unary_mul.comp ((const 3).prod hSb)))
        have hgk := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hkb)
        have hgi := unary_add.comp ((const 3).prod hidx)
        exact (cons encC).comp (((diffEntryRows_polyTime.comp
          ((hdb.prod hdb).prod ((hgk.prod hgk).prod (hgi.prod hgi)))).prod (const 0)).prod
          (const []))
      have hConst : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × ℚ ↦
          let d := circuitDim s.1.1.1 s.1.1.2
          [(singleEntryRows d d (3 + s.1.1.1 + s.1.2) (3 + s.1.1.1 + s.1.2) 1, s.2)])
          (encPair encB encRat) encARMConstraints := by
        have hNb := (fst _ _).comp ((fst _ _).comp (fst encB encRat))
        have hSb := (snd _ _).comp ((fst _ _).comp (fst encB encRat))
        have hkb := (snd _ _).comp (fst encB encRat)
        have hv := snd encB encRat
        have hdb := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod
          (unary_mul.comp ((const 3).prod hSb)))
        have hgk := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hkb)
        exact (cons encC).comp (((singleEntryRows_polyTime.comp
          ((hdb.prod hdb).prod ((hgk.prod hgk).prod (const 1)))).prod hv).prod (const []))
      have hAdd : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) ↦
          let d := circuitDim s.1.1.1 s.1.1.2
          [(addEntryRows d d (3 + s.1.1.1 + s.1.2) (3 + s.1.1.1 + s.1.2)
            (3 + s.1.1.1 + s.2.1) (3 + s.1.1.1 + s.2.1)
            (3 + s.1.1.1 + s.2.2) (3 + s.1.1.1 + s.2.2), (0 : ℚ))])
          (encPair encB (encPair encUnary encUnary)) encARMConstraints := by
        have hNb := (fst _ _).comp ((fst _ _).comp (fst encB (encPair encUnary encUnary)))
        have hSb := (snd _ _).comp ((fst _ _).comp (fst encB (encPair encUnary encUnary)))
        have hkb := (snd _ _).comp (fst encB (encPair encUnary encUnary))
        have hl := (fst _ _).comp (snd encB (encPair encUnary encUnary))
        have hr := (snd _ _).comp (snd encB (encPair encUnary encUnary))
        have hdb := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod
          (unary_mul.comp ((const 3).prod hSb)))
        have hgk := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hkb)
        have hgl := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hl)
        have hgr := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hr)
        exact (cons encC).comp (((addEntryRows_polyTime.comp
          ((hdb.prod hdb).prod ((hgk.prod hgk).prod ((hgl.prod hgl).prod (hgr.prod hgr))))).prod
          (const 0)).prod (const []))
      have hNeg : ComputableInPolyTime (fun s : ((ℕ × ℕ) × ℕ) × ℕ ↦
          let d := circuitDim s.1.1.1 s.1.1.2
          [(negEntryRows d d (3 + s.1.1.1 + s.1.2) (3 + s.1.1.1 + s.1.2)
            (3 + s.1.1.1 + s.2) (3 + s.1.1.1 + s.2), (0 : ℚ))])
          (encPair encB encUnary) encARMConstraints := by
        have hNb := (fst _ _).comp ((fst _ _).comp (fst encB encUnary))
        have hSb := (snd _ _).comp ((fst _ _).comp (fst encB encUnary))
        have hkb := (snd _ _).comp (fst encB encUnary)
        have ha := snd encB encUnary
        have hdb := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod
          (unary_mul.comp ((const 3).prod hSb)))
        have hgk := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod hkb)
        have hga := unary_add.comp ((unary_add.comp ((const 3).prod hNb)).prod ha)
        exact (cons encC).comp (((negEntryRows_polyTime.comp
          ((hdb.prod hdb).prod ((hgk.prod hgk).prod (hga.prod hga)))).prod (const 0)).prod
          (const []))
      exact (sumElimSnd' hInp (sumElimSnd' hConst (sumElimSnd' hAdd
        (sumElimSnd' mulGateConstraints_polyTime hNeg)))).of_enc_eq fun s ↦ by
          rcases s with ⟨⟨⟨N, S⟩, k⟩, g | c | ⟨l, r⟩ | ⟨l, r⟩ | a⟩ <;> rfl
    have hToSum : ComputableInPolyTime
        (fun g : ArithGate ↦ match g with
          | .input i => Sum.inl i
          | .const c => Sum.inr (.inl c)
          | .add l r => Sum.inr (.inr (.inl (l, r)))
          | .mul l r => Sum.inr (.inr (.inr (.inl (l, r))))
          | .neg a => Sum.inr (.inr (.inr (.inr a))))
        encArithGateUnary
        (encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
          (encSum (encPair encUnary encUnary) encUnary)))) :=
      of_eq fun g ↦ by cases g <;> rfl
    exact (hGateSum.comp (hBase.prod (hToSum.comp hgp))).of_enc_eq fun q ↦ by
      rcases q with ⟨⟨N, S⟩, g, k⟩
      cases g <;> rfl
  have hallGates := flatMapWith hgateC (hN.prod hS) ((zipIdx encArithGateUnary).comp hgs)
  exact (listAppend encC).comp (((listAppend encC).comp (hgauge.prod hallGates)).prod houtC)

end Cslib.Complexity
