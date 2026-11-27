/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Reduction.Isomorphism
public import CslibFrontier.Computability.Complexity.Reduction.Isomorphism.Paddable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic

import CslibFrontier.Computability.Complexity.Classes.EXP.Padding
import CslibFrontier.Computability.Complexity.Classes.Ladner.Basic
import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Length-Increasing One-One Completeness for Exponential Time

Every language complete for linear exponential time `E` or exponential time `EXP` under
polynomial-time many-one reductions is also complete under strictly length-increasing
polynomial-time one-one reductions (`Cslib.Complexity.PolyTimeLengthIncreasingOneOneReducible`),
proved unconditionally under standard Lean axioms. In particular, any two `E`-complete languages
(and any two `EXP`-complete languages) over types equipped with total polynomial-time decoders are
mutually reducible via length-increasing one-one reductions, formalizing the theorem of Berman
 and of Watanabe.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Mutual polynomial-time length-increasing one-one reducibility between `(A, encA)` and
`(B, encB)`.
-/
def PolyTimeLengthIncreasingOneOneEquiv {α β : Type} (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (A : Set α) (B : Set β) : Prop :=
  PolyTimeLengthIncreasingOneOneReducible encA encB A B ∧
    PolyTimeLengthIncreasingOneOneReducible encB encA B A

/-- Characterization of `CslibFrontier.Complexity.PolyTimeLengthIncreasingOneOneEquiv`. -/
theorem polyTimeLengthIncreasingOneOneEquiv_iff {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β} :
    PolyTimeLengthIncreasingOneOneEquiv encA encB A B ↔
      PolyTimeLengthIncreasingOneOneReducible encA encB A B ∧
        PolyTimeLengthIncreasingOneOneReducible encB encA B A := by
  unfold PolyTimeLengthIncreasingOneOneEquiv
  rfl

/-- Symmetry of `CslibFrontier.Complexity.PolyTimeLengthIncreasingOneOneEquiv`. -/
theorem PolyTimeLengthIncreasingOneOneEquiv.symm {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : PolyTimeLengthIncreasingOneOneEquiv encA encB A B) :
    PolyTimeLengthIncreasingOneOneEquiv encB encA B A :=
  ⟨h.2, h.1⟩

/-- Transitivity of `CslibFrontier.Complexity.PolyTimeLengthIncreasingOneOneEquiv`. -/
theorem PolyTimeLengthIncreasingOneOneEquiv.trans {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {A : Set α} {B : Set β} {C : Set γ}
    (hAB : PolyTimeLengthIncreasingOneOneEquiv encA encB A B)
    (hBC : PolyTimeLengthIncreasingOneOneEquiv encB encC B C) :
    PolyTimeLengthIncreasingOneOneEquiv encA encC A C :=
  ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩

/-- Mutual polynomial-time invertible length-increasing one-one reducibility between `(A, encA)`
and `(B, encB)`. -/
def PolyTimeInvertibleLengthIncreasingOneOneEquiv {α β : Type} (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (A : Set α) (B : Set β) : Prop :=
  PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B ∧
    PolyTimeInvertibleLengthIncreasingOneOneReducible encB encA B A

/-- Characterization of `CslibFrontier.Complexity.PolyTimeInvertibleLengthIncreasingOneOneEquiv`. -/
theorem polyTimeInvertibleLengthIncreasingOneOneEquiv_iff {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β} :
    PolyTimeInvertibleLengthIncreasingOneOneEquiv encA encB A B ↔
      PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B ∧
        PolyTimeInvertibleLengthIncreasingOneOneReducible encB encA B A := by
  unfold PolyTimeInvertibleLengthIncreasingOneOneEquiv
  rfl

/-- Mutual polynomial-time invertible length-increasing one-one reducibility implies mutual
length-increasing one-one reducibility. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneEquiv.toLengthIncreasing {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : PolyTimeInvertibleLengthIncreasingOneOneEquiv encA encB A B) :
    PolyTimeLengthIncreasingOneOneEquiv encA encB A B :=
  ⟨h.1.polyTimeLengthIncreasingOneOneReducible, h.2.polyTimeLengthIncreasingOneOneReducible⟩

/-- By Berman and Hartmanis's polynomial-time Cantor–Schröder–Bernstein theorem, mutual
polynomial-time invertible length-increasing one-one reducibility implies polynomial-time
isomorphism. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneEquiv.polyTimeIsomorphic {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (h : PolyTimeInvertibleLengthIncreasingOneOneEquiv encA encB A B) :
    PolyTimeIsomorphic encA encB A B :=
  h.1.polyTimeIsomorphic h.2

/-! ### Berman–Watanabe diagonal construction -/

@[irreducible]
private noncomputable def simHeaderRun (w x : List Bool) (N : ℕ) : List ℕ × Bool :=
  universal (decodeDesc (unframe (unframe w)), x.map eBit, N)

private lemma simHeaderRun_eq (w x : List Bool) (N : ℕ) :
    simHeaderRun w x N = universal (decodeDesc (unframe (unframe w)), x.map eBit, N) := by
  unfold simHeaderRun
  rfl

private noncomputable def indexLookup (u : List Bool) (N : ℕ) : ℕ :=
  ((List.range N).filter fun j => decide (Ladner.word j = u)).headD 0

private lemma indexLookup_eq_index {u : List Bool} {N : ℕ} (hN : Ladner.index u < N) :
    indexLookup u N = Ladner.index u := by
  unfold indexLookup
  obtain ⟨k, hk⟩ : ∃ k, N = Ladner.index u + (k + 1) := ⟨N - Ladner.index u - 1, by omega⟩
  rw [hk, List.range_add, List.filter_append]
  have hleft :
      (List.range (Ladner.index u)).filter (fun j => decide (Ladner.word j = u)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    rw [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    intro heq
    have := congrArg Ladner.index heq
    rw [Ladner.index_word] at this
    omega
  rw [hleft, List.nil_append, List.range_succ_eq_map, List.map_cons, Nat.add_zero,
    List.filter_cons_of_pos (by simp [Ladner.word_index]), List.headD_cons]

private lemma filter_range_first {n j₀ : ℕ} {p : ℕ → Bool} (hj₀ : j₀ < n) (hp : p j₀ = true)
    (hmin : ∀ j < j₀, p j = false) :
    ((List.range n).filter p).isEmpty = false ∧ ((List.range n).filter p).headD 0 = j₀ := by
  obtain ⟨k, hk⟩ : ∃ k, n = j₀ + (k + 1) := ⟨n - j₀ - 1, by omega⟩
  rw [hk, List.range_add, List.filter_append]
  have hleft : (List.range j₀).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    rw [hmin j (List.mem_range.mp hj)]
    decide
  rw [hleft, List.nil_append, List.range_succ_eq_map, List.map_cons, Nat.add_zero,
    List.filter_cons_of_pos hp]
  exact ⟨rfl, rfl⟩

private lemma length_word_le_of_lt_index {j : ℕ} {u : List Bool} (hj : j < Ladner.index u) :
    (Ladner.word j).length ≤ u.length := by
  have h1 := Ladner.two_pow_length_word_le j
  have h2 := Ladner.index_add_two_le u
  have hpow : 2 ^ (Ladner.word j).length < 2 ^ (u.length + 1) := by omega
  have hlt : (Ladner.word j).length < u.length + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpow
  omega

private noncomputable def collisionList {α : Type} {encA : α ↪ List Bool} (DA : Decoder encA)
    (w : List Bool) (N : ℕ) : List ℕ :=
  (List.range (indexLookup (dropFrame w) N)).filter fun j =>
    decide (encA (DA.decode (Ladner.word j)) = Ladner.word j) &&
      decide (simHeaderRun w (frame (unframe w) ++ Ladner.word j) N = simHeaderRun w w N)

private noncomputable def watanabeTest {α : Type} {encA : α ↪ List Bool} (DA : Decoder encA)
    (dA dB : Desc) (κA κB : ℕ → ℕ) (p : List Bool × ℕ) : Bool :=
  let w := p.1
  let N := p.2
  let u := dropFrame w
  if encA (DA.decode u) = u ∧ (simHeaderRun w w N).2 = true then
    if (simHeaderRun w w N).1.length ≤ u.length then
      !decide (universal (dB, (simHeaderRun w w N).1, κB N) = ([eBit true], true))
    else if !(collisionList DA w N).isEmpty then
      !decide (universal (dA, (Ladner.word ((collisionList DA w N).headD 0)).map eBit, κA N) =
        ([eBit true], true))
    else
      decide (universal (dA, u.map eBit, κA N) = ([eBit true], true))
  else
    false

private theorem computableInPolyTime_simHeaderRun :
    ComputableInPolyTime (fun p : (List Bool × List Bool) × ℕ => simHeaderRun p.1.1 p.1.2 p.2)
      (encPair (encPair encBits encBits) encUnary) eOut := by
  have hdesc : ComputableInPolyTime (fun w : List Bool => decodeDesc (unframe (unframe w)))
      encBits eDesc :=
    computableInPolyTime_decodeDesc.comp
      (ComputableInPolyTime.unframe.comp ComputableInPolyTime.unframe)
  have hmap : ComputableInPolyTime (fun x : List Bool => x.map eBit)
      encBits (encList encUnary) := computableInPolyTime_map_eBit
  have hp11 : ComputableInPolyTime (fun p : (List Bool × List Bool) × ℕ => p.1.1)
      (encPair (encPair encBits encBits) encUnary) encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp (.fst _ _)
  have hp12 : ComputableInPolyTime (fun p : (List Bool × List Bool) × ℕ => p.1.2)
      (encPair (encPair encBits encBits) encUnary) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp (.fst _ _)
  have hp2 : ComputableInPolyTime (fun p : (List Bool × List Bool) × ℕ => p.2)
      (encPair (encPair encBits encBits) encUnary) encUnary := .snd _ _
  exact (computableInPolyTime_universal.comp
    ((hdesc.comp hp11).prod ((hmap.comp hp12).prod hp2))).of_enc_eq fun p => by
      simp [simHeaderRun_eq]

private theorem computableInPolyTime_indexLookup :
    ComputableInPolyTime (fun p : List Bool × ℕ => indexLookup p.1 p.2)
      (encPair encBits encUnary) encUnary := by
  have hrange : ComputableInPolyTime (fun p : List Bool × ℕ => List.range p.2)
      (encPair encBits encUnary) (encList encUnary) :=
    ComputableInPolyTime.unary_range' (.snd encBits encUnary)
  have htest : ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ => decide (Ladner.word q.2 = q.1.1))
      (encPair (encPair encBits encUnary) encUnary) encBool :=
    ComputableInPolyTime.decide_eq'
      (Ladner.computableInPolyTime_word.comp (.snd _ _))
      ((ComputableInPolyTime.fst encBits encUnary).comp (.fst _ _))
  have hfilt := ComputableInPolyTime.filterWithInput
    (test := fun (p : List Bool × ℕ) (j : ℕ) => decide (Ladner.word j = p.1)) hrange htest
  exact ComputableInPolyTime.listHeadDWithInput hfilt (.const 0)

private theorem computableInPolyTime_collisionList {α : Type} {encA : α ↪ List Bool}
    (DA : Decoder encA) :
    ComputableInPolyTime (fun p : List Bool × ℕ => collisionList DA p.1 p.2)
      (encPair encBits encUnary) (encList encUnary) := by
  have hencA : ComputableInPolyTime (fun a : α => encA a) encA encBits := .of_eq fun _ => rfl
  have hdecA : ComputableInPolyTime DA.decode encBits encA := DA.computableInPolyTime
  have hcanon : ComputableInPolyTime (fun u : List Bool => encA (DA.decode u))
      encBits encBits := hencA.comp hdecA
  have hp1 : ComputableInPolyTime (fun p : List Bool × ℕ => p.1)
      (encPair encBits encUnary) encBits := .fst _ _
  have hp2 : ComputableInPolyTime (fun p : List Bool × ℕ => p.2)
      (encPair encBits encUnary) encUnary := .snd _ _
  have hidx : ComputableInPolyTime (fun p : List Bool × ℕ => indexLookup (dropFrame p.1) p.2)
      (encPair encBits encUnary) encUnary :=
    computableInPolyTime_indexLookup.comp ((ComputableInPolyTime.dropFrame.comp hp1).prod hp2)
  have hrange : ComputableInPolyTime
      (fun p : List Bool × ℕ => List.range (indexLookup (dropFrame p.1) p.2))
      (encPair encBits encUnary) (encList encUnary) :=
    ComputableInPolyTime.unary_range' hidx
  have hq1 : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => q.1.1)
      (encPair (encPair encBits encUnary) encUnary) encBits := hp1.comp (.fst _ _)
  have hqN : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => q.1.2)
      (encPair (encPair encBits encUnary) encUnary) encUnary := hp2.comp (.fst _ _)
  have hqj : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => q.2)
      (encPair (encPair encBits encUnary) encUnary) encUnary := .snd _ _
  have hwj : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => Ladner.word q.2)
      (encPair (encPair encBits encUnary) encUnary) encBits :=
    Ladner.computableInPolyTime_word.comp hqj
  have hcand : ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ => frame (unframe q.1.1) ++ Ladner.word q.2)
      (encPair (encPair encBits encUnary) encUnary) encBits :=
    ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.frame.comp (ComputableInPolyTime.unframe.comp hq1)) hwj
  have hsim1 : ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ =>
        simHeaderRun q.1.1 (frame (unframe q.1.1) ++ Ladner.word q.2) q.1.2)
      (encPair (encPair encBits encUnary) encUnary) eOut :=
    computableInPolyTime_simHeaderRun.comp ((hq1.prod hcand).prod hqN)
  have hsim2 : ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ => simHeaderRun q.1.1 q.1.1 q.1.2)
      (encPair (encPair encBits encUnary) encUnary) eOut :=
    computableInPolyTime_simHeaderRun.comp ((hq1.prod hq1).prod hqN)
  have hcanonW : ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ => encA (DA.decode (Ladner.word q.2)))
      (encPair (encPair encBits encUnary) encUnary) encBits :=
    hcanon.comp hwj
  have htest : ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ =>
        decide (encA (DA.decode (Ladner.word q.2)) = Ladner.word q.2) &&
          decide (simHeaderRun q.1.1 (frame (unframe q.1.1) ++ Ladner.word q.2) q.1.2 =
            simHeaderRun q.1.1 q.1.1 q.1.2))
      (encPair (encPair encBits encUnary) encUnary) encBool :=
    ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.decide_eq' hcanonW hwj)
      (ComputableInPolyTime.decide_eq' hsim1 hsim2)
  exact ComputableInPolyTime.filterWithInput
    (test := fun (p : List Bool × ℕ) (j : ℕ) =>
      decide (encA (DA.decode (Ladner.word j)) = Ladner.word j) &&
        decide (simHeaderRun p.1 (frame (unframe p.1) ++ Ladner.word j) p.2 =
          simHeaderRun p.1 p.1 p.2))
    hrange htest

private theorem computableInPolyTime_watanabeTest {α : Type} {encA : α ↪ List Bool}
    (DA : Decoder encA) (dA dB : Desc) {κA κB : ℕ → ℕ}
    (hκA : ComputableInPolyTime κA encUnary encUnary)
    (hκB : ComputableInPolyTime κB encUnary encUnary) :
    ComputableInPolyTime (watanabeTest DA dA dB κA κB) (encPair encBits encUnary) encBool := by
  have hencA : ComputableInPolyTime (fun a : α => encA a) encA encBits := .of_eq fun _ => rfl
  have hdecA : ComputableInPolyTime DA.decode encBits encA := DA.computableInPolyTime
  have hcanon : ComputableInPolyTime (fun u : List Bool => encA (DA.decode u))
      encBits encBits := hencA.comp hdecA
  have hp1 : ComputableInPolyTime (fun p : List Bool × ℕ => p.1)
      (encPair encBits encUnary) encBits := .fst _ _
  have hp2 : ComputableInPolyTime (fun p : List Bool × ℕ => p.2)
      (encPair encBits encUnary) encUnary := .snd _ _
  have hu : ComputableInPolyTime (fun p : List Bool × ℕ => dropFrame p.1)
      (encPair encBits encUnary) encBits := ComputableInPolyTime.dropFrame.comp hp1
  have hcanonU : ComputableInPolyTime (fun p : List Bool × ℕ => encA (DA.decode (dropFrame p.1)))
      (encPair encBits encUnary) encBits := hcanon.comp hu
  have hsim : ComputableInPolyTime (fun p : List Bool × ℕ => simHeaderRun p.1 p.1 p.2)
      (encPair encBits encUnary) eOut :=
    computableInPolyTime_simHeaderRun.comp ((hp1.prod hp1).prod hp2)
  have hsim1 : ComputableInPolyTime (fun p : List Bool × ℕ => (simHeaderRun p.1 p.1 p.2).1)
      (encPair encBits encUnary) (encList encUnary) := hsim.fst'
  have hsim2 : ComputableInPolyTime (fun p : List Bool × ℕ => (simHeaderRun p.1 p.1 p.2).2)
      (encPair encBits encUnary) encBool := hsim.snd'
  have hcoll := computableInPolyTime_collisionList DA
  have hhead : ComputableInPolyTime
      (fun p : List Bool × ℕ => (collisionList DA p.1 p.2).headD 0)
      (encPair encBits encUnary) encUnary :=
    ComputableInPolyTime.listHeadDWithInput hcoll (.const 0)
  have hempty : ComputableInPolyTime
      (fun p : List Bool × ℕ => (collisionList DA p.1 p.2).isEmpty)
      (encPair encBits encUnary) encBool :=
    (ComputableInPolyTime.listIsEmpty' encUnary).comp hcoll
  have hmap : ComputableInPolyTime (fun x : List Bool => x.map eBit)
      encBits (encList encUnary) := computableInPolyTime_map_eBit
  have hc1 : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        decide (encA (DA.decode (dropFrame p.1)) = dropFrame p.1 ∧
          (simHeaderRun p.1 p.1 p.2).2 = true))
      (encPair encBits encUnary) encBool :=
    ComputableInPolyTime.decide_and
      (ComputableInPolyTime.decide_eq' hcanonU hu)
      (ComputableInPolyTime.decide_eq' hsim2 (.const true))
  have hlen1 : ComputableInPolyTime (fun p : List Bool × ℕ => (simHeaderRun p.1 p.1 p.2).1.length)
      (encPair encBits encUnary) encUnary :=
    (ComputableInPolyTime.length_list encUnary).comp hsim1
  have hlen2 : ComputableInPolyTime (fun p : List Bool × ℕ => (dropFrame p.1).length)
      (encPair encBits encUnary) encUnary :=
    ComputableInPolyTime.length_bits_comp hu
  have hle_pt : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        decide ((simHeaderRun p.1 p.1 p.2).1.length ≤ (dropFrame p.1).length))
      (encPair encBits encUnary) encBool :=
    ComputableInPolyTime.unary_le' hlen1 hlen2
  have hunivB : ComputableInPolyTime
      (fun p : List Bool × ℕ => universal (dB, (simHeaderRun p.1 p.1 p.2).1, κB p.2))
      (encPair encBits encUnary) eOut :=
    computableInPolyTime_universal.comp
      ((ComputableInPolyTime.const dB).prod (hsim1.prod (hκB.comp hp2)))
  have hb1 : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        !decide (universal (dB, (simHeaderRun p.1 p.1 p.2).1, κB p.2) = ([eBit true], true)))
      (encPair encBits encUnary) encBool :=
    ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' hunivB (.const ([eBit true], true)))
  have hhead_map : ComputableInPolyTime
      (fun p : List Bool × ℕ => (Ladner.word ((collisionList DA p.1 p.2).headD 0)).map eBit)
      (encPair encBits encUnary) (encList encUnary) :=
    hmap.comp (Ladner.computableInPolyTime_word.comp hhead)
  have hunivA2 : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        universal (dA, (Ladner.word ((collisionList DA p.1 p.2).headD 0)).map eBit, κA p.2))
      (encPair encBits encUnary) eOut :=
    computableInPolyTime_universal.comp
      ((ComputableInPolyTime.const dA).prod (hhead_map.prod (hκA.comp hp2)))
  have hb2 : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        !decide (universal (dA, (Ladner.word ((collisionList DA p.1 p.2).headD 0)).map eBit,
          κA p.2) = ([eBit true], true)))
      (encPair encBits encUnary) encBool :=
    ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' hunivA2 (.const ([eBit true], true)))
  have hunivA3 : ComputableInPolyTime
      (fun p : List Bool × ℕ => universal (dA, (dropFrame p.1).map eBit, κA p.2))
      (encPair encBits encUnary) eOut :=
    computableInPolyTime_universal.comp
      ((ComputableInPolyTime.const dA).prod ((hmap.comp hu).prod (hκA.comp hp2)))
  have hb3 : ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        decide (universal (dA, (dropFrame p.1).map eBit, κA p.2) = ([eBit true], true)))
      (encPair encBits encUnary) encBool :=
    ComputableInPolyTime.decide_eq' hunivA3 (.const ([eBit true], true))
  exact ComputableInPolyTime.ite_decide hc1
    (ComputableInPolyTime.ite_decide hle_pt hb1
      (ComputableInPolyTime.ite (ComputableInPolyTime.bool_not.comp hempty) hb2 hb3))
    (.const false)

/-- **Core Berman–Watanabe reduction construction.** -/
private theorem polyTimeLengthIncreasingOneOneReducible_of_reducible {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (DA : Decoder encA) {gA : α → Bool} (hgA : ∀ a, a ∈ A ↔ gA a = true)
    {gB : β → Bool} (hgB : ∀ b, b ∈ B ↔ gB b = true) (dA dB : Desc)
    {κA κB G : ℕ → ℕ} {L : ℕ}
    (hGpow : ∀ n ≥ 1, 2 ^ n ≤ G n)
    (hdA : ∀ n ≥ L, ∀ a : α, (encA a).length ≤ n →
      universal (dA, (encA a).map eBit, κA (G n)) = ([eBit (gA a)], true))
    (hdB : ∀ n ≥ L, ∀ b : β, (encB b).length ≤ n →
      universal (dB, (encB b).map eBit, κB (G n)) = ([eBit (gB b)], true))
    (hG : ∀ t : ℕ → ℕ, PolynomiallyBounded t → ∀ᶠ n in Filter.atTop, t n ≤ G n)
    (hred : PolyTimeReducible encBits encB
      {w | watanabeTest DA dA dB κA κB (w, G w.length) = true} B) :
    PolyTimeLengthIncreasingOneOneReducible encA encB A B := by
  obtain ⟨r, hr, hrB⟩ := hred
  obtain ⟨t, _, ht, _, _, State, _, tm, htm⟩ := id hr
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  obtain ⟨kt, hkt⟩ := ht
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hkt
  let C₀ := listMax t (List.range (N₀ + 1))
  let tMono : ℕ → ℕ := fun n => C₀ + (n + 1) ^ kt
  have htMono_le (n : ℕ) : t n ≤ tMono n := by
    by_cases hn : N₀ ≤ n
    · have h1 : t n ≤ n ^ kt := hN₀ n hn
      have hpow : n ^ kt ≤ (n + 1) ^ kt := Nat.pow_le_pow_left (Nat.le_succ n) kt
      exact (h1.trans hpow).trans (Nat.le_add_left _ C₀)
    · have hmem : n ∈ List.range (N₀ + 1) := List.mem_range.mpr (by omega)
      exact (le_listMax hmem).trans (Nat.le_add_right C₀ _)
  have htMono_mono : Monotone tMono := fun m n hmn => by
    dsimp only [tMono]
    exact Nat.add_le_add_left (Nat.pow_le_pow_left (Nat.add_le_add_right hmn 1) kt) C₀
  have htMono_poly : PolynomiallyBounded tMono := by
    dsimp only [tMono]
    fun_prop
  have hrun (x : List Bool) :
      (tm.runFrom (tm.initCfg x) (tMono x.length)).Halted ∧
        (tm.runFrom (tm.initCfg x) (tMono x.length)).output = encB (r x) :=
    (htm x).runFrom_of_le (htMono_le x.length)
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hG tMono htMono_poly)
  let M := max (max M₁ L) 1
  let hdr₀ : List Bool := frame (eDesc (desc eS eBit tm)) ++ List.replicate M false
  let wOf : α → List Bool := fun a => frame hdr₀ ++ encA a
  let f : α → β := fun a => r (wOf a)
  have hwOf_len (a : α) : M + (encA a).length < (wOf a).length := by
    simp only [wOf, hdr₀, List.length_append, length_frame, List.length_replicate]
    omega
  have hwOf_ge_M₁ (a : α) : M₁ ≤ (wOf a).length := by
    have := hwOf_len a
    have : M₁ ≤ M := le_trans (le_max_left M₁ L) (le_max_left _ 1)
    omega
  have hwOf_ge_L (a : α) : L ≤ (wOf a).length := by
    have := hwOf_len a
    have : L ≤ M := le_trans (le_max_right M₁ L) (le_max_left _ 1)
    omega
  have hwOf_pos (a : α) : 1 ≤ (wOf a).length := by
    have := hwOf_len a
    have : 1 ≤ M := le_max_right _ 1
    omega
  have hunframe_wOf (a : α) : unframe (wOf a) = hdr₀ := by
    simp only [wOf, unframe_frame_append]
  have hdrop_wOf (a : α) : dropFrame (wOf a) = encA a := by
    simp only [wOf, dropFrame_frame_append]
  have hdecode_hdr₀ : decodeDesc (unframe hdr₀) = desc eS eBit tm := by
    simp only [hdr₀, decodeDesc_unframe_frame_append]
  have hsim_pair (a a' : α) (hlen : (encA a').length ≤ (encA a).length) :
      simHeaderRun (wOf a) (wOf a') (G (wOf a).length) = ((encB (f a')).map eBit, true) := by
    rw [simHeaderRun_eq, hunframe_wOf, hdecode_hdr₀]
    have hlen_w : (wOf a').length ≤ (wOf a).length := by
      simp only [wOf, List.length_append]
      omega
    have ht_le : tMono (wOf a').length ≤ G (wOf a).length :=
      (htMono_mono hlen_w).trans (hM₁ (wOf a).length (hwOf_ge_M₁ a))
    exact Ladner.universal_desc_of_halted_map eS tm (f := fun x => encB (r x))
      (t := fun x => tMono x.length) hrun ht_le
  have hsim_self (a : α) :
      simHeaderRun (wOf a) (wOf a) (G (wOf a).length) = ((encB (f a)).map eBit, true) :=
    hsim_pair a a le_rfl
  have hidx_lt (a : α) : Ladner.index (encA a) < G (wOf a).length := by
    have h1 := Ladner.index_add_two_le (encA a)
    have h2 : (encA a).length + 1 ≤ (wOf a).length := by
      have := hwOf_len a
      have : 1 ≤ M := le_max_right _ 1
      omega
    have h3 : 2 ^ ((encA a).length + 1) ≤ 2 ^ (wOf a).length :=
      Nat.pow_le_pow_right (by norm_num) h2
    have h4 := hGpow (wOf a).length (hwOf_pos a)
    omega
  have hlong (a : α) : (encA a).length < (encB (f a)).length := by
    by_contra! hle
    have hmem :
        (wOf a ∈ {w | watanabeTest DA dA dB κA κB (w, G w.length) = true}) ↔ f a ∈ B :=
      hrB (wOf a)
    have hdB_eval :
        universal (dB, (encB (f a)).map eBit, κB (G (wOf a).length)) =
          ([eBit (gB (f a))], true) :=
      hdB (wOf a).length (hwOf_ge_L a) (f a)
        (hle.trans (by simp only [wOf, List.length_append]; omega))
    simp only [Set.mem_ofPred_eq, watanabeTest, hdrop_wOf, DA.decode_enc, hsim_self a,
      ↓reduceIte, List.length_map, hle, hdB_eval, hgB] at hmem
    rcases hgb : gB (f a) with _ | _ <;> simp [hgb, eBit] at hmem
  have hcoll_spec (a : α) :
      collisionList DA (wOf a) (G (wOf a).length) =
        (List.range (Ladner.index (encA a))).filter fun j =>
          decide (encA (DA.decode (Ladner.word j)) = Ladner.word j) &&
            decide (simHeaderRun (wOf a) (frame hdr₀ ++ Ladner.word j) (G (wOf a).length) =
              ((encB (f a)).map eBit, true)) := by
    simp only [collisionList, hdrop_wOf, indexLookup_eq_index (hidx_lt a), hunframe_wOf,
      hsim_self a]
  have hpred_iff (a : α) {j : ℕ} (hj : j < Ladner.index (encA a)) :
      (decide (encA (DA.decode (Ladner.word j)) = Ladner.word j) &&
        decide (simHeaderRun (wOf a) (frame hdr₀ ++ Ladner.word j) (G (wOf a).length) =
          ((encB (f a)).map eBit, true))) = true ↔
        ∃ a' : α, Ladner.index (encA a') = j ∧ f a' = f a := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hcan, hsimj⟩
      let a' := DA.decode (Ladner.word j)
      have henc' : encA a' = Ladner.word j := hcan
      have hlen' : (encA a').length ≤ (encA a).length := by
        rw [henc']
        exact length_word_le_of_lt_index hj
      have hwOf' : frame hdr₀ ++ Ladner.word j = wOf a' := by
        simp only [wOf, henc']
      rw [hwOf', hsim_pair a a' hlen', Prod.mk.injEq] at hsimj
      have hmap_eq := List.map_injective_iff.mpr eBit.injective hsimj.1
      exact ⟨a', by rw [henc', Ladner.index_word], encB.injective hmap_eq⟩
    · rintro ⟨a', hidx', hfa'⟩
      have hwj : Ladner.word j = encA a' := by
        rw [← hidx', Ladner.word_index]
      have hlen' : (encA a').length ≤ (encA a).length := by
        rw [← hwj]
        exact length_word_le_of_lt_index hj
      refine ⟨by rw [hwj, DA.decode_enc], ?_⟩
      rw [hwj, show frame hdr₀ ++ encA a' = wOf a' from rfl, hsim_pair a a' hlen', hfa']
  have hinj : Function.Injective f := by
    intro a₁ a₂ hfa
    by_contra hne
    classical
    let P : ℕ → Prop := fun j => ∃ a' : α, Ladner.index (encA a') = j ∧ f a' = f a₁
    have hP_ex : ∃ j, P j := ⟨Ladner.index (encA a₁), a₁, rfl, rfl⟩
    let j₀ := Nat.find hP_ex
    obtain ⟨a₀, hj₀_eq, hfa₀⟩ := Nat.find_spec hP_ex
    have hj₀_min : ∀ j < j₀, ¬ P j := fun j hj => Nat.find_min hP_ex hj
    obtain ⟨a, ha_ne, hfa_eq⟩ : ∃ a : α, a ≠ a₀ ∧ f a = f a₀ := by
      by_cases h1 : a₁ = a₀
      · exact ⟨a₂, fun h2 => hne (h1.trans h2.symm), hfa.symm.trans hfa₀.symm⟩
      · exact ⟨a₁, h1, hfa₀.symm⟩
    have hj₀_le : j₀ ≤ Ladner.index (encA a) :=
      Nat.find_min' hP_ex ⟨a, rfl, hfa_eq.trans hfa₀⟩
    have hj₀_ne : j₀ ≠ Ladner.index (encA a) := by
      intro heq
      have hidx_eq : Ladner.index (encA a₀) = Ladner.index (encA a) := hj₀_eq.trans heq
      have hw_eq : encA a₀ = encA a := by
        simpa only [Ladner.word_index] using congrArg Ladner.word hidx_eq
      exact ha_ne (encA.injective hw_eq.symm)
    have hj₀_lt : j₀ < Ladner.index (encA a) := Nat.lt_of_le_of_ne hj₀_le hj₀_ne
    have hcoll_a₀ : collisionList DA (wOf a₀) (G (wOf a₀).length) = [] := by
      rw [hcoll_spec a₀, List.filter_eq_nil_iff]
      intro j hj
      have hj_lt : j < Ladner.index (encA a₀) := List.mem_range.mp hj
      have hj_lt_j₀ : j < j₀ := by dsimp only [j₀]; omega
      intro htrue
      obtain ⟨a', hidx', hfa'⟩ := (hpred_iff a₀ hj_lt).mp htrue
      exact hj₀_min j hj_lt_j₀ ⟨a', hidx', hfa'.trans hfa₀⟩
    have hB_a₀ : f a₀ ∈ B ↔ gA a₀ = true := by
      have hmem :
          f a₀ ∈ B ↔ (wOf a₀ ∈ {w | watanabeTest DA dA dB κA κB (w, G w.length) = true}) :=
        (hrB (wOf a₀)).symm
      have hdA_a₀ :
          universal (dA, (encA a₀).map eBit, κA (G (wOf a₀).length)) =
            ([eBit (gA a₀)], true) :=
        hdA (wOf a₀).length (hwOf_ge_L a₀) a₀
          (by simp only [wOf, List.length_append]; omega)
      simp only [Set.mem_ofPred_eq, watanabeTest, hdrop_wOf, DA.decode_enc, hsim_self a₀,
        ↓reduceIte, List.length_map, not_le.mpr (hlong a₀), hcoll_a₀, List.isEmpty_nil,
        Bool.not_true, Bool.false_eq_true, hdA_a₀] at hmem
      rcases hga : gA a₀ with _ | _ <;> simpa [hga, eBit] using hmem
    have hcoll_a :
        (collisionList DA (wOf a) (G (wOf a).length)).isEmpty = false ∧
          (collisionList DA (wOf a) (G (wOf a).length)).headD 0 = j₀ := by
      rw [hcoll_spec a]
      refine filter_range_first hj₀_lt ?_ ?_
      · exact (hpred_iff a hj₀_lt).mpr ⟨a₀, hj₀_eq, hfa_eq.symm⟩
      · intro j hj
        apply Bool.eq_false_iff.mpr
        intro htrue
        obtain ⟨a', hidx', hfa'⟩ := (hpred_iff a (hj.trans hj₀_lt)).mp htrue
        exact hj₀_min j hj ⟨a', hidx', hfa'.trans (hfa_eq.trans hfa₀)⟩
    have hB_a : f a ∈ B ↔ gA a₀ = false := by
      have hmem :
          f a ∈ B ↔ (wOf a ∈ {w | watanabeTest DA dA dB κA κB (w, G w.length) = true}) :=
        (hrB (wOf a)).symm
      have hword_j₀ : Ladner.word j₀ = encA a₀ := by
        rw [show j₀ = Ladner.index (encA a₀) from hj₀_eq.symm, Ladner.word_index]
      have hlen_a₀ : (encA a₀).length ≤ (wOf a).length := by
        have := length_word_le_of_lt_index hj₀_lt
        rw [hword_j₀] at this
        exact this.trans (by simp only [wOf, List.length_append]; omega)
      have hdA_a :
          universal (dA, (encA a₀).map eBit, κA (G (wOf a).length)) =
            ([eBit (gA a₀)], true) :=
        hdA (wOf a).length (hwOf_ge_L a) a₀ hlen_a₀
      simp only [Set.mem_ofPred_eq, watanabeTest, hdrop_wOf, DA.decode_enc, hsim_self a,
        ↓reduceIte, List.length_map, not_le.mpr (hlong a), hcoll_a.1, Bool.not_false,
        hcoll_a.2, hword_j₀, hdA_a] at hmem
      rcases hga : gA a₀ with _ | _ <;> simpa [hga, eBit] using hmem
    rw [hfa_eq, hB_a₀] at hB_a
    rcases hga : gA a₀ with _ | _ <;> simp [hga] at hB_a
  have hf_poly : ComputableInPolyTime f encA encB :=
    hr.comp (ComputableInPolyTime.bitsAppend (.const (frame hdr₀)) (.of_eq fun _ => rfl))
  refine ⟨f, ⟨hf_poly, hinj, hlong⟩, fun a => ?_⟩
  have hcoll_empty : collisionList DA (wOf a) (G (wOf a).length) = [] := by
    rw [hcoll_spec a, List.filter_eq_nil_iff]
    intro j hj
    rw [List.mem_range] at hj
    intro htrue
    obtain ⟨a', hidx', hfa'⟩ := (hpred_iff a hj).mp htrue
    have heq := hinj hfa'
    subst heq
    omega
  have hmem :
      (wOf a ∈ {w | watanabeTest DA dA dB κA κB (w, G w.length) = true}) ↔ f a ∈ B :=
    hrB (wOf a)
  have hdA_a :
      universal (dA, (encA a).map eBit, κA (G (wOf a).length)) = ([eBit (gA a)], true) :=
    hdA (wOf a).length (hwOf_ge_L a) a (by simp only [wOf, List.length_append]; omega)
  simp only [Set.mem_ofPred_eq, watanabeTest, hdrop_wOf, DA.decode_enc, hsim_self a,
    ↓reduceIte, List.length_map, not_le.mpr (hlong a), hcoll_empty, List.isEmpty_nil,
    Bool.not_true, Bool.false_eq_true, hdA_a] at hmem
  rw [hgA a, ← hmem]
  rcases hga : gA a with _ | _ <;> simp [eBit]

/-- **Berman–Watanabe length-increasing completeness for `E`**: every problem `(A, encA)` in `E`
equipped with a total polynomial-time decoder `DA` reduces via a length-increasing one-one
polynomial-time map to every `E`-complete problem `(B, encB)`. -/
theorem polyTimeLengthIncreasingOneOneReducible_of_polyTimeComplete_E {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (DA : Decoder encA) (hA : A ∈ E encA) (hB : PolyTimeComplete @E encB B) :
    PolyTimeLengthIncreasingOneOneReducible encA encB A B := by
  obtain ⟨kA, cA₁, cA₂, _, hdecA⟩ := mem_E_iff.mp hA
  obtain ⟨gA, ⟨_, StateA, _, tmA, htmA⟩, hgA⟩ := decidableInTimeAndSpace_iff.mp hdecA
  have := Fintype.ofFinite StateA
  let eSA : StateA ↪ ℕ := (Fintype.equivFin StateA).toEmbedding.trans Fin.valEmbedding
  obtain ⟨kB, cB₁, cB₂, _, hdecB⟩ := mem_E_iff.mp hB.1
  obtain ⟨gB, ⟨_, StateB, _, tmB, htmB⟩, hgB⟩ := decidableInTimeAndSpace_iff.mp hdecB
  have := Fintype.ofFinite StateB
  let eSB : StateB ↪ ℕ := (Fintype.equivFin StateB).toEmbedding.trans Fin.valEmbedding
  refine polyTimeLengthIncreasingOneOneReducible_of_reducible DA hgA hgB
    (desc eSA eBit tmA) (desc eSB eBit tmB)
    (κA := fun N => cA₁ * N ^ kA + cA₂) (κB := fun N => cB₁ * N ^ kB + cB₂)
    (G := fun n => 2 ^ n) (L := 0)
    (fun _ _ => le_rfl)
    (fun n _ a ha => ?_)
    (fun n _ b hb => ?_)
    (fun t ht => (PolynomiallyBounded.eventually_lt_two_pow ht).mono fun _ => le_of_lt)
    (hB.2 encBits _ (setOf_mem_E_of_computableInPolyTime_pad
      (computableInPolyTime_watanabeTest DA _ _ (by fun_prop) (by fun_prop))))
  · have hT : cA₁ * 2 ^ (kA * (encA a).length) + cA₂ ≤ cA₁ * (2 ^ n) ^ kA + cA₂ := by
      rw [← pow_mul, mul_comm n kA]
      gcongr
    obtain ⟨hhalt, hout⟩ := (htmA a).runFrom_of_le hT
    simp only [Cfg.Halted] at hhalt
    rw [universal_desc, hout, hhalt]
    rfl
  · have hT : cB₁ * 2 ^ (kB * (encB b).length) + cB₂ ≤ cB₁ * (2 ^ n) ^ kB + cB₂ := by
      rw [← pow_mul, mul_comm n kB]
      gcongr
    obtain ⟨hhalt, hout⟩ := (htmB b).runFrom_of_le hT
    simp only [Cfg.Halted] at hhalt
    rw [universal_desc, hout, hhalt]
    rfl

/-- **Berman–Watanabe length-increasing completeness for `EXP`**: every problem `(A, encA)` in
`EXP` equipped with a total polynomial-time decoder `DA` reduces via a length-increasing one-one
polynomial-time map to every `EXP`-complete problem `(B, encB)`. -/
theorem polyTimeLengthIncreasingOneOneReducible_of_polyTimeComplete_EXP {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (DA : Decoder encA) (hA : A ∈ EXP encA) (hB : PolyTimeComplete @EXP encB B) :
    PolyTimeLengthIncreasingOneOneReducible encA encB A B := by
  obtain ⟨kA, cA₁, cA₂, _, hdecA⟩ := mem_EXP_iff.mp hA
  obtain ⟨gA, ⟨_, StateA, _, tmA, htmA⟩, hgA⟩ := decidableInTimeAndSpace_iff.mp hdecA
  have := Fintype.ofFinite StateA
  let eSA : StateA ↪ ℕ := (Fintype.equivFin StateA).toEmbedding.trans Fin.valEmbedding
  obtain ⟨kB, cB₁, cB₂, _, hdecB⟩ := mem_EXP_iff.mp hB.1
  obtain ⟨gB, ⟨_, StateB, _, tmB, htmB⟩, hgB⟩ := decidableInTimeAndSpace_iff.mp hdecB
  have := Fintype.ofFinite StateB
  let eSB : StateB ↪ ℕ := (Fintype.equivFin StateB).toEmbedding.trans Fin.valEmbedding
  let k := max kA kB
  refine polyTimeLengthIncreasingOneOneReducible_of_reducible DA hgA hgB
    (desc eSA eBit tmA) (desc eSB eBit tmB)
    (κA := fun N => cA₁ * N + cA₂) (κB := fun N => cB₁ * N + cB₂)
    (G := fun n => 2 ^ (n ^ (k + 1) + 1)) (L := 1)
    (fun n _ => Nat.pow_le_pow_right (by norm_num)
      ((Nat.le_self_pow k.succ_ne_zero n).trans (Nat.le_add_right _ 1)))
    (fun n hn a ha => ?_)
    (fun n hn b hb => ?_)
    (fun t ht => (PolynomiallyBounded.eventually_lt_two_pow ht).mono fun n hn =>
      hn.le.trans (Nat.pow_le_pow_right (by norm_num)
        ((Nat.le_self_pow k.succ_ne_zero n).trans (Nat.le_add_right _ 1))))
    (hB.2 encBits _ (setOf_mem_EXP_of_computableInPolyTime_pad
      (computableInPolyTime_watanabeTest DA _ _ (by fun_prop) (by fun_prop))
      (L := fun w => w.length ^ (k + 1) + 1) (by fun_prop)))
  · have hkA : kA ≤ k + 1 := (le_max_left kA kB).trans (Nat.le_succ k)
    have hexp : (encA a).length ^ kA ≤ n ^ (k + 1) + 1 :=
      ((Nat.pow_le_pow_left ha kA).trans (Nat.pow_le_pow_right hn hkA)).trans
        (Nat.le_add_right _ 1)
    have hT : cA₁ * 2 ^ (encA a).length ^ kA + cA₂ ≤ cA₁ * 2 ^ (n ^ (k + 1) + 1) + cA₂ :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp)) _
    obtain ⟨hhalt, hout⟩ := (htmA a).runFrom_of_le hT
    simp only [Cfg.Halted] at hhalt
    rw [universal_desc, hout, hhalt]
    rfl
  · have hkB : kB ≤ k + 1 := (le_max_right kA kB).trans (Nat.le_succ k)
    have hexp : (encB b).length ^ kB ≤ n ^ (k + 1) + 1 :=
      ((Nat.pow_le_pow_left hb kB).trans (Nat.pow_le_pow_right hn hkB)).trans
        (Nat.le_add_right _ 1)
    have hT : cB₁ * 2 ^ (encB b).length ^ kB + cB₂ ≤ cB₁ * 2 ^ (n ^ (k + 1) + 1) + cB₂ :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp)) _
    obtain ⟨hhalt, hout⟩ := (htmB b).runFrom_of_le hT
    simp only [Cfg.Halted] at hhalt
    rw [universal_desc, hout, hhalt]
    rfl

/-- Any two `E`-complete problems over types with total polynomial-time decoders are
length-increasing one-one equivalent (`A ≡₁^{li} B`). -/
theorem eComplete_polyTimeLengthIncreasingOneOneEquiv {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (DA : Decoder encA) (DB : Decoder encB)
    (hA : PolyTimeComplete @E encA A) (hB : PolyTimeComplete @E encB B) :
    PolyTimeLengthIncreasingOneOneEquiv encA encB A B :=
  ⟨polyTimeLengthIncreasingOneOneReducible_of_polyTimeComplete_E DA hA.1 hB,
    polyTimeLengthIncreasingOneOneReducible_of_polyTimeComplete_E DB hB.1 hA⟩

/-- **Watanabe's theorem**: any two `EXP`-complete problems over types with
total polynomial-time decoders are length-increasing one-one equivalent (`A ≡₁^{li} B`).
-/
theorem expComplete_polyTimeLengthIncreasingOneOneEquiv {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (DA : Decoder encA) (DB : Decoder encB)
    (hA : PolyTimeComplete @EXP encA A) (hB : PolyTimeComplete @EXP encB B) :
    PolyTimeLengthIncreasingOneOneEquiv encA encB A B :=
  ⟨polyTimeLengthIncreasingOneOneReducible_of_polyTimeComplete_EXP DA hA.1 hB,
    polyTimeLengthIncreasingOneOneReducible_of_polyTimeComplete_EXP DB hB.1 hA⟩

/-- **Watanabe's theorem on bit-word languages (`encBits`)**: any two `EXP`-complete languages of
bit strings satisfy `A ≤₁^{li} B` and `B ≤₁^{li} A`. -/
theorem expComplete_polyTimeLengthIncreasingOneOneEquiv_bits {A B : Set (List Bool)}
    (hA : PolyTimeComplete @EXP encBits A) (hB : PolyTimeComplete @EXP encBits B) :
    PolyTimeLengthIncreasingOneOneEquiv encBits encBits A B :=
  expComplete_polyTimeLengthIncreasingOneOneEquiv Decoder.bits Decoder.bits hA hB

/-! ### Paddable complete languages for `EXP` and `PSPACE` -/

/-- Any two paddable `EXP`-complete problems with total polynomial-time decoders are
polynomial-time invertible length-increasing one-one equivalent. -/
theorem expComplete_polyTimeInvertibleLengthIncreasingOneOneEquiv_of_paddable {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hA : PolyTimeComplete @EXP encA A) (hB : PolyTimeComplete @EXP encB B)
    (hpA : Paddable encA A) (hpB : Paddable encB B)
    (DA : Decoder encA) (DB : Decoder encB) :
    PolyTimeInvertibleLengthIncreasingOneOneEquiv encA encB A B :=
  ⟨hpB.polyTimeInvertibleLengthIncreasingOneOneReducible DA (hB.2 encA A hA.1),
    hpA.polyTimeInvertibleLengthIncreasingOneOneReducible DB (hA.2 encB B hB.1)⟩

/-- Any two paddable `EXP`-complete problems with total polynomial-time decoders are
polynomial-time isomorphic. -/
theorem expComplete_polyTimeIsomorphic_of_paddable {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hA : PolyTimeComplete @EXP encA A) (hB : PolyTimeComplete @EXP encB B)
    (hpA : Paddable encA A) (hpB : Paddable encB B)
    (DA : Decoder encA) (DB : Decoder encB) :
    PolyTimeIsomorphic encA encB A B :=
  (expComplete_polyTimeInvertibleLengthIncreasingOneOneEquiv_of_paddable hA hB hpA hpB DA
    DB).polyTimeIsomorphic

/-- Any two paddable `PSPACE`-complete problems with total polynomial-time decoders are
polynomial-time invertible length-increasing one-one equivalent. -/
theorem pspaceComplete_polyTimeInvertibleLengthIncreasingOneOneEquiv_of_paddable {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hA : PSPACEComplete encA A) (hB : PSPACEComplete encB B)
    (hpA : Paddable encA A) (hpB : Paddable encB B)
    (DA : Decoder encA) (DB : Decoder encB) :
    PolyTimeInvertibleLengthIncreasingOneOneEquiv encA encB A B :=
  ⟨hpB.polyTimeInvertibleLengthIncreasingOneOneReducible DA (hB.2 encA A hA.1),
    hpA.polyTimeInvertibleLengthIncreasingOneOneReducible DB (hA.2 encB B hB.1)⟩

/-- Any two paddable `PSPACE`-complete problems with total polynomial-time decoders are
polynomial-time isomorphic. -/
theorem pspaceComplete_polyTimeIsomorphic_of_paddable {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hA : PSPACEComplete encA A) (hB : PSPACEComplete encB B)
    (hpA : Paddable encA A) (hpB : Paddable encB B)
    (DA : Decoder encA) (DB : Decoder encB) :
    PolyTimeIsomorphic encA encB A B :=
  (pspaceComplete_polyTimeInvertibleLengthIncreasingOneOneEquiv_of_paddable hA hB hpA hpB DA
    DB).polyTimeIsomorphic

end CslibFrontier.Complexity
