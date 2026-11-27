module

public import CslibFrontier.Computability.Automata.PebbleAutomaton
public import CslibFrontier.Computability.Complexity.SyntacticMorphism

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-!
# Inverse-Morphism Invariance of the Pebble Hierarchy

This module proves that every level `REG k` (`k ≥ 0`) of the pebble hierarchy is closed under
inverse images of syntactic morphisms (including erasing morphisms), so `REG` forms an invariant
hierarchy. All results are proved under standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Main results

* `CslibFrontier.Computability.Automata.mem_REG_of_syntacticReducible`: Each `REG k` is closed under
  inverse syntactic morphisms.
* `CslibFrontier.Computability.Automata.isInvariantHierarchy_REG`: `REG` is an invariant hierarchy.
-/

public section

namespace CslibFrontier.Computability.Automata

open CslibFrontier.Computability.Complexity

universe u

/-! ### Part 1: Invariance of `REG k` under inverse syntactic morphisms -/

section SyntacticInvariance

private inductive SimMode (m : ℕ) where
  | sim (offset : Option (Fin m))
  | scanRight
  | scanLeft
  deriving DecidableEq

private instance instFintypeSimMode (m : ℕ) : Fintype (SimMode m) := by
  let e : SimMode m ≃ Option (Fin m) ⊕ Unit ⊕ Unit :=
    { toFun := fun
        | .sim o => Sum.inl o
        | .scanRight => Sum.inr (Sum.inl ())
        | .scanLeft => Sum.inr (Sum.inr ())
      invFun := fun
        | Sum.inl o => .sim o
        | Sum.inr (Sum.inl ()) => .scanRight
        | Sum.inr (Sum.inr ()) => .scanLeft
      left_inv := fun x ↦ by cases x <;> rfl
      right_inv := fun x ↦ by rcases x with _ | ⟨⟨⟩ | ⟨⟩⟩ <;> rfl }
  exact Fintype.ofEquiv _ e.symm

private abbrev SimState (Q : Type*) (k m : ℕ) :=
  Q × (Fin k → Option (Fin m)) × SimMode m

private def maxImgLen {α β : Type*} [Fintype α] (f : α → List β) : ℕ :=
  1 + Finset.univ.sup fun a ↦ (f a).length

private theorem length_lt_maxImgLen {α β : Type*} [Fintype α] (f : α → List β) (a : α) :
    (f a).length < maxImgLen f := by
  have hle : (f a).length ≤ Finset.univ.sup fun x ↦ (f x).length :=
    Finset.le_sup (f := fun x ↦ (f x).length) (Finset.mem_univ a)
  unfold maxImgLen
  omega

private def blockStart {α β : Type*} (f : α → List β) (w : List α) (i : ℕ) : ℕ :=
  (syntacticMorphism f (w.take i)).length

private theorem blockStart_zero {α β : Type*} (f : α → List β) (w : List α) :
    blockStart f w 0 = 0 := by
  simp [blockStart]

private theorem blockStart_succ {α β : Type*} (f : α → List β) (w : List α)
    {i : ℕ} (hi : i < w.length) :
    blockStart f w (i + 1) = blockStart f w i + (f (w.get ⟨i, hi⟩)).length := by
  unfold blockStart
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, syntacticMorphism_append, syntacticMorphism_singleton,
    List.length_append, List.get_eq_getElem]

private theorem blockStart_length {α β : Type*} (f : α → List β) (w : List α) :
    blockStart f w w.length = (syntacticMorphism f w).length := by
  simp [blockStart]

private theorem blockStart_mono {α β : Type*} (f : α → List β) (w : List α)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length) :
    blockStart f w a ≤ blockStart f w b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
    have hlt : a + d < w.length := by omega
    have hs := blockStart_succ f w hlt
    have hle := ih (by omega)
    have : a + (d + 1) = a + d + 1 := by omega
    rw [this, hs]
    omega

private theorem get_syntacticMorphism_block {α β : Type*} (f : α → List β) (w : List α)
    {i j : ℕ} (hi : i < w.length) (hj : j < (f (w.get ⟨i, hi⟩)).length) :
    (syntacticMorphism f w).get
        ⟨blockStart f w i + j, by
          have h1 := blockStart_succ f w hi
          have h2 : blockStart f w (i + 1) ≤ (syntacticMorphism f w).length := by
            rw [← blockStart_length]
            exact blockStart_mono f w (by omega) le_rfl
          omega⟩ = (f (w.get ⟨i, hi⟩)).get ⟨j, hj⟩ := by
  have hsplit : syntacticMorphism f w =
      syntacticMorphism f (w.take i) ++ f (w.get ⟨i, hi⟩) ++
        syntacticMorphism f (w.drop (i + 1)) := by
    have hw : w = w.take i ++ [w.get ⟨i, hi⟩] ++ w.drop (i + 1) := by
      have h1 : w.take (i + 1) = w.take i ++ [w.get ⟨i, hi⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]
        simp only [Option.toList_some, List.get_eq_getElem]
      rw [← h1, List.take_append_drop]
    conv_lhs => rw [hw]
    rw [syntacticMorphism_append, syntacticMorphism_append, syntacticMorphism_singleton]
  have hidx : blockStart f w i + j <
      (syntacticMorphism f (w.take i) ++ f (w.get ⟨i, hi⟩)).length := by
    simp only [blockStart, List.length_append]
    omega
  have hget1 :
      (syntacticMorphism f w)[blockStart f w i + j]'(by rw [hsplit, List.length_append]; omega) =
      (syntacticMorphism f (w.take i) ++ f (w.get ⟨i, hi⟩))[blockStart f w i + j]'hidx := by
    have hcongr : ∀ {l₁ l₂ : List β} (hl : l₁ = l₂) (n : ℕ) (hn : n < l₁.length),
        l₁[n]'hn = l₂[n]'(hl ▸ hn) := by rintro _ _ rfl _ _; rfl
    rw [hcongr hsplit, List.getElem_append_left hidx]
  simp only [List.get_eq_getElem]
  rw [hget1]
  have hge : (syntacticMorphism f (w.take i)).length ≤ blockStart f w i + j := by
    simp [blockStart]
  rw [List.getElem_append_right hge]
  simp [blockStart]

private def simAutomaton {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) :
    PebbleAutomaton k α (SimState Q k (maxImgLen f)) :=
  let m := maxImgLen f
  { q₀ := (M.q₀, fun _ ↦ none, .sim none)
    halting := {s | s.1 ∈ M.halting ∧ match s.2.2 with | .sim _ => True | _ => False}
    accepting := {s | s.1 ∈ M.accepting ∧ match s.2.2 with | .sim _ => True | _ => False}
    accepting_subset_halting := fun _ hs ↦ ⟨M.accepting_subset_halting hs.1, hs.2⟩
    δ := fun s sym A B ↦
      let q := s.1
      let pebOff := s.2.1
      let mode := s.2.2
      match mode with
      | .scanRight =>
        match sym with
        | .leftEnd => ((q, pebOff, .scanRight), ∅, A ∪ B, .right)
        | .rightEnd => ((q, pebOff, .sim none), ∅, A ∪ B, .stay)
        | .sym a =>
          if hlen : 0 < (f a).length then
            ((q, pebOff, .sim (some ⟨0, lt_trans hlen (length_lt_maxImgLen f a)⟩)),
              A, B, .stay)
          else
            ((q, pebOff, .scanRight), A, B, .right)
      | .scanLeft =>
        match sym with
        | .leftEnd => ((q, pebOff, .sim none), ∅, A ∪ B, .stay)
        | .rightEnd => ((q, pebOff, .scanLeft), ∅, A ∪ B, .left)
        | .sym a =>
          if hlen : 0 < (f a).length then
            ((q, pebOff, .sim (some ⟨(f a).length - 1,
                lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f a)⟩)),
              A, B, .stay)
          else
            ((q, pebOff, .scanLeft), A, B, .left)
      | .sim off =>
        match sym with
        | .leftEnd =>
          let res := M.δ q .leftEnd ∅ B
          let mode' : SimMode m := match res.2.2.2 with
            | .left => .sim none
            | .stay => .sim none
            | .right => .scanRight
          ((res.1, pebOff, mode'), ∅, A ∪ B, res.2.2.2)
        | .rightEnd =>
          let res := M.δ q .rightEnd ∅ B
          let mode' : SimMode m := match res.2.2.2 with
            | .left => .scanLeft
            | .stay => .sim none
            | .right => .sim none
          ((res.1, pebOff, mode'), ∅, A ∪ B, res.2.2.2)
        | .sym a =>
          match off with
          | none => ((q, pebOff, .sim none), A, B, .stay)
          | some j =>
            if hj : j.val < (f a).length then
              let AM := A.filter fun r ↦ pebOff r = some j
              let Aother := A.filter fun r ↦ pebOff r ≠ some j
              let res := M.δ q (.sym ((f a).get ⟨j.val, hj⟩)) AM B
              let CM := res.2.1
              let DM := res.2.2.1
              let pebOff' : Fin k → Option (Fin m) := fun r ↦
                if r ∈ CM then some j else if r ∈ DM then none else pebOff r
              match res.2.2.2 with
              | .stay =>
                ((res.1, pebOff', .sim (some j)), CM ∪ Aother, DM, .stay)
              | .right =>
                if hj' : j.val + 1 < (f a).length then
                  ((res.1, pebOff', .sim (some ⟨j.val + 1,
                      lt_trans hj' (length_lt_maxImgLen f a)⟩)),
                    CM ∪ Aother, DM, .stay)
                else
                  ((res.1, pebOff', .scanRight), CM ∪ Aother, DM, .right)
              | .left =>
                if hj' : 0 < j.val then
                  ((res.1, pebOff', .sim (some ⟨j.val - 1,
                      lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩)),
                    CM ∪ Aother, DM, .stay)
                else
                  ((res.1, pebOff', .scanLeft), CM ∪ Aother, DM, .left)
            else
              ((q, pebOff, .sim (some j)), A, B, .stay)
    pebble_disjoint := by
      intro s sym A B hAB
      rcases s with ⟨q, pebOff, mode⟩
      cases mode with
      | scanRight =>
        cases sym with
        | leftEnd => exact Finset.disjoint_empty_left _
        | rightEnd => exact Finset.disjoint_empty_left _
        | sym a => dsimp only; split_ifs <;> exact hAB
      | scanLeft =>
        cases sym with
        | leftEnd => exact Finset.disjoint_empty_left _
        | rightEnd => exact Finset.disjoint_empty_left _
        | sym a => dsimp only; split_ifs <;> exact hAB
      | sim off =>
        cases sym with
        | leftEnd => exact Finset.disjoint_empty_left _
        | rightEnd => exact Finset.disjoint_empty_left _
        | sym a =>
          cases off with
          | none => exact hAB
          | some j =>
            dsimp only
            by_cases hj : j.val < (f a).length
            · simp only [hj, ↓reduceDIte]
              have hAM_B : Disjoint (A.filter fun r ↦ pebOff r = some j) B :=
                hAB.mono_left (Finset.filter_subset _ _)
              have hCM_DM := M.pebble_disjoint q (.sym ((f a).get ⟨j.val, hj⟩)) _ B hAM_B
              have hcons := M.pebble_conserved q (.sym ((f a).get ⟨j.val, hj⟩)) _ B hAM_B
              have hAother_DM : Disjoint (A.filter fun r ↦ pebOff r ≠ some j)
                  (M.δ q (.sym ((f a).get ⟨j.val, hj⟩))
                    (A.filter fun r ↦ pebOff r = some j) B).2.2.1 := by
                rw [Finset.disjoint_left]
                intro r hr1 hr2
                have hmem : r ∈ (A.filter fun r ↦ pebOff r = some j) ∪ B := by
                  rw [← hcons]
                  exact Finset.mem_union_right _ hr2
                simp only [Finset.mem_union, Finset.mem_filter] at hr1 hmem
                rcases hmem with ⟨_, hEq⟩ | hB
                · exact hr1.2 hEq
                · exact Finset.disjoint_left.mp hAB hr1.1 hB
              have hdisj := Finset.disjoint_union_left.mpr ⟨hCM_DM, hAother_DM⟩
              cases (M.δ q (.sym ((f a).get ⟨j.val, hj⟩))
                (A.filter fun r ↦ pebOff r = some j) B).2.2.2 <;>
                (dsimp only; try split_ifs) <;> exact hdisj
            · simp only [hj, ↓reduceDIte]; exact hAB
    pebble_conserved := by
      intro s sym A B hAB
      rcases s with ⟨q, pebOff, mode⟩
      cases mode with
      | scanRight =>
        cases sym with
        | leftEnd => exact Finset.empty_union _
        | rightEnd => exact Finset.empty_union _
        | sym a => dsimp only; split_ifs <;> rfl
      | scanLeft =>
        cases sym with
        | leftEnd => exact Finset.empty_union _
        | rightEnd => exact Finset.empty_union _
        | sym a => dsimp only; split_ifs <;> rfl
      | sim off =>
        cases sym with
        | leftEnd => exact Finset.empty_union _
        | rightEnd => exact Finset.empty_union _
        | sym a =>
          cases off with
          | none => rfl
          | some j =>
            dsimp only
            by_cases hj : j.val < (f a).length
            · simp only [hj, ↓reduceDIte]
              have hAM_B : Disjoint (A.filter fun r ↦ pebOff r = some j) B :=
                hAB.mono_left (Finset.filter_subset _ _)
              have hcons := M.pebble_conserved q (.sym ((f a).get ⟨j.val, hj⟩)) _ B hAM_B
              have hEq : ((M.δ q (.sym ((f a).get ⟨j.val, hj⟩))
                    (A.filter fun r ↦ pebOff r = some j) B).2.1 ∪
                    A.filter fun r ↦ pebOff r ≠ some j) ∪
                    (M.δ q (.sym ((f a).get ⟨j.val, hj⟩))
                      (A.filter fun r ↦ pebOff r = some j) B).2.2.1 = A ∪ B := by
                ext r
                have hr := Finset.ext_iff.mp hcons r
                simp only [Finset.mem_union, Finset.mem_filter] at hr ⊢
                tauto
              cases (M.δ q (.sym ((f a).get ⟨j.val, hj⟩))
                (A.filter fun r ↦ pebOff r = some j) B).2.2.2 <;>
                (dsimp only; try split_ifs) <;> exact hEq
            · simp only [hj, ↓reduceDIte]
    no_pebble_leftEnd := by
      intro s A B _
      rcases s with ⟨q, pebOff, mode⟩
      cases mode <;> rfl
    no_pebble_rightEnd := by
      intro s A B _
      rcases s with ⟨q, pebOff, mode⟩
      cases mode <;> rfl }

private def PosRel {α β : Type*} [Fintype α] (f : α → List β) (w : List α)
    (i : Fin (w.length + 2)) (off : Option (Fin (maxImgLen f)))
    (p : Fin ((syntacticMorphism f w).length + 2)) : Prop :=
  (i.val = 0 ∧ off = none ∧ p.val = 0) ∨
  (i.val = w.length + 1 ∧ off = none ∧ p.val = (syntacticMorphism f w).length + 1) ∨
  (∃ (h1 : 0 < i.val) (h2 : i.val ≤ w.length) (j : Fin (maxImgLen f)),
    off = some j ∧ j.val < (f (w.get ⟨i.val - 1, by omega⟩)).length ∧
    p.val = blockStart f w (i.val - 1) + j.val + 1)

private def PebRel {k : ℕ} {α β Q : Type*} [Fintype α] (f : α → List β) (w : List α)
    (c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f)))
    (c : PebbleAutomaton.Cfg k (syntacticMorphism f w).length Q) : Prop :=
  ∀ r : Fin k,
    ((c.pebbles r).val = 0 ∧ (c'.pebbles r).val = 0 ∧ c'.state.2.1 r = none) ∨
    (∃ (i : Fin (w.length + 2)) (j : Fin (maxImgLen f))
      (_ : 0 < i.val) (h2 : i.val ≤ w.length),
      j.val < (f (w.get ⟨i.val - 1, by omega⟩)).length ∧
      (c'.pebbles r).val = i.val ∧ c'.state.2.1 r = some j ∧
      (c.pebbles r).val = blockStart f w (i.val - 1) + j.val + 1)

private def SimRel {k : ℕ} {α β Q : Type*} [Fintype α] (f : α → List β) (w : List α)
    (c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f)))
    (c : PebbleAutomaton.Cfg k (syntacticMorphism f w).length Q) : Prop :=
  c'.state.1 = c.state ∧
  ∃ off : Option (Fin (maxImgLen f)),
    c'.state.2.2 = .sim off ∧ PosRel f w c'.head off c.head ∧ PebRel f w c' c

private theorem pebRel_avail_eq {k : ℕ} {α β Q : Type*} [Fintype α] (f : α → List β) (w : List α)
    {c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f))}
    {c : PebbleAutomaton.Cfg k (syntacticMorphism f w).length Q}
    (hpeb : PebRel f w c' c) :
    PebbleAutomaton.pebblesAvail c = PebbleAutomaton.pebblesAvail c' := by
  ext r
  simp only [PebbleAutomaton.mem_pebblesAvail_iff]
  rcases hpeb r with ⟨h1, h2, _⟩ | ⟨_, _, _, _, _, h1, _, h2⟩
  · exact ⟨fun _ ↦ h2, fun _ ↦ h1⟩
  · constructor <;> intro h <;> omega

private theorem pebRel_atHead_endmarker {k : ℕ} {α β Q : Type*} [Fintype α] (f : α → List β)
    (w : List α) {c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f))}
    {c : PebbleAutomaton.Cfg k (syntacticMorphism f w).length Q}
    (hpeb : PebRel f w c' c)
    (hend : c.head.val = 0 ∨ c.head.val = (syntacticMorphism f w).length + 1) :
    PebbleAutomaton.pebblesAtHead c = ∅ := by
  ext r
  simp only [PebbleAutomaton.mem_pebblesAtHead_iff, Finset.notMem_empty, iff_false, not_and]
  intro hEq hne
  rcases hpeb r with ⟨h0, _, _⟩ | ⟨i, j, hi1, hi2, hj, _, _, hp⟩
  · exact hne (hEq.symm.trans h0)
  · rcases hend with hc0 | hcN
    · omega
    · have hsucc := blockStart_succ f w (show i.val - 1 < w.length by omega)
      have hle : blockStart f w i.val ≤ (syntacticMorphism f w).length := by
        rw [← blockStart_length]
        exact blockStart_mono f w hi2 le_rfl
      have hidx : i.val - 1 + 1 = i.val := by omega
      rw [hidx] at hsucc
      omega

private theorem pebRel_atHead_inner {k : ℕ} {α β Q : Type*} [Fintype α] (f : α → List β)
    (w : List α) {c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f))}
    {c : PebbleAutomaton.Cfg k (syntacticMorphism f w).length Q}
    (hpeb : PebRel f w c' c) {j : Fin (maxImgLen f)}
    (h1 : 0 < c'.head.val) (h2 : c'.head.val ≤ w.length)
    (hj : j.val < (f (w.get ⟨c'.head.val - 1, by omega⟩)).length)
    (hpos : c.head.val = blockStart f w (c'.head.val - 1) + j.val + 1) :
    PebbleAutomaton.pebblesAtHead c =
      (PebbleAutomaton.pebblesAtHead c').filter fun r ↦ c'.state.2.1 r = some j := by
  ext r
  simp only [Finset.mem_filter, PebbleAutomaton.mem_pebblesAtHead_iff]
  rcases hpeb r with ⟨h0, _, hnone⟩ | ⟨i, j', hi1, hi2, hj', hpi, hpo, hpc⟩
  · constructor
    · intro ⟨hEq, _⟩; omega
    · intro ⟨_, hSome⟩; rw [hnone] at hSome; exact absurd hSome (by simp)
  · constructor
    · rintro ⟨hEq, _⟩
      have hblock : i.val = c'.head.val ∧ j'.val = j.val := by
        have hlt_sub : ∀ {a b : ℕ} (hab : a < b) (hb : b < w.length),
            blockStart f w a + (f (w.get ⟨a, lt_trans hab hb⟩)).length ≤ blockStart f w b := by
          intro a b hab hb
          have hs := blockStart_succ f w (lt_trans hab hb)
          rw [← hs]
          exact blockStart_mono f w (Nat.succ_le_of_lt hab) (le_of_lt hb)
        by_cases hlt : i.val < c'.head.val
        · have hb := hlt_sub (show i.val - 1 < c'.head.val - 1 by omega) (by omega)
          omega
        · by_cases hgt : c'.head.val < i.val
          · have hb := hlt_sub (show c'.head.val - 1 < i.val - 1 by omega) (by omega)
            omega
          · have hiEq : i.val = c'.head.val := by omega
            rw [hiEq] at hpc
            exact ⟨hiEq, by omega⟩
      refine ⟨⟨hpi.trans hblock.1, by omega⟩, ?_⟩
      rw [hpo]
      exact congrArg some (Fin.ext hblock.2)
    · rintro ⟨⟨hEq, _⟩, hSome⟩
      rw [hpo] at hSome
      have hjEq := Option.some.inj hSome
      have hiEq : i.val = c'.head.val := hpi.symm.trans hEq
      refine ⟨?_, by omega⟩
      rw [hpc, hpos, hiEq, hjEq]

private theorem scanRight_reaches {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) (w : List α)
    (c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f)))
    (hmode : c'.state.2.2 = .scanRight) (hhead : 1 ≤ c'.head.val)
    (hpeb_no_end : ∀ r, (c'.pebbles r).val ≤ w.length) :
    ∃ (d : ℕ) (off : Option (Fin (maxImgLen f))),
      let c'' := ((simAutomaton f M).step w)^[d] c'
      1 ≤ d ∧ c''.state.1 = c'.state.1 ∧ c''.state.2.1 = c'.state.2.1 ∧
      c''.pebbles = c'.pebbles ∧ c''.state.2.2 = .sim off ∧
      ((∃ (i : Fin (w.length + 2)) (h1 : 0 < i.val) (h2 : i.val ≤ w.length)
          (hj : 0 < (f (w.get ⟨i.val - 1, by omega⟩)).length),
          c''.head = i ∧ off = some ⟨0, lt_trans hj (length_lt_maxImgLen f _)⟩ ∧
          blockStart f w (i.val - 1) = blockStart f w (c'.head.val - 1)) ∨
       (c''.head.val = w.length + 1 ∧ off = none ∧
          blockStart f w w.length = blockStart f w (c'.head.val - 1))) := by
  suffices ∀ (rem : ℕ) (c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f))),
      w.length + 1 - c'.head.val = rem →
      c'.state.2.2 = .scanRight → 1 ≤ c'.head.val →
      (∀ r, (c'.pebbles r).val ≤ w.length) →
      ∃ (d : ℕ) (off : Option (Fin (maxImgLen f))),
        let c'' := ((simAutomaton f M).step w)^[d] c'
        1 ≤ d ∧ c''.state.1 = c'.state.1 ∧ c''.state.2.1 = c'.state.2.1 ∧
        c''.pebbles = c'.pebbles ∧ c''.state.2.2 = .sim off ∧
        ((∃ (i : Fin (w.length + 2)) (h1 : 0 < i.val) (h2 : i.val ≤ w.length)
            (hj : 0 < (f (w.get ⟨i.val - 1, by omega⟩)).length),
            c''.head = i ∧ off = some ⟨0, lt_trans hj (length_lt_maxImgLen f _)⟩ ∧
            blockStart f w (i.val - 1) = blockStart f w (c'.head.val - 1)) ∨
         (c''.head.val = w.length + 1 ∧ off = none ∧
            blockStart f w w.length = blockStart f w (c'.head.val - 1))) by
    exact this _ c' rfl hmode hhead hpeb_no_end
  intro rem
  induction rem with
  | zero =>
    intro c' hrem hmode _ hpeb_no_end
    have hEnd : c'.head.val = w.length + 1 := by omega
    have hNotHalt : c'.state ∉ (simAutomaton f M).halting := by simp [simAutomaton, hmode]
    have hstep : (simAutomaton f M).step w c' =
        ⟨(c'.state.1, c'.state.2.1, .sim none), c'.head, c'.pebbles⟩ := by
      rw [PebbleAutomaton.step_of_not_mem_halting _ _ hNotHalt]
      have htape : tapeAt w c'.head = .rightEnd := by
        have : c'.head = ⟨w.length + 1, by omega⟩ := Fin.ext hEnd
        rw [this, tapeAt_last]
      simp only [simAutomaton, hmode, htape, moveHead_stay]
      ext <;> try rfl
      rename_i r
      dsimp only
      have hnotA : r ∉ PebbleAutomaton.pebblesAtHead c' := by
        simp only [PebbleAutomaton.mem_pebblesAtHead_iff, not_and]
        intro hEq
        have := hpeb_no_end r
        omega
      by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
      · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
        simp [hnotA, hB, h0]
      · simp [hnotA, hB]
    refine ⟨1, none, ?_⟩
    dsimp only
    rw [Function.iterate_one, hstep]
    refine ⟨le_rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hEnd, rfl, ?_⟩⟩
    have : c'.head.val - 1 = w.length := by omega
    rw [this]
  | succ rem ih =>
    intro c' hrem hmode hhead hpeb_no_end
    have hle : c'.head.val ≤ w.length := by omega
    have hNotHalt : c'.state ∉ (simAutomaton f M).halting := by simp [simAutomaton, hmode]
    have htape : tapeAt w c'.head = .sym (w.get ⟨c'.head.val - 1, by omega⟩) :=
      tapeAt_inner w c'.head (by omega) hle
    by_cases hlen : 0 < (f (w.get ⟨c'.head.val - 1, by omega⟩)).length
    · have hstep : (simAutomaton f M).step w c' =
          ⟨(c'.state.1, c'.state.2.1, .sim (some ⟨0, lt_trans hlen (length_lt_maxImgLen f _)⟩)),
            c'.head, c'.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hNotHalt]
        simp only [simAutomaton, hmode, htape, hlen, ↓reduceDIte, moveHead_stay]
        ext <;> try rfl
        rename_i r
        dsimp only
        by_cases hA : r ∈ PebbleAutomaton.pebblesAtHead c'
        · have hEq : (c'.pebbles r).val = c'.head.val :=
            ((PebbleAutomaton.mem_pebblesAtHead_iff _ _).mp hA).1
          simp only [hA, ↓reduceIte, hle, ↓reduceDIte]
          exact hEq.symm
        · by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
          · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
            simp only [hA, ↓reduceIte, hB]
            exact h0.symm
          · simp [hA, hB]
      refine ⟨1, some ⟨0, lt_trans hlen (length_lt_maxImgLen f _)⟩, ?_⟩
      dsimp only
      rw [Function.iterate_one, hstep]
      exact ⟨le_rfl, rfl, rfl, rfl, rfl, Or.inl ⟨c'.head, by omega, hle, hlen, rfl, rfl, rfl⟩⟩
    · have hstep : (simAutomaton f M).step w c' =
          ⟨c'.state, moveHead c'.head .right, c'.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hNotHalt]
        simp only [simAutomaton, hmode, htape, hlen, ↓reduceDIte]
        ext
        · rfl
        · rfl
        · exact hmode.symm
        · rfl
        · rename_i r
          dsimp only
          by_cases hA : r ∈ PebbleAutomaton.pebblesAtHead c'
          · have hEq : (c'.pebbles r).val = c'.head.val :=
              ((PebbleAutomaton.mem_pebblesAtHead_iff _ _).mp hA).1
            simp only [hA, ↓reduceIte, hle, ↓reduceDIte]
            exact hEq.symm
          · by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
            · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
              simp only [hA, ↓reduceIte, hB]
              exact h0.symm
            · simp [hA, hB]
      have hnextHead : (moveHead c'.head .right).val = c'.head.val + 1 :=
        moveHead_right_val c'.head (by omega)
      have hbs : blockStart f w c'.head.val = blockStart f w (c'.head.val - 1) := by
        have hs := blockStart_succ f w (show c'.head.val - 1 < w.length by omega)
        have hidx : c'.head.val - 1 + 1 = c'.head.val := by omega
        rw [hidx] at hs
        omega
      rcases ih ((simAutomaton f M).step w c') (by rw [hstep]; dsimp only; omega)
          (by rw [hstep]; exact hmode) (by rw [hstep]; dsimp only; omega)
          (by rw [hstep]; exact hpeb_no_end) with ⟨d, off, hd_pos, hd1, hd2, hd3, hd4, hd5⟩
      refine ⟨d + 1, off, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      refine ⟨hd1.trans (by rw [hstep]), hd2.trans (by rw [hstep]), hd3.trans (by rw [hstep]),
        hd4, ?_⟩
      have hhd : ((simAutomaton f M).step w c').head.val = c'.head.val + 1 := by
        rw [hstep]; exact hnextHead
      rw [hhd, Nat.add_sub_cancel, hbs] at hd5
      exact hd5

private theorem scanLeft_reaches {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) (w : List α)
    (c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f)))
    (hmode : c'.state.2.2 = .scanLeft) (hhead : c'.head.val ≤ w.length)
    (hpeb_no_end : ∀ r, (c'.pebbles r).val ≤ w.length) :
    ∃ (d : ℕ) (off : Option (Fin (maxImgLen f))),
      let c'' := ((simAutomaton f M).step w)^[d] c'
      1 ≤ d ∧ c''.state.1 = c'.state.1 ∧ c''.state.2.1 = c'.state.2.1 ∧
      c''.pebbles = c'.pebbles ∧ c''.state.2.2 = .sim off ∧
      ((∃ (i : Fin (w.length + 2)) (h1 : 0 < i.val) (h2 : i.val ≤ w.length)
          (_ : 0 < (f (w.get ⟨i.val - 1, by omega⟩)).length),
          c''.head = i ∧
          off = some ⟨(f (w.get ⟨i.val - 1, by omega⟩)).length - 1,
            lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f _)⟩ ∧
          blockStart f w i.val = blockStart f w c'.head.val) ∨
       (c''.head.val = 0 ∧ off = none ∧ blockStart f w c'.head.val = 0)) := by
  suffices ∀ (rem : ℕ) (c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f))),
      c'.head.val = rem →
      c'.state.2.2 = .scanLeft → c'.head.val ≤ w.length →
      (∀ r, (c'.pebbles r).val ≤ w.length) →
      ∃ (d : ℕ) (off : Option (Fin (maxImgLen f))),
        let c'' := ((simAutomaton f M).step w)^[d] c'
        1 ≤ d ∧ c''.state.1 = c'.state.1 ∧ c''.state.2.1 = c'.state.2.1 ∧
        c''.pebbles = c'.pebbles ∧ c''.state.2.2 = .sim off ∧
        ((∃ (i : Fin (w.length + 2)) (h1 : 0 < i.val) (h2 : i.val ≤ w.length)
            (hj : 0 < (f (w.get ⟨i.val - 1, by omega⟩)).length),
            c''.head = i ∧
            off = some ⟨(f (w.get ⟨i.val - 1, by omega⟩)).length - 1,
              lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f _)⟩ ∧
            blockStart f w i.val = blockStart f w c'.head.val) ∨
         (c''.head.val = 0 ∧ off = none ∧ blockStart f w c'.head.val = 0)) by
    exact this _ c' rfl hmode hhead hpeb_no_end
  intro rem
  induction rem with
  | zero =>
    intro c' hrem hmode _ _
    have hNotHalt : c'.state ∉ (simAutomaton f M).halting := by simp [simAutomaton, hmode]
    have hstep : (simAutomaton f M).step w c' =
        ⟨(c'.state.1, c'.state.2.1, .sim none), c'.head, c'.pebbles⟩ := by
      rw [PebbleAutomaton.step_of_not_mem_halting _ _ hNotHalt]
      have htape : tapeAt w c'.head = .leftEnd := by
        have : c'.head = ⟨0, by omega⟩ := Fin.ext hrem
        rw [this, tapeAt_zero]
      simp only [simAutomaton, hmode, htape, moveHead_stay]
      ext <;> try rfl
      rename_i r
      dsimp only
      have hnotA : r ∉ PebbleAutomaton.pebblesAtHead c' := by
        simp [PebbleAutomaton.mem_pebblesAtHead_iff, hrem]
      by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
      · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
        simp [hnotA, hB, h0]
      · simp [hnotA, hB]
    refine ⟨1, none, ?_⟩
    dsimp only
    rw [Function.iterate_one, hstep]
    exact ⟨le_rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hrem, rfl, by rw [hrem, blockStart_zero]⟩⟩
  | succ rem ih =>
    intro c' hrem hmode hle hpeb_no_end
    have hNotHalt : c'.state ∉ (simAutomaton f M).halting := by simp [simAutomaton, hmode]
    have htape : tapeAt w c'.head = .sym (w.get ⟨c'.head.val - 1, by omega⟩) :=
      tapeAt_inner w c'.head (by omega) hle
    by_cases hlen : 0 < (f (w.get ⟨c'.head.val - 1, by omega⟩)).length
    · have hstep : (simAutomaton f M).step w c' =
          ⟨(c'.state.1, c'.state.2.1,
              .sim (some ⟨(f (w.get ⟨c'.head.val - 1, by omega⟩)).length - 1,
                lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f _)⟩)),
            c'.head, c'.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hNotHalt]
        simp only [simAutomaton, hmode, htape, hlen, ↓reduceDIte, moveHead_stay]
        ext <;> try rfl
        rename_i r
        dsimp only
        by_cases hA : r ∈ PebbleAutomaton.pebblesAtHead c'
        · have hEq : (c'.pebbles r).val = c'.head.val :=
            ((PebbleAutomaton.mem_pebblesAtHead_iff _ _).mp hA).1
          simp only [hA, ↓reduceIte, hle, ↓reduceDIte]
          exact hEq.symm
        · by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
          · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
            simp only [hA, ↓reduceIte, hB]
            exact h0.symm
          · simp [hA, hB]
      refine ⟨1, some ⟨(f (w.get ⟨c'.head.val - 1, by omega⟩)).length - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f _)⟩, ?_⟩
      dsimp only
      rw [Function.iterate_one, hstep]
      exact ⟨le_rfl, rfl, rfl, rfl, rfl, Or.inl ⟨c'.head, by omega, hle, hlen, rfl, rfl, rfl⟩⟩
    · have hstep : (simAutomaton f M).step w c' =
          ⟨c'.state, moveHead c'.head .left, c'.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hNotHalt]
        simp only [simAutomaton, hmode, htape, hlen, ↓reduceDIte]
        ext
        · rfl
        · rfl
        · exact hmode.symm
        · rfl
        · rename_i r
          dsimp only
          by_cases hA : r ∈ PebbleAutomaton.pebblesAtHead c'
          · have hEq : (c'.pebbles r).val = c'.head.val :=
              ((PebbleAutomaton.mem_pebblesAtHead_iff _ _).mp hA).1
            simp only [hA, ↓reduceIte, hle, ↓reduceDIte]
            exact hEq.symm
          · by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
            · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
              simp only [hA, ↓reduceIte, hB]
              exact h0.symm
            · simp [hA, hB]
      have hbs : blockStart f w c'.head.val = blockStart f w (c'.head.val - 1) := by
        have hs := blockStart_succ f w (show c'.head.val - 1 < w.length by omega)
        have hidx : c'.head.val - 1 + 1 = c'.head.val := by omega
        rw [hidx] at hs
        omega
      rcases ih ((simAutomaton f M).step w c') (by rw [hstep]; simp [hrem])
          (by rw [hstep]; exact hmode) (by rw [hstep]; simp; omega)
          (by rw [hstep]; exact hpeb_no_end) with ⟨d, off, hd_pos, hd1, hd2, hd3, hd4, hd5⟩
      refine ⟨d + 1, off, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      refine ⟨hd1.trans (by rw [hstep]), hd2.trans (by rw [hstep]), hd3.trans (by rw [hstep]),
        hd4, ?_⟩
      have hhd : ((simAutomaton f M).step w c').head.val = c'.head.val - 1 := by
        rw [hstep]; simp
      rw [hhd, ← hbs] at hd5
      exact hd5

private theorem sim_step {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) (w : List α)
    {c' : PebbleAutomaton.Cfg k w.length (SimState Q k (maxImgLen f))}
    {c : PebbleAutomaton.Cfg k (syntacticMorphism f w).length Q}
    (hrel : SimRel f w c' c) :
    ∃ t : ℕ, 1 ≤ t ∧
      SimRel f w (((simAutomaton f M).step w)^[t] c') (M.step (syntacticMorphism f w) c) := by
  let v := syntacticMorphism f w
  have hvlen : v.length = (syntacticMorphism f w).length := rfl
  rcases hrel with ⟨hstate, off, hmode, hpos, hpeb⟩
  have hpeb_no_end : ∀ r, (c'.pebbles r).val ≤ w.length := by
    intro r
    rcases hpeb r with ⟨_, h0, _⟩ | ⟨i, _, _, hi2, _, hpi, _, _⟩ <;> omega
  by_cases hH : c.state ∈ M.halting
  · have hH' : c'.state ∈ (simAutomaton f M).halting := by
      simp [simAutomaton, hstate, hH, hmode]
    refine ⟨1, le_rfl, ?_⟩
    simp only [Function.iterate_one, PebbleAutomaton.step_of_mem_halting _ _ hH',
      PebbleAutomaton.step_of_mem_halting _ _ hH]
    exact ⟨hstate, off, hmode, hpos, hpeb⟩
  · have hH' : c'.state ∉ (simAutomaton f M).halting := by
      simp [simAutomaton, hstate, hH]
    have havail : PebbleAutomaton.pebblesAvail c = PebbleAutomaton.pebblesAvail c' :=
      pebRel_avail_eq f w hpeb
    rcases hpos with ⟨hi0, hoff, hp0⟩ | ⟨hiN, hoff, hpN⟩ | ⟨hi1, hi2, j, hoff, hj, hp⟩
    · -- Case 1: Left endmarker
      have htape : tapeAt w c'.head = .leftEnd := by
        have : c'.head = ⟨0, by omega⟩ := Fin.ext hi0
        rw [this, tapeAt_zero]
      have htapeV : tapeAt v c.head = .leftEnd := by
        have : c.head = ⟨0, by omega⟩ := Fin.ext hp0
        rw [this, tapeAt_zero]
      have hAtV : PebbleAutomaton.pebblesAtHead c = ∅ :=
        pebRel_atHead_endmarker f w hpeb (Or.inl hp0)
      let res := M.δ c.state .leftEnd ∅ (PebbleAutomaton.pebblesAvail c)
      have hres_C : res.2.1 = ∅ :=
        M.no_pebble_leftEnd c.state ∅ (PebbleAutomaton.pebblesAvail c)
          (Finset.disjoint_empty_left _)
      have hres_D : res.2.2.1 = PebbleAutomaton.pebblesAvail c := by
        have hcons := M.pebble_conserved c.state .leftEnd ∅ (PebbleAutomaton.pebblesAvail c)
          (Finset.disjoint_empty_left _)
        simpa [res, hres_C] using hcons
      have hstepM : M.step v c = ⟨res.1, moveHead c.head res.2.2.2, c.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hH]
        have htapeV' : tapeAt (syntacticMorphism f w) c.head = .leftEnd := htapeV
        simp only [htapeV', hAtV]
        ext
        · rfl
        · rfl
        · rename_i r
          dsimp only
          change (if r ∈ res.2.1 then
              if hpos : c.head.val ≤ (syntacticMorphism f w).length then
                ⟨c.head.val, Nat.lt_succ_of_le hpos⟩
              else ⟨0, Nat.zero_lt_succ _⟩
            else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c.pebbles r).val =
            (c.pebbles r).val
          simp only [hres_C, Finset.notMem_empty, ↓reduceIte, hres_D]
          by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c
          · have h0 : (c.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
            simp [hB, h0]
          · simp [hB]
      have hstep' : (simAutomaton f M).step w c' =
          ⟨(res.1, c'.state.2.1,
              match res.2.2.2 with
              | .left => .sim none
              | .stay => .sim none
              | .right => .scanRight),
            moveHead c'.head res.2.2.2, c'.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hH']
        simp only [simAutomaton, hmode, hoff, htape, hstate, ← havail]
        ext <;> try rfl
        rename_i r
        dsimp only
        have hnotA : r ∉ PebbleAutomaton.pebblesAtHead c' := by
          simp [PebbleAutomaton.mem_pebblesAtHead_iff, hi0]
        by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
        · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
          simp [hnotA, havail, hB, h0]
        · simp [hnotA, havail, hB]
      cases hdir : res.2.2.2 with
      | left =>
        refine ⟨1, le_rfl, ?_⟩
        rw [Function.iterate_one, hstep', hstepM, hdir]
        refine ⟨rfl, none, rfl, Or.inl ⟨by simp [hi0], rfl, by simp [hp0]⟩, ?_⟩
        intro r; exact hpeb r
      | stay =>
        refine ⟨1, le_rfl, ?_⟩
        rw [Function.iterate_one, hstep', hstepM, hdir]
        refine ⟨rfl, none, rfl, Or.inl ⟨by simp [hi0], rfl, by simp [hp0]⟩, ?_⟩
        intro r; exact hpeb r
      | right =>
        have hstep1 := hstep'
        simp only [hdir] at hstep1
        have hhead1 : (moveHead c'.head .right).val = 1 := by
          rw [moveHead_right_val _ (by omega)]; omega
        have hheadV : (moveHead c.head .right).val = 1 := by
          rw [moveHead_right_val _ (by omega)]; omega
        rcases scanRight_reaches f M w ((simAutomaton f M).step w c')
            (by rw [hstep1]) (by rw [hstep1]; dsimp only; omega)
            (by rw [hstep1]; exact hpeb_no_end) with ⟨d, off', hd_pos, hd1, hd2, hd3, hd4, hd5⟩
        refine ⟨d + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply, hstepM, hdir]
        refine ⟨hd1.trans (by rw [hstep1]), off', hd4, ?_, ?_⟩
        · have hhd : ((simAutomaton f M).step w c').head.val = 1 := by
            rw [hstep1]; exact hhead1
          rw [hhd, Nat.sub_self, blockStart_zero] at hd5
          rcases hd5 with ⟨i, hi1', hi2', hj', hci, hoff', hbs⟩ | ⟨hEnd, hoff', hbs⟩
          · refine Or.inr (Or.inr ⟨by rw [hci]; exact hi1', by rw [hci]; exact hi2',
              ⟨0, lt_trans hj' (length_lt_maxImgLen f _)⟩, hoff', ?_, ?_⟩)
            · simp only [hci]; exact hj'
            · rw [hci, hbs, hheadV]; rfl
          · refine Or.inr (Or.inl ⟨hEnd, hoff', ?_⟩)
            rw [blockStart_length] at hbs
            rw [hheadV]
            omega
        · intro r
          have hr := hpeb r
          rw [hd2, hd3, hstep1]
          exact hr
    · -- Case 2: Right endmarker
      have htape : tapeAt w c'.head = .rightEnd := by
        have : c'.head = ⟨w.length + 1, by omega⟩ := Fin.ext hiN
        rw [this, tapeAt_last]
      have htapeV : tapeAt v c.head = .rightEnd := by
        have : c.head = ⟨v.length + 1, by omega⟩ := Fin.ext hpN
        rw [this, tapeAt_last]
      have hAtV : PebbleAutomaton.pebblesAtHead c = ∅ :=
        pebRel_atHead_endmarker f w hpeb (Or.inr hpN)
      let res := M.δ c.state .rightEnd ∅ (PebbleAutomaton.pebblesAvail c)
      have hres_C : res.2.1 = ∅ :=
        M.no_pebble_rightEnd c.state ∅ (PebbleAutomaton.pebblesAvail c)
          (Finset.disjoint_empty_left _)
      have hres_D : res.2.2.1 = PebbleAutomaton.pebblesAvail c := by
        have hcons := M.pebble_conserved c.state .rightEnd ∅ (PebbleAutomaton.pebblesAvail c)
          (Finset.disjoint_empty_left _)
        simpa [res, hres_C] using hcons
      have hstepM : M.step v c = ⟨res.1, moveHead c.head res.2.2.2, c.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hH]
        have htapeV' : tapeAt (syntacticMorphism f w) c.head = .rightEnd := htapeV
        simp only [htapeV', hAtV]
        ext
        · rfl
        · rfl
        · rename_i r
          dsimp only
          change (if r ∈ res.2.1 then
              if hpos : c.head.val ≤ (syntacticMorphism f w).length then
                ⟨c.head.val, Nat.lt_succ_of_le hpos⟩
              else ⟨0, Nat.zero_lt_succ _⟩
            else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c.pebbles r).val =
            (c.pebbles r).val
          simp only [hres_C, Finset.notMem_empty, ↓reduceIte, hres_D]
          by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c
          · have h0 : (c.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
            simp [hB, h0]
          · simp [hB]
      have hstep' : (simAutomaton f M).step w c' =
          ⟨(res.1, c'.state.2.1,
              match res.2.2.2 with
              | .left => .scanLeft
              | .stay => .sim none
              | .right => .sim none),
            moveHead c'.head res.2.2.2, c'.pebbles⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hH']
        simp only [simAutomaton, hmode, hoff, htape, hstate, ← havail]
        ext <;> try rfl
        rename_i r
        dsimp only
        have hnotA : r ∉ PebbleAutomaton.pebblesAtHead c' := by
          simp only [PebbleAutomaton.mem_pebblesAtHead_iff, not_and]
          intro hEq
          have := hpeb_no_end r
          omega
        by_cases hB : r ∈ PebbleAutomaton.pebblesAvail c'
        · have h0 : (c'.pebbles r).val = 0 := (PebbleAutomaton.mem_pebblesAvail_iff _ _).mp hB
          simp [hnotA, havail, hB, h0]
        · simp [hnotA, havail, hB]
      cases hdir : res.2.2.2 with
      | right =>
        refine ⟨1, le_rfl, ?_⟩
        rw [Function.iterate_one, hstep', hstepM, hdir]
        have h1' : (moveHead c'.head .right).val = w.length + 1 := by
          have : c'.head = ⟨w.length + 1, by omega⟩ := Fin.ext hiN
          rw [this, moveHead_right_last]
        have h1V : (moveHead c.head .right).val = v.length + 1 := by
          have : c.head = ⟨v.length + 1, by omega⟩ := Fin.ext hpN
          rw [this, moveHead_right_last]
        refine ⟨rfl, none, rfl, Or.inr (Or.inl ⟨h1', rfl, h1V⟩), ?_⟩
        intro r; exact hpeb r
      | stay =>
        refine ⟨1, le_rfl, ?_⟩
        rw [Function.iterate_one, hstep', hstepM, hdir]
        refine ⟨rfl, none, rfl, Or.inr (Or.inl ⟨by simp [hiN], rfl, by simp [hpN]⟩), ?_⟩
        intro r; exact hpeb r
      | left =>
        have hstep1 := hstep'
        simp only [hdir] at hstep1
        have hhead1 : (moveHead c'.head .left).val = w.length := by simp [hiN]
        have hheadV : (moveHead c.head .left).val = v.length := by simp [hpN, hvlen]
        rcases scanLeft_reaches f M w ((simAutomaton f M).step w c')
            (by rw [hstep1]) (by rw [hstep1]; dsimp only; omega)
            (by rw [hstep1]; exact hpeb_no_end) with ⟨d, off', hd_pos, hd1, hd2, hd3, hd4, hd5⟩
        refine ⟨d + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply, hstepM, hdir]
        refine ⟨hd1.trans (by rw [hstep1]), off', hd4, ?_, ?_⟩
        · have hhd : ((simAutomaton f M).step w c').head.val = w.length := by
            rw [hstep1]; exact hhead1
          rw [hhd, blockStart_length] at hd5
          rcases hd5 with ⟨i, hi1', hi2', hj', hci, hoff', hbs⟩ | ⟨h0, hoff', hbs⟩
          · have hsucc := blockStart_succ f w (show i.val - 1 < w.length by omega)
            have hidx : i.val - 1 + 1 = i.val := by omega
            rw [hidx] at hsucc
            refine Or.inr (Or.inr ⟨by rw [hci]; exact hi1', by rw [hci]; exact hi2',
              ⟨(f (w.get ⟨i.val - 1, by omega⟩)).length - 1,
                lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f _)⟩,
              hoff', ?_, ?_⟩)
            · simp only [hci]; omega
            · rw [hci, hheadV]
              dsimp only
              omega
          · refine Or.inl ⟨h0, hoff', ?_⟩
            rw [hheadV]
            exact hbs
        · intro r
          have hr := hpeb r
          rw [hd2, hd3, hstep1]
          exact hr
    · -- Case 3: Inner cell `(i, j)`
      have htape : tapeAt w c'.head = .sym (w.get ⟨c'.head.val - 1, by omega⟩) :=
        tapeAt_inner w c'.head hi1 hi2
      have hpc_le : c.head.val ≤ v.length := by
        have hs := blockStart_succ f w (show c'.head.val - 1 < w.length by omega)
        have hidx : c'.head.val - 1 + 1 = c'.head.val := by omega
        rw [hidx] at hs
        have hle := blockStart_mono f w hi2 le_rfl
        rw [blockStart_length] at hle
        omega
      have htapeV : tapeAt v c.head =
          .sym ((f (w.get ⟨c'.head.val - 1, by omega⟩)).get ⟨j.val, hj⟩) := by
        rw [tapeAt_inner v c.head (by omega) hpc_le]
        congr 1
        have hget := get_syntacticMorphism_block f w (show c'.head.val - 1 < w.length by omega) hj
        have hsub : c.head.val - 1 = blockStart f w (c'.head.val - 1) + j.val := by omega
        simpa [v, hsub] using hget
      have hAtV : PebbleAutomaton.pebblesAtHead c =
          (PebbleAutomaton.pebblesAtHead c').filter fun r ↦ c'.state.2.1 r = some j :=
        pebRel_atHead_inner f w hpeb hi1 hi2 hj hp
      let AM := (PebbleAutomaton.pebblesAtHead c').filter fun r ↦ c'.state.2.1 r = some j
      let Aother := (PebbleAutomaton.pebblesAtHead c').filter fun r ↦ c'.state.2.1 r ≠ some j
      let res := M.δ c.state (.sym ((f (w.get ⟨c'.head.val - 1, by omega⟩)).get ⟨j.val, hj⟩))
        AM (PebbleAutomaton.pebblesAvail c')
      have hAM_B : Disjoint AM (PebbleAutomaton.pebblesAvail c') :=
        (PebbleAutomaton.disjoint_pebblesAtHead_pebblesAvail c').mono_left
          (Finset.filter_subset _ _)
      have hCM_DM := M.pebble_disjoint c.state
        (.sym ((f (w.get ⟨c'.head.val - 1, by omega⟩)).get ⟨j.val, hj⟩))
        AM (PebbleAutomaton.pebblesAvail c') hAM_B
      have hcons := M.pebble_conserved c.state
        (.sym ((f (w.get ⟨c'.head.val - 1, by omega⟩)).get ⟨j.val, hj⟩))
        AM (PebbleAutomaton.pebblesAvail c') hAM_B
      have hAother_DM : Disjoint Aother res.2.2.1 := by
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        have hmem : r ∈ AM ∪ PebbleAutomaton.pebblesAvail c' := by
          rw [← hcons]; exact Finset.mem_union_right _ hr2
        simp only [AM, Aother, Finset.mem_union, Finset.mem_filter] at hr1 hmem
        rcases hmem with ⟨_, hEq⟩ | hB
        · exact hr1.2 hEq
        · exact Finset.disjoint_left.mp (PebbleAutomaton.disjoint_pebblesAtHead_pebblesAvail c')
            hr1.1 hB
      have hstepM : M.step v c =
          ⟨res.1, moveHead c.head res.2.2.2,
            fun r ↦ if r ∈ res.2.1 then ⟨c.head.val, Nat.lt_succ_of_le hpc_le⟩
              else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c.pebbles r⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hH]
        have htapeV' : tapeAt (syntacticMorphism f w) c.head =
            .sym ((f (w.get ⟨c'.head.val - 1, by omega⟩)).get ⟨j.val, hj⟩) := htapeV
        have hpc_le' : c.head.val ≤ (syntacticMorphism f w).length := hpc_le
        simp only [htapeV', hAtV, havail, hpc_le', ↓reduceDIte]
        rfl
      have hpeb_after : ∀ (mode' : SimMode (maxImgLen f)) (head' : Fin (w.length + 2)),
          PebRel f w
            ⟨(res.1,
                fun r ↦ if r ∈ res.2.1 then some j
                  else if r ∈ res.2.2.1 then none else c'.state.2.1 r,
                mode'),
              head',
              fun r ↦ if r ∈ res.2.1 ∪ Aother then ⟨c'.head.val, Nat.lt_succ_of_le hi2⟩
                else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c'.pebbles r⟩
            (M.step v c) := by
        intro mode' head' r
        rw [hstepM]
        dsimp only
        by_cases hC : r ∈ res.2.1
        · right
          refine ⟨c'.head, j, hi1, hi2, hj, ?_, ?_, ?_⟩
          · simp [hC]
          · simp [hC]
          · simp [hC, hp]
        · by_cases hD : r ∈ res.2.2.1
          · left
            have hnotO : r ∉ Aother := Finset.disjoint_right.mp hAother_DM hD
            simp [hC, hD, hnotO]
          · have hnotAM : r ∉ AM := by
              intro hm
              have : r ∈ res.2.1 ∪ res.2.2.1 := by rw [hcons]; exact Finset.mem_union_left _ hm
              simp [hC, hD] at this
            have hnotB : r ∉ PebbleAutomaton.pebblesAvail c' := by
              intro hm
              have : r ∈ res.2.1 ∪ res.2.2.1 := by rw [hcons]; exact Finset.mem_union_right _ hm
              simp [hC, hD] at this
            by_cases hO : r ∈ Aother
            · have hA : r ∈ PebbleAutomaton.pebblesAtHead c' := (Finset.mem_filter.mp hO).1
              have hEq : (c'.pebbles r).val = c'.head.val :=
                ((PebbleAutomaton.mem_pebblesAtHead_iff _ _).mp hA).1
              rcases hpeb r with ⟨_, h0', _⟩ | ⟨i', j', hi1', hi2', hj', hpi', hpo', hpc'⟩
              · omega
              · right
                refine ⟨i', j', hi1', hi2', hj', ?_, ?_, ?_⟩
                · simp only [hC, hO, Finset.mem_union, or_true, ↓reduceIte]
                  exact hEq.symm.trans hpi'
                · simp [hC, hD, hpo']
                · simp [hC, hD, hpc']
            · simp only [hC, hD, hO, Finset.mem_union, or_self, ↓reduceIte]
              exact hpeb r
      have hpeb_no_end_after : ∀ r,
          ((if r ∈ res.2.1 ∪ Aother then
              (⟨c'.head.val, Nat.lt_succ_of_le hi2⟩ : Fin (w.length + 1))
            else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c'.pebbles r).val ≤
              w.length) := by
        intro r
        split_ifs
        · exact hi2
        · omega
        · exact hpeb_no_end r
      have hstep'_base : (simAutomaton f M).step w c' =
          let pebOff' : Fin k → Option (Fin (maxImgLen f)) := fun r ↦
            if r ∈ res.2.1 then some j else if r ∈ res.2.2.1 then none else c'.state.2.1 r
          let peb' : Fin k → Fin (w.length + 1) := fun r ↦
            if r ∈ res.2.1 ∪ Aother then ⟨c'.head.val, Nat.lt_succ_of_le hi2⟩
            else if r ∈ res.2.2.1 then ⟨0, Nat.zero_lt_succ _⟩ else c'.pebbles r
          match res.2.2.2 with
          | .stay => ⟨(res.1, pebOff', .sim (some j)), c'.head, peb'⟩
          | .right =>
            if hj' : j.val + 1 < (f (w.get ⟨c'.head.val - 1, by omega⟩)).length then
              ⟨(res.1, pebOff', .sim (some ⟨j.val + 1,
                  lt_trans hj' (length_lt_maxImgLen f _)⟩)),
                c'.head, peb'⟩
            else
              ⟨(res.1, pebOff', .scanRight), moveHead c'.head .right, peb'⟩
          | .left =>
            if hj' : 0 < j.val then
              ⟨(res.1, pebOff', .sim (some ⟨j.val - 1,
                  lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩)),
                c'.head, peb'⟩
            else
              ⟨(res.1, pebOff', .scanLeft), moveHead c'.head .left, peb'⟩ := by
        rw [PebbleAutomaton.step_of_not_mem_halting _ _ hH']
        simp only [simAutomaton, hmode, hoff, htape, hstate, hj, ↓reduceDIte, hi2]
        cases res.2.2.2 with
        | stay =>
          dsimp only [AM, Aother, res]
          simp only [moveHead_stay, Finset.mem_union]
        | right =>
          dsimp only [AM, Aother, res]
          by_cases hj' : j.val + 1 < (f (w.get ⟨c'.head.val - 1, by omega⟩)).length
          · simp only [hj', ↓reduceDIte, moveHead_stay, Finset.mem_union]
          · simp only [hj', ↓reduceDIte, Finset.mem_union]
        | left =>
          dsimp only [AM, Aother, res]
          by_cases hj' : 0 < j.val
          · simp only [hj', ↓reduceDIte, moveHead_stay, Finset.mem_union]
          · simp only [hj', ↓reduceDIte, Finset.mem_union]
      cases hdir : res.2.2.2 with
      | stay =>
        refine ⟨1, le_rfl, ?_⟩
        simp only [Function.iterate_one, hstep'_base, hdir]
        refine ⟨by rw [hstepM], some j, rfl, Or.inr (Or.inr ⟨hi1, hi2, j, rfl, hj, ?_⟩),
          hpeb_after _ _⟩
        rw [hstepM, hdir]
        simpa using hp
      | right =>
        by_cases hj' : j.val + 1 < (f (w.get ⟨c'.head.val - 1, by omega⟩)).length
        · refine ⟨1, le_rfl, ?_⟩
          simp only [Function.iterate_one, hstep'_base, hdir, hj', ↓reduceDIte]
          refine ⟨by rw [hstepM], some ⟨j.val + 1, lt_trans hj' (length_lt_maxImgLen f _)⟩, rfl,
            Or.inr (Or.inr ⟨hi1, hi2, _, rfl, hj', ?_⟩), hpeb_after _ _⟩
          rw [hstepM, hdir]
          dsimp only
          rw [moveHead_right_val _ (by omega)]
          omega
        · have hstep1 := hstep'_base
          simp only [hdir, hj', ↓reduceDIte] at hstep1
          have hhead1 : (moveHead c'.head .right).val = c'.head.val + 1 :=
            moveHead_right_val _ (by omega)
          have hheadV : (moveHead c.head .right).val = blockStart f w c'.head.val + 1 := by
            have hs := blockStart_succ f w (show c'.head.val - 1 < w.length by omega)
            have hidx : c'.head.val - 1 + 1 = c'.head.val := by omega
            rw [hidx] at hs
            rw [moveHead_right_val _ (by omega)]
            omega
          rcases scanRight_reaches f M w ((simAutomaton f M).step w c')
              (by rw [hstep1]) (by rw [hstep1]; dsimp only; omega)
              (by rw [hstep1]; exact hpeb_no_end_after) with
            ⟨d, off', hd_pos, hd1, hd2, hd3, hd4, hd5⟩
          refine ⟨d + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply]
          refine ⟨hd1.trans (by rw [hstep1, hstepM]), off', hd4, ?_, ?_⟩
          · have hhd : ((simAutomaton f M).step w c').head.val = c'.head.val + 1 := by
              rw [hstep1]; exact hhead1
            rw [hhd, Nat.add_sub_cancel] at hd5
            rw [hstepM, hdir]
            dsimp only
            rcases hd5 with ⟨i, hi1', hi2', hji', hci, hoff', hbs⟩ | ⟨hEnd, hoff', hbs⟩
            · refine Or.inr (Or.inr ⟨by rw [hci]; exact hi1', by rw [hci]; exact hi2',
                ⟨0, lt_trans hji' (length_lt_maxImgLen f _)⟩, hoff',
                by simp only [hci]; exact hji', ?_⟩)
              rw [hci, hbs, hheadV]
              rfl
            · refine Or.inr (Or.inl ⟨hEnd, hoff', ?_⟩)
              rw [blockStart_length] at hbs
              rw [hheadV]
              omega
          · have hpeb1 := hpeb_after .scanRight (moveHead c'.head .right)
            intro r
            have hr := hpeb1 r
            rw [hd2, hd3, hstep1]
            exact hr
      | left =>
        by_cases hj' : 0 < j.val
        · refine ⟨1, le_rfl, ?_⟩
          simp only [Function.iterate_one, hstep'_base, hdir, hj', ↓reduceDIte]
          refine ⟨by rw [hstepM], some ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩, rfl,
            Or.inr (Or.inr ⟨hi1, hi2, _, rfl, by dsimp only; omega, ?_⟩), hpeb_after _ _⟩
          rw [hstepM, hdir]
          simp only [moveHead_left_val]
          omega
        · have hstep1 := hstep'_base
          simp only [hdir, hj', ↓reduceDIte] at hstep1
          have hhead1 : (moveHead c'.head .left).val = c'.head.val - 1 := by simp
          have hheadV : (moveHead c.head .left).val = blockStart f w (c'.head.val - 1) := by
            simp only [moveHead_left_val]
            omega
          rcases scanLeft_reaches f M w ((simAutomaton f M).step w c')
              (by rw [hstep1]) (by rw [hstep1]; dsimp only; omega)
              (by rw [hstep1]; exact hpeb_no_end_after) with
            ⟨d, off', hd_pos, hd1, hd2, hd3, hd4, hd5⟩
          refine ⟨d + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply]
          refine ⟨hd1.trans (by rw [hstep1, hstepM]), off', hd4, ?_, ?_⟩
          · have hhd : ((simAutomaton f M).step w c').head.val = c'.head.val - 1 := by
              rw [hstep1]; exact hhead1
            rw [hhd] at hd5
            rw [hstepM, hdir]
            dsimp only
            rcases hd5 with ⟨i, hi1', hi2', hji', hci, hoff', hbs⟩ | ⟨h0, hoff', hbs⟩
            · have hs := blockStart_succ f w (show i.val - 1 < w.length by omega)
              have hidx : i.val - 1 + 1 = i.val := by omega
              rw [hidx] at hs
              refine Or.inr (Or.inr ⟨by rw [hci]; exact hi1', by rw [hci]; exact hi2',
                ⟨(f (w.get ⟨i.val - 1, by omega⟩)).length - 1,
                  lt_of_le_of_lt (Nat.sub_le _ _) (length_lt_maxImgLen f _)⟩,
                hoff', by simp only [hci]; omega, ?_⟩)
              rw [hci, hheadV]
              dsimp only
              omega
            · refine Or.inl ⟨h0, hoff', ?_⟩
              rw [hheadV]
              exact hbs
          · have hpeb1 := hpeb_after .scanLeft (moveHead c'.head .left)
            intro r
            have hr := hpeb1 r
            rw [hd2, hd3, hstep1]
            exact hr

private theorem sim_run {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) (w : List α) (s : ℕ) :
    ∃ t : ℕ, SimRel f w ((simAutomaton f M).run w t) (M.run (syntacticMorphism f w) s) := by
  induction s with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [PebbleAutomaton.run_zero]
    refine ⟨by simp [simAutomaton], none, by simp [simAutomaton],
      Or.inl ⟨by simp, rfl, by simp⟩,
      fun r ↦ Or.inl ⟨by simp, by simp, by simp [simAutomaton]⟩⟩
  | succ s ih =>
    rcases ih with ⟨t, hrel⟩
    rcases sim_step f M w hrel with ⟨d, _, hrel'⟩
    refine ⟨d + t, ?_⟩
    rw [PebbleAutomaton.run_succ, PebbleAutomaton.run_add]
    exact hrel'

private theorem mem_simHalting_iff {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) (s : SimState Q k (maxImgLen f)) :
    s ∈ (simAutomaton f M).halting ↔
      s.1 ∈ M.halting ∧ match s.2.2 with | .sim _ => True | _ => False := Iff.rfl

private theorem mem_simAccepting_iff {k : ℕ} {α β Q : Type*} [Fintype α]
    (f : α → List β) (M : PebbleAutomaton k β Q) (s : SimState Q k (maxImgLen f)) :
    s ∈ (simAutomaton f M).accepting ↔
      s.1 ∈ M.accepting ∧ match s.2.2 with | .sim _ => True | _ => False := Iff.rfl

/-- Every level `REG k` of the pebble hierarchy is closed under inverse syntactic morphisms. -/
theorem mem_REG_of_syntacticReducible {k : ℕ} {α β : Type u} [Fintype α] [Fintype β]
    {L₁ : Set (List α)} {L₂ : Set (List β)}
    (hred : SyntacticReducible L₁ L₂) (hL₂ : L₂ ∈ REG k) : L₁ ∈ REG k := by
  rcases hred with ⟨f, rfl⟩
  rcases hL₂ with ⟨Q, _, M, hHalt, hEq⟩
  refine ⟨SimState Q k (maxImgLen f), inferInstance, simAutomaton f M, ?_, ?_⟩
  · intro w
    rcases hHalt (syntacticMorphism f w) with ⟨s, hs⟩
    rcases sim_run f M w s with ⟨t, hstate, off, hmode, _, _⟩
    exact ⟨t, (mem_simHalting_iff f M _).mpr ⟨hstate ▸ hs, by rw [hmode]; trivial⟩⟩
  · ext w
    simp only [Set.mem_preimage]
    rw [PebbleAutomaton.mem_acceptedLanguage_iff, ← hEq, PebbleAutomaton.mem_acceptedLanguage_iff]
    rcases hHalt (syntacticMorphism f w) with ⟨sH, hsH⟩
    rcases sim_run f M w sH with ⟨tH, hstateH, offH, hmodeH, _, _⟩
    have htH_halt : ((simAutomaton f M).run w tH).state ∈ (simAutomaton f M).halting :=
      (mem_simHalting_iff f M _).mpr ⟨hstateH ▸ hsH, by rw [hmodeH]; trivial⟩
    constructor
    · rintro ⟨t, ht⟩
      have hEqRun := (simAutomaton f M).run_eq_of_mem_halting w htH_halt (max t tH)
        (le_max_right _ _)
      have hEqRun2 := (simAutomaton f M).run_eq_of_mem_halting w
        ((simAutomaton f M).accepting_subset_halting ht) (max t tH) (le_max_left _ _)
      have hEqCfg : (simAutomaton f M).run w tH = (simAutomaton f M).run w t :=
        hEqRun.symm.trans hEqRun2
      have hacc : ((simAutomaton f M).run w tH).state ∈ (simAutomaton f M).accepting :=
        hEqCfg.symm ▸ ht
      exact ⟨sH, hstateH ▸ ((mem_simAccepting_iff f M _).mp hacc).1⟩
    · rintro ⟨s, hs⟩
      have hEqRun := M.run_eq_of_mem_halting (syntacticMorphism f w) hsH (max s sH)
        (le_max_right _ _)
      have hEqRun2 := M.run_eq_of_mem_halting (syntacticMorphism f w)
        (M.accepting_subset_halting hs) (max s sH) (le_max_left _ _)
      have hacc : (M.run (syntacticMorphism f w) sH).state ∈ M.accepting :=
        (hEqRun.symm.trans hEqRun2).symm ▸ hs
      exact ⟨tH, (mem_simAccepting_iff f M _).mpr ⟨hstateH ▸ hacc, by rw [hmodeH]; trivial⟩⟩

/-- The pebble hierarchy `REG` is an invariant hierarchy under syntactic morphisms. -/
theorem isInvariantHierarchy_REG : IsInvariantHierarchy (REG : ℕ → LanguageClass) := by
  intro k _ α β _ _ L₁ L₂ hL₂ hred
  exact mem_REG_of_syntacticReducible hred hL₂

end SyntacticInvariance


end CslibFrontier.Computability.Automata
