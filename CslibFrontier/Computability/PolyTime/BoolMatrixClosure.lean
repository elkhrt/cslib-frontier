/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.GetD

/-!
# Polynomial-time equivalence closure on Boolean adjacency matrices

Computing the reflexive-symmetric-transitive closure (`Relation.EqvGen`) of an `R × R` Boolean
adjacency matrix via `R` Boolean matrix-squaring iterations runs in deterministic polynomial time
(`Turing.MultiTapeTM.ComputableInPolyTime`) on multi-tape Turing machines.

## Main definitions

* `Cslib.PolyTime.boolMatStep`: single Boolean matrix-squaring step on `R × R` matrices.
* `Cslib.PolyTime.boolMatClosure`: `R`-step reflexive-symmetric-transitive closure of an `R × R`
  Boolean matrix.
* `Cslib.PolyTime.encBoolMatrix`: framed-list encoding `encList (encList encBool)` of Boolean
  matrices.

## Main results

* `Cslib.PolyTime.getD_boolMatClosure_iff_eqvGen`: `boolMatClosure R adj` computes exact
  `Relation.EqvGen` on `Fin R`.
* `Cslib.PolyTime.boolMatClosure_computableInPolyTime`: `boolMatClosure` is computable in
  polynomial time whenever `R` is unary-computable and `adj` is polynomial-time computable.
-/

public section

namespace Cslib.PolyTime

open Turing Turing.MultiTapeTM

/-- Framed list-of-rows encoding of Boolean matrices `List (List Bool)`. -/
abbrev encBoolMatrix : List (List Bool) ↪ List Bool :=
  encList (encList encBool)

/-- One Boolean matrix-squaring step on `R × R` matrices. -/
def boolMatStep (R : ℕ) (M : List (List Bool)) : List (List Bool) :=
  (List.range R).map fun i ↦
    let row_i := M.getD i []
    (List.range R).map fun j ↦
      row_i.getD j false ||
        (List.range R).any fun mid ↦ row_i.getD mid false && (M.getD mid []).getD j false

/-- Reflexive-symmetric-transitive closure (`Relation.EqvGen`) of an `R × R` Boolean adjacency
matrix computed by `R` squaring steps. -/
def boolMatClosure (R : ℕ) (adj : List (List Bool)) : List (List Bool) :=
  let init := (List.range R).map fun i ↦
    (List.range R).map fun j ↦
      decide (i = j) || (adj.getD i []).getD j false || (adj.getD j []).getD i false
  (boolMatStep R)^[R] init

private theorem shape_boolMatStep (R : ℕ) (M : List (List Bool)) :
    (boolMatStep R M).length = R ∧ ∀ row ∈ boolMatStep R M, row.length = R := by
  refine ⟨by simp only [boolMatStep, List.length_map, List.length_range], ?_⟩
  intro row hrow
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
  simp only [List.length_map, List.length_range]

private theorem shape_iterate_boolMatStep (R : ℕ) (init : List (List Bool))
    (hinit : init.length = R ∧ ∀ row ∈ init, row.length = R) (s : ℕ) :
    ((boolMatStep R)^[s] init).length = R ∧
      ∀ row ∈ (boolMatStep R)^[s] init, row.length = R := by
  induction s with
  | zero => exact hinit
  | succ _ _ =>
    rw [Function.iterate_succ_apply']
    exact shape_boolMatStep R _

private def walkLe {R : ℕ} (symRel : Fin R → Fin R → Prop) : ℕ → Fin R → Fin R → Prop
  | 0, u, v => symRel u v
  | s + 1, u, v => walkLe symRel s u v ∨ ∃ mid : Fin R, walkLe symRel s u mid ∧
    walkLe symRel s mid v

/-- `boolMatClosure R adj` computes exact `Relation.EqvGen` on `Fin R`. -/
theorem getD_boolMatClosure_iff_eqvGen {R : ℕ} {adj : List (List Bool)}
    (rel : Fin R → Fin R → Prop)
    (hadj : ∀ x y : Fin R, (adj.getD x.val []).getD y.val false = true ↔ rel x y)
    (x y : Fin R) :
    ((boolMatClosure R adj).getD x.val []).getD y.val false = true ↔
      Relation.EqvGen rel x y := by
  let symRel (u v : Fin R) : Prop := u = v ∨ rel u v ∨ rel v u
  let init := (List.range R).map fun i ↦
    (List.range R).map fun j ↦
      decide (i = j) || (adj.getD i []).getD j false || (adj.getD j []).getD i false
  have hinit_iff (u v : Fin R) :
      (init.getD u.val []).getD v.val false = true ↔ symRel u v := by
    dsimp only [init, symRel]
    have hu_len : u.val < ((List.range R).map fun i ↦
        (List.range R).map fun j ↦
          decide (i = j) || (adj.getD i []).getD j false || (adj.getD j []).getD i false).length :=
      by rw [List.length_map, List.length_range]; exact u.isLt
    rw [List.getD_eq_getElem _ _ hu_len]
    simp only [List.getElem_map, List.getElem_range]
    have hv_len : v.val < ((List.range R).map fun j ↦
        decide (u.val = j) || (adj.getD u.val []).getD j false ||
          (adj.getD j []).getD u.val false).length :=
      by rw [List.length_map, List.length_range]; exact v.isLt
    rw [List.getD_eq_getElem _ _ hv_len]
    simp only [List.getElem_map, List.getElem_range, Bool.or_eq_true, decide_eq_true_eq,
      hadj u v, hadj v u, Fin.ext_iff, or_assoc]
  have hiter_iff (s : ℕ) (u v : Fin R) :
      (((boolMatStep R)^[s] init).getD u.val []).getD v.val false = true ↔
        walkLe symRel s u v := by
    induction s generalizing u v with
    | zero =>
      dsimp only [Function.iterate_zero_apply, walkLe]
      exact hinit_iff u v
    | succ s ih =>
      rw [Function.iterate_succ_apply']
      dsimp only [boolMatStep, walkLe]
      set M := (boolMatStep R)^[s] init
      have hu_len : u.val < ((List.range R).map fun i ↦
          (List.range R).map fun j ↦
            (M.getD i []).getD j false ||
              (List.range R).any fun mid ↦
                (M.getD i []).getD mid false && (M.getD mid []).getD j false).length :=
        by rw [List.length_map, List.length_range]; exact u.isLt
      rw [List.getD_eq_getElem _ _ hu_len]
      simp only [List.getElem_map, List.getElem_range]
      have hv_len : v.val < ((List.range R).map fun j ↦
          (M.getD u.val []).getD j false ||
            (List.range R).any fun mid ↦
              (M.getD u.val []).getD mid false && (M.getD mid []).getD j false).length :=
        by rw [List.length_map, List.length_range]; exact v.isLt
      rw [List.getD_eq_getElem _ _ hv_len]
      simp only [List.getElem_map, List.getElem_range, Bool.or_eq_true, List.any_eq_true,
        List.mem_range, Bool.and_eq_true]
      rw [ih u v]
      refine or_congr_right ⟨?_, ?_⟩
      · rintro ⟨m, hm, h1, h2⟩
        exact ⟨⟨m, hm⟩, (ih u ⟨m, hm⟩).mp h1, (ih ⟨m, hm⟩ v).mp h2⟩
      · rintro ⟨mid, h1, h2⟩
        exact ⟨mid.val, mid.isLt, (ih u mid).mpr h1, (ih mid v).mpr h2⟩
  change (((boolMatStep R)^[R] init).getD x.val []).getD y.val false = true ↔ _
  rw [hiter_iff R x y]
  have hsound (s : ℕ) {u v : Fin R} (hw : walkLe symRel s u v) : Relation.EqvGen rel u v := by
    induction s generalizing u v with
    | zero =>
      rcases hw with rfl | h1 | h2
      · exact Relation.EqvGen.refl u
      · exact Relation.EqvGen.rel u v h1
      · exact Relation.EqvGen.symm v u (Relation.EqvGen.rel v u h2)
    | succ _ ih =>
      rcases hw with hw1 | ⟨mid, hw1, hw2⟩
      · exact ih hw1
      · exact Relation.EqvGen.trans u mid v (ih hw1) (ih hw2)
  refine ⟨hsound R, fun heqv ↦ ?_⟩
  classical
  let G : SimpleGraph (Fin R) :=
    { Adj := fun u v ↦ u ≠ v ∧ (rel u v ∨ rel v u)
      symm := ⟨fun _ _ ⟨hne, h⟩ ↦ ⟨hne.symm, h.symm⟩⟩
      loopless := ⟨fun _ ⟨hne, _⟩ ↦ hne rfl⟩ }
  have hreach : G.Reachable x y := by
    induction heqv with
    | rel u v h =>
      by_cases huv : u = v
      · subst huv; exact SimpleGraph.Reachable.refl u
      · exact SimpleGraph.Adj.reachable ⟨huv, Or.inl h⟩
    | refl u => exact SimpleGraph.Reachable.refl u
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨p, hp_path⟩ := hreach.exists_isPath
  have hp_len : p.length < R := by
    have hnodup := hp_path.support_nodup
    have hsup_len : p.support.length = p.length + 1 := SimpleGraph.Walk.length_support p
    have hle_card := List.Nodup.length_le_card hnodup
    rw [Fintype.card_fin, hsup_len] at hle_card
    omega
  have hwalk_mono {s₁ s₂ : ℕ} (hs : s₁ ≤ s₂) {u v : Fin R} (hw : walkLe symRel s₁ u v) :
      walkLe symRel s₂ u v := by
    induction hs with
    | refl => exact hw
    | step _ ih => exact Or.inl ih
  have hwalk_of_len : ∀ {u v : Fin R} (q : G.Walk u v), walkLe symRel q.length u v := by
    intro u v q
    induction q with
    | nil => exact Or.inl rfl
    | @cons a b _ hadj q' ih =>
      exact Or.inr ⟨b, hwalk_mono (Nat.zero_le q'.length) (Or.inr hadj.2), ih⟩
  exact hwalk_mono hp_len.le (hwalk_of_len p)

/-- **`boolMatClosure` is computable in deterministic polynomial time.** -/
theorem boolMatClosure_computableInPolyTime {γ : Type} {encIn : γ ↪ List Bool}
    {Rfn : γ → ℕ} {adjFn : γ → List (List Bool)}
    (hR : ComputableInPolyTime Rfn encIn encUnary)
    (hadj : ComputableInPolyTime adjFn encIn encBoolMatrix) :
    ComputableInPolyTime (fun x ↦ boolMatClosure (Rfn x) (adjFn x))
      encIn encBoolMatrix := by
  have hinit : ComputableInPolyTime
      (fun x ↦ (List.range (Rfn x)).map fun i ↦
        (List.range (Rfn x)).map fun j ↦
          decide (i = j) || ((adjFn x).getD i []).getD j false ||
            ((adjFn x).getD j []).getD i false)
      encIn encBoolMatrix := by
    refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.unary_range' hR) ?_
    refine ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.unary_range' (hR.comp (.fst _ _))) ?_
    let encQ := encPair (encPair encIn encUnary) encUnary
    have hx : ComputableInPolyTime (fun q : (γ × ℕ) × ℕ ↦ q.1.1) encQ encIn :=
      (ComputableInPolyTime.fst _ _).comp (.fst _ _)
    have hi : ComputableInPolyTime (fun q : (γ × ℕ) × ℕ ↦ q.1.2) encQ encUnary :=
      (ComputableInPolyTime.snd _ _).comp (.fst _ _)
    have hj : ComputableInPolyTime (fun q : (γ × ℕ) × ℕ ↦ q.2) encQ encUnary := .snd _ _
    have heq_ij : ComputableInPolyTime (fun q : (γ × ℕ) × ℕ ↦ decide (q.1.2 = q.2))
        encQ encBool :=
      (ComputableInPolyTime.unary_beq' hi hj).of_enc_eq fun q ↦
        congrArg encBool (Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, beq_iff_eq]))
    have hrow_i := ComputableInPolyTime.listGetDWithInput (hadj.comp hx) hi []
    have hrow_j := ComputableInPolyTime.listGetDWithInput (hadj.comp hx) hj []
    have hij_bit := ComputableInPolyTime.listGetDWithInput hrow_i hj false
    have hji_bit := ComputableInPolyTime.listGetDWithInput hrow_j hi false
    exact ComputableInPolyTime.bool_or' (ComputableInPolyTime.bool_or' heq_ij hij_bit) hji_bit
  have hstep : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) ↦ boolMatStep p.1 p.2)
      (encPair encUnary encBoolMatrix) encBoolMatrix := by
    unfold boolMatStep
    dsimp only
    refine ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.unary_range' (.fst _ _)) ?_
    refine ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.unary_range' ((ComputableInPolyTime.fst _ _).comp (.fst _ _))) ?_
    let encQ2 := encPair (encPair (encPair encUnary encBoolMatrix) encUnary) encUnary
    have hM : ComputableInPolyTime
        (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ ↦ q.1.1.2) encQ2 encBoolMatrix :=
      ((ComputableInPolyTime.snd _ _).comp (.fst _ _)).comp (.fst _ _)
    have hR_q : ComputableInPolyTime
        (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ ↦ q.1.1.1) encQ2 encUnary :=
      ((ComputableInPolyTime.fst _ _).comp (.fst _ _)).comp (.fst _ _)
    have hi_q : ComputableInPolyTime
        (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ ↦ q.1.2) encQ2 encUnary :=
      (ComputableInPolyTime.snd _ _).comp (.fst _ _)
    have hj_q : ComputableInPolyTime
        (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ ↦ q.2) encQ2 encUnary := .snd _ _
    have hrow_i := ComputableInPolyTime.listGetDWithInput hM hi_q []
    have hij_bit := ComputableInPolyTime.listGetDWithInput hrow_i hj_q false
    have hany : ComputableInPolyTime
        (fun q : ((ℕ × List (List Bool)) × ℕ) × ℕ ↦
          (List.range q.1.1.1).any fun mid ↦
            (q.1.1.2.getD q.1.2 []).getD mid false && (q.1.1.2.getD mid []).getD q.2 false)
        encQ2 encBool := by
      refine ComputableInPolyTime.anyWithInput (ComputableInPolyTime.unary_range' hR_q) ?_
      let encZ := encPair encQ2 encUnary
      have hM' : ComputableInPolyTime
          (fun z : (((ℕ × List (List Bool)) × ℕ) × ℕ) × ℕ ↦ z.1.1.1.2) encZ encBoolMatrix :=
        hM.comp (.fst _ _)
      have hi' : ComputableInPolyTime
          (fun z : (((ℕ × List (List Bool)) × ℕ) × ℕ) × ℕ ↦ z.1.1.2) encZ encUnary :=
        hi_q.comp (.fst _ _)
      have hj' : ComputableInPolyTime
          (fun z : (((ℕ × List (List Bool)) × ℕ) × ℕ) × ℕ ↦ z.1.2) encZ encUnary :=
        hj_q.comp (.fst _ _)
      have hmid : ComputableInPolyTime
          (fun z : (((ℕ × List (List Bool)) × ℕ) × ℕ) × ℕ ↦ z.2) encZ encUnary := .snd _ _
      have hri := ComputableInPolyTime.listGetDWithInput hM' hi' []
      have hrm := ComputableInPolyTime.listGetDWithInput hM' hmid []
      exact ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.listGetDWithInput hri hmid false)
        (ComputableInPolyTime.listGetDWithInput hrm hj' false)
    exact ComputableInPolyTime.bool_or' hij_bit hany
  have hR_poly : PolyBounded (fun x ↦ (encIn x).length) Rfn := hR.polyBounded
  have hbound : PolyBounded (fun x ↦ (encIn x).length)
      (fun x ↦ Rfn x * (2 * (Rfn x * 3) + 1)) := by
    have h1 := hR_poly.mul (.const 3)
    have h2 := (PolyBounded.const 2).mul h1 |>.add (.const 1)
    exact hR_poly.mul h2
  refine ComputableInPolyTime.iterateWith hR hR hinit hstep hbound fun x s _ ↦ ?_
  have hshape := shape_iterate_boolMatStep (Rfn x)
    ((List.range (Rfn x)).map fun i ↦
      (List.range (Rfn x)).map fun j ↦
        decide (i = j) || ((adjFn x).getD i []).getD j false ||
          ((adjFn x).getD j []).getD i false)
    ⟨by simp only [List.length_map, List.length_range], fun row hrow ↦ by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
      simp only [List.length_map, List.length_range]⟩ s
  refine (length_encList_le (encList encBool) _ (b := Rfn x * 3) fun row hrow ↦ ?_).trans
    (by rw [hshape.1])
  refine (length_encList_le encBool row (b := 1) fun _ _ ↦ ?_).trans
    (by rw [hshape.2 row hrow])
  simp only [encBool_apply, List.length_singleton, le_refl]

end Cslib.PolyTime
