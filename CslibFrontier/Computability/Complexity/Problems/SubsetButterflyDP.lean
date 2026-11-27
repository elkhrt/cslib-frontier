/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.Disjunctive
public import CslibFrontier.Computability.Complexity.Problems.SetPacking
public import CslibFrontier.Computability.Complexity.Problems.SubsetButterflyTable

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import CslibFrontier.Computability.Complexity.Problems.Graph
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# $O^*(2^{|\mathcal{U}|})$ Subset Dynamic Programming for Set Packing and Exact Covering

This module instantiates the streaming bit-rotation carry butterfly from
`CslibFrontier.Computability.Complexity.Problems.SubsetButterflyTable` on `SetSystem`
characteristic masks to prove $O(2^{|\mathcal{U}|} \cdot \mathrm{poly}(|I|))$
(`DecidableInExpTime` with exact base-$2$ rate $\delta = 1$) multi-tape Turing machine algorithms
for `SetPacking` and `ExactCover`, together with universe-parameterized `FPT` membership and the
Cai–Juedes sublogarithmic-universe `FPT` corollaries.

## Main results

* `CslibFrontier.ParameterizedComplexity.setPacking_decidableInExpTime_one`,
  `CslibFrontier.ParameterizedComplexity.exactCover_decidableInExpTime_one`: deterministic
  multi-tape
  Turing machine algorithms deciding `SetPacking` and `ExactCover` in time
  $O(2^{|\mathcal{U}|} \cdot (|I| + 1)^e)$ ($\delta = 1$).
* `CslibFrontier.ParameterizedComplexity.setPacking_mem_FPT_universe`,
  `CslibFrontier.ParameterizedComplexity.exactCover_mem_FPT_universe`: fixed-parameter tractability
  parameterized by universe cardinality $|\mathcal{U}|$.
* `CslibFrontier.ParameterizedComplexity.exists_fpt_decider_setPacking_sublog`,
  `CslibFrontier.ParameterizedComplexity.setPacking_sublog_mem_FPT`,
  `CslibFrontier.ParameterizedComplexity.exists_fpt_decider_exactCover_sublog`,
  `CslibFrontier.ParameterizedComplexity.exactCover_sublog_mem_FPT`: Cai–Juedes fixed-parameter
  tractability when $|\mathcal{U}| \le f(r) \cdot o(\log_2 |\mathcal{S}|)$.
-/

public section

namespace CslibFrontier.ParameterizedComplexity

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Multi-Stage Butterfly Iteration over `SetSystem` -/

private def distinctGround (S : SetSystem) : List ℕ :=
  (Graph.mk S.ground []).distinctVertices

private def masksOfSetSystem (S : SetSystem) : List (List Bool) :=
  let U := distinctGround S
  S.sets.map fun A => U.map fun u => decide (u ∈ A)

private def doubleCellStep (p : List SubsetDPCell × List SubsetDPCell) :
    List SubsetDPCell × List SubsetDPCell :=
  (p.1 ++ p.2, p.2 ++ p.2)

private theorem iterate_doubleCellStep (a b : SubsetDPCell) (k : ℕ) :
    (doubleCellStep^[k] ([a], [b])).1 = [a] ++ List.replicate (2 ^ k - 1) b ∧
      (doubleCellStep^[k] ([a], [b])).2 = List.replicate (2 ^ k) b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', doubleCellStep]
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine ⟨?_, ?_⟩
    · have hlen : 2 ^ k - 1 + 2 ^ k = 2 ^ (k + 1) - 1 := by
        rw [Nat.pow_succ, Nat.mul_two]; omega
      rw [ih.1, ih.2, List.append_assoc, ← List.replicate_add, hlen]
    · rw [ih.2, ← List.replicate_add, Nat.pow_succ, Nat.mul_two]

private def initCellTable (mode : Bool) (q : ℕ) : List SubsetDPCell :=
  let c0 : SubsetDPCell := (some 0, some 0)
  let cRest : SubsetDPCell := if mode then (some 0, some 0) else (none, none)
  (doubleCellStep^[q] ([c0], [cRest])).1

private theorem initCellTable_eq_tabulateLSB (mode : Bool) (masks : List (List Bool)) (q : ℕ) :
    initCellTable mode q =
      tabulateLSB q (fun bs =>
        let v := subsetDPPrefix mode masks 0 (setOfBits q bs)
        (v, v)) := by
  rw [initCellTable, (iterate_doubleCellStep _ _ q).1, ← tabulateLSB_eq_single_false]
  refine tabulateLSB_congr fun bs hbs => ?_
  rw [subsetDPPrefix_zero]
  cases mode
  · have hiff : setOfBits q bs = ∅ ↔ bs = List.replicate q false := by
      constructor
      · intro h
        refine List.ext_getElem (by simp [hbs]) fun j hj₁ _ => ?_
        rw [List.getElem_replicate]
        have hnot : (⟨j, hj₁.trans_eq hbs⟩ : Fin q) ∉ setOfBits q bs := by rw [h]; simp
        rw [mem_setOfBits_iff, List.getD_eq_getElem _ _ hj₁] at hnot
        cases hb : bs[j]
        · rfl
        · exact absurd hb hnot
      · rintro rfl; exact setOfBits_replicate_false q
    by_cases hbs0 : bs = List.replicate q false
    · simp [hbs0, setOfBits_replicate_false]
    · have hne : setOfBits q bs ≠ ∅ := mt hiff.mp hbs0
      simp [hbs0, hne]
  · by_cases hbs0 : bs = List.replicate q false <;> simp [hbs0]

private abbrev DPParams := (List (List Bool) × ℕ) × (ℕ × ℕ)

private abbrev encDPParams : DPParams ↪ List Bool :=
  encPair (encPair (encList encBits) encUnary) (encPair encUnary encUnary)

private abbrev DPState := DPParams × List SubsetDPCell

private abbrev encDPState : DPState ↪ List Bool := encPair encDPParams (encList encSubsetDPCell)

private def dpInit (mode : Bool) (S : SetSystem) : DPState :=
  let q := (distinctGround S).length
  let masks := masksOfSetSystem S
  (((masks, q), (0, 0)), initCellTable mode q)

private def dpStep (mode : Bool) (st : DPState) : DPState :=
  let masks := st.1.1.1
  let q := st.1.1.2
  let r := st.1.2.1
  let i := st.1.2.2
  let isLast := decide (i + 1 = q)
  let bit := (masks.getD r []).getD i false
  let rNext := if i + 1 = q then r + 1 else r
  let iNext := if i + 1 = q then 0 else i + 1
  (((masks, q), (rNext, iNext)), butterflyPass mode isLast bit st.2)

private def tmRunDP (mode : Bool) (S : SetSystem) : Option ℕ :=
  let q := (distinctGround S).length
  let m := S.sets.length
  let fin := ((dpStep mode)^[m * q] (dpInit mode S)).2
  (fin.foldl (fun _ c => c) (none, none)).1

private def tmDecideSetPacking (p : SetSystem × ℕ) : Bool :=
  isOverGroundBool p.1 &&
    if p.1.ground.isEmpty then decide (p.2 ≤ p.1.sets.length)
    else decide (p.2 ≤ (tmRunDP true p.1).getD 0)

private def tmDecideExactCover (p : SetSystem × ℕ) : Bool :=
  isOverGroundBool p.1 &&
    if p.1.ground.isEmpty then true
    else
      match tmRunDP false p.1 with
      | none => false
      | some v => decide (v ≤ p.2)

private theorem dpStep_invariant (mode : Bool) (S : SetSystem)
    (hq : 0 < (distinctGround S).length) :
    let q := (distinctGround S).length
    let masks := masksOfSetSystem S
    ((dpStep mode)^[masks.length * q] (dpInit mode S)).2 =
      tabulateLSB q (fun bs =>
        let v := subsetDPPrefix mode masks masks.length (setOfBits q bs)
        (v, v)) ∧
    ∀ k ≤ masks.length * q,
      let r := k / q
      let i := k % q
      ((dpStep mode)^[k] (dpInit mode S)).1 = ((masks, q), (r, i)) ∧
      ((dpStep mode)^[k] (dpInit mode S)).2 =
        tabulateLSB q (fun bs =>
          let T := setOfBits q (bs.rotate (q - i))
          (subsetDPPrefix mode masks r T,
           subsetDPExpectedCarry (subsetDPPrefix mode masks r) (masks.getD r []) i T)) := by
  intro q masks
  have hpass : ∀ (r : ℕ) (i : ℕ), i ≤ q →
      ((dpStep mode)^[i] (((masks, q), (r, 0)),
        tabulateLSB q (fun bs =>
          let v := subsetDPPrefix mode masks r (setOfBits q bs)
          (v, v)))).1 =
        ((masks, q), if i = q then (r + 1, 0) else (r, i)) ∧
      ((dpStep mode)^[i] (((masks, q), (r, 0)),
        tabulateLSB q (fun bs =>
          let v := subsetDPPrefix mode masks r (setOfBits q bs)
          (v, v)))).2 =
        if i = q then
          tabulateLSB q (fun bs =>
            let v := subsetDPPrefix mode masks (r + 1) (setOfBits q bs)
            (v, v))
        else
          tabulateLSB q (fun bs =>
            let T := setOfBits q (bs.rotate (q - i))
            (subsetDPPrefix mode masks r T,
             subsetDPExpectedCarry (subsetDPPrefix mode masks r) (masks.getD r []) i T)) := by
    intro r i hi
    induction i with
    | zero =>
      have hq_ne : 0 ≠ q := hq.ne
      simp only [Function.iterate_zero, id_eq, hq_ne, ↓reduceIte]
      refine ⟨trivial, tabulateLSB_congr fun bs hbs => ?_⟩
      rw [Nat.sub_zero, show bs.rotate q = bs from hbs ▸ List.rotate_length bs,
        subsetDPExpectedCarry_zero]
    | succ i ihi =>
      have hi_lt : i < q := Nat.lt_of_succ_le hi
      have hi_ne : i ≠ q := hi_lt.ne
      obtain ⟨hfst, hsnd⟩ := ihi hi_lt.le
      simp only [hi_ne, ↓reduceIte] at hfst hsnd
      rw [Function.iterate_succ_apply', dpStep, hfst, hsnd]
      dsimp only
      rw [butterflyPass_tabulateLSB_step hq hi_lt mode masks]
      by_cases hlast : i + 1 = q <;> simp [hlast, q]
  have hstage : ∀ r ≤ masks.length,
      ((dpStep mode)^[r * q] (dpInit mode S)) =
        (((masks, q), (r, 0)),
          tabulateLSB q (fun bs =>
            let v := subsetDPPrefix mode masks r (setOfBits q bs)
            (v, v))) := by
    intro r hr
    induction r with
    | zero =>
      simp only [Nat.zero_mul, Function.iterate_zero, id_eq, dpInit]
      exact Prod.ext rfl (initCellTable_eq_tabulateLSB mode masks q)
    | succ r ihr =>
      rw [show (r + 1) * q = q + r * q by ring, Function.iterate_add_apply,
        ihr (Nat.le_of_succ_le hr)]
      obtain ⟨h1, h2⟩ := hpass r q le_rfl
      simp only [↓reduceIte] at h1 h2
      exact Prod.ext h1 h2
  refine ⟨congrArg Prod.snd (hstage masks.length le_rfl), fun k hk => ?_⟩
  let r := k / q
  let i := k % q
  have hdiv_mod : r * q + i = k := by rw [mul_comm]; exact Nat.div_add_mod k q
  have hi_lt : i < q := Nat.mod_lt k hq
  have hr_le : r ≤ masks.length := by
    have : r * q ≤ masks.length * q := (Nat.le_add_right _ i).trans (hdiv_mod.symm ▸ hk)
    exact Nat.le_of_mul_le_mul_right this hq
  have hiter : (dpStep mode)^[k] (dpInit mode S) =
      (dpStep mode)^[i] (((masks, q), (r, 0)),
        tabulateLSB q (fun bs =>
          let v := subsetDPPrefix mode masks r (setOfBits q bs)
          (v, v))) := by
    rw [← hdiv_mod, Nat.add_comm, Function.iterate_add_apply, hstage r hr_le]
  dsimp only
  rw [hiter]
  obtain ⟨h1, h2⟩ := hpass r i hi_lt.le
  simp only [hi_lt.ne, ↓reduceIte] at h1 h2
  exact ⟨h1, h2⟩

private theorem masks_disjoint_iff (S : SetSystem) (hover : IsOverGround S)
    (i j : Fin S.sets.length) :
    let U := distinctGround S
    let masks := masksOfSetSystem S
    Disjoint (setOfBits U.length (masks[i]'(by simp [masks, masksOfSetSystem])))
      (setOfBits U.length (masks[j]'(by simp [masks, masksOfSetSystem]))) ↔
      Disjoint (S.sets[i].toFinset) (S.sets[j].toFinset) := by
  intro U masks
  have hget (idx : Fin S.sets.length) (k : Fin U.length) :
      (masks[idx]'(by simp [masks, masksOfSetSystem])).getD k.1 false = true ↔
        U[k] ∈ S.sets[idx] := by
    have hk_lt : k.1 < (distinctGround S).length := k.isLt
    rw [List.getD_eq_getElem _ _ (by simp [masks, masksOfSetSystem, hk_lt])]
    simp [U, masks, masksOfSetSystem]
  simp only [Finset.disjoint_left, mem_setOfBits_iff, List.mem_toFinset]
  constructor
  · intro h x hxi hxj
    have hxU : x ∈ U := (Graph.mem_distinctVertices (G := ⟨S.ground, []⟩)).mpr
      (hover S.sets[i] (List.getElem_mem i.isLt) x hxi)
    obtain ⟨k, hk_lt, rfl⟩ := List.mem_iff_getElem.mp hxU
    exact h ((hget i ⟨k, hk_lt⟩).mpr hxi) ((hget j ⟨k, hk_lt⟩).mpr hxj)
  · intro h k hki hkj
    exact h ((hget i k).mp hki) ((hget j k).mp hkj)

private theorem tmDecideSetPacking_eq_true_iff (p : SetSystem × ℕ) :
    tmDecideSetPacking p = true ↔ p ∈ SetPacking := by
  rcases p with ⟨S, r_tgt⟩
  simp only [tmDecideSetPacking, Bool.and_eq_true, isOverGroundBool_eq_true_iff, mem_setPacking_iff]
  by_cases hover : IsOverGround S
  · simp only [hover, true_and]
    by_cases hemp : S.ground.isEmpty
    · simp only [hemp, ↓reduceIte, decide_eq_true_eq]
      have hground_nil : S.ground = [] := List.isEmpty_iff.mp hemp
      constructor
      · intro hle
        refine ⟨Finset.univ, by simpa using hle, fun i _ j _ _ => ?_⟩
        have hempty_i : S.sets[i].toFinset = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
          fun x hx => by
            have := hover S.sets[i] (List.getElem_mem i.isLt) x (List.mem_toFinset.mp hx)
            rw [hground_nil] at this; exact List.not_mem_nil this
        dsimp only; rw [hempty_i]; exact Finset.disjoint_empty_left _
      · rintro ⟨C, hle, _⟩
        exact hle.trans ((Finset.card_le_univ C).trans_eq (Fintype.card_fin _))
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
      have hground_ne : S.ground ≠ [] := by simpa using hemp
      obtain ⟨u₀, hu₀⟩ := List.exists_mem_of_ne_nil S.ground hground_ne
      have hq_pos : 0 < (distinctGround S).length :=
        List.length_pos_of_mem ((Graph.mem_distinctVertices (G := ⟨S.ground, []⟩)).mpr hu₀)
      obtain ⟨hfin, -⟩ := dpStep_invariant true S hq_pos
      have hm_eq : (masksOfSetSystem S).length = S.sets.length := by simp [masksOfSetSystem]
      have hrun : tmRunDP true S =
          subsetDPPrefix true (masksOfSetSystem S) (masksOfSetSystem S).length
            (Finset.univ : Finset (Fin (distinctGround S).length)) := by
        dsimp only [tmRunDP]
        rw [← hm_eq, hfin, foldl_last_tabulateLSB, setOfBits_replicate_true]
      obtain ⟨v, hv, hv_gt⟩ :=
        subsetDPPrefix_true_spec (masksOfSetSystem S) (masksOfSetSystem S).length le_rfl
          (Finset.univ : Finset (Fin (distinctGround S).length))
      rw [hrun, hv, Option.getD_some]
      let eIdx : Fin (masksOfSetSystem S).length ≃ Fin S.sets.length := finCongr hm_eq
      constructor
      · intro hr_le
        obtain ⟨C, _, rfl, hdisj, _⟩ := hv_gt.1
        refine ⟨C.map eIdx.toEmbedding, by simpa using hr_le, ?_⟩
        intro i hi j hj hij
        obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
        obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
        have hij' : i' ≠ j' := fun he => hij (congrArg eIdx he)
        exact (masks_disjoint_iff S hover (eIdx i') (eIdx j')).mp (hdisj hi' hj' hij')
      · rintro ⟨C, hr_le, hdisj⟩
        refine hr_le.trans (hv_gt.2 ?_)
        refine ⟨C.map eIdx.symm.toEmbedding, fun j _ => j.isLt, by simp, ?_,
          fun _ _ => Finset.subset_univ _⟩
        intro i hi j hj hij
        obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
        obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
        have hij' : i' ≠ j' := fun he => hij (congrArg eIdx.symm he)
        simpa [eIdx] using (masks_disjoint_iff S hover i' j').mpr (hdisj hi' hj' hij')
  · simp [hover]

private theorem tmDecideExactCover_eq_true_iff (p : SetSystem × ℕ) :
    tmDecideExactCover p = true ↔ p ∈ ExactCover := by
  rcases p with ⟨S, r_tgt⟩
  simp only [tmDecideExactCover, Bool.and_eq_true, isOverGroundBool_eq_true_iff, mem_exactCover_iff]
  by_cases hover : IsOverGround S
  · simp only [hover, true_and]
    by_cases hemp : S.ground.isEmpty
    · simp only [hemp, ↓reduceIte, true_iff]
      have hground_nil : S.ground = [] := List.isEmpty_iff.mp hemp
      exact ⟨∅, Nat.zero_le _, by simp [SetSystem.IsCover, hground_nil],
        by rw [isDisjointSelection_iff]; simp⟩
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      have hground_ne : S.ground ≠ [] := by simpa using hemp
      obtain ⟨u₀, hu₀⟩ := List.exists_mem_of_ne_nil S.ground hground_ne
      have hq_pos : 0 < (distinctGround S).length :=
        List.length_pos_of_mem ((Graph.mem_distinctVertices (G := ⟨S.ground, []⟩)).mpr hu₀)
      obtain ⟨hfin, -⟩ := dpStep_invariant false S hq_pos
      have hm_eq : (masksOfSetSystem S).length = S.sets.length := by simp [masksOfSetSystem]
      have hrun : tmRunDP false S =
          subsetDPPrefix false (masksOfSetSystem S) (masksOfSetSystem S).length
            (Finset.univ : Finset (Fin (distinctGround S).length)) := by
        dsimp only [tmRunDP]
        rw [← hm_eq, hfin, foldl_last_tabulateLSB, setOfBits_replicate_true]
      obtain ⟨h_some, h_none⟩ :=
        subsetDPPrefix_false_spec (masksOfSetSystem S) (masksOfSetSystem S).length le_rfl
          (Finset.univ : Finset (Fin (distinctGround S).length))
      rw [hrun]
      let U := distinctGround S
      let masks := masksOfSetSystem S
      let eIdx : Fin masks.length ≃ Fin S.sets.length := finCongr hm_eq
      have hbit (i : Fin S.sets.length) (k : Fin U.length) :
          k ∈ setOfBits U.length masks[eIdx.symm i] ↔ U[k] ∈ S.sets[i] := by
        have hk_lt : k.1 < (distinctGround S).length := k.isLt
        rw [mem_setOfBits_iff]
        change ((masksOfSetSystem S)[i.1]'(by simp [masksOfSetSystem, i.isLt])).getD k.1 false =
          true ↔ U[k.1] ∈ S.sets[i.1]
        rw [List.getD_eq_getElem _ _ (by simp [masksOfSetSystem, hk_lt])]
        simp [U, masksOfSetSystem]
      have hcov_iff (C : Finset (Fin S.sets.length)) :
          (C.map eIdx.symm.toEmbedding).biUnion (fun j => setOfBits U.length masks[j]) =
            Finset.univ ↔ S.IsCover C := by
        simp only [Finset.ext_iff, Finset.mem_biUnion, Finset.mem_map, Equiv.coe_toEmbedding,
          Finset.mem_univ, iff_true, SetSystem.IsCover]
        constructor
        · intro h u hu
          have huU : u ∈ U := (Graph.mem_distinctVertices (G := ⟨S.ground, []⟩)).mpr hu
          obtain ⟨k, hk_lt, rfl⟩ := List.mem_iff_getElem.mp huU
          obtain ⟨j, ⟨i, hiC, rfl⟩, hkj⟩ := h ⟨k, hk_lt⟩
          exact ⟨i, hiC, (hbit i ⟨k, hk_lt⟩).mp hkj⟩
        · intro h k
          have hkG : U[k] ∈ S.ground :=
            (Graph.mem_distinctVertices (G := ⟨S.ground, []⟩)).mp (List.getElem_mem k.isLt)
          obtain ⟨i, hiC, hui⟩ := h U[k] hkG
          exact ⟨eIdx.symm i, ⟨i, hiC, rfl⟩, (hbit i k).mpr hui⟩
      cases hval : subsetDPPrefix false masks masks.length
        (Finset.univ : Finset (Fin U.length)) with
      | none =>
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨C, _, hcov, hdisj⟩
        refine h_none hval ⟨C.map eIdx.symm.toEmbedding, fun j _ => j.isLt, ?_,
          (hcov_iff C).mpr hcov⟩
        intro i hi j hj hij
        obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
        obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
        simpa [eIdx] using (masks_disjoint_iff S hover i' j').mpr
          (hdisj hi' hj' fun he => hij (congrArg eIdx.symm he))
      | some v =>
        simp only [decide_eq_true_eq]
        obtain ⟨⟨C₀, _, rfl, hdj₀, hbi₀⟩, hv_lb⟩ := h_some v hval
        constructor
        · intro hle
          let C := C₀.map eIdx.toEmbedding
          have hmap_back : C.map eIdx.symm.toEmbedding = C₀ := by
            ext j; simp [C]
          refine ⟨C, by simpa [C] using hle, (hcov_iff C).mp (hmap_back.symm ▸ hbi₀), ?_⟩
          intro i hi j hj hij
          obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
          obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
          exact (masks_disjoint_iff S hover (eIdx i') (eIdx j')).mp
            (hdj₀ hi' hj' fun he => hij (congrArg eIdx he))
        · rintro ⟨C, hle, hcov, hdisj⟩
          refine (hv_lb ?_).trans hle
          refine ⟨C.map eIdx.symm.toEmbedding, fun j _ => j.isLt, by simp, ?_,
            (hcov_iff C).mpr hcov⟩
          intro i hi j hj hij
          obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
          obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
          simpa [eIdx] using (masks_disjoint_iff S hover i' j').mpr
            (hdisj hi' hj' fun he => hij (congrArg eIdx.symm he))
  · simp [hover]

/-! ### 2. Multi-Tape Complexity Bounds and `DecidableInExpTime` Theorems -/

private theorem length_sets_le_encSetSystem (S : SetSystem) :
    S.sets.length ≤ (encSetSystem S).length := by
  calc S.sets.length ≤ (encNatSetList S.sets).length :=
        length_le_length_encList (encList encNat) S.sets
    _ ≤ (encSetSystem S).length := by rw [encSetSystem_apply]; enc_len

private theorem length_distinctGround_eq (S : SetSystem) :
    (distinctGround S).length = S.ground.toFinset.card :=
  Graph.length_distinctVertices ⟨S.ground, []⟩

private theorem length_distinctGround_le (S : SetSystem) :
    (distinctGround S).length ≤ (encSetSystem S).length := by
  rw [length_distinctGround_eq]
  calc S.ground.toFinset.card ≤ S.ground.length := List.toFinset_card_le _
    _ ≤ (encList encNat S.ground).length := length_le_length_encList encNat S.ground
    _ ≤ (encSetSystem S).length := by rw [encSetSystem_apply]; enc_len

open ComputableInPolyTime in
private theorem computableInPolyTime_distinctGround :
    ComputableInPolyTime distinctGround encSetSystem (encList encNat) := by
  unfold distinctGround
  exact Graph.computableInPolyTime_distinctVertices.comp
    (encGraph_mk_polyTime computableInPolyTime_setSystemGround (const []))

open ComputableInPolyTime in
private theorem computableInPolyTime_masksOfSetSystem :
    ComputableInPolyTime masksOfSetSystem encSetSystem (encList encBits) := by
  unfold masksOfSetSystem
  have hinner : ComputableInPolyTime
      (fun p : SetSystem × List ℕ =>
        (distinctGround p.1).map fun u => decide (u ∈ p.2))
      (encPair encSetSystem (encList encNat)) (encList encBool) := by
    have := computableInPolyTime_distinctGround
    fun_prop
  have htoBits : ComputableInPolyTime (fun w : List Bool => w) (encList encBool) encBits :=
    (bits_encList_polyTime encBool).2
  exact mapWithInput computableInPolyTime_setSystemSets (htoBits.comp hinner)

private theorem length_encMasks_le (S : SetSystem) :
    (encList encBits (masksOfSetSystem S)).length ≤
      3 * ((encSetSystem S).length + 1) ^ 2 := by
  have hm := length_sets_le_encSetSystem S
  have hq := length_distinctGround_le S
  have hrow : ∀ w ∈ masksOfSetSystem S, (encBits w).length ≤ (encSetSystem S).length := by
    intro w hw
    simp only [masksOfSetSystem, List.mem_map] at hw
    obtain ⟨A, _, rfl⟩ := hw
    simpa [encBits_apply] using hq
  calc (encList encBits (masksOfSetSystem S)).length
      ≤ (masksOfSetSystem S).length * (2 * (encSetSystem S).length + 1) :=
        length_encList_le encBits _ hrow
    _ = S.sets.length * (2 * (encSetSystem S).length + 1) := by simp [masksOfSetSystem]
    _ ≤ (encSetSystem S).length * (2 * (encSetSystem S).length + 1) :=
        Nat.mul_le_mul_right _ hm
    _ ≤ 3 * ((encSetSystem S).length + 1) ^ 2 := by nlinarith

open ComputableInPolyTime in
private theorem computableInO_dpInit (mode : Bool) :
    ∃ d, ComputableInO (dpInit mode) encSetSystem encDPState
      (fun S => 2 ^ S.ground.toFinset.card * ((encSetSystem S).length + 1) ^ d)
      (fun S => 2 ^ S.ground.toFinset.card * ((encSetSystem S).length + 1) ^ d) := by
  let c0 : SubsetDPCell := (some 0, some 0)
  let cRest : SubsetDPCell := if mode then (some 0, some 0) else (none, none)
  have hq_unary : ComputableInPolyTime (fun S : SetSystem => (distinctGround S).length)
      encSetSystem encUnary :=
    (length_list encNat).comp computableInPolyTime_distinctGround
  have hq_bin : ComputableInPolyTime (fun S : SetSystem => (distinctGround S).length)
      encSetSystem encNat :=
    unary_to_binary.comp hq_unary
  have hinitP : ComputableInPolyTime (fun _ : SetSystem => ([c0], [cRest]))
      encSetSystem (encPair (encList encSubsetDPCell) (encList encSubsetDPCell)) :=
    const ([c0], [cRest])
  have hparams : ComputableInPolyTime
      (fun S : SetSystem => ((masksOfSetSystem S, (distinctGround S).length), (0, 0)))
      encSetSystem encDPParams :=
    ((computableInPolyTime_masksOfSetSystem.prod hq_unary).prod
      ((const 0).prod (const 0)))
  obtain ⟨Tn, Sn, hTn, hSn, hn⟩ := hq_bin.exists_computableInO
  obtain ⟨Ti, Si, hTi, hSi, hi⟩ := hinitP.exists_computableInO
  obtain ⟨Tp, Sp, hTp, hSp, hp_inO⟩ := hparams.exists_computableInO
  have hstep : ComputableInO doubleCellStep
      (encPair (encList encSubsetDPCell) (encList encSubsetDPCell))
      (encPair (encList encSubsetDPCell) (encList encSubsetDPCell))
      (fun p => (encPair (encList encSubsetDPCell) (encList encSubsetDPCell) p).length)
      (fun p => (encPair (encList encSubsetDPCell) (encList encSubsetDPCell) p).length) := by
    have hp := (ComputableInO.listAppend'
      (ComputableInO.fst (encList encSubsetDPCell) (encList encSubsetDPCell))
      (ComputableInO.snd (encList encSubsetDPCell) (encList encSubsetDPCell))).prod
      (ComputableInO.listAppend'
        (ComputableInO.snd (encList encSubsetDPCell) (encList encSubsetDPCell))
        (ComputableInO.snd (encList encSubsetDPCell) (encList encSubsetDPCell)))
    refine hp.mono 4 (fun p => ?_) (fun p => ?_)
    all_goals simp only [length_encPair]; omega
  let cMax : ℕ := 2 * max (encSubsetDPCell c0).length (encSubsetDPCell cRest).length + 4
  let B : SetSystem → ℕ := fun S => 8 * cMax * 2 ^ S.ground.toFinset.card
  have hB : ∀ S k, k ≤ (distinctGround S).length →
      (encPair (encList encSubsetDPCell) (encList encSubsetDPCell)
        (doubleCellStep^[k] ([c0], [cRest]))).length ≤ B S := by
    intro S k hk
    rw [length_distinctGround_eq] at hk
    rw [length_encPair, (iterate_doubleCellStep c0 cRest k).1,
      (iterate_doubleCellStep c0 cRest k).2]
    simp only [List.singleton_append]
    have hrep : ∀ (m : ℕ) (r : SubsetDPCell),
        (encList encSubsetDPCell (List.replicate m r)).length =
          m * (2 * (encSubsetDPCell r).length + 1) := by
      intro m r
      rw [length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
    have hc0 : 2 * (encSubsetDPCell c0).length + 1 ≤ cMax := by
      dsimp [cMax]
      have := le_max_left (encSubsetDPCell c0).length (encSubsetDPCell cRest).length
      omega
    have hcr : 2 * (encSubsetDPCell cRest).length + 1 ≤ cMax := by
      dsimp [cMax]
      have := le_max_right (encSubsetDPCell c0).length (encSubsetDPCell cRest).length
      omega
    have hpow : 2 ^ k ≤ 2 ^ S.ground.toFinset.card := Nat.pow_le_pow_right (by omega) hk
    have h1 : (encList encSubsetDPCell (c0 :: List.replicate (2 ^ k - 1) cRest)).length ≤
        cMax + (2 ^ k - 1) * cMax := by
      rw [encList_cons, List.length_append, length_frame, hrep]
      exact Nat.add_le_add hc0 (Nat.mul_le_mul_left _ hcr)
    have h2 : (encList encSubsetDPCell (List.replicate (2 ^ k) cRest)).length ≤ 2 ^ k * cMax := by
      rw [hrep]; exact Nat.mul_le_mul_left _ hcr
    have hpow1 : 1 ≤ 2 ^ S.ground.toFinset.card := Nat.one_le_two_pow
    have hcMax4 : 4 ≤ cMax := by dsimp [cMax]; omega
    dsimp only [B]
    have hsub : (2 ^ k - 1) * cMax ≤ cMax * 2 ^ S.ground.toFinset.card := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left cMax ((Nat.sub_le (2 ^ k) 1).trans hpow)
    have hp_c : 2 ^ k * cMax ≤ cMax * 2 ^ S.ground.toFinset.card := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left cMax hpow
    have h1_c : cMax ≤ cMax * 2 ^ S.ground.toFinset.card :=
      Nat.le_mul_of_pos_right cMax hpow1
    have h4_c : 4 ≤ cMax * 2 ^ S.ground.toFinset.card := hcMax4.trans h1_c
    rw [show 8 * cMax * 2 ^ S.ground.toFinset.card = 8 * (cMax * 2 ^ S.ground.toFinset.card) by
      ring]
    omega
  have hit := ComputableInO.iterate hn hi hstep
    (R := B) (Q := B) (B := B) hB hB hB
  have hall := hp_inO.prod ((ComputableInO.fst _ _).comp_linear hit)
  have hpoly : PolyBounded (fun S : SetSystem => (encSetSystem S).length)
      (fun S => Tp S + Sp S + Tn S + Sn S + Ti S + Si S +
        ((encNat (distinctGround S).length).length + 1) ^ 2 +
        (encDPParams ((masksOfSetSystem S, (distinctGround S).length), (0, 0))).length + 16) := by
    have : PolyBounded (fun S : SetSystem => (encSetSystem S).length)
        (fun S => (encDPParams ((masksOfSetSystem S, (distinctGround S).length), (0, 0))).length) :=
      hparams.polyBounded_length
    growth_poly
  obtain ⟨Cp, dp, hCp⟩ := hpoly.exists_le
  refine ⟨dp + 2, hall.mono (2 * Cp + 32 * cMax + 8) (fun S => ?_) (fun S => ?_)⟩
  all_goals
    set X := 2 ^ S.ground.toFinset.card
    set L := (encSetSystem S).length
    have hX1 : 1 ≤ X := Nat.one_le_two_pow
    have hq_le : (distinctGround S).length + 1 ≤ L + 1 :=
      Nat.add_le_add_right (length_distinctGround_le S) 1
    have hover := hCp S
    change _ ≤ Cp * (L + 1) ^ dp at hover
    have hpow_dp : (L + 1) ^ dp ≤ (L + 1) ^ (dp + 2) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hover' : Tp S + Sp S + Tn S + Sn S + Ti S + Si S +
        ((encNat (distinctGround S).length).length + 1) ^ 2 +
        (encDPParams ((masksOfSetSystem S, (distinctGround S).length), (0, 0))).length + 16 ≤
        Cp * (X * (L + 1) ^ (dp + 2)) := by
      calc _ ≤ Cp * (L + 1) ^ dp := hover
        _ ≤ Cp * (L + 1) ^ (dp + 2) := Nat.mul_le_mul_left Cp hpow_dp
        _ ≤ Cp * (X * (L + 1) ^ (dp + 2)) :=
            Nat.mul_le_mul_left Cp (Nat.le_mul_of_pos_left _ hX1)
    have hBS : B S = 8 * cMax * X := rfl
    have hcnt_sq : ((distinctGround S).length + 1) *
        ((encNat (distinctGround S).length).length + 1) ^ 2 ≤
        Cp * (X * (L + 1) ^ (dp + 2)) := by
      have hc : ((encNat (distinctGround S).length).length + 1) ^ 2 ≤ Cp * (L + 1) ^ dp := by omega
      calc ((distinctGround S).length + 1) *
            ((encNat (distinctGround S).length).length + 1) ^ 2
          ≤ (L + 1) * (Cp * (L + 1) ^ dp) := Nat.mul_le_mul hq_le hc
        _ = Cp * (L + 1) ^ (dp + 1) := by rw [pow_succ]; ring
        _ ≤ Cp * (L + 1) ^ (dp + 2) :=
            Nat.mul_le_mul_left Cp (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
        _ ≤ Cp * (X * (L + 1) ^ (dp + 2)) :=
            Nat.mul_le_mul_left Cp (Nat.le_mul_of_pos_left _ hX1)
    have hBX : ((distinctGround S).length + 1) * (2 * B S) ≤
        16 * cMax * (X * (L + 1) ^ (dp + 2)) := by
      calc ((distinctGround S).length + 1) * (2 * B S)
          ≤ (L + 1) * (16 * cMax * X) :=
            Nat.mul_le_mul hq_le (by rw [hBS]; exact le_of_eq (by ring))
        _ = 16 * cMax * (X * (L + 1) ^ 1) := by ring
        _ ≤ 16 * cMax * (X * (L + 1) ^ (dp + 2)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left X
              (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)))
    have hBS_1 : B S ≤ 8 * cMax * (X * (L + 1) ^ (dp + 2)) := by
      rw [hBS]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right X
        (Nat.one_le_pow _ _ (Nat.succ_pos _)))
    have hcnt1 : (encNat (distinctGround S).length).length ≤
        ((encNat (distinctGround S).length).length + 1) ^ 2 :=
      (Nat.le_succ _).trans (Nat.le_self_pow (n := 2) (by decide) _)
    try rw [show ((distinctGround S).length + 1) *
        (B S + B S + ((encNat (distinctGround S).length).length + 1) ^ 2) =
        ((distinctGround S).length + 1) * (2 * B S) +
          ((distinctGround S).length + 1) *
            ((encNat (distinctGround S).length).length + 1) ^ 2 by ring]
    generalize X * (L + 1) ^ (dp + 2) = Z at hover' hcnt_sq hBX hBS_1 ⊢
    rw [show (2 * Cp + 32 * cMax + 8) * (Z + 1) =
        Cp * Z + Cp * Z + 16 * cMax * Z + 8 * cMax * Z + 8 * cMax * Z + 8 * Z +
          (2 * Cp + 32 * cMax + 8) by ring]
    omega

open ComputableInPolyTime in
private theorem computableInO_dpStep (mode : Bool) :
    ∃ d, ComputableInO (dpStep mode) encDPState encDPState
      (fun st => (encDPState st).length +
        (st.2.length + 1) * ((encDPParams st.1).length +
          listMax (fun r => (encSubsetDPCell r).length) st.2 + 32) ^ d)
      (fun st => (encDPState st).length +
        (st.2.length + 1) * ((encDPParams st.1).length +
          listMax (fun r => (encSubsetDPCell r).length) st.2 + 32) ^ d) := by
  obtain ⟨db, hbfly⟩ := computableInO_butterflyPass
  have hnextP : ComputableInPolyTime
      (fun p : DPParams =>
        let q := p.1.2
        let r := p.2.1
        let i := p.2.2
        ((p.1.1, q), (if i + 1 = q then r + 1 else r, if i + 1 = q then 0 else i + 1)))
      encDPParams encDPParams := by
    have hm : ComputableInPolyTime (fun p : DPParams => p.1.1) encDPParams (encList encBits) := by
      unfold encDPParams; fun_prop
    have hq : ComputableInPolyTime (fun p : DPParams => p.1.2) encDPParams encUnary := by
      unfold encDPParams; fun_prop
    have hr : ComputableInPolyTime (fun p : DPParams => p.2.1) encDPParams encUnary := by
      unfold encDPParams; fun_prop
    have hi : ComputableInPolyTime (fun p : DPParams => p.2.2) encDPParams encUnary := by
      unfold encDPParams; fun_prop
    have hcp : ComputableInPolyTime (fun p : DPParams => decide (p.2.2 + 1 = p.1.2))
        encDPParams encBool :=
      (ComputableInDegree.eq encUnary).computableInPolyTime.comp ((unary_succ.comp hi).prod hq)
    exact (hm.prod hq).prod
      ((hcp.ite_decide (unary_succ.comp hr) hr).prod
       (hcp.ite_decide (const 0) (unary_succ.comp hi)))
  have hflags : ComputableInPolyTime
      (fun p : DPParams =>
        ((mode, decide (p.2.2 + 1 = p.1.2)), (p.1.1.getD p.2.1 []).getD p.2.2 false))
      encDPParams encSubsetDPFlags := by
    have hm : ComputableInPolyTime (fun p : DPParams => p.1.1) encDPParams (encList encBits) := by
      unfold encDPParams; fun_prop
    have hq : ComputableInPolyTime (fun p : DPParams => p.1.2) encDPParams encUnary := by
      unfold encDPParams; fun_prop
    have hr : ComputableInPolyTime (fun p : DPParams => p.2.1) encDPParams encUnary := by
      unfold encDPParams; fun_prop
    have hi : ComputableInPolyTime (fun p : DPParams => p.2.2) encDPParams encUnary := by
      unfold encDPParams; fun_prop
    have hcp : ComputableInPolyTime (fun p : DPParams => decide (p.2.2 + 1 = p.1.2))
        encDPParams encBool :=
      (ComputableInDegree.eq encUnary).computableInPolyTime.comp ((unary_succ.comp hi).prod hq)
    exact ((const mode).prod hcp).prod (bitsGetDWithInput (listGetDWithInput hm hr []) hi false)
  obtain ⟨T₁, S₁, hT₁, hS₁, hP₁⟩ := hnextP.exists_computableInO
  obtain ⟨c₁, d₁, hcd₁⟩ := (hT₁.add hS₁).exists_le
  obtain ⟨T₂, S₂, hT₂, hS₂, hP₂⟩ := hflags.exists_computableInO
  obtain ⟨c₂, d₂, hcd₂⟩ := (hT₂.add hS₂).exists_le
  have hfl_st := hP₂.comp (ComputableInO.fst encDPParams (encList encSubsetDPCell))
  have hfull := (hP₁.comp (ComputableInO.fst encDPParams (encList encSubsetDPCell))).prod
    (hbfly.comp (hfl_st.prod (ComputableInO.snd encDPParams (encList encSubsetDPCell))))
  let d := max (max d₁ d₂) db + 1
  let M : DPState → ℕ := fun st =>
    (encDPParams st.1).length + listMax (fun r => (encSubsetDPCell r).length) st.2 + 32
  let P : DPState → ℕ := fun st => (st.2.length + 1) * M st ^ d
  refine ⟨d, hfull.mono (c₁ + c₂ + 20) (fun st => ?_) (fun st => ?_)⟩
  all_goals
    dsimp only [Function.comp_def]
    have hM1 : 1 ≤ M st := by dsimp [M]; omega
    have hP_pow : ∀ e ≤ d, (st.2.length + 1) * M st ^ e ≤ P st := fun e he =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM1 he)
    have hparam1 : T₁ st.1 + S₁ st.1 ≤ c₁ * P st := by
      calc T₁ st.1 + S₁ st.1 ≤ c₁ * ((encDPParams st.1).length + 1) ^ d₁ := hcd₁ st.1
        _ ≤ c₁ * M st ^ d₁ := Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (by dsimp [M]; omega) d₁)
        _ ≤ c₁ * P st := Nat.mul_le_mul_left c₁
            ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (hP_pow d₁ (by omega)))
    have hparam2 : T₂ st.1 + S₂ st.1 ≤ c₂ * P st := by
      calc T₂ st.1 + S₂ st.1 ≤ c₂ * ((encDPParams st.1).length + 1) ^ d₂ := hcd₂ st.1
        _ ≤ c₂ * M st ^ d₂ := Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left (by dsimp [M]; omega) d₂)
        _ ≤ c₂ * P st := Nat.mul_le_mul_left c₂
            ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (hP_pow d₂ (by omega)))
    have hdb : (st.2.length + 1) *
        (listMax (fun c => (encSubsetDPCell c).length) st.2 + 32) ^ db ≤ P st :=
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [M]; omega) db)).trans
        (hP_pow db (by omega))
    have hL_le : (encList encSubsetDPCell st.2).length ≤ (encDPState st).length := by
      rw [encDPState, length_encPair]; omega
    have hfl_len : ∀ fl : SubsetDPFlags, (encSubsetDPFlags fl).length ≤ 12 := by
      rintro ⟨⟨a, b⟩, c⟩
      change (encPair (encPair encBool encBool) encBool ((a, b), c)).length ≤ 12
      simp
    have hP1 : 32 ≤ P st := by
      calc 32 ≤ M st ^ 1 := by rw [pow_one]; dsimp only [M]; omega
        _ ≤ M st ^ d := Nat.pow_le_pow_right hM1 (by omega)
        _ ≤ P st := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    let fl_st : SubsetDPFlags :=
      ((mode, decide (st.1.2.2 + 1 = st.1.1.2)), (st.1.1.1.getD st.1.2.1 []).getD st.1.2.2 false)
    have hpair_fl : (encPair encSubsetDPFlags (encList encSubsetDPCell) (fl_st, st.2)).length ≤
        (encDPState st).length + 25 := by
      have h1 := hfl_len fl_st
      rw [length_encPair]
      dsimp only
      omega
    unfold encDPState at hL_le hpair_fl ⊢
    dsimp only [P] at hparam1 hparam2 hdb hP1 ⊢
    generalize (st.2.length + 1) * M st ^ d = Z at hparam1 hparam2 hdb hP1 ⊢
    have hcZ : (c₁ + c₂ + 20) * ((encPair encDPParams (encList encSubsetDPCell) st).length + Z +
      1) =
        c₁ * Z + c₂ * Z + 20 * Z +
          c₁ * (encPair encDPParams (encList encSubsetDPCell) st).length +
          c₂ * (encPair encDPParams (encList encSubsetDPCell) st).length +
          20 * (encPair encDPParams (encList encSubsetDPCell) st).length +
          (c₁ + c₂ + 20) := by ring
    rw [hcZ]
    omega

private theorem dpState_size_bound (mode : Bool) (S : SetSystem)
    (hq : 0 < (distinctGround S).length) {k : ℕ}
    (hk : k ≤ (masksOfSetSystem S).length * (distinctGround S).length) :
    let st := (dpStep mode)^[k] (dpInit mode S)
    let L := (encSetSystem S).length
    st.2.length = 2 ^ S.ground.toFinset.card ∧
      (encDPParams st.1).length ≤ 16 * (L + 1) ^ 2 ∧
      (∀ c ∈ st.2, (encSubsetDPCell c).length ≤ 6 * (L + 1)) ∧
      (encDPState st).length ≤
        2 ^ S.ground.toFinset.card * (14 * (L + 1)) + 32 * (L + 1) ^ 2 + 8 := by
  intro st L
  obtain ⟨-, hinv⟩ := dpStep_invariant mode S hq
  obtain ⟨h1, h2⟩ := hinv k hk
  have hm_le : (masksOfSetSystem S).length ≤ L :=
    (show (masksOfSetSystem S).length = S.sets.length by simp [masksOfSetSystem]).trans_le
      (length_sets_le_encSetSystem S)
  have hq_le : (distinctGround S).length ≤ L := length_distinctGround_le S
  have hlen2 : st.2.length = 2 ^ S.ground.toFinset.card := by
    dsimp only [st]; rw [h2, length_tabulateLSB, length_distinctGround_eq]
  have hparams_len : (encDPParams st.1).length ≤ 16 * (L + 1) ^ 2 := by
    dsimp only [st]
    rw [h1]
    unfold encDPParams
    rw [length_encPair, length_encPair, length_encPair]
    simp only [encUnary_apply, List.length_replicate]
    have hmasks_len : (encList encBits (masksOfSetSystem S)).length ≤ 3 * (L + 1) ^ 2 :=
      length_encMasks_le S
    have hr_le : k / (distinctGround S).length ≤ L :=
      (Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hk)).trans hm_le
    have hi_le : k % (distinctGround S).length ≤ L :=
      (Nat.mod_lt k hq).le.trans hq_le
    nlinarith
  have hopt_bound : ∀ o : Option ℕ, (∀ v, o = some v → v ≤ L) →
      (encOption encNat o).length ≤ L + 2 := by
    intro o ho
    cases o with
    | none => simp
    | some v =>
      have hvL : v ≤ L := ho v rfl
      have hv2 : v < 2 ^ (L + 1) :=
        hvL.trans_lt (Nat.lt_two_pow_self.trans_le
          (Nat.pow_le_pow_right (by omega) (Nat.le_succ L)))
      have hn := length_encNat_le_of_lt_two_pow hv2
      simp only [encOption_some, List.length_cons]
      omega
  have hcell_len : ∀ c ∈ st.2, (encSubsetDPCell c).length ≤ 6 * (L + 1) := by
    intro c hc
    dsimp [st] at hc
    rw [h2] at hc
    obtain ⟨bs, _, rfl⟩ := mem_tabulateLSB_exists hc
    set r := k / (distinctGround S).length
    set T := setOfBits (distinctGround S).length
      (bs.rotate ((distinctGround S).length - k % (distinctGround S).length))
    have hr_le : r ≤ L :=
      (Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hk)).trans hm_le
    have h1_opt := hopt_bound (subsetDPPrefix mode (masksOfSetSystem S) r T) fun v hv =>
      (subsetDPPrefix_bound mode (masksOfSetSystem S) r T v hv).trans hr_le
    have h2_opt := hopt_bound
      (subsetDPExpectedCarry (subsetDPPrefix mode (masksOfSetSystem S) r)
        ((masksOfSetSystem S).getD r []) (k % (distinctGround S).length) T) fun v hv =>
      (subsetDPExpectedCarry_bound mode (masksOfSetSystem S) r
        (k % (distinctGround S).length) ((masksOfSetSystem S).getD r []) T v hv).trans hr_le
    change (encPair (encOption encNat) (encOption encNat) _).length ≤ 6 * (L + 1)
    rw [length_encPair]
    dsimp only
    omega
  have hlist_len : (encList encSubsetDPCell st.2).length ≤
      2 ^ S.ground.toFinset.card * (14 * (L + 1)) := by
    have hl := length_encList_le encSubsetDPCell st.2 hcell_len
    rw [hlen2] at hl
    exact hl.trans (Nat.mul_le_mul_left _ (by omega))
  refine ⟨hlen2, hparams_len, hcell_len, ?_⟩
  unfold encDPState
  rw [length_encPair]
  omega

open ComputableInPolyTime in
private theorem computableInO_tmRunDP (mode : Bool) :
    ∃ e, ComputableInO (tmRunDP mode) encSetSystem (encOption encNat)
      (fun S => 2 ^ S.ground.toFinset.card * ((encSetSystem S).length + 1) ^ e)
      (fun S => 2 ^ S.ground.toFinset.card * ((encSetSystem S).length + 1) ^ e) := by
  have hcnt_pt : ComputableInPolyTime
      (fun S : SetSystem => S.sets.length * (distinctGround S).length)
      encSetSystem encNat :=
    unary_to_binary.comp (unary_mul.comp
      (((length_list (encList encNat)).comp computableInPolyTime_setSystemSets).prod
       ((length_list encNat).comp computableInPolyTime_distinctGround)))
  obtain ⟨Tcnt, Scnt, hTcnt, hScnt, hcnt⟩ := hcnt_pt.exists_computableInO
  obtain ⟨d₀, hinit⟩ := computableInO_dpInit mode
  obtain ⟨ds, hstep⟩ := computableInO_dpStep mode
  let stMax : SetSystem → ℕ := fun S =>
    2 ^ S.ground.toFinset.card * (14 * ((encSetSystem S).length + 1)) +
      32 * ((encSetSystem S).length + 1) ^ 2 + 64
  let rdMax : SetSystem → ℕ := fun S =>
    stMax S + 2 * 2 ^ S.ground.toFinset.card *
      (22 * ((encSetSystem S).length + 1) ^ 2 + 40) ^ ds
  have hst_all : ∀ (S : SetSystem) (k : ℕ),
      k ≤ S.sets.length * (distinctGround S).length →
      (encDPState ((dpStep mode)^[k] (dpInit mode S))).length ≤ stMax S ∧
      ((encDPState ((dpStep mode)^[k] (dpInit mode S))).length +
        (((dpStep mode)^[k] (dpInit mode S)).2.length + 1) *
          ((encDPParams ((dpStep mode)^[k] (dpInit mode S)).1).length +
            listMax (fun r => (encSubsetDPCell r).length)
              ((dpStep mode)^[k] (dpInit mode S)).2 + 32) ^ ds) ≤ rdMax S := by
    intro S k hk
    by_cases hq : 0 < (distinctGround S).length
    · have hk' : k ≤ (masksOfSetSystem S).length * (distinctGround S).length := by
        simpa [masksOfSetSystem] using hk
      obtain ⟨hlen2, hpar, hcell, htot⟩ := dpState_size_bound mode S hq hk'
      have hlm : listMax (fun r => (encSubsetDPCell r).length)
          ((dpStep mode)^[k] (dpInit mode S)).2 ≤ 6 * ((encSetSystem S).length + 1) :=
        listMax_le hcell
      have hst_le : (encDPState ((dpStep mode)^[k] (dpInit mode S))).length ≤ stMax S :=
        htot.trans (by dsimp [stMax]; omega)
      refine ⟨hst_le, Nat.add_le_add hst_le ?_⟩
      have h2q : ((dpStep mode)^[k] (dpInit mode S)).2.length + 1 ≤
          2 * 2 ^ S.ground.toFinset.card := by
        rw [hlen2]; have := @Nat.one_le_two_pow S.ground.toFinset.card; omega
      have hbase : (encDPParams ((dpStep mode)^[k] (dpInit mode S)).1).length +
          listMax (fun r => (encSubsetDPCell r).length) ((dpStep mode)^[k] (dpInit mode S)).2 +
          32 ≤ 22 * ((encSetSystem S).length + 1) ^ 2 + 40 := by
        have hL_sq : (encSetSystem S).length + 1 ≤ ((encSetSystem S).length + 1) ^ 2 :=
          Nat.le_self_pow (n := 2) (by decide) _
        omega
      exact (Nat.mul_le_mul h2q (Nat.pow_le_pow_left hbase ds)).trans_eq (by ring)
    · have hq0 : (distinctGround S).length = 0 := by omega
      have hk0 : k = 0 := by rw [hq0, Nat.mul_zero] at hk; omega
      subst hk0
      simp only [Function.iterate_zero, id_eq, dpInit, hq0, initCellTable]
      have hmasks_len := length_encMasks_le S
      have hc0_len : (encSubsetDPCell (some 0, some 0)).length ≤ 10 := by decide
      have hpar0 : (encDPParams ((masksOfSetSystem S, 0), (0, 0))).length ≤
          12 * ((encSetSystem S).length + 1) ^ 2 + 4 := by
        unfold encDPParams
        rw [length_encPair, length_encPair, length_encPair]
        simp only [encUnary_apply, List.length_replicate]
        omega
      have htab0 : (encList encSubsetDPCell [(some 0, some 0)]).length ≤ 24 := by
        simp only [encList_cons, encList_nil, List.length_append, length_frame, List.length_nil]
        omega
      have hst0 : (encDPState (((masksOfSetSystem S, 0), (0, 0)), [(some 0, some 0)])).length ≤
          stMax S := by
        unfold encDPState
        rw [length_encPair]
        have h1 : 1 ≤ ((encSetSystem S).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
        dsimp only [stMax]
        omega
      refine ⟨hst0, Nat.add_le_add hst0 ?_⟩
      have hlm0 : listMax (fun r => (encSubsetDPCell r).length) [(some 0, some 0)] ≤ 10 :=
        listMax_le fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hc0_len
      have hbase0 : (encDPParams ((masksOfSetSystem S, 0), (0, 0))).length +
          listMax (fun r => (encSubsetDPCell r).length) [(some 0, some 0)] + 32 ≤
          22 * ((encSetSystem S).length + 1) ^ 2 + 40 := by
        have : 1 ≤ ((encSetSystem S).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
        omega
      have hX1 : 1 ≤ 2 ^ S.ground.toFinset.card := Nat.one_le_two_pow
      simpa using Nat.mul_le_mul (by omega : 2 ≤ 2 * 2 ^ S.ground.toFinset.card)
        (Nat.pow_le_pow_left hbase0 ds)
  have hit := ComputableInO.iterate hcnt hinit hstep
    (R := rdMax) (Q := rdMax) (B := stMax)
    (fun S k hk => (hst_all S k hk).2)
    (fun S k hk => (hst_all S k hk).2)
    (fun S k hk => (hst_all S k hk).1)
  have hlast := (ComputableInO.fst (encOption encNat) (encOption encNat)).comp_linear
    (computableInO_lastSubsetCell.comp
      ((ComputableInO.snd encDPParams (encList encSubsetDPCell)).comp_linear hit))
  have hoverhead : PolyBounded (fun S : SetSystem => (encSetSystem S).length)
      (fun S => Tcnt S + Scnt S +
        ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2 +
        (22 * ((encSetSystem S).length + 1) ^ 2 + 40) ^ ds + 64) := by
    have : PolyBounded (fun S : SetSystem => (encSetSystem S).length)
        (fun S => (encNat (S.sets.length * (distinctGround S).length)).length) :=
      hcnt_pt.polyBounded_length
    growth_poly
  obtain ⟨Cp, dp, hCp⟩ := hoverhead.exists_le
  set E := d₀ + dp + 6
  refine ⟨E, hlast.mono (64 * (Cp + 64)) (fun S => ?_) (fun S => ?_)⟩
  all_goals
    dsimp only [Function.comp_def]
    set X := 2 ^ S.ground.toFinset.card
    set L := (encSetSystem S).length
    have hX1 : 1 ≤ X := Nat.one_le_two_pow
    have hL1 : 1 ≤ L + 1 := Nat.succ_pos L
    have hcnt_val : S.sets.length * (distinctGround S).length + 1 ≤ (L + 1) ^ 2 := by
      have hm := length_sets_le_encSetSystem S
      have hq := length_distinctGround_le S
      nlinarith [Nat.mul_le_mul hm hq]
    have hover := hCp S
    change Tcnt S + Scnt S +
        ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2 +
        (22 * (L + 1) ^ 2 + 40) ^ ds + 64 ≤ Cp * (L + 1) ^ dp at hover
    have hstMax_bound : stMax S ≤ 112 * (X * (L + 1) ^ 2) := by
      dsimp only [stMax]
      change X * (14 * (L + 1)) + 32 * (L + 1) ^ 2 + 64 ≤ 112 * (X * (L + 1) ^ 2)
      have h1 : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (n := 2) (by decide) _
      have h2 : 1 ≤ X * (L + 1) ^ 2 := Nat.mul_pos hX1 (Nat.one_le_pow _ _ hL1)
      have h3 : X * (14 * (L + 1)) ≤ 14 * (X * (L + 1) ^ 2) := by
        calc X * (14 * (L + 1)) = 14 * (X * (L + 1)) := by ring
          _ ≤ 14 * (X * (L + 1) ^ 2) := Nat.mul_le_mul_left 14 (Nat.mul_le_mul_left X h1)
      have h4 : 32 * (L + 1) ^ 2 ≤ 32 * (X * (L + 1) ^ 2) :=
        Nat.mul_le_mul_left 32 (Nat.le_mul_of_pos_left _ hX1)
      omega
    have hrdMax_bound : rdMax S ≤ (2 * Cp + 112) * (X * (L + 1) ^ (dp + 2)) := by
      dsimp only [rdMax]
      change stMax S + 2 * X * (22 * (L + 1) ^ 2 + 40) ^ ds ≤
        (2 * Cp + 112) * (X * (L + 1) ^ (dp + 2))
      have hpow_ds : (22 * (L + 1) ^ 2 + 40) ^ ds ≤ Cp * (L + 1) ^ dp := by omega
      have hpow2 : (L + 1) ^ 2 ≤ (L + 1) ^ (dp + 2) :=
        Nat.pow_le_pow_right hL1 (Nat.le_add_left 2 dp)
      have hpow_dp : (L + 1) ^ dp ≤ (L + 1) ^ (dp + 2) :=
        Nat.pow_le_pow_right hL1 (Nat.le_add_right dp 2)
      have h1 := hstMax_bound.trans
        (Nat.mul_le_mul_left 112 (Nat.mul_le_mul_left X hpow2))
      have h2 : 2 * X * (22 * (L + 1) ^ 2 + 40) ^ ds ≤
          2 * Cp * (X * (L + 1) ^ (dp + 2)) := by
        calc 2 * X * (22 * (L + 1) ^ 2 + 40) ^ ds
            ≤ 2 * X * (Cp * (L + 1) ^ (dp + 2)) :=
              Nat.mul_le_mul_left (2 * X) (hpow_ds.trans (Nat.mul_le_mul_left Cp hpow_dp))
          _ = 2 * Cp * (X * (L + 1) ^ (dp + 2)) := by ring
      rw [Nat.add_mul]
      omega
    have hfin_st := (hst_all S (S.sets.length * (distinctGround S).length) le_rfl).1
    have hfin_list : (encList encSubsetDPCell
        ((dpStep mode)^[S.sets.length * (distinctGround S).length] (dpInit mode S)).2).length ≤
        stMax S := by
      have := hfin_st; unfold encDPState at this; rw [length_encPair] at this; omega
    have hfin_len_lm :
        (((dpStep mode)^[S.sets.length * (distinctGround S).length] (dpInit mode S)).2.length + 1) *
        (listMax (fun r => (encSubsetDPCell r).length)
          ((dpStep mode)^[S.sets.length * (distinctGround S).length] (dpInit mode S)).2 + 5) ≤
        32 * (X * (L + 1) ^ 2) := by
      by_cases hq : 0 < (distinctGround S).length
      · obtain ⟨hlen2, _, hcell, _⟩ := dpState_size_bound mode S hq
          (k := S.sets.length * (distinctGround S).length) (by simp [masksOfSetSystem])
        have hlm := listMax_le hcell
        rw [hlen2]
        calc (X + 1) * (listMax (fun r => (encSubsetDPCell r).length) _ + 5)
            ≤ (2 * X) * (11 * (L + 1)) := Nat.mul_le_mul (by omega) (by omega)
          _ = 22 * (X * (L + 1)) := by ring
          _ ≤ 32 * (X * (L + 1) ^ 2) := Nat.mul_le_mul (by omega)
              (Nat.mul_le_mul_left X (Nat.le_self_pow (n := 2) (by decide) _))
      · have hq0 : (distinctGround S).length = 0 := by omega
        simp only [hq0, Nat.mul_zero, Function.iterate_zero, id_eq, dpInit, initCellTable,
          List.length_cons, List.length_nil]
        have hc0_len : (encSubsetDPCell (some 0, some 0)).length ≤ 10 := by decide
        have hlm0 : listMax (fun r => (encSubsetDPCell r).length) [(some 0, some 0)] ≤ 10 :=
          listMax_le fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hc0_len
        have : 1 ≤ X * (L + 1) ^ 2 := Nat.mul_pos hX1 (Nat.one_le_pow _ _ hL1)
        omega
    have hfin_lm_only :
        listMax (fun r => (encSubsetDPCell r).length)
          ((dpStep mode)^[S.sets.length * (distinctGround S).length] (dpInit mode S)).2 + 5 ≤
        32 * (X * (L + 1) ^ 2) :=
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans hfin_len_lm
    have hpE_d0 : X * (L + 1) ^ d₀ ≤ X * (L + 1) ^ E :=
      Nat.mul_le_mul_left X (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega))
    have hpE_2 : X * (L + 1) ^ 2 ≤ X * (L + 1) ^ E :=
      Nat.mul_le_mul_left X (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega))
    have hpE_dp : (L + 1) ^ dp ≤ X * (L + 1) ^ E :=
      (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega)).trans (Nat.le_mul_of_pos_left _ hX1)
    have hcnt_mul : (S.sets.length * (distinctGround S).length + 1) *
        (rdMax S + stMax S +
          ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2) ≤
        (3 * Cp + 224) * (X * (L + 1) ^ E) := by
      have hsum_rd : rdMax S + stMax S +
          ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2 ≤
          (3 * Cp + 224) * (X * (L + 1) ^ (dp + 2)) := by
        have h1 := hstMax_bound.trans (Nat.mul_le_mul_left 112
          (Nat.mul_le_mul_left X (Nat.pow_le_pow_right hL1 (Nat.le_add_left 2 dp))))
        have h2 : ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2 ≤
            Cp * (X * (L + 1) ^ (dp + 2)) := by
          calc _ ≤ Cp * (L + 1) ^ dp := by omega
            _ ≤ Cp * (L + 1) ^ (dp + 2) :=
                Nat.mul_le_mul_left Cp (Nat.pow_le_pow_right hL1 (Nat.le_add_right dp 2))
            _ ≤ Cp * (X * (L + 1) ^ (dp + 2)) :=
                Nat.mul_le_mul_left Cp (Nat.le_mul_of_pos_left _ hX1)
        have hexp : (3 * Cp + 224) * (X * (L + 1) ^ (dp + 2)) =
            (2 * Cp + 112) * (X * (L + 1) ^ (dp + 2)) + 112 * (X * (L + 1) ^ (dp + 2)) +
              Cp * (X * (L + 1) ^ (dp + 2)) := by ring
        rw [hexp]; omega
      calc _ ≤ (L + 1) ^ 2 * ((3 * Cp + 224) * (X * (L + 1) ^ (dp + 2))) :=
            Nat.mul_le_mul hcnt_val hsum_rd
        _ = (3 * Cp + 224) * (X * (L + 1) ^ (dp + 4)) := by
            rw [show dp + 4 = 2 + (dp + 2) by omega, Nat.pow_add]; ring
        _ ≤ (3 * Cp + 224) * (X * (L + 1) ^ E) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left X
              (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega)))
    have hcnt_len_le : (encNat (S.sets.length * (distinctGround S).length)).length ≤
        Cp * (X * (L + 1) ^ E) := by
      have h1 : (encNat (S.sets.length * (distinctGround S).length)).length ≤
          ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2 :=
        (Nat.le_succ _).trans (Nat.le_self_pow (n := 2) (by decide) _)
      have h2 : ((encNat (S.sets.length * (distinctGround S).length)).length + 1) ^ 2 ≤
          Cp * (L + 1) ^ dp := by omega
      exact (h1.trans h2).trans (Nat.mul_le_mul_left Cp hpE_dp)
    have hTcnt_le : Tcnt S + Scnt S ≤ Cp * (X * (L + 1) ^ E) :=
      (by omega : Tcnt S + Scnt S ≤ Cp * (L + 1) ^ dp).trans (Nat.mul_le_mul_left Cp hpE_dp)
    have hrd_E : rdMax S ≤ (2 * Cp + 112) * (X * (L + 1) ^ E) :=
      hrdMax_bound.trans (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left X (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega))))
    have hst_E : stMax S ≤ 112 * (X * (L + 1) ^ E) :=
      hstMax_bound.trans (Nat.mul_le_mul_left 112 hpE_2)
    have hlm_E := hfin_len_lm.trans (Nat.mul_le_mul_left 32 hpE_2)
    have hlm_only_E := hfin_lm_only.trans (Nat.mul_le_mul_left 32 hpE_2)
    have hlist_E := hfin_list.trans hst_E
    change _ ≤ 64 * (Cp + 64) * (X * (L + 1) ^ E + 1)
    generalize X * (L + 1) ^ E = Z at *
    rw [show 64 * (Cp + 64) * (Z + 1) =
        (3 * Cp + 224) * Z + (2 * Cp + 112) * Z + Cp * Z + Cp * Z + 57 * (Cp * Z) +
          3760 * Z + 64 * Cp + 4096 by ring]
    omega

open ComputableInPolyTime in
/-- **Subset dynamic programming for `SetPacking`**: `SetPacking` is decidable on multi-tape Turing
machines in time $O(2^{|\mathcal{U}|} \cdot (|I| + 1)^e)$ (`DecidableInExpTime` with $\delta =
  1$). -/
theorem setPacking_decidableInExpTime_one :
    DecidableInExpTime SetPacking encSetCover (fun p => p.1.ground.toFinset.card) 1 := by
  obtain ⟨e₀, hrun⟩ := computableInO_tmRunDP true
  have hguard : ComputableInPolyTime
      (fun p : SetSystem × ℕ => isOverGroundBool p.1) encSetCover encBool :=
    computableInPolyTime_isOverGroundBool.comp (fst encSetSystem encNat)
  have hemp : ComputableInPolyTime
      (fun p : SetSystem × ℕ => p.1.ground.isEmpty) encSetCover encBool :=
    (listIsEmpty' encNat).comp (computableInPolyTime_setSystemGround.comp
      (fst encSetSystem encNat))
  have htriv : ComputableInPolyTime
      (fun p : SetSystem × ℕ => decide (p.2 ≤ p.1.sets.length)) encSetCover encBool := by
    have hr := snd encSetSystem encNat
    have hm := unary_to_binary.comp ((length_list (encList encNat)).comp
      (computableInPolyTime_setSystemSets.comp (fst encSetSystem encNat)))
    exact binary_le' hr hm
  have hcmp : ComputableInPolyTime
      (fun q : ℕ × Option ℕ => decide (q.1 ≤ q.2.getD 0))
      (encPair encNat (encOption encNat)) encBool := by
    have hget : ComputableInPolyTime (fun q : ℕ × Option ℕ => q.2.getD 0)
        (encPair encNat (encOption encNat)) encNat :=
      optionGetDWithInput (snd _ _) (const 0)
    exact binary_le' (fst _ _) hget
  obtain ⟨dG, _, hG⟩ := hguard.exists_degree
  obtain ⟨dE, _, hE⟩ := hemp.exists_degree
  obtain ⟨dT, _, hT⟩ := htriv.exists_degree
  obtain ⟨dC, _, hC⟩ := hcmp.exists_degree
  obtain ⟨dAnd, _, hAnd⟩ := bool_and.exists_degree
  have hbranch := hC.inO.comp
    ((ComputableInO.snd encSetSystem encNat).prod
      (hrun.comp (ComputableInO.fst encSetSystem encNat)))
  have hfull : ComputableInO tmDecideSetPacking encSetCover encBool _ _ :=
    hAnd.inO.comp (hG.inO.prod (hE.inO.ite hT.inO hbranch))
  have ⟨l_run, _, _⟩ := hrun
  set E := max (max dG dE) (max dT (e₀ + dC + 2)) + 2
  refine DecidableInExpTime.of_computableInO hfull
    (fun p => (tmDecideSetPacking_eq_true_iff p).symm)
    ((4 * (l_run + 4)) ^ dC + 5 ^ dAnd + 16) E fun p => ?_
  dsimp only [Function.comp_def]
  set X := 2 ^ p.1.ground.toFinset.card
  set L := (encSetCover p).length
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hL1 : 1 ≤ L + 1 := Nat.succ_pos L
  have hS_le : (encSetSystem p.1).length ≤ L := by
    dsimp only [L]; unfold encSetCover; rw [length_encPair]; omega
  have hp2_le : (encNat p.2).length ≤ L := by
    dsimp only [L]; unfold encSetCover; rw [length_encPair]; omega
  have hpow_le : ∀ a ≤ E, (L + 1) ^ a ≤ X * (L + 1) ^ E := fun a ha =>
    (Nat.pow_le_pow_right hL1 ha).trans (Nat.le_mul_of_pos_left _ hX1)
  have hrun_le : X * ((encSetSystem p.1).length + 1) ^ e₀ ≤ X * (L + 1) ^ e₀ :=
    Nat.mul_le_mul_left X (Nat.pow_le_pow_left (Nat.add_le_add_right hS_le 1) e₀)
  have hrun_out_poly : (encOption encNat (tmRunDP true p.1)).length ≤ L + 2 := by
    by_cases hq : 0 < (distinctGround p.1).length
    · obtain ⟨hfin, -⟩ := dpStep_invariant true p.1 hq
      have hm_eq : (masksOfSetSystem p.1).length = p.1.sets.length := by simp [masksOfSetSystem]
      have hrun_eq : tmRunDP true p.1 =
          subsetDPPrefix true (masksOfSetSystem p.1) (masksOfSetSystem p.1).length
            (Finset.univ : Finset (Fin (distinctGround p.1).length)) := by
        dsimp only [tmRunDP]
        rw [← hm_eq, hfin, foldl_last_tabulateLSB, setOfBits_replicate_true]
      rw [hrun_eq]
      cases hval : subsetDPPrefix true (masksOfSetSystem p.1)
        (masksOfSetSystem p.1).length
        (Finset.univ : Finset (Fin (distinctGround p.1).length)) with
      | none => simp
      | some v =>
        have hv_le : v ≤ L :=
          (subsetDPPrefix_bound true _ _ _ v hval).trans
            (hm_eq.le.trans ((length_sets_le_encSetSystem p.1).trans hS_le))
        have hv2 : v < 2 ^ (L + 1) :=
          hv_le.trans_lt (Nat.lt_two_pow_self.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.le_succ L)))
        have hn := length_encNat_le_of_lt_two_pow hv2
        simp only [encOption_some, List.length_cons]
        omega
    · have hq0 : (distinctGround p.1).length = 0 := by omega
      have hrun0 : tmRunDP true p.1 = some 0 := by
        dsimp only [tmRunDP]
        rw [hq0, Nat.mul_zero, Function.iterate_zero, id_eq, dpInit, hq0, initCellTable]
        simp
      rw [hrun0]; simp [encOption_some]
  have hcmp_in : (encPair encNat (encOption encNat) (p.2, tmRunDP true p.1)).length + 1 ≤
      4 * (L + 1) := by rw [length_encPair]; dsimp only; omega
  have hcmp_pow : ((encPair encNat (encOption encNat) (p.2, tmRunDP true p.1)).length + 1) ^ dC ≤
      4 ^ dC * (X * (L + 1) ^ E) := by
    calc _ ≤ (4 * (L + 1)) ^ dC := Nat.pow_le_pow_left hcmp_in dC
      _ = 4 ^ dC * (L + 1) ^ dC := Nat.mul_pow _ _ _
      _ ≤ 4 ^ dC * (X * (L + 1) ^ E) :=
          Nat.mul_le_mul_left _ (hpow_le dC (by dsimp [E]; omega))
  have hG_E := hpow_le dG (by dsimp [E]; omega)
  have hE_E := hpow_le dE (by dsimp [E]; omega)
  have hT_E := hpow_le dT (by dsimp [E]; omega)
  have he0_E : X * ((encSetSystem p.1).length + 1) ^ e₀ ≤ X * (L + 1) ^ E :=
    hrun_le.trans (Nat.mul_le_mul_left X (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega)))
  have hL_E := hpow_le 1 (by dsimp [E]; omega)
  have hpair_bool : ∀ q : Bool × Bool, (encPair encBool encBool q).length = 4 :=
    fun _ => by simp
  simp only [hpair_bool]
  have hand_E : (4 + 1) ^ dAnd ≤ 5 ^ dAnd * (X * (L + 1) ^ E) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos hX1 (Nat.one_le_pow _ _ hL1))
  have h4_le : 4 ^ dC ≤ (4 * (l_run + 4)) ^ dC :=
    Nat.pow_le_pow_left (by omega) dC
  have hcmp_pow' := hcmp_pow.trans (Nat.mul_le_mul_right _ h4_le)
  have hite_bound :
      (if p.1.ground.isEmpty then (L + 1) ^ dT
       else L + (L + X * ((encSetSystem p.1).length + 1) ^ e₀) +
         ((encPair encNat (encOption encNat) (p.2, tmRunDP true p.1)).length + 1) ^ dC) ≤
      ((4 * (l_run + 4)) ^ dC + 4) * (X * (L + 1) ^ E) := by
    split_ifs
    · exact hT_E.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    · rw [pow_one] at hL_E
      generalize X * (L + 1) ^ E = Z at he0_E hL_E hcmp_pow' ⊢
      rw [Nat.add_mul]
      omega
  have hmain : (L + 1) ^ dG + ((L + 1) ^ dE +
      (if p.1.ground.isEmpty then (L + 1) ^ dT
       else L + (L + X * ((encSetSystem p.1).length + 1) ^ e₀) +
         ((encPair encNat (encOption encNat) (p.2, tmRunDP true p.1)).length + 1) ^ dC)) +
      (4 + 1) ^ dAnd ≤ ((4 * (l_run + 4)) ^ dC + 5 ^ dAnd + 16) * (X * (L + 1) ^ E) := by
    generalize X * (L + 1) ^ E = Z at hG_E hE_E hand_E hite_bound ⊢
    rw [show ((4 * (l_run + 4)) ^ dC + 5 ^ dAnd + 16) * Z =
        ((4 * (l_run + 4)) ^ dC + 4) * Z + 5 ^ dAnd * Z + 12 * Z by ring]
    omega
  rw [one_mul, Real.rpow_natCast]
  exact (Nat.cast_le.mpr hmain).trans_eq (by dsimp only [X, L]; push_cast; ring)

open ComputableInPolyTime in
/-- **Subset dynamic programming for `ExactCover`**: `ExactCover` is decidable on multi-tape Turing
machines in time $O(2^{|\mathcal{U}|} \cdot (|I| + 1)^e)$ (`DecidableInExpTime` with $\delta =
  1$). -/
theorem exactCover_decidableInExpTime_one :
    DecidableInExpTime ExactCover encSetCover (fun p => p.1.ground.toFinset.card) 1 := by
  obtain ⟨e₀, hrun⟩ := computableInO_tmRunDP false
  have hguard : ComputableInPolyTime
      (fun p : SetSystem × ℕ => isOverGroundBool p.1) encSetCover encBool :=
    computableInPolyTime_isOverGroundBool.comp (fst encSetSystem encNat)
  have hemp : ComputableInPolyTime
      (fun p : SetSystem × ℕ => p.1.ground.isEmpty) encSetCover encBool :=
    (listIsEmpty' encNat).comp (computableInPolyTime_setSystemGround.comp
      (fst encSetSystem encNat))
  have hcmp : ComputableInPolyTime
      (fun q : ℕ × Option ℕ =>
        match q.2 with | none => false | some v => decide (v ≤ q.1))
      (encPair encNat (encOption encNat)) encBool := by
    have heq : (fun q : ℕ × Option ℕ =>
        match q.2 with | none => false | some v => decide (v ≤ q.1)) =
        fun q => q.2.elim false fun v => decide (v ≤ q.1) := by
      funext ⟨_, o⟩; cases o <;> rfl
    rw [heq]
    refine optionElimWithInput (snd _ _) (const false) ?_
    exact binary_le' (snd _ _) (fst _ _ |>.comp (fst _ _))
  obtain ⟨dG, _, hG⟩ := hguard.exists_degree
  obtain ⟨dE, _, hE⟩ := hemp.exists_degree
  obtain ⟨dC, _, hC⟩ := hcmp.exists_degree
  obtain ⟨dAnd, _, hAnd⟩ := bool_and.exists_degree
  have hbranch := hC.inO.comp
    ((ComputableInO.snd encSetSystem encNat).prod
      (hrun.comp (ComputableInO.fst encSetSystem encNat)))
  have hfull : ComputableInO tmDecideExactCover encSetCover encBool _ _ :=
    hAnd.inO.comp (hG.inO.prod (hE.inO.ite (ComputableInO.const true) hbranch))
  set E := max dG (max dE (e₀ + dC + 2)) + 2
  refine DecidableInExpTime.of_computableInO hfull
    (fun p => (tmDecideExactCover_eq_true_iff p).symm)
    (4 ^ dC + 5 ^ dAnd + 16) E fun p => ?_
  dsimp only [Function.comp_def]
  set X := 2 ^ p.1.ground.toFinset.card
  set L := (encSetCover p).length
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hL1 : 1 ≤ L + 1 := Nat.succ_pos L
  have hS_le : (encSetSystem p.1).length ≤ L := by
    dsimp only [L]; unfold encSetCover; rw [length_encPair]; omega
  have hp2_le : (encNat p.2).length ≤ L := by
    dsimp only [L]; unfold encSetCover; rw [length_encPair]; omega
  have hpow_le : ∀ a ≤ E, (L + 1) ^ a ≤ X * (L + 1) ^ E := fun a ha =>
    (Nat.pow_le_pow_right hL1 ha).trans (Nat.le_mul_of_pos_left _ hX1)
  have hrun_out_poly : (encOption encNat (tmRunDP false p.1)).length ≤ L + 2 := by
    by_cases hq : 0 < (distinctGround p.1).length
    · obtain ⟨hfin, -⟩ := dpStep_invariant false p.1 hq
      have hm_eq : (masksOfSetSystem p.1).length = p.1.sets.length := by simp [masksOfSetSystem]
      have hrun_eq : tmRunDP false p.1 =
          subsetDPPrefix false (masksOfSetSystem p.1) (masksOfSetSystem p.1).length
            (Finset.univ : Finset (Fin (distinctGround p.1).length)) :=
            by
        dsimp only [tmRunDP]
        rw [← hm_eq, hfin, foldl_last_tabulateLSB, setOfBits_replicate_true]
      rw [hrun_eq]
      cases hval : subsetDPPrefix false (masksOfSetSystem p.1)
        (masksOfSetSystem p.1).length
        (Finset.univ : Finset (Fin (distinctGround p.1).length)) with
      | none => simp
      | some v =>
        have hv_le : v ≤ L :=
          (subsetDPPrefix_bound false _ _ _ v hval).trans
            (hm_eq.le.trans ((length_sets_le_encSetSystem p.1).trans hS_le))
        have hv2 : v < 2 ^ (L + 1) :=
          hv_le.trans_lt (Nat.lt_two_pow_self.trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.le_succ L)))
        have hn := length_encNat_le_of_lt_two_pow hv2
        simp only [encOption_some, List.length_cons]
        omega
    · have hq0 : (distinctGround p.1).length = 0 := by omega
      have hrun0 : tmRunDP false p.1 = some 0 := by
        dsimp only [tmRunDP]
        rw [hq0, Nat.mul_zero, Function.iterate_zero, id_eq, dpInit, hq0, initCellTable]
        simp
      rw [hrun0]; simp [encOption_some]
  have hcmp_in : (encPair encNat (encOption encNat) (p.2, tmRunDP false p.1)).length + 1 ≤
      4 * (L + 1) := by rw [length_encPair]; dsimp only; omega
  have hcmp_pow : ((encPair encNat (encOption encNat) (p.2, tmRunDP false p.1)).length + 1) ^ dC ≤
      4 ^ dC * (X * (L + 1) ^ E) := by
    calc _ ≤ (4 * (L + 1)) ^ dC := Nat.pow_le_pow_left hcmp_in dC
      _ = 4 ^ dC * (L + 1) ^ dC := Nat.mul_pow _ _ _
      _ ≤ 4 ^ dC * (X * (L + 1) ^ E) :=
          Nat.mul_le_mul_left _ (hpow_le dC (by dsimp [E]; omega))
  have hG_E := hpow_le dG (by dsimp [E]; omega)
  have hE_E := hpow_le dE (by dsimp [E]; omega)
  have he0_E : X * ((encSetSystem p.1).length + 1) ^ e₀ ≤ X * (L + 1) ^ E :=
    Nat.mul_le_mul_left X ((Nat.pow_le_pow_left (Nat.add_le_add_right hS_le 1) e₀).trans
      (Nat.pow_le_pow_right hL1 (by dsimp [E]; omega)))
  have hL_E := hpow_le 1 (by dsimp [E]; omega)
  have hpair_bool : ∀ q : Bool × Bool, (encPair encBool encBool q).length = 4 :=
    fun _ => by simp
  simp only [hpair_bool]
  have hand_E : (4 + 1) ^ dAnd ≤ 5 ^ dAnd * (X * (L + 1) ^ E) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos hX1 (Nat.one_le_pow _ _ hL1))
  have hite_bound :
      (if p.1.ground.isEmpty then L
       else L + (L + X * ((encSetSystem p.1).length + 1) ^ e₀) +
         ((encPair encNat (encOption encNat) (p.2, tmRunDP false p.1)).length + 1) ^ dC) ≤
      (4 ^ dC + 4) * (X * (L + 1) ^ E) := by
    split_ifs
    · rw [pow_one] at hL_E
      exact (Nat.le_succ L).trans (hL_E.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
    · rw [pow_one] at hL_E
      generalize X * (L + 1) ^ E = Z at he0_E hL_E hcmp_pow ⊢
      rw [Nat.add_mul]
      omega
  have hmain : (L + 1) ^ dG + ((L + 1) ^ dE +
      (if p.1.ground.isEmpty then L
       else L + (L + X * ((encSetSystem p.1).length + 1) ^ e₀) +
         ((encPair encNat (encOption encNat) (p.2, tmRunDP false p.1)).length + 1) ^ dC)) +
      (4 + 1) ^ dAnd ≤ (4 ^ dC + 5 ^ dAnd + 16) * (X * (L + 1) ^ E) := by
    generalize X * (L + 1) ^ E = Z at hG_E hE_E hand_E hite_bound ⊢
    rw [show (4 ^ dC + 5 ^ dAnd + 16) * Z =
        (4 ^ dC + 4) * Z + 5 ^ dAnd * Z + 12 * Z by ring]
    omega
  rw [one_mul, Real.rpow_natCast]
  exact (Nat.cast_le.mpr hmain).trans_eq (by dsimp only [X, L]; push_cast; ring)

/-! ### 3. Universe-Parameterized `FPT` and Cai–Juedes Sublogarithmic Corollaries -/

/-- `SetPacking` is fixed-parameter tractable when parameterized by universe cardinality
$|\mathcal{U}|$. -/
theorem setPacking_mem_FPT_universe :
    SetPacking ∈ FPT encSetCover (fun p => p.1.ground.toFinset.card) :=
  setPacking_decidableInExpTime_one.mem_FPT

/-- `ExactCover` is fixed-parameter tractable when parameterized by universe cardinality
$|\mathcal{U}|$. -/
theorem exactCover_mem_FPT_universe :
    ExactCover ∈ FPT encSetCover (fun p => p.1.ground.toFinset.card) :=
  exactCover_decidableInExpTime_one.mem_FPT

private theorem sets_length_le_encSetCover (p : SetSystem × ℕ) :
    p.1.sets.length ≤ (encSetCover p).length + 1 := by
  have h1 := length_sets_le_encSetSystem p.1
  have h2 : (encSetSystem p.1).length ≤ (encSetCover p).length := by
    unfold encSetCover; rw [length_encPair]; omega
  omega

/-- **Uniform Cai–Juedes FPT decider for `SetPacking`**: a single multi-tape Turing machine decides
`SetPacking` on all inputs and halts within FPT time $F(r) \cdot (|I| + 1)^c$ on every instance
with $|\mathcal{U}| \le f(r) \cdot s(|\mathcal{S}|)$, for arbitrary $f \ge 0$ and
$s(n) = o(\log_2 n)$. -/
theorem exists_fpt_decider_setPacking_sublog {f s : ℕ → ℝ}
    (hf : ∀ r, 0 ≤ f r) (hs : IsSublogBaseTwo s) :
    ∃ (dec : SetSystem × ℕ → Bool) (t w : SetSystem × ℕ → ℕ) (F : ℕ → ℕ) (c : ℕ),
      ComputableInTimeAndSpace dec encSetCover encBool t w ∧
      (∀ p, p ∈ SetPacking ↔ dec p = true) ∧
      ∀ p, (p.1.ground.toFinset.card : ℝ) ≤ f p.2 * s p.1.sets.length →
        t p ≤ F p.2 * ((encSetCover p).length + 1) ^ c :=
  exists_fpt_decider_of_decidableInExpTime_sublog zero_le_one
    setPacking_decidableInExpTime_one sets_length_le_encSetCover hf hs

/-- **Guarded Cai–Juedes `FPT` membership for `SetPacking`**: restricting `SetPacking` to any
polynomial-time guard enforcing $|\mathcal{U}| \le f(r) \cdot s(|\mathcal{S}|)$ ($f \ge 0$,
$s(n) = o(\log_2 n)$) places the problem in `FPT` parameterized by `r`. -/
theorem setPacking_sublog_mem_FPT {f s : ℕ → ℝ}
    (hf : ∀ r, 0 ≤ f r) (hs : IsSublogBaseTwo s)
    {guard : SetSystem × ℕ → Bool}
    (hguard : ComputableInPolyTime guard encSetCover encBool)
    (hbound : ∀ p, guard p = true →
      (p.1.ground.toFinset.card : ℝ) ≤ f p.2 * s p.1.sets.length) :
    {p | guard p = true} ∩ SetPacking ∈ FPT encSetCover Prod.snd :=
  mem_FPT_of_decidableInExpTime_sublog zero_le_one
    setPacking_decidableInExpTime_one sets_length_le_encSetCover hf hs hguard hbound

/-- **Uniform Cai–Juedes FPT decider for `ExactCover`**. -/
theorem exists_fpt_decider_exactCover_sublog {f s : ℕ → ℝ}
    (hf : ∀ r, 0 ≤ f r) (hs : IsSublogBaseTwo s) :
    ∃ (dec : SetSystem × ℕ → Bool) (t w : SetSystem × ℕ → ℕ) (F : ℕ → ℕ) (c : ℕ),
      ComputableInTimeAndSpace dec encSetCover encBool t w ∧
      (∀ p, p ∈ ExactCover ↔ dec p = true) ∧
      ∀ p, (p.1.ground.toFinset.card : ℝ) ≤ f p.2 * s p.1.sets.length →
        t p ≤ F p.2 * ((encSetCover p).length + 1) ^ c :=
  exists_fpt_decider_of_decidableInExpTime_sublog zero_le_one
    exactCover_decidableInExpTime_one sets_length_le_encSetCover hf hs

/-- **Guarded Cai–Juedes `FPT` membership for `ExactCover`**. -/
theorem exactCover_sublog_mem_FPT {f s : ℕ → ℝ}
    (hf : ∀ r, 0 ≤ f r) (hs : IsSublogBaseTwo s)
    {guard : SetSystem × ℕ → Bool}
    (hguard : ComputableInPolyTime guard encSetCover encBool)
    (hbound : ∀ p, guard p = true →
      (p.1.ground.toFinset.card : ℝ) ≤ f p.2 * s p.1.sets.length) :
    {p | guard p = true} ∩ ExactCover ∈ FPT encSetCover Prod.snd :=
  mem_FPT_of_decidableInExpTime_sublog zero_le_one
    exactCover_decidableInExpTime_one sets_length_le_encSetCover hf hs hguard hbound

end CslibFrontier.ParameterizedComplexity
