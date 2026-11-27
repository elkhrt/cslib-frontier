module

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.BlockTape
public import CslibFrontier.Computability.Circuit.ObliviousCircuit
import CslibFrontier.Computability.Circuit.Boolean.OpValue
import CslibFrontier.Computability.Circuit.Encoding.Evaluation
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Pippenger–Fischer $O(T \log T)$ Oblivious Circuit Simulation

This module assembles the full Pippenger–Fischer oblivious Boolean
circuit simulation of any deterministic multi-tape Turing machine (`Turing.MultiTapeTM`),
building on `CslibFrontier.Computability.Circuit.BlockTape` and
`CslibFrontier.Computability.Circuit.ObliviousCircuit`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Oblivious.emitSchedulePass`: scheduled half-tape
  rebalance pass across levels `0..., L - 2` at step `t`.
* `CslibFrontier.Computability.Circuit.Oblivious.initStateW`: initial wire layout for
  arbitrary input-tape wire indices `inputWires`.
* `CslibFrontier.Computability.Circuit.Oblivious.emitTmStep`: one complete oblivious TM step
  (finite transition table + tape shifts + scheduled rebalances).
* `CslibFrontier.Computability.Circuit.Oblivious.buildGates`: full `T`-step oblivious gate
  builder.
* `CslibFrontier.Computability.Circuit.Oblivious.obliviousCircuitWithWires`: resulting
  `Circuit Boolean.signature totalInputs 1` with optional output negation.

## Main results

* `CslibFrontier.Computability.Circuit.Oblivious.size_obliviousCircuitWithWires_le`: the
  oblivious circuit has $O((T + 1)(\log_2(\max(T, N) + 2) + 1))$ gates, independent of
  `totalInputs`.
* `CslibFrontier.Computability.Circuit.Oblivious.eval_obliviousCircuitWithWires`: exact
  evaluation equivalence against `tm.runFrom (tm.initCfg input) T`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Oblivious

open Turing MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-! ### Helper lemmas for list indexing and `OutView` encoding -/

private theorem getD_mem_of_lt {α : Type} {l : List α} {k : ℕ} {d : α} (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk

private theorem getD_take_append {α : Type} (l mid : List α) (k j : ℕ) (d : α)
    (hk : k + mid.length ≤ l.length) :
    ((l.take k ++ mid ++ l.drop (k + mid.length)).getD j d) =
      if j < k then l.getD j d
      else if j < k + mid.length then mid.getD (j - k) d
      else l.getD j d := by
  have htk : (l.take k).length = k := by simp [List.length_take]; omega
  by_cases hj1 : j < k
  · simp only [hj1, ↓reduceIte]
    rw [List.append_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj1,
      ← List.getD_eq_getElem?_getD]
  · simp only [hj1, ↓reduceIte]
    by_cases hj2 : j < k + mid.length
    · simp only [hj2, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [List.length_append, htk]; exact hj2),
        List.getElem?_append_right (by omega), htk, ← List.getD_eq_getElem?_getD]
    · simp only [hj2, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [List.length_append, htk]; omega),
        List.length_append, htk, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
      congr 2; omega

/-- Four-state index of `OutView`: `empty ↦ 0`, `one false ↦ 1`, `one true ↦ 2`, `many ↦ 3`. -/
@[expose] def outViewIdx : OutView → Fin 4
  | .empty => 0
  | .one false => 1
  | .one true => 2
  | .many => 3

/-- Default empty `TapeW` fallback for `List.getD`. -/
@[expose] def defaultTapeW : TapeW := ((0, 0), ([], []))

/-! ### Tape-step, half-tape rebalance, and scheduled rebalance pass specs -/

theorem emitShiftLevel0_spec {x : List Bool} {g : Gates} {fls sPop sKeep sPush w0 w1 : ℕ}
    {lw : LevelW} {lvl : BlockLevel 0} (hg : g.WF x.length)
    (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (hsPop : sPop < g.2) (hsKeep : sKeep < g.2) (hsPush : sPush < g.2)
    (hw0 : w0 < g.2) (hw1 : w1 < g.2) (henc : lw.Encodes g x lvl)
    (hcnt : 1 ≤ lvl.cnt ∧ lvl.cnt ≤ 4)
    (hoh : (g.val x sPop = true ∧ g.val x sKeep = false ∧ g.val x sPush = false) ∨
           (g.val x sPop = false ∧ g.val x sKeep = true ∧ g.val x sPush = false) ∨
           (g.val x sPop = false ∧ g.val x sKeep = false ∧ g.val x sPush = true)) :
    let res := emitShiftLevel0 g fls sPop sKeep sPush w0 w1 lw
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧ res.1.1.length = g.1.length + 80 ∧
    res.2.Encodes res.1 x
      (if g.val x sPop then (BlockLevel.pop0 lvl).2
       else if g.val x sKeep then lvl
       else BlockLevel.push0 (g.val x w0, g.val x w1) lvl) := by
  have hstep : ∀ {gBase : Gates} (hgB : gBase.WF x.length) (hextB : Gates.Extends g gBase)
      (xs : List (ℕ × ℕ × ℕ)) (hxs : ∀ t ∈ xs, t.1 < g.2 ∧ t.2.1 < g.2 ∧ t.2.2 < g.2),
      let m := emitMap gBase (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) xs
      m.1.WF x.length ∧ Gates.Extends gBase m.1 ∧ m.2.length = xs.length ∧
      m.1.1.length = gBase.1.length + 5 * xs.length ∧
      (∀ w ∈ m.2, w < m.1.2) ∧
      (∀ (i : ℕ) (hi : i < xs.length),
        m.1.val x (m.2.getD i 0) =
          if g.val x sPop then g.val x xs[i].1
          else if g.val x sKeep then g.val x xs[i].2.1
          else g.val x xs[i].2.2) := by
    intro gBase hgB hextB xs hxs
    refine emitMap_spec (K := 5)
      (spec := fun t : ℕ × ℕ × ℕ => if g.val x sPop then g.val x t.1
        else if g.val x sKeep then g.val x t.2.1 else g.val x t.2.2)
      hgB fun g₀ t ht hg₀ hext₀ => ?_
    have hext := Gates.extends_trans hextB hext₀
    have hle : g.2 ≤ g₀.2 := by
      rcases hext with ⟨rr, hrr⟩; rw [hg.2, hg₀.2, hrr, List.length_append]; omega
    have hti := hxs t ht
    have hm := Gates.gMux3_spec hg₀ (lt_of_lt_of_le hsPop hle) (lt_of_lt_of_le hti.1 hle)
      (lt_of_lt_of_le hsKeep hle) (lt_of_lt_of_le hti.2.1 hle)
      (lt_of_lt_of_le hsPush hle) (lt_of_lt_of_le hti.2.2 hle)
    refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
    rw [hm.2.2.2.2,
      Gates.val_of_extends_wf hg hext hsPop, Gates.val_of_extends_wf hg hext hsKeep,
      Gates.val_of_extends_wf hg hext hsPush, Gates.val_of_extends_wf hg hext hti.1,
      Gates.val_of_extends_wf hg hext hti.2.1, Gates.val_of_extends_wf hg hext hti.2.2]
    rcases hoh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3]
  have hc := fun k (hk : k < 6) => henc.1.getD_cnt hk
  have hr := fun k (hk : k < 10) => henc.1.getD_cell (show 0 < 2 ^ 0 by norm_num) hk
  rw [emitShiftLevel0_eq]
  let cntSpec : List (ℕ × ℕ × ℕ) :=
    [(lw.1.getD 1 0, lw.1.getD 0 0, fls), (lw.1.getD 2 0, lw.1.getD 1 0, lw.1.getD 0 0),
     (lw.1.getD 3 0, lw.1.getD 2 0, lw.1.getD 1 0), (lw.1.getD 4 0, lw.1.getD 3 0, lw.1.getD 2 0),
     (lw.1.getD 5 0, lw.1.getD 4 0, lw.1.getD 3 0), (fls, lw.1.getD 5 0, lw.1.getD 4 0)]
  let rowSpec : List (ℕ × ℕ × ℕ) :=
    [((lw.2.getD 0 []).getD 2 0, (lw.2.getD 0 []).getD 0 0, w0),
     ((lw.2.getD 0 []).getD 3 0, (lw.2.getD 0 []).getD 1 0, w1),
     ((lw.2.getD 0 []).getD 4 0, (lw.2.getD 0 []).getD 2 0, (lw.2.getD 0 []).getD 0 0),
     ((lw.2.getD 0 []).getD 5 0, (lw.2.getD 0 []).getD 3 0, (lw.2.getD 0 []).getD 1 0),
     ((lw.2.getD 0 []).getD 6 0, (lw.2.getD 0 []).getD 4 0, (lw.2.getD 0 []).getD 2 0),
     ((lw.2.getD 0 []).getD 7 0, (lw.2.getD 0 []).getD 5 0, (lw.2.getD 0 []).getD 3 0),
     ((lw.2.getD 0 []).getD 8 0, (lw.2.getD 0 []).getD 6 0, (lw.2.getD 0 []).getD 4 0),
     ((lw.2.getD 0 []).getD 9 0, (lw.2.getD 0 []).getD 7 0, (lw.2.getD 0 []).getD 5 0),
     ((lw.2.getD 0 []).getD 8 0, (lw.2.getD 0 []).getD 8 0, (lw.2.getD 0 []).getD 6 0),
     ((lw.2.getD 0 []).getD 9 0, (lw.2.getD 0 []).getD 9 0, (lw.2.getD 0 []).getD 7 0)]
  have hm1 := hstep hg (Gates.extends_refl g) cntSpec (by
    intro t ht; simp only [cntSpec, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by first | exact hfls | exact hc _ (by omega),
             hc _ (by omega),
             by first | exact hfls | exact hc _ (by omega)⟩)
  have hm2 := hstep hm1.1 hm1.2.1 rowSpec (by
    intro t ht; simp only [rowSpec, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hr _ (by omega), hr _ (by omega),
             by first | exact hw0 | exact hw1 | exact hr _ (by omega)⟩)
  set r1 := emitMap g (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) cntSpec
  set r2 := emitMap r1.1 (fun g₀ t => Gates.gMux3 g₀ sPop t.1 sKeep t.2.1 sPush t.2.2) rowSpec
  have hge12 : r1.1.2 ≤ r2.1.2 := by
    rcases hm2.2.1 with ⟨rr, hrr⟩; rw [hm1.1.2, hm2.1.2, hrr, List.length_append]; omega
  have hlen1 := hm1.2.2.2.1; have hlen2 := hm2.2.2.2.1
  dsimp only [cntSpec, rowSpec, List.length_cons, List.length_nil] at hlen1 hlen2
  refine ⟨hm2.1, Gates.extends_trans hm1.2.1 hm2.2.1,
    by change r2.1.1.length = g.1.length + 80; omega,
    ⟨⟨hm1.2.2.1, fun w hw => lt_of_lt_of_le (hm1.2.2.2.2.1 w hw) hge12,
      by simp, fun row hrow => by
        simp only [List.mem_singleton] at hrow; subst hrow; exact ⟨hm2.2.2.1, hm2.2.2.2.2.1⟩⟩,
     fun k => ?_, fun j s => ?_⟩⟩
  · have hvk := hm1.2.2.2.2.2 k.val (by simp [cntSpec])
    rw [Gates.val_of_extends_wf hm1.1 hm2.2.1 (hm1.2.2.2.2.1 _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hm1.2.2.1]; exact k.isLt)]
      exact List.getElem_mem _))]
    rw [hvk]
    rcases lvl with ⟨cnt, slots⟩
    rcases hcnt with ⟨hcnt1, hcnt2⟩
    have hc0 := henc.2.1 ⟨0, by decide⟩; have hc1 := henc.2.1 ⟨1, by decide⟩
    have hc2 := henc.2.1 ⟨2, by decide⟩; have hc3 := henc.2.1 ⟨3, by decide⟩
    have hc4 := henc.2.1 ⟨4, by decide⟩; have hc5 := henc.2.1 ⟨5, by decide⟩
    dsimp only at hcnt1 hcnt2 hc0 hc1 hc2 hc3 hc4 hc5
    rcases hoh with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;>
      (fin_cases k <;> dsimp only [cntSpec] <;>
       simp only [List.getElem_cons_zero, List.getElem_cons_succ, BlockLevel.pop0_eq,
         BlockLevel.push0_eq, hflsV, hc0, hc1, hc2, hc3, hc4, hc5] <;>
       interval_cases cnt <;> rfl)
  · have hj0 : j = ⟨0, by norm_num⟩ := Fin.ext (by have := j.isLt; simp at this; omega)
    subst hj0
    dsimp only
    have hv0 := hm2.2.2.2.2.2 (2 * s.val) (by simp [rowSpec]; omega)
    have hv1 := hm2.2.2.2.2.2 (2 * s.val + 1) (by simp [rowSpec]; omega)
    simp only [List.getD_cons_zero]; rw [hv0, hv1]
    have h0 := henc.2.2 ⟨0, by norm_num⟩ ⟨0, by decide⟩
    have h1' := henc.2.2 ⟨0, by norm_num⟩ ⟨1, by decide⟩
    have h2' := henc.2.2 ⟨0, by norm_num⟩ ⟨2, by decide⟩
    have h3' := henc.2.2 ⟨0, by norm_num⟩ ⟨3, by decide⟩
    have h4' := henc.2.2 ⟨0, by norm_num⟩ ⟨4, by decide⟩
    dsimp only at h0 h1' h2' h3' h4'
    rcases hoh with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;>
      (fin_cases s <;>
       dsimp only [rowSpec, BlockLevel.pop0_eq, BlockLevel.push0_eq, List.getElem_cons_zero,
         List.getElem_cons_succ] <;>
       first | exact h0 | exact h1' | exact h2' | exact h3' | exact h4' | rfl)


theorem emitTapeStep0_spec {x : List Bool} {g : Gates} {fls mNeg mZero mPos w0 w1 L : ℕ}
    {tw : TapeW} {bt : BlockTape L} (hL : 0 < L)
    (hg : g.WF x.length) (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (hmNeg : mNeg < g.2) (hmZero : mZero < g.2) (hmPos : mPos < g.2)
    (hw0 : w0 < g.2) (hw1 : w1 < g.2) (henc : tw.Encodes g x bt)
    (hL0 : 1 ≤ (bt.left ⟨0, hL⟩).cnt ∧ (bt.left ⟨0, hL⟩).cnt ≤ 4)
    (hR0 : 1 ≤ (bt.right ⟨0, hL⟩).cnt ∧ (bt.right ⟨0, hL⟩).cnt ≤ 4)
    (hoh : (g.val x mNeg = true ∧ g.val x mZero = false ∧ g.val x mPos = false) ∨
           (g.val x mNeg = false ∧ g.val x mZero = true ∧ g.val x mPos = false) ∨
           (g.val x mNeg = false ∧ g.val x mZero = false ∧ g.val x mPos = true)) :
    let res := emitTapeStep0 g fls mNeg mZero mPos w0 w1 tw
    let m : SignType := if g.val x mNeg then .neg else if g.val x mZero then .zero else .pos
    let w : BlockCell := (g.val x w0, g.val x w1)
    let bt' : BlockTape L :=
      match m with
      | .zero => { head := w, left := bt.left, right := bt.right }
      | .pos =>
        let p := bt.right.pop0 hL
        { head := p.1, left := bt.left.push0 hL w, right := p.2 }
      | .neg =>
        let p := bt.left.pop0 hL
        { head := p.1, left := p.2, right := bt.right.push0 hL w }
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧ res.1.1.length = g.1.length + 170 ∧
    res.2.Encodes res.1 x bt' := by
  dsimp only [emitTapeStep0_eq]
  have hle_wf : ∀ {ga gb : Gates}, ga.WF x.length → gb.WF x.length → Gates.Extends ga gb →
      ga.2 ≤ gb.2 := fun hw1 hw2 ⟨rr, hrr⟩ => by rw [hw1.2, hw2.2, hrr, List.length_append]; omega
  have hl0 := henc.2.2.2.1.2 ⟨0, hL⟩
  have hr0 := henc.2.2.2.2.2 ⟨0, hL⟩
  have hlh0 := hl0.1.getD_cell (show 0 < 2 ^ 0 by norm_num) (show 0 < 10 by omega)
  have hlh1 := hl0.1.getD_cell (show 0 < 2 ^ 0 by norm_num) (show 1 < 10 by omega)
  have hrh0 := hr0.1.getD_cell (show 0 < 2 ^ 0 by norm_num) (show 0 < 10 by omega)
  have hrh1 := hr0.1.getD_cell (show 0 < 2 ^ 0 by norm_num) (show 1 < 10 by omega)
  set rM1 := Gates.gMux3 g mNeg (((tw.2.1.getD 0 ([], [])).2.getD 0 []).getD 0 0) mZero w0 mPos
    (((tw.2.2.getD 0 ([], [])).2.getD 0 []).getD 0 0)
  have hm1 := Gates.gMux3_spec hg hmNeg hlh0 hmZero hw0 hmPos hrh0
  have hm1_wf : rM1.1.WF x.length := hm1.1
  have hm1_ext : Gates.Extends g rM1.1 := hm1.2.1
  have hle1 : g.2 ≤ rM1.1.2 := hle_wf hg hm1_wf hm1_ext
  set rM2 := Gates.gMux3 rM1.1 mNeg (((tw.2.1.getD 0 ([], [])).2.getD 0 []).getD 1 0) mZero w1 mPos
    (((tw.2.2.getD 0 ([], [])).2.getD 0 []).getD 1 0)
  have hm2 := Gates.gMux3_spec hm1_wf (lt_of_lt_of_le hmNeg hle1) (lt_of_lt_of_le hlh1 hle1)
    (lt_of_lt_of_le hmZero hle1) (lt_of_lt_of_le hw1 hle1)
    (lt_of_lt_of_le hmPos hle1) (lt_of_lt_of_le hrh1 hle1)
  have hm2_wf : rM2.1.WF x.length := hm2.1
  have hm2_ext : Gates.Extends rM1.1 rM2.1 := hm2.2.1
  have hle2 : rM1.1.2 ≤ rM2.1.2 := hle_wf hm1_wf hm2_wf hm2_ext
  have he12 : Gates.Extends g rM2.1 := Gates.extends_trans hm1_ext hm2_ext
  have hle02 : g.2 ≤ rM2.1.2 := hle1.trans hle2
  set rShL := emitShiftLevel0 rM2.1 fls mNeg mZero mPos w0 w1 (tw.2.1.getD 0 ([], []))
  have hshL := emitShiftLevel0_spec hm2_wf (lt_of_lt_of_le hfls hle02)
    (by rw [Gates.val_of_extends_wf hg he12 hfls, hflsV])
    (lt_of_lt_of_le hmNeg hle02) (lt_of_lt_of_le hmZero hle02) (lt_of_lt_of_le hmPos hle02)
    (lt_of_lt_of_le hw0 hle02) (lt_of_lt_of_le hw1 hle02)
    (hl0.of_extends hg he12 hle02) hL0
    (by rw [Gates.val_of_extends_wf hg he12 hmNeg, Gates.val_of_extends_wf hg he12 hmZero,
          Gates.val_of_extends_wf hg he12 hmPos]; exact hoh)
  have hshL_wf : rShL.1.WF x.length := hshL.1
  have hshL_ext : Gates.Extends rM2.1 rShL.1 := hshL.2.1
  have hle3 : rM2.1.2 ≤ rShL.1.2 := hle_wf hm2_wf hshL_wf hshL_ext
  have he13 : Gates.Extends g rShL.1 := Gates.extends_trans he12 hshL_ext
  have hle03 : g.2 ≤ rShL.1.2 := hle02.trans hle3
  have hohR : (g.val x mPos = true ∧ g.val x mZero = false ∧ g.val x mNeg = false) ∨
      (g.val x mPos = false ∧ g.val x mZero = true ∧ g.val x mNeg = false) ∨
      (g.val x mPos = false ∧ g.val x mZero = false ∧ g.val x mNeg = true) := by
    rcases hoh with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inr (Or.inr ⟨c, b, a⟩)
    · exact Or.inr (Or.inl ⟨c, b, a⟩)
    · exact Or.inl ⟨c, b, a⟩
  set rShR := emitShiftLevel0 rShL.1 fls mPos mZero mNeg w0 w1 (tw.2.2.getD 0 ([], []))
  have hshR := emitShiftLevel0_spec hshL_wf (lt_of_lt_of_le hfls hle03)
    (by rw [Gates.val_of_extends_wf hg he13 hfls, hflsV])
    (lt_of_lt_of_le hmPos hle03) (lt_of_lt_of_le hmZero hle03) (lt_of_lt_of_le hmNeg hle03)
    (lt_of_lt_of_le hw0 hle03) (lt_of_lt_of_le hw1 hle03)
    (hr0.of_extends hg he13 hle03) hR0
    (by rw [Gates.val_of_extends_wf hg he13 hmPos, Gates.val_of_extends_wf hg he13 hmZero,
          Gates.val_of_extends_wf hg he13 hmNeg]; exact hohR)
  have hshR_wf : rShR.1.WF x.length := hshR.1
  have hshR_ext : Gates.Extends rShL.1 rShR.1 := hshR.2.1
  have hle4 : rShL.1.2 ≤ rShR.1.2 := hle_wf hshL_wf hshR_wf hshR_ext
  have he34 : Gates.Extends rM2.1 rShR.1 := Gates.extends_trans hshL_ext hshR_ext
  have he24 : Gates.Extends rM1.1 rShR.1 := Gates.extends_trans hm2_ext he34
  have he14 : Gates.Extends g rShR.1 := Gates.extends_trans hm1_ext he24
  have hle24 : rM2.1.2 ≤ rShR.1.2 := hle3.trans hle4
  have hle14 : rM1.1.2 ≤ rShR.1.2 := hle2.trans hle24
  have hle04 : g.2 ≤ rShR.1.2 := hle1.trans hle14
  have hm1_lt : rM1.2 < rM1.1.2 := hm1.2.2.1
  have hm2_lt : rM2.2 < rM2.1.2 := hm2.2.2.1
  refine ⟨hshR_wf, he14,
    by rw [hshR.2.2.1, hshL.2.2.1, hm2.2.2.2.1, hm1.2.2.2.1],
    lt_of_lt_of_le hm1_lt hle14, lt_of_lt_of_le hm2_lt hle24, ?_, ?_, ?_⟩
  · rw [Gates.val_of_extends_wf hm1_wf he24 hm1_lt,
      Gates.val_of_extends_wf hm2_wf he34 hm2_lt,
      hm1.2.2.2.2, hm2.2.2.2.2,
      Gates.val_of_extends_wf hg hm1_ext hmNeg, Gates.val_of_extends_wf hg hm1_ext hmZero,
      Gates.val_of_extends_wf hg hm1_ext hmPos, Gates.val_of_extends_wf hg hm1_ext hlh1,
      Gates.val_of_extends_wf hg hm1_ext hw1, Gates.val_of_extends_wf hg hm1_ext hrh1]
    have hLhd := hl0.2.2 ⟨0, by norm_num⟩ ⟨0, by decide⟩
    have hRhd := hr0.2.2 ⟨0, by norm_num⟩ ⟨0, by decide⟩
    dsimp only at hLhd hRhd
    rcases hoh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · simp only [h1, h2, h3, Bool.true_and, Bool.false_and, Bool.or_false,
        BlockHalfTape.pop0_eq, BlockLevel.pop0_eq]
      exact hLhd
    · simp [h1, h2, h3]
    · simp only [h1, h2, h3, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte, BlockHalfTape.pop0_eq, BlockLevel.pop0_eq]
      exact hRhd
  · refine ⟨by have := henc.2.2.2.1.1; simp; omega, fun i => ?_⟩
    by_cases hi : i.val = 0
    · have hi0 : i = ⟨0, hL⟩ := Fin.ext hi
      subst hi0
      rw [List.getD_cons_zero]
      have hEncL : LevelW.Encodes rShR.1 x rShL.2 _ := hshL.2.2.2.of_extends hshL_wf hshR_ext hle4
      rw [Gates.val_of_extends_wf hg he12 hmNeg, Gates.val_of_extends_wf hg he12 hmZero,
        Gates.val_of_extends_wf hg he12 hw0, Gates.val_of_extends_wf hg he12 hw1] at hEncL
      rcases hoh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
        simpa [h1, h2, h3, BlockHalfTape.pop0_eq, BlockHalfTape.push0_eq] using hEncL
    · have hgt' : ((rShL.2 :: tw.2.1.drop 1).getD i.val ([], [])) = tw.2.1.getD i.val ([], []) := by
        cases h : i.val with
        | zero => omega
        | succ k =>
          rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_drop,
            ← List.getD_eq_getElem?_getD, Nat.add_comm]
      rw [hgt']
      have hE := (henc.2.2.2.1.2 i).of_extends hg he14 hle04
      rcases hoh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
        simpa [h1, h2, h3, BlockHalfTape.pop0_eq, BlockHalfTape.push0_eq, hi] using hE
  · refine ⟨by have := henc.2.2.2.2.1; simp; omega, fun i => ?_⟩
    by_cases hi : i.val = 0
    · have hi0 : i = ⟨0, hL⟩ := Fin.ext hi
      subst hi0
      rw [List.getD_cons_zero]
      have hEncR : LevelW.Encodes rShR.1 x rShR.2 _ := hshR.2.2.2
      rw [Gates.val_of_extends_wf hg he13 hmPos, Gates.val_of_extends_wf hg he13 hmZero,
        Gates.val_of_extends_wf hg he13 hw0, Gates.val_of_extends_wf hg he13 hw1] at hEncR
      rcases hoh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
        simpa [h1, h2, h3, BlockHalfTape.pop0_eq, BlockHalfTape.push0_eq] using hEncR
    · have hgt' : ((rShR.2 :: tw.2.2.drop 1).getD i.val ([], [])) = tw.2.2.getD i.val ([], []) := by
        cases h : i.val with
        | zero => omega
        | succ k =>
          rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_drop,
            ← List.getD_eq_getElem?_getD, Nat.add_comm]
      rw [hgt']
      have hE := (henc.2.2.2.2.2 i).of_extends hg he14 hle04
      rcases hoh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
        simpa [h1, h2, h3, BlockHalfTape.pop0_eq, BlockHalfTape.push0_eq, hi] using hE

theorem emitRebalanceHalfTape_spec {x : List Bool} {g : Gates} {fls L lvl : ℕ}
    {hw : HalfW} {ht : BlockHalfTape L} (hlvl : lvl + 1 < L)
    (hg : g.WF x.length) (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (henc : hw.Encodes g x ht)
    (hcL : (ht ⟨lvl, Nat.lt_of_succ_lt hlvl⟩).cnt ≤ 5)
    (hcH1 : 1 ≤ (ht ⟨lvl + 1, hlvl⟩).cnt) (hcH2 : (ht ⟨lvl + 1, hlvl⟩).cnt ≤ 4) :
    let res := emitRebalanceHalfTape g fls hw lvl
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧
    res.1.1.length = g.1.length + 37 + 210 * 2 ^ lvl ∧
    res.2.Encodes res.1 x (ht.rebalanceAt lvl hlvl) := by
  dsimp only [emitRebalanceHalfTape_eq]
  have hrb := emitRebalanceLevel_spec hg hfls hflsV (henc.2 ⟨lvl, Nat.lt_of_succ_lt hlvl⟩)
    (henc.2 ⟨lvl + 1, hlvl⟩) hcL hcH1 hcH2
  have hle : g.2 ≤ (emitRebalanceLevel g fls (hw.getD lvl ([], []))
      (hw.getD (lvl + 1) ([], []))).1.2 := by
    rcases hrb.2.1 with ⟨rr, hrr⟩; rw [hg.2, hrb.1.2, hrr, List.length_append]; omega
  refine ⟨hrb.1, hrb.2.1, hrb.2.2.1, ?_, fun i => ?_⟩
  · have hlen := henc.1
    simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
      List.length_nil]
    omega
  · have hget := getD_take_append hw
      [(emitRebalanceLevel g fls (hw.getD lvl ([], [])) (hw.getD (lvl + 1) ([], []))).2.1,
       (emitRebalanceLevel g fls (hw.getD lvl ([], [])) (hw.getD (lvl + 1) ([], []))).2.2]
      lvl i.val ([], []) (by rw [henc.1]; simp; omega)
    have hmid :
        [(emitRebalanceLevel g fls (hw.getD lvl ([], [])) (hw.getD (lvl + 1) ([], []))).2.1,
         (emitRebalanceLevel g fls (hw.getD lvl ([], [])) (hw.getD (lvl +
           1) ([], []))).2.2].length = 2 := rfl
    rw [hmid] at hget
    rw [hget]
    dsimp only [BlockHalfTape.rebalanceAt_eq]
    by_cases h1 : i.val = lvl
    · have hi : i = ⟨lvl, Nat.lt_of_succ_lt hlvl⟩ := Fin.ext h1
      subst hi
      have hnot : ¬ (lvl < lvl) := Nat.lt_irrefl lvl
      have hlt2 : lvl < lvl + 2 := by omega
      simp only [hnot, ↓reduceIte, hlt2, Nat.sub_self, List.getD_cons_zero, ↓reduceDIte]
      exact hrb.2.2.2.1
    · by_cases h2 : i.val = lvl + 1
      · have hi : i = ⟨lvl + 1, hlvl⟩ := Fin.ext h2
        subst hi
        have hnot : ¬ (lvl + 1 < lvl) := by omega
        have hlt2 : lvl + 1 < lvl + 2 := by omega
        have hsub : lvl + 1 - lvl = 1 := by omega
        simp only [hnot, ↓reduceIte, hlt2, h1, hsub, List.getD_cons_succ, List.getD_cons_zero,
          ↓reduceDIte]
        exact hrb.2.2.2.2
      · by_cases hlt : i.val < lvl
        · simp only [hlt, ↓reduceIte, h1, h2, ↓reduceDIte]
          exact (henc.2 i).of_extends hg hrb.2.1 hle
        · have hnot2 : ¬ (i.val < lvl + 2) := by omega
          simp only [hlt, ↓reduceIte, hnot2, h1, h2, ↓reduceDIte]
          exact (henc.2 i).of_extends hg hrb.2.1 hle

/-- Oblivious scheduled rebalance pass for one half-tape at step `t → t + 1`:
folds `emitRebalanceHalfTape` over `lvl ∈ List.range (L - 1)`, triggering iff
`(t + 1) % 2 ^ (lvl + 1) = 0`. -/
@[expose] def emitSchedulePass (L fls t : ℕ) (g : Gates) (hw : HalfW) : Gates × HalfW :=
  (List.range (L - 1)).foldl (fun acc lvl =>
    if (t + 1) % 2 ^ (lvl + 1) = 0 then
      emitRebalanceHalfTape acc.1 fls acc.2 lvl
    else acc) (g, hw)

/-- Gate-count overhead of one scheduled rebalance pass on a single half-tape at step `t`. -/
@[expose] def schedulePassCost (L t : ℕ) : ℕ :=
  ((List.range (L - 1)).map fun lvl =>
    if (t + 1) % 2 ^ (lvl + 1) = 0 then 37 + 210 * 2 ^ lvl else 0).sum

theorem emitSchedulePass_spec {x : List Bool} {g : Gates} {fls L t : ℕ}
    {hw : HalfW} {ht : BlockHalfTape L} (hL : 0 < L)
    (hg : g.WF x.length) (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (henc : hw.Encodes g x ht)
    (hstep0 :
      (if (t + 1) % 2 = 0 then (ht ⟨0, hL⟩).cnt ≤ 5
       else 1 ≤ (ht ⟨0, hL⟩).cnt ∧ (ht ⟨0, hL⟩).cnt ≤ 4) ∧
      ∀ i : Fin L, i.val ≠ 0 →
        if t % 2 ^ (i.val + 1) < 2 ^ i.val then 2 ≤ (ht i).cnt ∧ (ht i).cnt ≤ 3
        else 1 ≤ (ht i).cnt ∧ (ht i).cnt ≤ 4) :
    let res := emitSchedulePass L fls t g hw
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧
    res.1.1.length = g.1.length + schedulePassCost L t ∧
    res.2.Encodes res.1 x (ht.rebalanceSchedule t) := by
  have haux : ∀ (m : ℕ) (hm : m ≤ L - 1),
      let res := (List.range m).foldl (fun acc lvl =>
        if (t + 1) % 2 ^ (lvl + 1) = 0 then emitRebalanceHalfTape acc.1 fls acc.2 lvl
        else acc) (g, hw)
      let cost := ((List.range m).map fun lvl =>
        if (t + 1) % 2 ^ (lvl + 1) = 0 then 37 + 210 * 2 ^ lvl else 0).sum
      res.1.WF x.length ∧ Gates.Extends g res.1 ∧ res.1.1.length = g.1.length + cost ∧
      res.2.Encodes res.1 x (BlockHalfTape.rebalanceScheduleAux t m hm ht) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨hg, Gates.extends_refl g, by simp, henc⟩
    | succ m ih =>
      intro hm
      obtain ⟨hW, hE, hG, hEnc⟩ := ih (Nat.le_of_succ_le hm)
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      dsimp
      by_cases hdiv : (t + 1) % 2 ^ (m + 1) = 0
      · simp only [hdiv, ↓reduceIte]
        set prev := (List.range m).foldl (fun acc lvl =>
          if (t + 1) % 2 ^ (lvl + 1) = 0 then emitRebalanceHalfTape acc.1 fls acc.2 lvl
          else acc) (g, hw)
        have hle_g : g.2 ≤ prev.1.2 := by
          rcases hE with ⟨rr, hrr⟩; rw [hg.2, hW.2, hrr, List.length_append]; omega
        have hbd := BlockHalfTape.rebalanceScheduleAux_cnt_bounds hL hstep0 (by omega : m +
          1 < L) hdiv
        have hrb := emitRebalanceHalfTape_spec (by omega : m + 1 < L) hW
          (lt_of_lt_of_le hfls hle_g) (by rw [Gates.val_of_extends_wf hg hE hfls, hflsV])
          hEnc hbd.1 hbd.2.1 hbd.2.2
        exact ⟨hrb.1, Gates.extends_trans hE hrb.2.1, by omega, hrb.2.2.2⟩
      · simp only [hdiv, ↓reduceIte]
        exact ⟨hW, hE, by omega, hEnc⟩
  exact haux (L - 1) le_rfl

/-! ### Initial wire layout `initStateW` and `StateW.Encodes` -/

/-- Wire encoding invariant for a full `ObliviousCfg k L State`. -/
@[expose] def StateW.Encodes {k L numStates : ℕ} {State : Type} (e : State ≃ Fin numStates)
    (g : Gates) (x : List Bool) (sw : StateW) (oc : ObliviousCfg k L State) : Prop :=
  sw.1.1.length = numStates + 1 ∧ (∀ w ∈ sw.1.1, w < g.2) ∧
  g.val x (sw.1.1.getD 0 0) = decide (oc.state = none) ∧
  (∀ q : Fin numStates,
    g.val x (sw.1.1.getD (q.val + 1) 0) = decide (oc.state.map e = some q)) ∧
  sw.1.2.length = 4 ∧ (∀ w ∈ sw.1.2, w < g.2) ∧
  (∀ o : Fin 4, g.val x (sw.1.2.getD o.val 0) = decide (outViewIdx oc.outView = o)) ∧
  sw.2.1.Encodes g x oc.inputTape ∧
  sw.2.2.length = k ∧ ∀ r : Fin k, (sw.2.2.getD r.val defaultTapeW).Encodes g x (oc.workTapes r)

/-- Constant `L`-level half-tape wire layout filled with `(w0, w1)`. -/
@[expose] def initHalfConstW (L fls tru w0 w1 : ℕ) : HalfW :=
  (List.range L).map fun i =>
    ([fls, fls, tru, fls, fls, fls], List.replicate (2 ^ i) [w0, w1, w0, w1, w0, w1, w0, w1, w0,
      w1])

/-- Half-tape wire layout populated from `cells : List (ℕ × ℕ)` with fallback `(def0, def1)`. -/
@[expose] def initHalfFromW (L fls tru : ℕ) (cells : List (ℕ × ℕ)) (def0 def1 : ℕ) : HalfW :=
  (List.range L).map fun i =>
    let B := 2 ^ i
    let off := 2 * (B - 1)
    ([fls, fls, tru, fls, fls, fls],
      (List.range B).map fun j =>
        let c0 := cells.getD (off + j) (def0, def1)
        let c1 := cells.getD (off + B + j) (def0, def1)
        let c2 := cells.getD (off + 2 * B + j) (def0, def1)
        let c3 := cells.getD (off + 3 * B + j) (def0, def1)
        let c4 := cells.getD (off + 4 * B + j) (def0, def1)
        [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2])

/-- Initial `StateW` for an `ObliviousCfg` with arbitrary `inputWires`. -/
@[expose] def initStateW (L k numStates q0Idx fls tru : ℕ) (inputWires : List ℕ) : StateW :=
  let inHead := match inputWires with | [] => (fls, tru) | w :: _ => (tru, w)
  let inRightCells := (inputWires.drop 1).map fun w => (tru, w)
  let stateW := (List.range (numStates + 1)).map fun s => if s = q0Idx + 1 then tru else fls
  let outW := [tru, fls, fls, fls]
  let inTape : TapeW :=
    (inHead, (initHalfConstW L fls tru fls fls, initHalfFromW L fls tru inRightCells fls tru))
  let wkTape : TapeW :=
    ((fls, fls), (initHalfConstW L fls tru fls fls, initHalfConstW L fls tru fls fls))
  ((stateW, outW), (inTape, List.replicate k wkTape))

theorem initHalfConstW_encodes {x : List Bool} {g : Gates} {L fls tru w0 w1 : ℕ}
    (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (htru : tru < g.2) (htruV : g.val x tru = true)
    (hw0 : w0 < g.2) (hw1 : w1 < g.2) :
    (initHalfConstW L fls tru w0 w1).Encodes g x (BlockHalfTape.initConst L (g.val x w0,
      g.val x w1)) := by
  refine ⟨by simp [initHalfConstW], fun i => ?_⟩
  simp only [initHalfConstW, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.isLt, Option.map_some, Option.getD_some]
  refine ⟨⟨by simp, fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption,
    by simp, fun row hr => ?_⟩, fun c => ?_, fun j s => ?_⟩
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hr
    refine ⟨by simp, fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption⟩
  · fin_cases c <;> simp [BlockHalfTape.initConst_eq, BlockLevel.initConst_eq, hflsV, htruV]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, j.isLt, ↓reduceIte,
      Option.getD_some, BlockHalfTape.initConst_eq, BlockLevel.initConst_eq]
    fin_cases s <;> rfl

theorem initHalfFromW_encodes {x : List Bool} {g : Gates} {L fls tru def0 def1 : ℕ}
    {cells : List (ℕ × ℕ)}
    (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (htru : tru < g.2) (htruV : g.val x tru = true)
    (hd0 : def0 < g.2) (hd1 : def1 < g.2)
    (hcells : ∀ c ∈ cells, c.1 < g.2 ∧ c.2 < g.2) :
    (initHalfFromW L fls tru cells def0 def1).Encodes g x
      (BlockHalfTape.initFrom L fun j =>
        let c := cells.getD j (def0, def1)
        (g.val x c.1, g.val x c.2)) := by
  have hc_lt : ∀ k, (cells.getD k (def0, def1)).1 < g.2 ∧ (cells.getD k (def0, def1)).2 < g.2 := by
    intro k
    by_cases hk : k < cells.length
    · exact hcells _ (getD_mem_of_lt hk)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      exact ⟨hd0, hd1⟩
  refine ⟨by simp [initHalfFromW], fun i => ?_⟩
  simp only [initHalfFromW, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.isLt, Option.map_some, Option.getD_some]
  refine ⟨⟨by simp, fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption,
    by simp, fun row hr => ?_⟩, fun c => ?_, fun j s => ?_⟩
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    refine ⟨by simp, fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hc_lt _).1
      · exact (hc_lt _).2
      · exact (hc_lt _).1
      · exact (hc_lt _).2
      · exact (hc_lt _).1
      · exact (hc_lt _).2
      · exact (hc_lt _).1
      · exact (hc_lt _).2
      · exact (hc_lt _).1
      · exact (hc_lt _).2⟩
  · fin_cases c <;> simp [BlockHalfTape.initFrom_eq, hflsV, htruV]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt,
      Option.map_some, Option.getD_some, BlockHalfTape.initFrom_eq]
    fin_cases s <;> simp [Nat.add_assoc]

theorem initStateW_spec {k L numStates : ℕ} {State : Type} (e : State ≃ Fin numStates)
    (tm : MultiTapeTM k Bool State) {x : List Bool} {g : Gates} {fls tru : ℕ}
    {inputWires : List ℕ}
    (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (htru : tru < g.2) (htruV : g.val x tru = true)
    (hin : ∀ w ∈ inputWires, w < g.2) :
    let input := inputWires.map (g.val x)
    StateW.Encodes e g x (initStateW L k numStates (e tm.q₀).val fls tru inputWires)
      (ObliviousCfg.init L tm input) := by
  dsimp only [initStateW, StateW.Encodes, ObliviousCfg.init_eq]
  refine ⟨by simp, fun w hw => ?_, ?_, fun q => ?_, by simp, fun w hw => ?_, fun o => ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩, by simp, fun r => ?_⟩
  · obtain ⟨s, _, rfl⟩ := List.mem_map.mp hw; split_ifs <;> assumption
  · simp [List.getD_eq_getElem?_getD, hflsV]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show q.val + 1 < numStates + 1 by omega), Option.map_some,
      Option.getD_some, Nat.add_right_cancel_iff, Option.map_some, Option.some.injEq]
    by_cases hq : q.val = (e tm.q₀).val
    · have heq : q = e tm.q₀ := Fin.ext hq
      subst heq; simp [htruV]
    · have hne : e tm.q₀ ≠ q := fun h => hq (congrArg Fin.val h).symm
      simp [hq, hflsV, hne]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  · fin_cases o <;> simp [outViewIdx, htruV, hflsV]
  · cases inputWires with
    | nil => exact hfls
    | cons w _ => exact htru
  · cases inputWires with
    | nil => exact htru
    | cons w _ => exact hin w List.mem_cons_self
  · cases inputWires with
    | nil => simp [BlockCell.inputCell_eq, BlockCell.rightEnd_eq, hflsV, htruV]
    | cons w tl => simp [BlockCell.inputCell_eq, htruV]
  · simpa [BlockCell.leftEnd_eq, hflsV] using
      initHalfConstW_encodes (L := L) hfls hflsV htru htruV hfls hfls
  · have hrc : ∀ c ∈ (inputWires.drop 1).map (fun w => (tru, w)), c.1 < g.2 ∧ c.2 < g.2 := by
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      exact ⟨htru, hin w (List.mem_of_mem_drop hw)⟩
    have hfrm := initHalfFromW_encodes (L := L) hfls hflsV htru htruV hfls htru hrc
    have hfun : (fun j => let c := ((inputWires.drop 1).map fun w => (tru, w)).getD j (fls, tru)
        (g.val x c.1, g.val x c.2)) =
        (fun j => BlockCell.inputCell (inputWires.map (g.val x)) (2 + j : ℕ)) := by
      funext j
      have h1 : ¬ ((2 + j : ℕ) : ℤ) ≤ 0 := by omega
      have h2 : ((2 + j : ℕ) : ℤ).toNat - 1 = j + 1 := by omega
      simp only [BlockCell.inputCell_eq, h1, ↓reduceIte, h2, List.length_map,
        BlockCell.rightEnd_eq]
      by_cases hj : j + 1 < inputWires.length
      · have hjd : j < (inputWires.drop 1).length := by simp; omega
        simp only [hj, ↓reduceDIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hjd, Option.map_some, Option.getD_some]
        simp [htruV]
      · simp only [hj, ↓reduceDIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          Option.getD_none]
        simp [hflsV, htruV]
    rwa [hfun] at hfrm
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, r.isLt, ↓reduceIte,
      Option.getD_some]
    refine ⟨hfls, hfls, by simp [hflsV],
      by simpa [hflsV] using initHalfConstW_encodes (L := L) hfls hflsV htru htruV hfls hfls,
      by simpa [hflsV] using initHalfConstW_encodes (L := L) hfls hflsV htru htruV hfls hfls⟩

/-! ### Finite transition table and single oblivious TM step `emitTmStep` -/

/-- Active TM situation: current state, input-head `BlockCell`, and `k` work-head `BlockCell`s. -/
abbrev ActiveSit (k numStates : ℕ) : Type := Fin numStates × BlockCell × (Fin k → BlockCell)

/-- Canonical finite list of all active situations for `k` work tapes and `numStates` states. -/
@[expose] noncomputable def allActiveSits (k numStates : ℕ) : List (ActiveSit k numStates) :=
  (Finset.univ : Finset (ActiveSit k numStates)).toList

/-- Gate-level literal wire for `(b, w, nw)`: `w` if `b = true`, else `nw`. -/
@[expose] def litWire (b : Bool) (w nw : ℕ) : ℕ := if b then w else nw

/-- Emit one indicator wire per active situation in `sits`. -/
@[expose] def emitIndicators {k numStates : ℕ} (g : Gates) (tru : ℕ) (sw : StateW)
    (inNeg0 inNeg1 : ℕ) (wkNeg0 wkNeg1 : List ℕ) (sits : List (ActiveSit k numStates)) :
    Gates × List ℕ :=
  emitMap g (fun gc sit =>
    let qW := sw.1.1.getD (sit.1.val + 1) 0
    let inW0 := litWire sit.2.1.1 sw.2.1.1.1 inNeg0
    let inW1 := litWire sit.2.1.2 sw.2.1.1.2 inNeg1
    let wkWs := (List.finRange k).flatMap fun r =>
      let tw := sw.2.2.getD r.val defaultTapeW
      [litWire (sit.2.2 r).1 tw.1.1 (wkNeg0.getD r.val 0),
       litWire (sit.2.2 r).2 tw.1.2 (wkNeg1.getD r.val 0)]
    Gates.gAndList gc tru (qW :: inW0 :: inW1 :: wkWs)) sits

/-- Variable-cost version of `emitMap_spec` where each element `a` emits `cost a` gates. -/
theorem emitMap_spec_var {α : Type} {x : List Bool} {g : Gates}
    {f : Gates → α → Gates × ℕ} {xs : List α} {cost : α → ℕ} {spec : α → Bool}
    (hg : g.WF x.length)
    (hf : ∀ (g₀ : Gates) (a : α), a ∈ xs → g₀.WF x.length → Gates.Extends g g₀ →
      let r := f g₀ a
      r.1.WF x.length ∧ Gates.Extends g₀ r.1 ∧ r.2 < r.1.2 ∧
        r.1.1.length = g₀.1.length + cost a ∧ r.1.val x r.2 = spec a) :
    let r := emitMap g f xs
    r.1.WF x.length ∧ Gates.Extends g r.1 ∧ r.2.length = xs.length ∧
    r.1.1.length = g.1.length + (xs.map cost).sum ∧
    (∀ w ∈ r.2, w < r.1.2) ∧
    (∀ (i : ℕ) (hi : i < xs.length), r.1.val x (r.2.getD i 0) = spec xs[i]) := by
  suffices h : ∀ (l : List α), (∀ a ∈ l, a ∈ xs) → ∀ (g₀ : Gates),
      g₀.WF x.length → Gates.Extends g g₀ →
      let r := emitMap g₀ f l
      r.1.WF x.length ∧ Gates.Extends g₀ r.1 ∧ r.2.length = l.length ∧
      r.1.1.length = g₀.1.length + (l.map cost).sum ∧
      (∀ w ∈ r.2, w < r.1.2) ∧
      (∀ (i : ℕ) (hi : i < l.length), r.1.val x (r.2.getD i 0) = spec l[i]) by
    exact h xs (fun _ ha => ha) g hg (Gates.extends_refl g)
  intro l
  induction l with
  | nil =>
    intro _ g₀ hg₀ _
    exact ⟨hg₀, Gates.extends_refl g₀, rfl, by simp [emitMap_eq], by simp [emitMap_eq],
      fun _ hi => by simp at hi⟩
  | cons a tl ih =>
    intro hsub g₀ hg₀ hext₀
    have ha : a ∈ xs := hsub a List.mem_cons_self
    have hstep := hf g₀ a ha hg₀ hext₀
    set p := f g₀ a
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      ih (fun b hb => hsub b (List.mem_cons_of_mem a hb)) p.1 hstep.1
        (Gates.extends_trans hext₀ hstep.2.1)
    have hfold : ∀ (l' : List α) (g' : Gates) (acc : List ℕ),
        let res := l'.foldl (fun q b => let q' := f q.1 b; (q'.1, q'.2 :: q.2)) (g', acc)
        let res0 := l'.foldl (fun q b => let q' := f q.1 b; (q'.1, q'.2 :: q.2)) (g', [])
        res.1 = res0.1 ∧ res.2 = res0.2 ++ acc := by
      intro l'
      induction l' with
      | nil => intro g' acc; exact ⟨rfl, by simp⟩
      | cons b tl' ih' =>
        intro g' acc; simp only [List.foldl_cons]
        have ha1 := ih' (f g' b).1 ((f g' b).2 :: acc)
        have ha2 := ih' (f g' b).1 [(f g' b).2]
        exact ⟨ha1.1.trans ha2.1.symm, by rw [ha1.2, ha2.2, List.append_assoc,
          List.singleton_append]⟩
    have hf1 := hfold tl p.1 [p.2]
    have hge : p.1.2 ≤ (emitMap p.1 f tl).1.2 := by
      rcases h2 with ⟨rr, hrr⟩; rw [h1.2, hstep.1.2, hrr, List.length_append]; omega
    have hrev : (emitMap g₀ f (a :: tl)).1 = (emitMap p.1 f tl).1 ∧
        (emitMap g₀ f (a :: tl)).2 = p.2 :: (emitMap p.1 f tl).2 := by
      refine ⟨hf1.1, ?_⟩
      dsimp only [emitMap_eq, List.foldl_cons]; rw [hf1.2]; simp
    dsimp only; rw [hrev.1, hrev.2]
    refine ⟨h1, Gates.extends_trans hstep.2.1 h2, by simp [h3],
      by rw [h4, hstep.2.2.2.1, List.map_cons, List.sum_cons]; omega, ?_, ?_⟩
    · intro w hw; simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le hstep.2.2.1 hge
      · exact h5 w hw
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [Gates.val_of_extends_wf hstep.1 h2 hstep.2.2.1, hstep.2.2.2.2]
      | succ i' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        exact h6 i' (by simp at hi; omega)

/-- Fixed `22`-gate `OutView` update gadget via `emitMap`: given `sHalt`, current 4 one-hot
`outW`, and 3 active output-action wires `(outNone, outF, outT)`, emits the next 4 one-hot
`OutView` wires. -/
@[expose] def emitOutUpdate (g : Gates) (sHalt outNone outF outT : ℕ) (outW : List ℕ) :
    Gates × List ℕ :=
  let o0 := outW.getD 0 0; let o1 := outW.getD 1 0
  let o2 := outW.getD 2 0; let o3 := outW.getD 3 0
  let (g, oFT) := Gates.gOr g outF outT
  let (g, o123) := Gates.gOr3 g o1 o2 o3
  let andPairs : List (ℕ × ℕ) :=
    [(sHalt, o0), (sHalt, o1), (sHalt, o2), (sHalt, o3),
     (outNone, o0), (outNone, o1), (outNone, o2), (outNone, o3),
     (outF, o0), (outT, o0), (oFT, o123)]
  let (g, ps) := emitMap g (fun gc p => Gates.gAnd gc p.1 p.2) andPairs
  let a := fun k => ps.getD k 0
  let orTriples : List (ℕ × ℕ × ℕ) :=
    [(a 0, a 4, a 4), (a 1, a 5, a 8), (a 2, a 6, a 9), (a 3, a 7, a 10)]
  emitMap g (fun gc t => Gates.gOr3 gc t.1 t.2.1 t.2.2) orTriples

theorem emitOutUpdate_spec {x : List Bool} {g : Gates} {sHalt outNone outF outT : ℕ}
    {outW : List ℕ} {ov : OutView} {aout : Option Bool} {halted : Bool}
    (hg : g.WF x.length) (hsHalt : sHalt < g.2) (hN : outNone < g.2) (hF : outF < g.2)
    (hT : outT < g.2) (houtW_len : outW.length = 4) (houtW_lt : ∀ w ∈ outW, w < g.2)
    (houtW_val : ∀ o : Fin 4, g.val x (outW.getD o.val 0) = decide (outViewIdx ov = o))
    (hH_val : g.val x sHalt = halted)
    (hN_val : g.val x outNone = (!halted && decide (aout = none)))
    (hF_val : g.val x outF = (!halted && decide (aout = some false)))
    (hT_val : g.val x outT = (!halted && decide (aout = some true))) :
    let res := emitOutUpdate g sHalt outNone outF outT outW
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧ res.1.1.length = g.1.length + 22 ∧
    res.2.length = 4 ∧ (∀ w ∈ res.2, w < res.1.2) ∧
    (∀ o : Fin 4, res.1.val x (res.2.getD o.val 0) =
      decide (outViewIdx (if halted then ov else ov.push aout) = o)) := by
  dsimp only [emitOutUpdate]
  have hle : ∀ {ga gb : Gates}, ga.WF x.length → gb.WF x.length → Gates.Extends ga gb →
      ga.2 ≤ gb.2 := fun hw1 hw2 ⟨rr, hrr⟩ => by rw [hw1.2, hw2.2, hrr, List.length_append]; omega
  have ho_lt : ∀ k < 4, outW.getD k 0 < g.2 := fun k hk =>
    houtW_lt _ (getD_mem_of_lt (by rw [houtW_len]; exact hk))
  have s1 := Gates.gOr_spec hg hF hT
  set r1 := Gates.gOr g outF outT
  have l1 := hle hg s1.1 s1.2.1
  have s2 := Gates.gOr3_spec s1.1 (lt_of_lt_of_le (ho_lt 1 (by omega)) l1)
    (lt_of_lt_of_le (ho_lt 2 (by omega)) l1) (lt_of_lt_of_le (ho_lt 3 (by omega)) l1)
  set r2 := Gates.gOr3 r1.1 (outW.getD 1 0) (outW.getD 2 0) (outW.getD 3 0)
  have l2 := l1.trans (hle s1.1 s2.1 s2.2.1); have e2 := Gates.extends_trans s1.2.1 s2.2.1
  let andPairs : List (ℕ × ℕ) :=
    [(sHalt, outW.getD 0 0), (sHalt, outW.getD 1 0), (sHalt, outW.getD 2 0), (sHalt, outW.getD 3 0),
     (outNone, outW.getD 0 0), (outNone, outW.getD 1 0), (outNone, outW.getD 2 0), (outNone,
       outW.getD 3 0),
     (outF, outW.getD 0 0), (outT, outW.getD 0 0), (r1.2, r2.2)]
  have hm1 := emitMap_spec (x := x) (K := 1) (xs := andPairs)
    (f := fun gc p => Gates.gAnd gc p.1 p.2)
    (spec := fun p => r2.1.val x p.1 && r2.1.val x p.2) s2.1
    (fun gc p hp hgc hextc => by
      have lc := hle s2.1 hgc hextc
      have hp_lt : p.1 < r2.1.2 ∧ p.2 < r2.1.2 := by
        simp only [andPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨lt_of_lt_of_le hsHalt l2, lt_of_lt_of_le (ho_lt 0 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hsHalt l2, lt_of_lt_of_le (ho_lt 1 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hsHalt l2, lt_of_lt_of_le (ho_lt 2 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hsHalt l2, lt_of_lt_of_le (ho_lt 3 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hN l2, lt_of_lt_of_le (ho_lt 0 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hN l2, lt_of_lt_of_le (ho_lt 1 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hN l2, lt_of_lt_of_le (ho_lt 2 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hN l2, lt_of_lt_of_le (ho_lt 3 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hF l2, lt_of_lt_of_le (ho_lt 0 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le hT l2, lt_of_lt_of_le (ho_lt 0 (by omega)) l2⟩
        · exact ⟨lt_of_lt_of_le s1.2.2.1 (hle s1.1 s2.1 s2.2.1), s2.2.2.1⟩
      have ha := Gates.gAnd_spec hgc (lt_of_lt_of_le hp_lt.1 lc) (lt_of_lt_of_le hp_lt.2 lc)
      exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, by
        rw [ha.2.2.2.2, Gates.val_of_extends_wf s2.1 hextc hp_lt.1,
          Gates.val_of_extends_wf s2.1 hextc hp_lt.2]⟩)
  set ps := (emitMap r2.1 (fun gc p => Gates.gAnd gc p.1 p.2) andPairs).2
  set g1 := (emitMap r2.1 (fun gc p => Gates.gAnd gc p.1 p.2) andPairs).1
  let orTriples : List (ℕ × ℕ × ℕ) :=
    [(ps.getD 0 0, ps.getD 4 0, ps.getD 4 0), (ps.getD 1 0, ps.getD 5 0, ps.getD 8 0),
     (ps.getD 2 0, ps.getD 6 0, ps.getD 9 0), (ps.getD 3 0, ps.getD 7 0, ps.getD 10 0)]
  have hps_lt : ∀ k < 11, ps.getD k 0 < g1.2 := fun k hk =>
    hm1.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hm1.2.2.1]; exact hk))
  have hm2 := emitMap_spec (x := x) (K := 2) (xs := orTriples)
    (f := fun gc t => Gates.gOr3 gc t.1 t.2.1 t.2.2)
    (spec := fun t => g1.val x t.1 || g1.val x t.2.1 || g1.val x t.2.2) hm1.1
    (fun gc t ht hgc hextc => by
      have lc := hle hm1.1 hgc hextc
      have ht_lt : t.1 < g1.2 ∧ t.2.1 < g1.2 ∧ t.2.2 < g1.2 := by
        simp only [orTriples, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact ⟨hps_lt 0 (by decide), hps_lt 4 (by decide), hps_lt 4 (by decide)⟩
        · exact ⟨hps_lt 1 (by decide), hps_lt 5 (by decide), hps_lt 8 (by decide)⟩
        · exact ⟨hps_lt 2 (by decide), hps_lt 6 (by decide), hps_lt 9 (by decide)⟩
        · exact ⟨hps_lt 3 (by decide), hps_lt 7 (by decide), hps_lt 10 (by decide)⟩
      have ho := Gates.gOr3_spec hgc (lt_of_lt_of_le ht_lt.1 lc) (lt_of_lt_of_le ht_lt.2.1 lc)
        (lt_of_lt_of_le ht_lt.2.2 lc)
      exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, by
        rw [ho.2.2.2.2, Gates.val_of_extends_wf hm1.1 hextc ht_lt.1,
          Gates.val_of_extends_wf hm1.1 hextc ht_lt.2.1,
          Gates.val_of_extends_wf hm1.1 hextc ht_lt.2.2]⟩)
  refine ⟨hm2.1, Gates.extends_trans e2 (Gates.extends_trans hm1.2.1 hm2.2.1),
    by have h1 : andPairs.length = 11 := rfl; have h2 : orTriples.length = 4 := rfl
       have hg2l : (emitMap g1 (fun gc t => Gates.gOr3 gc t.1 t.2.1 t.2.2) orTriples).1.1.length =
           g1.1.length + 2 * orTriples.length := hm2.2.2.2.1
       have hg1l : g1.1.length = r2.1.1.length + 1 * andPairs.length := hm1.2.2.2.1
       rw [hg2l, hg1l, s2.2.2.2.1, s1.2.2.2.1, h1, h2],
    hm2.2.2.1, hm2.2.2.2.2.1, fun o => ?_⟩
  rw [hm2.2.2.2.2.2 o.val (by simp [orTriples])]
  have hv : ∀ (k : ℕ) (hk : k < 11),
      g1.val x (ps.getD k 0) = (r2.1.val x andPairs[k].1 && r2.1.val x andPairs[k].2) :=
    fun k hk => hm1.2.2.2.2.2 k hk
  have hv0 : g.val x (outW.getD 0 0) = decide (outViewIdx ov = 0) := houtW_val 0
  have hv1 : g.val x (outW.getD 1 0) = decide (outViewIdx ov = 1) := houtW_val 1
  have hv2 : g.val x (outW.getD 2 0) = decide (outViewIdx ov = 2) := houtW_val 2
  have hv3 : g.val x (outW.getD 3 0) = decide (outViewIdx ov = 3) := houtW_val 3
  have hs1v : r2.1.val x r1.2 = (g.val x outF || g.val x outT) := by
    rw [Gates.val_of_extends_wf s1.1 s2.2.1 s1.2.2.1, s1.2.2.2.2]
  have hs2v : r2.1.val x r2.2 = (g.val x (outW.getD 1 0) || g.val x (outW.getD 2 0) ||
      g.val x (outW.getD 3 0)) := by
    rw [s2.2.2.2.2, Gates.val_of_extends_wf hg s1.2.1 (ho_lt 1 (by omega)),
      Gates.val_of_extends_wf hg s1.2.1 (ho_lt 2 (by omega)),
      Gates.val_of_extends_wf hg s1.2.1 (ho_lt 3 (by omega))]
  have hval_e2 : ∀ w, w < g.2 → r2.1.val x w = g.val x w := fun w hw =>
    Gates.val_of_extends_wf hg e2 hw
  fin_cases o <;> dsimp only [orTriples] <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ,
      hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide),
      hv 4 (by decide), hv 5 (by decide), hv 6 (by decide), hv 7 (by decide),
      hv 8 (by decide), hv 9 (by decide), hv 10 (by decide),
      andPairs, hs1v, hs2v, hval_e2 _ hsHalt, hval_e2 _ hN, hval_e2 _ hF, hval_e2 _ hT,
      hval_e2 _ (ho_lt 0 (by omega)), hval_e2 _ (ho_lt 1 (by omega)),
      hval_e2 _ (ho_lt 2 (by omega)), hval_e2 _ (ho_lt 3 (by omega)),
      hH_val, hN_val, hF_val, hT_val, hv0, hv1, hv2, hv3] <;>
    cases halted <;> cases ov with
    | empty =>
      cases aout with
      | none => rfl
      | some b => cases b <;> rfl
    | one c =>
      cases c <;> cases aout with
      | none => rfl
      | some b => cases b <;> rfl
    | many =>
      cases aout with
      | none => rfl
      | some b => cases b <;> rfl

/-- Select the indicator wires whose situation satisfies `pred`. -/
@[expose] def pickWires {k numStates : ℕ} (sits : List (ActiveSit k numStates))
    (inds : List ℕ) (pred : ActiveSit k numStates → Bool) : List ℕ :=
  ((List.range sits.length).filter fun idx =>
    (sits[idx]?.map fun sit => pred sit).getD false).map
    fun idx => inds.getD idx 0

/-- Emit the move, write, level-0 shift, and scheduled rebalance pass for one work tape `r`. -/
@[expose] noncomputable def emitWorkTapeStep {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls t sHalt : ℕ) (inds : List ℕ) (tw : TapeW) (gc : Gates) (r : Fin k) :
    Gates × TapeW :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  let (gc, mNeg) := Gates.gOrList gc fls
    (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .neg))
  let (gc, mZero) := Gates.gOrList gc sHalt
    (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .zero))
  let (gc, mPos) := Gates.gOrList gc fls
    (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .pos))
  let (gc, hW0) := Gates.gAnd gc sHalt tw.1.1
  let (gc, hW1) := Gates.gAnd gc sHalt tw.1.2
  let wkCell := fun (sit : ActiveSit k numStates) =>
    match ((act sit).workTapes r).1 with
    | none => sit.2.2 r
    | some s => BlockCell.ofOption s
  let (gc, w0) := Gates.gOrList gc hW0 (pickWires sits inds fun sit => (wkCell sit).1)
  let (gc, w1) := Gates.gOrList gc hW1 (pickWires sits inds fun sit => (wkCell sit).2)
  let (gc, tw0) := emitTapeStep0 gc fls mNeg mZero mPos w0 w1 tw
  let (gc, twL) := emitSchedulePass L fls t gc tw0.2.1
  let (gc, twR) := emitSchedulePass L fls t gc tw0.2.2
  (gc, (tw0.1, (twL, twR)))

/-- Constant base gate count emitted by one call to `emitWorkTapeStep` (excluding scheduled
rebalances). -/
@[expose] noncomputable def workTapeStepCost {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) (r : Fin k) : ℕ :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  let pickLen := fun (pred : ActiveSit k numStates → Bool) =>
    ((List.range sits.length).filter fun idx =>
      (sits[idx]?.map fun sit => pred sit).getD false).length
  let wkCell := fun (sit : ActiveSit k numStates) =>
    match ((act sit).workTapes r).1 with
    | none => sit.2.2 r
    | some s => BlockCell.ofOption s
  pickLen (fun sit => decide (((act sit).workTapes r).2 = .neg)) +
  pickLen (fun sit => decide (((act sit).workTapes r).2 = .zero)) +
  pickLen (fun sit => decide (((act sit).workTapes r).2 = .pos)) +
  2 +
  pickLen (fun sit => (wkCell sit).1) +
  pickLen (fun sit => (wkCell sit).2) +
  170

/-- Emit one complete oblivious TM step at time `t → t + 1`:
negates head bits, computes situation indicators, combines transition outputs, shifts all
`1 + k` tapes at level `0`, and runs the scheduled rebalance pass on all `2 + 2 * k`
half-tapes. -/
@[expose] noncomputable def emitTmStep {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls tru t : ℕ) (g : Gates) (sw : StateW) : Gates × StateW :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  let (g, inN0) := Gates.gNot g sw.2.1.1.1
  let (g, inN1) := Gates.gNot g sw.2.1.1.2
  let (g, wkN0) := emitMap g (fun gc r => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.1)
    (List.finRange k)
  let (g, wkN1) := emitMap g (fun gc r => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.2)
    (List.finRange k)
  let (g, inds) := emitIndicators g tru sw inN0 inN1 wkN0 wkN1 sits
  let sHalt := sw.1.1.getD 0 0
  let (g, ns0) := Gates.gOrList g sHalt
    (pickWires sits inds fun sit => decide ((act sit).state = none))
  let (g, nsRest) := emitMap g (fun gc (q' : Fin numStates) =>
    Gates.gOrList gc fls
      (pickWires sits inds fun sit => decide ((act sit).state.map e = some q')))
    (List.finRange numStates)
  let nextStateW := ns0 :: nsRest
  let (g, outNone) := Gates.gOrList g fls
    (pickWires sits inds fun sit => decide ((act sit).output = none))
  let (g, outF) := Gates.gOrList g fls
    (pickWires sits inds fun sit => decide ((act sit).output = some false))
  let (g, outT) := Gates.gOrList g fls
    (pickWires sits inds fun sit => decide ((act sit).output = some true))
  let (g, nextOutW) := emitOutUpdate g sHalt outNone outF outT sw.1.2
  let (g, inNeg) := Gates.gOrList g fls
    (pickWires sits inds fun sit =>
      decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg))
  let (g, inZero) := Gates.gOrList g sHalt
    (pickWires sits inds fun sit =>
      decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero))
  let (g, inPos) := Gates.gOrList g fls
    (pickWires sits inds fun sit =>
      decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos))
  let (g, inTape0) := emitTapeStep0 g fls inNeg inZero inPos sw.2.1.1.1 sw.2.1.1.2 sw.2.1
  let (g, inL) := emitSchedulePass L fls t g inTape0.2.1
  let (g, inR) := emitSchedulePass L fls t g inTape0.2.2
  let nextInTape : TapeW := (inTape0.1, (inL, inR))
  let resWk := (List.finRange k).foldl (fun (acc : Gates × List TapeW) (r : Fin k) =>
    let p := emitWorkTapeStep e tm L fls t sHalt inds
      (sw.2.2.getD r.val defaultTapeW) acc.1 r
    (p.1, p.2 :: acc.2)) (g, [])
  (resWk.1, ((nextStateW, nextOutW), (nextInTape, resWk.2.reverse)))

/-- Constant base gate count emitted by one call to `emitTmStep` (excluding scheduled
rebalances), depending only on `tm` and `e`. -/
@[expose] noncomputable def tmStepBaseCost {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) : ℕ :=
  let sits := allActiveSits k numStates
  let act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  let pickLen := fun (pred : ActiveSit k numStates → Bool) =>
    ((List.range sits.length).filter fun idx =>
      (sits[idx]?.map fun sit => pred sit).getD false).length
  (2 + 2 * k) + (3 + 2 * k) * sits.length +
  pickLen (fun sit => decide ((act sit).state = none)) +
  ((List.finRange numStates).map fun q' =>
    pickLen (fun sit => decide ((act sit).state.map e = some q'))).sum +
  pickLen (fun sit => decide ((act sit).output = none)) +
  pickLen (fun sit => decide ((act sit).output = some false)) +
  pickLen (fun sit => decide ((act sit).output = some true)) + 22 +
  pickLen (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg)) +
  pickLen (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero)) +
  pickLen (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos)) +
  170 + ((List.finRange k).map (workTapeStepCost e tm)).sum

/-- Non-dependent `Option` predicate evaluator so `match` never captures proof hypotheses. -/
@[expose] def optPred {α : Type} (o : Option α) (f : α → Bool) : Bool :=
  match o with
  | none => false
  | some q => f q

/-- Key combinator for `emitTmStep_spec`: `pickWires` evaluates to
`oc_state = some q ∧ pred currentSit`. -/
theorem pick_any_eq {k numStates : ℕ} {State : Type} (e : State ≃ Fin numStates)
    {x : List Bool} {g : Gates} {inds : List ℕ} {oc_state : Option State}
    {c_in : BlockCell} {c_wk : Fin k → BlockCell} (sits : List (ActiveSit k numStates))
    (hsits : ∀ sit : ActiveSit k numStates, sit ∈ sits)
    (hval : ∀ (idx : ℕ) (h : idx < sits.length),
      g.val x (inds.getD idx 0) =
        decide (∃ (q : State), oc_state = some q ∧ sits[idx] = (e q, c_in, c_wk)))
    (pred : ActiveSit k numStates → Bool) :
    (pickWires sits inds pred).any (g.val x) =
      optPred oc_state (fun q => pred (e q, c_in, c_wk)) := by
  dsimp only [pickWires, optPred]
  rw [Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨w, ⟨idx, ⟨hidx, hpred⟩, rfl⟩, hw⟩
    rw [List.getElem?_eq_getElem hidx] at hpred
    rw [hval idx hidx] at hw
    obtain ⟨q, hq, hsit⟩ := decide_eq_true_eq.mp hw
    subst hq; dsimp only; rw [← hsit]; exact hpred
  · intro h
    cases oc_state with
    | none => simp at h
    | some q =>
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp (hsits (e q, c_in, c_wk))
      refine ⟨inds.getD idx 0, ⟨idx, ⟨hidx, ?_⟩, rfl⟩, ?_⟩
      · rw [List.getElem?_eq_getElem hidx, hget]; exact h
      · rw [hval idx hidx]; exact decide_eq_true ⟨q, rfl, hget⟩

theorem emitWorkTapeStep_spec {k L numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    {x : List Bool} {g gI gc : Gates} {fls t sHalt : ℕ} {inds : List ℕ} {tw : TapeW}
    {oc : ObliviousCfg k L State} {r : Fin k} (hL : 0 < L)
    (hg : g.WF x.length) (hgI : gI.WF x.length) (hgc : gc.WF x.length)
    (he0I : Gates.Extends g gI) (heIc : Gates.Extends gI gc)
    (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (hsHalt : sHalt < g.2) (hsHaltV : g.val x sHalt = decide (oc.state = none))
    (hinds_len : inds.length = (allActiveSits k numStates).length)
    (hinds_lt : ∀ w ∈ inds, w < gI.2)
    (hinds_val : ∀ (idx : ℕ) (h : idx < (allActiveSits k numStates).length),
      gI.val x (inds.getD idx 0) =
        decide (∃ q : State, oc.state = some q ∧
          (allActiveSits k numStates)[idx] =
            (e q, oc.inputTape.head, fun r' => (oc.workTapes r').head)))
    (htw : TapeW.Encodes g x tw (oc.workTapes r)) (hinv : (oc.workTapes r).Inv t) :
    let res := emitWorkTapeStep e tm L fls t sHalt inds tw gc r
    res.1.WF x.length ∧ Gates.Extends gc res.1 ∧
    res.1.1.length = gc.1.length + workTapeStepCost e tm r + 2 * schedulePassCost L t ∧
    TapeW.Encodes res.1 x res.2 ((oc.step hL tm t).workTapes r) := by
  have hle_wf : ∀ {ga gb : Gates}, ga.WF x.length → gb.WF x.length → Gates.Extends ga gb →
      ga.2 ≤ gb.2 := fun hw1 hw2 ⟨rr, hrr⟩ => by rw [hw1.2, hw2.2, hrr, List.length_append]; omega
  dsimp only [emitWorkTapeStep, workTapeStepCost]
  set sits := allActiveSits k numStates
  set act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
  have hsits_mem : ∀ sit : ActiveSit k numStates, sit ∈ sits := fun sit =>
    Finset.mem_toList.mpr (Finset.mem_univ sit)
  have hpick : ∀ {ga : Gates} {base : ℕ} (hga : ga.WF x.length) (heIa : Gates.Extends gI ga)
      (hbase : base < ga.2) (pred : ActiveSit k numStates → Bool),
      let res := Gates.gOrList ga base (pickWires sits inds pred)
      res.1.WF x.length ∧ Gates.Extends ga res.1 ∧ res.2 < res.1.2 ∧
      res.1.1.length = ga.1.length + ((List.range sits.length).filter fun idx =>
        (sits[idx]?.map fun sit => pred sit).getD false).length ∧
      res.1.val x res.2 = (ga.val x base ||
        match oc.state with
        | none => false
        | some q => pred (e q, oc.inputTape.head, fun r' => (oc.workTapes r').head)) := by
    intro ga base hga heIa hbase pred
    have hle_a := hle_wf hgI hga heIa
    have hws : ∀ w ∈ pickWires sits inds pred, w < ga.2 := by
      intro w hw; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hw
      have hlt : idx < sits.length := List.mem_range.mp (List.mem_filter.mp hidx).1
      exact lt_of_lt_of_le (hinds_lt _ (getD_mem_of_lt (by rw [hinds_len]; exact hlt))) hle_a
    have hor := Gates.gOrList_spec hga hbase hws
    refine ⟨hor.1, hor.2.1, hor.2.2.1, by rw [hor.2.2.2.1]; simp [pickWires], ?_⟩
    rw [hor.2.2.2.2]; congr 1
    exact pick_any_eq e sits hsits_mem
      (fun idx h => by
        rw [Gates.val_of_extends_wf hgI heIa
          (hinds_lt _ (getD_mem_of_lt (by rw [hinds_len]; exact h)))]
        exact hinds_val idx h) pred
  have he0c := Gates.extends_trans he0I heIc
  have hl0I := hle_wf hg hgI he0I
  have hlIc := hle_wf hgI hgc heIc
  have hl0c := hl0I.trans hlIc
  set r1 := Gates.gOrList gc fls (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 =
    .neg))
  have p1 := hpick hgc heIc (lt_of_lt_of_le hfls hl0c)
    (fun sit => decide (((act sit).workTapes r).2 = .neg))
  have e1 := Gates.extends_trans heIc p1.2.1; have l1 := hle_wf hgI p1.1 e1
  set r2 :=
    Gates.gOrList r1.1 sHalt (pickWires sits inds
      fun sit => decide (((act sit).workTapes r).2 = .zero))
  have p2 := hpick p1.1 e1 (lt_of_lt_of_le hsHalt (hl0I.trans l1))
    (fun sit => decide (((act sit).workTapes r).2 = .zero))
  have e2 := Gates.extends_trans e1 p2.2.1; have l2 := hle_wf hgI p2.1 e2
  set r3 :=
    Gates.gOrList r2.1 fls (pickWires sits inds
      fun sit => decide (((act sit).workTapes r).2 = .pos))
  have p3 := hpick p2.1 e2 (lt_of_lt_of_le hfls (hl0I.trans l2))
    (fun sit => decide (((act sit).workTapes r).2 = .pos))
  have e3 := Gates.extends_trans e2 p3.2.1; have l3 := hle_wf hgI p3.1 e3
  have e03 := Gates.extends_trans he0I e3; have l03 := hl0I.trans l3
  set r4 := Gates.gAnd r3.1 sHalt tw.1.1
  have p4 := Gates.gAnd_spec p3.1 (lt_of_lt_of_le hsHalt l03) (lt_of_lt_of_le htw.1 l03)
  have e4 := Gates.extends_trans e3 p4.2.1; have l4 := hle_wf hgI p4.1 e4
  have e04 := Gates.extends_trans he0I e4; have l04 := hl0I.trans l4
  set r5 := Gates.gAnd r4.1 sHalt tw.1.2
  have p5 := Gates.gAnd_spec p4.1 (lt_of_lt_of_le hsHalt l04) (lt_of_lt_of_le htw.2.1 l04)
  have e5 := Gates.extends_trans e4 p5.2.1; have l5 := hle_wf hgI p5.1 e5
  let wkCell : ActiveSit k numStates → BlockCell := fun sit =>
    match ((act sit).workTapes r).1 with | none => sit.2.2 r | some s => BlockCell.ofOption s
  set r6 := Gates.gOrList r5.1 r4.2 (pickWires sits inds fun sit => (wkCell sit).1)
  have p6 := hpick p5.1 e5 (lt_of_lt_of_le p4.2.2.1 (hle_wf p4.1 p5.1 p5.2.1))
    (fun sit => (wkCell sit).1)
  have e6 := Gates.extends_trans e5 p6.2.1; have l6 := hle_wf hgI p6.1 e6
  set r7 := Gates.gOrList r6.1 r5.2 (pickWires sits inds fun sit => (wkCell sit).2)
  have p7 := hpick p6.1 e6 (lt_of_lt_of_le p5.2.2.1 (hle_wf p5.1 p6.1 p6.2.1))
    (fun sit => (wkCell sit).2)
  have e7 := Gates.extends_trans e6 p7.2.1; have l7 := hle_wf hgI p7.1 e7
  have e07 := Gates.extends_trans he0I e7; have l07 := hl0I.trans l7
  have hm_val :
      let m : SignType := match oc.state with
        | none => .zero
        | some q => ((tm.tr q oc.inputTape.head.toOption
            (fun r' => (oc.workTapes r').head.toOption)).workTapes r).2
      r7.1.val x r1.2 = decide (m = .neg) ∧
      r7.1.val x r2.2 = decide (m = .zero) ∧
      r7.1.val x r3.2 = decide (m = .pos) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Gates.val_of_extends_wf p1.1 (Gates.extends_trans p2.2.1 (Gates.extends_trans p3.2.1
        (Gates.extends_trans p4.2.1 (Gates.extends_trans p5.2.1
          (Gates.extends_trans p6.2.1 p7.2.1))))) p1.2.2.1,
        p1.2.2.2.2, Gates.val_of_extends_wf hg he0c hfls, hflsV, Bool.false_or]
      cases hst : oc.state <;> simp [act]
    · rw [Gates.val_of_extends_wf p2.1 (Gates.extends_trans p3.2.1 (Gates.extends_trans p4.2.1
        (Gates.extends_trans p5.2.1 (Gates.extends_trans p6.2.1 p7.2.1)))) p2.2.2.1, p2.2.2.2.2,
        Gates.val_of_extends_wf hg (Gates.extends_trans he0I e1) hsHalt, hsHaltV]
      cases hst : oc.state <;> simp [act]
    · rw [Gates.val_of_extends_wf p3.1 (Gates.extends_trans p4.2.1 (Gates.extends_trans p5.2.1
        (Gates.extends_trans p6.2.1 p7.2.1))) p3.2.2.1, p3.2.2.2.2,
        Gates.val_of_extends_wf hg (Gates.extends_trans he0I e2) hfls, hflsV, Bool.false_or]
      cases hst : oc.state <;> simp [act]
  have hohW : (r7.1.val x r1.2 = true ∧ r7.1.val x r2.2 = false ∧ r7.1.val x r3.2 = false) ∨
      (r7.1.val x r1.2 = false ∧ r7.1.val x r2.2 = true ∧ r7.1.val x r3.2 = false) ∨
      (r7.1.val x r1.2 = false ∧ r7.1.val x r2.2 = false ∧ r7.1.val x r3.2 = true) := by
    rw [hm_val.1, hm_val.2.1, hm_val.2.2]
    set m : SignType := match oc.state with
      | none => .zero
      | some q => ((tm.tr q oc.inputTape.head.toOption
          (fun r' => (oc.workTapes r').head.toOption)).workTapes r).2
    cases m <;> simp
  have hw_val :
      (r7.1.val x r6.2, r7.1.val x r7.2) =
        match oc.state with
        | none => (oc.workTapes r).head
        | some q =>
          match ((tm.tr q oc.inputTape.head.toOption
              (fun r' => (oc.workTapes r').head.toOption)).workTapes r).1 with
          | none => (oc.workTapes r).head
          | some s => BlockCell.ofOption s := by
    have hv6 : r7.1.val x r6.2 = (decide (oc.state = none) && (oc.workTapes r).head.1 ||
        match oc.state with
        | none => false
        | some q => (wkCell (e q, oc.inputTape.head, fun r' => (oc.workTapes r').head)).1) := by
      dsimp only [r7, r6, r5, r4, r3, r2, r1]
      rw [Gates.val_of_extends_wf p6.1 p7.2.1 p6.2.2.1, p6.2.2.2.2,
        Gates.val_of_extends_wf p4.1 p5.2.1 p4.2.2.1, p4.2.2.2.2,
        Gates.val_of_extends_wf hg e03 hsHalt, Gates.val_of_extends_wf hg e03 htw.1,
        hsHaltV, (Prod.mk.inj htw.2.2.1).1]
    have hv7 : r7.1.val x r7.2 = (decide (oc.state = none) && (oc.workTapes r).head.2 ||
        match oc.state with
        | none => false
        | some q => (wkCell (e q, oc.inputTape.head, fun r' => (oc.workTapes r').head)).2) := by
      dsimp only [r7, r6, r5, r4, r3, r2, r1]
      rw [p7.2.2.2.2, Gates.val_of_extends_wf p5.1 p6.2.1 p5.2.2.1, p5.2.2.2.2,
        Gates.val_of_extends_wf hg e04 hsHalt, Gates.val_of_extends_wf hg e04 htw.2.1,
        hsHaltV, (Prod.mk.inj htw.2.2.1).2]
    rw [hv6, hv7]; cases hst : oc.state <;> simp [wkCell, act]
  set r8 := emitTapeStep0 r7.1 fls r1.2 r2.2 r3.2 r6.2 r7.2 tw
  have hp8 := emitTapeStep0_spec hL p7.1 (lt_of_lt_of_le hfls l07)
    (by rw [Gates.val_of_extends_wf hg e07 hfls, hflsV])
    (lt_of_lt_of_le p1.2.2.1 (hle_wf p1.1 p7.1 (Gates.extends_trans p2.2.1
      (Gates.extends_trans p3.2.1
      (Gates.extends_trans p4.2.1 (Gates.extends_trans p5.2.1
        (Gates.extends_trans p6.2.1 p7.2.1)))))))
    (lt_of_lt_of_le p2.2.2.1 (hle_wf p2.1 p7.1 (Gates.extends_trans p3.2.1
      (Gates.extends_trans p4.2.1
      (Gates.extends_trans p5.2.1 (Gates.extends_trans p6.2.1 p7.2.1))))))
    (lt_of_lt_of_le p3.2.2.1 (hle_wf p3.1 p7.1 (Gates.extends_trans p4.2.1
      (Gates.extends_trans p5.2.1
      (Gates.extends_trans p6.2.1 p7.2.1)))))
    (lt_of_lt_of_le p6.2.2.1 (hle_wf p6.1 p7.1 p7.2.1)) p7.2.2.1
    (htw.of_extends hg e07 l07)
    (BlockHalfTape.cnt0_of_inv hL hinv.1) (BlockHalfTape.cnt0_of_inv hL hinv.2) hohW
  have e08 := Gates.extends_trans e07 hp8.2.1; have l08 := hle_wf hg hp8.1 e08
  have hstL := BlockHalfTape.step0_of_inv hL hinv.1
  have hstR := BlockHalfTape.step0_of_inv hL hinv.2
  set r9 := emitSchedulePass L fls t r8.1 r8.2.2.1
  have hp9 := emitSchedulePass_spec hL hp8.1 (lt_of_lt_of_le hfls l08)
    (by rw [Gates.val_of_extends_wf hg e08 hfls, hflsV]) hp8.2.2.2.2.2.2.1
    (by dsimp only; rcases hohW with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
        dsimp only [r7, r6, r5, r4, r3, r2, r1] at h1 h2
        · simp only [h1, ↓reduceIte]; exact hstL.2.1
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstL.2.2
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstL.1 _)
  have e09 := Gates.extends_trans e08 hp9.2.1; have l09 := hle_wf hg hp9.1 e09
  set r10 := emitSchedulePass L fls t r9.1 r8.2.2.2
  have hp10 := emitSchedulePass_spec hL hp9.1 (lt_of_lt_of_le hfls l09)
    (by rw [Gates.val_of_extends_wf hg e09 hfls, hflsV])
    (hp8.2.2.2.2.2.2.2.of_extends hp8.1 hp9.2.1 (hle_wf hp8.1 hp9.1 hp9.2.1))
    (by dsimp only; rcases hohW with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
        dsimp only [r7, r6, r5, r4, r3, r2, r1] at h1 h2
        · simp only [h1, ↓reduceIte]; exact hstR.1 _
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstR.2.2
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstR.2.1)
  have hExtAll := Gates.extends_trans p1.2.1 (Gates.extends_trans p2.2.1 (Gates.extends_trans p3.2.1
    (Gates.extends_trans p4.2.1 (Gates.extends_trans p5.2.1 (Gates.extends_trans p6.2.1
      (Gates.extends_trans p7.2.1 (Gates.extends_trans hp8.2.1
        (Gates.extends_trans hp9.2.1 hp10.2.1))))))))
  refine ⟨hp10.1, hExtAll,
    by rw [hp10.2.2.1, hp9.2.2.1, hp8.2.2.1, p7.2.2.2.1, p6.2.2.2.1, p5.2.2.2.1, p4.2.2.2.1,
         p3.2.2.2.1, p2.2.2.2.1, p1.2.2.2.1]; dsimp only [wkCell, act, sits]; omega, ?_⟩
  let btW0 : BlockTape L :=
    match (if r7.1.val x r1.2 then SignType.neg else if r7.1.val x r2.2 then .zero else .pos) with
    | .zero => { head := (r7.1.val x r6.2, r7.1.val x r7.2), left := (oc.workTapes r).left,
                 right := (oc.workTapes r).right }
    | .pos => let p := (oc.workTapes r).right.pop0 hL
              { head := p.1, left :=
                (oc.workTapes r).left.push0 hL (r7.1.val x r6.2, r7.1.val x r7.2),
                right := p.2 }
    | .neg => let p := (oc.workTapes r).left.pop0 hL
              { head := p.1, left := p.2,
                right := (oc.workTapes r).right.push0 hL (r7.1.val x r6.2, r7.1.val x r7.2) }
  have htw_enc : TapeW.Encodes r10.1 x (r8.2.1, (r9.2, r10.2))
      { head := btW0.head, left := btW0.left.rebalanceSchedule t, right :=
        btW0.right.rebalanceSchedule t } :=
    ⟨lt_of_lt_of_le hp8.2.2.2.1 (hle_wf hp8.1 hp10.1 (Gates.extends_trans hp9.2.1 hp10.2.1)),
     lt_of_lt_of_le hp8.2.2.2.2.1 (hle_wf hp8.1 hp10.1 (Gates.extends_trans hp9.2.1 hp10.2.1)),
     by rw [Gates.val_of_extends_wf hp8.1 (Gates.extends_trans hp9.2.1 hp10.2.1) hp8.2.2.2.1,
          Gates.val_of_extends_wf hp8.1 (Gates.extends_trans hp9.2.1 hp10.2.1) hp8.2.2.2.2.1]
        exact hp8.2.2.2.2.2.1,
     hp9.2.2.2.of_extends hp9.1 hp10.2.1 (hle_wf hp9.1 hp10.1 hp10.2.1),
     hp10.2.2.2⟩
  have hm_eq : (if r7.1.val x r1.2 then SignType.neg else if r7.1.val x r2.2 then .zero else .pos) =
      match oc.state with
      | none => .zero
      | some q => ((tm.tr q oc.inputTape.head.toOption
          (fun r' => (oc.workTapes r').head.toOption)).workTapes r).2 := by
    rw [hm_val.1, hm_val.2.1]
    set m : SignType := match oc.state with
      | none => .zero
      | some q => ((tm.tr q oc.inputTape.head.toOption
          (fun r' => (oc.workTapes r').head.toOption)).workTapes r).2
    cases m <;> rfl
  dsimp only [btW0] at htw_enc
  rw [hm_eq, hw_val] at htw_enc
  cases hst : oc.state with
  | none => simpa [ObliviousCfg.step_eq, BlockTape.step_eq, hst] using htw_enc
  | some q =>
    cases hm : ((tm.tr q oc.inputTape.head.toOption
        (fun r' => (oc.workTapes r').head.toOption)).workTapes r).2 <;>
      · simp only [ObliviousCfg.step_eq, BlockTape.step_eq, hst, hm] at htw_enc ⊢
        exact htw_enc


@[simp] theorem outViewIdx_empty : outViewIdx .empty = 0 := rfl

@[simp] theorem outViewIdx_one_false : outViewIdx (.one false) = 1 := rfl

@[simp] theorem outViewIdx_one_true : outViewIdx (.one true) = 2 := rfl

@[simp] theorem outViewIdx_many : outViewIdx .many = 3 := rfl

@[simp] theorem litWire_true (w nw : ℕ) : litWire true w nw = w := rfl

@[simp] theorem litWire_false (w nw : ℕ) : litWire false w nw = nw := rfl

theorem defaultTapeW_eq :
    defaultTapeW = ((0, 0), ([], [])) := rfl

theorem schedulePassCost_eq (L t : ℕ) :
    schedulePassCost L t =
      ((List.range (L - 1)).map fun lvl =>
        if (t + 1) % 2 ^ (lvl + 1) = 0 then 37 + 210 * 2 ^ lvl else 0).sum := rfl

theorem initHalfConstW_eq (L fls tru w0 w1 : ℕ) :
    initHalfConstW L fls tru w0 w1 =
      (List.range L).map fun i =>
        ([fls, fls, tru, fls, fls, fls], List.replicate (2 ^ i) [w0, w1, w0, w1, w0, w1, w0, w1, w0,
          w1]) := rfl

theorem initHalfFromW_eq (L fls tru : ℕ) (cells : List (ℕ × ℕ)) (def0 def1 : ℕ) :
    initHalfFromW L fls tru cells def0 def1 =
      (List.range L).map fun i =>
        let B := 2 ^ i
        let off := 2 * (B - 1)
        ([fls, fls, tru, fls, fls, fls],
          (List.range B).map fun j =>
            let c0 := cells.getD (off + j) (def0, def1)
            let c1 := cells.getD (off + B + j) (def0, def1)
            let c2 := cells.getD (off + 2 * B + j) (def0, def1)
            let c3 := cells.getD (off + 3 * B + j) (def0, def1)
            let c4 := cells.getD (off + 4 * B + j) (def0, def1)
            [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2]) := rfl

theorem initStateW_eq (L k numStates q0Idx fls tru : ℕ) (inputWires : List ℕ) :
    initStateW L k numStates q0Idx fls tru inputWires =
      let inHead := match inputWires with | [] => (fls, tru) | w :: _ => (tru, w)
      let inRightCells := (inputWires.drop 1).map fun w => (tru, w)
      let stateW := (List.range (numStates + 1)).map fun s => if s = q0Idx + 1 then tru else fls
      let outW := [tru, fls, fls, fls]
      let inTape : TapeW :=
        (inHead, (initHalfConstW L fls tru fls fls, initHalfFromW L fls tru inRightCells fls tru))
      let wkTape : TapeW :=
        ((fls, fls), (initHalfConstW L fls tru fls fls, initHalfConstW L fls tru fls fls))
      ((stateW, outW), (inTape, List.replicate k wkTape)) := rfl

theorem emitIndicators_eq {k numStates : ℕ} (g : Gates) (tru : ℕ) (sw : StateW)
    (inNeg0 inNeg1 : ℕ) (wkNeg0 wkNeg1 : List ℕ) (sits : List (ActiveSit k numStates)) :
    emitIndicators g tru sw inNeg0 inNeg1 wkNeg0 wkNeg1 sits =
      emitMap g (fun gc sit =>
        let qW := sw.1.1.getD (sit.1.val + 1) 0
        let inW0 := litWire sit.2.1.1 sw.2.1.1.1 inNeg0
        let inW1 := litWire sit.2.1.2 sw.2.1.1.2 inNeg1
        let wkWs := (List.finRange k).flatMap fun r =>
          let tw := sw.2.2.getD r.val defaultTapeW
          [litWire (sit.2.2 r).1 tw.1.1 (wkNeg0.getD r.val 0),
           litWire (sit.2.2 r).2 tw.1.2 (wkNeg1.getD r.val 0)]
        Gates.gAndList gc tru (qW :: inW0 :: inW1 :: wkWs)) sits := rfl

theorem emitOutUpdate_eq (g : Gates) (sHalt outNone outF outT : ℕ) (outW : List ℕ) :
    emitOutUpdate g sHalt outNone outF outT outW =
      let o0 := outW.getD 0 0; let o1 := outW.getD 1 0
      let o2 := outW.getD 2 0; let o3 := outW.getD 3 0
      let (g, oFT) := Gates.gOr g outF outT
      let (g, o123) := Gates.gOr3 g o1 o2 o3
      let andPairs : List (ℕ × ℕ) :=
        [(sHalt, o0), (sHalt, o1), (sHalt, o2), (sHalt, o3),
         (outNone, o0), (outNone, o1), (outNone, o2), (outNone, o3),
         (outF, o0), (outT, o0), (oFT, o123)]
      let (g, ps) := emitMap g (fun gc p => Gates.gAnd gc p.1 p.2) andPairs
      let a := fun k => ps.getD k 0
      let orTriples : List (ℕ × ℕ × ℕ) :=
        [(a 0, a 4, a 4), (a 1, a 5, a 8), (a 2, a 6, a 9), (a 3, a 7, a 10)]
      emitMap g (fun gc t => Gates.gOr3 gc t.1 t.2.1 t.2.2) orTriples := rfl

theorem pickWires_eq {k numStates : ℕ} (sits : List (ActiveSit k numStates))
    (inds : List ℕ) (pred : ActiveSit k numStates → Bool) :
    pickWires sits inds pred =
      ((List.range sits.length).filter fun idx =>
        (sits[idx]?.map fun sit => pred sit).getD false).map
        fun idx => inds.getD idx 0 := rfl

theorem emitWorkTapeStep_eq {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls t sHalt : ℕ) (inds : List ℕ) (tw : TapeW) (gc : Gates) (r : Fin k) :
    emitWorkTapeStep e tm L fls t sHalt inds tw gc r =
      let sits := allActiveSits k numStates
      let act : ActiveSit k numStates → Action k Bool State := fun sit =>
        tm.tr (e.symm sit.1) sit.2.1.toOption (fun r' => (sit.2.2 r').toOption)
      let (gc, mNeg) := Gates.gOrList gc fls
        (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .neg))
      let (gc, mZero) := Gates.gOrList gc sHalt
        (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .zero))
      let (gc, mPos) := Gates.gOrList gc fls
        (pickWires sits inds fun sit => decide (((act sit).workTapes r).2 = .pos))
      let (gc, hW0) := Gates.gAnd gc sHalt tw.1.1
      let (gc, hW1) := Gates.gAnd gc sHalt tw.1.2
      let wkCell := fun (sit : ActiveSit k numStates) =>
        match ((act sit).workTapes r).1 with
        | none => sit.2.2 r
        | some s => BlockCell.ofOption s
      let (gc, w0) := Gates.gOrList gc hW0 (pickWires sits inds fun sit => (wkCell sit).1)
      let (gc, w1) := Gates.gOrList gc hW1 (pickWires sits inds fun sit => (wkCell sit).2)
      let (gc, tw0) := emitTapeStep0 gc fls mNeg mZero mPos w0 w1 tw
      let (gc, twL) := emitSchedulePass L fls t gc tw0.2.1
      let (gc, twR) := emitSchedulePass L fls t gc tw0.2.2
      (gc, (tw0.1, (twL, twR))) := rfl

theorem emitTmStep_eq {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (L fls tru t : ℕ) (g : Gates) (sw : StateW) :
    emitTmStep e tm L fls tru t g sw =
      let sits := allActiveSits k numStates
      let act : ActiveSit k numStates → Action k Bool State := fun sit =>
        tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
      let (g, inN0) := Gates.gNot g sw.2.1.1.1
      let (g, inN1) := Gates.gNot g sw.2.1.1.2
      let (g, wkN0) := emitMap g (fun gc r => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.1)
        (List.finRange k)
      let (g, wkN1) := emitMap g (fun gc r => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.2)
        (List.finRange k)
      let (g, inds) := emitIndicators g tru sw inN0 inN1 wkN0 wkN1 sits
      let sHalt := sw.1.1.getD 0 0
      let (g, ns0) := Gates.gOrList g sHalt
        (pickWires sits inds fun sit => decide ((act sit).state = none))
      let (g, nsRest) := emitMap g (fun gc (q' : Fin numStates) =>
        Gates.gOrList gc fls
          (pickWires sits inds fun sit => decide ((act sit).state.map e = some q')))
        (List.finRange numStates)
      let nextStateW := ns0 :: nsRest
      let (g, outNone) := Gates.gOrList g fls
        (pickWires sits inds fun sit => decide ((act sit).output = none))
      let (g, outF) := Gates.gOrList g fls
        (pickWires sits inds fun sit => decide ((act sit).output = some false))
      let (g, outT) := Gates.gOrList g fls
        (pickWires sits inds fun sit => decide ((act sit).output = some true))
      let (g, nextOutW) := emitOutUpdate g sHalt outNone outF outT sw.1.2
      let (g, inNeg) := Gates.gOrList g fls
        (pickWires sits inds fun sit =>
          decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg))
      let (g, inZero) := Gates.gOrList g sHalt
        (pickWires sits inds fun sit =>
          decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero))
      let (g, inPos) := Gates.gOrList g fls
        (pickWires sits inds fun sit =>
          decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos))
      let (g, inTape0) := emitTapeStep0 g fls inNeg inZero inPos sw.2.1.1.1 sw.2.1.1.2 sw.2.1
      let (g, inL) := emitSchedulePass L fls t g inTape0.2.1
      let (g, inR) := emitSchedulePass L fls t g inTape0.2.2
      let nextInTape : TapeW := (inTape0.1, (inL, inR))
      let resWk := (List.finRange k).foldl (fun (acc : Gates × List TapeW) (r : Fin k) =>
        let p := emitWorkTapeStep e tm L fls t sHalt inds
          (sw.2.2.getD r.val defaultTapeW) acc.1 r
        (p.1, p.2 :: acc.2)) (g, [])
      (resWk.1, ((nextStateW, nextOutW), (nextInTape, resWk.2.reverse))) := rfl

theorem tmStepBaseCost_eq {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) :
    tmStepBaseCost e tm =
      let sits := allActiveSits k numStates
      let act : ActiveSit k numStates → Action k Bool State := fun sit =>
        tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
      let pickLen := fun (pred : ActiveSit k numStates → Bool) =>
        ((List.range sits.length).filter fun idx =>
          (sits[idx]?.map fun sit => pred sit).getD false).length
      (2 + 2 * k) + (3 + 2 * k) * sits.length +
      pickLen (fun sit => decide ((act sit).state = none)) +
      ((List.finRange numStates).map fun q' =>
        pickLen (fun sit => decide ((act sit).state.map e = some q'))).sum +
      pickLen (fun sit => decide ((act sit).output = none)) +
      pickLen (fun sit => decide ((act sit).output = some false)) +
      pickLen (fun sit => decide ((act sit).output = some true)) + 22 +
      pickLen (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg)) +
      pickLen (fun sit =>
        decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero)) +
      pickLen (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos)) +
      170 + ((List.finRange k).map (workTapeStepCost e tm)).sum := rfl

end CslibFrontier.Computability.Circuit.Oblivious
