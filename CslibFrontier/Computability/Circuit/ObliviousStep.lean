module

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.ObliviousSimulation
import CslibFrontier.Computability.Circuit.Boolean.OpValue
import CslibFrontier.Computability.Circuit.Encoding.Evaluation
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Pippenger–Fischer Oblivious Step and $O(T \log T)$ Circuit Builder

This module completes the Pippenger–Fischer oblivious Boolean circuit
simulation, proving correctness and the $O(T \log T)$ gate bound for `emitTmStep`,
`buildGates`, and `obliviousCircuitWithWires`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Oblivious.pfLevels`: canonical level count `L(T, N)`.
* `CslibFrontier.Computability.Circuit.Oblivious.buildGates`: full `T`-step oblivious gate
  builder.
* `CslibFrontier.Computability.Circuit.Oblivious.obliviousCircuitWithWires`: resulting
  `Circuit Boolean.signature totalInputs 1` with optional output negation.

## Main results

* `CslibFrontier.Computability.Circuit.Oblivious.emitTmStep_spec`: correctness and exact gate
  count of one full oblivious TM step.
* `CslibFrontier.Computability.Circuit.Oblivious.size_obliviousCircuitWithWires_le`: the
  oblivious circuit has $O((T + 1)(\log_2(\max(T, N) + 2) + 1))$ gates, independent of
  `totalInputs`.
* `CslibFrontier.Computability.Circuit.Oblivious.eval_obliviousCircuitWithWires`: exact
  evaluation equivalence against `tm.runFrom (tm.initCfg input) T`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Oblivious

open Turing MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

namespace Gates

theorem gMux_spec {x : List Bool} {g : Gates} {sel a b : ℕ} (hg : g.WF x.length)
    (hs : sel < g.2) (ha : a < g.2) (hb : b < g.2) :
    let r := gMux g sel a b
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + 4 ∧
      r.1.val x r.2 = (if g.val x sel then g.val x a else g.val x b) := by
  rw [gMux_eq]
  dsimp only
  have h1 := gNot_spec hg hs
  have hlt1 : g.2 < (gNot g sel).1.2 := by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega
  have h2 := gAnd_spec h1.1 (lt_trans hs hlt1) (lt_trans ha hlt1)
  have hlt2 : (gNot g sel).1.2 < (gAnd (gNot g sel).1 sel a).1.2 := by
    rw [h2.1.2, h1.1.2, h2.2.2.2.1]; omega
  have h3 := gAnd_spec h2.1 (lt_trans h1.2.2.1 hlt2) (lt_trans (lt_trans hb hlt1) hlt2)
  have hlt3 : (gAnd (gNot g sel).1 sel a).1.2 <
      (gAnd (gAnd (gNot g sel).1 sel a).1 (gNot g sel).2 b).1.2 := by
    rw [h3.1.2, h2.1.2, h3.2.2.2.1]; omega
  have h4 := gOr_spec h3.1 (lt_trans h2.2.2.1 hlt3) h3.2.2.1
  have he12 := extends_trans h1.2.1 h2.2.1
  have he13 := extends_trans he12 h3.2.1
  refine ⟨h4.1, extends_trans he13 h4.2.1, h4.2.2.1,
    by rw [h4.2.2.2.1, h3.2.2.2.1, h2.2.2.2.1, h1.2.2.2.1], ?_⟩
  rw [h4.2.2.2.2, val_of_extends_wf h2.1 h3.2.1 h2.2.2.1, h2.2.2.2.2,
    val_of_extends_wf hg h1.2.1 hs, val_of_extends_wf hg h1.2.1 ha,
    h3.2.2.2.2, val_of_extends_wf h1.1 h2.2.1 h1.2.2.1, h1.2.2.2.2,
    val_of_extends_wf hg he12 hb]
  cases g.val x sel <;> simp

theorem gAndList_spec {x : List Bool} {g : Gates} {tru : ℕ} {ws : List ℕ}
    (hg : g.WF x.length) (htru : tru < g.2) (hws : ∀ w ∈ ws, w < g.2) :
    let r := gAndList g tru ws
    r.1.WF x.length ∧ Extends g r.1 ∧ r.2 < r.1.2 ∧ r.1.1.length = g.1.length + ws.length ∧
      r.1.val x r.2 = (g.val x tru && ws.all (g.val x)) := by
  induction ws generalizing g tru with
  | nil =>
    exact ⟨hg, extends_refl g, htru, rfl, by simp [gAndList_eq]⟩
  | cons w tl ih =>
    simp only [gAndList_eq, List.foldl_cons]
    have hw : w < g.2 := hws w List.mem_cons_self
    have h1 := gAnd_spec hg htru hw
    have hlt1 : g.2 < (gAnd g tru w).1.2 := by rw [h1.1.2, hg.2, h1.2.2.2.1]; omega
    have h2 := ih h1.1 h1.2.2.1 (fun u hu => lt_trans (hws u (List.mem_cons_of_mem w hu)) hlt1)
    dsimp only [gAndList_eq] at h2
    refine ⟨h2.1, extends_trans h1.2.1 h2.2.1, h2.2.2.1,
      by rw [h2.2.2.2.1, h1.2.2.2.1, List.length_cons]; omega, ?_⟩
    rw [h2.2.2.2.2, h1.2.2.2.2]
    have hall : tl.all ((gAnd g tru w).1.val x) = tl.all (g.val x) := by
      rw [Bool.eq_iff_iff]; simp only [List.all_eq_true]
      exact forall_congr' fun u => imp_congr_right fun hu => by
        rw [val_of_extends_wf hg h1.2.1 (hws u (List.mem_cons_of_mem w hu))]
    rw [hall]; simp [Bool.and_assoc]

end Gates

private theorem getD_mem_of_lt {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem emitTmStep_spec {k L numStates : ℕ} {State : Type} (e : State ≃ Fin numStates)
    (tm : MultiTapeTM k Bool State) {x : List Bool} {g : Gates} {fls tru t : ℕ}
    {sw : StateW} {oc : ObliviousCfg k L State} (hL : 0 < L)
    (hg : g.WF x.length) (hfls : fls < g.2) (hflsV : g.val x fls = false)
    (htru : tru < g.2) (htruV : g.val x tru = true)
    (henc : StateW.Encodes e g x sw oc)
    (hinvIn : oc.inputTape.Inv t) (hinvWk : ∀ r : Fin k, (oc.workTapes r).Inv t) :
    let res := emitTmStep e tm L fls tru t g sw
    res.1.WF x.length ∧ Gates.Extends g res.1 ∧
    res.1.1.length = g.1.length + tmStepBaseCost e tm + (2 + 2 * k) * schedulePassCost L t ∧
    StateW.Encodes e res.1 x res.2 (oc.step hL tm t) := by
  have hle_wf : ∀ {ga gb : Gates}, ga.WF x.length → gb.WF x.length → Gates.Extends ga gb →
      ga.2 ≤ gb.2 := fun hw1 hw2 ⟨rr, hrr⟩ => by rw [hw1.2, hw2.2, hrr, List.length_append]; omega
  dsimp only [emitTmStep_eq, tmStepBaseCost_eq]
  set sits := allActiveSits k numStates
  set act : ActiveSit k numStates → Action k Bool State := fun sit =>
    tm.tr (e.symm sit.1) sit.2.1.toOption (fun r => (sit.2.2 r).toOption)
  -- Step 1: Head negations (`inN0, inN1, wkN0, wkN1`)
  set rN0 := Gates.gNot g sw.2.1.1.1
  have hn0 := Gates.gNot_spec hg henc.2.2.2.2.2.2.2.1.1
  have hle_n0 := hle_wf hg hn0.1 hn0.2.1
  set rN1 := Gates.gNot rN0.1 sw.2.1.1.2
  have hn1 := Gates.gNot_spec hn0.1 (lt_of_lt_of_le henc.2.2.2.2.2.2.2.1.2.1 hle_n0)
  have hle_n1 := hle_wf hn0.1 hn1.1 hn1.2.1
  have he_n1 := Gates.extends_trans hn0.2.1 hn1.2.1
  have hle_0n1 := hle_n0.trans hle_n1
  have hwk0_enc := fun (r : Fin k) => henc.2.2.2.2.2.2.2.2.2 r
  set rWkN0 :=
    emitMap rN1.1 (fun gc (r : Fin k) => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.1)
    (List.finRange k)
  have hwkN0 := emitMap_spec (x := x) (K := 1) (xs := List.finRange k)
    (f := fun gc (r : Fin k) => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.1)
    (spec := fun r => !(oc.workTapes r).head.1) hn1.1 (fun gc r _ hgc hextc => by
      have hle_c := hle_0n1.trans (hle_wf hn1.1 hgc hextc)
      have hm := Gates.gNot_spec hgc (lt_of_lt_of_le (hwk0_enc r).1 hle_c)
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
      rw [hm.2.2.2.2, Gates.val_of_extends_wf hg (Gates.extends_trans he_n1 hextc) (hwk0_enc r).1,
        (Prod.mk.inj (hwk0_enc r).2.2.1).1])
  have hle_wn0 := hle_wf hn1.1 hwkN0.1 hwkN0.2.1
  have he_wn0 := Gates.extends_trans he_n1 hwkN0.2.1
  have hle_0wn0 := hle_0n1.trans hle_wn0
  set rWkN1 :=
    emitMap rWkN0.1 (fun gc (r : Fin k) => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.2)
    (List.finRange k)
  have hwkN1 := emitMap_spec (x := x) (K := 1) (xs := List.finRange k)
    (f := fun gc (r : Fin k) => Gates.gNot gc (sw.2.2.getD r.val defaultTapeW).1.2)
    (spec := fun r => !(oc.workTapes r).head.2) hwkN0.1 (fun gc r _ hgc hextc => by
      have hle_c := hle_0wn0.trans (hle_wf hwkN0.1 hgc hextc)
      have hm := Gates.gNot_spec hgc (lt_of_lt_of_le (hwk0_enc r).2.1 hle_c)
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
      rw [hm.2.2.2.2,
        Gates.val_of_extends_wf hg (Gates.extends_trans he_wn0 hextc) (hwk0_enc r).2.1,
        (Prod.mk.inj (hwk0_enc r).2.2.1).2])
  have hle_wn1 := hle_wf hwkN0.1 hwkN1.1 hwkN1.2.1
  have he_wn1 := Gates.extends_trans he_wn0 hwkN1.2.1
  have hle_0wn1 := hle_0wn0.trans hle_wn1
  -- Step 2: Situation indicators
  have hlit_in0 : ∀ b, litWire b sw.2.1.1.1 rN0.2 < rWkN1.1.2 ∧
      rWkN1.1.val x (litWire b sw.2.1.1.1 rN0.2) = (oc.inputTape.head.1 == b) := by
    intro b; cases b <;> simp only [litWire_false, litWire_true]
    · refine ⟨lt_of_lt_of_le hn0.2.2.1 (hle_n1.trans (hle_wn0.trans hle_wn1)), ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hn0.1 (Gates.extends_trans hn1.2.1
        (Gates.extends_trans hwkN0.2.1 hwkN1.2.1))
        hn0.2.2.1, hn0.2.2.2.2, (Prod.mk.inj henc.2.2.2.2.2.2.2.1.2.2.1).1]
      cases oc.inputTape.head.1 <;> rfl
    · refine ⟨lt_of_lt_of_le henc.2.2.2.2.2.2.2.1.1 hle_0wn1, ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hg he_wn1 henc.2.2.2.2.2.2.2.1.1,
        (Prod.mk.inj henc.2.2.2.2.2.2.2.1.2.2.1).1]
      cases oc.inputTape.head.1 <;> rfl
  have hlit_in1 : ∀ b, litWire b sw.2.1.1.2 rN1.2 < rWkN1.1.2 ∧
      rWkN1.1.val x (litWire b sw.2.1.1.2 rN1.2) = (oc.inputTape.head.2 == b) := by
    intro b; cases b <;> simp only [litWire_false, litWire_true]
    · refine ⟨lt_of_lt_of_le hn1.2.2.1 (hle_wn0.trans hle_wn1), ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hn1.1 (Gates.extends_trans hwkN0.2.1 hwkN1.2.1) hn1.2.2.1,
        hn1.2.2.2.2, Gates.val_of_extends_wf hg hn0.2.1 henc.2.2.2.2.2.2.2.1.2.1,
        (Prod.mk.inj henc.2.2.2.2.2.2.2.1.2.2.1).2]
      cases oc.inputTape.head.2 <;> rfl
    · refine ⟨lt_of_lt_of_le henc.2.2.2.2.2.2.2.1.2.1 hle_0wn1, ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hg he_wn1 henc.2.2.2.2.2.2.2.1.2.1,
        (Prod.mk.inj henc.2.2.2.2.2.2.2.1.2.2.1).2]
      cases oc.inputTape.head.2 <;> rfl
  have hlit_wk0 : ∀ (r : Fin k) (b : Bool),
      litWire b (sw.2.2.getD r.val defaultTapeW).1.1 (rWkN0.2.getD r.val 0) < rWkN1.1.2 ∧
      rWkN1.1.val x (litWire b (sw.2.2.getD r.val defaultTapeW).1.1 (rWkN0.2.getD r.val 0)) =
        ((oc.workTapes r).head.1 == b) := by
    intro r b; cases b <;> simp only [litWire_false, litWire_true]
    · have hmem : rWkN0.2.getD r.val 0 ∈ rWkN0.2 := getD_mem_of_lt (by rw [hwkN0.2.2.1]; simp)
      refine ⟨lt_of_lt_of_le (hwkN0.2.2.2.2.1 _ hmem) hle_wn1, ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hwkN0.1 hwkN1.2.1 (hwkN0.2.2.2.2.1 _ hmem),
        hwkN0.2.2.2.2.2 r.val (by simp)]
      simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
      cases (oc.workTapes r).head.1 <;> rfl
    · refine ⟨lt_of_lt_of_le (hwk0_enc r).1 hle_0wn1, ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hg he_wn1 (hwk0_enc r).1, (Prod.mk.inj (hwk0_enc r).2.2.1).1]
      cases (oc.workTapes r).head.1 <;> rfl
  have hlit_wk1 : ∀ (r : Fin k) (b : Bool),
      litWire b (sw.2.2.getD r.val defaultTapeW).1.2 (rWkN1.2.getD r.val 0) < rWkN1.1.2 ∧
      rWkN1.1.val x (litWire b (sw.2.2.getD r.val defaultTapeW).1.2 (rWkN1.2.getD r.val 0)) =
        ((oc.workTapes r).head.2 == b) := by
    intro r b; cases b <;> simp only [litWire_false, litWire_true]
    · have hmem : rWkN1.2.getD r.val 0 ∈ rWkN1.2 := getD_mem_of_lt (by rw [hwkN1.2.2.1]; simp)
      refine ⟨hwkN1.2.2.2.2.1 _ hmem, ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [hwkN1.2.2.2.2.2 r.val (by simp)]
      simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
      cases (oc.workTapes r).head.2 <;> rfl
    · refine ⟨lt_of_lt_of_le (hwk0_enc r).2.1 hle_0wn1, ?_⟩
      dsimp only [rWkN1, rWkN0, rN1, rN0]
      rw [Gates.val_of_extends_wf hg he_wn1 (hwk0_enc r).2.1, (Prod.mk.inj (hwk0_enc r).2.2.1).2]
      cases (oc.workTapes r).head.2 <;> rfl
  set rInds := emitIndicators rWkN1.1 tru sw rN0.2 rN1.2 rWkN0.2 rWkN1.2 sits
  have hinds := emitMap_spec (x := x) (K := 3 + 2 * k) (xs := sits)
    (f := fun gc sit =>
      let qW := sw.1.1.getD (sit.1.val + 1) 0
      let inW0 := litWire sit.2.1.1 sw.2.1.1.1 rN0.2
      let inW1 := litWire sit.2.1.2 sw.2.1.1.2 rN1.2
      let wkWs := (List.finRange k).flatMap fun r =>
        let tw := sw.2.2.getD r.val defaultTapeW
        [litWire (sit.2.2 r).1 tw.1.1 (rWkN0.2.getD r.val 0),
         litWire (sit.2.2 r).2 tw.1.2 (rWkN1.2.getD r.val 0)]
      Gates.gAndList gc tru (qW :: inW0 :: inW1 :: wkWs))
    (spec := fun sit => decide (∃ q : State, oc.state = some q ∧
      sit = (e q, oc.inputTape.head, fun r => (oc.workTapes r).head)))
    hwkN1.1 (fun gc sit _ hgc hextc => by
      have hle_c := hle_wf hwkN1.1 hgc hextc
      have hq_lt : sw.1.1.getD (sit.1.val + 1) 0 < rWkN1.1.2 :=
        lt_of_lt_of_le (henc.2.1 _ (getD_mem_of_lt (by rw [henc.1]; omega))) hle_0wn1
      have hws_lt : ∀ w ∈ (sw.1.1.getD (sit.1.val + 1) 0 ::
          litWire sit.2.1.1 sw.2.1.1.1 rN0.2 :: litWire sit.2.1.2 sw.2.1.1.2 rN1.2 ::
          (List.finRange k).flatMap fun r =>
            [litWire (sit.2.2 r).1 (sw.2.2.getD r.val defaultTapeW).1.1 (rWkN0.2.getD r.val 0),
             litWire (sit.2.2 r).2 (sw.2.2.getD r.val defaultTapeW).1.2 (rWkN1.2.getD r.val 0)]),
          w < gc.2 := by
        intro w hw
        simp only [List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hw
        rcases hw with rfl | rfl | rfl | ⟨r, hr⟩
        · exact lt_of_lt_of_le hq_lt hle_c
        · exact lt_of_lt_of_le (hlit_in0 _).1 hle_c
        · exact lt_of_lt_of_le (hlit_in1 _).1 hle_c
        · simp only [List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact lt_of_lt_of_le (hlit_wk0 r _).1 hle_c
          · exact lt_of_lt_of_le (hlit_wk1 r _).1 hle_c
      have hand := Gates.gAndList_spec hgc (lt_of_lt_of_le htru (hle_0wn1.trans hle_c)) hws_lt
      have hlen_ws : (sw.1.1.getD (sit.1.val + 1) 0 ::
          litWire sit.2.1.1 sw.2.1.1.1 rN0.2 :: litWire sit.2.1.2 sw.2.1.1.2 rN1.2 ::
          (List.finRange k).flatMap fun r =>
            [litWire (sit.2.2 r).1 (sw.2.2.getD r.val defaultTapeW).1.1 (rWkN0.2.getD r.val 0),
             litWire (sit.2.2 r).2 (sw.2.2.getD r.val defaultTapeW).1.2
               (rWkN1.2.getD r.val 0)]).length =
          3 + 2 * k := by
        simp [List.length_flatMap]; omega
      refine ⟨hand.1, hand.2.1, hand.2.2.1, by rw [hand.2.2.2.1, hlen_ws], ?_⟩
      rw [hand.2.2.2.2, Gates.val_of_extends_wf hg (Gates.extends_trans he_wn1 hextc) htru, htruV,
        Bool.true_and]
      simp only [List.all_flatMap, List.all_cons, List.all_nil, Bool.and_true]
      rw [Gates.val_of_extends_wf hg (Gates.extends_trans he_wn1 hextc)
          (henc.2.1 _ (getD_mem_of_lt (by rw [henc.1]; omega))),
        henc.2.2.2.1 sit.1,
        Gates.val_of_extends_wf hwkN1.1 hextc (hlit_in0 _).1, (hlit_in0 _).2,
        Gates.val_of_extends_wf hwkN1.1 hextc (hlit_in1 _).1, (hlit_in1 _).2]
      have hall_wk : (List.finRange k).all (fun r =>
          gc.val x (litWire (sit.2.2 r).1 (sw.2.2.getD r.val defaultTapeW).1.1
            (rWkN0.2.getD r.val 0)) &&
          gc.val x (litWire (sit.2.2 r).2 (sw.2.2.getD r.val defaultTapeW).1.2
            (rWkN1.2.getD r.val 0))) =
          decide (sit.2.2 = fun r => (oc.workTapes r).head) := by
        rw [Bool.eq_iff_iff, List.all_eq_true]
        simp only [List.mem_finRange, true_implies, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro h; funext r
          have hr := h r
          rw [Gates.val_of_extends_wf hwkN1.1 hextc (hlit_wk0 r _).1, (hlit_wk0 r _).2,
            Gates.val_of_extends_wf hwkN1.1 hextc (hlit_wk1 r _).1, (hlit_wk1 r _).2] at hr
          exact Prod.ext (beq_iff_eq.mp hr.1).symm (beq_iff_eq.mp hr.2).symm
        · intro h r
          rw [Gates.val_of_extends_wf hwkN1.1 hextc (hlit_wk0 r _).1, (hlit_wk0 r _).2,
            Gates.val_of_extends_wf hwkN1.1 hextc (hlit_wk1 r _).1, (hlit_wk1 r _).2, h]
          exact ⟨beq_self_eq_true _, beq_self_eq_true _⟩
      rw [hall_wk, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨hq, hi0, hi1, hwk⟩
        obtain ⟨q, hqo, hqe⟩ := Option.map_eq_some_iff.mp hq
        exact ⟨q, hqo, Prod.ext hqe.symm (Prod.ext (Prod.ext hi0.symm hi1.symm) hwk)⟩
      · rintro ⟨q, hq, hsit⟩
        have h1 : sit.1 = e q := congrArg Prod.fst hsit
        have h2 : sit.2.1 = oc.inputTape.head := congrArg (fun p => p.2.1) hsit
        have h3 : sit.2.2 = fun r => (oc.workTapes r).head := congrArg (fun p => p.2.2) hsit
        exact ⟨by rw [hq, Option.map_some, h1], (congrArg Prod.fst h2).symm,
          (congrArg Prod.snd h2).symm, h3⟩)
  have hinds_wf : rInds.1.WF x.length := hinds.1
  have hinds_ext : Gates.Extends rWkN1.1 rInds.1 := hinds.2.1
  have hinds_len : rInds.2.length = sits.length := hinds.2.2.1
  have hinds_mem : ∀ w ∈ rInds.2, w < rInds.1.2 := hinds.2.2.2.2.1
  have hinds_val : ∀ (idx : ℕ) (h : idx < sits.length),
      rInds.1.val x (rInds.2.getD idx 0) =
        decide (∃ q : State, oc.state = some q ∧
          sits[idx] = (e q, oc.inputTape.head, fun r => (oc.workTapes r).head)) :=
    hinds.2.2.2.2.2
  have hsits_mem : ∀ sit : ActiveSit k numStates, sit ∈ sits := fun sit =>
    Finset.mem_toList.mpr (Finset.mem_univ sit)
  have hpick_spec : ∀ {gc : Gates} {base : ℕ} (hgc : gc.WF x.length)
      (hextc : Gates.Extends rInds.1 gc) (hbase : base < gc.2) (pred : ActiveSit k numStates →
        Bool),
      let r := Gates.gOrList gc base (pickWires sits rInds.2 pred)
      r.1.WF x.length ∧ Gates.Extends gc r.1 ∧ r.2 < r.1.2 ∧
      r.1.1.length = gc.1.length + ((List.range sits.length).filter fun idx =>
        (sits[idx]?.map fun sit => pred sit).getD false).length ∧
      r.1.val x r.2 = (gc.val x base ||
        match oc.state with
        | none => false
        | some q => pred (e q, oc.inputTape.head, fun r => (oc.workTapes r).head)) := by
    intro gc base hgc hextc hbase pred
    have hle_c := hle_wf hinds_wf hgc hextc
    have hws : ∀ w ∈ pickWires sits rInds.2 pred, w < gc.2 := by
      intro w hw; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hw
      have hlt : idx < sits.length := List.mem_range.mp (List.mem_filter.mp hidx).1
      exact lt_of_lt_of_le (hinds_mem _ (getD_mem_of_lt (by rw [hinds_len]; exact hlt))) hle_c
    have hor := Gates.gOrList_spec hgc hbase hws
    refine ⟨hor.1, hor.2.1, hor.2.2.1, by rw [hor.2.2.2.1, pickWires_eq, List.length_map], ?_⟩
    rw [hor.2.2.2.2]; congr 1
    exact pick_any_eq e sits hsits_mem
      (fun idx h => by
        rw [Gates.val_of_extends_wf hinds_wf hextc
          (hinds_mem _ (getD_mem_of_lt (by rw [hinds_len]; exact h)))]
        exact hinds_val idx h) pred
  have he_I := Gates.extends_trans he_wn1 hinds.2.1
  have hle_0I := hle_wf hg hinds.1 he_I
  have hfls_I : fls < rInds.1.2 := lt_of_lt_of_le hfls hle_0I
  have hsHalt_lt : sw.1.1.getD 0 0 < rInds.1.2 :=
    lt_of_lt_of_le (henc.2.1 _ (getD_mem_of_lt (by rw [henc.1]; omega))) hle_0I
  -- Step 3: Next state wires
  set rNs0 := Gates.gOrList rInds.1 (sw.1.1.getD 0 0)
    (pickWires sits rInds.2 fun sit => decide ((act sit).state = none))
  have hns0 := hpick_spec hinds.1 (Gates.extends_refl _) hsHalt_lt
    (fun sit => decide ((act sit).state = none))
  set rNsRest := emitMap rNs0.1 (fun gc (q' : Fin numStates) =>
    Gates.gOrList gc fls
      (pickWires sits rInds.2 fun sit => decide ((act sit).state.map e = some q')))
    (List.finRange numStates)
  have hnsRest := emitMap_spec_var (x := x) (xs := List.finRange numStates)
    (cost := fun q' => ((List.range sits.length).filter fun idx =>
      (sits[idx]?.map fun sit => decide ((act sit).state.map e = some q')).getD false).length)
    (spec := fun q' => decide ((oc.step hL tm t).state.map e = some q'))
    hns0.1 (fun gc q' _ hgc hextc => by
      have heI := Gates.extends_trans hns0.2.1 hextc
      have hle_c := hle_wf hinds.1 hgc heI
      have h := hpick_spec hgc heI (lt_of_lt_of_le hfls_I hle_c)
        (fun sit => decide ((act sit).state.map e = some q'))
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
      rw [h.2.2.2.2, Gates.val_of_extends_wf hg (Gates.extends_trans he_I heI) hfls, hflsV,
        Bool.false_or]
      cases hst : oc.state with
      | none => simp [ObliviousCfg.step_eq, hst]
      | some q => simp [ObliviousCfg.step_eq, hst, act])
  -- Step 4: Next output-view wires
  have he_ns := Gates.extends_trans hns0.2.1 hnsRest.2.1
  have hle_ns := hle_wf hinds.1 hnsRest.1 he_ns
  set rON := Gates.gOrList rNsRest.1 fls
    (pickWires sits rInds.2 fun sit => decide ((act sit).output = none))
  have hoN := hpick_spec hnsRest.1 he_ns (lt_of_lt_of_le hfls_I hle_ns)
    (fun sit => decide ((act sit).output = none))
  have he_oN := Gates.extends_trans he_ns hoN.2.1; have hle_oN := hle_wf hinds.1 hoN.1 he_oN
  set rOF := Gates.gOrList rON.1 fls
    (pickWires sits rInds.2 fun sit => decide ((act sit).output = some false))
  have hoF := hpick_spec hoN.1 he_oN (lt_of_lt_of_le hfls_I hle_oN)
    (fun sit => decide ((act sit).output = some false))
  have he_oF := Gates.extends_trans he_oN hoF.2.1; have hle_oF := hle_wf hinds.1 hoF.1 he_oF
  set rOT := Gates.gOrList rOF.1 fls
    (pickWires sits rInds.2 fun sit => decide ((act sit).output = some true))
  have hoT := hpick_spec hoF.1 he_oF (lt_of_lt_of_le hfls_I hle_oF)
    (fun sit => decide ((act sit).output = some true))
  have he_oT := Gates.extends_trans he_oF hoT.2.1; have hle_oT := hle_wf hinds.1 hoT.1 he_oT
  have he_0oT := Gates.extends_trans he_I he_oT; have hle_0oT := hle_wf hg hoT.1 he_0oT
  set rOutU := emitOutUpdate rOT.1 (sw.1.1.getD 0 0) rON.2 rOF.2 rOT.2 sw.1.2
  have houtU := emitOutUpdate_spec (ov := oc.outView)
    (aout := match oc.state with
      | none => none
      | some q => (tm.tr q oc.inputTape.head.toOption (fun r =>
        (oc.workTapes r).head.toOption)).output)
    (halted := decide (oc.state = none))
    hoT.1 (lt_of_lt_of_le hsHalt_lt hle_oT)
    (lt_of_lt_of_le hoN.2.2.1 (hle_wf hoN.1 hoT.1 (Gates.extends_trans hoF.2.1 hoT.2.1)))
    (lt_of_lt_of_le hoF.2.2.1 (hle_wf hoF.1 hoT.1 hoT.2.1))
    hoT.2.2.1 henc.2.2.2.2.1 (fun w hw => lt_of_lt_of_le (henc.2.2.2.2.2.1 w hw) hle_0oT)
    (fun o => by
      rw [Gates.val_of_extends_wf hg he_0oT
        (henc.2.2.2.2.2.1 _ (getD_mem_of_lt (by rw [henc.2.2.2.2.1]; exact o.isLt)))]
      exact henc.2.2.2.2.2.2.1 o)
    (by rw [Gates.val_of_extends_wf hg he_0oT (henc.2.1 _ (getD_mem_of_lt (by rw [henc.1]; omega)))]
        exact henc.2.2.1)
    (by rw [Gates.val_of_extends_wf hoN.1 (Gates.extends_trans hoF.2.1 hoT.2.1) hoN.2.2.1,
      hoN.2.2.2.2,
          Gates.val_of_extends_wf hg (Gates.extends_trans he_I he_ns) hfls, hflsV, Bool.false_or]
        cases hst : oc.state <;> simp [act])
    (by rw [Gates.val_of_extends_wf hoF.1 hoT.2.1 hoF.2.2.1, hoF.2.2.2.2,
          Gates.val_of_extends_wf hg (Gates.extends_trans he_I he_oN) hfls, hflsV, Bool.false_or]
        cases hst : oc.state <;> simp [act])
    (by rw [hoT.2.2.2.2, Gates.val_of_extends_wf hg (Gates.extends_trans he_I he_oF) hfls, hflsV,
          Bool.false_or]
        cases hst : oc.state <;> simp [act])
  -- Step 5: Input-tape step + schedule pass
  have he_ou := Gates.extends_trans he_oT houtU.2.1; have hle_ou := hle_wf hinds.1 houtU.1 he_ou
  set rINeg := Gates.gOrList rOutU.1 fls
    (pickWires sits rInds.2
      fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg))
  have hiNeg := hpick_spec houtU.1 he_ou (lt_of_lt_of_le hfls_I hle_ou)
    (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .neg))
  have hiNeg_wf : rINeg.1.WF x.length := hiNeg.1
  have hiNeg_ext : Gates.Extends rOutU.1 rINeg.1 := hiNeg.2.1
  have hiNeg_lt : rINeg.2 < rINeg.1.2 := hiNeg.2.2.1
  have he_iN := Gates.extends_trans he_ou hiNeg_ext; have hle_iN := hle_wf hinds_wf hiNeg_wf he_iN
  set rIZero := Gates.gOrList rINeg.1 (sw.1.1.getD 0 0)
    (pickWires sits rInds.2
      fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero))
  have hiZero := hpick_spec hiNeg_wf he_iN (lt_of_lt_of_le hsHalt_lt hle_iN)
    (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .zero))
  have hiZero_wf : rIZero.1.WF x.length := hiZero.1
  have hiZero_ext : Gates.Extends rINeg.1 rIZero.1 := hiZero.2.1
  have hiZero_lt : rIZero.2 < rIZero.1.2 := hiZero.2.2.1
  have he_iZ := Gates.extends_trans he_iN hiZero_ext; have hle_iZ := hle_wf hinds_wf hiZero_wf he_iZ
  set rIPos := Gates.gOrList rIZero.1 fls
    (pickWires sits rInds.2
      fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos))
  have hiPos := hpick_spec hiZero_wf he_iZ (lt_of_lt_of_le hfls_I hle_iZ)
    (fun sit => decide (ObliviousCfg.clampInputMove sit.2.1 (act sit).inputTape = .pos))
  have hiPos_wf : rIPos.1.WF x.length := hiPos.1
  have hiPos_ext : Gates.Extends rIZero.1 rIPos.1 := hiPos.2.1
  have hiPos_lt : rIPos.2 < rIPos.1.2 := hiPos.2.2.1
  have he_iP := Gates.extends_trans he_iZ hiPos_ext; have hle_iP := hle_wf hinds_wf hiPos_wf he_iP
  have he_0iP := Gates.extends_trans he_I he_iP; have hle_0iP := hle_wf hg hiPos_wf he_0iP
  have hMoveIn_val :
      let mIn : SignType := match oc.state with
        | none => .zero
        | some q => ObliviousCfg.clampInputMove oc.inputTape.head
            (tm.tr q oc.inputTape.head.toOption (fun r => (oc.workTapes r).head.toOption)).inputTape
      rIPos.1.val x rINeg.2 = decide (mIn = .neg) ∧
      rIPos.1.val x rIZero.2 = decide (mIn = .zero) ∧
      rIPos.1.val x rIPos.2 = decide (mIn = .pos) := by
    have hNeg_val : rINeg.1.val x rINeg.2 = _ := hiNeg.2.2.2.2
    have hZero_val : rIZero.1.val x rIZero.2 = _ := hiZero.2.2.2.2
    have hPos_val : rIPos.1.val x rIPos.2 = _ := hiPos.2.2.2.2
    refine ⟨?_, ?_, ?_⟩
    · rw [Gates.val_of_extends_wf hiNeg_wf (Gates.extends_trans hiZero_ext hiPos_ext) hiNeg_lt,
        hNeg_val, Gates.val_of_extends_wf hg (Gates.extends_trans he_I he_ou) hfls, hflsV,
          Bool.false_or]
      cases hst : oc.state <;> simp [act]
    · rw [Gates.val_of_extends_wf hiZero_wf hiPos_ext hiZero_lt, hZero_val,
        Gates.val_of_extends_wf hg (Gates.extends_trans he_I he_iN)
          (henc.2.1 _ (getD_mem_of_lt (by rw [henc.1]; omega))), henc.2.2.1]
      cases hst : oc.state <;> simp [act]
    · rw [hPos_val, Gates.val_of_extends_wf hg (Gates.extends_trans he_I he_iZ) hfls, hflsV,
      Bool.false_or]
      cases hst : oc.state <;> simp [act]
  have hohIn : (rIPos.1.val x rINeg.2 = true ∧ rIPos.1.val x rIZero.2 = false ∧
    rIPos.1.val x rIPos.2 = false) ∨
      (rIPos.1.val x rINeg.2 = false ∧ rIPos.1.val x rIZero.2 = true ∧
        rIPos.1.val x rIPos.2 = false) ∨
      (rIPos.1.val x rINeg.2 = false ∧ rIPos.1.val x rIZero.2 = false ∧
        rIPos.1.val x rIPos.2 = true) := by
    rw [hMoveIn_val.1, hMoveIn_val.2.1, hMoveIn_val.2.2]
    set mIn : SignType := match oc.state with
      | none => .zero
      | some q => ObliviousCfg.clampInputMove oc.inputTape.head
          (tm.tr q oc.inputTape.head.toOption (fun r => (oc.workTapes r).head.toOption)).inputTape
    cases mIn <;> simp
  set rIn0 := emitTapeStep0 rIPos.1 fls rINeg.2 rIZero.2 rIPos.2 sw.2.1.1.1 sw.2.1.1.2 sw.2.1
  have hin0_step := emitTapeStep0_spec hL hiPos_wf (lt_of_lt_of_le hfls hle_0iP)
    (by rw [Gates.val_of_extends_wf hg he_0iP hfls, hflsV])
    (lt_of_lt_of_le hiNeg_lt (hle_wf hiNeg_wf hiPos_wf (Gates.extends_trans hiZero_ext hiPos_ext)))
    (lt_of_lt_of_le hiZero_lt (hle_wf hiZero_wf hiPos_wf hiPos_ext))
    hiPos_lt
    (lt_of_lt_of_le henc.2.2.2.2.2.2.2.1.1 hle_0iP)
    (lt_of_lt_of_le henc.2.2.2.2.2.2.2.1.2.1 hle_0iP)
    (henc.2.2.2.2.2.2.2.1.of_extends hg he_0iP hle_0iP)
    (BlockHalfTape.cnt0_of_inv hL hinvIn.1) (BlockHalfTape.cnt0_of_inv hL hinvIn.2) hohIn
  have he_in0 := Gates.extends_trans he_0iP hin0_step.2.1; have hle_in0 :=
    hle_wf hg hin0_step.1 he_in0
  have hstep0_in := BlockHalfTape.step0_of_inv hL hinvIn.1
  have hstep0_inR := BlockHalfTape.step0_of_inv hL hinvIn.2
  set rInL := emitSchedulePass L fls t rIn0.1 rIn0.2.2.1
  have hinL_step := emitSchedulePass_spec hL hin0_step.1 (lt_of_lt_of_le hfls hle_in0)
    (by rw [Gates.val_of_extends_wf hg he_in0 hfls, hflsV]) hin0_step.2.2.2.2.2.2.1
    (by dsimp only; rcases hohIn with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
        · simp only [h1, ↓reduceIte]; exact hstep0_in.2.1
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstep0_in.2.2
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstep0_in.1 _)
  have he_inL := Gates.extends_trans he_in0 hinL_step.2.1; have hle_inL :=
    hle_wf hg hinL_step.1 he_inL
  set rInR := emitSchedulePass L fls t rInL.1 rIn0.2.2.2
  have hinR_step := emitSchedulePass_spec hL hinL_step.1 (lt_of_lt_of_le hfls hle_inL)
    (by rw [Gates.val_of_extends_wf hg he_inL hfls, hflsV])
    (hin0_step.2.2.2.2.2.2.2.of_extends hin0_step.1 hinL_step.2.1
      (hle_wf hin0_step.1 hinL_step.1 hinL_step.2.1))
    (by dsimp only; rcases hohIn with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
        · simp only [h1, ↓reduceIte]; exact hstep0_inR.1 _
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstep0_inR.2.2
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact hstep0_inR.2.1)
  have he_inR := Gates.extends_trans he_inL hinR_step.2.1
  -- Step 6: Work-tape fold over `List.finRange k`
  have he_start : Gates.Extends rInds.1 rInR.1 :=
    Gates.extends_trans he_iP (Gates.extends_trans hin0_step.2.1
      (Gates.extends_trans hinL_step.2.1 hinR_step.2.1))
  have hwk_fold : ∀ (l : List (Fin k)) (g0 : Gates),
      g0.WF x.length → Gates.Extends rInR.1 g0 →
      let res := l.foldl (fun (acc : Gates × List TapeW) (r : Fin k) =>
        let p := emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) rInds.2
          (sw.2.2.getD r.val defaultTapeW) acc.1 r
        (p.1, p.2 :: acc.2)) (g0, [])
      res.1.WF x.length ∧ Gates.Extends g0 res.1 ∧ res.2.length = l.length ∧
      res.1.1.length =
        g0.1.length + (l.map (workTapeStepCost e tm)).sum + 2 * l.length * schedulePassCost L t ∧
      (∀ (i : ℕ) (hi : i < l.length),
        (res.2.reverse.getD i defaultTapeW).Encodes res.1 x ((oc.step hL tm t).workTapes l[i]))
          := by
    intro l
    induction l with
    | nil =>
      intro g0 hg0 _; exact ⟨hg0, Gates.extends_refl g0, rfl, by simp, fun _ hi => by simp at hi⟩
    | cons r tl ih =>
      intro g0 hg0 hext0
      set p := emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) rInds.2
        (sw.2.2.getD r.val defaultTapeW) g0 r
      have h1 := emitWorkTapeStep_spec e tm hL hg hinds_wf hg0 he_I
        (Gates.extends_trans he_start hext0) hfls hflsV
        (henc.2.1 _ (getD_mem_of_lt (by rw [henc.1]; omega))) henc.2.2.1
        hinds_len hinds_mem hinds_val (hwk0_enc r) (hinvWk r)
      have h1_len : p.1.1.length =
        g0.1.length + workTapeStepCost e tm r + 2 * schedulePassCost L t :=
        h1.2.2.1
      have hfold_app : ∀ (l' : List (Fin k)) (g' : Gates) (acc : List TapeW),
          let q1 := l'.foldl (fun (a : Gates × List TapeW) (r' : Fin k) =>
            let q := emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) rInds.2
              (sw.2.2.getD r'.val defaultTapeW) a.1 r'
            (q.1, q.2 :: a.2)) (g', acc)
          let q0 := l'.foldl (fun (a : Gates × List TapeW) (r' : Fin k) =>
            let q := emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) rInds.2
              (sw.2.2.getD r'.val defaultTapeW) a.1 r'
            (q.1, q.2 :: a.2)) (g', [])
          q1.1 = q0.1 ∧ q1.2 = q0.2 ++ acc := by
        intro l'
        induction l' with
        | nil => intro g' acc; exact ⟨rfl, by simp⟩
        | cons a tl' ih' =>
          intro g' acc; simp only [List.foldl_cons]
          set qa := emitWorkTapeStep e tm L fls t (sw.1.1.getD 0 0) rInds.2
            (sw.2.2.getD a.val defaultTapeW) g' a
          have a1 := ih' qa.1 (qa.2 :: acc)
          have a2 := ih' qa.1 [qa.2]
          exact ⟨a1.1.trans a2.1.symm, by rw [a1.2, a2.2, List.append_assoc, List.singleton_append]⟩
      dsimp only; rw [List.foldl_cons]
      have ha := hfold_app tl p.1 [p.2]
      obtain ⟨hW', hE', hLen', hG', hEnc'⟩ := ih p.1 h1.1 (Gates.extends_trans hext0 h1.2.1)
      rw [ha.1, ha.2]
      refine ⟨hW', Gates.extends_trans h1.2.1 hE',
        by rw [List.length_append, hLen']; simp,
        by rw [hG', h1_len, List.map_cons, List.sum_cons, List.length_cons]; ring, ?_⟩
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
      intro i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        exact h1.2.2.2.of_extends h1.1 hE' (hle_wf h1.1 hW' hE')
      | succ i' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        exact hEnc' i' (by simp at hi; omega)
  obtain ⟨hWfin, hEfin, hLenfin, hGfin, hEncfin⟩ :=
    hwk_fold (List.finRange k) rInR.1 hinR_step.1 (Gates.extends_refl _)
  have he_0fin := Gates.extends_trans he_inR hEfin
  have he_ns_fin := Gates.extends_trans (Gates.extends_trans hoN.2.1 (Gates.extends_trans hoF.2.1
    (Gates.extends_trans hoT.2.1 (Gates.extends_trans houtU.2.1 (Gates.extends_trans hiNeg.2.1
      (Gates.extends_trans hiZero.2.1 (Gates.extends_trans hiPos.2.1
        (Gates.extends_trans hin0_step.2.1
        (Gates.extends_trans hinL_step.2.1 hinR_step.2.1))))))))) hEfin
  have he_ou_fin :=
    Gates.extends_trans (Gates.extends_trans hiNeg.2.1 (Gates.extends_trans hiZero.2.1
    (Gates.extends_trans hiPos.2.1 (Gates.extends_trans hin0_step.2.1
      (Gates.extends_trans hinL_step.2.1
      hinR_step.2.1))))) hEfin
  have hle_ns_fin := hle_wf hnsRest.1 hWfin he_ns_fin
  have hle_ou_fin := hle_wf houtU.1 hWfin he_ou_fin
  have hle_in_fin := hle_wf hinR_step.1 hWfin hEfin
  have hG_inR : rInR.1.1.length = rInL.1.1.length + schedulePassCost L t := hinR_step.2.2.1
  have hG_inL : rInL.1.1.length = rIn0.1.1.length + schedulePassCost L t := hinL_step.2.2.1
  have hG_in0 : rIn0.1.1.length = rIPos.1.1.length + 170 := hin0_step.2.2.1
  have hG_iP : rIPos.1.1.length = rIZero.1.1.length + _ := hiPos.2.2.2.1
  have hG_iZ : rIZero.1.1.length = rINeg.1.1.length + _ := hiZero.2.2.2.1
  have hG_iN : rINeg.1.1.length = rOutU.1.1.length + _ := hiNeg.2.2.2.1
  have hG_oU : rOutU.1.1.length = rOT.1.1.length + 22 := houtU.2.2.1
  have hG_oT : rOT.1.1.length = rOF.1.1.length + _ := hoT.2.2.2.1
  have hG_oF : rOF.1.1.length = rON.1.1.length + _ := hoF.2.2.2.1
  have hG_oN : rON.1.1.length = rNsRest.1.1.length + _ := hoN.2.2.2.1
  have hG_nsR : rNsRest.1.1.length = rNs0.1.1.length + _ := hnsRest.2.2.2.1
  have hG_ns0 : rNs0.1.1.length = rInds.1.1.length + _ := hns0.2.2.2.1
  have hG_inds : rInds.1.1.length = rWkN1.1.1.length + (3 + 2 * k) * sits.length := hinds.2.2.2.1
  have hG_wk1 : rWkN1.1.1.length = rWkN0.1.1.length + 1 * (List.finRange k).length := hwkN1.2.2.2.1
  have hG_wk0 : rWkN0.1.1.length = rN1.1.1.length + 1 * (List.finRange k).length := hwkN0.2.2.2.1
  have hG_n1 : rN1.1.1.length = rN0.1.1.length + 1 := hn1.2.2.2.1
  have hG_n0 : rN0.1.1.length = g.1.length + 1 := hn0.2.2.2.1
  have hLen_nsR : rNsRest.2.length = numStates := hnsRest.2.2.1.trans (List.length_finRange)
  have hns0_wf : rNs0.1.WF x.length := hns0.1
  have hnsRest_wf : rNsRest.1.WF x.length := hnsRest.1
  have houtU_wf : rOutU.1.WF x.length := houtU.1
  have hns0_ext : Gates.Extends rNs0.1 rNsRest.1 := hnsRest.2.1
  have hns0_lt : rNs0.2 < rNs0.1.2 := hns0.2.2.1
  have hns0_val : rNs0.1.val x rNs0.2 = _ := hns0.2.2.2.2
  have hnsRest_mem : ∀ w ∈ rNsRest.2, w < rNsRest.1.2 := hnsRest.2.2.2.2.1
  have hnsRest_val : ∀ (i : ℕ) (hi : i < (List.finRange numStates).length),
      rNsRest.1.val x (rNsRest.2.getD i 0) = _ := hnsRest.2.2.2.2.2
  have houtU_len : rOutU.2.length = 4 := houtU.2.2.2.1
  have houtU_mem : ∀ w ∈ rOutU.2, w < rOutU.1.2 := houtU.2.2.2.2.1
  have houtU_val : ∀ o : Fin 4, rOutU.1.val x (rOutU.2.getD o.val 0) = _ := houtU.2.2.2.2.2
  refine ⟨hWfin, he_0fin, ?_, ?_⟩
  · rw [hGfin, hG_inR, hG_inL, hG_in0, hG_iP, hG_iZ, hG_iN, hG_oU, hG_oT, hG_oF, hG_oN,
      hG_nsR, hG_ns0, hG_inds, hG_wk1, hG_wk0, hG_n1, hG_n0]
    simp only [List.length_finRange]; dsimp only [act, sits]; ring
  · refine ⟨by rw [List.length_cons, hLen_nsR], fun w hw => ?_, ?_, fun q => ?_,
      houtU_len, fun w hw => lt_of_lt_of_le (houtU_mem w hw) hle_ou_fin,
      fun o => ?_, ?_, by rw [List.length_reverse, hLenfin, List.length_finRange], fun r => ?_⟩
    · simp only [List.mem_cons] at hw; rcases hw with rfl | hw
      · exact lt_of_lt_of_le hns0_lt (hle_wf hns0_wf hWfin (Gates.extends_trans hns0_ext he_ns_fin))
      · exact lt_of_lt_of_le (hnsRest_mem w hw) hle_ns_fin
    · rw [List.getD_cons_zero,
        Gates.val_of_extends_wf hns0_wf (Gates.extends_trans hns0_ext he_ns_fin) hns0_lt,
        hns0_val, Gates.val_of_extends_wf hg he_I (henc.2.1 _ (getD_mem_of_lt
          (by rw [henc.1]; omega))),
        henc.2.2.1]
      cases hst : oc.state <;> simp [ObliviousCfg.step_eq, act, hst]
    · rw [List.getD_cons_succ,
        Gates.val_of_extends_wf hnsRest_wf he_ns_fin
          (hnsRest_mem _ (getD_mem_of_lt (by rw [hLen_nsR]; exact q.isLt))),
        hnsRest_val q.val (by simp)]
      simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
    · rw [Gates.val_of_extends_wf houtU_wf he_ou_fin
        (houtU_mem _ (getD_mem_of_lt (by rw [houtU_len]; exact o.isLt))),
        houtU_val o]
      cases hst : oc.state <;> simp [ObliviousCfg.step_eq, hst]
    · let btIn0 : BlockTape L :=
        match (if rIPos.1.val x rINeg.2 then SignType.neg else if rIPos.1.val x rIZero.2 then
          .zero else .pos) with
        | .zero => { head := (rIPos.1.val x sw.2.1.1.1, rIPos.1.val x sw.2.1.1.2), left :=
          oc.inputTape.left,
                     right := oc.inputTape.right }
        | .pos => let p := oc.inputTape.right.pop0 hL
                  { head := p.1,
                    left := oc.inputTape.left.push0 hL (rIPos.1.val x sw.2.1.1.1,
                      rIPos.1.val x sw.2.1.1.2),
                    right := p.2 }
        | .neg => let p := oc.inputTape.left.pop0 hL
                  { head := p.1, left := p.2,
                    right := oc.inputTape.right.push0 hL (rIPos.1.val x sw.2.1.1.1,
                      rIPos.1.val x sw.2.1.1.2) }
      have htw_in : TapeW.Encodes rInR.1 x (rIn0.2.1, (rInL.2, rInR.2))
          { head := btIn0.head, left := btIn0.left.rebalanceSchedule t, right :=
            btIn0.right.rebalanceSchedule t } :=
        ⟨lt_of_lt_of_le hin0_step.2.2.2.1 (hle_wf hin0_step.1 hinR_step.1
          (Gates.extends_trans hinL_step.2.1 hinR_step.2.1)),
         lt_of_lt_of_le hin0_step.2.2.2.2.1 (hle_wf hin0_step.1 hinR_step.1
           (Gates.extends_trans hinL_step.2.1 hinR_step.2.1)),
         by rw [Gates.val_of_extends_wf hin0_step.1
           (Gates.extends_trans hinL_step.2.1 hinR_step.2.1) hin0_step.2.2.2.1,
              Gates.val_of_extends_wf hin0_step.1
                (Gates.extends_trans hinL_step.2.1 hinR_step.2.1) hin0_step.2.2.2.2.1]
            exact hin0_step.2.2.2.2.2.1,
         hinL_step.2.2.2.of_extends hinL_step.1 hinR_step.2.1
           (hle_wf hinL_step.1 hinR_step.1 hinR_step.2.1),
         hinR_step.2.2.2⟩
      have hm_eq :
        (if rIPos.1.val x rINeg.2 then SignType.neg else if rIPos.1.val x rIZero.2 then .zero
          else .pos) =
          match oc.state with
          | none => .zero
          | some q => ObliviousCfg.clampInputMove oc.inputTape.head
              (tm.tr q oc.inputTape.head.toOption (fun r =>
                (oc.workTapes r).head.toOption)).inputTape := by
        rw [hMoveIn_val.1, hMoveIn_val.2.1]
        set mIn : SignType := match oc.state with
          | none => .zero
          | some q => ObliviousCfg.clampInputMove oc.inputTape.head
              (tm.tr q oc.inputTape.head.toOption (fun r =>
                (oc.workTapes r).head.toOption)).inputTape
        cases mIn <;> rfl
      dsimp only [btIn0] at htw_in
      rw [hm_eq, Gates.val_of_extends_wf hg he_0iP henc.2.2.2.2.2.2.2.1.1,
        Gates.val_of_extends_wf hg he_0iP henc.2.2.2.2.2.2.2.1.2.1,
          henc.2.2.2.2.2.2.2.1.2.2.1] at htw_in
      have htw_in' := htw_in.of_extends hinR_step.1 hEfin hle_in_fin
      cases hst : oc.state with
      | none => simpa [ObliviousCfg.step_eq, BlockTape.step_eq, hst] using htw_in'
      | some q =>
        cases hm : ObliviousCfg.clampInputMove oc.inputTape.head
            (tm.tr q oc.inputTape.head.toOption (fun r =>
              (oc.workTapes r).head.toOption)).inputTape <;>
          · simp only [ObliviousCfg.step_eq, BlockTape.step_eq, hst, hm] at htw_in' ⊢
            exact htw_in'
    · have h := hEncfin r.val (by simp)
      have hr_idx : (List.finRange k)[r.val]'(by simp) = r := by simp
      rw [hr_idx] at h
      exact h

/-! ### Full `T`-step gate builder, `O(T log T)` size bound, and evaluation correctness -/

/-- Canonical level count `L := Nat.size (max T N + 2) + 2`, satisfying `0 < L`,
`T < 2 ^ (L - 1)`, `N + 2 < 2 * (2 ^ L - 1)`, and `L ≤ Nat.log 2 (max T N + 2) + 3`. -/
@[expose] def pfLevels (T N : ℕ) : ℕ :=
  Nat.size (max T N + 2) + 2

theorem pfLevels_pos (T N : ℕ) : 0 < pfLevels T N := by
  simp [pfLevels]

theorem pfLevels_step_bound (T N : ℕ) : T < 2 ^ (pfLevels T N - 1) := by
  have h1 : max T N + 2 < 2 ^ Nat.size (max T N + 2) := Nat.lt_size_self _
  have h2 : Nat.size (max T N + 2) ≤ pfLevels T N - 1 := by simp [pfLevels]
  calc T ≤ max T N := le_max_left _ _
    _ < max T N + 2 := by omega
    _ < 2 ^ Nat.size (max T N + 2) := h1
    _ ≤ 2 ^ (pfLevels T N - 1) := Nat.pow_le_pow_right (by norm_num) h2

theorem pfLevels_input_bound (T N : ℕ) : N + 2 < 2 * (2 ^ pfLevels T N - 1) := by
  have h1 : max T N + 2 < 2 ^ Nat.size (max T N + 2) := Nat.lt_size_self _
  have h2 : 2 ^ Nat.size (max T N + 2) ≤ 2 ^ pfLevels T N :=
    Nat.pow_le_pow_right (by norm_num) (by simp [pfLevels])
  have h3 : 1 ≤ 2 ^ pfLevels T N := Nat.one_le_two_pow
  have : N ≤ max T N := le_max_right _ _
  omega

theorem pfLevels_le_log (T N : ℕ) : pfLevels T N ≤ Nat.log 2 (max T N + 2) + 3 := by
  simp [pfLevels, Nat.size_eq_log_two_add_one (show max T N + 2 ≠ 0 by omega)]

/-- Build the full `T`-step oblivious gate list and output wire for `tm` on arbitrary
`inputWires` with `totalInputs` primary inputs. If `negateOut = true`, negates the final
acceptance wire `outW[2]` (`OutView.one true`). -/
@[expose] noncomputable def buildGates {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (totalInputs : ℕ) (inputWires : List ℕ) (T : ℕ) (negateOut : Bool) : Gates × ℕ :=
  let L := pfLevels T inputWires.length
  let g0 := Gates.init totalInputs
  let fls := totalInputs
  let tru := totalInputs + 1
  let sw0 := initStateW L k numStates (e tm.q₀).val fls tru inputWires
  let (gFin, swFin) := (List.range T).foldl
    (fun acc t => emitTmStep e tm L fls tru t acc.1 acc.2) (g0, sw0)
  let outW := swFin.1.2.getD 2 0
  if negateOut then Gates.gNot gFin outW else (gFin, outW)

/-- Arithmetic bound: for every level `lvl`, the number of steps `t < T` with
`(t + 1) % 2 ^ (lvl + 1) = 0` is `T / 2 ^ (lvl + 1)`. -/
private theorem sum_schedulePassCost_le (L T : ℕ) :
    ((List.range T).map (schedulePassCost L)).sum ≤ 247 * T * L := by
  have hswap : ((List.range T).map (schedulePassCost L)).sum =
      ((List.range (L - 1)).map fun lvl =>
        (37 + 210 * 2 ^ lvl) *
          ((List.range T).filter fun t => (t + 1) % 2 ^ (lvl + 1) = 0).length).sum := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton,
        List.sum_singleton]
      simp only [schedulePassCost_eq]
      have hadd : ∀ l : List ℕ, ∀ f g : ℕ → ℕ, (l.map fun i => f i + g i).sum =
          (l.map f).sum + (l.map g).sum := by
        intro l f g; induction l with
        | nil => simp
        | cons a tl iht => simp [iht]; omega
      rw [← hadd]
      congr 1; refine List.map_congr_left fun lvl _ => ?_
      rw [List.filter_append, List.length_append, List.filter_singleton]
      by_cases h : (T + 1) % 2 ^ (lvl + 1) = 0
      · simp only [h, ↓reduceIte, decide_true, Bool.cond_true, List.length_singleton]; ring
      · simp only [h, ↓reduceIte, decide_false, Bool.cond_false, List.length_nil, Nat.add_zero]
  have hcnt : ∀ (d T : ℕ), 0 < d →
      ((List.range T).filter fun t => (t + 1) % d = 0).length ≤ T / d := by
    intro d T hd
    induction T with
    | zero => simp
    | succ T ih =>
      rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton]
      by_cases h : (T + 1) % d = 0
      · simp only [h, decide_true]
        have hdiv : (T + 1) / d = T / d + 1 := by
          rw [Nat.succ_div]; simp [Nat.dvd_of_mod_eq_zero h]
        rw [hdiv]; exact Nat.add_le_add_right ih 1
      · simp only [h, decide_false]
        exact ih.trans (Nat.div_le_div_right (Nat.le_succ T))
  rw [hswap]
  have hterm : ∀ lvl ∈ List.range (L - 1),
      (37 + 210 * 2 ^ lvl) * ((List.range T).filter fun t => (t + 1) % 2 ^ (lvl + 1) = 0).length ≤
        247 * T := by
    intro lvl _
    have hc := hcnt (2 ^ (lvl + 1)) T (by positivity)
    have hmul : 2 ^ lvl * (T / 2 ^ (lvl + 1)) ≤ T := by
      have h1 : 2 ^ (lvl + 1) * (T / 2 ^ (lvl + 1)) ≤ T := Nat.mul_div_le T _
      rw [pow_succ] at h1
      calc 2 ^ lvl * (T / 2 ^ (lvl + 1)) ≤ 2 ^ lvl * 2 * (T / 2 ^ (lvl + 1)) := by
            exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ T := h1
    have hdiv_le : T / 2 ^ (lvl + 1) ≤ T := Nat.div_le_self T _
    calc (37 + 210 * 2 ^ lvl) * ((List.range T).filter fun t => (t + 1) % 2 ^ (lvl + 1) = 0).length
        ≤ (37 + 210 * 2 ^ lvl) * (T / 2 ^ (lvl + 1)) := Nat.mul_le_mul_left _ hc
      _ = 37 * (T / 2 ^ (lvl + 1)) + 210 * (2 ^ lvl * (T / 2 ^ (lvl + 1))) := by ring
      _ ≤ 37 * T + 210 * T :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hdiv_le) (Nat.mul_le_mul_left _ hmul)
      _ = 247 * T := by ring
  have hsum_le_list : ∀ (l : List ℕ) (f : ℕ → ℕ) (c : ℕ), (∀ a ∈ l, f a ≤ c) →
      (l.map f).sum ≤ l.length * c := by
    intro l f c h
    induction l with
    | nil => simp
    | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have h1 := h a List.mem_cons_self
      have h2 := ih fun b hb => h b (List.mem_cons_of_mem a hb)
      omega
  calc ((List.range (L - 1)).map fun lvl =>
          (37 + 210 * 2 ^ lvl) *
            ((List.range T).filter fun t => (t + 1) % 2 ^ (lvl + 1) = 0).length).sum
      ≤ (List.range (L - 1)).length * (247 * T) := hsum_le_list _ _ _ hterm
    _ = (L - 1) * (247 * T) := by simp
    _ ≤ L * (247 * T) := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
    _ = 247 * T * L := by ring

theorem buildGates_spec {k numStates : ℕ} {State : Type} (e : State ≃ Fin numStates)
    (tm : MultiTapeTM k Bool State) (totalInputs T : ℕ) (inputWires : List ℕ) (negateOut : Bool)
    {x : List Bool} (hx : x.length = totalInputs)
    (hin : ∀ w ∈ inputWires, w < totalInputs + 2) :
    let res := buildGates e tm totalInputs inputWires T negateOut
    let input := inputWires.map fun w => (Gates.init totalInputs).val x w
    res.1.WF totalInputs ∧ res.2 < res.1.2 ∧
    res.1.1.length ≤ 3 + T * tmStepBaseCost e tm +
      (2 + 2 * k) * 247 * T * (Nat.log 2 (max T inputWires.length + 2) + 3) ∧
    res.1.val x res.2 =
      if negateOut then !(decide ((tm.runFrom (tm.initCfg input) T).output = [true]))
      else decide ((tm.runFrom (tm.initCfg input) T).output = [true]) := by
  subst hx
  dsimp only [buildGates]
  set L := pfLevels T inputWires.length
  have hL : 0 < L := pfLevels_pos T inputWires.length
  have hT : T < 2 ^ (L - 1) := pfLevels_step_bound T inputWires.length
  set g0 := Gates.init x.length
  set fls := x.length
  set tru := x.length + 1
  have hinit_wf : g0.WF x.length := Gates.init_wf x.length
  have hfls : fls < g0.2 := by simp [g0, fls]
  have htru : tru < g0.2 := by simp [g0, tru]
  have hflsV : g0.val x fls = false := Gates.init_val_fls x
  have htruV : g0.val x tru = true := Gates.init_val_tru x
  have hinit_len : g0.1.length = 2 := rfl
  have hin' : ∀ w ∈ inputWires, w < g0.2 := hin
  set input := inputWires.map (g0.val x)
  have hLN : input.length + 2 < 2 * (2 ^ L - 1) := by
    simpa [input] using pfLevels_input_bound T inputWires.length
  have hsw0 := initStateW_spec (L := L) e tm hfls hflsV htru htruV hin'
  have hfold : ∀ m ≤ T,
      let acc := (List.range m).foldl (fun acc t => emitTmStep e tm L fls tru t acc.1 acc.2)
        (g0, initStateW L k numStates (e tm.q₀).val fls tru inputWires)
      let oc := (List.range m).foldl (fun oc t => oc.step hL tm t) (ObliviousCfg.init L tm input)
      acc.1.WF x.length ∧ Gates.Extends g0 acc.1 ∧
      acc.1.1.length = g0.1.length + m * tmStepBaseCost e tm +
        (2 + 2 * k) * ((List.range m).map (schedulePassCost L)).sum ∧
      StateW.Encodes e acc.1 x acc.2 oc := by
    intro m
    induction m with
    | zero =>
      intro _; exact ⟨hinit_wf, Gates.extends_refl g0, by simp, hsw0⟩
    | succ m ih =>
      intro hm
      obtain ⟨hW, hE, hG, hEnc⟩ := ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      have hagr := ObliviousCfg.run_agrees tm input hL hT hLN m (by omega)
      have hle_m : g0.2 ≤ ((List.range m).foldl
          (fun acc t => emitTmStep e tm L fls tru t acc.1 acc.2)
          (g0, initStateW L k numStates (e tm.q₀).val fls tru inputWires)).1.2 := by
        rcases hE with ⟨rr, hrr⟩; rw [hinit_wf.2, hW.2, hrr, List.length_append]; omega
      have hst := emitTmStep_spec e tm hL hW (lt_of_lt_of_le hfls hle_m)
        (by rw [Gates.val_of_extends_wf hinit_wf hE hfls, hflsV])
        (lt_of_lt_of_le htru hle_m)
        (by rw [Gates.val_of_extends_wf hinit_wf hE htru, htruV])
        hEnc hagr.2.2.1 hagr.2.2.2.2.1
      refine ⟨hst.1, Gates.extends_trans hE hst.2.1, ?_, hst.2.2.2⟩
      rw [hst.2.2.1, hG]; ring
  obtain ⟨hW, hE, hG, hEnc⟩ := hfold T le_rfl
  have hagrT := ObliviousCfg.run_agrees tm input hL hT hLN T le_rfl
  set accT := (List.range T).foldl (fun acc t => emitTmStep e tm L fls tru t acc.1 acc.2)
    (g0, initStateW L k numStates (e tm.q₀).val fls tru inputWires)
  have hout_lt : accT.2.1.2.getD 2 0 < accT.1.2 :=
    hEnc.2.2.2.2.2.1 _ (getD_mem_of_lt (by rw [hEnc.2.2.2.2.1]; omega))
  have hout_val : accT.1.val x (accT.2.1.2.getD 2 0) =
      decide ((tm.runFrom (tm.initCfg input) T).output = [true]) := by
    have hv := hEnc.2.2.2.2.2.2.1 ⟨2, by decide⟩
    dsimp only at hv
    rw [hv, hagrT.2.1, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    have hidx : ∀ ov : OutView, outViewIdx ov = ⟨2, by decide⟩ ↔ ov = .one true := by
      intro ov; cases ov with
      | empty => simp
      | one b => cases b <;> simp
      | many => simp
    rw [hidx, OutView.ofList_eq_one_iff]
  have hsum_le := sum_schedulePassCost_le L T
  have hL_le : L ≤ Nat.log 2 (max T inputWires.length + 2) + 3 :=
    pfLevels_le_log T inputWires.length
  have hlen_bound : accT.1.1.length + 1 ≤ 3 + T * tmStepBaseCost e tm +
      (2 + 2 * k) * 247 * T * (Nat.log 2 (max T inputWires.length + 2) + 3) := by
    have h1 : (2 + 2 * k) * ((List.range T).map (schedulePassCost L)).sum ≤
        (2 + 2 * k) * (247 * T * L) := Nat.mul_le_mul_left _ hsum_le
    have h2 : (2 + 2 * k) * (247 * T * L) ≤
        (2 + 2 * k) * (247 * T * (Nat.log 2 (max T inputWires.length + 2) + 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL_le)
    rw [hG, hinit_len]
    nlinarith
  cases negateOut
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨hW, hout_lt, by omega, hout_val⟩
  · simp only [↓reduceIte]
    have hn := Gates.gNot_spec hW hout_lt
    exact ⟨hn.1, hn.2.2.1, by rw [hn.2.2.2.1]; omega, by rw [hn.2.2.2.2, hout_val]⟩

/-- The `O(T log T)` oblivious De Morgan Boolean circuit on `totalInputs` primary inputs
simulating `tm` for `T` steps on `inputWires` (with optional output negation). -/
@[expose] noncomputable def obliviousCircuitWithWires {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (totalInputs : ℕ) (inputWires : List ℕ) (T : ℕ) (negateOut : Bool)
    (hin : ∀ w ∈ inputWires, w < totalInputs + 2) :
    Circuit Boolean.signature totalInputs 1 :=
  let res := buildGates e tm totalInputs inputWires T negateOut
  let code : List (Boolean.Op × List ℕ) × List ℕ := (res.1.1.reverse, [res.2])
  have hsome : (Circuit.ofCode totalInputs 1 code :
    Option (Circuit Boolean.signature totalInputs 1)).isSome := by
    have hspec := buildGates_spec e tm totalInputs T inputWires negateOut
      (x := List.replicate totalInputs false) (by simp) hin
    rw [Circuit.isSome_ofCode_iff]
    refine ⟨hspec.1.1, rfl, fun i hi => ?_⟩
    simp only [code, List.mem_singleton] at hi; subst hi
    rw [List.length_reverse, ← hspec.1.2]
    exact hspec.2.1
  (Circuit.ofCode totalInputs 1 code).get hsome

theorem code_obliviousCircuitWithWires {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (totalInputs : ℕ) (inputWires : List ℕ) (T : ℕ) (negateOut : Bool)
    (hin : ∀ w ∈ inputWires, w < totalInputs + 2) :
    (obliviousCircuitWithWires e tm totalInputs inputWires T negateOut hin).code =
      ((buildGates e tm totalInputs inputWires T negateOut).1.1.reverse,
       [(buildGates e tm totalInputs inputWires T negateOut).2]) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

theorem size_obliviousCircuitWithWires_le {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (totalInputs : ℕ) (inputWires : List ℕ) (T : ℕ) (negateOut : Bool)
    (hin : ∀ w ∈ inputWires, w < totalInputs + 2) :
    (obliviousCircuitWithWires e tm totalInputs inputWires T negateOut hin).size ≤
      3 + T * tmStepBaseCost e tm +
        (2 + 2 * k) * 247 * T * (Nat.log 2 (max T inputWires.length + 2) + 3) := by
  have hlen := (buildGates_spec e tm totalInputs T inputWires negateOut
    (x := List.replicate totalInputs false) (by simp) hin).2.2.1
  rw [← Circuit.length_code_fst, code_obliviousCircuitWithWires, List.length_reverse]
  exact hlen

theorem eval_obliviousCircuitWithWires {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (totalInputs : ℕ) (inputWires : List ℕ) (T : ℕ) (negateOut : Bool)
    (hin : ∀ w ∈ inputWires, w < totalInputs + 2) (x : Fin totalInputs → Bool) :
    let input := inputWires.map fun w => (Gates.init totalInputs).val (List.ofFn x) w
    (obliviousCircuitWithWires e tm totalInputs inputWires T negateOut hin).eval
      Boolean.interpretation x 0 =
      if negateOut then !(decide ((tm.runFrom (tm.initCfg input) T).output = [true]))
      else decide ((tm.runFrom (tm.initCfg input) T).output = [true]) := by
  have hspec := buildGates_spec e tm totalInputs T inputWires negateOut
    (x := List.ofFn x) (by simp) hin
  rw [Circuit.eval_eq_evalOutput, code_obliviousCircuitWithWires]
  have hout :
    ((obliviousCircuitWithWires e tm totalInputs inputWires T negateOut hin).outputs 0).toNat =
      (buildGates e tm totalInputs inputWires T negateOut).2 := by
    have hc := code_obliviousCircuitWithWires e tm totalInputs inputWires T negateOut hin
    have h2 := congrArg Prod.snd hc
    simp only [Circuit.code, List.ofFn_succ, Fin.isValue, List.ofFn_zero] at h2
    exact List.cons.inj h2 |>.1
  rw [hout]
  exact hspec.2.2.2

theorem pfLevels_eq (T N : ℕ) :
    pfLevels T N = Nat.size (max T N + 2) + 2 := rfl

/-- Lower bound `2 ≤ pfLevels T N`. -/
@[simp] theorem two_le_pfLevels (T N : ℕ) : 2 ≤ pfLevels T N := by
  rw [pfLevels_eq]; omega

theorem buildGates_eq {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State)
    (totalInputs : ℕ) (inputWires : List ℕ) (T : ℕ) (negateOut : Bool) :
    buildGates e tm totalInputs inputWires T negateOut =
      let L := pfLevels T inputWires.length
      let g0 := Gates.init totalInputs
      let fls := totalInputs
      let tru := totalInputs + 1
      let sw0 := initStateW L k numStates (e tm.q₀).val fls tru inputWires
      let (gFin, swFin) := (List.range T).foldl
        (fun acc t => emitTmStep e tm L fls tru t acc.1 acc.2) (g0, sw0)
      let outW := swFin.1.2.getD 2 0
      if negateOut then Gates.gNot gFin outW else (gFin, outW) := rfl

end CslibFrontier.Computability.Circuit.Oblivious

