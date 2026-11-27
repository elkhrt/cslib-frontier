module

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Circuit.NondeterministicCircuit
public import CslibFrontier.Computability.Circuit.ObliviousStep
public import CslibFrontier.Computability.Circuit.ObliviousSchedulePoly
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Uniformity of Pippenger–Fischer Oblivious Circuits

This module proves polynomial-time computability of the Pippenger–Fischer $O(T \log T)$ oblivious
Boolean circuit builder `buildGates`, and derives two main `P`-uniform circuit theorems:

1. `exists_oblivious_uniform_circuits`: any deterministic multi-tape Turing machine running in
   polynomial-time computable time $T(n)$ admits a `P`-uniform De Morgan circuit family of size
   $O(T(n) \log(\max(T(n), n) + 2))$.
2. `exists_coNSIZE_ignore_circuits_of_mem_NTIME`: every language $L \in \mathrm{NTIME}(t)$ with
   polynomial-time computable $t$ admits a `P`-uniform map $(x, 1^m) \mapsto D_{x, m}$ producing
   co-nondeterministic witness circuits of primary arity $m$ and size
   $O((t(|x|) + |x| + 1) \log(t(|x|) + |x| + 2))$ (independent of $m$) deciding $x \notin L$.

## Main results

* `CslibFrontier.Computability.Circuit.Oblivious.computableInPolyTime_buildGates`: polynomial-time
  computability of `buildGates` on well-formed `inputWires`.
* `CslibFrontier.Computability.Circuit.Oblivious.exists_oblivious_uniform_circuits`: `P`-uniform
  $O(T \log(\max(T, N) + 2))$ oblivious circuit simulation.
* `CslibFrontier.Computability.Circuit.Oblivious.exists_coNSIZE_ignore_circuits_of_mem_NTIME`:
  `P`-uniform co-nondeterministic witness circuits ignoring primary inputs for $\mathrm{NTIME}(t)$.
-/

public section

namespace CslibFrontier.Computability.Circuit.Oblivious

open Turing MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open CslibFrontier.Computability.Circuit

/-! ### `initStateW` uniformity with unary capacity cap -/

private def initHalfConstWCap (cap L fls tru w0 w1 : ℕ) : HalfW :=
  (List.range L).map fun i =>
    ([fls, fls, tru, fls, fls, fls],
      List.replicate (min cap (2 ^ i)) [w0, w1, w0, w1, w0, w1, w0, w1, w0, w1])

private def initHalfFromWCap (cap L fls tru : ℕ) (cells : List (ℕ × ℕ)) (def0 def1 : ℕ) : HalfW :=
  (List.range L).map fun i =>
    let B := min cap (2 ^ i)
    let off := 2 * (B - 1)
    ([fls, fls, tru, fls, fls, fls],
      (List.range B).map fun j =>
        let c0 := cells.getD (off + j) (def0, def1)
        let c1 := cells.getD (off + B + j) (def0, def1)
        let c2 := cells.getD (off + 2 * B + j) (def0, def1)
        let c3 := cells.getD (off + 3 * B + j) (def0, def1)
        let c4 := cells.getD (off + 4 * B + j) (def0, def1)
        [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2])

private theorem initHalfConstWCap_eq {cap L fls tru w0 w1 : ℕ} (hcap : 2 ^ (L - 1) ≤ cap) :
    initHalfConstWCap cap L fls tru w0 w1 = initHalfConstW L fls tru w0 w1 := by
  simp only [initHalfConstWCap, initHalfConstW_eq]
  refine List.map_congr_left fun i hi => ?_
  have hiL : i < L := List.mem_range.mp hi
  rw [Nat.min_eq_right ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hcap)]

private theorem initHalfFromWCap_eq {cap L fls tru : ℕ} {cells : List (ℕ × ℕ)} {def0 def1 : ℕ}
    (hcap : 2 ^ (L - 1) ≤ cap) :
    initHalfFromWCap cap L fls tru cells def0 def1 = initHalfFromW L fls tru cells def0 def1 := by
  simp only [initHalfFromWCap, initHalfFromW_eq]
  refine List.map_congr_left fun i hi => ?_
  have hiL : i < L := List.mem_range.mp hi
  have hmin : min cap (2 ^ i) = 2 ^ i :=
    Nat.min_eq_right ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hcap)
  rw [hmin]

private theorem poly_initHalfConstWCap :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) =>
        initHalfConstWCap p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary encUnary)
        (encPair (encPair encNat encNat) (encPair encNat encNat)))
      encHalfW := by
  set P := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))
  set encP : P ↪ List Bool :=
    encPair (encPair encUnary encUnary) (encPair (encPair encNat encNat) (encPair encNat encNat))
  have hcap := poly_fst (ComputableInPolyTime.fst (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encPair encNat encNat)))
  have hL := poly_snd (ComputableInPolyTime.fst (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encPair encNat encNat)))
  have hfls := poly_fst (poly_fst (ComputableInPolyTime.snd (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encPair encNat encNat))))
  have htru := poly_snd (poly_fst (ComputableInPolyTime.snd (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encPair encNat encNat))))
  have hw0 := poly_fst (poly_snd (ComputableInPolyTime.snd (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encPair encNat encNat))))
  have hw1 := poly_snd (poly_snd (ComputableInPolyTime.snd (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encPair encNat encNat))))
  have hcnt := poly_cons' hfls (poly_cons' hfls (poly_cons' htru
    (poly_cons' hfls (poly_cons' hfls (poly_cons' hfls (ComputableInPolyTime.const []))))))
  have hrow := poly_cons' hw0 (poly_cons' hw1 (poly_cons' hw0 (poly_cons' hw1
    (poly_cons' hw0 (poly_cons' hw1 (poly_cons' hw0 (poly_cons' hw1
      (poly_cons' hw0 (poly_cons' hw1 (ComputableInPolyTime.const []))))))))))
  unfold initHalfConstWCap
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp' hL) ?_
  have qI := ComputableInPolyTime.snd encP encUnary
  exact (poly_comp_fst hcnt).prod
    (ComputableInPolyTime.replicate
      (ComputableInPolyTime.binary_min_unary' (poly_comp_fst hcap)
        (ComputableInPolyTime.binary_two_pow.comp' qI))
      (poly_comp_fst hrow))

private theorem poly_initHalfFromWCap :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (List (ℕ × ℕ) × (ℕ × ℕ)) =>
        initHalfFromWCap p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair (encPair encUnary encUnary) (encPair encNat encNat))
        (encPair (encList (encPair encNat encNat)) (encPair encNat encNat)))
      encHalfW := by
  set P := ((ℕ × ℕ) × (ℕ × ℕ)) × (List (ℕ × ℕ) × (ℕ × ℕ))
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair encUnary encUnary) (encPair encNat encNat))
      (encPair (encList (encPair encNat encNat)) (encPair encNat encNat))
  have h1 := ComputableInPolyTime.fst (encPair (encPair encUnary encUnary) (encPair encNat encNat))
    (encPair (encList (encPair encNat encNat)) (encPair encNat encNat))
  have h2 := ComputableInPolyTime.snd (encPair (encPair encUnary encUnary) (encPair encNat encNat))
    (encPair (encList (encPair encNat encNat)) (encPair encNat encNat))
  have hcap := poly_fst (poly_fst h1)
  have hL := poly_snd (poly_fst h1)
  have hfls := poly_fst (poly_snd h1)
  have htru := poly_snd (poly_snd h1)
  have hcells := poly_fst h2
  have hdef := poly_snd h2
  have hcnt := poly_cons' hfls (poly_cons' hfls (poly_cons' htru
    (poly_cons' hfls (poly_cons' hfls (poly_cons' hfls (ComputableInPolyTime.const []))))))
  unfold initHalfFromWCap
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp' hL) ?_
  set Q := P × ℕ
  set encQ : Q ↪ List Bool := encPair encP encUnary
  have qI := ComputableInPolyTime.snd encP encUnary
  have qB : ComputableInPolyTime (fun q : Q => min q.1.1.1.1 (2 ^ q.2)) encQ encUnary :=
    ComputableInPolyTime.binary_min_unary' (poly_comp_fst hcap)
      (ComputableInPolyTime.binary_two_pow.comp' qI)
  have hrows : ComputableInPolyTime
      (fun q : Q =>
        let B := min q.1.1.1.1 (2 ^ q.2)
        let off := 2 * (B - 1)
        (List.range B).map fun j =>
          let c0 := q.1.2.1.getD (off + j) q.1.2.2
          let c1 := q.1.2.1.getD (off + B + j) q.1.2.2
          let c2 := q.1.2.1.getD (off + 2 * B + j) q.1.2.2
          let c3 := q.1.2.1.getD (off + 3 * B + j) q.1.2.2
          let c4 := q.1.2.1.getD (off + 4 * B + j) q.1.2.2
          [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2])
      encQ (encList (encList encNat)) := by
    refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp' qB) ?_
    set R := Q × ℕ
    set encR : R ↪ List Bool := encPair encQ encUnary
    have rJ := ComputableInPolyTime.snd encQ encUnary
    have rB : ComputableInPolyTime (fun r : R => min r.1.1.1.1.1 (2 ^ r.1.2)) encR encUnary :=
      poly_comp_fst qB
    have rOff := ComputableInPolyTime.unary_mul.comp'
      ((ComputableInPolyTime.const 2).prod
        (ComputableInPolyTime.unary_sub.comp' (rB.prod (ComputableInPolyTime.const 1))))
    have rCells : ComputableInPolyTime (fun r : R => r.1.1.2.1) encR
        (encList (encPair encNat encNat)) := poly_comp_fst (poly_comp_fst hcells)
    have rDef : ComputableInPolyTime (fun r : R => r.1.1.2.2) encR (encPair encNat encNat) :=
      poly_comp_fst (poly_comp_fst hdef)
    have hcell : ∀ (k : ℕ), ComputableInPolyTime
        (fun r : R =>
          let B := min r.1.1.1.1.1 (2 ^ r.1.2)
          let off := 2 * (B - 1)
          r.1.1.2.1.getD (off + k * B + r.2) r.1.1.2.2)
        encR (encPair encNat encNat) := by
      intro k
      have hkB := ComputableInPolyTime.unary_mul.comp' ((ComputableInPolyTime.const k).prod rB)
      have hidx := ComputableInPolyTime.unary_add.comp'
        ((ComputableInPolyTime.unary_add.comp' (rOff.prod hkB)).prod rJ)
      have hget := (ComputableInPolyTime.listGetD (encA := encPair encNat encNat) (0, 0)).comp'
        (rCells.prod hidx)
      have hlt := ComputableInPolyTime.unary_lt' hidx
        ((ComputableInPolyTime.length (encPair encNat encNat)).comp' rCells)
      refine (ComputableInPolyTime.ite_decide hlt hget rDef).of_enc_eq fun r => congrArg _ ?_
      by_cases h : 2 * (min r.1.1.1.1.1 (2 ^ r.1.2) - 1) + k * min r.1.1.1.1.1 (2 ^ r.1.2) + r.2 <
          r.1.1.2.1.length
      · simp only [h, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        rfl
      · simp only [h, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    have hc0 : ComputableInPolyTime (fun r : R =>
        r.1.1.2.1.getD (2 * (min r.1.1.1.1.1 (2 ^ r.1.2) - 1) + r.2) r.1.1.2.2)
        encR (encPair encNat encNat) := by simpa using hcell 0
    have hc1 : ComputableInPolyTime (fun r : R =>
        r.1.1.2.1.getD (2 * (min r.1.1.1.1.1 (2 ^ r.1.2) - 1) + min r.1.1.1.1.1 (2 ^ r.1.2) + r.2)
          r.1.1.2.2) encR (encPair encNat encNat) := by simpa [Nat.one_mul] using hcell 1
    have hc2 := hcell 2; have hc3 := hcell 3; have hc4 := hcell 4
    exact (poly_cons' (poly_fst hc0) (poly_cons' (poly_snd hc0)
      (poly_cons' (poly_fst hc1) (poly_cons' (poly_snd hc1)
      (poly_cons' (poly_fst hc2) (poly_cons' (poly_snd hc2)
      (poly_cons' (poly_fst hc3) (poly_cons' (poly_snd hc3)
      (poly_cons' (poly_fst hc4) (poly_cons' (poly_snd hc4)
        (ComputableInPolyTime.const []))))))))))).of_enc_eq fun _ => rfl
  exact ((poly_comp_fst hcnt).prod hrows).of_enc_eq fun _ => rfl

/-! ### Agreement of `safeBuildGates` with `buildGates` and `computableInPolyTime_buildGates` -/

private theorem safeSchedulePass_eq_of_shape {L fls t : ℕ} {g : Gates} {hw : HalfW}
    (hL : 0 < L) (hlen : hw.length = L)
    (hrows : ∀ i : Fin L, (hw.getD i.val ([], [])).2.length = 2 ^ i.val) :
    safeSchedulePass L fls t g hw = emitSchedulePass L fls t g hw := by
  suffices ∀ (m : ℕ), m ≤ L - 1 →
      (List.range m).foldl (safeRebalanceStep fls t) (g, hw) =
        (List.range m).foldl (fun acc lvl =>
          if (t + 1) % 2 ^ (lvl + 1) = 0 then emitRebalanceHalfTape acc.1 fls acc.2 lvl
          else acc) (g, hw) ∧
      let res := (List.range m).foldl (safeRebalanceStep fls t) (g, hw)
      res.2.length = L ∧ ∀ i : Fin L, (res.2.getD i.val ([], [])).2.length = 2 ^ i.val by
    exact (this (L - 1) le_rfl).1
  intro m; induction m with
  | zero => exact fun _ => ⟨rfl, hlen, hrows⟩
  | succ m ih =>
    intro hm
    obtain ⟨heq, hl, hr⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ← heq]
    set acc := (List.range m).foldl (safeRebalanceStep fls t) (g, hw)
    have hlt1 : m + 1 < acc.2.length := by rw [hl]; omega
    have hrow : (acc.2.getD (m + 1) ([], [])).2.length = 2 * (acc.2.getD m ([], [])).2.length := by
      have h1 := hr ⟨m + 1, by omega⟩; have h0 := hr ⟨m, by omega⟩
      dsimp only at h1 h0; rw [h1, h0, pow_succ]; ring
    dsimp only [safeRebalanceStep_eq]
    by_cases hdiv : (t + 1) % 2 ^ (m + 1) = 0
    · simp only [hdiv, hlt1, hrow, and_self, ↓reduceIte]
      have hrb := emitRebalanceLevel_row_lengths acc.1 fls
        (acc.2.getD m ([], [])) (acc.2.getD (m + 1) ([], []))
      have hrm : (acc.2.getD m ([], [])).2.length = 2 ^ m := hr ⟨m, by omega⟩
      refine ⟨trivial, by simp [emitRebalanceHalfTape_eq, hl]; omega, fun i => ?_⟩
      dsimp only [emitRebalanceHalfTape_eq]
      rw [getD_take_two_drop acc.2 _ _ m i.val ([], []) (by rw [hl]; omega)]
      by_cases h1 : i.val = m
      · simp only [h1, ↓reduceIte]; rw [hrb.2.2.1, hrm]
      · by_cases h2 : i.val = m + 1
        · have hne : m + 1 ≠ m := by omega
          simp only [h2, hne, ↓reduceIte]; rw [hrb.2.2.2.1, hrm, pow_succ]; ring
        · simp only [h1, h2, ↓reduceIte]; exact hr i
    · simp only [hdiv, false_and, ↓reduceIte]; exact ⟨trivial, hl, hr⟩

private theorem safeTmStep_eq_of_encodes {k L numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) (hL : 0 < L)
    {x : List Bool} {g : Gates} {fls tru t : ℕ} {sw : StateW} {oc : ObliviousCfg k L State}
    (henc : StateW.Encodes e g x sw oc) :
    safeTmStep e tm L fls tru t g sw = emitTmStep e tm L fls tru t g sw := by
  have hstep0_pass : ∀ {ga : Gates} {mN mZ mP w0 w1 : ℕ} {tw : TapeW} {bt : BlockTape L},
      tw.Encodes g x bt →
      let t0 := emitTapeStep0 ga fls mN mZ mP w0 w1 tw
      safeDoubleSchedule L fls t t0.1 t0.2 =
        let rL := emitSchedulePass L fls t t0.1 t0.2.2.1
        let rR := emitSchedulePass L fls t rL.1 t0.2.2.2
        (rR.1, (t0.2.1, (rL.2, rR.2))) := by
    intro ga mN mZ mP w0 w1 tw bt htw
    have hshape :
        (emitTapeStep0 ga fls mN mZ mP w0 w1 tw).2.2.1.length = L ∧
        (∀ i : Fin L,
          ((emitTapeStep0 ga fls mN mZ mP w0 w1 tw).2.2.1.getD i.val ([], [])).2.length =
          2 ^ i.val) ∧
        (emitTapeStep0 ga fls mN mZ mP w0 w1 tw).2.2.2.length = L ∧
        (∀ i : Fin L,
          ((emitTapeStep0 ga fls mN mZ mP w0 w1 tw).2.2.2.getD i.val ([], [])).2.length =
          2 ^ i.val) := by
      rw [emitTapeStep0_eq]
      refine ⟨by simp [htw.2.2.2.1.1]; omega, fun i => ?_, by simp [htw.2.2.2.2.1]; omega,
        fun i => ?_⟩
      · cases hi : i.val with
        | zero => simp [emitShiftLevel0_eq, emitMap_eq]
        | succ j =>
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_cons_succ, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
          simpa [hi, Nat.add_comm] using (htw.2.2.2.1.2 ⟨1 + j, by omega⟩).1.2.2.1
      · cases hi : i.val with
        | zero => simp [emitShiftLevel0_eq, emitMap_eq]
        | succ j =>
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_cons_succ, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
          simpa [hi, Nat.add_comm] using (htw.2.2.2.2.2 ⟨1 + j, by omega⟩).1.2.2.1
    change let t0 := emitTapeStep0 ga fls mN mZ mP w0 w1 tw
      let rL := safeSchedulePass L fls t t0.1 t0.2.2.1
      let rR := safeSchedulePass L fls t rL.1 t0.2.2.2
      (rR.1, (t0.2.1, (rL.2, rR.2))) = _
    dsimp only
    rw [safeSchedulePass_eq_of_shape hL hshape.1 hshape.2.1,
        safeSchedulePass_eq_of_shape hL hshape.2.2.1 hshape.2.2.2]
  exact safeTmStep_eq_emitTmStep_of_pass e tm
    (fun _ _ _ _ _ _ => hstep0_pass henc.2.2.2.2.2.2.2.1)
    (fun r _ _ _ _ _ _ => hstep0_pass (henc.2.2.2.2.2.2.2.2.2 r))

private theorem isCodeFrom_gate_bounds {N k : ℕ} {code : List (Boolean.Op × List ℕ)}
    (h : Program.IsCodeFrom Boolean.signature N k code) :
    ∀ gt ∈ code, gt.2.length ≤ 2 ∧ ∀ w ∈ gt.2, w < N + k + code.length := by
  induction code generalizing k with
  | nil => intro _ hg; simp at hg
  | cons gt tl ih =>
    rw [Program.isCodeFrom_cons] at h
    intro g' hg'; simp only [List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · refine ⟨?_, fun w hw => lt_of_lt_of_le (h.1.2 w hw) (by simp)⟩
      rw [h.1.1]; cases g'.1 <;> simp
    · obtain ⟨hlen, hw⟩ := ih h.2 g' hg'
      exact ⟨hlen, fun w hw' => lt_of_lt_of_le (hw w hw') (by simp; omega)⟩

private theorem length_encStateW_of_encodes {k L numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) {x : List Bool} {g : Gates} {sw : StateW}
    {oc : ObliviousCfg k L State} {W : ℕ}
    (henc : StateW.Encodes e g x sw oc) (hW : ∀ w < g.2, (encNat w).length ≤ W) :
    let Rows := 2 ^ L
    let Lev := 2 * (6 * (2 * W + 1)) + 1 + Rows * (2 * (10 * (2 * W + 1)) + 1)
    let Hw := L * (2 * Lev + 1)
    let Tw := 2 * (2 * W + 1 + W) + 1 + (2 * Hw + 1 + Hw)
    (encStateW sw).length ≤
      2 * (2 * ((numStates + 1) * (2 * W + 1)) + 1 + 4 * (2 * W + 1)) + 1 +
        (2 * Tw + 1 + k * (2 * Tw + 1)) := by
  have hHalf : ∀ {hw : HalfW} {ht : BlockHalfTape L}, hw.Encodes g x ht →
      (encHalfW hw).length ≤ L * (2 * (2 * (6 * (2 * W + 1)) + 1 +
        2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) + 1) := by
    intro hw ht hh
    refine (length_encList_le encLevelW hw fun lv hlv => ?_).trans
      (Nat.mul_le_mul_right _ (by rw [hh.1]))
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hlv
    have hiL : i < L := by rw [hh.1] at hi; exact hi
    have hlvE := hh.2 ⟨i, hiL⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hlvE
    exact length_encLevelW_le hlvE.1.1.le (fun w hw => hW w (hlvE.1.2.1 w hw))
      (hlvE.1.2.2.1.le.trans (Nat.pow_le_pow_right (by norm_num) hiL.le))
      (fun r hr => ⟨(hlvE.1.2.2.2 r hr).1.le, fun w hw => hW w ((hlvE.1.2.2.2 r hr).2 w hw)⟩)
  have hTape : ∀ {tw : TapeW} {bt : BlockTape L}, tw.Encodes g x bt →
      (encTapeW tw).length ≤ 2 * (2 * W + 1 + W) + 1 +
        (2 * (L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) + 1)) +
          1 +
          L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) + 1)) := by
    intro tw bt ht
    change (encPair (encPair encNat encNat) (encPair encHalfW encHalfW) tw).length ≤ _
    simp only [length_encPair]
    have h1 := hW _ ht.1; have h2 := hW _ ht.2.1
    have hL := hHalf ht.2.2.2.1; have hR := hHalf ht.2.2.2.2
    omega
  change (encPair (encPair (encList encNat) (encList encNat))
    (encPair encTapeW (encList encTapeW)) sw).length ≤ _
  simp only [length_encPair]
  have hs1 : (encList encNat sw.1.1).length ≤ (numStates + 1) * (2 * W + 1) :=
    (length_encList_le encNat sw.1.1 fun w hw => hW w (henc.2.1 w hw)).trans
      (Nat.mul_le_mul_right _ henc.1.le)
  have hs2 : (encList encNat sw.1.2).length ≤ 4 * (2 * W + 1) :=
    (length_encList_le encNat sw.1.2 fun w hw => hW w (henc.2.2.2.2.2.1 w hw)).trans
      (Nat.mul_le_mul_right _ henc.2.2.2.2.1.le)
  have hIn := hTape henc.2.2.2.2.2.2.2.1
  have hWk : (encList encTapeW sw.2.2).length ≤ k * (2 * (2 * (2 * W + 1 + W) + 1 +
      (2 * (L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) + 1)) + 1 +
        L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) + 1))) +
          1) := by
    refine (length_encList_le encTapeW sw.2.2 fun tw htw => ?_).trans
      (Nat.mul_le_mul_right _ henc.2.2.2.2.2.2.2.2.1.le)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htw
    have hiK : i < k := by rw [henc.2.2.2.2.2.2.2.2.1] at hi; exact hi
    have htwE := henc.2.2.2.2.2.2.2.2.2 ⟨i, hiK⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at htwE
    exact hTape htwE
  omega

theorem computableInPolyTime_buildGates {k numStates : ℕ} {State : Type}
    (e : State ≃ Fin numStates) (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime
      (fun p : ((ℕ × List ℕ) × ℕ) × Bool =>
        if p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) then
          buildGates e tm p.1.1.1 p.1.1.2 p.1.2 p.2
        else (Gates.init 0, 0))
      (encPair (encPair (encPair encNat (encList encNat)) encUnary) encBool)
      (encPair encGates encNat) := by
  set P := ((ℕ × List ℕ) × ℕ) × Bool
  set encP : P ↪ List Bool :=
    encPair (encPair (encPair encNat (encList encNat)) encUnary) encBool
  have htot : ComputableInPolyTime (fun p : P => p.1.1.1) encP encNat :=
    poly_fst (poly_fst (ComputableInPolyTime.fst _ _))
  have hinW : ComputableInPolyTime (fun p : P => p.1.1.2) encP (encList encNat) :=
    poly_snd (poly_fst (ComputableInPolyTime.fst _ _))
  have hT : ComputableInPolyTime (fun p : P => p.1.2) encP encUnary :=
    poly_snd (ComputableInPolyTime.fst _ _)
  have hneg : ComputableInPolyTime (fun p : P => p.2) encP encBool :=
    ComputableInPolyTime.snd _ encBool
  have hvalid : ComputableInPolyTime
      (fun p : P => p.1.1.2.all fun w => decide (w < p.1.1.1 + 2)) encP encBool :=
    ComputableInPolyTime.allWithInput hinW
      (ComputableInPolyTime.binary_lt' (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.binary_add' (poly_comp_fst htot)
          (ComputableInPolyTime.const 2)))
  have hvalidDec : ComputableInPolyTime
      (fun p : P => decide (p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) = true)) encP encBool :=
    hvalid.of_enc_eq fun p => congrArg encBool (by
      cases p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) <;> rfl)
  have hN := (ComputableInPolyTime.length encNat).comp' hinW
  have hM2 := ComputableInPolyTime.unary_add.comp'
    ((ComputableInPolyTime.unary_max.comp' (hT.prod hN)).prod (ComputableInPolyTime.const 2))
  have hL : ComputableInPolyTime (fun p : P => pfLevels p.1.2 p.1.1.2.length) encP encUnary :=
    ComputableInPolyTime.unary_add.comp'
      ((ComputableInPolyTime.binary_size.comp'
        (ComputableInPolyTime.unary_to_binary.comp' hM2)).prod
        (ComputableInPolyTime.const 2))
  have hcap := ComputableInPolyTime.unary_mul.comp' ((ComputableInPolyTime.const 4).prod hM2)
  have htru := ComputableInPolyTime.binary_add' htot (ComputableInPolyTime.const 1)
  have hg0 : ComputableInPolyTime (fun p : P => Gates.init p.1.1.1) encP encGates :=
    (ComputableInPolyTime.const [(Boolean.Op.const true, []), (Boolean.Op.const false, [])]).prod
      (ComputableInPolyTime.binary_add' htot (ComputableInPolyTime.const 2))
  have hisEmptyDec : ComputableInPolyTime (fun p : P => decide (p.1.1.2.isEmpty =
    true)) encP encBool :=
    ((ComputableInPolyTime.listIsEmpty' encNat).comp' hinW).of_enc_eq
      fun p => congrArg encBool (by cases p.1.1.2 <;> rfl)
  have hinHead : ComputableInPolyTime
      (fun p : P =>
        if p.1.1.2.isEmpty then (p.1.1.1, p.1.1.1 + 1) else (p.1.1.1 + 1, p.1.1.2.headD 0))
      encP (encPair encNat encNat) :=
    (ComputableInPolyTime.ite_decide hisEmptyDec (htot.prod htru)
      (htru.prod ((ComputableInPolyTime.headD 0).comp' hinW))).of_enc_eq fun p =>
        congrArg (encPair encNat encNat) (by cases p.1.1.2 <;> simp)
  have hinRight := ComputableInPolyTime.mapWithInput (f := fun (p : P) (w : ℕ) => (p.1.1.1 + 1, w))
    (ComputableInPolyTime.listDropWithInput hinW (ComputableInPolyTime.const 1))
    ((poly_comp_fst htru).prod (ComputableInPolyTime.snd encP encNat))
  have hstateW : ComputableInPolyTime
      (fun p : P => (List.range (numStates + 1)).map fun s =>
        if s = (e tm.q₀).val + 1 then p.1.1.1 + 1 else p.1.1.1) encP (encList encNat) :=
    ComputableInPolyTime.mapConst (List.range (numStates + 1)) fun s _ => by
      by_cases hs : s = (e tm.q₀).val + 1 <;> simpa [hs] using (by first | exact htru | exact htot)
  have houtW0 := poly_cons' htru (poly_cons' htot (poly_cons' htot (poly_cons' htot
    (ComputableInPolyTime.const []))))
  have hhalfC := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) =>
      initHalfConstWCap q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2)
    _ poly_initHalfConstWCap ((hcap.prod hL).prod ((htot.prod htru).prod (htot.prod htot)))
  have hhalfF := @ComputableInPolyTime.comp' P _ _ encP _ _
    (fun q : ((ℕ × ℕ) × (ℕ × ℕ)) × (List (ℕ × ℕ) × (ℕ × ℕ)) =>
      initHalfFromWCap q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2)
    _ poly_initHalfFromWCap (((hcap.prod hL).prod (htot.prod htru)).prod (hinRight.prod
      (htot.prod htru)))
  have hsw0 : ComputableInPolyTime
      (fun p : P =>
        let L := pfLevels p.1.2 p.1.1.2.length
        let cap := 4 * (max p.1.2 p.1.1.2.length + 2)
        let fls := p.1.1.1; let tru := p.1.1.1 + 1
        let inHead := if p.1.1.2.isEmpty then (fls, tru) else (tru, p.1.1.2.headD 0)
        let inRightCells := (p.1.1.2.drop 1).map fun w => (tru, w)
        let stateW := (List.range (numStates + 1)).map fun s => if s =
          (e tm.q₀).val + 1 then tru else fls
        let outW := [tru, fls, fls, fls]
        let inTape : TapeW := (inHead, (initHalfConstWCap cap L fls tru fls fls,
          initHalfFromWCap cap L fls tru inRightCells fls tru))
        let wkTape : TapeW := ((fls, fls), (initHalfConstWCap cap L fls tru fls fls,
          initHalfConstWCap cap L fls tru fls fls))
        ((stateW, outW), (inTape, List.replicate k wkTape)))
      encP encStateW :=
    ((hstateW.prod houtW0).prod
      ((hinHead.prod (hhalfC.prod hhalfF)).prod
        (ComputableInPolyTime.replicate (ComputableInPolyTime.const k)
          ((htot.prod htot).prod (hhalfC.prod hhalfC))))).of_enc_eq
      fun _ => rfl
  have hlist := ComputableInPolyTime.range.comp'
    (ComputableInPolyTime.ite_decide hvalidDec hT (ComputableInPolyTime.const 0))
  have hpar := (hL.prod htot).prod htru
  have hinit := ComputableInPolyTime.ite_decide hvalidDec (hg0.prod hsw0)
    (ComputableInPolyTime.const (Gates.init 0, (([], []), (defaultTapeW, []))))
  have hstep : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × (Gates × StateW)) × ℕ =>
        safeTmStep e tm q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.2 q.1.2.1 q.1.2.2)
      (encPair (encPair (encPair (encPair encUnary encNat) encNat)
        (encPair encGates encStateW)) encUnary)
      (encPair encGates encStateW) := poly_safeTmStep e tm
  have hsz_poly : PolyBounded (fun p : P => (encP p).length) (fun p : P =>
      let n := (encP p).length + 2
      let M := 3 + n * tmStepBaseCost e tm + (2 + 2 * k) * 247 * n * (8 * n)
      let W := n + M + 1
      let G := 4 * W + 11
      let L := n + 3
      let Rows := 8 * n
      let Lev := 2 * (6 * (2 * W + 1)) + 1 + Rows * (2 * (10 * (2 * W + 1)) + 1)
      let Hw := L * (2 * Lev + 1)
      let Tw := 2 * (2 * W + 1 + W) + 1 + (2 * Hw + 1 + Hw)
      let Sw := 2 * (2 * ((numStates + 1) * (2 * W + 1)) + 1 + 4 * (2 * W + 1)) + 1 +
        (2 * Tw + 1 + k * (2 * Tw + 1))
      2 * (2 * (M * (2 * G + 1)) + 1 + W) + 1 + Sw + 100) := by
    have hS : PolyBounded (fun p : P => (encP p).length) (fun p : P => (encP p).length) :=
      PolyBounded.self
    have hn := hS.add (PolyBounded.const 2)
    have hM := ((PolyBounded.const 3).add (hn.mul (PolyBounded.const (tmStepBaseCost e tm)))).add
      (((PolyBounded.const ((2 + 2 * k) * 247)).mul hn).mul ((PolyBounded.const 8).mul hn))
    have hW := (hn.add hM).add (PolyBounded.const 1)
    have hG := ((PolyBounded.const 4).mul hW).add (PolyBounded.const 11)
    have hL := hn.add (PolyBounded.const 3)
    have hRows := (PolyBounded.const 8).mul hn
    have hLev := (((PolyBounded.const 2).mul ((PolyBounded.const 6).mul
      (((PolyBounded.const 2).mul hW).add (PolyBounded.const 1)))).add (PolyBounded.const 1)).add
      (hRows.mul (((PolyBounded.const 2).mul ((PolyBounded.const 10).mul
        (((PolyBounded.const 2).mul hW).add (PolyBounded.const 1)))).add (PolyBounded.const 1)))
    have hHw := hL.mul (((PolyBounded.const 2).mul hLev).add (PolyBounded.const 1))
    have hTw :=
      (((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul hW).add
        (PolyBounded.const 1)).add hW)).add
      (PolyBounded.const 1)).add ((((PolyBounded.const 2).mul hHw).add
        (PolyBounded.const 1)).add hHw)
    have hSw :=
      (((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul ((PolyBounded.const
        (numStates + 1)).mul
      (((PolyBounded.const 2).mul hW).add (PolyBounded.const 1)))).add (PolyBounded.const 1)).add
      ((PolyBounded.const 4).mul (((PolyBounded.const 2).mul hW).add
        (PolyBounded.const 1))))).add (PolyBounded.const 1)).add
      ((((PolyBounded.const 2).mul hTw).add (PolyBounded.const 1)).add
        ((PolyBounded.const k).mul (((PolyBounded.const 2).mul hTw).add (PolyBounded.const 1))))
    exact ((((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul (hM.mul
      (((PolyBounded.const 2).mul hG).add (PolyBounded.const 1)))).add
        (PolyBounded.const 1)).add hW)).add
      (PolyBounded.const 1)).add hSw).add (PolyBounded.const 100)
  have hP_len : ∀ (p : P), (encNat p.1.1.1).length ≤ (encP p).length ∧
      p.1.1.2.length ≤ (encP p).length ∧ p.1.2 ≤ (encP p).length := by
    intro p
    have h1 := length_le_encPair_left (encPair (encPair encNat (encList encNat)) encUnary) encBool p
    have h2 := (length_le_encPair_left (encPair encNat (encList encNat)) encUnary p.1).trans h1
    have h3 := (length_le_encPair_left encNat (encList encNat) p.1.1).trans h2
    have h4 := (length_le_encPair_right encNat (encList encNat) p.1.1).trans h2
    have h5 := (length_le_encPair_right (encPair encNat (encList encNat)) encUnary p.1).trans h1
    simp only [encUnary_apply, List.length_replicate] at h5
    exact ⟨h3, (length_le_encList encNat p.1.1.2).trans h4, h5⟩
  have hfold := (ComputableInPolyTime.foldlWith_spec
    (step := fun (par : (ℕ × ℕ) × ℕ) (acc : Gates × StateW) (t : ℕ) =>
      safeTmStep e tm par.1.1 par.1.2 par.2 t acc.1 acc.2)
    hpar hlist hinit hstep
    (fun p consumed acc =>
      let L := pfLevels p.1.2 p.1.1.2.length
      let x := List.replicate p.1.1.1 false
      let input := p.1.1.2.map fun w => (Gates.init p.1.1.1).val x w
      let oc := (List.range consumed.length).foldl
        (fun oc t => oc.step (pfLevels_pos p.1.2 p.1.1.2.length) tm t)
        (ObliviousCfg.init L tm input)
      (p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) = true →
        acc.1.WF p.1.1.1 ∧ Gates.Extends (Gates.init p.1.1.1) acc.1 ∧
        acc.1.1.length = 2 + consumed.length * tmStepBaseCost e tm +
          (2 + 2 * k) * ((List.range consumed.length).map (schedulePassCost L)).sum ∧
        StateW.Encodes e acc.1 x acc.2 oc) ∧
      (p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) = false →
        acc = (Gates.init 0, (([], []), (defaultTapeW, [])))))
    (fun p => ⟨fun hval => by
      simp only [hval, ↓reduceIte]
      have hcap : 2 ^ (pfLevels p.1.2 p.1.1.2.length - 1) ≤ 4 * (max p.1.2 p.1.1.2.length + 2) := by
        have hM : max p.1.2 p.1.1.2.length + 2 ≠ 0 := by omega
        have hsz := Nat.size_eq_log_two_add_one hM
        have hpow := Nat.pow_log_le_self 2 hM
        have hL1 : pfLevels p.1.2 p.1.1.2.length - 1 =
          Nat.log 2 (max p.1.2 p.1.1.2.length + 2) + 2 := by
          dsimp only [pfLevels_eq]; omega
        rw [hL1, pow_add]; linarith
      have hhead : (if p.1.1.2.isEmpty then (p.1.1.1, p.1.1.1 + 1) else (p.1.1.1 +
        1, p.1.1.2.headD 0)) =
          match p.1.1.2 with | [] => (p.1.1.1, p.1.1.1 + 1) | w :: _ => (p.1.1.1 + 1, w) := by
        cases p.1.1.2 <;> rfl
      have hsw_eq :
          (let L := pfLevels p.1.2 p.1.1.2.length
           let cap := 4 * (max p.1.2 p.1.1.2.length + 2)
           let fls := p.1.1.1; let tru := p.1.1.1 + 1
           let inHead := if p.1.1.2.isEmpty then (fls, tru) else (tru, p.1.1.2.headD 0)
           let inRightCells := (p.1.1.2.drop 1).map fun w => (tru, w)
           let stateW := (List.range (numStates + 1)).map fun s =>
             if s = (e tm.q₀).val + 1 then tru else fls
           let outW := [tru, fls, fls, fls]
           let inTape : TapeW := (inHead, (initHalfConstWCap cap L fls tru fls fls,
             initHalfFromWCap cap L fls tru inRightCells fls tru))
           let wkTape : TapeW := ((fls, fls), (initHalfConstWCap cap L fls tru fls fls,
             initHalfConstWCap cap L fls tru fls fls))
           ((stateW, outW), (inTape, List.replicate k wkTape))) =
          initStateW (pfLevels p.1.2 p.1.1.2.length) k numStates (e tm.q₀).val
            p.1.1.1 (p.1.1.1 + 1) p.1.1.2 := by
        dsimp only [initStateW_eq]
        rw [hhead, initHalfConstWCap_eq hcap, initHalfFromWCap_eq hcap, List.drop_one]
        rfl
      have hin : ∀ w ∈ p.1.1.2, w < (Gates.init p.1.1.1).2 := by
        intro w hw
        have := List.all_eq_true.mp hval w hw
        simpa [] using decide_eq_true_eq.mp this
      have hflsV : (Gates.init p.1.1.1).val (List.replicate p.1.1.1 false) p.1.1.1 = false := by
        simpa using Gates.init_val_fls (List.replicate p.1.1.1 false)
      have htruV : (Gates.init p.1.1.1).val (List.replicate p.1.1.1 false) (p.1.1.1 + 1) =
        true := by
        simpa using Gates.init_val_tru (List.replicate p.1.1.1 false)
      refine ⟨by simpa using Gates.init_wf p.1.1.1, Gates.extends_refl _, by simp, ?_⟩
      rw [hsw_eq]
      exact initStateW_spec e tm (by simp) hflsV (by simp) htruV hin,
      fun hval => by simp only [hval, Bool.false_eq_true, ↓reduceIte]⟩)
    (fun p consumed acc t hpref hinv => ⟨fun hval => by
      have ht_eq : t = consumed.length := by
        have hlt : consumed.length < (consumed ++ [t]).length := by
          rw [List.length_append, List.length_singleton]; omega
        have hget := List.IsPrefix.getElem hpref hlt
        simpa [List.getElem_range] using hget
      have hm_lt : consumed.length < p.1.2 := by
        have := hpref.length_le; simp [hval] at this; omega
      obtain ⟨hW, hE, hG, hEnc⟩ := hinv.1 hval
      dsimp only
      rw [List.length_append, List.length_singleton, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton, ht_eq]
      set L := pfLevels p.1.2 p.1.1.2.length
      have hL_pos := pfLevels_pos p.1.2 p.1.1.2.length
      have hstep_eq := safeTmStep_eq_of_encodes e tm hL_pos
        (fls := p.1.1.1) (tru := p.1.1.1 + 1) (t := consumed.length) hEnc
      rw [hstep_eq]
      set x := List.replicate p.1.1.1 false
      have hx : x.length = p.1.1.1 := by simp [x]
      have hW' : acc.1.WF x.length := hx.symm ▸ hW
      have hagr := ObliviousCfg.run_agrees tm (p.1.1.2.map fun w => (Gates.init p.1.1.1).val x w)
        hL_pos (pfLevels_step_bound p.1.2 p.1.1.2.length)
        (by simpa using pfLevels_input_bound p.1.2 p.1.1.2.length) consumed.length (by omega)
      have hle_m : (Gates.init p.1.1.1).2 ≤ acc.1.2 := by
        rcases hE with ⟨rr, hrr⟩; rw [(Gates.init_wf p.1.1.1).2, hW.2, hrr,
          List.length_append]; omega
      have hst := emitTmStep_spec e tm hL_pos hW'
        (fls := p.1.1.1) (tru := p.1.1.1 + 1)
        (lt_of_lt_of_le (by simp) hle_m)
        (by rw [Gates.val_of_extends_wf (hx.symm ▸ Gates.init_wf p.1.1.1) hE (by simp)]
            simpa [x] using Gates.init_val_fls x)
        (lt_of_lt_of_le (by simp) hle_m)
        (by rw [Gates.val_of_extends_wf (hx.symm ▸ Gates.init_wf p.1.1.1) hE (by simp)]
            simpa [x] using Gates.init_val_tru x)
        hEnc hagr.2.2.1 hagr.2.2.2.2.1
      refine ⟨hx ▸ hst.1, Gates.extends_trans hE hst.2.1, ?_, hst.2.2.2⟩
      rw [hst.2.2.1, hG]; ring,
      fun hval => by
        have := hpref.length_le; simp [hval] at this⟩)
    hsz_poly
    (fun p consumed acc hpref hinv => by
      obtain ⟨htot_l, hN_l, hT_l⟩ := hP_len p
      by_cases hval : p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) = true
      · obtain ⟨hW, _, hG, hEnc⟩ := hinv.1 hval
        set L := pfLevels p.1.2 p.1.1.2.length
        set n := (encP p).length + 2
        set M := 3 + n * tmStepBaseCost e tm + (2 + 2 * k) * 247 * n * (8 * n)
        set W := n + M + 1
        set G := 4 * W + 11
        have hclen : consumed.length ≤ p.1.2 := by
          have := hpref.length_le; simp [hval] at this; omega
        have hL_le_n : L ≤ n + 3 := by
          have h1 := pfLevels_le_log p.1.2 p.1.1.2.length
          have h2 : Nat.log 2 (max p.1.2 p.1.1.2.length + 2) ≤ max p.1.2 p.1.1.2.length + 2 :=
            Nat.log_le_self 2 _
          omega
        have h2L : 2 ^ L ≤ 8 * n := by
          have hM0 : max p.1.2 p.1.1.2.length + 2 ≠ 0 := by omega
          have hsz := Nat.size_eq_log_two_add_one hM0
          have hpow := Nat.pow_log_le_self 2 hM0
          have hL_eq : L = Nat.log 2 (max p.1.2 p.1.1.2.length + 2) + 3 := by
            dsimp only [L, pfLevels_eq]; omega
          have hmax : max p.1.2 p.1.1.2.length + 2 ≤ n := by dsimp only [n]; omega
          rw [hL_eq, pow_add]; norm_num; linarith
        have hstep_cost : ∀ t, schedulePassCost L t ≤ 247 * 2 ^ L := by
          intro t
          have hgeom : ∀ m, ((List.range m).map fun lvl => 37 + 210 * 2 ^ lvl).sum ≤
            247 * 2 ^ m := by
            intro m; induction m with
            | zero => simp
            | succ m ih =>
              rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                List.sum_singleton, pow_succ]
              have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
              omega
          have hle_all : schedulePassCost L t ≤
              ((List.range (L - 1)).map fun lvl => 37 + 210 * 2 ^ lvl).sum := by
            simp only [schedulePassCost_eq]
            suffices ∀ (xs : List ℕ),
                (xs.map fun lvl => if (t + 1) % 2 ^ (lvl + 1) =
                  0 then 37 + 210 * 2 ^ lvl else 0).sum ≤
                (xs.map fun lvl => 37 + 210 * 2 ^ lvl).sum from this _
            intro xs; induction xs with
            | nil => simp
            | cons a tl ih => simp only [List.map_cons, List.sum_cons]; split <;> omega
          exact hle_all.trans ((hgeom (L - 1)).trans (Nat.mul_le_mul_left 247
            (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le L 1))))
        have hsum_le : ((List.range consumed.length).map (schedulePassCost L)).sum ≤
            247 * n * (8 * n) := by
          have hle_m : ∀ m, ((List.range m).map (schedulePassCost L)).sum ≤ m * (247 * 2 ^ L) := by
            intro m; induction m with
            | zero => simp
            | succ m ih =>
              rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                List.sum_singleton, Nat.succ_mul]
              exact Nat.add_le_add ih (hstep_cost m)
          have h1 := (hle_m consumed.length).trans
            (Nat.mul_le_mul (by omega : consumed.length ≤ n) (Nat.mul_le_mul_left 247 h2L))
          calc ((List.range consumed.length).map (schedulePassCost L)).sum
              ≤ n * (247 * (8 * n)) := h1
            _ = 247 * n * (8 * n) := by ring
        have hM_ge : acc.1.1.length ≤ M := by
          rw [hG]
          have h1 : consumed.length * tmStepBaseCost e tm ≤ n * tmStepBaseCost e tm :=
            Nat.mul_le_mul_right _ (by omega)
          have h2 : (2 + 2 * k) * ((List.range consumed.length).map (schedulePassCost L)).sum ≤
              (2 + 2 * k) * (247 * n * (8 * n)) := Nat.mul_le_mul_left _ hsum_le
          dsimp only [M]; linarith
        have hW_ge : ∀ w < acc.1.2, (encNat w).length ≤ W := by
          intro w hw
          have hw_le : w ≤ p.1.1.1 + M := by rw [hW.2] at hw; omega
          exact (length_encNat_le_add hw_le).trans (by dsimp only [W, n]; omega)
        have hG_ge : ∀ gt ∈ acc.1.1, (Boolean.encGate gt).length ≤ G := by
          intro gt hgt
          have hgt_rev : gt ∈ acc.1.1.reverse := List.mem_reverse.mpr hgt
          obtain ⟨hlen_gt, hw_gt⟩ := isCodeFrom_gate_bounds hW.1 gt hgt_rev
          have hw_bound : ∀ w ∈ gt.2, (encNat w).length ≤ W := fun w hw =>
            hW_ge w (lt_of_lt_of_le (hw_gt w hw) (by rw [List.length_reverse, hW.2]; omega))
          exact (length_encGate_le hlen_gt hw_bound).trans (by dsimp only [G]; omega)
        have hGates_le : (encGates acc.1).length ≤ 2 * (M * (2 * G + 1)) + 1 + W :=
          length_encGates_le hM_ge hG_ge
            ((length_encNat_le_add (by rw [hW.2]; omega : acc.1.2 ≤ p.1.1.1 + M)).trans
              (by dsimp only [W, n]; omega))
        have hSw_le : (encStateW acc.2).length ≤
            2 * (2 * ((numStates + 1) * (2 * W + 1)) + 1 + 4 * (2 * W + 1)) + 1 +
              (2 * (2 * (2 * W + 1 + W) + 1 + (2 * ((n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1)) + 1 + (n +
                  3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1))) + 1 +
              k * (2 * (2 * (2 * W + 1 + W) + 1 + (2 * ((n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1)) + 1 + (n +
                  3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1))) + 1)) := by
          have hbase := length_encStateW_of_encodes e hEnc hW_ge
          have hLev_le : 2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1) ≤
              2 * (6 * (2 * W + 1)) + 1 + (8 * n) * (2 * (10 * (2 * W + 1)) + 1) := by
            have := Nat.mul_le_mul_right (2 * (10 * (2 * W + 1)) + 1) h2L; omega
          have hHw_le : L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) +
            1)) + 1) ≤
              (n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 + (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) +
                1) :=
            Nat.mul_le_mul hL_le_n (by omega)
          have hTw_le :
              2 * (2 * W + 1 + W) + 1 +
                (2 * (L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) +
                  1)) + 1 +
                  L * (2 * (2 * (6 * (2 * W + 1)) + 1 + 2 ^ L * (2 * (10 * (2 * W + 1)) + 1)) +
                    1)) ≤
              2 * (2 * W + 1 + W) + 1 +
                (2 * ((n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 + (8 * n) * (2 * (10 * (2 * W +
                  1)) + 1)) + 1)) + 1 +
                  (n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 + (8 * n) * (2 * (10 * (2 * W + 1)) +
                    1)) + 1)) := by
            omega
          have hK_le := Nat.mul_le_mul_left k
            (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hTw_le) 1)
          dsimp only at hbase
          exact hbase.trans (Nat.add_le_add_left
            (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hTw_le) 1) hK_le) _)
        change (encPair encGates encStateW acc).length ≤ _
        rw [length_encPair]
        have h1 : 2 * (encGates acc.1).length + 1 + (encStateW acc.2).length ≤
            2 * (2 * (M * (2 * G + 1)) + 1 + W) + 1 +
              (2 * (2 * ((numStates + 1) * (2 * W + 1)) + 1 + 4 * (2 * W + 1)) + 1 +
                (2 * (2 * (2 * W + 1 + W) + 1 + (2 * ((n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                  (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1)) + 1 +
                  (n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                    (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1))) + 1 +
                k * (2 * (2 * (2 * W + 1 + W) + 1 + (2 * ((n + 3) * (2 * (2 * (6 * (2 * W + 1)) +
                  1 + (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1)) + 1 +
                  (n + 3) * (2 * (2 * (6 * (2 * W + 1)) + 1 +
                    (8 * n) * (2 * (10 * (2 * W + 1)) + 1)) + 1))) + 1))) + 100 := by omega
        exact h1
      · have hvalF : p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) = false :=
          Bool.eq_false_iff.mpr hval
        rw [hinv.2 hvalF]
        have hconst : (encPair encGates encStateW
            (Gates.init 0, (([], []), (defaultTapeW, [])))).length ≤ 100 := by
          decide
        dsimp only; omega)).1
  have hfin_g := poly_fst hfold
  have hfin_out := poly_getD_const (poly_snd (poly_fst (poly_snd hfold))) 2 0
  have hnegDec : ComputableInPolyTime (fun p : P => decide (p.2 = true)) encP encBool :=
    hneg.of_enc_eq fun p => congrArg encBool (by cases p.2 <;> rfl)
  have hres := ComputableInPolyTime.ite_decide hnegDec (poly_gNot' hfin_g hfin_out)
    (hfin_g.prod hfin_out)
  have hguarded := ComputableInPolyTime.ite_decide hvalidDec hres
    (ComputableInPolyTime.const (Gates.init 0, 0))
  refine hguarded.of_enc_eq fun p => congrArg (encPair encGates encNat) ?_
  by_cases hval : p.1.1.2.all (fun w => decide (w < p.1.1.1 + 2)) = true
  · simp only [hval, ↓reduceIte]
    have hcap : 2 ^ (pfLevels p.1.2 p.1.1.2.length - 1) ≤ 4 * (max p.1.2 p.1.1.2.length + 2) := by
      have hM : max p.1.2 p.1.1.2.length + 2 ≠ 0 := by omega
      have hsz := Nat.size_eq_log_two_add_one hM
      have hpow := Nat.pow_log_le_self 2 hM
      have hL1 : pfLevels p.1.2 p.1.1.2.length - 1 =
        Nat.log 2 (max p.1.2 p.1.1.2.length + 2) + 2 := by
        dsimp only [pfLevels_eq]; omega
      rw [hL1, pow_add]; linarith
    have hhead : (if p.1.1.2.isEmpty then (p.1.1.1, p.1.1.1 + 1) else (p.1.1.1 +
      1, p.1.1.2.headD 0)) =
        match p.1.1.2 with | [] => (p.1.1.1, p.1.1.1 + 1) | w :: _ => (p.1.1.1 + 1, w) := by
      cases p.1.1.2 <;> rfl
    have hsw_eq :
        (let L := pfLevels p.1.2 p.1.1.2.length
         let cap := 4 * (max p.1.2 p.1.1.2.length + 2)
         let fls := p.1.1.1; let tru := p.1.1.1 + 1
         let inHead := if p.1.1.2.isEmpty then (fls, tru) else (tru, p.1.1.2.headD 0)
         let inRightCells := (p.1.1.2.drop 1).map fun w => (tru, w)
         let stateW := (List.range (numStates + 1)).map fun s =>
           if s = (e tm.q₀).val + 1 then tru else fls
         let outW := [tru, fls, fls, fls]
         let inTape : TapeW := (inHead, (initHalfConstWCap cap L fls tru fls fls,
           initHalfFromWCap cap L fls tru inRightCells fls tru))
         let wkTape : TapeW := ((fls, fls), (initHalfConstWCap cap L fls tru fls fls,
           initHalfConstWCap cap L fls tru fls fls))
         ((stateW, outW), (inTape, List.replicate k wkTape))) =
        initStateW (pfLevels p.1.2 p.1.1.2.length) k numStates (e tm.q₀).val
          p.1.1.1 (p.1.1.1 + 1) p.1.1.2 := by
      dsimp only [initStateW_eq]
      rw [hhead, initHalfConstWCap_eq hcap, initHalfFromWCap_eq hcap, List.drop_one]
      rfl
    have hin : ∀ w ∈ p.1.1.2, w < (Gates.init p.1.1.1).2 := by
      intro w hw; simpa [] using decide_eq_true_eq.mp (List.all_eq_true.mp hval w hw)
    -- Show fold with `safeTmStep` equals fold with `emitTmStep`.
    have hfeq : ∀ m ≤ p.1.2,
        (List.range m).foldl (fun acc t => safeTmStep e tm (pfLevels p.1.2 p.1.1.2.length)
          p.1.1.1 (p.1.1.1 + 1) t acc.1 acc.2)
          (Gates.init p.1.1.1, initStateW (pfLevels p.1.2 p.1.1.2.length) k numStates (e tm.q₀).val
            p.1.1.1 (p.1.1.1 + 1) p.1.1.2) =
        (List.range m).foldl (fun acc t => emitTmStep e tm (pfLevels p.1.2 p.1.1.2.length)
          p.1.1.1 (p.1.1.1 + 1) t acc.1 acc.2)
          (Gates.init p.1.1.1, initStateW (pfLevels p.1.2 p.1.1.2.length) k numStates (e tm.q₀).val
            p.1.1.1 (p.1.1.1 + 1) p.1.1.2) ∧
        let acc :=
          (List.range m).foldl (fun acc t => emitTmStep e tm (pfLevels p.1.2 p.1.1.2.length)
          p.1.1.1 (p.1.1.1 + 1) t acc.1 acc.2)
          (Gates.init p.1.1.1, initStateW (pfLevels p.1.2 p.1.1.2.length) k numStates (e tm.q₀).val
            p.1.1.1 (p.1.1.1 + 1) p.1.1.2)
        acc.1.WF p.1.1.1 ∧ Gates.Extends (Gates.init p.1.1.1) acc.1 ∧
        StateW.Encodes e acc.1 (List.replicate p.1.1.1 false) acc.2
          ((List.range m).foldl (fun oc t => oc.step (pfLevels_pos p.1.2 p.1.1.2.length) tm t)
            (ObliviousCfg.init (pfLevels p.1.2 p.1.1.2.length) tm
              (p.1.1.2.map fun w => (Gates.init p.1.1.1).val (List.replicate p.1.1.1 false) w)))
                := by
      intro m; induction m with
      | zero =>
        intro _; refine ⟨rfl, by simpa using Gates.init_wf p.1.1.1, Gates.extends_refl _, ?_⟩
        exact initStateW_spec e tm (by simp)
          (by simpa using Gates.init_val_fls (List.replicate p.1.1.1 false))
          (by simp)
          (by simpa using Gates.init_val_tru (List.replicate p.1.1.1 false)) hin
      | succ m ih =>
        intro hm; obtain ⟨heq, hW, hE, hEnc⟩ := ih (by omega)
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil, heq]
        rw [safeTmStep_eq_of_encodes e tm (pfLevels_pos p.1.2 p.1.1.2.length)
          (fls := p.1.1.1) (tru := p.1.1.1 + 1) (t := m) hEnc]
        set x := List.replicate p.1.1.1 false
        have hx : x.length = p.1.1.1 := by simp [x]
        have hagr := ObliviousCfg.run_agrees tm (p.1.1.2.map fun w => (Gates.init p.1.1.1).val x w)
          (pfLevels_pos p.1.2 p.1.1.2.length) (pfLevels_step_bound p.1.2 p.1.1.2.length)
          (by simpa using pfLevels_input_bound p.1.2 p.1.1.2.length) m (by omega)
        have hle_m : (Gates.init p.1.1.1).2 ≤
            ((List.range m).foldl (fun acc t => emitTmStep e tm (pfLevels p.1.2 p.1.1.2.length)
              p.1.1.1 (p.1.1.1 + 1) t acc.1 acc.2)
              (Gates.init p.1.1.1, initStateW (pfLevels p.1.2 p.1.1.2.length) k numStates
                (e tm.q₀).val p.1.1.1 (p.1.1.1 + 1) p.1.1.2)).1.2 := by
          rcases hE with ⟨rr, hrr⟩; rw [(Gates.init_wf p.1.1.1).2, hW.2, hrr,
            List.length_append]; omega
        have hst := emitTmStep_spec e tm (pfLevels_pos p.1.2 p.1.1.2.length) (hx.symm ▸ hW)
          (fls := p.1.1.1) (tru := p.1.1.1 + 1)
          (lt_of_lt_of_le (by simp) hle_m)
          (by rw [Gates.val_of_extends_wf (hx.symm ▸ Gates.init_wf p.1.1.1) hE
            (by simp)]
              simpa [x] using Gates.init_val_fls x)
          (lt_of_lt_of_le (by simp) hle_m)
          (by rw [Gates.val_of_extends_wf (hx.symm ▸ Gates.init_wf p.1.1.1) hE
            (by simp)]
              simpa [x] using Gates.init_val_tru x)
          hEnc hagr.2.2.1 hagr.2.2.2.2.1
        exact ⟨rfl, hx ▸ hst.1, Gates.extends_trans hE hst.2.1, hst.2.2.2⟩
    dsimp only [buildGates_eq]
    rw [hsw_eq, (hfeq p.1.2 le_rfl).1]
  · simp [hval]

/-! ### Headline uniform oblivious circuit theorems -/

/-- **Polynomial-time uniform oblivious circuit simulation**: every deterministic multi-tape
Turing machine running in polynomial-time computable time `T n` admits a `P`-uniform family of
De Morgan Boolean circuits of size `O((T n + 1) * (Nat.log 2 (max (T n) n + 2) + 1))`
simulating `T n` steps of `tm` on inputs of length `n`. -/
theorem exists_oblivious_uniform_circuits {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) {T : ℕ → ℕ}
    (hT : ComputableInPolyTime T encUnary encUnary) :
    ∃ (C : ℕ) (gen : ∀ n, Circuit Boolean.signature n 1),
      ComputableInPolyTime (fun n => (⟨n, gen n⟩ : Σ m, Circuit Boolean.signature m 1))
        encUnary (Boolean.encCircuit 1) ∧
      (∀ n, (gen n).size ≤ C * (T n + 1) * (Nat.log 2 (max (T n) n + 2) + 1)) ∧
      (∀ n (x : Fin n → Bool),
        (gen n).eval Boolean.interpretation x 0 =
          decide ((tm.runFrom (tm.initCfg (List.ofFn x)) (T n)).output = [true])) := by
  have : Fintype State := Fintype.ofFinite State
  let e : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  let hin : ∀ n, ∀ w ∈ List.range n, w < n + 2 := fun n w hw =>
    lt_trans (List.mem_range.mp hw) (by omega)
  let gen : ∀ n, Circuit Boolean.signature n 1 := fun n =>
    obliviousCircuitWithWires e tm n (List.range n) (T n) false (hin n)
  refine ⟨3 + tmStepBaseCost e tm + 3 * ((2 + 2 * k) * 247), gen, ?_, ?_, ?_⟩
  · have hrange : ComputableInPolyTime (fun n => List.range n) encUnary (encList encNat) :=
      (ComputableInPolyTime.mapWithInput (f := fun (_ : ℕ) (i : ℕ) => i)
        ComputableInPolyTime.range
        (ComputableInPolyTime.unary_to_binary.comp'
          (ComputableInPolyTime.snd encUnary encUnary))).of_enc_eq fun n => by simp
    have hbg := (computableInPolyTime_buildGates e tm).comp'
      (((ComputableInPolyTime.unary_to_binary.prod hrange).prod hT).prod
        (ComputableInPolyTime.const false))
    have hcode : ComputableInPolyTime (fun n => (n, (gen n).code)) encUnary
        (encPair encUnary Boolean.encCode) :=
      (ComputableInPolyTime.id'.prod
        ((ComputableInPolyTime.listReverseWithInput (poly_fst (poly_fst hbg))).prod
          (poly_cons' (poly_snd hbg) (ComputableInPolyTime.const [])))).of_enc_eq fun n => by
        have hall : (List.range n).all (fun w => decide (w < n + 2)) = true :=
          List.all_eq_true.mpr fun w hw => decide_eq_true (hin n w hw)
        dsimp only [gen]
        rw [code_obliviousCircuitWithWires]
        simp [hall]
    exact hcode.of_enc_eq fun n => by simp [Boolean.encCircuit_apply]
  · intro n
    have hsz := size_obliviousCircuitWithWires_le e tm n (List.range n) (T n) false (hin n)
    simp only [List.length_range] at hsz
    set L := Nat.log 2 (max (T n) n + 2)
    have h1 : 3 ≤ 3 * (T n + 1) * (L + 1) := by
      have hpos : 1 ≤ (T n + 1) * (L + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      calc 3 = 3 * 1 := by ring
        _ ≤ 3 * ((T n + 1) * (L + 1)) := Nat.mul_le_mul_left 3 hpos
        _ = 3 * (T n + 1) * (L + 1) := by ring
    have h2 : T n * tmStepBaseCost e tm ≤ tmStepBaseCost e tm * (T n + 1) * (L + 1) := by
      have htl : T n ≤ (T n + 1) * (L + 1) :=
        (Nat.le_succ (T n)).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos L))
      calc T n * tmStepBaseCost e tm = tmStepBaseCost e tm * T n := Nat.mul_comm _ _
        _ ≤ tmStepBaseCost e tm * ((T n + 1) * (L + 1)) := Nat.mul_le_mul_left _ htl
        _ = tmStepBaseCost e tm * (T n + 1) * (L + 1) := by ring
    have h3 : (2 + 2 * k) * 247 * T n * (L + 3) ≤
        3 * ((2 + 2 * k) * 247) * (T n + 1) * (L + 1) := by
      calc (2 + 2 * k) * 247 * T n * (L + 3)
          ≤ (2 + 2 * k) * 247 * (T n + 1) * (3 * (L + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_succ _)) (by omega)
        _ = 3 * ((2 + 2 * k) * 247) * (T n + 1) * (L + 1) := by ring
    have hsum : 3 + T n * tmStepBaseCost e tm + (2 + 2 * k) * 247 * T n * (L + 3) ≤
        (3 + tmStepBaseCost e tm + 3 * ((2 + 2 * k) * 247)) * (T n + 1) * (L + 1) := by
      calc 3 + T n * tmStepBaseCost e tm + (2 + 2 * k) * 247 * T n * (L + 3)
          ≤ 3 * (T n + 1) * (L + 1) + tmStepBaseCost e tm * (T n + 1) * (L + 1) +
            3 * ((2 + 2 * k) * 247) * (T n + 1) * (L + 1) :=
            Nat.add_le_add (Nat.add_le_add h1 h2) h3
        _ = (3 + tmStepBaseCost e tm + 3 * ((2 + 2 * k) * 247)) * (T n + 1) * (L + 1) := by ring
    exact hsz.trans hsum
  · intro n x
    have hev := eval_obliviousCircuitWithWires e tm n (List.range n) (T n) false (hin n) x
    have hmap : (List.range n).map (fun w => (Gates.init n).val (List.ofFn x) w) = List.ofFn x := by
      apply List.ext_getElem (by simp)
      intro i hi _
      simp only [List.length_map, List.length_range] at hi
      simp only [List.getElem_map, List.getElem_range]
      have hlen : (List.ofFn x).length = n := by simp
      have hval := Gates.init_val_input (x := List.ofFn x) (by omega : i < (List.ofFn x).length)
      rw [hlen] at hval
      exact hval
    dsimp only [gen]
    rw [hev, hmap]
    simp

/-- Auxiliary logarithmic bound: `Nat.log 2 (K * M) ≤ (Nat.log 2 K + 2) * (Nat.log 2 M + 1)`. -/
private theorem log_mul_le_mul_succ (K M : ℕ) :
    Nat.log 2 (K * M) ≤ (Nat.log 2 K + 2) * (Nat.log 2 M + 1) := by
  by_cases hK : K = 0
  · subst hK; simp
  by_cases hM : M = 0
  · subst hM; simp
  have h1 : K < 2 ^ (Nat.log 2 K + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  have h2 : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hmul : K * M < 2 ^ (Nat.log 2 K + Nat.log 2 M + 2) := by
    calc K * M < 2 ^ (Nat.log 2 K + 1) * 2 ^ (Nat.log 2 M + 1) :=
          Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log 2 K + Nat.log 2 M + 2) := by rw [← pow_add]; ring_nf
  have hlog : Nat.log 2 (K * M) < Nat.log 2 K + Nat.log 2 M + 2 :=
    (Nat.log_lt_iff_lt_pow (by norm_num) (Nat.mul_ne_zero hK hM)).mpr hmul
  nlinarith

/-- **Uniform co-nondeterministic circuits ignoring primary inputs for `NTIME`**:
for every language `L ∈ NTIME encBits t` with polynomial-time computable `t`, there is a constant
`C` and a polynomial-time computable family `(x, m) ↦ D_{x, m}` of witness circuits of primary
arity `m` and size at most `C * (t |x| + |x| + 1) * (Nat.log 2 (t |x| + |x| + 2) + 1)`
(independent of `m`) that co-nondeterministically accept every `u : Fin m → Bool` iff `x ∉ L`. -/
theorem exists_coNSIZE_ignore_circuits_of_mem_NTIME {L : Language Bool} {t : ℕ → ℕ}
    (hL : L ∈ NTIME encBits t) (ht : ComputableInPolyTime t encUnary encUnary) :
    ∃ (C : ℕ) (gen : ∀ (_x : List Bool) (m : ℕ), WitnessCircuit m),
      ComputableInPolyTime
        (fun p : List Bool × ℕ => (⟨p.2, gen p.1 p.2⟩ : Σ m, WitnessCircuit m))
        (encPair encBits encUnary) WitnessCircuit.encWitnessCircuit ∧
      (∀ x m, (gen x m).size ≤
        C * (t x.length + x.length + 1) * (Nat.log 2 (t x.length + x.length + 2) + 1)) ∧
      (∀ x m (u : Fin m → Bool), (gen x m).CoNondetAccepts u ↔ x ∉ L) := by
  obtain ⟨V, c, hV, hViff⟩ := exists_verifier_of_mem_NTIME hL
  obtain ⟨c₁, ⟨k, State, hfin, tm, htm⟩, _⟩ := hV
  have : Fintype State := Fintype.ofFinite State
  let e : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  let wLen : List Bool → ℕ := fun x => c * t x.length + c
  let inWires : List Bool → ℕ → List ℕ := fun x m =>
    (frame x).map (fun b => if b then m + wLen x + 1 else m + wLen x) ++
    (List.range (wLen x)).map (fun j => m + j)
  let Tstep : List Bool → ℕ := fun x => c₁ * (2 * x.length + 1 + wLen x + 1)
  have hin : ∀ x m, ∀ w ∈ inWires x m, w < m + wLen x + 2 := by
    intro x m w hw
    simp only [inWires, List.mem_append, List.mem_map, List.mem_range] at hw
    rcases hw with ⟨b, _, rfl⟩ | ⟨j, hj, rfl⟩
    · cases b <;> simp
    · omega
  let gen : ∀ (x : List Bool) (m : ℕ), WitnessCircuit m := fun x m =>
    ⟨wLen x, obliviousCircuitWithWires e tm (m + wLen x) (inWires x m) (Tstep x) true (hin x m)⟩
  let K : ℕ := (c₁ + 1) * (2 + c + 2)
  let C : ℕ :=
    c + 3 + (tmStepBaseCost e tm + 3 * ((2 + 2 * k) * 247) * (Nat.log 2 K + 5)) * K
  refine ⟨C, gen, ?_, ?_, ?_⟩
  · -- Polynomial-time uniformity of `(x, m) ↦ ⟨m, gen x m⟩`.
    set P := List Bool × ℕ
    set encP : P ↪ List Bool := encPair encBits encUnary
    have hx : ComputableInPolyTime (fun p : P => p.1) encP encBits :=
      ComputableInPolyTime.fst _ _
    have hm : ComputableInPolyTime (fun p : P => p.2) encP encUnary :=
      ComputableInPolyTime.snd _ _
    have hxLen : ComputableInPolyTime (fun p : P => p.1.length) encP encUnary :=
      ComputableInPolyTime.length_bits.comp' hx
    have hwLen : ComputableInPolyTime (fun p : P => wLen p.1) encP encUnary :=
      ComputableInPolyTime.unary_add.comp'
        ((ComputableInPolyTime.unary_mul.comp'
          ((ComputableInPolyTime.const c).prod (ht.comp' hxLen))).prod
          (ComputableInPolyTime.const c))
    have htotU : ComputableInPolyTime (fun p : P => p.2 + wLen p.1) encP encUnary :=
      ComputableInPolyTime.unary_add.comp' (hm.prod hwLen)
    have htot : ComputableInPolyTime (fun p : P => p.2 + wLen p.1) encP encNat :=
      ComputableInPolyTime.unary_to_binary.comp' htotU
    have htru : ComputableInPolyTime (fun p : P => p.2 + wLen p.1 + 1) encP encNat :=
      ComputableInPolyTime.binary_add' htot (ComputableInPolyTime.const 1)
    have hframe : ComputableInPolyTime (fun p : P => frame p.1) encP (encList encBool) :=
      ComputableInPolyTime.bitsToList.comp' ((ComputableInPolyTime.bitsFrame encBits).comp' hx)
    have hpart1 : ComputableInPolyTime
        (fun p : P => (frame p.1).map fun b => if b then p.2 + wLen p.1 + 1 else p.2 + wLen p.1)
        encP (encList encNat) :=
      ComputableInPolyTime.mapWithInput (f := fun (p : P) (b : Bool) =>
        if b then p.2 + wLen p.1 + 1 else p.2 + wLen p.1) hframe
        (ComputableInPolyTime.ite_decide
          ((ComputableInPolyTime.snd encP encBool).of_enc_eq fun q =>
            congrArg encBool (by cases q.2 <;> rfl))
          (poly_comp_fst htru) (poly_comp_fst htot))
    have hpart2 : ComputableInPolyTime
        (fun p : P => (List.range (wLen p.1)).map fun j => p.2 + j) encP (encList encNat) :=
      ComputableInPolyTime.mapWithInput (f := fun (p : P) (j : ℕ) => p.2 + j)
        (ComputableInPolyTime.range.comp' hwLen)
        (ComputableInPolyTime.unary_to_binary.comp'
          (ComputableInPolyTime.unary_add.comp'
            ((poly_comp_fst hm).prod (ComputableInPolyTime.snd encP encUnary))))
    have hinW : ComputableInPolyTime (fun p : P => inWires p.1 p.2) encP (encList encNat) :=
      poly_append' hpart1 hpart2
    have hTstep : ComputableInPolyTime (fun p : P => Tstep p.1) encP encUnary :=
      ComputableInPolyTime.unary_mul.comp'
        ((ComputableInPolyTime.const c₁).prod
          (ComputableInPolyTime.unary_add.comp'
            ((ComputableInPolyTime.unary_add.comp'
              ((ComputableInPolyTime.unary_add.comp'
                ((ComputableInPolyTime.unary_mul.comp'
                  ((ComputableInPolyTime.const 2).prod hxLen)).prod
                  (ComputableInPolyTime.const 1))).prod hwLen)).prod
              (ComputableInPolyTime.const 1))))
    have hbg := (computableInPolyTime_buildGates e tm).comp'
      (((htot.prod hinW).prod hTstep).prod (ComputableInPolyTime.const true))
    have hpack : ComputableInPolyTime
        (fun p : P => (p.2, (p.2 + wLen p.1, (gen p.1 p.2).circuit.code))) encP
        (encPair encUnary (encPair encUnary Boolean.encCode)) :=
      (hm.prod (htotU.prod
        ((ComputableInPolyTime.listReverseWithInput (poly_fst (poly_fst hbg))).prod
          (poly_cons' (poly_snd hbg) (ComputableInPolyTime.const []))))).of_enc_eq fun p => by
        have hall : (inWires p.1 p.2).all (fun w => decide (w < p.2 + wLen p.1 + 2)) = true :=
          List.all_eq_true.mpr fun w hw => decide_eq_true (hin p.1 p.2 w hw)
        dsimp only [gen]
        rw [code_obliviousCircuitWithWires]
        simp [hall]
    exact hpack.of_enc_eq fun p => by
      dsimp only [gen, WitnessCircuit.encWitnessCircuit_apply]
      simp [Boolean.encCircuit_apply]
  · -- Size bound independent of `m`.
    intro x m
    set N := t x.length + x.length
    have hsz := size_obliviousCircuitWithWires_le e tm (m + wLen x) (inWires x m) (Tstep x)
      true (hin x m)
    have hlen : (inWires x m).length = 2 * x.length + 1 + wLen x := by
      simp [inWires, wLen]
    have hw_le : wLen x ≤ c * (N + 1) := by dsimp only [wLen, N]; nlinarith
    have hT_le : Tstep x ≤ K * (N + 1) := by
      have hsum : 2 * x.length + 1 + wLen x + 1 ≤ (2 + c + 2) * (N + 1) := by
        dsimp only [wLen, N]; nlinarith
      calc Tstep x = c₁ * (2 * x.length + 1 + wLen x + 1) := rfl
        _ ≤ (c₁ + 1) * ((2 + c + 2) * (N + 1)) := Nat.mul_le_mul (Nat.le_succ _) hsum
        _ = K * (N + 1) := by dsimp only [K]; ring
    have hmax_le : max (Tstep x) (inWires x m).length + 2 ≤ K * (N + 2) := by
      have h1 : Tstep x + 2 ≤ K * (N + 2) := by
        have hK1 : 2 ≤ K := by dsimp only [K]; nlinarith
        calc Tstep x + 2 ≤ K * (N + 1) + K := Nat.add_le_add hT_le hK1
          _ = K * (N + 2) := by ring
      have h2 : (inWires x m).length + 2 ≤ K * (N + 2) := by
        rw [hlen]
        have hsum : 2 * x.length + 1 + wLen x + 2 ≤ (2 + c + 2) * (N + 2) := by
          dsimp only [wLen, N]; nlinarith
        calc 2 * x.length + 1 + wLen x + 2
            ≤ 1 * ((2 + c + 2) * (N + 2)) := by simpa using hsum
          _ ≤ (c₁ + 1) * ((2 + c + 2) * (N + 2)) :=
            Nat.mul_le_mul_right _ (Nat.succ_pos c₁)
          _ = K * (N + 2) := by dsimp only [K]; ring
      omega
    have hlog_le : Nat.log 2 (max (Tstep x) (inWires x m).length + 2) + 3 ≤
        (Nat.log 2 K + 5) * (Nat.log 2 (N + 2) + 1) := by
      have h1 := (Nat.log_mono_right hmax_le).trans (log_mul_le_mul_succ K (N + 2))
      have h2 : 3 ≤ 3 * (Nat.log 2 (N + 2) + 1) := Nat.le_mul_of_pos_right 3 (Nat.succ_pos _)
      calc Nat.log 2 (max (Tstep x) (inWires x m).length + 2) + 3
          ≤ (Nat.log 2 K + 2) * (Nat.log 2 (N + 2) + 1) + 3 * (Nat.log 2 (N + 2) + 1) :=
            Nat.add_le_add h1 h2
        _ = (Nat.log 2 K + 5) * (Nat.log 2 (N + 2) + 1) := by ring
    have hc_le : (gen x m).circuit.size ≤ C * (N + 1) * (Nat.log 2 (N + 2) + 1) := by
      have hstep1 : 3 ≤ 3 * (N + 1) * (Nat.log 2 (N + 2) + 1) := by
        have hpos : 1 ≤ (N + 1) * (Nat.log 2 (N + 2) + 1) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
        calc 3 = 3 * 1 := by ring
          _ ≤ 3 * ((N + 1) * (Nat.log 2 (N + 2) + 1)) := Nat.mul_le_mul_left 3 hpos
          _ = 3 * (N + 1) * (Nat.log 2 (N + 2) + 1) := by ring
      have hstep2 : Tstep x * tmStepBaseCost e tm ≤
          tmStepBaseCost e tm * K * (N + 1) * (Nat.log 2 (N + 2) + 1) := by
        have htl : Tstep x ≤ K * (N + 1) * (Nat.log 2 (N + 2) + 1) :=
          hT_le.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
        calc Tstep x * tmStepBaseCost e tm = tmStepBaseCost e tm * Tstep x := Nat.mul_comm _ _
          _ ≤ tmStepBaseCost e tm * (K * (N + 1) * (Nat.log 2 (N + 2) + 1)) :=
            Nat.mul_le_mul_left _ htl
          _ = tmStepBaseCost e tm * K * (N + 1) * (Nat.log 2 (N + 2) + 1) := by ring
      have hstep3 : (2 + 2 * k) * 247 * Tstep x *
          (Nat.log 2 (max (Tstep x) (inWires x m).length + 2) + 3) ≤
          3 * ((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
            (Nat.log 2 (N + 2) + 1) := by
        have hm1 : (2 + 2 * k) * 247 * Tstep x ≤
            (2 + 2 * k) * 247 * (K * (N + 1)) := Nat.mul_le_mul_left _ hT_le
        have hm2 := Nat.mul_le_mul hm1 hlog_le
        calc (2 + 2 * k) * 247 * Tstep x *
              (Nat.log 2 (max (Tstep x) (inWires x m).length + 2) + 3)
            ≤ (2 + 2 * k) * 247 * (K * (N + 1)) *
              ((Nat.log 2 K + 5) * (Nat.log 2 (N + 2) + 1)) := hm2
          _ ≤ 3 * ((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
              (Nat.log 2 (N + 2) + 1) := by
            have : (2 + 2 * k) * 247 * (K * (N + 1)) *
                ((Nat.log 2 K + 5) * (Nat.log 2 (N + 2) + 1)) =
                1 * (((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
                  (Nat.log 2 (N + 2) + 1)) := by ring
            rw [this]
            calc 1 * (((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
                    (Nat.log 2 (N + 2) + 1))
                ≤ 3 * (((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
                    (Nat.log 2 (N + 2) + 1)) :=
                  Nat.mul_le_mul_right _ (by norm_num)
              _ = 3 * ((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
                  (Nat.log 2 (N + 2) + 1) := by ring
      have htot_le : 3 + Tstep x * tmStepBaseCost e tm + (2 + 2 * k) * 247 * Tstep x *
          (Nat.log 2 (max (Tstep x) (inWires x m).length + 2) + 3) ≤
          C * (N + 1) * (Nat.log 2 (N + 2) + 1) := by
        calc 3 + Tstep x * tmStepBaseCost e tm + (2 + 2 * k) * 247 * Tstep x *
              (Nat.log 2 (max (Tstep x) (inWires x m).length + 2) + 3)
            ≤ 3 * (N + 1) * (Nat.log 2 (N + 2) + 1) +
              tmStepBaseCost e tm * K * (N + 1) * (Nat.log 2 (N + 2) + 1) +
              3 * ((2 + 2 * k) * 247) * (Nat.log 2 K + 5) * K * (N + 1) *
                (Nat.log 2 (N + 2) + 1) :=
              Nat.add_le_add (Nat.add_le_add hstep1 hstep2) hstep3
          _ ≤ (c + 3 + (tmStepBaseCost e tm + 3 * ((2 + 2 * k) * 247) * (Nat.log 2 K + 5)) * K) *
              (N + 1) * (Nat.log 2 (N + 2) + 1) := by
            have hc0 : 0 ≤ c * (N + 1) * (Nat.log 2 (N + 2) + 1) := Nat.zero_le _
            linarith
          _ = C * (N + 1) * (Nat.log 2 (N + 2) + 1) := rfl
      exact hsz.trans htot_le
    have hw_le' : wLen x ≤ C * (N + 1) * (Nat.log 2 (N + 2) + 1) := by
      have h1 : c ≤ C := by dsimp only [C]; omega
      calc wLen x ≤ c * (N + 1) := hw_le
        _ ≤ C * (N + 1) := Nat.mul_le_mul_right _ h1
        _ ≤ C * (N + 1) * (Nat.log 2 (N + 2) + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    exact max_le hc_le hw_le'
  · -- Semantic correctness: co-nondeterministic acceptance iff `x ∉ L`.
    intro x m u
    have hiff := hViff x (wLen x) le_rfl
    rw [WitnessCircuit.coNondetAccepts_iff,
      show (x ∉ L) ↔ ¬(∃ w, w.length = wLen x ∧ V (x, w) = true)
      from not_congr hiff]
    constructor
    · intro hco ⟨w, hw, hVw⟩
      let y : Fin (wLen x) → Bool := fun i => w[i.val]'(by omega)
      have hy : List.ofFn y = w := by
        apply List.ext_getElem (by simp [hw])
        intro i hi _; simp [y]
      have hlen_uy : (List.ofFn (Fin.append u y)).length = m + wLen x := by simp
      have hev := eval_obliviousCircuitWithWires e tm (m + wLen x) (inWires x m) (Tstep x)
        true (hin x m) (Fin.append u y)
      have hmap : (inWires x m).map
          (fun w => (Gates.init (m + wLen x)).val (List.ofFn (Fin.append u y)) w) =
          encPair encBits encBits (x, w) := by
        simp only [inWires, List.map_append, List.map_map, encPair_apply, encBits_apply]
        congr 1
        · apply List.ext_getElem (by simp)
          intro i hi _
          simp only [List.length_map] at hi
          simp only [List.getElem_map, Function.comp_apply]
          cases hb : (frame x)[i] with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            simpa [hlen_uy] using Gates.init_val_fls (List.ofFn (Fin.append u y))
          | true =>
            simp only [↓reduceIte]
            simpa [hlen_uy] using Gates.init_val_tru (List.ofFn (Fin.append u y))
        · rw [← hy]
          apply List.ext_getElem (by simp)
          intro i hi _
          simp only [List.length_map, List.length_range] at hi
          simp only [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_ofFn]
          have hval : (Gates.init (m + wLen x)).val (List.ofFn (Fin.append u y)) (m + i) =
              (List.ofFn (Fin.append u y))[m + i]'(by rw [hlen_uy]; omega) := by
            simpa [hlen_uy] using Gates.init_val_input (x := List.ofFn (Fin.append u y))
              (by rw [hlen_uy]; omega : m + i < (List.ofFn (Fin.append u y)).length)
          rw [hval, List.getElem_ofFn]
          exact Fin.append_right u y ⟨i, hi⟩
      have hrun := (htm (x, w)).runFrom_of_le (J := Tstep x) (by simp [Tstep, hw])
      have hval := hco y
      dsimp only [gen] at hval
      rw [hev] at hval
      rw [hmap, hrun.2, encBool_apply, hVw] at hval
      simp at hval
    · intro hnot y
      have hlen_uy : (List.ofFn (Fin.append u y)).length = m + wLen x := by simp [gen]
      have hev := eval_obliviousCircuitWithWires e tm (m + wLen x) (inWires x m) (Tstep x)
        true (hin x m) (Fin.append u y)
      have hmap : (inWires x m).map
          (fun w => (Gates.init (m + wLen x)).val (List.ofFn (Fin.append u y)) w) =
          encPair encBits encBits (x, List.ofFn y) := by
        simp only [inWires, List.map_append, List.map_map, encPair_apply, encBits_apply]
        congr 1
        · apply List.ext_getElem (by simp)
          intro i hi _
          simp only [List.length_map] at hi
          simp only [List.getElem_map, Function.comp_apply]
          cases hb : (frame x)[i] with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            simpa [hlen_uy] using Gates.init_val_fls (List.ofFn (Fin.append u y))
          | true =>
            simp only [↓reduceIte]
            simpa [hlen_uy] using Gates.init_val_tru (List.ofFn (Fin.append u y))
        · apply List.ext_getElem (by simp [gen])
          intro i hi _
          simp only [List.length_map, List.length_range] at hi
          simp only [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_ofFn]
          have hval : (Gates.init (m + wLen x)).val (List.ofFn (Fin.append u y)) (m + i) =
              (List.ofFn (Fin.append u y))[m + i]'(by rw [hlen_uy]; omega) := by
            simpa [hlen_uy] using Gates.init_val_input (x := List.ofFn (Fin.append u y))
              (by rw [hlen_uy]; omega : m + i < (List.ofFn (Fin.append u y)).length)
          rw [hval, List.getElem_ofFn]
          exact Fin.append_right u y ⟨i, hi⟩
      have hrun := (htm (x, List.ofFn y)).runFrom_of_le (J := Tstep x) (by simp [Tstep, gen])
      have hVf : V (x, List.ofFn y) = false := by
        cases hv : V (x, List.ofFn y) with
        | false => rfl
        | true => exact False.elim (hnot ⟨List.ofFn y, by simp [gen], hv⟩)
      dsimp only [gen]
      rw [hev]
      rw [hmap, hrun.2, encBool_apply, hVf]
      simp

end CslibFrontier.Computability.Circuit.Oblivious
