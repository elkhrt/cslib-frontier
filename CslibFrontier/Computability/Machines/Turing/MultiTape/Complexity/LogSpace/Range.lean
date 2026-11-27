/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BitsGetElem
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-range iteration and equality testing in logarithmic space

`Turing.MultiTapeTM.ComputableInLogSpace.map_range_const` iterates a logarithmic-space computation
over a fixed compile-time range `List.range k`. Here we prove the general polynomial-range closure
rules: whenever `r : α → ℕ` is computable in logarithmic space with unary output (`encUnary`) and
`f : α × ℕ → β` is computable in logarithmic space on `encPair encIn encUnary`, a single
random-access query machine (`Turing.QueryMachine`) streams `f(a, 0), …, f(a, r a - 1)` by reading
each prefix `frame (encIn a) ++ replicate i true` directly from
`frame (encIn a) ++ replicate (r a) true` through `Turing.VirtualWord.Native.machine`.

## Main results

* `CslibFrontier.Computability.LogSpace.flatMapBits_range_pair`,
  `CslibFrontier.Computability.LogSpace.flatMapBits_range`: streaming bit-word concatenation
  over `List.range (r a)`.
* `CslibFrontier.Computability.LogSpace.map_range`,
  `CslibFrontier.Computability.LogSpace.flatMap_range`,
  `CslibFrontier.Computability.LogSpace.mapToBits_range`: mapping and flat-mapping over
  `List.range (r a)` in logarithmic space.
* `CslibFrontier.Computability.LogSpace.all_range`,
  `CslibFrontier.Computability.LogSpace.any_range`,
  `CslibFrontier.Computability.LogSpace.countP_range`,
  `CslibFrontier.Computability.LogSpace.filter_range`: bounded universal/existential
  quantification, unary population counting, and filtering in logarithmic space.
* `CslibFrontier.Computability.LogSpace.bitsEq`,
  `CslibFrontier.Computability.LogSpace.decideEq`: equality testing on bit words and arbitrary
  injectively encoded types in logarithmic space.
-/

public section

namespace CslibFrontier.Computability.LogSpace

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Turing.MultiTapeTM.ComputableInSpace

/-! ### 1. Streaming Range-Iteration Query Machine -/

/-- State `(phase, base, bound, idx, cfg)` of the range-streaming query machine:
`phase = 0` counts `w.length` via the framed markers, `phase = 1` counts the unary range `k`,
and `phase = 2` simulates `d` on `frame w ++ replicate idx true` for `idx = 0, …, k - 1`. -/
abbrev LogSpaceRangeState : Type := ℕ × ℕ × ℕ × ℕ × SCfg

/-- Encoding of `LogSpaceRangeState` as nested binary naturals paired with `eCfg`. -/
abbrev encLogSpaceRangeState : LogSpaceRangeState ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat eCfg)))

/-- Virtual input bit seen by `d` on `frame w ++ replicate idx true` when reading position
`cfg.inputPos - 1` from `frame w ++ replicate k true` (`base = 2 * w.length + 1`, `idx < k`). -/
def rangeVirtBit (s : LogSpaceRangeState) (b : Option Bool) : Option Bool :=
  if s.2.2.2.2.inputPos - 1 < s.2.1 + s.2.2.2.1 then b else none

/-- Random-access query machine iterating the native configuration adapter of `d` across
`idx = 0, …, k - 1` on `frame w ++ replicate k true`. -/
def logSpaceRangeMachine (d : Desc) : QueryMachine LogSpaceRangeState where
  init := (0, 0, 0, 0, Universal.init d)
  query s :=
    if s.1 = 0 then 2 * s.2.1
    else if s.1 = 1 then s.2.1 + s.2.2.1
    else (VirtualWord.Native.machine d).query s.2.2.2.2
  next p :=
    let s := p.1
    let b := p.2
    if s.1 = 0 then
      if b == some true then (0, s.2.1 + 1, 0, 0, Universal.init d)
      else (1, 2 * s.2.1 + 1, 0, 0, Universal.init d)
    else if s.1 = 1 then
      if b == some true then (1, s.2.1, s.2.2.1 + 1, 0, Universal.init d)
      else (2, s.2.1, s.2.2.1, 0, Universal.init d)
    else if s.1 = 2 then
      if s.2.2.2.1 < s.2.2.1 then
        if (VirtualWord.Native.machine d).halted s.2.2.2.2 then
          (2, s.2.1, s.2.2.1, s.2.2.2.1 + 1, Universal.init d)
        else
          (2, s.2.1, s.2.2.1, s.2.2.2.1,
            (VirtualWord.Native.machine d).next (s.2.2.2.2, rangeVirtBit s b))
      else s
    else s
  emit p :=
    let s := p.1
    let b := p.2
    if s.1 = 2 then
      if s.2.2.2.1 < s.2.2.1 then
        if (VirtualWord.Native.machine d).halted s.2.2.2.2 then []
        else (VirtualWord.Native.machine d).emit (s.2.2.2.2, rangeVirtBit s b)
      else []
    else []
  halted s := decide (s.1 = 2) && decide (s.2.2.1 ≤ s.2.2.2.1)
  finish _ := []

section Components

private lemma rangeVirtBit_inSpace :
    ComputableInSpace (fun p : LogSpaceRangeState × Option Bool ↦ rangeVirtBit p.1 p.2)
      (QueryMachine.encStateRead encLogSpaceRangeState) (encOption encBool)
      (fun p ↦ (QueryMachine.encStateRead encLogSpaceRangeState p).length) := by
  have hs := fst encLogSpaceRangeState (encOption encBool)
  have hb := snd encLogSpaceRangeState (encOption encBool)
  have hs1 := snd' hs
  have hbase := fst' hs1
  have hs2 := snd' hs1
  have hs3 := snd' hs2
  have hidx := fst' hs3
  have hcfg := snd' hs3
  have hpos := budget_natPred (eCfg_inputPos_budget hcfg)
  have hlim := budget_natAdd hbase hidx
  refine (budget_ite (budget_natLt hpos hlim) hb (budget_const none)).of_enc_eq fun p ↦ ?_
  simp only [rangeVirtBit, decide_eq_true_eq]

private lemma logSpaceRangeMachine_components_inSpace (d : Desc) :
    ComputableInSpace (logSpaceRangeMachine d).query encLogSpaceRangeState encNat
      (fun s ↦ (encLogSpaceRangeState s).length) ∧
    ComputableInSpace (logSpaceRangeMachine d).next
      (QueryMachine.encStateRead encLogSpaceRangeState) encLogSpaceRangeState
      (fun p ↦ (QueryMachine.encStateRead encLogSpaceRangeState p).length) ∧
    ComputableInSpace (logSpaceRangeMachine d).emit
      (QueryMachine.encStateRead encLogSpaceRangeState) encBits
      (fun p ↦ (QueryMachine.encStateRead encLogSpaceRangeState p).length) ∧
    ComputableInSpace (logSpaceRangeMachine d).halted encLogSpaceRangeState encBool
      (fun s ↦ (encLogSpaceRangeState s).length) ∧
    ComputableInSpace (logSpaceRangeMachine d).finish encLogSpaceRangeState encBits
      (fun s ↦ (encLogSpaceRangeState s).length) := by
  obtain ⟨hMq, hMn, hMe, hMh, -⟩ := VirtualWord.Native.components_inSpace d
  have hid := budget_id (enc := encLogSpaceRangeState) (.refl _)
  have hph := fst' hid
  have hr1 := snd' hid
  have hbase := fst' hr1
  have hr2 := snd' hr1
  have hbnd := fst' hr2
  have hr3 := snd' hr2
  have hidx := fst' hr3
  have hcfg := snd' hr3
  have hp := fst encLogSpaceRangeState (encOption encBool)
  have hb := snd encLogSpaceRangeState (encOption encBool)
  have hp_ph := fst' hp
  have hp_r1 := snd' hp
  have hp_base := fst' hp_r1
  have hp_r2 := snd' hp_r1
  have hp_bnd := fst' hp_r2
  have hp_r3 := snd' hp_r2
  have hp_idx := fst' hp_r3
  have hp_cfg := snd' hp_r3
  have hvirt := rangeVirtBit_inSpace
  have hsomeTrue : ComputableInSpace (fun p : LogSpaceRangeState × Option Bool ↦
      p.2 == some true) (QueryMachine.encStateRead encLogSpaceRangeState) encBool
      (fun p ↦ (QueryMachine.encStateRead encLogSpaceRangeState p).length) :=
    budget_finite (encC := encBool) (fun o : Option Bool ↦ o == some true) hb
  have mkSt {γ : Type} {encA : γ ↪ List Bool} {B : γ → ℕ}
      {f1 f2 f3 f4 : γ → ℕ} {f5 : γ → SCfg}
      (h1 : ComputableInSpace f1 encA encNat B) (h2 : ComputableInSpace f2 encA encNat B)
      (h3 : ComputableInSpace f3 encA encNat B) (h4 : ComputableInSpace f4 encA encNat B)
      (h5 : ComputableInSpace f5 encA eCfg B) :
      ComputableInSpace (fun a ↦ (f1 a, f2 a, f3 a, f4 a, f5 a))
        encA encLogSpaceRangeState B :=
    budget_prod h1 (budget_prod h2 (budget_prod h3 (budget_prod h4 h5)))
  refine ⟨?_, ?_, ?_, ?_, budget_const []⟩
  · refine (budget_ite (budget_natEq hph (budget_const 0))
      (budget_natMul (budget_const 2) hbase)
      (budget_ite (budget_natEq hph (budget_const 1))
        (budget_natAdd hbase hbnd)
        (budget_comp_linear hMq hcfg))).of_enc_eq fun s ↦ ?_
    simp only [logSpaceRangeMachine, decide_eq_true_eq]
  · have hinitCfg : ComputableInSpace
        (fun _ : LogSpaceRangeState × Option Bool ↦ Universal.init d)
        (QueryMachine.encStateRead encLogSpaceRangeState) eCfg
        (fun p ↦ (QueryMachine.encStateRead encLogSpaceRangeState p).length) :=
      budget_const (Universal.init d)
    have hbr0 := budget_ite hsomeTrue
      (mkSt (budget_const 0) (budget_natAdd hp_base (budget_const 1))
        (budget_const 0) (budget_const 0) hinitCfg)
      (mkSt (budget_const 1)
        (budget_natAdd (budget_natMul (budget_const 2) hp_base) (budget_const 1))
        (budget_const 0) (budget_const 0) hinitCfg)
    have hbr1 := budget_ite hsomeTrue
      (mkSt (budget_const 1) hp_base (budget_natAdd hp_bnd (budget_const 1))
        (budget_const 0) hinitCfg)
      (mkSt (budget_const 2) hp_base hp_bnd (budget_const 0) hinitCfg)
    have hbr2 := budget_ite (budget_natLt hp_idx hp_bnd)
      (budget_ite (budget_comp_linear hMh hp_cfg)
        (mkSt (budget_const 2) hp_base hp_bnd (budget_natAdd hp_idx (budget_const 1)) hinitCfg)
        (mkSt (budget_const 2) hp_base hp_bnd hp_idx
          (budget_comp_linear hMn (budget_prod hp_cfg hvirt))))
      hp
    refine (budget_ite (budget_natEq hp_ph (budget_const 0)) hbr0
      (budget_ite (budget_natEq hp_ph (budget_const 1)) hbr1
        (budget_ite (budget_natEq hp_ph (budget_const 2)) hbr2 hp))).of_enc_eq fun p ↦ ?_
    simp only [logSpaceRangeMachine, decide_eq_true_eq]
  · refine (budget_ite (budget_natEq hp_ph (budget_const 2))
      (budget_ite (budget_natLt hp_idx hp_bnd)
        (budget_ite (budget_comp_linear hMh hp_cfg)
          (budget_const [])
          (budget_comp_linear hMe (budget_prod hp_cfg hvirt)))
        (budget_const []))
      (budget_const [])).of_enc_eq fun p ↦ ?_
    simp only [logSpaceRangeMachine, decide_eq_true_eq]
  · have h2 := budget_natEq hph (budget_const 2)
    have hle : ComputableInSpace (fun s : LogSpaceRangeState ↦ decide (s.2.2.1 ≤ s.2.2.2.1))
        encLogSpaceRangeState encBool (fun s ↦ (encLogSpaceRangeState s).length) := by
      refine (budget_finite (encC := encBool) Bool.not (budget_natLt hidx hbnd)).of_enc_eq
        fun s ↦ ?_
      by_cases h : s.2.2.2.1 < s.2.2.1 <;> simp [h, Nat.not_lt.mp, not_le.mpr]
    exact budget_finite (encC := encBool) (fun q : Bool × Bool ↦ q.1 && q.2) (budget_prod h2 hle)

end Components

section Trace

variable (d : Desc) (w : List Bool) (k : ℕ)

private abbrev fullWord : List Bool := frame w ++ List.replicate k true

private abbrev virtWord (i : ℕ) : List Bool := frame w ++ List.replicate i true

private lemma length_fullWord : (fullWord w k).length = 2 * w.length + 1 + k := by
  simp [fullWord, length_frame]

private lemma fullWord_marker {j : ℕ} (hj : j < w.length) :
    (fullWord w k)[2 * j]? = some true := by
  rw [fullWord, List.getElem?_append_left (by rw [length_frame]; omega)]
  exact getElem?_frame_two_mul hj

private lemma fullWord_end_frame :
    (fullWord w k)[2 * w.length]? = some false := by
  rw [fullWord, List.getElem?_append_left (by rw [length_frame]; omega)]
  exact getElem?_frame_two_mul_length w

private lemma fullWord_unary {r : ℕ} (hr : r < k) :
    (fullWord w k)[2 * w.length + 1 + r]? = some true := by
  rw [fullWord, List.getElem?_append_right (by rw [length_frame]; omega)]
  simp [length_frame, hr]

private lemma fullWord_after :
    (fullWord w k)[2 * w.length + 1 + k]? = none := by
  rw [List.getElem?_eq_none]
  rw [length_fullWord]

private lemma rangeVirtBit_read_eq {i : ℕ} (hi : i ≤ k) (cfg : SCfg) :
    rangeVirtBit (2, 2 * w.length + 1, k, i, cfg)
      ((logSpaceRangeMachine d).read (fullWord w k) (2, 2 * w.length + 1, k, i, cfg)) =
      (VirtualWord.Native.machine d).read (virtWord w i) cfg := by
  have hvlen : (virtWord w i).length = 2 * w.length + 1 + i := by
    simp [virtWord, length_frame]
  simp only [rangeVirtBit, QueryMachine.read, logSpaceRangeMachine, VirtualWord.Native.machine]
  by_cases hlt : cfg.inputPos - 1 < 2 * w.length + 1 + i
  · simp only [hlt, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    by_cases hframe : cfg.inputPos - 1 < 2 * w.length + 1
    · rw [fullWord, virtWord,
        List.getElem?_append_left (by rw [length_frame]; omega),
        List.getElem?_append_left (by rw [length_frame]; omega)]
    · rw [fullWord, virtWord,
        List.getElem?_append_right (by rw [length_frame]; omega),
        List.getElem?_append_right (by rw [length_frame]; omega)]
      have h1 : cfg.inputPos - 1 - (frame w).length < (List.replicate k true).length := by
        rw [length_frame, List.length_replicate]; omega
      have h2 : cfg.inputPos - 1 - (frame w).length < (List.replicate i true).length := by
        rw [length_frame, List.length_replicate]; omega
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
        List.getElem_replicate, List.getElem_replicate]
  · simp only [hlt, ↓reduceIte]
    symm
    exact List.getElem?_eq_none (by omega)

private lemma runFrom_phase0 :
    ∀ j ≤ w.length,
      (logSpaceRangeMachine d).runFrom (fullWord w k) (0, 0, 0, 0, Universal.init d) j =
        (0, j, 0, 0, Universal.init d) ∧
      (∀ t < j,
        (logSpaceRangeMachine d).halted
          ((logSpaceRangeMachine d).runFrom (fullWord w k) (0, 0, 0, 0, Universal.init d) t) =
          false ∧
        (logSpaceRangeMachine d).emit
          ((logSpaceRangeMachine d).runFrom (fullWord w k) (0, 0, 0, 0, Universal.init d) t,
            (logSpaceRangeMachine d).read (fullWord w k)
              ((logSpaceRangeMachine d).runFrom (fullWord w k) (0, 0, 0, 0, Universal.init d) t)) =
          [])
  | 0, _ => ⟨rfl, fun _ ht ↦ absurd ht (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨hrun, hpre⟩ := runFrom_phase0 j (by omega)
    have hread : (logSpaceRangeMachine d).read (fullWord w k) (0, j, 0, 0, Universal.init d) =
        some true := by
      simp [QueryMachine.read, logSpaceRangeMachine, fullWord_marker w k (by omega : j < w.length)]
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [QueryMachine.runFrom_succ, hrun, QueryMachine.step, hread]
      simp [logSpaceRangeMachine]
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
      · exact hpre t hlt
      · rw [hrun]
        simp [logSpaceRangeMachine]

private lemma step_phase0_end :
    (logSpaceRangeMachine d).step (fullWord w k) (0, w.length, 0, 0, Universal.init d) =
      (1, 2 * w.length + 1, 0, 0, Universal.init d) := by
  have hread : (logSpaceRangeMachine d).read (fullWord w k) (0, w.length, 0, 0, Universal.init d) =
      some false := by
    simp [QueryMachine.read, logSpaceRangeMachine, fullWord_end_frame w k]
  rw [QueryMachine.step, hread]
  simp [logSpaceRangeMachine]

private lemma runFrom_phase1 :
    ∀ r ≤ k,
      (logSpaceRangeMachine d).runFrom (fullWord w k)
        (1, 2 * w.length + 1, 0, 0, Universal.init d) r =
        (1, 2 * w.length + 1, r, 0, Universal.init d) ∧
      (∀ t < r,
        (logSpaceRangeMachine d).halted
          ((logSpaceRangeMachine d).runFrom (fullWord w k)
            (1, 2 * w.length + 1, 0, 0, Universal.init d) t) = false ∧
        (logSpaceRangeMachine d).emit
          ((logSpaceRangeMachine d).runFrom (fullWord w k)
            (1, 2 * w.length + 1, 0, 0, Universal.init d) t,
            (logSpaceRangeMachine d).read (fullWord w k)
              ((logSpaceRangeMachine d).runFrom (fullWord w k)
                (1, 2 * w.length + 1, 0, 0, Universal.init d) t)) = [])
  | 0, _ => ⟨rfl, fun _ ht ↦ absurd ht (Nat.not_lt_zero _)⟩
  | r + 1, hr => by
    obtain ⟨hrun, hpre⟩ := runFrom_phase1 r (by omega)
    have hread : (logSpaceRangeMachine d).read (fullWord w k)
        (1, 2 * w.length + 1, r, 0, Universal.init d) = some true := by
      simp [QueryMachine.read, logSpaceRangeMachine, fullWord_unary w k (by omega : r < k)]
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [QueryMachine.runFrom_succ, hrun, QueryMachine.step, hread]
      simp [logSpaceRangeMachine]
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with hlt | rfl
      · exact hpre t hlt
      · rw [hrun]
        simp [logSpaceRangeMachine]

private lemma step_phase1_end :
    (logSpaceRangeMachine d).step (fullWord w k) (1, 2 * w.length + 1, k, 0, Universal.init d) =
      (2, 2 * w.length + 1, k, 0, Universal.init d) := by
  have hread : (logSpaceRangeMachine d).read (fullWord w k)
      (1, 2 * w.length + 1, k, 0, Universal.init d) = none := by
    change (fullWord w k)[2 * w.length + 1 + k]? = none
    exact fullWord_after w k
  rw [QueryMachine.step, hread]
  simp [logSpaceRangeMachine]

private lemma runFrom_round {i τ : ℕ} (hi : i < k)
    (hpre_d : ∀ t < τ,
      (VirtualWord.Native.machine d).halted
        ((VirtualWord.Native.machine d).run (virtWord w i) t) = false) :
    ∀ t ≤ τ,
      (logSpaceRangeMachine d).runFrom (fullWord w k)
        (2, 2 * w.length + 1, k, i, Universal.init d) t =
        (2, 2 * w.length + 1, k, i, (VirtualWord.Native.machine d).run (virtWord w i) t)
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := runFrom_round hi hpre_d t (by omega)
    have hnh : (VirtualWord.Native.machine d).halted
        ((VirtualWord.Native.machine d).run (virtWord w i) t) = false :=
      hpre_d t (by omega)
    have hnh_outer : (logSpaceRangeMachine d).halted
        (2, 2 * w.length + 1, k, i, (VirtualWord.Native.machine d).run (virtWord w i) t) =
        false := by
      simp [logSpaceRangeMachine, Nat.not_le.mpr hi]
    have hnext : ∀ (cfg : SCfg) (b : Option Bool),
        (VirtualWord.Native.machine d).halted cfg = false →
        (logSpaceRangeMachine d).next ((2, 2 * w.length + 1, k, i, cfg), b) =
          (2, 2 * w.length + 1, k, i,
            (VirtualWord.Native.machine d).next
              (cfg, rangeVirtBit (2, 2 * w.length + 1, k, i, cfg) b)) := by
      intro cfg b hh
      simp [logSpaceRangeMachine, hi, hh]
    rw [QueryMachine.runFrom_succ, ih, QueryMachine.step, hnh_outer]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hnext _ _ hnh, rangeVirtBit_read_eq d w k hi.le,
      QueryMachine.run_succ, QueryMachine.step, hnh]
    simp only [Bool.false_eq_true, ↓reduceIte]

private lemma step_round_end {i τ : ℕ} (hi : i < k)
    (hhalt_d : (VirtualWord.Native.machine d).halted
      ((VirtualWord.Native.machine d).run (virtWord w i) τ) = true) :
    (logSpaceRangeMachine d).step (fullWord w k)
      (2, 2 * w.length + 1, k, i, (VirtualWord.Native.machine d).run (virtWord w i) τ) =
      (2, 2 * w.length + 1, k, i + 1, Universal.init d) := by
  have hnh_outer : (logSpaceRangeMachine d).halted
      (2, 2 * w.length + 1, k, i, (VirtualWord.Native.machine d).run (virtWord w i) τ) = false := by
    simp [logSpaceRangeMachine, Nat.not_le.mpr hi]
  rw [QueryMachine.step, hnh_outer]
  simp [logSpaceRangeMachine, hi, hhalt_d]

end Trace

/-! ### 2. Unbounded Polynomial-Range Iteration in Logarithmic Space -/

/-- Concatenating `f (a, 0), …, f (a, k - 1)` for a logarithmic-space bit-word family
`f : α × ℕ → List Bool` is computable in logarithmic space on `encPair encIn encUnary`. -/
theorem flatMapBits_range_pair {α : Type} {encIn : α ↪ List Bool}
    {f : α × ℕ → List Bool}
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBits) :
    ComputableInLogSpace
      (fun p : α × ℕ ↦ ((List.range p.2).map fun i ↦ f (p.1, i)).flatten)
      (encPair encIn encUnary) encBits := by
  classical
  obtain ⟨_, cf, _, Sf, hfinS, tmf, htmf⟩ := hf
  let _ : Fintype Sf := Fintype.ofFinite Sf
  let eS : Sf ↪ ℕ := (Fintype.equivFin Sf).toEmbedding.trans Fin.valEmbedding
  set df : Desc := Universal.desc eS Universal.eBit tmf
  let M := logSpaceRangeMachine df
  have hex (a : α) (i : ℕ) :
      ∃ t, (tmf.runFrom (tmf.initCfg (virtWord (encIn a) i)) t).state = none :=
    ⟨_, ((htmf (a, i)).1).choose_spec.1⟩
  let τ (a : α) (i : ℕ) : ℕ := Nat.find (hex a i)
  have hhalt_d (a : α) (i : ℕ) :
      (VirtualWord.Native.machine df).halted
        ((VirtualWord.Native.machine df).run (virtWord (encIn a) i) (τ a i)) = true := by
    rw [VirtualWord.Native.halted_native]
    exact Option.isNone_iff_eq_none.mpr (Nat.find_spec (hex a i))
  have hpre_d (a : α) (i : ℕ) :
      ∀ t < τ a i,
        (VirtualWord.Native.machine df).halted
          ((VirtualWord.Native.machine df).run (virtWord (encIn a) i) t) = false := by
    intro t ht
    rw [VirtualWord.Native.halted_native, Option.isNone_eq_false_iff, Option.isSome_iff_ne_none]
    exact Nat.find_min (hex a i) ht
  have hout_d (a : α) (i : ℕ) :
      (VirtualWord.Native.machine df).output (virtWord (encIn a) i) (τ a i) = f (a, i) := by
    rw [VirtualWord.Native.output_native]
    obtain ⟨t_out, ht_halt, ht_out⟩ := (htmf (a, i)).1
    have hvw_eq : encPair encIn encUnary (a, i) = virtWord (encIn a) i := rfl
    rw [hvw_eq] at ht_halt ht_out
    have hle : τ a i ≤ t_out := Nat.find_min' (hex a i) ht_halt
    rw [tmf.runFrom_eq_of_halt _ hle (Nat.find_spec (hex a i))] at ht_out
    simpa only [encBits_apply] using ht_out
  let roundSteps (a : α) (m : ℕ) : ℕ :=
    ((List.range m).map fun i ↦ τ a i + 1).sum
  let totalTime (p : α × ℕ) : ℕ :=
    ((encIn p.1).length + 1) + (p.2 + 1) + roundSteps p.1 p.2
  have hcomp := logSpaceRangeMachine_components_inSpace df
  have hphase2 (a : α) (k : ℕ) :
      ∀ m ≤ k,
        M.runFrom (fullWord (encIn a) k)
          (2, 2 * (encIn a).length + 1, k, 0, Universal.init df)
          (roundSteps a m) = (2, 2 * (encIn a).length + 1, k, m, Universal.init df) ∧
        (∀ t < roundSteps a m,
          M.halted (M.runFrom (fullWord (encIn a) k)
            (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) t) = false ∧
          ∃ i < m, ∃ u ≤ τ a i,
            M.runFrom (fullWord (encIn a) k)
              (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) t =
              (2, 2 * (encIn a).length + 1, k, i,
                (VirtualWord.Native.machine df).run (virtWord (encIn a) i) u)) ∧
        ((List.range (roundSteps a m)).map fun t ↦
          let st := M.runFrom (fullWord (encIn a) k)
            (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) t
          M.emit (st, M.read (fullWord (encIn a) k) st)).flatten =
          ((List.range m).map fun i ↦ f (a, i)).flatten := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨rfl, fun _ ht ↦ absurd ht (Nat.not_lt_zero _), rfl⟩
    | succ m ih =>
      obtain ⟨hrun_m, hpre_m, hout_m⟩ := ih (by omega)
      have hm_lt : m < k := Nat.lt_of_succ_le hm
      have hrs : roundSteps a (m + 1) = roundSteps a m + (τ a m + 1) := by
        simp only [roundSteps, List.range_succ, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton]
      have hround_run : ∀ u ≤ τ a m,
          M.runFrom (fullWord (encIn a) k)
            (2, 2 * (encIn a).length + 1, k, 0, Universal.init df)
            (roundSteps a m + u) =
            (2, 2 * (encIn a).length + 1, k, m,
              (VirtualWord.Native.machine df).run (virtWord (encIn a) m) u) := by
        intro u hu
        rw [QueryMachine.runFrom_add, hrun_m]
        exact runFrom_round df (encIn a) k hm_lt (hpre_d a m) u hu
      have hend : M.runFrom (fullWord (encIn a) k)
          (2, 2 * (encIn a).length + 1, k, 0, Universal.init df)
          (roundSteps a (m + 1)) =
          (2, 2 * (encIn a).length + 1, k, m + 1, Universal.init df) := by
        rw [hrs, ← Nat.add_assoc, QueryMachine.runFrom_succ, hround_run (τ a m) le_rfl]
        exact step_round_end df (encIn a) k hm_lt (hhalt_d a m)
      refine ⟨hend, fun t ht ↦ ?_, ?_⟩
      · rw [hrs] at ht
        rcases lt_or_ge t (roundSteps a m) with hlt | hge
        · obtain ⟨hnh, i, hi, u, hu, hst⟩ := hpre_m t hlt
          exact ⟨hnh, i, Nat.lt_succ_of_lt hi, u, hu, hst⟩
        · set u := t - roundSteps a m
          have hu_le : u ≤ τ a m := by omega
          have htu : t = roundSteps a m + u := by omega
          rw [htu, hround_run u hu_le]
          refine ⟨by simp [M, logSpaceRangeMachine, Nat.not_le.mpr hm_lt],
            m, Nat.lt_succ_self m, u, hu_le, rfl⟩
      · rw [hrs, List.range_add, List.map_append, List.flatten_append, hout_m,
          List.range_succ (n := m), List.map_append, List.flatten_append, List.map_singleton,
          List.flatten_singleton]
        congr 1
        rw [List.range_succ, List.map_append, List.map_append, List.flatten_append,
          List.map_singleton, List.map_singleton, List.flatten_singleton]
        have hlast : M.emit
              (M.runFrom (fullWord (encIn a) k)
                (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) (roundSteps a m + τ a m),
               M.read (fullWord (encIn a) k)
                (M.runFrom (fullWord (encIn a) k)
                  (2, 2 * (encIn a).length + 1, k, 0, Universal.init df)
                  (roundSteps a m + τ a m))) = [] := by
          rw [hround_run (τ a m) le_rfl]
          simp [M, logSpaceRangeMachine, hm_lt, hhalt_d a m]
        rw [List.map_map]
        change ((List.range (τ a m)).map fun u ↦
            M.emit
              (M.runFrom (fullWord (encIn a) k)
                (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) (roundSteps a m + u),
               M.read (fullWord (encIn a) k)
                (M.runFrom (fullWord (encIn a) k)
                  (2, 2 * (encIn a).length + 1, k, 0, Universal.init df)
                  (roundSteps a m + u)))).flatten ++
          M.emit
            (M.runFrom (fullWord (encIn a) k)
              (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) (roundSteps a m + τ a m),
             M.read (fullWord (encIn a) k)
              (M.runFrom (fullWord (encIn a) k)
                (2, 2 * (encIn a).length + 1, k, 0, Universal.init df)
                (roundSteps a m + τ a m))) = f (a, m)
        rw [hlast, List.append_nil, ← hout_d a m,
          (VirtualWord.Native.machine df).output_eq_of_not_halted
            (virtWord (encIn a) m) (hpre_d a m)]
        simp only [show (VirtualWord.Native.machine df).finish = fun _ ↦ [] from rfl,
          List.append_nil]
        congr 1
        refine List.map_congr_left fun u hu ↦ ?_
        have hu_lt : u < τ a m := List.mem_range.mp hu
        have hemit : ∀ (cfg : SCfg) (b : Option Bool),
            (VirtualWord.Native.machine df).halted cfg = false →
            M.emit ((2, 2 * (encIn a).length + 1, k, m, cfg), b) =
              (VirtualWord.Native.machine df).emit
                (cfg, rangeVirtBit (2, 2 * (encIn a).length + 1, k, m, cfg) b) := by
          intro cfg b hh
          simp [M, logSpaceRangeMachine, hm_lt, hh]
        rw [hround_run u hu_lt.le, hemit _ _ (hpre_d a m u hu_lt),
          rangeVirtBit_read_eq df (encIn a) k hm_lt.le]
  have hprefix01 (a : α) (k : ℕ) :
      M.run (fullWord (encIn a) k) (((encIn a).length + 1) + (k + 1)) =
        (2, 2 * (encIn a).length + 1, k, 0, Universal.init df) := by
    change (logSpaceRangeMachine df).runFrom (fullWord (encIn a) k)
      (0, 0, 0, 0, Universal.init df) (((encIn a).length + 1) + (k + 1)) = _
    rw [QueryMachine.runFrom_add]
    have hp0 : (logSpaceRangeMachine df).runFrom (fullWord (encIn a) k)
        (0, 0, 0, 0, Universal.init df) ((encIn a).length + 1) =
        (1, 2 * (encIn a).length + 1, 0, 0, Universal.init df) := by
      rw [QueryMachine.runFrom_succ, (runFrom_phase0 df (encIn a) k (encIn a).length le_rfl).1]
      exact step_phase0_end df (encIn a) k
    rw [hp0, QueryMachine.runFrom_succ, (runFrom_phase1 df (encIn a) k k le_rfl).1]
    exact step_phase1_end df (encIn a) k
  have hall_trace (p : α × ℕ) :
      let a := p.1
      let k := p.2
      M.run (fullWord (encIn a) k) (totalTime p) =
        (2, 2 * (encIn a).length + 1, k, k, Universal.init df) ∧
      (∀ t < totalTime p, M.halted (M.run (fullWord (encIn a) k) t) = false) ∧
      M.output (fullWord (encIn a) k) (totalTime p) =
        ((List.range k).map fun i ↦ f (a, i)).flatten ∧
      (∀ t ≤ totalTime p,
        ∃ ph ≤ 2, ∃ bnd ≤ 2 * (encIn a).length + 1, ∃ kk ≤ k, ∃ idx ≤ k,
          M.run (fullWord (encIn a) k) t =
            (ph, bnd, kk, idx, (M.run (fullWord (encIn a) k) t).2.2.2.2) ∧
          ((M.run (fullWord (encIn a) k) t).2.2.2.2 = Universal.init df ∨
            ∃ i < k, ∃ u ≤ τ a i,
              (M.run (fullWord (encIn a) k) t).2.2.2.2 =
                (VirtualWord.Native.machine df).run (virtWord (encIn a) i) u)) := by
    rcases p with ⟨a, k⟩
    set w := encIn a
    dsimp only [totalTime]
    obtain ⟨hrun2, hpre2, hout2⟩ := hphase2 a k k le_rfl
    have hfinal : M.run (fullWord w k) ((w.length + 1) + (k + 1) + roundSteps a k) =
        (2, 2 * w.length + 1, k, k, Universal.init df) := by
      change M.runFrom (fullWord w k) M.init _ = _
      rw [QueryMachine.runFrom_add, show M.runFrom (fullWord w k) M.init _ =
        M.run (fullWord w k) _ from rfl, hprefix01 a k, hrun2]
    have hstate_pre : ∀ t ≤ (w.length + 1) + (k + 1) + roundSteps a k,
        (t < (w.length + 1) + (k + 1) + roundSteps a k →
          M.halted (M.run (fullWord w k) t) = false ∧
          (t < (w.length + 1) + (k + 1) →
            M.emit (M.run (fullWord w k) t, M.read (fullWord w k) (M.run (fullWord w k) t)) =
              [])) ∧
        ∃ ph ≤ 2, ∃ bnd ≤ 2 * w.length + 1, ∃ kk ≤ k, ∃ idx ≤ k,
          M.run (fullWord w k) t = (ph, bnd, kk, idx, (M.run (fullWord w k) t).2.2.2.2) ∧
          ((M.run (fullWord w k) t).2.2.2.2 = Universal.init df ∨
            ∃ i < k, ∃ u ≤ τ a i,
              (M.run (fullWord w k) t).2.2.2.2 =
                (VirtualWord.Native.machine df).run (virtWord w i) u) := by
      intro t ht
      rcases lt_or_ge t (w.length + 1) with ht0 | ht1
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ht0) with hlt0 | rfl
        · have hr : M.run (fullWord w k) t = (0, t, 0, 0, Universal.init df) :=
            (runFrom_phase0 df w k t (by omega)).1
          rw [hr]
          exact ⟨fun _ ↦ ⟨by simp [M, logSpaceRangeMachine],
              fun _ ↦ by simp [M, logSpaceRangeMachine]⟩,
            0, by omega, t, by omega, 0, by omega, 0, by omega, rfl, Or.inl rfl⟩
        · have hr : M.run (fullWord w k) w.length = (0, w.length, 0, 0, Universal.init df) :=
            (runFrom_phase0 df w k w.length le_rfl).1
          rw [hr]
          exact ⟨fun _ ↦ ⟨by simp [M, logSpaceRangeMachine],
              fun _ ↦ by simp [M, logSpaceRangeMachine]⟩,
            0, by omega, w.length, by omega, 0, by omega, 0, by omega, rfl, Or.inl rfl⟩
      · rcases lt_or_ge t ((w.length + 1) + (k + 1)) with ht1' | ht2
        · set r := t - (w.length + 1)
          have hr_eq : t = (w.length + 1) + r := by omega
          have hp0 : M.runFrom (fullWord w k) M.init (w.length + 1) =
              (1, 2 * w.length + 1, 0, 0, Universal.init df) := by
            change (logSpaceRangeMachine df).runFrom (fullWord w k)
              (0, 0, 0, 0, Universal.init df) (w.length + 1) = _
            rw [QueryMachine.runFrom_succ, (runFrom_phase0 df w k w.length le_rfl).1]
            exact step_phase0_end df w k
          have hrun_r : M.run (fullWord w k) t =
              M.runFrom (fullWord w k) (1, 2 * w.length + 1, 0, 0, Universal.init df) r := by
            change M.runFrom (fullWord w k) M.init t = _
            rw [hr_eq, QueryMachine.runFrom_add, hp0]
          rcases lt_or_eq_of_le (show r ≤ k by omega) with hrl | hreq
          · have hr1 := (runFrom_phase1 df w k r hrl.le).1
            rw [hrun_r, hr1]
            exact ⟨fun _ ↦ ⟨by simp [M, logSpaceRangeMachine],
                fun _ ↦ by simp [M, logSpaceRangeMachine]⟩,
              1, by omega, 2 * w.length + 1, le_rfl, r, hrl.le, 0, by omega, rfl, Or.inl rfl⟩
          · have hr1 := (runFrom_phase1 df w k k le_rfl).1
            rw [hrun_r, hreq, hr1]
            exact ⟨fun _ ↦ ⟨by simp [M, logSpaceRangeMachine],
                fun _ ↦ by simp [M, logSpaceRangeMachine]⟩,
              1, by omega, 2 * w.length + 1, le_rfl, k, le_rfl, 0, by omega, rfl, Or.inl rfl⟩
        · set s2 := t - ((w.length + 1) + (k + 1))
          have hs2_eq : t = ((w.length + 1) + (k + 1)) + s2 := by omega
          have hrun_s2 : M.run (fullWord w k) t =
              M.runFrom (fullWord w k) (2, 2 * w.length + 1, k, 0, Universal.init df) s2 := by
            change M.runFrom (fullWord w k) M.init t = _
            rw [hs2_eq, QueryMachine.runFrom_add]
            change M.runFrom (fullWord w k) (M.run (fullWord w k) _) s2 = _
            rw [hprefix01 a k]
          rcases lt_or_eq_of_le (show s2 ≤ roundSteps a k by omega) with hs2_lt | hs2_end
          · obtain ⟨hnh, i, hi, u, hu, hst⟩ := hpre2 s2 hs2_lt
            rw [hrun_s2, hst]
            exact ⟨fun _ ↦ ⟨by simpa [hst] using hnh, fun hbad ↦ absurd hbad (by omega)⟩,
              2, le_rfl, 2 * w.length + 1, le_rfl, k, le_rfl, i, hi.le, rfl,
              Or.inr ⟨i, hi, u, hu, rfl⟩⟩
          · rw [hrun_s2, hs2_end, hrun2]
            exact ⟨fun hbad ↦ absurd hbad (by omega),
              2, le_rfl, 2 * w.length + 1, le_rfl, k, le_rfl, k, le_rfl, rfl, Or.inl rfl⟩
    have hpre_only : ∀ t < (w.length + 1) + (k + 1) + roundSteps a k,
        M.halted (M.run (fullWord w k) t) = false :=
      fun t ht ↦ (hstate_pre t ht.le).1 ht |>.1
    refine ⟨hfinal, hpre_only, ?_, fun t ht ↦ (hstate_pre t ht).2⟩
    rw [M.output_eq_of_not_halted (fullWord w k) hpre_only]
    simp only [show M.finish = fun _ ↦ [] from rfl, List.append_nil]
    rw [List.range_add, List.map_append, List.flatten_append]
    have hzero_pre : ((List.range ((w.length + 1) + (k + 1))).map fun t ↦
        M.emit (M.run (fullWord w k) t, M.read (fullWord w k) (M.run (fullWord w k) t))).flatten =
        [] := by
      rw [List.flatten_eq_nil_iff]
      intro l hl
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
      have ht_lt : t < (w.length + 1) + (k + 1) := List.mem_range.mp ht
      exact ((hstate_pre t (by omega)).1 (by omega)).2 ht_lt
    rw [hzero_pre, List.nil_append, List.map_map, ← hout2]
    congr 1
    refine List.map_congr_left fun s2 hs2 ↦ ?_
    change M.emit (M.run (fullWord w k) (((w.length + 1) + (k + 1)) + s2), _) = _
    have heq : M.run (fullWord w k) (((w.length + 1) + (k + 1)) + s2) =
        M.runFrom (fullWord w k) (2, 2 * w.length + 1, k, 0, Universal.init df) s2 := by
      change M.runFrom (fullWord w k) M.init _ = _
      rw [QueryMachine.runFrom_add]
      change M.runFrom (fullWord w k) (M.run (fullWord w k) _) s2 = _
      rw [hprefix01 a k]
    rw [heq]
  obtain ⟨C_b, hCb⟩ := VirtualWord.Native.budget_le eS tmf
  set C₀ : ℕ := (eCfg (Universal.init df)).length + C_b * (cf + 2) + 2
  have henc_eq (p : α × ℕ) : encPair encIn encUnary p = fullWord (encIn p.1) p.2 := rfl
  refine M.computableInLogSpace hcomp.1 hcomp.2.1 hcomp.2.2.1 hcomp.2.2.2.1 hcomp.2.2.2.2
    totalTime
    (fun p ↦ by
      rw [henc_eq, (hall_trace p).1]
      simp [M, logSpaceRangeMachine])
    (fun p t ht ↦ by
      rw [henc_eq]
      exact (hall_trace p).2.1 t ht)
    (fun p ↦ by
      rw [henc_eq, encBits_apply]
      exact ((hall_trace p).2.2.1).symm)
    ⟨16 * C₀ + 40, fun p t ht ↦ ?_⟩
  rcases p with ⟨a, k⟩
  obtain ⟨ph, hph, bnd, hbnd, kk, hkk, idx, hidx, hst_eq, hcfg_cases⟩ :=
    (hall_trace (a, k)).2.2.2 t ht
  dsimp only at hbnd hkk hidx hst_eq hcfg_cases
  set w := encIn a
  rw [henc_eq (a, k)]
  set L : ℕ := Nat.log2 (fullWord w k).length + 1
  have hL1 : 1 ≤ L := Nat.le_add_left _ _
  have hXlen : (fullWord w k).length = 2 * w.length + 1 + k := length_fullWord w k
  have hnat_bound (x : ℕ) (hx : x ≤ (fullWord w k).length) :
      (encNat x).length ≤ L :=
    length_encNat_le_log2 hx
  have he1 : (encNat ph).length ≤ 3 * L := by
    have : (encNat ph).length ≤ 2 :=
      length_encNat_le_of_lt_two_pow (p := 2) (by omega)
    omega
  have he2 : (encNat bnd).length ≤ L := hnat_bound bnd (by omega)
  have he3 : (encNat kk).length ≤ L := hnat_bound kk (by omega)
  have he4 : (encNat idx).length ≤ L := hnat_bound idx (by omega)
  have he5 : (eCfg (M.run (fullWord w k) t).2.2.2.2).length ≤ C₀ * L := by
    rcases hcfg_cases with hinit_eq | ⟨i, hi, u, -, hrun_eq⟩
    · rw [hinit_eq]
      exact (show (eCfg (Universal.init df)).length ≤ C₀ by dsimp only [C₀]; omega).trans
        (Nat.le_mul_of_pos_right C₀ hL1)
    · rw [hrun_eq]
      have hVi : (virtWord w i).length ≤ (fullWord w k).length := by
        rw [hXlen]
        simp only [virtWord, List.length_append, length_frame, List.length_replicate]
        omega
      have hsp := (VirtualWord.Native.length_native_run_le_of_space eS tmf (virtWord w i) u
        (cf * (Nat.log2 (virtWord w i).length + 1)) (htmf (a, i)).2.2).trans
        (hCb (virtWord w i).length (cf * (Nat.log2 (virtWord w i).length + 1)))
      have hlog_mono : Nat.log2 (virtWord w i).length + 1 ≤ L := by
        dsimp only [L]
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
        exact Nat.add_le_add_right (Nat.log_mono_right hVi) 1
      calc (eCfg ((VirtualWord.Native.machine df).run (virtWord w i) u)).length
          ≤ C_b * (cf * (Nat.log2 (virtWord w i).length + 1) +
              (Nat.log2 (virtWord w i).length + 1)) := by
            simpa [Nat.add_assoc] using hsp
        _ = C_b * (cf + 1) * (Nat.log2 (virtWord w i).length + 1) := by ring
        _ ≤ C_b * (cf + 1) * L := Nat.mul_le_mul_left _ hlog_mono
        _ ≤ C₀ * L := Nat.mul_le_mul_right L (by dsimp only [C₀]; nlinarith)
  change (encLogSpaceRangeState (M.run (fullWord w k) t)).length ≤ (16 * C₀ + 40) * L
  rw [hst_eq]
  simp only [encLogSpaceRangeState, length_encPair]
  nlinarith

/-! ### 3. Derived Logarithmic-Space Range and Equality Combinators -/

section Combinators

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- Concatenating `f (a, 0), …, f (a, r a - 1)` in logarithmic space for any logspace unary
count `r : α → ℕ` and logspace bit-word family `f : α × ℕ → List Bool`. -/
theorem flatMapBits_range {r : α → ℕ} {f : α × ℕ → List Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBits) :
    ComputableInLogSpace
      (fun a ↦ ((List.range (r a)).map fun i ↦ f (a, i)).flatten) encIn encBits :=
  (flatMapBits_range_pair hf).comp (ComputableInLogSpace.pair .id hr)

/-- Mapping a logarithmic-space family `f : α × ℕ → β` over `List.range (r a)`, where `r : α → ℕ`
is computable in logarithmic space with unary output, is computable in logarithmic space. -/
theorem map_range {r : α → ℕ} {f : α × ℕ → β}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encOut) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).map fun i ↦ f (a, i))
      encIn (encList encOut) := by
  have hg : ComputableInLogSpace (fun p : α × ℕ ↦ frame (encOut (f p)))
      (encPair encIn encUnary) encBits :=
    ComputableInLogSpace.frame.comp hf.encoding_comp
  refine (flatMapBits_range hr hg).congr fun a ↦ ?_
  change (List.map (fun i ↦ f (a, i)) (List.range (r a))).flatMap (frame ∘ encOut) = _
  rw [List.flatMap_map]
  rfl

/-- Flat-mapping a logarithmic-space list family `f : α × ℕ → List β` over `List.range (r a)` is
computable in logarithmic space. -/
theorem flatMap_range {r : α → ℕ} {f : α × ℕ → List β}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) (encList encOut)) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).flatMap fun i ↦ f (a, i))
      encIn (encList encOut) := by
  refine (flatMapBits_range hr hf.encoding_comp).congr fun a ↦ ?_
  change ((List.range (r a)).flatMap fun i ↦ f (a, i)).flatMap (frame ∘ encOut) =
    ((List.range (r a)).map fun i ↦ (f (a, i)).flatMap (frame ∘ encOut)).flatten
  induction (List.range (r a)) with
  | nil => rfl
  | cons i is ih => simp [List.flatMap_cons, List.flatMap_append, ih]

/-- Mapping a logarithmic-space Boolean family `f : α × ℕ → Bool` over `List.range (r a)` into a
raw bit word (`encBits`) is computable in logarithmic space. -/
theorem mapToBits_range {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).map fun i ↦ f (a, i)) encIn encBits := by
  refine (flatMapBits_range hr hf.encoding_comp).congr fun a ↦ ?_
  change (List.range (r a)).map (fun i ↦ f (a, i)) =
    ((List.range (r a)).map fun i ↦ [f (a, i)]).flatten
  induction (List.range (r a)) with
  | nil => rfl
  | cons i is ih => simp [ ← ih]

/-- Universal quantification `(List.range (r a)).all (fun i ↦ f (a, i))` in logarithmic space. -/
theorem all_range {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).all fun i ↦ f (a, i)) encIn encBool := by
  refine ((ComputableInLogSpace.bitsAll _root_.id).comp
    (mapToBits_range hr hf)).congr_fun fun a ↦ ?_
  simp [List.all_map]

/-- Existential quantification `(List.range (r a)).any (fun i ↦ f (a, i))` in logarithmic space. -/
theorem any_range {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).any fun i ↦ f (a, i)) encIn encBool := by
  refine ((ComputableInLogSpace.bitsAny _root_.id).comp
    (mapToBits_range hr hf)).congr_fun fun a ↦ ?_
  simp [List.any_map]

private def keepTrueTransducer : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), if b then [true] else [])
  final _ := []
  length_step_le _ b := by cases b <;> simp
  length_final_le _ := by simp

private lemma keepTrueTransducer_run (xs : List Bool) :
    keepTrueTransducer.run () xs = List.replicate (xs.countP _root_.id) true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [Transducer.run_cons, ih]
    cases b <;> simp [keepTrueTransducer, List.replicate_succ]

/-- Counting `(List.range (r a)).countP (fun i ↦ f (a, i))` with unary output (`encUnary`) in
logarithmic space. -/
theorem countP_range {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).countP fun i ↦ f (a, i))
      encIn encUnary := by
  have hkeep : ComputableInLogSpace (fun xs : List Bool ↦ xs.countP _root_.id) encBits encUnary :=
    keepTrueTransducer.computableInLogSpace fun xs ↦ (keepTrueTransducer_run xs).symm
  refine (hkeep.comp (mapToBits_range hr hf)).congr_fun fun a ↦ ?_
  simp [List.countP_map]

/-- Filtering `(List.range (r a)).filter (fun i ↦ f (a, i))` into `encList encUnary` in
logarithmic space. -/
theorem filter_range {r : α → ℕ} {f : α × ℕ → Bool}
    (hr : ComputableInLogSpace r encIn encUnary)
    (hf : ComputableInLogSpace f (encPair encIn encUnary) encBool) :
    ComputableInLogSpace (fun a ↦ (List.range (r a)).filter fun i ↦ f (a, i))
      encIn (encList encUnary) := by
  have hbody : ComputableInLogSpace
      (fun p : α × ℕ ↦ if f p then [p.2] else ([] : List ℕ))
      (encPair encIn encUnary) (encList encUnary) :=
    ComputableInLogSpace.ite hf
      (ComputableInLogSpace.listSingleton.comp (ComputableInLogSpace.snd encIn encUnary))
      (ComputableInLogSpace.const [])
  refine (flatMap_range hr hbody).congr_fun fun a ↦ ?_
  induction (List.range (r a)) with
  | nil => rfl
  | cons i is ih =>
    cases hfi : f (a, i) <;> simp [List.flatMap_cons, hfi, ih]

/-- Equality test `decide (p.1 = p.2)` on bit words (`encPair encBits encBits`) in logarithmic
space. -/
theorem bitsEq :
    ComputableInLogSpace (fun p : List Bool × List Bool ↦ decide (p.1 = p.2))
      (encPair encBits encBits) encBool := by
  have hu : ComputableInLogSpace Prod.fst (encPair encBits encBits) encBits :=
    ComputableInLogSpace.fst encBits encBits
  have hv : ComputableInLogSpace Prod.snd (encPair encBits encBits) encBits :=
    ComputableInLogSpace.snd encBits encBits
  have hlenEq : ComputableInLogSpace
      (fun p : List Bool × List Bool ↦ decide (p.1.length = p.2.length))
      (encPair encBits encBits) encBool :=
    ComputableInLogSpace.unaryEq
      (ComputableInLogSpace.bitsLength.comp hu)
      (ComputableInLogSpace.bitsLength.comp hv)
  have hidxBin : ComputableInLogSpace (fun q : (List Bool × List Bool) × ℕ ↦ q.2)
      (encPair (encPair encBits encBits) encUnary) encNat :=
    ComputableInLogSpace.unaryToBinary
      (ComputableInLogSpace.snd (encPair encBits encBits) encUnary)
  have hqP := ComputableInLogSpace.fst (encPair encBits encBits) encUnary
  have hget1 : ComputableInLogSpace
      (fun q : (List Bool × List Bool) × ℕ ↦ q.1.1[q.2]?)
      (encPair (encPair encBits encBits) encUnary) (encOption encBool) :=
    computableInLogSpace_bitsGetElem?.comp (ComputableInLogSpace.pair (hu.comp hqP) hidxBin)
  have hget2 : ComputableInLogSpace
      (fun q : (List Bool × List Bool) × ℕ ↦ q.1.2[q.2]?)
      (encPair (encPair encBits encBits) encUnary) (encOption encBool) :=
    computableInLogSpace_bitsGetElem?.comp (ComputableInLogSpace.pair (hv.comp hqP) hidxBin)
  have hcmpBit : ComputableInLogSpace
      (fun q : (List Bool × List Bool) × ℕ ↦ decide (q.1.1[q.2]? = q.1.2[q.2]?))
      (encPair (encPair encBits encBits) encUnary) encBool :=
    (ComputableInLogSpace.of_finite
      (encIn := encPair (encOption encBool) (encOption encBool))
      fun o : Option Bool × Option Bool ↦ decide (o.1 = o.2)).comp
      (ComputableInLogSpace.pair hget1 hget2)
  have hallBits := all_range (ComputableInLogSpace.bitsLength.comp hu) hcmpBit
  refine (ComputableInLogSpace.bool_and hlenEq hallBits).congr_fun fun ⟨u, v⟩ ↦ ?_
  by_cases heq : u = v
  · subst heq
    simp
  · simp only [Function.comp_apply, heq, decide_false, Bool.false_eq]
    rw [Bool.eq_false_iff]
    intro hboth
    obtain ⟨hlen_b, hall_b⟩ := Bool.and_eq_true_iff.mp hboth
    have hlen : u.length = v.length := of_decide_eq_true hlen_b
    have hall : ∀ i ∈ List.range u.length, decide (u[i]? = v[i]?) = true :=
      List.all_eq_true.mp hall_b
    apply heq
    refine List.ext_getElem hlen fun i hi₁ hi₂ ↦ ?_
    have hi := of_decide_eq_true (hall i (List.mem_range.mpr hi₁))
    rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂] at hi
    exact Option.some.inj hi

/-- Equality test `decide (f₁ a = f₂ a)` in logarithmic space for any two logarithmic-space
functions `f₁, f₂ : α → β` into an injectively encoded type `(β, encOut)`. -/
theorem decideEq [DecidableEq β] {f₁ f₂ : α → β}
    (h₁ : ComputableInLogSpace f₁ encIn encOut)
    (h₂ : ComputableInLogSpace f₂ encIn encOut) :
    ComputableInLogSpace (fun a ↦ decide (f₁ a = f₂ a)) encIn encBool := by
  refine (bitsEq.comp
    (ComputableInLogSpace.pair h₁.encoding_comp h₂.encoding_comp)).congr_fun fun a ↦ ?_
  simp [encOut.injective.eq_iff]

end Combinators

end CslibFrontier.Computability.LogSpace
