/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.UGraph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.USTCON.Reader.Cert
import CslibFrontier.Computability.USTCON.Reader.Invariant
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# All-pairs undirected graph reachability in logarithmic space

Computing the flat `n × n` all-pairs undirected reachability truth table `ugraphReachTable G` of an
undirected graph `G : Cslib.Complexity.UGraphInstance` is computable in deterministic logarithmic
space (`Turing.MultiTapeTM.ComputableInLogSpace`) on multi-tape Turing machines.

The construction simulates Reingold's read machine (`Cslib.USTCON.Reader.machine`) sequentially
across all ordered pairs `(s, t) ∈ Fin G.n × Fin G.n` inside a single `Turing.QueryMachine`,
synthesizing the virtual `1^n 0 1^s 0 1^t 0` header for each pair `(s, t)` from `O(log n)` binary
counters while forwarding adjacency queries into `G.encode`.

## Main definitions

* `Cslib.USTCON.ugraphReachTable`: flat row-major `G.n × G.n` Boolean reachability table of an
  undirected graph `G : UGraphInstance`.

## Main results

* `Cslib.USTCON.length_ugraphReachTable`: `(ugraphReachTable G).length = G.n * G.n`.
* `Cslib.USTCON.getD_ugraphReachTable`: entry `s * G.n + t` of `ugraphReachTable G` is `true` iff
  `G.graph.Reachable s t`.
* `Cslib.USTCON.computableInLogSpace_ugraphReachTable`: `ugraphReachTable` is computable in
  deterministic logarithmic space (`ComputableInLogSpace ugraphReachTable encUGraph encBits`).
-/

public section

namespace Cslib.USTCON

open Cslib.Complexity Turing Turing.MultiTapeTM

/-- Flat row-major `n × n` reachability table of an undirected graph `G` on `Fin G.n`: entry
`s * G.n + t` records whether `G.graph.Reachable s t`. -/
noncomputable def ugraphReachTable (G : UGraphInstance) : List Bool :=
  (List.finRange G.n).flatMap fun s ↦
    (List.finRange G.n).map fun t ↦
      @decide (G.graph.Reachable s t) (Classical.propDecidable _)

/-- The reachability table of `G` has length `G.n * G.n`. -/
@[simp]
theorem length_ugraphReachTable (G : UGraphInstance) :
    (ugraphReachTable G).length = G.n * G.n := by
  simp [ugraphReachTable, List.length_flatMap, List.map_const', List.sum_replicate]

/-- Entry `s * G.n + t` of `ugraphReachTable G` is `true` iff `G.graph.Reachable s t`. -/
theorem getD_ugraphReachTable (G : UGraphInstance) (s t : Fin G.n) :
    (ugraphReachTable G).getD (s.val * G.n + t.val) false = true ↔ G.graph.Reachable s t := by
  have heq : ugraphReachTable G =
      adjacencyMatrix (fun x y ↦ @decide (G.graph.Reachable x y) (Classical.propDecidable _)) := by
    simp only [ugraphReachTable, adjacencyMatrix, List.ofFn_eq_map]
  rw [heq, getD_adjacencyMatrix]
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

section ReachQueryMachine

open Cslib.USTCON.Reader

private abbrev ReachQState : Type :=
  (Bool × (ℕ × ℕ × ℕ)) × State

private def encReachQState : ReachQState ↪ List Bool :=
  encPair (encPair encBool encNat3) encState

private def virtBit (n s t : ℕ) (q : State) (ob : Option Bool) : Bool :=
  match addr q with
  | none => false
  | some A =>
    if A < n + s + t + 3 then
      if A < n + 1 then decide (A < n)
      else if A < n + s + 2 then decide (A < n + 1 + s)
      else decide (A < n + s + 2 + t)
    else ob.getD false

private def reachQuery (st : ReachQState) : ℕ :=
  if !st.1.1 then st.1.2.1
  else
    let (n, s, t) := st.1.2
    match addr st.2 with
    | none => 0
    | some A =>
      if A < n + s + t + 3 then 0
      else n + 1 + (A - (n + s + t + 3))

private def reachNext (p : ReachQState × Option Bool) : ReachQState :=
  let st := p.1
  let ob := p.2
  if !st.1.1 then
    let n := st.1.2.1
    if ob == some true then ((false, (n + 1, 0, 0)), init)
    else if n = 0 then ((true, (0, 0, 0)), { init with ctl := .done })
    else ((true, (n, 0, 0)), init)
  else
    let (n, s, t) := st.1.2
    if n = 0 then st
    else
      let vb := virtBit n s t st.2 ob
      let q' := (Cslib.USTCON.Reader.step st.2 vb).1
      if q'.ctl = .done then
        if t + 1 < n then ((true, (n, s, t + 1)), init)
        else if s + 1 < n then ((true, (n, s + 1, 0)), init)
        else ((true, (0, 0, 0)), q')
      else ((true, (n, s, t)), q')

private def reachEmit (p : ReachQState × Option Bool) : List Bool :=
  let st := p.1
  let ob := p.2
  if !st.1.1 then []
  else
    let (n, s, t) := st.1.2
    if n = 0 then []
    else (Cslib.USTCON.Reader.step st.2 (virtBit n s t st.2 ob)).2

private def reachHalted (st : ReachQState) : Bool :=
  st.1.1 && decide (st.1.2.1 = 0)

private def reachQM : QueryMachine ReachQState where
  init := ((false, (0, 0, 0)), init)
  query := reachQuery
  next := reachNext
  emit := reachEmit
  halted := reachHalted
  finish _ := []

private theorem stateBudget_le_encState (q : State) :
    stateBudget q ≤ 2 * (encState q).length + 3 := by
  simp [stateBudget, stepBudget, encStepIn, encBool_apply]

private theorem readerAddr_inSpace :
    ComputableInSpace addr encState (encOption encNat) stateBudget :=
  addr_inSpace

private theorem readerHalt_inSpace :
    ComputableInSpace (fun q : State ↦ decide (q.ctl = .done)) encState encBool stateBudget :=
  halt_inSpace

private theorem readerStep_inSpace :
    ComputableInSpace (fun p : State × Bool ↦ Cslib.USTCON.Reader.step p.1 p.2)
      (encPair encState encBool) (encPair encState encBits) fun p ↦ stateBudget p.1 :=
  step_inSpace

section SpaceCerts

attribute [local irreducible] encState Cslib.USTCON.Reader.step Cslib.USTCON.Reader.addr

private theorem reachQuery_inSpace :
    ComputableInSpace reachQM.query encReachQState encNat
      fun s ↦ (encReachQState s).length := by
  open ComputableInSpace in
  let Bs : ReachQState → ℕ := fun s ↦ (encReachQState s).length
  have h1 := fst (encPair encBool encNat3) encState
  have hq : ComputableInSpace (fun s : ReachQState ↦ s.2) encReachQState encState Bs := snd _ _
  have hphase : ComputableInSpace (fun s : ReachQState ↦ s.1.1) encReachQState encBool Bs :=
    fst' h1
  have hnst := snd' h1
  have hn : ComputableInSpace (fun s : ReachQState ↦ s.1.2.1) encReachQState encNat Bs :=
    fst' hnst
  have hs : ComputableInSpace (fun s : ReachQState ↦ s.1.2.2.1) encReachQState encNat Bs :=
    fst' (snd' hnst)
  have ht : ComputableInSpace (fun s : ReachQState ↦ s.1.2.2.2) encReachQState encNat Bs :=
    snd' (snd' hnst)
  have haddr : ComputableInSpace (fun s : ReachQState ↦ addr s.2) encReachQState
      (encOption encNat) Bs :=
    budget_comp_lin readerAddr_inSpace
      ⟨3, fun q ↦ by dsimp only; have := stateBudget_le_encState q; omega⟩ hq
  have hisSome := budget_optionIsSome haddr
  have hA := budget_optionGetD 0 haddr
  have hhdr := budget_natAdd (budget_natAdd (budget_natAdd hn hs) ht) (budget_const 3)
  have hlt := budget_natLt hA hhdr
  have hpos := budget_natAdd (budget_natSucc hn) (budget_natSub hA hhdr)
  have hnotPhase := budget_finite (encC := encBool) not hphase
  have hall := budget_ite hnotPhase hn
    (budget_ite hisSome (budget_ite hlt (budget_const 0) hpos) (budget_const 0))
  refine hall.of_enc_eq fun s ↦ ?_
  congr 1
  dsimp only [reachQM, reachQuery]
  rcases s with ⟨⟨ph, n, sv, tv⟩, q⟩
  cases ph
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases addr q with
    | none => simp
    | some A =>
      by_cases hlt' : A < n + sv + tv + 3 <;> simp [hlt']

private theorem virtBit_inSpace :
    ComputableInSpace
      (fun p : ReachQState × Option Bool ↦
        virtBit p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2)
      (QueryMachine.encStateRead encReachQState) encBool
      fun p ↦ (QueryMachine.encStateRead encReachQState p).length := by
  open ComputableInSpace in
  let encIn := QueryMachine.encStateRead encReachQState
  let Bs : ReachQState × Option Bool → ℕ := fun p ↦ (encIn p).length
  have hst : ComputableInSpace Prod.fst encIn encReachQState Bs := fst _ _
  have hob : ComputableInSpace Prod.snd encIn (encOption encBool) Bs := snd _ _
  have h1 := fst' hst
  have hq := snd' hst
  have hnst := snd' h1
  have hn := fst' hnst
  have hs := fst' (snd' hnst)
  have ht := snd' (snd' hnst)
  have haddr : ComputableInSpace (fun p : ReachQState × Option Bool ↦ addr p.1.2) encIn
      (encOption encNat) Bs :=
    budget_comp_lin readerAddr_inSpace
      ⟨3, fun q ↦ by dsimp only; have := stateBudget_le_encState q; omega⟩ hq
  have hisSome := budget_optionIsSome haddr
  have hA := budget_optionGetD 0 haddr
  have hhdr := budget_natAdd (budget_natAdd (budget_natAdd hn hs) ht) (budget_const 3)
  have hn1 := budget_natSucc hn
  have hns2 := budget_natAdd (budget_natAdd hn hs) (budget_const 2)
  have hnst2 := budget_natAdd hns2 ht
  have hobD := budget_optionGetD false hob
  have hall := budget_ite hisSome
    (budget_ite (budget_natLt hA hhdr)
      (budget_ite (budget_natLt hA hn1) (budget_natLt hA hn)
        (budget_ite (budget_natLt hA hns2) (budget_natLt hA (budget_natAdd hn1 hs))
          (budget_natLt hA hnst2)))
      hobD)
    (budget_const false)
  refine hall.of_enc_eq fun p ↦ ?_
  congr 1
  rcases p with ⟨⟨⟨_, n, sv, tv⟩, q⟩, ob⟩
  dsimp only [virtBit]
  cases addr q with
  | none => simp
  | some A =>
    by_cases h1' : A < n + sv + tv + 3
    · by_cases h2' : A < n + 1
      · simp [h1', h2']
      · by_cases h3' : A < n + sv + 2
        · simp [h1', h2', h3', show n + 1 + sv = n + sv + 1 by omega]
        · simp [h1', h2', h3']
    · simp [h1']

private theorem reachStepPair_inSpace :
    ComputableInSpace
      (fun p : ReachQState × Option Bool ↦
        Cslib.USTCON.Reader.step p.1.2
          (virtBit p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2))
      (QueryMachine.encStateRead encReachQState) (encPair encState encBits)
      fun p ↦ (QueryMachine.encStateRead encReachQState p).length := by
  open ComputableInSpace in
  let encIn := QueryMachine.encStateRead encReachQState
  let Bs : ReachQState × Option Bool → ℕ := fun p ↦ (encIn p).length
  have hst : ComputableInSpace Prod.fst encIn encReachQState Bs := fst _ _
  have hq : ComputableInSpace (fun p : ReachQState × Option Bool ↦ p.1.2) encIn encState Bs :=
    snd' hst
  have harg := budget_prod hq virtBit_inSpace
  exact budget_comp_lin readerStep_inSpace
    ⟨3, fun r ↦ by
      dsimp only
      have := stateBudget_le_encState r.1
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega⟩
    harg

private theorem reachNext_inSpace :
    ComputableInSpace reachQM.next (QueryMachine.encStateRead encReachQState) encReachQState
      fun p ↦ (QueryMachine.encStateRead encReachQState p).length := by
  open ComputableInSpace in
  let encIn := QueryMachine.encStateRead encReachQState
  let Bs : ReachQState × Option Bool → ℕ := fun p ↦ (encIn p).length
  have hst : ComputableInSpace Prod.fst encIn encReachQState Bs := fst _ _
  have hob : ComputableInSpace Prod.snd encIn (encOption encBool) Bs := snd _ _
  have h1 := fst' hst
  have hphase := fst' h1
  have hnst := snd' h1
  have hn := fst' hnst
  have hs := fst' (snd' hnst)
  have ht := snd' (snd' hnst)
  have hobTrue : ComputableInSpace (fun p : ReachQState × Option Bool ↦ p.2 == some true)
      encIn encBool Bs :=
    budget_finite (fun o : Option Bool ↦ o == some true) hob
  have hq' := fst' reachStepPair_inSpace
  have hdone : ComputableInSpace
      (fun p : ReachQState × Option Bool ↦
        decide ((Cslib.USTCON.Reader.step p.1.2
          (virtBit p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2)).1.ctl = .done))
      encIn encBool Bs :=
    budget_comp_lin readerHalt_inSpace
      ⟨3, fun q ↦ by dsimp only; have := stateBudget_le_encState q; omega⟩ hq'
  let mkSt (ph : ReachQState × Option Bool → Bool)
      (nf sf tf : ReachQState × Option Bool → ℕ)
      (qf : ReachQState × Option Bool → State)
      (hph : ComputableInSpace ph encIn encBool Bs)
      (hnf : ComputableInSpace nf encIn encNat Bs)
      (hsf : ComputableInSpace sf encIn encNat Bs)
      (htf : ComputableInSpace tf encIn encNat Bs)
      (hqf : ComputableInSpace qf encIn encState Bs) :
      ComputableInSpace (fun p ↦ (((ph p, (nf p, sf p, tf p)), qf p) : ReachQState))
        encIn encReachQState Bs :=
    budget_prod (budget_prod hph (budget_prod hnf (budget_prod hsf htf))) hqf
  have cFalse := budget_const (encIn := encIn) (Bs := Bs) (encB := encBool) false
  have cTrue := budget_const (encIn := encIn) (Bs := Bs) (encB := encBool) true
  have cZero := budget_const (encIn := encIn) (Bs := Bs) (encB := encNat) 0
  have cInit := budget_const (encIn := encIn) (Bs := Bs) (encB := encState) init
  have cDone := budget_const (encIn := encIn) (Bs := Bs) (encB := encState)
    { init with ctl := .done }
  have br0 := budget_ite hobTrue
    (mkSt _ _ _ _ _ cFalse (budget_natSucc hn) cZero cZero cInit)
    (budget_ite (budget_natIsZero hn)
      (mkSt _ _ _ _ _ cTrue cZero cZero cZero cDone)
      (mkSt _ _ _ _ _ cTrue hn cZero cZero cInit))
  have br1 := budget_ite (budget_natIsZero hn) hst
    (budget_ite hdone
      (budget_ite (budget_natLt (budget_natSucc ht) hn)
        (mkSt _ _ _ _ _ cTrue hn hs (budget_natSucc ht) cInit)
        (budget_ite (budget_natLt (budget_natSucc hs) hn)
          (mkSt _ _ _ _ _ cTrue hn (budget_natSucc hs) cZero cInit)
          (mkSt _ _ _ _ _ cTrue cZero cZero cZero hq')))
      (mkSt _ _ _ _ _ cTrue hn hs ht hq'))
  have hall := budget_ite (budget_finite not hphase) br0 br1
  refine hall.of_enc_eq fun p ↦ ?_
  congr 1
  dsimp only [reachQM]
  rcases p with ⟨⟨⟨ph, n, sv, tv⟩, q⟩, ob⟩
  cases ph
  · simp only [reachNext, Bool.not_false, ↓reduceIte]
    cases (ob == some true)
    · by_cases hn0 : n = 0 <;> simp [hn0]
    · simp
  · simp only [reachNext, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      by_cases hd :
          (Cslib.USTCON.Reader.step q (virtBit n sv tv q ob)).1.ctl = .done
      · by_cases ht' : tv + 1 < n
        · simp [hd, ht']
        · by_cases hs' : sv + 1 < n <;> simp [hd, ht', hs']
      · simp [hd]

private theorem reachEmit_inSpace :
    ComputableInSpace reachQM.emit (QueryMachine.encStateRead encReachQState) encBits
      fun p ↦ (QueryMachine.encStateRead encReachQState p).length := by
  open ComputableInSpace in
  let encIn := QueryMachine.encStateRead encReachQState
  let Bs : ReachQState × Option Bool → ℕ := fun p ↦ (encIn p).length
  have hst : ComputableInSpace Prod.fst encIn encReachQState Bs := fst _ _
  have hphase := fst' (fst' hst)
  have hn := fst' (snd' (fst' hst))
  have hout := snd' reachStepPair_inSpace
  have cNil := budget_const (encIn := encIn) (Bs := Bs) (encB := encBits) ([] : List Bool)
  have hall := budget_ite (budget_finite not hphase) cNil
    (budget_ite (budget_natIsZero hn) cNil hout)
  refine hall.of_enc_eq fun p ↦ ?_
  congr 1
  dsimp only [reachQM]
  rcases p with ⟨⟨⟨ph, n, _, _⟩, _⟩, _⟩
  cases ph
  · simp [reachEmit]
  · by_cases hn0 : n = 0 <;> simp [reachEmit, hn0]

end SpaceCerts

private theorem reachHalted_inSpace :
    ComputableInSpace reachQM.halted encReachQState encBool
      fun s ↦ (encReachQState s).length := by
  open ComputableInSpace in
  let Bs : ReachQState → ℕ := fun s ↦ (encReachQState s).length
  have h1 := fst (encPair encBool encNat3) encState
  have hphase := fst' h1
  have hn := fst' (snd' h1)
  exact (budget_finite (fun p : Bool × Bool ↦ p.1 && p.2)
    (budget_prod hphase (budget_natIsZero hn))).of_enc_eq fun _ ↦ rfl

private theorem reachFinish_inSpace :
    ComputableInSpace reachQM.finish encReachQState encBits
      fun s ↦ (encReachQState s).length :=
  ComputableInSpace.budget_const []

private def mkUSTCON (G : UGraphInstance) (s t : Fin G.n) : USTCONInstance where
  n := G.n
  adj := G.adj
  symm := G.symm
  loopless := G.loopless
  s := s
  t := t

private theorem virtBit_eq_readBit (G : UGraphInstance) (s t : Fin G.n)
    {q : State} (hinv : Inv (mkUSTCON G s t) q) :
    virtBit G.n s.val t.val q (reachQM.read G.encode ((true, (G.n, s.val, t.val)), q)) =
      machine.readBit (mkUSTCON G s t).encode q := by
  obtain ⟨hb, hp⟩ := hinv
  rcases hc : q.ctl with _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · simp only [Phase, hc] at hp
    have hcnt : q.cnt ≤ G.n := hb.cnt
    have hA : addr q = some q.cnt := by simp [addr, hc]
    have hlt1 : q.cnt < G.n + s.val + t.val + 3 := by omega
    have hlt2 : q.cnt < G.n + 1 := by omega
    rw [readBit_of_addr hA, (mkUSTCON G s t).getD_encode_n hcnt]
    simp only [virtBit, hA, hlt1, hlt2, ↓reduceIte, mkUSTCON]
    exact decide_eq_decide.mpr Iff.rfl
  · simp only [Phase, hc] at hp
    have hn_eq : q.n = G.n := by simpa [mkUSTCON] using congrArg State.n hp.1
    have hcnt : q.cnt ≤ s.val := hp.2
    have hA : addr q = some (G.n + 1 + q.cnt) := by simp [addr, hc, hn_eq]
    rw [readBit_of_addr hA]
    have hs_bit := (mkUSTCON G s t).getD_encode_s hcnt
    change (mkUSTCON G s t).encode.getD (G.n + 1 + q.cnt) false = _ at hs_bit
    rw [hs_bit]
    simp only [virtBit, hA, mkUSTCON]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    exact decide_eq_decide.mpr ⟨by omega, by omega⟩
  · simp only [Phase, hc] at hp
    have hn_eq : q.n = G.n := by simpa [mkUSTCON] using congrArg State.n hp.1
    have hs_eq : q.s = s.val := by simpa [mkUSTCON] using congrArg State.s hp.1
    have hcnt : q.cnt ≤ t.val := hp.2
    have hA : addr q = some (G.n + 1 + s.val + 1 + q.cnt) := by
      simp [addr, hc, hn_eq, hs_eq]
    rw [readBit_of_addr hA]
    have ht_bit := (mkUSTCON G s t).getD_encode_t hcnt
    change (mkUSTCON G s t).encode.getD (G.n + 1 + s.val + 1 + q.cnt) false = _ at ht_bit
    rw [ht_bit]
    simp only [virtBit, hA, mkUSTCON]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact decide_eq_decide.mpr ⟨by omega, by omega⟩
  · have hA : addr q = none := by simp [addr, hc]
    rw [readBit_of_addr_none hA]; simp [virtBit, hA]
  · have hA : addr q = none := by simp [addr, hc]
    rw [readBit_of_addr_none hA]; simp [virtBit, hA]
  · have hA : addr q = none := by simp [addr, hc]
    rw [readBit_of_addr_none hA]; simp [virtBit, hA]
  · have hA : addr q = none := by simp [addr, hc]
    rw [readBit_of_addr_none hA]; simp [virtBit, hA]
  · simp only [Phase, hc, WalkParams] at hp
    obtain ⟨⟨hn_eq, hs_eq, ht_eq, _, _⟩, _⟩ := hp
    by_cases hroot : q.ev.atRoot
    · have hv1 : q.ev.vertex.1 < G.n := hb.v₁
      have hv2 : q.ev.vertex.2 < G.n := hb.v₂
      have hA : addr q =
          some (G.n + s.val + t.val + 3 + (q.ev.vertex.1 * G.n + q.ev.vertex.2)) := by
        simp [addr, hc, hroot, hn_eq, hs_eq, ht_eq, mkUSTCON]
      rw [readBit_of_addr hA]
      have hmat := (mkUSTCON G s t).getD_encode_matrix ⟨q.ev.vertex.1, hv1⟩ ⟨q.ev.vertex.2, hv2⟩
      change (mkUSTCON G s t).encode.getD
        (G.n + s.val + t.val + 3 + (q.ev.vertex.1 * G.n + q.ev.vertex.2)) false =
        G.adj ⟨q.ev.vertex.1, hv1⟩ ⟨q.ev.vertex.2, hv2⟩ at hmat
      rw [hmat]
      have hnl : ¬(G.n + s.val + t.val + 3 + (q.ev.vertex.1 * G.n + q.ev.vertex.2) <
          G.n + s.val + t.val + 3) := by omega
      have hq_pos : reachQM.query ((true, (G.n, s.val, t.val)), q) =
          G.n + 1 + (q.ev.vertex.1 * G.n + q.ev.vertex.2) := by
        simp [reachQM, reachQuery, hA, hnl]
      simp only [virtBit, hA, hnl, ↓reduceIte, QueryMachine.read, hq_pos,
        G.getElem?_encode_matrix hv1 hv2, Option.getD_some]
    · have hA : addr q = none := by simp [addr, hc, hroot]
      rw [readBit_of_addr_none hA]; simp [virtBit, hA]
  · have hA : addr q = none := by simp [addr, hc]
    rw [readBit_of_addr_none hA]; simp [virtBit, hA]
  · have hA : addr q = none := by simp [addr, hc]
    rw [readBit_of_addr_none hA]; simp [virtBit, hA]

private theorem length_encReachQState_le (st : ReachQState) :
    (encReachQState st).length ≤
      16 * ((encNat st.1.2.1).length + (encNat st.1.2.2.1).length +
        (encNat st.1.2.2.2).length + (encState st.2).length + 2) := by
  simp only [encReachQState, encNat3, length_encPair, encBool_apply, List.length_singleton]
  omega

private def reachBoundConst : ℕ :=
  128 * (stateConst + 128)

private theorem length_encNat_le_log_encode (G : UGraphInstance) {x : ℕ} (hx : x ≤ G.n) :
    (encNat x).length ≤ Nat.log2 G.encode.length + 1 := by
  rw [length_encNat_eq_size]
  have hlen := G.length_encode
  have hlt : x < 2 ^ (Nat.log2 G.encode.length + 1) :=
    calc x ≤ G.n := hx
      _ < G.encode.length := by omega
      _ < 2 ^ (Nat.log2 G.encode.length + 1) := Nat.lt_log2_self
  exact Nat.size_le.mpr hlt

private theorem length_encState_init_ctl_le (c : Ctl) :
    (encState { init with ctl := c }).length ≤ 704 := by
  refine (length_encState_le _).trans ?_
  have hctl : (encCtl c).length < 10 := by
    dsimp only [encCtl]
    have hlt := length_encFinEnum_lt c
    have hcard : Nat.card Ctl = 10 := by rw [Nat.card_eq_fintype_card]; decide
    omega
  have h0_len : (encNat 0).length = 0 := by simp
  simp only [init, h0_len, encList_nil, List.length_nil]
  omega

private theorem reachBoundConst_ge : 16384 ≤ reachBoundConst := by
  dsimp only [reachBoundConst]
  omega

private theorem reachBoundConst_mul_ge (L : ℕ) :
    128 * (stateConst * L) + 16384 * L ≤ reachBoundConst * L := by
  have h : reachBoundConst * L = 128 * (stateConst * L) + 16384 * L := by
    dsimp only [reachBoundConst]
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  omega

private theorem length_encReachQState_header_le (G : UGraphInstance) {i : ℕ} (hi : i ≤ G.n) :
    (encReachQState ((false, (i, 0, 0)), init)).length ≤
      reachBoundConst * (Nat.log2 G.encode.length + 1) := by
  have hi_len := length_encNat_le_log_encode G hi
  have h0_len : (encNat 0).length = 0 := by simp
  have hinit_len : (encState init).length ≤ 704 := length_encState_init_ctl_le .hdrN
  refine (length_encReachQState_le _).trans ?_
  simp only [h0_len]
  have h1 : 16 * ((encNat i).length + 0 + 0 + (encState init).length + 2) ≤
      16384 * (Nat.log2 G.encode.length + 1) := by omega
  exact h1.trans (Nat.mul_le_mul_right _ reachBoundConst_ge)

private theorem log2_encode_mkUSTCON_le (G : UGraphInstance) (s t : Fin G.n) :
    Nat.log2 (mkUSTCON G s t).encode.length ≤ Nat.log2 G.encode.length + 2 := by
  let I := mkUSTCON G s t
  have hG := G.length_encode
  have hIs : s.val < G.n := s.isLt
  have hIt : t.val < G.n := t.isLt
  have hI : I.encode.length = G.n + s.val + t.val + 3 + G.n * G.n := by
    simp [I, mkUSTCON, USTCONInstance.encode, USTCONInstance.toSTCONInstance,
      STCONInstance.encode]
    omega
  have hI_ne : I.encode.length ≠ 0 := by omega
  have hltG : G.encode.length < 2 ^ (Nat.log2 G.encode.length + 1) := Nat.lt_log2_self
  have hlt_pow : I.encode.length < 2 ^ (Nat.log2 G.encode.length + 3) :=
    calc I.encode.length ≤ 4 * G.encode.length := by omega
      _ < 4 * 2 ^ (Nat.log2 G.encode.length + 1) := by omega
      _ = 2 ^ (Nat.log2 G.encode.length + 3) := by ring
  have hlt_log := (Nat.log2_lt hI_ne).mpr hlt_pow
  dsimp only [I] at hlt_log
  omega

private theorem length_encReachQState_pair_le (G : UGraphInstance) (s t : Fin G.n) (k : ℕ) :
    (encReachQState ((true, (G.n, s.val, t.val)),
      (machine.run (mkUSTCON G s t).encode k).state)).length ≤
      reachBoundConst * (Nat.log2 G.encode.length + 1) := by
  set L := Nat.log2 G.encode.length + 1
  have hL : 1 ≤ L := Nat.succ_pos _
  have hn_len : (encNat G.n).length ≤ L := length_encNat_le_log_encode G le_rfl
  have hs_len : (encNat s.val).length ≤ L := length_encNat_le_log_encode G s.isLt.le
  have ht_len : (encNat t.val).length ≤ L := length_encNat_le_log_encode G t.isLt.le
  have hq_len := length_encState_run_le (I := mkUSTCON G s t) k
  have hlogI := log2_encode_mkUSTCON_le G s t
  have hq_L : (encState (machine.run (mkUSTCON G s t).encode k).state).length ≤
      4 * (stateConst * L) :=
    calc (encState (machine.run (mkUSTCON G s t).encode k).state).length
        ≤ stateConst * (Nat.log2 (mkUSTCON G s t).encode.length + 2) := hq_len
      _ ≤ stateConst * (4 * L) := Nat.mul_le_mul_left stateConst (by omega)
      _ = 4 * (stateConst * L) := by
        rw [← Nat.mul_assoc, Nat.mul_comm stateConst 4, Nat.mul_assoc]
  have hrc := reachBoundConst_mul_ge L
  refine (length_encReachQState_le _).trans ?_
  dsimp only
  omega

private theorem length_encReachQState_done_le (G : UGraphInstance) (s t : Fin G.n) (k : ℕ) :
    (encReachQState ((true, (0, 0, 0)),
      (machine.run (mkUSTCON G s t).encode k).state)).length ≤
      reachBoundConst * (Nat.log2 G.encode.length + 1) := by
  set L := Nat.log2 G.encode.length + 1
  have hL : 1 ≤ L := Nat.succ_pos _
  have h0_len : (encNat 0).length = 0 := by simp
  have hq_len := length_encState_run_le (I := mkUSTCON G s t) k
  have hlogI := log2_encode_mkUSTCON_le G s t
  have hq_L : (encState (machine.run (mkUSTCON G s t).encode k).state).length ≤
      4 * (stateConst * L) :=
    calc (encState (machine.run (mkUSTCON G s t).encode k).state).length
        ≤ stateConst * (Nat.log2 (mkUSTCON G s t).encode.length + 2) := hq_len
      _ ≤ stateConst * (4 * L) := Nat.mul_le_mul_left stateConst (by omega)
      _ = 4 * (stateConst * L) := by
        rw [← Nat.mul_assoc, Nat.mul_comm stateConst 4, Nat.mul_assoc]
  have hrc := reachBoundConst_mul_ge L
  refine (length_encReachQState_le _).trans ?_
  dsimp only
  simp only [h0_len]
  omega

private def ReachRunSeg (w : List Bool) (B : ℕ) (start target : ReachQState)
    (out : List Bool) : Prop :=
  ∃ T, reachQM.runFrom w start T = target ∧
    (∀ i < T, reachQM.halted (reachQM.runFrom w start i) = false) ∧
    ((List.range T).map fun i ↦
      reachQM.emit (reachQM.runFrom w start i,
        reachQM.read w (reachQM.runFrom w start i))).flatten = out ∧
    (∀ i ≤ T, (encReachQState (reachQM.runFrom w start i)).length ≤ B)

private theorem ReachRunSeg.refl {w : List Bool} {B : ℕ} (s : ReachQState)
    (hs : (encReachQState s).length ≤ B) : ReachRunSeg w B s s [] :=
  ⟨0, rfl, fun _ h ↦ absurd h (by omega), rfl, fun i hi ↦ by rw [Nat.le_zero.mp hi]; exact hs⟩

private theorem ReachRunSeg.trans {w : List Bool} {B : ℕ} {s₁ s₂ s₃ : ReachQState}
    {o₁ o₂ : List Bool} (h₁ : ReachRunSeg w B s₁ s₂ o₁) (h₂ : ReachRunSeg w B s₂ s₃ o₂) :
    ReachRunSeg w B s₁ s₃ (o₁ ++ o₂) := by
  obtain ⟨T₁, hr₁, hp₁, ho₁, hb₁⟩ := h₁
  obtain ⟨T₂, hr₂, hp₂, ho₂, hb₂⟩ := h₂
  refine ⟨T₁ + T₂, by rw [QueryMachine.runFrom_add, hr₁, hr₂], fun i hi ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · by_cases hlt : i < T₁
    · exact hp₁ i hlt
    · rw [show i = T₁ + (i - T₁) by omega, QueryMachine.runFrom_add, hr₁]
      exact hp₂ (i - T₁) (by omega)
  · rw [List.range_add, List.map_append, List.flatten_append, ho₁, ← ho₂]
    congr 2
    rw [List.map_map]
    refine List.map_congr_left fun _ _ ↦ ?_
    simp only [Function.comp_apply, QueryMachine.runFrom_add, hr₁]
  · by_cases hle : i ≤ T₁
    · exact hb₁ i hle
    · rw [show i = T₁ + (i - T₁) by omega, QueryMachine.runFrom_add, hr₁]
      exact hb₂ (i - T₁) (by omega)

private theorem ReachRunSeg.single {w : List Bool} {B : ℕ} {s s' : ReachQState} {o : List Bool}
    (hh : reachQM.halted s = false)
    (hnext : reachQM.next (s, reachQM.read w s) = s')
    (hemit : reachQM.emit (s, reachQM.read w s) = o)
    (hbs : (encReachQState s).length ≤ B)
    (hbs' : (encReachQState s').length ≤ B) :
    ReachRunSeg w B s s' o := by
  refine ⟨1, ?_, fun i hi ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · rw [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero, QueryMachine.step, hh]
    simp [hnext]
  · rw [Nat.lt_one_iff.mp hi]; exact hh
  · simp [hemit]
  · rcases eq_or_ne i 0 with rfl | _
    · exact hbs
    · rw [show i = 1 by omega, QueryMachine.runFrom_succ, QueryMachine.runFrom_zero,
        QueryMachine.step, hh]
      simpa [hnext] using hbs'

private theorem reachRunSeg_header (G : UGraphInstance) :
    let B := reachBoundConst * (Nat.log2 G.encode.length + 1)
    ReachRunSeg G.encode B reachQM.init
      (if G.n = 0 then ((true, (0, 0, 0)), { init with ctl := .done })
       else ((true, (G.n, 0, 0)), init)) [] := by
  intro B
  have hloop : ∀ m ≤ G.n,
      ReachRunSeg G.encode B ((false, (0, 0, 0)), init) ((false, (m, 0, 0)), init) [] := by
    intro m hm
    induction m with
    | zero => exact .refl _ (length_encReachQState_header_le G (Nat.zero_le _))
    | succ m ih =>
      have hm_lt : m < G.n := by omega
      have hstep : ReachRunSeg G.encode B ((false, (m, 0, 0)), init)
          ((false, (m + 1, 0, 0)), init) [] := by
        refine .single rfl ?_ rfl
          (length_encReachQState_header_le G hm_lt.le)
          (length_encReachQState_header_le G hm)
        have hread : reachQM.read G.encode ((false, (m, 0, 0)), init) = some true := by
          simp [QueryMachine.read, reachQM, reachQuery, G.getElem?_encode_n hm_lt.le, hm_lt]
        change reachNext (((false, (m, 0, 0)), init),
          reachQM.read G.encode ((false, (m, 0, 0)), init)) = _
        rw [hread]
        rfl
      exact (ih hm_lt.le).trans hstep
  have hpre := hloop G.n le_rfl
  have hread_end : reachQM.read G.encode ((false, (G.n, 0, 0)), init) = some false := by
    simp [QueryMachine.read, reachQM, reachQuery, G.getElem?_encode_n le_rfl]
  by_cases hn0 : G.n = 0
  · rw [ite_eq_left hn0]
    have h0_done_len :
        (encReachQState ((true, (0, 0, 0)), { init with ctl := .done })).length ≤ B := by
      have h0_len : (encNat 0).length = 0 := by simp
      have hd_len : (encState { init with ctl := .done }).length ≤ 704 :=
        length_encState_init_ctl_le .done
      refine (length_encReachQState_le _).trans ?_
      simp only [h0_len]
      have h1 : 16 * (0 + 0 + 0 + (encState { init with ctl := .done }).length + 2) ≤
          16384 * (Nat.log2 G.encode.length + 1) := by omega
      exact h1.trans (Nat.mul_le_mul_right _ reachBoundConst_ge)
    have hlast : ReachRunSeg G.encode B ((false, (G.n, 0, 0)), init)
        ((true, (0, 0, 0)), { init with ctl := .done }) [] := by
      refine .single rfl ?_ rfl (length_encReachQState_header_le G le_rfl) h0_done_len
      change reachNext (((false, (G.n, 0, 0)), init),
        reachQM.read G.encode ((false, (G.n, 0, 0)), init)) = _
      rw [hread_end]
      simp [reachNext, hn0]
    exact hpre.trans hlast
  · rw [ite_eq_right hn0]
    have hpos : 0 < G.n := Nat.pos_of_ne_zero hn0
    have hlast : ReachRunSeg G.encode B ((false, (G.n, 0, 0)), init)
        ((true, (G.n, 0, 0)), init) [] := by
      refine .single rfl ?_ rfl
        (length_encReachQState_header_le G le_rfl)
        (length_encReachQState_pair_le G ⟨0, hpos⟩ ⟨0, hpos⟩ 0)
      change reachNext (((false, (G.n, 0, 0)), init),
        reachQM.read G.encode ((false, (G.n, 0, 0)), init)) = _
      rw [hread_end]
      simp [reachNext, hn0]
    exact hpre.trans hlast

private theorem reachRunSeg_pair (G : UGraphInstance) (s t : Fin G.n) :
    let B := reachBoundConst * (Nat.log2 G.encode.length + 1)
    ∃ q_end : State,
      ReachRunSeg G.encode B
        ((true, (G.n, s.val, t.val)), init)
        (if t.val + 1 < G.n then ((true, (G.n, s.val, t.val + 1)), init)
         else if s.val + 1 < G.n then ((true, (G.n, s.val + 1, 0)), init)
         else ((true, (0, 0, 0)), q_end))
        [@decide (G.graph.Reachable s t) (Classical.propDecidable _)] := by
  classical
  intro B
  let I := mkUSTCON G s t
  have hn_pos : 0 < G.n := Fin.pos s
  have hn_ne : G.n ≠ 0 := hn_pos.ne'
  have hex_halt : ∃ k, machine.halt (machine.run I.encode k).state = true := by
    obtain ⟨k, hk, _⟩ := exists_run_eq I
    exact ⟨k, hk⟩
  let K := Nat.find hex_halt
  have hK_halt : machine.halt (machine.run I.encode K).state = true := Nat.find_spec hex_halt
  have hK_pre : ∀ k < K, machine.halt (machine.run I.encode k).state = false := fun k hk ↦
    Bool.eq_false_iff.mpr (Nat.find_min hex_halt hk)
  have hK_pos : 0 < K := by
    by_contra h0
    have hK0 : K = 0 := by omega
    rw [hK0] at hK_halt
    nomatch hK_halt
  have hK_out : (machine.run I.encode K).out =
      [@decide (G.graph.Reachable s t) (Classical.propDecidable _)] := by
    obtain ⟨K₂, hK₂_halt, hK₂_out⟩ := exists_run_eq I
    have hle : K ≤ K₂ := Nat.find_min' hex_halt hK₂_halt
    have hstay : ∀ d, machine.run I.encode (K + d) = machine.run I.encode K := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [← Nat.add_assoc, ReadMachine.run_add, ReadMachine.runFrom_one, ih,
          ReadMachine.next, ite_eq_left hK_halt]
    have heq := hstay (K₂ - K)
    rw [show K + (K₂ - K) = K₂ by omega] at heq
    rw [← heq, hK₂_out]
    congr 1
  have hstep_eq (k : ℕ) (hk : k < K) :
      let qk := (machine.run I.encode k).state
      let st_k : ReachQState := ((true, (G.n, s.val, t.val)), qk)
      Cslib.USTCON.Reader.step qk (virtBit G.n s.val t.val qk (reachQM.read G.encode st_k)) =
        ((machine.run I.encode (k + 1)).state,
          (machine.step qk (machine.readBit I.encode qk)).2) ∧
        (machine.run I.encode (k + 1)).out =
          (machine.run I.encode k).out ++ (machine.step qk (machine.readBit I.encode qk)).2 := by
    intro qk st_k
    have hvb := virtBit_eq_readBit G s t (inv_run (I := I) k)
    have hnh : machine.halt (machine.run I.encode k).state = false := hK_pre k hk
    have hrun1 : machine.run I.encode (k + 1) =
        ReadMachine.next machine I.encode (machine.run I.encode k) := by
      rw [ReadMachine.run_add, ReadMachine.runFrom_one]
    rw [hvb, hrun1]
    dsimp only [ReadMachine.next]
    rw [ite_eq_right (by rw [hnh]; decide)]
    exact ⟨rfl, rfl⟩
  have hprefix : ∀ m ≤ K - 1,
      ReachRunSeg G.encode B
        ((true, (G.n, s.val, t.val)), init)
        ((true, (G.n, s.val, t.val)), (machine.run I.encode m).state)
        (machine.run I.encode m).out := by
    intro m hm
    induction m with
    | zero =>
      exact .refl _ (length_encReachQState_pair_le G s t 0)
    | succ m ih =>
      have hmK : m < K := by omega
      have hm1K : m + 1 < K := by omega
      obtain ⟨hstep_q, hout_q⟩ := hstep_eq m hmK
      have hndone : (machine.run I.encode (m + 1)).state.ctl ≠ .done := by
        have := hK_pre (m + 1) hm1K
        simpa [machine] using this
      have h1 : ReachRunSeg G.encode B
          ((true, (G.n, s.val, t.val)), (machine.run I.encode m).state)
          ((true, (G.n, s.val, t.val)), (machine.run I.encode (m + 1)).state)
          (machine.step (machine.run I.encode m).state
            (machine.readBit I.encode (machine.run I.encode m).state)).2 := by
        refine .single (by simp [reachQM, reachHalted, hn_ne]) ?_ ?_
          (length_encReachQState_pair_le G s t m)
          (length_encReachQState_pair_le G s t (m + 1))
        · change reachNext (((true, (G.n, s.val, t.val)), (machine.run I.encode m).state),
            reachQM.read G.encode
              ((true, (G.n, s.val, t.val)), (machine.run I.encode m).state)) = _
          dsimp only [reachNext]
          rw [ite_eq_right (by decide), ite_eq_right hn_ne]
          have hq1 : (Cslib.USTCON.Reader.step (machine.run I.encode m).state
              (virtBit G.n s.val t.val (machine.run I.encode m).state
                (reachQM.read G.encode
                  ((true, (G.n, s.val, t.val)), (machine.run I.encode m).state)))).1 =
              (machine.run I.encode (m + 1)).state :=
            congrArg Prod.fst hstep_q
          rw [hq1, ite_eq_right hndone]
        · change reachEmit (((true, (G.n, s.val, t.val)), (machine.run I.encode m).state),
            reachQM.read G.encode
              ((true, (G.n, s.val, t.val)), (machine.run I.encode m).state)) = _
          dsimp only [reachEmit]
          rw [ite_eq_right (by decide), ite_eq_right hn_ne, hstep_q]
      rw [hout_q]
      exact (ih (by omega)).trans h1
  let qK := (machine.run I.encode K).state
  refine ⟨qK, ?_⟩
  have hpreK := hprefix (K - 1) le_rfl
  obtain ⟨hstep_last, hout_last⟩ := hstep_eq (K - 1) (by omega)
  have hK_eq : K - 1 + 1 = K := by omega
  rw [hK_eq] at hstep_last hout_last
  have hdoneK : qK.ctl = .done := by simpa [machine, qK] using hK_halt
  have htarget_len :
      (encReachQState
        (if t.val + 1 < G.n then ((true, (G.n, s.val, t.val + 1)), init)
         else if s.val + 1 < G.n then ((true, (G.n, s.val + 1, 0)), init)
         else ((true, (0, 0, 0)), qK))).length ≤ B := by
    by_cases ht' : t.val + 1 < G.n
    · rw [ite_eq_left ht']
      exact length_encReachQState_pair_le G s ⟨t.val + 1, ht'⟩ 0
    · rw [ite_eq_right ht']
      by_cases hs' : s.val + 1 < G.n
      · rw [ite_eq_left hs']
        exact length_encReachQState_pair_le G ⟨s.val + 1, hs'⟩ ⟨0, hn_pos⟩ 0
      · rw [ite_eq_right hs']
        exact length_encReachQState_done_le G s t K
  have hlast : ReachRunSeg G.encode B
      ((true, (G.n, s.val, t.val)), (machine.run I.encode (K - 1)).state)
      (if t.val + 1 < G.n then ((true, (G.n, s.val, t.val + 1)), init)
       else if s.val + 1 < G.n then ((true, (G.n, s.val + 1, 0)), init)
       else ((true, (0, 0, 0)), qK))
      (machine.step (machine.run I.encode (K - 1)).state
        (machine.readBit I.encode (machine.run I.encode (K - 1)).state)).2 := by
    refine .single (by simp [reachQM, reachHalted, hn_ne]) ?_ ?_
      (length_encReachQState_pair_le G s t (K - 1)) htarget_len
    · change reachNext (((true, (G.n, s.val, t.val)), (machine.run I.encode (K - 1)).state),
        reachQM.read G.encode
          ((true, (G.n, s.val, t.val)), (machine.run I.encode (K - 1)).state)) = _
      dsimp only [reachNext]
      rw [ite_eq_right (by decide), ite_eq_right hn_ne]
      have hqK : (Cslib.USTCON.Reader.step (machine.run I.encode (K - 1)).state
          (virtBit G.n s.val t.val (machine.run I.encode (K - 1)).state
            (reachQM.read G.encode
              ((true, (G.n, s.val, t.val)), (machine.run I.encode (K - 1)).state)))).1 = qK :=
        congrArg Prod.fst hstep_last
      rw [hqK, ite_eq_left hdoneK]
    · change reachEmit (((true, (G.n, s.val, t.val)), (machine.run I.encode (K - 1)).state),
        reachQM.read G.encode
          ((true, (G.n, s.val, t.val)), (machine.run I.encode (K - 1)).state)) = _
      dsimp only [reachEmit]
      rw [ite_eq_right (by decide), ite_eq_right hn_ne, hstep_last]
  have hfull := hpreK.trans hlast
  rwa [← hout_last, hK_out] at hfull

private theorem exists_reachQM_run (G : UGraphInstance) :
    ∃ T, reachQM.halted (reachQM.run G.encode T) = true ∧
      (∀ i < T, reachQM.halted (reachQM.run G.encode i) = false) ∧
      reachQM.output G.encode T = ugraphReachTable G ∧
      (∀ i ≤ T, (encReachQState (reachQM.run G.encode i)).length ≤
        reachBoundConst * (Nat.log2 G.encode.length + 1)) := by
  let B := reachBoundConst * (Nat.log2 G.encode.length + 1)
  have hhdr := reachRunSeg_header G
  by_cases hn0 : G.n = 0
  · rw [ite_eq_left hn0] at hhdr
    obtain ⟨T, hr, hp, ho, hb⟩ := hhdr
    refine ⟨T, ?_, hp, ?_, hb⟩
    · change reachQM.halted (reachQM.runFrom G.encode reachQM.init T) = true
      rw [hr]; rfl
    · rw [QueryMachine.output_eq_of_not_halted _ _ hp]
      have hfin : reachQM.finish (reachQM.run G.encode T) = [] := rfl
      rw [hfin, List.append_nil]
      exact ho.trans (by simp [ugraphReachTable, hn0])
  · rw [ite_eq_right hn0] at hhdr
    have htake1_finRange (hm : 0 < G.n) : (List.finRange G.n).take 1 = [⟨0, hm⟩] := by
      refine List.ext_getElem (by simp; omega) fun i _ h2 ↦ ?_
      have hi0 : i = 0 := by simp at h2; omega
      subst hi0
      simp
    have hrow : ∀ s : Fin G.n, ∃ q_end : State,
        ReachRunSeg G.encode B
          ((true, (G.n, s.val, 0)), init)
          (if s.val + 1 < G.n then ((true, (G.n, s.val + 1, 0)), init)
           else ((true, (0, 0, 0)), q_end))
          ((List.finRange G.n).map fun t ↦
            @decide (G.graph.Reachable s t) (Classical.propDecidable _)) := by
      intro s
      have hcol : ∀ m (hm : m < G.n), ∃ q_end : State,
          ReachRunSeg G.encode B
            ((true, (G.n, s.val, 0)), init)
            (if m + 1 < G.n then ((true, (G.n, s.val, m + 1)), init)
             else if s.val + 1 < G.n then ((true, (G.n, s.val + 1, 0)), init)
             else ((true, (0, 0, 0)), q_end))
            (((List.finRange G.n).take (m + 1)).map fun t ↦
              @decide (G.graph.Reachable s t) (Classical.propDecidable _)) := by
        intro m hm
        induction m with
        | zero =>
          obtain ⟨q_end, h0⟩ := reachRunSeg_pair G s ⟨0, hm⟩
          refine ⟨q_end, ?_⟩
          rwa [htake1_finRange hm, List.map_singleton]
        | succ m ih =>
          have hm_lt : m < G.n := by omega
          obtain ⟨_, hprev⟩ := ih hm_lt
          rw [ite_eq_left hm] at hprev
          obtain ⟨q_end, hcur⟩ := reachRunSeg_pair G s ⟨m + 1, hm⟩
          refine ⟨q_end, ?_⟩
          have htake_succ : (List.finRange G.n).take (m + 2) =
              (List.finRange G.n).take (m + 1) ++ [⟨m + 1, hm⟩] := by
            have hlen : m + 1 < (List.finRange G.n).length := by simp [hm]
            simpa using List.take_succ_eq_append_getElem hlen
          rw [htake_succ, List.map_append, List.map_singleton]
          exact hprev.trans hcur
      obtain ⟨q_end, hlast⟩ := hcol (G.n - 1) (by omega)
      have hsub : G.n - 1 + 1 = G.n := by omega
      rw [hsub, ite_eq_right (Nat.lt_irrefl G.n),
        List.take_of_length_le (by simp)] at hlast
      exact ⟨q_end, hlast⟩
    have hall_rows : ∀ m (hm : m < G.n), ∃ q_end : State,
        ReachRunSeg G.encode B
          ((true, (G.n, 0, 0)), init)
          (if m + 1 < G.n then ((true, (G.n, m + 1, 0)), init)
           else ((true, (0, 0, 0)), q_end))
          (((List.finRange G.n).take (m + 1)).flatMap fun s ↦
            (List.finRange G.n).map fun t ↦
              @decide (G.graph.Reachable s t) (Classical.propDecidable _)) := by
      intro m hm
      induction m with
      | zero =>
        obtain ⟨q_end, h0⟩ := hrow ⟨0, hm⟩
        refine ⟨q_end, ?_⟩
        simpa [htake1_finRange hm] using h0
      | succ m ih =>
        have hm_lt : m < G.n := by omega
        obtain ⟨_, hprev⟩ := ih hm_lt
        rw [ite_eq_left hm] at hprev
        obtain ⟨q_end, hcur⟩ := hrow ⟨m + 1, hm⟩
        refine ⟨q_end, ?_⟩
        have htake_succ : (List.finRange G.n).take (m + 2) =
            (List.finRange G.n).take (m + 1) ++ [⟨m + 1, hm⟩] := by
          have hlen : m + 1 < (List.finRange G.n).length := by simp [hm]
          simpa using List.take_succ_eq_append_getElem hlen
        rw [htake_succ, List.flatMap_append, List.flatMap_singleton]
        exact hprev.trans hcur
    obtain ⟨q_end, hbody⟩ := hall_rows (G.n - 1) (by omega)
    have hsub : G.n - 1 + 1 = G.n := by omega
    rw [hsub, ite_eq_right (Nat.lt_irrefl G.n),
      List.take_of_length_le (by simp)] at hbody
    have htotal := hhdr.trans hbody
    rw [List.nil_append] at htotal
    obtain ⟨T, hr, hp, ho, hb⟩ := htotal
    refine ⟨T, ?_, hp, ?_, hb⟩
    · change reachQM.halted (reachQM.runFrom G.encode reachQM.init T) = true
      rw [hr]; rfl
    · rw [QueryMachine.output_eq_of_not_halted _ _ hp]
      have hfin : reachQM.finish (reachQM.run G.encode T) = [] := rfl
      rw [hfin, List.append_nil]
      exact ho

/-- **All-pairs undirected reachability is computable in logarithmic space.** -/
theorem computableInLogSpace_ugraphReachTable :
    ComputableInLogSpace ugraphReachTable encUGraph encBits := by
  classical
  choose timeF hhalt hpre hout hsize using exists_reachQM_run
  exact reachQM.computableInLogSpace
    reachQuery_inSpace reachNext_inSpace reachEmit_inSpace
    reachHalted_inSpace reachFinish_inSpace
    timeF hhalt hpre (fun G ↦ (hout G).symm) ⟨reachBoundConst, hsize⟩

end ReachQueryMachine

end Cslib.USTCON
