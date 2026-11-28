/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.DeterminantOracleMachine

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Three-Layer Buntrock--Damm--Hertrampf--Meinel Circuit Compiler

This module constructs the three-layer relativized $\mathrm{NC}^1(\mathrm{det}_{\mathbb{Z}_k})$
circuit family (`Cslib.Complexity.buildBuntrockCircuit`) simulating a logspace
deterministic oracle Turing machine `M` relative to an oracle language `O ∈ DETk k`, and proves
that the resulting language belongs to `DETk k`
(`Cslib.Complexity.buntrockCircuitLanguage_mem_DETk`) under standard Lean axioms.

## Main definitions

* `Cslib.Complexity.WPTarget`, `Cslib.Complexity.WPNode`,
  `Cslib.Complexity.decodeControlWork`,
  `Cslib.Complexity.wpWorkStep`,
  `Cslib.Complexity.wpClassifyStep`: single-work-phase deterministic transition graph
  extracting query lengths, query bits, post-query targets, and accepting halts.
* `Cslib.Complexity.buntrockLayer1Circuit`,
  `Cslib.Complexity.buildBuntrockCircuit`,
  `Cslib.Complexity.buntrockCircuitLanguage`: three-layer $\mathrm{DET}_k$ circuit
  family for $M^O$.

## Main results

* `Cslib.Complexity.biTape_represents_unique`: uniqueness of `BiTape` representing a
  given integer-indexed tape at a given head position.
* `Cslib.Complexity.decodeControlWork_eq_some_iff`,
  `Cslib.Complexity.card_wpNode_le`: exact register decoding and polynomial state
  bound on `WPNode`.
* `Cslib.Complexity.eval_buntrockLayer1Circuit`,
  `Cslib.Complexity.eval_buildBuntrockCircuit_eq`: exact evaluation of Layer-1 and
  full three-layer Buntrock determinant circuits on an input word `w`.
* `Cslib.Complexity.buntrockCircuitLanguage_mem_DETk`: for every $k \ge 2$ and valid
  $\mathrm{DET}_k$ circuit family `CO` for `O`, `buntrockCircuitLanguage k CO M c ∈ DETk k`.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

private theorem stackTape_eq_of_read_eq {Symbol : Type*} {a b : Cslib.Turing.StackTape Symbol}
    (h : ∀ p : ℕ, a.read p = b.read p) : a = b := by
  suffices key : ∀ m : ℕ, ∀ x y : Cslib.Turing.StackTape Symbol,
      x.toList.length + y.toList.length = m → (∀ p : ℕ, x.read p = y.read p) → x = y from
    key _ a b rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro x y hm hxy
    by_cases hz : m = 0
    · exact Cslib.Turing.StackTape.ext
        ((List.length_eq_zero_iff.mp (by omega)).trans
          (List.length_eq_zero_iff.mp (by omega)).symm)
    · have hlt : x.tail.toList.length + y.tail.toList.length < m := by
        simp only [Cslib.Turing.StackTape.tail_toList, List.length_tail]; omega
      exact (Cslib.Turing.StackTape.eq_iff x y).mpr
        ⟨hxy 0, ih _ hlt x.tail y.tail rfl fun p ↦ hxy (p + 1)⟩

/-- Any two `BiTape`s representing the same integer-indexed tape contents at the same head position
are equal. -/
theorem biTape_represents_unique {Symbol : Type*} {t₁ t₂ : Cslib.Turing.BiTape Symbol}
    {contents : ℤ → Option Symbol} {head : ℤ}
    (h₁ : t₁.Represents contents head) (h₂ : t₂.Represents contents head) : t₁ = t₂ := by
  have hread : ∀ p : ℤ, t₁.read p = t₂.read p := fun p ↦ (h₁ p).trans (h₂ p).symm
  exact Cslib.Turing.BiTape.ext (hread 0)
    (stackTape_eq_of_read_eq fun p ↦ hread (Int.negSucc p))
    (stackTape_eq_of_read_eq fun p ↦ hread (Int.ofNat (p + 1)))

/-- Target predicates extracted from a single deterministic work phase of `M` (at most `N` steps)
starting at round-start vertex `u₀ : Fin N`. -/
inductive WPTarget (N : ℕ)
  | queryLen (L : Fin (N + 1))
  | queryBit (j : Fin N)
  | yesTarget (v : Fin N)
  | noTarget (v : Fin N)
  | accHalt

/-- State space of the `(N + 1)`-step single-work-phase deterministic DAG: `some (u, qlen, b)` for
an active configuration at vertex `u`, emitted query length `qlen ≤ N`, and tracked bit flag `b`,
or `none` for the accepted target sink at step `N + 1`. -/
abbrev WPNode (N : ℕ) :=
  Option (Fin N × Fin (N + 1) × Bool)

/-- Decode the unique `(q, work)` matching registers `r`, if any. -/
noncomputable def decodeControlWork {k_tapes : ℕ} {State : Type} [Fintype State]
    (r : Register k_tapes → ℕ) : Option (State × (Fin k_tapes → Option Bool)) := by
  classical
  exact (Finset.univ : Finset (State × (Fin k_tapes → Option Bool))).toList.find? fun qw ↦
    decide (r .control = stateCode (some qw.1)) &&
      (List.ofFn fun i : Fin k_tapes ↦ decide (r (.head i) = symbolCode (qw.2 i))).all id

theorem decodeControlWork_eq_some_iff {k_tapes : ℕ} {State : Type} [Fintype State]
    (r : Register k_tapes → ℕ) (qw : State × (Fin k_tapes → Option Bool)) :
    decodeControlWork r = some qw ↔
      r .control = stateCode (some qw.1) ∧
        ∀ i, r (.head i) = symbolCode (qw.2 i) := by
  classical
  let pred (x : State × (Fin k_tapes → Option Bool)) : Bool :=
    decide (r .control = stateCode (some x.1)) &&
      (List.ofFn fun i : Fin k_tapes ↦ decide (r (.head i) = symbolCode (x.2 i))).all id
  have hpred_iff (x : State × (Fin k_tapes → Option Bool)) :
      pred x = true ↔ r .control = stateCode (some x.1) ∧
        ∀ i, r (.head i) = symbolCode (x.2 i) := by
    simp [pred, List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  have hpred_uniq {x y} (hx : pred x = true) (hy : pred y = true) : x = y := by
    obtain ⟨hx1, hx2⟩ := (hpred_iff x).mp hx
    obtain ⟨hy1, hy2⟩ := (hpred_iff y).mp hy
    have hq : x.1 = y.1 := Option.some.inj (stateCode_injective (hx1.symm.trans hy1))
    have hw : x.2 = y.2 := funext fun i ↦ symbolCode_injective ((hx2 i).symm.trans (hy2 i))
    exact Prod.ext hq hw
  change (Finset.univ.toList).find? pred = some qw ↔ _
  rw [← hpred_iff qw]
  constructor
  · intro h
    exact List.find?_some h
  · intro hqw
    have hmem : qw ∈ (Finset.univ : Finset _).toList := Finset.mem_toList.mpr (Finset.mem_univ qw)
    obtain ⟨y, hy⟩ := List.find?_isSome.mpr ⟨qw, hmem, hqw⟩ |> Option.isSome_iff_exists.mp
    rw [hy, Option.some.injEq]
    exact hpred_uniq (List.find?_some hy) hqw

/-- Deterministic work-phase transition on `WPNode N` for `t < N` (advancing `.step` and freezing on
`.query` / `.halt`), parameterized by `optJ : Option (Fin N)` (the query bit position to record). -/
@[expose]
noncomputable def wpWorkStep {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (B n : ℕ)
    (optJ : Option (Fin (vertexBound (k := k_tapes) B)))
    (symOf : Fin (vertexBound (k := k_tapes) B) → Option Bool) :
    WPNode (vertexBound (k := k_tapes) B) → Option (WPNode (vertexBound (k := k_tapes) B))
  | none => none
  | some (u, qlen, b) =>
    let N := vertexBound (k := k_tapes) B
    let r := readRegisters (k := k_tapes) B u.val
    if valid (k := k_tapes) (State := State) B n u.val && decide (r .output = 0) then
      match decodeControlWork (State := State) r with
      | none => none
      | some (q, work) =>
        match M.tr q (inputSymbol n (r .inputPos) (symOf u)) work with
        | .step moveIn moveWork emit nextQ =>
          let act : Action k_tapes Bool State := ⟨moveIn, moveWork, none, some nextQ⟩
          let r' := nextRegisters n r act
          let nextLen := qlen.val + (if emit.isSome then 1 else 0)
          if hfit : fitsB B r' = true ∧ nextLen < N + 1 then
            let vVal := Cslib.Radix.pack B r'
            if hv : vVal < N ∧ valid (k := k_tapes) (State := State) B n vVal = true then
              let hitBit : Bool :=
                match optJ, emit with
                | some j, some true => decide (qlen.val = j.val)
                | _, _ => false
              some (some (⟨vVal, hv.1⟩, ⟨nextLen, hfit.2⟩, b || hitBit))
            else none
          else none
        | .query _ _ => some (some (u, qlen, b))
        | .halt _ => some (some (u, qlen, b))
    else none

@[simp]
theorem wpWorkStep_none {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (B n : ℕ)
    (optJ : Option (Fin (vertexBound (k := k_tapes) B)))
    (symOf : Fin (vertexBound (k := k_tapes) B) → Option Bool) :
    wpWorkStep M B n optJ symOf none = none :=
  rfl

theorem wpWorkStep_some {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (B n : ℕ)
    (optJ : Option (Fin (vertexBound (k := k_tapes) B)))
    (symOf : Fin (vertexBound (k := k_tapes) B) → Option Bool)
    (u : Fin (vertexBound (k := k_tapes) B))
    (qlen : Fin (vertexBound (k := k_tapes) B + 1)) (b : Bool) :
    wpWorkStep M B n optJ symOf (some (u, qlen, b)) =
      let N := vertexBound (k := k_tapes) B
      let r := readRegisters (k := k_tapes) B u.val
      if valid (k := k_tapes) (State := State) B n u.val && decide (r .output = 0) then
        match decodeControlWork (State := State) r with
        | none => none
        | some (q, work) =>
          match M.tr q (inputSymbol n (r .inputPos) (symOf u)) work with
          | .step moveIn moveWork emit nextQ =>
            let act : Action k_tapes Bool State := ⟨moveIn, moveWork, none, some nextQ⟩
            let r' := nextRegisters n r act
            let nextLen := qlen.val + (if emit.isSome then 1 else 0)
            if hfit : fitsB B r' = true ∧ nextLen < N + 1 then
              let vVal := Cslib.Radix.pack B r'
              if hv : vVal < N ∧ valid (k := k_tapes) (State := State) B n vVal = true then
                let hitBit : Bool :=
                  match optJ, emit with
                  | some j, some true => decide (qlen.val = j.val)
                  | _, _ => false
                some (some (⟨vVal, hv.1⟩, ⟨nextLen, hfit.2⟩, b || hitBit))
              else none
            else none
          | .query _ _ => some (some (u, qlen, b))
          | .halt _ => some (some (u, qlen, b))
      else none :=
  rfl

/-- Classification step `t = N` on `WPNode N` testing `tgt : WPTarget N` and transitioning to `none`
when satisfied. -/
@[expose]
noncomputable def wpClassifyStep {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (B n : ℕ)
    (tgt : WPTarget (vertexBound (k := k_tapes) B))
    (symOf : Fin (vertexBound (k := k_tapes) B) → Option Bool) :
    WPNode (vertexBound (k := k_tapes) B) → Option (WPNode (vertexBound (k := k_tapes) B))
  | none => none
  | some (u, qlen, b) =>
    let r := readRegisters (k := k_tapes) B u.val
    if valid (k := k_tapes) (State := State) B n u.val && decide (r .output = 0) then
      match decodeControlWork (State := State) r with
      | none => none
      | some (q, work) =>
        match M.tr q (inputSymbol n (r .inputPos) (symOf u)) work, tgt with
        | .query _ _, .queryLen L => if qlen = L then some none else none
        | .query _ _, .queryBit _ => if b then some none else none
        | .query onYes _, .yesTarget v =>
          let act : Action k_tapes Bool State := ⟨.zero, fun _ ↦ (none, .zero), none, some onYes⟩
          let r' := nextRegisters n r act
          if fitsB B r' && decide (v.val = Cslib.Radix.pack B r') &&
             valid (k := k_tapes) (State := State) B n v.val then
            some none
          else none
        | .query _ onNo, .noTarget v =>
          let act : Action k_tapes Bool State := ⟨.zero, fun _ ↦ (none, .zero), none, some onNo⟩
          let r' := nextRegisters n r act
          if fitsB B r' && decide (v.val = Cslib.Radix.pack B r') &&
             valid (k := k_tapes) (State := State) B n v.val then
            some none
          else none
        | .halt true, .accHalt => some none
        | _, _ => none
    else none

@[simp]
theorem wpClassifyStep_none {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (B n : ℕ)
    (tgt : WPTarget (vertexBound (k := k_tapes) B))
    (symOf : Fin (vertexBound (k := k_tapes) B) → Option Bool) :
    wpClassifyStep M B n tgt symOf none = none :=
  rfl

theorem wpClassifyStep_some {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (B n : ℕ)
    (tgt : WPTarget (vertexBound (k := k_tapes) B))
    (symOf : Fin (vertexBound (k := k_tapes) B) → Option Bool)
    (u : Fin (vertexBound (k := k_tapes) B))
    (qlen : Fin (vertexBound (k := k_tapes) B + 1)) (b : Bool) :
    wpClassifyStep M B n tgt symOf (some (u, qlen, b)) =
      let r := readRegisters (k := k_tapes) B u.val
      if valid (k := k_tapes) (State := State) B n u.val && decide (r .output = 0) then
        match decodeControlWork (State := State) r with
        | none => none
        | some (q, work) =>
          match M.tr q (inputSymbol n (r .inputPos) (symOf u)) work, tgt with
          | .query _ _, .queryLen L => if qlen = L then some none else none
          | .query _ _, .queryBit _ => if b then some none else none
          | .query onYes _, .yesTarget v =>
            let act : Action k_tapes Bool State := ⟨.zero, fun _ ↦ (none, .zero), none, some onYes⟩
            let r' := nextRegisters n r act
            if fitsB B r' && decide (v.val = Cslib.Radix.pack B r') &&
               valid (k := k_tapes) (State := State) B n v.val then
              some none
            else none
          | .query _ onNo, .noTarget v =>
            let act : Action k_tapes Bool State := ⟨.zero, fun _ ↦ (none, .zero), none, some onNo⟩
            let r' := nextRegisters n r act
            if fitsB B r' && decide (v.val = Cslib.Radix.pack B r') &&
               valid (k := k_tapes) (State := State) B n v.val then
              some none
            else none
          | .halt true, .accHalt => some none
          | _, _ => none
      else none :=
  rfl

theorem card_wpNode_le (N : ℕ) :
    Fintype.card (WPNode N) ≤ 2 * (N + 1) ^ 2 + 1 := by
  simp only [WPNode, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  nlinarith

private noncomputable def buntrockLayer1StepSpec (k : ℕ) {k_tapes : ℕ} {State : Type}
    [Fintype State] (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ)
    (tgt : WPTarget (vertexBound (k := k_tapes) Bn))
    (s : Fin (vertexBound (k := k_tapes) Bn + 1)) :
    SingleVarMatrixSpec k n (Fintype.card (WPNode (vertexBound (k := k_tapes) Bn))) :=
  let Nn := vertexBound (k := k_tapes) Bn
  let eWP : WPNode Nn ≃ Fin (Fintype.card (WPNode Nn)) := Fintype.equivFin (WPNode Nn)
  let optJ : Option (Fin Nn) :=
    match tgt with
    | .queryBit j => some j
    | _ => none
  { readIdx := fun i _ ↦
      match eWP.symm i with
      | none => none
      | some (u, _, _) =>
        let q := queryIndex (k := k_tapes) Bn u.val
        if hq : q < n then some ⟨q, hq⟩ else none
    valFalse := fun i j ↦
      let symOf (u : Fin Nn) : Option Bool :=
        if queryIndex (k := k_tapes) Bn u.val < n then some false else none
      let nxt :=
        if s.val < Nn then wpWorkStep M Bn n optJ symOf (eWP.symm i)
        else wpClassifyStep M Bn n tgt symOf (eWP.symm i)
      let _ : Decidable (nxt = some (eWP.symm j)) := Classical.propDecidable _
      if nxt = some (eWP.symm j) then 1 else 0
    valTrue := fun i j ↦
      let symOf (_ : Fin Nn) : Option Bool := some true
      let nxt :=
        if s.val < Nn then wpWorkStep M Bn n optJ symOf (eWP.symm i)
        else wpClassifyStep M Bn n tgt symOf (eWP.symm i)
      let _ : Decidable (nxt = some (eWP.symm j)) := Classical.propDecidable _
      if nxt = some (eWP.symm j) then 1 else 0 }

/-- Single Layer-1 single-literal determinant circuit testing work-phase target `tgt` from
round-start configuration `u₀` at radix `Bn` and input length `n`. -/
noncomputable def buntrockLayer1Circuit (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn))
    (tgt : WPTarget (vertexBound (k := k_tapes) Bn)) :
    Circuit oracleSignature n 1 :=
  let Nn := vertexBound (k := k_tapes) Bn
  let eWP : WPNode Nn ≃ Fin (Fintype.card (WPNode Nn)) := Fintype.equivFin (WPNode Nn)
  let hMwp_pos : 0 < Fintype.card (WPNode Nn) := Fintype.card_pos_iff.mpr ⟨none⟩
  singleLiteralDetCircuit
    (layeredDAGSpec hMwp_pos (eWP (some (u₀, ⟨0, Nat.succ_pos Nn⟩, false)))
      (buntrockLayer1StepSpec k M Bn n tgt) (Pi.single (eWP none) 1)) 0 true

/-- Exact evaluation of `buntrockLayer1Circuit` on an input word `w`: for `k ≥ 2`, its output bit
equals whether `(N + 1)` deterministic transitions of `(wpWorkStep / wpClassifyStep)` reach `none`.
-/
theorem eval_buntrockLayer1Circuit {k : ℕ} (hk : 2 ≤ k) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn : ℕ) (w : List Bool)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn))
    (tgt : WPTarget (vertexBound (k := k_tapes) Bn)) :
    let Nn := vertexBound (k := k_tapes) Bn
    let eWP := Fintype.equivFin (WPNode Nn)
    let symOf (u : Fin Nn) : Option Bool := w[queryIndex (k := k_tapes) Bn u.val]?
    let wpNext (s : Fin (Nn + 1)) (i : Fin (Fintype.card (WPNode Nn))) :
        Option (Fin (Fintype.card (WPNode Nn))) :=
      let optJ : Option (Fin Nn) := match tgt with | .queryBit j => some j | _ => none
      let res :=
        if s.val < Nn then wpWorkStep M Bn w.length optJ symOf (eWP.symm i)
        else wpClassifyStep M Bn w.length tgt symOf (eWP.symm i)
      res.map eWP
    (buntrockLayer1Circuit k M Bn w.length u₀ tgt).eval
      (oracleInterpretation (detZModLanguage k)) (fun i : Fin w.length ↦ w[i.val]) 0 =
      decide (iterOpt (eWP (some (u₀, ⟨0, Nat.succ_pos Nn⟩, false))) wpNext (Nn + 1) le_rfl =
        some (eWP none)) := by
  have hk_ne : NeZero k := ⟨by omega⟩
  have h1_ne : (1 : ZMod k) ≠ 0 := zmod_one_ne_zero hk
  intro Nn eWP symOf wpNext
  let xIn : Fin w.length → Bool := fun i ↦ w[i.val]
  dsimp only [buntrockLayer1Circuit]
  have heWP_def : Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)) = eWP := rfl
  rw [eval_singleLiteralDetCircuit, Bool.true_xor, det_layeredDAGSpec_eval]
  have hstep_det : ∀ (s : Fin (Nn + 1)) (i j : Fin (Fintype.card (WPNode Nn))),
      (buntrockLayer1StepSpec k M Bn w.length tgt s).eval xIn i j =
        if wpNext s i = some j then 1 else 0 := by
    intro s i j
    have hequiv (o : Option (WPNode Nn)) :
        (o = some (eWP.symm j)) ↔ (o.map eWP = some j) := by
      cases o with
      | none => simp
      | some x =>
        simp only [Option.some.injEq, Option.map_some]
        exact ⟨fun h ↦ by rw [h, Equiv.apply_symm_apply],
          fun h ↦ by rw [← h, Equiv.symm_apply_apply]⟩
    have hite_eq {o₁ o₂ : Option (WPNode Nn)} (ho : o₁ = o₂) :
        @ite _ (o₁ = some (eWP.symm j)) (Classical.propDecidable _) (1 : ZMod k) 0 =
          if o₂.map eWP = some j then 1 else 0 := by
      subst ho
      by_cases hm : o₁.map eWP = some j
      · rw [ite_eq_left hm, ite_eq_left ((hequiv o₁).mpr hm)]
      · rw [ite_eq_right hm, ite_eq_right (fun h ↦ hm ((hequiv o₁).mp h))]
    let optJ : Option (Fin Nn) := match tgt with | .queryBit j => some j | _ => none
    let fFalse (u : Fin Nn) : Option Bool :=
      if queryIndex (k := k_tapes) Bn u.val < w.length then some false else none
    let stepFn (f : Fin Nn → Option Bool) (nd : WPNode Nn) : Option (WPNode Nn) :=
      if s.val < Nn then wpWorkStep M Bn w.length optJ f nd
      else wpClassifyStep M Bn w.length tgt f nd
    cases hnode : eWP.symm i with
    | none =>
      have hread : (buntrockLayer1StepSpec k M Bn w.length tgt s).readIdx i j = none := by
        dsimp only [buntrockLayer1StepSpec]; rw [heWP_def, hnode]
      have hfalse : (buntrockLayer1StepSpec k M Bn w.length tgt s).valFalse i j = 0 := by
        dsimp only [buntrockLayer1StepSpec]
        exact (hite_eq (o₂ := none) (by rw [heWP_def, hnode]; split_ifs <;> rfl)).trans rfl
      have hwp : wpNext s i = none := by
        dsimp only [wpNext]; rw [hnode]; split_ifs <;> rfl
      rw [SingleVarMatrixSpec.eval_apply, hread, hfalse, hwp]; rfl
    | some uqb =>
      rcases uqb with ⟨u, qlen, b⟩
      have hread : (buntrockLayer1StepSpec k M Bn w.length tgt s).readIdx i j =
          if hq : queryIndex (k := k_tapes) Bn u.val < w.length then some ⟨_, hq⟩ else none := by
        dsimp only [buntrockLayer1StepSpec]; rw [heWP_def, hnode]
      have hstep_loc (f₁ f₂ : Fin Nn → Option Bool) (hf : f₁ u = f₂ u) :
          stepFn f₁ (some (u, qlen, b)) = stepFn f₂ (some (u, qlen, b)) := by
        dsimp only [stepFn, wpWorkStep, wpClassifyStep]; rw [hf]
      have hfalse : (buntrockLayer1StepSpec k M Bn w.length tgt s).valFalse i j =
          if (stepFn fFalse (some (u, qlen, b))).map eWP = some j then 1 else 0 := by
        dsimp only [buntrockLayer1StepSpec]
        exact hite_eq (by dsimp only [stepFn, optJ, fFalse]; rw [heWP_def, hnode])
      have htrue : (buntrockLayer1StepSpec k M Bn w.length tgt s).valTrue i j =
          if (stepFn (fun _ ↦ some true) (some (u, qlen, b))).map eWP = some j then 1 else 0 := by
        dsimp only [buntrockLayer1StepSpec]
        exact hite_eq (by dsimp only [stepFn, optJ]; rw [heWP_def, hnode])
      have hwp : wpNext s i = (stepFn symOf (some (u, qlen, b))).map eWP := by
        dsimp only [wpNext, stepFn, optJ]; rw [hnode]; cases tgt <;> rfl
      rw [SingleVarMatrixSpec.eval_apply, hread, hfalse, htrue, hwp]
      by_cases hq : queryIndex (k := k_tapes) Bn u.val < w.length
      · simp only [hq, ↓reduceDIte]
        have hget : symOf u = some (xIn ⟨_, hq⟩) := List.getElem?_eq_getElem hq
        cases hx : xIn ⟨_, hq⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hstep_loc fFalse symOf (by simp [fFalse, hq, hget, hx])]
        · simp only [↓reduceIte]
          rw [hstep_loc (fun _ ↦ some true) symOf (by simp [hget, hx])]
      · simp only [hq, ↓reduceDIte]
        have hget : symOf u = none := List.getElem?_eq_none (not_lt.mp hq)
        rw [hstep_loc fFalse symOf (by simp [fFalse, hq, hget])]
  rw [heWP_def, walkVec_option_deterministic _ wpNext _ hstep_det (Nn + 1) le_rfl]
  cases hres : iterOpt (eWP (some (u₀, ⟨0, Nat.succ_pos Nn⟩, false))) wpNext (Nn + 1) le_rfl with
  | none => simp
  | some idx =>
    rw [Finset.sum_eq_single idx]
    · by_cases heq : idx = eWP none
      · subst heq; simp [h1_ne]
      · simp [heq]
    · intro i' _ hne; simp [Pi.single_eq_of_ne hne]
    · simp

private abbrev buntrockB1 (Nn : ℕ) : ℕ :=
  (Nn + 1) + Nn + Nn + Nn + 1

private def decodeBuntrockB1 (Nn : ℕ) (idx : Fin (buntrockB1 Nn)) : WPTarget Nn :=
  if h1 : idx.val < Nn + 1 then .queryLen ⟨idx.val, h1⟩
  else if h2 : idx.val - (Nn + 1) < Nn then .queryBit ⟨idx.val - (Nn + 1), h2⟩
  else if h3 : idx.val - ((Nn + 1) + Nn) < Nn then
    .yesTarget ⟨idx.val - ((Nn + 1) + Nn), h3⟩
  else if h4 : idx.val - ((Nn + 1) + Nn + Nn) < Nn then
    .noTarget ⟨idx.val - ((Nn + 1) + Nn + Nn), h4⟩
  else .accHalt

private def hasLenWire (Nn : ℕ) (u₀ : Fin Nn) (L : Fin (Nn + 1)) : Fin (Nn * buntrockB1 Nn) :=
  ⟨u₀.val * buntrockB1 Nn + L.val, by
    have hu := u₀.isLt; have hL := L.isLt; dsimp [buntrockB1]; nlinarith⟩

private def qBitWire (Nn : ℕ) (u₀ : Fin Nn) (j : Fin Nn) : Fin (Nn * buntrockB1 Nn) :=
  ⟨u₀.val * buntrockB1 Nn + ((Nn + 1) + j.val), by
    have hu := u₀.isLt; have hj := j.isLt; dsimp [buntrockB1]; nlinarith⟩

private def yesWire (Nn : ℕ) (u₀ v : Fin Nn) : Fin (Nn * buntrockB1 Nn) :=
  ⟨u₀.val * buntrockB1 Nn + ((Nn + 1) + Nn + v.val), by
    have hu := u₀.isLt; have hv := v.isLt; dsimp [buntrockB1]; nlinarith⟩

private def noWire (Nn : ℕ) (u₀ v : Fin Nn) : Fin (Nn * buntrockB1 Nn) :=
  ⟨u₀.val * buntrockB1 Nn + ((Nn + 1) + Nn + Nn + v.val), by
    have hu := u₀.isLt; have hv := v.isLt; dsimp [buntrockB1]; nlinarith⟩

private def accWire (Nn : ℕ) (u₀ : Fin Nn) : Fin (Nn * buntrockB1 Nn) :=
  ⟨u₀.val * buntrockB1 Nn + ((Nn + 1) + Nn + Nn + Nn), by
    have hu := u₀.isLt; dsimp [buntrockB1]; nlinarith⟩

private def qAnsWire (Nn : ℕ) (u₀ : Fin Nn) (L : Fin (Nn + 1)) : Fin (Nn * (Nn + 1)) :=
  ⟨u₀.val * (Nn + 1) + L.val, by
    have hu := u₀.isLt; have hL := L.isLt; nlinarith⟩

private noncomputable def buntrockLayer1 (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ) :
    Circuit oracleSignature n
      (vertexBound (k := k_tapes) Bn * buntrockB1 (vertexBound (k := k_tapes) Bn)) :=
  let Nn := vertexBound (k := k_tapes) Bn
  let B₁ := buntrockB1 Nn
  Circuit.pi fun p : Fin (Nn * B₁) ↦
    let u₀ : Fin Nn :=
      ⟨p.val / B₁, Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
    let idx : Fin B₁ := ⟨p.val % B₁, Nat.mod_lt _ (by dsimp [B₁, buntrockB1]; omega)⟩
    buntrockLayer1Circuit k M Bn n u₀ (decodeBuntrockB1 Nn idx)

private def buntrockOracleAnsLayer (CO : ∀ q, Circuit oracleSignature q 1) (Nn : ℕ) :
    Circuit oracleSignature (Nn * buntrockB1 Nn) (Nn * (Nn + 1)) :=
  Circuit.pi fun p : Fin (Nn * (Nn + 1)) ↦
    let u₀ : Fin Nn :=
      ⟨p.val / (Nn + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
    let L : Fin (Nn + 1) := ⟨p.val % (Nn + 1), Nat.mod_lt _ (Nat.succ_pos Nn)⟩
    (CO L.val).comp (Circuit.wiring oracleSignature fun j : Fin L.val ↦
      qBitWire Nn u₀ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp L.isLt)⟩)

private def buntrockLayer2a (CO : ∀ q, Circuit oracleSignature q 1) (Nn : ℕ) :
    Circuit oracleSignature (Nn * buntrockB1 Nn) (Nn * buntrockB1 Nn + Nn * (Nn + 1)) :=
  (Circuit.id oracleSignature (Nn * buntrockB1 Nn)).append (buntrockOracleAnsLayer CO Nn)

private def buntrockOrAnsDM (Nn : ℕ) (u₀ : Fin Nn) :
    Circuit signature (Nn * buntrockB1 Nn + Nn * (Nn + 1)) 1 :=
  Circuit.balanced (Circuit.oneGate (σ := signature) .or ![0, 1])
    (Circuit.oneGate (σ := signature) (.const false) Fin.elim0)
    (List.ofFn fun L : Fin (Nn + 1) ↦
      (Circuit.oneGate (σ := signature) .and ![0, 1]).comp
        (Circuit.wiring signature ![Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L),
          Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L)]))

private def buntrockStepMuxFn (b : Fin 3 → Bool) : Bool :=
  (b 0 && b 2) || (b 1 && !b 2)

private def buntrockLayer2bDM (Nn : ℕ) :
    Circuit signature (Nn * buntrockB1 Nn + Nn * (Nn + 1)) (Nn * (Nn + 1)) :=
  let stepMuxDM : Circuit signature 3 1 := truthTableCircuit1 3 buntrockStepMuxFn
  Circuit.pi fun p : Fin (Nn * (Nn + 1)) ↦
    let u₀ : Fin Nn :=
      ⟨p.val / (Nn + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
    let col : Fin (Nn + 1) := ⟨p.val % (Nn + 1), Nat.mod_lt _ (Nat.succ_pos Nn)⟩
    if hv : col.val < Nn then
      let v : Fin Nn := ⟨col.val, hv⟩
      stepMuxDM.comp
        ((Circuit.wiring signature (fun _ : Fin 1 ↦
            Fin.castAdd (Nn * (Nn + 1)) (yesWire Nn u₀ v))).append
          ((Circuit.wiring signature (fun _ : Fin 1 ↦
              Fin.castAdd (Nn * (Nn + 1)) (noWire Nn u₀ v))).append
            (buntrockOrAnsDM Nn u₀)))
    else
      Circuit.wiring signature fun _ : Fin 1 ↦ Fin.castAdd (Nn * (Nn + 1)) (accWire Nn u₀)

private theorem buntrockStartLt {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (c n : ℕ) :
    startID M.envelopeNTM (radix (radixExponent State c) n) <
      vertexBound (k := k_tapes) (radix (radixExponent State c) n) := by
  let D : ℕ := radixExponent State c
  let Bn : ℕ := radix D n
  let w₀ := List.replicate n false
  have hD : 2 ≤ D := by simp only [D, radixExponent]; omega
  have hbase : w₀.length + 2 ≤ Bn := by
    simp only [w₀, List.length_replicate, Bn, radix]
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ (n + 2) ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have hc_lt : Fintype.card (Option State) < Bn :=
    Nat.lt_of_succ_lt (card_succ_lt_radix c n)
  have h3_lt : 3 < Bn :=
    calc 3 < 2 ^ 2 := by decide
      _ ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ Bn := Nat.pow_le_pow_right (by omega) hD
  have hfit₀ : Fits Bn (registers (M.envelopeNTM.initView w₀)) := by
    intro i
    cases i with
    | inputPos =>
      simpa [registers, MultiTapeNTM.initView, FiniteCfg.init] using
        lt_of_lt_of_le (by omega : 1 < w₀.length + 2) hbase
    | control => exact (Fintype.equivFin (Option State) _).isLt.trans hc_lt
    | output => exact (outputCode_lt _).trans h3_lt
    | head _ => simpa [registers] using (symbolCode_lt _).trans h3_lt
    | left _ | right _ =>
      simpa [registers, MultiTapeNTM.initView, FiniteCfg.init, Cslib.Turing.BiTape.nil] using
        Nat.zero_lt_of_lt h3_lt
  rw [← vertexID_init M.envelopeNTM Bn w₀]
  exact vertexID_lt hfit₀

private def buntrockRoundStepSpec (k Nn : ℕ) : SingleVarMatrixSpec k (Nn * (Nn + 1)) (Nn + 1) where
  readIdx i j :=
    if hi : i.val < Nn then
      some ⟨i.val * (Nn + 1) + j.val, by have := j.isLt; nlinarith⟩
    else none
  valFalse i j :=
    if i.val < Nn then 0 else if j.val = Nn then 1 else 0
  valTrue i j :=
    if i.val < Nn then 1 else if j.val = Nn then 1 else 0

private def buntrockLayer3 (k Nn : ℕ) (startIdx : Fin Nn) :
    Circuit oracleSignature (Nn * (Nn + 1)) 1 :=
  singleLiteralDetCircuit
    (layeredDAGSpec (Nat.succ_pos Nn) (Fin.castSucc startIdx)
      (fun _ : Fin (Nn + 1) ↦ buntrockRoundStepSpec k Nn)
      (Pi.single (Fin.last Nn) 1))
    0 true

private theorem size_buntrockLayer1_le (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ) :
    (buntrockLayer1 k M Bn n).size ≤
      (vertexBound (k := k_tapes) Bn * buntrockB1 (vertexBound (k := k_tapes) Bn)) * (n + 4) := by
  let Nn := vertexBound (k := k_tapes) Bn
  let B₁ := buntrockB1 Nn
  unfold buntrockLayer1
  rw [Circuit.size_pi]
  calc ∑ p : Fin (Nn * B₁), _
      ≤ ∑ _p : Fin (Nn * B₁), (n + 4) :=
        Finset.sum_le_sum fun _ _ ↦ by
          unfold buntrockLayer1Circuit
          exact size_singleLiteralDetCircuit_le _ _ _
    _ = (Nn * B₁) * (n + 4) := by simp

private theorem fanInAtMost_buntrockLayer1 (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn n r : ℕ) (h2 : 2 ≤ r)
    (henc : DetZModInstance.encodedLen k
      ((vertexBound (k := k_tapes) Bn + 1 + 1) *
        Fintype.card (WPNode (vertexBound (k := k_tapes) Bn)) + 1) ≤ r) :
    (buntrockLayer1 k M Bn n).FanInAtMost r := by
  unfold buntrockLayer1
  exact Circuit.fanInAtMost_pi fun _ ↦ by
    unfold buntrockLayer1Circuit
    exact (fanInAtMost_singleLiteralDetCircuit _ _ _).mono (max_le h2 henc)

private theorem depthWith_buntrockLayer1_le (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ) :
    (buntrockLayer1 k M Bn n).depthWith nc1OracleDepthWeight ≤
      4 + Nat.log 2 (DetZModInstance.encodedLen k
        ((vertexBound (k := k_tapes) Bn + 1 + 1) *
          Fintype.card (WPNode (vertexBound (k := k_tapes) Bn)) + 1)) := by
  unfold buntrockLayer1
  exact Circuit.depthWith_pi_le (σ := oracleSignature) nc1OracleDepthWeight _ fun _ ↦ by
    dsimp only [buntrockLayer1Circuit]
    exact (depthWith_singleLiteralDetCircuit_le _ _ _).trans (by omega)

private theorem eval_buntrockLayer1 (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ)
    (I : Interpretation oracleSignature Bool) (xIn : Fin n → Bool)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn))
    (wIdx : Fin (vertexBound (k := k_tapes) Bn * buntrockB1 (vertexBound (k := k_tapes) Bn)))
    (off : ℕ) (hoff : off < buntrockB1 (vertexBound (k := k_tapes) Bn))
    (hw : wIdx.val = u₀.val * buntrockB1 (vertexBound (k := k_tapes) Bn) + off) :
    (buntrockLayer1 k M Bn n).eval I xIn wIdx =
      (buntrockLayer1Circuit k M Bn n u₀ (decodeBuntrockB1 _ ⟨off, hoff⟩)).eval I xIn 0 := by
  let Nn := vertexBound (k := k_tapes) Bn
  let B₁ := buntrockB1 Nn
  have hB₁_pos : 0 < B₁ := by dsimp [B₁, buntrockB1]; omega
  have hdiv : wIdx.val / B₁ = u₀.val := by
    dsimp only [B₁, Nn]
    rw [hw, Nat.mul_comm, Nat.mul_add_div hB₁_pos, Nat.div_eq_of_lt hoff, add_zero]
  have hmod : wIdx.val % B₁ = off := by
    dsimp only [B₁, Nn]
    rw [hw, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hoff]
  unfold buntrockLayer1
  dsimp only []
  rw [Circuit.eval_pi]
  dsimp only []
  have h1 : (⟨wIdx.val / B₁,
      Nat.div_lt_of_lt_mul (by have hp : wIdx.val < Nn * B₁ := wIdx.isLt; nlinarith)⟩ : Fin Nn) =
      u₀ :=
    Fin.ext hdiv
  have h2 : (⟨wIdx.val % B₁, Nat.mod_lt _ hB₁_pos⟩ : Fin B₁) = ⟨off, hoff⟩ :=
    Fin.ext hmod
  dsimp only [Nn, B₁] at h1 h2
  rw [h1, h2]

section Layer1Wires

variable (k : ℕ) {k_tapes : ℕ} {State : Type} [Fintype State]
  (M : OracleMultiTapeTM k_tapes State) (Bn n : ℕ)
  (I : Interpretation oracleSignature Bool) (xIn : Fin n → Bool)
  (u₀ : Fin (vertexBound (k := k_tapes) Bn))

private theorem eval_buntrockLayer1_hasLenWire (L : Fin (vertexBound (k := k_tapes) Bn + 1)) :
    (buntrockLayer1 k M Bn n).eval I xIn (hasLenWire _ u₀ L) =
      (buntrockLayer1Circuit k M Bn n u₀ (.queryLen L)).eval I xIn 0 := by
  rw [eval_buntrockLayer1 k M Bn n I xIn u₀ (hasLenWire _ u₀ L) L.val
    (by have hL := L.isLt; dsimp [buntrockB1]; omega) rfl]
  congr 2; dsimp only [decodeBuntrockB1]; rw [dite_eq_left L.isLt]

private theorem eval_buntrockLayer1_qBitWire (r : Fin (vertexBound (k := k_tapes) Bn)) :
    (buntrockLayer1 k M Bn n).eval I xIn (qBitWire _ u₀ r) =
      (buntrockLayer1Circuit k M Bn n u₀ (.queryBit r)).eval I xIn 0 := by
  have hr := r.isLt
  rw [eval_buntrockLayer1 k M Bn n I xIn u₀ (qBitWire _ u₀ r)
    ((vertexBound (k := k_tapes) Bn + 1) + r.val) (by dsimp [buntrockB1]; omega) rfl]
  congr 2; dsimp only [decodeBuntrockB1]
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg WPTarget.queryBit (Fin.ext (by simp))

private theorem eval_buntrockLayer1_yesWire (v : Fin (vertexBound (k := k_tapes) Bn)) :
    (buntrockLayer1 k M Bn n).eval I xIn (yesWire _ u₀ v) =
      (buntrockLayer1Circuit k M Bn n u₀ (.yesTarget v)).eval I xIn 0 := by
  have hv := v.isLt
  rw [eval_buntrockLayer1 k M Bn n I xIn u₀ (yesWire _ u₀ v)
    ((vertexBound (k := k_tapes) Bn + 1) + vertexBound (k := k_tapes) Bn + v.val)
    (by dsimp [buntrockB1]; omega) rfl]
  congr 2; dsimp only [decodeBuntrockB1]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg WPTarget.yesTarget (Fin.ext (by simp))

private theorem eval_buntrockLayer1_noWire (v : Fin (vertexBound (k := k_tapes) Bn)) :
    (buntrockLayer1 k M Bn n).eval I xIn (noWire _ u₀ v) =
      (buntrockLayer1Circuit k M Bn n u₀ (.noTarget v)).eval I xIn 0 := by
  have hv := v.isLt
  rw [eval_buntrockLayer1 k M Bn n I xIn u₀ (noWire _ u₀ v)
    ((vertexBound (k := k_tapes) Bn + 1) + vertexBound (k := k_tapes) Bn +
      vertexBound (k := k_tapes) Bn + v.val) (by dsimp [buntrockB1]; omega) rfl]
  congr 2; dsimp only [decodeBuntrockB1]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]
  exact congrArg WPTarget.noTarget (Fin.ext (by simp))

private theorem eval_buntrockLayer1_accWire :
    (buntrockLayer1 k M Bn n).eval I xIn (accWire _ u₀) =
      (buntrockLayer1Circuit k M Bn n u₀ .accHalt).eval I xIn 0 := by
  rw [eval_buntrockLayer1 k M Bn n I xIn u₀ (accWire _ u₀)
    ((vertexBound (k := k_tapes) Bn + 1) + vertexBound (k := k_tapes) Bn +
      vertexBound (k := k_tapes) Bn + vertexBound (k := k_tapes) Bn)
    (by dsimp [buntrockB1]; omega) rfl]
  congr 2; dsimp only [decodeBuntrockB1]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega)]

end Layer1Wires

private theorem size_buntrockOracleAnsLayer_le (CO : ∀ q, Circuit oracleSignature q 1)
    (Nn B_O : ℕ) (hB : ∀ q ≤ Nn, (CO q).size ≤ B_O) :
    (buntrockOracleAnsLayer CO Nn).size ≤ (Nn * (Nn + 1)) * B_O := by
  unfold buntrockOracleAnsLayer
  rw [Circuit.size_pi]
  calc ∑ p : Fin (Nn * (Nn + 1)), _
      ≤ ∑ _p : Fin (Nn * (Nn + 1)), B_O :=
        Finset.sum_le_sum fun p _ ↦ by
          dsimp only []
          rw [Circuit.size_comp, Circuit.size_wiring, zero_add]
          exact hB _ (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos Nn)))
    _ = (Nn * (Nn + 1)) * B_O := by simp

private theorem fanInAtMost_buntrockOracleAnsLayer (CO : ∀ q, Circuit oracleSignature q 1)
    (Nn r : ℕ) (hr : ∀ q ≤ Nn, (CO q).FanInAtMost r) :
    (buntrockOracleAnsLayer CO Nn).FanInAtMost r := by
  unfold buntrockOracleAnsLayer
  exact Circuit.fanInAtMost_pi fun p ↦
    (hr _ (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos Nn)))).comp
      (Circuit.fanInAtMost_wiring _ _)

private theorem depthWith_buntrockOracleAnsLayer_le (CO : ∀ q, Circuit oracleSignature q 1)
    (Nn D_O : ℕ) (hD : ∀ q ≤ Nn, (CO q).depthWith nc1OracleDepthWeight ≤ D_O) :
    (buntrockOracleAnsLayer CO Nn).depthWith nc1OracleDepthWeight ≤ D_O := by
  unfold buntrockOracleAnsLayer
  exact Circuit.depthWith_pi_le (σ := oracleSignature) nc1OracleDepthWeight _ fun p ↦ by
    dsimp only []
    refine (Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight _ _).trans ?_
    simp only [Circuit.depthWith_wiring, add_zero]
    exact hD _ (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos Nn)))

private theorem eval_buntrockOracleAnsLayer (CO : ∀ q, Circuit oracleSignature q 1) (Nn : ℕ)
    (I : Interpretation oracleSignature Bool) (y1 : Fin (Nn * buntrockB1 Nn) → Bool)
    (u₀ : Fin Nn) (L : Fin (Nn + 1)) :
    (buntrockOracleAnsLayer CO Nn).eval I y1 (qAnsWire Nn u₀ L) =
      (CO L.val).eval I (fun j : Fin L.val ↦
        y1 (qBitWire Nn u₀ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp L.isLt)⟩)) 0 := by
  unfold buntrockOracleAnsLayer
  dsimp only []
  rw [Circuit.eval_pi]
  dsimp only [qAnsWire]
  have hdL : (u₀.val * (Nn + 1) + L.val) / (Nn + 1) = u₀.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.succ_pos Nn), Nat.div_eq_of_lt L.isLt, add_zero]
  have hmL : (u₀.val * (Nn + 1) + L.val) % (Nn + 1) = L.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt L.isLt]
  have hu' : (⟨(u₀.val * (Nn + 1) + L.val) / (Nn + 1),
      Nat.div_lt_of_lt_mul (by have hu := u₀.isLt; have hL := L.isLt; nlinarith)⟩ : Fin Nn) =
    u₀ := Fin.ext hdL
  rw [hu']
  have hcast : ∀ (q : ℕ) (hq : q < Nn + 1), q = L.val →
      ((CO q).comp (Circuit.wiring oracleSignature fun j : Fin q ↦
        qBitWire Nn u₀ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp hq)⟩)).eval I y1 0 =
      (CO L.val).eval I (fun j : Fin L.val ↦
        y1 (qBitWire Nn u₀ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp L.isLt)⟩)) 0 := by
    rintro _ hq rfl
    rw [Circuit.eval_comp, Circuit.eval_wiring]; rfl
  exact hcast _ (Nat.mod_lt _ (Nat.succ_pos Nn)) hmL

private theorem size_buntrockOrAnsDM_le (Nn : ℕ) (u₀ : Fin Nn) :
    (buntrockOrAnsDM Nn u₀).size ≤ 3 * (Nn + 2) := by
  unfold buntrockOrAnsDM
  have hor := Circuit.size_balanced_le
    (Circuit.oneGate (σ := signature) .or ![0, 1])
    (Circuit.oneGate (σ := signature) (.const false) Fin.elim0)
    (List.ofFn fun L : Fin (Nn + 1) ↦
      (Circuit.oneGate (σ := signature) .and ![0, 1]).comp
        (Circuit.wiring signature ![Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L),
          Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L)]))
  have h1 : (Circuit.size ∘ fun L : Fin (Nn + 1) ↦
      ((Circuit.oneGate (σ := signature) .and ![0, 1]).comp
        (Circuit.wiring signature ![Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L),
          Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L)]))) = fun _ ↦ 1 :=
    funext fun _ ↦ by simp [Circuit.size_comp]
  have hrep : ∀ m, (List.replicate m (1 : ℕ)).sum = m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [List.replicate_succ, List.sum_cons, ih]; omega
  have hsum_and :
      ((List.ofFn fun L : Fin (Nn + 1) ↦
        ((Circuit.oneGate (σ := signature) .and ![0, 1]).comp
          (Circuit.wiring signature ![Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L),
            Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L)]))).map
        Circuit.size).sum = Nn + 1 := by
    rw [List.map_ofFn, h1, List.ofFn_const, hrep (Nn + 1)]
  rw [hsum_and] at hor
  simp only [List.length_ofFn, Circuit.size_oneGate] at hor
  omega

private theorem depth_buntrockOrAnsDM_le (Nn : ℕ) (u₀ : Fin Nn) :
    (buntrockOrAnsDM Nn u₀).depthWith 1 ≤ 1 + Nat.clog 2 (Nn + 1) := by
  unfold buntrockOrAnsDM
  rw [Circuit.depthWith_one]
  have hb := Circuit.depth_balanced_le_max
    (Circuit.oneGate (σ := signature) .or ![0, 1])
    (Circuit.oneGate (σ := signature) (.const false) Fin.elim0) (D := 1)
    (l := List.ofFn fun L : Fin (Nn + 1) ↦
      (Circuit.oneGate (σ := signature) .and ![0, 1]).comp
        (Circuit.wiring signature ![Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L),
          Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L)]))
    (fun C hC ↦ by
      obtain ⟨L, rfl⟩ := List.mem_ofFn.mp hC
      rw [← Circuit.depthWith_one]
      exact (Circuit.depthWith_comp_le (σ := signature) 1 _ _).trans (by simp))
  simpa using hb

private theorem size_buntrockLayer2bDM_le (Nn : ℕ) :
    (buntrockLayer2bDM Nn).size ≤ (Nn * (Nn + 1)) * (45 + 3 * (Nn + 2)) := by
  unfold buntrockLayer2bDM
  rw [Circuit.size_pi]
  calc ∑ p : Fin (Nn * (Nn + 1)), _
      ≤ ∑ _p : Fin (Nn * (Nn + 1)), (45 + 3 * (Nn + 2)) :=
        Finset.sum_le_sum fun p _ ↦ by
          dsimp only []
          split_ifs with hv
          · simp only [Circuit.size_comp, Circuit.size_append, Circuit.size_wiring]
            have hmux : (truthTableCircuit1 3 buntrockStepMuxFn).size ≤ 40 :=
              size_truthTableCircuit1_le 3 buntrockStepMuxFn
            have hor := size_buntrockOrAnsDM_le Nn
              ⟨p.val / (Nn + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
            omega
          · simp
    _ = (Nn * (Nn + 1)) * (45 + 3 * (Nn + 2)) := by simp

private theorem depth_buntrockLayer2bDM_le (Nn : ℕ) :
    (buntrockLayer2bDM Nn).depth ≤ 15 + Nat.clog 2 (Nn + 1) := by
  unfold buntrockLayer2bDM
  refine Circuit.depth_pi_le _ fun p ↦ ?_
  dsimp only []
  split_ifs with hv
  · rw [← Circuit.depthWith_one]
    refine (Circuit.depthWith_comp_le (σ := signature) 1 _ _).trans ?_
    have hmux : (truthTableCircuit1 3 buntrockStepMuxFn).depthWith 1 ≤ 10 := by
      rw [Circuit.depthWith_one]; exact depth_truthTableCircuit1_le 3 buntrockStepMuxFn
    let u₀ : Fin Nn := ⟨p.val / (Nn + 1), Nat.div_lt_of_lt_mul (by have hp := p.isLt; nlinarith)⟩
    let v : Fin Nn := ⟨p.val % (Nn + 1), hv⟩
    have happ : (((Circuit.wiring signature fun _ : Fin 1 ↦
          Fin.castAdd (Nn * (Nn + 1)) (yesWire Nn u₀ v)).append
        ((Circuit.wiring signature fun _ : Fin 1 ↦
            Fin.castAdd (Nn * (Nn + 1)) (noWire Nn u₀ v)).append
          (buntrockOrAnsDM Nn u₀))).depthWith 1) ≤ 1 + Nat.clog 2 (Nn + 1) := by
      refine (Circuit.depthWith_append_le (σ := signature) 1 _ _).trans (max_le (by simp) ?_)
      refine (Circuit.depthWith_append_le (σ := signature) 1 _ _).trans (max_le (by simp) ?_)
      exact depth_buntrockOrAnsDM_le Nn u₀
    dsimp only [u₀, v] at happ
    omega
  · simp

private theorem eval_buntrockLayer2bDM (k Nn : ℕ)
    (zMid : Fin (Nn * buntrockB1 Nn + Nn * (Nn + 1)) → Bool)
    (u₀ : Fin Nn) (col : Fin (Nn + 1)) :
    ((buntrockLayer2bDM Nn).mapOp toOracle).eval (oracleInterpretation (detZModLanguage k)) zMid
      ⟨u₀.val * (Nn + 1) + col.val, by have hu := u₀.isLt; have hc := col.isLt; nlinarith⟩ =
      let orAns :=
        (List.ofFn fun L : Fin (Nn + 1) ↦
          zMid (Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L)) &&
            zMid (Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L))).any id
      if hv : col.val < Nn then
        (zMid (Fin.castAdd (Nn * (Nn + 1)) (yesWire Nn u₀ ⟨col.val, hv⟩)) && orAns) ||
          (zMid (Fin.castAdd (Nn * (Nn + 1)) (noWire Nn u₀ ⟨col.val, hv⟩)) && !orAns)
      else
        zMid (Fin.castAdd (Nn * (Nn + 1)) (accWire Nn u₀)) := by
  have hdiv : (u₀.val * (Nn + 1) + col.val) / (Nn + 1) = u₀.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.succ_pos Nn), Nat.div_eq_of_lt col.isLt, add_zero]
  have hmod : (u₀.val * (Nn + 1) + col.val) % (Nn + 1) = col.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt col.isLt]
  unfold buntrockLayer2bDM
  rw [Circuit.eval_mapOp (I := interpretation), Circuit.eval_pi]
  dsimp only []
  have hu_eq : (⟨(u₀.val * (Nn + 1) + col.val) / (Nn + 1),
      Nat.div_lt_of_lt_mul (by have hu := u₀.isLt; have hc := col.isLt; nlinarith)⟩ : Fin Nn) =
    u₀ := Fin.ext hdiv
  rw [hu_eq]
  suffices hcol_cast : ∀ (cVal : ℕ), cVal = col.val →
      ((if hv : cVal < Nn then
          (truthTableCircuit1 3 buntrockStepMuxFn).comp
            ((Circuit.wiring signature fun _ : Fin 1 ↦
                Fin.castAdd (Nn * (Nn + 1)) (yesWire Nn u₀ ⟨cVal, hv⟩)).append
              ((Circuit.wiring signature fun _ : Fin 1 ↦
                  Fin.castAdd (Nn * (Nn + 1)) (noWire Nn u₀ ⟨cVal, hv⟩)).append
                (buntrockOrAnsDM Nn u₀)))
        else
          Circuit.wiring signature fun _ : Fin 1 ↦
            Fin.castAdd (Nn * (Nn + 1)) (accWire Nn u₀)).eval interpretation zMid) 0 = _ from
    hcol_cast _ hmod
  rintro _ rfl
  have hor_eval :
      (buntrockOrAnsDM Nn u₀).eval interpretation zMid 0 =
        (List.ofFn fun L : Fin (Nn + 1) ↦
          zMid (Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L)) &&
            zMid (Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L))).any id := by
    unfold buntrockOrAnsDM
    have hfold :
        ∀ l : List (Circuit signature (Nn * buntrockB1 Nn + Nn * (Nn + 1)) 1),
          ((Circuit.balanced (Circuit.oneGate (σ := signature) .or ![0, 1])
            (Circuit.oneGate (σ := signature) (.const false) Fin.elim0) l).eval
            interpretation zMid) 0 =
          l.any (fun C ↦ C.eval interpretation zMid 0) := by
      intro l
      rw [Circuit.eval_balanced]
      refine List.balancedFold_induction
        (p := fun l (res : Fin 1 → Bool) ↦ res 0 = l.any (fun C ↦ C.eval interpretation zMid 0))
        (?_) (fun _ ↦ ?_) (fun l₁ l₂ r₁ r₂ _ _ ih₁ ih₂ ↦ ?_) l
      · rfl
      · simp
      · change (r₁ 0 || r₂ 0) = _; rw [ih₁, ih₂, List.any_append]
    rw [hfold, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    simp only [List.mem_ofFn, id_eq, exists_exists_eq_and]
    refine exists_congr fun L ↦ ?_
    simp only [Circuit.eval_comp, Circuit.eval_oneGate, Circuit.eval_wiring, interpretation]
    rfl
  by_cases hv : col.val < Nn
  · simp only [hv, ↓reduceDIte]
    rw [Circuit.eval_comp, eval_truthTableCircuit1]
    set muxIn := ((Circuit.wiring signature fun _ : Fin 1 ↦
          Fin.castAdd (Nn * (Nn + 1)) (yesWire Nn u₀ ⟨col.val, hv⟩)).append
        ((Circuit.wiring signature fun _ : Fin 1 ↦
            Fin.castAdd (Nn * (Nn + 1)) (noWire Nn u₀ ⟨col.val, hv⟩)).append
          (buntrockOrAnsDM Nn u₀)))
    have hb0 : muxIn.eval interpretation zMid 0 =
        zMid (Fin.castAdd (Nn * (Nn + 1)) (yesWire Nn u₀ ⟨col.val, hv⟩)) := by
      change muxIn.eval interpretation zMid (Fin.castAdd 2 (0 : Fin 1)) = _
      rw [Circuit.eval_append, Fin.append_left, Circuit.eval_wiring]; rfl
    have hb1 : muxIn.eval interpretation zMid 1 =
        zMid (Fin.castAdd (Nn * (Nn + 1)) (noWire Nn u₀ ⟨col.val, hv⟩)) := by
      change muxIn.eval interpretation zMid (Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1))) = _
      rw [Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_left,
        Circuit.eval_wiring]; rfl
    have hb2 : muxIn.eval interpretation zMid 2 =
        (buntrockOrAnsDM Nn u₀).eval interpretation zMid 0 := by
      change muxIn.eval interpretation zMid (Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1))) = _
      rw [Circuit.eval_append, Fin.append_right, Circuit.eval_append, Fin.append_right]
    dsimp only [buntrockStepMuxFn]
    rw [hb0, hb1, hb2, hor_eval]
  · simp [hv]

private def buntrockLayer2 (CO : ∀ q, Circuit oracleSignature q 1) (Nn : ℕ) :
    Circuit oracleSignature (Nn * buntrockB1 Nn) (Nn * (Nn + 1)) :=
  ((buntrockLayer2bDM Nn).mapOp toOracle).comp (buntrockLayer2a CO Nn)

private theorem size_buntrockLayer2_le (CO : ∀ q, Circuit oracleSignature q 1)
    (Nn B_O : ℕ) (hB : ∀ q ≤ Nn, (CO q).size ≤ B_O) :
    (buntrockLayer2 CO Nn).size ≤
      (Nn * (Nn + 1)) * B_O + (Nn * (Nn + 1)) * (45 + 3 * (Nn + 2)) := by
  unfold buntrockLayer2 buntrockLayer2a
  simp only [Circuit.size_comp, Circuit.size_mapOp, Circuit.size_append, Circuit.id,
    Circuit.size_wiring]
  have hs2a := size_buntrockOracleAnsLayer_le CO Nn B_O hB
  have hs2b := size_buntrockLayer2bDM_le Nn
  omega

private theorem fanInAtMost_buntrockLayer2 (CO : ∀ q, Circuit oracleSignature q 1)
    (Nn r : ℕ) (h2 : 2 ≤ r) (hr : ∀ q ≤ Nn, (CO q).FanInAtMost r) :
    (buntrockLayer2 CO Nn).FanInAtMost r := by
  unfold buntrockLayer2 buntrockLayer2a
  exact (circuit_fanInAtMost_mapOp_toOracle (buntrockLayer2bDM Nn) h2).comp
    ((Circuit.fanInAtMost_wiring _ _).append (fanInAtMost_buntrockOracleAnsLayer CO Nn r hr))

private theorem depthWith_buntrockLayer2_le (CO : ∀ q, Circuit oracleSignature q 1)
    (Nn D_O : ℕ) (hD : ∀ q ≤ Nn, (CO q).depthWith nc1OracleDepthWeight ≤ D_O) :
    (buntrockLayer2 CO Nn).depthWith nc1OracleDepthWeight ≤
      15 + Nat.clog 2 (Nn + 1) + D_O := by
  unfold buntrockLayer2 buntrockLayer2a
  have hc2 := Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight
    ((buntrockLayer2bDM Nn).mapOp toOracle)
    ((Circuit.id oracleSignature (Nn * buntrockB1 Nn)).append (buntrockOracleAnsLayer CO Nn))
  have hdepth : ((buntrockLayer2bDM Nn).mapOp toOracle).depthWith nc1OracleDepthWeight =
      (buntrockLayer2bDM Nn).depth := by
    rw [Circuit.depthWith_mapOp]; exact (buntrockLayer2bDM Nn).depthWith_one
  rw [hdepth] at hc2
  have hd2b := depth_buntrockLayer2bDM_le Nn
  have hd2a := depthWith_buntrockOracleAnsLayer_le CO Nn D_O hD
  have happ := (Circuit.depthWith_append_le (σ := oracleSignature) nc1OracleDepthWeight
    (Circuit.id oracleSignature (Nn * buntrockB1 Nn))
    (buntrockOracleAnsLayer CO Nn)).trans (max_le (by simp) hd2a)
  omega

private theorem eval_buntrockLayer2 (k Nn : ℕ) {O : Language Bool}
    (CO : ∀ q, Circuit oracleSignature q 1)
    (hCO : ∀ q, (CO q).Computes (oracleInterpretation (detZModLanguage k)) (single (O.slice q)))
    (y1 : Fin (Nn * buntrockB1 Nn) → Bool)
    (u₀ : Fin Nn) (j : Fin (Nn + 1)) :
    (buntrockLayer2 CO Nn).eval (oracleInterpretation (detZModLanguage k)) y1
      ⟨u₀.val * (Nn + 1) + j.val, by have hu := u₀.isLt; have hj := j.isLt; nlinarith⟩ =
      let roundOracleAns :=
        (List.ofFn fun L : Fin (Nn + 1) ↦
          y1 (hasLenWire Nn u₀ L) &&
            O.slice L.val (fun r : Fin L.val ↦
              y1 (qBitWire Nn u₀
                ⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.lt_succ_iff.mp L.isLt)⟩))).any id
      if hj : j.val < Nn then
        (y1 (yesWire Nn u₀ ⟨j.val, hj⟩) && roundOracleAns) ||
          (y1 (noWire Nn u₀ ⟨j.val, hj⟩) && !roundOracleAns)
      else
        y1 (accWire Nn u₀) := by
  unfold buntrockLayer2
  rw [Circuit.eval_comp, eval_buntrockLayer2bDM]
  have hor_eq :
      (List.ofFn fun L : Fin (Nn + 1) ↦
        ((buntrockLayer2a CO Nn).eval (oracleInterpretation (detZModLanguage k)) y1)
          (Fin.castAdd (Nn * (Nn + 1)) (hasLenWire Nn u₀ L)) &&
        ((buntrockLayer2a CO Nn).eval (oracleInterpretation (detZModLanguage k)) y1)
          (Fin.natAdd (Nn * buntrockB1 Nn) (qAnsWire Nn u₀ L))).any id =
      (List.ofFn fun L : Fin (Nn + 1) ↦
        y1 (hasLenWire Nn u₀ L) &&
          O.slice L.val (fun r : Fin L.val ↦
            y1 (qBitWire Nn u₀
              ⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.lt_succ_iff.mp L.isLt)⟩))).any id := by
    refine congrArg (List.any · id) (congrArg List.ofFn (funext fun L ↦ ?_))
    unfold buntrockLayer2a
    rw [Circuit.eval_append, Fin.append_left, Circuit.id, Circuit.eval_wiring, Function.comp_id,
      Fin.append_right, eval_buntrockOracleAnsLayer, hCO L.val]
    rfl
  dsimp only []
  rw [hor_eq]
  unfold buntrockLayer2a
  by_cases hj : j.val < Nn
  · simp only [hj, ↓reduceDIte, Circuit.eval_append, Fin.append_left, Circuit.id,
      Circuit.eval_wiring, Function.comp_id]
  · simp only [hj, ↓reduceDIte, Circuit.eval_append, Fin.append_left, Circuit.id,
      Circuit.eval_wiring, Function.comp_id]

private theorem size_buntrockLayer3_le (k Nn : ℕ) (startIdx : Fin Nn) :
    (buntrockLayer3 k Nn startIdx).size ≤ Nn * (Nn + 1) + 4 := by
  unfold buntrockLayer3
  exact size_singleLiteralDetCircuit_le _ _ _

private theorem fanInAtMost_buntrockLayer3 (k Nn : ℕ) (startIdx : Fin Nn) (r : ℕ)
    (h2 : 2 ≤ r) (henc : DetZModInstance.encodedLen k ((Nn + 1 + 1) * (Nn + 1) + 1) ≤ r) :
    (buntrockLayer3 k Nn startIdx).FanInAtMost r := by
  unfold buntrockLayer3
  exact (fanInAtMost_singleLiteralDetCircuit _ _ _).mono (max_le h2 henc)

private theorem depthWith_buntrockLayer3_le (k Nn : ℕ) (startIdx : Fin Nn) :
    (buntrockLayer3 k Nn startIdx).depthWith nc1OracleDepthWeight ≤
      4 + Nat.log 2 (DetZModInstance.encodedLen k ((Nn + 1 + 1) * (Nn + 1) + 1)) := by
  unfold buntrockLayer3
  simpa only [Nat.succ_eq_add_one] using
    (depthWith_singleLiteralDetCircuit_le _ _ _).trans (by omega)

private theorem eval_buntrockLayer3 {k : ℕ} (hk : 2 ≤ k) (Nn : ℕ) (startIdx : Fin Nn)
    (y2 : Fin (Nn * (Nn + 1)) → Bool)
    (roundNext : Fin (Nn + 1) → Option (Fin (Nn + 1)))
    (hround_last : roundNext (Fin.last Nn) = some (Fin.last Nn))
    (hy2 : ∀ (u₀ : Fin Nn) (j : Fin (Nn + 1)),
      y2 ⟨u₀.val * (Nn + 1) + j.val, by have hu := u₀.isLt; have hj := j.isLt; nlinarith⟩ =
        decide (roundNext (Fin.castSucc u₀) = some j)) :
    (buntrockLayer3 k Nn startIdx).eval (oracleInterpretation (detZModLanguage k)) y2 0 =
      decide (iterOpt (Fin.castSucc startIdx) (fun _ ↦ roundNext) (Nn + 1) le_rfl =
        some (Fin.last Nn)) := by
  have hk_ne : NeZero k := ⟨by omega⟩
  have h1_ne : (1 : ZMod k) ≠ 0 := zmod_one_ne_zero hk
  unfold buntrockLayer3
  rw [eval_singleLiteralDetCircuit, Bool.true_xor, det_layeredDAGSpec_eval]
  have hround_mat : ∀ (s : Fin (Nn + 1)) (i j : Fin (Nn + 1)),
      (buntrockRoundStepSpec k Nn).eval y2 i j =
        if roundNext i = some j then 1 else 0 := by
    intro _ i j
    rw [SingleVarMatrixSpec.eval_apply]
    dsimp only [buntrockRoundStepSpec]
    by_cases hi : i.val < Nn
    · simp only [hi, ↓reduceDIte, ↓reduceIte]
      rw [hy2 ⟨i.val, hi⟩ j]
      have hcast : Fin.castSucc (⟨i.val, hi⟩ : Fin Nn) = i := Fin.ext rfl
      rw [hcast]
      cases roundNext i == some j <;> simp
    · have hi_last : i = Fin.last Nn := Fin.ext (by have := i.isLt; simp; omega)
      subst hi_last
      simp only [Fin.val_last, lt_irrefl Nn, ↓reduceDIte, ↓reduceIte, hround_last]
      by_cases hj : j = Fin.last Nn
      · subst hj; simp
      · have hj_val : j.val ≠ Nn := fun h ↦ hj (Fin.ext (by simpa using h))
        simp [hj_val, Ne.symm hj]
  rw [walkVec_option_deterministic (Fin.castSucc startIdx) (fun _ ↦ roundNext) _ hround_mat
    (Nn + 1) le_rfl]
  cases hres : iterOpt (Fin.castSucc startIdx) (fun _ ↦ roundNext) (Nn + 1) le_rfl with
  | none => simp
  | some idx =>
    rw [Finset.sum_eq_single idx]
    · by_cases heq : idx = Fin.last Nn
      · subst heq; simp [h1_ne]
      · simp [heq]
    · intro j _ hne; simp [Pi.single_eq_of_ne hne]
    · simp

attribute [local irreducible]
  buntrockLayer1 buntrockOracleAnsLayer buntrockLayer2bDM buntrockLayer2 buntrockLayer3

private theorem two_mul_sq_add_one_le (m : ℕ) :
    2 * (m + 1) ^ 2 + 1 ≤ 3 * (m + 2) ^ 2 := by
  have h : 3 * (m + 2) ^ 2 = 2 * (m + 1) ^ 2 + 1 + (m ^ 2 + 8 * m + 9) := by ring
  omega

private theorem buntrock_log_le_of_poly {X n aB dB : ℕ}
    (hX : X ≤ aB * (n + 1) ^ dB) :
    Nat.log 2 X ≤ (aB + 1 + 2 * dB) * (Nat.log 2 n + 1) := by
  by_cases h0 : X = 0
  · simp [h0]
  · have hn2 : n + 1 ≤ 2 ^ (Nat.log 2 n + 2) := by
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two n
      have h1 : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_pow _ 2 Nat.two_pos
      rw [pow_succ] at hlt; rw [pow_succ, pow_succ]; omega
    have ha2 : aB < 2 ^ (aB + 1) :=
      Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right Nat.two_pos (Nat.le_succ aB))
    have hpow : X < 2 ^ ((aB + 1 + 2 * dB) * (Nat.log 2 n + 1) + 1) :=
      calc X ≤ aB * (n + 1) ^ dB := hX
        _ ≤ aB * (2 ^ (Nat.log 2 n + 2)) ^ dB :=
            Nat.mul_le_mul_left aB (Nat.pow_le_pow_left hn2 dB)
        _ < 2 ^ (aB + 1) * (2 ^ (Nat.log 2 n + 2)) ^ dB :=
            Nat.mul_lt_mul_of_pos_right ha2 (Nat.pow_pos (Nat.two_pow_pos (Nat.log 2 n + 2)))
        _ = 2 ^ ((aB + 1) + dB * (Nat.log 2 n + 2)) := by
            rw [← pow_mul, mul_comm (Nat.log 2 n + 2) dB, ← pow_add]
        _ ≤ 2 ^ ((aB + 1 + 2 * dB) * (Nat.log 2 n + 1) + 1) := by
            refine Nat.pow_le_pow_right Nat.two_pos ?_
            have h : (aB + 1 + 2 * dB) * (Nat.log 2 n + 1) + 1 =
                (aB + 1) + dB * (Nat.log 2 n + 2) +
                  (aB * Nat.log 2 n + Nat.log 2 n + dB * Nat.log 2 n + 1) := by ring
            omega
    exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow Nat.one_lt_two h0).mpr hpow)

private theorem buntrock_log_pow_succ_le (n pCard : ℕ) :
    Nat.log 2 ((n + 2) ^ pCard + 1) ≤ 2 * (pCard + 1) * (Nat.log 2 n + 1) := by
  have hn2 : n + 2 ≤ 2 ^ (Nat.log 2 n + 2) := by
    have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have h1 : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_pow _ 2 Nat.two_pos
    rw [pow_succ] at hlt; rw [pow_succ, pow_succ]; omega
  have hexp : pCard * (Nat.log 2 n + 2) < 2 * (pCard + 1) * (Nat.log 2 n + 1) := by
    have h : 2 * (pCard + 1) * (Nat.log 2 n + 1) =
        pCard * (Nat.log 2 n + 2) + (pCard * Nat.log 2 n + 2 * Nat.log 2 n + 2) := by ring
    omega
  have hpow : (n + 2) ^ pCard + 1 < 2 ^ (2 * (pCard + 1) * (Nat.log 2 n + 1) + 1) := by
    calc (n + 2) ^ pCard + 1
        ≤ (2 ^ (Nat.log 2 n + 2)) ^ pCard + 1 :=
          Nat.add_le_add_right (Nat.pow_le_pow_left hn2 pCard) 1
      _ = 2 ^ (pCard * (Nat.log 2 n + 2)) + 1 := by rw [← pow_mul, mul_comm]
      _ < 2 ^ (2 * (pCard + 1) * (Nat.log 2 n + 1) + 1) := by
          rw [pow_succ']
          have h2 : 1 ≤ 2 ^ (pCard * (Nat.log 2 n + 2)) := Nat.one_le_pow _ 2 Nat.two_pos
          have h3 : 2 ^ (pCard * (Nat.log 2 n + 2)) <
              2 ^ (2 * (pCard + 1) * (Nat.log 2 n + 1)) :=
            Nat.pow_lt_pow_right Nat.one_lt_two hexp
          omega
  exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow Nat.one_lt_two (by omega)).mpr hpow)

private theorem buntrock_clog_pow_succ_le (n pCard : ℕ) :
    Nat.clog 2 ((n + 2) ^ pCard + 1) ≤ 2 * (pCard + 1) * (Nat.log 2 n + 1) + 1 :=
  ((Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
    (Nat.lt_pow_succ_log_self Nat.one_lt_two _).le).trans
    (Nat.add_le_add_right (buntrock_log_pow_succ_le n pCard) 1)

/-- Three-layer Buntrock--Damm--Hertrampf--Meinel circuit on `n` input bits simulating `M` with
space constant `c` and oracle circuit family `CO`. -/
noncomputable def buildBuntrockCircuit (k : ℕ) (CO : ∀ q, Circuit oracleSignature q 1)
    {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (c n : ℕ) :
    Circuit oracleSignature n 1 :=
  let Bn : ℕ := radix (radixExponent State c) n
  let Nn : ℕ := vertexBound (k := k_tapes) Bn
  (buntrockLayer3 k Nn ⟨startID M.envelopeNTM Bn, buntrockStartLt M c n⟩).comp
    ((buntrockLayer2 CO Nn).comp (buntrockLayer1 k M Bn n))

/-- Language over `Bool` accepted by the uniform slice family `buildBuntrockCircuit k CO M c`. -/
@[expose]
def buntrockCircuitLanguage (k : ℕ) (CO : ∀ q, Circuit oracleSignature q 1)
    {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (c : ℕ) : Language Bool :=
  {w : List Bool |
    (buildBuntrockCircuit k CO M c w.length).eval (oracleInterpretation (detZModLanguage k))
      (fun i : Fin w.length ↦ w[i.val]) 0 = true}

/-- **Membership of `buntrockCircuitLanguage` in $\mathrm{DET}_k$**: when `(CO, cO, sO)` is a
polynomial-size, polynomial-fan-in, $O(\log n)$-depth $\mathrm{DET}_k$ circuit family, the
three-layer Buntrock simulation circuit family also has polynomial size, polynomial fan-in, and
Cook--Wilson logarithmic depth. -/
theorem buntrockCircuitLanguage_mem_DETk (k : ℕ)
    (CO : ∀ q, Circuit oracleSignature q 1) {cO : ℕ} {sO : ℕ → ℕ}
    (hsO : PolynomiallyBounded sO)
    (hCO_bounds : ∀ q, (CO q).size ≤ sO q ∧ (CO q).FanInAtMost (sO q) ∧
      (CO q).depthWith nc1OracleDepthWeight ≤ cO * (Nat.log 2 q + 1))
    {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (c : ℕ) :
    buntrockCircuitLanguage k CO M c ∈ DETk k := by
  obtain ⟨aO, dO, hsO_poly⟩ := polynomiallyBounded_iff_le.1 hsO
  let D : ℕ := radixExponent State c
  let pCard : ℕ := D * Fintype.card (Register k_tapes)
  let B (n : ℕ) : ℕ := radix D n
  let N (n : ℕ) : ℕ := vertexBound (k := k_tapes) (B n)
  have hN_eq (n : ℕ) : N n = (n + 2) ^ pCard := vertexBound_eq_pow D n
  have hN_pos (n : ℕ) : 0 < N n := by rw [hN_eq]; exact Nat.pow_pos (by omega)
  let B₁_ub (n : ℕ) : ℕ := 5 * ((n + 2) ^ pCard + 2)
  let Mwp_ub (n : ℕ) : ℕ := 3 * ((n + 2) ^ pCard + 2) ^ 2
  let dag1_ub (n : ℕ) : ℕ := ((n + 2) ^ pCard + 2) * Mwp_ub n + 1
  let dag3_ub (n : ℕ) : ℕ := ((n + 2) ^ pCard + 2) * ((n + 2) ^ pCard + 1) + 1
  let sizeBound (n : ℕ) : ℕ :=
    ((n + 2) ^ pCard * B₁_ub n) * (n + 4) +
    ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1)) *
      (aO * ((n + 2) ^ pCard + 2) ^ dO + 2) +
    ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1)) *
      (45 + 3 * ((n + 2) ^ pCard + 2)) +
    ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1) + 4) +
    DetZModInstance.encodedLen k (dag1_ub n) +
    DetZModInstance.encodedLen k (dag3_ub n) + 4
  have hpoly : PolynomiallyBounded sizeBound := by
    dsimp only [sizeBound, B₁_ub, Mwp_ub, dag1_ub, dag3_ub]
    simp only [DetZModInstance.encodedLen_eq]
    fun_prop
  obtain ⟨aB, dB, hsize_poly⟩ := polynomiallyBounded_iff_le.1 hpoly
  let depthConst : ℕ := 20 * (aB + dB + cO + 1) * (pCard + 2) + 80
  refine ⟨buildBuntrockCircuit k CO M c, depthConst, sizeBound, hpoly, fun n ↦ ?_⟩
  have hNn : vertexBound (k := k_tapes) (radix (radixExponent State c) n) = (n + 2) ^ pCard :=
    hN_eq n
  have h2_sb : 2 ≤ sizeBound n := by dsimp [sizeBound]; omega
  have hMwp_le :
      Fintype.card (WPNode (vertexBound (k := k_tapes) (radix (radixExponent State c) n))) ≤
        Mwp_ub n :=
    (card_wpNode_le _).trans (by dsimp only [Mwp_ub]; rw [← hNn]; exact two_mul_sq_add_one_le _)
  have hdag1_le :
      (vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1 + 1) *
        Fintype.card (WPNode (vertexBound (k := k_tapes) (radix (radixExponent State c) n))) + 1 ≤
        dag1_ub n := by
    dsimp only [dag1_ub]; rw [← hNn]
    exact Nat.add_le_add_right (Nat.mul_le_mul le_rfl hMwp_le) 1
  have henc1_le : DetZModInstance.encodedLen k
      ((vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1 + 1) *
        Fintype.card (WPNode (vertexBound (k := k_tapes) (radix (radixExponent State c) n))) + 1) ≤
      sizeBound n := by
    have hmono : DetZModInstance.encodedLen k
        ((vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1 + 1) *
          Fintype.card (WPNode (vertexBound (k := k_tapes) (radix (radixExponent State c) n))) +
            1) ≤
        DetZModInstance.encodedLen k (dag1_ub n) := by
      rw [DetZModInstance.encodedLen_eq, DetZModInstance.encodedLen_eq]
      have hsq := Nat.mul_le_mul hdag1_le hdag1_le
      have hmul := Nat.mul_le_mul_right (zmodBitWidth k) hsq
      omega
    exact hmono.trans (by dsimp [sizeBound]; omega)
  have henc3_le : DetZModInstance.encodedLen k
      ((vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1 + 1) *
        (vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1) + 1) ≤
      sizeBound n := by
    have heq3 :
        (vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1 + 1) *
          (vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1) + 1 =
        dag3_ub n := by dsimp [dag3_ub]; rw [hNn]
    rw [heq3]; dsimp [sizeBound]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Gate size bound
    dsimp only [buildBuntrockCircuit]
    simp only [Circuit.size_comp]
    have hB₁_le :
        buntrockB1 (vertexBound (k := k_tapes) (radix (radixExponent State c) n)) ≤ B₁_ub n := by
      dsimp [buntrockB1, B₁_ub]; rw [hNn]; omega
    have hs1 : (buntrockLayer1 k M (radix (radixExponent State c) n) n).size ≤
        ((n + 2) ^ pCard * B₁_ub n) * (n + 4) :=
      (size_buntrockLayer1_le k M _ n).trans
        (Nat.mul_le_mul_right _ (by rw [hNn] at hB₁_le ⊢; exact Nat.mul_le_mul_left _ hB₁_le))
    have hs2 : (buntrockLayer2 CO
        (vertexBound (k := k_tapes) (radix (radixExponent State c) n))).size ≤
        ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1)) *
          (aO * ((n + 2) ^ pCard + 2) ^ dO + 2) +
        ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1)) * (45 + 3 * ((n + 2) ^ pCard + 2)) := by
      refine (size_buntrockLayer2_le CO _
        (aO * ((n + 2) ^ pCard + 2) ^ dO + 2) fun q hq ↦ ?_).trans (by rw [hNn])
      have hq_le : q + 1 ≤ (n + 2) ^ pCard + 2 := by rw [← hNn]; omega
      exact (hCO_bounds q).1.trans ((hsO_poly q).trans
        ((Nat.mul_le_mul_left aO (Nat.pow_le_pow_left hq_le dO)).trans (Nat.le_add_right _ 2)))
    have hs3 : (buntrockLayer3 k (vertexBound (k := k_tapes) (radix (radixExponent State c) n))
        ⟨startID M.envelopeNTM (radix (radixExponent State c) n), buntrockStartLt M c n⟩).size ≤
        (n + 2) ^ pCard * ((n + 2) ^ pCard + 1) + 4 :=
      (size_buntrockLayer3_le _ _ _).trans (by rw [hNn])
    dsimp only [sizeBound]
    omega
  · -- Fan-in bound
    dsimp only [buildBuntrockCircuit]
    refine (fanInAtMost_buntrockLayer3 _ _ _ _ h2_sb henc3_le).comp ?_
    refine (fanInAtMost_buntrockLayer2 CO _ _ h2_sb fun q hq ↦ (hCO_bounds q).2.1.mono ?_).comp
      (fanInAtMost_buntrockLayer1 _ _ _ _ _ h2_sb henc1_le)
    have hq_le : q + 1 ≤ (n + 2) ^ pCard + 2 := by rw [← hNn]; omega
    have hs_le : sO q ≤ aO * ((n + 2) ^ pCard + 2) ^ dO :=
      (hsO_poly q).trans (Nat.mul_le_mul_left aO (Nat.pow_le_pow_left hq_le dO))
    have h1_prod : 1 ≤ (n + 2) ^ pCard * ((n + 2) ^ pCard + 1) := by
      rw [← hNn]; exact Nat.mul_pos (hN_pos n) (Nat.succ_pos _)
    have hterm : aO * ((n + 2) ^ pCard + 2) ^ dO ≤
        ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1)) *
          (aO * ((n + 2) ^ pCard + 2) ^ dO + 2) :=
      calc aO * ((n + 2) ^ pCard + 2) ^ dO
          ≤ 1 * (aO * ((n + 2) ^ pCard + 2) ^ dO + 2) := by omega
        _ ≤ ((n + 2) ^ pCard * ((n + 2) ^ pCard + 1)) *
              (aO * ((n + 2) ^ pCard + 2) ^ dO + 2) :=
            Nat.mul_le_mul_right _ h1_prod
    exact hs_le.trans (hterm.trans (by dsimp [sizeBound]; omega))
  · -- Cook--Wilson logarithmic depth bound
    have hlog_Nn : Nat.log 2
        (vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1) ≤
        2 * (pCard + 1) * (Nat.log 2 n + 1) := by
      rw [hNn]; exact buntrock_log_pow_succ_le n pCard
    have hclog_Nn : Nat.clog 2
        (vertexBound (k := k_tapes) (radix (radixExponent State c) n) + 1) ≤
        2 * (pCard + 1) * (Nat.log 2 n + 1) + 1 := by
      rw [hNn]; exact buntrock_clog_pow_succ_le n pCard
    have hd1 : (buntrockLayer1 k M (radix (radixExponent State c) n) n).depthWith
        nc1OracleDepthWeight ≤ 4 + (aB + 1 + 2 * dB) * (Nat.log 2 n + 1) :=
      (depthWith_buntrockLayer1_le k M _ n).trans
        (Nat.add_le_add_left (buntrock_log_le_of_poly (henc1_le.trans (hsize_poly n))) 4)
    have hd2 : (buntrockLayer2 CO
        (vertexBound (k := k_tapes) (radix (radixExponent State c) n))).depthWith
        nc1OracleDepthWeight ≤
        16 + 2 * (pCard + 1) * (Nat.log 2 n + 1) +
          cO * (2 * (pCard + 1) * (Nat.log 2 n + 1) + 1) := by
      refine (depthWith_buntrockLayer2_le CO _
        (cO * (2 * (pCard + 1) * (Nat.log 2 n + 1) + 1)) fun q hq ↦ ?_).trans ?_
      · have hlogL : Nat.log 2 q ≤ 2 * (pCard + 1) * (Nat.log 2 n + 1) :=
          (Nat.log_mono_right (Nat.le_succ_of_le hq)).trans hlog_Nn
        exact (hCO_bounds q).2.2.trans (Nat.mul_le_mul_left cO (Nat.add_le_add_right hlogL 1))
      · omega
    have hd3 : (buntrockLayer3 k (vertexBound (k := k_tapes) (radix (radixExponent State c) n))
        ⟨startID M.envelopeNTM (radix (radixExponent State c) n),
          buntrockStartLt M c n⟩).depthWith nc1OracleDepthWeight ≤
        4 + (aB + 1 + 2 * dB) * (Nat.log 2 n + 1) :=
      (depthWith_buntrockLayer3_le _ _ _).trans
        (Nat.add_le_add_left (buntrock_log_le_of_poly (henc3_le.trans (hsize_poly n))) 4)
    have harith_buntrock : ∀ (l : ℕ),
        (4 + (aB + 1 + 2 * dB) * (l + 1)) +
          ((16 + 2 * (pCard + 1) * (l + 1) + cO * (2 * (pCard + 1) * (l + 1) + 1)) +
            (4 + (aB + 1 + 2 * dB) * (l + 1))) ≤
          depthConst * (l + 1) := by
      intro l
      dsimp only [depthConst]
      calc (4 + (aB + 1 + 2 * dB) * (l + 1)) +
            ((16 + 2 * (pCard + 1) * (l + 1) + cO * (2 * (pCard + 1) * (l + 1) + 1)) +
              (4 + (aB + 1 + 2 * dB) * (l + 1)))
          = (2 * aB + 2 + 4 * dB + 2 * (pCard + 1) + 2 * cO * (pCard + 1)) * (l + 1) +
              (cO + 24) := by ring
        _ ≤ (2 * aB + 2 + 4 * dB + 2 * (pCard + 1) + 2 * cO * (pCard + 1)) * (l + 1) +
              (cO + 24) * (l + 1) :=
            Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.succ_pos l)) _
        _ = (2 * aB + 4 * dB + 2 * pCard + 2 * cO * (pCard + 1) + cO + 28) * (l + 1) := by ring
        _ ≤ (20 * (aB + dB + cO + 1) * (pCard + 2) + 80) * (l + 1) :=
            Nat.mul_le_mul_right (l + 1) (by
              have hcO3 : 2 * cO * (pCard + 1) + cO ≤ 3 * cO * (pCard + 2) := by
                calc 2 * cO * (pCard + 1) + cO
                    ≤ 2 * cO * (pCard + 2) + cO * (pCard + 2) :=
                      Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
                        (Nat.le_mul_of_pos_right _ (by omega))
                  _ = 3 * cO * (pCard + 2) := by ring
              have ha20 : 2 * aB ≤ 20 * aB * (pCard + 2) :=
                (Nat.mul_le_mul_right aB (by decide : 2 ≤ 20)).trans
                  (Nat.le_mul_of_pos_right _ (by omega))
              have hd20 : 4 * dB ≤ 20 * dB * (pCard + 2) :=
                (Nat.mul_le_mul_right dB (by decide : 4 ≤ 20)).trans
                  (Nat.le_mul_of_pos_right _ (by omega))
              have hp20 : 2 * pCard ≤ 20 * 1 * (pCard + 2) := by omega
              have hexpand : 20 * (aB + dB + cO + 1) * (pCard + 2) =
                  20 * aB * (pCard + 2) + 20 * dB * (pCard + 2) +
                    20 * cO * (pCard + 2) + 20 * 1 * (pCard + 2) := by ring
              have hcO20 : 3 * cO * (pCard + 2) ≤ 20 * cO * (pCard + 2) :=
                Nat.mul_le_mul_right (pCard + 2) (Nat.mul_le_mul_right cO (by decide))
              omega)
    dsimp only [buildBuntrockCircuit]
    have hc_top := Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight
      (buntrockLayer3 k (vertexBound (k := k_tapes) (radix (radixExponent State c) n))
        ⟨startID M.envelopeNTM (radix (radixExponent State c) n), buntrockStartLt M c n⟩)
      ((buntrockLayer2 CO (vertexBound (k := k_tapes) (radix (radixExponent State c) n))).comp
        (buntrockLayer1 k M (radix (radixExponent State c) n) n))
    have hc_mid := Circuit.depthWith_comp_le (σ := oracleSignature) nc1OracleDepthWeight
      (buntrockLayer2 CO (vertexBound (k := k_tapes) (radix (radixExponent State c) n)))
      (buntrockLayer1 k M (radix (radixExponent State c) n) n)
    have har := harith_buntrock (Nat.log 2 n)
    omega
  · -- Slice semantics of `buntrockCircuitLanguage`
    intro x
    funext j
    obtain rfl : j = 0 := Subsingleton.elim j 0
    dsimp only [single]
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
    change _ ↔ (buildBuntrockCircuit k CO M c (List.ofFn x).length).eval
      (oracleInterpretation (detZModLanguage k)) (fun i ↦ (List.ofFn x)[i.val]) 0 = true
    have hfn : ∀ (m : ℕ) (hm : m = n) (y : Fin m → Bool),
        (∀ i : Fin m, y i = x (Fin.cast hm i)) →
        (buildBuntrockCircuit k CO M c m).eval
            (oracleInterpretation (detZModLanguage k)) y 0 =
          (buildBuntrockCircuit k CO M c n).eval
            (oracleInterpretation (detZModLanguage k)) x 0 := by
      rintro m rfl y hy
      congr 2
      funext i
      exact hy i
    rw [hfn (List.ofFn x).length List.length_ofFn
      (fun i ↦ (List.ofFn x)[i.val]) (fun i ↦ by simp only [List.getElem_ofFn]; rfl)]

/-- Exact evaluation of `buildBuntrockCircuit` on an input word `w`: given Layer-1 output bits
`wpAccepted` and a deterministic round-transition map `roundNext` matching Layer-2's MUX and
accepting-halt wires, `buildBuntrockCircuit k CO M c w.length` outputs whether `(Nn + 1)` steps of
`roundNext` from `Fin.castSucc startU` reach `Fin.last Nn`. -/
theorem eval_buildBuntrockCircuit_eq {k : ℕ} (hk : 2 ≤ k) {O : Language Bool}
    (CO : ∀ q, Circuit oracleSignature q 1)
    (hCO : ∀ q, (CO q).Computes (oracleInterpretation (detZModLanguage k)) (single (O.slice q)))
    {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (c : ℕ) (w : List Bool)
    (wpAccepted : Fin (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length)) →
      WPTarget (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length)) → Bool)
    (hwp : ∀ u₀ tgt,
      (buntrockLayer1Circuit k M (radix (radixExponent State c) w.length) w.length u₀ tgt).eval
        (oracleInterpretation (detZModLanguage k)) (fun i : Fin w.length ↦ w[i.val]) 0 =
        wpAccepted u₀ tgt)
    (roundNext :
      Fin (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length) + 1) →
        Option (Fin (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length) + 1)))
    (hround_last : roundNext (Fin.last _) = some (Fin.last _))
    (hround_unique : ∀ u₀ j,
      (let Nn := vertexBound (k := k_tapes) (radix (radixExponent State c) w.length)
       let roundOracleAns :=
         (List.ofFn fun L : Fin (Nn + 1) ↦
           wpAccepted u₀ (.queryLen L) &&
             O.slice L.val (fun r : Fin L.val ↦
               wpAccepted u₀ (.queryBit
                 ⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.lt_succ_iff.mp L.isLt)⟩))).any id
       if hj : j.val < Nn then
         (wpAccepted u₀ (.yesTarget ⟨j.val, hj⟩) && roundOracleAns) ||
           (wpAccepted u₀ (.noTarget ⟨j.val, hj⟩) && !roundOracleAns)
       else wpAccepted u₀ .accHalt) =
      decide (roundNext (Fin.castSucc u₀) = some j))
    (startU : Fin (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length)))
    (hstartU : startU.val = startID M.envelopeNTM (radix (radixExponent State c) w.length)) :
    (buildBuntrockCircuit k CO M c w.length).eval (oracleInterpretation (detZModLanguage k))
        (fun i : Fin w.length ↦ w[i.val]) 0 =
      decide (iterOpt (Fin.castSucc startU) (fun _ ↦ roundNext)
        (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length) + 1) le_rfl =
        some (Fin.last _)) := by
  dsimp only [buildBuntrockCircuit]
  simp only [Circuit.eval_comp]
  have hstart_eq :
      (⟨startID M.envelopeNTM (radix (radixExponent State c) w.length),
        buntrockStartLt M c w.length⟩ :
        Fin (vertexBound (k := k_tapes) (radix (radixExponent State c) w.length))) = startU :=
    Fin.ext hstartU.symm
  rw [hstart_eq]
  refine eval_buntrockLayer3 hk _ startU _ roundNext hround_last fun u₀ j ↦ ?_
  rw [eval_buntrockLayer2 k _ CO hCO _ u₀ j, ← hround_unique u₀ j]
  dsimp only []
  by_cases hj : j.val < vertexBound (k := k_tapes) (radix (radixExponent State c) w.length)
  · simp only [hj, ↓reduceDIte, eval_buntrockLayer1_hasLenWire, eval_buntrockLayer1_qBitWire,
      eval_buntrockLayer1_yesWire, eval_buntrockLayer1_noWire, hwp]
  · simp only [hj, ↓reduceDIte, eval_buntrockLayer1_accWire, hwp]

/-! ### Private sanity check -/

section Sanity

private example : Fintype.card (WPNode 2) ≤ 2 * (2 + 1) ^ 2 + 1 :=
  card_wpNode_le 2

end Sanity

end Cslib.Complexity
