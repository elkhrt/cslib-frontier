/-
Copyright (c) 2026 CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.ConvThreeSum
public import CslibFrontier.Computability.Complexity.FineGrained.ModuloPacking
import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalModel
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Chan–He Bounded-Worklist Turing Machine for Reducing 3SUM to Convolution-3SUM

This module constructs and analyzes the deterministic multi-tape Turing machine state transition,
input validator, initializer, and per-round tape and time bounds for Chan and He's bounded-worklist
reduction from positive-integer three-set `3SUM` to `Convolution-3SUM`.

## Main definitions

* `CslibFrontier.Complexity.ChanHeTask`, `CslibFrontier.Complexity.encChanHeTask`,
  `CslibFrontier.Complexity.ChanHeCtx`, `CslibFrontier.Complexity.encChanHeCtx`,
  `CslibFrontier.Complexity.ChanHeState`, `CslibFrontier.Complexity.encChanHeState`,
  `CslibFrontier.Complexity.chanHeStep`, `CslibFrontier.Complexity.chanHeStepCost`,
  `CslibFrontier.Complexity.chanHeIterBudget`: bounded-worklist state, transition, cost, and budget.
* `CslibFrontier.Complexity.validThreeSumBool`, `CslibFrontier.Complexity.threeSumMaxVal`,
  `CslibFrontier.Complexity.chanHeInit`, `CslibFrontier.Complexity.chanHeInitRawCost`,
  `CslibFrontier.Complexity.chanHeInitScale`, `CslibFrontier.Complexity.decideThreeSum`,
  `CslibFrontier.Complexity.chanHeValidStateBnd`, `CslibFrontier.Complexity.chanHeConvCap`,
  `CslibFrontier.Complexity.chanHeValidRoundBnd`: validator, initializer, decider, and trajectory
  caps.

## Main results

* `CslibFrontier.Complexity.decideThreeSum_iff`,
  `CslibFrontier.Complexity.computableInO_chanHeStep`,
  `CslibFrontier.Complexity.computableInO_validThreeSumBool`,
  `CslibFrontier.Complexity.computableInO_chanHeInitAndBudget`,
  `CslibFrontier.Complexity.encChanHeState_valid_le`,
  `CslibFrontier.Complexity.chanHeStepCost_valid_le`,
  `CslibFrontier.Complexity.mPar_le_bound`: soundness, Turing machine complexity, and uniform step
  caps.
-/

public section

namespace CslibFrontier.Complexity

open Turing Turing.MultiTapeTM
open Cslib.Complexity
open Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.ThreeSum.ChanHe
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

private theorem length_encNat (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

private theorem size_le_self (k : ℕ) : k.size ≤ k :=
  Nat.size_le.mpr k.lt_two_pow_self

attribute [local irreducible] encNat encIntBin encUnary

/-! ### Worklist state, step function, and correctness invariant -/

/-- A single worklist task `(fuel, (L₁, (L₂, L₃)))` in the Chan–He recursion tree. -/
abbrev ChanHeTask := ℕ × IntTriple

/-- Binary tape encoding of `ChanHeTask`. -/
@[expose] def encChanHeTask : ChanHeTask ↪ List Bool := encPair encNat encIntTriple

/-- Read-only context `((U, (N, Λ)), Q)` shared across all steps of a Chan–He run. -/
abbrev ChanHeCtx := (ℕ × (ℕ × ℕ)) × List ℕ

/-- Binary tape encoding of `ChanHeCtx`. -/
@[expose] def encChanHeCtx : ChanHeCtx ↪ List Bool :=
  encPair (encPair encNat (encPair encNat encNat)) (encList encNat)

/-- Bounded-worklist state `((found, stack), ctx)` of the Chan–He reduction. -/
abbrev ChanHeState := (Bool × List ChanHeTask) × ChanHeCtx

/-- Binary tape encoding of `ChanHeState`. -/
@[expose] def encChanHeState : ChanHeState ↪ List Bool :=
  encPair (encPair encBool (encList encChanHeTask)) encChanHeCtx

private def defaultWTask : ChanHeTask := (0, ([], ([], [])))

private def wTaskSkip (t : ChanHeTask) : Bool :=
  decide (t.1 = 0) || (t.2.1.isEmpty || (t.2.2.1.isEmpty || t.2.2.2.isEmpty))

/-- One step of the Chan–He bounded-worklist recursion using a `ConvThreeSum` decider `gConv`. -/
def chanHeStep (gConv : List ℕ → Bool) (st : ChanHeState) : ChanHeState :=
  if st.1.1 || st.1.2.isEmpty then ((st.1.1, []), st.2)
  else
    let t := st.1.2.headD defaultWTask; let rest := st.1.2.tail
    if wTaskSkip t then ((false, rest), st.2)
    else
      let M := modulusList st.2.2 st.2.1.2.2 t.2.1 t.2.2.1 t.2.2.2
      if gConv (oneArrayList st.2.1.1 st.2.1.2.1 M t.2.1 t.2.2.1 t.2.2.2) then ((true, []), st.2)
      else
        let f' := t.1 - 1
        ((false, (f', (heavyList M t.2.1, t.2.2)) ::
          (f', (t.2.1, (heavyList M t.2.2.1, t.2.2.2))) ::
          (f', (t.2.1, (t.2.2.1, heavyList M t.2.2.2))) :: rest), st.2)

/-- Any state with an empty worklist stack is a fixed point of `chanHeStep`. -/
@[simp] theorem chanHeStep_nil (gConv : List ℕ → Bool) (b : Bool) (ctx : ChanHeCtx) :
    chanHeStep gConv ((b, []), ctx) = ((b, []), ctx) := by simp [chanHeStep]

/-- Polylogarithmic upper bound `2 * (2 * ⌊log₂ n⌋ + 2)^5` on the total number of worklist steps. -/
def chanHeIterBudget (n : ℕ) : ℕ := 2 * (2 * Nat.log 2 n + 2) ^ 5

/-- Explicit upper bound `chanHeIterBudget n + 1 ≤ 65 * L ^ 5` whenever `n.size + 1 ≤ L`. -/
theorem chanHeIterBudget_succ_le {n L : ℕ} (hL : n.size + 1 ≤ L) :
    chanHeIterBudget n + 1 ≤ 65 * L ^ 5 := by
  unfold chanHeIterBudget
  rw [natLog2_eq_size_sub_one]
  have h1 : 2 * (n.size - 1) + 2 ≤ 2 * L := by omega
  have h2 : (2 * (n.size - 1) + 2) ^ 5 ≤ 32 * L ^ 5 :=
    (Nat.pow_le_pow_left h1 5).trans_eq (by ring)
  have hL1 : 1 ≤ L ^ 5 := Nat.one_le_pow 5 L (by omega)
  omega

private theorem work_fuel_le_iterBudget (n : ℕ) : Math.work (fuel n) ≤ chanHeIterBudget n := by
  have hw := Math.work_eq (fuel n)
  have hf := three_pow_fuel_le n
  rw [pow_succ'] at hw
  unfold chanHeIterBudget; omega

private def toMathTask (t : ChanHeTask) : Math.Task :=
  ⟨t.1, ![t.2.1.toFinset, t.2.2.1.toFinset, t.2.2.2.toFinset]⟩

private structure TaskInv (n U f₀ : ℕ) (t : ChanHeTask) : Prop where
  nd₁ : t.2.1.Nodup
  nd₂ : t.2.2.1.Nodup
  nd₃ : t.2.2.2.Nodup
  len₁ : t.2.1.length ≤ n
  len₂ : t.2.2.1.length ≤ n
  len₃ : t.2.2.2.length ≤ n
  bdd₁ : Bdd U t.2.1.toFinset
  bdd₂ : Bdd U t.2.2.1.toFinset
  bdd₃ : Bdd U t.2.2.2.toFinset
  fuel_le : t.1 ≤ f₀

private theorem bdd_size_int {U : ℕ} {L : List ℤ} (hb : Bdd U L.toFinset) :
    listMax (fun z => (encIntBin z).length) L ≤ U.size + 1 := by
  refine listMax_le fun z hz => ?_
  rw [length_encIntBin]
  have habs : |z| ≤ (U : ℤ) := hb z (List.mem_toFinset.mpr hz)
  have hna : (z.natAbs : ℤ) ≤ (U : ℤ) := (Int.natCast_natAbs z).trans_le habs
  exact Nat.succ_le_succ (Nat.size_le_size (Int.ofNat_le.mp hna))

private theorem chanHeStep_spec {gConv : List ℕ → Bool}
    (hg : ∀ A, A ∈ ConvThreeSum ↔ gConv A = true) {n U : ℕ} :
    let m := mPar n U
    let ctx : ChanHeCtx := ((U, (2 * m ^ 2, labelBits U)), primesList m)
    ∀ (ans : Bool) (stk : List ChanHeTask),
      (∀ t ∈ stk, TaskInv n U (fuel n) t) →
      Math.Bounded (fuel n) (stk.map toMathTask) →
      let st' := chanHeStep gConv ((ans, stk), ctx)
      st'.2 = ctx ∧
        (∀ t ∈ st'.1.2, TaskInv n U (fuel n) t) ∧
        Math.Bounded (fuel n) (st'.1.2.map toMathTask) ∧
        ((st'.1.1 = true ∨ ∃ ν ∈ Math.output (Nat.primesLE m) (labelBits U)
            (st'.1.2.map toMathTask), Convolution (8 * m ^ 2) (ν.oneArray U)) ↔
          (ans = true ∨ ∃ ν ∈ Math.output (Nat.primesLE m) (labelBits U)
            (stk.map toMathTask), Convolution (8 * m ^ 2) (ν.oneArray U))) ∧
        (st'.1.1 = true ∨ st'.1.2 = [] ∨
          Math.potential (st'.1.2.map toMathTask) + 1 ≤ Math.potential (stk.map toMathTask)) := by
  intro m ctx ans stk hinv hbnd
  have hQ_sort : List.Pairwise (· < ·) (primesList m) := pairwise_primesList m
  have hQ_fs : (primesList m).toFinset = Nat.primesLE m := primesList_toFinset m
  have hQ_pos : ∀ q ∈ primesList m, 0 < q := fun q hq => by
    rw [primesList_eq_filter_range, List.mem_filter, decide_eq_true_eq] at hq
    exact hq.2.pos
  cases ans with
  | true =>
    have hs : chanHeStep gConv ((true, stk), ctx) = ((true, []), ctx) := by simp [chanHeStep]
    rw [hs]; exact ⟨rfl, by simp, trivial, by simp, Or.inl rfl⟩
  | false =>
    rcases stk with _ | ⟨t, rest⟩
    · have hs : chanHeStep gConv ((false, []), ctx) = ((false, []), ctx) := by simp [chanHeStep]
      rw [hs]; exact ⟨rfl, by simp, trivial, Iff.rfl, Or.inr (Or.inl rfl)⟩
    · have ht : TaskInv n U (fuel n) t := hinv t (List.mem_cons_self ..)
      have hrest : ∀ r ∈ rest, TaskInv n U (fuel n) r := fun r hr =>
        hinv r (List.mem_cons_of_mem _ hr)
      have hout := Math.output_step (Nat.primesLE m) (labelBits U) (toMathTask t)
        (rest.map toMathTask)
      have hpot := Math.potential_step (Nat.primesLE m) (labelBits U) (toMathTask t)
        (rest.map toMathTask)
      have hbstep := Math.bounded_step (Nat.primesLE m) (labelBits U) (toMathTask t)
        (rest.map toMathTask) (by simpa using hbnd)
      by_cases hsk : wTaskSkip t = true
      · have hs : chanHeStep gConv ((false, t :: rest), ctx) = ((false, rest), ctx) := by
          unfold chanHeStep; simp [hsk]
        have hmstep : Math.step (Nat.primesLE m) (labelBits U) (toMathTask t)
            (rest.map toMathTask) = (rest.map toMathTask, none) := by
          unfold wTaskSkip at hsk
          simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hsk
          rcases t with ⟨_ | f, L₁, L₂, L₃⟩
          · rfl
          · have hemp : (toMathTask (f + 1, (L₁, (L₂, L₃)))).empty := by
              change L₁.toFinset = ∅ ∨ L₂.toFinset = ∅ ∨ L₃.toFinset = ∅
              rcases hsk with hf | rfl | rfl | rfl
              · omega
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
            unfold Math.step
            have hf' : (toMathTask (f + 1, (L₁, (L₂, L₃)))).fuel = f + 1 := rfl
            simp only [hf', hemp, ↓reduceIte]
        rw [hmstep] at hout hpot hbstep
        rw [hs]
        refine ⟨rfl, hrest, hbstep, ?_, Or.inr (Or.inr hpot)⟩
        simp only [List.map_cons, hout, Option.toList_none, List.nil_append]
      · have hskF : wTaskSkip t = false := Bool.eq_false_iff.mpr hsk
        have hinfo : ∃ f, t.1 = f + 1 ∧ ¬ (toMathTask t).empty := by
          unfold wTaskSkip at hskF
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, List.isEmpty_eq_false_iff]
            at hskF
          obtain ⟨hf0, h1, h2, h3⟩ := hskF
          refine ⟨t.1 - 1, by omega, ?_⟩
          simp only [toMathTask, Math.Task.empty, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val, List.toFinset_eq_empty_iff, not_or]
          exact ⟨h1, h2, h3⟩
        obtain ⟨f, htf, hnemp⟩ := hinfo
        let M := modulusList (primesList m) (labelBits U) t.2.1 t.2.2.1 t.2.2.2
        have hM_pos : 0 < M := modulusList_pos hQ_pos _ _ _ _
        have hM_eq : M = modulus (Nat.primesLE m) (labelBits U)
            t.2.1.toFinset t.2.2.1.toFinset t.2.2.2.toFinset := by
          rw [← hQ_fs]; exact modulusList_eq_modulus hQ_sort _ ht.nd₁ ht.nd₂ ht.nd₃
        let arr := oneArrayList U (2 * m ^ 2) M t.2.1 t.2.2.1 t.2.2.2
        have harr_pos : ∀ a ∈ arr, 0 < a := fun a ha =>
          (oneArrayList_pos_and_le hM_pos ht.nd₁ ht.nd₂ ht.nd₃ ht.bdd₁ ht.bdd₂ ht.bdd₃ ha).1
        have hhit_iff : gConv arr = true ↔
            Convolution (8 * m ^ 2)
              (((toMathTask t).node (Nat.primesLE m) (labelBits U)).oneArray U) := by
          rw [← hg arr, mem_convThreeSum_iff, and_iff_right harr_pos]
          dsimp only [arr]
          rw [oneArrayList_conv_iff hM_pos ht.nd₁ ht.nd₂ ht.nd₃ ht.bdd₁ ht.bdd₂ ht.bdd₃,
            show 4 * (2 * m ^ 2) = 8 * m ^ 2 by ring, hM_eq]
          rfl
        let c1 : ChanHeTask := (f, (heavyList M t.2.1, (t.2.2.1, t.2.2.2)))
        let c2 : ChanHeTask := (f, (t.2.1, (heavyList M t.2.2.1, t.2.2.2)))
        let c3 : ChanHeTask := (f, (t.2.1, (t.2.2.1, heavyList M t.2.2.2)))
        have hmap_ch : (c1 :: c2 :: c3 :: rest).map toMathTask =
            (toMathTask t).children (Nat.primesLE m) (labelBits U) f ++ rest.map toMathTask := by
          simp only [List.map_cons, List.cons_append, List.nil_append, Math.Task.children,
            toMathTask, Math.Task.node, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
            c1, c2, c3, heavyList_toFinset ht.nd₁, heavyList_toFinset ht.nd₂,
            heavyList_toFinset ht.nd₃, hM_eq]
        have hmstep : Math.step (Nat.primesLE m) (labelBits U) (toMathTask t)
            (rest.map toMathTask) =
            ((c1 :: c2 :: c3 :: rest).map toMathTask,
              some ((toMathTask t).node (Nat.primesLE m) (labelBits U))) := by
          rw [hmap_ch]; unfold Math.step
          have htf' : (toMathTask t).fuel = f + 1 := htf
          simp [htf', hnemp]
        rw [hmstep] at hout hpot hbstep
        by_cases hhit : gConv arr = true
        · have hs : chanHeStep gConv ((false, t :: rest), ctx) = ((true, []), ctx) := by
            unfold chanHeStep; simp [hskF, ctx, M, arr, hhit]
          rw [hs]
          refine ⟨rfl, by simp, trivial, ?_, Or.inl rfl⟩
          simp only [List.map_cons, hout, Option.toList_some, List.singleton_append, List.mem_cons,
            Bool.false_eq_true, false_or, true_or, true_iff]
          exact ⟨_, Or.inl rfl, hhit_iff.mp hhit⟩
        · have hhitF : gConv arr = false := Bool.eq_false_iff.mpr hhit
          have hs : chanHeStep gConv ((false, t :: rest), ctx) =
              ((false, c1 :: c2 :: c3 :: rest), ctx) := by
            unfold chanHeStep
            have hf' : t.1 - 1 = f := by omega
            simp [hskF, ctx, M, arr, hhitF, hf', c1, c2, c3]
          have hbdd_heavy {L : List ℤ} (hb : Bdd U L.toFinset) : Bdd U (heavyList M L).toFinset :=
            fun z hz => hb z (List.mem_toFinset.mpr (mem_heavyList_sub (List.mem_toFinset.mp hz)))
          have hc_inv : ∀ r ∈ c1 :: c2 :: c3 :: rest, TaskInv n U (fuel n) r := by
            intro r hr
            have hf_le : f ≤ fuel n := by have := ht.fuel_le; omega
            rcases List.mem_cons.mp hr with rfl | hr1
            · exact ⟨heavyList_nodup ht.nd₁, ht.nd₂, ht.nd₃,
                (length_heavyList_le M _).trans ht.len₁, ht.len₂, ht.len₃,
                hbdd_heavy ht.bdd₁, ht.bdd₂, ht.bdd₃, hf_le⟩
            · rcases List.mem_cons.mp hr1 with rfl | hr2
              · exact ⟨ht.nd₁, heavyList_nodup ht.nd₂, ht.nd₃, ht.len₁,
                  (length_heavyList_le M _).trans ht.len₂, ht.len₃,
                  ht.bdd₁, hbdd_heavy ht.bdd₂, ht.bdd₃, hf_le⟩
              · rcases List.mem_cons.mp hr2 with rfl | hr3
                · exact ⟨ht.nd₁, ht.nd₂, heavyList_nodup ht.nd₃, ht.len₁, ht.len₂,
                    (length_heavyList_le M _).trans ht.len₃,
                    ht.bdd₁, ht.bdd₂, hbdd_heavy ht.bdd₃, hf_le⟩
                · exact hrest r hr3
          rw [hs]
          refine ⟨rfl, hc_inv, hbstep, ?_, Or.inr (Or.inr hpot)⟩
          simp only [List.map_cons, hout, Option.toList_some, List.singleton_append, List.mem_cons,
            Bool.false_eq_true, false_or]
          have hno : ¬ Convolution (8 * m ^ 2)
              (((toMathTask t).node (Nat.primesLE m) (labelBits U)).oneArray U) :=
            fun hc => hhit (hhit_iff.mpr hc)
          constructor
          · rintro ⟨ν, hν, hc⟩; exact ⟨ν, Or.inr hν, hc⟩
          · rintro ⟨ν, rfl | hν, hc⟩
            · exact absurd hc hno
            · exact ⟨ν, hν, hc⟩

private theorem iterate_chanHeStep_inv {gConv : List ℕ → Bool}
    (hg : ∀ A, A ∈ ConvThreeSum ↔ gConv A = true) {n U : ℕ}
    {L₁ L₂ L₃ : List ℤ} (hroot : TaskInv n U (fuel n) (fuel n, (L₁, (L₂, L₃)))) :
    let m := mPar n U
    let ctx : ChanHeCtx := ((U, (2 * m ^ 2, labelBits U)), primesList m)
    let st₀ : ChanHeState := ((false, [(fuel n, (L₁, (L₂, L₃)))]), ctx)
    ∀ j,
      let st := (chanHeStep gConv)^[j] st₀
      st.2 = ctx ∧
        (∀ t ∈ st.1.2, TaskInv n U (fuel n) t) ∧
        Math.Bounded (fuel n) (st.1.2.map toMathTask) ∧
        ((st.1.1 = true ∨ ∃ ν ∈ Math.output (Nat.primesLE m) (labelBits U)
            (st.1.2.map toMathTask), Convolution (8 * m ^ 2) (ν.oneArray U)) ↔
          ∃ ν ∈ reduction n U L₁.toFinset L₂.toFinset L₃.toFinset,
            Convolution (8 * m ^ 2) (ν.oneArray U)) ∧
        (st.1.1 = true ∨ st.1.2 = [] ∨
          Math.potential (st.1.2.map toMathTask) + j ≤ Math.work (fuel n)) := by
  intro m ctx st₀ j
  induction j with
  | zero =>
    simp only [Function.iterate_zero_apply, st₀, List.mem_singleton, forall_eq, List.map_cons,
      List.map_nil, Bool.false_eq_true, false_or, Math.potential, List.sum_cons, List.sum_nil,
      add_zero]
    refine ⟨trivial, hroot, Math.bounded_singleton _, ?_, Or.inr le_rfl⟩
    simp [Math.output, Math.Task.output, toMathTask, reduction, m]
  | succ j ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    set st := (chanHeStep gConv)^[j] st₀
    obtain ⟨hctx, hinv, hbnd, hiff, hpot⟩ := ih
    have hst_eq : st = ((st.1.1, st.1.2), ctx) := Prod.ext rfl hctx
    rw [hst_eq]
    obtain ⟨hctx', hinv', hbnd', hiff', hpot'⟩ := chanHeStep_spec hg st.1.1 st.1.2 hinv hbnd
    refine ⟨hctx', hinv', hbnd', hiff'.trans hiff, ?_⟩
    rcases hpot' with h1 | h2 | hp'
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · rcases hpot with h1 | h2 | hp
      · rw [h1]; exact Or.inl (by simp [chanHeStep])
      · rw [h2]; exact Or.inr (Or.inl (by simp [chanHeStep]))
      · exact Or.inr (Or.inr (by
          have hp1 : Math.potential ((chanHeStep gConv ((st.1.1, st.1.2), ctx)).1.2.map
            toMathTask) + 1 ≤ Math.potential (st.1.2.map toMathTask) := hp'
          have hp0 : Math.potential (st.1.2.map toMathTask) + j ≤ Math.work (fuel n) := hp
          omega))

/-- Decides whether `p : ThreeSumInput` is a well-formed nonempty positive duplicate-free
equal-length triple. -/
def validThreeSumBool (p : ThreeSumInput) : Bool :=
  decide (p.1.length = p.2.1.length) && decide (p.2.1.length = p.2.2.length) &&
    !decide (p.1.length = 0) &&
    allPosNatList p.1 && allPosNatList p.2.1 && allPosNatList p.2.2 &&
    decide p.1.Nodup && decide p.2.1.Nodup && decide p.2.2.Nodup

/-- If `validThreeSumBool p = true`, then `1 ≤ p.1.length` and `threeSumSize p = 3 * p.1.length`. -/
theorem validThreeSumBool_lengths {p : ThreeSumInput} (hv : validThreeSumBool p = true) :
    1 ≤ p.1.length ∧ threeSumSize p = 3 * p.1.length := by
  unfold validThreeSumBool at hv
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at hv
  have h1 := hv.1.1.1.1.1.1.1.1
  have h2 := hv.1.1.1.1.1.1.1.2
  have hn0 := hv.1.1.1.1.1.1.2
  have hsum := threeSumSize_add p
  omega

/-- Maximum input entry `max_{w ∈ X ∪ Y ∪ Z} w` of `p : ThreeSumInput`. -/
def threeSumMaxVal (p : ThreeSumInput) : ℕ :=
  max (maxNatList p.1) (max (maxNatList p.2.1) (maxNatList p.2.2))

/-- The bit-length of `threeSumMaxVal p` is strictly below `threeSumBitScale p`. -/
theorem threeSumMaxVal_size_succ_le (p : ThreeSumInput) :
    (threeSumMaxVal p).size + 1 ≤ threeSumBitScale p := by
  obtain ⟨b1, b2, b3⟩ := listMax_size_lt_threeSumBitScale p
  have s1 := (maxNatList_size_le p.1).trans_lt b1
  have s2 := (maxNatList_size_le p.2.1).trans_lt b2
  have s3 := (maxNatList_size_le p.2.2).trans_lt b3
  unfold threeSumMaxVal
  rcases le_total (maxNatList p.2.1) (maxNatList p.2.2) with h23 | h23 <;>
    rcases le_total (maxNatList p.1) (max (maxNatList p.2.1) (maxNatList p.2.2)) with h1 | h1
  · rw [max_eq_right h1, max_eq_right h23]; omega
  · rw [max_eq_left h1]; omega
  · rw [max_eq_right h1, max_eq_left h23]; omega
  · rw [max_eq_left h1]; omega

/-- Initial Chan–He worklist state constructed from `p : ThreeSumInput`. -/
def chanHeInit (p : ThreeSumInput) : ChanHeState :=
  let n := p.1.length
  let U := threeSumMaxVal p
  let m := mPar n U
  let L₁ := p.1.map (fun x : ℕ => (x : ℤ))
  let L₂ := p.2.1.map (fun y : ℕ => (y : ℤ))
  let L₃ := p.2.2.map (fun z : ℕ => -(z : ℤ))
  ((false, [(fuel n, (L₁, (L₂, L₃)))]), ((U, (2 * m ^ 2, labelBits U)), primesList m))

/-- Decides `ThreeSum` by running `chanHeIterBudget p.1.length` steps of `chanHeStep gConv`. -/
def decideThreeSum (gConv : List ℕ → Bool) (p : ThreeSumInput) : Bool :=
  if validThreeSumBool p then
    (((chanHeStep gConv)^[chanHeIterBudget p.1.length] (chanHeInit p)).1).1
  else false

/-- Conditional evaluation identity for `decideThreeSum`. -/
theorem decideThreeSum_eq_ite (gConv : List ℕ → Bool) (p : ThreeSumInput) :
    decideThreeSum gConv p = if validThreeSumBool p then
      (((chanHeStep gConv)^[chanHeIterBudget p.1.length] (chanHeInit p)).1).1 else false := by
  unfold decideThreeSum; rfl

private theorem valid_root_inv {p : ThreeSumInput} (hv : validThreeSumBool p = true) :
    let n := p.1.length
    let U := threeSumMaxVal p
    1 ≤ n ∧ p.1.length = p.2.1.length ∧ p.2.1.length = p.2.2.length ∧
      (∀ x ∈ p.1, 0 < x) ∧ (∀ y ∈ p.2.1, 0 < y) ∧ (∀ z ∈ p.2.2, 0 < z) ∧
      p.1.Nodup ∧ p.2.1.Nodup ∧ p.2.2.Nodup ∧
      TaskInv n U (fuel n)
        (fuel n, (p.1.map (fun x : ℕ => (x : ℤ)),
          (p.2.1.map (fun y : ℕ => (y : ℤ)), p.2.2.map (fun z : ℕ => -(z : ℤ))))) := by
  unfold validThreeSumBool at hv
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    allPosNatList_eq_true_iff] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlen1, hlen2⟩, hn0⟩, hp1⟩, hp2⟩, hp3⟩, hnd1⟩, hnd2⟩, hnd3⟩ := hv
  let n := p.1.length
  let U := threeSumMaxVal p
  have hbdd_pos (A : List ℕ) (hA : maxNatList A ≤ U) :
      Bdd U (A.map fun x : ℕ => (x : ℤ)).toFinset := fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    rw [maxNatList_eq_listMax] at hA
    rw [abs_of_nonneg (Nat.cast_nonneg x)]; exact_mod_cast (le_listMax (f := id) hx).trans hA
  have hb1 : Bdd U (p.1.map fun x : ℕ => (x : ℤ)).toFinset := hbdd_pos p.1 (le_max_left _ _)
  have hb2 : Bdd U (p.2.1.map fun y : ℕ => (y : ℤ)).toFinset :=
    hbdd_pos p.2.1 ((le_max_left _ _).trans (le_max_right _ _))
  have hb3 : Bdd U (p.2.2.map fun z : ℕ => -(z : ℤ)).toFinset := fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    have hA : listMax id p.2.2 ≤ U := by
      rw [← maxNatList_eq_listMax]; exact (le_max_right _ _).trans (le_max_right _ _)
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg x)]
    exact_mod_cast (le_listMax (f := id) hx).trans hA
  refine ⟨by omega, hlen1, hlen2, hp1, hp2, hp3, hnd1, hnd2, hnd3,
    hnd1.map Nat.cast_injective, hnd2.map Nat.cast_injective,
    hnd3.map fun _ _ h => Nat.cast_injective (neg_injective h),
    by rw [List.length_map], by rw [List.length_map, hlen1],
    by rw [List.length_map, ← hlen2, ← hlen1], hb1, hb2, hb3, le_rfl⟩

/-- `decideThreeSum gConv` decides `ThreeSum` whenever `gConv` decides `ConvThreeSum`. -/
theorem decideThreeSum_iff {gConv : List ℕ → Bool}
    (hg : ∀ A, A ∈ ConvThreeSum ↔ gConv A = true) (p : ThreeSumInput) :
    p ∈ ThreeSum ↔ decideThreeSum gConv p = true := by
  unfold decideThreeSum
  by_cases hv : validThreeSumBool p = true
  · simp only [hv, ↓reduceIte]
    obtain ⟨hn1, hlen1, hlen2, hp1, hp2, hp3, hnd1, hnd2, hnd3, hroot⟩ := valid_root_inv hv
    let n := p.1.length
    let U := threeSumMaxVal p
    let L₁ := p.1.map (fun x : ℕ => (x : ℤ))
    let L₂ := p.2.1.map (fun y : ℕ => (y : ℤ))
    let L₃ := p.2.2.map (fun z : ℕ => -(z : ℤ))
    have hadm : Admissible n U L₁.toFinset L₂.toFinset L₃.toFinset :=
      ⟨(List.toFinset_card_le L₁).trans hroot.len₁,
       (List.toFinset_card_le L₂).trans hroot.len₂,
       (List.toFinset_card_le L₃).trans hroot.len₃,
       hroot.bdd₁, hroot.bdd₂, hroot.bdd₃⟩
    obtain ⟨_, _, _, hiff, hpot⟩ := iterate_chanHeStep_inv hg hroot (chanHeIterBudget n)
    have hdone :
        let st := (chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)
        st.1.1 = true ∨ st.1.2 = [] := by
      rcases hpot with h1 | h2 | hp
      · exact Or.inl h1
      · exact Or.inr h2
      · rcases hstk : ((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1.2 with
          _ | ⟨t, ts⟩
        · exact Or.inr hstk
        · exfalso
          change Math.potential (((chanHeStep gConv)^[chanHeIterBudget n]
            (chanHeInit p)).1.2.map toMathTask) + chanHeIterBudget n ≤ Math.work (fuel n) at hp
          rw [hstk] at hp
          simp only [Math.potential, List.map_cons, List.sum_cons] at hp
          have := Math.work_pos (toMathTask t).fuel
          have := work_fuel_le_iterBudget n
          omega
    have hans_iff :
        (((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1).1 = true ↔
          HasThreeSetSolution L₁.toFinset L₂.toFinset L₃.toFinset := by
      rw [reduction_correct_oneArray hn1 hadm, ← hiff]
      rcases hdone with h1 | h2
      · change (((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1).1 = true ↔
          (((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1).1 = true ∨ _
        simp [h1]
      · change (((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1).1 = true ↔
          (((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1).1 = true ∨
            ∃ ν ∈ Math.output _ _
              (((chanHeStep gConv)^[chanHeIterBudget n] (chanHeInit p)).1.2.map toMathTask), _
        simp [h2, Math.output]
    rw [hans_iff, mem_threeSum_iff]
    simp only [hnd1, hnd2, hnd3, hlen1, hlen2, true_and]
    rw [and_iff_right hp1, and_iff_right hp2, and_iff_right hp3]
    unfold HasThreeSetSolution
    simp only [L₁, L₂, L₃, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨x, hx, y, hy, z, hz, hsum⟩
      exact ⟨x, ⟨x, hx, rfl⟩, y, ⟨y, hy, rfl⟩, -(z : ℤ), ⟨z, hz, rfl⟩,
        by push_cast [← hsum]; ring⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, hsum⟩
      exact ⟨x, hx, y, hy, z, hz, by omega⟩
  · have hvF : validThreeSumBool p = false := Bool.eq_false_iff.mpr hv
    simp only [hvF, Bool.false_eq_true, ↓reduceIte, iff_false]
    rw [mem_threeSum_iff]
    rintro ⟨hnd1, hnd2, hnd3, hlen1, hlen2, hp1, hp2, hp3, x, hx, _⟩
    have hn0 : p.1.length ≠ 0 := fun h => by rw [List.length_eq_zero_iff.mp h] at hx; cases hx
    apply hv; unfold validThreeSumBool
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      allPosNatList_eq_true_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hlen1, hlen2⟩, hn0⟩, hp1⟩, hp2⟩, hp3⟩, hnd1⟩, hnd2⟩, hnd3⟩

/-! ### Quantitative parameter bounds and multi-tape Turing machines -/

/-- Upper bound `labelBits U ≤ U.size + 2`. -/
theorem labelBits_le_size (U : ℕ) : labelBits U ≤ U.size + 2 := by
  unfold labelBits
  rw [natLog2_eq_size_sub_one]
  have : (2 * U).size ≤ U.size + 1 :=
    Nat.size_le.mpr (by have := Nat.lt_size_self U; rw [Nat.pow_add]; omega)
  omega

/-- Subquadratic parameter bound `mPar n U ≤ 512 * √n * (n.size + 1) * (U.size + 1)^2`. -/
theorem mPar_le_bound {n U : ℕ} (hn : 1 ≤ n) :
    mPar n U ≤ 512 * Nat.sqrt n * (n.size + 1) * (U.size + 1) ^ 2 := by
  have hL : labelBits U ≤ 2 * (U.size + 1) := by have := labelBits_le_size U; omega
  have hsq1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hw : wPar n U + 1 ≤ 21 * (U.size + 1) * Nat.sqrt n := by
    unfold wPar
    have : Nat.sqrt n + 1 ≤ 2 * Nat.sqrt n := by omega
    calc 5 * labelBits U * (Nat.sqrt n + 1) + 1
        ≤ 5 * (2 * (U.size + 1)) * (2 * Nat.sqrt n) + 1 := by gcongr
      _ ≤ 21 * (U.size + 1) * Nat.sqrt n := by nlinarith
  have hw_sz : (wPar n U + 1).size ≤ n.size + U.size + 7 := by
    refine Nat.size_le.mpr ?_
    have h1 : 21 < 2 ^ 5 := by decide
    have h2 : U.size + 1 < 2 ^ (U.size + 1) := Nat.lt_two_pow_self
    have h3 : Nat.sqrt n < 2 ^ n.size := (Nat.sqrt_le_self n).trans_lt (Nat.lt_size_self n)
    have h4 : 21 * (U.size + 1) * Nat.sqrt n ≤ 2 ^ 5 * 2 ^ (U.size + 1) * 2 ^ n.size :=
      Nat.mul_le_mul (Nat.mul_le_mul h1.le h2.le) h3.le
    have h5 : 2 ^ 5 * 2 ^ (U.size + 1) * 2 ^ n.size < 2 ^ (n.size + U.size + 7) := by
      simp only [← Nat.pow_add]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    exact lt_of_le_of_lt hw (lt_of_le_of_lt h4 h5)
  have hlg : 2 * Nat.log 2 (wPar n U + 1) + 4 ≤ 20 * (n.size + 1) * (U.size + 1) := by
    rw [natLog2_eq_size_sub_one]
    have : 2 * ((wPar n U + 1).size - 1) + 4 ≤ 2 * n.size + 2 * U.size + 18 := by omega
    nlinarith
  unfold mPar
  calc (wPar n U + 1) * (2 * Nat.log 2 (wPar n U + 1) + 4)
      ≤ (21 * (U.size + 1) * Nat.sqrt n) * (20 * (n.size + 1) * (U.size + 1)) :=
        Nat.mul_le_mul hw hlg
    _ ≤ 512 * Nat.sqrt n * (n.size + 1) * (U.size + 1) ^ 2 := by nlinarith

/-- Logarithmic recursion depth bound `fuel n ≤ 3 * (n.size + 2)`. -/
theorem fuel_le_size (n : ℕ) : fuel n ≤ 3 * (n.size + 2) := by
  unfold fuel height
  rw [natClog2_eq_size_pred, natLog2_eq_size_sub_one]
  split_ifs
  · omega
  · have := size_le_self (n.size - 1 + 2 - 1); omega

/-- Per-round time and space budget for `chanHeStep gConv` at degree `d` and oracle cost `tConv`. -/
def chanHeStepCost (tConv : List ℕ → ℕ) (d : ℕ) (st : ChanHeState) : ℕ :=
  let t := st.1.2.headD defaultWTask; let Q := st.2.2
  let U := st.2.1.1; let N := st.2.1.2.1; let Λ := st.2.1.2.2
  let M := modulusList Q Λ t.2.1 t.2.2.1 t.2.2.2
  let mi : ModInput := (Q, (Λ, t.2)); let pi : PackInput := ((U, (N, M)), t.2)
  (encChanHeState st).length + (Q.length + 1) * modLen mi * (modScale mi + 1) ^ d +
    packLen pi * (packScale pi + 1) ^ d +
    (if st.1.1 || st.1.2.isEmpty || wTaskSkip t then 0
      else tConv (oneArrayList U N M t.2.1 t.2.2.1 t.2.2.2)) +
    (t.2.1.length + 1) * (heavyScale (M, t.2.1) + 1) ^ d +
    (t.2.2.1.length + 1) * (heavyScale (M, t.2.2.1) + 1) ^ d +
    (t.2.2.2.length + 1) * (heavyScale (M, t.2.2.2) + 1) ^ d + (t.1.size + 1) ^ d

private theorem computableInPolyTime_predNat :
    ComputableInPolyTime (fun k : ℕ => k - 1) encNat encNat := by fun_prop

/-- `chanHeStep gConv` is computable within time and space `O(chanHeStepCost tConv d)`. -/
theorem computableInO_chanHeStep {gConv : List ℕ → Bool} {tConv : List ℕ → ℕ}
    (hg : ComputableInO gConv (encList encNat) encBool tConv tConv) :
    ∃ d, ComputableInO (chanHeStep gConv) encChanHeState encChanHeState
      (chanHeStepCost tConv d) (chanHeStepCost tConv d) := by
  obtain ⟨dm, hmod⟩ := computableInO_modulusList
  obtain ⟨dp, hpack⟩ := computableInO_oneArrayList
  obtain ⟨dh, hheavy⟩ := computableInO_heavyList
  obtain ⟨dpr, _, hdpr⟩ := computableInPolyTime_predNat.exists_degree
  let hP1 := ComputableInO.fst (encPair encBool (encList encChanHeTask)) encChanHeCtx
  let hCtx := ComputableInO.snd (encPair encBool (encList encChanHeTask)) encChanHeCtx
  let hAns := (ComputableInO.fst encBool (encList encChanHeTask)).comp_linear hP1
  let hStk := (ComputableInO.snd encBool (encList encChanHeTask)).comp_linear hP1
  let hTop := (ComputableInO.headD' (enc := encChanHeTask) defaultWTask).comp_linear hStk
  let hRest := (ComputableInO.tail' (enc := encChanHeTask)).comp_linear hStk
  let hF := (ComputableInO.fst encNat encIntTriple).comp_linear hTop
  let hTr := (ComputableInO.snd encNat encIntTriple).comp_linear hTop
  let hA1 := (ComputableInO.fst (encList encIntBin) _).comp_linear hTr
  let hA23 := (ComputableInO.snd (encList encIntBin) _).comp_linear hTr
  let hA2 := (ComputableInO.fst (encList encIntBin) (encList encIntBin)).comp_linear hA23
  let hA3 := (ComputableInO.snd (encList encIntBin) (encList encIntBin)).comp_linear hA23
  let hUNL :=
    (ComputableInO.fst (encPair encNat (encPair encNat encNat)) (encList encNat)).comp_linear hCtx
  let hQ :=
    (ComputableInO.snd (encPair encNat (encPair encNat encNat)) (encList encNat)).comp_linear hCtx
  let hU := (ComputableInO.fst encNat (encPair encNat encNat)).comp_linear hUNL
  let hNL := (ComputableInO.snd encNat (encPair encNat encNat)).comp_linear hUNL
  let hN := (ComputableInO.fst encNat encNat).comp_linear hNL
  let hLam := (ComputableInO.snd encNat encNat).comp_linear hNL
  have hStop := hAns.or' hStk.isEmpty'
  have hSkip := hF.natIsZero'.or' (hA1.isEmpty'.or' (hA2.isEmpty'.or' hA3.isEmpty'))
  have hNil : ComputableInO (fun _ : ChanHeState => ([] : List ChanHeTask))
      encChanHeState (encList encChanHeTask) (fun st => (encChanHeState st).length) (fun _ => 0) :=
    ComputableInO.constZero []
  have hTrue : ComputableInO (fun _ : ChanHeState => true) encChanHeState encBool
      (fun st => (encChanHeState st).length) (fun _ => 0) := ComputableInO.constZero true
  have hFalse : ComputableInO (fun _ : ChanHeState => false) encChanHeState encBool
      (fun st => (encChanHeState st).length) (fun _ => 0) := ComputableInO.constZero false
  have hBrStop := (hAns.prod hNil).prod hCtx
  have hBrSkip := (hFalse.prod hRest).prod hCtx
  have hBrHit := (hTrue.prod hNil).prod hCtx
  have hM := hmod.comp (hQ.prod (hLam.prod hTr))
  have hArr := hpack.comp ((hU.prod (hN.prod hM)).prod hTr)
  have hHit := hg.comp hArr
  have hF' := hdpr.inO.comp hF
  have hH1 := hheavy.comp (hM.prod hA1)
  have hH2 := hheavy.comp (hM.prod hA2)
  have hH3 := hheavy.comp (hM.prod hA3)
  have hC1 := hF'.prod (hH1.prod hA23)
  have hC2 := hF'.prod (hA1.prod (hH2.prod hA3))
  have hC3 := hF'.prod (hA1.prod (hA2.prod hH3))
  have hPush := (ComputableInO.cons' (enc := encChanHeTask)).comp_linear (hC1.prod
    ((ComputableInO.cons' (enc := encChanHeTask)).comp_linear (hC2.prod
      ((ComputableInO.cons' (enc := encChanHeTask)).comp_linear (hC3.prod hRest)))))
  have hBrMiss := (hFalse.prod hPush).prod hCtx
  have hFull := hStop.ite hBrStop (hSkip.ite hBrSkip (hHit.ite hBrHit hBrMiss))
  let D := dm + dp + dh + dpr + 1
  refine ⟨D, (hFull.of_enc_eq fun _ => rfl).weaken ?_ ?_⟩
  all_goals
    refine BigOLe.of_le_linear 128 0 fun st => ?_
    let t := st.1.2.headD defaultWTask
    let M := modulusList st.2.2 st.2.1.2.2 t.2.1 t.2.2.1 t.2.2.2
    let mi : ModInput := (st.2.2, (st.2.1.2.2, t.2))
    let pi : PackInput := ((st.2.1.1, (st.2.1.2.1, M)), t.2)
    have hstk_le : (encList encChanHeTask st.1.2).length ≤ (encChanHeState st).length := by
      simp only [encChanHeState, length_encPair]; omega
    have htop_le : (encChanHeTask t).length ≤ (encChanHeState st).length := by
      cases hs : st.1.2 with
      | nil =>
        have h0 : (encChanHeTask defaultWTask).length ≤ 5 := by
          change (encPair encNat (encPair (encList encIntBin)
            (encPair (encList encIntBin) (encList encIntBin))) (0, ([], ([], [])))).length ≤ 5
          simp only [length_encPair, length_encNat]; decide
        have hmin : 5 ≤ (encChanHeState st).length := by
          simp only [encChanHeState, encChanHeCtx, length_encPair, encBool_apply,
            List.length_singleton]; omega
        dsimp only [t]; rw [hs]; dsimp only [List.headD]; omega
      | cons a as =>
        have ha : (encChanHeTask a).length ≤ (encList encChanHeTask (a :: as)).length := by
          rw [encList_cons, List.length_append, length_frame]; omega
        rw [hs] at hstk_le; dsimp only [t]; rw [hs]; dsimp only [List.headD]; omega
    have hrest_le : (encList encChanHeTask st.1.2.tail).length ≤ (encChanHeState st).length := by
      rcases hs : st.1.2 with _ | ⟨a, as⟩
      · exact (show (encList encChanHeTask []).length ≤ _ by rwa [hs] at hstk_le)
      · have h1 : (encList encChanHeTask as).length ≤ (encList encChanHeTask (a :: as)).length := by
          rw [encList_cons, List.length_append]; omega
        rw [hs] at hstk_le; exact h1.trans hstk_le
    have htr_le : (encIntTriple t.2).length ≤ (encChanHeTask t).length := by
      simp only [encChanHeTask, length_encPair]; omega
    have hf_le : (encNat t.1).length ≤ (encChanHeState st).length := by
      have : (encChanHeTask t).length = _ := length_encPair t; omega
    have htr_eq : (encIntTriple t.2).length = 2 * (encList encIntBin t.2.1).length + 1 +
        (encPair (encList encIntBin) (encList encIntBin) t.2.2).length := length_encPair t.2
    have ha1_le : (encList encIntBin t.2.1).length ≤ (encChanHeState st).length := by omega
    have ha23_le : (encPair (encList encIntBin) (encList encIntBin) t.2.2).length ≤
        (encChanHeState st).length := by omega
    have ha2_le : (encList encIntBin t.2.2.1).length ≤ (encChanHeState st).length := by
      have h' : 2 * (encList encIntBin t.2.2.1).length + 1 +
          (encList encIntBin t.2.2.2).length ≤ (encChanHeState st).length := by
        rwa [length_encPair] at ha23_le
      omega
    have ha3_le : (encList encIntBin t.2.2.2).length ≤ (encChanHeState st).length := by
      have h' : 2 * (encList encIntBin t.2.2.1).length + 1 +
          (encList encIntBin t.2.2.2).length ≤ (encChanHeState st).length := by
        rwa [length_encPair] at ha23_le
      omega
    have hup1 (s a : ℕ) (had : a ≤ D) : s ^ a ≤ (s + 1) ^ D :=
      (Nat.pow_le_pow_left (Nat.le_succ s) a).trans (Nat.pow_le_pow_right (Nat.succ_pos s) had)
    have hm_t := Nat.mul_le_mul_left ((st.2.2.length + 1) * modLen mi)
      (hup1 (modScale mi) dm (by dsimp only [D]; omega))
    have hm_s : modLen mi * modScale mi ^ dm ≤
        (st.2.2.length + 1) * modLen mi * (modScale mi + 1) ^ D :=
      (Nat.mul_le_mul_left (modLen mi) (hup1 (modScale mi) dm (by dsimp only [D]; omega))).trans
        (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (show 0 < st.2.2.length + 1 by omega)))
    have hp_b := Nat.mul_le_mul_left (packLen pi)
      (hup1 (packScale pi) dp (by dsimp only [D]; omega))
    have hh1 := Nat.mul_le_mul_left (t.2.1.length + 1)
      (hup1 (heavyScale (M, t.2.1)) dh (by dsimp only [D]; omega))
    have hh2 := Nat.mul_le_mul_left (t.2.2.1.length + 1)
      (hup1 (heavyScale (M, t.2.2.1)) dh (by dsimp only [D]; omega))
    have hh3 := Nat.mul_le_mul_left (t.2.2.2.length + 1)
      (hup1 (heavyScale (M, t.2.2.2)) dh (by dsimp only [D]; omega))
    have hpr_b : ((encNat t.1).length + 1) ^ dpr ≤ (t.1.size + 1) ^ D := by
      rw [length_encNat]
      exact Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [D]; omega)
    have hp1_le : (encPair encBool (encList encChanHeTask) st.1).length ≤
        (encChanHeState st).length := by simp only [encChanHeState, length_encPair]; omega
    have hctx_le : (encChanHeCtx st.2).length ≤ (encChanHeState st).length := by
      simp only [encChanHeState, length_encPair]; omega
    have hunl_le : (encPair encNat (encPair encNat encNat) st.2.1).length ≤
        (encChanHeState st).length := by
      have : (encChanHeCtx st.2).length = _ := length_encPair st.2; omega
    have hnl_le : (encPair encNat encNat st.2.1.2).length ≤ (encChanHeState st).length := by
      have : (encPair encNat (encPair encNat encNat) st.2.1).length = _ := length_encPair st.2.1
      omega
    have hq_le : (encList encNat st.2.2).length ≤ (encChanHeState st).length := by
      have : (encChanHeCtx st.2).length = _ := length_encPair st.2; omega
    dsimp only [chanHeStepCost, wTaskSkip, Function.comp_apply, encChanHeState, t, M, mi, pi] at *
    change _ ≤ 128 * _ + 0
    by_cases hc1 : (st.1.1 || st.1.2.isEmpty) = true
    · simp only [hc1, Bool.true_or, ↓reduceIte]; omega
    · have hc1F := Bool.eq_false_iff.mpr hc1
      simp only [hc1F, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega

/-- `validThreeSumBool` is computable in quasi-linear time on a multi-tape Turing machine. -/
theorem computableInO_validThreeSumBool :
    ∃ d, ComputableInO validThreeSumBool encThreeSum encBool
      (fun p => (threeSumSize p + 1) * (threeSumBitScale p + (threeSumSize p).size + 6) ^ d)
      (fun p => (threeSumSize p + 1) * (threeSumBitScale p + (threeSumSize p).size + 6) ^ d) := by
  obtain ⟨dl, hlen⟩ := computableInO_listLengthNat encNat
  obtain ⟨da, hall⟩ := computableInO_allPosNatList
  obtain ⟨dn, hnd⟩ := computableInO_decide_nodup_nat
  have heqPt : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.1 = q.2))
      (encPair encNat encNat) encBool := by fun_prop
  obtain ⟨de, _, hde⟩ := heqPt.exists_degree
  let hX := ComputableInO.fst (encList encNat) (encPair (encList encNat) (encList encNat))
  let hYZ := ComputableInO.snd (encList encNat) (encPair (encList encNat) (encList encNat))
  let hY := (ComputableInO.fst (encList encNat) (encList encNat)).comp_linear hYZ
  let hZ := (ComputableInO.snd (encList encNat) (encList encNat)).comp_linear hYZ
  let sc (p : ThreeSumInput) := threeSumBitScale p + (threeSumSize p).size + 6
  let cost (d : ℕ) (p : ThreeSumInput) := (threeSumSize p + 1) * sc p ^ d
  have hEncBnd (p : ThreeSumInput) :
      (encList encNat p.1).length ≤ 3 * (p.1.length * sc p) ∧
        (encList encNat p.2.1).length ≤ 3 * (p.2.1.length * sc p) ∧
        (encList encNat p.2.2).length ≤ 3 * (p.2.2.length * sc p) ∧
        (encThreeSum p).length ≤ 12 * ((threeSumSize p + 1) * sc p) := by
    obtain ⟨hmX, hmY, hmZ⟩ := listMax_size_lt_threeSumBitScale p
    have b (L : List ℕ) (hM : listMax Nat.size L < threeSumBitScale p) :
        (encList encNat L).length ≤ 3 * (L.length * sc p) :=
      ((length_encList_le_mul encNat L (b := listMax Nat.size L) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _ (by dsimp only [sc]; omega : _ ≤ 3 * sc p))).trans_eq
        (Nat.mul_left_comm _ _ _)
    refine ⟨b p.1 hmX, b p.2.1 hmY, b p.2.2 hmZ, ?_⟩
    change (encPair (encList encNat) (encPair (encList encNat) (encList encNat)) p).length ≤ _
    simp only [length_encPair]
    have := b p.1 hmX; have := b p.2.1 hmY; have := b p.2.2 hmZ
    have := threeSumSize_add p; have : 1 ≤ sc p := by dsimp only [sc]; omega
    nlinarith
  have upIn (d : ℕ) (hd : 1 ≤ d) (p : ThreeSumInput) :
      (encThreeSum p).length ≤ 12 * cost d p :=
    (hEncBnd p).2.2.2.trans (Nat.mul_le_mul_left 12
      (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)))
  have liftL {f : List ℕ → Bool} {df : ℕ}
      (hf : ComputableInO f (encList encNat) encBool
        (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ df)
        (fun L => (L.length + 1) * (listMax Nat.size L + 4) ^ df))
      (proj : ThreeSumInput → List ℕ)
      (hproj : ComputableInO proj encThreeSum (encList encNat)
        (fun p => (encThreeSum p).length) (fun p => (encThreeSum p).length))
      (hL : ∀ p, (proj p).length ≤ threeSumSize p)
      (hM : ∀ p, listMax Nat.size (proj p) < threeSumBitScale p) :
      ComputableInO (f ∘ proj) encThreeSum encBool (cost (df + 1)) (cost (df + 1)) := by
    refine (hf.comp hproj).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 14 0 fun p => ?_
      have hin := upIn (df + 1) (by omega) p
      have hc : ((proj p).length + 1) * (listMax Nat.size (proj p) + 4) ^ df ≤ cost (df + 1) p :=
        Nat.mul_le_mul (Nat.succ_le_succ (hL p))
          ((Nat.pow_le_pow_left (by have := hM p; dsimp only [sc]; omega) df).trans
            (Nat.pow_le_pow_right (by dsimp only [sc]; omega) (by omega)))
      change (encThreeSum p).length +
        ((proj p).length + 1) * (listMax Nat.size (proj p) + 4) ^ df ≤ 14 * cost (df + 1) p + 0
      omega
  have liftNd (proj : ThreeSumInput → List ℕ)
      (hproj : ComputableInO proj encThreeSum (encList encNat)
        (fun p => (encThreeSum p).length) (fun p => (encThreeSum p).length))
      (hL : ∀ p, (proj p).length ≤ threeSumSize p)
      (hM : ∀ p, listMax Nat.size (proj p) < threeSumBitScale p)
      (hE : ∀ p, (encList encNat (proj p)).length ≤ 3 * ((proj p).length * sc p)) :
      ComputableInO ((fun L : List ℕ => decide L.Nodup) ∘ proj) encThreeSum encBool
        (cost (dn + 1)) (cost (dn + 1)) := by
    refine (hnd.comp hproj).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (14 + 3 * 3 ^ dn) 0 fun p => ?_
      have hin := upIn (dn + 1) (by omega) p
      have he' : (encList encNat (proj p)).length + 1 ≤ 3 * ((threeSumSize p + 1) * sc p) := by
        have := hE p; have := hL p; have : 1 ≤ sc p := by dsimp only [sc]; omega
        nlinarith
      have hp : (listMax Nat.size (proj p) + 1) ^ dn ≤ 3 ^ dn * sc p ^ dn :=
        (Nat.pow_le_pow_left (by have := hM p; dsimp only [sc]; omega : _ ≤ 3 * sc p) dn).trans_eq
          (Nat.mul_pow 3 _ dn)
      have hc : ((encList encNat (proj p)).length + 1) * (listMax Nat.size (proj p) + 1) ^ dn ≤
          3 * 3 ^ dn * cost (dn + 1) p :=
        calc _ ≤ (3 * ((threeSumSize p + 1) * sc p)) * (3 ^ dn * sc p ^ dn) :=
              Nat.mul_le_mul he' hp
          _ = 3 * 3 ^ dn * ((threeSumSize p + 1) * (sc p * sc p ^ dn)) := by ring
          _ = 3 * 3 ^ dn * cost (dn + 1) p := by dsimp only [cost]; rw [pow_succ' (sc p) dn]
      change (encThreeSum p).length + _ ≤ (14 + 3 * 3 ^ dn) * cost (dn + 1) p + 0
      rw [Nat.add_mul 14 (3 * 3 ^ dn)]; omega
  have liftLen (proj : ThreeSumInput → List ℕ)
      (hproj : ComputableInO proj encThreeSum (encList encNat)
        (fun p => (encThreeSum p).length) (fun p => (encThreeSum p).length))
      (hL : ∀ p, (proj p).length ≤ threeSumSize p)
      (hM : ∀ p, listMax Nat.size (proj p) < threeSumBitScale p) :
      ComputableInO (List.length ∘ proj) encThreeSum encNat (cost (dl + 1)) (cost (dl + 1)) := by
    refine (hlen.comp hproj).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 28 0 fun p => ?_
      have hin := upIn (dl + 1) (by omega) p
      have he : (encList encNat (proj p)).length ≤ 3 * cost (dl + 1) p :=
        ((length_encList_le_mul encNat (proj p) (b := listMax Nat.size (proj p)) fun x hx => by
          rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
          (Nat.mul_le_mul (Nat.le_succ_of_le (hL p))
            ((by have := hM p; dsimp only [sc]; omega : _ ≤ 3 * sc p).trans
              (Nat.mul_le_mul_left 3 (Nat.le_self_pow (by omega) _))))).trans_eq
          (Nat.mul_left_comm _ _ _)
      have hlm : listMax (fun a => (encNat a).length) (proj p) = listMax Nat.size (proj p) := by
        simp only [length_encNat]
      have hp : (listMax (fun a => (encNat a).length) (proj p) + (proj p).length.size + 4) ^ dl ≤
          sc p ^ (dl + 1) :=
        (Nat.pow_le_pow_left
          (by rw [hlm]; have := hM p; have := Nat.size_le_size (hL p); dsimp only [sc]; omega)
          dl).trans (Nat.pow_le_pow_right (by dsimp only [sc]; omega) (by omega))
      have h1 : ((proj p).length + 1) *
          (listMax (fun a => (encNat a).length) (proj p) + (proj p).length.size + 4) ^ dl ≤
          cost (dl + 1) p :=
        Nat.mul_le_mul (by have := hL p; omega) hp
      have h2 : (listMax (fun a => (encNat a).length) (proj p) + (proj p).length.size + 4) ^ dl ≤
          cost (dl + 1) p :=
        hp.trans (Nat.le_mul_of_pos_left _ (show 0 < threeSumSize p + 1 by omega))
      dsimp only [Function.comp_apply, cost] at *; omega
  have mX : ComputableInO (fun p : ThreeSumInput => p.1) encThreeSum (encList encNat)
      (fun p => (encThreeSum p).length) (fun p => (encThreeSum p).length) := hX
  have mY : ComputableInO (fun p : ThreeSumInput => p.2.1) encThreeSum (encList encNat)
      (fun p => (encThreeSum p).length) (fun p => (encThreeSum p).length) := hY
  have mZ : ComputableInO (fun p : ThreeSumInput => p.2.2) encThreeSum (encList encNat)
      (fun p => (encThreeSum p).length) (fun p => (encThreeSum p).length) := hZ
  have hszX (p : ThreeSumInput) : p.1.length ≤ threeSumSize p := by
    have := threeSumSize_add p; omega
  have hszY (p : ThreeSumInput) : p.2.1.length ≤ threeSumSize p := by
    have := threeSumSize_add p; omega
  have hszZ (p : ThreeSumInput) : p.2.2.length ≤ threeSumSize p := by
    have := threeSumSize_add p; omega
  have hmXp (p : ThreeSumInput) := (listMax_size_lt_threeSumBitScale p).1
  have hmYp (p : ThreeSumInput) := (listMax_size_lt_threeSumBitScale p).2.1
  have hmZp (p : ThreeSumInput) := (listMax_size_lt_threeSumBitScale p).2.2
  have wlX := liftLen _ mX hszX hmXp
  have wlY := liftLen _ mY hszY hmYp
  have wlZ := liftLen _ mZ hszZ hmZp
  have liftEq (f g : ThreeSumInput → ℕ)
      (hf : ComputableInO f encThreeSum encNat (cost (dl + 1)) (cost (dl + 1)))
      (hg : ComputableInO g encThreeSum encNat (cost (dl + 1)) (cost (dl + 1)))
      (hfb : ∀ p, f p ≤ threeSumSize p) (hgb : ∀ p, g p ≤ threeSumSize p) :
      ComputableInO (fun p => decide (f p = g p)) encThreeSum encBool
        (cost (dl + de + 1)) (cost (dl + de + 1)) := by
    refine ((hde.inO.comp (hf.prod hg)).of_enc_eq fun _ => rfl).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (4 + 4 ^ de) 0 fun p => ?_
      have hu : cost (dl + 1) p ≤ cost (dl + de + 1) p :=
        Nat.mul_le_mul_left (threeSumSize p + 1)
          (Nat.pow_le_pow_right (by dsimp only [sc]; omega) (by omega))
      have hp : ((encPair encNat encNat (f p, g p)).length + 1) ^ de ≤
          4 ^ de * cost (dl + de + 1) p := by
        rw [length_encPair, length_encNat, length_encNat]
        have := Nat.size_le_size (hfb p); have := Nat.size_le_size (hgb p)
        exact (Nat.pow_le_pow_left (by dsimp only [sc]; omega : _ ≤ 4 * sc p) de).trans
          ((Nat.mul_pow 4 _ de).le.trans (Nat.mul_le_mul_left _
            ((Nat.pow_le_pow_right (by dsimp only [sc]; omega) (by omega)).trans
              (Nat.le_mul_of_pos_left _ (show 0 < threeSumSize p + 1 by omega)))))
      change cost (dl + 1) p + cost (dl + 1) p + ((encPair encNat encNat (f p, g p)).length +
        1) ^ de
        ≤ (4 + 4 ^ de) * cost (dl + de + 1) p + 0
      rw [Nat.add_mul 4 (4 ^ de)]; omega
  have andC {f g : ThreeSumInput → Bool} {d1 d2 : ℕ} (d : ℕ) (h1 : d1 ≤ d) (h2 : d2 ≤ d)
      (hf : ComputableInO f encThreeSum encBool (cost d1) (cost d1))
      (hg : ComputableInO g encThreeSum encBool (cost d2) (cost d2)) :
      ComputableInO (fun p => f p && g p) encThreeSum encBool (cost d) (cost d) := by
    refine (hf.and' hg).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 2 0 fun p => ?_
      have u1 : cost d1 p ≤ cost d p := Nat.mul_le_mul_left (threeSumSize p + 1)
        (Nat.pow_le_pow_right (by dsimp only [sc]; omega) h1)
      have u2 : cost d2 p ≤ cost d p := Nat.mul_le_mul_left (threeSumSize p + 1)
        (Nat.pow_le_pow_right (by dsimp only [sc]; omega) h2)
      change cost d1 p + cost d2 p ≤ 2 * cost d p + 0; omega
  let D := dl + de + da + dn + 2
  have w1 := andC D (by omega) (by omega) (liftEq _ _ wlX wlY hszX hszY)
    (liftEq _ _ wlY wlZ hszY hszZ)
  have w2 := andC D le_rfl (by omega) (andC D le_rfl (by omega) w1 wlX.natIsZero'.not')
    (liftL hall _ mX hszX hmXp)
  have w3 := andC D le_rfl (by omega) (andC D le_rfl (by omega) w2 (liftL hall _ mY hszY hmYp))
    (liftL hall _ mZ hszZ hmZp)
  have w4 := andC D le_rfl (by omega) (andC D le_rfl (by omega) w3
    (liftNd _ mX hszX hmXp fun p => (hEncBnd p).1))
    (liftNd _ mY hszY hmYp fun p => (hEncBnd p).2.1)
  exact ⟨D, (andC D le_rfl (by omega) w4
    (liftNd _ mZ hszZ hmZp fun p => (hEncBnd p).2.2.1)).of_enc_eq fun _ => rfl⟩

/-- Linear-factor cost term `threeSumSize p + (mPar p.1.length U + 1)^2 + 1` of `chanHeInit`. -/
def chanHeInitRawCost (p : ThreeSumInput) : ℕ :=
  threeSumSize p + (mPar p.1.length (threeSumMaxVal p) + 1) ^ 2 + 1

/-- Logarithmic-scale factor of `chanHeInit`. -/
def chanHeInitScale (p : ThreeSumInput) : ℕ :=
  let U := threeSumMaxVal p
  threeSumBitScale p + (threeSumSize p).size + U.size + (mPar p.1.length U + 1).size + 8

/-- Explicit upper bound on `chanHeInitRawCost p`. -/
theorem chanHeInitRawCost_le {p : ThreeSumInput} {R : ℕ}
    (h : threeSumSize p + (mPar p.1.length (threeSumMaxVal p) + 1) ^ 2 + 1 ≤ R) :
    chanHeInitRawCost p ≤ R := h

/-- Explicit upper bound on `chanHeInitScale p`. -/
theorem chanHeInitScale_le {p : ThreeSumInput} {S : ℕ}
    (h : threeSumBitScale p + (threeSumSize p).size + (threeSumMaxVal p).size +
      (mPar p.1.length (threeSumMaxVal p) + 1).size + 8 ≤ S) :
    chanHeInitScale p ≤ S := h

private theorem computableInPolyTime_max2 :
    ComputableInPolyTime (fun q : ℕ × ℕ => max q.1 q.2) (encPair encNat encNat) encNat :=
  (by fun_prop : ComputableInPolyTime (fun q : ℕ × ℕ => if decide (q.1 ≤ q.2) then q.2 else q.1)
    (encPair encNat encNat) encNat).of_enc_eq fun q =>
    congrArg encNat (by simp [Nat.max_def])

private theorem computableInPolyTime_twoSq :
    ComputableInPolyTime (fun m : ℕ => 2 * m ^ 2) encNat encNat :=
  (by fun_prop : ComputableInPolyTime (fun m : ℕ => 2 * (m * m)) encNat encNat).of_enc_eq
    fun m => congrArg encNat (by ring)

private theorem computableInPolyTime_iterBudget :
    ComputableInPolyTime chanHeIterBudget encNat encNat := by
  unfold chanHeIterBudget
  have h1 : ComputableInPolyTime (fun n : ℕ => 2 * Nat.log 2 n + 2) encNat encNat := by fun_prop
  have h5 : ComputableInPolyTime (fun k : ℕ => 2 * (k * k * k * k * k)) encNat encNat := by
    fun_prop
  exact (h5.comp h1).of_enc_eq fun _ => congrArg encNat (by dsimp only [Function.comp_apply]; ring)

/-- Both `chanHeIterBudget p.1.length` and `chanHeInit p` are computable within time and space
`O(chanHeInitRawCost p * chanHeInitScale p ^ d)`. -/
theorem computableInO_chanHeInitAndBudget :
    ∃ d,
      ComputableInO (fun p : ThreeSumInput => chanHeIterBudget p.1.length) encThreeSum encNat
        (fun p => chanHeInitRawCost p * chanHeInitScale p ^ d)
        (fun p => chanHeInitRawCost p * chanHeInitScale p ^ d) ∧
      ComputableInO chanHeInit encThreeSum encChanHeState
        (fun p => chanHeInitRawCost p * chanHeInitScale p ^ d)
        (fun p => chanHeInitRawCost p * chanHeInitScale p ^ d) := by
  obtain ⟨dl, hlen⟩ := computableInO_listLengthNat encNat
  obtain ⟨dmx, hmax⟩ := computableInO_maxNatList
  obtain ⟨dmx2, _, hdmx2⟩ := computableInPolyTime_max2.exists_degree
  obtain ⟨dmp, _, hdmp⟩ := computableInPolyTime_mPar.exists_degree
  obtain ⟨d2s, _, hd2s⟩ := computableInPolyTime_twoSq.exists_degree
  obtain ⟨dlb, _, hdlb⟩ := computableInPolyTime_labelBits.exists_degree
  obtain ⟨dfl, _, hdfl⟩ := computableInPolyTime_fuel.exists_degree
  obtain ⟨dib, _, hdib⟩ := computableInPolyTime_iterBudget.exists_degree
  obtain ⟨dpr, hpr⟩ := computableInO_primesList
  obtain ⟨dcP, hcastP⟩ := computableInO_mapNatToInt (fun x : ℕ => (x : ℤ)) (by fun_prop)
  obtain ⟨dcN, hcastN⟩ := computableInO_mapNatToInt (fun z : ℕ => -(z : ℤ)) (by fun_prop)
  let hX := ComputableInO.fst (encList encNat) (encPair (encList encNat) (encList encNat))
  let hYZ := ComputableInO.snd (encList encNat) (encPair (encList encNat) (encList encNat))
  let hY := (ComputableInO.fst (encList encNat) (encList encNat)).comp_linear hYZ
  let hZ := (ComputableInO.snd (encList encNat) (encList encNat)).comp_linear hYZ
  have hlenIn (p : ThreeSumInput) :
      (encPair (encList encNat) (encPair (encList encNat) (encList encNat)) p).length ≤
        12 * (chanHeInitRawCost p * chanHeInitScale p) := by
    simp only [length_encPair]
    obtain ⟨hmX, hmY, hmZ⟩ := listMax_size_lt_threeSumBitScale p
    have bnd (L : List ℕ) (hM : listMax Nat.size L < threeSumBitScale p) :
        (encList encNat L).length ≤ 3 * (L.length * chanHeInitScale p) :=
      ((length_encList_le_mul encNat L (b := listMax Nat.size L) fun x hx => by
        rw [length_encNat]; exact le_listMax (f := Nat.size) hx).trans
        (Nat.mul_le_mul_left _
          (by dsimp only [chanHeInitScale]; omega : _ ≤ 3 * chanHeInitScale p))).trans_eq
        (Nat.mul_left_comm _ _ _)
    have := bnd p.1 hmX; have := bnd p.2.1 hmY; have := bnd p.2.2 hmZ
    have hsum := threeSumSize_add p
    have hR : p.1.length + p.2.1.length + p.2.2.length + 1 ≤ chanHeInitRawCost p := by
      dsimp only [chanHeInitRawCost]; omega
    have hS : 1 ≤ chanHeInitScale p := by dsimp only [chanHeInitScale]; omega
    nlinarith
  have hn : ComputableInO (fun p : ThreeSumInput => p.1.length) encThreeSum encNat
      (fun p => chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1))
      (fun p => chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1)) := by
    refine (hlen.comp hX).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear 32 0 fun p => ?_
      have hsum := threeSumSize_add p
      have hmX := (listMax_size_lt_threeSumBitScale p).1
      have hS1 : 1 ≤ chanHeInitScale p := by dsimp only [chanHeInitScale]; omega
      have hSD : chanHeInitScale p ≤ chanHeInitScale p ^ (dl + 1) :=
        Nat.le_self_pow (by omega) _
      have hin := (hlenIn p).trans
        (Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left (chanHeInitRawCost p) hSD))
      have hX_le : (encList encNat p.1).length ≤
          (encPair (encList encNat) (encPair (encList encNat) (encList encNat)) p).length := by
        rw [length_encPair]; omega
      have hlm : listMax (fun a => (encNat a).length) p.1 = listMax Nat.size p.1 := by
        simp only [length_encNat]
      have hls : p.1.length.size ≤ (threeSumSize p).size := Nat.size_le_size (by omega)
      have hp : (listMax (fun a => (encNat a).length) p.1 + p.1.length.size + 4) ^ dl ≤
          chanHeInitScale p ^ (dl + 1) :=
        (Nat.pow_le_pow_left (by rw [hlm]; dsimp only [chanHeInitScale]; omega) dl).trans
          (Nat.pow_le_pow_right hS1 (by omega))
      have hm : (p.1.length + 1) *
          (listMax (fun a => (encNat a).length) p.1 + p.1.length.size + 4) ^ dl ≤
          chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1) :=
        Nat.mul_le_mul (by dsimp only [chanHeInitRawCost]; omega) hp
      have hm' : (listMax (fun a => (encNat a).length) p.1 + p.1.length.size + 4) ^ dl ≤
          chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1) :=
        hp.trans (Nat.le_mul_of_pos_left _ (by dsimp only [chanHeInitRawCost]; omega))
      change _ ≤ 32 * (chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1)) + 0; omega
  let dU := dmx + 2 * dmx2 + 2
  have hU : ComputableInO threeSumMaxVal encThreeSum encNat
      (fun p => chanHeInitRawCost p * chanHeInitScale p ^ dU)
      (fun p => chanHeInitRawCost p * chanHeInitScale p ^ dU) := by
    have hu := hdmx2.inO.comp ((hmax.comp hX).prod
      (hdmx2.inO.comp ((hmax.comp hY).prod (hmax.comp hZ))))
    refine (hu.of_enc_eq fun _ => rfl).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (64 + 2 * 4 ^ dmx2) 0 fun p => ?_
      have hsum := threeSumSize_add p
      obtain ⟨hmX, hmY, hmZ⟩ := listMax_size_lt_threeSumBitScale p
      have hS1 : 1 ≤ chanHeInitScale p := by dsimp only [chanHeInitScale]; omega
      have hSD : chanHeInitScale p ≤ chanHeInitScale p ^ dU :=
        Nat.le_self_pow (by dsimp only [dU]; omega) _
      have hin := (hlenIn p).trans
        (Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left (chanHeInitRawCost p) hSD))
      have bmx (L : List ℕ) (hL : L.length + 1 ≤ chanHeInitRawCost p)
          (hM : listMax Nat.size L < threeSumBitScale p) :
          (L.length + 1) * (listMax Nat.size L + 4) ^ dmx ≤
            chanHeInitRawCost p * chanHeInitScale p ^ dU :=
        Nat.mul_le_mul hL
          ((Nat.pow_le_pow_left (by dsimp only [chanHeInitScale]; omega) dmx).trans
            (Nat.pow_le_pow_right hS1 (by dsimp only [dU]; omega)))
      have b1 := bmx p.1 (by dsimp only [chanHeInitRawCost]; omega) hmX
      have b2 := bmx p.2.1 (by dsimp only [chanHeInitRawCost]; omega) hmY
      have b3 := bmx p.2.2 (by dsimp only [chanHeInitRawCost]; omega) hmZ
      have bp (a b : ℕ) (ha : a.size < threeSumBitScale p) (hb : b.size < threeSumBitScale p) :
          ((encPair encNat encNat (a, b)).length + 1) ^ dmx2 ≤
            4 ^ dmx2 * (chanHeInitRawCost p * chanHeInitScale p ^ dU) := by
        rw [length_encPair, length_encNat, length_encNat]
        exact (Nat.pow_le_pow_left
          (by dsimp only [chanHeInitScale]; omega : _ ≤ 4 * chanHeInitScale p) dmx2).trans
          ((Nat.mul_pow 4 _ dmx2).le.trans (Nat.mul_le_mul_left _
            ((Nat.pow_le_pow_right hS1 (by dsimp only [dU]; omega)).trans
              (Nat.le_mul_of_pos_left _ (by dsimp only [chanHeInitRawCost]; omega)))))
      have s1 := (maxNatList_size_le p.1).trans_lt hmX
      have s2 := (maxNatList_size_le p.2.1).trans_lt hmY
      have s3 := (maxNatList_size_le p.2.2).trans_lt hmZ
      have s23 : (max (maxNatList p.2.1) (maxNatList p.2.2)).size < threeSumBitScale p := by
        rcases le_total (maxNatList p.2.1) (maxNatList p.2.2) with h | h
        · rwa [max_eq_right h]
        · rwa [max_eq_left h]
      have p1 := bp _ _ s2 s3
      have p2 := bp _ _ s1 s23
      dsimp only [Function.comp_apply] at *
      change _ ≤ (64 + 2 * 4 ^ dmx2) * (chanHeInitRawCost p * chanHeInitScale p ^ dU) + 0
      rw [Nat.add_mul 64 (2 * 4 ^ dmx2), Nat.mul_assoc 2 (4 ^ dmx2)]; omega
  let dm := dl + dU + dmp + 2
  have hm : ComputableInO (fun p : ThreeSumInput => mPar p.1.length (threeSumMaxVal p))
      encThreeSum encNat
      (fun p => chanHeInitRawCost p * chanHeInitScale p ^ dm)
      (fun p => chanHeInitRawCost p * chanHeInitScale p ^ dm) := by
    refine (hdmp.inO.comp (hn.prod hU)).weaken ?_ ?_
    all_goals
      refine BigOLe.of_le_linear (4 + 4 ^ dmp) 0 fun p => ?_
      have hsum := threeSumSize_add p
      have hS1 : 1 ≤ chanHeInitScale p := by dsimp only [chanHeInitScale]; omega
      have h1 := Nat.mul_le_mul_left (chanHeInitRawCost p)
        (Nat.pow_le_pow_right hS1 (by dsimp only [dm]; omega : dl + 1 ≤ dm))
      have h2 := Nat.mul_le_mul_left (chanHeInitRawCost p)
        (Nat.pow_le_pow_right hS1 (by dsimp only [dm]; omega : dU ≤ dm))
      have hns : p.1.length.size ≤ (threeSumSize p).size := Nat.size_le_size (by omega)
      have hp : ((encPair encNat encNat (p.1.length, threeSumMaxVal p)).length + 1) ^ dmp ≤
          4 ^ dmp * (chanHeInitRawCost p * chanHeInitScale p ^ dm) := by
        rw [length_encPair, length_encNat, length_encNat]
        exact (Nat.pow_le_pow_left
          (by dsimp only [chanHeInitScale]; omega : _ ≤ 4 * chanHeInitScale p) dmp).trans
          ((Nat.mul_pow 4 _ dmp).le.trans (Nat.mul_le_mul_left _
            ((Nat.pow_le_pow_right hS1 (by dsimp only [dm]; omega)).trans
              (Nat.le_mul_of_pos_left _ (by dsimp only [chanHeInitRawCost]; omega)))))
      change _ ≤ (4 + 4 ^ dmp) * (chanHeInitRawCost p * chanHeInitScale p ^ dm) + 0
      rw [Nat.add_mul 4 (4 ^ dmp)]; omega
  have hN := hd2s.inO.comp hm
  have hLam := hdlb.inO.comp hU
  have hQ := hpr.comp hm
  have hF := hdfl.inO.comp hn
  have hBud := hdib.inO.comp hn
  have hL1 := hcastP.comp hX; have hL2 := hcastP.comp hY; have hL3 := hcastN.comp hZ
  have hTop := hF.prod (hL1.prod (hL2.prod hL3))
  have hNil : ComputableInO (fun _ : ThreeSumInput => ([] : List ChanHeTask))
      encThreeSum (encList encChanHeTask) (fun p => (encThreeSum p).length) (fun _ => 0) :=
    ComputableInO.constZero []
  have hFalse : ComputableInO (fun _ : ThreeSumInput => false) encThreeSum encBool
      (fun p => (encThreeSum p).length) (fun _ => 0) := ComputableInO.constZero false
  have hStk := (ComputableInO.cons' (enc := encChanHeTask)).comp_linear (hTop.prod hNil)
  have hInit := ((hFalse.prod hStk).prod ((hU.prod (hN.prod hLam)).prod hQ)).of_enc_eq
    (g := chanHeInit) fun _ => rfl
  let D := dm + d2s + dlb + dfl + dib + dpr + dcP + dcN + 2
  have up (k : ℕ) (hk : k ≤ D) (p : ThreeSumInput) :
      chanHeInitRawCost p * chanHeInitScale p ^ k ≤ chanHeInitRawCost p * chanHeInitScale p ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by dsimp only [chanHeInitScale]; omega) hk)
  have uPow (a d : ℕ) (hd : d ≤ D) (p : ThreeSumInput) (ha : a + 1 ≤ 2 * chanHeInitScale p) :
      (a + 1) ^ d ≤ 2 ^ d * (chanHeInitRawCost p * chanHeInitScale p ^ D) :=
    (Nat.pow_le_pow_left ha d).trans ((Nat.mul_pow 2 _ d).le.trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_right (by dsimp only [chanHeInitScale]; omega) hd).trans
        (Nat.le_mul_of_pos_left _ (by dsimp only [chanHeInitRawCost]; omega)))))
  refine ⟨D, hBud.weaken ?_ ?_, hInit.weaken ?_ ?_⟩
  · refine BigOLe.of_le_linear (2 + 2 ^ dib) 0 fun p => by
      have h1 := up (dl + 1) (by dsimp only [D, dm]; omega) p
      have hns : p.1.length.size ≤ (threeSumSize p).size :=
        Nat.size_le_size (by have := threeSumSize_add p; omega)
      have h2 := uPow p.1.length.size dib (by dsimp only [D]; omega) p
        (by dsimp only [chanHeInitScale]; omega)
      change chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1) +
        ((encNat p.1.length).length + 1) ^ dib ≤ _
      rw [length_encNat, Nat.add_mul 2 (2 ^ dib)]; omega
  · refine BigOLe.of_le_linear (2 + 2 ^ dib) 0 fun p => by
      have h1 := up (dl + 1) (by dsimp only [D, dm]; omega) p
      have hns : p.1.length.size ≤ (threeSumSize p).size :=
        Nat.size_le_size (by have := threeSumSize_add p; omega)
      have h2 := uPow p.1.length.size dib (by dsimp only [D]; omega) p
        (by dsimp only [chanHeInitScale]; omega)
      change chanHeInitRawCost p * chanHeInitScale p ^ (dl + 1) +
        ((encNat p.1.length).length + 1) ^ dib ≤ _
      rw [length_encNat, Nat.add_mul 2 (2 ^ dib)]; omega
  all_goals
    refine BigOLe.of_le_linear (256 + 2 ^ dfl + 2 ^ d2s + 2 ^ dlb) 0 fun p => ?_
    have hsum := threeSumSize_add p
    obtain ⟨hmX, hmY, hmZ⟩ := listMax_size_lt_threeSumBitScale p
    have hSD : chanHeInitScale p ≤ chanHeInitScale p ^ D :=
      Nat.le_self_pow (by dsimp only [D]; omega) _
    have hin := (hlenIn p).trans
      (Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left (chanHeInitRawCost p) hSD))
    have u_n := up (dl + 1) (by dsimp only [D, dm]; omega) p
    have u_U := up dU (by dsimp only [D, dm]; omega) p
    have u_m := up dm (by dsimp only [D]; omega) p
    have hns : p.1.length.size ≤ (threeSumSize p).size := Nat.size_le_size (by omega)
    let Uv := threeSumMaxVal p
    let mv := mPar p.1.length Uv
    have p_fl := uPow (encNat p.1.length).length dfl (by dsimp only [D]; omega) p
      (by rw [length_encNat]; dsimp only [chanHeInitScale]; omega)
    have p_2s := uPow (encNat mv).length d2s (by dsimp only [D]; omega) p
      (by rw [length_encNat]; have := Nat.size_le_size (by omega : mv ≤ mv + 1)
          dsimp only [mv, Uv] at *; dsimp only [chanHeInitScale]; omega)
    have p_lb := uPow (encNat Uv).length dlb (by dsimp only [D]; omega) p
      (by rw [length_encNat]; dsimp only [Uv, chanHeInitScale]; omega)
    have p_pr_pow : ((mv + 1).size + 1) ^ dpr ≤ chanHeInitScale p ^ D :=
      (Nat.pow_le_pow_left (by dsimp only [mv, Uv, chanHeInitScale]; omega) dpr).trans
        (Nat.pow_le_pow_right (by dsimp only [chanHeInitScale]; omega)
          (by dsimp only [D]; omega))
    have p_pr_t : (mv + 1) ^ 2 * ((mv + 1).size + 1) ^ dpr ≤
        chanHeInitRawCost p * chanHeInitScale p ^ D :=
      Nat.mul_le_mul (by dsimp only [chanHeInitRawCost, mv, Uv]; omega) p_pr_pow
    have p_pr_s : (mv + 1) * ((mv + 1).size + 1) ^ dpr ≤
        chanHeInitRawCost p * chanHeInitScale p ^ D :=
      Nat.mul_le_mul (by have : mv + 1 ≤ (mv + 1) ^ 2 := Nat.le_self_pow (by decide) _
                         dsimp only [mv, Uv] at *; dsimp only [chanHeInitRawCost]; omega) p_pr_pow
    have bMap (L : List ℕ) (dc : ℕ) (hdc : dc ≤ D) (hL : L.length + 1 ≤ chanHeInitRawCost p)
        (hM : listMax Nat.size L < threeSumBitScale p) :
        (L.length + 1) * (listMax Nat.size L + 4) ^ dc ≤
          chanHeInitRawCost p * chanHeInitScale p ^ D :=
      Nat.mul_le_mul hL
        ((Nat.pow_le_pow_left (by dsimp only [chanHeInitScale]; omega) dc).trans
          (Nat.pow_le_pow_right (by dsimp only [chanHeInitScale]; omega) hdc))
    have bL1 : (p.1.length + 1) * (listMax Nat.size p.1 + 4) ^ dcP ≤
        chanHeInitRawCost p * chanHeInitScale p ^ D :=
      bMap p.1 dcP (by dsimp only [D]; omega) (by dsimp only [chanHeInitRawCost]; omega) hmX
    have bL2 : (p.2.1.length + 1) * (listMax Nat.size p.2.1 + 4) ^ dcP ≤
        chanHeInitRawCost p * chanHeInitScale p ^ D :=
      bMap p.2.1 dcP (by dsimp only [D]; omega) (by dsimp only [chanHeInitRawCost]; omega) hmY
    have bL3 : (p.2.2.length + 1) * (listMax Nat.size p.2.2 + 4) ^ dcN ≤
        chanHeInitRawCost p * chanHeInitScale p ^ D :=
      bMap p.2.2 dcN (by dsimp only [D]; omega) (by dsimp only [chanHeInitRawCost]; omega) hmZ
    have hin_eq : (encThreeSum p).length =
        2 * (encList encNat p.1).length + 1 +
          (encPair (encList encNat) (encList encNat) p.2).length := length_encPair p
    have hyz_eq : (encPair (encList encNat) (encList encNat) p.2).length = _ := length_encPair p.2
    have hin_rfl : (encThreeSum p).length =
        (encPair (encList encNat) (encPair (encList encNat) (encList encNat)) p).length := rfl
    dsimp only [Function.comp_apply, mv, Uv] at *
    change _ ≤ (256 + 2 ^ dfl + 2 ^ d2s + 2 ^ dlb) * (chanHeInitRawCost p * chanHeInitScale p ^ D) +
      0
    rw [Nat.add_mul (256 + 2 ^ dfl + 2 ^ d2s) (2 ^ dlb),
        Nat.add_mul (256 + 2 ^ dfl) (2 ^ d2s), Nat.add_mul 256 (2 ^ dfl)]; omega

/-! ### Uniform encoded-state and per-round cost bounds along trajectories -/

/-- Uniform upper bound on the encoded worklist state length at every step on a valid input. -/
def chanHeValidStateBnd (p : ThreeSumInput) : ℕ :=
  if validThreeSumBool p then
    let n := p.1.length; let U := threeSumMaxVal p; let m := mPar n U
    400 * (fuel n + 1) * (n + m + 1) * (n.size + U.size + (m + 1).size + 16)
  else 0

/-- Upper bound on a single `ConvThreeSum` oracle call on a packed array of length `8 * m^2`. -/
noncomputable def chanHeConvCap (cConv : ℕ) (ε₁ : ℝ) (e n U : ℕ) : ℕ :=
  Nat.ceil ((cConv : ℝ) * ((8 * mPar n U ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) *
    ((U.size + 10 : ℕ) : ℝ) ^ e + cConv) + 1

/-- Uniform upper bound on `chanHeStepCost tConv ds` at every step on a valid input. -/
noncomputable def chanHeValidRoundBnd (cConv : ℕ) (ε₁ : ℝ) (e ds : ℕ) (p : ThreeSumInput) : ℕ :=
  if validThreeSumBool p then
    let n := p.1.length; let U := threeSumMaxVal p; let m := mPar n U
    let sc := 32 * (n.size + U.size + (m + 1).size + 16)
    chanHeValidStateBnd p + (m + 2) * (m + 3 * n + 2) * sc ^ ds +
      (2 * m ^ 2 + 3 * n + 1) * sc ^ ds + chanHeConvCap cConv ε₁ e n U + 4 * (n + 1) * sc ^ ds
  else 0

/-- Every iterate `(chanHeStep gConv)^[j] (chanHeInit p)` on a valid input has encoded length
at most `chanHeValidStateBnd p`. -/
theorem encChanHeState_valid_le {gConv : List ℕ → Bool}
    (hg_iff : ∀ A, A ∈ ConvThreeSum ↔ gConv A = true) {p : ThreeSumInput}
    (hv : validThreeSumBool p = true) (j : ℕ) :
    (encChanHeState ((chanHeStep gConv)^[j] (chanHeInit p))).length ≤ chanHeValidStateBnd p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hroot⟩ := valid_root_inv hv
  obtain ⟨hctx, hinv, hbnd, _, _⟩ := iterate_chanHeStep_inv hg_iff hroot j
  set st := (chanHeStep gConv)^[j] (chanHeInit p)
  have hstk_len : st.1.2.length ≤ 2 * fuel p.1.length + 1 := by
    have := hbnd.length_le; rwa [List.length_map] at this
  let n := p.1.length
  let U := threeSumMaxVal p
  let m := mPar n U
  let sc := n.size + U.size + (m + 1).size + 16
  simp only [chanHeValidStateBnd, hv, ↓reduceIte]
  have htask_len : ∀ t ∈ st.1.2, (encChanHeTask t).length ≤ 44 * ((n + 1) * sc) := by
    intro t ht; have hi := hinv t ht
    have bL (L : List ℤ) (hl : L.length ≤ n) (hb : Bdd U L.toFinset) :
        (encList encIntBin L).length ≤ 3 * (n * sc) := by
      have h1 := length_encList_le_mul encIntBin L (b := U.size + 1) fun z hz =>
        (le_listMax (f := fun w => (encIntBin w).length) hz).trans (bdd_size_int hb)
      calc _ ≤ L.length * (3 * sc) :=
            h1.trans (Nat.mul_le_mul_left _ (by dsimp only [sc]; omega))
        _ ≤ n * (3 * sc) := Nat.mul_le_mul_right _ hl
        _ = 3 * (n * sc) := Nat.mul_left_comm _ _ _
    have b1 := bL t.2.1 hi.len₁ hi.bdd₁
    have b2 := bL t.2.2.1 hi.len₂ hi.bdd₂
    have b3 := bL t.2.2.2 hi.len₃ hi.bdd₃
    have hfs : t.1.size ≤ sc := by
      have hf := fuel_le_size n
      have h3 := Nat.size_le.mpr (show fuel n < 2 ^ (n.size + 4) by
        have := Nat.lt_two_pow_self (n := n.size); rw [Nat.pow_add]
        have : 2 ^ 4 = 16 := by decide
        omega)
      have := (Nat.size_le_size hi.fuel_le).trans h3
      dsimp only [sc]; omega
    have hsc1 : 1 ≤ sc := by dsimp only [sc]; omega
    change (encPair encNat (encPair (encList encIntBin)
      (encPair (encList encIntBin) (encList encIntBin))) t).length ≤ _
    simp only [length_encPair, length_encNat]; nlinarith
  have hstk_enc : (encList encChanHeTask st.1.2).length ≤
      90 * (2 * fuel n + 1) * ((n + 1) * sc) := by
    have h1 := length_encList_le_mul encChanHeTask st.1.2 (b := 44 * ((n + 1) * sc)) htask_len
    have h2 : 2 * (44 * ((n + 1) * sc)) + 1 ≤ 90 * ((n + 1) * sc) := by
      have : 1 ≤ sc := by dsimp only [sc]; omega
      nlinarith
    calc _ ≤ st.1.2.length * (90 * ((n + 1) * sc)) := h1.trans (Nat.mul_le_mul_left _ h2)
      _ ≤ (2 * fuel n + 1) * (90 * ((n + 1) * sc)) := Nat.mul_le_mul_right _ hstk_len
      _ = 90 * (2 * fuel n + 1) * ((n + 1) * sc) := by ring
  have hctx_enc : (encChanHeCtx st.2).length ≤ 12 * ((m + 1) * sc) := by
    rw [show st.2 = ((U, (2 * m ^ 2, labelBits U)), primesList m) from hctx]
    simp only [encChanHeCtx, length_encPair, length_encNat]
    have hQ := length_encList_le_mul encNat (primesList m) (b := (m + 1).size) fun q hq => by
      rw [length_encNat]
      rw [primesList_eq_filter_range, List.mem_filter] at hq
      exact Nat.size_le_size (List.mem_range.mp hq.1).le
    have hQ' : (encList encNat (primesList m)).length ≤ 3 * ((m + 1) * sc) :=
      ((hQ.trans (Nat.mul_le_mul_left _ (by dsimp only [sc]; omega : _ ≤ 3 * sc))).trans
        (Nat.mul_le_mul_right _ (length_primesList_le m))).trans_eq (Nat.mul_left_comm _ _ _)
    have hNsz : (2 * m ^ 2).size ≤ 2 * (m + 1).size + 2 := by
      refine Nat.size_le.mpr ?_
      have hlt := Nat.lt_size_self (m + 1)
      have h1 : 2 * m ^ 2 < 2 * (m + 1) * (m + 1) := by nlinarith
      have h2 : 2 * (m + 1) * (m + 1) ≤ 2 ^ 1 * 2 ^ (m + 1).size * 2 ^ (m + 1).size :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlt.le) hlt.le
      simp only [← Nat.pow_add] at h2
      have hp := Nat.pow_lt_pow_right (a := 2) (by decide)
        (show 1 + (m + 1).size + (m + 1).size < 2 * (m + 1).size + 2 by omega)
      linarith
    have hLsz : (labelBits U).size ≤ U.size + 2 := (size_le_self _).trans (labelBits_le_size U)
    have hhead : 2 * U.size + 1 + (2 * (2 * m ^ 2).size + 1 + (labelBits U).size) ≤ 4 * sc := by
      dsimp only [sc]; omega
    nlinarith
  have hbl : (encBool st.1.1).length = 1 := by cases st.1.1 <;> rfl
  simp only [encChanHeState, length_encPair, hbl]
  change 2 * (2 * 1 + 1 + (encList encChanHeTask st.1.2).length) + 1 +
    (encChanHeCtx st.2).length ≤ 400 * (fuel n + 1) * (n + m + 1) * sc
  have hsc1 : 1 ≤ sc := by dsimp only [sc]; omega
  have hstep1 : 2 * (90 * (2 * fuel n + 1) * ((n + 1) * sc)) ≤
      360 * (fuel n + 1) * ((n + m + 1) * sc) := by
    have : (n + 1) * sc ≤ (n + m + 1) * sc := Nat.mul_le_mul_right sc (by omega)
    nlinarith
  have hstep2 : 12 * ((m + 1) * sc) ≤ 12 * (fuel n + 1) * ((n + m + 1) * sc) := by
    have h1 : (m + 1) * sc ≤ (n + m + 1) * sc := Nat.mul_le_mul_right sc (by omega)
    have h2 : (n + m + 1) * sc ≤ (fuel n + 1) * ((n + m + 1) * sc) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    nlinarith
  have hpos_prod : 1 ≤ (fuel n + 1) * ((n + m + 1) * sc) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (by omega) hsc1)
  nlinarith

/-- Every iterate `(chanHeStep gConv)^[j] (chanHeInit p)` on a valid input satisfies
`chanHeStepCost tConv ds st ≤ chanHeValidRoundBnd cConv ε₁ e ds p`. -/
theorem chanHeStepCost_valid_le {gConv : List ℕ → Bool} {tConv : List ℕ → ℕ} {cConv e ds : ℕ}
    {ε₁ : ℝ} (hg_iff : ∀ A, A ∈ ConvThreeSum ↔ gConv A = true)
    (htConv : ∀ A : List ℕ,
      (tConv A : ℝ) ≤ (cConv : ℝ) * ((A.length : ℝ) ^ (2 - ε₁) *
        (convThreeSumBitScale A : ℝ) ^ e) + cConv)
    {p : ThreeSumInput} (hv : validThreeSumBool p = true) (j : ℕ) :
    chanHeStepCost tConv ds ((chanHeStep gConv)^[j] (chanHeInit p)) ≤
      chanHeValidRoundBnd cConv ε₁ e ds p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hroot⟩ := valid_root_inv hv
  obtain ⟨hctx, hinv, _, _, _⟩ := iterate_chanHeStep_inv hg_iff hroot j
  have hst_bnd := encChanHeState_valid_le hg_iff hv j
  set st := (chanHeStep gConv)^[j] (chanHeInit p)
  let n := p.1.length
  let U := threeSumMaxVal p
  let m := mPar n U
  let sc0 := n.size + U.size + (m + 1).size + 16
  let sc := 32 * sc0
  simp only [chanHeValidRoundBnd, hv, ↓reduceIte]
  unfold chanHeStepCost
  rw [show st.2 = ((U, (2 * m ^ 2, labelBits U)), primesList m) from hctx]; dsimp only
  let t := st.1.2.headD defaultWTask
  have ht_inv : TaskInv n U (fuel n) t := by
    cases hs : st.1.2 with
    | nil =>
      dsimp only [t]; rw [hs]
      exact ⟨List.nodup_nil, List.nodup_nil, List.nodup_nil, Nat.zero_le _, Nat.zero_le _,
        Nat.zero_le _, fun _ h => False.elim (List.not_mem_nil (List.mem_toFinset.mp h)),
        fun _ h => False.elim (List.not_mem_nil (List.mem_toFinset.mp h)),
        fun _ h => False.elim (List.not_mem_nil (List.mem_toFinset.mp h)), Nat.zero_le _⟩
    | cons a as =>
      dsimp only [t]; rw [hs]
      exact hinv a (by change a ∈ st.1.2; rw [hs]; exact List.mem_cons_self ..)
  have hQlm : listMax Nat.size (primesList m) ≤ (m + 1).size := listMax_le fun q hq => by
    rw [primesList_eq_filter_range, List.mem_filter] at hq
    exact Nat.size_le_size (List.mem_range.mp hq.1).le
  have hQlen : (primesList m).length ≤ m + 1 := length_primesList_le m
  let M := modulusList (primesList m) (labelBits U) t.2.1 t.2.2.1 t.2.2.2
  have hMsz : M.size ≤ 2 * (m + 1).size + 3 := (modulusList_size_le _ _ _ _ _).trans (by omega)
  have hNsz : (2 * m ^ 2).size ≤ 2 * (m + 1).size + 2 := by
    refine Nat.size_le.mpr ?_
    have hlt := Nat.lt_size_self (m + 1)
    have h1 : 2 * m ^ 2 < 2 * (m + 1) * (m + 1) := by nlinarith
    have h2 : 2 * (m + 1) * (m + 1) ≤ 2 ^ 1 * 2 ^ (m + 1).size * 2 ^ (m + 1).size :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlt.le) hlt.le
    simp only [← Nat.pow_add] at h2
    have hp := Nat.pow_lt_pow_right (a := 2) (by decide)
      (show 1 + (m + 1).size + (m + 1).size < 2 * (m + 1).size + 2 by omega)
    linarith
  have hml : modLen (primesList m, (labelBits U, t.2)) ≤ m + 3 * n + 2 :=
    modLen_le (x := (primesList m, (labelBits U, t.2)))
      (by dsimp only; have := ht_inv.len₁; have := ht_inv.len₂; have := ht_inv.len₃; omega)
  have hml_sz : (modLen (primesList m, (labelBits U, t.2))).size ≤ sc0 := by
    refine (Nat.size_le_size hml).trans (Nat.size_le.mpr ?_)
    have ha : m + 1 ≤ 2 ^ ((m + 1).size + n.size) :=
      (Nat.lt_size_self (m + 1)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hb : n ≤ 2 ^ ((m + 1).size + n.size) :=
      (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have h3 : m + 3 * n + 2 < 2 ^ (((m + 1).size + n.size) + 4) := by
      have hp : 2 ^ (((m + 1).size + n.size) + 4) = 2 ^ ((m + 1).size + n.size) * 16 :=
        Nat.pow_add 2 _ 4
      have h1 : 1 ≤ 2 ^ ((m + 1).size + n.size) := Nat.one_le_two_pow
      omega
    exact h3.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [sc0]; omega))
  have hms : modScale (primesList m, (labelBits U, t.2)) + 1 ≤ sc :=
    (Nat.add_le_add_right (modScale_le (x := (primesList m, (labelBits U, t.2))) hQlm
      (Nat.size_le_size hQlen) ((size_le_self _).trans (labelBits_le_size U))
      (bdd_size_int ht_inv.bdd₁) (bdd_size_int ht_inv.bdd₂) (bdd_size_int ht_inv.bdd₃)
      hml_sz) 1).trans (by dsimp only [sc, sc0]; omega)
  have hmod_term := Nat.mul_le_mul (Nat.mul_le_mul (by omega : (primesList m).length + 1 ≤ m + 2)
    hml) (Nat.pow_le_pow_left hms ds)
  have hpl : packLen ((U, (2 * m ^ 2, M)), t.2) ≤ 2 * m ^ 2 + 3 * n + 1 :=
    packLen_le (x := ((U, (2 * m ^ 2, M)), t.2))
      (by dsimp only; have := ht_inv.len₁; have := ht_inv.len₂; have := ht_inv.len₃; omega)
  have hpl_sz : (packLen ((U, (2 * m ^ 2, M)), t.2)).size ≤ 3 * sc0 := by
    refine (Nat.size_le_size hpl).trans (Nat.size_le.mpr ?_)
    have ha : 2 * m ^ 2 ≤ 2 ^ (2 * (m + 1).size + n.size + 2) :=
      (Nat.size_le.mp hNsz).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hb : n ≤ 2 ^ (2 * (m + 1).size + n.size + 2) :=
      (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have h3 : 2 * m ^ 2 + 3 * n + 1 < 2 ^ ((2 * (m + 1).size + n.size + 2) + 3) := by
      have hp : 2 ^ ((2 * (m + 1).size + n.size + 2) + 3) =
        2 ^ (2 * (m + 1).size + n.size + 2) * 8 := Nat.pow_add 2 _ 3
      have h1 : 1 ≤ 2 ^ (2 * (m + 1).size + n.size + 2) := Nat.one_le_two_pow
      omega
    exact h3.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [sc0]; omega))
  have hps : packScale ((U, (2 * m ^ 2, M)), t.2) + 1 ≤ sc :=
    (Nat.add_le_add_right (packScale_le (x := ((U, (2 * m ^ 2, M)), t.2)) le_rfl hNsz hMsz
      (bdd_size_int ht_inv.bdd₁) (bdd_size_int ht_inv.bdd₂) (bdd_size_int ht_inv.bdd₃)
      hpl_sz) 1).trans (by dsimp only [sc, sc0]; omega)
  have hpack_term := Nat.mul_le_mul hpl (Nat.pow_le_pow_left hps ds)
  have hconv_term : (if st.1.1 || st.1.2.isEmpty || wTaskSkip t then 0
      else tConv (oneArrayList U (2 * m ^ 2) M t.2.1 t.2.2.1 t.2.2.2)) ≤
        chanHeConvCap cConv ε₁ e n U := by
    split_ifs
    · exact Nat.zero_le _
    · let arr := oneArrayList U (2 * m ^ 2) M t.2.1 t.2.2.1 t.2.2.2
      have hM_pos : 0 < M := modulusList_pos (fun q hq => by
        rw [primesList_eq_filter_range, List.mem_filter, decide_eq_true_eq] at hq
        exact hq.2.pos) _ _ _ _
      have harr_len : arr.length = 8 * m ^ 2 := by
        dsimp only [arr]; rw [length_oneArrayList]; ring
      have harr_bs : convThreeSumBitScale arr ≤ U.size + 10 :=
        convThreeSumBitScale_le fun a ha => by
          have hub := (oneArrayList_pos_and_le hM_pos ht_inv.nd₁ ht_inv.nd₂ ht_inv.nd₃
            ht_inv.bdd₁ ht_inv.bdd₂ ht_inv.bdd₃ ha).2
          exact Nat.size_le.mpr (by
            have := Nat.lt_size_self U
            have hp : 2 ^ (U.size + 9) = 2 ^ U.size * 512 := Nat.pow_add 2 U.size 9
            omega)
      have ht0 := htConv arr
      rw [harr_len] at ht0
      have hbR : (convThreeSumBitScale arr : ℝ) ^ e ≤ ((U.size + 10 : ℕ) : ℝ) ^ e :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast harr_bs) e
      have hleR : (tConv arr : ℝ) ≤
          (cConv : ℝ) * ((8 * m ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) * ((U.size + 10 : ℕ) : ℝ) ^ e +
            cConv := by
        have := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbR
            (by positivity : (0 : ℝ) ≤ ((8 * m ^ 2 : ℕ) : ℝ) ^ (2 - ε₁)))
          (Nat.cast_nonneg cConv)
        linarith
      have hle_ceil : tConv arr ≤
          Nat.ceil ((cConv : ℝ) * ((8 * m ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) *
            ((U.size + 10 : ℕ) : ℝ) ^ e + cConv) := by
        exact_mod_cast hleR.trans (Nat.le_ceil _)
      exact hle_ceil.trans (Nat.le_succ _)
  have bHeavy (L : List ℤ) (hl : L.length ≤ n) (hb : Bdd U L.toFinset) :
      (L.length + 1) * (heavyScale (M, L) + 1) ^ ds ≤ (n + 1) * sc ^ ds :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left
      ((Nat.add_le_add_right (heavyScale_le (p := (M, L)) hMsz (bdd_size_int hb)
        (Nat.size_le_size hl)) 1).trans (by dsimp only [sc, sc0]; omega)) ds)
  have hh1 := bHeavy t.2.1 ht_inv.len₁ ht_inv.bdd₁
  have hh2 := bHeavy t.2.2.1 ht_inv.len₂ ht_inv.bdd₂
  have hh3 := bHeavy t.2.2.2 ht_inv.len₃ ht_inv.bdd₃
  have hfpr : (t.1.size + 1) ^ ds ≤ (n + 1) * sc ^ ds := by
    have hf := fuel_le_size n
    have h3 := Nat.size_le.mpr (show fuel n < 2 ^ (n.size + 4) by
      have := Nat.lt_two_pow_self (n := n.size)
      have hp : 2 ^ (n.size + 4) = 2 ^ n.size * 16 := Nat.pow_add 2 n.size 4
      omega)
    have := (Nat.size_le_size ht_inv.fuel_le).trans h3
    exact (Nat.pow_le_pow_left (by dsimp only [sc, sc0]; omega) ds).trans
      (Nat.le_mul_of_pos_left _ (show 0 < n + 1 by omega))
  have h4 : 4 * (n + 1) * sc ^ ds =
      (n + 1) * sc ^ ds + (n + 1) * sc ^ ds + (n + 1) * sc ^ ds + (n + 1) * sc ^ ds := by ring
  dsimp only [t, M, m, U, n, sc, sc0] at *; omega

/-- Explicit upper bound on `chanHeValidStateBnd p` for valid inputs. -/
theorem chanHeValidStateBnd_le {p : ThreeSumInput} (hv : validThreeSumBool p = true) {B : ℕ}
    (h : let n := p.1.length; let U := threeSumMaxVal p; let m := mPar n U
      400 * (fuel n + 1) * (n + m + 1) * (n.size + U.size + (m + 1).size + 16) ≤ B) :
    chanHeValidStateBnd p ≤ B := by
  unfold chanHeValidStateBnd; simp only [hv, ↓reduceIte]; exact h

/-- Explicit upper bound on `chanHeConvCap cConv ε₁ e n U` as a real number. -/
theorem chanHeConvCap_cast_le (cConv : ℕ) {ε₁ : ℝ} (e n U : ℕ) :
    (chanHeConvCap cConv ε₁ e n U : ℝ) ≤
      (cConv : ℝ) * ((8 * mPar n U ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) *
        ((U.size + 10 : ℕ) : ℝ) ^ e + (cConv + 2 : ℝ) := by
  unfold chanHeConvCap
  have hcl := (Nat.ceil_lt_add_one
    (by positivity : (0 : ℝ) ≤ (cConv : ℝ) * ((8 * mPar n U ^ 2 : ℕ) : ℝ) ^ (2 - ε₁) *
      ((U.size + 10 : ℕ) : ℝ) ^ e + cConv)).le
  rw [Nat.cast_add, Nat.cast_one]; linarith

/-- Explicit evaluation of `chanHeValidRoundBnd` on a valid input. -/
theorem chanHeValidRoundBnd_of_valid (cConv : ℕ) (ε₁ : ℝ) (e ds : ℕ) {p : ThreeSumInput}
    (hv : validThreeSumBool p = true) :
    chanHeValidRoundBnd cConv ε₁ e ds p =
      let n := p.1.length; let U := threeSumMaxVal p; let m := mPar n U
      let sc := 32 * (n.size + U.size + (m + 1).size + 16)
      chanHeValidStateBnd p + (m + 2) * (m + 3 * n + 2) * sc ^ ds +
        (2 * m ^ 2 + 3 * n + 1) * sc ^ ds + chanHeConvCap cConv ε₁ e n U +
        4 * (n + 1) * sc ^ ds := by
  unfold chanHeValidRoundBnd; simp only [hv, ↓reduceIte]

end CslibFrontier.Complexity
