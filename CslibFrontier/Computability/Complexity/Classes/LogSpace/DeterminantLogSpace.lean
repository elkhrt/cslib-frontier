/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.DeterminantWorkPhase

import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Buntrock--Damm--Hertrampf--Meinel Theorem: $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}} \subseteq
\mathrm{DET}_k$

This module proves of Buntrock, Damm, Hertrampf, and Meinel: for every integer
$k \ge 2$, relativized logarithmic space $\mathrm{L}^O$ is contained in $\mathrm{DET}_k$ whenever
$O \in \mathrm{DET}_k$ (`Cslib.Complexity.LOracle_subset_DETkOn`), and hence
$\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}} \subseteq \mathrm{DET}_k \subseteq \mathrm{DET}$
(`Cslib.Complexity.LModL_subset_DETkOn`,
`Cslib.Complexity.LModL_subset_DETOn`), under standard Lean axioms.

## Main results

* `Cslib.Complexity.LOracle_subset_DETkOn`: for every $k \ge 2$ and
  $O \in \mathrm{DET}_k$, $\mathrm{L}^O \subseteq \mathrm{DET}_k$.
* `Cslib.Complexity.LModL_subset_DETkOn`,
  `Cslib.Complexity.LModL_encBits_subset_DETk`,
  `Cslib.Complexity.LModL_subset_DETOn`: **Buntrock--Damm--Hertrampf--Meinel theorem**
  — for every $k \ge 2$, $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}} \subseteq \mathrm{DET}_k \subseteq
  \mathrm{DET}$.
-/

public section

namespace Cslib.Complexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

section BuntrockTheorem

private theorem exists_viewRep_fits_radix {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (c : ℕ) (w : List Bool)
    (hspace : ∀ t, RunPath.space (M.runPath O w t).toRunPath ≤ c * (Nat.log2 w.length + 1))
    (t : ℕ) :
    ∃ view : FiniteCfg k_tapes Bool State,
      ViewRep view (M.runCfg O w t).1 ∧
      Fits (radix (radixExponent State c) w.length) (registers view) := by
  let D : ℕ := radixExponent State c
  let n := w.length
  let Bn := radix D n
  obtain ⟨view, _, hrep⟩ :=
    exists_viewStep_of_runPath (M.runPath O w t).toRunPath (M.runPath O w t).head_eq
  rw [M.runPath_last] at hrep
  have hD : 2 ≤ D := by simp only [D, radixExponent]; omega
  have hbase : w.length + 2 ≤ Bn :=
    calc w.length + 2 = (w.length + 2) ^ 1 := (pow_one _).symm
      _ ≤ Bn := Nat.pow_le_pow_right (by omega) (by omega)
  have hc_lt : Fintype.card (Option State) < Bn :=
    Nat.lt_of_succ_lt (card_succ_lt_radix c n)
  have h3_lt : 3 < Bn :=
    calc 3 < 2 ^ 2 := by decide
      _ ≤ (w.length + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ Bn := Nat.pow_le_pow_right (by omega) hD
  have hS : 3 ^ (4 * (c * (Nat.log2 n + 1)) + 1) ≤ Bn := by
    have hlog : 2 ^ (Nat.log2 n + 1) ≤ (n + 2) ^ 2 :=
      (Nat.two_pow_log2_succ_le n).trans (by nlinarith)
    calc 3 ^ (4 * (c * (Nat.log2 n + 1)) + 1)
        ≤ 4 ^ (4 * (c * (Nat.log2 n + 1)) + 1) := Nat.pow_le_pow_left (by decide) _
      _ = 2 ^ (8 * (c * (Nat.log2 n + 1)) + 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
          exact congrArg (2 ^ ·) (by ring)
      _ ≤ 2 ^ ((8 * c + 2) * (Nat.log2 n + 1)) :=
          Nat.pow_le_pow_right (by decide) (by nlinarith)
      _ = (2 ^ (Nat.log2 n + 1)) ^ (8 * c + 2) := by rw [← pow_mul, mul_comm]
      _ ≤ ((n + 2) ^ 2) ^ (8 * c + 2) := Nat.pow_le_pow_left hlog _
      _ ≤ Bn := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by omega) (by simp only [D, radixExponent]; omega)
  have hfit : Fits Bn (registers view) := by
    intro reg
    cases reg with
    | inputPos => exact view.inputPos.isLt.trans_le (hrep.input ▸ hbase)
    | control => exact (Fintype.equivFin (Option State) view.state).isLt.trans hc_lt
    | output => exact (outputCode_lt _).trans h3_lt
    | head _ => exact (symbolCode_lt _).trans h3_lt
    | left tape | right tape =>
      have hle_tape : RunPath.spaceUsedByTape (M.runPath O w t).toRunPath tape ≤
          c * (Nat.log2 n + 1) :=
        (Finset.single_le_sum
          (f := fun i ↦ RunPath.spaceUsedByTape (M.runPath O w t).toRunPath i)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ tape)).trans (hspace t)
      obtain ⟨hhead, hcells⟩ := RunPath.natAbs_lt_spaceUsedByTape (M.runPath O w t).toRunPath
        (fun i z ↦ by rw [(M.runPath O w t).head_eq]; simp [Cfg.init])
        (fun i ↦ by rw [(M.runPath O w t).head_eq]; rfl) tape
      have hlast_rep : (view.workTapes tape).Represents
          ((M.runPath O w t).last.workTapes tape)
          ((M.runPath O w t).last.workTapePos tape) := by
        rw [M.runPath_last]; exact hrep.workTapes tape
      have hbi : (view.workTapes tape).spaceUsed ≤ 4 * (c * (Nat.log2 n + 1)) + 1 :=
        hlast_rep.spaceUsed_le (hhead.trans_le hle_tape)
          fun z hz ↦ (hcells z hz).trans_le hle_tape
      simp only [Cslib.Turing.BiTape.spaceUsed] at hbi
      exact (stackCode_lt _).trans_le
        ((Nat.pow_le_pow_right (Nat.succ_pos 2) (by omega)).trans hS)
  exact ⟨view, hrep, hfit⟩

attribute [local irreducible] vertexBound radix radixExponent

noncomputable section Simulation

private theorem simInit_viewRep_fits {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (hview_run : ∀ t, ∃ view : FiniteCfg k_tapes Bool State,
      ViewRep view (M.runCfg O w t).1 ∧ Fits Bn (registers view)) :
    ViewRep (M.envelopeNTM.initView w) (M.runCfg O w 0).1 ∧
      Fits Bn (registers (M.envelopeNTM.initView w)) := by
  obtain ⟨view₀, hrep₀, hfit₀⟩ := hview_run 0
  have hview₀_eq : view₀ = M.envelopeNTM.initView w := by
    apply coreCode_injective (hrep₀.input.trans rfl)
    change encCore (view₀.inputPos.val, view₀.state, view₀.workTapes, view₀.output) =
      encCore ((M.envelopeNTM.initView w).inputPos.val, (M.envelopeNTM.initView w).state,
        (M.envelopeNTM.initView w).workTapes, (M.envelopeNTM.initView w).output)
    have hp : view₀.inputPos.val = (M.envelopeNTM.initView w).inputPos.val := hrep₀.inputPos
    have hs : view₀.state = (M.envelopeNTM.initView w).state := hrep₀.state
    have ho : view₀.output = (M.envelopeNTM.initView w).output := by rw [hrep₀.output]; rfl
    have hwt : view₀.workTapes = (M.envelopeNTM.initView w).workTapes := by
      funext i
      have hnil_rep : (Cslib.Turing.BiTape.nil : Cslib.Turing.BiTape Bool).Represents
          ((M.runCfg O w 0).1.workTapes i) ((M.runCfg O w 0).1.workTapePos i) := by
        intro pos; simp [Cfg.init]
      exact biTape_represents_unique (hrep₀.workTapes i) hnil_rep
    rw [hp, hs, hwt, ho]
  exact ⟨hview₀_eq ▸ hrep₀, hview₀_eq ▸ hfit₀⟩

private theorem runCfg_output_nil {k_tapes : ℕ} {State : Type}
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (w : List Bool) :
    ∀ t, (M.runCfg O w t).1.state ≠ none → (M.runCfg O w t).1.output = [] := by
  classical
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    rw [M.runCfg_succ]
    cases hs : (M.runCfg O w t).1.state with
    | none =>
      rw [M.stepCfg_of_state_eq_none _ hs]
      intro h; exact (h hs).elim
    | some q =>
      rw [M.stepCfg_of_state_eq_some _ hs]
      have hnil := ih (by simp [hs])
      cases M.tr q (M.runCfg O w t).1.inputSymbol (M.runCfg O w t).1.workTapeSymbols <;>
        simp [Action.apply, hnil]

private theorem runCfg_stay_of_halted {k_tapes : ℕ} {State : Type}
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (w : List Bool) :
    ∀ {t₁ t₂}, t₁ ≤ t₂ → (M.runCfg O w t₁).1.Halted →
      M.runCfg O w t₂ = M.runCfg O w t₁ := by
  intro t₁ t₂ hle hh
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, M.runCfg_succ, ih (Nat.le_add_right _ _)]
    exact M.stepCfg_of_state_eq_none _ hh

private abbrev simSymOf (k_tapes Bn : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k_tapes) Bn)) : Option Bool :=
  w[queryIndex (k := k_tapes) Bn u.val]?

private abbrev simWpNext {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn : ℕ) (w : List Bool)
    (tgt : WPTarget (vertexBound (k := k_tapes) Bn))
    (s : Fin (vertexBound (k := k_tapes) Bn + 1))
    (i : Fin (Fintype.card (WPNode (vertexBound (k := k_tapes) Bn)))) :
    Option (Fin (Fintype.card (WPNode (vertexBound (k := k_tapes) Bn)))) :=
  (if s.val < vertexBound (k := k_tapes) Bn then
    wpWorkStep M Bn w.length
      (match tgt with | .queryBit j => some j | _ => none)
      (simSymOf k_tapes Bn w)
      ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn))).symm i)
   else
    wpClassifyStep M Bn w.length tgt (simSymOf k_tapes Bn w)
      ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn))).symm i)).map
    (Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)))

private abbrev simWpAccepted {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn : ℕ) (w : List Bool)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn))
    (tgt : WPTarget (vertexBound (k := k_tapes) Bn)) : Bool :=
  decide (iterOpt
    ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)))
      (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k := k_tapes) Bn)⟩, false)))
    (simWpNext M Bn w tgt)
    (vertexBound (k := k_tapes) Bn + 1) le_rfl =
    some ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn))) none))

private abbrev simRoundOracleAns {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn)) : Bool :=
  (List.ofFn fun L : Fin (vertexBound (k := k_tapes) Bn + 1) ↦
    simWpAccepted M Bn w u₀ (.queryLen L) &&
      O.slice L.val (fun j : Fin L.val ↦
        simWpAccepted M Bn w u₀ (.queryBit
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp L.isLt)⟩))).any id

private abbrev simRoundStepBool {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (u₀ v : Fin (vertexBound (k := k_tapes) Bn)) : Bool :=
  (simWpAccepted M Bn w u₀ (.yesTarget v) && simRoundOracleAns M O Bn w u₀) ||
    (simWpAccepted M Bn w u₀ (.noTarget v) && !simRoundOracleAns M O Bn w u₀)

private abbrev simRoundAccBool {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn : ℕ) (w : List Bool)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn)) : Bool :=
  simWpAccepted M Bn w u₀ .accHalt

private abbrev simRoundNext {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (i : Fin (vertexBound (k := k_tapes) Bn + 1)) :
    Option (Fin (vertexBound (k := k_tapes) Bn + 1)) :=
  if hi : i.val < vertexBound (k := k_tapes) Bn then
    if simRoundAccBool M Bn w ⟨i.val, hi⟩ then some (Fin.last (vertexBound (k := k_tapes) Bn))
    else ((Finset.univ : Finset (Fin (vertexBound (k := k_tapes) Bn))).toList.find?
      (simRoundStepBool M O Bn w ⟨i.val, hi⟩)).map Fin.castSucc
  else some (Fin.last (vertexBound (k := k_tapes) Bn))

private theorem simWpIter_indep {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (Bn : ℕ) (w : List Bool) :
    ∀ (u₀ : Fin (vertexBound (k := k_tapes) Bn))
      (tgt₁ tgt₂ : WPTarget (vertexBound (k := k_tapes) Bn))
      (s : ℕ) (hs : s ≤ vertexBound (k := k_tapes) Bn),
      (iterOpt
        ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)))
          (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k := k_tapes) Bn)⟩, false)))
        (simWpNext M Bn w tgt₁)
        s (Nat.le_succ_of_le hs)).map (fun idx ↦
          ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn))).symm idx).map
            fun st ↦ (st.1, st.2.1)) =
      (iterOpt
        ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)))
          (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k := k_tapes) Bn)⟩, false)))
        (simWpNext M Bn w tgt₂)
        s (Nat.le_succ_of_le hs)).map (fun idx ↦
          ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn))).symm idx).map
            fun st ↦ (st.1, st.2.1)) := by
  intro u₀ tgt₁ tgt₂ s hs
  induction s with
  | zero => simp
  | succ s ih =>
    have hs_lt : s < (vertexBound (k := k_tapes) Bn) := hs
    rw [iterOpt_succ, iterOpt_succ]
    have hih := ih (Nat.le_of_lt hs_lt)
    cases h1 : iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
      k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
        k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt₁) s
        (Nat.le_succ_of_le (Nat.le_of_lt hs_lt)) <;>
      cases h2 : iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
        k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
          k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt₂) s
        (Nat.le_succ_of_le (Nat.le_of_lt hs_lt))
    · rfl
    · rw [h1, h2] at hih; simp at hih
    · rw [h1, h2] at hih; simp at hih
    · rename_i idx₁ idx₂
      rw [h1, h2] at hih
      simp only [Option.map_some, Option.some.injEq] at hih
      dsimp only [Option.bind, simWpNext]
      simp only [hs_lt, ↓reduceIte]
      cases hn1 : (Fintype.equivFin (WPNode (vertexBound (k :=
        k_tapes) Bn))).symm idx₁ <;> cases hn2 : (Fintype.equivFin (WPNode (vertexBound (k :=
          k_tapes) Bn))).symm idx₂
      · rfl
      · rw [hn1, hn2] at hih; simp at hih
      · rw [hn1, hn2] at hih; simp at hih
      · rename_i st₁ st₂
        rw [hn1, hn2] at hih
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hih
        rcases st₁ with ⟨u₁, ql₁, b₁⟩
        rcases st₂ with ⟨u₂, ql₂, b₂⟩
        dsimp only at hih
        obtain ⟨rfl, rfl⟩ := hih
        rw [wpWorkStep_some, wpWorkStep_some]
        dsimp only []
        split_ifs with hv
        · cases hdec : decodeControlWork (State := State)
            (readRegisters (k := k_tapes) Bn u₁.val) with
          | none => rfl
          | some qw =>
            rcases qw with ⟨q, work⟩
            dsimp only
            cases M.tr q
                (inputSymbol w.length (readRegisters (k :=
                  k_tapes) Bn u₁.val .inputPos) ((simSymOf k_tapes Bn w) u₁))
                work with
            | step moveIn moveWork emit nextQ =>
              dsimp only
              split_ifs <;> simp [Equiv.symm_apply_apply]
            | query _ _ => simp [Equiv.symm_apply_apply]
            | halt _ => simp [Equiv.symm_apply_apply]
        · rfl

private theorem simRoundNext_unique {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (u₀ : Fin (vertexBound (k := k_tapes) Bn))
    (j : Fin (vertexBound (k := k_tapes) Bn + 1)) :
    (if hj : j.val < vertexBound (k := k_tapes) Bn then
      simRoundStepBool M O Bn w u₀ ⟨j.val, hj⟩
     else simRoundAccBool M Bn w u₀) =
      decide (simRoundNext M O Bn w (Fin.castSucc u₀) = some j) := by
  have hwp_iter_indep := simWpIter_indep M Bn w
  have h_mutual_excl :
      (∀ v : Fin (vertexBound (k :=
        k_tapes) Bn), (simRoundAccBool M Bn w) u₀ = true →
          (simRoundStepBool M O Bn w) u₀ v = false) ∧
      (∀ v₁ v₂ : Fin (vertexBound (k :=
        k_tapes) Bn), (simRoundStepBool M O Bn w) u₀ v₁ = true →
          (simRoundStepBool M O Bn w) u₀ v₂ = true → v₁ = v₂) := by
    have hindep (tgt : WPTarget (vertexBound (k := k_tapes) Bn)) :
        (simWpAccepted M Bn w) u₀ tgt = true →
        ∃ u_end qlen_end b_end,
          iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
            k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
              k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt)
            (vertexBound (k := k_tapes) Bn) (Nat.le_succ (vertexBound (k :=
              k_tapes) Bn)) = some ((Fintype.equivFin (WPNode (vertexBound (k :=
                k_tapes) Bn))) (some (u_end, qlen_end, b_end))) ∧
          wpClassifyStep M Bn w.length tgt (simSymOf k_tapes Bn w) (some (u_end, qlen_end, b_end)) =
            some none := by
      intro hacc
      dsimp only [simWpAccepted] at hacc
      rw [iterOpt_succ, decide_eq_true_eq] at hacc
      cases hN_it : iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
        k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
          k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt)
          (vertexBound (k := k_tapes) Bn) (Nat.le_succ (vertexBound (k := k_tapes) Bn)) with
      | none => rw [hN_it] at hacc; simp at hacc
      | some idx =>
        rw [hN_it] at hacc
        dsimp only [Option.bind, simWpNext] at hacc
        simp only [lt_irrefl (vertexBound (k := k_tapes) Bn), ↓reduceIte, Option.map_eq_some_iff,
          Equiv.apply_eq_iff_eq] at hacc
        obtain ⟨_, hcl, rfl⟩ := hacc
        cases hsym : (Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn))).symm idx with
        | none => rw [hsym] at hcl; simp at hcl
        | some st =>
          rcases st with ⟨u_end, ql_end, b_end⟩
          refine ⟨u_end, ql_end, b_end, ?_, by rwa [hsym] at hcl⟩
          rw [← hsym, Equiv.apply_symm_apply]
    have hsame_u {tgt₁ tgt₂ : WPTarget (vertexBound (k :=
      k_tapes) Bn)} {u₁ u₂ : Fin (vertexBound (k := k_tapes) Bn)} {ql₁ ql₂ : Fin ((vertexBound (k :=
        k_tapes) Bn) + 1)}
        {b₁ b₂ : Bool}
        (h1 : iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
          k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
            k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt₁)
          (vertexBound (k := k_tapes) Bn) (Nat.le_succ (vertexBound (k :=
            k_tapes) Bn)) = some ((Fintype.equivFin (WPNode (vertexBound (k :=
              k_tapes) Bn))) (some (u₁, ql₁, b₁))))
        (h2 : iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
          k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
            k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt₂)
          (vertexBound (k := k_tapes) Bn) (Nat.le_succ (vertexBound (k :=
            k_tapes) Bn)) = some ((Fintype.equivFin (WPNode (vertexBound (k :=
              k_tapes) Bn))) (some (u₂, ql₂, b₂)))) :
        u₁ = u₂ ∧ ql₁ = ql₂ := by
      have h := hwp_iter_indep u₀ tgt₁ tgt₂ (vertexBound (k := k_tapes) Bn) le_rfl
      rw [h1, h2] at h
      simpa [Equiv.symm_apply_apply] using h
    have hguard_pos {tgt : WPTarget (vertexBound (k := k_tapes) Bn)}
        {u : Fin (vertexBound (k := k_tapes) Bn)}
        {ql : Fin (vertexBound (k := k_tapes) Bn + 1)} {b : Bool}
        (hcl : wpClassifyStep M Bn w.length tgt (simSymOf k_tapes Bn w) (some (u, ql, b)) =
          some none) :
        (valid (k := k_tapes) (State := State) Bn w.length u.val &&
          decide (readRegisters (k := k_tapes) Bn u.val .output = 0)) = true := by
      rw [wpClassifyStep_some] at hcl
      dsimp only [] at hcl
      by_contra hneg
      rw [ite_eq_right hneg] at hcl
      cases hcl
    refine ⟨fun v hacc ↦ Bool.eq_false_iff.mpr fun hstep ↦ ?_, fun v₁ v₂ hs₁ hs₂ ↦ ?_⟩
    · obtain ⟨u₁, ql₁, b₁, hit₁, hcl₁⟩ := hindep .accHalt hacc
      dsimp only [simRoundStepBool] at hstep
      rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hstep
      rcases hstep with ⟨hyes, _⟩ | ⟨hno, _⟩
      · obtain ⟨u₂, ql₂, b₂, hit₂, hcl₂⟩ := hindep (.yesTarget v) hyes
        obtain ⟨rfl, rfl⟩ := hsame_u hit₁ hit₂
        have hv_ok := hguard_pos hcl₁
        rw [wpClassifyStep_some] at hcl₁ hcl₂
        dsimp only [] at hcl₁ hcl₂
        rw [ite_eq_left hv_ok] at hcl₁ hcl₂
        cases hdec : decodeControlWork (State := State)
            (readRegisters (k := k_tapes) Bn u₁.val) with
        | none => rw [hdec] at hcl₁; simp at hcl₁
        | some qw =>
          rcases qw with ⟨q, work⟩
          rw [hdec] at hcl₁ hcl₂
          dsimp only at hcl₁ hcl₂
          cases htr : M.tr q _ work <;> rw [htr] at hcl₁ hcl₂ <;> simp at hcl₁ hcl₂
      · obtain ⟨u₂, ql₂, b₂, hit₂, hcl₂⟩ := hindep (.noTarget v) hno
        obtain ⟨rfl, rfl⟩ := hsame_u hit₁ hit₂
        have hv_ok := hguard_pos hcl₁
        rw [wpClassifyStep_some] at hcl₁ hcl₂
        dsimp only [] at hcl₁ hcl₂
        rw [ite_eq_left hv_ok] at hcl₁ hcl₂
        cases hdec : decodeControlWork (State := State)
            (readRegisters (k := k_tapes) Bn u₁.val) with
        | none => rw [hdec] at hcl₁; simp at hcl₁
        | some qw =>
          rcases qw with ⟨q, work⟩
          rw [hdec] at hcl₁ hcl₂
          dsimp only at hcl₁ hcl₂
          cases htr : M.tr q _ work <;> rw [htr] at hcl₁ hcl₂ <;> simp at hcl₁ hcl₂
    · dsimp only [simRoundStepBool] at hs₁ hs₂
      cases hans : (simRoundOracleAns M O Bn w) u₀
      · simp only [hans, Bool.and_false, Bool.not_false, Bool.and_true, Bool.false_or] at hs₁ hs₂
        obtain ⟨u₁, ql₁, b₁, hit₁, hcl₁⟩ := hindep (.noTarget v₁) hs₁
        obtain ⟨u₂, ql₂, b₂, hit₂, hcl₂⟩ := hindep (.noTarget v₂) hs₂
        obtain ⟨rfl, rfl⟩ := hsame_u hit₁ hit₂
        have hv_ok := hguard_pos hcl₁
        rw [wpClassifyStep_some] at hcl₁ hcl₂
        dsimp only [] at hcl₁ hcl₂
        rw [ite_eq_left hv_ok] at hcl₁ hcl₂
        cases hdec : decodeControlWork (State := State)
            (readRegisters (k := k_tapes) Bn u₁.val) with
        | none => rw [hdec] at hcl₁; simp at hcl₁
        | some qw =>
          rcases qw with ⟨q, work⟩
          rw [hdec] at hcl₁ hcl₂
          dsimp only at hcl₁ hcl₂
          cases htr : M.tr q _ work with
          | step _ _ _ _ => rw [htr] at hcl₁; simp at hcl₁
          | halt _ => rw [htr] at hcl₁; simp at hcl₁
          | query onYes onNo =>
            rw [htr] at hcl₁ hcl₂
            dsimp only at hcl₁ hcl₂
            split_ifs at hcl₁ with hc₁
            split_ifs at hcl₂ with hc₂
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁ hc₂
            exact Fin.ext (hc₁.1.2.trans hc₂.1.2.symm)
      · simp only [hans, Bool.and_true, Bool.not_true, Bool.and_false, Bool.or_false] at hs₁ hs₂
        obtain ⟨u₁, ql₁, b₁, hit₁, hcl₁⟩ := hindep (.yesTarget v₁) hs₁
        obtain ⟨u₂, ql₂, b₂, hit₂, hcl₂⟩ := hindep (.yesTarget v₂) hs₂
        obtain ⟨rfl, rfl⟩ := hsame_u hit₁ hit₂
        have hv_ok := hguard_pos hcl₁
        rw [wpClassifyStep_some] at hcl₁ hcl₂
        dsimp only [] at hcl₁ hcl₂
        rw [ite_eq_left hv_ok] at hcl₁ hcl₂
        cases hdec : decodeControlWork (State := State)
            (readRegisters (k := k_tapes) Bn u₁.val) with
        | none => rw [hdec] at hcl₁; simp at hcl₁
        | some qw =>
          rcases qw with ⟨q, work⟩
          rw [hdec] at hcl₁ hcl₂
          dsimp only at hcl₁ hcl₂
          cases htr : M.tr q _ work with
          | step _ _ _ _ => rw [htr] at hcl₁; simp at hcl₁
          | halt _ => rw [htr] at hcl₁; simp at hcl₁
          | query onYes onNo =>
            rw [htr] at hcl₁ hcl₂
            dsimp only at hcl₁ hcl₂
            split_ifs at hcl₁ with hc₁
            split_ifs at hcl₂ with hc₂
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁ hc₂
            exact Fin.ext (hc₁.1.2.trans hc₂.1.2.symm)
  dsimp only [simRoundNext]
  have hu_lt : (Fin.castSucc u₀).val < (vertexBound (k := k_tapes) Bn) := u₀.isLt
  have hu_eq : (⟨(Fin.castSucc u₀).val, hu_lt⟩ : Fin (vertexBound (k := k_tapes) Bn)) = u₀ :=
    Fin.ext rfl
  simp only [hu_lt, ↓reduceDIte, hu_eq]
  by_cases hj : j.val < (vertexBound (k := k_tapes) Bn)
  · simp only [hj, ↓reduceDIte]
    by_cases hacc : (simRoundAccBool M Bn w) u₀ = true
    · simp only [hacc, ↓reduceIte]
      rw [h_mutual_excl.1 ⟨j.val, hj⟩ hacc]
      symm
      rw [decide_eq_false_iff_not]
      intro heq
      have := congrArg Fin.val (Option.some.inj heq)
      simp only [Fin.val_last] at this
      omega
    · have hacc_f : (simRoundAccBool M Bn w) u₀ = false := Bool.eq_false_iff.mpr hacc
      rw [hacc_f]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hs : (simRoundStepBool M O Bn w) u₀ ⟨j.val, hj⟩ = true
      · rw [hs]
        have hmem : (⟨j.val, hj⟩ : Fin (vertexBound (k :=
          k_tapes) Bn)) ∈ (Finset.univ : Finset (Fin (vertexBound (k := k_tapes) Bn))).toList :=
          Finset.mem_toList.mpr (Finset.mem_univ _)
        have hisSome : ((Finset.univ : Finset (Fin (vertexBound (k := k_tapes) Bn))).toList.find?
            (simRoundStepBool M O Bn w u₀)).isSome :=
          List.find?_isSome.mpr ⟨⟨j.val, hj⟩, hmem, hs⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hisSome
        have hv_eq : v = ⟨j.val, hj⟩ := h_mutual_excl.2 v _ (List.find?_some hv) hs
        rw [hv, hv_eq]
        symm
        rw [decide_eq_true_eq, Option.map_some, Option.some.injEq]
        exact Fin.ext rfl
      · have hs_f : (simRoundStepBool M O Bn w) u₀ ⟨j.val, hj⟩ = false := Bool.eq_false_iff.mpr hs
        rw [hs_f]
        symm
        rw [decide_eq_false_iff_not]
        intro heq
        rw [Option.map_eq_some_iff] at heq
        obtain ⟨v, hv, hvj⟩ := heq
        have hv_eq : v = ⟨j.val, hj⟩ :=
          Fin.ext (by have := congrArg Fin.val hvj; simpa using this)
        subst hv_eq
        exact hs (List.find?_some hv)
  · have hj_eq : j = Fin.last (vertexBound (k := k_tapes) Bn) :=
      Fin.ext (by have := j.isLt; simp; omega)
    subst hj_eq
    simp only [Fin.val_last, lt_irrefl (vertexBound (k := k_tapes) Bn), ↓reduceDIte]
    cases hacc : (simRoundAccBool M Bn w) u₀
    · simp only [Bool.false_eq_true, ↓reduceIte]
      symm
      rw [decide_eq_false_iff_not]
      intro heq
      rw [Option.map_eq_some_iff] at heq
      obtain ⟨v, _, hv⟩ := heq
      have := congrArg Fin.val hv
      simp only [Fin.val_castSucc, Fin.val_last] at this
      exact absurd this (ne_of_lt v.isLt)
    · simp

private theorem simWorkStep_exact {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool) :
    ∀ (t : ℕ) (qlen : Fin (vertexBound (k := k_tapes) Bn + 1)) (_b : Bool)
      (_tgt : WPTarget (vertexBound (k := k_tapes) Bn)),
      (M.runCfg O w t).1.state ≠ none →
      (M.runCfg O w t).2.length = qlen.val →
      ∀ (view : FiniteCfg k_tapes Bool State),
        ViewRep view (M.runCfg O w t).1 →
        ∀ (hfit : Fits Bn (registers view)),
          let u : Fin (vertexBound (k := k_tapes) Bn) := ⟨vertexID Bn view, vertexID_lt hfit⟩
          let r := readRegisters (k := k_tapes) Bn u.val
          ∃ q : State, (M.runCfg O w t).1.state = some q ∧
            valid (k := k_tapes) (State := State) Bn w.length u.val = true ∧
            r .output = 0 ∧
            decodeControlWork (State := State) r = some (q, view.workTapeSymbols) ∧
            inputSymbol w.length (r .inputPos) (simSymOf k_tapes Bn w u) =
              (M.runCfg O w t).1.inputSymbol ∧
            view.workTapeSymbols = (M.runCfg O w t).1.workTapeSymbols := by
  have hrun_output_nil := runCfg_output_nil M O w
  intro t qlen _ _ hrun _ view hrep hfit u r
  cases hst : (M.runCfg O w t).1.state with
  | none => exact (hrun hst).elim
  | some q =>
    have hv_st : view.state = some q := hrep.state.trans hst
    have hout_nil : (M.runCfg O w t).1.output = [] := hrun_output_nil t hrun
    have hv_out : view.output = [] := by rw [hrep.output, hout_nil]; rfl
    have hrr : r = registers view := readRegisters_vertexID hfit
    have hval : valid (k := k_tapes) (State := State) Bn w.length u.val = true := by
      simpa [u, hrep.input] using valid_vertexID hfit
    have hout0 : r .output = 0 := by simp [hrr, registers, hv_out, outputCode]
    have hdec : decodeControlWork (State := State) r = some (q, view.workTapeSymbols) := by
      rw [decodeControlWork_eq_some_iff, hrr]
      exact ⟨by simp [registers, hv_st], fun _ ↦ rfl⟩
    obtain ⟨hin_sym, hwk_sym⟩ := hrep.symbols
    have hin_q : inputSymbol w.length (r .inputPos) ((simSymOf k_tapes Bn w) u) =
      (M.runCfg O w t).1.inputSymbol := by
      have hq := inputSymbol_query hfit
      simpa [hrr, registers, u, simSymOf, hrep.input, hin_sym] using hq
    exact ⟨q, rfl, hval, hout0, hdec, hin_q, hwk_sym⟩

private theorem simExists_phase_end {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (H₀ : ℕ) (hhalt₀ : (M.runCfg O w H₀).1.Halted)
    (hview_run : ∀ t, ∃ view : FiniteCfg k_tapes Bool State,
      ViewRep view (M.runCfg O w t).1 ∧ Fits Bn (registers view)) :
    ∀ (t₀ : ℕ), (M.runCfg O w t₀).1.state ≠ none → (M.runCfg O w t₀).2 = [] →
      ∃ d ≤ vertexBound (k := k_tapes) Bn,
        (∀ s < d, ∃ q moveIn moveWork emit nextQ,
          (M.runCfg O w (t₀ + s)).1.state = some q ∧
          M.tr q (M.runCfg O w (t₀ + s)).1.inputSymbol
            (M.runCfg O w (t₀ + s)).1.workTapeSymbols =
            .step moveIn moveWork emit nextQ) ∧
        (∃ q, (M.runCfg O w (t₀ + d)).1.state = some q ∧
          ((∃ onYes onNo, M.tr q (M.runCfg O w (t₀ + d)).1.inputSymbol
              (M.runCfg O w (t₀ + d)).1.workTapeSymbols = .query onYes onNo) ∨
           (∃ acc, M.tr q (M.runCfg O w (t₀ + d)).1.inputSymbol
              (M.runCfg O w (t₀ + d)).1.workTapeSymbols = .halt acc))) := by
  classical
  have hrun_output_nil := runCfg_output_nil M O w
  have hrun_stay {t₁ t₂} := @runCfg_stay_of_halted _ _ M O w t₁ t₂
  intro t₀ hrun₀ _
  have hex_nonstep : ∃ d, ¬(∃ q moveIn moveWork emit nextQ,
      (M.runCfg O w (t₀ + d)).1.state = some q ∧
      M.tr q (M.runCfg O w (t₀ + d)).1.inputSymbol
        (M.runCfg O w (t₀ + d)).1.workTapeSymbols = .step moveIn moveWork emit nextQ) := by
    refine ⟨H₀, ?_⟩
    rintro ⟨q, _, _, _, _, hst, _⟩
    have hh : (M.runCfg O w (t₀ + H₀)).1.Halted :=
      (congrArg (fun p ↦ p.1.Halted) (hrun_stay (Nat.le_add_left H₀ t₀) hhalt₀)).mpr hhalt₀
    change (M.runCfg O w (t₀ + H₀)).1.state = none at hh
    rw [hh] at hst
    cases hst
  let d := Nat.find hex_nonstep
  have hd_spec := Nat.find_spec hex_nonstep
  have hd_min : ∀ s < d, ∃ q moveIn moveWork emit nextQ,
      (M.runCfg O w (t₀ + s)).1.state = some q ∧
      M.tr q (M.runCfg O w (t₀ + s)).1.inputSymbol
        (M.runCfg O w (t₀ + s)).1.workTapeSymbols = .step moveIn moveWork emit nextQ :=
    fun s hs ↦ of_not_not (Nat.find_min hex_nonstep hs)
  have hrun_le : ∀ s ≤ d, (M.runCfg O w (t₀ + s)).1.state ≠ none := by
    intro s hs
    induction s with
    | zero => simpa using hrun₀
    | succ s _ =>
      obtain ⟨q, mI, mW, em, nQ, hst, htr⟩ := hd_min s (Nat.lt_of_succ_le hs)
      rw [Nat.add_succ, M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst, htr]
      simp [Action.apply]
  have hd_le_Nn : d ≤ (vertexBound (k := k_tapes) Bn) := by
    by_contra hgt
    have hNn_lt_d : (vertexBound (k := k_tapes) Bn) < d := not_le.mp hgt
    choose viewOf hrepOf hfitOf using fun s : Fin ((vertexBound (k :=
      k_tapes) Bn) + 1) ↦ hview_run (t₀ + s.val)
    let uOf (s : Fin ((vertexBound (k := k_tapes) Bn) + 1)) : Fin (vertexBound (k := k_tapes) Bn) :=
      ⟨vertexID Bn (viewOf s), vertexID_lt (hfitOf s)⟩
    have hnot_inj : ¬Function.Injective uOf := fun hinj ↦ by
      have := Fintype.card_le_of_injective uOf hinj
      simp only [Fintype.card_fin] at this
      omega
    simp only [Function.Injective, not_forall] at hnot_inj
    obtain ⟨s₁, s₂, hu_eq, hs_ne⟩ := hnot_inj
    have hv_eq : viewOf s₁ = viewOf s₂ := by
      have hout_class (s : Fin ((vertexBound (k := k_tapes) Bn) + 1)) :
          outputClass (viewOf s).output = (viewOf s).output := by
        have hs_le : s.val ≤ d := le_trans (Nat.lt_succ_iff.mp s.isLt) (le_of_lt hNn_lt_d)
        have hnil := hrun_output_nil (t₀ + s.val) (hrun_le s.val hs_le)
        rw [(hrepOf s).output, hnil]
        rfl
      exact vertexID_injective
        ((hrepOf s₁).input.trans (hrepOf s₂).input.symm)
        (hout_class s₁) (hout_class s₂) (hfitOf s₁) (hfitOf s₂)
        (congrArg Fin.val hu_eq)
    obtain ⟨a, b, hab, ha_le_Nn, _, hview_ab⟩ :
        ∃ a b, a < b ∧ a ≤ (vertexBound (k := k_tapes) Bn) ∧ b ≤ (vertexBound (k := k_tapes) Bn) ∧
          ∃ v, ViewRep v (M.runCfg O w (t₀ + a)).1 ∧
            ViewRep v (M.runCfg O w (t₀ + b)).1 := by
      rcases lt_or_gt_of_ne (fun h ↦ hs_ne (Fin.ext h)) with hlt | hgt
      · exact ⟨s₁.val, s₂.val, hlt, Nat.lt_succ_iff.mp s₁.isLt, Nat.lt_succ_iff.mp s₂.isLt,
          viewOf s₁, hrepOf s₁, hv_eq ▸ hrepOf s₂⟩
      · exact ⟨s₂.val, s₁.val, hgt, Nat.lt_succ_iff.mp s₂.isLt, Nat.lt_succ_iff.mp s₁.isLt,
          viewOf s₂, hrepOf s₂, hv_eq.symm ▸ hrepOf s₁⟩
    obtain ⟨v₀, hrep_a, hrep_b⟩ := hview_ab
    have hstep_lock' : ∀ {s t₂ : ℕ} {v : FiniteCfg k_tapes Bool State},
        s < d →
        ViewRep v (M.runCfg O w (t₀ + s)).1 →
        ViewRep v (M.runCfg O w t₂).1 →
        ∃ v', ViewRep v' (M.runCfg O w (t₀ + (s + 1))).1 ∧
          ViewRep v' (M.runCfg O w (t₂ + 1)).1 := by
      intro s t₂ v hs_lt hr₁ hr₂
      obtain ⟨q, mI, mW, em, nQ, hst₁, htr₁⟩ := hd_min s hs_lt
      have hst₂ : (M.runCfg O w t₂).1.state = some q :=
        hr₂.state.symm.trans (hr₁.state.trans hst₁)
      have hin₂ : (M.runCfg O w t₂).1.inputSymbol = (M.runCfg O w (t₀ + s)).1.inputSymbol :=
        hr₂.symbols.1.symm.trans hr₁.symbols.1
      have hwk₂ : (M.runCfg O w t₂).1.workTapeSymbols =
          (M.runCfg O w (t₀ + s)).1.workTapeSymbols :=
        hr₂.symbols.2.symm.trans hr₁.symbols.2
      let act : Action k_tapes Bool State := ⟨mI, mW, none, some nQ⟩
      refine ⟨(v.step act).summarizeOutput, ?_, ?_⟩
      · rw [← Nat.add_assoc, M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst₁, htr₁]
        exact hr₁.step act
      · rw [M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst₂, hin₂, hwk₂, htr₁]
        exact hr₂.step act
    have hblock : ∀ (t₂ : ℕ),
        ViewRep v₀ (M.runCfg O w t₂).1 →
        ViewRep v₀ (M.runCfg O w (t₂ + (b - a))).1 := by
      intro t₂ hr₂
      have hwalk : ∀ k ≤ b - a, ∃ vk,
          ViewRep vk (M.runCfg O w (t₀ + (a + k))).1 ∧
          ViewRep vk (M.runCfg O w (t₂ + k)).1 := by
        intro k hk
        induction k with
        | zero => exact ⟨v₀, hrep_a, hr₂⟩
        | succ k ih =>
          obtain ⟨vk, hrk1, hrk2⟩ := ih (Nat.le_of_succ_le hk)
          obtain ⟨vk', hrk1', hrk2'⟩ := hstep_lock' (by omega : a + k < d) hrk1 hrk2
          rw [Nat.add_assoc a k 1] at hrk1'
          exact ⟨vk', hrk1', hrk2'⟩
      obtain ⟨vb, hrb1, hrb2⟩ := hwalk (b - a) le_rfl
      rw [Nat.add_sub_cancel' (le_of_lt hab)] at hrb1
      have hvb_eq : vb = v₀ := by
        apply coreCode_injective (hrb1.input.trans hrep_b.input.symm)
        change encCore (vb.inputPos.val, vb.state, vb.workTapes, vb.output) =
          encCore (v₀.inputPos.val, v₀.state, v₀.workTapes, v₀.output)
        have hp : vb.inputPos.val = v₀.inputPos.val := hrb1.inputPos.trans hrep_b.inputPos.symm
        have hs : vb.state = v₀.state := hrb1.state.trans hrep_b.state.symm
        have ho : vb.output = v₀.output := hrb1.output.trans hrep_b.output.symm
        have hw : vb.workTapes = v₀.workTapes := funext fun i ↦
          biTape_represents_unique (hrb1.workTapes i) (hrep_b.workTapes i)
        rw [hp, hs, hw, ho]
      exact hvb_eq ▸ hrb2
    have hpump : ∀ m : ℕ, ViewRep v₀ (M.runCfg O w (t₀ + a + m * (b - a))).1 := by
      intro m
      induction m with
      | zero => simpa using hrep_a
      | succ m ih =>
        have := hblock (t₀ + a + m * (b - a)) ih
        simpa [Nat.succ_mul, Nat.add_assoc] using this
    have hrep_H := hpump (H₀ + 1)
    have hpos_ba : 0 < b - a := Nat.sub_pos_of_lt hab
    have hge_H : H₀ ≤ t₀ + a + (H₀ + 1) * (b - a) := by nlinarith
    have hh_pump : (M.runCfg O w (t₀ + a + (H₀ + 1) * (b - a))).1.Halted :=
      (congrArg (fun p ↦ p.1.Halted) (hrun_stay hge_H hhalt₀)).mpr hhalt₀
    have hh_a : (M.runCfg O w (t₀ + a)).1.state = none :=
      hrep_a.state.symm.trans (hrep_H.state.trans hh_pump)
    exact hrun_le a (le_of_lt (lt_of_le_of_lt ha_le_Nn hNn_lt_d)) hh_a
  refine ⟨d, hd_le_Nn, hd_min, ?_⟩
  cases hst_d : (M.runCfg O w (t₀ + d)).1.state with
  | none => exact (hrun_le d le_rfl hst_d).elim
  | some q =>
    refine ⟨q, rfl, ?_⟩
    cases htr_d : M.tr q (M.runCfg O w (t₀ + d)).1.inputSymbol
        (M.runCfg O w (t₀ + d)).1.workTapeSymbols with
    | step mI mW em nQ => exact (hd_spec ⟨q, mI, mW, em, nQ, hst_d, htr_d⟩).elim
    | query onY onN => exact Or.inl ⟨onY, onN, rfl⟩
    | halt acc => exact Or.inr ⟨acc, rfl⟩

private theorem simPhase_sim {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (H₀ : ℕ) (hhalt₀ : (M.runCfg O w H₀).1.Halted)
    (hview_run : ∀ t, ∃ view : FiniteCfg k_tapes Bool State,
      ViewRep view (M.runCfg O w t).1 ∧ Fits Bn (registers view)) :
    ∀ (t₀ : ℕ), (M.runCfg O w t₀).1.state ≠ none → (M.runCfg O w t₀).2 = [] →
      ∀ (view₀' : FiniteCfg k_tapes Bool State)
        (_hrep₀' : ViewRep view₀' (M.runCfg O w t₀).1)
        (hfit₀' : Fits Bn (registers view₀')),
        let u₀ : Fin (vertexBound (k := k_tapes) Bn) := ⟨vertexID Bn view₀', vertexID_lt hfit₀'⟩
        ∃ d ≤ vertexBound (k := k_tapes) Bn, ∃ (view_d : FiniteCfg k_tapes Bool State)
          (_hrep_d : ViewRep view_d (M.runCfg O w (t₀ + d)).1)
          (hfit_d : Fits Bn (registers view_d))
          (hlen_d : (M.runCfg O w (t₀ + d)).2.length < vertexBound (k := k_tapes) Bn + 1),
          (∀ tgt : WPTarget (vertexBound (k := k_tapes) Bn),
            iterOpt
              ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)))
                (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k := k_tapes) Bn)⟩, false)))
              (simWpNext M Bn w tgt)
              (vertexBound (k := k_tapes) Bn) (Nat.le_succ (vertexBound (k := k_tapes) Bn)) =
              some ((Fintype.equivFin (WPNode (vertexBound (k := k_tapes) Bn)))
                (some (⟨vertexID Bn view_d, vertexID_lt hfit_d⟩,
                  ⟨(M.runCfg O w (t₀ + d)).2.length, hlen_d⟩,
                  match tgt with
                  | .queryBit j => ((M.runCfg O w (t₀ + d)).2[j.val]?).getD false
                  | _ => false)))) ∧
          (∃ q, (M.runCfg O w (t₀ + d)).1.state = some q ∧
            ((∃ onYes onNo, M.tr q (M.runCfg O w (t₀ + d)).1.inputSymbol
                (M.runCfg O w (t₀ + d)).1.workTapeSymbols = .query onYes onNo) ∨
             (∃ acc, M.tr q (M.runCfg O w (t₀ + d)).1.inputSymbol
                (M.runCfg O w (t₀ + d)).1.workTapeSymbols = .halt acc))) := by
  have hwork_step_exact := simWorkStep_exact M O Bn w
  have hexists_phase_end := simExists_phase_end M O Bn w H₀ hhalt₀ hview_run
  intro t₀ hrun₀ hbuf₀ view₀' hrep₀' hfit₀' u₀
  obtain ⟨d, hd_le, hd_steps, hd_end⟩ := hexists_phase_end t₀ hrun₀ hbuf₀
  have hstep_sim :
      ∀ (s : ℕ) (hs : s ≤ d),
        ∃ (vs : FiniteCfg k_tapes Bool State)
          (hreps : ViewRep vs (M.runCfg O w (t₀ + s)).1)
          (hfits : Fits Bn (registers vs))
          (hlens : (M.runCfg O w (t₀ + s)).2.length ≤ s),
          ∀ tgt : WPTarget (vertexBound (k := k_tapes) Bn),
            iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
              k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
                k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt)
              s (Nat.le_succ_of_le (le_trans hs hd_le)) =
              some ((Fintype.equivFin (WPNode (vertexBound (k :=
                k_tapes) Bn))) (some (⟨vertexID Bn vs, vertexID_lt hfits⟩,
                ⟨(M.runCfg O w (t₀ + s)).2.length,
                  Nat.lt_succ_of_le (le_trans hlens (le_trans hs hd_le))⟩,
                match tgt with
                | .queryBit j => ((M.runCfg O w (t₀ + s)).2[j.val]?).getD false
                | _ => false))) := by
    intro s hs
    induction s with
    | zero =>
      refine ⟨view₀', by simpa using hrep₀', hfit₀', by simp [hbuf₀], fun tgt ↦ ?_⟩
      simp only [Nat.add_zero, hbuf₀, List.length_nil]
      cases tgt <;> rfl
    | succ s ih =>
      obtain ⟨vs, hreps, hfits, hlens, hih⟩ := ih (Nat.le_of_succ_le hs)
      obtain ⟨q, mI, mW, em, nQ, hst_s, htr_s⟩ := hd_steps s (Nat.lt_of_succ_le hs)
      let act : Action k_tapes Bool State := ⟨mI, mW, none, some nQ⟩
      let vs' := (vs.step act).summarizeOutput
      have hreps' : ViewRep vs' (M.runCfg O w (t₀ + (s + 1))).1 := by
        rw [← Nat.add_assoc, M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst_s, htr_s]
        exact hreps.step act
      obtain ⟨v_can, hrep_can, hfit_can⟩ := hview_run (t₀ + (s + 1))
      have hvs'_eq : vs' = v_can := by
        apply coreCode_injective (hreps'.input.trans hrep_can.input.symm)
        change encCore (vs'.inputPos.val, vs'.state, vs'.workTapes, vs'.output) =
          encCore (v_can.inputPos.val, v_can.state, v_can.workTapes, v_can.output)
        rw [hreps'.inputPos.trans hrep_can.inputPos.symm,
          hreps'.state.trans hrep_can.state.symm,
          funext fun i ↦ biTape_represents_unique (hreps'.workTapes i) (hrep_can.workTapes i),
          hreps'.output.trans hrep_can.output.symm]
      have hfits' : Fits Bn (registers vs') := hvs'_eq ▸ hfit_can
      have hbuf_succ : (M.runCfg O w (t₀ + (s + 1))).2 =
          (M.runCfg O w (t₀ + s)).2 ++ em.toList := by
        rw [← Nat.add_assoc, M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst_s, htr_s]
        rfl
      have hlens' : (M.runCfg O w (t₀ + (s + 1))).2.length ≤ s + 1 := by
        rw [hbuf_succ, List.length_append]
        have := em.length_toList_le
        omega
      refine ⟨vs', hreps', hfits', hlens', fun tgt ↦ ?_⟩
      have hs_lt_Nn : s < (vertexBound (k := k_tapes) Bn) :=
        lt_of_lt_of_le (Nat.lt_of_succ_le hs) hd_le
      rw [iterOpt_succ, hih tgt]
      dsimp only [Option.bind, simWpNext]
      simp only [hs_lt_Nn, ↓reduceIte, Equiv.symm_apply_apply]
      obtain ⟨q', hst_q', hval_s, hout0_s, hdec_s, hin_s, hwk_s⟩ :=
        hwork_step_exact (t₀ + s) ⟨(M.runCfg O w (t₀ + s)).2.length,
          Nat.lt_succ_of_le (le_trans hlens (le_trans (Nat.le_of_succ_le hs) hd_le))⟩
          false tgt (by simp [hst_s]) rfl vs hreps hfits
      obtain rfl : q' = q := Option.some.inj (hst_q'.symm.trans hst_s)
      rw [wpWorkStep_some]
      dsimp only []
      rw [hval_s, decide_eq_true hout0_s, Bool.and_self, ite_eq_left rfl, hdec_s]
      dsimp only []
      rw [hin_s, hwk_s, htr_s]
      dsimp only []
      have hreg_step : nextRegisters w.length (readRegisters (k :=
        k_tapes) Bn (vertexID Bn vs)) act =
          registers vs' := by
        rw [readRegisters_vertexID hfits]
        simpa [vs', hreps.input] using (registers_step vs act).symm
      have hfitB' : fitsB Bn
          (nextRegisters w.length (readRegisters (k :=
            k_tapes) Bn (vertexID Bn vs)) act) = true := by
        rw [hreg_step]; exact fitsB_eq_true.mpr hfits'
      have hlen_eq : (M.runCfg O w (t₀ + (s + 1))).2.length =
          (M.runCfg O w (t₀ + s)).2.length + (if em.isSome then 1 else 0) := by
        rw [hbuf_succ, List.length_append]
        cases em <;> simp
      have hpack_lt : Cslib.Radix.pack Bn
          (nextRegisters w.length (readRegisters (k :=
            k_tapes) Bn (vertexID Bn vs)) act) < (vertexBound (k := k_tapes) Bn) ∧
          valid (k := k_tapes) (State := State) Bn w.length
            (Cslib.Radix.pack Bn
              (nextRegisters w.length (readRegisters (k :=
                k_tapes) Bn (vertexID Bn vs)) act)) = true := by
        rw [hreg_step]
        exact ⟨vertexID_lt hfits',
          by simpa [vertexID, hreps'.input] using valid_vertexID hfits'⟩
      have hfit_pair : fitsB Bn
          (nextRegisters w.length (readRegisters (k := k_tapes) Bn (vertexID Bn vs)) act) = true ∧
          (M.runCfg O w (t₀ + s)).2.length + (if em.isSome then 1 else 0) < (vertexBound (k :=
            k_tapes) Bn) + 1 :=
        ⟨hfitB', by omega⟩
      rw [dite_eq_left hfit_pair, dite_eq_left hpack_lt]
      simp only [Option.map_some, Option.some.injEq]
      congr 2
      refine Prod.ext (Fin.ext (congrArg (Cslib.Radix.pack Bn) hreg_step))
        (Prod.ext (Fin.ext hlen_eq.symm) ?_)
      dsimp only []
      cases tgt with
      | queryBit j =>
        rw [hbuf_succ]
        cases em with
        | none => simp
        | some bit =>
          simp only [Option.toList]
          by_cases hlt_j : j.val < (M.runCfg O w (t₀ + s)).2.length
          · have hne_j : (M.runCfg O w (t₀ + s)).2.length ≠ j.val := ne_of_gt hlt_j
            rw [List.getElem?_append_left hlt_j]
            cases bit <;> simp [hne_j]
          · by_cases heq_j : (M.runCfg O w (t₀ + s)).2.length = j.val
            · rw [List.getElem?_eq_none (le_of_eq heq_j),
                List.getElem?_append_right (le_of_eq heq_j)]
              simp only [heq_j, Nat.sub_self, List.getElem?_cons_zero, Option.getD_none,
                Option.getD_some, Bool.false_or]
              cases bit <;> simp
            · rw [List.getElem?_eq_none (by omega),
                List.getElem?_eq_none (by simp; omega)]
              cases bit <;> simp [heq_j]
      | _ => simp
  obtain ⟨vd, hrepd, hfitd, hlend, hsim_d⟩ := hstep_sim d le_rfl
  have hlen_lt : (M.runCfg O w (t₀ + d)).2.length < (vertexBound (k := k_tapes) Bn) + 1 :=
    Nat.lt_succ_of_le (le_trans hlend hd_le)
  have hfreeze : ∀ (r : ℕ) (hr : d + r ≤ (vertexBound (k :=
    k_tapes) Bn)) (tgt : WPTarget (vertexBound (k := k_tapes) Bn)),
      iterOpt ((Fintype.equivFin (WPNode (vertexBound (k :=
        k_tapes) Bn))) (some (u₀, ⟨0, Nat.succ_pos (vertexBound (k :=
          k_tapes) Bn)⟩, false))) ((simWpNext M Bn w) tgt)
        (d + r) (Nat.le_succ_of_le hr) =
        some ((Fintype.equivFin (WPNode (vertexBound (k :=
          k_tapes) Bn))) (some (⟨vertexID Bn vd, vertexID_lt hfitd⟩,
          ⟨(M.runCfg O w (t₀ + d)).2.length, hlen_lt⟩,
          match tgt with
          | .queryBit j => ((M.runCfg O w (t₀ + d)).2[j.val]?).getD false
          | _ => false))) := by
    intro r hr tgt
    induction r with
    | zero => simpa using hsim_d tgt
    | succ r ih =>
      have hdr_lt : d + r < (vertexBound (k := k_tapes) Bn) := Nat.lt_of_succ_le hr
      change iterOpt _ _ ((d + r) + 1) _ = _
      rw [iterOpt_succ, ih (Nat.le_of_lt hdr_lt)]
      dsimp only [Option.bind, simWpNext]
      simp only [hdr_lt, ↓reduceIte, Equiv.symm_apply_apply]
      obtain ⟨q_end, hst_end, htr_end⟩ := hd_end
      obtain ⟨q', hst_q', hval_d, hout0_d, hdec_d, hin_d, hwk_d⟩ :=
        hwork_step_exact (t₀ + d) ⟨(M.runCfg O w (t₀ + d)).2.length, hlen_lt⟩
          false tgt (by simp [hst_end]) rfl vd hrepd hfitd
      obtain rfl : q' = q_end := Option.some.inj (hst_q'.symm.trans hst_end)
      rw [wpWorkStep_some]
      dsimp only []
      rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
      dsimp only []
      rw [hin_d, hwk_d]
      rcases htr_end with ⟨onY, onN, hq_tr⟩ | ⟨acc, hh_tr⟩
      · rw [hq_tr]; simp
      · rw [hh_tr]; simp
  refine ⟨d, hd_le, vd, hrepd, hfitd, hlen_lt, fun tgt ↦ ?_, hd_end⟩
  have := hfreeze ((vertexBound (k := k_tapes) Bn) - d) (by omega) tgt
  simpa [Nat.add_sub_of_le hd_le] using this

private theorem simRound_sim {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (H₀ : ℕ) (hhalt₀ : (M.runCfg O w H₀).1.Halted)
    (hview_run : ∀ t, ∃ view : FiniteCfg k_tapes Bool State,
      ViewRep view (M.runCfg O w t).1 ∧ Fits Bn (registers view)) :
    ∀ (t₀ : ℕ), (M.runCfg O w t₀).1.state ≠ none → (M.runCfg O w t₀).2 = [] →
      ∀ (view₀' : FiniteCfg k_tapes Bool State)
        (_hrep₀' : ViewRep view₀' (M.runCfg O w t₀).1)
        (hfit₀' : Fits Bn (registers view₀')),
        let u₀ : Fin (vertexBound (k := k_tapes) Bn) := ⟨vertexID Bn view₀', vertexID_lt hfit₀'⟩
        (∃ d ≤ vertexBound (k := k_tapes) Bn,
          (M.runCfg O w (t₀ + d + 1)).1.Halted ∧
          ((M.runCfg O w (t₀ + d + 1)).1.output = [true] ↔
            simRoundNext M O Bn w (Fin.castSucc u₀) =
              some (Fin.last (vertexBound (k := k_tapes) Bn))) ∧
          ((M.runCfg O w (t₀ + d + 1)).1.output ≠ [true] →
            simRoundNext M O Bn w (Fin.castSucc u₀) = none)) ∨
        (∃ d ≤ vertexBound (k := k_tapes) Bn, ∃ (view₁ : FiniteCfg k_tapes Bool State)
          (_hrep₁ : ViewRep view₁ (M.runCfg O w (t₀ + d + 1)).1)
          (hfit₁ : Fits Bn (registers view₁)),
          (M.runCfg O w (t₀ + d + 1)).1.state ≠ none ∧
          (M.runCfg O w (t₀ + d + 1)).2 = [] ∧
          simRoundNext M O Bn w (Fin.castSucc u₀) =
            some (Fin.castSucc ⟨vertexID Bn view₁, vertexID_lt hfit₁⟩)) := by
  classical
  intro t₀ hrun₀ hbuf₀ view₀' hrep₀' hfit₀' u₀
  have hrun_output_nil := runCfg_output_nil M O w
  have hround_unique := simRoundNext_unique M O Bn w
  have hwork_step_exact := simWorkStep_exact M O Bn w
  have hphase_sim := simPhase_sim M O Bn w H₀ hhalt₀ hview_run
  obtain ⟨d, hd_le, vd, hrepd, hfitd, hlen_lt, hiter_d, q_end, hst_end, htr_end⟩ :=
    hphase_sim t₀ hrun₀ hbuf₀ view₀' hrep₀' hfit₀'
  obtain ⟨q', hst_q', hval_d, hout0_d, hdec_d, hin_d, hwk_d⟩ :=
    hwork_step_exact (t₀ + d) ⟨(M.runCfg O w (t₀ + d)).2.length, hlen_lt⟩
      false .accHalt (by simp [hst_end]) rfl vd hrepd hfitd
  obtain rfl : q' = q_end := Option.some.inj (hst_q'.symm.trans hst_end)
  have hwp_acc_iff (tgt : WPTarget (vertexBound (k := k_tapes) Bn)) :
      (simWpAccepted M Bn w) u₀ tgt = true ↔
        wpClassifyStep M Bn w.length tgt (simSymOf k_tapes Bn w)
          (some (⟨vertexID Bn vd, vertexID_lt hfitd⟩,
            ⟨(M.runCfg O w (t₀ + d)).2.length, hlen_lt⟩,
            match tgt with
            | .queryBit j => ((M.runCfg O w (t₀ + d)).2[j.val]?).getD false
            | _ => false)) = some none := by
    dsimp only [simWpAccepted]
    rw [iterOpt_succ, hiter_d tgt]
    dsimp only [Option.bind, simWpNext]
    simp only [lt_irrefl (vertexBound (k :=
      k_tapes) Bn), ↓reduceIte, Equiv.symm_apply_apply, decide_eq_true_eq,
      Option.map_eq_some_iff, Equiv.apply_eq_iff_eq]
    exact ⟨fun ⟨_, h, he⟩ ↦ he ▸ h, fun h ↦ ⟨none, h, rfl⟩⟩
  rcases htr_end with ⟨onYes, onNo, hq_tr⟩ | ⟨acc, hh_tr⟩
  · right
    let qWord := (M.runCfg O w (t₀ + d)).2
    let nextState : State := if qWord ∈ O then onYes else onNo
    let actQ : Action k_tapes Bool State := ⟨.zero, fun _ ↦ (none, .zero), none, some nextState⟩
    let view₁ := (vd.step actQ).summarizeOutput
    have hrep₁ : ViewRep view₁ (M.runCfg O w (t₀ + d + 1)).1 := by
      rw [M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst_end, hq_tr,
        OracleMultiTapeTM.instrToAction_query]
      exact hrepd.step actQ
    obtain ⟨v_can, hrep_can, hfit_can⟩ := hview_run (t₀ + d + 1)
    have hv₁_eq : view₁ = v_can := by
      apply coreCode_injective (hrep₁.input.trans hrep_can.input.symm)
      change encCore (view₁.inputPos.val, view₁.state, view₁.workTapes, view₁.output) =
        encCore (v_can.inputPos.val, v_can.state, v_can.workTapes, v_can.output)
      rw [hrep₁.inputPos.trans hrep_can.inputPos.symm,
        hrep₁.state.trans hrep_can.state.symm,
        funext fun i ↦ biTape_represents_unique (hrep₁.workTapes i) (hrep_can.workTapes i),
        hrep₁.output.trans hrep_can.output.symm]
    have hfit₁ : Fits Bn (registers view₁) := hv₁_eq ▸ hfit_can
    have hst₁ : (M.runCfg O w (t₀ + d + 1)).1.state = some nextState := by
      rw [M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst_end, hq_tr,
        OracleMultiTapeTM.instrToAction_query]
      rfl
    have hbuf₁ : (M.runCfg O w (t₀ + d + 1)).2 = [] := by
      rw [M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst_end, hq_tr,
        OracleMultiTapeTM.instrToAction_query]
    refine ⟨d, hd_le, view₁, hrep₁, hfit₁, by simp [hst₁], hbuf₁, ?_⟩
    have hor_ans : (simRoundOracleAns M O Bn w) u₀ = decide (qWord ∈ O) := by
      let L₀ : Fin ((vertexBound (k := k_tapes) Bn) + 1) := ⟨qWord.length, hlen_lt⟩
      have hlen_iff (L : Fin ((vertexBound (k := k_tapes) Bn) + 1)) :
          (simWpAccepted M Bn w) u₀ (.queryLen L) = decide (L = L₀) := by
        rw [Bool.eq_iff_iff, hwp_acc_iff, decide_eq_true_eq, wpClassifyStep_some]
        dsimp only []
        rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
        dsimp only []
        rw [hin_d, hwk_d, hq_tr]
        dsimp only []
        split_ifs with hL
        · exact ⟨fun _ ↦ hL.symm, fun _ ↦ rfl⟩
        · exact ⟨fun h ↦ (by cases h), fun h ↦ (hL h.symm).elim⟩
      have hbit_eq (j : Fin L₀.val) :
          (simWpAccepted M Bn w) u₀ (.queryBit
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp L₀.isLt)⟩) =
            qWord[j.val]'j.isLt := by
        rw [Bool.eq_iff_iff, hwp_acc_iff, wpClassifyStep_some]
        dsimp only []
        rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
        dsimp only []
        rw [hin_d, hwk_d, hq_tr]
        dsimp only []
        simp only [qWord, List.getElem?_eq_getElem j.isLt, Option.getD_some]
        cases (M.runCfg O w (t₀ + d)).2[j.val]'j.isLt <;> simp
      dsimp only [simRoundOracleAns]
      rw [Bool.eq_iff_iff, List.any_eq_true]
      simp only [List.mem_ofFn, id_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨_, ⟨L, rfl⟩, hboth⟩
        rw [Bool.and_eq_true] at hboth
        have hL_eq : L = L₀ := of_decide_eq_true ((hlen_iff L) ▸ hboth.1)
        subst hL_eq
        rw [Language.slice_eq_true_iff] at hboth
        have hword_eq : (List.ofFn fun j : Fin L₀.val ↦
            (simWpAccepted M Bn w) u₀ (.queryBit ⟨j.val, _⟩)) = qWord :=
          (congrArg List.ofFn (funext hbit_eq)).trans List.ofFn_getElem
        rw [hword_eq] at hboth
        exact hboth.2
      · intro hmem
        refine ⟨true, ⟨L₀, ?_⟩, rfl⟩
        rw [hlen_iff L₀, decide_eq_true (rfl : L₀ = L₀), Bool.true_and,
          Language.slice_eq_true_iff]
        have hword_eq : (List.ofFn fun j : Fin L₀.val ↦
            (simWpAccepted M Bn w) u₀ (.queryBit ⟨j.val, _⟩)) = qWord :=
          (congrArg List.ofFn (funext hbit_eq)).trans List.ofFn_getElem
        rwa [hword_eq]
    let v₁ : Fin (vertexBound (k := k_tapes) Bn) := ⟨vertexID Bn view₁, vertexID_lt hfit₁⟩
    have hstep_v₁ : (simRoundStepBool M O Bn w) u₀ v₁ = true := by
      dsimp only [simRoundStepBool]
      rw [hor_ans]
      have hreg₁ : nextRegisters w.length
          (readRegisters (k := k_tapes) Bn (vertexID Bn vd)) actQ = registers view₁ := by
        rw [readRegisters_vertexID hfitd]
        simpa [view₁, hrepd.input] using (registers_step vd actQ).symm
      have hv₁_val : valid (k := k_tapes) (State := State) Bn w.length v₁.val = true := by
        simpa [v₁, hrep₁.input] using valid_vertexID hfit₁
      by_cases hmem : qWord ∈ O
      · simp only [hmem, decide_true, Bool.and_true, Bool.not_true, Bool.and_false, Bool.or_false]
        rw [hwp_acc_iff, wpClassifyStep_some]
        dsimp only []
        rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
        dsimp only []
        rw [hin_d, hwk_d, hq_tr]
        dsimp only []
        have hact_eq : (⟨.zero, fun _ ↦ (none, .zero), none, some onYes⟩ :
            Action k_tapes Bool State) = actQ := by
          dsimp [actQ, nextState]; simp [hmem]
        rw [hact_eq, hreg₁, fitsB_eq_true.mpr hfit₁, hv₁_val]
        simp [v₁, vertexID]
      · simp only [hmem, decide_false, Bool.and_false, Bool.not_false, Bool.and_true,
          Bool.false_or]
        rw [hwp_acc_iff, wpClassifyStep_some]
        dsimp only []
        rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
        dsimp only []
        rw [hin_d, hwk_d, hq_tr]
        dsimp only []
        have hact_eq : (⟨.zero, fun _ ↦ (none, .zero), none, some onNo⟩ :
            Action k_tapes Bool State) = actQ := by
          dsimp [actQ, nextState]; simp [hmem]
        rw [hact_eq, hreg₁, fitsB_eq_true.mpr hfit₁, hv₁_val]
        simp [v₁, vertexID]
    have huniq_v₁ := hround_unique u₀ (Fin.castSucc v₁)
    simp only [Fin.val_castSucc, v₁.isLt, ↓reduceDIte] at huniq_v₁
    have hfin : (⟨v₁.val, v₁.isLt⟩ : Fin (vertexBound (k := k_tapes) Bn)) = v₁ := Fin.ext rfl
    rw [hfin, hstep_v₁] at huniq_v₁
    exact (of_decide_eq_true huniq_v₁.symm)
  · left
    have hhalt_d1 : (M.runCfg O w (t₀ + d + 1)).1.Halted ∧
        (M.runCfg O w (t₀ + d + 1)).1.output = [acc] := by
      rw [M.runCfg_succ, M.stepCfg_of_state_eq_some _ hst_end, hh_tr]
      have hnil := hrun_output_nil (t₀ + d) (by simp [hst_end])
      exact ⟨rfl, by simp [Action.apply, hnil]⟩
    have hacc_bool : (simRoundAccBool M Bn w) u₀ = acc := by
      dsimp only [simRoundAccBool]
      rw [Bool.eq_iff_iff, hwp_acc_iff, wpClassifyStep_some]
      dsimp only []
      rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
      dsimp only []
      rw [hin_d, hwk_d, hh_tr]
      cases acc <;> simp
    have hno_step (v : Fin (vertexBound (k :=
      k_tapes) Bn)) : (simRoundStepBool M O Bn w) u₀ v = false := by
      dsimp only [simRoundStepBool]
      have hy_f : (simWpAccepted M Bn w) u₀ (.yesTarget v) = false := by
        rw [Bool.eq_false_iff, ne_eq, hwp_acc_iff, wpClassifyStep_some]
        dsimp only []
        rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
        dsimp only []
        rw [hin_d, hwk_d, hh_tr]
        cases acc <;> simp
      have hn_f : (simWpAccepted M Bn w) u₀ (.noTarget v) = false := by
        rw [Bool.eq_false_iff, ne_eq, hwp_acc_iff, wpClassifyStep_some]
        dsimp only []
        rw [hval_d, decide_eq_true hout0_d, Bool.and_self, ite_eq_left rfl, hdec_d]
        dsimp only []
        rw [hin_d, hwk_d, hh_tr]
        cases acc <;> simp
      simp [hy_f, hn_f]
    refine ⟨d, hd_le, hhalt_d1.1, ?_, ?_⟩
    · rw [hhalt_d1.2]
      have hlast_u := hround_unique u₀ (Fin.last (vertexBound (k := k_tapes) Bn))
      simp only [Fin.val_last, lt_irrefl (vertexBound (k :=
        k_tapes) Bn), ↓reduceDIte, hacc_bool] at hlast_u
      cases acc <;> simpa using hlast_u
    · rw [hhalt_d1.2]
      intro hnot
      have hacc_f : acc = false := by cases acc <;> simp at hnot ⊢
      subst hacc_f
      dsimp only [simRoundNext]
      have hu_lt : (Fin.castSucc u₀).val < (vertexBound (k := k_tapes) Bn) := u₀.isLt
      have hu_eq : (⟨(Fin.castSucc u₀).val, hu_lt⟩ : Fin (vertexBound (k := k_tapes) Bn)) = u₀ :=
        Fin.ext rfl
      simp only [hu_lt, ↓reduceDIte, hu_eq, hacc_bool, Bool.false_eq_true, ↓reduceIte,
        Option.map_eq_none_iff, List.find?_eq_none]
      intro v _
      simp [hno_step v]

private theorem simHalted_within_rounds {k_tapes : ℕ} {State : Type} [Fintype State]
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (Bn : ℕ) (w : List Bool)
    (H₀ : ℕ) (hhalt₀ : (M.runCfg O w H₀).1.Halted)
    (hview_run : ∀ t, ∃ view : FiniteCfg k_tapes Bool State,
      ViewRep view (M.runCfg O w t).1 ∧ Fits Bn (registers view))
    (hfit_init : Fits Bn (registers (M.envelopeNTM.initView w))) :
    ∃ t_halt, (M.runCfg O w t_halt).1.Halted ∧
      (((M.runCfg O w t_halt).1.output = [true] ∧
        iterOpt
          (Fin.castSucc
            (⟨vertexID Bn (M.envelopeNTM.initView w), vertexID_lt hfit_init⟩ :
              Fin (vertexBound (k := k_tapes) Bn)))
          (fun _ ↦ simRoundNext M O Bn w) (vertexBound (k := k_tapes) Bn + 1) le_rfl =
          some (Fin.last (vertexBound (k := k_tapes) Bn))) ∨
       ((M.runCfg O w t_halt).1.output ≠ [true] ∧
        iterOpt
          (Fin.castSucc
            (⟨vertexID Bn (M.envelopeNTM.initView w), vertexID_lt hfit_init⟩ :
              Fin (vertexBound (k := k_tapes) Bn)))
          (fun _ ↦ simRoundNext M O Bn w) (vertexBound (k := k_tapes) Bn + 1) le_rfl = none)) := by
  let startU : Fin (vertexBound (k := k_tapes) Bn) :=
    ⟨vertexID Bn (M.envelopeNTM.initView w), vertexID_lt hfit_init⟩
  have hrun_stay {t₁ t₂} := @runCfg_stay_of_halted _ _ M O w t₁ t₂
  have hround_sim := simRound_sim M O Bn w H₀ hhalt₀ hview_run
  have hrep_init : ViewRep (M.envelopeNTM.initView w) (M.runCfg O w 0).1 :=
    (simInit_viewRep_fits M O Bn w hview_run).1
  have hrounds_sim :
      ∀ (r : ℕ) (hr : r ≤ (vertexBound (k := k_tapes) Bn) + 1),
        (∃ t_halt, (M.runCfg O w t_halt).1.Halted ∧
          (((M.runCfg O w t_halt).1.output = [true] ∧
            iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) r hr =
              some (Fin.last (vertexBound (k := k_tapes) Bn))) ∨
           ((M.runCfg O w t_halt).1.output ≠ [true] ∧
            iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) r hr = none))) ∨
        (∃ t_r ≥ r, ∃ (vr : FiniteCfg k_tapes Bool State)
          (hrepr : ViewRep vr (M.runCfg O w t_r).1)
          (hfitr : Fits Bn (registers vr)),
          (M.runCfg O w t_r).1.state ≠ none ∧
          (M.runCfg O w t_r).2 = [] ∧
          iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) r hr =
            some (Fin.castSucc ⟨vertexID Bn vr, vertexID_lt hfitr⟩)) := by
    intro r hr
    induction r with
    | zero =>
      right
      refine ⟨0, Nat.zero_le _, M.envelopeNTM.initView w, hrep_init, hfit_init,
        by simp [Cfg.init], rfl, rfl⟩
    | succ r ih =>
      rcases ih (Nat.le_of_succ_le hr) with
        ⟨t_halt, hhalt_t, ⟨hyes_t, hit_t⟩ | ⟨hno_t, hit_t⟩⟩ |
        ⟨t_r, _, vr, hrepr, hfitr, hrun_r, hbuf_r, hit_r⟩
      · left
        refine ⟨t_halt, hhalt_t, Or.inl ⟨hyes_t, ?_⟩⟩
        rw [iterOpt_succ, hit_t]
        simp [simRoundNext]
      · left
        refine ⟨t_halt, hhalt_t, Or.inr ⟨hno_t, ?_⟩⟩
        rw [iterOpt_succ, hit_t]
        rfl
      · rcases hround_sim t_r hrun_r hbuf_r vr hrepr hfitr with
          ⟨d, _, hhalt_d, hyes_iff, hno_imp⟩ |
          ⟨d, _, vr1, hrepr1, hfitr1, hrun_r1, hbuf_r1, hnext_r1⟩
        · left
          refine ⟨t_r + d + 1, hhalt_d, ?_⟩
          by_cases hout_d : (M.runCfg O w (t_r + d + 1)).1.output = [true]
          · refine Or.inl ⟨hout_d, ?_⟩
            rw [iterOpt_succ, hit_r]
            exact hyes_iff.mp hout_d
          · refine Or.inr ⟨hout_d, ?_⟩
            rw [iterOpt_succ, hit_r]
            exact hno_imp hout_d
        · right
          refine ⟨t_r + d + 1, by omega, vr1, hrepr1, hfitr1, hrun_r1, hbuf_r1, ?_⟩
          rw [iterOpt_succ, hit_r]
          exact hnext_r1
  rcases hrounds_sim ((vertexBound (k :=
    k_tapes) Bn) + 1) le_rfl with hdone | ⟨_, _, _, _, hfit_end, _, _, hit_end⟩
  · exact hdone
  · exfalso
    have hall_active : ∀ s : Fin ((vertexBound (k := k_tapes) Bn) + 1),
        ∃ (ts : ℕ) (vs : FiniteCfg k_tapes Bool State)
          (hreps : ViewRep vs (M.runCfg O w ts).1)
          (hfits : Fits Bn (registers vs)),
          (M.runCfg O w ts).1.state ≠ none ∧
          (M.runCfg O w ts).2 = [] ∧
          iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) s.val
            (Nat.le_succ_of_le (Nat.lt_succ_iff.mp s.isLt)) =
            some (Fin.castSucc ⟨vertexID Bn vs, vertexID_lt hfits⟩) := by
      intro s
      have hiter_congr : ∀ (n' : ℕ) (hn' : n' ≤ (vertexBound (k := k_tapes) Bn) + 1),
          n' = (vertexBound (k := k_tapes) Bn) + 1 →
          iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) n' hn' =
            iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w))
              ((vertexBound (k := k_tapes) Bn) + 1) le_rfl := by
        rintro _ _ rfl; rfl
      rcases hrounds_sim s.val (Nat.le_succ_of_le (Nat.lt_succ_iff.mp s.isLt)) with
        ⟨_, _, ⟨_, hit_s⟩ | ⟨_, hit_s⟩⟩ | ⟨ts, _, vs, hreps, hfit_s, hruns, hbufs, hit_s⟩
      · have hstay_last : ∀ m (hm : s.val + m ≤ (vertexBound (k := k_tapes) Bn) + 1),
            iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) (s.val + m) hm =
              some (Fin.last (vertexBound (k := k_tapes) Bn)) := by
          intro m hm
          induction m with
          | zero => exact hit_s
          | succ m ih =>
            change iterOpt _ _ ((s.val + m) + 1) hm = _
            rw [iterOpt_succ, ih (Nat.le_of_succ_le hm)]
            simp [simRoundNext]
        have hend := hstay_last ((vertexBound (k := k_tapes) Bn) + 1 - s.val)
          (by have := s.isLt; omega)
        have hidx_eq : s.val + ((vertexBound (k := k_tapes) Bn) + 1 - s.val) =
            (vertexBound (k := k_tapes) Bn) + 1 := by
          have := s.isLt; omega
        rw [hiter_congr _ _ hidx_eq, hit_end] at hend
        have := congrArg Fin.val (Option.some.inj hend)
        simp only [Fin.val_castSucc, Fin.val_last] at this
        exact absurd this (ne_of_lt (vertexID_lt hfit_end))
      · have hstay_none : ∀ m (hm : s.val + m ≤ (vertexBound (k := k_tapes) Bn) + 1),
            iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) (s.val + m) hm =
              none := by
          intro m hm
          induction m with
          | zero => exact hit_s
          | succ m ih =>
            change iterOpt _ _ ((s.val + m) + 1) hm = _
            rw [iterOpt_succ, ih (Nat.le_of_succ_le hm)]
            rfl
        have hend := hstay_none ((vertexBound (k := k_tapes) Bn) + 1 - s.val)
          (by have := s.isLt; omega)
        have hidx_eq : s.val + ((vertexBound (k := k_tapes) Bn) + 1 - s.val) =
            (vertexBound (k := k_tapes) Bn) + 1 := by
          have := s.isLt; omega
        rw [hiter_congr _ _ hidx_eq, hit_end] at hend
        cases hend
      · exact ⟨ts, vs, hreps, hfit_s, hruns, hbufs, hit_s⟩
    choose _ vR _ hfitR _ _ hitR using hall_active
    let uR (s : Fin ((vertexBound (k := k_tapes) Bn) + 1)) : Fin (vertexBound (k := k_tapes) Bn) :=
      ⟨vertexID Bn (vR s), vertexID_lt (hfitR s)⟩
    have hnot_inj : ¬Function.Injective uR := fun hinj ↦ by
      have := Fintype.card_le_of_injective uR hinj
      simp only [Fintype.card_fin] at this
      omega
    simp only [Function.Injective, not_forall] at hnot_inj
    obtain ⟨s₁, s₂, hu_eq, hs_ne⟩ := hnot_inj
    obtain ⟨a, b, hab, ha_le, hb_le, hit_eq⟩ :
        ∃ (a b : ℕ) (_ : a < b) (ha_le : a ≤ (vertexBound (k := k_tapes) Bn))
          (hb_le : b ≤ (vertexBound (k := k_tapes) Bn)),
          iterOpt (Fin.castSucc startU)
            (fun _ ↦ (simRoundNext M O Bn w)) a (Nat.le_succ_of_le ha_le) =
            iterOpt (Fin.castSucc startU)
              (fun _ ↦ (simRoundNext M O Bn w)) b (Nat.le_succ_of_le hb_le) := by
      rcases lt_or_gt_of_ne (fun h ↦ hs_ne (Fin.ext h)) with hlt | hgt
      · refine ⟨s₁.val, s₂.val, hlt, Nat.lt_succ_iff.mp s₁.isLt, Nat.lt_succ_iff.mp s₂.isLt, ?_⟩
        rw [hitR s₁, hitR s₂]
        exact congrArg (some ∘ Fin.castSucc) hu_eq
      · refine ⟨s₂.val, s₁.val, hgt, Nat.lt_succ_iff.mp s₂.isLt, Nat.lt_succ_iff.mp s₁.isLt, ?_⟩
        rw [hitR s₂, hitR s₁]
        exact congrArg (some ∘ Fin.castSucc) hu_eq.symm
    let iterInf (m : ℕ) : Option (Fin ((vertexBound (k := k_tapes) Bn) + 1)) :=
      Nat.rec (some (Fin.castSucc startU)) (fun _ acc ↦ acc.bind (simRoundNext M O Bn w)) m
    have hiter_eq : ∀ s (hs : s ≤ (vertexBound (k := k_tapes) Bn) + 1),
        iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w)) s hs = iterInf s := by
      intro s hs
      induction s with
      | zero => rfl
      | succ s ih =>
        rw [iterOpt_succ]
        change (iterOpt (Fin.castSucc startU) (fun _ ↦ (simRoundNext M O Bn w))
          s (Nat.le_of_succ_le hs)).bind (simRoundNext M O Bn w) =
          (iterInf s).bind (simRoundNext M O Bn w)
        rw [ih (Nat.le_of_succ_le hs)]
    have hinf_ab : iterInf a = iterInf b := by
      rw [← hiter_eq a (Nat.le_succ_of_le ha_le), ← hiter_eq b (Nat.le_succ_of_le hb_le), hit_eq]
    have hinf_cycle : ∀ m, iterInf (a + m * (b - a)) = iterInf a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hshift : ∀ k, iterInf (a + m * (b - a) + k) = iterInf (a + k) := by
          intro k
          induction k with
          | zero => simpa using ih
          | succ k ihk =>
            change (iterInf (a + m * (b - a) + k)).bind (simRoundNext M O Bn w) =
              (iterInf (a + k)).bind (simRoundNext M O Bn w)
            rw [ihk]
        have := hshift (b - a)
        rw [Nat.add_sub_cancel' (le_of_lt hab), ← hinf_ab] at this
        simpa [Nat.succ_mul, Nat.add_assoc] using this
    have hrounds_inf' : ∀ r : ℕ,
        (iterInf r = some (Fin.last (vertexBound (k := k_tapes) Bn)) ∨ iterInf r = none) ∨
        (∃ t_r ≥ r, ∃ (vr : FiniteCfg k_tapes Bool State)
          (hrepr : ViewRep vr (M.runCfg O w t_r).1)
          (hfitr : Fits Bn (registers vr)),
          (M.runCfg O w t_r).1.state ≠ none ∧
          (M.runCfg O w t_r).2 = [] ∧
          iterInf r = some (Fin.castSucc ⟨vertexID Bn vr, vertexID_lt hfitr⟩)) := by
      intro r
      induction r with
      | zero =>
        right
        exact ⟨0, Nat.zero_le _, M.envelopeNTM.initView w, hrep_init,
          hfit_init, by simp [Cfg.init], rfl, rfl⟩
      | succ r ih =>
        rcases ih with (hlast | hnone) | ⟨tr, htr_ge, vr, hrepr, hfitr, hrun_r, hbuf_r, hit_r⟩
        · left; left
          change (iterInf r).bind (simRoundNext M O Bn w) = _
          rw [hlast]; simp [simRoundNext]
        · left; right
          change (iterInf r).bind (simRoundNext M O Bn w) = none
          rw [hnone]; rfl
        · rcases hround_sim tr hrun_r hbuf_r vr hrepr hfitr with
            ⟨d, _, _, hyes_iff, hno_imp⟩ |
            ⟨d, _, vr1, hrepr1, hfitr1, hrun_r1, hbuf_r1, hnext_r1⟩
          · left
            by_cases hout_d : (M.runCfg O w (tr + d + 1)).1.output = [true]
            · left
              change (iterInf r).bind (simRoundNext M O Bn w) = _
              rw [hit_r]; exact hyes_iff.mp hout_d
            · right
              change (iterInf r).bind (simRoundNext M O Bn w) = none
              rw [hit_r]; exact hno_imp hout_d
          · right
            refine ⟨tr + d + 1, by omega, vr1, hrepr1, hfitr1, hrun_r1, hbuf_r1, ?_⟩
            change (iterInf r).bind (simRoundNext M O Bn w) = _
            rw [hit_r]; exact hnext_r1
    let rBig := a + (H₀ + 1) * (b - a)
    have hrBig_ge : H₀ ≤ rBig := by
      have : 1 ≤ b - a := Nat.sub_pos_of_lt hab
      dsimp only [rBig]
      nlinarith
    have hinf_rBig : iterInf rBig =
        some (Fin.castSucc (uR ⟨a, Nat.lt_succ_of_le ha_le⟩)) := by
      dsimp only [rBig]
      rw [hinf_cycle (H₀ + 1), ← hiter_eq a (Nat.le_succ_of_le ha_le),
        hitR ⟨a, Nat.lt_succ_of_le ha_le⟩]
    rcases hrounds_inf' rBig with (hlast | hnone) | ⟨tr, htr_ge, _, _, _, hrun_tr, _, _⟩
    · rw [hinf_rBig] at hlast
      have := congrArg Fin.val (Option.some.inj hlast)
      simp only [Fin.val_castSucc, Fin.val_last] at this
      exact absurd this (ne_of_lt (uR _).isLt)
    · rw [hinf_rBig] at hnone; cases hnone
    · have hh_tr : (M.runCfg O w tr).1.Halted :=
        (congrArg (fun p ↦ p.1.Halted) (hrun_stay (le_trans hrBig_ge htr_ge) hhalt₀)).mpr hhalt₀
      exact hrun_tr hh_tr

end Simulation

/-- **Relativized $\mathrm{L}^O \subseteq \mathrm{DET}_k$ whenever $O \in \mathrm{DET}_k$**:
for every $k \ge 2$ and every oracle language $O \in \mathrm{DET}_k$, every problem decided in
deterministic logarithmic space with oracle $O$ lies in $\mathrm{DET}_k$. -/
theorem LOracle_subset_DETkOn {k : ℕ} (hk : 2 ≤ k) {O : Language Bool} (hO : O ∈ DETk k)
    {α : Type} {enc : α ↪ List Bool} :
    LOracle O enc ⊆ DETkOn k enc := by
  obtain ⟨CO, cO, sO, hsO, hCO⟩ := hO
  rintro A ⟨k_tapes, State, hfinite, M, c, hM⟩
  classical
  let _ : Fintype State := Fintype.ofFinite State
  have hL_mem : buntrockCircuitLanguage k CO M c ∈ DETk k :=
    buntrockCircuitLanguage_mem_DETk k CO hsO
      (fun q ↦ ⟨(hCO q).1, (hCO q).2.1, (hCO q).2.2.1⟩) M c
  refine ⟨buntrockCircuitLanguage k CO M c, hL_mem, fun a ↦ ?_⟩
  obtain ⟨hspace, ⟨H₀, hhalt₀⟩, hA_iff⟩ := hM a
  rw [hA_iff]
  let w := enc a
  let Bn := radix (radixExponent State c) w.length
  have hview_run := exists_viewRep_fits_radix M O c w hspace
  have hfit_init : Fits Bn (registers (M.envelopeNTM.initView w)) :=
    (simInit_viewRep_fits M O Bn w hview_run).2
  let startU : Fin (vertexBound (k := k_tapes) Bn) :=
    ⟨vertexID Bn (M.envelopeNTM.initView w), vertexID_lt hfit_init⟩
  have heval_wp (u₀ : Fin (vertexBound (k := k_tapes) Bn))
      (tgt : WPTarget (vertexBound (k := k_tapes) Bn)) :
      (buntrockLayer1Circuit k M Bn w.length u₀ tgt).eval
        (oracleInterpretation (detZModLanguage k)) (fun i : Fin w.length ↦ w[i.val]) 0 =
        simWpAccepted M Bn w u₀ tgt := by
    have h := eval_buntrockLayer1Circuit hk M Bn w u₀ tgt
    dsimp only [] at h
    rw [h]
    dsimp only [simWpAccepted]
    congr 2
    refine congrArg (fun f ↦ iterOpt _ f _ _) (funext fun s ↦ funext fun i ↦ ?_)
    dsimp only [simWpNext, simSymOf]
    cases tgt <;> rfl
  change (∃ t, (M.runCfg O w t).1.Halted ∧ (M.runCfg O w t).1.output = [true]) ↔
    (buildBuntrockCircuit k CO M c w.length).eval
      (oracleInterpretation (detZModLanguage k)) (fun i : Fin w.length ↦ w[i.val]) 0 = true
  rw [eval_buildBuntrockCircuit_eq hk CO (fun q ↦ (hCO q).2.2.2) M c w
    (simWpAccepted M Bn w) heval_wp
    (simRoundNext M O Bn w) (by simp [simRoundNext, Bn]) (simRoundNext_unique M O Bn w)
    startU (vertexID_init M.envelopeNTM Bn w), decide_eq_true_eq]
  have hrun_stay {t₁ t₂} := @runCfg_stay_of_halted _ _ M O w t₁ t₂
  obtain ⟨t_halt, hhalt_th, ⟨hyes_th, hit_last⟩ | ⟨hno_th, hit_none⟩⟩ :=
    simHalted_within_rounds M O Bn w H₀ hhalt₀ hview_run hfit_init
  · rw [hit_last]
    exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨t_halt, hhalt_th, hyes_th⟩⟩
  · rw [hit_none]
    simp only [reduceCtorEq, iff_false, not_exists, not_and]
    intro t hht hout_t
    have hm1 := hrun_stay (le_max_left t t_halt) hht
    have hm2 := hrun_stay (le_max_right t t_halt) hhalt_th
    have heq : (M.runCfg O w t).1.output = (M.runCfg O w t_halt).1.output := by
      rw [← hm1, hm2]
    exact hno_th (heq ▸ hout_t)

/-- **Buntrock--Damm--Hertrampf--Meinel Theorem**: for every modulus `k ≥ 2`,
$\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}} \subseteq \mathrm{DET}_k$ on all encoded decision problems.
-/
theorem LModL_subset_DETkOn {k : ℕ} (hk : 2 ≤ k) {α : Type} {enc : α ↪ List Bool} :
    LModL k enc ⊆ DETkOn k enc := by
  rintro A ⟨O, hO_mod, hA_lor⟩
  exact LOracle_subset_DETkOn hk (ModL_encBits_subset_DETk hk hO_mod) hA_lor

/-- Bitstring-language form of $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}} \subseteq \mathrm{DET}_k$ for
every modulus `k ≥ 2`. -/
theorem LModL_encBits_subset_DETk {k : ℕ} (hk : 2 ≤ k) :
    LModL k MultiTapeTM.encBits ⊆ DETk k := by
  intro L hL
  exact (mem_DETkOn_encBits_iff (k := k) (A := L)).mp (LModL_subset_DETkOn hk hL)

/-- **$\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}} \subseteq \mathrm{DET}$** for every modulus `k ≥ 2`. -/
theorem LModL_subset_DETOn {k : ℕ} (hk : 2 ≤ k) {α : Type} {enc : α ↪ List Bool} :
    LModL k enc ⊆ DETOn enc :=
  (LModL_subset_DETkOn hk).trans (DETkOn_subset_DETOn hk enc)

end BuntrockTheorem

/-! ### Private sanity check -/

section Sanity

private example {L : Language Bool} (h : L ∈ LModL 2 MultiTapeTM.encBits) :
    L ∈ DETk 2 ∧ L ∈ DET :=
  ⟨LModL_encBits_subset_DETk (by decide) h,
   DETk_subset_DET (by decide) (LModL_encBits_subset_DETk (by decide) h)⟩

end Sanity

end Cslib.Complexity
