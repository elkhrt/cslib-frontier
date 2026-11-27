/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.SAT

import CslibFrontier.Computability.Complexity.Problems.BipartitePerfectMatching.Membership
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.Vars
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fintype

/-!
# Tovey's Theorem: `2`-Occurrence `SAT` is in `P`

This module proves Tovey's theorem (`TwoOccurrenceSAT ∈ P encCNF`): deciding satisfiability
of a CNF formula in which every variable occurs in at most `2` clauses is in deterministic
polynomial time.

After removing tautological clauses (`c` containing both `(v, true)` and `(v, false)`) and
iteratively eliminating pure literals (`v` occurring with only one polarity across remaining
clauses), every remaining variable occurs once positively and once negatively across two distinct
clauses. Satisfiability of the residual formula is then equivalent to the existence of a left-total
clause-to-variable matching, decided in polynomial time via
`Cslib.Complexity.BipartitePerfectMatching.decider`.

## Main definitions

* `CslibFrontier.Complexity.TwoOccurrenceSAT`: satisfiable CNF formulas over `ℕ` in which every
  variable occurs in at most `2` clauses.
* `CslibFrontier.Complexity.twoOccurrenceDecider`: deterministic polynomial-time decider for `CNF`
  formulas with `≤ 2` clause occurrences per variable.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_twoOccurrenceDecider`: polynomial-time
  computability of `twoOccurrenceDecider`.
* `CslibFrontier.Complexity.twoOccurrenceDecider_eq_true_iff`: correctness on all CNF formulas with
  `≤ 2` occurrences per variable.
* `CslibFrontier.Complexity.twoOccurrenceSAT_mem_P`: `TwoOccurrenceSAT ∈ P encCNF`.
-/

public section

namespace CslibFrontier.Complexity

open Finset Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- `TwoOccurrenceSAT`: satisfiable CNF formulas in which every variable occurs in at most `2`
clauses.
-/
def TwoOccurrenceSAT : Set (CNF ℕ) :=
  {φ | (∀ v, φ.occurrences v ≤ 2) ∧ φ.Satisfiable}

/-- Boolean guard checking that every variable occurring in `φ` appears in at most `2` clauses. -/
def checkMaxTwoOcc (φ : CNF ℕ) : Bool :=
  φ.distinctVars.all fun v =>
    decide ((φ.countP fun c => c.any fun l => decide (l.1 = v)) ≤ 2)

/-- Remove tautological clauses (`c` containing both `(v, true)` and `(v, false)`). -/
def removeTautologies (φ : CNF ℕ) : CNF ℕ :=
  φ.filter fun c => !(c.any fun l => c.contains (l.1, !l.2))

/-- Test whether variable `v` is pure in `ψ` (occurs with at most one polarity across `ψ`). -/
def isPureVar (ψ : CNF ℕ) (v : ℕ) : Bool :=
  !(ψ.any fun c => c.contains (v, false)) || !(ψ.any fun c => c.contains (v, true))

/-- One step of pure-literal elimination: remove all clauses containing the first pure variable in
`ψ.distinctVars`, if any. -/
def pureStep (ψ : CNF ℕ) : CNF ℕ :=
  match (ψ.distinctVars.filter (isPureVar ψ)).head? with
  | none => ψ
  | some v => ψ.filter fun c => !(c.any fun l => decide (l.1 = v))

/-- Iterated pure-literal elimination after tautology removal. -/
def pureElim (φ : CNF ℕ) : CNF ℕ :=
  pureStep^[(removeTautologies φ).length] (removeTautologies φ)

/-- Encode a pure-literal-free `2`-occurrence CNF `ψ` as an `n × n` row-major bipartite-matching
word (`n = ψ.distinctVars.length`), padded with `n - ψ.length` all-`true` rows when `ψ.length ≤ n`,
or the non-square word `[false, false]` when `n < ψ.length`. -/
def toMatchingWord (ψ : CNF ℕ) : List Bool :=
  let dvars := ψ.distinctVars
  let n := dvars.length
  if n < ψ.length then
    [false, false]
  else
    (List.range n).flatMap fun u =>
      (List.range n).map fun j =>
        if u < ψ.length then
          (ψ.getD u []).any fun l => decide (l.1 = dvars.getD j 0)
        else
          true

/-- Polynomial-time decider for `CNF` formulas with at most `2` occurrences per variable. -/
def twoOccurrenceDecider (φ : CNF ℕ) : Bool :=
  BipartitePerfectMatching.decider (toMatchingWord (pureElim φ))

private theorem sublist_countP_le {α : Type*} {l₁ l₂ : List α} (h : List.Sublist l₁ l₂)
    (p : α → Bool) : l₁.countP p ≤ l₂.countP p := by
  induction h with
  | slnil => rfl
  | cons _ _ ih => simp only [List.countP_cons]; split_ifs <;> omega
  | cons_cons _ _ ih => simp only [List.countP_cons]; split_ifs <;> omega

private theorem pureStep_sublist (ψ : CNF ℕ) : List.Sublist (pureStep ψ) ψ := by
  unfold pureStep
  rcases (ψ.distinctVars.filter (isPureVar ψ)).head? with _ | v
  · exact List.Sublist.refl _
  · exact List.filter_sublist

private theorem pureStep_iterate_sublist (k : ℕ) (ψ : CNF ℕ) : List.Sublist (pureStep^[k] ψ) ψ := by
  induction k generalizing ψ with
  | zero => exact List.Sublist.refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (pureStep ψ)).trans (pureStep_sublist ψ)

/-- `twoOccurrenceDecider` runs in deterministic polynomial time. -/
theorem computableInPolyTime_twoOccurrenceDecider :
    ComputableInPolyTime twoOccurrenceDecider encCNF encBool := by
  have hrem : ComputableInPolyTime removeTautologies encCNF encCNF := by
    unfold removeTautologies; fun_prop
  have hpure : ComputableInPolyTime (fun p : CNF ℕ × ℕ => isPureVar p.1 p.2)
      (encPair encCNF encNat) encBool := by
    unfold isPureVar; fun_prop
  have hstep : ComputableInPolyTime pureStep encCNF encCNF := by
    have hhead : ComputableInPolyTime
        (fun ψ : CNF ℕ => (ψ.distinctVars.filter (isPureVar ψ)).head?)
        encCNF (encOption encNat) :=
      (head? encNat).comp (filterWithInput SAT.computableInPolyTime_distinctVars hpure)
    have heq : pureStep = fun ψ : CNF ℕ =>
        let opt := (ψ.distinctVars.filter (isPureVar ψ)).head?
        if opt.isSome then
          ψ.filter fun c => !(c.any fun l => decide (l.1 = opt.getD 0))
        else
          ψ := by
      funext ψ; unfold pureStep
      rcases (ψ.distinctVars.filter (isPureVar ψ)).head? with _ | v <;> rfl
    rw [heq]; fun_prop
  have helim : ComputableInPolyTime pureElim encCNF encCNF := by
    unfold pureElim
    refine ComputableInPolyTime.iterate
      (SAT.computableInPolyTime_length hrem) hrem hstep
      (bound := fun φ => (encCNF φ).length) PolyBounded.self fun φ i _ => ?_
    have hsub : List.Sublist (pureStep^[i] (removeTautologies φ)) φ :=
      (pureStep_iterate_sublist i (removeTautologies φ)).trans List.filter_sublist
    exact length_encList_sublist (encList (encPair encNat encBool)) hsub
  have hword_framed : ComputableInPolyTime toMatchingWord encCNF (encList encBool) := by
    have hdv : ComputableInPolyTime CNF.distinctVars encCNF (encList encNat) :=
      SAT.computableInPolyTime_distinctVars
    have hn : ComputableInPolyTime (fun ψ : CNF ℕ => ψ.distinctVars.length) encCNF encUnary :=
      (length_list encNat).comp hdv
    have hm : ComputableInPolyTime (fun ψ : CNF ℕ => ψ.length) encCNF encUnary :=
      SAT.computableInPolyTime_length id'
    have hrng : ComputableInPolyTime (fun ψ : CNF ℕ => List.range ψ.distinctVars.length)
        encCNF (encList encUnary) := by fun_prop
    have hcell : ComputableInPolyTime
        (fun q : (CNF ℕ × ℕ) × ℕ =>
          if q.1.2 < q.1.1.length then
            (q.1.1.getD q.1.2 []).any fun l => decide (l.1 = q.1.1.distinctVars.getD q.2 0)
          else true)
        (encPair (encPair encCNF encUnary) encUnary) encBool := by
      have hψ := (fst encCNF encUnary).comp (fst (encPair encCNF encUnary) encUnary)
      have hu := (snd encCNF encUnary).comp (fst (encPair encCNF encUnary) encUnary)
      have hj := snd (encPair encCNF encUnary) encUnary
      have hcl_u : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.1.1.getD q.1.2 [])
          (encPair (encPair encCNF encUnary) encUnary) (encClause encNat) :=
        (listGetD (encA := encClause encNat) (encL := encList (encClause encNat))
          ([] : Clause ℕ)).comp (hψ.prod hu)
      have hdv_j : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ => q.1.1.distinctVars.getD q.2 0)
          (encPair (encPair encCNF encUnary) encUnary) encNat :=
        (listGetD (0 : ℕ)).comp ((hdv.comp hψ).prod hj)
      have hany_u : ComputableInPolyTime
          (fun q : (CNF ℕ × ℕ) × ℕ =>
            (q.1.1.getD q.1.2 []).any fun l => decide (l.1 = q.1.1.distinctVars.getD q.2 0))
          (encPair (encPair encCNF encUnary) encUnary) encBool :=
        anyWithInput hcl_u (by fun_prop)
      have heq_ite : (fun q : (CNF ℕ × ℕ) × ℕ =>
          if q.1.2 < q.1.1.length then
            (q.1.1.getD q.1.2 []).any fun l => decide (l.1 = q.1.1.distinctVars.getD q.2 0)
          else true) =
          fun q => if decide (q.1.2 < q.1.1.length) then
            (q.1.1.getD q.1.2 []).any fun l => decide (l.1 = q.1.1.distinctVars.getD q.2 0)
          else true := funext fun _ => by simp only [decide_eq_true_eq]
      rw [heq_ite]
      exact ite' (unary_lt' hu (hm.comp hψ)) hany_u (const true)
    have hgrid : ComputableInPolyTime
        (fun ψ : CNF ℕ =>
          (List.range ψ.distinctVars.length).flatMap fun u =>
            (List.range ψ.distinctVars.length).map fun j =>
              if u < ψ.length then
                (ψ.getD u []).any fun l => decide (l.1 = ψ.distinctVars.getD j 0)
              else true)
        encCNF (encList encBool) :=
      flatMapWithInput hrng (mapWithInput (hrng.comp (fst encCNF encUnary)) hcell)
    have heq_top : toMatchingWord = fun ψ : CNF ℕ =>
        if decide (ψ.distinctVars.length < ψ.length) then [false, false]
        else
          (List.range ψ.distinctVars.length).flatMap fun u =>
            (List.range ψ.distinctVars.length).map fun j =>
              if u < ψ.length then
                (ψ.getD u []).any fun l => decide (l.1 = ψ.distinctVars.getD j 0)
              else true :=
      funext fun _ => by unfold toMatchingWord; simp only [decide_eq_true_eq]
    rw [heq_top]
    exact ite' (unary_lt' hn hm) (const [false, false]) hgrid
  have hword : ComputableInPolyTime toMatchingWord encCNF encBits :=
    (bits_encList_polyTime encBool).2.comp hword_framed
  exact BipartitePerfectMatching.computableInPolyTime_decider.comp (hword.comp helim)

private theorem satisfiable_removeTautologies (φ : CNF ℕ) :
    (removeTautologies φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_⟩
    by_cases ht : (c.any fun l => c.contains (l.1, !l.2)) = true
    · obtain ⟨⟨v, b⟩, hvb, hneg_c⟩ := List.any_eq_true.mp ht
      have hneg : (v, !b) ∈ c := List.contains_iff_mem.mp hneg_c
      rw [Clause.eval_eq_true_iff]
      by_cases hsv : σ v = b
      · exact ⟨(v, b), hvb, by simp [hsv]⟩
      · have hsv' : σ v = !b := by cases b <;> rcases h : σ v <;> simp_all
        exact ⟨(v, !b), hneg, by simp [hsv']⟩
    · have hmem : c ∈ removeTautologies φ :=
        List.mem_filter.mpr ⟨hc, by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr ht⟩
      exact (CNF.eval_eq_true_iff _ _).mp hσ c hmem
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (CNF.eval_eq_true_iff _ _).mpr fun c hc =>
      (CNF.eval_eq_true_iff _ _).mp hσ c (List.mem_of_mem_filter hc)⟩

private theorem satisfiable_pureStep (ψ : CNF ℕ) :
    (pureStep ψ).Satisfiable ↔ ψ.Satisfiable := by
  unfold pureStep
  rcases hhead : (ψ.distinctVars.filter (isPureVar ψ)).head? with _ | v
  · exact Iff.rfl
  · have hv_mem : v ∈ ψ.distinctVars.filter (isPureVar ψ) := List.mem_of_head? hhead
    have hpure : isPureVar ψ v = true := (List.mem_filter.mp hv_mem).2
    constructor
    · rintro ⟨σ, hσ⟩
      simp only [isPureVar, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false] at hpure
      rcases hpure with hno_neg | hno_pos
      · refine ⟨Function.update σ v true, (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_⟩
        by_cases hhas : (c.any fun l => decide (l.1 = v)) = true
        · obtain ⟨⟨u, b⟩, hub, huv_dec⟩ := List.any_eq_true.mp hhas
          obtain rfl : u = v := of_decide_eq_true huv_dec
          have hb : b = true := by
            cases b
            · exact absurd (List.contains_iff_mem.mpr hub) (by simpa using hno_neg c hc)
            · rfl
          subst hb
          exact (Clause.eval_eq_true_iff _ _).mpr ⟨(u, true), hub, by simp⟩
        · have hc_f : c ∈ ψ.filter (fun d => !(d.any fun l => decide (l.1 = v))) :=
            List.mem_filter.mpr ⟨hc, by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hhas⟩
          have hc_sat := (CNF.eval_eq_true_iff _ _).mp hσ c hc_f
          obtain ⟨⟨u, b⟩, hub, hval⟩ := (Clause.eval_eq_true_iff _ _).mp hc_sat
          have huv : u ≠ v := fun h => hhas (by
            rw [List.any_eq_true]; exact ⟨(u, b), hub, decide_eq_true h⟩)
          exact (Clause.eval_eq_true_iff _ _).mpr
            ⟨(u, b), hub, by simpa [Function.update_of_ne huv] using hval⟩
      · refine ⟨Function.update σ v false, (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_⟩
        by_cases hhas : (c.any fun l => decide (l.1 = v)) = true
        · obtain ⟨⟨u, b⟩, hub, huv_dec⟩ := List.any_eq_true.mp hhas
          obtain rfl : u = v := of_decide_eq_true huv_dec
          have hb : b = false := by
            cases b
            · rfl
            · exact absurd (List.contains_iff_mem.mpr hub) (by simpa using hno_pos c hc)
          subst hb
          exact (Clause.eval_eq_true_iff _ _).mpr ⟨(u, false), hub, by simp⟩
        · have hc_f : c ∈ ψ.filter (fun d => !(d.any fun l => decide (l.1 = v))) :=
            List.mem_filter.mpr ⟨hc, by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hhas⟩
          have hc_sat := (CNF.eval_eq_true_iff _ _).mp hσ c hc_f
          obtain ⟨⟨u, b⟩, hub, hval⟩ := (Clause.eval_eq_true_iff _ _).mp hc_sat
          have huv : u ≠ v := fun h => hhas (by
            rw [List.any_eq_true]; exact ⟨(u, b), hub, decide_eq_true h⟩)
          exact (Clause.eval_eq_true_iff _ _).mpr
            ⟨(u, b), hub, by simpa [Function.update_of_ne huv] using hval⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨σ, (CNF.eval_eq_true_iff _ _).mpr fun c hc =>
        (CNF.eval_eq_true_iff _ _).mp hσ c (List.mem_of_mem_filter hc)⟩

private theorem pureStep_length_lt_of_isSome {ψ : CNF ℕ}
    (hs : ((ψ.distinctVars.filter (isPureVar ψ)).head?).isSome = true) :
    (pureStep ψ).length < ψ.length := by
  unfold pureStep
  rcases hhead : (ψ.distinctVars.filter (isPureVar ψ)).head? with _ | v
  · simp [hhead] at hs
  · have hv_mem : v ∈ ψ.distinctVars :=
      (List.mem_filter.mp (List.mem_of_head? hhead)).1
    obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp (CNF.mem_distinctVars.mp hv_mem)
    exact List.length_filter_lt_length_iff_exists.mpr ⟨c, hc, by
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_eq_true, decide_eq_true_eq]
      exact ⟨(v, b), hl, rfl⟩⟩

private theorem pureElim_no_pure (φ : CNF ℕ) :
    ((pureElim φ).distinctVars.filter (isPureVar (pureElim φ))).head? = none := by
  set φ₀ := removeTautologies φ
  have haux : ∀ k (ψ : CNF ℕ), ψ.length ≤ k →
      ((pureStep^[k] ψ).distinctVars.filter (isPureVar (pureStep^[k] ψ))).head? = none := by
    intro k
    induction k with
    | zero =>
      intro ψ hlen
      obtain rfl := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      rfl
    | succ k ih =>
      intro ψ hlen
      rcases hhead : (ψ.distinctVars.filter (isPureVar ψ)).head? with _ | v
      · have hfix : pureStep ψ = ψ := by simp [pureStep, hhead]
        have hiter : pureStep^[k + 1] ψ = ψ := by
          clear ih hlen; induction k with
          | zero => exact hfix
          | succ m ihm => rw [Function.iterate_succ_apply', ihm, hfix]
        rw [hiter]; exact hhead
      · rw [Function.iterate_succ_apply]
        have hlt := pureStep_length_lt_of_isSome (ψ := ψ) (by simp [hhead])
        exact ih (pureStep ψ) (by omega)
  exact haux φ₀.length φ₀ le_rfl

/-- Correctness of `twoOccurrenceDecider` on every CNF formula with at most `2` occurrences per
variable. -/
theorem twoOccurrenceDecider_eq_true_iff {φ : CNF ℕ} (hocc : ∀ v, φ.occurrences v ≤ 2) :
    twoOccurrenceDecider φ = true ↔ φ.Satisfiable := by
  classical
  unfold twoOccurrenceDecider
  rw [BipartitePerfectMatching.decider_eq_true_iff]
  set ψ := pureElim φ
  have hsat_eq : ψ.Satisfiable ↔ φ.Satisfiable := by
    have hiter : ∀ k (χ : CNF ℕ), (pureStep^[k] χ).Satisfiable ↔ χ.Satisfiable := by
      intro k; induction k with
      | zero => intro _; exact Iff.rfl
      | succ k ih =>
        intro χ; rw [Function.iterate_succ_apply, ih, satisfiable_pureStep]
    exact (hiter _ _).trans (satisfiable_removeTautologies φ)
  have hψ_sub_taut : List.Sublist ψ (removeTautologies φ) := pureStep_iterate_sublist _ _
  have hψ_sub_φ : List.Sublist ψ φ := hψ_sub_taut.trans List.filter_sublist
  have hψ_occ : ∀ v, ψ.occurrences v ≤ 2 := fun v =>
    (sublist_countP_le hψ_sub_φ _).trans (hocc v)
  have hψ_no_taut : ∀ c ∈ ψ, ∀ v, ¬ ((v, true) ∈ c ∧ (v, false) ∈ c) := by
    intro c hc v ⟨ht, hf⟩
    have hc_rt := hψ_sub_taut.subset hc
    obtain ⟨_, hnt⟩ := List.mem_filter.mp hc_rt
    simp only [Bool.not_eq_true', List.any_eq_false] at hnt
    exact absurd (List.contains_iff_mem.mpr hf) (by simpa using hnt (v, true) ht)
  have hψ_no_pure : ∀ v ∈ ψ.distinctVars,
      (∃ c ∈ ψ, (v, false) ∈ c) ∧ (∃ c ∈ ψ, (v, true) ∈ c) := by
    intro v hv
    have hnone := pureElim_no_pure φ
    have hnot_mem : v ∉ ψ.distinctVars.filter (isPureVar ψ) := by
      intro hm
      rcases hflt : ψ.distinctVars.filter (isPureVar ψ) with _ | ⟨x, xs⟩
      · rw [hflt] at hm; cases hm
      · rw [hflt] at hnone; cases hnone
    have hnp : isPureVar ψ v = false := by
      by_contra ht
      exact hnot_mem (List.mem_filter.mpr ⟨hv, Bool.eq_true_of_not_eq_false ht⟩)
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hnp
    have h1' : (ψ.any fun c => c.contains (v, false)) = true := by
      cases h : (ψ.any fun c => c.contains (v, false))
      · rw [h] at h1; cases h1
      · rfl
    have h2' : (ψ.any fun c => c.contains (v, true)) = true := by
      cases h : (ψ.any fun c => c.contains (v, true))
      · rw [h] at h2; cases h2
      · rfl
    obtain ⟨c₁, hc₁, hm₁⟩ := List.any_eq_true.mp h1'
    obtain ⟨c₂, hc₂, hm₂⟩ := List.any_eq_true.mp h2'
    exact ⟨⟨c₁, hc₁, List.contains_iff_mem.mp hm₁⟩, ⟨c₂, hc₂, List.contains_iff_mem.mp hm₂⟩⟩
  rw [← hsat_eq]
  set dvars := ψ.distinctVars
  set n := dvars.length
  set m := ψ.length
  have hex_inj_of_sat : ψ.Satisfiable →
      ∃ (g : Fin m → Fin n) (bfn : Fin m → Bool),
        Function.Injective g ∧ ∀ u : Fin m, (dvars[g u], bfn u) ∈ ψ[u] := by
    rintro ⟨σ, hσ⟩
    have hsat_u : ∀ u : Fin m, ∃ (j : Fin n) (b : Bool),
        (dvars[j], b) ∈ ψ[u] ∧ σ (dvars[j]) = b := by
      intro u
      have hcu := (CNF.eval_eq_true_iff _ _).mp hσ ψ[u] (List.getElem_mem u.2)
      obtain ⟨⟨v, b⟩, hvb, hval⟩ := (Clause.eval_eq_true_iff _ _).mp hcu
      have hv_dv : v ∈ dvars :=
        CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr ⟨ψ[u], List.getElem_mem u.2, b, hvb⟩)
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv_dv
      exact ⟨⟨j, hj⟩, b, hvb, by simpa using hval⟩
    choose g bfn hg_mem hg_val using hsat_u
    refine ⟨g, bfn, fun u₁ u₂ hEq => ?_, hg_mem⟩
    by_contra hne
    set v := dvars[g u₁]
    have hm₁ : (v, bfn u₁) ∈ ψ[u₁] := hg_mem u₁
    have hm₂ : (v, bfn u₂) ∈ ψ[u₂] := by simpa [v, hEq] using hg_mem u₂
    have hb_eq : bfn u₁ = bfn u₂ :=
      (hg_val u₁).symm.trans (by simpa [v, hEq] using hg_val u₂)
    rw [← hb_eq] at hm₂
    have hv_dv : v ∈ dvars := List.getElem_mem (g u₁).2
    obtain ⟨⟨c_neg, hc_neg, hm_neg⟩, ⟨c_pos, hc_pos, hm_pos⟩⟩ := hψ_no_pure v hv_dv
    have hex_u₃ : ∃ (u₃ : ℕ) (hu₃ : u₃ < m), (v, !(bfn u₁)) ∈ ψ[u₃] := by
      cases hb : bfn u₁
      · obtain ⟨u₃, hu₃, rfl⟩ := List.mem_iff_getElem.mp hc_pos
        exact ⟨u₃, hu₃, hm_pos⟩
      · obtain ⟨u₃, hu₃, rfl⟩ := List.mem_iff_getElem.mp hc_neg
        exact ⟨u₃, hu₃, hm_neg⟩
    obtain ⟨u₃, hu₃, hm₃⟩ := hex_u₃
    have hu3_ne1 : u₃ ≠ u₁.1 := by
      rintro rfl
      cases hb : bfn u₁
      · rw [hb] at hm₁ hm₃
        exact hψ_no_taut _ (List.getElem_mem u₁.2) v ⟨hm₃, hm₁⟩
      · rw [hb] at hm₁ hm₃
        exact hψ_no_taut _ (List.getElem_mem u₁.2) v ⟨hm₁, hm₃⟩
    have hu3_ne2 : u₃ ≠ u₂.1 := by
      rintro rfl
      cases hb : bfn u₁
      · rw [hb] at hm₂ hm₃
        exact hψ_no_taut _ (List.getElem_mem u₂.2) v ⟨hm₃, hm₂⟩
      · rw [hb] at hm₂ hm₃
        exact hψ_no_taut _ (List.getElem_mem u₂.2) v ⟨hm₂, hm₃⟩
    have hu1_ne2 : u₁.1 ≠ u₂.1 := Fin.val_ne_of_ne hne
    have hcard3 : 3 ≤ ({u₁.1, u₂.1, u₃} : Finset ℕ).card := by
      rw [card_insert_of_notMem (by simp [hu1_ne2, hu3_ne1.symm]),
        card_insert_of_notMem (by simp [hu3_ne2.symm]), card_singleton]
    have hsub_occ : ({u₁.1, u₂.1, u₃} : Finset ℕ).card ≤ ψ.occurrences v := by
      have hidx_eq : ψ.occurrences v =
          ((List.range m).filter fun idx =>
            decide (∃ l ∈ ψ.getD idx [], l.1 = v)).length := by
        have hmap : ψ = (List.range m).map fun idx => ψ.getD idx [] :=
          List.ext_getElem (by simp [m]) fun idx h1 _ => by
            simp only [List.getElem_map, List.getElem_range]
            exact (List.getD_eq_getElem _ _ h1).symm
        conv_lhs => rw [hmap, CNF.occurrences, List.countP_eq_length_filter,
          List.filter_map, List.length_map]
        rfl
      rw [hidx_eq, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      refine card_le_card fun idx hidx => ?_
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      simp only [mem_insert, mem_singleton] at hidx
      rcases hidx with rfl | rfl | rfl
      · exact ⟨u₁.2, (v, bfn u₁), by rw [List.getD_eq_getElem _ _ u₁.2]; exact hm₁, rfl⟩
      · exact ⟨u₂.2, (v, bfn u₁), by rw [List.getD_eq_getElem _ _ u₂.2]; exact hm₂, rfl⟩
      · exact ⟨hu₃, (v, !(bfn u₁)), by rw [List.getD_eq_getElem _ _ hu₃]; exact hm₃, rfl⟩
    have := hψ_occ v; omega
  by_cases hgt : n < m
  · have hword_false : toMatchingWord ψ = [false, false] := by
      simp [toMatchingWord, n, m, dvars, hgt]
    rw [hword_false]
    constructor
    · rintro ⟨k, hk, _⟩
      exfalso; simp only [List.length_cons, List.length_nil] at hk
      rcases k with _ | _ | k <;> nlinarith
    · intro hsat
      obtain ⟨g, _, hg_inj, _⟩ := hex_inj_of_sat hsat
      have hle : m ≤ n := by
        simpa [Fintype.card_fin] using Fintype.card_le_of_injective g hg_inj
      omega
  · -- `m ≤ n`: `toMatchingWord ψ` has square length `n * n`
    have hmn : m ≤ n := not_lt.mp hgt
    let row (u : ℕ) : List Bool :=
      (List.range n).map fun j =>
        if u < m then (ψ.getD u []).any fun l => decide (l.1 = dvars.getD j 0) else true
    have hword_eq : toMatchingWord ψ = (List.range n).flatMap row := by
      simp [toMatchingWord, n, m, dvars, hgt, row]
    have hword_len : (toMatchingWord ψ).length = n * n := by
      rw [hword_eq, List.length_flatMap]
      simp [row, List.map_const', smul_eq_mul]
    have hadj_eq : ∀ (u j : Fin n),
        BipartitePerfectMatching.graph (toMatchingWord ψ) n (u, j) =
          if u.1 < m then (ψ.getD u.1 []).any fun l => decide (l.1 = dvars[j]) else true := by
      intro u j
      simp only [BipartitePerfectMatching.graph, BipartitePerfectMatching.adj]
      have hidx_lt : j.1 + n * u.1 < (toMatchingWord ψ).length := by
        rw [hword_len]; exact (finProdFinEquiv (u, j)).isLt
      rw [List.getD_eq_getElem _ _ hidx_lt]
      have hsplit_r : List.range n =
          List.range u.1 ++ u.1 :: ((List.range (n - u.1 - 1)).map (u.1 + 1 + ·)) := by
        have h1 := @List.range_add u.1 (n - u.1)
        rw [Nat.add_sub_of_le u.2.le] at h1
        have h2 : n - u.1 = 1 + (n - u.1 - 1) := by omega
        rw [h1, h2, @List.range_add 1 (n - u.1 - 1), List.range_one, List.map_append,
          List.map_singleton, List.map_map]
        simp [Function.comp_def, Nat.add_assoc]
      have hpref_len : ((List.range u.1).flatMap row).length = n * u.1 := by
        simp [row, List.length_flatMap, List.map_const', smul_eq_mul, mul_comm]
      have hflat_split : toMatchingWord ψ =
          ((List.range u.1).flatMap row) ++ (row u.1 ++
            (((List.range (n - u.1 - 1)).map (u.1 + 1 + ·)).flatMap row)) := by
        rw [hword_eq, hsplit_r, List.flatMap_append, List.flatMap_cons]
      have hget : (toMatchingWord ψ)[j.1 + n * u.1]'hidx_lt = (row u.1)[j.1]'(by simp [row]) := by
        simp only [hflat_split]
        rw [List.getElem_append_right (by rw [hpref_len]; omega),
          List.getElem_append_left
            (by rw [hpref_len]; simp only [row, List.length_map, List.length_range]; omega)]
        congr 1; omega
      rw [hget]
      simp only [row, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ j.2]
      by_cases hum : u.1 < m <;> simp [hum]
    rw [BipartitePerfectMatching.mem_iff_of_length_eq hword_len]
    constructor
    · rintro ⟨π, hπ⟩
      let satLit (u : Fin m) : Bool :=
        let j := π ⟨u.1, lt_of_lt_of_le u.2 hmn⟩
        ((ψ[u].filter fun l => decide (l.1 = dvars[j])).headD (0, true)).2
      let σ (v : ℕ) : Bool :=
        if h : ∃ u : Fin m, dvars[π ⟨u.1, lt_of_lt_of_le u.2 hmn⟩] = v then
          satLit h.choose
        else
          false
      refine ⟨σ, (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_⟩
      obtain ⟨u_nat, hu_lt, rfl⟩ := List.mem_iff_getElem.mp hc
      let u : Fin m := ⟨u_nat, hu_lt⟩
      let uN : Fin n := ⟨u.1, lt_of_lt_of_le u.2 hmn⟩
      have hedge := hπ uN
      rw [hadj_eq uN (π uN), ite_eq_left u.2, List.getD_eq_getElem _ _ u.2,
        List.any_eq_true] at hedge
      obtain ⟨⟨v₀, b₀⟩, hv₀, hv₀_eq⟩ := hedge
      have hflt_ne : ψ[u].filter (fun l => decide (l.1 = dvars[π uN])) ≠ [] := by
        intro hnil
        have hm : (v₀, b₀) ∈ ψ[u].filter (fun l => decide (l.1 = dvars[π uN])) :=
          List.mem_filter.mpr ⟨hv₀, hv₀_eq⟩
        rw [hnil] at hm; exact List.not_mem_nil hm
      rcases hflt : ψ[u].filter (fun l => decide (l.1 = dvars[π uN])) with _ | ⟨⟨v₁, b₁⟩, _⟩
      · exact absurd hflt hflt_ne
      · have hmem₁ : (v₁, b₁) ∈ ψ[u].filter (fun l => decide (l.1 = dvars[π uN])) := by
          rw [hflt]; exact List.mem_cons_self
        obtain ⟨hmem_cl, hv₁_eq⟩ := List.mem_filter.mp hmem₁
        have hv₁_d : v₁ = dvars[π uN] := of_decide_eq_true hv₁_eq
        have hex : ∃ u' : Fin m, dvars[π ⟨u'.1, lt_of_lt_of_le u'.2 hmn⟩] = v₁ :=
          ⟨u, hv₁_d.symm⟩
        have hu_choose : hex.choose = u := by
          have hspec : dvars[π ⟨hex.choose.1, lt_of_lt_of_le hex.choose.2 hmn⟩] = dvars[π uN] :=
            hex.choose_spec.trans hv₁_d
          have hdv_nd : dvars.Nodup := CNF.nodup_distinctVars ψ
          have hπ_eq : π ⟨hex.choose.1, _⟩ = π uN :=
            Fin.ext ((List.Nodup.getElem_inj_iff hdv_nd).mp hspec)
          exact Fin.ext (Fin.mk.inj (π.injective hπ_eq))
        have hσ_v₁ : σ v₁ = b₁ := by
          simp only [σ, dite_eq_left hex, hu_choose, satLit, uN, hflt, List.headD_cons]
        exact (Clause.eval_eq_true_iff _ _).mpr
          ⟨(v₁, b₁), hmem_cl, by simp [hσ_v₁]⟩
    · intro hsat
      obtain ⟨g, bfn, hg_inj, hg_mem⟩ := hex_inj_of_sat hsat
      let S_L : Finset (Fin n) := univ.filter fun u => u.1 < m
      let gL (u : ↥S_L) : Fin n := g ⟨u.1.1, (mem_filter.mp u.2).2⟩
      have hgL_inj : Function.Injective gL := fun a b h =>
        Subtype.ext (Fin.ext (Fin.mk.inj (hg_inj h)))
      let T_R : Finset (Fin n) := univ.image gL
      have hcard_eq : T_R.card = S_L.card := by
        rw [card_image_of_injective _ hgL_inj, card_univ, Fintype.card_coe]
      have hcompl_card : Fintype.card ↥(S_Lᶜ) = Fintype.card ↥(T_Rᶜ) := by
        simp only [Fintype.card_coe, card_compl, hcard_eq]
      let e_compl : ↥(S_Lᶜ) ≃ ↥(T_Rᶜ) := Fintype.equivOfCardEq hcompl_card
      let π_fn (u : Fin n) : Fin n :=
        if hu : u ∈ S_L then gL ⟨u, hu⟩ else (e_compl ⟨u, mem_compl.mpr hu⟩).1
      have hπ_inj : Function.Injective π_fn := by
        intro u₁ u₂ hEq
        by_cases h1 : u₁ ∈ S_L <;> by_cases h2 : u₂ ∈ S_L <;>
          simp only [π_fn, h1, h2, ↓reduceDIte] at hEq
        · exact congrArg Subtype.val (hgL_inj hEq)
        · exfalso
          have hmem : (e_compl ⟨u₂, mem_compl.mpr h2⟩).1 ∈ T_R := by
            rw [← hEq]; exact mem_image_of_mem gL (mem_univ (⟨u₁, h1⟩ : ↥S_L))
          exact (mem_compl.mp (e_compl ⟨u₂, mem_compl.mpr h2⟩).2) hmem
        · exfalso
          have hmem : (e_compl ⟨u₁, mem_compl.mpr h1⟩).1 ∈ T_R := by
            rw [hEq]; exact mem_image_of_mem gL (mem_univ (⟨u₂, h2⟩ : ↥S_L))
          exact (mem_compl.mp (e_compl ⟨u₁, mem_compl.mpr h1⟩).2) hmem
        · exact congrArg Subtype.val (e_compl.injective (Subtype.ext hEq))
      refine ⟨Equiv.ofBijective π_fn (Finite.injective_iff_bijective.mp hπ_inj), fun u => ?_⟩
      change BipartitePerfectMatching.graph (toMatchingWord ψ) n (u, π_fn u) = true
      rw [hadj_eq]
      by_cases hu : u.1 < m
      · have huS : u ∈ S_L := mem_filter.mpr ⟨mem_univ u, hu⟩
        simp only [hu, ↓reduceIte, π_fn, dite_eq_left huS, List.getD_eq_getElem _ _ hu,
          List.any_eq_true, decide_eq_true_eq]
        exact ⟨(dvars[g ⟨u.1, hu⟩], bfn ⟨u.1, hu⟩), hg_mem ⟨u.1, hu⟩, rfl⟩
      · simp [hu]

/-- **Tovey's Theorem**: `2`-occurrence `SAT` belongs to `P`. -/
theorem twoOccurrenceSAT_mem_P : TwoOccurrenceSAT ∈ P encCNF := by
  have hguard : ComputableInPolyTime checkMaxTwoOcc encCNF encBool := by
    unfold checkMaxTwoOcc
    exact allWithInput SAT.computableInPolyTime_distinctVars (by fun_prop)
  refine ⟨fun φ => checkMaxTwoOcc φ && twoOccurrenceDecider φ,
    bool_and' hguard computableInPolyTime_twoOccurrenceDecider, fun φ => ?_⟩
  have hcnt (v : ℕ) :
      (φ.countP fun c => c.any fun l => decide (l.1 = v)) = φ.occurrences v := by
    unfold CNF.occurrences
    congr 1
    funext c
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
    simp only [decide_eq_true_eq]
  have hchk : checkMaxTwoOcc φ = true ↔ ∀ v, φ.occurrences v ≤ 2 := by
    simp only [checkMaxTwoOcc, List.all_eq_true, decide_eq_true_eq, hcnt]
    constructor
    · intro h v
      by_cases hv : v ∈ φ.vars
      · exact h v (CNF.mem_distinctVars.mpr hv)
      · have h0 : φ.occurrences v = 0 := by
          simp only [CNF.occurrences, List.countP_eq_zero, decide_eq_true_eq]
          rintro c hc ⟨⟨u, b⟩, hl, rfl⟩
          exact hv (CNF.mem_vars.mpr ⟨c, hc, b, hl⟩)
        omega
    · intro h v _
      exact h v
  rw [Set.mem_ofPred_eq, Bool.and_eq_true, hchk]
  exact and_congr_right fun hocc => (twoOccurrenceDecider_eq_true_iff hocc).symm

end CslibFrontier.Complexity
