/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
public import CslibFrontier.Foundations.BooleanAnalysis.Influence

import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Boppana's Bounded-Depth Circuit Total Influence Theorem

**Boppana's theorem**: every single-output Boolean circuit over the unbounded-fan-in basis
(`Cslib.Circuits.Boolean.Unbounded.signature`) of depth at most `d` and size at most `s` computing
`f : BitString n → Bool` has total influence at most `(442 * max (Real.log s) 1) ^ (max d 1 - 1)`.
More sharply, if `C` has AND/OR depth `C.depthWith Unbounded.andOrCost ≤ d` and at most `M`
conjunction and disjunction gates (`C.program.cost Unbounded.andOrCost ≤ M`), then
`totalInfluence (signVal ∘ f) ≤ (442 * max (Real.log M) 1) ^ (max d 1 - 1)`.

## Main results

* `CslibFrontier.Circuits.Boolean.Unbounded.exists_const_or_circuit_of_comp_fill`: constant
  propagation under a partial assignment `ρ` yields either a constant function or a circuit of no
  greater size, AND/OR cost, depth, or AND/OR depth.
* `CslibFrontier.Circuits.Boolean.Unbounded.totalInfluence_dnf_le`: every width-`w` DNF formula has
  total influence at most `2 * w`.
* `CslibFrontier.Circuits.Boolean.Unbounded.totalInfluence_le_max_andOrCost_one`,
  `CslibFrontier.Circuits.Boolean.Unbounded.totalInfluence_le_one_of_depthWith_le_one`:
  dimension-free gate-count influence bound and `≤ 1` bound at AND/OR depth at most `1`.
* `CslibFrontier.Circuits.Boolean.Unbounded.boppana_totalInfluence_le_of_depthWith_le`,
  `CslibFrontier.Circuits.Boolean.Unbounded.boppana_totalInfluence_le`: Boppana's bounded-depth
  circuit total influence theorem.
-/

public section

namespace CslibFrontier.Circuits.Boolean.Unbounded

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Cslib.DecisionTree Cslib.Logic.PL Finset Function
open scoped BigOperators

private lemma totalInfluence_const {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) :
    totalInfluence (fun _ : ι → Bool ↦ c) = 0 := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq]
  refine sum_eq_zero fun S _ ↦ ?_
  rw [fourierCoeff_const]
  split_ifs with hS <;> simp [hS]

private lemma totalInfluence_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) :
    totalInfluence (-f) = totalInfluence f := by
  have hneg : ∀ S, fourierCoeff (-f) S = -fourierCoeff f S := fun S ↦ by
    rw [show -f = fun x ↦ (-1 : ℝ) * f x from funext fun x ↦ by simp, fourierCoeff_const_mul]
    ring
  simp only [totalInfluence_eq_sum_card_mul_fourierCoeff_sq, hneg, neg_sq]

section RestrictionClosure

private def extendConstMap {n g : ℕ} {α : Type*} (wm : Wire n g → α) (v : α) :
    Wire n (g + 1) → α :=
  Wire.elim (fun i ↦ wm (.input i)) (Fin.lastCases v fun j ↦ wm (.gate j))

private lemma extendConstMap_castSucc {n g : ℕ} {α : Type*} (wm : Wire n g → α) (v : α)
    (w : Wire n g) : extendConstMap wm v w.castSucc = wm w := by
  cases w <;> simp [extendConstMap]

private lemma extendConstMap_last {n g : ℕ} {α : Type*} (wm : Wire n g → α) (v : α) :
    extendConstMap wm v (.gate (Fin.last g)) = v := by
  simp [extendConstMap]

private def extendGateMap {n g g' : ℕ} (wm : Wire n g → Bool ⊕ Wire n g') :
    Wire n (g + 1) → Bool ⊕ Wire n (g' + 1) :=
  extendConstMap (fun w ↦ (wm w).map id Wire.castSucc) (Sum.inr (.gate (Fin.last g')))

private lemma extendGateMap_castSucc {n g g' : ℕ} (wm : Wire n g → Bool ⊕ Wire n g')
    (w : Wire n g) :
    extendGateMap wm w.castSucc = (wm w).map id Wire.castSucc :=
  extendConstMap_castSucc _ _ w

private lemma extendGateMap_last {n g g' : ℕ} (wm : Wire n g → Bool ⊕ Wire n g') :
    extendGateMap wm (.gate (Fin.last g)) = Sum.inr (.gate (Fin.last g')) :=
  extendConstMap_last _ _

private theorem exists_restricted_program {n g : ℕ} (ρ : PartialAssignment (Fin n))
    (p : Program Unbounded.signature n g) :
    ∃ (g' : ℕ) (p' : Program Unbounded.signature n g') (wm : Wire n g → Bool ⊕ Wire n g'),
      g' ≤ g ∧
      p'.cost andOrCost ≤ p.cost andOrCost ∧
      (∀ w x, Sum.elim id (p'.trace interpretation x) (wm w) =
        p.trace interpretation (ρ.fill x) w) ∧
      (∀ w w', wm w = Sum.inr w' →
        p'.wireDepths w' ≤ p.wireDepths w ∧
          p'.wireDepthsWith andOrCost w' ≤ p.wireDepthsWith andOrCost w) := by
  induction p with
  | empty =>
    refine ⟨0, .empty,
      Wire.elim (fun i ↦ match ρ i with | some b => Sum.inl b | none => Sum.inr (.input i))
        Fin.elim0,
      le_rfl, le_rfl, fun w x ↦ ?_, fun w w' hw ↦ ?_⟩
    · cases w with
      | input i =>
        cases hρ : ρ i <;> simp [PartialAssignment.fill, hρ]
      | gate k => exact k.elim0
    · cases w with
      | input i =>
        rw [Wire.elim_input] at hw
        cases hρ : ρ i with
        | none =>
          rw [hρ] at hw
          injection hw with hw'
          subst hw'
          exact ⟨le_rfl, le_rfl⟩
        | some b =>
          rw [hρ] at hw
          cases hw
      | gate k => exact k.elim0
  | @gate g q line ih =>
    obtain ⟨g', q', wm, hg', hcost, htrace, hdepth⟩ := ih
    have hconst_step : ∀ (b : Bool),
        (∀ x, (q.gate line).trace interpretation (ρ.fill x) (.gate (Fin.last g)) = b) →
        ∃ (g'' : ℕ) (p'' : Program Unbounded.signature n g'')
          (wm' : Wire n (g + 1) → Bool ⊕ Wire n g''),
          g'' ≤ g + 1 ∧
          p''.cost andOrCost ≤ (q.gate line).cost andOrCost ∧
          (∀ w x, Sum.elim id (p''.trace interpretation x) (wm' w) =
            (q.gate line).trace interpretation (ρ.fill x) w) ∧
          (∀ w w', wm' w = Sum.inr w' →
            p''.wireDepths w' ≤ (q.gate line).wireDepths w ∧
              p''.wireDepthsWith andOrCost w' ≤ (q.gate line).wireDepthsWith andOrCost w) := by
      intro b hb
      refine ⟨g', q', extendConstMap wm (Sum.inl b), hg'.trans (Nat.le_succ g),
        hcost.trans (Nat.le_add_right _ _), fun w x ↦ ?_, fun w w' hw ↦ ?_⟩
      · induction w using Wire.lastCases with
        | last => rw [extendConstMap_last, hb x]; rfl
        | castSucc w =>
          rw [extendConstMap_castSucc, Program.trace_gate_castSucc, htrace w x]
      · induction w using Wire.lastCases with
        | last => rw [extendConstMap_last] at hw; cases hw
        | castSucc w =>
          rw [extendConstMap_castSucc] at hw
          rw [Program.wireDepths_gate_castSucc, Program.wireDepthsWith_gate_castSucc]
          exact hdepth w w' hw
    have hgate_step : ∀ (line' : Line Unbounded.signature n g'),
        andOrCost line'.op = andOrCost line.op →
        (∀ a', ∃ a, wm (line.wires a) = Sum.inr (line'.wires a')) →
        (∀ x, interpretation line'.op (fun a' ↦ q'.trace interpretation x (line'.wires a')) =
          interpretation line.op (fun a ↦ q.trace interpretation (ρ.fill x) (line.wires a))) →
        ∃ (g'' : ℕ) (p'' : Program Unbounded.signature n g'')
          (wm' : Wire n (g + 1) → Bool ⊕ Wire n g''),
          g'' ≤ g + 1 ∧
          p''.cost andOrCost ≤ (q.gate line).cost andOrCost ∧
          (∀ w x, Sum.elim id (p''.trace interpretation x) (wm' w) =
            (q.gate line).trace interpretation (ρ.fill x) w) ∧
          (∀ w w', wm' w = Sum.inr w' →
            p''.wireDepths w' ≤ (q.gate line).wireDepths w ∧
              p''.wireDepthsWith andOrCost w' ≤ (q.gate line).wireDepthsWith andOrCost w) := by
      intro line' hcost_eq hsub heval
      refine ⟨g' + 1, q'.gate line', extendGateMap wm, Nat.succ_le_succ hg', ?_, fun w x ↦ ?_,
        fun w w' hw ↦ ?_⟩
      · simp only [Program.cost_gate, hcost_eq]
        exact Nat.add_le_add_right hcost _
      · induction w using Wire.lastCases with
        | last =>
          rw [extendGateMap_last, Sum.elim_inr, Program.trace_gate_last, Program.trace_gate_last]
          exact heval x
        | castSucc w =>
          rw [extendGateMap_castSucc, Program.trace_gate_castSucc]
          cases hwm : wm w with
          | inl c =>
            have h := htrace w x
            rw [hwm] at h
            exact h
          | inr w₀ =>
            have h := htrace w x
            rw [hwm, Sum.elim_inr] at h
            simpa [Program.trace_gate_castSucc] using h
      · induction w using Wire.lastCases with
        | last =>
          rw [extendGateMap_last, Sum.inr.injEq] at hw
          subst hw
          have h1 : ∀ (c : Unbounded.Op → ℕ), c line'.op = c line.op →
              (∀ u u', wm u = Sum.inr u' → q'.wireDepthsWith c u' ≤ q.wireDepthsWith c u) →
              (q'.gate line').wireDepthsWith c (.gate (Fin.last g')) ≤
                (q.gate line).wireDepthsWith c (.gate (Fin.last g)) := by
            intro c hc hcd
            simp only [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last,
              Line.depthWith_eq_sup, hc]
            refine Nat.add_le_add_right (Finset.sup_le fun a' _ ↦ ?_) _
            obtain ⟨a, ha⟩ := hsub a'
            exact (hcd _ _ ha).trans
              (Finset.le_sup (f := fun a ↦ q.wireDepthsWith c (line.wires a)) (mem_univ a))
          have hd1 := h1 1 rfl fun u u' hu ↦ by
            simpa only [Program.wireDepthsWith_one] using (hdepth u u' hu).1
          simp only [Program.wireDepthsWith_one] at hd1
          exact ⟨hd1, h1 andOrCost hcost_eq fun u u' hu ↦ (hdepth u u' hu).2⟩
        | castSucc w =>
          rw [extendGateMap_castSucc] at hw
          cases hwm : wm w with
          | inl c => simp [hwm] at hw
          | inr w₀ =>
            simp only [hwm, Sum.map_inr, Sum.inr.injEq] at hw
            subst hw
            rw [Program.wireDepths_gate_castSucc, Program.wireDepths_gate_castSucc,
              Program.wireDepthsWith_gate_castSucc, Program.wireDepthsWith_gate_castSucc]
            exact hdepth w w₀ hwm
    rcases line with ⟨op, wires⟩
    cases op with
    | not =>
      cases h0 : wm (wires 0) with
      | inl b =>
        refine hconst_step (!b) fun x ↦ ?_
        rw [Program.trace_gate_last, interpretation_not]
        have ht := htrace (wires 0) x
        rw [h0] at ht
        exact congrArg Bool.not ht.symm
      | inr w₀ =>
        refine hgate_step ⟨.not, fun _ ↦ w₀⟩ rfl (fun _ ↦ ⟨0, h0⟩) fun x ↦ ?_
        simp only [interpretation_not]
        have ht := htrace (wires 0) x
        rw [h0, Sum.elim_inr] at ht
        exact congrArg Bool.not ht
    | and m =>
      by_cases hfalse : ∃ a : Fin m, wm (wires a) = Sum.inl false
      · obtain ⟨a₀, ha₀⟩ := hfalse
        refine hconst_step false fun x ↦ ?_
        rw [Program.trace_gate_last, interpretation_and, decide_eq_false_iff_not, not_forall]
        refine ⟨a₀, ?_⟩
        have ht := htrace (wires a₀) x
        rw [ha₀] at ht
        simp [← ht]
      · let wl : List (Wire n g') :=
          (List.finRange m).filterMap fun a ↦
            match wm (wires a) with | Sum.inl _ => none | Sum.inr w' => some w'
        refine hgate_step ⟨.and wl.length, fun j ↦ wl[j.val]⟩ rfl (fun j ↦ ?_) fun x ↦ ?_
        · have hmem : wl[j.val] ∈ wl := List.getElem_mem j.isLt
          obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp hmem
          cases hwm : wm (wires a) with
          | inl b => simp [hwm] at ha
          | inr w' =>
            simp only [hwm, Option.some.injEq] at ha
            exact ⟨a, hwm.trans (congrArg Sum.inr ha)⟩
        · rw [Bool.eq_iff_iff]
          simp only [interpretation_and, decide_eq_true_iff]
          constructor
          · intro hall a
            have ht := htrace (wires a) x
            cases hwm : wm (wires a) with
            | inl b =>
              rw [hwm] at ht
              cases b
              · exact absurd ⟨a, hwm⟩ hfalse
              · exact ht.symm
            | inr w' =>
              rw [hwm, Sum.elim_inr] at ht
              have hmem : w' ∈ wl := List.mem_filterMap.mpr ⟨a, List.mem_finRange a, by simp [hwm]⟩
              obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hmem
              exact ht.symm.trans (hall ⟨idx, hidx⟩)
          · intro hall j
            have hmem : wl[j.val] ∈ wl := List.getElem_mem j.isLt
            obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp hmem
            cases hwm : wm (wires a) with
            | inl b => simp [hwm] at ha
            | inr w' =>
              simp only [hwm, Option.some.injEq] at ha
              have ht := htrace (wires a) x
              rw [hwm, Sum.elim_inr, ha] at ht
              exact ht.trans (hall a)
    | or m =>
      by_cases htrue : ∃ a : Fin m, wm (wires a) = Sum.inl true
      · obtain ⟨a₀, ha₀⟩ := htrue
        refine hconst_step true fun x ↦ ?_
        rw [Program.trace_gate_last, interpretation_or, decide_eq_true_iff]
        refine ⟨a₀, ?_⟩
        have ht := htrace (wires a₀) x
        rw [ha₀] at ht
        exact ht.symm
      · let wl : List (Wire n g') :=
          (List.finRange m).filterMap fun a ↦
            match wm (wires a) with | Sum.inl _ => none | Sum.inr w' => some w'
        refine hgate_step ⟨.or wl.length, fun j ↦ wl[j.val]⟩ rfl (fun j ↦ ?_) fun x ↦ ?_
        · have hmem : wl[j.val] ∈ wl := List.getElem_mem j.isLt
          obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp hmem
          cases hwm : wm (wires a) with
          | inl b => simp [hwm] at ha
          | inr w' =>
            simp only [hwm, Option.some.injEq] at ha
            exact ⟨a, hwm.trans (congrArg Sum.inr ha)⟩
        · rw [Bool.eq_iff_iff]
          simp only [interpretation_or, decide_eq_true_iff]
          constructor
          · rintro ⟨j, hj⟩
            have hmem : wl[j.val] ∈ wl := List.getElem_mem j.isLt
            obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp hmem
            cases hwm : wm (wires a) with
            | inl b => simp [hwm] at ha
            | inr w' =>
              simp only [hwm, Option.some.injEq] at ha
              have ht := htrace (wires a) x
              rw [hwm, Sum.elim_inr, ha] at ht
              exact ⟨a, ht.symm.trans hj⟩
          · rintro ⟨a, ha⟩
            have ht := htrace (wires a) x
            cases hwm : wm (wires a) with
            | inl b =>
              rw [hwm] at ht
              cases b
              · simp [← ht] at ha
              · exact absurd ⟨a, hwm⟩ htrue
            | inr w' =>
              rw [hwm, Sum.elim_inr] at ht
              have hmem : w' ∈ wl := List.mem_filterMap.mpr ⟨a, List.mem_finRange a, by simp [hwm]⟩
              obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hmem
              exact ⟨⟨idx, hidx⟩, ht.trans ha⟩

/-- **Constant-propagation restriction closure**: restricting `C : Circuit Unbounded.signature n 1`
computing `single f` by a partial assignment `ρ : PartialAssignment (Fin n)` yields either a
constant Boolean function or a circuit `C'` computing `single (f ∘ ρ.fill)` with `C'.size ≤ C.size`,
`C'.program.cost andOrCost ≤ C.program.cost andOrCost`, `C'.depth ≤ C.depth`, and
`C'.depthWith andOrCost ≤ C.depthWith andOrCost`. -/
theorem exists_const_or_circuit_of_comp_fill {n : ℕ} {C : Circuit Unbounded.signature n 1}
    {f : (Fin n → Bool) → Bool} (hC : C.Computes interpretation (single f))
    (ρ : PartialAssignment (Fin n)) :
    (∃ b : Bool, ∀ x, f (ρ.fill x) = b) ∨
      ∃ C' : Circuit Unbounded.signature n 1,
        C'.Computes interpretation (single (f ∘ ρ.fill)) ∧
        C'.size ≤ C.size ∧
        C'.program.cost andOrCost ≤ C.program.cost andOrCost ∧
        C'.depth ≤ C.depth ∧
        C'.depthWith andOrCost ≤ C.depthWith andOrCost := by
  obtain ⟨g', p', wm, hg', hcost, htrace, hdepth⟩ := exists_restricted_program ρ C.program
  have hout : ∀ x, C.program.trace interpretation (ρ.fill x) (C.outputs 0) = f (ρ.fill x) :=
    fun x ↦ congrFun (hC (ρ.fill x)) 0
  cases hwm : wm (C.outputs 0) with
  | inl b =>
    refine Or.inl ⟨b, fun x ↦ ?_⟩
    have ht := htrace (C.outputs 0) x
    rw [hwm, hout x] at ht
    exact ht.symm
  | inr w₀ =>
    let C' : Circuit Unbounded.signature n 1 := ⟨p', fun _ ↦ w₀⟩
    refine Or.inr ⟨C', fun x ↦ funext fun j ↦ ?_, hg', hcost, ?_, ?_⟩
    · rw [Subsingleton.elim j 0, single_apply, Function.comp_apply, ← hout x]
      have ht := htrace (C.outputs 0) x
      rw [hwm] at ht
      exact ht
    · rw [Circuit.depth_le_iff]
      intro j
      rw [Subsingleton.elim j 0]
      exact (hdepth _ _ hwm).1.trans (C.outputDepths_le_depth 0)
    · rw [Circuit.depthWith_le_iff]
      intro j
      rw [Subsingleton.elim j 0]
      exact (hdepth _ _ hwm).2.trans (C.wireDepthsWith_outputs_le_depthWith andOrCost 0)

end RestrictionClosure

/-! ### Narrow-DNF and Gate-Count Total Influence Bounds -/

section BaseInfluenceBounds

private lemma totalInfluence_signVal_bne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (b : Bool) :
    totalInfluence (fun x ↦ signVal (f x != b)) = totalInfluence (fun x ↦ signVal (f x)) := by
  cases b
  · simp
  · have hneg : (fun x ↦ signVal (f x != true)) = -(fun x ↦ signVal (f x)) :=
      funext fun x ↦ by simp [signVal_not]
    rw [hneg, totalInfluence_neg]

private lemma totalInfluence_signVal_literal {n : ℕ} (i₀ : Fin n) (b : Bool) :
    totalInfluence (fun x : Fin n → Bool ↦ signVal (x i₀ != b)) = 1 := by
  rw [totalInfluence_signVal_bne]
  have hchi : (fun x : Fin n → Bool ↦ signVal (x i₀)) = chi ℝ ({i₀} : Finset (Fin n)) :=
    funext fun x ↦ (chi_singleton i₀ x).symm
  rw [hchi, totalInfluence_chi, card_singleton, Nat.cast_one]

/-- **Narrow-DNF total influence bound**: every disjunctive normal form formula `D : DNF (Fin n)`
whose terms have length at most `w` satisfies
`totalInfluence (fun x ↦ signVal (DNF.eval x D)) ≤ 2 * w`. -/
theorem totalInfluence_dnf_le {n w : ℕ} {D : DNF (Fin n)} (hD : ∀ t ∈ D, t.length ≤ w) :
    totalInfluence (fun x ↦ signVal (DNF.eval x D)) ≤ 2 * (w : ℝ) := by
  let P : Finset ((Fin n → Bool) × Fin n) :=
    univ.filter fun p ↦ DNF.eval (update p.1 p.2 (!p.1 p.2)) D ≠ DNF.eval p.1 D
  let Pt : Finset ((Fin n → Bool) × Fin n) :=
    univ.filter fun p ↦ DNF.eval p.1 D = true ∧ DNF.eval (update p.1 p.2 (!p.1 p.2)) D = false
  let Pf : Finset ((Fin n → Bool) × Fin n) :=
    univ.filter fun p ↦ DNF.eval p.1 D = false ∧ DNF.eval (update p.1 p.2 (!p.1 p.2)) D = true
  have hpart : P = Pt ∪ Pf := by
    ext ⟨x, i⟩
    simp only [P, Pt, Pf, mem_union, mem_filter, mem_univ, true_and]
    cases DNF.eval x D <;> cases DNF.eval (update x i (!x i)) D <;> simp
  have hdisj : Disjoint Pt Pf := by
    rw [disjoint_filter]
    rintro ⟨x, i⟩ _ ⟨ht, _⟩ ⟨hf, _⟩
    exact Bool.false_ne_true (hf.symm.trans ht)
  have hbij : #Pf = #Pt := by
    refine card_nbij' (fun p ↦ (update p.1 p.2 (!p.1 p.2), p.2))
      (fun p ↦ (update p.1 p.2 (!p.1 p.2), p.2))
      (fun ⟨x, i⟩ hp ↦ ?_) (fun ⟨x, i⟩ hp ↦ ?_)
      (fun ⟨x, i⟩ _ ↦ ?_) (fun ⟨x, i⟩ _ ↦ ?_)
    · obtain ⟨hf, ht⟩ := (mem_filter.mp hp).2
      refine mem_filter.mpr ⟨mem_univ _, ht, ?_⟩
      have hinv : update (update x i (!x i)) i (!(update x i (!x i) i)) = x := by
        ext j; by_cases hj : j = i <;> simp [hj]
      rwa [hinv]
    · obtain ⟨ht, hf⟩ := (mem_filter.mp hp).2
      refine mem_filter.mpr ⟨mem_univ _, hf, ?_⟩
      have hinv : update (update x i (!x i)) i (!(update x i (!x i) i)) = x := by
        ext j; by_cases hj : j = i <;> simp [hj]
      rwa [hinv]
    · ext j
      · by_cases hj : j = i <;> simp [hj]
      · rfl
    · ext j
      · by_cases hj : j = i <;> simp [hj]
      · rfl
  have hPt_le : #Pt ≤ Fintype.card (Fin n → Bool) * w := by
    have hsum : #Pt = ∑ x : Fin n → Bool,
        #{i : Fin n | DNF.eval x D = true ∧ DNF.eval (update x i (!x i)) D = false} := by
      have heq : Pt = (univ ×ˢ univ).filter fun p : (Fin n → Bool) × Fin n ↦
          DNF.eval p.1 D = true ∧ DNF.eval (update p.1 p.2 (!p.1 p.2)) D = false := by
        ext p; simp [Pt]
      rw [heq, card_eq_sum_ones, sum_filter, sum_product]
      refine sum_congr rfl fun x _ ↦ ?_
      rw [← sum_filter, ← card_eq_sum_ones]
    rw [hsum]
    refine (sum_le_sum (g := fun _ : Fin n → Bool ↦ w) fun x _ ↦ ?_).trans_eq
      (by rw [sum_const, card_univ, smul_eq_mul])
    by_cases hx : DNF.eval x D = true
    · obtain ⟨t, htD, htx⟩ := (DNF.eval_eq_true_iff x D).mp hx
      let V : Finset (Fin n) := (t.map Prod.fst).toFinset
      have hsub : (univ.filter fun i : Fin n ↦ DNF.eval x D = true ∧
          DNF.eval (update x i (!x i)) D = false) ⊆ V := by
        intro i hi
        by_contra hiV
        have hne : ∀ l ∈ t, l.1 ≠ i := fun l hl hli ↦
          hiV (List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, hli⟩))
        have hstay : DNF.eval (update x i (!x i)) D = true :=
          (DNF.eval_eq_true_iff _ D).mpr ⟨t, htD, (Term.eval_update_of_forall_ne hne x _).trans htx⟩
        exact Bool.false_ne_true ((mem_filter.mp hi).2.2.symm.trans hstay)
      exact (card_le_card hsub).trans
        ((List.toFinset_card_le _).trans ((List.length_map _).trans_le (hD t htD)))
    · rw [filter_false_of_mem fun i _ ⟨ht, _⟩ ↦ hx ht, card_empty]
      exact Nat.zero_le w
  have hP_le : (#P : ℝ) ≤ (Fintype.card (Fin n → Bool) : ℝ) * (2 * (w : ℝ)) := by
    have hnat : #P ≤ Fintype.card (Fin n → Bool) * (2 * w) := by
      rw [hpart, card_union_of_disjoint hdisj, hbij]
      linarith
    exact_mod_cast hnat
  have hsum_P : (∑ x : Fin n → Bool,
      (#{i : Fin n | DNF.eval (update x i (!x i)) D ≠ DNF.eval x D} : ℝ)) = (#P : ℝ) := by
    norm_cast
    have heq : P = (univ ×ˢ univ).filter fun p : (Fin n → Bool) × Fin n ↦
        DNF.eval (update p.1 p.2 (!p.1 p.2)) D ≠ DNF.eval p.1 D := by
      ext p; simp [P]
    rw [heq, card_eq_sum_ones, sum_filter, sum_product]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_filter, ← card_eq_sum_ones]
  rw [totalInfluence_signVal, Finset.expect_eq_sum_div_card, card_univ, hsum_P,
    div_le_iff₀ (by positivity)]
  linarith

private lemma two_mul_mul_two_pow_sub_le (n r : ℕ) (hr : r ≤ n) :
    2 * r * 2 ^ (n - r) ≤ 2 ^ n := by
  rcases r with _ | _ | _ | m
  · simp
  · have h : 2 * 1 * 2 ^ (n - 1) = 2 ^ (1 + (n - 1)) := by rw [pow_add]; ring
    rw [h, Nat.add_sub_of_le hr]
  · have h : 2 * 2 * 2 ^ (n - 2) = 2 ^ (2 + (n - 2)) := by rw [pow_add]; ring
    rw [h, Nat.add_sub_of_le hr]
  · have hpow : ∀ k : ℕ, 2 * (k + 3) ≤ 2 ^ (k + 3) := by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        rw [Nat.add_succ, pow_succ']
        omega
    calc 2 * (m + 3) * 2 ^ (n - (m + 3))
        ≤ 2 ^ (m + 3) * 2 ^ (n - (m + 3)) := Nat.mul_le_mul_right _ (hpow m)
      _ = 2 ^ ((m + 3) + (n - (m + 3))) := (pow_add 2 _ _).symm
      _ = 2 ^ n := by rw [Nat.add_sub_of_le hr]

private lemma card_filter_agree_subset_eq {n : ℕ} (S : Finset (Fin n)) (val : Fin n → Bool) :
    #{z : Fin n → Bool | ∀ i ∈ S, z i = val i} = 2 ^ (n - #S) := by
  have heq : (univ.filter fun z : Fin n → Bool ↦ ∀ i ∈ S, z i = val i) =
      Fintype.piFinset fun i : Fin n ↦ if i ∈ S then {val i} else univ := by
    ext z
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i ↦ ?_
    by_cases hi : i ∈ S <;> simp [hi]
  rw [heq, Fintype.card_piFinset]
  have hcard_ite : ∀ i : Fin n,
      #(if i ∈ S then ({val i} : Finset Bool) else univ) = if i ∈ S then 1 else 2 := fun i ↦ by
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hcard_ite]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  have hcompl : #(univ.filter fun i : Fin n ↦ i ∉ S) = n - #S := by
    have h := card_filter_add_card_filter_not (s := univ) (p := fun i : Fin n ↦ i ∈ S)
    have hS : (univ.filter fun i : Fin n ↦ i ∈ S) = S := by ext i; simp
    rw [hS, card_univ, Fintype.card_fin] at h
    omega
  rw [hcompl]

private lemma wire_eq_input_or_non_not_gate {n g : ℕ} (p : Program Unbounded.signature n g)
    (w : Wire n g) :
    (∃ (i : Fin n) (b : Bool),
      ∀ x, p.trace interpretation x w = (x i != b)) ∨
    (∃ (k : Fin g) (b : Bool), (p.lines k).op ≠ .not ∧
      p.depthsWith andOrCost k ≤ p.wireDepthsWith andOrCost w ∧
      (∃ j : Fin g, w = .gate j ∧ k ≤ j) ∧
      ∀ x, p.trace interpretation x w = (p.eval interpretation x k != b)) := by
  refine p.wire_induction
    (P := fun w ↦
      (∃ (i : Fin n) (b : Bool), ∀ x, p.trace interpretation x w = (x i != b)) ∨
      (∃ (k : Fin g) (b : Bool), (p.lines k).op ≠ .not ∧
        p.depthsWith andOrCost k ≤ p.wireDepthsWith andOrCost w ∧
        (∃ j : Fin g, w = .gate j ∧ k ≤ j) ∧
        ∀ x, p.trace interpretation x w = (p.eval interpretation x k != b)))
    (fun i ↦ Or.inl ⟨i, false, fun x ↦ by simp⟩)
    (fun k ih ↦ ?_) w
  by_cases hop : (p.lines k).op = .not
  · let a₀ : Fin (p.lines k).op.arity := ⟨0, by simp [hop]⟩
    have hnot : ∀ x, p.trace interpretation x (.gate k) =
        !p.trace interpretation x ((p.lines k).wires a₀) :=
      fun x ↦ (p.trace_gate interpretation x k).trans
        (interpretation_of_op_eq_not hop (p.trace interpretation x))
    rcases ih a₀ with ⟨i, b, hb⟩ | ⟨k', b, hop', hdep, ⟨j, hj, hk'j⟩, hb⟩
    · refine Or.inl ⟨i, !b, fun x ↦ ?_⟩
      rw [hnot x, hb x]
      cases x i <;> cases b <;> rfl
    · have hjk : j < k := p.lt_of_lines_wires_eq_gate k a₀ j hj
      have hdep_le : p.wireDepthsWith andOrCost ((p.lines k).wires a₀) ≤
          p.depthsWith andOrCost k :=
        (Nat.le_add_right _ _).trans (p.wireDepthsWith_lines_add_le andOrCost k a₀)
      refine Or.inr ⟨k', !b, hop', hdep.trans hdep_le, ⟨k, rfl, hk'j.trans hjk.le⟩, fun x ↦ ?_⟩
      rw [hnot x, hb x]
      cases p.eval interpretation x k' <;> cases b <;> rfl
  · exact Or.inr ⟨k, false, hop, le_rfl, ⟨k, rfl, le_rfl⟩, fun x ↦ by simp⟩

private def LocalGateFlip {n g : ℕ} (p : Program Unbounded.signature n g) (k : Fin g)
    (x : Fin n → Bool) (i : Fin n) : Prop :=
  (p.lines k).op ≠ .not ∧
    p.eval interpretation (update x i (!x i)) k ≠ p.eval interpretation x k ∧
    ∀ j : Fin g, j < k → (p.lines j).op ≠ .not →
      p.depthsWith andOrCost j < p.depthsWith andOrCost k →
        p.eval interpretation (update x i (!x i)) j = p.eval interpretation x j

private noncomputable instance {n g : ℕ} (p : Program Unbounded.signature n g) (k : Fin g)
    (x : Fin n → Bool) (i : Fin n) : Decidable (LocalGateFlip p k x i) :=
  Classical.propDecidable _

private lemma localGateFlip_update {n g : ℕ} (p : Program Unbounded.signature n g) (k : Fin g)
    (x : Fin n → Bool) (i : Fin n) :
    LocalGateFlip p k (update x i (!x i)) i ↔ LocalGateFlip p k x i := by
  have hinv : update (update x i (!x i)) i (!(update x i (!x i) i)) = x := by
    ext j; by_cases hj : j = i <;> simp [hj]
  simp only [LocalGateFlip, hinv, ne_comm]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
    forall_congr' fun _ ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
      imp_congr_right fun _ ↦ eq_comm

private lemma card_localGateFlip_le {n g : ℕ} (p : Program Unbounded.signature n g) (k : Fin g) :
    #{q : (Fin n → Bool) × Fin n | LocalGateFlip p k q.1 q.2} ≤ 2 ^ n := by
  classical
  by_cases hop : (p.lines k).op = .not
  · rw [filter_false_of_mem fun q _ hq ↦ hq.1 hop, card_empty]
    positivity
  · let target : Bool := match (p.lines k).op with | .and _ => true | .or _ => false | .not => true
    have htarget_forced : ∀ (z : Fin n → Bool), p.eval interpretation z k = target →
        ∀ a : Fin (p.lines k).op.arity, p.trace interpretation z ((p.lines k).wires a) =
          target := by
      intro z hz
      have hl := (p.lines_eval interpretation z k).trans hz
      rcases hline : (p.lines k) with ⟨op, wires⟩
      cases op with
      | not => exact absurd rfl (by rw [hline] at hop; exact hop)
      | and m =>
        have htar : target = true := by dsimp [target]; rw [hline]
        rw [hline] at hl
        rw [htar] at hl ⊢
        intro a
        exact (interpretation_of_op_eq_and (l := ⟨.and m, wires⟩) rfl _).mp hl a
      | or m =>
        have htar : target = false := by dsimp [target]; rw [hline]
        rw [hline] at hl
        rw [htar] at hl ⊢
        intro a
        have hfalse : ¬ ∃ a', p.trace interpretation z (wires a') = true := by
          rw [← interpretation_of_op_eq_or (l := ⟨.or m, wires⟩) rfl]
          exact Bool.eq_false_iff.mp hl
        cases hval : p.trace interpretation z (wires a)
        · rfl
        · exact absurd ⟨a, hval⟩ hfalse
    let LitReq (idx : Fin n) (val : Bool) : Prop :=
      ∃ a : Fin (p.lines k).op.arity,
        ∀ w, p.trace interpretation w ((p.lines k).wires a) = (w idx != (target != val))
    let S : Finset (Fin n) := univ.filter fun idx ↦ LitReq idx false ∨ LitReq idx true
    let Pt : Finset ((Fin n → Bool) × Fin n) :=
      univ.filter fun q ↦ LocalGateFlip p k q.1 q.2 ∧ p.eval interpretation q.1 k = target
    let Pf : Finset ((Fin n → Bool) × Fin n) :=
      univ.filter fun q ↦ LocalGateFlip p k q.1 q.2 ∧ p.eval interpretation q.1 k = !target
    have hpart : (univ.filter fun q : (Fin n → Bool) × Fin n ↦ LocalGateFlip p k q.1 q.2) =
        Pt ∪ Pf := by
      ext ⟨x, i⟩
      simp only [Pt, Pf, mem_union, mem_filter, mem_univ, true_and]
      cases p.eval interpretation x k <;> cases htar : target <;> simp
    have hdisj : Disjoint Pt Pf := by
      rw [disjoint_filter]
      rintro ⟨x, i⟩ _ ⟨_, ht⟩ ⟨_, hf⟩
      cases htar : target <;> simp_all
    have hbij : #Pf = #Pt := by
      refine card_nbij' (fun q ↦ (update q.1 q.2 (!q.1 q.2), q.2))
        (fun q ↦ (update q.1 q.2 (!q.1 q.2), q.2))
        (fun ⟨x, i⟩ hq ↦ ?_) (fun ⟨x, i⟩ hq ↦ ?_)
        (fun ⟨x, i⟩ _ ↦ Prod.ext (funext fun j ↦ by by_cases hj : j = i <;> simp [hj]) rfl)
        (fun ⟨x, i⟩ _ ↦ Prod.ext (funext fun j ↦ by by_cases hj : j = i <;> simp [hj]) rfl)
      · obtain ⟨hmf, hf⟩ := (mem_filter.mp hq).2
        refine mem_filter.mpr ⟨mem_univ _, (localGateFlip_update p k x i).mpr hmf, ?_⟩
        have hne := hmf.2.1
        cases h1 : p.eval interpretation (update x i (!x i)) k <;>
          cases h2 : p.eval interpretation x k <;> cases htar : target <;> simp_all
      · obtain ⟨hmf, ht⟩ := (mem_filter.mp hq).2
        refine mem_filter.mpr ⟨mem_univ _, (localGateFlip_update p k x i).mpr hmf, ?_⟩
        have hne := hmf.2.1
        cases h1 : p.eval interpretation (update x i (!x i)) k <;>
          cases h2 : p.eval interpretation x k <;> cases htar : target <;> simp_all
    have hPt_bound : 2 * #Pt ≤ 2 ^ n := by
      by_cases hconflict : ∃ idx : Fin n, LitReq idx false ∧ LitReq idx true
      · obtain ⟨idx, ⟨a0, ha0⟩, ⟨a1, ha1⟩⟩ := hconflict
        have hempty : Pt = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          rintro ⟨z, i⟩ hz
          have h0 := (ha0 z).symm.trans (htarget_forced z (mem_filter.mp hz).2.2 a0)
          have h1 := (ha1 z).symm.trans (htarget_forced z (mem_filter.mp hz).2.2 a1)
          cases hz0 : z idx <;> cases htar : target <;> simp_all
        rw [hempty, card_empty, mul_zero]
        positivity
      · push Not at hconflict
        let reqVal : Fin n → Bool := fun idx ↦ if LitReq idx true then true else false
        have hPt_sub : Pt ⊆
            (univ.filter fun z : Fin n → Bool ↦ ∀ idx ∈ S, z idx = reqVal idx) ×ˢ S := by
          rintro ⟨z, i⟩ hz
          obtain ⟨hmf, hzt⟩ := (mem_filter.mp hz).2
          rw [mem_product, mem_filter]
          refine ⟨⟨mem_univ z, fun idx hidx ↦ ?_⟩, ?_⟩
          · rcases (mem_filter.mp hidx).2 with h0 | h1
            · have hnot1 : ¬ LitReq idx true := hconflict idx h0
              dsimp only [reqVal]
              rw [ite_eq_right hnot1]
              obtain ⟨a, ha⟩ := h0
              have ht := (ha z).symm.trans (htarget_forced z hzt a)
              cases hz0 : z idx <;> cases htar : target <;> simp_all
            · dsimp only [reqVal]
              rw [ite_eq_left h1]
              obtain ⟨a, ha⟩ := h1
              have ht := (ha z).symm.trans (htarget_forced z hzt a)
              cases hz0 : z idx <;> cases htar : target <;> simp_all
          · have hex_arg : ∃ a : Fin (p.lines k).op.arity,
                p.trace interpretation (update z i (!z i)) ((p.lines k).wires a) ≠
                  p.trace interpretation z ((p.lines k).wires a) := by
              by_contra! hall
              apply hmf.2.1
              rw [← p.lines_eval interpretation (update z i (!z i)) k,
                ← p.lines_eval interpretation z k]
              unfold Line.eval
              congr 1
              funext a
              exact hall a
            obtain ⟨a, ha_ne⟩ := hex_arg
            rcases wire_eq_input_or_non_not_gate p ((p.lines k).wires a) with
              ⟨idx, b, hb⟩ | ⟨k', b, hop', hdep_k', ⟨j, hj, hk'j⟩, hb⟩
            · have hij : idx = i := by
                by_contra hne
                apply ha_ne
                rw [hb, hb, Function.update_of_ne hne]
              subst hij
              rw [mem_filter]
              refine ⟨mem_univ idx, ?_⟩
              cases hval : (target != b)
              · exact Or.inl ⟨a, fun w ↦ by
                  rw [hb w]; cases htar : target <;> cases b <;> simp_all⟩
              · exact Or.inr ⟨a, fun w ↦ by
                  rw [hb w]; cases htar : target <;> cases b <;> simp_all⟩
            · have hjk : j < k := p.lt_of_lines_wires_eq_gate k a j hj
              have hk'k : k' < k := lt_of_le_of_lt hk'j hjk
              have hlt_dep : p.depthsWith andOrCost k' < p.depthsWith andOrCost k := by
                have hstep := p.wireDepthsWith_lines_add_le andOrCost k a
                rw [andOrCost_eq_one_of_ne_not hop] at hstep
                omega
              have heq := hmf.2.2 k' hk'k hop' hlt_dep
              exact absurd ((hb _).trans (congrArg (· != b) heq |>.trans (hb z).symm)) ha_ne
        have hcard_le := (card_le_card hPt_sub).trans_eq (card_product _ _)
        rw [card_filter_agree_subset_eq S reqVal] at hcard_le
        have hS_le : #S ≤ n := (card_le_univ S).trans_eq (Fintype.card_fin n)
        calc 2 * #Pt ≤ 2 * (2 ^ (n - #S) * #S) := Nat.mul_le_mul_left 2 hcard_le
          _ = 2 * #S * 2 ^ (n - #S) := by ring
          _ ≤ 2 ^ n := two_mul_mul_two_pow_sub_le n #S hS_le
    rw [hpart, card_union_of_disjoint hdisj, hbij]
    linarith

private lemma totalInfluence_signVal_le_of_sensitive_card {n M : ℕ} {f : (Fin n → Bool) → Bool}
    (hcard : #{q : (Fin n → Bool) × Fin n | f (update q.1 q.2 (!q.1 q.2)) ≠ f q.1} ≤ M * 2 ^ n) :
    totalInfluence (fun x ↦ signVal (f x)) ≤ (M : ℝ) := by
  let P : Finset ((Fin n → Bool) × Fin n) :=
    univ.filter fun q ↦ f (update q.1 q.2 (!q.1 q.2)) ≠ f q.1
  have hsum_P : (∑ x : Fin n → Bool,
      (#{i : Fin n | f (update x i (!x i)) ≠ f x} : ℝ)) = (#P : ℝ) := by
    norm_cast
    have heq : P = (univ ×ˢ univ).filter fun q : (Fin n → Bool) × Fin n ↦
        f (update q.1 q.2 (!q.1 q.2)) ≠ f q.1 := by
      ext q; simp [P]
    rw [heq, card_eq_sum_ones, sum_filter, sum_product]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_filter, ← card_eq_sum_ones]
  have hcard_cube : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_cast
  rw [totalInfluence_signVal, Finset.expect_eq_sum_div_card, card_univ, hsum_P, hcard_cube,
    div_le_iff₀ (by positivity)]
  exact_mod_cast hcard

/-- **Dimension-free AND/OR gate-count total influence bound**: for every circuit
`C : Circuit Unbounded.signature n 1` computing `single f`,
`totalInfluence (fun x ↦ signVal (f x)) ≤ max (C.program.cost andOrCost) 1`. -/
theorem totalInfluence_le_max_andOrCost_one {n : ℕ} {C : Circuit Unbounded.signature n 1}
    {f : (Fin n → Bool) → Bool} (hC : C.Computes interpretation (single f)) :
    totalInfluence (fun x ↦ signVal (f x)) ≤ max (C.program.cost andOrCost : ℝ) 1 := by
  classical
  have hout : ∀ x, C.program.trace interpretation x (C.outputs 0) = f x :=
    fun x ↦ congrFun (hC x) 0
  rcases wire_eq_input_or_non_not_gate C.program (C.outputs 0) with
    ⟨i₀, b, hb⟩ | ⟨k_out, b, hop_out, _, _, hb⟩
  · have hfeq : f = fun x ↦ (x i₀ != b) := funext fun x ↦ (hout x).symm.trans (hb x)
    rw [hfeq, totalInfluence_signVal_literal]
    exact le_max_right _ _
  · refine (totalInfluence_signVal_le_of_sensitive_card (M := C.program.cost andOrCost) ?_).trans
      (le_max_left _ _)
    let G : Finset (Fin C.size) := univ.filter fun k ↦ (C.program.lines k).op ≠ .not
    have hsub : (univ.filter fun q : (Fin n → Bool) × Fin n ↦
          f (update q.1 q.2 (!q.1 q.2)) ≠ f q.1) ⊆ G.biUnion fun k ↦
        univ.filter fun q : (Fin n → Bool) × Fin n ↦ LocalGateFlip C.program k q.1 q.2 := by
      rintro ⟨x, i⟩ hxi
      have hflip : f (update x i (!x i)) ≠ f x := (mem_filter.mp hxi).2
      have hk_flip : C.program.eval interpretation (update x i (!x i)) k_out ≠
          C.program.eval interpretation x k_out := by
        intro heq
        apply hflip
        rw [← hout (update x i (!x i)), ← hout x, hb, hb, heq]
      let Flips : Finset (Fin C.size) := univ.filter fun k ↦
        (C.program.lines k).op ≠ .not ∧
          C.program.eval interpretation (update x i (!x i)) k ≠
            C.program.eval interpretation x k
      have hne : Flips.Nonempty := ⟨k_out, mem_filter.mpr ⟨mem_univ _, hop_out, hk_flip⟩⟩
      let k₀ := Flips.min' hne
      have hk₀ : k₀ ∈ Flips := Flips.min'_mem hne
      obtain ⟨hop₀, hflip₀⟩ := (mem_filter.mp hk₀).2
      refine mem_biUnion.mpr ⟨k₀, mem_filter.mpr ⟨mem_univ _, hop₀⟩,
        mem_filter.mpr ⟨mem_univ _, hop₀, hflip₀, fun j hjk₀ hopj _ ↦ ?_⟩⟩
      by_contra hjflip
      exact not_le_of_gt hjk₀ (Flips.min'_le j (mem_filter.mpr ⟨mem_univ _, hopj, hjflip⟩))
    calc #{q : (Fin n → Bool) × Fin n | f (update q.1 q.2 (!q.1 q.2)) ≠ f q.1}
        ≤ #(G.biUnion fun k ↦
            univ.filter fun q : (Fin n → Bool) × Fin n ↦ LocalGateFlip C.program k q.1 q.2) :=
          card_le_card hsub
      _ ≤ ∑ k ∈ G, #{q : (Fin n → Bool) × Fin n | LocalGateFlip C.program k q.1 q.2} :=
          card_biUnion_le
      _ ≤ ∑ _k ∈ G, 2 ^ n := sum_le_sum fun k _ ↦ card_localGateFlip_le C.program k
      _ = #G * 2 ^ n := by rw [sum_const, smul_eq_mul]
      _ = C.program.cost andOrCost * 2 ^ n := by rw [cost_andOrCost_eq_card]

/-- **Depth-`≤ 1` total influence bound**: every circuit `C : Circuit Unbounded.signature n 1` of
AND/OR depth at most `1` computing `single f` satisfies
`totalInfluence (fun x ↦ signVal (f x)) ≤ 1`. -/
theorem totalInfluence_le_one_of_depthWith_le_one {n : ℕ} {C : Circuit Unbounded.signature n 1}
    {f : (Fin n → Bool) → Bool} (hC : C.Computes interpretation (single f))
    (hd : C.depthWith andOrCost ≤ 1) :
    totalInfluence (fun x ↦ signVal (f x)) ≤ 1 := by
  classical
  have hout : ∀ x, C.program.trace interpretation x (C.outputs 0) = f x :=
    fun x ↦ congrFun (hC x) 0
  rcases wire_eq_input_or_non_not_gate C.program (C.outputs 0) with
    ⟨i₀, b, hb⟩ | ⟨k_out, b, hop_out, hdep_out, _, hb⟩
  · have hfeq : f = fun x ↦ (x i₀ != b) := funext fun x ↦ (hout x).symm.trans (hb x)
    rw [hfeq, totalInfluence_signVal_literal]
  · have hk_le1 : C.program.depthsWith andOrCost k_out ≤ 1 :=
      hdep_out.trans ((C.wireDepthsWith_outputs_le_depthWith andOrCost 0).trans hd)
    refine (totalInfluence_signVal_le_of_sensitive_card (M := 1) ?_).trans_eq Nat.cast_one
    rw [one_mul]
    refine (card_le_card (t := univ.filter fun q : (Fin n → Bool) × Fin n ↦
        LocalGateFlip C.program k_out q.1 q.2) fun ⟨x, i⟩ hxi ↦ ?_).trans
      (card_localGateFlip_le C.program k_out)
    have hflip : f (update x i (!x i)) ≠ f x := (mem_filter.mp hxi).2
    have hk_flip : C.program.eval interpretation (update x i (!x i)) k_out ≠
        C.program.eval interpretation x k_out := by
      intro heq
      apply hflip
      rw [← hout (update x i (!x i)), ← hout x, hb, hb, heq]
    refine mem_filter.mpr ⟨mem_univ _, hop_out, hk_flip, fun j _ hopj hlt ↦ ?_⟩
    have hj_ge1 : 1 ≤ C.program.depthsWith andOrCost j := by
      have hcost := C.program.cost_le_depthsWith andOrCost j
      rwa [andOrCost_eq_one_of_ne_not hopj] at hcost
    omega

end BaseInfluenceBounds

/-! ### Multi-Stage Random Restrictions and Boppana's Theorem -/

section BoppanaMain

private lemma expect_totalInfluence_comp_fill_outside {n : ℕ} (F : (Fin n → Bool) → ℝ)
    (J : Finset (Fin n)) :
    (𝔼 z : Fin n → Bool, totalInfluence (F ∘ (PartialAssignment.outside J z).fill)) =
      ∑ i ∈ J, influence i F := by
  have hcoord : ∀ i : Fin n,
      (𝔼 z : Fin n → Bool, influence i (F ∘ (PartialAssignment.outside J z).fill)) =
        if i ∈ J then influence i F else 0 := fun i ↦ by
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi]
      have hder : ∀ z x : Fin n → Bool,
          derivative i (F ∘ (PartialAssignment.outside J z).fill) x =
            derivative i F (J.piecewise x z) := fun z x ↦ by
        have hnone : PartialAssignment.outside J z i = none := by
          simp [PartialAssignment.outside, hi]
        simp [derivative, PartialAssignment.fill_update_of_eq_none hnone,
          ← PartialAssignment.fill_outside]
      simp only [influence, hder]
      exact expect_expect_piecewise_sq (derivative i F) J
    · rw [ite_eq_right hi]
      have hder : ∀ z x : Fin n → Bool,
          derivative i (F ∘ (PartialAssignment.outside J z).fill) x = 0 := fun z x ↦ by
        have hnot : PartialAssignment.outside J z i ≠ none := by
          simp [PartialAssignment.outside, hi]
        simp [derivative, PartialAssignment.fill_update_of_ne_none hnot]
      simp [influence, hder]
  simp only [totalInfluence]
  rw [expect_sum_comm]
  simp_rw [hcoord]
  rw [sum_ite_mem, univ_inter]

private lemma sum_powersetCard_sum_mem_eq {n ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (w : Fin n → ℝ) :
    (n : ℝ) * (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, ∑ i ∈ J, w i) =
      ((n.choose ℓ : ℝ) * (ℓ : ℝ)) * ∑ i : Fin n, w i := by
  have hn1 : 1 ≤ n := hℓ1.trans hℓn
  let c : Fin n → ℕ := fun i ↦ #{J ∈ (univ : Finset (Fin n)).powersetCard ℓ | i ∈ J}
  have hc_swap : ∀ i j : Fin n, c i = c j := fun i j ↦ by
    let π := Equiv.swap i j
    refine card_nbij' (fun J ↦ J.map π.toEmbedding) (fun J ↦ J.map π.toEmbedding)
      (fun J hJ ↦ ?_) (fun J hJ ↦ ?_) (fun J _ ↦ ?_) (fun J _ ↦ ?_)
    · obtain ⟨hJp, hiJ⟩ := mem_filter.mp hJ
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
      · rw [card_map, (mem_powersetCard.mp hJp).2]
      · rw [mem_map]
        exact ⟨i, hiJ, Equiv.swap_apply_left i j⟩
    · obtain ⟨hJp, hjJ⟩ := mem_filter.mp hJ
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
      · rw [card_map, (mem_powersetCard.mp hJp).2]
      · rw [mem_map]
        exact ⟨j, hjJ, Equiv.swap_apply_right i j⟩
    · ext k
      simp [π]
    · ext k
      simp [π]
  let i₀ : Fin n := ⟨0, hn1⟩
  let K : ℕ := c i₀
  have hc_eq : ∀ i : Fin n, c i = K := fun i ↦ hc_swap i i₀
  have hsum_card : n * K = n.choose ℓ * ℓ := by
    have h1 : (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, #J) = n.choose ℓ * ℓ := by
      rw [sum_congr rfl (g := fun _ ↦ ℓ) fun J hJ ↦ (mem_powersetCard.mp hJ).2, sum_const,
        card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
    have h2 : (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, #J) = ∑ i : Fin n, c i := by
      have hite : ∀ J : Finset (Fin n), #J = ∑ i : Fin n, if i ∈ J then 1 else 0 := fun J ↦ by
        rw [card_eq_sum_ones, ← sum_filter, filter_mem_eq_inter, univ_inter]
      simp_rw [hite]
      rw [sum_comm]
      exact sum_congr rfl fun i _ ↦ by dsimp only [c]; rw [card_eq_sum_ones, sum_filter]
    have h3 : (∑ i : Fin n, c i) = n * K := by
      rw [sum_congr rfl fun i _ ↦ hc_eq i, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hswap_sum : (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, ∑ i ∈ J, w i) =
      (K : ℝ) * ∑ i : Fin n, w i := by
    have hite : ∀ J : Finset (Fin n), (∑ i ∈ J, w i) =
        ∑ i : Fin n, if i ∈ J then w i else 0 := fun J ↦ by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter]
    have hlhs : (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, ∑ i ∈ J, w i) =
        ∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ,
          ∑ i : Fin n, if i ∈ J then w i else 0 :=
      sum_congr rfl fun J _ ↦ hite J
    rw [hlhs, sum_comm]
    have hterm : ∀ i : Fin n,
        (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, if i ∈ J then w i else 0) =
          (K : ℝ) * w i := fun i ↦ by
      have hci : #((univ : Finset (Fin n)).powersetCard ℓ |>.filter fun J ↦ i ∈ J) = K := hc_eq i
      rw [← sum_filter, sum_const, nsmul_eq_mul, hci]
    simp_rw [hterm, ← mul_sum]
  rw [hswap_sum, ← mul_assoc, show (n : ℝ) * (K : ℝ) = ((n * K : ℕ) : ℝ) by push_cast; rfl,
    hsum_card]
  push_cast
  ring

private lemma sum_powersetCard_sum_outside_eq {n ℓ : ℕ} (g : PartialAssignment (Fin n) → ℝ) :
    (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ,
      ∑ z : Fin n → Bool, g (PartialAssignment.outside J z)) =
      (2 : ℝ) ^ ℓ * ∑ ρ ∈ PartialAssignment.withFree (Fin n) ℓ, g ρ := by
  let S : Finset (Finset (Fin n) × (Fin n → Bool)) :=
    (univ : Finset (Fin n)).powersetCard ℓ ×ˢ univ
  let W : Finset (PartialAssignment (Fin n)) := PartialAssignment.withFree (Fin n) ℓ
  have hprod : (∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ,
      ∑ z : Fin n → Bool, g (PartialAssignment.outside J z)) =
      ∑ p ∈ S, g (PartialAssignment.outside p.1 p.2) :=
    (sum_product (f := fun p ↦ g (PartialAssignment.outside p.1 p.2)) _ _).symm
  have hmaps : ∀ p ∈ S, PartialAssignment.outside p.1 p.2 ∈ W := fun p hp ↦ by
    obtain ⟨hJ, _⟩ := mem_product.mp hp
    rw [PartialAssignment.mem_withFree, PartialAssignment.free_outside]
    exact (mem_powersetCard.mp hJ).2
  rw [hprod, ← sum_fiberwise_of_maps_to hmaps, mul_sum]
  refine sum_congr rfl fun ρ hρ ↦ ?_
  have hfree : #ρ.free = ℓ := PartialAssignment.mem_withFree.mp hρ
  have hcongr : (∑ p ∈ S.filter (fun p ↦ PartialAssignment.outside p.1 p.2 = ρ),
      g (PartialAssignment.outside p.1 p.2)) =
      ∑ _p ∈ S.filter (fun p ↦ PartialAssignment.outside p.1 p.2 = ρ), g ρ :=
    sum_congr rfl fun p hp ↦ congrArg g (mem_filter.mp hp).2
  rw [hcongr, sum_const, nsmul_eq_mul]
  have hcard : #(S.filter fun p ↦ PartialAssignment.outside p.1 p.2 = ρ) = 2 ^ ℓ := by
    rw [← hfree, ← PartialAssignment.card_filter_outside_eq ρ]
    refine card_nbij' (fun p ↦ p.2) (fun z ↦ (ρ.free, z))
      (fun p hp ↦ ?_) (fun z hz ↦ ?_) (fun p hp ↦ ?_) (fun _ _ ↦ rfl)
    · obtain ⟨_, hpρ⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_univ _, (hpρ ▸ PartialAssignment.free_outside p.1 p.2) ▸ hpρ⟩
    · have hz' : PartialAssignment.outside ρ.free z = ρ := (mem_filter.mp hz).2
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_powersetCard.mpr ⟨subset_univ _, hfree⟩, mem_univ _⟩, hz'⟩
    · obtain ⟨_, hpρ⟩ := mem_filter.mp hp
      exact Prod.ext (hpρ ▸ PartialAssignment.free_outside p.1 p.2) rfl
  rw [hcard]
  norm_cast

private lemma mul_card_withFree_totalInfluence_eq {n ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (F : (Fin n → Bool) → ℝ) :
    (ℓ : ℝ) * (#(PartialAssignment.withFree (Fin n) ℓ) : ℝ) * totalInfluence F =
      (n : ℝ) * ∑ ρ ∈ PartialAssignment.withFree (Fin n) ℓ, totalInfluence (F ∘ ρ.fill) := by
  have hcard_cube : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_cast
  have hJ : ∀ J : Finset (Fin n),
      (∑ z : Fin n → Bool, totalInfluence (F ∘ (PartialAssignment.outside J z).fill)) =
        (2 : ℝ) ^ n * ∑ i ∈ J, influence i F := fun J ↦ by
    have hex := expect_totalInfluence_comp_fill_outside F J
    rw [Finset.expect_eq_sum_div_card, card_univ, hcard_cube, div_eq_iff (by positivity)] at hex
    linarith
  have hlhs := sum_powersetCard_sum_outside_eq (n := n) (ℓ := ℓ)
    (fun ρ ↦ totalInfluence (F ∘ ρ.fill))
  simp_rw [hJ] at hlhs
  rw [← mul_sum] at hlhs
  have hrhs := congrArg ((n : ℝ) * ·) hlhs
  have hmul_n : (n : ℝ) * ((2 : ℝ) ^ n *
      ∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, ∑ i ∈ J, influence i F) =
      (2 : ℝ) ^ n * ((n : ℝ) *
        ∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ, ∑ i ∈ J, influence i F) := by ring
  rw [hmul_n, sum_powersetCard_sum_mem_eq hℓ1 hℓn (fun i ↦ influence i F), ← totalInfluence] at hrhs
  have hW : (#(PartialAssignment.withFree (Fin n) ℓ) : ℝ) =
      (n.choose ℓ : ℝ) * (2 : ℝ) ^ (n - ℓ) := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    push_cast
    rfl
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (n - ℓ) := by
    rw [← pow_add, Nat.add_sub_of_le hℓn]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  rw [hpow] at hrhs
  have hcancel : (2 : ℝ) ^ ℓ *
      ((ℓ : ℝ) * (#(PartialAssignment.withFree (Fin n) ℓ) : ℝ) * totalInfluence F) =
      (2 : ℝ) ^ ℓ *
        ((n : ℝ) * ∑ ρ ∈ PartialAssignment.withFree (Fin n) ℓ, totalInfluence (F ∘ ρ.fill)) := by
    rw [hW]
    linarith [hrhs]
  exact mul_left_cancel₀ h2pos.ne' hcancel

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hexp_neg : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
    have h := Real.add_one_le_exp (-1 / 2 : ℝ)
    linarith
  have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hexp_neg (Real.exp_nonneg (1 / 2 : ℝ))
    rw [← Real.exp_add, show (-1 / 2 : ℝ) + 1 / 2 = 0 by ring, Real.exp_zero] at hmul
    linarith
  rw [← Real.log_exp (1 / 2 : ℝ)]
  exact Real.log_le_log (Real.exp_pos _) hexp_half

private lemma good_restriction_totalInfluence_le {n t e : ℕ} (ht2 : 2 ≤ t)
    {C : Circuit Unbounded.signature n 1} {f : (Fin n → Bool) → Bool}
    (hC : C.Computes interpretation (single f))
    (hd : C.depthWith andOrCost ≤ e + 2) {ρ : PartialAssignment (Fin n)}
    (hgood : ∀ k, C.program.depthsWith andOrCost k ≤ e + 1 →
      Shallow t ρ fun x ↦ C.program.eval interpretation x k) :
    totalInfluence (fun x ↦ signVal (f (ρ.fill x))) ≤ 2 * (t : ℝ) := by
  have hout : ∀ x, C.program.trace interpretation x (C.outputs 0) = f x :=
    fun x ↦ congrFun (hC x) 0
  rcases wire_eq_input_or_non_not_gate C.program (C.outputs 0) with
    ⟨i₀, b, hb⟩ | ⟨k_out, b, hop_out, hdep_out, _, hb⟩
  · cases hρ : ρ i₀ with
    | none =>
      have hfeq : (fun x ↦ signVal (f (ρ.fill x))) = fun x ↦ signVal (x i₀ != b) :=
        funext fun x ↦ by rw [← hout (ρ.fill x), hb, PartialAssignment.fill, hρ]; rfl
      rw [hfeq, totalInfluence_signVal_literal]
      have ht_real : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
      linarith
    | some c =>
      have hfeq : (fun x ↦ signVal (f (ρ.fill x))) = fun _ ↦ signVal (c != b) := funext fun x ↦ by
        rw [← hout (ρ.fill x), hb, PartialAssignment.fill, hρ]; rfl
      rw [hfeq, totalInfluence_const]
      positivity
  · have hk_dep : C.program.depthsWith andOrCost k_out ≤ e + 2 :=
      hdep_out.trans ((C.wireDepthsWith_outputs_le_depthWith andOrCost 0).trans hd)
    have hargs : ∀ a : Fin (C.program.lines k_out).op.arity,
        Shallow t ρ fun x ↦ C.program.trace interpretation x ((C.program.lines k_out).wires a) :=
      fun a ↦ by
        have hlt := C.program.wireDepthsWith_lines_add_le andOrCost k_out a
        rw [andOrCost_eq_one_of_ne_not hop_out] at hlt
        cases hw : (C.program.lines k_out).wires a with
        | input idx => exact shallow_proj ht2 ρ idx
        | gate k' =>
          rw [hw, Program.wireDepthsWith_gateWire] at hlt
          exact hgood k' (by omega)
    obtain ⟨D, b', hD, heval⟩ := exists_dnf_of_shallow hop_out hargs
    have hfeq : (fun x ↦ signVal (f (ρ.fill x))) =
        fun x ↦ signVal (DNF.eval x D != (b' != b)) := funext fun x ↦ by
      have h1 := (hout (ρ.fill x)).symm.trans (hb (ρ.fill x))
      have h2 := (heval x).trans
        (congrArg (· != b') (C.program.lines_eval interpretation (ρ.fill x) k_out))
      rw [h1, h2]
      cases C.program.eval interpretation (ρ.fill x) k_out <;> cases b <;> cases b' <;> rfl
    rw [hfeq, totalInfluence_signVal_bne]
    exact totalInfluence_dnf_le fun u hu ↦ (hD u hu).1.le

/-- **Boppana's Bounded-Depth Circuit Total Influence Theorem (AND/OR depth and cost)**: for every
circuit `C : Circuit Unbounded.signature n 1` computing `single f` with `C.depthWith andOrCost ≤ d`
and `C.program.cost andOrCost ≤ M`,
`totalInfluence (fun x ↦ signVal (f x)) ≤ (442 * max (Real.log M) 1) ^ (max d 1 - 1)`. -/
theorem boppana_totalInfluence_le_of_depthWith_le {n d M : ℕ}
    {C : Circuit Unbounded.signature n 1} {f : (Fin n → Bool) → Bool}
    (hC : C.Computes interpretation (single f))
    (hd : C.depthWith andOrCost ≤ d) (hM : C.program.cost andOrCost ≤ M) :
    totalInfluence (fun x ↦ signVal (f x)) ≤
      (442 * max (Real.log (M : ℝ)) 1) ^ (max d 1 - 1) := by
  let L : ℝ := max (Real.log (M : ℝ)) 1
  have hL1 : 1 ≤ L := le_max_right _ _
  have hbase1 : 1 ≤ 442 * L := by linarith
  by_cases hd1 : d ≤ 1
  · have hmax : max d 1 - 1 = 0 := by omega
    rw [hmax, pow_zero]
    exact totalInfluence_le_one_of_depthWith_le_one hC (hd.trans hd1)
  · push Not at hd1
    have hd2 : 2 ≤ d := hd1
    by_cases hM1 : M ≤ 1
    · refine (totalInfluence_le_max_andOrCost_one hC).trans ?_
      have hcost1 : max (C.program.cost andOrCost : ℝ) 1 ≤ 1 := by
        refine max_le ?_ le_rfl
        exact_mod_cast hM.trans hM1
      exact hcost1.trans (one_le_pow₀ hbase1)
    · push Not at hM1
      have hM2 : 2 ≤ M := hM1
      let k : ℕ := Nat.log 2 M
      have hk_pow : 2 ^ k ≤ M := Nat.pow_log_le_self 2 (by omega)
      have hM_lt : M < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
      have hk_le_2L : (k : ℝ) ≤ 2 * L := by
        have hpow_real : (2 : ℝ) ^ k ≤ (M : ℝ) := by exact_mod_cast hk_pow
        have hlog_le : Real.log ((2 : ℝ) ^ k) ≤ Real.log (M : ℝ) :=
          Real.log_le_log (by positivity) hpow_real
        rw [Real.log_pow] at hlog_le
        have hhalf := half_le_log_two
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hlogM : Real.log (M : ℝ) ≤ L := le_max_left _ _
        nlinarith
      let t : ℕ := 2 * k + 2
      have ht2 : 2 ≤ t := by omega
      have hM_sq_le : M ^ 2 ≤ 2 ^ t := by
        have hle : M ≤ 2 ^ (k + 1) := hM_lt.le
        calc M ^ 2 ≤ (2 ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left hle 2
          _ = 2 ^ ((k + 1) * 2) := (pow_mul 2 (k + 1) 2).symm
          _ = 2 ^ t := by congr 1; omega
      have ht_le_6L : (t : ℝ) ≤ 6 * L := by
        have ht_cast : (t : ℝ) = 2 * (k : ℝ) + 2 := by dsimp [t]; push_cast; ring
        linarith
      let e : ℕ := d - 2
      have hmax_exp : max d 1 - 1 = e + 1 := by omega
      let F : (Fin n → Bool) → ℝ := fun x ↦ signVal (f x)
      have hmain : totalInfluence F ≤ 34 * (2 * (t : ℝ) + 1) * (16 * (t : ℝ) + 1) ^ e := by
        by_cases hn_small : n < 34 * t * (16 * t + 1) ^ e
        · have hti_n : totalInfluence F ≤ (n : ℝ) := by
            have h := totalInfluence_le_mul_expect_sq F
            have hsq : (𝔼 x : Fin n → Bool, F x ^ 2) = 1 := by
              have h1 : ∀ x, F x ^ 2 = 1 := fun x ↦ by dsimp [F]; rw [sq, signVal_mul_self]
              simp_rw [h1]
              exact expect_const univ_nonempty 1
            rwa [hsq, Fintype.card_fin, mul_one] at h
          have hn_le : (n : ℝ) ≤ 34 * (t : ℝ) * (16 * (t : ℝ) + 1) ^ e := by
            exact_mod_cast hn_small.le
          refine hti_n.trans (hn_le.trans ?_)
          have hnonneg : 0 ≤ (16 * (t : ℝ) + 1) ^ e := by positivity
          nlinarith
        · push Not at hn_small
          let Q : ℕ := 17 * (16 * t + 1) ^ e
          have hQ_pos : 0 < Q := by positivity
          let ℓ : ℕ := n / 17 / (16 * t + 1) ^ e
          have hℓ_eq : ℓ = n / Q := Nat.div_div_eq_div_mul n 17 ((16 * t + 1) ^ e)
          have hm : 2 * t * (16 * t + 1) ^ e ≤ n / 17 :=
            (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
          have h2t_le_ℓ : 2 * t ≤ ℓ :=
            (Nat.le_div_iff_mul_le (by positivity)).mpr hm
          have hℓ1 : 1 ≤ ℓ := by omega
          have hℓn : ℓ ≤ n := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
          have hn_le_ℓ : n ≤ 34 * (16 * t + 1) ^ e * ℓ := by
            have hlt : n < ℓ * Q + Q := by
              rw [hℓ_eq]
              exact Nat.lt_div_mul_add hQ_pos
            have hle2 : ℓ * Q + Q ≤ Q * (2 * ℓ) := by nlinarith
            have h2Q : Q * (2 * ℓ) = 34 * (16 * t + 1) ^ e * ℓ := by dsimp [Q]; ring
            omega
          let W := PartialAssignment.withFree (Fin n) ℓ
          have hW_pos : 0 < #W := by
            rw [PartialAssignment.card_withFree, Fintype.card_fin]
            exact Nat.mul_pos (Nat.choose_pos hℓn) (by positivity)
          let Bad : PartialAssignment (Fin n) → Prop := fun ρ ↦
            ∃ k', C.program.depthsWith andOrCost k' ≤ e + 1 ∧
              ¬ Shallow t ρ fun x ↦ C.program.eval interpretation x k'
          classical
          have hswitch : 2 ^ t * #{ρ ∈ W | Bad ρ} ≤ M * #W := by
            have hm' : t * (16 * t + 1) ^ e ≤ n / 17 :=
              (Nat.mul_le_mul_right _ (by omega : t ≤ 2 * t)).trans hm
            have hs := two_pow_mul_card_filter_exists_not_shallow_le_depthWith
              (p := C.program) ht2 hm' e le_rfl
            have hcard_le :
                #{k' | (C.program.lines k').op ≠ .not ∧
                  C.program.depthsWith andOrCost k' ≤ e + 1} ≤ M :=
              (card_le_card fun k' hk' ↦
                mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hk').2.1⟩).trans
                ((cost_andOrCost_eq_card C.program).symm.trans_le hM)
            exact hs.trans (Nat.mul_le_mul_right _ hcard_le)
          have hper_ρ : ∀ ρ ∈ W,
              totalInfluence (F ∘ ρ.fill) ≤
                2 * (t : ℝ) + if Bad ρ then (M : ℝ) else 0 := fun ρ _ ↦ by
            split_ifs with hbad
            · have hbad_le : totalInfluence (F ∘ ρ.fill) ≤ (M : ℝ) := by
                rcases exists_const_or_circuit_of_comp_fill hC ρ with
                  ⟨b, hb⟩ | ⟨C', hC', _, hC'_cost, _, _⟩
                · have hconst : F ∘ ρ.fill = fun _ ↦ signVal b :=
                    funext fun x ↦ congrArg signVal (hb x)
                  rw [hconst, totalInfluence_const]
                  positivity
                · refine (totalInfluence_le_max_andOrCost_one hC').trans ?_
                  refine max_le ?_ (by exact_mod_cast (by omega : 1 ≤ M))
                  exact_mod_cast hC'_cost.trans hM
              have ht_nonneg : (0 : ℝ) ≤ 2 * (t : ℝ) := by positivity
              linarith
            · rw [add_zero]
              have hgood : ∀ k', C.program.depthsWith andOrCost k' ≤ e + 1 →
                  Shallow t ρ fun x ↦ C.program.eval interpretation x k' :=
                fun k' hk' ↦ by_contra fun hns ↦ hbad ⟨k', hk', hns⟩
              exact good_restriction_totalInfluence_le ht2 hC
                (hd.trans_eq (by omega : d = e + 2)) hgood
          have hsum_W : ∑ ρ ∈ W, totalInfluence (F ∘ ρ.fill) ≤
              (2 * (t : ℝ) + 1) * (#W : ℝ) := by
            have h1 : ∑ ρ ∈ W, totalInfluence (F ∘ ρ.fill) ≤
                (#W : ℝ) * (2 * (t : ℝ)) + (#{ρ ∈ W | Bad ρ} : ℝ) * (M : ℝ) := by
              calc ∑ ρ ∈ W, totalInfluence (F ∘ ρ.fill)
                  ≤ ∑ ρ ∈ W, (2 * (t : ℝ) + if Bad ρ then (M : ℝ) else 0) := sum_le_sum hper_ρ
                _ = (#W : ℝ) * (2 * (t : ℝ)) + ∑ ρ ∈ W, (if Bad ρ then (M : ℝ) else 0) := by
                    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
                _ = (#W : ℝ) * (2 * (t : ℝ)) + (#{ρ ∈ W | Bad ρ} : ℝ) * (M : ℝ) := by
                    rw [← sum_filter, sum_const, nsmul_eq_mul]
            have hbad_sum : (#{ρ ∈ W | Bad ρ} : ℝ) * (M : ℝ) ≤ (#W : ℝ) := by
              have hsw_real : (2 : ℝ) ^ t * (#{ρ ∈ W | Bad ρ} : ℝ) ≤ (M : ℝ) * (#W : ℝ) := by
                exact_mod_cast hswitch
              have hM2_real : (M : ℝ) ^ 2 ≤ (2 : ℝ) ^ t := by exact_mod_cast hM_sq_le
              have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
              have hmulM := mul_le_mul_of_nonneg_right hsw_real (Nat.cast_nonneg M)
              have hprod : (M : ℝ) * (#W : ℝ) * (M : ℝ) = (M : ℝ) ^ 2 * (#W : ℝ) := by ring
              have hle_pow : (M : ℝ) ^ 2 * (#W : ℝ) ≤ (2 : ℝ) ^ t * (#W : ℝ) :=
                mul_le_mul_of_nonneg_right hM2_real (Nat.cast_nonneg #W)
              have hcomb : (2 : ℝ) ^ t * ((#{ρ ∈ W | Bad ρ} : ℝ) * (M : ℝ)) ≤
                  (2 : ℝ) ^ t * (#W : ℝ) := by linarith
              exact le_of_mul_le_mul_left hcomb h2t_pos
            linarith
          have hdc := mul_card_withFree_totalInfluence_eq hℓ1 hℓn F
          have hℓW_pos : (0 : ℝ) < (ℓ : ℝ) * (#W : ℝ) := by positivity
          have hn_real : (n : ℝ) ≤ 34 * (16 * (t : ℝ) + 1) ^ e * (ℓ : ℝ) := by
            exact_mod_cast hn_le_ℓ
          have hmul_le : ((ℓ : ℝ) * (#W : ℝ)) * totalInfluence F ≤
              ((ℓ : ℝ) * (#W : ℝ)) * (34 * (2 * (t : ℝ) + 1) * (16 * (t : ℝ) + 1) ^ e) := by
            rw [hdc]
            calc (n : ℝ) * ∑ ρ ∈ W, totalInfluence (F ∘ ρ.fill)
                ≤ (n : ℝ) * ((2 * (t : ℝ) + 1) * (#W : ℝ)) :=
                  mul_le_mul_of_nonneg_left hsum_W (Nat.cast_nonneg n)
              _ ≤ (34 * (16 * (t : ℝ) + 1) ^ e * (ℓ : ℝ)) * ((2 * (t : ℝ) + 1) * (#W : ℝ)) :=
                  mul_le_mul_of_nonneg_right hn_real (by positivity)
              _ = ((ℓ : ℝ) * (#W : ℝ)) * (34 * (2 * (t : ℝ) + 1) * (16 * (t : ℝ) + 1) ^ e) := by
                  ring
          exact le_of_mul_le_mul_left hmul_le hℓW_pos
      rw [hmax_exp, pow_succ']
      have hfactor1 : 34 * (2 * (t : ℝ) + 1) ≤ 442 * L := by linarith
      have hfactor2 : (16 * (t : ℝ) + 1) ^ e ≤ (442 * L) ^ e :=
        pow_le_pow_left₀ (by positivity) (by linarith) e
      exact hmain.trans (mul_le_mul hfactor1 hfactor2 (by positivity) (by positivity))

private lemma max_log_mono_nat {a b : ℕ} (hab : a ≤ b) :
    max (Real.log (a : ℝ)) 1 ≤ max (Real.log (b : ℝ)) 1 := by
  by_cases ha : a = 0
  · subst ha
    simp
  · refine max_le ?_ (le_max_right _ _)
    have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
    exact (Real.log_le_log ha_pos (by exact_mod_cast hab)).trans (le_max_left _ _)

/-- **Boppana's Bounded-Depth Circuit Total Influence Theorem**: every circuit
`C : Circuit Unbounded.signature n 1` of depth `C.depth ≤ d` and size `C.size ≤ s` computing
`single f` satisfies
`totalInfluence (fun x ↦ signVal (f x)) ≤ (442 * max (Real.log s) 1) ^ (max d 1 - 1)`. -/
theorem boppana_totalInfluence_le {n d s : ℕ} {C : Circuit Unbounded.signature n 1}
    {f : (Fin n → Bool) → Bool} (hC : C.Computes interpretation (single f))
    (hd : C.depth ≤ d) (hs : C.size ≤ s) :
    totalInfluence (fun x ↦ signVal (f x)) ≤
      (442 * max (Real.log (s : ℝ)) 1) ^ (max d 1 - 1) := by
  have hcost_le : C.program.cost andOrCost ≤ s :=
    (cost_andOrCost_eq_card C.program).trans_le
      (((card_filter_le _ _).trans_eq (by simp)).trans hs)
  exact boppana_totalInfluence_le_of_depthWith_le hC
    ((C.depthWith_le_depth andOrCost_le_one).trans hd) hcost_le

-- Sharpness check: 2-bit parity has total influence `2 > 1`, so no circuit of AND/OR depth ≤ 1
-- over the unbounded-fan-in basis can compute 2-bit parity.
example : ¬ ∃ C : Circuit Unbounded.signature 2 1,
    C.Computes interpretation (single (parity 2)) ∧ C.depthWith andOrCost ≤ 1 := by
  rintro ⟨C, hC, hd⟩
  have hle1 := totalInfluence_le_one_of_depthWith_le_one hC hd
  have hchi : (fun x : Fin 2 → Bool ↦ signVal (parity 2 x)) =
      chi ℝ (univ : Finset (Fin 2)) :=
    funext fun x ↦ (chi_eq_signVal_parityOn univ x).symm
  rw [hchi, totalInfluence_chi, card_univ, Fintype.card_fin] at hle1
  norm_num at hle1

end BoppanaMain

end CslibFrontier.Circuits.Boolean.Unbounded
