/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring

import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.Compact.Relabel
import CslibFrontier.Logics.Propositional.CNF.ModelCount.Relabel
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ThreeOccurrence
import CslibFrontier.Logics.Propositional.CNF.ThreeOccurrence.PolyTime
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# `#2SAT-3` is `#P`-complete

Formalizes counting satisfying assignments of `2-CNF` formulas in which every variable occurs at
most `3` times (`SharpTwoSATThree`), proves a native polynomial-time parsimonious reduction from
`SharpTwoSAT` via `CNF.toThreeOccurrence`, and concludes `#P`-completeness under polynomial-time
counting Turing reductions.

## Main definitions

* `Cslib.Complexity.twoSATThreeSyntax`: polynomial-time syntax guard for 2-CNF-3.
* `Cslib.Complexity.SharpTwoSATThree`: `#2SAT-3` counting problem.
* `Cslib.Complexity.toTwoSATThree`: total polynomial-time parsimonious reduction from `#2SAT`.

## Main results

* `Cslib.Complexity.parsimoniousReducible_SharpTwoSAT_SharpTwoSATThree`
* `Cslib.Complexity.countingTuringHard_of_parsimonious_from_SharpTwoSAT`
* `Cslib.Complexity.SharpTwoSATThree_countingTuringComplete`
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Syntax check for 2-CNF-3: every clause has length `≤ 2` and every variable occurs at most `3`
times (with multiplicity). -/
@[expose] def twoSATThreeSyntax (φ : CNF ℕ) : Bool :=
  (φ.all fun c => decide (c.length ≤ 2)) &&
    (φ.vars.all fun v => decide (φ.vars.count v ≤ 3))

theorem twoSATThreeSyntax_iff (φ : CNF ℕ) :
    twoSATThreeSyntax φ = true ↔
      (∀ c ∈ φ, c.length ≤ 2) ∧ (∀ v, φ.vars.count v ≤ 3) := by
  simp only [twoSATThreeSyntax, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hv⟩
    refine ⟨hw, fun v => ?_⟩
    by_cases hm : v ∈ φ.vars
    · exact hv v hm
    · simp [List.count_eq_zero.mpr hm]
  · exact fun h => ⟨h.1, fun v _ => h.2 v⟩

@[fun_prop]
theorem computableInPolyTime_twoSATThreeSyntax :
    ComputableInPolyTime twoSATThreeSyntax encCNF encBool := by
  fun_prop [twoSATThreeSyntax]

/-- `#2SAT-3`: number of satisfying assignments of a 2-CNF formula where every variable occurs at
most 3 times, and `0` outside that syntax. -/
@[expose] def SharpTwoSATThree (φ : CNF ℕ) : ℕ :=
  if twoSATThreeSyntax φ then φ.modelCount else 0

/-- Total polynomial-time parsimonious reduction from `#2SAT` to `#2SAT-3`. -/
def toTwoSATThree (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 2)) then
    φ.toThreeOccurrence.relabel ThreeSATThree.numberCopy
  else [[]]

@[fun_prop]
theorem computableInPolyTime_toTwoSATThree :
    ComputableInPolyTime toTwoSATThree encCNF encCNF := by
  fun_prop [toTwoSATThree]

theorem sharpTwoSATThree_toTwoSATThree (φ : CNF ℕ) :
    SharpTwoSATThree (toTwoSATThree φ) = SharpTwoSAT φ := by
  unfold toTwoSATThree SharpTwoSATThree SharpTwoSAT
  by_cases hw : (φ.all fun c => decide (c.length ≤ 2)) = true
  · simp only [hw, ↓reduceIte]
    have hsyn :
        twoSATThreeSyntax (φ.toThreeOccurrence.relabel ThreeSATThree.numberCopy) = true := by
      rw [twoSATThreeSyntax_iff]
      have hw' : ∀ c ∈ φ, c.length ≤ 2 := by simpa using hw
      refine ⟨?_, ?_⟩
      · intro c hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        simpa using CNF.width_toThreeOccurrence (le_refl 2) hw' d hd
      · exact CNF.count_vars_relabel_le_of_injOn _ _ ThreeSATThree.numberCopy_injective.injOn
          (CNF.count_vars_toThreeOccurrence_le φ)
    simp only [hsyn, ↓reduceIte]
    rw [CNF.modelCount_relabel ThreeSATThree.numberCopy_injective,
      CNF.modelCount_toThreeOccurrence]
  · have hfal : (φ.all fun c => decide (c.length ≤ 2)) = false := Bool.eq_false_iff.mpr hw
    simp only [hfal, Bool.false_eq_true, ↓reduceIte]
    have hsyn : twoSATThreeSyntax [[]] = true := by decide
    simp only [hsyn, ↓reduceIte]
    simp [CNF.modelCount, CNF.eval, Clause.eval]

theorem parsimoniousReducible_SharpTwoSAT_SharpTwoSATThree :
    ParsimoniousReducible encCNF encCNF SharpTwoSAT SharpTwoSATThree :=
  ⟨toTwoSATThree, computableInPolyTime_toTwoSATThree,
    fun φ => (sharpTwoSATThree_toTwoSATThree φ).symm⟩

theorem SharpTwoSATThree.mem_SharpP : SharpTwoSATThree ∈ SharpP encCNF := by
  have h : SharpTwoSATThree = fun φ => if twoSATThreeSyntax φ then SharpSAT φ else 0 := by
    funext φ; rfl
  rw [h]
  exact (parsimoniousReducible_guard computableInPolyTime_twoSATThreeSyntax).mem_SharpP
    SharpSAT.mem_SharpP

@[local fun_prop]
private theorem computableInPolyTime_zVar_aux {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun a => zVar (f a) (g a)) enc encNat := by
  unfold zVar
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_uVar_aux {α : Type} {enc : α ↪ List Bool} {f g h : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary)
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun a => uVar (f a) (g a) (h a)) enc encNat := by
  unfold uVar
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

private theorem computableInPolyTime_clauseWeightTwoSAT_aux :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => clauseWeightTwoSAT p.1 p.2)
      (encPair encCNF encUnary) encCNF := by
  have hd : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars
  have hgadget : ComputableInPolyTime (fun p : ℕ × (Clause ℕ × ℕ) => clauseWeightGadget p.1 p.2)
      (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
    polytime [clauseWeightGadget]
  polytime [clauseWeightTwoSAT, clauseWeightVarTauts]

/-- Any parsimonious reduction from `SharpTwoSAT` transfers `#P`-hardness under polynomial-time
counting Turing reductions via `clauseWeightTwoSAT`. -/
theorem countingTuringHard_of_parsimonious_from_SharpTwoSAT {β : Type} {encB : β ↪ List Bool}
    {g : β → ℕ} (hred : ParsimoniousReducible encCNF encB SharpTwoSAT g) :
    CountingTuringHard encB g := by
  obtain ⟨r, hr, hspec⟩ := hred
  refine CookLevin.SharpSAT_sharpPHard.trans_countingTuring ?_
  let queries (φ : CNF ℕ) : List β :=
    ((List.range (φ.length + 1)).map (clauseWeightTwoSAT φ)).map r
  let bound (φ : CNF ℕ) : ℕ :=
    φ.vars.length + φ.length * (φ.length + 1) + 1
  have hqueries : ComputableInPolyTime queries encCNF (encList encB) := by
    have hcw := computableInPolyTime_clauseWeightTwoSAT_aux
    have hq1 : ComputableInPolyTime
        (fun φ : CNF ℕ => (List.range (φ.length + 1)).map (clauseWeightTwoSAT φ))
        encCNF (encList encCNF) := by polytime
    exact ComputableInPolyTime.mapWithInput hq1 (hr.comp (ComputableInPolyTime.snd _ _))
  have hbound : ComputableInPolyTime bound encCNF encUnary := by
    have hv := SAT.computableInPolyTime_vars_length ComputableInPolyTime.id'
    have hm := SAT.computableInPolyTime_length ComputableInPolyTime.id'
    fun_prop
  have hcombine : ComputableInPolyTime clauseWeightCombine
      (encPair encCNF (encList encNat)) encNat := by
    unfold clauseWeightCombine
    have hm := SAT.computableInPolyTime_length ComputableInPolyTime.id'
    simp only [Nat.testBit_zero]
    fun_prop
  refine PolyTimeOracleProgram.of_batchNatBits queries bound clauseWeightCombine
    hqueries hbound hcombine ?_ ?_
  · intro φ b hb
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hψ
    rw [List.mem_range] at hk
    rw [← hspec]
    exact size_SharpTwoSAT_clauseWeightTwoSAT_le (by omega)
  · intro φ
    have hmap : (queries φ).map g =
        (List.range (φ.length + 1)).map fun k => SharpTwoSAT (clauseWeightTwoSAT φ k) := by
      simp only [queries, List.map_map, Function.comp_def, ← hspec]
    rw [hmap]
    exact clauseWeightCombine_spec φ

/-- **Roth**: `#2SAT-3` is `#P`-complete under polynomial-time counting Turing reductions. -/
theorem SharpTwoSATThree_countingTuringComplete :
    CountingTuringComplete encCNF SharpTwoSATThree :=
  ⟨SharpTwoSATThree.mem_SharpP,
    countingTuringHard_of_parsimonious_from_SharpTwoSAT
      parsimoniousReducible_SharpTwoSAT_SharpTwoSATThree⟩

end Cslib.Complexity
