/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NAEThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.SetSplitting
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
import CslibFrontier.Computability.Complexity.Reduction.Guard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Positive Not-All-Equal Satisfiability and Set Splitting NP-Completeness

This module defines positive (monotone) not-all-equal Boolean satisfiability (`PositiveNAESAT`),
its width-three (`PositiveNAEThreeSAT`) and exact-three distinct-variable
(`PositiveNAEEUThreeSAT`) restrictions on `Cslib.Logic.PL.CNF ℕ` under `Cslib.Complexity.encCNF`,
and proves their `NP`-completeness together with the `NP`-completeness of `SetSplitting`
(Garey and Johnson SP4).

## Main definitions

* `Cslib.Complexity.PositiveNAESAT`: positive CNF formulas having a not-all-equal assignment.
* `Cslib.Complexity.PositiveNAEThreeSAT`: positive NAE-satisfiable CNF formulas of clause width
  at most three.
* `Cslib.Complexity.PositiveNAEEUThreeSAT`: positive NAE-satisfiable CNF formulas in which every
  clause has three pairwise distinct variables.
* `Cslib.Complexity.positiveNAESATToSetSplitting`: polynomial-time reduction from `PositiveNAESAT`
  to `Cslib.Complexity.SetSplitting`.

## Main results

* `Cslib.Complexity.mem_PositiveNAESAT_iff`: semantic characterization of `PositiveNAESAT`.
* `Cslib.Complexity.PositiveNAEEUThreeSAT.npComplete`,
  `Cslib.Complexity.PositiveNAEThreeSAT.npComplete`,
  `Cslib.Complexity.PositiveNAESAT.npComplete`: `NP`-completeness of all three positive NAE-SAT
  variants.
* `Cslib.Complexity.SetSplitting.npComplete`: `NP`-completeness of set splitting / hypergraph
  `2`-colorability.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Positive (monotone) not-all-equal satisfiability: CNF formulas with only positive literals
that have a truth assignment giving every clause at least one true and at least one false
variable. -/
@[expose] def PositiveNAESAT : Set (CNF ℕ) :=
  {φ | OneSAT.positiveCheck φ = true ∧ φ.NAESatisfiable}

/-- Positive not-all-equal satisfiability with clause width at most three. -/
@[expose] def PositiveNAEThreeSAT : Set (CNF ℕ) :=
  {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ OneSAT.positiveCheck φ = true ∧ φ.NAESatisfiable}

/-- Positive not-all-equal satisfiability with exactly three distinct variables per clause. -/
@[expose] def PositiveNAEEUThreeSAT : Set (CNF ℕ) :=
  {φ | φ.IsExactThreeDistinct ∧ OneSAT.positiveCheck φ = true ∧ φ.NAESatisfiable}

/-- Semantic characterization of `PositiveNAESAT`: every literal has polarity `true`, and some
assignment `σ : ℕ → Bool` sets at least one variable to `true` and at least one variable to `false`
in every clause. -/
theorem mem_PositiveNAESAT_iff {φ : CNF ℕ} :
    φ ∈ PositiveNAESAT ↔
      (∀ c ∈ φ, ∀ l ∈ c, l.2 = true) ∧
        ∃ σ : ℕ → Bool, ∀ c ∈ φ,
          (∃ v, (v, true) ∈ c ∧ σ v = true) ∧ (∃ v, (v, true) ∈ c ∧ σ v = false) := by
  change OneSAT.positiveCheck φ = true ∧ φ.NAESatisfiable ↔ _
  rw [OneSAT.positiveCheck_iff]
  refine and_congr_right fun hpos ↦ exists_congr fun σ ↦ ?_
  simp only [CNF.evalNAE, Bool.and_eq_true, CNF.eval_eq_true_iff, Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨ht, hf⟩ c hc
    obtain ⟨⟨u, bu⟩, hu, hσu⟩ := ht c hc
    obtain ⟨⟨v, bv⟩, hv, hσv⟩ := hf c hc
    obtain rfl : bu = true := hpos c hc (u, bu) hu
    obtain rfl : bv = true := hpos c hc (v, bv) hv
    simp only [Bool.not_eq_true'] at hσu hσv
    exact ⟨⟨u, hu, hσu⟩, ⟨v, hv, hσv⟩⟩
  · intro h
    refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
    · obtain ⟨u, hu, hσu⟩ := (h c hc).1
      exact ⟨(u, true), hu, by simp [hσu]⟩
    · obtain ⟨v, hv, hσv⟩ := (h c hc).2
      exact ⟨(v, true), hv, by simp [hσv]⟩

/-- Positive not-all-equal satisfiability belongs to `NP`. -/
theorem PositiveNAESAT.mem_NP : PositiveNAESAT ∈ NP encCNF :=
  mem_NP_of_guard OneSAT.computableInPolyTime_positiveCheck NAESAT.mem_NP fun _ ↦ Iff.rfl

/-- Positive width-three not-all-equal satisfiability belongs to `NP`. -/
theorem PositiveNAEThreeSAT.mem_NP : PositiveNAEThreeSAT ∈ NP encCNF :=
  mem_NP_of_guard PositiveOneInThreeSAT.computableInPolyTime_syntaxCheck NAESAT.mem_NP fun φ ↦ by
    change (_ ∧ _ ∧ _) ↔ _ ∧ _
    rw [PositiveOneInThreeSAT.syntaxCheck_iff, NAESAT, Set.mem_ofPred_eq, and_assoc]

/-- Positive exact-three distinct-variable not-all-equal satisfiability belongs to `NP`. -/
theorem PositiveNAEEUThreeSAT.mem_NP : PositiveNAEEUThreeSAT ∈ NP encCNF :=
  mem_NP_of_guard
    (EUThreeSAT.computableInPolyTime_syntaxCheck.bool_and'
      OneSAT.computableInPolyTime_positiveCheck)
    NAESAT.mem_NP fun φ ↦ by
      change (_ ∧ _ ∧ _) ↔ _ ∧ _
      rw [Bool.and_eq_true, EUThreeSAT.syntaxCheck_iff, NAESAT, Set.mem_ofPred_eq, and_assoc]

/-- Every literal emitted by `toNAEEUThreeSAT` has positive polarity. -/
theorem positiveCheck_toNAEEUThreeSAT (φ : CNF ℕ) :
    OneSAT.positiveCheck (toNAEEUThreeSAT φ) = true := by
  rw [OneSAT.positiveCheck_iff]
  unfold toNAEEUThreeSAT
  split_ifs with hg
  · obtain ⟨hex, hpos⟩ := (PositiveOneInExactThreeSAT.syntaxCheck_iff φ).mp hg
    rw [OneSAT.positiveCheck_iff] at hpos
    intro d hd
    obtain ⟨c, hc, hd'⟩ := List.mem_flatMap.mp hd
    rcases c with _ | ⟨l₀, _ | ⟨l₁, _ | ⟨l₂, _ | _⟩⟩⟩
    · have hlen := (hex [] hc).1; simp at hlen
    · have hlen := (hex [l₀] hc).1; simp at hlen
    · have hlen := (hex [l₀, l₁] hc).1; simp at hlen
    · have h0 : l₀.2 = true := hpos [l₀, l₁, l₂] hc l₀ (by simp)
      have h1 : l₁.2 = true := hpos [l₀, l₁, l₂] hc l₁ (by simp)
      have h2 : l₂.2 = true := hpos [l₀, l₁, l₂] hc l₂ (by simp)
      simp only [NAEEUThreeSAT.clause, List.getD, NAEEUThreeSAT.liftLiteral,
        Clause.oneNAEEncoding, List.mem_cons, List.not_mem_nil, or_false] at hd'
      intro l hl
      rcases hd' with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> simp [h0, h1, h2]
    · have hlen := (hex _ hc).1
      simp at hlen
  · intro d hd l hl
    simp only [List.mem_singleton] at hd
    subst hd
    cases hl

/-- Total correctness of `toNAEEUThreeSAT` as a reduction from `PositiveOneInExactThreeSAT` to
`PositiveNAEEUThreeSAT`. -/
theorem mem_PositiveNAEEUThreeSAT_toNAEEUThreeSAT_iff (φ : CNF ℕ) :
    toNAEEUThreeSAT φ ∈ PositiveNAEEUThreeSAT ↔ φ ∈ PositiveOneInExactThreeSAT := by
  have heq : toNAEEUThreeSAT φ ∈ PositiveNAEEUThreeSAT ↔ toNAEEUThreeSAT φ ∈ NAEEUThreeSAT := by
    change (_ ∧ OneSAT.positiveCheck _ = true ∧ _) ↔ (_ ∧ _)
    simp [positiveCheck_toNAEEUThreeSAT φ]
  exact heq.trans (mem_NAEEUThreeSAT_toNAEEUThreeSAT_iff φ)

/-- `PositiveOneInExactThreeSAT` reduces in polynomial time to `PositiveNAEEUThreeSAT`. -/
theorem polyTimeReducible_positiveOneInExactThreeSAT_positiveNAEEUThreeSAT :
    PolyTimeReducible encCNF encCNF PositiveOneInExactThreeSAT PositiveNAEEUThreeSAT :=
  ⟨toNAEEUThreeSAT, computableInPolyTime_toNAEEUThreeSAT,
    fun φ ↦ (mem_PositiveNAEEUThreeSAT_toNAEEUThreeSAT_iff φ).symm⟩

/-- `PositiveNAEEUThreeSAT` is `NP`-hard. -/
theorem PositiveNAEEUThreeSAT.npHard : NPHard encCNF PositiveNAEEUThreeSAT :=
  PositiveOneInExactThreeSAT_npHard.trans
    polyTimeReducible_positiveOneInExactThreeSAT_positiveNAEEUThreeSAT

/-- `PositiveNAEEUThreeSAT` is `NP`-complete. -/
theorem PositiveNAEEUThreeSAT.npComplete : NPComplete encCNF PositiveNAEEUThreeSAT :=
  ⟨PositiveNAEEUThreeSAT.mem_NP, PositiveNAEEUThreeSAT.npHard⟩

/-- `PositiveNAEEUThreeSAT` reduces in polynomial time to `PositiveNAEThreeSAT`. -/
theorem polyTimeReducible_positiveNAEEUThreeSAT_positiveNAEThreeSAT :
    PolyTimeReducible encCNF encCNF PositiveNAEEUThreeSAT PositiveNAEThreeSAT := by
  refine .of_guard [[]]
    (EUThreeSAT.computableInPolyTime_syntaxCheck.bool_and'
      OneSAT.computableInPolyTime_positiveCheck)
    ComputableInPolyTime.id'
    (by simp [PositiveNAEThreeSAT, CNF.NAESatisfiable, CNF.evalNAE]) fun φ ↦ ?_
  change (_ ∧ _ ∧ _) ↔ _ ∧ (_ ∧ _ ∧ _)
  rw [Bool.and_eq_true, EUThreeSAT.syntaxCheck_iff]
  exact ⟨fun ⟨hex, hp, hs⟩ ↦ ⟨⟨hex, hp⟩, fun c hc ↦ (hex c hc).1.le, hp, hs⟩,
    fun ⟨⟨hex, hp⟩, _, _, hs⟩ ↦ ⟨hex, hp, hs⟩⟩

/-- `PositiveNAEThreeSAT` is `NP`-hard. -/
theorem PositiveNAEThreeSAT.npHard : NPHard encCNF PositiveNAEThreeSAT :=
  PositiveNAEEUThreeSAT.npHard.trans polyTimeReducible_positiveNAEEUThreeSAT_positiveNAEThreeSAT

/-- `PositiveNAEThreeSAT` is `NP`-complete. -/
theorem PositiveNAEThreeSAT.npComplete : NPComplete encCNF PositiveNAEThreeSAT :=
  ⟨PositiveNAEThreeSAT.mem_NP, PositiveNAEThreeSAT.npHard⟩

/-- `PositiveNAEThreeSAT` reduces in polynomial time to `PositiveNAESAT`. -/
theorem polyTimeReducible_positiveNAEThreeSAT_positiveNAESAT :
    PolyTimeReducible encCNF encCNF PositiveNAEThreeSAT PositiveNAESAT := by
  refine .of_guard [[]] PositiveOneInThreeSAT.computableInPolyTime_syntaxCheck
    ComputableInPolyTime.id'
    (by simp [PositiveNAESAT, CNF.NAESatisfiable, CNF.evalNAE]) fun φ ↦ ?_
  change (_ ∧ _ ∧ _) ↔ _ ∧ (_ ∧ _)
  rw [PositiveOneInThreeSAT.syntaxCheck_iff]
  exact ⟨fun ⟨hw, hp, hs⟩ ↦ ⟨⟨hw, hp⟩, hp, hs⟩, fun ⟨⟨hw, hp⟩, _, hs⟩ ↦ ⟨hw, hp, hs⟩⟩

/-- `PositiveNAESAT` is `NP`-hard. -/
theorem PositiveNAESAT.npHard : NPHard encCNF PositiveNAESAT :=
  PositiveNAEThreeSAT.npHard.trans polyTimeReducible_positiveNAEThreeSAT_positiveNAESAT

/-- `PositiveNAESAT` is `NP`-complete. -/
theorem PositiveNAESAT.npComplete : NPComplete encCNF PositiveNAESAT :=
  ⟨PositiveNAESAT.mem_NP, PositiveNAESAT.npHard⟩

/-- Polynomial-time reduction from `PositiveNAESAT` to `SetSplitting`, mapping a positive CNF
formula `φ` to the family of variable lists of its clauses over ground list `φ.vars`, and rejecting
non-positive formulas via `⟨[], [[]]⟩`. -/
def positiveNAESATToSetSplitting (φ : CNF ℕ) : SetSplittingInstance :=
  if OneSAT.positiveCheck φ then
    { ground := φ.vars, sets := φ.map fun c ↦ c.map Prod.fst }
  else
    { ground := [], sets := [[]] }

/-- `positiveNAESATToSetSplitting` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_positiveNAESATToSetSplitting :
    ComputableInPolyTime positiveNAESATToSetSplitting encCNF encSetSplitting := by
  have : ComputableInPolyTime (CNF.vars (V := ℕ))
      (encList (encList (encPair encNat encBool))) (encList encNat) :=
    CNF.computableInPolyTime_vars encNat
  have : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ φ.map fun c ↦ c.map Prod.fst)
      (encList (encList (encPair encNat encBool))) (encList (encList encNat)) := by
    fun_prop
  have : ComputableInPolyTime OneSAT.positiveCheck
      (encList (encList (encPair encNat encBool))) encBool :=
    OneSAT.computableInPolyTime_positiveCheck
  unfold positiveNAESATToSetSplitting encCNF
  fun_prop

/-- Exact membership equivalence for `positiveNAESATToSetSplitting`. -/
theorem mem_SetSplitting_positiveNAESATToSetSplitting_iff (φ : CNF ℕ) :
    positiveNAESATToSetSplitting φ ∈ SetSplitting ↔ φ ∈ PositiveNAESAT := by
  classical
  unfold positiveNAESATToSetSplitting
  by_cases hpos : OneSAT.positiveCheck φ = true
  · simp only [hpos, ↓reduceIte, mem_PositiveNAESAT_iff]
    have hpos' := (OneSAT.positiveCheck_iff φ).mp hpos
    rw [and_iff_right hpos']
    have hmem_vars : ∀ {c : Clause ℕ} {v : ℕ}, c ∈ φ → (v, true) ∈ c → v ∈ φ.vars :=
      fun {c v} hc hv ↦ List.mem_map.mpr ⟨(v, true), List.mem_flatten.mpr ⟨c, hc, hv⟩, rfl⟩
    constructor
    · rintro ⟨A, _, hsp⟩
      refine ⟨fun v ↦ decide (v ∈ A), fun c hc ↦ ?_⟩
      obtain ⟨⟨u, hu, huA⟩, ⟨v, hv, _, hvA⟩⟩ := hsp (c.map Prod.fst) (List.mem_map_of_mem hc)
      obtain ⟨⟨u, bu⟩, hu', rfl⟩ := List.mem_map.mp hu
      obtain ⟨⟨v, bv⟩, hv', rfl⟩ := List.mem_map.mp hv
      obtain rfl : bu = true := hpos' c hc (u, bu) hu'
      obtain rfl : bv = true := hpos' c hc (v, bv) hv'
      exact ⟨⟨u, hu', decide_eq_true huA⟩, ⟨v, hv', decide_eq_false hvA⟩⟩
    · rintro ⟨σ, hσ⟩
      refine ⟨φ.vars.toFinset.filter fun v ↦ σ v = true,
        fun v hv ↦ List.mem_toFinset.mp (Finset.mem_filter.mp hv).1, ?_⟩
      intro s hs
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
      obtain ⟨⟨u, hu, hσu⟩, ⟨v, hv, hσv⟩⟩ := hσ c hc
      refine ⟨⟨u, List.mem_map.mpr ⟨(u, true), hu, rfl⟩,
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hmem_vars hc hu), hσu⟩⟩,
        ⟨v, List.mem_map.mpr ⟨(v, true), hv, rfl⟩, hmem_vars hc hv,
          fun hvA ↦ Bool.false_ne_true (hσv.symm.trans (Finset.mem_filter.mp hvA).2)⟩⟩
  · simp only [hpos, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun ⟨A, _, hsp⟩ ↦ ?_, fun h ↦ (hpos h.1).elim⟩
    obtain ⟨⟨u, hu, _⟩, _⟩ := hsp [] (List.mem_singleton_self [])
    cases hu

/-- `PositiveNAESAT` reduces in polynomial time to `SetSplitting`. -/
theorem polyTimeReducible_positiveNAESAT_setSplitting :
    PolyTimeReducible encCNF encSetSplitting PositiveNAESAT SetSplitting :=
  ⟨positiveNAESATToSetSplitting, computableInPolyTime_positiveNAESATToSetSplitting,
    fun φ ↦ (mem_SetSplitting_positiveNAESATToSetSplitting_iff φ).symm⟩

/-- `SetSplitting` (Garey and Johnson SP4) is `NP`-hard. -/
theorem SetSplitting.npHard : NPHard encSetSplitting SetSplitting :=
  PositiveNAESAT.npHard.trans polyTimeReducible_positiveNAESAT_setSplitting

/-- `SetSplitting` (Garey and Johnson SP4) is `NP`-complete. -/
theorem SetSplitting.npComplete : NPComplete encSetSplitting SetSplitting :=
  ⟨SetSplitting.mem_NP, SetSplitting.npHard⟩

end Cslib.Complexity
