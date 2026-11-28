module

public import CslibFrontier.Computability.Complexity.ProofSystem.ExtendedFrege

import Cslib.Computability.Circuit.Boolean.Basic
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Range-Avoidance `τ`-Formulas and Uniform Circuit Builders

Given a Boolean circuit `c : Circuit Boolean.signature n m` and candidate output `b : BitString m`,
the **`τ`-formula** `tauFormula varBase c b`
encodes `b ∉ Set.range (c.eval Boolean.interpretation)` as a propositional tautology on atoms for
the `n` inputs and `c.size` gates of `c`, alongside declarative `RawGate` circuit builders.

## Main definitions

* `CslibFrontier.ProofComplexity.litNe`, `CslibFrontier.ProofComplexity.formulaIff`: fixed-width
  mismatch literal and propositional biconditional.
* `CslibFrontier.ProofComplexity.lineSpecFormula`, `CslibFrontier.ProofComplexity.gateEqFormula`,
  `CslibFrontier.ProofComplexity.stdWireAtom`: gate-operation formulas and contiguous wire
  numbering.
* `CslibFrontier.ProofComplexity.tauFormulaWith`, `CslibFrontier.ProofComplexity.tauFormula`:
  general and standard `τ(c)_b` range-avoidance formulas.
* `CslibFrontier.ProofComplexity.RawGate`, `CslibFrontier.ProofComplexity.appendRawGates`,
  `CslibFrontier.ProofComplexity.buildRawCircuit`, `CslibFrontier.ProofComplexity.evalRawGates`,
  `CslibFrontier.ProofComplexity.buildTauFormulaRaw`: declarative gate-list circuits and builders.

## Main results

* `CslibFrontier.ProofComplexity.tauFormulaWith_mem_taut_iff` and
  `CslibFrontier.ProofComplexity.tauFormula_mem_taut_iff`: `τ(c)_b ∈ TAUT ↔ b ∉ Set.range c.eval`.
* `CslibFrontier.ProofComplexity.exists_substitute_encFormula_tauFormula`: fixed-length Boolean
  substitution representation of `b ↦ encFormula (tauFormula 0 c b)`.
* `CslibFrontier.ProofComplexity.computableInPolyTime_tauFormulaRaw`: uniform polynomial-time
  construction of `tauFormulaWith` for compiled `RawGate` circuits.


-/

public section

namespace CslibFrontier.ProofComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Cslib.Complexity
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Finset

/-! ### `τ`-formulas for Boolean circuits -/

/-- Fixed-width mismatch literal asserting that atom `v` evaluates differently from `b`:
`(v → ⊥) ∨ (⊥ ∧ ⊥)` when `b = true`, and `(v ∨ ⊥) ∧ (⊥ → ⊥)` when `b = false`. Both encodings
consist of `encFormula (.atom v)` followed by an exact `30`-bit suffix. -/
@[expose]
def litNe (v : ℕ) (b : Bool) : Formula :=
  if b then .or (.imp (.atom v) .falsum) (.and .falsum .falsum)
  else .and (.or (.atom v) .falsum) (.imp .falsum .falsum)

/-- Boolean evaluation of `litNe v b` is `true` iff `σ v ≠ b`. -/
@[simp]
theorem eval_litNe_bool (v : ℕ) (b : Bool) (σ : ℕ → Bool) :
    (litNe v b).eval σ = (σ v != b) := by
  cases b <;> simp only [litNe, ↓reduceIte, Bool.false_eq_true, Proposition.eval_or_bool,
    Proposition.eval_and_bool, Proposition.eval_imp_bool, Proposition.eval_atom_bool,
    Proposition.eval_falsum_bool] <;> cases σ v <;> rfl

/-- Atoms occurring in `litNe v b`. -/
@[simp]
theorem formulaAtoms_litNe (v : ℕ) (b : Bool) : formulaAtoms (litNe v b) = {v} := by
  cases b <;> simp [litNe]

/-- Substitution through `litNe v b`. -/
theorem subst_litNe (f : ℕ → Formula) (v : ℕ) (b : Bool) :
    (litNe v b).subst f =
      if b then .or (.imp (f v) .falsum) (.and .falsum .falsum)
      else .and (.or (f v) .falsum) (.imp .falsum .falsum) := by
  cases b <;> rfl

/-- The `30`-bit postfix suffix after `encFormula (.atom v)` in `encFormula (litNe v b)`. -/
def litNeSuffix (b : Bool) : List Bool :=
  if b then
    encFormula .falsum ++ frame (encFormTok (.inr 3)) ++
      encFormula .falsum ++ encFormula .falsum ++ frame (encFormTok (.inr 1)) ++
      frame (encFormTok (.inr 2))
  else
    encFormula .falsum ++ frame (encFormTok (.inr 2)) ++
      encFormula .falsum ++ encFormula .falsum ++ frame (encFormTok (.inr 3)) ++
      frame (encFormTok (.inr 1))

/-- `litNeSuffix b` has exact length `30` for both `b = false` and `b = true`. -/
@[simp]
theorem length_litNeSuffix (b : Bool) : (litNeSuffix b).length = 30 := by
  cases b <;> decide

/-- Exact binary encoding of `litNe v b`: `encFormula (.atom v) ++ litNeSuffix b`. -/
theorem encFormula_litNe (v : ℕ) (b : Bool) :
    encFormula (litNe v b) = encFormula (.atom v) ++ litNeSuffix b := by
  cases b <;> simp [litNe, litNeSuffix, encFormula_or, encFormula_and, encFormula_imp,
    List.append_assoc]

/-- Propositional biconditional `(A → B) ∧ (B → A)`. -/
@[expose]
def formulaIff (A B : Formula) : Formula :=
  .and (.imp A B) (.imp B A)

/-- Boolean evaluation of `formulaIff A B` holds iff `A.eval σ = B.eval σ`. -/
@[simp]
theorem eval_formulaIff_eq_true (A B : Formula) (σ : ℕ → Bool) :
    (formulaIff A B).eval σ = true ↔ A.eval σ = B.eval σ := by
  simp only [formulaIff, Proposition.eval_and_bool, Proposition.eval_imp_bool]
  cases A.eval σ <;> cases B.eval σ <;> simp

/-- Atoms occurring in `formulaIff A B`. -/
theorem formulaAtoms_formulaIff (A B : Formula) :
    formulaAtoms (formulaIff A B) = formulaAtoms A ∪ formulaAtoms B := by
  simp only [formulaIff, formulaAtoms_and, formulaAtoms_imp]
  ext v; simp

/-- Encoded bit length of `formulaIff A B`. -/
theorem length_encFormula_formulaIff (A B : Formula) :
    (encFormula (formulaIff A B)).length =
      (encFormula A).length + (encFormula B).length + (frame (encFormTok (.inr 3))).length +
      ((encFormula B).length + (encFormula A).length + (frame (encFormTok (.inr 3))).length) +
      (frame (encFormTok (.inr 1))).length := by
  simp only [formulaIff, encFormula_and, encFormula_imp, List.length_append]

/-- De Morgan constant gate interpretation. -/
theorem interpretation_const (b : Bool) (x : Fin 0 → Bool) :
    interpretation (.const b) x = b := rfl

/-- De Morgan negation gate interpretation. -/
theorem interpretation_not (x : Fin 1 → Bool) :
    interpretation .not x = !x 0 := rfl

/-- De Morgan conjunction gate interpretation. -/
theorem interpretation_and (x : Fin 2 → Bool) :
    interpretation .and x = (x 0 && x 1) := rfl

/-- De Morgan disjunction gate interpretation. -/
theorem interpretation_or (x : Fin 2 → Bool) :
    interpretation .or x = (x 0 || x 1) := rfl

/-- Formula expressing the Boolean operation of a circuit gate `l : Line signature n g` under atom
numbering `wAtom : Wire n g → ℕ`. -/
@[expose]
def lineSpecFormula {n g : ℕ} (wAtom : Wire n g → ℕ) (l : Line signature n g) : Formula :=
  match l with
  | ⟨.const false, _⟩ => .falsum
  | ⟨.const true, _⟩ => .imp .falsum .falsum
  | ⟨.not, ws⟩ => .imp (.atom (wAtom (ws 0))) .falsum
  | ⟨.and, ws⟩ => .and (.atom (wAtom (ws 0))) (.atom (wAtom (ws 1)))
  | ⟨.or, ws⟩ => .or (.atom (wAtom (ws 0))) (.atom (wAtom (ws 1)))

/-- Boolean evaluation of `lineSpecFormula` matches `Line.eval Boolean.interpretation`. -/
theorem eval_lineSpecFormula {n g : ℕ} (wAtom : Wire n g → ℕ) (l : Line signature n g)
    (σ : ℕ → Bool) :
    (lineSpecFormula wAtom l).eval σ =
      l.eval interpretation (fun i => σ (wAtom (.input i))) (fun k => σ (wAtom (.gate k))) := by
  rcases l with ⟨op, ws⟩
  have hw (w : Wire n g) :
      Wire.elim (fun i => σ (wAtom (.input i))) (fun k => σ (wAtom (.gate k))) w = σ (wAtom w) := by
    cases w <;> rfl
  cases op with
  | const b => cases b <;> rfl
  | not => simp [lineSpecFormula, Line.eval, interpretation_not, hw]
  | and => simp [lineSpecFormula, Line.eval, interpretation_and, hw]
  | or => simp [lineSpecFormula, Line.eval, interpretation_or, hw]

/-- Gate-definition formula asserting `wAtom (.gate k) ↔ lineSpecFormula wAtom l`. -/
@[expose]
def gateEqFormula {n g : ℕ} (wAtom : Wire n g → ℕ) (k : Fin g) (l : Line signature n g) :
    Formula :=
  formulaIff (.atom (wAtom (.gate k))) (lineSpecFormula wAtom l)

/-- Boolean evaluation of `gateEqFormula`. -/
theorem eval_gateEqFormula_eq_true {n g : ℕ} (wAtom : Wire n g → ℕ) (k : Fin g)
    (l : Line signature n g) (σ : ℕ → Bool) :
    (gateEqFormula wAtom k l).eval σ = true ↔
      σ (wAtom (.gate k)) =
        l.eval interpretation (fun i => σ (wAtom (.input i))) (fun r => σ (wAtom (.gate r))) := by
  rw [gateEqFormula, eval_formulaIff_eq_true, Proposition.eval_atom_bool, eval_lineSpecFormula]

/-- Every atom in `gateEqFormula wAtom k l` lies in the range of `wAtom`. -/
theorem formulaAtoms_gateEqFormula_subset {n g : ℕ} (wAtom : Wire n g → ℕ) (k : Fin g)
    (l : Line signature n g) :
    (formulaAtoms (gateEqFormula wAtom k l) : Set ℕ) ⊆ Set.range wAtom := by
  intro v hv
  simp only [mem_coe, gateEqFormula, formulaAtoms_formulaIff, mem_union, formulaAtoms_atom,
    mem_singleton] at hv
  rcases hv with rfl | hv
  · exact ⟨.gate k, rfl⟩
  · rcases l with ⟨op, ws⟩
    cases op with
    | const b => cases b <;> simp [lineSpecFormula] at hv
    | not =>
      simp only [lineSpecFormula, formulaAtoms_imp, formulaAtoms_atom, formulaAtoms_falsum,
        union_empty, mem_singleton] at hv
      exact ⟨ws 0, hv.symm⟩
    | and =>
      simp only [lineSpecFormula, formulaAtoms_and, formulaAtoms_atom, mem_union,
        mem_singleton] at hv
      exact hv.elim (fun h => ⟨ws 0, h.symm⟩) (fun h => ⟨ws 1, h.symm⟩)
    | or =>
      simp only [lineSpecFormula, formulaAtoms_or, formulaAtoms_atom, mem_union,
        mem_singleton] at hv
      exact hv.elim (fun h => ⟨ws 0, h.symm⟩) (fun h => ⟨ws 1, h.symm⟩)

/-- Standard contiguous wire-to-atom numbering starting at `varBase`: input `i : Fin n` maps to
`varBase + i.val`, and gate `k : Fin g` maps to `varBase + n + k.val`. -/
@[expose]
def stdWireAtom (varBase n : ℕ) {g : ℕ} : Wire n g → ℕ
  | .input i => varBase + i.val
  | .gate k => varBase + n + k.val

/-- Standard wire atom of an input wire `.input i`. -/
@[simp] theorem stdWireAtom_input (varBase n : ℕ) {g : ℕ} (i : Fin n) :
    stdWireAtom varBase n (.input i : Wire n g) = varBase + i.val := rfl
/-- Standard wire atom of a gate wire `.gate k`. -/
@[simp] theorem stdWireAtom_gate (varBase n : ℕ) {g : ℕ} (k : Fin g) :
    stdWireAtom varBase n (.gate k : Wire n g) = varBase + n + k.val := rfl

/-- `stdWireAtom varBase n` is injective. -/
theorem stdWireAtom_injective (varBase n g : ℕ) :
    Function.Injective (stdWireAtom varBase n (g := g)) := by
  intro w₁ w₂ h; cases w₁ <;> cases w₂ <;> simp only [stdWireAtom] at h
  · exact congrArg Wire.input (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Wire.gate (Fin.ext (by omega))

/-- Every `stdWireAtom varBase n w` belongs to `[varBase, varBase + n + g)`. -/
theorem stdWireAtom_mem_Ico (varBase n : ℕ) {g : ℕ} (w : Wire n g) :
    stdWireAtom varBase n w ∈ Ico varBase (varBase + n + g) := by
  cases w <;> (simp only [stdWireAtom, mem_Ico]; omega)

/-- Downward shift `(· - varBase)` reduces `stdWireAtom varBase n` to `stdWireAtom 0 n`. -/
@[simp] theorem stdWireAtom_sub (varBase n : ℕ) {g : ℕ} (w : Wire n g) :
    stdWireAtom varBase n w - varBase = stdWireAtom 0 n w := by
  cases w <;> (simp only [stdWireAtom]; omega)

/-- List of gate-definition axioms of a Boolean circuit `c` under wire numbering `wAtom`. -/
@[expose] def gateDefsWith {n m : ℕ} (c : Circuit signature n m) (wAtom : Wire n c.size → ℕ) :
    List Formula := List.ofFn fun k : Fin c.size => gateEqFormula wAtom k (c.program.lines k)

/-- `gateDefsWith c wAtom` has exact length `c.size`. -/
@[simp] theorem length_gateDefsWith {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) : (gateDefsWith c wAtom).length = c.size := List.length_ofFn

/-- Expressing `gateDefsWith c wAtom` as a map over `List.finRange c.size`. -/
theorem gateDefsWith_eq_map_finRange {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) : gateDefsWith c wAtom =
      (List.finRange c.size).map fun k => gateEqFormula wAtom k (c.program.lines k) :=
  List.ofFn_eq_map

/-- Output-mismatch disjunction `⋁_{j < m} litNe (wAtom (c.outputs j)) (b j)`. -/
@[expose] def outMismatchWith {n m : ℕ} (c : Circuit signature n m) (wAtom : Wire n c.size → ℕ)
    (b : BitString m) : Formula :=
  bigOr (List.ofFn fun j : Fin m => litNe (wAtom (c.outputs j)) (b j))

/-- The **`τ`-formula** `τ(c)_b` under a general wire-to-atom numbering `wAtom`. -/
@[expose] def tauFormulaWith {n m : ℕ} (c : Circuit signature n m) (wAtom : Wire n c.size → ℕ)
    (b : BitString m) : Formula :=
  Frege.Formula.imps (gateDefsWith c wAtom) (outMismatchWith c wAtom b)

/-- Standard **`τ`-formula** `τ(c)_b` on atoms `[varBase, varBase + n + c.size)`. -/
@[expose] def tauFormula (varBase : ℕ) {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) : Formula := tauFormulaWith c (stdWireAtom varBase n) b

/-- Boolean evaluation of `Frege.Formula.imps Δ φ`. -/
theorem eval_imps_eq_true (Δ : List Formula) (φ : Formula) (σ : ℕ → Bool) :
    (Frege.Formula.imps Δ φ).eval σ = true ↔
      (∀ δ ∈ Δ, δ.eval σ = true) → φ.eval σ = true := by
  induction Δ with
  | nil => simp [Frege.Formula.imps]
  | cons δ Δ ih =>
    change (Proposition.imp δ (Frege.Formula.imps Δ φ)).eval σ = true ↔ _
    rw [Proposition.eval_imp_bool]
    cases hδ : δ.eval σ <;> simp [hδ, ih]

/-- Boolean evaluation of `tauFormulaWith c wAtom b` fails under `σ` iff `σ` satisfies every gate
equation of `c` and assigns output vector `b`. -/
theorem eval_tauFormulaWith_eq_true {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) (b : BitString m) (σ : ℕ → Bool) :
    (tauFormulaWith c wAtom b).eval σ = true ↔
      (∀ k : Fin c.size, σ (wAtom (.gate k)) =
        (c.program.lines k).eval interpretation
          (fun i => σ (wAtom (.input i))) (fun r => σ (wAtom (.gate r)))) →
      c.eval interpretation (fun i => σ (wAtom (.input i))) ≠ b := by
  rw [tauFormulaWith, eval_imps_eq_true]
  have hgates : (∀ δ ∈ gateDefsWith c wAtom, δ.eval σ = true) ↔
      ∀ k : Fin c.size, σ (wAtom (.gate k)) =
        (c.program.lines k).eval interpretation
          (fun i => σ (wAtom (.input i))) (fun r => σ (wAtom (.gate r))) := by
    simp only [gateDefsWith, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
      eval_gateEqFormula_eq_true]
  have hout_iff : (outMismatchWith c wAtom b).eval σ = true ↔
      ∃ j : Fin m, σ (wAtom (c.outputs j)) ≠ b j := by
    simp [outMismatchWith, eval_bigOr_bool, List.ofFn_eq_map, List.any_eq_true]
  refine ⟨fun h hg heq => ?_, fun h hg => ?_⟩
  · obtain ⟨j, hj⟩ := hout_iff.1 (h (hgates.2 hg))
    have hval : (fun r => σ (wAtom (.gate r))) =
        c.program.eval interpretation (fun i => σ (wAtom (.input i))) :=
      c.program.eq_eval_of_forall_lines_eval interpretation _ _ fun k => (hg k).symm
    apply hj
    have hcj : c.eval interpretation (fun i => σ (wAtom (.input i))) j =
        σ (wAtom (c.outputs j)) := by
      cases hw : c.outputs j with
      | input i => simp [Circuit.eval, Program.trace, hw, Wire.elim]
      | gate k => simp [Circuit.eval, Program.trace, hw, Wire.elim, ← congrFun hval k]
    exact hcj.symm.trans (congrFun heq j)
  · have hg' := hgates.1 hg
    have hne := h hg'
    have hval : (fun r => σ (wAtom (.gate r))) =
        c.program.eval interpretation (fun i => σ (wAtom (.input i))) :=
      c.program.eq_eval_of_forall_lines_eval interpretation _ _ fun k => (hg' k).symm
    have hex : ∃ j : Fin m, c.eval interpretation (fun i => σ (wAtom (.input i))) j ≠ b j := by
      by_contra hall; push Not at hall; exact hne (funext hall)
    obtain ⟨j, hj⟩ := hex
    refine hout_iff.2 ⟨j, fun heq => hj ?_⟩
    cases hw : c.outputs j with
    | input i => simpa [Circuit.eval, Program.trace, hw, Wire.elim] using heq
    | gate k =>
      rw [hw] at heq
      simp only [Circuit.eval, Program.trace, Function.comp_apply, hw, Wire.elim]
      exact (congrFun hval k).symm.trans heq

/-- **Soundness and completeness of `tauFormulaWith`.** For any injective wire-to-atom map `wAtom`,
`tauFormulaWith c wAtom b ∈ TAUT` iff `b ∉ Set.range (c.eval interpretation)`. -/
theorem tauFormulaWith_mem_taut_iff {n m : ℕ} (c : Circuit signature n m)
    {wAtom : Wire n c.size → ℕ} (hinj : Function.Injective wAtom) (b : BitString m) :
    tauFormulaWith c wAtom b ∈ TAUT ↔ b ∉ Set.range (c.eval interpretation) := by
  classical
  constructor
  · rintro htaut ⟨x, rfl⟩
    let wVal : Wire n c.size → Bool
      | .input i => x i
      | .gate k => c.program.eval interpretation x k
    let σ : ℕ → Bool := fun v =>
      if h : ∃ w, wAtom w = v then wVal (Classical.choose h) else false
    have hσ (w : Wire n c.size) : σ (wAtom w) = wVal w := by
      have hex : ∃ w', wAtom w' = wAtom w := ⟨w, rfl⟩
      simp only [σ, hex, dite_true]
      exact congrArg wVal (hinj (Classical.choose_spec hex))
    have hin : (fun i => σ (wAtom (.input i))) = x := funext fun i => hσ (.input i)
    have hgt : (fun r => σ (wAtom (.gate r))) = c.program.eval interpretation x :=
      funext fun r => hσ (.gate r)
    have hsat := (eval_tauFormulaWith_eq_true c wAtom (c.eval interpretation x) σ).1 (htaut σ)
    refine hsat (fun k => ?_) (congrArg (c.eval interpretation) hin)
    rw [hin, hgt, hσ (.gate k)]
    exact (c.program.lines_eval interpretation x k).symm
  · intro hnot σ
    exact (eval_tauFormulaWith_eq_true c wAtom b σ).2 fun _ heq => hnot ⟨_, heq⟩

/-- **Soundness and completeness of `τ(c)_b`.** `tauFormula varBase c b ∈ TAUT` if and only if
`b ∉ Set.range (c.eval Boolean.interpretation)`. -/
theorem tauFormula_mem_taut_iff (varBase : ℕ) {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) :
    tauFormula varBase c b ∈ TAUT ↔ b ∉ Set.range (c.eval interpretation) :=
  tauFormulaWith_mem_taut_iff c (stdWireAtom_injective varBase n c.size) b

/-- Reindexing output wires along `hm : m₁ = m₂` preserves `tauFormulaWith`. -/
theorem tauFormulaWith_reindexOutputs {n m₁ m₂ : ℕ} (c : Circuit signature n m₁) (hm : m₁ = m₂)
    (wAtom : Wire n c.size → ℕ) (b : BitString m₂) :
    tauFormulaWith
        { size := c.size
          program := c.program
          outputs := fun j => c.outputs (j.cast hm.symm) } wAtom b =
      tauFormulaWith c wAtom (fun j => b (j.cast hm)) := by
  subst hm; rfl

/-- Atoms of `Frege.Formula.imps Δ φ`. -/
theorem formulaAtoms_imps (Δ : List Formula) (φ : Formula) :
    formulaAtoms (Frege.Formula.imps Δ φ) =
      Δ.foldr (fun δ acc => formulaAtoms δ ∪ acc) (formulaAtoms φ) := by
  induction Δ with
  | nil => rfl
  | cons δ Δ ih =>
    change formulaAtoms (.imp δ (Frege.Formula.imps Δ φ)) = _
    rw [formulaAtoms_imp, ih]; rfl

/-- Every atom occurring in `tauFormulaWith c wAtom b` lies in `Set.range wAtom`. -/
theorem formulaAtoms_tauFormulaWith_subset {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) (b : BitString m) :
    (formulaAtoms (tauFormulaWith c wAtom b) : Set ℕ) ⊆ Set.range wAtom := by
  have hfold : ∀ (l : List Formula) (init : Finset ℕ),
      (∀ δ ∈ l, (formulaAtoms δ : Set ℕ) ⊆ Set.range wAtom) →
      (init : Set ℕ) ⊆ Set.range wAtom →
      ((l.foldr (fun δ acc => formulaAtoms δ ∪ acc) init : Finset ℕ) : Set ℕ) ⊆
        Set.range wAtom := by
    intro l init
    induction l with
    | nil => exact fun _ hi => hi
    | cons δ l ih =>
      intro hl hi v hv
      simp only [List.foldr_cons, mem_coe, mem_union] at hv
      exact hv.elim (fun h => hl δ List.mem_cons_self h)
        (fun h => ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hi h)
  rw [tauFormulaWith, formulaAtoms_imps]
  refine hfold _ _ (fun δ hδ => ?_) ?_
  · simp only [gateDefsWith, List.mem_ofFn] at hδ
    obtain ⟨k, rfl⟩ := hδ
    exact formulaAtoms_gateEqFormula_subset wAtom k _
  · rw [outMismatchWith, formulaAtoms_bigOr]
    refine hfold _ _ (fun α hα => ?_) (by simp)
    simp only [List.mem_ofFn] at hα
    obtain ⟨j, rfl⟩ := hα
    intro v hv
    simp only [mem_coe, formulaAtoms_litNe, mem_singleton] at hv
    exact ⟨c.outputs j, hv.symm⟩

/-- Every atom occurring in `tauFormula varBase c b` lies in `[varBase, varBase + n + c.size)`. -/
theorem formulaAtoms_tauFormula_subset (varBase : ℕ) {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) :
    formulaAtoms (tauFormula varBase c b) ⊆ Ico varBase (varBase + n + c.size) := by
  intro v hv
  obtain ⟨w, rfl⟩ := formulaAtoms_tauFormulaWith_subset c (stdWireAtom varBase n) b hv
  exact stdWireAtom_mem_Ico varBase n w

/-- Substitution commutes over `Frege.Formula.imps`. -/
theorem subst_imps (f : ℕ → Formula) (Δ : List Formula) (φ : Formula) :
    (Frege.Formula.imps Δ φ).subst f =
      Frege.Formula.imps (Δ.map (Proposition.subst f)) (φ.subst f) := by
  induction Δ with
  | nil => rfl
  | cons δ Δ ih =>
    change Proposition.imp (δ.subst f) ((Frege.Formula.imps Δ φ).subst f) = _
    rw [ih]; rfl

/-- Substituting through `outMismatchWith`. -/
theorem subst_outMismatchWith (f : ℕ → Formula) {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) (b : BitString m) :
    (outMismatchWith c wAtom b).subst f =
      bigOr (List.ofFn fun j : Fin m => (litNe (wAtom (c.outputs j)) (b j)).subst f) := by
  simp only [outMismatchWith, subst_bigOr, List.map_ofFn]; rfl

/-- Congruence of `tauFormulaWith` under substitutions agreeing pointwise along two wire
numberings. -/
theorem subst_tauFormulaWith_congr {n m : ℕ} (c : Circuit signature n m)
    (wAtom₁ wAtom₂ : Wire n c.size → ℕ) (b : BitString m) (f₁ f₂ : ℕ → Formula)
    (h : ∀ w, f₁ (wAtom₁ w) = f₂ (wAtom₂ w)) :
    (tauFormulaWith c wAtom₁ b).subst f₁ = (tauFormulaWith c wAtom₂ b).subst f₂ := by
  have hspec (l : Line signature n c.size) :
      (lineSpecFormula wAtom₁ l).subst f₁ = (lineSpecFormula wAtom₂ l).subst f₂ := by
    rcases l with ⟨op, _⟩
    cases op with
    | const bv => cases bv <;> rfl
    | not => simp [lineSpecFormula, subst_imp, subst_var, subst_falsum, h]
    | and => simp [lineSpecFormula, subst_and, subst_var, h]
    | or => simp [lineSpecFormula, subst_or, subst_var, h]
  dsimp only [tauFormulaWith]
  rw [subst_imps, subst_imps]
  congr 1
  · simp only [gateDefsWith, List.map_ofFn]; congr 1; funext k
    simp [gateEqFormula, formulaIff, subst_and, subst_imp, subst_var, hspec, h]
  · rw [subst_outMismatchWith, subst_outMismatchWith]; congr 2; funext j
    rw [subst_litNe, subst_litNe, h]

/-- Renaming atoms commutes directly with `tauFormulaWith`. -/
theorem renameAtoms_tauFormulaWith (r : ℕ → ℕ) {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) (b : BitString m) :
    renameAtoms r (tauFormulaWith c wAtom b) = tauFormulaWith c (r ∘ wAtom) b :=
  (subst_tauFormulaWith_congr c wAtom (r ∘ wAtom) b (fun v => .atom (r v)) Proposition.atom
    fun _ => rfl).trans (subst_atom _)

/-- Shifting atoms down by `varBase` maps `tauFormula varBase c b` to `tauFormula 0 c b`. -/
@[simp]
theorem renameAtoms_sub_tauFormula (varBase : ℕ) {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) :
    renameAtoms (· - varBase) (tauFormula varBase c b) = tauFormula 0 c b := by
  rw [tauFormula, renameAtoms_tauFormulaWith, tauFormula]
  congr 1; funext w; exact stdWireAtom_sub varBase n w

/-- Two substitutions agreeing on `formulaAtoms φ` produce identical formulas. -/
theorem subst_congr_atoms {f g : ℕ → Formula} {φ : Formula}
    (h : ∀ v ∈ formulaAtoms φ, f v = g v) : φ.subst f = φ.subst g :=
  subst_congr h

/-! ### Encoded-length bounds and fixed-length Boolean substitution for `τ(c)_b` -/

/-- `encNat` length is monotone in the natural number. -/
theorem length_encNat_mono {a b : ℕ} (h : a ≤ b) : (encNat a).length ≤ (encNat b).length := by
  change a.bits.length ≤ b.bits.length
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

/-- `(encNat a).length ≤ a` for every `a : ℕ`. -/
theorem length_encNat_le_self (a : ℕ) : (encNat a).length ≤ a := by
  change a.bits.length ≤ a; rw [Nat.size_eq_bits_len]
  suffices ∀ m : ℕ, m.size ≤ m from this a
  intro m; induction m using Nat.binaryRec with
  | zero => simp
  | bit b n ih =>
    cases b <;> by_cases hn : n = 0
    · subst hn; simp
    · rw [Nat.size_bit (by simp [Nat.bit_val, hn])]; simp only [Nat.bit_val,
      Bool.toNat_false]; omega
    · subst hn; simp
    · rw [Nat.size_bit (by simp [Nat.bit_val])]; simp only [Nat.bit_val, Bool.toNat_true]; omega

/-- Upper bound on the encoded bit length of an atomic formula `atom v`. -/
theorem length_encFormula_atom_le (v : ℕ) :
    (encFormula (.atom v)).length ≤ 2 * (encNat v).length + 3 := by
  simp only [encFormula_apply, toPostfix_atom, encList_cons, encList_nil, List.append_nil,
    length_frame, encFormTok_inl, encSum_inl, List.length_cons]; omega

/-- Upper bound on the encoded bit length of `gateEqFormula wAtom k l` when every wire atom is
at most `V`. -/
theorem length_encFormula_gateEqFormula_le {n g V : ℕ} {wAtom : Wire n g → ℕ}
    (hV : ∀ w, wAtom w ≤ V) (k : Fin g) (l : Line signature n g) :
    (encFormula (gateEqFormula wAtom k l)).length ≤ 16 * ((encNat V).length + 10) := by
  have hatom (w : Wire n g) : (encFormula (.atom (wAtom w))).length ≤ 2 * (encNat V).length + 3 :=
    (length_encFormula_atom_le _).trans (by have := length_encNat_mono (hV w); omega)
  have hop (op : Fin 4) : (frame (encFormTok (.inr op))).length ≤ 10 := by fin_cases op <;> decide
  have hbot : (encFormula .falsum).length ≤ 10 := by decide
  have hspec : (encFormula (lineSpecFormula wAtom l)).length ≤ 4 * (encNat V).length + 30 := by
    rcases l with ⟨op, ws⟩
    cases op with
    | const b =>
      cases b
      · simpa only [lineSpecFormula] using hbot.trans (by omega)
      · have := hop 3; simp only [lineSpecFormula, encFormula_imp, List.length_append]; omega
    | not =>
      have := hatom (ws 0); have := hop 3
      simp only [lineSpecFormula, encFormula_imp, List.length_append]; omega
    | and =>
      have := hatom (ws 0); have := hatom (ws 1); have := hop 1
      simp only [lineSpecFormula, encFormula_and, List.length_append]; omega
    | or =>
      have := hatom (ws 0); have := hatom (ws 1); have := hop 2
      simp only [lineSpecFormula, encFormula_or, List.length_append]; omega
  have hk := hatom (.gate k); have h1 := hop 1; have h3 := hop 3
  simp only [gateEqFormula, formulaIff, encFormula_and, encFormula_imp, List.length_append]; omega

/-- Encoded bit length of `bigOr αs` when every disjunct has encoded length at most `B`. -/
theorem length_encFormula_bigOr_le {αs : List Formula} {B : ℕ}
    (hB : ∀ α ∈ αs, (encFormula α).length ≤ B) :
    (encFormula (bigOr αs)).length ≤ (αs.length + 1) * (B + 10) := by
  have hbot : (encFormula .falsum).length ≤ 10 := by decide
  have hop2 : (frame (encFormTok (.inr 2))).length ≤ 10 := by decide
  induction αs with
  | nil => simp only [bigOr_nil, List.length_nil]; omega
  | cons α rest ih =>
    have hα := hB α List.mem_cons_self
    cases rest with
    | nil => simp only [bigOr_singleton, List.length_cons, List.length_nil]; nlinarith
    | cons β tail =>
      have ihr := ih fun x hx => hB x (List.mem_cons_of_mem _ hx)
      simp only [bigOr_cons_cons, encFormula_or, List.length_append, List.length_cons] at ihr ⊢
      nlinarith

/-- Encoded length of `Frege.Formula.imps Δ φ` when every antecedent has encoded length `≤ B`. -/
theorem length_encFormula_imps_le {Δ : List Formula} {B : ℕ} (φ : Formula)
    (hB : ∀ δ ∈ Δ, (encFormula δ).length ≤ B) :
    (encFormula (Frege.Formula.imps Δ φ)).length ≤ Δ.length * (B + 10) + (encFormula φ).length := by
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
  induction Δ with
  | nil => simp [Frege.Formula.imps]
  | cons δ Δ ih =>
    have hδ := hB δ List.mem_cons_self
    have ihΔ := ih fun x hx => hB x (List.mem_cons_of_mem _ hx)
    change (encFormula (Proposition.imp δ (Frege.Formula.imps Δ φ))).length ≤ _
    rw [encFormula_imp, List.length_append, List.length_append, List.length_cons]; nlinarith

/-- Explicit upper bound on `(encFormula (tauFormulaWith c wAtom b)).length` when all wire atoms
are bounded by `V`. -/
theorem length_encFormula_tauFormulaWith_le {n m V : ℕ} (c : Circuit signature n m)
    {wAtom : Wire n c.size → ℕ} (hV : ∀ w, wAtom w ≤ V) (b : BitString m) :
    (encFormula (tauFormulaWith c wAtom b)).length ≤
      20 * (c.size + m + 1) * ((encNat V).length + 12) := by
  have hout : (encFormula (outMismatchWith c wAtom b)).length ≤
      (m + 1) * (2 * (encNat V).length + 45) := by
    have := length_encFormula_bigOr_le (B := 2 * (encNat V).length + 35)
      (αs := List.ofFn fun j : Fin m => litNe (wAtom (c.outputs j)) (b j)) fun α hα => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hα
        have ha := length_encFormula_atom_le (wAtom (c.outputs j))
        have hb := length_encNat_mono (hV (c.outputs j))
        rw [encFormula_litNe, List.length_append, length_litNeSuffix]; omega
    simpa only [outMismatchWith, List.length_ofFn] using this
  have himp := length_encFormula_imps_le (B := 16 * ((encNat V).length + 10))
    (Δ := gateDefsWith c wAtom) (outMismatchWith c wAtom b) fun δ hδ => by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hδ; exact length_encFormula_gateEqFormula_le hV k _
  simp only [gateDefsWith, List.length_ofFn] at himp
  exact (himp.trans (Nat.add_le_add_left hout _)).trans (by nlinarith)

/-- Explicit upper bound on `(encFormula (tauFormula varBase c b)).length`. -/
theorem length_encFormula_tauFormula_le (varBase : ℕ) {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) :
    (encFormula (tauFormula varBase c b)).length ≤
      20 * (c.size + m + 1) * ((encNat (varBase + n + c.size)).length + 12) :=
  length_encFormula_tauFormulaWith_le c
    (fun w => (mem_Ico.1 (stdWireAtom_mem_Ico varBase n w)).2.le) b

/-- Simple quadratic bound on `(encFormula (tauFormula 0 c b)).length`. -/
theorem length_encFormula_tauFormula_zero_le {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) :
    (encFormula (tauFormula 0 c b)).length ≤ 20 * (n + c.size + m + 12) ^ 2 := by
  have h1 := length_encFormula_tauFormula_le 0 c b
  have h2 : (encNat (0 + n + c.size)).length ≤ n + c.size := by
    simpa using length_encNat_le_self (n + c.size)
  have h3 : 20 * (c.size + m + 1) * ((encNat (0 + n + c.size)).length + 12) ≤
      20 * (c.size + m + 1) * (n + c.size + 12) := Nat.mul_le_mul_left _ (by omega)
  exact (h1.trans h3).trans (by nlinarith)

/-- Lower bound `m ≤ (encFormula (tauFormulaWith c wAtom b)).length`. -/
theorem output_le_length_encFormula_tauFormulaWith {n m : ℕ} (c : Circuit signature n m)
    (wAtom : Wire n c.size → ℕ) (b : BitString m) :
    m ≤ (encFormula (tauFormulaWith c wAtom b)).length := by
  have himps_ge (Δ : List Formula) (φ : Formula) :
      (encFormula φ).length ≤ (encFormula (Frege.Formula.imps Δ φ)).length := by
    induction Δ with
    | nil => exact le_rfl
    | cons δ Δ ih =>
      change _ ≤ (encFormula (Proposition.imp δ (Frege.Formula.imps Δ φ))).length
      rw [encFormula_imp, List.length_append, List.length_append]; omega
  have hbig_ge : ∀ l : List Formula,
      (∀ α ∈ l, 1 ≤ (encFormula α).length) → l.length ≤ (encFormula (bigOr l)).length := by
    intro l; induction l with
    | nil => intro _; simp
    | cons α rest ih =>
      intro hl; have hα := hl α List.mem_cons_self
      cases rest with
      | nil => simpa using hα
      | cons _ _ =>
        have ihr := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
        simp only [bigOr_cons_cons, encFormula_or, List.length_append, List.length_cons] at ihr ⊢
        omega
  have hb := hbig_ge (List.ofFn fun j : Fin m => litNe (wAtom (c.outputs j)) (b j))
    fun α _ => length_encFormula_pos α
  rw [List.length_ofFn] at hb
  exact hb.trans (himps_ge _ (outMismatchWith c wAtom b))

/-- Lower bound `m ≤ (encFormula (tauFormula varBase c b)).length`. -/
theorem output_le_length_encFormula_tauFormula (varBase : ℕ) {n m : ℕ} (c : Circuit signature n m)
    (b : BitString m) :
    m ≤ (encFormula (tauFormula varBase c b)).length :=
  output_le_length_encFormula_tauFormulaWith c (stdWireAtom varBase n) b

/-- **Fixed-length substitution representation of `b ↦ encFormula (tauFormula 0 c b)`.** -/
theorem exists_substitute_encFormula_tauFormula {n m : ℕ} (c : Circuit signature n m) :
    ∃ (L : ℕ) (ρ : Fin L → Fin (m + m) ⊕ Bool),
      L ≤ 20 * (n + c.size + m + 12) ^ 2 ∧
      ∀ b : BitString m,
        encFormula (tauFormula 0 c b) =
          List.ofFn (substitute ρ (Fin.append b (fun j => !b j))) := by
  let ext (b : BitString m) : BitString (m + m) := Fin.append b (fun j => !b j)
  let evalSW (sw : List (Fin (m + m) ⊕ Bool)) (b : BitString m) : List Bool :=
    sw.map fun s => s.elim (ext b) id
  let constSW (bs : List Bool) : List (Fin (m + m) ⊕ Bool) := bs.map Sum.inr
  have hconst (bs : List Bool) (b : BitString m) : evalSW (constSW bs) b = bs := by
    simp [evalSW, constSW, List.map_map]
  have happ (s₁ s₂ : List (Fin (m + m) ⊕ Bool)) (b : BitString m) :
      evalSW (s₁ ++ s₂) b = evalSW s₁ b ++ evalSW s₂ b := List.map_append
  let sufEntry (j : Fin m) : Bool → Bool → Fin (m + m) ⊕ Bool
    | false, false => .inr false | true, true => .inr true
    | false, true => .inl (Fin.castAdd m j) | true, false => .inl (Fin.natAdd m j)
  have hsufEntry (j : Fin m) (bf bt : Bool) (b : BitString m) :
      (sufEntry j bf bt).elim (ext b) id = if b j then bt else bf := by
    have hL : ext b (Fin.castAdd m j) = b j := Fin.append_left b (fun i => !b i) j
    have hR : ext b (Fin.natAdd m j) = !b j := Fin.append_right b (fun i => !b i) j
    cases bf <;> cases bt
    · cases b j <;> rfl
    · change ext b (Fin.castAdd m j) = _; rw [hL]; cases b j <;> rfl
    · change ext b (Fin.natAdd m j) = _; rw [hR]; cases b j <;> rfl
    · cases b j <;> rfl
  let sufSW (j : Fin m) : List (Fin (m + m) ⊕ Bool) :=
    List.ofFn fun r : Fin 30 =>
      sufEntry j ((litNeSuffix false).getD r.val false) ((litNeSuffix true).getD r.val false)
  have hsuf (j : Fin m) (b : BitString m) : evalSW (sufSW j) b = litNeSuffix (b j) := by
    have hgt (bv : Bool) (r : ℕ) (h₂ : r < 30) :
        (litNeSuffix bv).getD r false = (litNeSuffix bv)[r]'(by simp [h₂]) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [h₂]), Option.getD_some]
    cases hbj : b j
    · refine List.ext_getElem (by simp [evalSW, sufSW]) fun r _ h₂ => ?_
      rw [length_litNeSuffix] at h₂
      simp only [evalSW, sufSW, List.getElem_map, List.getElem_ofFn, hsufEntry, hbj,
        Bool.false_eq_true, ↓reduceIte]
      exact hgt false r h₂
    · refine List.ext_getElem (by simp [evalSW, sufSW]) fun r _ h₂ => ?_
      rw [length_litNeSuffix] at h₂
      simp only [evalSW, sufSW, List.getElem_map, List.getElem_ofFn, hsufEntry, hbj, ↓reduceIte]
      exact hgt true r h₂
  let litSW (j : Fin m) : List (Fin (m + m) ⊕ Bool) :=
    constSW (encFormula (.atom (stdWireAtom 0 n (c.outputs j)))) ++ sufSW j
  have hlit (j : Fin m) (b : BitString m) :
      evalSW (litSW j) b = encFormula (litNe (stdWireAtom 0 n (c.outputs j)) (b j)) := by
    rw [encFormula_litNe]; simp only [litSW, happ, hconst, hsuf]
  have hbig : ∀ js : List (Fin m), ∃ sw : List (Fin (m + m) ⊕ Bool), ∀ b : BitString m,
      evalSW sw b =
        encFormula (bigOr (js.map fun j => litNe (stdWireAtom 0 n (c.outputs j)) (b j))) := by
    intro js; induction js with
    | nil => exact ⟨constSW (encFormula .falsum), fun b => hconst _ b⟩
    | cons j rest ih =>
      cases rest with
      | nil => exact ⟨litSW j, hlit j⟩
      | cons _ _ =>
        obtain ⟨swr, hswr⟩ := ih
        exact ⟨litSW j ++ swr ++ constSW (frame (encFormTok (.inr 2))), fun b => by
          simp only [List.map_cons, bigOr_cons_cons, encFormula_or, happ, hlit, hswr, hconst]⟩
  obtain ⟨swOut, hswOut⟩ := hbig (List.finRange m)
  have himps : ∀ Δ : List Formula, ∃ sw : List (Fin (m + m) ⊕ Bool), ∀ b : BitString m,
      evalSW sw b = encFormula (Frege.Formula.imps Δ (outMismatchWith c (stdWireAtom 0 n) b)) := by
    intro Δ; induction Δ with
    | nil => exact ⟨swOut, fun b => by
        change evalSW swOut b = encFormula (outMismatchWith c (stdWireAtom 0 n) b)
        rw [outMismatchWith, List.ofFn_eq_map]; exact hswOut b⟩
    | cons δ Δ ih =>
      obtain ⟨swΔ, hswΔ⟩ := ih
      exact ⟨constSW (encFormula δ) ++ swΔ ++ constSW (frame (encFormTok (.inr 3))), fun b => by
        change evalSW _ b = encFormula (.imp δ (Frege.Formula.imps Δ _))
        simp only [encFormula_imp, happ, hconst, hswΔ]⟩
  obtain ⟨sw, hsw⟩ := himps (gateDefsWith c (stdWireAtom 0 n))
  let ρ : Fin sw.length → Fin (m + m) ⊕ Bool := fun i => sw[i.val]
  have hρ (b : BitString m) : encFormula (tauFormula 0 c b) = List.ofFn (substitute ρ (ext b)) := by
    rw [tauFormula, tauFormulaWith, ← hsw b]
    exact List.ext_getElem (by simp [evalSW]) fun i _ _ => by simp [evalSW, substitute, ρ]
  have hlen : sw.length = (encFormula (tauFormula 0 c (fun _ => false))).length := by
    rw [hρ (fun _ => false), List.length_ofFn]
  exact ⟨sw.length, ρ, hlen ▸ length_encFormula_tauFormula_zero_le c _, hρ⟩

/-! ### Declarative `RawGate` circuits and uniform polynomial-time `τ`-formula construction -/

/-- First-order Boolean gate representation referencing prior wires by raw index `< n + g`
(inputs `0 .. n - 1`, prior gates `n .. n + g - 1`; out-of-range indices default to wire `0` or
`const false`). -/
inductive RawGate where
  /-- Constant Boolean gate `const b`. -/
  | const (b : Bool)
  /-- Unary negation gate `¬ w`. -/
  | not (w : ℕ)
  /-- Binary conjunction gate `w₁ ∧ w₂`. -/
  | and (w₁ w₂ : ℕ)
  /-- Binary disjunction gate `w₁ ∨ w₂`. -/
  | or (w₁ w₂ : ℕ)
  deriving DecidableEq

/-- Resolve a raw wire index `idx` to a typed `Wire n g` (falling back to `.input 0` or `.gate 0`
if out of bounds when `n + g > 0`). -/
@[expose] def natToWire (n g idx : ℕ) : Option (Wire n g) :=
  if h1 : idx < n then some (.input ⟨idx, h1⟩)
  else if h2 : idx - n < g then some (.gate ⟨idx - n, h2⟩)
  else none

/-- `natToWire n g idx` resolves input indices `idx < n` to `.input ⟨idx, h⟩`. -/
theorem natToWire_of_lt (g : ℕ) {n idx : ℕ} (h : idx < n) :
    natToWire n g idx = some (.input ⟨idx, h⟩) := by simp [natToWire, h]

/-- `natToWire n g idx` resolves gate indices `n ≤ idx < n + g` to `.gate ⟨idx - n, h2⟩`. -/
theorem natToWire_of_ge_of_lt {n g idx : ℕ} (h1 : ¬idx < n) (h2 : idx - n < g) :
    natToWire n g idx = some (.gate ⟨idx - n, h2⟩) := by simp [natToWire, h1, h2]

/-- Inverse of `natToWire`: raw wire index in `0 .. n + g - 1`. -/
@[expose] def wireToNat {n g : ℕ} : Wire n g → ℕ
  | .input i => i.val
  | .gate k => n + k.val

/-- Raw index of an input wire `.input i`. -/
@[simp] theorem wireToNat_input {n g : ℕ} (i : Fin n) :
    wireToNat (.input i : Wire n g) = i.val := rfl

/-- Raw index of a gate wire `.gate k`. -/
@[simp] theorem wireToNat_gate {n g : ℕ} (k : Fin g) :
    wireToNat (.gate k : Wire n g) = n + k.val := rfl

/-- `wireToNat w < n + g`. -/
theorem wireToNat_lt {n g : ℕ} (w : Wire n g) : wireToNat w < n + g := by
  cases w <;> (simp only [wireToNat_input, wireToNat_gate]; omega)

/-- `natToWire` left-inverts `wireToNat`. -/
@[simp]
theorem natToWire_wireToNat {n g : ℕ} (w : Wire n g) : natToWire n g (wireToNat w) = some w := by
  cases w with
  | input i => exact natToWire_of_lt g i.isLt
  | gate k =>
    rw [wireToNat_gate, natToWire_of_ge_of_lt (by omega) (by omega)]
    congr 2; exact Fin.ext (by dsimp; omega)

/-- `natToWire n g idx` succeeds whenever `idx < n + g`. -/
theorem isSome_natToWire_of_lt {n g idx : ℕ} (h : idx < n + g) :
    ∃ w : Wire n g, natToWire n g idx = some w ∧ wireToNat w = idx := by
  by_cases h1 : idx < n
  · exact ⟨.input ⟨idx, h1⟩, natToWire_of_lt g h1, rfl⟩
  · have h2 : idx - n < g := by omega
    exact ⟨.gate ⟨idx - n, h2⟩, natToWire_of_ge_of_lt h1 h2, by simp; omega⟩

/-- Convert a `RawGate` into a typed `Line signature n g` (falling back to `const false` if any
referenced index is `≥ n + g`). -/
@[expose] def rawGateToLine (n g : ℕ) : RawGate → Line signature n g
  | .const b => ⟨.const b, Fin.elim0⟩
  | .not w =>
    match natToWire n g w with
    | some w₀ => ⟨.not, fun _ => w₀⟩
    | none => ⟨.const false, Fin.elim0⟩
  | .and w₁ w₂ =>
    match natToWire n g w₁, natToWire n g w₂ with
    | some u₁, some u₂ => ⟨.and, ![u₁, u₂]⟩
    | _, _ => ⟨.const false, Fin.elim0⟩
  | .or w₁ w₂ =>
    match natToWire n g w₁, natToWire n g w₂ with
    | some u₁, some u₂ => ⟨.or, ![u₁, u₂]⟩
    | _, _ => ⟨.const false, Fin.elim0⟩

/-- `rawGateToLine` on a constant gate `.const b`. -/
@[simp] theorem rawGateToLine_const (n g : ℕ) (b : Bool) :
    rawGateToLine n g (.const b) = ⟨.const b, Fin.elim0⟩ := rfl

/-- `rawGateToLine` on an in-bounds negation gate `.not w`. -/
theorem rawGateToLine_not_of_eq {n g w : ℕ} {u : Wire n g} (hu : natToWire n g w = some u) :
    rawGateToLine n g (.not w) = ⟨.not, fun _ => u⟩ := by
  dsimp only [rawGateToLine]; rw [hu]

/-- `rawGateToLine` on an in-bounds conjunction gate `.and w₁ w₂`. -/
theorem rawGateToLine_and_of_eq {n g w₁ w₂ : ℕ} {u₁ u₂ : Wire n g}
    (h₁ : natToWire n g w₁ = some u₁) (h₂ : natToWire n g w₂ = some u₂) :
    rawGateToLine n g (.and w₁ w₂) = ⟨.and, ![u₁, u₂]⟩ := by
  dsimp only [rawGateToLine]; rw [h₁, h₂]

/-- `rawGateToLine` on an in-bounds disjunction gate `.or w₁ w₂`. -/
theorem rawGateToLine_or_of_eq {n g w₁ w₂ : ℕ} {u₁ u₂ : Wire n g}
    (h₁ : natToWire n g w₁ = some u₁) (h₂ : natToWire n g w₂ = some u₂) :
    rawGateToLine n g (.or w₁ w₂) = ⟨.or, ![u₁, u₂]⟩ := by
  dsimp only [rawGateToLine]; rw [h₁, h₂]

/-- Gate-count widening `Wire n g → Wire n g'` for `g ≤ g'`. -/
@[expose] def wireCastLE {n g g' : ℕ} (h : g ≤ g') : Wire n g → Wire n g'
  | .input i => .input i
  | .gate k => .gate (k.castLE h)

/-- `wireCastLE` leaves input wires unchanged. -/
@[simp] theorem wireCastLE_input {n g g' : ℕ} (h : g ≤ g') (i : Fin n) :
    wireCastLE h (.input i) = .input i := rfl

/-- `wireCastLE` widens gate indices via `Fin.castLE`. -/
@[simp] theorem wireCastLE_gate {n g g' : ℕ} (h : g ≤ g') (k : Fin g) :
    wireCastLE h (.gate k : Wire n g) = .gate (k.castLE h) := rfl

/-- `wireCastLE` preserves `wireToNat`. -/
@[simp] theorem wireToNat_wireCastLE {n g g' : ℕ} (h : g ≤ g') (w : Wire n g) :
    wireToNat (wireCastLE h w) = wireToNat w := by cases w <;> rfl

/-- Cast a `Program signature n g` along a gate-count equality `g = g'`. -/
def programCast {n g g' : ℕ} (h : g = g') (p : Program signature n g) : Program signature n g' :=
  h ▸ p

/-- Append a list of `RawGate`s to an existing `Program signature n g`. -/
def appendRawGates {n : ℕ} :
    ∀ {g : ℕ}, Program signature n g → (gs : List RawGate) → Program signature n (g + gs.length)
  | _, p, [] => p
  | g, p, rg :: rest =>
    programCast (by simp; omega) (appendRawGates (p.gate (rawGateToLine n g rg)) rest)

/-- Single-step Boolean evaluation of a `RawGate` against a flat wire-value list `vals` of length
`n + g` (out-of-range indices evaluate to `const false`, matching `rawGateToLine`). -/
@[expose] def evalRawGate (vals : List Bool) : RawGate → Bool
  | .const b => b
  | .not w => if w < vals.length then !vals.getD w false else false
  | .and w₁ w₂ =>
    if w₁ < vals.length && w₂ < vals.length then vals.getD w₁ false && vals.getD w₂ false else false
  | .or w₁ w₂ =>
    if w₁ < vals.length && w₂ < vals.length then vals.getD w₁ false || vals.getD w₂ false else false

/-- Evaluating a constant `RawGate`. -/
@[simp] theorem evalRawGate_const (vals : List Bool) (b : Bool) :
    evalRawGate vals (.const b) = b := rfl

/-- Evaluating a negation `RawGate`. -/
theorem evalRawGate_not (vals : List Bool) (w : ℕ) :
    evalRawGate vals (.not w) = if w < vals.length then !vals.getD w false else false := rfl

/-- Evaluating a conjunction `RawGate`. -/
theorem evalRawGate_and (vals : List Bool) (w₁ w₂ : ℕ) :
    evalRawGate vals (.and w₁ w₂) =
      if w₁ < vals.length && w₂ < vals.length then vals.getD w₁ false && vals.getD w₂ false
      else false := rfl

/-- Evaluating a disjunction `RawGate`. -/
theorem evalRawGate_or (vals : List Bool) (w₁ w₂ : ℕ) :
    evalRawGate vals (.or w₁ w₂) =
      if w₁ < vals.length && w₂ < vals.length then vals.getD w₁ false || vals.getD w₂ false
      else false := rfl

/-- Evaluate a list of `RawGate`s starting from initial wire-value list `vals`, returning the full
extended wire-value list of length `vals.length + gs.length`. -/
@[expose] def evalRawGates (vals : List Bool) (gs : List RawGate) : List Bool :=
  gs.foldl (fun acc rg => acc ++ [evalRawGate acc rg]) vals

/-- Evaluating an empty `RawGate` list leaves `vals` unchanged. -/
@[simp] theorem evalRawGates_nil (vals : List Bool) : evalRawGates vals [] = vals := rfl

/-- Evaluating `rg :: gs` appends `evalRawGate vals rg` and continues on `gs`. -/
@[simp] theorem evalRawGates_cons (vals : List Bool) (rg : RawGate) (gs : List RawGate) :
    evalRawGates vals (rg :: gs) = evalRawGates (vals ++ [evalRawGate vals rg]) gs := rfl

/-- Total wire-list length after `evalRawGates vals gs`. -/
@[simp] theorem length_evalRawGates (vals : List Bool) (gs : List RawGate) :
    (evalRawGates vals gs).length = vals.length + gs.length := by
  induction gs generalizing vals with
  | nil => simp [evalRawGates]
  | cons rg rest ih =>
    simp only [evalRawGates, List.foldl_cons, List.length_cons] at ih ⊢; rw [ih]; simp; omega

/-- `evalRawGates vals gs` keeps `vals` as a prefix. -/
theorem getD_evalRawGates_lt (vals : List Bool) (gs : List RawGate) {i : ℕ} (hi : i < vals.length) :
    (evalRawGates vals gs).getD i false = vals.getD i false := by
  induction gs generalizing vals with
  | nil => rfl
  | cons rg rest ih =>
    simp only [evalRawGates, List.foldl_cons] at ih ⊢
    rw [ih (vals ++ [evalRawGate vals rg]) (by simp; omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
      List.getElem?_eq_getElem hi, List.getElem_append_left hi]

/-- Splitting `evalRawGates vals (gs₁ ++ gs₂)`. -/
theorem evalRawGates_append (vals : List Bool) (gs₁ gs₂ : List RawGate) :
    evalRawGates vals (gs₁ ++ gs₂) = evalRawGates (evalRawGates vals gs₁) gs₂ :=
  List.foldl_append

/-- Exact agreement between `rawGateToLine.eval` and `evalRawGate`. -/
theorem eval_rawGateToLine {n g : ℕ} (x : Fin n → Bool) (gv : Fin g → Bool) (rg : RawGate) :
    (rawGateToLine n g rg).eval interpretation x gv =
      evalRawGate (List.ofFn x ++ List.ofFn gv) rg := by
  set vals := List.ofFn x ++ List.ofFn gv
  have hlen : vals.length = n + g := by simp [vals]
  have hlk (idx : ℕ) (h : idx < n + g) (w : Wire n g) (hw : natToWire n g idx = some w) :
      Wire.elim x gv w = vals.getD idx false := by
    by_cases h1 : idx < n
    · simp only [natToWire, h1, dite_true, Option.some.injEq] at hw; subst hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.getElem_append_left (by simp [h1]), List.getElem_ofFn]; rfl
    · have h2 : idx - n < g := by omega
      simp only [natToWire, h1, h2, dite_false, dite_true, Option.some.injEq] at hw; subst hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.getElem_append_right (by simp; omega)]; simp [Wire.elim]
  have hnone (idx : ℕ) (h : ¬(idx < n + g)) : natToWire n g idx = none := by
    simp only [natToWire]; split_ifs <;> first | omega | rfl
  cases rg with
  | const b => simp [Line.eval, interpretation_const]
  | not w =>
    by_cases hw : w < n + g
    · obtain ⟨u, hu, -⟩ := isSome_natToWire_of_lt hw
      rw [rawGateToLine_not_of_eq hu, evalRawGate_not, hlen, ite_eq_left hw]
      simp [Line.eval, interpretation_not, hlk w hw u hu]
    · dsimp only [rawGateToLine]; rw [hnone w hw, evalRawGate_not, hlen, ite_eq_right hw]
      simp [Line.eval, interpretation_const]
  | and w₁ w₂ =>
    by_cases h12 : w₁ < n + g ∧ w₂ < n + g
    · obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h12.1
      obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h12.2
      rw [rawGateToLine_and_of_eq hu₁ hu₂, evalRawGate_and, hlen]
      simp [h12.1, h12.2, Line.eval, interpretation_and, hlk w₁ h12.1 u₁ hu₁, hlk w₂ h12.2 u₂ hu₂]
    · simp only [evalRawGate_and, hlen, Bool.and_eq_true, decide_eq_true_eq, h12,
        ↓reduceIte]
      by_cases h1 : w₁ < n + g
      · dsimp only [rawGateToLine]; rw [hnone w₂ fun h2 => h12 ⟨h1, h2⟩]
        cases natToWire n g w₁ <;> simp [Line.eval, interpretation_const]
      · dsimp only [rawGateToLine]; rw [hnone w₁ h1]; simp [Line.eval, interpretation_const]
  | or w₁ w₂ =>
    by_cases h12 : w₁ < n + g ∧ w₂ < n + g
    · obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt h12.1
      obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt h12.2
      rw [rawGateToLine_or_of_eq hu₁ hu₂, evalRawGate_or, hlen]
      simp [h12.1, h12.2, Line.eval, interpretation_or, hlk w₁ h12.1 u₁ hu₁, hlk w₂ h12.2 u₂ hu₂]
    · simp only [evalRawGate_or, hlen, Bool.and_eq_true, decide_eq_true_eq, h12,
        ↓reduceIte]
      by_cases h1 : w₁ < n + g
      · dsimp only [rawGateToLine]; rw [hnone w₂ fun h2 => h12 ⟨h1, h2⟩]
        cases natToWire n g w₁ <;> simp [Line.eval, interpretation_const]
      · dsimp only [rawGateToLine]; rw [hnone w₁ h1]; simp [Line.eval, interpretation_const]

/-- Full trace equivalence between `(appendRawGates p gs).eval` and `evalRawGates`. -/
theorem ofFn_eval_appendRawGates {n g : ℕ} (p : Program signature n g) (gs : List RawGate)
    (x : Fin n → Bool) :
    List.ofFn x ++ List.ofFn ((appendRawGates p gs).eval interpretation x) =
      evalRawGates (List.ofFn x ++ List.ofFn (p.eval interpretation x)) gs := by
  induction gs generalizing g p with
  | nil => rfl
  | cons rg rest ih =>
    have hcast : ∀ {a b : ℕ} (h : a = b) (q : Program signature n a),
        List.ofFn ((programCast h q).eval interpretation x) =
          List.ofFn (q.eval interpretation x) := by
      rintro a _ rfl q; rfl
    simp only [appendRawGates, hcast, ih, evalRawGates, List.foldl_cons]
    congr 1
    have hgate : List.ofFn ((p.gate (rawGateToLine n g rg)).eval interpretation x) =
        List.ofFn (p.eval interpretation x) ++
          [(rawGateToLine n g rg).eval interpretation x (p.eval interpretation x)] := by
      refine List.ext_getElem (by simp) fun k h₁ _ => ?_
      simp only [List.length_ofFn] at h₁; rw [List.getElem_ofFn]
      by_cases hkg : k < g
      · rw [List.getElem_append_left (by simp [hkg]), List.getElem_ofFn]
        simpa using Program.eval_gate_castSucc p (rawGateToLine n g rg) interpretation x ⟨k, hkg⟩
      · have hke : k = g := by omega
        have hlast : (⟨k, h₁⟩ : Fin (g + 1)) = Fin.last g := Fin.ext hke
        rw [hlast, List.getElem_append_right (by simp [hke])]
        simp only [List.length_ofFn, hke, Nat.sub_self, List.getElem_cons_zero]
        exact Program.eval_gate_last p (rawGateToLine n g rg) interpretation x
    rw [hgate, eval_rawGateToLine, List.append_assoc]

/-- Exact description of `(appendRawGates p gs).lines`: the first `g` lines copy `p.lines`, and
line `g + r` encodes `gs[r]`. -/
theorem lines_appendRawGates {n g : ℕ} (p : Program signature n g) (gs : List RawGate)
    (k : Fin (g + gs.length)) :
    (appendRawGates p gs).lines k =
      if hk : k.val < g then
        (p.lines ⟨k.val, hk⟩).mapWires (wireCastLE (Nat.le_add_right g gs.length))
      else
        (rawGateToLine n (g + (k.val - g)) (gs[k.val - g]'(by omega))).mapWires
          (wireCastLE (by omega)) := by
  have hmw_id : ∀ {a : ℕ} (l : Line signature n a) (h : a ≤ a), l.mapWires (wireCastLE h) = l := by
    intro a ⟨op, ws⟩ _; dsimp only [Line.mapWires]; congr 1; funext i
    dsimp only [Function.comp_apply]; cases ws i <;> rfl
  have hmw_comp : ∀ {a b c : ℕ} (l : Line signature n a) (h₁ : a ≤ b) (h₂ : b ≤ c),
      (l.mapWires (wireCastLE h₁)).mapWires (wireCastLE h₂) =
        l.mapWires (wireCastLE (h₁.trans h₂)) := by
    intro a b c ⟨op, ws⟩ _ _; dsimp only [Line.mapWires]; congr 1; funext i
    dsimp only [Function.comp_apply]; cases ws i <;> rfl
  have hcs_eq : ∀ {a : ℕ}, (Wire.Renaming.castSucc : Wire n a → Wire n (a + 1)) =
      wireCastLE (Nat.le_succ a) := fun {a} => by funext w; cases w <;> rfl
  have haux : ∀ {a b c : ℕ} (hab : a = b) (ha : a ≤ c) (hb : b ≤ c) (g0 : RawGate),
      (rawGateToLine n a g0).mapWires (wireCastLE ha) =
        (rawGateToLine n b g0).mapWires (wireCastLE hb) := by rintro a _ _ rfl _ _ _; rfl
  induction gs generalizing g p with
  | nil =>
    have hk : k.val < g := k.isLt
    simp only [appendRawGates, hk]; exact (hmw_id _ _).symm
  | cons rg rest ih =>
    have hcast_lines : ∀ {a b : ℕ} (h : a = b) (q : Program signature n a) (idx : Fin b),
        (programCast h q).lines idx = (q.lines (idx.cast h.symm)).mapWires (wireCastLE h.le) := by
      rintro a _ rfl _ _; exact (hmw_id _ _).symm
    have heq : g + 1 + rest.length = g + (rg :: rest).length := by simp; omega
    dsimp only [appendRawGates]; rw [hcast_lines heq, ih]
    by_cases hk1 : k.val < g + 1
    · have hk1' : (k.cast heq.symm).val < g + 1 := hk1
      rw [dite_eq_left hk1', hmw_comp]
      by_cases hk0 : k.val < g
      · rw [dite_eq_left hk0, show (⟨(k.cast heq.symm).val, hk1'⟩ : Fin (g + 1)) =
          (⟨k.val, hk0⟩ : Fin g).castSucc from rfl, Program.lines_gate_castSucc, hcs_eq, hmw_comp]
      · have hke : k.val = g := by omega
        rw [dite_eq_right hk0, show (⟨(k.cast heq.symm).val, hk1'⟩ : Fin (g + 1)) =
          Fin.last g from Fin.ext hke, Program.lines_gate_last, hcs_eq, hmw_comp]
        simp only [show k.val - g = 0 by omega, List.getElem_cons_zero]
        exact haux (by omega) _ _ rg
    · have hk1' : ¬((k.cast heq.symm).val < g + 1) := hk1
      rw [dite_eq_right hk1', dite_eq_right (by omega), hmw_comp]
      have hget : (rg :: rest)[k.val - g]'(by simp; omega) =
          rest[k.val - (g + 1)]'(by omega) := by
            simp [show k.val - g = k.val - (g + 1) + 1 by omega]
      simp only [Fin.val_cast, hget]; exact haux (by omega) _ _ _

/-- Compile a `List RawGate` and output raw indices `outs : List ℕ` into a Boolean circuit. -/
@[expose] def buildRawCircuit (n : ℕ) (hpos : 0 < n) (gs : List RawGate) (outs : List ℕ) :
    Circuit signature n outs.length where
  size := gs.length
  program := programCast (Nat.zero_add gs.length) (appendRawGates Program.empty gs)
  outputs j := (natToWire n gs.length outs[j.val]).getD (.input ⟨0, hpos⟩)

/-- Size of `buildRawCircuit`. -/
@[simp] theorem size_buildRawCircuit (n : ℕ) (hpos : 0 < n) (gs : List RawGate) (outs : List ℕ) :
    (buildRawCircuit n hpos gs outs).size = gs.length := rfl

/-- Evaluating `buildRawCircuit` indexes `evalRawGates (List.ofFn x) gs` at each output wire. -/
theorem eval_buildRawCircuit (n : ℕ) (hpos : 0 < n) (gs : List RawGate) (outs : List ℕ)
    (houts : ∀ j : Fin outs.length, outs[j.val] < n + gs.length) (x : BitString n)
    (j : Fin outs.length) :
    (buildRawCircuit n hpos gs outs).eval interpretation x j =
      (evalRawGates (List.ofFn x) gs).getD outs[j.val] false := by
  have htrace : List.ofFn x ++
      List.ofFn ((buildRawCircuit n hpos gs outs).program.eval interpretation x) =
      evalRawGates (List.ofFn x) gs := by
    have h0 := ofFn_eval_appendRawGates (n := n) (Program.empty : Program signature n 0) gs x
    have hcast : ∀ {a b : ℕ} (h : a = b) (q : Program signature n a),
        List.ofFn ((programCast h q).eval interpretation x) =
          List.ofFn (q.eval interpretation x) := by rintro a _ rfl q; rfl
    simpa [buildRawCircuit, hcast] using h0
  obtain ⟨w, hw, hwnat⟩ := isSome_natToWire_of_lt (houts j)
  have hout_eq : (buildRawCircuit n hpos gs outs).outputs j = w := by
    simp only [buildRawCircuit, hw, Option.getD_some]
  dsimp only [Circuit.eval, Program.trace, Function.comp_apply]
  rw [hout_eq, ← hwnat, ← htrace]
  cases w with
  | input i =>
    rw [wireToNat, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
    simp [Wire.elim]
  | gate k =>
    rw [wireToNat, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp [Wire.elim]

/-- Lines of `buildRawCircuit`. -/
theorem lines_buildRawCircuit (n : ℕ) (hpos : 0 < n) (gs : List RawGate) (outs : List ℕ)
    (k : Fin gs.length) :
    (buildRawCircuit n hpos gs outs).program.lines k =
      (rawGateToLine n k.val gs[k.val]).mapWires (wireCastLE k.isLt.le) := by
  have hcast_lines : ∀ {a b : ℕ} (h : a = b) (q : Program signature n a) (idx : Fin b),
      (programCast h q).lines idx =
        (q.lines (idx.cast h.symm)).mapWires (wireCastLE h.le) := by
    rintro a _ rfl q idx; change q.lines idx = (q.lines idx).mapWires _
    rcases q.lines idx with ⟨_, ws⟩; dsimp only [Line.mapWires]; congr 1; funext i
    dsimp only [Function.comp_apply]; cases ws i <;> rfl
  have haux : ∀ {a b c d : ℕ} (hab : a = b) (h₁ : a ≤ c) (h₂ : c ≤ d) (h₃ : b ≤ d) (rg : RawGate),
      ((rawGateToLine n a rg).mapWires (wireCastLE h₁)).mapWires (wireCastLE h₂) =
        (rawGateToLine n b rg).mapWires (wireCastLE h₃) := by
    rintro a _ c d rfl h₁ h₂ _ rg; rcases rawGateToLine n a rg with ⟨_, ws⟩
    dsimp only [Line.mapWires]; congr 1; funext i
    dsimp only [Function.comp_apply]; cases ws i <;> rfl
  dsimp only [buildRawCircuit]
  rw [hcast_lines (Nat.zero_add gs.length), lines_appendRawGates]
  simp only [Fin.val_cast, Nat.not_lt_zero, dite_false, Nat.sub_zero]
  exact haux (Nat.zero_add k.val) _ _ _ _

/-- Binary encoding of `RawGate`. -/
def encRawGate : RawGate ↪ List Bool :=
  let encR := encSum (encSum encBool encUnary)
    (encSum (encPair encUnary encUnary) (encPair encUnary encUnary))
  { toFun := fun
      | .const b => encR (.inl (.inl b)) | .not w => encR (.inl (.inr w))
      | .and w₁ w₂ => encR (.inr (.inl (w₁, w₂))) | .or w₁ w₂ => encR (.inr (.inr (w₁, w₂)))
    inj' := fun g₁ g₂ h => by
      cases g₁ <;> cases g₂ <;>
        (have hinj := encR.injective h
         simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at hinj)
      · exact congrArg RawGate.const hinj
      · exact congrArg RawGate.not hinj
      · exact congrArg₂ RawGate.and hinj.1 hinj.2
      · exact congrArg₂ RawGate.or hinj.1 hinj.2 }

/-- Constant `RawGate` constructor is computable in polynomial time. -/
theorem computableInPolyTime_rawGate_const :
    ComputableInPolyTime RawGate.const encBool encRawGate :=
  ((sumInl (encSum encBool encUnary) (encSum (encPair encUnary encUnary)
    (encPair encUnary encUnary))).comp (sumInl encBool encUnary)).of_enc_eq fun _ => rfl

/-- Negation `RawGate` constructor is computable in polynomial time (unary wire index). -/
theorem computableInPolyTime_rawGate_not : ComputableInPolyTime RawGate.not encUnary encRawGate :=
  ((sumInl (encSum encBool encUnary) (encSum (encPair encUnary encUnary)
    (encPair encUnary encUnary))).comp (sumInr encBool encUnary)).of_enc_eq fun _ => rfl

/-- Conjunction `RawGate` constructor is computable in polynomial time (unary wire indices). -/
theorem computableInPolyTime_rawGate_and :
    ComputableInPolyTime (fun p : ℕ × ℕ => RawGate.and p.1 p.2)
      (encPair encUnary encUnary) encRawGate :=
  ((sumInr (encSum encBool encUnary) _).comp
    (sumInl (encPair encUnary encUnary) (encPair encUnary encUnary))).of_enc_eq fun _ => rfl

/-- Disjunction `RawGate` constructor is computable in polynomial time (unary wire indices). -/
theorem computableInPolyTime_rawGate_or :
    ComputableInPolyTime (fun p : ℕ × ℕ => RawGate.or p.1 p.2)
      (encPair encUnary encUnary) encRawGate :=
  ((sumInr (encSum encBool encUnary) _).comp
    (sumInr (encPair encUnary encUnary) (encPair encUnary encUnary))).of_enc_eq fun _ => rfl

private abbrev RawGateSum := (Bool ⊕ ℕ) ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℕ))
private def rawGateToSum : RawGate → RawGateSum
  | .const b => .inl (.inl b) | .not w => .inl (.inr w)
  | .and w₁ w₂ => .inr (.inl (w₁, w₂)) | .or w₁ w₂ => .inr (.inr (w₁, w₂))

private theorem computableInPolyTime_rawGateToSum :
    ComputableInPolyTime rawGateToSum encRawGate (encSum (encSum encBool encUnary)
      (encSum (encPair encUnary encUnary) (encPair encUnary encUnary))) :=
  ComputableInPolyTime.of_eq fun g => by cases g <;> rfl

/-- `evalRawGates` is computable in polynomial time. -/
theorem computableInPolyTime_evalRawGates :
    ComputableInPolyTime (fun p : List Bool × List RawGate => evalRawGates p.1 p.2)
      (encPair encBits (encList encRawGate)) encBits := by
  let EUU := encPair encUnary encUnary
  let E := encPair encBits encRawGate
  have hstep1 : ComputableInPolyTime (fun p : List Bool × RawGate => evalRawGate p.1 p.2)
      E encBool := by
    let E01 := encPair E (encSum encBool encUnary); let E23 := encPair E (encSum EUU EUU)
    have hV : ComputableInPolyTime Prod.fst E encBits := fst _ _
    have hnot : ComputableInPolyTime
        (fun r : ((List Bool × RawGate) × (Bool ⊕ ℕ)) × ℕ =>
          if r.2 < r.1.1.1.length then !r.1.1.1.getD r.2 false else false)
        (encPair E01 encUnary) encBool := by
      have hv := hV.comp ((fst E (encSum encBool encUnary)).comp (fst E01 encUnary))
      have hw := snd E01 encUnary
      exact ite_decide (unary_lt.comp (hw.prod (length_bits.comp hv)))
        (bool_not.comp (bitsGetDWithInput hv hw false)) (const false)
    have hbin (op : Bool → Bool → Bool)
        (hop : ComputableInPolyTime (fun q : Bool × Bool => op q.1 q.2)
          (encPair encBool encBool) encBool) :
        ComputableInPolyTime (fun r : ((List Bool × RawGate) × (ℕ × ℕ ⊕ ℕ × ℕ)) × (ℕ × ℕ) =>
          if decide (r.2.1 < r.1.1.1.length) && decide (r.2.2 < r.1.1.1.length) then
            op (r.1.1.1.getD r.2.1 false) (r.1.1.1.getD r.2.2 false) else false)
          (encPair E23 EUU) encBool := by
      have hv := hV.comp ((fst E (encSum EUU EUU)).comp (fst E23 EUU))
      have hw1 := (fst encUnary encUnary).comp (snd E23 EUU)
      have hw2 := (snd encUnary encUnary).comp (snd E23 EUU)
      have hl := length_bits.comp hv
      exact (ite_decide (decide_eq'
          (bool_and' (unary_lt.comp (hw1.prod hl)) (unary_lt.comp (hw2.prod hl))) (const true))
        (hop.comp ((bitsGetDWithInput hv hw1 false).prod (bitsGetDWithInput hv hw2 false)))
        (const false)).of_enc_eq fun _ => by congr 1
    have hL := sumElimWithInput (eg := E01) (ea := encBool) (eb := encUnary)
      (left := fun _ b => b)
      (right := fun q w => if w < q.1.1.length then !q.1.1.getD w false else false)
      (snd E (encSum encBool encUnary)) (snd E01 encBool) hnot
    have hR := sumElimWithInput (eg := E23) (ea := EUU) (eb := EUU)
      (left := fun q p => if decide (p.1 < q.1.1.length) && decide (p.2 < q.1.1.length) then
        q.1.1.getD p.1 false && q.1.1.getD p.2 false else false)
      (right := fun q p => if decide (p.1 < q.1.1.length) && decide (p.2 < q.1.1.length) then
        q.1.1.getD p.1 false || q.1.1.getD p.2 false else false)
      (snd E (encSum EUU EUU)) (hbin (· && ·) bool_and) (hbin (· || ·) bool_or)
    exact (sumElimWithInput (eg := E) (ea := encSum encBool encUnary) (eb := encSum EUU EUU)
      (left := fun p => Sum.elim id fun w => if w < p.1.length then !p.1.getD w false else false)
      (right := fun p => Sum.elim
        (fun w => if decide (w.1 < p.1.length) && decide (w.2 < p.1.length) then
          p.1.getD w.1 false && p.1.getD w.2 false else false)
        (fun w => if decide (w.1 < p.1.length) && decide (w.2 < p.1.length) then
          p.1.getD w.1 false || p.1.getD w.2 false else false))
      (computableInPolyTime_rawGateToSum.comp (snd encBits encRawGate))
      (hL.of_enc_eq fun q => by cases q.2 <;> rfl)
      (hR.of_enc_eq fun q => by cases q.2 <;> rfl)).of_enc_eq fun ⟨_, g⟩ => by cases g <;> rfl
  let EP := encPair encBits (encList encRawGate)
  let EF := encPair (encPair EP encBits) encRawGate
  have hacc : ComputableInPolyTime (fun q => q.1.2) EF encBits :=
    (snd EP encBits).comp (fst (encPair EP encBits) encRawGate)
  have hbit := hstep1.comp (hacc.prod (snd (encPair EP encBits) encRawGate))
  exact foldlWithInput_of_bounded_growth (encIn := EP) (encA := encRawGate)
    (encL := encList encRawGate) (encB := encBits) (list := Prod.snd) (init := Prod.fst)
    (step := fun _ acc rg => acc ++ [evalRawGate acc rg]) (fst _ _)
    ⟨snd _ _, bitsAppend hacc (hbit.of_enc_eq fun _ => rfl), inferInstance, inferInstance⟩
    (growth := fun _ => 1) ⟨.const 1, fun _ _ _ _ => by simp⟩

/-- First-order builder for `tauFormulaWith` on a compiled `RawGate` circuit. -/
def buildTauFormulaRaw (atoms : List ℕ) (n : ℕ) (gs : List RawGate) (outs : List ℕ)
    (bs : List Bool) : Formula :=
  let gateForm (k : ℕ) (rg : RawGate) : Formula :=
    let spec : Formula := match rg with
      | .const false => .falsum | .const true => .imp .falsum .falsum
      | .not w => if w < n + k then .imp (.atom (atoms.getD w 0)) .falsum else .falsum
      | .and w₁ w₂ => if w₁ < n + k && w₂ < n + k then
          .and (.atom (atoms.getD w₁ 0)) (.atom (atoms.getD w₂ 0)) else .falsum
      | .or w₁ w₂ => if w₁ < n + k && w₂ < n + k then
          .or (.atom (atoms.getD w₁ 0)) (.atom (atoms.getD w₂ 0)) else .falsum
    formulaIff (.atom (atoms.getD (n + k) 0)) spec
  let gdefs := (List.range gs.length).map fun k => gateForm k (gs.getD k (.const false))
  let olits := (List.range outs.length).map fun j =>
    let idx := outs.getD j 0
    litNe (atoms.getD (if idx < n + gs.length then idx else 0) 0) (bs.getD j false)
  Frege.Formula.imps gdefs (bigOr olits)

/-- `buildTauFormulaRaw` produces the exact `tauFormulaWith` of `buildRawCircuit`. -/
theorem buildTauFormulaRaw_eq (n : ℕ) (hpos : 0 < n) (gs : List RawGate) (outs : List ℕ)
    (wAtom : Wire n gs.length → ℕ) (b : BitString outs.length) :
    let atoms := (List.ofFn fun i : Fin n => wAtom (.input i)) ++
      (List.ofFn fun k : Fin gs.length => wAtom (.gate k))
    buildTauFormulaRaw atoms n gs outs (List.ofFn b) =
      tauFormulaWith (buildRawCircuit n hpos gs outs) wAtom b := by
  intro atoms
  have hatom (idx : ℕ) (h : idx < n + gs.length) (w : Wire n gs.length)
      (hw : natToWire n gs.length idx = some w) : atoms.getD idx 0 = wAtom w := by
    by_cases h1 : idx < n
    · simp only [natToWire, h1, dite_true, Option.some.injEq] at hw; subst hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [atoms]; omega),
        Option.getD_some, List.getElem_append_left (by simp [h1]), List.getElem_ofFn]
    · have h2 : idx - n < gs.length := by omega
      simp only [natToWire, h1, h2, dite_false, dite_true, Option.some.injEq] at hw; subst hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [atoms]; omega),
        Option.getD_some, List.getElem_append_right (by simp; omega)]; simp
  have hatom_k (k : Fin gs.length) (idx : ℕ) (h : idx < n + k.val) (w : Wire n k.val)
      (hw : natToWire n k.val idx = some w) :
      atoms.getD idx 0 = wAtom (wireCastLE k.isLt.le w) := by
    refine hatom idx (by omega) (wireCastLE k.isLt.le w) ?_
    by_cases h1 : idx < n
    · simp only [natToWire, h1, dite_true, Option.some.injEq] at hw; subst hw
      simp [wireCastLE, natToWire, h1]
    · have h2 : idx - n < k.val := by omega
      simp only [natToWire, h1, h2, dite_false, dite_true, Option.some.injEq] at hw; subst hw
      simp [wireCastLE, natToWire, h1, show idx - n < gs.length by omega]
  have hnone_k (k : Fin gs.length) (idx : ℕ) (h : ¬(idx < n + k.val)) :
      natToWire n k.val idx = none := by
    simp only [natToWire]; split_ifs <;> first | omega | rfl
  dsimp only [buildTauFormulaRaw, tauFormulaWith]
  congr 1
  · refine List.ext_getElem (by simp [gateDefsWith]) fun k h₁ _ => ?_
    simp only [List.length_map, List.length_range] at h₁
    let kf : Fin gs.length := ⟨k, h₁⟩
    simp only [List.getElem_map, List.getElem_range, gateDefsWith, List.getElem_ofFn]
    have hgk : gs.getD k (.const false) = gs[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]
    have hnk : atoms.getD (n + k) 0 = wAtom (.gate kf) :=
      hatom (n + k) (by omega) (.gate kf) (by simp [natToWire, show ¬(n + k < n) by omega, h₁, kf])
    change formulaIff (.atom (atoms.getD (n + k) 0)) _ =
      formulaIff (.atom (wAtom (.gate kf)))
        (lineSpecFormula wAtom ((buildRawCircuit n hpos gs outs).program.lines kf))
    rw [hgk, hnk, lines_buildRawCircuit n hpos gs outs kf]; congr 1
    change _ = lineSpecFormula wAtom ((rawGateToLine n k gs[k]).mapWires (wireCastLE kf.isLt.le))
    cases hrg : gs[k] with
    | const bv => cases bv <;> rfl
    | not w =>
      by_cases hw : w < n + k
      · obtain ⟨u, hu, -⟩ := isSome_natToWire_of_lt (g := k) hw
        dsimp only [rawGateToLine]; rw [hu]; simp only [hw, ↓reduceIte, hatom_k kf w hw u hu]; rfl
      · dsimp only [rawGateToLine]; rw [hnone_k kf w hw]; simp [hw, Line.mapWires, lineSpecFormula]
    | and w₁ w₂ =>
      by_cases h12 : w₁ < n + k ∧ w₂ < n + k
      · obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt (g := k) h12.1
        obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt (g := k) h12.2
        rw [rawGateToLine_and_of_eq hu₁ hu₂]
        simp only [Bool.and_eq_true, decide_eq_true_eq, h12.1, h12.2, and_self,
          ↓reduceIte, hatom_k kf w₁ h12.1 u₁ hu₁, hatom_k kf w₂ h12.2 u₂ hu₂]; rfl
      · by_cases h1 : w₁ < n + k
        · have h2 : ¬w₂ < n + k := fun h2 => h12 ⟨h1, h2⟩
          dsimp only [rawGateToLine]; rw [hnone_k kf w₂ h2]
          cases natToWire n k w₁ <;> simp [h2, Line.mapWires, lineSpecFormula]
        · dsimp only [rawGateToLine]; rw [hnone_k kf w₁ h1]
          simp [h1, Line.mapWires, lineSpecFormula]
    | or w₁ w₂ =>
      by_cases h12 : w₁ < n + k ∧ w₂ < n + k
      · obtain ⟨u₁, hu₁, -⟩ := isSome_natToWire_of_lt (g := k) h12.1
        obtain ⟨u₂, hu₂, -⟩ := isSome_natToWire_of_lt (g := k) h12.2
        rw [rawGateToLine_or_of_eq hu₁ hu₂]
        simp only [Bool.and_eq_true, decide_eq_true_eq, h12.1, h12.2, and_self,
          ↓reduceIte, hatom_k kf w₁ h12.1 u₁ hu₁, hatom_k kf w₂ h12.2 u₂ hu₂]; rfl
      · by_cases h1 : w₁ < n + k
        · have h2 : ¬w₂ < n + k := fun h2 => h12 ⟨h1, h2⟩
          dsimp only [rawGateToLine]; rw [hnone_k kf w₂ h2]
          cases natToWire n k w₁ <;> simp [h2, Line.mapWires, lineSpecFormula]
        · dsimp only [rawGateToLine]; rw [hnone_k kf w₁ h1]
          simp [h1, Line.mapWires, lineSpecFormula]
  · simp only [outMismatchWith]; congr 1
    refine List.ext_getElem (by simp) fun j h₁ _ => ?_
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, buildRawCircuit]
    have hoj : outs.getD j 0 = outs[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]
    have hbj : (List.ofFn b).getD j false = b ⟨j, h₁⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [h₁]),
        Option.getD_some, List.getElem_ofFn]
    rw [hoj, hbj]; congr 1
    by_cases hlt : outs[j] < n + gs.length
    · obtain ⟨u, hu, -⟩ := isSome_natToWire_of_lt hlt
      simp only [hlt, ↓reduceIte, hu, Option.getD_some, hatom outs[j] hlt u hu]
    · have hn : natToWire n gs.length outs[j] = none := by
        simp only [natToWire]; split_ifs <;> first | omega | rfl
      simp only [hlt, ↓reduceIte, hn, Option.getD_none]
      exact hatom 0 (by omega) (.input ⟨0, hpos⟩) (by simp [natToWire, hpos])

/-- Helper: building the gate specification formula in `buildTauFormulaRaw` is computable in
polynomial time. -/
private theorem computableInPolyTime_rawGateSpec :
    ComputableInPolyTime
      (fun p : (List ℕ × ℕ) × RawGate => match p.2 with
        | .const false => (Proposition.falsum : Formula) | .const true => .imp .falsum .falsum
        | .not w => if w < p.1.2 then .imp (.atom (p.1.1.getD w 0)) .falsum else .falsum
        | .and w₁ w₂ => if w₁ < p.1.2 && w₂ < p.1.2 then
            .and (.atom (p.1.1.getD w₁ 0)) (.atom (p.1.1.getD w₂ 0)) else .falsum
        | .or w₁ w₂ => if w₁ < p.1.2 && w₂ < p.1.2 then
            .or (.atom (p.1.1.getD w₁ 0)) (.atom (p.1.1.getD w₂ 0)) else .falsum)
      (encPair (encPair (encList encNat) encUnary) encRawGate) encFormula := by
  let EC := encPair (encList encNat) encUnary; let E := encPair EC encRawGate
  let EUU := encPair encUnary encUnary
  let E01 := encPair E (encSum encBool encUnary); let E23 := encPair E (encSum EUU EUU)
  have hconst := ite_decide (encB := encFormula) (decide_eq' (snd E01 encBool) (const true))
    (const (Proposition.imp .falsum .falsum : Formula)) (const (Proposition.falsum : Formula))
  have hnot : ComputableInPolyTime (fun r : (((List ℕ × ℕ) × RawGate) × (Bool ⊕ ℕ)) × ℕ =>
      if r.2 < r.1.1.1.2 then .imp (.atom (r.1.1.1.1.getD r.2 0)) .falsum
      else (Proposition.falsum : Formula)) (encPair E01 encUnary) encFormula := by
    have hc := (fst EC encRawGate).comp ((fst E (encSum encBool encUnary)).comp (fst E01 encUnary))
    have hat := (fst (encList encNat) encUnary).comp hc
    have hbd := (snd (encList encNat) encUnary).comp hc; have hw := snd E01 encUnary
    exact ite_decide (unary_lt.comp (hw.prod hbd)) (computableInPolyTime_imp.comp
      ((computableInPolyTime_atom.comp (listGetDWithInput hat hw 0)).prod
        (const (Proposition.falsum : Formula)))) (const (Proposition.falsum : Formula))
  have hbin (op : Formula → Formula → Formula)
      (hop : ComputableInPolyTime (fun q : Formula × Formula => op q.1 q.2)
        (encPair encFormula encFormula) encFormula) :
      ComputableInPolyTime (fun r : (((List ℕ × ℕ) × RawGate) × (ℕ × ℕ ⊕ ℕ × ℕ)) × (ℕ × ℕ) =>
        if decide (r.2.1 < r.1.1.1.2) && decide (r.2.2 < r.1.1.1.2) then
          op (.atom (r.1.1.1.1.getD r.2.1 0)) (.atom (r.1.1.1.1.getD r.2.2 0))
        else (Proposition.falsum : Formula)) (encPair E23 EUU) encFormula := by
    have hc := (fst EC encRawGate).comp ((fst E (encSum EUU EUU)).comp (fst E23 EUU))
    have hat := (fst (encList encNat) encUnary).comp hc
    have hbd := (snd (encList encNat) encUnary).comp hc
    have hw1 := (fst encUnary encUnary).comp (snd E23 EUU)
    have hw2 := (snd encUnary encUnary).comp (snd E23 EUU)
    exact (ite_decide (decide_eq'
        (bool_and' (unary_lt.comp (hw1.prod hbd)) (unary_lt.comp (hw2.prod hbd))) (const true))
      (hop.comp ((computableInPolyTime_atom.comp (listGetDWithInput hat hw1 0)).prod
        (computableInPolyTime_atom.comp (listGetDWithInput hat hw2 0))))
      (const .falsum)).of_enc_eq fun _ => by congr 1
  have hL := sumElimWithInput (eg := E01) (ea := encBool) (eb := encUnary)
    (left := fun _ b => if b then (Proposition.imp .falsum .falsum : Formula) else .falsum)
    (right := fun q w => if w < q.1.1.2 then .imp (.atom (q.1.1.1.getD w 0)) .falsum else .falsum)
    (snd E (encSum encBool encUnary)) (hconst.of_enc_eq fun r => by cases r.2 <;> rfl) hnot
  have hR := sumElimWithInput (eg := E23) (ea := EUU) (eb := EUU)
    (left := fun q w => if decide (w.1 < q.1.1.2) && decide (w.2 < q.1.1.2) then
      Proposition.and (.atom (q.1.1.1.getD w.1 0)) (.atom (q.1.1.1.getD w.2 0)) else .falsum)
    (right := fun q w => if decide (w.1 < q.1.1.2) && decide (w.2 < q.1.1.2) then
      Proposition.or (.atom (q.1.1.1.getD w.1 0)) (.atom (q.1.1.1.getD w.2 0)) else .falsum)
    (snd E (encSum EUU EUU)) (hbin Proposition.and computableInPolyTime_and)
    (hbin Proposition.or computableInPolyTime_or)
  exact (sumElimWithInput (eg := E) (ea := encSum encBool encUnary) (eb := encSum EUU EUU)
    (left := fun p => Sum.elim
      (fun b => if b then (Proposition.imp .falsum .falsum : Formula) else .falsum)
      (fun w => if w < p.1.2 then .imp (.atom (p.1.1.getD w 0)) .falsum else .falsum))
    (right := fun p => Sum.elim
      (fun w => if decide (w.1 < p.1.2) && decide (w.2 < p.1.2) then
        Proposition.and (.atom (p.1.1.getD w.1 0)) (.atom (p.1.1.getD w.2 0)) else .falsum)
      (fun w => if decide (w.1 < p.1.2) && decide (w.2 < p.1.2) then
        Proposition.or (.atom (p.1.1.getD w.1 0)) (.atom (p.1.1.getD w.2 0)) else .falsum))
    (computableInPolyTime_rawGateToSum.comp (snd EC encRawGate))
    (hL.of_enc_eq fun q => by cases q.2 <;> rfl)
    (hR.of_enc_eq fun q => by cases q.2 <;> rfl)).of_enc_eq fun ⟨_, g⟩ => by
      cases g with | const b => cases b <;> rfl | _ => rfl

/-- `buildTauFormulaRaw` is computable in uniform polynomial time. -/
theorem computableInPolyTime_tauFormulaRaw :
    ComputableInPolyTime
      (fun p : List ℕ × (ℕ × (List RawGate × (List ℕ × List Bool))) =>
        buildTauFormulaRaw p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair (encList encNat)
        (encPair encUnary (encPair (encList encRawGate) (encPair (encList encUnary) encBits))))
      encFormula := by
  let E4 := encPair (encList encUnary) encBits
  let E3 := encPair (encList encRawGate) E4
  let E2 := encPair encUnary E3
  let E := encPair (encList encNat) E2
  have hatoms := fst (encList encNat) E2; have hp2 := snd (encList encNat) E2
  have hn := (fst encUnary E3).comp hp2; have hp3 := (snd encUnary E3).comp hp2
  have hgs := (fst (encList encRawGate) E4).comp hp3
  have hp4 := (snd (encList encRawGate) E4).comp hp3
  have houts := (fst (encList encUnary) encBits).comp hp4
  have hbs := (snd (encList encUnary) encBits).comp hp4
  have hiff : ComputableInPolyTime (fun q : Formula × Formula => formulaIff q.1 q.2)
      (encPair encFormula encFormula) encFormula :=
    computableInPolyTime_and.comp ((computableInPolyTime_imp.comp id').prod
      (computableInPolyTime_imp.comp ((snd _ _).prod (fst _ _))))
  have hgdefs : ComputableInPolyTime
      (fun p : List ℕ × (ℕ × (List RawGate × (List ℕ × List Bool))) =>
        (List.range p.2.2.1.length).map fun k =>
          let rg := p.2.2.1.getD k (.const false)
          formulaIff (.atom (p.1.getD (p.2.1 + k) 0))
            (match rg with
             | .const false => .falsum | .const true => .imp .falsum .falsum
             | .not w => if w < p.2.1 + k then .imp (.atom (p.1.getD w 0)) .falsum else .falsum
             | .and w₁ w₂ => if w₁ < p.2.1 + k && w₂ < p.2.1 + k then
                 .and (.atom (p.1.getD w₁ 0)) (.atom (p.1.getD w₂ 0)) else .falsum
             | .or w₁ w₂ => if w₁ < p.2.1 + k && w₂ < p.2.1 + k then
                 .or (.atom (p.1.getD w₁ 0)) (.atom (p.1.getD w₂ 0)) else .falsum))
      E (encList encFormula) := by
    refine mapWithInput (range.comp ((length encRawGate).comp hgs)) ?_
    let EK := encPair E encUnary; have hp := fst E encUnary; have hk := snd E encUnary
    have hnk := unary_add' (hn.comp hp) hk
    have hrg := listGetDWithInput (hgs.comp hp) hk (.const false)
    have hlhs := computableInPolyTime_atom.comp (listGetDWithInput (hatoms.comp hp) hnk 0)
    exact hiff.comp (hlhs.prod
      (computableInPolyTime_rawGateSpec.comp (((hatoms.comp hp).prod hnk).prod hrg)))
  have holits : ComputableInPolyTime
      (fun p : List ℕ × (ℕ × (List RawGate × (List ℕ × List Bool))) =>
        (List.range p.2.2.2.1.length).map fun j =>
          let idx := p.2.2.2.1.getD j 0
          let wIdx := if idx < p.2.1 + p.2.2.1.length then idx else 0
          litNe (p.1.getD wIdx 0) (p.2.2.2.2.getD j false))
      E (encList encFormula) := by
    refine mapWithInput (range.comp ((length encUnary).comp houts)) ?_
    let EJ := encPair E encUnary; have hp := fst E encUnary; have hj := snd E encUnary
    have hidx := listGetDWithInput (houts.comp hp) hj 0
    have htot := unary_add' (hn.comp hp) ((length encRawGate).comp (hgs.comp hp))
    have hwIdx := ite_decide (unary_lt.comp (hidx.prod htot)) hidx (const 0)
    have hat := computableInPolyTime_atom.comp (listGetDWithInput (hatoms.comp hp) hwIdx 0)
    have hbj := bitsGetDWithInput (hbs.comp hp) hj false
    have hbot : ComputableInPolyTime (fun _ => (Proposition.falsum : Formula)) EJ encFormula :=
      const (Proposition.falsum : Formula)
    have hbrT := computableInPolyTime_or.comp
      ((computableInPolyTime_imp.comp (hat.prod hbot)).prod
        (const (Proposition.and .falsum .falsum : Formula)))
    have hbrF := computableInPolyTime_and.comp
      ((computableInPolyTime_or.comp (hat.prod hbot)).prod
        (const (Proposition.imp .falsum .falsum : Formula)))
    exact (ite_decide hbj hbrT hbrF).of_enc_eq fun _ => by
      dsimp only [litNe, Function.comp_apply]
  exact computableInPolyTime_imps.comp (hgdefs.prod (computableInPolyTime_bigOr.comp holits))

end CslibFrontier.ProofComplexity
