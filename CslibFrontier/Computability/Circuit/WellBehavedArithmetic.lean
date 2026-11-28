/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Computability.Circuit.Basic
public import CslibFrontier.Computability.Circuit.Depth
public import CslibFrontier.Computability.Circuit.Encoding.Basic
public import CslibFrontier.Computability.Circuit.Encoding.EvaluationTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Basic.Real.Basic

import CslibFrontier.Computability.Circuit.Encoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Well-Behaved Linear Arithmetic Circuits and Polynomial-Time Rational Evaluation

This module formalizes linear/comparison arithmetic circuits over `{+, -, ×, max, min, >}` with
scalar constants and proves that circuits of logarithmic multiplication depth can be evaluated in
deterministic polynomial time on multi-tape Turing machines
(`Turing.MultiTapeTM.ComputableInPolyTime`)
under standard Lean axioms.

## Main definitions

* `CslibFrontier.WellBehavedArithmetic.LinearArithBinOp`: binary gate tags
  `add | sub | mul | max | min | gt`.
* `CslibFrontier.WellBehavedArithmetic.LinearArithOp`: gate operations (binary operations and
  scalar constants).
* `CslibFrontier.WellBehavedArithmetic.linearArithSignature`: circuit signature for
  linear/comparison arithmetic circuits.
* `CslibFrontier.WellBehavedArithmetic.linearArithInterpretation`,
  `CslibFrontier.WellBehavedArithmetic.ratInterpretation`,
  `CslibFrontier.WellBehavedArithmetic.realInterpretation`: semantics over ordered rings, `ℚ`,
  and `ℝ`.
* `CslibFrontier.WellBehavedArithmetic.mulDepth`,
  `CslibFrontier.WellBehavedArithmetic.IsWellBehaved`:
  multiplication depth and logarithmic multiplication-depth predicate.
* `CslibFrontier.WellBehavedArithmetic.evalWellBehavedCode`,
  `CslibFrontier.WellBehavedArithmetic.evalWellBehavedOutputs`: bounded-multiplication-depth
  runtime evaluators.

## Main results

* `CslibFrontier.WellBehavedArithmetic.eval_realInterpretation_ratCast`: exact compatibility
  between `ℚ` and `ℝ` circuit evaluation on rational inputs.
* `CslibFrontier.WellBehavedArithmetic.evalWellBehavedOutputs_eq_of_isWellBehaved`: exactness of the
  runtime evaluator on all `c₀`-well-behaved circuits.
* `CslibFrontier.WellBehavedArithmetic.computableInPolyTime_evalWellBehavedCode`,
  `CslibFrontier.WellBehavedArithmetic.computableInPolyTime_evalWellBehavedOutputs`,
  `CslibFrontier.WellBehavedArithmetic.computableInPolyTime_evalWellBehavedCircuit`:
  polynomial-time multi-tape Turing machine certificates.
-/

public section

namespace CslibFrontier.WellBehavedArithmetic

open Cslib.Circuits Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Binary gate tags of a linear/comparison arithmetic circuit: `{+, -, ×, max, min, >}`. -/
inductive LinearArithBinOp : Type
  | add
  | sub
  | mul
  | max
  | min
  | gt
  deriving DecidableEq, Repr

/-- Explicit constructive enumeration of `LinearArithBinOp`. -/
instance instFinEnumLinearArithBinOp : FinEnum LinearArithBinOp :=
  FinEnum.ofList [.add, .sub, .mul, .max, .min, .gt] fun op ↦ by cases op <;> decide

/-- Binary encoding of `LinearArithBinOp` by unary finite rank. -/
def encLinearArithBinOp : LinearArithBinOp ↪ List Bool :=
  encFinEnum LinearArithBinOp

universe u

/-- Gate operations of a linear/comparison arithmetic circuit over scalar constants `F`. -/
inductive LinearArithOp (F : Type u) : Type u
  | bin (op : LinearArithBinOp)
  | const (c : F)
  deriving DecidableEq, Repr

namespace LinearArithOp

/-- Equivalence between `LinearArithOp F` and `LinearArithBinOp ⊕ F`. -/
def equivSum {F : Type*} : LinearArithOp F ≃ LinearArithBinOp ⊕ F where
  toFun
    | .bin op => .inl op
    | .const c => .inr c
  invFun
    | .inl op => .bin op
    | .inr c => .const c
  left_inv op := by cases op <;> rfl
  right_inv s := by cases s <;> rfl

/-- Binary encoding of `LinearArithOp F` given a scalar encoding `eF`. -/
def encoding {F : Type} (eF : F ↪ List Bool) : LinearArithOp F ↪ List Bool :=
  equivSum.toEmbedding.trans (encSum encLinearArithBinOp eF)

/-- Multiplication cost of an operation: `1` for multiplication and `0` otherwise. -/
def mulCost {F : Type*} : LinearArithOp F → ℕ
  | .bin .mul => 1
  | _ => 0

@[simp]
theorem mulCost_mul {F : Type*} : mulCost (.bin .mul : LinearArithOp F) = 1 := by
  rfl

@[simp]
theorem mulCost_const {F : Type*} (c : F) : mulCost (.const c) = 0 := by
  rfl

/-- Every gate has multiplication cost at most `1`. -/
theorem mulCost_le_one {F : Type*} (op : LinearArithOp F) : mulCost op ≤ 1 := by
  cases op with
  | const _ => exact Nat.zero_le 1
  | bin bop => cases bop <;> simp [mulCost]

/-- Arity of a linear/comparison arithmetic gate: `2` for binary gates and `0` for constants. -/
abbrev arity {F : Type u} : LinearArithOp F → ℕ
  | .bin _ => 2
  | .const _ => 0

end LinearArithOp

/-- Signature of linear/comparison arithmetic circuits over scalar type `F`. -/
abbrev linearArithSignature (F : Type u) : Signature.{u} where
  Op := LinearArithOp F
  Arity := LinearArithOp.arity

/-- Evaluate a binary operation `op : LinearArithBinOp` in an ordered ring `R`. -/
noncomputable def evalBinOp {R : Type*} [Ring R] [LinearOrder R] (op : LinearArithBinOp)
    (a b : R) : R :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .max => Max.max a b
  | .min => Min.min a b
  | .gt => @ite R (b < a) (Classical.propDecidable (b < a)) 1 0

@[simp]
theorem evalBinOp_add {R : Type*} [Ring R] [LinearOrder R] (a b : R) :
    evalBinOp .add a b = a + b := by
  rfl

@[simp]
theorem evalBinOp_sub {R : Type*} [Ring R] [LinearOrder R] (a b : R) :
    evalBinOp .sub a b = a - b := by
  rfl

@[simp]
theorem evalBinOp_mul {R : Type*} [Ring R] [LinearOrder R] (a b : R) :
    evalBinOp .mul a b = a * b := by
  rfl

/-- Semantics of `linearArithSignature F` in any ordered ring `R` via a scalar map `F → R`. -/
noncomputable def linearArithInterpretation {F R : Type*} [Ring R] [LinearOrder R]
    (constant : F → R) : Interpretation (linearArithSignature F) R
  | .bin op, args => evalBinOp op (args 0) (args 1)
  | .const c, _ => constant c

@[simp]
theorem linearArithInterpretation_bin {F R : Type*} [Ring R] [LinearOrder R]
    (constant : F → R) (op : LinearArithBinOp) (args : Fin 2 → R) :
    linearArithInterpretation constant (.bin op) args = evalBinOp op (args 0) (args 1) := by
  rfl

@[simp]
theorem linearArithInterpretation_const {F R : Type*} [Ring R] [LinearOrder R]
    (constant : F → R) (c : F) (args : Fin 0 → R) :
    linearArithInterpretation constant (.const c) args = constant c := by
  rfl

/-- Exact rational interpretation of `linearArithSignature ℚ`. -/
noncomputable def ratInterpretation : Interpretation (linearArithSignature ℚ) ℚ :=
  linearArithInterpretation id

@[simp]
theorem ratInterpretation_bin (op : LinearArithBinOp) (args : Fin 2 → ℚ) :
    ratInterpretation (.bin op) args = evalBinOp op (args 0) (args 1) := by
  rfl

@[simp]
theorem ratInterpretation_const (c : ℚ) (args : Fin 0 → ℚ) :
    ratInterpretation (.const c) args = c := by
  rfl

/-- Exact real interpretation of `linearArithSignature ℚ`. -/
noncomputable def realInterpretation : Interpretation (linearArithSignature ℚ) ℝ :=
  linearArithInterpretation Rat.cast

@[simp]
theorem realInterpretation_bin (op : LinearArithBinOp) (args : Fin 2 → ℝ) :
    realInterpretation (.bin op) args = evalBinOp op (args 0) (args 1) := by
  rfl

@[simp]
theorem realInterpretation_const (c : ℚ) (args : Fin 0 → ℝ) :
    realInterpretation (.const c) args = (c : ℝ) := by
  rfl

/-- Casting `ℚ → ℝ` commutes with every binary gate operation in `LinearArithBinOp`. -/
theorem ratCast_evalBinOp (op : LinearArithBinOp) (a b : ℚ) :
    ((evalBinOp op a b : ℚ) : ℝ) = evalBinOp op (a : ℝ) (b : ℝ) := by
  cases op with
  | add => exact Rat.cast_add a b
  | sub => exact Rat.cast_sub a b
  | mul => exact Rat.cast_mul a b
  | max => exact Rat.cast_max a b
  | min => exact Rat.cast_min a b
  | gt =>
    dsimp [evalBinOp]
    by_cases h : b < a
    · have hr : (b : ℝ) < (a : ℝ) := Rat.cast_lt.mpr h
      simp [h, hr]
    · have hr : ¬((b : ℝ) < (a : ℝ)) := mt Rat.cast_lt.mp h
      simp [h, hr]

/-- Evaluating a rational linear arithmetic circuit in `ℝ` on cast rational inputs produces the
exact cast of its `ℚ` evaluation. -/
theorem eval_realInterpretation_ratCast {n m : ℕ}
    (c : Circuit (linearArithSignature ℚ) n m) (x : Fin n → ℚ) (j : Fin m) :
    c.eval realInterpretation (fun i ↦ (x i : ℝ)) j =
      ((c.eval ratInterpretation x j : ℚ) : ℝ) := by
  change c.program.trace realInterpretation (fun i ↦ (x i : ℝ)) (c.outputs j) =
    ((c.program.trace ratInterpretation x (c.outputs j) : ℚ) : ℝ)
  refine c.program.wire_induction
    (P := fun w ↦ c.program.trace realInterpretation (fun i ↦ (x i : ℝ)) w =
      ((c.program.trace ratInterpretation x w : ℚ) : ℝ))
    (fun _ ↦ rfl) (fun k ih ↦ ?_) (c.outputs j)
  rw [c.program.trace_gate, c.program.trace_gate]
  generalize c.program.lines k = line at ih ⊢
  rcases line with ⟨bop | q, wires⟩
  · dsimp only at ih
    rw [realInterpretation_bin, ratInterpretation_bin, ratCast_evalBinOp, ih 0, ih 1]
  · simp [realInterpretation, ratInterpretation, linearArithInterpretation]

/-- Multiplication depth of a linear arithmetic circuit. -/
def mulDepth {F : Type*} {n m : ℕ} (c : Circuit (linearArithSignature F) n m) : ℕ :=
  c.depthWith LinearArithOp.mulCost

/-- A rational linear arithmetic circuit is `c₀`-well-behaved if its multiplication depth is at
most `c₀ * (Nat.log 2 (c.size + 1) + 1)`. -/
def IsWellBehaved (c₀ : ℕ) {n m : ℕ} (c : Circuit (linearArithSignature ℚ) n m) : Prop :=
  mulDepth c ≤ c₀ * (Nat.log 2 (c.size + 1) + 1)

/-- Binary encoding of rational linear arithmetic circuits with `m` outputs. -/
abbrev encLinearArithCircuit (m : ℕ) :
    (Σ n, Circuit (linearArithSignature ℚ) n m) ↪ List Bool :=
  Circuit.encCircuit (LinearArithOp.encoding encRat) m

/-- Multiplication-depth cap computed from a raw gate list and logarithmic constant `c₀`. -/
def mulDepthCap (c₀ : ℕ) (gates : List (LinearArithOp ℚ × List ℕ)) : ℕ :=
  c₀ * (Nat.log 2 (gates.length + 1) + 1)

/-- Computable rational binary gate evaluation matching `evalBinOp` on `ℚ`. -/
def evalBinOpRat (op : LinearArithBinOp) (a b : ℚ) : ℚ :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .max => if decide (a ≤ b) then b else a
  | .min => if decide (a ≤ b) then a else b
  | .gt => if decide (b < a) then 1 else 0

private theorem evalBinOpRat_eq (op : LinearArithBinOp) (a b : ℚ) :
    evalBinOpRat op a b = evalBinOp op a b := by
  cases op with
  | add | sub | mul => rfl
  | max =>
    dsimp [evalBinOpRat, evalBinOp]
    by_cases h : a ≤ b
    · simp [h]
    · simp [h, max_eq_left_of_lt (not_le.mp h)]
  | min =>
    dsimp [evalBinOpRat, evalBinOp]
    by_cases h : a ≤ b
    · simp [h]
    · simp [h, min_eq_right_of_lt (not_le.mp h)]
  | gt =>
    dsimp [evalBinOpRat, evalBinOp]
    by_cases h : b < a <;> simp [h]

/-- Clamped `(ℚ × ℕ)` interpretation tracking `(value, mulDepth)`. -/
noncomputable def boundedRatInterpretation (cap : ℕ) :
    Interpretation (linearArithSignature ℚ) (ℚ × ℕ)
  | .const q, _ => (q, 0)
  | .bin op, args =>
      let w0 := args 0
      let w1 := args 1
      let d := Max.max w0.2 w1.2 + (if op = .mul then 1 else 0)
      if decide (d ≤ cap) then
        (evalBinOpRat op w0.1 w1.1, d)
      else
        (0, cap + 1)

/-- Runtime gate-list evaluator under multiplication-depth cap `mulDepthCap c₀ gates`. -/
noncomputable def evalWellBehavedCode (c₀ : ℕ) (x : List ℚ)
    (gates : List (LinearArithOp ℚ × List ℕ)) : List (ℚ × ℕ) :=
  evalCode (boundedRatInterpretation (mulDepthCap c₀ gates)) (0, 0)
    (x.map fun q ↦ (q, 0)) gates

/-- Runtime multi-output evaluator returning rational output values. -/
noncomputable def evalWellBehavedOutputs (c₀ : ℕ)
    (code : List (LinearArithOp ℚ × List ℕ) × List ℕ) (x : List ℚ) : List ℚ :=
  (evalOutputs (boundedRatInterpretation (mulDepthCap c₀ code.1)) (0, 0)
    code (x.map fun q ↦ (q, 0))).map Prod.fst

private theorem length_program_code {σ : Signature} {n g : ℕ} (p : Program σ n g) :
    p.code.length = g := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [Program.code_gate, ih]

private theorem trace_boundedRatInterpretation_eq {n g : ℕ}
    (p : Program (linearArithSignature ℚ) n g) (x : Fin n → ℚ) (cap : ℕ) (w : Wire n g)
    (hw : p.wireDepthsWith LinearArithOp.mulCost w ≤ cap) :
    p.trace (boundedRatInterpretation cap) (fun i ↦ (x i, 0)) w =
      (p.trace ratInterpretation x w, p.wireDepthsWith LinearArithOp.mulCost w) := by
  refine p.wire_induction
    (P := fun w ↦ p.wireDepthsWith LinearArithOp.mulCost w ≤ cap →
      p.trace (boundedRatInterpretation cap) (fun i ↦ (x i, 0)) w =
        (p.trace ratInterpretation x w, p.wireDepthsWith LinearArithOp.mulCost w))
    (fun _ _ ↦ rfl) (fun k ih hk ↦ ?_) w hw
  rw [Program.wireDepthsWith_gateWire] at hk
  have harg : ∀ s, p.wireDepthsWith LinearArithOp.mulCost ((p.lines k).wires s) ≤ cap := fun s ↦
    (Nat.le_add_right _ _).trans
      ((p.wireDepthsWith_lines_add_le LinearArithOp.mulCost k s).trans hk)
  rw [p.trace_gate, p.trace_gate, Program.wireDepthsWith_gateWire,
    p.depthsWith_eq_depthWith_lines]
  rw [p.depthsWith_eq_depthWith_lines] at hk
  generalize p.lines k = line at ih harg hk ⊢
  rcases line with ⟨bop | q, wires_l⟩
  · dsimp only at ih harg
    have ih0 := ih 0 (harg 0)
    have ih1 := ih 1 (harg 1)
    have hfold : Fin.foldl 2 (fun depth s ↦
        Max.max depth (p.wireDepthsWith LinearArithOp.mulCost (wires_l s))) 0 =
        Max.max (p.wireDepthsWith LinearArithOp.mulCost (wires_l 0))
          (p.wireDepthsWith LinearArithOp.mulCost (wires_l 1)) := by
      simp [Fin.foldl_succ]
    have hcost : LinearArithOp.mulCost (LinearArithOp.bin bop : LinearArithOp ℚ) =
        (if bop = .mul then 1 else 0) := by
      cases bop <;> rfl
    have hd_eq : Max.max (p.wireDepthsWith LinearArithOp.mulCost (wires_l 0))
          (p.wireDepthsWith LinearArithOp.mulCost (wires_l 1)) +
          (if bop = .mul then 1 else 0) =
        (⟨LinearArithOp.bin bop, wires_l⟩ :
          Line (linearArithSignature ℚ) n g).depthWith LinearArithOp.mulCost
          (p.wireDepthsWith LinearArithOp.mulCost) := by
      simp [Line.depthWith, hfold, hcost]
    dsimp only at hk ⊢
    simp only [boundedRatInterpretation, ratInterpretation, linearArithInterpretation,
      ih0, ih1, hd_eq, decide_eq_true_eq.mpr hk, ↓reduceIte, evalBinOpRat_eq]
  · simp [boundedRatInterpretation, ratInterpretation, linearArithInterpretation,
      Line.depthWith, LinearArithOp.mulCost]

/-- On every `c₀`-well-behaved circuit `c`, `evalWellBehavedOutputs` computes the exact output list
`List.ofFn (c.eval ratInterpretation x)`. -/
theorem evalWellBehavedOutputs_eq_of_isWellBehaved {c₀ n m : ℕ}
    {c : Circuit (linearArithSignature ℚ) n m} (hw : IsWellBehaved c₀ c) (x : Fin n → ℚ) :
    evalWellBehavedOutputs c₀ c.code (List.ofFn x) =
      List.ofFn (c.eval ratInterpretation x) := by
  have hcode_len : c.code.1.length = c.size := length_program_code c.program
  have hcap : c.depthWith LinearArithOp.mulCost ≤ mulDepthCap c₀ c.code.1 := by
    rw [IsWellBehaved, mulDepth, ← hcode_len] at hw
    exact hw
  have hmap : (List.ofFn x).map (fun q ↦ (q, (0 : ℕ))) = List.ofFn (fun i ↦ (x i, (0 : ℕ))) := by
    simp [Function.comp_def]
  unfold evalWellBehavedOutputs
  rw [hmap, Circuit.evalOutputs_code, List.map_ofFn]
  congr 1
  ext j
  simp only [Function.comp_apply]
  have hj : c.program.wireDepthsWith LinearArithOp.mulCost (c.outputs j) ≤
      mulDepthCap c₀ c.code.1 :=
    (c.wireDepthsWith_outputs_le_depthWith LinearArithOp.mulCost j).trans hcap
  exact congrArg Prod.fst
    (trace_boundedRatInterpretation_eq c.program x (mulDepthCap c₀ c.code.1) (c.outputs j) hj)

private def constDen (op : LinearArithOp ℚ) : ℕ :=
  match op with
  | .const q => q.den
  | .bin _ => 1

private def constNumAbs (op : LinearArithOp ℚ) : ℕ :=
  match op with
  | .const q => q.num.natAbs
  | .bin _ => 0

private def commonDen (x : List ℚ) (gates : List (LinearArithOp ℚ × List ℕ)) : ℕ :=
  (x.map Rat.den).prod * (gates.map fun g ↦ constDen g.1).prod

private def maxNumAbs (x : List ℚ) (gates : List (LinearArithOp ℚ × List ℕ)) : ℕ :=
  Max.max 1 (Max.max ((x.map fun q ↦ q.num.natAbs).foldr Max.max 0)
    ((gates.map fun g ↦ constNumAbs g.1).foldr Max.max 0))

private lemma commonDen_pos (x : List ℚ) (gates : List (LinearArithOp ℚ × List ℕ)) :
    1 ≤ commonDen x gates := by
  have hx : 1 ≤ (x.map Rat.den).prod := by
    refine List.one_le_prod_of_one_le fun d hd ↦ ?_
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hd
    exact Nat.succ_le_of_lt q.pos
  have hg : 1 ≤ (gates.map fun g ↦ constDen g.1).prod := by
    refine List.one_le_prod_of_one_le fun d hd ↦ ?_
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hd
    cases h : g.1 with
    | const q => simpa [constDen] using Nat.succ_le_of_lt q.pos
    | bin _ => simp [constDen]
  exact one_le_mul_of_one_le_of_one_le hx hg

private lemma maxNumAbs_pos (x : List ℚ) (gates : List (LinearArithOp ℚ × List ℕ)) :
    1 ≤ maxNumAbs x gates :=
  le_max_left 1 _

private lemma foldr_max_le_of_forall {l : List ℕ} {B : ℕ} (h : ∀ m ∈ l, m ≤ B) :
    l.foldr Max.max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le B
  | cons a l ih =>
    exact max_le (h a (List.mem_cons_self ..)) (ih fun m hm ↦ h m (List.mem_cons_of_mem _ hm))

private lemma mem_le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ≤ l.foldr Max.max 0 := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | hm
    · exact le_max_left _ _
    · exact (ih hm).trans (le_max_right _ _)

private lemma rat_eq_over_commonDen {q : ℚ} {D M₀ : ℕ} (hD1 : 1 ≤ D) (hdiv : q.den ∣ D)
    (hnum : q.num.natAbs ≤ M₀) :
    ∃ z : ℤ, q = (z : ℚ) / (D : ℚ) ∧ z.natAbs ≤ M₀ * D := by
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨q.num * (k : ℤ), ?_, ?_⟩
  · have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hk
      omega
    have hk_q : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, mul_div_mul_right _ _ hk_q,
      Rat.num_div_den]
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    have hk_le : k ≤ D := by
      rw [hk]
      exact Nat.le_mul_of_pos_left k q.pos
    exact Nat.mul_le_mul hnum hk_le

private def WireBounded (D M₀ cap t : ℕ) (w : ℚ × ℕ) : Prop :=
  (w.2 ≤ cap ∧ ∃ z : ℤ, w.1 = (z : ℚ) / ((D ^ (2 ^ w.2) : ℕ) : ℚ) ∧
      z.natAbs ≤ (2 ^ t * M₀ * D) ^ (2 ^ w.2)) ∨
    (w.1 = 0 ∧ w.2 = cap + 1)

private lemma wireBounded_zero (D M₀ cap t : ℕ) : WireBounded D M₀ cap t (0, 0) :=
  Or.inl ⟨Nat.zero_le cap, 0, by simp, by simp⟩

private lemma wireBounded_mono_step {D M₀ cap t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {w : ℚ × ℕ}
    (hw : WireBounded D M₀ cap t₁ w) : WireBounded D M₀ cap t₂ w := by
  rcases hw with ⟨hd, z, hv, hz⟩ | hclamp
  · refine Or.inl ⟨hd, z, hv, hz.trans ?_⟩
    exact Nat.pow_le_pow_left (Nat.mul_le_mul_right D
      (Nat.mul_le_mul_right M₀ (Nat.pow_le_pow_right (by omega) ht))) _
  · exact Or.inr hclamp

private lemma scale_commonDen {D A d d' : ℕ} (hDA : D ≤ A) (hdd : d ≤ d')
    {v : ℚ} {z : ℤ} (hv : v = (z : ℚ) / ((D ^ (2 ^ d) : ℕ) : ℚ))
    (hz : z.natAbs ≤ A ^ (2 ^ d)) (hD1 : 1 ≤ D) :
    ∃ z' : ℤ, v = (z' : ℚ) / ((D ^ (2 ^ d') : ℕ) : ℚ) ∧ z'.natAbs ≤ A ^ (2 ^ d') := by
  have hpow_le : 2 ^ d ≤ 2 ^ d' := Nat.pow_le_pow_right (by omega) hdd
  set diff := 2 ^ d' - 2 ^ d
  have hsum : 2 ^ d + diff = 2 ^ d' := Nat.add_sub_of_le hpow_le
  refine ⟨z * ((D ^ diff : ℕ) : ℤ), ?_, ?_⟩
  · have hD0 : ((D ^ diff : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero (pow_ne_zero diff (by omega))).ne'
    rw [hv, ← hsum, pow_add, Nat.cast_mul, Int.cast_mul, Int.cast_natCast,
      mul_div_mul_right _ _ hD0]
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc z.natAbs * D ^ diff
        ≤ A ^ (2 ^ d) * A ^ diff := Nat.mul_le_mul hz (Nat.pow_le_pow_left hDA diff)
      _ = A ^ (2 ^ d') := by rw [← pow_add, hsum]

private lemma wireBounded_step {D M₀ cap t : ℕ} (hD1 : 1 ≤ D) (hM1 : 1 ≤ M₀)
    {gate : LinearArithOp ℚ × List ℕ}
    (hconst_den : constDen gate.1 ∣ D) (hconst_num : constNumAbs gate.1 ≤ M₀)
    {tr : List (ℚ × ℕ)} (htrace : ∀ w ∈ tr, WireBounded D M₀ cap t w) :
    ∀ w ∈ evalCodeStep (boundedRatInterpretation cap) (0, 0) (tr, gate),
      WireBounded D M₀ cap (t + 1) w := by
  intro w hw
  rcases gate with ⟨op, args⟩
  rw [evalCodeStep, List.mem_append, List.mem_singleton] at hw
  rcases hw with hmem | rfl
  · exact wireBounded_mono_step (Nat.le_succ t) (htrace w hmem)
  · let arg (i : ℕ) : ℚ × ℕ := args[i]?.elim (0, 0) (tr.getD · (0, 0))
    have harg_bd : ∀ i : ℕ, WireBounded D M₀ cap t (arg i) := fun i ↦ by
      dsimp only [arg]
      rcases args[i]? with _ | idx
      · exact wireBounded_zero D M₀ cap t
      · rw [Option.elim_some, List.getD_eq_getElem?_getD]
        rcases hget : tr[idx]? with _ | w'
        · exact wireBounded_zero D M₀ cap t
        · exact htrace w' (List.mem_of_getElem? hget)
    cases op with
    | bin bop =>
      set w0 := arg 0
      set w1 := arg 1
      set d_max := Max.max w0.2 w1.2
      set d := d_max + (if bop = .mul then 1 else 0)
      change WireBounded D M₀ cap (t + 1)
        (if decide (d ≤ cap) then (evalBinOpRat bop w0.1 w1.1, d) else (0, cap + 1))
      by_cases hle : d ≤ cap
      · simp only [decide_eq_true hle, ↓reduceIte]
        have hw0_le : w0.2 ≤ cap := (le_max_left w0.2 w1.2).trans ((Nat.le_add_right _ _).trans hle)
        have hw1_le : w1.2 ≤ cap :=
          (le_max_right w0.2 w1.2).trans ((Nat.le_add_right _ _).trans hle)
        obtain ⟨_, z0, hv0, hz0⟩ :
            w0.2 ≤ cap ∧ ∃ z : ℤ, w0.1 = (z : ℚ) / ((D ^ (2 ^ w0.2) : ℕ) : ℚ) ∧
              z.natAbs ≤ (2 ^ t * M₀ * D) ^ (2 ^ w0.2) := by
          rcases (show WireBounded D M₀ cap t w0 from harg_bd 0) with h | ⟨_, hc⟩
          · exact h
          · omega
        obtain ⟨_, z1, hv1, hz1⟩ :
            w1.2 ≤ cap ∧ ∃ z : ℤ, w1.1 = (z : ℚ) / ((D ^ (2 ^ w1.2) : ℕ) : ℚ) ∧
              z.natAbs ≤ (2 ^ t * M₀ * D) ^ (2 ^ w1.2) := by
          rcases (show WireBounded D M₀ cap t w1 from harg_bd 1) with h | ⟨_, hc⟩
          · exact h
          · omega
        set A := 2 ^ t * M₀ * D
        have hDA : D ≤ A := by
          have : 1 ≤ 2 ^ t * M₀ := Nat.mul_pos (Nat.two_pow_pos t) hM1
          exact Nat.le_mul_of_pos_left D this
        obtain ⟨u0, hu0_eq, hu0_bd⟩ :=
          scale_commonDen hDA (le_max_left w0.2 w1.2) hv0 hz0 hD1
        obtain ⟨u1, hu1_eq, hu1_bd⟩ :=
          scale_commonDen hDA (le_max_right w0.2 w1.2) hv1 hz1 hD1
        have h2A : 2 * A = 2 ^ (t + 1) * M₀ * D := by dsimp [A]; ring
        have htwo_pow_pos : 0 < 2 ^ d_max := Nat.two_pow_pos d_max
        have h2_le_pow : 2 * A ^ (2 ^ d_max) ≤ (2 * A) ^ (2 ^ d_max) := by
          rw [Nat.mul_pow 2 A]
          exact Nat.mul_le_mul_right _ (Nat.le_self_pow htwo_pow_pos.ne' 2)
        cases bop with
        | add =>
          have hd_eq : d = d_max := by simp [d]
          refine Or.inl ⟨hle, u0 + u1, ?_, ?_⟩
          · rw [evalBinOpRat_eq, evalBinOp, hu0_eq, hu1_eq, hd_eq, Int.cast_add, add_div]
          · rw [hd_eq, ← h2A]
            exact (Int.natAbs_add_le u0 u1).trans ((Nat.add_le_add hu0_bd hu1_bd).trans
              (by simpa [two_mul] using h2_le_pow))
        | sub =>
          have hd_eq : d = d_max := by simp [d]
          refine Or.inl ⟨hle, u0 - u1, ?_, ?_⟩
          · rw [evalBinOpRat_eq, evalBinOp, hu0_eq, hu1_eq, hd_eq, Int.cast_sub, sub_div]
          · rw [hd_eq, ← h2A]
            exact (Int.natAbs_sub_le u0 u1).trans ((Nat.add_le_add hu0_bd hu1_bd).trans
              (by simpa [two_mul] using h2_le_pow))
        | max =>
          have hd_eq : d = d_max := by simp [d]
          by_cases hcmp : w0.1 ≤ w1.1
          · refine Or.inl ⟨hle, u1, ?_, ?_⟩
            · simp only [evalBinOpRat, decide_eq_true hcmp, ↓reduceIte, hd_eq]
              exact hu1_eq
            · rw [hd_eq, ← h2A]
              exact hu1_bd.trans (Nat.pow_le_pow_left (by omega) _)
          · refine Or.inl ⟨hle, u0, ?_, ?_⟩
            · simp only [evalBinOpRat, decide_eq_false hcmp, Bool.false_eq_true, ↓reduceIte, hd_eq]
              exact hu0_eq
            · rw [hd_eq, ← h2A]
              exact hu0_bd.trans (Nat.pow_le_pow_left (by omega) _)
        | min =>
          have hd_eq : d = d_max := by simp [d]
          by_cases hcmp : w0.1 ≤ w1.1
          · refine Or.inl ⟨hle, u0, ?_, ?_⟩
            · simp only [evalBinOpRat, decide_eq_true hcmp, ↓reduceIte, hd_eq]
              exact hu0_eq
            · rw [hd_eq, ← h2A]
              exact hu0_bd.trans (Nat.pow_le_pow_left (by omega) _)
          · refine Or.inl ⟨hle, u1, ?_, ?_⟩
            · simp only [evalBinOpRat, decide_eq_false hcmp, Bool.false_eq_true, ↓reduceIte, hd_eq]
              exact hu1_eq
            · rw [hd_eq, ← h2A]
              exact hu1_bd.trans (Nat.pow_le_pow_left (by omega) _)
        | gt =>
          have hd_eq : d = d_max := by simp [d]
          by_cases hcmp : w1.1 < w0.1
          · refine Or.inl ⟨hle, (D ^ (2 ^ d_max) : ℕ), ?_, ?_⟩
            · have hD0 : ((D ^ (2 ^ d_max) : ℕ) : ℚ) ≠ 0 :=
                Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))).ne'
              simp only [evalBinOpRat, decide_eq_true hcmp, ↓reduceIte, hd_eq, Int.cast_natCast]
              exact (div_self hD0).symm
            · rw [Int.natAbs_natCast, hd_eq, ← h2A]
              exact (Nat.pow_le_pow_left hDA _).trans (Nat.pow_le_pow_left (by omega) _)
          · refine Or.inl ⟨hle, 0, ?_, ?_⟩
            · simp [evalBinOpRat, hcmp, hd_eq]
            · simp
        | mul =>
          have hd_eq : d = d_max + 1 := by simp [d]
          have hpow2 : 2 ^ d = 2 ^ d_max + 2 ^ d_max := by
            rw [hd_eq, pow_succ, mul_two]
          refine Or.inl ⟨hle, u0 * u1, ?_, ?_⟩
          · rw [evalBinOpRat_eq, evalBinOp, hu0_eq, hu1_eq, hpow2, pow_add, Nat.cast_mul,
              Int.cast_mul, div_mul_div_comm]
          · rw [Int.natAbs_mul, hpow2, ← h2A]
            calc u0.natAbs * u1.natAbs
                ≤ A ^ (2 ^ d_max) * A ^ (2 ^ d_max) := Nat.mul_le_mul hu0_bd hu1_bd
              _ = A ^ (2 ^ d_max + 2 ^ d_max) := (pow_add A _ _).symm
              _ ≤ (2 * A) ^ (2 ^ d_max + 2 ^ d_max) := Nat.pow_le_pow_left (by omega) _
      · simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr ⟨rfl, rfl⟩
    | const q =>
      change WireBounded D M₀ cap (t + 1) (q, 0)
      have hqd : q.den ∣ D := by simpa [constDen] using hconst_den
      have hqn : q.num.natAbs ≤ M₀ := by simpa [constNumAbs] using hconst_num
      obtain ⟨z, hzv, hzb⟩ := rat_eq_over_commonDen hD1 hqd hqn
      refine Or.inl ⟨Nat.zero_le cap, z, ?_, ?_⟩
      · simpa using hzv
      · simpa [Nat.mul_assoc] using hzb.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (t + 1)))

private lemma prod_den_le_two_pow_encList (x : List ℚ) :
    (x.map Rat.den).prod ≤ 2 ^ (encList encRat x).length := by
  induction x with
  | nil => simp
  | cons q xs ih =>
    simp only [List.map_cons, List.prod_cons, encList_cons, List.length_append, length_frame]
    have hq : q.den ≤ 2 ^ (encRat q).length := (den_lt_two_pow_length_encRat q).le
    have hq2 : q.den ≤ 2 ^ (2 * (encRat q).length + 1) :=
      hq.trans (Nat.pow_le_pow_right (by omega) (by omega))
    calc q.den * (xs.map Rat.den).prod
        ≤ 2 ^ (2 * (encRat q).length + 1) * 2 ^ (encList encRat xs).length :=
          Nat.mul_le_mul hq2 ih
      _ = 2 ^ ((2 * (encRat q).length + 1) + (encList encRat xs).length) :=
          (pow_add 2 _ _).symm

private lemma length_encRat_le_encGate (g : LinearArithOp ℚ × List ℕ) (q : ℚ)
    (hq : g.1 = .const q) :
    (encRat q).length ≤ (Circuit.encGate (LinearArithOp.encoding encRat) g).length := by
  have h1 : (LinearArithOp.encoding encRat g.1).length = (encRat q).length + 1 := by
    simp [LinearArithOp.encoding, LinearArithOp.equivSum, hq]
  simp only [Circuit.encGate, length_encPair, h1]
  omega

private lemma prod_constDen_le_two_pow_encGates (gates : List (LinearArithOp ℚ × List ℕ)) :
    (gates.map fun g ↦ constDen g.1).prod ≤
      2 ^ (encList (Circuit.encGate (LinearArithOp.encoding encRat)) gates).length := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.prod_cons, encList_cons, List.length_append, length_frame]
    have hg : constDen g.1 ≤
        2 ^ (2 * (Circuit.encGate (LinearArithOp.encoding encRat) g).length + 1) := by
      cases h : g.1 with
      | bin _ =>
        simp only [constDen]
        exact Nat.one_le_two_pow
      | const q =>
        simp only [constDen]
        have hlen := length_encRat_le_encGate g q h
        exact (den_lt_two_pow_length_encRat q).le.trans
          (Nat.pow_le_pow_right (by omega) (by omega))
    calc constDen g.1 * (gs.map fun g ↦ constDen g.1).prod
        ≤ 2 ^ (2 * (Circuit.encGate (LinearArithOp.encoding encRat) g).length + 1) *
            2 ^ (encList (Circuit.encGate (LinearArithOp.encoding encRat)) gs).length :=
          Nat.mul_le_mul hg ih
      _ = _ := (pow_add 2 _ _).symm

private lemma maxNumAbs_le_two_pow (x : List ℚ) (gates : List (LinearArithOp ℚ × List ℕ)) :
    maxNumAbs x gates ≤
      2 ^ ((encList encRat x).length +
        (encList (Circuit.encGate (LinearArithOp.encoding encRat)) gates).length) := by
  set Bx := (encList encRat x).length
  set Bg := (encList (Circuit.encGate (LinearArithOp.encoding encRat)) gates).length
  refine max_le Nat.one_le_two_pow (max_le ?_ ?_)
  · refine foldr_max_le_of_forall fun m hm ↦ ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    have hlen : (encRat q).length ≤ Bx :=
      SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) x q hq
    exact (natAbs_num_lt_two_pow_length_encRat q).le.trans
      (Nat.pow_le_pow_right (by omega) (hlen.trans (Nat.le_add_right Bx Bg)))
  · refine foldr_max_le_of_forall fun m hm ↦ ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
    cases h : g.1 with
    | bin _ => simp [constNumAbs]
    | const q =>
      simp only [constNumAbs]
      have hlen1 := length_encRat_le_encGate g q h
      have hlen2 := SizedListEncoding.length_elem_le
        (encA := Circuit.encGate (LinearArithOp.encoding encRat))
        (encL := encList (Circuit.encGate (LinearArithOp.encoding encRat))) gates g hg
      exact (natAbs_num_lt_two_pow_length_encRat q).le.trans
        (Nat.pow_le_pow_right (by omega) ((hlen1.trans hlen2).trans (Nat.le_add_left Bg Bx)))

private lemma encWire_length_of_wireBounded {D M₀ cap t E K : ℕ} (hD1 : 1 ≤ D)
    (hD_le : D ≤ 2 ^ E) (hM_le : M₀ ≤ 2 ^ E) (ht_le : t ≤ E) (hK : 2 ^ cap ≤ K)
    {w : ℚ × ℕ} (hw : WireBounded D M₀ cap t w) :
    (encPair encRat encUnary w).length ≤ 18 * (E * K) + cap + 15 := by
  rcases hw with ⟨hd, z, hv, hz⟩ | ⟨hv0, hd⟩
  · have hA_le : 2 ^ t * M₀ * D ≤ 2 ^ (3 * E) := by
      calc 2 ^ t * M₀ * D
          ≤ 2 ^ E * 2 ^ E * 2 ^ E :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) ht_le) hM_le) hD_le
        _ = 2 ^ (3 * E) := by rw [← pow_add, ← pow_add]; congr 1; omega
    have h2d_le : 2 ^ w.2 ≤ K := (Nat.pow_le_pow_right (by omega) hd).trans hK
    have hz_pow : z.natAbs ≤ 2 ^ (3 * (E * K)) := by
      calc z.natAbs
          ≤ (2 ^ t * M₀ * D) ^ (2 ^ w.2) := hz
        _ ≤ (2 ^ (3 * E)) ^ K :=
            (Nat.pow_le_pow_left hA_le _).trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) h2d_le)
        _ = 2 ^ (3 * (E * K)) := by rw [← pow_mul, Nat.mul_assoc]
    have hden_pow : D ^ (2 ^ w.2) ≤ 2 ^ (3 * (E * K)) := by
      calc D ^ (2 ^ w.2)
          ≤ (2 ^ E) ^ K :=
            (Nat.pow_le_pow_left hD_le _).trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) h2d_le)
        _ = 2 ^ (E * K) := (pow_mul 2 E K).symm
        _ ≤ 2 ^ (3 * (E * K)) := Nat.pow_le_pow_right (by omega) (by omega)
    have hdivInt : w.1 = Rat.divInt z ((D ^ (2 ^ w.2) : ℕ) : ℤ) := by
      rw [hv, Rat.divInt_eq_div, Int.cast_natCast]
    have hden_ne : ((D ^ (2 ^ w.2) : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (pow_pos (by omega : 0 < D) (2 ^ w.2)).ne'
    have hnum_le : w.1.num.natAbs ≤ 2 ^ (3 * (E * K)) := by
      rw [hdivInt]
      exact (Rat.natAbs_num_divInt_le z _ hden_ne).trans hz_pow
    have hden_le : w.1.den ≤ 2 ^ (3 * (E * K)) := by
      rw [hdivInt]
      exact (Rat.den_divInt_le z _ hden_ne).trans (by simpa using hden_pow)
    have hsize_pow : (2 ^ (3 * (E * K))).size ≤ 3 * (E * K) + 1 :=
      Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _))
    have hrat_len : (encRat w.1).length ≤ 9 * (E * K) + 6 := by
      have h := length_encRat_le w.1 hnum_le hden_le
      omega
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  · have h0_len : (encRat (0 : ℚ)).length = 4 := by
      rw [length_encRat]; rfl
    simp only [length_encPair, hv0, h0_len, hd, encUnary_apply, List.length_replicate]
    omega

private def evalBoundedLeftBranch (p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ))
    (bop : LinearArithBinOp) : ℚ × ℕ :=
  let w0 := p.2.2[0]?.elim ((0 : ℚ), (0 : ℕ)) (p.1.2.getD · ((0 : ℚ), (0 : ℕ)))
  let w1 := p.2.2[1]?.elim ((0 : ℚ), (0 : ℕ)) (p.1.2.getD · ((0 : ℚ), (0 : ℕ)))
  let d := Max.max w0.2 w1.2 + (if bop = .mul then 1 else 0)
  if decide (d ≤ p.1.1) then (evalBinOpRat bop w0.1 w1.1, d) else (0, p.1.1 + 1)

private def evalBoundedRightBranch (_ : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ))
    (q : ℚ) : ℚ × ℕ :=
  (q, 0)

private abbrev encBoundedWire : ℚ × ℕ ↪ List Bool :=
  encPair encRat encUnary

private abbrev encBoundedStep :
    ((ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ)) ↪ List Bool :=
  encPair (encPair encUnary (encList encBoundedWire))
    (Circuit.encGate (LinearArithOp.encoding encRat))

private theorem polyTime_evalBoundedStep :
    ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦
        evalCodeStep (boundedRatInterpretation p.1.1) (0, 0) (p.1.2, p.2))
      encBoundedStep (encList encBoundedWire) := by
  have hcap : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦ p.1.1)
      encBoundedStep encUnary :=
    (fst (encPair encUnary (encList encBoundedWire))
      (Circuit.encGate (LinearArithOp.encoding encRat))).fst'
  have htrace : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦ p.1.2)
      encBoundedStep (encList encBoundedWire) :=
    (fst (encPair encUnary (encList encBoundedWire))
      (Circuit.encGate (LinearArithOp.encoding encRat))).snd'
  have hop : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦ p.2.1)
      encBoundedStep (LinearArithOp.encoding encRat) :=
    (snd (encPair encUnary (encList encBoundedWire))
      (Circuit.encGate (LinearArithOp.encoding encRat))).fst'
  have hargs : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦ p.2.2)
      encBoundedStep (encList encNat) :=
    (snd (encPair encUnary (encList encBoundedWire))
      (Circuit.encGate (LinearArithOp.encoding encRat))).snd'
  have hw (i : ℕ) : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦
        p.2.2[i]?.elim ((0 : ℚ), (0 : ℕ)) (p.1.2.getD · ((0 : ℚ), (0 : ℕ))))
      encBoundedStep encBoundedWire :=
    optionElimWithInput (getElem? hargs (const i)) (const ((0 : ℚ), (0 : ℕ)))
      (listGetD_binary (encA := encBoundedWire) ((0 : ℚ), (0 : ℕ))
        (htrace.comp' (fst encBoundedStep encNat)) (snd encBoundedStep encNat))
  have hop_sum : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦ LinearArithOp.equivSum p.2.1)
      encBoundedStep (encSum encLinearArithBinOp encRat) :=
    (ComputableInPolyTime.of_eq (f := LinearArithOp.equivSum)
      (encIn := LinearArithOp.encoding encRat)
      (encOut := encSum encLinearArithBinOp encRat) fun _ ↦ rfl).comp' hop
  have hleft : ComputableInPolyTime
      (fun q : ((ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ)) × LinearArithBinOp ↦
        evalBoundedLeftBranch q.1 q.2)
      (encPair encBoundedStep encLinearArithBinOp) encBoundedWire := by
    refine finite_cases (input := encPair encBoundedStep encLinearArithBinOp)
      (output := encBoundedWire) (tagEncoding := encLinearArithBinOp)
      (tag := Prod.snd) (branch := fun bop q ↦ evalBoundedLeftBranch q.1 bop)
      (snd encBoundedStep encLinearArithBinOp) fun bop ↦ ?_
    have hw0 := (hw 0).comp' (fst encBoundedStep encLinearArithBinOp)
    have hw1 := (hw 1).comp' (fst encBoundedStep encLinearArithBinOp)
    have hcap' := hcap.comp' (fst encBoundedStep encLinearArithBinOp)
    have hd : ComputableInPolyTime
        (fun q : ((ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ)) × LinearArithBinOp ↦
          Max.max (q.1.2.2[0]?.elim ((0 : ℚ), (0 : ℕ)) (q.1.1.2.getD · ((0 : ℚ), (0 : ℕ)))).2
            (q.1.2.2[1]?.elim ((0 : ℚ), (0 : ℕ)) (q.1.1.2.getD · ((0 : ℚ), (0 : ℕ)))).2 +
            (if bop = .mul then 1 else 0))
        (encPair encBoundedStep encLinearArithBinOp) encUnary :=
      unary_add' (unary_max.comp' (hw0.snd'.prod hw1.snd')) (const (if bop = .mul then 1 else 0))
    have hbin : ComputableInPolyTime
        (fun q : ((ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ)) × LinearArithBinOp ↦
          evalBinOpRat bop
            (q.1.2.2[0]?.elim ((0 : ℚ), (0 : ℕ)) (q.1.1.2.getD · ((0 : ℚ), (0 : ℕ)))).1
            (q.1.2.2[1]?.elim ((0 : ℚ), (0 : ℕ)) (q.1.1.2.getD · ((0 : ℚ), (0 : ℕ)))).1)
        (encPair encBoundedStep encLinearArithBinOp) encRat := by
      cases bop with
      | add => exact rat_add' hw0.fst' hw1.fst'
      | sub => exact rat_sub' hw0.fst' hw1.fst'
      | mul => exact rat_mul' hw0.fst' hw1.fst'
      | max => exact (rat_le' hw0.fst' hw1.fst').ite' hw1.fst' hw0.fst'
      | min => exact (rat_le' hw0.fst' hw1.fst').ite' hw0.fst' hw1.fst'
      | gt => exact (rat_lt' hw1.fst' hw0.fst').ite' (const 1) (const 0)
    exact (unary_le' hd hcap').ite' (hbin.prod hd) ((const 0).prod (unary_add' hcap' (const 1)))
  have hright : ComputableInPolyTime
      (fun q : ((ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ)) × ℚ ↦
        evalBoundedRightBranch q.1 q.2)
      (encPair encBoundedStep encRat) encBoundedWire :=
    (snd encBoundedStep encRat).prod (const 0)
  have hval := sumElimWithInput (left := evalBoundedLeftBranch) (right := evalBoundedRightBranch)
    hop_sum hleft hright
  have hval_eq : ComputableInPolyTime
      (fun p : (ℕ × List (ℚ × ℕ)) × (LinearArithOp ℚ × List ℕ) ↦
        boundedRatInterpretation p.1.1 p.2.1 fun a ↦
          p.2.2[a.val]?.elim ((0 : ℚ), (0 : ℕ)) (p.1.2.getD · ((0 : ℚ), (0 : ℕ))))
      encBoundedStep encBoundedWire := by
    refine hval.of_enc_eq fun p ↦ congrArg encBoundedWire ?_
    rcases p.2.1 with bop | q <;> rfl
  exact listAppend' htrace (cons' hval_eq (const []))

/-- **Polynomial-Time Gate-Trace Evaluation of Well-Behaved Rational Arithmetic Circuits**. -/
theorem computableInPolyTime_evalWellBehavedCode (c₀ : ℕ) {α : Type}
    {encIn : α ↪ List Bool} {x : α → List ℚ}
    {gates : α → List (LinearArithOp ℚ × List ℕ)}
    (hx : ComputableInPolyTime x encIn (encList encRat))
    (hgates : ComputableInPolyTime gates encIn
      (encList (Circuit.encGate (LinearArithOp.encoding encRat)))) :
    ComputableInPolyTime (fun a ↦ evalWellBehavedCode c₀ (x a) (gates a))
      encIn (encList (encPair encRat encUnary)) := by
  let encWire := encPair encRat encUnary
  let encGateQ := Circuit.encGate (LinearArithOp.encoding encRat)
  have hlen : ComputableInPolyTime (fun a ↦ (gates a).length) encIn encUnary :=
    (length_list encGateQ).comp hgates
  have hcap : ComputableInPolyTime (fun a ↦ mulDepthCap c₀ (gates a)) encIn encUnary :=
    unary_mul' (const c₀) (unary_add' (unary_log_two.comp (unary_add' hlen (const 1))) (const 1))
  have hinit : ComputableInPolyTime (fun a ↦ (x a).map fun q ↦ (q, (0 : ℕ)))
      encIn (encList encWire) :=
    mapWith ((snd encBool encRat).prod (const 0)) (const false) hx
  let E (a : α) : ℕ :=
    (encList encRat (x a)).length + (encList encGateQ (gates a)).length + (gates a).length + 1
  let K (a : α) : ℕ := (2 * ((gates a).length + 1)) ^ c₀
  let size (a : α) : ℕ :=
    ((x a).length + (gates a).length) *
      (2 * (18 * (E a * K a) + mulDepthCap c₀ (gates a) + 15) + 1)
  have hE_poly : PolyBounded (fun a ↦ (encIn a).length) E :=
    ((hx.polyBounded_length.add hgates.polyBounded_length).add hlen.polyBounded).add (.const 1)
  have hK_poly : PolyBounded (fun a ↦ (encIn a).length) K :=
    ((PolyBounded.const 2).mul (hlen.polyBounded.add (.const 1))).pow c₀
  have hxlen_poly : PolyBounded (fun a ↦ (encIn a).length) (fun a ↦ (x a).length) :=
    ((length_list encRat).comp hx).polyBounded
  have hsize_poly : PolyBounded (fun a ↦ (encIn a).length) size :=
    (hxlen_poly.add hlen.polyBounded).mul
      (((PolyBounded.const 2).mul
        ((((PolyBounded.const 18).mul (hE_poly.mul hK_poly)).add hcap.polyBounded).add
          (.const 15))).add (.const 1))
  refine (foldlWith_spec
    (step := fun cap trace gate ↦ evalCodeStep (boundedRatInterpretation cap) (0, 0) (trace, gate))
    hcap hgates hinit polyTime_evalBoundedStep
    (fun a consumed trace ↦
      trace.length = (x a).length + consumed.length ∧
      ∀ w ∈ trace, WireBounded (commonDen (x a) (gates a)) (maxNumAbs (x a) (gates a))
        (mulDepthCap c₀ (gates a)) consumed.length w)
    (fun a ↦ ?_) (fun a consumed trace g hpref ⟨hlen_tr, hbd⟩ ↦ ?_) hsize_poly
    (fun a consumed trace hpref ⟨hlen_tr, hbd⟩ ↦ ?_)).1
  · refine ⟨by simp, fun w hw ↦ ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
    have hqd : q.den ∣ commonDen (x a) (gates a) :=
      dvd_mul_of_dvd_left (List.dvd_prod (List.mem_map_of_mem hq)) _
    have hqn : q.num.natAbs ≤ maxNumAbs (x a) (gates a) :=
      (mem_le_foldr_max (List.mem_map_of_mem (f := fun r : ℚ ↦ r.num.natAbs) hq)).trans
        ((le_max_left _ _).trans (le_max_right 1 _))
    obtain ⟨z, hzv, hzb⟩ := rat_eq_over_commonDen (commonDen_pos (x a) (gates a)) hqd hqn
    exact Or.inl ⟨Nat.zero_le _, z, by simpa using hzv, by simpa using hzb⟩
  · have hg_mem : g ∈ gates a := hpref.subset (by simp)
    have hcd : constDen g.1 ∣ commonDen (x a) (gates a) :=
      dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map_of_mem hg_mem)) _
    have hcn : constNumAbs g.1 ≤ maxNumAbs (x a) (gates a) :=
      (mem_le_foldr_max
        (List.mem_map_of_mem (f := fun r : LinearArithOp ℚ × List ℕ ↦ constNumAbs r.1)
          hg_mem)).trans
        ((le_max_right _ _).trans (le_max_right 1 _))
    refine ⟨by simp [evalCodeStep, hlen_tr, Nat.add_assoc], ?_⟩
    simpa only [List.length_append, List.length_singleton] using
      wireBounded_step (commonDen_pos (x a) (gates a)) (maxNumAbs_pos (x a) (gates a))
        hcd hcn hbd
  · have hcons_le : consumed.length ≤ (gates a).length := hpref.length_le
    have hD_le : commonDen (x a) (gates a) ≤ 2 ^ E a := by
      calc commonDen (x a) (gates a)
          ≤ 2 ^ (encList encRat (x a)).length * 2 ^ (encList encGateQ (gates a)).length :=
            Nat.mul_le_mul (prod_den_le_two_pow_encList (x a))
              (prod_constDen_le_two_pow_encGates (gates a))
        _ = 2 ^ ((encList encRat (x a)).length + (encList encGateQ (gates a)).length) :=
            (pow_add 2 _ _).symm
        _ ≤ 2 ^ E a := Nat.pow_le_pow_right (by omega) (by dsimp [E, encGateQ]; omega)
    have hM_le : maxNumAbs (x a) (gates a) ≤ 2 ^ E a :=
      (maxNumAbs_le_two_pow (x a) (gates a)).trans
        (Nat.pow_le_pow_right (by omega) (by dsimp [E, encGateQ]; omega))
    have ht_le : consumed.length ≤ E a := hcons_le.trans (by dsimp [E]; omega)
    have hK_le : 2 ^ mulDepthCap c₀ (gates a) ≤ K a := by
      dsimp [mulDepthCap, K]
      rw [Nat.mul_comm c₀, pow_mul]
      refine Nat.pow_le_pow_left ?_ c₀
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
    have hper_elem : ∀ w ∈ trace,
        2 * (encWire w).length + 1 ≤
          2 * (18 * (E a * K a) + mulDepthCap c₀ (gates a) + 15) + 1 :=
      fun w hw ↦ Nat.add_le_add_right
        (Nat.mul_le_mul_left 2
          (encWire_length_of_wireBounded (commonDen_pos (x a) (gates a))
            hD_le hM_le ht_le hK_le (hbd w hw))) 1
    rw [length_encList]
    calc (trace.map fun w ↦ 2 * (encWire w).length + 1).sum
        ≤ trace.length * (2 * (18 * (E a * K a) + mulDepthCap c₀ (gates a) + 15) + 1) := by
          simpa only [List.length_map, smul_eq_mul] using
            List.sum_le_length_nsmul (trace.map fun w ↦ 2 * (encWire w).length + 1)
              (2 * (18 * (E a * K a) + mulDepthCap c₀ (gates a) + 15) + 1) fun m hm ↦ by
                obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
                exact hper_elem w hw
      _ ≤ size a := by
          dsimp [size]
          rw [hlen_tr]
          exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hcons_le _)

/-- **Polynomial-Time Multi-Output Evaluation of Well-Behaved Rational Arithmetic Circuits**. -/
@[fun_prop]
theorem computableInPolyTime_evalWellBehavedOutputs (c₀ : ℕ) {α : Type}
    {encIn : α ↪ List Bool}
    {code : α → List (LinearArithOp ℚ × List ℕ) × List ℕ} {x : α → List ℚ}
    (hcode : ComputableInPolyTime code encIn (Circuit.encCode (LinearArithOp.encoding encRat)))
    (hx : ComputableInPolyTime x encIn (encList encRat)) :
    ComputableInPolyTime (fun a ↦ evalWellBehavedOutputs c₀ (code a) (x a))
      encIn (encList encRat) := by
  have htrace := computableInPolyTime_evalWellBehavedCode c₀ hx hcode.fst'
  have hlookup : ComputableInPolyTime
      (fun a ↦ (code a).2.map fun o ↦ ((evalWellBehavedCode c₀ (x a) (code a).1).getD o (0, 0)).1)
      encIn (encList encRat) :=
    mapWithInput hcode.snd'
      ((listGetD_binary (encA := encBoundedWire) ((0 : ℚ), (0 : ℕ))
        (htrace.comp' (fst encIn encNat)) (snd encIn encNat)).fst')
  refine hlookup.of_enc_eq fun a ↦ congrArg (encList encRat) ?_
  simp [evalWellBehavedOutputs, evalOutputs, evalWellBehavedCode, List.map_map]

/-- **Uniform Polynomial-Time Evaluation of Typed Well-Behaved Rational Arithmetic Circuits**. -/
theorem computableInPolyTime_evalWellBehavedCircuit (c₀ m : ℕ) :
    ComputableInPolyTime
      (fun p : (Σ n, Circuit (linearArithSignature ℚ) n m) × List ℚ ↦
        evalWellBehavedOutputs c₀ p.1.2.code p.2)
      (encPair (encLinearArithCircuit m) (encList encRat)) (encList encRat) := by
  have h1 : ComputableInPolyTime
      (fun p : (Σ n, Circuit (linearArithSignature ℚ) n m) × List ℚ ↦ (p.1.1, p.1.2.code))
      (encPair (encLinearArithCircuit m) (encList encRat))
      (encPair encUnary (Circuit.encCode (LinearArithOp.encoding encRat))) :=
    (Circuit.computableInPolyTime_arity_code (σ := linearArithSignature ℚ)
      (LinearArithOp.encoding encRat) m).comp'
      (fst (encLinearArithCircuit m) (encList encRat))
  exact computableInPolyTime_evalWellBehavedOutputs c₀ h1.snd'
    (snd (encLinearArithCircuit m) (encList encRat))

end CslibFrontier.WellBehavedArithmetic
