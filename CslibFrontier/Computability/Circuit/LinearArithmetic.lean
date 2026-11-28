/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/
module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Basic.Real.Basic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Rat.Lemmas

/-!
# Linear Arithmetic Circuits: Semantics, Lipschitz Bounds, and Polynomial-Time Evaluation

This module formalizes **linear arithmetic circuits** (also called piecewise-linear arithmetic
circuits), whose gates perform input lookup, rational constants, addition, subtraction,
multiplication by a rational constant, minimum, and maximum.

Unlike general arithmetic circuits (where iterated multiplication causes doubly-exponential
bit-length blowup), linear arithmetic circuits have polynomially bounded wire denominators and
numerators: every intermediate wire denominator divides the product of all input and constant
denominators, and every wire magnitude grows by at most a single multiplicative factor per gate.
Consequently, rational evaluation of a linear arithmetic circuit is computable in polynomial
time (`CslibFrontier.Computability.Circuit.computableInPolyTime_evalRat`), and every linear
arithmetic circuit computes a globally Lipschitz continuous piecewise-linear map on `ℝⁿ` with a
computable rational Lipschitz bound (`CslibFrontier.Computability.Circuit.evalReal_lipschitz`).

## Main definitions

* `CslibFrontier.Computability.Circuit.LinearGate`: gate operations of a linear arithmetic circuit.
* `CslibFrontier.Computability.Circuit.LinearArithCircuit`: a linear arithmetic circuit (input
  arity, gate list, output wire list).
* `CslibFrontier.Computability.Circuit.encLinearGate`,
  `CslibFrontier.Computability.Circuit.encLinearArithCircuit`: binary encodings under
  `Turing.MultiTapeTM.encRat` and `Turing.MultiTapeTM.encNat`.
* `CslibFrontier.Computability.Circuit.evalGate`, `CslibFrontier.Computability.Circuit.evalWires`,
  `CslibFrontier.Computability.Circuit.evalRat`, `CslibFrontier.Computability.Circuit.evalReal`:
  exact wire and output evaluation over `ℚ` and `ℝ`.
* `CslibFrontier.Computability.Circuit.lipschitzStep`,
  `CslibFrontier.Computability.Circuit.wireLipschitzBounds`,
  `CslibFrontier.Computability.Circuit.outputLipschitzBound`: computable rational `ℓ∞`-Lipschitz
  bounds for each wire and output.

## Main results

* `CslibFrontier.Computability.Circuit.evalReal_eq_evalRat`: real evaluation on rational inputs
  agrees with rational evaluation.
* `CslibFrontier.Computability.Circuit.evalReal_lipschitz`: global `ℓ∞`-Lipschitz continuity of
  every linear arithmetic circuit.
* `CslibFrontier.Computability.Circuit.computableInPolyTime_evalRat`: rational evaluation of a
  linear arithmetic circuit is computable in polynomial time.
-/

public section

namespace CslibFrontier.Computability.Circuit

open Turing.MultiTapeTM ComputableInPolyTime

/-- A single gate of a linear arithmetic circuit. Wire indices are `0`-based, with inputs
occupying wires `0, …, numInputs - 1` and gate `k` writing to wire `numInputs + k`. -/
inductive LinearGate : Type
  /-- Forward wire `idx` (typically an input wire). -/
  | input (idx : ℕ)
  /-- Rational constant `q`. -/
  | const (q : ℚ)
  /-- Sum of wires `i` and `j`. -/
  | add (i j : ℕ)
  /-- Difference of wires `i` and `j`. -/
  | sub (i j : ℕ)
  /-- Scalar multiplication of wire `i` by rational constant `q`. -/
  | scale (q : ℚ) (i : ℕ)
  /-- Minimum of wires `i` and `j`. -/
  | min (i j : ℕ)
  /-- Maximum of wires `i` and `j`. -/
  | max (i j : ℕ)
  deriving DecidableEq, Repr

/-- A linear arithmetic circuit with `numInputs` input wires, a sequential list of `gates`,
and a list of `outputs` wire indices. -/
@[ext]
structure LinearArithCircuit : Type where
  /-- Number of input wires. -/
  numInputs : ℕ
  /-- Sequential gate list; gate `k` may read any previously computed wire (out-of-range reads
  default to `0`). -/
  gates : List LinearGate
  /-- Output wire indices. -/
  outputs : List ℕ
  deriving DecidableEq, Repr

namespace LinearGate

/-- The denominator of the rational constant carried by a gate (`1` if none). -/
def constDen : LinearGate → ℕ
  | .const q => q.den
  | .scale q _ => q.den
  | _ => 1

/-- The numerator magnitude of the rational constant carried by a gate (`0` if none). -/
def constAbs : LinearGate → ℕ
  | .const q => q.num.natAbs
  | .scale q _ => q.num.natAbs
  | _ => 0

theorem constDen_pos (g : LinearGate) : 0 < g.constDen := by
  cases g <;> simp [constDen, Rat.den_pos]

/-- Canonical injective tuple representation `(tag, q, i, j)` of a `LinearGate`. -/
def toTuple : LinearGate → ℕ × ℚ × ℕ × ℕ
  | .input i => (0, 0, i, 0)
  | .const q => (1, q, 0, 0)
  | .add i j => (2, 0, i, j)
  | .sub i j => (3, 0, i, j)
  | .scale q i => (4, q, i, 0)
  | .min i j => (5, 0, i, j)
  | .max i j => (6, 0, i, j)

theorem toTuple_injective : Function.Injective toTuple := by
  intro g₁ g₂ h
  cases g₁ <;> cases g₂ <;> simp [toTuple] at h <;> simp_all

@[simp] theorem constDen_input (i : ℕ) : constDen (.input i) = 1 := by rfl
@[simp] theorem constDen_const (q : ℚ) : constDen (.const q) = q.den := by rfl
@[simp] theorem constDen_add (i j : ℕ) : constDen (.add i j) = 1 := by rfl
@[simp] theorem constDen_sub (i j : ℕ) : constDen (.sub i j) = 1 := by rfl
@[simp] theorem constDen_scale (q : ℚ) (i : ℕ) : constDen (.scale q i) = q.den := by rfl
@[simp] theorem constDen_min (i j : ℕ) : constDen (.min i j) = 1 := by rfl
@[simp] theorem constDen_max (i j : ℕ) : constDen (.max i j) = 1 := by rfl

@[simp] theorem constAbs_input (i : ℕ) : constAbs (.input i) = 0 := by rfl
@[simp] theorem constAbs_const (q : ℚ) : constAbs (.const q) = q.num.natAbs := by rfl
@[simp] theorem constAbs_add (i j : ℕ) : constAbs (.add i j) = 0 := by rfl
@[simp] theorem constAbs_sub (i j : ℕ) : constAbs (.sub i j) = 0 := by rfl
@[simp] theorem constAbs_scale (q : ℚ) (i : ℕ) : constAbs (.scale q i) = q.num.natAbs := by rfl
@[simp] theorem constAbs_min (i j : ℕ) : constAbs (.min i j) = 0 := by rfl
@[simp] theorem constAbs_max (i j : ℕ) : constAbs (.max i j) = 0 := by rfl

@[simp] theorem toTuple_input (i : ℕ) : toTuple (.input i) = (0, 0, i, 0) := by rfl
@[simp] theorem toTuple_const (q : ℚ) : toTuple (.const q) = (1, q, 0, 0) := by rfl
@[simp] theorem toTuple_add (i j : ℕ) : toTuple (.add i j) = (2, 0, i, j) := by rfl
@[simp] theorem toTuple_sub (i j : ℕ) : toTuple (.sub i j) = (3, 0, i, j) := by rfl
@[simp] theorem toTuple_scale (q : ℚ) (i : ℕ) : toTuple (.scale q i) = (4, q, i, 0) := by rfl
@[simp] theorem toTuple_min (i j : ℕ) : toTuple (.min i j) = (5, 0, i, j) := by rfl
@[simp] theorem toTuple_max (i j : ℕ) : toTuple (.max i j) = (6, 0, i, j) := by rfl

end LinearGate

/-- Binary encoding of a `LinearGate` via its canonical tuple `(tag, q, i, j)`. -/
def encLinearGate : LinearGate ↪ List Bool :=
  ⟨fun g => encPair encNat (encPair encRat (encPair encNat encNat)) g.toTuple,
    (encPair encNat (encPair encRat (encPair encNat encNat))).injective.comp
      LinearGate.toTuple_injective⟩

theorem encLinearGate_eq (g : LinearGate) :
    encLinearGate g = encPair encNat (encPair encRat (encPair encNat encNat)) g.toTuple := by
  rfl

/-- Binary encoding of a `LinearArithCircuit` as `(numInputs, gates, outputs)`. -/
def encLinearArithCircuit : LinearArithCircuit ↪ List Bool :=
  ⟨fun C => encPair encNat (encPair (encList encLinearGate) (encList encNat))
      (C.numInputs, C.gates, C.outputs),
    fun C₁ C₂ h => by
      have h' := (encPair encNat (encPair (encList encLinearGate) (encList encNat))).injective h
      cases C₁; cases C₂; simp_all⟩

theorem encLinearArithCircuit_eq (C : LinearArithCircuit) :
    encLinearArithCircuit C =
      encPair encNat (encPair (encList encLinearGate) (encList encNat))
        (C.numInputs, C.gates, C.outputs) := by
  rfl

/-- Evaluate a single `LinearGate` against the current wire values over any ordered field. -/
def evalGate {α : Type*} [Field α] [LinearOrder α]
    (vals : List α) : LinearGate → α
  | .input idx => vals.getD idx 0
  | .const q => (q : α)
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .sub i j => vals.getD i 0 - vals.getD j 0
  | .scale q i => (q : α) * vals.getD i 0
  | .min i j => Min.min (vals.getD i 0) (vals.getD j 0)
  | .max i j => Max.max (vals.getD i 0) (vals.getD j 0)

/-- Step function for sequential gate evaluation, appending the new gate value to `vals`. -/
def evalStep {α : Type*} [Field α] [LinearOrder α]
    (vals : List α) (g : LinearGate) : List α :=
  vals ++ [evalGate vals g]

/-- Evaluate all wires of `gates` starting from input wire values `x`. -/
def evalWires {α : Type*} [Field α] [LinearOrder α]
    (gates : List LinearGate) (x : List α) : List α :=
  gates.foldl evalStep x

/-- Evaluate the rational outputs of a linear arithmetic circuit on input vector `x`. -/
def evalRat (C : LinearArithCircuit) (x : List ℚ) : List ℚ :=
  let vals := evalWires C.gates (x.take C.numInputs)
  C.outputs.map fun o => vals.getD o 0

/-- Evaluate the real outputs of a linear arithmetic circuit on input vector `x`. -/
noncomputable def evalReal (C : LinearArithCircuit) (x : List ℝ) : List ℝ :=
  let vals := evalWires C.gates (x.take C.numInputs)
  C.outputs.map fun o => vals.getD o 0

section EvalAPI

variable {α : Type*} [Field α] [LinearOrder α]

@[simp]
theorem evalGate_input (vals : List α) (idx : ℕ) :
    evalGate vals (.input idx) = vals.getD idx 0 := by rfl

@[simp]
theorem evalGate_const (vals : List α) (q : ℚ) :
    evalGate vals (.const q) = (q : α) := by rfl

@[simp]
theorem evalGate_add (vals : List α) (i j : ℕ) :
    evalGate vals (.add i j) = vals.getD i 0 + vals.getD j 0 := by rfl

@[simp]
theorem evalGate_sub (vals : List α) (i j : ℕ) :
    evalGate vals (.sub i j) = vals.getD i 0 - vals.getD j 0 := by rfl

@[simp]
theorem evalGate_scale (vals : List α) (q : ℚ) (i : ℕ) :
    evalGate vals (.scale q i) = (q : α) * vals.getD i 0 := by rfl

@[simp]
theorem evalGate_min (vals : List α) (i j : ℕ) :
    evalGate vals (.min i j) = Min.min (vals.getD i 0) (vals.getD j 0) := by rfl

@[simp]
theorem evalGate_max (vals : List α) (i j : ℕ) :
    evalGate vals (.max i j) = Max.max (vals.getD i 0) (vals.getD j 0) := by rfl

theorem evalStep_eq (vals : List α) (g : LinearGate) :
    evalStep vals g = vals ++ [evalGate vals g] := by
  rfl

@[simp]
theorem evalWires_nil (x : List α) : evalWires ([] : List LinearGate) x = x := by
  rfl

@[simp]
theorem evalWires_cons (g : LinearGate) (gs : List LinearGate) (x : List α) :
    evalWires (g :: gs) x = evalWires gs (x ++ [evalGate x g]) := by
  rfl

theorem evalWires_append (gs₁ gs₂ : List LinearGate) (x : List α) :
    evalWires (gs₁ ++ gs₂) x = evalWires gs₂ (evalWires gs₁ x) := by
  exact List.foldl_append

@[simp]
theorem length_evalWires (gates : List LinearGate) (x : List α) :
    (evalWires gates x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [evalWires_cons, ih (x ++ [evalGate x g])]
    simp
    omega

theorem evalWires_getD_of_lt (gates : List LinearGate) (x : List α) {i : ℕ}
    (hi : i < x.length) :
    (evalWires gates x).getD i 0 = x.getD i 0 := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [evalWires_cons, ih (x ++ [evalGate x g]) (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem evalRat_eq (C : LinearArithCircuit) (x : List ℚ) :
    evalRat C x = C.outputs.map fun o => (evalWires C.gates (x.take C.numInputs)).getD o 0 := by
  rfl

theorem evalReal_eq (C : LinearArithCircuit) (x : List ℝ) :
    evalReal C x = C.outputs.map fun o => (evalWires C.gates (x.take C.numInputs)).getD o 0 := by
  rfl

@[simp]
theorem evalRat_length (C : LinearArithCircuit) (x : List ℚ) :
    (evalRat C x).length = C.outputs.length := by
  exact List.length_map _

@[simp]
theorem evalReal_length (C : LinearArithCircuit) (x : List ℝ) :
    (evalReal C x).length = C.outputs.length := by
  exact List.length_map _

end EvalAPI

private theorem list_getD_map_ratCast (l : List ℚ) (i : ℕ) :
    (l.map (fun q : ℚ => (q : ℝ))).getD i 0 = ((l.getD i 0 : ℚ) : ℝ) := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ k => simpa using ih k

private theorem evalGate_map_ratCast (vals : List ℚ) (g : LinearGate) :
    evalGate (vals.map (fun q : ℚ => (q : ℝ))) g = ((evalGate vals g : ℚ) : ℝ) := by
  cases g <;>
    simp only [evalGate, list_getD_map_ratCast, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_min, Rat.cast_max, Rat.cast_id]

private theorem evalWires_map_ratCast (gates : List LinearGate) (x : List ℚ) :
    evalWires gates (x.map (fun q : ℚ => (q : ℝ))) =
      (evalWires gates x).map (fun q : ℚ => (q : ℝ)) := by
  induction gates generalizing x with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons, evalStep]
    have hstep : x.map (fun q : ℚ => (q : ℝ)) ++ [evalGate (x.map (fun q : ℚ => (q : ℝ))) g] =
        (x ++ [evalGate x g]).map (fun q : ℚ => (q : ℝ)) := by
      simp [evalGate_map_ratCast]
    rw [hstep]
    exact ih (x ++ [evalGate x g])

/-- Real evaluation on rational inputs coincides with rational evaluation cast to `ℝ`. -/
theorem evalReal_eq_evalRat (C : LinearArithCircuit) (x : List ℚ) :
    evalReal C (x.map (fun q : ℚ => (q : ℝ))) = (evalRat C x).map (fun q : ℚ => (q : ℝ)) := by
  dsimp only [evalReal, evalRat]
  rw [← List.map_take, evalWires_map_ratCast, List.map_map]
  refine List.map_congr_left fun o _ => ?_
  exact list_getD_map_ratCast _ o

/-- Wire-level `ℓ∞`-Lipschitz bound step: `input` has bound `1`, `const` has `0`, `add`/`sub`
add bounds, `scale q` multiplies by `|q|`, and `min`/`max` take the maximum. -/
def lipschitzStep (bounds : List ℚ) : LinearGate → List ℚ
  | .input idx => bounds ++ [bounds.getD idx 0]
  | .const _ => bounds ++ [0]
  | .add i j => bounds ++ [bounds.getD i 0 + bounds.getD j 0]
  | .sub i j => bounds ++ [bounds.getD i 0 + bounds.getD j 0]
  | .scale q i => bounds ++ [|q| * bounds.getD i 0]
  | .min i j => bounds ++ [Max.max (bounds.getD i 0) (bounds.getD j 0)]
  | .max i j => bounds ++ [Max.max (bounds.getD i 0) (bounds.getD j 0)]

/-- Computable rational `ℓ∞`-Lipschitz bounds for all wires of `C`. -/
def wireLipschitzBounds (C : LinearArithCircuit) : List ℚ :=
  C.gates.foldl lipschitzStep (List.replicate C.numInputs (1 : ℚ))

/-- Computable rational `ℓ∞`-Lipschitz bound for output `k` (or `0` if out of range). -/
def outputLipschitzBound (C : LinearArithCircuit) (k : ℕ) : ℚ :=
  (wireLipschitzBounds C).getD (C.outputs.getD k 0) 0

@[simp]
theorem lipschitzStep_input (bs : List ℚ) (idx : ℕ) :
    lipschitzStep bs (.input idx) = bs ++ [bs.getD idx 0] := by rfl

@[simp]
theorem lipschitzStep_const (bs : List ℚ) (q : ℚ) :
    lipschitzStep bs (.const q) = bs ++ [0] := by rfl

@[simp]
theorem lipschitzStep_add (bs : List ℚ) (i j : ℕ) :
    lipschitzStep bs (.add i j) = bs ++ [bs.getD i 0 + bs.getD j 0] := by rfl

@[simp]
theorem lipschitzStep_sub (bs : List ℚ) (i j : ℕ) :
    lipschitzStep bs (.sub i j) = bs ++ [bs.getD i 0 + bs.getD j 0] := by rfl

@[simp]
theorem lipschitzStep_scale (bs : List ℚ) (q : ℚ) (i : ℕ) :
    lipschitzStep bs (.scale q i) = bs ++ [|q| * bs.getD i 0] := by rfl

@[simp]
theorem lipschitzStep_min (bs : List ℚ) (i j : ℕ) :
    lipschitzStep bs (.min i j) = bs ++ [Max.max (bs.getD i 0) (bs.getD j 0)] := by rfl

@[simp]
theorem lipschitzStep_max (bs : List ℚ) (i j : ℕ) :
    lipschitzStep bs (.max i j) = bs ++ [Max.max (bs.getD i 0) (bs.getD j 0)] := by rfl

theorem wireLipschitzBounds_eq (C : LinearArithCircuit) :
    wireLipschitzBounds C = C.gates.foldl lipschitzStep (List.replicate C.numInputs (1 : ℚ)) := by
  rfl

theorem outputLipschitzBound_eq (C : LinearArithCircuit) (k : ℕ) :
    outputLipschitzBound C k = (wireLipschitzBounds C).getD (C.outputs.getD k 0) 0 := by
  rfl

private theorem lipschitzStep_nonneg {bs : List ℚ} (hbs : ∀ i, 0 ≤ bs.getD i 0)
    (g : LinearGate) (i : ℕ) :
    0 ≤ (lipschitzStep bs g).getD i 0 := by
  have hget : ∀ (v : ℚ), 0 ≤ v → 0 ≤ (bs ++ [v]).getD i 0 := fun v hv => by
    by_cases hi : i < bs.length
    · have h : (bs ++ [v]).getD i 0 = bs.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      rw [h]; exact hbs i
    · rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with rfl | hgt
      · have h : (bs ++ [v]).getD bs.length 0 = v := by simp [List.getD_eq_getElem?_getD]
        rw [h]; exact hv
      · have h : (bs ++ [v]).getD i 0 = 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (bs ++ [v]).length ≤ i by
            simp; omega)]
        rw [h]
  cases g with
  | input idx => exact hget _ (hbs idx)
  | const _ => exact hget _ (le_refl 0)
  | add j k => exact hget _ (add_nonneg (hbs j) (hbs k))
  | sub j k => exact hget _ (add_nonneg (hbs j) (hbs k))
  | scale q j => exact hget _ (mul_nonneg (abs_nonneg q) (hbs j))
  | min j k => exact hget _ (le_max_of_le_left (hbs j))
  | max j k => exact hget _ (le_max_of_le_left (hbs j))

private theorem abs_min_sub_min_le (a b a' b' : ℝ) :
    |Min.min a b - Min.min a' b'| ≤ Max.max |a - a'| |b - b'| := by
  have ha := abs_le.mp (le_max_left |a - a'| |b - b'|)
  have hb := abs_le.mp (le_max_right |a - a'| |b - b'|)
  by_cases h : a ≤ b <;> by_cases h' : a' ≤ b'
  · rw [min_eq_left h, min_eq_left h', abs_le]; constructor <;> linarith
  · rw [min_eq_left h, min_eq_right (le_of_not_ge h'), abs_le]; constructor <;> linarith
  · rw [min_eq_right (le_of_not_ge h), min_eq_left h', abs_le]; constructor <;> linarith
  · rw [min_eq_right (le_of_not_ge h), min_eq_right (le_of_not_ge h'), abs_le]
    constructor <;> linarith

private theorem abs_max_sub_max_le (a b a' b' : ℝ) :
    |Max.max a b - Max.max a' b'| ≤ Max.max |a - a'| |b - b'| := by
  have h := abs_min_sub_min_le (-a) (-b) (-a') (-b')
  rw [min_neg_neg, min_neg_neg] at h
  simpa [sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm] using h

private theorem evalWires_lipschitz_aux (gates : List LinearGate) (x y : List ℝ) (bs : List ℚ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlen : x.length = bs.length) (hleny : y.length = bs.length)
    (hb_nonneg : ∀ i, 0 ≤ bs.getD i 0)
    (hxy : ∀ i, |x.getD i 0 - y.getD i 0| ≤ (bs.getD i 0 : ℝ) * δ) :
    ∀ i, |(evalWires gates x).getD i 0 - (evalWires gates y).getD i 0| ≤
      ((gates.foldl lipschitzStep bs).getD i 0 : ℝ) * δ := by
  induction gates generalizing x y bs with
  | nil => exact hxy
  | cons g gs ih =>
    simp only [evalWires_cons, List.foldl_cons]
    refine ih (x ++ [evalGate x g]) (y ++ [evalGate y g]) (lipschitzStep bs g) ?_ ?_ ?_ ?_
    · cases g <;> simp [hlen]
    · cases g <;> simp [hleny]
    · exact lipschitzStep_nonneg hb_nonneg g
    · intro i
      by_cases hi : i < bs.length
      · have hx' : (x ++ [evalGate x g]).getD i 0 = x.getD i 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hi)]
        have hy' : (y ++ [evalGate y g]).getD i 0 = y.getD i 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hleny ▸ hi)]
        have hb' : (lipschitzStep bs g).getD i 0 = bs.getD i 0 := by
          cases g <;> simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        rw [hx', hy', hb']
        exact hxy i
      · have hge : bs.length ≤ i := Nat.le_of_not_lt hi
        rcases eq_or_lt_of_le hge with rfl | hgt
        · have hx' : (x ++ [evalGate x g]).getD bs.length 0 = evalGate x g := by
            simp [List.getD_eq_getElem?_getD, ← hlen]
          have hy' : (y ++ [evalGate y g]).getD bs.length 0 = evalGate y g := by
            simp [List.getD_eq_getElem?_getD, ← hleny]
          rw [hx', hy']
          cases g with
          | input idx =>
            have hb' : (lipschitzStep bs (.input idx)).getD bs.length 0 = bs.getD idx 0 := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_input, evalGate_input]
            exact hxy idx
          | const q =>
            have hb' : (lipschitzStep bs (.const q)).getD bs.length 0 = 0 := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_const, evalGate_const]
            simp
          | add j k =>
            have hb' : (lipschitzStep bs (.add j k)).getD bs.length 0 =
                bs.getD j 0 + bs.getD k 0 := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_add, evalGate_add, Rat.cast_add, add_mul]
            have htri : |(x.getD j 0 + x.getD k 0) - (y.getD j 0 + y.getD k 0)| ≤
                |x.getD j 0 - y.getD j 0| + |x.getD k 0 - y.getD k 0| := by
              rw [show (x.getD j 0 + x.getD k 0) - (y.getD j 0 + y.getD k 0) =
                  (x.getD j 0 - y.getD j 0) + (x.getD k 0 - y.getD k 0) by ring]
              exact abs_add_le _ _
            linarith [hxy j, hxy k]
          | sub j k =>
            have hb' : (lipschitzStep bs (.sub j k)).getD bs.length 0 =
                bs.getD j 0 + bs.getD k 0 := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_sub, evalGate_sub, Rat.cast_add, add_mul]
            have htri : |(x.getD j 0 - x.getD k 0) - (y.getD j 0 - y.getD k 0)| ≤
                |x.getD j 0 - y.getD j 0| + |x.getD k 0 - y.getD k 0| := by
              rw [show (x.getD j 0 - x.getD k 0) - (y.getD j 0 - y.getD k 0) =
                  (x.getD j 0 - y.getD j 0) - (x.getD k 0 - y.getD k 0) by ring]
              exact abs_sub _ _
            linarith [hxy j, hxy k]
          | scale q j =>
            have hb' : (lipschitzStep bs (.scale q j)).getD bs.length 0 =
                |q| * bs.getD j 0 := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_scale, evalGate_scale, Rat.cast_mul, Rat.cast_abs, mul_assoc,
              ← mul_sub, abs_mul]
            exact mul_le_mul_of_nonneg_left (hxy j) (abs_nonneg _)
          | min j k =>
            have hb' : (lipschitzStep bs (.min j k)).getD bs.length 0 =
                Max.max (bs.getD j 0) (bs.getD k 0) := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_min, evalGate_min, Rat.cast_max]
            refine le_trans (abs_min_sub_min_le _ _ _ _) ?_
            rw [max_mul_of_nonneg _ _ hδ]
            exact max_le_max (hxy j) (hxy k)
          | max j k =>
            have hb' : (lipschitzStep bs (.max j k)).getD bs.length 0 =
                Max.max (bs.getD j 0) (bs.getD k 0) := by
              simp [List.getD_eq_getElem?_getD]
            rw [hb', evalGate_max, evalGate_max, Rat.cast_max]
            refine le_trans (abs_max_sub_max_le _ _ _ _) ?_
            rw [max_mul_of_nonneg _ _ hδ]
            exact max_le_max (hxy j) (hxy k)
        · have hx' : (x ++ [evalGate x g]).getD i 0 = 0 := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (show (x ++ [evalGate x g]).length ≤ i by simp; omega)]
          have hy' : (y ++ [evalGate y g]).getD i 0 = 0 := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (show (y ++ [evalGate y g]).length ≤ i by simp; omega)]
          have hb' : (lipschitzStep bs g).getD i 0 = 0 := by
            have hlen_step : (lipschitzStep bs g).length = bs.length + 1 := by
              cases g <;> simp
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            rfl
          rw [hx', hy', hb']
          simp

/-- **Global Lipschitz continuity of linear arithmetic circuits**: for any `x, y : List ℝ` of
length `C.numInputs` with `|x_i - y_i| ≤ δ` (`δ ≥ 0`), every output wire `k` satisfies
`|(evalReal C x)_k - (evalReal C y)_k| ≤ outputLipschitzBound C k * δ`. -/
theorem evalReal_lipschitz (C : LinearArithCircuit) {x y : List ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hxlen : x.length = C.numInputs) (hylen : y.length = C.numInputs)
    (hxy : ∀ i, |x.getD i 0 - y.getD i 0| ≤ δ) (k : ℕ) :
    |(evalReal C x).getD k 0 - (evalReal C y).getD k 0| ≤
      (outputLipschitzBound C k : ℝ) * δ := by
  have htake_x : x.take C.numInputs = x := List.take_of_length_le (le_of_eq hxlen)
  have htake_y : y.take C.numInputs = y := List.take_of_length_le (le_of_eq hylen)
  have hrep_nonneg : ∀ i, 0 ≤ (List.replicate C.numInputs (1 : ℚ)).getD i 0 := fun i => by
    by_cases hi : i < C.numInputs
    · simp [List.getD_eq_getElem?_getD, hi]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  have hmain := evalWires_lipschitz_aux C.gates x y (List.replicate C.numInputs (1 : ℚ)) hδ
    (by simp [hxlen]) (by simp [hylen]) hrep_nonneg
    (fun i => by
      by_cases hi : i < C.numInputs
      · simpa [List.getD_eq_getElem?_getD, hi] using hxy i
      · have hge : C.numInputs ≤ i := Nat.le_of_not_lt hi
        have hx0 : x.getD i 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hxlen.symm ▸ hge)]; rfl
        have hy0 : y.getD i 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hylen.symm ▸ hge)]; rfl
        have hr0 : (List.replicate C.numInputs (1 : ℚ)).getD i 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
        rw [hx0, hy0, hr0]
        simp)
  by_cases hk : k < C.outputs.length
  · have hget : ∀ (l : List ℝ), (C.outputs.map fun o => l.getD o 0).getD k 0 =
        l.getD (C.outputs.getD k 0) 0 := fun l => by
      simp [List.getD_eq_getElem?_getD, hk]
    simpa only [evalReal, htake_x, htake_y, hget, outputLipschitzBound, wireLipschitzBounds] using
      hmain (C.outputs.getD k 0)
  · have hge : C.outputs.length ≤ k := Nat.le_of_not_lt hk
    have h1 : (evalReal C x).getD k 0 = 0 := by
      rw [evalReal_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    have h2 : (evalReal C y).getD k 0 = 0 := by
      rw [evalReal_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    rw [h1, h2, sub_self, abs_zero]
    have hnonneg : ∀ (gates : List LinearGate) (bs : List ℚ),
        (∀ i, 0 ≤ bs.getD i 0) → ∀ i, 0 ≤ (gates.foldl lipschitzStep bs).getD i 0 := by
      intro gates
      induction gates with
      | nil => intro bs h; exact h
      | cons g gs ih =>
        intro bs hbs
        exact ih _ (lipschitzStep_nonneg hbs g)
    have h0 : 0 ≤ (outputLipschitzBound C k : ℝ) := by
      exact_mod_cast hnonneg C.gates (List.replicate C.numInputs (1 : ℚ)) hrep_nonneg _
    exact mul_nonneg h0 hδ

section PolyTime

attribute [local irreducible] encRat encNat encUnary encLinearGate encLinearArithCircuit

private theorem rat_den_dvd_of_add {a b : ℚ} {D : ℕ} (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a + b).den ∣ D := by
  obtain ⟨k₁, hk₁⟩ := ha
  obtain ⟨k₂, hk₂⟩ := hb
  have hmul : (a + b) * (D : ℚ) = ((a.num * k₁ + b.num * k₂ : ℤ) : ℚ) := by
    rw [add_mul]
    have ha' : a * (D : ℚ) = ((a.num * k₁ : ℤ) : ℚ) := by
      rw [hk₁, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]
      push_cast
      ring
    have hb' : b * (D : ℚ) = ((b.num * k₂ : ℤ) : ℚ) := by
      rw [hk₂, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]
      push_cast
      ring
    rw [ha', hb']
    push_cast
    ring
  by_cases hD0 : D = 0
  · simp [hD0]
  · have hDpos : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD0
    have heq : a + b = ((a.num * k₁ + b.num * k₂ : ℤ) : ℚ) / (D : ℚ) :=
      eq_div_of_mul_eq hDpos hmul
    rw [heq, ← Int.cast_natCast D, ← Rat.divInt_eq_div]
    exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)

private theorem rat_den_dvd_of_sub {a b : ℚ} {D : ℕ} (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a - b).den ∣ D := by
  rw [sub_eq_add_neg]
  exact rat_den_dvd_of_add ha (by simpa [Rat.den_neg_eq_den] using hb)

private theorem rat_den_dvd_of_mul {a b : ℚ} {D₁ D₂ : ℕ} (ha : a.den ∣ D₁) (hb : b.den ∣ D₂) :
    (a * b).den ∣ D₁ * D₂ := by
  exact dvd_trans (Rat.mul_den_dvd a b) (Nat.mul_dvd_mul ha hb)

private theorem rat_abs_mul_den (q : ℚ) : |q| * (q.den : ℚ) = (q.num.natAbs : ℚ) := by
  have h1 : |(q.num : ℚ)| = (q.num.natAbs : ℚ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have h2 : |(q.den : ℚ)| = (q.den : ℚ) := abs_of_nonneg (Nat.cast_nonneg _)
  nth_rw 1 [← Rat.num_div_den q]
  rw [abs_div, h1, h2, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr q.den_nz)]

private theorem rat_abs_le_num_natAbs (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  have hden : (1 : ℚ) ≤ (q.den : ℚ) := by exact_mod_cast q.pos
  have hnum : |q| * (q.den : ℚ) = (q.num.natAbs : ℚ) := rat_abs_mul_den q
  nlinarith [abs_nonneg q]

private theorem evalWires_rat_bounds_aux (gates : List LinearGate) (x : List ℚ)
    {D₀ A₀ : ℕ} (hA₀ : 0 < A₀)
    (hx : ∀ q ∈ x, q.den ∣ D₀ ∧ |q| ≤ (A₀ : ℚ)) :
    ∀ v ∈ evalWires gates x,
      v.den ∣ D₀ * (gates.map LinearGate.constDen).prod ∧
      |v| ≤ ((A₀ * (gates.map (fun g => g.constAbs + 2)).prod : ℕ) : ℚ) := by
  induction gates generalizing x D₀ A₀ with
  | nil =>
    intro v hv
    simpa [evalWires] using hx v hv
  | cons g gs ih =>
    intro v hv
    simp only [evalWires, List.foldl_cons, evalStep] at hv
    have hgetD : ∀ i, (x.getD i 0).den ∣ D₀ ∧ |x.getD i 0| ≤ (A₀ : ℚ) := by
      intro i
      by_cases hi : i < x.length
      · have hmem : x.getD i 0 ∈ x := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
          exact List.getElem_mem hi
        exact hx _ hmem
      · have h0 : x.getD i 0 = 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
        rw [h0]
        exact ⟨one_dvd _, by simp⟩
    have hg_den : (evalGate x g).den ∣ D₀ * g.constDen := by
      cases g with
      | input idx => simpa [evalGate, LinearGate.constDen] using (hgetD idx).1
      | const q => simp [evalGate, LinearGate.constDen]
      | add i j =>
        simpa [evalGate, LinearGate.constDen] using
          rat_den_dvd_of_add (hgetD i).1 (hgetD j).1
      | sub i j =>
        simpa [evalGate, LinearGate.constDen] using
          rat_den_dvd_of_sub (hgetD i).1 (hgetD j).1
      | scale q i =>
        simpa [evalGate, LinearGate.constDen, mul_comm] using
          rat_den_dvd_of_mul (dvd_refl q.den) (hgetD i).1
      | min i j =>
        simp only [evalGate, LinearGate.constDen, mul_one]
        rcases min_choice (x.getD i 0) (x.getD j 0) with h | h <;> rw [h]
        · exact (hgetD i).1
        · exact (hgetD j).1
      | max i j =>
        simp only [evalGate, LinearGate.constDen, mul_one]
        rcases max_choice (x.getD i 0) (x.getD j 0) with h | h <;> rw [h]
        · exact (hgetD i).1
        · exact (hgetD j).1
    have hg_abs : |evalGate x g| ≤ ((A₀ * (g.constAbs + 2) : ℕ) : ℚ) := by
      have hA1 : (1 : ℚ) ≤ (A₀ : ℚ) := by exact_mod_cast hA₀
      cases g with
      | input idx =>
        simp only [evalGate, LinearGate.constAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_zero,
          Nat.cast_ofNat]
        linarith [(hgetD idx).2, abs_nonneg (x.getD idx 0)]
      | const q =>
        simp only [evalGate, LinearGate.constAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
          Rat.cast_id]
        have hq := rat_abs_le_num_natAbs q
        nlinarith
      | add i j =>
        simp only [evalGate, LinearGate.constAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_zero,
          Nat.cast_ofNat]
        have h1 := (hgetD i).2; have h2 := (hgetD j).2
        linarith [abs_add_le (x.getD i 0) (x.getD j 0)]
      | sub i j =>
        simp only [evalGate, LinearGate.constAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_zero,
          Nat.cast_ofNat]
        have h1 := (hgetD i).2; have h2 := (hgetD j).2
        linarith [abs_sub (x.getD i 0) (x.getD j 0)]
      | scale q i =>
        simp only [evalGate, LinearGate.constAbs, abs_mul, Nat.cast_mul, Nat.cast_add,
          Nat.cast_ofNat, Rat.cast_id]
        have h1 := (hgetD i).2; have hq := rat_abs_le_num_natAbs q
        have hq0 : (0 : ℚ) ≤ |q| := abs_nonneg q
        nlinarith
      | min i j =>
        simp only [evalGate, LinearGate.constAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_zero,
          Nat.cast_ofNat]
        rcases min_choice (x.getD i 0) (x.getD j 0) with h | h <;> rw [h]
        · linarith [(hgetD i).2, abs_nonneg (x.getD i 0)]
        · linarith [(hgetD j).2, abs_nonneg (x.getD j 0)]
      | max i j =>
        simp only [evalGate, LinearGate.constAbs, Nat.cast_mul, Nat.cast_add, Nat.cast_zero,
          Nat.cast_ofNat]
        rcases max_choice (x.getD i 0) (x.getD j 0) with h | h <;> rw [h]
        · linarith [(hgetD i).2, abs_nonneg (x.getD i 0)]
        · linarith [(hgetD j).2, abs_nonneg (x.getD j 0)]
    have hx' : ∀ q ∈ x ++ [evalGate x g],
        q.den ∣ D₀ * g.constDen ∧ |q| ≤ ((A₀ * (g.constAbs + 2) : ℕ) : ℚ) := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · refine ⟨dvd_mul_of_dvd_left (hx q hq).1 _, ?_⟩
        calc |q| ≤ (A₀ : ℚ) := (hx q hq).2
          _ ≤ ((A₀ * (g.constAbs + 2) : ℕ) : ℚ) := by
            push_cast
            have : (1 : ℚ) ≤ (g.constAbs : ℚ) + 2 := by
              linarith [Nat.cast_nonneg (α := ℚ) g.constAbs]
            nlinarith
      · rw [List.mem_singleton.mp hq]
        exact ⟨hg_den, hg_abs⟩
    have hres := ih (x ++ [evalGate x g]) (Nat.mul_pos hA₀ (by omega)) hx' v hv
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using hres

private theorem length_encLinearGate_const_bounds (g : LinearGate) :
    g.constDen.size ≤ (encLinearGate g).length ∧
      (g.constAbs + 2).size ≤ (encLinearGate g).length + 3 := by
  have hrat_le : ∀ q : ℚ, (encRat q).length ≤ (encLinearGate g).length →
      q.den.size ≤ (encLinearGate g).length ∧
        (q.num.natAbs + 2).size ≤ (encLinearGate g).length + 3 := by
    intro q hq
    have hlen := length_encRat q
    have hsz : (q.num.natAbs + 2).size ≤ q.num.natAbs.size + 2 := by
      by_cases h0 : q.num.natAbs = 0
      · rw [h0]; decide
      · have hpos : 1 ≤ q.num.natAbs.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
        have h2 : (2 : ℕ).size = 2 := by decide
        have := Nat.size_add_le_max q.num.natAbs 2
        omega
    omega
  have hmid : (encRat g.toTuple.2.1).length ≤ (encLinearGate g).length := by
    rw [encLinearGate_eq]
    have h1 := length_le_encPair_right encNat (encPair encRat (encPair encNat encNat)) g.toTuple
    have h2 := length_le_encPair_left encRat (encPair encNat encNat) g.toTuple.2
    exact h2.trans h1
  have hpos : 4 ≤ (encLinearGate g).length := (four_le_length_encRat _).trans hmid
  have h0 : (1 : ℕ).size = 1 := by decide
  have h2 : (2 : ℕ).size = 2 := by decide
  cases g with
  | const q =>
    simpa [LinearGate.constDen, LinearGate.constAbs, LinearGate.toTuple] using hrat_le q hmid
  | scale q _ =>
    simpa [LinearGate.constDen, LinearGate.constAbs, LinearGate.toTuple] using hrat_le q hmid
  | input _ => simp only [LinearGate.constDen, LinearGate.constAbs, zero_add]; omega
  | add _ _ => simp only [LinearGate.constDen, LinearGate.constAbs, zero_add]; omega
  | sub _ _ => simp only [LinearGate.constDen, LinearGate.constAbs, zero_add]; omega
  | min _ _ => simp only [LinearGate.constDen, LinearGate.constAbs, zero_add]; omega
  | max _ _ => simp only [LinearGate.constDen, LinearGate.constAbs, zero_add]; omega

private theorem nat_size_prod_le (l : List ℕ) : l.prod.size ≤ (l.map Nat.size).sum + 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hmul := Nat.size_mul_le a t.prod
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    omega

private theorem evalGate_polyTime :
    ComputableInPolyTime (fun p : List ℚ × LinearGate => evalGate p.1 p.2)
      (encPair (encList encRat) encLinearGate) encRat := by
  have htuple : ComputableInPolyTime (fun p : List ℚ × LinearGate => (p.1, p.2.toTuple))
      (encPair (encList encRat) encLinearGate)
      (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat)))) :=
    ComputableInPolyTime.of_eq fun p => by simp [encPair, encLinearGate_eq]
  let evalT : List ℚ × (ℕ × ℚ × ℕ × ℕ) → ℚ := fun p =>
    let vals := p.1
    let tag := p.2.1
    let q := p.2.2.1
    let i := p.2.2.2.1
    let j := p.2.2.2.2
    let vi := vals.getD i 0
    let vj := vals.getD j 0
    if decide (tag = 0) then vi
    else if decide (tag = 1) then q
    else if decide (tag = 2) then vi + vj
    else if decide (tag = 3) then vi - vj
    else if decide (tag = 4) then q * vi
    else if decide (tag = 5) then (if decide (vi ≤ vj) then vi else vj)
    else (if decide (vi ≤ vj) then vj else vi)
  have hevalT : ComputableInPolyTime evalT
      (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
      encRat := by
    dsimp only [evalT]
    have hvals : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.1)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        (encList encRat) := by fun_prop
    have htag : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.2.1)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encNat := by fun_prop
    have hq : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.2.2.1)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encRat := by fun_prop
    have hi : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.2.2.2.1)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encNat := by fun_prop
    have hj : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.2.2.2.2)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encNat := by fun_prop
    have hvi : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.1.getD p.2.2.2.1 0)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encRat := listGetD_binary (encA := encRat) 0 hvals hi
    have hvj : ComputableInPolyTime (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) => p.1.getD p.2.2.2.2 0)
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encRat := listGetD_binary (encA := encRat) 0 hvals hj
    have hle : ComputableInPolyTime
        (fun p : List ℚ × (ℕ × ℚ × ℕ × ℕ) =>
          decide (p.1.getD p.2.2.2.1 0 ≤ p.1.getD p.2.2.2.2 0))
        (encPair (encList encRat) (encPair encNat (encPair encRat (encPair encNat encNat))))
        encBool := rat_le' hvi hvj
    have hmin := hle.ite hvi hvj
    have hmax := hle.ite hvj hvi
    have h5 := (htag.decide_eq' (const 5)).ite hmin hmax
    have h4 := (htag.decide_eq' (const 4)).ite (rat_mul' hq hvi) h5
    have h3 := (htag.decide_eq' (const 3)).ite (rat_sub' hvi hvj) h4
    have h2 := (htag.decide_eq' (const 2)).ite (rat_add' hvi hvj) h3
    have h1 := (htag.decide_eq' (const 1)).ite hq h2
    exact (htag.decide_eq' (const 0)).ite hvi h1
  refine (hevalT.comp htuple).of_enc_eq fun p => congrArg encRat ?_
  rcases p with ⟨vals, g⟩
  cases g <;> simp [evalT, evalGate, LinearGate.toTuple, min_def, max_def]

private theorem evalWires_polyTime :
    ComputableInPolyTime (fun p : List LinearGate × List ℚ => evalWires p.1 p.2)
      (encPair (encList encLinearGate) (encList encRat)) (encList encRat) := by
  have hstep : ComputableInPolyTime (fun p : List ℚ × LinearGate => evalStep p.1 p.2)
      (encPair (encList encRat) encLinearGate) (encList encRat) := by
    have h1 : ComputableInPolyTime (fun p : List ℚ × LinearGate => p.1)
        (encPair (encList encRat) encLinearGate) (encList encRat) :=
      fst (encList encRat) encLinearGate
    have h2 : ComputableInPolyTime (fun p : List ℚ × LinearGate => [evalGate p.1 p.2])
        (encPair (encList encRat) encLinearGate) (encList encRat) :=
      (cons encRat).comp (evalGate_polyTime.prod (const []))
    exact (listAppend encRat).comp (h1.prod h2)
  have hbound : PolyBounded
      (fun p : List LinearGate × List ℚ =>
        (encPair (encList encLinearGate) (encList encRat) p).length)
      (fun p : List LinearGate × List ℚ =>
        let L := (encPair (encList encLinearGate) (encList encRat) p).length
        (L + 1) * (2 * (18 * L + 60) + 1)) := by
    refine PolyBounded.of_forall_le 1000 2 fun p => ?_
    set L := (encPair (encList encLinearGate) (encList encRat) p).length
    nlinarith
  refine foldl' (list := Prod.fst) (init := Prod.snd) (step := evalStep)
    (fst (encList encLinearGate) (encList encRat))
    (snd (encList encLinearGate) (encList encRat)) hstep hbound ?_
  intro ⟨gates, x⟩ i hi
  set L := (encPair (encList encLinearGate) (encList encRat) (gates, x)).length
  have hLgates : (encList encLinearGate gates).length ≤ L :=
    length_le_encPair_left (encList encLinearGate) (encList encRat) (gates, x)
  have hLx : (encList encRat x).length ≤ L :=
    length_le_encPair_right (encList encLinearGate) (encList encRat) (gates, x)
  set gs := gates.take i
  have hgs_len : gs.length ≤ gates.length := (List.length_take_le i gates).trans hi
  have hlen_wires : (evalWires gs x).length ≤ L := by
    rw [length_evalWires]
    have hx_le : x.length ≤ (encList encRat x).length :=
      SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) x
    have hg_le : gates.length ≤ (encList encLinearGate gates).length :=
      SizedListEncoding.length_le (encA := encLinearGate) (encL := encList encLinearGate) gates
    have hpair : L = 2 * (encList encLinearGate gates).length + 1 + (encList encRat x).length := by
      simp [L, length_encPair]
    omega
  -- Now bound `(encRat v).length ≤ 18 * L + 60` for every `v ∈ evalWires gs x`.
  set D₀ : ℕ := (x.map (·.den)).prod
  set A₀ : ℕ := (x.map (fun q : ℚ => q.num.natAbs)).sum + 1
  have hD₀_pos : 0 < D₀ :=
    List.prod_pos (by intro d hd; rcases List.mem_map.mp hd with ⟨q, _, rfl⟩; exact q.pos)
  have hD_pos : 0 < D₀ * (gs.map LinearGate.constDen).prod :=
    Nat.mul_pos hD₀_pos (List.prod_pos (by
      intro d hd; rcases List.mem_map.mp hd with ⟨g, _, rfl⟩; exact g.constDen_pos))
  have hD_size : (D₀ * (gs.map LinearGate.constDen).prod).size ≤ 2 * L + 2 := by
    have h1 := Nat.size_mul_le D₀ (gs.map LinearGate.constDen).prod
    have hD₀_sz : D₀.size ≤ (encList encRat x).length + 1 := by
      have hprod := nat_size_prod_le (x.map (·.den))
      have hsum_all : ∀ l : List ℚ,
          ((l.map (·.den)).map Nat.size).sum ≤ (encList encRat l).length := by
        intro l
        induction l with
        | nil => simp
        | cons q t ih =>
          have hq : q.den.size ≤ (encRat q).length := by rw [length_encRat]; omega
          simp only [List.map_cons, List.sum_cons, encList_cons, List.length_append, length_frame]
          omega
      have hsum := hsum_all x
      dsimp only [D₀]
      omega
    have hDg_sz : ((gs.map LinearGate.constDen).prod).size ≤
      (encList encLinearGate gates).length + 1 := by
      have hprod := nat_size_prod_le (gs.map LinearGate.constDen)
      have hsub : (encList encLinearGate gs).length ≤ (encList encLinearGate gates).length :=
        length_encList_sublist encLinearGate (List.take_sublist i gates)
      have hsum_all : ∀ l : List LinearGate,
          ((l.map LinearGate.constDen).map Nat.size).sum ≤ (encList encLinearGate l).length := by
        intro l
        induction l with
        | nil => simp
        | cons g t ih =>
          have hg := (length_encLinearGate_const_bounds g).1
          simp only [List.map_cons, List.sum_cons, encList_cons, List.length_append, length_frame]
          omega
      have hsum := hsum_all gs
      omega
    omega
  have hA_size : (A₀ * (gs.map (fun g : LinearGate => g.constAbs + 2)).prod).size ≤ 6 * L + 6 := by
    have h1 := Nat.size_mul_le A₀ (gs.map (fun g : LinearGate => g.constAbs + 2)).prod
    have hA₀_sz : A₀.size ≤ (encList encRat x).length + 2 := by
      have hsum_le : ((x.map fun q : ℚ => q.num.natAbs).sum).size ≤ (encList encRat x).length := by
        have hsz : ∀ l : List ℚ, ((l.map fun q : ℚ => q.num.natAbs).sum).size ≤
          (encList encRat l).length := by
          intro l
          induction l with
          | nil => simp
          | cons q t ih =>
            have hadd := Nat.size_add_le_max q.num.natAbs (t.map fun r : ℚ => r.num.natAbs).sum
            have hq : q.num.natAbs.size ≤ (encRat q).length := by rw [length_encRat]; omega
            simp only [List.map_cons, List.sum_cons, encList_cons, List.length_append, length_frame]
            omega
        exact hsz x
      have hadd := Nat.size_add_le_max ((x.map fun q : ℚ => q.num.natAbs).sum) 1
      have h1sz : (1 : ℕ).size = 1 := by decide
      dsimp only [A₀]
      omega
    have hAg_sz : ((gs.map (fun g : LinearGate => g.constAbs + 2)).prod).size ≤
      4 * (encList encLinearGate gates).length + 2 := by
      have hprod := nat_size_prod_le (gs.map (fun g : LinearGate => g.constAbs + 2))
      have hsub : (encList encLinearGate gs).length ≤ (encList encLinearGate gates).length :=
        length_encList_sublist encLinearGate (List.take_sublist i gates)
      have hsum_all : ∀ l : List LinearGate,
          ((l.map (fun g : LinearGate => g.constAbs + 2)).map Nat.size).sum ≤
            4 * (encList encLinearGate l).length := by
        intro l
        induction l with
        | nil => simp
        | cons g t ih =>
          have hg := (length_encLinearGate_const_bounds g).2
          have hpos : 1 ≤ (encLinearGate g).length := by
            have := (length_encLinearGate_const_bounds g).1
            have := Nat.size_pos.mpr g.constDen_pos
            omega
          simp only [List.map_cons, List.sum_cons, encList_cons, List.length_append, length_frame]
          omega
      have hsum := hsum_all gs
      omega
    omega
  have hval_bound : ∀ v ∈ evalWires gs x, (encRat v).length ≤ 18 * L + 60 := by
    intro v hv
    obtain ⟨hdvd, habs⟩ := evalWires_rat_bounds_aux gs x (Nat.succ_pos _)
      (fun q hq => ⟨List.dvd_prod (List.mem_map_of_mem hq), by
        calc |q| ≤ (q.num.natAbs : ℚ) := rat_abs_le_num_natAbs q
          _ ≤ (A₀ : ℚ) := by
            have hle : q.num.natAbs ≤ A₀ :=
              Nat.le_succ_of_le (List.le_sum_of_mem
                (List.mem_map_of_mem (f := fun r : ℚ => r.num.natAbs) hq))
            exact_mod_cast hle⟩) v hv
    set D := D₀ * (gs.map LinearGate.constDen).prod
    set A := A₀ * (gs.map (fun g : LinearGate => g.constAbs + 2)).prod
    have hden_le : v.den ≤ D := Nat.le_of_dvd hD_pos hdvd
    have hnum_le : v.num.natAbs ≤ A * D := by
      have hmul : (v.num.natAbs : ℚ) ≤ (A : ℚ) * (v.den : ℚ) := by
        have h1 : (v.num.natAbs : ℚ) = |v| * (v.den : ℚ) := (rat_abs_mul_den v).symm
        rw [h1]
        exact mul_le_mul_of_nonneg_right habs (Nat.cast_nonneg _)
      have h2 : (v.num.natAbs : ℚ) ≤ ((A * D : ℕ) : ℚ) := by
        push_cast
        exact hmul.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hden_le) (Nat.cast_nonneg _))
      exact_mod_cast h2
    have hlen_v := length_encRat_le v hnum_le hden_le
    have hAD_sz := Nat.size_mul_le A D
    omega
  have hlist_le := length_encList_le encRat (evalWires gs x) hval_bound
  have hmul_le : (evalWires gs x).length * (2 * (18 * L + 60) + 1) ≤
      (L + 1) * (2 * (18 * L + 60) + 1) :=
    Nat.mul_le_mul_right _ (hlen_wires.trans (Nat.le_succ L))
  exact hlist_le.trans hmul_le

/-- **Polynomial-time rational evaluation of linear arithmetic circuits**: evaluating a
`LinearArithCircuit` on a rational input list is computable in polynomial time under
`encLinearArithCircuit` and `encRat`. -/
@[fun_prop]
theorem computableInPolyTime_evalRat :
    ComputableInPolyTime (fun p : LinearArithCircuit × List ℚ => evalRat p.1 p.2)
      (encPair encLinearArithCircuit (encList encRat)) (encList encRat) := by
  have hC_proj : ComputableInPolyTime
      (fun C : LinearArithCircuit => (C.numInputs, C.gates, C.outputs))
      encLinearArithCircuit
      (encPair encNat (encPair (encList encLinearGate) (encList encNat))) :=
    ComputableInPolyTime.of_eq fun C => (encLinearArithCircuit_eq C).symm
  have hC_tuple : ComputableInPolyTime
      (fun p : LinearArithCircuit × List ℚ => (p.1.numInputs, p.1.gates, p.1.outputs))
      (encPair encLinearArithCircuit (encList encRat))
      (encPair encNat (encPair (encList encLinearGate) (encList encNat))) :=
    hC_proj.comp (fst encLinearArithCircuit (encList encRat))
  have hnum : ComputableInPolyTime (fun p : LinearArithCircuit × List ℚ => p.1.numInputs)
      (encPair encLinearArithCircuit (encList encRat)) encNat := hC_tuple.fst'
  have hgates : ComputableInPolyTime (fun p : LinearArithCircuit × List ℚ => p.1.gates)
      (encPair encLinearArithCircuit (encList encRat)) (encList encLinearGate) :=
    hC_tuple.snd'.fst'
  have houts : ComputableInPolyTime (fun p : LinearArithCircuit × List ℚ => p.1.outputs)
      (encPair encLinearArithCircuit (encList encRat)) (encList encNat) :=
    hC_tuple.snd'.snd'
  have hx : ComputableInPolyTime (fun p : LinearArithCircuit × List ℚ => p.2)
      (encPair encLinearArithCircuit (encList encRat)) (encList encRat) :=
    snd encLinearArithCircuit (encList encRat)
  -- Compute `x.take C.numInputs` via `zipIdx` and `filter` (avoiding binary-to-unary conversion).
  have htake : ComputableInPolyTime
      (fun p : LinearArithCircuit × List ℚ => p.2.take p.1.numInputs)
      (encPair encLinearArithCircuit (encList encRat)) (encList encRat) := by
    have hzip : ComputableInPolyTime
        (fun p : LinearArithCircuit × List ℚ => p.2.zipIdx)
        (encPair encLinearArithCircuit (encList encRat))
        (encList (encPair encRat encUnary)) := (zipIdx encRat).comp hx
    let encIn := encPair encLinearArithCircuit (encList encRat)
    have hfilt : ComputableInPolyTime
        (fun p : LinearArithCircuit × List ℚ =>
          p.2.zipIdx.filter fun q => decide (q.2 < p.1.numInputs))
        encIn (encList (encPair encRat encUnary)) :=
      filterWithInput hzip
        (binary_lt'
          (unary_to_binary.comp ((snd encRat encUnary).comp (snd encIn (encPair encRat encUnary))))
          (hnum.comp (fst encIn (encPair encRat encUnary))))
    have hmap : ComputableInPolyTime
        (fun p : LinearArithCircuit × List ℚ =>
          (p.2.zipIdx.filter fun q => decide (q.2 < p.1.numInputs)).map Prod.fst)
        encIn (encList encRat) :=
      mapWith ((fst encRat encUnary).comp (snd encUnit (encPair encRat encUnary)))
        (const ()) hfilt
    refine hmap.of_enc_eq fun p => congrArg (encList encRat) ?_
    -- `((l.zipIdx).filter (·.2 < n)).map Prod.fst = l.take n`!
    have hlem : ∀ (l : List ℚ) (k n : ℕ),
        ((l.zipIdx k).filter (fun q => decide (q.2 < n))).map Prod.fst = l.take (n - k) := by
      have hge_zip : ∀ (l : List ℚ) (m : ℕ) (q : ℚ × ℕ), q ∈ l.zipIdx m → m ≤ q.2 := by
        intro l
        induction l with
        | nil => intro m q hq; simp at hq
        | cons a t ih =>
          intro m q hq
          rw [List.zipIdx_cons, List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact le_refl m
          · exact (Nat.le_succ m).trans (ih (m + 1) q hq)
      intro l
      induction l with
      | nil => intro k n; simp
      | cons a t ih =>
        intro k n
        by_cases hkn : k < n
        · have hsub : n - k = (n - (k + 1)) + 1 := by omega
          simp only [List.zipIdx_cons, List.filter_cons, hkn, decide_true, ↓reduceIte,
            List.map_cons, hsub, List.take_succ_cons]
          congr 1
          exact ih (k + 1) n
        · have hsub : n - k = 0 := by omega
          have hfalse : ∀ q ∈ t.zipIdx (k + 1), ¬ (q.2 < n) := by
            intro q hq
            have := hge_zip t (k + 1) q hq
            omega
          rw [hsub, List.take_zero]
          simp only [List.zipIdx_cons, List.filter_cons, hkn, decide_false, Bool.false_eq_true,
            ↓reduceIte, List.map_eq_nil_iff, List.filter_eq_nil_iff]
          intro q hq
          simp [hfalse q hq]
    simpa [List.zipIdx] using (hlem p.2 0 p.1.numInputs).symm
  have hwires : ComputableInPolyTime
      (fun p : LinearArithCircuit × List ℚ => evalWires p.1.gates (p.2.take p.1.numInputs))
      (encPair encLinearArithCircuit (encList encRat)) (encList encRat) :=
    evalWires_polyTime.comp (hgates.prod htake)
  exact mapWith
    (listGetD_binary (encA := encRat) 0 (fst (encList encRat) encNat) (snd (encList encRat) encNat))
    hwires houts

end PolyTime

end CslibFrontier.Computability.Circuit

