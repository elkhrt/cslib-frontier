/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.Circuit
public import Mathlib.Algebra.FreeAlgebra

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

/-!
# Fan-in 2 Noncommutative Arithmetic Circuits with Weighted Edges

This module formalizes the fan-in 2 noncommutative arithmetic circuit model of
weighted fan-in 2 DAG circuits with scalar-weighted edges,
syntactic degree, gate depth, in-place normalization eliminating syntactic-degree-`0` children of
product gates without increasing circuit size, variable-dependence leaf bounds, and the canonical
embedding from `Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature F) m 1`.

## Main definitions

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.GateKind`: node labels (constant leaf, variable
  leaf, weighted sum
  gate, weighted product gate) referencing only earlier vertices in topological order.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit`: fan-in 2 noncommutative
  arithmetic circuit with
  vertex count `size`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.evalGate`, `NoncommCircuit.eval`:
  polynomial computed
  at each gate and at the designated output.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.synDeg`,
  `NoncommCircuit.circuitSynDeg`: syntactic
  degree of a gate and of the circuit.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.gateDepth`: longest path length
  from a leaf.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.IsNormalized`,
  `NoncommCircuit.normalize`:
  size-preserving normalization ensuring every product gate has children of syntactic degree `≥ 1`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.ofCslibCircuit`: embedding of
  `Cslib.Circuits.Circuit`
  over `arithSignature F` with size `m + c.size`.

## Main results

* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.normalize_size`,
  `normalize_synDeg`,
  `normalize_evalGate`, `normalize_eval`, `isNormalized_normalize`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.ofCslibCircuit_size`,
  `ofCslibCircuit_eval`.
* `CslibFrontier.Circuits.Arithmetic.Noncommutative.NoncommCircuit.exists_var_gate_of_lift_ne`:
  variable dependence
  forces a corresponding variable leaf.
-/

public section

namespace CslibFrontier.Circuits.Arithmetic.Noncommutative

open _root_.FreeAlgebra

/-- The label and incoming edges of vertex `k` in a topologically ordered fan-in 2
noncommutative arithmetic circuit over `F` and variables `α`. -/
inductive GateKind (F α : Type*) (k : ℕ) where
  /-- Leaf labeled by a scalar constant `c ∈ F`. -/
  | const (c : F) : GateKind F α k
  /-- Leaf labeled by a variable `x ∈ α`. -/
  | var (x : α) : GateKind F α k
  /-- Internal sum gate `wa • a + wb • b` with weighted edges from earlier vertices `a, b`. -/
  | add (a b : Fin k) (wa wb : F) : GateKind F α k
  /-- Internal product gate `(wa • a) * (wb • b)` with ordered left/right children `a, b`. -/
  | mul (a b : Fin k) (wa wb : F) : GateKind F α k

/-- A fan-in 2 noncommutative arithmetic circuit over `F` and variables `α` with edge weights,
represented in topological order. `size` is the total number of vertices (leaves and gates). -/
structure NoncommCircuit (F α : Type*) where
  /-- Total number of vertices (leaves and internal gates) in the DAG. -/
  size : ℕ
  /-- The gate or leaf specification at each vertex `i` in topological order. -/
  gates : (i : Fin size) → GateKind F α i.val
  /-- The designated output vertex of the circuit. -/
  output : Fin size

namespace NoncommCircuit

section Evaluation

variable {F α : Type*} [CommSemiring F]

/-- The noncommutative polynomial in `FreeAlgebra F α` computed at gate `i` of `Ψ`. -/
noncomputable def evalGate (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) : FreeAlgebra F α :=
  match Ψ.gates i with
  | .const c => algebraMap F (FreeAlgebra F α) c
  | .var x => ι F x
  | .add a b wa wb =>
      wa • Ψ.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩ +
        wb • Ψ.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩
  | .mul a b wa wb =>
      (wa • Ψ.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩) *
        (wb • Ψ.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩)
termination_by i.val
decreasing_by
  · exact a.isLt
  · exact b.isLt
  · exact a.isLt
  · exact b.isLt

/-- The noncommutative polynomial computed at the output gate of `Ψ`. -/
noncomputable def eval (Ψ : NoncommCircuit F α) : FreeAlgebra F α :=
  Ψ.evalGate Ψ.output

/-- Equation lemma for `evalGate` at a constant leaf. -/
@[simp]
theorem evalGate_const (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {c : F}
    (h : Ψ.gates i = .const c) :
    Ψ.evalGate i = algebraMap F (FreeAlgebra F α) c := by
  rw [evalGate, h]

/-- Equation lemma for `evalGate` at a variable leaf. -/
@[simp]
theorem evalGate_var (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {x : α}
    (h : Ψ.gates i = .var x) :
    Ψ.evalGate i = ι F x := by
  rw [evalGate, h]

/-- Equation lemma for `evalGate` at a sum gate. -/
theorem evalGate_add (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {a b : Fin i.val} {wa wb : F}
    (h : Ψ.gates i = .add a b wa wb) :
    Ψ.evalGate i =
      wa • Ψ.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩ +
        wb • Ψ.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩ := by
  rw [evalGate, h]

/-- Equation lemma for `evalGate` at a product gate. -/
theorem evalGate_mul (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {a b : Fin i.val} {wa wb : F}
    (h : Ψ.gates i = .mul a b wa wb) :
    Ψ.evalGate i =
      (wa • Ψ.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩) *
        (wb • Ψ.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩) := by
  rw [evalGate, h]

/-- Equation lemma relating `eval` to `evalGate` at the output gate. -/
theorem eval_eq_evalGate_output (Ψ : NoncommCircuit F α) :
    Ψ.eval = Ψ.evalGate Ψ.output := by rfl

end Evaluation

section DegreesAndDepth

variable {F α : Type*}

/-- The syntactic degree of gate `i` in `Ψ`: `0` on constants, `1` on variables, `max` on sum
gates, and `+` on product gates. -/
def synDeg (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) : ℕ :=
  match Ψ.gates i with
  | .const _ => 0
  | .var _ => 1
  | .add a b _ _ =>
      max (Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩)
        (Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩)
  | .mul a b _ _ =>
      Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ +
        Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩
termination_by i.val
decreasing_by
  · exact a.isLt
  · exact b.isLt
  · exact a.isLt
  · exact b.isLt

/-- Equation lemma for `synDeg` at a constant leaf. -/
@[simp]
theorem synDeg_const (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {c : F}
    (h : Ψ.gates i = .const c) : Ψ.synDeg i = 0 := by
  rw [synDeg, h]

/-- Equation lemma for `synDeg` at a variable leaf. -/
@[simp]
theorem synDeg_var (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {x : α}
    (h : Ψ.gates i = .var x) : Ψ.synDeg i = 1 := by
  rw [synDeg, h]

/-- Equation lemma for `synDeg` at a sum gate. -/
theorem synDeg_add (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {a b : Fin i.val} {wa wb : F}
    (h : Ψ.gates i = .add a b wa wb) :
    Ψ.synDeg i =
      max (Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩)
        (Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩) := by
  rw [synDeg, h]

/-- Equation lemma for `synDeg` at a product gate. -/
theorem synDeg_mul (Ψ : NoncommCircuit F α) {i : Fin Ψ.size} {a b : Fin i.val} {wa wb : F}
    (h : Ψ.gates i = .mul a b wa wb) :
    Ψ.synDeg i =
      Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ +
        Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ := by
  rw [synDeg, h]

/-- The syntactic degree of a circuit: the maximum syntactic degree over all vertices. -/
def circuitSynDeg (Ψ : NoncommCircuit F α) : ℕ :=
  Finset.univ.sup Ψ.synDeg

/-- The depth of gate `i` in `Ψ`: the length of the longest path from a leaf to `i`. -/
def gateDepth (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) : ℕ :=
  match Ψ.gates i with
  | .const _ => 0
  | .var _ => 0
  | .add a b _ _ =>
      max (Ψ.gateDepth ⟨a.val, lt_trans a.isLt i.isLt⟩)
        (Ψ.gateDepth ⟨b.val, lt_trans b.isLt i.isLt⟩) + 1
  | .mul a b _ _ =>
      max (Ψ.gateDepth ⟨a.val, lt_trans a.isLt i.isLt⟩)
        (Ψ.gateDepth ⟨b.val, lt_trans b.isLt i.isLt⟩) + 1
termination_by i.val
decreasing_by
  · exact a.isLt
  · exact b.isLt
  · exact a.isLt
  · exact b.isLt

/-- Predicate asserting that vertex `i` of `Ψ` is a product gate. -/
@[expose] def IsMulGate (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) : Prop :=
  match Ψ.gates i with
  | .mul _ _ _ _ => True
  | _ => False

/-- Decidability of `IsMulGate`. -/
instance instDecidablePredIsMulGate (Ψ : NoncommCircuit F α) :
    DecidablePred Ψ.IsMulGate := fun i ↦ by
  unfold IsMulGate
  cases Ψ.gates i <;> infer_instance

/-- A circuit is normalized when every product gate has both inputs of syntactic degree `≥ 1`. -/
def IsNormalized (Ψ : NoncommCircuit F α) : Prop :=
  ∀ (i : Fin Ψ.size) (a b : Fin i.val) (wa wb : F),
    Ψ.gates i = .mul a b wa wb →
      1 ≤ Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ ∧
        1 ≤ Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩

/-- In a normalized circuit, both inputs of every product gate have syntactic degree `≥ 1`. -/
theorem IsNormalized.mul_pos {Ψ : NoncommCircuit F α} (hNorm : Ψ.IsNormalized)
    (i : Fin Ψ.size) (a b : Fin i.val) (wa wb : F) (h : Ψ.gates i = .mul a b wa wb) :
    1 ≤ Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ ∧
      1 ≤ Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ := by
  exact hNorm i a b wa wb h

end DegreesAndDepth

section Normalization

variable {F α : Type*} [CommSemiring F]

/-- Scalar value extracted from any gate (agrees with `evalGate` whenever `synDeg = 0`). -/
def constVal (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) : F :=
  match Ψ.gates i with
  | .const c => c
  | .var _ => 0
  | .add a b wa wb =>
      wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩ +
        wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩
  | .mul a b wa wb =>
      (wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩) *
        (wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩)
termination_by i.val
decreasing_by
  · exact a.isLt
  · exact b.isLt
  · exact a.isLt
  · exact b.isLt

/-- Every gate of syntactic degree `0` computes the scalar `algebraMap F _ (Ψ.constVal i)`. -/
theorem evalGate_eq_algebraMap_of_synDeg_zero (Ψ : NoncommCircuit F α) (i : Fin Ψ.size)
    (h0 : Ψ.synDeg i = 0) :
    Ψ.evalGate i = algebraMap F (FreeAlgebra F α) (Ψ.constVal i) := by
  induction hn : i.val using Nat.strong_induction_on generalizing i with
  | ind k ih =>
    subst hn
    cases hg : Ψ.gates i with
    | const c =>
      rw [evalGate_const Ψ hg, constVal, hg]
    | var x =>
      rw [synDeg_var Ψ hg] at h0
      omega
    | add a b wa wb =>
      rw [synDeg_add Ψ hg] at h0
      have ha0 : Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ = 0 := by omega
      have hb0 : Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ = 0 := by omega
      have iha := ih a.val a.isLt ⟨a.val, lt_trans a.isLt i.isLt⟩ ha0 rfl
      have ihb := ih b.val b.isLt ⟨b.val, lt_trans b.isLt i.isLt⟩ hb0 rfl
      rw [evalGate_add Ψ hg, constVal, hg, iha, ihb]
      simp [Algebra.algebraMap_eq_smul_one, map_add, map_mul, smul_smul, mul_comm]
    | mul a b wa wb =>
      rw [synDeg_mul Ψ hg] at h0
      have ha0 : Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ = 0 := by omega
      have hb0 : Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ = 0 := by omega
      have iha := ih a.val a.isLt ⟨a.val, lt_trans a.isLt i.isLt⟩ ha0 rfl
      have ihb := ih b.val b.isLt ⟨b.val, lt_trans b.isLt i.isLt⟩ hb0 rfl
      rw [evalGate_mul Ψ hg, constVal, hg, iha, ihb]
      simp [Algebra.algebraMap_eq_smul_one, map_mul, smul_smul, mul_comm, mul_left_comm]

/-- In-place normalization of `Ψ`: every product gate with a syntactic-degree-`0` child is
replaced by an equivalent constant leaf or weighted sum gate, preserving vertex count, syntactic
degrees, and every gate's polynomial. -/
@[expose] def normalize (Ψ : NoncommCircuit F α) : NoncommCircuit F α where
  size := Ψ.size
  output := Ψ.output
  gates i :=
    match Ψ.gates i with
    | .const c => .const c
    | .var x => .var x
    | .add a b wa wb => .add a b wa wb
    | .mul a b wa wb =>
        let da := Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩
        let db := Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩
        if da = 0 then
          if db = 0 then
            .const ((wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩) *
              (wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩))
          else
            .add b b (wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩ * wb) 0
        else if db = 0 then
          .add a a (wa * wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩) 0
        else
          .mul a b wa wb

/-- `normalize` preserves the circuit size. -/
@[simp]
theorem normalize_size (Ψ : NoncommCircuit F α) : (Ψ.normalize).size = Ψ.size := by
  rfl

/-- `normalize` preserves the syntactic degree of every gate. -/
theorem normalize_synDeg (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) :
    Ψ.normalize.synDeg i = Ψ.synDeg i := by
  induction hn : i.val using Nat.strong_induction_on generalizing i with
  | ind k ih =>
    subst hn
    cases hg : Ψ.gates i with
    | const c =>
      have hng : Ψ.normalize.gates i = .const c := by simp [normalize, hg]
      rw [synDeg_const _ hng, synDeg_const _ hg]
    | var x =>
      have hng : Ψ.normalize.gates i = .var x := by simp [normalize, hg]
      rw [synDeg_var _ hng, synDeg_var _ hg]
    | add a b wa wb =>
      have hng : Ψ.normalize.gates i = .add a b wa wb := by simp [normalize, hg]
      have iha : Ψ.normalize.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ =
          Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ :=
        ih a.val a.isLt ⟨a.val, lt_trans a.isLt i.isLt⟩ rfl
      have ihb : Ψ.normalize.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ =
          Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ :=
        ih b.val b.isLt ⟨b.val, lt_trans b.isLt i.isLt⟩ rfl
      rw [synDeg_add _ hng, synDeg_add _ hg, iha, ihb]
    | mul a b wa wb =>
      rw [synDeg_mul _ hg]
      have iha : ∀ h, Ψ.normalize.synDeg ⟨a.val, h⟩ = Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ :=
        fun _ ↦ ih a.val a.isLt ⟨a.val, lt_trans a.isLt i.isLt⟩ rfl
      have ihb : ∀ h, Ψ.normalize.synDeg ⟨b.val, h⟩ = Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ :=
        fun _ ↦ ih b.val b.isLt ⟨b.val, lt_trans b.isLt i.isLt⟩ rfl
      by_cases ha0 : Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ = 0
      · by_cases hb0 : Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ = 0
        · have hng : Ψ.normalize.gates i =
              .const ((wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩) *
                (wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩)) := by
            simp [normalize, hg, ha0, hb0]
          rw [synDeg_const _ hng, ha0, hb0]
        · have hng : Ψ.normalize.gates i =
              .add b b (wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩ * wb) 0 := by
            simp [normalize, hg, ha0, hb0]
          rw [synDeg_add _ hng, ihb, ha0, max_self, zero_add]
      · by_cases hb0 : Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ = 0
        · have hng : Ψ.normalize.gates i =
              .add a a (wa * wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩) 0 := by
            simp [normalize, hg, ha0, hb0]
          rw [synDeg_add _ hng, iha, hb0, max_self, add_zero]
        · have hng : Ψ.normalize.gates i = .mul a b wa wb := by
            simp [normalize, hg, ha0, hb0]
          rw [synDeg_mul _ hng, iha, ihb]

/-- `normalize` preserves the polynomial computed at every gate. -/
theorem normalize_evalGate (Ψ : NoncommCircuit F α) (i : Fin Ψ.size) :
    Ψ.normalize.evalGate i = Ψ.evalGate i := by
  induction hn : i.val using Nat.strong_induction_on generalizing i with
  | ind k ih =>
    subst hn
    cases hg : Ψ.gates i with
    | const c =>
      have hng : Ψ.normalize.gates i = .const c := by simp [normalize, hg]
      rw [evalGate_const _ hng, evalGate_const _ hg]
    | var x =>
      have hng : Ψ.normalize.gates i = .var x := by simp [normalize, hg]
      rw [evalGate_var _ hng, evalGate_var _ hg]
    | add a b wa wb =>
      have hng : Ψ.normalize.gates i = .add a b wa wb := by simp [normalize, hg]
      have iha : Ψ.normalize.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩ =
          Ψ.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩ :=
        ih a.val a.isLt ⟨a.val, lt_trans a.isLt i.isLt⟩ rfl
      have ihb : Ψ.normalize.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩ =
          Ψ.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩ :=
        ih b.val b.isLt ⟨b.val, lt_trans b.isLt i.isLt⟩ rfl
      rw [evalGate_add _ hng, evalGate_add _ hg, iha, ihb]
    | mul a b wa wb =>
      rw [evalGate_mul _ hg]
      have iha : ∀ h, Ψ.normalize.evalGate ⟨a.val, h⟩ =
          Ψ.evalGate ⟨a.val, lt_trans a.isLt i.isLt⟩ :=
        fun _ ↦ ih a.val a.isLt ⟨a.val, lt_trans a.isLt i.isLt⟩ rfl
      have ihb : ∀ h, Ψ.normalize.evalGate ⟨b.val, h⟩ =
          Ψ.evalGate ⟨b.val, lt_trans b.isLt i.isLt⟩ :=
        fun _ ↦ ih b.val b.isLt ⟨b.val, lt_trans b.isLt i.isLt⟩ rfl
      by_cases ha0 : Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ = 0
      · have hva := evalGate_eq_algebraMap_of_synDeg_zero Ψ _ ha0
        by_cases hb0 : Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ = 0
        · have hvb := evalGate_eq_algebraMap_of_synDeg_zero Ψ _ hb0
          have hng : Ψ.normalize.gates i =
              .const ((wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩) *
                (wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩)) := by
            simp [normalize, hg, ha0, hb0]
          rw [evalGate_const _ hng, hva, hvb]
          simp [Algebra.algebraMap_eq_smul_one, map_mul, smul_smul, mul_comm, mul_left_comm]
        · have hng : Ψ.normalize.gates i =
              .add b b (wa * Ψ.constVal ⟨a.val, lt_trans a.isLt i.isLt⟩ * wb) 0 := by
            simp [normalize, hg, ha0, hb0]
          rw [evalGate_add _ hng, ihb, hva]
          simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm, mul_left_comm]
      · by_cases hb0 : Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ = 0
        · have hvb := evalGate_eq_algebraMap_of_synDeg_zero Ψ _ hb0
          have hng : Ψ.normalize.gates i =
              .add a a (wa * wb * Ψ.constVal ⟨b.val, lt_trans b.isLt i.isLt⟩) 0 := by
            simp [normalize, hg, ha0, hb0]
          rw [evalGate_add _ hng, iha, hvb]
          simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm, mul_assoc]
        · have hng : Ψ.normalize.gates i = .mul a b wa wb := by
            simp [normalize, hg, ha0, hb0]
          rw [evalGate_mul _ hng, iha, ihb]

/-- `normalize` preserves the output polynomial of the circuit. -/
theorem normalize_eval (Ψ : NoncommCircuit F α) : Ψ.normalize.eval = Ψ.eval :=
  Ψ.normalize_evalGate Ψ.output

/-- `normalize Ψ` is always normalized. -/
theorem isNormalized_normalize (Ψ : NoncommCircuit F α) : Ψ.normalize.IsNormalized := by
  intro i a b wa wb hng
  have h1 : Ψ.normalize.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ =
      Ψ.synDeg ⟨a.val, lt_trans a.isLt i.isLt⟩ :=
    normalize_synDeg Ψ ⟨a.val, lt_trans a.isLt i.isLt⟩
  have h2 : Ψ.normalize.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ =
      Ψ.synDeg ⟨b.val, lt_trans b.isLt i.isLt⟩ :=
    normalize_synDeg Ψ ⟨b.val, lt_trans b.isLt i.isLt⟩
  rw [h1, h2]
  cases hg : Ψ.gates i with
  | const c => simp [normalize, hg] at hng
  | var x => simp [normalize, hg] at hng
  | add a' b' wa' wb' => simp [normalize, hg] at hng
  | mul a' b' wa' wb' =>
    by_cases ha0 : Ψ.synDeg ⟨a'.val, lt_trans a'.isLt i.isLt⟩ = 0
    · by_cases hb0 : Ψ.synDeg ⟨b'.val, lt_trans b'.isLt i.isLt⟩ = 0 <;>
        simp [normalize, hg, ha0, hb0] at hng
    · by_cases hb0 : Ψ.synDeg ⟨b'.val, lt_trans b'.isLt i.isLt⟩ = 0
      · simp [normalize, hg, ha0, hb0] at hng
      · simp only [normalize, hg, ha0, hb0, ↓reduceIte, GateKind.mul.injEq] at hng
        rcases hng with ⟨rfl, rfl, -, -⟩
        exact ⟨Nat.pos_of_ne_zero ha0, Nat.pos_of_ne_zero hb0⟩

end Normalization

section VariableDependence

variable {F α : Type*} [CommSemiring F]

/-- If no leaf of `Ψ` is labeled by `x`, then setting `x ↦ 0` preserves `Ψ.evalGate i`. -/
theorem lift_zero_evalGate_of_no_var (Ψ : NoncommCircuit F α) [DecidableEq α] (x : α)
    (hno : ∀ i : Fin Ψ.size, Ψ.gates i ≠ .var x) (i : Fin Ψ.size) :
    FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y) (Ψ.evalGate i) =
      Ψ.evalGate i := by
  induction hn : i.val using Nat.strong_induction_on generalizing i with
  | ind k ih =>
    subst hn
    cases hg : Ψ.gates i with
    | const c =>
      rw [evalGate_const _ hg, AlgHom.commutes]
    | var y =>
      have hy : y ≠ x := fun hyx ↦ hno i (hg.trans (congrArg GateKind.var hyx))
      rw [evalGate_var _ hg, FreeAlgebra.lift_ι_apply]
      simp [hy]
    | add a b wa wb =>
      rw [evalGate_add _ hg, map_add, map_smul, map_smul,
        ih a.val a.isLt _ rfl, ih b.val b.isLt _ rfl]
    | mul a b wa wb =>
      rw [evalGate_mul _ hg, map_mul, map_smul, map_smul,
        ih a.val a.isLt _ rfl, ih b.val b.isLt _ rfl]

/-- If setting `x ↦ 0` changes `Ψ.eval`, then `Ψ` contains a leaf labeled by `x`. -/
theorem exists_var_gate_of_lift_ne (Ψ : NoncommCircuit F α) [DecidableEq α] (x : α)
    (hne : FreeAlgebra.lift F (fun y ↦ if y = x then 0 else ι F y) Ψ.eval ≠ Ψ.eval) :
    ∃ i : Fin Ψ.size, Ψ.gates i = .var x := by
  by_contra h
  push Not at h
  exact hne (lift_zero_evalGate_of_no_var Ψ x h Ψ.output)

end VariableDependence

section CslibBridge

variable {F : Type*} [CommSemiring F]

/-- Extract line `k` (with wires strictly preceding `k`) from a `Cslib.Circuits.Program`. -/
private def programLineAt {σ : Cslib.Circuits.Signature} {m : ℕ} :
    ∀ {s : ℕ}, Cslib.Circuits.Program σ m s → (k : Fin s) → Cslib.Circuits.Line σ m k.val
  | _, .empty, k => Fin.elim0 k
  | _, .gate p l, k => Fin.lastCases l (fun j ↦ programLineAt p j) k

private theorem programLineAt_gate_castSucc {σ : Cslib.Circuits.Signature} {m g : ℕ}
    (p : Cslib.Circuits.Program σ m g) (l : Cslib.Circuits.Line σ m g) (j : Fin g) :
    programLineAt (p.gate l) j.castSucc = programLineAt p j := by
  simp [programLineAt]

/-- Map a `Wire m k` into `Fin (m + k)`. -/
private def wireToFin {m k : ℕ} : Cslib.Circuits.Wire m k → Fin (m + k)
  | .input i => ⟨i.val, by omega⟩
  | .gate j => ⟨m + j.val, by omega⟩

private theorem wireToFin_lt {m k : ℕ} (w : Cslib.Circuits.Wire m k) :
    (wireToFin w).val < m + k := (wireToFin w).isLt

/-- Translate a single `Line` of `arithSignature F` into a `GateKind`. -/
private def lineToGate {m k : ℕ}
    (line : Cslib.Circuits.Line (Cslib.Circuits.arithSignature F) m k) :
    GateKind F (Fin m) (m + k) :=
  match line with
  | ⟨.const a, _⟩ => .const a
  | ⟨.add, w⟩ => .add (wireToFin (w 0)) (wireToFin (w 1)) 1 1
  | ⟨.mul, w⟩ => .mul (wireToFin (w 0)) (wireToFin (w 1)) 1 1

/-- Convert an unweighted `Cslib.Circuits.Circuit (arithSignature F) m 1` into a `NoncommCircuit`
with `m + c.size` vertices (the `m` input leaves followed by the `c.size` program gates). -/
def ofCslibCircuit {m : ℕ}
    (c : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature F) m 1) :
    NoncommCircuit F (Fin m) where
  size := m + c.size
  output := wireToFin (c.outputs 0)
  gates i :=
    if h : i.val < m then
      .var ⟨i.val, h⟩
    else
      let k : Fin c.size := ⟨i.val - m, by omega⟩
      have hk : m + k.val = i.val := by dsimp [k]; omega
      hk ▸ lineToGate (programLineAt c.program k)

/-- The size of `ofCslibCircuit c` is `m + c.size`. -/
@[simp]
theorem ofCslibCircuit_size {m : ℕ}
    (c : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature F) m 1) :
    (ofCslibCircuit c).size = m + c.size := by
  rfl

private theorem evalGate_eq_of_prefix {α : Type*} (Ψ₁ Ψ₂ : NoncommCircuit F α)
    (n : ℕ)
    (hg : ∀ (k : ℕ) (hk1 : k < Ψ₁.size) (hk2 : k < Ψ₂.size), k < n →
      Ψ₁.gates ⟨k, hk1⟩ = Ψ₂.gates ⟨k, hk2⟩) :
    ∀ (k : ℕ) (hk1 : k < Ψ₁.size) (hk2 : k < Ψ₂.size), k < n →
      Ψ₁.evalGate ⟨k, hk1⟩ = Ψ₂.evalGate ⟨k, hk2⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk1 hk2 hkn
    have hgate := hg k hk1 hk2 hkn
    cases h1 : Ψ₁.gates ⟨k, hk1⟩ with
    | const c =>
      have h2 : Ψ₂.gates ⟨k, hk2⟩ = .const c := hgate.symm.trans h1
      rw [evalGate_const _ h1, evalGate_const _ h2]
    | var x =>
      have h2 : Ψ₂.gates ⟨k, hk2⟩ = .var x := hgate.symm.trans h1
      rw [evalGate_var _ h1, evalGate_var _ h2]
    | add a b wa wb =>
      have h2 : Ψ₂.gates ⟨k, hk2⟩ = .add a b wa wb := hgate.symm.trans h1
      rw [evalGate_add _ h1, evalGate_add _ h2,
        ih a.val a.isLt _ _ (lt_trans a.isLt hkn),
        ih b.val b.isLt _ _ (lt_trans b.isLt hkn)]
    | mul a b wa wb =>
      have h2 : Ψ₂.gates ⟨k, hk2⟩ = .mul a b wa wb := hgate.symm.trans h1
      rw [evalGate_mul _ h1, evalGate_mul _ h2,
        ih a.val a.isLt _ _ (lt_trans a.isLt hkn),
        ih b.val b.isLt _ _ (lt_trans b.isLt hkn)]

private theorem ofCslibCircuit_gates_prefix {m g : ℕ}
    (p : Cslib.Circuits.Program (Cslib.Circuits.arithSignature F) m g)
    (line : Cslib.Circuits.Line (Cslib.Circuits.arithSignature F) m g)
    (out₁ : Cslib.Circuits.Wire m (g + 1)) (out₂ : Cslib.Circuits.Wire m g)
    (k : ℕ) (hk1 : k < (ofCslibCircuit (F := F) ⟨p.gate line, fun _ ↦ out₁⟩).size)
    (hk2 : k < (ofCslibCircuit (F := F) ⟨p, fun _ ↦ out₂⟩).size) :
    (ofCslibCircuit (F := F) ⟨p.gate line, fun _ ↦ out₁⟩).gates ⟨k, hk1⟩ =
      (ofCslibCircuit (F := F) ⟨p, fun _ ↦ out₂⟩).gates ⟨k, hk2⟩ := by
  have hk2' : k < m + g := hk2
  by_cases hkm : k < m
  · simp [ofCslibCircuit, hkm]
  · simp only [ofCslibCircuit, hkm, ↓reduceDIte]
    have hkl : k - m < g := by omega
    have hcast : (⟨k - m, by omega⟩ : Fin (g + 1)) = (⟨k - m, hkl⟩ : Fin g).castSucc := rfl
    have hpa : programLineAt (p.gate line) ⟨k - m, by omega⟩ = programLineAt p ⟨k - m, hkl⟩ := by
      exact programLineAt_gate_castSucc p line ⟨k - m, hkl⟩
    have hline_eq :
        (show m + (⟨k - m, by omega⟩ : Fin (g + 1)).val = k by dsimp; omega) ▸
          lineToGate (programLineAt (p.gate line) ⟨k - m, by omega⟩) =
        (show m + (⟨k - m, hkl⟩ : Fin g).val = k by dsimp; omega) ▸
          lineToGate (programLineAt p ⟨k - m, hkl⟩) := by
      congr 1
      · exact congrArg lineToGate hpa
    exact hline_eq

private theorem cast_lineToGate_eq {m s : ℕ}
    (p : Cslib.Circuits.Program (Cslib.Circuits.arithSignature F) m s)
    {k₁ k₂ : Fin s} (hk : k₁ = k₂) (h1 : m + k₁.val = m + k₂.val) :
    h1 ▸ lineToGate (programLineAt p k₁) = lineToGate (programLineAt p k₂) := by
  subst hk
  rfl

private theorem evalGate_ofCslibCircuit_wire {m s : ℕ}
    (p : Cslib.Circuits.Program (Cslib.Circuits.arithSignature F) m s)
    (out : Cslib.Circuits.Wire m s) (w : Cslib.Circuits.Wire m s) :
    (ofCslibCircuit (F := F) ⟨p, fun _ ↦ out⟩).evalGate (wireToFin w) =
      p.trace (Cslib.Circuits.arithInterpretationWith F (algebraMap F _)) (ι F) w := by
  induction p with
  | empty =>
    cases w with
    | input j =>
      have hg : (ofCslibCircuit (F := F) ⟨.empty, fun _ ↦ out⟩).gates (wireToFin (.input j)) =
          .var j := by
        have hj : (wireToFin (.input j : Cslib.Circuits.Wire m 0)).val < m := j.isLt
        unfold ofCslibCircuit
        dsimp only
        rw [dite_eq_left hj]
        rfl
      rw [evalGate_var _ hg]
      rfl
    | gate g => exact Fin.elim0 g
  | @gate g p line ih =>
    have hpref : ∀ (u : Cslib.Circuits.Wire m g),
        (ofCslibCircuit (F := F) ⟨p.gate line, fun _ ↦ out⟩).evalGate
          ⟨(wireToFin u).val, by
            have := wireToFin_lt u
            change (wireToFin u).val < m + (g + 1)
            omega⟩ =
        (ofCslibCircuit (F := F) ⟨p, fun _ ↦ u⟩).evalGate (wireToFin u) := by
      intro u
      exact evalGate_eq_of_prefix
        (ofCslibCircuit (F := F) ⟨p.gate line, fun _ ↦ out⟩)
        (ofCslibCircuit (F := F) ⟨p, fun _ ↦ u⟩)
        (m + g)
        (fun k hk1 hk2 _ ↦ ofCslibCircuit_gates_prefix p line out u k hk1 hk2)
        (wireToFin u).val _ (wireToFin_lt u) (wireToFin_lt u)
    cases w using Cslib.Circuits.Wire.lastCases with
    | last =>
      have hge : ¬ (m + g < m) := by omega
      have hgate_last :
          (ofCslibCircuit (F := F) ⟨p.gate line, fun _ ↦ out⟩).gates
            (wireToFin (.gate (Fin.last g))) =
          lineToGate line := by
        unfold ofCslibCircuit
        dsimp only [wireToFin, Fin.val_last]
        rw [dite_eq_right hge]
        have hfin : (⟨m + g - m, by omega⟩ : Fin (g + 1)) = Fin.last g :=
          Fin.ext (Nat.add_sub_cancel_left m g)
        have hpa : programLineAt (p.gate line) (Fin.last g) = line := by simp [programLineAt]
        exact (cast_lineToGate_eq (p.gate line) hfin (by dsimp; omega)).trans
          (congrArg lineToGate hpa)
      have htrace :
          (p.gate line).trace (Cslib.Circuits.arithInterpretationWith F (algebraMap F _)) (ι F)
            (.gate (Fin.last g)) =
          line.eval (Cslib.Circuits.arithInterpretationWith F (algebraMap F _)) (ι F)
            (p.eval (Cslib.Circuits.arithInterpretationWith F (algebraMap F _)) (ι F)) := by
        simp [Cslib.Circuits.Program.trace]
      rw [htrace]
      rcases line with ⟨op, wires⟩
      cases op with
      | const a =>
        rw [evalGate_const _ hgate_last]
        simp [Cslib.Circuits.Line.eval]
      | add =>
        rw [evalGate_add _ hgate_last, one_smul, one_smul]
        have h0 := (hpref (wires 0)).trans (ih (wires 0) (wires 0))
        have h1 := (hpref (wires 1)).trans (ih (wires 1) (wires 1))
        simpa [Cslib.Circuits.Line.eval, Cslib.Circuits.Program.trace, wireToFin] using
          congrArg₂ (· + ·) h0 h1
      | mul =>
        rw [evalGate_mul _ hgate_last, one_smul, one_smul]
        have h0 := (hpref (wires 0)).trans (ih (wires 0) (wires 0))
        have h1 := (hpref (wires 1)).trans (ih (wires 1) (wires 1))
        simpa [Cslib.Circuits.Line.eval, Cslib.Circuits.Program.trace, wireToFin] using
          congrArg₂ (· * ·) h0 h1
    | castSucc u =>
      rw [Cslib.Circuits.Program.trace_gate_castSucc]
      have hu_eq : (wireToFin u.castSucc : Fin (m + (g + 1))).val = (wireToFin u).val := by
        cases u <;> rfl
      have hfin : (wireToFin u.castSucc : Fin (m + (g + 1))) =
          ⟨(wireToFin u).val, by have := wireToFin_lt u; omega⟩ := Fin.ext hu_eq
      change (ofCslibCircuit (F := F) ⟨p.gate line, fun _ ↦ out⟩).evalGate
        (wireToFin u.castSucc) = _
      rw [hfin]
      exact (hpref u).trans (ih u u)

/-- `ofCslibCircuit c` computes the same noncommutative polynomial as `c`. -/
theorem ofCslibCircuit_eval {m : ℕ}
    (c : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature F) m 1) :
    (ofCslibCircuit c).eval = c.noncommPolynomial 0 := by
  rcases c with ⟨p, outputs⟩
  rw [Cslib.Circuits.Circuit.noncommPolynomial_eq_eval, Cslib.Circuits.Circuit.eval,
    Function.comp_apply, eval, ofCslibCircuit]
  exact evalGate_ofCslibCircuit_wire p (outputs 0) (outputs 0)

end CslibBridge

end NoncommCircuit

end CslibFrontier.Circuits.Arithmetic.Noncommutative
