/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Probability.StatisticalDistance
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Cslib.Probability.PMF

import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Only-Computation-Leaks Circuit Resilience and Group NAND Gadgets

This module formalizes the Micali–Reyzin "only computation leaks" (OCL) model over `Cslib`
straight-line De Morgan Boolean circuits (`Cslib.Circuits.Circuit Boolean.signature`), proves
base-case security and raw-input parity impossibility theorems under standard Lean axioms, and
formalizes Barrington / Miles–Viola conjugate-word group NAND gate gadgets together with
non-abelian necessity and concrete realizations in `SL(2, F)` for every finite field of
characteristic `2` and even `𝔽₂`-dimension (in particular `|F| = 4^m`).

## Main definitions

- `Cslib.Circuits.LeakageResilience.UsesInput`: predicate indicating that an input wire appears in
  the output or some internal gate of a De Morgan Boolean circuit.
- `Cslib.Circuits.LeakageResilience.OCLPartition`, `Cslib.Circuits.LeakageResilience.OCLAdversary`,
  `Cslib.Circuits.LeakageResilience.RandomizedOCLCircuit`,
  `Cslib.Circuits.LeakageResilience.IsOCLSecure`,
  `Cslib.Circuits.LeakageResilience.IsEncodedOCLSecure`: topological block partitions, adaptive
  block-wise leakage adversaries, randomized OCL circuits, and raw/encoded OCL security.
- `Cslib.Circuits.LeakageResilience.GroupGateGadget`: conjugate-word NAND gate gadgets over a group.

## Main results

- `Cslib.Circuits.LeakageResilience.isOCLSecure_zero_leakage`,
  `Cslib.Circuits.LeakageResilience.isEncodedOCLSecure_zero_leakage`,
  `Cslib.Circuits.LeakageResilience.isOCLSecure_const`,
  `Cslib.Circuits.LeakageResilience.isEncodedOCLSecure_const`: base-case OCL security results.
- `Cslib.Circuits.LeakageResilience.not_isOCLSecure_raw_xor`,
  `Cslib.Circuits.LeakageResilience.not_isOCLSecure_xor_unshielded`: impossibility of raw-input OCL
  security for `2`-bit parity.
- `Cslib.Circuits.LeakageResilience.not_exists_groupGateGadget_of_commGroup`: no commutative group
  has a group NAND gate gadget.
- `Cslib.Circuits.LeakageResilience.exists_sl2_groupGateGadget_of_even_finrank`,
  `Cslib.Circuits.LeakageResilience.exists_sl2_groupGateGadget_of_card_eq_four_pow`: length-`4`
  group NAND gate gadgets in `SL(2, F)`.
-/

public section

namespace Cslib.Circuits.LeakageResilience

open Cslib.Circuits
open scoped Cslib.Probability.PMF

universe u

/-! ### Wire Usage and Micali–Reyzin OCL Partitions -/

section OCLModel

/-- Predicate stating that input wire `x` appears in the output support or in some internal gate
of a straight-line De Morgan Boolean circuit `C`. -/
def UsesInput {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1) (x : Fin n) : Prop :=
  x ∈ C.inputSupport ∨
    ∃ (k : Fin C.size) (a : Fin (Boolean.signature.Arity (C.program.lines k).op)),
      (C.program.lines k).wires a = .input x

private lemma program_eval_eq_of_eq_on_lines {n g : ℕ} (p : Program Boolean.signature n g)
    {v₁ v₂ : Fin n → Bool}
    (hv : ∀ (k : Fin g) (a : Fin (Boolean.signature.Arity (p.lines k).op)) (x : Fin n),
      (p.lines k).wires a = .input x → v₁ x = v₂ x) :
    p.eval Boolean.interpretation v₁ = p.eval Boolean.interpretation v₂ := by
  induction p with
  | empty => exact Subsingleton.elim _ _
  | @gate g q line ih =>
    have hq : q.eval Boolean.interpretation v₁ = q.eval Boolean.interpretation v₂ := by
      refine ih fun k a x hx ↦ ?_
      have hv' := hv k.castSucc
      rw [Program.lines_gate_castSucc] at hv'
      exact hv' a x (by simp [Line.mapWires_wires, hx])
    funext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · rw [Program.eval_gate_last, Program.eval_gate_last, hq]
      unfold Line.eval
      congr 1
      funext a
      simp only [Function.comp_apply]
      cases hw : line.wires a with
      | input x =>
        simp only [Wire.elim_input]
        have hv' := hv (Fin.last g)
        rw [Program.lines_gate_last] at hv'
        exact hv' a x (by simp [Line.mapWires_wires, hw])
      | gate j => rfl
    · simp only [Program.eval_gate_castSucc, hq]

/-- If two input valuations agree on every input wire used by `C`, then `C.program.eval` agrees
on them. -/
lemma program_eval_eq_of_eq_on_usesInput {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1)
    {v₁ v₂ : Fin n → Bool} (hv : ∀ x, UsesInput C x → v₁ x = v₂ x) :
    C.program.eval Boolean.interpretation v₁ = C.program.eval Boolean.interpretation v₂ :=
  program_eval_eq_of_eq_on_lines C.program fun k a x hx ↦ hv x (Or.inr ⟨k, a, hx⟩)

/-- If two input valuations agree on every input wire used by `C`, then `C.program.trace` agrees
on them. -/
lemma program_trace_eq_of_eq_on_usesInput {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1)
    {v₁ v₂ : Fin n → Bool} (hv : ∀ x, UsesInput C x → v₁ x = v₂ x)
    (k : Fin C.size) (a : Fin (Boolean.signature.Arity (C.program.lines k).op)) :
    C.program.trace Boolean.interpretation v₁ ((C.program.lines k).wires a) =
      C.program.trace Boolean.interpretation v₂ ((C.program.lines k).wires a) := by
  cases hw : (C.program.lines k).wires a with
  | input x =>
    simp only [Program.trace_input]
    exact hv x (Or.inr ⟨k, a, hw⟩)
  | gate j =>
    simp only [Program.trace_gateWire, Program.gateFunction_apply]
    exact congrFun (program_eval_eq_of_eq_on_usesInput C hv) j

/-- If two input valuations agree on every input wire used by `C`, then `C.eval` agrees on them.
-/
lemma eval_eq_of_eq_on_usesInput {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1)
    {v₁ v₂ : Fin n → Bool} (hv : ∀ x, UsesInput C x → v₁ x = v₂ x) :
    C.eval Boolean.interpretation v₁ = C.eval Boolean.interpretation v₂ :=
  C.dependsOn_eval Boolean.interpretation fun x hx ↦ hv x (Or.inl hx)

/-- A topological partition of a straight-line De Morgan Boolean circuit `C` into `m ≥ 1`
sequential computation blocks in the Micali–Reyzin OCL model: every input and internal gate wire
entering gate `k` belongs to a block at most `gateBlock k`. -/
@[ext]
structure OCLPartition {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1) (m : ℕ) where
  /-- Positive block count. -/
  pos : 1 ≤ m
  /-- Block assignment for each input wire. -/
  inputBlock : Fin n → Fin m
  /-- Block assignment for each internal gate. -/
  gateBlock : Fin C.size → Fin m
  /-- Topological ordering for input wires feeding a gate. -/
  input_le_gate : ∀ (k : Fin C.size) (a : Fin (Boolean.signature.Arity (C.program.lines k).op))
    (x : Fin n), (C.program.lines k).wires a = .input x → inputBlock x ≤ gateBlock k
  /-- Topological ordering for internal gate wires feeding a gate. -/
  gate_le_gate : ∀ (k : Fin C.size) (a : Fin (Boolean.signature.Arity (C.program.lines k).op))
    (j : Fin C.size), (C.program.lines k).wires a = .gate j → gateBlock j ≤ gateBlock k

/-- Trivial one-block OCL partition placing every input and gate in block `0`. -/
def OCLPartition.trivial {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1) :
    OCLPartition C 1 where
  pos := le_rfl
  inputBlock _ := 0
  gateBlock _ := 0
  input_le_gate _ _ _ _ := le_rfl
  gate_le_gate _ _ _ _ := le_rfl

@[simp]
lemma OCLPartition.trivial_inputBlock {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1)
    (x : Fin n) : (OCLPartition.trivial C).inputBlock x = 0 := by
  unfold OCLPartition.trivial; rfl

@[simp]
lemma OCLPartition.trivial_gateBlock {n : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1)
    (k : Fin C.size) : (OCLPartition.trivial C).gateBlock k = 0 := by
  unfold OCLPartition.trivial; rfl

/-- An `ℓ`-bounded adaptive OCL adversary against a partitioned circuit `(C, P)`: at each block
`b : Fin m`, given prior leakage from blocks `< b`, active input wires assigned to block `b`,
gate outputs in block `b`, and incoming operand wire values of gates in block `b`, outputs `ℓ`
bits of leakage. -/
@[ext]
structure OCLAdversary {n m : ℕ} (C : Cslib.Circuits.Circuit Boolean.signature n 1)
    (P : OCLPartition C m) (ℓ : ℕ) where
  /-- Adaptive leakage function at block `b`. -/
  leak : (b : Fin m) →
    (Fin b.1 → Fin ℓ → Bool) →
    (∀ x : Fin n, P.inputBlock x = b → UsesInput C x → Bool) →
    (∀ k : Fin C.size, P.gateBlock k = b → Bool) →
    (∀ k : Fin C.size, P.gateBlock k = b →
      Fin (Boolean.signature.Arity (C.program.lines k).op) → Bool) →
    (Fin ℓ → Bool)

/-- Prefix leakage transcript of blocks `0, ..., b - 1` produced by `adv` on valuation `v`. -/
def OCLAdversary.blockEval {n m ℓ : ℕ} {C : Cslib.Circuits.Circuit Boolean.signature n 1}
    {P : OCLPartition C m} (adv : OCLAdversary C P ℓ) (v : Fin n → Bool) :
    (b : ℕ) → b ≤ m → (Fin b → Fin ℓ → Bool)
  | 0, _ => Fin.elim0
  | b + 1, hb =>
    let prev := adv.blockEval v b (Nat.le_of_succ_le hb)
    let cur := adv.leak ⟨b, hb⟩ prev
      (fun x _ _ ↦ v x)
      (fun k _ ↦ C.program.eval Boolean.interpretation v k)
      (fun k _ a ↦ C.program.trace Boolean.interpretation v ((C.program.lines k).wires a))
    fun j ↦ if hj : j.1 < b then prev ⟨j.1, hj⟩ else cur

/-- Complete `m`-block adaptive leakage vector produced by `adv` on valuation `v`. -/
def OCLAdversary.run {n m ℓ : ℕ} {C : Cslib.Circuits.Circuit Boolean.signature n 1}
    {P : OCLPartition C m} (adv : OCLAdversary C P ℓ) (v : Fin n → Bool) :
    Fin m → Fin ℓ → Bool :=
  adv.blockEval v m le_rfl

private lemma OCLAdversary.blockEval_eq_of_eq_on_usesInput {n m ℓ : ℕ}
    {C : Cslib.Circuits.Circuit Boolean.signature n 1} {P : OCLPartition C m}
    (adv : OCLAdversary C P ℓ) {v₁ v₂ : Fin n → Bool}
    (hv : ∀ x, UsesInput C x → v₁ x = v₂ x) (b : ℕ) (hb : b ≤ m) :
    adv.blockEval v₁ b hb = adv.blockEval v₂ b hb := by
  induction b with
  | zero => funext j; exact Fin.elim0 j
  | succ b ih =>
    have hprev := ih (Nat.le_of_succ_le hb)
    have hIn : (fun (x : Fin n) (_ : P.inputBlock x = ⟨b, hb⟩) (_ : UsesInput C x) ↦ v₁ x) =
        (fun (x : Fin n) (_ : P.inputBlock x = ⟨b, hb⟩) (_ : UsesInput C x) ↦ v₂ x) := by
      funext x _ hx; exact hv x hx
    have hGate : (fun (k : Fin C.size) (_ : P.gateBlock k = ⟨b, hb⟩) ↦
          C.program.eval Boolean.interpretation v₁ k) =
        (fun (k : Fin C.size) (_ : P.gateBlock k = ⟨b, hb⟩) ↦
          C.program.eval Boolean.interpretation v₂ k) := by
      funext k _; exact congrFun (program_eval_eq_of_eq_on_usesInput C hv) k
    have hWire : (fun (k : Fin C.size) (_ : P.gateBlock k = ⟨b, hb⟩)
          (a : Fin (Boolean.signature.Arity (C.program.lines k).op)) ↦
          C.program.trace Boolean.interpretation v₁ ((C.program.lines k).wires a)) =
        (fun (k : Fin C.size) (_ : P.gateBlock k = ⟨b, hb⟩)
          (a : Fin (Boolean.signature.Arity (C.program.lines k).op)) ↦
          C.program.trace Boolean.interpretation v₂ ((C.program.lines k).wires a)) := by
      funext k _ a; exact program_trace_eq_of_eq_on_usesInput C hv k a
    dsimp only [OCLAdversary.blockEval]
    rw [hprev, hIn, hGate, hWire]

/-- If two valuations agree on every input variable used by `C`, any OCL adversary produces the
same leakage vector. -/
lemma OCLAdversary.run_eq_of_eq_on_usesInput {n m ℓ : ℕ}
    {C : Cslib.Circuits.Circuit Boolean.signature n 1} {P : OCLPartition C m}
    (adv : OCLAdversary C P ℓ) {v₁ v₂ : Fin n → Bool}
    (hv : ∀ x, UsesInput C x → v₁ x = v₂ x) :
    adv.run v₁ = adv.run v₂ :=
  adv.blockEval_eq_of_eq_on_usesInput hv m le_rfl

/-- A randomized straight-line De Morgan circuit equipped with an `m`-block OCL partition, taking
`n` input bits and `r` uniform random coin bits. -/
@[ext]
structure RandomizedOCLCircuit (n r m : ℕ) where
  /-- Underlying De Morgan circuit over `Fin (n + r)`. -/
  circuit : Cslib.Circuits.Circuit Boolean.signature (n + r) 1
  /-- Topological OCL block partition of `circuit`. -/
  partition : OCLPartition circuit m

/-- Distribution of the `m`-block adaptive leakage vector under uniform random coins `Fin r → Bool`
on input `x : Fin n → Bool`. -/
noncomputable def RandomizedOCLCircuit.leakageDist {n r m ℓ : ℕ}
    (RC : RandomizedOCLCircuit n r m) (adv : OCLAdversary RC.circuit RC.partition ℓ)
    (x : Fin n → Bool) : PMF (Fin m → Fin ℓ → Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin r → Bool)).map fun ρ ↦ adv.run (Fin.addCases x ρ)

/-- Raw-input OCL security: `RC` computes `f` on every coin assignment, and for all inputs `x, y`
with `f x = f y`, every `ℓ`-bounded OCL adversary induces leakage distributions within statistical
distance `ε`. -/
def IsOCLSecure {n r m : ℕ} (RC : RandomizedOCLCircuit n r m)
    (f : (Fin n → Bool) → Bool) (ℓ : ℕ) (ε : ℝ) : Prop :=
  (∀ (x : Fin n → Bool) (ρ : Fin r → Bool),
    RC.circuit.eval Boolean.interpretation (Fin.addCases x ρ) 0 = f x) ∧
  ∀ (adv : OCLAdversary RC.circuit RC.partition ℓ) (x y : Fin n → Bool),
    f x = f y → dist (RC.leakageDist adv x) (RC.leakageDist adv y) ≤ ε

/-- Characterization of `IsOCLSecure`. -/
lemma isOCLSecure_iff {n r m : ℕ} {RC : RandomizedOCLCircuit n r m}
    {f : (Fin n → Bool) → Bool} {ℓ : ℕ} {ε : ℝ} :
    IsOCLSecure RC f ℓ ε ↔
      (∀ (x : Fin n → Bool) (ρ : Fin r → Bool),
        RC.circuit.eval Boolean.interpretation (Fin.addCases x ρ) 0 = f x) ∧
      ∀ (adv : OCLAdversary RC.circuit RC.partition ℓ) (x y : Fin n → Bool),
        f x = f y → dist (RC.leakageDist adv x) (RC.leakageDist adv y) ≤ ε :=
  Iff.rfl

/-- Per-bit randomized input encoding lifting `bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool)`
independently to each coordinate of `x : Fin n → Bool`. -/
def encodeBits {n r₀ w : ℕ} (bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool))
    (x : Fin n → Bool) (coins : Fin n → Fin r₀ → Bool) : Fin (n * w) → Bool :=
  fun p ↦
    let q := finProdFinEquiv.symm p
    bitEnc (x q.1) (coins q.1) q.2

/-- Distribution of the `m`-block adaptive leakage vector on an input `x : Fin n → Bool` encoded
bitwise via `bitEnc` using independent uniform coins `Fin n → Fin r₀ → Bool`. -/
noncomputable def RandomizedOCLCircuit.encodedLeakageDist {n w r₀ r m ℓ : ℕ}
    (bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool))
    (RC : RandomizedOCLCircuit (n * w) r m) (adv : OCLAdversary RC.circuit RC.partition ℓ)
    (x : Fin n → Bool) : PMF (Fin m → Fin ℓ → Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → Fin r₀ → Bool)).bind fun coins ↦
    RC.leakageDist adv (encodeBits bitEnc x coins)

/-- Bitwise-encoded OCL security: `(bitEnc, RC)` computes `f` on every encoding and circuit coin
assignment, and for all `x, y` with `f x = f y`, every `ℓ`-bounded OCL adversary induces encoded
leakage distributions within statistical distance `ε`. -/
def IsEncodedOCLSecure {n w r₀ r m : ℕ} (bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool))
    (RC : RandomizedOCLCircuit (n * w) r m) (f : (Fin n → Bool) → Bool) (ℓ : ℕ) (ε : ℝ) : Prop :=
  (∀ (x : Fin n → Bool) (coins : Fin n → Fin r₀ → Bool) (ρ : Fin r → Bool),
    RC.circuit.eval Boolean.interpretation (Fin.addCases (encodeBits bitEnc x coins) ρ) 0 = f x) ∧
  ∀ (adv : OCLAdversary RC.circuit RC.partition ℓ) (x y : Fin n → Bool),
    f x = f y →
      dist (RC.encodedLeakageDist bitEnc adv x) (RC.encodedLeakageDist bitEnc adv y) ≤ ε

/-- Characterization of `IsEncodedOCLSecure`. -/
lemma isEncodedOCLSecure_iff {n w r₀ r m : ℕ}
    {bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool)}
    {RC : RandomizedOCLCircuit (n * w) r m} {f : (Fin n → Bool) → Bool} {ℓ : ℕ} {ε : ℝ} :
    IsEncodedOCLSecure bitEnc RC f ℓ ε ↔
      (∀ (x : Fin n → Bool) (coins : Fin n → Fin r₀ → Bool) (ρ : Fin r → Bool),
        RC.circuit.eval Boolean.interpretation
          (Fin.addCases (encodeBits bitEnc x coins) ρ) 0 = f x) ∧
      ∀ (adv : OCLAdversary RC.circuit RC.partition ℓ) (x y : Fin n → Bool),
        f x = f y →
          dist (RC.encodedLeakageDist bitEnc adv x) (RC.encodedLeakageDist bitEnc adv y) ≤ ε :=
  Iff.rfl

end OCLModel

/-! ### Base-Case OCL Security and Unshielded Parity Separation -/

section BaseAndSharpness

/-- Any randomized OCL circuit computing `f` is unconditionally `(0, 0)`-OCL-secure. -/
theorem isOCLSecure_zero_leakage {n r m : ℕ} (RC : RandomizedOCLCircuit n r m)
    {f : (Fin n → Bool) → Bool}
    (hcomp : ∀ (x : Fin n → Bool) (ρ : Fin r → Bool),
      RC.circuit.eval Boolean.interpretation (Fin.addCases x ρ) 0 = f x) :
    IsOCLSecure RC f 0 0 := by
  refine ⟨hcomp, fun adv x y _ ↦ ?_⟩
  have hsub : Subsingleton (Fin m → Fin 0 → Bool) :=
    ⟨fun a b ↦ funext fun _ ↦ funext fun i ↦ Fin.elim0 i⟩
  have heq : RC.leakageDist adv x = RC.leakageDist adv y := by
    ext t
    simp only [RandomizedOCLCircuit.leakageDist, PMF.map_apply]
    refine tsum_congr fun ρ ↦ ?_
    congr 1
    exact propext (by constructor <;> intro _ <;> exact Subsingleton.elim _ _)
  rw [heq, dist_self]

/-- Any bitwise-encoded randomized OCL circuit computing `f` is unconditionally `(0, 0)`-OCL-secure.
-/
theorem isEncodedOCLSecure_zero_leakage {n w r₀ r m : ℕ}
    (bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool))
    (RC : RandomizedOCLCircuit (n * w) r m) {f : (Fin n → Bool) → Bool}
    (hcomp : ∀ (x : Fin n → Bool) (coins : Fin n → Fin r₀ → Bool) (ρ : Fin r → Bool),
      RC.circuit.eval Boolean.interpretation (Fin.addCases (encodeBits bitEnc x coins) ρ) 0 = f x) :
    IsEncodedOCLSecure bitEnc RC f 0 0 := by
  refine ⟨hcomp, fun adv x y _ ↦ ?_⟩
  have hsub : Subsingleton (Fin m → Fin 0 → Bool) :=
    ⟨fun a b ↦ funext fun _ ↦ funext fun i ↦ Fin.elim0 i⟩
  have heq : RC.encodedLeakageDist bitEnc adv x = RC.encodedLeakageDist bitEnc adv y := by
    ext t
    simp only [RandomizedOCLCircuit.encodedLeakageDist, RandomizedOCLCircuit.leakageDist,
      PMF.bind_apply, PMF.map_apply]
    refine tsum_congr fun coins ↦ ?_
    congr 1
    refine tsum_congr fun ρ ↦ ?_
    congr 1
    exact propext (by constructor <;> intro _ <;> exact Subsingleton.elim _ _)
  rw [heq, dist_self]

/-- Any randomized OCL circuit ignoring all `Fin n` input wires and computing constant `b : Bool`
is `0`-OCL-secure for every leakage bound `ℓ`. -/
theorem isOCLSecure_const {n r m : ℕ} (RC : RandomizedOCLCircuit n r m) (b : Bool)
    (hign : ∀ i : Fin n, ¬ UsesInput RC.circuit (Fin.castAdd r i))
    (hcomp : ∀ (x : Fin n → Bool) (ρ : Fin r → Bool),
      RC.circuit.eval Boolean.interpretation (Fin.addCases x ρ) 0 = b)
    (ℓ : ℕ) :
    IsOCLSecure RC (fun _ ↦ b) ℓ 0 := by
  refine ⟨hcomp, fun adv x y _ ↦ ?_⟩
  have heq : RC.leakageDist adv x = RC.leakageDist adv y := by
    simp only [RandomizedOCLCircuit.leakageDist]
    congr 1
    funext ρ
    refine adv.run_eq_of_eq_on_usesInput fun z hz ↦ ?_
    revert hz
    exact Fin.addCases (fun i hi ↦ False.elim (hign i hi)) (fun _ _ ↦ by simp) z
  rw [heq, dist_self]

/-- Any bitwise-encoded randomized OCL circuit ignoring all encoded input wires and computing
constant `b : Bool` is `0`-OCL-secure for every leakage bound `ℓ`. -/
theorem isEncodedOCLSecure_const {n w r₀ r m : ℕ}
    (bitEnc : Bool → (Fin r₀ → Bool) → (Fin w → Bool))
    (RC : RandomizedOCLCircuit (n * w) r m) (b : Bool)
    (hign : ∀ i : Fin (n * w), ¬ UsesInput RC.circuit (Fin.castAdd r i))
    (hcomp : ∀ (x : Fin n → Bool) (coins : Fin n → Fin r₀ → Bool) (ρ : Fin r → Bool),
      RC.circuit.eval Boolean.interpretation (Fin.addCases (encodeBits bitEnc x coins) ρ) 0 = b)
    (ℓ : ℕ) :
    IsEncodedOCLSecure bitEnc RC (fun _ ↦ b) ℓ 0 := by
  refine ⟨hcomp, fun adv x y _ ↦ ?_⟩
  have heq : RC.encodedLeakageDist bitEnc adv x = RC.encodedLeakageDist bitEnc adv y := by
    simp only [RandomizedOCLCircuit.encodedLeakageDist, RandomizedOCLCircuit.leakageDist]
    congr 1
    funext coins
    congr 1
    funext ρ
    refine adv.run_eq_of_eq_on_usesInput fun z hz ↦ ?_
    revert hz
    exact Fin.addCases (fun i hi ↦ False.elim (hign i hi)) (fun _ _ ↦ by simp) z
  rw [heq, dist_self]

/-- Impossibility of raw-input OCL security for parity: for any randomness count `r`, block count
`m`, and `RC : RandomizedOCLCircuit 2 r m`, `RC` fails raw `IsOCLSecure` at `ℓ = 1` for all
`ε < 1`, explaining why OCL compilers require randomized input encoding. -/
theorem not_isOCLSecure_raw_xor {r m : ℕ} (RC : RandomizedOCLCircuit 2 r m) {ε : ℝ}
    (hε : ε < 1) :
    ¬ IsOCLSecure RC (fun v ↦ bne (v 0) (v 1)) 1 ε := by
  rintro ⟨hcomp, hsec⟩
  let i0 : Fin (2 + r) := Fin.castAdd r (0 : Fin 2)
  have huses : UsesInput RC.circuit i0 := by
    by_contra hno
    have h00 := hcomp ![false, false] (fun _ ↦ false)
    have h10 := hcomp ![true, false] (fun _ ↦ false)
    have heq : RC.circuit.eval Boolean.interpretation
          (Fin.addCases ![false, false] (fun _ : Fin r ↦ false)) =
        RC.circuit.eval Boolean.interpretation
          (Fin.addCases ![true, false] (fun _ : Fin r ↦ false)) := by
      refine eval_eq_of_eq_on_usesInput RC.circuit fun z hz ↦ ?_
      revert hz
      refine Fin.addCases (fun i hi ↦ ?_) (fun _ _ ↦ by simp) z
      fin_cases i
      · exact False.elim (hno hi)
      · rfl
    have heq0 := congrFun heq 0
    rw [h00, h10] at heq0
    exact absurd heq0 (by decide)
  let b₀ : Fin m := RC.partition.inputBlock i0
  let adv : OCLAdversary RC.circuit RC.partition 1 :=
    { leak := fun b _ inps _ _ ↦ fun _ ↦
        if hb : b = b₀ then inps i0 hb.symm huses else false }
  let x : Fin 2 → Bool := ![false, false]
  let y : Fin 2 → Bool := ![true, true]
  have hf : bne (x 0) (x 1) = bne (y 0) (y 1) := by decide
  have hle := hsec adv x y hf
  have hblock : ∀ (v : Fin 2 → Bool) (ρ : Fin r → Bool) (b : ℕ) (hb : b ≤ m)
      (j : Fin b), adv.blockEval (Fin.addCases v ρ) b hb j =
        fun _ ↦ if j.1 = b₀.1 then v 0 else false := by
    intro v ρ b hb j
    induction b with
    | zero => exact Fin.elim0 j
    | succ b ih =>
      dsimp only [OCLAdversary.blockEval]
      by_cases hj : j.1 < b
      · simp only [hj, ↓reduceDIte]
        exact ih (Nat.le_of_succ_le hb) ⟨j.1, hj⟩
      · simp only [hj, ↓reduceDIte]
        have hjEq : j.1 = b := by omega
        funext _
        dsimp only [adv]
        by_cases hb0 : (⟨b, hb⟩ : Fin m) = b₀
        · have hbVal : b = b₀.1 := congrArg Fin.val hb0
          have hi0 : Fin.addCases v ρ i0 = v 0 := by simp [i0]
          simp [hjEq, hbVal, hi0]
        · have hne : b ≠ b₀.1 := fun h ↦ hb0 (Fin.ext h)
          simp [hjEq, hne, hb0]
  have hrunx : ∀ ρ : Fin r → Bool, adv.run (Fin.addCases x ρ) = fun _ _ ↦ false := by
    intro ρ; funext j _; rw [OCLAdversary.run, hblock x ρ m le_rfl j]; simp [x]
  have hruny : ∀ ρ : Fin r → Bool,
      adv.run (Fin.addCases y ρ) = fun j _ ↦ if j.1 = b₀.1 then true else false := by
    intro ρ; funext j _; rw [OCLAdversary.run, hblock y ρ m le_rfl j]; simp [y]
  have hdx : RC.leakageDist adv x = PMF.pure (fun _ _ ↦ false) := by
    rw [RandomizedOCLCircuit.leakageDist]
    simp_rw [hrunx]
    exact PMF.map_const _ _
  have hdy : RC.leakageDist adv y =
      PMF.pure (fun j _ ↦ if j.1 = b₀.1 then true else false) := by
    rw [RandomizedOCLCircuit.leakageDist]
    simp_rw [hruny]
    exact PMF.map_const _ _
  have hne : (fun (_ : Fin m) (_ : Fin 1) ↦ false) ≠
      (fun j _ ↦ if j.1 = b₀.1 then true else false) := by
    intro h
    have h0 := congrFun (congrFun h b₀) 0
    simp at h0
  have hdisj : Disjoint (PMF.pure (fun (_ : Fin m) (_ : Fin 1) ↦ false)).support
      (PMF.pure (fun j _ ↦ if j.1 = b₀.1 then true else false)).support := by
    rw [PMF.support_pure, PMF.support_pure, Set.disjoint_singleton]
    exact hne
  rw [hdx, hdy, Cslib.Probability.PMF.dist_eq_one_of_disjoint_support hdisj] at hle
  linarith

end BaseAndSharpness

/-! ### Group NAND Gate Gadgets and `SL(2, F)` Realization -/

section GroupGadgets

/-- Concrete four-element field `𝔽₄ = 𝔽₂[ω]/(ω² + ω + 1)` used internally to witness
`GroupGateGadget` in `SL(2, F)` via `decide +kernel`. -/
@[ext]
private structure GF4 where
  c0 : ZMod 2
  c1 : ZMod 2
  deriving DecidableEq

namespace GF4

private instance instFintype : Fintype GF4 :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2)
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun a ↦ (a.c0, a.c1), fun _ ↦ rfl, fun _ ↦ rfl⟩

private lemma card : Fintype.card GF4 = 4 := by decide

private def zero : GF4 := ⟨0, 0⟩
private def one : GF4 := ⟨1, 0⟩
private def omega : GF4 := ⟨0, 1⟩

private instance : Zero GF4 := ⟨zero⟩
private instance : One GF4 := ⟨one⟩
private instance : Inhabited GF4 := ⟨0⟩
private instance : Nontrivial GF4 := ⟨⟨0, 1, by decide⟩⟩

private instance : Add GF4 := ⟨fun a b ↦ ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
private instance : Neg GF4 := ⟨fun a ↦ a⟩
private instance : Sub GF4 := ⟨fun a b ↦ ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
private instance : Mul GF4 :=
  ⟨fun a b ↦ ⟨a.c0 * b.c0 + a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c1⟩⟩
private instance : Inv GF4 := ⟨fun a ↦ a * a⟩

private instance : AddCommGroup GF4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  nsmul n a := if n % 2 = 0 then 0 else a
  nsmul_zero := by decide
  nsmul_succ n a := by
    change (if (n + 1) % 2 = 0 then 0 else a) = (if n % 2 = 0 then 0 else a) + a
    rw [Nat.add_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> revert a <;> decide
  neg_add_cancel := by decide
  add_comm := by decide
  zsmul k a := if k % 2 = 0 then 0 else a
  zsmul_zero' := by decide
  zsmul_succ' n a := by
    change (if ((n.succ : ℕ) : ℤ) % 2 = 0 then 0 else a) =
      (if (n : ℤ) % 2 = 0 then 0 else a) + a
    norm_cast
    rw [Nat.succ_eq_add_one, Nat.add_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> revert a <;> decide
  zsmul_neg' n a := by
    change (if Int.negSucc n % 2 = 0 then 0 else a) =
      -(if ((n.succ : ℕ) : ℤ) % 2 = 0 then 0 else a)
    have hneg : ∀ x : GF4, -x = x := fun _ ↦ rfl
    rw [hneg]
    split_ifs <;> first | rfl | omega
  sub_eq_add_neg := by decide

private instance : CommRing GF4 where
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  natCast n := if n % 2 = 0 then 0 else 1
  natCast_zero := by decide
  natCast_succ n := by
    change (if (n + 1) % 2 = 0 then 0 else (1 : GF4)) =
      (if n % 2 = 0 then 0 else (1 : GF4)) + 1
    rw [Nat.add_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp only [h] <;> decide
  intCast k := if k % 2 = 0 then 0 else 1
  intCast_ofNat n := by
    change (if (n : ℤ) % 2 = 0 then 0 else (1 : GF4)) = if n % 2 = 0 then 0 else (1 : GF4)
    norm_cast
  intCast_negSucc n := by
    change (if Int.negSucc n % 2 = 0 then 0 else (1 : GF4)) =
      -(if (n + 1) % 2 = 0 then 0 else (1 : GF4))
    have h0 : (-0 : GF4) = 0 := rfl
    have h1 : (-1 : GF4) = 1 := rfl
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
    · have h2 : Int.negSucc n % 2 = 0 := by omega
      simp [h2, h, h0]
    · have h2 : Int.negSucc n % 2 ≠ 0 := by omega
      simp [h2, h, h1]

private instance : Field GF4 where
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ ↦ rfl
  qsmul := _
  qsmul_def := fun _ _ ↦ rfl

private instance : CharP GF4 2 where
  cast_eq_zero_iff n := by
    change (if n % 2 = 0 then (0 : GF4) else 1) = 0 ↔ 2 ∣ n
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private instance : Algebra (ZMod 2) GF4 := ZMod.algebra GF4 2

private lemma finrank_zmod2 : Module.finrank (ZMod 2) GF4 = 2 := by
  have h := FiniteField.pow_finrank_eq_card 2 GF4
  rw [card] at h
  have h2 : (2 : ℕ) ^ 2 = 4 := by decide
  rw [← h2] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h

end GF4

/-- Evaluation of a single conjugation step `(u, inv, idx)` in `G` on inputs `x₀, x₁ : Bool` with
canonical generator `gen : G`. -/
@[expose] def evalWordOp {G : Type u} [Group G] (gen : G) (x₀ x₁ : Bool)
    (op : G × Bool × Fin 2) : G :=
  let b := if op.2.2 = 0 then x₀ else x₁
  let base := if b then (if op.2.1 then gen⁻¹ else gen) else 1
  op.1 * base * op.1⁻¹

/-- Evaluation of a conjugate-word NAND gadget `w` over `G` on `(x₀, x₁ : Bool)`. -/
@[expose] def evalNandWord {G : Type u} [Group G] (gen : G) (w : List (G × Bool × Fin 2))
    (x₀ x₁ : Bool) : G :=
  gen * (w.map (evalWordOp gen x₀ x₁)).prod

/-- A concrete Barrington-style conjugate-word NAND gate gadget over a group `G`: a non-identity
generator `gen ≠ 1` and a word of conjugates of `(gen^{± x_idx})` computing `gen^{!(x₀ && x₁)}`. -/
structure GroupGateGadget (G : Type u) [Group G] where
  /-- Non-identity encoding generator for `true`. -/
  gen : G
  /-- Non-triviality condition `gen ≠ 1`. -/
  gen_ne_one : gen ≠ 1
  /-- List of conjugation instructions `(u, inv, idx)`. -/
  nandWord : List (G × Bool × Fin 2)
  /-- Exact NAND evaluation specification. -/
  eval_nandWord : ∀ x₀ x₁ : Bool,
    evalNandWord gen nandWord x₀ x₁ = if !(x₀ && x₁) then gen else 1

/-- Pushforward of a `GroupGateGadget` along an injective group homomorphism. -/
def GroupGateGadget.map {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (g : GroupGateGadget G) : GroupGateGadget H where
  gen := φ g.gen
  gen_ne_one h := g.gen_ne_one (hφ (h.trans (map_one φ).symm))
  nandWord := g.nandWord.map fun (u, inv, idx) ↦ (φ u, inv, idx)
  eval_nandWord x₀ x₁ := by
    have hmap : evalNandWord (φ g.gen) (g.nandWord.map fun (u, inv, idx) ↦ (φ u, inv, idx))
        x₀ x₁ = φ (evalNandWord g.gen g.nandWord x₀ x₁) := by
      simp only [evalNandWord, List.map_map, map_mul, map_list_prod]
      congr 2
      refine List.map_congr_left fun ⟨u, inv, idx⟩ _ ↦ ?_
      dsimp only [Function.comp_def, evalWordOp]
      fin_cases idx <;> cases inv <;> simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte,
        Bool.false_eq_true]
      · cases x₀ <;> simp [map_mul, map_inv]
      · cases x₀ <;> simp [map_mul, map_inv]
      · cases x₁ <;> simp [map_mul, map_inv]
      · cases x₁ <;> simp [map_mul, map_inv]
    rw [hmap, g.eval_nandWord x₀ x₁]
    by_cases h0 : x₀ <;> by_cases h1 : x₁ <;> simp [h0, h1]

@[simp]
lemma GroupGateGadget.map_gen {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (g : GroupGateGadget G) :
    (g.map φ hφ).gen = φ g.gen := by
  unfold GroupGateGadget.map; rfl

@[simp]
lemma GroupGateGadget.map_nandWord {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (g : GroupGateGadget G) :
    (g.map φ hφ).nandWord = g.nandWord.map fun (u, inv, idx) ↦ (φ u, inv, idx) := by
  unfold GroupGateGadget.map; rfl

/-- No commutative group has a `GroupGateGadget`. -/
theorem not_exists_groupGateGadget_of_commGroup (G : Type u) [CommGroup G] :
    ¬ Nonempty (GroupGateGadget G) := by
  rintro ⟨⟨gen, hne, w, heval⟩⟩
  have hcomm : ∀ x₀ x₁ : Bool,
      evalNandWord gen w x₀ x₁ =
        gen * ((w.map fun op ↦
          let b := if op.2.2 = 0 then x₀ else x₁
          if b then (if op.2.1 then gen⁻¹ else gen) else 1)).prod := by
    intro x₀ x₁
    simp only [evalNandWord]
    congr 2
    refine List.map_congr_left fun op _ ↦ ?_
    simp only [evalWordOp]
    rw [mul_assoc, mul_comm _ op.1⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hprod : evalNandWord gen w false false * evalNandWord gen w true true =
      evalNandWord gen w true false * evalNandWord gen w false true := by
    rw [hcomm false false, hcomm true true, hcomm true false, hcomm false true]
    have hlist : ∀ l : List (G × Bool × Fin 2),
        (l.map fun op ↦ if (if op.2.2 = 0 then false else false) then
          (if op.2.1 then gen⁻¹ else gen) else 1).prod *
        (l.map fun op ↦ if (if op.2.2 = 0 then true else true) then
          (if op.2.1 then gen⁻¹ else gen) else 1).prod =
        (l.map fun op ↦ if (if op.2.2 = 0 then true else false) then
          (if op.2.1 then gen⁻¹ else gen) else 1).prod *
        (l.map fun op ↦ if (if op.2.2 = 0 then false else true) then
          (if op.2.1 then gen⁻¹ else gen) else 1).prod := by
      intro l
      induction l with
      | nil => simp
      | cons op t ih =>
        simp only [List.map_cons, List.prod_cons]
        have hhd : (if (if op.2.2 = 0 then false else false) then
            (if op.2.1 then gen⁻¹ else gen) else 1) *
          (if (if op.2.2 = 0 then true else true) then
            (if op.2.1 then gen⁻¹ else gen) else 1) =
          (if (if op.2.2 = 0 then true else false) then
            (if op.2.1 then gen⁻¹ else gen) else 1) *
          (if (if op.2.2 = 0 then false else true) then
            (if op.2.1 then gen⁻¹ else gen) else 1) := by
          rcases Fin.exists_fin_two.mp ⟨op.2.2, rfl⟩ with h0 | h0 <;> simp [h0]
        calc _ = ((if (if op.2.2 = 0 then false else false) then
            (if op.2.1 then gen⁻¹ else gen) else 1) *
          (if (if op.2.2 = 0 then true else true) then
            (if op.2.1 then gen⁻¹ else gen) else 1)) *
          ((t.map fun op ↦ if (if op.2.2 = 0 then false else false) then
            (if op.2.1 then gen⁻¹ else gen) else 1).prod *
          (t.map fun op ↦ if (if op.2.2 = 0 then true else true) then
            (if op.2.1 then gen⁻¹ else gen) else 1).prod) := by ac_rfl
          _ = ((if (if op.2.2 = 0 then true else false) then
            (if op.2.1 then gen⁻¹ else gen) else 1) *
          (if (if op.2.2 = 0 then false else true) then
            (if op.2.1 then gen⁻¹ else gen) else 1)) *
          ((t.map fun op ↦ if (if op.2.2 = 0 then true else false) then
            (if op.2.1 then gen⁻¹ else gen) else 1).prod *
          (t.map fun op ↦ if (if op.2.2 = 0 then false else true) then
            (if op.2.1 then gen⁻¹ else gen) else 1).prod) := by rw [hhd, ih]
          _ = _ := by ac_rfl
    calc _ = (gen * gen) * _ := by rw [mul_mul_mul_comm]
      _ = (gen * gen) * _ := by rw [hlist w]
      _ = _ := by rw [← mul_mul_mul_comm]
  rw [heval false false, heval true true, heval true false, heval false true] at hprod
  simp only [Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true, ↓reduceIte] at hprod
  exact hne (mul_left_cancel (a := gen) hprod.symm)

private def sl2GF4GroupGateGadget : GroupGateGadget (Matrix.SpecialLinearGroup (Fin 2) GF4) :=
  let gen : Matrix.SpecialLinearGroup (Fin 2) GF4 :=
    ⟨!![GF4.omega, 1; 1, 0], by decide +kernel⟩
  let u : Matrix.SpecialLinearGroup (Fin 2) GF4 :=
    ⟨!![0, 1; 1, GF4.omega + 1], by decide +kernel⟩
  let v : Matrix.SpecialLinearGroup (Fin 2) GF4 :=
    ⟨!![0, GF4.omega; GF4.omega + 1, 0], by decide +kernel⟩
  { gen := gen
    gen_ne_one := fun h ↦ by
      have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
      exact absurd h00 (by decide +kernel)
    nandWord := [(u, false, 0), (v, false, 1), (u, true, 0), (v, true, 1)]
    eval_nandWord := fun x₀ x₁ ↦ by
      cases x₀ <;> cases x₁ <;>
        exact Subtype.ext (Matrix.ext fun i j ↦ by
          fin_cases i <;> fin_cases j <;> decide +kernel) }

private def sl2OfGF4RingHom {F : Type u} [CommRing F] [Nontrivial F] (φ : GF4 →+* F) :
    GroupGateGadget (Matrix.SpecialLinearGroup (Fin 2) F) :=
  sl2GF4GroupGateGadget.map (Matrix.SpecialLinearGroup.map φ) fun _ _ hAB ↦
    Subtype.ext (Matrix.ext fun i j ↦
      φ.injective (congrFun (congrFun (congrArg Subtype.val hAB) i) j))

/-- Every finite field `F` of characteristic `2` and even `ZMod 2`-dimension has a length-`4`
`GroupGateGadget` in `SL(2, F)`. -/
theorem exists_sl2_groupGateGadget_of_even_finrank (F : Type u) [Field F] [Finite F]
    [Algebra (ZMod 2) F] (hdiv : 2 ∣ Module.finrank (ZMod 2) F) :
    ∃ g : GroupGateGadget (Matrix.SpecialLinearGroup (Fin 2) F), g.nandWord.length = 4 := by
  have hdiv' : Module.finrank (ZMod 2) GF4 ∣ Module.finrank (ZMod 2) F := by
    rw [GF4.finrank_zmod2]
    exact hdiv
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := GF4) (L := F) hdiv'
  exact ⟨sl2OfGF4RingHom φ.toRingHom, by
    dsimp only [sl2OfGF4RingHom, GroupGateGadget.map]
    rw [List.length_map]
    rfl⟩

/-- Every finite field `F` of characteristic `2` and even `ZMod 2`-dimension has a concrete
`GroupGateGadget` in `SL(2, F)`. -/
theorem nonempty_sl2_groupGateGadget_of_even_finrank (F : Type u) [Field F] [Finite F]
    [Algebra (ZMod 2) F] (hdiv : 2 ∣ Module.finrank (ZMod 2) F) :
    Nonempty (GroupGateGadget (Matrix.SpecialLinearGroup (Fin 2) F)) :=
  let ⟨g, _⟩ := exists_sl2_groupGateGadget_of_even_finrank F hdiv
  ⟨g⟩

/-- Every finite field `F` of cardinality `4^m` has a length-`4` `GroupGateGadget` in
`SL(2, F)`. -/
theorem exists_sl2_groupGateGadget_of_card_eq_four_pow (F : Type u) [Field F] [Fintype F]
    (m : ℕ) (hcard : Fintype.card F = 4 ^ m) :
    ∃ g : GroupGateGadget (Matrix.SpecialLinearGroup (Fin 2) F), g.nandWord.length = 4 := by
  obtain ⟨p, hchar, n, hp, hcardp⟩ := FiniteField.card' (K := F)
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ (2 * m) := by
      have hpow : p ^ (n : ℕ) = 2 ^ (2 * m) := by
        rw [← hcardp, hcard]
        have h4 : (4 : ℕ) = 2 ^ 2 := rfl
        rw [h4, ← pow_mul]
      rw [← hpow]
      exact dvd_pow_self p n.ne_zero
    exact ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)).resolve_left hp.ne_one
  subst hp2
  let : CharP F 2 := hchar
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfin : Module.finrank (ZMod 2) F = 2 * m := by
    have hpow : 2 ^ Module.finrank (ZMod 2) F = 2 ^ (2 * m) := by
      rw [FiniteField.pow_finrank_eq_card 2 F, hcard]
      have h4 : (4 : ℕ) = 2 ^ 2 := rfl
      rw [h4, ← pow_mul]
    exact Nat.pow_right_injective (by decide : 1 < 2) hpow
  exact exists_sl2_groupGateGadget_of_even_finrank F ⟨m, hfin⟩

/-- Every finite field `F` of cardinality `4^m` has a concrete `GroupGateGadget` in `SL(2, F)`.
-/
theorem nonempty_sl2_groupGateGadget_of_card_eq_four_pow (F : Type u) [Field F] [Fintype F]
    (m : ℕ) (hcard : Fintype.card F = 4 ^ m) :
    Nonempty (GroupGateGadget (Matrix.SpecialLinearGroup (Fin 2) F)) :=
  let ⟨g, _⟩ := exists_sl2_groupGateGadget_of_card_eq_four_pow F m hcard
  ⟨g⟩

end GroupGadgets

end Cslib.Circuits.LeakageResilience
