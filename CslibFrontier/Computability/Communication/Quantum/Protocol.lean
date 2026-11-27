/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CslibFrontier.Computability.Communication.Quantum.MatrixNorms

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Quantum Communication Protocols with Unlimited Shared Entanglement

This module defines canonical two-party Quantum Merlin–Arthur communication protocols
`QuantumCommProtocol X Y w` with **unlimited finite-dimensional shared entanglement**, a
`w`-qubit witness held by Bob, and `comm` 1-qubit messages exchanged between Alice and Bob,
together with the Yao–Kremer transcript decomposition (`opA`, `opB`), forward and adjoint `2^c`
norm bounds, and acceptance-probability bounds.

## Main definitions

* `CslibFrontier.CommunicationComplexity.QuantumCommProtocol`: canonical two-party QMA quantum
  communication protocol with unlimited shared entanglement.
* `CslibFrontier.CommunicationComplexity.QuantumCommProtocol.acceptProb`: acceptance probability on
  `(x, y)` and witness `ψ`.
* `CslibFrontier.CommunicationComplexity.QuantumCommProtocol.Computes`: completeness and soundness
  specification.
* `CslibFrontier.CommunicationComplexity.qmaCommComplexity`: $\mathrm{QMA}^{cc}(F) = \min (w + c)$.

## Main results

* `CslibFrontier.CommunicationComplexity.QuantumCommProtocol.yao_kremer_finalState`: Yao–Kremer
  transcript decomposition of the final state.
* `CslibFrontier.CommunicationComplexity.QuantumCommProtocol.acceptProb_nonneg` and
  `acceptProb_le_one`: probability bounds on `acceptProb`.
* `CslibFrontier.CommunicationComplexity.QuantumCommProtocol.sum_norm_sq_opA_le` and
  `sum_norm_sq_opB_le`: $2^c$ norm bounds on Yao–Kremer transcript operators.
-/

public section

open scoped BigOperators
open Finset Matrix Cslib

namespace CslibFrontier.CommunicationComplexity

/-! ### Canonical Quantum Communication Protocols with Unlimited Shared Entanglement -/

/-- A two-party Quantum Merlin–Arthur communication protocol on `X × Y` with a `w`-qubit quantum
witness (held by Bob), unlimited finite-dimensional shared entanglement `entState`, and `comm`
1-qubit messages exchanged between Alice and Bob. -/
structure QuantumCommProtocol (X Y : Type*) (w : ℕ) where
  /-- Alice's finite private workspace basis. -/
  WorkA : Type
  [fintypeWorkA : Fintype WorkA]
  [decidableEqWorkA : DecidableEq WorkA]
  /-- Bob's finite private workspace basis. -/
  WorkB : Type
  [fintypeWorkB : Fintype WorkB]
  [decidableEqWorkB : DecidableEq WorkB]
  /-- Alice's finite entanglement register basis (unbounded dimension). -/
  EntA : Type
  [fintypeEntA : Fintype EntA]
  [decidableEqEntA : DecidableEq EntA]
  /-- Bob's finite entanglement register basis (unbounded dimension). -/
  EntB : Type
  [fintypeEntB : Fintype EntB]
  [decidableEqEntB : DecidableEq EntB]
  /-- Number of 1-qubit messages communicated. -/
  comm : ℕ
  /-- Speaker schedule: `false` = Alice acts and sends message `r`; `true` = Bob acts and sends. -/
  speaker : Fin comm → Bool
  /-- Alice's local unitaries on `(WorkA × EntA) × Bool` (for turns with `speaker r = false`). -/
  aliceU : Fin comm → X →
    EuclideanSpace ℂ ((WorkA × EntA) × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((WorkA × EntA) × Bool)
  /-- Bob's local unitaries on `(BitString w × WorkB × EntB) × Bool` (`speaker r = true`). -/
  bobU : Fin comm → Y →
    EuclideanSpace ℂ ((BitString w × WorkB × EntB) × Bool) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((BitString w × WorkB × EntB) × Bool)
  /-- Bob's final local unitary before measurement. -/
  finalBobU : Y →
    EuclideanSpace ℂ ((BitString w × WorkB × EntB) × Bool) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((BitString w × WorkB × EntB) × Bool)
  /-- Alice's fixed initial workspace basis state. -/
  initA : WorkA
  /-- Bob's fixed initial workspace basis state. -/
  initB : WorkB
  /-- Arbitrary unit shared entangled state on `EntA × EntB`. -/
  entState : EuclideanSpace ℂ (EntA × EntB)
  /-- Normalization of the shared entangled state. -/
  norm_entState : ‖entState‖ = 1
  /-- Accepting outcomes on Bob's final register `(BitString w × WorkB × EntB) × Bool`. -/
  accept : Finset ((BitString w × WorkB × EntB) × Bool)

attribute [instance] QuantumCommProtocol.fintypeWorkA QuantumCommProtocol.decidableEqWorkA
  QuantumCommProtocol.fintypeWorkB QuantumCommProtocol.decidableEqWorkB
  QuantumCommProtocol.fintypeEntA QuantumCommProtocol.decidableEqEntA
  QuantumCommProtocol.fintypeEntB QuantumCommProtocol.decidableEqEntB

namespace QuantumCommProtocol

variable {X Y : Type*} {w : ℕ}

/-- Alice's private + entanglement register basis. -/
abbrev HA (P : QuantumCommProtocol X Y w) : Type := P.WorkA × P.EntA

/-- Bob's witness + private + entanglement register basis. -/
abbrev HB (P : QuantumCommProtocol X Y w) : Type := BitString w × P.WorkB × P.EntB

/-- Joint computational basis `(HA × HB) × Bool`. -/
abbrev Joint (P : QuantumCommProtocol X Y w) : Type := (P.HA × P.HB) × Bool

/-- Initial joint state for witness `ψ`. -/
noncomputable def initState (P : QuantumCommProtocol X Y w)
    (ψ : EuclideanSpace ℂ (BitString w)) : EuclideanSpace ℂ P.Joint :=
  WithLp.toLp 2 fun p =>
    if p.1.1.1 = P.initA ∧ p.1.2.2.1 = P.initB ∧ p.2 = false then
      ψ.ofLp p.1.2.1 * P.entState.ofLp (p.1.1.2, p.1.2.2.2)
    else 0

lemma initState_apply (P : QuantumCommProtocol X Y w)
    (ψ : EuclideanSpace ℂ (BitString w)) (p : P.Joint) :
    (P.initState ψ).ofLp p =
      if p.1.1.1 = P.initA ∧ p.1.2.2.1 = P.initB ∧ p.2 = false then
        ψ.ofLp p.1.2.1 * P.entState.ofLp (p.1.1.2, p.1.2.2.2)
      else 0 := by rfl

@[simp]
lemma initState_zero (P : QuantumCommProtocol X Y w) :
    P.initState 0 = 0 := by
  ext p; simp [initState]

@[simp]
lemma initState_add (P : QuantumCommProtocol X Y w)
    (ψ φ : EuclideanSpace ℂ (BitString w)) :
    P.initState (ψ + φ) = P.initState ψ + P.initState φ := by
  ext p; simp only [initState_apply, PiLp.add_apply]; split_ifs <;> ring

@[simp]
lemma initState_smul (P : QuantumCommProtocol X Y w) (c : ℂ)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.initState (c • ψ) = c • P.initState ψ := by
  ext p; simp only [initState_apply, PiLp.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- Lift Alice's unitary `V` on `HA × Bool` to `Joint`. -/
noncomputable def liftAlice (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HA × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HA × Bool))
    (χ : EuclideanSpace ℂ P.Joint) : EuclideanSpace ℂ P.Joint :=
  WithLp.toLp 2 fun p =>
    (V (WithLp.toLp 2 fun am => χ.ofLp ((am.1, p.1.2), am.2))).ofLp (p.1.1, p.2)

lemma liftAlice_apply (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HA × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HA × Bool))
    (χ : EuclideanSpace ℂ P.Joint) (p : P.Joint) :
    (P.liftAlice V χ).ofLp p =
      (V (WithLp.toLp 2 fun am => χ.ofLp ((am.1, p.1.2), am.2))).ofLp (p.1.1, p.2) := by rfl

@[simp]
lemma liftAlice_add (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HA × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HA × Bool))
    (χ₁ χ₂ : EuclideanSpace ℂ P.Joint) :
    P.liftAlice V (χ₁ + χ₂) = P.liftAlice V χ₁ + P.liftAlice V χ₂ := by
  ext p
  have h : (WithLp.toLp 2 fun am : P.HA × Bool => (χ₁ + χ₂).ofLp ((am.1, p.1.2), am.2)) =
      (WithLp.toLp 2 fun am => χ₁.ofLp ((am.1, p.1.2), am.2)) +
      (WithLp.toLp 2 fun am => χ₂.ofLp ((am.1, p.1.2), am.2)) := rfl
  rw [liftAlice_apply, h, map_add]
  rfl

@[simp]
lemma liftAlice_smul (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HA × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HA × Bool))
    (c : ℂ) (χ : EuclideanSpace ℂ P.Joint) :
    P.liftAlice V (c • χ) = c • P.liftAlice V χ := by
  ext p
  have h : (WithLp.toLp 2 fun am : P.HA × Bool => (c • χ).ofLp ((am.1, p.1.2), am.2)) =
      c • (WithLp.toLp 2 fun am => χ.ofLp ((am.1, p.1.2), am.2)) := rfl
  rw [liftAlice_apply, h, map_smul]
  rfl

lemma liftAlice_sum {ι : Type*} (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HA × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HA × Bool))
    (s : Finset ι) (f : ι → EuclideanSpace ℂ P.Joint) :
    P.liftAlice V (∑ i ∈ s, f i) = ∑ i ∈ s, P.liftAlice V (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := P.liftAlice_smul V 0 0
    simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.liftAlice_add, ih]

@[simp]
lemma liftAlice_refl (P : QuantumCommProtocol X Y w) (χ : EuclideanSpace ℂ P.Joint) :
    P.liftAlice (LinearIsometryEquiv.refl ℂ _) χ = χ := by
  ext p; rfl

/-- Lift Bob's unitary `V` on `HB × Bool` to `Joint`. -/
noncomputable def liftBob (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HB × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HB × Bool))
    (χ : EuclideanSpace ℂ P.Joint) : EuclideanSpace ℂ P.Joint :=
  WithLp.toLp 2 fun p =>
    (V (WithLp.toLp 2 fun bm => χ.ofLp ((p.1.1, bm.1), bm.2))).ofLp (p.1.2, p.2)

lemma liftBob_apply (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HB × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HB × Bool))
    (χ : EuclideanSpace ℂ P.Joint) (p : P.Joint) :
    (P.liftBob V χ).ofLp p =
      (V (WithLp.toLp 2 fun bm => χ.ofLp ((p.1.1, bm.1), bm.2))).ofLp (p.1.2, p.2) := by rfl

@[simp]
lemma liftBob_add (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HB × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HB × Bool))
    (χ₁ χ₂ : EuclideanSpace ℂ P.Joint) :
    P.liftBob V (χ₁ + χ₂) = P.liftBob V χ₁ + P.liftBob V χ₂ := by
  ext p
  have h : (WithLp.toLp 2 fun bm : P.HB × Bool => (χ₁ + χ₂).ofLp ((p.1.1, bm.1), bm.2)) =
      (WithLp.toLp 2 fun bm => χ₁.ofLp ((p.1.1, bm.1), bm.2)) +
      (WithLp.toLp 2 fun bm => χ₂.ofLp ((p.1.1, bm.1), bm.2)) := rfl
  rw [liftBob_apply, h, map_add]
  rfl

@[simp]
lemma liftBob_smul (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HB × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HB × Bool))
    (c : ℂ) (χ : EuclideanSpace ℂ P.Joint) :
    P.liftBob V (c • χ) = c • P.liftBob V χ := by
  ext p
  have h : (WithLp.toLp 2 fun bm : P.HB × Bool => (c • χ).ofLp ((p.1.1, bm.1), bm.2)) =
      c • (WithLp.toLp 2 fun bm => χ.ofLp ((p.1.1, bm.1), bm.2)) := rfl
  rw [liftBob_apply, h, map_smul]
  rfl

lemma liftBob_sum {ι : Type*} (P : QuantumCommProtocol X Y w)
    (V : EuclideanSpace ℂ (P.HB × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HB × Bool))
    (s : Finset ι) (f : ι → EuclideanSpace ℂ P.Joint) :
    P.liftBob V (∑ i ∈ s, f i) = ∑ i ∈ s, P.liftBob V (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := P.liftBob_smul V 0 0
    simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.liftBob_add, ih]

@[simp]
lemma liftBob_refl (P : QuantumCommProtocol X Y w) (χ : EuclideanSpace ℂ P.Joint) :
    P.liftBob (LinearIsometryEquiv.refl ℂ _) χ = χ := by
  ext p; rfl

/-- Joint state after `t` communication steps (`0 ≤ t ≤ P.comm`). -/
noncomputable def runSteps (P : QuantumCommProtocol X Y w) (x : X) (y : Y) :
    ℕ → EuclideanSpace ℂ P.Joint → EuclideanSpace ℂ P.Joint
  | 0, χ => χ
  | t + 1, χ =>
    if ht : t < P.comm then
      let prev := P.runSteps x y t χ
      if P.speaker ⟨t, ht⟩ then P.liftBob (P.bobU ⟨t, ht⟩ y) prev
      else P.liftAlice (P.aliceU ⟨t, ht⟩ x) prev
    else P.runSteps x y t χ

@[simp]
lemma runSteps_zero (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (χ : EuclideanSpace ℂ P.Joint) : P.runSteps x y 0 χ = χ := by rfl

lemma runSteps_succ (P : QuantumCommProtocol X Y w) (x : X) (y : Y) (t : ℕ)
    (χ : EuclideanSpace ℂ P.Joint) :
    P.runSteps x y (t + 1) χ =
      if ht : t < P.comm then
        let prev := P.runSteps x y t χ
        if P.speaker ⟨t, ht⟩ then P.liftBob (P.bobU ⟨t, ht⟩ y) prev
        else P.liftAlice (P.aliceU ⟨t, ht⟩ x) prev
      else P.runSteps x y t χ := by rfl

@[simp]
lemma runSteps_add (P : QuantumCommProtocol X Y w) (x : X) (y : Y) (t : ℕ)
    (χ₁ χ₂ : EuclideanSpace ℂ P.Joint) :
    P.runSteps x y t (χ₁ + χ₂) = P.runSteps x y t χ₁ + P.runSteps x y t χ₂ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [runSteps_succ, ih]
    split_ifs <;> simp

@[simp]
lemma runSteps_smul (P : QuantumCommProtocol X Y w) (x : X) (y : Y) (t : ℕ)
    (c : ℂ) (χ : EuclideanSpace ℂ P.Joint) :
    P.runSteps x y t (c • χ) = c • P.runSteps x y t χ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [runSteps_succ, ih]
    split_ifs <;> simp

lemma runSteps_sum {ι : Type*} (P : QuantumCommProtocol X Y w) (x : X) (y : Y) (t : ℕ)
    (s : Finset ι) (f : ι → EuclideanSpace ℂ P.Joint) :
    P.runSteps x y t (∑ i ∈ s, f i) = ∑ i ∈ s, P.runSteps x y t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := P.runSteps_smul x y t 0 0
    simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.runSteps_add, ih]

/-- Final joint state after all `P.comm` messages and Bob's final local unitary. -/
noncomputable def finalState (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ (BitString w)) : EuclideanSpace ℂ P.Joint :=
  P.liftBob (P.finalBobU y) (P.runSteps x y P.comm (P.initState ψ))

lemma finalState_eq_liftBob_runSteps (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.finalState x y ψ =
      P.liftBob (P.finalBobU y) (P.runSteps x y P.comm (P.initState ψ)) := by rfl

@[simp]
lemma finalState_add (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (ψ φ : EuclideanSpace ℂ (BitString w)) :
    P.finalState x y (ψ + φ) = P.finalState x y ψ + P.finalState x y φ := by
  simp [finalState]

@[simp]
lemma finalState_smul (P : QuantumCommProtocol X Y w) (x : X) (y : Y) (c : ℂ)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.finalState x y (c • ψ) = c • P.finalState x y ψ := by
  simp [finalState]

/-- Acceptance probability of `P` on `(x, y)` with witness `ψ`. -/
noncomputable def acceptProb (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ (BitString w)) : ℝ :=
  ∑ p : P.Joint with (p.1.2, p.2) ∈ P.accept, ‖(P.finalState x y ψ).ofLp p‖ ^ 2

lemma acceptProb_eq_sum_norm_sq (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.acceptProb x y ψ =
      ∑ p : P.Joint with (p.1.2, p.2) ∈ P.accept, ‖(P.finalState x y ψ).ofLp p‖ ^ 2 := by rfl

/-- `P` computes `F : X × Y → Bool` with completeness error `ε₁` and soundness error `ε₂`. -/
@[expose]
def Computes (P : QuantumCommProtocol X Y w) (F : X × Y → Bool) (ε₁ ε₂ : ℝ) : Prop :=
  (∀ x y, F (x, y) = true →
    ∃ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 ∧ 1 - ε₁ ≤ P.acceptProb x y ψ) ∧
  (∀ x y, F (x, y) = false →
    ∀ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 → P.acceptProb x y ψ ≤ ε₂)

/-- Acceptance probability matrix for a witness-free (`w = 0`) protocol. -/
noncomputable def acceptMatrix (P : QuantumCommProtocol X Y 0) : Matrix X Y ℝ :=
  Matrix.of fun x y => P.acceptProb x y (WithLp.toLp 2 fun _ => 1)

lemma acceptMatrix_apply (P : QuantumCommProtocol X Y 0) (x : X) (y : Y) :
    P.acceptMatrix x y = P.acceptProb x y (WithLp.toLp 2 fun _ => 1) := by rfl

end QuantumCommProtocol

/-- The QMA communication complexity $\mathrm{QMA}^{cc}(F)$: minimum `w + c` over QMA
communication protocols with unlimited shared entanglement computing `F` with error `1 / 3`. -/
noncomputable def qmaCommComplexity {X Y : Type*} (F : X × Y → Bool) : ℕ :=
  sInf {k | ∃ (w : ℕ) (P : QuantumCommProtocol X Y w),
    P.Computes F (1 / 3) (1 / 3) ∧ w + P.comm = k}

/-- Any QMA communication protocol computing `F` with error `1 / 3` upper-bounds
`qmaCommComplexity F`. -/
lemma qmaCommComplexity_le {X Y : Type*} {w : ℕ} {F : X × Y → Bool}
    (P : QuantumCommProtocol X Y w) (hP : P.Computes F (1 / 3) (1 / 3)) :
    qmaCommComplexity F ≤ w + P.comm :=
  Nat.sInf_le ⟨w, P, hP, rfl⟩

/-- If at least one QMA communication protocol computes `F` with error `1 / 3`, then some protocol
achieves `qmaCommComplexity F`. -/
lemma exists_protocol_eq_qmaCommComplexity {X Y : Type*} {F : X × Y → Bool}
    (hne : ∃ (w : ℕ) (P : QuantumCommProtocol X Y w), P.Computes F (1 / 3) (1 / 3)) :
    ∃ (w : ℕ) (P : QuantumCommProtocol X Y w),
      P.Computes F (1 / 3) (1 / 3) ∧ w + P.comm = qmaCommComplexity F := by
  obtain ⟨w₀, P₀, hP₀⟩ := hne
  exact Nat.sInf_mem (⟨w₀ + P₀.comm, w₀, P₀, hP₀, rfl⟩ :
    {k | ∃ (w : ℕ) (P : QuantumCommProtocol X Y w),
      P.Computes F (1 / 3) (1 / 3) ∧ w + P.comm = k}.Nonempty)

/-! ### Yao–Kremer Transcript Decomposition and Schmidt Factorization -/

section Factorization

variable {X Y : Type*} {w : ℕ}

/-- Embed a vector in `ℂ^α` into the `b`-message slice of `ℂ^(α × Bool)` (zero on the other
message value). -/
noncomputable def embedBool {α : Type*} (b : Bool) (v : EuclideanSpace ℂ α) :
    EuclideanSpace ℂ (α × Bool) :=
  WithLp.toLp 2 fun am => if am.2 = b then v.ofLp am.1 else 0

lemma embedBool_apply {α : Type*} (b : Bool) (v : EuclideanSpace ℂ α) (am : α × Bool) :
    (embedBool b v).ofLp am = if am.2 = b then v.ofLp am.1 else 0 := by rfl

@[simp]
lemma embedBool_zero {α : Type*} (b : Bool) :
    embedBool b (0 : EuclideanSpace ℂ α) = 0 := by
  ext am; simp [embedBool]

@[simp]
lemma embedBool_add {α : Type*} (b : Bool) (v₁ v₂ : EuclideanSpace ℂ α) :
    embedBool b (v₁ + v₂) = embedBool b v₁ + embedBool b v₂ := by
  ext am; simp only [embedBool_apply, PiLp.add_apply]; split_ifs <;> simp

@[simp]
lemma embedBool_smul {α : Type*} (b : Bool) (c : ℂ) (v : EuclideanSpace ℂ α) :
    embedBool b (c • v) = c • embedBool b v := by
  ext am; simp only [embedBool_apply, PiLp.smul_apply, smul_eq_mul]; split_ifs <;> simp

/-- Extract the `b`-message slice of a vector in `ℂ^(α × Bool)` as a vector in `ℂ^α`. -/
noncomputable def sliceBool {α : Type*} (b : Bool) (v : EuclideanSpace ℂ (α × Bool)) :
    EuclideanSpace ℂ α :=
  WithLp.toLp 2 fun a => v.ofLp (a, b)

lemma norm_sq_embedBool {α : Type*} [Fintype α] (b : Bool) (v : EuclideanSpace ℂ α) :
    ‖embedBool b v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool, embedBool]
  cases b <;> simp

lemma norm_sq_sliceBool_sum {α : Type*} [Fintype α] (v : EuclideanSpace ℂ (α × Bool)) :
    ‖sliceBool false v‖ ^ 2 + ‖sliceBool true v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool, sliceBool]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => add_comm _ _

lemma inner_embedBool_sliceBool {α : Type*} [Fintype α] (b : Bool)
    (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ (α × Bool)) :
    inner ℂ (embedBool b u) v = inner ℂ u (sliceBool b v) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_bool, embedBool, sliceBool]
  cases b <;> simp

/-- Linear step map `v ↦ sliceBool bOut (U (embedBool bIn v))` for a single message bit. -/
private noncomputable def stepLinearMap {α : Type*} [Fintype α]
    (U : EuclideanSpace ℂ (α × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × Bool))
    (bIn bOut : Bool) : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α where
  toFun v := sliceBool bOut (U (embedBool bIn v))
  map_add' v₁ v₂ := by
    ext a
    simp only [sliceBool, PiLp.toLp_apply, PiLp.add_apply, embedBool_add, map_add]
  map_smul' c v := by
    ext a
    simp only [sliceBool, PiLp.toLp_apply, PiLp.smul_apply, embedBool_smul, map_smul,
      RingHom.id_apply]

private lemma norm_sq_adjoint_stepLinearMap_le {α : Type*} [Fintype α]
    (U : EuclideanSpace ℂ (α × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × Bool))
    (bIn bOut : Bool) (ξ : EuclideanSpace ℂ α) :
    ‖LinearMap.adjoint (stepLinearMap U bIn bOut) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  have hadj : LinearMap.adjoint (stepLinearMap U bIn bOut) ξ =
      sliceBool bIn (U.symm (embedBool bOut ξ)) := by
    apply ext_inner_left ℂ
    intro u
    rw [LinearMap.adjoint_inner_right, ← inner_embedBool_sliceBool, ← U.inner_map_map,
      LinearIsometryEquiv.apply_symm_apply]
    dsimp only [stepLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [← inner_conj_symm, inner_embedBool_sliceBool, inner_conj_symm]
  rw [hadj]
  have h1 := norm_sq_sliceBool_sum (U.symm (embedBool bOut ξ))
  rw [U.symm.norm_map, norm_sq_embedBool] at h1
  cases bIn <;>
    linarith [sq_nonneg ‖sliceBool false (U.symm (embedBool bOut ξ))‖,
      sq_nonneg ‖sliceBool true (U.symm (embedBool bOut ξ))‖]

/-- Split a sum over `BitString c` filtered by `P` when coordinate `t` changes from fixed `false`
in `S₀` to unconstrained in `S₁`. -/
private lemma sum_filter_bitString_update {c : ℕ} (t : Fin c)
    (S₀ S₁ : Finset (BitString c)) (f : BitString c → ℝ)
    (hS₀ : ∀ s ∈ S₀, s t = false)
    (hupd : ∀ s ∈ S₀, ∀ b : Bool, Function.update s t b ∈ S₁)
    (hclr : ∀ s ∈ S₁, Function.update s t false ∈ S₀) :
    ∑ s ∈ S₁, f s = ∑ s ∈ S₀, (f (Function.update s t false) + f (Function.update s t true)) := by
  let e : S₀ × Bool ≃ S₁ :=
    { toFun := fun ⟨⟨s, hs⟩, b⟩ => ⟨Function.update s t b, hupd s hs b⟩
      invFun := fun ⟨s, hs⟩ => (⟨Function.update s t false, hclr s hs⟩, s t)
      left_inv := fun ⟨⟨s, hs⟩, b⟩ => by
        ext : 1
        · apply Subtype.ext; funext i
          by_cases hie : i = t
          · subst hie; simp [hS₀ s hs]
          · simp [Function.update_of_ne hie]
        · simp
      right_inv := fun ⟨s, hs⟩ => by
        apply Subtype.ext; funext i
        by_cases hie : i = t
        · subst hie; simp
        · simp [Function.update_of_ne hie] }
  rw [← Finset.sum_coe_sort S₁,
    Fintype.sum_equiv e.symm (fun i : S₁ => f i.1) (fun p : S₀ × Bool => f (e p).1)
      (fun i => by simp),
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  simp only [e, Equiv.coe_fn_mk]
  rw [Finset.sum_coe_sort S₀
    (fun s => f (Function.update s t true) + f (Function.update s t false))]
  refine Finset.sum_congr rfl fun s _ => by ring

private lemma sum_filter_bitString_ge_update {c t : ℕ} (htlt : t < c) (f : BitString c → ℝ) :
    ∑ s : BitString c with (∀ i : Fin c, t + 1 ≤ i.1 → s i = false), f s =
      ∑ s : BitString c with (∀ i : Fin c, t ≤ i.1 → s i = false),
        (f (Function.update s ⟨t, htlt⟩ false) + f (Function.update s ⟨t, htlt⟩ true)) :=
  sum_filter_bitString_update ⟨t, htlt⟩ _ _ f
    (fun s hs => (Finset.mem_filter.mp hs).2 ⟨t, htlt⟩ le_rfl)
    (fun s hs b => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by
      rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
      exact (Finset.mem_filter.mp hs).2 i (by omega)⟩)
    (fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by
      by_cases hie : i = ⟨t, htlt⟩
      · subst hie; simp
      · rw [Function.update_of_ne hie]
        exact (Finset.mem_filter.mp hs).2 i (by simp [Fin.ext_iff] at hie; omega)⟩)

private lemma sum_filter_bitString_lt_update {c t : ℕ} (htlt : t < c) (f : BitString c → ℝ) :
    ∑ s : BitString c with (∀ i : Fin c, i.1 < t → s i = false), f s =
      ∑ s : BitString c with (∀ i : Fin c, i.1 < t + 1 → s i = false),
        (f (Function.update s ⟨t, htlt⟩ false) + f (Function.update s ⟨t, htlt⟩ true)) :=
  sum_filter_bitString_update ⟨t, htlt⟩ _ _ f
    (fun s hs => (Finset.mem_filter.mp hs).2 ⟨t, htlt⟩ (by dsimp; omega))
    (fun s hs b => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by
      rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
      exact (Finset.mem_filter.mp hs).2 i (by omega)⟩)
    (fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by
      by_cases hie : i = ⟨t, htlt⟩
      · subst hie; simp
      · rw [Function.update_of_ne hie]
        exact (Finset.mem_filter.mp hs).2 i (by simp [Fin.ext_iff] at hie; omega)⟩)

/-- Alice's transcript operator `opA t s x` for `0 ≤ t ≤ P.comm`. -/
noncomputable def opA (P : QuantumCommProtocol X Y w) :
    ℕ → BitString P.comm → X → EuclideanSpace ℂ P.HA →ₗ[ℂ] EuclideanSpace ℂ P.HA
  | 0, _, _ => LinearMap.id
  | t + 1, s, x =>
    if ht : t < P.comm then
      if P.speaker ⟨t, ht⟩ then opA P t s x
      else
        let prev := if h0 : t = 0 then false else s ⟨t - 1, by omega⟩
        (stepLinearMap (P.aliceU ⟨t, ht⟩ x) prev (s ⟨t, ht⟩)).comp (opA P t s x)
    else opA P t s x

@[simp]
lemma opA_zero (P : QuantumCommProtocol X Y w) (s : BitString P.comm) (x : X) :
    opA P 0 s x = LinearMap.id := by rfl

/-- Bob's transcript operator `opB t s y` for `0 ≤ t ≤ P.comm`. -/
noncomputable def opB (P : QuantumCommProtocol X Y w) :
    ℕ → BitString P.comm → Y → EuclideanSpace ℂ P.HB →ₗ[ℂ] EuclideanSpace ℂ P.HB
  | 0, _, _ => LinearMap.id
  | t + 1, s, y =>
    if ht : t < P.comm then
      if P.speaker ⟨t, ht⟩ then
        let prev := if h0 : t = 0 then false else s ⟨t - 1, by omega⟩
        (stepLinearMap (P.bobU ⟨t, ht⟩ y) prev (s ⟨t, ht⟩)).comp (opB P t s y)
      else opB P t s y
    else opB P t s y

@[simp]
lemma opB_zero (P : QuantumCommProtocol X Y w) (s : BitString P.comm) (y : Y) :
    opB P 0 s y = LinearMap.id := by rfl

/-- Suffix operators for clean backward norm induction: Alice's side from `t` to `P.comm`. -/
private noncomputable def opASuffix (P : QuantumCommProtocol X Y w) (x : X) :
    (t : ℕ) → Bool → BitString P.comm → EuclideanSpace ℂ P.HA →ₗ[ℂ] EuclideanSpace ℂ P.HA
  | t, bIn, s =>
    if ht : t < P.comm then
      let next := opASuffix P x (t + 1) (s ⟨t, ht⟩) s
      if P.speaker ⟨t, ht⟩ then next
      else next.comp (stepLinearMap (P.aliceU ⟨t, ht⟩ x) bIn (s ⟨t, ht⟩))
    else LinearMap.id
termination_by t => P.comm - t

/-- Suffix operators for clean backward norm induction: Bob's side from `t` to `P.comm`. -/
private noncomputable def opBSuffix (P : QuantumCommProtocol X Y w) (y : Y) :
    (t : ℕ) → Bool → BitString P.comm → EuclideanSpace ℂ P.HB →ₗ[ℂ] EuclideanSpace ℂ P.HB
  | t, bIn, s =>
    if ht : t < P.comm then
      let next := opBSuffix P y (t + 1) (s ⟨t, ht⟩) s
      if P.speaker ⟨t, ht⟩ then
        next.comp (stepLinearMap (P.bobU ⟨t, ht⟩ y) bIn (s ⟨t, ht⟩))
      else next
    else LinearMap.id
termination_by t => P.comm - t

private lemma opA_congr (P : QuantumCommProtocol X Y w) (t : ℕ) (s₁ s₂ : BitString P.comm)
    (h : ∀ i : Fin P.comm, i.1 < t → s₁ i = s₂ i) (x : X) :
    opA P t s₁ x = opA P t s₂ x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [opA]
    by_cases ht : t < P.comm
    · simp only [ht, ↓reduceDIte]
      by_cases hsp : P.speaker ⟨t, ht⟩ = true
      · simp only [hsp, ↓reduceIte]
        exact ih (fun i hi => h i (by omega))
      · simp only [hsp, Bool.false_eq_true, ↓reduceIte]
        rw [ih (fun i hi => h i (by omega)), h ⟨t, ht⟩ (by dsimp; omega)]
        congr 2
        by_cases h0 : t = 0
        · simp only [h0, ↓reduceDIte]
        · simp only [h0, ↓reduceDIte]
          rw [h ⟨t - 1, by omega⟩ (by dsimp; omega)]
    · simp only [ht, ↓reduceDIte]
      exact ih (fun i hi => h i (by omega))

private lemma opB_congr (P : QuantumCommProtocol X Y w) (t : ℕ) (s₁ s₂ : BitString P.comm)
    (h : ∀ i : Fin P.comm, i.1 < t → s₁ i = s₂ i) (y : Y) :
    opB P t s₁ y = opB P t s₂ y := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [opB]
    by_cases ht : t < P.comm
    · simp only [ht, ↓reduceDIte]
      by_cases hsp : P.speaker ⟨t, ht⟩ = true
      · simp only [hsp, ↓reduceIte]
        rw [ih (fun i hi => h i (by omega)), h ⟨t, ht⟩ (by dsimp; omega)]
        congr 2
        by_cases h0 : t = 0
        · simp only [h0, ↓reduceDIte]
        · simp only [h0, ↓reduceDIte]
          rw [h ⟨t - 1, by omega⟩ (by dsimp; omega)]
      · simp only [hsp, Bool.false_eq_true, ↓reduceIte]
        exact ih (fun i hi => h i (by omega))
    · simp only [ht, ↓reduceDIte]
      exact ih (fun i hi => h i (by omega))

private lemma opASuffix_congr (P : QuantumCommProtocol X Y w) (x : X) (t : ℕ) (bIn : Bool)
    (s₁ s₂ : BitString P.comm) (h : ∀ i : Fin P.comm, t ≤ i.1 → s₁ i = s₂ i) :
    opASuffix P x t bIn s₁ = opASuffix P x t bIn s₂ := by
  by_cases ht : t < P.comm
  · rw [opASuffix, opASuffix]
    simp only [ht, ↓reduceDIte, h ⟨t, ht⟩ le_rfl]
    rw [opASuffix_congr P x (t + 1) (s₂ ⟨t, ht⟩) s₁ s₂ (fun i hi => h i (by omega))]
  · rw [opASuffix, opASuffix]; simp [ht]
termination_by P.comm - t

private lemma opBSuffix_congr (P : QuantumCommProtocol X Y w) (y : Y) (t : ℕ) (bIn : Bool)
    (s₁ s₂ : BitString P.comm) (h : ∀ i : Fin P.comm, t ≤ i.1 → s₁ i = s₂ i) :
    opBSuffix P y t bIn s₁ = opBSuffix P y t bIn s₂ := by
  by_cases ht : t < P.comm
  · rw [opBSuffix, opBSuffix]
    simp only [ht, ↓reduceDIte, h ⟨t, ht⟩ le_rfl]
    rw [opBSuffix_congr P y (t + 1) (s₂ ⟨t, ht⟩) s₁ s₂ (fun i hi => h i (by omega))]
  · rw [opBSuffix, opBSuffix]; simp [ht]
termination_by P.comm - t

private lemma opASuffix_zero_eq_opA (P : QuantumCommProtocol X Y w) (x : X)
    (s : BitString P.comm) :
    opASuffix P x 0 false s = opA P P.comm s x := by
  suffices h : ∀ (t : ℕ) (ht : t ≤ P.comm),
      (opASuffix P x t (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) s).comp
        (opA P t s x) = opA P P.comm s x by
    simpa [opA] using h 0 (Nat.zero_le _)
  intro t ht
  induction hrem : P.comm - t generalizing t with
  | zero =>
    have hteq : t = P.comm := by omega
    subst hteq
    rw [opASuffix]; simp
  | succ d ih =>
    have htlt : t < P.comm := by omega
    rw [opASuffix]; simp only [htlt, ↓reduceDIte]
    have hnext := ih (t + 1) (by omega) (by omega)
    simp only [show t + 1 ≠ 0 by omega, ↓reduceDIte, show t + 1 - 1 = t by omega] at hnext
    rw [← hnext]
    by_cases hsp : P.speaker ⟨t, htlt⟩ = true
    · simp only [opA, htlt, ↓reduceDIte, hsp, ↓reduceIte]
    · simp only [opA, htlt, ↓reduceDIte, hsp, Bool.false_eq_true, ↓reduceIte,
        LinearMap.comp_assoc]

private lemma opBSuffix_zero_eq_opB (P : QuantumCommProtocol X Y w) (y : Y)
    (s : BitString P.comm) :
    opBSuffix P y 0 false s = opB P P.comm s y := by
  suffices h : ∀ (t : ℕ) (ht : t ≤ P.comm),
      (opBSuffix P y t (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) s).comp
        (opB P t s y) = opB P P.comm s y by
    simpa [opB] using h 0 (Nat.zero_le _)
  intro t ht
  induction hrem : P.comm - t generalizing t with
  | zero =>
    have hteq : t = P.comm := by omega
    subst hteq
    rw [opBSuffix]; simp
  | succ d ih =>
    have htlt : t < P.comm := by omega
    rw [opBSuffix]; simp only [htlt, ↓reduceDIte]
    have hnext := ih (t + 1) (by omega) (by omega)
    simp only [show t + 1 ≠ 0 by omega, ↓reduceDIte, show t + 1 - 1 = t by omega] at hnext
    rw [← hnext]
    by_cases hsp : P.speaker ⟨t, htlt⟩ = true
    · simp only [opB, htlt, ↓reduceDIte, hsp, ↓reduceIte, LinearMap.comp_assoc]
    · simp only [opB, htlt, ↓reduceDIte, hsp, Bool.false_eq_true, ↓reduceIte]

/-- Forward norm bound on `opA`: `∑_s ‖opA t s x v‖² ≤ 2^t ‖v‖²`. -/
lemma sum_norm_sq_opA_le (P : QuantumCommProtocol X Y w) (x : X)
    (v : EuclideanSpace ℂ P.HA) :
    ∑ s : BitString P.comm, ‖opA P P.comm s x v‖ ^ 2 ≤ (2 : ℝ) ^ P.comm * ‖v‖ ^ 2 := by
  suffices h : ∀ (t : ℕ) (ht : t ≤ P.comm),
      ∑ s : BitString P.comm with (∀ i : Fin P.comm, t ≤ i.1 → s i = false),
        ‖opA P t s x v‖ ^ 2 ≤ (2 : ℝ) ^ t * ‖v‖ ^ 2 by
    simpa using h P.comm le_rfl
  intro t; induction t with
  | zero =>
    intro _
    have hsing : (Finset.univ.filter fun s : BitString P.comm =>
        ∀ i : Fin P.comm, 0 ≤ i.1 → s i = false) = {fun _ => false} := by
      ext s; simp [funext_iff]
    rw [hsing, Finset.sum_singleton]; simp [opA]
  | succ t ih =>
    intro ht
    have htlt : t < P.comm := by omega
    let S₁ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, t + 1 ≤ i.1 → s i = false
    let S₀ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, t ≤ i.1 → s i = false
    have hsplit : ∑ s ∈ S₁, ‖opA P (t + 1) s x v‖ ^ 2 =
        ∑ s ∈ S₀, (‖opA P (t + 1) (Function.update s ⟨t, htlt⟩ false) x v‖ ^ 2 +
          ‖opA P (t + 1) (Function.update s ⟨t, htlt⟩ true) x v‖ ^ 2) :=
      sum_filter_bitString_ge_update htlt (fun s => ‖opA P (t + 1) s x v‖ ^ 2)
    rw [hsplit]
    have hstep : ∀ s ∈ S₀,
        ‖opA P (t + 1) (Function.update s ⟨t, htlt⟩ false) x v‖ ^ 2 +
        ‖opA P (t + 1) (Function.update s ⟨t, htlt⟩ true) x v‖ ^ 2 ≤
          2 * ‖opA P t s x v‖ ^ 2 := by
      intro s _
      have heq0 : opA P t (Function.update s ⟨t, htlt⟩ false) x = opA P t s x :=
        opA_congr P t _ _
          (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) x
      have heq1 : opA P t (Function.update s ⟨t, htlt⟩ true) x = opA P t s x :=
        opA_congr P t _ _
          (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) x
      simp only [opA, htlt, ↓reduceDIte]
      by_cases hsp : P.speaker ⟨t, htlt⟩ = true
      · simp only [hsp, ↓reduceIte]
        rw [heq0, heq1]; linarith
      · simp only [hsp, Bool.false_eq_true, ↓reduceIte, LinearMap.comp_apply, stepLinearMap,
          LinearMap.coe_mk, AddHom.coe_mk, heq0, heq1, Function.update_self]
        have hp0 : (if h0 : t = 0 then false else
            Function.update s ⟨t, htlt⟩ false ⟨t - 1, by omega⟩) =
            (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) := by
          by_cases h0 : t = 0
          · simp only [h0, ↓reduceDIte]
          · simp only [h0, ↓reduceDIte]
            exact Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
        have hp1 : (if h0 : t = 0 then false else
            Function.update s ⟨t, htlt⟩ true ⟨t - 1, by omega⟩) =
            (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) := by
          by_cases h0 : t = 0
          · simp only [h0, ↓reduceDIte]
          · simp only [h0, ↓reduceDIte]
            exact Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
        rw [hp0, hp1, norm_sq_sliceBool_sum, (P.aliceU ⟨t, htlt⟩ x).norm_map, norm_sq_embedBool]
        linarith [sq_nonneg ‖opA P t s x v‖]
    calc ∑ s ∈ S₀, (‖opA P (t + 1) (Function.update s ⟨t, htlt⟩ false) x v‖ ^ 2 +
            ‖opA P (t + 1) (Function.update s ⟨t, htlt⟩ true) x v‖ ^ 2)
        ≤ ∑ s ∈ S₀, 2 * ‖opA P t s x v‖ ^ 2 := Finset.sum_le_sum hstep
      _ = 2 * ∑ s ∈ S₀, ‖opA P t s x v‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ((2 : ℝ) ^ t * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
      _ = (2 : ℝ) ^ (t + 1) * ‖v‖ ^ 2 := by ring

/-- Forward norm bound on `opB`: `∑_s ‖opB t s y u‖² ≤ 2^t ‖u‖²`. -/
lemma sum_norm_sq_opB_le (P : QuantumCommProtocol X Y w) (y : Y)
    (u : EuclideanSpace ℂ P.HB) :
    ∑ s : BitString P.comm, ‖opB P P.comm s y u‖ ^ 2 ≤ (2 : ℝ) ^ P.comm * ‖u‖ ^ 2 := by
  suffices h : ∀ (t : ℕ) (ht : t ≤ P.comm),
      ∑ s : BitString P.comm with (∀ i : Fin P.comm, t ≤ i.1 → s i = false),
        ‖opB P t s y u‖ ^ 2 ≤ (2 : ℝ) ^ t * ‖u‖ ^ 2 by
    simpa using h P.comm le_rfl
  intro t; induction t with
  | zero =>
    intro _
    have hsing : (Finset.univ.filter fun s : BitString P.comm =>
        ∀ i : Fin P.comm, 0 ≤ i.1 → s i = false) = {fun _ => false} := by
      ext s; simp [funext_iff]
    rw [hsing, Finset.sum_singleton]; simp [opB]
  | succ t ih =>
    intro ht
    have htlt : t < P.comm := by omega
    let S₁ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, t + 1 ≤ i.1 → s i = false
    let S₀ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, t ≤ i.1 → s i = false
    have hsplit : ∑ s ∈ S₁, ‖opB P (t + 1) s y u‖ ^ 2 =
        ∑ s ∈ S₀, (‖opB P (t + 1) (Function.update s ⟨t, htlt⟩ false) y u‖ ^ 2 +
          ‖opB P (t + 1) (Function.update s ⟨t, htlt⟩ true) y u‖ ^ 2) :=
      sum_filter_bitString_ge_update htlt (fun s => ‖opB P (t + 1) s y u‖ ^ 2)
    rw [hsplit]
    have hstep : ∀ s ∈ S₀,
        ‖opB P (t + 1) (Function.update s ⟨t, htlt⟩ false) y u‖ ^ 2 +
        ‖opB P (t + 1) (Function.update s ⟨t, htlt⟩ true) y u‖ ^ 2 ≤
          2 * ‖opB P t s y u‖ ^ 2 := by
      intro s _
      have heq0 : opB P t (Function.update s ⟨t, htlt⟩ false) y = opB P t s y :=
        opB_congr P t _ _
          (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) y
      have heq1 : opB P t (Function.update s ⟨t, htlt⟩ true) y = opB P t s y :=
        opB_congr P t _ _
          (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) y
      simp only [opB, htlt, ↓reduceDIte]
      by_cases hsp : P.speaker ⟨t, htlt⟩ = true
      · simp only [hsp, ↓reduceIte, LinearMap.comp_apply, stepLinearMap, LinearMap.coe_mk,
          AddHom.coe_mk, heq0, heq1, Function.update_self]
        have hp0 : (if h0 : t = 0 then false else
            Function.update s ⟨t, htlt⟩ false ⟨t - 1, by omega⟩) =
            (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) := by
          by_cases h0 : t = 0
          · simp only [h0, ↓reduceDIte]
          · simp only [h0, ↓reduceDIte]
            exact Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
        have hp1 : (if h0 : t = 0 then false else
            Function.update s ⟨t, htlt⟩ true ⟨t - 1, by omega⟩) =
            (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) := by
          by_cases h0 : t = 0
          · simp only [h0, ↓reduceDIte]
          · simp only [h0, ↓reduceDIte]
            exact Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
        rw [hp0, hp1, norm_sq_sliceBool_sum, (P.bobU ⟨t, htlt⟩ y).norm_map, norm_sq_embedBool]
        linarith [sq_nonneg ‖opB P t s y u‖]
      · simp only [hsp, Bool.false_eq_true, ↓reduceIte]
        rw [heq0, heq1]; linarith
    calc ∑ s ∈ S₀, (‖opB P (t + 1) (Function.update s ⟨t, htlt⟩ false) y u‖ ^ 2 +
            ‖opB P (t + 1) (Function.update s ⟨t, htlt⟩ true) y u‖ ^ 2)
        ≤ ∑ s ∈ S₀, 2 * ‖opB P t s y u‖ ^ 2 := Finset.sum_le_sum hstep
      _ = 2 * ∑ s ∈ S₀, ‖opB P t s y u‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ((2 : ℝ) ^ t * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
      _ = (2 : ℝ) ^ (t + 1) * ‖u‖ ^ 2 := by ring

/-- Backward (adjoint) norm bound on `opA`: `∑_s ‖(opA P.comm s x)† v‖² ≤ 2^P.comm ‖v‖²`. -/
lemma sum_norm_sq_adjoint_opA_le (P : QuantumCommProtocol X Y w) (x : X)
    (v : EuclideanSpace ℂ P.HA) :
    ∑ s : BitString P.comm, ‖LinearMap.adjoint (opA P P.comm s x) v‖ ^ 2 ≤
      (2 : ℝ) ^ P.comm * ‖v‖ ^ 2 := by
  suffices h : ∀ (t : ℕ) (ht : t ≤ P.comm) (bIn : Bool),
      ∑ s : BitString P.comm with (∀ i : Fin P.comm, i.1 < t → s i = false),
        ‖LinearMap.adjoint (opASuffix P x t bIn s) v‖ ^ 2 ≤
          (2 : ℝ) ^ (P.comm - t) * ‖v‖ ^ 2 by
    have h0 := h 0 (Nat.zero_le _) false
    simp only [Nat.sub_zero, not_lt_zero, IsEmpty.forall_iff, implies_true,
      Finset.filter_true] at h0
    simpa [opASuffix_zero_eq_opA] using h0
  intro t ht
  induction hd : P.comm - t generalizing t with
  | zero =>
    intro bIn
    have hteq : t = P.comm := by omega
    subst hteq
    have hsing : (Finset.univ.filter fun s : BitString P.comm =>
        ∀ i : Fin P.comm, i.1 < P.comm → s i = false) = {fun _ => false} := by
      ext s; simp [funext_iff, Fin.is_lt]
    rw [hsing, Finset.sum_singleton, opASuffix]
    simp
  | succ d ih =>
    intro bIn
    have htlt : t < P.comm := by omega
    let S₀ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, i.1 < t → s i = false
    let S₁ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, i.1 < t + 1 → s i = false
    have hsplit : ∑ s ∈ S₀, ‖LinearMap.adjoint (opASuffix P x t bIn s) v‖ ^ 2 =
        ∑ s ∈ S₁,
          (‖LinearMap.adjoint (opASuffix P x t bIn (Function.update s ⟨t, htlt⟩ false)) v‖ ^ 2 +
           ‖LinearMap.adjoint (opASuffix P x t bIn (Function.update s ⟨t, htlt⟩ true)) v‖ ^ 2) :=
      sum_filter_bitString_lt_update htlt
        (fun s => ‖LinearMap.adjoint (opASuffix P x t bIn s) v‖ ^ 2)
    rw [hsplit]
    have hterm : ∀ b : Bool,
        ∑ s ∈ S₁,
          ‖LinearMap.adjoint (opASuffix P x t bIn (Function.update s ⟨t, htlt⟩ b)) v‖ ^ 2 ≤
          (2 : ℝ) ^ d * ‖v‖ ^ 2 := by
      intro b
      calc ∑ s ∈ S₁,
            ‖LinearMap.adjoint (opASuffix P x t bIn (Function.update s ⟨t, htlt⟩ b)) v‖ ^ 2
          ≤ ∑ s ∈ S₁, ‖LinearMap.adjoint (opASuffix P x (t + 1) b s) v‖ ^ 2 := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [opASuffix]; simp only [htlt, ↓reduceDIte, Function.update_self]
            have hcongr : opASuffix P x (t + 1) b (Function.update s ⟨t, htlt⟩ b) =
                opASuffix P x (t + 1) b s :=
              opASuffix_congr P x (t + 1) b _ _ fun i hi =>
                Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
            rw [hcongr]
            split_ifs with hsp
            · exact le_rfl
            · rw [LinearMap.adjoint_comp, LinearMap.comp_apply]
              exact norm_sq_adjoint_stepLinearMap_le (P.aliceU ⟨t, htlt⟩ x) bIn b _
        _ ≤ (2 : ℝ) ^ d * ‖v‖ ^ 2 := ih (t + 1) (by omega) (by omega) b
    rw [Finset.sum_add_distrib]
    calc ∑ s ∈ S₁,
          ‖LinearMap.adjoint (opASuffix P x t bIn (Function.update s ⟨t, htlt⟩ false)) v‖ ^ 2 +
        ∑ s ∈ S₁,
          ‖LinearMap.adjoint (opASuffix P x t bIn (Function.update s ⟨t, htlt⟩ true)) v‖ ^ 2
        ≤ (2 : ℝ) ^ d * ‖v‖ ^ 2 + (2 : ℝ) ^ d * ‖v‖ ^ 2 := add_le_add (hterm false) (hterm true)
      _ = (2 : ℝ) ^ (d + 1) * ‖v‖ ^ 2 := by ring

/-- Backward (adjoint) norm bound on `opB`: `∑_s ‖(opB P.comm s y)† u‖² ≤ 2^P.comm ‖u‖²`. -/
lemma sum_norm_sq_adjoint_opB_le (P : QuantumCommProtocol X Y w) (y : Y)
    (u : EuclideanSpace ℂ P.HB) :
    ∑ s : BitString P.comm, ‖LinearMap.adjoint (opB P P.comm s y) u‖ ^ 2 ≤
      (2 : ℝ) ^ P.comm * ‖u‖ ^ 2 := by
  suffices h : ∀ (t : ℕ) (ht : t ≤ P.comm) (bIn : Bool),
      ∑ s : BitString P.comm with (∀ i : Fin P.comm, i.1 < t → s i = false),
        ‖LinearMap.adjoint (opBSuffix P y t bIn s) u‖ ^ 2 ≤
          (2 : ℝ) ^ (P.comm - t) * ‖u‖ ^ 2 by
    have h0 := h 0 (Nat.zero_le _) false
    simp only [Nat.sub_zero, not_lt_zero, IsEmpty.forall_iff, implies_true,
      Finset.filter_true] at h0
    simpa [opBSuffix_zero_eq_opB] using h0
  intro t ht
  induction hd : P.comm - t generalizing t with
  | zero =>
    intro bIn
    have hteq : t = P.comm := by omega
    subst hteq
    have hsing : (Finset.univ.filter fun s : BitString P.comm =>
        ∀ i : Fin P.comm, i.1 < P.comm → s i = false) = {fun _ => false} := by
      ext s; simp [funext_iff, Fin.is_lt]
    rw [hsing, Finset.sum_singleton, opBSuffix]
    simp
  | succ d ih =>
    intro bIn
    have htlt : t < P.comm := by omega
    let S₀ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, i.1 < t → s i = false
    let S₁ := Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, i.1 < t + 1 → s i = false
    have hsplit : ∑ s ∈ S₀, ‖LinearMap.adjoint (opBSuffix P y t bIn s) u‖ ^ 2 =
        ∑ s ∈ S₁,
          (‖LinearMap.adjoint (opBSuffix P y t bIn (Function.update s ⟨t, htlt⟩ false)) u‖ ^ 2 +
           ‖LinearMap.adjoint (opBSuffix P y t bIn (Function.update s ⟨t, htlt⟩ true)) u‖ ^ 2) :=
      sum_filter_bitString_lt_update htlt
        (fun s => ‖LinearMap.adjoint (opBSuffix P y t bIn s) u‖ ^ 2)
    rw [hsplit]
    have hterm : ∀ b : Bool,
        ∑ s ∈ S₁,
          ‖LinearMap.adjoint (opBSuffix P y t bIn (Function.update s ⟨t, htlt⟩ b)) u‖ ^ 2 ≤
          (2 : ℝ) ^ d * ‖u‖ ^ 2 := by
      intro b
      calc ∑ s ∈ S₁,
            ‖LinearMap.adjoint (opBSuffix P y t bIn (Function.update s ⟨t, htlt⟩ b)) u‖ ^ 2
          ≤ ∑ s ∈ S₁, ‖LinearMap.adjoint (opBSuffix P y (t + 1) b s) u‖ ^ 2 := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [opBSuffix]; simp only [htlt, ↓reduceDIte, Function.update_self]
            have hcongr : opBSuffix P y (t + 1) b (Function.update s ⟨t, htlt⟩ b) =
                opBSuffix P y (t + 1) b s :=
              opBSuffix_congr P y (t + 1) b _ _ fun i hi =>
                Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
            rw [hcongr]
            split_ifs with hsp
            · rw [LinearMap.adjoint_comp, LinearMap.comp_apply]
              exact norm_sq_adjoint_stepLinearMap_le (P.bobU ⟨t, htlt⟩ y) bIn b _
            · exact le_rfl
        _ ≤ (2 : ℝ) ^ d * ‖u‖ ^ 2 := ih (t + 1) (by omega) (by omega) b
    rw [Finset.sum_add_distrib]
    calc ∑ s ∈ S₁,
          ‖LinearMap.adjoint (opBSuffix P y t bIn (Function.update s ⟨t, htlt⟩ false)) u‖ ^ 2 +
        ∑ s ∈ S₁,
          ‖LinearMap.adjoint (opBSuffix P y t bIn (Function.update s ⟨t, htlt⟩ true)) u‖ ^ 2
        ≤ (2 : ℝ) ^ d * ‖u‖ ^ 2 + (2 : ℝ) ^ d * ‖u‖ ^ 2 := add_le_add (hterm false) (hterm true)
      _ = (2 : ℝ) ^ (d + 1) * ‖u‖ ^ 2 := by ring

/-- Exact Yao–Kremer decomposition of `P.finalState x y ψ` using a separable initial state. -/
lemma yao_kremer_finalState (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (vA : EuclideanSpace ℂ P.HA) (uB : EuclideanSpace ℂ P.HB) :
    P.liftBob (P.finalBobU y)
        (P.runSteps x y P.comm
          (WithLp.toLp 2 fun p : P.Joint =>
            if p.2 = false then vA.ofLp p.1.1 * uB.ofLp p.1.2 else 0)) =
      WithLp.toLp 2 fun p : P.Joint =>
        ∑ s : BitString P.comm,
          (opA P P.comm s x vA).ofLp p.1.1 *
          (P.finalBobU y (embedBool (if h0 : P.comm = 0 then false else s ⟨P.comm - 1, by omega⟩)
            (opB P P.comm s y uB))).ofLp (p.1.2, p.2) := by
  have hsteps : ∀ (t : ℕ) (ht : t ≤ P.comm),
      P.runSteps x y t
          (WithLp.toLp 2 fun p : P.Joint =>
            if p.2 = false then vA.ofLp p.1.1 * uB.ofLp p.1.2 else 0) =
        WithLp.toLp 2 fun p : P.Joint =>
          ∑ s : BitString P.comm with (∀ i : Fin P.comm, t ≤ i.1 → s i = false),
            if p.2 = (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) then
              (opA P t s x vA).ofLp p.1.1 * (opB P t s y uB).ofLp p.1.2
            else 0 := by
    intro t; induction t with
    | zero =>
      intro _
      ext ⟨⟨a, b⟩, m⟩
      have hsing : (Finset.univ.filter fun s : BitString P.comm =>
          ∀ i : Fin P.comm, 0 ≤ i.1 → s i = false) = {fun _ => false} := by
        ext s; simp [funext_iff]
      simp only [QuantumCommProtocol.runSteps, PiLp.toLp_apply, hsing, Finset.sum_singleton,
        opA, opB, LinearMap.id_apply, ↓reduceDIte]
    | succ t ih =>
      intro ht
      have htlt : t < P.comm := by omega
      simp only [QuantumCommProtocol.runSteps, htlt, ↓reduceDIte]
      rw [ih (by omega)]
      ext ⟨⟨a, b⟩, m⟩
      let S₁ := Finset.univ.filter fun s : BitString P.comm =>
        ∀ i : Fin P.comm, t + 1 ≤ i.1 → s i = false
      let S₀ := Finset.univ.filter fun s : BitString P.comm =>
        ∀ i : Fin P.comm, t ≤ i.1 → s i = false
      have hsum_m : ∀ (f : BitString P.comm → ℂ),
          ∑ s ∈ S₁, (if m = s ⟨t, htlt⟩ then f s else 0) =
            ∑ s ∈ S₀, f (Function.update s ⟨t, htlt⟩ m) := by
        intro f
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun s _ => Function.update s ⟨t, htlt⟩ false) ?_ ?_ ?_ ?_
        · intro s hs
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩
          by_cases hie : i = ⟨t, htlt⟩
          · subst hie; simp
          · rw [Function.update_of_ne hie]
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2 i
              (by simp [Fin.ext_iff] at hie; omega)
        · intro s₁ hs₁ s₂ hs₂ h
          have hm1 : s₁ ⟨t, htlt⟩ = m := (Finset.mem_filter.mp hs₁).2.symm
          have hm2 : s₂ ⟨t, htlt⟩ = m := (Finset.mem_filter.mp hs₂).2.symm
          funext i
          by_cases hie : i = ⟨t, htlt⟩
          · subst hie; rw [hm1, hm2]
          · have hi := congr_fun h i; simpa [Function.update_of_ne hie] using hi
        · intro s hs
          refine ⟨Function.update s ⟨t, htlt⟩ m, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, fun i hi => by
              rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
              exact (Finset.mem_filter.mp hs).2 i (by omega)⟩, by simp⟩, ?_⟩
          funext i
          by_cases hie : i = ⟨t, htlt⟩
          · subst hie; simp [(Finset.mem_filter.mp hs).2 ⟨t, htlt⟩ le_rfl]
          · simp [Function.update_of_ne hie]
        · intro s hs
          have hms : s ⟨t, htlt⟩ = m := (Finset.mem_filter.mp hs).2.symm
          congr 1; funext i
          by_cases hie : i = ⟨t, htlt⟩
          · subst hie; simp [hms]
          · simp [Function.update_of_ne hie]
      by_cases hsp : P.speaker ⟨t, htlt⟩ = true
      · simp only [hsp, ↓reduceIte, QuantumCommProtocol.liftBob, PiLp.toLp_apply]
        have hlin : (WithLp.toLp 2 fun bm : P.HB × Bool =>
            ∑ s ∈ S₀, if bm.2 = (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) then
              (opA P t s x vA).ofLp a * (opB P t s y uB).ofLp bm.1 else 0) =
            ∑ s ∈ S₀, (opA P t s x vA).ofLp a •
              embedBool (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩)
                (opB P t s y uB) := by
          ext ⟨b', m'⟩; simp [Finset.sum_apply, embedBool]
        rw [hlin, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
        simp only [show t + 1 ≠ 0 by omega, ↓reduceDIte, show t + 1 - 1 = t by omega]
        rw [hsum_m]
        refine Finset.sum_congr rfl fun s _ => ?_
        have hA : opA P (t + 1) (Function.update s ⟨t, htlt⟩ m) x = opA P t s x := by
          simp only [opA, htlt, ↓reduceDIte, hsp, ↓reduceIte]
          exact opA_congr P t _ _
            (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) x
        have hB : opB P (t + 1) (Function.update s ⟨t, htlt⟩ m) y uB =
            sliceBool m (P.bobU ⟨t, htlt⟩ y
              (embedBool (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩)
                (opB P t s y uB))) := by
          simp only [opB, htlt, ↓reduceDIte, hsp, ↓reduceIte, LinearMap.comp_apply, stepLinearMap,
            LinearMap.coe_mk, AddHom.coe_mk, Function.update_self]
          have hB0 : opB P t (Function.update s ⟨t, htlt⟩ m) y = opB P t s y :=
            opB_congr P t _ _
              (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) y
          have hp : (if h0 : t = 0 then false else
              Function.update s ⟨t, htlt⟩ m ⟨t - 1, by omega⟩) =
              (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) := by
            by_cases h0 : t = 0
            · simp only [h0, ↓reduceDIte]
            · simp only [h0, ↓reduceDIte]
              exact Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
          rw [hB0, hp]
        rw [hA, hB, map_smul, PiLp.smul_apply, smul_eq_mul]; rfl
      · simp only [hsp, Bool.false_eq_true, ↓reduceIte, QuantumCommProtocol.liftAlice,
          PiLp.toLp_apply]
        have hlin : (WithLp.toLp 2 fun am : P.HA × Bool =>
            ∑ s ∈ S₀, if am.2 = (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) then
              (opA P t s x vA).ofLp am.1 * (opB P t s y uB).ofLp b else 0) =
            ∑ s ∈ S₀, (opB P t s y uB).ofLp b •
              embedBool (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩)
                (opA P t s x vA) := by
          ext ⟨a', m'⟩; simp [Finset.sum_apply, embedBool, mul_comm]
        rw [hlin, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
        simp only [show t + 1 ≠ 0 by omega, ↓reduceDIte, show t + 1 - 1 = t by omega]
        rw [hsum_m]
        refine Finset.sum_congr rfl fun s _ => ?_
        have hB : opB P (t + 1) (Function.update s ⟨t, htlt⟩ m) y = opB P t s y := by
          simp only [opB, htlt, ↓reduceDIte, hsp, Bool.false_eq_true, ↓reduceIte]
          exact opB_congr P t _ _
            (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) y
        have hA : opA P (t + 1) (Function.update s ⟨t, htlt⟩ m) x vA =
            sliceBool m (P.aliceU ⟨t, htlt⟩ x
              (embedBool (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩)
                (opA P t s x vA))) := by
          simp only [opA, htlt, ↓reduceDIte, hsp, Bool.false_eq_true, ↓reduceIte,
            LinearMap.comp_apply, stepLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
            Function.update_self]
          have hA0 : opA P t (Function.update s ⟨t, htlt⟩ m) x = opA P t s x :=
            opA_congr P t _ _
              (fun i hi => Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _) x
          have hp : (if h0 : t = 0 then false else
              Function.update s ⟨t, htlt⟩ m ⟨t - 1, by omega⟩) =
              (if h0 : t = 0 then false else s ⟨t - 1, by omega⟩) := by
            by_cases h0 : t = 0
            · simp only [h0, ↓reduceDIte]
            · simp only [h0, ↓reduceDIte]
              exact Function.update_of_ne (by simp [Fin.ext_iff]; omega) _ _
          rw [hA0, hp]
        rw [hA, hB, map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm]; rfl
  rw [hsteps P.comm le_rfl]
  ext ⟨⟨a, b⟩, m⟩
  have hfilt : (Finset.univ.filter fun s : BitString P.comm =>
      ∀ i : Fin P.comm, P.comm ≤ i.1 → s i = false) = Finset.univ :=
    Finset.filter_eq_self.mpr fun _ _ i hi => absurd i.2 (not_lt.mpr hi)
  simp only [QuantumCommProtocol.liftBob, PiLp.toLp_apply, hfilt]
  have hlin : (WithLp.toLp 2 fun bm : P.HB × Bool =>
      ∑ s : BitString P.comm,
        if bm.2 = (if h0 : P.comm = 0 then false else s ⟨P.comm - 1, by omega⟩) then
          (opA P P.comm s x vA).ofLp a * (opB P P.comm s y uB).ofLp bm.1 else 0) =
      ∑ s : BitString P.comm, (opA P P.comm s x vA).ofLp a •
        embedBool (if h0 : P.comm = 0 then false else s ⟨P.comm - 1, by omega⟩)
          (opB P P.comm s y uB) := by
    ext ⟨b', m'⟩; simp [Finset.sum_apply, embedBool]
  rw [hlin, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, PiLp.smul_apply, smul_eq_mul]

/-- `P.finalState x y` preserves inner products (in particular, norms). -/
lemma QuantumCommProtocol.inner_finalState (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (a b : EuclideanSpace ℂ (BitString w)) :
    inner ℂ (P.finalState x y a) (P.finalState x y b) = inner ℂ a b := by
  have hbob_isom : ∀ (V : EuclideanSpace ℂ (P.HB × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HB × Bool))
      (χ₁ χ₂ : EuclideanSpace ℂ P.Joint),
      inner ℂ (P.liftBob V χ₁) (P.liftBob V χ₂) = inner ℂ χ₁ χ₂ := by
    intro V χ₁ χ₂
    let eB : P.Joint ≃ P.HA × (P.HB × Bool) :=
      { toFun := fun p => (p.1.1, (p.1.2, p.2))
        invFun := fun q => ((q.1, q.2.1), q.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, dotProduct]
    rw [Fintype.sum_equiv eB
      (fun p => (P.liftBob V χ₂).ofLp p * (star (P.liftBob V χ₁).ofLp) p)
      (fun q => (V (WithLp.toLp 2 fun bm => χ₂.ofLp ((q.1, bm.1), bm.2))).ofLp q.2 *
        star ((V (WithLp.toLp 2 fun bm => χ₁.ofLp ((q.1, bm.1), bm.2))).ofLp q.2))
      (fun _ => rfl)]
    rw [Fintype.sum_equiv eB
      (fun p => χ₂.ofLp p * (star χ₁.ofLp) p)
      (fun q => χ₂.ofLp ((q.1, q.2.1), q.2.2) * star (χ₁.ofLp ((q.1, q.2.1), q.2.2)))
      (fun _ => rfl)]
    conv_lhs => rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have h := V.inner_map_map
      (WithLp.toLp 2 fun bm => χ₁.ofLp ((a', bm.1), bm.2))
      (WithLp.toLp 2 fun bm => χ₂.ofLp ((a', bm.1), bm.2))
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply] using h
  have halice_isom : ∀ (V : EuclideanSpace ℂ (P.HA × Bool) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (P.HA × Bool))
      (χ₁ χ₂ : EuclideanSpace ℂ P.Joint),
      inner ℂ (P.liftAlice V χ₁) (P.liftAlice V χ₂) = inner ℂ χ₁ χ₂ := by
    intro V χ₁ χ₂
    let eA : P.Joint ≃ P.HB × (P.HA × Bool) :=
      { toFun := fun p => (p.1.2, (p.1.1, p.2))
        invFun := fun q => ((q.2.1, q.1), q.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, dotProduct]
    rw [Fintype.sum_equiv eA
      (fun p => (P.liftAlice V χ₂).ofLp p * (star (P.liftAlice V χ₁).ofLp) p)
      (fun q => (V (WithLp.toLp 2 fun am => χ₂.ofLp ((am.1, q.1), am.2))).ofLp q.2 *
        star ((V (WithLp.toLp 2 fun am => χ₁.ofLp ((am.1, q.1), am.2))).ofLp q.2))
      (fun _ => rfl)]
    rw [Fintype.sum_equiv eA
      (fun p => χ₂.ofLp p * (star χ₁.ofLp) p)
      (fun q => χ₂.ofLp ((q.2.1, q.1), q.2.2) * star (χ₁.ofLp ((q.2.1, q.1), q.2.2)))
      (fun _ => rfl)]
    conv_lhs => rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b' _ => ?_
    have h := V.inner_map_map
      (WithLp.toLp 2 fun am => χ₁.ofLp ((am.1, b'), am.2))
      (WithLp.toLp 2 fun am => χ₂.ofLp ((am.1, b'), am.2))
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply] using h
  have hrun_isom : ∀ (t : ℕ) (χ₁ χ₂ : EuclideanSpace ℂ P.Joint),
      inner ℂ (P.runSteps x y t χ₁) (P.runSteps x y t χ₂) = inner ℂ χ₁ χ₂ := by
    intro t; induction t with
    | zero => intro _ _; rfl
    | succ t ih =>
      intro χ₁ χ₂; simp only [QuantumCommProtocol.runSteps]
      by_cases ht : t < P.comm
      · simp only [ht, ↓reduceDIte]
        by_cases hsp : P.speaker ⟨t, ht⟩ = true
        · simp only [hsp, ↓reduceIte]; rw [hbob_isom, ih]
        · simp only [hsp, Bool.false_eq_true, ↓reduceIte]; rw [halice_isom, ih]
      · simp only [ht, ↓reduceDIte]; exact ih _ _
  rw [QuantumCommProtocol.finalState, QuantumCommProtocol.finalState, hbob_isom, hrun_isom]
  let eI : P.Joint ≃ (P.WorkA × P.WorkB × Bool) × (BitString w × (P.EntA × P.EntB)) :=
    { toFun := fun p => ((p.1.1.1, p.1.2.2.1, p.2), (p.1.2.1, (p.1.1.2, p.1.2.2.2)))
      invFun := fun q => (((q.1.1, q.2.2.1), (q.2.1, (q.1.2.1, q.2.2.2))), q.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, dotProduct]
  rw [Fintype.sum_equiv eI
    (fun p => (P.initState b).ofLp p * (star (P.initState a).ofLp) p)
    (fun q => (if q.1.1 = P.initA ∧ q.1.2.1 = P.initB ∧ q.1.2.2 = false then
        b.ofLp q.2.1 * P.entState.ofLp q.2.2 else 0) *
      star (if q.1.1 = P.initA ∧ q.1.2.1 = P.initB ∧ q.1.2.2 = false then
        a.ofLp q.2.1 * P.entState.ofLp q.2.2 else 0))
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (P.initA, P.initB, false)
    (fun w' _ hw' => by
      refine Finset.sum_eq_zero fun q _ => ?_
      have hne : ¬ (w'.1 = P.initA ∧ w'.2.1 = P.initB ∧ w'.2.2 = false) := fun h =>
        hw' (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
      simp [hne])
    (by simp)]
  simp only [true_and, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  have hent1 : ∑ e : P.EntA × P.EntB, P.entState.ofLp e * star (P.entState.ofLp e) = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) P.entState
    rw [P.norm_entState, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] at h
    simpa only [Pi.star_apply, RCLike.ofReal_one, one_pow] using h
  refine Finset.sum_congr rfl fun u' _ => ?_
  calc ∑ e : P.EntA × P.EntB,
        (b.ofLp u' * P.entState.ofLp e) * star (a.ofLp u' * P.entState.ofLp e)
      = (b.ofLp u' * star (a.ofLp u')) *
          ∑ e : P.EntA × P.EntB, P.entState.ofLp e * star (P.entState.ofLp e) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => by simp only [star_mul]; ring
    _ = b.ofLp u' * (star a.ofLp) u' := by rw [hent1, mul_one]; rfl

lemma QuantumCommProtocol.acceptProb_nonneg (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ (BitString w)) : 0 ≤ P.acceptProb x y ψ := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma QuantumCommProtocol.acceptProb_le_one (P : QuantumCommProtocol X Y w) (x : X) (y : Y)
    {ψ : EuclideanSpace ℂ (BitString w)} (hψ : ‖ψ‖ = 1) : P.acceptProb x y ψ ≤ 1 := by
  calc P.acceptProb x y ψ ≤ ‖P.finalState x y ψ‖ ^ 2 := by
        rw [QuantumCommProtocol.acceptProb, EuclideanSpace.norm_sq_eq]
        exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    _ = ‖ψ‖ ^ 2 := by
        have h1 := P.inner_finalState x y ψ ψ
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h1
        exact_mod_cast h1
    _ = 1 := by rw [hψ, one_pow]

end Factorization

end CslibFrontier.CommunicationComplexity
