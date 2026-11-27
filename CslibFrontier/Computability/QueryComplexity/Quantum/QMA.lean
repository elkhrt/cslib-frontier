/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Dual

import CslibFrontier.Computability.QueryComplexity.Quantum.Composition
import CslibFrontier.Computability.QueryComplexity.Quantum.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantum Merlin–Arthur Query Protocols

This module defines canonical Quantum Merlin–Arthur (QMA) query protocols built directly on
`Cslib.Quantum.State` and `Cslib.Quantum.run`, together with:

1. **Maximally-mixed witness simulation**: `QMAQueryProtocol.mixedAcceptProb`, which has degree at
   most `2 * P.queries` and satisfies `P.acceptProb x ψ ≤ 2^w * P.mixedAcceptProb x`.
2. **Literal bit-restriction closure**: `QMAQueryProtocol.comapLiteral`, transferring protocols
   across literal bit restrictions without changing witness length or query complexity.

## Main definitions

* `CslibFrontier.QueryComplexity.QMAQueryProtocol`: canonical quantum query verifier with `w`-qubit
  witness and `q` phase-oracle queries.
* `CslibFrontier.QueryComplexity.QMAQueryProtocol.acceptProb`: acceptance probability on input `x`
  and
  witness `ψ`.
* `CslibFrontier.QueryComplexity.QMAQueryProtocol.mixedAcceptProb`: average acceptance probability
  over
  the computational-basis witnesses.
* `CslibFrontier.QueryComplexity.QMAQueryProtocol.Computes`: completeness/soundness specification.
* `CslibFrontier.QueryComplexity.qmaQueryComplexity`: $\mathrm{QMA}^{dt}(f) = \min (w + q)$.

## Main results

* `CslibFrontier.QueryComplexity.mixedAcceptProb_mem_lowDegree`: the maximally-mixed acceptance
  probability has degree at most `2 * P.queries`.
* `CslibFrontier.QueryComplexity.acceptProb_le_two_pow_mul_mixedAcceptProb`: every unit witness
  accepts
  with probability at most `2^w * mixedAcceptProb`.
* `CslibFrontier.QueryComplexity.QMAQueryProtocol.comapLiteral`: closure under literal restrictions.
-/

public section

open scoped BigOperators
open Finset Cslib Cslib.BitString Cslib.Quantum

namespace CslibFrontier.QueryComplexity

/-! ### Canonical QMA Query Protocols -/

/-- A Quantum Merlin–Arthur query protocol on `N`-bit inputs with a `w`-qubit quantum witness. -/
structure QMAQueryProtocol (N w : ℕ) where
  /-- Finite computational basis of the verifier's private workspace register. -/
  Work : Type
  [fintypeWork : Fintype Work]
  [decidableEqWork : DecidableEq Work]
  /-- Number of controlled phase-oracle queries. -/
  queries : ℕ
  /-- Verifier unitaries `U_0, U_1, ..., U_queries` acting on query, control, witness, and work. -/
  unitary : ℕ → State N (BitString w × Work) ≃ₗᵢ[ℂ] State N (BitString w × Work)
  /-- Fixed initial basis state of the query, control, and work registers. -/
  initWork : Fin N × Bool × Work
  /-- Accepting measurement outcomes. -/
  accept : Finset (Fin N × Bool × (BitString w × Work))

attribute [instance] QMAQueryProtocol.fintypeWork QMAQueryProtocol.decidableEqWork

namespace QMAQueryProtocol

variable {N w : ℕ}

/-- Embed a `w`-qubit witness state `ψ` alongside the fixed initial query/control/work basis state
`P.initWork`. -/
noncomputable def embedWitness (P : QMAQueryProtocol N w)
    (ψ : EuclideanSpace ℂ (BitString w)) : State N (BitString w × P.Work) :=
  WithLp.toLp 2 fun p =>
    if (p.1, p.2.1, p.2.2.2) = P.initWork then ψ.ofLp p.2.2.1 else 0

lemma embedWitness_apply (P : QMAQueryProtocol N w) (ψ : EuclideanSpace ℂ (BitString w))
    (p : Fin N × Bool × (BitString w × P.Work)) :
    (P.embedWitness ψ).ofLp p =
      if (p.1, p.2.1, p.2.2.2) = P.initWork then ψ.ofLp p.2.2.1 else 0 := by rfl

@[simp]
lemma embedWitness_add (P : QMAQueryProtocol N w) (ψ φ : EuclideanSpace ℂ (BitString w)) :
    P.embedWitness (ψ + φ) = P.embedWitness ψ + P.embedWitness φ := by
  ext p; simp only [embedWitness_apply, PiLp.add_apply]; split_ifs <;> simp

@[simp]
lemma embedWitness_smul (P : QMAQueryProtocol N w) (c : ℂ) (ψ : EuclideanSpace ℂ (BitString w)) :
    P.embedWitness (c • ψ) = c • P.embedWitness ψ := by
  ext p; simp only [embedWitness_apply, PiLp.smul_apply, smul_eq_mul]; split_ifs <;> simp

@[simp]
lemma norm_embedWitness (P : QMAQueryProtocol N w) (ψ : EuclideanSpace ℂ (BitString w)) :
    ‖P.embedWitness ψ‖ = ‖ψ‖ := by
  have hsq : ‖P.embedWitness ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [embedWitness_apply]
    let e : (Fin N × Bool × (BitString w × P.Work)) ≃ BitString w × (Fin N × Bool × P.Work) :=
      { toFun := fun p => (p.2.2.1, (p.1, p.2.1, p.2.2.2))
        invFun := fun q => (q.2.1, q.2.2.1, (q.1, q.2.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.sum_equiv e
      (fun p => ‖if (p.1, p.2.1, p.2.2.2) = P.initWork then ψ.ofLp p.2.2.1 else 0‖ ^ 2)
      (fun q => ‖if q.2 = P.initWork then ψ.ofLp q.1 else 0‖ ^ 2)
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single P.initWork (fun q _ hq => by simp [hq]) (by simp)]
    simp
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Linear isometry embedding the witness register into the full verifier state space. -/
noncomputable def embedWitnessLI (P : QMAQueryProtocol N w) :
    EuclideanSpace ℂ (BitString w) →ₗᵢ[ℂ] State N (BitString w × P.Work) where
  toFun := P.embedWitness
  map_add' := P.embedWitness_add
  map_smul' := P.embedWitness_smul
  norm_map' := P.norm_embedWitness

@[simp]
lemma embedWitnessLI_apply (P : QMAQueryProtocol N w)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.embedWitnessLI ψ = P.embedWitness ψ := by rfl

/-- Final verifier state on input `x` and witness `ψ`. -/
noncomputable def runState (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ : EuclideanSpace ℂ (BitString w)) : State N (BitString w × P.Work) :=
  Cslib.Quantum.run (fun t => (P.unitary t).toLinearIsometry) (P.embedWitness ψ) x P.queries

lemma runState_eq_run (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.runState x ψ =
      Cslib.Quantum.run (fun t => (P.unitary t).toLinearIsometry)
        (P.embedWitness ψ) x P.queries := by rfl

@[simp]
lemma runState_add (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ φ : EuclideanSpace ℂ (BitString w)) :
    P.runState x (ψ + φ) = P.runState x ψ + P.runState x φ := by
  have hlin : ∀ t, Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry)
      (P.embedWitness ψ + P.embedWitness φ) x t =
      Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry) (P.embedWitness ψ) x t +
      Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry) (P.embedWitness φ) x t := by
    intro t
    induction t with
    | zero => simp [Cslib.Quantum.run, map_add]
    | succ t ih => simp [Cslib.Quantum.run, ih, map_add]
  simpa [runState, P.embedWitness_add] using hlin P.queries

@[simp]
lemma runState_smul (P : QMAQueryProtocol N w) (x : BitString N) (c : ℂ)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.runState x (c • ψ) = c • P.runState x ψ := by
  have hlin : ∀ t, Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry)
      (c • P.embedWitness ψ) x t =
      c • Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry) (P.embedWitness ψ) x t := by
    intro t
    induction t with
    | zero => simp [Cslib.Quantum.run, map_smul]
    | succ t ih => simp [Cslib.Quantum.run, ih, map_smul]
  simpa [runState, P.embedWitness_smul] using hlin P.queries

@[simp]
lemma norm_runState (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ : EuclideanSpace ℂ (BitString w)) : ‖P.runState x ψ‖ = ‖ψ‖ := by
  rw [runState, norm_run, norm_embedWitness]

/-- Acceptance probability of `P` on input `x` and witness `ψ`. -/
noncomputable def acceptProb (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ : EuclideanSpace ℂ (BitString w)) : ℝ :=
  measureProb (P.runState x ψ) P.accept

lemma acceptProb_eq_measureProb (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ : EuclideanSpace ℂ (BitString w)) :
    P.acceptProb x ψ = measureProb (P.runState x ψ) P.accept := by rfl

lemma acceptProb_nonneg (P : QMAQueryProtocol N w) (x : BitString N)
    (ψ : EuclideanSpace ℂ (BitString w)) : 0 ≤ P.acceptProb x ψ := by
  exact measureProb_nonneg _ _

lemma acceptProb_le_one (P : QMAQueryProtocol N w) (x : BitString N)
    {ψ : EuclideanSpace ℂ (BitString w)} (hψ : ‖ψ‖ = 1) : P.acceptProb x ψ ≤ 1 := by
  have h := measureProb_le_measureProb_univ (P.runState x ψ) P.accept
  rw [measureProb_univ, P.norm_runState, hψ, one_pow] at h
  exact h

/-- `P` computes `f` with completeness error `ε₁` and soundness error `ε₂`. -/
@[expose]
def Computes (P : QMAQueryProtocol N w) (f : BooleanFunction N) (ε₁ ε₂ : ℝ) : Prop :=
  (∀ x, f x = true → ∃ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 ∧ 1 - ε₁ ≤ P.acceptProb x ψ) ∧
  (∀ x, f x = false → ∀ ψ : EuclideanSpace ℂ (BitString w), ‖ψ‖ = 1 → P.acceptProb x ψ ≤ ε₂)

/-- Acceptance probability when the verifier is fed the maximally mixed `w`-qubit witness. -/
noncomputable def mixedAcceptProb (P : QMAQueryProtocol N w) (x : BitString N) : ℝ :=
  (2 : ℝ) ^ (-(w : ℤ)) * ∑ u : BitString w, P.acceptProb x (ket u)

end QMAQueryProtocol

/-- The QMA query complexity $\mathrm{QMA}^{dt}(f)$: the minimum `w + q` over QMA query protocols
computing `f` with completeness and soundness error at most `1 / 3`. -/
noncomputable def qmaQueryComplexity {N : ℕ} (f : BooleanFunction N) : ℕ :=
  sInf {c | ∃ (w : ℕ) (P : QMAQueryProtocol N w), P.Computes f (1 / 3) (1 / 3) ∧ w + P.queries = c}

/-- Any QMA query protocol computing `f` with error `1 / 3` upper-bounds `qmaQueryComplexity f`. -/
lemma qmaQueryComplexity_le {N w : ℕ} {f : BooleanFunction N} (P : QMAQueryProtocol N w)
    (hP : P.Computes f (1 / 3) (1 / 3)) :
    qmaQueryComplexity f ≤ w + P.queries :=
  Nat.sInf_le ⟨w, P, hP, rfl⟩

/-- If at least one QMA query protocol computes `f` with error `1 / 3`, then some protocol
achieves `qmaQueryComplexity f`. -/
lemma exists_protocol_eq_qmaQueryComplexity {N : ℕ} {f : BooleanFunction N}
    (hne : ∃ (w : ℕ) (P : QMAQueryProtocol N w), P.Computes f (1 / 3) (1 / 3)) :
    ∃ (w : ℕ) (P : QMAQueryProtocol N w),
      P.Computes f (1 / 3) (1 / 3) ∧ w + P.queries = qmaQueryComplexity f := by
  obtain ⟨w₀, P₀, hP₀⟩ := hne
  exact Nat.sInf_mem (⟨w₀ + P₀.queries, w₀, P₀, hP₀, rfl⟩ :
    {c | ∃ (w : ℕ) (P : QMAQueryProtocol N w),
      P.Computes f (1 / 3) (1 / 3) ∧ w + P.queries = c}.Nonempty)

/-! ### Maximally-mixed witness polynomial properties -/

/-- The maximally-mixed acceptance probability is a real polynomial of degree at most
`2 * P.queries`. -/
theorem mixedAcceptProb_mem_lowDegree {N w : ℕ} (P : QMAQueryProtocol N w) :
    P.mixedAcceptProb ∈ lowDegree ℝ (Fin N) (2 * P.queries) := by
  have hfun : P.mixedAcceptProb =
      (2 : ℝ) ^ (-(w : ℤ)) • ∑ u : BitString w, fun x => P.acceptProb x (ket u) := by
    ext x; simp [QMAQueryProtocol.mixedAcceptProb, Finset.sum_apply]
  rw [hfun]
  refine Submodule.smul_mem _ _ (sum_mem_lowDegree _ fun u _ => ?_)
  exact measureProb_run_mem_lowDegree (fun t => (P.unitary t).toLinearIsometry)
    (P.embedWitness (ket u)) P.queries P.accept

/-- Every unit witness accepts with probability at most `2^w * P.mixedAcceptProb x`. -/
theorem acceptProb_le_two_pow_mul_mixedAcceptProb {N w : ℕ} (P : QMAQueryProtocol N w)
    (x : BitString N) {ψ : EuclideanSpace ℂ (BitString w)} (hψ : ‖ψ‖ = 1) :
    P.acceptProb x ψ ≤ (2 : ℝ) ^ w * P.mixedAcceptProb x := by
  have hpow : (2 : ℝ) ^ w * P.mixedAcceptProb x = ∑ u : BitString w, P.acceptProb x (ket u) := by
    rw [QMAQueryProtocol.mixedAcceptProb, ← mul_assoc, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (by positivity), one_mul]
  rw [hpow]
  have hexp : P.runState x ψ = ∑ u : BitString w, ψ.ofLp u • P.runState x (ket u) := by
    have hsum : ψ = ∑ u : BitString w, ψ.ofLp u • ket u := (sum_smul_ket ψ).symm
    conv_lhs => rw [hsum]
    have hrun_sum : ∀ (S : Finset (BitString w)),
        P.runState x (∑ u ∈ S, ψ.ofLp u • ket u) =
          ∑ u ∈ S, ψ.ofLp u • P.runState x (ket u) := by
      intro S
      classical
      induction S using Finset.induction_on with
      | empty =>
        have h0 : P.runState x 0 = 0 := by
          have := P.runState_smul x 0 0; simpa using this
        simpa using h0
      | insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, P.runState_add, P.runState_smul, ih]
    exact hrun_sum Finset.univ
  have hnorm_sum : ∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  simp only [QMAQueryProtocol.acceptProb, measureProb]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [hexp, WithLp.ofLp_sum, Finset.sum_apply]
  have hcs : ‖∑ u : BitString w, (ψ.ofLp u • P.runState x (ket u)).ofLp p‖ ^ 2 ≤
      (∑ u : BitString w, ‖ψ.ofLp u‖ ^ 2) *
        (∑ u : BitString w, ‖(P.runState x (ket u)).ofLp p‖ ^ 2) := by
    have htri : ‖∑ u : BitString w, ψ.ofLp u * (P.runState x (ket u)).ofLp p‖ ≤
        ∑ u : BitString w, ‖ψ.ofLp u‖ * ‖(P.runState x (ket u)).ofLp p‖ :=
      (norm_sum_le _ _).trans_eq (by simp)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcs_real := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun u : BitString w => ‖ψ.ofLp u‖)
      (fun u : BitString w => ‖(P.runState x (ket u)).ofLp p‖)
    simpa [PiLp.smul_apply, smul_eq_mul] using hsq.trans hcs_real
  rw [hnorm_sum, one_mul] at hcs
  exact hcs

lemma mixedAcceptProb_bounds_of_computes {N w : ℕ} {P : QMAQueryProtocol N w}
    {f : BooleanFunction N} {ε₁ ε₂ : ℝ} (hP : P.Computes f ε₁ ε₂) (x : BitString N) :
    (f x = true → (1 - ε₁) * (2 : ℝ) ^ (-(w : ℤ)) ≤ P.mixedAcceptProb x ∧
      P.mixedAcceptProb x ≤ 1) ∧
    (f x = false → 0 ≤ P.mixedAcceptProb x ∧ P.mixedAcceptProb x ≤ ε₂) := by
  constructor
  · intro hfx
    obtain ⟨ψ, hψ, hacc⟩ := hP.1 x hfx
    have h1 := acceptProb_le_two_pow_mul_mixedAcceptProb P x hψ
    constructor
    · rw [zpow_neg, zpow_natCast, mul_inv_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w)]
      linarith
    · rw [QMAQueryProtocol.mixedAcceptProb, zpow_neg, zpow_natCast]
      have hsum : ∑ u : BitString w, P.acceptProb x (ket u) ≤ (2 : ℝ) ^ w := by
        calc ∑ u : BitString w, P.acceptProb x (ket u)
            ≤ ∑ _u : BitString w, (1 : ℝ) := Finset.sum_le_sum fun u _ =>
              P.acceptProb_le_one x (norm_ket u)
          _ = (2 : ℝ) ^ w := by simp
      rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w), mul_one]
      exact hsum
  · intro hfx
    constructor
    · rw [QMAQueryProtocol.mixedAcceptProb]
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun u _ => P.acceptProb_nonneg x (ket u))
    · rw [QMAQueryProtocol.mixedAcceptProb, zpow_neg, zpow_natCast]
      have hsum : ∑ u : BitString w, P.acceptProb x (ket u) ≤ (2 : ℝ) ^ w * ε₂ := by
        calc ∑ u : BitString w, P.acceptProb x (ket u)
            ≤ ∑ _u : BitString w, ε₂ := Finset.sum_le_sum fun u _ =>
              hP.2 x hfx (ket u) (norm_ket u)
          _ = (2 : ℝ) ^ w * ε₂ := by simp
      rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w)]
      exact hsum

/-! ### Literal bit-restriction closure -/

private noncomputable def comapIdxOf {M N : ℕ} (φ : BitString M → BitString N) (i : Fin N) :
    Option (Fin M) := by
  classical
  exact if h : ∃ j : Fin M, ∀ x, φ x i = x j then some (Classical.choose h) else none

private noncomputable def comapConstOf {M N : ℕ} (φ : BitString M → BitString N) (i : Fin N) :
    Bool := by
  classical
  exact if h : ∃ c : Bool, ∀ x, φ x i = c then Classical.choose h else false

private noncomputable def comapSwapEquiv {M N w : ℕ} [NeZero M] (W : Type)
    (φ : BitString M → BitString N) :
    Equiv.Perm (Fin M × Bool × (BitString w × W × Fin N × Bool)) :=
  { toFun := fun p =>
      match comapIdxOf φ p.2.2.2.2.1 with
      | some j => (p.1 + j, p.2.2.2.2.2, (p.2.2.1, (p.2.2.2.1, p.2.2.2.2.1, p.2.1)))
      | none => p
    invFun := fun p =>
      match comapIdxOf φ p.2.2.2.2.1 with
      | some j => (p.1 - j, p.2.2.2.2.2, (p.2.2.1, (p.2.2.2.1, p.2.2.2.2.1, p.2.1)))
      | none => p
    left_inv := fun ⟨m, cM, u, wk, i, b⟩ => by
      dsimp only
      cases h : comapIdxOf φ i with
      | none => simp [h]
      | some j => simp [h]
    right_inv := fun ⟨m, cM, u, wk, i, b⟩ => by
      dsimp only
      cases h : comapIdxOf φ i with
      | none => simp [h]
      | some j => simp [h] }

private noncomputable def comapConstPhase {M N w : ℕ} (W : Type) [Fintype W]
    (φ : BitString M → BitString N) :
    State M (BitString w × W × Fin N × Bool) ≃ₗᵢ[ℂ] State M (BitString w × W × Fin N × Bool) :=
  { toFun := fun ψ => WithLp.toLp 2 fun p =>
      (match comapIdxOf φ p.2.2.2.2.1 with
       | some _ => (1 : ℂ)
       | none => if p.2.2.2.2.2 && comapConstOf φ p.2.2.2.2.1 then -1 else 1) * ψ.ofLp p
    map_add' := fun ψ φ' => by ext p; simp [mul_add]
    map_smul' := fun c ψ => by
      ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    invFun := fun ψ => WithLp.toLp 2 fun p =>
      (match comapIdxOf φ p.2.2.2.2.1 with
       | some _ => (1 : ℂ)
       | none => if p.2.2.2.2.2 && comapConstOf φ p.2.2.2.2.1 then -1 else 1) * ψ.ofLp p
    left_inv := fun ψ => by
      ext p
      simp only [← mul_assoc]
      cases comapIdxOf φ p.2.2.2.2.1 <;> split_ifs <;> simp
    right_inv := fun ψ => by
      ext p
      simp only [← mul_assoc]
      cases comapIdxOf φ p.2.2.2.2.1 <;> split_ifs <;> simp
    norm_map' := fun ψ => by
      have hsq : ‖(WithLp.toLp 2 fun p =>
          (match comapIdxOf φ p.2.2.2.2.1 with
           | some _ => (1 : ℂ)
           | none => if p.2.2.2.2.2 && comapConstOf φ p.2.2.2.2.1 then -1 else 1) * ψ.ofLp p :
            State M (BitString w × W × Fin N × Bool))‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [PiLp.toLp_apply, norm_mul]
        cases comapIdxOf φ p.2.2.2.2.1 <;> split_ifs <;> simp
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private lemma comapConstPhase_apply {M N w : ℕ} (W : Type) [Fintype W]
    (φ : BitString M → BitString N) (ψ : State M (BitString w × W × Fin N × Bool))
    (p : Fin M × Bool × (BitString w × W × Fin N × Bool)) :
    (comapConstPhase W φ ψ).ofLp p =
      (match comapIdxOf φ p.2.2.2.2.1 with
       | some _ => (1 : ℂ)
       | none => if p.2.2.2.2.2 && comapConstOf φ p.2.2.2.2.1 then -1 else 1) * ψ.ofLp p :=
  rfl

private noncomputable def comapLiftU {M N w : ℕ} (W : Type) [Fintype W]
    (V : State N (BitString w × W) ≃ₗᵢ[ℂ] State N (BitString w × W)) :
    State M (BitString w × W × Fin N × Bool) ≃ₗᵢ[ℂ] State M (BitString w × W × Fin N × Bool) :=
  let e : (Fin M × Bool × (BitString w × W × Fin N × Bool)) ≃
      (Fin M × Bool) × (Fin N × Bool × (BitString w × W)) :=
    { toFun := fun p => ((p.1, p.2.1), (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1)))
      invFun := fun q => (q.1.1, q.1.2, (q.2.2.2.1, (q.2.2.2.2, q.2.1, q.2.2.1)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let toF : State M (BitString w × W × Fin N × Bool) →
      State M (BitString w × W × Fin N × Bool) := fun ψ =>
    WithLp.toLp 2 fun p =>
      (V (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q)))).ofLp
        (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1))
  let invF : State M (BitString w × W × Fin N × Bool) →
      State M (BitString w × W × Fin N × Bool) := fun ψ =>
    WithLp.toLp 2 fun p =>
      (V.symm (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q)))).ofLp
        (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1))
  { toFun := toF
    invFun := invF
    map_add' := fun ψ φ' => by
      ext p
      have h : (WithLp.toLp 2 fun q => (ψ + φ').ofLp (e.symm ((p.1, p.2.1), q))) =
          (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q))) +
          (WithLp.toLp 2 fun q => φ'.ofLp (e.symm ((p.1, p.2.1), q))) := rfl
      dsimp only [toF]
      rw [h, map_add]
      rfl
    map_smul' := fun c ψ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (c • ψ).ofLp (e.symm ((p.1, p.2.1), q))) =
          c • (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q))) := rfl
      dsimp only [toF]
      rw [h, map_smul]
      rfl
    left_inv := fun ψ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (toF ψ).ofLp (e.symm ((p.1, p.2.1), q))) =
          V (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q))) := by
        ext q; rfl
      simp only [invF, h, LinearIsometryEquiv.symm_apply_apply]; rfl
    right_inv := fun ψ => by
      ext p
      have h : (WithLp.toLp 2 fun q => (invF ψ).ofLp (e.symm ((p.1, p.2.1), q))) =
          V.symm (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q))) := by
        ext q; rfl
      simp only [toF, h, LinearIsometryEquiv.apply_symm_apply]; rfl
    norm_map' := fun ψ => by
      have hsq : ‖toF ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        dsimp only [toF]
        rw [Fintype.sum_equiv e
          (fun p => ‖(V (WithLp.toLp 2 fun q => ψ.ofLp (e.symm ((p.1, p.2.1), q)))).ofLp
            (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1))‖ ^ 2)
          (fun q => ‖(V (WithLp.toLp 2 fun r => ψ.ofLp (e.symm (q.1, r)))).ofLp q.2‖ ^ 2)
          (fun _ => rfl)]
        rw [Fintype.sum_equiv e (fun p => ‖ψ.ofLp p‖ ^ 2)
          (fun q => ‖ψ.ofLp (e.symm q)‖ ^ 2) (fun p => by simp)]
        conv_lhs => rw [Fintype.sum_prod_type]
        conv_rhs => rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun mb _ => ?_
        dsimp only
        rw [← EuclideanSpace.norm_sq_eq, V.norm_map, EuclideanSpace.norm_sq_eq]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private lemma comapLiftU_apply {M N w : ℕ} (W : Type) [Fintype W]
    (V : State N (BitString w × W) ≃ₗᵢ[ℂ] State N (BitString w × W))
    (ψ : State M (BitString w × W × Fin N × Bool))
    (p : Fin M × Bool × (BitString w × W × Fin N × Bool)) :
    (comapLiftU W V ψ).ofLp p =
      (V (WithLp.toLp 2 fun q => ψ.ofLp (p.1, p.2.1, (q.2.2.1, (q.2.2.2, q.1, q.2.1))))).ofLp
        (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1)) :=
  rfl

private noncomputable def comapEmbedN {M N w : ℕ} [NeZero M] {W : Type}
    (χ : State N (BitString w × W)) : State M (BitString w × W × Fin N × Bool) :=
  WithLp.toLp 2 fun p =>
    if p.1 = (0 : Fin M) ∧ p.2.1 = false then
      χ.ofLp (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1))
    else 0

private noncomputable def comapUnitary {M N w : ℕ} [NeZero M]
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N) (t : ℕ) :
    State M (BitString w × P.Work × Fin N × Bool) ≃ₗᵢ[ℂ]
      State M (BitString w × P.Work × Fin N × Bool) :=
  let SPre := (permute (comapSwapEquiv (w := w) P.Work φ)).trans (comapConstPhase P.Work φ)
  let SPost := (permute (comapSwapEquiv (w := w) P.Work φ)).symm
  if t = 0 then
    if P.queries = 0 then comapLiftU P.Work (P.unitary 0)
    else (comapLiftU P.Work (P.unitary 0)).trans SPre
  else if t < P.queries then
    (SPost.trans (comapLiftU P.Work (P.unitary t))).trans SPre
  else if t = P.queries then
    SPost.trans (comapLiftU P.Work (P.unitary P.queries))
  else
    LinearIsometryEquiv.refl ℂ _

/-- Pull back a `QMAQueryProtocol N w` along a literal bit restriction
`φ : BitString M → BitString N` (every output coordinate is either constant or equals some input
coordinate), preserving `w`, `queries`, and exact acceptance probabilities for every witness. -/
noncomputable def QMAQueryProtocol.comapLiteral {M N w : ℕ} (hM : 0 < M)
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N) :
    QMAQueryProtocol M w :=
  have : NeZero M := ⟨hM.ne'⟩
  { Work := P.Work × Fin N × Bool
    queries := P.queries
    unitary := comapUnitary P φ
    initWork := ((0 : Fin M), false, (P.initWork.2.2, P.initWork.1, P.initWork.2.1))
    accept := Finset.univ.filter fun p =>
      p.1 = (0 : Fin M) ∧ p.2.1 = false ∧
        (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1)) ∈ P.accept }

@[simp]
lemma QMAQueryProtocol.queries_comapLiteral {M N w : ℕ} (hM : 0 < M)
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N) :
    (P.comapLiteral hM φ).queries = P.queries := by rfl

private lemma comapUnitary_zero_of_pos {M N w : ℕ} [NeZero M]
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N) (hq : 0 < P.queries)
    (χ : State M (BitString w × P.Work × Fin N × Bool)) :
    comapUnitary P φ 0 χ =
      comapConstPhase P.Work φ (permute (comapSwapEquiv (w := w) P.Work φ)
        (comapLiftU P.Work (P.unitary 0) χ)) := by
  simp only [comapUnitary, hq.ne', ↓reduceIte]
  rfl

private lemma comapUnitary_mid {M N w : ℕ} [NeZero M]
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N) {t : ℕ}
    (ht0 : t ≠ 0) (ht : t < P.queries)
    (χ : State M (BitString w × P.Work × Fin N × Bool)) :
    comapUnitary P φ t χ =
      comapConstPhase P.Work φ (permute (comapSwapEquiv (w := w) P.Work φ)
        (comapLiftU P.Work (P.unitary t)
          ((permute (comapSwapEquiv (w := w) P.Work φ)).symm χ))) := by
  simp only [comapUnitary, ht0, ht, ↓reduceIte]
  rfl

private lemma comapUnitary_last {M N w : ℕ} [NeZero M]
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N) (hq : 0 < P.queries)
    (χ : State M (BitString w × P.Work × Fin N × Bool)) :
    comapUnitary P φ P.queries χ =
      comapLiftU P.Work (P.unitary P.queries)
        ((permute (comapSwapEquiv (w := w) P.Work φ)).symm χ) := by
  simp only [comapUnitary, hq.ne', lt_self_iff_false, ↓reduceIte]
  rfl

lemma QMAQueryProtocol.acceptProb_comapLiteral {M N w : ℕ} (hM : 0 < M)
    (P : QMAQueryProtocol N w) (φ : BitString M → BitString N)
    (hφ : ∀ i : Fin N, (∃ c : Bool, ∀ x, φ x i = c) ∨ (∃ j : Fin M, ∀ x, φ x i = x j))
    (x : BitString M) (ψ : EuclideanSpace ℂ (BitString w)) :
    (P.comapLiteral hM φ).acceptProb x ψ = P.acceptProb (φ x) ψ := by
  have : NeZero M := ⟨hM.ne'⟩
  let P' := P.comapLiteral hM φ
  have hembed_init : P'.embedWitness ψ = comapEmbedN (P.embedWitness ψ) := by
    ext ⟨m, cM, u, wk, i, b⟩
    simp only [embedWitness_apply, comapEmbedN, P', comapLiteral]
    by_cases h1 : m = (0 : Fin M) ∧ cM = false
    · rcases h1 with ⟨rfl, rfl⟩
      by_cases h2 : (i, b, wk) = P.initWork
      · rw [← h2]; simp
      · have hne : ((0 : Fin M), false, (wk, i, b)) ≠
            ((0 : Fin M), false, (P.initWork.2.2, P.initWork.1, P.initWork.2.1)) := by
          intro heq
          apply h2
          rcases Prod.mk.inj heq with ⟨_, heq2⟩
          rcases Prod.mk.inj heq2 with ⟨_, heq3⟩
          rcases Prod.mk.inj heq3 with ⟨h3, heq4⟩
          rcases Prod.mk.inj heq4 with ⟨h4, h5⟩
          exact Prod.ext h4 (Prod.ext h5 h3)
        simp only [↓reduceIte, h2, true_and, hne]
    · have hne : (m, cM, (wk, i, b)) ≠
          ((0 : Fin M), false, (P.initWork.2.2, P.initWork.1, P.initWork.2.1)) := by
        intro heq
        apply h1
        rcases Prod.mk.inj heq with ⟨h1a, heq2⟩
        rcases Prod.mk.inj heq2 with ⟨h1b, _⟩
        exact ⟨h1a, h1b⟩
      simp only [h1, ↓reduceIte, hne]
  have hrun_eq : P'.runState x ψ = comapEmbedN (P.runState (φ x) ψ) := by
    unfold QMAQueryProtocol.runState
    rw [hembed_init]
    have hperm_symm : ∀ (χ : State M (BitString w × P.Work × Fin N × Bool)) p,
        ((permute (comapSwapEquiv (w := w) P.Work φ)).symm χ).ofLp p =
          χ.ofLp (comapSwapEquiv (w := w) P.Work φ p) := by
      intro χ p
      conv_rhs => rw [← (permute (comapSwapEquiv (w := w) P.Work φ)).apply_symm_apply χ]
      rw [permute_apply, Equiv.symm_apply_apply]
    have horacle : ∀ χ : State N (BitString w × P.Work),
        (permute (comapSwapEquiv (w := w) P.Work φ)).symm
          (phaseOracle x
            (comapConstPhase P.Work φ
              (permute (comapSwapEquiv (w := w) P.Work φ) (comapEmbedN χ)))) =
        comapEmbedN (phaseOracle (φ x) χ) := by
      intro χ
      ext ⟨m, cM, u, wk, i, b⟩
      rw [hperm_symm, phaseOracle_apply, comapConstPhase_apply, permute_apply,
        Equiv.symm_apply_apply]
      cases hidx : comapIdxOf φ i with
      | some j =>
        have hj : ∀ y, φ y i = y j := by
          have hex : ∃ j' : Fin M, ∀ y, φ y i = y j' := by
            by_contra hno
            simp [comapIdxOf, hno] at hidx
          have hch : some (Classical.choose hex) = some j := by
            simpa [comapIdxOf, hex] using hidx
          exact (Option.some.inj hch) ▸ Classical.choose_spec hex
        have hswap : comapSwapEquiv (w := w) P.Work φ (m, cM, u, wk, i, b) =
            (m + j, b, u, wk, i, cM) := by
          simp [comapSwapEquiv, hidx]
        rw [hswap]
        dsimp only
        rw [hidx]
        simp only [one_mul, comapEmbedN, phaseOracle_apply, hj x]
        by_cases hm : m = (0 : Fin M) ∧ cM = false
        · rcases hm with ⟨rfl, rfl⟩
          simp
        · simp [hm]
      | none =>
        have hconst : ∀ y, φ y i = comapConstOf φ i := by
          have hno : ¬ ∃ j : Fin M, ∀ y, φ y i = y j := by
            intro hex; simp [comapIdxOf, hex] at hidx
          have hc : ∃ c : Bool, ∀ y, φ y i = c := (hφ i).resolve_right hno
          dsimp only [comapConstOf]
          simp only [hc, ↓reduceDIte]
          exact Classical.choose_spec hc
        have hswap : comapSwapEquiv (w := w) P.Work φ (m, cM, u, wk, i, b) =
            (m, cM, u, wk, i, b) := by
          simp [comapSwapEquiv, hidx]
        rw [hswap]
        dsimp only
        rw [hidx]
        simp only [comapEmbedN, phaseOracle_apply, hconst x]
        by_cases hm : m = (0 : Fin M) ∧ cM = false
        · rcases hm with ⟨rfl, rfl⟩
          by_cases hbc : (b && comapConstOf φ i) = true <;> simp [hbc]
        · simp [hm]
    have hlift : ∀ (V : State N (BitString w × P.Work) ≃ₗᵢ[ℂ] State N (BitString w × P.Work))
        (χ : State N (BitString w × P.Work)),
        comapLiftU P.Work V (comapEmbedN (M := M) χ) = comapEmbedN (M := M) (V χ) := by
      intro V χ
      ext ⟨m, cM, u, wk, i, b⟩
      rw [comapLiftU_apply]
      simp only [comapEmbedN, PiLp.toLp_apply]
      by_cases hm : m = (0 : Fin M) ∧ cM = false
      · have hslice : (WithLp.toLp 2 fun q : Fin N × Bool × (BitString w × P.Work) =>
            if m = (0 : Fin M) ∧ cM = false then
              χ.ofLp (q.1, q.2.1, (q.2.2.1, q.2.2.2)) else 0) = χ := by
          ext q; simp [hm]
        rw [hslice]
        simp [hm]
      · have hslice : (WithLp.toLp 2 fun q : Fin N × Bool × (BitString w × P.Work) =>
            if m = (0 : Fin M) ∧ cM = false then
              χ.ofLp (q.1, q.2.1, (q.2.2.1, q.2.2.2)) else 0) = 0 := by
          ext q; simp [hm]
        rw [hslice, map_zero, PiLp.zero_apply]
        simp [hm]
    rcases Nat.eq_zero_or_pos P.queries with hq0 | hqpos
    · have hq0' : P'.queries = 0 := hq0
      rw [hq0', hq0]
      simp only [Cslib.Quantum.run, P', comapLiteral, comapUnitary, hq0, ↓reduceIte,
        LinearIsometryEquiv.coe_toLinearIsometry]
      exact hlift (P.unitary 0) (P.embedWitness ψ)
    · let U' : ℕ → State M (BitString w × P.Work × Fin N × Bool) →ₗᵢ[ℂ]
          State M (BitString w × P.Work × Fin N × Bool) :=
        fun s => (comapUnitary P φ s).toLinearIsometry
      have hpre : ∀ t, t < P.queries →
          Cslib.Quantum.run U' (comapEmbedN (P.embedWitness ψ)) x t =
          comapConstPhase P.Work φ (permute (comapSwapEquiv (w := w) P.Work φ)
            (comapEmbedN (Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry)
              (P.embedWitness ψ) (φ x) t))) := by
        intro t ht
        induction t with
        | zero =>
          change comapUnitary P φ 0 (comapEmbedN (P.embedWitness ψ)) =
            comapConstPhase P.Work φ (permute (comapSwapEquiv (w := w) P.Work φ)
              (comapEmbedN ((P.unitary 0) (P.embedWitness ψ))))
          rw [comapUnitary_zero_of_pos P φ hqpos, hlift]
        | succ t ih =>
          have ht' : t < P.queries := by omega
          change comapUnitary P φ (t + 1) (phaseOracle x
            (Cslib.Quantum.run U' (comapEmbedN (P.embedWitness ψ)) x t)) =
            comapConstPhase P.Work φ (permute (comapSwapEquiv (w := w) P.Work φ)
              (comapEmbedN ((P.unitary (t + 1)) (phaseOracle (φ x)
                (Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry)
                  (P.embedWitness ψ) (φ x) t)))))
          rw [ih ht', comapUnitary_mid P φ (by omega) ht, horacle, hlift]
      have hlast : P.queries = (P.queries - 1) + 1 := by omega
      have hprev := hpre (P.queries - 1) (by omega)
      have hrun_last :
          Cslib.Quantum.run (fun s => (P'.unitary s).toLinearIsometry)
            (comapEmbedN (P.embedWitness ψ)) x P'.queries =
          comapUnitary P φ P.queries
            (phaseOracle x (Cslib.Quantum.run U' (comapEmbedN (P.embedWitness ψ)) x
              (P.queries - 1))) := by
        change Cslib.Quantum.run U' (comapEmbedN (P.embedWitness ψ)) x P.queries = _
        conv_lhs => rw [hlast]
        simp only [Cslib.Quantum.run, ← hlast]
        rfl
      have hrun_last_P :
          Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry)
            (P.embedWitness ψ) (φ x) P.queries =
          (P.unitary P.queries)
            (phaseOracle (φ x)
              (Cslib.Quantum.run (fun s => (P.unitary s).toLinearIsometry)
                (P.embedWitness ψ) (φ x) (P.queries - 1))) := by
        conv_lhs => rw [hlast]
        simp only [Cslib.Quantum.run, LinearIsometryEquiv.coe_toLinearIsometry, ← hlast]
      rw [hrun_last, hrun_last_P, hprev, comapUnitary_last P φ hqpos, horacle, hlift]
  rw [QMAQueryProtocol.acceptProb, hrun_eq]
  simp only [measureProb, comapLiteral, comapEmbedN]
  rw [Finset.sum_filter]
  let e : (Fin M × Bool × (BitString w × P.Work × Fin N × Bool)) ≃
      (Fin M × Bool) × (Fin N × Bool × (BitString w × P.Work)) :=
    { toFun := fun p => ((p.1, p.2.1), (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1)))
      invFun := fun q => (q.1.1, q.1.2, (q.2.2.2.1, (q.2.2.2.2, q.2.1, q.2.2.1)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.sum_equiv e
    (fun p => if p.1 = (0 : Fin M) ∧ p.2.1 = false ∧
        (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1)) ∈ P.accept then
        ‖if p.1 = (0 : Fin M) ∧ p.2.1 = false then
          (P.runState (φ x) ψ).ofLp (p.2.2.2.2.1, p.2.2.2.2.2, (p.2.2.1, p.2.2.2.1)) else 0‖ ^ 2
      else 0)
    (fun q => if q.1.1 = (0 : Fin M) ∧ q.1.2 = false ∧ q.2 ∈ P.accept then
        ‖if q.1.1 = (0 : Fin M) ∧ q.1.2 = false then (P.runState (φ x) ψ).ofLp q.2 else 0‖ ^ 2
      else 0)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ((0 : Fin M), false) (fun mb _ hmb => by
    refine Finset.sum_eq_zero fun q _ => ?_
    have hnot : ¬ (mb.1 = (0 : Fin M) ∧ mb.2 = false) := fun h => hmb (Prod.ext h.1 h.2)
    simp [hnot]) (by simp)]
  simp only [true_and, ↓reduceIte, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  rfl

end CslibFrontier.QueryComplexity
