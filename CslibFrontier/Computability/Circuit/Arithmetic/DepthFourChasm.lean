/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaOps
public import CslibFrontier.Computability.Circuit.Arithmetic.Permanent
public import CslibFrontier.Computability.Circuit.Arithmetic.SPCircuit
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Computability.Circuit.Depth
public import CslibFrontier.Foundations.Data.List.BalancedFold
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic Circuit Depth Reduction and the Depth-Four Chasm

This module develops homogeneous arithmetic circuits, syntactic depth-four `ΣΠΣΠ` circuits with
bounded bottom fan-in, logarithmic-depth algebraic tree balancing, and depth reduction to
subexponential-size homogeneous depth-four `ΣΠΣΠ` circuits over an arbitrary commutative semiring.

## Overview

1. **Syntactically homogeneous arithmetic circuits and homogenization**:
   `Cslib.Circuits.Arithmetic.HomogCircuit` models constant-free fan-in-two arithmetic DAG
   circuits whose gates carry positive syntactic degrees (`≥ 1`), with scalar-weighted additions
   restricted to equal-degree gates and multiplications adding degrees. Every gate computes a
   homogeneous polynomial of its syntactic degree (`HomogCircuit.isHomogeneous_gatePoly`), and
   every `HomogCircuit` compiles to an ordinary `Circuit (arithSignature K) n 1`
   (`HomogCircuit.exists_circuit`). Conversely, Strassen homogenization
   (`exists_homogCircuit_allComponents`) turns any arithmetic circuit of size `s` in `n`
   variables and any degree `d ≥ 1` into a single `HomogCircuit` of size at most
   `2 * (n + s) * d ^ 2` simultaneously computing all homogeneous components of degrees
   `1, …, d` of the circuit's output polynomial.

2. **Syntactic depth-four `ΣΠΣΠ` circuits**:
   `Cslib.Circuits.Arithmetic.DepthFourCircuit` represents a sum of products of sparse bottom
   polynomials, together with bounded-fan-in (`DepthFourCircuit.IsBounded`), homogeneity
   (`DepthFourCircuit.IsHomogeneous`, `DepthFourCircuit.IsHomogeneousBounded`), monomial size
   (`DepthFourCircuit.bottomSize`, `DepthFourCircuit.size`), and compilation to unbounded-fan-in
   formulas and circuits of product-depth at most two (`DepthFourCircuit.toSPFormula`,
   `DepthFourCircuit.toSPCircuit`).

3. **Heavy-child frontier quotients**:
   For any degree threshold `m`, `HomogCircuit.frontier` selects the multiplication gates of
   degree `> m` whose two children both have degree `≤ m`, and `HomogCircuit.quot` defines the
   formal heavy-child quotient polynomial. Both the gate frontier identity
   (`HomogCircuit.gatePoly_eq_sum_frontier`) and the quotient frontier composition identity
   (`HomogCircuit.quot_eq_sum_frontier`) hold unconditionally over every commutative semiring.

4. **Logarithmic-depth algebraic tree balancing**:
   Staged round-by-round evaluation of gates and heavy-child quotients doubles the covered degree
   range each round, compiling any homogeneous circuit of degree `d ≥ 1` into an unbounded-sum,
   fan-in-two-product `SPCircuit` of depth at most `5 * Nat.clog 2 d + 1` and product-depth at most
   `3 * Nat.clog 2 d` (`HomogCircuit.exists_spProgram_log_depth`). Combining this with Strassen
   homogenization yields logarithmic-depth `SPCircuit` depth reduction
   (`exists_spCircuit_log_depth`, `VP.exists_log_depth_spCircuit`), and compiling unbounded fan-in
   via balanced binary trees (`SPCircuit.exists_balanced_arithCircuit`) yields `O((log n) ^ 2)`
   depth over fan-in-two arithmetic circuits (`VP.exists_logSq_depth_circuit`).

5. **Depth-four chasm theorem and `VP` vs. `VNP` separation**:
   Recursively applying the gate frontier identity at threshold `m = Δ - τ` with greedy adjacent
   factor merging reduces any `HomogCircuit` gate of degree `d` to a homogeneous `ΣΠΣΠ` circuit
   with top fan-in at most `H.size ^ frontierExp τ d` and middle fan-in at most `ceilDiv (2 * d) τ`
   (`HomogCircuit.exists_depthFourCircuit`). Setting `τ = ceilDiv d t` gives the full tradeoff
   (`HomogCircuit.exists_depthFourCircuit_tradeoff`, `exists_depthFourCircuit_of_isHomogeneous`),
   and specializing to `t = max 1 (Nat.sqrt d)` proves the subexponential depth-four chasm theorem
   for circuits and for `VP` (`exists_depthFourCircuit_sqrt`, `VP.exists_homog_depthFour_chasm`,
   `VP.exists_depthFour_chasm`), together with separation corollaries showing that super-chasm
   homogeneous `ΣΠΣΠ` lower bounds separate `VP` from `VNP`
   (`not_mem_VP_of_depthFour_lower_bound`, `VP_ne_VNP_of_depthFour_lower_bound`,
   `VP_ne_VNP_of_permFamily_depthFour_lower_bound`).

6. **Concrete non-vacuity witnesses**:
   Explicit integer arithmetic and depth-four circuits witness non-vacuity of homogenization,
   logarithmic-depth reduction, the depth-four chasm bound, and product-depth-two compilation.

## Main definitions

* `Cslib.Circuits.Arithmetic.HomogGate`, `Cslib.Circuits.Arithmetic.HomogCircuit`: constant-free
  syntactically homogeneous arithmetic DAG circuits.
* `Cslib.Circuits.Arithmetic.DepthFourCircuit`: syntactic depth-four `ΣΠΣΠ` circuits and their
  homogeneity, bounded-fan-in, and size predicates.
* `Cslib.Circuits.Arithmetic.HomogCircuit.frontier`,
  `Cslib.Circuits.Arithmetic.HomogCircuit.quot`: heavy-child frontier and formal quotients.
* `Cslib.Circuits.Arithmetic.ceilDiv`, `Cslib.Circuits.Arithmetic.frontierExp`: ceiling division
  and the depth-four frontier recursion exponent.

## Main results

* `Cslib.Circuits.Arithmetic.HomogCircuit.isHomogeneous_gatePoly`: every homogeneous gate computes
  a homogeneous polynomial of its syntactic degree.
* `Cslib.Circuits.Arithmetic.exists_homogCircuit_allComponents`: Strassen homogenization of an
  arbitrary arithmetic circuit.
* `Cslib.Circuits.Arithmetic.HomogCircuit.gatePoly_eq_sum_frontier`,
  `Cslib.Circuits.Arithmetic.HomogCircuit.quot_eq_sum_frontier`: the two frontier decomposition
  identities.
* `Cslib.Circuits.Arithmetic.DepthFourCircuit.toSPFormula`: compilation of depth-four circuits
  into product-depth-two formulas.
* `Cslib.Circuits.Arithmetic.exists_spCircuit_log_depth`,
  `Cslib.Circuits.Arithmetic.SPCircuit.exists_balanced_arithCircuit`,
  `Cslib.Circuits.Arithmetic.VP.exists_log_depth_spCircuit`,
  `Cslib.Circuits.Arithmetic.VP.exists_logSq_depth_circuit`: logarithmic-depth and
  polylogarithmic-depth algebraic tree balancing.
* `Cslib.Circuits.Arithmetic.HomogCircuit.exists_depthFourCircuit`,
  `Cslib.Circuits.Arithmetic.exists_depthFourCircuit_sqrt`,
  `Cslib.Circuits.Arithmetic.exists_depthFourCircuit_of_totalDegree_le`,
  `Cslib.Circuits.Arithmetic.VP.exists_homog_depthFour_chasm`,
  `Cslib.Circuits.Arithmetic.VP.exists_depthFour_chasm`: the depth-four chasm theorems.
* `Cslib.Circuits.Arithmetic.not_mem_VP_of_depthFour_lower_bound`,
  `Cslib.Circuits.Arithmetic.VP_ne_VNP_of_depthFour_lower_bound`,
  `Cslib.Circuits.Arithmetic.VP_ne_VNP_of_permFamily_depthFour_lower_bound`: separation of `VP`
  from `VNP` via super-chasm homogeneous depth-four lower bounds.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

/-! ### : Syntactically homogeneous arithmetic circuits and homogenization -/

/-- A gate of a constant-free syntactically homogeneous arithmetic DAG circuit over `K` in `n`
variables, referencing strictly earlier gates `< g`. Scalar weights live on addition edges. -/
inductive HomogGate (K : Type u) (n g : ℕ) : Type u
  /-- The zero polynomial of formal degree `d ≥ 1`. -/
  | zero (d : ℕ)
  /-- The input variable `X i` of formal degree `1`. -/
  | var (i : Fin n)
  /-- A weighted linear combination `c₁ * u + c₂ * v` of two earlier gates of equal degree. -/
  | add (c₁ c₂ : K) (u v : Fin g)
  /-- The product `u * v` of two earlier gates of positive degrees. -/
  | mul (u v : Fin g)

/-- Cast the index bound of a `HomogGate` along a propositional equality of bounds. -/
def HomogGate.castBound {K : Type u} {n g₁ g₂ : ℕ} (h : g₁ = g₂) :
    HomogGate K n g₁ → HomogGate K n g₂ := by
  subst h
  exact id

@[simp] theorem HomogGate.castBound_rfl {K : Type u} {n g : ℕ} (x : HomogGate K n g) :
    x.castBound rfl = x :=
  rfl

/-- A constant-free syntactically homogeneous fan-in-two arithmetic DAG circuit over `K` in `n`
variables. Every gate has positive syntactic degree `≥ 1`, addition combines gates of equal degree,
and multiplication adds degrees. -/
structure HomogCircuit (K : Type u) (n : ℕ) : Type u where
  /-- Number of gates in the DAG. -/
  size : ℕ
  /-- Syntactic degree of each gate. -/
  deg : Fin size → ℕ
  /-- Every gate has positive syntactic degree. -/
  deg_pos : ∀ v, 1 ≤ deg v
  /-- The gate operation at index `v`, referring only to gates `< v`. -/
  gates : (v : Fin size) → HomogGate K n v.1
  /-- Syntactic degree compatibility of each gate with its children. -/
  gate_deg : ∀ v, match gates v with
    | .zero d => deg v = d
    | .var _ => deg v = 1
    | .add _ _ u w =>
      deg ⟨u.1, u.2.trans v.2⟩ = deg v ∧ deg ⟨w.1, w.2.trans v.2⟩ = deg v
    | .mul u w =>
      deg v = deg ⟨u.1, u.2.trans v.2⟩ + deg ⟨w.1, w.2.trans v.2⟩

namespace HomogCircuit

variable {K : Type u} {n : ℕ}

/-- The formal polynomial computed at gate `v` of a homogeneous circuit. -/
noncomputable def gatePoly [CommSemiring K] (H : HomogCircuit K n) (v : Fin H.size) :
    MvPolynomial (Fin n) K :=
  match H.gates v with
  | .zero _ => 0
  | .var i => X i
  | .add c₁ c₂ u w =>
    C c₁ * H.gatePoly ⟨u.1, u.2.trans v.2⟩ + C c₂ * H.gatePoly ⟨w.1, w.2.trans v.2⟩
  | .mul u w =>
    H.gatePoly ⟨u.1, u.2.trans v.2⟩ * H.gatePoly ⟨w.1, w.2.trans v.2⟩
termination_by v.1

/-- Direct point evaluation of gate `v` at `x : Fin n → K`. -/
def gateEval [CommSemiring K] (H : HomogCircuit K n) (x : Fin n → K) (v : Fin H.size) : K :=
  match H.gates v with
  | .zero _ => 0
  | .var i => x i
  | .add c₁ c₂ u w =>
    c₁ * H.gateEval x ⟨u.1, u.2.trans v.2⟩ + c₂ * H.gateEval x ⟨w.1, w.2.trans v.2⟩
  | .mul u w =>
    H.gateEval x ⟨u.1, u.2.trans v.2⟩ * H.gateEval x ⟨w.1, w.2.trans v.2⟩
termination_by v.1

/-- Evaluating the formal polynomial of gate `v` agrees with direct point evaluation. -/
theorem eval_gatePoly [CommSemiring K] (H : HomogCircuit K n) (x : Fin n → K) (v : Fin H.size) :
    MvPolynomial.eval x (H.gatePoly v) = H.gateEval x v := by
  induction hv : v.1 using Nat.strongRecOn generalizing v with
  | ind k ih =>
    subst hv
    rw [gatePoly, gateEval]
    cases H.gates v with
    | zero _ => simp
    | var i => simp
    | add c₁ c₂ u w =>
      simp only [map_add, map_mul, eval_C, ih u.1 u.2 ⟨u.1, u.2.trans v.2⟩ rfl,
        ih w.1 w.2 ⟨w.1, w.2.trans v.2⟩ rfl]
    | mul u w =>
      simp only [map_mul, ih u.1 u.2 ⟨u.1, u.2.trans v.2⟩ rfl,
        ih w.1 w.2 ⟨w.1, w.2.trans v.2⟩ rfl]

/-- Every gate `v` of a `HomogCircuit` computes a homogeneous polynomial of degree `H.deg v`. -/
theorem isHomogeneous_gatePoly [CommSemiring K] (H : HomogCircuit K n) (v : Fin H.size) :
    (H.gatePoly v).IsHomogeneous (H.deg v) := by
  induction hv : v.1 using Nat.strongRecOn generalizing v with
  | ind k ih =>
    subst hv
    rw [gatePoly]
    have hdeg := H.gate_deg v
    cases hg : H.gates v with
    | zero d =>
      exact isHomogeneous_zero (Fin n) K (H.deg v)
    | var i =>
      rw [hg] at hdeg
      rw [hdeg]
      exact isHomogeneous_X K i
    | add c₁ c₂ u w =>
      rw [hg] at hdeg
      have hu := ih u.1 u.2 ⟨u.1, u.2.trans v.2⟩ rfl
      have hw := ih w.1 w.2 ⟨w.1, w.2.trans v.2⟩ rfl
      rw [hdeg.1] at hu
      rw [hdeg.2] at hw
      exact (hu.C_mul c₁).add (hw.C_mul c₂)
    | mul u w =>
      rw [hg] at hdeg
      have hu := ih u.1 u.2 ⟨u.1, u.2.trans v.2⟩ rfl
      have hw := ih w.1 w.2 ⟨w.1, w.2.trans v.2⟩ rfl
      rw [hdeg]
      exact hu.mul hw

/-- The empty homogeneous circuit with zero gates. -/
def empty : HomogCircuit K n where
  size := 0
  deg := Fin.elim0
  deg_pos v := v.elim0
  gates v := v.elim0
  gate_deg v := v.elim0

/-- Append one valid homogeneous gate to `H`. -/
def push (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d) (g : HomogGate K n H.size)
    (hg : match g with
      | .zero d' => d = d'
      | .var _ => d = 1
      | .add _ _ u w => H.deg u = d ∧ H.deg w = d
      | .mul u w => d = H.deg u + H.deg w) : HomogCircuit K n where
  size := H.size + 1
  deg v := if hv : v.1 < H.size then H.deg ⟨v.1, hv⟩ else d
  deg_pos v := by
    by_cases hv : v.1 < H.size
    · simp only [hv, ↓reduceDIte]
      exact H.deg_pos ⟨v.1, hv⟩
    · simp only [hv, ↓reduceDIte]
      exact hd
  gates v :=
    if hv : v.1 < H.size then H.gates ⟨v.1, hv⟩
    else g.castBound (by omega)
  gate_deg v := by
    by_cases hv : v.1 < H.size
    · simp only [hv, ↓reduceDIte]
      have hgd := H.gate_deg ⟨v.1, hv⟩
      cases hgv : H.gates ⟨v.1, hv⟩ with
      | zero d' =>
        rw [hgv] at hgd
        exact hgd
      | var i =>
        rw [hgv] at hgd
        exact hgd
      | add c₁ c₂ u w =>
        rw [hgv] at hgd
        simp only [u.2.trans hv, w.2.trans hv, ↓reduceDIte]
        exact hgd
      | mul u w =>
        rw [hgv] at hgd
        simp only [u.2.trans hv, w.2.trans hv, ↓reduceDIte]
        exact hgd
    · have heq : v.1 = H.size := by omega
      simp only [hv, ↓reduceDIte]
      cases v with
      | mk val hlt =>
        dsimp only at heq
        subst heq
        rw [HomogGate.castBound_rfl]
        cases g with
        | zero d' => exact hg
        | var i => exact hg
        | add c₁ c₂ u w =>
          dsimp only
          simp only [u.2, w.2, ↓reduceDIte]
          exact hg
        | mul u w =>
          dsimp only
          simp only [u.2, w.2, ↓reduceDIte]
          exact hg

/-- Pushing a gate preserves the degrees of all earlier gates. -/
theorem deg_push_castSucc (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d)
    (g : HomogGate K n H.size) (hg) (v : Fin H.size) :
    (H.push d hd g hg).deg v.castSucc = H.deg v := by
  simp [push, v.2]

/-- The newly pushed gate has syntactic degree `d`. -/
theorem deg_push_last (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d)
    (g : HomogGate K n H.size) (hg) :
    (H.push d hd g hg).deg (Fin.last H.size) = d := by
  simp [push]

/-- Unfolding equation for `gatePoly`. -/
theorem gatePoly_eq [CommSemiring K] (H : HomogCircuit K n) (v : Fin H.size) :
    H.gatePoly v =
      match H.gates v with
      | .zero _ => 0
      | .var i => X i
      | .add c₁ c₂ u w =>
        C c₁ * H.gatePoly ⟨u.1, u.2.trans v.2⟩ + C c₂ * H.gatePoly ⟨w.1, w.2.trans v.2⟩
      | .mul u w =>
        H.gatePoly ⟨u.1, u.2.trans v.2⟩ * H.gatePoly ⟨w.1, w.2.trans v.2⟩ := by
  rw [gatePoly]

/-- Pushing a gate preserves the polynomials of all earlier gates. -/
theorem gatePoly_push_castSucc [CommSemiring K] (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d)
    (g : HomogGate K n H.size) (hg) (v : Fin H.size) :
    (H.push d hd g hg).gatePoly v.castSucc = H.gatePoly v := by
  induction hk : v.1 using Nat.strongRecOn generalizing v with
  | ind k ih =>
    subst hk
    rw [gatePoly_eq (H.push d hd g hg) v.castSucc, gatePoly_eq H v]
    have hgates : (H.push d hd g hg).gates v.castSucc = H.gates v := by
      simp [push, v.2]
    rw [hgates]
    cases H.gates v with
    | zero _ => rfl
    | var _ => rfl
    | add c₁ c₂ u w =>
      have hu := ih u.1 u.2 ⟨u.1, u.2.trans v.2⟩ rfl
      have hw := ih w.1 w.2 ⟨w.1, w.2.trans v.2⟩ rfl
      exact congrArg₂ (· + ·) (congrArg (C c₁ * ·) hu) (congrArg (C c₂ * ·) hw)
    | mul u w =>
      have hu := ih u.1 u.2 ⟨u.1, u.2.trans v.2⟩ rfl
      have hw := ih w.1 w.2 ⟨w.1, w.2.trans v.2⟩ rfl
      exact congrArg₂ (· * ·) hu hw

/-- Pushing a `.zero` gate computes `0`. -/
theorem gatePoly_push_zero [CommSemiring K] (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d) :
    (H.push d hd (.zero d) rfl).gatePoly (Fin.last H.size) = 0 := by
  rw [gatePoly_eq (H.push d hd (.zero d) rfl) (Fin.last H.size)]
  have hg : (H.push d hd (.zero d) rfl).gates (Fin.last H.size) = .zero d := by simp [push]
  rw [hg]

/-- Pushing a `.var i` gate computes `X i`. -/
theorem gatePoly_push_var [CommSemiring K] (H : HomogCircuit K n) (i : Fin n) :
    (H.push 1 le_rfl (.var i) rfl).gatePoly (Fin.last H.size) = X i := by
  rw [gatePoly_eq (H.push 1 le_rfl (.var i) rfl) (Fin.last H.size)]
  have hg : (H.push 1 le_rfl (.var i) rfl).gates (Fin.last H.size) = .var i := by simp [push]
  rw [hg]

/-- Pushing an `.add` gate computes the weighted linear combination of its two children. -/
theorem gatePoly_push_add [CommSemiring K] (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d)
    (c₁ c₂ : K) (u w : Fin H.size) (hg : H.deg u = d ∧ H.deg w = d) :
    (H.push d hd (.add c₁ c₂ u w) hg).gatePoly (Fin.last H.size) =
      C c₁ * H.gatePoly u + C c₂ * H.gatePoly w := by
  rw [gatePoly_eq (H.push d hd (.add c₁ c₂ u w) hg) (Fin.last H.size)]
  have hgt : (H.push d hd (.add c₁ c₂ u w) hg).gates (Fin.last H.size) = .add c₁ c₂ u w := by
    simp [push]
  rw [hgt]
  exact congrArg₂ (· + ·)
    (congrArg (C c₁ * ·) (H.gatePoly_push_castSucc d hd (.add c₁ c₂ u w) hg u))
    (congrArg (C c₂ * ·) (H.gatePoly_push_castSucc d hd (.add c₁ c₂ u w) hg w))

/-- Pushing a `.mul` gate computes the product of its two children. -/
theorem gatePoly_push_mul [CommSemiring K] (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d)
    (u w : Fin H.size) (hg : d = H.deg u + H.deg w) :
    (H.push d hd (.mul u w) hg).gatePoly (Fin.last H.size) = H.gatePoly u * H.gatePoly w := by
  rw [gatePoly_eq (H.push d hd (.mul u w) hg) (Fin.last H.size)]
  have hgt : (H.push d hd (.mul u w) hg).gates (Fin.last H.size) = .mul u w := by simp [push]
  rw [hgt]
  exact congrArg₂ (· * ·)
    (H.gatePoly_push_castSucc d hd (.mul u w) hg u)
    (H.gatePoly_push_castSucc d hd (.mul u w) hg w)

/-- `H'` extends `H` when `H.size ≤ H'.size` and every earlier gate keeps its degree and
computed polynomial. -/
def Extends [CommSemiring K] (H H' : HomogCircuit K n) : Prop :=
  ∃ hle : H.size ≤ H'.size,
    ∀ v : Fin H.size,
      H'.deg (v.castLE hle) = H.deg v ∧ H'.gatePoly (v.castLE hle) = H.gatePoly v

/-- Extension is reflexive. -/
theorem Extends.refl [CommSemiring K] (H : HomogCircuit K n) : H.Extends H :=
  ⟨le_rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Extension is transitive. -/
theorem Extends.trans [CommSemiring K] {H₁ H₂ H₃ : HomogCircuit K n}
    (h₁₂ : H₁.Extends H₂) (h₂₃ : H₂.Extends H₃) : H₁.Extends H₃ := by
  rcases h₁₂ with ⟨hle₁₂, h₁₂⟩
  rcases h₂₃ with ⟨hle₂₃, h₂₃⟩
  refine ⟨hle₁₂.trans hle₂₃, fun v => ?_⟩
  have h1 := h₁₂ v
  have h2 := h₂₃ (v.castLE hle₁₂)
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- Pushing a gate extends the circuit. -/
theorem extends_push [CommSemiring K] (H : HomogCircuit K n) (d : ℕ) (hd : 1 ≤ d)
    (g : HomogGate K n H.size) (hg) : H.Extends (H.push d hd g hg) :=
  ⟨Nat.le_succ _, fun v =>
    ⟨H.deg_push_castSucc d hd g hg v, H.gatePoly_push_castSucc d hd g hg v⟩⟩

/-- Compile a `HomogCircuit K n` into an ordinary arithmetic `Program (arithSignature K) n g`
computing all gates with at most `5 * H.size` gates. -/
theorem exists_program_of_homogCircuit [CommSemiring K] (H : HomogCircuit K n) :
    ∃ (g : ℕ) (p : Program (arithSignature K) n g) (wire : Fin H.size → Wire n g),
      g ≤ 5 * H.size ∧
      ∀ v : Fin H.size, p.trace (arithInterpretationWith K C) X (wire v) = H.gatePoly v := by
  let I := arithInterpretationWith K (C : K → MvPolynomial (Fin n) K)
  suffices ∀ (m : ℕ) (hm : m ≤ H.size),
      ∃ (g : ℕ) (p : Program (arithSignature K) n g)
        (wire : (v : Fin H.size) → v.1 < m → Wire n g),
        g ≤ 5 * m ∧
        ∀ (v : Fin H.size) (hv : v.1 < m), p.trace I X (wire v hv) = H.gatePoly v by
    obtain ⟨g, p, wire, hg, htr⟩ := this H.size le_rfl
    exact ⟨g, p, fun v => wire v v.2, hg, fun v => htr v v.2⟩
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨0, .empty, fun _ hv => absurd hv (Nat.not_lt_zero _), Nat.zero_le _,
      fun _ hv => absurd hv (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨g, p, wire, hg, htr⟩ := ih (Nat.le_of_succ_le hm)
    let v₀ : Fin H.size := ⟨m, hm⟩
    have hstep : ∃ (g' : ℕ) (p' : Program (arithSignature K) n g') (w₀ : Wire n g')
        (lift : Wire n g → Wire n g'),
        g' ≤ g + 5 ∧
        (∀ w : Wire n g, p'.trace I X (lift w) = p.trace I X w) ∧
        p'.trace I X w₀ = H.gatePoly v₀ := by
      cases hgv : H.gates v₀ with
      | zero _ =>
        let p1 : Program (arithSignature K) n (g + 1) := p.gate ⟨.const 0, Fin.elim0⟩
        refine ⟨g + 1, p1, .gate (Fin.last g), Wire.castSucc, by omega,
          fun w => p.trace_gate_castSucc _ I X w, ?_⟩
        rw [Program.trace_gate_last, gatePoly, hgv]
        simp [I]
      | var i =>
        refine ⟨g, p, .input i, id, by omega, fun _ => rfl, ?_⟩
        rw [gatePoly, hgv]
        rfl
      | add c₁ c₂ u w =>
        let wu : Wire n g := wire ⟨u.1, u.2.trans hm⟩ u.2
        let ww : Wire n g := wire ⟨w.1, w.2.trans hm⟩ w.2
        let p1 := p.gate ⟨.const c₁, Fin.elim0⟩
        let p2 := p1.gate ⟨.mul, ![.gate (Fin.last g), wu.castSucc]⟩
        let p3 := p2.gate ⟨.const c₂, Fin.elim0⟩
        let p4 := p3.gate ⟨.mul, ![.gate (Fin.last (g + 2)), ww.castSucc.castSucc.castSucc]⟩
        let w2 : Wire n (g + 4) := (Wire.gate (Fin.last (g + 1))).castSucc.castSucc
        let p5 := p4.gate ⟨.add, ![w2, .gate (Fin.last (g + 3))]⟩
        let lift : Wire n g → Wire n (g + 5) := fun x =>
          x.castSucc.castSucc.castSucc.castSucc.castSucc
        refine ⟨g + 5, p5, .gate (Fin.last (g + 4)), lift, le_rfl, fun x => ?_, ?_⟩
        · simp only [lift, p5, p4, p3, p2, p1, Program.trace_gate_castSucc]
        · have ht1 : p1.trace I X (.gate (Fin.last g)) = C c₁ := by
            rw [Program.trace_gate_last]; rfl
          have ht2 : p2.trace I X (.gate (Fin.last (g + 1))) =
              C c₁ * H.gatePoly ⟨u.1, u.2.trans hm⟩ := by
            rw [Program.trace_gate_last]
            simp only [I, arithInterpretationWith_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_fin_one, ht1, p1, Program.trace_gate_castSucc]
            exact congrArg (C c₁ * ·) (htr ⟨u.1, u.2.trans hm⟩ u.2)
          have ht3 : p3.trace I X (.gate (Fin.last (g + 2))) = C c₂ := by
            rw [Program.trace_gate_last]; rfl
          have ht4 : p4.trace I X (.gate (Fin.last (g + 3))) =
              C c₂ * H.gatePoly ⟨w.1, w.2.trans hm⟩ := by
            rw [Program.trace_gate_last]
            simp only [I, arithInterpretationWith_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_fin_one, ht3, p3, p2, p1, Program.trace_gate_castSucc]
            exact congrArg (C c₂ * ·) (htr ⟨w.1, w.2.trans hm⟩ w.2)
          rw [Program.trace_gate_last]
          simp only [I, arithInterpretationWith_add, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, w2, p4, p3, Program.trace_gate_castSucc, ht4, ht2]
          conv_rhs => rw [gatePoly, hgv]
      | mul u w =>
        let wu : Wire n g := wire ⟨u.1, u.2.trans hm⟩ u.2
        let ww : Wire n g := wire ⟨w.1, w.2.trans hm⟩ w.2
        let p1 := p.gate ⟨.mul, ![wu, ww]⟩
        refine ⟨g + 1, p1, .gate (Fin.last g), Wire.castSucc, by omega,
          fun x => p.trace_gate_castSucc _ I X x, ?_⟩
        rw [Program.trace_gate_last, gatePoly, hgv]
        simp only [I, arithInterpretationWith_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact congrArg₂ (· * ·) (htr ⟨u.1, u.2.trans hm⟩ u.2) (htr ⟨w.1, w.2.trans hm⟩ w.2)
    obtain ⟨g', p', w₀, lift, hg', hlift, hw₀⟩ := hstep
    refine ⟨g', p', fun v hv => if hlt : v.1 < m then lift (wire v hlt) else w₀, by omega,
      fun v hv => ?_⟩
    dsimp only
    by_cases hlt : v.1 < m
    · rw [dite_eq_left hlt, hlift, htr v hlt]
    · rw [dite_eq_right hlt]
      have hveq : v = v₀ := Fin.ext (show v.1 = m by omega)
      rw [hveq, hw₀]

/-- Every gate of a `HomogCircuit K n` is computed by a standard arithmetic circuit of size at
most `5 * H.size`. -/
theorem exists_circuit [CommSemiring K] (H : HomogCircuit K n) (out : Fin H.size) :
    ∃ c : Circuit (arithSignature K) n 1,
      c.polynomial 0 = H.gatePoly out ∧ c.size ≤ 5 * H.size := by
  obtain ⟨g, p, wire, hg, htr⟩ := H.exists_program_of_homogCircuit
  exact ⟨⟨p, fun _ => wire out⟩, htr out, hg⟩

end HomogCircuit

/-! ### Strassen homogenization of arbitrary arithmetic circuits -/

/-- Cauchy product formula for the degree-`δ` homogeneous component of a product of multivariate
polynomials over any commutative semiring. -/
theorem homogeneousComponent_mul_eq_sum {σ K : Type*} [CommSemiring K]
    (δ : ℕ) (P Q : MvPolynomial σ K) :
    homogeneousComponent δ (P * Q) =
      ∑ p ∈ Finset.range (δ + 1),
        homogeneousComponent p P * homogeneousComponent (δ - p) Q := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_sum]
  by_cases hed : e.degree = δ
  · rw [ite_eq_left hed, coeff_mul]
    simp_rw [coeff_mul, coeff_homogeneousComponent]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun uv huv => ?_
    have heq : uv.1 + uv.2 = e := by simpa using huv
    have hsum_deg : uv.1.degree + uv.2.degree = δ := by
      rw [← map_add, heq, hed]
    rw [Finset.sum_eq_single uv.1.degree]
    · rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · intro p _ hp
      rw [ite_eq_right hp.symm, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [ite_eq_right hed]
    symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun uv huv => ?_
    have heq : uv.1 + uv.2 = e := by simpa using huv
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases h1 : uv.1.degree = p
    · have h2 : uv.2.degree ≠ δ - p := by
        intro h2eq
        apply hed
        rw [← heq, map_add, h1, h2eq]
        omega
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- The degree-`0` homogeneous component of `P` is the constant polynomial `C (P.coeff 0)`. -/
theorem homogeneousComponent_zero_eq_C_coeff {σ K : Type*} [CommSemiring K]
    (P : MvPolynomial σ K) :
    homogeneousComponent 0 P = C (P.coeff 0) := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_C]
  by_cases he0 : e = 0
  · subst he0
    simp
  · have hne : e.degree ≠ 0 := by
      intro hz
      apply he0
      ext i
      rw [Finsupp.zero_apply]
      have hi : e i ≤ e.degree := by
        rw [Finsupp.degree_apply]
        by_cases hmem : i ∈ e.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
        · rw [Finsupp.notMem_support_iff.mp hmem]
          exact Nat.zero_le _
      omega
    rw [ite_eq_right hne, ite_eq_right (Ne.symm he0)]

/-- A homogeneous polynomial of degree `0` equals `C (P.coeff 0)`. -/
theorem eq_C_coeff_zero_of_isHomogeneous_zero {σ K : Type*} [CommSemiring K]
    {P : MvPolynomial σ K} (hP : P.IsHomogeneous 0) :
    P = C (P.coeff 0) := by
  have hself : homogeneousComponent 0 P = P := by
    rw [homogeneousComponent_of_mem hP, ite_eq_left rfl]
  conv_lhs => rw [← hself]
  exact homogeneousComponent_zero_eq_C_coeff P

/-- A homogeneous polynomial of degree `1` on `Fin n` is a linear combination of the variables. -/
theorem eq_sum_C_mul_X_of_isHomogeneous_one {K : Type*} [CommSemiring K] {n : ℕ}
    {P : MvPolynomial (Fin n) K} (hP : P.IsHomogeneous 1) :
    P = ∑ i : Fin n, C (P.coeff (Finsupp.single i 1)) * X i := by
  classical
  ext e
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_X]
  by_cases hmem : e ∈ P.support
  · have hw : e.degree = 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hmem)
    have hex : ∃ i : Fin n, e = Finsupp.single i 1 := by
      have hne : e.support.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [Finsupp.degree_apply, hemp] at hw
        simp at hw
      rcases hne with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      ext j
      rw [Finsupp.degree_apply] at hw
      have hi_pos : 1 ≤ e i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      have hi_le : e i ≤ ∑ x ∈ e.support, e x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      by_cases hji : j = i
      · subst hji
        simp only [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne hji]
        by_contra hnz
        have hj : j ∈ e.support := Finsupp.mem_support_iff.mpr hnz
        have hjer : j ∈ e.support.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
        have hsplit : ∑ x ∈ e.support, e x = e i + ∑ x ∈ e.support.erase i, e x := by
          rw [← Finset.sum_insert (Finset.notMem_erase i _), Finset.insert_erase hi]
        have hj_le : e j ≤ ∑ x ∈ e.support.erase i, e x :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hjer
        have hj_pos : 1 ≤ e j := Nat.pos_of_ne_zero hnz
        omega
    rcases hex with ⟨i, rfl⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hne : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i 1 := by
        intro heq
        have := congrArg (fun f : Fin n →₀ ℕ => f j) heq
        simp [hji] at this
      rw [ite_eq_right hne, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ i) hnot
  · have hz : P.coeff e = 0 := notMem_support_iff.mp hmem
    rw [hz]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases he : Finsupp.single i (1 : ℕ) = e
    · rw [he, hz, zero_mul]
    · rw [ite_eq_right he, mul_zero]

/-- Helper step for Strassen homogenization: given a `HomogCircuit` already containing the
degree-`1, …, δ` components of two wires `w₁, w₂` with constant terms `a₁, a₂`, append at most
`2 * δ` gates computing the degree-`δ` component of their product. -/
private theorem homogCircuit_push_mulComponent {K : Type u} [CommSemiring K] {n : ℕ}
    (H : HomogCircuit K n) (δ : ℕ) (hδ : 1 ≤ δ) (a₁ a₂ : K)
    (P₁ P₂ : MvPolynomial (Fin n) K)
    (idx₁ idx₂ : (p : ℕ) → 1 ≤ p → p ≤ δ → Fin H.size)
    (hidx₁ : ∀ p hp1 hpδ, H.deg (idx₁ p hp1 hpδ) = p ∧
      H.gatePoly (idx₁ p hp1 hpδ) = homogeneousComponent p P₁)
    (hidx₂ : ∀ p hp1 hpδ, H.deg (idx₂ p hp1 hpδ) = p ∧
      H.gatePoly (idx₂ p hp1 hpδ) = homogeneousComponent p P₂)
    (ha₁ : homogeneousComponent 0 P₁ = C a₁)
    (ha₂ : homogeneousComponent 0 P₂ = C a₂) :
    ∃ (H' : HomogCircuit K n) (out : Fin H'.size),
      H.Extends H' ∧
      H'.size ≤ H.size + 2 * δ ∧
      H'.deg out = δ ∧
      H'.gatePoly out = homogeneousComponent δ (P₁ * P₂) := by
  let u₂ := idx₂ δ hδ le_rfl
  let u₁ := idx₁ δ hδ le_rfl
  let H0 := H.push δ hδ (.add a₁ a₂ u₂ u₁)
    ⟨(hidx₂ δ hδ le_rfl).1, (hidx₁ δ hδ le_rfl).1⟩
  have hH0_ext : H.Extends H0 := H.extends_push _ _ _ _
  have hH0_deg : H0.deg (Fin.last H.size) = δ := H.deg_push_last _ _ _ _
  have hH0_poly : H0.gatePoly (Fin.last H.size) =
      C a₁ * homogeneousComponent δ P₂ + C a₂ * homogeneousComponent δ P₁ := by
    rw [H.gatePoly_push_add, (hidx₂ δ hδ le_rfl).2, (hidx₁ δ hδ le_rfl).2]
  suffices hacc : ∀ (k : ℕ) (hk : k ≤ δ - 1),
      ∃ (Hk : HomogCircuit K n) (acc : Fin Hk.size),
        H.Extends Hk ∧
        Hk.size ≤ H.size + 1 + 2 * k ∧
        Hk.deg acc = δ ∧
        Hk.gatePoly acc =
          C a₁ * homogeneousComponent δ P₂ + C a₂ * homogeneousComponent δ P₁ +
            ∑ p ∈ Finset.Ico 1 (k + 1),
              homogeneousComponent p P₁ * homogeneousComponent (δ - p) P₂ by
    obtain ⟨Hf, out, hExt, hsz, hdeg, hpoly⟩ := hacc (δ - 1) le_rfl
    refine ⟨Hf, out, hExt, by omega, hdeg, ?_⟩
    rw [hpoly, homogeneousComponent_mul_eq_sum]
    rw [Finset.sum_range_succ]
    have hsplit : Finset.range δ = {0} ∪ Finset.Ico 1 δ := by
      ext p
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega
    have hdisj : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 δ) := by
      rw [Finset.disjoint_singleton_left, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton]
    simp only [Nat.sub_zero, Nat.sub_self, ha₁, ha₂, show δ - 1 + 1 = δ by omega]
    ring
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨H0, Fin.last H.size, hH0_ext, by simp [H0, HomogCircuit.push], hH0_deg,
      by simp [hH0_poly]⟩
  | succ k ih =>
    intro hk
    obtain ⟨Hk, acc, hExt, hsz, hdeg, hpoly⟩ := ih (by omega)
    rcases hExt with ⟨hle, hpres⟩
    let p := k + 1
    have hp1 : 1 ≤ p := by omega
    have hpδ : p ≤ δ := by omega
    have hq1 : 1 ≤ δ - p := by omega
    have hqδ : δ - p ≤ δ := Nat.sub_le δ p
    let v₁ : Fin Hk.size := (idx₁ p hp1 hpδ).castLE hle
    let v₂ : Fin Hk.size := (idx₂ (δ - p) hq1 hqδ).castLE hle
    have hv₁_deg : Hk.deg v₁ = p := (hpres _).1.trans (hidx₁ p hp1 hpδ).1
    have hv₂_deg : Hk.deg v₂ = δ - p := (hpres _).1.trans (hidx₂ (δ - p) hq1 hqδ).1
    have hv₁_poly : Hk.gatePoly v₁ = homogeneousComponent p P₁ :=
      (hpres _).2.trans (hidx₁ p hp1 hpδ).2
    have hv₂_poly : Hk.gatePoly v₂ = homogeneousComponent (δ - p) P₂ :=
      (hpres _).2.trans (hidx₂ (δ - p) hq1 hqδ).2
    have hmul_deg : δ = Hk.deg v₁ + Hk.deg v₂ := by rw [hv₁_deg, hv₂_deg]; omega
    let Hm := Hk.push δ hδ (.mul v₁ v₂) hmul_deg
    have hHm_ext : Hk.Extends Hm := Hk.extends_push _ _ _ _
    let prodIdx : Fin Hm.size := Fin.last Hk.size
    let acc' : Fin Hm.size := acc.castSucc
    have hprod_deg : Hm.deg prodIdx = δ := Hk.deg_push_last _ _ _ _
    have hacc'_deg : Hm.deg acc' = δ := (Hk.deg_push_castSucc _ _ _ _ acc).trans hdeg
    let Ha := Hm.push δ hδ (.add 1 1 acc' prodIdx) ⟨hacc'_deg, hprod_deg⟩
    have hH_Hk : H.Extends Hk := ⟨hle, hpres⟩
    have hHa_ext : H.Extends Ha := hH_Hk.trans (hHm_ext.trans (Hm.extends_push _ _ _ _))
    refine ⟨Ha, Fin.last Hm.size, hHa_ext, by dsimp [Ha, Hm, HomogCircuit.push]; omega,
      Hm.deg_push_last _ _ _ _, ?_⟩
    rw [Hm.gatePoly_push_add, map_one, one_mul, one_mul,
      Hk.gatePoly_push_castSucc, Hk.gatePoly_push_mul, hpoly, hv₁_poly, hv₂_poly]
    have hIco : Finset.Ico 1 (k + 1 + 1) = insert (k + 1) (Finset.Ico 1 (k + 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIco, Finset.sum_insert (by simp)]
    change _ + homogeneousComponent (k + 1) P₁ * homogeneousComponent (δ - (k + 1)) P₂ = _
    ring

/-- **Strassen homogenization**: for any arithmetic circuit `c : Circuit (arithSignature K) n 1`
over a commutative semiring `K` and any `d ≥ 1`, there exists a constant-free syntactically
homogeneous circuit `H : HomogCircuit K n` of size at most `2 * (n + c.size) * d ^ 2` together
with gates computing `homogeneousComponent k (c.polynomial 0)` for every `1 ≤ k ≤ d`. -/
theorem exists_homogCircuit_allComponents {K : Type u} [CommSemiring K] {n d : ℕ}
    (hd : 1 ≤ d) (c : Circuit (arithSignature K) n 1) :
    ∃ (H : HomogCircuit K n) (compGate : Fin d → Fin H.size),
      H.size ≤ 2 * (n + c.size) * d ^ 2 ∧
      ∀ δ : Fin d,
        H.deg (compGate δ) = δ.1 + 1 ∧
        H.gatePoly (compGate δ) = homogeneousComponent (δ.1 + 1) (c.polynomial 0) := by
  let I := arithInterpretationWith K (C : K → MvPolynomial (Fin n) K)
  let N := n + c.size
  let wireOfNat : (k : ℕ) → k < N → Wire n c.size := fun k hk =>
    if h : k < n then .input ⟨k, h⟩ else .gate ⟨k - n, by omega⟩
  let natOfWire : Wire n c.size → ℕ := fun
    | .input i => i.1
    | .gate j => n + j.1
  have hnat_lt : ∀ w : Wire n c.size, natOfWire w < N := fun w => by
    cases w with
    | input i => dsimp [natOfWire, N]; omega
    | gate j => dsimp [natOfWire, N]; omega
  have hwire_nat : ∀ w : Wire n c.size, wireOfNat (natOfWire w) (hnat_lt w) = w := fun w => by
    cases w with
    | input i => simp [wireOfNat, natOfWire, i.2]
    | gate j =>
      simp only [wireOfNat, natOfWire]
      rw [dite_eq_right (by omega)]
      congr 1; exact Fin.ext (show n + j.1 - n = j.1 by omega)
  have hbuild : ∀ (m : ℕ) (hm : m ≤ N),
      ∃ (H : HomogCircuit K n) (tbl : (k : ℕ) → k < m → Fin d → Fin H.size),
        H.size ≤ 2 * m * d ^ 2 ∧
        ∀ (k : ℕ) (hk : k < m) (δ : Fin d),
          H.deg (tbl k hk δ) = δ.1 + 1 ∧
          H.gatePoly (tbl k hk δ) =
            homogeneousComponent (δ.1 + 1)
              (c.program.trace I X (wireOfNat k (hk.trans_le hm))) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨HomogCircuit.empty, fun _ hk => absurd hk (Nat.not_lt_zero _), Nat.zero_le _,
        fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨H, tbl, hsz, htbl⟩ := ih (Nat.le_of_succ_le hm)
      have hm_lt : m < N := hm
      let w_m : Wire n c.size := wireOfNat m hm_lt
      have hrow : ∀ (r : ℕ) (hr : r ≤ d),
          ∃ (Hr : HomogCircuit K n) (row : (q : ℕ) → q < r → Fin Hr.size),
            H.Extends Hr ∧
            Hr.size ≤ H.size + 2 * d * r ∧
            ∀ (q : ℕ) (hq : q < r),
              Hr.deg (row q hq) = q + 1 ∧
              Hr.gatePoly (row q hq) =
                homogeneousComponent (q + 1) (c.program.trace I X w_m) := by
        intro r
        induction r with
        | zero =>
          intro _
          exact ⟨H, fun _ hq => absurd hq (Nat.not_lt_zero _), HomogCircuit.Extends.refl H,
            by simp, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩
        | succ r ihr =>
          intro hr
          obtain ⟨Hr, row, hExt, hszr, hrowr⟩ := ihr (Nat.le_of_succ_le hr)
          let δ := r + 1
          have hδ1 : 1 ≤ δ := by omega
          have hstep : ∃ (Hr' : HomogCircuit K n) (out : Fin Hr'.size),
              Hr.Extends Hr' ∧
              Hr'.size ≤ Hr.size + 2 * d ∧
              Hr'.deg out = δ ∧
              Hr'.gatePoly out = homogeneousComponent δ (c.program.trace I X w_m) := by
            cases hw : w_m with
            | input i =>
              by_cases hr0 : r = 0
              · subst hr0
                let Hr' := Hr.push 1 le_rfl (.var i) rfl
                refine ⟨Hr', Fin.last Hr.size, Hr.extends_push _ _ _ _,
                  by dsimp [Hr', HomogCircuit.push]; omega, Hr.deg_push_last _ _ _ _, ?_⟩
                rw [Hr.gatePoly_push_var, Program.trace_input,
                  homogeneousComponent_of_mem (isHomogeneous_X K i), ite_eq_left rfl]
              · let Hr' := Hr.push δ hδ1 (.zero δ) rfl
                refine ⟨Hr', Fin.last Hr.size, Hr.extends_push _ _ _ _,
                  by dsimp [Hr', HomogCircuit.push]; omega, Hr.deg_push_last _ _ _ _, ?_⟩
                rw [Hr.gatePoly_push_zero, Program.trace_input,
                  homogeneousComponent_of_mem (isHomogeneous_X K i), ite_eq_right (by omega)]
            | gate j =>
              have hjm : n + j.1 = m := by
                simp only [w_m, wireOfNat] at hw
                by_cases hmn : m < n
                · rw [dite_eq_left hmn] at hw; cases hw
                · rw [dite_eq_right hmn] at hw
                  injection hw with hj
                  have := congrArg Fin.val hj
                  dsimp at this
                  omega
              have htr_j : c.program.trace I X (.gate j) =
                  I (c.program.lines j).op fun a =>
                    c.program.trace I X ((c.program.lines j).wires a) :=
                c.program.trace_gate I X j
              have hlt_wire : ∀ a, natOfWire ((c.program.lines j).wires a) < m := by
                intro a
                cases hwa : (c.program.lines j).wires a with
                | input i =>
                  have hi := i.2
                  dsimp [natOfWire]
                  omega
                | gate j' =>
                  have := c.program.lt_of_lines_wires_eq_gate j a j' hwa
                  dsimp [natOfWire]
                  omega
              rcases hExt with ⟨hleH, hpresH⟩
              generalize hline : c.program.lines j = L at htr_j hlt_wire
              rcases L with ⟨op, ws⟩
              cases op with
              | const a =>
                let Hr' := Hr.push δ hδ1 (.zero δ) rfl
                refine ⟨Hr', Fin.last Hr.size, Hr.extends_push _ _ _ _,
                  by dsimp [Hr', HomogCircuit.push]; omega, Hr.deg_push_last _ _ _ _, ?_⟩
                rw [Hr.gatePoly_push_zero, htr_j]
                simp only [I, arithInterpretationWith_const,
                  homogeneousComponent_of_mem (isHomogeneous_C (Fin n) a),
                  ite_eq_right (show δ ≠ 0 by omega)]
              | add =>
                let k₀ := natOfWire (ws 0)
                let k₁ := natOfWire (ws 1)
                have hk₀ : k₀ < m := hlt_wire 0
                have hk₁ : k₁ < m := hlt_wire 1
                let u₀ : Fin Hr.size := (tbl k₀ hk₀ ⟨r, hr⟩).castLE hleH
                let u₁ : Fin Hr.size := (tbl k₁ hk₁ ⟨r, hr⟩).castLE hleH
                have hu₀_deg : Hr.deg u₀ = δ := (hpresH _).1.trans (htbl k₀ hk₀ ⟨r, hr⟩).1
                have hu₁_deg : Hr.deg u₁ = δ := (hpresH _).1.trans (htbl k₁ hk₁ ⟨r, hr⟩).1
                have hu₀_poly : Hr.gatePoly u₀ =
                    homogeneousComponent δ (c.program.trace I X (ws 0)) := by
                  refine (hpresH _).2.trans ((htbl k₀ hk₀ ⟨r, hr⟩).2.trans ?_)
                  rw [hwire_nat (ws 0)]
                have hu₁_poly : Hr.gatePoly u₁ =
                    homogeneousComponent δ (c.program.trace I X (ws 1)) := by
                  refine (hpresH _).2.trans ((htbl k₁ hk₁ ⟨r, hr⟩).2.trans ?_)
                  rw [hwire_nat (ws 1)]
                let Hr' := Hr.push δ hδ1 (.add 1 1 u₀ u₁) ⟨hu₀_deg, hu₁_deg⟩
                refine ⟨Hr', Fin.last Hr.size, Hr.extends_push _ _ _ _,
                  by dsimp [Hr', HomogCircuit.push]; omega, Hr.deg_push_last _ _ _ _, ?_⟩
                rw [Hr.gatePoly_push_add, htr_j]
                simp only [I, arithInterpretationWith_add, map_one, one_mul, map_add,
                  hu₀_poly, hu₁_poly]
              | mul =>
                let k₀ := natOfWire (ws 0)
                let k₁ := natOfWire (ws 1)
                have hk₀ : k₀ < m := hlt_wire 0
                have hk₁ : k₁ < m := hlt_wire 1
                let P₀ := c.program.trace I X (ws 0)
                let P₁ := c.program.trace I X (ws 1)
                let idx₀ : (p : ℕ) → 1 ≤ p → p ≤ δ → Fin Hr.size := fun p hp1 hpδ =>
                  (tbl k₀ hk₀ ⟨p - 1, by omega⟩).castLE hleH
                let idx₁ : (p : ℕ) → 1 ≤ p → p ≤ δ → Fin Hr.size := fun p hp1 hpδ =>
                  (tbl k₁ hk₁ ⟨p - 1, by omega⟩).castLE hleH
                have hidx₀ : ∀ p hp1 hpδ, Hr.deg (idx₀ p hp1 hpδ) = p ∧
                    Hr.gatePoly (idx₀ p hp1 hpδ) = homogeneousComponent p P₀ := fun p hp1 hpδ => by
                  have h := htbl k₀ hk₀ ⟨p - 1, by omega⟩
                  have hp := hpresH (tbl k₀ hk₀ ⟨p - 1, by omega⟩)
                  refine ⟨hp.1.trans (by dsimp at h; omega), hp.2.trans ?_⟩
                  rw [h.2, show p - 1 + 1 = p by omega, hwire_nat (ws 0)]
                have hidx₁ : ∀ p hp1 hpδ, Hr.deg (idx₁ p hp1 hpδ) = p ∧
                    Hr.gatePoly (idx₁ p hp1 hpδ) = homogeneousComponent p P₁ := fun p hp1 hpδ => by
                  have h := htbl k₁ hk₁ ⟨p - 1, by omega⟩
                  have hp := hpresH (tbl k₁ hk₁ ⟨p - 1, by omega⟩)
                  refine ⟨hp.1.trans (by dsimp at h; omega), hp.2.trans ?_⟩
                  rw [h.2, show p - 1 + 1 = p by omega, hwire_nat (ws 1)]
                obtain ⟨Hr', out, hExt', hsz', hdeg', hpoly'⟩ :=
                  homogCircuit_push_mulComponent Hr δ hδ1 (P₀.coeff 0) (P₁.coeff 0) P₀ P₁
                    idx₀ idx₁ hidx₀ hidx₁
                    (homogeneousComponent_zero_eq_C_coeff P₀)
                    (homogeneousComponent_zero_eq_C_coeff P₁)
                refine ⟨Hr', out, hExt', by omega, hdeg', ?_⟩
                rw [hpoly', htr_j]
                rfl
          obtain ⟨Hr', out, hExt', hsz', hdeg', hpoly'⟩ := hstep
          rcases hExt' with ⟨hle', hpres'⟩
          refine ⟨Hr', fun q hq => if hlt : q < r then (row q hlt).castLE hle' else out,
            hExt.trans ⟨hle', hpres'⟩, ?_, fun q hq => ?_⟩
          · calc
              Hr'.size ≤ Hr.size + 2 * d := hsz'
              _ ≤ H.size + 2 * d * r + 2 * d := Nat.add_le_add_right hszr _
              _ = H.size + 2 * d * (r + 1) := by ring
          · dsimp only
            by_cases hlt : q < r
            · rw [dite_eq_left hlt]
              exact ⟨(hpres' _).1.trans (hrowr q hlt).1, (hpres' _).2.trans (hrowr q hlt).2⟩
            · rw [dite_eq_right hlt]
              have hqr : q = r := by omega
              subst hqr
              exact ⟨hdeg', hpoly'⟩
      obtain ⟨H', row, hExt, hsz', hrow'⟩ := hrow d le_rfl
      rcases hExt with ⟨hle, hpres⟩
      refine ⟨H', fun k hk δ => if hlt : k < m then (tbl k hlt δ).castLE hle else row δ.1 δ.2,
        ?_, fun k hk δ => ?_⟩
      · calc
          H'.size ≤ H.size + 2 * d * d := hsz'
          _ ≤ 2 * m * d ^ 2 + 2 * d * d := Nat.add_le_add_right hsz _
          _ = 2 * (m + 1) * d ^ 2 := by ring
      · dsimp only
        by_cases hlt : k < m
        · rw [dite_eq_left hlt]
          exact ⟨(hpres _).1.trans (htbl k hlt δ).1, (hpres _).2.trans (htbl k hlt δ).2⟩
        · rw [dite_eq_right hlt]
          have hkm : k = m := by omega
          subst hkm
          exact hrow' δ.1 δ.2
  obtain ⟨H, tbl, hsz, htbl⟩ := hbuild N le_rfl
  let k_out := natOfWire (c.outputs 0)
  have hk_out : k_out < N := hnat_lt (c.outputs 0)
  refine ⟨H, fun δ => tbl k_out hk_out δ, hsz, fun δ => ?_⟩
  rcases htbl k_out hk_out δ with ⟨hdeg, hpoly⟩
  refine ⟨hdeg, hpoly.trans ?_⟩
  rw [hwire_nat (c.outputs 0)]
  rfl

/-- Strassen homogenization for a single homogeneous component of degree `d ≥ 1`. -/
theorem exists_homogCircuit_homogeneousComponent {K : Type u} [CommSemiring K] {n d : ℕ}
    (hd : 1 ≤ d) (c : Circuit (arithSignature K) n 1) :
    ∃ (H : HomogCircuit K n) (out : Fin H.size),
      H.size ≤ 2 * (n + c.size) * d ^ 2 ∧
      H.deg out = d ∧
      H.gatePoly out = homogeneousComponent d (c.polynomial 0) := by
  obtain ⟨H, compGate, hsz, hcomp⟩ := exists_homogCircuit_allComponents hd c
  refine ⟨H, compGate ⟨d - 1, by omega⟩, hsz, ?_⟩
  simpa [show d - 1 + 1 = d by omega] using hcomp ⟨d - 1, by omega⟩

/-- Strassen homogenization for a circuit computing a homogeneous polynomial of degree `d ≥ 1`. -/
theorem exists_homogCircuit_of_isHomogeneous {K : Type u} [CommSemiring K] {n d : ℕ}
    (hd : 1 ≤ d) (c : Circuit (arithSignature K) n 1)
    (hhom : (c.polynomial 0).IsHomogeneous d) :
    ∃ (H : HomogCircuit K n) (out : Fin H.size),
      H.size ≤ 2 * (n + c.size) * d ^ 2 ∧
      H.deg out = d ∧
      H.gatePoly out = c.polynomial 0 := by
  obtain ⟨H, out, hsz, hdeg, hpoly⟩ := exists_homogCircuit_homogeneousComponent hd c
  rw [homogeneousComponent_of_mem hhom, ite_eq_left rfl] at hpoly
  exact ⟨H, out, hsz, hdeg, hpoly⟩

/-! ### : Syntactic depth-four `ΣΠΣΠ` circuits -/

/-- A syntactic depth-four `ΣΠΣΠ` arithmetic circuit over variables `σ` and coefficients `K`,
representing `∑ i : Fin topFanin, ∏ j : Fin (prodFanin i), factors i j`, where each bottom factor
`factors i j` is a sparse `ΣΠ` polynomial (sum of monomials). -/
structure DepthFourCircuit (K : Type u) (σ : Type*) [CommSemiring K] where
  /-- Top sum fan-in (number of middle product gates). -/
  topFanin : ℕ
  /-- Middle product fan-in of each summand. -/
  prodFanin : Fin topFanin → ℕ
  /-- Bottom `ΣΠ` polynomial feeding each input of each middle product gate. -/
  factors : (i : Fin topFanin) → Fin (prodFanin i) → MvPolynomial σ K

namespace DepthFourCircuit

variable {K : Type u} {σ : Type*} [CommSemiring K]

/-- The formal polynomial computed by a depth-four `ΣΠΣΠ` circuit. -/
noncomputable def polynomial (C : DepthFourCircuit K σ) : MvPolynomial σ K :=
  ∑ i : Fin C.topFanin, ∏ j : Fin (C.prodFanin i), C.factors i j

/-- `C` is a `ΣΠ^{[a]}ΣΠ^{[τ]}` circuit: every middle product gate has fan-in at most `a`, and
every bottom polynomial has total degree (bottom product fan-in) at most `τ`. -/
def IsBounded (C : DepthFourCircuit K σ) (a τ : ℕ) : Prop :=
  (∀ i, C.prodFanin i ≤ a) ∧ (∀ i j, (C.factors i j).totalDegree ≤ τ)

/-- `C` is syntactically homogeneous of degree `d`: every bottom factor is homogeneous and the
degrees in each middle product gate sum to `d`. -/
def IsHomogeneous (C : DepthFourCircuit K σ) (d : ℕ) : Prop :=
  ∀ i, ∃ degs : Fin (C.prodFanin i) → ℕ,
    (∑ j, degs j) = d ∧ ∀ j, (C.factors i j).IsHomogeneous (degs j)

/-- `C` is a homogeneous `ΣΠ^{[a]}ΣΠ^{[τ]}` circuit of degree `d` whose bottom factors all have
positive homogeneous degree `1 ≤ degs i j ≤ τ`. -/
def IsHomogeneousBounded (C : DepthFourCircuit K σ) (d a τ : ℕ) : Prop :=
  (∀ i, C.prodFanin i ≤ a) ∧
  ∀ i, ∃ degs : Fin (C.prodFanin i) → ℕ,
    (∑ j, degs j) = d ∧
    (∀ j, 1 ≤ degs j ∧ degs j ≤ τ) ∧
    (∀ j, (C.factors i j).IsHomogeneous (degs j))

/-- Total number of bottom monomials across all bottom `ΣΠ` polynomials of `C`. -/
noncomputable def bottomSize (C : DepthFourCircuit K σ) : ℕ :=
  ∑ i : Fin C.topFanin, ∑ j : Fin (C.prodFanin i), (C.factors i j).support.card

/-- Total syntactic size of `C`: the top sum gate, all middle product gates, and all bottom
monomials. -/
noncomputable def size (C : DepthFourCircuit K σ) : ℕ :=
  1 + C.topFanin + C.bottomSize

/-- A homogeneous depth-four circuit of degree `d` computes a homogeneous polynomial of degree
`d`. -/
theorem isHomogeneous_polynomial {C : DepthFourCircuit K σ} {d : ℕ} (hC : C.IsHomogeneous d) :
    C.polynomial.IsHomogeneous d := by
  unfold polynomial
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
  obtain ⟨degs, hsum, hfac⟩ := hC i
  rw [← hsum]
  exact MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => hfac j

/-- Every `IsHomogeneousBounded d a τ` circuit is both homogeneous of degree `d` and bounded
`ΣΠ^{[a]}ΣΠ^{[τ]}`. -/
theorem IsHomogeneousBounded.isHomogeneous {C : DepthFourCircuit K σ} {d a τ : ℕ}
    (hC : C.IsHomogeneousBounded d a τ) : C.IsHomogeneous d := fun i =>
  let ⟨degs, hsum, _, hfac⟩ := hC.2 i
  ⟨degs, hsum, hfac⟩

/-- A homogeneous polynomial of degree `δ` has total degree at most `δ`. -/
theorem totalDegree_le_of_isHomogeneous {P : MvPolynomial σ K} {δ : ℕ}
    (hP : P.IsHomogeneous δ) : P.totalDegree ≤ δ := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have hw := hP (mem_support_iff.mp hm)
  simpa [Finsupp.weight_apply, Finsupp.sum] using hw.le

/-- Every `IsHomogeneousBounded d a τ` circuit satisfies `IsBounded a τ`. -/
theorem IsHomogeneousBounded.isBounded {C : DepthFourCircuit K σ} {d a τ : ℕ}
    (hC : C.IsHomogeneousBounded d a τ) : C.IsBounded a τ := by
  refine ⟨hC.1, fun i j => ?_⟩
  obtain ⟨degs, _, hdeg, hfac⟩ := hC.2 i
  exact (totalDegree_le_of_isHomogeneous (hfac j)).trans (hdeg j).2

/-- Monotonicity of `IsBounded` in both middle and bottom fan-in bounds. -/
theorem IsBounded.mono {C : DepthFourCircuit K σ} {a₁ a₂ τ₁ τ₂ : ℕ}
    (hC : C.IsBounded a₁ τ₁) (ha : a₁ ≤ a₂) (hτ : τ₁ ≤ τ₂) : C.IsBounded a₂ τ₂ :=
  ⟨fun i => (hC.1 i).trans ha, fun i j => (hC.2 i j).trans hτ⟩

/-- Monotonicity of `IsHomogeneousBounded` in middle and bottom fan-in bounds. -/
theorem IsHomogeneousBounded.mono {C : DepthFourCircuit K σ} {d a₁ a₂ τ₁ τ₂ : ℕ}
    (hC : C.IsHomogeneousBounded d a₁ τ₁) (ha : a₁ ≤ a₂) (hτ : τ₁ ≤ τ₂) :
    C.IsHomogeneousBounded d a₂ τ₂ :=
  ⟨fun i => (hC.1 i).trans ha, fun i =>
    let ⟨degs, hsum, hdeg, hfac⟩ := hC.2 i
    ⟨degs, hsum, fun j => ⟨(hdeg j).1, (hdeg j).2.trans hτ⟩, hfac⟩⟩

/-- Support cardinality of a homogeneous polynomial of degree `δ` in `n` variables is at most
`Nat.choose (n + δ - 1) δ`. -/
theorem card_support_le_choose_of_isHomogeneous {n δ : ℕ} {P : MvPolynomial (Fin n) K}
    (hP : P.IsHomogeneous δ) :
    P.support.card ≤ (n + δ - 1).choose δ := by
  classical
  have hsub : P.support ⊆ (Finset.univ : Finset (Fin n)).finsuppAntidiag δ := by
    intro m hm
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    have hw : m.degree = δ := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hm)
    rw [← hw, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ m.support)
      (fun x _ hx => Finsupp.notMem_support_iff.mp hx)).symm
  calc
    P.support.card ≤ ((Finset.univ : Finset (Fin n)).finsuppAntidiag δ).card :=
      Finset.card_le_card hsub
    _ = (n + δ - 1).choose δ := by
      simpa using Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) δ

/-- For `1 ≤ n` and `δ ≤ τ`, `(n + δ - 1).choose δ ≤ (n + τ - 1).choose τ`. -/
theorem choose_monomialCount_mono {n δ τ : ℕ} (hn : 1 ≤ n) (hδτ : δ ≤ τ) :
    (n + δ - 1).choose δ ≤ (n + τ - 1).choose τ := by
  rw [← Nat.choose_symm (by omega : δ ≤ n + δ - 1),
    ← Nat.choose_symm (by omega : τ ≤ n + τ - 1)]
  rw [show n + δ - 1 - δ = n - 1 by omega, show n + τ - 1 - τ = n - 1 by omega]
  exact Nat.choose_le_choose (n - 1) (by omega)

/-- Every homogeneous `ΣΠ^{[a]}ΣΠ^{[τ]}` circuit in `n ≥ 1` variables has bottom monomial count
at most `C.topFanin * a * (n + τ - 1).choose τ`. -/
theorem bottomSize_le_of_isHomogeneousBounded {n d a τ : ℕ} (hn : 1 ≤ n)
    {C : DepthFourCircuit K (Fin n)} (hC : C.IsHomogeneousBounded d a τ) :
    C.bottomSize ≤ C.topFanin * a * (n + τ - 1).choose τ := by
  unfold bottomSize
  calc
    ∑ i : Fin C.topFanin, ∑ j : Fin (C.prodFanin i), (C.factors i j).support.card
        ≤ ∑ i : Fin C.topFanin, ∑ _j : Fin (C.prodFanin i), (n + τ - 1).choose τ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      obtain ⟨degs, _, hdeg, hfac⟩ := hC.2 i
      exact (card_support_le_choose_of_isHomogeneous (hfac j)).trans
        (choose_monomialCount_mono hn (hdeg j).2)
    _ ≤ ∑ _i : Fin C.topFanin, a * (n + τ - 1).choose τ := by
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (hC.1 i)
    _ = C.topFanin * a * (n + τ - 1).choose τ := by
      simp [mul_assoc]

/-- The constant-polynomial depth-four circuit of top fan-in `1` and middle fan-in `1`. -/
noncomputable def ofConst (c : K) : DepthFourCircuit K σ where
  topFanin := 1
  prodFanin _ := 1
  factors _ _ := C c

@[simp] theorem polynomial_ofConst (c : K) : (ofConst (σ := σ) c).polynomial = C c := by
  change (∑ _i : Fin 1, ∏ _j : Fin 1, (C c : MvPolynomial σ K)) = C c
  simp

theorem isBounded_ofConst (c : K) {a τ : ℕ} (ha : 1 ≤ a) :
    (ofConst (σ := σ) c).IsBounded a τ :=
  ⟨fun _ => ha, fun _ _ => by simp [ofConst]⟩

/-- Sum of two depth-four circuits, adding their top fan-ins. -/
def add (C₁ C₂ : DepthFourCircuit K σ) : DepthFourCircuit K σ where
  topFanin := C₁.topFanin + C₂.topFanin
  prodFanin := Fin.append C₁.prodFanin C₂.prodFanin
  factors i :=
    Fin.addCases
      (motive := fun k => Fin (Fin.append C₁.prodFanin C₂.prodFanin k) → MvPolynomial σ K)
      (fun i₁ j => C₁.factors i₁ (Fin.cast (Fin.append_left _ _ i₁) j))
      (fun i₂ j => C₂.factors i₂ (Fin.cast (Fin.append_right _ _ i₂) j)) i

/-- The sum of two depth-four circuits computes the sum of their polynomials. -/
theorem polynomial_add (C₁ C₂ : DepthFourCircuit K σ) :
    (C₁.add C₂).polynomial = C₁.polynomial + C₂.polynomial := by
  unfold polynomial add
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i₁ _ => ?_
    simp only [Fin.addCases_left]
    exact Finset.prod_bij (fun j _ => Fin.cast (Fin.append_left _ _ i₁) j)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Fin.cast_injective _ h)
      (fun j _ => ⟨Fin.cast (Fin.append_left _ _ i₁).symm j, Finset.mem_univ _, by ext; rfl⟩)
      (fun _ _ => rfl)
  · refine Finset.sum_congr rfl fun i₂ _ => ?_
    simp only [Fin.addCases_right]
    exact Finset.prod_bij (fun j _ => Fin.cast (Fin.append_right _ _ i₂) j)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Fin.cast_injective _ h)
      (fun j _ => ⟨Fin.cast (Fin.append_right _ _ i₂).symm j, Finset.mem_univ _, by ext; rfl⟩)
      (fun _ _ => rfl)

/-- `IsBounded` is preserved under `DepthFourCircuit.add`. -/
theorem isBounded_add {C₁ C₂ : DepthFourCircuit K σ} {a τ : ℕ}
    (h₁ : C₁.IsBounded a τ) (h₂ : C₂.IsBounded a τ) : (C₁.add C₂).IsBounded a τ := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · induction i using Fin.addCases with
    | left i₁ => simpa [add] using h₁.1 i₁
    | right i₂ => simpa [add] using h₂.1 i₂
  · induction i using Fin.addCases with
    | left i₁ => simpa [add] using h₁.2 i₁ _
    | right i₂ => simpa [add] using h₂.2 i₂ _

/-- Compile a `DepthFourCircuit K (Fin n)` into an unbounded-fan-in `SPFormula K n` of
product-depth at most `2` (a syntactic depth-four `ΣΠΣΠ` formula). -/
noncomputable def toSPFormula {n : ℕ} (C : DepthFourCircuit K (Fin n)) : SPFormula K n :=
  SPFormula.add (fun _ => 1) fun i =>
    SPFormula.mul fun j => SPFormula.ofSparse (C.factors i j)

/-- The compiled `SPFormula` computes the exact same polynomial as `C`. -/
@[simp] theorem polynomial_toSPFormula {n : ℕ} (C : DepthFourCircuit K (Fin n)) :
    C.toSPFormula.polynomial = C.polynomial := by
  simp [toSPFormula, polynomial]

/-- The compiled `SPFormula` has product-depth at most `2`. -/
theorem productDepth_toSPFormula_le {n : ℕ} (C : DepthFourCircuit K (Fin n)) :
    C.toSPFormula.productDepth ≤ 2 := by
  rw [toSPFormula, SPFormula.productDepth_add]
  refine Finset.sup_le fun i _ => ?_
  rw [SPFormula.productDepth_mul]
  exact Nat.add_le_add_right
    (Finset.sup_le fun j _ => SPFormula.productDepth_ofSparse_le (C.factors i j)) 1

/-- Node-count bound for `C.toSPFormula` on a `ΣΠ^{[a]}ΣΠ^{[τ]}` circuit. -/
theorem nodeCount_toSPFormula_le {n a τ : ℕ} {C : DepthFourCircuit K (Fin n)}
    (hC : C.IsBounded a τ) :
    C.toSPFormula.nodeCount ≤
      1 + C.topFanin * (1 + a) + C.bottomSize * (τ + 1) := by
  rw [toSPFormula, SPFormula.add, Formula.nodeCount_gate]
  have hterm : ∀ i : Fin C.topFanin,
      (SPFormula.mul fun j => SPFormula.ofSparse (C.factors i j)).nodeCount ≤
        1 + a + (∑ j : Fin (C.prodFanin i), (C.factors i j).support.card) * (τ + 1) := by
    intro i
    rw [SPFormula.mul, Formula.nodeCount_gate]
    have hsum :
        (∑ j : Fin (C.prodFanin i), (SPFormula.ofSparse (C.factors i j)).nodeCount) ≤
          ∑ j : Fin (C.prodFanin i), ((C.factors i j).support.card * (τ + 1) + 1) := by
      refine Finset.sum_le_sum fun j _ => (SPFormula.nodeCount_ofSparse_le _).trans ?_
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hC.2 i j) 1)) 1
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
    have hi := hC.1 i
    exact (Nat.add_le_add_right hsum 1).trans (by omega)
  calc
    (∑ i : Fin C.topFanin,
        (SPFormula.mul fun j => SPFormula.ofSparse (C.factors i j)).nodeCount) + 1
        ≤ (∑ i : Fin C.topFanin,
            (1 + a + (∑ j : Fin (C.prodFanin i), (C.factors i j).support.card) * (τ + 1))) + 1 :=
      Nat.add_le_add_right (Finset.sum_le_sum fun i _ => hterm i) 1
    _ = 1 + C.topFanin * (1 + a) + C.bottomSize * (τ + 1) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, bottomSize]
      ring

/-- Compile a `DepthFourCircuit K (Fin n)` into an `SPCircuit K n` of product-depth at most `2`. -/
noncomputable def toSPCircuit {n : ℕ} (C : DepthFourCircuit K (Fin n)) : SPCircuit K n :=
  C.toSPFormula.toCircuit

@[simp] theorem polynomial_toSPCircuit {n : ℕ} (C : DepthFourCircuit K (Fin n)) :
    C.toSPCircuit.polynomial = C.polynomial := by
  rw [toSPCircuit, SPCircuit.polynomial_toCircuit, polynomial_toSPFormula]

theorem productDepth_toSPCircuit_le {n : ℕ} (C : DepthFourCircuit K (Fin n)) :
    C.toSPCircuit.productDepth ≤ 2 :=
  (SPCircuit.productDepth_toCircuit_le _).trans C.productDepth_toSPFormula_le

end DepthFourCircuit

/-! ### : Heavy-child frontier quotients and decomposition identities -/

namespace HomogCircuit

variable {K : Type u} {n : ℕ}

/-- A gate `w` belongs to the `m`-frontier of `H` when `H.deg w > m` and `w` is a multiplication
gate whose two children both have degree at most `m`. -/
def isFrontier (H : HomogCircuit K n) (m : ℕ) (w : Fin H.size) : Prop :=
  m < H.deg w ∧ match H.gates w with
    | .mul w₁ w₂ =>
      H.deg ⟨w₁.1, w₁.2.trans w.2⟩ ≤ m ∧ H.deg ⟨w₂.1, w₂.2.trans w.2⟩ ≤ m
    | _ => False

instance instDecidableIsFrontier (H : HomogCircuit K n) (m : ℕ) (w : Fin H.size) :
    Decidable (H.isFrontier m w) := by
  unfold isFrontier
  cases H.gates w <;> dsimp only <;> infer_instance

/-- The finite set of all gates in the `m`-frontier of `H`. -/
def frontier (H : HomogCircuit K n) (m : ℕ) : Finset (Fin H.size) :=
  Finset.univ.filter fun w => H.isFrontier m w

/-- Heavy-child formal quotient `H.quot m u w`: linear coefficient of gate `w` when expanding
`H.gatePoly u` along heavy-child paths stopping at degree `≤ m` or at an `m`-frontier gate. -/
noncomputable def quot [CommSemiring K] (H : HomogCircuit K n) (m : ℕ)
    (u w : Fin H.size) : MvPolynomial (Fin n) K :=
  if H.deg u ≤ m then 0
  else if u = w then 1
  else match H.gates u with
    | .zero _ => 0
    | .var _ => 0
    | .add c₁ c₂ u₁ u₂ =>
      C c₁ * H.quot m ⟨u₁.1, u₁.2.trans u.2⟩ w + C c₂ * H.quot m ⟨u₂.1, u₂.2.trans u.2⟩ w
    | .mul u₁ u₂ =>
      let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
      let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
      if H.deg u₁' ≤ m ∧ H.deg u₂' ≤ m then 0
      else if H.deg u₂' ≤ H.deg u₁' then
        H.gatePoly u₂' * H.quot m u₁' w
      else
        H.gatePoly u₁' * H.quot m u₂' w
termination_by u.1

/-- `H.quot m u w` vanishes whenever `H.deg u < H.deg w`. -/
theorem quot_eq_zero_of_lt [CommSemiring K] (H : HomogCircuit K n) (m : ℕ)
    (u w : Fin H.size) (hlt : H.deg u < H.deg w) : H.quot m u w = 0 := by
  induction hu : u.1 using Nat.strongRecOn generalizing u with
  | ind k ih =>
    subst hu
    rw [quot]
    split_ifs with hm huw
    · rfl
    · subst huw; omega
    · have hgd := H.gate_deg u
      cases hg : H.gates u with
      | zero _ => rfl
      | var _ => rfl
      | add c₁ c₂ u₁ u₂ =>
        rw [hg] at hgd
        dsimp only
        have h1 := ih u₁.1 u₁.2 ⟨u₁.1, u₁.2.trans u.2⟩ (by omega) rfl
        have h2 := ih u₂.1 u₂.2 ⟨u₂.1, u₂.2.trans u.2⟩ (by omega) rfl
        rw [h1, h2, mul_zero, mul_zero, add_zero]
      | mul u₁ u₂ =>
        rw [hg] at hgd
        dsimp only
        let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
        let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
        change H.deg u = H.deg u₁' + H.deg u₂' at hgd
        split_ifs with hfr hcmp
        · rfl
        · have h1 := ih u₁.1 u₁.2 u₁' (by have := H.deg_pos u₂'; omega) rfl
          rw [h1, mul_zero]
        · have h2 := ih u₂.1 u₂.2 u₂' (by have := H.deg_pos u₁'; omega) rfl
          rw [h2, mul_zero]

/-- `H.quot m u w` vanishes whenever `H.deg w ≤ m`. -/
theorem quot_eq_zero_of_deg_le [CommSemiring K] (H : HomogCircuit K n) (m : ℕ)
    (u w : Fin H.size) (hw : H.deg w ≤ m) : H.quot m u w = 0 := by
  induction hu : u.1 using Nat.strongRecOn generalizing u with
  | ind k ih =>
    subst hu
    rw [quot]
    split_ifs with hm huw
    · rfl
    · subst huw; omega
    · cases H.gates u with
      | zero _ => rfl
      | var _ => rfl
      | add c₁ c₂ u₁ u₂ =>
        dsimp only
        rw [ih u₁.1 u₁.2 ⟨u₁.1, u₁.2.trans u.2⟩ rfl, ih u₂.1 u₂.2 ⟨u₂.1, u₂.2.trans u.2⟩ rfl,
          mul_zero, mul_zero, add_zero]
      | mul u₁ u₂ =>
        dsimp only
        split_ifs
        · rfl
        · rw [ih u₁.1 u₁.2 ⟨u₁.1, u₁.2.trans u.2⟩ rfl, mul_zero]
        · rw [ih u₂.1 u₂.2 ⟨u₂.1, u₂.2.trans u.2⟩ rfl, mul_zero]

/-- Diagonal value: `H.quot m u u = 1` whenever `m < H.deg u`. -/
theorem quot_self [CommSemiring K] (H : HomogCircuit K n) {m : ℕ} {u : Fin H.size}
    (hm : m < H.deg u) : H.quot m u u = 1 := by
  rw [quot, ite_eq_right (by omega), ite_eq_left rfl]

/-- Every heavy-child quotient `H.quot m u w` is homogeneous of degree `H.deg u - H.deg w`. -/
theorem isHomogeneous_quot [CommSemiring K] (H : HomogCircuit K n) (m : ℕ)
    (u w : Fin H.size) : (H.quot m u w).IsHomogeneous (H.deg u - H.deg w) := by
  induction hu : u.1 using Nat.strongRecOn generalizing u with
  | ind k ih =>
    subst hu
    rw [quot]
    split_ifs with hm huw
    · exact isHomogeneous_zero _ _ _
    · subst huw
      rw [Nat.sub_self]
      exact isHomogeneous_one (Fin n) K
    · have hgd := H.gate_deg u
      cases hg : H.gates u with
      | zero _ => exact isHomogeneous_zero _ _ _
      | var _ => exact isHomogeneous_zero _ _ _
      | add c₁ c₂ u₁ u₂ =>
        rw [hg] at hgd
        dsimp only
        have h1 := ih u₁.1 u₁.2 ⟨u₁.1, u₁.2.trans u.2⟩ rfl
        have h2 := ih u₂.1 u₂.2 ⟨u₂.1, u₂.2.trans u.2⟩ rfl
        rw [hgd.1] at h1
        rw [hgd.2] at h2
        exact (h1.C_mul c₁).add (h2.C_mul c₂)
      | mul u₁ u₂ =>
        rw [hg] at hgd
        dsimp only
        let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
        let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
        change H.deg u = H.deg u₁' + H.deg u₂' at hgd
        split_ifs with hfr hcmp
        · exact isHomogeneous_zero _ _ _
        · by_cases hlt : H.deg u₁' < H.deg w
          · rw [H.quot_eq_zero_of_lt m u₁' w hlt, mul_zero]
            exact isHomogeneous_zero _ _ _
          · have h1 := ih u₁.1 u₁.2 u₁' rfl
            have h2 := H.isHomogeneous_gatePoly u₂'
            have hmul := h2.mul h1
            rwa [show H.deg u₂' + (H.deg u₁' - H.deg w) = H.deg u - H.deg w by omega] at hmul
        · by_cases hlt : H.deg u₂' < H.deg w
          · rw [H.quot_eq_zero_of_lt m u₂' w hlt, mul_zero]
            exact isHomogeneous_zero _ _ _
          · have h2 := ih u₂.1 u₂.2 u₂' rfl
            have h1 := H.isHomogeneous_gatePoly u₁'
            have hmul := h1.mul h2
            rwa [show H.deg u₁' + (H.deg u₂' - H.deg w) = H.deg u - H.deg w by omega] at hmul

/-- **Gate frontier decomposition identity**: for every threshold `1 ≤ m` and gate `u` with
`m < H.deg u`, `H.gatePoly u` equals `∑ w ∈ H.frontier m, H.quot m u w * H.gatePoly w`. -/
theorem gatePoly_eq_sum_frontier [CommSemiring K] (H : HomogCircuit K n) {m : ℕ} (hm1 : 1 ≤ m)
    (u : Fin H.size) (hmu : m < H.deg u) :
    H.gatePoly u = ∑ w ∈ H.frontier m, H.quot m u w * H.gatePoly w := by
  induction hu : u.1 using Nat.strongRecOn generalizing u with
  | ind k ih =>
    subst hu
    have hgd := H.gate_deg u
    cases hg : H.gates u with
    | zero d =>
      rw [gatePoly, hg]
      symm
      refine Finset.sum_eq_zero fun w hw => ?_
      have hne : u ≠ w := by
        rintro rfl
        have hf := (Finset.mem_filter.mp hw).2
        simp [isFrontier, hg] at hf
      rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg, zero_mul]
    | var i =>
      rw [hg] at hgd
      omega
    | add c₁ c₂ u₁ u₂ =>
      rw [hg] at hgd
      let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
      let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
      change H.deg u₁' = H.deg u ∧ H.deg u₂' = H.deg u at hgd
      have hnot_fr : u ∉ H.frontier m := by
        intro hmem
        have hf := (Finset.mem_filter.mp hmem).2
        simp [isFrontier, hg] at hf
      have hterm : ∀ w ∈ H.frontier m,
          H.quot m u w * H.gatePoly w =
            C c₁ * (H.quot m u₁' w * H.gatePoly w) + C c₂ * (H.quot m u₂' w * H.gatePoly w) := by
        intro w hw
        have hne : u ≠ w := fun h => hnot_fr (h ▸ hw)
        rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← ih u₁.1 u₁.2 u₁' (by omega) rfl, ← ih u₂.1 u₂.2 u₂' (by omega) rfl]
      rw [gatePoly, hg]
    | mul u₁ u₂ =>
      rw [hg] at hgd
      let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
      let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
      change H.deg u = H.deg u₁' + H.deg u₂' at hgd
      by_cases hfr : H.deg u₁' ≤ m ∧ H.deg u₂' ≤ m
      · have hu_mem : u ∈ H.frontier m := by
          rw [frontier, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, hmu, ?_⟩
          rw [hg]
          exact hfr
        symm
        rw [Finset.sum_eq_single u]
        · rw [H.quot_self hmu, one_mul]
        · intro w _ hwu
          rw [quot, ite_eq_right (by omega), ite_eq_right hwu.symm, hg]
          dsimp only
          rw [ite_eq_left hfr, zero_mul]
        · intro hnot
          exact absurd hu_mem hnot
      · have hnot_fr : u ∉ H.frontier m := by
          intro hmem
          have hf := (Finset.mem_filter.mp hmem).2.2
          rw [hg] at hf
          exact hfr hf
        by_cases hcmp : H.deg u₂' ≤ H.deg u₁'
        · have hu₁_gt : m < H.deg u₁' := by omega
          have hterm : ∀ w ∈ H.frontier m,
              H.quot m u w * H.gatePoly w =
                H.gatePoly u₂' * (H.quot m u₁' w * H.gatePoly w) := by
            intro w hw
            have hne : u ≠ w := fun h => hnot_fr (h ▸ hw)
            rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg]
            dsimp only
            rw [ite_eq_right hfr, ite_eq_left hcmp, mul_assoc]
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
            ← ih u₁.1 u₁.2 u₁' hu₁_gt rfl, gatePoly, hg, mul_comm]
        · have hu₂_gt : m < H.deg u₂' := by omega
          have hterm : ∀ w ∈ H.frontier m,
              H.quot m u w * H.gatePoly w =
                H.gatePoly u₁' * (H.quot m u₂' w * H.gatePoly w) := by
            intro w hw
            have hne : u ≠ w := fun h => hnot_fr (h ▸ hw)
            rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg]
            dsimp only
            rw [ite_eq_right hfr, ite_eq_right hcmp, mul_assoc]
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
            ← ih u₂.1 u₂.2 u₂' hu₂_gt rfl, gatePoly, hg]

/-- **Quotient frontier composition identity**: for `1 ≤ m ≤ t` and gates `u, w` with
`H.deg w ≤ t < H.deg u`,
`H.quot m u w = ∑ v ∈ H.frontier t, H.quot t u v * H.quot m v w`. -/
theorem quot_eq_sum_frontier [CommSemiring K] (H : HomogCircuit K n) {m t : ℕ}
    (hm1 : 1 ≤ m) (hmt : m ≤ t) (u w : Fin H.size) (hwt : H.deg w ≤ t) (htu : t < H.deg u) :
    H.quot m u w = ∑ v ∈ H.frontier t, H.quot t u v * H.quot m v w := by
  induction hu : u.1 using Nat.strongRecOn generalizing u with
  | ind k ih =>
    subst hu
    have hgd := H.gate_deg u
    have hmu : m < H.deg u := lt_of_le_of_lt hmt htu
    have huw : u ≠ w := by
      rintro rfl
      omega
    cases hg : H.gates u with
    | zero d =>
      rw [quot, ite_eq_right (by omega), ite_eq_right huw, hg]
      symm
      refine Finset.sum_eq_zero fun v hv => ?_
      have hne : u ≠ v := by
        rintro rfl
        have hf := (Finset.mem_filter.mp hv).2
        simp [isFrontier, hg] at hf
      rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg, zero_mul]
    | var i =>
      rw [hg] at hgd
      omega
    | add c₁ c₂ u₁ u₂ =>
      rw [hg] at hgd
      let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
      let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
      change H.deg u₁' = H.deg u ∧ H.deg u₂' = H.deg u at hgd
      have hnot_fr : u ∉ H.frontier t := by
        intro hmem
        have hf := (Finset.mem_filter.mp hmem).2
        simp [isFrontier, hg] at hf
      have hterm : ∀ v ∈ H.frontier t,
          H.quot t u v * H.quot m v w =
            C c₁ * (H.quot t u₁' v * H.quot m v w) + C c₂ * (H.quot t u₂' v * H.quot m v w) := by
        intro v hv
        have hne : u ≠ v := fun h => hnot_fr (h ▸ hv)
        rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← ih u₁.1 u₁.2 u₁' (by omega) rfl, ← ih u₂.1 u₂.2 u₂' (by omega) rfl]
      rw [quot, ite_eq_right (by omega), ite_eq_right huw, hg]
    | mul u₁ u₂ =>
      rw [hg] at hgd
      let u₁' : Fin H.size := ⟨u₁.1, u₁.2.trans u.2⟩
      let u₂' : Fin H.size := ⟨u₂.1, u₂.2.trans u.2⟩
      change H.deg u = H.deg u₁' + H.deg u₂' at hgd
      by_cases hfrt : H.deg u₁' ≤ t ∧ H.deg u₂' ≤ t
      · have hu_mem : u ∈ H.frontier t := by
          rw [frontier, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, htu, ?_⟩
          rw [hg]
          exact hfrt
        symm
        rw [Finset.sum_eq_single u]
        · rw [H.quot_self htu, one_mul]
        · intro v _ hvu
          rw [quot, ite_eq_right (by omega), ite_eq_right hvu.symm, hg]
          dsimp only
          rw [ite_eq_left hfrt, zero_mul]
        · intro hnot
          exact absurd hu_mem hnot
      · have hnot_frt : u ∉ H.frontier t := by
          intro hmem
          have hf := (Finset.mem_filter.mp hmem).2.2
          rw [hg] at hf
          exact hfrt hf
        have hnot_frm : ¬(H.deg u₁' ≤ m ∧ H.deg u₂' ≤ m) := fun h =>
          hfrt ⟨h.1.trans hmt, h.2.trans hmt⟩
        by_cases hcmp : H.deg u₂' ≤ H.deg u₁'
        · have hu₁_gt : t < H.deg u₁' := by omega
          have hterm : ∀ v ∈ H.frontier t,
              H.quot t u v * H.quot m v w =
                H.gatePoly u₂' * (H.quot t u₁' v * H.quot m v w) := by
            intro v hv
            have hne : u ≠ v := fun h => hnot_frt (h ▸ hv)
            rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg]
            dsimp only
            rw [ite_eq_right hfrt, ite_eq_left hcmp, mul_assoc]
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← ih u₁.1 u₁.2 u₁' hu₁_gt rfl]
          rw [quot, ite_eq_right (by omega), ite_eq_right huw, hg]
          dsimp only
          rw [ite_eq_right hnot_frm, ite_eq_left hcmp]
        · have hu₂_gt : t < H.deg u₂' := by omega
          have hterm : ∀ v ∈ H.frontier t,
              H.quot t u v * H.quot m v w =
                H.gatePoly u₁' * (H.quot t u₂' v * H.quot m v w) := by
            intro v hv
            have hne : u ≠ v := fun h => hnot_frt (h ▸ hv)
            rw [quot, ite_eq_right (by omega), ite_eq_right hne, hg]
            dsimp only
            rw [ite_eq_right hfrt, ite_eq_right hcmp, mul_assoc]
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← ih u₂.1 u₂.2 u₂' hu₂_gt rfl]
          rw [quot, ite_eq_right (by omega), ite_eq_right huw, hg]
          dsimp only
          rw [ite_eq_right hnot_frm, ite_eq_right hcmp]

end HomogCircuit

/-! ### : Algebraic tree-balancing and logarithmic-depth reduction (VSBR) -/

/-- A program extension preserving values, depths, and weighted depths of all earlier wires. -/
private structure ProgExt (σ : Signature) {U : Type*} (I : Interpretation σ U)
    (cost : σ.Op → ℕ) {n g₁ g₂ : ℕ} (p₁ : Program σ n g₁) (p₂ : Program σ n g₂) where
  lift : Wire n g₁ → Wire n g₂
  trace_eq : ∀ x w, p₂.trace I x (lift w) = p₁.trace I x w
  depth_eq : ∀ w, p₂.wireDepths (lift w) = p₁.wireDepths w
  costDepth_eq : ∀ w, p₂.wireDepthsWith cost (lift w) = p₁.wireDepthsWith cost w

private def ProgExt.refl {σ : Signature} {U : Type*} {I : Interpretation σ U} {cost : σ.Op → ℕ}
    {n g : ℕ} (p : Program σ n g) : ProgExt σ I cost p p where
  lift := id
  trace_eq _ _ := rfl
  depth_eq _ := rfl
  costDepth_eq _ := rfl

private def ProgExt.trans {σ : Signature} {U : Type*} {I : Interpretation σ U} {cost : σ.Op → ℕ}
    {n g₁ g₂ g₃ : ℕ} {p₁ : Program σ n g₁} {p₂ : Program σ n g₂} {p₃ : Program σ n g₃}
    (e₁ : ProgExt σ I cost p₁ p₂) (e₂ : ProgExt σ I cost p₂ p₃) :
    ProgExt σ I cost p₁ p₃ where
  lift := e₂.lift ∘ e₁.lift
  trace_eq x w := (e₂.trace_eq x (e₁.lift w)).trans (e₁.trace_eq x w)
  depth_eq w := (e₂.depth_eq (e₁.lift w)).trans (e₁.depth_eq w)
  costDepth_eq w := (e₂.costDepth_eq (e₁.lift w)).trans (e₁.costDepth_eq w)

private def ProgExt.gate {σ : Signature} {U : Type*} (I : Interpretation σ U) (cost : σ.Op → ℕ)
    {n g : ℕ} (p : Program σ n g) (line : Line σ n g) :
    ProgExt σ I cost p (p.gate line) where
  lift := Wire.castSucc
  trace_eq x w := p.trace_gate_castSucc line I x w
  depth_eq w := p.wireDepths_gate_castSucc line w
  costDepth_eq w := p.wireDepthsWith_gate_castSucc cost line w

/-- Depth of a line with `cost`, bounded when every argument wire has weighted depth `≤ D`. -/
private theorem line_depthWith_le {σ : Signature} {n g : ℕ} (cost : σ.Op → ℕ)
    (line : Line σ n g) (depths : Wire n g → ℕ) {D : ℕ}
    (hD : ∀ a, depths (line.wires a) ≤ D) :
    line.depthWith cost depths ≤ D + cost line.op := by
  rw [Line.depthWith_eq_sup]
  exact Nat.add_le_add_right (Finset.sup_le fun a _ => hD a) _

/-- Unit-cost depth of a line bounded when every argument wire has depth `≤ D`. -/
private theorem line_depth_le {σ : Signature} {n g : ℕ} (line : Line σ n g)
    (depths : Wire n g → ℕ) {D : ℕ} (hD : ∀ a, depths (line.wires a) ≤ D) :
    line.depth depths ≤ D + 1 :=
  (line.depth_le_add_one_iff depths).2 hD

/-- Append a list of triple-products `(w₁ * w₂) * w₃` and a single unbounded sum gate over them to
an `SPCircuit` program, preserving `FanInAtMost M`. -/
private theorem spPushSumOfTriples {K : Type u} [CommSemiring K] {n g M D₁ D₂ P₁ P₂ : ℕ}
    (p : Program (sigmaPiSignature K) n g) (hpM : p.FanInAtMost M) (hM2 : 2 ≤ M)
    (L : List (Wire n g × Wire n g × Wire n g)) (hLM : L.length ≤ M)
    (hD₁ : ∀ t ∈ L, p.wireDepths t.1 ≤ D₁ ∧ p.wireDepths t.2.1 ≤ D₁)
    (hD₂ : ∀ t ∈ L, p.wireDepths t.2.2 ≤ D₂)
    (hP₁ : ∀ t ∈ L,
      p.wireDepthsWith SigmaPiOp.mulCost t.1 ≤ P₁ ∧
      p.wireDepthsWith SigmaPiOp.mulCost t.2.1 ≤ P₁)
    (hP₂ : ∀ t ∈ L, p.wireDepthsWith SigmaPiOp.mulCost t.2.2 ≤ P₂) :
    let I := sigmaPiInterpretationWith K (C : K → MvPolynomial (Fin n) K)
    ∃ (g' : ℕ) (p' : Program (sigmaPiSignature K) n g') (out : Wire n g')
      (_ext : ProgExt (sigmaPiSignature K) I SigmaPiOp.mulCost p p'),
      g' ≤ g + 2 * L.length + 1 ∧
      p'.FanInAtMost M ∧
      p'.trace I X out =
        (L.map fun t => (p.trace I X t.1 * p.trace I X t.2.1) * p.trace I X t.2.2).sum ∧
      p'.wireDepths out ≤ max (D₁ + 1) D₂ + 2 ∧
      p'.wireDepthsWith SigmaPiOp.mulCost out ≤ max (P₁ + 1) P₂ + 1 := by
  intro I
  -- First push all `L.length` triple-product wires (`2 * L.length` binary `.mul 2` gates).
  have hprods : ∀ (xs : List (Wire n g × Wire n g × Wire n g)),
      (∀ t ∈ xs, p.wireDepths t.1 ≤ D₁ ∧ p.wireDepths t.2.1 ≤ D₁) →
      (∀ t ∈ xs, p.wireDepths t.2.2 ≤ D₂) →
      (∀ t ∈ xs,
        p.wireDepthsWith SigmaPiOp.mulCost t.1 ≤ P₁ ∧
        p.wireDepthsWith SigmaPiOp.mulCost t.2.1 ≤ P₁) →
      (∀ t ∈ xs, p.wireDepthsWith SigmaPiOp.mulCost t.2.2 ≤ P₂) →
      ∃ (g₁ : ℕ) (p₁ : Program (sigmaPiSignature K) n g₁) (ws : List (Wire n g₁))
        (ext : ProgExt (sigmaPiSignature K) I SigmaPiOp.mulCost p p₁),
        g₁ = g + 2 * xs.length ∧
        p₁.FanInAtMost M ∧
        ws.length = xs.length ∧
        ws.map (p₁.trace I X) =
          xs.map (fun t => (p.trace I X t.1 * p.trace I X t.2.1) * p.trace I X t.2.2) ∧
        (∀ w ∈ ws, p₁.wireDepths w ≤ max (D₁ + 1) D₂ + 1) ∧
        (∀ w ∈ ws, p₁.wireDepthsWith SigmaPiOp.mulCost w ≤ max (P₁ + 1) P₂ + 1) := by
    intro xs
    induction xs with
    | nil =>
      intro _ _ _ _
      exact ⟨g, p, [], ProgExt.refl p, by simp, hpM, rfl, rfl,
        fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil)⟩
    | cons t tl ih =>
      intro hd₁ hd₂ hp₁ hp₂
      obtain ⟨g₁, p₁, ws, ext₁, hg₁, hp₁M, hlen, hmap, hwd, hwp⟩ :=
        ih (fun x hx => hd₁ x (List.mem_cons_of_mem _ hx))
          (fun x hx => hd₂ x (List.mem_cons_of_mem _ hx))
          (fun x hx => hp₁ x (List.mem_cons_of_mem _ hx))
          (fun x hx => hp₂ x (List.mem_cons_of_mem _ hx))
      let line1 : Line (sigmaPiSignature K) n g₁ :=
        ⟨.mul 2, ![ext₁.lift t.1, ext₁.lift t.2.1]⟩
      let p2 : Program (sigmaPiSignature K) n (g₁ + 1) := p₁.gate line1
      let line2 : Line (sigmaPiSignature K) n (g₁ + 1) :=
        ⟨.mul 2, ![.gate (Fin.last g₁), (ext₁.lift t.2.2).castSucc]⟩
      let p3 : Program (sigmaPiSignature K) n (g₁ + 2) := p2.gate line2
      let ext2 : ProgExt (sigmaPiSignature K) I SigmaPiOp.mulCost p₁ p3 :=
        (ProgExt.gate I SigmaPiOp.mulCost p₁ line1).trans
          (ProgExt.gate I SigmaPiOp.mulCost p2 line2)
      let w_new : Wire n (g₁ + 2) := .gate (Fin.last (g₁ + 1))
      have hfan3 : p3.FanInAtMost M := ⟨⟨hp₁M, hM2⟩, hM2⟩
      have ht1_tr : p2.trace I X (.gate (Fin.last g₁)) = p.trace I X t.1 * p.trace I X t.2.1 := by
        rw [Program.trace_gate_last]
        simp only [I, line1, sigmaPiInterpretationWith_mul, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ext₁.trace_eq]
      have ht2_tr : p3.trace I X w_new =
          (p.trace I X t.1 * p.trace I X t.2.1) * p.trace I X t.2.2 := by
        rw [Program.trace_gate_last]
        simp only [I, line2, sigmaPiInterpretationWith_mul, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          ht1_tr, p2, Program.trace_gate_castSucc, ext₁.trace_eq]
      have hd1_t := hd₁ t List.mem_cons_self
      have hd2_t := hd₂ t List.mem_cons_self
      have hp1_t := hp₁ t List.mem_cons_self
      have hp2_t := hp₂ t List.mem_cons_self
      have hdep1 : p2.wireDepths (.gate (Fin.last g₁)) ≤ D₁ + 1 := by
        rw [Program.wireDepths_gateWire, Program.depths_gate_last]
        refine line_depth_le line1 p₁.wireDepths fun a => ?_
        fin_cases a
        · simpa [line1, ext₁.depth_eq] using hd1_t.1
        · simpa [line1, ext₁.depth_eq] using hd1_t.2
      have hdep2 : p3.wireDepths w_new ≤ max (D₁ + 1) D₂ + 1 := by
        rw [Program.wireDepths_gateWire, Program.depths_gate_last]
        refine line_depth_le line2 p2.wireDepths fun a => ?_
        fin_cases a
        · exact hdep1.trans (le_max_left _ _)
        · simpa [line2, p2, Program.wireDepths_gate_castSucc, ext₁.depth_eq] using
            hd2_t.trans (le_max_right _ _)
      have hpd1 : p2.wireDepthsWith SigmaPiOp.mulCost (.gate (Fin.last g₁)) ≤ P₁ + 1 := by
        rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
        refine (line_depthWith_le SigmaPiOp.mulCost line1 _ fun a => ?_).trans_eq rfl
        fin_cases a
        · simpa [line1, ext₁.costDepth_eq] using hp1_t.1
        · simpa [line1, ext₁.costDepth_eq] using hp1_t.2
      have hpd2 : p3.wireDepthsWith SigmaPiOp.mulCost w_new ≤ max (P₁ + 1) P₂ + 1 := by
        rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
        refine (line_depthWith_le SigmaPiOp.mulCost line2 _ fun a => ?_).trans_eq rfl
        fin_cases a
        · exact hpd1.trans (le_max_left _ _)
        · simpa [line2, p2, Program.wireDepthsWith_gate_castSucc, ext₁.costDepth_eq] using
            hp2_t.trans (le_max_right _ _)
      refine ⟨g₁ + 2, p3, w_new :: ws.map ext2.lift, ext₁.trans ext2,
        by simp [hg₁]; omega, hfan3, by simp [hlen], ?_, ?_, ?_⟩
      · simp only [List.map_cons, ht2_tr, List.map_map]
        congr 1
        have hcomp : (p3.trace I X ∘ ext2.lift) = p₁.trace I X := funext fun w => ext2.trace_eq X w
        rw [hcomp, hmap]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact hdep2
        · rcases List.mem_map.mp hmem with ⟨u, hu, rfl⟩
          rw [ext2.depth_eq]
          exact hwd u hu
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact hpd2
        · rcases List.mem_map.mp hmem with ⟨u, hu, rfl⟩
          rw [ext2.costDepth_eq]
          exact hwp u hu
  obtain ⟨g₁, p₁, ws, ext₁, hg₁, hp₁M, hlen, hmap, hwd, hwp⟩ := hprods L hD₁ hD₂ hP₁ hP₂
  let addLine : Line (sigmaPiSignature K) n g₁ :=
    ⟨.add ws.length (fun _ => 1), fun j => ws.get j⟩
  let p₂ : Program (sigmaPiSignature K) n (g₁ + 1) := p₁.gate addLine
  let out : Wire n (g₁ + 1) := .gate (Fin.last g₁)
  refine ⟨g₁ + 1, p₂, out, ext₁.trans (ProgExt.gate I SigmaPiOp.mulCost p₁ addLine),
    by omega, ⟨hp₁M, by change ws.length ≤ M; omega⟩, ?_, ?_, ?_⟩
  · rw [Program.trace_gate_last]
    simp only [I, addLine, sigmaPiInterpretationWith_add, map_one, one_mul]
    rw [← List.sum_ofFn]
    have hofFn : (List.ofFn fun j : Fin ws.length => p₁.trace I X (ws.get j)) =
        ws.map (p₁.trace I X) := by
      conv_rhs => rw [← List.ofFn_get ws]
      rw [List.map_ofFn]
      rfl
    rw [hofFn, hmap]
  · rw [Program.wireDepths_gateWire, Program.depths_gate_last]
    exact (line_depth_le addLine p₁.wireDepths fun j => hwd _ (List.get_mem ws j)).trans
      (by omega)
  · rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
    have h := line_depthWith_le SigmaPiOp.mulCost addLine
      (p₁.wireDepthsWith SigmaPiOp.mulCost) (fun j => hwp _ (List.get_mem ws j))
    simpa [addLine] using h

/-- **VSBR logarithmic-depth reduction (unbounded-sum, fan-in-two-product `SPCircuit`)**:
for any `H : HomogCircuit K n` and degree bound `d`, there exists an `SPCircuit` program
simultaneously computing every gate `H.gatePoly u` (`H.deg u ≤ d`) with:
* fan-in at most `max 2 (max n H.size)`,
* size at most `(H.size + (d + 1) * H.size ^ 2) * (1 + Nat.clog 2 d * (2 * H.size + 1))`,
* depth at most `5 * Nat.clog 2 d + 1`, and
* product-depth at most `3 * Nat.clog 2 d`. -/
theorem HomogCircuit.exists_spProgram_log_depth {K : Type u} [CommSemiring K] {n d : ℕ}
    (H : HomogCircuit K n) :
    let I := sigmaPiInterpretationWith K (C : K → MvPolynomial (Fin n) K)
    let R := Nat.clog 2 d
    let M := max 2 (max n H.size)
    ∃ (g : ℕ) (p : Program (sigmaPiSignature K) n g) (gateWire : Fin H.size → Wire n g),
      g ≤ (H.size + (d + 1) * H.size ^ 2) * (1 + R * (2 * H.size + 1)) ∧
      p.FanInAtMost M ∧
      ∀ u : Fin H.size, H.deg u ≤ d →
        p.trace I X (gateWire u) = H.gatePoly u ∧
        p.wireDepths (gateWire u) ≤ 5 * R + 1 ∧
        p.wireDepthsWith SigmaPiOp.mulCost (gateWire u) ≤ 3 * R := by
  intro I R M
  have hM2 : 2 ≤ M := le_max_left 2 _
  have hMn : n ≤ M := (le_max_left n H.size).trans (le_max_right 2 _)
  have hMs : H.size ≤ M := (le_max_right n H.size).trans (le_max_right 2 _)
  -- Helper: push a finite `Fin k`-indexed family of degree-`≤ 1` homogeneous polynomials
  -- (`k` gates, depth `≤ 1`, product-depth `0`).
  have hpushDegLeOne : ∀ {g₀ : ℕ} (p₀ : Program (sigmaPiSignature K) n g₀), p₀.FanInAtMost M →
      ∀ (k : ℕ) (F : Fin k → MvPolynomial (Fin n) K) (isDeg : Fin k → ℕ),
      (∀ i, isDeg i = 0 → (F i).IsHomogeneous 0) →
      (∀ i, isDeg i = 1 → (F i).IsHomogeneous 1) →
      ∃ (g₁ : ℕ) (p₁ : Program (sigmaPiSignature K) n g₁) (ws : Fin k → Wire n g₁)
        (ext : ProgExt (sigmaPiSignature K) I SigmaPiOp.mulCost p₀ p₁),
        g₁ = g₀ + k ∧
        p₁.FanInAtMost M ∧
        (∀ i, p₁.wireDepths (ws i) ≤ 1) ∧
        (∀ i, p₁.wireDepthsWith SigmaPiOp.mulCost (ws i) = 0) ∧
        (∀ i, isDeg i ≤ 1 → p₁.trace I X (ws i) = F i) := by
    intro g₀ p₀ hp₀ k
    induction k with
    | zero =>
      intro _ _ _ _
      exact ⟨g₀, p₀, Fin.elim0, ProgExt.refl p₀, rfl, hp₀,
        fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro F isDeg h0 h1
      obtain ⟨g₁, p₁, ws, ext₁, hg₁, hp₁M, hwd, hwp, htr⟩ :=
        ih (fun i => F i.castSucc) (fun i => isDeg i.castSucc)
          (fun i => h0 i.castSucc) (fun i => h1 i.castSucc)
      let iL : Fin (k + 1) := Fin.last k
      let line : Line (sigmaPiSignature K) n g₁ :=
        if isDeg iL = 0 then ⟨.const ((F iL).coeff 0), Fin.elim0⟩
        else if isDeg iL = 1 then
          ⟨.add n (fun j => (F iL).coeff (Finsupp.single j 1)), Wire.input⟩
        else ⟨.const 0, Fin.elim0⟩
      let p₂ : Program (sigmaPiSignature K) n (g₁ + 1) := p₁.gate line
      have hfan₂ : p₂.FanInAtMost M := by
        refine ⟨hp₁M, ?_⟩
        dsimp only [line]
        split_ifs <;> simp [hMn]
      have hwd_last : p₂.wireDepths (.gate (Fin.last g₁)) ≤ 1 := by
        rw [Program.wireDepths_gateWire, Program.depths_gate_last]
        dsimp only [line]
        by_cases hiz : isDeg iL = 0
        · rw [ite_eq_left hiz]
          exact line_depth_le _ p₁.wireDepths (D := 0) fun a => a.elim0
        · rw [ite_eq_right hiz]
          by_cases hi1 : isDeg iL = 1
          · rw [ite_eq_left hi1]
            exact line_depth_le _ p₁.wireDepths (D := 0) fun _ => by simp
          · rw [ite_eq_right hi1]
            exact line_depth_le _ p₁.wireDepths (D := 0) fun a => a.elim0
      have hwp_last : p₂.wireDepthsWith SigmaPiOp.mulCost (.gate (Fin.last g₁)) = 0 := by
        rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
        apply Nat.eq_zero_of_le_zero
        dsimp only [line]
        by_cases hiz : isDeg iL = 0
        · rw [ite_eq_left hiz]
          exact line_depthWith_le (σ := sigmaPiSignature K) SigmaPiOp.mulCost
            ⟨.const ((F iL).coeff 0), Fin.elim0⟩ _ (D := 0) fun a => a.elim0
        · rw [ite_eq_right hiz]
          by_cases hi1 : isDeg iL = 1
          · rw [ite_eq_left hi1]
            exact line_depthWith_le (σ := sigmaPiSignature K) SigmaPiOp.mulCost
              ⟨.add n (fun j => (F iL).coeff (Finsupp.single j 1)), Wire.input⟩ _ (D := 0)
              fun _ => by simp
          · rw [ite_eq_right hi1]
            exact line_depthWith_le (σ := sigmaPiSignature K) SigmaPiOp.mulCost
              ⟨.const 0, Fin.elim0⟩ _ (D := 0) fun a => a.elim0
      have htr_last : isDeg iL ≤ 1 → p₂.trace I X (.gate (Fin.last g₁)) = F iL := by
        intro hle
        rw [Program.trace_gate_last]
        dsimp only [line]
        by_cases hiz : isDeg iL = 0
        · rw [ite_eq_left hiz]
          exact (eq_C_coeff_zero_of_isHomogeneous_zero (h0 iL hiz)).symm
        · have hi1 : isDeg iL = 1 := by omega
          rw [ite_eq_right hiz, ite_eq_left hi1]
          exact (eq_sum_C_mul_X_of_isHomogeneous_one (h1 iL hi1)).symm
      refine ⟨g₁ + 1, p₂, Fin.lastCases (.gate (Fin.last g₁)) (fun i => (ws i).castSucc),
        ext₁.trans (ProgExt.gate I SigmaPiOp.mulCost p₁ line),
        by omega, hfan₂, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hwd_last
        | cast j => simpa [p₂, Program.wireDepths_gate_castSucc] using hwd j
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hwp_last
        | cast j => simpa [p₂, Program.wireDepthsWith_gate_castSucc] using hwp j
      · intro i hi
        induction i using Fin.lastCases with
        | last => simpa using htr_last hi
        | cast j => simpa [p₂, Program.trace_gate_castSucc] using htr j hi
  -- Helper: batch-update a `Fin k`-indexed family of target polynomials by triple-product lists.
  have hbatchTriples : ∀ {g₀ : ℕ} (p₀ : Program (sigmaPiSignature K) n g₀), p₀.FanInAtMost M →
      ∀ (k D₁ D₂ P₁ P₂ : ℕ)
        (oldW : Fin k → Wire n g₀)
        (upd : Fin k → Prop) [DecidablePred upd]
        (triples : Fin k → List (Wire n g₀ × Wire n g₀ × Wire n g₀)),
      (∀ i, upd i → (triples i).length ≤ H.size) →
      (∀ i, upd i → ∀ t ∈ triples i, p₀.wireDepths t.1 ≤ D₁ ∧ p₀.wireDepths t.2.1 ≤ D₁) →
      (∀ i, upd i → ∀ t ∈ triples i, p₀.wireDepths t.2.2 ≤ D₂) →
      (∀ i, upd i → ∀ t ∈ triples i,
        p₀.wireDepthsWith SigmaPiOp.mulCost t.1 ≤ P₁ ∧
        p₀.wireDepthsWith SigmaPiOp.mulCost t.2.1 ≤ P₁) →
      (∀ i, upd i → ∀ t ∈ triples i, p₀.wireDepthsWith SigmaPiOp.mulCost t.2.2 ≤ P₂) →
      ∃ (g₁ : ℕ) (p₁ : Program (sigmaPiSignature K) n g₁) (newW : Fin k → Wire n g₁)
        (ext : ProgExt (sigmaPiSignature K) I SigmaPiOp.mulCost p₀ p₁),
        g₁ ≤ g₀ + k * (2 * H.size + 1) ∧
        p₁.FanInAtMost M ∧
        (∀ i, ¬upd i → newW i = ext.lift (oldW i)) ∧
        (∀ i, upd i →
          p₁.trace I X (newW i) =
            ((triples i).map fun t =>
              (p₀.trace I X t.1 * p₀.trace I X t.2.1) * p₀.trace I X t.2.2).sum ∧
          p₁.wireDepths (newW i) ≤ max (D₁ + 1) D₂ + 2 ∧
          p₁.wireDepthsWith SigmaPiOp.mulCost (newW i) ≤ max (P₁ + 1) P₂ + 1) := by
    intro g₀ p₀ hp₀ k D₁ D₂ P₁ P₂
    induction k with
    | zero =>
      intro _ _ _ _ _ _ _ _ _
      exact ⟨g₀, p₀, Fin.elim0, ProgExt.refl p₀, by simp, hp₀,
        fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro oldW upd _ triples hlen hd₁ hd₂ hp₁ hp₂
      obtain ⟨g₁, p₁, newW, ext₁, hg₁, hp₁M, hkeep, hupd⟩ :=
        ih (fun i => oldW i.castSucc) (fun i => upd i.castSucc) (fun i => triples i.castSucc)
          (fun i => hlen i.castSucc) (fun i => hd₁ i.castSucc) (fun i => hd₂ i.castSucc)
          (fun i => hp₁ i.castSucc) (fun i => hp₂ i.castSucc)
      let iL : Fin (k + 1) := Fin.last k
      by_cases hu : upd iL
      · let L' := (triples iL).map fun t => (ext₁.lift t.1, ext₁.lift t.2.1, ext₁.lift t.2.2)
        have hL'_len : L'.length ≤ M := by
          rw [List.length_map]
          exact (hlen iL hu).trans hMs
        obtain ⟨g₂, p₂, outL, ext₂, hg₂, hp₂M, hout_tr, hout_d, hout_p⟩ :=
          spPushSumOfTriples p₁ hp₁M hM2 L' hL'_len
            (fun t ht => by
              rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
              simpa [ext₁.depth_eq] using hd₁ iL hu s hs)
            (fun t ht => by
              rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
              simpa [ext₁.depth_eq] using hd₂ iL hu s hs)
            (fun t ht => by
              rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
              simpa [ext₁.costDepth_eq] using hp₁ iL hu s hs)
            (fun t ht => by
              rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
              simpa [ext₁.costDepth_eq] using hp₂ iL hu s hs)
        refine ⟨g₂, p₂, Fin.lastCases outL (fun i => ext₂.lift (newW i)), ext₁.trans ext₂,
          ?_, hp₂M, ?_, ?_⟩
        · have hLlen : L'.length ≤ H.size := by rw [List.length_map]; exact hlen iL hu
          calc
            g₂ ≤ g₁ + 2 * L'.length + 1 := hg₂
            _ ≤ (g₀ + k * (2 * H.size + 1)) + (2 * H.size + 1) := by omega
            _ = g₀ + (k + 1) * (2 * H.size + 1) := by ring
        · intro i hnot
          induction i using Fin.lastCases with
          | last => exact absurd hu hnot
          | cast j => simp [hkeep j hnot, ProgExt.trans]
        · intro i hi
          induction i using Fin.lastCases with
          | last =>
            dsimp only
            rw [Fin.lastCases_last]
            refine ⟨?_, hout_d, hout_p⟩
            rw [hout_tr]
            simp only [L', List.map_map]
            congr 1
            refine List.map_congr_left fun t _ => ?_
            change p₁.trace I X (ext₁.lift t.1) * p₁.trace I X (ext₁.lift t.2.1) *
              p₁.trace I X (ext₁.lift t.2.2) =
              p₀.trace I X t.1 * p₀.trace I X t.2.1 * p₀.trace I X t.2.2
            simp only [ext₁.trace_eq]
          | cast j =>
            rcases hupd j hi with ⟨htr_j, hd_j, hp_j⟩
            dsimp only
            rw [Fin.lastCases_castSucc, ext₂.depth_eq, ext₂.costDepth_eq]
            exact ⟨(ext₂.trace_eq X (newW j)).trans htr_j, hd_j, hp_j⟩
      · refine ⟨g₁, p₁, Fin.lastCases (ext₁.lift (oldW iL)) newW, ext₁, ?_, hp₁M, ?_, ?_⟩
        · calc
            g₁ ≤ g₀ + k * (2 * H.size + 1) := hg₁
            _ ≤ g₀ + (k * (2 * H.size + 1) + (2 * H.size + 1)) := by omega
            _ = g₀ + (k + 1) * (2 * H.size + 1) := by ring
        · intro i hnot
          induction i using Fin.lastCases with
          | last => simp [iL]
          | cast j => simp [hkeep j hnot]
        · intro i hi
          induction i using Fin.lastCases with
          | last => exact absurd hi hu
          | cast j => simpa using hupd j hi
  -- Main round induction: after round `r`, compute all `gatePoly u` (`deg u ≤ min d (2^r)`) and
  -- all `quot m u w` (`1 ≤ m ≤ d`, `deg u ≤ d`, `deg u - deg w ≤ 2^r`).
  let QIdx := Fin (d + 1) × Fin H.size × Fin H.size
  let qEquiv : QIdx ≃ Fin ((d + 1) * H.size ^ 2) :=
    (Equiv.prodCongr (Equiv.refl (Fin (d + 1))) finProdFinEquiv).trans
      (finProdFinEquiv.trans (finCongr (by ring)))
  have hrounds : ∀ r : ℕ,
      ∃ (g : ℕ) (p : Program (sigmaPiSignature K) n g)
        (gateW : Fin H.size → Wire n g)
        (quotW : Fin (d + 1) → Fin H.size → Fin H.size → Wire n g),
        g ≤ (H.size + (d + 1) * H.size ^ 2) * (1 + r * (2 * H.size + 1)) ∧
        p.FanInAtMost M ∧
        (∀ u : Fin H.size,
          p.wireDepths (gateW u) ≤ 5 * r + 1 ∧
          p.wireDepthsWith SigmaPiOp.mulCost (gateW u) ≤ 3 * r ∧
          (H.deg u ≤ d → H.deg u ≤ 2 ^ r → p.trace I X (gateW u) = H.gatePoly u)) ∧
        (∀ (m : Fin (d + 1)) (u w : Fin H.size),
          p.wireDepths (quotW m u w) ≤ 5 * r + 1 ∧
          p.wireDepthsWith SigmaPiOp.mulCost (quotW m u w) ≤ 3 * r ∧
          (1 ≤ m.1 → H.deg u ≤ d → H.deg u - H.deg w ≤ 2 ^ r →
            p.trace I X (quotW m u w) = H.quot m.1 u w)) := by
    intro r
    induction r with
    | zero =>
      -- Round 0: emit all degree-`1` gates and degree-`≤ 1` quotients in one layer (depth `≤ 1`).
      obtain ⟨g1, p1, gateW, _, hg1, hp1M, hgd1, hgp1, hgt1⟩ :=
        hpushDegLeOne Program.empty trivial H.size H.gatePoly H.deg
          (fun u h0 => by have := H.deg_pos u; omega)
          (fun u h1 => h1 ▸ H.isHomogeneous_gatePoly u)
      let Fq : Fin ((d + 1) * H.size ^ 2) → MvPolynomial (Fin n) K := fun idx =>
        let t := qEquiv.symm idx
        H.quot t.1.1 t.2.1 t.2.2
      let Dq : Fin ((d + 1) * H.size ^ 2) → ℕ := fun idx =>
        let t := qEquiv.symm idx
        H.deg t.2.1 - H.deg t.2.2
      obtain ⟨g2, p2, quotFlat, ext2, hg2, hp2M, hqd2, hqp2, hqt2⟩ :=
        hpushDegLeOne p1 hp1M ((d + 1) * H.size ^ 2) Fq Dq
          (fun idx h0 => h0 ▸ H.isHomogeneous_quot _ _ _)
          (fun idx h1 => h1 ▸ H.isHomogeneous_quot _ _ _)
      refine ⟨g2, p2, fun u => ext2.lift (gateW u),
        fun m u w => quotFlat (qEquiv (m, u, w)),
        by simp [hg2, hg1], hp2M, ?_, ?_⟩
      · intro u
        refine ⟨by simpa [ext2.depth_eq] using hgd1 u,
          by simpa [ext2.costDepth_eq] using (hgp1 u).le, fun _ hdeg1 => ?_⟩
        rw [ext2.trace_eq]
        exact hgt1 u (by simpa using hdeg1)
      · intro m u w
        refine ⟨hqd2 _, (hqp2 _).le, fun _ _ hdiff => ?_⟩
        have h := hqt2 (qEquiv (m, u, w)) (by simpa [Dq] using hdiff)
        simpa [Fq] using h
    | succ r ih =>
      obtain ⟨g0, p0, gateW0, quotW0, hg0, hp0M, hgate0, hquot0⟩ := ih
      -- Phase A: update `gateW u` for all `u` with `2 ^ r < H.deg u ≤ min d (2 ^ (r + 1))`.
      let updA : Fin H.size → Prop := fun u =>
        2 ^ r < H.deg u ∧ H.deg u ≤ d ∧ H.deg u ≤ 2 ^ (r + 1)
      let _ : DecidablePred updA := fun u => by unfold updA; infer_instance
      let mA : ℕ := 2 ^ r
      let frontierListA : Fin H.size → List (Fin H.size) := fun u =>
        ((H.frontier mA).filter fun w => H.deg w ≤ H.deg u).toList
      let tripleOfA (u : Fin H.size) (w : Fin H.size) : Wire n g0 × Wire n g0 × Wire n g0 :=
        if hmu : mA < d + 1 then
          match H.gates w with
          | .mul w₁ w₂ =>
            (gateW0 ⟨w₁.1, w₁.2.trans w.2⟩, gateW0 ⟨w₂.1, w₂.2.trans w.2⟩,
              quotW0 ⟨mA, hmu⟩ u w)
          | _ => (gateW0 u, gateW0 u, gateW0 u)
        else (gateW0 u, gateW0 u, gateW0 u)
      let triplesA (u : Fin H.size) : List (Wire n g0 × Wire n g0 × Wire n g0) :=
        (frontierListA u).map (tripleOfA u)
      have hlenA : ∀ u, updA u → (triplesA u).length ≤ H.size := fun u _ => by
        dsimp only [triplesA, frontierListA]
        rw [List.length_map, Finset.length_toList]
        exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin H.size)
      have hdepthA : ∀ u, updA u → ∀ t ∈ triplesA u,
          (p0.wireDepths t.1 ≤ 5 * r + 1 ∧ p0.wireDepths t.2.1 ≤ 5 * r + 1) ∧
          p0.wireDepths t.2.2 ≤ 5 * r + 1 ∧
          (p0.wireDepthsWith SigmaPiOp.mulCost t.1 ≤ 3 * r ∧
            p0.wireDepthsWith SigmaPiOp.mulCost t.2.1 ≤ 3 * r) ∧
          p0.wireDepthsWith SigmaPiOp.mulCost t.2.2 ≤ 3 * r := by
        intro u _ t ht
        rcases List.mem_map.mp ht with ⟨w, _, rfl⟩
        dsimp only [tripleOfA]
        split_ifs
        · cases H.gates w <;>
            exact ⟨⟨(hgate0 _).1, (hgate0 _).1⟩,
              by first | exact (hquot0 _ _ _).1 | exact (hgate0 _).1,
              ⟨(hgate0 _).2.1, (hgate0 _).2.1⟩,
              by first | exact (hquot0 _ _ _).2.1 | exact (hgate0 _).2.1⟩
        · exact ⟨⟨(hgate0 _).1, (hgate0 _).1⟩, (hgate0 _).1,
            ⟨(hgate0 _).2.1, (hgate0 _).2.1⟩, (hgate0 _).2.1⟩
      obtain ⟨g1, p1, gateW1, ext1, hg1, hp1M, hkeepA, hupdA⟩ :=
        hbatchTriples p0 hp0M H.size (5 * r + 1) (5 * r + 1) (3 * r) (3 * r)
          gateW0 updA triplesA hlenA
          (fun u hu t ht => (hdepthA u hu t ht).1)
          (fun u hu t ht => (hdepthA u hu t ht).2.1)
          (fun u hu t ht => (hdepthA u hu t ht).2.2.1)
          (fun u hu t ht => (hdepthA u hu t ht).2.2.2)
      -- Verify Phase A correctness & depth bounds (`depth ≤ 5r + 4`, `mulDepth ≤ 3r + 2`).
      have hgate1 : ∀ u : Fin H.size,
          p1.wireDepths (gateW1 u) ≤ 5 * r + 4 ∧
          p1.wireDepthsWith SigmaPiOp.mulCost (gateW1 u) ≤ 3 * r + 2 ∧
          (H.deg u ≤ d → H.deg u ≤ 2 ^ (r + 1) → p1.trace I X (gateW1 u) = H.gatePoly u) := by
        intro u
        by_cases hu : updA u
        · rcases hupdA u hu with ⟨htr_u, hd_u, hp_u⟩
          refine ⟨by omega, by omega, fun _ _ => ?_⟩
          rw [htr_u]
          have hm1 : 1 ≤ mA := Nat.one_le_two_pow
          have hmu : mA < H.deg u := hu.1
          have hmd : mA < d + 1 := by have := hu.2.1; omega
          rw [H.gatePoly_eq_sum_frontier hm1 u hmu]
          have hfilt_sum :
              (∑ w ∈ H.frontier mA, H.quot mA u w * H.gatePoly w) =
                ∑ w ∈ (H.frontier mA).filter (fun w => H.deg w ≤ H.deg u),
                  H.quot mA u w * H.gatePoly w := by
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) fun w hw hnot => ?_
            have hlt : H.deg u < H.deg w := by
              simp only [Finset.mem_filter, hw, true_and, not_le] at hnot
              exact hnot
            rw [H.quot_eq_zero_of_lt mA u w hlt, zero_mul]
          rw [hfilt_sum]
          have hlist_sum : ∀ (S : Finset (Fin H.size)) (f : Fin H.size → MvPolynomial (Fin n) K),
              (S.toList.map f).sum = ∑ w ∈ S, f w := fun S f => by
            rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
            rfl
          rw [← hlist_sum, List.map_map]
          congr 1
          refine List.map_congr_left fun w hw => ?_
          have hw_mem := Finset.mem_toList.mp hw
          rw [Finset.mem_filter] at hw_mem
          have hw_fr := (Finset.mem_filter.mp hw_mem.1).2
          have hw_le := hw_mem.2
          dsimp only [Function.comp_apply, tripleOfA]
          rw [dite_eq_left hmd]
          rcases hw_fr with ⟨hw_gt, hw_mul⟩
          cases hgw : H.gates w with
          | zero _ => rw [hgw] at hw_mul; exact False.elim hw_mul
          | var _ => rw [hgw] at hw_mul; exact False.elim hw_mul
          | add _ _ _ _ => rw [hgw] at hw_mul; exact False.elim hw_mul
          | mul w₁ w₂ =>
            rw [hgw] at hw_mul
            let w₁' : Fin H.size := ⟨w₁.1, w₁.2.trans w.2⟩
            let w₂' : Fin H.size := ⟨w₂.1, w₂.2.trans w.2⟩
            have h1m : H.deg w₁' ≤ mA := hw_mul.1
            have h2m : H.deg w₂' ≤ mA := hw_mul.2
            have hw₁_tr : p0.trace I X (gateW0 w₁') = H.gatePoly w₁' :=
              (hgate0 w₁').2.2 (by have := hu.2.1; omega) h1m
            have hw₂_tr : p0.trace I X (gateW0 w₂') = H.gatePoly w₂' :=
              (hgate0 w₂').2.2 (by have := hu.2.1; omega) h2m
            have hq_tr : p0.trace I X (quotW0 ⟨mA, hmd⟩ u w) = H.quot mA u w := by
              have hdiff : H.deg u - H.deg w ≤ 2 ^ r := by
                have h2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
                have := hu.2.2
                dsimp only [mA] at hw_gt
                omega
              exact (hquot0 ⟨mA, hmd⟩ u w).2.2 hm1 hu.2.1 hdiff
            dsimp only
            rw [hw₁_tr, hw₂_tr, hq_tr]
            have hgp_w : H.gatePoly w = H.gatePoly w₁' * H.gatePoly w₂' := by
              rw [gatePoly_eq, hgw]
            rw [hgp_w, mul_comm]
        · rw [hkeepA u hu, ext1.depth_eq, ext1.costDepth_eq]
          refine ⟨(hgate0 u).1.trans (by omega), (hgate0 u).2.1.trans (by omega),
            fun hud h2r => ?_⟩
          rw [ext1.trace_eq]
          have hle2r : H.deg u ≤ 2 ^ r := by
            dsimp only [updA] at hu
            omega
          exact (hgate0 u).2.2 hud hle2r
      -- Phase B: update `quotW m u w` for `1 ≤ m`, `deg u ≤ d`, `2^r < deg u - deg w ≤ 2^(r+1)`.
      let quotW1 (m : Fin (d + 1)) (u w : Fin H.size) : Wire n g1 := ext1.lift (quotW0 m u w)
      let flatOld : Fin ((d + 1) * H.size ^ 2) → Wire n g1 := fun idx =>
        let t := qEquiv.symm idx
        quotW1 t.1 t.2.1 t.2.2
      let updB : Fin ((d + 1) * H.size ^ 2) → Prop := fun idx =>
        let t := qEquiv.symm idx
        1 ≤ t.1.1 ∧ H.deg t.2.1 ≤ d ∧ 2 ^ r < H.deg t.2.1 - H.deg t.2.2 ∧
          H.deg t.2.1 - H.deg t.2.2 ≤ 2 ^ (r + 1)
      let _ : DecidablePred updB := fun idx => by unfold updB; infer_instance
      let predB (m : Fin (d + 1)) (u w v : Fin H.size) : Prop :=
        H.deg v ≤ H.deg u ∧
        match H.gates v with
        | .mul v₁ v₂ =>
          let v₁' : Fin H.size := ⟨v₁.1, v₁.2.trans v.2⟩
          let v₂' : Fin H.size := ⟨v₂.1, v₂.2.trans v.2⟩
          ¬(H.deg v₁' ≤ m.1 ∧ H.deg v₂' ≤ m.1) ∧
          if H.deg v₂' ≤ H.deg v₁' then H.deg w ≤ H.deg v₁' else H.deg w ≤ H.deg v₂'
        | _ => False
      classical
      let frontierListB (m : Fin (d + 1)) (u w : Fin H.size) : List (Fin H.size) :=
        if hm_lt : m.1 < H.deg w then
          let t := H.deg w + 2 ^ r
          ((H.frontier t).filter (predB m u w)).toList
        else []
      let tripleOfB (m : Fin (d + 1)) (u w : Fin H.size) (v : Fin H.size) :
          Wire n g1 × Wire n g1 × Wire n g1 :=
        let t := H.deg w + 2 ^ r
        if ht : t < d + 1 then
          match H.gates v with
          | .mul v₁ v₂ =>
            let v₁' : Fin H.size := ⟨v₁.1, v₁.2.trans v.2⟩
            let v₂' : Fin H.size := ⟨v₂.1, v₂.2.trans v.2⟩
            if H.deg v₂' ≤ H.deg v₁' then
              (quotW1 ⟨t, ht⟩ u v, quotW1 m v₁' w, gateW1 v₂')
            else
              (quotW1 ⟨t, ht⟩ u v, quotW1 m v₂' w, gateW1 v₁')
          | _ => (quotW1 m u w, quotW1 m u w, gateW1 u)
        else (quotW1 m u w, quotW1 m u w, gateW1 u)
      let triplesB (idx : Fin ((d + 1) * H.size ^ 2)) :
          List (Wire n g1 × Wire n g1 × Wire n g1) :=
        let p := qEquiv.symm idx
        (frontierListB p.1 p.2.1 p.2.2).map (tripleOfB p.1 p.2.1 p.2.2)
      have hlenB : ∀ idx, updB idx → (triplesB idx).length ≤ H.size := fun idx _ => by
        dsimp only [triplesB, frontierListB]
        split_ifs
        · rw [List.length_map, Finset.length_toList]
          exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin H.size)
        · simp
      have hdepthB : ∀ idx, updB idx → ∀ s ∈ triplesB idx,
          (p1.wireDepths s.1 ≤ 5 * r + 1 ∧ p1.wireDepths s.2.1 ≤ 5 * r + 1) ∧
          p1.wireDepths s.2.2 ≤ 5 * r + 4 ∧
          (p1.wireDepthsWith SigmaPiOp.mulCost s.1 ≤ 3 * r ∧
            p1.wireDepthsWith SigmaPiOp.mulCost s.2.1 ≤ 3 * r) ∧
          p1.wireDepthsWith SigmaPiOp.mulCost s.2.2 ≤ 3 * r + 2 := by
        intro idx _ s hs
        rcases List.mem_map.mp hs with ⟨v, _, rfl⟩
        dsimp only [tripleOfB]
        split_ifs
        · cases H.gates v with
          | mul v₁ v₂ =>
            dsimp only
            split_ifs <;>
              exact ⟨⟨by simpa [quotW1, ext1.depth_eq] using (hquot0 _ _ _).1,
                  by simpa [quotW1, ext1.depth_eq] using (hquot0 _ _ _).1⟩,
                (hgate1 _).1,
                ⟨by simpa [quotW1, ext1.costDepth_eq] using (hquot0 _ _ _).2.1,
                  by simpa [quotW1, ext1.costDepth_eq] using (hquot0 _ _ _).2.1⟩,
                (hgate1 _).2.1⟩
          | _ =>
            exact ⟨⟨by simpa [quotW1, ext1.depth_eq] using (hquot0 _ _ _).1,
                by simpa [quotW1, ext1.depth_eq] using (hquot0 _ _ _).1⟩,
              (hgate1 _).1,
              ⟨by simpa [quotW1, ext1.costDepth_eq] using (hquot0 _ _ _).2.1,
                by simpa [quotW1, ext1.costDepth_eq] using (hquot0 _ _ _).2.1⟩,
              (hgate1 _).2.1⟩
        · exact ⟨⟨by simpa [quotW1, ext1.depth_eq] using (hquot0 _ _ _).1,
              by simpa [quotW1, ext1.depth_eq] using (hquot0 _ _ _).1⟩,
            (hgate1 _).1,
            ⟨by simpa [quotW1, ext1.costDepth_eq] using (hquot0 _ _ _).2.1,
              by simpa [quotW1, ext1.costDepth_eq] using (hquot0 _ _ _).2.1⟩,
            (hgate1 _).2.1⟩
      obtain ⟨g2, p2, quotFlat2, ext2, hg2, hp2M, hkeepB, hupdB⟩ :=
        hbatchTriples p1 hp1M ((d + 1) * H.size ^ 2) (5 * r + 1) (5 * r + 4) (3 * r) (3 * r + 2)
          flatOld updB triplesB hlenB
          (fun idx hi s hs => (hdepthB idx hi s hs).1)
          (fun idx hi s hs => (hdepthB idx hi s hs).2.1)
          (fun idx hi s hs => (hdepthB idx hi s hs).2.2.1)
          (fun idx hi s hs => (hdepthB idx hi s hs).2.2.2)
      refine ⟨g2, p2, fun u => ext2.lift (gateW1 u),
        fun m u w => quotFlat2 (qEquiv (m, u, w)), ?_, hp2M, ?_, ?_⟩
      · calc
          g2 ≤ g1 + (d + 1) * H.size ^ 2 * (2 * H.size + 1) := hg2
          _ ≤ g0 + H.size * (2 * H.size + 1) +
              (d + 1) * H.size ^ 2 * (2 * H.size + 1) := Nat.add_le_add_right hg1 _
          _ ≤ (H.size + (d + 1) * H.size ^ 2) * (1 + r * (2 * H.size + 1)) +
              H.size * (2 * H.size + 1) + (d + 1) * H.size ^ 2 * (2 * H.size + 1) :=
            Nat.add_le_add_right (Nat.add_le_add_right hg0 _) _
          _ = (H.size + (d + 1) * H.size ^ 2) * (1 + (r + 1) * (2 * H.size + 1)) := by ring
      · intro u
        refine ⟨by rw [ext2.depth_eq]; exact (hgate1 u).1.trans (by omega),
          by rw [ext2.costDepth_eq]; exact (hgate1 u).2.1.trans (by omega),
          fun hud h2r => by rw [ext2.trace_eq]; exact (hgate1 u).2.2 hud h2r⟩
      · intro m u w
        dsimp only
        let idx := qEquiv (m, u, w)
        change p2.wireDepths (quotFlat2 idx) ≤ 5 * (r + 1) + 1 ∧
          p2.wireDepthsWith SigmaPiOp.mulCost (quotFlat2 idx) ≤ 3 * (r + 1) ∧
          (1 ≤ m.1 → H.deg u ≤ d → H.deg u - H.deg w ≤ 2 ^ (r + 1) →
            p2.trace I X (quotFlat2 idx) = H.quot m.1 u w)
        by_cases hiu : updB idx
        · rcases hupdB idx hiu with ⟨htr_q, hd_q, hp_q⟩
          refine ⟨by omega, by omega, fun hm1 hud hdiff => ?_⟩
          rw [htr_q]
          dsimp only [triplesB, idx]
          rw [Equiv.symm_apply_apply]
          dsimp only [frontierListB]
          by_cases hmw : m.1 < H.deg w
          · rw [dite_eq_left hmw]
            let t := H.deg w + 2 ^ r
            have hmt : m.1 ≤ t := by dsimp [t]; omega
            have hwt : H.deg w ≤ t := by dsimp [t]; omega
            have hdiff_gt : 2 ^ r < H.deg u - H.deg w := by
              have hiu' := hiu
              dsimp only [updB, idx] at hiu'
              rw [Equiv.symm_apply_apply] at hiu'
              exact hiu'.2.2.1
            have htu : t < H.deg u := by dsimp [t]; omega
            have ht_lt : t < d + 1 := by omega
            rw [H.quot_eq_sum_frontier hm1 hmt u w hwt htu]
            let S_good := (H.frontier t).filter (predB m u w)
            have hfilt_eq :
                (∑ v ∈ H.frontier t, H.quot t u v * H.quot m.1 v w) =
                  ∑ v ∈ S_good, H.quot t u v * H.quot m.1 v w := by
              symm
              refine Finset.sum_subset (Finset.filter_subset _ _) fun v hv hnot => ?_
              have hv_fr := (Finset.mem_filter.mp hv).2
              by_cases hvu : H.deg v ≤ H.deg u
              · rcases hv_fr with ⟨hvt, hv_mul⟩
                have hvw : v ≠ w := by rintro rfl; omega
                cases hgv : H.gates v with
                | zero _ => rw [hgv] at hv_mul; exact False.elim hv_mul
                | var _ => rw [hgv] at hv_mul; exact False.elim hv_mul
                | add _ _ _ _ => rw [hgv] at hv_mul; exact False.elim hv_mul
                | mul v₁ v₂ =>
                  let v₁' : Fin H.size := ⟨v₁.1, v₁.2.trans v.2⟩
                  let v₂' : Fin H.size := ⟨v₂.1, v₂.2.trans v.2⟩
                  have hcond_false : ¬(¬(H.deg v₁' ≤ m.1 ∧ H.deg v₂' ≤ m.1) ∧
                      if H.deg v₂' ≤ H.deg v₁' then H.deg w ≤ H.deg v₁'
                      else H.deg w ≤ H.deg v₂') := by
                    intro hc
                    apply hnot
                    rw [Finset.mem_filter]
                    refine ⟨hv, hvu, ?_⟩
                    rw [hgv]
                    exact hc
                  conv_lhs =>
                    rhs
                    rw [quot, ite_eq_right (by omega), ite_eq_right hvw, hgv]
                  dsimp only
                  by_cases hfrm : H.deg v₁' ≤ m.1 ∧ H.deg v₂' ≤ m.1
                  · rw [ite_eq_left hfrm, mul_zero]
                  · rw [ite_eq_right hfrm]
                    by_cases hcmp : H.deg v₂' ≤ H.deg v₁'
                    · rw [ite_eq_left hcmp]
                      have hlt1 : H.deg v₁' < H.deg w := by
                        by_contra hge
                        exact hcond_false ⟨hfrm, by rw [ite_eq_left hcmp]; omega⟩
                      rw [H.quot_eq_zero_of_lt m.1 v₁' w hlt1, mul_zero, mul_zero]
                    · rw [ite_eq_right hcmp]
                      have hlt2 : H.deg v₂' < H.deg w := by
                        by_contra hge
                        exact hcond_false ⟨hfrm, by rw [ite_eq_right hcmp]; omega⟩
                      rw [H.quot_eq_zero_of_lt m.1 v₂' w hlt2, mul_zero, mul_zero]
              · rw [H.quot_eq_zero_of_lt t u v (by omega), zero_mul]
            rw [hfilt_eq]
            have hlist_sum : ∀ (S : Finset (Fin H.size)) (f : Fin H.size → MvPolynomial (Fin n) K),
                (S.toList.map f).sum = ∑ v ∈ S, f v := fun S f => by
              rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
              rfl
            rw [← hlist_sum, List.map_map]
            congr 1
            refine List.map_congr_left fun v hv => ?_
            have hv_mem := Finset.mem_toList.mp hv
            rw [Finset.mem_filter] at hv_mem
            have hv_fr := (Finset.mem_filter.mp hv_mem.1).2
            rcases hv_mem.2 with ⟨hvu, hv_cond⟩
            rcases hv_fr with ⟨hvt, hv_mul⟩
            have hvw : v ≠ w := by rintro rfl; omega
            dsimp only [Function.comp_apply, tripleOfB]
            rw [dite_eq_left ht_lt]
            have hgd := H.gate_deg v
            cases hgv : H.gates v with
            | zero _ => rw [hgv] at hv_mul; exact False.elim hv_mul
            | var _ => rw [hgv] at hv_mul; exact False.elim hv_mul
            | add _ _ _ _ => rw [hgv] at hv_mul; exact False.elim hv_mul
            | mul v₁ v₂ =>
              rw [hgv] at hv_mul hv_cond hgd
              let v₁' : Fin H.size := ⟨v₁.1, v₁.2.trans v.2⟩
              let v₂' : Fin H.size := ⟨v₂.1, v₂.2.trans v.2⟩
              change H.deg v = H.deg v₁' + H.deg v₂' at hgd
              have hqt_tr : p1.trace I X (quotW1 ⟨t, ht_lt⟩ u v) = H.quot t u v := by
                dsimp only [quotW1]
                rw [ext1.trace_eq]
                have hdiff_uv : H.deg u - H.deg v ≤ 2 ^ r := by
                  have h2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
                  omega
                exact (hquot0 ⟨t, ht_lt⟩ u v).2.2 (by dsimp [t]; omega) hud hdiff_uv
              have h2r_eq : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
              dsimp only
              by_cases hcmp : H.deg v₂' ≤ H.deg v₁'
              · rw [ite_eq_left hcmp]
                have hle1 : H.deg w ≤ H.deg v₁' := by
                  have hc := hv_cond.2
                  rwa [ite_eq_left hcmp] at hc
                have hqm_tr : p1.trace I X (quotW1 m v₁' w) = H.quot m.1 v₁' w := by
                  dsimp only [quotW1]
                  rw [ext1.trace_eq]
                  have hv1t : H.deg v₁' ≤ H.deg w + 2 ^ r := hv_mul.1
                  exact (hquot0 m v₁' w).2.2 hm1 (by omega) (by omega)
                have hgv2_tr : p1.trace I X (gateW1 v₂') = H.gatePoly v₂' :=
                  (hgate1 v₂').2.2 (by omega) (by omega)
                rw [hqt_tr, hqm_tr, hgv2_tr]
                conv_rhs =>
                  rhs
                  rw [quot, ite_eq_right (by omega), ite_eq_right hvw, hgv]
                dsimp only
                rw [ite_eq_right hv_cond.1, ite_eq_left hcmp]
                ring
              · rw [ite_eq_right hcmp]
                have hle2 : H.deg w ≤ H.deg v₂' := by
                  have hc := hv_cond.2
                  rwa [ite_eq_right hcmp] at hc
                have hqm_tr : p1.trace I X (quotW1 m v₂' w) = H.quot m.1 v₂' w := by
                  dsimp only [quotW1]
                  rw [ext1.trace_eq]
                  have hv2t : H.deg v₂' ≤ H.deg w + 2 ^ r := hv_mul.2
                  exact (hquot0 m v₂' w).2.2 hm1 (by omega) (by omega)
                have hgv1_tr : p1.trace I X (gateW1 v₁') = H.gatePoly v₁' :=
                  (hgate1 v₁').2.2 (by omega) (by omega)
                rw [hqt_tr, hqm_tr, hgv1_tr]
                conv_rhs =>
                  rhs
                  rw [quot, ite_eq_right (by omega), ite_eq_right hvw, hgv]
                dsimp only
                rw [ite_eq_right hv_cond.1, ite_eq_right hcmp]
                ring
          · rw [dite_eq_right hmw]
            simp only [List.map_nil, List.sum_nil]
            exact (H.quot_eq_zero_of_deg_le m.1 u w (by omega)).symm
        · rw [hkeepB idx hiu]
          have hflat : flatOld idx = ext1.lift (quotW0 m u w) := by
            simp [flatOld, idx, quotW1]
          rw [hflat, ext2.depth_eq, ext1.depth_eq, ext2.costDepth_eq, ext1.costDepth_eq]
          refine ⟨(hquot0 m u w).1.trans (by omega), (hquot0 m u w).2.1.trans (by omega),
            fun hm1 hud hdiff => ?_⟩
          rw [ext2.trace_eq, ext1.trace_eq]
          have hle2r : H.deg u - H.deg w ≤ 2 ^ r := by
            dsimp only [updB, idx] at hiu
            rw [Equiv.symm_apply_apply] at hiu
            dsimp only at hiu
            omega
          exact (hquot0 m u w).2.2 hm1 hud hle2r
  obtain ⟨g, p, gateW, _, hg, hpM, hgate, _⟩ := hrounds R
  have hd_le_pow : d ≤ 2 ^ R := Nat.le_pow_clog (by decide) d
  exact ⟨g, p, gateW, hg, hpM, fun u hud =>
    ⟨(hgate u).2.2 hud (hud.trans hd_le_pow), (hgate u).1, (hgate u).2.1⟩⟩

/-- **VSBR logarithmic-depth reduction for an arbitrary arithmetic circuit** (unbounded-sum,
fan-in-two-product `SPCircuit`): any `c : Circuit (arithSignature K) n 1` computing a polynomial
of total degree at most `d` compiles to an `SPCircuit K n` computing `c.polynomial 0` with:
* depth at most `5 * Nat.clog 2 (max 1 d) + 2`,
* product-depth at most `3 * Nat.clog 2 (max 1 d)`,
* fan-in at most `max 2 (max n (max (d + 1) (2 * (n + c.size) * (max 1 d) ^ 2)))`, and
* size polynomial in `(n, c.size, d)`. -/
theorem exists_spCircuit_log_depth {K : Type u} [CommSemiring K] {n d : ℕ}
    (c : Circuit (arithSignature K) n 1) (hdeg : (c.polynomial 0).totalDegree ≤ d) :
    let D := max 1 d
    let S := 2 * (n + c.size) * D ^ 2
    let R := Nat.clog 2 D
    ∃ C : SPCircuit K n,
      C.polynomial = c.polynomial 0 ∧
      C.depth ≤ 5 * R + 2 ∧
      C.productDepth ≤ 3 * R ∧
      C.FanInAtMost (max 2 (max n (max (d + 1) S))) ∧
      C.size ≤ (S + (D + 1) * S ^ 2) * (1 + R * (2 * S + 1)) + 2 := by
  intro D S R
  let I := sigmaPiInterpretationWith K (C : K → MvPolynomial (Fin n) K)
  let M := max 2 (max n (max (d + 1) S))
  have hD1 : 1 ≤ D := le_max_left 1 d
  obtain ⟨H, compGate, hHsz, hcomp⟩ := exists_homogCircuit_allComponents hD1 c
  obtain ⟨g, p, gateW, hg, hpM, hgate⟩ := H.exists_spProgram_log_depth (d := D)
  have hSM : max 2 (max n H.size) ≤ M := by
    refine max_le (le_max_left 2 _) (max_le ((le_max_left n _).trans (le_max_right 2 _)) ?_)
    exact (hHsz.trans (le_max_right (d + 1) S)).trans
      ((le_max_right n _).trans (le_max_right 2 _))
  have hpM' : p.FanInAtMost M :=
    Program.fanInAtMost_iff.mpr fun k => (Program.fanInAtMost_iff.mp hpM k).trans hSM
  -- Append constant term `C ((c.polynomial 0).coeff 0)` and one final sum over `k = 0, …, d`.
  let constLine : Line (sigmaPiSignature K) n g := ⟨.const ((c.polynomial 0).coeff 0), Fin.elim0⟩
  let p1 : Program (sigmaPiSignature K) n (g + 1) := p.gate constLine
  let sumWires : Fin (d + 1) → Wire n (g + 1) := fun k =>
    if hk : k.1 = 0 then .gate (Fin.last g)
    else (gateW (compGate ⟨k.1 - 1, by have := k.2; omega⟩)).castSucc
  let sumLine : Line (sigmaPiSignature K) n (g + 1) := ⟨.add (d + 1) (fun _ => 1), sumWires⟩
  let p2 : Program (sigmaPiSignature K) n (g + 2) := p1.gate sumLine
  let C : SPCircuit K n := ⟨p2, fun _ => .gate (Fin.last (g + 1))⟩
  have hM_d1 : d + 1 ≤ M :=
    (le_max_left (d + 1) S).trans ((le_max_right n _).trans (le_max_right 2 _))
  have hfanC : C.FanInAtMost M := ⟨⟨hpM', Nat.zero_le M⟩, hM_d1⟩
  have hC_poly : C.polynomial = c.polynomial 0 := by
    change p2.trace I X (.gate (Fin.last (g + 1))) = c.polynomial 0
    rw [Program.trace_gate_last]
    simp only [I, sumLine, sigmaPiInterpretationWith_add, map_one, one_mul]
    have hsum_range :
        (∑ k : Fin (d + 1), p1.trace I X (sumWires k)) =
          ∑ k ∈ Finset.range (d + 1),
            if hk : k < d + 1 then p1.trace I X (sumWires ⟨k, hk⟩) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => by rw [dite_eq_left k.2]
    rw [hsum_range]
    have hterm : ∀ k ∈ Finset.range (d + 1),
        (if hk : k < d + 1 then p1.trace I X (sumWires ⟨k, hk⟩) else 0) =
          homogeneousComponent k (c.polynomial 0) := by
      intro k hk
      have hklt : k < d + 1 := Finset.mem_range.mp hk
      rw [dite_eq_left hklt]
      dsimp only [sumWires]
      by_cases hk0 : k = 0
      · subst hk0
        rw [dite_eq_left rfl, Program.trace_gate_last]
        exact (homogeneousComponent_zero_eq_C_coeff _).symm
      · rw [dite_eq_right hk0, Program.trace_gate_castSucc]
        have hc := hcomp ⟨k - 1, by omega⟩
        have hdeg_le : H.deg (compGate ⟨k - 1, by omega⟩) ≤ D := by
          rw [hc.1]; omega
        rw [(hgate _ hdeg_le).1, hc.2, show k - 1 + 1 = k by omega]
    rw [Finset.sum_congr rfl hterm]
    ext e
    rw [coeff_sum]
    simp only [coeff_homogeneousComponent]
    rw [Finset.sum_ite_eq (Finset.range (d + 1)) e.degree]
    by_cases hed : e.degree < d + 1
    · rw [ite_eq_left (Finset.mem_range.mpr hed)]
    · rw [ite_eq_right (by simpa [Finset.mem_range] using hed)]
      symm
      by_contra hne
      have hle_td : e.degree ≤ (c.polynomial 0).totalDegree :=
        Finset.le_sup (f := fun s => s.sum fun _ m => m) (mem_support_iff.mpr hne)
      omega
  have hC_depth : C.depth ≤ 5 * R + 2 := by
    rw [Circuit.depth_le_iff]
    intro j
    change p2.wireDepths (.gate (Fin.last (g + 1))) ≤ 5 * R + 2
    rw [Program.wireDepths_gateWire, Program.depths_gate_last]
    refine (line_depth_le sumLine p1.wireDepths (D := 5 * R + 1) fun k => ?_).trans (by omega)
    have hk_lt : k.1 < d + 1 := k.2
    dsimp only [sumLine, sumWires]
    by_cases hk0 : k.1 = 0
    · rw [dite_eq_left hk0, Program.wireDepths_gateWire, Program.depths_gate_last]
      exact (line_depth_le constLine p.wireDepths (D := 0) fun a => a.elim0).trans (by omega)
    · rw [dite_eq_right hk0, Program.wireDepths_gate_castSucc]
      have hc := hcomp ⟨k.1 - 1, by omega⟩
      exact (hgate _ (by rw [hc.1]; omega)).2.1
  have hC_pdepth : C.productDepth ≤ 3 * R := by
    rw [SPCircuit.productDepth, Circuit.depthWith_le_iff]
    intro j
    change p2.wireDepthsWith SigmaPiOp.mulCost (.gate (Fin.last (g + 1))) ≤ 3 * R
    rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
    refine (line_depthWith_le SigmaPiOp.mulCost sumLine _ (D := 3 * R) fun k => ?_).trans
      (by simp [sumLine])
    have hk_lt : k.1 < d + 1 := k.2
    dsimp only [sumLine, sumWires]
    by_cases hk0 : k.1 = 0
    · rw [dite_eq_left hk0, Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
      refine (line_depthWith_le SigmaPiOp.mulCost constLine _ (D := 0) fun a => a.elim0).trans ?_
      simp [constLine]
    · rw [dite_eq_right hk0, Program.wireDepthsWith_gate_castSucc]
      have hc := hcomp ⟨k.1 - 1, by omega⟩
      exact (hgate _ (by rw [hc.1]; omega)).2.2
  have hC_size : C.size ≤ (S + (D + 1) * S ^ 2) * (1 + R * (2 * S + 1)) + 2 := by
    change g + 2 ≤ _
    refine Nat.add_le_add_right (hg.trans ?_) 2
    have h1 : H.size + (D + 1) * H.size ^ 2 ≤ S + (D + 1) * S ^ 2 :=
      Nat.add_le_add hHsz (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHsz 2))
    have h2 : 1 + R * (2 * H.size + 1) ≤ 1 + R * (2 * S + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left R (by omega)) 1
    exact Nat.mul_le_mul h1 h2
  exact ⟨C, hC_poly, hC_depth, hC_pdepth, hfanC, hC_size⟩

/-- Shared-wire balanced binary fold in `Program (arithSignature K) n g` for `.add` (unit `0`) or
`.mul` (unit `1`), preserving all earlier wires and adding at most `ws.length + 1` gates while
raising depth by at most `Nat.clog 2 ws.length`. -/
private theorem arithPushBalancedFold {K : Type u} [CommSemiring K] {n : ℕ}
    (op : ArithOp K) (hop : ArithOp.arity K op = 2) (e : K)
    (bin : MvPolynomial (Fin n) K → MvPolynomial (Fin n) K → MvPolynomial (Fin n) K)
    (hbin : ∀ x : Fin 2 → MvPolynomial (Fin n) K,
      arithInterpretationWith K C op (fun a => x (Fin.cast hop a)) = bin (x 0) (x 1))
    (hassoc : ∀ a b c, bin (bin a b) c = bin a (bin b c))
    (hlid : ∀ a, bin (C e) a = a) (hrid : ∀ a, bin a (C e) = a)
    {g D : ℕ} (p : Program (arithSignature K) n g)
    (ws : List (Wire n g)) (hD : ∀ w ∈ ws, p.wireDepths w ≤ D) :
    let I := arithInterpretationWith K (C : K → MvPolynomial (Fin n) K)
    ∃ (g' : ℕ) (p' : Program (arithSignature K) n g') (out : Wire n g')
      (_ext : ProgExt (arithSignature K) I (fun _ => 1) p p'),
      (ws = [] → g' ≤ g + 1) ∧
      (ws ≠ [] → g' ≤ g + (ws.length - 1)) ∧
      p'.trace I X out = (ws.map (p.trace I X)).foldr bin (C e) ∧
      (ws = [] → p'.wireDepths out ≤ 1) ∧
      (ws ≠ [] → p'.wireDepths out ≤ D + Nat.clog 2 ws.length) := by
  intro I
  induction hlen : ws.length using Nat.strongRecOn generalizing g D ws with
  | ind m ih =>
    subst hlen
    match ws with
    | [] =>
      let line : Line (arithSignature K) n g := ⟨.const e, Fin.elim0⟩
      refine ⟨g + 1, p.gate line, .gate (Fin.last g), ProgExt.gate I (fun _ => 1) p line,
        fun _ => le_rfl, fun h => absurd rfl h, ?_, ?_, fun h => absurd rfl h⟩
      · rw [Program.trace_gate_last]; rfl
      · intro _
        rw [Program.wireDepths_gateWire, Program.depths_gate_last]
        exact line_depth_le line p.wireDepths (D := 0) fun a => a.elim0
    | [w] =>
      refine ⟨g, p, w, ProgExt.refl p, fun h => absurd h (List.cons_ne_nil _ _),
        fun _ => by simp, ?_, fun h => absurd h (List.cons_ne_nil _ _), ?_⟩
      · simp [hrid]
      · intro _
        simpa using hD w List.mem_cons_self
    | w₁ :: w₂ :: rest =>
      set L := w₁ :: w₂ :: rest
      have hL2 : 2 ≤ L.length := by simp [L]
      let L₁ := L.take (L.length / 2)
      let L₂ := L.drop (L.length / 2)
      have hL₁_ne : L₁ ≠ [] := by simp [L₁, L, List.take_eq_nil_iff]
      have hL₂_ne : L₂ ≠ [] := by
        simp only [L₂, L, ne_eq, List.drop_eq_nil_iff, List.length_cons]
        omega
      have hL₁_lt : L₁.length < L.length := by simp only [L₁, List.length_take]; omega
      have hL₂_lt : L₂.length < L.length := by simp only [L₂, List.length_drop]; omega
      obtain ⟨g₁, p₁, out₁, ext₁, _, hg₁, htr₁, _, hd₁⟩ :=
        ih L₁.length hL₁_lt p L₁ (fun w hw => hD w (List.mem_of_mem_take hw)) rfl
      obtain ⟨g₂, p₂, out₂, ext₂, _, hg₂, htr₂, _, hd₂⟩ :=
        ih (L₂.map ext₁.lift).length (by rw [List.length_map]; exact hL₂_lt)
          p₁ (L₂.map ext₁.lift) (fun w hw => by
            rcases List.mem_map.mp hw with ⟨u, hu, rfl⟩
            rw [ext₁.depth_eq]
            exact hD u (List.mem_of_mem_drop hu)) rfl
      let line : Line (arithSignature K) n g₂ :=
        ⟨op, fun a => ![ext₂.lift out₁, out₂] (Fin.cast hop a)⟩
      let p₃ : Program (arithSignature K) n (g₂ + 1) := p₂.gate line
      have hL₂_map_ne : L₂.map ext₁.lift ≠ [] := by simpa using hL₂_ne
      have hlen₁ : L₁.length ≤ (L.length + 1) / 2 := by
        simp only [L₁, List.length_take]; omega
      have hlen₂ : (L₂.map ext₁.lift).length ≤ (L.length + 1) / 2 := by
        simp only [L₂, List.length_map, List.length_drop]; omega
      have hclog₁ : Nat.clog 2 L₁.length + 1 ≤ Nat.clog 2 L.length := by
        rw [Nat.clog_of_two_le (by decide) hL2]
        exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
      have hclog₂ : Nat.clog 2 (L₂.map ext₁.lift).length + 1 ≤ Nat.clog 2 L.length := by
        rw [Nat.clog_of_two_le (by decide) hL2]
        exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
      have hL₁_pos : 1 ≤ L₁.length := List.length_pos_iff.mpr hL₁_ne
      have hL₂_pos : 1 ≤ L₂.length := List.length_pos_iff.mpr hL₂_ne
      have hsumlen : L₁.length + L₂.length = L.length := by
        rw [← List.length_append, List.take_append_drop]
      refine ⟨g₂ + 1, p₃, .gate (Fin.last g₂),
        (ext₁.trans ext₂).trans (ProgExt.gate I (fun _ => 1) p₂ line),
        fun h => absurd h (List.cons_ne_nil _ _), ?_, ?_,
        fun h => absurd h (List.cons_ne_nil _ _), ?_⟩
      · intro _
        have h1 := hg₁ hL₁_ne
        have h2 := hg₂ hL₂_map_ne
        rw [List.length_map] at h2
        change g₂ + 1 ≤ g + (L.length - 1)
        omega
      · rw [Program.trace_gate_last]
        have hfun : (fun a => p₂.trace I X (line.wires a)) =
            (fun a => ![p₂.trace I X (ext₂.lift out₁), p₂.trace I X out₂] (Fin.cast hop a)) := by
          funext a
          have ha : (Fin.cast hop a).1 = 0 ∨ (Fin.cast hop a).1 = 1 := by omega
          rcases ha with h0 | h1
          · have hcast : Fin.cast hop a = 0 := Fin.ext h0
            simp only [line, hcast, Matrix.cons_val_zero]
          · have hcast : Fin.cast hop a = 1 := Fin.ext h1
            simp only [line, hcast, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        have hval : I line.op (fun a => p₂.trace I X (line.wires a)) =
            bin (p₂.trace I X (ext₂.lift out₁)) (p₂.trace I X out₂) := by
          rw [hfun]
          exact hbin ![p₂.trace I X (ext₂.lift out₁), p₂.trace I X out₂]
        rw [hval, ext₂.trace_eq, htr₁, htr₂]
        have hmap2 : (L₂.map ext₁.lift).map (p₁.trace I X) = L₂.map (p.trace I X) := by
          rw [List.map_map]
          exact List.map_congr_left fun u _ => ext₁.trace_eq X u
        rw [hmap2]
        have hsplit : L.map (p.trace I X) = L₁.map (p.trace I X) ++ L₂.map (p.trace I X) := by
          rw [← List.map_append, List.take_append_drop]
        rw [hsplit, List.foldr_append]
        have hfold : ∀ (xs : List (MvPolynomial (Fin n) K)) (y : MvPolynomial (Fin n) K),
            bin (xs.foldr bin (C e)) y = xs.foldr bin y := by
          intro xs y
          induction xs with
          | nil => simp [hlid]
          | cons a tl ihtl => simp only [List.foldr_cons, hassoc, ihtl]
        exact hfold (L₁.map (p.trace I X)) _
      · intro _
        rw [Program.wireDepths_gateWire, Program.depths_gate_last]
        refine (line_depth_le line p₂.wireDepths
          (D := D + Nat.clog 2 L.length - 1) fun a => ?_).trans (by omega)
        have ha : (Fin.cast hop a).1 = 0 ∨ (Fin.cast hop a).1 = 1 := by omega
        rcases ha with h0 | h1
        · have hcast : Fin.cast hop a = 0 := Fin.ext h0
          simp only [line, hcast, Matrix.cons_val_zero, ext₂.depth_eq]
          have := hd₁ hL₁_ne
          omega
        · have hcast : Fin.cast hop a = 1 := Fin.ext h1
          simp only [line, hcast, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          have := hd₂ hL₂_map_ne
          omega

/-- **Balanced fan-in-two compilation of unbounded-fan-in arithmetic circuits**: any
`C : SPCircuit K n` with fan-in at most `M` compiles to a fan-in-two arithmetic circuit
`c : Circuit (arithSignature K) n 1` computing the exact same polynomial with:
* `c.size ≤ C.size * (3 * M + 1)`, and
* `c.depth ≤ C.depth * (Nat.clog 2 M + 2)`. -/
theorem SPCircuit.exists_balanced_arithCircuit {K : Type u} [CommSemiring K] {n M : ℕ}
    (S : SPCircuit K n) (hM : S.FanInAtMost M) :
    ∃ c : Circuit (arithSignature K) n 1,
      c.polynomial 0 = S.polynomial ∧
      c.size ≤ S.size * (3 * M + 1) ∧
      c.depth ≤ S.depth * (Nat.clog 2 M + 2) := by
  let IA := arithInterpretationWith K (C : K → MvPolynomial (Fin n) K)
  let IS := sigmaPiInterpretationWith K (C : K → MvPolynomial (Fin n) K)
  let L := Nat.clog 2 M + 2
  have hprog : ∀ {g₀ : ℕ} (q : Program (sigmaPiSignature K) n g₀), q.FanInAtMost M →
      ∃ (g : ℕ) (p : Program (arithSignature K) n g) (φ : Wire n g₀ → Wire n g),
        g ≤ g₀ * (3 * M + 1) ∧
        (∀ w : Wire n g₀, p.trace IA X (φ w) = q.trace IS X w) ∧
        (∀ w : Wire n g₀, p.wireDepths (φ w) ≤ q.wireDepths w * L) := by
    intro g₀ q
    induction q with
    | empty =>
      intro _
      exact ⟨0, .empty, id, by simp,
        fun w => by cases w with | input _ => rfl | gate j => exact j.elim0,
        fun w => by cases w with | input _ => simp | gate j => exact j.elim0⟩
    | @gate g₀ q line ih =>
      intro hfan
      obtain ⟨g, p, φ, hg, htr, hdep⟩ := ih hfan.1
      have harity : (sigmaPiSignature K).Arity line.op ≤ M := hfan.2
      let D := Finset.univ.sup fun a => q.wireDepths (line.wires a)
      have hline_dep : line.depth q.wireDepths = D + 1 := by
        have h := line.depthWith_eq_sup 1 q.wireDepths
        simpa [Line.depthWith_one, Program.wireDepthsWith_one, D] using h
      have harg_dep : ∀ a, p.wireDepths (φ (line.wires a)) ≤ D * L := fun a =>
        (hdep (line.wires a)).trans (Nat.mul_le_mul_right L
          (Finset.le_sup (f := fun a => q.wireDepths (line.wires a)) (Finset.mem_univ a)))
      have hcompile_line :
          ∃ (g' : ℕ) (p' : Program (arithSignature K) n g') (out : Wire n g')
            (ext : ProgExt (arithSignature K) IA (fun _ => 1) p p'),
            g' ≤ g + (3 * M + 1) ∧
            p'.trace IA X out = line.eval IS X (q.eval IS X) ∧
            p'.wireDepths out ≤ (D + 1) * L := by
        rcases line with ⟨op, ws⟩
        cases op with
        | const a =>
          let ln : Line (arithSignature K) n g := ⟨.const a, Fin.elim0⟩
          refine ⟨g + 1, p.gate ln, .gate (Fin.last g), ProgExt.gate IA (fun _ => 1) p ln,
            by omega, ?_, ?_⟩
          · rw [Program.trace_gate_last]; rfl
          · rw [Program.wireDepths_gateWire, Program.depths_gate_last]
            exact (line_depth_le ln p.wireDepths (D := 0) fun b => b.elim0).trans
              (by dsimp [L]; nlinarith)
        | mul m =>
          have hmM : m ≤ M := harity
          let wList : List (Wire n g) := List.ofFn fun a : Fin m => φ (ws a)
          obtain ⟨g', p', out, ext, hg0', hgne', htr', hd0, hdne⟩ :=
            arithPushBalancedFold (K := K) .mul rfl (1 : K) (· * ·)
              (fun _ => rfl) mul_assoc (fun a => by rw [map_one, one_mul])
              (fun a => by rw [map_one, mul_one]) p wList
              (fun w hw => by
                rcases List.mem_ofFn.mp hw with ⟨a, rfl⟩
                exact harg_dep a)
          refine ⟨g', p', out, ext, ?_, ?_, ?_⟩
          · have hlen : wList.length = m := List.length_ofFn
            by_cases hnil : wList = []
            · exact (hg0' hnil).trans (by omega)
            · exact (hgne' hnil).trans (by omega)
          · rw [htr']
            change ((List.ofFn fun a : Fin m => φ (ws a)).map (p.trace IA X)).foldr (· * ·) (C 1) =
              ∏ a : Fin m, q.trace IS X (ws a)
            rw [map_one, List.map_ofFn, ← List.prod_eq_foldr, List.prod_ofFn]
            exact Finset.prod_congr rfl fun a _ => htr (ws a)
          · by_cases hm0 : m = 0
            · have hnil : wList = [] := List.eq_nil_of_length_eq_zero (by simp [wList, hm0])
              exact (hd0 hnil).trans (by dsimp [L]; nlinarith)
            · have hne : wList ≠ [] := by
                intro hnil
                have hlen0 := congrArg List.length hnil
                simp only [wList, List.length_ofFn, List.length_nil] at hlen0
                exact hm0 hlen0
              have hcl : Nat.clog 2 wList.length ≤ Nat.clog 2 M := by
                rw [show wList.length = m from List.length_ofFn]
                exact Nat.clog_mono_right 2 hmM
              have h1 := hdne hne
              dsimp only [L] at h1 ⊢
              nlinarith
        | add m coeff =>
          have hmM : m ≤ M := harity
          -- Push `m` scalar-multiplied wires `C (coeff a) * φ (ws a)` (`2 * m` gates, depth `+2`).
          have hscale : ∀ (k : ℕ) (hk : k ≤ m),
              ∃ (g₁ : ℕ) (p₁ : Program (arithSignature K) n g₁) (sws : List (Wire n g₁))
                (ext₁ : ProgExt (arithSignature K) IA (fun _ => 1) p p₁),
                g₁ = g + 2 * k ∧
                sws.length = k ∧
                sws.map (p₁.trace IA X) =
                  List.ofFn (fun a : Fin k =>
                    C (coeff ⟨a.1, a.2.trans_le hk⟩) * q.trace IS X (ws ⟨a.1, a.2.trans_le hk⟩)) ∧
                ∀ w ∈ sws, p₁.wireDepths w ≤ D * L + 2 := by
            intro k
            induction k with
            | zero =>
              intro _
              exact ⟨g, p, [], ProgExt.refl p, by simp, rfl, rfl,
                fun _ h => absurd h (List.not_mem_nil)⟩
            | succ k ihk =>
              intro hk
              obtain ⟨g₁, p₁, sws, ext₁, hg₁, hlen₁, hmap₁, hwd₁⟩ := ihk (Nat.le_of_succ_le hk)
              let aL : Fin m := ⟨k, hk⟩
              let cLine : Line (arithSignature K) n g₁ := ⟨.const (coeff aL), Fin.elim0⟩
              let p₂ := p₁.gate cLine
              let mLine : Line (arithSignature K) n (g₁ + 1) :=
                ⟨.mul, ![.gate (Fin.last g₁), (ext₁.lift (φ (ws aL))).castSucc]⟩
              let p₃ := p₂.gate mLine
              let ext₂ : ProgExt (arithSignature K) IA (fun _ => 1) p₁ p₃ :=
                (ProgExt.gate IA (fun _ => 1) p₁ cLine).trans
                  (ProgExt.gate IA (fun _ => 1) p₂ mLine)
              let wNew : Wire n (g₁ + 2) := .gate (Fin.last (g₁ + 1))
              have htr_new : p₃.trace IA X wNew = C (coeff aL) * q.trace IS X (ws aL) := by
                rw [Program.trace_gate_last]
                have hc_tr : p₂.trace IA X (.gate (Fin.last g₁)) = C (coeff aL) := by
                  rw [Program.trace_gate_last]; rfl
                simp only [IA, mLine, arithInterpretationWith_mul, Matrix.cons_val_zero,
                  Matrix.cons_val_one, Matrix.cons_val_fin_one, hc_tr, p₂,
                  Program.trace_gate_castSucc, ext₁.trace_eq, htr]
              have hd_c : p₂.wireDepths (.gate (Fin.last g₁)) ≤ 1 := by
                rw [Program.wireDepths_gateWire, Program.depths_gate_last]
                exact line_depth_le cLine p₁.wireDepths (D := 0) fun b => b.elim0
              have hd_new : p₃.wireDepths wNew ≤ D * L + 2 := by
                rw [Program.wireDepths_gateWire, Program.depths_gate_last]
                refine (line_depth_le mLine p₂.wireDepths (D := D * L + 1) fun b => ?_).trans
                  (by omega)
                fin_cases b
                · exact hd_c.trans (by omega)
                · simpa [mLine, p₂, Program.wireDepths_gate_castSucc, ext₁.depth_eq] using
                    (harg_dep aL).trans (Nat.le_succ _)
              refine ⟨g₁ + 2, p₃, sws.map ext₂.lift ++ [wNew], ext₁.trans ext₂,
                by omega, by simp [hlen₁], ?_, ?_⟩
              · rw [List.map_append, List.map_map, List.map_singleton, htr_new]
                have hcomp : (p₃.trace IA X ∘ ext₂.lift) = p₁.trace IA X :=
                  funext fun w => ext₂.trace_eq X w
                rw [hcomp, hmap₁, List.ofFn_succ', List.concat_eq_append]
                rfl
              · intro w hw
                rcases List.mem_append.mp hw with hmem | hsing
                · rcases List.mem_map.mp hmem with ⟨u, hu, rfl⟩
                  rw [ext₂.depth_eq]
                  exact hwd₁ u hu
                · rw [List.mem_singleton.mp hsing]
                  exact hd_new
          obtain ⟨g₁, p₁, sws, ext₁, hg₁, hlen₁, hmap₁, hwd₁⟩ := hscale m le_rfl
          obtain ⟨g₂, p₂, out, ext₂, hg0₂, hgne₂, htr₂, hd0, hdne⟩ :=
            arithPushBalancedFold (K := K) .add rfl (0 : K) (· + ·)
              (fun _ => rfl) add_assoc (fun a => by rw [map_zero, zero_add])
              (fun a => by rw [map_zero, add_zero]) p₁ sws hwd₁
          refine ⟨g₂, p₂, out, ext₁.trans ext₂, ?_, ?_, ?_⟩
          · by_cases hnil : sws = []
            · exact (hg0₂ hnil).trans (by omega)
            · exact (hgne₂ hnil).trans (by omega)
          · rw [htr₂, hmap₁, map_zero, ← List.sum_eq_foldr, List.sum_ofFn]
            rfl
          · by_cases hm0 : m = 0
            · have hnil : sws = [] := List.eq_nil_of_length_eq_zero (by omega)
              exact (hd0 hnil).trans (by dsimp [L]; nlinarith)
            · have hne : sws ≠ [] := by
                intro hnil
                have h0 := congrArg List.length hnil
                rw [hlen₁, List.length_nil] at h0
                exact hm0 h0
              have hcl : Nat.clog 2 sws.length ≤ Nat.clog 2 M := by
                rw [hlen₁]
                exact Nat.clog_mono_right 2 hmM
              have h1 := hdne hne
              dsimp only [L] at h1 ⊢
              nlinarith
      obtain ⟨g', p', out, ext, hg', hout_tr, hout_dep⟩ := hcompile_line
      refine ⟨g', p', Wire.lastCases out (fun w => ext.lift (φ w)), ?_, ?_, ?_⟩
      · calc
          g' ≤ g + (3 * M + 1) := hg'
          _ ≤ g₀ * (3 * M + 1) + (3 * M + 1) := Nat.add_le_add_right hg _
          _ = (g₀ + 1) * (3 * M + 1) := by ring
      · intro w
        induction w using Wire.lastCases with
        | last =>
          simpa only [Wire.lastCases, Fin.lastCases_last, Program.trace_gateWire,
            Program.gateFunction_gate_last] using hout_tr
        | castSucc w =>
          rw [Program.trace_gate_castSucc]
          cases w with
          | input i =>
            simpa only [Wire.castSucc, Wire.lastCases, ext.trace_eq] using htr (.input i)
          | gate j =>
            simpa only [Wire.castSucc, Wire.lastCases, Fin.lastCases_castSucc, ext.trace_eq]
              using htr (.gate j)
      · intro w
        induction w using Wire.lastCases with
        | last =>
          simpa only [Wire.lastCases, Fin.lastCases_last, Program.wireDepths_gateWire,
            Program.depths_gate_last, hline_dep] using hout_dep
        | castSucc w =>
          rw [Program.wireDepths_gate_castSucc]
          cases w with
          | input i =>
            simpa only [Wire.castSucc, Wire.lastCases, ext.depth_eq] using hdep (.input i)
          | gate j =>
            simpa only [Wire.castSucc, Wire.lastCases, Fin.lastCases_castSucc, ext.depth_eq]
              using hdep (.gate j)
  obtain ⟨g, p, φ, hg, htr, hdep⟩ := hprog S.program hM
  refine ⟨⟨p, fun _ => φ (S.outputs 0)⟩, htr (S.outputs 0), hg, ?_⟩
  rw [Circuit.depth_le_iff]
  intro j
  fin_cases j
  exact (hdep (S.outputs 0)).trans (Nat.mul_le_mul_right L (S.outputDepths_le_depth 0))

/-- **VSBR depth reduction for `VP` (logarithmic-depth `SPCircuit`)**: every family `f ∈ VP K`
admits a polynomially bounded size `SPCircuit` family computing `f.poly n` with depth
`O(log (n + 2))` and product-depth `O(log (n + 2))`. -/
theorem VP.exists_log_depth_spCircuit {K : Type u} [CommSemiring K] {f : PolynomialFamily K}
    (hf : f ∈ VP K) :
    ∃ (C : ∀ n, SPCircuit K (f.vars n)) (cDepth : ℕ),
      PolynomiallyBounded (fun n => (C n).size) ∧
      (∀ n, (C n).polynomial = f.poly n) ∧
      (∀ n, (C n).depth ≤ cDepth * (Nat.log 2 (n + 2) + 1)) ∧
      (∀ n, (C n).productDepth ≤ cDepth * (Nat.log 2 (n + 2) + 1)) := by
  obtain ⟨⟨hvars, hdeg⟩, c, hcsize, hcpoly⟩ := hf
  choose C hCpoly hCdep hCpdep _ hCsize using
    fun n => exists_spCircuit_log_depth (c n) (d := (f.poly n).totalDegree)
      (by rw [hcpoly n])
  obtain ⟨cd, ed, hdeg_le⟩ := polynomiallyBounded_iff_le.mp hdeg
  have hlog_bound : ∀ n, Nat.clog 2 (max 1 (f.poly n).totalDegree) ≤
      (cd + ed + 2) * (Nat.log 2 (n + 2) + 1) := by
    intro n
    have hpow : max 1 (f.poly n).totalDegree ≤ 2 ^ ((cd + ed + 2) * (Nat.log 2 (n + 2) + 1)) := by
      have hn2 : n + 1 ≤ 2 ^ (Nat.log 2 (n + 2) + 1) :=
        (Nat.le_succ (n + 1)).trans (Nat.lt_pow_succ_log_self (by decide) (n + 2)).le
      have hcd : cd ≤ 2 ^ cd := Nat.le_of_lt Nat.lt_two_pow_self
      have h1 : 1 ≤ 2 ^ ((cd + ed + 2) * (Nat.log 2 (n + 2) + 1)) := Nat.one_le_two_pow
      refine max_le h1 ((hdeg_le n).trans ?_)
      calc
        cd * (n + 1) ^ ed ≤ 2 ^ cd * (2 ^ (Nat.log 2 (n + 2) + 1)) ^ ed :=
          Nat.mul_le_mul hcd (Nat.pow_le_pow_left hn2 ed)
        _ = 2 ^ (cd + ed * (Nat.log 2 (n + 2) + 1)) := by
          rw [← pow_mul, ← pow_add, mul_comm ed]
        _ ≤ 2 ^ ((cd + ed + 2) * (Nat.log 2 (n + 2) + 1)) := by
          refine Nat.pow_le_pow_right (by decide) ?_
          nlinarith
    exact Nat.clog_le_of_le_pow hpow
  refine ⟨C, 5 * (cd + ed + 2) + 2, ?_, fun n => (hCpoly n).trans (hcpoly n), fun n => ?_,
    fun n => ?_⟩
  · have hD : PolynomiallyBounded (fun n => max 1 (f.poly n).totalDegree) :=
      (PolynomiallyBounded.const 1).max hdeg
    have hS : PolynomiallyBounded
        (fun n => 2 * (f.vars n + (c n).size) * (max 1 (f.poly n).totalDegree) ^ 2) :=
      ((PolynomiallyBounded.const 2).mul (hvars.add hcsize)).mul (hD.pow 2)
    have hR : PolynomiallyBounded (fun n => Nat.clog 2 (max 1 (f.poly n).totalDegree)) :=
      hD.mono_of_le fun n => Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    have htot : PolynomiallyBounded (fun n =>
        (2 * (f.vars n + (c n).size) * (max 1 (f.poly n).totalDegree) ^ 2 +
          (max 1 (f.poly n).totalDegree + 1) *
            (2 * (f.vars n + (c n).size) * (max 1 (f.poly n).totalDegree) ^ 2) ^ 2) *
          (1 + Nat.clog 2 (max 1 (f.poly n).totalDegree) *
            (2 * (2 * (f.vars n + (c n).size) * (max 1 (f.poly n).totalDegree) ^ 2) + 1)) + 2) :=
      ((hS.add ((hD.add (PolynomiallyBounded.const 1)).mul (hS.pow 2))).mul
        ((PolynomiallyBounded.const 1).add
          (hR.mul (((PolynomiallyBounded.const 2).mul hS).add (PolynomiallyBounded.const 1))))).add
        (PolynomiallyBounded.const 2)
    exact htot.mono_of_le hCsize
  · have hl := hlog_bound n
    have hd := hCdep n
    nlinarith
  · have hl := hlog_bound n
    have hp := hCpdep n
    nlinarith

/-- **VSBR depth reduction for `VP` (polylogarithmic-depth fan-in-two circuits, `VP ⊆ VNC²`)**:
every family `f ∈ VP K` is computed by fan-in-two arithmetic circuits `c n` of polynomially
bounded size and depth `O((log (n + 2)) ^ 2)`. -/
theorem VP.exists_logSq_depth_circuit {K : Type u} [CommSemiring K] {f : PolynomialFamily K}
    (hf : f ∈ VP K) :
    ∃ (c : ∀ n, Circuit (arithSignature K) (f.vars n) 1) (cDepth : ℕ),
      PolynomiallyBounded (fun n => (c n).size) ∧
      (∀ n, (c n).polynomial 0 = f.poly n) ∧
      (∀ n, (c n).depth ≤ cDepth * (Nat.log 2 (n + 2) + 1) ^ 2) := by
  obtain ⟨⟨hvars, hdeg⟩, c0, hc0size, hc0poly⟩ := hf
  choose C hCpoly hCdep _ hCfan hCsize using
    fun n => exists_spCircuit_log_depth (c0 n) (d := (f.poly n).totalDegree)
      (by rw [hc0poly n])
  choose cb hcb_poly hcb_size hcb_dep using
    fun n => (C n).exists_balanced_arithCircuit (hCfan n)
  let Mfn (n : ℕ) : ℕ :=
    max 2 (max (f.vars n) (max ((f.poly n).totalDegree + 1)
      (2 * (f.vars n + (c0 n).size) * (max 1 (f.poly n).totalDegree) ^ 2)))
  have hD : PolynomiallyBounded (fun n => max 1 (f.poly n).totalDegree) :=
    (PolynomiallyBounded.const 1).max hdeg
  have hS : PolynomiallyBounded
      (fun n => 2 * (f.vars n + (c0 n).size) * (max 1 (f.poly n).totalDegree) ^ 2) :=
    ((PolynomiallyBounded.const 2).mul (hvars.add hc0size)).mul (hD.pow 2)
  have hMpoly : PolynomiallyBounded Mfn :=
    (PolynomiallyBounded.const 2).max
      (hvars.max ((hdeg.add (PolynomiallyBounded.const 1)).max hS))
  obtain ⟨cm, em, hMle⟩ := polynomiallyBounded_iff_le.mp hMpoly
  obtain ⟨cd, ed, hdeg_le⟩ := polynomiallyBounded_iff_le.mp hdeg
  have hclog_poly : ∀ (a b n : ℕ),
      a * (n + 1) ^ b ≤ 2 ^ ((a + b + 2) * (Nat.log 2 (n + 2) + 1)) := by
    intro a b n
    have hn2 : n + 1 ≤ 2 ^ (Nat.log 2 (n + 2) + 1) :=
      (Nat.le_succ (n + 1)).trans (Nat.lt_pow_succ_log_self (by decide) (n + 2)).le
    have ha : a ≤ 2 ^ a := Nat.le_of_lt Nat.lt_two_pow_self
    calc
      a * (n + 1) ^ b ≤ 2 ^ a * (2 ^ (Nat.log 2 (n + 2) + 1)) ^ b :=
        Nat.mul_le_mul ha (Nat.pow_le_pow_left hn2 b)
      _ = 2 ^ (a + b * (Nat.log 2 (n + 2) + 1)) := by rw [← pow_mul, ← pow_add, mul_comm b]
      _ ≤ 2 ^ ((a + b + 2) * (Nat.log 2 (n + 2) + 1)) :=
        Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hCsize_poly : PolynomiallyBounded (fun n => (C n).size) := by
    have hR : PolynomiallyBounded (fun n => Nat.clog 2 (max 1 (f.poly n).totalDegree)) :=
      hD.mono_of_le fun n => Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    have htot : PolynomiallyBounded (fun n =>
        (2 * (f.vars n + (c0 n).size) * (max 1 (f.poly n).totalDegree) ^ 2 +
          (max 1 (f.poly n).totalDegree + 1) *
            (2 * (f.vars n + (c0 n).size) * (max 1 (f.poly n).totalDegree) ^ 2) ^ 2) *
          (1 + Nat.clog 2 (max 1 (f.poly n).totalDegree) *
            (2 * (2 * (f.vars n + (c0 n).size) * (max 1 (f.poly n).totalDegree) ^ 2) + 1)) + 2) :=
      ((hS.add ((hD.add (PolynomiallyBounded.const 1)).mul (hS.pow 2))).mul
        ((PolynomiallyBounded.const 1).add
          (hR.mul (((PolynomiallyBounded.const 2).mul hS).add (PolynomiallyBounded.const 1))))).add
        (PolynomiallyBounded.const 2)
    exact htot.mono_of_le hCsize
  refine ⟨cb, (5 * (cd + ed + 2) + 2) * (cm + em + 4),
    (hCsize_poly.mul
      (((PolynomiallyBounded.const 3).mul hMpoly).add (PolynomiallyBounded.const 1))).mono_of_le
      hcb_size,
    fun n => (hcb_poly n).trans ((hCpoly n).trans (hc0poly n)), fun n => ?_⟩
  have hL_M : Nat.clog 2 (Mfn n) ≤ (cm + em + 2) * (Nat.log 2 (n + 2) + 1) :=
    Nat.clog_le_of_le_pow ((hMle n).trans (hclog_poly cm em n))
  have hL_D : Nat.clog 2 (max 1 (f.poly n).totalDegree) ≤
      (cd + ed + 2) * (Nat.log 2 (n + 2) + 1) :=
    Nat.clog_le_of_le_pow (max_le Nat.one_le_two_pow ((hdeg_le n).trans (hclog_poly cd ed n)))
  have h1 : (C n).depth ≤ (5 * (cd + ed + 2) + 2) * (Nat.log 2 (n + 2) + 1) := by
    have := hCdep n; nlinarith
  have h2 : Nat.clog 2 (Mfn n) + 2 ≤ (cm + em + 4) * (Nat.log 2 (n + 2) + 1) := by nlinarith
  calc
    (cb n).depth ≤ (C n).depth * (Nat.clog 2 (Mfn n) + 2) := hcb_dep n
    _ ≤ ((5 * (cd + ed + 2) + 2) * (Nat.log 2 (n + 2) + 1)) *
        ((cm + em + 4) * (Nat.log 2 (n + 2) + 1)) := Nat.mul_le_mul h1 h2
    _ = (5 * (cd + ed + 2) + 2) * (cm + em + 4) * (Nat.log 2 (n + 2) + 1) ^ 2 := by ring

/-! ### : The depth-four chasm theorem and `VP` vs. `VNP` separation -/

/-- Ceiling integer division `⌈a / b⌉ = (a + b - 1) / b` for `1 ≤ b`. -/
def ceilDiv (a b : ℕ) : ℕ :=
  (a + b - 1) / b

/-- For `1 ≤ a` and `1 ≤ b`, `1 ≤ ceilDiv a b`. -/
theorem one_le_ceilDiv {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ ceilDiv a b := by
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le hb).mpr (by omega)

/-- For `1 ≤ b`, `a ≤ ceilDiv a b * b`. -/
theorem le_ceilDiv_mul {a b : ℕ} (hb : 1 ≤ b) :
    a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have hdiv := Nat.div_add_mod (a + b - 1) b
  have hmod : (a + b - 1) % b < b := Nat.mod_lt _ hb
  have hmul : b * ((a + b - 1) / b) = ((a + b - 1) / b) * b := Nat.mul_comm _ _
  omega

/-- If `a ≤ k * b` with `1 ≤ b`, then `ceilDiv a b ≤ k`. -/
theorem ceilDiv_le_of_le_mul {a b k : ℕ} (hb : 1 ≤ b) (hle : a ≤ k * b) :
    ceilDiv a b ≤ k := by
  unfold ceilDiv
  have hlt : a + b - 1 < (k + 1) * b := by
    rw [Nat.add_one_mul]
    omega
  have hlt_div : (a + b - 1) / b < k + 1 := (Nat.div_lt_iff_lt_mul hb).mpr hlt
  omega

/-- Monotonicity of `ceilDiv` in the numerator. -/
theorem ceilDiv_mono_left {a₁ a₂ b : ℕ} (hle : a₁ ≤ a₂) :
    ceilDiv a₁ b ≤ ceilDiv a₂ b :=
  Nat.div_le_div_right (by omega)

/-- For `1 ≤ t`, `ceilDiv d t ≤ d`. -/
theorem ceilDiv_le_self {d t : ℕ} (ht : 1 ≤ t) :
    ceilDiv d t ≤ d :=
  ceilDiv_le_of_le_mul ht (Nat.le_mul_of_pos_right d ht)

/-- Universal non-divisibility bound: for all `1 ≤ d` and `1 ≤ t`,
`ceilDiv (2 * d) (ceilDiv d t) ≤ 2 * t`. -/
theorem ceilDiv_two_mul_ceilDiv_le {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) :
    ceilDiv (2 * d) (ceilDiv d t) ≤ 2 * t := by
  have hτ : 1 ≤ ceilDiv d t := one_le_ceilDiv hd ht
  have hd_le : d ≤ ceilDiv d t * t := le_ceilDiv_mul ht
  refine ceilDiv_le_of_le_mul hτ ?_
  calc
    2 * d ≤ 2 * (ceilDiv d t * t) := Nat.mul_le_mul_left 2 hd_le
    _ = (2 * t) * ceilDiv d t := by ring

/-- Key exponent inequality for the `m = Δ - τ` frontier recursion:
`(2 * d) / (ceilDiv d t + 1) ≤ 2 * t`. -/
theorem two_mul_div_succ_ceilDiv_le {d t : ℕ} (ht : 1 ≤ t) :
    (2 * d) / (ceilDiv d t + 1) ≤ 2 * t := by
  have hd_le : d ≤ ceilDiv d t * t := le_ceilDiv_mul ht
  have hlt : 2 * d < (2 * t) * (ceilDiv d t + 1) := by
    calc
      2 * d ≤ 2 * (ceilDiv d t * t) := Nat.mul_le_mul_left 2 hd_le
      _ = 2 * t * ceilDiv d t := by ring
      _ < 2 * t * ceilDiv d t + 2 * t := by omega
      _ = (2 * t) * (ceilDiv d t + 1) := by ring
  exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul (by omega)).mpr hlt)

/-- Sharp square-root parameter bound: `ceilDiv d (max 1 (Nat.sqrt d)) ≤ Nat.sqrt d + 2`. -/
theorem ceilDiv_sqrt_le (d : ℕ) :
    ceilDiv d (max 1 (Nat.sqrt d)) ≤ Nat.sqrt d + 2 := by
  by_cases hd0 : d = 0
  · subst hd0
    simp [ceilDiv]
  · have hpos : 0 < Nat.sqrt d := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hd0)
    have hmax : max 1 (Nat.sqrt d) = Nat.sqrt d := max_eq_right hpos
    rw [hmax]
    refine ceilDiv_le_of_le_mul hpos ?_
    have hlt : d < (Nat.sqrt d + 1) * (Nat.sqrt d + 1) := Nat.lt_succ_sqrt d
    nlinarith

/-- Predicate asserting that every adjacent pair in `items` has degree sum strictly greater than
`τ`. -/
private def AdjacentSumGt {α : Type*} (τ : ℕ) : List (ℕ × α) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => τ < a.1 + b.1 ∧ AdjacentSumGt τ (b :: rest)

private def lastFst {α : Type*} (x : ℕ × α) : List (ℕ × α) → ℕ
  | [] => x.1
  | y :: tl => lastFst y tl

private lemma one_le_lastFst {α : Type*} :
    ∀ (x : ℕ × α) (xs : List (ℕ × α)),
      1 ≤ x.1 → (∀ q ∈ xs, 1 ≤ q.1) → 1 ≤ lastFst x xs
  | _, [], hx, _ => hx
  | _, y :: tl, _, hxs =>
    one_le_lastFst y tl (hxs y List.mem_cons_self)
      (fun q hq => hxs q (List.mem_cons_of_mem _ hq))

private lemma adjacentSumGt_two_mul_sum_ge {α : Type*} (τ : ℕ) :
    ∀ (x : ℕ × α) (xs : List (ℕ × α)),
      AdjacentSumGt τ (x :: xs) →
      xs.length * (τ + 1) + x.1 + lastFst x xs ≤ 2 * ((x :: xs).map Prod.fst).sum
  | x, [], _ => by simp [lastFst]; omega
  | x, y :: tl, ⟨hxy, hadj⟩ => by
    have ih := adjacentSumGt_two_mul_sum_ge τ y tl hadj
    simp only [List.length_cons, List.map_cons, List.sum_cons, lastFst] at ih ⊢
    rw [Nat.add_one_mul]
    omega

/-- Any nonempty list of positive-degree items satisfying `AdjacentSumGt τ` has length at most
`ceilDiv (2 * (items.map Prod.fst).sum) τ`. -/
private theorem length_le_ceilDiv_of_adjacentSumGt {α : Type*} {τ : ℕ} (hτ : 1 ≤ τ) :
    ∀ {items : List (ℕ × α)},
      items ≠ [] →
      (∀ q ∈ items, 1 ≤ q.1) →
      AdjacentSumGt τ items →
      items.length ≤ ceilDiv (2 * (items.map Prod.fst).sum) τ
  | [], hne, _, _ => False.elim (hne rfl)
  | x :: xs, _, hpos, hadj => by
    have hx1 : 1 ≤ x.1 := hpos x List.mem_cons_self
    have hlast1 : 1 ≤ lastFst x xs :=
      one_le_lastFst x xs hx1 (fun q hq => hpos q (List.mem_cons_of_mem _ hq))
    have hsum := adjacentSumGt_two_mul_sum_ge τ x xs hadj
    set d := ((x :: xs).map Prod.fst).sum
    have hlen_mul : xs.length * τ ≤ xs.length * (τ + 1) :=
      Nat.mul_le_mul_left xs.length (by omega)
    have hbound : (xs.length + 1) * τ ≤ 2 * d + τ - 1 := by
      rw [Nat.add_one_mul]
      omega
    unfold ceilDiv
    simp only [List.length_cons]
    exact (Nat.le_div_iff_mul_le hτ).mpr hbound

/-- Greedy adjacent factor merger: merges adjacent pairs `(d₁, P₁), (d₂, P₂)` whenever
`d₁ + d₂ ≤ τ`, preserving product, degree sum, and homogeneity of each factor. -/
private noncomputable def mergeHomogItems {K : Type u} [CommSemiring K] {σ : Type*} (τ : ℕ) :
    List (ℕ × MvPolynomial σ K) → List (ℕ × MvPolynomial σ K)
  | [] => []
  | [x] => [x]
  | (d₁, P₁) :: (d₂, P₂) :: rest =>
    if d₁ + d₂ ≤ τ then
      mergeHomogItems τ ((d₁ + d₂, P₁ * P₂) :: rest)
    else
      (d₁, P₁) :: mergeHomogItems τ ((d₂, P₂) :: rest)
termination_by items => items.length

private lemma mergeHomogItems_cons_nonempty {K : Type u} [CommSemiring K] {σ : Type*} (τ : ℕ)
    (x : ℕ × MvPolynomial σ K) (xs : List (ℕ × MvPolynomial σ K)) :
    ∃ (h : ℕ × MvPolynomial σ K) (outTl : List (ℕ × MvPolynomial σ K)),
      mergeHomogItems τ (x :: xs) = h :: outTl ∧ x.1 ≤ h.1 := by
  induction hn : xs.length using Nat.strongRecOn generalizing x xs with
  | ind k ih =>
    subst hn
    cases xs with
    | nil => exact ⟨x, [], by rw [mergeHomogItems], le_rfl⟩
    | cons y rest =>
      rcases x with ⟨d₁, P₁⟩
      rcases y with ⟨d₂, P₂⟩
      rw [mergeHomogItems]
      split_ifs with hle
      · obtain ⟨h, outTl, heq, hh⟩ :=
          ih rest.length (Nat.lt_succ_self _) (d₁ + d₂, P₁ * P₂) rest rfl
        exact ⟨h, outTl, heq, by omega⟩
      · exact ⟨(d₁, P₁), mergeHomogItems τ ((d₂, P₂) :: rest), rfl, le_rfl⟩

/-- Master invariant for `mergeHomogItems τ`: preserves product, degree sum, nonemptiness,
degree bounds `1 ≤ q.1 ≤ τ`, homogeneity `(q.2).IsHomogeneous q.1`, and establishes
`AdjacentSumGt τ`. -/
private theorem mergeHomogItems_spec {K : Type u} [CommSemiring K] {σ : Type*} (τ : ℕ)
    (items : List (ℕ × MvPolynomial σ K))
    (hpos : ∀ q ∈ items, 1 ≤ q.1 ∧ q.1 ≤ τ)
    (hhom : ∀ q ∈ items, q.2.IsHomogeneous q.1) :
    let out := mergeHomogItems τ items
    (out.map Prod.snd).prod = (items.map Prod.snd).prod ∧
    (out.map Prod.fst).sum = (items.map Prod.fst).sum ∧
    (items ≠ [] → out ≠ []) ∧
    (∀ q ∈ out, 1 ≤ q.1 ∧ q.1 ≤ τ) ∧
    (∀ q ∈ out, q.2.IsHomogeneous q.1) ∧
    AdjacentSumGt τ out := by
  induction hn : items.length using Nat.strongRecOn generalizing items with
  | ind k ih =>
    subst hn
    cases items with
    | nil =>
      simp [mergeHomogItems, AdjacentSumGt]
    | cons x xs =>
      cases xs with
      | nil =>
        simp only [mergeHomogItems, List.map_cons, List.map_nil, ne_eq, reduceCtorEq,
          not_false_eq_true, imp_self, List.mem_singleton, forall_eq, AdjacentSumGt, true_and,
          and_true]
        exact ⟨hpos x List.mem_cons_self, hhom x List.mem_cons_self⟩
      | cons y rest =>
        rcases x with ⟨d₁, P₁⟩
        rcases y with ⟨d₂, P₂⟩
        have hd₁ := hpos (d₁, P₁) List.mem_cons_self
        have hd₂ := hpos (d₂, P₂) (List.mem_cons_of_mem _ List.mem_cons_self)
        have hh₁ := hhom (d₁, P₁) List.mem_cons_self
        have hh₂ := hhom (d₂, P₂) (List.mem_cons_of_mem _ List.mem_cons_self)
        dsimp only
        rw [mergeHomogItems]
        split_ifs with hle
        · have hpos' : ∀ q ∈ ((d₁ + d₂, P₁ * P₂) :: rest), 1 ≤ q.1 ∧ q.1 ≤ τ := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hrest
            · exact ⟨by omega, hle⟩
            · exact hpos q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest))
          have hhom' : ∀ q ∈ ((d₁ + d₂, P₁ * P₂) :: rest), q.2.IsHomogeneous q.1 := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hrest
            · exact hh₁.mul hh₂
            · exact hhom q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest))
          rcases ih (rest.length + 1) (by simp) ((d₁ + d₂, P₁ * P₂) :: rest) hpos' hhom' rfl with
            ⟨hprod, hsum, hne, hout_pos, hout_hom, hadj⟩
          refine ⟨?_, ?_, fun _ => hne (List.cons_ne_nil _ _), hout_pos, hout_hom, hadj⟩
          · rw [hprod]; simp [mul_assoc]
          · rw [hsum]; simp [add_assoc]
        · have hpos' : ∀ q ∈ ((d₂, P₂) :: rest), 1 ≤ q.1 ∧ q.1 ≤ τ :=
            fun q hq => hpos q (List.mem_cons_of_mem _ hq)
          have hhom' : ∀ q ∈ ((d₂, P₂) :: rest), q.2.IsHomogeneous q.1 :=
            fun q hq => hhom q (List.mem_cons_of_mem _ hq)
          rcases ih (rest.length + 1) (by simp) ((d₂, P₂) :: rest) hpos' hhom' rfl with
            ⟨hprod, hsum, _, hout_pos, hout_hom, hadj⟩
          obtain ⟨h_hd, outTl, heq_hd, hd₂_le⟩ :=
            mergeHomogItems_cons_nonempty τ (d₂, P₂) rest
          refine ⟨?_, ?_, fun _ => List.cons_ne_nil _ _, ?_, ?_, ?_⟩
          · simp [hprod]
          · simp [hsum]
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | htl
            · exact hd₁
            · exact hout_pos q htl
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | htl
            · exact hh₁
            · exact hout_hom q htl
          · rw [heq_hd] at hadj ⊢
            exact ⟨by omega, hadj⟩

/-- Recursion-tree exponent for the `m = Δ - τ` frontier expansion, avoiding any `log Δ`
overhead in the exponent. -/
def frontierExp (τ Δ : ℕ) : ℕ :=
  if Δ ≤ τ then 0 else (2 * Δ) / (τ + 1) - 1

/-- Additive step inequality for `frontierExp` across a frontier multiplication gate with child
degrees `p, q ≤ Δ - τ` and `p + q ≤ Δ`. -/
theorem frontierExp_step_le {τ Δ p q : ℕ} (hτ : 1 ≤ τ) (hΔ : τ < Δ)
    (hpm : p ≤ Δ - τ) (hqm : q ≤ Δ - τ) (hpq : p + q ≤ Δ) :
    1 + frontierExp τ p + frontierExp τ q ≤ frontierExp τ Δ := by
  let K := τ + 1
  have hK_pos : 0 < K := by dsimp [K]; omega
  unfold frontierExp
  rw [ite_eq_right (by omega : ¬ Δ ≤ τ)]
  change 1 + (if p ≤ τ then 0 else (2 * p) / K - 1) +
    (if q ≤ τ then 0 else (2 * q) / K - 1) ≤ (2 * Δ) / K - 1
  have hΔ_div2 : 2 ≤ (2 * Δ) / K :=
    (Nat.le_div_iff_mul_le hK_pos).mpr (by dsimp [K]; omega)
  by_cases hpτ : p ≤ τ <;> by_cases hqτ : q ≤ τ
  · rw [ite_eq_left hpτ, ite_eq_left hqτ]; omega
  · rw [ite_eq_left hpτ, ite_eq_right hqτ]
    have hq_div2 : 2 ≤ (2 * q) / K :=
      (Nat.le_div_iff_mul_le hK_pos).mpr (by dsimp [K]; omega)
    have hstep : (2 * q) / K + 1 ≤ (2 * Δ) / K := by
      have h1 : (2 * q + K) / K = (2 * q) / K + 1 := Nat.add_div_right (2 * q) hK_pos
      rw [← h1]
      exact Nat.div_le_div_right (by dsimp [K]; omega)
    omega
  · rw [ite_eq_right hpτ, ite_eq_left hqτ]
    have hp_div2 : 2 ≤ (2 * p) / K :=
      (Nat.le_div_iff_mul_le hK_pos).mpr (by dsimp [K]; omega)
    have hstep : (2 * p) / K + 1 ≤ (2 * Δ) / K := by
      have h1 : (2 * p + K) / K = (2 * p) / K + 1 := Nat.add_div_right (2 * p) hK_pos
      rw [← h1]
      exact Nat.div_le_div_right (by dsimp [K]; omega)
    omega
  · rw [ite_eq_right hpτ, ite_eq_right hqτ]
    have hp_div2 : 2 ≤ (2 * p) / K :=
      (Nat.le_div_iff_mul_le hK_pos).mpr (by dsimp [K]; omega)
    have hq_div2 : 2 ≤ (2 * q) / K :=
      (Nat.le_div_iff_mul_le hK_pos).mpr (by dsimp [K]; omega)
    have hsum_div : (2 * p) / K + (2 * q) / K ≤ (2 * Δ) / K := by
      refine (Nat.le_div_iff_mul_le hK_pos).mpr ?_
      have h1 : ((2 * p) / K) * K ≤ 2 * p := Nat.div_mul_le_self (2 * p) K
      have h2 : ((2 * q) / K) * K ≤ 2 * q := Nat.div_mul_le_self (2 * q) K
      rw [Nat.add_mul]
      omega
    omega

/-- Upper bound `frontierExp τ Δ ≤ (2 * Δ) / (τ + 1)`. -/
theorem frontierExp_le_two_mul_div (τ Δ : ℕ) :
    frontierExp τ Δ ≤ (2 * Δ) / (τ + 1) := by
  unfold frontierExp
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.sub_le _ 1

/-- Tradeoff exponent bound: `frontierExp (ceilDiv d t) d ≤ 2 * t` for all `1 ≤ t`. -/
theorem frontierExp_ceilDiv_le {d t : ℕ} (ht : 1 ≤ t) :
    frontierExp (ceilDiv d t) d ≤ 2 * t :=
  (frontierExp_le_two_mul_div _ _).trans (two_mul_div_succ_ceilDiv_le ht)

/-- **Homogeneous frontier depth-four reduction**: for any `H : HomogCircuit K n`, any bottom-degree
bound `τ ≥ 1`, and any gate `u : Fin H.size`, there exists a homogeneous `DepthFourCircuit`
computing `H.gatePoly u` with bottom degrees in `[1, τ]`, middle product fan-in at most
`ceilDiv (2 * H.deg u) τ`, and top fan-in at most `H.size ^ frontierExp τ (H.deg u)`. -/
theorem HomogCircuit.exists_depthFourCircuit {K : Type u} [CommSemiring K] {n τ : ℕ}
    (hτ : 1 ≤ τ) (H : HomogCircuit K n) (u : Fin H.size) :
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = H.gatePoly u ∧
      D.IsHomogeneousBounded (H.deg u) (ceilDiv (2 * H.deg u) τ) τ ∧
      D.topFanin ≤ H.size ^ frontierExp τ (H.deg u) := by
  have hunmerged :
      ∀ (Δ : ℕ), 1 ≤ Δ → ∀ (v : Fin H.size), H.deg v = Δ →
        ∃ (m_top : ℕ) (raw : Fin m_top → List (ℕ × MvPolynomial (Fin n) K)),
          m_top ≤ H.size ^ frontierExp τ Δ ∧
          (∀ i : Fin m_top,
            raw i ≠ [] ∧
            ((raw i).map Prod.fst).sum = Δ ∧
            ∀ q ∈ raw i, 1 ≤ q.1 ∧ q.1 ≤ τ ∧ q.2.IsHomogeneous q.1) ∧
          H.gatePoly v = ∑ i : Fin m_top, ((raw i).map Prod.snd).prod := by
    intro Δ
    induction Δ using Nat.strongRecOn with
    | ind Δ ih =>
      intro hΔ1 v hvΔ
      have hHpos : 1 ≤ H.size := Nat.succ_le_of_lt (Nat.zero_le _ |>.trans_lt v.2)
      by_cases hle : Δ ≤ τ
      · have hexp0 : frontierExp τ Δ = 0 := by unfold frontierExp; rw [ite_eq_left hle]
        rw [hexp0, pow_zero]
        refine ⟨1, fun _ => [(Δ, H.gatePoly v)], le_rfl,
          fun _ => ⟨List.cons_ne_nil _ _, by simp, fun q hq => ?_⟩, by simp⟩
        rcases List.mem_singleton.mp hq with rfl
        exact ⟨hΔ1, hle, hvΔ ▸ H.isHomogeneous_gatePoly v⟩
      · have hgt : τ < Δ := by omega
        let m := Δ - τ
        have hm1 : 1 ≤ m := by dsimp [m]; omega
        have hmv : m < H.deg v := by dsimp [m]; omega
        have hexp_pos : 1 ≤ frontierExp τ Δ := by
          unfold frontierExp
          rw [ite_eq_right hle]
          have hdiv2 : 2 ≤ (2 * Δ) / (τ + 1) :=
            (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
          omega
        let S : Finset (Fin H.size) := (H.frontier m).filter fun w => H.deg w ≤ Δ
        have hcut : H.gatePoly v = ∑ w ∈ S, H.quot m v w * H.gatePoly w := by
          rw [H.gatePoly_eq_sum_frontier hm1 v hmv]
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun w hw hnot => ?_
          have hlt : H.deg v < H.deg w := by
            simp only [S, Finset.mem_filter, hw, true_and, not_le] at hnot
            omega
          rw [H.quot_eq_zero_of_lt m v w hlt, zero_mul]
        have hbranch : ∀ w ∈ S,
            ∃ ls : List (List (ℕ × MvPolynomial (Fin n) K)),
              ls.length ≤ H.size ^ (frontierExp τ Δ - 1) ∧
              (∀ items ∈ ls,
                items ≠ [] ∧
                (items.map Prod.fst).sum = Δ ∧
                ∀ q ∈ items, 1 ≤ q.1 ∧ q.1 ≤ τ ∧ q.2.IsHomogeneous q.1) ∧
              (ls.map fun items => (items.map Prod.snd).prod).sum =
                H.quot m v w * H.gatePoly w := by
          intro w hw
          have hw_mem := Finset.mem_filter.mp hw
          have hw_fr := (Finset.mem_filter.mp hw_mem.1).2
          have hw_le : H.deg w ≤ Δ := hw_mem.2
          rcases hw_fr with ⟨hw_gt, hw_mul⟩
          have hgd := H.gate_deg w
          cases hgw : H.gates w with
          | zero _ => rw [hgw] at hw_mul; exact False.elim hw_mul
          | var _ => rw [hgw] at hw_mul; exact False.elim hw_mul
          | add _ _ _ _ => rw [hgw] at hw_mul; exact False.elim hw_mul
          | mul w₁ w₂ =>
            rw [hgw] at hw_mul hgd
            let w₁' : Fin H.size := ⟨w₁.1, w₁.2.trans w.2⟩
            let w₂' : Fin H.size := ⟨w₂.1, w₂.2.trans w.2⟩
            change H.deg w = H.deg w₁' + H.deg w₂' at hgd
            have hp1 : 1 ≤ H.deg w₁' := H.deg_pos w₁'
            have hq1 : 1 ≤ H.deg w₂' := H.deg_pos w₂'
            have hpm : H.deg w₁' ≤ m := hw_mul.1
            have hqm : H.deg w₂' ≤ m := hw_mul.2
            have hp_lt : H.deg w₁' < Δ := by dsimp [m] at hpm; omega
            have hq_lt : H.deg w₂' < Δ := by dsimp [m] at hqm; omega
            obtain ⟨m₁, raw₁, hm₁, hraw₁, hpoly₁⟩ := ih (H.deg w₁') hp_lt hp1 w₁' rfl
            obtain ⟨m₂, raw₂, hm₂, hraw₂, hpoly₂⟩ := ih (H.deg w₂') hq_lt hq1 w₂' rfl
            have hstep := frontierExp_step_le hτ hgt hpm hqm (by omega)
            have hlen_mul : m₁ * m₂ ≤ H.size ^ (frontierExp τ Δ - 1) := by
              calc
                m₁ * m₂ ≤ H.size ^ frontierExp τ (H.deg w₁') *
                    H.size ^ frontierExp τ (H.deg w₂') := Nat.mul_le_mul hm₁ hm₂
                _ = H.size ^ (frontierExp τ (H.deg w₁') + frontierExp τ (H.deg w₂')) :=
                  (pow_add _ _ _).symm
                _ ≤ H.size ^ (frontierExp τ Δ - 1) :=
                  Nat.pow_le_pow_right hHpos (by omega)
            have hgp_w : H.gatePoly w = H.gatePoly w₁' * H.gatePoly w₂' := by
              rw [gatePoly_eq, hgw]
            by_cases hweq : H.deg w = Δ
            · have hq0 : (H.quot m v w).IsHomogeneous 0 := by
                have h := H.isHomogeneous_quot m v w
                rwa [hvΔ, hweq, Nat.sub_self] at h
              let c₀ : K := (H.quot m v w).coeff 0
              have hqC : H.quot m v w = C c₀ := eq_C_coeff_zero_of_isHomogeneous_zero hq0
              let scaleHead (a : K) :
                  List (ℕ × MvPolynomial (Fin n) K) → List (ℕ × MvPolynomial (Fin n) K)
                | [] => []
                | (d₀, P₀) :: tl => (d₀, C a * P₀) :: tl
              let pairItem (k : Fin (m₁ * m₂)) : List (ℕ × MvPolynomial (Fin n) K) :=
                let ij := finProdFinEquiv.symm k
                scaleHead c₀ (raw₁ ij.1) ++ raw₂ ij.2
              refine ⟨List.ofFn pairItem, by rw [List.length_ofFn]; exact hlen_mul, ?_, ?_⟩
              · intro items hmem
                rcases List.mem_ofFn.mp hmem with ⟨k, rfl⟩
                let ij := finProdFinEquiv.symm k
                rcases hraw₁ ij.1 with ⟨hne₁, hsum₁, hq₁⟩
                rcases hraw₂ ij.2 with ⟨_, hsum₂, hq₂⟩
                cases hcons₁ : raw₁ ij.1 with
                | nil => exact False.elim (hne₁ hcons₁)
                | cons hd₁ tl₁ =>
                  rcases hd₁ with ⟨d₀, P₀⟩
                  have hmem_hd : (d₀, P₀) ∈ raw₁ ij.1 := by rw [hcons₁]; exact List.mem_cons_self
                  have hmem_tl : ∀ q ∈ tl₁, q ∈ raw₁ ij.1 := fun q hq => by
                    rw [hcons₁]; exact List.mem_cons_of_mem _ hq
                  have hsum₁' : d₀ + (tl₁.map Prod.fst).sum = H.deg w₁' := by
                    have hs := hsum₁
                    change ((raw₁ ij.1).map Prod.fst).sum = H.deg w₁' at hs
                    rwa [hcons₁, List.map_cons, List.sum_cons] at hs
                  dsimp only [pairItem, scaleHead]
                  rw [hcons₁]
                  refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
                  · simp only [List.cons_append, List.map_cons, List.map_append, List.sum_cons,
                      List.sum_append]
                    change d₀ + ((tl₁.map Prod.fst).sum + ((raw₂ ij.2).map Prod.fst).sum) = Δ
                    rw [hsum₂]
                    omega
                  · intro q hq
                    rcases List.mem_append.mp hq with hleft | hright
                    · rcases List.mem_cons.mp hleft with rfl | htl
                      · rcases hq₁ (d₀, P₀) hmem_hd with ⟨hd0_1, hd0_τ, hP0⟩
                        refine ⟨hd0_1, hd0_τ, ?_⟩
                        simpa using (isHomogeneous_C (Fin n) c₀).mul hP0
                      · exact hq₁ q (hmem_tl q htl)
                    · exact hq₂ q hright
              · have hmap_ofFn :
                    ((List.ofFn pairItem).map fun items => (items.map Prod.snd).prod) =
                      List.ofFn fun k => ((pairItem k).map Prod.snd).prod := by
                  rw [List.map_ofFn]; rfl
                rw [hmap_ofFn, List.sum_ofFn, ← Equiv.sum_comp finProdFinEquiv,
                  Fintype.sum_prod_type, hqC, hgp_w, hpoly₁, hpoly₂, Finset.sum_mul,
                  Finset.mul_sum]
                refine Finset.sum_congr rfl fun i₁ _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i₂ _ => ?_
                rcases hraw₁ i₁ with ⟨hne₁, _, _⟩
                cases hcons₁ : raw₁ i₁ with
                | nil => exact False.elim (hne₁ hcons₁)
                | cons hd₁ tl₁ =>
                  rcases hd₁ with ⟨d₀, P₀⟩
                  dsimp only [pairItem, scaleHead]
                  simp only [Equiv.symm_apply_apply, hcons₁, List.cons_append, List.map_cons,
                    List.map_append, List.prod_cons, List.prod_append]
                  ring
            · let kq := Δ - H.deg w
              have hkq1 : 1 ≤ kq := by dsimp [kq]; omega
              have hkqτ : kq ≤ τ := by dsimp [kq, m] at hw_gt ⊢; omega
              have hq_hom : (H.quot m v w).IsHomogeneous kq := by
                have h := H.isHomogeneous_quot m v w
                rwa [hvΔ] at h
              let pairItem (k : Fin (m₁ * m₂)) : List (ℕ × MvPolynomial (Fin n) K) :=
                let ij := finProdFinEquiv.symm k
                (kq, H.quot m v w) :: (raw₁ ij.1 ++ raw₂ ij.2)
              refine ⟨List.ofFn pairItem, by rw [List.length_ofFn]; exact hlen_mul, ?_, ?_⟩
              · intro items hmem
                rcases List.mem_ofFn.mp hmem with ⟨k, rfl⟩
                let ij := finProdFinEquiv.symm k
                rcases hraw₁ ij.1 with ⟨_, hsum₁, hq₁⟩
                rcases hraw₂ ij.2 with ⟨_, hsum₂, hq₂⟩
                refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
                · dsimp only [pairItem]
                  rw [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
                  change kq + (((raw₁ ij.1).map Prod.fst).sum + ((raw₂ ij.2).map Prod.fst).sum) = Δ
                  rw [hsum₁, hsum₂]
                  dsimp only [kq]
                  omega
                · intro q hq
                  rcases List.mem_cons.mp hq with rfl | hrest
                  · exact ⟨hkq1, hkqτ, hq_hom⟩
                  · rcases List.mem_append.mp hrest with hleft | hright
                    · exact hq₁ q hleft
                    · exact hq₂ q hright
              · have hmap_ofFn :
                    ((List.ofFn pairItem).map fun items => (items.map Prod.snd).prod) =
                      List.ofFn fun k => ((pairItem k).map Prod.snd).prod := by
                  rw [List.map_ofFn]; rfl
                rw [hmap_ofFn, List.sum_ofFn, ← Equiv.sum_comp finProdFinEquiv,
                  Fintype.sum_prod_type, hgp_w, hpoly₁, hpoly₂, Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i₁ _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i₂ _ => ?_
                change ((pairItem (finProdFinEquiv (i₁, i₂))).map Prod.snd).prod =
                  H.quot m v w * (((raw₁ i₁).map Prod.snd).prod * ((raw₂ i₂).map Prod.snd).prod)
                dsimp only [pairItem]
                simp only [Equiv.symm_apply_apply, List.map_cons, List.map_append,
                  List.prod_cons, List.prod_append]
        have hconcat : ∀ (ws : List (Fin H.size)), (∀ w ∈ ws, w ∈ S) →
            ∃ all : List (List (ℕ × MvPolynomial (Fin n) K)),
              all.length ≤ ws.length * H.size ^ (frontierExp τ Δ - 1) ∧
              (∀ items ∈ all,
                items ≠ [] ∧
                (items.map Prod.fst).sum = Δ ∧
                ∀ q ∈ items, 1 ≤ q.1 ∧ q.1 ≤ τ ∧ q.2.IsHomogeneous q.1) ∧
              (all.map fun items => (items.map Prod.snd).prod).sum =
                (ws.map fun w => H.quot m v w * H.gatePoly w).sum := by
          intro ws
          induction ws with
          | nil =>
            intro _
            exact ⟨[], by simp, fun _ h => False.elim (List.not_mem_nil h), by simp⟩
          | cons w tl ihtl =>
            intro hws
            obtain ⟨ls, hls_len, hls_inv, hls_sum⟩ := hbranch w (hws w List.mem_cons_self)
            obtain ⟨rest, hrest_len, hrest_inv, hrest_sum⟩ :=
              ihtl fun x hx => hws x (List.mem_cons_of_mem _ hx)
            refine ⟨ls ++ rest, ?_, ?_, ?_⟩
            · rw [List.length_append, List.length_cons, Nat.add_one_mul]
              omega
            · intro items hmem
              rcases List.mem_append.mp hmem with h1 | h2
              · exact hls_inv items h1
              · exact hrest_inv items h2
            · rw [List.map_append, List.sum_append, hls_sum, hrest_sum, List.map_cons,
                List.sum_cons]
        obtain ⟨all, hall_len, hall_inv, hall_sum⟩ :=
          hconcat S.toList fun w hw => Finset.mem_toList.mp hw
        have hSlen : S.toList.length ≤ H.size := by
          rw [Finset.length_toList]
          exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin H.size)
        have hall_bound : all.length ≤ H.size ^ frontierExp τ Δ := by
          calc
            all.length ≤ S.toList.length * H.size ^ (frontierExp τ Δ - 1) := hall_len
            _ ≤ H.size * H.size ^ (frontierExp τ Δ - 1) := Nat.mul_le_mul_right _ hSlen
            _ = H.size ^ frontierExp τ Δ := by
              rw [← pow_succ', show frontierExp τ Δ - 1 + 1 = frontierExp τ Δ by omega]
        refine ⟨all.length, fun i => all.get i, hall_bound,
          fun i => hall_inv (all.get i) (List.get_mem all i), ?_⟩
        rw [hcut]
        have hlist_sum : (S.toList.map fun w => H.quot m v w * H.gatePoly w).sum =
            ∑ w ∈ S, H.quot m v w * H.gatePoly w := by
          rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
          rfl
        rw [← hlist_sum, ← hall_sum, ← List.sum_ofFn]
        congr 1
        conv_lhs => rw [← List.ofFn_get all]
        rw [List.map_ofFn]
        rfl
  obtain ⟨m_top, raw, hm_top, hraw, hpoly⟩ := hunmerged (H.deg u) (H.deg_pos u) u rfl
  let terms (i : Fin m_top) : List (ℕ × MvPolynomial (Fin n) K) := mergeHomogItems τ (raw i)
  let D : DepthFourCircuit K (Fin n) :=
    { topFanin := m_top
      prodFanin := fun i => (terms i).length
      factors := fun i j => ((terms i).get j).2 }
  refine ⟨D, ?_, ?_, hm_top⟩
  · rw [hpoly]
    unfold DepthFourCircuit.polynomial
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hraw i with ⟨_, _, hq⟩
    have hm := mergeHomogItems_spec τ (raw i) (fun q h => ⟨(hq q h).1, (hq q h).2.1⟩)
      (fun q h => (hq q h).2.2)
    rw [← hm.1, ← List.prod_ofFn]
    congr 1
    conv_rhs => rw [← List.ofFn_get (mergeHomogItems τ (raw i))]
    rw [List.map_ofFn]
    rfl
  · refine ⟨fun i => ?_, fun i => ?_⟩
    · rcases hraw i with ⟨hne, hsum, hq⟩
      have hm := mergeHomogItems_spec τ (raw i) (fun q h => ⟨(hq q h).1, (hq q h).2.1⟩)
        (fun q h => (hq q h).2.2)
      have hne_out : terms i ≠ [] := hm.2.2.1 hne
      have hlen := length_le_ceilDiv_of_adjacentSumGt hτ hne_out
        (fun q h => (hm.2.2.2.1 q h).1) hm.2.2.2.2.2
      rwa [hm.2.1, hsum] at hlen
    · rcases hraw i with ⟨_, hsum, hq⟩
      have hm := mergeHomogItems_spec τ (raw i) (fun q h => ⟨(hq q h).1, (hq q h).2.1⟩)
        (fun q h => (hq q h).2.2)
      refine ⟨fun j => ((terms i).get j).1, ?_, ?_, ?_⟩
      · rw [← List.sum_ofFn, ← hsum, ← hm.2.1]
        congr 1
        conv_rhs => rw [← List.ofFn_get (mergeHomogItems τ (raw i))]
        rw [List.map_ofFn]
        rfl
      · intro j
        exact hm.2.2.2.1 _ (List.get_mem (terms i) j)
      · intro j
        exact hm.2.2.2.2.1 _ (List.get_mem (terms i) j)

/-- **Parameterized depth-four chasm tradeoff for homogeneous circuits**: for every `t ≥ 1` and
every gate `u` of `H : HomogCircuit K n` (of degree `d = H.deg u`), setting `τ := ceilDiv d t`
yields a homogeneous `ΣΠ^{[2 * t]}ΣΠ^{[τ]}` circuit computing `H.gatePoly u` with top fan-in at
most `H.size ^ (2 * t)`. -/
theorem HomogCircuit.exists_depthFourCircuit_tradeoff {K : Type u} [CommSemiring K] {n t : ℕ}
    (ht : 1 ≤ t) (H : HomogCircuit K n) (u : Fin H.size) :
    let d := H.deg u
    let τ := ceilDiv d t
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = H.gatePoly u ∧
      D.IsHomogeneousBounded d (2 * t) τ ∧
      D.topFanin ≤ H.size ^ (2 * t) := by
  intro d τ
  have hd : 1 ≤ d := H.deg_pos u
  have hτ : 1 ≤ τ := one_le_ceilDiv hd ht
  obtain ⟨D, hpoly, hhb, htop⟩ := H.exists_depthFourCircuit hτ u
  have hHpos : 1 ≤ H.size := Nat.succ_le_of_lt (Nat.zero_le _ |>.trans_lt u.2)
  refine ⟨D, hpoly, hhb.mono (ceilDiv_two_mul_ceilDiv_le hd ht) le_rfl, ?_⟩
  exact htop.trans (Nat.pow_le_pow_right hHpos (frontierExp_ceilDiv_le ht))

/-- **Depth-four chasm tradeoff for any homogeneous component of an arithmetic circuit**:
for any `c : Circuit (arithSignature K) n 1`, `d ≥ 1`, and `t ≥ 1`, the degree-`d` homogeneous
component of `c.polynomial 0` is computed by a homogeneous `ΣΠ^{[2 * t]}ΣΠ^{[ceilDiv d t]}`
circuit with top fan-in at most `(2 * (n + c.size) * d ^ 2) ^ (2 * t)`. -/
theorem exists_depthFourCircuit_homogeneousComponent {K : Type u} [CommSemiring K] {n d t : ℕ}
    (hd : 1 ≤ d) (ht : 1 ≤ t) (c : Circuit (arithSignature K) n 1) :
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = homogeneousComponent d (c.polynomial 0) ∧
      D.IsHomogeneousBounded d (2 * t) (ceilDiv d t) ∧
      D.topFanin ≤ (2 * (n + c.size) * d ^ 2) ^ (2 * t) := by
  obtain ⟨H, out, hsz, hdeg, hpoly⟩ := exists_homogCircuit_homogeneousComponent hd c
  obtain ⟨D, hDpoly, hDhb, hDtop⟩ := H.exists_depthFourCircuit_tradeoff ht out
  rw [hdeg] at hDhb
  exact ⟨D, hDpoly.trans hpoly, hDhb, hDtop.trans (Nat.pow_le_pow_left hsz _)⟩

/-- **Depth-four chasm tradeoff for a homogeneous polynomial computed by an arithmetic circuit**. -/
theorem exists_depthFourCircuit_of_isHomogeneous {K : Type u} [CommSemiring K] {n d t : ℕ}
    (hd : 1 ≤ d) (ht : 1 ≤ t) (c : Circuit (arithSignature K) n 1)
    (hhom : (c.polynomial 0).IsHomogeneous d) :
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = c.polynomial 0 ∧
      D.IsHomogeneousBounded d (2 * t) (ceilDiv d t) ∧
      D.topFanin ≤ (2 * (n + c.size) * d ^ 2) ^ (2 * t) := by
  obtain ⟨D, hDpoly, hDhb, hDtop⟩ := exists_depthFourCircuit_homogeneousComponent hd ht c
  rw [homogeneousComponent_of_mem hhom, ite_eq_left rfl] at hDpoly
  exact ⟨D, hDpoly, hDhb, hDtop⟩

/-- **The depth-four chasm theorem (`t = √d` instantiation)**: any degree-`d` (`d ≥ 1`) homogeneous
polynomial computed by an arithmetic circuit `c` of size `s` in `n` variables is computed by a
homogeneous `ΣΠ^{[2 * t]}ΣΠ^{[√d + 2]}` circuit (`t = max 1 (Nat.sqrt d)`) with subexponential
top fan-in at most `(2 * (n + s) * d ^ 2) ^ (2 * t)`. -/
theorem exists_depthFourCircuit_sqrt {K : Type u} [CommSemiring K] {n d : ℕ}
    (hd : 1 ≤ d) (c : Circuit (arithSignature K) n 1)
    (hhom : (c.polynomial 0).IsHomogeneous d) :
    let t := max 1 (Nat.sqrt d)
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = c.polynomial 0 ∧
      D.IsHomogeneousBounded d (2 * t) (Nat.sqrt d + 2) ∧
      D.topFanin ≤ (2 * (n + c.size) * d ^ 2) ^ (2 * t) := by
  intro t
  have ht : 1 ≤ t := le_max_left 1 _
  obtain ⟨D, hDpoly, hDhb, hDtop⟩ := exists_depthFourCircuit_of_isHomogeneous hd ht c hhom
  exact ⟨D, hDpoly, hDhb.mono le_rfl (ceilDiv_sqrt_le d), hDtop⟩

/-- **Depth-four chasm size bound (`ΣΠΣΠ^[√d]` total monomial size)**: for `1 ≤ n` and `1 ≤ d`,
combining `exists_depthFourCircuit_sqrt` with monomial counting gives a homogeneous depth-four
circuit whose bottom monomial count is bounded explicitly by
`(2 * (n + s) * d ^ 2) ^ (2 * t) * (2 * t) * (n + Nat.sqrt d + 1).choose (Nat.sqrt d + 2)`. -/
theorem exists_depthFourCircuit_sqrt_size {K : Type u} [CommSemiring K] {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (c : Circuit (arithSignature K) n 1)
    (hhom : (c.polynomial 0).IsHomogeneous d) :
    let t := max 1 (Nat.sqrt d)
    let τ := Nat.sqrt d + 2
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = c.polynomial 0 ∧
      D.IsHomogeneousBounded d (2 * t) τ ∧
      D.topFanin ≤ (2 * (n + c.size) * d ^ 2) ^ (2 * t) ∧
      D.bottomSize ≤ (2 * (n + c.size) * d ^ 2) ^ (2 * t) * (2 * t) * (n + τ - 1).choose τ := by
  intro t τ
  obtain ⟨D, hDpoly, hDhb, hDtop⟩ := exists_depthFourCircuit_sqrt hd c hhom
  have hbot : D.bottomSize ≤ D.topFanin * (2 * t) * (n + τ - 1).choose τ :=
    D.bottomSize_le_of_isHomogeneousBounded hn hDhb
  exact ⟨D, hDpoly, hDhb, hDtop, hbot.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hDtop))⟩

/-- **Depth-four reduction for an arbitrary (possibly inhomogeneous) arithmetic circuit** of total
degree at most `d`: sums the constant term and the homogeneous depth-four circuits of degrees
`1, …, d`, producing a `ΣΠ^{[2 * t]}ΣΠ^{[ceilDiv d t]}` circuit of top fan-in at most
`1 + d * (2 * (n + c.size) * d ^ 2) ^ (2 * t)`. -/
theorem exists_depthFourCircuit_of_totalDegree_le {K : Type u} [CommSemiring K] {n d t : ℕ}
    (ht : 1 ≤ t) (c : Circuit (arithSignature K) n 1)
    (hdeg : (c.polynomial 0).totalDegree ≤ d) :
    ∃ D : DepthFourCircuit K (Fin n),
      D.polynomial = c.polynomial 0 ∧
      D.IsBounded (2 * t) (ceilDiv d t) ∧
      D.topFanin ≤ 1 + d * (2 * (n + c.size) * d ^ 2) ^ (2 * t) := by
  let S := (2 * (n + c.size) * d ^ 2) ^ (2 * t)
  have hpart : ∀ k : ℕ, k ≤ d →
      ∃ D : DepthFourCircuit K (Fin n),
        D.polynomial = ∑ r ∈ Finset.range (k + 1), homogeneousComponent r (c.polynomial 0) ∧
        D.IsBounded (2 * t) (ceilDiv d t) ∧
        D.topFanin ≤ 1 + k * S := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨DepthFourCircuit.ofConst ((c.polynomial 0).coeff 0), ?_,
        DepthFourCircuit.isBounded_ofConst _ (by omega), by simp [DepthFourCircuit.ofConst]⟩
      rw [DepthFourCircuit.polynomial_ofConst, Finset.sum_range_one]
      exact (homogeneousComponent_zero_eq_C_coeff _).symm
    | succ k ih =>
      intro hk
      obtain ⟨D₁, hpoly₁, hb₁, htop₁⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨D₂, hpoly₂, hhb₂, htop₂⟩ :=
        exists_depthFourCircuit_homogeneousComponent (by omega : 1 ≤ k + 1) ht c
      have hb₂ : D₂.IsBounded (2 * t) (ceilDiv d t) :=
        hhb₂.isBounded.mono le_rfl (ceilDiv_mono_left hk)
      have htop₂_le : D₂.topFanin ≤ S := by
        refine htop₂.trans (Nat.pow_le_pow_left ?_ _)
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 2)
      refine ⟨D₁.add D₂, ?_, D₁.isBounded_add hb₁ hb₂, ?_⟩
      · rw [D₁.polynomial_add, hpoly₁, hpoly₂, ← Finset.sum_range_succ]
      · change D₁.topFanin + D₂.topFanin ≤ 1 + (k + 1) * S
        rw [Nat.add_one_mul]
        omega
  obtain ⟨D, hpoly, hb, htop⟩ := hpart d le_rfl
  refine ⟨D, hpoly.trans ?_, hb, htop⟩
  ext e
  rw [coeff_sum]
  simp only [coeff_homogeneousComponent]
  rw [Finset.sum_ite_eq (Finset.range (d + 1)) e.degree]
  by_cases hed : e.degree < d + 1
  · rw [ite_eq_left (Finset.mem_range.mpr hed)]
  · rw [ite_eq_right (by simpa [Finset.mem_range] using hed)]
    symm
    by_contra hne
    have hle_td : e.degree ≤ (c.polynomial 0).totalDegree :=
      Finset.le_sup (f := fun s => s.sum fun _ m => m) (mem_support_iff.mpr hne)
    omega

/-- **Depth-four chasm for homogeneous families in `VP`**: every homogeneous family `f ∈ VP K` of
degrees `d n ≥ 1` admits a polynomially bounded base `B` and homogeneous `ΣΠΣΠ` circuits `D n`
with bottom degree at most `Nat.sqrt (d n) + 2`, middle fan-in at most
`2 * max 1 (Nat.sqrt (d n))`, and subexponential top fan-in at most
`(B n) ^ (2 * max 1 (Nat.sqrt (d n)))`. -/
theorem VP.exists_homog_depthFour_chasm {K : Type u} [CommSemiring K]
    {f : PolynomialFamily K} (hf : f ∈ VP K) (d : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ d n) (hhom : ∀ n, (f.poly n).IsHomogeneous (d n))
    (hd_poly : PolynomiallyBounded d) :
    ∃ (B : ℕ → ℕ) (D : ∀ n, DepthFourCircuit K (Fin (f.vars n))),
      PolynomiallyBounded B ∧
      ∀ n,
        let t := max 1 (Nat.sqrt (d n))
        (D n).polynomial = f.poly n ∧
        (D n).IsHomogeneousBounded (d n) (2 * t) (Nat.sqrt (d n) + 2) ∧
        (D n).topFanin ≤ (B n) ^ (2 * t) := by
  obtain ⟨⟨hvars, _⟩, c, hcsize, hcpoly⟩ := hf
  choose D hDpoly hDhb hDtop using fun n =>
    exists_depthFourCircuit_sqrt (hd n) (c n) ((hcpoly n).symm ▸ hhom n)
  let B (n : ℕ) : ℕ := 2 * (f.vars n + (c n).size) * (d n) ^ 2
  have hB : PolynomiallyBounded B :=
    ((PolynomiallyBounded.const 2).mul (hvars.add hcsize)).mul (hd_poly.pow 2)
  exact ⟨B, D, hB, fun n => ⟨(hDpoly n).trans (hcpoly n), hDhb n, hDtop n⟩⟩

/-- **Depth-four chasm for arbitrary (not necessarily homogeneous) families in `VP`**: every
`f ∈ VP K` admits a polynomially bounded base `B` and `ΣΠΣΠ` circuits `D n` with bottom degree at
most `Nat.sqrt (max 1 (f.poly n).totalDegree) + 2`, middle fan-in at most
`2 * max 1 (Nat.sqrt (max 1 (f.poly n).totalDegree))`, and subexponential top fan-in at most
`(B n) ^ (2 * max 1 (Nat.sqrt (max 1 (f.poly n).totalDegree)))`. -/
theorem VP.exists_depthFour_chasm {K : Type u} [CommSemiring K]
    {f : PolynomialFamily K} (hf : f ∈ VP K) :
    ∃ (B : ℕ → ℕ) (D : ∀ n, DepthFourCircuit K (Fin (f.vars n))),
      PolynomiallyBounded B ∧
      ∀ n,
        let d := max 1 (f.poly n).totalDegree
        let t := max 1 (Nat.sqrt d)
        (D n).polynomial = f.poly n ∧
        (D n).IsBounded (2 * t) (Nat.sqrt d + 2) ∧
        (D n).topFanin ≤ (B n) ^ (2 * t) := by
  obtain ⟨⟨hvars, hdeg⟩, c, hcsize, hcpoly⟩ := hf
  let dfn (n : ℕ) : ℕ := max 1 (f.poly n).totalDegree
  let tfn (n : ℕ) : ℕ := max 1 (Nat.sqrt (dfn n))
  choose D hDpoly hDb hDtop using fun n =>
    exists_depthFourCircuit_of_totalDegree_le (d := dfn n)
      (le_max_left 1 (Nat.sqrt (dfn n))) (c n)
      (by rw [hcpoly n]; exact le_max_right 1 _)
  let Sfn (n : ℕ) : ℕ := 2 * (f.vars n + (c n).size) * (dfn n) ^ 2
  let B (n : ℕ) : ℕ := (dfn n + 1) * (Sfn n + 1)
  have hdf : PolynomiallyBounded dfn := (PolynomiallyBounded.const 1).max hdeg
  have hSf : PolynomiallyBounded Sfn :=
    ((PolynomiallyBounded.const 2).mul (hvars.add hcsize)).mul (hdf.pow 2)
  have hB : PolynomiallyBounded B :=
    (hdf.add (PolynomiallyBounded.const 1)).mul (hSf.add (PolynomiallyBounded.const 1))
  refine ⟨B, D, hB, fun n => ?_⟩
  refine ⟨(hDpoly n).trans (hcpoly n), (hDb n).mono le_rfl (ceilDiv_sqrt_le (dfn n)), ?_⟩
  have ht1 : 1 ≤ tfn n := le_max_left 1 _
  have h2t : 2 ≤ 2 * tfn n := by omega
  calc
    (D n).topFanin ≤ 1 + dfn n * (Sfn n) ^ (2 * tfn n) := hDtop n
    _ ≤ 1 * (Sfn n + 1) ^ (2 * tfn n) + dfn n * (Sfn n + 1) ^ (2 * tfn n) :=
      Nat.add_le_add (by simpa using Nat.one_le_pow (2 * tfn n) (Sfn n + 1) (by omega))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))
    _ = (dfn n + 1) * (Sfn n + 1) ^ (2 * tfn n) := by ring
    _ ≤ (dfn n + 1) ^ (2 * tfn n) * (Sfn n + 1) ^ (2 * tfn n) :=
      Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) (dfn n + 1))
    _ = (B n) ^ (2 * tfn n) := (mul_pow _ _ _).symm

/-- **Super-chasm depth-four lower bounds exclude a family from `VP`**: if a homogeneous family
`f` of polynomially bounded degrees `d n ≥ 1` exceeds every `(B n) ^ (2 * t)` top-fan-in bound
(for polynomially bounded `B`) on homogeneous `ΣΠ^{[2 * t]}ΣΠ^{[√(d n) + 2]}` circuits
(`t = max 1 (Nat.sqrt (d n))`), then `f ∉ VP K`. -/
theorem not_mem_VP_of_depthFour_lower_bound {K : Type u} [CommSemiring K]
    {f : PolynomialFamily K} (d : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ d n) (hhom : ∀ n, (f.poly n).IsHomogeneous (d n))
    (hd_poly : PolynomiallyBounded d)
    (hlb : ∀ B : ℕ → ℕ, PolynomiallyBounded B →
      ∃ n : ℕ,
        let t := max 1 (Nat.sqrt (d n))
        ∀ D : DepthFourCircuit K (Fin (f.vars n)),
          D.polynomial = f.poly n →
          D.IsHomogeneousBounded (d n) (2 * t) (Nat.sqrt (d n) + 2) →
          (B n) ^ (2 * t) < D.topFanin) :
    f ∉ VP K := by
  intro hf
  obtain ⟨B, D, hB, hchasm⟩ := VP.exists_homog_depthFour_chasm hf d hd hhom hd_poly
  obtain ⟨n, hn⟩ := hlb B hB
  rcases hchasm n with ⟨hpoly, hhb, htop⟩
  exact Nat.not_lt.mpr htop (hn (D n) hpoly hhb)

/-- **Depth-four chasm separation criterion (`VP ≠ VNP`)**: if a homogeneous family `f ∈ VNP K`
satisfies a super-chasm lower bound against homogeneous `ΣΠΣΠ^[√(d n) + 2]` circuits, then
`VP K ≠ VNP K`. -/
theorem VP_ne_VNP_of_depthFour_lower_bound {K : Type u} [CommSemiring K]
    {f : PolynomialFamily K} (hf_vnp : f ∈ VNP K) (d : ℕ → ℕ)
    (hd : ∀ n, 1 ≤ d n) (hhom : ∀ n, (f.poly n).IsHomogeneous (d n))
    (hd_poly : PolynomiallyBounded d)
    (hlb : ∀ B : ℕ → ℕ, PolynomiallyBounded B →
      ∃ n : ℕ,
        let t := max 1 (Nat.sqrt (d n))
        ∀ D : DepthFourCircuit K (Fin (f.vars n)),
          D.polynomial = f.poly n →
          D.IsHomogeneousBounded (d n) (2 * t) (Nat.sqrt (d n) + 2) →
          (B n) ^ (2 * t) < D.topFanin) :
    VP K ≠ VNP K := by
  intro hEq
  exact not_mem_VP_of_depthFour_lower_bound d hd hhom hd_poly hlb (hEq ▸ hf_vnp)

/-- The `n × n` generic permanent is a homogeneous polynomial of degree `n`. -/
theorem permFamily_isHomogeneous (K : Type u) [CommSemiring K] (n : ℕ) :
    ((permFamily K).poly n).IsHomogeneous n := by
  change (genericMatrix K n).permanent.IsHomogeneous n
  rw [Matrix.permanent]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin n => genericMatrix K n (σ i) i) (fun _ => 1) fun i _ => by
    simpa [genericMatrix] using MvPolynomial.isHomogeneous_X K (finProdFinEquiv (σ i, i)) using 1
  simp

/-- **Permanent specialization of the depth-four chasm separation**: over any commutative ring `K`,
proving that for every polynomially bounded `B` there exists `n ≥ 1` where every homogeneous
`ΣΠ^{[2 * √n]}ΣΠ^{[√n + 2]}` circuit computing the `n × n` generic permanent has top fan-in
strictly exceeding `(B n) ^ (2 * √n)` separates `VP K` from `VNP K`. -/
theorem VP_ne_VNP_of_permFamily_depthFour_lower_bound {K : Type u} [CommRing K]
    (hlb : ∀ B : ℕ → ℕ, PolynomiallyBounded B →
      ∃ n : ℕ, 1 ≤ n ∧
        ∀ D : DepthFourCircuit K (Fin (n * n)),
          D.polynomial = (genericMatrix K n).permanent →
          D.IsHomogeneousBounded n (2 * Nat.sqrt n) (Nat.sqrt n + 2) →
          (B n) ^ (2 * Nat.sqrt n) < D.topFanin) :
    VP K ≠ VNP K := by
  intro hEq
  have hperm : permFamily K ∈ VP K := hEq ▸ permFamily_mem_VNP
  obtain ⟨_, c, hcsize, hcpoly⟩ := hperm
  let B (n : ℕ) : ℕ := 2 * (n * n + (c n).size) * n ^ 2
  have hB : PolynomiallyBounded B :=
    ((PolynomiallyBounded.const 2).mul
      ((PolynomiallyBounded.id.mul PolynomiallyBounded.id).add hcsize)).mul
      (PolynomiallyBounded.id.pow 2)
  obtain ⟨n, hn1, hlb_n⟩ := hlb B hB
  have hsqrt : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn1
  have hmax : max 1 (Nat.sqrt n) = Nat.sqrt n := max_eq_right hsqrt
  obtain ⟨D, hDpoly, hDhb, hDtop⟩ :=
    exists_depthFourCircuit_sqrt hn1 (c n) ((hcpoly n).symm ▸ permFamily_isHomogeneous K n)
  rw [hmax] at hDhb hDtop
  exact Nat.not_lt.mpr hDtop (hlb_n D (hDpoly.trans (hcpoly n)) hDhb)

/-! ### : Concrete non-vacuity witnesses -/

/-- Concrete fan-in-two arithmetic circuit of size `3` computing `(X 0 + X 1) ^ 4` in
`ℤ[X₀, X₁]`. -/
def exampleCircuitBinomialPow4 : Circuit (arithSignature ℤ) 2 1 :=
  let p0 : Program (arithSignature ℤ) 2 0 := .empty
  let p1 : Program (arithSignature ℤ) 2 1 := p0.gate ⟨ArithOp.add, ![Wire.input 0, Wire.input 1]⟩
  let p2 : Program (arithSignature ℤ) 2 2 := p1.gate ⟨ArithOp.mul, ![Wire.gate 0, Wire.gate 0]⟩
  let p3 : Program (arithSignature ℤ) 2 3 := p2.gate ⟨ArithOp.mul, ![Wire.gate 1, Wire.gate 1]⟩
  ⟨p3, fun _ => Wire.gate 2⟩

/-- `exampleCircuitBinomialPow4` computes `(X 0 + X 1) ^ 4`. -/
theorem exampleCircuitBinomialPow4_polynomial :
    exampleCircuitBinomialPow4.polynomial 0 = (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) ^ 4 := by
  let I := arithInterpretationWith ℤ (C : ℤ → MvPolynomial (Fin 2) ℤ)
  let p0 : Program (arithSignature ℤ) 2 0 := .empty
  let p1 : Program (arithSignature ℤ) 2 1 := p0.gate ⟨ArithOp.add, ![Wire.input 0, Wire.input 1]⟩
  let p2 : Program (arithSignature ℤ) 2 2 := p1.gate ⟨ArithOp.mul, ![Wire.gate 0, Wire.gate 0]⟩
  let p3 : Program (arithSignature ℤ) 2 3 := p2.gate ⟨ArithOp.mul, ![Wire.gate 1, Wire.gate 1]⟩
  change p3.trace I X (Wire.gate 2) = _
  have h0 : p1.trace I X (Wire.gate 0) = X 0 + X 1 := by
    dsimp only [p1]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Program.trace_gate_last]
    simp [I]
  have h1 : p2.trace I X (Wire.gate 1) = (X 0 + X 1) * (X 0 + X 1) := by
    dsimp only [p2]
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, Program.trace_gate_last]
    simp only [I, arithInterpretationWith_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact congrArg₂ (· * ·) h0 h0
  dsimp only [p3]
  rw [show (2 : Fin 3) = Fin.last 2 from rfl, Program.trace_gate_last]
  simp only [I, arithInterpretationWith_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [h1]
  ring

/-- `exampleCircuitBinomialPow4` computes a homogeneous polynomial of degree `4`. -/
theorem exampleCircuitBinomialPow4_isHomogeneous :
    (exampleCircuitBinomialPow4.polynomial 0).IsHomogeneous 4 := by
  rw [exampleCircuitBinomialPow4_polynomial]
  have h1 : (X 0 + X 1 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 :=
    (isHomogeneous_X ℤ (0 : Fin 2)).add (isHomogeneous_X ℤ (1 : Fin 2))
  simpa using h1.pow 4

/-- Non-vacuity witness for VSBR logarithmic-depth reduction on `exampleCircuitBinomialPow4`:
there exists an `SPCircuit ℤ 2` computing `(X 0 + X 1) ^ 4` of depth at most `12` and
product-depth at most `6`. -/
theorem exampleCircuitBinomialPow4_spCircuit_log_depth :
    ∃ C : SPCircuit ℤ 2,
      C.polynomial = (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) ^ 4 ∧
      C.depth ≤ 12 ∧ C.productDepth ≤ 6 := by
  have hdeg : (exampleCircuitBinomialPow4.polynomial 0).totalDegree ≤ 4 :=
    DepthFourCircuit.totalDegree_le_of_isHomogeneous exampleCircuitBinomialPow4_isHomogeneous
  obtain ⟨C, hpoly, hdep, hpdep, _, _⟩ :=
    exists_spCircuit_log_depth exampleCircuitBinomialPow4 hdeg
  have hclog : Nat.clog 2 4 = 2 := by decide
  refine ⟨C, hpoly.trans exampleCircuitBinomialPow4_polynomial, ?_, ?_⟩
  · simpa [hclog] using hdep
  · simpa [hclog] using hpdep

/-- Non-vacuity witness for the depth-four chasm theorem on `exampleCircuitBinomialPow4`:
there exists a homogeneous `ΣΠ^{[4]}ΣΠ^{[4]}` circuit computing `(X 0 + X 1) ^ 4` with top fan-in
at most `160 ^ 4`. -/
theorem exampleCircuitBinomialPow4_depthFour_chasm :
    ∃ D : DepthFourCircuit ℤ (Fin 2),
      D.polynomial = (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) ^ 4 ∧
      D.IsHomogeneousBounded 4 4 4 ∧
      D.topFanin ≤ 160 ^ 4 := by
  obtain ⟨D, hpoly, hhb, htop⟩ :=
    exists_depthFourCircuit_sqrt (by decide : 1 ≤ 4) exampleCircuitBinomialPow4
      exampleCircuitBinomialPow4_isHomogeneous
  have hsqrt : Nat.sqrt 4 = 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.sqrt_eq]
  have hsz : exampleCircuitBinomialPow4.size = 3 := rfl
  refine ⟨D, hpoly.trans exampleCircuitBinomialPow4_polynomial, ?_, ?_⟩
  · simpa [hsqrt] using hhb
  · simpa [hsqrt, hsz] using htop

/-- A concrete homogeneous depth-four `ΣΠ^{[2]}ΣΠ^{[2]}` circuit over `ℤ` computing the cubic
polynomial `(X 0 + X 1) * (X 0 ^ 2 + X 1 ^ 2)`. -/
noncomputable def exampleDepthFourCubic : DepthFourCircuit ℤ (Fin 2) where
  topFanin := 1
  prodFanin _ := 2
  factors _ j := if j.1 = 0 then X 0 + X 1 else X 0 ^ 2 + X 1 ^ 2

/-- `exampleDepthFourCubic` computes `(X 0 + X 1) * (X 0 ^ 2 + X 1 ^ 2)`. -/
theorem exampleDepthFourCubic_polynomial :
    exampleDepthFourCubic.polynomial =
      (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) * (X 0 ^ 2 + X 1 ^ 2) := by
  unfold DepthFourCircuit.polynomial exampleDepthFourCubic
  simp [Fin.prod_univ_two]

/-- `exampleDepthFourCubic` satisfies `IsHomogeneousBounded 3 2 2`, witnessing non-vacuity of the
homogeneous bounded depth-four predicate. -/
theorem exampleDepthFourCubic_isHomogeneousBounded :
    exampleDepthFourCubic.IsHomogeneousBounded 3 2 2 := by
  refine ⟨fun _ => le_rfl, fun _ => ⟨fun j => if j.1 = 0 then 1 else 2, ?_, ?_, ?_⟩⟩
  · change (∑ j : Fin 2, if j.1 = 0 then 1 else 2) = 3
    simp [Fin.sum_univ_two]
  · intro j
    fin_cases j <;> simp
  · intro j
    fin_cases j
    · simpa [exampleDepthFourCubic] using
        (isHomogeneous_X ℤ (0 : Fin 2)).add (isHomogeneous_X ℤ (1 : Fin 2))
    · simpa [exampleDepthFourCubic] using
        ((isHomogeneous_X ℤ (0 : Fin 2)).pow 2).add ((isHomogeneous_X ℤ (1 : Fin 2)).pow 2)

/-- Compiling `exampleDepthFourCubic` to an `SPFormula` preserves its polynomial and certifies
product-depth at most `2` and bottom monomial count at most `6`. -/
theorem exampleDepthFourCubic_compiled_properties :
    exampleDepthFourCubic.toSPFormula.polynomial =
      (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) * (X 0 ^ 2 + X 1 ^ 2) ∧
    exampleDepthFourCubic.toSPFormula.productDepth ≤ 2 ∧
    exampleDepthFourCubic.bottomSize ≤ 6 := by
  refine ⟨exampleDepthFourCubic.polynomial_toSPFormula.trans exampleDepthFourCubic_polynomial,
    exampleDepthFourCubic.productDepth_toSPFormula_le, ?_⟩
  have h := exampleDepthFourCubic.bottomSize_le_of_isHomogeneousBounded (by decide : 1 ≤ 2)
    exampleDepthFourCubic_isHomogeneousBounded
  simpa [exampleDepthFourCubic] using h

end Cslib.Circuits.Arithmetic
