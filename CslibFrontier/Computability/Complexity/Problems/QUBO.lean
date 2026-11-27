/-
Copyright (c) 2026 Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cslib contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TSP
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic unconstrained binary optimization, Ising forms, and TSP reduction

A **quadratic unconstrained binary optimization** (`QUBO`) instance on a finite variable set `ι`
over a commutative ring `R` evaluates `E_Q(z) = ∑_{i,j} Q_{i,j} z_i z_j + ∑_i c_i z_i + c_0` at
binary assignments `z : ι → Bool` (`boolBit z_i ∈ {0, 1}`). An **Ising energy form** (`IsingForm`)
evaluates `H(z) = ∑_{i,j} J_{i,j} σ_i σ_j + ∑_i h_i σ_i + E_0` on spins `σ_i = 2 z_i - 1 ∈ {-1, 1}`.

We establish:
* normal-form invariances (`QUBO.eval_extractDiag`, `QUBO.eval_absorbLinear`) and exact objective-
  and coupling-graph-preserving bidirectional translations `QUBO.toIsing` and `IsingForm.toQUBO`
  [Boros and Hammer], [Lucas];
* the two-way one-hot assignment (permutation-matrix) quadratic penalty (`assignmentPenalty`,
  `assignmentPenaltyQUBO`) with permutation characterization `isAssignmentMatrix_iff_exists_perm`
  and infeasible penalty lower bound (`one_le_assignmentPenalty_of_not`);
* the exact Lucas QUBO and Ising reduction from `Cslib.Complexity.TSP`: for every nonempty
  `x : TSPInstance` (`0 < x.dist.length`), `x ∈ TSP` if and only if there exists a binary assignment
  on `Fin n × Fin n` where `(tspToQUBO x hn).eval z ≤ x.bound`, and equivalently where
  `(tspToIsing x hn).eval z ≤ x.bound` (`mem_TSP_iff_exists_qubo_le`,
  `mem_TSP_iff_exists_ising_le`).
-/

public section

open scoped BigOperators Matrix

namespace CslibFrontier.Complexity

universe u v

/-- Embeds `Bool` into `{0, 1}` in `R`. -/
def boolBit {R : Type v} [Zero R] [One R] (b : Bool) : R :=
  if b then 1 else 0

@[simp] theorem boolBit_false {R : Type v} [Zero R] [One R] : (boolBit false : R) = 0 := by rfl
@[simp] theorem boolBit_true {R : Type v} [Zero R] [One R] : (boolBit true : R) = 1 := by rfl

@[simp]
theorem boolBit_mul_self {R : Type v} [MulZeroOneClass R] (b : Bool) :
    (boolBit b : R) * boolBit b = boolBit b := by
  cases b <;> simp

@[simp, norm_cast]
theorem cast_boolBit_nat {R : Type v} [AddMonoidWithOne R] (b : Bool) :
    ((boolBit b : ℕ) : R) = boolBit b := by
  cases b <;> simp

/-- Embeds `Bool` as an Ising spin in `{-1, 1}` in `R`. -/
def boolSpin {R : Type v} [One R] [Neg R] (b : Bool) : R :=
  if b then 1 else -1

@[simp] theorem boolSpin_false {R : Type v} [One R] [Neg R] : (boolSpin false : R) = -1 := by rfl
@[simp] theorem boolSpin_true {R : Type v} [One R] [Neg R] : (boolSpin true : R) = 1 := by rfl

theorem boolSpin_eq_two_mul_boolBit_sub_one {R : Type v} [Ring R] (b : Bool) :
    (boolSpin b : R) = 2 * boolBit b - 1 := by
  cases b <;> norm_num

@[simp]
theorem boolSpin_mul_self {R : Type v} [Ring R] (b : Bool) :
    (boolSpin b : R) * boolSpin b = 1 := by
  cases b <;> simp

/-- A quadratic unconstrained binary optimization objective on variables `ι` over `R`. -/
@[ext]
structure QUBO (ι : Type u) (R : Type v) where
  /-- Quadratic interaction matrix `Q_{i,j}`. -/
  quad : Matrix ι ι R
  /-- Linear bias coefficients `c_i`. -/
  lin : ι → R
  /-- Constant offset `c_0`. -/
  const : R

namespace QUBO

variable {ι : Type u} {R : Type v}

instance [Zero R] : Zero (QUBO ι R) := ⟨⟨0, 0, 0⟩⟩
instance [Zero R] : Inhabited (QUBO ι R) := ⟨0⟩
instance [Add R] : Add (QUBO ι R) :=
  ⟨fun P Q ↦ ⟨P.quad + Q.quad, P.lin + Q.lin, P.const + Q.const⟩⟩
instance {S : Type*} [SMul S R] : SMul S (QUBO ι R) :=
  ⟨fun a Q ↦ ⟨a • Q.quad, a • Q.lin, a • Q.const⟩⟩

/-- Evaluates a QUBO instance at `z : ι → Bool`. -/
def eval [Fintype ι] [CommSemiring R] (Q : QUBO ι R) (z : ι → Bool) : R :=
  (∑ i, ∑ j, Q.quad i j * boolBit (z i) * boolBit (z j)) +
    (∑ i, Q.lin i * boolBit (z i)) + Q.const

@[simp]
theorem eval_add [Fintype ι] [CommSemiring R] (P Q : QUBO ι R) (z : ι → Bool) :
    (P + Q).eval z = P.eval z + Q.eval z := by
  change ((∑ i, ∑ j, (P.quad + Q.quad) i j * boolBit (z i) * boolBit (z j)) +
    (∑ i, (P.lin + Q.lin) i * boolBit (z i)) + (P.const + Q.const)) = _
  simp only [eval, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

@[simp]
theorem eval_smul [Fintype ι] [CommSemiring R] (a : R) (Q : QUBO ι R) (z : ι → Bool) :
    (a • Q).eval z = a * Q.eval z := by
  change ((∑ i, ∑ j, (a • Q.quad) i j * boolBit (z i) * boolBit (z j)) +
    (∑ i, (a • Q.lin) i * boolBit (z i)) + a * Q.const) = _
  simp only [eval, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

/-- Moves the diagonal of `Q.quad` into `Q.lin` using `z_i^2 = z_i`. -/
def extractDiag [DecidableEq ι] [Add R] [Zero R] (Q : QUBO ι R) : QUBO ι R where
  quad := Matrix.of fun i j ↦ if i = j then 0 else Q.quad i j
  lin i := Q.lin i + Q.quad i i
  const := Q.const

@[simp]
theorem eval_extractDiag [Fintype ι] [DecidableEq ι] [CommSemiring R] (Q : QUBO ι R)
    (z : ι → Bool) : Q.extractDiag.eval z = Q.eval z := by
  have hrow : ∀ i : ι,
      (∑ j, Q.extractDiag.quad i j * boolBit (z i) * boolBit (z j)) +
          Q.quad i i * boolBit (z i) =
        ∑ j, Q.quad i j * boolBit (z i) * boolBit (z j) := fun i ↦ by
    rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ Q.quad i j * boolBit (z i) * boolBit (z j)) (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ
        (fun j ↦ Q.extractDiag.quad i j * boolBit (z i) * boolBit (z j)) (Finset.mem_univ i),
      add_comm]
    simp only [extractDiag, Matrix.of_apply, ↓reduceIte, zero_mul, zero_add]
    congr 1
    · rw [mul_assoc, boolBit_mul_self]
    · exact Finset.sum_congr rfl fun j hj ↦ by simp [(Finset.ne_of_mem_erase hj).symm]
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) fun i _ ↦ hrow i
  simp only [Finset.sum_add_distrib, extractDiag] at hsum
  simp only [eval, extractDiag, add_mul, Finset.sum_add_distrib]
  calc
    (∑ x, ∑ j, (Matrix.of fun i j ↦ if i = j then 0 else Q.quad i j) x j *
          boolBit (z x) * boolBit (z j)) +
        ((∑ x, Q.lin x * boolBit (z x)) + ∑ x, Q.quad x x * boolBit (z x)) + Q.const
      = ((∑ x, ∑ j, (Matrix.of fun i j ↦ if i = j then 0 else Q.quad i j) x j *
            boolBit (z x) * boolBit (z j)) + ∑ x, Q.quad x x * boolBit (z x)) +
          (∑ x, Q.lin x * boolBit (z x)) + Q.const := by ring
    _ = (∑ i, ∑ j, Q.quad i j * boolBit (z i) * boolBit (z j)) +
          (∑ i, Q.lin i * boolBit (z i)) + Q.const := by rw [hsum]

/-- Absorbs `Q.lin` into the diagonal of `Q.quad`. -/
def absorbLinear [DecidableEq ι] [Add R] [Zero R] (Q : QUBO ι R) : QUBO ι R where
  quad := Q.quad + Matrix.diagonal Q.lin
  lin := 0
  const := Q.const

@[simp]
theorem eval_absorbLinear [Fintype ι] [DecidableEq ι] [CommSemiring R] (Q : QUBO ι R)
    (z : ι → Bool) : Q.absorbLinear.eval z = Q.eval z := by
  have hdiag :
      ∑ i : ι, ∑ j : ι, Matrix.diagonal Q.lin i j * boolBit (z i) * boolBit (z j) =
        ∑ i : ι, Q.lin i * boolBit (z i) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [Finset.sum_eq_single i]
      · simp [mul_assoc]
      · intro j _ hji; simp [Matrix.diagonal_apply_ne _ hji.symm]
      · intro hi; exact absurd (Finset.mem_univ i) hi
  simp [eval, absorbLinear, add_mul, Finset.sum_add_distrib, hdiag]

/-- Undirected quadratic interaction graph of a QUBO instance. -/
def couplingGraph [AddCommMonoid R] (Q : QUBO ι R) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ Q.quad i j + Q.quad j i ≠ 0
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [add_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end QUBO

/-- A classical Ising spin-glass energy form on `ι` over `R`. -/
@[ext]
structure IsingForm (ι : Type u) (R : Type v) where
  /-- Pairwise spin coupling matrix `J_{i,j}`. -/
  coupling : Matrix ι ι R
  /-- Longitudinal external field `h_i`. -/
  field : ι → R
  /-- Constant offset `E_0`. -/
  const : R

namespace IsingForm

variable {ι : Type u} {R : Type v}

/-- Evaluates an Ising form at `z : ι → Bool` via `σ_i = 2 z_i - 1`. -/
def eval [Fintype ι] [CommRing R] (M : IsingForm ι R) (z : ι → Bool) : R :=
  (∑ i, ∑ j, M.coupling i j * boolSpin (z i) * boolSpin (z j)) +
    (∑ i, M.field i * boolSpin (z i)) + M.const

/-- Undirected spin-spin coupling graph of an Ising form. -/
def couplingGraph [AddCommMonoid R] (M : IsingForm ι R) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ M.coupling i j + M.coupling j i ≠ 0
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [add_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Converts an Ising form into an equivalent QUBO via `σ_i = 2 z_i - 1`. -/
def toQUBO [Fintype ι] [CommRing R] (M : IsingForm ι R) : QUBO ι R where
  quad := Matrix.of fun i j ↦ 4 * M.coupling i j
  lin i := 2 * M.field i - 2 * ∑ j, (M.coupling i j + M.coupling j i)
  const := M.const - (∑ i, M.field i) + ∑ i, ∑ j, M.coupling i j

@[simp]
theorem eval_toQUBO [Fintype ι] [CommRing R] (M : IsingForm ι R) (z : ι → Bool) :
    M.toQUBO.eval z = M.eval z := by
  simp only [eval, QUBO.eval, toQUBO, Matrix.of_apply, boolSpin_eq_two_mul_boolBit_sub_one]
  have hexp : ∀ i j : ι,
      M.coupling i j * (2 * boolBit (z i) - 1) * (2 * boolBit (z j) - 1) =
        ((4 * M.coupling i j * boolBit (z i) * boolBit (z j) -
            2 * M.coupling i j * boolBit (z i)) -
          2 * M.coupling i j * boolBit (z j)) + M.coupling i j := fun _ _ ↦ by ring
  have h2 : ∑ i : ι, ∑ j : ι, 2 * M.coupling i j * boolBit (z j) =
      ∑ i : ι, 2 * (∑ j, M.coupling j i) * boolBit (z i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ i : ι, ∑ j : ι, 2 * M.coupling i j * boolBit (z i) =
      2 * (∑ j, M.coupling i j) * boolBit (z i) := fun _ ↦ by rw [Finset.mul_sum, Finset.sum_mul]
  have hlin :
      ∑ i : ι, (2 * M.field i - 2 * ((∑ j, M.coupling i j) + ∑ j, M.coupling j i)) *
          boolBit (z i) =
        (∑ i, 2 * M.field i * boolBit (z i)) -
          (∑ i, 2 * (∑ j, M.coupling i j) * boolBit (z i)) -
          ∑ i, 2 * (∑ j, M.coupling j i) * boolBit (z i) := by
    simp_rw [show ∀ i : ι,
      (2 * M.field i - 2 * ((∑ j, M.coupling i j) + ∑ j, M.coupling j i)) * boolBit (z i) =
        (2 * M.field i * boolBit (z i) - 2 * (∑ j, M.coupling i j) * boolBit (z i)) -
          2 * (∑ j, M.coupling j i) * boolBit (z i) from fun _ ↦ by ring,
      Finset.sum_sub_distrib]
  have hfield :
      ∑ i : ι, M.field i * (2 * boolBit (z i) - 1) =
        (∑ i, 2 * M.field i * boolBit (z i)) - ∑ i, M.field i := by
    simp_rw [show ∀ i : ι, M.field i * (2 * boolBit (z i) - 1) =
      2 * M.field i * boolBit (z i) - M.field i from fun _ ↦ by ring, Finset.sum_sub_distrib]
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  rw [hlin, hfield]
  ring

end IsingForm

/-- Converts a QUBO into a canonical zero-diagonal Ising form over any field (with exact equality
over characteristic-zero fields such as `ℚ`, `ℝ`) via `z_i = (σ_i + 1) / 2`. -/
def QUBO.toIsing {ι : Type u} {R : Type v} [Fintype ι] [DecidableEq ι] [Field R]
    (Q : QUBO ι R) : IsingForm ι R :=
  let Q₀ := Q.extractDiag
  { coupling := Matrix.of fun i j ↦ Q₀.quad i j / 4
    field := fun i ↦ Q₀.lin i / 2 + (∑ j, (Q₀.quad i j + Q₀.quad j i)) / 4
    const := Q₀.const + (∑ i, Q₀.lin i) / 2 + (∑ i, ∑ j, Q₀.quad i j) / 4 }

@[simp]
theorem QUBO.eval_toIsing {ι : Type u} {R : Type v} [Fintype ι] [DecidableEq ι] [Field R]
    [CharZero R] (Q : QUBO ι R) (z : ι → Bool) : Q.toIsing.eval z = Q.eval z := by
  rw [← Q.eval_extractDiag z]
  set Q₀ := Q.extractDiag
  change IsingForm.eval
    { coupling := Matrix.of fun i j ↦ Q₀.quad i j / 4
      field := fun i ↦ Q₀.lin i / 2 + (∑ j, (Q₀.quad i j + Q₀.quad j i)) / 4
      const := Q₀.const + (∑ i, Q₀.lin i) / 2 + (∑ i, ∑ j, Q₀.quad i j) / 4 } z = Q₀.eval z
  rw [← IsingForm.eval_toQUBO]
  have hlin : ∀ i : ι,
      2 * (Q₀.lin i / 2 + (∑ j, (Q₀.quad i j + Q₀.quad j i)) / 4) -
          2 * ∑ j, (Q₀.quad i j / 4 + Q₀.quad j i / 4) = Q₀.lin i := fun i ↦ by
    have hs : ∑ j, (Q₀.quad i j / 4 + Q₀.quad j i / 4) =
        (∑ j, (Q₀.quad i j + Q₀.quad j i)) / 4 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hs]; ring
  have hconst :
      Q₀.const + (∑ i, Q₀.lin i) / 2 + (∑ i, ∑ j, Q₀.quad i j) / 4 -
          (∑ i, (Q₀.lin i / 2 + (∑ j, (Q₀.quad i j + Q₀.quad j i)) / 4)) +
          (∑ i, ∑ j, Q₀.quad i j / 4) = Q₀.const := by
    have hs3 : ∑ i, (∑ j, (Q₀.quad i j + Q₀.quad j i)) / 4 =
        2 * ((∑ i, ∑ j, Q₀.quad i j) / 4) := by
      rw [← Finset.sum_div]
      have hswap : ∑ i, ∑ j, Q₀.quad j i = ∑ i, ∑ j, Q₀.quad i j := Finset.sum_comm
      have hadd : ∑ i, ∑ j, (Q₀.quad i j + Q₀.quad j i) =
          (∑ i, ∑ j, Q₀.quad i j) + ∑ i, ∑ j, Q₀.quad j i := by
        simp_rw [Finset.sum_add_distrib]
      rw [hadd, hswap]; ring
    have hs4 : ∑ i, ∑ j, Q₀.quad i j / 4 = (∑ i, ∑ j, Q₀.quad i j) / 4 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ ↦ (Finset.sum_div _ _ _).symm
    rw [Finset.sum_add_distrib, ← Finset.sum_div, hs3, hs4]; ring
  simp only [QUBO.eval, IsingForm.toQUBO, Matrix.of_apply,
    show ∀ i j, 4 * (Q₀.quad i j / 4) = Q₀.quad i j from fun _ _ ↦ by ring, hlin, hconst]

@[simp]
theorem QUBO.couplingGraph_toIsing {ι : Type u} {R : Type v} [Fintype ι] [DecidableEq ι] [Field R]
    [CharZero R] (Q : QUBO ι R) : Q.toIsing.couplingGraph = Q.couplingGraph := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [IsingForm.couplingGraph, QUBO.couplingGraph]
  · simp only [IsingForm.couplingGraph, QUBO.couplingGraph, QUBO.toIsing, QUBO.extractDiag,
      Matrix.of_apply, hij, Ne.symm hij, ↓reduceIte]
    rw [show Q.quad i j / 4 + Q.quad j i / 4 = (Q.quad i j + Q.quad j i) / 4 by ring]
    exact and_congr_right fun _ ↦ div_ne_zero_iff.trans (and_iff_left (by norm_num : (4 : R) ≠ 0))

/-- One-hot permutation matrix of `π : Equiv.Perm α`. -/
def permOneHot {α : Type u} [DecidableEq α] (π : Equiv.Perm α) : Matrix α α Bool :=
  Matrix.of fun i j ↦ decide (π j = i)

/-- Two-way assignment constraint (`∑_i z_{i,j} = 1` and `∑_j z_{i,j} = 1`). -/
def IsAssignmentMatrix {α : Type u} [Fintype α] (z : Matrix α α Bool) : Prop :=
  (∀ j, ∑ i, (boolBit (z i j) : ℕ) = 1) ∧ ∀ i, ∑ j, (boolBit (z i j) : ℕ) = 1

/-- Two-way quadratic assignment penalty over `ℚ`. -/
def assignmentPenalty {α : Type u} [Fintype α] (z : Matrix α α Bool) : ℚ :=
  (∑ j, ((∑ i, (boolBit (z i j) : ℚ)) - 1) ^ 2) +
    ∑ i, ((∑ j, (boolBit (z i j) : ℚ)) - 1) ^ 2

/-- QUBO representation of `assignmentPenalty` over `ℚ`. -/
def assignmentPenaltyQUBO (α : Type u) [Fintype α] [DecidableEq α] : QUBO (α × α) ℚ where
  quad := Matrix.of fun u v ↦
    (if u.2 = v.2 ∧ u.1 ≠ v.1 then (1 : ℚ) else 0) +
      if u.1 = v.1 ∧ u.2 ≠ v.2 then (1 : ℚ) else 0
  lin _ := -2
  const := 2 * (Fintype.card α : ℚ)

theorem isAssignmentMatrix_permOneHot {α : Type u} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) : IsAssignmentMatrix (permOneHot π) := by
  refine ⟨fun j ↦ ?_, fun i ↦ ?_⟩
  · rw [Finset.sum_eq_single (π j)]
    · simp [permOneHot]
    · intro i _ hi; simp [permOneHot, Ne.symm hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (π.symm i)]
    · simp [permOneHot]
    · intro j _ hj
      have : π j ≠ i := fun h ↦ hj ((Equiv.eq_symm_apply π).mpr h)
      simp [permOneHot, this]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem isAssignmentMatrix_iff_exists_perm {α : Type u} [Fintype α] [DecidableEq α]
    (z : Matrix α α Bool) :
    IsAssignmentMatrix z ↔ ∃ π : Equiv.Perm α, z = permOneHot π := by
  refine ⟨fun ⟨hcol, hrow⟩ ↦ ?_, fun ⟨π, h⟩ ↦ h ▸ isAssignmentMatrix_permOneHot π⟩
  have huniq : ∀ f : α → Bool, ∑ x, (boolBit (f x) : ℕ) = 1 → ∃! x, f x = true := fun f hf ↦ by
    have hcard : (Finset.univ.filter fun x ↦ f x = true).card = 1 := by
      rw [Finset.card_filter]; convert hf using 2 with x; cases f x <;> rfl
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    refine ⟨a, ?_, fun y hy ↦ ?_⟩
    · have hmem : a ∈ Finset.univ.filter fun x ↦ f x = true := by
        rw [ha]; exact Finset.mem_singleton_self a
      exact (Finset.mem_filter.mp hmem).2
    · have hmem : y ∈ ({a} : Finset α) := by
        rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
      exact Finset.mem_singleton.mp hmem
  have hcu := fun j ↦ huniq _ (hcol j)
  have hru := fun i ↦ huniq _ (hrow i)
  let π : Equiv.Perm α :=
    { toFun := fun j ↦ (hcu j).choose
      invFun := fun i ↦ (hru i).choose
      left_inv := fun j ↦ ((hru (hcu j).choose).choose_spec.2 j (hcu j).choose_spec.1).symm
      right_inv := fun i ↦ ((hcu (hru i).choose).choose_spec.2 i (hru i).choose_spec.1).symm }
  refine ⟨π, Matrix.ext fun i j ↦ ?_⟩
  cases hzij : z i j
  · have : π j ≠ i := fun he ↦ by
      have ht : z (π j) j = true := (hcu j).choose_spec.1
      rw [he, hzij] at ht; cases ht
    simp [permOneHot, this]
  · have : π j = i := ((hcu j).choose_spec.2 i hzij).symm
    simp [permOneHot, this]

theorem assignmentPenalty_eq_zero_iff {α : Type u} [Fintype α] (z : Matrix α α Bool) :
    assignmentPenalty z = 0 ↔ IsAssignmentMatrix z := by
  unfold assignmentPenalty IsAssignmentMatrix
  rw [add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _]
  have hsq : ∀ s : ℕ, ((s : ℚ) - 1) ^ 2 = 0 ↔ s = 1 := fun s ↦ by
    rw [sq_eq_zero_iff, sub_eq_zero]; exact_mod_cast Iff.rfl
  simp_rw [Finset.mem_univ, forall_true_left, ← cast_boolBit_nat (R := ℚ), ← Nat.cast_sum, hsq]

theorem one_le_assignmentPenalty_of_not {α : Type u} [Fintype α] {z : Matrix α α Bool}
    (hz : ¬IsAssignmentMatrix z) : 1 ≤ assignmentPenalty z := by
  have hone : ∀ s : ℕ, s ≠ 1 → (1 : ℚ) ≤ ((s : ℚ) - 1) ^ 2 := fun s hs ↦ by
    have hZ : (1 : ℤ) ≤ ((s : ℤ) - 1) ^ 2 := by
      have : (1 : ℤ) ≤ |(s : ℤ) - 1| := Int.one_le_abs (by omega)
      nlinarith [sq_abs ((s : ℤ) - 1)]
    exact_mod_cast hZ
  have hnot : (∃ j, ∑ i, (boolBit (z i j) : ℕ) ≠ 1) ∨ ∃ i, ∑ j, (boolBit (z i j) : ℕ) ≠ 1 := by
    by_contra h; push Not at h; exact hz h
  unfold assignmentPenalty
  simp_rw [← cast_boolBit_nat (R := ℚ), ← Nat.cast_sum]
  rcases hnot with ⟨j, hj⟩ | ⟨i, hi⟩
  · have hsingle :
        (((∑ i, (boolBit (z i j) : ℕ) : ℕ) : ℚ) - 1) ^ 2 ≤
          ∑ j' : α, (((∑ i, (boolBit (z i j') : ℕ) : ℕ) : ℚ) - 1) ^ 2 :=
      Finset.single_le_sum (f := fun j' ↦ (((∑ i, (boolBit (z i j') : ℕ) : ℕ) : ℚ) - 1) ^ 2)
        (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    exact le_trans (hone _ hj)
      (le_add_of_le_of_nonneg hsingle (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  · have hsingle :
        (((∑ j, (boolBit (z i j) : ℕ) : ℕ) : ℚ) - 1) ^ 2 ≤
          ∑ i' : α, (((∑ j, (boolBit (z i' j) : ℕ) : ℕ) : ℚ) - 1) ^ 2 :=
      Finset.single_le_sum (f := fun i' ↦ (((∑ j, (boolBit (z i' j) : ℕ) : ℕ) : ℚ) - 1) ^ 2)
        (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)
    exact le_trans (hone _ hi)
      (le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hsingle)

theorem eval_assignmentPenaltyQUBO {α : Type u} [Fintype α] [DecidableEq α]
    (z : Matrix α α Bool) :
    (assignmentPenaltyQUBO α).eval (Function.uncurry z) = assignmentPenalty z := by
  have hexp : ∀ f : α → Bool,
      ((∑ x, (boolBit (f x) : ℚ)) - 1) ^ 2 =
        (∑ x, ∑ y, (if x ≠ y then (1 : ℚ) else 0) * boolBit (f x) * boolBit (f y)) -
          (∑ x, boolBit (f x)) + 1 := fun f ↦ by
    have hsq : (∑ x, (boolBit (f x) : ℚ)) ^ 2 =
        (∑ x, ∑ y, (if x ≠ y then (1 : ℚ) else 0) * boolBit (f x) * boolBit (f y)) +
          ∑ x, boolBit (f x) := by
      rw [sq, Finset.sum_mul_sum]
      simp_rw [show ∀ x : α, ∑ y, (boolBit (f x) : ℚ) * boolBit (f y) =
          (∑ y, (if x ≠ y then (1 : ℚ) else 0) * boolBit (f x) * boolBit (f y)) + boolBit (f x)
        from fun x ↦ by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), boolBit_mul_self, add_comm]
          congr 1
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
          simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_mul, zero_add]
          exact Finset.sum_congr rfl fun y hy ↦ by simp [(Finset.ne_of_mem_erase hy).symm],
        Finset.sum_add_distrib]
    linarith [show ((∑ x, (boolBit (f x) : ℚ)) - 1) ^ 2 =
      (∑ x, (boolBit (f x) : ℚ)) ^ 2 - 2 * ∑ x, (boolBit (f x) : ℚ) + 1 by ring]
  unfold assignmentPenalty assignmentPenaltyQUBO QUBO.eval
  simp only [Fintype.sum_prod_type, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, hexp, Finset.sum_sub_distrib]
  have hunc : ∀ i j : α, Function.uncurry z (i, j) = z i j := fun _ _ ↦ rfl
  simp only [hunc]
  have h1 : ∑ j : α, ∑ i : α, ∑ i' : α,
      (if i ≠ i' then (1 : ℚ) else 0) * boolBit (z i j) * boolBit (z i' j) =
    ∑ i, ∑ j, ∑ i', ∑ j',
      (if j = j' ∧ i ≠ i' then (1 : ℚ) else 0) * boolBit (z i j) * boolBit (z i' j') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun i' _ ↦ ?_
    rw [Finset.sum_eq_single j] <;> simp +contextual [eq_comm]
  have h2 : ∑ i : α, ∑ j : α, ∑ j' : α,
      (if j ≠ j' then (1 : ℚ) else 0) * boolBit (z i j) * boolBit (z i j') =
    ∑ i, ∑ j, ∑ i', ∑ j',
      (if i = i' ∧ j ≠ j' then (1 : ℚ) else 0) * boolBit (z i j) * boolBit (z i' j') :=
    Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ ↦ ?_
      rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]
  have hlin : ∑ i : α, ∑ j : α, (-2 : ℚ) * boolBit (z i j) =
      -(2 * ∑ i : α, ∑ j : α, (boolBit (z i j) : ℚ)) := by
    simp_rw [show ∀ q : ℚ, (-2 : ℚ) * q = -(2 * q) from fun _ ↦ by ring, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
  have hcomm : ∑ j : α, ∑ i : α, (boolBit (z i j) : ℚ) =
      ∑ i : α, ∑ j : α, (boolBit (z i j) : ℚ) := Finset.sum_comm
  rw [h1, h2, hcomm, hlin]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- Lucas QUBO encoding of a nonempty `Cslib.Complexity.TSPInstance` on `n²` binary variables
(`n = x.dist.length`), using penalty weight `x.bound + 1`. -/
def tspToQUBO (x : Cslib.Complexity.TSPInstance) (hn : 0 < x.dist.length) :
    QUBO (Fin x.dist.length × Fin x.dist.length) ℚ :=
  let n := x.dist.length
  let next : Fin n → Fin n := fun k ↦ ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩
  let tourQ : QUBO (Fin n × Fin n) ℚ :=
    { quad := Matrix.of fun u v ↦
        if v.2 = next u.2 then (Cslib.Complexity.TSP.dist x.dist u.1.val v.1.val : ℚ) else 0
      lin := 0
      const := 0 }
  tourQ + ((x.bound : ℚ) + 1) • assignmentPenaltyQUBO (Fin n)

/-- Lucas Ising encoding of a nonempty `Cslib.Complexity.TSPInstance`. -/
def tspToIsing (x : Cslib.Complexity.TSPInstance) (hn : 0 < x.dist.length) :
    IsingForm (Fin x.dist.length × Fin x.dist.length) ℚ :=
  (tspToQUBO x hn).toIsing

/-- **Exact TSP-to-QUBO reduction**: for every nonempty `x : TSPInstance`, `x ∈ TSP` if and only if
some `n²`-bit assignment satisfies `(tspToQUBO x hn).eval z ≤ x.bound`. -/
theorem mem_TSP_iff_exists_qubo_le (x : Cslib.Complexity.TSPInstance) (hn : 0 < x.dist.length) :
    x ∈ Cslib.Complexity.TSP ↔
      ∃ z : Fin x.dist.length × Fin x.dist.length → Bool,
        (tspToQUBO x hn).eval z ≤ (x.bound : ℚ) := by
  set n := x.dist.length
  let next : Fin n → Fin n := fun k ↦ ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩
  let tourQ : QUBO (Fin n × Fin n) ℚ :=
    { quad := Matrix.of fun u v ↦
        if v.2 = next u.2 then (Cslib.Complexity.TSP.dist x.dist u.1.val v.1.val : ℚ) else 0
      lin := 0
      const := 0 }
  have hdecomp : ∀ w : Matrix (Fin n) (Fin n) Bool,
      (tspToQUBO x hn).eval (Function.uncurry w) =
        tourQ.eval (Function.uncurry w) + ((x.bound : ℚ) + 1) * assignmentPenalty w := fun w ↦ by
    rw [tspToQUBO, QUBO.eval_add, QUBO.eval_smul, eval_assignmentPenaltyQUBO w]
  have hperm_eval : ∀ π : Equiv.Perm (Fin n),
      (tspToQUBO x hn).eval (Function.uncurry (permOneHot π)) =
        ((Cslib.Complexity.TSP.tourLength x.dist
          (List.ofFn fun k : Fin n ↦ (π k).val) : ℕ) : ℚ) := by
    intro π
    rw [hdecomp, (assignmentPenalty_eq_zero_iff _).mpr (isAssignmentMatrix_permOneHot π),
      mul_zero, add_zero]
    simp only [tourQ, QUBO.eval, Fintype.sum_prod_type, Matrix.of_apply, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    have hunc : ∀ i α : Fin n, Function.uncurry (permOneHot π) (i, α) = permOneHot π i α :=
      fun _ _ ↦ rfl
    simp only [hunc]
    have hsum :
        (∑ i : Fin n, ∑ α : Fin n, ∑ j : Fin n, ∑ β : Fin n,
            (if β = next α then (Cslib.Complexity.TSP.dist x.dist i.val j.val : ℚ) else 0) *
              boolBit (permOneHot π i α) * boolBit (permOneHot π j β)) =
          ∑ α : Fin n, (Cslib.Complexity.TSP.dist x.dist (π α).val (π (next α)).val : ℚ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [Finset.sum_eq_single (π α)]
      · rw [Finset.sum_eq_single (π (next α))]
        · rw [Finset.sum_eq_single (next α)]
          · simp [permOneHot]
          · intro β _ hβ; simp [hβ]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro j _ hj
          exact Finset.sum_eq_zero fun β _ ↦ by
            by_cases hβ : β = next α
            · subst hβ; simp [permOneHot, Ne.symm hj]
            · simp [hβ]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro i _ hi
        exact Finset.sum_eq_zero fun j _ ↦ Finset.sum_eq_zero fun β _ ↦ by
          simp [permOneHot, Ne.symm hi]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]
    let p := List.ofFn fun k : Fin n ↦ (π k).val
    have hzip : List.zipWith (Cslib.Complexity.TSP.dist x.dist) p (p.rotate 1) =
        List.ofFn fun k : Fin n ↦ Cslib.Complexity.TSP.dist x.dist (π k).val (π (next k)).val := by
      apply List.ext_getElem (by simp [p])
      intro k _ hk2
      rw [List.getElem_zipWith, List.getElem_rotate, List.getElem_ofFn]
      simp [p, next]
    change _ = (((List.zipWith (Cslib.Complexity.TSP.dist x.dist) p (p.rotate 1)).sum : ℕ) : ℚ)
    rw [hzip, List.sum_ofFn, Nat.cast_sum]
  constructor
  · rintro ⟨p, hp, hle⟩
    have hplen : p.length = n := by simpa using hp.length_eq
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range
    let f : Fin n → Fin n := fun k ↦
      ⟨p[k.val]'(by omega), List.mem_range.mp (hp.subset (List.getElem_mem _))⟩
    have hinj : Function.Injective f := fun a b h ↦
      Fin.ext ((hnodup.getElem_inj_iff (hi := by omega) (hj := by omega)).mp
        (congr_arg Fin.val h))
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    have hpeq : p = List.ofFn fun k : Fin n ↦ (π k).val :=
      List.ext_getElem (by simp [hplen]) fun k _ _ ↦ by simp [π, f]
    refine ⟨Function.uncurry (permOneHot π), ?_⟩
    rw [hperm_eval, ← hpeq]
    exact_mod_cast hle
  · rintro ⟨u, hle⟩
    let z : Matrix (Fin n) (Fin n) Bool := Matrix.of (Function.curry u)
    have hu : u = Function.uncurry z := by ext ⟨i, α⟩; rfl
    rw [hu] at hle
    have hvalid : IsAssignmentMatrix z := by
      by_contra hnot
      have hpen : (1 : ℚ) ≤ assignmentPenalty z := one_le_assignmentPenalty_of_not hnot
      have htour_nn : (0 : ℚ) ≤ tourQ.eval (Function.uncurry z) := by
        simp only [tourQ, QUBO.eval, Matrix.of_apply, Pi.zero_apply, zero_mul,
          Finset.sum_const_zero, add_zero]
        refine Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦ ?_
        have hba : (boolBit (Function.uncurry z a) : ℚ) = boolBit (z a.1 a.2) := rfl
        have hbb : (boolBit (Function.uncurry z b) : ℚ) = boolBit (z b.1 b.2) := rfl
        rw [hba, hbb]
        by_cases h : b.2 = next a.2 <;> cases z a.1 a.2 <;> cases z b.1 b.2 <;> simp [h]
      have hmul : (x.bound : ℚ) + 1 ≤ ((x.bound : ℚ) + 1) * assignmentPenalty z := by
        simpa using mul_le_mul_of_nonneg_left hpen (by positivity)
      rw [hdecomp] at hle
      linarith
    obtain ⟨π, hzπ⟩ := (isAssignmentMatrix_iff_exists_perm z).mp hvalid
    rw [hzπ, hperm_eval] at hle
    have hle_nat :
        Cslib.Complexity.TSP.tourLength x.dist (List.ofFn fun k : Fin n ↦ (π k).val) ≤ x.bound :=
      Nat.cast_le (α := ℚ).mp hle
    refine ⟨List.ofFn fun k : Fin n ↦ (π k).val, ?_, hle_nat⟩
    refine (List.perm_ext_iff_of_nodup
      (List.nodup_ofFn.mpr fun a b h ↦ π.injective (Fin.ext h)) List.nodup_range).mpr fun v ↦ ?_
    simp only [List.mem_ofFn, List.mem_range]
    exact ⟨fun ⟨k, hk⟩ ↦ hk ▸ (π k).isLt, fun hv ↦ ⟨π.symm ⟨v, hv⟩, by simp⟩⟩

/-- **Exact TSP-to-Ising reduction**: for every nonempty `x : TSPInstance`, `x ∈ TSP` if and only if
some `n²`-spin configuration satisfies `(tspToIsing x hn).eval z ≤ x.bound`. -/
theorem mem_TSP_iff_exists_ising_le (x : Cslib.Complexity.TSPInstance) (hn : 0 < x.dist.length) :
    x ∈ Cslib.Complexity.TSP ↔
      ∃ z : Fin x.dist.length × Fin x.dist.length → Bool,
        (tspToIsing x hn).eval z ≤ (x.bound : ℚ) := by
  simp_rw [tspToIsing, QUBO.eval_toIsing]
  exact mem_TSP_iff_exists_qubo_le x hn

end CslibFrontier.Complexity
