module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Data.Matrix.Mul

import CslibFrontier.Computability.Complexity.FineGrained.ExhaustiveSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Foundations.Data.Int.Radix
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.LinearAlgebra.Matrix.IntegerKernel
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Fixed-Parameter Tractability of Bounded-System Integer Linear Feasibility

This module proves under standard Lean axioms that integer linear inequality feasibility
`A u ≤ b` (`BoundedEntryILP`) is fixed-parameter tractable parameterized by the number of
variables `p`, the number of constraints `R`, and the maximum bit-length (or magnitude) of active
matrix entries, with arbitrary unbounded binary right-hand side `b : List ℤ`:

* **RHS-independent small integer-linear-combination certificate**: minimizing a radix-weighted
  objective `∑_j x_j (K + 1)^j` over nonnegative equality solutions `A' x = b` yields a solution
  whose large support has `ℚ`-linearly independent columns. Forming the padded Gram matrix `G` on
  the large support and multiplying by `adjugate G` expresses `x - z = (W *ᵥ (b - A' *ᵥ z)) / d`
  for an integer tuple `(z, d, W)` whose bit-length depends only on `(p, R, maxEntryBits A)` and is
  independent of `b`.
* **Polynomial-time verification and exhaustive search (`BoundedEntryILP_decidableInPowerExpTime`,
  `BoundedEntryILP_mem_FPT`, `BoundedEntryILP_mem_FPT_magnitude`)**: unpacking `(z, d, W)`,
  evaluating integer truncated division via `binary_div`, and verifying `A *ᵥ u ≤ b` yields a
  `2 ^ O((p + R + L)^4) * poly(|I|)` multi-tape Turing-machine decider (`BoundedEntryILP ∈ FPT`).
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime
open scoped Nat Matrix

/-- Encoding of a matrix `List (List ℤ)` with binary-encoded entries. -/
abbrev encIntMatrix : List (List ℤ) ↪ List Bool :=
  encList (encList encIntBin)

/-- An instance of integer linear inequality feasibility `A u ≤ b` (`u : Fin numVars → ℤ`). -/
@[ext]
structure BoundedILPInstance where
  /-- Number of integer variables `p` (encoded in unary). -/
  numVars : ℕ
  /-- Constraint matrix rows `A` (entries encoded in binary). -/
  matrix : List (List ℤ)
  /-- Right-hand side vector `b` (entries encoded in binary, unbounded). -/
  rhs : List ℤ
  deriving DecidableEq, Repr, Inhabited

/-- Binary encoding of `BoundedILPInstance`. -/
enc_structure encBoundedILP : BoundedILPInstance where
  numVars : encUnary,
  matrix : encIntMatrix,
  rhs : (encList encIntBin)

attribute [local fun_prop] encBoundedILP_numVars_polyTime encBoundedILP_matrix_polyTime
  encBoundedILP_rhs_polyTime encBoundedILP_mk_polyTime

/-- Active `R × p` integer matrix of `I : BoundedILPInstance`. -/
@[expose]
def ilpMatrix (I : BoundedILPInstance) : Matrix (Fin I.matrix.length) (Fin I.numVars) ℤ :=
  Matrix.of fun i j ↦ (I.matrix[i.1]).getD j.1 0

/-- Active `R`-dimensional right-hand side vector of `I : BoundedILPInstance`. -/
@[expose]
def ilpRhs (I : BoundedILPInstance) : Fin I.matrix.length → ℤ :=
  fun i ↦ I.rhs.getD i.1 0

/-- **Integer Linear Inequality Feasibility**: the set of
instances `I = (p, A, b)` admitting `u : Fin p → ℤ` with `A *ᵥ u ≤ b`. -/
@[expose]
def BoundedEntryILP : Set BoundedILPInstance :=
  {I | ∃ u : Fin I.numVars → ℤ, ilpMatrix I *ᵥ u ≤ ilpRhs I}

/-- Row-wise unfolding of `I ∈ BoundedEntryILP`. -/
theorem mem_BoundedEntryILP_iff (I : BoundedILPInstance) :
    I ∈ BoundedEntryILP ↔
      ∃ u : Fin I.numVars → ℤ, ∀ i (hi : i < I.matrix.length),
        ∑ j : Fin I.numVars, (I.matrix[i]).getD j.1 0 * u j ≤ I.rhs.getD i 0 := by
  change (∃ u : Fin I.numVars → ℤ, ∀ i : Fin I.matrix.length,
      ∑ j : Fin I.numVars, (I.matrix[i.1]).getD j.1 0 * u j ≤ I.rhs.getD i.1 0) ↔ _
  exact ⟨fun ⟨u, h⟩ ↦ ⟨u, fun i hi ↦ h ⟨i, hi⟩⟩,
    fun ⟨u, h⟩ ↦ ⟨u, fun ⟨i, hi⟩ ↦ h i hi⟩⟩

/-- Maximum binary length `e.natAbs.size` among active entries `A_{i, j}`
(`i < matrix.length`, `j < numVars`). -/
@[expose]
def maxActiveEntryBits (I : BoundedILPInstance) : ℕ :=
  ((List.range I.matrix.length).flatMap fun i ↦
    (List.range I.numVars).map fun j ↦
      ((I.matrix.getD i []).getD j 0).natAbs.size).foldl max 0

/-- Maximum absolute magnitude `e.natAbs` among active entries `A_{i, j}`
(`i < matrix.length`, `j < numVars`). -/
@[expose]
def maxActiveEntryNatAbs (I : BoundedILPInstance) : ℕ :=
  ((List.range I.matrix.length).flatMap fun i ↦
    (List.range I.numVars).map fun j ↦
      ((I.matrix.getD i []).getD j 0).natAbs).foldl max 0

/-- Structural ILP parameter `numVars + numRows + maxActiveEntryBits`. -/
@[expose]
def ilpParam (I : BoundedILPInstance) : ℕ :=
  I.numVars + I.matrix.length + maxActiveEntryBits I

/-- Magnitude ILP parameter `numVars + numRows + maxActiveEntryNatAbs`. -/
@[expose]
def ilpMagnitudeParam (I : BoundedILPInstance) : ℕ :=
  I.numVars + I.matrix.length + maxActiveEntryNatAbs I

/-- Equation for `ilpMagnitudeParam`. -/
theorem ilpMagnitudeParam_eq (I : BoundedILPInstance) :
    ilpMagnitudeParam I = I.numVars + I.matrix.length + maxActiveEntryNatAbs I := rfl

/-- When `I.numVars = 0`, `maxActiveEntryNatAbs I = 0`. -/
theorem maxActiveEntryNatAbs_of_numVars_eq_zero {I : BoundedILPInstance}
    (h : I.numVars = 0) : maxActiveEntryNatAbs I = 0 := by
  unfold maxActiveEntryNatAbs
  rw [h]
  simp only [List.range_zero, List.map_nil]
  induction List.range I.matrix.length with
  | nil => rfl
  | cons _ _ ih => exact ih

private lemma le_foldl_max_init (l : List ℕ) (init : ℕ) :
    init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    obtain ⟨h1, h2⟩ := ih (max init a)
    refine ⟨(Nat.le_max_left init a).trans h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (Nat.le_max_right init x).trans h1
    · exact h2 x hx

private lemma foldl_max_mono_list {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (hle : ∀ k (hk₁ : k < l₁.length) (hk₂ : k < l₂.length), l₁[k] ≤ l₂[k]) (init₁ init₂ : ℕ)
    (hinit : init₁ ≤ init₂) :
    l₁.foldl max init₁ ≤ l₂.foldl max init₂ := by
  induction l₁ generalizing l₂ init₁ init₂ with
  | nil =>
    cases l₂ with
    | nil => exact hinit
    | cons _ _ => simp at hlen
  | cons a₁ as₁ ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons a₂ as₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ha : a₁ ≤ a₂ := hle 0 (by simp) (by simp)
      exact ih hlen (fun k hk₁ hk₂ ↦ hle (k + 1) (by simpa using hk₁) (by simpa using hk₂))
        (max init₁ a₁) (max init₂ a₂) (max_le_max hinit ha)

theorem maxActiveEntryBits_le_maxActiveEntryNatAbs (I : BoundedILPInstance) :
    maxActiveEntryBits I ≤ maxActiveEntryNatAbs I := by
  unfold maxActiveEntryBits maxActiveEntryNatAbs
  have heq :
      ((List.range I.matrix.length).flatMap fun i ↦
        (List.range I.numVars).map fun j ↦ ((I.matrix.getD i []).getD j 0).natAbs.size) =
      (((List.range I.matrix.length).flatMap fun i ↦
        (List.range I.numVars).map fun j ↦ ((I.matrix.getD i []).getD j 0).natAbs)).map
        Nat.size := by
    simp [List.map_flatMap, List.map_map, Function.comp_def]
  rw [heq]
  exact foldl_max_mono_list (by simp) (fun k _ _ ↦ by simp [Nat.size_le_self]) 0 0 le_rfl

theorem ilpParam_le_ilpMagnitudeParam (I : BoundedILPInstance) :
    ilpParam I ≤ ilpMagnitudeParam I := by
  have := maxActiveEntryBits_le_maxActiveEntryNatAbs I
  unfold ilpParam ilpMagnitudeParam
  omega

theorem maxActiveEntryNatAbs_le_of_forall (I : BoundedILPInstance) {B : ℕ}
    (hB : ∀ i (hi : i < I.matrix.length) j, j < I.numVars →
      ((I.matrix[i]).getD j 0).natAbs ≤ B) :
    maxActiveEntryNatAbs I ≤ B := by
  have hfold : ∀ (l : List ℕ) (init : ℕ), init ≤ B → (∀ x ∈ l, x ≤ B) → l.foldl max init ≤ B := by
    intro l
    induction l with
    | nil => intro init hinit _; exact hinit
    | cons a as ih =>
      intro init hinit hall
      exact ih (max init a) (max_le hinit (hall a List.mem_cons_self))
        fun x hx ↦ hall x (List.mem_cons_of_mem a hx)
  refine hfold _ 0 (Nat.zero_le B) fun x hx ↦ ?_
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨i, hi, j, hj, rfl⟩ := hx
  rw [List.getD_eq_getElem _ _ hi]
  exact hB i hi j hj

theorem abs_ilpMatrix_le (I : BoundedILPInstance) (i : Fin I.matrix.length)
    (j : Fin I.numVars) :
    |ilpMatrix I i j| ≤ (2 ^ maxActiveEntryBits I : ℕ) := by
  have hmem : ((I.matrix.getD i.1 []).getD j.1 0).natAbs.size ∈
      (List.range I.matrix.length).flatMap fun r ↦
        (List.range I.numVars).map fun c ↦
          ((I.matrix.getD r []).getD c 0).natAbs.size := by
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨i.1, i.2, j.1, j.2, rfl⟩
  have hsize_le : ((I.matrix[i.1]).getD j.1 0).natAbs.size ≤ maxActiveEntryBits I := by
    have h := (le_foldl_max_init _ 0).2 _ hmem
    rwa [List.getD_eq_getElem _ _ i.2] at h
  have hlt : ((I.matrix[i.1]).getD j.1 0).natAbs < 2 ^ maxActiveEntryBits I :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by omega) hsize_le)
  have habs : |ilpMatrix I i j| = (((I.matrix[i.1]).getD j.1 0).natAbs : ℤ) :=
    Int.abs_eq_natAbs _
  rw [habs]
  exact_mod_cast hlt.le

/-! ### Power-exponential time implies FPT -/

/-- Any problem decidable in `2 ^ (C * (μ a + 1) ^ p) * poly(|a|)` time lies in `FPT`. -/
theorem decidableInPowerExpTime_mem_FPT {α : Type} {A : Set α} {enc : α ↪ List Bool}
    {μ : α → ℕ} {p : ℝ} (h : DecidableInPowerExpTime A enc μ p) :
    A ∈ FPT enc μ := by
  obtain ⟨C, e, h⟩ := h
  refine ⟨fun k ↦ ⌈(2 : ℝ) ^ (C * (k + 1 : ℝ) ^ p)⌉₊, e,
    h.mono 1 (fun a ↦ ?_) fun _ ↦ by positivity⟩
  have hle := mul_le_mul_of_nonneg_right
    (Nat.le_ceil ((2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ p)))
    (by positivity : (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
  push_cast
  linarith

/-! ### Direct `Fin`-indexed nonnegative equality form & RHS-independent Gram certificate -/

private def nonnegFormFin {R p : ℕ} (A : Matrix (Fin R) (Fin p) ℤ) :
    Matrix (Fin R) (Fin (2 * p + R)) ℤ :=
  Matrix.of fun i j ↦
    if hj1 : j.1 < p then A i ⟨j.1, hj1⟩
    else if hj2 : j.1 < 2 * p then -A i ⟨j.1 - p, by omega⟩
    else if j.1 - 2 * p = i.1 then 1 else 0

private lemma abs_nonnegFormFin_le {R p B : ℕ} {A : Matrix (Fin R) (Fin p) ℤ}
    (hB1 : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ B) (i : Fin R) (j : Fin (2 * p + R)) :
    |nonnegFormFin A i j| ≤ B := by
  simp only [nonnegFormFin, Matrix.of_apply]
  split_ifs with hj1 hj2 heq
  · exact hA i ⟨j.1, hj1⟩
  · rw [abs_neg]; exact hA i ⟨j.1 - p, by omega⟩
  · simp; omega
  · simp

private lemma nonnegFormFin_mulVec {R p : ℕ} (A : Matrix (Fin R) (Fin p) ℤ)
    (x : Fin (2 * p + R) → ℤ) (i : Fin R) :
    (nonnegFormFin A *ᵥ x) i =
      (∑ j : Fin p, A i j * (x ⟨j.1, by omega⟩ - x ⟨p + j.1, by omega⟩)) +
        x ⟨2 * p + i.1, by omega⟩ := by
  change ∑ j : Fin (2 * p + R), nonnegFormFin A i j * x j = _
  let g : ℕ → ℤ := fun k ↦
    (if hk1 : k < p then A i ⟨k, hk1⟩
     else if hk2 : k < 2 * p then -A i ⟨k - p, by omega⟩
     else if k - 2 * p = i.1 then 1 else 0) *
    (if hk : k < 2 * p + R then x ⟨k, hk⟩ else 0)
  have hg_eq (j : Fin (2 * p + R)) : nonnegFormFin A i j * x j = g j.1 := by
    simp [g, nonnegFormFin, j.2]
  simp_rw [hg_eq]
  rw [Fin.sum_univ_eq_sum_range g (2 * p + R)]
  have hsplit1 : 2 * p + R = p + p + R := by omega
  have hsum_split : ∑ k ∈ Finset.range (2 * p + R), g k =
      ((∑ k ∈ Finset.range p, g k) + ∑ k ∈ Finset.range p, g (p + k)) +
        ∑ k ∈ Finset.range R, g (p + p + k) := by
    rw [hsplit1, Finset.sum_range_add, Finset.sum_range_add]
  rw [hsum_split]
  dsimp only [g]
  have h1 : ∑ k ∈ Finset.range p,
      (if hk1 : k < p then A i ⟨k, hk1⟩
       else if hk2 : k < 2 * p then -A i ⟨k - p, by omega⟩
       else if k - 2 * p = i.1 then 1 else 0) *
      (if hk : k < 2 * p + R then x ⟨k, hk⟩ else 0) =
      ∑ j : Fin p, A i j * x ⟨j.1, by omega⟩ := by
    let f1 : ℕ → ℤ := fun k ↦ if hk : k < p then A i ⟨k, hk⟩ * x ⟨k, by omega⟩ else 0
    have hf1 (j : Fin p) : A i j * x ⟨j.1, by omega⟩ = f1 j.1 := by simp [f1, j.2]
    simp_rw [hf1]
    rw [Fin.sum_univ_eq_sum_range f1 p]
    refine Finset.sum_congr rfl fun k hk_r ↦ ?_
    have hk : k < p := Finset.mem_range.mp hk_r
    have hkQ : k < 2 * p + R := by omega
    simp [f1, hk, hkQ]
  have h2 : ∑ k ∈ Finset.range p,
      (if hk1 : p + k < p then A i ⟨p + k, hk1⟩
       else if hk2 : p + k < 2 * p then -A i ⟨p + k - p, by omega⟩
       else if p + k - 2 * p = i.1 then 1 else 0) *
      (if hk : p + k < 2 * p + R then x ⟨p + k, hk⟩ else 0) =
      -(∑ j : Fin p, A i j * x ⟨p + j.1, by omega⟩) := by
    let f2 : ℕ → ℤ := fun k ↦ if hk : k < p then -(A i ⟨k, hk⟩ * x ⟨p + k, by omega⟩) else 0
    have hf2 (j : Fin p) : -(A i j * x ⟨p + j.1, by omega⟩) = f2 j.1 := by simp [f2, j.2]
    rw [← Finset.sum_neg_distrib]
    simp_rw [hf2]
    rw [Fin.sum_univ_eq_sum_range f2 p]
    refine Finset.sum_congr rfl fun k hk_r ↦ ?_
    have hk : k < p := Finset.mem_range.mp hk_r
    have hnot1 : ¬ (p + k < p) := by omega
    have hk2 : p + k < 2 * p := by omega
    have hkQ : p + k < 2 * p + R := by omega
    simp [f2, hk, hnot1, hk2, hkQ]
  have h3 : ∑ k ∈ Finset.range R,
      (if hk1 : p + p + k < p then A i ⟨p + p + k, hk1⟩
       else if hk2 : p + p + k < 2 * p then -A i ⟨p + p + k - p, by omega⟩
       else if p + p + k - 2 * p = i.1 then 1 else 0) *
      (if hk : p + p + k < 2 * p + R then x ⟨p + p + k, hk⟩ else 0) =
      x ⟨2 * p + i.1, by omega⟩ := by
    have hcongr : ∑ k ∈ Finset.range R,
        (if hk1 : p + p + k < p then A i ⟨p + p + k, hk1⟩
         else if hk2 : p + p + k < 2 * p then -A i ⟨p + p + k - p, by omega⟩
         else if p + p + k - 2 * p = i.1 then 1 else 0) *
        (if hk : p + p + k < 2 * p + R then x ⟨p + p + k, hk⟩ else 0) =
        ∑ k ∈ Finset.range R,
          if k = i.1 then x ⟨2 * p + i.1, by omega⟩ else 0 := by
      refine Finset.sum_congr rfl fun k hk_r ↦ ?_
      have hk : k < R := Finset.mem_range.mp hk_r
      have hnot1 : ¬ (p + p + k < p) := by omega
      have hnot2 : ¬ (p + p + k < 2 * p) := by omega
      have hkQ : p + p + k < 2 * p + R := by omega
      have hsub : p + p + k - 2 * p = k := by omega
      simp only [hnot1, hnot2, hkQ, hsub, ↓reduceDIte]
      split_ifs with hki
      · subst hki
        rw [one_mul]
        congr 1
        exact Fin.ext (by dsimp; omega)
      · rw [zero_mul]
    rw [hcongr, Finset.sum_ite_eq']
    simp [Finset.mem_range.mpr i.2]
  rw [h1, h2, h3]
  have hsub_sum : ∑ j : Fin p, A i j * (x ⟨j.1, by omega⟩ - x ⟨p + j.1, by omega⟩) =
      (∑ j : Fin p, A i j * x ⟨j.1, by omega⟩) -
        ∑ j : Fin p, A i j * x ⟨p + j.1, by omega⟩ := by
    simp [mul_sub, Finset.sum_sub_distrib]
  linarith

private lemma nonnegFormFin_solution {R p : ℕ} {A : Matrix (Fin R) (Fin p) ℤ} {b : Fin R → ℤ}
    {u : Fin p → ℤ} (hu : A *ᵥ u ≤ b) :
    ∃ x : Fin (2 * p + R) → ℤ, 0 ≤ x ∧ nonnegFormFin A *ᵥ x = b := by
  let x : Fin (2 * p + R) → ℤ := fun j ↦
    if hj1 : j.1 < p then max (u ⟨j.1, hj1⟩) 0
    else if hj2 : j.1 < 2 * p then max (-u ⟨j.1 - p, by omega⟩) 0
    else b ⟨j.1 - 2 * p, by omega⟩ - (A *ᵥ u) ⟨j.1 - 2 * p, by omega⟩
  refine ⟨x, fun j ↦ ?_, funext fun i ↦ ?_⟩
  · dsimp only [x]
    split_ifs with hj1 hj2
    · exact le_max_right _ _
    · exact le_max_right _ _
    · exact sub_nonneg.mpr (hu ⟨j.1 - 2 * p, by omega⟩)
  · rw [nonnegFormFin_mulVec]
    have hdiff (j : Fin p) : x ⟨j.1, by omega⟩ - x ⟨p + j.1, by omega⟩ = u j := by
      have hj1 : j.1 < p := j.2
      have hnot1 : ¬ (p + j.1 < p) := by omega
      have hj2 : p + j.1 < 2 * p := by omega
      have hfin : (⟨p + j.1 - p, by omega⟩ : Fin p) = j := Fin.ext (by dsimp; omega)
      simp only [x, hj1, hnot1, hj2, ↓reduceDIte, hfin]
      exact max_zero_sub_max_neg_zero_eq_self (u j)
    have hslack : x ⟨2 * p + i.1, by omega⟩ = b i - (A *ᵥ u) i := by
      have hnot1 : ¬ (2 * p + i.1 < p) := by omega
      have hnot2 : ¬ (2 * p + i.1 < 2 * p) := by omega
      simp [x, hnot1, hnot2]
    simp_rw [hdiff, hslack]
    change (A *ᵥ u) i + (b i - (A *ᵥ u) i) = b i
    ring

private lemma exists_nonneg_int_indep_large {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) {x₀ : Fin n → ℤ} (hx₀ : 0 ≤ x₀) (hAx₀ : A *ᵥ x₀ = b) :
    ∃ x : Fin n → ℤ, 0 ≤ x ∧ A *ᵥ x = b ∧
      Function.Injective
        ((A.submatrix id (fun j : {j //
          (n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n : ℕ) ≤ x j} ↦ j.1)).map
          (Int.cast : ℤ → ℚ)).mulVecLin := by
  classical
  let K := n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n
  let cost (x : Fin n → ℤ) : ℤ := ∑ j, x j * (K + 1 : ℤ) ^ j.val
  let S : Set (Fin n → ℤ) := {x | 0 ≤ x ∧ A *ᵥ x = b}
  have hS : S.Nonempty := ⟨x₀, hx₀, hAx₀⟩
  let x := Function.argminOn (fun x ↦ (cost x).toNat) S hS
  obtain ⟨hx, hAx⟩ : x ∈ S := Function.argminOn_mem _ S hS
  have hcost : ∀ y : Fin n → ℤ, 0 ≤ y → 0 ≤ cost y := fun y hy ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hy j) (by positivity)
  have hmin : ∀ y, 0 ≤ y → A *ᵥ y = b → cost x ≤ cost y := fun y hy hAy ↦ by
    have h : (cost x).toNat ≤ (cost y).toNat :=
      Function.argminOn_le (fun x ↦ (cost x).toNat) S ⟨hy, hAy⟩
    have := hcost x hx
    have := hcost y hy
    omega
  refine ⟨x, hx, hAx, ?_⟩
  by_contra hinj
  let J := {j : Fin n // (K : ℤ) ≤ x j}
  let AJ : Matrix (Fin m) J ℤ := A.submatrix id Subtype.val
  obtain ⟨cJ, hcJ, hAcJ, hcJB⟩ := Matrix.exists_int_mulVec_eq_zero_of_not_injective AJ
    (fun i j ↦ hA i j.1) (r := n) (by
      calc Fintype.card J ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
        _ ≤ n + 1 := by simp) hinj
  let c : Fin n → ℤ := fun j ↦ if hj : (K : ℤ) ≤ x j then cJ ⟨j, hj⟩ else 0
  have hcB (j : Fin n) : |c j| ≤ x j ∧ |c j| ≤ K := by
    by_cases hj : (K : ℤ) ≤ x j
    · have h : |cJ ⟨j, hj⟩| ≤ K := by simpa only [Fintype.card_fin] using hcJB ⟨j, hj⟩
      simpa only [c, hj, ↓reduceDIte] using ⟨h.trans hj, h⟩
    · simpa [c, hj] using hx j
  have hAc : A *ᵥ c = 0 := by
    ext i
    change ∑ j, A i j * c j = 0
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j ↦ (K : ℤ) ≤ x j)]
    have hzero : ∑ j : {j : Fin n // ¬(K : ℤ) ≤ x j}, A i j.1 * c j.1 = 0 :=
      Finset.sum_eq_zero fun j _ ↦ by simp [c, j.2]
    rw [hzero, add_zero]
    have heq : ∀ j : J, c j.1 = cJ j := fun j ↦ by simp [c, j.2]
    simpa only [AJ, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, heq, Pi.zero_apply]
      using congrFun hAcJ i
  have hplus : 0 ≤ x + c := fun j ↦ by
    change 0 ≤ x j + c j
    linarith [(abs_le.mp (hcB j).1).1]
  have hminus : 0 ≤ x - c := fun j ↦ sub_nonneg.mpr (le_abs_self _ |>.trans (hcB j).1)
  have h1 := hmin (x + c) hplus (by rw [Matrix.mulVec_add, hAx, hAc, add_zero])
  have h2 := hmin (x - c) hminus (by rw [Matrix.mulVec_sub, hAx, hAc, sub_zero])
  have hcost_add : cost (x + c) = cost x + cost c := by
    simp [cost, add_mul, Finset.sum_add_distrib]
  have hcost_sub : cost (x - c) = cost x - cost c := by
    simp [cost, sub_mul, Finset.sum_sub_distrib]
  have hc0 : cost c = 0 := by linarith
  have hc_eq : c = 0 := by
    let a : ℕ → ℤ := fun j ↦ if hj : j < n then c ⟨j, hj⟩ else 0
    have hsum : ∑ j ∈ Finset.range n, a j * (K + 1 : ℤ) ^ j = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [a, cost] using hc0
    have h := Int.eq_zero_of_sum_mul_pow_eq_zero (a := a)
      (fun j hj ↦ by simpa [a, hj] using Int.lt_add_one_iff.mpr (hcB ⟨j, hj⟩).2) hsum
    funext j
    simpa [a, j.isLt] using h j j.isLt
  exact hcJ (funext fun j ↦ by simpa [c, j.2] using congrFun hc_eq j.1)

/-- RHS-independent Gram + adjugate integer certificate for `A' *ᵥ x = b`, `x ≥ 0`:
returns `(z, d, W)` with `0 < d` and all entries bounded by `(Q + 1) * B * K` such that
`z j + (W *ᵥ (b - A' *ᵥ z)) j / d` recovers a nonnegative solution `x` of `A' *ᵥ x = b`. -/
private lemma exists_gram_adjugate_certificate {R Q B : ℕ}
    {A' : Matrix (Fin R) (Fin Q) ℤ} {b : Fin R → ℤ}
    (hB1 : 1 ≤ B) (hA' : ∀ i j, |A' i j| ≤ B)
    {x₀ : Fin Q → ℤ} (hx₀ : 0 ≤ x₀) (hAx₀ : A' *ᵥ x₀ = b) :
    let K := Q.factorial * (R * ((Q + 1) * B) ^ 2 + 1) ^ Q
    let Mmax := (Q + 1) * B * K
    ∃ (z : Fin Q → ℤ) (d : ℤ) (W : Matrix (Fin Q) (Fin R) ℤ) (x : Fin Q → ℤ),
      0 ≤ x ∧ A' *ᵥ x = b ∧ 0 < d ∧
      (∀ j, |z j| ≤ Mmax) ∧ |d| ≤ Mmax ∧ (∀ j i, |W j i| ≤ Mmax) ∧
      (∀ j, (W *ᵥ (b - A' *ᵥ z)) j = (x j - z j) * d) := by
  classical
  intro K Mmax
  obtain ⟨x, hx, hAx, hinj⟩ := exists_nonneg_int_indep_large hA' hx₀ hAx₀
  let z : Fin Q → ℤ := fun j ↦ if (K : ℤ) ≤ x j then 0 else x j
  let G : Matrix (Fin Q) (Fin Q) ℤ := Matrix.of fun j k ↦
    if (K : ℤ) ≤ x j ∧ (K : ℤ) ≤ x k then ∑ i : Fin R, A' i j * A' i k
    else if j = k then 1 else 0
  let Mrhs : Matrix (Fin Q) (Fin R) ℤ := Matrix.of fun j i ↦
    if (K : ℤ) ≤ x j then A' i j else 0
  -- Identity `G *ᵥ (x - z) = Mrhs *ᵥ (b - A' *ᵥ z)` over `ℤ`
  have hGxz : G *ᵥ (x - z) = Mrhs *ᵥ (b - A' *ᵥ z) := by
    ext j
    simp only [Matrix.mulVec, dotProduct, G, Mrhs, Matrix.of_apply, Pi.sub_apply]
    by_cases hj : (K : ℤ) ≤ x j
    · have hterm (k : Fin Q) :
          (if (K : ℤ) ≤ x j ∧ (K : ℤ) ≤ x k then ∑ i : Fin R, A' i j * A' i k
           else if j = k then 1 else 0) * (x k - z k) =
          (∑ i : Fin R, A' i j * A' i k) * (x k - z k) := by
        by_cases hk : (K : ℤ) ≤ x k
        · simp [hj, hk]
        · simp [z, hk]
      simp_rw [hterm, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hj, ↓reduceIte, ← Finset.mul_sum]
      congr 1
      have hAx_i : ∑ k : Fin Q, A' i k * x k = b i := congrFun hAx i
      simp_rw [mul_sub, Finset.sum_sub_distrib, hAx_i]
    · trans (0 : ℤ)
      · refine Finset.sum_eq_zero fun k _ ↦ ?_
        by_cases hjk : j = k
        · subst hjk; simp [z, hj]
        · simp [hj, hjk]
      · symm
        exact Finset.sum_eq_zero fun i _ ↦ by simp [hj]
  -- Nonsingularity `G.det ≠ 0` over `ℚ`
  have hdet_ne : G.det ≠ 0 := by
    intro hdet0
    let GK : Matrix (Fin Q) (Fin Q) ℚ := G.map (Int.cast : ℤ → ℚ)
    let AK : Matrix (Fin R) (Fin Q) ℚ := A'.map (Int.cast : ℤ → ℚ)
    have hGK_det : GK.det = 0 := by
      have hcast : ((G.det : ℤ) : ℚ) = GK.det := (Int.castRingHom ℚ).map_det G
      rw [← hcast, hdet0, Int.cast_zero]
    obtain ⟨v, hv_ne, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hGK_det
    have hv_off (k : Fin Q) (hk : ¬ (K : ℤ) ≤ x k) : v k = 0 := by
      have hrow := congrFun hGv k
      simp only [GK, G, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, hk,
        false_and, ↓reduceIte, Pi.zero_apply] at hrow
      simpa [ite_mul] using hrow
    have hv_on (j : Fin Q) (hj : (K : ℤ) ≤ x j) :
        ∑ i : Fin R, AK i j * (AK *ᵥ v) i = 0 := by
      have hrow := congrFun hGv j
      simp only [GK, G, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, hj,
        true_and, Pi.zero_apply] at hrow
      have hrewrite : ∑ k : Fin Q,
          (↑(if (K : ℤ) ≤ x k then ∑ i : Fin R, A' i j * A' i k
             else if j = k then 1 else 0) : ℚ) * v k =
          ∑ k : Fin Q, (∑ i : Fin R, AK i j * AK i k) * v k := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        by_cases hk : (K : ℤ) ≤ x k
        · simp [AK, hk]
        · simp [hv_off k hk]
      rw [hrewrite] at hrow
      simp_rw [Finset.sum_mul, mul_assoc] at hrow
      rw [Finset.sum_comm] at hrow
      simpa only [AK, Matrix.mulVec, dotProduct, ← Finset.mul_sum] using hrow
    have hquad : ∑ i : Fin R, (AK *ᵥ v) i * (AK *ᵥ v) i = 0 := by
      have hswap : ∑ i : Fin R, (AK *ᵥ v) i * (AK *ᵥ v) i =
          ∑ j : Fin Q, v j * (∑ i : Fin R, AK i j * (AK *ᵥ v) i) := by
        have h1 (i : Fin R) : (AK *ᵥ v) i * (AK *ᵥ v) i =
            ∑ j : Fin Q, v j * (AK i j * (AK *ᵥ v) i) := by
          change (∑ j : Fin Q, AK i j * v j) * (AK *ᵥ v) i = _
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
        simp_rw [h1]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ (Finset.mul_sum _ _ _).symm
      rw [hswap]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases hj : (K : ℤ) ≤ x j
      · simp [hv_on j hj]
      · simp [hv_off j hj]
    have hAv0 : AK *ᵥ v = 0 := by
      ext i
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ ↦ mul_self_nonneg ((AK *ᵥ v) k))).mp hquad i (Finset.mem_univ i)
      exact mul_self_eq_zero.mp hi0
    let J := {j : Fin Q // (K : ℤ) ≤ x j}
    let vJ : J → ℚ := fun j ↦ v j.1
    have hAJ_vJ : ((A'.submatrix id Subtype.val).map (Int.cast : ℤ → ℚ)).mulVecLin vJ = 0 := by
      ext i
      have hi := congrFun hAv0 i
      change ∑ k : Fin Q, AK i k * v k = 0 at hi
      rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin Q ↦ (K : ℤ) ≤ x k)] at hi
      have hoff0 : ∑ k : {k : Fin Q // ¬(K : ℤ) ≤ x k}, AK i k.1 * v k.1 = 0 :=
        Finset.sum_eq_zero fun k _ ↦ by simp [hv_off k.1 k.2]
      rw [hoff0, add_zero] at hi
      simpa [AK, vJ, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using hi
    have hvJ0 : vJ = 0 := hinj (hAJ_vJ.trans (LinearMap.map_zero _).symm)
    refine hv_ne (funext fun k ↦ ?_)
    by_cases hk : (K : ℤ) ≤ x k
    · exact congrFun hvJ0 ⟨k, hk⟩
    · exact hv_off k hk
  -- Entry bounds on `G`, `G.det`, `adjugate G`, and `W`
  let Cg : ℕ := R * B ^ 2 + 1
  have hG_le (j k : Fin Q) : |G j k| ≤ Cg := by
    simp only [G, Matrix.of_apply]
    split_ifs
    · have hsum : |∑ i : Fin R, A' i j * A' i k| ≤ (R * B ^ 2 : ℕ) := by
        calc |∑ i : Fin R, A' i j * A' i k|
            ≤ ∑ i : Fin R, |A' i j * A' i k| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin R, ((B : ℤ) * B) := Finset.sum_le_sum fun i _ ↦ by
              rw [abs_mul]
              exact mul_le_mul (hA' i j) (hA' i k) (abs_nonneg _) (by positivity)
          _ = (R * B ^ 2 : ℕ) := by simp [sq]
      exact hsum.trans (by push_cast [Cg]; omega)
    · simp only [abs_one]
      push_cast [Cg]
      linarith [show (0 : ℤ) ≤ (R : ℤ) * (B : ℤ) ^ 2 by positivity]
    · simp only [abs_zero]; positivity
  let Dg : ℕ := Q.factorial * Cg ^ Q
  have hDg_le_K : Dg ≤ K := by
    dsimp only [Dg, K, Cg]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have : B ≤ (Q + 1) * B := Nat.le_mul_of_pos_left B (by omega)
    have : B ^ 2 ≤ ((Q + 1) * B) ^ 2 := Nat.pow_le_pow_left this 2
    nlinarith
  have hdet_le : |G.det| ≤ Dg := by
    simpa [Dg] using Matrix.det_le (abv := AbsoluteValue.abs) hG_le
  have hadj_le (j k : Fin Q) : |Matrix.adjugate G j k| ≤ Dg := by
    have hcr : Matrix.adjugate G j k = Matrix.cramer G (Pi.single k 1) j := by
      rw [Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
    rw [hcr, Matrix.cramer_apply]
    have hupd : ∀ a b : Fin Q, |G.updateCol j (Pi.single k 1) a b| ≤ Cg := fun a b ↦ by
      rw [Matrix.updateCol_apply]
      split_ifs
      · by_cases hak : a = k
        · subst hak
          simp only [Pi.single_eq_same, abs_one]
          push_cast [Cg]
          linarith [show (0 : ℤ) ≤ (R : ℤ) * (B : ℤ) ^ 2 by positivity]
        · simp only [Pi.single_eq_of_ne hak, abs_zero]
          positivity
      · exact hG_le a b
    simpa [Dg] using Matrix.det_le (abv := AbsoluteValue.abs) hupd
  let sgn : ℤ := if 0 < G.det then 1 else -1
  let d : ℤ := sgn * G.det
  have hsgn_abs : |sgn| = 1 := by dsimp [sgn]; split_ifs <;> simp
  have hd_pos : 0 < d := by
    dsimp [d, sgn]
    rcases lt_or_gt_of_ne hdet_ne with hneg | hpos
    · have hnot : ¬ (0 < G.det) := not_lt.mpr hneg.le
      simp only [hnot, ↓reduceIte]; omega
    · simp only [hpos, ↓reduceIte]; omega
  let W : Matrix (Fin Q) (Fin R) ℤ := sgn • (Matrix.adjugate G * Mrhs)
  have hKM : (K : ℤ) ≤ Mmax := by
    dsimp only [Mmax]
    have h1 : 1 ≤ (Q + 1) * B := Nat.mul_pos (by omega) hB1
    exact_mod_cast Nat.le_mul_of_pos_left K h1
  have hz_le (j : Fin Q) : |z j| ≤ Mmax := by
    by_cases hj : (K : ℤ) ≤ x j
    · simp [z, hj]
    · have hzj : z j = x j := by simp [z, hj]
      rw [hzj, abs_of_nonneg (hx j)]
      exact (le_of_lt (not_le.mp hj)).trans hKM
  have hd_le : |d| ≤ Mmax := by
    rw [abs_mul, hsgn_abs, one_mul]
    exact (hdet_le.trans (by exact_mod_cast hDg_le_K)).trans hKM
  have hW_le (j : Fin Q) (i : Fin R) : |W j i| ≤ Mmax := by
    simp only [W, Matrix.smul_apply, smul_eq_mul, abs_mul, hsgn_abs, one_mul, Matrix.mul_apply]
    have hMrhs_le (k : Fin Q) : |Mrhs k i| ≤ B := by
      simp only [Mrhs, Matrix.of_apply]
      split_ifs
      · exact hA' i k
      · simp
    calc |∑ k : Fin Q, Matrix.adjugate G j k * Mrhs k i|
        ≤ ∑ k : Fin Q, |Matrix.adjugate G j k * Mrhs k i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin Q, ((K : ℤ) * B) := Finset.sum_le_sum fun k _ ↦ by
          rw [abs_mul]
          exact mul_le_mul ((hadj_le j k).trans (by exact_mod_cast hDg_le_K)) (hMrhs_le k)
            (abs_nonneg _) (by positivity)
      _ = (Q : ℤ) * B * K := by simp; ring
      _ ≤ Mmax := by
          dsimp [Mmax]
          exact_mod_cast (show Q * B * K ≤ (Q + 1) * B * K by nlinarith)
  have hW_eq (j : Fin Q) : (W *ᵥ (b - A' *ᵥ z)) j = (x j - z j) * d := by
    have hvec : W *ᵥ (b - A' *ᵥ z) = d • (x - z) := by
      calc W *ᵥ (b - A' *ᵥ z)
          = sgn • (Matrix.adjugate G *ᵥ (Mrhs *ᵥ (b - A' *ᵥ z))) := by
              rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
        _ = sgn • (Matrix.adjugate G *ᵥ (G *ᵥ (x - z))) := by rw [hGxz]
        _ = sgn • ((Matrix.adjugate G * G) *ᵥ (x - z)) := by rw [Matrix.mulVec_mulVec]
        _ = d • (x - z) := by
              rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
    have hj := congrFun hvec j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hj
    linarith
  exact ⟨z, d, W, x, hx, hAx, hd_pos, hz_le, hd_le, hW_le, hW_eq⟩

/-! ### Bit-width bounds and executable polynomial-time verifier -/

/-- Magnitude bit-width upper bound for each field of `(z, d, W)`. -/
@[expose]
def ilpFieldMagBits (p R L : ℕ) : ℕ :=
  let Q := 2 * p + R
  (Q + L + 3) + Q * Q + Q * (R + 2 * Q + 2 * L + 7) + 2

/-- Total bit-width `(Q + 1 + Q * R) * (ilpFieldMagBits p R L + 1)` of a packed certificate `r`. -/
@[expose]
def ilpTotalBits (I : BoundedILPInstance) : ℕ :=
  let p := I.numVars
  let R := I.matrix.length
  let Q := 2 * p + R
  let L := maxActiveEntryBits I
  (Q + 1 + Q * R) * (ilpFieldMagBits p R L + 1)

private lemma natAbs_lt_two_pow_ilpFieldMagBits (p R L : ℕ) :
    let Q := 2 * p + R
    let B := 2 ^ L
    let K := Q.factorial * (R * ((Q + 1) * B) ^ 2 + 1) ^ Q
    (Q + 1) * B * K < 2 ^ ilpFieldMagBits p R L := by
  intro Q B K
  suffices hsz : ((Q + 1) * B * K).size ≤ ilpFieldMagBits p R L from
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by omega) hsz)
  have hB : B.size ≤ L + 1 :=
    Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self L))
  have hQ1 : (Q + 1).size ≤ Q + 1 := Nat.size_le_self _
  have hQ : Q.size ≤ Q := Nat.size_le_self _
  have hR : R.size ≤ R := Nat.size_le_self _
  have hfac := Nat.size_factorial_le Q
  have hs1 := Nat.size_mul_le (Q + 1) B
  have hs2 := Nat.size_pow_le ((Q + 1) * B) 2
  have hs3 := Nat.size_mul_le R (((Q + 1) * B) ^ 2)
  have hs4 := Nat.size_add_le (R * ((Q + 1) * B) ^ 2) 1
  have hs5 := Nat.size_pow_le (R * ((Q + 1) * B) ^ 2 + 1) Q
  have hs6 := Nat.size_mul_le Q.factorial ((R * ((Q + 1) * B) ^ 2 + 1) ^ Q)
  have hs7 := Nat.size_mul_le ((Q + 1) * B) K
  norm_num only [Nat.size_one] at hs4
  have hK : K.size ≤ Q * Q + Q * (R + 2 * Q + 2 * L + 7) + 2 := by
    dsimp only [K]
    nlinarith
  dsimp only [ilpFieldMagBits]
  change ((Q + 1) * B * K).size ≤
    ((2 * p + R) + L + 3) + (2 * p + R) * (2 * p + R) +
      (2 * p + R) * (R + 2 * (2 * p + R) + 2 * L + 7) + 2
  change ((Q + 1) * B * K).size ≤
    (Q + L + 3) + Q * Q + Q * (R + 2 * Q + 2 * L + 7) + 2
  omega

theorem ilpTotalBits_le_poly_param (I : BoundedILPInstance) :
    (ilpTotalBits I : ℝ) ≤ 250 * (ilpParam I + 1 : ℝ) ^ (4 : ℝ) := by
  set p := I.numVars
  set R := I.matrix.length
  set L := maxActiveEntryBits I
  set M := ilpParam I + 1
  have hpM : p ≤ M := by dsimp [M, ilpParam]; omega
  have hRM : R ≤ M := by dsimp [M, ilpParam]; omega
  have hLM : L ≤ M := by dsimp [M, ilpParam]; omega
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  set Q := 2 * p + R
  have hQM : Q ≤ 2 * M := by dsimp [Q, M, ilpParam]; omega
  have hcnt : Q + 1 + Q * R ≤ 5 * M ^ 2 := by nlinarith
  have hwid : ilpFieldMagBits p R L + 1 ≤ 45 * M ^ 2 := by
    dsimp only [ilpFieldMagBits]
    change (Q + L + 3) + Q * Q + Q * (R + 2 * Q + 2 * L + 7) + 2 + 1 ≤ 45 * M ^ 2
    nlinarith
  have hprod : ilpTotalBits I ≤ 250 * M ^ 4 := by
    have hm := Nat.mul_le_mul hcnt hwid
    dsimp only [ilpTotalBits]
    change (Q + 1 + Q * R) * (ilpFieldMagBits p R L + 1) ≤ 250 * M ^ 4
    nlinarith
  have hcast : (ilpTotalBits I : ℝ) ≤ 250 * (M : ℝ) ^ (4 : ℕ) := by exact_mod_cast hprod
  rwa [← Real.rpow_natCast (M : ℝ) 4, show ((4 : ℕ) : ℝ) = (4 : ℝ) by norm_num,
    show (M : ℝ) = (ilpParam I + 1 : ℝ) by dsimp [M]; push_cast; rfl] at hcast

/-- Decode a fixed-width bit block `[signBit] ++ magBits` (most-significant magnitude bit first)
into a signed integer. -/
def decodeSignedField (w : List Bool) : ℤ :=
  if w.headD false then -(Cslib.BitString.binaryValue w.tail : ℤ)
  else (Cslib.BitString.binaryValue w.tail : ℤ)

/-- Encode `v : ℤ` with `v.natAbs < 2 ^ magBits` as a `(magBits + 1)`-bit word. -/
def encodeSignedField (magBits : ℕ) (v : ℤ) : List Bool :=
  decide (v < 0) :: Cslib.BitString.binaryWord magBits v.natAbs

private lemma length_encodeSignedField {magBits : ℕ} {v : ℤ} (hv : v.natAbs < 2 ^ magBits) :
    (encodeSignedField magBits v).length = magBits + 1 := by
  simp [encodeSignedField, Cslib.BitString.length_binaryWord hv]

private lemma decodeSignedField_encodeSignedField (magBits : ℕ) (v : ℤ) :
    decodeSignedField (encodeSignedField magBits v) = v := by
  simp only [decodeSignedField, encodeSignedField, List.headD_cons, List.tail_cons,
    Cslib.BitString.binaryValue_binaryWord, Int.natCast_natAbs]
  by_cases hv : v < 0
  · simp [hv, abs_of_neg hv]
  · simp [hv, abs_of_nonneg (not_lt.mp hv)]

/-- Truncated integer division by a natural `d` (`0` when `d = 0`). -/
def intTruncDiv (a : ℤ) (d : ℕ) : ℤ :=
  if decide (a < 0) then -((a.natAbs / d : ℕ) : ℤ) else ((a.natAbs / d : ℕ) : ℤ)

private lemma intTruncDiv_mul_cancel (q : ℤ) {d : ℕ} (hd : 0 < d) :
    intTruncDiv (q * (d : ℤ)) d = q := by
  have h1 : (q * (d : ℤ)).natAbs = q.natAbs * d := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have h2 : (q * (d : ℤ)).natAbs / d = q.natAbs := by
    rw [h1, Nat.mul_div_cancel _ hd]
  unfold intTruncDiv
  rw [h2, Int.natCast_natAbs]
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  by_cases hq : q < 0
  · have hneg : q * (d : ℤ) < 0 := mul_neg_of_neg_of_pos hq hdZ
    simp [hneg, abs_of_neg hq]
  · have hnonneg : ¬ (q * (d : ℤ) < 0) :=
      not_lt.mpr (mul_nonneg (not_lt.mp hq) hdZ.le)
    simp [hnonneg, abs_of_nonneg (not_lt.mp hq)]

/-- Candidate `u : List ℤ` (length `I.numVars`) unpacked from `(I, r)` and checked against
`A u ≤ b`. -/
def verifyILPCertificate (p : BoundedILPInstance × ℕ) : Bool :=
  let I := p.1
  let r := p.2
  let nVars := I.numVars
  let R := I.matrix.length
  let Q := 2 * nVars + R
  let L := maxActiveEntryBits I
  let magBits := ilpFieldMagBits nVars R L
  let fieldWidth := magBits + 1
  let fieldCount := Q + 1 + Q * R
  let rows := Cslib.BitString.listRows fieldCount fieldWidth
    (Cslib.BitString.lowBits (fieldCount * fieldWidth) r)
  let fields : List ℤ := rows.map decodeSignedField
  let zList : List ℤ := (List.range Q).map fun k ↦ fields.getD k 0
  let dNat : ℕ := (fields.getD Q 0).toNat
  let rhsPrime : List ℤ := (List.range R).map fun i ↦
    I.rhs.getD i 0 -
      ((List.range nVars).map fun j ↦
        (I.matrix.getD i []).getD j 0 * (zList.getD j 0 - zList.getD (nVars + j) 0)).sum -
      zList.getD (2 * nVars + i) 0
  let xList : List ℤ := (List.range Q).map fun j ↦
    zList.getD j 0 +
      intTruncDiv
        (((List.range R).map fun i ↦
          fields.getD (Q + 1 + j * R + i) 0 * rhsPrime.getD i 0).sum)
        dNat
  let uList : List ℤ := (List.range nVars).map fun j ↦
    xList.getD j 0 - xList.getD (nVars + j) 0
  (List.range R).all fun i ↦
    decide (((List.range nVars).map fun j ↦
      (I.matrix.getD i []).getD j 0 * uList.getD j 0).sum ≤ I.rhs.getD i 0)

/-! ### Polynomial-time computability of `ilpTotalBits` and `verifyILPCertificate` -/

section PolyTimeVerifier

private lemma foldl_max_eq_init_or_mem : ∀ (l : List ℕ) (init : ℕ),
    l.foldl max init = init ∨ l.foldl max init ∈ l := by
  intro l
  induction l with
  | nil => intro init; exact Or.inl rfl
  | cons a as ih =>
    intro init
    rw [List.foldl_cons]
    rcases ih (max init a) with h | h
    · rw [h]
      rcases max_choice init a with hm | hm
      · exact Or.inl hm
      · rw [hm]
        exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem a h)

private lemma computableInPolyTime_foldlMax :
    ComputableInPolyTime (fun l : List ℕ ↦ l.foldl max 0) (encList encUnary) encUnary :=
  foldl' id' (const 0) unary_max (B := fun l ↦ (encList encUnary l).length) .self fun l i _ ↦ by
    rcases foldl_max_eq_init_or_mem (l.take i) 0 with h0 | hmem
    · simp [h0]
    · exact length_le_encList_of_mem encUnary (List.mem_of_mem_take hmem)

@[fun_prop]
theorem computableInPolyTime_maxActiveEntryBits :
    ComputableInPolyTime maxActiveEntryBits encBoundedILP encUnary := by
  have hp : ComputableInPolyTime BoundedILPInstance.numVars encBoundedILP encUnary := by fun_prop
  have hm : ComputableInPolyTime BoundedILPInstance.matrix encBoundedILP encIntMatrix := by fun_prop
  have hR : ComputableInPolyTime (fun I : BoundedILPInstance ↦ I.matrix.length)
      encBoundedILP encUnary := (length_list (encList encIntBin)).comp hm
  have hflat : ComputableInPolyTime
      (fun I : BoundedILPInstance ↦
        (List.range I.matrix.length).flatMap fun i ↦
          (List.range I.numVars).map fun j ↦
            ((I.matrix.getD i []).getD j 0).natAbs.size)
      encBoundedILP (encList encUnary) := by
    refine flatMapWithInput (range.comp hR) ?_
    set F1 := encPair encBoundedILP encUnary
    refine mapWithInput (range.comp (hp.comp (fst encBoundedILP encUnary))) ?_
    set F2 := encPair F1 encUnary
    have hrow : ComputableInPolyTime (fun q : (BoundedILPInstance × ℕ) × ℕ ↦
        q.1.1.matrix.getD q.1.2 []) F2 (encList encIntBin) :=
      listGetDWithInput (hm.comp ((fst encBoundedILP encUnary).comp (fst F1 encUnary)))
        ((snd encBoundedILP encUnary).comp (fst F1 encUnary)) []
    have hent : ComputableInPolyTime (fun q : (BoundedILPInstance × ℕ) × ℕ ↦
        (q.1.1.matrix.getD q.1.2 []).getD q.2 0) F2 encIntBin :=
      listGetDWithInput hrow (snd F1 encUnary) 0
    exact binary_size.comp (intBin_natAbs.comp hent)
  unfold maxActiveEntryBits
  exact computableInPolyTime_foldlMax.comp hflat

attribute [local irreducible] maxActiveEntryBits

@[fun_prop]
theorem computableInPolyTime_ilpTotalBits :
    ComputableInPolyTime ilpTotalBits encBoundedILP encUnary := by
  unfold ilpTotalBits ilpFieldMagBits
  fun_prop

@[fun_prop]
theorem computableInPolyTime_decodeSignedField :
    ComputableInPolyTime decodeSignedField encBits encIntBin := by
  unfold decodeSignedField
  exact intBin_signMagnitude' (headD false) (bitsBinaryValue.comp bitsTail)

@[fun_prop]
theorem computableInPolyTime_intTruncDiv :
    ComputableInPolyTime (fun p : ℤ × ℕ ↦ intTruncDiv p.1 p.2)
      (encPair encIntBin encNat) encIntBin := by
  unfold intTruncDiv
  exact intBin_signMagnitude' (intBin_isNeg.comp (fst encIntBin encNat))
    (binary_div.comp ((intBin_natAbs.comp (fst encIntBin encNat)).prod (snd encIntBin encNat)))

@[fun_prop]
theorem computableInPolyTime_verifyILPCertificate :
    ComputableInPolyTime verifyILPCertificate (encPair encBoundedILP encNat) encBool := by
  set E := encPair encBoundedILP encNat
  have hI : ComputableInPolyTime Prod.fst E encBoundedILP := fst encBoundedILP encNat
  have hr : ComputableInPolyTime Prod.snd E encNat := snd encBoundedILP encNat
  have hnVars : ComputableInPolyTime (fun p : BoundedILPInstance × ℕ ↦ p.1.numVars) E encUnary := by
    fun_prop
  have hm : ComputableInPolyTime (fun p : BoundedILPInstance × ℕ ↦ p.1.matrix) E encIntMatrix := by
    fun_prop
  have hb : ComputableInPolyTime (fun p : BoundedILPInstance × ℕ ↦ p.1.rhs)
      E (encList encIntBin) := by fun_prop
  have hR : ComputableInPolyTime (fun p : BoundedILPInstance × ℕ ↦ p.1.matrix.length)
      E encUnary := (length_list (encList encIntBin)).comp hm
  have hQ : ComputableInPolyTime
      (fun p : BoundedILPInstance × ℕ ↦ 2 * p.1.numVars + p.1.matrix.length) E encUnary := by
    fun_prop
  have hfw : ComputableInPolyTime
      (fun p : BoundedILPInstance × ℕ ↦
        ilpFieldMagBits p.1.numVars p.1.matrix.length (maxActiveEntryBits p.1) + 1)
      E encUnary := by
    unfold ilpFieldMagBits
    fun_prop
  have hfc : ComputableInPolyTime
      (fun p : BoundedILPInstance × ℕ ↦
        let Q := 2 * p.1.numVars + p.1.matrix.length
        Q + 1 + Q * p.1.matrix.length)
      E encUnary := by
    fun_prop
  have htot : ComputableInPolyTime (fun p : BoundedILPInstance × ℕ ↦ ilpTotalBits p.1)
      E encUnary := computableInPolyTime_ilpTotalBits.comp hI
  have hrows : ComputableInPolyTime
      (fun p : BoundedILPInstance × ℕ ↦
        let Q := 2 * p.1.numVars + p.1.matrix.length
        let fw := ilpFieldMagBits p.1.numVars p.1.matrix.length (maxActiveEntryBits p.1) + 1
        let fc := Q + 1 + Q * p.1.matrix.length
        Cslib.BitString.listRows fc fw (Cslib.BitString.lowBits (fc * fw) p.2))
      E (encList encBits) :=
    bitsRowsWithInput hfc hfw (bitsLow htot hr)
  let fieldsFn (p : BoundedILPInstance × ℕ) : List ℤ :=
    let Q := 2 * p.1.numVars + p.1.matrix.length
    let fw := ilpFieldMagBits p.1.numVars p.1.matrix.length (maxActiveEntryBits p.1) + 1
    let fc := Q + 1 + Q * p.1.matrix.length
    (Cslib.BitString.listRows fc fw (Cslib.BitString.lowBits (fc * fw) p.2)).map decodeSignedField
  have hfields : ComputableInPolyTime fieldsFn E (encList encIntBin) :=
    (map computableInPolyTime_decodeSignedField).comp hrows
  let zListFn (p : BoundedILPInstance × ℕ) : List ℤ :=
    (List.range (2 * p.1.numVars + p.1.matrix.length)).map fun k ↦ (fieldsFn p).getD k 0
  have hzList : ComputableInPolyTime zListFn E (encList encIntBin) :=
    mapWithInput (range.comp hQ)
      (listGetDWithInput (hfields.comp (fst E encUnary)) (snd E encUnary) 0)
  let dNatFn (p : BoundedILPInstance × ℕ) : ℕ :=
    ((fieldsFn p).getD (2 * p.1.numVars + p.1.matrix.length) 0).toNat
  have hdNat : ComputableInPolyTime dNatFn E encNat :=
    intBin_toNat.comp (listGetDWithInput hfields hQ 0)
  let rhsPrimeFn (p : BoundedILPInstance × ℕ) : List ℤ :=
    (List.range p.1.matrix.length).map fun i ↦
      p.1.rhs.getD i 0 -
        ((List.range p.1.numVars).map fun j ↦
          (p.1.matrix.getD i []).getD j 0 *
            ((zListFn p).getD j 0 - (zListFn p).getD (p.1.numVars + j) 0)).sum -
        (zListFn p).getD (2 * p.1.numVars + i) 0
  have hrhsP : ComputableInPolyTime rhsPrimeFn E (encList encIntBin) := by
    refine mapWithInput (range.comp hR) ?_
    set F1 := encPair E encUnary
    have hp1 := fst E encUnary
    have hi1 := snd E encUnary
    have hbi := listGetDWithInput (hb.comp hp1) hi1 0
    have hzslack : ComputableInPolyTime
        (fun q : (BoundedILPInstance × ℕ) × ℕ ↦
          (zListFn q.1).getD (2 * q.1.1.numVars + q.2) 0) F1 encIntBin :=
      listGetDWithInput (hzList.comp hp1) (by fun_prop) 0
    have hsum_row : ComputableInPolyTime
        (fun q : (BoundedILPInstance × ℕ) × ℕ ↦
          ((List.range q.1.1.numVars).map fun j ↦
            (q.1.1.matrix.getD q.2 []).getD j 0 *
              ((zListFn q.1).getD j 0 - (zListFn q.1).getD (q.1.1.numVars + j) 0)).sum)
        F1 encIntBin := by
      refine intBin_sum.comp (mapWithInput (range.comp (hnVars.comp hp1)) ?_)
      set F2 := encPair F1 encUnary
      have hq2 := fst F1 encUnary
      have hj2 := snd F1 encUnary
      have hrow : ComputableInPolyTime
          (fun w : ((BoundedILPInstance × ℕ) × ℕ) × ℕ ↦ w.1.1.1.matrix.getD w.1.2 [])
          F2 (encList encIntBin) :=
        listGetDWithInput (hm.comp (hp1.comp hq2)) (hi1.comp hq2) []
      have haij := listGetDWithInput hrow hj2 0
      have hzj1 := listGetDWithInput (hzList.comp (hp1.comp hq2)) hj2 0
      have hzj2 := listGetDWithInput (hzList.comp (hp1.comp hq2))
        (unary_add.comp ((hnVars.comp (hp1.comp hq2)).prod hj2)) 0
      exact intBin_mul' haij (intBin_sub' hzj1 hzj2)
    exact intBin_sub' (intBin_sub' hbi hsum_row) hzslack
  let xListFn (p : BoundedILPInstance × ℕ) : List ℤ :=
    let Q := 2 * p.1.numVars + p.1.matrix.length
    let R := p.1.matrix.length
    (List.range Q).map fun j ↦
      (zListFn p).getD j 0 +
        intTruncDiv
          (((List.range R).map fun i ↦
            (fieldsFn p).getD (Q + 1 + j * R + i) 0 * (rhsPrimeFn p).getD i 0).sum)
          (dNatFn p)
  have hxList : ComputableInPolyTime xListFn E (encList encIntBin) := by
    refine mapWithInput (range.comp hQ) ?_
    set F1 := encPair E encUnary
    have hp1 := fst E encUnary
    have hj1 := snd E encUnary
    have hzj := listGetDWithInput (hzList.comp hp1) hj1 0
    have hnum : ComputableInPolyTime
        (fun q : (BoundedILPInstance × ℕ) × ℕ ↦
          ((List.range q.1.1.matrix.length).map fun i ↦
            (fieldsFn q.1).getD
              ((2 * q.1.1.numVars + q.1.1.matrix.length) + 1 + q.2 * q.1.1.matrix.length + i) 0 *
              (rhsPrimeFn q.1).getD i 0).sum)
        F1 encIntBin := by
      refine intBin_sum.comp (mapWithInput (range.comp (hR.comp hp1)) ?_)
      set F2 := encPair F1 encUnary
      have hq2 := fst F1 encUnary
      have hi2 := snd F1 encUnary
      have hidx : ComputableInPolyTime
          (fun w : ((BoundedILPInstance × ℕ) × ℕ) × ℕ ↦
            (2 * w.1.1.1.numVars + w.1.1.1.matrix.length) + 1 +
              w.1.2 * w.1.1.1.matrix.length + w.2)
          F2 encUnary := by fun_prop
      have hwji := listGetDWithInput (hfields.comp (hp1.comp hq2)) hidx 0
      have hrpi := listGetDWithInput (hrhsP.comp (hp1.comp hq2)) hi2 0
      exact intBin_mul' hwji hrpi
    have hdiv := computableInPolyTime_intTruncDiv.comp (hnum.prod (hdNat.comp hp1))
    exact intBin_add' hzj hdiv
  let uListFn (p : BoundedILPInstance × ℕ) : List ℤ :=
    (List.range p.1.numVars).map fun j ↦
      (xListFn p).getD j 0 - (xListFn p).getD (p.1.numVars + j) 0
  have huList : ComputableInPolyTime uListFn E (encList encIntBin) := by
    refine mapWithInput (range.comp hnVars) ?_
    set F1 := encPair E encUnary
    have hp1 := fst E encUnary
    have hj1 := snd E encUnary
    exact intBin_sub'
      (listGetDWithInput (hxList.comp hp1) hj1 0)
      (listGetDWithInput (hxList.comp hp1) (unary_add.comp ((hnVars.comp hp1).prod hj1)) 0)
  have hall : ComputableInPolyTime
      (fun p : BoundedILPInstance × ℕ ↦
        (List.range p.1.matrix.length).all fun i ↦
          decide (((List.range p.1.numVars).map fun j ↦
            (p.1.matrix.getD i []).getD j 0 * (uListFn p).getD j 0).sum ≤ p.1.rhs.getD i 0))
      E encBool := by
    refine allWithInput (range.comp hR) ?_
    set F1 := encPair E encUnary
    have hp1 := fst E encUnary
    have hi1 := snd E encUnary
    have hlhs : ComputableInPolyTime
        (fun q : (BoundedILPInstance × ℕ) × ℕ ↦
          ((List.range q.1.1.numVars).map fun j ↦
            (q.1.1.matrix.getD q.2 []).getD j 0 * (uListFn q.1).getD j 0).sum)
        F1 encIntBin := by
      refine intBin_sum.comp (mapWithInput (range.comp (hnVars.comp hp1)) ?_)
      set F2 := encPair F1 encUnary
      have hq2 := fst F1 encUnary
      have hj2 := snd F1 encUnary
      have hrow : ComputableInPolyTime
          (fun w : ((BoundedILPInstance × ℕ) × ℕ) × ℕ ↦ w.1.1.1.matrix.getD w.1.2 [])
          F2 (encList encIntBin) :=
        listGetDWithInput (hm.comp (hp1.comp hq2)) (hi1.comp hq2) []
      exact intBin_mul' (listGetDWithInput hrow hj2 0)
        (listGetDWithInput (huList.comp (hp1.comp hq2)) hj2 0)
    exact intBin_le' hlhs (listGetDWithInput (hb.comp hp1) hi1 0)
  exact hall.of_enc_eq fun _ ↦ rfl

end PolyTimeVerifier

/-! ### Exactness of `verifyILPCertificate` and FPT theorem -/

private lemma sum_map_range_int (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k.1 := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
                 simp

private lemma flatMap_range_getD {α : Type} (m R : ℕ) (g : ℕ → List α)
    (hg : ∀ a < m, (g a).length = R) (dflt : α)
    {a b : ℕ} (ha : a < m) (hb : b < R) :
    ((List.range m).flatMap g).getD (a * R + b) dflt = (g a).getD b dflt := by
  induction m with
  | zero => omega
  | succ m' ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen_pre : ((List.range m').flatMap g).length = m' * R := by
      rw [List.length_flatMap]
      have hmap : ((List.range m').map fun x ↦ (g x).length) = List.replicate m' R :=
        List.ext_getElem (by simp) fun t ht _ ↦ by
          simp only [List.length_map, List.length_range] at ht
          simp [hg t (by omega)]
      rw [hmap, List.sum_replicate, smul_eq_mul]
    by_cases ham : a < m'
    · have hlt : a * R + b < m' * R := by
        have h1 : (a + 1) * R ≤ m' * R := Nat.mul_le_mul_right R ham
        linarith
      rw [List.getD_append _ _ _ _ (by rwa [hlen_pre])]
      exact ih (fun x hx ↦ hg x (by omega)) ham
    · have ha_eq : a = m' := by omega
      subst ha_eq
      rw [List.getD_append_right _ _ _ _ (by rw [hlen_pre]; omega), hlen_pre,
        Nat.add_sub_cancel_left]

theorem exists_verifyILPCertificate_iff (I : BoundedILPInstance) :
    I ∈ BoundedEntryILP ↔ ∃ r < 2 ^ ilpTotalBits I, verifyILPCertificate (I, r) = true := by
  constructor
  · rintro ⟨u₀, hu₀⟩
    set p := I.numVars
    set R := I.matrix.length
    set Q := 2 * p + R
    set L := maxActiveEntryBits I
    set B := 2 ^ L
    have hB1 : 1 ≤ B := Nat.one_le_pow L 2 (by omega)
    have hA_le : ∀ i j, |ilpMatrix I i j| ≤ B := abs_ilpMatrix_le I
    obtain ⟨x₀, hx₀, hAx₀⟩ := nonnegFormFin_solution hu₀
    have hA'_le := abs_nonnegFormFin_le hB1 hA_le
    obtain ⟨z, d, W, x, hx, hAx, hd_pos, hz_le, hd_le, hW_le, hW_eq⟩ :=
      exists_gram_adjugate_certificate hB1 hA'_le hx₀ hAx₀
    set magBits := ilpFieldMagBits p R L
    set fw := magBits + 1
    set fc := Q + 1 + Q * R
    have hM_lt : (Q + 1) * B * (Q.factorial * (R * ((Q + 1) * B) ^ 2 + 1) ^ Q) < 2 ^ magBits :=
      natAbs_lt_two_pow_ilpFieldMagBits p R L
    let valList : List ℤ :=
      (List.ofFn z ++ [d]) ++
        ((List.range Q).flatMap fun j ↦
          (List.range R).map fun i ↦
            if hj : j < Q then if hi : i < R then W ⟨j, hj⟩ ⟨i, hi⟩ else 0 else 0)
    have hval_len : valList.length = fc := by
      have hflat_len : (((List.range Q).flatMap fun j ↦
          (List.range R).map fun i ↦
            if hj : j < Q then if hi : i < R then W ⟨j, hj⟩ ⟨i, hi⟩ else 0 else 0)).length =
          Q * R := by
        rw [List.length_flatMap]
        simp [List.map_const']
      simp only [valList, List.length_append, List.length_ofFn, List.length_singleton, hflat_len]
      rfl
    have hval_lt : ∀ v ∈ valList, v.natAbs < 2 ^ magBits := by
      intro v hv
      simp only [valList, List.mem_append, List.mem_ofFn, List.mem_singleton, List.mem_flatMap,
        List.mem_range, List.mem_map] at hv
      have hle : |v| ≤ ((Q + 1) * B * (Q.factorial * (R * ((Q + 1) * B) ^ 2 + 1) ^ Q) : ℕ) := by
        rcases hv with (⟨j, rfl⟩ | rfl) | ⟨j, hj, i, hi, rfl⟩
        · exact hz_le j
        · exact hd_le
        · simp only [hj, hi, ↓reduceDIte]; exact hW_le ⟨j, hj⟩ ⟨i, hi⟩
      have hnat : v.natAbs ≤ (Q + 1) * B * (Q.factorial * (R * ((Q + 1) * B) ^ 2 + 1) ^ Q) := by
        rw [Int.abs_eq_natAbs] at hle
        exact_mod_cast hle
      exact hnat.trans_lt hM_lt
    let words : List (List Bool) := valList.map (encodeSignedField magBits)
    let fullWord : List Bool := words.flatten
    have hwords_len : ∀ w ∈ words, w.length = fw := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact length_encodeSignedField (hval_lt v hv)
    have hfull_len : fullWord.length = fc * fw := by
      rw [List.length_flatten, List.map_congr_left fun w hw ↦ hwords_len w hw,
        List.map_const', List.sum_replicate, smul_eq_mul]
      simp [words, hval_len]
    let r : ℕ := (BitVec.ofBoolListLE fullWord).toNat
    have hr_lt : r < 2 ^ ilpTotalBits I := by
      have h1 : r < 2 ^ fullWord.length := BitVec.isLt _
      rwa [hfull_len] at h1
    have hlow : Cslib.BitString.lowBits (fc * fw) r = fullWord := by
      apply List.ext_getElem (by simp [hfull_len])
      intro k hk₁ hk₂
      simp only [Cslib.BitString.lowBits, List.getElem_map, List.getElem_range, r,
        BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk₂, Option.getD_some]
    have hrows_eq : Cslib.BitString.listRows fc fw
        (Cslib.BitString.lowBits (fc * fw) r) = words := by
      rw [hlow]
      have hwlen : words.length = fc := by simp [words, hval_len]
      rw [← hwlen]
      exact Cslib.BitString.listRows_flatten words hwords_len
    have hfields_eq : words.map decodeSignedField = valList := by
      simp [words, List.map_map, Function.comp_def, decodeSignedField_encodeSignedField]
    -- Indexing helper into `valList`
    have hofFn_len : (List.ofFn z).length = Q := by
      simp only [List.length_ofFn]
      rfl
    have hval_z (k : ℕ) (hk : k < Q) : valList.getD k 0 = z ⟨k, hk⟩ := by
      simp only [valList]
      rw [List.getD_append _ _ _ _ (by simp [hofFn_len]; omega),
        List.getD_append _ _ _ _ (by rwa [hofFn_len]),
        List.getD_eq_getElem _ _ (by rwa [hofFn_len]), List.getElem_ofFn]
    have hval_d : valList.getD Q 0 = d := by
      simp only [valList]
      rw [List.getD_append _ _ _ _ (by simp [hofFn_len]),
        List.getD_append_right _ _ _ _ (by rw [hofFn_len]),
        hofFn_len, Nat.sub_self]
      rfl
    have hval_W (j : ℕ) (hj : j < Q) (i : ℕ) (hi : i < R) :
        valList.getD (Q + 1 + j * R + i) 0 = W ⟨j, hj⟩ ⟨i, hi⟩ := by
      simp only [valList]
      have hpre_len : (List.ofFn z ++ [d]).length = Q + 1 := by simp [hofFn_len]
      have hidx_eq : Q + 1 + j * R + i - (Q + 1) = j * R + i := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hpre_len]; omega), hpre_len, hidx_eq,
        flatMap_range_getD Q R _ (fun _ _ ↦ by simp) 0 hj hi,
        List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range]
      simp [hj, hi]
    refine ⟨r, hr_lt, ?_⟩
    unfold verifyILPCertificate
    dsimp only
    change (let rows := Cslib.BitString.listRows fc fw (Cslib.BitString.lowBits (fc * fw) r); _) =
      true
    rw [hrows_eq]
    dsimp only
    rw [hfields_eq]
    -- Show `zList.getD k 0 = z ⟨k, hk⟩`, `dNat = d.toNat`, `rhsPrime.getD i 0 = (b - A' *ᵥ z) i`,
    -- and `xList.getD j 0 = x ⟨j, hj⟩`
    let zList : List ℤ := (List.range Q).map fun k ↦ valList.getD k 0
    have hz_get (k : ℕ) (hk : k < Q) : zList.getD k 0 = z ⟨k, hk⟩ := by
      dsimp [zList]
      rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_map, List.getElem_range,
        hval_z k hk]
    let rhsPrime : List ℤ := (List.range R).map fun i ↦
      I.rhs.getD i 0 -
        ((List.range p).map fun j ↦
          (I.matrix.getD i []).getD j 0 * (zList.getD j 0 - zList.getD (p + j) 0)).sum -
        zList.getD (2 * p + i) 0
    have hrhs_get (i : Fin R) :
        rhsPrime.getD i.1 0 = (ilpRhs I - nonnegFormFin (ilpMatrix I) *ᵥ z) i := by
      dsimp only [rhsPrime]
      rw [List.getD_eq_getElem _ _ (by simp [i.2]), List.getElem_map, List.getElem_range,
        Pi.sub_apply, nonnegFormFin_mulVec, sum_map_range_int]
      have h1 : ∑ j : Fin p,
          (I.matrix.getD i.1 []).getD j.1 0 * (zList.getD j.1 0 - zList.getD (p + j.1) 0) =
          ∑ j : Fin p,
            ilpMatrix I i j * (z ⟨j.1, by omega⟩ - z ⟨p + j.1, by omega⟩) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [List.getD_eq_getElem _ _ i.2, hz_get j.1 (by omega), hz_get (p + j.1) (by omega)]
        rfl
      rw [h1, hz_get (2 * p + i.1) (by omega)]
      dsimp only [ilpRhs]
      ring
    have hd_toNat : (valList.getD Q 0).toNat = d.natAbs := by
      rw [hval_d]; omega
    have hdNat_pos : 0 < (valList.getD Q 0).toNat := by
      rw [hval_d]; omega
    have hdNat_cast : (((valList.getD Q 0).toNat : ℕ) : ℤ) = d := by
      rw [hval_d]; omega
    let xList : List ℤ := (List.range Q).map fun j ↦
      zList.getD j 0 +
        intTruncDiv
          (((List.range R).map fun i ↦
            valList.getD (Q + 1 + j * R + i) 0 * rhsPrime.getD i 0).sum)
          (valList.getD Q 0).toNat
    have hx_get (j : ℕ) (hj : j < Q) : xList.getD j 0 = x ⟨j, hj⟩ := by
      dsimp only [xList]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range,
        hz_get j hj, sum_map_range_int]
      have hnum : (∑ i : Fin R, valList.getD (Q + 1 + j * R + i.1) 0 * rhsPrime.getD i.1 0) =
          (x ⟨j, hj⟩ - z ⟨j, hj⟩) * ((valList.getD Q 0).toNat : ℤ) := by
        have h1 : (∑ i : Fin R, valList.getD (Q + 1 + j * R + i.1) 0 * rhsPrime.getD i.1 0) =
            (W *ᵥ (ilpRhs I - nonnegFormFin (ilpMatrix I) *ᵥ z)) ⟨j, hj⟩ := by
          change _ = ∑ i : Fin R, W ⟨j, hj⟩ i * (ilpRhs I - nonnegFormFin (ilpMatrix I) *ᵥ z) i
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hval_W j hj i.1 i.2, hrhs_get i]
        rw [h1, hW_eq ⟨j, hj⟩, hdNat_cast]
      rw [hnum, intTruncDiv_mul_cancel _ hdNat_pos]
      ring
    rw [List.all_eq_true]
    intro i hi_r
    have hi : i < R := List.mem_range.mp hi_r
    rw [decide_eq_true_eq, sum_map_range_int]
    have hrow_eq : (∑ j : Fin p,
        (I.matrix.getD i []).getD j.1 0 *
          (((List.range p).map fun k ↦
            xList.getD k 0 - xList.getD (p + k) 0).getD j.1 0)) =
        ∑ j : Fin p, ilpMatrix I ⟨i, hi⟩ j *
          (x ⟨j.1, by omega⟩ - x ⟨p + j.1, by omega⟩) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [List.getD_eq_getElem I.matrix [] hi,
        List.getD_eq_getElem ((List.range p).map _) 0
          (by simp only [List.length_map, List.length_range]; exact j.2),
        List.getElem_map, List.getElem_range, hx_get j.1 (by omega), hx_get (p + j.1) (by omega)]
      rfl
    rw [hrow_eq]
    have hAx_i := congrFun hAx ⟨i, hi⟩
    rw [nonnegFormFin_mulVec] at hAx_i
    have hslack_nn : 0 ≤ x ⟨2 * p + i, by omega⟩ := hx ⟨2 * p + i, by omega⟩
    dsimp only [ilpRhs] at hAx_i
    linarith
  · -- Soundness: `verifyILPCertificate (I, r) = true` directly witnesses `u : Fin numVars → ℤ`
    rintro ⟨r, _, hok⟩
    unfold verifyILPCertificate at hok
    dsimp only at hok
    rw [List.all_eq_true] at hok
    -- Extract the constructed `uList`
    set nVars := I.numVars
    set R := I.matrix.length
    set Q := 2 * nVars + R
    set L := maxActiveEntryBits I
    set magBits := ilpFieldMagBits nVars R L
    set fieldWidth := magBits + 1
    set fieldCount := Q + 1 + Q * R
    set rows := Cslib.BitString.listRows fieldCount fieldWidth
      (Cslib.BitString.lowBits (fieldCount * fieldWidth) r)
    set fields : List ℤ := rows.map decodeSignedField
    set zList : List ℤ := (List.range Q).map fun k ↦ fields.getD k 0
    set dNat : ℕ := (fields.getD Q 0).toNat
    set rhsPrime : List ℤ := (List.range R).map fun i ↦
      I.rhs.getD i 0 -
        ((List.range nVars).map fun j ↦
          (I.matrix.getD i []).getD j 0 * (zList.getD j 0 - zList.getD (nVars + j) 0)).sum -
        zList.getD (2 * nVars + i) 0
    set xList : List ℤ := (List.range Q).map fun j ↦
      zList.getD j 0 +
        intTruncDiv
          (((List.range R).map fun i ↦
            fields.getD (Q + 1 + j * R + i) 0 * rhsPrime.getD i 0).sum)
          dNat
    set uList : List ℤ := (List.range nVars).map fun j ↦
      xList.getD j 0 - xList.getD (nVars + j) 0
    rw [mem_BoundedEntryILP_iff]
    refine ⟨fun j ↦ uList.getD j.1 0, fun i hi ↦ ?_⟩
    have hi_ok := of_decide_eq_true (hok i (List.mem_range.mpr hi))
    rw [sum_map_range_int, List.getD_eq_getElem _ _ hi] at hi_ok
    exact hi_ok

/-- **Power-exponential FPT time bound for `BoundedEntryILP`**: integer linear inequality
feasibility `A u ≤ b` is decidable in time
`2 ^ O((numVars + numRows + maxActiveEntryBits)^4) * poly(|I|)`. -/
theorem BoundedEntryILP_decidableInPowerExpTime :
    DecidableInPowerExpTime BoundedEntryILP encBoundedILP ilpParam 4 := by
  obtain ⟨e, hleaf⟩ := DecidableInExpTime.of_computableInPolyTime (μ := fun _ ↦ 0)
    computableInPolyTime_verifyILPCertificate
    (A := {p : BoundedILPInstance × ℕ | verifyILPCertificate p = true})
    (fun _ ↦ Iff.rfl)
  have hleafP : DecidableInPowerExpTime
      {p : BoundedILPInstance × ℕ | verifyILPCertificate p = true}
      (encPair encBoundedILP encNat) (fun _ ↦ 0) 0 :=
    ⟨0, e, by simpa using hleaf⟩
  have hres := DecidableInPowerExpTime.of_exhaustiveSearch
    (f := id) (ν := ilpTotalBits)
    id' computableInPolyTime_ilpTotalBits
    (fun I ↦ exists_verifyILPCertificate_iff I)
    (C := 250) (K := 0) (q := 4) (b := 0) (p := 0)
    ilpTotalBits_le_poly_param
    (fun _ _ ↦ by simp)
    le_rfl
    hleafP
  simpa using hres

/-- `BoundedEntryILP` is fixed-parameter
tractable parameterized by `ilpParam` (`numVars + numRows + maxActiveEntryBits`). -/
theorem BoundedEntryILP_mem_FPT :
    BoundedEntryILP ∈ FPT encBoundedILP ilpParam :=
  decidableInPowerExpTime_mem_FPT BoundedEntryILP_decidableInPowerExpTime

/-- Corollary: `BoundedEntryILP` is fixed-parameter tractable parameterized by
`ilpMagnitudeParam` (`numVars + numRows + maxActiveEntryNatAbs`). -/
theorem BoundedEntryILP_mem_FPT_magnitude :
    BoundedEntryILP ∈ FPT encBoundedILP ilpMagnitudeParam :=
  FPT_subset_FPT_of_le_comp (h := id) ilpParam_le_ilpMagnitudeParam BoundedEntryILP_mem_FPT

/-- Non-degenerate intended-domain witness for `BoundedEntryILP` with large right-hand side
(`2` variables, `3` constraints, large RHS `10^6`, unique solution `u = (500000, 500000)`). -/
theorem boundedEntryILP_witness :
    let I : BoundedILPInstance :=
      ⟨2, [[1, 1], [-1, 0], [0, -1]], [1000000, -500000, -500000]⟩
    I ∈ BoundedEntryILP ∧ ilpMagnitudeParam I = 6 := by
  intro I
  refine ⟨⟨![500000, 500000], fun i ↦ ?_⟩, by decide⟩
  fin_cases i <;> decide

end CslibFrontier.Complexity
