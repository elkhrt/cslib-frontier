/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Affine Rank Minimization (`ARM(k)`) and Arithmetic Circuit Definitions

Core definitions for the Affine Rank Minimization decision problem `ARM(k)` over `ℝ`,
its binary encoding `encARMInstance`, the Frobenius inner product, block-matrix constraint
compilation, and topologically ordered arithmetic circuits over `ℝ`.
-/

public section

namespace Cslib.Complexity

open Matrix Turing.MultiTapeTM

/-! ### Frobenius inner product and elementary matrices -/

/-- The Frobenius inner product `⟨A, X⟩ = ∑ i, ∑ j, A i j * X i j` on `m × n` real matrices. -/
@[expose] def frobeniusInner {m n : ℕ} (A X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j * X i j

/-- Explicit double-sum expansion of the Frobenius inner product. -/
theorem frobeniusInner_eq_sum {m n : ℕ} (A X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner A X = ∑ i : Fin m, ∑ j : Fin n, A i j * X i j := rfl

/-- Left-additivity of the Frobenius inner product. -/
theorem frobeniusInner_add_left {m n : ℕ} (A B X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner (A + B) X = frobeniusInner A X + frobeniusInner B X := by
  simp only [frobeniusInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- Left-subtraction of the Frobenius inner product. -/
theorem frobeniusInner_sub_left {m n : ℕ} (A B X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner (A - B) X = frobeniusInner A X - frobeniusInner B X := by
  simp only [frobeniusInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Left-scaling of the Frobenius inner product. -/
theorem frobeniusInner_smul_left {m n : ℕ} (c : ℝ) (A X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner (c • A) X = c * frobeniusInner A X := by
  simp only [frobeniusInner, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Elementary rational matrix `E^{(r, c)}` with `1` at `(r, c)` and `0` elsewhere. -/
@[expose] def entryMatrix (m n : ℕ) (r : Fin m) (c : Fin n) : Matrix (Fin m) (Fin n) ℚ :=
  Matrix.of fun i j ↦ if i = r ∧ j = c then 1 else 0

/-- Entry formula for the elementary rational matrix `entryMatrix`. -/
@[simp] theorem entryMatrix_apply (m n : ℕ) (r : Fin m) (c : Fin n) (i : Fin m) (j : Fin n) :
    entryMatrix m n r c i j = if i = r ∧ j = c then 1 else 0 := rfl

/-- Elementary real matrix `E^{(r, c)}` with `1` at `(r, c)` and `0` elsewhere. -/
@[expose] def entryMatrixReal (m n : ℕ) (r : Fin m) (c : Fin n) : Matrix (Fin m) (Fin n) ℝ :=
  (entryMatrix m n r c).map ((↑) : ℚ → ℝ)

/-- Casting the rational elementary matrix recovers `entryMatrixReal`. -/
theorem entryMatrix_map_cast (m n : ℕ) (r : Fin m) (c : Fin n) :
    (entryMatrix m n r c).map ((↑) : ℚ → ℝ) = entryMatrixReal m n r c := rfl

/-- Entry formula for the elementary real matrix `entryMatrixReal`. -/
@[simp] theorem entryMatrixReal_apply (m n : ℕ) (r : Fin m) (c : Fin n) (i : Fin m) (j : Fin n) :
    entryMatrixReal m n r c i j = if i = r ∧ j = c then 1 else 0 := by
  simp only [entryMatrixReal, Matrix.map_apply, entryMatrix_apply]
  split_ifs <;> simp

/-- Inner product with an elementary matrix extracts the designated entry `X r c`. -/
@[simp] theorem frobeniusInner_entryMatrixReal {m n : ℕ} (r : Fin m) (c : Fin n)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner (entryMatrixReal m n r c) X = X r c := by
  simp only [frobeniusInner, entryMatrixReal, entryMatrix, Matrix.map_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro j _ hj; simp [hj]
    · intro hc; exact absurd (Finset.mem_univ c) hc
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]
  · intro hr; exact absurd (Finset.mem_univ r) hr

/-- Difference of two elementary rational matrices `E^{(r₁, c₁)} - E^{(r₂, c₂)}`. -/
@[expose] def entryDiffMatrix (m n : ℕ) (r₁ : Fin m) (c₁ : Fin n) (r₂ : Fin m) (c₂ : Fin n) :
    Matrix (Fin m) (Fin n) ℚ :=
  entryMatrix m n r₁ c₁ - entryMatrix m n r₂ c₂

/-- Inner product with a difference of elementary matrices extracts `X r₁ c₁ - X r₂ c₂`. -/
@[simp] theorem frobeniusInner_entryDiffMatrix {m n : ℕ} (r₁ : Fin m) (c₁ : Fin n)
    (r₂ : Fin m) (c₂ : Fin n) (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((entryDiffMatrix m n r₁ c₁ r₂ c₂).map ((↑) : ℚ → ℝ)) X =
      X r₁ c₁ - X r₂ c₂ := by
  have hmap : (entryDiffMatrix m n r₁ c₁ r₂ c₂).map ((↑) : ℚ → ℝ) =
      entryMatrixReal m n r₁ c₁ - entryMatrixReal m n r₂ c₂ := by
    ext i j
    simp [entryDiffMatrix, entryMatrixReal]
  rw [hmap, frobeniusInner_sub_left, frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal]

/-! ### Block-matrix selection identities and constraint compilation -/

/-- Row-selection matrix `S_I ∈ {0, 1}^{p × m}` associated to an index map `I : Fin p → Fin m`. -/
@[expose] def rowSelectionMatrix {p m : ℕ} (I : Fin p → Fin m) : Matrix (Fin p) (Fin m) ℝ :=
  Matrix.of fun a i ↦ if i = I a then 1 else 0

/-- Column-selection matrix `T_J ∈ {0, 1}^{n × q}` associated to `J : Fin q → Fin n`. -/
@[expose] def colSelectionMatrix {n q : ℕ} (J : Fin q → Fin n) : Matrix (Fin n) (Fin q) ℝ :=
  Matrix.of fun j b ↦ if j = J b then 1 else 0

/-- Block-selection identity `X[I, J] = S_I X T_J` (). -/
theorem submatrix_eq_selection_mul {m n p q : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (I : Fin p → Fin m) (J : Fin q → Fin n) :
    X.submatrix I J = rowSelectionMatrix I * X * colSelectionMatrix J := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, rowSelectionMatrix, colSelectionMatrix,
    Matrix.of_apply]
  have hL : ∀ j : Fin n,
      (∑ i : Fin m, (if i = I a then (1 : ℝ) else 0) * X i j) = X (I a) j := by
    intro j
    rw [Finset.sum_eq_single (I a)]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hL]
  rw [Finset.sum_eq_single (J b)]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Designated-entry decoding map (, ). -/
@[expose] def designatedEntry {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (c : Fin n) :
    ℝ :=
  X r c

/-- Designated-entry decoding returns the `(r, c)` matrix entry. -/
@[simp] theorem designatedEntry_apply {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin m) (c : Fin n) : designatedEntry X r c = X r c := rfl

/-- Consistency constraint equating two designated entries (). -/
@[expose] def consistencyConstraint {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (r₁ : Fin m) (c₁ : Fin n) (r₂ : Fin m) (c₂ : Fin n) : Prop :=
  X r₁ c₁ = X r₂ c₂

/-- fixing an entry and equating two entries
are each representable by a single affine Frobenius constraint with rational coefficients in
`{0, ±1}`. -/
theorem entry_constraints {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    (∀ (r : Fin m) (c : Fin n) (a : ℚ),
      ∃ (A : Matrix (Fin m) (Fin n) ℚ) (b : ℚ),
        (∀ i j, A i j ∈ ({0, 1} : Set ℚ)) ∧
        (frobeniusInner (A.map ((↑) : ℚ → ℝ)) X = (b : ℝ) ↔ X r c = (a : ℝ))) ∧
    (∀ (r₁ : Fin m) (c₁ : Fin n) (r₂ : Fin m) (c₂ : Fin n),
      ∃ (A : Matrix (Fin m) (Fin n) ℚ) (b : ℚ),
        (∀ i j, A i j ∈ ({-1, 0, 1} : Set ℚ)) ∧
        (frobeniusInner (A.map ((↑) : ℚ → ℝ)) X = (b : ℝ) ↔ X r₁ c₁ = X r₂ c₂)) := by
  refine ⟨fun r c a ↦ ⟨entryMatrix m n r c, a, fun i j ↦ ?_, ?_⟩,
    fun r₁ c₁ r₂ c₂ ↦ ⟨entryDiffMatrix m n r₁ c₁ r₂ c₂, 0, fun i j ↦ ?_, ?_⟩⟩
  · simp only [entryMatrix, Matrix.of_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs <;> simp
  · change frobeniusInner (entryMatrixReal m n r c) X = (a : ℝ) ↔ _
    rw [frobeniusInner_entryMatrixReal]
  · simp only [entryDiffMatrix, entryMatrix, Matrix.sub_apply, Matrix.of_apply,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs <;> norm_num
  · rw [frobeniusInner_entryDiffMatrix, Rat.cast_zero, sub_eq_zero]

/-- fixing `T` designated entries is
representable by `T` affine constraints with `{0, 1}` coefficients, and equating two
`p × q` submatrices is representable by `p * q` affine constraints with `{0, ±1}` coefficients. -/
theorem block_constraints_compile {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    (∀ (T : ℕ) (pos : Fin T → Fin m × Fin n) (vals : Fin T → ℚ),
      ∃ (A : Fin T → Matrix (Fin m) (Fin n) ℚ) (b : Fin T → ℚ),
        (∀ t i j, A t i j ∈ ({0, 1} : Set ℚ)) ∧
        ((∀ t, frobeniusInner ((A t).map ((↑) : ℚ → ℝ)) X = (b t : ℝ)) ↔
          ∀ t, X (pos t).1 (pos t).2 = (vals t : ℝ))) ∧
    (∀ {p q : ℕ} (I I' : Fin p → Fin m) (J J' : Fin q → Fin n),
      ∃ (A : Fin p × Fin q → Matrix (Fin m) (Fin n) ℚ) (b : Fin p × Fin q → ℚ),
        (∀ idx i j, A idx i j ∈ ({-1, 0, 1} : Set ℚ)) ∧
        ((∀ idx, frobeniusInner ((A idx).map ((↑) : ℚ → ℝ)) X = (b idx : ℝ)) ↔
          X.submatrix I J = X.submatrix I' J')) := by
  constructor
  · intro T pos vals
    refine ⟨fun t ↦ entryMatrix m n (pos t).1 (pos t).2, vals, fun t i j ↦ ?_, ?_⟩
    · simp only [entryMatrix, Matrix.of_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
      split_ifs <;> simp
    · constructor <;> intro h t
      · have ht := h t
        have hmap : (entryMatrix m n (pos t).1 (pos t).2).map ((↑) : ℚ → ℝ) =
            entryMatrixReal m n (pos t).1 (pos t).2 := by
          ext i j; simp [entryMatrixReal]
        rw [hmap, frobeniusInner_entryMatrixReal] at ht
        exact ht
      · have hmap : (entryMatrix m n (pos t).1 (pos t).2).map ((↑) : ℚ → ℝ) =
            entryMatrixReal m n (pos t).1 (pos t).2 := by
          ext i j; simp [entryMatrixReal]
        rw [hmap, frobeniusInner_entryMatrixReal]
        exact h t
  · intro p q I I' J J'
    refine ⟨fun idx ↦ entryDiffMatrix m n (I idx.1) (J idx.2) (I' idx.1) (J' idx.2),
      fun _ ↦ 0, fun idx i j ↦ ?_, ?_⟩
    · simp only [entryDiffMatrix, entryMatrix, Matrix.sub_apply, Matrix.of_apply,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      split_ifs <;> norm_num
    · simp only [frobeniusInner_entryDiffMatrix, Rat.cast_zero, sub_eq_zero, Prod.forall]
      constructor
      · intro h; ext a b; exact h a b
      · intro h a b; exact congrFun (congrFun h a) b

/-! ### Affine Rank Minimization `ARM(k)` () -/

/-- An instance of Affine Rank Minimization (): rational dimensions `rows × cols` and
a finite list of affine constraints `(A_ℓ, b_ℓ)` with `A_ℓ ∈ ℚ^{rows × cols}` and `b_ℓ ∈ ℚ`. -/
@[ext]
structure ARMInstance where
 /-- Number of matrix rows `m`. -/
  rows : ℕ
 /-- Number of matrix columns `n`. -/
  cols : ℕ
 /-- List of rational affine constraints `(A_ℓ, b_ℓ)`. -/
  constraints : List (List (List ℚ) × ℚ)
 /-- Each constraint matrix has `rows` rows, each of length `cols`. -/
  dims_ok : ∀ c ∈ constraints, c.1.length = rows ∧ ∀ r ∈ c.1, r.length = cols

/-- Convert a list-of-lists constraint matrix of an `ARMInstance` to a `Matrix`. -/
@[expose] def ARMInstance.matrixAt (inst : ARMInstance) (c : List (List ℚ) × ℚ) :
    Matrix (Fin inst.rows) (Fin inst.cols) ℚ :=
  Matrix.of fun i j ↦ (c.1.getD i.1 []).getD j.1 0

/-- Entry formula for `ARMInstance.matrixAt`. -/
@[simp] theorem ARMInstance.matrixAt_apply (inst : ARMInstance) (c : List (List ℚ) × ℚ)
    (i : Fin inst.rows) (j : Fin inst.cols) :
    inst.matrixAt c i j = (c.1.getD i.1 []).getD j.1 0 := rfl

/-- A real matrix `X` satisfies all affine constraints of an `ARMInstance`. -/
@[expose] def ARMInstance.Satisfies (inst : ARMInstance)
    (X : Matrix (Fin inst.rows) (Fin inst.cols) ℝ) : Prop :=
  ∀ c ∈ inst.constraints, frobeniusInner ((inst.matrixAt c).map ((↑) : ℚ → ℝ)) X = (c.2 : ℝ)

/-- Feasibility of an `ARM(k)` instance: there exists a real matrix `X` satisfying all affine
constraints with `rank(X) ≤ k`. -/
@[expose] def ARMInstance.Feasible (inst : ARMInstance) (k : ℕ) : Prop :=
  ∃ X : Matrix (Fin inst.rows) (Fin inst.cols) ℝ, inst.Satisfies X ∧ X.rank ≤ k

/-- The decision problem `ARM(k)` . -/
@[expose] def ARM (k : ℕ) : Set ARMInstance :=
  {inst | inst.Feasible k}

/-- Membership in `ARM k` unfolded to feasibility. -/
theorem mem_ARM_iff {k : ℕ} {inst : ARMInstance} : inst ∈ ARM k ↔ inst.Feasible k :=
  Iff.rfl

/-- Binary encoding of rational constraint lists in `ARMInstance`. -/
abbrev encARMConstraints : List (List (List ℚ) × ℚ) ↪ List Bool :=
  encList (encPair (encList (encList encRat)) encRat)

/-- Binary encoding of `ARMInstance` with binary dimensions `(rows, cols)` and framed rational
matrices and scalars. -/
@[expose] def encARMInstance : ARMInstance ↪ List Bool where
  toFun inst := encPair encNat (encPair encNat encARMConstraints)
    (inst.rows, (inst.cols, inst.constraints))
  inj' a b h := by
    have h' := (encPair encNat (encPair encNat encARMConstraints)).injective h
    exact ARMInstance.ext (congrArg Prod.fst h') (congrArg (fun p ↦ p.2.1) h')
      (congrArg (fun p ↦ p.2.2) h')

/-- Convert a `Matrix (Fin m) (Fin n) ℚ` to a row-list representation. -/
@[expose] def matrixToRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : List (List ℚ) :=
  List.ofFn fun i : Fin m ↦ List.ofFn fun j : Fin n ↦ A i j

/-- Row count of `matrixToRows`. -/
@[simp] theorem matrixToRows_length {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    (matrixToRows A).length = m := by
  simp [matrixToRows]

/-- Column count of every row in `matrixToRows`. -/
theorem matrixToRows_row_length {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) {r : List ℚ}
    (hr : r ∈ matrixToRows A) : r.length = n := by
  simp only [matrixToRows, List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  simp

/-- Reading back `(i, j)` from `matrixToRows A` recovers `A i j`. -/
theorem matrixToRows_getD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    ((matrixToRows A).getD i.1 []).getD j.1 0 = A i j := by
  simp [matrixToRows, List.getD_eq_getElem?_getD, i.2, j.2]

/-- Construct an `ARMInstance` from a finite list of `(Matrix, ℚ)` constraints. -/
@[expose] def ARMInstance.ofMatrices {m n : ℕ}
    (cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ)) : ARMInstance where
  rows := m
  cols := n
  constraints := cs.map fun p ↦ (matrixToRows p.1, p.2)
  dims_ok := by
    intro c hc
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    exact ⟨matrixToRows_length p.1, fun _ hr ↦ matrixToRows_row_length p.1 hr⟩

/-- Satisfaction of `ARMInstance.ofMatrices` is equivalent to satisfying each matrix equation. -/
theorem ARMInstance.satisfies_ofMatrices_iff {m n : ℕ}
    (cs : List (Matrix (Fin m) (Fin n) ℚ × ℚ)) (X : Matrix (Fin m) (Fin n) ℝ) :
    (ARMInstance.ofMatrices cs).Satisfies X ↔
      ∀ p ∈ cs, frobeniusInner (p.1.map ((↑) : ℚ → ℝ)) X = (p.2 : ℝ) := by
  constructor
  · intro h p hp
    have hc := h (matrixToRows p.1, p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hmat : (ARMInstance.ofMatrices cs).matrixAt (matrixToRows p.1, p.2) = p.1 := by
      ext i j
      exact matrixToRows_getD p.1 i j
    rw [← hmat]
    exact hc
  · intro h c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hmat : (ARMInstance.ofMatrices cs).matrixAt (matrixToRows p.1, p.2) = p.1 := by
      ext i j
      exact matrixToRows_getD p.1 i j
    rw [hmat]
    exact h p hp

/-! ### ETR Equality Form () -/

/-- An ETR instance in equality form :
a finite conjunction of integer-coefficient polynomial equalities over `ℝ^N`. -/
structure ETREqualitySystem where
 /-- Number of real variables `N`. -/
  numVars : ℕ
 /-- Integer-coefficient polynomials `f_1, …, f_T ∈ ℤ[y_1, …, y_N]`. -/
  polys : List (MvPolynomial (Fin numVars) ℤ)

/-- Satisfiability of an ETR equality-form system over `ℝ`. -/
@[expose] def ETREqualitySystem.Satisfiable (S : ETREqualitySystem) : Prop :=
  ∃ y : Fin S.numVars → ℝ, ∀ f ∈ S.polys, MvPolynomial.eval₂ (Int.castRingHom ℝ) y f = 0

/-! ### Arithmetic Circuits over `ℝ` (, ) -/

/-- A gate operation in a topologically ordered arithmetic circuit over `ℝ`
. -/
inductive ArithGate where
 /-- Input gate reading variable `x_idx`. -/
  | input (idx : ℕ)
 /-- Constant gate producing rational scalar `val ∈ ℚ`. -/
  | const (val : ℚ)
 /-- Binary addition gate `g₁ + g₂`. -/
  | add (lhs rhs : ℕ)
 /-- Binary multiplication gate `g₁ × g₂`. -/
  | mul (lhs rhs : ℕ)
 /-- Unary negation gate `-g₁`. -/
  | neg (arg : ℕ)
  deriving DecidableEq, Repr

/-- Well-formedness of a gate at topological index `bound` in a circuit with `numInputs` inputs. -/
@[expose] def ArithGate.WellFormed (numInputs bound : ℕ) : ArithGate → Prop
  | .input idx => idx < numInputs
  | .const _ => True
  | .add lhs rhs => lhs < bound ∧ rhs < bound
  | .mul lhs rhs => lhs < bound ∧ rhs < bound
  | .neg arg => arg < bound

/-- Well-formedness characterization for an input gate. -/
@[simp] theorem ArithGate.wellFormed_input (numInputs bound idx : ℕ) :
    (ArithGate.input idx).WellFormed numInputs bound ↔ idx < numInputs := Iff.rfl

/-- Well-formedness characterization for a constant gate. -/
@[simp] theorem ArithGate.wellFormed_const (numInputs bound : ℕ) (val : ℚ) :
    (ArithGate.const val).WellFormed numInputs bound ↔ True := Iff.rfl

/-- Well-formedness characterization for an addition gate. -/
theorem ArithGate.wellFormed_add (numInputs bound lhs rhs : ℕ) :
    (ArithGate.add lhs rhs).WellFormed numInputs bound ↔ lhs < bound ∧ rhs < bound := Iff.rfl

/-- Well-formedness characterization for a multiplication gate. -/
theorem ArithGate.wellFormed_mul (numInputs bound lhs rhs : ℕ) :
    (ArithGate.mul lhs rhs).WellFormed numInputs bound ↔ lhs < bound ∧ rhs < bound := Iff.rfl

/-- Well-formedness characterization for a negation gate. -/
@[simp] theorem ArithGate.wellFormed_neg (numInputs bound arg : ℕ) :
    (ArithGate.neg arg).WellFormed numInputs bound ↔ arg < bound := Iff.rfl

/-- Binary encoding of `ArithGate` for polynomial-time complexity accounting. -/
@[expose] def encArithGate : ArithGate ↪ List Bool where
  toFun
    | .input i => encSum encNat (encSum encRat (encSum (encPair encNat encNat)
        (encSum (encPair encNat encNat) encNat))) (.inl i)
    | .const c => encSum encNat (encSum encRat (encSum (encPair encNat encNat)
        (encSum (encPair encNat encNat) encNat))) (.inr (.inl c))
    | .add a b => encSum encNat (encSum encRat (encSum (encPair encNat encNat)
        (encSum (encPair encNat encNat) encNat))) (.inr (.inr (.inl (a, b))))
    | .mul a b => encSum encNat (encSum encRat (encSum (encPair encNat encNat)
        (encSum (encPair encNat encNat) encNat))) (.inr (.inr (.inr (.inl (a, b)))))
    | .neg a => encSum encNat (encSum encRat (encSum (encPair encNat encNat)
        (encSum (encPair encNat encNat) encNat))) (.inr (.inr (.inr (.inr a))))
  inj' a b h := by
    cases a <;> cases b <;>
      have h' := (encSum encNat (encSum encRat (encSum (encPair encNat encNat)
        (encSum (encPair encNat encNat) encNat)))).injective h <;>
      simp_all

/-- An arithmetic circuit over `ℝ` in topological order with a designated output gate
. -/
structure ArithCircuit where
 /-- Number of input variables `x_1, …, x_n`. -/
  numInputs : ℕ
 /-- Topologically ordered finite list of gates. -/
  gates : List ArithGate
 /-- Index of the designated output gate `g_out`. -/
  output : ℕ
 /-- Acyclicity and input-index validity of every gate. -/
  gates_wf : ∀ (k : ℕ) (hk : k < gates.length), gates[k].WellFormed numInputs k
 /-- The designated output gate lies in `gates`. -/
  output_lt : output < gates.length

/-- Size of an arithmetic circuit: the number of gates . -/
@[expose] def ArithCircuit.size (C : ArithCircuit) : ℕ :=
  C.gates.length

/-- Size of an arithmetic circuit equals `C.gates.length`. -/
@[simp] theorem ArithCircuit.size_eq_length (C : ArithCircuit) :
    C.size = C.gates.length := rfl

/-- Bit-size of an arithmetic circuit: gate count plus total bit-length of all rational
constants . -/
@[expose] def ArithCircuit.bitSize (C : ArithCircuit) : ℕ :=
  C.gates.length + (C.gates.map fun
    | .const c => (encRat c).length
    | _ => 0).sum

/-- Evaluate a single gate given already-evaluated values of earlier gates. -/
@[expose] def evalGateStep {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) : ArithGate → ℝ
  | .input idx => if h : idx < n then x ⟨idx, h⟩ else 0
  | .const c => (c : ℝ)
  | .add l r => vals.getD l 0 + vals.getD r 0
  | .mul l r => vals.getD l 0 * vals.getD r 0
  | .neg a => -(vals.getD a 0)

/-- Evaluation of an input gate. -/
@[simp] theorem evalGateStep_input {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) (idx : ℕ) :
    evalGateStep x vals (.input idx) = if h : idx < n then x ⟨idx, h⟩ else 0 := rfl

/-- Evaluation of a constant gate. -/
@[simp] theorem evalGateStep_const {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) (c : ℚ) :
    evalGateStep x vals (.const c) = (c : ℝ) := rfl

/-- Evaluation of an addition gate. -/
@[simp] theorem evalGateStep_add {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) (l r : ℕ) :
    evalGateStep x vals (.add l r) = vals.getD l 0 + vals.getD r 0 := rfl

/-- Evaluation of a multiplication gate. -/
@[simp] theorem evalGateStep_mul {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) (l r : ℕ) :
    evalGateStep x vals (.mul l r) = vals.getD l 0 * vals.getD r 0 := rfl

/-- Evaluation of a negation gate. -/
@[simp] theorem evalGateStep_neg {n : ℕ} (x : Fin n → ℝ) (vals : List ℝ) (a : ℕ) :
    evalGateStep x vals (.neg a) = -(vals.getD a 0) := rfl

/-- Evaluate all gates of a circuit in topological order, returning the list of gate values. -/
@[expose] def evalGatesList {n : ℕ} (x : Fin n → ℝ) (gates : List ArithGate) : List ℝ :=
  gates.foldl (fun acc g ↦ acc ++ [evalGateStep x acc g]) []

/-- Empty gate list evaluates to the empty value list. -/
@[simp] theorem evalGatesList_nil {n : ℕ} (x : Fin n → ℝ) :
    evalGatesList x [] = [] := rfl

/-- Explicit fold characterization of `evalGatesList`. -/
theorem evalGatesList_eq_foldl {n : ℕ} (x : Fin n → ℝ) (gates : List ArithGate) :
    evalGatesList x gates = gates.foldl (fun acc g ↦ acc ++ [evalGateStep x acc g]) [] := rfl

/-- Appending a single gate extends `evalGatesList` by one evaluated value. -/
theorem evalGatesList_append_singleton {n : ℕ} (x : Fin n → ℝ)
    (gs : List ArithGate) (g : ArithGate) :
    evalGatesList x (gs ++ [g]) =
      evalGatesList x gs ++ [evalGateStep x (evalGatesList x gs) g] := by
  simp [evalGatesList]

/-- Length of `evalGatesList` equals the number of gates. -/
@[simp] theorem evalGatesList_length {n : ℕ} (x : Fin n → ℝ) (gates : List ArithGate) :
    (evalGatesList x gates).length = gates.length := by
  unfold evalGatesList
  suffices ∀ (acc : List ℝ) (gs : List ArithGate),
      (gs.foldl (fun a g ↦ a ++ [evalGateStep x a g]) acc).length = acc.length + gs.length by
    simpa using this [] gates
  intro acc gs
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

private theorem foldl_append_prefix {α : Type*} (d : α) (f : List α → ArithGate → α)
    (gs : List ArithGate) (acc : List α) (k : ℕ) (hk : k < acc.length) :
    (gs.foldl (fun a g ↦ a ++ [f a g]) acc).getD k d = acc.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc g]).length := by simp; omega
    rw [ih (acc ++ [f acc g]) hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private theorem foldl_append_getD_eq {n : ℕ} (x : Fin n → ℝ) (gs : List ArithGate)
    (acc : List ℝ) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl (fun a g ↦ a ++ [evalGateStep x a g]) acc).getD (acc.length + k) 0 =
      evalGateStep x
        ((gs.take k).foldl (fun a g ↦ a ++ [evalGateStep x a g]) acc)
        gs[k] := by
  induction gs generalizing acc k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.take_zero, List.foldl_nil,
        List.getElem_cons_zero]
      have hlen : acc.length < (acc ++ [evalGateStep x acc g]).length := by simp
      have hprefix := foldl_append_prefix 0 (evalGateStep x) gs (acc ++ [evalGateStep x acc g])
        acc.length hlen
      rw [hprefix]
      simp [List.getD_eq_getElem?_getD]
    | succ k' =>
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have hk' : k' < gs.length := by simpa using hk
      have hidx : acc.length + (k' + 1) = (acc ++ [evalGateStep x acc g]).length + k' := by
        simp; omega
      rw [hidx]
      exact ih (acc ++ [evalGateStep x acc g]) k' hk'

/-- Appending gates preserves earlier entries of `evalGatesList`. -/
theorem evalGatesList_append_getD {n : ℕ} (x : Fin n → ℝ) (gs₁ gs₂ : List ArithGate)
    {k : ℕ} (hk : k < gs₁.length) :
    (evalGatesList x (gs₁ ++ gs₂)).getD k 0 = (evalGatesList x gs₁).getD k 0 := by
  unfold evalGatesList
  rw [List.foldl_append]
  have hlen : k < (gs₁.foldl (fun acc g ↦ acc ++ [evalGateStep x acc g]) []).length := by
    change k < (evalGatesList x gs₁).length
    rwa [evalGatesList_length]
  exact foldl_append_prefix 0 (evalGateStep x) gs₂ _ k hlen

/-- Reading the last entry of `evalGatesList x (gs ++ [g])` recovers `evalGateStep`. -/
theorem evalGatesList_snoc_last {n : ℕ} (x : Fin n → ℝ) (gs : List ArithGate) (g : ArithGate) :
    (evalGatesList x (gs ++ [g])).getD gs.length 0 =
      evalGateStep x (evalGatesList x gs) g := by
  rw [evalGatesList_append_singleton]
  have hlen : (evalGatesList x gs).length = gs.length := evalGatesList_length x gs
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

/-- Evaluating a well-formed gate list on `Fin N → ℝ` agrees with its restriction to
`Fin N₀ → ℝ`. -/
theorem evalGatesList_restrict_eq {N₀ N : ℕ} (hle : N₀ ≤ N) (y : Fin N → ℝ)
    (gs : List ArithGate) (hwf : ∀ k (hk : k < gs.length), gs[k].WellFormed N₀ k) :
    evalGatesList y gs = evalGatesList (fun i : Fin N₀ ↦ y ⟨i.1, i.2.trans_le hle⟩) gs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have hwf_gs : ∀ k (hk : k < gs.length), gs[k].WellFormed N₀ k := fun k hk ↦ by
      have h := hwf k (by simp; omega)
      rwa [List.getElem_append_left hk] at h
    have hwf_g : g.WellFormed N₀ gs.length := by
      have h := hwf gs.length (by simp)
      simpa using h
    rw [evalGatesList_append_singleton, evalGatesList_append_singleton, ih hwf_gs]
    congr 2
    cases g with
    | input idx =>
      have hlt : idx < N₀ := hwf_g
      have hlt' : idx < N := hlt.trans_le hle
      simp [hlt, hlt']
    | const c => rfl
    | add l r => rfl
    | mul l r => rfl
    | neg a => rfl

/-- Value computed by gate `k` of an arithmetic circuit `C` on real input `x`. -/
@[expose] def ArithCircuit.evalGate (C : ArithCircuit) (x : Fin C.numInputs → ℝ)
    (k : Fin C.gates.length) : ℝ :=
  (evalGatesList x C.gates).getD k.1 0

/-- Formula for `ArithCircuit.evalGate` in terms of `evalGatesList`. -/
theorem ArithCircuit.evalGate_eq (C : ArithCircuit) (x : Fin C.numInputs → ℝ)
    (k : Fin C.gates.length) : C.evalGate x k = (evalGatesList x C.gates).getD k.1 0 := rfl

/-- Output value `p_C(x)` computed at the designated output gate of `C`. -/
@[expose] def ArithCircuit.eval (C : ArithCircuit) (x : Fin C.numInputs → ℝ) : ℝ :=
  C.evalGate x ⟨C.output, C.output_lt⟩

/-- Formula for `ArithCircuit.eval` in terms of `evalGate`. -/
theorem ArithCircuit.eval_eq (C : ArithCircuit) (x : Fin C.numInputs → ℝ) :
    C.eval x = C.evalGate x ⟨C.output, C.output_lt⟩ := rfl

/-- Satisfiability of an arithmetic circuit: `∃ x ∈ ℝ^n, p_C(x) = 0`. -/
@[expose] def ArithCircuit.Satisfiable (C : ArithCircuit) : Prop :=
  ∃ x : Fin C.numInputs → ℝ, C.eval x = 0

/-- Gate-equality constraint system `GateEq(C)` : one polynomial equality per gate. -/
@[expose] def ArithCircuit.GateEq (C : ArithCircuit) (x : Fin C.numInputs → ℝ)
    (z : Fin C.gates.length → ℝ) : Prop :=
  ∀ (k : Fin C.gates.length),
    match h : C.gates[k.1] with
    | .input idx =>
        ∃ hidx : idx < C.numInputs, z k = x ⟨idx, hidx⟩
    | .const c => z k = (c : ℝ)
    | .add l r =>
        ∃ (hl : l < C.gates.length) (hr : r < C.gates.length),
          z k = z ⟨l, hl⟩ + z ⟨r, hr⟩
    | .mul l r =>
        ∃ (hl : l < C.gates.length) (hr : r < C.gates.length),
          z k = z ⟨l, hl⟩ * z ⟨r, hr⟩
    | .neg a =>
        ∃ (ha : a < C.gates.length), z k = -z ⟨a, ha⟩

/-- The canonical topological evaluation `z_g = C.evalGate x g` satisfies `GateEq(C)`. -/
theorem ArithCircuit.gateEq_evalGate (C : ArithCircuit) (x : Fin C.numInputs → ℝ) :
    C.GateEq x (C.evalGate x) := by
  intro k
  have hwf := C.gates_wf k.1 k.2
  have hget : C.evalGate x k =
      evalGateStep x ((C.gates.take k.1).foldl (fun a g ↦ a ++ [evalGateStep x a g]) [])
        C.gates[k.1] := by
    simpa [ArithCircuit.evalGate, evalGatesList] using
      foldl_append_getD_eq x C.gates [] k.1 k.2
  have hpref : ∀ j (hj : j < k.1),
      ((C.gates.take k.1).foldl (fun a g ↦ a ++ [evalGateStep x a g]) []).getD j 0 =
        C.evalGate x ⟨j, hj.trans k.2⟩ := by
    intro j hj
    have htake : C.gates = C.gates.take k.1 ++ C.gates.drop k.1 := (List.take_append_drop _ _).symm
    have hlen : j < ((C.gates.take k.1).foldl (fun a g ↦ a ++ [evalGateStep x a g]) []).length := by
      have : ((C.gates.take k.1).foldl (fun a g ↦ a ++ [evalGateStep x a g]) []).length =
          (C.gates.take k.1).length := by
        simpa [evalGatesList] using evalGatesList_length x (C.gates.take k.1)
      rw [this, List.length_take]
      omega
    have h1 := foldl_append_prefix 0 (evalGateStep x) (C.gates.drop k.1)
      ((C.gates.take k.1).foldl (fun a g ↦ a ++ [evalGateStep x a g]) []) j hlen
    rw [← h1]
    simp only [ArithCircuit.evalGate, evalGatesList]
    rw [← List.foldl_append, List.take_append_drop]
  generalize hgate : C.gates[k.1] = g at hwf hget ⊢
  cases g with
  | input idx =>
    simp only [ArithGate.WellFormed] at hwf
    refine ⟨hwf, ?_⟩
    rw [hget]
    simp [evalGateStep, hwf]
  | const c =>
    rw [hget]
    simp [evalGateStep]
  | add l r =>
    simp only [ArithGate.WellFormed] at hwf
    refine ⟨hwf.1.trans k.2, hwf.2.trans k.2, ?_⟩
    rw [hget, evalGateStep, hpref l hwf.1, hpref r hwf.2]
  | mul l r =>
    simp only [ArithGate.WellFormed] at hwf
    refine ⟨hwf.1.trans k.2, hwf.2.trans k.2, ?_⟩
    rw [hget, evalGateStep, hpref l hwf.1, hpref r hwf.2]
  | neg a =>
    simp only [ArithGate.WellFormed] at hwf
    refine ⟨hwf.trans k.2, ?_⟩
    rw [hget, evalGateStep, hpref a hwf]

/-- Any assignment `z` satisfying `GateEq(C)` coincides with `C.evalGate x` at every gate. -/
theorem ArithCircuit.eq_evalGate_of_gateEq (C : ArithCircuit) {x : Fin C.numInputs → ℝ}
    {z : Fin C.gates.length → ℝ} (hz : C.GateEq x z) :
    ∀ k : Fin C.gates.length, z k = C.evalGate x k := by
  have heval := C.gateEq_evalGate x
  have hstrong : ∀ (m : ℕ) (hm : m < C.gates.length), z ⟨m, hm⟩ = C.evalGate x ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm
      have hzk := hz ⟨m, hm⟩
      have hek := heval ⟨m, hm⟩
      have hwf := C.gates_wf m hm
      generalize hgate : C.gates[m] = g at hzk hek hwf
      cases g with
      | input idx =>
        obtain ⟨h1, hz1⟩ := hzk
        obtain ⟨h2, he2⟩ := hek
        rw [hz1, he2]
      | const c =>
        rw [hzk, hek]
      | add l r =>
        obtain ⟨hl1, hr1, hz1⟩ := hzk
        obtain ⟨hl2, hr2, he2⟩ := hek
        simp only [ArithGate.WellFormed] at hwf
        rw [hz1, he2, ih l hwf.1 hl1, ih r hwf.2 hr1]
      | mul l r =>
        obtain ⟨hl1, hr1, hz1⟩ := hzk
        obtain ⟨hl2, hr2, he2⟩ := hek
        simp only [ArithGate.WellFormed] at hwf
        rw [hz1, he2, ih l hwf.1 hl1, ih r hwf.2 hr1]
      | neg a =>
        obtain ⟨ha1, hz1⟩ := hzk
        obtain ⟨ha2, he2⟩ := hek
        simp only [ArithGate.WellFormed] at hwf
        rw [hz1, he2, ih a hwf ha1]
  intro k
  exact hstrong k.1 k.2

/-- and
an arithmetic circuit evaluates to `0` at
`x` if and only if there exists a gate assignment `z` satisfying `GateEq(C)` and `z_{g_out} = 0`. -/
theorem circuit_constraints_exact (C : ArithCircuit) (x : Fin C.numInputs → ℝ) :
    C.eval x = 0 ↔ ∃ z : Fin C.gates.length → ℝ, C.GateEq x z ∧ z ⟨C.output, C.output_lt⟩ = 0 := by
  constructor
  · intro h
    exact ⟨C.evalGate x, C.gateEq_evalGate x, h⟩
  · rintro ⟨z, hz, hout⟩
    rw [ArithCircuit.eval, ← C.eq_evalGate_of_gateEq hz ⟨C.output, C.output_lt⟩, hout]

/-- . -/
theorem circuit_semantics_equiv (C : ArithCircuit) (x : Fin C.numInputs → ℝ) :
    C.eval x = 0 ↔ ∃ z : Fin C.gates.length → ℝ, C.GateEq x z ∧ z ⟨C.output, C.output_lt⟩ = 0 :=
  circuit_constraints_exact C x

end Cslib.Complexity
