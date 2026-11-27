/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.RankPrimitives
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Embedding and Arithmetic-Circuit Compilation into `ARM(3)`

Global embedding of disjoint-support canonical-gauge gadgets and the explicit linear-size
compiler `compileCircuit` mapping arithmetic circuits over `ℝ` to `ARM(3)` instances,
with soundness, completeness, and exact equivalence.
-/

public section

namespace Cslib.Complexity

open Matrix Turing.MultiTapeTM

/-! ### Disjoint-Support Gadgets and Global Embedding () -/

/-- A local gadget specification on `m × n` matrices sharing a fixed `3 × 3` gauge block
`(I₀, J₀)` . -/
structure GadgetSpec (m n : ℕ) (I₀ : Fin 3 ↪ Fin m) (J₀ : Fin 3 ↪ Fin n) where
 /-- Active row support `ℛ_t` (including the gauge rows `I₀`). -/
  rowSupport : Set (Fin m)
 /-- Active column support `𝒞_t` (including the gauge columns `J₀`). -/
  colSupport : Set (Fin n)
 /-- The gadget's affine constraints `(A, b)`. -/
  constraints : List (Matrix (Fin m) (Fin n) ℚ × ℚ)
 /-- Every constraint matrix is supported inside `rowSupport × colSupport`. -/
  support_ok : ∀ p ∈ constraints, ∀ i j, p.1 i j ≠ 0 → i ∈ rowSupport ∧ j ∈ colSupport

/-- any family of gadgets with
pairwise disjoint non-gauge row supports and pairwise disjoint non-gauge column supports that
admits local canonical-gauge factors `(U^(t), V^(t))` embeds into a single global canonical-gauge
rank-3 matrix `X = U * V` satisfying every gadget's affine constraints simultaneously and
agreeing with each local matrix `U^(t) * V^(t)` on its support. -/
theorem global_embedding {m n : ℕ} {ι : Type*}
    {I₀ : Fin 3 ↪ Fin m} {J₀ : Fin 3 ↪ Fin n} {B : Matrix (Fin 3) (Fin 3) ℝ}
    (G : ι → GadgetSpec m n I₀ J₀)
    (hdisj_rows : ∀ s t, s ≠ t →
      Disjoint ((G s).rowSupport \ Set.range I₀) ((G t).rowSupport \ Set.range I₀))
    (hdisj_cols : ∀ s t, s ≠ t →
      Disjoint ((G s).colSupport \ Set.range J₀) ((G t).colSupport \ Set.range J₀))
    (U_loc : ι → Matrix (Fin m) (Fin 3) ℝ) (V_loc : ι → Matrix (Fin 3) (Fin n) ℝ)
    (hgaugeU : ∀ t, (U_loc t).submatrix I₀ id = 1)
    (hgaugeV : ∀ t, (V_loc t).submatrix id J₀ = B)
    (hsat : ∀ t, (ARMInstance.ofMatrices (G t).constraints).Satisfies (U_loc t * V_loc t)) :
    ∃ (U : Matrix (Fin m) (Fin 3) ℝ) (V : Matrix (Fin 3) (Fin n) ℝ),
      U.submatrix I₀ id = 1 ∧
      V.submatrix id J₀ = B ∧
      (∀ t i j, i ∈ (G t).rowSupport → j ∈ (G t).colSupport →
        (U * V) i j = (U_loc t * V_loc t) i j) ∧
      (∀ t, (ARMInstance.ofMatrices (G t).constraints).Satisfies (U * V)) := by
  classical
  let U : Matrix (Fin m) (Fin 3) ℝ := Matrix.of fun i k ↦
    if hI : ∃ r : Fin 3, I₀ r = i then (if hI.choose = k then 1 else 0)
    else if hR : ∃ t : ι, i ∈ (G t).rowSupport then U_loc hR.choose i k
    else 0
  let V : Matrix (Fin 3) (Fin n) ℝ := Matrix.of fun k j ↦
    if hJ : ∃ c : Fin 3, J₀ c = j then B k hJ.choose
    else if hC : ∃ t : ι, j ∈ (G t).colSupport then V_loc hC.choose k j
    else 0
  have hU_I₀ : U.submatrix I₀ id = 1 := by
    ext r k
    have hex : ∃ s : Fin 3, I₀ s = I₀ r := ⟨r, rfl⟩
    have hch : hex.choose = r := I₀.injective hex.choose_spec
    simp only [Matrix.submatrix_apply, id_eq, U, Matrix.of_apply, hex, ↓reduceDIte, hch,
      Matrix.one_apply]
  have hV_J₀ : V.submatrix id J₀ = B := by
    ext k c
    have hex : ∃ s : Fin 3, J₀ s = J₀ c := ⟨c, rfl⟩
    have hch : hex.choose = c := J₀.injective hex.choose_spec
    simp only [Matrix.submatrix_apply, id_eq, V, Matrix.of_apply, hex, ↓reduceDIte, hch]
  have hU_agree : ∀ t i k, i ∈ (G t).rowSupport → U i k = U_loc t i k := by
    intro t i k hi
    by_cases hI : ∃ r : Fin 3, I₀ r = i
    · obtain ⟨r, rfl⟩ := hI
      have h1 := congrFun (congrFun hU_I₀ r) k
      have h2 := congrFun (congrFun (hgaugeU t) r) k
      exact h1.trans h2.symm
    · have hR : ∃ s : ι, i ∈ (G s).rowSupport := ⟨t, hi⟩
      simp only [U, Matrix.of_apply, hI, ↓reduceDIte, hR]
      have heq : hR.choose = t := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj_rows _ _ hne) ⟨hR.choose_spec, hI⟩ ⟨hi, hI⟩
      rw [heq]
  have hV_agree : ∀ t k j, j ∈ (G t).colSupport → V k j = V_loc t k j := by
    intro t k j hj
    by_cases hJ : ∃ c : Fin 3, J₀ c = j
    · obtain ⟨c, rfl⟩ := hJ
      have h1 := congrFun (congrFun hV_J₀ k) c
      have h2 := congrFun (congrFun (hgaugeV t) k) c
      exact h1.trans h2.symm
    · have hC : ∃ s : ι, j ∈ (G s).colSupport := ⟨t, hj⟩
      simp only [V, Matrix.of_apply, hJ, ↓reduceDIte, hC]
      have heq : hC.choose = t := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj_cols _ _ hne) ⟨hC.choose_spec, hJ⟩ ⟨hj, hJ⟩
      rw [heq]
  have hXY : ∀ t i j, i ∈ (G t).rowSupport → j ∈ (G t).colSupport →
      (U * V) i j = (U_loc t * V_loc t) i j := by
    intro t i j hi hj
    simp only [Matrix.mul_apply, hU_agree t i _ hi, hV_agree t _ j hj]
  refine ⟨U, V, hU_I₀, hV_J₀, hXY, fun t ↦ ?_⟩
  rw [ARMInstance.satisfies_ofMatrices_iff]
  intro p hp
  have hsat_t := (ARMInstance.satisfies_ofMatrices_iff _ _).mp (hsat t) p hp
  rw [← hsat_t]
  simp only [frobeniusInner_eq_sum, Matrix.map_apply]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases h0 : p.1 i j = 0
  · simp [h0]
  · obtain ⟨hi, hj⟩ := (G t).support_ok p hp i j h0
    rw [hXY t i j hi hj]

/-! ### Explicit Circuit-to-`ARM(3)` Compilation (`compileCircuit`) -/

/-- Total matrix dimension `d = 3 + N + 3 * S` allocated by `compileCircuit`. -/
@[expose] def circuitDim (numInputs numGates : ℕ) : ℕ :=
  3 + numInputs + 3 * numGates

/-- Primary carrier index `(3 + i, 3 + i)` for circuit input variable `x_i`. -/
@[expose] def inputCarrierIdx (numInputs numGates i : ℕ) (hi : i < numInputs) :
    Fin (circuitDim numInputs numGates) :=
  ⟨3 + i, by unfold circuitDim; omega⟩

/-- Primary carrier index `(3 + N + k, 3 + N + k)` for gate `k`. -/
@[expose] def gateCarrierIdx (numInputs numGates k : ℕ) (hk : k < numGates) :
    Fin (circuitDim numInputs numGates) :=
  ⟨3 + numInputs + k, by unfold circuitDim; omega⟩

/-- First auxiliary row/column index `3 + N + S + 2 * k` for gate `k`'s multiplication gadget. -/
@[expose] def mulAuxIdx1 (numInputs numGates k : ℕ) (hk : k < numGates) :
    Fin (circuitDim numInputs numGates) :=
  ⟨3 + numInputs + numGates + 2 * k, by unfold circuitDim; omega⟩

/-- Second auxiliary row/column index `3 + N + S + 2 * k + 1` for gate `k`'s gadget. -/
@[expose] def mulAuxIdx2 (numInputs numGates k : ℕ) (hk : k < numGates) :
    Fin (circuitDim numInputs numGates) :=
  ⟨3 + numInputs + numGates + 2 * k + 1, by unfold circuitDim; omega⟩

/-- Build an `m × n` rational row-list with `val` at `(r, c)` and `0` elsewhere. -/
@[expose] def singleEntryRows (m n r c : ℕ) (val : ℚ) : List (List ℚ) :=
  (List.range m).map fun i ↦
    (List.range n).map fun j ↦
      if i = r ∧ j = c then val else 0

/-- Build an `m × n` rational row-list with `1` at `(r₁, c₁)`, `-1` at `(r₂, c₂)`, and `0`
elsewhere (assuming `(r₁, c₁) ≠ (r₂, c₂)`). -/
@[expose] def diffEntryRows (m n r₁ c₁ r₂ c₂ : ℕ) : List (List ℚ) :=
  (List.range m).map fun i ↦
    (List.range n).map fun j ↦
      (if i = r₁ ∧ j = c₁ then (1 : ℚ) else 0) -
      (if i = r₂ ∧ j = c₂ then (1 : ℚ) else 0)

/-- Build an `m × n` rational row-list encoding `X[r_z, c_z] - X[r_x, c_x] - X[r_y, c_y] = 0`. -/
@[expose] def addEntryRows (m n r_z c_z rₓ cₓ rᵧ cᵧ : ℕ) : List (List ℚ) :=
  (List.range m).map fun i ↦
    (List.range n).map fun j ↦
      (if i = r_z ∧ j = c_z then (1 : ℚ) else 0) -
      (if i = rₓ ∧ j = cₓ then (1 : ℚ) else 0) -
      (if i = rᵧ ∧ j = cᵧ then (1 : ℚ) else 0)

/-- Build an `m × n` rational row-list encoding `X[r_z, c_z] + X[r_x, c_x] = 0`. -/
@[expose] def negEntryRows (m n r_z c_z rₓ cₓ : ℕ) : List (List ℚ) :=
  (List.range m).map fun i ↦
    (List.range n).map fun j ↦
      (if i = r_z ∧ j = c_z then (1 : ℚ) else 0) +
      (if i = rₓ ∧ j = cₓ then (1 : ℚ) else 0)

/-- Row count of `singleEntryRows`. -/
theorem singleEntryRows_dims (m n r c : ℕ) (val : ℚ) :
    (singleEntryRows m n r c val).length = m ∧
    ∀ row ∈ singleEntryRows m n r c val, row.length = n := by
  refine ⟨by simp [singleEntryRows], fun row hrow ↦ ?_⟩
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Row count of `diffEntryRows`. -/
theorem diffEntryRows_dims (m n r₁ c₁ r₂ c₂ : ℕ) :
    (diffEntryRows m n r₁ c₁ r₂ c₂).length = m ∧
    ∀ row ∈ diffEntryRows m n r₁ c₁ r₂ c₂, row.length = n := by
  refine ⟨by simp [diffEntryRows], fun row hrow ↦ ?_⟩
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Row count of `addEntryRows`. -/
theorem addEntryRows_dims (m n r_z c_z rₓ cₓ rᵧ cᵧ : ℕ) :
    (addEntryRows m n r_z c_z rₓ cₓ rᵧ cᵧ).length = m ∧
    ∀ row ∈ addEntryRows m n r_z c_z rₓ cₓ rᵧ cᵧ, row.length = n := by
  refine ⟨by simp [addEntryRows], fun row hrow ↦ ?_⟩
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Row count of `negEntryRows`. -/
theorem negEntryRows_dims (m n r_z c_z rₓ cₓ : ℕ) :
    (negEntryRows m n r_z c_z rₓ cₓ).length = m ∧
    ∀ row ∈ negEntryRows m n r_z c_z rₓ cₓ, row.length = n := by
  refine ⟨by simp [negEntryRows], fun row hrow ↦ ?_⟩
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Frobenius inner product with `singleEntryRows` extracts `val * X r c`. -/
theorem frobeniusInner_singleEntryRows {m n : ℕ} (r : Fin m) (c : Fin n) (val : ℚ)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((Matrix.of fun (i : Fin m) (j : Fin n) ↦
      ((singleEntryRows m n r.1 c.1 val).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) X =
      (val : ℝ) * X r c := by
  have hmat : ((Matrix.of fun (i : Fin m) (j : Fin n) ↦
      ((singleEntryRows m n r.1 c.1 val).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) =
      (val : ℝ) • entryMatrixReal m n r c := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      singleEntryRows, entryMatrixReal_apply, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range, i.2, j.2, Option.map_some, Option.getD_some,
      Fin.ext_iff]
    split_ifs <;> simp
  rw [hmat, frobeniusInner_smul_left, frobeniusInner_entryMatrixReal]

/-- The 9 gauge-fixing affine constraints pinning `X[0..2, 0..2] = I₃`. -/
@[expose] def gaugeConstraints (d : ℕ) : List (List (List ℚ) × ℚ) :=
  [ (singleEntryRows d d 0 0 1, 1), (singleEntryRows d d 0 1 1, 0), (singleEntryRows d d 0 2 1, 0),
    (singleEntryRows d d 1 0 1, 0), (singleEntryRows d d 1 1 1, 1), (singleEntryRows d d 1 2 1, 0),
    (singleEntryRows d d 2 0 1, 0), (singleEntryRows d d 2 1 1, 0), (singleEntryRows d d 2 2 1, 1) ]

/-- The affine constraints emitted for gate `k` of an arithmetic circuit with `N` inputs and
`S` gates. -/
@[expose] def gateConstraints (N S k : ℕ) : ArithGate → List (List (List ℚ) × ℚ)
  | .input idx =>
      let d := circuitDim N S
      [(diffEntryRows d d (3 + N + k) (3 + N + k) (3 + idx) (3 + idx), 0)]
  | .const c =>
      let d := circuitDim N S
      [(singleEntryRows d d (3 + N + k) (3 + N + k) 1, c)]
  | .add l r =>
      let d := circuitDim N S
      [(addEntryRows d d (3 + N + k) (3 + N + k) (3 + N + l) (3 + N + l)
        (3 + N + r) (3 + N + r), 0)]
  | .neg a =>
      let d := circuitDim N S
      [(negEntryRows d d (3 + N + k) (3 + N + k) (3 + N + a) (3 + N + a), 0)]
  | .mul l r =>
      let d := circuitDim N S
      let r1 := 3 + N + S + 2 * k
      let r2 := 3 + N + S + 2 * k + 1
      [ (singleEntryRows d d r1 r1 1, 1),
        (singleEntryRows d d 0 r1 1, 0), (singleEntryRows d d 0 r2 1, 0),
        (singleEntryRows d d 1 r1 1, 0), (singleEntryRows d d 1 r2 1, 0),
        (singleEntryRows d d r1 0 1, 0), (singleEntryRows d d r1 1 1, 0),
        (singleEntryRows d d r2 0 1, 0), (singleEntryRows d d r2 1 1, 0),
        (diffEntryRows d d r1 r2 (3 + N + l) (3 + N + l), 0),
        (diffEntryRows d d r2 r1 (3 + N + r) (3 + N + r), 0),
        (diffEntryRows d d r2 r2 (3 + N + k) (3 + N + k), 0) ]

/-- All affine constraints produced by compiling `(numInputs, gates, output)`. -/
@[expose] def compileCircuitConstraints (numInputs : ℕ) (gates : List ArithGate) (output : ℕ) :
    List (List (List ℚ) × ℚ) :=
  let d := circuitDim numInputs gates.length
  gaugeConstraints d ++
    (gates.zipIdx.flatMap fun p ↦ gateConstraints numInputs gates.length p.2 p.1) ++
    [(singleEntryRows d d (3 + numInputs + output) (3 + numInputs + output) 1, 0)]

/-- Compile an arithmetic circuit `C` into an `ARM(3)` instance . -/
@[expose] def compileCircuit (C : ArithCircuit) : ARMInstance where
  rows := circuitDim C.numInputs C.gates.length
  cols := circuitDim C.numInputs C.gates.length
  constraints := compileCircuitConstraints C.numInputs C.gates C.output
  dims_ok := by
    intro c hc
    dsimp [compileCircuitConstraints] at hc
    simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hc
    rcases hc with (hc | ⟨⟨g, k⟩, _, hc⟩) | rfl
    · simp only [gaugeConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact singleEntryRows_dims _ _ _ _ _
    · cases g with
      | input idx =>
        simp only [gateConstraints, List.mem_singleton] at hc
        subst hc; exact diffEntryRows_dims _ _ _ _ _ _
      | const val =>
        simp only [gateConstraints, List.mem_singleton] at hc
        subst hc; exact singleEntryRows_dims _ _ _ _ _
      | add l r =>
        simp only [gateConstraints, List.mem_singleton] at hc
        subst hc; exact addEntryRows_dims _ _ _ _ _ _ _ _
      | neg a =>
        simp only [gateConstraints, List.mem_singleton] at hc
        subst hc; exact negEntryRows_dims _ _ _ _ _ _
      | mul l r =>
        simp only [gateConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact singleEntryRows_dims _ _ _ _ _
        · exact diffEntryRows_dims _ _ _ _ _ _
        · exact diffEntryRows_dims _ _ _ _ _ _
        · exact diffEntryRows_dims _ _ _ _ _ _
    · exact singleEntryRows_dims _ _ _ _ _

/-! ### Size and Bit-Complexity Bounds (, ) -/

/-- and `compileCircuit C` has matrix dimension `3 + numInputs + 3 * C.size` and at most
`10 + 12 * C.size` affine constraints (strictly linear in the circuit size). -/
theorem compileCircuit_size_le (C : ArithCircuit) :
    (compileCircuit C).rows = 3 + C.numInputs + 3 * C.size ∧
    (compileCircuit C).cols = 3 + C.numInputs + 3 * C.size ∧
    (compileCircuit C).constraints.length ≤ 10 + 12 * C.size := by
  refine ⟨rfl, rfl, ?_⟩
  rw [ArithCircuit.size_eq_length]
  dsimp [compileCircuit, compileCircuitConstraints]
  simp only [List.length_append, gaugeConstraints, List.length_cons, List.length_nil]
  have hflat : ∀ (gs : List (ArithGate × ℕ)),
      (gs.flatMap fun p ↦ gateConstraints C.numInputs C.gates.length p.2 p.1).length ≤
        12 * gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 : (gateConstraints C.numInputs C.gates.length p.2 p.1).length ≤ 12 := by
        cases p.1 <;> simp [gateConstraints]
      omega
  have hlen := hflat C.gates.zipIdx
  simp only [List.length_zipIdx] at hlen
  omega

private theorem mem_zipIdx_iff {α : Type*} (l : List α) (x : α) (k : ℕ) :
    (x, k) ∈ l.zipIdx ↔ ∃ h : k < l.length, l[k] = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, heq⟩
    simp only [List.length_zipIdx] at hi
    rw [List.getElem_zipIdx] at heq
    have hik : i = k := by simpa using congrArg Prod.snd heq
    subst hik
    exact ⟨hi, congrArg Prod.fst heq⟩
  · rintro ⟨hk, hx⟩
    refine ⟨k, by simpa using hk, ?_⟩
    rw [List.getElem_zipIdx]
    simp [hx]

/-- every constraint matrix produced by
`compileCircuit C` has small integer entries in `{-2, -1, 0, 1, 2}` (in fact `{-1, 0, 1}`
whenever addition gates have distinct operands), and every right-hand side scalar is either `0`,
`1`, or a constant directly copied from a constant gate of `C`. -/
theorem compileCircuit_coeff_bounds (C : ArithCircuit) :
    ∀ c ∈ (compileCircuit C).constraints,
      (∀ row ∈ c.1, ∀ q ∈ row, q ∈ ({-2, -1, 0, 1, 2} : Set ℚ)) ∧
      (c.2 = 0 ∨ c.2 = 1 ∨ ∃ val : ℚ, ArithGate.const val ∈ C.gates ∧ c.2 = val) := by
  have hsingle : ∀ m n r c (v : ℚ), v ∈ ({-2, -1, 0, 1, 2} : Set ℚ) →
      ∀ row ∈ singleEntryRows m n r c v, ∀ q ∈ row, q ∈ ({-2, -1, 0, 1, 2} : Set ℚ) := by
    intro m n r c v hv row hrow q hq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    split_ifs <;> simp [hv]
  have hdiff : ∀ m n r₁ c₁ r₂ c₂,
      ∀ row ∈ diffEntryRows m n r₁ c₁ r₂ c₂, ∀ q ∈ row, q ∈ ({-2, -1, 0, 1, 2} : Set ℚ) := by
    intro m n r₁ c₁ r₂ c₂ row hrow q hq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    split_ifs <;> norm_num
  have hadd : ∀ m n r_z c_z rₓ cₓ rᵧ cᵧ,
      ∀ row ∈ addEntryRows m n r_z c_z rₓ cₓ rᵧ cᵧ,
        ∀ q ∈ row, q ∈ ({-2, -1, 0, 1, 2} : Set ℚ) := by
    intro m n r_z c_z rₓ cₓ rᵧ cᵧ row hrow q hq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    split_ifs <;> norm_num
  have hneg : ∀ m n r_z c_z rₓ cₓ,
      ∀ row ∈ negEntryRows m n r_z c_z rₓ cₓ, ∀ q ∈ row, q ∈ ({-2, -1, 0, 1, 2} : Set ℚ) := by
    intro m n r_z c_z rₓ cₓ row hrow q hq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    split_ifs <;> norm_num
  intro c hc
  dsimp [compileCircuit, compileCircuitConstraints] at hc
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hc
  rcases hc with (hc | ⟨⟨g, k⟩, hmem, hc⟩) | rfl
  · simp only [gaugeConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨hsingle _ _ _ _ _ (by simp), by simp⟩
  · have hgmem : g ∈ C.gates := by
      obtain ⟨hk, rfl⟩ := (mem_zipIdx_iff C.gates g k).mp hmem
      exact List.getElem_mem hk
    cases g with
    | input idx =>
      simp only [gateConstraints, List.mem_singleton] at hc; subst hc
      exact ⟨hdiff _ _ _ _ _ _, Or.inl rfl⟩
    | const val =>
      simp only [gateConstraints, List.mem_singleton] at hc; subst hc
      exact ⟨hsingle _ _ _ _ _ (by simp), Or.inr (Or.inr ⟨val, hgmem, rfl⟩)⟩
    | add l r =>
      simp only [gateConstraints, List.mem_singleton] at hc; subst hc
      exact ⟨hadd _ _ _ _ _ _ _ _, Or.inl rfl⟩
    | neg a =>
      simp only [gateConstraints, List.mem_singleton] at hc; subst hc
      exact ⟨hneg _ _ _ _ _ _, Or.inl rfl⟩
    | mul l r =>
      simp only [gateConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inr (Or.inl rfl)⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩
      · exact ⟨hdiff _ _ _ _ _ _, Or.inl rfl⟩
      · exact ⟨hdiff _ _ _ _ _ _, Or.inl rfl⟩
      · exact ⟨hdiff _ _ _ _ _ _, Or.inl rfl⟩
  · exact ⟨hsingle _ _ _ _ _ (by simp), Or.inl rfl⟩

/-! ### Helper evaluation lemmas for compiled row-list constraints -/

private theorem eval_singleEntryRows {m n r c : ℕ} (hr : r < m) (hc : c < n)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((singleEntryRows m n r c 1).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) X =
      X ⟨r, hr⟩ ⟨c, hc⟩ := by
  have hmat : ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((singleEntryRows m n r c 1).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) =
      entryMatrixReal m n ⟨r, hr⟩ ⟨c, hc⟩ := by
    ext i j
    simp [singleEntryRows, List.getD_eq_getElem?_getD, Fin.ext_iff]
    split_ifs <;> simp
  rw [hmat, frobeniusInner_entryMatrixReal]

private theorem eval_diffEntryRows {m n r₁ c₁ r₂ c₂ : ℕ}
    (hr₁ : r₁ < m) (hc₁ : c₁ < n) (hr₂ : r₂ < m) (hc₂ : c₂ < n)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((diffEntryRows m n r₁ c₁ r₂ c₂).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) X =
      X ⟨r₁, hr₁⟩ ⟨c₁, hc₁⟩ - X ⟨r₂, hr₂⟩ ⟨c₂, hc₂⟩ := by
  have hmat : ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((diffEntryRows m n r₁ c₁ r₂ c₂).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) =
      entryMatrixReal m n ⟨r₁, hr₁⟩ ⟨c₁, hc₁⟩ - entryMatrixReal m n ⟨r₂, hr₂⟩ ⟨c₂, hc₂⟩ := by
    ext i j
    simp [diffEntryRows, List.getD_eq_getElem?_getD, Fin.ext_iff]
    split_ifs <;> simp
  rw [hmat, frobeniusInner_sub_left, frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal]

private theorem eval_addEntryRows {m n r_z c_z rₓ cₓ rᵧ cᵧ : ℕ}
    (hrz : r_z < m) (hcz : c_z < n) (hrx : rₓ < m) (hcx : cₓ < n)
    (hry : rᵧ < m) (hcy : cᵧ < n) (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((addEntryRows m n r_z c_z rₓ cₓ rᵧ cᵧ).getD i.1 []).getD j.1 0).map
        ((↑) : ℚ → ℝ)) X =
      X ⟨r_z, hrz⟩ ⟨c_z, hcz⟩ - X ⟨rₓ, hrx⟩ ⟨cₓ, hcx⟩ - X ⟨rᵧ, hry⟩ ⟨cᵧ, hcy⟩ := by
  have hmat : ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((addEntryRows m n r_z c_z rₓ cₓ rᵧ cᵧ).getD i.1 []).getD j.1 0).map
        ((↑) : ℚ → ℝ)) =
      entryMatrixReal m n ⟨r_z, hrz⟩ ⟨c_z, hcz⟩ - entryMatrixReal m n ⟨rₓ, hrx⟩ ⟨cₓ, hcx⟩ -
        entryMatrixReal m n ⟨rᵧ, hry⟩ ⟨cᵧ, hcy⟩ := by
    ext i j
    simp [addEntryRows, List.getD_eq_getElem?_getD, Fin.ext_iff]
    split_ifs <;> simp
  rw [hmat, frobeniusInner_sub_left, frobeniusInner_sub_left,
    frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal]

private theorem eval_negEntryRows {m n r_z c_z rₓ cₓ : ℕ}
    (hrz : r_z < m) (hcz : c_z < n) (hrx : rₓ < m) (hcx : cₓ < n)
    (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusInner ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((negEntryRows m n r_z c_z rₓ cₓ).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) X =
      X ⟨r_z, hrz⟩ ⟨c_z, hcz⟩ + X ⟨rₓ, hrx⟩ ⟨cₓ, hcx⟩ := by
  have hmat : ((Matrix.of fun i : Fin m ↦ fun j : Fin n ↦
      ((negEntryRows m n r_z c_z rₓ cₓ).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) =
      entryMatrixReal m n ⟨r_z, hrz⟩ ⟨c_z, hcz⟩ + entryMatrixReal m n ⟨rₓ, hrx⟩ ⟨cₓ, hcx⟩ := by
    ext i j
    simp [negEntryRows, List.getD_eq_getElem?_getD, Fin.ext_iff]
    split_ifs <;> simp
  rw [hmat, frobeniusInner_add_left, frobeniusInner_entryMatrixReal, frobeniusInner_entryMatrixReal]

/-! ### Forward Direction (Soundness: ) -/

/-- if the arithmetic circuit `C` is
satisfiable over `ℝ`, then `compileCircuit C` admits a feasible matrix `X` of rank at most `3`. -/
theorem compileCircuit_soundness (C : ArithCircuit) (hsat : C.Satisfiable) :
    (compileCircuit C).Feasible 3 := by
  set N := C.numInputs
  set S := C.gates.length
  set d := circuitDim N S
  obtain ⟨x, hx⟩ := hsat
  let z : Fin S → ℝ := C.evalGate x
  have hz : C.GateEq x z := C.gateEq_evalGate x
 -- Construct canonical-gauge global factors `(U, V)` directly with `U[0..2,:] = I₃`, `V[:,0..2] =
 -- I₃`.
  let U : Matrix (Fin d) (Fin 3) ℝ := Matrix.of fun i t ↦
    if _h0 : i.1 < 3 then (if i.1 = t.1 then 1 else 0)
    else if _h1 : i.1 < 3 + N then (if t.1 = 2 then x ⟨i.1 - 3, by omega⟩ else 0)
    else if _h2 : i.1 < 3 + N + S then (if t.1 = 2 then z ⟨i.1 - (3 + N), by omega⟩ else 0)
    else
      let off := i.1 - (3 + N + S)
      let k := off / 2
      if hk : k < S then
        if off % 2 = 0 then (if t.1 = 2 then 1 else 0)
        else
          match C.gates[k] with
          | .mul _ r =>
            if hr : r < S then (if t.1 = 2 then z ⟨r, hr⟩ else 0) else 0
          | _ => 0
      else 0
  let V : Matrix (Fin 3) (Fin d) ℝ := Matrix.of fun t j ↦
    if j.1 < 3 then (if t.1 = j.1 then 1 else 0)
    else if j.1 < 3 + N then (if t.1 = 2 then 1 else 0)
    else if j.1 < 3 + N + S then (if t.1 = 2 then 1 else 0)
    else
      let off := j.1 - (3 + N + S)
      let k := off / 2
      if hk : k < S then
        if off % 2 = 0 then (if t.1 = 2 then 1 else 0)
        else
          match C.gates[k] with
          | .mul l _ =>
            if hl : l < S then (if t.1 = 2 then z ⟨l, hl⟩ else 0) else 0
          | _ => 0
      else 0
  let X : Matrix (Fin d) (Fin d) ℝ := U * V
  have hX_entry : ∀ i j : Fin d, X i j = U i 0 * V 0 j + U i 1 * V 1 j + U i 2 * V 2 j := by
    intro i j
    simp [X, Matrix.mul_apply, Fin.sum_univ_three]
  have hX_gauge : ∀ (a b : Fin 3),
      X ⟨a.1, by dsimp [d, circuitDim]; omega⟩ ⟨b.1, by dsimp [d, circuitDim]; omega⟩ =
        if a.1 = b.1 then 1 else 0 := by
    intro a b
    rw [hX_entry]
    fin_cases a <;> fin_cases b <;> simp [U, V]
  have hX_inp : ∀ i (hi : i < N),
      X ⟨3 + i, by dsimp [d, circuitDim]; omega⟩ ⟨3 + i, by dsimp [d, circuitDim]; omega⟩ =
        x ⟨i, hi⟩ := by
    intro i hi
    rw [hX_entry]
    have h1 : ¬ (3 + i < 3) := by omega
    have h2 : 3 + i < 3 + N := by omega
    simp [U, V, h1, h2]
  have hX_gate : ∀ k (hk : k < S),
      X ⟨3 + N + k, by dsimp [d, circuitDim]; omega⟩ ⟨3 + N + k, by dsimp [d, circuitDim]; omega⟩ =
        z ⟨k, hk⟩ := by
    intro k hk
    rw [hX_entry]
    have h1 : ¬ (3 + N + k < 3) := by omega
    have h2 : ¬ (3 + N + k < 3 + N) := by omega
    have h3 : 3 + N + k < 3 + N + S := by omega
    simp [U, V, h1, h2, h3]
  have hsingle : ∀ (r c : ℕ) (hr : r < d) (hc : c < d) (val : ℚ),
      X ⟨r, hr⟩ ⟨c, hc⟩ = (val : ℝ) →
      frobeniusInner (((compileCircuit C).matrixAt (singleEntryRows d d r c 1, val)).map
        ((↑) : ℚ → ℝ)) X = (val : ℝ) := fun r c hr hc val h ↦
    (eval_singleEntryRows hr hc X).trans h
  have hdiff : ∀ (r₁ c₁ r₂ c₂ : ℕ) (hr₁ : r₁ < d) (hc₁ : c₁ < d) (hr₂ : r₂ < d) (hc₂ : c₂ < d),
      X ⟨r₁, hr₁⟩ ⟨c₁, hc₁⟩ = X ⟨r₂, hr₂⟩ ⟨c₂, hc₂⟩ →
      frobeniusInner (((compileCircuit C).matrixAt (diffEntryRows d d r₁ c₁ r₂ c₂, 0)).map
        ((↑) : ℚ → ℝ)) X = ((0 : ℚ) : ℝ) := fun r₁ c₁ r₂ c₂ hr₁ hc₁ hr₂ hc₂ h ↦
    (eval_diffEntryRows hr₁ hc₁ hr₂ hc₂ X).trans (by rw [h, sub_self, Rat.cast_zero])
  have hadd : ∀ (r_z c_z rₓ cₓ rᵧ cᵧ : ℕ) (hrz : r_z < d) (hcz : c_z < d)
      (hrx : rₓ < d) (hcx : cₓ < d) (hry : rᵧ < d) (hcy : cᵧ < d),
      X ⟨r_z, hrz⟩ ⟨c_z, hcz⟩ = X ⟨rₓ, hrx⟩ ⟨cₓ, hcx⟩ + X ⟨rᵧ, hry⟩ ⟨cᵧ, hcy⟩ →
      frobeniusInner (((compileCircuit C).matrixAt
        (addEntryRows d d r_z c_z rₓ cₓ rᵧ cᵧ, 0)).map ((↑) : ℚ → ℝ)) X = ((0 : ℚ) : ℝ) :=
    fun r_z c_z rₓ cₓ rᵧ cᵧ hrz hcz hrx hcx hry hcy h ↦
      (eval_addEntryRows hrz hcz hrx hcx hry hcy X).trans (by rw [h, Rat.cast_zero]; ring)
  have hneg : ∀ (r_z c_z rₓ cₓ : ℕ) (hrz : r_z < d) (hcz : c_z < d) (hrx : rₓ < d) (hcx : cₓ < d),
      X ⟨r_z, hrz⟩ ⟨c_z, hcz⟩ = -X ⟨rₓ, hrx⟩ ⟨cₓ, hcx⟩ →
      frobeniusInner (((compileCircuit C).matrixAt (negEntryRows d d r_z c_z rₓ cₓ, 0)).map
        ((↑) : ℚ → ℝ)) X = ((0 : ℚ) : ℝ) := fun r_z c_z rₓ cₓ hrz hcz hrx hcx h ↦
    (eval_negEntryRows hrz hcz hrx hcx X).trans (by rw [h, Rat.cast_zero]; ring)
  refine ⟨X, ?_, (rank_factorization_equiv X 3).mpr ⟨U, V, rfl⟩⟩
  intro c hc
  dsimp [compileCircuit, compileCircuitConstraints] at hc
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hc
  rcases hc with (hc | ⟨⟨g, k⟩, hmem, hc⟩) | rfl
  · simp only [gaugeConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsingle 0 0 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 1
        (by simpa using hX_gauge 0 0)
    · exact hsingle 0 1 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 0
        (by simpa using hX_gauge 0 1)
    · exact hsingle 0 2 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 0
        (by simpa using hX_gauge 0 2)
    · exact hsingle 1 0 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 0
        (by simpa using hX_gauge 1 0)
    · exact hsingle 1 1 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 1
        (by simpa using hX_gauge 1 1)
    · exact hsingle 1 2 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 0
        (by simpa using hX_gauge 1 2)
    · exact hsingle 2 0 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 0
        (by simpa using hX_gauge 2 0)
    · exact hsingle 2 1 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 0
        (by simpa using hX_gauge 2 1)
    · exact hsingle 2 2 (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) 1
        (by simpa using hX_gauge 2 2)
  · obtain ⟨hk, hgk⟩ := (mem_zipIdx_iff C.gates g k).mp hmem
    change k < S at hk
    have hzk := hz ⟨k, hk⟩
    rw [hgk] at hzk
    cases g with
    | input idx =>
      simp only [gateConstraints, List.mem_singleton] at hc
      subst hc
      obtain ⟨hidx, hzeq⟩ := hzk
      exact hdiff (3 + N + k) (3 + N + k) (3 + idx) (3 + idx)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by rw [hX_gate k hk, hX_inp idx hidx, hzeq])
    | const val =>
      simp only [gateConstraints, List.mem_singleton] at hc
      subst hc
      exact hsingle (3 + N + k) (3 + N + k)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega) val
        (by rw [hX_gate k hk, hzk])
    | add l r =>
      simp only [gateConstraints, List.mem_singleton] at hc
      subst hc
      obtain ⟨hl, hr, hzeq⟩ := hzk
      exact hadd (3 + N + k) (3 + N + k) (3 + N + l) (3 + N + l) (3 + N + r) (3 + N + r)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by rw [hX_gate k hk, hX_gate l hl, hX_gate r hr, hzeq])
    | neg a =>
      simp only [gateConstraints, List.mem_singleton] at hc
      subst hc
      obtain ⟨ha, hzeq⟩ := hzk
      exact hneg (3 + N + k) (3 + N + k) (3 + N + a) (3 + N + a)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
        (by rw [hX_gate k hk, hX_gate a ha, hzeq])
    | mul l r =>
      obtain ⟨hl, hr, hzeq⟩ := hzk
      have hr1_lt : 3 + N + S + 2 * k < d := by dsimp [d, circuitDim]; omega
      have hr2_lt : 3 + N + S + 2 * k + 1 < d := by dsimp [d, circuitDim]; omega
      have hUr1 : ∀ t : Fin 3, U ⟨3 + N + S + 2 * k, hr1_lt⟩ t = if t.1 = 2 then 1 else 0 := by
        intro t
        have h1 : ¬ (3 + N + S + 2 * k < 3) := by omega
        have h2 : ¬ (3 + N + S + 2 * k < 3 + N) := by omega
        have h3 : ¬ (3 + N + S + 2 * k < 3 + N + S) := by omega
        simp [U, h1, h2, h3, hk]
      have hUr2 : ∀ t : Fin 3,
          U ⟨3 + N + S + 2 * k + 1, hr2_lt⟩ t = if t.1 = 2 then z ⟨r, hr⟩ else 0 := by
        intro t
        have h1 : ¬ (3 + N + S + 2 * k + 1 < 3) := by omega
        have h2 : ¬ (3 + N + S + 2 * k + 1 < 3 + N) := by omega
        have h3 : ¬ (3 + N + S + 2 * k + 1 < 3 + N + S) := by omega
        have hoff : 3 + N + S + 2 * k + 1 - (3 + N + S) = 2 * k + 1 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        have hmod : (2 * k + 1) % 2 = 1 := by omega
        simp only [U, Matrix.of_apply, h1, h2, h3, ↓reduceDIte]
        rw [hoff, hdiv, hmod]
        simp only [hk, ↓reduceDIte, hgk]
        simp [show r < S from hr]
      have hVc1 : ∀ t : Fin 3, V t ⟨3 + N + S + 2 * k, hr1_lt⟩ = if t.1 = 2 then 1 else 0 := by
        intro t
        have h1 : ¬ (3 + N + S + 2 * k < 3) := by omega
        have h2 : ¬ (3 + N + S + 2 * k < 3 + N) := by omega
        have h3 : ¬ (3 + N + S + 2 * k < 3 + N + S) := by omega
        simp [V, h1, h2, h3, hk]
      have hVc2 : ∀ t : Fin 3,
          V t ⟨3 + N + S + 2 * k + 1, hr2_lt⟩ = if t.1 = 2 then z ⟨l, hl⟩ else 0 := by
        intro t
        have h1 : ¬ (3 + N + S + 2 * k + 1 < 3) := by omega
        have h2 : ¬ (3 + N + S + 2 * k + 1 < 3 + N) := by omega
        have h3 : ¬ (3 + N + S + 2 * k + 1 < 3 + N + S) := by omega
        have hoff : 3 + N + S + 2 * k + 1 - (3 + N + S) = 2 * k + 1 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        have hmod : (2 * k + 1) % 2 = 1 := by omega
        simp only [V, Matrix.of_apply, h1, h2, h3, ↓reduceIte]
        rw [hoff, hdiv, hmod]
        simp only [hk, ↓reduceDIte, hgk]
        simp [show l < S from hl]
      simp only [gateConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsingle _ _ hr1_lt hr1_lt 1 (by
          rw [hX_entry, hUr1, hUr1, hUr1, hVc1, hVc1, hVc1]; norm_num)
      · exact hsingle 0 _ (by dsimp [d, circuitDim]; omega) hr1_lt 0 (by
          rw [hX_entry, hVc1, hVc1, hVc1]; simp [U])
      · exact hsingle 0 _ (by dsimp [d, circuitDim]; omega) hr2_lt 0 (by
          rw [hX_entry, hVc2, hVc2, hVc2]; simp [U])
      · exact hsingle 1 _ (by dsimp [d, circuitDim]; omega) hr1_lt 0 (by
          rw [hX_entry, hVc1, hVc1, hVc1]; simp [U])
      · exact hsingle 1 _ (by dsimp [d, circuitDim]; omega) hr2_lt 0 (by
          rw [hX_entry, hVc2, hVc2, hVc2]; simp [U])
      · exact hsingle _ 0 hr1_lt (by dsimp [d, circuitDim]; omega) 0 (by
          rw [hX_entry, hUr1, hUr1, hUr1]; simp [V])
      · exact hsingle _ 1 hr1_lt (by dsimp [d, circuitDim]; omega) 0 (by
          rw [hX_entry, hUr1, hUr1, hUr1]; simp [V])
      · exact hsingle _ 0 hr2_lt (by dsimp [d, circuitDim]; omega) 0 (by
          rw [hX_entry, hUr2, hUr2, hUr2]; simp [V])
      · exact hsingle _ 1 hr2_lt (by dsimp [d, circuitDim]; omega) 0 (by
          rw [hX_entry, hUr2, hUr2, hUr2]; simp [V])
      · exact hdiff _ _ (3 + N + l) (3 + N + l) hr1_lt hr2_lt
          (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
          (by rw [hX_gate l hl, hX_entry, hUr1, hUr1, hUr1, hVc2, hVc2, hVc2]; norm_num)
      · exact hdiff _ _ (3 + N + r) (3 + N + r) hr2_lt hr1_lt
          (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
          (by rw [hX_gate r hr, hX_entry, hUr2, hUr2, hUr2, hVc1, hVc1, hVc1]; norm_num)
      · exact hdiff _ _ (3 + N + k) (3 + N + k) hr2_lt hr2_lt
          (by dsimp [d, circuitDim]; omega) (by dsimp [d, circuitDim]; omega)
          (by rw [hX_gate k hk, hX_entry, hUr2, hUr2, hUr2, hVc2, hVc2, hVc2, hzeq]; norm_num; ring)
  · have hout_lt : 3 + N + C.output < d := by
      have := C.output_lt; dsimp [d, N, S, circuitDim]; omega
    exact hsingle (3 + N + C.output) (3 + N + C.output) hout_lt hout_lt 0 (by
      rw [hX_gate C.output C.output_lt, Rat.cast_zero]; exact hx)

/-! ### Converse Direction (Completeness: ) -/

/-- if `compileCircuit C` admits a
feasible matrix `X` of rank at most `3`, then the decoded carrier values satisfy `C`, hence
`C.Satisfiable`. -/
theorem compileCircuit_completeness (C : ArithCircuit) (hfeas : (compileCircuit C).Feasible 3) :
    C.Satisfiable := by
  obtain ⟨X, hsat, hrank⟩ := hfeas
  set N := C.numInputs
  set S := C.gates.length
  set d := circuitDim N S
  let x : Fin N → ℝ := fun i ↦ X (inputCarrierIdx N S i.1 i.2) (inputCarrierIdx N S i.1 i.2)
  let z : Fin S → ℝ := fun k ↦ X (gateCarrierIdx N S k.1 k.2) (gateCarrierIdx N S k.1 k.2)
  have hmem_gauge : ∀ c ∈ gaugeConstraints d, c ∈ (compileCircuit C).constraints := by
    intro c hc
    dsimp [compileCircuit, compileCircuitConstraints]
    exact List.mem_append_left _ (List.mem_append_left _ hc)
  have hmem_gate : ∀ (k : Fin S) c,
      c ∈ gateConstraints N S k.1 C.gates[k.1] → c ∈ (compileCircuit C).constraints := by
    intro k c hc
    dsimp [compileCircuit, compileCircuitConstraints]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    refine List.mem_flatMap.mpr ⟨(C.gates[k.1], k.1), ?_, hc⟩
    exact (mem_zipIdx_iff C.gates C.gates[k.1] k.1).mpr ⟨k.2, rfl⟩
  have hmem_out : (singleEntryRows d d (3 + N + C.output) (3 + N + C.output) 1, 0) ∈
      (compileCircuit C).constraints := by
    dsimp [compileCircuit, compileCircuitConstraints]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hsingle_eval : ∀ (r c : Fin d) (val : ℚ),
      (singleEntryRows d d r.1 c.1 1, val) ∈ (compileCircuit C).constraints →
        X r c = (val : ℝ) := by
    intro r c val hmem
    have hc := hsat _ hmem
    change frobeniusInner ((Matrix.of fun i : Fin d ↦ fun j : Fin d ↦
      ((singleEntryRows d d r.1 c.1 1).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) X =
        (val : ℝ) at hc
    rwa [eval_singleEntryRows r.2 c.2 X] at hc
  have hdiff_eval : ∀ (r₁ c₁ r₂ c₂ : Fin d),
      (diffEntryRows d d r₁.1 c₁.1 r₂.1 c₂.1, 0) ∈ (compileCircuit C).constraints →
        X r₁ c₁ = X r₂ c₂ := by
    intro r₁ c₁ r₂ c₂ hmem
    have hc := hsat _ hmem
    change frobeniusInner ((Matrix.of fun i : Fin d ↦ fun j : Fin d ↦
      ((diffEntryRows d d r₁.1 c₁.1 r₂.1 c₂.1).getD i.1 []).getD j.1 0).map ((↑) : ℚ → ℝ)) X =
        ((0 : ℚ) : ℝ) at hc
    rw [eval_diffEntryRows r₁.2 c₁.2 r₂.2 c₂.2 X, Rat.cast_zero, sub_eq_zero] at hc
    exact hc
  let I₀ : Fin 3 ↪ Fin d := ⟨fun i ↦ ⟨i.1, by dsimp [d, circuitDim]; omega⟩,
    fun a b h ↦ Fin.ext (by simpa using congrArg Fin.val h)⟩
  have hI₀ : ∀ t : Fin 3, I₀ t = ⟨t.1, by dsimp [d, circuitDim]; omega⟩ := fun _ ↦ rfl
  have hpin : X.submatrix I₀ I₀ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext a b
    change X (I₀ a) (I₀ b) = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b
    rw [hI₀ a, hI₀ b]
    fin_cases a <;> fin_cases b
    · simpa using hsingle_eval ⟨0, by dsimp [d, circuitDim]; omega⟩
        ⟨0, by dsimp [d, circuitDim]; omega⟩ 1 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨0, by dsimp [d, circuitDim]; omega⟩
        ⟨1, by dsimp [d, circuitDim]; omega⟩ 0 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨0, by dsimp [d, circuitDim]; omega⟩
        ⟨2, by dsimp [d, circuitDim]; omega⟩ 0 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨1, by dsimp [d, circuitDim]; omega⟩
        ⟨0, by dsimp [d, circuitDim]; omega⟩ 0 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨1, by dsimp [d, circuitDim]; omega⟩
        ⟨1, by dsimp [d, circuitDim]; omega⟩ 1 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨1, by dsimp [d, circuitDim]; omega⟩
        ⟨2, by dsimp [d, circuitDim]; omega⟩ 0 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨2, by dsimp [d, circuitDim]; omega⟩
        ⟨0, by dsimp [d, circuitDim]; omega⟩ 0 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨2, by dsimp [d, circuitDim]; omega⟩
        ⟨1, by dsimp [d, circuitDim]; omega⟩ 0 (hmem_gauge _ (by simp [gaugeConstraints]))
    · simpa using hsingle_eval ⟨2, by dsimp [d, circuitDim]; omega⟩
        ⟨2, by dsimp [d, circuitDim]; omega⟩ 1 (hmem_gauge _ (by simp [gaugeConstraints]))
  have hB2 : ((1 : Matrix (Fin 3) (Fin 3) ℝ).submatrix ![0, 1] ![0, 1]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [Matrix.one_apply]
  have hgateEq : C.GateEq x z := by
    intro k
    have hwf := C.gates_wf k.1 k.2
    generalize hgk : C.gates[k.1] = g at hwf
    cases g with
    | input idx =>
      simp only [ArithGate.wellFormed_input] at hwf
      refine ⟨hwf, ?_⟩
      exact hdiff_eval (gateCarrierIdx N S k.1 k.2) (gateCarrierIdx N S k.1 k.2)
        (inputCarrierIdx N S idx hwf) (inputCarrierIdx N S idx hwf)
        (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, gateCarrierIdx, inputCarrierIdx, d]))
    | const val =>
      exact hsingle_eval (gateCarrierIdx N S k.1 k.2) (gateCarrierIdx N S k.1 k.2) val
        (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, gateCarrierIdx, d]))
    | add l r =>
      rw [ArithGate.wellFormed_add] at hwf
      have hl : l < S := hwf.1.trans k.2
      have hr : r < S := hwf.2.trans k.2
      refine ⟨hl, hr, ?_⟩
      have hc := hsat (addEntryRows d d (3 + N + k.1) (3 + N + k.1) (3 + N + l) (3 + N + l)
        (3 + N + r) (3 + N + r), 0) (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, d]))
      have hklt : 3 + N + k.1 < (compileCircuit C).rows := by
        change 3 + N + k.1 < d; dsimp [d, circuitDim]; omega
      have hllt : 3 + N + l < (compileCircuit C).rows := by
        change 3 + N + l < d; dsimp [d, circuitDim]; omega
      have hrlt : 3 + N + r < (compileCircuit C).rows := by
        change 3 + N + r < d; dsimp [d, circuitDim]; omega
      have hev := eval_addEntryRows (r_z := 3 + N + k.1) (c_z := 3 + N + k.1)
        (rₓ := 3 + N + l) (cₓ := 3 + N + l) (rᵧ := 3 + N + r) (cᵧ := 3 + N + r)
        hklt hklt hllt hllt hrlt hrlt (X := X)
      have hzero : z k - z ⟨l, hl⟩ - z ⟨r, hr⟩ = 0 :=
        (hev.symm.trans hc).trans Rat.cast_zero
      linarith
    | neg a =>
      simp only [ArithGate.wellFormed_neg] at hwf
      have ha : a < S := hwf.trans k.2
      refine ⟨ha, ?_⟩
      have hc := hsat (negEntryRows d d (3 + N + k.1) (3 + N + k.1) (3 + N + a) (3 + N + a), 0)
        (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, d]))
      have hklt : 3 + N + k.1 < (compileCircuit C).rows := by
        change 3 + N + k.1 < d; dsimp [d, circuitDim]; omega
      have halt : 3 + N + a < (compileCircuit C).rows := by
        change 3 + N + a < d; dsimp [d, circuitDim]; omega
      have hev := eval_negEntryRows (r_z := 3 + N + k.1) (c_z := 3 + N + k.1)
        (rₓ := 3 + N + a) (cₓ := 3 + N + a) hklt hklt halt halt (X := X)
      have hzero : z k + z ⟨a, ha⟩ = 0 :=
        (hev.symm.trans hc).trans Rat.cast_zero
      linarith
    | mul l r =>
      rw [ArithGate.wellFormed_mul] at hwf
      have hl : l < S := hwf.1.trans k.2
      have hr : r < S := hwf.2.trans k.2
      refine ⟨hl, hr, ?_⟩
      let r1 := mulAuxIdx1 N S k.1 k.2
      let r2 := mulAuxIdx2 N S k.1 k.2
      have h11 : X r1 r1 = 1 := by
        simpa using hsingle_eval r1 r1 1
          (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, mulAuxIdx1, d]))
      have hztop : ∀ p q : Fin 2, X (I₀ (![0, 1] p)) (![r1, r2] q) = 0 := by
        intro p q
        fin_cases p <;> fin_cases q
        · simpa [hI₀] using hsingle_eval ⟨0, by dsimp [d, circuitDim]; omega⟩ r1 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, mulAuxIdx1, d]))
        · simpa [hI₀] using hsingle_eval ⟨0, by dsimp [d, circuitDim]; omega⟩ r2 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r2, mulAuxIdx2, d]))
        · simpa [hI₀] using hsingle_eval ⟨1, by dsimp [d, circuitDim]; omega⟩ r1 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, mulAuxIdx1, d]))
        · simpa [hI₀] using hsingle_eval ⟨1, by dsimp [d, circuitDim]; omega⟩ r2 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r2, mulAuxIdx2, d]))
      have hzbot : ∀ p q : Fin 2, X (![r1, r2] p) (I₀ (![0, 1] q)) = 0 := by
        intro p q
        fin_cases p <;> fin_cases q
        · simpa [hI₀] using hsingle_eval r1 ⟨0, by dsimp [d, circuitDim]; omega⟩ 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, mulAuxIdx1, d]))
        · simpa [hI₀] using hsingle_eval r1 ⟨1, by dsimp [d, circuitDim]; omega⟩ 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, mulAuxIdx1, d]))
        · simpa [hI₀] using hsingle_eval r2 ⟨0, by dsimp [d, circuitDim]; omega⟩ 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r2, mulAuxIdx2, d]))
        · simpa [hI₀] using hsingle_eval r2 ⟨1, by dsimp [d, circuitDim]; omega⟩ 0
            (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r2, mulAuxIdx2, d]))
      have hmul : X r2 r2 = X r1 r2 * X r2 r1 :=
        det_forcing_soundness hrank hpin hB2 hztop hzbot h11
      have hcl : X r1 r2 = z ⟨l, hl⟩ :=
        hdiff_eval r1 r2 (gateCarrierIdx N S l hl) (gateCarrierIdx N S l hl)
          (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, r2, mulAuxIdx1, mulAuxIdx2,
            gateCarrierIdx, d]))
      have hcr : X r2 r1 = z ⟨r, hr⟩ :=
        hdiff_eval r2 r1 (gateCarrierIdx N S r hr) (gateCarrierIdx N S r hr)
          (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r1, r2, mulAuxIdx1, mulAuxIdx2,
            gateCarrierIdx, d]))
      have hck : X r2 r2 = z k :=
        hdiff_eval r2 r2 (gateCarrierIdx N S k.1 k.2) (gateCarrierIdx N S k.1 k.2)
          (hmem_gate k _ (by rw [hgk]; simp [gateConstraints, r2, mulAuxIdx2, gateCarrierIdx, d]))
      rw [← hck, hmul, hcl, hcr]
  have hout : z ⟨C.output, C.output_lt⟩ = 0 := by
    simpa [z] using hsingle_eval (gateCarrierIdx N S C.output C.output_lt)
      (gateCarrierIdx N S C.output C.output_lt) 0 hmem_out
  exact ⟨x, (circuit_constraints_exact C x).mpr ⟨z, hgateEq, hout⟩⟩

/-- an arithmetic circuit `C` is satisfiable over `ℝ` if and only if its compiled `ARM(3)` instance
`compileCircuit C` is feasible. -/
theorem circuit_iff_arm3 (C : ArithCircuit) :
    C.Satisfiable ↔ (compileCircuit C).Feasible 3 :=
  ⟨compileCircuit_soundness C, compileCircuit_completeness C⟩

/-- . -/
theorem soundness_rank3 (C : ArithCircuit) :
    C.Satisfiable ↔ (compileCircuit C).Feasible 3 :=
  circuit_iff_arm3 C

/-- . -/
theorem arm_correct (C : ArithCircuit) :
    C.Satisfiable ↔ (compileCircuit C).Feasible 3 :=
  circuit_iff_arm3 C

end Cslib.Complexity
