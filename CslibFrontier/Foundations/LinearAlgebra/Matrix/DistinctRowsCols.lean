/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Rank

import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Distinct Rows and Columns of Matrices

This module defines the numbers of distinct rows and distinct columns of a matrix over arbitrary
index and entry types, proves their basic algebraic and rank inequalities under standard Lean
axioms, and derives fiber-multiplicity sum-compression identities for matrices whose rows and
columns factor through finite representative sets.

In communication complexity, `distinctRows M` and `distinctCols M` bound the deterministic leaf
count and log-rank parameters of a communication matrix `M`, while in
parameterized matrix algorithms they govern structural compression under matrix and Hadamard
products.

## Main definitions

* `CslibFrontier.Matrix.distinctRows`: cardinality of the set of row vectors of a matrix `M`.
* `CslibFrontier.Matrix.distinctCols`: cardinality of the set of column vectors of a matrix `M`.

## Main results

* `CslibFrontier.Matrix.distinctCols_eq_distinctRows_transpose`,
  `CslibFrontier.Matrix.distinctRows_eq_distinctCols_transpose`: transpose duality.
* `CslibFrontier.Matrix.distinctRows_le_card`, `CslibFrontier.Matrix.distinctCols_le_card`,
  `CslibFrontier.Matrix.distinctRows_pos`, `CslibFrontier.Matrix.distinctCols_pos`: cardinality
  and positivity bounds.
* `CslibFrontier.Matrix.distinctRows_mul_le`, `CslibFrontier.Matrix.distinctCols_mul_le`: matrix
  multiplication cannot increase the number of distinct rows of the left factor or distinct columns
  of the right factor.
* `CslibFrontier.Matrix.distinctRows_hadamard_le_mul`,
  `CslibFrontier.Matrix.distinctCols_hadamard_le_mul`: submultiplicativity under Hadamard products.
* `CslibFrontier.Matrix.rank_le_distinctCols`, `CslibFrontier.Matrix.rank_le_distinctRows`: the
  rank of a matrix over a field is at most its number of distinct columns and its number of
  distinct rows.
* `CslibFrontier.Matrix.exists_row_representatives_of_distinctRows_le`,
  `CslibFrontier.Matrix.sum_rows_eq_sum_fiber_card_nsmul`,
  `CslibFrontier.Matrix.sum_entries_eq_sum_row_col_fibers`: finite representative factorizations
  and fiber-multiplicity sum compression.
-/

public section

open scoped BigOperators Matrix

namespace CslibFrontier.Matrix

section Basic

variable {m n p α β : Type*}

/-- The number of distinct row vectors of a matrix `M : Matrix m n α`, defined via `Set.ncard`
on the range of `i ↦ M i`. -/
@[expose]
noncomputable def distinctRows (M : _root_.Matrix m n α) : ℕ :=
  (Set.range fun i : m ↦ fun j : n ↦ M i j).ncard

/-- The number of distinct column vectors of a matrix `M : Matrix m n α`, defined via `Set.ncard`
on the range of `j ↦ (i ↦ M i j)`. -/
@[expose]
noncomputable def distinctCols (M : _root_.Matrix m n α) : ℕ :=
  (Set.range fun j : n ↦ fun i : m ↦ M i j).ncard

/-- The number of distinct columns of `M` equals the number of distinct rows of `Mᵀ`. -/
@[simp]
theorem distinctCols_eq_distinctRows_transpose (M : _root_.Matrix m n α) :
    distinctCols M = distinctRows Mᵀ := by
  unfold distinctCols distinctRows
  rfl

/-- The number of distinct rows of `M` equals the number of distinct columns of `Mᵀ`. -/
theorem distinctRows_eq_distinctCols_transpose (M : _root_.Matrix m n α) :
    distinctRows M = distinctCols Mᵀ := by
  unfold distinctRows distinctCols
  rfl

/-- A matrix over a `Fintype` row index `m` has at most `Fintype.card m` distinct rows. -/
theorem distinctRows_le_card [Fintype m] (M : _root_.Matrix m n α) :
    distinctRows M ≤ Fintype.card m := by
  rw [distinctRows, ← Set.image_univ]
  exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])

/-- A matrix over a `Fintype` column index `n` has at most `Fintype.card n` distinct columns. -/
theorem distinctCols_le_card [Fintype n] (M : _root_.Matrix m n α) :
    distinctCols M ≤ Fintype.card n := by
  rw [distinctCols_eq_distinctRows_transpose]
  exact distinctRows_le_card Mᵀ

/-- A matrix with a nonempty finite row index type has at least one distinct row. -/
theorem distinctRows_pos [Finite m] [Nonempty m] (M : _root_.Matrix m n α) :
    0 < distinctRows M :=
  (Set.range_nonempty _).ncard_pos (Set.finite_range _)

/-- A matrix with a nonempty finite column index type has at least one distinct column. -/
theorem distinctCols_pos [Finite n] [Nonempty n] (M : _root_.Matrix m n α) :
    0 < distinctCols M :=
  (Set.range_nonempty _).ncard_pos (Set.finite_range _)

/-- Entrywise mapping cannot increase the number of distinct rows. -/
theorem distinctRows_map_le [Finite m] (M : _root_.Matrix m n α) (f : α → β) :
    distinctRows (M.map f) ≤ distinctRows M := by
  have hsub : (Set.range fun i : m ↦ fun j : n ↦ M.map f i j) =
      (fun (r : n → α) (j : n) ↦ f (r j)) '' (Set.range fun i : m ↦ fun j : n ↦ M i j) := by
    ext w
    simp only [_root_.Matrix.map_apply, Set.mem_range, Set.mem_image]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨fun j ↦ M i j, ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, rfl⟩, hi⟩ ↦ ⟨i, hi⟩⟩
  rw [distinctRows, distinctRows, hsub]
  exact Set.ncard_image_le (Set.finite_range _)

/-- Multiplying `A * B` cannot produce more distinct rows than `A` has. -/
theorem distinctRows_mul_le [Finite m] [Fintype n] [Mul α] [AddCommMonoid α]
    (A : _root_.Matrix m n α) (B : _root_.Matrix n p α) :
    distinctRows (A * B) ≤ distinctRows A := by
  have hrange : (Set.range fun i : m ↦ fun k : p ↦ (A * B) i k) =
      (fun (r : n → α) (k : p) ↦ ∑ j : n, r j * B j k) ''
        (Set.range fun i : m ↦ fun j : n ↦ A i j) := by
    ext w
    simp only [_root_.Matrix.mul_apply, Set.mem_range, Set.mem_image]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨fun j ↦ A i j, ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, rfl⟩, hi⟩ ↦ ⟨i, hi⟩⟩
  rw [distinctRows, distinctRows, hrange]
  exact Set.ncard_image_le (Set.finite_range _)

/-- Multiplying `A * B` cannot produce more distinct columns than `B` has. -/
theorem distinctCols_mul_le [Fintype n] [Finite p] [CommSemiring α]
    (A : _root_.Matrix m n α) (B : _root_.Matrix n p α) :
    distinctCols (A * B) ≤ distinctCols B := by
  rw [distinctCols_eq_distinctRows_transpose, _root_.Matrix.transpose_mul]
  exact distinctRows_mul_le Bᵀ Aᵀ

/-- Submultiplicativity of `distinctRows` under the Hadamard product `A ⊙ B`. -/
theorem distinctRows_hadamard_le_mul [Finite m] [Mul α]
    (A B : _root_.Matrix m n α) :
    distinctRows (A ⊙ B) ≤ distinctRows A * distinctRows B := by
  let SA := Set.range fun i : m ↦ fun j : n ↦ A i j
  let SB := Set.range fun i : m ↦ fun j : n ↦ B i j
  have hsub : (Set.range fun i : m ↦ fun j : n ↦ (A ⊙ B) i j) ⊆
      (fun (q : (n → α) × (n → α)) (j : n) ↦ q.1 j * q.2 j) '' (SA ×ˢ SB) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(fun j ↦ A i j, fun j ↦ B i j), ⟨⟨i, rfl⟩, ⟨i, rfl⟩⟩, rfl⟩
  have hfin : (SA ×ˢ SB).Finite := (Set.finite_range _).prod (Set.finite_range _)
  calc distinctRows (A ⊙ B)
      ≤ ((fun (q : (n → α) × (n → α)) (j : n) ↦ q.1 j * q.2 j) '' (SA ×ˢ SB)).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (SA ×ˢ SB).ncard := Set.ncard_image_le hfin
    _ = distinctRows A * distinctRows B := Set.ncard_prod

/-- Submultiplicativity of `distinctCols` under the Hadamard product `A ⊙ B`. -/
theorem distinctCols_hadamard_le_mul [Finite n] [Mul α]
    (A B : _root_.Matrix m n α) :
    distinctCols (A ⊙ B) ≤ distinctCols A * distinctCols B := by
  rw [distinctCols_eq_distinctRows_transpose, _root_.Matrix.transpose_hadamard]
  exact distinctRows_hadamard_le_mul Aᵀ Bᵀ

end Basic

section Rank

variable {m n K : Type*} [Fintype n] [Field K]

/-- Over a field, the rank of a matrix is at most its number of distinct columns. -/
theorem rank_le_distinctCols (M : _root_.Matrix m n K) :
    M.rank ≤ distinctCols M := by
  classical
  let S : Set (m → K) := Set.range fun j : n ↦ fun i : m ↦ M i j
  have hfin : S.Finite := Set.finite_range _
  rw [_root_.Matrix.rank, _root_.Matrix.range_mulVecLin]
  have hEq : (Set.range M.col : Set (m → K)) = S := rfl
  rw [hEq, ← hfin.coe_toFinset]
  unfold distinctCols
  calc Module.finrank K (Submodule.span K (hfin.toFinset : Set (m → K)))
      ≤ hfin.toFinset.card :=
        (finrank_span_le_card (R := K) (hfin.toFinset : Set (m → K))).trans (by simp)
    _ = S.ncard := (Set.ncard_eq_toFinset_card S hfin).symm

/-- Over a field, the rank of a matrix is at most its number of distinct rows. -/
theorem rank_le_distinctRows [Finite m] (M : _root_.Matrix m n K) :
    M.rank ≤ distinctRows M := by
  let _ : Fintype m := Fintype.ofFinite m
  rw [← _root_.Matrix.rank_transpose, distinctRows_eq_distinctCols_transpose]
  exact rank_le_distinctCols Mᵀ

end Rank

section FiberCompression

variable {m n α M₀ : Type*}

/-- If `M : Matrix m n α` on a nonempty finite row index type satisfies `distinctRows M ≤ L`, then
the rows of `M` factor through `Fin L` via `g : m → Fin L` and `rep : Fin L → m`. -/
theorem exists_row_representatives_of_distinctRows_le [Finite m] [Nonempty m]
    (M : _root_.Matrix m n α) {L : ℕ} (hL : distinctRows M ≤ L) :
    ∃ (g : m → Fin L) (rep : Fin L → m), ∀ i : m, M i = M (rep (g i)) := by
  classical
  let S : Set (n → α) := Set.range fun i : m ↦ fun j : n ↦ M i j
  have hfin : S.Finite := Set.finite_range _
  have hcard : hfin.toFinset.card ≤ L := by
    unfold distinctRows at hL
    exact (Set.ncard_eq_toFinset_card S hfin).symm.trans_le hL
  let e : Fin hfin.toFinset.card ≃ hfin.toFinset := hfin.toFinset.equivFin.symm
  let dflt : m := Classical.arbitrary m
  let pickRow : (n → α) → m := fun r ↦ if hr : r ∈ S then hr.choose else dflt
  have hpick (r : n → α) (hr : r ∈ S) : M (pickRow r) = r := by
    simp only [pickRow, hr, ↓reduceDIte]
    exact hr.choose_spec
  let rep : Fin L → m := fun b ↦
    if hb : (b : ℕ) < hfin.toFinset.card then pickRow (e ⟨b, hb⟩).1 else dflt
  let g : m → Fin L := fun i ↦
    Fin.castLE hcard (e.symm ⟨fun j ↦ M i j, hfin.mem_toFinset.mpr ⟨i, rfl⟩⟩)
  refine ⟨g, rep, fun i ↦ ?_⟩
  let idx := e.symm ⟨fun j ↦ M i j, hfin.mem_toFinset.mpr ⟨i, rfl⟩⟩
  have hgi : g i = Fin.castLE hcard idx := rfl
  have hlt : ((g i : Fin L) : ℕ) < hfin.toFinset.card := by
    rw [hgi]
    exact idx.isLt
  have hrep : rep (g i) = pickRow (e ⟨(g i : ℕ), hlt⟩).1 := by
    simp only [rep, hlt, ↓reduceDIte]
  have heq_val : (g i : ℕ) = (idx : ℕ) := by rw [hgi]; rfl
  have heq_idx : (⟨(g i : ℕ), hlt⟩ : Fin hfin.toFinset.card) = idx := Fin.ext heq_val
  rw [hrep, heq_idx, Equiv.apply_symm_apply]
  exact (hpick (fun j ↦ M i j) ⟨i, rfl⟩).symm

/-- Fiber-multiplicity sum compression along `g : m → ι` and representatives `rep : ι → m`. -/
theorem sum_rows_eq_sum_fiber_card_nsmul {ι : Type*} [Fintype m] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M₀] (f : m → M₀) (g : m → ι) (rep : ι → m)
    (hrep : ∀ i : m, f i = f (rep (g i))) :
    ∑ i : m, f i = ∑ a : ι, (Finset.univ.filter fun i : m ↦ g i = a).card • f (rep a) := by
  calc ∑ i : m, f i
      = ∑ a : ι, ∑ i ∈ Finset.univ.filter (fun i : m ↦ g i = a), f i :=
        (Finset.sum_fiberwise_of_maps_to (fun _ _ ↦ Finset.mem_univ _) f).symm
    _ = ∑ a : ι, ∑ i ∈ Finset.univ.filter (fun i : m ↦ g i = a), f (rep a) := by
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hrep i, (Finset.mem_filter.mp hi).2]
    _ = ∑ a : ι, (Finset.univ.filter fun i : m ↦ g i = a).card • f (rep a) := by
        simp only [Finset.sum_const]

/-- Two-dimensional block-multiplicity sum compression along row and column representatives. -/
theorem sum_entries_eq_sum_row_col_fibers {ι₁ ι₂ : Type*} [Fintype m] [Fintype n]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [AddCommMonoid M₀]
    (X : _root_.Matrix m n α) (φ : α → M₀)
    (g₁ : m → ι₁) (rep₁ : ι₁ → m) (h₁ : ∀ i j, X i j = X (rep₁ (g₁ i)) j)
    (g₂ : n → ι₂) (rep₂ : ι₂ → n) (h₂ : ∀ i j, X i j = X i (rep₂ (g₂ j))) :
    ∑ i : m, ∑ j : n, φ (X i j) =
      ∑ a : ι₁, ∑ b : ι₂,
        ((Finset.univ.filter fun i : m ↦ g₁ i = a).card *
          (Finset.univ.filter fun j : n ↦ g₂ j = b).card) • φ (X (rep₁ a) (rep₂ b)) := by
  have hrow : ∀ i : m, (∑ j : n, φ (X i j)) = ∑ j : n, φ (X (rep₁ (g₁ i)) j) := fun i ↦
    Finset.sum_congr rfl fun j _ ↦ by rw [h₁ i j]
  rw [sum_rows_eq_sum_fiber_card_nsmul (fun i : m ↦ ∑ j : n, φ (X i j)) g₁ rep₁ hrow]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have hcol : ∀ j : n, φ (X (rep₁ a) j) = φ (X (rep₁ a) (rep₂ (g₂ j))) := fun j ↦ by
    rw [h₂ (rep₁ a) j]
  rw [sum_rows_eq_sum_fiber_card_nsmul (fun j : n ↦ φ (X (rep₁ a) j)) g₂ rep₂ hcol,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [mul_smul]

end FiberCompression

end CslibFrontier.Matrix
